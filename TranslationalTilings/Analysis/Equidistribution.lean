import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.Analysis.CirclePolynomial

/-!
# Equidistribution of circle-polynomial sequences

This file proves the Weyl character criterion on the unit additive circle,
the Cesàro van der Corput estimate used for polynomial phases, and the
continuous bump-function consequence needed by the avoidance argument.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- The standard circle character converts addition on the torus into multiplication. -/
theorem circlePhase_add (x y : Torus) :
    circlePhase (x + y) = circlePhase x * circlePhase y := by
  simp [circlePhase, fourier_apply, AddCircle.toCircle_add,
    Circle.coe_mul]

/-- The standard circle character has unit norm. -/
theorem norm_circlePhase (x : Torus) : ‖circlePhase x‖ = 1 := by
  rw [circlePhase, fourier_one]
  exact Circle.norm_coe _

/-- Every nontrivial integer character has zero Haar integral on the torus. -/
theorem integral_circlePhase_zsmul (k : ℤ) (hk : k ≠ 0) :
    ∫ x : Torus, circlePhase (k • x) ∂AddCircle.haarAddCircle = 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  simpa [fourierCoeff, fourier_apply, circlePhase, hk] using h

private theorem continuousMap_integrable (f : C(Torus, ℂ)) :
    MeasureTheory.Integrable f AddCircle.haarAddCircle := by
  simpa only [MeasureTheory.integrableOn_univ] using
    (ContinuousOn.integrableOn_compact isCompact_univ
      f.continuous.continuousOn)

private theorem cesaroAverage_comp_add (u : ℕ → Torus)
    (f g : C(Torus, ℂ)) (N : ℕ) :
    cesaroAverage (fun n ↦ (f + g) (u n)) N =
      cesaroAverage (fun n ↦ f (u n)) N +
        cesaroAverage (fun n ↦ g (u n)) N := by
  simp only [cesaroAverage, ContinuousMap.add_apply,
    Finset.sum_add_distrib, mul_add]

private theorem cesaroAverage_comp_smul (u : ℕ → Torus)
    (a : ℂ) (f : C(Torus, ℂ)) (N : ℕ) :
    cesaroAverage (fun n ↦ (a • f) (u n)) N =
      a • cesaroAverage (fun n ↦ f (u n)) N := by
  simp only [cesaroAverage, ContinuousMap.smul_apply, smul_eq_mul,
    ← Finset.mul_sum]
  ring

private theorem norm_cesaroAverage_comp_sub_le (u : ℕ → Torus)
    (f g : C(Torus, ℂ)) (N : ℕ) :
    ‖cesaroAverage (fun n ↦ f (u n)) N -
        cesaroAverage (fun n ↦ g (u n)) N‖ ≤ ‖f - g‖ := by
  have heq : cesaroAverage (fun n ↦ f (u n)) N -
      cesaroAverage (fun n ↦ g (u n)) N =
      cesaroAverage (fun n ↦ (f - g) (u n)) N := by
    simp [cesaroAverage, Finset.sum_sub_distrib, mul_sub]
  rw [heq]
  rw [cesaroAverage]
  calc
    ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, (f (u n) - g (u n))‖
        ≤ ‖(N : ℂ)⁻¹‖ *
            ∑ n ∈ Finset.range N, ‖f (u n) - g (u n)‖ := by
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _))
    _ ≤ ‖(N : ℂ)⁻¹‖ *
            ∑ _n ∈ Finset.range N, ‖f - g‖ := by
          gcongr with n hn
          simpa only [ContinuousMap.sub_apply] using
            ContinuousMap.norm_coe_le_norm (f - g) (u n)
    _ ≤ ‖f - g‖ := by
          by_cases hN : N = 0
          · simp [hN]
          · simp [norm_inv, hN]

private theorem norm_integral_continuousMap_sub_le (f g : C(Torus, ℂ)) :
    ‖(∫ x, f x ∂AddCircle.haarAddCircle) -
        ∫ x, g x ∂AddCircle.haarAddCircle‖ ≤ ‖f - g‖ := by
  rw [← MeasureTheory.integral_sub (continuousMap_integrable f)
    (continuousMap_integrable g)]
  have h := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := AddCircle.haarAddCircle)
    (f := fun x ↦ f x - g x) (C := ‖f - g‖)
    (Filter.Eventually.of_forall fun x ↦ by
      simpa only [ContinuousMap.sub_apply] using
        ContinuousMap.norm_coe_le_norm (f - g) x)
  simpa using h

private theorem fourier_limit_implies_equidistributed
    (u : ℕ → Torus)
    (hchar : ∀ k : ℤ, k ≠ 0 → Filter.Tendsto
      (fun N ↦ cesaroAverage (fun n ↦ circlePhase (k • u n)) N)
      Filter.atTop (nhds 0)) :
    Equidistributed u := by
  intro f
  have hspan : ∀ g : C(Torus, ℂ),
      g ∈ Submodule.span ℂ (Set.range (@fourier (1 : ℝ))) →
      Filter.Tendsto
        (fun N ↦ cesaroAverage (fun n ↦ g (u n)) N)
        Filter.atTop
        (nhds (∫ x, g x ∂AddCircle.haarAddCircle)) := by
    intro g hg
    refine Submodule.span_induction (p := fun g _ ↦ Filter.Tendsto
      (fun N ↦ cesaroAverage (fun n ↦ g (u n)) N)
      Filter.atTop (nhds (∫ x, g x ∂AddCircle.haarAddCircle)))
      ?_ ?_ ?_ ?_ hg
    · intro g hg
      obtain ⟨k, rfl⟩ := hg
      by_cases hk : k = 0
      · subst k
        have hev : ∀ᶠ N in Filter.atTop,
            cesaroAverage (fun n ↦ fourier 0 (u n)) N = 1 := by
          filter_upwards [Filter.eventually_ge_atTop 1] with N hN
          simp [cesaroAverage, Nat.ne_of_gt hN]
        have hlim : Filter.Tendsto
            (fun N ↦ cesaroAverage (fun n ↦ fourier 0 (u n)) N)
            Filter.atTop (nhds 1) :=
          tendsto_const_nhds.congr' (hev.mono fun _ hN ↦ hN.symm)
        simpa using hlim
      · have hc := hchar k hk
        convert hc using 1
        · funext N
          congr 2
          funext n
          simp [circlePhase, fourier_apply]
        · apply congrArg nhds
          rw [← integral_circlePhase_zsmul k hk]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          simp [circlePhase, fourier_apply]
    · simp [cesaroAverage]
    · intro g₁ g₂ _ _ hg₁ hg₂
      convert hg₁.add hg₂ using 1
      · funext N
        exact cesaroAverage_comp_add u g₁ g₂ N
      · apply congrArg nhds
        exact MeasureTheory.integral_add
          (continuousMap_integrable g₁) (continuousMap_integrable g₂)
    · intro a g _ hg
      convert hg.const_smul a using 1
      · funext N
        exact cesaroAverage_comp_smul u a g N
      · apply congrArg nhds
        simpa only [ContinuousMap.smul_apply, smul_eq_mul] using
          (MeasureTheory.integral_smul (μ := AddCircle.haarAddCircle)
            a (fun x ↦ g x))
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  have hfclosure :
      f ∈ (Submodule.span ℂ
        (Set.range (@fourier (1 : ℝ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨g, hgspan, hgf⟩ :=
    (Metric.mem_closure_iff.mp hfclosure) (eps / 4) (by positivity)
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (hspan g hgspan)
    (eps / 2) (by positivity)
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have havg := norm_cesaroAverage_comp_sub_le u f g N
  have hint := norm_integral_continuousMap_sub_le g f
  have hmid := hN₀ N hN
  rw [dist_eq_norm] at hgf hmid ⊢
  calc
    ‖cesaroAverage (fun n ↦ f (u n)) N -
        ∫ x, f x ∂AddCircle.haarAddCircle‖
        ≤ ‖cesaroAverage (fun n ↦ f (u n)) N -
              cesaroAverage (fun n ↦ g (u n)) N‖ +
            ‖cesaroAverage (fun n ↦ g (u n)) N -
              ∫ x, g x ∂AddCircle.haarAddCircle‖ +
            ‖(∫ x, g x ∂AddCircle.haarAddCircle) -
              ∫ x, f x ∂AddCircle.haarAddCircle‖ := by
          calc
            _ = ‖(cesaroAverage (fun n ↦ f (u n)) N -
                    cesaroAverage (fun n ↦ g (u n)) N) +
                  (cesaroAverage (fun n ↦ g (u n)) N -
                    ∫ x, g x ∂AddCircle.haarAddCircle) +
                  ((∫ x, g x ∂AddCircle.haarAddCircle) -
                    ∫ x, f x ∂AddCircle.haarAddCircle)‖ := by ring_nf
            _ ≤ _ := (norm_add_le _ _).trans
              (add_le_add (norm_add_le _ _) le_rfl)
    _ < eps := by
      have havg' : ‖cesaroAverage (fun n ↦ f (u n)) N -
          cesaroAverage (fun n ↦ g (u n)) N‖ < eps / 4 :=
        havg.trans_lt hgf
      have hint' : ‖(∫ x, g x ∂AddCircle.haarAddCircle) -
          ∫ x, f x ∂AddCircle.haarAddCircle‖ < eps / 4 :=
        hint.trans_lt (by simpa [norm_sub_rev] using hgf)
      linarith

/-- Weyl's character criterion for one-sided sequences on the unit additive circle. -/
theorem equidistributed_iff_characters (u : ℕ → Torus) :
  Equidistributed u ↔ ∀ k : ℤ, k ≠ 0 → Filter.Tendsto
    (fun N ↦ cesaroAverage (fun n ↦ circlePhase (k • u n)) N)
    Filter.atTop (nhds 0) := by
  constructor
  · intro hu k hk
    have h := hu (fourier k)
    have hi := integral_circlePhase_zsmul k hk
    convert h using 1
    · funext N
      congr 2
      funext n
      simp [circlePhase, fourier_apply]
    · apply congrArg nhds
      rw [← hi]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simp [circlePhase, fourier_apply]
  · exact fourier_limit_implies_equidistributed u

private theorem symmetricCesaroAverage_comp_add (u : ℤ → Torus)
    (f g : C(Torus, ℂ)) (N : ℕ) :
    symmetricCesaroAverage (fun n ↦ (f + g) (u n)) N =
      symmetricCesaroAverage (fun n ↦ f (u n)) N +
        symmetricCesaroAverage (fun n ↦ g (u n)) N := by
  simp only [symmetricCesaroAverage, ContinuousMap.add_apply,
    Finset.sum_add_distrib, mul_add]

private theorem symmetricCesaroAverage_comp_smul (u : ℤ → Torus)
    (a : ℂ) (f : C(Torus, ℂ)) (N : ℕ) :
    symmetricCesaroAverage (fun n ↦ (a • f) (u n)) N =
      a • symmetricCesaroAverage (fun n ↦ f (u n)) N := by
  simp only [symmetricCesaroAverage, ContinuousMap.smul_apply, smul_eq_mul,
    ← Finset.mul_sum]
  ring

private theorem norm_symmetricCesaroAverage_comp_sub_le (u : ℤ → Torus)
    (f g : C(Torus, ℂ)) (N : ℕ) :
    ‖symmetricCesaroAverage (fun n ↦ f (u n)) N -
        symmetricCesaroAverage (fun n ↦ g (u n)) N‖ ≤ ‖f - g‖ := by
  have heq : symmetricCesaroAverage (fun n ↦ f (u n)) N -
      symmetricCesaroAverage (fun n ↦ g (u n)) N =
      symmetricCesaroAverage (fun n ↦ (f - g) (u n)) N := by
    simp [symmetricCesaroAverage, Finset.sum_sub_distrib, mul_sub]
  rw [heq, symmetricCesaroAverage]
  have hcard : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    ‖(((2 * N + 1 : ℕ) : ℂ))⁻¹ *
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (f (u n) - g (u n))‖
        ≤ ‖(((2 * N + 1 : ℕ) : ℂ))⁻¹‖ *
            ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
              ‖f (u n) - g (u n)‖ := by
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _))
    _ ≤ ‖(((2 * N + 1 : ℕ) : ℂ))⁻¹‖ *
            ∑ _n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖f - g‖ := by
          gcongr with n hn
          simpa only [ContinuousMap.sub_apply] using
            ContinuousMap.norm_coe_le_norm (f - g) (u n)
    _ ≤ ‖f - g‖ := by
          simp only [Finset.sum_const, nsmul_eq_mul, hcard,
            norm_inv, norm_natCast]
          push_cast
          field_simp
          exact le_rfl

private theorem symmetric_fourier_limit
    (u : ℤ → Torus)
    (hchar : ∀ k : ℤ, k ≠ 0 → Filter.Tendsto
      (fun N ↦ symmetricCesaroAverage
        (fun n ↦ circlePhase (k • u n)) N)
      Filter.atTop (nhds 0))
    (k : ℤ) :
    Filter.Tendsto
      (fun N ↦ symmetricCesaroAverage (fun n ↦ fourier k (u n)) N)
      Filter.atTop
      (nhds (∫ x : Torus, fourier k x
        ∂(AddCircle.haarAddCircle : MeasureTheory.Measure Torus))) := by
  by_cases hk : k = 0
  · subst k
    have heq : (fun N ↦ symmetricCesaroAverage
          (fun n ↦ fourier 0 (u n)) N) = fun _ ↦ 1 := by
      funext N
      have hcard : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card =
          2 * N + 1 := by
        rw [Int.card_Icc]
        omega
      simp only [symmetricCesaroAverage, fourier_zero,
        Finset.sum_const, nsmul_eq_mul, hcard]
      push_cast
      have hd : (2 * (N : ℂ) + 1) ≠ 0 := by
        exact_mod_cast (show 2 * N + 1 ≠ 0 by omega)
      rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    rw [heq]
    simp
  · have hc := hchar k hk
    convert hc using 1
    · funext N
      congr 2
      funext n
      simp [circlePhase, fourier_apply]
    · apply congrArg nhds
      rw [← integral_circlePhase_zsmul k hk]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simp [circlePhase, fourier_apply]

private noncomputable def symmetricLimitSubmodule
    (u : ℤ → Torus) : Submodule ℂ C(Torus, ℂ) where
  carrier := {g | Filter.Tendsto
    (fun N ↦ symmetricCesaroAverage (fun n ↦ g (u n)) N)
    Filter.atTop (nhds (∫ x, g x ∂AddCircle.haarAddCircle))}
  zero_mem' := by simp [symmetricCesaroAverage]
  add_mem' := by
    intro g₁ g₂ hg₁ hg₂
    change Filter.Tendsto
      (fun N ↦ symmetricCesaroAverage (fun n ↦ g₁ (u n)) N)
      Filter.atTop (nhds (∫ x, g₁ x ∂AddCircle.haarAddCircle)) at hg₁
    change Filter.Tendsto
      (fun N ↦ symmetricCesaroAverage (fun n ↦ g₂ (u n)) N)
      Filter.atTop (nhds (∫ x, g₂ x ∂AddCircle.haarAddCircle)) at hg₂
    change Filter.Tendsto
      (fun N ↦ symmetricCesaroAverage (fun n ↦ (g₁ + g₂) (u n)) N)
      Filter.atTop (nhds (∫ x, (g₁ + g₂) x
        ∂AddCircle.haarAddCircle))
    convert hg₁.add hg₂ using 1
    · funext N
      exact symmetricCesaroAverage_comp_add u g₁ g₂ N
    · apply congrArg nhds
      exact MeasureTheory.integral_add
        (continuousMap_integrable g₁) (continuousMap_integrable g₂)
  smul_mem' := by
    intro a g hg
    change Filter.Tendsto
      (fun N ↦ symmetricCesaroAverage (fun n ↦ g (u n)) N)
      Filter.atTop (nhds (∫ x, g x ∂AddCircle.haarAddCircle)) at hg
    change Filter.Tendsto
      (fun N ↦ symmetricCesaroAverage (fun n ↦ (a • g) (u n)) N)
      Filter.atTop (nhds (∫ x, (a • g) x ∂AddCircle.haarAddCircle))
    convert hg.const_smul a using 1
    · funext N
      exact symmetricCesaroAverage_comp_smul u a g N
    · apply congrArg nhds
      simpa only [ContinuousMap.smul_apply, smul_eq_mul] using
        (MeasureTheory.integral_smul (μ := AddCircle.haarAddCircle)
          a (fun x ↦ g x))

private theorem symmetric_fourier_span_limit
    (u : ℤ → Torus)
    (hchar : ∀ k : ℤ, k ≠ 0 → Filter.Tendsto
      (fun N ↦ symmetricCesaroAverage
        (fun n ↦ circlePhase (k • u n)) N)
      Filter.atTop (nhds 0))
    (g : C(Torus, ℂ))
    (hg : g ∈ Submodule.span ℂ (Set.range (@fourier (1 : ℝ)))) :
      Filter.Tendsto
        (fun N ↦ symmetricCesaroAverage (fun n ↦ g (u n)) N)
        Filter.atTop
        (nhds (∫ x, g x ∂AddCircle.haarAddCircle)) := by
  have hle : Submodule.span ℂ (Set.range (@fourier (1 : ℝ))) ≤
      symmetricLimitSubmodule u := Submodule.span_le.mpr (by
    rintro _ ⟨k, rfl⟩
    change Filter.Tendsto
      (fun N ↦ symmetricCesaroAverage (fun n ↦ fourier k (u n)) N)
      Filter.atTop (nhds (∫ x, fourier k x ∂AddCircle.haarAddCircle))
    exact symmetric_fourier_limit u hchar k)
  exact hle hg

private theorem fourier_limit_implies_equidistributedInt
    (u : ℤ → Torus)
    (hchar : ∀ k : ℤ, k ≠ 0 → Filter.Tendsto
      (fun N ↦ symmetricCesaroAverage
        (fun n ↦ circlePhase (k • u n)) N)
      Filter.atTop (nhds 0)) :
    EquidistributedInt u := by
  intro f
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  have hfclosure :
      f ∈ (Submodule.span ℂ
        (Set.range (@fourier (1 : ℝ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨g, hgspan, hgf⟩ :=
    (Metric.mem_closure_iff.mp hfclosure) (eps / 4) (by positivity)
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp
    (symmetric_fourier_span_limit u hchar g hgspan)
    (eps / 2) (by positivity)
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have havg := norm_symmetricCesaroAverage_comp_sub_le u f g N
  have hint := norm_integral_continuousMap_sub_le g f
  have hmid := hN₀ N hN
  rw [dist_eq_norm] at hgf hmid ⊢
  calc
    ‖symmetricCesaroAverage (fun n ↦ f (u n)) N -
        ∫ x, f x ∂AddCircle.haarAddCircle‖
        ≤ ‖symmetricCesaroAverage (fun n ↦ f (u n)) N -
              symmetricCesaroAverage (fun n ↦ g (u n)) N‖ +
            ‖symmetricCesaroAverage (fun n ↦ g (u n)) N -
              ∫ x, g x ∂AddCircle.haarAddCircle‖ +
            ‖(∫ x, g x ∂AddCircle.haarAddCircle) -
              ∫ x, f x ∂AddCircle.haarAddCircle‖ := by
          calc
            _ = ‖(symmetricCesaroAverage (fun n ↦ f (u n)) N -
                    symmetricCesaroAverage (fun n ↦ g (u n)) N) +
                  (symmetricCesaroAverage (fun n ↦ g (u n)) N -
                    ∫ x, g x ∂AddCircle.haarAddCircle) +
                  ((∫ x, g x ∂AddCircle.haarAddCircle) -
                    ∫ x, f x ∂AddCircle.haarAddCircle)‖ := by ring_nf
            _ ≤ _ := (norm_add_le _ _).trans
              (add_le_add (norm_add_le _ _) le_rfl)
    _ < eps := by
      have havg' : ‖symmetricCesaroAverage (fun n ↦ f (u n)) N -
          symmetricCesaroAverage (fun n ↦ g (u n)) N‖ < eps / 4 :=
        havg.trans_lt hgf
      have hint' : ‖(∫ x, g x ∂AddCircle.haarAddCircle) -
          ∫ x, f x ∂AddCircle.haarAddCircle‖ < eps / 4 :=
        hint.trans_lt (by simpa [norm_sub_rev] using hgf)
      linarith

/-- Weyl's character criterion for symmetrically averaged integer-indexed sequences. -/
theorem equidistributedInt_iff_characters (u : ℤ → Torus) :
  EquidistributedInt u ↔ ∀ k : ℤ, k ≠ 0 → Filter.Tendsto
    (fun N ↦ symmetricCesaroAverage
      (fun n ↦ circlePhase (k • u n)) N)
    Filter.atTop (nhds 0) := by
  constructor
  · intro hu k hk
    have h := hu (fourier k)
    have hi := integral_circlePhase_zsmul k hk
    convert h using 1
    · funext N
      congr 2
      funext n
      simp [circlePhase, fourier_apply]
    · apply congrArg nhds
      rw [← hi]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simp [circlePhase, fourier_apply]
  · exact fourier_limit_implies_equidistributedInt u

/-- A nonzero integer multiple of a nontorsion torus element remains nontorsion. -/
theorem nontorsion_zsmul {a : Torus} (ha : addOrderOf a = 0)
    {k : ℤ} (hk : k ≠ 0) : addOrderOf (k • a) = 0 := by
  by_contra hne
  have hpos : 0 < addOrderOf (k • a) := Nat.pos_of_ne_zero hne
  have hz : (addOrderOf (k • a) : ℤ) • (k • a) = 0 :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mp (dvd_refl _)
  have hz' : ((addOrderOf (k • a) : ℤ) * k) • a = 0 := by
    simpa only [mul_smul] using hz
  have hdiv : (addOrderOf a : ℤ) ∣
      (addOrderOf (k • a) : ℤ) * k :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz'
  rw [ha] at hdiv
  have hprod : (addOrderOf (k • a) : ℤ) * k = 0 := by
    simpa using hdiv
  exact hk (mul_eq_zero.mp hprod |>.resolve_left
    (Int.ofNat_ne_zero.mpr hpos.ne'))

private theorem cesaro_powers_tendsto_zero (z : ℂ)
    (hz : z ≠ 1) (hnorm : ‖z‖ = 1) :
    Filter.Tendsto (fun N ↦ cesaroAverage (fun n ↦ z ^ n) N)
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Filter.Tendsto
      (fun N : ℕ ↦ (2 / ‖z - 1‖) * (1 / (N : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (2 / ‖z - 1‖)
  apply squeeze_zero' (Filter.Eventually.of_forall fun N ↦ norm_nonneg _)
    (Filter.Eventually.of_forall fun N ↦ ?_) hlim
  by_cases hN : N = 0
  · simp [hN, cesaroAverage]
  have hden : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hsum : (∑ n ∈ Finset.range N, z ^ n) =
      (z ^ N - 1) / (z - 1) :=
    (eq_div_iff hden).2 (geom_sum_mul z N)
  rw [cesaroAverage, hsum, norm_mul, norm_inv, norm_div, norm_natCast]
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    calc
      ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hnorm]; norm_num
  have hdpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hden
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero hN
  rw [inv_eq_one_div]
  calc
    (1 / (N : ℝ)) * (‖z ^ N - 1‖ / ‖z - 1‖) ≤
        (1 / (N : ℝ)) * (2 / ‖z - 1‖) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hnum hdpos.le) (by positivity)
    _ = (2 / ‖z - 1‖) * (1 / (N : ℝ)) := by ring

/-- Cesàro averages of every nontrivial character of a nontorsion linear phase vanish. -/
theorem irrational_linear_phase_tendsto_zero
    (a : Torus) (ha : addOrderOf a = 0) (k : ℤ) (hk : k ≠ 0) :
  Filter.Tendsto
    (fun N ↦ cesaroAverage
      (fun n ↦ circlePhase (k • ((n : ℤ) • a))) N)
    Filter.atTop (nhds 0) := by
  let z := circlePhase (k • a)
  have hz : z ≠ 1 := by
    intro hz1
    have hx0 : k • a = 0 := by
      apply AddCircle.injective_toCircle one_ne_zero
      have hc : (k • a).toCircle = 1 :=
        Circle.coe_injective (by
          simpa [z, circlePhase, fourier_one] using hz1)
      simp [hc]
    have hord := nontorsion_zsmul ha hk
    rw [hx0] at hord
    simp at hord
  have hnorm : ‖z‖ = 1 := norm_circlePhase (k • a)
  convert cesaro_powers_tendsto_zero z hz hnorm using 1
  funext N
  congr 2
  funext n
  rw [show k • ((n : ℤ) • a) = n • (k • a) by
    change k • ((n : ℤ) • a) = (n : ℤ) • (k • a)
    rw [smul_smul, smul_smul, mul_comm]]
  simp [z, circlePhase, AddCircle.toCircle_nsmul, Circle.coe_pow]


private theorem norm_sum_sq_le_card_mul_sum_sq_norm
    {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hnorm : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
  have hsq : (∑ i ∈ s, ‖f i‖) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 :=
    by
      simpa [mul_comm] using
        (Finset.sum_mul_sq_le_sq_mul_sq s
          (fun i ↦ ‖f i‖) (fun _ ↦ (1 : ℝ)))
  have hsum : 0 ≤ ∑ i ∈ s, ‖f i‖ :=
    Finset.sum_nonneg (fun i _ ↦ norm_nonneg (f i))
  nlinarith [norm_nonneg (∑ i ∈ s, f i)]

private theorem block_norm_expansion (u : ℕ → ℂ) (H N : ℕ) :
    (((∑ n ∈ Finset.range N,
        ‖∑ i ∈ Finset.range H, u (n + i)‖ ^ 2 : ℝ) : ℂ)) =
      ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        ∑ n ∈ Finset.range N, star (u (n + i)) * u (n + j) := by
  push_cast
  have hterm (z : ℂ) : (‖z‖ : ℂ) ^ 2 = star z * z := by
    calc
      (‖z‖ : ℂ) ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      _ = star z * z := by
        rw [Complex.sq_norm]
        simpa only [starRingEnd_apply] using
          Complex.normSq_eq_conj_mul_self (z := z)
  simp_rw [hterm, star_sum, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  rw [Finset.sum_comm]

private theorem norm_shifted_sum_le (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (i N : ℕ) :
    ‖∑ n ∈ Finset.range N, f (n + i)‖ ≤
      ‖∑ n ∈ Finset.range N, f n‖ + 2 * i := by
  have hshift :
      (∑ n ∈ Finset.range N, f (n + i)) -
          ∑ n ∈ Finset.range N, f n =
        (∑ n ∈ Finset.range i, f (N + n)) -
          ∑ n ∈ Finset.range i, f n := by
    have hi := Finset.sum_range_add f i N
    have hN := Finset.sum_range_add f N i
    simp_rw [Nat.add_comm i] at hi
    linear_combination -(hi) + hN
  calc
    ‖∑ n ∈ Finset.range N, f (n + i)‖ ≤
        ‖∑ n ∈ Finset.range N, f n‖ +
          ‖(∑ n ∈ Finset.range N, f (n + i)) -
            ∑ n ∈ Finset.range N, f n‖ := by
      have heq : (∑ n ∈ Finset.range N, f (n + i)) =
          (∑ n ∈ Finset.range N, f n) +
            ((∑ n ∈ Finset.range N, f (n + i)) -
              ∑ n ∈ Finset.range N, f n) := by ring
      calc
        ‖∑ n ∈ Finset.range N, f (n + i)‖ =
            ‖(∑ n ∈ Finset.range N, f n) +
              ((∑ n ∈ Finset.range N, f (n + i)) -
                ∑ n ∈ Finset.range N, f n)‖ := congrArg norm heq
        _ ≤ _ := norm_add_le _ _
    _ = ‖∑ n ∈ Finset.range N, f n‖ +
          ‖(∑ n ∈ Finset.range i, f (N + n)) -
            ∑ n ∈ Finset.range i, f n‖ := by rw [hshift]
    _ ≤ ‖∑ n ∈ Finset.range N, f n‖ +
          ((i : ℝ) + i) := by
      gcongr
      calc
        ‖(∑ n ∈ Finset.range i, f (N + n)) -
            ∑ n ∈ Finset.range i, f n‖ ≤
            ‖∑ n ∈ Finset.range i, f (N + n)‖ +
              ‖∑ n ∈ Finset.range i, f n‖ := norm_sub_le _ _
        _ ≤ (∑ _n ∈ Finset.range i, (1 : ℝ)) +
              ∑ _n ∈ Finset.range i, (1 : ℝ) := by
          gcongr
          · exact (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun n hn ↦ hf (N + n))
          · exact (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun n hn ↦ hf n)
        _ = (i : ℝ) + i := by simp
    _ = ‖∑ n ∈ Finset.range N, f n‖ + 2 * i := by ring

private theorem norm_sum_sub_shifted_sum_le (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (i N : ℕ) :
    ‖(∑ n ∈ Finset.range N, f n) -
        ∑ n ∈ Finset.range N, f (n + i)‖ ≤ 2 * i := by
  have hshift :
      (∑ n ∈ Finset.range N, f n) -
          ∑ n ∈ Finset.range N, f (n + i) =
        (∑ n ∈ Finset.range i, f n) -
          ∑ n ∈ Finset.range i, f (N + n) := by
    have hi := Finset.sum_range_add f i N
    have hN := Finset.sum_range_add f N i
    simp_rw [Nat.add_comm i] at hi
    linear_combination hi - hN
  rw [hshift]
  calc
    ‖(∑ n ∈ Finset.range i, f n) -
        ∑ n ∈ Finset.range i, f (N + n)‖ ≤
      ‖∑ n ∈ Finset.range i, f n‖ +
        ‖∑ n ∈ Finset.range i, f (N + n)‖ := norm_sub_le _ _
    _ ≤ (∑ _n ∈ Finset.range i, (1 : ℝ)) +
          ∑ _n ∈ Finset.range i, (1 : ℝ) := by
      gcongr
      · exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun n hn ↦ hf n)
      · exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun n hn ↦ hf (N + n))
    _ = 2 * i := by simp; ring

private theorem sum_Icc_one_eq_sum_range_succ
    (a : ℕ → ℝ) (H : ℕ) :
    (∑ h ∈ Finset.Icc 1 (H - 1), a h) =
      ∑ q ∈ Finset.range (H - 1), a (q + 1) := by
  symm
  apply Finset.sum_bij (fun q _ ↦ q + 1)
  · intro q hq
    simp only [Finset.mem_range] at hq
    simp only [Finset.mem_Icc]
    omega
  · intro q₁ hq₁ q₂ hq₂ heq
    omega
  · intro h hh
    simp only [Finset.mem_Icc] at hh
    refine ⟨h - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro q hq
    rfl

private theorem sum_initial_succ_le_sum_Icc
    (a : ℕ → ℝ) (ha : ∀ h, 0 ≤ a h)
    (H i : ℕ) (hH : 0 < H) (hi : i < H) :
    (∑ q ∈ Finset.range i, a (q + 1)) ≤
      ∑ h ∈ Finset.Icc 1 (H - 1), a h := by
  rw [sum_Icc_one_eq_sum_range_succ a H]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega))
    (fun q hq hnot ↦ ha (q + 1))

private theorem correlation_norm_bound (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (h n : ℕ) :
    ‖star (u n) * u (n + h)‖ ≤ 1 := by
  rw [norm_mul, norm_star]
  nlinarith [norm_nonneg (u n), norm_nonneg (u (n + h)),
    hu n, hu (n + h)]

private theorem upper_pair_re_le (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (N i j : ℕ) (hij : i < j) :
    (∑ n ∈ Finset.range N, star (u (n + i)) * u (n + j)).re ≤
      ‖∑ n ∈ Finset.range N, star (u n) * u (n + (j - i))‖ + 2 * i := by
  let f : ℕ → ℂ := fun n ↦ star (u n) * u (n + (j - i))
  have hterm (n : ℕ) :
      star (u (n + i)) * u (n + j) = f (n + i) := by
    simp only [f]
    rw [show n + i + (j - i) = n + j by omega]
  rw [show (∑ n ∈ Finset.range N,
      star (u (n + i)) * u (n + j)) =
        ∑ n ∈ Finset.range N, f (n + i) by
      apply Finset.sum_congr rfl
      intro n hn
      exact hterm n]
  exact (Complex.re_le_norm _).trans
    (norm_shifted_sum_le f
      (fun n ↦ correlation_norm_bound u hu (j - i) n) i N)

private theorem lower_pair_re_le (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (N i j : ℕ) (hji : j < i) :
    (∑ n ∈ Finset.range N, star (u (n + i)) * u (n + j)).re ≤
      ‖∑ n ∈ Finset.range N, star (u n) * u (n + (i - j))‖ + 2 * j := by
  have hconj :
      (∑ n ∈ Finset.range N, star (u (n + i)) * u (n + j)) =
        star (∑ n ∈ Finset.range N,
          star (u (n + j)) * u (n + i)) := by
    rw [star_sum]
    simp_rw [star_mul, star_star]
  rw [hconj]
  change (∑ n ∈ Finset.range N,
    star (u (n + j)) * u (n + i)).re ≤ _
  exact upper_pair_re_le u hu N j i hji

private theorem diagonal_pair_re_le (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (N i : ℕ) :
    (∑ n ∈ Finset.range N, star (u (n + i)) * u (n + i)).re ≤ N := by
  have hterm (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    calc
      (star z * z).re = (Complex.normSq z : ℂ).re := by
        rw [Complex.normSq_eq_conj_mul_self]
        rfl
      _ = Complex.normSq z := rfl
      _ = ‖z‖ ^ 2 := (Complex.sq_norm z).symm
  rw [← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply]
  simp_rw [hterm]
  calc
    (∑ n ∈ Finset.range N, ‖u (n + i)‖ ^ 2) ≤
        ∑ _n ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      nlinarith [norm_nonneg (u (n + i)), hu (n + i)]
    _ = N := by simp

private theorem lower_row_re_le (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (H N i : ℕ)
    (hH : 0 < H) (hi : i < H) :
    ∑ j ∈ Finset.range i,
        (∑ n ∈ Finset.range N,
          star (u (n + i)) * u (n + j)).re ≤
      (∑ h ∈ Finset.Icc 1 (H - 1),
        ‖∑ n ∈ Finset.range N, star (u n) * u (n + h)‖) +
        2 * H ^ 2 := by
  let a : ℕ → ℝ := fun h ↦
    ‖∑ n ∈ Finset.range N, star (u n) * u (n + h)‖
  have hpoint (j : ℕ) (hj : j ∈ Finset.range i) :
      (∑ n ∈ Finset.range N,
          star (u (n + i)) * u (n + j)).re ≤ a (i - j) + 2 * j := by
    exact lower_pair_re_le u hu N i j
      (by simpa only [Finset.mem_range] using hj)
  calc
    ∑ j ∈ Finset.range i,
        (∑ n ∈ Finset.range N,
          star (u (n + i)) * u (n + j)).re ≤
        ∑ j ∈ Finset.range i, (a (i - j) + 2 * j) :=
      Finset.sum_le_sum hpoint
    _ = (∑ j ∈ Finset.range i, a (i - j)) +
          ∑ j ∈ Finset.range i, (2 * j : ℝ) := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ h ∈ Finset.Icc 1 (H - 1), a h) + 2 * H ^ 2 := by
      apply add_le_add
      · calc
          (∑ j ∈ Finset.range i, a (i - j)) =
              ∑ q ∈ Finset.range i, a (q + 1) := by
            rw [← Finset.sum_range_reflect (fun q ↦ a (q + 1)) i]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Finset.mem_range] at hj
            congr 2
            omega
          _ ≤ ∑ h ∈ Finset.Icc 1 (H - 1), a h :=
            sum_initial_succ_le_sum_Icc a (fun h ↦ norm_nonneg _) H i hH hi
      · calc
          (∑ j ∈ Finset.range i, (2 * j : ℝ)) ≤
              ∑ _j ∈ Finset.range i, (2 * H : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            simp only [Finset.mem_range] at hj
            norm_num
            exact_mod_cast (le_of_lt (hj.trans hi))
          _ ≤ 2 * H ^ 2 := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            have hiR : (i : ℝ) ≤ H := by exact_mod_cast hi.le
            nlinarith [show (0 : ℝ) ≤ H by positivity]
    _ = _ := rfl

private theorem upper_row_re_le (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (H N i : ℕ)
    (hH : 0 < H) (hi : i < H) :
    ∑ q ∈ Finset.range (H - i - 1),
        (∑ n ∈ Finset.range N,
          star (u (n + i)) * u (n + (i + 1 + q))).re ≤
      (∑ h ∈ Finset.Icc 1 (H - 1),
        ‖∑ n ∈ Finset.range N, star (u n) * u (n + h)‖) +
        2 * H ^ 2 := by
  let a : ℕ → ℝ := fun h ↦
    ‖∑ n ∈ Finset.range N, star (u n) * u (n + h)‖
  have hlen : H - i - 1 < H := by omega
  have hpoint (q : ℕ) (hq : q ∈ Finset.range (H - i - 1)) :
      (∑ n ∈ Finset.range N,
          star (u (n + i)) * u (n + (i + 1 + q))).re ≤
        a (q + 1) + 2 * i := by
    have hij : i < i + 1 + q := by omega
    simpa only [a, show i + 1 + q - i = q + 1 by omega] using
      upper_pair_re_le u hu N i (i + 1 + q) hij
  calc
    ∑ q ∈ Finset.range (H - i - 1),
        (∑ n ∈ Finset.range N,
          star (u (n + i)) * u (n + (i + 1 + q))).re ≤
        ∑ q ∈ Finset.range (H - i - 1), (a (q + 1) + 2 * i) :=
      Finset.sum_le_sum hpoint
    _ = (∑ q ∈ Finset.range (H - i - 1), a (q + 1)) +
          ∑ _q ∈ Finset.range (H - i - 1), (2 * i : ℝ) := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ h ∈ Finset.Icc 1 (H - 1), a h) + 2 * H ^ 2 := by
      apply add_le_add
      · exact sum_initial_succ_le_sum_Icc a (fun h ↦ norm_nonneg _)
          H (H - i - 1) hH hlen
      · calc
          (∑ _q ∈ Finset.range (H - i - 1), (2 * i : ℝ)) ≤
              ∑ _q ∈ Finset.range (H - i - 1), (2 * H : ℝ) := by
            apply Finset.sum_le_sum
            intro q hq
            norm_num
            exact_mod_cast hi.le
          _ ≤ 2 * H ^ 2 := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            have hlenR : ((H - i - 1 : ℕ) : ℝ) ≤ H := by
              exact_mod_cast (Nat.sub_le H (i + 1))
            nlinarith [show (0 : ℝ) ≤ H by positivity]
    _ = _ := rfl

private theorem row_re_le (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (H N i : ℕ)
    (hH : 0 < H) (hi : i < H) :
    ∑ j ∈ Finset.range H,
        (∑ n ∈ Finset.range N,
          star (u (n + i)) * u (n + j)).re ≤
      N + 2 * (∑ h ∈ Finset.Icc 1 (H - 1),
        ‖∑ n ∈ Finset.range N, star (u n) * u (n + h)‖) +
        4 * H ^ 2 := by
  let F : ℕ → ℝ := fun j ↦
    (∑ n ∈ Finset.range N,
      star (u (n + i)) * u (n + j)).re
  have hsplit :
      (∑ j ∈ Finset.range H, F j) =
        (∑ j ∈ Finset.range i, F j) + F i +
          ∑ q ∈ Finset.range (H - i - 1), F (i + 1 + q) := by
    calc
      (∑ j ∈ Finset.range H, F j) =
          ∑ j ∈ Finset.range (i + (H - i)), F j := by
        congr 3
        omega
      _ = (∑ j ∈ Finset.range i, F j) +
          ∑ q ∈ Finset.range (H - i), F (i + q) :=
        Finset.sum_range_add F i (H - i)
      _ = (∑ j ∈ Finset.range i, F j) +
          (∑ q ∈ Finset.range 1, F (i + q) +
            ∑ q ∈ Finset.range (H - i - 1), F (i + (1 + q))) := by
        congr 1
        rw [← Finset.sum_range_add]
        congr 3
        omega
      _ = (∑ j ∈ Finset.range i, F j) + F i +
          ∑ q ∈ Finset.range (H - i - 1), F (i + 1 + q) := by
        simp only [Finset.sum_range_one, Nat.add_zero, add_assoc]
  rw [hsplit]
  have hlo := lower_row_re_le u hu H N i hH hi
  have hdiag := diagonal_pair_re_le u hu N i
  have hup := upper_row_re_le u hu H N i hH hi
  dsimp only [F] at hlo hdiag hup ⊢
  nlinarith

private theorem block_re_le (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (H N : ℕ) (hH : 0 < H) :
    ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        (∑ n ∈ Finset.range N,
          star (u (n + i)) * u (n + j)).re ≤
      H * N + 2 * H * (∑ h ∈ Finset.Icc 1 (H - 1),
        ‖∑ n ∈ Finset.range N, star (u n) * u (n + h)‖) +
        4 * H ^ 3 := by
  calc
    ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        (∑ n ∈ Finset.range N,
          star (u (n + i)) * u (n + j)).re ≤
      ∑ _i ∈ Finset.range H,
        ((N : ℝ) + 2 * (∑ h ∈ Finset.Icc 1 (H - 1),
          ‖∑ n ∈ Finset.range N, star (u n) * u (n + h)‖) +
          4 * H ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact row_re_le u hu H N i hH
        (by simpa only [Finset.mem_range] using hi)
    _ = H * N + 2 * H * (∑ h ∈ Finset.Icc 1 (H - 1),
        ‖∑ n ∈ Finset.range N, star (u n) * u (n + h)‖) +
        4 * H ^ 3 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

private theorem block_norm_sum_le (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (H N : ℕ) (hH : 0 < H) :
    (∑ n ∈ Finset.range N,
        ‖∑ i ∈ Finset.range H, u (n + i)‖ ^ 2 : ℝ) ≤
      H * N + 2 * H * (∑ h ∈ Finset.Icc 1 (H - 1),
        ‖∑ n ∈ Finset.range N, star (u n) * u (n + h)‖) +
        4 * H ^ 3 := by
  have hexpand := congrArg Complex.re (block_norm_expansion u H N)
  change (∑ n ∈ Finset.range N,
      ‖∑ i ∈ Finset.range H, u (n + i)‖ ^ 2 : ℝ) =
    (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
      ∑ n ∈ Finset.range N,
        star (u (n + i)) * u (n + j)).re at hexpand
  rw [← Complex.reCLM_apply, map_sum] at hexpand
  simp only [Complex.reCLM_apply] at hexpand
  simp_rw [← Complex.reCLM_apply, map_sum, Complex.reCLM_apply] at hexpand
  rw [hexpand]
  have hcollapse :
      (∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
        ∑ n ∈ Finset.range N,
          (star (u (n + i)) * u (n + j)).re) =
        ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
          (∑ n ∈ Finset.range N,
            star (u (n + i)) * u (n + j)).re := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Complex.reCLM_apply, map_sum]
    rfl
  rw [hcollapse]
  exact block_re_le u hu H N hH

private theorem block_sum_norm_le (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (H N : ℕ) :
    ‖∑ n ∈ Finset.range N, ∑ i ∈ Finset.range H, u (n + i)‖ ≤
      H * N := by
  calc
    ‖∑ n ∈ Finset.range N, ∑ i ∈ Finset.range H, u (n + i)‖ ≤
        ∑ n ∈ Finset.range N,
          ∑ i ∈ Finset.range H, ‖u (n + i)‖ := by
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun n hn ↦ norm_sum_le _ _)
    _ ≤ ∑ _n ∈ Finset.range N,
          ∑ _i ∈ Finset.range H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact Finset.sum_le_sum fun i hi ↦ hu (n + i)
    _ = H * N := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

private theorem mul_norm_sum_le_norm_block_sum_add (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (H N : ℕ) :
    H * ‖∑ n ∈ Finset.range N, u n‖ ≤
      ‖∑ n ∈ Finset.range N, ∑ i ∈ Finset.range H, u (n + i)‖ +
        2 * H ^ 2 := by
  let S : ℂ := ∑ n ∈ Finset.range N, u n
  let B : ℂ := ∑ n ∈ Finset.range N,
    ∑ i ∈ Finset.range H, u (n + i)
  have hid : (H : ℂ) * S - B =
      ∑ i ∈ Finset.range H,
        (S - ∑ n ∈ Finset.range N, u (n + i)) := by
    dsimp only [S, B]
    rw [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_comm]
    simp only [Finset.card_range, nsmul_eq_mul]
  have hdiff : ‖(H : ℂ) * S - B‖ ≤ 2 * H ^ 2 := by
    rw [hid]
    calc
      ‖∑ i ∈ Finset.range H,
          (S - ∑ n ∈ Finset.range N, u (n + i))‖ ≤
          ∑ i ∈ Finset.range H,
            ‖S - ∑ n ∈ Finset.range N, u (n + i)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range H, (2 * H : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (norm_sum_sub_shifted_sum_le u hu i N).trans
          (by
            simp only [Finset.mem_range] at hi
            norm_num
            exact_mod_cast hi.le)
      _ = 2 * H ^ 2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  calc
    H * ‖∑ n ∈ Finset.range N, u n‖ = ‖(H : ℂ) * S‖ := by
      rw [norm_mul, norm_natCast]
    _ ≤ ‖B‖ + ‖(H : ℂ) * S - B‖ := by
      have heq : (H : ℂ) * S = B + ((H : ℂ) * S - B) := by ring
      calc
        ‖(H : ℂ) * S‖ = ‖B + ((H : ℂ) * S - B)‖ :=
          congrArg norm heq
        _ ≤ _ := norm_add_le _ _
    _ ≤ ‖B‖ + 2 * H ^ 2 := by gcongr
    _ = _ := rfl

private theorem mul_sq_norm_sum_le_sq_norm_block_sum_add (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (H N : ℕ) :
    H ^ 2 * ‖∑ n ∈ Finset.range N, u n‖ ^ 2 ≤
      ‖∑ n ∈ Finset.range N, ∑ i ∈ Finset.range H, u (n + i)‖ ^ 2 +
        4 * H ^ 3 * N + 4 * H ^ 4 := by
  have hmain := mul_norm_sum_le_norm_block_sum_add u hu H N
  have hB := block_sum_norm_le u hu H N
  have hH0 : (0 : ℝ) ≤ H := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hS0 : 0 ≤ ‖∑ n ∈ Finset.range N, u n‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖∑ n ∈ Finset.range N,
      ∑ i ∈ Finset.range H, u (n + i)‖ := norm_nonneg _
  have hx0 : 0 ≤ H * ‖∑ n ∈ Finset.range N, u n‖ :=
    mul_nonneg hH0 hS0
  have hy0 : 0 ≤ ‖∑ n ∈ Finset.range N,
      ∑ i ∈ Finset.range H, u (n + i)‖ + 2 * H ^ 2 := by positivity
  have hsquare := (sq_le_sq₀ hx0 hy0).2 hmain
  have hcross :
      4 * H ^ 2 * ‖∑ n ∈ Finset.range N,
          ∑ i ∈ Finset.range H, u (n + i)‖ ≤
        4 * H ^ 3 * N := by
    calc
      4 * H ^ 2 * ‖∑ n ∈ Finset.range N,
          ∑ i ∈ Finset.range H, u (n + i)‖ ≤
          4 * H ^ 2 * (H * N) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      _ = 4 * H ^ 3 * N := by ring
  nlinarith

private theorem vanDerCorput_finite (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ 1) (H N : ℕ)
    (hH : 0 < H) (hN : 0 < N) :
    ‖cesaroAverage u N‖ ^ 2 ≤
      (1 : ℝ) / H + (2 / H) *
        ∑ h ∈ Finset.Icc 1 (H - 1),
          ‖cesaroAverage (fun n ↦ star (u n) * u (n + h)) N‖ +
        8 * H / N + 4 * H ^ 2 / N ^ 2 := by
  let S : ℂ := ∑ n ∈ Finset.range N, u n
  let B : ℂ := ∑ n ∈ Finset.range N,
    ∑ i ∈ Finset.range H, u (n + i)
  let C : ℝ := ∑ h ∈ Finset.Icc 1 (H - 1),
    ‖∑ n ∈ Finset.range N, star (u n) * u (n + h)‖
  have hmove := mul_sq_norm_sum_le_sq_norm_block_sum_add u hu H N
  have hcauchy : ‖B‖ ^ 2 ≤ N *
      ∑ n ∈ Finset.range N,
        ‖∑ i ∈ Finset.range H, u (n + i)‖ ^ 2 := by
    dsimp only [B]
    simpa only [Finset.card_range, Nat.cast_id] using
      norm_sum_sq_le_card_mul_sum_sq_norm (Finset.range N)
        (fun n ↦ ∑ i ∈ Finset.range H, u (n + i))
  have hblock := block_norm_sum_le u hu H N hH
  have hblock' : (N : ℝ) *
      (∑ n ∈ Finset.range N,
        ‖∑ i ∈ Finset.range H, u (n + i)‖ ^ 2) ≤
      N * (H * N + 2 * H * C + 4 * H ^ 3) := by
    exact mul_le_mul_of_nonneg_left (by simpa only [C] using hblock)
      (by positivity)
  have htotal : (H : ℝ) ^ 2 * ‖S‖ ^ 2 ≤
      H * N ^ 2 + 2 * H * N * C + 8 * H ^ 3 * N + 4 * H ^ 4 := by
    calc
      (H : ℝ) ^ 2 * ‖S‖ ^ 2 ≤
          ‖B‖ ^ 2 + 4 * H ^ 3 * N + 4 * H ^ 4 := by
        simpa only [S, B] using hmove
      _ ≤ N * (∑ n ∈ Finset.range N,
          ‖∑ i ∈ Finset.range H, u (n + i)‖ ^ 2) +
            4 * H ^ 3 * N + 4 * H ^ 4 := by gcongr
      _ ≤ N * (H * N + 2 * H * C + 4 * H ^ 3) +
            4 * H ^ 3 * N + 4 * H ^ 4 := by gcongr
      _ = H * N ^ 2 + 2 * H * N * C +
            8 * H ^ 3 * N + 4 * H ^ 4 := by ring
  have hHne : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have havg : ‖cesaroAverage u N‖ ^ 2 = ‖S‖ ^ 2 / N ^ 2 := by
    rw [cesaroAverage]
    dsimp only [S]
    rw [norm_mul, norm_inv, norm_natCast]
    field_simp
  have hcorr (h : ℕ) :
      ‖cesaroAverage (fun n ↦ star (u n) * u (n + h)) N‖ =
        ‖∑ n ∈ Finset.range N, star (u n) * u (n + h)‖ / N := by
    rw [cesaroAverage, norm_mul, norm_inv, norm_natCast]
    field_simp
  have hcancel : (H : ℝ) * ‖S‖ ^ 2 ≤
      N ^ 2 + 2 * N * C + 8 * H ^ 2 * N + 4 * H ^ 3 := by
    apply le_of_mul_le_mul_left ?_ (show (0 : ℝ) < H by exact_mod_cast hH)
    calc
      (H : ℝ) * (H * ‖S‖ ^ 2) = H ^ 2 * ‖S‖ ^ 2 := by ring
      _ ≤ H * N ^ 2 + 2 * H * N * C + 8 * H ^ 3 * N + 4 * H ^ 4 := htotal
      _ = H * (N ^ 2 + 2 * N * C + 8 * H ^ 2 * N + 4 * H ^ 3) := by ring
  rw [havg]
  simp_rw [hcorr]
  dsimp only [C] at hcancel
  rw [← Finset.sum_div] 
  field_simp
  nlinarith [hcancel]


private theorem norm_cesaroAverage_le_one_vdc
    (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) (N : ℕ) :
    ‖cesaroAverage u N‖ ≤ 1 := by
  by_cases hN : N = 0
  · simp [hN, cesaroAverage]
  rw [cesaroAverage, norm_mul, norm_inv, norm_natCast]
  calc
    (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, u n‖ ≤
        (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, (1 : ℝ) := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ hu n)
    _ = 1 := by simp [hN]

/-- A Cesàro van der Corput bound in terms of finitely many correlation limsups. -/
theorem vanDerCorput_cesaro
    (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) (H : ℕ) (hH : 0 < H) :
  Filter.limsup (fun N ↦ ‖cesaroAverage u N‖ ^ 2) Filter.atTop ≤
    (2 : ℝ) / H + (2 / H) *
      ∑ h ∈ Finset.Icc 1 (H - 1),
        Filter.limsup
          (fun N ↦ ‖cesaroAverage
            (fun n ↦ star (u n) * u (n + h)) N‖)
          Filter.atTop := by
  let s := Finset.Icc 1 (H - 1)
  let a : ℕ → ℕ → ℝ := fun h N ↦
    ‖cesaroAverage (fun n ↦ star (u n) * u (n + h)) N‖
  let L : ℕ → ℝ := fun h ↦ Filter.limsup (a h) Filter.atTop
  let R : ℝ := (2 : ℝ) / H + (2 / H) * ∑ h ∈ s, L h
  have huavg (N : ℕ) : ‖cesaroAverage u N‖ ≤ 1 :=
    norm_cesaroAverage_le_one_vdc u hu N
  have ha_nonneg (h N : ℕ) : 0 ≤ a h N := norm_nonneg _
  have ha_le (h N : ℕ) : a h N ≤ 1 := by
    apply norm_cesaroAverage_le_one_vdc
    intro n
    rw [norm_mul, norm_star]
    nlinarith [norm_nonneg (u n), norm_nonneg (u (n + h)), hu n, hu (n + h)]
  have hmain : Filter.limsup (fun N ↦ ‖cesaroAverage u N‖ ^ 2)
      Filter.atTop ≤ R := by
    apply (Filter.limsup_le_iff
      (f := Filter.atTop) (u := fun N ↦ ‖cesaroAverage u N‖ ^ 2)
      (x := R)
      (h₁ := Filter.isCoboundedUnder_le_of_le _
        (fun N ↦ sq_nonneg ‖cesaroAverage u N‖))
      (h₂ := Filter.isBoundedUnder_of_eventually_le (a := (1 : ℝ))
        (Filter.Eventually.of_forall fun N ↦ by
          have h := huavg N
          nlinarith [norm_nonneg (cesaroAverage u N)]))).2
    intro y hy
    let gap : ℝ := y - R
    have hgap : 0 < gap := sub_pos.mpr hy
    let delta : ℝ := gap / 4
    have hdelta : 0 < delta := div_pos hgap (by norm_num)
    have ha_event (h : ℕ) : ∀ᶠ N in Filter.atTop, a h N < L h + delta := by
      exact ((Filter.limsup_le_iff
        (f := Filter.atTop) (u := a h) (x := L h)
        (h₁ := Filter.isCoboundedUnder_le_of_le _ (ha_nonneg h))
        (h₂ := Filter.isBoundedUnder_of_eventually_le (a := (1 : ℝ))
          (Filter.Eventually.of_forall (ha_le h)))).1 le_rfl)
        (L h + delta) (by linarith)
    have hall : ∀ᶠ N in Filter.atTop, ∀ h ∈ s, a h N ≤ L h + delta := by
      rw [Filter.eventually_all_finset]
      intro h hh
      exact (ha_event h).mono (fun N hN ↦ hN.le)
    have hinv : Filter.Tendsto (fun N : ℕ ↦ (1 : ℝ) / N)
        Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
    have herrlim : Filter.Tendsto
        (fun N : ℕ ↦ (8 : ℝ) * H / N + 4 * H ^ 2 / N ^ 2)
        Filter.atTop (nhds 0) := by
      have h₁ := hinv.const_mul ((8 : ℝ) * H)
      have h₂ := (hinv.mul hinv).const_mul ((4 : ℝ) * H ^ 2)
      convert h₁.add h₂ using 1
      · funext N
        simp only [one_div]
        ring
      · simp
    have herr : ∀ᶠ N : ℕ in Filter.atTop,
        (8 : ℝ) * H / N + 4 * H ^ 2 / N ^ 2 < gap / 4 :=
      (Metric.tendsto_nhds.mp herrlim (gap / 4) hdelta) |>.mono
        (fun N hN ↦ by
          rw [Real.dist_eq, sub_zero, abs_lt] at hN
          exact hN.2)
    have hNpos : ∀ᶠ N in Filter.atTop, 0 < N :=
      Filter.eventually_ge_atTop 1
    filter_upwards [hall, herr, hNpos] with N hallN herrN hNpos
    have hfinite := vanDerCorput_finite u hu H N hH hNpos
    have hsum : ∑ h ∈ s, a h N ≤ ∑ h ∈ s, L h + (s.card : ℝ) * delta := by
      calc
        ∑ h ∈ s, a h N ≤ ∑ h ∈ s, (L h + delta) :=
          Finset.sum_le_sum fun h hh ↦ hallN h hh
        _ = ∑ h ∈ s, L h + (s.card : ℝ) * delta := by
          rw [Finset.sum_add_distrib]
          simp
    have hcard : (s.card : ℝ) ≤ H := by
      have hcardNat : s.card ≤ H := by
        calc
          s.card ≤ (Finset.range H).card := Finset.card_le_card
            (show s ⊆ Finset.range H by
              intro h hh
              simp only [s, Finset.mem_Icc] at hh
              simp only [Finset.mem_range]
              omega)
          _ = H := Finset.card_range H
      exact_mod_cast hcardNat
    have hcoef : 0 ≤ (2 : ℝ) / H := by positivity
    have hsum' : (2 / (H : ℝ)) * ∑ h ∈ s, a h N ≤
        (2 / H) * ∑ h ∈ s, L h + gap / 2 := by
      calc
        (2 / (H : ℝ)) * ∑ h ∈ s, a h N ≤
            (2 / H) * (∑ h ∈ s, L h + (s.card : ℝ) * delta) :=
          mul_le_mul_of_nonneg_left hsum hcoef
        _ ≤ (2 / H) * ∑ h ∈ s, L h + 2 * delta := by
          have hHR : (0 : ℝ) < H := by exact_mod_cast hH
          have hdelta0 : 0 ≤ delta := hdelta.le
          calc
            _ = (2 / H) * ∑ h ∈ s, L h +
                ((2 / H) * (s.card : ℝ)) * delta := by ring
            _ ≤ (2 / H) * ∑ h ∈ s, L h + 2 * delta := by
              gcongr
              calc
                (2 / H) * (s.card : ℝ) ≤ (2 / H) * H :=
                  mul_le_mul_of_nonneg_left hcard (by positivity)
                _ = 2 := by field_simp
        _ = _ := by simp only [delta, gap]; ring
    have hsum'' : (2 / (H : ℝ)) * ∑ h ∈ Finset.Icc 1 (H - 1),
          ‖cesaroAverage (fun n ↦ star (u n) * u (n + h)) N‖ ≤
        (2 / H) * ∑ h ∈ s, L h + gap / 2 := by
      simpa only [s, a] using hsum'
    calc
      ‖cesaroAverage u N‖ ^ 2 ≤
          (1 : ℝ) / H + (2 / H) * ∑ h ∈ s, L h + gap / 2 +
            ((8 : ℝ) * H / N + 4 * H ^ 2 / N ^ 2) := by
        linarith
      _ < y := by
        dsimp only [gap, R] at hgap herrN ⊢
        have hinvH : 0 < (1 : ℝ) / H := by positivity
        have hsplit : (2 : ℝ) / H = 1 / H + 1 / H := by ring
        rw [hsplit] at hgap herrN ⊢
        nlinarith
  simpa only [R, s, L, a] using hmain

private theorem sum_range_blocks (f : ℕ → ℂ) (H q : ℕ) :
    (∑ n ∈ Finset.range (H * q), f n) =
      ∑ a : Fin H, ∑ t ∈ Finset.range q, f (H * t + (a : ℕ)) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      simp_rw [Finset.sum_range_succ]
      rw [Finset.sum_add_distrib]
      congr 1
      exact (Fin.sum_univ_eq_sum_range
        (fun x ↦ f (H * q + x)) H).symm

private theorem sum_range_blocks_add (f : ℕ → ℂ)
    (H q b : ℕ) :
    (∑ n ∈ Finset.range (H * q + b), f n) =
      (∑ a : Fin H, ∑ t ∈ Finset.range q,
        f (H * t + (a : ℕ))) +
      ∑ a ∈ Finset.range b, f (H * q + a) := by
  rw [Finset.sum_range_add, sum_range_blocks]

private theorem cesaro_term_identity (f : ℕ → ℂ)
    (H q a : ℕ) :
    (((q + 1 : ℕ) : ℂ) *
        cesaroAverage (fun t ↦ f (H * t + a)) (q + 1) -
      (q : ℂ) * cesaroAverage (fun t ↦ f (H * t + a)) q) =
        f (H * q + a) := by
  by_cases hq : q = 0
  · simp [hq, cesaroAverage]
  simp only [cesaroAverage, Finset.sum_range_succ, Nat.cast_add,
    Nat.cast_one]
  rw [mul_inv_cancel_left₀ (by exact_mod_cast Nat.succ_ne_zero q),
    mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr hq)]
  ring

private theorem residue_ratio_tendsto (H b : ℕ) (hH : 0 < H) :
    Filter.Tendsto
      (fun q : ℕ ↦ ((H * q + b : ℕ) : ℂ)⁻¹ * (q : ℂ))
      Filter.atTop (nhds (H : ℂ)⁻¹) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds
    (0 : ℂ) b 1 (d := H) (by exact_mod_cast hH.ne')
  convert h using 1 <;> simp [div_eq_mul_inv, mul_comm, add_comm]

private theorem residue_ratio_succ_tendsto (H b : ℕ) (hH : 0 < H) :
    Filter.Tendsto
      (fun q : ℕ ↦ ((H * q + b : ℕ) : ℂ)⁻¹ *
        ((q + 1 : ℕ) : ℂ))
      Filter.atTop (nhds (H : ℂ)⁻¹) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds
    (1 : ℂ) b 1 (d := H) (by exact_mod_cast hH.ne')
  convert h using 1 <;>
    simp [div_eq_mul_inv, mul_comm, add_comm, Nat.cast_add]

private theorem cesaro_residue_term_tendsto_zero
    (f : ℕ → ℂ) (H b : ℕ) (hH : 0 < H)
    (a : Fin H) (z : ℂ)
    (hlim : Filter.Tendsto
      (fun N ↦ cesaroAverage (fun t ↦ f (H * t + (a : ℕ))) N)
      Filter.atTop (nhds z)) :
    Filter.Tendsto
      (fun q ↦ ((H * q + b : ℕ) : ℂ)⁻¹ *
        f (H * q + (a : ℕ))) Filter.atTop (nhds 0) := by
  have hlimSucc := hlim.comp (Filter.tendsto_add_atTop_nat 1)
  have hprodSucc := (residue_ratio_succ_tendsto H b hH).mul hlimSucc
  have hprod := (residue_ratio_tendsto H b hH).mul hlim
  have hsub := hprodSucc.sub hprod
  convert hsub using 1
  · funext q
    rw [← cesaro_term_identity f H q (a : ℕ)]
    simp only [Function.comp_apply, Nat.add_comm]
    rw [mul_sub]
    ring_nf
  · ring_nf

private theorem cesaro_residue_fixed_remainder
    (f : ℕ → ℂ) (H : ℕ) (hH : 0 < H)
    (z₀ : Fin H → ℂ)
    (hlim : ∀ a : Fin H, Filter.Tendsto
      (fun N ↦ cesaroAverage (fun t ↦ f (H * t + (a : ℕ))) N)
      Filter.atTop (nhds (z₀ a)))
    (b : Fin H) :
    Filter.Tendsto
      (fun q ↦ cesaroAverage f (H * q + (b : ℕ)))
      Filter.atTop (nhds ((H : ℂ)⁻¹ * ∑ a, z₀ a)) := by
  have hsumlim : Filter.Tendsto
      (fun q ↦ ∑ a : Fin H,
        cesaroAverage (fun t ↦ f (H * t + (a : ℕ))) q)
      Filter.atTop (nhds (∑ a : Fin H, z₀ a)) := by
    simpa using tendsto_finsetSum Finset.univ
      (fun a _ ↦ hlim a)
  have hmain := (residue_ratio_tendsto H (b : ℕ) hH).mul hsumlim
  have hrem : Filter.Tendsto
      (fun q ↦ ∑ a ∈ Finset.range (b : ℕ),
        ((H * q + (b : ℕ) : ℕ) : ℂ)⁻¹ * f (H * q + a))
      Filter.atTop (nhds 0) := by
    have hs : Filter.Tendsto
        (fun q ↦ ∑ a ∈ Finset.range (b : ℕ),
          ((H * q + (b : ℕ) : ℕ) : ℂ)⁻¹ * f (H * q + a))
        Filter.atTop (nhds (∑ _a ∈ Finset.range (b : ℕ), (0 : ℂ))) := by
      apply tendsto_finsetSum (Finset.range (b : ℕ))
      intro a ha
      exact cesaro_residue_term_tendsto_zero f H (b : ℕ) hH
        ⟨a, lt_of_lt_of_le (Finset.mem_range.mp ha) b.isLt.le⟩ (z₀ ⟨a,
          lt_of_lt_of_le (Finset.mem_range.mp ha) b.isLt.le⟩)
        (hlim ⟨a, lt_of_lt_of_le (Finset.mem_range.mp ha) b.isLt.le⟩)
    simpa using hs
  have hadd := hmain.add hrem
  convert hadd using 1
  · funext q
    by_cases hq : q = 0
    · subst q
      simp only [cesaroAverage, Nat.mul_zero, zero_add, Nat.cast_zero,
        Finset.sum_range_zero]
      rw [Finset.mul_sum]
      simp
    rw [cesaroAverage, sum_range_blocks_add]
    simp_rw [show ∀ a : Fin H,
        ∑ t ∈ Finset.range q, f (H * t + (a : ℕ)) =
          (q : ℂ) * cesaroAverage
            (fun t ↦ f (H * t + (a : ℕ))) q by
      intro a
      simp [cesaroAverage, hq]]
    rw [mul_add]
    simp only [Finset.mul_sum]
    simp [mul_assoc]
  · ring_nf

/-- Cesàro limits on all residue classes recombine into the corresponding uniform average. -/
theorem cesaroAverage_of_residue_classes
    (f : ℕ → ℂ) (H : ℕ) (hH : 0 < H) (z₀ : Fin H → ℂ)
    (hlim : ∀ a : Fin H, Filter.Tendsto
      (fun N ↦ cesaroAverage (fun t ↦ f (H * t + (a : ℕ))) N)
      Filter.atTop (nhds (z₀ a))) :
  Filter.Tendsto (fun N ↦ cesaroAverage f N) Filter.atTop
    (nhds ((H : ℂ)⁻¹ * ∑ a, z₀ a)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have hall : ∀ᶠ q in Filter.atTop, ∀ b : Fin H,
      dist (cesaroAverage f (H * q + (b : ℕ)))
        ((H : ℂ)⁻¹ * ∑ a, z₀ a) < eps := by
    rw [Filter.eventually_all]
    intro b
    exact (Metric.tendsto_nhds.mp
      (cesaro_residue_fixed_remainder f H hH z₀ hlim b) eps heps)
  have hdiv : Filter.Tendsto (fun N ↦ N / H)
      Filter.atTop Filter.atTop := Nat.tendsto_div_const_atTop hH.ne'
  filter_upwards [hdiv.eventually hall] with N hN
  let b : Fin H := ⟨N % H, Nat.mod_lt _ hH⟩
  have hdecomp : H * (N / H) + (b : ℕ) = N := by
    dsimp [b]
    exact Nat.div_add_mod N H
  simpa [hdecomp] using hN b

private def shiftDifference (P : CirclePolynomial d) (h : ℤ) :
    CirclePolynomial d :=
  ⟨fun j ↦
    (∑ i : Fin (d + 1),
      ((Nat.choose (i : ℕ) (j : ℕ) : ℤ) * h ^ ((i : ℕ) - (j : ℕ))) •
        P.coeff i) - P.coeff j⟩

private theorem extended_add_pow (n h : ℤ) (i : Fin (d + 1)) :
    (n + h) ^ (i : ℕ) =
      ∑ j : Fin (d + 1),
        n ^ (j : ℕ) * h ^ ((i : ℕ) - (j : ℕ)) *
          (Nat.choose (i : ℕ) (j : ℕ) : ℤ) := by
  rw [add_pow]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ n ^ j * h ^ ((i : ℕ) - j) *
      (Nat.choose (i : ℕ) j : ℤ)) (d + 1)]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.le_of_lt_succ i.isLt)))
  intro j hj hnot
  have hij : (i : ℕ) < j := by
    simp only [Finset.mem_range] at hnot
    omega
  rw [Nat.choose_eq_zero_of_lt hij]
  simp

private theorem shiftDifference_eval (P : CirclePolynomial d) (h n : ℤ) :
    shiftDifference P h n = P (n + h) - P n := by
  rw [CirclePolynomial.eval, CirclePolynomial.eval, CirclePolynomial.eval]
  simp only [shiftDifference, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum,
    smul_smul]
  rw [sub_left_inj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [extended_add_pow n h i, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

private theorem shiftDifference_coeff_above
    (P : CirclePolynomial d) (h : ℤ) (r j : Fin (d + 1))
    (hrj : (r : ℕ) ≤ (j : ℕ))
    (habove : ∀ i : Fin (d + 1),
      (r : ℕ) < (i : ℕ) → P.coeff i = 0) :
    (shiftDifference P h).coeff j = 0 := by
  change (∑ i : Fin (d + 1),
      ((Nat.choose (i : ℕ) (j : ℕ) : ℤ) * h ^ ((i : ℕ) - (j : ℕ))) •
        P.coeff i) - P.coeff j = 0
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · rw [Nat.choose_eq_zero_of_lt hijlt]
      simp
    · rw [habove i (lt_of_le_of_lt hrj hjilt)]
      simp
  · simp

private theorem shiftDifference_coeff_pred
    (P : CirclePolynomial d) (h : ℤ) (r j : Fin (d + 1))
    (hrj : (r : ℕ) = (j : ℕ) + 1)
    (habove : ∀ i : Fin (d + 1),
      (r : ℕ) < (i : ℕ) → P.coeff i = 0) :
    (shiftDifference P h).coeff j =
      (((r : ℕ) : ℤ) * h) • P.coeff r := by
  change (∑ i : Fin (d + 1),
      ((Nat.choose (i : ℕ) (j : ℕ) : ℤ) * h ^ ((i : ℕ) - (j : ℕ))) •
        P.coeff i) - P.coeff j = _
  have hrne : r ≠ j := by
    intro e
    have := congrArg Fin.val e
    omega
  have hjmem : j ∈ (Finset.univ : Finset (Fin (d + 1))) := Finset.mem_univ j
  rw [← Finset.sum_erase_add _ _ hjmem]
  have hrmem : r ∈ (Finset.univ.erase j : Finset (Fin (d + 1))) := by
    simp [hrne]
  rw [Finset.sum_eq_single r]
  · simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
      pow_zero, one_smul]
    rw [hrj, Nat.choose_succ_self_right]
    have hsub : (j : ℕ) + 1 - (j : ℕ) = 1 := by omega
    rw [hsub, pow_one]
    push_cast
    abel
  · intro i hi hir
    have hij : i ≠ j := by simpa using hi
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with hijlt | hijEq | hjilt
    · rw [Nat.choose_eq_zero_of_lt hijlt]
      simp
    · exact (hij (Fin.ext hijEq)).elim
    · have hri : (r : ℕ) < (i : ℕ) := by
        have hne : (i : ℕ) ≠ (r : ℕ) := fun e ↦ hir (Fin.ext e)
        omega
      rw [habove i hri]
      simp
  · exact fun hnot ↦ (hnot hrmem).elim

private def affineRestriction (P : CirclePolynomial d)
    (k H a : ℤ) : CirclePolynomial d :=
  ⟨fun j ↦
    ∑ i : Fin (d + 1),
      (k * (Nat.choose (i : ℕ) (j : ℕ) : ℤ) *
        H ^ (j : ℕ) * a ^ ((i : ℕ) - (j : ℕ))) • P.coeff i⟩

private theorem affineRestriction_eval
    (P : CirclePolynomial d) (k H a n : ℤ) :
    affineRestriction P k H a n = k • P (H * n + a) := by
  rw [CirclePolynomial.eval, CirclePolynomial.eval]
  simp only [affineRestriction, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [extended_add_pow (H * n) a i, Finset.mul_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

private theorem zsmul_eq_zero_of_base_zsmul_eq_zero
    (x : Torus) (H z : ℤ) (j : ℕ) (hj : 0 < j)
    (hH : H • x = 0) : (z * H ^ j) • x = 0 := by
  rw [show z * H ^ j = (z * H ^ (j - 1)) * H by
    rw [← pow_sub_one_mul hj.ne' H]
    ring]
  rw [mul_zsmul, hH, smul_zero]

private theorem affineRestriction_coeff_above
    (P : CirclePolynomial d) (k H a : ℤ) (r j : Fin (d + 1))
    (hrpos : 0 < (r : ℕ)) (hrj : (r : ℕ) < (j : ℕ))
    (hkill : ∀ i : Fin (d + 1),
      (r : ℕ) < (i : ℕ) → H • P.coeff i = 0) :
    (affineRestriction P k H a).coeff j = 0 := by
  change ∑ i : Fin (d + 1),
      (k * (Nat.choose (i : ℕ) (j : ℕ) : ℤ) *
        H ^ (j : ℕ) * a ^ ((i : ℕ) - (j : ℕ))) • P.coeff i = 0
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hij : (j : ℕ) ≤ (i : ℕ)
  · have hri : (r : ℕ) < (i : ℕ) := hrj.trans_le hij
    have hz := zsmul_eq_zero_of_base_zsmul_eq_zero
      (P.coeff i) H
      (k * (Nat.choose (i : ℕ) (j : ℕ) : ℤ) *
        a ^ ((i : ℕ) - (j : ℕ)))
      (j : ℕ) (hrpos.trans hrj) (hkill i hri)
    exact (congrArg (fun z : ℤ ↦ z • P.coeff i) (by ring)).trans hz
  · have hij' : (i : ℕ) < (j : ℕ) := Nat.lt_of_not_ge hij
    rw [Nat.choose_eq_zero_of_lt hij']
    simp

private theorem affineRestriction_coeff_leading
    (P : CirclePolynomial d) (k H a : ℤ) (r : Fin (d + 1))
    (hrpos : 0 < (r : ℕ))
    (hkill : ∀ i : Fin (d + 1),
      (r : ℕ) < (i : ℕ) → H • P.coeff i = 0) :
    (affineRestriction P k H a).coeff r =
      (k * H ^ (r : ℕ)) • P.coeff r := by
  change ∑ i : Fin (d + 1),
      (k * (Nat.choose (i : ℕ) (r : ℕ) : ℤ) *
        H ^ (r : ℕ) * a ^ ((i : ℕ) - (r : ℕ))) • P.coeff i = _
  rw [Finset.sum_eq_single r]
  · simp
  · intro i hi hir
    rcases lt_or_gt_of_ne hir with hirlt | hrilt
    · rw [Nat.choose_eq_zero_of_lt hirlt]
      simp
    · have hz := zsmul_eq_zero_of_base_zsmul_eq_zero
        (P.coeff i) H
        (k * (Nat.choose (i : ℕ) (r : ℕ) : ℤ) *
          a ^ ((i : ℕ) - (r : ℕ)))
        (r : ℕ) hrpos (hkill i hrilt)
      exact (congrArg (fun z : ℤ ↦ z • P.coeff i) (by ring)).trans hz
  · simp

private theorem star_circlePhase (x : Torus) :
    star (circlePhase x) = circlePhase (-x) := by
  simp only [circlePhase, fourier_one, Complex.star_def]
  rw [← Circle.coe_inv_eq_conj]
  simp [AddCircle.toCircle_neg]

private theorem norm_cesaroAverage_le_one
    (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) (N : ℕ) :
    ‖cesaroAverage u N‖ ≤ 1 := by
  by_cases hN : N = 0
  · simp [hN, cesaroAverage]
  rw [cesaroAverage, norm_mul, norm_inv, norm_natCast]
  calc
    (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, u n‖ ≤
        (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, (1 : ℝ) := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ hu n)
    _ = 1 := by
      simp [hN]

private theorem circlePolynomial_eval_linear
    (P : CirclePolynomial d) (r : Fin (d + 1))
    (hr : (r : ℕ) = 1)
    (habove : ∀ i : Fin (d + 1),
      (r : ℕ) < (i : ℕ) → P.coeff i = 0)
    (n : ℤ) :
    P n = P.coeff 0 + n • P.coeff r := by
  rw [CirclePolynomial.eval]
  have hrne : r ≠ (0 : Fin (d + 1)) := by
    intro e
    have := congrArg Fin.val e
    simp only [Fin.val_zero] at this
    omega
  have h0mem : (0 : Fin (d + 1)) ∈
      (Finset.univ : Finset (Fin (d + 1))) := Finset.mem_univ _
  rw [← Finset.sum_erase_add _ _ h0mem]
  have hrmem : r ∈
      (Finset.univ.erase (0 : Fin (d + 1)) : Finset (Fin (d + 1))) := by
    simp [hrne]
  rw [Finset.sum_eq_single r]
  · simp only [hr, pow_one, Fin.val_zero, pow_zero, one_zsmul]
    abel
  · intro i hi hir
    have hi0 : i ≠ (0 : Fin (d + 1)) := by simpa using hi
    have hri : (r : ℕ) < (i : ℕ) := by
      have hpos : 0 < (i : ℕ) := Fin.pos_iff_ne_zero.mpr hi0
      have hne : (i : ℕ) ≠ (r : ℕ) := fun e ↦ hir (Fin.ext e)
      omega
    rw [habove i hri, smul_zero]
  · exact fun hnot ↦ (hnot hrmem).elim

private theorem polynomial_phase_leading_aux (m : ℕ) :
    ∀ {d : ℕ} (P : CirclePolynomial d)
      (r : Fin (d + 1)),
      (r : ℕ) = m + 1 →
      addOrderOf (P.coeff r) = 0 →
      (∀ i : Fin (d + 1),
        (r : ℕ) < (i : ℕ) → P.coeff i = 0) →
      ∀ (k : ℤ), k ≠ 0 →
        Filter.Tendsto
          (fun N ↦ cesaroAverage
            (fun n ↦ circlePhase (k • P (n : ℤ))) N)
          Filter.atTop (nhds 0) := by
  induction m with
  | zero =>
      intro d P r hr hirr habove k hk
      have hlin := irrational_linear_phase_tendsto_zero
        (P.coeff r) hirr k hk
      have hconst : Filter.Tendsto
          (fun N ↦ circlePhase (k • P.coeff 0) *
            cesaroAverage
              (fun n ↦ circlePhase (k • ((n : ℤ) • P.coeff r))) N)
          Filter.atTop (nhds 0) := by
        simpa using hlin.const_mul (circlePhase (k • P.coeff 0))
      convert hconst using 1
      funext N
      simp_rw [cesaroAverage, circlePolynomial_eval_linear P r (by omega) habove,
        smul_add, circlePhase_add, Finset.mul_sum]
      ring_nf
  | succ m ih =>
      intro d P r hr hirr habove k hk
      let j : Fin (d + 1) := ⟨m + 1, by
        have := r.isLt
        omega⟩
      have hrj : (r : ℕ) = (j : ℕ) + 1 := by simp [j]; omega
      let u : ℕ → ℂ := fun n ↦ circlePhase (k • P (n : ℤ))
      have hu (n : ℕ) : ‖u n‖ ≤ 1 := by
        simp [u, norm_circlePhase]
      have hcorr (h : ℕ) (hh : 0 < h) :
          Filter.Tendsto
            (fun N ↦ cesaroAverage
              (fun n ↦ star (u n) * u (n + h)) N)
            Filter.atTop (nhds 0) := by
        let Q := shiftDifference P (h : ℤ)
        have hqcoeff : Q.coeff j =
            (((r : ℕ) : ℤ) * (h : ℤ)) • P.coeff r := by
          exact shiftDifference_coeff_pred P h r j hrj habove
        have hscalar : (((r : ℕ) : ℤ) * (h : ℤ)) ≠ 0 := by
          exact mul_ne_zero (by omega) (by omega)
        have hqirr : addOrderOf (Q.coeff j) = 0 := by
          rw [hqcoeff]
          exact nontorsion_zsmul hirr hscalar
        have hqabove : ∀ i : Fin (d + 1),
            (j : ℕ) < (i : ℕ) → Q.coeff i = 0 := by
          intro i hi
          exact shiftDifference_coeff_above P h r i (by omega) habove
        have hq := ih Q j (by simp [j]) hqirr hqabove k hk
        convert hq using 1
        funext N
        congr 2
        funext n
        simp only [u]
        rw [star_circlePhase, ← circlePhase_add]
        congr 1
        rw [shiftDifference_eval]
        push_cast
        rw [smul_sub]
        abel
      have hlimsupCorr (h : ℕ) (hh : 0 < h) :
          Filter.limsup
              (fun N ↦ ‖cesaroAverage
                (fun n ↦ star (u n) * u (n + h)) N‖)
              Filter.atTop = 0 := by
        simpa using (hcorr h hh).norm.limsup_eq
      rw [tendsto_zero_iff_norm_tendsto_zero]
      change Filter.Tendsto (fun N ↦ ‖cesaroAverage u N‖)
        Filter.atTop (nhds 0)
      apply Metric.tendsto_atTop.mpr
      intro eps heps
      obtain ⟨H, hH⟩ : ∃ H : ℕ, 0 < H ∧ (2 : ℝ) / H < eps ^ 2 := by
        obtain ⟨H, hH⟩ := exists_nat_gt (2 / eps ^ 2)
        have hsq : 0 < eps ^ 2 := sq_pos_of_pos heps
        have hHpos : 0 < H := by
          by_contra hzero
          have : H = 0 := Nat.eq_zero_of_not_pos hzero
          subst H
          simp only [Nat.cast_zero] at hH
          have : 0 < 2 / eps ^ 2 := div_pos (by norm_num) hsq
          linarith
        refine ⟨H, hHpos, (div_lt_iff₀ (by exact_mod_cast hHpos)).2 ?_⟩
        have hH' : 2 / eps ^ 2 < (H : ℝ) := hH
        simpa [mul_comm] using (div_lt_iff₀ hsq).mp hH'
      have hvdc := vanDerCorput_cesaro u hu H hH.1
      have hsumzero :
          ∑ h ∈ Finset.Icc 1 (H - 1),
              Filter.limsup
                (fun N ↦ ‖cesaroAverage
                  (fun n ↦ star (u n) * u (n + h)) N‖)
                Filter.atTop = 0 := by
        apply Finset.sum_eq_zero
        intro h hh
        rw [Finset.mem_Icc] at hh
        exact hlimsupCorr h (by omega)
      rw [hsumzero, mul_zero, add_zero] at hvdc
      have hev : ∀ᶠ N in Filter.atTop,
          ‖cesaroAverage u N‖ ^ 2 < eps ^ 2 :=
        ((Filter.limsup_le_iff (f := Filter.atTop)
          (u := fun N ↦ ‖cesaroAverage u N‖ ^ 2)
          (x := (2 : ℝ) / H)
          (h₁ := Filter.isCoboundedUnder_le_of_le _
            (fun N ↦ sq_nonneg ‖cesaroAverage u N‖))
          (h₂ := Filter.isBoundedUnder_of_eventually_le
            (a := (1 : ℝ)) (Filter.Eventually.of_forall fun N ↦ by
              have hn := norm_cesaroAverage_le_one u hu N
              nlinarith [norm_nonneg (cesaroAverage u N)]))).mp hvdc)
          (eps ^ 2) hH.2
      rw [Filter.eventually_atTop] at hev
      obtain ⟨N₀, hev⟩ := hev
      refine ⟨N₀, fun N hN ↦ ?_⟩
      have hsqN := hev N hN
      have hnonneg : 0 ≤ ‖cesaroAverage u N‖ := norm_nonneg _
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
      nlinarith

/-- A circle-polynomial phase with nontorsion leading coefficient has vanishing
character average. -/
theorem polynomial_phase_tendsto_zero_of_leading_nontorsion
    (P : CirclePolynomial d)
    (r : Fin (d + 1)) (hr : 0 < (r : ℕ))
    (hirr : addOrderOf (P.coeff r) = 0)
    (habove : ∀ i : Fin (d + 1),
      (r : ℕ) < (i : ℕ) → P.coeff i = 0)
    (k : ℤ) (hk : k ≠ 0) :
  Filter.Tendsto
    (fun N ↦ cesaroAverage
      (fun n ↦ circlePhase (k • P (n : ℤ))) N)
    Filter.atTop (nhds 0) := by
  exact polynomial_phase_leading_aux ((r : ℕ) - 1) P r
    (by omega) hirr habove k hk

/-- Any nontorsion nonconstant coefficient forces every nontrivial polynomial
character average to vanish. -/
theorem polynomial_phase_tendsto_zero_of_nontorsion_coeff
    (P : CirclePolynomial d)
    (hcoeff : ∃ i : Fin (d + 1),
      0 < (i : ℕ) ∧ addOrderOf (P.coeff i) = 0)
    (k : ℤ) (hk : k ≠ 0) :
  Filter.Tendsto
    (fun N ↦ cesaroAverage
      (fun n ↦ circlePhase (k • P (n : ℤ))) N)
    Filter.atTop (nhds 0) := by
  let s : Finset (Fin (d + 1)) := Finset.univ.filter fun i ↦
    0 < (i : ℕ) ∧ addOrderOf (P.coeff i) = 0
  have hs : s.Nonempty := by
    obtain ⟨i, hi, hirr⟩ := hcoeff
    exact ⟨i, by simp [s, hi, hirr]⟩
  let r : Fin (d + 1) := s.max' hs
  have hrmem : r ∈ s := Finset.max'_mem s hs
  have hrpos : 0 < (r : ℕ) := by
    exact (Finset.mem_filter.mp hrmem).2.1
  have hrirr : addOrderOf (P.coeff r) = 0 := by
    exact (Finset.mem_filter.mp hrmem).2.2
  have haboveOrder (i : Fin (d + 1)) (hri : (r : ℕ) < (i : ℕ)) :
      addOrderOf (P.coeff i) ≠ 0 := by
    intro hiirr
    have himem : i ∈ s := by simp [s, hrpos.trans hri, hiirr]
    have hir := Finset.le_max' s i himem
    exact (not_le_of_gt hri) hir
  let t : Finset (Fin (d + 1)) := Finset.univ.filter fun i ↦
    (r : ℕ) < (i : ℕ)
  let H : ℕ := ∏ i ∈ t, addOrderOf (P.coeff i)
  have hH : 0 < H := by
    apply Finset.prod_pos
    intro i hi
    have hri : (r : ℕ) < (i : ℕ) := by simpa [t] using hi
    exact Nat.pos_of_ne_zero (haboveOrder i hri)
  have hkill (i : Fin (d + 1)) (hri : (r : ℕ) < (i : ℕ)) :
      (H : ℤ) • P.coeff i = 0 := by
    have himem : i ∈ t := by
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hri
    have hdvd : addOrderOf (P.coeff i) ∣ H := by
      exact Finset.dvd_prod_of_mem (fun i ↦ addOrderOf (P.coeff i)) himem
    apply addOrderOf_dvd_iff_zsmul_eq_zero.mp
    exact_mod_cast hdvd
  have hres (a : Fin H) : Filter.Tendsto
      (fun N ↦ cesaroAverage
        (fun n ↦ circlePhase (k • P (H * n + (a : ℕ) : ℕ))) N)
      Filter.atTop (nhds 0) := by
    let R := affineRestriction P k (H : ℤ) (a : ℤ)
    have hrcoeff : R.coeff r =
        (k * (H : ℤ) ^ (r : ℕ)) • P.coeff r := by
      exact affineRestriction_coeff_leading P k H a r hrpos hkill
    have hscalar : k * (H : ℤ) ^ (r : ℕ) ≠ 0 := by
      apply mul_ne_zero hk
      exact pow_ne_zero _ (by exact_mod_cast hH.ne')
    have hrR : addOrderOf (R.coeff r) = 0 := by
      rw [hrcoeff]
      exact nontorsion_zsmul hrirr hscalar
    have haboveR : ∀ i : Fin (d + 1),
        (r : ℕ) < (i : ℕ) → R.coeff i = 0 := by
      intro i hi
      exact affineRestriction_coeff_above P k H a r i hrpos hi hkill
    have hR := polynomial_phase_tendsto_zero_of_leading_nontorsion
      R r hrpos hrR haboveR 1 one_ne_zero
    convert hR using 1
    funext N
    congr 2
    funext n
    rw [affineRestriction_eval]
    push_cast
    simp only [one_zsmul]
  have hcombine := cesaroAverage_of_residue_classes
    (fun n ↦ circlePhase (k • P (n : ℤ))) H hH
    (fun _ ↦ (0 : ℂ)) hres
  simpa using hcombine

/-- A circle-polynomial sequence with a nontorsion nonconstant coefficient is equidistributed. -/
theorem polynomial_equidistributed_of_nontorsion_coeff
    (P : CirclePolynomial d)
    (hcoeff : ∃ i : Fin (d + 1),
      0 < (i : ℕ) ∧ addOrderOf (P.coeff i) = 0) :
  Equidistributed (fun n : ℕ ↦ P (n : ℤ)) := by
  rw [equidistributed_iff_characters]
  intro k hk
  exact polynomial_phase_tendsto_zero_of_nontorsion_coeff P hcoeff k hk

/-- The continuous tent function supported on the metric ball of radius `eps` about `c`. -/
noncomputable def ballBump (c : Torus) (eps : ℝ) : C(Torus, ℝ) :=
  ⟨fun x ↦ max 0 (eps - dist x c),
    continuous_const.max
      (continuous_const.sub (continuous_id.dist continuous_const))⟩

/-- A positive-radius torus ball bump has strictly positive Haar integral. -/
theorem integral_ballBump_pos
    {eps : ℝ} {c : Torus} (heps : 0 < eps) :
  0 < ∫ x, ballBump c eps x ∂AddCircle.haarAddCircle := by
  have hint : MeasureTheory.Integrable (ballBump c eps)
      AddCircle.haarAddCircle := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        (ballBump c eps).continuous.continuousOn)
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
    (x := c) (ballBump c eps).continuous hint
    (fun x ↦ le_max_left _ _) (by simpa [ballBump] using heps)

/-- A sequence avoiding a nonempty metric ball cannot be equidistributed. -/
theorem not_equidistributed_of_avoidsBall
    {eps : ℝ} {c : Torus}
    (u : ℕ → Torus) (heps : 0 < eps)
    (havoid : ∀ n, u n ∉ Metric.ball c eps) :
  ¬ Equidistributed u := by
  intro hu
  let f : C(Torus, ℂ) :=
    ⟨fun x ↦ (ballBump c eps x : ℂ),
      Complex.continuous_ofReal.comp (ballBump c eps).continuous⟩
  have hfzero (n : ℕ) : f (u n) = 0 := by
    have hn : eps ≤ dist (u n) c := by
      simpa only [Metric.mem_ball, not_lt] using havoid n
    simp [f, ballBump, max_eq_left (sub_nonpos.mpr hn)]
  have havgzero : (fun N : ℕ ↦
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (u n)) = fun _ ↦ 0 := by
    funext N
    simp [hfzero]
  have hlim := hu f
  rw [havgzero] at hlim
  have hintzero : (∫ x, f x ∂AddCircle.haarAddCircle) = 0 :=
    tendsto_nhds_unique hlim tendsto_const_nhds
  have hreal : (0 : ℝ) <
      ∫ x, ballBump c eps x ∂AddCircle.haarAddCircle :=
    integral_ballBump_pos heps
  have hcoe : (∫ x, f x ∂AddCircle.haarAddCircle) =
      ((∫ x, ballBump c eps x ∂AddCircle.haarAddCircle : ℝ) : ℂ) := by
    simpa [f] using (integral_complex_ofReal
      (μ := AddCircle.haarAddCircle)
      (f := fun x ↦ ballBump c eps x))
  rw [hcoe] at hintzero
  exact hreal.ne' (Complex.ofReal_eq_zero.mp hintzero)

private theorem torsion_nonconstant_coefficients_of_avoidsBall_aux
    {d : ℕ} {eps : ℝ} {c : Torus}
    (P : CirclePolynomial d) (heps : 0 < eps)
    (havoid : P.AvoidsBall c eps) :
  P.HasTorsionNonconstantCoeffs := by
  intro i hi
  rw [← addOrderOf_pos_iff]
  exact Nat.pos_of_ne_zero (fun hzero ↦
    not_equidistributed_of_avoidsBall
      (fun n : ℕ ↦ P (n : ℤ)) heps (fun n ↦ havoid n)
      (polynomial_equidistributed_of_nontorsion_coeff
        P ⟨i, hi, hzero⟩))

/-- A circle polynomial avoiding a positive-radius ball has rational nonconstant coefficients. -/
theorem rational_nonconstant_coefficients_of_avoidsBall
    {d : ℕ} {eps : ℝ} {c : Torus}
    (P : CirclePolynomial d) (heps : 0 < eps)
    (havoid : P.AvoidsBall c eps) :
  P.HasRationalNonconstantCoeffs :=
  (rational_iff_torsion_nonconstant P).mpr
    (torsion_nonconstant_coefficients_of_avoidsBall_aux P heps havoid)

/-- A circle polynomial avoiding a positive-radius ball has torsion nonconstant coefficients. -/
theorem torsion_nonconstant_coefficients_of_avoidsBall
    {d : ℕ} {eps : ℝ} {c : Torus}
    (P : CirclePolynomial d) (heps : 0 < eps)
    (havoid : P.AvoidsBall c eps) :
  P.HasTorsionNonconstantCoeffs :=
  torsion_nonconstant_coefficients_of_avoidsBall_aux P heps havoid

end TranslationalTilings
