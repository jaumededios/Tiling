import TranslationalTilings.Analysis.CirclePolynomial
import TranslationalTilings.Analysis.Equidistribution
import TranslationalTilings.Analysis.FejerSeparator

/-!
# Rigidity of polynomial sequences avoiding an arc

This file transfers the complete exponential-sum estimate to circle-valued
polynomials and proves the explicit Fejér-separator rigidity argument.  It also
specializes the metric-ball result to the half-circle formulation used in the
tiling argument and packages bounded periods into a universal period.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- Coefficient-facing strengthening of Greenfeld--Tao, Lemma 4.2. -/
theorem complete_exponential_sum_paper
    (d : ℕ) (hd : 0 < d) (P : CirclePolynomial d)
    (hrat : P.HasTorsionNonconstantCoeffs)
    (_hnonconstant : ¬ P.CoefficientConstant) :
  ‖completeSum P P.commonDenominator‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ)) := by
  rw [norm_completeSum_eq_integralPhase P hrat]
  simpa only [integralPhase_modulus] using
    integral_complete_exponential_sum_effective d hd (P.integralPhase hrat)
      (integralPhase_primitive P hrat)

/-- Greenfeld--Tao, Lemma 4.2, literally for a nonconstant map. -/
theorem complete_exponential_sum_paper_functionNonconstant
    (d : ℕ) (hd : 0 < d) (P : CirclePolynomial d)
    (hrat : P.HasTorsionNonconstantCoeffs)
    (hnonconstant : ¬ P.FunctionConstant) :
  ‖completeSum P P.commonDenominator‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ)) := by
  exact complete_exponential_sum_paper d hd P hrat
    (P.not_coefficientConstant_of_not_functionConstant hnonconstant)

/-- Uniform big-O form of the complete exponential-sum estimate in fixed degree. -/
theorem complete_exponential_sum_paper_bigO (d : ℕ) (hd : 0 < d) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ P : CirclePolynomial d,
    P.HasTorsionNonconstantCoeffs → ¬ P.FunctionConstant →
    ‖completeSum P P.commonDenominator‖ ≤
      C * Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ)) := by
  refine ⟨stechkinNatConstant d, Nat.cast_nonneg _, ?_⟩
  intro P hrat hnonconstant
  exact complete_exponential_sum_paper_functionNonconstant
    d hd P hrat hnonconstant

/-- Explicit upper bound for a period forced by avoidance of a rational ball. -/
def rigidityPeriodBound (d : ℕ) (eps : ℚ) : ℕ :=
  if d = 0 then 1 else
    max 1 (separatorDegree eps *
      (stechkinNatConstant d * separatorL1NatBound eps) ^ d)

/-- Rigidity-period bound for a missing ball opposite a half-circle. -/
def halfCirclePeriodBound (d : ℕ) : ℕ :=
  rigidityPeriodBound d (1 / 8)

/-- Common multiple of all positive half-circle rigidity periods in degree `d`. -/
def universalRigidityPeriod (d : ℕ) : ℕ :=
  (Finset.Icc 1 (halfCirclePeriodBound d)).lcm id

/-- The explicit rigidity-period bound is positive. -/
theorem rigidityPeriodBound_pos (d : ℕ) (eps : ℚ) :
  0 < rigidityPeriodBound d eps := by
  simp only [rigidityPeriodBound]
  split <;> omega

private theorem zsmul_eval (P : CirclePolynomial d) (k : ℤ) (n : ℤ) :
    P.zsmul k n = k • P n := by
  simp only [CirclePolynomial.eval, CirclePolynomial.zsmul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, smul_smul, mul_comm]

/-- Extract a nonzero Fourier frequency whose complete sum is large. -/
private theorem exists_large_completeSum
    (P : CirclePolynomial d) (c : Torus) (eps : ℚ)
    (heps : 0 < eps) (hsmall : eps < 1 / 2)
    (Q : ℕ) (hQ : 0 < Q) (havoid : P.AvoidsBall c eps) :
  ∃ k ∈ Finset.Icc (-(separatorDegree eps : ℤ))
      (separatorDegree eps : ℤ),
    k ≠ 0 ∧
    (Q : ℝ) / separatorL1NatBound eps ≤
      ‖completeSum (P.zsmul k) Q‖ := by
  let K : Finset ℤ := Finset.Icc (-(separatorDegree eps : ℤ))
      (separatorDegree eps : ℤ)
  let a : ℤ → ℂ := fejerSeparatorCoeff c eps
  let S : ℤ → ℂ := fun k ↦ completeSum (P.zsmul k) Q
  obtain ⟨ha0, _, hpositive, hl1⟩ :=
    fejer_separator_spec c eps heps hsmall
  have hexpand :
      (∑ n ∈ Finset.Icc 1 Q, fejerSeparatorEval c eps (P n)) =
        ∑ k ∈ K, a k * S k := by
    simp only [fejerSeparatorEval, K, a, S, completeSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [zsmul_eval]
  have hQcard : (Q : ℝ) =
      ∑ _n ∈ Finset.Icc 1 Q, (1 : ℝ) := by
    simp [Nat.card_Icc]
  have hQre : (Q : ℝ) ≤
      (∑ n ∈ Finset.Icc 1 Q,
        fejerSeparatorEval c eps (P n)).re := by
    rw [hQcard]
    change (∑ _n ∈ Finset.Icc 1 Q, (1 : ℝ)) ≤
      Complex.reCLM (∑ n ∈ Finset.Icc 1 Q,
        fejerSeparatorEval c eps (P n))
    rw [map_sum]
    apply Finset.sum_le_sum
    intro n _
    exact (hpositive (P n) (havoid n)).2
  have hweighted : (Q : ℝ) ≤
      ∑ k ∈ K, ‖a k‖ * ‖S k‖ := by
    calc
      (Q : ℝ) ≤ (∑ n ∈ Finset.Icc 1 Q,
        fejerSeparatorEval c eps (P n)).re := hQre
      _ = (∑ k ∈ K, a k * S k).re := congrArg Complex.re hexpand
      _ ≤ ‖∑ k ∈ K, a k * S k‖ := Complex.re_le_norm _
      _ ≤ ∑ k ∈ K, ‖a k * S k‖ := norm_sum_le _ _
      _ = ∑ k ∈ K, ‖a k‖ * ‖S k‖ := by
        apply Finset.sum_congr rfl
        intro k _
        exact norm_mul _ _
  have hLpos : 0 < separatorL1NatBound eps := by
    simp [separatorL1NatBound]
  have hLcast : 0 < (separatorL1NatBound eps : ℝ) := by
    exact_mod_cast hLpos
  have hQcast : 0 < (Q : ℝ) := by
    exact_mod_cast hQ
  have hmass : (∑ k ∈ K, ‖a k‖) ≤
      (separatorL1NatBound eps : ℝ) := by
    simpa [K, a] using hl1
  have hex : ∃ k ∈ K, a k ≠ 0 ∧
      (Q : ℝ) / separatorL1NatBound eps ≤ ‖S k‖ := by
    by_contra hnone
    push Not at hnone
    have hterm_le (k : ℤ) (hk : k ∈ K) :
        ‖a k‖ * ‖S k‖ ≤ ‖a k‖ *
          ((Q : ℝ) / separatorL1NatBound eps) := by
      rcases eq_or_ne (a k) 0 with ha | ha
      · simp [ha]
      · exact mul_le_mul_of_nonneg_left
          (le_of_lt (hnone k hk ha)) (norm_nonneg _)
    have hsum_le : (∑ k ∈ K, ‖a k‖ * ‖S k‖) ≤
        ∑ k ∈ K, ‖a k‖ *
          ((Q : ℝ) / separatorL1NatBound eps) :=
      Finset.sum_le_sum hterm_le
    have hright : (∑ k ∈ K, ‖a k‖ *
        ((Q : ℝ) / separatorL1NatBound eps)) ≤ Q := by
      rw [← Finset.sum_mul]
      calc
        (∑ k ∈ K, ‖a k‖) *
            ((Q : ℝ) / separatorL1NatBound eps) ≤
            (separatorL1NatBound eps : ℝ) *
              ((Q : ℝ) / separatorL1NatBound eps) :=
          mul_le_mul_of_nonneg_right hmass
            (div_nonneg hQcast.le hLcast.le)
        _ = Q := by field_simp
    have hQeq : (∑ k ∈ K, ‖a k‖ * ‖S k‖) = Q :=
      le_antisymm (hsum_le.trans hright) hweighted
    have hpositiveSum : 0 < ∑ k ∈ K, ‖a k‖ * ‖S k‖ := by
      rw [hQeq]
      exact hQcast
    rw [Finset.sum_pos_iff_of_nonneg
      (fun k _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))] at hpositiveSum
    obtain ⟨k, hk, hkpos⟩ := hpositiveSum
    have hwpos : 0 < ‖a k‖ := by
      nlinarith [norm_nonneg (a k), norm_nonneg (S k)]
    have hak : a k ≠ 0 := by
      intro hak
      simp [hak] at hwpos
    have hstrict : ‖a k‖ * ‖S k‖ <
        ‖a k‖ * ((Q : ℝ) / separatorL1NatBound eps) :=
      mul_lt_mul_of_pos_left (hnone k hk hak) hwpos
    have hsum_strict : (∑ k ∈ K, ‖a k‖ * ‖S k‖) <
        ∑ k ∈ K, ‖a k‖ *
          ((Q : ℝ) / separatorL1NatBound eps) :=
      Finset.sum_lt_sum hterm_le ⟨k, hk, hstrict⟩
    exact (not_lt_of_ge hweighted) (hsum_strict.trans_le hright)
  obtain ⟨k, hk, hak, hkbound⟩ := hex
  refine ⟨k, hk, ?_, ?_⟩
  · intro hk0
    subst k
    exact hak ha0
  · simpa [S] using hkbound

/-- Greenfeld--Tao, Lemma 4.3, for a metric ball. -/
theorem periodic_of_avoidsBall
    (P : CirclePolynomial d) (c : Torus) (eps : ℚ)
    (heps : 0 < eps) (hsmall : eps < 1 / 2)
    (havoid : P.AvoidsBall c eps) :
  ∃ Q, 0 < Q ∧ Q ≤ rigidityPeriodBound d eps ∧ P.PeriodicWith Q := by
  rcases eq_or_ne d 0 with rfl | hd0
  · have hconst : P.CoefficientConstant := by
      intro i hi
      omega
    obtain ⟨x, hx⟩ := P.functionConstant_of_coefficientConstant hconst
    refine ⟨1, by omega, by simp [rigidityPeriodBound], ?_⟩
    intro n
    rw [hx, hx]
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    have hrat : P.HasTorsionNonconstantCoeffs :=
      torsion_nonconstant_coefficients_of_avoidsBall P
        (Rat.cast_pos.mpr heps) havoid
    let Q := P.commonDenominator
    have hQ : 0 < Q := commonDenominator_pos P hrat
    have hperiod : P.PeriodicWith Q := periodic_commonDenominator P hrat
    obtain ⟨k, hkK, hk0, hkLower⟩ :=
      exists_large_completeSum P c eps heps hsmall Q hQ havoid
    let Pk := P.zsmul k
    let q := Pk.commonDenominator
    have hratk : Pk.HasTorsionNonconstantCoeffs := by
      intro i hi
      exact (hrat i hi).zsmul
    have hq : 0 < q := commonDenominator_pos Pk hratk
    have hqdiv : q ∣ Q := commonDenominator_zsmul_dvd P hrat k
    have hperiodk : Pk.PeriodicWith q := periodic_commonDenominator Pk hratk
    have hrepeat := normalized_completeSum_repeat Pk Q q hQ hq hqdiv hperiodk
    have hrepeatNorm := congrArg norm hrepeat
    have hrepeatReal : ‖completeSum Pk Q‖ / (Q : ℝ) =
        ‖completeSum Pk q‖ / (q : ℝ) := by
      rw [norm_mul, norm_mul, norm_inv, norm_inv,
        norm_natCast, norm_natCast] at hrepeatNorm
      simpa only [div_eq_mul_inv, mul_comm] using hrepeatNorm
    have hQcast : 0 < (Q : ℝ) := by
      exact_mod_cast hQ
    have hqcast : 0 < (q : ℝ) := by
      exact_mod_cast hq
    have hLpos : 0 < separatorL1NatBound eps := by
      simp [separatorL1NatBound]
    have hLcast : 0 < (separatorL1NatBound eps : ℝ) := by
      exact_mod_cast hLpos
    have hnormalizedLower :
        (1 : ℝ) / separatorL1NatBound eps ≤
          ‖completeSum Pk q‖ / q := by
      calc
        (1 : ℝ) / separatorL1NatBound eps =
            ((Q : ℝ) / separatorL1NatBound eps) / Q := by
          field_simp
        _ ≤ ‖completeSum Pk Q‖ / Q :=
          div_le_div_of_nonneg_right hkLower hQcast.le
        _ = ‖completeSum Pk q‖ / q := hrepeatReal
    have hreverse : Q ∣ Int.natAbs k * q :=
      commonDenominator_dvd_natAbs_mul_zsmul P hrat k
    have hkabs : Int.natAbs k ≤ separatorDegree eps := by
      have hkInt : |k| ≤ (separatorDegree eps : ℤ) :=
        (abs_le).2 (Finset.mem_Icc.mp hkK)
      rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
      exact hkInt
    have hQ_le_mul : Q ≤ Int.natAbs k * q :=
      Nat.le_of_dvd (Nat.mul_pos (Int.natAbs_pos.mpr hk0) hq) hreverse
    have hq_bound : q ≤
        (stechkinNatConstant d * separatorL1NatBound eps) ^ d := by
      rcases Classical.em Pk.CoefficientConstant with hconstant | hnonconstant
      · have hq_one : q = 1 := by
          change Pk.commonDenominator = 1
          unfold CirclePolynomial.commonDenominator
          calc
            (CirclePolynomial.nonconstantIndices d).lcm
                (fun i ↦ addOrderOf (Pk.coeff i)) =
                (CirclePolynomial.nonconstantIndices d).lcm (fun _ ↦ 1) := by
              apply Finset.lcm_congr rfl
              intro i hi
              have hi' : 0 < (i : ℕ) :=
                (Finset.mem_filter.mp hi).2
              rw [hconstant i hi']
              simp
            _ = 1 := by
              induction CirclePolynomial.nonconstantIndices d using Finset.induction_on with
              | empty => simp
              | @insert i s _ ih => simp [ih]
        rw [hq_one]
        exact Nat.one_le_pow d _ (Nat.mul_pos
          (pow_pos (by omega) _) hLpos)
      · have hupper :=
          complete_exponential_sum_paper d hd Pk hratk hnonconstant
        have hupperDiv : ‖completeSum Pk q‖ / (q : ℝ) ≤
            (stechkinNatConstant d : ℝ) *
              Real.rpow (q : ℝ) (1 - (1 : ℝ) / (d : ℝ)) / q :=
          div_le_div_of_nonneg_right hupper hqcast.le
        have hrootpos : 0 < Real.rpow (q : ℝ) ((d : ℝ)⁻¹) :=
          Real.rpow_pos_of_pos hqcast _
        have hpowerDiv :
            Real.rpow (q : ℝ) (1 - (1 : ℝ) / (d : ℝ)) / q =
              (Real.rpow (q : ℝ) ((d : ℝ)⁻¹))⁻¹ := by
          rw [Real.rpow_eq_pow, Real.rpow_eq_pow, one_div]
          rw [Real.rpow_sub hqcast, Real.rpow_one]
          field_simp
        have hrootIneq :
            (1 : ℝ) / separatorL1NatBound eps ≤
              (stechkinNatConstant d : ℝ) /
                Real.rpow (q : ℝ) ((d : ℝ)⁻¹) := by
          calc
            (1 : ℝ) / separatorL1NatBound eps ≤
                ‖completeSum Pk q‖ / q := hnormalizedLower
            _ ≤ (stechkinNatConstant d : ℝ) *
                Real.rpow (q : ℝ) (1 - (1 : ℝ) / (d : ℝ)) / q :=
              hupperDiv
            _ = (stechkinNatConstant d : ℝ) /
                Real.rpow (q : ℝ) ((d : ℝ)⁻¹) := by
              calc
                (stechkinNatConstant d : ℝ) *
                    Real.rpow (q : ℝ) (1 - (1 : ℝ) / (d : ℝ)) / q =
                    (stechkinNatConstant d : ℝ) *
                      (Real.rpow (q : ℝ) (1 - (1 : ℝ) / (d : ℝ)) / q) := by
                  ring
                _ = (stechkinNatConstant d : ℝ) *
                    (Real.rpow (q : ℝ) ((d : ℝ)⁻¹))⁻¹ := by
                  rw [hpowerDiv]
                _ = (stechkinNatConstant d : ℝ) /
                    Real.rpow (q : ℝ) ((d : ℝ)⁻¹) := by
                  rw [div_eq_mul_inv]
        have hrootBound : Real.rpow (q : ℝ) ((d : ℝ)⁻¹) ≤
            (stechkinNatConstant d : ℝ) * separatorL1NatBound eps := by
          have hfirst := (le_div_iff₀ hrootpos).mp hrootIneq
          calc
            Real.rpow (q : ℝ) ((d : ℝ)⁻¹) =
                (((1 : ℝ) / separatorL1NatBound eps) *
                  Real.rpow (q : ℝ) ((d : ℝ)⁻¹)) *
                    separatorL1NatBound eps := by field_simp
            _ ≤ (stechkinNatConstant d : ℝ) *
                separatorL1NatBound eps :=
              mul_le_mul_of_nonneg_right hfirst hLcast.le
        have hrootBound' : (q : ℝ) ^ ((d : ℝ)⁻¹) ≤
            (stechkinNatConstant d : ℝ) * separatorL1NatBound eps := by
          simpa only [Real.rpow_eq_pow] using hrootBound
        have hpow := pow_le_pow_left₀
          (Real.rpow_nonneg hqcast.le ((d : ℝ)⁻¹)) hrootBound' d
        have hrootpow :
            (((q : ℝ) ^ ((d : ℝ)⁻¹) : ℝ) ^ d) = q :=
          Real.rpow_inv_natCast_pow hqcast.le hd.ne'
        rw [hrootpow] at hpow
        apply (Nat.cast_le (α := ℝ)).mp
        simpa only [Nat.cast_pow, Nat.cast_mul] using hpow
    refine ⟨Q, hQ, ?_, hperiod⟩
    simp only [rigidityPeriodBound, hd0, if_false]
    apply le_trans hQ_le_mul
    apply le_trans (Nat.mul_le_mul hkabs hq_bound)
    exact Nat.le_max_right _ _

/-- A polynomial with real lifts in `[0, 1/2]` avoids the opposite ball. -/
theorem halfCircle_avoidsBall
    (P : CirclePolynomial d) (hhalf : P.HasHalfCircleLifts) :
  P.AvoidsBall (((3 / 4 : ℝ) : Torus)) (1 / 8 : ℝ) := by
  intro n hn
  obtain ⟨t, ht, hPt⟩ := hhalf n
  have hclosed : (t : Torus) ∈
      Metric.closedBall (((3 / 4 : ℝ) : Torus)) (1 / 8 : ℝ) := by
    rw [← hPt]
    exact Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hn))
  have hpre : t ∈ (fun x : ℝ ↦ (x : Torus)) ⁻¹'
      Metric.closedBall (((3 / 4 : ℝ) : Torus)) (1 / 8 : ℝ) := hclosed
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hpre
  simp only [Set.mem_iUnion, Metric.mem_closedBall, Real.dist_eq] at hpre
  obtain ⟨z, hz⟩ := hpre
  rcases eq_or_ne z 0 with rfl | hz0
  · norm_num [zsmul_eq_mul] at hz
    have hsign : t - (3 / 4 : ℝ) ≤ 0 := by linarith [ht.2]
    rw [abs_of_nonpos hsign] at hz
    norm_num at hz
    linarith [ht.2]
  · rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero ℝ hz0 with hzneg | hzpos
    · norm_num [zsmul_eq_mul] at hz
      have hsign : 0 ≤ t - (3 / 4 + (z : ℝ)) := by linarith [ht.1]
      rw [abs_of_nonneg hsign] at hz
      linarith [ht.1]
    · norm_num [zsmul_eq_mul] at hz
      have hsign : t - (3 / 4 + (z : ℝ)) ≤ 0 := by linarith [ht.2]
      rw [abs_of_nonpos hsign] at hz
      linarith [ht.2]

/-- A circle polynomial whose values lift to a half-circle has a bounded period. -/
theorem periodic_of_halfCircle
    (P : CirclePolynomial d) (hhalf : P.HasHalfCircleLifts) :
  ∃ Q, 0 < Q ∧ Q ≤ halfCirclePeriodBound d ∧ P.PeriodicWith Q := by
  have havoid : P.AvoidsBall (((3 / 4 : ℝ) : Torus))
      (((1 / 8 : ℚ) : ℝ)) := by
    simpa using halfCircle_avoidsBall P hhalf
  simpa only [halfCirclePeriodBound] using
    periodic_of_avoidsBall P (((3 / 4 : ℝ) : Torus)) (1 / 8 : ℚ)
      (by norm_num) (by norm_num) havoid

/-- Every positive bounded half-circle period divides the universal period. -/
theorem period_dvd_universalRigidityPeriod
    (q : ℕ) (hq : 0 < q) (hbound : q ≤ halfCirclePeriodBound d) :
  q ∣ universalRigidityPeriod d := by
  apply Finset.dvd_lcm
  exact Finset.mem_Icc.mpr ⟨hq, hbound⟩

/-- A bounded half-circle period promotes to the universal rigidity period. -/
theorem periodic_universalRigidityPeriod
    (P : CirclePolynomial d) (q : ℕ)
    (hperiod : P.PeriodicWith q) (hq : 0 < q)
    (hbound : q ≤ halfCirclePeriodBound d) :
  P.PeriodicWith (universalRigidityPeriod d) := by
  obtain ⟨m, hm⟩ := period_dvd_universalRigidityPeriod q hq hbound
  rw [hm]
  change Function.Periodic P ((q * m : ℕ) : ℤ)
  rw [Nat.cast_mul]
  simpa [mul_comm] using hperiod.nsmul m

end TranslationalTilings
