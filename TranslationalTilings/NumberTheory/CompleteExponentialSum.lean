import TranslationalTilings.NumberTheory.ChenCompleteSum
import TranslationalTilings.NumberTheory.QuadraticCompleteSum
import TranslationalTilings.NumberTheory.PolynomialWeilBound

/-!
# Effective complete exponential-sum bounds

This terminal module supplies the proved polynomial Weil input to the conditional Chen machinery,
packages the resulting prime-power and composite bounds, handles the linear and quadratic cases,
and replaces Chen's finite exceptional-prime factor by the explicit natural constant
`stechkinNatConstant`. It also transports the final estimate to integral polynomial phases.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- The polynomial prime-field additive-character bound furnished by the Stepanov development. -/
theorem polynomialPrimeSumBound : PolynomialPrimeSumBound := by
  intro p _ f hpos hsmall
  let _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact polynomial_addChar_sum_prime
    (Fact.out : p.Prime) f hpos hsmall

/-- Chen's prime-modulus estimate after discharging the abstract polynomial Weil hypothesis. -/
theorem chen_prime_base
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hd : 3 ≤ d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum p hp.pos f‖ ≤
    min (Real.rpow p ((1 : ℝ) / d))
        ((d - 1 : ℝ) *
          Real.rpow p (-(1 : ℝ) / 2 + (1 : ℝ) / d)) *
      Real.rpow p (1 - (1 : ℝ) / d) := by
  exact chen_prime_base_of polynomialPrimeSumBound hp f hdegree hd hdp hprimitive

/-- The unconditional Chen bound for a primitive polynomial sum modulo a prime power. -/
theorem primePower_completeSum_bound
    (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    chenLocalFactor d p *
      Real.rpow (p ^ a : ℝ) (1 - (1 : ℝ) / d) := by
  exact primePower_completeSum_bound_of_primeBound
    polynomialPrimeSumBound hp ha f hprimitive hdegree hd

/-- The finite-product form of ACK Theorem 2.2 for primitive polynomial sums modulo any
positive modulus. -/
theorem ack_theorem_2_2_finiteProduct
    (d q : ℕ) (hd : 3 ≤ d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    chenGlobalFactor d * Real.rpow q (1 - (1 : ℝ) / d) := by
  exact ack_theorem_2_2_finiteProduct_of_primeBound
    polynomialPrimeSumBound d q hd hq f hdegree hprimitive

private theorem prime_not_dvd_coeff_one_or_coeff_two
    {p a : ℕ} (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ 2)
    (hprimitive : Nat.Coprime (p ^ a) (Polynomial.nonconstantContentNat f)) :
    ¬ p ∣ Int.natAbs (f.coeff 1) ∨
      ¬ p ∣ Int.natAbs (f.coeff 2) := by
  have hpcoprime : Nat.Coprime p (Polynomial.nonconstantContentNat f) :=
    Nat.Coprime.of_dvd_left (dvd_pow_self p ha.ne') hprimitive
  rw [hp.coprime_iff_not_dvd] at hpcoprime
  by_contra hboth
  push Not at hboth
  apply hpcoprime
  rw [Polynomial.nonconstantContentNat, Polynomial.contentNat]
  rw [← show Int.natAbs (p : ℤ) = p by simp, Int.natAbs_dvd_natAbs]
  rw [Polynomial.content]
  apply Finset.dvd_gcd
  intro i hi
  rcases hboth with ⟨hone, htwo⟩
  have honeZ : (p : ℤ) ∣ f.coeff 1 := by
    exact Int.natAbs_dvd_natAbs.mp (by simpa using hone)
  have htwoZ : (p : ℤ) ∣ f.coeff 2 := by
    exact Int.natAbs_dvd_natAbs.mp (by simpa using htwo)
  rcases i with _ | _ | _ | i
  · simp [Polynomial.nonconstantPart]
  · rw [Polynomial.nonconstantPart, Polynomial.coeff_sub,
      Polynomial.coeff_C_of_ne_zero (by omega), sub_zero]
    exact honeZ
  · rw [Polynomial.nonconstantPart, Polynomial.coeff_sub,
      Polynomial.coeff_C_of_ne_zero (by omega), sub_zero]
    exact htwoZ
  · have hcoeff : f.coeff (i + 3) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Polynomial.nonconstantPart, Polynomial.coeff_sub, hcoeff,
      Polynomial.coeff_C_of_ne_zero (by omega), sub_zero]
    exact dvd_zero _

private theorem quadratic_primePower_local_bound
    {p a : ℕ} (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ 2)
    (hprimitive : Nat.Coprime (p ^ a) (Polynomial.nonconstantContentNat f)) :
    ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
      if p = 2 then Real.sqrt (2 * p ^ a) else Real.sqrt (p ^ a) := by
  have hunit := prime_not_dvd_coeff_one_or_coeff_two hp ha f hdegree hprimitive
  by_cases hp2 : p = 2
  · subst p
    rw [if_pos rfl]
    by_cases ha1 : a = 1
    · subst a
      have hprimitiveTwo :
          Nat.Coprime 2 (Polynomial.nonconstantContentNat f) := by
        simpa using hprimitive
      simpa using quadratic_mod_two_bound f hdegree hprimitiveTwo
    · have ha2 : 2 ≤ a := by omega
      by_cases hlinearDiv : 2 ∣ Int.natAbs (f.coeff 1)
      · have hquadratic : ¬ 2 ∣ Int.natAbs (f.coeff 2) :=
          hunit.resolve_left (not_not.mpr hlinearDiv)
        have hlinearEven : Even (f.coeff 1) := by
          rw [← Int.natAbs_even, even_iff_two_dvd]
          exact hlinearDiv
        have hquadraticOdd : Odd (f.coeff 2) := by
          rw [← Int.not_even_iff_odd]
          intro heven
          apply hquadratic
          rw [← even_iff_two_dvd, Int.natAbs_even]
          exact heven
        exact (quadratic_twoPower_quadratic_odd_norm ha2 f hdegree
          hlinearEven hquadraticOdd).le
      · have hlinearOdd : Odd (f.coeff 1) := by
          rw [← Int.not_even_iff_odd]
          intro heven
          apply hlinearDiv
          rw [← even_iff_two_dvd, Int.natAbs_even]
          exact heven
        rw [quadratic_twoPower_linear_odd_eq_zero ha2 f hdegree hlinearOdd,
          norm_zero]
        positivity
  · rw [if_neg hp2]
    by_cases hquadraticDiv : p ∣ Int.natAbs (f.coeff 2)
    · have hlinear : ¬ p ∣ Int.natAbs (f.coeff 1) :=
        hunit.resolve_right (not_not.mpr hquadraticDiv)
      rw [quadratic_primePower_linear_unit_eq_zero hp ha f hdegree
        hlinear hquadraticDiv, norm_zero]
      positivity
    · exact (quadratic_oddPrimePower_norm hp hp2 ha f hdegree
        hquadraticDiv).le

private theorem quadratic_factorization_product_bound
    (q : ℕ) (hq : 0 < q) :
    (∏ p : FactorizationPrimeSupport q,
        if p.1 = 2 then
          Real.sqrt (2 * p.1 ^ q.factorization p.1)
        else Real.sqrt (p.1 ^ q.factorization p.1)) ≤
      if Even q then Real.sqrt (2 * q) else Real.sqrt q := by
  classical
  calc
    (∏ p : FactorizationPrimeSupport q,
        if p.1 = 2 then
          Real.sqrt (2 * p.1 ^ q.factorization p.1)
        else Real.sqrt (p.1 ^ q.factorization p.1)) =
        ∏ p ∈ q.factorization.support,
          if p = 2 then Real.sqrt (2 * p ^ q.factorization p)
          else Real.sqrt (p ^ q.factorization p) := by
      exact factorizationPrimeSupport_prod_eq (fun p ↦
        if p = 2 then Real.sqrt (2 * p ^ q.factorization p)
        else Real.sqrt (p ^ q.factorization p))
    _ ≤ if Even q then Real.sqrt (2 * q) else Real.sqrt q := by
      have hlocal (p : ℕ) :
          (if p = 2 then Real.sqrt (2 * p ^ q.factorization p)
            else Real.sqrt (p ^ q.factorization p)) =
          (if p = 2 then Real.sqrt 2 else 1) *
            Real.rpow (p ^ q.factorization p : ℝ) ((1 : ℝ) / 2) := by
        by_cases hp2 : p = 2
        · subst p
          rw [if_pos rfl, if_pos rfl, Real.rpow_eq_pow,
            ← Real.sqrt_eq_rpow]
          exact Real.sqrt_mul (by positivity) _
        · simp only [if_neg hp2, one_mul, Real.rpow_eq_pow,
            ← Real.sqrt_eq_rpow]
      simp_rw [hlocal, Finset.prod_mul_distrib]
      rw [factorization_rpow_product q hq]
      have htwo : 2 ∈ q.factorization.support ↔ Even q := by
        rw [Nat.support_factorization, Nat.mem_primeFactors, even_iff_two_dvd]
        constructor
        · exact fun h ↦ h.2.1
        · exact fun h ↦ ⟨Nat.prime_two, h, hq.ne'⟩
      have hextra :
          (∏ p ∈ q.factorization.support,
              if p = 2 then Real.sqrt 2 else 1) =
            if Even q then Real.sqrt 2 else 1 := by
        by_cases heven : Even q
        · rw [if_pos heven, Finset.prod_eq_single 2]
          · simp
          · intro p _hp hp2
            simp [hp2]
          · exact fun hnot ↦ (hnot (htwo.mpr heven)).elim
        · rw [if_neg heven]
          apply Finset.prod_eq_one
          intro p hp
          simp only [ite_eq_right_iff]
          intro hp2
          subst p
          exact (heven (htwo.mp hp)).elim
      rw [hextra]
      by_cases heven : Even q
      · rw [if_pos heven, if_pos heven, Real.rpow_eq_pow,
          ← Real.sqrt_eq_rpow]
        exact (Real.sqrt_mul (by positivity) _).symm.le
      · simp only [if_neg heven, one_mul, Real.rpow_eq_pow,
          ← Real.sqrt_eq_rpow, le_refl]

/-- A primitive quadratic complete sum is bounded by `sqrt q` for odd `q` and `sqrt (2q)`
for even `q`. -/
theorem quadratic_polynomialCompleteSum_parity_bound
    (hq : 0 < q) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    if Even q then Real.sqrt (2 * q) else Real.sqrt q := by
  classical
  obtain ⟨D⟩ := exists_completeSumFactorizationData q hq f hprimitive
  rw [D.norm_eq_product]
  calc
    (∏ p : FactorizationPrimeSupport q,
        ‖factorizationLocalCompleteSum q f D.scalar p‖) ≤
        ∏ p : FactorizationPrimeSupport q,
          if p.1 = 2 then
            Real.sqrt (2 * p.1 ^ q.factorization p.1)
          else Real.sqrt (p.1 ^ q.factorization p.1) := by
      apply Finset.prod_le_prod
      · intro p _hp
        positivity
      · intro p _hp
        unfold factorizationLocalCompleteSum
        have ha : 0 < q.factorization p.1 := by
          have := p.property
          rw [Finsupp.mem_support_iff] at this
          omega
        apply quadratic_primePower_local_bound
          (factorizationPrimeSupport_prime p) ha
        · rw [Polynomial.natDegree_C_mul_eq f (D.scalar_ne_zero p)]
          exact hdegree
        · exact D.local_primitive p
    _ ≤ if Even q then Real.sqrt (2 * q) else Real.sqrt q :=
      quadratic_factorization_product_bound q hq

/-- The parity-independent bound `sqrt (2q)` for primitive complete sums of degree at most two. -/
theorem quadratic_polynomialCompleteSum_bound
    (hq : 0 < q) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤ Real.sqrt (2 * q) := by
  calc
    ‖polynomialCompleteSum q hq f‖ ≤
        if Even q then Real.sqrt (2 * q) else Real.sqrt q :=
      quadratic_polynomialCompleteSum_parity_bound hq f hdegree hprimitive
    _ ≤ Real.sqrt (2 * q) := by
      split
      · rfl
      · apply Real.sqrt_le_sqrt
        have hqNonneg : (0 : ℝ) ≤ q := by positivity
        nlinarith

/-- An explicit natural majorant for all degree-`d` constants in the complete-sum estimate. -/
def stechkinNatConstant (d : ℕ) : ℕ :=
  2 ^ (10 * (d + 1) ^ 8)

/-- Every local Chen factor in degree at least three is at most `d ^ 2`. -/
theorem chenLocalFactor_le (d p : ℕ) (hd : 3 ≤ d) :
    chenLocalFactor d p ≤ d ^ 2 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdOne : (1 : ℝ) ≤ d := by linarith
  have hdNonneg : (0 : ℝ) ≤ d := hdOne.trans' zero_le_one
  unfold chenLocalFactor
  split
  · nlinarith [sq_nonneg ((d : ℝ) - 1)]
  split
  · calc
      Real.rpow d ((2 : ℝ) / d) ≤ Real.rpow d 2 := by
        apply Real.rpow_le_rpow_of_exponent_le hdOne
        have hdPos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hdOne
        rw [div_le_iff₀ hdPos]
        nlinarith
      _ = (d : ℝ) ^ 2 := Real.rpow_natCast _ 2
  split
  · calc
      Real.rpow d ((3 : ℝ) / d) ≤ Real.rpow d 2 := by
        apply Real.rpow_le_rpow_of_exponent_le hdOne
        have hdPos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hdOne
        rw [div_le_iff₀ hdPos]
        nlinarith
      _ = (d : ℝ) ^ 2 := Real.rpow_natCast _ 2
  · have hrpow : Real.rpow d ((3 : ℝ) / d) ≤ d := by
      calc
        Real.rpow d ((3 : ℝ) / d) ≤ Real.rpow d 1 := by
          apply Real.rpow_le_rpow_of_exponent_le hdOne
          have hdPos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hdOne
          rw [div_le_iff₀ hdPos]
          simpa using hdR
        _ = d := by simp
    have hrpowNonneg : 0 ≤ Real.rpow d ((3 : ℝ) / d) :=
      Real.rpow_nonneg hdNonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hdOne) hrpowNonneg]

/-- At most `(d + 1) ^ 6` primes occur in the explicit exceptional-prime set. -/
theorem chenExceptionalPrimes_card_le (d : ℕ) :
    (chenExceptionalPrimes d).card ≤ (d + 1) ^ 6 := by
  let N := (d + 1) ^ 6
  have hsubset : chenExceptionalPrimes d ⊆ Finset.range (N + 1) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hne : chenExceptionalPrimes d ≠ Finset.range (N + 1) := by
    intro heq
    have hzero : 0 ∈ chenExceptionalPrimes d := by
      rw [heq]
      simp [N]
    exact Nat.not_prime_zero (Finset.mem_filter.mp hzero).2
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩)
  simp only [Finset.card_range, N] at hlt
  omega

/-- Chen's global factor is bounded by the product majorant `(d ^ 2) ^ ((d + 1) ^ 6)`. -/
theorem chenGlobalFactor_le_degreePow (d : ℕ) (hd : 3 ≤ d) :
    chenGlobalFactor d ≤
      ((d : ℝ) ^ 2) ^ ((d + 1) ^ 6) := by
  calc
    chenGlobalFactor d ≤
        ((d : ℝ) ^ 2) ^ (chenExceptionalPrimes d).card := by
      rw [chenGlobalFactor]
      calc
        ∏ p ∈ chenExceptionalPrimes d, chenLocalFactor d p ≤
            ∏ _p ∈ chenExceptionalPrimes d, (d : ℝ) ^ 2 := by
          apply Finset.prod_le_prod
          · intro p _hp
            exact zero_le_one.trans (one_le_chenLocalFactor d p hd)
          · intro p _hp
            exact chenLocalFactor_le d p hd
        _ = ((d : ℝ) ^ 2) ^ (chenExceptionalPrimes d).card := by simp
    _ ≤ ((d : ℝ) ^ 2) ^ ((d + 1) ^ 6) := by
      apply pow_le_pow_right₀
      · have hdOne : (1 : ℝ) ≤ d := by
          exact_mod_cast (show 1 ≤ d by omega)
        have hs : (1 : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 :=
          (sq_le_sq₀ zero_le_one (zero_le_one.trans hdOne)).mpr hdOne
        simpa using hs
      · exact chenExceptionalPrimes_card_le d

/-- The elementary estimate `d ≤ 2 ^ d` used to make the final constant executable. -/
theorem nat_le_two_pow (d : ℕ) : d ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by omega)
      omega

/-- The exponent arising from Chen's degree majorant fits inside the exponent of
`stechkinNatConstant`. -/
theorem chenMajorant_exponent_le (d : ℕ) :
    2 * d * (d + 1) ^ 6 ≤ 10 * (d + 1) ^ 8 := by
  rw [show 2 * d * (d + 1) ^ 6 = (2 * d) * (d + 1) ^ 6 by ring]
  rw [show 10 * (d + 1) ^ 8 = (10 * (d + 1) ^ 2) * (d + 1) ^ 6 by ring]
  apply Nat.mul_le_mul_right
  nlinarith

/-- The natural-number degree majorant is bounded by `stechkinNatConstant d`. -/
theorem chenDegreePow_le_natConstant (d : ℕ) :
    (d ^ 2) ^ ((d + 1) ^ 6) ≤ stechkinNatConstant d := by
  calc
    (d ^ 2) ^ ((d + 1) ^ 6) ≤
        ((2 ^ d) ^ 2) ^ ((d + 1) ^ 6) :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_left (nat_le_two_pow d) 2) _
    _ = 2 ^ (2 * d * (d + 1) ^ 6) := by ring
    _ ≤ 2 ^ (10 * (d + 1) ^ 8) :=
      Nat.pow_le_pow_right (by omega) (chenMajorant_exponent_le d)
    _ = stechkinNatConstant d := rfl

/-- Casting the natural degree majorant to `ℝ` agrees with the corresponding real power. -/
theorem chenDegreePow_cast (d : ℕ) :
    ((((d ^ 2) ^ ((d + 1) ^ 6) : ℕ) : ℝ)) =
      ((d : ℝ) ^ 2) ^ ((d + 1) ^ 6) := by
  norm_cast

/-- Chen's global factor is bounded by the explicit real cast of `stechkinNatConstant`. -/
theorem chenGlobalFactor_le_stechkinNatConstant
    (d : ℕ) (hd : 3 ≤ d) :
    chenGlobalFactor d ≤ stechkinNatConstant d := by
  calc
    chenGlobalFactor d ≤ ((d : ℝ) ^ 2) ^ ((d + 1) ^ 6) :=
      chenGlobalFactor_le_degreePow d hd
    _ = (((d ^ 2) ^ ((d + 1) ^ 6) : ℕ) : ℝ) :=
      (chenDegreePow_cast d).symm
    _ ≤ (stechkinNatConstant d : ℝ) := by
      exact_mod_cast chenDegreePow_le_natConstant d

/-- The explicit Stechkin constant is monotone in the degree bound. -/
theorem stechkinNatConstant_mono {e d : ℕ} (hed : e ≤ d) :
    stechkinNatConstant e ≤ stechkinNatConstant d := by
  apply Nat.pow_le_pow_right (by omega)
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left (Nat.add_le_add_right hed 1) 8

private theorem two_le_stechkinNatConstant (d : ℕ) :
    2 ≤ stechkinNatConstant d := by
  apply Nat.le_pow
  positivity

private theorem two_le_stechkinNatConstant_real (d : ℕ) :
    (2 : ℝ) ≤ stechkinNatConstant d := by
  exact_mod_cast two_le_stechkinNatConstant d

private theorem stechkinNatConstant_cast_mono {e d : ℕ} (hed : e ≤ d) :
    (stechkinNatConstant e : ℝ) ≤ stechkinNatConstant d := by
  exact_mod_cast stechkinNatConstant_mono hed

private theorem polynomialCompleteSum_effective_core
    (hWeil : PolynomialPrimeSumBound)
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow q (1 - (1 : ℝ) / d) := by
  have hqOne : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq.ne')
  have hdOne : (1 : ℝ) ≤ d := by
    exact_mod_cast hd
  have hexponentNonneg : (0 : ℝ) ≤ 1 - (1 : ℝ) / d := by
    have hinv : (1 : ℝ) / d ≤ 1 / 1 :=
      one_div_le_one_div_of_le (by norm_num) hdOne
    norm_num at hinv ⊢
    linarith
  have hRpowOne : (1 : ℝ) ≤ Real.rpow q (1 - (1 : ℝ) / d) := by
    rw [Real.rpow_eq_pow]
    exact Real.one_le_rpow hqOne hexponentNonneg
  have hConstantOne : (1 : ℝ) ≤ stechkinNatConstant d := by
    exact (by norm_num : (1 : ℝ) ≤ 2).trans
      (two_le_stechkinNatConstant_real d)
  have hRhsOne :
      (1 : ℝ) ≤ (stechkinNatConstant d : ℝ) *
        Real.rpow q (1 - (1 : ℝ) / d) := by
    calc
      (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ (stechkinNatConstant d : ℝ) *
          Real.rpow q (1 - (1 : ℝ) / d) :=
        mul_le_mul hConstantOne hRpowOne zero_le_one
          (zero_le_one.trans hConstantOne)
  by_cases hlinear : f.natDegree ≤ 1
  · exact (linear_polynomialCompleteSum_bound hq f hlinear hprimitive).trans
      hRhsOne
  by_cases hquadratic : f.natDegree ≤ 2
  · have hdTwo : 2 ≤ d :=
      (Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hlinear)).trans hdegree
    have hdTwoReal : (2 : ℝ) ≤ d := by exact_mod_cast hdTwo
    have hinv : (1 : ℝ) / d ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hdTwoReal
    have hexponentHalf : (1 : ℝ) / 2 ≤ 1 - (1 : ℝ) / d := by
      linarith
    have hsqrtQ :
        Real.sqrt q ≤ Real.rpow q (1 - (1 : ℝ) / d) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_eq_pow]
      exact Real.rpow_le_rpow_of_exponent_le hqOne hexponentHalf
    have hsqrtTwo : Real.sqrt 2 ≤ (2 : ℝ) := by norm_num
    have hConstantTwo : (2 : ℝ) ≤ stechkinNatConstant d := by
      exact two_le_stechkinNatConstant_real d
    calc
      ‖polynomialCompleteSum q hq f‖ ≤ Real.sqrt (2 * q) :=
        quadratic_polynomialCompleteSum_bound hq f hquadratic hprimitive
      _ = Real.sqrt 2 * Real.sqrt q := Real.sqrt_mul (by norm_num) _
      _ ≤ 2 * Real.sqrt q :=
        mul_le_mul_of_nonneg_right hsqrtTwo (Real.sqrt_nonneg _)
      _ ≤ (stechkinNatConstant d : ℝ) * Real.sqrt q :=
        mul_le_mul_of_nonneg_right hConstantTwo (Real.sqrt_nonneg _)
      _ ≤ (stechkinNatConstant d : ℝ) *
          Real.rpow q (1 - (1 : ℝ) / d) :=
        mul_le_mul_of_nonneg_left hsqrtQ
          (zero_le_one.trans hConstantOne)
  · have hdegreeThree : 3 ≤ f.natDegree :=
      Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hquadratic)
    have hAck := ack_theorem_2_2_finiteProduct_of_primeBound hWeil
      f.natDegree q hdegreeThree hq f rfl hprimitive
    have hFactor :
        chenGlobalFactor f.natDegree ≤ (stechkinNatConstant d : ℝ) := by
      calc
        chenGlobalFactor f.natDegree ≤ stechkinNatConstant f.natDegree :=
          chenGlobalFactor_le_stechkinNatConstant f.natDegree hdegreeThree
        _ ≤ (stechkinNatConstant d : ℝ) := by
          exact stechkinNatConstant_cast_mono hdegree
    have hdegreePos : (0 : ℝ) < f.natDegree := by
      exact_mod_cast (show 0 < f.natDegree from
        hdegreeThree.trans' (by norm_num))
    have hdegreeReal : (f.natDegree : ℝ) ≤ d := by exact_mod_cast hdegree
    have hinv : (1 : ℝ) / d ≤ 1 / f.natDegree :=
      one_div_le_one_div_of_le hdegreePos hdegreeReal
    have hexponent :
        (1 : ℝ) - 1 / f.natDegree ≤ 1 - 1 / d := by
      linarith
    have hRpow :
        Real.rpow q (1 - (1 : ℝ) / f.natDegree) ≤
          Real.rpow q (1 - (1 : ℝ) / d) := by
      rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
      exact Real.rpow_le_rpow_of_exponent_le hqOne hexponent
    have hLeftRpowNonneg :
        (0 : ℝ) ≤ Real.rpow q (1 - (1 : ℝ) / f.natDegree) := by
      rw [Real.rpow_eq_pow]
      exact Real.rpow_nonneg (by positivity) _
    exact hAck.trans (mul_le_mul hFactor hRpow hLeftRpowNonneg
      (zero_le_one.trans hConstantOne))

/-- An effective complete-sum bound for primitive integer polynomials of degree at most `d`. -/
theorem polynomialCompleteSum_effective
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow q (1 - (1 : ℝ) / d) := by
  exact polynomialCompleteSum_effective_core polynomialPrimeSumBound
    d q hd hq f hdegree hprimitive

/-- The effective complete-sum bound conditional on an arbitrary polynomial prime-sum estimate. -/
theorem polynomialCompleteSum_effective_of_primeBound
    (hWeil : PolynomialPrimeSumBound)
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow q (1 - (1 : ℝ) / d) := by
  exact polynomialCompleteSum_effective_core hWeil
    d q hd hq f hdegree hprimitive

/-- The effective complete exponential-sum estimate for a primitive integral polynomial phase. -/
theorem integral_complete_exponential_sum_effective
    (d : ℕ) (hd : 0 < d) (A : IntegralPolynomialPhase d)
    (hprimitive : A.Primitive) :
  ‖integralCompleteSum A‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow A.modulus (1 - (1 : ℝ) / d) := by
  rw [integralCompleteSum_eq_polynomialCompleteSum]
  exact polynomialCompleteSum_effective d A.modulus hd A.modulus_pos
    A.toPolynomial A.natDegree_toPolynomial_le
    (A.primitive_toPolynomial hprimitive)

/-- The integral-phase effective estimate conditional on a polynomial prime-sum bound. -/
theorem integral_complete_exponential_sum_effective_of_primeBound
    (hWeil : PolynomialPrimeSumBound)
    (d : ℕ) (hd : 0 < d) (A : IntegralPolynomialPhase d)
    (hprimitive : A.Primitive) :
  ‖integralCompleteSum A‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow A.modulus (1 - (1 : ℝ) / d) := by
  rw [integralCompleteSum_eq_polynomialCompleteSum]
  exact polynomialCompleteSum_effective_of_primeBound hWeil d A.modulus hd
    A.modulus_pos A.toPolynomial A.natDegree_toPolynomial_le
    (A.primitive_toPolynomial hprimitive)

end TranslationalTilings
