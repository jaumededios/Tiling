import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Content
import TranslationalTilings.NumberTheory.FiniteCyclicPhase

/-!
# Linear and quadratic complete sums

The exact degree-one and degree-two branches of the complete-sum estimate,
including odd prime powers and the full two-primary parity split.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- The integral polynomial `A X² + B X + C`. -/
noncomputable def quadraticPolynomial (A B C : ℤ) : Polynomial ℤ :=
  Polynomial.monomial 2 A + Polynomial.monomial 1 B + Polynomial.C C

/-- The pure quadratic Gauss sum with coefficient `A` modulo `q`. -/
noncomputable def quadraticGaussSum
    (q : ℕ) (hq : 0 < q) (A : ℤ) : ℂ :=
  polynomialCompleteSum q hq (quadraticPolynomial A 0 0)

private theorem quadraticPolynomial_eval
    (q : ℕ) [NeZero q] (A B C : ℤ) (x : ZMod q) :
    Polynomial.eval x
        ((quadraticPolynomial A B C).map (Int.castRingHom (ZMod q))) =
      (A : ZMod q) * x ^ 2 + (B : ZMod q) * x + (C : ZMod q) := by
  simp [quadraticPolynomial, Polynomial.eval_add, Polynomial.eval_monomial]

private theorem polynomialCompleteSum_quadratic
    (q : ℕ) [NeZero q] (hq : 0 < q) (A B C : ℤ) :
    polynomialCompleteSum q hq (quadraticPolynomial A B C) =
      ∑ x : ZMod q,
        ZMod.stdAddChar ((A : ZMod q) * x ^ 2 + (B : ZMod q) * x + (C : ZMod q)) := by
  simp only [polynomialCompleteSum, quadraticPolynomial_eval]

private theorem quadraticGaussSum_eq_sum
    (q : ℕ) [NeZero q] (hq : 0 < q) (A : ℤ) :
    quadraticGaussSum q hq A =
      ∑ x : ZMod q, ZMod.stdAddChar ((A : ZMod q) * x ^ 2) := by
  rw [quadraticGaussSum, polynomialCompleteSum_quadratic]
  simp

private theorem finEquiv_apply_eq_natCast
    (q : ℕ) [NeZero q] (i : Fin q) :
    ZMod.finEquiv q i = (i.val : ZMod q) := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q => exact (Fin.cast_val_eq_self i).symm

private theorem finEquiv_symm_val
    (q : ℕ) [NeZero q] (x : ZMod q) :
    ((ZMod.finEquiv q).symm x).val = x.val := by
  have h := congrArg ZMod.val
    (finEquiv_apply_eq_natCast q ((ZMod.finEquiv q).symm x))
  rw [RingEquiv.apply_symm_apply] at h
  rw [ZMod.val_natCast,
    Nat.mod_eq_of_lt ((ZMod.finEquiv q).symm x).isLt] at h
  exact h.symm

private theorem sum_zmod_mul
    (m n : ℕ) [NeZero m] [NeZero n]
    (f : ZMod (m * n) → ℂ) :
    ∑ x : ZMod (m * n), f x =
      ∑ y : ZMod m, ∑ z : ZMod n,
        f ((z.val + n * y.val : ℕ) : ZMod (m * n)) := by
  let e : ZMod m × ZMod n ≃ ZMod (m * n) :=
    (Equiv.prodCongr (ZMod.finEquiv m).toEquiv.symm
      (ZMod.finEquiv n).toEquiv.symm).trans
      (finProdFinEquiv.trans (ZMod.finEquiv (m * n)).toEquiv)
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  change
    ZMod.finEquiv (m * n)
        (finProdFinEquiv
          ((ZMod.finEquiv m).symm y, (ZMod.finEquiv n).symm z)) =
      ((z.val + n * y.val : ℕ) : ZMod (m * n))
  rw [finEquiv_apply_eq_natCast]
  congr 1
  simp [finProdFinEquiv, finEquiv_symm_val]

private theorem sum_zmod_eq_mul
    (q m n : ℕ) [NeZero q] [NeZero m] [NeZero n]
    (hq : q = m * n) (f : ZMod q → ℂ) :
    ∑ x : ZMod q, f x =
      ∑ y : ZMod m, ∑ z : ZMod n,
        f ((z.val + n * y.val : ℕ) : ZMod q) := by
  subst q
  exact sum_zmod_mul m n f

private theorem stdAddChar_mul_modulus
    (m n : ℕ) [NeZero m] [NeZero n] (t : ℤ) :
    ZMod.stdAddChar ((n : ℤ) * t : ZMod (m * n)) =
      ZMod.stdAddChar (t : ZMod m) := by
  have hcast :
      ((n : ℤ) : ZMod (m * n)) * (t : ZMod (m * n)) =
        (((n : ℤ) * t : ℤ) : ZMod (m * n)) := by
    norm_num
  calc
    ZMod.stdAddChar ((n : ℤ) * t : ZMod (m * n)) =
        ZMod.stdAddChar (((n : ℤ) * t : ℤ) : ZMod (m * n)) :=
      congrArg _ hcast
    _ = ZMod.stdAddChar (t : ZMod m) := by
      rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
      congr 1
      push_cast
      have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
      field_simp [hn]

private theorem stdAddChar_mul_modulus_eq
    (q m n : ℕ) [NeZero q] [NeZero m] [NeZero n]
    (hq : q = m * n) (t : ℤ) :
    ZMod.stdAddChar ((n : ℤ) * t : ZMod q) =
      ZMod.stdAddChar (t : ZMod m) := by
  subst q
  exact stdAddChar_mul_modulus m n t

private theorem sum_stdAddChar_mul
    (q : ℕ) [NeZero q] (b : ZMod q) :
    ∑ x : ZMod q, ZMod.stdAddChar (b * x) =
      if b = 0 then (q : ℂ) else 0 := by
  have h := AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar q)
  simpa [mul_comm, ZMod.card] using h

private theorem quadraticSum_normSq
    (q : ℕ) [NeZero q] (A B : ZMod q) :
    (Complex.normSq
        (∑ x : ZMod q, ZMod.stdAddChar (A * x ^ 2 + B * x)) : ℂ) =
      ∑ h : ZMod q,
        ZMod.stdAddChar (A * h ^ 2 + B * h) *
          (if 2 * A * h = 0 then (q : ℂ) else 0) := by
  rw [Complex.normSq_eq_conj_mul_self]
  calc
    starRingEnd ℂ (∑ x : ZMod q, ZMod.stdAddChar (A * x ^ 2 + B * x)) *
        (∑ y : ZMod q, ZMod.stdAddChar (A * y ^ 2 + B * y)) =
      ∑ x : ZMod q, ∑ y : ZMod q,
        starRingEnd ℂ (ZMod.stdAddChar (A * x ^ 2 + B * x)) *
          ZMod.stdAddChar (A * y ^ 2 + B * y) := by
      simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ x : ZMod q, ∑ h : ZMod q,
        starRingEnd ℂ (ZMod.stdAddChar (A * x ^ 2 + B * x)) *
          ZMod.stdAddChar (A * (x + h) ^ 2 + B * (x + h)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.sum_bijective (fun h : ZMod q ↦ x + h)
        (AddGroup.addLeft_bijective x) _ _ (fun _ ↦ rfl)).symm
    _ = ∑ h : ZMod q, ∑ x : ZMod q,
        starRingEnd ℂ (ZMod.stdAddChar (A * x ^ 2 + B * x)) *
          ZMod.stdAddChar (A * (x + h) ^ 2 + B * (x + h)) := by
      rw [Finset.sum_comm]
    _ = ∑ h : ZMod q, ∑ x : ZMod q,
        ZMod.stdAddChar (A * h ^ 2 + B * h) *
          ZMod.stdAddChar ((2 * A * h) * x) := by
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro x _
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
        ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ h : ZMod q,
        ZMod.stdAddChar (A * h ^ 2 + B * h) *
          (∑ x : ZMod q, ZMod.stdAddChar ((2 * A * h) * x)) := by
      simp only [Finset.mul_sum]
    _ = ∑ h : ZMod q,
        ZMod.stdAddChar (A * h ^ 2 + B * h) *
          (if 2 * A * h = 0 then (q : ℂ) else 0) := by
      simp_rw [sum_stdAddChar_mul]

/-- The quadratic Gauss sum modulo one is one. -/
theorem quadraticGaussSum_one (A : ℤ) :
  quadraticGaussSum 1 (by omega) A = 1 := by
  let _ : NeZero 1 := ⟨by omega⟩
  rw [quadraticGaussSum_eq_sum]
  simp only [Fintype.sum_unique]
  rw [← (ZMod.stdAddChar (N := 1)).map_zero_eq_one]
  congr 1

/-- Every integral polynomial of degree at most two is its explicit quadratic
coefficient expansion. -/
theorem _root_.Polynomial.eq_quadraticPolynomial_of_natDegree_le
    (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2) :
  f = quadraticPolynomial (f.coeff 2) (f.coeff 1) (f.coeff 0) := by
  ext n
  change f.coeff n =
    (Polynomial.monomial 2 (f.coeff 2) +
      Polynomial.monomial 1 (f.coeff 1) +
      Polynomial.C (f.coeff 0)).coeff n
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_monomial,
    Polynomial.coeff_monomial, Polynomial.coeff_C]
  by_cases hn : n ≤ 2
  · interval_cases n <;> simp
  · have hfzero : f.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hdegree (by omega : 2 < n))
    simp [hfzero, show 2 ≠ n by omega, show 1 ≠ n by omega,
      show n ≠ 0 by omega]

private theorem isUnit_intCast_primePower
    (hp : p.Prime) (A : ℤ)
    (hA : ¬ p ∣ Int.natAbs A) :
    IsUnit (A : ZMod (p ^ a)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime]
  simpa using (hp.coprime_pow_of_not_dvd hA).symm

/-- A unit-coefficient quadratic Gauss sum modulo an odd prime has norm
`sqrt p`. -/
theorem quadraticGaussSum_oddPrime_base
    (hp : p.Prime) (hpodd : p ≠ 2) (A : ℤ)
    (hA : ¬ p ∣ Int.natAbs A) :
  ‖quadraticGaussSum p hp.pos A‖ = Real.sqrt p := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : NeZero p := ⟨hp.ne_zero⟩
  rw [quadraticGaussSum_eq_sum]
  have hAunit : IsUnit (A : ZMod p) := by
    rw [CharP.isUnit_intCast_iff hp]
    intro hdiv
    apply hA
    simpa using Int.natAbs_dvd_natAbs.mpr hdiv
  have htwo : (2 : ZMod p) ≠ 0 := by
    apply Ring.two_ne_zero
    rw [ZMod.ringChar_zmod_n]
    exact hpodd
  have hnorm := quadraticSum_normSq p (A : ZMod p) 0
  have hnorm' :
      (Complex.normSq
        (∑ x : ZMod p, ZMod.stdAddChar ((A : ZMod p) * x ^ 2)) : ℂ) = p := by
    simpa [htwo, hAunit.ne_zero] using hnorm
  have hnormReal :
      Complex.normSq
          (∑ x : ZMod p, ZMod.stdAddChar ((A : ZMod p) * x ^ 2)) = p := by
    exact_mod_cast hnorm'
  rw [Complex.norm_def, hnormReal]

/-- A quadratic Gauss sum modulo four with odd coefficient has norm `sqrt 8`. -/
theorem quadraticGaussSum_two_base_two
    (A : ℤ) (hA : Odd A) :
  ‖quadraticGaussSum 4 (by omega) A‖ = Real.sqrt 8 := by
  let _ : NeZero 4 := ⟨by omega⟩
  rw [quadraticGaussSum_eq_sum]
  rcases hA with ⟨k, rfl⟩
  have hnorm := quadraticSum_normSq 4
    (((2 * k + 1 : ℤ) : ZMod 4)) 0
  have htwoA :
      2 * (((2 * k + 1 : ℤ) : ZMod 4)) = 2 := by
    push_cast
    calc
      2 * (2 * (k : ZMod 4) + 1) = 4 * (k : ZMod 4) + 2 := by ring
      _ = 2 := by
        have hfour : (4 : ZMod 4) = 0 := ZMod.natCast_self 4
        rw [hfour, zero_mul, zero_add]
  rw [htwoA] at hnorm
  have hrhs :
      (∑ h : ZMod 4,
        ZMod.stdAddChar ((((2 * k + 1 : ℤ) : ZMod 4)) * h ^ 2 + 0 * h) *
          (if 2 * h = 0 then ((4 : ℕ) : ℂ) else 0)) = ((8 : ℕ) : ℂ) := by
    have htwo : (2 : ZMod 4) ≠ 0 := by decide
    have hfour : (4 : ZMod 4) = 0 := by decide
    have hsix : (6 : ZMod 4) ≠ 0 := by decide
    rw [← (ZMod.finEquiv 4).sum_comp]
    norm_num [Fin.sum_univ_succ, finEquiv_apply_eq_natCast, htwo, hfour, hsix]
    rw [if_pos hfour]
    have hphase : (2 * (k : ZMod 4) + 1) * 4 = 0 := by rw [hfour, mul_zero]
    rw [hphase, (ZMod.stdAddChar (N := 4)).map_zero_eq_one]
    norm_num
  rw [hrhs] at hnorm
  have hnormReal :
      Complex.normSq
          (∑ x : ZMod 4,
            ZMod.stdAddChar ((((2 * k + 1 : ℤ) : ZMod 4)) * x ^ 2)) = 8 := by
    have hnorm' :
        (Complex.normSq
          (∑ x : ZMod 4,
            ZMod.stdAddChar ((((2 * k + 1 : ℤ) : ZMod 4)) * x ^ 2)) : ℂ) = 8 := by
      simpa using hnorm
    exact_mod_cast hnorm'
  rw [Complex.norm_def, hnormReal]

/-- A quadratic Gauss sum modulo eight with odd coefficient has norm four. -/
theorem quadraticGaussSum_two_base_three
    (A : ℤ) (hA : Odd A) :
  ‖quadraticGaussSum 8 (by omega) A‖ = 4 := by
  let _ : NeZero 8 := ⟨by omega⟩
  rw [quadraticGaussSum_eq_sum]
  rcases hA with ⟨k, rfl⟩
  have hnorm := quadraticSum_normSq 8
    (((2 * k + 1 : ℤ) : ZMod 8)) 0
  have htwoA :
      2 * (((2 * k + 1 : ℤ) : ZMod 8)) = 2 ∨
        2 * (((2 * k + 1 : ℤ) : ZMod 8)) = 6 := by
    rcases k.even_or_odd with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left
      push_cast
      calc
        2 * (2 * ((j : ZMod 8) + j) + 1) = 8 * (j : ZMod 8) + 2 := by ring
        _ = 2 := by
          have height : (8 : ZMod 8) = 0 := ZMod.natCast_self 8
          rw [height, zero_mul, zero_add]
    · right
      push_cast
      calc
        2 * (2 * (2 * (j : ZMod 8) + 1) + 1) = 8 * (j : ZMod 8) + 6 := by ring
        _ = 6 := by
          have height : (8 : ZMod 8) = 0 := ZMod.natCast_self 8
          rw [height, zero_mul, zero_add]
  have hkernel (h : ZMod 8) :
      2 * (((2 * k + 1 : ℤ) : ZMod 8)) * h = 0 ↔ 2 * h = 0 := by
    rcases htwoA with htwoA | htwoA
    · rw [htwoA]
    · rw [htwoA]
      fin_cases h <;> decide
  simp_rw [hkernel] at hnorm
  have hrhs :
      (∑ h : ZMod 8,
        ZMod.stdAddChar ((((2 * k + 1 : ℤ) : ZMod 8)) * h ^ 2 + 0 * h) *
          (if 2 * h = 0 then ((8 : ℕ) : ℂ) else 0)) = ((16 : ℕ) : ℂ) := by
    have htwo : (2 : ZMod 8) ≠ 0 := by decide
    have hfour : (4 : ZMod 8) ≠ 0 := by decide
    have hsix : (6 : ZMod 8) ≠ 0 := by decide
    have height : (8 : ZMod 8) = 0 := by decide
    have hten : (10 : ZMod 8) ≠ 0 := by decide
    have htwelve : (12 : ZMod 8) ≠ 0 := by decide
    have hfourteen : (14 : ZMod 8) ≠ 0 := by decide
    have hsixteen : (16 : ZMod 8) = 0 := by decide
    rw [← (ZMod.finEquiv 8).sum_comp]
    norm_num [Fin.sum_univ_succ, finEquiv_apply_eq_natCast, htwo, hfour,
      hsix, height, hten, htwelve, hfourteen, hsixteen]
    rw [if_pos height]
    have hphase : (2 * (k : ZMod 8) + 1) * 16 = 0 := by rw [hsixteen, mul_zero]
    rw [hphase, (ZMod.stdAddChar (N := 8)).map_zero_eq_one]
    norm_num
  rw [hrhs] at hnorm
  have hnormReal :
      Complex.normSq
          (∑ x : ZMod 8,
            ZMod.stdAddChar ((((2 * k + 1 : ℤ) : ZMod 8)) * x ^ 2)) = 16 := by
    have hnorm' :
        (Complex.normSq
          (∑ x : ZMod 8,
            ZMod.stdAddChar ((((2 * k + 1 : ℤ) : ZMod 8)) * x ^ 2)) : ℂ) = 16 := by
      simpa using hnorm
    exact_mod_cast hnorm'
  rw [Complex.norm_def, hnormReal]
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem nonconstantContentNat_eq_natAbs_coeff_one
    (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 1) :
    Polynomial.nonconstantContentNat f = Int.natAbs (f.coeff 1) := by
  have htwo : f.coeff 2 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hdegree (by omega))
  rw [f.eq_quadraticPolynomial_of_natDegree_le (hdegree.trans (by omega)), htwo]
  have hpart :
      Polynomial.nonconstantPart
          (quadraticPolynomial 0 (f.coeff 1) (f.coeff 0)) =
        Polynomial.monomial 1 (f.coeff 1) := by
    ext n
    simp [Polynomial.nonconstantPart, quadraticPolynomial,
      Polynomial.coeff_monomial]
  have hcoeff :
      (quadraticPolynomial 0 (f.coeff 1) (f.coeff 0)).coeff 1 = f.coeff 1 := by
    change
      (Polynomial.monomial 2 0 + Polynomial.monomial 1 (f.coeff 1) +
        Polynomial.C (f.coeff 0)).coeff 1 = f.coeff 1
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_monomial,
      Polynomial.coeff_monomial, Polynomial.coeff_C]
    simp
  rw [Polynomial.nonconstantContentNat, Polynomial.contentNat, hpart,
    Polynomial.content_monomial]
  rw [← Int.abs_eq_normalize, Int.natAbs_abs]
  rw [hcoeff]

private theorem linear_completeSum_eq_zero_of_isUnit
    (q : ℕ) [NeZero q] (hq : 0 < q) (hq1 : 1 < q) (B C : ℤ)
    (hB : IsUnit (B : ZMod q)) :
    polynomialCompleteSum q hq (quadraticPolynomial 0 B C) = 0 := by
  let _ : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (by omega)
  rw [polynomialCompleteSum_quadratic]
  simp only [Int.cast_zero, zero_mul, zero_add]
  simp_rw [AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul]
  have horth := AddChar.sum_mulShift (B : ZMod q)
    (ZMod.isPrimitive_stdAddChar q)
  rw [if_neg hB.ne_zero] at horth
  have hsum : ∑ x : ZMod q, ZMod.stdAddChar ((B : ZMod q) * x) = 0 := by
    simpa [mul_comm] using horth
  rw [hsum, zero_mul]

/-- A primitive genuinely linear complete sum modulo a prime power vanishes. -/
theorem linear_polynomialCompleteSum_eq_zero
    (hq : 1 < q) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 1)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  polynomialCompleteSum q (Nat.zero_lt_of_lt hq) f = 0 := by
  let _ : NeZero q := ⟨by omega⟩
  have hBcoprime : Nat.Coprime q (Int.natAbs (f.coeff 1)) := by
    simpa [nonconstantContentNat_eq_natAbs_coeff_one f hdegree] using hprimitive
  have hB : IsUnit (f.coeff 1 : ZMod q) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime]
    simpa using hBcoprime
  have htwo : f.coeff 2 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hdegree (by omega))
  rw [f.eq_quadraticPolynomial_of_natDegree_le (hdegree.trans (by omega)), htwo]
  exact linear_completeSum_eq_zero_of_isUnit q (Nat.zero_lt_of_lt hq) hq _ _ hB

/-- The complete-sum bound for integral polynomials of degree at most one. -/
theorem linear_polynomialCompleteSum_bound
    (hq : 0 < q) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 1)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤ 1 := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hq.ne') with hq1 | hqgt
  · subst q
    let _ : NeZero 1 := ⟨by omega⟩
    simp [polynomialCompleteSum]
  · rw [linear_polynomialCompleteSum_eq_zero hqgt f hdegree hprimitive, norm_zero]
    norm_num

private theorem quadraticSum_norm_of_isUnit_two_mul
    (q : ℕ) [NeZero q] (A B : ZMod q) (hunit : IsUnit (2 * A)) :
    ‖∑ x : ZMod q, ZMod.stdAddChar (A * x ^ 2 + B * x)‖ = Real.sqrt q := by
  have hnorm := quadraticSum_normSq q A B
  have hkernel (h : ZMod q) : 2 * A * h = 0 ↔ h = 0 := by
    rcases hunit with ⟨u, hu⟩
    rw [← hu]
    simp
  simp_rw [hkernel] at hnorm
  have hnorm' :
      (Complex.normSq
        (∑ x : ZMod q, ZMod.stdAddChar (A * x ^ 2 + B * x)) : ℂ) = q := by
    simpa using hnorm
  have hnormReal :
      Complex.normSq (∑ x : ZMod q, ZMod.stdAddChar (A * x ^ 2 + B * x)) = q := by
    exact_mod_cast hnorm'
  rw [Complex.norm_def, hnormReal]

private theorem quadraticCompleteSum_norm_of_isUnit_two_mul
    (q : ℕ) [NeZero q] (hq : 0 < q) (A B C : ℤ)
    (hunit : IsUnit (2 * (A : ZMod q))) :
    ‖polynomialCompleteSum q hq (quadraticPolynomial A B C)‖ = Real.sqrt q := by
  rw [polynomialCompleteSum_quadratic]
  have hfactor :
      (∑ x : ZMod q,
          ZMod.stdAddChar ((A : ZMod q) * x ^ 2 + (B : ZMod q) * x + (C : ZMod q))) =
        (∑ x : ZMod q,
          ZMod.stdAddChar ((A : ZMod q) * x ^ 2 + (B : ZMod q) * x)) *
          ZMod.stdAddChar (C : ZMod q) := by
    simp_rw [AddChar.map_add_eq_mul]
    rw [Finset.sum_mul]
  rw [hfactor, norm_mul, quadraticSum_norm_of_isUnit_two_mul q _ _ hunit,
    (ZMod.stdAddChar (N := q)).norm_apply, mul_one]

/-- Completing the square identifies an odd-prime-power quadratic sum with a
unit scalar times the corresponding pure Gauss sum. -/
theorem quadraticCompleteSum_oddPrime_completeSquare
    (hp : p.Prime) (hpodd : p ≠ 2) (ha : 0 < a)
    (A B C : ℤ) (hA : ¬ p ∣ Int.natAbs A) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos _)
      (quadraticPolynomial A B C)‖ =
    ‖quadraticGaussSum (p ^ a) (pow_pos hp.pos _) A‖ := by
  have _ha : 0 < a := ha
  let _ : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hAunit : IsUnit (A : ZMod (p ^ a)) :=
    isUnit_intCast_primePower hp A hA
  have htwo_not_dvd : ¬ p ∣ Int.natAbs (2 : ℤ) := by
    change ¬ p ∣ 2
    intro hdiv
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hpone | hptwo
    · exact hp.ne_one hpone
    · exact hpodd hptwo
  have htwoUnit : IsUnit (2 : ZMod (p ^ a)) :=
    by simpa only [Int.cast_ofNat] using
      (isUnit_intCast_primePower hp 2 htwo_not_dvd)
  have hunit : IsUnit (2 * (A : ZMod (p ^ a))) := htwoUnit.mul hAunit
  rw [quadraticCompleteSum_norm_of_isUnit_two_mul _ _ _ _ _ hunit,
    quadraticGaussSum_eq_sum]
  symm
  simpa using
    (quadraticSum_norm_of_isUnit_two_mul (p ^ a) (A : ZMod (p ^ a)) 0 hunit)

/-- Exact norm of a primitive quadratic complete sum modulo an odd prime
power. -/
theorem quadratic_oddPrimePower_norm
    (hp : p.Prime) (hpodd : p ≠ 2) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ 2)
    (hquadratic : ¬ p ∣ Int.natAbs (f.coeff 2)) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ =
    Real.sqrt (p ^ a) := by
  have _ha : 0 < a := ha
  rw [f.eq_quadraticPolynomial_of_natDegree_le hdegree]
  let _ : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hAunit : IsUnit (f.coeff 2 : ZMod (p ^ a)) :=
    isUnit_intCast_primePower hp _ hquadratic
  have htwo_not_dvd : ¬ p ∣ Int.natAbs (2 : ℤ) := by
    change ¬ p ∣ 2
    intro hdiv
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hpone | hptwo
    · exact hp.ne_one hpone
    · exact hpodd hptwo
  have htwoUnit : IsUnit (2 : ZMod (p ^ a)) :=
    by simpa only [Int.cast_ofNat] using
      (isUnit_intCast_primePower hp 2 htwo_not_dvd)
  simpa using
    (quadraticCompleteSum_norm_of_isUnit_two_mul (p ^ a) (pow_pos hp.pos a)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (htwoUnit.mul hAunit))

private theorem stdAddChar_mod_two_one :
    ZMod.stdAddChar (1 : ZMod 2) = (-1 : ℂ) := by
  change ZMod.stdAddChar ((1 : ℤ) : ZMod 2) = (-1 : ℂ)
  rw [ZMod.stdAddChar_coe]
  norm_num
  rw [show 2 * (π : ℂ) * Complex.I / 2 = (π : ℂ) * Complex.I by ring]
  exact Complex.exp_pi_mul_I

/-- Exact norm of a quadratic complete sum modulo two in the primitive parity
cases. -/
theorem quadraticCompleteSum_mod_two_norm
    (A B C : ℤ) :
  ‖polynomialCompleteSum 2 (by omega) (quadraticPolynomial A B C)‖ =
    if Even (A + B) then 2 else 0 := by
  let _ : NeZero 2 := ⟨by omega⟩
  rw [polynomialCompleteSum_quadratic]
  have hsum :
      (∑ x : ZMod 2,
        ZMod.stdAddChar ((A : ZMod 2) * x ^ 2 + (B : ZMod 2) * x + (C : ZMod 2))) =
      ZMod.stdAddChar (C : ZMod 2) +
        ZMod.stdAddChar ((A + B + C : ℤ) : ZMod 2) := by
    rw [← (ZMod.finEquiv 2).sum_comp]
    norm_num [Fin.sum_univ_succ, finEquiv_apply_eq_natCast]
  rw [hsum]
  by_cases heven : Even (A + B)
  · rw [if_pos heven]
    have hzero : ((A + B : ℤ) : ZMod 2) = 0 :=
      ZMod.intCast_eq_zero_iff_even.mpr heven
    have harg : ((A + B + C : ℤ) : ZMod 2) = (C : ZMod 2) := by
      push_cast
      calc
        (A : ZMod 2) + B + C = ((A + B : ℤ) : ZMod 2) + C := by push_cast; ring
        _ = C := by rw [hzero, zero_add]
    rw [harg, ← two_mul, norm_mul,
      (ZMod.stdAddChar (N := 2)).norm_apply, mul_one]
    norm_num
  · rw [if_neg heven]
    have hodd : Odd (A + B) := by
      rcases (A + B).even_or_odd with he | ho
      · exact (heven he).elim
      · exact ho
    rcases hodd with ⟨k, hk⟩
    have hone : ((A + B : ℤ) : ZMod 2) = 1 := by
      rw [hk]
      push_cast
      have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
      rw [htwo, zero_mul, zero_add]
    have harg : ((A + B + C : ℤ) : ZMod 2) = 1 + (C : ZMod 2) := by
      push_cast
      calc
        (A : ZMod 2) + B + C = ((A + B : ℤ) : ZMod 2) + C := by push_cast; ring
        _ = 1 + C := by rw [hone]
    rw [harg, AddChar.map_add_eq_mul, stdAddChar_mod_two_one]
    ring_nf
    rw [norm_zero]

/-- The square-root type bound for primitive quadratic sums modulo two. -/
theorem quadratic_mod_two_bound
    (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hprimitive : Nat.Coprime 2 (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum 2 (by omega) f‖ ≤ 2 := by
  have _hprimitive := hprimitive
  rw [f.eq_quadraticPolynomial_of_natDegree_le hdegree,
    quadraticCompleteSum_mod_two_norm]
  split_ifs <;> norm_num

private theorem stdAddChar_twoPower_half
    (a : ℕ) (ha : 0 < a) :
    ZMod.stdAddChar ((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a)) = (-1 : ℂ) := by
  let _ : NeZero (2 ^ a) := ⟨pow_ne_zero _ (by omega)⟩
  rw [show ((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a)) =
      ((2 ^ (a - 1) : ℤ) : ZMod (2 ^ a)) by norm_num]
  rw [ZMod.stdAddChar_coe]
  have hpow : (2 : ℕ) ^ a = 2 * 2 ^ (a - 1) := by
    calc
      2 ^ a = 2 ^ ((a - 1) + 1) := by congr 1; omega
      _ = 2 ^ (a - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (a - 1) := by rw [mul_comm]
  rw [hpow]
  push_cast
  have hne : ((2 : ℂ) ^ (a - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show 2 * (π : ℂ) * Complex.I * (2 : ℂ) ^ (a - 1) /
      (2 * (2 : ℂ) ^ (a - 1)) = (π : ℂ) * Complex.I by field_simp]
  exact Complex.exp_pi_mul_I

private theorem quadraticCompleteSum_twoPower_linear_odd_eq_zero
    (a : ℕ) (ha : 2 ≤ a) (A B C : ℤ) (hB : Odd B) :
    polynomialCompleteSum (2 ^ a) (pow_pos (by omega) a)
      (quadraticPolynomial A B C) = 0 := by
  let _ : NeZero (2 ^ a) := ⟨pow_ne_zero _ (by omega)⟩
  rw [polynomialCompleteSum_quadratic]
  let H : ZMod (2 ^ a) := ((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a))
  have htwoH : 2 * H = 0 := by
    dsimp [H]
    have hpow : (2 : ℕ) * 2 ^ (a - 1) = 2 ^ a := by
      calc
        2 * 2 ^ (a - 1) = 2 ^ (a - 1) * 2 := by rw [mul_comm]
        _ = 2 ^ ((a - 1) + 1) := by rw [pow_succ]
        _ = 2 ^ a := by congr 1; omega
    calc
      (2 : ZMod (2 ^ a)) * ((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a)) =
          (((2 : ℕ) * 2 ^ (a - 1) : ℕ) : ZMod (2 ^ a)) := by norm_num
      _ = 0 := by rw [hpow, ZMod.natCast_self]
  have hHH : H ^ 2 = 0 := by
    have hdvd : 2 ^ a ∣ (2 ^ (a - 1)) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega : a ≤ (a - 1) * 2)
    rcases hdvd with ⟨d, hd⟩
    dsimp [H]
    calc
      (((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a))) ^ 2 =
          (((2 ^ (a - 1)) ^ 2 : ℕ) : ZMod (2 ^ a)) := by norm_num
      _ = 0 := by rw [hd, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hBH : (B : ZMod (2 ^ a)) * H = H := by
    rcases hB with ⟨k, rfl⟩
    push_cast
    calc
      ((2 : ZMod (2 ^ a)) * (k : ZMod (2 ^ a)) + 1) * H =
          (k : ZMod (2 ^ a)) * (2 * H) + H := by ring
      _ = H := by rw [htwoH, mul_zero, zero_add]
  have hphase (x : ZMod (2 ^ a)) :
      (A : ZMod (2 ^ a)) * (x + H) ^ 2 + (B : ZMod (2 ^ a)) * (x + H) +
          (C : ZMod (2 ^ a)) =
        ((A : ZMod (2 ^ a)) * x ^ 2 + (B : ZMod (2 ^ a)) * x +
          (C : ZMod (2 ^ a))) + H := by
    calc
      _ = ((A : ZMod (2 ^ a)) * x ^ 2 + (B : ZMod (2 ^ a)) * x + C) +
          ((A : ZMod (2 ^ a)) * x * (2 * H) + A * H ^ 2 + B * H) := by ring
      _ = ((A : ZMod (2 ^ a)) * x ^ 2 + (B : ZMod (2 ^ a)) * x + C) + H := by
        rw [htwoH, mul_zero, hHH, mul_zero, hBH, zero_add, zero_add]
  have hcharH : ZMod.stdAddChar H = (-1 : ℂ) :=
    stdAddChar_twoPower_half a (by omega)
  have hshift :
      (∑ x : ZMod (2 ^ a),
        ZMod.stdAddChar ((A : ZMod (2 ^ a)) * x ^ 2 + (B : ZMod (2 ^ a)) * x +
          (C : ZMod (2 ^ a)))) =
      -(∑ x : ZMod (2 ^ a),
        ZMod.stdAddChar ((A : ZMod (2 ^ a)) * x ^ 2 + (B : ZMod (2 ^ a)) * x +
          (C : ZMod (2 ^ a)))) := by
    calc
      _ = ∑ x : ZMod (2 ^ a),
          ZMod.stdAddChar ((A : ZMod (2 ^ a)) * (x + H) ^ 2 +
            (B : ZMod (2 ^ a)) * (x + H) + (C : ZMod (2 ^ a))) := by
        exact (Fintype.sum_bijective (fun x : ZMod (2 ^ a) ↦ x + H)
          (AddGroup.addRight_bijective H) _ _ (fun _ ↦ rfl)).symm
      _ = ∑ x : ZMod (2 ^ a),
          -ZMod.stdAddChar ((A : ZMod (2 ^ a)) * x ^ 2 +
            (B : ZMod (2 ^ a)) * x + (C : ZMod (2 ^ a))) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hphase, AddChar.map_add_eq_mul, hcharH]
        ring
      _ = _ := by rw [Finset.sum_neg_distrib]
  have htwoSum :
      2 * (∑ x : ZMod (2 ^ a),
        ZMod.stdAddChar ((A : ZMod (2 ^ a)) * x ^ 2 + (B : ZMod (2 ^ a)) * x +
          (C : ZMod (2 ^ a)))) = 0 := by
    linear_combination hshift
  exact (mul_eq_zero.mp htwoSum).resolve_left (by norm_num)

/-- A quadratic complete sum modulo a nontrivial power of two vanishes when
its linear coefficient is odd. -/
theorem quadratic_twoPower_linear_odd_eq_zero
    (ha : 2 ≤ a) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hlinear : Odd (f.coeff 1)) :
  polynomialCompleteSum (2 ^ a) (pow_pos (by omega) a) f = 0 := by
  rw [f.eq_quadraticPolynomial_of_natDegree_le hdegree]
  exact quadraticCompleteSum_twoPower_linear_odd_eq_zero a ha _ _ _ hlinear

/-- A quadratic complete sum modulo an odd prime power vanishes when its
linear coefficient is a unit and its quadratic coefficient is not. -/
theorem quadratic_primePower_linear_unit_eq_zero
    (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ 2)
    (hlinear : ¬ p ∣ Int.natAbs (f.coeff 1))
    (hquadratic : p ∣ Int.natAbs (f.coeff 2)) :
  polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f = 0 := by
  rw [f.eq_quadraticPolynomial_of_natDegree_le hdegree]
  let _ : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [polynomialCompleteSum_quadratic]
  let H : ZMod (p ^ a) := ((p ^ (a - 1) : ℕ) : ZMod (p ^ a))
  have hpH : (p : ZMod (p ^ a)) * H = 0 := by
    dsimp [H]
    have hpow : p * p ^ (a - 1) = p ^ a := by
      calc
        p * p ^ (a - 1) = p ^ (a - 1) * p := by rw [mul_comm]
        _ = p ^ ((a - 1) + 1) := by rw [pow_succ]
        _ = p ^ a := by congr 1; omega
    calc
      (p : ZMod (p ^ a)) * ((p ^ (a - 1) : ℕ) : ZMod (p ^ a)) =
          ((p * p ^ (a - 1) : ℕ) : ZMod (p ^ a)) := by norm_num
      _ = 0 := by rw [hpow, ZMod.natCast_self]
  have hAdiv : (p : ℤ) ∣ f.coeff 2 :=
    Int.natAbs_dvd_natAbs.mp hquadratic
  rcases hAdiv with ⟨k, hk⟩
  have hAH : (f.coeff 2 : ZMod (p ^ a)) * H = 0 := by
    rw [hk]
    push_cast
    calc
      ((p : ZMod (p ^ a)) * (k : ZMod (p ^ a))) * H =
          (k : ZMod (p ^ a)) * (p * H) := by ring
      _ = 0 := by rw [hpH, mul_zero]
  have hHne : H ≠ 0 := by
    dsimp [H]
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (pow_pos hp.pos _)
      (Nat.pow_lt_pow_right hp.one_lt (by omega))
  have hBunit : IsUnit (f.coeff 1 : ZMod (p ^ a)) :=
    isUnit_intCast_primePower hp _ hlinear
  have hDne : (f.coeff 1 : ZMod (p ^ a)) * H ≠ 0 := by
    rcases hBunit with ⟨u, hu⟩
    rw [← hu]
    simpa using hHne
  have hchar_ne :
      ZMod.stdAddChar ((f.coeff 1 : ZMod (p ^ a)) * H) ≠ 1 := by
    intro heq
    apply hDne
    apply ZMod.injective_stdAddChar
    simpa using heq
  have hphase (x : ZMod (p ^ a)) :
      (f.coeff 2 : ZMod (p ^ a)) * (x + H) ^ 2 +
          (f.coeff 1 : ZMod (p ^ a)) * (x + H) +
          (f.coeff 0 : ZMod (p ^ a)) =
        ((f.coeff 2 : ZMod (p ^ a)) * x ^ 2 +
          (f.coeff 1 : ZMod (p ^ a)) * x + (f.coeff 0 : ZMod (p ^ a))) +
          (f.coeff 1 : ZMod (p ^ a)) * H := by
    calc
      _ = ((f.coeff 2 : ZMod (p ^ a)) * x ^ 2 +
          (f.coeff 1 : ZMod (p ^ a)) * x + f.coeff 0) +
          (2 * x * ((f.coeff 2 : ZMod (p ^ a)) * H) +
            H * ((f.coeff 2 : ZMod (p ^ a)) * H) + f.coeff 1 * H) := by ring
      _ = _ := by rw [hAH, mul_zero, mul_zero, zero_add, zero_add]
  have hshift :
      (∑ x : ZMod (p ^ a),
        ZMod.stdAddChar ((f.coeff 2 : ZMod (p ^ a)) * x ^ 2 +
          (f.coeff 1 : ZMod (p ^ a)) * x + (f.coeff 0 : ZMod (p ^ a)))) =
      (∑ x : ZMod (p ^ a),
        ZMod.stdAddChar ((f.coeff 2 : ZMod (p ^ a)) * x ^ 2 +
          (f.coeff 1 : ZMod (p ^ a)) * x + (f.coeff 0 : ZMod (p ^ a)))) *
        ZMod.stdAddChar ((f.coeff 1 : ZMod (p ^ a)) * H) := by
    calc
      _ = ∑ x : ZMod (p ^ a),
          ZMod.stdAddChar ((f.coeff 2 : ZMod (p ^ a)) * (x + H) ^ 2 +
            (f.coeff 1 : ZMod (p ^ a)) * (x + H) +
            (f.coeff 0 : ZMod (p ^ a))) := by
        exact (Fintype.sum_bijective (fun x : ZMod (p ^ a) ↦ x + H)
          (AddGroup.addRight_bijective H) _ _ (fun _ ↦ rfl)).symm
      _ = _ := by
        simp_rw [hphase, AddChar.map_add_eq_mul]
        rw [Finset.sum_mul]
  have hfactor :
      (1 - ZMod.stdAddChar ((f.coeff 1 : ZMod (p ^ a)) * H)) *
        (∑ x : ZMod (p ^ a),
          ZMod.stdAddChar ((f.coeff 2 : ZMod (p ^ a)) * x ^ 2 +
            (f.coeff 1 : ZMod (p ^ a)) * x + (f.coeff 0 : ZMod (p ^ a)))) = 0 := by
    linear_combination hshift
  exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hchar_ne.symm)

private theorem not_two_dvd_natAbs_of_odd (A : ℤ) (hA : Odd A) :
    ¬ 2 ∣ Int.natAbs A := by
  intro hdiv
  have hdivInt : (2 : ℤ) ∣ A := Int.natAbs_dvd_natAbs.mp hdiv
  rcases hA with ⟨k, hk⟩
  rcases hdivInt with ⟨j, hj⟩
  omega

private theorem quadraticSum_norm_twoPower_of_odd_even
    (a : ℕ) (ha : 2 ≤ a) (A B : ℤ) (hA : Odd A) (hB : Even B) :
    ‖∑ x : ZMod (2 ^ a),
      ZMod.stdAddChar ((A : ZMod (2 ^ a)) * x ^ 2 + (B : ZMod (2 ^ a)) * x)‖ =
      Real.sqrt (2 * 2 ^ a) := by
  let _ : NeZero (2 ^ a) := ⟨pow_ne_zero _ (by omega)⟩
  let H : ZMod (2 ^ a) := ((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a))
  have htwoH : 2 * H = 0 := by
    dsimp [H]
    have hpow : (2 : ℕ) * 2 ^ (a - 1) = 2 ^ a := by
      calc
        2 * 2 ^ (a - 1) = 2 ^ (a - 1) * 2 := by rw [mul_comm]
        _ = 2 ^ ((a - 1) + 1) := by rw [pow_succ]
        _ = 2 ^ a := by congr 1; omega
    calc
      (2 : ZMod (2 ^ a)) * ((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a)) =
          (((2 : ℕ) * 2 ^ (a - 1) : ℕ) : ZMod (2 ^ a)) := by norm_num
      _ = 0 := by rw [hpow, ZMod.natCast_self]
  have hHH : H ^ 2 = 0 := by
    have hdvd : 2 ^ a ∣ (2 ^ (a - 1)) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega : a ≤ (a - 1) * 2)
    rcases hdvd with ⟨d, hd⟩
    dsimp [H]
    calc
      (((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a))) ^ 2 =
          (((2 ^ (a - 1)) ^ 2 : ℕ) : ZMod (2 ^ a)) := by norm_num
      _ = 0 := by rw [hd, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hHne : H ≠ 0 := by
    dsimp [H]
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (pow_pos (by omega) _)
      (Nat.pow_lt_pow_right (by omega) (by omega))
  have hBHzero : (B : ZMod (2 ^ a)) * H = 0 := by
    rcases hB with ⟨k, rfl⟩
    push_cast
    calc
      ((k : ZMod (2 ^ a)) + k) * H =
          (k : ZMod (2 ^ a)) * (2 * H) := by ring
      _ = 0 := by rw [htwoH, mul_zero]
  have hAunit : IsUnit (A : ZMod (2 ^ a)) :=
    isUnit_intCast_primePower Nat.prime_two A (not_two_dvd_natAbs_of_odd A hA)
  have htwoKernel (h : ZMod (2 ^ a)) : 2 * h = 0 ↔ h = 0 ∨ h = H := by
    have hneg := ZMod.neg_eq_self_iff h
    have hval : 2 * h = 0 ↔ h = 0 ∨ 2 * h.val = 2 ^ a := by
      simpa [two_mul, neg_eq_iff_add_eq_zero] using hneg
    rw [hval]
    constructor
    · rintro (hh | hh)
      · exact Or.inl hh
      · right
        have hv : h.val = 2 ^ (a - 1) := by
          have hpow : 2 ^ a = 2 * 2 ^ (a - 1) := by
            calc
              2 ^ a = 2 ^ ((a - 1) + 1) := by congr 1; omega
              _ = 2 ^ (a - 1) * 2 := by rw [pow_succ]
              _ = 2 * 2 ^ (a - 1) := by rw [mul_comm]
          omega
        calc
          h = (h.val : ZMod (2 ^ a)) := h.natCast_zmod_val.symm
          _ = H := by rw [hv]
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · right
        have hpow : 2 * (2 ^ (a - 1)) = 2 ^ a := by
          calc
            2 * 2 ^ (a - 1) = 2 ^ (a - 1) * 2 := by rw [mul_comm]
            _ = 2 ^ ((a - 1) + 1) := by rw [pow_succ]
            _ = 2 ^ a := by congr 1; omega
        dsimp [H]
        rw [ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))]
        exact hpow
  have hkernel (h : ZMod (2 ^ a)) :
      2 * (A : ZMod (2 ^ a)) * h = 0 ↔ h = 0 ∨ h = H := by
    rw [show 2 * (A : ZMod (2 ^ a)) * h = (A : ZMod (2 ^ a)) * (2 * h) by ring]
    rcases hAunit with ⟨u, hu⟩
    rw [← hu]
    simpa using htwoKernel h
  have hnorm := quadraticSum_normSq (2 ^ a)
    (A : ZMod (2 ^ a)) (B : ZMod (2 ^ a))
  simp_rw [hkernel] at hnorm
  have hphaseH :
      (A : ZMod (2 ^ a)) * H ^ 2 + (B : ZMod (2 ^ a)) * H = 0 := by
    rw [hHH, mul_zero, hBHzero, zero_add]
  have hsummand (h : ZMod (2 ^ a)) :
      ZMod.stdAddChar ((A : ZMod (2 ^ a)) * h ^ 2 + (B : ZMod (2 ^ a)) * h) *
          (if h = 0 ∨ h = H then ((2 ^ a : ℕ) : ℂ) else 0) =
        if h = 0 then ((2 ^ a : ℕ) : ℂ)
        else if h = H then ((2 ^ a : ℕ) : ℂ) else 0 := by
    by_cases hzero : h = 0
    · subst h
      simp
    · by_cases hhalf : h = H
      · subst h
        simp [hHne, hphaseH]
      · simp [hzero, hhalf]
  simp_rw [hsummand] at hnorm
  have hsingle (y : ZMod (2 ^ a)) :
      (∑ x : ZMod (2 ^ a),
        if x = y then ((2 ^ a : ℕ) : ℂ) else 0) = ((2 ^ a : ℕ) : ℂ) := by
    simp
  have hsum :
      (∑ x : ZMod (2 ^ a),
        if x = 0 then ((2 ^ a : ℕ) : ℂ)
        else if x = H then ((2 ^ a : ℕ) : ℂ) else 0) =
          ((2 * 2 ^ a : ℕ) : ℂ) := by
    have hzeroH : (0 : ZMod (2 ^ a)) ≠ H := hHne.symm
    calc
      _ = (∑ x : ZMod (2 ^ a),
            if x = 0 then ((2 ^ a : ℕ) : ℂ) else 0) +
          (∑ x : ZMod (2 ^ a),
            if x = H then ((2 ^ a : ℕ) : ℂ) else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hxzero : x = 0
        · subst x
          simp [hzeroH]
        · by_cases hxhalf : x = H
          · subst x
            simp [hHne]
          · simp [hxzero, hxhalf]
      _ = _ := by rw [hsingle, hsingle]; push_cast; ring
  rw [hsum] at hnorm
  have hnormReal :
      Complex.normSq
        (∑ x : ZMod (2 ^ a),
          ZMod.stdAddChar ((A : ZMod (2 ^ a)) * x ^ 2 +
            (B : ZMod (2 ^ a)) * x)) = 2 * 2 ^ a := by
    exact_mod_cast hnorm
  rw [Complex.norm_def, hnormReal]

private theorem quadraticCompleteSum_norm_twoPower_of_odd_even
    (a : ℕ) (ha : 2 ≤ a) (A B C : ℤ) (hA : Odd A) (hB : Even B) :
    ‖polynomialCompleteSum (2 ^ a) (pow_pos (by omega) a)
      (quadraticPolynomial A B C)‖ = Real.sqrt (2 * 2 ^ a) := by
  let _ : NeZero (2 ^ a) := ⟨pow_ne_zero _ (by omega)⟩
  rw [polynomialCompleteSum_quadratic]
  have hfactor :
      (∑ x : ZMod (2 ^ a),
          ZMod.stdAddChar ((A : ZMod (2 ^ a)) * x ^ 2 +
            (B : ZMod (2 ^ a)) * x + (C : ZMod (2 ^ a))) =
        (∑ x : ZMod (2 ^ a),
          ZMod.stdAddChar ((A : ZMod (2 ^ a)) * x ^ 2 +
            (B : ZMod (2 ^ a)) * x)) * ZMod.stdAddChar (C : ZMod (2 ^ a))) := by
    simp_rw [AddChar.map_add_eq_mul]
    rw [Finset.sum_mul]
  rw [hfactor, norm_mul,
    quadraticSum_norm_twoPower_of_odd_even a ha A B hA hB,
    (ZMod.stdAddChar (N := 2 ^ a)).norm_apply, mul_one]

/-- Completing the square reduces the even-linear two-power quadratic sum to
the pure quadratic Gauss sum. -/
theorem quadraticCompleteSum_two_completeSquare
    (A B C : ℤ) (hA : Odd A) (hB : Even B)
    (a : ℕ) (ha : 2 ≤ a) :
  ‖polynomialCompleteSum (2 ^ a) (pow_pos (by omega) _)
      (quadraticPolynomial A B C)‖ =
    ‖quadraticGaussSum (2 ^ a) (pow_pos (by omega) _) A‖ := by
  rw [quadraticCompleteSum_norm_twoPower_of_odd_even a ha A B C hA hB,
    quadraticGaussSum_eq_sum]
  symm
  simpa using
    (quadraticSum_norm_twoPower_of_odd_even a ha A 0 hA (by simp))

/-- Exact norm of a primitive quadratic complete sum modulo a power of two. -/
theorem quadratic_twoPower_quadratic_odd_norm
    (ha : 2 ≤ a) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hlinear : Even (f.coeff 1)) (hquadratic : Odd (f.coeff 2)) :
  ‖polynomialCompleteSum (2 ^ a) (pow_pos (by omega) a) f‖ =
    Real.sqrt (2 * 2 ^ a) := by
  rw [f.eq_quadraticPolynomial_of_natDegree_le hdegree]
  exact quadraticCompleteSum_norm_twoPower_of_odd_even a ha _ _ _ hquadratic hlinear

/-- The exact two-step recurrence for unit-coefficient quadratic Gauss sums at
odd prime powers. -/
theorem quadraticGaussSum_oddPrime_recurrence
    (hp : p.Prime) (hpodd : p ≠ 2) (A : ℤ)
    (hA : ¬ p ∣ Int.natAbs A) (a : ℕ) :
  quadraticGaussSum (p ^ (a + 2)) (pow_pos hp.pos _) A =
    (p : ℂ) * quadraticGaussSum (p ^ a) (pow_pos hp.pos _) A := by
  have hp0 : p ≠ 0 := hp.ne_zero
  let _ : NeZero p := ⟨hp0⟩
  let _ : NeZero (p ^ a) := ⟨pow_ne_zero _ hp0⟩
  let _ : NeZero (p ^ (a + 1)) := ⟨pow_ne_zero _ hp0⟩
  let _ : NeZero (p ^ (a + 2)) := ⟨pow_ne_zero _ hp0⟩
  rw [quadraticGaussSum_eq_sum, quadraticGaussSum_eq_sum]
  have hq2 : p ^ (a + 2) = p * p ^ (a + 1) := by
    simp only [pow_add, pow_one, pow_two]
    ring
  have hq1 : p ^ (a + 1) = p ^ a * p := by
    simp only [pow_add, pow_one]
  have hq2' : p ^ (a + 2) = p ^ a * p ^ 2 := by
    simp only [pow_add]
  have hphase (y : ZMod p) (z : ZMod (p ^ (a + 1))) :
      ZMod.stdAddChar
          ((A : ZMod (p ^ (a + 2))) *
            ((z.val + p ^ (a + 1) * y.val : ℕ) : ZMod (p ^ (a + 2))) ^ 2) =
        ZMod.stdAddChar
            ((A : ZMod (p ^ (a + 2))) *
              ((z.val : ℕ) : ZMod (p ^ (a + 2))) ^ 2) *
          ZMod.stdAddChar
            (((2 * A * (z.val : ℤ) * (y.val : ℤ) : ℤ)) : ZMod p) := by
    have hlast :
        (((A * (p ^ (a + 1) : ℤ) ^ 2 * (y.val : ℤ) ^ 2 : ℤ)) :
          ZMod (p ^ (a + 2))) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hdvdNat : p ^ (a + 2) ∣ (p ^ (a + 1)) ^ 2 := by
        rw [← pow_mul]
        exact pow_dvd_pow p (by omega : a + 2 ≤ (a + 1) * 2)
      have hdvdInt : (p ^ (a + 2) : ℤ) ∣ (p ^ (a + 1) : ℤ) ^ 2 := by
        exact_mod_cast hdvdNat
      exact (hdvdInt.mul_left A).mul_right ((y.val : ℤ) ^ 2)
    have harg :
        (A : ZMod (p ^ (a + 2))) *
            ((z.val + p ^ (a + 1) * y.val : ℕ) : ZMod (p ^ (a + 2))) ^ 2 =
          (A : ZMod (p ^ (a + 2))) *
              ((z.val : ℕ) : ZMod (p ^ (a + 2))) ^ 2 +
            (((p ^ (a + 1) : ℤ) *
              (2 * A * (z.val : ℤ) * (y.val : ℤ)) : ℤ) :
                ZMod (p ^ (a + 2))) := by
      push_cast
      have hlast' :
          (A : ZMod (p ^ (a + 2))) * (p ^ (a + 1) : ZMod (p ^ (a + 2))) ^ 2 *
              (y.val : ZMod (p ^ (a + 2))) ^ 2 = 0 := by
        exact_mod_cast hlast
      rw [show
        (A : ZMod (p ^ (a + 2))) *
            ((z.val : ZMod (p ^ (a + 2))) +
              (p ^ (a + 1) : ZMod (p ^ (a + 2))) * y.val) ^ 2 =
          (A : ZMod (p ^ (a + 2))) * (z.val : ZMod (p ^ (a + 2))) ^ 2 +
            (p ^ (a + 1) : ZMod (p ^ (a + 2))) *
              (2 * A * z.val * y.val) +
            A * (p ^ (a + 1) : ZMod (p ^ (a + 2))) ^ 2 * y.val ^ 2 by ring,
        hlast', add_zero]
    rw [harg, AddChar.map_add_eq_mul]
    congr 1
    convert
      (stdAddChar_mul_modulus_eq (p ^ (a + 2)) p (p ^ (a + 1)) hq2
        (2 * A * (z.val : ℤ) * (y.val : ℤ))) using 1
    all_goals norm_num
  rw [sum_zmod_eq_mul (p ^ (a + 2)) p (p ^ (a + 1)) hq2]
  simp_rw [hphase]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have htwoAunit : IsUnit ((2 * A : ℤ) : ZMod p) := by
    rw [CharP.isUnit_intCast_iff hp]
    intro hdiv
    have hdivNat : p ∣ 2 * Int.natAbs A := by
      simpa [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr hdiv
    rcases hp.dvd_mul.mp hdivNat with hpTwo | hpA
    · rcases (Nat.dvd_prime Nat.prime_two).mp hpTwo with hpone | hptwo
      · exact hp.ne_one hpone
      · exact hpodd hptwo
    · exact hA hpA
  have hcoeff (z : ZMod (p ^ (a + 1))) :
      (((2 * A * (z.val : ℤ) : ℤ)) : ZMod p) = 0 ↔
        ((z.val : ℕ) : ZMod p) = 0 := by
    rcases htwoAunit with ⟨u, hu⟩
    have hcast :
        (((2 * A : ℤ)) : ZMod p) * ((z.val : ℕ) : ZMod p) =
          (((2 * A * (z.val : ℤ) : ℤ)) : ZMod p) := by norm_num
    rw [← hcast, ← hu]
    simp
  simp_rw [show ∀ z : ZMod (p ^ (a + 1)),
      (∑ y : ZMod p,
        ZMod.stdAddChar
          (((2 * A * (z.val : ℤ) * (y.val : ℤ) : ℤ)) : ZMod p)) =
        if ((z.val : ℕ) : ZMod p) = 0 then (p : ℂ) else 0 by
    intro z
    have hy (y : ZMod p) :
        (((2 * A * (z.val : ℤ) * (y.val : ℤ) : ℤ)) : ZMod p) =
          (((2 * A * (z.val : ℤ) : ℤ)) : ZMod p) * y := by
      have hycast : ((y.val : ℕ) : ZMod p) = y := y.natCast_zmod_val
      push_cast
      rw [hycast]
    simp_rw [hy]
    rw [sum_stdAddChar_mul]
    exact if_congr (hcoeff z) rfl rfl]
  rw [sum_zmod_eq_mul (p ^ (a + 1)) (p ^ a) p hq1]
  -- The low base-p digit is forced to vanish; the surviving phase descends by p².
  have hinner (w : ZMod (p ^ a)) :
      (∑ r : ZMod p,
        ZMod.stdAddChar
            ((A : ZMod (p ^ (a + 2))) *
              (((((r.val + p * w.val : ℕ) : ZMod (p ^ a * p))).val : ℕ) :
                ZMod (p ^ (a + 2))) ^ 2) *
          (if (((((r.val + p * w.val : ℕ) : ZMod (p ^ a * p))).val : ℕ) :
              ZMod p) = 0
            then (p : ℂ) else 0)) =
        (p : ℂ) *
          ZMod.stdAddChar ((A : ZMod (p ^ a)) * w ^ 2) := by
    have hval (r : ZMod p) :
        (((r.val + p * w.val : ℕ) : ZMod (p ^ a * p))).val = r.val + p * w.val := by
      rw [ZMod.val_natCast_of_lt]
      have hr : r.val < p := r.val_lt
      have hw : w.val < p ^ a := w.val_lt
      calc
        r.val + p * w.val < p + p * w.val := Nat.add_lt_add_right hr _
        _ = p * (w.val + 1) := by ring
        _ ≤ p * p ^ a := Nat.mul_le_mul_left p (Nat.succ_le_iff.mpr hw)
        _ = p ^ a * p := by rw [mul_comm]
    simp_rw [hval]
    have hlow (r : ZMod p) :
        ((r.val + p * w.val : ℕ) : ZMod p) = r := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
        r.natCast_zmod_val]
    simp_rw [hlow]
    rw [Finset.sum_eq_single 0]
    · simp only [ZMod.val_zero, zero_add]
      rw [if_true]
      have hdesc := stdAddChar_mul_modulus_eq (p ^ (a + 2)) (p ^ a) (p ^ 2) hq2'
        (A * (w.val : ℤ) ^ 2)
      have hwcast : ((w.val : ℕ) : ZMod (p ^ a)) = w := w.natCast_zmod_val
      have hdesc' :
          ZMod.stdAddChar
              ((A : ZMod (p ^ (a + 2))) *
                ((p * w.val : ℕ) : ZMod (p ^ (a + 2))) ^ 2) =
            ZMod.stdAddChar ((A : ZMod (p ^ a)) * w ^ 2) := by
        simpa [hwcast, pow_two, mul_assoc, mul_comm, mul_left_comm] using hdesc
      rw [hdesc']
      ring
    · intro r _ hr0
      rw [if_neg hr0, mul_zero]
    · simp
  calc
    _ = ∑ w : ZMod (p ^ a),
        (p : ℂ) * ZMod.stdAddChar ((A : ZMod (p ^ a)) * w ^ 2) := by
      apply Finset.sum_congr rfl
      intro w _
      exact hinner w
    _ = _ := by rw [Finset.mul_sum]

/-- The exact two-step recurrence for odd-coefficient quadratic Gauss sums at
powers of two. -/
theorem quadraticGaussSum_two_recurrence
    (A : ℤ) (hA : Odd A) (a : ℕ) (ha : 2 ≤ a) :
  quadraticGaussSum (2 ^ (a + 2)) (pow_pos (by omega) _) A =
    2 * quadraticGaussSum (2 ^ a) (pow_pos (by omega) _) A := by
  let _ : NeZero 2 := ⟨by omega⟩
  let _ : NeZero (2 ^ a) := ⟨pow_ne_zero _ (by omega)⟩
  let _ : NeZero (2 ^ (a + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  let _ : NeZero (2 ^ (a + 2)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [quadraticGaussSum_eq_sum, quadraticGaussSum_eq_sum]
  have hq2 : 2 ^ (a + 2) = 2 ^ (a + 1) * 2 := by
    simp only [pow_add, pow_one, pow_two]
    ring
  have hq1 : 2 ^ (a + 1) = 2 * 2 ^ a := by
    simp only [pow_add, pow_one]
    ring
  have hq2scale : 2 ^ (a + 2) = 2 ^ a * 4 := by
    norm_num [pow_add, pow_two]
  rw [sum_zmod_eq_mul (2 ^ (a + 2)) (2 ^ (a + 1)) 2 hq2]
  have hsplit (y : ZMod (2 ^ (a + 1))) :
      (∑ r : ZMod 2,
        ZMod.stdAddChar
          ((A : ZMod (2 ^ (a + 2))) *
            ((r.val + 2 * y.val : ℕ) : ZMod (2 ^ (a + 2))) ^ 2)) =
        ZMod.stdAddChar
            ((A : ZMod (2 ^ (a + 2))) *
              ((2 * y.val : ℕ) : ZMod (2 ^ (a + 2))) ^ 2) +
          ZMod.stdAddChar
            ((A : ZMod (2 ^ (a + 2))) *
              ((1 + 2 * y.val : ℕ) : ZMod (2 ^ (a + 2))) ^ 2) := by
    rw [← (ZMod.finEquiv 2).sum_comp]
    norm_num [Fin.sum_univ_succ, finEquiv_apply_eq_natCast]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hevenPhase (y : ZMod (2 ^ (a + 1))) :
      ZMod.stdAddChar
          ((A : ZMod (2 ^ (a + 2))) *
            ((2 * y.val : ℕ) : ZMod (2 ^ (a + 2))) ^ 2) =
        ZMod.stdAddChar
          ((A : ZMod (2 ^ a)) * ((y.val : ℕ) : ZMod (2 ^ a)) ^ 2) := by
    have hdesc := stdAddChar_mul_modulus_eq
      (2 ^ (a + 2)) (2 ^ a) 4 hq2scale (A * (y.val : ℤ) ^ 2)
    have hfour : (4 : ZMod (2 ^ (a + 2))) = 2 * 2 := by norm_num
    simpa [hfour, pow_two, mul_assoc, mul_comm, mul_left_comm] using hdesc
  simp_rw [hevenPhase]
  have hevenSum :
      (∑ y : ZMod (2 ^ (a + 1)),
        ZMod.stdAddChar
          ((A : ZMod (2 ^ a)) * ((y.val : ℕ) : ZMod (2 ^ a)) ^ 2)) =
        2 * ∑ w : ZMod (2 ^ a),
          ZMod.stdAddChar ((A : ZMod (2 ^ a)) * w ^ 2) := by
    rw [sum_zmod_eq_mul (2 ^ (a + 1)) 2 (2 ^ a) hq1]
    have hinner (t : ZMod 2) :
        (∑ w : ZMod (2 ^ a),
          ZMod.stdAddChar
            ((A : ZMod (2 ^ a)) *
              (((((w.val + 2 ^ a * t.val : ℕ) : ZMod (2 ^ (a + 1)))).val : ℕ) :
                ZMod (2 ^ a)) ^ 2)) =
          ∑ w : ZMod (2 ^ a),
            ZMod.stdAddChar ((A : ZMod (2 ^ a)) * w ^ 2) := by
      apply Finset.sum_congr rfl
      intro w _
      have ht : t.val = 0 ∨ t.val = 1 := by
        have htlt := t.val_lt
        omega
      have hval :
          (((w.val + 2 ^ a * t.val : ℕ) : ZMod (2 ^ (a + 1)))).val =
            w.val + 2 ^ a * t.val := by
        rw [ZMod.val_natCast_of_lt]
        rcases ht with ht | ht <;> rw [ht]
        · simp only [mul_zero, add_zero]
          exact w.val_lt.trans_le (by omega)
        · simp only [mul_one]
          have hw := w.val_lt
          omega
      rw [hval, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
        add_zero, w.natCast_zmod_val]
    simp_rw [hinner]
    simp [ZMod.card]
  rw [hevenSum]
  have hoddSum :
      (∑ y : ZMod (2 ^ (a + 1)),
        ZMod.stdAddChar
          ((A : ZMod (2 ^ (a + 2))) *
            ((1 + 2 * y.val : ℕ) : ZMod (2 ^ (a + 2))) ^ 2)) = 0 := by
    let H : ZMod (2 ^ (a + 1)) :=
      ((2 ^ (a - 1) : ℕ) : ZMod (2 ^ (a + 1)))
    let K : ZMod (2 ^ (a + 2)) :=
      ((2 ^ a : ℕ) : ZMod (2 ^ (a + 2)))
    have hfourK : 4 * K = 0 := by
      dsimp [K]
      have hpow : (4 : ℕ) * 2 ^ a = 2 ^ (a + 2) := by
        norm_num [pow_add, pow_two]
        ring
      calc
        (4 : ZMod (2 ^ (a + 2))) * ((2 ^ a : ℕ) : ZMod (2 ^ (a + 2))) =
            (((4 : ℕ) * 2 ^ a : ℕ) : ZMod (2 ^ (a + 2))) := by norm_num
        _ = 0 := by rw [hpow, ZMod.natCast_self]
    have hKK : K ^ 2 = 0 := by
      have hdvd : 2 ^ (a + 2) ∣ (2 ^ a) ^ 2 := by
        rw [← pow_mul]
        exact pow_dvd_pow 2 (by omega : a + 2 ≤ a * 2)
      rcases hdvd with ⟨d, hd⟩
      dsimp [K]
      calc
        (((2 ^ a : ℕ) : ZMod (2 ^ (a + 2)))) ^ 2 =
            (((2 ^ a) ^ 2 : ℕ) : ZMod (2 ^ (a + 2))) := by norm_num
        _ = 0 := by rw [hd, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    have hAK : (A : ZMod (2 ^ (a + 2))) * (2 * K) = 2 * K := by
      rcases hA with ⟨j, rfl⟩
      push_cast
      calc
        ((2 : ZMod (2 ^ (a + 2))) * (j : ZMod (2 ^ (a + 2))) + 1) * (2 * K) =
            (j : ZMod (2 ^ (a + 2))) * (4 * K) + 2 * K := by ring
        _ = 2 * K := by rw [hfourK, mul_zero, zero_add]
    have hlift (y : ZMod (2 ^ (a + 1))) :
        ((1 + 2 * (y + H).val : ℕ) : ZMod (2 ^ (a + 2))) =
          ((1 + 2 * y.val : ℕ) : ZMod (2 ^ (a + 2))) + K := by
      have hsmall :
          ((y.val + 2 ^ (a - 1) : ℕ) : ZMod (2 ^ (a + 1))) = y + H := by
        dsimp [H]
        rw [Nat.cast_add, y.natCast_zmod_val]
      have hsmall' :
          (((y + H).val : ℕ) : ZMod (2 ^ (a + 1))) = y + H :=
        (y + H).natCast_zmod_val
      have hdiv :
          (2 ^ (a + 1) : ℤ) ∣
            ((y + H).val : ℤ) - ((y.val : ℤ) + 2 ^ (a - 1)) := by
        apply (ZMod.intCast_eq_intCast_iff_dvd_sub
          ((y.val : ℤ) + 2 ^ (a - 1)) ((y + H).val : ℤ) (2 ^ (a + 1))).mp
        exact_mod_cast hsmall.trans hsmall'.symm
      have hhalfNat : 2 * 2 ^ (a - 1) = 2 ^ a := by
        calc
          2 * 2 ^ (a - 1) = 2 ^ (a - 1) * 2 := by rw [mul_comm]
          _ = 2 ^ ((a - 1) + 1) := by rw [pow_succ]
          _ = 2 ^ a := by congr 1; omega
      have hK : K = ((2 * 2 ^ (a - 1) : ℕ) : ZMod (2 ^ (a + 2))) := by
        dsimp [K]
        rw [hhalfNat]
      rw [hK]
      have heqBig :
          (((1 + 2 * (y + H).val : ℕ) : ℤ) : ZMod (2 ^ (a + 2))) =
            (((1 + 2 * y.val + 2 * 2 ^ (a - 1) : ℕ) : ℤ) :
              ZMod (2 ^ (a + 2))) := by
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
        rcases hdiv with ⟨d, hd⟩
        use -d
        have hpow : (2 ^ (a + 2) : ℤ) = 2 * (2 ^ (a + 1) : ℤ) := by
          norm_num [pow_add, pow_two]
          ring
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
          Nat.cast_pow] at ⊢
        rw [hpow]
        linear_combination -2 * hd
      exact_mod_cast heqBig
    have hphase (y : ZMod (2 ^ (a + 1))) :
        ZMod.stdAddChar
            ((A : ZMod (2 ^ (a + 2))) *
              ((1 + 2 * (y + H).val : ℕ) : ZMod (2 ^ (a + 2))) ^ 2) =
          -ZMod.stdAddChar
            ((A : ZMod (2 ^ (a + 2))) *
              ((1 + 2 * y.val : ℕ) : ZMod (2 ^ (a + 2))) ^ 2) := by
      let X : ZMod (2 ^ (a + 2)) :=
        ((1 + 2 * y.val : ℕ) : ZMod (2 ^ (a + 2)))
      have htwoXK : 2 * X * K = 2 * K := by
        dsimp [X]
        push_cast
        calc
          2 * (1 + 2 * (y.val : ZMod (2 ^ (a + 2)))) * K =
              2 * K + (y.val : ZMod (2 ^ (a + 2))) * (4 * K) := by ring
          _ = 2 * K := by rw [hfourK, mul_zero, add_zero]
      have harg : (A : ZMod (2 ^ (a + 2))) * (X + K) ^ 2 =
          (A : ZMod (2 ^ (a + 2))) * X ^ 2 + 2 * K := by
        calc
          _ = (A : ZMod (2 ^ (a + 2))) * X ^ 2 +
              A * (2 * X * K) + A * K ^ 2 := by ring
          _ = _ := by rw [htwoXK, hAK, hKK, mul_zero, add_zero]
      have htwoKNat : 2 * 2 ^ a = 2 ^ (a + 1) := by
        simp only [pow_add, pow_one]
        ring
      have htwoK : 2 * K = ((2 ^ (a + 1) : ℕ) : ZMod (2 ^ (a + 2))) := by
        dsimp [K]
        calc
          (2 : ZMod (2 ^ (a + 2))) * ((2 ^ a : ℕ) : ZMod (2 ^ (a + 2))) =
              (((2 : ℕ) * 2 ^ a : ℕ) : ZMod (2 ^ (a + 2))) := by norm_num
          _ = _ := by rw [htwoKNat]
      have hcharTwoK : ZMod.stdAddChar (2 * K) = (-1 : ℂ) := by
        rw [htwoK]
        exact stdAddChar_twoPower_half (a + 2) (by omega)
      rw [hlift]
      change ZMod.stdAddChar ((A : ZMod (2 ^ (a + 2))) * (X + K) ^ 2) = _
      rw [harg, AddChar.map_add_eq_mul, hcharTwoK]
      dsimp [X]
      ring
    have hshift :
        (∑ y : ZMod (2 ^ (a + 1)),
          ZMod.stdAddChar
            ((A : ZMod (2 ^ (a + 2))) *
              ((1 + 2 * y.val : ℕ) : ZMod (2 ^ (a + 2))) ^ 2)) =
        -(∑ y : ZMod (2 ^ (a + 1)),
          ZMod.stdAddChar
            ((A : ZMod (2 ^ (a + 2))) *
              ((1 + 2 * y.val : ℕ) : ZMod (2 ^ (a + 2))) ^ 2)) := by
      calc
        _ = ∑ y : ZMod (2 ^ (a + 1)),
            ZMod.stdAddChar
              ((A : ZMod (2 ^ (a + 2))) *
                ((1 + 2 * (y + H).val : ℕ) : ZMod (2 ^ (a + 2))) ^ 2) := by
          exact (Fintype.sum_bijective (fun y : ZMod (2 ^ (a + 1)) ↦ y + H)
            (AddGroup.addRight_bijective H) _ _ (fun _ ↦ rfl)).symm
        _ = _ := by simp_rw [hphase, Finset.sum_neg_distrib]
    have htwoSum :
        2 * (∑ y : ZMod (2 ^ (a + 1)),
          ZMod.stdAddChar
            ((A : ZMod (2 ^ (a + 2))) *
              ((1 + 2 * y.val : ℕ) : ZMod (2 ^ (a + 2))) ^ 2)) = 0 := by
      linear_combination hshift
    exact (mul_eq_zero.mp htwoSum).resolve_left (by norm_num)
  rw [hoddSum, add_zero]

end TranslationalTilings
