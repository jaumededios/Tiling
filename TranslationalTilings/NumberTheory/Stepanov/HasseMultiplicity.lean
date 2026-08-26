import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.SimpleModule.Basic
/-!
Hasse-derivative multiplicity estimates and the linear-algebra construction of
the additive Stepanov auxiliary polynomial over a prime field.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators

namespace TranslationalTilings.Stepanov

open Polynomial

/-- `P` and its first `R - 1` Hasse derivatives vanish at `a`. -/
def VanishesToOrderAtLeast {K : Type*} [CommRing K]
    (P : Polynomial K) (a : K) (R : ℕ) : Prop :=
  ∀ r < R, (P.hasseDeriv r).eval a = 0

/-- For a nonzero polynomial, Hasse vanishing through order `R - 1` is equivalent to root
multiplicity at least `R`. -/
theorem vanishesToOrderAtLeast_iff_rootMultiplicity
    {K : Type*} [Field K] {P : Polynomial K}
    (hP : P ≠ 0) (a : K) (R : ℕ) :
    VanishesToOrderAtLeast P a R ↔ R ≤ P.rootMultiplicity a := by
  rw [Polynomial.rootMultiplicity_eq_rootMultiplicity]
  change VanishesToOrderAtLeast P a R ↔
    R ≤ (Polynomial.taylor a P).rootMultiplicity 0
  rw [Polynomial.le_rootMultiplicity_iff ((Polynomial.taylor_eq_zero a P).not.mpr hP)]
  simpa only [VanishesToOrderAtLeast, Polynomial.taylor_coeff, map_zero, sub_zero]
    using (Polynomial.X_pow_dvd_iff (f := Polynomial.taylor a P) (n := R)).symm

/-- Distinct points at which a nonzero polynomial vanishes to order `R` contribute at least
`R` each to its degree. -/
theorem card_mul_le_natDegree_of_vanishes
    {K : Type*} [Field K] {P : Polynomial K} (hP : P ≠ 0)
    (A : Finset K) {R : ℕ}
    (hvanish : ∀ a ∈ A, VanishesToOrderAtLeast P a R) :
    A.card * R ≤ P.natDegree := by
  classical
  have hdiv : (∏ a ∈ A, (Polynomial.X - Polynomial.C a) ^ R) ∣ P := by
    refine Finset.prod_dvd_of_coprime (s := fun a : K => (X - C a) ^ R) ?_ ?_
    · intro a ha b hb hab
      exact (Polynomial.pairwise_coprime_X_sub_C Function.injective_id hab).pow
    · intro a ha
      exact (Polynomial.le_rootMultiplicity_iff hP).mp
        ((vanishesToOrderAtLeast_iff_rootMultiplicity hP a R).mp (hvanish a ha))
  have hdegree := Polynomial.natDegree_le_of_dvd hdiv hP
  have hprod : (∏ a ∈ A, (Polynomial.X - Polynomial.C a) ^ R).natDegree =
      A.card * R := by
    rw [Polynomial.natDegree_prod_of_monic A
      (fun a : K => (Polynomial.X - Polynomial.C a) ^ R)]
    · simp [Polynomial.natDegree_pow]
    · exact fun a _ => (Polynomial.monic_X_sub_C a).pow R
  rwa [hprod] at hdegree

private theorem prime_dvd_choose_pow_mul_of_pos_of_lt
    {p : ℕ} [Fact p.Prime] (m i l : ℕ) (hl0 : 0 < l) (hl : l < p ^ m) :
    p ∣ (p ^ m * i).choose l := by
  induction m generalizing l with
  | zero =>
      exact False.elim ((Nat.ne_of_gt hl0) (Nat.lt_one_iff.mp (by simpa using hl)))
  | succ m ih =>
      have hp0 : 0 < p := (Fact.out : p.Prime).pos
      have hmodN : p ^ (m + 1) * i % p = 0 := by
        simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      have hdivN : p ^ (m + 1) * i / p = p ^ m * i := by
        simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm, hp0]
      have hLucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := p ^ (m + 1) * i) (k := l) (p := p)
      rw [hmodN, hdivN] at hLucas
      by_cases hpl : p ∣ l
      · obtain ⟨l', rfl⟩ := hpl
        have hl'0 : 0 < l' := by
          by_contra h
          have : l' = 0 := Nat.eq_zero_of_not_pos h
          simp [this] at hl0
        have hl' : l' < p ^ m := by
          rw [pow_succ] at hl
          exact (Nat.mul_lt_mul_left hp0).mp (by simpa [Nat.mul_comm] using hl)
        have hdiv := ih l' hl'0 hl'
        have hquot : p * l' / p = l' := Nat.mul_div_cancel_left l' hp0
        have hR :
            p ∣ Nat.choose 0 (p * l' % p) * (p ^ m * i).choose (p * l' / p) := by
          simpa [hquot] using hdiv
        exact Nat.modEq_zero_iff_dvd.mp
          (hLucas.trans (Nat.modEq_zero_iff_dvd.mpr hR))
      · have hlmod : 0 < l % p :=
          Nat.pos_of_ne_zero ((Nat.dvd_iff_mod_eq_zero).not.mp hpl)
        have hz : Nat.choose 0 (l % p) = 0 := Nat.choose_eq_zero_of_lt hlmod
        exact Nat.modEq_zero_iff_dvd.mp (by simpa [hz] using hLucas)

private theorem hasseDeriv_X_pow_pow_mul_eq_zero
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (m i l : ℕ) (hl0 : 0 < l) (hl : l < p ^ m) :
    (Polynomial.X ^ (p ^ m * i) : Polynomial K).hasseDeriv l = 0 := by
  rw [← Polynomial.monomial_one_right_eq_X_pow, Polynomial.hasseDeriv_monomial]
  have hd : p ∣ (p ^ m * i).choose l :=
    prime_dvd_choose_pow_mul_of_pos_of_lt m i l hl0 hl
  have hcast : (↑((p ^ m * i).choose l) : K) = 0 :=
    (CharP.cast_eq_zero_iff K p _).mpr hd
  rw [hcast, zero_mul, Polynomial.monomial_zero_right]

private theorem hasseDeriv_mul_X_pow_pow_mul
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (a : Polynomial K) (m i r : ℕ) (hr : r < p ^ m) :
    (a * Polynomial.X ^ (p ^ m * i)).hasseDeriv r =
      a.hasseDeriv r * Polynomial.X ^ (p ^ m * i) := by
  rw [Polynomial.hasseDeriv_mul]
  rw [Finset.sum_eq_single (r, 0)]
  · simp
  · rintro ⟨k, l⟩ hmem hne
    have hsum : k + l = r := Finset.mem_antidiagonal.mp hmem
    have hl0 : 0 < l := by
      by_contra hl
      have hlz : l = 0 := Nat.eq_zero_of_not_pos hl
      subst hlz
      simp_all
    have hllt : l < p ^ m := by omega
    rw [hasseDeriv_X_pow_pow_mul_eq_zero m i l hl0 hllt, mul_zero]
  · simp

/-- Evaluating a Hasse derivative of `P(X^(p^m))` below the Frobenius scale agrees with the
corresponding derivative of `P` at `x^(p^m)`. -/
theorem hasseDeriv_eval_frobenius
    {K : Type*} [Field K] {p : ℕ} [CharP K p]
    (Q : Polynomial (Polynomial K)) {m r : ℕ} (hr : r < p ^ m) :
    (Q.eval (Polynomial.X ^ (p ^ m))).hasseDeriv r =
      (Q.sum fun i a ↦
        Polynomial.C (a.hasseDeriv r) * Polynomial.X ^ i).eval
          (Polynomial.X ^ (p ^ m)) := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · let _ : Fact p.Prime := ⟨hp⟩
    induction Q using Polynomial.induction_on' with
    | add P Q hP hQ =>
        rw [Polynomial.eval_add, map_add, hP, Polynomial.sum_add_index P Q,
          Polynomial.eval_add, ← hQ]
        · intro i
          simp
        · intro i a b
          simp [map_add, add_mul]
    | monomial i a =>
        rw [Polynomial.sum_monomial_index]
        · simp only [Polynomial.eval_monomial, Polynomial.eval_mul,
            Polynomial.eval_C, Polynomial.eval_X_pow]
          simpa [← pow_mul] using hasseDeriv_mul_X_pow_pow_mul a m i r hr
        · simp
  · rcases m with _ | m
    · have hr0 : r = 0 := by simpa using hr
      subst r
      simp only [pow_zero, Polynomial.hasseDeriv_zero',
        Polynomial.C_mul_X_pow_eq_monomial, Polynomial.sum_monomial_eq]
    · simp at hr

/-- Numerical parameters satisfying the dimension and degree inequalities required by the
additive Stepanov construction. -/
structure AdditiveStepanovParameters (p d n : ℕ) where
  /-- The Frobenius-block exponent used in the auxiliary-polynomial construction. -/
  u : ℕ
  /-- The degree bound for each auxiliary coefficient polynomial. -/
  S : ℕ
  /-- The number of coefficient columns in the auxiliary-polynomial construction. -/
  K : ℕ
  /-- The Hasse-multiplicity threshold imposed on the auxiliary polynomial. -/
  R : ℕ
  u_eq : u = n / 2
  S_eq : S = p ^ (n - 2)
  K_eq : K = p ^ (u - 2) / (2 * d)
  K_pos : 0 < K
  two_mul_d_le_K : 2 * d ≤ K
  R_eq : R = p * K
  R_lt_frobenius : R < p ^ u
  dimension_ok :
    R * (S + d * (p - 1) * p ^ (u - 1) + K) <
      p * S * (K + 1)
  norm_degree_ok :
    p * S + d * p ^ u * (p - 1) < p ^ n

/-- Under `2 ≤ d < p` and the stated size hypothesis on `n`, constructs admissible Stepanov
parameters with positive coefficient range. -/
theorem exists_additive_stepanov_parameters
    (p d : ℕ) (hp : p.Prime) (hd : 2 ≤ d) (hdp : d < p) :
    ∃ N, ∀ n ≥ N, Nonempty (AdditiveStepanovParameters p d n) := by
  let M := 4 * d + 2
  refine ⟨2 * M, ?_⟩
  intro n hn
  let u := n / 2
  let S := p ^ (n - 2)
  let A := p ^ (u - 2)
  let c := 2 * d
  let K := A / c
  let R := p * K
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 2 ≤ p := hp.two_le
  have hp3 : 3 ≤ p := by omega
  have hc : 0 < c := by dsimp [c]; omega
  have huM : M ≤ u := by
    dsimp [u]
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    simpa [Nat.mul_comm] using hn
  have hu2 : 2 ≤ u := by dsimp [M] at huM; omega
  have hn2 : 2 ≤ n := by
    have hdouble : 2 * u ≤ n := by
      dsimp [u]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self n 2
    omega
  have hexp : 4 * d ≤ u - 2 := by
    dsimp [M] at huM
    omega
  have hfour : 4 * d * d ≤ 2 ^ (4 * d) := by
    have h := Nat.two_mul_sq_add_one_le_two_pow_two_mul (2 * d)
    rw [show 2 * (2 * d) = 4 * d by ring] at h
    calc
      4 * d * d ≤ 2 * (2 * d) ^ 2 + 1 := by nlinarith
      _ ≤ 2 ^ (4 * d) := h
  have htwoexp : 2 ^ (4 * d) ≤ 2 ^ (u - 2) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
  have hbaseexp : 2 ^ (u - 2) ≤ p ^ (u - 2) :=
    Nat.pow_le_pow_left hp2 (u - 2)
  have hA : 4 * d * d ≤ A := by
    dsimp [A]
    exact hfour.trans (htwoexp.trans hbaseexp)
  have hAc : K * c ≤ A := by
    dsimp [K]
    simpa [Nat.mul_comm] using Nat.mul_div_le A c
  have hKlarge : c ≤ K := by
    apply (Nat.le_div_iff_mul_le hc).2
    dsimp [c]
    nlinarith
  have hKpos : 0 < K := lt_of_lt_of_le hc hKlarge
  have hKleA : K ≤ A := by
    dsimp [K]
    exact Nat.div_le_self A c
  have hApos : 0 < A := by dsimp [A]; positivity
  have hpow_pred : p * A = p ^ (u - 1) := by
    dsimp [A]
    rw [show u - 1 = (u - 2) + 1 by omega, pow_succ]
    ac_rfl
  have hRlt : R < p ^ u := by
    have hle : p * K ≤ p * A := Nat.mul_le_mul_left p hKleA
    have hlt : p ^ (u - 1) < p ^ u := Nat.pow_lt_pow_right hp1 (by omega)
    dsimp [R]
    exact hle.trans_lt (hpow_pred.trans_lt hlt)
  have hSbound : p ^ (2 * u - 2) ≤ S := by
    dsimp [S]
    apply Nat.pow_le_pow_right hp0
    have hdouble : 2 * u ≤ n := by
      dsimp [u]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self n 2
    omega
  have hpow_middle : A * p * p ^ (u - 1) = p ^ (2 * u - 2) := by
    dsimp [A]
    calc
      p ^ (u - 2) * p * p ^ (u - 1) =
          p ^ ((u - 2) + 1 + (u - 1)) := by simp [pow_add]
      _ = p ^ (2 * u - 2) := by congr 1; omega
  let T₁ := K * d * (p - 1) * p ^ (u - 1)
  let T₂ := K * K
  have hT₁ : 2 * T₁ < p ^ (2 * u - 2) := by
    calc
      2 * T₁ = (K * c) * (p - 1) * p ^ (u - 1) := by
        dsimp [T₁, c]
        ring
      _ ≤ A * (p - 1) * p ^ (u - 1) := by
        gcongr
      _ < A * p * p ^ (u - 1) := by
        gcongr
        omega
      _ = p ^ (2 * u - 2) := hpow_middle
  have hpow_square : A * A * p * p = p ^ (2 * u - 2) := by
    dsimp [A]
    calc
      p ^ (u - 2) * p ^ (u - 2) * p * p =
          p ^ ((u - 2) + (u - 2) + 1 + 1) := by simp [pow_add]
      _ = p ^ (2 * u - 2) := by congr 1; omega
  have hT₂ : 2 * T₂ < p ^ (2 * u - 2) := by
    have hsq : K * K ≤ A * A := Nat.mul_le_mul hKleA hKleA
    calc
      2 * T₂ = 2 * (K * K) := by rfl
      _ ≤ 2 * (A * A) := Nat.mul_le_mul_left 2 hsq
      _ < (A * A) * (p * p) := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.mul_lt_mul_of_pos_left (show 2 < p * p by nlinarith)
            (Nat.mul_pos hApos hApos)
      _ = p ^ (2 * u - 2) := by
        rw [← hpow_square]
        ring
  have hsmall : T₁ + T₂ < S := by
    have h1 := hT₁.trans_le hSbound
    have h2 := hT₂.trans_le hSbound
    omega
  have hdimension :
      R * (S + d * (p - 1) * p ^ (u - 1) + K) <
        p * S * (K + 1) := by
    dsimp [T₁, T₂] at hsmall
    dsimp [R]
    calc
      p * K * (S + d * (p - 1) * p ^ (u - 1) + K) =
          p * K * S + p * (K * d * (p - 1) * p ^ (u - 1) + K * K) := by ring
      _ < p * K * S + p * S :=
        Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hsmall hp0) _
      _ = p * S * (K + 1) := by ring
  have hdA : d < A := by nlinarith
  have hdu : d < p ^ (u - 1) := by
    exact hdA.trans_le (by
      rw [← hpow_pred]
      exact Nat.le_mul_of_pos_left A hp0)
  have hdupow : d * p ^ u < p ^ (n - 1) := by
    calc
      d * p ^ u < p ^ (u - 1) * p ^ u :=
        Nat.mul_lt_mul_of_pos_right hdu (by positivity)
      _ = p ^ (2 * u - 1) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ p ^ (n - 1) := by
        apply Nat.pow_le_pow_right hp0
        have hdouble : 2 * u ≤ n := by
          dsimp [u]
          simpa [Nat.mul_comm] using Nat.div_mul_le_self n 2
        omega
  have hnorm : p * S + d * p ^ u * (p - 1) < p ^ n := by
    have hmul := Nat.mul_lt_mul_of_pos_right hdupow (by omega : 0 < p - 1)
    have hpS : p * S = p ^ (n - 1) := by
      dsimp [S]
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
      ac_rfl
    have hpn : p ^ n = p ^ (n - 1) * p := by
      calc
        p ^ n = p ^ ((n - 1) + 1) := by congr 1; omega
        _ = p ^ (n - 1) * p := by rw [pow_succ]
    rw [hpS]
    calc
      p ^ (n - 1) + d * p ^ u * (p - 1) <
          p ^ (n - 1) + p ^ (n - 1) * (p - 1) := Nat.add_lt_add_left hmul _
      _ = p ^ (n - 1) * p := by
        nth_rewrite 1 [← mul_one (p ^ (n - 1))]
        rw [← mul_add]
        congr 1
        omega
      _ = p ^ n := hpn.symm
  exact ⟨⟨u, S, K, R, rfl, rfl, rfl, hKpos, hKlarge,
    rfl, hRlt, hdimension, hnorm⟩⟩

/-- The coefficient-degree cutoff `S` in an admissible parameter package is positive. -/
theorem AdditiveStepanovParameters.S_pos
    {p d n : ℕ} (par : AdditiveStepanovParameters p d n) :
    0 < par.S := by
  by_contra hS
  have hS0 : par.S = 0 := Nat.eq_zero_of_not_pos hS
  have hdim := par.dimension_ok
  simp [hS0] at hdim

/-- Admissible parameters force the extension exponent `n` to be positive. -/
theorem AdditiveStepanovParameters.n_pos
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hu : par.u = 0 := by simpa [hn0] using par.u_eq
  have hR : par.R < 1 := by simpa [hu] using par.R_lt_frobenius
  have hReq := par.R_eq
  have hK := par.K_pos
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hprod : 0 < p * par.K := Nat.mul_pos hp0 hK
  omega

/-- Polynomial representative of the upper Frobenius-trace block
`f + f^p + ... + f^(p^(n-u-1))`. -/
noncomputable def upperTracePolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (n u : ℕ) : Polynomial (ZMod p) :=
  ∑ t ∈ Finset.Ico u n, f ^ (p ^ t)

private theorem hasseDeriv_pow_char_pow_eq_zero
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (f : Polynomial K) (m l : ℕ) (hl0 : 0 < l) (hl : l < p ^ m) :
    (f ^ (p ^ m)).hasseDeriv l = 0 := by
  induction f using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [add_pow_char_pow, map_add, hP, hQ, add_zero]
  | monomial i a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_pow, ← map_pow, ← pow_mul]
      have hs := hasseDeriv_mul_X_pow_pow_mul
        (Polynomial.C (a ^ (p ^ m))) m i l hl
      rw [Polynomial.hasseDeriv_C l _ hl0, zero_mul] at hs
      simpa [Nat.mul_comm] using hs

private theorem upperTracePolynomial_hasseDeriv_eq_zero
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p))
    (n u l : ℕ) (hl0 : 0 < l) (hl : l < p ^ u) :
    (upperTracePolynomial f n u).hasseDeriv l = 0 := by
  rw [upperTracePolynomial]
  simp_rw [map_sum]
  apply Finset.sum_eq_zero
  intro t ht
  have hut : u ≤ t := (Finset.mem_Ico.mp ht).1
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  exact hasseDeriv_pow_char_pow_eq_zero f t l hl0
    (hl.trans_le (Nat.pow_le_pow_right hp0 hut))

private theorem hasseDeriv_mul_of_right_frozen
    {K : Type*} [Field K] (A B : Polynomial K) (r : ℕ)
    (hB : ∀ l, 0 < l → l ≤ r → B.hasseDeriv l = 0) :
    (A * B).hasseDeriv r = A.hasseDeriv r * B := by
  rw [Polynomial.hasseDeriv_mul]
  rw [Finset.sum_eq_single (r, 0)]
  · simp
  · rintro ⟨k, l⟩ hmem hne
    have hsum : k + l = r := Finset.mem_antidiagonal.mp hmem
    have hl0 : 0 < l := by
      by_contra hl
      have hlz : l = 0 := Nat.eq_zero_of_not_pos hl
      subst hlz
      simp_all
    rw [hB l hl0 (by omega), mul_zero]
  · simp

private theorem upperTracePolynomial_power_hasseDeriv_eq_zero
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p))
    (n u i l : ℕ) (hl0 : 0 < l) (hl : l < p ^ u) :
    (upperTracePolynomial f n u ^ i).hasseDeriv l = 0 := by
  induction i with
  | zero =>
      simpa using Polynomial.hasseDeriv_apply_one (R := ZMod p) l hl0
  | succ i ih =>
      rw [pow_succ]
      rw [hasseDeriv_mul_of_right_frozen]
      · rw [ih, zero_mul]
      · intro q hq0 hql
        exact upperTracePolynomial_hasseDeriv_eq_zero f n u q hq0 (hql.trans_lt hl)

/-- A rectangular family of coefficient polynomials, each of degree strictly below `S`. -/
structure AdditiveAuxiliaryCoefficients {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (k : Type*) [Field k] where
  /-- The family of low-degree coefficient polynomials indexed by residue and column. -/
  coeff : Fin p → Fin (par.K + 1) → Polynomial k
  degree_lt : ∀ i j, (coeff i j).natDegree < par.S

/-- At least one polynomial in the auxiliary coefficient family is nonzero. -/
def AdditiveAuxiliaryCoefficients.Nonzero
    {p d n : ℕ} {par : AdditiveStepanovParameters p d n}
    {k : Type*} [Field k]
    (e : AdditiveAuxiliaryCoefficients par k) : Prop :=
  ∃ i j, e.coeff i j ≠ 0

/-- The Stepanov auxiliary polynomial assembled from coefficient polynomials, powers of the
upper trace block, and `p^n`-spaced monomials. -/
noncomputable def additiveAuxiliaryPolynomial
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p))
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) :
    Polynomial (ZMod p) :=
  ∑ i : Fin p, ∑ j : Fin (par.K + 1),
    e.coeff i j * upperTracePolynomial f n par.u ^ i.1 *
      Polynomial.X ^ (p ^ n * j.1)

/-- Coordinate model for all coefficients of the bounded-degree auxiliary family. -/
abbrev AdditiveCoeffVector {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :=
  Fin p → Fin (par.K + 1) → Fin par.S → ZMod p

/-- Uniform column bound used to record all reduced Hasse-derivative constraints. -/
def additiveConstraintDegree {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n) : ℕ :=
  par.S + d * (p - 1) * p ^ (par.u - 1) + par.K

/-- Finite-dimensional target containing every derivative-order/degree constraint. -/
abbrev AdditiveConstraintTarget {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :=
  Fin par.R → Fin (additiveConstraintDegree par) → ZMod p

/-- Converts one coefficient column in the coordinate vector into a polynomial of degree below
`S`. -/
noncomputable def coeffPolynomial
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) (i : Fin p)
    (j : Fin (par.K + 1)) : Polynomial (ZMod p) :=
  ∑ s : Fin par.S,
    Polynomial.C (v i j s) * Polynomial.X ^ s.1

/-- The coefficient extractor for `coeffPolynomial` recovers the supplied coordinate below `S`
and is zero outside that range. -/
theorem coeffPolynomial_coeff
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) (i : Fin p)
    (j : Fin (par.K + 1)) (s : Fin par.S) :
    (coeffPolynomial v i j).coeff s.1 = v i j s := by
  classical
  rw [coeffPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    have hval : t.1 ≠ s.1 := fun h => hts (Fin.ext h)
    rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, if_neg hval]
  · simp

/-- Every polynomial decoded from a coefficient vector has natural degree strictly below `S`. -/
theorem coeffPolynomial_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) (i : Fin p)
    (j : Fin (par.K + 1)) :
    (coeffPolynomial v i j).natDegree < par.S := by
  classical
  have hS : 0 < par.S := par.S_pos
  rw [coeffPolynomial]
  refine lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le Finset.univ
      (fun s : Fin par.S => Polynomial.C (v i j s) * Polynomial.X ^ s.1) ?_)
    (Nat.pred_lt hS.ne')
  intro s _
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  exact (Polynomial.natDegree_monomial_le (v i j s)).trans
    (Nat.le_pred_of_lt s.isLt)

private theorem coeffPolynomial_add
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v w : AdditiveCoeffVector par) (i : Fin p)
    (j : Fin (par.K + 1)) :
    coeffPolynomial (v + w) i j = coeffPolynomial v i j + coeffPolynomial w i j := by
  classical
  simp only [coeffPolynomial, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private theorem coeffPolynomial_smul
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (c : ZMod p) (v : AdditiveCoeffVector par) (i : Fin p)
    (j : Fin (par.K + 1)) :
    coeffPolynomial (c • v) i j = c • coeffPolynomial v i j := by
  classical
  ext q
  by_cases hq : q < par.S
  · let s : Fin par.S := ⟨q, hq⟩
    simpa [s] using congrArg (Polynomial.coeff · q)
      (show coeffPolynomial (c • v) i j = c • coeffPolynomial v i j by
        rw [← Polynomial.C_mul', coeffPolynomial, coeffPolynomial]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        rw [Finset.mul_sum]
        congr 1
        funext t
        simp [mul_assoc])
  · have hleft := coeffPolynomial_natDegree_lt (c • v) i j
    have hright := coeffPolynomial_natDegree_lt v i j
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hleft (Nat.le_of_not_gt hq))]
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le hright (Nat.le_of_not_gt hq))]

/-- Decodes the full coordinate vector into an auxiliary coefficient family. -/
noncomputable def coeffVectorToCoefficients
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) :
    AdditiveAuxiliaryCoefficients par (ZMod p) where
  coeff := coeffPolynomial v
  degree_lt := coeffPolynomial_natDegree_lt v

/-- Underlying function from coefficient vectors to their Stepanov auxiliary polynomials. -/
noncomputable def coeffVectorToAuxiliaryFun
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (v : AdditiveCoeffVector par) :
    Polynomial (ZMod p) :=
  additiveAuxiliaryPolynomial par f (coeffVectorToCoefficients v)

/-- Decoding and assembling the auxiliary polynomial preserves addition. -/
theorem coeffVectorToAuxiliaryFun_add
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (v w : AdditiveCoeffVector par) :
    coeffVectorToAuxiliaryFun par f (v + w) =
      coeffVectorToAuxiliaryFun par f v +
        coeffVectorToAuxiliaryFun par f w := by
  classical
  simp only [coeffVectorToAuxiliaryFun, additiveAuxiliaryPolynomial,
    coeffVectorToCoefficients, coeffPolynomial_add, add_mul, Finset.sum_add_distrib]

/-- Decoding and assembling the auxiliary polynomial preserves scalar multiplication. -/
theorem coeffVectorToAuxiliaryFun_smul
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (c : ZMod p)
    (v : AdditiveCoeffVector par) :
    coeffVectorToAuxiliaryFun par f (c • v) =
      c • coeffVectorToAuxiliaryFun par f v := by
  classical
  simp only [coeffVectorToAuxiliaryFun, additiveAuxiliaryPolynomial,
    coeffVectorToCoefficients, coeffPolynomial_smul, smul_eq_C_mul,
    Finset.smul_sum, mul_assoc]

/-- Linear map from coefficient coordinates to Stepanov auxiliary polynomials. -/
noncomputable def coeffVectorToAuxiliary
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) :
    AdditiveCoeffVector par →ₗ[ZMod p] Polynomial (ZMod p) where
  toFun := coeffVectorToAuxiliaryFun par f
  map_add' := coeffVectorToAuxiliaryFun_add par f
  map_smul' := coeffVectorToAuxiliaryFun_smul par f

private theorem hasseDeriv_map_eq_map_hasseDeriv
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (g : R →+* S) (P : Polynomial R) (r : ℕ) :
    (P.map g).hasseDeriv r = (P.hasseDeriv r).map g := by
  ext q
  simp [Polynomial.hasseDeriv_coeff]

private theorem coeffVectorToAuxiliary_hasseDeriv
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (v : AdditiveCoeffVector par)
    (r : ℕ) (hr : r < par.R) :
    (((coeffVectorToAuxiliary par f) v).hasseDeriv r) =
      ∑ i : Fin p, ∑ j : Fin (par.K + 1),
        (coeffPolynomial v i j).hasseDeriv r *
          upperTracePolynomial f n par.u ^ i.1 *
            Polynomial.X ^ (p ^ n * j.1) := by
  classical
  have hu : par.u ≤ n := by
    rw [par.u_eq]
    exact Nat.div_le_self n 2
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hrn : r < p ^ n :=
    (hr.trans par.R_lt_frobenius).trans_le (Nat.pow_le_pow_right hp0 hu)
  change (Polynomial.hasseDeriv r)
      (∑ i : Fin p, ∑ j : Fin (par.K + 1),
        coeffPolynomial v i j * upperTracePolynomial f n par.u ^ i.1 *
          Polynomial.X ^ (p ^ n * j.1)) = _
  simp_rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hasseDeriv_mul_X_pow_pow_mul _ n j.1 r hrn]
  rw [hasseDeriv_mul_of_right_frozen]
  intro q hq0 hqr
  exact upperTracePolynomial_power_hasseDeriv_eq_zero f n par.u i.1 q hq0
    (hqr.trans_lt (hr.trans par.R_lt_frobenius))

/-- Polynomial representative of the lower trace block with `u` Frobenius terms. -/
noncomputable def lowerTracePolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) : Polynomial (ZMod p) :=
  ∑ t ∈ Finset.range u, f ^ (p ^ t)

/-- Bivariate reduction of a Hasse derivative of the auxiliary polynomial modulo the graph
relation `Y = lowerTracePolynomial f u`. -/
noncomputable def reducedHassePolynomial
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ)
    (v : AdditiveCoeffVector par) : Polynomial (ZMod p) :=
  ∑ i : Fin p, ∑ j : Fin (par.K + 1),
    (coeffPolynomial v i j).hasseDeriv r *
      (Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1 *
        Polynomial.X ^ j.1

/-- Reduced Hasse polynomials are additive in the coefficient vector. -/
theorem reducedHassePolynomial_add
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ)
    (v w : AdditiveCoeffVector par) :
    reducedHassePolynomial par f b r (v + w) =
      reducedHassePolynomial par f b r v +
        reducedHassePolynomial par f b r w := by
  classical
  simp only [reducedHassePolynomial, coeffPolynomial_add, map_add,
    add_mul, Finset.sum_add_distrib]

/-- Reduced Hasse polynomials commute with scalar multiplication of coefficient vectors. -/
theorem reducedHassePolynomial_smul
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ)
    (c : ZMod p) (v : AdditiveCoeffVector par) :
    reducedHassePolynomial par f b r (c • v) =
      c • reducedHassePolynomial par f b r v := by
  classical
  simp only [reducedHassePolynomial, coeffPolynomial_smul, map_smul,
    smul_mul_assoc, Finset.smul_sum]

/-- Linear map sending coefficient data to its derivative-`r` reduced Hasse polynomial. -/
noncomputable def reducedHasseLinearMap
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ) :
    AdditiveCoeffVector par →ₗ[ZMod p] Polynomial (ZMod p) where
  toFun := reducedHassePolynomial par f b r
  map_add' := reducedHassePolynomial_add par f b r
  map_smul' := reducedHassePolynomial_smul par f b r

/-- Records every coefficient of every reduced Hasse polynomial below the prescribed bounds. -/
noncomputable def additiveConstraintFun
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p)
    (v : AdditiveCoeffVector par) : AdditiveConstraintTarget par :=
  fun r q ↦ (reducedHassePolynomial par f b r.1 v).coeff q.1

/-- The complete constraint table preserves addition. -/
theorem additiveConstraintFun_add
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p)
    (v w : AdditiveCoeffVector par) :
    additiveConstraintFun par f b (v + w) =
      additiveConstraintFun par f b v +
        additiveConstraintFun par f b w := by
  funext r q
  simp [additiveConstraintFun, reducedHassePolynomial_add]

/-- The complete constraint table preserves scalar multiplication. -/
theorem additiveConstraintFun_smul
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p)
    (c : ZMod p) (v : AdditiveCoeffVector par) :
    additiveConstraintFun par f b (c • v) =
      c • additiveConstraintFun par f b v := by
  funext r q
  simp [additiveConstraintFun, reducedHassePolynomial_smul]

/-- Linear constraint map whose kernel consists of coefficient vectors satisfying all required
Hasse-vanishing equations. -/
noncomputable def additiveConstraint
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) :
    AdditiveCoeffVector par →ₗ[ZMod p] AdditiveConstraintTarget par where
  toFun := additiveConstraintFun par f b
  map_add' := additiveConstraintFun_add par f b
  map_smul' := additiveConstraintFun_smul par f b

/-- Bounds the degree of the lower trace block by `d * p^(u-1)`. -/
theorem lowerTracePolynomial_natDegree_le
    {p : ℕ} [Fact p.Prime] {d : ℕ}
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (u : ℕ) :
    (lowerTracePolynomial f u).natDegree ≤ d * p ^ (u - 1) := by
  classical
  by_cases hu : u = 0
  · simp [lowerTracePolynomial, hu]
  rw [lowerTracePolynomial]
  refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range u)
    (fun t : ℕ => f ^ (p ^ t)) ?_
  intro t htmem
  rw [Polynomial.natDegree_pow, hdegree]
  have htlt : t < u := Finset.mem_range.mp htmem
  have ht : t ≤ u - 1 := by omega
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left d (Nat.pow_le_pow_right hp0 ht)

/-- On a point satisfying the trace equation, the upper trace block evaluates to the negative of
the lower trace block. -/
theorem upperTracePolynomial_eval_eq_of_trace_eq
    {p : ℕ} [Fact p.Prime] {n u : ℕ}
    (f : Polynomial (ZMod p)) (hn : n ≠ 0) (hu : u ≤ n)
    (b : ZMod p) (x : GaloisField p n)
    (hx : Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b) :
    (upperTracePolynomial f n u).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x =
      (Polynomial.C b - lowerTracePolynomial f u).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x := by
  let y : GaloisField p n :=
    f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x
  have htrace := FiniteField.algebraMap_trace_eq_sum_pow
    (ZMod p) (GaloisField p n) y
  rw [GaloisField.finrank p hn, Nat.card_zmod, hx] at htrace
  have hsplit := Finset.sum_range_add_sum_Ico (fun t : ℕ => y ^ (p ^ t)) hu
  calc
    (upperTracePolynomial f n u).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x =
        ∑ t ∈ Finset.Ico u n, y ^ (p ^ t) := by
      rw [upperTracePolynomial, Polynomial.eval₂_finsetSum]
      simp [y]
    _ = algebraMap (ZMod p) (GaloisField p n) b -
        ∑ t ∈ Finset.range u, y ^ (p ^ t) := by
      apply eq_sub_iff_add_eq.mpr
      calc
        (∑ t ∈ Finset.Ico u n, y ^ (p ^ t)) +
            ∑ t ∈ Finset.range u, y ^ (p ^ t) =
            (∑ t ∈ Finset.range u, y ^ (p ^ t)) +
              ∑ t ∈ Finset.Ico u n, y ^ (p ^ t) := add_comm _ _
        _ = ∑ t ∈ Finset.range n, y ^ (p ^ t) := hsplit
        _ = algebraMap (ZMod p) (GaloisField p n) b := htrace.symm
    _ = (Polynomial.C b - lowerTracePolynomial f u).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x := by
      rw [lowerTracePolynomial, Polynomial.eval₂_sub,
        Polynomial.eval₂_C, Polynomial.eval₂_finsetSum]
      simp [y]

/-- Evaluating the reduced bivariate polynomial on the lower trace graph recovers the corresponding
Hasse derivative of the auxiliary polynomial. -/
theorem reducedHassePolynomial_eval₂_eq_hasseDeriv_eval
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p)
    (v : AdditiveCoeffVector par) (r : ℕ) (hr : r < par.R)
    (x : GaloisField p n)
    (hx : Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b) :
    (reducedHassePolynomial par f b r v).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x =
      Polynomial.eval x
        ((((coeffVectorToAuxiliary par f) v).map
          (algebraMap (ZMod p) (GaloisField p n))).hasseDeriv r) := by
  classical
  have hn : n ≠ 0 := par.n_pos.ne'
  have hu : par.u ≤ n := by
    rw [par.u_eq]
    exact Nat.div_le_self n 2
  have hupper := upperTracePolynomial_eval_eq_of_trace_eq f hn hu b x hx
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hxpow := FiniteField.pow_card x
  rw [Fintype.card_eq_nat_card, GaloisField.card p n hn] at hxpow
  rw [hasseDeriv_map_eq_map_hasseDeriv,
    Polynomial.eval_map,
    coeffVectorToAuxiliary_hasseDeriv par f v r hr,
    reducedHassePolynomial]
  simp_rw [Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rw [hupper, pow_mul, hxpow]

/-- Every reduced Hasse polynomial lies below the common constraint-degree cutoff. -/
theorem reducedHassePolynomial_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (b : ZMod p) (r : ℕ) (v : AdditiveCoeffVector par) :
    (reducedHassePolynomial par f b r v).natDegree <
      additiveConstraintDegree par := by
  classical
  let L := d * p ^ (par.u - 1)
  let D := additiveConstraintDegree par
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hS : 0 < par.S := par.S_pos
  have hD : 0 < D := by
    dsimp [D, additiveConstraintDegree]
    omega
  have hbase : (Polynomial.C b - lowerTracePolynomial f par.u).natDegree ≤ L := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [max_le_iff]
    exact ⟨by simp [L], lowerTracePolynomial_natDegree_le f hdegree par.u⟩
  change (reducedHassePolynomial par f b r v).natDegree < D
  rw [reducedHassePolynomial]
  refine lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le Finset.univ
      (fun i : Fin p => ∑ j : Fin (par.K + 1),
        (coeffPolynomial v i j).hasseDeriv r *
          (Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1 *
            Polynomial.X ^ j.1) ?_)
    (Nat.pred_lt hD.ne')
  intro i _
  refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
    (fun j : Fin (par.K + 1) =>
      (coeffPolynomial v i j).hasseDeriv r *
        (Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1 *
          Polynomial.X ^ j.1) ?_
  intro j _
  apply Nat.le_pred_of_lt
  have hc : ((coeffPolynomial v i j).hasseDeriv r).natDegree < par.S :=
    ((Polynomial.natDegree_hasseDeriv_le _ _).trans (Nat.sub_le _ _)).trans_lt
      (coeffPolynomial_natDegree_lt v i j)
  have hi : i.1 ≤ p - 1 := by omega
  have hj : j.1 ≤ par.K := by omega
  have hpow :
      ((Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1).natDegree ≤
        (p - 1) * L := by
    rw [Polynomial.natDegree_pow]
    exact (Nat.mul_le_mul_left i.1 hbase).trans
      (Nat.mul_le_mul_right L hi)
  have hterm' :
      (((coeffPolynomial v i j).hasseDeriv r *
          (Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1) *
          Polynomial.X ^ j.1).natDegree ≤
        ((coeffPolynomial v i j).hasseDeriv r).natDegree +
          ((Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1).natDegree + j.1 := by
    calc
      (((coeffPolynomial v i j).hasseDeriv r *
            (Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1) *
            Polynomial.X ^ j.1).natDegree
          ≤ (((coeffPolynomial v i j).hasseDeriv r *
              (Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1)).natDegree +
              (Polynomial.X ^ j.1 : Polynomial (ZMod p)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (((coeffPolynomial v i j).hasseDeriv r).natDegree +
              ((Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1).natDegree) +
              j.1 := Nat.add_le_add Polynomial.natDegree_mul_le (by simp)
  dsimp [L] at hpow
  dsimp [D, additiveConstraintDegree, L]
  calc
    (((coeffPolynomial v i j).hasseDeriv r *
          (Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1) *
          Polynomial.X ^ j.1).natDegree
        ≤ ((coeffPolynomial v i j).hasseDeriv r).natDegree +
            ((Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1).natDegree + j.1 := hterm'
    _ < par.S + (p - 1) * (d * p ^ (par.u - 1)) + par.K := by omega
    _ = par.S + d * (p - 1) * p ^ (par.u - 1) + par.K := by ring

/-- Computes the coefficient-coordinate dimension as `p * (K + 1) * S`. -/
theorem additiveCoeffVector_finrank
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :
    Module.finrank (ZMod p) (AdditiveCoeffVector par) =
      p * par.S * (par.K + 1) := by
  simp [AdditiveCoeffVector, Module.finrank_pi_fintype]
  ac_rfl

/-- Computes the constraint-space dimension as `R * additiveConstraintDegree`. -/
theorem additiveConstraintTarget_finrank
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :
    Module.finrank (ZMod p) (AdditiveConstraintTarget par) =
      par.R * additiveConstraintDegree par := by
  simp [AdditiveConstraintTarget, Module.finrank_pi_fintype]

/-- The parameter dimension inequality gives a nonzero coefficient vector in the kernel of the
constraint map. -/
theorem exists_nonzero_mem_additiveConstraint_ker
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) :
    ∃ v : AdditiveCoeffVector par,
      v ≠ 0 ∧ v ∈ LinearMap.ker (additiveConstraint par f b) := by
  have hdim :
      Module.finrank (ZMod p) (AdditiveConstraintTarget par) <
        Module.finrank (ZMod p) (AdditiveCoeffVector par) := by
    rw [additiveConstraintTarget_finrank, additiveCoeffVector_finrank]
    exact par.dimension_ok
  have hker : LinearMap.ker (additiveConstraint par f b) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, hvker⟩

/-- Kernel membership forces every constrained reduced Hasse polynomial to vanish identically. -/
theorem reducedHassePolynomial_eq_zero_of_mem_ker
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (b : ZMod p) (v : AdditiveCoeffVector par)
    (hv : v ∈ LinearMap.ker (additiveConstraint par f b))
    (r : Fin par.R) :
    reducedHassePolynomial par f b r.1 v = 0 := by
  apply Polynomial.ext
  intro q
  rw [Polynomial.coeff_zero]
  by_cases hq : q < additiveConstraintDegree par
  · let q' : Fin (additiveConstraintDegree par) := ⟨q, hq⟩
    have hzero := LinearMap.mem_ker.mp hv
    have hcoord := congrFun (congrFun hzero r) q'
    simpa [additiveConstraint, additiveConstraintFun, q'] using hcoord
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((reducedHassePolynomial_natDegree_lt par f hdegree b r.1 v).trans_le
        (Nat.le_of_not_gt hq))

/-- A decoded auxiliary coefficient family is nonzero exactly when its coordinate vector is
nonzero. -/
theorem coeffVectorToCoefficients_nonzero_iff
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) :
    (coeffVectorToCoefficients v).Nonzero ↔ v ≠ 0 := by
  constructor
  · rintro ⟨i, j, hij⟩ rfl
    exact hij (by ext q; simp [coeffVectorToCoefficients, coeffPolynomial])
  · intro hv
    by_contra hnonzero
    simp only [AdditiveAuxiliaryCoefficients.Nonzero, not_exists] at hnonzero
    apply hv
    funext i j s
    have hz : (coeffVectorToCoefficients v).coeff i j = 0 :=
      not_ne_iff.mp (hnonzero i j)
    have hs := congrArg (fun P : Polynomial (ZMod p) => P.coeff s.1) hz
    simpa [coeffVectorToCoefficients, coeffPolynomial_coeff] using hs

/-- Constructs a nonzero bounded-degree coefficient family whose auxiliary polynomial has all
required reduced Hasse derivatives equal to zero. -/
theorem exists_additive_stepanov_coefficients
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (b : ZMod p) :
    ∃ e : AdditiveAuxiliaryCoefficients par (ZMod p), e.Nonzero ∧
      ∀ x : GaloisField p n,
        Algebra.trace (ZMod p) (GaloisField p n)
            (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b →
          VanishesToOrderAtLeast
            ((additiveAuxiliaryPolynomial par f e).map
              (algebraMap (ZMod p) (GaloisField p n))) x par.R := by
  obtain ⟨v, hv0, hvker⟩ := exists_nonzero_mem_additiveConstraint_ker par f b
  refine ⟨coeffVectorToCoefficients v,
    (coeffVectorToCoefficients_nonzero_iff v).mpr hv0, ?_⟩
  intro x hx
  change ∀ r < par.R,
    Polynomial.eval x
      (((((coeffVectorToAuxiliary par f) v).map
        (algebraMap (ZMod p) (GaloisField p n))).hasseDeriv r)) = 0
  intro r hr
  let r' : Fin par.R := ⟨r, hr⟩
  have hred := reducedHassePolynomial_eq_zero_of_mem_ker
    par f hdegree b v hvker r'
  have heval := reducedHassePolynomial_eval₂_eq_hasseDeriv_eval
    par f b v r hr x hx
  rw [hred, Polynomial.eval₂_zero] at heval
  exact heval.symm

end TranslationalTilings.Stepanov
