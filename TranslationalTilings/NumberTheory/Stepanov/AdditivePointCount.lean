import TranslationalTilings.NumberTheory.Stepanov.TranslationProduct

/-!
# Additive Stepanov point counts

This module bounds the degree of the additive auxiliary polynomial, converts its prescribed
multiplicities into an upper bound for trace fibres over finite extensions, and balances those
fibres to obtain the square-root-error point-count estimate used by the exponential-sum argument.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings.Stepanov

open Polynomial

/-- The additive auxiliary polynomial has the degree bound dictated by the Stepanov parameters. -/
theorem additiveAuxiliaryPolynomial_natDegree_le
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) :
    (additiveAuxiliaryPolynomial par f e).natDegree ≤
      par.S + d * (p - 1) * p ^ (n - 1) + p ^ n * par.K := by
  classical
  rw [additiveAuxiliaryPolynomial]
  refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
    (fun i : Fin p ↦ ∑ j : Fin (par.K + 1),
      e.coeff i j * upperTracePolynomial f n par.u ^ i.1 *
        X ^ (p ^ n * j.1)) ?_
  intro i hi
  refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
    (fun j : Fin (par.K + 1) ↦
      e.coeff i j * upperTracePolynomial f n par.u ^ i.1 *
        X ^ (p ^ n * j.1)) ?_
  intro j hj
  refine Polynomial.natDegree_mul_le.trans ?_
  refine Nat.add_le_add ?_ ?_
  · refine Polynomial.natDegree_mul_le.trans ?_
    refine Nat.add_le_add (Nat.le_of_lt (e.degree_lt i j)) ?_
    refine Polynomial.natDegree_pow_le.trans ?_
    have hupper : (upperTracePolynomial f n par.u).natDegree ≤
        d * p ^ (n - 1) := by
      rw [upperTracePolynomial]
      refine Polynomial.natDegree_sum_le_of_forall_le (Finset.Ico par.u n)
        (fun t : ℕ ↦ f ^ (p ^ t)) ?_
      intro t ht
      rw [Polynomial.natDegree_pow, hdegree]
      have htn : t ≤ n - 1 := by
        have := (Finset.mem_Ico.mp ht).2
        omega
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left d
        (Nat.pow_le_pow_right (Fact.out : p.Prime).pos htn)
    calc
      i.1 * (upperTracePolynomial f n par.u).natDegree
          ≤ (p - 1) * (d * p ^ (n - 1)) :=
        Nat.mul_le_mul (Nat.le_pred_of_lt i.2) hupper
      _ = d * (p - 1) * p ^ (n - 1) := by ring
  · rw [Polynomial.natDegree_X_pow]
    exact Nat.mul_le_mul_left _ (Nat.le_pred_of_lt j.2)

/-- The number of extension-field elements whose polynomial phase has prescribed trace `b`. -/
noncomputable def tracePhaseFiberCard
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (n : ℕ) (b : ZMod p) : ℕ := by
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  exact (Finset.univ.filter fun x : GaloisField p n ↦
    Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b).card

/-- A one-sided Stepanov upper bound for a trace-phase fibre. -/
theorem stepanov_traceFiberCard_upper
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p) (b : ZMod p) :
    (tracePhaseFiberCard f n b : ℝ) ≤ (p : ℝ) ^ (n - 1) +
      ((par.S + d * (p - 1) * p ^ (n - 1) : ℕ) : ℝ) / par.R := by
  classical
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  obtain ⟨e, he, hvanish⟩ :=
    exists_additive_stepanov_coefficients par f hdegree b
  let P := additiveAuxiliaryPolynomial par f e
  let PE := P.map (algebraMap (ZMod p) (GaloisField p n))
  let A := Finset.univ.filter fun x : GaloisField p n ↦
    Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b
  have hP : P ≠ 0 := additiveAuxiliaryPolynomial_ne_zero
    par f hdegree hpos hsmall e he
  have hPE : PE ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff
      (algebraMap (ZMod p) (GaloisField p n)).injective).2 hP
  have hmul : A.card * par.R ≤ PE.natDegree := by
    apply card_mul_le_natDegree_of_vanishes hPE A
    intro x hx
    exact hvanish x (Finset.mem_filter.mp hx).2
  have hdegreePE : PE.natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      (algebraMap (ZMod p) (GaloisField p n)).injective P
  have hnat : A.card * par.R ≤
      par.S + d * (p - 1) * p ^ (n - 1) + p ^ n * par.K := by
    rw [hdegreePE] at hmul
    exact hmul.trans (additiveAuxiliaryPolynomial_natDegree_le par f hdegree e)
  have hRpos : 0 < par.R := by
    rw [par.R_eq]
    exact Nat.mul_pos (Fact.out : p.Prime).pos par.K_pos
  have hnpos : 0 < n := par.n_pos
  have hreal : ((A.card * par.R : ℕ) : ℝ) ≤
      ((par.S + d * (p - 1) * p ^ (n - 1) + p ^ n * par.K : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hAcard : A.card = tracePhaseFiberCard f n b := by
    rfl
  rw [hAcard] at hreal
  push_cast at hreal
  have hRreal : (0 : ℝ) < par.R := by exact_mod_cast hRpos
  have hpown : (p : ℝ) ^ n * par.K =
      (p : ℝ) ^ (n - 1) * par.R := by
    rw [par.R_eq]
    push_cast
    have hpowreal : (p : ℝ) ^ n = (p : ℝ) ^ (n - 1) * p := by
      calc
        (p : ℝ) ^ n = (p : ℝ) ^ ((n - 1) + 1) := by
          congr 1
          omega
        _ = (p : ℝ) ^ (n - 1) * p := by rw [pow_succ]
    calc
      (p : ℝ) ^ n * par.K =
          ((p : ℝ) ^ (n - 1) * p) * par.K := by
        rw [hpowreal]
      _ = (p : ℝ) ^ (n - 1) * (p * par.K) := by ring
  have hdiff : (tracePhaseFiberCard f n b : ℝ) - (p : ℝ) ^ (n - 1) ≤
      ((par.S + d * (p - 1) * p ^ (n - 1) : ℕ) : ℝ) / par.R := by
    apply (le_div_iff₀ hRreal).2
    rw [hpown] at hreal
    push_cast
    nlinarith
  nlinarith

private theorem sum_tracePhaseFiberCard
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) {n : ℕ} (hn : n ≠ 0) :
    ∑ b : ZMod p, tracePhaseFiberCard f n b = p ^ n := by
  classical
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  rw [← GaloisField.card p n hn]
  change (∑ b : ZMod p, (Finset.univ.filter fun x : GaloisField p n ↦
    Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b).card) =
        Nat.card (GaloisField p n)
  rw [← @Fintype.card_eq_nat_card (GaloisField p n) (by infer_instance)]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  simp

private theorem abs_tracePhaseFiberCard_sub_le_of_upper
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) {n : ℕ} (hn : 0 < n)
    (E : ℝ) (hE : 0 ≤ E)
    (hupper : ∀ b : ZMod p,
      (tracePhaseFiberCard f n b : ℝ) ≤ (p : ℝ) ^ (n - 1) + E)
    (b : ZMod p) :
    |(tracePhaseFiberCard f n b : ℝ) - (p : ℝ) ^ (n - 1)| ≤
      ((p - 1 : ℕ) : ℝ) * E := by
  classical
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  let T : Finset (ZMod p) := Finset.univ.erase b
  have hcardT : T.card = p - 1 := by
    dsimp [T]
    rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ,
      ZMod.card]
  have hrest : ∑ c ∈ T, (tracePhaseFiberCard f n c : ℝ) ≤
      ((p - 1 : ℕ) : ℝ) * ((p : ℝ) ^ (n - 1) + E) := by
    calc
      ∑ c ∈ T, (tracePhaseFiberCard f n c : ℝ) ≤
          ∑ _c ∈ T, ((p : ℝ) ^ (n - 1) + E) := by
        exact Finset.sum_le_sum fun c hc ↦ hupper c
      _ = (T.card : ℝ) * ((p : ℝ) ^ (n - 1) + E) := by
        simp
        ring
      _ = ((p - 1 : ℕ) : ℝ) * ((p : ℝ) ^ (n - 1) + E) := by
        rw [hcardT]
  have hsumReal : ∑ c : ZMod p, (tracePhaseFiberCard f n c : ℝ) =
      (p : ℝ) ^ n := by
    exact_mod_cast sum_tracePhaseFiberCard f hn.ne'
  have hsplit :
      (∑ c ∈ T, (tracePhaseFiberCard f n c : ℝ)) +
          tracePhaseFiberCard f n b = (p : ℝ) ^ n := by
    rw [← hsumReal]
    exact Finset.sum_erase_add
      (Finset.univ : Finset (ZMod p))
      (fun c ↦ (tracePhaseFiberCard f n c : ℝ)) (Finset.mem_univ b)
  have hpow : (p : ℝ) ^ n = (p : ℝ) ^ (n - 1) * p := by
    calc
      (p : ℝ) ^ n = (p : ℝ) ^ ((n - 1) + 1) := by
        congr 1
        omega
      _ = (p : ℝ) ^ (n - 1) * p := by rw [pow_succ]
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpminus : (1 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ p - 1)
  have hpmreal : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  rw [hpmreal] at hrest hpminus ⊢
  rw [abs_le]
  constructor
  · rw [hpow] at hsplit
    nlinarith
  · have hb := hupper b
    nlinarith

private theorem stepanov_error_le_sqrt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) (hd : 2 ≤ d) :
    ((par.S + d * (p - 1) * p ^ (n - 1) : ℕ) : ℝ) / par.R ≤
      ((8 * d ^ 2 * p ^ 2 : ℕ) : ℝ) * (Real.sqrt p) ^ n := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hn0 : 0 < n := par.n_pos
  have hR0 : 0 < par.R := by
    rw [par.R_eq]
    exact Nat.mul_pos hp0 par.K_pos
  let A := p ^ (par.u - 2)
  have hu2 : 2 ≤ par.u := by
    by_contra hu
    have huexp : par.u - 2 = 0 := by omega
    have hK := par.K_eq
    rw [huexp, pow_zero] at hK
    have hdiv : 1 / (2 * d) = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv] at hK
    have hKpos := par.K_pos
    omega
  have hAle : A ≤ 4 * d * par.K := by
    have hlt := Nat.lt_mul_div_succ A (by omega : 0 < 2 * d)
    have hK := par.K_eq
    dsimp [A] at hlt
    rw [← hK] at hlt
    calc
      A ≤ 2 * d * (par.K + 1) := Nat.le_of_lt hlt
      _ ≤ 4 * d * par.K := by
        nlinarith [par.two_mul_d_le_K]
  have hpowStep : p ^ n = p ^ (n - 1) * p := by
    calc
      p ^ n = p ^ ((n - 1) + 1) := by congr 1; omega
      _ = p ^ (n - 1) * p := by rw [pow_succ]
  have hSle : par.S ≤ p ^ n := by
    rw [par.S_eq]
    exact Nat.pow_le_pow_right hp0 (Nat.sub_le n 2)
  have hterm : d * (p - 1) * p ^ (n - 1) ≤ d * p ^ n := by
    calc
      d * (p - 1) * p ^ (n - 1) ≤ d * p * p ^ (n - 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left d (Nat.sub_le p 1))
      _ = d * (p ^ (n - 1) * p) := by ring
      _ = d * p ^ n := by rw [hpowStep]
  have hnum : par.S + d * (p - 1) * p ^ (n - 1) ≤ 2 * d * p ^ n := by
    calc
      par.S + d * (p - 1) * p ^ (n - 1) ≤ p ^ n + d * p ^ n :=
        Nat.add_le_add hSle hterm
      _ ≤ 2 * d * p ^ n := by
        have hpowpos : 0 < p ^ n := pow_pos hp0 _
        nlinarith
  have hnle : n ≤ 2 * par.u + 1 := by
    have h := Nat.lt_mul_div_succ n (by norm_num : 0 < 2)
    rw [← par.u_eq] at h
    omega
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hsqrtpow : (p : ℝ) ^ par.u ≤ (Real.sqrt p) ^ n := by
    calc
      (p : ℝ) ^ par.u = (Real.sqrt p) ^ (2 * par.u) := by
        rw [pow_mul, Real.sq_sqrt (by positivity)]
      _ ≤ (Real.sqrt p) ^ n := by
        apply pow_le_pow_right₀ hsqrt1
        simpa [par.u_eq, Nat.mul_comm] using Nat.div_mul_le_self n 2
  have hdecomp : p ^ (2 * par.u + 1) = p ^ 3 * A * p ^ par.u := by
    dsimp [A]
    calc
      p ^ (2 * par.u + 1) = p ^ (3 + (par.u - 2) + par.u) := by
        congr 1
        omega
      _ = p ^ 3 * p ^ (par.u - 2) * p ^ par.u := by
        simp only [pow_add]
  have hpower : (p : ℝ) ^ n ≤
      (p : ℝ) ^ 3 * A * (Real.sqrt p) ^ n := by
    calc
      (p : ℝ) ^ n ≤ (p : ℝ) ^ (2 * par.u + 1) := by
        exact pow_le_pow_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_le) hnle
      _ = (p : ℝ) ^ 3 * A * (p : ℝ) ^ par.u := by
        exact_mod_cast hdecomp
      _ ≤ (p : ℝ) ^ 3 * A * (Real.sqrt p) ^ n := by
        gcongr
  have hnumReal :
      ((par.S + d * (p - 1) * p ^ (n - 1) : ℕ) : ℝ) ≤
        (2 * d * p ^ n : ℕ) := by
    exact_mod_cast hnum
  have hAleReal : (A : ℝ) ≤ (4 * d * par.K : ℕ) := by
    exact_mod_cast hAle
  have hbound :
      ((par.S + d * (p - 1) * p ^ (n - 1) : ℕ) : ℝ) ≤
        ((8 * d ^ 2 * p ^ 2 : ℕ) : ℝ) *
          (Real.sqrt p) ^ n * par.R := by
    calc
      ((par.S + d * (p - 1) * p ^ (n - 1) : ℕ) : ℝ) ≤
          (2 * d : ℕ) * (p : ℝ) ^ n := by
        simpa using hnumReal
      _ ≤ (2 * d : ℕ) *
          ((p : ℝ) ^ 3 * A * (Real.sqrt p) ^ n) := by
        gcongr
      _ ≤ (2 * d : ℕ) *
          ((p : ℝ) ^ 3 * (4 * d * par.K : ℕ) *
            (Real.sqrt p) ^ n) := by
        gcongr
      _ = ((8 * d ^ 2 * p ^ 2 : ℕ) : ℝ) *
          (Real.sqrt p) ^ n * par.R := by
        rw [par.R_eq]
        push_cast
        ring
  apply (div_le_iff₀ (by exact_mod_cast hR0)).2
  simpa [mul_assoc] using hbound

private theorem tracePhaseFiberCard_eq_of_natDegree_one
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (hfdeg : f.natDegree = 1)
    {n : ℕ} (hn : 0 < n) (b : ZMod p) :
    tracePhaseFiberCard f n b = p ^ (n - 1) := by
  classical
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  let a := f.coeff 1
  let c := f.coeff 0
  have hf0 : f ≠ 0 := by
    intro hf
    rw [hf, Polynomial.natDegree_zero] at hfdeg
    omega
  have ha : a ≠ 0 := by
    have hc : f.coeff 1 = f.leadingCoeff := by
      rw [← hfdeg]
      exact Polynomial.coeff_natDegree
    dsimp [a]
    rw [hc]
    exact Polynomial.leadingCoeff_ne_zero.mpr hf0
  have hf : f = C a * X + C c := by
    simpa [a, c] using Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hfdeg)
  let ell : GaloisField p n →ₗ[ZMod p] ZMod p :=
    (Algebra.trace (ZMod p) (GaloisField p n)).comp
      (LinearMap.mulLeft (ZMod p)
        (algebraMap (ZMod p) (GaloisField p n) a))
  have haE : algebraMap (ZMod p) (GaloisField p n) a ≠ 0 :=
    by
      intro h
      apply ha
      apply (algebraMap (ZMod p) (GaloisField p n)).injective
      simpa using h
  have hellSurj : Function.Surjective ell := by
    have hnondeg :=
      (traceForm_nondegenerate (ZMod p) (GaloisField p n)).1
        (algebraMap (ZMod p) (GaloisField p n) a)
    simp_rw [Algebra.traceForm_apply] at hnondeg
    obtain ⟨y, hy⟩ : ∃ y : GaloisField p n,
        Algebra.trace (ZMod p) (GaloisField p n)
          (algebraMap (ZMod p) (GaloisField p n) a * y) ≠ 0 := by
      by_contra! h
      exact haE (hnondeg h)
    have hellY : ell y ≠ 0 := by simpa [ell] using hy
    intro t
    refine ⟨(t / ell y) • y, ?_⟩
    rw [map_smul]
    change (t / ell y) * ell y = t
    exact div_mul_cancel₀ t hellY
  let target := fun r : ZMod p ↦ r -
    Algebra.trace (ZMod p) (GaloisField p n)
      (algebraMap (ZMod p) (GaloisField p n) c)
  have heval (x : GaloisField p n) :
      Algebra.trace (ZMod p) (GaloisField p n)
          (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) =
        ell x + Algebra.trace (ZMod p) (GaloisField p n)
          (algebraMap (ZMod p) (GaloisField p n) c) := by
    simp [hf, ell]
  have hphase (r : ZMod p) : tracePhaseFiberCard f n r =
      (Finset.univ.filter fun x : GaloisField p n ↦ ell x = target r).card := by
    simp only [tracePhaseFiberCard]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heval]
    dsimp [target]
    constructor <;> intro h
    · linear_combination h
    · linear_combination h
  have hall (r s : ZMod p) :
      tracePhaseFiberCard f n r = tracePhaseFiberCard f n s := by
    rw [hphase, hphase]
    apply AddMonoidHom.card_fiber_eq_of_mem_range ell.toAddMonoidHom
    · rcases hellSurj (target r) with ⟨x, hx⟩
      exact ⟨x, hx⟩
    · rcases hellSurj (target s) with ⟨x, hx⟩
      exact ⟨x, hx⟩
  have hsum := sum_tracePhaseFiberCard f hn.ne'
  have hsumconst : ∑ r : ZMod p, tracePhaseFiberCard f n r =
      ∑ _r : ZMod p, tracePhaseFiberCard f n b := by
    apply Finset.sum_congr rfl
    intro r hr
    exact hall r b
  rw [hsumconst] at hsum
  have heq : p * tracePhaseFiberCard f n b = p * p ^ (n - 1) := by
    simpa [ZMod.card, show p ^ n = p * p ^ (n - 1) by
      calc
        p ^ n = p ^ ((n - 1) + 1) := by congr 1; omega
        _ = p * p ^ (n - 1) := by rw [pow_succ]; ring] using hsum
  exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos heq

/-- Trace-phase fibres are equidistributed up to a uniform square-root error for all large
extensions. -/
theorem additive_stepanov_point_count
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ b : ZMod p,
      |(tracePhaseFiberCard f n b : ℝ) - (p : ℝ) ^ (n - 1)| ≤
        C * (Real.sqrt p) ^ n := by
  let d := f.natDegree
  by_cases hd1 : d = 1
  · refine ⟨0, le_rfl, 1, ?_⟩
    intro n hn b
    have heq := tracePhaseFiberCard_eq_of_natDegree_one f
      (by simpa [d] using hd1) (n := n) (by omega) b
    rw [heq]
    push_cast
    simp
  · have hd2 : 2 ≤ d := by
      dsimp [d]
      omega
    obtain ⟨N₀, hparameters⟩ := exists_additive_stepanov_parameters
      p d (Fact.out : p.Prime) hd2 (by simpa [d] using hsmall)
    let C : ℝ := ((8 * d ^ 2 * p ^ 3 : ℕ) : ℝ)
    refine ⟨C, by positivity, max N₀ 1, ?_⟩
    intro n hn b
    have hnN : N₀ ≤ n := (Nat.le_max_left _ _).trans hn
    have hn0 : 0 < n := lt_of_lt_of_le (Nat.zero_lt_one.trans_le
      (Nat.le_max_right N₀ 1)) hn
    let par : AdditiveStepanovParameters p d n :=
      Classical.choice (hparameters n hnN)
    let E : ℝ :=
      ((par.S + d * (p - 1) * p ^ (n - 1) : ℕ) : ℝ) / par.R
    have hE : 0 ≤ E := by positivity
    have hupper : ∀ c : ZMod p,
        (tracePhaseFiberCard f n c : ℝ) ≤ (p : ℝ) ^ (n - 1) + E := by
      intro c
      exact stepanov_traceFiberCard_upper par f (by rfl)
        (by simpa [d] using hpos) (by simpa [d] using hsmall) c
    have habs := abs_tracePhaseFiberCard_sub_le_of_upper
      f hn0 E hE hupper b
    have herror : E ≤ ((8 * d ^ 2 * p ^ 2 : ℕ) : ℝ) *
        (Real.sqrt p) ^ n := stepanov_error_le_sqrt par hd2
    calc
      |(tracePhaseFiberCard f n b : ℝ) - (p : ℝ) ^ (n - 1)| ≤
          ((p - 1 : ℕ) : ℝ) * E := habs
      _ ≤ ((p - 1 : ℕ) : ℝ) *
          (((8 * d ^ 2 * p ^ 2 : ℕ) : ℝ) * (Real.sqrt p) ^ n) := by
        gcongr
      _ ≤ C * (Real.sqrt p) ^ n := by
        dsimp [C]
        have hpminus : p - 1 ≤ p := Nat.sub_le p 1
        have hcoef : (p - 1) * (8 * d ^ 2 * p ^ 2) ≤
            8 * d ^ 2 * p ^ 3 := by
          calc
            (p - 1) * (8 * d ^ 2 * p ^ 2) ≤
                p * (8 * d ^ 2 * p ^ 2) := Nat.mul_le_mul_right _ hpminus
            _ = 8 * d ^ 2 * p ^ 3 := by ring
        calc
          ((p - 1 : ℕ) : ℝ) *
                (((8 * d ^ 2 * p ^ 2 : ℕ) : ℝ) * (Real.sqrt p) ^ n) =
              (((p - 1) * (8 * d ^ 2 * p ^ 2) : ℕ) : ℝ) *
                (Real.sqrt p) ^ n := by push_cast; ring
          _ ≤ ((8 * d ^ 2 * p ^ 3 : ℕ) : ℝ) *
                (Real.sqrt p) ^ n := by gcongr

end TranslationalTilings.Stepanov
