import Mathlib.FieldTheory.RatFunc.AsPolynomial
import TranslationalTilings.NumberTheory.Stepanov.ArtinSchreier
import TranslationalTilings.NumberTheory.Stepanov.HasseMultiplicity
import TranslationalTilings.NumberTheory.Stepanov.NewtonWaring

/-!
# Translation products and nonvanishing of the additive auxiliary polynomial

This module forms the product of a nested polynomial over all translations by the prime field,
expresses the invariant product as a polynomial in `X ^ p - X`, and controls the quotient's
coefficient degrees. An Artin--Schreier norm argument then shows successively that all coefficient
blocks of a vanishing additive Stepanov auxiliary polynomial are zero, yielding the required
nonvanishing theorem.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators

namespace TranslationalTilings.Stepanov

open Polynomial

/-- Translate the outer variable of a nested polynomial by the constant `beta`. -/
noncomputable def polynomialTranslate
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (beta : ZMod p) :
    Polynomial (Polynomial (ZMod p)) :=
  P.comp (Polynomial.X + Polynomial.C (Polynomial.C beta))

/-- The product of all prime-field translates of a nested polynomial. -/
noncomputable def translationProduct
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) :
    Polynomial (Polynomial (ZMod p)) :=
  ∏ beta : ZMod p, polynomialTranslate P beta

/-- The full translation product is invariant under every prime-field translation. -/
theorem translationProduct_translate
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (gamma : ZMod p) :
    polynomialTranslate (translationProduct P) gamma = translationProduct P := by
  classical
  rw [polynomialTranslate, translationProduct]
  change (Polynomial.compRingHom (X + C (C gamma)))
      (∏ beta : ZMod p, polynomialTranslate P beta) = _
  rw [map_prod]
  let e : ZMod p ≃ ZMod p := Equiv.addRight gamma
  calc
    ∏ beta : ZMod p,
        (polynomialTranslate P beta).comp (X + C (C gamma)) =
        ∏ beta : ZMod p, polynomialTranslate P (e beta) := by
          apply Finset.prod_congr rfl
          intro beta _
          unfold polynomialTranslate
          rw [Polynomial.comp_assoc]
          congr 1
          simp [e]
          ring
    _ = ∏ beta : ZMod p, polynomialTranslate P beta := e.prod_comp _

private theorem prime_dvd_natDegree_of_translate_one
    {p : ℕ} [Fact p.Prime]
    {F : Polynomial (Polynomial (ZMod p))} (hFpos : 0 < F.natDegree)
    (hinv : F.comp (X + C (C (1 : ZMod p))) = F) :
    p ∣ F.natDegree := by
  let m := F.natDegree
  have hm : m = F.natDegree := rfl
  have hmpos : 0 < m := by simpa [m] using hFpos
  have hc := congrArg (fun Q : Polynomial (Polynomial (ZMod p)) ↦ Q.coeff (m - 1)) hinv
  rw [← Polynomial.taylor_apply] at hc
  rw [Polynomial.taylor_coeff] at hc
  have hderiv :
      (F.hasseDeriv (m - 1)).natDegree < 2 := by
    refine lt_of_le_of_lt (Polynomial.natDegree_hasseDeriv_le F (m - 1)) ?_
    rw [hm]
    omega
  rw [Polynomial.eval_eq_sum_range' hderiv] at hc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one, Polynomial.hasseDeriv_coeff] at hc
  have hchoose : m.choose (m - 1) = m := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    rw [hk]
    simp
  have hone : 1 + (m - 1) = m := by omega
  rw [Nat.choose_self, Nat.cast_one, one_mul, hone, hchoose, hm,
    Polynomial.coeff_natDegree] at hc
  simp only [map_one, mul_one] at hc
  have hcast : (m : Polynomial (ZMod p)) = 0 := by
    have hlc : F.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt hFpos)
    apply (mul_eq_zero.mp ?_).resolve_right hlc
    linear_combination hc
  exact (CharP.cast_eq_zero_iff (Polynomial (ZMod p)) p m).mp hcast

private theorem frobeniusVariable_translate
    {p : ℕ} [Fact p.Prime] (beta : ZMod p) :
    (X ^ p - X : Polynomial (Polynomial (ZMod p))).comp
        (X + C (C beta)) = X ^ p - X := by
  rw [Polynomial.sub_comp, Polynomial.X_pow_comp, Polynomial.X_comp]
  rw [add_pow_char]
  rw [← map_pow, ← map_pow, ZMod.pow_card]
  ring

private theorem exists_comp_frobeniusVariable_of_invariant
    {p : ℕ} [Fact p.Prime]
    (F : Polynomial (Polynomial (ZMod p)))
    (hinv : ∀ beta : ZMod p, F.comp (X + C (C beta)) = F) :
    ∃ Q : Polynomial (Polynomial (ZMod p)),
      F = Q.comp (X ^ p - X) ∧ Q.natDegree * p ≤ F.natDegree := by
  classical
  induction hm : F.natDegree using Nat.strong_induction_on generalizing F with
  | h n ih =>
      by_cases hF : F = 0
      · subst F
        exact ⟨0, by simp, by simp⟩
      by_cases hn : n = 0
      · have hFnat : F.natDegree = 0 := hm.trans hn
        refine ⟨C (F.coeff 0), ?_, ?_⟩
        · rw [Polynomial.C_comp]
          exact Polynomial.eq_C_of_natDegree_eq_zero hFnat
        · simp [hn]
      have hnpos : 0 < n := by
        exact Nat.pos_of_ne_zero hn
      have hpdvd : p ∣ n := by
        rw [← hm]
        apply prime_dvd_natDegree_of_translate_one
          (by simpa [hm] using hnpos)
        simpa using hinv 1
      rcases hpdvd with ⟨a, ha⟩
      have hp0 : 0 < p := (Fact.out : p.Prime).pos
      have hWmonic : (X ^ p - X : Polynomial (Polynomial (ZMod p))).Monic := by
        apply Polynomial.monic_X_pow_sub
        simpa using (Fact.out : p.Prime).one_lt
      have hWdeg : (X ^ p - X : Polynomial (Polynomial (ZMod p))).natDegree = p := by
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
        simpa using (Fact.out : p.Prime).one_lt
      let G := F - C F.leadingCoeff * (X ^ p - X) ^ a
      have htermne : C F.leadingCoeff *
          (X ^ p - X : Polynomial (Polynomial (ZMod p))) ^ a ≠ 0 := by
        exact mul_ne_zero (Polynomial.C_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hF))
          (hWmonic.pow a).ne_zero
      have htermdeg : (C F.leadingCoeff *
          (X ^ p - X : Polynomial (Polynomial (ZMod p))) ^ a).degree = F.degree := by
        rw [Polynomial.degree_eq_natDegree htermne, Polynomial.degree_eq_natDegree hF,
          Polynomial.natDegree_C_mul (Polynomial.leadingCoeff_ne_zero.mpr hF),
          hWmonic.natDegree_pow, hWdeg, hm, ha, Nat.mul_comm]
      have htermlc : (C F.leadingCoeff *
          (X ^ p - X : Polynomial (Polynomial (ZMod p))) ^ a).leadingCoeff =
          F.leadingCoeff := by
        simp [hWmonic.leadingCoeff, Polynomial.leadingCoeff_pow]
      have hGdeg : G.natDegree < n := by
        by_cases hG : G = 0
        · simp [hG, hnpos]
        · rw [← hm]
          apply (Polynomial.natDegree_lt_iff_degree_lt hG).mpr
          simpa [G, Polynomial.degree_eq_natDegree hF] using
            (Polynomial.degree_sub_lt_left htermdeg.symm hF htermlc.symm)
      have hGinv : ∀ beta : ZMod p, G.comp (X + C (C beta)) = G := by
        intro beta
        simp only [G, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp,
          Polynomial.pow_comp, hinv beta, frobeniusVariable_translate beta]
      rcases ih G.natDegree hGdeg G hGinv rfl with ⟨Q₀, hQ₀, hQ₀deg⟩
      refine ⟨Q₀ + C F.leadingCoeff * X ^ a, ?_, ?_⟩
      · rw [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
          Polynomial.X_pow_comp]
        rw [← hQ₀]
        dsimp [G]
        ring
      · have hQ₀lt : Q₀.natDegree < a := by
          have hlt : Q₀.natDegree * p < a * p :=
            lt_of_le_of_lt hQ₀deg (by simpa [ha, Nat.mul_comm] using hGdeg)
          exact (Nat.mul_lt_mul_right hp0).mp hlt
        have hmonomialDeg : (C F.leadingCoeff * X ^ a :
            Polynomial (Polynomial (ZMod p))).natDegree = a := by
          rw [Polynomial.natDegree_C_mul (Polynomial.leadingCoeff_ne_zero.mpr hF),
            Polynomial.natDegree_X_pow]
        calc
          (Q₀ + C F.leadingCoeff * X ^ a).natDegree * p ≤
              max Q₀.natDegree
                (C F.leadingCoeff * X ^ a :
                  Polynomial (Polynomial (ZMod p))).natDegree * p :=
            Nat.mul_le_mul_right p (Polynomial.natDegree_add_le _ _)
          _ = a * p := by rw [hmonomialDeg, max_eq_right hQ₀lt.le]
          _ = n := (Nat.mul_comm a p).trans ha.symm

/-- A translation product of outer degree below `p` factors through `X ^ p - X` with
quotient degree at most `p - 1`. -/
theorem exists_translationProductQuotient
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p) :
    ∃ Q : Polynomial (Polynomial (ZMod p)),
      translationProduct P =
          Q.comp (Polynomial.X ^ p - Polynomial.X) ∧
        Q.natDegree ≤ p - 1 := by
  classical
  have hinv : ∀ beta : ZMod p,
      (translationProduct P).comp (X + C (C beta)) = translationProduct P := by
    intro beta
    exact translationProduct_translate P beta
  rcases exists_comp_frobeniusVariable_of_invariant (translationProduct P) hinv with
    ⟨Q, hQ, hQdeg⟩
  refine ⟨Q, hQ, ?_⟩
  have hprod : (translationProduct P).natDegree ≤ p * (p - 1) := by
    rw [translationProduct]
    calc
      (∏ beta : ZMod p, polynomialTranslate P beta).natDegree ≤
          ∑ beta : ZMod p, (polynomialTranslate P beta).natDegree := by
            simpa using Polynomial.natDegree_prod_le (Finset.univ : Finset (ZMod p))
              (polynomialTranslate P)
      _ = p * P.natDegree := by
        simp [polynomialTranslate, ← Polynomial.taylor_apply]
      _ ≤ p * (p - 1) := Nat.mul_le_mul_left p (Nat.le_pred_of_lt hP)
  apply Nat.le_of_mul_le_mul_right _ (Fact.out : p.Prime).pos
  exact hQdeg.trans (hprod.trans_eq (Nat.mul_comm p (p - 1)))

/-- A chosen quotient expressing a low-degree translation product as a polynomial in `X ^ p - X`. -/
noncomputable def translationProductQuotient
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) :
    Polynomial (Polynomial (ZMod p)) :=
  if hP : P.natDegree < p then
    Classical.choose (exists_translationProductQuotient P hP)
  else 0

/-- The chosen translation-product quotient satisfies the factorization and degree bound. -/
theorem translationProductQuotient_spec
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p) :
    translationProduct P =
        (translationProductQuotient P).comp
          (Polynomial.X ^ p - Polynomial.X) ∧
      (translationProductQuotient P).natDegree ≤ p - 1 := by
  rw [translationProductQuotient, dif_pos hP]
  exact Classical.choose_spec (exists_translationProductQuotient P hP)

private theorem coeff_mul_natDegree_le_add
    {R : Type*} [CommRing R]
    (A B : Polynomial (Polynomial R)) (a b n : ℕ)
    (hA : ∀ i, (A.coeff i).natDegree ≤ a)
    (hB : ∀ i, (B.coeff i).natDegree ≤ b) :
    ((A * B).coeff n).natDegree ≤ a + b := by
  classical
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro ij hij
  exact Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add (hA ij.1) (hB ij.2))

-- Expanding translation coefficients requires normalizing a nested polynomial composition.
private theorem polynomialTranslate_coeff_natDegree_lt
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (beta : ZMod p)
    {S : ℕ} (hS : 0 < S) (hcoeff : ∀ i, (P.coeff i).natDegree < S)
    (n : ℕ) : ((polynomialTranslate P beta).coeff n).natDegree < S := by
  classical
  rw [polynomialTranslate, ← Polynomial.taylor_apply, Polynomial.taylor_coeff,
    Polynomial.hasseDeriv_apply, Polynomial.eval_sum, Polynomial.sum_def]
  simp_rw [Polynomial.eval_monomial]
  refine lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le P.support
      (fun i ↦
        ((i.choose n : Polynomial (ZMod p)) * P.coeff i) *
          (Polynomial.C beta) ^ (i - n)) ?_)
    (Nat.pred_lt hS.ne')
  intro i hi
  refine Polynomial.natDegree_mul_le.trans ?_
  calc
    ((i.choose n : Polynomial (ZMod p)) * P.coeff i).natDegree +
          ((Polynomial.C beta) ^ (i - n)).natDegree ≤
        ((i.choose n : Polynomial (ZMod p))).natDegree +
          (P.coeff i).natDegree +
            (i - n) * (Polynomial.C beta).natDegree :=
      Nat.add_le_add Polynomial.natDegree_mul_le Polynomial.natDegree_pow_le
    _ ≤ S - 1 := by
      simpa only [Nat.pred_eq_sub_one, Polynomial.natDegree_natCast, Polynomial.natDegree_C,
        zero_add, mul_zero, Nat.add_zero] using
        Nat.le_pred_of_lt (hcoeff i)

private theorem translationProduct_coeff_natDegree_lt
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p)))
    {S : ℕ} (hS : 0 < S) (hcoeff : ∀ i, (P.coeff i).natDegree < S)
    (n : ℕ) : ((translationProduct P).coeff n).natDegree < p * S := by
  classical
  have hprod (s : Finset (ZMod p)) : ∀ n,
      ((∏ beta ∈ s, polynomialTranslate P beta).coeff n).natDegree ≤
        s.card * (S - 1) := by
    induction s using Finset.induction_on with
    | empty =>
        intro n
        simp only [Finset.prod_empty, Finset.card_empty, zero_mul]
        rw [Polynomial.coeff_one]
        split <;> simp
    | @insert beta s hbeta ih =>
        intro n
        rw [Finset.prod_insert hbeta]
        refine (coeff_mul_natDegree_le_add _ _ (S - 1) (s.card * (S - 1)) n
          (fun i ↦ Nat.le_pred_of_lt
            (polynomialTranslate_coeff_natDegree_lt P beta hS hcoeff i))
          (ih)).trans ?_
        rw [Finset.card_insert_of_notMem hbeta]
        simp only [Nat.add_mul]
        omega
  rw [translationProduct]
  refine lt_of_le_of_lt (hprod Finset.univ n) ?_
  rw [Finset.card_univ, ZMod.card]
  exact Nat.mul_lt_mul_of_pos_left (Nat.pred_lt hS.ne') (Fact.out : p.Prime).pos

private theorem coeff_natDegree_lt_of_comp_frobeniusVariable
    {p : ℕ} [Fact p.Prime]
    (Q : Polynomial (Polynomial (ZMod p)))
    {B : ℕ} (hB : 0 < B)
    (hcomp : ∀ n,
      (((Q.comp (X ^ p - X)).coeff n : Polynomial (ZMod p))).natDegree < B) :
    ∀ n, (Q.coeff n).natDegree < B := by
  classical
  let W : Polynomial (Polynomial (ZMod p)) := X ^ p - X
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hWdeg : W.natDegree = p := by
    dsimp [W]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt,
      Polynomial.natDegree_X_pow]
    simpa using hp1
  have hWmonic : W.Monic := by
    dsimp [W]
    apply Polynomial.monic_X_pow_sub
    simpa using hp1
  induction hm : Q.natDegree using Nat.strong_induction_on generalizing Q with
  | h m ih =>
      intro n
      by_cases hQ : Q = 0
      · subst Q
        simp [hB]
      have hlc : Q.leadingCoeff.natDegree < B := by
        have hc := hcomp (Q.comp W).natDegree
        rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_comp
          (by rw [hWdeg]; exact hp0.ne'), hWmonic.leadingCoeff, one_pow, mul_one] at hc
        exact hc
      have hstrip : ∀ r, (Q.eraseLead.coeff r).natDegree < B := by
        rcases Q.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt | hz
        · intro r
          refine ih Q.eraseLead.natDegree (by simpa [hm] using hlt) Q.eraseLead ?_ rfl r
          intro k
          have hidentity : Q.eraseLead.comp W =
              Q.comp W - C Q.leadingCoeff * W ^ Q.natDegree := by
            apply eq_sub_of_add_eq
            simpa only [Polynomial.add_comp, Polynomial.mul_comp,
              Polynomial.C_comp, Polynomial.X_pow_comp] using
              congrArg (fun R ↦ R.comp W) Q.eraseLead_add_C_mul_X_pow
          rw [hidentity, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
          refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_
          rw [max_lt_iff]
          refine ⟨?_, ?_⟩
          · simpa [W] using hcomp k
          · refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
            have hmap : W ^ Q.natDegree =
                ((X ^ p - X : Polynomial (ZMod p)) ^ Q.natDegree).map C := by
              simp [W]
            rw [hmap, Polynomial.coeff_map, Polynomial.natDegree_C]
            simpa using hlc
        · intro r
          rw [hz]
          simp [hB]
      rw [← Q.eraseLead_add_C_mul_X_pow, Polynomial.coeff_add]
      refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
      rw [max_lt_iff]
      refine ⟨hstrip n, ?_⟩
      rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
      split
      · simpa using hlc
      · simp [hB]

/-- Coefficients of the translation-product quotient have inner degree strictly below `p * S`. -/
theorem translationProductQuotient_coeff_natDegree_lt
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p)
    {S : ℕ} (hS : 0 < S)
    (hcoeff : ∀ i, (P.coeff i).natDegree < S) (a : ℕ) :
    ((translationProductQuotient P).coeff a).natDegree < p * S := by
  apply coeff_natDegree_lt_of_comp_frobeniusVariable
    (translationProductQuotient P) (Nat.mul_pos (Fact.out : p.Prime).pos hS)
  intro n
  rw [← (translationProductQuotient_spec P hP).1]
  exact translationProduct_coeff_natDegree_lt P hS hcoeff n

/-- The norm polynomial obtained by evaluating the translation quotient at `f 0 - f ^ (p ^ u)`. -/
noncomputable def zeroBlockNormPolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (P : Polynomial (Polynomial (ZMod p))) : Polynomial (ZMod p) :=
  (translationProductQuotient P).eval
    (Polynomial.C (f.coeff 0) - f ^ (p ^ u))

/-- A degree bound for the zero-block norm polynomial in terms of the block and phase degrees. -/
theorem zeroBlockNormPolynomial_natDegree_lt
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (P : Polynomial (Polynomial (ZMod p)))
    (hP : P.natDegree < p) {S : ℕ} (hS : 0 < S)
    (hcoeff : ∀ i, (P.coeff i).natDegree < S) :
    (zeroBlockNormPolynomial f u P).natDegree <
      p * S + f.natDegree * p ^ u * (p - 1) := by
  classical
  let Q := translationProductQuotient P
  let V := C (f.coeff 0) - f ^ (p ^ u)
  have hT : 0 < p * S + f.natDegree * p ^ u * (p - 1) :=
    Nat.add_pos_left (Nat.mul_pos (Fact.out : p.Prime).pos hS) _
  have hV : V.natDegree ≤ f.natDegree * p ^ u := by
    dsimp [V]
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_pow]
    simp [Nat.mul_comm]
  rw [zeroBlockNormPolynomial, Polynomial.eval_eq_sum_range]
  refine lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le
      (Finset.range (Q.natDegree + 1))
      (fun i ↦ Q.coeff i * V ^ i) ?_)
    (Nat.pred_lt hT.ne')
  intro i hi
  apply Nat.le_pred_of_lt
  have hiQ : i ≤ Q.natDegree := by
    simpa [Finset.mem_range] using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hiP : i ≤ p - 1 := hiQ.trans (translationProductQuotient_spec P hP).2
  refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
  refine lt_of_lt_of_le
    (Nat.add_lt_add_of_lt_of_le
      (translationProductQuotient_coeff_natDegree_lt P hP hS hcoeff i)
      Polynomial.natDegree_pow_le) ?_
  calc
    p * S + i * V.natDegree
        ≤ p * S + i * (f.natDegree * p ^ u) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left i hV) _
    _ ≤ p * S + (p - 1) * (f.natDegree * p ^ u) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right (f.natDegree * p ^ u) hiP) _
    _ = p * S + f.natDegree * p ^ u * (p - 1) := by ac_rfl

private theorem lowerTracePolynomial_frobenius_sub_self
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) :
    (lowerTracePolynomial f u) ^ p - lowerTracePolynomial f u =
      f ^ (p ^ u) - f := by
  classical
  induction u with
  | zero => simp [lowerTracePolynomial, (Fact.out : p.Prime).ne_zero]
  | succ u ih =>
      have ih' :
          (∑ t ∈ Finset.range u, f ^ (p ^ t)) ^ p -
              (∑ t ∈ Finset.range u, f ^ (p ^ t)) =
            f ^ (p ^ u) - f := by
        simpa [lowerTracePolynomial] using ih
      have hpow : (f ^ (p ^ u)) ^ p = f ^ (p ^ (u + 1)) := by
        rw [← pow_mul, pow_succ]
      rw [lowerTracePolynomial, Finset.sum_range_succ]
      rw [add_pow_char, hpow]
      calc
        (∑ t ∈ Finset.range u, f ^ p ^ t) ^ p + f ^ p ^ (u + 1) -
              ((∑ t ∈ Finset.range u, f ^ p ^ t) + f ^ p ^ u) =
            ((∑ t ∈ Finset.range u, f ^ p ^ t) ^ p -
              (∑ t ∈ Finset.range u, f ^ p ^ t)) +
                (f ^ p ^ (u + 1) - f ^ p ^ u) := by ring
        _ = f ^ p ^ (u + 1) - f := by rw [ih']; ring

private theorem upperTracePolynomial_frobenius_sub_self
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) {n u : ℕ} (hu : u ≤ n) :
    (upperTracePolynomial f n u) ^ p - upperTracePolynomial f n u =
      f ^ (p ^ n) - f ^ (p ^ u) := by
  classical
  have hupper : upperTracePolynomial f n u =
      lowerTracePolynomial f n - lowerTracePolynomial f u := by
    rw [upperTracePolynomial, lowerTracePolynomial, lowerTracePolynomial,
      Finset.sum_Ico_eq_sub _ hu]
  rw [hupper, sub_pow_char]
  calc
    lowerTracePolynomial f n ^ p - lowerTracePolynomial f u ^ p -
          (lowerTracePolynomial f n - lowerTracePolynomial f u) =
        (lowerTracePolynomial f n ^ p - lowerTracePolynomial f n) -
          (lowerTracePolynomial f u ^ p - lowerTracePolynomial f u) := by ring
    _ = f ^ p ^ n - f ^ p ^ u := by
      rw [lowerTracePolynomial_frobenius_sub_self,
        lowerTracePolynomial_frobenius_sub_self]
      ring

/-- Divisibility of a block evaluation by `X ^ (p ^ n)` transfers to its zero-block norm. -/
theorem X_pow_dvd_zeroBlockNormPolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (n u : ℕ)
    (P : Polynomial (Polynomial (ZMod p)))
    (hP : P.natDegree < p) (hu : u ≤ n)
    (hdiv : Polynomial.X ^ (p ^ n) ∣
      P.eval (upperTracePolynomial f n u)) :
    Polynomial.X ^ (p ^ n) ∣ zeroBlockNormPolynomial f u P := by
  classical
  let Phi := upperTracePolynomial f n u
  let V := C (f.coeff 0) - f ^ (p ^ u)
  let Q := translationProductQuotient P
  have hprod : X ^ (p ^ n) ∣ (translationProduct P).eval Phi := by
    apply hdiv.trans
    rw [translationProduct, Polynomial.eval_prod]
    simpa [polynomialTranslate, Polynomial.eval_comp] using
      (Finset.dvd_prod_of_mem
        (fun beta : ZMod p ↦ (polynomialTranslate P beta).eval Phi)
        (Finset.mem_univ (0 : ZMod p)))
  have hQW : X ^ (p ^ n) ∣ Q.eval (Phi ^ p - Phi) := by
    have hevalW : (X ^ p - X : Polynomial (Polynomial (ZMod p))).eval Phi =
        Phi ^ p - Phi := by simp
    rw [← hevalW, ← Polynomial.eval_comp,
      ← (translationProductQuotient_spec P hP).1]
    simpa [Phi] using hprod
  have hX : X ∣ f - C (f.coeff 0) := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub]
    simp
  have hfpow : X ^ (p ^ n) ∣ f ^ (p ^ n) - C (f.coeff 0) := by
    have hpow := pow_dvd_pow_of_dvd hX (p ^ n)
    simpa [sub_pow_char_pow, ← Polynomial.C_pow, ZMod.pow_card_pow] using hpow
  have harg : X ^ (p ^ n) ∣ (Phi ^ p - Phi) - V := by
    have hid : (Phi ^ p - Phi) - V = f ^ (p ^ n) - C (f.coeff 0) := by
      dsimp [Phi, V]
      rw [upperTracePolynomial_frobenius_sub_self f hu]
      ring
    rwa [hid]
  have hdiff : X ^ (p ^ n) ∣
      Q.eval (Phi ^ p - Phi) - Q.eval V :=
    harg.trans (Polynomial.sub_dvd_eval_sub (Phi ^ p - Phi) V Q)
  have := dvd_sub hQW hdiff
  simpa [zeroBlockNormPolynomial, Q, V] using this

/-- Under the Stepanov parameter inequality, a sufficiently divisible zero-block norm is zero. -/
theorem zeroBlockNormPolynomial_eq_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (P : Polynomial (Polynomial (ZMod p)))
    (hP : P.natDegree < p)
    (hcoeff : ∀ i, (P.coeff i).natDegree < par.S)
    (hdiv : Polynomial.X ^ (p ^ n) ∣
      P.eval (upperTracePolynomial f n par.u)) :
    zeroBlockNormPolynomial f par.u P = 0 := by
  apply Polynomial.eq_zero_of_dvd_of_natDegree_lt
    (X_pow_dvd_zeroBlockNormPolynomial f n par.u P hP
      (by rw [par.u_eq]; exact Nat.div_le_self n 2) hdiv)
  rw [Polynomial.natDegree_X_pow]
  exact (zeroBlockNormPolynomial_natDegree_lt f par.u P hP par.S_pos hcoeff).trans
    (by simpa [hdegree] using par.norm_degree_ok)

/-- The Artin--Schreier polynomial governing the zero-block norm evaluation. -/
noncomputable def zeroBlockArtinSchreierPolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) :
    Polynomial (RatFunc (ZMod p)) :=
  Polynomial.X ^ p - Polynomial.X +
    Polynomial.C
      (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
        (f ^ (p ^ u) - Polynomial.C (f.coeff 0)))

/-- The zero-block Artin--Schreier polynomial is a translate of the rational-function model. -/
theorem zeroBlockArtinSchreierPolynomial_translate
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) :
    zeroBlockArtinSchreierPolynomial f u =
      (artinSchreierRatFuncPolynomial (eraseConstant f)).comp
      (Polynomial.X + Polynomial.C
          (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
            (lowerTracePolynomial f u))) := by
  have htrace :
      (Polynomial.C (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
          (lowerTracePolynomial f u)) : Polynomial (RatFunc (ZMod p))) ^ p -
        Polynomial.C (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
          (lowerTracePolynomial f u)) =
      Polynomial.C (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) f) ^
          (p ^ u) -
        Polynomial.C (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) f) := by
    simpa only [map_sub, map_pow] using
      congrArg
        (fun g : Polynomial (ZMod p) ↦
          (Polynomial.C
            (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) g) :
              Polynomial (RatFunc (ZMod p))))
        (lowerTracePolynomial_frobenius_sub_self f u)
  simp only [zeroBlockArtinSchreierPolynomial,
    artinSchreierRatFuncPolynomial, eraseConstant, Polynomial.add_comp,
    Polynomial.sub_comp, Polynomial.X_pow_comp, Polynomial.X_comp,
    Polynomial.C_comp, add_pow_char, map_sub, map_pow]
  linear_combination -htrace

/-- The zero-block Artin--Schreier polynomial is irreducible when the phase degree lies in
`(0,p)`. -/
theorem zeroBlockArtinSchreierPolynomial_irreducible
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    Irreducible (zeroBlockArtinSchreierPolynomial f u) := by
  rw [zeroBlockArtinSchreierPolynomial_translate]
  let t : RatFunc (ZMod p) :=
    algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
      (lowerTracePolynomial f u)
  have hirr := artinSchreierRatFuncPolynomial_irreducible
    (eraseConstant f) (by simpa [eraseConstant_natDegree f hpos] using hpos)
      (by simpa [eraseConstant_natDegree f hpos] using hsmall)
  rw [Polynomial.comp_eq_aeval]
  exact hirr.map (Polynomial.algEquivAevalXAddC t).toRingEquiv.toMulEquiv

/-- Evaluate a nested block after mapping its coefficients into an Artin--Schreier extension. -/
noncomputable def zeroBlockEval
    {p : ℕ} [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L]
    (P : Polynomial (Polynomial (ZMod p))) (z : L) : L :=
  P.eval₂
    ((algebraMap (RatFunc (ZMod p)) L).comp
      (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)))) z

/-- Vanishing of the zero-block norm forces one translated block factor to vanish at every
Artin--Schreier root. -/
theorem zeroBlockNorm_eq_zero_implies_exists_zero_factor
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p)
    (hnorm : zeroBlockNormPolynomial f u P = 0) :
    ∀ {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L] (z : L),
      Polynomial.aeval z (zeroBlockArtinSchreierPolynomial f u) = 0 →
      ∃ beta : ZMod p,
        zeroBlockEval P
          (z + algebraMap (RatFunc (ZMod p)) L
            (algebraMap (ZMod p) (RatFunc (ZMod p)) beta)) = 0 := by
  classical
  intro L _ _ z hz
  let phi : Polynomial (ZMod p) →+* L :=
    (algebraMap (RatFunc (ZMod p)) L).comp
      (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)))
  let V : Polynomial (ZMod p) := C (f.coeff 0) - f ^ (p ^ u)
  let Q := translationProductQuotient P
  have hz0 : z ^ p - z + phi (f ^ (p ^ u) - C (f.coeff 0)) = 0 := by
    simpa [zeroBlockArtinSchreierPolynomial, Polynomial.aeval_def, phi] using hz
  have hzarg : phi V = z ^ p - z := by
    dsimp [V]
    rw [map_sub]
    rw [map_sub] at hz0
    linear_combination -hz0
  have hnormL : phi (zeroBlockNormPolynomial f u P) = 0 := by
    rw [hnorm, map_zero]
  have hQzero : Q.eval₂ phi (z ^ p - z) = 0 := by
    rw [← hzarg, Polynomial.eval₂_at_apply]
    simpa [zeroBlockNormPolynomial, Q, V] using hnormL
  have hprod : (translationProduct P).eval₂ phi z = 0 := by
    rw [(translationProductQuotient_spec P hP).1,
      Polynomial.eval₂_comp]
    simpa [Q] using hQzero
  rw [translationProduct, Polynomial.eval₂_finsetProd] at hprod
  simp only [polynomialTranslate, Polynomial.eval₂_comp,
    Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C,
    phi] at hprod
  rw [Finset.prod_eq_zero_iff] at hprod
  rcases hprod with ⟨beta, _, hbeta⟩
  refine ⟨beta, ?_⟩
  change P.eval₂
    ((algebraMap (RatFunc (ZMod p)) L).comp
      (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))))
    (z + algebraMap (RatFunc (ZMod p)) L
      (algebraMap (ZMod p) (RatFunc (ZMod p)) beta)) = 0
  simpa using hbeta

/-- Translating an Artin--Schreier root by a prime-field element does not change its
minimal polynomial. -/
theorem zeroBlock_minpoly_add_primeField
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L]
    (z : L)
    (hz : Polynomial.aeval z (zeroBlockArtinSchreierPolynomial f u) = 0)
    (beta : ZMod p) :
    minpoly (RatFunc (ZMod p))
      (z + algebraMap (RatFunc (ZMod p)) L
        (algebraMap (ZMod p) (RatFunc (ZMod p)) beta)) =
      zeroBlockArtinSchreierPolynomial f u := by
  let _ : CharP L p :=
    charP_of_injective_algebraMap
      (algebraMap (RatFunc (ZMod p)) L).injective p
  let b : L := algebraMap (RatFunc (ZMod p)) L
    (algebraMap (ZMod p) (RatFunc (ZMod p)) beta)
  have hb : b ^ p = b := by
    dsimp [b]
    rw [← map_pow, ← map_pow, ZMod.pow_card]
  have hy : Polynomial.aeval (z + b)
      (zeroBlockArtinSchreierPolynomial f u) = 0 := by
    simp only [zeroBlockArtinSchreierPolynomial, Polynomial.aeval_def,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at hz ⊢
    rw [show (z + b) ^ p = z ^ p + b ^ p by exact add_pow_char z b p, hb]
    linear_combination hz
  have hmonic : (zeroBlockArtinSchreierPolynomial f u).Monic := by
    let c := algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
      (f ^ (p ^ u) - C (f.coeff 0))
    have heq : zeroBlockArtinSchreierPolynomial f u =
        artinSchreierPolynomial p (-c) := by
      simp [zeroBlockArtinSchreierPolynomial, artinSchreierPolynomial, c]
      ring
    rw [heq]
    exact artinSchreierPolynomial_monic (-c)
  exact (minpoly.eq_of_irreducible_of_monic
    (zeroBlockArtinSchreierPolynomial_irreducible f u hpos hsmall)
    hy hmonic).symm

/-- A nested polynomial of outer degree below `p` that vanishes at such a translated root
is zero. -/
theorem eq_zero_of_zeroBlockEval_eq_zero
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p)
    {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L]
    (z : L)
    (hz : Polynomial.aeval z (zeroBlockArtinSchreierPolynomial f u) = 0)
    (beta : ZMod p)
    (hzero : zeroBlockEval P
      (z + algebraMap (RatFunc (ZMod p)) L
        (algebraMap (ZMod p) (RatFunc (ZMod p)) beta)) = 0) :
    P = 0 := by
  let K := RatFunc (ZMod p)
  let amap : Polynomial (ZMod p) →+* K :=
    algebraMap (Polynomial (ZMod p)) K
  have hinj : Function.Injective amap := by
    simpa [amap, K] using RatFunc.algebraMap_injective (ZMod p)
  let y : L := z + algebraMap K L (algebraMap (ZMod p) K beta)
  let PK : Polynomial K := P.map amap
  have hroot : Polynomial.aeval y PK = 0 := by
    simpa [y, PK, amap, K, Polynomial.aeval_def, zeroBlockEval,
      Polynomial.eval₂_map] using hzero
  have hdvd : zeroBlockArtinSchreierPolynomial f u ∣ PK := by
    have hmin := minpoly.dvd K y hroot
    rw [zeroBlock_minpoly_add_primeField f u hpos hsmall z hz beta] at hmin
    exact hmin
  have hPK : PK = 0 := by
    by_contra hne
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne
    have hzeroDegree :
        (zeroBlockArtinSchreierPolynomial f u).natDegree = p := by
      let c := algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
        (f ^ (p ^ u) - C (f.coeff 0))
      have heq : zeroBlockArtinSchreierPolynomial f u =
          artinSchreierPolynomial p (-c) := by
        simp [zeroBlockArtinSchreierPolynomial, artinSchreierPolynomial, c]
        ring
      rw [heq, artinSchreierPolynomial_natDegree]
    have hmapDegree : PK.natDegree = P.natDegree := by
      exact Polynomial.natDegree_map_eq_of_injective hinj P
    rw [hzeroDegree, hmapDegree] at hle
    exact (not_le_of_gt hP) hle
  apply (Polynomial.map_eq_zero_iff hinj).mp
  exact hPK

/-- The outer polynomial block obtained by fixing the second index of the auxiliary coefficients. -/
noncomputable def auxiliaryBlock
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (j : Fin (par.K + 1)) : Polynomial (Polynomial (ZMod p)) :=
  ∑ i : Fin p, Polynomial.monomial i.1 (e.coeff i j)

/-- Every auxiliary block has outer degree strictly below `p`. -/
theorem auxiliaryBlock_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (j : Fin (par.K + 1)) : (auxiliaryBlock e j).natDegree < p := by
  classical
  refine lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le Finset.univ
      (fun i : Fin p ↦ Polynomial.monomial i.1 (e.coeff i j)) ?_)
    (Nat.pred_lt (Fact.out : p.Prime).ne_zero)
  intro i hi
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_pred_of_lt i.2)

/-- Every coefficient of an auxiliary block has inner degree strictly below `par.S`. -/
theorem auxiliaryBlock_coeff_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (j : Fin (par.K + 1)) (i : ℕ) :
    ((auxiliaryBlock e j).coeff i).natDegree < par.S := by
  classical
  rw [auxiliaryBlock, Polynomial.finsetSum_coeff]
  refine lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le Finset.univ
      (fun q : Fin p ↦ (Polynomial.monomial q.1 (e.coeff q j)).coeff i) ?_)
    (Nat.pred_lt par.S_pos.ne')
  intro q hq
  rw [Polynomial.coeff_monomial]
  split
  · exact Nat.le_pred_of_lt (e.degree_lt q j)
  · simp

private theorem additiveAuxiliaryPolynomial_eq_sum_blocks
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p))
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) :
    additiveAuxiliaryPolynomial par f e =
      ∑ j : Fin (par.K + 1),
        (auxiliaryBlock e j).eval (upperTracePolynomial f n par.u) *
          X ^ (p ^ n * j.1) := by
  classical
  rw [additiveAuxiliaryPolynomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [auxiliaryBlock, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial, Finset.sum_mul]

/-- If earlier blocks vanish, vanishing of the full auxiliary polynomial forces
`X ^ (p ^ n)` to divide the current block evaluation. -/
theorem X_pow_dvd_auxiliaryBlock_eval_of_previous_eq_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p))
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (haux : additiveAuxiliaryPolynomial par f e = 0)
    (j : Fin (par.K + 1))
    (hprev : ∀ q : Fin (par.K + 1), q.1 < j.1 →
      auxiliaryBlock e q = 0) :
    Polynomial.X ^ (p ^ n) ∣
      (auxiliaryBlock e j).eval (upperTracePolynomial f n par.u) := by
  classical
  let N := p ^ n
  let A := fun q : Fin (par.K + 1) ↦
    (auxiliaryBlock e q).eval (upperTracePolynomial f n par.u)
  let T := fun q : Fin (par.K + 1) ↦ A q * X ^ (N * q.1)
  have hsum : ∑ q : Fin (par.K + 1), T q = 0 := by
    rw [← additiveAuxiliaryPolynomial_eq_sum_blocks par f e]
    simpa [T, A, N] using haux
  have hother (q : Fin (par.K + 1)) (hqj : q ≠ j) :
      X ^ (N * (j.1 + 1)) ∣ T q := by
    by_cases hq : q.1 < j.1
    · have hz := hprev q hq
      simp [T, A, hz]
    · have hjq : j.1 + 1 ≤ q.1 := by
        have hne : q.1 ≠ j.1 := fun h ↦ hqj (Fin.ext h)
        omega
      have hpow : (X : Polynomial (ZMod p)) ^ (N * (j.1 + 1)) ∣
          X ^ (N * q.1) :=
        pow_dvd_pow (X : Polynomial (ZMod p)) (Nat.mul_le_mul_left N hjq)
      exact dvd_mul_of_dvd_right hpow (A q)
  have hrest : X ^ (N * (j.1 + 1)) ∣
      ∑ q ∈ (Finset.univ.erase j), T q := by
    apply Finset.dvd_sum
    intro q hq
    exact hother q (Finset.ne_of_mem_erase hq)
  have hterm : X ^ (N * (j.1 + 1)) ∣ T j := by
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin (par.K + 1))))
      (f := T) (Finset.mem_univ j)
    have heq : T j = -(∑ q ∈ (Finset.univ.erase j), T q) := by
      rw [hsum] at hsplit
      linear_combination hsplit
    rw [heq]
    exact dvd_neg.mpr hrest
  have hcancel :
      X ^ N * X ^ (N * j.1) ∣ A j * X ^ (N * j.1) := by
    simpa [T, Nat.mul_add, pow_add, mul_comm, mul_left_comm, mul_assoc] using hterm
  exact (mul_dvd_mul_iff_right
    (pow_ne_zero (N * j.1) (Polynomial.X_ne_zero :
      (X : Polynomial (ZMod p)) ≠ 0))).mp hcancel

private theorem zeroBlockArtinSchreierPolynomial_natDegree
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) :
    (zeroBlockArtinSchreierPolynomial f u).natDegree = p := by
  let c := algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
    (f ^ (p ^ u) - C (f.coeff 0))
  have heq : zeroBlockArtinSchreierPolynomial f u =
      artinSchreierPolynomial p (-c) := by
    simp [zeroBlockArtinSchreierPolynomial, artinSchreierPolynomial, c]
    ring
  rw [heq, artinSchreierPolynomial_natDegree]

/-- If the auxiliary polynomial and all preceding blocks vanish, then the current block vanishes. -/
theorem auxiliaryBlock_eq_zero_of_previous_eq_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (haux : additiveAuxiliaryPolynomial par f e = 0)
    (j : Fin (par.K + 1))
    (hprev : ∀ q : Fin (par.K + 1), q.1 < j.1 →
      auxiliaryBlock e q = 0) :
    auxiliaryBlock e j = 0 := by
  let P := auxiliaryBlock e j
  have hP : P.natDegree < p := auxiliaryBlock_natDegree_lt e j
  have hcoeff : ∀ i, (P.coeff i).natDegree < par.S :=
    auxiliaryBlock_coeff_natDegree_lt e j
  have hdiv : X ^ (p ^ n) ∣ P.eval (upperTracePolynomial f n par.u) :=
    X_pow_dvd_auxiliaryBlock_eval_of_previous_eq_zero par f e haux j hprev
  have hnorm : zeroBlockNormPolynomial f par.u P = 0 :=
    zeroBlockNormPolynomial_eq_zero par f hdegree P hP hcoeff hdiv
  let G := zeroBlockArtinSchreierPolynomial f par.u
  let E := G.SplittingField
  let z : E := Polynomial.rootOfSplits
    (Polynomial.SplittingField.splits G)
    (Polynomial.degree_ne_of_natDegree_ne (by
      rw [Polynomial.natDegree_map, zeroBlockArtinSchreierPolynomial_natDegree]
      exact (Fact.out : p.Prime).ne_zero))
  have hz : Polynomial.aeval z G = 0 := by
    simpa [Polynomial.aeval_def, z] using
      (Polynomial.eval_rootOfSplits (Polynomial.SplittingField.splits G)
        (Polynomial.degree_ne_of_natDegree_ne (by
          rw [Polynomial.natDegree_map,
            zeroBlockArtinSchreierPolynomial_natDegree]
          exact (Fact.out : p.Prime).ne_zero)))
  have hex := zeroBlockNorm_eq_zero_implies_exists_zero_factor
    f par.u P hP hnorm z (by simpa [G] using hz)
  rcases hex with ⟨beta, hbeta⟩
  exact eq_zero_of_zeroBlockEval_eq_zero f par.u
    (by simpa [hdegree] using hpos) (by simpa [hdegree] using hsmall)
    P hP z (by simpa [G] using hz) beta hbeta

/-- A vanishing additive auxiliary polynomial has every auxiliary coefficient block equal
to zero. -/
theorem all_auxiliaryBlocks_eq_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (haux : additiveAuxiliaryPolynomial par f e = 0) :
    ∀ j : Fin (par.K + 1), auxiliaryBlock e j = 0 := by
  intro j
  induction hj : j.1 using Nat.strong_induction_on generalizing j with
  | h m ih =>
      apply auxiliaryBlock_eq_zero_of_previous_eq_zero
        par f hdegree hpos hsmall e haux j
      intro q hq
      exact ih q.1 (by simpa [hj] using hq) q rfl

private theorem auxiliaryBlock_coeff_fin
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (i : Fin p) (j : Fin (par.K + 1)) :
    (auxiliaryBlock e j).coeff i.1 = e.coeff i j := by
  classical
  rw [auxiliaryBlock, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro q hq hqi
    rw [Polynomial.coeff_monomial, if_neg]
    exact fun hval ↦ hqi (Fin.ext hval)
  · simp

/-- Nonzero auxiliary coefficients give a nonzero additive auxiliary polynomial via the
block argument. -/
theorem additiveAuxiliaryPolynomial_ne_zero_of_blocks
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) (he : e.Nonzero) :
    additiveAuxiliaryPolynomial par f e ≠ 0 := by
  intro haux
  rcases he with ⟨i, j, hij⟩
  apply hij
  have hblock := all_auxiliaryBlocks_eq_zero
    par f hdegree hpos hsmall e haux j
  have hcoeff := congrArg
    (fun P : Polynomial (Polynomial (ZMod p)) ↦ P.coeff i.1) hblock
  rw [auxiliaryBlock_coeff_fin] at hcoeff
  simpa using hcoeff

/-- The additive Stepanov auxiliary polynomial associated to nonzero coefficients is nonzero. -/
theorem additiveAuxiliaryPolynomial_ne_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) (he : e.Nonzero) :
    additiveAuxiliaryPolynomial par f e ≠ 0 :=
  additiveAuxiliaryPolynomial_ne_zero_of_blocks
    par f hdegree hpos hsmall e he

end TranslationalTilings.Stepanov
