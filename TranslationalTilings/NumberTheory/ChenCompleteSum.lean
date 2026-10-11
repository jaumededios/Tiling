import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Content
import TranslationalTilings.NumberTheory.PolynomialCongruence

/-!
# Complete polynomial sums

This file develops the conditional prime-power estimate of
Arkhipov--Chubarikov--Karatsuba, including the stationary-phase recurrences,
the middle- and small-prime inductions, and a support-indexed CRT
factorization.  The prime-denominator input is packaged by
`PolynomialPrimeSumBound`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- The complete polynomial phase sum over the residue class `v` modulo `p`. -/
noncomputable def primePowerResidueClassSum
    (p a : ℕ) (hp : p.Prime) (f : Polynomial ℤ)
    (v : ZMod p) : ℂ :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  ∑ x : ZMod (p ^ a),
    if (x.val : ZMod p) = v then
      ZMod.stdAddChar (Polynomial.eval x (f.map (Int.castRingHom _)))
    else 0

/-- The shortened stationary sum obtained after fixing a residue class modulo `p`. -/
noncomputable def primePowerStationaryShortSum
    (p a : ℕ) (hp : p.Prime) (f : Polynomial ℤ)
    (v : ZMod p) : ℂ :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p ^ (a - 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  ∑ y : ZMod (p ^ (a - 2)),
    ZMod.stdAddChar
      (Polynomial.eval ((v.val + p * y.val : ℕ) : ZMod (p ^ a))
        (f.map (Int.castRingHom _)))

/-- Decompose a prime-power complete sum into its residue classes modulo `p`. -/
theorem ack_completeSum_eq_sum_residueClasses
    [Fact p.Prime] (hp : p.Prime) (_ha : 0 < a)
    (f : Polynomial ℤ) :
  polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f =
    ∑ v : ZMod p, primePowerResidueClassSum p a hp f v := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  simp only [polynomialCompleteSum, primePowerResidueClassSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.sum_eq_single ((x.val : ℕ) : ZMod p)]
  · simp
  · intro b _hb hne
    simp only [ite_eq_right_iff]
    intro h
    exfalso
    apply hne
    rw [← h]
  · simp

private theorem residueClassFiber_card
    (hp : p.Prime) (ha : 0 < a) (v : ZMod p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
    ((Finset.univ : Finset (ZMod (p ^ a))).filter
      (fun x => (x.val : ZMod p) = v)).card = p ^ (a - 1) := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpdiv : p ∣ p ^ a := dvd_pow_self p ha.ne'
  let phi : ZMod (p ^ a) →+ ZMod p :=
    (ZMod.castHom hpdiv (ZMod p)).toAddMonoidHom
  have hsurj : Function.Surjective phi := ZMod.castHom_surjective hpdiv
  have heq (w : ZMod p) :
      ((Finset.univ : Finset (ZMod (p ^ a))).filter
        (fun x => phi x = w)).card =
      ((Finset.univ : Finset (ZMod (p ^ a))).filter
        (fun x => phi x = v)).card := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range phi
      (hsurj w) (hsurj v)
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (ZMod (p ^ a))))
    (t := (Finset.univ : Finset (ZMod p))) (f := phi) (by simp)
  have hcard : p ^ a = p *
      ((Finset.univ : Finset (ZMod (p ^ a))).filter
        (fun x => phi x = v)).card := by
    have hpartition' : p ^ a = ∑ w : ZMod p,
        ((Finset.univ : Finset (ZMod (p ^ a))).filter
          (fun x => phi x = w)).card := by
      simpa only [Finset.card_univ, ZMod.card] using hpartition
    calc
      p ^ a = ∑ w : ZMod p,
          ((Finset.univ : Finset (ZMod (p ^ a))).filter
            (fun x => phi x = w)).card := hpartition'
      _ = p * ((Finset.univ : Finset (ZMod (p ^ a))).filter
            (fun x => phi x = v)).card := by
        simp_rw [heq]
        simp
  have hpow : p ^ a = p * p ^ (a - 1) := by
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    simp [pow_succ']
  have hc : ((Finset.univ : Finset (ZMod (p ^ a))).filter
        (fun x => phi x = v)).card = p ^ (a - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    rw [← hcard, ← hpow]
  calc
    ((Finset.univ : Finset (ZMod (p ^ a))).filter
        (fun x => (x.val : ZMod p) = v)).card =
        ((Finset.univ : Finset (ZMod (p ^ a))).filter
          (fun x => phi x = v)).card := by
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [phi]
    _ = p ^ (a - 1) := hc

/-- The trivial cardinality bound for a single residue-class sum. -/
theorem ack_residueClass_trivial
    (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ) (v : ZMod p) :
  ‖primePowerResidueClassSum p a hp f v‖ ≤ (p : ℝ) ^ (a - 1) := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [primePowerResidueClassSum]
  calc
    ‖∑ x : ZMod (p ^ a),
        if (x.val : ZMod p) = v then
          ZMod.stdAddChar (Polynomial.eval x (f.map (Int.castRingHom _)))
        else 0‖ ≤
        ∑ x : ZMod (p ^ a),
          ‖if (x.val : ZMod p) = v then
            ZMod.stdAddChar (Polynomial.eval x (f.map (Int.castRingHom _)))
          else 0‖ := norm_sum_le _ _
    _ = (((Finset.univ : Finset (ZMod (p ^ a))).filter
          (fun x => (x.val : ZMod p) = v)).card : ℝ) := by
      calc
        ∑ x : ZMod (p ^ a),
            ‖if (x.val : ZMod p) = v then
              ZMod.stdAddChar (Polynomial.eval x (f.map (Int.castRingHom _)))
            else 0‖ =
            ∑ x : ZMod (p ^ a),
              if (x.val : ZMod p) = v then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          split <;> simp_all [ZMod.stdAddChar_apply, Circle.norm_coe]
        _ = _ := by simp
    _ = (p : ℝ) ^ (a - 1) := by
      rw [residueClassFiber_card hp ha v]
      norm_num

/-- The degree-dependent threshold separating the large-prime range. -/
noncomputable def chenLargePrimeThreshold (d : ℕ) : ℝ :=
  Real.rpow (d - 1 : ℝ) ((2 * d : ℝ) / (d - 2 : ℝ))

/-- The degree-dependent upper threshold for the middle-prime range. -/
noncomputable def chenMiddlePrimeThreshold (d : ℕ) : ℝ :=
  Real.rpow (d - 1 : ℝ) ((d : ℝ) / (d - 2 : ℝ))

private theorem modPrime_nonconstantPart_ne_zero
    (_hp : p.Prime) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
    Polynomial.modPrime p (Polynomial.nonconstantPart f) ≠ 0 := by
  intro hzero
  apply hprimitive
  rw [Polynomial.nonconstantContentNat, Polynomial.contentNat,
    ← Int.natCast_dvd]
  apply Polynomial.dvd_content_iff_C_dvd.mpr
  apply (Polynomial.C_dvd_iff_dvd_coeff (p : ℤ) _).mpr
  intro n
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hn := congrArg (fun q : Polynomial (ZMod p) => q.coeff n) hzero
  simpa [Polynomial.modPrime] using hn

private theorem modPrime_natDegree_pos
    (hp : p.Prime) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
    0 < (Polynomial.modPrime p f).natDegree := by
  have hbar := modPrime_nonconstantPart_ne_zero hp f hprimitive
  by_contra h
  have hdeg : (Polynomial.modPrime p f).natDegree ≤ 0 := by omega
  have hbarEq : Polynomial.modPrime p (Polynomial.nonconstantPart f) =
      Polynomial.modPrime p f -
        Polynomial.C ((f.coeff 0 : ℤ) : ZMod p) := by
    simp [Polynomial.modPrime, Polynomial.nonconstantPart]
  rw [hbarEq, Polynomial.eq_C_of_natDegree_le_zero hdeg] at hbar
  simp [Polynomial.modPrime] at hbar

private theorem completeSum_trivial
    (q : ℕ) (hq : 0 < q) (f : Polynomial ℤ) :
    ‖polynomialCompleteSum q hq f‖ ≤ q := by
  let _ : NeZero q := ⟨hq.ne'⟩
  rw [polynomialCompleteSum]
  calc
    ‖∑ x : ZMod q,
        ZMod.stdAddChar (Polynomial.eval x
          (f.map (Int.castRingHom (ZMod q))))‖ ≤
        ∑ x : ZMod q,
          ‖ZMod.stdAddChar (Polynomial.eval x
            (f.map (Int.castRingHom (ZMod q))))‖ := norm_sum_le _ _
    _ = ∑ _x : ZMod q, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro x _hx
      simp [ZMod.stdAddChar_apply, Circle.norm_coe]
    _ = q := by simp

/-- The prime-modulus base estimate, conditional on a prime polynomial-sum bound. -/
theorem chen_prime_base_of
    (hWeil : PolynomialPrimeSumBound)
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (_hd : 3 ≤ d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum p hp.pos f‖ ≤
    min (Real.rpow p ((1 : ℝ) / d))
        ((d - 1 : ℝ) *
          Real.rpow p (-(1 : ℝ) / 2 + (1 : ℝ) / d)) *
      Real.rpow p (1 - (1 : ℝ) / d) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let fbar := Polynomial.modPrime p f
  have hepos : 0 < fbar.natDegree :=
    modPrime_natDegree_pos hp f hprimitive
  have he_le : fbar.natDegree ≤ d := by
    exact Polynomial.natDegree_map_le.trans_eq hdegree
  have hep : fbar.natDegree < p := lt_of_le_of_lt he_le hdp
  have hweil := hWeil p fbar hepos hep
  have hsum : polynomialCompleteSum p hp.pos f =
      ∑ x : ZMod p, ZMod.stdAddChar (fbar.eval x) := by
    rfl
  have hweil' : ‖polynomialCompleteSum p hp.pos f‖ ≤
      (d - 1 : ℝ) * Real.sqrt p := by
    rw [hsum]
    calc
      ‖∑ x : ZMod p, ZMod.stdAddChar (fbar.eval x)‖ ≤
          (fbar.natDegree - 1 : ℝ) * Real.sqrt p := hweil
      _ ≤ (d - 1 : ℝ) * Real.sqrt p := by
        gcongr
  have htriv := completeSum_trivial p hp.pos f
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hscale : 0 ≤ Real.rpow p (1 - (1 : ℝ) / d) :=
    Real.rpow_nonneg hpR.le _
  have hfirst : Real.rpow p ((1 : ℝ) / d) *
      Real.rpow p (1 - (1 : ℝ) / d) = p := by
    calc
      Real.rpow p ((1 : ℝ) / d) *
          Real.rpow p (1 - (1 : ℝ) / d) =
          Real.rpow p ((1 : ℝ) / d + (1 - (1 : ℝ) / d)) :=
        (Real.rpow_add hpR _ _).symm
      _ = p := by
        rw [show (1 : ℝ) / d + (1 - (1 : ℝ) / d) = 1 by ring]
        exact Real.rpow_one p
  have hsecond : ((d - 1 : ℝ) *
        Real.rpow p (-(1 : ℝ) / 2 + (1 : ℝ) / d)) *
      Real.rpow p (1 - (1 : ℝ) / d) =
      (d - 1 : ℝ) * Real.sqrt p := by
    rw [mul_assoc]
    congr 1
    calc
      Real.rpow p (-(1 : ℝ) / 2 + (1 : ℝ) / d) *
          Real.rpow p (1 - (1 : ℝ) / d) =
          Real.rpow p
            ((-(1 : ℝ) / 2 + (1 : ℝ) / d) +
              (1 - (1 : ℝ) / d)) := (Real.rpow_add hpR _ _).symm
      _ = Real.sqrt p := by
        rw [show (-(1 : ℝ) / 2 + (1 : ℝ) / d) +
            (1 - (1 : ℝ) / d) = 1 / 2 by ring]
        exact (Real.sqrt_eq_rpow p).symm
  rw [min_mul_of_nonneg _ _ hscale, hfirst, hsecond]
  exact le_min (by exact_mod_cast htriv) hweil'

/-- In the large-prime range, a derivative root has stationary order at least two. -/
theorem _root_.Polynomial.stationaryOrder_two_le
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (_hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  2 ≤ Polynomial.stationaryOrder f p mu.val := by
  have hd : 0 < d := by
    have horder :=
      Polynomial.ack_lemma_2_3 hp f hdegree.le hprimitive mu.val
    omega
  have hchild := Polynomial.stationaryChildInvariant hp f hdegree
    hd hprimitive mu.val
  exact Polynomial.stationaryOrder_two_le_of_isRoot hp f mu
    hchild.translate_ne_zero hmu

private theorem chen_contentNat_dvd_coeff (F : Polynomial ℤ) (n : ℕ) :
    (Polynomial.contentNat F : ℤ) ∣ F.coeff n := by
  simpa [Polynomial.contentNat, Int.natCast_natAbs, Int.abs_eq_normalize,
    Polynomial.normalize_content] using Polynomial.content_dvd_coeff (p := F) n

private theorem chen_primePowOrder_dvd_coeff
    (hp : p.Prime) (F : Polynomial ℤ) (n : ℕ) :
    ((p ^ Polynomial.coefficientPadicOrder p F : ℕ) : ℤ) ∣ F.coeff n := by
  let _ : Fact p.Prime := ⟨hp⟩
  apply dvd_trans (Int.natCast_dvd_natCast.mpr ?_) (chen_contentNat_dvd_coeff F n)
  exact (padicValNat_dvd_iff (Polynomial.coefficientPadicOrder p F)
    (Polynomial.contentNat F)).2 (Or.inr le_rfl)

private theorem chen_stationaryTranslate_coeff_of_pos
    (f : Polynomial ℤ) (p n : ℕ) (mu : ℤ) (hn : 0 < n) :
    (Polynomial.stationaryTranslate f p mu).coeff n =
      (Polynomial.taylor mu f).coeff n * (p : ℤ) ^ n := by
  rw [Polynomial.stationaryTranslate, Polynomial.coeff_sub,
    Polynomial.primeScaleTranslate]
  rw [Polynomial.coeff_C]
  simp only [hn.ne', ↓reduceIte, sub_zero]
  rw [show f.comp (Polynomial.C (p : ℤ) * Polynomial.X + Polynomial.C mu) =
      (Polynomial.taylor mu f).comp (Polynomial.C (p : ℤ) * Polynomial.X) by
    simp only [Polynomial.taylor_apply, Polynomial.comp_assoc,
      Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]]
  exact Polynomial.comp_C_mul_X_coeff

private theorem chen_taylor_derivative
    {R : Type*} [CommRing R] (r : R) (f : Polynomial R) :
    Polynomial.taylor r f.derivative = (Polynomial.taylor r f).derivative := by
  simp only [Polynomial.taylor_apply, Polynomial.derivative_comp]
  simp

private theorem chen_derivative_modPrime_ne_zero
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
    Polynomial.modPrime p f.derivative ≠ 0 := by
  let fbar := Polynomial.modPrime p f
  let e := fbar.natDegree
  have hepos : 0 < e := modPrime_natDegree_pos hp f hprimitive
  have he_le : e ≤ d := by
    exact Polynomial.natDegree_map_le.trans_eq hdegree
  have hep : e < p := lt_of_le_of_lt he_le hdp
  have hecast : (e : ZMod p) ≠ 0 := by
    intro he
    rw [ZMod.natCast_eq_zero_iff] at he
    exact (Nat.not_dvd_of_pos_of_lt hepos hep) he
  have hfbar : fbar ≠ 0 := by
    intro hzero
    dsimp [e] at hepos
    rw [hzero] at hepos
    simp at hepos
  have hlead : fbar.coeff e ≠ 0 := by
    rw [show e = fbar.natDegree from rfl, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hfbar
  intro hz
  have hz' : fbar.derivative = 0 := by
    simpa [fbar, Polynomial.modPrime] using hz
  have hcoeff := congrArg (fun F : Polynomial (ZMod p) ↦ F.coeff (e - 1)) hz'
  rw [Polynomial.coeff_derivative, Polynomial.coeff_zero,
    show e - 1 + 1 = e by omega] at hcoeff
  have hcast : ((e - 1 : ℕ) : ZMod p) + 1 = (e : ZMod p) := by
    rw [Nat.cast_sub (by omega : 1 ≤ e)]
    ring
  rw [hcast] at hcoeff
  exact (mul_ne_zero hlead hecast) hcoeff

private theorem chen_contentOrder_le_of_coeff_factor
    {p : ℕ} (hp : p.Prime) (F : Polynomial ℤ) (n : ℕ) (t : ℤ)
    (hcoeff : F.coeff n = t * (p : ℤ) ^ n)
    (ht : ¬ (p : ℤ) ∣ t) :
    Polynomial.coefficientPadicOrder p F ≤ n := by
  let u := Polynomial.coefficientPadicOrder p F
  by_contra hle
  have hnu : n + 1 ≤ u := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hle)
  have horder : (((p ^ u : ℕ) : ℤ)) ∣ F.coeff n :=
    chen_primePowOrder_dvd_coeff hp F n
  have hpow : (((p ^ (n + 1) : ℕ) : ℤ)) ∣ ((p ^ u : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (pow_dvd_pow p hnu)
  have hdiv := dvd_trans hpow horder
  rw [hcoeff] at hdiv
  have hcancel : ((p : ℤ) ^ n) * (p : ℤ) ∣ ((p : ℤ) ^ n) * t := by
    simpa [Nat.cast_pow, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hdiv
  exact ht ((mul_dvd_mul_iff_left
    (pow_ne_zero n (by exact_mod_cast hp.ne_zero))).mp hcancel)

/-- Bound stationary order by one plus the multiplicity of the derivative root. -/
theorem _root_.Polynomial.stationaryOrder_le_rootMultiplicity_succ
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (_hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  Polynomial.stationaryOrder f p mu.val ≤
    (Polynomial.modPrime p f.derivative).rootMultiplicity mu + 1 := by
  let gbar := Polynomial.modPrime p f.derivative
  let m := gbar.rootMultiplicity mu
  have hgbar : gbar ≠ 0 := chen_derivative_modPrime_ne_zero hp f hdegree hdp hprimitive
  have htaylorDeriv : (Polynomial.taylor mu gbar).coeff m ≠ 0 := by
    dsimp [m]
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr
      ((Polynomial.taylor_eq_zero mu gbar).not.mpr hgbar)
  have htaylorSucc :
      (Polynomial.taylor mu (Polynomial.modPrime p f)).coeff (m + 1) ≠ 0 := by
    have hrelation := congrArg (fun F : Polynomial (ZMod p) ↦ F.coeff m)
      (chen_taylor_derivative mu (Polynomial.modPrime p f))
    rw [Polynomial.coeff_derivative] at hrelation
    have hderivMap : (Polynomial.modPrime p f).derivative = gbar := by
      simp [gbar, Polynomial.modPrime]
    rw [hderivMap] at hrelation
    intro hzero
    apply htaylorDeriv
    rw [hrelation, hzero, zero_mul]
  have htaylorInt :
      ¬ (p : ℤ) ∣ (Polynomial.taylor (mu.val : ℤ) f).coeff (m + 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change ((Int.castRingHom (ZMod p))
      ((Polynomial.taylor (mu.val : ℤ) f).coeff (m + 1))) ≠ 0
    rw [← Polynomial.coeff_map]
    have hmap := Polynomial.map_taylor f (mu.val : ℤ) (Int.castRingHom (ZMod p))
    rw [hmap]
    simpa [Polynomial.modPrime, ZMod.natCast_zmod_val] using htaylorSucc
  change Polynomial.coefficientPadicOrder p
      (Polynomial.stationaryTranslate f p mu.val) ≤ m + 1
  exact chen_contentOrder_le_of_coeff_factor hp _ (m + 1) _
    (chen_stationaryTranslate_coeff_of_pos f p (m + 1) mu.val (by omega))
    htaylorInt

private theorem rootMassModPrime_le_natDegree
    (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ) :
    Polynomial.rootMassModPrime p f ≤ (Polynomial.modPrime p f).natDegree := by
  classical
  by_cases hf : Polynomial.modPrime p f = 0
  · simp [Polynomial.rootMassModPrime, Polynomial.rootsModPrime, hf]
  · have hroots : Polynomial.rootsModPrime p f =
        (Polynomial.modPrime p f).roots.toFinset := by
      ext x
      simp [Polynomial.rootsModPrime, Polynomial.mem_roots hf]
    rw [Polynomial.rootMassModPrime, hroots]
    calc
      ∑ x ∈ (Polynomial.modPrime p f).roots.toFinset,
          (Polynomial.modPrime p f).rootMultiplicity x =
          (Polynomial.modPrime p f).roots.card := by
        rw [← Multiset.toFinset_sum_count_eq
          (Polynomial.modPrime p f).roots]
        apply Finset.sum_congr rfl
        intro x _hx
        exact (Polynomial.count_roots (Polynomial.modPrime p f)).symm
      _ ≤ (Polynomial.modPrime p f).natDegree :=
        Polynomial.card_roots' (Polynomial.modPrime p f)

/-- The total derivative-root multiplicity modulo `p` is at most `d - 1`. -/
theorem _root_.Polynomial.derivativeRootMass_le
    [Fact p.Prime] (_hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (_hdp : d < p)
    (_hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  Polynomial.derivativeRootMass f p ≤ d - 1 := by
  calc
    Polynomial.derivativeRootMass f p ≤
        (Polynomial.modPrime p f.derivative).natDegree :=
      rootMassModPrime_le_natDegree p _
    _ = (Polynomial.modPrime p f).derivative.natDegree := by
      simp [Polynomial.modPrime, ← Polynomial.derivative_map]
    _ ≤ (Polynomial.modPrime p f).natDegree - 1 :=
      Polynomial.natDegree_derivative_le _
    _ ≤ f.natDegree - 1 :=
      Nat.sub_le_sub_right Polynomial.natDegree_map_le 1
    _ = d - 1 := by rw [hdegree]

private theorem chen_contentNat_C_mul (u : ℤ) (F : Polynomial ℤ) :
    Polynomial.contentNat (Polynomial.C u * F) =
      Int.natAbs u * Polynomial.contentNat F := by
  rw [Polynomial.contentNat, Polynomial.contentNat, Polynomial.content_C_mul,
    Int.natAbs_mul, ← Int.abs_eq_normalize, Int.natAbs_abs]

private theorem chen_contentNat_ne_zero (F : Polynomial ℤ) (hF : F ≠ 0) :
    Polynomial.contentNat F ≠ 0 := by
  rw [Polynomial.contentNat, Int.natAbs_ne_zero]
  exact fun h ↦ hF (Polynomial.content_eq_zero_iff.mp h)

private theorem chen_stationaryNormalize_derivative_eq
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
    (Polynomial.stationaryNormalize f p mu.val).derivative =
      Polynomial.normalizedPrimeScaleTranslate f.derivative p mu.val := by
  let A := Polynomial.stationaryTranslate f p mu.val
  let B := Polynomial.stationaryNormalize f p mu.val
  let P := Polynomial.primeScaleTranslate f.derivative p mu.val
  let u := Polynomial.stationaryOrder f p mu.val
  have hdpos : 0 < d := by
    have hbarpos := modPrime_natDegree_pos hp f hprimitive
    have hbarle : (Polynomial.modPrime p f).natDegree ≤ d :=
      Polynomial.natDegree_map_le.trans_eq hdegree
    omega
  have hchild := Polynomial.stationaryChildInvariant hp f hdegree hdpos
    hprimitive mu.val
  have hAne : A ≠ 0 := hchild.translate_ne_zero
  have hBdegree : B.natDegree = d := hchild.natDegree_eq
  have hBprimitive : ¬ p ∣ Polynomial.nonconstantContentNat B := hchild.primitive
  have hu2 : 2 ≤ u := Polynomial.stationaryOrder_two_le hp f hdegree hdp
    hprimitive mu hmu
  have hBderivMod : Polynomial.modPrime p B.derivative ≠ 0 :=
    chen_derivative_modPrime_ne_zero hp B hBdegree hdp hBprimitive
  have hBderiv : B.derivative ≠ 0 := by
    intro hzero
    apply hBderivMod
    simp [hzero, Polynomial.modPrime]
  have hBcontentPrimitive : ¬ p ∣ Polynomial.contentNat B.derivative := by
    intro hdiv
    apply hBderivMod
    ext n
    rw [Polynomial.modPrime, Polynomial.coeff_map, Polynomial.coeff_zero]
    change (((B.derivative.coeff n : ℤ) : ZMod p)) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hdiv)
      (chen_contentNat_dvd_coeff B.derivative n)
  have hAderiv : A.derivative = Polynomial.C (p : ℤ) * P := by
    dsimp [A, P]
    simp only [Polynomial.stationaryTranslate, map_sub, Polynomial.derivative_C,
      sub_zero, Polynomial.primeScaleTranslate, Polynomial.derivative_comp,
      Polynomial.derivative_add, Polynomial.derivative_C_mul_X,
      Polynomial.derivative_C, add_zero]
  have hspecA := Polynomial.normalizeAtPrime_spec hp A hAne
  have hspecAB : A = Polynomial.C ((p : ℤ) ^ u) * B := by
    simpa [A, B, u, Polynomial.stationaryNormalize,
      Polynomial.stationaryOrder, Nat.cast_pow] using hspecA
  have hspecDeriv := congrArg Polynomial.derivative hspecAB
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul,
    zero_add] at hspecDeriv
  have hPB : P = Polynomial.C ((p : ℤ) ^ (u - 1)) * B.derivative := by
    apply Polynomial.ext
    intro n
    have hnA := congrArg (fun F : Polynomial ℤ ↦ F.coeff n) hAderiv
    have hnSpec := congrArg (fun F : Polynomial ℤ ↦ F.coeff n) hspecDeriv
    simp only [Polynomial.coeff_C_mul] at hnA hnSpec
    have heq : (p : ℤ) ^ u * B.derivative.coeff n =
        (p : ℤ) * P.coeff n := by
      rw [← hnA, ← hnSpec]
    have hu : u - 1 + 1 = u := by omega
    rw [← hu, pow_succ] at heq
    simp only [Polynomial.coeff_C_mul]
    apply (Int.mul_eq_mul_left_iff
      (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)).mp
    simpa [mul_assoc, mul_comm, mul_left_comm] using heq.symm
  have hPne : P ≠ 0 := by
    rw [hPB]
    exact mul_ne_zero
      (Polynomial.C_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)))
      hBderiv
  have hPorder : Polynomial.coefficientPadicOrder p P = u - 1 := by
    rw [hPB, Polynomial.coefficientPadicOrder, chen_contentNat_C_mul]
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero)
      (chen_contentNat_ne_zero B.derivative hBderiv),
      padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hBcontentPrimitive, Nat.add_zero]
  have hspecP := Polynomial.normalizeAtPrime_spec hp P hPne
  change B.derivative = Polynomial.normalizeAtPrime p P
  apply Polynomial.ext
  intro n
  have hnPB := congrArg (fun F : Polynomial ℤ ↦ F.coeff n) hPB
  have hnP := congrArg (fun F : Polynomial ℤ ↦ F.coeff n) hspecP
  simp only [Polynomial.coeff_C_mul] at hnPB hnP
  rw [hPorder] at hnP
  simp only [Nat.cast_pow] at hnP
  have hpowne : (p : ℤ) ^ (u - 1) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  apply (Int.mul_eq_mul_left_iff hpowne).mp
  rw [← hnPB, ← hnP]

/-- A stationary child's derivative-root mass is bounded by its parent's local
root multiplicity. -/
theorem _root_.Polynomial.stationaryNormalize_derivativeRootMass_le
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  Polynomial.derivativeRootMass
      (Polynomial.stationaryNormalize f p mu.val) p ≤
    (Polynomial.modPrime p f.derivative).rootMultiplicity mu := by
  have hg : Polynomial.modPrime p f.derivative ≠ 0 :=
    chen_derivative_modPrime_ne_zero hp f hdegree hdp hprimitive
  change Polynomial.rootMassModPrime p
      (Polynomial.stationaryNormalize f p mu.val).derivative ≤ _
  rw [chen_stationaryNormalize_derivative_eq hp f hdegree hdp hprimitive mu hmu]
  exact Polynomial.ack_lemma_2_2_rootMass hp f.derivative hg mu hmu

/-- ACK inequality (2.9), converting a middle-prime fractional power to a
linear multiplicity weight. -/
theorem ack_ineq_2_9
    (d m p : ℕ) (hd : 3 ≤ d) (hm : 1 ≤ m) (hmd : m ≤ d - 1)
    (hp : d < p) (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d) :
  Real.rpow p ((m : ℝ) / d) ≤
    (m : ℝ) * Real.rpow p ((1 : ℝ) / d) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmdCast : (m : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hmd
  have hmdR : (m : ℝ) ≤ d - 1 := by
    simpa [Nat.cast_sub (by omega : 1 ≤ d)] using hmdCast
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (lt_trans (by omega : 0 < d) hp)
  have hden : (0 : ℝ) < d - 2 := by linarith
  let theta : ℝ := ((m : ℝ) - 1) / (d - 2)
  have htheta0 : 0 ≤ theta :=
    div_nonneg (sub_nonneg.mpr hmR) hden.le
  have htheta1 : theta ≤ 1 := by
    dsimp [theta]
    rw [div_le_one hden]
    linarith
  have hbern : Real.rpow (d - 1 : ℝ) theta ≤ m := by
    have hb := rpow_one_add_le_one_add_mul_self
      (s := (d : ℝ) - 2) (p := theta) (by linarith) htheta0 htheta1
    rw [show (1 : ℝ) + (d - 2) = d - 1 by ring,
      show (1 : ℝ) + theta * (d - 2) = m by
        dsimp [theta]
        field_simp
        ring] at hb
    exact hb
  let t : ℝ := ((m : ℝ) - 1) / d
  have ht0 : 0 ≤ t :=
    div_nonneg (sub_nonneg.mpr hmR) (by positivity)
  have hpt : Real.rpow p t ≤ Real.rpow (chenMiddlePrimeThreshold d) t :=
    Real.rpow_le_rpow hpR.le hpB ht0
  have hthreshold : Real.rpow (chenMiddlePrimeThreshold d) t =
      Real.rpow (d - 1 : ℝ) theta := by
    rw [chenMiddlePrimeThreshold]
    calc
      Real.rpow (Real.rpow (d - 1 : ℝ) ((d : ℝ) / (d - 2))) t =
          Real.rpow (d - 1 : ℝ) (((d : ℝ) / (d - 2)) * t) :=
        (Real.rpow_mul (by linarith : (0 : ℝ) ≤ d - 1) _ _).symm
      _ = Real.rpow (d - 1 : ℝ) theta := by
        congr 1
        dsimp [theta, t]
        field_simp
  have hsmall : Real.rpow p t ≤ m := by
    rw [hthreshold] at hpt
    exact hpt.trans hbern
  have hsplit : (m : ℝ) / d = (1 : ℝ) / d + t := by
    dsimp [t]
    field_simp
    ring
  rw [hsplit]
  calc
    Real.rpow p ((1 : ℝ) / d + t) =
        Real.rpow p ((1 : ℝ) / d) * Real.rpow p t :=
      Real.rpow_add hpR _ _
    _ ≤ Real.rpow p ((1 : ℝ) / d) * m :=
      mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hpR.le _)
    _ = m * Real.rpow p ((1 : ℝ) / d) := mul_comm _ _

/-- ACK inequality (2.11), the exponent comparison used for late roots. -/
theorem ack_ineq_2_11
    (d L r₁ M₁ : ℕ) (hd : 3 ≤ d) (hr : 0 < r₁)
    (hL : r₁ * L ≤ M₁ + r₁) :
  (L : ℝ) ≤
    (L + 1 : ℝ) * (1 - (1 : ℝ) / d) - 1 + (2 : ℝ) / d +
      (M₁ : ℝ) / ((r₁ : ℝ) * d) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hr0 : (r₁ : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hLR : (r₁ : ℝ) * L ≤ M₁ + r₁ := by exact_mod_cast hL
  have hnum : (0 : ℝ) ≤ M₁ + r₁ - r₁ * L := by linarith
  rw [show (L + 1 : ℝ) * (1 - (1 : ℝ) / d) - 1 + (2 : ℝ) / d +
      (M₁ : ℝ) / ((r₁ : ℝ) * d) =
      L + ((M₁ : ℝ) + r₁ - r₁ * L) / (r₁ * d) by
    field_simp [hd0, hr0]
    ring]
  exact le_add_of_nonneg_right (div_nonneg hnum (by positivity))

/-- ACK inequality (2.12), absorbing the late-root count into derivative mass. -/
theorem ack_ineq_2_12
    (d r₁ M₁ p : ℕ) (hd : 3 ≤ d) (hr : 1 ≤ r₁)
    (hrM : r₁ ≤ M₁) (hMd : M₁ ≤ d - 1) (hp : d < p)
    (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d) :
  (r₁ : ℝ) *
      Real.rpow p ((M₁ : ℝ) / ((r₁ : ℝ) * d)) ≤
    (M₁ : ℝ) * Real.rpow p ((1 : ℝ) / d) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hrR : (1 : ℝ) ≤ r₁ := by exact_mod_cast hr
  have hrMR : (r₁ : ℝ) ≤ M₁ := by exact_mod_cast hrM
  have hMdCast : (M₁ : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hMd
  have hMdR : (M₁ : ℝ) ≤ d - 1 := by
    simpa [Nat.cast_sub (by omega : 1 ≤ d)] using hMdCast
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (lt_trans (by omega : 0 < d) hp)
  have hrpos : (0 : ℝ) < r₁ := lt_of_lt_of_le zero_lt_one hrR
  have hden : (0 : ℝ) < d - 2 := by linarith
  let x : ℝ := (M₁ : ℝ) / r₁
  have hx1 : 1 ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ hrpos]
    simpa using hrMR
  have hxd : x ≤ d - 1 := by
    dsimp [x]
    calc
      (M₁ : ℝ) / r₁ ≤ M₁ := div_le_self (by positivity) hrR
      _ ≤ d - 1 := hMdR
  let theta : ℝ := (x - 1) / (d - 2)
  have htheta0 : 0 ≤ theta :=
    div_nonneg (sub_nonneg.mpr hx1) hden.le
  have htheta1 : theta ≤ 1 := by
    dsimp [theta]
    rw [div_le_one hden]
    linarith
  have hbern : Real.rpow (d - 1 : ℝ) theta ≤ x := by
    have hb := rpow_one_add_le_one_add_mul_self
      (s := (d : ℝ) - 2) (p := theta) (by linarith) htheta0 htheta1
    rw [show (1 : ℝ) + (d - 2) = d - 1 by ring,
      show (1 : ℝ) + theta * (d - 2) = x by
        dsimp [theta]
        field_simp
        ring] at hb
    exact hb
  let t : ℝ := (x - 1) / d
  have ht0 : 0 ≤ t :=
    div_nonneg (sub_nonneg.mpr hx1) (by positivity)
  have hpt : Real.rpow p t ≤ Real.rpow (chenMiddlePrimeThreshold d) t :=
    Real.rpow_le_rpow hpR.le hpB ht0
  have hthreshold : Real.rpow (chenMiddlePrimeThreshold d) t =
      Real.rpow (d - 1 : ℝ) theta := by
    rw [chenMiddlePrimeThreshold]
    calc
      Real.rpow (Real.rpow (d - 1 : ℝ) ((d : ℝ) / (d - 2))) t =
          Real.rpow (d - 1 : ℝ) (((d : ℝ) / (d - 2)) * t) :=
        (Real.rpow_mul (by linarith : (0 : ℝ) ≤ d - 1) _ _).symm
      _ = Real.rpow (d - 1 : ℝ) theta := by
        congr 1
        dsimp [theta, t]
        field_simp
  have hsmall : Real.rpow p t ≤ x := by
    rw [hthreshold] at hpt
    exact hpt.trans hbern
  have hsplit : (M₁ : ℝ) / ((r₁ : ℝ) * d) = (1 : ℝ) / d + t := by
    dsimp [t, x]
    field_simp
    ring
  rw [hsplit]
  calc
    (r₁ : ℝ) * Real.rpow p ((1 : ℝ) / d + t) =
        r₁ * (Real.rpow p ((1 : ℝ) / d) * Real.rpow p t) := by
      congr 1
      exact Real.rpow_add hpR _ _
    _ ≤ r₁ * (Real.rpow p ((1 : ℝ) / d) * x) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hpR.le _)
      · exact hrpos.le
    _ = M₁ * Real.rpow p ((1 : ℝ) / d) := by
      dsimp [x]
      field_simp

/-- ACK inequality (2.8), the trivial bound for a late stationary block. -/
theorem ack_ineq_2_8
    (hp : p.Prime) (f : Polynomial ℤ) (L : ℕ) (mu : ZMod p) :
  ‖primePowerResidueClassSum p (L + 1) hp f mu‖ ≤ (p : ℝ) ^ L := by
  simpa using ack_residueClass_trivial hp (by omega : 0 < L + 1) f mu

/-- The power of `p` dividing all derivative coefficients is at most the degree. -/
theorem _root_.Polynomial.derivativeContent_pow_le_degree
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  p ^ Polynomial.derivativeContentOrder f p ≤ d := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  have hnotC : ¬ Polynomial.C (p : ℤ) ∣ Polynomial.nonconstantPart f := by
    intro hC
    apply hprimitive
    rw [Polynomial.nonconstantContentNat, Polynomial.contentNat,
      ← Int.natCast_dvd]
    exact Polynomial.dvd_content_iff_C_dvd.mpr hC
  have hex : ∃ n : ℕ,
      ¬ (p : ℤ) ∣ (Polynomial.nonconstantPart f).coeff n := by
    rw [Polynomial.C_dvd_iff_dvd_coeff] at hnotC
    push Not at hnotC
    exact hnotC
  obtain ⟨n, hn⟩ := hex
  have hnpos : 0 < n := by
    by_contra hn0
    have : n = 0 := by omega
    subst n
    simp [Polynomial.nonconstantPart] at hn
  have hncoeff : (Polynomial.nonconstantPart f).coeff n = f.coeff n := by
    rw [Polynomial.nonconstantPart, Polynomial.coeff_sub, Polynomial.coeff_C]
    simp [hnpos.ne']
  have hpan : ¬ (p : ℤ) ∣ f.coeff n := by simpa [hncoeff] using hn
  have hfn : f.coeff n ≠ 0 := fun h => hpan (by simp [h])
  have hnd : n ≤ d := by
    rw [← hdegree]
    exact Polynomial.le_natDegree_of_ne_zero hfn
  let t := Polynomial.derivativeContentOrder f p
  have hderivCoeff : f.derivative.coeff (n - 1) =
      f.coeff n * (n : ℤ) := by
    rw [Polynomial.coeff_derivative]
    have : n - 1 + 1 = n := by omega
    rw [this]
    norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
  have hpcontent : p ^ t ∣ Polynomial.contentNat f.derivative := by
    exact (padicValNat_dvd_iff t (Polynomial.contentNat f.derivative)).2
      (Or.inr le_rfl)
  have hcontentcoeff : Polynomial.contentNat f.derivative ∣
      Int.natAbs (f.derivative.coeff (n - 1)) := by
    rw [Polynomial.contentNat, Int.natAbs_dvd_natAbs]
    exact Polynomial.content_dvd_coeff (p := f.derivative) (n - 1)
  have hpowprod : p ^ t ∣ n * Int.natAbs (f.coeff n) := by
    have h := hpcontent.trans hcontentcoeff
    rw [hderivCoeff, Int.natAbs_mul, Int.natAbs_natCast,
      Nat.mul_comm] at h
    exact h
  have hcop : Nat.Coprime (p ^ t) (Int.natAbs (f.coeff n)) := by
    apply Nat.Coprime.pow_left
    apply hp.coprime_iff_not_dvd.mpr
    intro hdvd
    apply hpan
    apply (Int.natAbs_dvd_natAbs).mp
    simpa using hdvd
  have hpown : p ^ t ∣ n := hcop.dvd_of_dvd_mul_right hpowprod
  exact (Nat.le_of_dvd hnpos hpown).trans hnd

private theorem normalizeAtPrime_natDegree
    (hp : p.Prime) (F : Polynomial ℤ) (hF : F ≠ 0) :
    (Polynomial.normalizeAtPrime p F).natDegree = F.natDegree := by
  have hspec := Polynomial.normalizeAtPrime_spec hp F hF
  have hnorm : Polynomial.normalizeAtPrime p F ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hspec
    exact hF hspec
  have hscalar :
      (((p ^ Polynomial.coefficientPadicOrder p F : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast pow_ne_zero (Polynomial.coefficientPadicOrder p F) hp.ne_zero
  have hdegree := congrArg Polynomial.natDegree hspec
  rw [Polynomial.natDegree_C_mul_of_mul_ne_zero
    (mul_ne_zero hscalar (Polynomial.leadingCoeff_ne_zero.mpr hnorm))] at hdegree
  exact hdegree.symm

/-- The normalized derivative's root mass modulo `p` is bounded by `d - 1`. -/
theorem _root_.Polynomial.smallPrimeStationaryMass_le_degree
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  Polynomial.smallPrimeStationaryMass f p ≤ d - 1 := by
  have hdpos : 0 < d := by
    have horder := Polynomial.ack_lemma_2_3 hp f hdegree.le hprimitive 0
    omega
  have hfdeg : 0 < f.natDegree := hdegree.symm ▸ hdpos
  have hderiv : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr hfdeg.ne'
  calc
    Polynomial.smallPrimeStationaryMass f p ≤
        (Polynomial.modPrime p
          (Polynomial.normalizedDerivative f p)).natDegree :=
      rootMassModPrime_le_natDegree p _
    _ ≤ (Polynomial.normalizedDerivative f p).natDegree :=
      Polynomial.natDegree_map_le
    _ = f.derivative.natDegree := by
      exact normalizeAtPrime_natDegree hp f.derivative hderiv
    _ = f.natDegree - 1 := Polynomial.natDegree_derivative f
    _ = d - 1 := by rw [hdegree]

private theorem modPrime_ne_zero_of_content_primitive
    [Fact p.Prime] (F : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.contentNat F) :
    Polynomial.modPrime p F ≠ 0 := by
  intro hzero
  apply hprimitive
  rw [Polynomial.contentNat, ← Int.natCast_dvd]
  apply Polynomial.dvd_content_iff_C_dvd.mpr
  apply (Polynomial.C_dvd_iff_dvd_coeff (p : ℤ) _).mpr
  intro n
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hn := congrArg (fun G : Polynomial (ZMod p) ↦ G.coeff n) hzero
  simpa [Polynomial.modPrime] using hn

private theorem chen_normalizeAtPrime_C_primePow_mul
    (hp : p.Prime) (F : Polynomial ℤ) (hF : F ≠ 0) (k : ℕ) :
    Polynomial.normalizeAtPrime p (Polynomial.C ((p : ℤ) ^ k) * F) =
      Polynomial.normalizeAtPrime p F := by
  let _ : Fact p.Prime := ⟨hp⟩
  let G := Polynomial.C ((p : ℤ) ^ k) * F
  have hscalar : (p : ℤ) ^ k ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hG : G ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hscalar) hF
  have horder : Polynomial.coefficientPadicOrder p G =
      k + Polynomial.coefficientPadicOrder p F := by
    dsimp [G]
    rw [Polynomial.coefficientPadicOrder, chen_contentNat_C_mul]
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero)
      (chen_contentNat_ne_zero F hF), padicValNat.prime_pow]
    rfl
  have hspecG := Polynomial.normalizeAtPrime_spec hp G hG
  have hspecF := Polynomial.normalizeAtPrime_spec hp F hF
  have hcommon : G = Polynomial.C ((p : ℤ) ^
      (k + Polynomial.coefficientPadicOrder p F)) *
      Polynomial.normalizeAtPrime p F := by
    calc
      G = Polynomial.C ((p : ℤ) ^ k) * F := rfl
      _ = Polynomial.C ((p : ℤ) ^ k) *
          (Polynomial.C ((p : ℤ) ^ Polynomial.coefficientPadicOrder p F) *
            Polynomial.normalizeAtPrime p F) := congrArg _ hspecF
      _ = _ := by
        simp only [Polynomial.C_mul, pow_add]
        ring
  apply Polynomial.ext
  intro n
  have hnG := congrArg (fun H : Polynomial ℤ ↦ H.coeff n) hspecG
  have hnCommon := congrArg (fun H : Polynomial ℤ ↦ H.coeff n) hcommon
  rw [horder] at hnG
  simp only [Polynomial.coeff_C_mul, Nat.cast_pow] at hnG hnCommon
  have hpow : (p : ℤ) ^ (k + Polynomial.coefficientPadicOrder p F) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  apply (Int.mul_eq_mul_left_iff hpow).mp
  rw [← hnG, ← hnCommon]

private theorem chen_stationaryNormalize_normalizedDerivative_eq
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) :
    Polynomial.normalizedDerivative
        (Polynomial.stationaryNormalize f p mu.val) p =
      Polynomial.normalizedPrimeScaleTranslate
        (Polynomial.normalizedDerivative f p) p mu.val := by
  let t := Polynomial.derivativeContentOrder f p
  let D := Polynomial.normalizedDerivative f p
  let A := Polynomial.stationaryTranslate f p mu.val
  let B := Polynomial.stationaryNormalize f p mu.val
  let Pf := Polynomial.primeScaleTranslate f.derivative p mu.val
  let PD := Polynomial.primeScaleTranslate D p mu.val
  let u := Polynomial.stationaryOrder f p mu.val
  have hdpos : 0 < d := by
    have horder := Polynomial.ack_lemma_2_3 hp f hdegree.le hprimitive mu.val
    omega
  have hfderiv : f.derivative ≠ 0 := by
    apply Polynomial.derivative_ne_zero.mpr
    rw [hdegree]
    omega
  have hchild := Polynomial.stationaryChildInvariant hp f hdegree hdpos
    hprimitive mu.val
  have hAne : A ≠ 0 := hchild.translate_ne_zero
  have hBdegree : B.natDegree = d := hchild.natDegree_eq
  have hBderiv : B.derivative ≠ 0 := by
    apply Polynomial.derivative_ne_zero.mpr
    rw [hBdegree]
    omega
  have hu1 : 1 ≤ u :=
    (Polynomial.ack_lemma_2_3 hp f hdegree.le hprimitive mu.val).1
  have hspecD := Polynomial.normalizeAtPrime_spec hp f.derivative hfderiv
  have hDne : D ≠ 0 := by
    intro hzero
    rw [show Polynomial.normalizeAtPrime p f.derivative = D from rfl,
      hzero, mul_zero] at hspecD
    exact hfderiv hspecD
  have hspecAB : A = Polynomial.C ((p : ℤ) ^ u) * B := by
    have hspecA := Polynomial.normalizeAtPrime_spec hp A hAne
    simpa [A, B, u, Polynomial.stationaryNormalize,
      Polynomial.stationaryOrder, Nat.cast_pow] using hspecA
  have hAderiv : A.derivative = Polynomial.C (p : ℤ) * Pf := by
    dsimp [A, Pf]
    simp only [Polynomial.stationaryTranslate, map_sub, Polynomial.derivative_C,
      sub_zero, Polynomial.primeScaleTranslate, Polynomial.derivative_comp,
      Polynomial.derivative_add, Polynomial.derivative_C_mul_X,
      Polynomial.derivative_C, add_zero]
  have hspecDeriv := congrArg Polynomial.derivative hspecAB
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul,
    zero_add] at hspecDeriv
  have hPfB : Pf = Polynomial.C ((p : ℤ) ^ (u - 1)) * B.derivative := by
    apply Polynomial.ext
    intro n
    have hnA := congrArg (fun F : Polynomial ℤ ↦ F.coeff n) hAderiv
    have hnSpec := congrArg (fun F : Polynomial ℤ ↦ F.coeff n) hspecDeriv
    simp only [Polynomial.coeff_C_mul] at hnA hnSpec ⊢
    have heq : (p : ℤ) ^ u * B.derivative.coeff n =
        (p : ℤ) * Pf.coeff n := by rw [← hnA, ← hnSpec]
    have hu : u - 1 + 1 = u := by omega
    rw [← hu, pow_succ] at heq
    apply (Int.mul_eq_mul_left_iff
      (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)).mp
    simpa [mul_assoc, mul_comm, mul_left_comm] using heq.symm
  have hPfD : Pf = Polynomial.C ((p : ℤ) ^ t) * PD := by
    have hspecDt : f.derivative = Polynomial.C ((p : ℤ) ^ t) * D := by
      simpa [t, D, Polynomial.normalizedDerivative,
        Polynomial.derivativeContentOrder, Nat.cast_pow] using hspecD
    dsimp [Pf, PD]
    rw [hspecDt]
    simp [Polynomial.primeScaleTranslate]
  have hPfne : Pf ≠ 0 := by
    rw [hPfB]
    exact mul_ne_zero
      (Polynomial.C_ne_zero.mpr
        (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))) hBderiv
  have hPDne : PD ≠ 0 := by
    intro hzero
    apply hPfne
    rw [hPfD, hzero, mul_zero]
  have hnormPfB : Polynomial.normalizeAtPrime p Pf =
      Polynomial.normalizeAtPrime p B.derivative := by
    rw [hPfB, chen_normalizeAtPrime_C_primePow_mul hp B.derivative hBderiv]
  have hnormPfD : Polynomial.normalizeAtPrime p Pf =
      Polynomial.normalizeAtPrime p PD := by
    rw [hPfD, chen_normalizeAtPrime_C_primePow_mul hp PD hPDne]
  change Polynomial.normalizeAtPrime p B.derivative =
    Polynomial.normalizeAtPrime p PD
  exact hnormPfB.symm.trans hnormPfD

/-- Bound a small-prime stationary child's mass by the corresponding normalized
derivative-root multiplicity. -/
theorem _root_.Polynomial.stationaryNormalize_smallPrimeStationaryMass_le
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (hmu : mu ∈ Polynomial.smallPrimeStationaryRoots f p) :
  Polynomial.smallPrimeStationaryMass
      (Polynomial.stationaryNormalize f p mu.val) p ≤
    (Polynomial.modPrime p
      (Polynomial.normalizedDerivative f p)).rootMultiplicity mu := by
  let D := Polynomial.normalizedDerivative f p
  have hfpos : 0 < f.natDegree := by
    have horder := Polynomial.ack_lemma_2_3 hp f le_rfl hprimitive mu.val
    omega
  have hfderiv : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr hfpos.ne'
  have hDprimitive : ¬ p ∣ Polynomial.contentNat D := by
    exact Polynomial.normalizeAtPrime_primitive hp f.derivative hfderiv
  have hDmod : Polynomial.modPrime p D ≠ 0 :=
    modPrime_ne_zero_of_content_primitive D hDprimitive
  have hmuRoot : (Polynomial.modPrime p D).IsRoot mu := by
    simpa [D, Polynomial.smallPrimeStationaryRoots,
      Polynomial.rootsModPrime] using hmu
  change Polynomial.rootMassModPrime p
      (Polynomial.normalizedDerivative
        (Polynomial.stationaryNormalize f p mu.val) p) ≤ _
  rw [chen_stationaryNormalize_normalizedDerivative_eq hp f hdegree hprimitive mu]
  exact Polynomial.ack_lemma_2_2_rootMass hp D hDmod mu hmuRoot

private theorem polynomialEval_map_intCast (q : ℕ) [NeZero q]
    (f : Polynomial ℤ) (n : ℤ) :
    Polynomial.eval (n : ZMod q) (f.map (Int.castRingHom _)) =
      ((f.eval n : ℤ) : ZMod q) := by
  simp

private theorem chen_stdAddChar_mul_modulus
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

private theorem chen_stdAddChar_mul_modulus_eq
    (q m n : ℕ) [NeZero q] [NeZero m] [NeZero n]
    (hq : q = m * n) (t : ℤ) :
    ZMod.stdAddChar ((n : ℤ) * t : ZMod q) =
      ZMod.stdAddChar (t : ZMod m) := by
  subst q
  exact chen_stdAddChar_mul_modulus m n t

private theorem stdAddChar_primePow_topDigit
    (hp : p.Prime) (ha : 0 < a) (t : ℤ) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
    ZMod.stdAddChar (((p ^ (a - 1) : ℕ) : ℤ) * t : ZMod (p ^ a)) =
      ZMod.stdAddChar (t : ZMod p) := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let _ : NeZero (p ^ (a - 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpow : p ^ a = p * p ^ (a - 1) := by
    calc
      p ^ a = p ^ (1 + (a - 1)) := by congr 1; omega
      _ = p * p ^ (a - 1) := by rw [pow_add, pow_one]
  exact chen_stdAddChar_mul_modulus_eq (p ^ a) p (p ^ (a - 1)) hpow t

/-- ACK equation (2.3): nonstationary residue classes contribute zero. -/
theorem ack_eq_2_3_vanish
    (hp : p.Prime) (ha : 2 ≤ a) (f : Polynomial ℤ) (v : ZMod p)
    (hv : ¬ (Polynomial.modPrime p f.derivative).IsRoot v) :
  primePowerResidueClassSum p a hp f v = 0 := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let H : ZMod (p ^ a) := ((p ^ (a - 1) : ℕ) : ZMod (p ^ a))
  let P : Polynomial (ZMod (p ^ a)) := f.map (Int.castRingHom _)
  let Pbar : Polynomial (ZMod p) := Polynomial.modPrime p f.derivative
  have hHsq : H ^ 2 = 0 := by
    have hdvd : p ^ a ∣ (p ^ (a - 1)) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow p (by omega : a ≤ (a - 1) * 2)
    rcases hdvd with ⟨e, he⟩
    dsimp [H]
    calc
      (((p ^ (a - 1) : ℕ) : ZMod (p ^ a))) ^ 2 =
          (((p ^ (a - 1)) ^ 2 : ℕ) : ZMod (p ^ a)) := by norm_num
      _ = 0 := by rw [he, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hpdiv : p ∣ p ^ a := dvd_pow_self p (by omega)
  let phi : ZMod (p ^ a) →+* ZMod p := ZMod.castHom hpdiv (ZMod p)
  have hphi_val (x : ZMod (p ^ a)) : phi x = (x.val : ZMod p) := by
    simp [phi]
  have hphiH : phi H = 0 := by
    dsimp [H]
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_pow_self p (by omega : a - 1 ≠ 0)
  have hclassShift (x : ZMod (p ^ a)) :
      (((x + H).val : ℕ) : ZMod p) = ((x.val : ℕ) : ZMod p) := by
    rw [← hphi_val, ← hphi_val, map_add, hphiH, add_zero]
  have hEvalShift (x : ZMod (p ^ a)) :
      Polynomial.eval (x + H) P =
        Polynomial.eval x P + Polynomial.eval x P.derivative * H := by
    exact Polynomial.eval_add_of_sq_eq_zero P x H hHsq
  have hderivEval (x : ZMod (p ^ a)) :
      Polynomial.eval x P.derivative =
        ((f.derivative.eval (x.val : ℤ) : ℤ) : ZMod (p ^ a)) := by
    have hx : ((x.val : ℕ) : ZMod (p ^ a)) = x := x.natCast_zmod_val
    dsimp [P]
    rw [Polynomial.derivative_map]
    conv_lhs => rw [← hx]
    simpa using polynomialEval_map_intCast (p ^ a) f.derivative (x.val : ℤ)
  let c : ZMod p := Polynomial.eval v Pbar
  have hcne : c ≠ 0 := hv
  have hchi : ZMod.stdAddChar c ≠ 1 := by
    intro h
    apply hcne
    apply ZMod.injective_stdAddChar
    simpa using h
  have hderivMod (x : ZMod (p ^ a))
      (hxv : ((x.val : ℕ) : ZMod p) = v) :
      ((f.derivative.eval (x.val : ℤ) : ℤ) : ZMod p) = c := by
    dsimp [c, Pbar, Polynomial.modPrime]
    rw [← hxv]
    simpa using (polynomialEval_map_intCast p f.derivative (x.val : ℤ)).symm
  have hcharLinear (x : ZMod (p ^ a))
      (hxv : ((x.val : ℕ) : ZMod p) = v) :
      ZMod.stdAddChar (Polynomial.eval x P.derivative * H) =
        ZMod.stdAddChar c := by
    rw [hderivEval]
    have htop := stdAddChar_primePow_topDigit hp (by omega : 0 < a)
      (f.derivative.eval (x.val : ℤ))
    have harg :
        ((f.derivative.eval (x.val : ℤ) : ℤ) : ZMod (p ^ a)) * H =
          (((p ^ (a - 1) : ℕ) : ℤ) * f.derivative.eval (x.val : ℤ) :
            ZMod (p ^ a)) := by
      dsimp [H]
      norm_num
      ring
    rw [harg, htop, hderivMod x hxv]
  let F : ZMod (p ^ a) → ℂ := fun x ↦
    if (x.val : ZMod p) = v then ZMod.stdAddChar (Polynomial.eval x P) else 0
  have hshiftTerm (x : ZMod (p ^ a)) : F (x + H) = F x * ZMod.stdAddChar c := by
    dsimp [F]
    rw [hclassShift]
    by_cases hxv : ((x.val : ℕ) : ZMod p) = v
    · rw [if_pos hxv, if_pos hxv, hEvalShift, AddChar.map_add_eq_mul,
        hcharLinear x hxv]
    · rw [if_neg hxv, if_neg hxv, zero_mul]
  rw [primePowerResidueClassSum]
  change (∑ x : ZMod (p ^ a), F x) = 0
  have hshift :
      (∑ x : ZMod (p ^ a), F x) =
        (∑ x : ZMod (p ^ a), F x) * ZMod.stdAddChar c := by
    calc
      _ = ∑ x : ZMod (p ^ a), F (x + H) := by
        exact (Fintype.sum_bijective (fun x : ZMod (p ^ a) ↦ x + H)
          (AddGroup.addRight_bijective H) _ _ (fun _ ↦ rfl)).symm
      _ = _ := by simp_rw [hshiftTerm, Finset.sum_mul]
  have hfactor :
      (1 - ZMod.stdAddChar c) * (∑ x : ZMod (p ^ a), F x) = 0 := by
    linear_combination hshift
  exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hchi.symm)

private theorem chen_finEquiv_apply_eq_natCast
    (q : ℕ) [NeZero q] (i : Fin q) :
    ZMod.finEquiv q i = (i.val : ZMod q) := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q => exact (Fin.cast_val_eq_self i).symm

private theorem chen_finEquiv_symm_val
    (q : ℕ) [NeZero q] (x : ZMod q) :
    ((ZMod.finEquiv q).symm x).val = x.val := by
  have h := congrArg ZMod.val
    (chen_finEquiv_apply_eq_natCast q ((ZMod.finEquiv q).symm x))
  rw [RingEquiv.apply_symm_apply] at h
  rw [ZMod.val_natCast,
    Nat.mod_eq_of_lt ((ZMod.finEquiv q).symm x).isLt] at h
  exact h.symm

private theorem chen_sum_zmod_mul
    (m n : ℕ) [NeZero m] [NeZero n]
    (F : ZMod (m * n) → ℂ) :
    ∑ x : ZMod (m * n), F x =
      ∑ y : ZMod m, ∑ z : ZMod n,
        F ((z.val + n * y.val : ℕ) : ZMod (m * n)) := by
  let e : ZMod m × ZMod n ≃ ZMod (m * n) :=
    (Equiv.prodCongr (ZMod.finEquiv m).toEquiv.symm
      (ZMod.finEquiv n).toEquiv.symm).trans
      (finProdFinEquiv.trans (ZMod.finEquiv (m * n)).toEquiv)
  rw [← e.sum_comp F, Fintype.sum_prod_type]
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
  rw [chen_finEquiv_apply_eq_natCast]
  congr 1
  simp [finProdFinEquiv, chen_finEquiv_symm_val]

private theorem chen_sum_zmod_eq_mul
    (q m n : ℕ) [NeZero q] [NeZero m] [NeZero n]
    (hq : q = m * n) (F : ZMod q → ℂ) :
    ∑ x : ZMod q, F x =
      ∑ y : ZMod m, ∑ z : ZMod n,
        F ((z.val + n * y.val : ℕ) : ZMod q) := by
  subst q
  exact chen_sum_zmod_mul m n F

/-- ACK equation (2.4): a stationary residue-class sum is `p` times its short sum. -/
theorem ack_eq_2_4
    (hp : p.Prime) (ha : 2 ≤ a) (f : Polynomial ℤ) (mu : ZMod p)
    (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  primePowerResidueClassSum p a hp f mu =
    (p : ℂ) * primePowerStationaryShortSum p a hp f mu := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let _ : NeZero (p ^ (a - 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let _ : NeZero (p ^ (a - 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let P : Polynomial (ZMod (p ^ a)) := f.map (Int.castRingHom _)
  let Pbar : Polynomial (ZMod p) := Polynomial.modPrime p f.derivative
  let H : ZMod (p ^ a) := ((p ^ (a - 1) : ℕ) : ZMod (p ^ a))
  let G : ZMod (p ^ a) → ℂ := fun x ↦
    ZMod.stdAddChar (Polynomial.eval x P)
  have hqa : p ^ a = p ^ (a - 1) * p := by
    calc
      p ^ a = p ^ ((a - 1) + 1) := by congr 1; omega
      _ = p ^ (a - 1) * p := by rw [pow_succ]
  have hqa1 : p ^ (a - 1) = p * p ^ (a - 2) := by
    calc
      p ^ (a - 1) = p ^ (1 + (a - 2)) := by congr 1; omega
      _ = p * p ^ (a - 2) := by rw [pow_add, pow_one]
  have hpdiv : p ∣ p ^ a := dvd_pow_self p (by omega : a ≠ 0)
  let phi : ZMod (p ^ a) →+* ZMod p := ZMod.castHom hpdiv (ZMod p)
  have hphi_val (x : ZMod (p ^ a)) : phi x = (x.val : ZMod p) := by
    simp [phi]
  have hclass (y : ZMod (p ^ (a - 1))) (z : ZMod p) :
      ((((z.val + p * y.val : ℕ) : ZMod (p ^ a)).val : ℕ) : ZMod p) = z := by
    rw [← hphi_val]
    rw [map_natCast]
    push_cast
    rw [ZMod.natCast_zmod_val]
    simp
  have hfiber : primePowerResidueClassSum p a hp f mu =
      ∑ y : ZMod (p ^ (a - 1)), G ((mu.val + p * y.val : ℕ) : ZMod (p ^ a)) := by
    rw [primePowerResidueClassSum]
    change (∑ x : ZMod (p ^ a),
      if (x.val : ZMod p) = mu then G x else 0) = _
    rw [chen_sum_zmod_eq_mul (p ^ a) (p ^ (a - 1)) p hqa]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single mu]
    · rw [if_pos (hclass y mu)]
    · intro z _ hzne
      rw [if_neg (by rw [hclass y z]; exact hzne)]
    · simp
  have hHsq : H ^ 2 = 0 := by
    have hdvd : p ^ a ∣ (p ^ (a - 1)) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow p (by omega : a ≤ (a - 1) * 2)
    rcases hdvd with ⟨e, he⟩
    dsimp [H]
    calc
      (((p ^ (a - 1) : ℕ) : ZMod (p ^ a))) ^ 2 =
          (((p ^ (a - 1)) ^ 2 : ℕ) : ZMod (p ^ a)) := by norm_num
      _ = 0 := by rw [he, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hderivEval (x : ZMod (p ^ a)) :
      Polynomial.eval x P.derivative =
        ((f.derivative.eval (x.val : ℤ) : ℤ) : ZMod (p ^ a)) := by
    have hx : ((x.val : ℕ) : ZMod (p ^ a)) = x := x.natCast_zmod_val
    dsimp [P]
    rw [Polynomial.derivative_map]
    conv_lhs => rw [← hx]
    simpa using polynomialEval_map_intCast (p ^ a) f.derivative (x.val : ℤ)
  have hderivModZero (x : ZMod (p ^ a))
      (hxmu : ((x.val : ℕ) : ZMod p) = mu) :
      ((f.derivative.eval (x.val : ℤ) : ℤ) : ZMod p) = 0 := by
    have hmu0 : Polynomial.eval mu Pbar = 0 := hmu
    dsimp [Pbar, Polynomial.modPrime] at hmu0
    rw [← hxmu] at hmu0
    have heval := polynomialEval_map_intCast p f.derivative (x.val : ℤ)
    have hxcast : ((x.val : ℤ) : ZMod p) = ((x.val : ℕ) : ZMod p) := by
      norm_num
    rw [hxcast] at heval
    rw [heval] at hmu0
    exact hmu0
  have hderivHZero (x : ZMod (p ^ a))
      (hxmu : ((x.val : ℕ) : ZMod p) = mu) :
      Polynomial.eval x P.derivative * H = 0 := by
    rw [hderivEval]
    have hdvd : (p : ℤ) ∣ f.derivative.eval (x.val : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hderivModZero x hxmu
    rcases hdvd with ⟨t, ht⟩
    rw [ht]
    dsimp [H]
    have hcast :
        (((p : ℤ) * t : ℤ) : ZMod (p ^ a)) *
            ((p ^ (a - 1) : ℕ) : ZMod (p ^ a)) =
          ((p ^ a : ℕ) : ZMod (p ^ a)) * (t : ZMod (p ^ a)) := by
      rw [hqa]
      push_cast
      ring
    rw [hcast, ZMod.natCast_self, zero_mul]
  have hphaseShift (x : ZMod (p ^ a))
      (hxmu : ((x.val : ℕ) : ZMod p) = mu) (k : ZMod (p ^ a)) :
      G (x + k * H) = G x := by
    have hsq : (k * H) ^ 2 = 0 := by
      rw [mul_pow, hHsq, mul_zero]
    dsimp [G]
    rw [Polynomial.eval_add_of_sq_eq_zero P x (k * H) hsq]
    have hzero : Polynomial.eval x P.derivative * (k * H) = 0 := by
      calc
        Polynomial.eval x P.derivative * (k * H) =
            k * (Polynomial.eval x P.derivative * H) := by ring
        _ = 0 := by rw [hderivHZero x hxmu, mul_zero]
    rw [hzero, add_zero]
  have hrepetition (b : ZMod p) (y : ZMod (p ^ (a - 2))) :
      G (((mu.val + p * (y.val + p ^ (a - 2) * b.val) : ℕ) :
          ZMod (p ^ a))) =
        G ((mu.val + p * y.val : ℕ) : ZMod (p ^ a)) := by
    let x : ZMod (p ^ a) := ((mu.val + p * y.val : ℕ) : ZMod (p ^ a))
    have hxmu : ((x.val : ℕ) : ZMod p) = mu := by
      rw [← hphi_val]
      dsimp [x]
      rw [map_natCast]
      push_cast
      rw [ZMod.natCast_zmod_val]
      simp
    have harg :
        ((mu.val + p * (y.val + p ^ (a - 2) * b.val) : ℕ) :
            ZMod (p ^ a)) = x + (b.val : ZMod (p ^ a)) * H := by
      dsimp [x, H]
      rw [hqa1]
      push_cast
      ring
    rw [harg, hphaseShift x hxmu]
  have hrepetitionCast (b : ZMod p) (y : ZMod (p ^ (a - 2))) :
      G ((mu.val + p *
          (((y.val + p ^ (a - 2) * b.val : ℕ) :
            ZMod (p ^ (a - 1))).val) : ℕ) : ZMod (p ^ a)) =
        G ((mu.val + p * y.val : ℕ) : ZMod (p ^ a)) := by
    have hlt : y.val + p ^ (a - 2) * b.val < p ^ (a - 1) := by
      calc
        y.val + p ^ (a - 2) * b.val <
            p ^ (a - 2) + p ^ (a - 2) * b.val :=
          Nat.add_lt_add_right y.val_lt _
        _ = p ^ (a - 2) * (b.val + 1) := by ring
        _ ≤ p ^ (a - 2) * p :=
          Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr b.val_lt)
        _ = p ^ (a - 1) := by rw [hqa1, mul_comm]
    rw [ZMod.val_natCast_of_lt hlt]
    exact hrepetition b y
  rw [hfiber, primePowerStationaryShortSum]
  change (∑ y : ZMod (p ^ (a - 1)),
      G ((mu.val + p * y.val : ℕ) : ZMod (p ^ a))) =
    (p : ℂ) * ∑ y : ZMod (p ^ (a - 2)),
      G ((mu.val + p * y.val : ℕ) : ZMod (p ^ a))
  rw [chen_sum_zmod_eq_mul (p ^ (a - 1)) p (p ^ (a - 2)) hqa1]
  simp_rw [hrepetitionCast]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

/-- ACK equation (2.5): exact descent from a stationary class to its normalized child. -/
theorem ack_eq_2_5
    (hp : p.Prime) (ha : 2 ≤ a) (f : Polynomial ℤ) (mu : ZMod p)
    (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu)
    (htranslate : Polynomial.stationaryTranslate f p mu.val ≠ 0)
    (hsigma : Polynomial.stationaryOrder f p mu.val < a) :
  ‖primePowerResidueClassSum p a hp f mu‖ =
    (p : ℝ) ^ (Polynomial.stationaryOrder f p mu.val - 1) *
      ‖polynomialCompleteSum
        (p ^ (a - Polynomial.stationaryOrder f p mu.val))
        (pow_pos hp.pos _) (Polynomial.stationaryNormalize f p mu.val)‖ := by
  let sigma := Polynomial.stationaryOrder f p mu.val
  let g := Polynomial.stationaryNormalize f p mu.val
  let q := p ^ a
  let m := p ^ (a - sigma)
  let r := p ^ (sigma - 2)
  let qs := p ^ (a - 2)
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : NeZero q := ⟨by dsimp [q]; exact pow_ne_zero _ hp.ne_zero⟩
  let _ : NeZero m := ⟨by dsimp [m]; exact pow_ne_zero _ hp.ne_zero⟩
  let _ : NeZero r := ⟨by dsimp [r]; exact pow_ne_zero _ hp.ne_zero⟩
  let _ : NeZero qs := ⟨by dsimp [qs]; exact pow_ne_zero _ hp.ne_zero⟩
  have hsigma2 : 2 ≤ sigma := by
    dsimp [sigma]
    exact Polynomial.stationaryOrder_two_le_of_isRoot hp f mu htranslate hmu
  have hsigma_le : sigma ≤ a := hsigma.le
  have hq : q = m * p ^ sigma := by
    dsimp [q, m]
    rw [← pow_add]
    congr 1
    omega
  have hqs : qs = r * m := by
    dsimp [qs, r, m]
    rw [← pow_add]
    congr 1
    omega
  have hscalar : Polynomial.stationaryTranslate f p mu.val =
      Polynomial.C (((p ^ sigma : ℕ) : ℤ)) * g := by
    dsimp [sigma, g]
    exact Polynomial.normalizeAtPrime_spec hp _ htranslate
  have hstationaryEval (y : ℤ) :
      f.eval (mu.val + (p : ℤ) * y) =
        f.eval (mu.val : ℤ) +
          ((p ^ sigma : ℕ) : ℤ) * g.eval y := by
    have heval := congrArg (fun F : Polynomial ℤ ↦ F.eval y) hscalar
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at heval
    dsimp [Polynomial.stationaryTranslate,
      Polynomial.primeScaleTranslate] at heval
    simp only [Polynomial.eval_sub, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X] at heval
    rw [add_comm (mu.val : ℤ)]
    simpa [add_comm] using (sub_eq_iff_eq_add.mp heval)
  let cphase : ℂ :=
    ZMod.stdAddChar ((f.eval (mu.val : ℤ) : ℤ) : ZMod q)
  let childPhase : ZMod qs → ℂ := fun y ↦
    ZMod.stdAddChar
      (Polynomial.eval ((y.val : ℕ) : ZMod m)
        (g.map (Int.castRingHom _)))
  have hphase (y : ZMod qs) :
      ZMod.stdAddChar
          (Polynomial.eval ((mu.val + p * y.val : ℕ) : ZMod q)
            (f.map (Int.castRingHom _))) =
        cphase * childPhase y := by
    have hevalf := polynomialEval_map_intCast q f
      (mu.val + (p : ℤ) * y.val)
    have hpoint :
        ((mu.val + (p : ℤ) * y.val : ℤ) : ZMod q) =
          ((mu.val + p * y.val : ℕ) : ZMod q) := by
      norm_num
    rw [hpoint] at hevalf
    have harg :
        Polynomial.eval ((mu.val + p * y.val : ℕ) : ZMod q)
            (f.map (Int.castRingHom _)) =
          ((f.eval (mu.val : ℤ) : ℤ) : ZMod q) +
            (((p ^ sigma : ℕ) : ℤ) * g.eval (y.val : ℤ) :
              ZMod q) := by
      rw [hevalf]
      rw [hstationaryEval]
      norm_num
    rw [harg, AddChar.map_add_eq_mul]
    congr 1
    dsimp [childPhase]
    have hscale := chen_stdAddChar_mul_modulus_eq q m (p ^ sigma) hq
      (g.eval (y.val : ℤ))
    have hchild := polynomialEval_map_intCast m g (y.val : ℤ)
    have hchildPoint :
        ((y.val : ℤ) : ZMod m) = ((y.val : ℕ) : ZMod m) := by
      norm_num
    rw [hchildPoint] at hchild
    rw [hchild]
    exact hscale
  have hmdiv : m ∣ qs := by
    rw [hqs]
    exact dvd_mul_left m r
  let psi : ZMod qs →+* ZMod m := ZMod.castHom hmdiv (ZMod m)
  have hpsi_val (x : ZMod qs) : psi x = (x.val : ZMod m) := by
    simp [psi]
  have hchildRepeat (b : ZMod r) (z : ZMod m) :
      childPhase ((z.val + m * b.val : ℕ) : ZMod qs) =
        ZMod.stdAddChar (Polynomial.eval z (g.map (Int.castRingHom _))) := by
    dsimp [childPhase]
    have hzclass :
        (((((z.val + m * b.val : ℕ) : ZMod qs).val : ℕ) : ZMod m)) = z := by
      rw [← hpsi_val]
      rw [map_natCast]
      push_cast
      rw [ZMod.natCast_zmod_val]
      simp
    rw [hzclass]
  have hchildSum :
      (∑ y : ZMod qs, childPhase y) =
        (r : ℂ) *
          polynomialCompleteSum m (by dsimp [m]; exact pow_pos hp.pos _) g := by
    rw [chen_sum_zmod_eq_mul qs r m hqs]
    simp_rw [hchildRepeat]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rfl
  have hshort : primePowerStationaryShortSum p a hp f mu =
      cphase * ((r : ℂ) *
        polynomialCompleteSum m (by dsimp [m]; exact pow_pos hp.pos _) g) := by
    rw [primePowerStationaryShortSum]
    change (∑ y : ZMod qs,
      ZMod.stdAddChar
        (Polynomial.eval ((mu.val + p * y.val : ℕ) : ZMod q)
          (f.map (Int.castRingHom _)))) = _
    simp_rw [hphase]
    rw [← Finset.mul_sum, hchildSum]
  have hcphase : ‖cphase‖ = 1 := by
    simp [cphase, ZMod.stdAddChar_apply, Circle.norm_coe]
  have hpr : (p : ℝ) * (r : ℝ) = (p : ℝ) ^ (sigma - 1) := by
    dsimp [r]
    rw [← Nat.cast_pow]
    push_cast
    rw [← pow_succ']
    congr 1
    omega
  rw [ack_eq_2_4 hp ha f mu hmu, hshort, norm_mul, norm_mul,
    norm_mul, hcphase, one_mul]
  norm_num
  calc
    (p : ℝ) * ((r : ℝ) *
        ‖polynomialCompleteSum m (by dsimp [m]; exact pow_pos hp.pos _) g‖) =
      ((p : ℝ) * (r : ℝ)) *
        ‖polynomialCompleteSum m (by dsimp [m]; exact pow_pos hp.pos _) g‖ := by
        rw [mul_assoc]
    _ = (p : ℝ) ^ (sigma - 1) *
        ‖polynomialCompleteSum m (by dsimp [m]; exact pow_pos hp.pos _) g‖ := by
      rw [hpr]
    _ = _ := by simp [sigma, m, g]

/-- ACK inequality (2.7), obtained for an early stationary class from a child
induction bound. -/
theorem ack_ineq_2_7_of_inductionBound
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (L : ℕ) (hL : 2 ≤ L) (mu : ZMod p)
    (hmu : mu ∈ Polynomial.earlyDerivativeRoots f p L)
    (hrec :
      ‖polynomialCompleteSum
        (p ^ (L + 1 - Polynomial.stationaryOrder f p mu.val))
        (pow_pos hp.pos _) (Polynomial.stationaryNormalize f p mu.val)‖ ≤
      ((Polynomial.modPrime p f.derivative).rootMultiplicity mu : ℝ) *
        Real.rpow p
          (-1 + (3 : ℝ) / d +
            (L + 1 - Polynomial.stationaryOrder f p mu.val : ℝ) *
              (1 - (1 : ℝ) / d))) :
  ‖primePowerResidueClassSum p (L + 1) hp f mu‖ ≤
    ((Polynomial.modPrime p f.derivative).rootMultiplicity mu : ℝ) *
      Real.rpow p
        (-2 +
          ((Polynomial.modPrime p f.derivative).rootMultiplicity mu + 1 : ℝ) / d +
          (3 : ℝ) / d + (L + 1 : ℝ) * (1 - (1 : ℝ) / d)) := by
  let sigma := Polynomial.stationaryOrder f p mu.val
  let M := (Polynomial.modPrime p f.derivative).rootMultiplicity mu
  have hmem := Finset.mem_filter.mp hmu
  have hroot : (Polynomial.modPrime p f.derivative).IsRoot mu := by
    simpa [Polynomial.derivativeRoots, Polynomial.rootsModPrime] using hmem.1
  have hsigmaL : sigma < L := by
    simpa [sigma] using hmem.2
  have hchild := Polynomial.stationaryChildInvariant hp f hdegree
    (by omega : 0 < d) hprimitive mu.val
  have hsigma2 : 2 ≤ sigma := by
    dsimp [sigma]
    exact Polynomial.stationaryOrder_two_le_of_isRoot hp f mu
      hchild.translate_ne_zero hroot
  have hsigmaM : sigma ≤ M + 1 := by
    dsimp [sigma, M]
    exact Polynomial.stationaryOrder_le_rootMultiplicity_succ hp f hdegree
      hdp hprimitive mu hroot
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  let Echild : ℝ :=
    -1 + (3 : ℝ) / d + ((L + 1 : ℝ) - sigma) * (1 - (1 : ℝ) / d)
  let Eout : ℝ :=
    -2 + ((M + 1 : ℕ) : ℝ) / d + (3 : ℝ) / d +
      (L + 1 : ℝ) * (1 - (1 : ℝ) / d)
  have hExp : ((sigma - 1 : ℕ) : ℝ) + Echild ≤ Eout := by
    have hsigmaCast : ((sigma - 1 : ℕ) : ℝ) = (sigma : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ sigma)]
      norm_num
    have hMCast : (sigma : ℝ) ≤ (M + 1 : ℕ) := by
      exact_mod_cast hsigmaM
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    dsimp [Echild, Eout]
    rw [hsigmaCast]
    field_simp [hd0]
    nlinarith
  rw [ack_eq_2_5 hp (by omega : 2 ≤ L + 1) f mu hroot
    hchild.translate_ne_zero (by simpa [sigma] using hsigmaL.trans_le (Nat.le_succ L))]
  change (p : ℝ) ^ (sigma - 1) *
      ‖polynomialCompleteSum (p ^ (L + 1 - sigma)) (pow_pos hp.pos _)
        (Polynomial.stationaryNormalize f p mu.val)‖ ≤ _
  calc
    (p : ℝ) ^ (sigma - 1) *
        ‖polynomialCompleteSum (p ^ (L + 1 - sigma)) (pow_pos hp.pos _)
          (Polynomial.stationaryNormalize f p mu.val)‖ ≤
      (p : ℝ) ^ (sigma - 1) * ((M : ℝ) * Real.rpow p Echild) := by
        apply mul_le_mul_of_nonneg_left
        · simpa [sigma, M, Echild] using hrec
        · positivity
    _ = (M : ℝ) * Real.rpow p (((sigma - 1 : ℕ) : ℝ) + Echild) := by
      rw [← Real.rpow_natCast]
      calc
        Real.rpow p ((sigma - 1 : ℕ) : ℝ) *
            ((M : ℝ) * Real.rpow p Echild) =
          (M : ℝ) * (Real.rpow p ((sigma - 1 : ℕ) : ℝ) *
            Real.rpow p Echild) := by ring
        _ = _ := congrArg ((M : ℝ) * ·)
          (Real.rpow_add hpR _ _).symm
    _ ≤ (M : ℝ) * Real.rpow p Eout := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_exponent_le hpOne hExp
      · positivity
    _ = _ := by simp [M, Eout]

/-- Characterize small-prime stationary roots by derivative divisibility after
removing the derivative content. -/
theorem _root_.Polynomial.mem_smallPrimeStationaryRoots_iff
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (v : ZMod p) :
  v ∈ Polynomial.smallPrimeStationaryRoots f p ↔
    (p ^ (Polynomial.derivativeContentOrder f p + 1) : ℤ) ∣
      f.derivative.eval v.val := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let t := Polynomial.derivativeContentOrder f p
  have hdpos : 0 < f.natDegree := by
    have horder := Polynomial.ack_lemma_2_3 hp f le_rfl hprimitive 0
    omega
  have hderiv : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr hdpos.ne'
  have hspec := Polynomial.normalizeAtPrime_spec hp f.derivative hderiv
  have heval := congrArg (fun F : Polynomial ℤ => F.eval (v.val : ℤ)) hspec
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at heval
  have hscalar : ((p : ℤ) ^ t) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  simp only [Polynomial.smallPrimeStationaryRoots, Polynomial.rootsModPrime,
    Finset.mem_filter, Finset.mem_univ, true_and, Polynomial.IsRoot]
  change Polynomial.eval v
      ((Polynomial.normalizedDerivative f p).map (Int.castRingHom (ZMod p))) = 0 ↔ _
  have hv : ((v.val : ℕ) : ZMod p) = v := ZMod.natCast_zmod_val v
  conv_lhs => rw [← hv]
  have hevalNorm : Polynomial.eval ((v.val : ℕ) : ZMod p)
      ((Polynomial.normalizedDerivative f p).map (Int.castRingHom (ZMod p))) =
      (((Polynomial.normalizedDerivative f p).eval (v.val : ℤ) : ℤ) : ZMod p) := by
    simpa using polynomialEval_map_intCast p
      (Polynomial.normalizedDerivative f p) (v.val : ℤ)
  rw [hevalNorm]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [heval]
  change (p : ℤ) ∣ (Polynomial.normalizedDerivative f p).eval (v.val : ℤ) ↔
    (p : ℤ) ^ (t + 1) ∣
      (p : ℤ) ^ t * (Polynomial.normalizedDerivative f p).eval (v.val : ℤ)
  rw [pow_succ]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (mul_dvd_mul_iff_left hscalar (b := (p : ℤ))
      (c := (Polynomial.normalizedDerivative f p).eval (v.val : ℤ))).symm

/-- A small-prime residue block vanishes when its normalized derivative value is
nonzero modulo `p`. -/
theorem ack_smallPrime_block_vanish
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hd : 3 ≤ d) (_hpd : p ≤ d)
    (_hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (ha : 2 * (Polynomial.derivativeContentOrder f p + 1) ≤ a)
    (v : ZMod p) (hv : v ∉ Polynomial.smallPrimeStationaryRoots f p) :
  primePowerResidueClassSum p a hp f v = 0 := by
  let t := Polynomial.derivativeContentOrder f p
  let D := Polynomial.normalizedDerivative f p
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let _ : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let H : ZMod (p ^ a) := ((p ^ (a - t - 1) : ℕ) : ZMod (p ^ a))
  let P : Polynomial (ZMod (p ^ a)) := f.map (Int.castRingHom _)
  let Dbar : Polynomial (ZMod p) := Polynomial.modPrime p D
  have htBlock : t + 1 ≤ a - t - 1 := by
    dsimp [t] at ha ⊢
    omega
  have haPos : 0 < a := by omega
  have hHsq : H ^ 2 = 0 := by
    have hdvd : p ^ a ∣ (p ^ (a - t - 1)) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow p (by omega : a ≤ (a - t - 1) * 2)
    rcases hdvd with ⟨e, he⟩
    dsimp [H]
    calc
      (((p ^ (a - t - 1) : ℕ) : ZMod (p ^ a))) ^ 2 =
          (((p ^ (a - t - 1)) ^ 2 : ℕ) : ZMod (p ^ a)) := by norm_num
      _ = 0 := by rw [he, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hpdiv : p ∣ p ^ a := dvd_pow_self p haPos.ne'
  let phi : ZMod (p ^ a) →+* ZMod p := ZMod.castHom hpdiv (ZMod p)
  have hphi_val (x : ZMod (p ^ a)) : phi x = (x.val : ZMod p) := by
    simp [phi]
  have hphiH : phi H = 0 := by
    dsimp [H]
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_pow_self p (by omega : a - t - 1 ≠ 0)
  have hclassShift (x : ZMod (p ^ a)) :
      (((x + H).val : ℕ) : ZMod p) = ((x.val : ℕ) : ZMod p) := by
    rw [← hphi_val, ← hphi_val, map_add, hphiH, add_zero]
  have hEvalShift (x : ZMod (p ^ a)) :
      Polynomial.eval (x + H) P =
        Polynomial.eval x P + Polynomial.eval x P.derivative * H := by
    exact Polynomial.eval_add_of_sq_eq_zero P x H hHsq
  have hderivEval (x : ZMod (p ^ a)) :
      Polynomial.eval x P.derivative =
        ((f.derivative.eval (x.val : ℤ) : ℤ) : ZMod (p ^ a)) := by
    have hx : ((x.val : ℕ) : ZMod (p ^ a)) = x := x.natCast_zmod_val
    dsimp [P]
    rw [Polynomial.derivative_map]
    conv_lhs => rw [← hx]
    simpa using polynomialEval_map_intCast (p ^ a) f.derivative (x.val : ℤ)
  have hfderiv : f.derivative ≠ 0 := by
    apply Polynomial.derivative_ne_zero.mpr
    rw [hdegree]
    omega
  have hspec : f.derivative = Polynomial.C ((p : ℤ) ^ t) * D := by
    dsimp [t, D, Polynomial.derivativeContentOrder,
      Polynomial.normalizedDerivative]
    simpa [Nat.cast_pow] using
      Polynomial.normalizeAtPrime_spec hp f.derivative hfderiv
  have hderivScalar (n : ℤ) :
      f.derivative.eval n = ((p : ℤ) ^ t) * D.eval n := by
    have h := congrArg (fun F : Polynomial ℤ ↦ F.eval n) hspec
    simpa using h
  let c : ZMod p := Polynomial.eval v Dbar
  have hcne : c ≠ 0 := by
    intro hc
    apply hv
    simp only [Polynomial.smallPrimeStationaryRoots,
      Polynomial.rootsModPrime, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hc
  have hchi : ZMod.stdAddChar c ≠ 1 := by
    intro h
    apply hcne
    apply ZMod.injective_stdAddChar
    simpa using h
  have hDmod (x : ZMod (p ^ a))
      (hxv : ((x.val : ℕ) : ZMod p) = v) :
      ((D.eval (x.val : ℤ) : ℤ) : ZMod p) = c := by
    dsimp [c, Dbar, Polynomial.modPrime]
    rw [← hxv]
    simpa using (polynomialEval_map_intCast p D (x.val : ℤ)).symm
  have hcharLinear (x : ZMod (p ^ a))
      (hxv : ((x.val : ℕ) : ZMod p) = v) :
      ZMod.stdAddChar (Polynomial.eval x P.derivative * H) =
        ZMod.stdAddChar c := by
    rw [hderivEval, hderivScalar]
    have htop := stdAddChar_primePow_topDigit hp haPos (D.eval (x.val : ℤ))
    have hpow : t + (a - t - 1) = a - 1 := by omega
    have harg :
        ((((p : ℤ) ^ t) * D.eval (x.val : ℤ) : ℤ) : ZMod (p ^ a)) * H =
          (((p ^ (a - 1) : ℕ) : ℤ) * D.eval (x.val : ℤ) :
            ZMod (p ^ a)) := by
      dsimp [H]
      rw [← Nat.cast_pow]
      push_cast
      calc
        (p : ZMod (p ^ a)) ^ t * ((D.eval (x.val : ℤ) : ℤ) : ZMod (p ^ a)) *
            (p : ZMod (p ^ a)) ^ (a - t - 1) =
          ((p : ZMod (p ^ a)) ^ t * (p : ZMod (p ^ a)) ^ (a - t - 1)) *
            ((D.eval (x.val : ℤ) : ℤ) : ZMod (p ^ a)) := by ring
        _ = (p : ZMod (p ^ a)) ^ (a - 1) *
            ((D.eval (x.val : ℤ) : ℤ) : ZMod (p ^ a)) := by
          rw [← pow_add, hpow]
    rw [harg, htop, hDmod x hxv]
  let F : ZMod (p ^ a) → ℂ := fun x ↦
    if (x.val : ZMod p) = v then ZMod.stdAddChar (Polynomial.eval x P) else 0
  have hshiftTerm (x : ZMod (p ^ a)) :
      F (x + H) = F x * ZMod.stdAddChar c := by
    dsimp [F]
    rw [hclassShift]
    by_cases hxv : ((x.val : ℕ) : ZMod p) = v
    · rw [if_pos hxv, if_pos hxv, hEvalShift, AddChar.map_add_eq_mul,
        hcharLinear x hxv]
    · rw [if_neg hxv, if_neg hxv, zero_mul]
  rw [primePowerResidueClassSum]
  change (∑ x : ZMod (p ^ a), F x) = 0
  have hshift :
      (∑ x : ZMod (p ^ a), F x) =
        (∑ x : ZMod (p ^ a), F x) * ZMod.stdAddChar c := by
    calc
      _ = ∑ x : ZMod (p ^ a), F (x + H) := by
        exact (Fintype.sum_bijective (fun x : ZMod (p ^ a) ↦ x + H)
          (AddGroup.addRight_bijective H) _ _ (fun _ ↦ rfl)).symm
      _ = _ := by simp_rw [hshiftTerm, Finset.sum_mul]
  have hfactor :
      (1 - ZMod.stdAddChar c) * (∑ x : ZMod (p ^ a), F x) = 0 := by
    linear_combination hshift
  exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hchi.symm)

private theorem ack_lateRoot_aggregate
    (d L r M p : ℕ) (hd : 3 ≤ d) (hr : 0 < r)
    (hrM : r ≤ M) (hMd : M ≤ d - 1) (hdp : d < p)
    (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d)
    (hLM : r * L ≤ M + r) :
    (r : ℝ) * (p : ℝ) ^ L ≤
      (M : ℝ) * Real.rpow p
        (-1 + (3 : ℝ) / d + (L + 1 : ℝ) * (1 - (1 : ℝ) / d)) := by
  let E : ℝ :=
    -1 + (3 : ℝ) / d + (L + 1 : ℝ) * (1 - (1 : ℝ) / d)
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (lt_trans (by omega : 0 < d) hdp)
  have hpOne : (1 : ℝ) ≤ p := by
    exact_mod_cast (show 1 ≤ p by omega)
  have h11 := ack_ineq_2_11 d L r M hd hr hLM
  have hExp : (L : ℝ) ≤ E - (1 : ℝ) / d +
      (M : ℝ) / ((r : ℝ) * d) := by
    dsimp [E]
    convert h11 using 1
    ring
  have h12 := ack_ineq_2_12 d r M p hd hr hrM hMd hdp hpB
  calc
    (r : ℝ) * (p : ℝ) ^ L =
        (r : ℝ) * Real.rpow p (L : ℝ) := by
      exact congrArg ((r : ℝ) * ·) (Real.rpow_natCast (p : ℝ) L).symm
    _ ≤ (r : ℝ) * Real.rpow p
        (E - (1 : ℝ) / d + (M : ℝ) / ((r : ℝ) * d)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_exponent_le hpOne hExp
      · positivity
    _ = ((r : ℝ) * Real.rpow p ((M : ℝ) / ((r : ℝ) * d))) *
        Real.rpow p (E - (1 : ℝ) / d) := by
      rw [show E - (1 : ℝ) / d + (M : ℝ) / ((r : ℝ) * d) =
          (M : ℝ) / ((r : ℝ) * d) + (E - (1 : ℝ) / d) by ring]
      calc
        (r : ℝ) * Real.rpow p
            ((M : ℝ) / ((r : ℝ) * d) + (E - (1 : ℝ) / d)) =
          (r : ℝ) * (Real.rpow p ((M : ℝ) / ((r : ℝ) * d)) *
            Real.rpow p (E - (1 : ℝ) / d)) :=
          congrArg ((r : ℝ) * ·) (Real.rpow_add hpR _ _)
        _ = _ := by ring
    _ ≤ ((M : ℝ) * Real.rpow p ((1 : ℝ) / d)) *
        Real.rpow p (E - (1 : ℝ) / d) := by
      exact mul_le_mul_of_nonneg_right h12 (Real.rpow_nonneg hpR.le _)
    _ = (M : ℝ) * Real.rpow p E := by
      calc
        (M : ℝ) * Real.rpow p ((1 : ℝ) / d) *
            Real.rpow p (E - (1 : ℝ) / d) =
          (M : ℝ) * (Real.rpow p ((1 : ℝ) / d) *
            Real.rpow p (E - (1 : ℝ) / d)) := by ring
        _ = (M : ℝ) * Real.rpow p
            ((1 : ℝ) / d + (E - (1 : ℝ) / d)) :=
          congrArg ((M : ℝ) * ·) (Real.rpow_add hpR _ _).symm
        _ = _ := by congr 2; ring
    _ = _ := rfl

private theorem ack_earlyRoot_aggregate
    {I : Type*} (s : Finset I) (m : I → ℕ) (d L p : ℕ)
    (hd : 0 < d) (hpOne : (1 : ℝ) ≤ p)
    (hm : ∀ i ∈ s, m i + 1 ≤ d) :
    ∑ i ∈ s, (m i : ℝ) * Real.rpow p
        (-2 + ((m i + 1 : ℕ) : ℝ) / d + (3 : ℝ) / d +
          (L + 1 : ℝ) * (1 - (1 : ℝ) / d)) ≤
      ((∑ i ∈ s, m i : ℕ) : ℝ) * Real.rpow p
        (-1 + (3 : ℝ) / d + (L + 1 : ℝ) * (1 - (1 : ℝ) / d)) := by
  let E : ℝ :=
    -1 + (3 : ℝ) / d + (L + 1 : ℝ) * (1 - (1 : ℝ) / d)
  calc
    ∑ i ∈ s, (m i : ℝ) * Real.rpow p
        (-2 + ((m i + 1 : ℕ) : ℝ) / d + (3 : ℝ) / d +
          (L + 1 : ℝ) * (1 - (1 : ℝ) / d)) ≤
      ∑ i ∈ s, (m i : ℝ) * Real.rpow p E := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
      · apply Real.rpow_le_rpow_of_exponent_le hpOne
        have hcast : ((m i + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hm i hi
        have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
        dsimp [E]
        field_simp [hd0]
        nlinarith
      · positivity
    _ = ((∑ i ∈ s, m i : ℕ) : ℝ) * Real.rpow p E := by
      rw [← Finset.sum_mul]
      norm_cast
    _ = _ := rfl

private theorem derivativeRoots_partition
    (p L : ℕ) [Fact p.Prime] (f : Polynomial ℤ) :
    Polynomial.derivativeRoots f p =
      Polynomial.earlyDerivativeRoots f p L ∪
        Polynomial.lateDerivativeRoots f p L := by
  ext mu
  simp only [Polynomial.earlyDerivativeRoots, Polynomial.lateDerivativeRoots,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hroot
    by_cases hs : Polynomial.stationaryOrder f p mu.val < L
    · exact Or.inl ⟨hroot, hs⟩
    · exact Or.inr ⟨hroot, Nat.le_of_not_gt hs⟩
  · rintro (⟨hroot, _⟩ | ⟨hroot, _⟩) <;> exact hroot

private theorem early_late_disjoint
    (p L : ℕ) [Fact p.Prime] (f : Polynomial ℤ) :
    Disjoint (Polynomial.earlyDerivativeRoots f p L)
      (Polynomial.lateDerivativeRoots f p L) := by
  apply Finset.disjoint_left.mpr
  intro mu hearly hlate
  simp only [Polynomial.earlyDerivativeRoots, Polynomial.lateDerivativeRoots,
    Finset.mem_filter] at hearly hlate
  omega

private theorem derivativeRootMass_partition
    (p L : ℕ) [Fact p.Prime] (f : Polynomial ℤ) :
    Polynomial.derivativeRootMass f p =
      Polynomial.derivativeRootMassOn f p
          (Polynomial.earlyDerivativeRoots f p L) +
        Polynomial.derivativeRootMassOn f p
          (Polynomial.lateDerivativeRoots f p L) := by
  change (∑ mu ∈ Polynomial.derivativeRoots f p,
      (Polynomial.modPrime p f.derivative).rootMultiplicity mu) =
    (∑ mu ∈ Polynomial.earlyDerivativeRoots f p L,
      (Polynomial.modPrime p f.derivative).rootMultiplicity mu) +
    ∑ mu ∈ Polynomial.lateDerivativeRoots f p L,
      (Polynomial.modPrime p f.derivative).rootMultiplicity mu
  rw [derivativeRoots_partition p L f,
    Finset.sum_union (early_late_disjoint p L f)]

private theorem late_card_le_mass
    (p L : ℕ) [Fact p.Prime] (f : Polynomial ℤ)
    (hmod : Polynomial.modPrime p f.derivative ≠ 0) :
    (Polynomial.lateDerivativeRoots f p L).card ≤
      Polynomial.derivativeRootMassOn f p
        (Polynomial.lateDerivativeRoots f p L) := by
  rw [Polynomial.derivativeRootMassOn]
  calc
    (Polynomial.lateDerivativeRoots f p L).card =
        ∑ mu ∈ Polynomial.lateDerivativeRoots f p L, 1 := by simp
    _ ≤ ∑ mu ∈ Polynomial.lateDerivativeRoots f p L,
        (Polynomial.modPrime p f.derivative).rootMultiplicity mu := by
      apply Finset.sum_le_sum
      intro mu hmu
      apply (Polynomial.rootMultiplicity_pos hmod).mpr
      have hroot := (Finset.mem_filter.mp hmu).1
      simpa [Polynomial.derivativeRoots, Polynomial.rootsModPrime] using hroot

private theorem late_sigma_mass
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (L : ℕ) :
    (Polynomial.lateDerivativeRoots f p L).card * L ≤
      Polynomial.derivativeRootMassOn f p
        (Polynomial.lateDerivativeRoots f p L) +
        (Polynomial.lateDerivativeRoots f p L).card := by
  calc
    (Polynomial.lateDerivativeRoots f p L).card * L =
        ∑ mu ∈ Polynomial.lateDerivativeRoots f p L, L := by simp
    _ ≤ ∑ mu ∈ Polynomial.lateDerivativeRoots f p L,
        ((Polynomial.modPrime p f.derivative).rootMultiplicity mu + 1) := by
      apply Finset.sum_le_sum
      intro mu hmu
      have hparts := Finset.mem_filter.mp hmu
      have hroot : (Polynomial.modPrime p f.derivative).IsRoot mu := by
        simpa [Polynomial.derivativeRoots, Polynomial.rootsModPrime] using hparts.1
      exact hparts.2.trans
        (Polynomial.stationaryOrder_le_rootMultiplicity_succ hp f hdegree
          hdp hprimitive mu hroot)
    _ = Polynomial.derivativeRootMassOn f p
          (Polynomial.lateDerivativeRoots f p L) +
        (Polynomial.lateDerivativeRoots f p L).card := by
      rw [Finset.sum_add_distrib]
      simp [Polynomial.derivativeRootMassOn]

private theorem ack_ineq_2_10_of_earlyBounds
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (L : ℕ) (hL : 1 ≤ L)
    (w : ZMod p → ℝ)
    (hearly : ∀ mu ∈ Polynomial.earlyDerivativeRoots f p L,
      ‖primePowerResidueClassSum p (L + 1) hp f mu‖ ≤ w mu) :
    ‖polynomialCompleteSum (p ^ (L + 1)) (pow_pos hp.pos _) f‖ ≤
      ((Polynomial.lateDerivativeRoots f p L).card : ℝ) * (p : ℝ) ^ L +
        ∑ mu ∈ Polynomial.earlyDerivativeRoots f p L, w mu := by
  let R := Polynomial.derivativeRoots f p
  let E := Polynomial.earlyDerivativeRoots f p L
  let T := Polynomial.lateDerivativeRoots f p L
  have hsumRoots :
      (∑ mu : ZMod p, primePowerResidueClassSum p (L + 1) hp f mu) =
        ∑ mu ∈ R, primePowerResidueClassSum p (L + 1) hp f mu := by
    calc
      (∑ mu : ZMod p, primePowerResidueClassSum p (L + 1) hp f mu) =
          ∑ mu : ZMod p, if mu ∈ R then
            primePowerResidueClassSum p (L + 1) hp f mu else 0 := by
        apply Finset.sum_congr rfl
        intro mu _hmu
        by_cases hroot : mu ∈ R
        · rw [if_pos hroot]
        · rw [if_neg hroot,
            ack_eq_2_3_vanish hp (by omega : 2 ≤ L + 1) f mu]
          simpa [R, Polynomial.derivativeRoots, Polynomial.rootsModPrime]
            using hroot
      _ = ∑ mu ∈ R, primePowerResidueClassSum p (L + 1) hp f mu := by
        simp
  rw [ack_completeSum_eq_sum_residueClasses hp (by omega : 0 < L + 1) f,
    hsumRoots]
  calc
    ‖∑ mu ∈ R, primePowerResidueClassSum p (L + 1) hp f mu‖ ≤
        ∑ mu ∈ R, ‖primePowerResidueClassSum p (L + 1) hp f mu‖ :=
      norm_sum_le _ _
    _ = (∑ mu ∈ E, ‖primePowerResidueClassSum p (L + 1) hp f mu‖) +
        ∑ mu ∈ T, ‖primePowerResidueClassSum p (L + 1) hp f mu‖ := by
      rw [show R = E ∪ T by
          simpa [R, E, T] using derivativeRoots_partition p L f,
        Finset.sum_union (by
          simpa [E, T] using early_late_disjoint p L f)]
    _ ≤ (∑ mu ∈ E, w mu) + ∑ _mu ∈ T, (p : ℝ) ^ L := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro mu hmu
        exact hearly mu (by simpa [E] using hmu)
      · apply Finset.sum_le_sum
        intro mu _hmu
        exact ack_ineq_2_8 hp f L mu
    _ = ((T.card : ℕ) : ℝ) * (p : ℝ) ^ L +
        ∑ mu ∈ E, w mu := by
      simp
      ring
    _ = _ := by simp [E, T]

private theorem ack_eq_2_6_induction
    [Fact p.Prime] (hp : p.Prime) (a : ℕ) (ha : 2 ≤ a) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hdp : d < p)
    (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    (Polynomial.derivativeRootMass f p : ℝ) *
      Real.rpow p
        (-1 + (3 : ℝ) / d + (a : ℝ) * (1 - (1 : ℝ) / d)) := by
  induction a using Nat.strong_induction_on generalizing f with
  | h a ih =>
      let L := a - 1
      let E := Polynomial.earlyDerivativeRoots f p L
      let T := Polynomial.lateDerivativeRoots f p L
      let mult : ZMod p → ℕ := fun mu ↦
        (Polynomial.modPrime p f.derivative).rootMultiplicity mu
      let M₁ := Polynomial.derivativeRootMassOn f p T
      let M₂ := Polynomial.derivativeRootMassOn f p E
      let r := T.card
      let eout : ℝ :=
        -1 + (3 : ℝ) / d + (L + 1 : ℝ) * (1 - (1 : ℝ) / d)
      have hLa : L + 1 = a := by
        dsimp [L]
        omega
      have hLone : 1 ≤ L := by
        dsimp [L]
        omega
      have hmod : Polynomial.modPrime p f.derivative ≠ 0 :=
        chen_derivative_modPrime_ne_zero hp f hdegree hdp hprimitive
      have hearly : ∀ mu ∈ E,
          ‖primePowerResidueClassSum p (L + 1) hp f mu‖ ≤
            (mult mu : ℝ) * Real.rpow p
              (-2 + ((mult mu + 1 : ℕ) : ℝ) / d + (3 : ℝ) / d +
                (L + 1 : ℝ) * (1 - (1 : ℝ) / d)) := by
        intro mu hmu
        have hmu' : mu ∈ Polynomial.earlyDerivativeRoots f p L := by
          simpa only [E] using hmu
        have hparts := Finset.mem_filter.mp hmu'
        have hroot : (Polynomial.modPrime p f.derivative).IsRoot mu := by
          simpa [Polynomial.derivativeRoots, Polynomial.rootsModPrime] using hparts.1
        have hchild := Polynomial.stationaryChildInvariant hp f hdegree
          (by omega : 0 < d) hprimitive mu.val
        have hsigma2 := Polynomial.stationaryOrder_two_le_of_isRoot hp f mu
          hchild.translate_ne_zero hroot
        have hsigmaL : Polynomial.stationaryOrder f p mu.val < L := hparts.2
        have hLtwo : 2 ≤ L := by omega
        let childExponent := L + 1 - Polynomial.stationaryOrder f p mu.val
        have hchildTwo : 2 ≤ childExponent := by
          dsimp [childExponent]
          omega
        have hchildLt : childExponent < a := by
          dsimp [childExponent]
          omega
        have hchildBound := ih childExponent hchildLt hchildTwo
          (Polynomial.stationaryNormalize f p mu.val) hchild.natDegree_eq
          hchild.primitive
        have hmass := Polynomial.stationaryNormalize_derivativeRootMass_le
          hp f hdegree hdp hprimitive mu hroot
        have hrec :
            ‖polynomialCompleteSum (p ^ childExponent) (pow_pos hp.pos _)
                (Polynomial.stationaryNormalize f p mu.val)‖ ≤
              (mult mu : ℝ) * Real.rpow p
                (-1 + (3 : ℝ) / d +
                  (childExponent : ℝ) * (1 - (1 : ℝ) / d)) := by
          calc
          ‖polynomialCompleteSum (p ^ childExponent) (pow_pos hp.pos _)
              (Polynomial.stationaryNormalize f p mu.val)‖ ≤
            (Polynomial.derivativeRootMass
                (Polynomial.stationaryNormalize f p mu.val) p : ℝ) *
              Real.rpow p
                (-1 + (3 : ℝ) / d +
                  (childExponent : ℝ) * (1 - (1 : ℝ) / d)) := hchildBound
          _ ≤ (mult mu : ℝ) * Real.rpow p
                (-1 + (3 : ℝ) / d +
                  (childExponent : ℝ) * (1 - (1 : ℝ) / d)) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hmass
            · exact Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _
          _ = _ := by simp [childExponent, mult]
        have hchildCast : (childExponent : ℝ) = (L : ℝ) + 1 -
            (Polynomial.stationaryOrder f p mu.val : ℝ) := by
          dsimp [childExponent]
          rw [Nat.cast_sub (by omega :
            Polynomial.stationaryOrder f p mu.val ≤ L + 1)]
          norm_num
        rw [hchildCast] at hrec
        have h27 := ack_ineq_2_7_of_inductionBound hp f hdegree hd hdp hprimitive
          L hLtwo mu hmu' (by simpa only [childExponent] using hrec)
        simpa [mult, Nat.cast_add] using h27
      have hassembly := ack_ineq_2_10_of_earlyBounds hp f L hLone
        (fun mu ↦ (mult mu : ℝ) * Real.rpow p
          (-2 + ((mult mu + 1 : ℕ) : ℝ) / d + (3 : ℝ) / d +
            (L + 1 : ℝ) * (1 - (1 : ℝ) / d))) hearly
      have hmassPartition : Polynomial.derivativeRootMass f p = M₂ + M₁ := by
        simpa [E, T, M₁, M₂, add_comm] using derivativeRootMass_partition p L f
      have htotalMass : Polynomial.derivativeRootMass f p ≤ d - 1 :=
        Polynomial.derivativeRootMass_le hp f hdegree hdp hprimitive
      have hM₁d : M₁ ≤ d - 1 := by omega
      have hrM₁ : r ≤ M₁ := by
        simpa [r, M₁, T] using late_card_le_mass p L f hmod
      have hLM₁ : r * L ≤ M₁ + r := by
        simpa [r, M₁, T] using late_sigma_mass hp f hdegree hdp hprimitive L
      have hlate : (r : ℝ) * (p : ℝ) ^ L ≤
          (M₁ : ℝ) * Real.rpow p eout := by
        by_cases hrzero : r = 0
        · rw [hrzero]
          norm_num only [Nat.cast_zero, zero_mul]
          exact mul_nonneg (Nat.cast_nonneg _)
            (Real.rpow_nonneg (x := (p : ℝ)) (by exact_mod_cast hp.pos.le) eout)
        · exact ack_lateRoot_aggregate d L r M₁ p hd (Nat.pos_of_ne_zero hrzero)
            hrM₁ hM₁d hdp hpB hLM₁
      have hmultDegree : ∀ mu ∈ E, mult mu + 1 ≤ d := by
        intro mu hmu
        have hmu' : mu ∈ Polynomial.earlyDerivativeRoots f p L := by
          simpa only [E] using hmu
        have hmuRoot : mu ∈ Polynomial.derivativeRoots f p :=
          (Finset.mem_filter.mp hmu').1
        have hmultTotal : mult mu ≤ Polynomial.derivativeRootMass f p := by
          rw [Polynomial.derivativeRootMass]
          exact Finset.single_le_sum
            (fun i _hi ↦ Nat.zero_le
              ((Polynomial.modPrime p f.derivative).rootMultiplicity i)) hmuRoot
        omega
      have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
      have hearlySum :
          ∑ mu ∈ E, (mult mu : ℝ) * Real.rpow p
              (-2 + ((mult mu + 1 : ℕ) : ℝ) / d + (3 : ℝ) / d +
                (L + 1 : ℝ) * (1 - (1 : ℝ) / d)) ≤
            (M₂ : ℝ) * Real.rpow p eout := by
        simpa [M₂, E, mult, eout, Polynomial.derivativeRootMassOn] using
          ack_earlyRoot_aggregate E mult d L p (by omega : 0 < d) hpOne hmultDegree
      calc
        ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ =
            ‖polynomialCompleteSum (p ^ (L + 1)) (pow_pos hp.pos _) f‖ := by
          rw [hLa]
        _ ≤ (r : ℝ) * (p : ℝ) ^ L +
            ∑ mu ∈ E, (mult mu : ℝ) * Real.rpow p
              (-2 + ((mult mu + 1 : ℕ) : ℝ) / d + (3 : ℝ) / d +
                (L + 1 : ℝ) * (1 - (1 : ℝ) / d)) := by
          simpa [r, T, E] using hassembly
        _ ≤ (M₁ : ℝ) * Real.rpow p eout +
            (M₂ : ℝ) * Real.rpow p eout := add_le_add hlate hearlySum
        _ = (Polynomial.derivativeRootMass f p : ℝ) * Real.rpow p eout := by
          have hmassCast : (Polynomial.derivativeRootMass f p : ℝ) =
              (M₂ : ℝ) + (M₁ : ℝ) := by exact_mod_cast hmassPartition
          rw [hmassCast]
          ring
        _ = _ := by
          have hLaCast : (L : ℝ) + 1 = a := by exact_mod_cast hLa
          dsimp [eout]
          rw [hLaCast]

/-- ACK equation (2.6): the middle-prime complete-sum bound obtained by strong
induction over stationary children. -/
theorem ack_eq_2_6
    [Fact p.Prime] (hp : p.Prime) (ha : 2 ≤ a) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hdp : d < p)
    (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    (Polynomial.derivativeRootMass f p : ℝ) *
      Real.rpow p
        (-1 + (3 : ℝ) / d + (a : ℝ) * (1 - (1 : ℝ) / d)) :=
  ack_eq_2_6_induction hp a ha f hdegree hd hdp hpB hprimitive

/-- ACK inequality (2.10): split the middle-prime complete sum into early and
late stationary-root contributions. -/
theorem ack_ineq_2_10
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hdp : d < p)
    (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (L : ℕ) (hL : 2 ≤ L) :
  ‖polynomialCompleteSum (p ^ (L + 1)) (pow_pos hp.pos _) f‖ ≤
    ((Polynomial.lateDerivativeRoots f p L).card : ℝ) * (p : ℝ) ^ L +
      ∑ mu ∈ Polynomial.earlyDerivativeRoots f p L,
        ((Polynomial.modPrime p f.derivative).rootMultiplicity mu : ℝ) *
          Real.rpow p
            (((Polynomial.modPrime p f.derivative).rootMultiplicity mu + 1 : ℝ) / d -
              2 + (3 : ℝ) / d +
              (L + 1 : ℝ) * (1 - (1 : ℝ) / d)) := by
  let w : ZMod p → ℝ := fun mu ↦
    ((Polynomial.modPrime p f.derivative).rootMultiplicity mu : ℝ) *
      Real.rpow p
        (((Polynomial.modPrime p f.derivative).rootMultiplicity mu + 1 : ℝ) / d -
          2 + (3 : ℝ) / d +
          (L + 1 : ℝ) * (1 - (1 : ℝ) / d))
  have hearly : ∀ mu ∈ Polynomial.earlyDerivativeRoots f p L,
      ‖primePowerResidueClassSum p (L + 1) hp f mu‖ ≤ w mu := by
    intro mu hmu
    have hparts := Finset.mem_filter.mp hmu
    have hroot : (Polynomial.modPrime p f.derivative).IsRoot mu := by
      simpa [Polynomial.derivativeRoots, Polynomial.rootsModPrime] using hparts.1
    let sigma := Polynomial.stationaryOrder f p mu.val
    let b := L + 1 - sigma
    have hsigmaL : sigma < L := by simpa [sigma] using hparts.2
    have hchild := Polynomial.stationaryChildInvariant hp f hdegree
      (by omega : 0 < d) hprimitive mu.val
    have hsigma2 : 2 ≤ sigma := by
      dsimp [sigma]
      exact Polynomial.stationaryOrder_two_le_of_isRoot hp f mu
        hchild.translate_ne_zero hroot
    have hb2 : 2 ≤ b := by dsimp [b]; omega
    have hrec0 := ack_eq_2_6 hp hb2
      (Polynomial.stationaryNormalize f p mu.val) hchild.natDegree_eq hd hdp
      hpB hchild.primitive
    have hmassChild :=
      Polynomial.stationaryNormalize_derivativeRootMass_le hp f hdegree
        hdp hprimitive mu hroot
    have hrec :
        ‖polynomialCompleteSum (p ^ b) (pow_pos hp.pos _)
          (Polynomial.stationaryNormalize f p mu.val)‖ ≤
        ((Polynomial.modPrime p f.derivative).rootMultiplicity mu : ℝ) *
          Real.rpow p
            (-1 + (3 : ℝ) / d + (b : ℝ) * (1 - (1 : ℝ) / d)) := by
      calc
        _ ≤ (Polynomial.derivativeRootMass
              (Polynomial.stationaryNormalize f p mu.val) p : ℝ) *
            Real.rpow p
              (-1 + (3 : ℝ) / d + (b : ℝ) * (1 - (1 : ℝ) / d)) :=
          hrec0
        _ ≤ ((Polynomial.modPrime p f.derivative).rootMultiplicity mu : ℝ) *
            Real.rpow p
              (-1 + (3 : ℝ) / d + (b : ℝ) * (1 - (1 : ℝ) / d)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hmassChild
          · exact Real.rpow_nonneg (by positivity) _
    have hbCast : (b : ℝ) = (L : ℝ) + 1 - (sigma : ℝ) := by
      dsimp [b]
      rw [Nat.cast_sub (by omega : sigma ≤ L + 1)]
      norm_num
    rw [hbCast] at hrec
    have h27 := ack_ineq_2_7_of_inductionBound hp f hdegree hd hdp
      hprimitive L hL mu hmu (by simpa only [b, sigma] using hrec)
    dsimp [w]
    have hexp :
        -2 +
            ((Polynomial.modPrime p f.derivative).rootMultiplicity mu + 1 : ℝ) / d +
            (3 : ℝ) / d + (L + 1 : ℝ) * (1 - (1 : ℝ) / d) =
          ((Polynomial.modPrime p f.derivative).rootMultiplicity mu + 1 : ℝ) / d -
            2 + (3 : ℝ) / d +
            (L + 1 : ℝ) * (1 - (1 : ℝ) / d) := by ring
    rw [← hexp]
    exact h27
  exact ack_ineq_2_10_of_earlyBounds hp f L (by omega) w hearly

private theorem ack_smallPrime_lowBlock_power
    (hp : p.Prime) (d a t : ℕ) (hd : 3 ≤ d) (hpd : p ≤ d)
    (hpt : p ^ t ≤ d) (ha : a < 2 * (t + 1)) :
    (p : ℝ) ^ a ≤ Real.rpow d ((3 : ℝ) / d) *
      Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) := by
  have hpa : p ^ a ≤ d ^ 3 := by
    calc
      p ^ a ≤ p ^ (t + t + 1) := by
        apply Nat.pow_le_pow_right hp.pos
        omega
      _ = (p ^ t) * (p ^ t) * p := by
        rw [pow_add, pow_add, pow_one]
      _ ≤ d * d * d := by gcongr
      _ = d ^ 3 := by ring
  have hpR : (0 : ℝ) ≤ p := by positivity
  have hpPosR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hdR : (0 : ℝ) ≤ d := by positivity
  have hdposR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hinvNonneg : (0 : ℝ) ≤ (1 : ℝ) / d := by positivity
  have hroot : Real.rpow p ((a : ℝ) / d) ≤ Real.rpow d ((3 : ℝ) / d) := by
    have hpaR : ((p ^ a : ℕ) : ℝ) ≤ ((d ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast hpa
    have hr := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (p ^ a : ℕ))
      hpaR hinvNonneg
    calc
      Real.rpow p ((a : ℝ) / d) =
          Real.rpow p ((a : ℝ) * ((1 : ℝ) / d)) := by congr 1; ring
      _ = Real.rpow ((p : ℝ) ^ a) ((1 : ℝ) / d) := by
        exact Real.rpow_natCast_mul hpR a ((1 : ℝ) / d)
      _ ≤ Real.rpow ((d : ℝ) ^ 3) ((1 : ℝ) / d) := by
        simpa using hr
      _ = Real.rpow d ((3 : ℝ) * ((1 : ℝ) / d)) := by
        exact (Real.rpow_natCast_mul hdR 3 ((1 : ℝ) / d)).symm
      _ = Real.rpow d ((3 : ℝ) / d) := by congr 1; ring
  calc
    (p : ℝ) ^ a = Real.rpow p (a : ℝ) := Real.rpow_natCast _ _ |>.symm
    _ = Real.rpow p
        ((a : ℝ) * (1 - (1 : ℝ) / d) + (a : ℝ) / d) := by
      congr 1
      field_simp
      ring
    _ = Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) *
        Real.rpow p ((a : ℝ) / d) := Real.rpow_add hpPosR _ _
    _ ≤ Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) *
        Real.rpow d ((3 : ℝ) / d) := by
      exact mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hpR _)
    _ = _ := by ring

private theorem ack_smallPrime_recursion_power
    {p : ℕ} (hp : p.Prime) (d a sigma : ℕ) (hd : 3 ≤ d)
    (hsigma1 : 1 ≤ sigma) (hsigmaD : sigma ≤ d) (hsigmaA : sigma ≤ a) :
    (p : ℝ) ^ (sigma - 1) *
        Real.rpow p ((a - sigma : ℕ) * (1 - (1 : ℝ) / d)) ≤
      Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) := by
  have hpPosR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOneR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hsigmaSub : ((sigma - 1 : ℕ) : ℝ) = (sigma : ℝ) - 1 := by
    rw [Nat.cast_sub hsigma1]
    norm_num
  have haSub : ((a - sigma : ℕ) : ℝ) = (a : ℝ) - sigma := by
    rw [Nat.cast_sub hsigmaA]
  have hexp : ((sigma - 1 : ℕ) : ℝ) +
      ((a - sigma : ℕ) : ℝ) * (1 - (1 : ℝ) / d) ≤
        (a : ℝ) * (1 - (1 : ℝ) / d) := by
    have hdPosR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hsigmaDR : (sigma : ℝ) ≤ d := by exact_mod_cast hsigmaD
    rw [hsigmaSub, haSub]
    field_simp
    nlinarith
  calc
    (p : ℝ) ^ (sigma - 1) *
        Real.rpow p ((a - sigma : ℕ) * (1 - (1 : ℝ) / d)) =
      Real.rpow p ((sigma - 1 : ℕ) : ℝ) *
        Real.rpow p (((a - sigma : ℕ) : ℝ) * (1 - (1 : ℝ) / d)) := by
          exact congrArg
            (· * Real.rpow p (((a - sigma : ℕ) : ℝ) *
              (1 - (1 : ℝ) / d)))
            (Real.rpow_natCast (p : ℝ) (sigma - 1)).symm
    _ = Real.rpow p (((sigma - 1 : ℕ) : ℝ) +
        ((a - sigma : ℕ) : ℝ) * (1 - (1 : ℝ) / d)) :=
      (Real.rpow_add hpPosR _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hpOneR hexp

private theorem ack_smallPrime_terminal_power
    {p : ℕ} (hp : p.Prime) (d a : ℕ) (hd : 3 ≤ d)
    (ha : 0 < a) (haD : a ≤ d) :
    (p : ℝ) ^ (a - 1) ≤ Real.rpow d ((3 : ℝ) / d) *
      Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) := by
  have hpPosR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOneR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hdOneR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hfactor : (1 : ℝ) ≤ Real.rpow d ((3 : ℝ) / d) :=
    Real.one_le_rpow hdOneR (by positivity)
  have haPos : 1 ≤ a := ha
  have haSub : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub haPos]
    norm_num
  have hexp : ((a - 1 : ℕ) : ℝ) ≤
      (a : ℝ) * (1 - (1 : ℝ) / d) := by
    have haDR : (a : ℝ) ≤ d := by exact_mod_cast haD
    have hdPosR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    rw [haSub]
    field_simp
    nlinarith
  calc
    (p : ℝ) ^ (a - 1) = Real.rpow p ((a - 1 : ℕ) : ℝ) := by
      exact (Real.rpow_natCast (p : ℝ) (a - 1)).symm
    _ ≤ Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) :=
      Real.rpow_le_rpow_of_exponent_le hpOneR hexp
    _ ≤ Real.rpow d ((3 : ℝ) / d) *
        Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) := by
      calc
        _ = 1 * Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) := by rw [one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right hfactor
          (Real.rpow_nonneg hpPosR.le _)

private theorem ack_eq_2_14_of_inductionBound
    [Fact p.Prime] (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (_hpd : p ≤ d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (hblock : 2 * (Polynomial.derivativeContentOrder f p + 1) ≤ a)
    (mu : ZMod p) (hmu : mu ∈ Polynomial.smallPrimeStationaryRoots f p)
    (hrec : Polynomial.stationaryOrder f p mu.val < a →
      ‖polynomialCompleteSum
        (p ^ (a - Polynomial.stationaryOrder f p mu.val))
        (pow_pos hp.pos _)
        (Polynomial.stationaryNormalize f p mu.val)‖ ≤
      Real.rpow d ((3 : ℝ) / d) *
        max 1 (Polynomial.smallPrimeStationaryMass
          (Polynomial.stationaryNormalize f p mu.val) p : ℝ) *
        Real.rpow p
          (((a - Polynomial.stationaryOrder f p mu.val : ℕ) : ℝ) *
            (1 - (1 : ℝ) / d))) :
  ‖primePowerResidueClassSum p a hp f mu‖ ≤
    (Polynomial.modPrime p
      (Polynomial.normalizedDerivative f p)).rootMultiplicity mu *
      Real.rpow d ((3 : ℝ) / d) *
      Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) := by
  let sigma := Polynomial.stationaryOrder f p mu.val
  let m := (Polynomial.modPrime p
    (Polynomial.normalizedDerivative f p)).rootMultiplicity mu
  have hrootD : (Polynomial.modPrime p
      (Polynomial.normalizedDerivative f p)).IsRoot mu := by
    simpa [Polynomial.smallPrimeStationaryRoots,
      Polynomial.rootsModPrime] using hmu
  have hdiv := (Polynomial.mem_smallPrimeStationaryRoots_iff hp f hprimitive mu).mp hmu
  have hpdiv : (p : ℤ) ∣ f.derivative.eval mu.val := by
    exact (dvd_pow_self (p : ℤ)
      (by omega : Polynomial.derivativeContentOrder f p + 1 ≠ 0)).trans hdiv
  have hroot : (Polynomial.modPrime p f.derivative).IsRoot mu := by
    rw [Polynomial.IsRoot]
    have heval := polynomialEval_map_intCast p f.derivative (mu.val : ℤ)
    have hmuval : ((mu.val : ℕ) : ZMod p) = mu := ZMod.natCast_zmod_val mu
    have heval' :
        Polynomial.eval ((mu.val : ℕ) : ZMod p)
            (f.derivative.map (Int.castRingHom (ZMod p))) =
          ((f.derivative.eval (mu.val : ℤ) : ℤ) : ZMod p) := by
      simpa using heval
    change Polynomial.eval mu (f.derivative.map (Int.castRingHom (ZMod p))) = 0
    rw [← hmuval, heval', ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hpdiv
  have hchild := Polynomial.stationaryChildInvariant hp f hdegree
    (by omega : 0 < d) hprimitive mu.val
  have hsigma2 : 2 ≤ sigma := by
    dsimp [sigma]
    exact Polynomial.stationaryOrder_two_le_of_isRoot hp f mu
      hchild.translate_ne_zero hroot
  have hsigmaD : sigma ≤ d := by
    dsimp [sigma]
    exact (Polynomial.ack_lemma_2_3 hp f hdegree.le hprimitive mu.val).2
  have hfderiv : f.derivative ≠ 0 := by
    apply Polynomial.derivative_ne_zero.mpr
    rw [hdegree]
    omega
  have hDprimitive : ¬ p ∣ Polynomial.contentNat
      (Polynomial.normalizedDerivative f p) :=
    Polynomial.normalizeAtPrime_primitive hp f.derivative hfderiv
  have hDmod : Polynomial.modPrime p
      (Polynomial.normalizedDerivative f p) ≠ 0 :=
    modPrime_ne_zero_of_content_primitive _ hDprimitive
  have hmpos : 1 ≤ m := by
    dsimp [m]
    exact (Polynomial.rootMultiplicity_pos hDmod).mpr hrootD
  by_cases hsigmaA : sigma < a
  · have hmassChild :=
      Polynomial.stationaryNormalize_smallPrimeStationaryMass_le hp f hdegree
        hprimitive mu hmu
    have hmaxChild : max 1 (Polynomial.smallPrimeStationaryMass
        (Polynomial.stationaryNormalize f p mu.val) p : ℝ) ≤ (m : ℝ) := by
      apply max_le
      · exact_mod_cast hmpos
      · exact_mod_cast hmassChild
    have hrec' :
        ‖polynomialCompleteSum (p ^ (a - sigma)) (pow_pos hp.pos _)
          (Polynomial.stationaryNormalize f p mu.val)‖ ≤
        Real.rpow d ((3 : ℝ) / d) * (m : ℝ) *
          Real.rpow p (((a - sigma : ℕ) : ℝ) *
            (1 - (1 : ℝ) / d)) := by
      calc
        _ ≤ Real.rpow d ((3 : ℝ) / d) *
            max 1 (Polynomial.smallPrimeStationaryMass
              (Polynomial.stationaryNormalize f p mu.val) p : ℝ) *
            Real.rpow p (((a - sigma : ℕ) : ℝ) *
              (1 - (1 : ℝ) / d)) := by simpa [sigma] using hrec hsigmaA
        _ ≤ Real.rpow d ((3 : ℝ) / d) * (m : ℝ) *
            Real.rpow p (((a - sigma : ℕ) : ℝ) *
              (1 - (1 : ℝ) / d)) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hmaxChild
              (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le d) _)
          · exact Real.rpow_nonneg (by exact_mod_cast Nat.zero_le p) _
    rw [ack_eq_2_5 hp (by omega : 2 ≤ a) f mu hroot
      hchild.translate_ne_zero (by simpa [sigma] using hsigmaA)]
    change (p : ℝ) ^ (sigma - 1) *
      ‖polynomialCompleteSum (p ^ (a - sigma)) (pow_pos hp.pos _)
        (Polynomial.stationaryNormalize f p mu.val)‖ ≤ _
    calc
      _ ≤ (p : ℝ) ^ (sigma - 1) *
          (Real.rpow d ((3 : ℝ) / d) * (m : ℝ) *
            Real.rpow p (((a - sigma : ℕ) : ℝ) *
              (1 - (1 : ℝ) / d))) := by
        exact mul_le_mul_of_nonneg_left hrec' (by positivity)
      _ = (m : ℝ) * Real.rpow d ((3 : ℝ) / d) *
          ((p : ℝ) ^ (sigma - 1) *
            Real.rpow p (((a - sigma : ℕ) : ℝ) *
              (1 - (1 : ℝ) / d))) := by ring
      _ ≤ (m : ℝ) * Real.rpow d ((3 : ℝ) / d) *
          Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) := by
        apply mul_le_mul_of_nonneg_left
        · exact ack_smallPrime_recursion_power hp d a sigma hd
            (by omega) hsigmaD hsigmaA.le
        · exact mul_nonneg (Nat.cast_nonneg _)
            (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le d) _)
      _ = _ := by simp [m]
  · have haSigma : a ≤ sigma := Nat.le_of_not_gt hsigmaA
    have hterminal := ack_smallPrime_terminal_power hp d a hd ha
      (haSigma.trans hsigmaD)
    calc
      ‖primePowerResidueClassSum p a hp f mu‖ ≤ (p : ℝ) ^ (a - 1) :=
        ack_residueClass_trivial hp ha f mu
      _ ≤ Real.rpow d ((3 : ℝ) / d) *
          Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) := hterminal
      _ ≤ (m : ℝ) * Real.rpow d ((3 : ℝ) / d) *
          Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) := by
        have hnonneg : 0 ≤ Real.rpow d ((3 : ℝ) / d) *
            Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) :=
          mul_nonneg
            (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le d) _)
            (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le p) _)
        calc
          _ = 1 * (Real.rpow d ((3 : ℝ) / d) *
              Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d))) := by ring
          _ ≤ (m : ℝ) * (Real.rpow d ((3 : ℝ) / d) *
              Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d))) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hmpos) hnonneg
          _ = _ := by ring
      _ = _ := by simp [m]

private theorem ack_smallPrime_strongPair
    [Fact p.Prime] (hp : p.Prime) (hpd : p ≤ d) (hd : 3 ≤ d) :
    ∀ a : ℕ, 0 < a → ∀ f : Polynomial ℤ,
      f.natDegree = d →
      (¬ p ∣ Polynomial.nonconstantContentNat f) →
      (‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
          Real.rpow d ((3 : ℝ) / d) *
            max 1 (Polynomial.smallPrimeStationaryMass f p : ℝ) *
            Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) ∧
        ∀ (_hblock : 2 * (Polynomial.derivativeContentOrder f p + 1) ≤ a)
          (mu : ZMod p), mu ∈ Polynomial.smallPrimeStationaryRoots f p →
          ‖primePowerResidueClassSum p a hp f mu‖ ≤
            (Polynomial.modPrime p
              (Polynomial.normalizedDerivative f p)).rootMultiplicity mu *
              Real.rpow d ((3 : ℝ) / d) *
              Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d))) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
      intro ha f hdegree hprimitive
      let C := Real.rpow d ((3 : ℝ) / d)
      let P := Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d))
      let S := Polynomial.smallPrimeStationaryRoots f p
      let mass := Polynomial.smallPrimeStationaryMass f p
      have hC1 : (1 : ℝ) ≤ C := by
        dsimp [C]
        exact Real.one_le_rpow
          (by exact_mod_cast (show 1 ≤ d by omega)) (by positivity)
      have hP0 : (0 : ℝ) ≤ P := by
        dsimp [P]
        exact Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _
      have hClass : ∀ (hblock :
          2 * (Polynomial.derivativeContentOrder f p + 1) ≤ a)
          (mu : ZMod p), mu ∈ S →
          ‖primePowerResidueClassSum p a hp f mu‖ ≤
            (Polynomial.modPrime p
              (Polynomial.normalizedDerivative f p)).rootMultiplicity mu * C * P := by
        intro hblock mu hmu
        have hmu' : mu ∈ Polynomial.smallPrimeStationaryRoots f p := by
          simpa [S] using hmu
        have hchild := Polynomial.stationaryChildInvariant hp f hdegree
          (by omega : 0 < d) hprimitive mu.val
        apply ack_eq_2_14_of_inductionBound hp ha f hdegree hd hpd hprimitive
          hblock mu hmu'
        intro hsigmaA
        let b := a - Polynomial.stationaryOrder f p mu.val
        have hbpos : 0 < b := by dsimp [b]; omega
        have hba : b < a := by
          dsimp [b]
          have hsigma1 := (Polynomial.ack_lemma_2_3 hp f hdegree.le
            hprimitive mu.val).1
          omega
        have hIH := (ih b hba hbpos
          (Polynomial.stationaryNormalize f p mu.val)
          hchild.natDegree_eq hchild.primitive).1
        simpa [b] using hIH
      have hTotal :
          ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
            C * max 1 (mass : ℝ) * P := by
        by_cases hblock :
            2 * (Polynomial.derivativeContentOrder f p + 1) ≤ a
        · have hsum :
              (∑ v : ZMod p, primePowerResidueClassSum p a hp f v) =
                ∑ mu ∈ S, primePowerResidueClassSum p a hp f mu := by
            calc
              (∑ v : ZMod p, primePowerResidueClassSum p a hp f v) =
                  ∑ v : ZMod p, if v ∈ S then
                    primePowerResidueClassSum p a hp f v else 0 := by
                apply Finset.sum_congr rfl
                intro v _hv
                by_cases hvS : v ∈ S
                · rw [if_pos hvS]
                · rw [if_neg hvS,
                    ack_smallPrime_block_vanish hp f hdegree hd hpd hprimitive
                      hblock v (by simpa [S] using hvS)]
              _ = ∑ mu ∈ S, primePowerResidueClassSum p a hp f mu := by simp
          rw [ack_completeSum_eq_sum_residueClasses hp ha f, hsum]
          calc
            ‖∑ mu ∈ S, primePowerResidueClassSum p a hp f mu‖ ≤
                ∑ mu ∈ S, ‖primePowerResidueClassSum p a hp f mu‖ :=
              norm_sum_le _ _
            _ ≤ ∑ mu ∈ S,
                ((Polynomial.modPrime p
                  (Polynomial.normalizedDerivative f p)).rootMultiplicity mu : ℝ) *
                    C * P := by
              apply Finset.sum_le_sum
              intro mu hmu
              exact hClass hblock mu hmu
            _ = (mass : ℝ) * C * P := by
              rw [← Finset.sum_mul, ← Finset.sum_mul]
              simp [mass, S, Polynomial.smallPrimeStationaryMass,
                Polynomial.rootMassModPrime,
                Polynomial.smallPrimeStationaryRoots]
            _ ≤ C * max 1 (mass : ℝ) * P := by
              have hmassMax : (mass : ℝ) ≤ max 1 (mass : ℝ) := le_max_right _ _
              calc
                (mass : ℝ) * C * P = C * (mass : ℝ) * P := by ring
                _ ≤ C * max 1 (mass : ℝ) * P :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hmassMax (le_trans zero_le_one hC1)) hP0
        · have ht := Polynomial.derivativeContent_pow_le_degree hp f hdegree hprimitive
          have htriv := completeSum_trivial (p ^ a) (pow_pos hp.pos a) f
          calc
            ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
                ((p ^ a : ℕ) : ℝ) := by exact_mod_cast htriv
            _ = (p : ℝ) ^ a := by norm_num
            _ ≤ C * P := by
              dsimp [C, P]
              exact ack_smallPrime_lowBlock_power hp d a
                (Polynomial.derivativeContentOrder f p) hd hpd ht (by omega)
            _ ≤ C * max 1 (mass : ℝ) * P := by
              have hmax : (1 : ℝ) ≤ max 1 (mass : ℝ) := le_max_left _ _
              apply mul_le_mul_of_nonneg_right _ hP0
              calc
                C = C * 1 := by ring
                _ ≤ C * max 1 (mass : ℝ) :=
                  mul_le_mul_of_nonneg_left hmax (le_trans zero_le_one hC1)
      exact ⟨by simpa [C, mass, P] using hTotal,
        fun hblock mu hmu ↦ by
          simpa [C, P, S] using hClass hblock mu (by simpa [S] using hmu)⟩

/-- ACK equation (2.13): the small-prime complete-sum estimate. -/
theorem ack_eq_2_13
    [Fact p.Prime] (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hpd : p ≤ d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    Real.rpow d ((3 : ℝ) / d) *
      max 1 (Polynomial.smallPrimeStationaryMass f p : ℝ) *
      Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) :=
  (ack_smallPrime_strongPair hp hpd hd a ha f hdegree hprimitive).1

/-- ACK equation (2.14): the small-prime estimate for an individual residue class. -/
theorem ack_eq_2_14
    [Fact p.Prime] (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hpd : p ≤ d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (hblock : 2 * (Polynomial.derivativeContentOrder f p + 1) ≤ a)
    (mu : ZMod p) (hmu : mu ∈ Polynomial.smallPrimeStationaryRoots f p) :
  ‖primePowerResidueClassSum p a hp f mu‖ ≤
    (Polynomial.modPrime p
      (Polynomial.normalizedDerivative f p)).rootMultiplicity mu *
      Real.rpow d ((3 : ℝ) / d) *
      Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) :=
  (ack_smallPrime_strongPair hp hpd hd a ha f hdegree hprimitive).2
    hblock mu hmu

private theorem ack_largePrime_weight_le
    (d m p : ℕ) (hd : 3 ≤ d) (hm : 1 ≤ m) (hmd : m ≤ d - 1)
    (hpB : chenMiddlePrimeThreshold d ≤ (p : ℝ)) :
    Real.rpow p ((m + 1 : ℝ) / d - 1) ≤ (m : ℝ) / (d - 1) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmdR : (m : ℝ) ≤ d - 1 := by
    have hmdCast : (m : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hmd
    simpa [Nat.cast_sub (by omega : 1 ≤ d)] using hmdCast
  have hbasePos : (0 : ℝ) < d - 1 := by linarith
  have hdenPos : (0 : ℝ) < d - 2 := by linarith
  have hpPos : (0 : ℝ) < p := by
    have hthresholdPos : 0 < chenMiddlePrimeThreshold d := by
      exact Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < d - 1) _
    linarith
  let theta : ℝ := ((m : ℝ) - 1) / (d - 2)
  let e : ℝ := ((m : ℝ) + 1) / d - 1
  have htheta0 : 0 ≤ theta :=
    div_nonneg (sub_nonneg.mpr hmR) hdenPos.le
  have htheta1 : theta ≤ 1 := by
    dsimp [theta]
    rw [div_le_one hdenPos]
    linarith
  have hbern : Real.rpow (d - 1 : ℝ) theta ≤ m := by
    have hb := rpow_one_add_le_one_add_mul_self
      (s := (d : ℝ) - 2) (p := theta) (by linarith) htheta0 htheta1
    rw [show (1 : ℝ) + (d - 2) = d - 1 by ring,
      show (1 : ℝ) + theta * (d - 2) = m by
        dsimp [theta]
        field_simp
        ring] at hb
    exact hb
  have heNonpos : e ≤ 0 := by
    dsimp [e]
    have hdPos : (0 : ℝ) < d := by linarith
    have hquot : ((m : ℝ) + 1) / d ≤ 1 := by
      rw [div_le_one hdPos]
      linarith
    linarith
  have hbase : Real.rpow p e ≤
      Real.rpow (chenMiddlePrimeThreshold d) e :=
    Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hbasePos _) hpB heNonpos
  have hthreshold : Real.rpow (chenMiddlePrimeThreshold d) e =
      Real.rpow (d - 1 : ℝ) (theta - 1) := by
    rw [chenMiddlePrimeThreshold]
    calc
      Real.rpow (Real.rpow (d - 1 : ℝ) ((d : ℝ) / (d - 2))) e =
          Real.rpow (d - 1 : ℝ) (((d : ℝ) / (d - 2)) * e) :=
        (Real.rpow_mul hbasePos.le _ _).symm
      _ = Real.rpow (d - 1 : ℝ) (theta - 1) := by
        congr 1
        dsimp [theta, e]
        field_simp
        ring
  rw [hthreshold] at hbase
  calc
    Real.rpow p ((m + 1 : ℝ) / d - 1) = Real.rpow p e := rfl
    _ ≤ Real.rpow (d - 1 : ℝ) (theta - 1) := hbase
    _ = Real.rpow (d - 1 : ℝ) theta / (d - 1) := by
      exact Real.rpow_sub_one hbasePos.ne' theta
    _ ≤ (m : ℝ) / (d - 1) := div_le_div_of_nonneg_right hbern hbasePos.le

private theorem ack_largePrime_recursion_power_eq
    {p : ℕ} (hp : p.Prime) (d a sigma : ℕ)
    (hsigma1 : 1 ≤ sigma) (hsigmaA : sigma ≤ a) :
    (p : ℝ) ^ (sigma - 1) *
        Real.rpow p (((a - sigma : ℕ) : ℝ) * (1 - (1 : ℝ) / d)) =
      Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) *
        Real.rpow p ((sigma : ℝ) / d - 1) := by
  have hpPosR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsigmaSub : ((sigma - 1 : ℕ) : ℝ) = (sigma : ℝ) - 1 := by
    rw [Nat.cast_sub hsigma1]
    norm_num
  have haSub : ((a - sigma : ℕ) : ℝ) = (a : ℝ) - sigma := by
    rw [Nat.cast_sub hsigmaA]
  calc
    (p : ℝ) ^ (sigma - 1) *
        Real.rpow p (((a - sigma : ℕ) : ℝ) * (1 - (1 : ℝ) / d)) =
      Real.rpow p ((sigma - 1 : ℕ) : ℝ) *
        Real.rpow p (((a - sigma : ℕ) : ℝ) * (1 - (1 : ℝ) / d)) := by
          exact congrArg
            (· * Real.rpow p (((a - sigma : ℕ) : ℝ) *
              (1 - (1 : ℝ) / d)))
            (Real.rpow_natCast (p : ℝ) (sigma - 1)).symm
    _ = Real.rpow p (((sigma - 1 : ℕ) : ℝ) +
        ((a - sigma : ℕ) : ℝ) * (1 - (1 : ℝ) / d)) :=
      (Real.rpow_add hpPosR _ _).symm
    _ = Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d) +
        ((sigma : ℝ) / d - 1)) := by
      congr 1
      rw [hsigmaSub, haSub]
      field_simp
      ring
    _ = _ := Real.rpow_add hpPosR _ _

private theorem ack_largePrime_terminal_power
    {p : ℕ} (hp : p.Prime) (d a sigma : ℕ) (hd : 0 < d) (ha : 0 < a)
    (haSigma : a ≤ sigma) :
    (p : ℝ) ^ (a - 1) ≤
      Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) *
        Real.rpow p ((sigma : ℝ) / d - 1) := by
  have hpOneR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have haSub : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub ha]
    norm_num
  have hexp : ((a - 1 : ℕ) : ℝ) ≤
      (a : ℝ) * (1 - (1 : ℝ) / d) + ((sigma : ℝ) / d - 1) := by
    have haSigmaR : (a : ℝ) ≤ sigma := by exact_mod_cast haSigma
    rw [haSub]
    have hdPos : (0 : ℝ) < d := by exact_mod_cast hd
    field_simp
    nlinarith
  calc
    (p : ℝ) ^ (a - 1) = Real.rpow p ((a - 1 : ℕ) : ℝ) :=
      (Real.rpow_natCast (p : ℝ) (a - 1)).symm
    _ ≤ Real.rpow p
        ((a : ℝ) * (1 - (1 : ℝ) / d) + ((sigma : ℝ) / d - 1)) :=
      Real.rpow_le_rpow_of_exponent_le hpOneR hexp
    _ = _ := Real.rpow_add (by exact_mod_cast hp.pos) _ _

private theorem ack_largePrime_stationaryWeight_sum_le
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hdp : d < p)
    (hpB : chenMiddlePrimeThreshold d ≤ (p : ℝ))
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
    ∑ mu ∈ Polynomial.derivativeRoots f p,
        Real.rpow p ((Polynomial.stationaryOrder f p mu.val : ℝ) / d - 1) ≤ 1 := by
  let mult : ZMod p → ℕ := fun mu ↦
    (Polynomial.modPrime p f.derivative).rootMultiplicity mu
  have hmod := chen_derivative_modPrime_ne_zero hp f hdegree hdp hprimitive
  have hmass := Polynomial.derivativeRootMass_le hp f hdegree hdp hprimitive
  have hpOneR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpoint : ∀ mu ∈ Polynomial.derivativeRoots f p,
      Real.rpow p ((Polynomial.stationaryOrder f p mu.val : ℝ) / d - 1) ≤
        (mult mu : ℝ) / (d - 1) := by
    intro mu hmu
    have hroot : (Polynomial.modPrime p f.derivative).IsRoot mu := by
      simpa [Polynomial.derivativeRoots, Polynomial.rootsModPrime] using hmu
    have hmpos : 1 ≤ mult mu := by
      dsimp [mult]
      exact (Polynomial.rootMultiplicity_pos hmod).mpr hroot
    have hmMass : mult mu ≤ Polynomial.derivativeRootMass f p := by
      rw [Polynomial.derivativeRootMass]
      exact Finset.single_le_sum
        (fun i _hi ↦ Nat.zero_le
          ((Polynomial.modPrime p f.derivative).rootMultiplicity i)) hmu
    have hmd : mult mu ≤ d - 1 := hmMass.trans hmass
    have hsigma := Polynomial.stationaryOrder_le_rootMultiplicity_succ
      hp f hdegree hdp hprimitive mu hroot
    calc
      Real.rpow p ((Polynomial.stationaryOrder f p mu.val : ℝ) / d - 1) ≤
          Real.rpow p (((mult mu + 1 : ℕ) : ℝ) / d - 1) := by
        apply Real.rpow_le_rpow_of_exponent_le hpOneR
        have hsigmaR : (Polynomial.stationaryOrder f p mu.val : ℝ) ≤
            (mult mu + 1 : ℕ) := by exact_mod_cast hsigma
        gcongr
      _ = Real.rpow p ((mult mu + 1 : ℝ) / d - 1) := by norm_num
      _ ≤ (mult mu : ℝ) / (d - 1) :=
        ack_largePrime_weight_le d (mult mu) p hd hmpos hmd hpB
  calc
    ∑ mu ∈ Polynomial.derivativeRoots f p,
        Real.rpow p ((Polynomial.stationaryOrder f p mu.val : ℝ) / d - 1) ≤
      ∑ mu ∈ Polynomial.derivativeRoots f p, (mult mu : ℝ) / (d - 1) := by
        apply Finset.sum_le_sum
        intro mu hmu
        exact hpoint mu hmu
    _ = (Polynomial.derivativeRootMass f p : ℝ) / (d - 1) := by
      rw [← Finset.sum_div]
      simp [Polynomial.derivativeRootMass, Polynomial.rootMassModPrime,
        Polynomial.derivativeRoots, Polynomial.rootsModPrime, mult]
    _ ≤ 1 := by
      have hmassR : (Polynomial.derivativeRootMass f p : ℝ) ≤ d - 1 := by
        have hmassCast : (Polynomial.derivativeRootMass f p : ℝ) ≤
            ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hmass
        simpa [Nat.cast_sub (by omega : 1 ≤ d)] using hmassCast
      have hden : (0 : ℝ) < (d : ℝ) - 1 := by
        have hdReal : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      rw [div_le_one hden]
      exact hmassR

private theorem ack_largePrime_induction
    [Fact p.Prime] (hp : p.Prime) (d : ℕ) (hd : 3 ≤ d) (hdp : d < p)
    (hpB : chenMiddlePrimeThreshold d ≤ (p : ℝ))
    (K : ℝ) (hK1 : 1 ≤ K)
    (hprime : ∀ F : Polynomial ℤ, F.natDegree = d →
      (¬ p ∣ Polynomial.nonconstantContentNat F) →
      ‖polynomialCompleteSum p hp.pos F‖ ≤
        K * Real.rpow p (1 - (1 : ℝ) / d)) :
    ∀ a : ℕ, 0 < a → ∀ F : Polynomial ℤ,
      F.natDegree = d →
      (¬ p ∣ Polynomial.nonconstantContentNat F) →
      ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) F‖ ≤
        K * Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d)) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
      intro ha F hdegree hprimitive
      by_cases haone : a = 1
      · subst a
        simpa using hprime F hdegree hprimitive
      · have ha2 : 2 ≤ a := by omega
        let P := Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d))
        let R := Polynomial.derivativeRoots F p
        have hKP0 : 0 ≤ K * P := by
          exact mul_nonneg (le_trans zero_le_one hK1)
            (Real.rpow_nonneg (by exact_mod_cast hp.pos.le) _)
        have hclass : ∀ mu ∈ R,
            ‖primePowerResidueClassSum p a hp F mu‖ ≤
              K * P * Real.rpow p
                ((Polynomial.stationaryOrder F p mu.val : ℝ) / d - 1) := by
          intro mu hmu
          have hroot : (Polynomial.modPrime p F.derivative).IsRoot mu := by
            simpa [R, Polynomial.derivativeRoots,
              Polynomial.rootsModPrime] using hmu
          have hchild := Polynomial.stationaryChildInvariant hp F hdegree
            (by omega : 0 < d) hprimitive mu.val
          let sigma := Polynomial.stationaryOrder F p mu.val
          have hsigma2 : 2 ≤ sigma := by
            dsimp [sigma]
            exact Polynomial.stationaryOrder_two_le_of_isRoot hp F mu
              hchild.translate_ne_zero hroot
          by_cases hsigmaA : sigma < a
          · let b := a - sigma
            have hbpos : 0 < b := by dsimp [b]; omega
            have hba : b < a := by dsimp [b]; omega
            have hIH := ih b hba hbpos
              (Polynomial.stationaryNormalize F p mu.val)
              hchild.natDegree_eq hchild.primitive
            rw [ack_eq_2_5 hp ha2 F mu hroot hchild.translate_ne_zero
              (by simpa [sigma] using hsigmaA)]
            change (p : ℝ) ^ (sigma - 1) *
              ‖polynomialCompleteSum (p ^ b) (pow_pos hp.pos _)
                (Polynomial.stationaryNormalize F p mu.val)‖ ≤ _
            calc
              _ ≤ (p : ℝ) ^ (sigma - 1) *
                  (K * Real.rpow p ((b : ℝ) *
                    (1 - (1 : ℝ) / d))) := by
                apply mul_le_mul_of_nonneg_left
                · exact hIH
                · positivity
              _ = K * ((p : ℝ) ^ (sigma - 1) *
                  Real.rpow p ((b : ℝ) * (1 - (1 : ℝ) / d))) := by ring
              _ = K * (P * Real.rpow p ((sigma : ℝ) / d - 1)) := by
                rw [show (b : ℕ) = a - sigma from rfl,
                  ack_largePrime_recursion_power_eq hp d a sigma
                    (by omega) hsigmaA.le]
              _ = _ := by ring
          · have haSigma : a ≤ sigma := Nat.le_of_not_gt hsigmaA
            have hterminal := ack_largePrime_terminal_power hp d a sigma
              (by omega : 0 < d) ha haSigma
            calc
              ‖primePowerResidueClassSum p a hp F mu‖ ≤ (p : ℝ) ^ (a - 1) :=
                ack_residueClass_trivial hp ha F mu
              _ ≤ P * Real.rpow p ((sigma : ℝ) / d - 1) := by
                simpa [P] using hterminal
              _ ≤ K * (P * Real.rpow p ((sigma : ℝ) / d - 1)) := by
                have htermNonneg : 0 ≤
                    P * Real.rpow p ((sigma : ℝ) / d - 1) :=
                  mul_nonneg
                    (by dsimp [P]; exact Real.rpow_nonneg (by positivity) _)
                    (Real.rpow_nonneg (by positivity) _)
                simpa using mul_le_mul_of_nonneg_right hK1 htermNonneg
              _ = _ := by ring
        have hsumRoots :
            (∑ mu : ZMod p, primePowerResidueClassSum p a hp F mu) =
              ∑ mu ∈ R, primePowerResidueClassSum p a hp F mu := by
          calc
            (∑ mu : ZMod p, primePowerResidueClassSum p a hp F mu) =
                ∑ mu : ZMod p, if mu ∈ R then
                  primePowerResidueClassSum p a hp F mu else 0 := by
              apply Finset.sum_congr rfl
              intro mu _hmu
              by_cases hroot : mu ∈ R
              · rw [if_pos hroot]
              · rw [if_neg hroot, ack_eq_2_3_vanish hp ha2 F mu]
                simpa [R, Polynomial.derivativeRoots,
                  Polynomial.rootsModPrime] using hroot
            _ = ∑ mu ∈ R, primePowerResidueClassSum p a hp F mu := by simp
        have hweights := ack_largePrime_stationaryWeight_sum_le
          hp F hdegree hd hdp hpB hprimitive
        rw [ack_completeSum_eq_sum_residueClasses hp ha F, hsumRoots]
        calc
          ‖∑ mu ∈ R, primePowerResidueClassSum p a hp F mu‖ ≤
              ∑ mu ∈ R, ‖primePowerResidueClassSum p a hp F mu‖ :=
            norm_sum_le _ _
          _ ≤ ∑ mu ∈ R, K * P * Real.rpow p
              ((Polynomial.stationaryOrder F p mu.val : ℝ) / d - 1) := by
            apply Finset.sum_le_sum
            intro mu hmu
            exact hclass mu hmu
          _ = K * P * (∑ mu ∈ R, Real.rpow p
              ((Polynomial.stationaryOrder F p mu.val : ℝ) / d - 1)) := by
            rw [Finset.mul_sum]
          _ ≤ K * P * 1 := mul_le_mul_of_nonneg_left
            (by simpa [R] using hweights) hKP0
          _ = _ := by simp [P]

private theorem ack_primeBase_coefficient_middle
    (d p : ℕ) (hd : 3 ≤ d) (_hp : p.Prime) :
    min (Real.rpow p ((1 : ℝ) / d))
        ((d - 1 : ℝ) * Real.rpow p (-(1 : ℝ) / 2 + (1 : ℝ) / d)) ≤
      Real.rpow d ((2 : ℝ) / d) := by
  let C := Real.rpow d ((2 : ℝ) / d)
  let e : ℝ := -(1 : ℝ) / 2 + (1 : ℝ) / d
  have hdPos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hpNonneg : (0 : ℝ) ≤ p := by positivity
  have hCpos : 0 < C := Real.rpow_pos_of_pos hdPos _
  have heNonpos : e ≤ 0 := by
    dsimp [e]
    have hhalf : (1 : ℝ) / d ≤ (1 : ℝ) / 2 :=
      div_le_div_of_nonneg_left zero_le_one (by norm_num)
        (by exact_mod_cast (show 2 ≤ d by omega))
    linarith
  by_cases hx : Real.rpow p ((1 : ℝ) / d) ≤ C
  · exact (min_le_left _ _).trans hx
  · have hxlt : C < Real.rpow p ((1 : ℝ) / d) := lt_of_not_ge hx
    have hCpow : C ^ d = (d : ℝ) ^ 2 := by
      dsimp [C]
      rw [← Real.rpow_mul_natCast (le_of_lt hdPos)]
      calc
        Real.rpow d (((2 : ℝ) / d) * d) = Real.rpow d 2 := by
          congr 1
          field_simp
        _ = (d : ℝ) ^ 2 := Real.rpow_natCast _ _
    have hxpow : C ^ d < (Real.rpow p ((1 : ℝ) / d)) ^ d := by
      exact pow_lt_pow_left₀ hxlt hCpos.le (by omega : d ≠ 0)
    have hrootpow : (Real.rpow p ((1 : ℝ) / d)) ^ d = (p : ℝ) := by
      have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdPos
      simpa [div_eq_mul_inv] using
        Real.rpow_inv_natCast_pow hpNonneg (by omega : d ≠ 0)
    have hbase : (d : ℝ) ^ 2 ≤ p := by
      rw [hCpow, hrootpow] at hxpow
      exact hxpow.le
    have hrpow : Real.rpow p e ≤ Real.rpow ((d : ℝ) ^ 2) e :=
      Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hdPos) hbase heNonpos
    have hrpowBase : Real.rpow ((d : ℝ) ^ 2) e = C / d := by
      calc
        Real.rpow ((d : ℝ) ^ 2) e = Real.rpow d ((2 : ℝ) * e) := by
          exact (Real.rpow_natCast_mul hdPos.le 2 e).symm
        _ = Real.rpow d ((2 : ℝ) / d - 1) := by
          congr 1
          dsimp [e]
          ring
        _ = C / d := by
          simpa [C] using Real.rpow_sub_one hdPos.ne' ((2 : ℝ) / d)
    have hdSub : (d - 1 : ℝ) ≤ d := by
      have hdsubCast : ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.sub_le d 1
      rw [Nat.cast_sub (by omega : 1 ≤ d)] at hdsubCast
      norm_num at hdsubCast ⊢
    calc
      min (Real.rpow p ((1 : ℝ) / d))
          ((d - 1 : ℝ) * Real.rpow p e) ≤
        (d - 1 : ℝ) * Real.rpow p e := min_le_right _ _
      _ ≤ (d - 1 : ℝ) * (C / d) :=
        mul_le_mul_of_nonneg_left (hrpow.trans_eq hrpowBase)
          (by positivity)
      _ ≤ (d : ℝ) * (C / d) :=
        mul_le_mul_of_nonneg_right hdSub (by positivity)
      _ = C := by field_simp
      _ = _ := rfl

private theorem ack_primeBase_coefficient_large
    (d p : ℕ) (hd : 3 ≤ d)
    (hpA : chenLargePrimeThreshold d < (p : ℝ)) :
    (d - 1 : ℝ) * Real.rpow p (-(1 : ℝ) / 2 + (1 : ℝ) / d) ≤ 1 := by
  let e : ℝ := -(1 : ℝ) / 2 + (1 : ℝ) / d
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hbasePos : (0 : ℝ) < d - 1 := by linarith
  have hdenPos : (0 : ℝ) < d - 2 := by linarith
  have heNonpos : e ≤ 0 := by
    dsimp [e]
    have hhalf : (1 : ℝ) / d ≤ (1 : ℝ) / 2 :=
      div_le_div_of_nonneg_left zero_le_one (by norm_num)
        (by exact_mod_cast (show 2 ≤ d by omega))
    linarith
  have hrpow : Real.rpow p e ≤ Real.rpow (chenLargePrimeThreshold d) e :=
    Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hbasePos _) hpA.le heNonpos
  have hthreshold : Real.rpow (chenLargePrimeThreshold d) e =
      1 / (d - 1 : ℝ) := by
    rw [chenLargePrimeThreshold]
    calc
      Real.rpow (Real.rpow (d - 1 : ℝ) ((2 * d : ℝ) / (d - 2))) e =
          Real.rpow (d - 1 : ℝ) (((2 * d : ℝ) / (d - 2)) * e) :=
        (Real.rpow_mul hbasePos.le _ _).symm
      _ = Real.rpow (d - 1 : ℝ) (-1) := by
        congr 1
        dsimp [e]
        field_simp
        ring
      _ = 1 / (d - 1 : ℝ) := by
        simpa [one_div] using Real.rpow_neg_one (d - 1 : ℝ)
  calc
    (d - 1 : ℝ) * Real.rpow p (-(1 : ℝ) / 2 + (1 : ℝ) / d) =
        (d - 1 : ℝ) * Real.rpow p e := rfl
    _ ≤ (d - 1 : ℝ) * (1 / (d - 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hrpow.trans_eq hthreshold) hbasePos.le
    _ = 1 := by field_simp

private theorem chenMiddlePrimeThreshold_ge_degree
    (d : ℕ) (hd : 3 ≤ d) :
    (d : ℝ) < chenMiddlePrimeThreshold d := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < d - 2 := by linarith
  have hexp : (1 : ℝ) ≤ (d : ℝ) / (d - 2) := by
    rw [le_div_iff₀ hden]
    linarith
  have hb := one_add_mul_self_le_rpow_one_add
    (s := (d : ℝ) - 2) (by linarith : (-1 : ℝ) ≤ d - 2) hexp
  rw [show (1 : ℝ) + (d - 2) = d - 1 by ring] at hb
  rw [show (1 : ℝ) + ((d : ℝ) / (d - 2)) * (d - 2) = d + 1 by
    field_simp
    ring] at hb
  exact (lt_add_one (d : ℝ)).trans_le hb

private theorem chenMiddlePrimeThreshold_le_large
    (d : ℕ) (hd : 3 ≤ d) :
    chenMiddlePrimeThreshold d ≤ chenLargePrimeThreshold d := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : (1 : ℝ) ≤ d - 1 := by linarith
  have hden : (0 : ℝ) < d - 2 := by linarith
  rw [chenMiddlePrimeThreshold, chenLargePrimeThreshold]
  apply Real.rpow_le_rpow_of_exponent_le hbase
  rw [div_le_div_iff₀ hden hden]
  nlinarith

private theorem rpow_natPrimePower
    (p a : ℕ) (hp : 0 < p) (x : ℝ) :
    Real.rpow (p ^ a : ℝ) x = Real.rpow p ((a : ℝ) * x) := by
  have hpR : (0 : ℝ) ≤ p := by exact_mod_cast hp.le
  calc
    Real.rpow (p ^ a : ℝ) x = Real.rpow ((p : ℝ) ^ a) x := by norm_num
    _ = Real.rpow p ((a : ℝ) * x) :=
      (Real.rpow_natCast_mul hpR a x).symm

/-- The explicit local loss factor attached to a prime divisor of the modulus. -/
noncomputable def chenLocalFactor (d p : ℕ) : ℝ :=
  if chenLargePrimeThreshold d < (p : ℝ) then 1
  else if chenMiddlePrimeThreshold d ≤ (p : ℝ) then
    Real.rpow d ((2 : ℝ) / d)
  else if d < p then Real.rpow d ((3 : ℝ) / d)
  else (d - 1 : ℝ) * Real.rpow d ((3 : ℝ) / d)

/-- The complete-sum estimate for every prime power, conditional on the
prime-modulus input. -/
theorem primePower_completeSum_bound_of_primeBound
    (hWeil : PolynomialPrimeSumBound)
    (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    chenLocalFactor d p *
      Real.rpow (p ^ a : ℝ) (1 - (1 : ℝ) / d) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let alpha : ℝ := 1 - (1 : ℝ) / d
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : Real.rpow (p ^ a : ℝ) alpha =
      Real.rpow p ((a : ℝ) * alpha) :=
    rpow_natPrimePower p a hp.pos alpha
  by_cases hpd : p ≤ d
  · have hthreshold := chenMiddlePrimeThreshold_ge_degree d hd
    have hmidLarge := chenMiddlePrimeThreshold_le_large d hd
    have hpMid : ¬ chenMiddlePrimeThreshold d ≤ (p : ℝ) := by
      have hpdR : (p : ℝ) ≤ d := by exact_mod_cast hpd
      linarith
    have hpLarge : ¬ chenLargePrimeThreshold d < (p : ℝ) := by
      have hpdR : (p : ℝ) ≤ d := by exact_mod_cast hpd
      linarith
    have hsmall := ack_eq_2_13 hp ha f hdegree hd hpd hprimitive
    have hmass := Polynomial.smallPrimeStationaryMass_le_degree
      hp f hdegree hprimitive
    have hmax : max 1 (Polynomial.smallPrimeStationaryMass f p : ℝ) ≤
        (d - 1 : ℕ) := by
      apply max_le
      · exact_mod_cast (show 1 ≤ d - 1 by omega)
      · exact_mod_cast hmass
    have hmaxR : max 1 (Polynomial.smallPrimeStationaryMass f p : ℝ) ≤
        (d : ℝ) - 1 := by
      simpa [Nat.cast_sub (by omega : 1 ≤ d)] using hmax
    rw [chenLocalFactor, if_neg hpLarge, if_neg hpMid, if_neg (by omega : ¬ d < p),
      hpow]
    calc
      ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
          Real.rpow d ((3 : ℝ) / d) *
            max 1 (Polynomial.smallPrimeStationaryMass f p : ℝ) *
            Real.rpow p ((a : ℝ) * alpha) := by simpa [alpha] using hsmall
      _ ≤ Real.rpow d ((3 : ℝ) / d) * (d - 1 : ℝ) *
          Real.rpow p ((a : ℝ) * alpha) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hmaxR
            (Real.rpow_nonneg (by positivity) _)
        · exact Real.rpow_nonneg hpR.le _
      _ = (d - 1 : ℝ) * Real.rpow d ((3 : ℝ) / d) *
          Real.rpow p ((a : ℝ) * alpha) := by ring
  · have hdp : d < p := by omega
    by_cases hpLarge : chenLargePrimeThreshold d < (p : ℝ)
    · have hpMid : chenMiddlePrimeThreshold d ≤ (p : ℝ) :=
        (chenMiddlePrimeThreshold_le_large d hd).trans hpLarge.le
      have hprime : ∀ F : Polynomial ℤ, F.natDegree = d →
          (¬ p ∣ Polynomial.nonconstantContentNat F) →
          ‖polynomialCompleteSum p hp.pos F‖ ≤
            (1 : ℝ) * Real.rpow p alpha := by
        intro F hFdegree hFprimitive
        have hb := chen_prime_base_of hWeil hp F hFdegree hd hdp hFprimitive
        have hcoeff : min (Real.rpow p ((1 : ℝ) / d))
            ((d - 1 : ℝ) * Real.rpow p (-(1 : ℝ) / 2 + (1 : ℝ) / d)) ≤ 1 :=
          (min_le_right _ _).trans
            (ack_primeBase_coefficient_large d p hd hpLarge)
        exact hb.trans (mul_le_mul_of_nonneg_right hcoeff
          (Real.rpow_nonneg hpR.le _))
      have hlarge := ack_largePrime_induction hp d hd hdp hpMid 1 le_rfl
        hprime a ha f hdegree hprimitive
      rw [chenLocalFactor, if_pos hpLarge, hpow]
      simpa [alpha] using hlarge
    · by_cases hpMid : chenMiddlePrimeThreshold d ≤ (p : ℝ)
      · let C₂ := Real.rpow d ((2 : ℝ) / d)
        have hC₂1 : (1 : ℝ) ≤ C₂ := by
          dsimp [C₂]
          exact Real.one_le_rpow (by linarith : (1 : ℝ) ≤ d) (by positivity)
        have hprime : ∀ F : Polynomial ℤ, F.natDegree = d →
            (¬ p ∣ Polynomial.nonconstantContentNat F) →
            ‖polynomialCompleteSum p hp.pos F‖ ≤ C₂ * Real.rpow p alpha := by
          intro F hFdegree hFprimitive
          have hb := chen_prime_base_of hWeil hp F hFdegree hd hdp hFprimitive
          exact hb.trans (mul_le_mul_of_nonneg_right
            (ack_primeBase_coefficient_middle d p hd hp)
            (Real.rpow_nonneg hpR.le _))
        have hmiddle := ack_largePrime_induction hp d hd hdp hpMid C₂ hC₂1
          hprime a ha f hdegree hprimitive
        rw [chenLocalFactor, if_neg hpLarge, if_pos hpMid, hpow]
        simpa [alpha, C₂] using hmiddle
      · have hC₂C₃ : Real.rpow d ((2 : ℝ) / d) ≤
            Real.rpow d ((3 : ℝ) / d) := by
          apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ d)
          gcongr
          norm_num
        have hbaseC₃ : ∀ F : Polynomial ℤ, F.natDegree = d →
            (¬ p ∣ Polynomial.nonconstantContentNat F) →
            ‖polynomialCompleteSum p hp.pos F‖ ≤
              Real.rpow d ((3 : ℝ) / d) * Real.rpow p alpha := by
          intro F hFdegree hFprimitive
          have hb := chen_prime_base_of hWeil hp F hFdegree hd hdp hFprimitive
          have hcoeff := (ack_primeBase_coefficient_middle d p hd hp).trans hC₂C₃
          exact hb.trans (mul_le_mul_of_nonneg_right hcoeff
            (Real.rpow_nonneg hpR.le _))
        have hmedium :
            ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
              Real.rpow d ((3 : ℝ) / d) *
                Real.rpow p ((a : ℝ) * alpha) := by
          by_cases haone : a = 1
          · subst a
            simpa using hbaseC₃ f hdegree hprimitive
          · have ha2 : 2 ≤ a := by omega
            have h26 := ack_eq_2_6 hp ha2 f hdegree hd hdp
              (le_of_not_ge hpMid) hprimitive
            have hmass := Polynomial.derivativeRootMass_le hp f hdegree hdp hprimitive
            let e : ℝ := -1 + (3 : ℝ) / d
            have heNonpos : e ≤ 0 := by
              dsimp [e]
              have : (3 : ℝ) / d ≤ 1 := by
                rw [div_le_one (by linarith : (0 : ℝ) < d)]
                exact hdR
              linarith
            have hrpow : Real.rpow p e ≤ Real.rpow d e :=
              Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < d)
                (by exact_mod_cast hdp.le) heNonpos
            have hmassR : (Polynomial.derivativeRootMass f p : ℝ) ≤ d - 1 := by
              have hc : (Polynomial.derivativeRootMass f p : ℝ) ≤
                  ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hmass
              simpa [Nat.cast_sub (by omega : 1 ≤ d)] using hc
            have hcoeff : (Polynomial.derivativeRootMass f p : ℝ) *
                Real.rpow p e ≤ Real.rpow d ((3 : ℝ) / d) := by
              calc
                _ ≤ (d - 1 : ℝ) * Real.rpow d e := by
                  exact mul_le_mul hmassR hrpow
                    (Real.rpow_nonneg hpR.le _) (by linarith)
                _ ≤ (d : ℝ) * Real.rpow d e := by
                  apply mul_le_mul_of_nonneg_right (by linarith)
                  exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ d) _
                _ = Real.rpow d ((3 : ℝ) / d) := by
                  calc
                    (d : ℝ) * Real.rpow d e =
                        Real.rpow d 1 * Real.rpow d e :=
                      congrArg (· * Real.rpow d e) (Real.rpow_one (d : ℝ)).symm
                    _ = Real.rpow d (1 + e) :=
                      (Real.rpow_add (by linarith : (0 : ℝ) < d) 1 e).symm
                    _ = _ := by
                      congr 1
                      dsimp [e]
                      ring
            calc
              _ ≤ (Polynomial.derivativeRootMass f p : ℝ) *
                  Real.rpow p (e + (a : ℝ) * alpha) := by
                simpa [e, alpha, add_assoc, add_comm, add_left_comm] using h26
              _ = ((Polynomial.derivativeRootMass f p : ℝ) *
                    Real.rpow p e) * Real.rpow p ((a : ℝ) * alpha) := by
                calc
                  (Polynomial.derivativeRootMass f p : ℝ) *
                      Real.rpow p (e + (a : ℝ) * alpha) =
                    (Polynomial.derivativeRootMass f p : ℝ) *
                      (Real.rpow p e * Real.rpow p ((a : ℝ) * alpha)) :=
                    congrArg ((Polynomial.derivativeRootMass f p : ℝ) * ·)
                      (Real.rpow_add hpR e ((a : ℝ) * alpha))
                  _ = _ := by ring
              _ ≤ Real.rpow d ((3 : ℝ) / d) *
                  Real.rpow p ((a : ℝ) * alpha) :=
                mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hpR.le _)
        rw [chenLocalFactor, if_neg hpLarge, if_neg hpMid, if_pos hdp, hpow]
        exact hmedium

private theorem stdAddChar_crt
    {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    {u₁ u₂ n : ℤ}
    (hbezout : u₁ * (q₂ : ℤ) + u₂ * (q₁ : ℤ) = 1) :
    letI : NeZero q₁ := ⟨hq₁.ne'⟩
    letI : NeZero q₂ := ⟨hq₂.ne'⟩
    letI : NeZero (q₁ * q₂) := ⟨(Nat.mul_pos hq₁ hq₂).ne'⟩
    ZMod.stdAddChar (n : ZMod (q₁ * q₂)) =
      ZMod.stdAddChar ((u₁ * n : ℤ) : ZMod q₁) *
        ZMod.stdAddChar ((u₂ * n : ℤ) : ZMod q₂) := by
  let _ : NeZero q₁ := ⟨hq₁.ne'⟩
  let _ : NeZero q₂ := ⟨hq₂.ne'⟩
  let _ : NeZero (q₁ * q₂) := ⟨(Nat.mul_pos hq₁ hq₂).ne'⟩
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe,
    ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hbezoutC : (u₁ : ℂ) * q₂ + (u₂ : ℂ) * q₁ = 1 := by
    exact_mod_cast hbezout
  have hq₁C : (q₁ : ℂ) ≠ 0 := by exact_mod_cast hq₁.ne'
  have hq₂C : (q₂ : ℂ) ≠ 0 := by exact_mod_cast hq₂.ne'
  have hfrac : (n : ℂ) / (q₁ * q₂) =
      (u₁ * n : ℂ) / q₁ + (u₂ * n : ℂ) / q₂ := by
    field_simp [hq₁C, hq₂C]
    have hb : (q₂ : ℂ) * u₁ + q₁ * u₂ = 1 := by
      simpa [mul_comm] using hbezoutC
    rw [hb, mul_one]
  push_cast
  calc
    2 * (Real.pi : ℂ) * Complex.I * n / (q₁ * q₂) =
        2 * (Real.pi : ℂ) * Complex.I * (n / (q₁ * q₂)) := by ring
    _ = 2 * (Real.pi : ℂ) * Complex.I *
        ((u₁ * n) / q₁ + (u₂ * n) / q₂) := by rw [hfrac]
    _ = 2 * (Real.pi : ℂ) * Complex.I * (u₁ * n) / q₁ +
        2 * (Real.pi : ℂ) * Complex.I * (u₂ * n) / q₂ := by ring

private theorem polynomialPhase_crt
    {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    {u₁ u₂ : ℤ}
    (hbezout : u₁ * (q₂ : ℤ) + u₂ * (q₁ : ℤ) = 1)
    (f : Polynomial ℤ) (x : ZMod (q₁ * q₂)) :
    letI : NeZero q₁ := ⟨hq₁.ne'⟩
    letI : NeZero q₂ := ⟨hq₂.ne'⟩
    letI : NeZero (q₁ * q₂) := ⟨(Nat.mul_pos hq₁ hq₂).ne'⟩
    ZMod.stdAddChar (Polynomial.eval x
      (f.map (Int.castRingHom (ZMod (q₁ * q₂))))) =
      ZMod.stdAddChar (Polynomial.eval (ZMod.cast x : ZMod q₁)
        ((Polynomial.C u₁ * f).map (Int.castRingHom (ZMod q₁)))) *
      ZMod.stdAddChar (Polynomial.eval (ZMod.cast x : ZMod q₂)
        ((Polynomial.C u₂ * f).map (Int.castRingHom (ZMod q₂)))) := by
  let _ : NeZero q₁ := ⟨hq₁.ne'⟩
  let _ : NeZero q₂ := ⟨hq₂.ne'⟩
  let _ : NeZero (q₁ * q₂) := ⟨(Nat.mul_pos hq₁ hq₂).ne'⟩
  have hchar := stdAddChar_crt hq₁ hq₂
    (n := f.eval (x.val : ℤ)) hbezout
  have hx : ((x.val : ℕ) : ZMod (q₁ * q₂)) = x := ZMod.natCast_zmod_val x
  have heval0 : Polynomial.eval x
      (f.map (Int.castRingHom (ZMod (q₁ * q₂)))) =
      ((f.eval (x.val : ℤ) : ℤ) : ZMod (q₁ * q₂)) := by
    conv_lhs => rw [← hx]
    simpa using polynomialEval_map_intCast (q₁ * q₂) f (x.val : ℤ)
  have heval1 : Polynomial.eval (ZMod.cast x : ZMod q₁)
      ((Polynomial.C u₁ * f).map (Int.castRingHom (ZMod q₁))) =
      ((u₁ * f.eval (x.val : ℤ) : ℤ) : ZMod q₁) := by
    rw [ZMod.cast_eq_val]
    simpa [Polynomial.eval_mul] using
      polynomialEval_map_intCast q₁ (Polynomial.C u₁ * f) x.val
  have heval2 : Polynomial.eval (ZMod.cast x : ZMod q₂)
      ((Polynomial.C u₂ * f).map (Int.castRingHom (ZMod q₂))) =
      ((u₂ * f.eval (x.val : ℤ) : ℤ) : ZMod q₂) := by
    rw [ZMod.cast_eq_val]
    simpa [Polynomial.eval_mul] using
      polynomialEval_map_intCast q₂ (Polynomial.C u₂ * f) x.val
  rw [heval0, heval1, heval2]
  exact hchar

/-- Chinese-remainder factorization of a complete polynomial sum at coprime moduli. -/
theorem polynomialCompleteSum_crt
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hcop : Nat.Coprime q₁ q₂)
    {u₁ u₂ : ℤ}
    (hbezout : u₁ * (q₂ : ℤ) + u₂ * (q₁ : ℤ) = 1)
    (f : Polynomial ℤ) :
  polynomialCompleteSum (q₁ * q₂) (Nat.mul_pos hq₁ hq₂) f =
    polynomialCompleteSum q₁ hq₁ (Polynomial.C u₁ * f) *
      polynomialCompleteSum q₂ hq₂ (Polynomial.C u₂ * f) := by
  let _ : NeZero q₁ := ⟨hq₁.ne'⟩
  let _ : NeZero q₂ := ⟨hq₂.ne'⟩
  let _ : NeZero (q₁ * q₂) := ⟨(Nat.mul_pos hq₁ hq₂).ne'⟩
  let e := ZMod.chineseRemainder hcop
  simp only [polynomialCompleteSum]
  calc
    ∑ x : ZMod (q₁ * q₂),
        ZMod.stdAddChar (Polynomial.eval x
          (f.map (Int.castRingHom (ZMod (q₁ * q₂))))) =
        ∑ x : ZMod (q₁ * q₂),
          ZMod.stdAddChar (Polynomial.eval (e x).1
            ((Polynomial.C u₁ * f).map (Int.castRingHom (ZMod q₁)))) *
          ZMod.stdAddChar (Polynomial.eval (e x).2
            ((Polynomial.C u₂ * f).map (Int.castRingHom (ZMod q₂)))) := by
      apply Finset.sum_congr rfl
      intro x _hx
      have hphase := polynomialPhase_crt hq₁ hq₂ hbezout f x
      simpa [e, ZMod.chineseRemainder] using hphase
    _ = ∑ y : ZMod q₁, ∑ z : ZMod q₂,
          ZMod.stdAddChar (Polynomial.eval y
            ((Polynomial.C u₁ * f).map (Int.castRingHom (ZMod q₁)))) *
          ZMod.stdAddChar (Polynomial.eval z
            ((Polynomial.C u₂ * f).map (Int.castRingHom (ZMod q₂)))) := by
      calc
        ∑ x : ZMod (q₁ * q₂),
            ZMod.stdAddChar (Polynomial.eval (e x).1
              ((Polynomial.C u₁ * f).map (Int.castRingHom (ZMod q₁)))) *
            ZMod.stdAddChar (Polynomial.eval (e x).2
              ((Polynomial.C u₂ * f).map (Int.castRingHom (ZMod q₂)))) =
            ∑ yz : ZMod q₁ × ZMod q₂,
              ZMod.stdAddChar (Polynomial.eval yz.1
                ((Polynomial.C u₁ * f).map (Int.castRingHom (ZMod q₁)))) *
              ZMod.stdAddChar (Polynomial.eval yz.2
                ((Polynomial.C u₂ * f).map (Int.castRingHom (ZMod q₂)))) := by
          let g : ZMod q₁ × ZMod q₂ → ℂ := fun yz =>
            ZMod.stdAddChar (Polynomial.eval yz.1
              ((Polynomial.C u₁ * f).map (Int.castRingHom (ZMod q₁)))) *
            ZMod.stdAddChar (Polynomial.eval yz.2
              ((Polynomial.C u₂ * f).map (Int.castRingHom (ZMod q₂))))
          change (∑ x : ZMod (q₁ * q₂), g (e x)) = ∑ yz, g yz
          exact Equiv.sum_comp e.toEquiv g
        _ = _ := Fintype.sum_prod_type _
    _ = (∑ y : ZMod q₁,
          ZMod.stdAddChar (Polynomial.eval y
            ((Polynomial.C u₁ * f).map (Int.castRingHom (ZMod q₁))))) *
        ∑ z : ZMod q₂,
          ZMod.stdAddChar (Polynomial.eval z
            ((Polynomial.C u₂ * f).map (Int.castRingHom (ZMod q₂)))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum]

private theorem coprime_natAbs_left_of_bezout
    {q₁ q₂ : ℕ} {u₁ u₂ : ℤ}
    (hbezout : u₁ * (q₂ : ℤ) + u₂ * (q₁ : ℤ) = 1) :
    Nat.Coprime q₁ (Int.natAbs u₁) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd q₁ (Int.natAbs u₁)
  have hgqN : g ∣ q₁ := Nat.gcd_dvd_left _ _
  have hguN : g ∣ Int.natAbs u₁ := Nat.gcd_dvd_right _ _
  have hgq : (g : ℤ) ∣ (q₁ : ℤ) := Int.natCast_dvd_natCast.mpr hgqN
  have hgu : (g : ℤ) ∣ u₁ := by
    apply (Int.natAbs_dvd_natAbs).mp
    simpa using hguN
  have hgOne : (g : ℤ) ∣ 1 := by
    rw [← hbezout]
    exact dvd_add (dvd_mul_of_dvd_left hgu _) (dvd_mul_of_dvd_right hgq _)
  have hgOneN : g ∣ 1 :=
    Int.natCast_dvd_natCast.mp (by simpa using hgOne)
  exact Nat.dvd_one.mp hgOneN

/-- A Bézout-scaled polynomial remains primitive at each coprime CRT factor. -/
theorem nonconstantContent_coprime_of_crt_unit
    (_hq₁ : 0 < q₁) (_hq₂ : 0 < q₂) (_hcop : Nat.Coprime q₁ q₂)
    (hprim : Nat.Coprime (q₁ * q₂)
      (Polynomial.nonconstantContentNat f))
    {u₁ u₂ : ℤ}
    (hbezout : u₁ * (q₂ : ℤ) + u₂ * (q₁ : ℤ) = 1) :
  Nat.Coprime q₁
      (Polynomial.nonconstantContentNat (Polynomial.C u₁ * f)) ∧
    Nat.Coprime q₂
      (Polynomial.nonconstantContentNat (Polynomial.C u₂ * f)) := by
  have hc₁ : Nat.Coprime q₁ (Polynomial.nonconstantContentNat f) :=
    Nat.Coprime.of_dvd_left (Nat.dvd_mul_right q₁ q₂) hprim
  have hc₂ : Nat.Coprime q₂ (Polynomial.nonconstantContentNat f) :=
    Nat.Coprime.of_dvd_left (Nat.dvd_mul_left q₂ q₁)
      (by simpa [Nat.mul_comm] using hprim)
  have hu₁ : Nat.Coprime q₁ (Int.natAbs u₁) :=
    coprime_natAbs_left_of_bezout hbezout
  have hu₂ : Nat.Coprime q₂ (Int.natAbs u₂) := by
    apply coprime_natAbs_left_of_bezout (q₂ := q₁) (u₂ := u₁)
    simpa [add_comm] using hbezout
  rw [Polynomial.nonconstantContentNat_C_mul,
    Polynomial.nonconstantContentNat_C_mul]
  exact ⟨hu₁.mul_right hc₁, hu₂.mul_right hc₂⟩

/-- The subtype of primes occurring in the factorization support of `q`. -/
abbrev FactorizationPrimeSupport (q : ℕ) :=
  {p : ℕ // p ∈ q.factorization.support}

/-- A scalar indexed exactly by the prime support of `q`. -/
abbrev FactorizationScalar (q : ℕ) :=
  FactorizationPrimeSupport q → ℤ

/-- Every element of `FactorizationPrimeSupport q` is prime. -/
theorem factorizationPrimeSupport_prime {q : ℕ}
    (p : FactorizationPrimeSupport q) : p.1.Prime :=
  Nat.prime_of_mem_primeFactors p.property

/-- Extend a support-indexed scalar to all natural numbers by the default value `0`. -/
def factorizationScalarLookup {q : ℕ}
    (u : FactorizationScalar q) (p : ℕ) : ℤ :=
  if hp : p ∈ q.factorization.support then u ⟨p, hp⟩ else 0

/-- On the factorization support, lookup returns the original support-indexed scalar. -/
@[simp] theorem factorizationScalarLookup_of_mem
    {q p : ℕ} (u : FactorizationScalar q)
    (hp : p ∈ q.factorization.support) :
  factorizationScalarLookup u p = u ⟨p, hp⟩ := by
  unfold factorizationScalarLookup
  rw [dif_pos hp]

/-- Away from the factorization support, lookup returns the default scalar `0`. -/
@[simp] theorem factorizationScalarLookup_of_not_mem
    {q p : ℕ} (u : FactorizationScalar q)
    (hp : p ∉ q.factorization.support) :
  factorizationScalarLookup u p = 0 := by
  unfold factorizationScalarLookup
  rw [dif_neg hp]

/-- Two support-indexed scalars are equal when they agree at every supported prime. -/
theorem factorizationScalar_ext {q : ℕ}
    {u v : FactorizationScalar q}
    (h : ∀ p, u p = v p) : u = v := by
  funext p
  exact h p

/-- Equality of support-indexed scalars is equivalent to equality of their total lookups. -/
theorem factorizationScalar_ext_iff_lookup_eq {q : ℕ}
    {u v : FactorizationScalar q} :
  u = v ↔ ∀ p, factorizationScalarLookup u p =
    factorizationScalarLookup v p := by
  constructor
  · rintro rfl p
    rfl
  · intro h
    apply factorizationScalar_ext
    intro p
    have hp := h p.1
    rw [factorizationScalarLookup_of_mem u p.property,
      factorizationScalarLookup_of_mem v p.property] at hp
    exact hp

/-- Rewrite a product over the support subtype as the corresponding filtered product. -/
theorem factorizationPrimeSupport_prod_eq
    {q : ℕ} {M : Type*} [CommMonoid M] (g : ℕ → M) :
  (∏ p : FactorizationPrimeSupport q, g p.1) =
    ∏ p ∈ q.factorization.support, g p := by
  classical
  exact Finset.prod_coe_sort q.factorization.support g

/-- The scalar on the empty factorization support of modulus `1` is uniquely determined. -/
theorem factorizationScalar_one_unique
    (u v : FactorizationScalar 1) : u = v := by
  apply factorizationScalar_ext
  intro p
  have hp : False := by simpa using p.property
  exact hp.elim

/-- The local complete sum obtained from a support-indexed CRT scalar. -/
noncomputable def factorizationLocalCompleteSum
    (q : ℕ) (f : Polynomial ℤ) (u : FactorizationScalar q)
    (p : FactorizationPrimeSupport q) : ℂ :=
  polynomialCompleteSum (p.1 ^ q.factorization p.1)
    (pow_pos (factorizationPrimeSupport_prime p).pos _)
    (Polynomial.C (u p) * f)

/-- Executable CRT data expressing a global complete sum as a product of
support-indexed local complete sums. -/
structure CompleteSumFactorizationData
    (q : ℕ) (hq : 0 < q) (f : Polynomial ℤ) where
  /-- The Bézout/CRT scaling coefficient attached to each supported prime. -/
  scalar : FactorizationScalar q
  scalar_ne_zero : ∀ p, scalar p ≠ 0
  local_primitive : ∀ p,
    Nat.Coprime (p.1 ^ q.factorization p.1)
      (Polynomial.nonconstantContentNat (Polynomial.C (scalar p) * f))
  norm_eq_product :
    ‖polynomialCompleteSum q hq f‖ =
      ∏ p : FactorizationPrimeSupport q,
        ‖factorizationLocalCompleteSum q f scalar p‖

/-- Factorization certificates with pointwise equal scalars are equal. -/
theorem CompleteSumFactorizationData.ext_scalar
    {q : ℕ} {hq : 0 < q} {f : Polynomial ℤ}
    (D₁ D₂ : CompleteSumFactorizationData q hq f)
    (hscalar : ∀ p, D₁.scalar p = D₂.scalar p) : D₁ = D₂ := by
  cases D₁ with
  | mk scalar₁ scalar_ne_zero₁ local_primitive₁ norm_eq_product₁ =>
    cases D₂ with
    | mk scalar₂ scalar_ne_zero₂ local_primitive₂ norm_eq_product₂ =>
      have h : scalar₁ = scalar₂ := factorizationScalar_ext hscalar
      subst scalar₂
      rfl

/-- The complete-sum factorization certificate at modulus `1` is unique. -/
theorem CompleteSumFactorizationData.one_unique
    {hq : 0 < 1} {f : Polynomial ℤ}
    (D₁ D₂ : CompleteSumFactorizationData 1 hq f) : D₁ = D₂ := by
  apply CompleteSumFactorizationData.ext_scalar
  intro p
  exact congrFun (factorizationScalar_one_unique D₁.scalar D₂.scalar) p

/-- Multiplication by a nonzero constant preserves the natural degree. -/
theorem _root_.Polynomial.natDegree_C_mul_eq
    (f : Polynomial ℤ) {u : ℤ} (hu : u ≠ 0) :
  (Polynomial.C u * f).natDegree = f.natDegree := by
  by_cases hf : f = 0
  · simp [hf]
  · rw [Polynomial.natDegree_C_mul_of_mul_ne_zero]
    exact mul_ne_zero hu (Polynomial.leadingCoeff_ne_zero.mpr hf)

/-- In a Bézout identity for coprime factors greater than one, the left
coefficient is nonzero. -/
theorem bezout_left_ne_zero_of_one_lt
    (hq₁ : 1 < q₁) {q₂ : ℕ} {u₁ u₂ : ℤ}
    (hbezout : u₁ * (q₂ : ℤ) + u₂ * (q₁ : ℤ) = 1) :
  u₁ ≠ 0 := by
  intro hu
  subst u₁
  simp only [zero_mul, zero_add] at hbezout
  have hdvd : (q₁ : ℤ) ∣ 1 := ⟨u₂, by simpa [mul_comm] using hbezout.symm⟩
  have : q₁ = 1 := Int.eq_one_of_dvd_one (by omega) hdvd
  omega

/-- The complete polynomial sum modulo `1` has norm one. -/
theorem polynomialCompleteSum_one_norm (f : Polynomial ℤ) :
  ‖polynomialCompleteSum 1 (by omega) f‖ = 1 := by
  simp [polynomialCompleteSum]

private theorem polynomialCompleteSum_congr
    {q₁ q₂ : ℕ} {hq₁ : 0 < q₁} {hq₂ : 0 < q₂}
    {f₁ f₂ : Polynomial ℤ} (hq : q₁ = q₂) (hf : f₁ = f₂) :
    polynomialCompleteSum q₁ hq₁ f₁ = polynomialCompleteSum q₂ hq₂ f₂ := by
  subst q₂
  subst f₂
  rfl

/-- Construct support-indexed CRT factorization data for every positive modulus. -/
theorem exists_completeSumFactorizationData
    (q : ℕ) (hq : 0 < q) (f : Polynomial ℤ)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  Nonempty (CompleteSumFactorizationData q hq f) := by
  classical
  let motive : ℕ → Sort _ := fun n ↦
    ∀ (hn : 0 < n) (g : Polynomial ℤ),
      Nat.Coprime n (Polynomial.nonconstantContentNat g) →
        Nonempty (CompleteSumFactorizationData n hn g)
  have hrec : ∀ n, motive n := Nat.recOnPosPrimePosCoprime
    (motive := motive)
    (fun p n hp hn ↦ by
      intro hpn g hprim
      let scalar : FactorizationScalar (p ^ n) := fun _ ↦ 1
      refine ⟨⟨scalar, ?_, ?_, ?_⟩⟩
      · intro r
        simp [scalar]
      · rintro ⟨r, hr⟩
        have hrp : r = p := by
          simpa [hp.factorization_pow, hn.ne'] using hr
        subst r
        rw [Nat.factorization_pow_self hp]
        simpa [scalar, Polynomial.nonconstantContentNat_C_mul] using hprim
      · let rp : FactorizationPrimeSupport (p ^ n) :=
          ⟨p, by simp [hp.factorization_pow, hn.ne']⟩
        let _ : Subsingleton (FactorizationPrimeSupport (p ^ n)) :=
          ⟨fun r s ↦ Subtype.ext (by
            have hr : r.1 = p := by
              simpa [hp.factorization_pow, hn.ne'] using r.property
            have hs : s.1 = p := by
              simpa [hp.factorization_pow, hn.ne'] using s.property
            omega)⟩
        rw [Fintype.prod_subsingleton _ rp]
        dsimp [rp, factorizationLocalCompleteSum, scalar]
        apply congrArg norm
        apply polynomialCompleteSum_congr
        · simp [hp.factorization_self]
        · simp)
    (by
      intro hn
      omega)
    (by
      intro _hn g _hprim
      let scalar : FactorizationScalar 1 := fun r ↦ by
        simpa using r.property
      refine ⟨⟨scalar, ?_, ?_, ?_⟩⟩
      · intro r
        have hr : False := by simpa using r.property
        exact hr.elim
      · intro r
        have hr : False := by simpa using r.property
        exact hr.elim
      · rw [polynomialCompleteSum_one_norm]
        simp [factorizationLocalCompleteSum, scalar])
    (fun a b ha hb hab iha ihb ↦ by
      intro habpos g hprim
      let u₁ : ℤ := Nat.gcdB a b
      let u₂ : ℤ := Nat.gcdA a b
      have hbezout : u₁ * (b : ℤ) + u₂ * (a : ℤ) = 1 := by
        have hgcd := Nat.gcd_eq_gcd_ab a b
        rw [hab.gcd_eq_one] at hgcd
        dsimp [u₁, u₂]
        calc
          Nat.gcdB a b * (b : ℤ) + Nat.gcdA a b * (a : ℤ) =
              (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b := by ring
          _ = 1 := hgcd.symm
      have hu₁ : u₁ ≠ 0 :=
        bezout_left_ne_zero_of_one_lt (q₁ := (a : ℤ)) (q₂ := b)
          (u₁ := u₁) (u₂ := u₂) (by exact_mod_cast ha) hbezout
      have hu₂ : u₂ ≠ 0 := by
        apply bezout_left_ne_zero_of_one_lt (q₁ := (b : ℤ)) (q₂ := a)
          (u₁ := u₂) (u₂ := u₁) (by exact_mod_cast hb)
        simpa [add_comm] using hbezout
      have hlocal := nonconstantContent_coprime_of_crt_unit
        (by omega : 0 < a) (by omega : 0 < b) hab hprim hbezout
      obtain ⟨D₁⟩ := iha (by omega) (Polynomial.C u₁ * g) hlocal.1
      obtain ⟨D₂⟩ := ihb (by omega) (Polynomial.C u₂ * g) hlocal.2
      have hdis : Disjoint a.factorization.support b.factorization.support :=
        hab.disjoint_primeFactors
      have hsupp : (a * b).factorization.support =
          a.factorization.support ∪ b.factorization.support := by
        rw [Nat.factorization_mul_of_coprime hab,
          Finsupp.support_add_eq hdis]
      have support_right {r : ℕ}
          (hr : r ∈ (a * b).factorization.support)
          (hra : r ∉ a.factorization.support) :
          r ∈ b.factorization.support := by
        have hrne : (a * b).factorization r ≠ 0 :=
          Finsupp.mem_support_iff.mp hr
        have hfa : a.factorization r = 0 :=
          Finsupp.notMem_support_iff.mp hra
        rw [Nat.factorization_mul_apply_of_coprime hab, hfa, zero_add] at hrne
        exact Finsupp.mem_support_iff.mpr hrne
      let scalar : FactorizationScalar (a * b) := fun r ↦
        if hra : r.1 ∈ a.factorization.support then
          u₁ * D₁.scalar ⟨r.1, hra⟩
        else
          u₂ * D₂.scalar ⟨r.1, support_right r.property hra⟩
      have scalar_eq_left (r : FactorizationPrimeSupport (a * b))
          (hra : r.1 ∈ a.factorization.support) :
          scalar r = u₁ * D₁.scalar ⟨r.1, hra⟩ := by
        change (if h : r.1 ∈ a.factorization.support then
          u₁ * D₁.scalar ⟨r.1, h⟩ else
          u₂ * D₂.scalar ⟨r.1, support_right r.property h⟩) = _
        rw [dif_pos hra]
      have scalar_eq_right (r : FactorizationPrimeSupport (a * b))
          (hra : r.1 ∉ a.factorization.support) :
          scalar r = u₂ * D₂.scalar
            ⟨r.1, support_right r.property hra⟩ := by
        change (if h : r.1 ∈ a.factorization.support then
          u₁ * D₁.scalar ⟨r.1, h⟩ else
          u₂ * D₂.scalar ⟨r.1, support_right r.property h⟩) = _
        rw [dif_neg hra]
      have hscalar_ne_zero (r : FactorizationPrimeSupport (a * b)) :
          scalar r ≠ 0 := by
        by_cases hra : r.1 ∈ a.factorization.support
        · rw [scalar_eq_left r hra]
          exact mul_ne_zero hu₁ (D₁.scalar_ne_zero _)
        · rw [scalar_eq_right r hra]
          exact mul_ne_zero hu₂ (D₂.scalar_ne_zero _)
      have hlocalPrimitive (r : FactorizationPrimeSupport (a * b)) :
          Nat.Coprime (r.1 ^ (a * b).factorization r.1)
            (Polynomial.nonconstantContentNat (Polynomial.C (scalar r) * g)) := by
        by_cases hra : r.1 ∈ a.factorization.support
        · have hrb : r.1 ∉ b.factorization.support :=
            Finset.disjoint_left.mp hdis hra
          have hfb : b.factorization r.1 = 0 :=
            Finsupp.notMem_support_iff.mp hrb
          have hexp : (a * b).factorization r.1 = a.factorization r.1 := by
            rw [Nat.factorization_mul_apply_of_coprime hab, hfb, add_zero]
          have hD := D₁.local_primitive ⟨r.1, hra⟩
          have hpoly : Polynomial.C (scalar r) * g =
              Polynomial.C (D₁.scalar ⟨r.1, hra⟩) *
                (Polynomial.C u₁ * g) := by
            rw [scalar_eq_left r hra]
            simp only [Polynomial.C_mul]
            ring
          rw [hexp, hpoly]
          exact hD
        · have hr := r.property
          have hrb : r.1 ∈ b.factorization.support :=
            support_right hr hra
          have hfa : a.factorization r.1 = 0 :=
            Finsupp.notMem_support_iff.mp hra
          have hexp : (a * b).factorization r.1 = b.factorization r.1 := by
            rw [Nat.factorization_mul_apply_of_coprime hab, hfa, zero_add]
          have hD := D₂.local_primitive ⟨r.1, hrb⟩
          have hpoly : Polynomial.C (scalar r) * g =
              Polynomial.C (D₂.scalar ⟨r.1, hrb⟩) *
                (Polynomial.C u₂ * g) := by
            rw [scalar_eq_right r hra]
            simp only [Polynomial.C_mul]
            ring
          rw [hexp, hpoly]
          exact hD
      let e₁ :
          {r : FactorizationPrimeSupport (a * b) //
            r.1 ∈ a.factorization.support} ≃ FactorizationPrimeSupport a :=
        {
        toFun r := ⟨r.1.1, r.2⟩
        invFun r := ⟨⟨r.1, by
          rw [hsupp]
          exact Finset.mem_union_left _ r.2⟩, r.2⟩
        left_inv r := by cases r; rfl
        right_inv r := by cases r; rfl
        }
      let e₂ :
          {r : FactorizationPrimeSupport (a * b) //
            r.1 ∉ a.factorization.support} ≃ FactorizationPrimeSupport b :=
        {
        toFun r := ⟨r.1.1, support_right r.1.property r.2⟩
        invFun r := ⟨⟨r.1, by
          rw [hsupp]
          exact Finset.mem_union_right _ r.2⟩, by
            exact fun hra ↦ Finset.disjoint_left.mp hdis hra r.2⟩
        left_inv r := by cases r; rfl
        right_inv r := by cases r; rfl
        }
      let finalNorm : FactorizationPrimeSupport (a * b) → ℝ := fun r ↦
        ‖factorizationLocalCompleteSum (a * b) g scalar r‖
      have hpoint₁
          (r : {r : FactorizationPrimeSupport (a * b) //
            r.1 ∈ a.factorization.support}) :
          finalNorm r =
            ‖factorizationLocalCompleteSum a (Polynomial.C u₁ * g)
              D₁.scalar (e₁ r)‖ := by
        have hrb : r.1.1 ∉ b.factorization.support :=
          Finset.disjoint_left.mp hdis r.2
        have hfb : b.factorization r.1.1 = 0 :=
          Finsupp.notMem_support_iff.mp hrb
        have hexp : (a * b).factorization r.1.1 = a.factorization r.1.1 := by
          rw [Nat.factorization_mul_apply_of_coprime hab, hfb, add_zero]
        have he₁ : e₁ r = ⟨r.1.1, r.2⟩ := by
          apply Subtype.ext
          rfl
        have hpoly : Polynomial.C (scalar r.1) * g =
            Polynomial.C (D₁.scalar (e₁ r)) * (Polynomial.C u₁ * g) := by
          rw [he₁]
          rw [scalar_eq_left r.1 r.2]
          simp only [Polynomial.C_mul]
          ring
        dsimp [finalNorm]
        unfold factorizationLocalCompleteSum
        apply congrArg norm
        apply polynomialCompleteSum_congr
        · have hval : (e₁ r).1 = r.1.1 := congrArg Subtype.val he₁
          calc
            r.1.1 ^ (a * b).factorization r.1.1 =
                r.1.1 ^ a.factorization r.1.1 := congrArg _ hexp
            _ = (e₁ r).1 ^ a.factorization (e₁ r).1 :=
              congrArg (fun x ↦ x ^ a.factorization x) hval.symm
        · exact hpoly
      have hpoint₂
          (r : {r : FactorizationPrimeSupport (a * b) //
            r.1 ∉ a.factorization.support}) :
          finalNorm r =
            ‖factorizationLocalCompleteSum b (Polynomial.C u₂ * g)
              D₂.scalar (e₂ r)‖ := by
        have hrb : r.1.1 ∈ b.factorization.support :=
          support_right r.1.property r.2
        have hfa : a.factorization r.1.1 = 0 :=
          Finsupp.notMem_support_iff.mp r.2
        have hexp : (a * b).factorization r.1.1 = b.factorization r.1.1 := by
          rw [Nat.factorization_mul_apply_of_coprime hab, hfa, zero_add]
        have he₂ : e₂ r = ⟨r.1.1, hrb⟩ := by
          apply Subtype.ext
          rfl
        have hpoly : Polynomial.C (scalar r.1) * g =
            Polynomial.C (D₂.scalar (e₂ r)) * (Polynomial.C u₂ * g) := by
          rw [he₂]
          rw [scalar_eq_right r.1 r.2]
          simp only [Polynomial.C_mul]
          ring
        dsimp [finalNorm]
        unfold factorizationLocalCompleteSum
        apply congrArg norm
        apply polynomialCompleteSum_congr
        · have hval : (e₂ r).1 = r.1.1 := congrArg Subtype.val he₂
          calc
            r.1.1 ^ (a * b).factorization r.1.1 =
                r.1.1 ^ b.factorization r.1.1 := congrArg _ hexp
            _ = (e₂ r).1 ^ b.factorization (e₂ r).1 :=
              congrArg (fun x ↦ x ^ b.factorization x) hval.symm
        · exact hpoly
      refine ⟨⟨scalar, hscalar_ne_zero, hlocalPrimitive, ?_⟩⟩
      rw [polynomialCompleteSum_crt (by omega) (by omega) hab hbezout g,
        norm_mul, D₁.norm_eq_product, D₂.norm_eq_product]
      change (∏ p : FactorizationPrimeSupport a,
          ‖factorizationLocalCompleteSum a (Polynomial.C u₁ * g) D₁.scalar p‖) *
          (∏ p : FactorizationPrimeSupport b,
            ‖factorizationLocalCompleteSum b (Polynomial.C u₂ * g) D₂.scalar p‖) =
        ∏ p : FactorizationPrimeSupport (a * b), finalNorm p
      rw [← Fintype.prod_subtype_mul_prod_subtype
        (fun r : FactorizationPrimeSupport (a * b) ↦
          r.1 ∈ a.factorization.support) finalNorm]
      congr 1
      · exact (Fintype.prod_equiv e₁ _ _ hpoint₁).symm
      · exact (Fintype.prod_equiv e₂ _ _ hpoint₂).symm)
  exact hrec q hq f hprimitive

/-- The product of real powers of the prime-power factors equals the same power
of the original modulus. -/
theorem factorization_rpow_product
    (q : ℕ) (hq : 0 < q) (x : ℝ) :
  ∏ p ∈ q.factorization.support,
      Real.rpow (p ^ q.factorization p : ℝ) x =
    Real.rpow q x := by
  have hfac : ∏ p ∈ q.factorization.support,
      p ^ q.factorization p = q := by
    simpa [Finsupp.prod] using Nat.prod_factorization_pow_eq_self hq.ne'
  calc
    ∏ p ∈ q.factorization.support,
        Real.rpow (p ^ q.factorization p : ℝ) x =
        Real.rpow (∏ p ∈ q.factorization.support,
          (p ^ q.factorization p : ℝ)) x := by
      exact Real.finsetProd_rpow _ _ (by intros; positivity) x
    _ = Real.rpow q x := by
      norm_cast
      rw [hfac]

/-- The finite set of primes at which the global Chen factor may be nontrivial. -/
def chenExceptionalPrimes (d : ℕ) : Finset ℕ :=
  (Finset.range ((d + 1) ^ 6 + 1)).filter Nat.Prime

/-- The explicit finite product of all exceptional local Chen factors. -/
noncomputable def chenGlobalFactor (d : ℕ) : ℝ :=
  ∏ p ∈ chenExceptionalPrimes d, chenLocalFactor d p

/-- For degree at least three, the large-prime threshold exponent is at most six. -/
theorem chenLargePrimeExponent_le_six (d : ℕ) (hd : 3 ≤ d) :
  (2 * d : ℝ) / (d - 2 : ℝ) ≤ 6 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 2 := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- Bound the large-prime threshold by the executable cutoff `(d + 1) ^ 6`. -/
theorem chenLargePrimeThreshold_le (d : ℕ) (hd : 3 ≤ d) :
  chenLargePrimeThreshold d ≤ (d + 1 : ℝ) ^ 6 := by
  have hbase : 1 ≤ (d - 1 : ℝ) := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  calc
    chenLargePrimeThreshold d =
        Real.rpow (d - 1 : ℝ) ((2 * d : ℝ) / (d - 2 : ℝ)) := rfl
    _ ≤ Real.rpow (d - 1 : ℝ) 6 :=
      Real.rpow_le_rpow_of_exponent_le hbase
        (chenLargePrimeExponent_le_six d hd)
    _ = (d - 1 : ℝ) ^ 6 := by
      exact Real.rpow_natCast (d - 1 : ℝ) 6
    _ ≤ (d + 1 : ℝ) ^ 6 := by
      gcongr
      have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith

/-- Every local Chen factor is at least one. -/
theorem one_le_chenLocalFactor (d p : ℕ) (hd : 3 ≤ d) :
  1 ≤ chenLocalFactor d p := by
  unfold chenLocalFactor
  split
  · exact le_rfl
  split
  · exact Real.one_le_rpow
      (by exact_mod_cast (show 1 ≤ d by omega)) (by positivity)
  split
  · exact Real.one_le_rpow
      (by exact_mod_cast (show 1 ≤ d by omega)) (by positivity)
  · have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have h₁ : (1 : ℝ) ≤ d - 1 := by linarith
    have h₂ : (1 : ℝ) ≤ Real.rpow d ((3 : ℝ) / d) :=
      Real.one_le_rpow
        (by exact_mod_cast (show 1 ≤ d by omega)) (by positivity)
    nlinarith

/-- A prime outside the exceptional support contributes the trivial local factor. -/
theorem chenLocalFactor_eq_one_of_prime_not_mem
    (d p : ℕ) (hd : 3 ≤ d) (hp : p.Prime)
    (hmem : p ∉ chenExceptionalPrimes d) :
  chenLocalFactor d p = 1 := by
  have hpBound : (d + 1) ^ 6 + 1 ≤ p := by
    have hnotlt : ¬ p < (d + 1) ^ 6 + 1 := by
      intro hlt
      apply hmem
      simp [chenExceptionalPrimes, hp, hlt]
    omega
  have hthreshold : chenLargePrimeThreshold d < (p : ℝ) := by
    calc
      chenLargePrimeThreshold d ≤ (d + 1 : ℝ) ^ 6 :=
        chenLargePrimeThreshold_le d hd
      _ < p := by exact_mod_cast hpBound
  simp [chenLocalFactor, hthreshold]

/-- The local-factor product over the prime support of `q` is bounded by the
global finite product. -/
theorem factorization_localFactor_product_le_global
    (d q : ℕ) (hd : 3 ≤ d) (_hq : 0 < q) :
  ∏ p ∈ q.factorization.support, chenLocalFactor d p ≤
    chenGlobalFactor d := by
  classical
  let s := q.factorization.support
  let t := chenExceptionalPrimes d
  calc
    ∏ p ∈ s, chenLocalFactor d p =
        ∏ p ∈ s, if p ∈ t then chenLocalFactor d p else 1 := by
      apply Finset.prod_congr rfl
      intro p hpS
      split
      · rfl
      · rw [chenLocalFactor_eq_one_of_prime_not_mem d p hd
          (Nat.prime_of_mem_primeFactors hpS)]
        assumption
    _ = ∏ p ∈ s.filter (· ∈ t), chenLocalFactor d p := by
      simp [Finset.prod_filter]
    _ ≤ ∏ p ∈ t, chenLocalFactor d p := by
      apply Finset.prod_le_prod_of_subset_of_one_le
      · intro p hpst
        exact (Finset.mem_filter.mp hpst).2
      · intro p _hpst
        exact (one_le_chenLocalFactor d p hd).trans' zero_le_one
      · intro p _hpt _hpnot
        exact one_le_chenLocalFactor d p hd
    _ = chenGlobalFactor d := rfl

/-- The global Chen factor is at least one. -/
theorem one_le_chenGlobalFactor (d : ℕ) (hd : 3 ≤ d) :
  1 ≤ chenGlobalFactor d := by
  apply Finset.one_le_prod
  intro p _hp
  exact one_le_chenLocalFactor d p hd

/-- ACK Theorem 2.2 with an explicit global finite-product constant, conditional
on the prime-modulus polynomial-sum input. -/
theorem ack_theorem_2_2_finiteProduct_of_primeBound
    (hWeil : PolynomialPrimeSumBound)
    (d q : ℕ) (hd : 3 ≤ d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    chenGlobalFactor d * Real.rpow q (1 - (1 : ℝ) / d) := by
  let alpha : ℝ := 1 - (1 : ℝ) / d
  obtain ⟨D⟩ := exists_completeSumFactorizationData q hq f hprimitive
  have hlocal : ∀ r : FactorizationPrimeSupport q,
      ‖factorizationLocalCompleteSum q f D.scalar r‖ ≤
        chenLocalFactor d r.1 *
          Real.rpow (r.1 ^ q.factorization r.1 : ℝ) alpha := by
    intro r
    have hrPrime := factorizationPrimeSupport_prime r
    let _ : Fact r.1.Prime := ⟨hrPrime⟩
    have ha : 0 < q.factorization r.1 :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp r.property)
    have hcop : Nat.Coprime r.1
        (Polynomial.nonconstantContentNat (Polynomial.C (D.scalar r) * f)) := by
      exact Nat.Coprime.of_dvd_left
        (dvd_pow_self r.1 ha.ne') (D.local_primitive r)
    have hprim : ¬ r.1 ∣
        Polynomial.nonconstantContentNat (Polynomial.C (D.scalar r) * f) :=
      hrPrime.coprime_iff_not_dvd.mp hcop
    have hlocalBound := primePower_completeSum_bound_of_primeBound hWeil
      hrPrime ha (Polynomial.C (D.scalar r) * f) hprim
      (Polynomial.natDegree_C_mul_eq f (D.scalar_ne_zero r) |>.trans hdegree) hd
    simpa [factorizationLocalCompleteSum, alpha] using hlocalBound
  calc
    ‖polynomialCompleteSum q hq f‖ =
        ∏ r : FactorizationPrimeSupport q,
          ‖factorizationLocalCompleteSum q f D.scalar r‖ := D.norm_eq_product
    _ ≤ ∏ r : FactorizationPrimeSupport q,
        (chenLocalFactor d r.1 *
          Real.rpow (r.1 ^ q.factorization r.1 : ℝ) alpha) := by
      apply Finset.prod_le_prod
      · intro r _hr
        exact norm_nonneg _
      · intro r _hr
        exact hlocal r
    _ = (∏ p ∈ q.factorization.support, chenLocalFactor d p) *
        ∏ p ∈ q.factorization.support,
          Real.rpow (p ^ q.factorization p : ℝ) alpha := by
      rw [Finset.prod_mul_distrib]
      congr 1
      · exact Finset.prod_coe_sort
          (s := q.factorization.support) (f := fun p ↦ chenLocalFactor d p)
      · exact Finset.prod_coe_sort
          (s := q.factorization.support)
          (f := fun p ↦ Real.rpow (p ^ q.factorization p : ℝ) alpha)
    _ = (∏ p ∈ q.factorization.support, chenLocalFactor d p) *
        Real.rpow q alpha := by
      rw [factorization_rpow_product q hq alpha]
    _ ≤ chenGlobalFactor d * Real.rpow q alpha :=
      mul_le_mul_of_nonneg_right
        (factorization_localFactor_product_le_global d q hd hq)
        (Real.rpow_nonneg (by exact_mod_cast hq.le) _)
    _ = _ := by rfl

end TranslationalTilings
