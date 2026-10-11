import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import TranslationalTilings.NumberTheory.FiniteCyclicPhase

/-!
# Polynomial congruences and stationary descent

This file develops the polynomial congruence API used by the complete-sum
recursion: reduction modulo a prime, coefficientwise content normalization,
stationary translations, multiplicity-weighted root bounds, and the convexity
estimate used to aggregate recursive branches.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- Reduce an integer polynomial coefficientwise to `ZMod p`. -/
noncomputable def _root_.Polynomial.modPrime (p : ℕ)
    (f : Polynomial ℤ) : Polynomial (ZMod p) :=
  f.map (Int.castRingHom (ZMod p))

/-- The roots modulo `p` of an integer polynomial, represented as a finite set. -/
noncomputable def _root_.Polynomial.rootsModPrime (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ) : Finset (ZMod p) :=
  Finset.univ.filter (Polynomial.modPrime p f).IsRoot

/-- The sum of the multiplicities of all roots of `f` modulo `p`. -/
noncomputable def _root_.Polynomial.rootMassModPrime (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ) : ℕ :=
  ∑ x ∈ Polynomial.rootsModPrime p f,
    (Polynomial.modPrime p f).rootMultiplicity x

/-- Divide every coefficient of an integer polynomial by the natural number `m`. -/
noncomputable def _root_.Polynomial.coeffDiv
    (f : Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  f.sum fun n a ↦ Polynomial.monomial n (a / (m : ℤ))

/-- The `p`-adic order of the natural content of an integer polynomial. -/
def _root_.Polynomial.coefficientPadicOrder
    (p : ℕ) (f : Polynomial ℤ) : ℕ :=
  padicValNat p (Polynomial.contentNat f)

/-- Remove the largest common power of `p` from the coefficients of `f`. -/
noncomputable def _root_.Polynomial.normalizeAtPrime
    (p : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.coeffDiv f (p ^ Polynomial.coefficientPadicOrder p f)

/-- Substitute `p * X + μ` into an integer polynomial. -/
noncomputable def _root_.Polynomial.primeScaleTranslate
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : Polynomial ℤ :=
  f.comp (Polynomial.C (p : ℤ) * Polynomial.X + Polynomial.C mu)

/-- Normalize the prime-scaled translate `f (p * X + μ)` at `p`. -/
noncomputable def _root_.Polynomial.normalizedPrimeScaleTranslate
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : Polynomial ℤ :=
  Polynomial.normalizeAtPrime p (Polynomial.primeScaleTranslate f p mu)

/-- The prime-scaled translate of `f` with its constant value `f μ` removed. -/
noncomputable def _root_.Polynomial.stationaryTranslate
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : Polynomial ℤ :=
  Polynomial.primeScaleTranslate f p mu - Polynomial.C (f.eval mu)

/-- The common `p`-adic coefficient order of the stationary translate. -/
noncomputable def _root_.Polynomial.stationaryOrder
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : ℕ :=
  Polynomial.coefficientPadicOrder p (Polynomial.stationaryTranslate f p mu)

/-- The stationary translate after removal of its common power of `p`. -/
noncomputable def _root_.Polynomial.stationaryNormalize
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : Polynomial ℤ :=
  Polynomial.normalizeAtPrime p (Polynomial.stationaryTranslate f p mu)

/-- The `p`-adic coefficient order of the derivative of `f`. -/
noncomputable def _root_.Polynomial.derivativeContentOrder
    (f : Polynomial ℤ) (p : ℕ) : ℕ :=
  Polynomial.coefficientPadicOrder p f.derivative

/-- The derivative of `f` after removal of its common power of `p`. -/
noncomputable def _root_.Polynomial.normalizedDerivative
    (f : Polynomial ℤ) (p : ℕ) : Polynomial ℤ :=
  Polynomial.normalizeAtPrime p f.derivative

/-- The roots modulo `p` of the derivative of `f`. -/
noncomputable def _root_.Polynomial.derivativeRoots
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Polynomial.rootsModPrime p f.derivative

/-- The total multiplicity of the roots modulo `p` of the derivative of `f`. -/
noncomputable def _root_.Polynomial.derivativeRootMass
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime] : ℕ :=
  Polynomial.rootMassModPrime p f.derivative

/-- Derivative roots whose stationary order is strictly below the cutoff `L`. -/
noncomputable def _root_.Polynomial.earlyDerivativeRoots
    (f : Polynomial ℤ) (p L : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (Polynomial.derivativeRoots f p).filter fun mu ↦
    Polynomial.stationaryOrder f p mu.val < L

/-- Derivative roots whose stationary order is at least the cutoff `L`. -/
noncomputable def _root_.Polynomial.lateDerivativeRoots
    (f : Polynomial ℤ) (p L : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (Polynomial.derivativeRoots f p).filter fun mu ↦
    L ≤ Polynomial.stationaryOrder f p mu.val

/-- The derivative-root multiplicity mass restricted to a finite set `s`. -/
noncomputable def _root_.Polynomial.derivativeRootMassOn
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime]
    (s : Finset (ZMod p)) : ℕ :=
  ∑ mu ∈ s, (Polynomial.modPrime p f.derivative).rootMultiplicity mu

/-- The roots modulo `p` of the normalized derivative, used in the small-prime recursion. -/
noncomputable def _root_.Polynomial.smallPrimeStationaryRoots
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Polynomial.rootsModPrime p (Polynomial.normalizedDerivative f p)

/-- The total root multiplicity of the normalized derivative modulo `p`. -/
noncomputable def _root_.Polynomial.smallPrimeStationaryMass
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime] : ℕ :=
  Polynomial.rootMassModPrime p (Polynomial.normalizedDerivative f p)

/-- The degree, constant-term, nonvanishing, and primitivity facts preserved by a
stationary child in the prime-power recursion. -/
structure _root_.Polynomial.StationaryChildInvariant
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) (d : ℕ) : Prop where
  translate_ne_zero : Polynomial.stationaryTranslate f p mu ≠ 0
  natDegree_eq : (Polynomial.stationaryNormalize f p mu).natDegree = d
  coeff_zero : (Polynomial.stationaryNormalize f p mu).coeff 0 = 0
  primitive :
    ¬ p ∣ Polynomial.nonconstantContentNat
      (Polynomial.stationaryNormalize f p mu)

/-- Multiplication by a constant scales the nonconstant content by its absolute value. -/
theorem _root_.Polynomial.nonconstantContentNat_C_mul
    (u : ℤ) (f : Polynomial ℤ) :
  Polynomial.nonconstantContentNat (Polynomial.C u * f) =
    Int.natAbs u * Polynomial.nonconstantContentNat f := by
  have hpart : Polynomial.nonconstantPart (Polynomial.C u * f) =
      Polynomial.C u * Polynomial.nonconstantPart f := by
    ext n
    simp only [Polynomial.nonconstantPart, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_C]
    split <;> simp_all
  rw [Polynomial.nonconstantContentNat, hpart,
    Polynomial.nonconstantContentNat, Polynomial.contentNat,
    Polynomial.contentNat, Polynomial.content_C_mul]
  rw [Int.natAbs_mul, ← Int.abs_eq_normalize, Int.natAbs_abs]

private theorem coeff_coeffDiv (f : Polynomial ℤ) (m n : ℕ) :
    (Polynomial.coeffDiv f m).coeff n = f.coeff n / (m : ℤ) := by
  classical
  simp only [Polynomial.coeffDiv, Polynomial.sum_def, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Finset.sum_ite_eq', Polynomial.mem_support_iff,
    ne_eq, ite_not, ite_eq_right_iff]
  intro h
  simp [h]

private theorem contentNat_dvd_coeff (f : Polynomial ℤ) (n : ℕ) :
    (Polynomial.contentNat f : ℤ) ∣ f.coeff n := by
  simpa [Polynomial.contentNat, Int.natCast_natAbs, Int.abs_eq_normalize,
    Polynomial.normalize_content] using Polynomial.content_dvd_coeff (p := f) n

private theorem contentNat_C_mul (u : ℤ) (f : Polynomial ℤ) :
    Polynomial.contentNat (Polynomial.C u * f) =
      Int.natAbs u * Polynomial.contentNat f := by
  rw [Polynomial.contentNat, Polynomial.contentNat, Polynomial.content_C_mul,
    Int.natAbs_mul, ← Int.abs_eq_normalize, Int.natAbs_abs]

private theorem contentNat_ne_zero (f : Polynomial ℤ) (hf : f ≠ 0) :
    Polynomial.contentNat f ≠ 0 := by
  rw [Polynomial.contentNat, Int.natAbs_ne_zero]
  exact fun h ↦ hf (Polynomial.content_eq_zero_iff.mp h)

private theorem primePowOrder_dvd_coeff
    (hp : p.Prime) (f : Polynomial ℤ) (n : ℕ) :
    ((p ^ Polynomial.coefficientPadicOrder p f : ℕ) : ℤ) ∣ f.coeff n := by
  let _ : Fact p.Prime := ⟨hp⟩
  apply dvd_trans (Int.natCast_dvd_natCast.mpr ?_) (contentNat_dvd_coeff f n)
  exact (padicValNat_dvd_iff (Polynomial.coefficientPadicOrder p f)
    (Polynomial.contentNat f)).2 (Or.inr le_rfl)

/-- Reconstruct `f` as its normalized polynomial times the removed power of `p`. -/
theorem _root_.Polynomial.normalizeAtPrime_spec
    (hp : p.Prime) (f : Polynomial ℤ) (_hf : f ≠ 0) :
  f = Polynomial.C
      ((p ^ Polynomial.coefficientPadicOrder p f : ℕ) : ℤ) *
    Polynomial.normalizeAtPrime p f := by
  ext n
  rw [Polynomial.coeff_C_mul, Polynomial.normalizeAtPrime, coeff_coeffDiv]
  exact (Int.mul_ediv_cancel_of_emod_eq_zero
    (Int.dvd_iff_emod_eq_zero.mp (primePowOrder_dvd_coeff hp f n))).symm

/-- A nonzero polynomial normalized at a prime has content not divisible by that prime. -/
theorem _root_.Polynomial.normalizeAtPrime_primitive
    (hp : p.Prime) (f : Polynomial ℤ) (hf : f ≠ 0) :
  ¬ p ∣ Polynomial.contentNat (Polynomial.normalizeAtPrime p f) := by
  let _ : Fact p.Prime := ⟨hp⟩
  intro hdiv
  have hcontent := congrArg Polynomial.contentNat
    (Polynomial.normalizeAtPrime_spec hp f hf)
  rw [contentNat_C_mul] at hcontent
  simp only [Nat.cast_pow, Int.natAbs_pow, Int.natAbs_natCast] at hcontent
  have hcontra : p ^ (Polynomial.coefficientPadicOrder p f + 1) ∣
      Polynomial.contentNat f := by
    rw [hcontent, pow_succ']
    simpa [Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_dvd_mul_left (p ^ Polynomial.coefficientPadicOrder p f) hdiv
  exact (pow_succ_padicValNat_not_dvd (p := p) (contentNat_ne_zero f hf))
    (by simpa [Polynomial.coefficientPadicOrder] using hcontra)

private theorem primeScaleTranslate_eq_taylor_comp
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) :
    Polynomial.primeScaleTranslate f p mu =
      (Polynomial.taylor mu f).comp (Polynomial.C (p : ℤ) * Polynomial.X) := by
  simp only [Polynomial.primeScaleTranslate, Polynomial.taylor_apply,
    Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.C_comp]

private theorem primeScaleTranslate_coeff
    (f : Polynomial ℤ) (p n : ℕ) (mu : ℤ) :
    (Polynomial.primeScaleTranslate f p mu).coeff n =
      (Polynomial.taylor mu f).coeff n * (p : ℤ) ^ n := by
  rw [primeScaleTranslate_eq_taylor_comp, Polynomial.comp_C_mul_X_coeff]

private theorem primeScaleTranslate_ne_zero
    (hp : p.Prime) (g : Polynomial ℤ) (hg : g ≠ 0) (mu : ℤ) :
    Polynomial.primeScaleTranslate g p mu ≠ 0 := by
  rw [primeScaleTranslate_eq_taylor_comp]
  intro hzero
  have htaylor : Polynomial.taylor mu g = 0 :=
    (Polynomial.comp_C_mul_X_eq_zero_iff (p := Polynomial.taylor mu g)
      (by simp [hp.ne_zero])).mp hzero
  exact hg ((Polynomial.taylor_eq_zero mu g).mp htaylor)

private theorem taylor_coefficient_at_rootMultiplicity_ne_zero
    [Fact p.Prime] (g : Polynomial ℤ) (hg : Polynomial.modPrime p g ≠ 0)
    (mu : ZMod p) :
    (Polynomial.taylor mu (Polynomial.modPrime p g)).coeff
        ((Polynomial.modPrime p g).rootMultiplicity mu) ≠ 0 := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr
    ((Polynomial.taylor_eq_zero mu (Polynomial.modPrime p g)).not.mpr hg)

private theorem integerTaylorCoefficient_at_rootMultiplicity_not_dvd
    [Fact p.Prime] (g : Polynomial ℤ) (hg : Polynomial.modPrime p g ≠ 0)
    (mu : ZMod p) :
    ¬ (p : ℤ) ∣ (Polynomial.taylor (mu.val : ℤ) g).coeff
      ((Polynomial.modPrime p g).rootMultiplicity mu) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change ((Int.castRingHom (ZMod p))
    ((Polynomial.taylor (mu.val : ℤ) g).coeff
      ((Polynomial.modPrime p g).rootMultiplicity mu))) ≠ 0
  rw [← Polynomial.coeff_map]
  simpa [Polynomial.modPrime] using
    taylor_coefficient_at_rootMultiplicity_ne_zero g hg mu

private theorem primeScaleTranslate_order_le_rootMultiplicity
    [Fact p.Prime] (hp : p.Prime) (g : Polynomial ℤ)
    (hg : Polynomial.modPrime p g ≠ 0) (mu : ZMod p) :
    Polynomial.coefficientPadicOrder p
        (Polynomial.primeScaleTranslate g p mu.val) ≤
      (Polynomial.modPrime p g).rootMultiplicity mu := by
  let m := (Polynomial.modPrime p g).rootMultiplicity mu
  let u := Polynomial.coefficientPadicOrder p
    (Polynomial.primeScaleTranslate g p mu.val)
  by_contra hle
  have hmu : m + 1 ≤ u := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hle)
  have horder : (((p ^ u : ℕ) : ℤ)) ∣
      (Polynomial.primeScaleTranslate g p mu.val).coeff m := by
    exact primePowOrder_dvd_coeff hp _ m
  have hpow : (((p ^ (m + 1) : ℕ) : ℤ)) ∣
      ((p ^ u : ℕ) : ℤ) := by
    exact Int.natCast_dvd_natCast.mpr (pow_dvd_pow p hmu)
  have hdiv := dvd_trans hpow horder
  have hcancel : ((p : ℤ) ^ m) * (p : ℤ) ∣
      ((p : ℤ) ^ m) * (Polynomial.taylor (mu.val : ℤ) g).coeff m := by
    simpa [primeScaleTranslate_coeff, Nat.cast_pow, pow_succ,
      mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hpne : (p : ℤ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hpdiv : (p : ℤ) ∣
      (Polynomial.taylor (mu.val : ℤ) g).coeff m :=
    (mul_dvd_mul_iff_left hpne).mp hcancel
  exact integerTaylorCoefficient_at_rootMultiplicity_not_dvd g hg mu hpdiv

/-- ACK Lemma 2.2: reduction modulo `p` cannot increase the degree. -/
theorem _root_.Polynomial.ack_lemma_2_2_degree
    [Fact p.Prime] (hp : p.Prime) (g : Polynomial ℤ)
    (hg : Polynomial.modPrime p g ≠ 0) (mu : ZMod p)
    (_hmu : (Polynomial.modPrime p g).IsRoot mu) :
  (Polynomial.modPrime p
      (Polynomial.normalizedPrimeScaleTranslate g p mu.val)).natDegree ≤
    (Polynomial.modPrime p g).rootMultiplicity mu := by
  let m := (Polynomial.modPrime p g).rootMultiplicity mu
  let u := Polynomial.coefficientPadicOrder p
    (Polynomial.primeScaleTranslate g p mu.val)
  have hg0 : g ≠ 0 := by
    intro h
    simp [h, Polynomial.modPrime] at hg
  have htranslate : Polynomial.primeScaleTranslate g p mu.val ≠ 0 :=
    primeScaleTranslate_ne_zero hp g hg0 mu.val
  have hule : u ≤ m := primeScaleTranslate_order_le_rootMultiplicity hp g hg mu
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hmn
  rw [Polynomial.modPrime, Polynomial.coeff_map]
  change (((Polynomial.normalizedPrimeScaleTranslate g p mu.val).coeff n : ℤ) :
    ZMod p) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hun : u + 1 ≤ n := Nat.succ_le_iff.mpr (lt_of_le_of_lt hule hmn)
  have hbig : (((p ^ (u + 1) : ℕ) : ℤ)) ∣
      (Polynomial.primeScaleTranslate g p mu.val).coeff n := by
    rw [primeScaleTranslate_coeff]
    simpa [Nat.cast_pow] using
      ((pow_dvd_pow (p : ℤ) hun).mul_left
        ((Polynomial.taylor (mu.val : ℤ) g).coeff n))
  have hspec := congrArg (fun f : Polynomial ℤ ↦ f.coeff n)
    (Polynomial.normalizeAtPrime_spec hp
      (Polynomial.primeScaleTranslate g p mu.val) htranslate)
  simp only [Polynomial.coeff_C_mul] at hspec
  change (Polynomial.primeScaleTranslate g p mu.val).coeff n =
    (p : ℤ) ^ u *
      (Polynomial.normalizedPrimeScaleTranslate g p mu.val).coeff n at hspec
  rw [hspec] at hbig
  have hcancel : ((p : ℤ) ^ u) * (p : ℤ) ∣
      ((p : ℤ) ^ u) *
        (Polynomial.normalizedPrimeScaleTranslate g p mu.val).coeff n := by
    simpa [Polynomial.normalizedPrimeScaleTranslate, Nat.cast_pow, pow_succ,
      mul_comm, mul_left_comm, mul_assoc] using hbig
  exact (mul_dvd_mul_iff_left
    (pow_ne_zero u (by exact_mod_cast hp.ne_zero))).mp hcancel

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
            intro x _
            exact (Polynomial.count_roots (Polynomial.modPrime p f)).symm
      _ ≤ (Polynomial.modPrime p f).natDegree :=
        Polynomial.card_roots' (Polynomial.modPrime p f)

/-- ACK Lemma 2.2: the multiplicity-weighted root count modulo `p` is degree-bounded. -/
theorem _root_.Polynomial.ack_lemma_2_2_rootMass
    [Fact p.Prime] (hp : p.Prime) (g : Polynomial ℤ)
    (hg : Polynomial.modPrime p g ≠ 0) (mu : ZMod p)
    (hmu : (Polynomial.modPrime p g).IsRoot mu) :
  Polynomial.rootMassModPrime p
      (Polynomial.normalizedPrimeScaleTranslate g p mu.val) ≤
    (Polynomial.modPrime p g).rootMultiplicity mu :=
  (rootMassModPrime_le_natDegree p _).trans
    (Polynomial.ack_lemma_2_2_degree hp g hg mu hmu)

private theorem stationaryTranslate_coeff_of_pos
    (f : Polynomial ℤ) (p n : ℕ) (mu : ℤ) (hn : 0 < n) :
    (Polynomial.stationaryTranslate f p mu).coeff n =
      (Polynomial.taylor mu f).coeff n * (p : ℤ) ^ n := by
  rw [Polynomial.stationaryTranslate, Polynomial.coeff_sub,
    primeScaleTranslate_coeff]
  rw [Polynomial.coeff_C]
  simp [hn.ne']

private theorem stationaryTranslate_coeff_zero
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) :
    (Polynomial.stationaryTranslate f p mu).coeff 0 = 0 := by
  simp [Polynomial.stationaryTranslate, primeScaleTranslate_coeff,
    Polynomial.taylor_coeff_zero]

private theorem stationaryTranslate_ne_zero_of_natDegree_pos
    (hp : p.Prime) (f : Polynomial ℤ) (hf : f ≠ 0)
    (hdegree : 0 < f.natDegree) (mu : ℤ) :
    Polynomial.stationaryTranslate f p mu ≠ 0 := by
  have hprime : Polynomial.primeScaleTranslate f p mu ≠ 0 :=
    primeScaleTranslate_ne_zero hp f hf mu
  have hprimeDegree : (Polynomial.primeScaleTranslate f p mu).natDegree =
      f.natDegree := by
    rw [primeScaleTranslate_eq_taylor_comp, Polynomial.natDegree_comp,
      Polynomial.natDegree_taylor,
      Polynomial.natDegree_C_mul_X (p : ℤ) (by exact_mod_cast hp.ne_zero),
      Nat.mul_one]
  intro hzero
  have hdegreeZero := congrArg Polynomial.natDegree hzero
  rw [Polynomial.stationaryTranslate,
    Polynomial.natDegree_sub_eq_left_of_natDegree_lt] at hdegreeZero
  · simp [hprimeDegree, hdegree.ne'] at hdegreeZero
  · simpa [hprimeDegree] using hdegree

private theorem modPrime_nonconstantPart_ne_zero_of_primitive
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
  have hn := congrArg (fun q : Polynomial (ZMod p) ↦ q.coeff n) hzero
  simpa [Polynomial.modPrime] using hn

private theorem nonconstant_natDegree_pos_of_primitive
    (hp : p.Prime) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
    0 < f.natDegree := by
  have hbar := modPrime_nonconstantPart_ne_zero_of_primitive hp f hprimitive
  have hdegree : (Polynomial.modPrime p (Polynomial.nonconstantPart f)).natDegree ≤
      f.natDegree := by
    calc
      _ ≤ (Polynomial.nonconstantPart f).natDegree := Polynomial.natDegree_map_le
      _ = f.natDegree := Polynomial.natDegree_sub_C
  exact Nat.pos_of_ne_zero fun hfdegree ↦ hbar <| by
    have hbarDegree :
        (Polynomial.modPrime p (Polynomial.nonconstantPart f)).natDegree ≤ 0 := by
      omega
    rw [Polynomial.eq_C_of_natDegree_le_zero hbarDegree]
    simp [Polynomial.modPrime, Polynomial.nonconstantPart]

private theorem contentOrder_le_of_coeff_factor
    {p : ℕ} (hp : p.Prime) (F : Polynomial ℤ) (n : ℕ) (t : ℤ)
    (hcoeff : F.coeff n = t * (p : ℤ) ^ n)
    (ht : ¬ (p : ℤ) ∣ t) :
    Polynomial.coefficientPadicOrder p F ≤ n := by
  let u := Polynomial.coefficientPadicOrder p F
  by_contra hle
  have hnu : n + 1 ≤ u := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hle)
  have horder : (((p ^ u : ℕ) : ℤ)) ∣ F.coeff n :=
    primePowOrder_dvd_coeff hp F n
  have hpow : (((p ^ (n + 1) : ℕ) : ℤ)) ∣ ((p ^ u : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (pow_dvd_pow p hnu)
  have hdiv := dvd_trans hpow horder
  rw [hcoeff] at hdiv
  have hcancel : ((p : ℤ) ^ n) * (p : ℤ) ∣ ((p : ℤ) ^ n) * t := by
    simpa [Nat.cast_pow, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hdiv
  exact ht ((mul_dvd_mul_iff_left
    (pow_ne_zero n (by exact_mod_cast hp.ne_zero))).mp hcancel)

private theorem stationaryTranslate_all_coeff_dvd
    {p : ℕ} (_hp : p.Prime) (f : Polynomial ℤ) (mu : ℤ) (n : ℕ) :
    (p : ℤ) ∣ (Polynomial.stationaryTranslate f p mu).coeff n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp [stationaryTranslate_coeff_zero]
  · rw [stationaryTranslate_coeff_of_pos f p n mu hn]
    exact dvd_mul_of_dvd_right (dvd_pow_self (p : ℤ) hn.ne') _

private theorem one_le_stationaryOrder
    {p : ℕ} {mu : ℤ} (hp : p.Prime) (f : Polynomial ℤ)
    (htranslate : Polynomial.stationaryTranslate f p mu ≠ 0) :
    1 ≤ Polynomial.stationaryOrder f p mu := by
  let _ : Fact p.Prime := ⟨hp⟩
  apply one_le_padicValNat_of_dvd
  · exact contentNat_ne_zero _ htranslate
  · rw [Polynomial.contentNat, ← Int.natCast_dvd]
    exact Polynomial.dvd_content_iff_C_dvd.mpr <|
      (Polynomial.C_dvd_iff_dvd_coeff (p : ℤ) _).mpr
        (stationaryTranslate_all_coeff_dvd hp f mu)

private theorem stationaryOrder_le_natDegree
    {p : ℕ} (hp : p.Prime) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) (mu : ℤ) :
    Polynomial.stationaryOrder f p mu ≤ f.natDegree := by
  let fbar := Polynomial.modPrime p (Polynomial.nonconstantPart f)
  let tau := fbar.natDegree
  have hfbar : fbar ≠ 0 :=
    modPrime_nonconstantPart_ne_zero_of_primitive hp f hprimitive
  have hcoeffZero : fbar.coeff 0 = 0 := by
    simp [fbar, Polynomial.modPrime, Polynomial.nonconstantPart]
  have htau : 0 < tau := by
    apply Nat.pos_of_ne_zero
    intro htauZero
    apply hfbar
    rw [Polynomial.eq_C_of_natDegree_le_zero (p := fbar) (by omega), hcoeffZero,
      Polynomial.C_0]
  have htauDegree : tau ≤ f.natDegree := by
    calc
      tau ≤ (Polynomial.nonconstantPart f).natDegree := Polynomial.natDegree_map_le
      _ = f.natDegree := Polynomial.natDegree_sub_C
  have htaylorBar : (Polynomial.taylor (mu : ZMod p) fbar).coeff tau ≠ 0 := by
    have htaylorNe : Polynomial.taylor (mu : ZMod p) fbar ≠ 0 :=
      (Polynomial.taylor_eq_zero (mu : ZMod p) fbar).not.mpr hfbar
    have htaylorDegree :
        (Polynomial.taylor (mu : ZMod p) fbar).natDegree = tau := by
      simp [tau]
    rw [← htaylorDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr htaylorNe
  have htaylorInt : ¬ (p : ℤ) ∣ (Polynomial.taylor mu f).coeff tau := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change ((Int.castRingHom (ZMod p)) ((Polynomial.taylor mu f).coeff tau)) ≠ 0
    rw [← Polynomial.coeff_map]
    have hmap := Polynomial.map_taylor f mu (Int.castRingHom (ZMod p))
    rw [hmap]
    have hcoeffEq : (Polynomial.taylor (mu : ZMod p) fbar).coeff tau =
        (Polynomial.taylor (mu : ZMod p) (Polynomial.modPrime p f)).coeff tau := by
      rw [show fbar = Polynomial.modPrime p f -
          Polynomial.C ((f.coeff 0 : ℤ) : ZMod p) by
        simp [fbar, Polynomial.modPrime, Polynomial.nonconstantPart]]
      simp only [map_sub, Polynomial.coeff_sub, Polynomial.taylor_C,
        Polynomial.coeff_C]
      simp [htau.ne']
    rw [hcoeffEq] at htaylorBar
    simpa [Polynomial.modPrime] using htaylorBar
  change Polynomial.coefficientPadicOrder p
      (Polynomial.stationaryTranslate f p mu) ≤ f.natDegree
  exact (contentOrder_le_of_coeff_factor hp _ tau _
    (stationaryTranslate_coeff_of_pos f p tau mu htau) htaylorInt).trans htauDegree

/-- ACK Lemma 2.3: stationary order and child degree are controlled by the
multiplicity of the corresponding derivative root. -/
theorem _root_.Polynomial.ack_lemma_2_3
    (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ℤ) :
  1 ≤ Polynomial.stationaryOrder f p mu ∧
    Polynomial.stationaryOrder f p mu ≤ d := by
  have hdegpos := nonconstant_natDegree_pos_of_primitive hp f hprimitive
  have hf : f ≠ 0 := by
    intro h
    subst f
    simp at hdegpos
  have htranslate := stationaryTranslate_ne_zero_of_natDegree_pos hp f hf hdegpos mu
  exact ⟨one_le_stationaryOrder hp f htranslate,
    (stationaryOrder_le_natDegree hp f hprimitive mu).trans hdegree⟩

private theorem stationaryTranslate_natDegree
    (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : 0 < f.natDegree) (mu : ℤ) :
    (Polynomial.stationaryTranslate f p mu).natDegree = f.natDegree := by
  have hprimeDegree : (Polynomial.primeScaleTranslate f p mu).natDegree =
      f.natDegree := by
    rw [primeScaleTranslate_eq_taylor_comp, Polynomial.natDegree_comp,
      Polynomial.natDegree_taylor,
      Polynomial.natDegree_C_mul_X (p : ℤ) (by exact_mod_cast hp.ne_zero),
      Nat.mul_one]
  rw [Polynomial.stationaryTranslate,
    Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  · exact hprimeDegree
  · calc
      (Polynomial.C (f.eval mu)).natDegree ≤ 0 := by simp
      _ < (Polynomial.primeScaleTranslate f p mu).natDegree := by
        rw [hprimeDegree]
        exact hdegree

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

/-- Package the invariants satisfied by a normalized stationary child. -/
theorem _root_.Polynomial.stationaryChildInvariant
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hd : 0 < d)
    (_hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ℤ) :
  Polynomial.StationaryChildInvariant f p mu d := by
  have hf : f ≠ 0 := by
    intro hzero
    exact hd.ne' (by simpa [hzero] using hdegree.symm)
  have hfdegree : 0 < f.natDegree := hdegree.symm ▸ hd
  have htranslate : Polynomial.stationaryTranslate f p mu ≠ 0 :=
    stationaryTranslate_ne_zero_of_natDegree_pos hp f hf hfdegree mu
  have hnormDegree : (Polynomial.stationaryNormalize f p mu).natDegree = d := by
    rw [Polynomial.stationaryNormalize,
      normalizeAtPrime_natDegree hp _ htranslate,
      stationaryTranslate_natDegree hp f hfdegree mu, hdegree]
  have hcoeffSpec := congrArg (fun q : Polynomial ℤ ↦ q.coeff 0)
    (Polynomial.normalizeAtPrime_spec hp
      (Polynomial.stationaryTranslate f p mu) htranslate)
  simp only [Polynomial.coeff_C_mul, stationaryTranslate_coeff_zero] at hcoeffSpec
  have hscalar :
      (((p ^ Polynomial.stationaryOrder f p mu : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast pow_ne_zero (Polynomial.stationaryOrder f p mu) hp.ne_zero
  have hcoeffZero : (Polynomial.stationaryNormalize f p mu).coeff 0 = 0 := by
    apply (mul_eq_zero.mp hcoeffSpec.symm).resolve_left
    simpa [Polynomial.stationaryOrder, Polynomial.coefficientPadicOrder] using hscalar
  have hfullPrimitive :
      ¬ p ∣ Polynomial.contentNat (Polynomial.stationaryNormalize f p mu) := by
    exact Polynomial.normalizeAtPrime_primitive hp _ htranslate
  refine ⟨htranslate, hnormDegree, hcoeffZero, ?_⟩
  simpa [Polynomial.nonconstantContentNat, Polynomial.nonconstantPart,
    hcoeffZero] using hfullPrimitive

private theorem stationaryTranslate_all_coeff_prime_sq_dvd
    (hp : p.Prime) (f : Polynomial ℤ) (mu : ZMod p)
    (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) (n : ℕ) :
    ((p ^ 2 : ℕ) : ℤ) ∣ (Polynomial.stationaryTranslate f p mu.val).coeff n := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  obtain rfl | rfl | n := n
  · simp [stationaryTranslate_coeff_zero]
  · rw [stationaryTranslate_coeff_of_pos f p 1 mu.val Nat.zero_lt_one]
    have hderiv : (p : ℤ) ∣ f.derivative.eval mu.val := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      change (Int.castRingHom (ZMod p)) (f.derivative.eval mu.val) = 0
      rw [← Polynomial.eval_map_apply]
      simpa [Polynomial.modPrime, Polynomial.IsRoot, Int.cast_natCast,
        ZMod.natCast_zmod_val] using hmu
    rw [Polynomial.taylor_coeff_one, pow_one, pow_two]
    rcases hderiv with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    norm_num [Nat.cast_pow]
    ring
  · rw [stationaryTranslate_coeff_of_pos f p (n + 2) mu.val (by omega)]
    have hpow : (p : ℤ) ^ 2 ∣ (p : ℤ) ^ (n + 2) :=
      pow_dvd_pow (p : ℤ) (by omega)
    simpa [Nat.cast_pow] using
      hpow.mul_left ((Polynomial.taylor (mu.val : ℤ) f).coeff (n + 2))

/-- A derivative root forces the associated stationary translate to have order at least two. -/
theorem _root_.Polynomial.stationaryOrder_two_le_of_isRoot
    (hp : p.Prime) (f : Polynomial ℤ) (mu : ZMod p)
    (htranslate : Polynomial.stationaryTranslate f p mu.val ≠ 0)
    (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  2 ≤ Polynomial.stationaryOrder f p mu.val := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [Polynomial.stationaryOrder, Polynomial.coefficientPadicOrder]
  apply (padicValNat_dvd_iff_le (p := p)
    (contentNat_ne_zero _ htranslate)).mp
  rw [Polynomial.contentNat, ← Int.natCast_dvd]
  apply Polynomial.dvd_content_iff_C_dvd.mpr
  exact (Polynomial.C_dvd_iff_dvd_coeff (((p ^ 2 : ℕ) : ℤ)) _).mpr
    (stationaryTranslate_all_coeff_prime_sq_dvd hp f mu hmu)

/-- A convexity bound controlling a finite sum of powers with prescribed total exponent. -/
theorem chen_convexity_bound
    {I : Type*} (s : Finset I) (a : ℝ) (m : I → ℕ)
    (ha : 1 < a) (hm : ∀ i ∈ s, 0 < m i) :
  ∑ i ∈ s, a ^ m i ≤
    max (((∑ i ∈ s, m i : ℕ) : ℝ) * a)
      (a ^ (∑ i ∈ s, m i)) := by
  classical
  let K := ∑ i ∈ s, m i
  have hmK (i : I) (hi : i ∈ s) : m i ≤ K := by
    exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (m j)) hi
  have hcardK : s.card ≤ K := by
    calc
      s.card = ∑ i ∈ s, 1 := by simp
      _ ≤ ∑ i ∈ s, m i :=
        Finset.sum_le_sum fun i hi ↦ hm i hi
      _ = K := rfl
  by_cases hK : K ≤ 1
  · have hmOne (i : I) (hi : i ∈ s) : m i = 1 := by
      have := hm i hi
      have := hmK i hi
      omega
    have hKcard : K = s.card := by
      calc
        K = ∑ i ∈ s, m i := rfl
        _ = ∑ i ∈ s, 1 := Finset.sum_congr rfl hmOne
        _ = s.card := by simp
    calc
      ∑ i ∈ s, a ^ m i = ∑ i ∈ s, a := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hmOne i hi, pow_one]
      _ = (s.card : ℝ) * a := by simp
      _ = (K : ℝ) * a := by rw [hKcard]
      _ ≤ max ((K : ℝ) * a) (a ^ K) := le_max_left _ _
  · have hKone : (1 : ℝ) < K := by exact_mod_cast Nat.lt_of_not_ge hK
    have hKsub : (K : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hKone)
    let alpha : I → ℝ := fun i ↦ ((K : ℝ) - m i) / ((K : ℝ) - 1)
    let beta : I → ℝ := fun i ↦ ((m i : ℝ) - 1) / ((K : ℝ) - 1)
    have hchord (i : I) (hi : i ∈ s) :
        a ^ m i ≤ alpha i * a + beta i * a ^ K := by
      have hmiOne : (1 : ℝ) ≤ m i := by exact_mod_cast hm i hi
      have hmiK : (m i : ℝ) ≤ K := by exact_mod_cast hmK i hi
      have halpha : 0 ≤ alpha i := by
        exact div_nonneg (sub_nonneg.mpr hmiK) (sub_nonneg.mpr hKone.le)
      have hbeta : 0 ≤ beta i := by
        exact div_nonneg (sub_nonneg.mpr hmiOne) (sub_nonneg.mpr hKone.le)
      have hab : alpha i + beta i = 1 := by
        dsimp [alpha, beta]
        field_simp
        ring
      have hcombo : alpha i • (1 : ℝ) + beta i • (K : ℝ) = (m i : ℝ) := by
        dsimp [alpha, beta]
        simp only [mul_one]
        field_simp
        ring
      have hconv := (convexOn_rpow_left (lt_trans zero_lt_one ha)).2
        (Set.mem_univ (1 : ℝ)) (Set.mem_univ (K : ℝ)) halpha hbeta hab
      rw [hcombo] at hconv
      simpa [alpha, beta, Real.rpow_natCast, smul_eq_mul] using hconv
    have hsumM : ∑ i ∈ s, (m i : ℝ) = (K : ℝ) := by
      exact_mod_cast (show ∑ i ∈ s, m i = K from rfl)
    have hsumAlpha : ∑ i ∈ s, alpha i =
        ((s.card : ℝ) * K - K) / ((K : ℝ) - 1) := by
      dsimp only [alpha]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, hsumM]
      simp only [Finset.sum_const, nsmul_eq_mul]
    have hsumBeta : ∑ i ∈ s, beta i =
        ((K : ℝ) - s.card) / ((K : ℝ) - 1) := by
      dsimp only [beta]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, hsumM]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    let lambda : ℝ := ((s.card : ℝ) - 1) / ((K : ℝ) - 1)
    have hlambdaZero : 0 ≤ lambda := by
      have hsnonempty : s.Nonempty := by
        by_contra hs
        have hKzero : K = 0 := by
          simp [K, Finset.not_nonempty_iff_eq_empty.mp hs]
        exact (by omega)
      exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hsnonempty.card_pos))
        (sub_nonneg.mpr hKone.le)
    have hlambdaOne : lambda ≤ 1 := by
      apply (div_le_one (sub_pos.mpr hKone)).mpr
      exact sub_le_sub_right (by exact_mod_cast hcardK) 1
    have hweighted :
        ((∑ i ∈ s, alpha i) * a +
            (∑ i ∈ s, beta i) * a ^ K) =
          lambda * ((K : ℝ) * a) + (1 - lambda) * a ^ K := by
      rw [hsumAlpha, hsumBeta]
      dsimp [lambda]
      field_simp
      ring
    calc
      ∑ i ∈ s, a ^ m i ≤
          ∑ i ∈ s, (alpha i * a + beta i * a ^ K) :=
        Finset.sum_le_sum hchord
      _ = (∑ i ∈ s, alpha i) * a +
          (∑ i ∈ s, beta i) * a ^ K := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
      _ = lambda * ((K : ℝ) * a) + (1 - lambda) * a ^ K := hweighted
      _ ≤ lambda * max ((K : ℝ) * a) (a ^ K) +
          (1 - lambda) * max ((K : ℝ) * a) (a ^ K) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hlambdaZero)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr hlambdaOne))
      _ = max ((K : ℝ) * a) (a ^ K) := by ring


end TranslationalTilings
