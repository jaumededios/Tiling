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
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 81b1799e2e08cdaa6639df75a16e15fb3c415793ee04f52cc3cdd2def5dd15a3  blueprint/05b-chen-complete-sums.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05b-chen-complete-sums.md:471; TranslationalTilings.primePowerResidueClassSum -/
namespace TranslationalTilings
noncomputable def primePowerResidueClassSum
    (p a : ℕ) (hp : p.Prime) (f : Polynomial ℤ)
    (v : ZMod p) : ℂ :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  ∑ x : ZMod (p ^ a),
    if (x.val : ZMod p) = v then
      ZMod.stdAddChar (Polynomial.eval x (f.map (Int.castRingHom _)))
    else 0
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:481; TranslationalTilings.primePowerStationaryShortSum -/
namespace TranslationalTilings
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
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:492; TranslationalTilings.ack_completeSum_eq_sum_residueClasses -/
namespace TranslationalTilings
axiom ack_completeSum_eq_sum_residueClasses
    [Fact p.Prime] (hp : p.Prime) (ha : 0 < a)
    (f : Polynomial ℤ) :
  polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f =
    ∑ v : ZMod p, primePowerResidueClassSum p a hp f v
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:498; TranslationalTilings.ack_eq_2_3_vanish -/
namespace TranslationalTilings
axiom ack_eq_2_3_vanish
    (hp : p.Prime) (ha : 2 ≤ a) (f : Polynomial ℤ) (v : ZMod p)
    (hv : ¬ (Polynomial.modPrime p f.derivative).IsRoot v) :
  primePowerResidueClassSum p a hp f v = 0
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:503; TranslationalTilings.ack_eq_2_4 -/
namespace TranslationalTilings
axiom ack_eq_2_4
    (hp : p.Prime) (ha : 2 ≤ a) (f : Polynomial ℤ) (mu : ZMod p)
    (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  primePowerResidueClassSum p a hp f mu =
    (p : ℂ) * primePowerStationaryShortSum p a hp f mu
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:509; TranslationalTilings.ack_eq_2_5 -/
namespace TranslationalTilings
axiom ack_eq_2_5
    (hp : p.Prime) (ha : 2 ≤ a) (f : Polynomial ℤ) (mu : ZMod p)
    (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu)
    (htranslate : Polynomial.stationaryTranslate f p mu.val ≠ 0)
    (hsigma : Polynomial.stationaryOrder f p mu.val < a) :
  ‖primePowerResidueClassSum p a hp f mu‖ =
    (p : ℝ) ^ (Polynomial.stationaryOrder f p mu.val - 1) *
      ‖polynomialCompleteSum
        (p ^ (a - Polynomial.stationaryOrder f p mu.val))
        (pow_pos hp.pos _) (Polynomial.stationaryNormalize f p mu.val)‖
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:520; TranslationalTilings.ack_residueClass_trivial -/
namespace TranslationalTilings
axiom ack_residueClass_trivial
    (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ) (v : ZMod p) :
  ‖primePowerResidueClassSum p a hp f v‖ ≤ (p : ℝ) ^ (a - 1)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:563; TranslationalTilings.chenLargePrimeThreshold -/
namespace TranslationalTilings
noncomputable def chenLargePrimeThreshold (d : ℕ) : ℝ :=
  Real.rpow (d - 1 : ℝ) ((2 * d : ℝ) / (d - 2 : ℝ))
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:566; TranslationalTilings.chenMiddlePrimeThreshold -/
namespace TranslationalTilings
noncomputable def chenMiddlePrimeThreshold (d : ℕ) : ℝ :=
  Real.rpow (d - 1 : ℝ) ((d : ℝ) / (d - 2 : ℝ))
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:571; Polynomial.stationaryOrder_two_le -/
namespace TranslationalTilings
axiom _root_.Polynomial.stationaryOrder_two_le
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  2 ≤ Polynomial.stationaryOrder f p mu.val
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:578; Polynomial.stationaryOrder_le_rootMultiplicity_succ -/
namespace TranslationalTilings
axiom _root_.Polynomial.stationaryOrder_le_rootMultiplicity_succ
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  Polynomial.stationaryOrder f p mu.val ≤
    (Polynomial.modPrime p f.derivative).rootMultiplicity mu + 1
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:586; Polynomial.derivativeRootMass_le -/
namespace TranslationalTilings
axiom _root_.Polynomial.derivativeRootMass_le
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  Polynomial.derivativeRootMass f p ≤ d - 1
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:592; Polynomial.stationaryNormalize_derivativeRootMass_le -/
namespace TranslationalTilings
axiom _root_.Polynomial.stationaryNormalize_derivativeRootMass_le
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  Polynomial.derivativeRootMass
      (Polynomial.stationaryNormalize f p mu.val) p ≤
    (Polynomial.modPrime p f.derivative).rootMultiplicity mu
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:627; TranslationalTilings.chen_prime_base_of -/
namespace TranslationalTilings
axiom chen_prime_base_of
    (hWeil : PolynomialPrimeSumBound)
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hd : 3 ≤ d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum p hp.pos f‖ ≤
    min (Real.rpow p ((1 : ℝ) / d))
        ((d - 1 : ℝ) *
          Real.rpow p (-(1 : ℝ) / 2 + (1 : ℝ) / d)) *
      Real.rpow p (1 - (1 : ℝ) / d)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:652; TranslationalTilings.ack_ineq_2_9 -/
namespace TranslationalTilings
axiom ack_ineq_2_9
    (d m p : ℕ) (hd : 3 ≤ d) (hm : 1 ≤ m) (hmd : m ≤ d - 1)
    (hp : d < p) (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d) :
  Real.rpow p ((m : ℝ) / d) ≤
    (m : ℝ) * Real.rpow p ((1 : ℝ) / d)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:658; TranslationalTilings.ack_ineq_2_11 -/
namespace TranslationalTilings
axiom ack_ineq_2_11
    (d L r₁ M₁ : ℕ) (hd : 3 ≤ d) (hr : 0 < r₁)
    (hL : r₁ * L ≤ M₁ + r₁) :
  (L : ℝ) ≤
    (L + 1 : ℝ) * (1 - (1 : ℝ) / d) - 1 + (2 : ℝ) / d +
      (M₁ : ℝ) / ((r₁ : ℝ) * d)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:665; TranslationalTilings.ack_ineq_2_12 -/
namespace TranslationalTilings
axiom ack_ineq_2_12
    (d r₁ M₁ p : ℕ) (hd : 3 ≤ d) (hr : 1 ≤ r₁)
    (hrM : r₁ ≤ M₁) (hMd : M₁ ≤ d - 1) (hp : d < p)
    (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d) :
  (r₁ : ℝ) *
      Real.rpow p ((M₁ : ℝ) / ((r₁ : ℝ) * d)) ≤
    (M₁ : ℝ) * Real.rpow p ((1 : ℝ) / d)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:684; TranslationalTilings.ack_ineq_2_7_of_inductionBound -/
namespace TranslationalTilings
axiom ack_ineq_2_7_of_inductionBound
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
          (3 : ℝ) / d + (L + 1 : ℝ) * (1 - (1 : ℝ) / d))
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:706; TranslationalTilings.ack_ineq_2_8 -/
namespace TranslationalTilings
axiom ack_ineq_2_8
    (hp : p.Prime) (f : Polynomial ℤ) (L : ℕ) (mu : ZMod p) :
  ‖primePowerResidueClassSum p (L + 1) hp f mu‖ ≤ (p : ℝ) ^ L
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:710; TranslationalTilings.ack_ineq_2_10 -/
namespace TranslationalTilings
axiom ack_ineq_2_10
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
              (L + 1 : ℝ) * (1 - (1 : ℝ) / d))
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:725; TranslationalTilings.ack_eq_2_6 -/
namespace TranslationalTilings
axiom ack_eq_2_6
    [Fact p.Prime] (hp : p.Prime) (ha : 2 ≤ a) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hdp : d < p)
    (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    (Polynomial.derivativeRootMass f p : ℝ) *
      Real.rpow p
        (-1 + (3 : ℝ) / d + (a : ℝ) * (1 - (1 : ℝ) / d))
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:766; Polynomial.derivativeContent_pow_le_degree -/
namespace TranslationalTilings
axiom _root_.Polynomial.derivativeContent_pow_le_degree
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  p ^ Polynomial.derivativeContentOrder f p ≤ d
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:771; Polynomial.mem_smallPrimeStationaryRoots_iff -/
namespace TranslationalTilings
axiom _root_.Polynomial.mem_smallPrimeStationaryRoots_iff
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (v : ZMod p) :
  v ∈ Polynomial.smallPrimeStationaryRoots f p ↔
    (p ^ (Polynomial.derivativeContentOrder f p + 1) : ℤ) ∣
      f.derivative.eval v.val
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:779; Polynomial.smallPrimeStationaryMass_le_degree -/
namespace TranslationalTilings
axiom _root_.Polynomial.smallPrimeStationaryMass_le_degree
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  Polynomial.smallPrimeStationaryMass f p ≤ d - 1
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:785; Polynomial.stationaryNormalize_smallPrimeStationaryMass_le -/
namespace TranslationalTilings
axiom _root_.Polynomial.stationaryNormalize_smallPrimeStationaryMass_le
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (hmu : mu ∈ Polynomial.smallPrimeStationaryRoots f p) :
  Polynomial.smallPrimeStationaryMass
      (Polynomial.stationaryNormalize f p mu.val) p ≤
    (Polynomial.modPrime p
      (Polynomial.normalizedDerivative f p)).rootMultiplicity mu
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:795; TranslationalTilings.ack_smallPrime_block_vanish -/
namespace TranslationalTilings
axiom ack_smallPrime_block_vanish
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hpd : p ≤ d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (ha : 2 * (Polynomial.derivativeContentOrder f p + 1) ≤ a)
    (v : ZMod p) (hv : v ∉ Polynomial.smallPrimeStationaryRoots f p) :
  primePowerResidueClassSum p a hp f v = 0
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:822; TranslationalTilings.ack_eq_2_13 -/
namespace TranslationalTilings
axiom ack_eq_2_13
    [Fact p.Prime] (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hpd : p ≤ d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    Real.rpow d ((3 : ℝ) / d) *
      max 1 (Polynomial.smallPrimeStationaryMass f p : ℝ) *
      Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d))
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:831; TranslationalTilings.ack_eq_2_14 -/
namespace TranslationalTilings
axiom ack_eq_2_14
    [Fact p.Prime] (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hpd : p ≤ d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (hblock : 2 * (Polynomial.derivativeContentOrder f p + 1) ≤ a)
    (mu : ZMod p) (hmu : mu ∈ Polynomial.smallPrimeStationaryRoots f p) :
  ‖primePowerResidueClassSum p a hp f mu‖ ≤
    (Polynomial.modPrime p
      (Polynomial.normalizedDerivative f p)).rootMultiplicity mu *
      Real.rpow d ((3 : ℝ) / d) *
      Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d))
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:867; TranslationalTilings.chenLocalFactor -/
namespace TranslationalTilings
noncomputable def chenLocalFactor (d p : ℕ) : ℝ :=
  if chenLargePrimeThreshold d < (p : ℝ) then 1
  else if chenMiddlePrimeThreshold d ≤ (p : ℝ) then
    Real.rpow d ((2 : ℝ) / d)
  else if d < p then Real.rpow d ((3 : ℝ) / d)
  else (d - 1 : ℝ) * Real.rpow d ((3 : ℝ) / d)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:882; TranslationalTilings.primePower_completeSum_bound_of_primeBound -/
namespace TranslationalTilings
axiom primePower_completeSum_bound_of_primeBound
    (hWeil : PolynomialPrimeSumBound)
    (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    chenLocalFactor d p *
      Real.rpow (p ^ a : ℝ) (1 - (1 : ℝ) / d)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:911; TranslationalTilings.polynomialCompleteSum_crt -/
namespace TranslationalTilings
axiom polynomialCompleteSum_crt
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hcop : Nat.Coprime q₁ q₂)
    {u₁ u₂ : ℤ}
    (hbezout : u₁ * (q₂ : ℤ) + u₂ * (q₁ : ℤ) = 1)
    (f : Polynomial ℤ) :
  polynomialCompleteSum (q₁ * q₂) (Nat.mul_pos hq₁ hq₂) f =
    polynomialCompleteSum q₁ hq₁ (Polynomial.C u₁ * f) *
      polynomialCompleteSum q₂ hq₂ (Polynomial.C u₂ * f)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:920; TranslationalTilings.nonconstantContent_coprime_of_crt_unit -/
namespace TranslationalTilings
axiom nonconstantContent_coprime_of_crt_unit
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hcop : Nat.Coprime q₁ q₂)
    (hprim : Nat.Coprime (q₁ * q₂)
      (Polynomial.nonconstantContentNat f))
    {u₁ u₂ : ℤ}
    (hbezout : u₁ * (q₂ : ℤ) + u₂ * (q₁ : ℤ) = 1) :
  Nat.Coprime q₁
      (Polynomial.nonconstantContentNat (Polynomial.C u₁ * f)) ∧
    Nat.Coprime q₂
      (Polynomial.nonconstantContentNat (Polynomial.C u₂ * f))
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:947; TranslationalTilings.FactorizationPrimeSupport -/
namespace TranslationalTilings
abbrev FactorizationPrimeSupport (q : ℕ) :=
  {p : ℕ // p ∈ q.factorization.support}
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:951; TranslationalTilings.FactorizationScalar -/
namespace TranslationalTilings
abbrev FactorizationScalar (q : ℕ) :=
  FactorizationPrimeSupport q → ℤ
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:954; TranslationalTilings.factorizationPrimeSupport_prime -/
namespace TranslationalTilings
theorem factorizationPrimeSupport_prime {q : ℕ}
    (p : FactorizationPrimeSupport q) : p.1.Prime :=
  Nat.prime_of_mem_primeFactors p.property
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:960; TranslationalTilings.factorizationScalarLookup -/
namespace TranslationalTilings
def factorizationScalarLookup {q : ℕ}
    (u : FactorizationScalar q) (p : ℕ) : ℤ :=
  if hp : p ∈ q.factorization.support then u ⟨p, hp⟩ else 0
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:964; TranslationalTilings.factorizationScalarLookup_of_mem -/
namespace TranslationalTilings
@[simp] theorem factorizationScalarLookup_of_mem
    {q p : ℕ} (u : FactorizationScalar q)
    (hp : p ∈ q.factorization.support) :
  factorizationScalarLookup u p = u ⟨p, hp⟩ := by
  unfold factorizationScalarLookup
  rw [dif_pos hp]
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:971; TranslationalTilings.factorizationScalarLookup_of_not_mem -/
namespace TranslationalTilings
@[simp] theorem factorizationScalarLookup_of_not_mem
    {q p : ℕ} (u : FactorizationScalar q)
    (hp : p ∉ q.factorization.support) :
  factorizationScalarLookup u p = 0 := by
  unfold factorizationScalarLookup
  rw [dif_neg hp]
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:978; TranslationalTilings.factorizationScalar_ext -/
namespace TranslationalTilings
theorem factorizationScalar_ext {q : ℕ}
    {u v : FactorizationScalar q}
    (h : ∀ p, u p = v p) : u = v := by
  funext p
  exact h p
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:984; TranslationalTilings.factorizationScalar_ext_iff_lookup_eq -/
namespace TranslationalTilings
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
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1001; TranslationalTilings.factorizationPrimeSupport_prod_eq -/
namespace TranslationalTilings
theorem factorizationPrimeSupport_prod_eq
    {q : ℕ} {M : Type*} [CommMonoid M] (g : ℕ → M) :
  (∏ p : FactorizationPrimeSupport q, g p.1) =
    ∏ p ∈ q.factorization.support, g p := by
  classical
  exact Finset.prod_coe_sort q.factorization.support g
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1009; TranslationalTilings.factorizationScalar_one_unique -/
namespace TranslationalTilings
theorem factorizationScalar_one_unique
    (u v : FactorizationScalar 1) : u = v := by
  apply factorizationScalar_ext
  intro p
  have hp : False := by simpa using p.property
  exact hp.elim
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1016; TranslationalTilings.factorizationLocalCompleteSum -/
namespace TranslationalTilings
noncomputable def factorizationLocalCompleteSum
    (q : ℕ) (f : Polynomial ℤ) (u : FactorizationScalar q)
    (p : FactorizationPrimeSupport q) : ℂ :=
  polynomialCompleteSum (p.1 ^ q.factorization p.1)
    (pow_pos (factorizationPrimeSupport_prime p).pos _)
    (Polynomial.C (u p) * f)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1023; TranslationalTilings.CompleteSumFactorizationData -/
namespace TranslationalTilings
structure CompleteSumFactorizationData
    (q : ℕ) (hq : 0 < q) (f : Polynomial ℤ) where
  scalar : FactorizationScalar q
  scalar_ne_zero : ∀ p, scalar p ≠ 0
  local_primitive : ∀ p,
    Nat.Coprime (p.1 ^ q.factorization p.1)
      (Polynomial.nonconstantContentNat (Polynomial.C (scalar p) * f))
  norm_eq_product :
    ‖polynomialCompleteSum q hq f‖ =
      ∏ p : FactorizationPrimeSupport q,
        ‖factorizationLocalCompleteSum q f scalar p‖
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1035; TranslationalTilings.CompleteSumFactorizationData.ext_scalar -/
namespace TranslationalTilings
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
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1047; TranslationalTilings.CompleteSumFactorizationData.one_unique -/
namespace TranslationalTilings
theorem CompleteSumFactorizationData.one_unique
    {hq : 0 < 1} {f : Polynomial ℤ}
    (D₁ D₂ : CompleteSumFactorizationData 1 hq f) : D₁ = D₂ := by
  apply CompleteSumFactorizationData.ext_scalar
  intro p
  exact congrFun (factorizationScalar_one_unique D₁.scalar D₂.scalar) p
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1054; Polynomial.natDegree_C_mul_eq -/
namespace TranslationalTilings
axiom _root_.Polynomial.natDegree_C_mul_eq
    (f : Polynomial ℤ) {u : ℤ} (hu : u ≠ 0) :
  (Polynomial.C u * f).natDegree = f.natDegree
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1058; TranslationalTilings.bezout_left_ne_zero_of_one_lt -/
namespace TranslationalTilings
axiom bezout_left_ne_zero_of_one_lt
    (hq₁ : 1 < q₁) {q₂ : ℕ} {u₁ u₂ : ℤ}
    (hbezout : u₁ * (q₂ : ℤ) + u₂ * (q₁ : ℤ) = 1) :
  u₁ ≠ 0
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1063; TranslationalTilings.polynomialCompleteSum_one_norm -/
namespace TranslationalTilings
axiom polynomialCompleteSum_one_norm (f : Polynomial ℤ) :
  ‖polynomialCompleteSum 1 (by omega) f‖ = 1
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1066; TranslationalTilings.exists_completeSumFactorizationData -/
namespace TranslationalTilings
axiom exists_completeSumFactorizationData
    (q : ℕ) (hq : 0 < q) (f : Polynomial ℤ)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  Nonempty (CompleteSumFactorizationData q hq f)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1071; TranslationalTilings.factorization_rpow_product -/
namespace TranslationalTilings
axiom factorization_rpow_product
    (q : ℕ) (hq : 0 < q) (x : ℝ) :
  ∏ p ∈ q.factorization.support,
      Real.rpow (p ^ q.factorization p : ℝ) x =
    Real.rpow q x
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1123; TranslationalTilings.chenExceptionalPrimes -/
namespace TranslationalTilings
def chenExceptionalPrimes (d : ℕ) : Finset ℕ :=
  (Finset.range ((d + 1) ^ 6 + 1)).filter Nat.Prime
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1126; TranslationalTilings.chenGlobalFactor -/
namespace TranslationalTilings
noncomputable def chenGlobalFactor (d : ℕ) : ℝ :=
  ∏ p ∈ chenExceptionalPrimes d, chenLocalFactor d p
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1129; TranslationalTilings.chenLargePrimeExponent_le_six -/
namespace TranslationalTilings
axiom chenLargePrimeExponent_le_six (d : ℕ) (hd : 3 ≤ d) :
  (2 * d : ℝ) / (d - 2 : ℝ) ≤ 6
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1132; TranslationalTilings.chenLargePrimeThreshold_le -/
namespace TranslationalTilings
axiom chenLargePrimeThreshold_le (d : ℕ) (hd : 3 ≤ d) :
  chenLargePrimeThreshold d ≤ (d + 1 : ℝ) ^ 6
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1135; TranslationalTilings.one_le_chenLocalFactor -/
namespace TranslationalTilings
axiom one_le_chenLocalFactor (d p : ℕ) (hd : 3 ≤ d) :
  1 ≤ chenLocalFactor d p
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1138; TranslationalTilings.chenLocalFactor_eq_one_of_prime_not_mem -/
namespace TranslationalTilings
axiom chenLocalFactor_eq_one_of_prime_not_mem
    (d p : ℕ) (hd : 3 ≤ d) (hp : p.Prime)
    (hmem : p ∉ chenExceptionalPrimes d) :
  chenLocalFactor d p = 1
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1143; TranslationalTilings.factorization_localFactor_product_le_global -/
namespace TranslationalTilings
axiom factorization_localFactor_product_le_global
    (d q : ℕ) (hd : 3 ≤ d) (hq : 0 < q) :
  ∏ p ∈ q.factorization.support, chenLocalFactor d p ≤
    chenGlobalFactor d
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1148; TranslationalTilings.one_le_chenGlobalFactor -/
namespace TranslationalTilings
axiom one_le_chenGlobalFactor (d : ℕ) (hd : 3 ≤ d) :
  1 ≤ chenGlobalFactor d
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1158; TranslationalTilings.ack_theorem_2_2_finiteProduct_of_primeBound -/
namespace TranslationalTilings
axiom ack_theorem_2_2_finiteProduct_of_primeBound
    (hWeil : PolynomialPrimeSumBound)
    (d q : ℕ) (hd : 3 ≤ d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    chenGlobalFactor d * Real.rpow q (1 - (1 : ℝ) / d)
end TranslationalTilings
