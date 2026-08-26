import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.FiniteDifference
import TranslationalTilings.NumberTheory.CompleteExponentialSum

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 0d459c591e615783c5e7e85e4c6de57640cab5775308ef93d36e12d5be1090e9  blueprint/05-polynomial-rigidity.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05-polynomial-rigidity.md:61; TranslationalTilings.CirclePolynomial -/
namespace TranslationalTilings
structure CirclePolynomial (d : ℕ) where
  coeff : Fin (d + 1) → Torus
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:64; TranslationalTilings.CirclePolynomial.eval -/
namespace TranslationalTilings
def CirclePolynomial.eval (P : CirclePolynomial d) (n : ℤ) : Torus :=
  ∑ i : Fin (d + 1), (n ^ (i : ℕ)) • P.coeff i
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:67; <instance@blueprint/05-polynomial-rigidity.md:67> -/
namespace TranslationalTilings
instance : CoeFun (CirclePolynomial d) (fun _ ↦ ℤ → Torus) :=
  ⟨CirclePolynomial.eval⟩
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:70; TranslationalTilings.CirclePolynomial.CoefficientConstant -/
namespace TranslationalTilings
def CirclePolynomial.CoefficientConstant (P : CirclePolynomial d) : Prop :=
  ∀ i : Fin (d + 1), 0 < (i : ℕ) → P.coeff i = 0
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:73; TranslationalTilings.CirclePolynomial.FunctionConstant -/
namespace TranslationalTilings
def CirclePolynomial.FunctionConstant (P : CirclePolynomial d) : Prop :=
  ∃ c : Torus, ∀ n : ℤ, P n = c
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:76; TranslationalTilings.CirclePolynomial.HasTorsionNonconstantCoeffs -/
namespace TranslationalTilings
def CirclePolynomial.HasTorsionNonconstantCoeffs
    (P : CirclePolynomial d) : Prop :=
  ∀ i : Fin (d + 1), 0 < (i : ℕ) → IsOfFinAddOrder (P.coeff i)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:80; TranslationalTilings.CirclePolynomial.HasRationalNonconstantCoeffs -/
namespace TranslationalTilings
def CirclePolynomial.HasRationalNonconstantCoeffs
    (P : CirclePolynomial d) : Prop :=
  ∀ i : Fin (d + 1), 0 < (i : ℕ) →
    ∃ q : ℚ, P.coeff i = ((q : ℝ) : Torus)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:85; TranslationalTilings.CirclePolynomial.nonconstantIndices -/
namespace TranslationalTilings
def CirclePolynomial.nonconstantIndices (d : ℕ) : Finset (Fin (d + 1)) :=
  Finset.univ.filter fun i ↦ 0 < (i : ℕ)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:88; TranslationalTilings.CirclePolynomial.commonDenominator -/
namespace TranslationalTilings
noncomputable def CirclePolynomial.commonDenominator
    (P : CirclePolynomial d) : ℕ :=
  (CirclePolynomial.nonconstantIndices d).lcm
    fun i ↦ addOrderOf (P.coeff i)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:93; TranslationalTilings.CirclePolynomial.AvoidsBall -/
namespace TranslationalTilings
def CirclePolynomial.AvoidsBall (P : CirclePolynomial d)
    (c : Torus) (eps : ℝ) : Prop :=
  ∀ n : ℤ, P n ∉ Metric.ball c eps
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:97; TranslationalTilings.CirclePolynomial.HasHalfCircleLifts -/
namespace TranslationalTilings
def CirclePolynomial.HasHalfCircleLifts (P : CirclePolynomial d) : Prop :=
  ∀ n : ℤ, ∃ t : ℝ,
    t ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) ∧ P n = (t : Torus)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:101; TranslationalTilings.CirclePolynomial.PeriodicWith -/
namespace TranslationalTilings
def CirclePolynomial.PeriodicWith (P : CirclePolynomial d) (Q : ℕ) : Prop :=
  Function.Periodic P (Q : ℤ)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:104; TranslationalTilings.CirclePolynomial.zsmul -/
namespace TranslationalTilings
def CirclePolynomial.zsmul (k : ℤ)
    (P : CirclePolynomial d) : CirclePolynomial d :=
  ⟨fun i ↦ k • P.coeff i⟩
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:108; TranslationalTilings.cesaroAverage -/
namespace TranslationalTilings
noncomputable def cesaroAverage (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f n
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:111; TranslationalTilings.symmetricCesaroAverage -/
namespace TranslationalTilings
noncomputable def symmetricCesaroAverage (f : ℤ → ℂ) (N : ℕ) : ℂ :=
  ((2 * N + 1 : ℕ) : ℂ)⁻¹ *
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f n
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:115; TranslationalTilings.Equidistributed -/
namespace TranslationalTilings
def Equidistributed (u : ℕ → Torus) : Prop :=
  ∀ f : C(Torus, ℂ), Filter.Tendsto
    (fun N : ℕ ↦ (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (u n))
    Filter.atTop (nhds (∫ x, f x ∂AddCircle.haarAddCircle))
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:120; TranslationalTilings.EquidistributedInt -/
namespace TranslationalTilings
def EquidistributedInt (u : ℤ → Torus) : Prop :=
  ∀ f : C(Torus, ℂ), Filter.Tendsto
    (fun N : ℕ ↦ symmetricCesaroAverage (fun n ↦ f (u n)) N)
    Filter.atTop (nhds (∫ x, f x ∂AddCircle.haarAddCircle))
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:125; TranslationalTilings.completeSum -/
namespace TranslationalTilings
noncomputable def completeSum (P : CirclePolynomial d) (Q : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 Q, circlePhase (P n)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:139; TranslationalTilings.CirclePolynomial.functionConstant_of_coefficientConstant -/
namespace TranslationalTilings
axiom CirclePolynomial.functionConstant_of_coefficientConstant
    (P : CirclePolynomial d) (hP : P.CoefficientConstant) :
  P.FunctionConstant
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:143; TranslationalTilings.CirclePolynomial.not_coefficientConstant_of_not_functionConstant -/
namespace TranslationalTilings
axiom CirclePolynomial.not_coefficientConstant_of_not_functionConstant
    (P : CirclePolynomial d) (hP : ¬ P.FunctionConstant) :
  ¬ P.CoefficientConstant
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:310; TranslationalTilings.intFallingFactorial -/
namespace TranslationalTilings
def intFallingFactorial (n : ℤ) (k : ℕ) : ℤ :=
  ∏ j ∈ Finset.range k, (n - j)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:313; TranslationalTilings.circle_newton_expansion -/
namespace TranslationalTilings
axiom circle_newton_expansion
    (f : ℤ → Torus) (h : backwardDiffIter 1 (d + 1) f = 0) :
  ∃ a : Fin (d + 1) → Torus, ∀ n : ℤ,
    f n = ∑ i : Fin (d + 1),
      intFallingFactorial n (i : ℕ) • a i
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:319; TranslationalTilings.fallingFactorial_to_monomial_circle -/
namespace TranslationalTilings
axiom fallingFactorial_to_monomial_circle
    (a : Fin (d + 1) → Torus) :
  ∃ b : Fin (d + 1) → Torus, ∀ n : ℤ,
    (∑ i : Fin (d + 1), intFallingFactorial n (i : ℕ) • a i) =
      ∑ i : Fin (d + 1), n ^ (i : ℕ) • b i
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:325; TranslationalTilings.exists_circlePolynomial_of_difference -/
namespace TranslationalTilings
axiom exists_circlePolynomial_of_difference
    (f : ℤ → Torus) (h : backwardDiffIter 1 (d + 1) f = 0) :
  ∃ P : CirclePolynomial d, ∀ n : ℤ, P n = f n
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:344; TranslationalTilings.rational_iff_torsion_nonconstant -/
namespace TranslationalTilings
axiom rational_iff_torsion_nonconstant (P : CirclePolynomial d) :
  P.HasRationalNonconstantCoeffs ↔ P.HasTorsionNonconstantCoeffs
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:347; TranslationalTilings.commonDenominator_pos -/
namespace TranslationalTilings
axiom commonDenominator_pos
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  0 < P.commonDenominator
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:351; TranslationalTilings.commonDenominator_eq_zero_of_coeff_addOrderOf_eq_zero -/
namespace TranslationalTilings
axiom commonDenominator_eq_zero_of_coeff_addOrderOf_eq_zero
    (P : CirclePolynomial d) {i : Fin (d + 1)}
    (hi : 0 < (i : ℕ)) (horder : addOrderOf (P.coeff i) = 0) :
  P.commonDenominator = 0
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:356; TranslationalTilings.coeff_zsmul_commonDenominator -/
namespace TranslationalTilings
axiom coeff_zsmul_commonDenominator
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs)
    (i : Fin (d + 1)) (hi : 0 < (i : ℕ)) :
  (P.commonDenominator : ℤ) • P.coeff i = 0
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:361; TranslationalTilings.periodic_commonDenominator -/
namespace TranslationalTilings
axiom periodic_commonDenominator
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  P.PeriodicWith P.commonDenominator
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:365; TranslationalTilings.commonDenominator_zsmul_dvd -/
namespace TranslationalTilings
axiom commonDenominator_zsmul_dvd
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs)
    (k : ℤ) :
  (P.zsmul k).commonDenominator ∣ P.commonDenominator
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:370; TranslationalTilings.commonDenominator_dvd_natAbs_mul_zsmul -/
namespace TranslationalTilings
axiom commonDenominator_dvd_natAbs_mul_zsmul
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs)
    (k : ℤ) :
  P.commonDenominator ∣
    Int.natAbs k * (P.zsmul k).commonDenominator
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:376; TranslationalTilings.normalized_completeSum_repeat -/
namespace TranslationalTilings
axiom normalized_completeSum_repeat
    (P : CirclePolynomial d) (Q Q' : ℕ)
    (hQ : 0 < Q) (hQ' : 0 < Q') (hdiv : Q' ∣ Q)
    (hperiod : P.PeriodicWith Q') :
  (Q : ℂ)⁻¹ * completeSum P Q =
    (Q' : ℂ)⁻¹ * completeSum P Q'
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:383; TranslationalTilings.normalized_completeSum_repeat_zero_regression -/
namespace TranslationalTilings
axiom normalized_completeSum_repeat_zero_regression :
  let P : CirclePolynomial 0 := ⟨fun _ ↦ 0⟩
  (0 : ℂ)⁻¹ * completeSum P 0 ≠
    (1 : ℂ)⁻¹ * completeSum P 1
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:408; TranslationalTilings.exists_integralPhase -/
namespace TranslationalTilings
axiom exists_integralPhase
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  ∃ A : IntegralPolynomialPhase d,
    A.modulus = P.commonDenominator ∧ A.Primitive ∧
    ∀ n : ℤ, P n = P.coeff 0 +
      (((A.evalNumerator n : ℝ) / A.modulus : ℝ) : Torus)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:415; TranslationalTilings.CirclePolynomial.integralPhase -/
namespace TranslationalTilings
noncomputable def CirclePolynomial.integralPhase
    (P : CirclePolynomial d)
    (hP : P.HasTorsionNonconstantCoeffs) : IntegralPolynomialPhase d :=
  Classical.choose (exists_integralPhase P hP)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:420; TranslationalTilings.integralPhase_modulus -/
namespace TranslationalTilings
axiom integralPhase_modulus
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  (P.integralPhase hP).modulus = P.commonDenominator
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:424; TranslationalTilings.integralPhase_primitive -/
namespace TranslationalTilings
axiom integralPhase_primitive
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  (P.integralPhase hP).Primitive
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:428; TranslationalTilings.integralPhase_eval -/
namespace TranslationalTilings
axiom integralPhase_eval
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) (n : ℤ) :
  P n = P.coeff 0 +
    ((((P.integralPhase hP).evalNumerator n : ℝ) /
      (P.integralPhase hP).modulus : ℝ) : Torus)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:434; TranslationalTilings.norm_completeSum_eq_integralPhase -/
namespace TranslationalTilings
axiom norm_completeSum_eq_integralPhase
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  ‖completeSum P P.commonDenominator‖ =
    ‖integralCompleteSum (P.integralPhase hP)‖
end TranslationalTilings
