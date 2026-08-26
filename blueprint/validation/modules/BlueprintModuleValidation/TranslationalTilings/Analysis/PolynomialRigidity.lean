import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.Analysis.CirclePolynomial
import TranslationalTilings.Analysis.Equidistribution
import TranslationalTilings.Analysis.FejerSeparator

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 0d459c591e615783c5e7e85e4c6de57640cab5775308ef93d36e12d5be1090e9  blueprint/05-polynomial-rigidity.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05-polynomial-rigidity.md:471; TranslationalTilings.complete_exponential_sum_paper -/
namespace TranslationalTilings
axiom complete_exponential_sum_paper
    (d : ℕ) (hd : 0 < d) (P : CirclePolynomial d)
    (hrat : P.HasTorsionNonconstantCoeffs)
    (hnonconstant : ¬ P.CoefficientConstant) :
  ‖completeSum P P.commonDenominator‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ))
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:481; TranslationalTilings.complete_exponential_sum_paper_functionNonconstant -/
namespace TranslationalTilings
axiom complete_exponential_sum_paper_functionNonconstant
    (d : ℕ) (hd : 0 < d) (P : CirclePolynomial d)
    (hrat : P.HasTorsionNonconstantCoeffs)
    (hnonconstant : ¬ P.FunctionConstant) :
  ‖completeSum P P.commonDenominator‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ))
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:490; TranslationalTilings.complete_exponential_sum_paper_bigO -/
namespace TranslationalTilings
axiom complete_exponential_sum_paper_bigO (d : ℕ) (hd : 0 < d) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ P : CirclePolynomial d,
    P.HasTorsionNonconstantCoeffs → ¬ P.FunctionConstant →
    ‖completeSum P P.commonDenominator‖ ≤
      C * Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ))
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:580; TranslationalTilings.rigidityPeriodBound -/
namespace TranslationalTilings
def rigidityPeriodBound (d : ℕ) (eps : ℚ) : ℕ :=
  if d = 0 then 1 else
    max 1 (separatorDegree eps *
      (stechkinNatConstant d * separatorL1NatBound eps) ^ d)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:585; TranslationalTilings.halfCirclePeriodBound -/
namespace TranslationalTilings
def halfCirclePeriodBound (d : ℕ) : ℕ :=
  rigidityPeriodBound d (1 / 8)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:588; TranslationalTilings.universalRigidityPeriod -/
namespace TranslationalTilings
def universalRigidityPeriod (d : ℕ) : ℕ :=
  (Finset.Icc 1 (halfCirclePeriodBound d)).lcm id
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:595; TranslationalTilings.rigidityPeriodBound_pos -/
namespace TranslationalTilings
axiom rigidityPeriodBound_pos (d : ℕ) (eps : ℚ) :
  0 < rigidityPeriodBound d eps
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:599; TranslationalTilings.periodic_of_avoidsBall -/
namespace TranslationalTilings
axiom periodic_of_avoidsBall
    (P : CirclePolynomial d) (c : Torus) (eps : ℚ)
    (heps : 0 < eps) (hsmall : eps < 1 / 2)
    (havoid : P.AvoidsBall c eps) :
  ∃ Q, 0 < Q ∧ Q ≤ rigidityPeriodBound d eps ∧ P.PeriodicWith Q
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:605; TranslationalTilings.halfCircle_avoidsBall -/
namespace TranslationalTilings
axiom halfCircle_avoidsBall
    (P : CirclePolynomial d) (hhalf : P.HasHalfCircleLifts) :
  P.AvoidsBall (((3 / 4 : ℝ) : Torus)) (1 / 8 : ℝ)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:609; TranslationalTilings.periodic_of_halfCircle -/
namespace TranslationalTilings
axiom periodic_of_halfCircle
    (P : CirclePolynomial d) (hhalf : P.HasHalfCircleLifts) :
  ∃ Q, 0 < Q ∧ Q ≤ halfCirclePeriodBound d ∧ P.PeriodicWith Q
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:613; TranslationalTilings.period_dvd_universalRigidityPeriod -/
namespace TranslationalTilings
axiom period_dvd_universalRigidityPeriod
    (q : ℕ) (hq : 0 < q) (hbound : q ≤ halfCirclePeriodBound d) :
  q ∣ universalRigidityPeriod d
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:617; TranslationalTilings.periodic_universalRigidityPeriod -/
namespace TranslationalTilings
axiom periodic_universalRigidityPeriod
    (P : CirclePolynomial d) (q : ℕ)
    (hperiod : P.PeriodicWith q) (hq : 0 < q)
    (hbound : q ≤ halfCirclePeriodBound d) :
  P.PeriodicWith (universalRigidityPeriod d)
end TranslationalTilings
