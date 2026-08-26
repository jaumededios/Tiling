import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.Analysis.Equidistribution

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 0d459c591e615783c5e7e85e4c6de57640cab5775308ef93d36e12d5be1090e9  blueprint/05-polynomial-rigidity.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05-polynomial-rigidity.md:524; TranslationalTilings.separatorOrder -/
namespace TranslationalTilings
def separatorOrder (eps : ℚ) : ℕ :=
  max 1 (Int.toNat ⌈(1 : ℚ) / (2 * eps ^ 2)⌉)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:527; TranslationalTilings.separatorDegree -/
namespace TranslationalTilings
def separatorDegree (eps : ℚ) : ℕ := separatorOrder eps - 1
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:529; TranslationalTilings.separatorL1NatBound -/
namespace TranslationalTilings
def separatorL1NatBound (eps : ℚ) : ℕ :=
  max 1 (2 * separatorDegree eps)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:532; TranslationalTilings.fejerWeight -/
namespace TranslationalTilings
def fejerWeight (N : ℕ) (k : ℤ) : ℚ :=
  if Int.natAbs k < N then 1 - (Int.natAbs k : ℚ) / N else 0
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:535; TranslationalTilings.fejerSeparatorCoeff -/
namespace TranslationalTilings
noncomputable def fejerSeparatorCoeff
    (c : Torus) (eps : ℚ) (k : ℤ) : ℂ :=
  if k = 0 then 0 else
    -2 * (fejerWeight (separatorOrder eps) k : ℂ) *
      circlePhase ((-k) • c)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:541; TranslationalTilings.fejerSeparatorEval -/
namespace TranslationalTilings
noncomputable def fejerSeparatorEval
    (c : Torus) (eps : ℚ) (x : Torus) : ℂ :=
  ∑ k ∈ Finset.Icc (-(separatorDegree eps : ℤ))
      (separatorDegree eps : ℤ),
    fejerSeparatorCoeff c eps k * circlePhase (k • x)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:551; TranslationalTilings.fejer_separator_spec -/
namespace TranslationalTilings
axiom fejer_separator_spec
    (c : Torus) (eps : ℚ) (heps : 0 < eps) (hsmall : eps < 1 / 2) :
  fejerSeparatorCoeff c eps 0 = 0 ∧
  (∀ k, separatorDegree eps < Int.natAbs k →
    fejerSeparatorCoeff c eps k = 0) ∧
  (∀ x, x ∉ Metric.ball c (eps : ℝ) →
    (fejerSeparatorEval c eps x).im = 0 ∧
    1 ≤ (fejerSeparatorEval c eps x).re) ∧
  (∑ k ∈ Finset.Icc (-(separatorDegree eps : ℤ))
      (separatorDegree eps : ℤ),
    ‖fejerSeparatorCoeff c eps k‖) ≤
      (separatorL1NatBound eps : ℝ)
end TranslationalTilings
