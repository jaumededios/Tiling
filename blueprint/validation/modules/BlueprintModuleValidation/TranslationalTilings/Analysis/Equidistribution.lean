import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.Analysis.CirclePolynomial

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 0d459c591e615783c5e7e85e4c6de57640cab5775308ef93d36e12d5be1090e9  blueprint/05-polynomial-rigidity.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05-polynomial-rigidity.md:160; TranslationalTilings.circlePhase_add -/
namespace TranslationalTilings
axiom circlePhase_add (x y : Torus) :
    circlePhase (x + y) = circlePhase x * circlePhase y
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:163; TranslationalTilings.norm_circlePhase -/
namespace TranslationalTilings
axiom norm_circlePhase (x : Torus) : ‖circlePhase x‖ = 1
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:165; TranslationalTilings.integral_circlePhase_zsmul -/
namespace TranslationalTilings
axiom integral_circlePhase_zsmul (k : ℤ) (hk : k ≠ 0) :
    ∫ x : Torus, circlePhase (k • x) ∂AddCircle.haarAddCircle = 0
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:168; TranslationalTilings.equidistributed_iff_characters -/
namespace TranslationalTilings
axiom equidistributed_iff_characters (u : ℕ → Torus) :
  Equidistributed u ↔ ∀ k : ℤ, k ≠ 0 → Filter.Tendsto
    (fun N ↦ cesaroAverage (fun n ↦ circlePhase (k • u n)) N)
    Filter.atTop (nhds 0)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:173; TranslationalTilings.equidistributedInt_iff_characters -/
namespace TranslationalTilings
axiom equidistributedInt_iff_characters (u : ℤ → Torus) :
  EquidistributedInt u ↔ ∀ k : ℤ, k ≠ 0 → Filter.Tendsto
    (fun N ↦ symmetricCesaroAverage
      (fun n ↦ circlePhase (k • u n)) N)
    Filter.atTop (nhds 0)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:192; TranslationalTilings.nontorsion_zsmul -/
namespace TranslationalTilings
axiom nontorsion_zsmul {a : Torus} (ha : addOrderOf a = 0)
    {k : ℤ} (hk : k ≠ 0) : addOrderOf (k • a) = 0
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:195; TranslationalTilings.irrational_linear_phase_tendsto_zero -/
namespace TranslationalTilings
axiom irrational_linear_phase_tendsto_zero
    (a : Torus) (ha : addOrderOf a = 0) (k : ℤ) (hk : k ≠ 0) :
  Filter.Tendsto
    (fun N ↦ cesaroAverage
      (fun n ↦ circlePhase (k • ((n : ℤ) • a))) N)
    Filter.atTop (nhds 0)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:202; TranslationalTilings.vanDerCorput_cesaro -/
namespace TranslationalTilings
axiom vanDerCorput_cesaro
    (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) (H : ℕ) (hH : 0 < H) :
  Filter.limsup (fun N ↦ ‖cesaroAverage u N‖ ^ 2) Filter.atTop ≤
    (2 : ℝ) / H + (2 / H) *
      ∑ h ∈ Finset.Icc 1 (H - 1),
        Filter.limsup
          (fun N ↦ ‖cesaroAverage
            (fun n ↦ star (u n) * u (n + h)) N‖)
          Filter.atTop
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:212; TranslationalTilings.cesaroAverage_of_residue_classes -/
namespace TranslationalTilings
axiom cesaroAverage_of_residue_classes
    (f : ℕ → ℂ) (H : ℕ) (hH : 0 < H) (z₀ : Fin H → ℂ)
    (hlim : ∀ a : Fin H, Filter.Tendsto
      (fun N ↦ cesaroAverage (fun t ↦ f (H * t + (a : ℕ))) N)
      Filter.atTop (nhds (z₀ a))) :
  Filter.Tendsto (fun N ↦ cesaroAverage f N) Filter.atTop
    (nhds ((H : ℂ)⁻¹ * ∑ a, z₀ a))
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:220; TranslationalTilings.polynomial_phase_tendsto_zero_of_leading_nontorsion -/
namespace TranslationalTilings
axiom polynomial_phase_tendsto_zero_of_leading_nontorsion
    (P : CirclePolynomial d)
    (r : Fin (d + 1)) (hr : 0 < (r : ℕ))
    (hirr : addOrderOf (P.coeff r) = 0)
    (habove : ∀ i : Fin (d + 1),
      (r : ℕ) < (i : ℕ) → P.coeff i = 0)
    (k : ℤ) (hk : k ≠ 0) :
  Filter.Tendsto
    (fun N ↦ cesaroAverage
      (fun n ↦ circlePhase (k • P (n : ℤ))) N)
    Filter.atTop (nhds 0)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:232; TranslationalTilings.polynomial_phase_tendsto_zero_of_nontorsion_coeff -/
namespace TranslationalTilings
axiom polynomial_phase_tendsto_zero_of_nontorsion_coeff
    (P : CirclePolynomial d)
    (hcoeff : ∃ i : Fin (d + 1),
      0 < (i : ℕ) ∧ addOrderOf (P.coeff i) = 0)
    (k : ℤ) (hk : k ≠ 0) :
  Filter.Tendsto
    (fun N ↦ cesaroAverage
      (fun n ↦ circlePhase (k • P (n : ℤ))) N)
    Filter.atTop (nhds 0)
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:242; TranslationalTilings.polynomial_equidistributed_of_nontorsion_coeff -/
namespace TranslationalTilings
axiom polynomial_equidistributed_of_nontorsion_coeff
    (P : CirclePolynomial d)
    (hcoeff : ∃ i : Fin (d + 1),
      0 < (i : ℕ) ∧ addOrderOf (P.coeff i) = 0) :
  Equidistributed (fun n : ℕ ↦ P (n : ℤ))
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:269; TranslationalTilings.ballBump -/
namespace TranslationalTilings
noncomputable def ballBump (c : Torus) (eps : ℝ) : C(Torus, ℝ) :=
  ⟨fun x ↦ max 0 (eps - dist x c),
    continuous_const.max
      (continuous_const.sub (continuous_id.dist continuous_const))⟩
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:274; TranslationalTilings.integral_ballBump_pos -/
namespace TranslationalTilings
axiom integral_ballBump_pos
    {eps : ℝ} {c : Torus} (heps : 0 < eps) :
  0 < ∫ x, ballBump c eps x ∂AddCircle.haarAddCircle
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:278; TranslationalTilings.not_equidistributed_of_avoidsBall -/
namespace TranslationalTilings
axiom not_equidistributed_of_avoidsBall
    {eps : ℝ} {c : Torus}
    (u : ℕ → Torus) (heps : 0 < eps)
    (havoid : ∀ n, u n ∉ Metric.ball c eps) :
  ¬ Equidistributed u
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:284; TranslationalTilings.rational_nonconstant_coefficients_of_avoidsBall -/
namespace TranslationalTilings
axiom rational_nonconstant_coefficients_of_avoidsBall
    {d : ℕ} {eps : ℝ} {c : Torus}
    (P : CirclePolynomial d) (heps : 0 < eps)
    (havoid : P.AvoidsBall c eps) :
  P.HasRationalNonconstantCoeffs
end TranslationalTilings

/- blueprint/05-polynomial-rigidity.md:290; TranslationalTilings.torsion_nonconstant_coefficients_of_avoidsBall -/
namespace TranslationalTilings
axiom torsion_nonconstant_coefficients_of_avoidsBall
    {d : ℕ} {eps : ℝ} {c : Torus}
    (P : CirclePolynomial d) (heps : 0 < eps)
    (havoid : P.AvoidsBall c eps) :
  P.HasTorsionNonconstantCoeffs
end TranslationalTilings
