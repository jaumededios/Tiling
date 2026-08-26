# Polynomial sequences on the circle

Paper coverage: Lemma 4.2, Lemma 4.3, and the polynomial input used in
Proposition 4.1(ii).  The recursively closed number-theory prerequisites are
separated into Chapters 05a--05b.  This analytic consumer is split into the
following Lean modules:

```text
TranslationalTilings/Analysis/CirclePolynomial.lean
TranslationalTilings/Analysis/Equidistribution.lean
TranslationalTilings/Analysis/FejerSeparator.lean
TranslationalTilings/Analysis/PolynomialRigidity.lean
```

The complete-sum proof is owned below this chapter, not duplicated here.
Chapter 05a proves the fixed-character prime-field polynomial estimate and
exports `polynomial_addChar_sum_prime`.  Chapter 05b formalizes the exact
Arkhipov--Chubarikov--Karatsuba/Chen stationary residue-class recursion,
low degrees, CRT, degree padding, and the global effective constant, exporting
`integral_complete_exponential_sum_effective`.  This chapter imports that
terminal API, normalizes a circle polynomial to its primitive integral phase,
and develops equidistribution, the Fejer separator, and rigidity.  The old
hybrid closest-root/splitting-field outline and every polynomial-dependent
`delta` have been removed completely.

## Imports and exact Mathlib reuse

```lean
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.FiniteDifference
import TranslationalTilings.NumberTheory.CompleteExponentialSum
```

The pinned Mathlib checkout supplies `fourier`,
`AddCircle.haarAddCircle`, `AddCircle.addOrderOf_coe_rat`,
`AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder`, `Finset.lcm`,
`Polynomial.eval`, `ZMod`, additive characters, Gauss sums, finite fields,
finite sums, Haar integration, and Stone--Weierstrass.
Chapter 1
supplies the unique project definitions `backwardDiff` and
`backwardDiffIter`.  Mathlib does **not** supply the polynomial
additive-character estimate, the Chen complete-sum theorem, polynomial
equidistribution, or the rigidity lemma.  Chapters 05a--05b close the first
two gaps recursively; the modules listed above close the latter two.

## 1. Circle polynomials and all data definitions

A coefficient vector has length `d+1`; it represents a polynomial of degree at
most `d`.  Only positive-index coefficients enter rationality and the common
denominator.  This is essential: avoidance of an arc says nothing about the
constant coefficient.

```lean
namespace TranslationalTilings

structure CirclePolynomial (d : ℕ) where
  coeff : Fin (d + 1) → Torus

def CirclePolynomial.eval (P : CirclePolynomial d) (n : ℤ) : Torus :=
  ∑ i : Fin (d + 1), (n ^ (i : ℕ)) • P.coeff i

instance : CoeFun (CirclePolynomial d) (fun _ ↦ ℤ → Torus) :=
  ⟨CirclePolynomial.eval⟩

def CirclePolynomial.CoefficientConstant (P : CirclePolynomial d) : Prop :=
  ∀ i : Fin (d + 1), 0 < (i : ℕ) → P.coeff i = 0

def CirclePolynomial.FunctionConstant (P : CirclePolynomial d) : Prop :=
  ∃ c : Torus, ∀ n : ℤ, P n = c

def CirclePolynomial.HasTorsionNonconstantCoeffs
    (P : CirclePolynomial d) : Prop :=
  ∀ i : Fin (d + 1), 0 < (i : ℕ) → IsOfFinAddOrder (P.coeff i)

def CirclePolynomial.HasRationalNonconstantCoeffs
    (P : CirclePolynomial d) : Prop :=
  ∀ i : Fin (d + 1), 0 < (i : ℕ) →
    ∃ q : ℚ, P.coeff i = ((q : ℝ) : Torus)

def CirclePolynomial.nonconstantIndices (d : ℕ) : Finset (Fin (d + 1)) :=
  Finset.univ.filter fun i ↦ 0 < (i : ℕ)

noncomputable def CirclePolynomial.commonDenominator
    (P : CirclePolynomial d) : ℕ :=
  (CirclePolynomial.nonconstantIndices d).lcm
    fun i ↦ addOrderOf (P.coeff i)

def CirclePolynomial.AvoidsBall (P : CirclePolynomial d)
    (c : Torus) (eps : ℝ) : Prop :=
  ∀ n : ℤ, P n ∉ Metric.ball c eps

def CirclePolynomial.HasHalfCircleLifts (P : CirclePolynomial d) : Prop :=
  ∀ n : ℤ, ∃ t : ℝ,
    t ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) ∧ P n = (t : Torus)

def CirclePolynomial.PeriodicWith (P : CirclePolynomial d) (Q : ℕ) : Prop :=
  Function.Periodic P (Q : ℤ)

def CirclePolynomial.zsmul (k : ℤ)
    (P : CirclePolynomial d) : CirclePolynomial d :=
  ⟨fun i ↦ k • P.coeff i⟩

noncomputable def cesaroAverage (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f n

noncomputable def symmetricCesaroAverage (f : ℤ → ℂ) (N : ℕ) : ℂ :=
  ((2 * N + 1 : ℕ) : ℂ)⁻¹ *
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f n

def Equidistributed (u : ℕ → Torus) : Prop :=
  ∀ f : C(Torus, ℂ), Filter.Tendsto
    (fun N : ℕ ↦ (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (u n))
    Filter.atTop (nhds (∫ x, f x ∂AddCircle.haarAddCircle))

def EquidistributedInt (u : ℤ → Torus) : Prop :=
  ∀ f : C(Torus, ℂ), Filter.Tendsto
    (fun N : ℕ ↦ symmetricCesaroAverage (fun n ↦ f (u n)) N)
    Filter.atTop (nhds (∫ x, f x ∂AddCircle.haarAddCircle))

noncomputable def completeSum (P : CirclePolynomial d) (Q : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 Q, circlePhase (P n)
```

The coefficient-facing complete-sum theorem uses `CoefficientConstant`.
`FunctionConstant` is kept distinct because a nonzero coefficient vector may
induce a constant function at a small modulus, for example
`(n^2+n)/2` modulo one.  The paper phrases Lemma 4.2 for a nonconstant map; the
following exported bridge gives the literal paper-facing corollary.  The
coefficient-facing theorem is stronger, and remains true in the
function-constant/nonzero-coefficient case because primitivity forces the
offending modulus to be bounded in terms of the degree.

```lean
theorem CirclePolynomial.functionConstant_of_coefficientConstant
    (P : CirclePolynomial d) (hP : P.CoefficientConstant) :
  P.FunctionConstant

theorem CirclePolynomial.not_coefficientConstant_of_not_functionConstant
    (P : CirclePolynomial d) (hP : ¬ P.FunctionConstant) :
  ¬ P.CoefficientConstant
```

The imported finite-cyclic-phase module from Chapter 05b owns `Torus`,
`circlePhase`, `IntegralPolynomialPhase`, `integralCompleteSum`, the Chen
local factors, and `stechkinNatConstant`.  Their definitions and all
cross-representation characteristic lemmas are stated once in that chapter.
This file constructs an integral phase only after its circle-specific
denominator data have been proved.

## 2. Fourier characters and equidistribution

The public character API is:

```lean
theorem circlePhase_add (x y : Torus) :
    circlePhase (x + y) = circlePhase x * circlePhase y

theorem norm_circlePhase (x : Torus) : ‖circlePhase x‖ = 1

theorem integral_circlePhase_zsmul (k : ℤ) (hk : k ≠ 0) :
    ∫ x : Torus, circlePhase (k • x) ∂AddCircle.haarAddCircle = 0

theorem equidistributed_iff_characters (u : ℕ → Torus) :
  Equidistributed u ↔ ∀ k : ℤ, k ≠ 0 → Filter.Tendsto
    (fun N ↦ cesaroAverage (fun n ↦ circlePhase (k • u n)) N)
    Filter.atTop (nhds 0)

theorem equidistributedInt_iff_characters (u : ℤ → Torus) :
  EquidistributedInt u ↔ ∀ k : ℤ, k ≠ 0 → Filter.Tendsto
    (fun N ↦ symmetricCesaroAverage
      (fun n ↦ circlePhase (k • u n)) N)
    Filter.atTop (nhds 0)
```

For the forward implications specialize the continuous test to a character
and use character orthogonality.  Conversely, finite complex linear
combinations of characters are a conjugation-closed subalgebra containing the
constants and separating points.  Complex Stone--Weierstrass gives uniform
approximation.  A probability measure changes an integral by at most the
uniform error, and every finite Cesaro average changes by at most the same
error; a three-epsilon argument closes the proof.  This is precisely where
Mathlib's compact AddCircle, Haar, and Fourier APIs are reused.

The polynomial Weyl chain exports:

```lean
theorem nontorsion_zsmul {a : Torus} (ha : addOrderOf a = 0)
    {k : ℤ} (hk : k ≠ 0) : addOrderOf (k • a) = 0

theorem irrational_linear_phase_tendsto_zero
    (a : Torus) (ha : addOrderOf a = 0) (k : ℤ) (hk : k ≠ 0) :
  Filter.Tendsto
    (fun N ↦ cesaroAverage
      (fun n ↦ circlePhase (k • ((n : ℤ) • a))) N)
    Filter.atTop (nhds 0)

theorem vanDerCorput_cesaro
    (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1) (H : ℕ) (hH : 0 < H) :
  Filter.limsup (fun N ↦ ‖cesaroAverage u N‖ ^ 2) Filter.atTop ≤
    (2 : ℝ) / H + (2 / H) *
      ∑ h ∈ Finset.Icc 1 (H - 1),
        Filter.limsup
          (fun N ↦ ‖cesaroAverage
            (fun n ↦ star (u n) * u (n + h)) N‖)
          Filter.atTop

theorem cesaroAverage_of_residue_classes
    (f : ℕ → ℂ) (H : ℕ) (hH : 0 < H) (z₀ : Fin H → ℂ)
    (hlim : ∀ a : Fin H, Filter.Tendsto
      (fun N ↦ cesaroAverage (fun t ↦ f (H * t + (a : ℕ))) N)
      Filter.atTop (nhds (z₀ a))) :
  Filter.Tendsto (fun N ↦ cesaroAverage f N) Filter.atTop
    (nhds ((H : ℂ)⁻¹ * ∑ a, z₀ a))

theorem polynomial_phase_tendsto_zero_of_leading_nontorsion
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

theorem polynomial_phase_tendsto_zero_of_nontorsion_coeff
    (P : CirclePolynomial d)
    (hcoeff : ∃ i : Fin (d + 1),
      0 < (i : ℕ) ∧ addOrderOf (P.coeff i) = 0)
    (k : ℤ) (hk : k ≠ 0) :
  Filter.Tendsto
    (fun N ↦ cesaroAverage
      (fun n ↦ circlePhase (k • P (n : ℤ))) N)
    Filter.atTop (nhds 0)

theorem polynomial_equidistributed_of_nontorsion_coeff
    (P : CirclePolynomial d)
    (hcoeff : ∃ i : Fin (d + 1),
      0 < (i : ℕ) ∧ addOrderOf (P.coeff i) = 0) :
  Equidistributed (fun n : ℕ ↦ P (n : ℤ))
```

For the leading-coefficient theorem, induction on `r` uses van der Corput.
For a fixed nonzero shift `h`, the correlation phase is the forward difference
`P(n+h)-P(n)`; its leading coefficient is `h*r*P.coeff r`, still nontorsion,
and its degree is `r-1`.  The base case is the geometric-series formula for a
nontorsion linear phase.

The general theorem cannot simply choose the largest nontorsion coefficient,
because higher torsion coefficients survive ordinary differencing.  Instead,
after applying the character `k`, let `r` be the largest nontorsion index and
let `H` be the lcm of the orders of all coefficients above `r`.  Split `n` into
the finitely many classes `H*t+a`.  On each class every positive-degree term
coming from an index above `r` vanishes; the coefficient of `t^r` is
`H^r*k*P.coeff r`, which is nontorsion.  Apply the leading theorem on every
class and recombine with `cesaroAverage_of_residue_classes`.

Avoidance contradicts equidistribution through an explicit continuous bump,
not by an unstated claim that an equidistributed sequence visits every open
set:

```lean
noncomputable def ballBump (c : Torus) (eps : ℝ) : C(Torus, ℝ) :=
  ⟨fun x ↦ max 0 (eps - dist x c),
    continuous_const.max
      (continuous_const.sub (continuous_id.dist continuous_const))⟩

theorem integral_ballBump_pos
    {eps : ℝ} {c : Torus} (heps : 0 < eps) :
  0 < ∫ x, ballBump c eps x ∂AddCircle.haarAddCircle

theorem not_equidistributed_of_avoidsBall
    {eps : ℝ} {c : Torus}
    (u : ℕ → Torus) (heps : 0 < eps)
    (havoid : ∀ n, u n ∉ Metric.ball c eps) :
  ¬ Equidistributed u

theorem rational_nonconstant_coefficients_of_avoidsBall
    {d : ℕ} {eps : ℝ} {c : Torus}
    (P : CirclePolynomial d) (heps : 0 < eps)
    (havoid : P.AvoidsBall c eps) :
  P.HasRationalNonconstantCoeffs

theorem torsion_nonconstant_coefficients_of_avoidsBall
    {d : ℕ} {eps : ℝ} {c : Torus}
    (P : CirclePolynomial d) (heps : 0 < eps)
    (havoid : P.AvoidsBall c eps) :
  P.HasTorsionNonconstantCoeffs
```

The bump vanishes outside the ball.  Haar measure has full support on the
compact group, so its integral is positive.  Under avoidance all sampled bump
values are zero, contradicting its positive limiting integral.  If a positive
coefficient were nontorsion, polynomial Weyl equidistribution would give that
contradiction.  Rational/torsion equivalence is then exactly the pinned
`AddCircle` API; the constant coefficient is never mentioned.

## 3. Finite differences really produce circle polynomials

Chapter 6 needs this public bridge rather than a prose assertion.  Adapt the
project's backward difference to Mathlib's forward difference as in Chapter 1.

```lean
def intFallingFactorial (n : ℤ) (k : ℕ) : ℤ :=
  ∏ j ∈ Finset.range k, (n - j)

theorem circle_newton_expansion
    (f : ℤ → Torus) (h : backwardDiffIter 1 (d + 1) f = 0) :
  ∃ a : Fin (d + 1) → Torus, ∀ n : ℤ,
    f n = ∑ i : Fin (d + 1),
      intFallingFactorial n (i : ℕ) • a i

theorem fallingFactorial_to_monomial_circle
    (a : Fin (d + 1) → Torus) :
  ∃ b : Fin (d + 1) → Torus, ∀ n : ℤ,
    (∑ i : Fin (d + 1), intFallingFactorial n (i : ℕ) • a i) =
      ∑ i : Fin (d + 1), n ^ (i : ℕ) • b i

theorem exists_circlePolynomial_of_difference
    (f : ℤ → Torus) (h : backwardDiffIter 1 (d + 1) f = 0) :
  ∃ P : CirclePolynomial d, ∀ n : ℤ, P n = f n
```

Here `backwardDiff` and `backwardDiffIter` are imported from
`TranslationalTilings.FiniteDifference`; Chapter 1 is their sole owner.

The Newton expansion is induction on `d`: the `d`th difference is constant,
subtract its falling-factorial antiderivative, and apply the induction
hypothesis.  The conversion uses signed Stirling-number identities.  Division
by `i!` is legitimate because `Torus` is divisible; choices are made only in
the proof and no algorithm depends on the chosen coefficients.  Polynomial
identities are first proved in `Polynomial ℤ`, then transported through the
additive action on `Torus`.

## 4. Common denominators and exact period transport

```lean
theorem rational_iff_torsion_nonconstant (P : CirclePolynomial d) :
  P.HasRationalNonconstantCoeffs ↔ P.HasTorsionNonconstantCoeffs

theorem commonDenominator_pos
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  0 < P.commonDenominator

theorem commonDenominator_eq_zero_of_coeff_addOrderOf_eq_zero
    (P : CirclePolynomial d) {i : Fin (d + 1)}
    (hi : 0 < (i : ℕ)) (horder : addOrderOf (P.coeff i) = 0) :
  P.commonDenominator = 0

theorem coeff_zsmul_commonDenominator
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs)
    (i : Fin (d + 1)) (hi : 0 < (i : ℕ)) :
  (P.commonDenominator : ℤ) • P.coeff i = 0

theorem periodic_commonDenominator
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  P.PeriodicWith P.commonDenominator

theorem commonDenominator_zsmul_dvd
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs)
    (k : ℤ) :
  (P.zsmul k).commonDenominator ∣ P.commonDenominator

theorem commonDenominator_dvd_natAbs_mul_zsmul
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs)
    (k : ℤ) :
  P.commonDenominator ∣
    Int.natAbs k * (P.zsmul k).commonDenominator

theorem normalized_completeSum_repeat
    (P : CirclePolynomial d) (Q Q' : ℕ)
    (hQ : 0 < Q) (hQ' : 0 < Q') (hdiv : Q' ∣ Q)
    (hperiod : P.PeriodicWith Q') :
  (Q : ℂ)⁻¹ * completeSum P Q =
    (Q' : ℂ)⁻¹ * completeSum P Q'

theorem normalized_completeSum_repeat_zero_regression :
  let P : CirclePolynomial 0 := ⟨fun _ ↦ 0⟩
  (0 : ℂ)⁻¹ * completeSum P 0 ≠
    (1 : ℂ)⁻¹ * completeSum P 1
```

Under the torsion hypothesis every lcm entry is positive; the lcm of the empty
family is one, so positivity includes `d=0`.  Without torsion an entry may have
`addOrderOf=0`, so the hypothesis on `commonDenominator_pos` is essential.  The
period proof expands `(n+Q)^i-n^i`; every term for `i>0` contains a factor `Q`,
which annihilates that coefficient.  For multiplication by `k`,
`ord(k*a) | ord(a)` and `ord(a) | |k|*ord(k*a)` coefficientwise; lcm
monotonicity gives both displayed divisibilities.  Repeated averaging requires
both periods to be positive, partitions `1..Q` into `Q/Q'` blocks, and uses
periodicity.  These lemmas close the exact
gap between the separator's sum over `Q` and the sharp estimate at
`commonDenominator (kP)`.
The two regression theorems record both failure modes of the omitted
hypotheses: a positive-index coefficient of infinite additive order forces
the lcm to be zero, and normalized repetition from `Q=0` to `Q'=1` already
fails for the zero degree-zero polynomial.

Normalization is an exported construction with a specification:

```lean
theorem exists_integralPhase
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  ∃ A : IntegralPolynomialPhase d,
    A.modulus = P.commonDenominator ∧ A.Primitive ∧
    ∀ n : ℤ, P n = P.coeff 0 +
      (((A.evalNumerator n : ℝ) / A.modulus : ℝ) : Torus)

noncomputable def CirclePolynomial.integralPhase
    (P : CirclePolynomial d)
    (hP : P.HasTorsionNonconstantCoeffs) : IntegralPolynomialPhase d :=
  Classical.choose (exists_integralPhase P hP)

theorem integralPhase_modulus
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  (P.integralPhase hP).modulus = P.commonDenominator

theorem integralPhase_primitive
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  (P.integralPhase hP).Primitive

theorem integralPhase_eval
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) (n : ℤ) :
  P n = P.coeff 0 +
    ((((P.integralPhase hP).evalNumerator n : ℝ) /
      (P.integralPhase hP).modulus : ℝ) : Torus)

theorem norm_completeSum_eq_integralPhase
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  ‖completeSum P P.commonDenominator‖ =
    ‖integralCompleteSum (P.integralPhase hP)‖
```

For each positive coefficient, `Q • a_i = 0` gives a representative
`A_i/Q` by `AddCircle.nsmul_eq_zero_iff`.  If a prime divided `Q` and every
`A_i`, then every coefficient order would divide `Q/p`, contradicting the
minimality of the lcm; hence the integral phase is primitive.  The constant
coefficient factors out of the complete sum as a unit and disappears after
taking the norm.

## 5. Transfer of the complete-sum theorem to circle polynomials

Chapter 05b is the sole owner of the complete rational-sum development.  Its
terminal theorem `integral_complete_exponential_sum_effective` has the
following inputs: a positive advertised degree `d`, an
`IntegralPolynomialPhase d`, and its `Primitive` proof.  Its conclusion is

`norm (integralCompleteSum A) <= stechkinNatConstant d *
  A.modulus^(1-1/d)`.

That theorem is not redeclared here.  Its exact proof dependency is the
Chapter 05b chain

`integral phase -> Polynomial Z -> ZMod character sum -> prime Weil bound
 -> Chen prime powers -> CRT -> low degrees -> degree padding`.

All coefficient, content, enumeration, sign-convention, and primitive-scaling
bridges belong to that chain and are therefore neither hidden nor duplicated
in this consumer.

The circle-polynomial transfer exports:

```lean
/-- Coefficient-facing strengthening of Greenfeld--Tao, Lemma 4.2. -/
theorem complete_exponential_sum_paper
    (d : ℕ) (hd : 0 < d) (P : CirclePolynomial d)
    (hrat : P.HasTorsionNonconstantCoeffs)
    (hnonconstant : ¬ P.CoefficientConstant) :
  ‖completeSum P P.commonDenominator‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ))

/-- Greenfeld--Tao, Lemma 4.2, literally for a nonconstant map. -/
theorem complete_exponential_sum_paper_functionNonconstant
    (d : ℕ) (hd : 0 < d) (P : CirclePolynomial d)
    (hrat : P.HasTorsionNonconstantCoeffs)
    (hnonconstant : ¬ P.FunctionConstant) :
  ‖completeSum P P.commonDenominator‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ))

theorem complete_exponential_sum_paper_bigO (d : ℕ) (hd : 0 < d) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ P : CirclePolynomial d,
    P.HasTorsionNonconstantCoeffs → ¬ P.FunctionConstant →
    ‖completeSum P P.commonDenominator‖ ≤
      C * Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ))
```

For the coefficient-facing theorem, construct `P.integralPhase hrat`.
`integralPhase_primitive` supplies exactly the hypothesis of the imported
terminal theorem, and `norm_completeSum_eq_integralPhase` identifies the two
norms.  The paper-facing theorem uses
`not_coefficientConstant_of_not_functionConstant`; the uniform form chooses
`C=stechkinNatConstant d` before `P`.  Thus the constant is genuinely
degree-only and the exponent remains exactly `1-1/d`.

Dependency sensitivity is recorded separately from theorem identity.  Any
uniform degree-only power saving `Q^(1-delta_d)` with `delta_d>0` would
still make the Fejer argument return a degree/interval-only denominator bound;
it would change only hidden functions of `|F|` downstream, not any printed
diameter or `ell` exponent.  Such a weaker input would suffice for the tiling
consequences, but it would not formalize the paper's labelled Lemma 4.2 and is
not exported under that name.

## 6. An explicit Fejer separator

For `0 < eps < 1/2`, set

`N = max 1 ceil(1/(2 eps^2))`

and use the Fejer kernel centered at `c`.  Removing the zero Fourier
coefficient from `2*(1-F_N)` gives a mean-zero real trigonometric polynomial.

```lean
def separatorOrder (eps : ℚ) : ℕ :=
  max 1 (Int.toNat ⌈(1 : ℚ) / (2 * eps ^ 2)⌉)

def separatorDegree (eps : ℚ) : ℕ := separatorOrder eps - 1

def separatorL1NatBound (eps : ℚ) : ℕ :=
  max 1 (2 * separatorDegree eps)

def fejerWeight (N : ℕ) (k : ℤ) : ℚ :=
  if Int.natAbs k < N then 1 - (Int.natAbs k : ℚ) / N else 0

noncomputable def fejerSeparatorCoeff
    (c : Torus) (eps : ℚ) (k : ℤ) : ℂ :=
  if k = 0 then 0 else
    -2 * (fejerWeight (separatorOrder eps) k : ℂ) *
      circlePhase ((-k) • c)

noncomputable def fejerSeparatorEval
    (c : Torus) (eps : ℚ) (x : Torus) : ℂ :=
  ∑ k ∈ Finset.Icc (-(separatorDegree eps : ℤ))
      (separatorDegree eps : ℤ),
    fejerSeparatorCoeff c eps k * circlePhase (k • x)
```

The exported specification is:

```lean
theorem fejer_separator_spec
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
```

The identity

`F_N(t)=N⁻¹*(sin(pi*N*t)/sin(pi*t))^2`

is proved by multiplying the finite geometric series by its conjugate.  If
`dist(x,c)≥eps`, then `|sin(pi*t)|≥2*dist(t,Z)≥2eps`, while the numerator has
absolute value at most one.  Hence
`F_N(x-c)≤1/(4*N*eps^2)≤1/2`, and
`2*(1-F_N)≥1`.  The coefficients occur in conjugate pairs, so the evaluation
is real.  Their absolute sum is at most `2*(N-1)`.  This direct construction
avoids an ineffective appeal to Weierstrass approximation.

## 7. Explicit rigidity and the half-circle bridge

```lean
def rigidityPeriodBound (d : ℕ) (eps : ℚ) : ℕ :=
  if d = 0 then 1 else
    max 1 (separatorDegree eps *
      (stechkinNatConstant d * separatorL1NatBound eps) ^ d)

def halfCirclePeriodBound (d : ℕ) : ℕ :=
  rigidityPeriodBound d (1 / 8)

def universalRigidityPeriod (d : ℕ) : ℕ :=
  (Finset.Icc 1 (halfCirclePeriodBound d)).lcm id
```

The rigidity theorem and all downstream bridges are:

```lean
theorem rigidityPeriodBound_pos (d : ℕ) (eps : ℚ) :
  0 < rigidityPeriodBound d eps

/-- Greenfeld--Tao, Lemma 4.3, for a metric ball. -/
theorem periodic_of_avoidsBall
    (P : CirclePolynomial d) (c : Torus) (eps : ℚ)
    (heps : 0 < eps) (hsmall : eps < 1 / 2)
    (havoid : P.AvoidsBall c eps) :
  ∃ Q, 0 < Q ∧ Q ≤ rigidityPeriodBound d eps ∧ P.PeriodicWith Q

theorem halfCircle_avoidsBall
    (P : CirclePolynomial d) (hhalf : P.HasHalfCircleLifts) :
  P.AvoidsBall (((3 / 4 : ℝ) : Torus)) (1 / 8 : ℝ)

theorem periodic_of_halfCircle
    (P : CirclePolynomial d) (hhalf : P.HasHalfCircleLifts) :
  ∃ Q, 0 < Q ∧ Q ≤ halfCirclePeriodBound d ∧ P.PeriodicWith Q

theorem period_dvd_universalRigidityPeriod
    (q : ℕ) (hq : 0 < q) (hbound : q ≤ halfCirclePeriodBound d) :
  q ∣ universalRigidityPeriod d

theorem periodic_universalRigidityPeriod
    (P : CirclePolynomial d) (q : ℕ)
    (hperiod : P.PeriodicWith q) (hq : 0 < q)
    (hbound : q ≤ halfCirclePeriodBound d) :
  P.PeriodicWith (universalRigidityPeriod d)
```

If `d=0`, period one is immediate.  Otherwise, avoidance first makes all
positive coefficients torsion; let `Q` be their lcm.  Average the Fejer
separator over this exact period.  Every term has real part at least one, but
the zero Fourier coefficient vanishes.  The triangle inequality and the
coefficient `l1` bound produce a nonzero `k` with

`1 / separatorL1NatBound eps ≤ |Q⁻¹ S(kP;Q)|`

and `|k|≤separatorDegree eps`.  Put `Qk=commonDenominator(kP)`.
`Qk | Q`, repeated averaging changes the left side to the normalized sum over
`Qk`, and the complete-sum estimate gives

`1/L ≤ C * Qk^(-1/d)`.

Raising the nonnegative inequality to the `d`th power yields
`Qk≤(C*L)^d`.  The reverse denominator divisibility gives
`Q≤|k|*Qk`, exactly the formula in `rigidityPeriodBound`.  If `kP` is
coefficient-constant, that same divisibility gives `Q≤|k|` and is an even
smaller branch; no false invocation of Lemma 4.2 occurs.

For the half-circle result, real lifts in `[0,1/2]` have circle distance at
least `1/4` from `3/4`, hence avoid the radius-`1/8` ball.  This formulation is
well typed: no order interval is placed on `AddCircle`.  Finally, the lcm over
`1..B` is positive because `B>0`, contains every positive bounded period, and
a multiple of a period is again a period.

## 8. Edge cases, regressions, and trust checks

- Degree zero: `commonDenominator=1`; every sequence has period one; no
  complete-sum theorem with `d` in a denominator is invoked.
- Irrational constant coefficient: allowed.  A constant polynomial can avoid
  a ball while its constant coefficient is irrational.
- Padded degree: the sum bound selects the actual degree and weakens its power
  to the declared upper degree.
- Small-modulus fixed divisors: coefficient-constant and function-constant are
  not conflated; the bounded-degeneracy branch is included in the
  prime-power proof.
- Character multiplication: both denominator divisibilities and normalized
  repeated averaging are tested for `k=0`, `k=±1`, and a collapsing order.
- Half circle: all order comparisons occur in the real lift, never in
  `AddCircle`.

Before this chapter is accepted, the implementation must satisfy:

```text
lake build
lake env lean TranslationalTilings/Analysis/PolynomialRigidity.lean
rg -n 'sorry|admit|axiom|opaque' TranslationalTilings
#print axioms TranslationalTilings.complete_exponential_sum_paper
#print axioms TranslationalTilings.periodic_of_avoidsBall
#print axioms TranslationalTilings.periodic_of_halfCircle
```

The axiom reports may contain only Lean's standard quotient/propext/choice
foundations inherited from Mathlib, never a project-specific analytic or
number-theoretic assumption.

```lean
end TranslationalTilings
```
