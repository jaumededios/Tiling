import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Tactic.Order

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 23f3373f2f8c6f1bc5d7ac91e541a7cbb875f039c26b478fa70608a0d99c27d5  blueprint/05a-weil-stepanov.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05a-weil-stepanov.md:1100; TranslationalTilings.Stepanov.VanishesToOrderAtLeast -/
namespace TranslationalTilings.Stepanov
def VanishesToOrderAtLeast {K : Type*} [CommRing K]
    (P : Polynomial K) (a : K) (R : ℕ) : Prop :=
  ∀ r < R, (P.hasseDeriv r).eval a = 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1104; TranslationalTilings.Stepanov.vanishesToOrderAtLeast_iff_rootMultiplicity -/
namespace TranslationalTilings.Stepanov
axiom vanishesToOrderAtLeast_iff_rootMultiplicity
    {K : Type*} [Field K] {P : Polynomial K}
    (hP : P ≠ 0) (a : K) (R : ℕ) :
    VanishesToOrderAtLeast P a R ↔ R ≤ P.rootMultiplicity a
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1109; TranslationalTilings.Stepanov.card_mul_le_natDegree_of_vanishes -/
namespace TranslationalTilings.Stepanov
axiom card_mul_le_natDegree_of_vanishes
    {K : Type*} [Field K] {P : Polynomial K} (hP : P ≠ 0)
    (A : Finset K) {R : ℕ}
    (hvanish : ∀ a ∈ A, VanishesToOrderAtLeast P a R) :
    A.card * R ≤ P.natDegree
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1115; TranslationalTilings.Stepanov.hasseDeriv_eval_frobenius -/
namespace TranslationalTilings.Stepanov
axiom hasseDeriv_eval_frobenius
    {K : Type*} [Field K] {p : ℕ} [CharP K p]
    (Q : Polynomial (Polynomial K)) {m r : ℕ} (hr : r < p ^ m) :
    (Q.eval (Polynomial.X ^ (p ^ m))).hasseDeriv r =
      (Q.sum fun i a ↦
        Polynomial.C (a.hasseDeriv r) * Polynomial.X ^ i).eval
          (Polynomial.X ^ (p ^ m))
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1155; TranslationalTilings.Stepanov.AdditiveStepanovParameters -/
namespace TranslationalTilings.Stepanov
structure AdditiveStepanovParameters (p d n : ℕ) where
  u : ℕ
  S : ℕ
  K : ℕ
  R : ℕ
  u_eq : u = n / 2
  S_eq : S = p ^ (n - 2)
  K_eq : K = p ^ (u - 2) / (2 * d)
  K_pos : 0 < K
  two_mul_d_le_K : 2 * d ≤ K
  R_eq : R = p * K
  R_lt_frobenius : R < p ^ u
  dimension_ok :
    R * (S + d * (p - 1) * p ^ (u - 1) + K) <
      p * S * (K + 1)
  norm_degree_ok :
    p * S + d * p ^ u * (p - 1) < p ^ n
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1173; TranslationalTilings.Stepanov.exists_additive_stepanov_parameters -/
namespace TranslationalTilings.Stepanov
axiom exists_additive_stepanov_parameters
    (p d : ℕ) (hp : p.Prime) (hd : 2 ≤ d) (hdp : d < p) :
    ∃ N, ∀ n ≥ N, Nonempty (AdditiveStepanovParameters p d n)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1177; TranslationalTilings.Stepanov.AdditiveStepanovParameters.S_pos -/
namespace TranslationalTilings.Stepanov
axiom AdditiveStepanovParameters.S_pos
    {p d n : ℕ} (par : AdditiveStepanovParameters p d n) :
    0 < par.S
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1181; TranslationalTilings.Stepanov.AdditiveStepanovParameters.n_pos -/
namespace TranslationalTilings.Stepanov
axiom AdditiveStepanovParameters.n_pos
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) : 0 < n
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1218; TranslationalTilings.Stepanov.upperTracePolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def upperTracePolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (n u : ℕ) : Polynomial (ZMod p) :=
  ∑ t ∈ Finset.Ico u n, f ^ (p ^ t)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1223; TranslationalTilings.Stepanov.AdditiveAuxiliaryCoefficients -/
namespace TranslationalTilings.Stepanov
structure AdditiveAuxiliaryCoefficients {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (k : Type*) [Field k] where
  coeff : Fin p → Fin (par.K + 1) → Polynomial k
  degree_lt : ∀ i j, (coeff i j).natDegree < par.S
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1229; TranslationalTilings.Stepanov.AdditiveAuxiliaryCoefficients.Nonzero -/
namespace TranslationalTilings.Stepanov
def AdditiveAuxiliaryCoefficients.Nonzero
    {p d n : ℕ} {par : AdditiveStepanovParameters p d n}
    {k : Type*} [Field k]
    (e : AdditiveAuxiliaryCoefficients par k) : Prop :=
  ∃ i j, e.coeff i j ≠ 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1235; TranslationalTilings.Stepanov.additiveAuxiliaryPolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def additiveAuxiliaryPolynomial
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p))
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) :
    Polynomial (ZMod p) :=
  ∑ i : Fin p, ∑ j : Fin (par.K + 1),
    e.coeff i j * upperTracePolynomial f n par.u ^ i.1 *
      Polynomial.X ^ (p ^ n * j.1)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1251; TranslationalTilings.Stepanov.AdditiveCoeffVector -/
namespace TranslationalTilings.Stepanov
abbrev AdditiveCoeffVector {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :=
  Fin p → Fin (par.K + 1) → Fin par.S → ZMod p
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1255; TranslationalTilings.Stepanov.additiveConstraintDegree -/
namespace TranslationalTilings.Stepanov
def additiveConstraintDegree {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n) : ℕ :=
  par.S + d * (p - 1) * p ^ (par.u - 1) + par.K
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1259; TranslationalTilings.Stepanov.AdditiveConstraintTarget -/
namespace TranslationalTilings.Stepanov
abbrev AdditiveConstraintTarget {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :=
  Fin par.R → Fin (additiveConstraintDegree par) → ZMod p
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1263; TranslationalTilings.Stepanov.coeffPolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def coeffPolynomial
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) (i : Fin p)
    (j : Fin (par.K + 1)) : Polynomial (ZMod p) :=
  ∑ s : Fin par.S,
    Polynomial.C (v i j s) * Polynomial.X ^ s.1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1271; TranslationalTilings.Stepanov.coeffPolynomial_coeff -/
namespace TranslationalTilings.Stepanov
axiom coeffPolynomial_coeff
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) (i : Fin p)
    (j : Fin (par.K + 1)) (s : Fin par.S) :
    (coeffPolynomial v i j).coeff s.1 = v i j s
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1278; TranslationalTilings.Stepanov.coeffPolynomial_natDegree_lt -/
namespace TranslationalTilings.Stepanov
axiom coeffPolynomial_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) (i : Fin p)
    (j : Fin (par.K + 1)) :
    (coeffPolynomial v i j).natDegree < par.S
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1285; TranslationalTilings.Stepanov.coeffVectorToCoefficients -/
namespace TranslationalTilings.Stepanov
noncomputable def coeffVectorToCoefficients
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) :
    AdditiveAuxiliaryCoefficients par (ZMod p) where
  coeff := coeffPolynomial v
  degree_lt := coeffPolynomial_natDegree_lt v
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1293; TranslationalTilings.Stepanov.coeffVectorToAuxiliaryFun -/
namespace TranslationalTilings.Stepanov
noncomputable def coeffVectorToAuxiliaryFun
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (v : AdditiveCoeffVector par) :
    Polynomial (ZMod p) :=
  additiveAuxiliaryPolynomial par f (coeffVectorToCoefficients v)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1300; TranslationalTilings.Stepanov.coeffVectorToAuxiliaryFun_add -/
namespace TranslationalTilings.Stepanov
axiom coeffVectorToAuxiliaryFun_add
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (v w : AdditiveCoeffVector par) :
    coeffVectorToAuxiliaryFun par f (v + w) =
      coeffVectorToAuxiliaryFun par f v +
        coeffVectorToAuxiliaryFun par f w
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1308; TranslationalTilings.Stepanov.coeffVectorToAuxiliaryFun_smul -/
namespace TranslationalTilings.Stepanov
axiom coeffVectorToAuxiliaryFun_smul
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (c : ZMod p)
    (v : AdditiveCoeffVector par) :
    coeffVectorToAuxiliaryFun par f (c • v) =
      c • coeffVectorToAuxiliaryFun par f v
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1316; TranslationalTilings.Stepanov.coeffVectorToAuxiliary -/
namespace TranslationalTilings.Stepanov
noncomputable def coeffVectorToAuxiliary
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) :
    AdditiveCoeffVector par →ₗ[ZMod p] Polynomial (ZMod p) where
  toFun := coeffVectorToAuxiliaryFun par f
  map_add' := coeffVectorToAuxiliaryFun_add par f
  map_smul' := coeffVectorToAuxiliaryFun_smul par f
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1325; TranslationalTilings.Stepanov.lowerTracePolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def lowerTracePolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) : Polynomial (ZMod p) :=
  ∑ t ∈ Finset.range u, f ^ (p ^ t)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1330; TranslationalTilings.Stepanov.reducedHassePolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def reducedHassePolynomial
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ)
    (v : AdditiveCoeffVector par) : Polynomial (ZMod p) :=
  ∑ i : Fin p, ∑ j : Fin (par.K + 1),
    (coeffPolynomial v i j).hasseDeriv r *
      (Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1 *
        Polynomial.X ^ j.1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1340; TranslationalTilings.Stepanov.reducedHassePolynomial_add -/
namespace TranslationalTilings.Stepanov
axiom reducedHassePolynomial_add
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ)
    (v w : AdditiveCoeffVector par) :
    reducedHassePolynomial par f b r (v + w) =
      reducedHassePolynomial par f b r v +
        reducedHassePolynomial par f b r w
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1349; TranslationalTilings.Stepanov.reducedHassePolynomial_smul -/
namespace TranslationalTilings.Stepanov
axiom reducedHassePolynomial_smul
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ)
    (c : ZMod p) (v : AdditiveCoeffVector par) :
    reducedHassePolynomial par f b r (c • v) =
      c • reducedHassePolynomial par f b r v
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1357; TranslationalTilings.Stepanov.reducedHasseLinearMap -/
namespace TranslationalTilings.Stepanov
noncomputable def reducedHasseLinearMap
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ) :
    AdditiveCoeffVector par →ₗ[ZMod p] Polynomial (ZMod p) where
  toFun := reducedHassePolynomial par f b r
  map_add' := reducedHassePolynomial_add par f b r
  map_smul' := reducedHassePolynomial_smul par f b r
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1366; TranslationalTilings.Stepanov.additiveConstraintFun -/
namespace TranslationalTilings.Stepanov
noncomputable def additiveConstraintFun
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p)
    (v : AdditiveCoeffVector par) : AdditiveConstraintTarget par :=
  fun r q ↦ (reducedHassePolynomial par f b r.1 v).coeff q.1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1373; TranslationalTilings.Stepanov.additiveConstraintFun_add -/
namespace TranslationalTilings.Stepanov
axiom additiveConstraintFun_add
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p)
    (v w : AdditiveCoeffVector par) :
    additiveConstraintFun par f b (v + w) =
      additiveConstraintFun par f b v +
        additiveConstraintFun par f b w
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1382; TranslationalTilings.Stepanov.additiveConstraintFun_smul -/
namespace TranslationalTilings.Stepanov
axiom additiveConstraintFun_smul
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p)
    (c : ZMod p) (v : AdditiveCoeffVector par) :
    additiveConstraintFun par f b (c • v) =
      c • additiveConstraintFun par f b v
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1390; TranslationalTilings.Stepanov.additiveConstraint -/
namespace TranslationalTilings.Stepanov
noncomputable def additiveConstraint
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) :
    AdditiveCoeffVector par →ₗ[ZMod p] AdditiveConstraintTarget par where
  toFun := additiveConstraintFun par f b
  map_add' := additiveConstraintFun_add par f b
  map_smul' := additiveConstraintFun_smul par f b
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1405; TranslationalTilings.Stepanov.lowerTracePolynomial_natDegree_le -/
namespace TranslationalTilings.Stepanov
axiom lowerTracePolynomial_natDegree_le
    {p : ℕ} [Fact p.Prime] {d : ℕ}
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (u : ℕ) :
    (lowerTracePolynomial f u).natDegree ≤ d * p ^ (u - 1)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1411; TranslationalTilings.Stepanov.reducedHassePolynomial_natDegree_lt -/
namespace TranslationalTilings.Stepanov
axiom reducedHassePolynomial_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (b : ZMod p) (r : ℕ) (v : AdditiveCoeffVector par) :
    (reducedHassePolynomial par f b r v).natDegree <
      additiveConstraintDegree par
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1419; TranslationalTilings.Stepanov.upperTracePolynomial_eval_eq_of_trace_eq -/
namespace TranslationalTilings.Stepanov
axiom upperTracePolynomial_eval_eq_of_trace_eq
    {p : ℕ} [Fact p.Prime] {n u : ℕ}
    (f : Polynomial (ZMod p)) (hn : n ≠ 0) (hu : u ≤ n)
    (b : ZMod p) (x : GaloisField p n)
    (hx : Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b) :
    (upperTracePolynomial f n u).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x =
      (Polynomial.C b - lowerTracePolynomial f u).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1430; TranslationalTilings.Stepanov.reducedHassePolynomial_eval₂_eq_hasseDeriv_eval -/
namespace TranslationalTilings.Stepanov
axiom reducedHassePolynomial_eval₂_eq_hasseDeriv_eval
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p)
    (v : AdditiveCoeffVector par) (r : ℕ) (hr : r < par.R)
    (x : GaloisField p n)
    (hx : Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b) :
    (reducedHassePolynomial par f b r v).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x =
      Polynomial.eval x
        ((((coeffVectorToAuxiliary par f) v).map
          (algebraMap (ZMod p) (GaloisField p n))).hasseDeriv r)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1444; TranslationalTilings.Stepanov.additiveCoeffVector_finrank -/
namespace TranslationalTilings.Stepanov
axiom additiveCoeffVector_finrank
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :
    Module.finrank (ZMod p) (AdditiveCoeffVector par) =
      p * par.S * (par.K + 1)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1450; TranslationalTilings.Stepanov.additiveConstraintTarget_finrank -/
namespace TranslationalTilings.Stepanov
axiom additiveConstraintTarget_finrank
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :
    Module.finrank (ZMod p) (AdditiveConstraintTarget par) =
      par.R * additiveConstraintDegree par
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1456; TranslationalTilings.Stepanov.exists_nonzero_mem_additiveConstraint_ker -/
namespace TranslationalTilings.Stepanov
axiom exists_nonzero_mem_additiveConstraint_ker
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) :
    ∃ v : AdditiveCoeffVector par,
      v ≠ 0 ∧ v ∈ LinearMap.ker (additiveConstraint par f b)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1463; TranslationalTilings.Stepanov.reducedHassePolynomial_eq_zero_of_mem_ker -/
namespace TranslationalTilings.Stepanov
axiom reducedHassePolynomial_eq_zero_of_mem_ker
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (b : ZMod p) (v : AdditiveCoeffVector par)
    (hv : v ∈ LinearMap.ker (additiveConstraint par f b))
    (r : Fin par.R) :
    reducedHassePolynomial par f b r.1 v = 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1472; TranslationalTilings.Stepanov.coeffVectorToCoefficients_nonzero_iff -/
namespace TranslationalTilings.Stepanov
axiom coeffVectorToCoefficients_nonzero_iff
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) :
    (coeffVectorToCoefficients v).Nonzero ↔ v ≠ 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1478; TranslationalTilings.Stepanov.exists_additive_stepanov_coefficients -/
namespace TranslationalTilings.Stepanov
axiom exists_additive_stepanov_coefficients
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (b : ZMod p) :
    ∃ e : AdditiveAuxiliaryCoefficients par (ZMod p), e.Nonzero ∧
      ∀ x : GaloisField p n,
        Algebra.trace (ZMod p) (GaloisField p n)
            (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b →
          VanishesToOrderAtLeast
            ((additiveAuxiliaryPolynomial par f e).map
              (algebraMap (ZMod p) (GaloisField p n))) x par.R
end TranslationalTilings.Stepanov
