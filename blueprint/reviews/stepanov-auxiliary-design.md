# Implementation design for the Stepanov auxiliary repairs W2--W4

## Status, snapshot, and scope

This note supplies an implementation design for Findings W2--W4 of
[`weil-stepanov-independent.md`](weil-stepanov-independent.md).  It does not
edit or approve `05a-weil-stepanov.md`.  The reviewed chapter remains exactly
SHA-256

```text
6b21e03f6e63f662eb6e3ab81b281f1eca01cf029ebbd3b9fdedac9f1b9df4d0
```

and the pinned Mathlib checkout used below is exactly

```text
db584cd6d46c92f209a44c0f1c829460d327499d
```

The workspace containing the blueprint is not a Git worktree.  The hash above,
not a branch name, fixes the design target.  The implementation order is W4,
then the invariant/irreducibility part of W3, and independently W2, followed by
the W3 block induction.  W1, W5--W7, and any edit of a blueprint chapter are
outside this note.

The combined signature skeleton is
`tmp/StepanovAuxDesignSkeleton.lean`.  It elaborates at the pinned commit with
only the intentional `sorry` warnings in definition proof fields:

```text
lake env lean \
  /home/codex/Documents/Codex/2026-08-24/usi/tmp/StepanovAuxDesignSkeleton.lean
```

The skeleton verifies names, namespaces, coercions, fields, algebras, and all
types below.  It is not proof evidence.

## Exact import union and pinned Mathlib reuse

The following import union elaborated.  Implementations should split it by the
module homes below rather than retain the union in every file.

```lean
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.AdjoinRoot
```

The exact reusable declarations are:

- finite Pi spaces: `Module.finrank_fintype_fun_eq_card` and
  `Module.finrank_fin_fun`;
- rank-nullity: `LinearMap.ker_ne_bot_of_finrank_lt` and
  `Submodule.exists_mem_ne_zero_of_ne_bot`;
- Hasse calculus: `Polynomial.hasseDeriv`, `hasseDeriv_mul`, and the existing
  chapter seam `hasseDeriv_eval_frobenius`;
- low-coefficient divisibility: `Polynomial.X_pow_dvd_iff`;
- substitution modulo a divisor: `Polynomial.sub_dvd_eval_sub`;
- degree forcing: `Polynomial.eq_zero_of_dvd_of_natDegree_lt` and
  `Polynomial.natDegree_X_pow`;
- affine substitutions: `Polynomial.algEquivAevalXAddC`,
  `Polynomial.taylor_apply`, `Polynomial.natDegree_taylor`, and
  `MulEquiv.irreducible_iff`;
- minimal polynomials: `minpoly.dvd`, `minpoly.eq_of_irreducible_of_monic`,
  `IntermediateField.adjoin.finrank`, and `minpoly.degree_eq_one_iff`;
- splitting fields and Galois cardinality:
  `Polynomial.rootOfSplits`, `Polynomial.eval_rootOfSplits`,
  `SplittingField.splits`, `IsGalois.of_separable_splitting_field`, and
  `IsGalois.card_aut_eq_finrank`;
- prime-subfield roots: `Subfield.mem_bot_iff_pow_eq_self` and
  `Subfield.card_bot`;
- Lagrange: `AddSubgroup.card_addSubgroup_dvd_card` and
  `Nat.Prime.eq_one_or_self_of_dvd`;
- rational functions: `RatFunc.num`, `RatFunc.denom`,
  `RatFunc.num_div_denom`, `RatFunc.denom_ne_zero`,
  `RatFunc.monic_denom`, `RatFunc.isCoprime_num_denom`, and, as a degree
  cross-check only, `RatFunc.inftyValuation.polynomial`.

Pinned Mathlib has no theorem saying that translation invariants are
polynomials in `T^p-T`, no direct trace-only Stepanov constraint map, and no
Artin--Schreier reducible-if-and-only-if-root theorem.  Those are genuinely new
project declarations.

## 1. W4 first: a correct Artin--Schreier criterion

Module home:
`TranslationalTilings/NumberTheory/Stepanov/ArtinSchreier.lean`.

Use a sign-neutral generic polynomial first.  The chapter polynomial is the
specialization with `c = -algebraMap _ _ f`.

```lean
noncomputable def artinSchreierPolynomial
    {K : Type*} [Field K] (p : ℕ) (c : K) : K[X] :=
  Polynomial.X ^ p - Polynomial.X - Polynomial.C c

theorem artinSchreierPolynomial_monic
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).Monic

theorem artinSchreierPolynomial_natDegree
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).natDegree = p

theorem artinSchreierPolynomial_derivative
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).derivative = -1

theorem artinSchreierPolynomial_separable
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).Separable
```

Choose one root in the splitting field and expose, rather than hide, the
simple-extension and Galois-group steps.

```lean
noncomputable def artinSchreierSplittingRoot
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).SplittingField :=
  Polynomial.rootOfSplits
    (SplittingField.splits (artinSchreierPolynomial p c))
    (Polynomial.degree_ne_of_natDegree_ne (by
      rw [Polynomial.natDegree_map,
        artinSchreierPolynomial_natDegree c]
      exact (Fact.out : p.Prime).ne_zero))

theorem artinSchreierSplittingRoot_isRoot
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    ((artinSchreierPolynomial p c).map
      (algebraMap K (artinSchreierPolynomial p c).SplittingField)).IsRoot
        (artinSchreierSplittingRoot c)

theorem artinSchreier_root_sub_root_mem_bot
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]
    {c : K} {x y : L}
    (hx : (artinSchreierPolynomial p c).eval₂ (algebraMap K L) x = 0)
    (hy : (artinSchreierPolynomial p c).eval₂ (algebraMap K L) y = 0) :
    x - y ∈ (⊥ : Subfield L)

theorem artinSchreier_splittingField_adjoin_root_eq_top
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    IntermediateField.adjoin K {artinSchreierSplittingRoot c} =
      (⊤ : IntermediateField K
        (artinSchreierPolynomial p c).SplittingField)
```

The last theorem follows because every other root is `alpha+a`, where
`a^p=a`; `Subfield.mem_bot_iff_pow_eq_self` puts `a` in the prime subfield,
which is already in the image of `K`.  Thus one root contains every root and
generates the splitting field.

The automorphism shift is an additive, not multiplicative, homomorphism.  Its
domain is wrapped in `Additive` because `Polynomial.Gal P` is a multiplicative
group.

```lean
noncomputable def artinSchreierAutShift
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    Additive (Polynomial.Gal (artinSchreierPolynomial p c)) →+
      (⊥ : Subfield (artinSchreierPolynomial p c).SplittingField) := by
  classical
  let α := artinSchreierSplittingRoot c
  refine
    { toFun := fun σ ↦ ⟨σ α - α, ?_⟩
      map_zero' := ?_
      map_add' := ?_ }
  · -- Both `σ α` and `α` solve the same equation; subtract them and
    -- use `Subfield.mem_bot_iff_pow_eq_self`.
    sorry
  · apply Subtype.ext
    simp
  · intro σ τ
    apply Subtype.ext
    -- `τ α-α` lies in the prime subfield, hence comes from `K` and is
    -- fixed by `σ`; expand `(σ*τ)α-α`.
    sorry

theorem artinSchreierAutShift_injective
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : Function.Injective (artinSchreierAutShift c)

theorem artinSchreier_minpoly_natDegree_dvd_prime
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    (minpoly K (artinSchreierSplittingRoot c)).natDegree ∣ p

theorem artinSchreier_minpoly_natDegree_eq_one_or_prime
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    (minpoly K (artinSchreierSplittingRoot c)).natDegree = 1 ∨
      (minpoly K (artinSchreierSplittingRoot c)).natDegree = p

theorem artinSchreierPolynomial_irreducible_iff_no_root
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    Irreducible (artinSchreierPolynomial p c) ↔
      ¬ ∃ x : K, x ^ p - x = c

theorem not_artinSchreierPolynomial_irreducible_iff_root
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    ¬ Irreducible (artinSchreierPolynomial p c) ↔
      ∃ x : K, x ^ p - x = c
```

For `artinSchreier_minpoly_natDegree_dvd_prime`, separability makes the
splitting field Galois.  Its Galois group embeds into the additive prime
subfield; the range cardinal divides `p`.  Injectivity identifies the Galois
cardinal with its range cardinal, `IsGalois.card_aut_eq_finrank` identifies it
with the extension degree, and the adjoin theorem identifies that degree with
the minpoly degree.  Since `p` is prime, the degree is `1` or `p`.  In the
degree-one case `minpoly.degree_eq_one_iff` puts the chosen root in `K`.  In the
degree-`p` case `minpoly.dvd`, monicity, and equal degrees identify the minpoly
with the Artin--Schreier polynomial.

This is not the invalid translate-product proof.  In particular it never
claims that all translates of a proper factor multiply to the original
polynomial.  Over `F₅`, the translates of `T(T-1)` still multiply to
`(T⁵-T)²`, as recorded in W4.

The rational-function specialization then has three named steps.

```lean
theorem ratFunc_eq_algebraMap_of_pow_sub_self_eq_algebraMap
    {p : ℕ} [Fact p.Prime]
    (h : RatFunc (ZMod p)) (g : Polynomial (ZMod p))
    (heq : h ^ p - h =
      algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) g) :
    ∃ A : Polynomial (ZMod p),
      h = algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) A

theorem polynomial_pow_sub_self_natDegree
    {p : ℕ} [Fact p.Prime]
    (A : Polynomial (ZMod p)) (hA : 0 < A.natDegree) :
    (A ^ p - A).natDegree = p * A.natDegree

theorem no_ratFunc_artinSchreier_root
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ¬ ∃ h : RatFunc (ZMod p),
      h ^ p - h =
        -algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) f

theorem artinSchreierRatFuncPolynomial_irreducible
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    Irreducible (artinSchreierRatFuncPolynomial f)
```

The first proof need not build every finite-prime valuation.  Write `h=A/B`
using `RatFunc.num_div_denom`.  If the monic denominator is not a unit, choose
an irreducible divisor `q` of it.  Clearing denominators in
`h^p-h=g` gives

```text
A^p - A*B^(p-1) = g*B^p.
```

Modulo `q`, this says `q | A^p`, hence `q | A`, contradicting
`RatFunc.isCoprime_num_denom`.  Therefore `B` is a unit; monicity makes it
`1`.  This is shorter and more robust than constructing a valuation at each
irreducible.  `RatFunc.inftyValuation.polynomial` remains only a cross-check of
the positive-degree calculation.

## 2. W2: the literal finite linear system

Module home:
`TranslationalTilings/NumberTheory/Stepanov/AdditivePointCount.lean`.

Keep the existing `AdditiveAuxiliaryCoefficients` as the downstream package,
but never apply rank-nullity to it.  The actual vector spaces are finite Pi
types.

```lean
abbrev AdditiveCoeffVector {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :=
  Fin p → Fin (par.K + 1) → Fin par.S → ZMod p

def additiveConstraintDegree {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n) : ℕ :=
  par.S + d * (p - 1) * p ^ (par.u - 1) + par.K

abbrev AdditiveConstraintTarget {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :=
  Fin par.R → Fin (additiveConstraintDegree par) → ZMod p

theorem AdditiveStepanovParameters.S_pos
    {p d n : ℕ} (par : AdditiveStepanovParameters p d n) : 0 < par.S

theorem AdditiveStepanovParameters.n_pos
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) : 0 < n
```

`S_pos` follows immediately from `dimension_ok`: its right side is positive,
so `p*S*(K+1)>0`.  It is needed because Mathlib defines the zero polynomial's
`natDegree` to be zero; the promised strict bound cannot hold when `S=0`.
For `n_pos`, primality and `K_pos` make `R=p*K≥2`.  If `n=0`, then
`u=n/2=0` and `R_lt_frobenius` would say `R<p^0=1`, a contradiction.

```lean
noncomputable def coeffPolynomial
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) (i : Fin p) (j : Fin (par.K + 1)) :
    Polynomial (ZMod p) :=
  ∑ s : Fin par.S,
    Polynomial.C (v i j s) * Polynomial.X ^ s.1

theorem coeffPolynomial_coeff
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) (i : Fin p) (j : Fin (par.K + 1))
    (s : Fin par.S) :
    (coeffPolynomial v i j).coeff s.1 = v i j s

theorem coeffPolynomial_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) (i : Fin p) (j : Fin (par.K + 1)) :
    (coeffPolynomial v i j).natDegree < par.S

noncomputable def coeffVectorToCoefficients
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) :
    AdditiveAuxiliaryCoefficients par (ZMod p) where
  coeff := coeffPolynomial v
  degree_lt := coeffPolynomial_natDegree_lt v

noncomputable def coeffVectorToAuxiliary
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) :
    AdditiveCoeffVector par →ₗ[ZMod p] Polynomial (ZMod p) where
  toFun v :=
    additiveAuxiliaryPolynomial par f (coeffVectorToCoefficients v)
  map_add' := by
    intro v w
    simp [additiveAuxiliaryPolynomial, coeffVectorToCoefficients,
      coeffPolynomial, Finset.sum_add_distrib, add_mul]
  map_smul' := by
    intro c v
    simp [additiveAuxiliaryPolynomial, coeffVectorToCoefficients,
      coeffPolynomial, Finset.mul_sum]
```

Define the lower trace polynomial separately.  The exact reduced Hasse
polynomial is important: Hasse differentiation acts only on the bounded
coefficient polynomial, while the frozen upper trace is replaced on the fiber
by `b-lowerTracePolynomial f u`, and `X^(p^n*j)` becomes `X^j` on evaluation.

```lean
noncomputable def lowerTracePolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) : Polynomial (ZMod p) :=
  ∑ t ∈ Finset.range u, f ^ (p ^ t)

noncomputable def reducedHassePolynomial
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ)
    (v : AdditiveCoeffVector par) : Polynomial (ZMod p) :=
  ∑ i : Fin p, ∑ j : Fin (par.K + 1),
    (coeffPolynomial v i j).hasseDeriv r *
      (Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1 *
        Polynomial.X ^ j.1

noncomputable def reducedHasseLinearMap
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ) :
    AdditiveCoeffVector par →ₗ[ZMod p] Polynomial (ZMod p) where
  toFun := reducedHassePolynomial par f b r
  map_add' := by
    intro v w
    simp [reducedHassePolynomial, coeffPolynomial,
      Finset.sum_add_distrib, add_mul]
  map_smul' := by
    intro c v
    simp [reducedHassePolynomial, coeffPolynomial]

noncomputable def additiveConstraint
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) :
    AdditiveCoeffVector par →ₗ[ZMod p] AdditiveConstraintTarget par where
  toFun v r q :=
    (reducedHassePolynomial par f b r.1 v).coeff q.1
  map_add' := by
    intro v w
    ext r q
    simp [reducedHassePolynomial, coeffPolynomial,
      Finset.sum_add_distrib, add_mul]
  map_smul' := by
    intro c v
    ext r q
    simp [reducedHassePolynomial, coeffPolynomial]
```

The proof interfaces, in dependency order, are:

```lean
theorem lowerTracePolynomial_natDegree_le
    {p : ℕ} [Fact p.Prime] {d : ℕ}
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d) (u : ℕ) :
    (lowerTracePolynomial f u).natDegree ≤ d * p ^ (u - 1)

theorem reducedHassePolynomial_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (b : ZMod p) (r : ℕ) (v : AdditiveCoeffVector par) :
    (reducedHassePolynomial par f b r v).natDegree <
      additiveConstraintDegree par

theorem upperTracePolynomial_eval_eq_of_trace_eq
    {p : ℕ} [Fact p.Prime] {n u : ℕ}
    (f : Polynomial (ZMod p)) (hn : n ≠ 0) (hu : u ≤ n)
    (b : ZMod p) (x : GaloisField p n)
    (hx : Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b) :
    (upperTracePolynomial f n u).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x =
      (Polynomial.C b - lowerTracePolynomial f u).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x

theorem reducedHassePolynomial_eval₂_eq_hasseDeriv_eval
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
```

The trace identity used by `upperTracePolynomial_eval_eq_of_trace_eq` is the
pinned finite-field sum-of-Frobenius-powers theorem and requires `hn`; it is
not valid at extension index zero.  In the parameterized caller, pass
`(par.n_pos).ne'`.  The last proof must literally form
`r < par.R < p^par.u` from `hr` and `par.R_lt_frobenius`.  That is the input to
Frobenius freezing for every `f^(p^t)`, `t≥u`.  From `par.u_eq` it also gets
`r<p^n`, freezing `X^(p^n*j)`.  The `r=0` case is handled before the positive
Hasse-index argument.  This is the exact point at which
`R_lt_frobenius` is consumed.

The finrank and kernel layer is then small:

```lean
theorem additiveCoeffVector_finrank
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :
    Module.finrank (ZMod p) (AdditiveCoeffVector par) =
      p * par.S * (par.K + 1)

theorem additiveConstraintTarget_finrank
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :
    Module.finrank (ZMod p) (AdditiveConstraintTarget par) =
      par.R * additiveConstraintDegree par

theorem exists_nonzero_mem_additiveConstraint_ker
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) :
    ∃ v : AdditiveCoeffVector par,
      v ≠ 0 ∧ v ∈ LinearMap.ker (additiveConstraint par f b)

theorem reducedHassePolynomial_eq_zero_of_mem_ker
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (b : ZMod p) (v : AdditiveCoeffVector par)
    (hv : v ∈ LinearMap.ker (additiveConstraint par f b))
    (r : Fin par.R) :
    reducedHassePolynomial par f b r.1 v = 0

theorem coeffVectorToCoefficients_nonzero_iff
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) :
    (coeffVectorToCoefficients v).Nonzero ↔ v ≠ 0
```

For the kernel theorem, rewrite both finranks, unfold
`additiveConstraintDegree`, and apply `par.dimension_ok` to
`LinearMap.ker_ne_bot_of_finrank_lt`; obtain the vector with
`Submodule.exists_mem_ne_zero_of_ne_bot`.  For a kernel vector every coefficient
below `D` is zero by definition.  The strict reduced degree bound then makes the
whole polynomial zero.  The evaluation theorem supplies every Hasse vanishing,
and `coeffVectorToCoefficients_nonzero_iff` supplies the existing packaged
`Nonzero` field.  Thus `exists_additive_stepanov_coefficients` becomes a short
composition and is no longer a theorem-sized linear-system assertion.

## 3. W3: translation product and the zero block

These declarations belong in `ArtinSchreier.lean` if made generic, or in a
small `TranslationProduct.lean` imported by `AdditivePointCount.lean`.  They
must not import the point-count theorem.

For `P` in the outer variable `T` with coefficients in `F_p[X]`, define the
translation product literally.  It is not called a conjugate norm.

```lean
noncomputable def polynomialTranslate
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (β : ZMod p) :
    Polynomial (Polynomial (ZMod p)) :=
  P.comp (Polynomial.X + Polynomial.C (Polynomial.C β))

noncomputable def translationProduct
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) :
    Polynomial (Polynomial (ZMod p)) :=
  ∏ β : ZMod p, polynomialTranslate P β

theorem translationProduct_translate
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (γ : ZMod p) :
    polynomialTranslate (translationProduct P) γ = translationProduct P

theorem exists_translationProductQuotient
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p) :
    ∃ Q : Polynomial (Polynomial (ZMod p)),
      translationProduct P = Q.comp (Polynomial.X ^ p - Polynomial.X) ∧
        Q.natDegree ≤ p - 1

noncomputable def translationProductQuotient
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) :
    Polynomial (Polynomial (ZMod p)) :=
  if hP : P.natDegree < p then
    Classical.choose (exists_translationProductQuotient P hP)
  else 0

theorem translationProductQuotient_spec
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p) :
    translationProduct P =
        (translationProductQuotient P).comp
          (Polynomial.X ^ p - Polynomial.X) ∧
      (translationProductQuotient P).natDegree ≤ p - 1

theorem translationProductQuotient_coeff_natDegree_lt
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p)
    {S : ℕ} (hS : 0 < S)
    (hcoeff : ∀ i, (P.coeff i).natDegree < S) (a : ℕ) :
    ((translationProductQuotient P).coeff a).natDegree < p * S
```

Proof of the fixed-ring theorem is an outer-degree induction, not a product of
factor translates.  Translation invariance forces the leading outer exponent
to be divisible by `p`.  Subtract the leading coefficient times
`(T^p-T)^a` and recurse.  The subtraction strictly lowers outer degree and
does not increase any `X`-coefficient degree.  Before this induction, prove
the finite reindexing identity
`Finset.univ.bij` for `β↦β+γ`.  The product degree is at most
`p*(p-1)`, so the quotient degree is at most `p-1`.  Multiplying `p` factors
whose coefficient degrees are `<S` gives the strict bound `<p*S`; the
fixed-ring induction preserves it.

Define the reduced norm polynomial, still over `F_p[X]`, by substituting the
zero-block Artin--Schreier value.

```lean
noncomputable def zeroBlockNormPolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (P : Polynomial (Polynomial (ZMod p))) : Polynomial (ZMod p) :=
  (translationProductQuotient P).eval
    (Polynomial.C (f.coeff 0) - f ^ (p ^ u))

theorem zeroBlockNormPolynomial_natDegree_lt
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (P : Polynomial (Polynomial (ZMod p)))
    (hP : P.natDegree < p) {S : ℕ} (hS : 0 < S)
    (hcoeff : ∀ i, (P.coeff i).natDegree < S) :
    (zeroBlockNormPolynomial f u P).natDegree <
      p * S + f.natDegree * p ^ u * (p - 1)

theorem X_pow_dvd_zeroBlockNormPolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (n u : ℕ)
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p)
    (hu : u ≤ n)
    (hdiv : Polynomial.X ^ (p ^ n) ∣
      P.eval (upperTracePolynomial f n u)) :
    Polynomial.X ^ (p ^ n) ∣ zeroBlockNormPolynomial f u P

theorem zeroBlockNormPolynomial_eq_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (P : Polynomial (Polynomial (ZMod p)))
    (hP : P.natDegree < p)
    (hcoeff : ∀ i, (P.coeff i).natDegree < par.S)
    (hdiv : Polynomial.X ^ (p ^ n) ∣
      P.eval (upperTracePolynomial f n par.u)) :
    zeroBlockNormPolynomial f par.u P = 0
```

For the divisibility bridge, evaluate the translation-product identity at
`upperTracePolynomial`.  Its `β=0` factor is divisible by `X^(p^n)`, so the
whole product is.  The Artin--Schreier identity gives the first substitution
`f^(p^n)-f^(p^u)`.  Then use exactly
`Polynomial.sub_dvd_eval_sub` and

```text
X^(p^n) | f^(p^n) - C(f.coeff 0)
```

to replace it modulo `X^(p^n)` by
`C(f.coeff 0)-f^(p^u)`.  This is the requested mod-`X^(p^n)` bridge.  The
strict degree theorem, `hdegree`, and `par.norm_degree_ok` give degree
`<p^n`, whereas `natDegree (X^(p^n))=p^n`; apply
`Polynomial.eq_zero_of_dvd_of_natDegree_lt`.

## 4. Transported irreducibility and the one-zero-factor argument

Define the polynomial whose root is the zero-block `z`:

```lean
noncomputable def zeroBlockArtinSchreierPolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) :
    Polynomial (RatFunc (ZMod p)) :=
  Polynomial.X ^ p - Polynomial.X +
    Polynomial.C
      (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
        (f ^ (p ^ u) - Polynomial.C (f.coeff 0)))

theorem zeroBlockArtinSchreierPolynomial_translate
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) :
    zeroBlockArtinSchreierPolynomial f u =
      (artinSchreierRatFuncPolynomial (eraseConstant f)).comp
        (Polynomial.X + Polynomial.C
          (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
            (lowerTracePolynomial f u)))

theorem zeroBlockArtinSchreierPolynomial_irreducible
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    Irreducible (zeroBlockArtinSchreierPolynomial f u)
```

Indeed, for `s=sum_(t<u) f^(p^t)`, the freshman's dream gives
`s^p-s=f^(p^u)-f`.  Therefore translating
`T^p-T+(f-f(0))` by `T↦T+s` gives
`T^p-T+(f^(p^u)-f(0))`.  Transport irreducibility with the multiplicative
equivalence underlying `Polynomial.algEquivAevalXAddC`; do not restate it as an
unproved substitution principle.

The evaluation and minpoly interfaces are:

```lean
noncomputable def zeroBlockEval
    {p : ℕ} [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L]
    (P : Polynomial (Polynomial (ZMod p))) (z : L) : L :=
  P.eval₂
    ((algebraMap (RatFunc (ZMod p)) L).comp
      (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)))) z

theorem zeroBlockNorm_eq_zero_implies_exists_zero_factor
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p)
    (hnorm : zeroBlockNormPolynomial f u P = 0) :
    ∀ {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L] (z : L),
      Polynomial.aeval z (zeroBlockArtinSchreierPolynomial f u) = 0 →
      ∃ β : ZMod p,
        zeroBlockEval P
          (z + algebraMap (RatFunc (ZMod p)) L
            (algebraMap (ZMod p) (RatFunc (ZMod p)) β)) = 0

theorem zeroBlock_minpoly_add_primeField
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L]
    (z : L)
    (hz : Polynomial.aeval z (zeroBlockArtinSchreierPolynomial f u) = 0)
    (β : ZMod p) :
    minpoly (RatFunc (ZMod p))
      (z + algebraMap (RatFunc (ZMod p)) L
        (algebraMap (ZMod p) (RatFunc (ZMod p)) β)) =
      zeroBlockArtinSchreierPolynomial f u

theorem eq_zero_of_zeroBlockEval_eq_zero
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p)
    {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L]
    (z : L)
    (hz : Polynomial.aeval z (zeroBlockArtinSchreierPolynomial f u) = 0)
    (β : ZMod p)
    (hzero : zeroBlockEval P
      (z + algebraMap (RatFunc (ZMod p)) L
        (algebraMap (ZMod p) (RatFunc (ZMod p)) β)) = 0) :
    P = 0
```

The first theorem uses `Finset.prod_eq_zero_iff`: after evaluating
`translationProductQuotient_spec` at `z`, the zero norm says the finite product
is zero, so **one** `β`-factor is zero.  It does not conclude that all factors
are zero.  The translated element `z+β` is another root of the same
irreducible degree-`p` polynomial.  Hence that polynomial is its minpoly.  If
the mapped outer polynomial `P` vanishes there, `minpoly.dvd` makes the
degree-`p` minpoly divide a polynomial of degree `<p`.  Apply
`Polynomial.eq_zero_of_dvd_of_natDegree_lt`; injectivity of
`Polynomial.map (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)))` returns
`P=0` over `F_p[X]`.

## 5. Literal block induction

Package a single `j`-block in the outer variable.

```lean
noncomputable def auxiliaryBlock
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (j : Fin (par.K + 1)) : Polynomial (Polynomial (ZMod p)) :=
  ∑ i : Fin p, Polynomial.monomial i.1 (e.coeff i j)

theorem auxiliaryBlock_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (j : Fin (par.K + 1)) : (auxiliaryBlock e j).natDegree < p

theorem auxiliaryBlock_coeff_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (j : Fin (par.K + 1)) (i : ℕ) :
    ((auxiliaryBlock e j).coeff i).natDegree < par.S

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
      (auxiliaryBlock e j).eval (upperTracePolynomial f n par.u)

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
    auxiliaryBlock e j = 0

theorem all_auxiliaryBlocks_eq_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (haux : additiveAuxiliaryPolynomial par f e = 0) :
    ∀ j : Fin (par.K + 1), auxiliaryBlock e j = 0
```

Assuming all earlier blocks are zero, rewrite the auxiliary as

```text
X^(p^n*j) *
  (P_j(Phi) + X^(p^n) * laterTail) = 0.
```

The coefficient ring is a domain and `X^(p^n*j)≠0`, so cancel it.  This
proves `X^(p^n) | P_j(Phi)`.  The zero-block norm, transported root, one-factor,
and minpoly lemmas give `P_j=0`.  Perform strong induction on `j.1` (or
`Fin.induction`) to get `all_auxiliaryBlocks_eq_zero`.  Coefficient extraction
from `auxiliaryBlock e j=0` gives every `e.coeff i j=0`, contradicting
`e.Nonzero`.  This makes `additiveAuxiliaryPolynomial_ne_zero` a short final
corollary instead of the location of the entire descent.

## 6. Edge audit

- **Characteristic two.** `Fact p.Prime` implies `2≤p`, so the generic
  Artin--Schreier criterion includes `p=2`: the minpoly degree is `1` or `2`,
  and `T²-T-c` has derivative `-1=1`.  The fixed-ring statement becomes
  `Q(T²-T)` with `Q.natDegree≤1`.  In the main theorem,
  `0<d<p=2` forces `d=1`, so the Stepanov parameter branch is bypassed exactly
  as Chapter 05a requires.
- **Degree one.** All W2 and W3 signatures remain true for `d=1` if a parameter
  value is supplied, but the final proof should continue to use the direct
  nonzero linear trace functional.  No proof of the degree-one theorem should
  depend on `K_pos`, the translation product, or the norm descent.
- **Zero polynomial block.** If `P=0`, `translationProduct P=0` and the chosen
  quotient may be `0`; all coefficient and norm degree bounds still need
  `S_pos` because `natDegree 0=0`.  The one-factor theorem is harmless: every
  factor is zero.  The minpoly step still concludes `P=0`.
- **Zero initial block but later nonzero blocks.** The induction does not choose
  a least index noncomputably.  It proves the `j=0` block, then cancels and
  proves each successor.  Already-zero blocks therefore cause no branch or
  division by a coefficient.
- **`K=0`.** The block type is still `Fin (K+1)=Fin 1`; the induction has one
  base block.  Actual Stepanov parameters have `K_pos`, but no helper should
  accidentally require a second block.
- **`R=0`.** `VanishesToOrderAtLeast` remains vacuous.  Actual parameters have
  `R=p*K>0` from primality and `K_pos`; use a named `par.R_pos` when an element
  of `Fin par.R` is required rather than relying on simplification.
- **`u=0`.** `lowerTracePolynomial f 0=0`; its displayed degree bound remains
  valid.  Actual positive-degree parameters force enough positivity for the
  freezing use, but helper statements should not use an unproved `u-1+1=u`.
  Split `u=0` before natural-subtraction rewrites.
- **`n=0`.** The upper/lower trace split is deliberately stated with
  `hn : n ≠ 0`.  At `n=0`, `X^(p^0)-X=0`, so the constructed
  `GaloisField p 0` is the splitting field generated by no roots and is
  base-field-equivalent.  For `f=1` and `b=1`, the trace hypothesis holds,
  while both trace-polynomial sums are empty: the claimed equality would read
  `0=1`.  This is the regression excluded by `hn`.  Actual Stepanov parameters
  supply `par.n_pos`, proved from `K_pos`, `R_eq`, primality, and
  `R_lt_frobenius`.
- **Signs.** A zero-block root satisfies
  `z^p-z=C(f.coeff 0)-f^(p^u)`.  With
  `s=sum_(t<u)f^(p^t)`, `w=z+s` satisfies
  `w^p-w=C(f.coeff 0)-f`; consequently
  `w` is a root of `T^p-T+(f-f(0))`.  The definition and affine identity above
  encode this sign and should be used as regression tests.

## 7. Remaining implementation obligations and blockers

There is no remaining type-level or pinned-Mathlib blocker: the combined
signature skeleton elaborates.  There are, however, two substantial new proof
obligations that should remain visible in planning.

1. The fixed-ring theorem
   `exists_translationProductQuotient`, including preservation of the inner
   coefficient-degree filtration, is not in Mathlib.  It needs an elementary
   outer-degree induction and is the largest new algebraic helper in W3.
2. The evaluation theorem for `reducedHassePolynomial` needs careful Hasse
   product bookkeeping.  Its statement has been reduced to the exact formula,
   and `par.R_lt_frobenius` now appears at the correct boundary, but the proof
   is not a one-line use of the current generic freezing theorem.

The Galois proof of the Artin--Schreier criterion is longer than the false
factor-product sentence, but all its field-theory components exist in the
pinned checkout.  If compile cost becomes material, the automorphism-shift
helpers should be kept private while the generic reducible-if-and-only-if-root
criterion remains public.  No performance claim is made without profiling.

This note is an implementation design and verification record only.  It does
not mark W2--W4 resolved, does not approve the reviewed chapter, and does not
satisfy the independent re-review gate.
