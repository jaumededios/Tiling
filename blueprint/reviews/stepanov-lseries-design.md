# Implementation design for W1: finite Artin L-series recurrence

## Scope and conclusion

This note repairs the design gap W1 identified in
`blueprint/reviews/weil-stepanov-independent.md`. It does not edit or approve
`blueprint/05a-weil-stepanov.md`. The workspace root is not a Git worktree, so
the reviewed input is the current filesystem snapshot. All Lean names and
signatures below were checked against pinned Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d` in
`/home/codex/Documents/Codex/2026-08-14/Tiling/.lake/packages/mathlib`.

The recommended repair is a bounded polynomial recurrence, not an unbounded
`PowerSeries` Euler product. For each coefficient cutoff `M`, form a finite
product over monic irreducibles of degrees `1,...,M`, truncate each geometric
factor at exponent `M / r`, and compare coefficients only through degree `M`.
This gives

```text
m * T m = sum (j=1..m) E j * T (m-j),
```

where `E j` is a finite marked-factor sum. Finite-field minpoly fibers identify
`E j` with the extension exponential sum `S j`. Independently, finite
factorization of `L` by the roots of `reverse L` gives

```text
m * T m = -sum (j=1..m) P j * T (m-j).
```

Strong induction, using `T 0 = 1`, then gives `S m = -P m`. No convergence,
infinite product, formal inverse, or unbounded coefficient extensionality is
needed.

There is no missing Mathlib theorem that blocks this route. There are three
substantial project proofs: the coefficient theorem for the bounded Euler
product, the cardinality/weight theorem for minpoly fibers, and the finite
root-factor Newton recurrence. Each is exposed below as a separate named
boundary.

## Imports and pinned Mathlib reuse

The repair can live in a new internal module
`TranslationalTilings/NumberTheory/Stepanov/ArtinLSeries.lean`, importing the
existing `NewtonWaring` module. The additional explicit Mathlib imports should
be:

```lean
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Basic
```

`NewtonWaring.lean` already needs
`Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities` and the additive
character imports. `Mathlib.NumberTheory.LegendreSymbol.AddCharacter` is only
needed if the same file also proves character orthogonality; the L-series
recurrences themselves use only `Mathlib.Algebra.Group.AddChar`.

Exact reusable declarations, verified in the pinned checkout, are:

- encoding: `Polynomial.monicEquivDegreeLT`,
  `Polynomial.degreeLTEquiv`, and `Fin.rev`/`Fin.revPerm`;
- normalized UFD factors:
  `UniqueFactorizationMonoid.normalizedFactors`,
  `UniqueFactorizationMonoid.prod_normalizedFactors_eq`,
  `UniqueFactorizationMonoid.irreducible_of_normalized_factor`,
  `UniqueFactorizationMonoid.normalize_normalized_factor`, and
  `UniqueFactorizationMonoid.normalizedFactors_mul`;
- polynomial specialization:
  `Polynomial.leadingCoeff_mul_prod_normalizedFactors`,
  `Polynomial.mem_normalizedFactors_iff`,
  `Polynomial.normalize_eq_self_iff_monic`, and
  `Polynomial.natDegree_multiset_prod`;
- finite-field divisor criterion:
  `Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` from
  `Mathlib.FieldTheory.Finite.Extension`;
- the distinct, similarly named splitting theorem
  `Polynomial.Irreducible.natDegree_dvd_finrank`;
- `GaloisField.finrank`, `GaloisField.card`, `ZMod.card`, and
  `Nat.card_zmod`;
- minpoly/orbits: `minpoly.eq_of_irreducible_of_monic`,
  `minpoly.irreducible`, `minpoly.monic`, `minpoly.degree_dvd`, and
  `Normal.minpoly_eq_iff_mem_orbit`;
- separable roots: `PerfectField.separable_of_irreducible`,
  `Polynomial.card_rootSet_eq_natDegree`,
  `Polynomial.Splits.of_dvd`,
  `Polynomial.IsSplittingField.splits`, and
  `Polynomial.Splits.exists_eval_eq_zero`;
- trace: `FiniteField.algebraMap_trace_eq_sum_pow` and
  `AddChar.map_nsmul_eq_pow`;
- root factorization/reverse:
  `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq`,
  `Polynomial.reverse_mul_of_domain`, `Polynomial.reverse_natDegree`,
  `Polynomial.reverse_leadingCoeff`, `Polynomial.reflect_reflect`, and
  `Polynomial.coeff_reverse`;
- coefficient calculations: `Polynomial.coeff_derivative`,
  `Polynomial.coeff_mul`, `Polynomial.coeff_X_mul`,
  `Polynomial.finsetSum_coeff`, and
  `Finset.sum_fiberwise_eq_sum_filter`;
- existing project seams: `MonicDegreePolynomial.toPolynomial_monic`,
  `MonicDegreePolynomial.toPolynomial_natDegree`,
  `monicPowerSum_eq_sum_roots`, `monicWeight_mul`, and
  `artinCoefficient_eq_zero_of_degree_le`.

Namespace warning: the iff divisor criterion is literally
`Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`, not
`Polynomial.Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`.
Conversely, `natDegree_dvd_finrank` is under
`Polynomial.Irreducible`. The diagnostic check caught this distinction.

## Dependency-ordered Lean API

All sums below are finite. These declarations are ordered so that no theorem
mentions a later construction.

### 1. Reconstruction of the fixed-degree monic encoding

The chapter's coordinate `i` is coefficient `n - 1 - i`; Mathlib's
`degreeLTEquiv` uses coefficient `i`. The only adapter is `Fin.rev`.

```lean
def reverseCoordinatesEquiv (k : Type*) (n : ℕ) :
    (Fin n → k) ≃ (Fin n → k) where
  toFun a i := a i.rev
  invFun a i := a i.rev
  left_inv a := by ext i; simp
  right_inv a := by ext i; simp

def MonicDegreePolynomial.coeffEquiv
    (k : Type*) [CommRing k] (n : ℕ) :
    MonicDegreePolynomial k n ≃ (Fin n → k) where
  toFun := MonicDegreePolynomial.coeff
  invFun := MonicDegreePolynomial.mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def monicEncodingEquiv
    (k : Type*) [CommRing k] [Nontrivial k] (n : ℕ) :
    MonicDegreePolynomial k n ≃
      {P : Polynomial k // P.Monic ∧ P.natDegree = n} :=
  (MonicDegreePolynomial.coeffEquiv k n).trans <|
    (reverseCoordinatesEquiv k n).trans <|
      (Polynomial.degreeLTEquiv k n).symm.toEquiv.trans
        (Polynomial.monicEquivDegreeLT (R := k) n).symm

theorem monicEncodingEquiv_apply
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (A : MonicDegreePolynomial k n) :
    (monicEncodingEquiv k n A).1 = A.toPolynomial

noncomputable def MonicDegreePolynomial.ofPolynomial
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (P : Polynomial k) (hPmonic : P.Monic)
    (hPdegree : P.natDegree = n) : MonicDegreePolynomial k n :=
  (monicEncodingEquiv k n).symm ⟨P, hPmonic, hPdegree⟩

theorem MonicDegreePolynomial.toPolynomial_ofPolynomial
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (P : Polynomial k) (hPmonic : P.Monic)
    (hPdegree : P.natDegree = n) :
    (MonicDegreePolynomial.ofPolynomial P hPmonic hPdegree).toPolynomial = P

theorem MonicDegreePolynomial.ofPolynomial_toPolynomial
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (A : MonicDegreePolynomial k n) :
    MonicDegreePolynomial.ofPolynomial A.toPolynomial
      A.toPolynomial_monic A.toPolynomial_natDegree = A
```

`monicEncodingEquiv_apply` is a finite-sum reindexing by `Fin.revPerm`; the
last two theorems are then the two inverse laws. This includes `n = 0`:
`Fin 0 → k` is a singleton, `degreeLT k 0` contains only zero, and the unique
encoded polynomial is `1`.

### 2. Degree-forgetting monics and normalized irreducible factors

Using a degree-forgetting subtype removes dependent-degree friction from
factor products. `Classical.decEq k` should stay local to the noncomputable
definition; public users should not have to supply `[DecidableEq k]`.

```lean
def MonicPolynomial (k : Type*) [CommRing k] :=
  {P : Polynomial k // P.Monic}

namespace MonicPolynomial

noncomputable def encoding
    {k : Type*} [CommRing k] [Nontrivial k]
    (P : MonicPolynomial k) :
    MonicDegreePolynomial k P.1.natDegree :=
  (monicEncodingEquiv k P.1.natDegree).symm ⟨P.1, P.2, rfl⟩

theorem encoding_toPolynomial
    {k : Type*} [CommRing k] [Nontrivial k]
    (P : MonicPolynomial k) : P.encoding.toPolynomial = P.1

noncomputable def normalizedIrreducibleFactors
    {k : Type*} [Field k] (P : MonicPolynomial k) :
    Multiset (MonicPolynomial k) := by
  letI := Classical.decEq k
  exact (UniqueFactorizationMonoid.normalizedFactors P.1).attach.map
    fun G ↦
      ⟨G.1,
        ((Polynomial.mem_normalizedFactors_iff P.2.ne_zero).mp G.2).2.1⟩

theorem normalizedIrreducibleFactors_irreducible
    {k : Type*} [Field k] (P : MonicPolynomial k)
    {G : MonicPolynomial k}
    (hG : G ∈ P.normalizedIrreducibleFactors) : Irreducible G.1

theorem normalizedIrreducibleFactors_prod
    {k : Type*} [Field k] (P : MonicPolynomial k) :
    (P.normalizedIrreducibleFactors.map fun G ↦ G.1).prod = P.1

theorem normalizedIrreducibleFactors_degree_sum
    {k : Type*} [Field k] (P : MonicPolynomial k) :
    (P.normalizedIrreducibleFactors.map fun G ↦ G.1.natDegree).sum =
      P.1.natDegree

end MonicPolynomial

noncomputable def monicPolynomialWeight
    {k : Type*} [Field k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (P : MonicPolynomial k) : ℂ :=
  monicWeight psi f P.encoding

theorem monicWeight_eq_prod_normalizedIrreducibleFactors
    {k : Type*} [Field k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (P : MonicPolynomial k) :
    monicPolynomialWeight psi f P =
      (P.normalizedIrreducibleFactors.map
        (monicPolynomialWeight psi f)).prod
```

For `normalizedIrreducibleFactors_prod`, use `Multiset.attach_map_val`, then
`prod_normalizedFactors_eq`; monicity changes `normalize P.1` to `P.1` by
`Polynomial.Monic.normalize_eq_self`. The degree sum follows from
`Polynomial.natDegree_multiset_prod` and the fact that irreducibles are
nonzero. The weight theorem is multiset induction using `monicWeight_mul`,
transporting through `encoding_toPolynomial`. For `P = 1` the factor multiset
is empty and both weights are `1`.

### 3. Finite Euler product and marked-factor recurrence

The following definition is exactly the inner coefficient appearing after a
factor is marked. It contains no infinite sum.

```lean
noncomputable def markedFactorSum
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (m : ℕ) : ℂ := by
  classical
  exact ∑ r ∈ Finset.Icc 1 m with r ∣ m,
    ∑ G : MonicDegreePolynomial k r,
      if Irreducible G.toPolynomial then
        (r : ℂ) * monicWeight psi f G ^ (m / r)
      else 0

noncomputable def truncatedEulerFactor
    {k : Type*} [Field k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (cutoff r : ℕ) (G : MonicDegreePolynomial k r) : Polynomial ℂ :=
  ∑ a ∈ Finset.range (cutoff / r + 1),
    Polynomial.monomial (a * r) (monicWeight psi f G ^ a)

noncomputable def truncatedEulerProduct
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (cutoff : ℕ) : Polynomial ℂ := by
  classical
  exact ∏ r ∈ Finset.Icc 1 cutoff,
    ∏ G : MonicDegreePolynomial k r,
      if Irreducible G.toPolynomial then
        truncatedEulerFactor psi f cutoff r G
      else 1

noncomputable def markedFactorPolynomial
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (cutoff : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.Icc 1 cutoff,
    Polynomial.monomial j (markedFactorSum psi f j)

theorem truncatedEulerProduct_coeff
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (cutoff : ℕ)
    {n : ℕ} (hn : n ≤ cutoff) :
    (truncatedEulerProduct psi f cutoff).coeff n =
      artinCoefficient psi f n

theorem truncatedEulerProduct_logDerivative_coeff
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (cutoff : ℕ)
    {n : ℕ} (hn : n ≤ cutoff) :
    (Polynomial.X *
      (truncatedEulerProduct psi f cutoff).derivative).coeff n =
    (truncatedEulerProduct psi f cutoff *
      markedFactorPolynomial psi f cutoff).coeff n

theorem artinCoefficient_zero
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) :
    artinCoefficient psi f 0 = 1

theorem artinCoefficient_markedFactor_recurrence
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * artinCoefficient psi f m =
      ∑ j ∈ Finset.Icc 1 m,
        markedFactorSum psi f j * artinCoefficient psi f (m - j)
```

Proof of `truncatedEulerProduct_coeff`: expand the finite product. A selected
exponent `a_G` gives the multiset containing `a_G` copies of every selected
irreducible `G`. Its total degree is the monomial exponent. The normalized
factor multiset and reconstruction equivalence give a bijection between
selections of total degree `n` and `MonicDegreePolynomial k n`.
`monicWeight_eq_prod_normalizedIrreducibleFactors` identifies the products of
weights. The cutoff loses nothing when `n ≤ cutoff`, because every factor of
a degree-`n` polynomial has degree at most `n`, and its multiplicity is at
most `n / r`.

For the logarithmic-derivative coefficient theorem, use
`Polynomial.derivative_prod_finset`. For one degree-`r` factor the coefficient
calculation is the finite identity

```text
X * d/dX (sum_{a=0..M/r} w^a X^(a*r))
= (sum_{a=0..M/r} w^a X^(a*r))
  * (sum_{b=1..M/r} r*w^b X^(b*r))   mod X^(M+1).
```

Terms above the cutoff are irrelevant. Summing over irreducibles and grouping
`j = b*r` gives `markedFactorPolynomial`. Finally use
`Polynomial.coeff_derivative`, `Polynomial.coeff_X_mul`, and
`Polynomial.coeff_mul` at `n = m`. This proves the requested recurrence with
the positive sign.

This interface is preferable to making the recurrence a direct monolithic
factor-count bijection: the bounded Euler product is a concrete diagnostic
object, and both coefficient lemmas can be tested independently.

### 4. Minpoly fibers and finite-field orbits

```lean
noncomputable def minpolyFiber
    {p : ℕ} [Fact p.Prime] (m : ℕ)
    (G : Polynomial (ZMod p)) : Finset (GaloisField p m) := by
  letI := Fintype.ofFinite (GaloisField p m)
  classical
  exact Finset.univ.filter fun x ↦ minpoly (ZMod p) x = G

theorem minpolyFiber_nonempty_iff_natDegree_dvd
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (G : Polynomial (ZMod p))
    (hGmonic : G.Monic) (hGirr : Irreducible G) :
    (minpolyFiber m G).Nonempty ↔ G.natDegree ∣ m

theorem card_minpolyFiber
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (G : Polynomial (ZMod p))
    (hGmonic : G.Monic) (hGirr : Irreducible G) :
    (minpolyFiber m G).card =
      if G.natDegree ∣ m then G.natDegree else 0

theorem minpolyFiber_eq_galoisOrbit
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (x : GaloisField p m) :
    ↑(minpolyFiber m (minpoly (ZMod p) x)) =
      MulAction.orbit
        (GaloisField p m ≃ₐ[ZMod p] GaloisField p m) x

noncomputable def minpolyEncoding
    {p m : ℕ} [Fact p.Prime] (x : GaloisField p m) :
    MonicDegreePolynomial (ZMod p)
      (minpoly (ZMod p) x).natDegree :=
  (monicEncodingEquiv (ZMod p) (minpoly (ZMod p) x).natDegree).symm
    ⟨minpoly (ZMod p) x,
      minpoly.monic (Algebra.IsIntegral.isIntegral x), rfl⟩
```

Mathematical proof:

1. Rewrite `Nat.card (ZMod p)` as `p`. By
   `hGirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`, `deg G ∣ m`
   iff `G ∣ X^(p^m)-X`.
2. `GaloisField p m` is the splitting field of `X^(p^m)-X`. A divisor `G`
   therefore splits there. Since `deg G > 0`, choose a root using
   `Splits.exists_eval_eq_zero`, and identify its minpoly with `G` by
   `minpoly.eq_of_irreducible_of_monic`.
3. Conversely, if `minpoly x = G`, `minpoly.degree_dvd` and
   `GaloisField.finrank p hm` give `deg G ∣ m`.
4. Over the finite field `ZMod p`, `G` is separable by
   `PerfectField.separable_of_irreducible`. Once `G` splits,
   `Polynomial.card_rootSet_eq_natDegree` gives exactly `deg G` distinct
   roots. Its root set equals the minpoly fiber, proving the cardinal theorem.
5. `Normal.minpoly_eq_iff_mem_orbit` identifies that fiber with the Galois
   orbit. Thus the phrase “an orbit of exactly `natDegree G` elements” is a
   literal theorem, not only a counting gloss.

### 5. Identifying orbit weight with the trace summand

```lean
theorem minpolyPhase_eq_sum_frobenius
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (f : Polynomial (ZMod p)) (x : GaloisField p m) :
    algebraMap (ZMod p) (GaloisField p m)
      (monicPhase f (minpolyEncoding x)) =
    ∑ i ∈ Finset.range (minpoly (ZMod p) x).natDegree,
      f.eval₂ (algebraMap (ZMod p) (GaloisField p m))
        (x ^ (p ^ i))

theorem traceLiftAddChar_eq_minpolyWeight_pow
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (psi : AddChar (ZMod p) ℂ)
    (f : Polynomial (ZMod p)) (x : GaloisField p m) :
    traceLiftAddChar psi m
        (f.eval₂ (algebraMap (ZMod p) (GaloisField p m)) x) =
    monicWeight psi f (minpolyEncoding x) ^
      (m / (minpoly (ZMod p) x).natDegree)

theorem markedFactorSum_eq_extensionExponentialSum
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (psi : AddChar (ZMod p) ℂ)
    (f : Polynomial (ZMod p)) :
    markedFactorSum psi f m = extensionExponentialSum psi f m

theorem artinCoefficient_extension_recurrence
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ)
    (f : Polynomial (ZMod p))
    {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * artinCoefficient psi f m =
      ∑ j ∈ Finset.Icc 1 m,
        extensionExponentialSum psi f j *
          artinCoefficient psi f (m - j)
```

For `minpolyPhase_eq_sum_frobenius`, use
`monicPowerSum_eq_sum_roots`, separability, and the fact that the roots of the
minpoly are the Frobenius orbit
`x, x^p, ..., x^(p^(r-1))`. The trace formula is
`FiniteField.algebraMap_trace_eq_sum_pow`; rewrite its finrank with
`GaloisField.finrank p hm`, commute Frobenius with polynomial evaluation, and
split `m = r * (m / r)` into `m/r` orbit blocks. Applying the additive
character changes repeated addition to a power by
`AddChar.map_nsmul_eq_pow`.

For `markedFactorSum_eq_extensionExponentialSum`, partition `Finset.univ` by
`x ↦ minpoly (ZMod p) x`, using `Finset.sum_fiberwise_eq_sum_filter` (or
`Finset.sum_bij`). The two fiber theorems say precisely which monic
irreducibles occur and give fiber cardinality `r`; the trace-weight theorem
says the summand is constant on the fiber. This produces

```text
sum_{r|m} sum_{G monic irreducible, deg G=r}
  r * weight(G)^(m/r).
```

The extension recurrence is now just the marked-factor recurrence with
`markedFactorSum_eq_extensionExponentialSum` rewritten for every
`j ∈ Icc 1 m`; such a `j` is automatically nonzero.

### 6. Reverse-root Newton recurrence

Keep the multiset lemma independent of Artin data.

```lean
noncomputable def rootFactorPolynomial
    (roots : Multiset ℂ) : Polynomial ℂ :=
  (roots.map fun omega ↦
    1 - Polynomial.C omega * Polynomial.X).prod

def rootPowerSum (roots : Multiset ℂ) (m : ℕ) : ℂ :=
  (roots.map fun omega ↦ omega ^ m).sum

theorem rootFactorPolynomial_newton_recurrence
    (roots : Multiset ℂ) {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * (rootFactorPolynomial roots).coeff m =
      -∑ j ∈ Finset.Icc 1 m,
        rootPowerSum roots j *
          (rootFactorPolynomial roots).coeff (m - j)

theorem eq_rootFactorPolynomial_reverse_roots
    (L : Polynomial ℂ) (hL0 : L.coeff 0 = 1) :
    L = rootFactorPolynomial L.reverse.roots

noncomputable def reverseRootPowerSum
    (L : Polynomial ℂ) (m : ℕ) : ℂ :=
  rootPowerSum L.reverse.roots m

theorem reverseRoot_newton_recurrence
    (L : Polynomial ℂ) (hL0 : L.coeff 0 = 1)
    {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * L.coeff m =
      -∑ j ∈ Finset.Icc 1 m,
        reverseRootPowerSum L j * L.coeff (m - j)
```

`rootFactorPolynomial_newton_recurrence` has a short multiset induction.
After adjoining a root `a`, coefficients satisfy
`T'_m = T_m - a*T_(m-1)` and power sums satisfy
`P'_j = P_j + a^j`; the new terms telescope. This proof works above the
degree as well, because polynomial coefficients are then zero.

For the factorization theorem, `hL0` implies `L ≠ 0`, trailing degree zero,
and `L.reverse.Monic` via `reverse_leadingCoeff` and
`trailingCoeff_eq_coeff_zero`. Since `ℂ` is algebraically closed,
`L.reverse.roots.card = L.reverse.natDegree`; use
`prod_multiset_X_sub_C_of_monic_of_roots_card_eq`. Reverse the product using
`reverse_mul_of_domain`; the reverse of `X - C omega` is
`1 - C omega * X`. Finally, `reverse_natDegree` plus
`reflect_reflect` gives `L.reverse.reverse = L`. The generic recurrence then
transports along the factorization.

Although Mathlib has `MvPolynomial.psum_eq_mul_esymm_sub_sum`, using it here
would require an additional translation between elementary symmetric
polynomials and reversed coefficients. The direct multiset induction is
smaller and keeps the reverse convention and signs visible.

### 7. Coefficient bridge and induction to the trace identity

The truncation definition of `artinLPolynomial` must be related to the full
coefficient sequence before the two recurrences can share the same `T`.

```lean
theorem artinLPolynomial_coeff_eq_artinCoefficient
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    (m : ℕ) :
    (artinLPolynomial psi f).coeff m = artinCoefficient psi f m
```

If `m < f.natDegree`, this is the coefficient of the defining finite sum. If
`f.natDegree ≤ m`, both sides are zero: the right side by
`artinCoefficient_eq_zero_of_degree_le`, and the left side because the
defining sum stops before `f.natDegree`.

The final induction is a generic algebra lemma:

```lean
theorem neg_eq_of_convolution_recurrences
    (T S P : ℕ → ℂ) (hT0 : T 0 = 1)
    (hS : ∀ {m : ℕ}, 0 < m →
      (m : ℂ) * T m =
        ∑ j ∈ Finset.Icc 1 m, S j * T (m - j))
    (hP : ∀ {m : ℕ}, 0 < m →
      (m : ℂ) * T m =
        -∑ j ∈ Finset.Icc 1 m, P j * T (m - j)) :
    ∀ {m : ℕ}, 0 < m → S m = -P m
```

Use strong induction on `m`. Equating the two recurrence right sides and
moving signs gives

```text
sum_{j=1..m} (S j + P j) * T (m-j) = 0.
```

For `j < m`, the induction hypothesis kills the summand. The only remaining
term is `(S m + P m) * T 0`; `hT0` makes it `S m + P m`. This proof does not
divide by `m`, so it is valid over any commutative ring in which the displayed
recurrences are stated; `ℂ` is sufficient for the current consumer.

Specialization:

```lean
theorem extensionExponentialSum_eq_neg_reverseRootPowerSum
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {m : ℕ} (hm : m ≠ 0) :
    extensionExponentialSum psi f m =
      -reverseRootPowerSum (artinLPolynomial psi f) m
```

Instantiate `T m := artinCoefficient psi f m`,
`S m := extensionExponentialSum psi f m`, and
`P m := reverseRootPowerSum (artinLPolynomial psi f) m`. Use
`artinCoefficient_zero`, the extension recurrence, the reverse recurrence,
`artinLPolynomial_coeff_eq_artinCoefficient`, and
`artinLPolynomial_coeff_zero`. The existing terminal theorem then follows by
unfolding

```lean
reciprocalRoots psi f = (artinLPolynomial psi f).reverse.roots
```

and `reverseRootPowerSum`.

## Edge cases

### Extension degree `m = 0`

Do not state an orbit theorem at `m = 0`. The required pinned facts
`GaloisField.finrank` and `GaloisField.card` explicitly require `m ≠ 0`, and
the intended extension exponential sum identity is only used for positive
extension degree. `extensionExponentialSum` may remain defined at zero for API
uniformity, but none of the factor/orbit/trace recurrence theorems should claim
anything about that value. Convert terminal `hm : m ≠ 0` to `0 < m` with
`Nat.pos_of_ne_zero hm` only at the recurrence call.

### Polynomial degree `d = 1`

No separate L-series branch is needed. The coefficient bridge gives
`T 0 = 1` and `T m = 0` for every `m ≥ 1`, because
`artinCoefficient_eq_zero_of_degree_le` applies already at degree one. Thus
`artinLPolynomial = 1`, its reverse-root multiset is empty, and the induction
forces every positive extension sum to be zero. This agrees with the direct
linear-polynomial character-sum argument. In particular, the recurrence
repair must not add a hypothesis `2 ≤ f.natDegree`.

### Constant polynomial / `d = 0`

The terminal theorem already assumes `0 < f.natDegree`, so this case is not
part of W1. The encoding and finite Euler product still have correct zero
coefficients: the unique degree-zero monic is `1`, its normalized factor
multiset is empty, and `artinCoefficient psi f 0 = 1`. Keep the existing
constant regression separate.

### Irreducible degree zero

There are no degree-zero irreducible polynomials over a field. Defining all
factor sums over `Finset.Icc 1 m` avoids division by zero and avoids needing a
proof field in the index type. This lower bound should not be weakened to
`range (m+1)` with a conditional denominator.

### Repeated factors

`normalizedIrreducibleFactors` is a `Multiset`, not a `Finset`. Multiplicity is
essential: if `G` occurs `c` times, the marked logarithmic derivative has the
terms `r*w^a` for `a = 1,...,c`, and these sum to `c` marked occurrences after
coefficient convolution. Deduplicating the factors would make the recurrence
false.

## Implementation order and acceptance checks

Implement in the following atomic order:

1. encoding equivalence and the two reconstruction lemmas;
2. degree-forgetting monics, normalized factor multiset, exact product, degree
   sum, and weight product;
3. `markedFactorSum`, the bounded Euler objects, and the two coefficient
   theorems;
4. marked-factor recurrence;
5. minpoly fiber nonemptiness, cardinality, and orbit equality;
6. minpoly Frobenius phase and trace-weight power;
7. marked sum equals extension sum and the extension recurrence;
8. root-factor factorization and Newton recurrence;
9. all-coefficients bridge for `artinLPolynomial`;
10. generic convolution induction and the terminal specialization.

Minimum regressions:

- `n = 0` monic encoding reconstructs `1`;
- `truncatedEulerProduct ... 0 = 1` and coefficient zero is one;
- cutoff `1` gives the recurrence `T 1 = markedFactorSum ... 1`;
- a square `G^2` contributes both marked exponents `r` and `2*r`;
- `minpolyFiber` for a linear `G` has cardinality one for every positive `m`;
- a degree-`r` irreducible has empty fiber when `r ∤ m` and cardinality `r`
  when `r ∣ m`;
- `rootFactorPolynomial {ω}` is `1 - C ω * X`, and its recurrence has the
  negative sign;
- `L = 1` has empty reverse roots and zero positive power sums;
- the `d = 1` specialization returns zero extension sums without Stepanov
  parameters.

## Verified skeleton and remaining blockers

The literal definitions and signatures in this note elaborate in
`work/StepanovLSeriesDesign.lean` under the pinned `lake env lean`. Exact
Mathlib declaration names were separately checked in
`work/StepanovMathlibChecks.lean`. These are diagnostic skeletons containing
axiom signatures; their successful elaboration is namespace/type evidence,
not proof evidence.

No external blocker remains. The bounded Euler coefficient theorem is the
largest new proof in this W1 slice, but its statement no longer hides an
unbounded formal product. The finite-field orbit theorem is not already
packaged by Mathlib; it must be proved from the divisor criterion, splitting,
separability, and normal-orbit APIs listed above. The trace-weight theorem must
also explicitly prove the Frobenius orbit block decomposition. Those are
project obligations and should not be replaced by a prose appeal to “unique
factorization” or “Galois conjugacy.”

This design repairs W1 at the recursive-interface level. It does not assess or
approve the independent W2--W7 findings.
