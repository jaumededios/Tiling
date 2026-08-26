import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import TranslationalTilings.NumberTheory.Stepanov.NewtonWaring
/-!
Finite Euler products for additive Artin L-series, their minpoly/Frobenius
interpretation, and the Newton recurrence identifying exponential sums with
power sums of reciprocal roots.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings.Stepanov

open Polynomial

noncomputable section

private theorem monicWeight_degree_zero
    {k : Type*} [Field k] (psi : AddChar k ℂ) (f : Polynomial k)
    (A : MonicDegreePolynomial k 0) : monicWeight psi f A = 1 := by
  have hApoly : A.toPolynomial = 1 := by
    rw [MonicDegreePolynomial.toPolynomial]
    simp
  have hpower : ∀ j : ℕ, monicPowerSum A j = 0 := by
    intro j
    have h := monicPowerSum_eq_sum_roots (K := k) A (by simp [hApoly]) j
    simpa [hApoly] using h
  simp [monicWeight, monicPhase, hpower]

private theorem artinCoefficient_zero_aux
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) :
    artinCoefficient psi f 0 = 1 := by
  classical
  let A : MonicDegreePolynomial k 0 := ⟨fun i ↦ Fin.elim0 i⟩
  rw [artinCoefficient, Fintype.sum_eq_single A]
  · exact monicWeight_degree_zero psi f A
  · intro B hBA
    exact (hBA (by
      apply congrArg MonicDegreePolynomial.mk
      funext i
      exact Fin.elim0 i)).elim

/-- Degree-`cutoff` Artin L-polynomial whose coefficient of `X^n` is the weighted sum over monic
degree-`n` polynomials. -/
noncomputable def artinLPolynomial {k : Type*} [CommRing k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (max 1 f.natDegree),
    Polynomial.monomial n (artinCoefficient psi f n)

/-- Multiset of roots of the reversed Artin L-polynomial, counted with multiplicity. -/
noncomputable def reciprocalRoots
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) : Multiset ℂ :=
  (artinLPolynomial psi f).reverse.roots

/-- The constant coefficient of the Artin L-polynomial is one. -/
theorem artinLPolynomial_coeff_zero
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    (artinLPolynomial psi f).coeff 0 = 1 := by
  classical
  rw [artinLPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simpa using artinCoefficient_zero_aux psi f
  · intro n hn hn0
    simp [Polynomial.coeff_monomial, hn0]
  · simp

/-- Regression check: at cutoff zero the Artin L-polynomial is the constant polynomial one. -/
theorem artinLPolynomial_constant_regression
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (c : ZMod p) :
    artinLPolynomial psi (Polynomial.C c) = 1 := by
  classical
  ext n
  rw [artinLPolynomial, Polynomial.finsetSum_coeff]
  by_cases hn : n = 0
  · subst n
    simp [artinCoefficient_zero_aux]
  · simp [Polynomial.coeff_monomial, Polynomial.coeff_one, hn]

/-- The Artin L-polynomial has natural degree at most its truncation cutoff. -/
theorem artinLPolynomial_natDegree_le
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    (artinLPolynomial psi f).natDegree ≤ f.natDegree - 1 := by
  classical
  by_cases hd : f.natDegree = 0
  · rw [show artinLPolynomial psi f = 1 by
      ext n
      rw [artinLPolynomial, Polynomial.finsetSum_coeff]
      by_cases hn : n = 0
      · subst n
        simp [hd, artinCoefficient_zero_aux]
      · simp [hd, Polynomial.coeff_monomial, Polynomial.coeff_one, hn]]
    simp
  have hdpos : 0 < f.natDegree := Nat.pos_of_ne_zero hd
  rw [artinLPolynomial, max_eq_right (by omega)]
  refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range f.natDegree)
    (fun n ↦ Polynomial.monomial n (artinCoefficient psi f n)) ?_
  intro n hn
  exact (Polynomial.natDegree_monomial_le _).trans (by
    apply Nat.le_sub_one_of_lt
    exact Finset.mem_range.mp hn)

/-- The reciprocal-root multiset has cardinality at most the Artin cutoff. -/
theorem reciprocalRoots_card_le
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    (reciprocalRoots psi f).card ≤ f.natDegree - 1 := by
  exact (Polynomial.card_roots' _).trans
    ((Polynomial.reverse_natDegree_le _).trans
      (artinLPolynomial_natDegree_le psi f))

/-- Weighted divisor sum over monic irreducibles whose degrees divide `m`, with the usual degree
marking factor. -/
noncomputable def markedFactorSum
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (m : ℕ) : ℂ := by
  classical
  exact ∑ r ∈ Finset.Icc 1 m with r ∣ m,
    ∑ G : MonicDegreePolynomial k r,
      if Irreducible G.toPolynomial then
        (r : ℂ) * monicWeight psi f G ^ (m / r)
      else 0

/-- Truncated geometric Euler factor associated to one monic polynomial and one exponent scale. -/
noncomputable def truncatedEulerFactor
    {k : Type*} [Field k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (cutoff r : ℕ) (G : MonicDegreePolynomial k r) : Polynomial ℂ :=
  ∑ a ∈ Finset.range (cutoff / r + 1),
    Polynomial.monomial (a * r) (monicWeight psi f G ^ a)

/-- Finite product of truncated local Euler factors over exponent scales and monic polynomials. -/
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

/-- Polynomial collecting the marked irreducible-factor sums up to the cutoff. -/
noncomputable def markedFactorPolynomial
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (cutoff : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.Icc 1 cutoff,
    Polynomial.monomial j (markedFactorSum psi f j)

private theorem markedFactorPolynomial_coeff_of_pos_le
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (cutoff : ℕ)
    {j : ℕ} (hjpos : 0 < j) (hj : j ≤ cutoff) :
    (markedFactorPolynomial psi f cutoff).coeff j =
      markedFactorSum psi f j := by
  classical
  rw [markedFactorPolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single j]
  · simp
  · intro a _ha haj
    rw [Polynomial.coeff_monomial, if_neg haj]
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨hjpos, hj⟩)).elim

private theorem markedFactorPolynomial_coeff_zero
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (cutoff : ℕ) :
    (markedFactorPolynomial psi f cutoff).coeff 0 = 0 := by
  classical
  rw [markedFactorPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro a ha
  rw [Polynomial.coeff_monomial, if_neg]
  exact (Nat.lt_of_lt_of_le Nat.zero_lt_one
    (Finset.mem_Icc.mp ha).1).ne'

private noncomputable instance instDecidableEqField
    {k : Type*} [Field k] : DecidableEq k := Classical.decEq k

private abbrev EulerBaseIndex (k : Type*) [Field k] [Fintype k]
    (cutoff : ℕ) :=
  Σ r : {r : ℕ // r ∈ Finset.Icc 1 cutoff}, MonicDegreePolynomial k r.1

private abbrev EulerPrime (k : Type*) [Field k] [Fintype k]
    (cutoff : ℕ) :=
  {i : EulerBaseIndex k cutoff // Irreducible i.2.toPolynomial}

private def EulerPrime.degree
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (i : EulerPrime k cutoff) : ℕ := i.1.1.1

private def EulerPrime.encoding
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (i : EulerPrime k cutoff) : MonicDegreePolynomial k i.degree := i.1.2

private noncomputable def EulerPrime.toPolynomial
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (i : EulerPrime k cutoff) : Polynomial k := i.encoding.toPolynomial

private theorem EulerPrime.degree_pos
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (i : EulerPrime k cutoff) : 0 < i.degree :=
  (Finset.mem_Icc.mp i.1.1.2).1

private theorem EulerPrime.degree_le
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (i : EulerPrime k cutoff) : i.degree ≤ cutoff :=
  (Finset.mem_Icc.mp i.1.1.2).2

private theorem EulerPrime.toPolynomial_monic
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (i : EulerPrime k cutoff) : i.toPolynomial.Monic :=
  i.encoding.toPolynomial_monic

private theorem EulerPrime.toPolynomial_natDegree
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (i : EulerPrime k cutoff) : i.toPolynomial.natDegree = i.degree :=
  i.encoding.toPolynomial_natDegree

private theorem EulerPrime.toPolynomial_irreducible
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (i : EulerPrime k cutoff) : Irreducible i.toPolynomial := i.2

private theorem MonicDegreePolynomial.toPolynomial_injective_fixed
    {k : Type*} [Field k] {n : ℕ} :
    Function.Injective
      (MonicDegreePolynomial.toPolynomial : MonicDegreePolynomial k n → Polynomial k) := by
  intro A B h
  apply (monicEncodingEquiv k n).injective
  apply Subtype.ext
  simpa only [monicEncodingEquiv_apply] using h

private theorem MonicDegreePolynomial.heq_of_toPolynomial_eq
    {k : Type*} [Field k] {n m : ℕ}
    (A : MonicDegreePolynomial k n) (B : MonicDegreePolynomial k m)
    (h : A.toPolynomial = B.toPolynomial) : HEq A B := by
  have hnm : n = m := by
    rw [← A.toPolynomial_natDegree, ← B.toPolynomial_natDegree, h]
  subst m
  exact heq_of_eq (MonicDegreePolynomial.toPolynomial_injective_fixed h)

private noncomputable def sigmaMonicWeight
    {k : Type*} [Field k] (psi : AddChar k ℂ) (f : Polynomial k)
    (z : Σ n, MonicDegreePolynomial k n) : ℂ :=
  monicWeight psi f z.2

private theorem EulerPrime.toPolynomial_injective
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ} :
    Function.Injective (EulerPrime.toPolynomial : EulerPrime k cutoff → Polynomial k) := by
  intro i j hij
  have hdegree : i.degree = j.degree := by
    rw [← i.toPolynomial_natDegree, ← j.toPolynomial_natDegree, hij]
  apply Subtype.ext
  cases i with
  | mk i hi =>
    cases j with
    | mk j hj =>
      cases i with
      | mk ri Gi =>
        cases j with
        | mk rj Gj =>
          have hrs : ri.1 = rj.1 := hdegree
          cases ri with
          | mk r hri =>
            cases rj with
            | mk s hsj =>
              dsimp at hrs
              subst s
              have hproof : hsj = hri := Subsingleton.elim _ _
              subst hsj
              have hG : Gi = Gj :=
                MonicDegreePolynomial.toPolynomial_injective_fixed hij
              subst Gj
              rfl

private noncomputable instance
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ} :
    Fintype (EulerPrime k cutoff) := Fintype.ofFinite _

private noncomputable instance
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ} :
    DecidableEq (EulerPrime k cutoff) := Classical.decEq _

private abbrev EulerSelection
    (k : Type*) [Field k] [Fintype k] (cutoff : ℕ) :=
  ∀ i : EulerPrime k cutoff, Fin (cutoff / i.degree + 1)

private noncomputable def selectionDegree
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (e : EulerSelection k cutoff) : ℕ :=
  ∑ i : EulerPrime k cutoff, (e i).1 * i.degree

private noncomputable def selectionPolynomial
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (e : EulerSelection k cutoff) : Polynomial k :=
  ∏ i : EulerPrime k cutoff, i.toPolynomial ^ (e i).1

private theorem monic_finset_prod
    {k ι : Type*} [Field k] (s : Finset ι) (P : ι → Polynomial k)
    (hP : ∀ i ∈ s, (P i).Monic) : (∏ i ∈ s, P i).Monic := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hP a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => hP i (Finset.mem_insert_of_mem hi)))

private theorem selectionPolynomial_monic
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (e : EulerSelection k cutoff) : (selectionPolynomial e).Monic := by
  classical
  apply monic_finset_prod
  intro i hi
  exact i.toPolynomial_monic.pow _

private theorem selectionPolynomial_natDegree
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (e : EulerSelection k cutoff) :
    (selectionPolynomial e).natDegree = selectionDegree e := by
  classical
  rw [selectionPolynomial, selectionDegree,
    Polynomial.natDegree_prod_of_monic]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.natDegree_pow, i.toPolynomial_natDegree]
  · intro i hi
    exact i.toPolynomial_monic.pow _

private theorem factorization_prime
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (i : EulerPrime k cutoff) :
    factorization i.toPolynomial = Finsupp.single i.toPolynomial 1 := by
  classical
  ext P
  rw [factorization_eq_count, UniqueFactorizationMonoid.normalizedFactors_irreducible
    i.toPolynomial_irreducible, i.toPolynomial_monic.normalize_eq_self]
  simp [Multiset.count_singleton, Finsupp.single_apply, eq_comm]

private theorem factorization_selectionPolynomial
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (e : EulerSelection k cutoff) :
    factorization (selectionPolynomial e) =
      ∑ i : EulerPrime k cutoff, (e i).1 • Finsupp.single i.toPolynomial 1 := by
  classical
  simp only [selectionPolynomial]
  induction (Finset.univ : Finset (EulerPrime k cutoff)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, factorization_mul]
      · rw [factorization_pow, factorization_prime, Finset.sum_insert hi, ih]
      · exact (i.toPolynomial_monic.pow _).ne_zero
      · exact (monic_finset_prod s _ (fun j hj => j.toPolynomial_monic.pow _)).ne_zero

private theorem factorization_selectionPolynomial_apply
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (e : EulerSelection k cutoff) (i : EulerPrime k cutoff) :
    factorization (selectionPolynomial e) i.toPolynomial = (e i).1 := by
  classical
  rw [factorization_selectionPolynomial, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    rw [Finsupp.smul_single]
    simp only [nsmul_eq_mul, mul_one, Finsupp.single_apply]
    rw [if_neg]
    intro hpoly
    exact hji (EulerPrime.toPolynomial_injective hpoly)
  · simp

private theorem selectionPolynomial_injective
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ} :
    Function.Injective (selectionPolynomial : EulerSelection k cutoff → Polynomial k) := by
  intro e e' he
  funext i
  apply Fin.ext
  rw [← factorization_selectionPolynomial_apply e i,
    ← factorization_selectionPolynomial_apply e' i, he]

private theorem count_mul_le_sum_map
    {a : Type*} [DecidableEq a] (s : Multiset a) (x : a) (w : a → ℕ) :
    Multiset.count x s * w x ≤ (s.map w).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons y s ih =>
      by_cases hy : y = x
      · subst y
        simp only [Multiset.count_cons_self, Multiset.map_cons, Multiset.sum_cons,
          Nat.add_mul]
        omega
      · simp only [Multiset.count_cons_of_ne (fun h ↦ hy h.symm), Multiset.map_cons,
          Multiset.sum_cons]
        omega

private theorem factorization_mul_degree_le
    {k : Type*} [Field k] {n : ℕ}
    (A : MonicDegreePolynomial k n) (P : Polynomial k) :
    factorization A.toPolynomial P * P.natDegree ≤ n := by
  let s := UniqueFactorizationMonoid.normalizedFactors A.toPolynomial
  calc
    factorization A.toPolynomial P * P.natDegree =
        Multiset.count P s * P.natDegree := by
          rw [factorization_eq_count]
    _ ≤ (s.map Polynomial.natDegree).sum := count_mul_le_sum_map s P _
    _ = n := by
      rw [← Polynomial.natDegree_multiset_prod s
        (UniqueFactorizationMonoid.zero_notMem_normalizedFactors A.toPolynomial)]
      rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq
        A.toPolynomial_monic.ne_zero, A.toPolynomial_monic.normalize_eq_self,
        A.toPolynomial_natDegree]

private noncomputable def decodingSelection
    {k : Type*} [Field k] [Fintype k] {cutoff n : ℕ}
    (hn : n ≤ cutoff) (A : MonicDegreePolynomial k n) :
  EulerSelection k cutoff := fun i ↦
  ⟨factorization A.toPolynomial i.toPolynomial, by
    have hmul : factorization A.toPolynomial i.toPolynomial * i.degree ≤ cutoff :=
      calc
        factorization A.toPolynomial i.toPolynomial * i.degree =
            factorization A.toPolynomial i.toPolynomial * i.toPolynomial.natDegree := by
              rw [i.toPolynomial_natDegree]
        _ ≤ n := factorization_mul_degree_le A i.toPolynomial
        _ ≤ cutoff := hn
    have hle : factorization A.toPolynomial i.toPolynomial ≤ cutoff / i.degree :=
      (Nat.le_div_iff_mul_le i.degree_pos).2 hmul
    omega⟩

private theorem selectionPolynomial_decodingSelection_factorization
    {k : Type*} [Field k] [Fintype k] {cutoff n : ℕ}
    (hn : n ≤ cutoff) (A : MonicDegreePolynomial k n) :
    factorization (selectionPolynomial (decodingSelection hn A)) =
      factorization A.toPolynomial := by
  classical
  ext P
  by_cases hP : factorization A.toPolynomial P = 0
  · rw [hP, factorization_selectionPolynomial]
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finsupp.smul_single]
    simp only [nsmul_eq_mul, mul_one, Finsupp.single_apply]
    split_ifs with hPi
    · subst P
      simp [decodingSelection, hP]
    · simp
  · have hcount : Multiset.count P
        (UniqueFactorizationMonoid.normalizedFactors A.toPolynomial) ≠ 0 := by
      simpa only [factorization_eq_count] using hP
    have hPmem : P ∈ UniqueFactorizationMonoid.normalizedFactors A.toPolynomial :=
      Multiset.count_pos.mp (Nat.pos_of_ne_zero hcount)
    have hPdata :=
      (Polynomial.mem_normalizedFactors_iff A.toPolynomial_monic.ne_zero).mp hPmem
    have hPpos : 0 < P.natDegree := (hPdata.1.natDegree_pos)
    have hPle : P.natDegree ≤ cutoff := by
      have := factorization_mul_degree_le A P
      have hfacpos : 0 < factorization A.toPolynomial P := Nat.pos_of_ne_zero hP
      exact (Nat.le_mul_of_pos_left P.natDegree hfacpos).trans (this.trans hn)
    let G : MonicDegreePolynomial k P.natDegree :=
      MonicDegreePolynomial.ofPolynomial P hPdata.2.1 rfl
    let i : EulerPrime k cutoff :=
      ⟨⟨⟨P.natDegree, Finset.mem_Icc.mpr ⟨hPpos, hPle⟩⟩, G⟩, by
        simpa [G, MonicDegreePolynomial.toPolynomial_ofPolynomial] using hPdata.1⟩
    have hiP : i.toPolynomial = P := by
      change G.toPolynomial = P
      exact MonicDegreePolynomial.toPolynomial_ofPolynomial P hPdata.2.1 rfl
    rw [← hiP, factorization_selectionPolynomial_apply]
    rfl

private theorem selectionPolynomial_decodingSelection
    {k : Type*} [Field k] [Fintype k] {cutoff n : ℕ}
    (hn : n ≤ cutoff) (A : MonicDegreePolynomial k n) :
    selectionPolynomial (decodingSelection hn A) = A.toPolynomial := by
  classical
  have hassoc := associated_of_factorization_eq
    (selectionPolynomial (decodingSelection hn A)) A.toPolynomial
    (selectionPolynomial_monic _).ne_zero A.toPolynomial_monic.ne_zero
    (selectionPolynomial_decodingSelection_factorization hn A)
  have hnorm : normalize (selectionPolynomial (decodingSelection hn A)) =
      normalize A.toPolynomial := normalize_eq_normalize_iff.mpr hassoc.dvd_dvd
  rw [(selectionPolynomial_monic (decodingSelection hn A)).normalize_eq_self,
    A.toPolynomial_monic.normalize_eq_self] at hnorm
  exact hnorm

private theorem selectionDegree_decodingSelection
    {k : Type*} [Field k] [Fintype k] {cutoff n : ℕ}
    (hn : n ≤ cutoff) (A : MonicDegreePolynomial k n) :
    selectionDegree (decodingSelection hn A) = n := by
  rw [← selectionPolynomial_natDegree, selectionPolynomial_decodingSelection hn A,
    A.toPolynomial_natDegree]

private noncomputable def selectionEquivMonicDegree
    {k : Type*} [Field k] [Fintype k] {cutoff n : ℕ}
    (hn : n ≤ cutoff) :
    {e : EulerSelection k cutoff // selectionDegree e = n} ≃
      MonicDegreePolynomial k n where
  toFun e := MonicDegreePolynomial.ofPolynomial (selectionPolynomial e.1)
    (selectionPolynomial_monic e.1) (by
      rw [selectionPolynomial_natDegree, e.2])
  invFun A := ⟨decodingSelection hn A, selectionDegree_decodingSelection hn A⟩
  left_inv e := by
    apply Subtype.ext
    apply selectionPolynomial_injective
    rw [selectionPolynomial_decodingSelection hn]
    exact MonicDegreePolynomial.toPolynomial_ofPolynomial _ _ _
  right_inv A := by
    apply MonicDegreePolynomial.toPolynomial_injective_fixed
    rw [MonicDegreePolynomial.toPolynomial_ofPolynomial,
      selectionPolynomial_decodingSelection hn A]

private noncomputable def primeEulerFactor
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (w : EulerPrime k cutoff → ℂ) (i : EulerPrime k cutoff) : Polynomial ℂ :=
  ∑ a : Fin (cutoff / i.degree + 1),
    Polynomial.monomial (a.1 * i.degree) (w i ^ a.1)

private noncomputable def primeEulerProduct
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (w : EulerPrime k cutoff → ℂ) : Polynomial ℂ :=
  ∏ i : EulerPrime k cutoff, primeEulerFactor w i

private theorem finset_prod_monomial
    {R ι : Type*} [CommSemiring R] (s : Finset ι)
    (d : ι → ℕ) (c : ι → R) :
    (∏ i ∈ s, Polynomial.monomial (d i) (c i)) =
      Polynomial.monomial (∑ i ∈ s, d i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha, ih,
        Polynomial.monomial_mul_monomial]

private theorem primeEulerProduct_eq_sum_selection
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (w : EulerPrime k cutoff → ℂ) :
    primeEulerProduct w =
      ∑ e : EulerSelection k cutoff,
        Polynomial.monomial (selectionDegree e)
          (∏ i : EulerPrime k cutoff, w i ^ (e i).1) := by
  classical
  rw [primeEulerProduct]
  simp_rw [primeEulerFactor]
  rw [Fintype.prod_sum]
  apply Fintype.sum_congr
  intro e
  rw [finset_prod_monomial]
  rfl

private theorem primeEulerProduct_coeff
    {k : Type*} [Field k] [Fintype k] {cutoff n : ℕ}
    (w : EulerPrime k cutoff → ℂ) :
    (primeEulerProduct w).coeff n =
      ∑ e : {e : EulerSelection k cutoff // selectionDegree e = n},
        ∏ i : EulerPrime k cutoff, w i ^ (e.1 i).1 := by
  classical
  rw [primeEulerProduct_eq_sum_selection, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_monomial]
  rw [← Finset.sum_filter (p := fun e : EulerSelection k cutoff ↦
    selectionDegree e = n) (fun e ↦ ∏ i, w i ^ (e i).1)]
  exact Finset.sum_subtype
    (Finset.univ.filter fun e : EulerSelection k cutoff ↦ selectionDegree e = n)
    (by intro e; simp) (fun e ↦ ∏ i, w i ^ (e i).1)

private noncomputable def nestedEulerProduct
    {k : Type*} [Field k] [Fintype k] (cutoff : ℕ)
    (W : (r : ℕ) → MonicDegreePolynomial k r → ℂ) : Polynomial ℂ := by
  classical
  exact ∏ r ∈ Finset.Icc 1 cutoff,
    ∏ G : MonicDegreePolynomial k r,
      if Irreducible G.toPolynomial then
        ∑ a ∈ Finset.range (cutoff / r + 1),
          Polynomial.monomial (a * r) (W r G ^ a)
      else 1

private noncomputable def iteratedEulerPrimeEquiv
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ} :
    (Σ r : {r : ℕ // r ∈ Finset.Icc 1 cutoff},
      {G : MonicDegreePolynomial k r.1 // Irreducible G.toPolynomial}) ≃
      EulerPrime k cutoff where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem nestedEulerProduct_eq_primeEulerProduct
    {k : Type*} [Field k] [Fintype k] (cutoff : ℕ)
    (W : (r : ℕ) → MonicDegreePolynomial k r → ℂ) :
    nestedEulerProduct cutoff W =
      primeEulerProduct (fun i : EulerPrime k cutoff ↦ W i.degree i.encoding) := by
  classical
  rw [nestedEulerProduct]
  let fintypeR : Fintype {r : ℕ // r ∈ Finset.Icc 1 cutoff} := Fintype.ofFinite _
  rw [Finset.prod_subtype (F := fintypeR)
    (Finset.Icc 1 cutoff) (fun r ↦ Iff.rfl)]
  have hinner (r : {r : ℕ // r ∈ Finset.Icc 1 cutoff}) :
      (∏ G : MonicDegreePolynomial k r.1,
        if Irreducible G.toPolynomial then
          ∑ a ∈ Finset.range (cutoff / r.1 + 1),
            Polynomial.monomial (a * r.1) (W r.1 G ^ a)
        else 1) =
      ∏ G : {G : MonicDegreePolynomial k r.1 // Irreducible G.toPolynomial},
        ∑ a ∈ Finset.range (cutoff / r.1 + 1),
          Polynomial.monomial (a * r.1) (W r.1 G.1 ^ a) := by
    rw [← Finset.prod_filter]
    exact Finset.prod_subtype
      (Finset.univ.filter fun G : MonicDegreePolynomial k r.1 ↦
        Irreducible G.toPolynomial) (fun G ↦ by simp)
      (fun G ↦ ∑ a ∈ Finset.range (cutoff / r.1 + 1),
        Polynomial.monomial (a * r.1) (W r.1 G ^ a))
  simp_rw [hinner]
  calc
    (∏ r : {r : ℕ // r ∈ Finset.Icc 1 cutoff},
      ∏ G : {G : MonicDegreePolynomial k r.1 // Irreducible G.toPolynomial},
        ∑ a ∈ Finset.range (cutoff / r.1 + 1),
          Polynomial.monomial (a * r.1) (W r.1 G.1 ^ a)) =
      ∏ x : (Σ r : {r : ℕ // r ∈ Finset.Icc 1 cutoff},
        {G : MonicDegreePolynomial k r.1 // Irreducible G.toPolynomial}),
          ∑ a ∈ Finset.range (cutoff / x.1.1 + 1),
            Polynomial.monomial (a * x.1.1) (W x.1.1 x.2.1 ^ a) :=
        (Fintype.prod_sigma (fun x : (Σ r : {r : ℕ // r ∈ Finset.Icc 1 cutoff},
          {G : MonicDegreePolynomial k r.1 // Irreducible G.toPolynomial}) ↦
            ∑ a ∈ Finset.range (cutoff / x.1.1 + 1),
              Polynomial.monomial (a * x.1.1) (W x.1.1 x.2.1 ^ a))).symm
    _ = primeEulerProduct (fun i : EulerPrime k cutoff ↦ W i.degree i.encoding) := by
      rw [primeEulerProduct]
      apply Fintype.prod_equiv iteratedEulerPrimeEquiv _ _
      intro x
      simp only [iteratedEulerPrimeEquiv, primeEulerFactor, EulerPrime.degree,
        EulerPrime.encoding]
      symm
      exact Fin.sum_univ_eq_sum_range
        (fun a ↦ Polynomial.monomial (a * x.1.1) (W x.1.1 x.2.1 ^ a))
        (cutoff / x.1.1 + 1)

private noncomputable def selectionFactorPolynomials
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (e : EulerSelection k cutoff) : Multiset (Polynomial k) :=
  ∑ i : EulerPrime k cutoff,
    Multiset.replicate (e i).1 i.toPolynomial

private theorem normalizedFactors_selectionPolynomial
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (e : EulerSelection k cutoff) :
    UniqueFactorizationMonoid.normalizedFactors (selectionPolynomial e) =
      selectionFactorPolynomials e := by
  classical
  ext P
  rw [← factorization_eq_count, factorization_selectionPolynomial,
    Finsupp.finsetSum_apply]
  rw [selectionFactorPolynomials]
  induction (Finset.univ : Finset (EulerPrime k cutoff)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      conv_rhs => rw [Finset.sum_insert hi]
      rw [Multiset.count_add, Multiset.count_replicate, ih]
      rw [Finsupp.smul_single]
      simp only [nsmul_eq_mul, mul_one, Finsupp.single_apply]
      by_cases h : i.toPolynomial = P <;> simp [h]

private noncomputable def EulerPrime.monicPolynomial
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (i : EulerPrime k cutoff) : MonicPolynomial k :=
  ⟨i.toPolynomial, i.toPolynomial_monic⟩

private noncomputable def selectionFactorMonics
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
  (e : EulerSelection k cutoff) : Multiset (MonicPolynomial k) :=
  ∑ i : EulerPrime k cutoff,
    Multiset.replicate (e i).1 i.monicPolynomial

private noncomputable def selectionMonicPolynomial
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (e : EulerSelection k cutoff) : MonicPolynomial k :=
  ⟨selectionPolynomial e, selectionPolynomial_monic e⟩

set_option backward.isDefEq.respectTransparency false in
private theorem normalizedIrreducibleFactors_selectionPolynomial
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
  (e : EulerSelection k cutoff) :
    (selectionMonicPolynomial e).normalizedIrreducibleFactors =
      selectionFactorMonics e := by
  classical
  apply Multiset.map_injective Subtype.val_injective
  unfold MonicPolynomial.normalizedIrreducibleFactors
  rw [Multiset.map_map]
  change Multiset.map Subtype.val
    (UniqueFactorizationMonoid.normalizedFactors (selectionPolynomial e)).attach = _
  rw [Multiset.attach_map_val]
  rw [normalizedFactors_selectionPolynomial]
  rw [selectionFactorPolynomials, selectionFactorMonics]
  induction (Finset.univ : Finset (EulerPrime k cutoff)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Multiset.map_add,
        Multiset.map_replicate, ih]
      rfl

set_option backward.isDefEq.respectTransparency false in
private theorem selection_weight_product
    {k : Type*} [Field k] [Fintype k] {cutoff : ℕ}
    (psi : AddChar k ℂ) (f : Polynomial k) (e : EulerSelection k cutoff) :
    monicPolynomialWeight psi f (selectionMonicPolynomial e) =
      ∏ i : EulerPrime k cutoff,
        monicWeight psi f i.encoding ^ (e i).1 := by
  rw [monicWeight_eq_prod_normalizedIrreducibleFactors,
    normalizedIrreducibleFactors_selectionPolynomial]
  rw [selectionFactorMonics]
  induction (Finset.univ : Finset (EulerPrime k cutoff)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Multiset.map_add, Multiset.prod_add,
        Multiset.map_replicate, Multiset.prod_replicate, Finset.prod_insert hi, ih]
      have hencoding : HEq i.monicPolynomial.encoding i.encoding := by
        apply MonicDegreePolynomial.heq_of_toPolynomial_eq
        exact calc
          i.monicPolynomial.encoding.toPolynomial =
              i.monicPolynomial.1 :=
            MonicPolynomial.encoding_toPolynomial i.monicPolynomial
          _ = i.encoding.toPolynomial := rfl
      have hindex : i.monicPolynomial.1.natDegree = i.degree :=
        i.toPolynomial_natDegree
      have hsigma :
            (⟨i.monicPolynomial.1.natDegree, i.monicPolynomial.encoding⟩ :
              Σ n, MonicDegreePolynomial k n) =
            ⟨i.degree, i.encoding⟩ :=
        Sigma.ext_iff.mpr ⟨hindex, hencoding⟩
      have hpower := congrArg
        (fun z : Σ n, MonicDegreePolynomial k n ↦
          sigmaMonicWeight psi f z ^ (e i).1) hsigma
      change
        sigmaMonicWeight psi f
            ⟨i.monicPolynomial.1.natDegree, i.monicPolynomial.encoding⟩ ^ (e i).1 * _ =
          sigmaMonicWeight psi f ⟨i.degree, i.encoding⟩ ^ (e i).1 * _
      rw [hpower]

set_option backward.isDefEq.respectTransparency false in
private theorem monicPolynomialWeight_eq_monicWeight_of_polynomial_eq
    {k : Type*} [Field k] (psi : AddChar k ℂ) (f : Polynomial k)
    (P : MonicPolynomial k) {n : ℕ} (A : MonicDegreePolynomial k n)
    (h : P.1 = A.toPolynomial) :
    monicPolynomialWeight psi f P = monicWeight psi f A := by
  have hencoding : HEq P.encoding A := by
    apply MonicDegreePolynomial.heq_of_toPolynomial_eq
    exact (MonicPolynomial.encoding_toPolynomial P).trans h
  have hindex : P.1.natDegree = n := by
    rw [h, A.toPolynomial_natDegree]
  have hsigma :
      (⟨P.1.natDegree, P.encoding⟩ : Σ m, MonicDegreePolynomial k m) =
        ⟨n, A⟩ := Sigma.ext_iff.mpr ⟨hindex, hencoding⟩
  change sigmaMonicWeight psi f ⟨P.1.natDegree, P.encoding⟩ =
    sigmaMonicWeight psi f ⟨n, A⟩
  exact congrArg (sigmaMonicWeight psi f) hsigma

private theorem nestedEulerProduct_coeff_eq_artinCoefficient
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (cutoff : ℕ)
    {n : ℕ} (hn : n ≤ cutoff) :
    (nestedEulerProduct cutoff (fun _r G ↦ monicWeight psi f G)).coeff n =
      artinCoefficient psi f n := by
  rw [nestedEulerProduct_eq_primeEulerProduct, primeEulerProduct_coeff,
    artinCoefficient]
  apply Fintype.sum_equiv (selectionEquivMonicDegree hn) _ _
  intro e
  rw [← selection_weight_product psi f e.1]
  apply monicPolynomialWeight_eq_monicWeight_of_polynomial_eq
  change selectionPolynomial e.1 =
    (selectionEquivMonicDegree hn e).toPolynomial
  symm
  have hdegree : (selectionPolynomial e.1).natDegree = n := by
    rw [selectionPolynomial_natDegree, e.2]
  change (MonicDegreePolynomial.ofPolynomial (selectionPolynomial e.1)
    (selectionPolynomial_monic e.1) hdegree).toPolynomial = selectionPolynomial e.1
  exact MonicDegreePolynomial.toPolynomial_ofPolynomial
    (selectionPolynomial e.1) (selectionPolynomial_monic e.1) hdegree

/-- Coefficients of the finite Euler product equal the Artin coefficients through the truncation
range. -/
theorem truncatedEulerProduct_coeff
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (cutoff : ℕ)
    {n : ℕ} (hn : n ≤ cutoff) :
    (truncatedEulerProduct psi f cutoff).coeff n =
      artinCoefficient psi f n := by
  change (nestedEulerProduct cutoff
    (fun _r G ↦ monicWeight psi f G)).coeff n = _
  exact nestedEulerProduct_coeff_eq_artinCoefficient psi f cutoff hn

private noncomputable def geometricEulerFactor
    (w : ℂ) (cutoff r : ℕ) : Polynomial ℂ :=
  ∑ a ∈ Finset.range (cutoff / r + 1),
    Polynomial.monomial (a * r) (w ^ a)

private noncomputable def geometricMarkedFactor
    (w : ℂ) (cutoff r : ℕ) : Polynomial ℂ :=
  ∑ b ∈ Finset.Icc 1 (cutoff / r),
    Polynomial.monomial (b * r) ((r : ℂ) * w ^ b)

private theorem geometricEulerFactor_coeff
    (w : ℂ) (cutoff : ℕ) {r : ℕ} (hr : 0 < r) (n : ℕ) :
    (geometricEulerFactor w cutoff r).coeff n =
      if _h : r ∣ n ∧ n / r ≤ cutoff / r then w ^ (n / r) else 0 := by
  classical
  rw [geometricEulerFactor, Polynomial.finsetSum_coeff]
  by_cases h : r ∣ n ∧ n / r ≤ cutoff / r
  · rw [dif_pos h, Finset.sum_eq_single (n / r)]
    · rw [Polynomial.coeff_monomial, if_pos]
      exact Nat.div_mul_cancel h.1
    · intro b _hb hbn
      rw [Polynomial.coeff_monomial, if_neg]
      intro hbr
      have : b = n / r := by
        apply Nat.mul_right_cancel hr
        rw [hbr, Nat.div_mul_cancel h.1]
      exact hbn this
    · intro hnmem
      exact (hnmem (Finset.mem_range.mpr (by omega))).elim
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Polynomial.coeff_monomial, if_neg]
    intro hbr
    apply h
    constructor
    · exact ⟨b, by simpa [Nat.mul_comm] using hbr.symm⟩
    · have hb' := Finset.mem_range.mp hb
      have hbn : n / r = b := by
        rw [← hbr, Nat.mul_div_cancel b hr]
      omega

private theorem X_derivative_geometricEulerFactor_coeff
    (w : ℂ) (cutoff : ℕ) {r n : ℕ} (hr : 0 < r) :
    (Polynomial.X * (geometricEulerFactor w cutoff r).derivative).coeff n =
      if _h : r ∣ n ∧ n / r ≤ cutoff / r
      then (n : ℂ) * w ^ (n / r) else 0 := by
  rcases n with _ | n
  · simp
  rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
    geometricEulerFactor_coeff w cutoff hr]
  by_cases h : r ∣ n.succ ∧ n.succ / r ≤ cutoff / r
  · rw [dif_pos h, dif_pos (by simpa [Nat.succ_eq_add_one] using h)]
    push_cast
    ring
  · rw [dif_neg h, dif_neg (by simpa [Nat.succ_eq_add_one] using h)]
    simp

private theorem geometricMarkedFactor_coeff
    (w : ℂ) (cutoff : ℕ) {r : ℕ} (hr : 0 < r) (n : ℕ) :
    (geometricMarkedFactor w cutoff r).coeff n =
      if _h : r ∣ n ∧ 1 ≤ n / r ∧ n / r ≤ cutoff / r
      then (r : ℂ) * w ^ (n / r) else 0 := by
  classical
  rw [geometricMarkedFactor, Polynomial.finsetSum_coeff]
  by_cases h : r ∣ n ∧ 1 ≤ n / r ∧ n / r ≤ cutoff / r
  · rw [dif_pos h, Finset.sum_eq_single (n / r)]
    · rw [Polynomial.coeff_monomial, if_pos]
      exact Nat.div_mul_cancel h.1
    · intro b _hb hbn
      rw [Polynomial.coeff_monomial, if_neg]
      intro hbr
      have : b = n / r := by
        apply Nat.mul_right_cancel hr
        rw [hbr, Nat.div_mul_cancel h.1]
      exact hbn this
    · intro hnmem
      exact (hnmem (Finset.mem_Icc.mpr ⟨h.2.1, h.2.2⟩)).elim
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Polynomial.coeff_monomial, if_neg]
    intro hbr
    apply h
    have hb' := Finset.mem_Icc.mp hb
    constructor
    · exact ⟨b, by simpa [Nat.mul_comm] using hbr.symm⟩
    · have hbn : n / r = b := by
        rw [← hbr, Nat.mul_div_cancel b hr]
      omega

private theorem geometricFactor_mul_marked_coeff_expand
    (w : ℂ) (cutoff r n : ℕ) :
    (geometricEulerFactor w cutoff r *
      geometricMarkedFactor w cutoff r).coeff n =
      ∑ a ∈ Finset.range (cutoff / r + 1),
        ∑ b ∈ Finset.Icc 1 (cutoff / r),
          if (a + b) * r = n
          then w ^ a * ((r : ℂ) * w ^ b) else 0 := by
  classical
  rw [geometricEulerFactor, geometricMarkedFactor, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Polynomial.monomial_mul_monomial, Polynomial.coeff_monomial]
  simp only [add_mul]

private theorem inner_geometricFactor_sum
    (w : ℂ) {A c b r n : ℕ} (hr : 0 < r)
    (hn : n = c * r) (hcA : c ≤ A) :
    (∑ a ∈ Finset.range (A + 1),
      if (a + b) * r = n
      then w ^ a * ((r : ℂ) * w ^ b) else 0) =
      if b ≤ c then (r : ℂ) * w ^ c else 0 := by
  classical
  by_cases hbc : b ≤ c
  · rw [if_pos hbc, Finset.sum_eq_single (c - b)]
    · rw [if_pos]
      · calc
          w ^ (c - b) * ((r : ℂ) * w ^ b) =
              (r : ℂ) * (w ^ (c - b) * w ^ b) := by ring
          _ = (r : ℂ) * w ^ c := by
            rw [← pow_add, Nat.sub_add_cancel hbc]
      · rw [hn, Nat.sub_add_cancel hbc]
    · intro a _ha hacb
      rw [if_neg]
      intro han
      have hab : a + b = c := by
        apply Nat.mul_right_cancel hr
        simpa only [hn] using han
      exact hacb (by omega)
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg hbc]
    apply Finset.sum_eq_zero
    intro a _ha
    rw [if_neg]
    intro han
    have hab : a + b = c := by
      apply Nat.mul_right_cancel hr
      simpa only [hn] using han
    omega

private theorem double_geometricFactor_sum
    (w : ℂ) {A c r n : ℕ} (hr : 0 < r)
    (hn : n = c * r) (hcA : c ≤ A) :
    (∑ a ∈ Finset.range (A + 1),
      ∑ b ∈ Finset.Icc 1 A,
        if (a + b) * r = n
        then w ^ a * ((r : ℂ) * w ^ b) else 0) =
      (n : ℂ) * w ^ c := by
  rw [Finset.sum_comm]
  simp_rw [inner_geometricFactor_sum w hr hn hcA]
  rw [← Finset.sum_filter]
  have hfilter : {b ∈ Finset.Icc 1 A | b ≤ c} = Finset.Icc 1 c := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilter]
  simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
  rw [hn]
  push_cast
  ring

private theorem geometricFactor_mul_marked_coeff
    (w : ℂ) (cutoff : ℕ) {r n : ℕ}
    (hr : 0 < r) (hn : n ≤ cutoff) :
    (geometricEulerFactor w cutoff r *
      geometricMarkedFactor w cutoff r).coeff n =
      if _h : r ∣ n ∧ 1 ≤ n / r
      then (n : ℂ) * w ^ (n / r) else 0 := by
  rw [geometricFactor_mul_marked_coeff_expand]
  by_cases h : r ∣ n ∧ 1 ≤ n / r
  · rw [dif_pos h]
    exact double_geometricFactor_sum w hr (Nat.div_mul_cancel h.1).symm
      (Nat.div_le_div_right hn)
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro a _ha
    apply Finset.sum_eq_zero
    intro b hb
    rw [if_neg]
    intro hab
    apply h
    constructor
    · exact ⟨a + b, by simpa [Nat.mul_comm] using hab.symm⟩
    · have hbpos : 0 < b := (Finset.mem_Icc.mp hb).1
      have hle : r ≤ n := by
        rw [← hab]
        exact Nat.le_mul_of_pos_left r (by omega)
      exact Nat.div_pos hle hr

private theorem geometricFactor_logDerivative_coeff
    (w : ℂ) (cutoff : ℕ) {r n : ℕ}
    (hr : 0 < r) (hn : n ≤ cutoff) :
    (Polynomial.X * (geometricEulerFactor w cutoff r).derivative).coeff n =
      (geometricEulerFactor w cutoff r *
        geometricMarkedFactor w cutoff r).coeff n := by
  rw [X_derivative_geometricEulerFactor_coeff w cutoff hr,
    geometricFactor_mul_marked_coeff w cutoff hr hn]
  by_cases h0 : n = 0
  · subst n
    simp
  by_cases hd : r ∣ n
  · have hle : n / r ≤ cutoff / r := Nat.div_le_div_right hn
    have hpos : 1 ≤ n / r := by
      exact Nat.one_le_iff_ne_zero.mpr (by
        intro hz
        have h := Nat.div_mul_cancel hd
        rw [hz, zero_mul] at h
        exact h0 h.symm)
    simp [hd, hle, hpos]
  · simp [hd]

private theorem coeff_mul_congr_le
    (Q A B : Polynomial ℂ) {n : ℕ}
    (h : ∀ j ≤ n, A.coeff j = B.coeff j) :
    (Q * A).coeff n = (Q * B).coeff n := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [h ij.2]
  have hs := Finset.mem_antidiagonal.mp hij
  omega

private theorem finsetProd_logDerivative_coeff
    {ι : Type*}
    (s : Finset ι) (F H : ι → Polynomial ℂ) (cutoff : ℕ)
    (hloc : ∀ i ∈ s, ∀ n ≤ cutoff,
      (Polynomial.X * (F i).derivative).coeff n =
        (F i * H i).coeff n)
    {n : ℕ} (hn : n ≤ cutoff) :
    (Polynomial.X * (∏ i ∈ s, F i).derivative).coeff n =
      ((∏ i ∈ s, F i) * (∑ i ∈ s, H i)).coeff n := by
  classical
  have hleft :
      Polynomial.X * (∏ i ∈ s, F i).derivative =
        ∑ i ∈ s, (∏ j ∈ s.erase i, F j) *
          (Polynomial.X * (F i).derivative) := by
    rw [Polynomial.derivative_prod_finset, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hright :
      (∏ i ∈ s, F i) * (∑ i ∈ s, H i) =
        ∑ i ∈ s, (∏ j ∈ s.erase i, F j) * (F i * H i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, Finset.prod_erase_mul _ _ hi]
  rw [hleft, hright, Polynomial.finsetSum_coeff,
    Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  apply coeff_mul_congr_le
  intro j hj
  exact hloc i hi j (hj.trans hn)

/-- The logarithmic derivative identity for the truncated Euler product, valid coefficientwise up
to the cutoff. -/
theorem truncatedEulerProduct_logDerivative_coeff
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (cutoff : ℕ)
    {n : ℕ} (hn : n ≤ cutoff) :
    (Polynomial.X *
      (truncatedEulerProduct psi f cutoff).derivative).coeff n =
    (truncatedEulerProduct psi f cutoff *
      markedFactorPolynomial psi f cutoff).coeff n := by
  classical
  let F : (r : ℕ) → MonicDegreePolynomial k r → Polynomial ℂ :=
    fun r G ↦ if Irreducible G.toPolynomial then
      truncatedEulerFactor psi f cutoff r G else 1
  let H : (r : ℕ) → MonicDegreePolynomial k r → Polynomial ℂ :=
    fun r G ↦ if Irreducible G.toPolynomial then
      geometricMarkedFactor (monicWeight psi f G) cutoff r else 0
  let PF : ℕ → Polynomial ℂ := fun r ↦ ∏ G, F r G
  let MH : ℕ → Polynomial ℂ := fun r ↦ ∑ G, H r G
  let Htot : Polynomial ℂ := ∑ r ∈ Finset.Icc 1 cutoff, MH r
  have hfactor (r : ℕ) (hr : r ∈ Finset.Icc 1 cutoff)
      (G : MonicDegreePolynomial k r) (j : ℕ) (hj : j ≤ cutoff) :
      (Polynomial.X * (F r G).derivative).coeff j =
        (F r G * H r G).coeff j := by
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    by_cases hG : Irreducible G.toPolynomial
    · simp only [F, H, if_pos hG, truncatedEulerFactor]
      exact geometricFactor_logDerivative_coeff
        (monicWeight psi f G) cutoff hrpos hj
    · simp [F, H, hG]
  have hinner (r : ℕ) (hr : r ∈ Finset.Icc 1 cutoff)
      (j : ℕ) (hj : j ≤ cutoff) :
      (Polynomial.X * (PF r).derivative).coeff j =
        (PF r * MH r).coeff j := by
    exact finsetProd_logDerivative_coeff Finset.univ (F r) (H r) cutoff
      (fun G _hG j hj ↦ hfactor r hr G j hj) hj
  have houter :
      (Polynomial.X * (∏ r ∈ Finset.Icc 1 cutoff, PF r).derivative).coeff n =
        ((∏ r ∈ Finset.Icc 1 cutoff, PF r) * Htot).coeff n := by
    exact finsetProd_logDerivative_coeff (Finset.Icc 1 cutoff) PF MH cutoff
      (fun r hr j hj ↦ hinner r hr j hj) hn
  have hHcoeff (j : ℕ) (hj : j ≤ cutoff) :
      Htot.coeff j = (markedFactorPolynomial psi f cutoff).coeff j := by
    by_cases hj0 : j = 0
    · subst j
      have hleft : Htot.coeff 0 = 0 := by
        change (∑ r ∈ Finset.Icc 1 cutoff, MH r).coeff 0 = 0
        rw [Polynomial.finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro r hr
        change (∑ G, H r G).coeff 0 = 0
        rw [Polynomial.finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro G _hG
        by_cases hGirr : Irreducible G.toPolynomial
        · simp only [H, if_pos hGirr, geometricMarkedFactor,
            Polynomial.finsetSum_coeff]
          apply Finset.sum_eq_zero
          intro b hb
          rw [Polynomial.coeff_monomial, if_neg]
          have hrpos := (Finset.mem_Icc.mp hr).1
          have hbpos := (Finset.mem_Icc.mp hb).1
          exact (Nat.mul_pos hbpos hrpos).ne'
        · simp [H, hGirr]
      have hright :
          (markedFactorPolynomial psi f cutoff).coeff 0 = 0 := by
        rw [markedFactorPolynomial, Polynomial.finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro a ha
        rw [Polynomial.coeff_monomial, if_neg]
        exact (Nat.lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp ha).1).ne'
      exact hleft.trans hright.symm
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hmarked :
        (markedFactorPolynomial psi f cutoff).coeff j =
          markedFactorSum psi f j := by
      rw [markedFactorPolynomial, Polynomial.finsetSum_coeff,
        Finset.sum_eq_single j]
      · simp
      · intro a _ha haj
        rw [Polynomial.coeff_monomial, if_neg haj]
      · intro hnot
        exact (hnot (Finset.mem_Icc.mpr ⟨hjpos, hj⟩)).elim
    rw [hmarked]
    change (∑ r ∈ Finset.Icc 1 cutoff, MH r).coeff j =
      markedFactorSum psi f j
    rw [Polynomial.finsetSum_coeff, markedFactorSum]
    have hlocal (r : ℕ) (hr : r ∈ Finset.Icc 1 cutoff) :
        (MH r).coeff j =
          if r ∣ j then
            ∑ G : MonicDegreePolynomial k r,
              if Irreducible G.toPolynomial then
                (r : ℂ) * monicWeight psi f G ^ (j / r)
              else 0
          else 0 := by
      have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
      change (∑ G, H r G).coeff j = _
      rw [Polynomial.finsetSum_coeff]
      by_cases hd : r ∣ j
      · rw [if_pos hd]
        apply Finset.sum_congr rfl
        intro G _hG
        by_cases hGirr : Irreducible G.toPolynomial
        · simp only [H, if_pos hGirr]
          rw [geometricMarkedFactor_coeff
            (monicWeight psi f G) cutoff hrpos]
          rw [dif_pos ⟨hd, Nat.one_le_iff_ne_zero.mpr (by
            intro hz
            have h := Nat.div_mul_cancel hd
            rw [hz, zero_mul] at h
            exact hj0 h.symm), Nat.div_le_div_right hj⟩]
        · simp [H, hGirr]
      · rw [if_neg hd]
        apply Finset.sum_eq_zero
        intro G _hG
        by_cases hGirr : Irreducible G.toPolynomial
        · simp only [H, if_pos hGirr]
          rw [geometricMarkedFactor_coeff
            (monicWeight psi f G) cutoff hrpos, dif_neg]
          exact fun h ↦ hd h.1
        · simp [H, hGirr]
    have hsumlocal :
        (∑ r ∈ Finset.Icc 1 cutoff, (MH r).coeff j) =
          ∑ r ∈ Finset.Icc 1 cutoff,
            if r ∣ j then
              ∑ G : MonicDegreePolynomial k r,
                if Irreducible G.toPolynomial then
                  (r : ℂ) * monicWeight psi f G ^ (j / r)
                else 0
            else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hlocal r hr
    rw [hsumlocal]
    rw [← Finset.sum_filter]
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hrone, _hrcut⟩, hrdiv⟩
      exact ⟨⟨hrone, Nat.le_of_dvd hjpos hrdiv⟩, hrdiv⟩
    · rintro ⟨⟨hrone, hrj⟩, hrdiv⟩
      exact ⟨⟨hrone, hrj.trans hj⟩, hrdiv⟩
  have hdef :
      (∏ r ∈ Finset.Icc 1 cutoff, PF r) =
        truncatedEulerProduct psi f cutoff := by
    rfl
  rw [hdef] at houter
  exact houter.trans
    (coeff_mul_congr_le (truncatedEulerProduct psi f cutoff) Htot
      (markedFactorPolynomial psi f cutoff)
      (fun j hj ↦ hHcoeff j (hj.trans hn)))

/-- The degree-zero Artin coefficient is one. -/
theorem artinCoefficient_zero
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) :
    artinCoefficient psi f 0 = 1 :=
  artinCoefficient_zero_aux psi f

/-- At cutoff zero the truncated Euler product is one. -/
theorem truncatedEulerProduct_zero
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) :
    truncatedEulerProduct psi f 0 = 1 := by
  classical
  simp [truncatedEulerProduct]

/-- Additive character on a finite extension obtained by composing with the field trace. -/
noncomputable def traceLiftAddChar
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (n : ℕ) :
    AddChar (GaloisField p n) ℂ :=
  psi.compAddMonoidHom
    (Algebra.trace (ZMod p) (GaloisField p n)).toAddMonoidHom

/-- Complete additive exponential sum of `f` over the degree-`m` finite-field extension. -/
noncomputable def extensionExponentialSum
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p))
    (n : ℕ) : ℂ := by
  letI := Fintype.ofFinite (GaloisField p n)
  exact ∑ x : GaloisField p n,
    traceLiftAddChar psi n
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x)

/-- The extension sum in degree one is the complete sum over the prime field. -/
theorem extensionExponentialSum_one_eq_primeSum
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    extensionExponentialSum psi f 1 =
      ∑ x : ZMod p, psi (f.eval x) := by
  classical
  let _ := Fintype.ofFinite (GaloisField p 1)
  let e := GaloisField.equivZmodP p
  rw [extensionExponentialSum]
  refine Fintype.sum_equiv e.toEquiv _ _ fun x ↦ ?_
  change psi (Algebra.trace (ZMod p) (GaloisField p 1)
    (f.eval₂ (algebraMap (ZMod p) (GaloisField p 1)) x)) =
      psi (f.eval (e x))
  congr 1
  rw [← Algebra.trace_eq_of_algEquiv e]
  rw [Algebra.trace_self_apply]
  simpa [Polynomial.aeval_def] using
    (Polynomial.aeval_algHom_apply e x f).symm

/-- Removing the constant coefficient from `f` multiplies the extension sum by the corresponding
character phase. -/
theorem extensionExponentialSum_eraseConstant
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p))
    {n : ℕ} (hn : n ≠ 0) :
    extensionExponentialSum psi f n =
      constantTwist psi f ^ n *
        extensionExponentialSum psi (eraseConstant f) n := by
  classical
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite _
  rw [extensionExponentialSum, extensionExponentialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  change psi (Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x)) =
    psi (f.coeff 0) ^ n *
      psi (Algebra.trace (ZMod p) (GaloisField p n)
        ((eraseConstant f).eval₂
          (algebraMap (ZMod p) (GaloisField p n)) x))
  rw [← AddChar.map_nsmul_eq_pow, ← psi.map_add_eq_mul]
  congr 1
  have hf : f = Polynomial.C (f.coeff 0) + eraseConstant f := by
    simp [eraseConstant]
  have heval :
      f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x =
        algebraMap (ZMod p) (GaloisField p n) (f.coeff 0) +
          (eraseConstant f).eval₂
            (algebraMap (ZMod p) (GaloisField p n)) x := by
    calc
      f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x =
          (Polynomial.C (f.coeff 0) + eraseConstant f).eval₂
            (algebraMap (ZMod p) (GaloisField p n)) x :=
        congrArg (fun P : Polynomial (ZMod p) ↦
          P.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) hf
      _ = _ := by rw [Polynomial.eval₂_add, Polynomial.eval₂_C]
  rw [heval, map_add,
    Algebra.trace_algebraMap, GaloisField.finrank p hn]

/-- Elements of a finite extension having a prescribed monic minimal polynomial. -/
noncomputable def minpolyFiber
    {p : ℕ} [Fact p.Prime] (m : ℕ)
    (G : Polynomial (ZMod p)) : Finset (GaloisField p m) := by
  letI := Fintype.ofFinite (GaloisField p m)
  classical
  exact Finset.univ.filter fun x ↦ minpoly (ZMod p) x = G

/-- Encodes an extension element by its monic minimal polynomial over the base field. -/
noncomputable def minpolyEncoding
    {p m : ℕ} [Fact p.Prime] (x : GaloisField p m) :
    MonicDegreePolynomial (ZMod p)
      (minpoly (ZMod p) x).natDegree :=
  (monicEncodingEquiv (ZMod p) (minpoly (ZMod p) x).natDegree).symm
    ⟨minpoly (ZMod p) x,
      minpoly.monic (Algebra.IsIntegral.isIntegral x), rfl⟩

private theorem minpoly_eq_iff_aeval_eq_zero_of_monic_irreducible
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (G : Polynomial K) (hGmonic : G.Monic) (hGirr : Irreducible G)
    (x : L) : minpoly K x = G ↔ Polynomial.aeval x G = 0 := by
  constructor
  · intro h
    rw [← h]
    exact minpoly.aeval K x
  · intro hx
    have h := minpoly.Irreducible.eq_minpoly hGirr hx
    have hlc : G.leadingCoeff = 1 := hGmonic.leadingCoeff
    simpa [hlc] using h.symm

private theorem irreducible_splits_galoisField_of_natDegree_dvd
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (G : Polynomial (ZMod p)) (hGirr : Irreducible G)
    (hdiv : G.natDegree ∣ m) :
    (G.map (algebraMap (ZMod p) (GaloisField p m))).Splits := by
  let _ : Fintype (GaloisField p m) := Fintype.ofFinite _
  have hGdiv :=
    (Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X hGirr).mp hdiv
  rw [Nat.card_zmod] at hGdiv
  have hbig := FiniteField.splits_X_pow_card_sub_X
    (p := p) (K := GaloisField p m)
  rw [Fintype.card_eq_nat_card, GaloisField.card p m hm] at hbig
  apply hbig.of_dvd
  · exact map_ne_zero
      (FiniteField.X_pow_card_pow_sub_X_ne_zero (ZMod p) hm
        (Fact.out : p.Prime).one_lt)
  · exact Polynomial.map_dvd _ hGdiv

/-- A monic irreducible polynomial has a root in the degree-`m` extension exactly when its degree
divides `m`. -/
theorem minpolyFiber_nonempty_iff_natDegree_dvd
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (G : Polynomial (ZMod p))
    (hGmonic : G.Monic) (hGirr : Irreducible G) :
    (minpolyFiber m G).Nonempty ↔ G.natDegree ∣ m := by
  constructor
  · rintro ⟨x, hx⟩
    have hmin : minpoly (ZMod p) x = G := by
      simpa [minpolyFiber] using hx
    have hd := minpoly.degree_dvd (K := ZMod p)
      (L := GaloisField p m) (Algebra.IsIntegral.isIntegral x)
    rw [GaloisField.finrank p hm] at hd
    simpa only [hmin] using hd
  · intro hdiv
    let phi : ZMod p →+* GaloisField p m := algebraMap _ _
    have hsplit := irreducible_splits_galoisField_of_natDegree_dvd hm G hGirr hdiv
    have hdegree : (G.map phi).degree ≠ 0 := by
      rw [G.degree_map phi]
      exact hGirr.degree_pos.ne'
    obtain ⟨x, hx⟩ := hsplit.exists_eval_eq_zero hdegree
    rw [Polynomial.eval_map_algebraMap] at hx
    have hmin :=
      (minpoly_eq_iff_aeval_eq_zero_of_monic_irreducible G hGmonic hGirr x).2 hx
    refine ⟨x, ?_⟩
    simp [minpolyFiber, hmin]

private theorem minpolyFiber_coe_eq_rootSet
    {p m : ℕ} [Fact p.Prime]
    (G : Polynomial (ZMod p))
    (hGmonic : G.Monic) (hGirr : Irreducible G) :
    (↑(minpolyFiber m G) : Set (GaloisField p m)) =
      G.rootSet (GaloisField p m) := by
  ext x
  rw [Polynomial.mem_rootSet]
  simp only [minpolyFiber, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [minpoly_eq_iff_aeval_eq_zero_of_monic_irreducible G hGmonic hGirr x]
  simp [hGirr.ne_zero]

/-- A nonempty minimal-polynomial fiber has cardinality equal to the polynomial degree. -/
theorem card_minpolyFiber
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (G : Polynomial (ZMod p))
    (hGmonic : G.Monic) (hGirr : Irreducible G) :
    (minpolyFiber m G).card =
      if G.natDegree ∣ m then G.natDegree else 0 := by
  classical
  by_cases hdiv : G.natDegree ∣ m
  · rw [if_pos hdiv]
    have hsplit := irreducible_splits_galoisField_of_natDegree_dvd hm G hGirr hdiv
    have hsep : G.Separable := PerfectField.separable_of_irreducible hGirr
    have hset := minpolyFiber_coe_eq_rootSet (m := m) G hGmonic hGirr
    calc
      (minpolyFiber m G).card = Fintype.card (minpolyFiber m G) := by
        rw [Fintype.card_coe]
      _ = Fintype.card (G.rootSet (GaloisField p m)) :=
        Fintype.card_congr (Equiv.setCongr hset)
      _ = G.natDegree := Polynomial.card_rootSet_eq_natDegree hsep hsplit
  · rw [if_neg hdiv]
    exact Finset.card_eq_zero.mpr (by
      apply Finset.not_nonempty_iff_eq_empty.mp
      simpa [minpolyFiber_nonempty_iff_natDegree_dvd hm G hGmonic hGirr] using hdiv)

/-- The fiber of a minimal polynomial is precisely the Frobenius orbit of any chosen root. -/
theorem minpolyFiber_eq_galoisOrbit
    {p m : ℕ} [Fact p.Prime] (_hm : m ≠ 0)
    (x : GaloisField p m) :
    ↑(minpolyFiber m (minpoly (ZMod p) x)) =
      MulAction.orbit
        (GaloisField p m ≃ₐ[ZMod p] GaloisField p m) x := by
  ext y
  simp only [minpolyFiber, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact Normal.minpoly_eq_iff_mem_orbit
    (F := ZMod p) (E := GaloisField p m) (x := y) (y := x)

private theorem galoisFrobenius_pow_apply
    {p m : ℕ} [Fact p.Prime]
    (i : ℕ) (x : GaloisField p m) :
    ((FiniteField.frobeniusAlgEquivOfAlgebraic
      (ZMod p) (GaloisField p m)) ^ i) x = x ^ (p ^ i) := by
  rw [AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [Fintype.card_eq_nat_card, Nat.card_zmod]

private theorem pow_prime_pow_eq_pow_mod_of_period
    {K : Type*} [CommMonoid K] (p r i : ℕ) (x : K)
    (_hr : 0 < r) (hperiod : x ^ (p ^ r) = x) :
    x ^ (p ^ i) = x ^ (p ^ (i % r)) := by
  have hblocks : ∀ q : ℕ, x ^ (p ^ (q * r)) = x := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        calc
          x ^ (p ^ ((q + 1) * r)) =
              x ^ (p ^ (q * r) * p ^ r) := by
            congr 2
            rw [← pow_add]
            congr 1
            ring
          _ = (x ^ (p ^ (q * r))) ^ (p ^ r) := by rw [pow_mul]
          _ = x ^ (p ^ r) := by rw [ih]
          _ = x := hperiod
  have hi : i = (i / r) * r + i % r := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod i r).symm
  calc
    x ^ (p ^ i) = x ^ (p ^ ((i / r) * r + i % r)) :=
      congrArg (fun e ↦ x ^ (p ^ e)) hi
    _ = x ^ (p ^ ((i / r) * r) * p ^ (i % r)) := by rw [pow_add]
    _ = (x ^ (p ^ ((i / r) * r))) ^ (p ^ (i % r)) := by rw [pow_mul]
    _ = x ^ (p ^ (i % r)) := by rw [hblocks]

private theorem frobeniusRange_image_eq_minpolyFiber
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (x : GaloisField p m) :
    {y : GaloisField p m | ∃ i < (minpoly (ZMod p) x).natDegree,
        x ^ (p ^ i) = y} =
      ↑(minpolyFiber m (minpoly (ZMod p) x)) := by
  classical
  let G := minpoly (ZMod p) x
  let r := G.natDegree
  have hGirr : Irreducible G := minpoly.irreducible
    (Algebra.IsIntegral.isIntegral x)
  have hr : 0 < r := hGirr.natDegree_pos
  have hGdivPoly : G ∣
      Polynomial.X ^ (Nat.card (ZMod p)) ^ r - Polynomial.X :=
    (Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X hGirr).mp dvd_rfl
  have hxzero : Polynomial.aeval x
      (Polynomial.X ^ (Nat.card (ZMod p)) ^ r - Polynomial.X) = 0 :=
    (hGirr.dvd_iff_aeval_eq_zero
      (by simpa only [G] using minpoly.aeval (ZMod p) x)).2 hGdivPoly
  have hperiod : x ^ (p ^ r) = x := by
    rw [Nat.card_zmod] at hxzero
    exact sub_eq_zero.mp (by simpa [Polynomial.aeval_def] using hxzero)
  ext y
  constructor
  · intro hy
    rcases hy with ⟨i, hi, rfl⟩
    have hmin := minpoly.algEquiv_eq
      ((FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod p) (GaloisField p m)) ^ i) x
    rw [galoisFrobenius_pow_apply] at hmin
    simpa [minpolyFiber, G] using hmin
  · intro hy
    have hyOrbit : y ∈ MulAction.orbit
        (GaloisField p m ≃ₐ[ZMod p] GaloisField p m) x := by
      rw [← minpolyFiber_eq_galoisOrbit hm x]
      exact hy
    rcases hyOrbit with ⟨g, rfl⟩
    obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow
      (p := p) (k := ZMod p) (GaloisField p m) g
    let s := i % r
    have hs : s < r := Nat.mod_lt i hr
    refine ⟨s, hs, ?_⟩
    change x ^ (p ^ s) = g x
    rw [hi x]
    rw [Nat.card_zmod]
    exact (pow_prime_pow_eq_pow_mod_of_period p r i x hr hperiod).symm

private theorem minpolyEncoding_toPolynomial
    {p m : ℕ} [Fact p.Prime] (x : GaloisField p m) :
    (minpolyEncoding x).toPolynomial = minpoly (ZMod p) x := by
  unfold minpolyEncoding
  exact MonicDegreePolynomial.toPolynomial_ofPolynomial
    (minpoly (ZMod p) x)
    (minpoly.monic (Algebra.IsIntegral.isIntegral x)) rfl

/-- The phase attached to a minimal polynomial is the sum of `f` over the Frobenius conjugates of
a root. -/
theorem minpolyPhase_eq_sum_frobenius
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (f : Polynomial (ZMod p)) (x : GaloisField p m) :
    algebraMap (ZMod p) (GaloisField p m)
        (monicPhase f (minpolyEncoding x)) =
      ∑ i ∈ Finset.range (minpoly (ZMod p) x).natDegree,
        f.eval₂ (algebraMap (ZMod p) (GaloisField p m))
          (x ^ (p ^ i)) := by
  classical
  let phi : ZMod p →+* GaloisField p m := algebraMap _ _
  let G : Polynomial (ZMod p) := minpoly (ZMod p) x
  let r : ℕ := G.natDegree
  have hGmonic : G.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hGirr : Irreducible G :=
    minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
  have hGsep : G.Separable := PerfectField.separable_of_irreducible hGirr
  have hsplit : (G.map phi).Splits := by
    exact Normal.splits
      (inferInstance : Normal (ZMod p) (GaloisField p m)) x
  have hdiv : r ∣ m := by
    have hd := minpoly.degree_dvd (K := ZMod p)
      (L := GaloisField p m) (Algebra.IsIntegral.isIntegral x)
    rw [GaloisField.finrank p hm] at hd
    simpa only [G, r] using hd
  let orbitFinset : Finset (GaloisField p m) :=
    (Finset.range r).image fun i ↦ x ^ (p ^ i)
  have horbit : orbitFinset = minpolyFiber m G := by
    ext y
    have hset := Set.ext_iff.mp
      (frobeniusRange_image_eq_minpolyFiber hm x) y
    change (∃ i < (minpoly (ZMod p) x).natDegree,
      x ^ (p ^ i) = y) ↔ y ∈ minpolyFiber m (minpoly (ZMod p) x) at hset
    simpa only [orbitFinset, Finset.mem_image, Finset.mem_range,
      G, r] using hset
  have horbitCard : orbitFinset.card = r := by
    rw [horbit, card_minpolyFiber hm G hGmonic hGirr, if_pos hdiv]
  have hinj : Set.InjOn (fun i : ℕ ↦ x ^ (p ^ i)) (Finset.range r) := by
    apply Finset.card_image_iff.mp
    simpa only [orbitFinset, Finset.card_range] using horbitCard
  have hrootsNodup : (G.map phi).roots.Nodup := by
    exact Polynomial.nodup_roots
      (show (G.map phi).Separable from hGsep.map)
  have hrootFinset : (G.map phi).roots.toFinset = minpolyFiber m G := by
    apply Finset.ext
    intro y
    have hset := Set.ext_iff.mp
      (minpolyFiber_coe_eq_rootSet G hGmonic hGirr) y
    simpa only [Polynomial.rootSet_def, Polynomial.aroots_def, phi,
      Finset.mem_coe] using hset.symm
  have hpower (j : ℕ) :
      phi (monicPowerSum (minpolyEncoding x) j) =
        ∑ i ∈ Finset.range r, (x ^ (p ^ i)) ^ j := by
    calc
      phi (monicPowerSum (minpolyEncoding x) j) =
          (((minpolyEncoding x).toPolynomial.map phi).roots.map
            fun y ↦ y ^ j).sum :=
        monicPowerSum_eq_sum_roots (minpolyEncoding x) (by
          simpa only [minpolyEncoding_toPolynomial, G] using hsplit) j
      _ = ((G.map phi).roots.map fun y ↦ y ^ j).sum := by
        rw [minpolyEncoding_toPolynomial]
      _ = ∑ y ∈ (G.map phi).roots.toFinset, y ^ j := by
        rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
          Multiset.dedup_eq_self.mpr hrootsNodup]
      _ = ∑ y ∈ orbitFinset, y ^ j := by rw [hrootFinset, horbit]
      _ = ∑ i ∈ Finset.range r, (x ^ (p ^ i)) ^ j := by
        change (∑ y ∈ (Finset.range r).image (fun i ↦ x ^ (p ^ i)), y ^ j) = _
        rw [Finset.sum_image hinj]
  change phi (monicPhase f (minpolyEncoding x)) =
    ∑ i ∈ Finset.range r, f.eval₂ phi (x ^ (p ^ i))
  simp only [monicPhase, map_sum, map_mul]
  simp_rw [hpower]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.eval₂_eq_sum]
  rfl

private theorem minpoly_frobenius_period
    {p m : ℕ} [Fact p.Prime] (x : GaloisField p m) :
    x ^ (p ^ (minpoly (ZMod p) x).natDegree) = x := by
  let G : Polynomial (ZMod p) := minpoly (ZMod p) x
  let r := G.natDegree
  have hGirr : Irreducible G :=
    minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
  have hGdiv : G ∣
      Polynomial.X ^ (Nat.card (ZMod p)) ^ r - Polynomial.X :=
    (Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X hGirr).mp dvd_rfl
  have hxzero : Polynomial.aeval x
      (Polynomial.X ^ (Nat.card (ZMod p)) ^ r - Polynomial.X) = 0 :=
    (hGirr.dvd_iff_aeval_eq_zero
      (by simpa only [G] using minpoly.aeval (ZMod p) x)).2 hGdiv
  rw [Nat.card_zmod] at hxzero
  exact sub_eq_zero.mp (by simpa [Polynomial.aeval_def, G, r] using hxzero)

private theorem sum_range_mul_of_periodic
    {M : Type*} [AddCommMonoid M] (g : ℕ → M) (q r : ℕ)
    (hperiod : ∀ i, g (i + r) = g i) :
    (∑ i ∈ Finset.range (q * r), g i) =
      q • ∑ i ∈ Finset.range r, g i := by
  have hshift : ∀ a i : ℕ, g (a * r + i) = g i := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
        intro i
        calc
          g ((a + 1) * r + i) = g ((a * r + i) + r) := by
            congr 1
            simp only [Nat.add_mul, one_mul]
            ac_rfl
          _ = g (a * r + i) := hperiod _
          _ = g i := ih i
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, succ_nsmul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      exact hshift q i

/-- On an element with minimal polynomial `G`, the trace-lifted character equals the `m/deg G`
power of the normalized local weight. -/
theorem traceLiftAddChar_eq_minpolyWeight_pow
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (psi : AddChar (ZMod p) ℂ)
    (f : Polynomial (ZMod p)) (x : GaloisField p m) :
    traceLiftAddChar psi m
        (f.eval₂ (algebraMap (ZMod p) (GaloisField p m)) x) =
      monicWeight psi f (minpolyEncoding x) ^
        (m / (minpoly (ZMod p) x).natDegree) := by
  classical
  let phi : ZMod p →+* GaloisField p m := algebraMap _ _
  let y : GaloisField p m := f.eval₂ phi x
  let r : ℕ := (minpoly (ZMod p) x).natDegree
  have hGirr : Irreducible (minpoly (ZMod p) x) :=
    minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
  have hr : 0 < r := by
    simpa only [r] using hGirr.natDegree_pos
  have hdiv : r ∣ m := by
    have hd := minpoly.degree_dvd (K := ZMod p)
      (L := GaloisField p m) (Algebra.IsIntegral.isIntegral x)
    rw [GaloisField.finrank p hm] at hd
    simpa only [r] using hd
  have hevalFrob (i : ℕ) :
      y ^ (p ^ i) = f.eval₂ phi (x ^ (p ^ i)) := by
    have h := Polynomial.aeval_algHom_apply
      ((FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod p) (GaloisField p m)) ^ i) x f
    simp only [Polynomial.aeval_def] at h
    rw [galoisFrobenius_pow_apply i x,
      galoisFrobenius_pow_apply i
        (f.eval₂ (algebraMap (ZMod p) (GaloisField p m)) x)] at h
    simpa only [y, phi] using h.symm
  have hxperiod : x ^ (p ^ r) = x := by
    simpa only [r] using minpoly_frobenius_period x
  let g : ℕ → GaloisField p m := fun i ↦ f.eval₂ phi (x ^ (p ^ i))
  have hgperiod (i : ℕ) : g (i + r) = g i := by
    apply congrArg (f.eval₂ phi)
    calc
      x ^ (p ^ (i + r)) = x ^ (p ^ r * p ^ i) := by rw [pow_add, mul_comm]
      _ = (x ^ (p ^ r)) ^ (p ^ i) := by rw [pow_mul]
      _ = x ^ (p ^ i) := by rw [hxperiod]
  have htrace :
      Algebra.trace (ZMod p) (GaloisField p m) y =
        (m / r) • monicPhase f (minpolyEncoding x) := by
    apply (FaithfulSMul.algebraMap_injective
      (ZMod p) (GaloisField p m))
    rw [map_nsmul]
    have hformula := FiniteField.algebraMap_trace_eq_sum_pow
      (ZMod p) (GaloisField p m) y
    rw [GaloisField.finrank p hm, Nat.card_zmod] at hformula
    rw [hformula]
    simp_rw [hevalFrob]
    change (∑ i ∈ Finset.range m, g i) =
      (m / r) • algebraMap (ZMod p) (GaloisField p m)
        (monicPhase f (minpolyEncoding x))
    calc
      (∑ i ∈ Finset.range m, g i) =
          ∑ i ∈ Finset.range ((m / r) * r), g i := by
        rw [Nat.div_mul_cancel hdiv]
      _ = (m / r) • ∑ i ∈ Finset.range r, g i :=
        sum_range_mul_of_periodic g (m / r) r hgperiod
      _ = (m / r) • algebraMap (ZMod p) (GaloisField p m)
          (monicPhase f (minpolyEncoding x)) := by
        rw [minpolyPhase_eq_sum_frobenius hm f x]
  change psi (Algebra.trace (ZMod p) (GaloisField p m) y) = _
  rw [htrace, AddChar.map_nsmul_eq_pow]
  rfl

private theorem sigma_minpolyEncoding_eq_iff
    {p m r : ℕ} [Fact p.Prime] (x : GaloisField p m)
    (G : MonicDegreePolynomial (ZMod p) r) :
    (⟨(minpoly (ZMod p) x).natDegree, minpolyEncoding x⟩ :
        Σ d, MonicDegreePolynomial (ZMod p) d) = ⟨r, G⟩ ↔
      minpoly (ZMod p) x = G.toPolynomial := by
  constructor
  · intro h
    have hpoly := congrArg
      (fun z : Σ d, MonicDegreePolynomial (ZMod p) d ↦ z.2.toPolynomial) h
    simpa only [minpolyEncoding_toPolynomial] using hpoly
  · intro hpoly
    have hdegree : (minpoly (ZMod p) x).natDegree = r := by
      rw [hpoly, G.toPolynomial_natDegree]
    apply Sigma.ext hdegree
    cases hdegree
    apply heq_of_eq
    apply (monicEncodingEquiv (ZMod p)
      (minpoly (ZMod p) x).natDegree).injective
    apply Subtype.ext
    simpa only [monicEncodingEquiv_apply, minpolyEncoding_toPolynomial]
      using hpoly

/-- Reindexing the extension field by minimal-polynomial fibers identifies the marked Euler sum
with the complete extension exponential sum. -/
theorem markedFactorSum_eq_extensionExponentialSum
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    markedFactorSum psi f m = extensionExponentialSum psi f m := by
  classical
  let _ : Fintype (GaloisField p m) := Fintype.ofFinite _
  let degrees : Finset ℕ := (Finset.Icc 1 m).filter fun r ↦ r ∣ m
  let Index := Σ r, MonicDegreePolynomial (ZMod p) r
  let factors : Finset Index := degrees.sigma fun r ↦ Finset.univ
  let enc : GaloisField p m → Index := fun x ↦
    ⟨(minpoly (ZMod p) x).natDegree, minpolyEncoding x⟩
  let term : GaloisField p m → ℂ := fun x ↦
    monicWeight psi f (minpolyEncoding x) ^
      (m / (minpoly (ZMod p) x).natDegree)
  have henc (x : GaloisField p m) : enc x ∈ factors := by
    rw [Finset.mem_sigma]
    constructor
    · apply Finset.mem_filter.mpr
      have hirr : Irreducible (minpoly (ZMod p) x) :=
        minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
      have hpos := hirr.natDegree_pos
      have hdiv := minpoly.degree_dvd (K := ZMod p)
        (L := GaloisField p m) (Algebra.IsIntegral.isIntegral x)
      rw [GaloisField.finrank p hm] at hdiv
      exact ⟨Finset.mem_Icc.mpr
        ⟨hpos, Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdiv⟩, hdiv⟩
    · exact Finset.mem_univ _
  have hfiber (r : ℕ) (G : MonicDegreePolynomial (ZMod p) r) :
      Finset.univ.filter (fun x : GaloisField p m ↦ enc x = ⟨r, G⟩) =
        minpolyFiber m G.toPolynomial := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, minpolyFiber,
      enc]
    exact sigma_minpolyEncoding_eq_iff x G
  have hinner (z : Index) (hz : z ∈ factors) :
      (∑ x ∈ Finset.univ with enc x = z, term x) =
        if Irreducible z.2.toPolynomial then
          (z.1 : ℂ) * monicWeight psi f z.2 ^ (m / z.1)
        else 0 := by
    rcases z with ⟨r, G⟩
    simp only at hz ⊢
    have hrmem : r ∈ degrees := (Finset.mem_sigma.mp hz).1
    have hdiv : r ∣ m := (Finset.mem_filter.mp hrmem).2
    by_cases hGirr : Irreducible G.toPolynomial
    · rw [if_pos hGirr]
      let fiber := Finset.univ.filter
        (fun x : GaloisField p m ↦ enc x = ⟨r, G⟩)
      calc
        (∑ x ∈ Finset.univ with enc x = ⟨r, G⟩, term x) =
            ∑ _x ∈ fiber, monicWeight psi f G ^ (m / r) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxeq : enc x = ⟨r, G⟩ := (Finset.mem_filter.mp hx).2
          change monicWeight psi f (minpolyEncoding x) ^
              (m / (minpoly (ZMod p) x).natDegree) = _
          change (⟨(minpoly (ZMod p) x).natDegree, minpolyEncoding x⟩ :
            Index) = ⟨r, G⟩ at hxeq
          cases hxeq
          rfl
        _ = fiber.card • monicWeight psi f G ^ (m / r) :=
          Finset.sum_const _
        _ = r • monicWeight psi f G ^ (m / r) := by
          rw [show fiber = minpolyFiber m G.toPolynomial by
            exact hfiber r G]
          rw [card_minpolyFiber hm G.toPolynomial
            G.toPolynomial_monic hGirr, if_pos (by
              simpa only [G.toPolynomial_natDegree] using hdiv),
            G.toPolynomial_natDegree]
        _ = (r : ℂ) * monicWeight psi f G ^ (m / r) := by
          rw [nsmul_eq_mul]
    · rw [if_neg hGirr]
      apply Finset.sum_eq_zero
      intro x hx
      have hxeq : enc x = ⟨r, G⟩ := (Finset.mem_filter.mp hx).2
      have hpoly := (sigma_minpolyEncoding_eq_iff x G).1 (by
        simpa only [enc] using hxeq)
      exact (hGirr (hpoly ▸
        minpoly.irreducible (Algebra.IsIntegral.isIntegral x))).elim
  rw [extensionExponentialSum]
  simp_rw [traceLiftAddChar_eq_minpolyWeight_pow hm]
  change markedFactorSum psi f m = ∑ x : GaloisField p m, term x
  calc
    markedFactorSum psi f m =
        ∑ z ∈ factors,
          if Irreducible z.2.toPolynomial then
            (z.1 : ℂ) * monicWeight psi f z.2 ^ (m / z.1)
          else 0 := by
      rw [markedFactorSum]
      change (∑ r ∈ degrees, ∑ G : MonicDegreePolynomial (ZMod p) r,
        if Irreducible G.toPolynomial then
          (r : ℂ) * monicWeight psi f G ^ (m / r) else 0) = _
      exact Finset.sum_sigma' degrees (fun r ↦ Finset.univ)
        (fun r G ↦ if Irreducible G.toPolynomial then
          (r : ℂ) * monicWeight psi f G ^ (m / r) else 0)
    _ = ∑ z ∈ factors, ∑ x ∈ Finset.univ with enc x = z, term x := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (hinner z hz).symm
    _ = ∑ x : GaloisField p m, term x :=
      Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := factors) (g := enc)
        (fun x _hx ↦ henc x) term

/-- Monic polynomial obtained as the product of `X - r` over a multiset of complex roots. -/
noncomputable def rootFactorPolynomial
    (roots : Multiset ℂ) : Polynomial ℂ :=
  (roots.map fun omega ↦
    1 - Polynomial.C omega * Polynomial.X).prod

/-- Sum of the `m`-th powers of all roots in a multiset. -/
def rootPowerSum (roots : Multiset ℂ) (m : ℕ) : ℂ :=
  (roots.map fun omega ↦ omega ^ m).sum

/-- Power sum of the reciprocal roots of the reversed Artin L-polynomial. -/
noncomputable def reverseRootPowerSum
    (L : Polynomial ℂ) (m : ℕ) : ℂ :=
  rootPowerSum L.reverse.roots m

private theorem rootFactorPolynomial_eq_reverse_prod_X_sub_C
    (roots : Multiset ℂ) :
    rootFactorPolynomial roots =
      ((roots.map fun omega ↦ Polynomial.X - Polynomial.C omega).prod).reverse := by
  have hreverseOne : (1 : Polynomial ℂ).reverse = 1 := by
    have hdegree : (1 : Polynomial ℂ).natDegree = 0 := by simp
    ext n
    rcases n with _ | n
    · simp
    · rw [Polynomial.coeff_reverse, hdegree,
        Polynomial.revAt_eq_self_of_lt (by omega)]
  have hreverseFactor : ∀ omega : ℂ,
      (Polynomial.X - Polynomial.C omega).reverse =
        1 - Polynomial.C omega * Polynomial.X := by
    intro omega
    have hdegree : (Polynomial.X - Polynomial.C omega).natDegree = 1 := by
      simp
    ext n
    rcases n with _ | n
    · simp
    · rcases n with _ | n
      · simp [Polynomial.coeff_reverse, hdegree, Polynomial.coeff_one]
      · rw [Polynomial.coeff_reverse, hdegree,
          Polynomial.revAt_eq_self_of_lt (by omega)]
        simp [Polynomial.coeff_one, Polynomial.coeff_X]
  induction roots using Multiset.induction_on with
  | empty => simpa [rootFactorPolynomial] using hreverseOne.symm
  | cons omega roots ih =>
      have ih' :
          (roots.map fun z ↦ 1 - Polynomial.C z * Polynomial.X).prod =
            ((roots.map fun z ↦ Polynomial.X - Polynomial.C z).prod).reverse := by
        simpa only [rootFactorPolynomial] using ih
      simp only [rootFactorPolynomial, Multiset.map_cons, Multiset.prod_cons]
      rw [Polynomial.reverse_mul_of_domain, hreverseFactor, ih']

private theorem rootFactorPolynomial_coeff_eq_esymm
    (roots : Multiset ℂ) (m : ℕ) :
    (rootFactorPolynomial roots).coeff m = (-1 : ℂ) ^ m * roots.esymm m := by
  let Q : Polynomial ℂ :=
    (roots.map fun omega ↦ Polynomial.X - Polynomial.C omega).prod
  rw [rootFactorPolynomial_eq_reverse_prod_X_sub_C]
  change Q.reverse.coeff m = _
  rw [Polynomial.coeff_reverse]
  have hQdegree : Q.natDegree = roots.card := by
    simpa only [Q] using Polynomial.natDegree_multiset_prod_X_sub_C_eq_card roots
  by_cases hm : m ≤ roots.card
  · rw [Polynomial.revAt_le (by simpa only [hQdegree] using hm)]
    rw [hQdegree]
    have hk : roots.card - m ≤ roots.card := Nat.sub_le _ _
    simpa only [Q, Nat.sub_sub_self hm] using Multiset.prod_X_sub_C_coeff roots hk
  · have hmgt : roots.card < m := Nat.lt_of_not_ge hm
    rw [Polynomial.revAt_eq_self_of_lt (by simpa only [hQdegree] using hmgt)]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa only [hQdegree] using hmgt)]
    have hpowers : roots.powersetCard m = 0 :=
      Multiset.powersetCard_eq_empty m hmgt
    simp [Multiset.esymm, hpowers]

private theorem eval_psum_eq_rootPowerSum
    (roots : Multiset ℂ) (m : ℕ) :
    MvPolynomial.eval (fun x : roots ↦ (x : ℂ))
        (MvPolynomial.psum roots ℂ m) = rootPowerSum roots m := by
  have hr :
      (Finset.univ : Finset roots).val.map (fun x : roots ↦ (x : ℂ)) = roots := by
    simp
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.eval_X,
    rootPowerSum]
  change ((Finset.univ : Finset roots).val.map
    (fun x : roots ↦ ((x : ℂ) ^ m))).sum = _
  change ((Finset.univ : Finset roots).val.map
    ((fun x : ℂ ↦ x ^ m) ∘ fun x : roots ↦ (x : ℂ))).sum = _
  rw [← Multiset.map_map, hr]

private theorem eval_esymm_eq_multiset_esymm
    (roots : Multiset ℂ) (m : ℕ) :
    MvPolynomial.eval (fun x : roots ↦ (x : ℂ))
        (MvPolynomial.esymm roots ℂ m) = roots.esymm m := by
  have hr :
      (Finset.univ : Finset roots).val.map (fun x : roots ↦ (x : ℂ)) = roots := by
    simp
  simpa [MvPolynomial.aeval_def, hr] using
    (MvPolynomial.aeval_esymm_eq_multiset_esymm roots ℂ m
      (fun x : roots ↦ (x : ℂ)))

private theorem sum_antidiagonal_fst_lt_eq_sum_Icc
    {M : Type*} [AddCommMonoid M] (m : ℕ) (F : ℕ → ℕ → M) :
    (∑ a ∈ Finset.antidiagonal m with a.1 < m, F a.1 a.2) =
      ∑ j ∈ Finset.Icc 1 m, F (m - j) j := by
  apply Finset.sum_nbij (fun a : ℕ × ℕ ↦ a.2)
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hsum := Finset.mem_antidiagonal.mp ha'.1
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have haSum := Finset.mem_antidiagonal.mp ha'.1
    have hbSum := Finset.mem_antidiagonal.mp hb'.1
    change a.2 = b.2 at hab
    have hfst : a.1 = b.1 := by omega
    exact Prod.ext hfst hab
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨(m - j, j), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_antidiagonal.mpr (by omega)
    · omega
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hsum := Finset.mem_antidiagonal.mp ha'.1
    congr 1
    omega

/-- Euler logarithmic differentiation gives the convolution recurrence between Artin coefficients
and marked factor sums. -/
theorem artinCoefficient_markedFactor_recurrence
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * artinCoefficient psi f m =
      ∑ j ∈ Finset.Icc 1 m,
        markedFactorSum psi f j * artinCoefficient psi f (m - j) := by
  classical
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let P := truncatedEulerProduct psi f (q + 1)
  let M := markedFactorPolynomial psi f (q + 1)
  have hright :
      (P * M).coeff (q + 1) =
        ∑ j ∈ Finset.Icc 1 (q + 1),
          markedFactorSum psi f j *
            artinCoefficient psi f (q + 1 - j) := by
    rw [Polynomial.coeff_mul]
    calc
      (∑ a ∈ Finset.antidiagonal (q + 1),
          P.coeff a.1 * M.coeff a.2) =
          ∑ a ∈ Finset.antidiagonal (q + 1) with a.1 < q + 1,
            markedFactorSum psi f a.2 * artinCoefficient psi f a.1 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a ha
        have hsum := Finset.mem_antidiagonal.mp ha
        by_cases halt : a.1 < q + 1
        · rw [if_pos halt]
          have ha2pos : 0 < a.2 := by omega
          rw [truncatedEulerProduct_coeff psi f (q + 1) (by omega),
            markedFactorPolynomial_coeff_of_pos_le psi f (q + 1)
              ha2pos (by omega)]
          ring
        · rw [if_neg halt]
          have ha2 : a.2 = 0 := by omega
          rw [ha2, markedFactorPolynomial_coeff_zero]
          simp
      _ = ∑ j ∈ Finset.Icc 1 (q + 1),
          markedFactorSum psi f j *
            artinCoefficient psi f (q + 1 - j) :=
        sum_antidiagonal_fst_lt_eq_sum_Icc (q + 1)
          (fun a b ↦ markedFactorSum psi f b * artinCoefficient psi f a)
  have hlog := truncatedEulerProduct_logDerivative_coeff
    psi f (q + 1) (n := q + 1) le_rfl
  change (Polynomial.X * P.derivative).coeff (q + 1) =
    (P * M).coeff (q + 1) at hlog
  rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
    truncatedEulerProduct_coeff psi f (q + 1) le_rfl, hright] at hlog
  simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hlog

/-- Replaces the marked factor sums in the Artin recurrence by complete extension exponential
sums. -/
theorem artinCoefficient_extension_recurrence
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p))
    {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * artinCoefficient psi f m =
      ∑ j ∈ Finset.Icc 1 m,
        extensionExponentialSum psi f j *
          artinCoefficient psi f (m - j) := by
  rw [artinCoefficient_markedFactor_recurrence psi f hm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [markedFactorSum_eq_extensionExponentialSum
    (Nat.ne_of_gt (Finset.mem_Icc.mp hj).1)]

/-- Newton's identity for the coefficients of a root-factor polynomial and the corresponding root
power sums. -/
theorem rootFactorPolynomial_newton_recurrence
    (roots : Multiset ℂ) {m : ℕ} (_hm : 0 < m) :
    (m : ℂ) * (rootFactorPolynomial roots).coeff m =
      -∑ j ∈ Finset.Icc 1 m,
        rootPowerSum roots j *
          (rootFactorPolynomial roots).coeff (m - j) := by
  let ev : MvPolynomial roots ℂ →+* ℂ :=
    MvPolynomial.eval (fun x : roots ↦ (x : ℂ))
  have hnewton := congrArg ev (MvPolynomial.mul_esymm_eq_sum roots ℂ m)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at hnewton
  rw [sum_antidiagonal_fst_lt_eq_sum_Icc m
    (fun a b ↦ (-1 : ℂ) ^ a *
      ev (MvPolynomial.esymm roots ℂ a) *
        ev (MvPolynomial.psum roots ℂ b))] at hnewton
  dsimp only [ev] at hnewton
  simp_rw [eval_esymm_eq_multiset_esymm, eval_psum_eq_rootPowerSum] at hnewton
  rw [rootFactorPolynomial_coeff_eq_esymm]
  simp_rw [rootFactorPolynomial_coeff_eq_esymm]
  rw [← mul_assoc, mul_comm (m : ℂ) ((-1 : ℂ) ^ m), mul_assoc]
  rw [hnewton]
  rw [← mul_assoc, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have hsign : (-1 : ℂ) ^ m * (-1 : ℂ) ^ (m + 1) = -1 := by
    rw [← pow_add]
    conv_lhs => rw [show m + (m + 1) = 2 * m + 1 by omega]
    rw [pow_add, pow_mul, neg_one_sq, one_pow, pow_one]
    ring
  rw [hsign]
  ring

/-- The normalized reversal of the Artin L-polynomial is exactly the root-factor polynomial of its
reciprocal roots. -/
theorem eq_rootFactorPolynomial_reverse_roots
    (L : Polynomial ℂ) (hL0 : L.coeff 0 = 1) :
    L = rootFactorPolynomial L.reverse.roots := by
  have hL0ne : L.coeff 0 ≠ 0 := by simp [hL0]
  have htrail : L.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hL0ne)
  have hdegree : L.reverse.natDegree = L.natDegree := by
    rw [Polynomial.reverse_natDegree, htrail, Nat.sub_zero]
  have hreverseReverse : L.reverse.reverse = L := by
    change Polynomial.reflect L.reverse.natDegree L.reverse = L
    rw [hdegree]
    exact Polynomial.reflect_reflect
  have hmonic : L.reverse.Monic := by
    rw [Polynomial.Monic, Polynomial.reverse_leadingCoeff,
      Polynomial.trailingCoeff_eq_coeff_zero hL0ne, hL0]
  have hroots : L.reverse.roots.card = L.reverse.natDegree :=
    IsAlgClosed.card_roots_eq_natDegree
  have hfactor :
      (L.reverse.roots.map fun z ↦ Polynomial.X - Polynomial.C z).prod =
        L.reverse :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hroots
  calc
    L = L.reverse.reverse := hreverseReverse.symm
    _ = ((L.reverse.roots.map fun z ↦
          Polynomial.X - Polynomial.C z).prod).reverse := by rw [hfactor]
    _ = rootFactorPolynomial L.reverse.roots :=
      (rootFactorPolynomial_eq_reverse_prod_X_sub_C _).symm

/-- Newton recurrence specialized to the reciprocal roots of the Artin L-polynomial. -/
theorem reverseRoot_newton_recurrence
    (L : Polynomial ℂ) (hL0 : L.coeff 0 = 1)
    {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * L.coeff m =
      -∑ j ∈ Finset.Icc 1 m,
        reverseRootPowerSum L j * L.coeff (m - j) := by
  have hrec := rootFactorPolynomial_newton_recurrence L.reverse.roots hm
  rw [← eq_rootFactorPolynomial_reverse_roots L hL0] at hrec
  simpa only [reverseRootPowerSum] using hrec

/-- Within the cutoff, coefficients of the Artin L-polynomial are the defining Artin
coefficients. -/
theorem artinLPolynomial_coeff_eq_artinCoefficient
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    (m : ℕ) :
    (artinLPolynomial psi f).coeff m = artinCoefficient psi f m := by
  classical
  by_cases hm : m < f.natDegree
  · rw [artinLPolynomial, max_eq_right (by omega), Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single m]
    · simp
    · intro n hn hnm
      rw [Polynomial.coeff_monomial, if_neg hnm]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hm)).elim
  · have hdm : f.natDegree ≤ m := Nat.le_of_not_gt hm
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      ((artinLPolynomial_natDegree_le psi f).trans_lt (by omega))]
    exact (artinCoefficient_eq_zero_of_degree_le psi hpsi f hf0 hpos hsmall hdm).symm

/-- Uniqueness for triangular convolution recurrences: two sequences with common unit constant
term have opposite driving terms when their coefficient recurrences agree. -/
theorem neg_eq_of_convolution_recurrences
    (T S P : ℕ → ℂ) (hT0 : T 0 = 1)
    (hS : ∀ {m : ℕ}, 0 < m →
      (m : ℂ) * T m =
        ∑ j ∈ Finset.Icc 1 m, S j * T (m - j))
    (hP : ∀ {m : ℕ}, 0 < m →
      (m : ℂ) * T m =
        -∑ j ∈ Finset.Icc 1 m, P j * T (m - j)) :
    ∀ {m : ℕ}, 0 < m → S m = -P m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hm
      have hrec :
          (∑ j ∈ Finset.Icc 1 m, S j * T (m - j)) =
            -∑ j ∈ Finset.Icc 1 m, P j * T (m - j) := by
        rw [← hS hm, ← hP hm]
      have hzero :
          ∑ j ∈ Finset.Icc 1 m, (S j + P j) * T (m - j) = 0 := by
        rw [Finset.sum_congr rfl (fun j _ ↦ by rw [add_mul]),
          Finset.sum_add_distrib, hrec]
        simp
      rw [Finset.sum_eq_single m] at hzero
      · rw [Nat.sub_self, hT0, mul_one] at hzero
        calc
          S m = (S m + P m) - P m := by ring
          _ = -P m := by rw [hzero]; ring
      · intro j hj hjm
        have hj' := Finset.mem_Icc.mp hj
        have hprev := ih j (by omega) hj'.1
        rw [hprev]
        ring
      · intro hnot
        exact (hnot (Finset.mem_Icc.mpr ⟨hm, le_rfl⟩)).elim

/-- Complete degree-`m` extension sums are the negatives of the `m`-th power sums of reciprocal
roots, throughout the cutoff range. -/
theorem extensionExponentialSum_eq_neg_reverseRootPowerSum
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {m : ℕ} (hm : m ≠ 0) :
    extensionExponentialSum psi f m =
      -reverseRootPowerSum (artinLPolynomial psi f) m := by
  apply neg_eq_of_convolution_recurrences
    (artinCoefficient psi f) (extensionExponentialSum psi f)
      (reverseRootPowerSum (artinLPolynomial psi f))
  · exact artinCoefficient_zero psi f
  · intro n hn
    exact artinCoefficient_extension_recurrence psi f hn
  · intro n hn
    simpa only [artinLPolynomial_coeff_eq_artinCoefficient
      psi hpsi f hf0 hpos hsmall] using
        reverseRoot_newton_recurrence (artinLPolynomial psi f)
          (artinLPolynomial_coeff_zero psi f) hn
  · exact Nat.pos_of_ne_zero hm

/-- For a nonconstant linear polynomial, every positive-degree extension exponential sum
vanishes. -/
theorem extensionExponentialSum_eq_zero_of_natDegree_eq_one
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hdegree : f.natDegree = 1) {m : ℕ} (hm : m ≠ 0) :
    extensionExponentialSum psi f m = 0 := by
  have hpos : 0 < f.natDegree := by omega
  have hsmall : f.natDegree < p := by
    rw [hdegree]
    exact (Fact.out : p.Prime).one_lt
  have hLdegree : (artinLPolynomial psi f).natDegree ≤ 0 := by
    simpa only [hdegree, Nat.reduceSubDiff] using
      artinLPolynomial_natDegree_le psi f
  have hL : artinLPolynomial psi f = 1 := by
    ext n
    by_cases hn : n = 0
    · subst n
      simpa using artinLPolynomial_coeff_zero psi f
    · rw [Polynomial.coeff_one, if_neg hn]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (hLdegree.trans_lt (Nat.pos_of_ne_zero hn))
  have hreverseOne : (1 : Polynomial ℂ).reverse = 1 := by
    have hdegreeOne : (1 : Polynomial ℂ).natDegree = 0 := by simp
    ext n
    rcases n with _ | n
    · simp
    · rw [Polynomial.coeff_reverse, hdegreeOne,
        Polynomial.revAt_eq_self_of_lt (by omega)]
  rw [extensionExponentialSum_eq_neg_reverseRootPowerSum
    psi hpsi f hf0 hpos hsmall hm, reverseRootPowerSum, hL, hreverseOne]
  simp [rootPowerSum]

/-- Main trace formula: extension exponential sums equal the negative reciprocal-root power sums
for every positive index up to the Artin cutoff. -/
theorem artinLPolynomial_trace_identity
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {n : ℕ} (hn : n ≠ 0) :
    extensionExponentialSum psi f n =
      -((reciprocalRoots psi f).map fun omega ↦ omega ^ n).sum := by
  simpa only [reciprocalRoots, reverseRootPowerSum, rootPowerSum] using
    extensionExponentialSum_eq_neg_reverseRootPowerSum
      psi hpsi f hf0 hpos hsmall hn

end

end TranslationalTilings.Stepanov
