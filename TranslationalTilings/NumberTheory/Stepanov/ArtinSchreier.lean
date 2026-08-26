import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Artin--Schreier polynomials

This module develops the algebraic facts about `X ^ p - X - c` needed by the Stepanov
argument. It describes a distinguished splitting-field root and the Galois shifts of that root,
derives the degree-one-or-`p` irreducibility criterion, and proves the required irreducibility
statement over the rational function field `RatFunc (ZMod p)`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace TranslationalTilings.Stepanov

open Polynomial

/-- The Artin--Schreier polynomial `X ^ p - X - c` over a field. -/
noncomputable def artinSchreierPolynomial
    {K : Type*} [Field K] (p : ℕ) (c : K) : Polynomial K :=
  Polynomial.X ^ p - Polynomial.X - Polynomial.C c

/-- An Artin--Schreier polynomial in characteristic `p` is monic. -/
theorem artinSchreierPolynomial_monic
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).Monic := by
  unfold artinSchreierPolynomial
  rw [sub_sub]
  apply (monic_X_pow p).sub_of_left
  calc
    (X + C c).degree ≤ 1 := by simp
    _ < (p : WithBot ℕ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
    _ = (X ^ p : Polynomial K).degree := by simp

/-- The natural degree of an Artin--Schreier polynomial is the characteristic prime `p`. -/
theorem artinSchreierPolynomial_natDegree
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).natDegree = p := by
  unfold artinSchreierPolynomial
  rw [sub_sub, natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
  exact (natDegree_add_le _ _).trans_lt (by simpa using (Fact.out : p.Prime).one_lt)

/-- The derivative of `X ^ p - X - c` in characteristic `p` is the constant `-1`. -/
theorem artinSchreierPolynomial_derivative
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).derivative = -1 := by
  simp [artinSchreierPolynomial, derivative_X_pow]

/-- Every Artin--Schreier polynomial is separable. -/
theorem artinSchreierPolynomial_separable
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).Separable := by
  rw [separable_def, artinSchreierPolynomial_derivative]
  rw [IsCoprime.neg_right_iff]
  exact isCoprime_one_right

/-- A distinguished root of an Artin--Schreier polynomial in its splitting field. -/
noncomputable def artinSchreierSplittingRoot
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).SplittingField :=
  Polynomial.rootOfSplits
    (Polynomial.SplittingField.splits (artinSchreierPolynomial p c))
    (Polynomial.degree_ne_of_natDegree_ne (by
      rw [Polynomial.natDegree_map, artinSchreierPolynomial_natDegree c]
      exact (Fact.out : p.Prime).ne_zero))

/-- The distinguished splitting-field element is a root of the mapped Artin--Schreier polynomial. -/
theorem artinSchreierSplittingRoot_isRoot
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    ((artinSchreierPolynomial p c).map
      (algebraMap K (artinSchreierPolynomial p c).SplittingField)).IsRoot
        (artinSchreierSplittingRoot c) := by
  exact Polynomial.eval_rootOfSplits _ _

/-- Any two roots of the same Artin--Schreier polynomial differ by an element of the prime field. -/
theorem artinSchreier_root_sub_root_mem_bot
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]
    {c : K} {x y : L}
    (hx : (artinSchreierPolynomial p c).eval₂ (algebraMap K L) x = 0)
    (hy : (artinSchreierPolynomial p c).eval₂ (algebraMap K L) y = 0) :
    x - y ∈ (⊥ : Subfield L) := by
  rw [Subfield.mem_bot_iff_pow_eq_self, sub_pow_char]
  have hx' : x ^ p - x = algebraMap K L c := by
    exact sub_eq_zero.mp (by simpa [artinSchreierPolynomial] using hx)
  have hy' : y ^ p - y = algebraMap K L c := by
    exact sub_eq_zero.mp (by simpa [artinSchreierPolynomial] using hy)
  linear_combination hx' - hy'

/-- A single Artin--Schreier root generates the entire splitting field. -/
theorem artinSchreier_splittingField_adjoin_root_eq_top
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    IntermediateField.adjoin K {artinSchreierSplittingRoot c} =
      (⊤ : IntermediateField K
        (artinSchreierPolynomial p c).SplittingField) := by
  let E := (artinSchreierPolynomial p c).SplittingField
  let α : E := artinSchreierSplittingRoot c
  let F : IntermediateField K E := IntermediateField.adjoin K {α}
  have hroots : (artinSchreierPolynomial p c).rootSet E ⊆ F := by
    intro y hy
    have hy0 :
        (artinSchreierPolynomial p c).eval₂ (algebraMap K E) y = 0 := by
      simpa [aeval_def] using (Polynomial.mem_rootSet'.mp hy).2
    have hα0 :
        (artinSchreierPolynomial p c).eval₂ (algebraMap K E) α = 0 := by
      rw [← Polynomial.eval_map]
      exact artinSchreierSplittingRoot_isRoot c
    have hdiff : y - α ∈ (⊥ : Subfield E) :=
      artinSchreier_root_sub_root_mem_bot hy0 hα0
    have hdiff' : y - α ∈ (⊥ : IntermediateField K E) := by
      exact (show (⊥ : Subfield E) ≤
        (⊥ : IntermediateField K E).toSubfield from bot_le) hdiff
    have hα : α ∈ F := IntermediateField.subset_adjoin K {α} (Set.mem_singleton α)
    rw [show y = α + (y - α) by ring]
    exact F.add_mem hα ((bot_le : (⊥ : IntermediateField K E) ≤ F) hdiff')
  have hsplit :
      IntermediateField.adjoin K ((artinSchreierPolynomial p c).rootSet E) = ⊤ :=
    (isSplittingField_iff_intermediateField.mp
      (inferInstance : (artinSchreierPolynomial p c).IsSplittingField K E)).2
  change F = ⊤
  apply top_unique
  rw [← hsplit]
  exact IntermediateField.adjoin_le_iff.mpr hroots

/-- Galois automorphisms embed additively into the prime field through their shift of the
chosen root. -/
theorem exists_artinSchreierAutShift
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    ∃ phi : Additive (Polynomial.Gal (artinSchreierPolynomial p c)) →+
        (⊥ : Subfield (artinSchreierPolynomial p c).SplittingField),
      (∀ sigma,
        (phi sigma : (artinSchreierPolynomial p c).SplittingField) =
          sigma (artinSchreierSplittingRoot c) -
            artinSchreierSplittingRoot c) ∧
      Function.Injective phi := by
  let E := (artinSchreierPolynomial p c).SplittingField
  let α : E := artinSchreierSplittingRoot c
  let G := Polynomial.Gal (artinSchreierPolynomial p c)
  have hα0 : (artinSchreierPolynomial p c).eval₂ (algebraMap K E) α = 0 := by
    rw [← Polynomial.eval_map]
    exact artinSchreierSplittingRoot_isRoot c
  have himage (sigma : G) :
      (artinSchreierPolynomial p c).eval₂ (algebraMap K E) (sigma α) = 0 := by
    have hm := (artinSchreierSplittingRoot_isRoot c).map
      (f := sigma.toRingEquiv.toRingHom)
    rw [Polynomial.map_map] at hm
    have hcomp : sigma.toRingEquiv.toRingHom.comp (algebraMap K E) = algebraMap K E := by
      ext k
      exact sigma.commutes k
    rw [hcomp] at hm
    rw [← Polynomial.eval_map]
    exact hm
  have hdiff (sigma : Additive G) : sigma α - α ∈ (⊥ : Subfield E) :=
    artinSchreier_root_sub_root_mem_bot (himage sigma.toMul) hα0
  let phi : Additive G →+ (⊥ : Subfield E) :=
    { toFun := fun sigma ↦ ⟨sigma α - α, hdiff sigma⟩
      map_zero' := by
        apply Subtype.ext
        change α - α = 0
        exact sub_self α
      map_add' := by
        intro sigma tau
        apply Subtype.ext
        change (sigma.toMul * tau.toMul) α - α =
          (sigma.toMul α - α) + (tau.toMul α - α)
        have hdtau : tau.toMul α - α ∈ (⊥ : IntermediateField K E) := by
          exact (show (⊥ : Subfield E) ≤
            (⊥ : IntermediateField K E).toSubfield from bot_le) (hdiff tau)
        have hfix : sigma.toMul (tau.toMul α - α) = tau.toMul α - α := by
          rcases IntermediateField.mem_bot.mp hdtau with ⟨k, hk⟩
          rw [← hk]
          exact sigma.toMul.commutes k
        change sigma.toMul (tau.toMul α) - α =
          (sigma.toMul α - α) + (tau.toMul α - α)
        calc
          sigma.toMul (tau.toMul α) - α =
              (sigma.toMul α - α) + sigma.toMul (tau.toMul α - α) := by
                rw [map_sub]
                ring
          _ = (sigma.toMul α - α) + (tau.toMul α - α) := by rw [hfix] }
  refine ⟨phi, fun sigma ↦ rfl, ?_⟩
  intro sigma tau heq
  apply Additive.toMul.injective
  apply Polynomial.Gal.ext
  intro y hy
  have hy0 : (artinSchreierPolynomial p c).eval₂ (algebraMap K E) y = 0 := by
    simpa [aeval_def] using (Polynomial.mem_rootSet'.mp hy).2
  have hdy : y - α ∈ (⊥ : Subfield E) :=
    artinSchreier_root_sub_root_mem_bot hy0 hα0
  have hdy' : y - α ∈ (⊥ : IntermediateField K E) := by
    exact (show (⊥ : Subfield E) ≤
      (⊥ : IntermediateField K E).toSubfield from bot_le) hdy
  have hfix (rho : G) : rho (y - α) = y - α := by
    rcases IntermediateField.mem_bot.mp hdy' with ⟨k, hk⟩
    rw [← hk]
    exact rho.commutes k
  have hshift : sigma.toMul α - α = tau.toMul α - α :=
    congrArg Subtype.val heq
  have halpha : sigma.toMul α = tau.toMul α := by
    linear_combination hshift
  calc
    sigma.toMul y = sigma.toMul (α + (y - α)) := by
      congr 1
      ring
    _ = sigma.toMul α + (y - α) := by rw [map_add, hfix]
    _ = tau.toMul α + (y - α) := by rw [halpha]
    _ = tau.toMul (α + (y - α)) := by rw [map_add, hfix]
    _ = tau.toMul y := by
      congr 1
      ring

/-- The chosen additive homomorphism sending a Galois automorphism to its root shift. -/
noncomputable def artinSchreierAutShift
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    Additive (Polynomial.Gal (artinSchreierPolynomial p c)) →+
      (⊥ : Subfield (artinSchreierPolynomial p c).SplittingField) :=
  Classical.choose (exists_artinSchreierAutShift c)

/-- The chosen automorphism-shift homomorphism evaluates as `σ α - α`. -/
theorem artinSchreierAutShift_apply
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K)
    (sigma : Additive (Polynomial.Gal (artinSchreierPolynomial p c))) :
    (artinSchreierAutShift c sigma :
      (artinSchreierPolynomial p c).SplittingField) =
        sigma (artinSchreierSplittingRoot c) -
          artinSchreierSplittingRoot c := by
  exact (Classical.choose_spec (exists_artinSchreierAutShift c)).1 sigma

/-- The Artin--Schreier automorphism-shift homomorphism is injective. -/
theorem artinSchreierAutShift_injective
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : Function.Injective (artinSchreierAutShift c) := by
  exact (Classical.choose_spec (exists_artinSchreierAutShift c)).2

/-- The minimal-polynomial degree of the chosen root divides the characteristic prime. -/
theorem artinSchreier_minpoly_natDegree_dvd_prime
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    (minpoly K (artinSchreierSplittingRoot c)).natDegree ∣ p := by
  let E := (artinSchreierPolynomial p c).SplittingField
  let α : E := artinSchreierSplittingRoot c
  have hcard : Nat.card (Polynomial.Gal (artinSchreierPolynomial p c)) =
      (minpoly K α).natDegree := by
    rw [Polynomial.Gal.card_of_separable (artinSchreierPolynomial_separable c)]
    rw [← IntermediateField.finrank_top',
      ← artinSchreier_splittingField_adjoin_root_eq_top c,
      IntermediateField.adjoin.finrank (IsIntegral.of_finite K α)]
  have hdvd := AddSubgroup.card_dvd_of_injective (artinSchreierAutShift c)
    (artinSchreierAutShift_injective c)
  change Nat.card (Polynomial.Gal (artinSchreierPolynomial p c)) ∣
    Nat.card (⊥ : Subfield E) at hdvd
  rw [Subfield.card_bot E p, hcard] at hdvd
  exact hdvd

/-- The chosen root has minimal-polynomial degree either one or `p`. -/
theorem artinSchreier_minpoly_natDegree_eq_one_or_prime
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    (minpoly K (artinSchreierSplittingRoot c)).natDegree = 1 ∨
      (minpoly K (artinSchreierSplittingRoot c)).natDegree = p :=
  (Fact.out : p.Prime).eq_one_or_self_of_dvd _
    (artinSchreier_minpoly_natDegree_dvd_prime c)

/-- An Artin--Schreier polynomial is irreducible exactly when `x ^ p - x = c` has no
base-field solution. -/
theorem artinSchreierPolynomial_irreducible_iff_no_root
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    Irreducible (artinSchreierPolynomial p c) ↔
      ¬ ∃ x : K, x ^ p - x = c := by
  constructor
  · intro hirr ⟨x, hx⟩
    apply hirr.not_isRoot_of_natDegree_ne_one
      (by rw [artinSchreierPolynomial_natDegree]; exact (Fact.out : p.Prime).ne_one)
    change (artinSchreierPolynomial p c).eval x = 0
    simpa [artinSchreierPolynomial] using (sub_eq_zero.mpr hx)
  · intro hnoroot
    let E := (artinSchreierPolynomial p c).SplittingField
    let α : E := artinSchreierSplittingRoot c
    have hα0 : (artinSchreierPolynomial p c).eval₂ (algebraMap K E) α = 0 := by
      rw [← Polynomial.eval_map]
      exact artinSchreierSplittingRoot_isRoot c
    rcases artinSchreier_minpoly_natDegree_eq_one_or_prime c with hdeg | hdeg
    · exfalso
      apply hnoroot
      rcases minpoly.natDegree_eq_one_iff.mp hdeg with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hformula : α ^ p - α - algebraMap K E c = 0 := by
        simpa [artinSchreierPolynomial] using hα0
      have hmapped : algebraMap K E (x ^ p - x - c) = 0 := by
        rw [map_sub, map_sub, map_pow, hx]
        exact hformula
      exact sub_eq_zero.mp ((algebraMap K E).injective (by simpa using hmapped))
    · have hdvd : minpoly K α ∣ artinSchreierPolynomial p c := by
        apply minpoly.dvd K α
        simpa [Polynomial.aeval_def] using hα0
      have heq : artinSchreierPolynomial p c = minpoly K α :=
        Polynomial.eq_of_monic_of_dvd_of_natDegree_le
          (minpoly.monic (IsIntegral.of_finite K α))
          (artinSchreierPolynomial_monic c) hdvd (by
            rw [artinSchreierPolynomial_natDegree, hdeg])
      rw [heq]
      exact minpoly.irreducible (IsIntegral.of_finite K α)

/-- Failure of Artin--Schreier irreducibility is equivalent to the existence of a
base-field root. -/
theorem not_artinSchreierPolynomial_irreducible_iff_root
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    ¬ Irreducible (artinSchreierPolynomial p c) ↔
      ∃ x : K, x ^ p - x = c := by
  simpa only [not_not] using not_congr (artinSchreierPolynomial_irreducible_iff_no_root c)

/-- The Artin--Schreier polynomial `X ^ p - X + f` over `RatFunc (ZMod p)`. -/
noncomputable def artinSchreierRatFuncPolynomial
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p)) :
    Polynomial (RatFunc (ZMod p)) :=
  Polynomial.X ^ p - Polynomial.X +
    Polynomial.C (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) f)

/-- A rational function whose Artin--Schreier difference is polynomial is itself polynomial. -/
theorem ratFunc_eq_algebraMap_of_pow_sub_self_eq_algebraMap
    {p : ℕ} [Fact p.Prime]
    (h : RatFunc (ZMod p)) (g : Polynomial (ZMod p))
    (heq : h ^ p - h =
      algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) g) :
    ∃ A : Polynomial (ZMod p),
      h = algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) A := by
  let P : Polynomial (Polynomial (ZMod p)) :=
    Polynomial.X ^ p - Polynomial.X - Polynomial.C g
  have hPmonic : P.Monic := by
    dsimp [P]
    rw [sub_sub]
    apply (Polynomial.monic_X_pow p).sub_of_left
    calc
      (Polynomial.X + Polynomial.C g).degree ≤ 1 := by simp
      _ < (p : WithBot ℕ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
      _ = (Polynomial.X ^ p : Polynomial (Polynomial (ZMod p))).degree := by simp
  have hint : IsIntegral (Polynomial (ZMod p)) h := by
    refine ⟨P, hPmonic, ?_⟩
    dsimp [P]
    simpa [Polynomial.aeval_def] using (sub_eq_zero.mpr heq)
  rcases IsIntegrallyClosed.isIntegral_iff.mp hint with ⟨A, hA⟩
  exact ⟨A, hA.symm⟩

/-- For a nonconstant polynomial `A`, the degree of `A ^ p - A` is `p * natDegree A`. -/
theorem polynomial_pow_sub_self_natDegree
    {p : ℕ} [Fact p.Prime]
    (A : Polynomial (ZMod p)) (hA : 0 < A.natDegree) :
    (A ^ p - A).natDegree = p * A.natDegree := by
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_pow]
  rw [Polynomial.natDegree_pow]
  nlinarith [(Fact.out : p.Prime).one_lt]

/-- A polynomial of degree strictly between zero and `p` is not an Artin--Schreier
difference in the rational function field. -/
theorem no_ratFunc_artinSchreier_root
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ¬ ∃ h : RatFunc (ZMod p),
      h ^ p - h =
        -algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) f := by
  rintro ⟨h, heq⟩
  have heq' : h ^ p - h =
      algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (-f) := by
    simpa using heq
  rcases ratFunc_eq_algebraMap_of_pow_sub_self_eq_algebraMap h (-f) heq' with ⟨A, hA⟩
  have hpoly : A ^ p - A = -f := by
    apply (RatFunc.algebraMap_injective (ZMod p))
    simpa [hA] using heq'
  by_cases hA0 : A.natDegree = 0
  · have hle : (A ^ p - A).natDegree ≤ 0 := by
      calc
        (A ^ p - A).natDegree ≤ max (A ^ p).natDegree A.natDegree :=
          Polynomial.natDegree_sub_le _ _
        _ ≤ 0 := by rw [Polynomial.natDegree_pow, hA0]; simp
    rw [hpoly, Polynomial.natDegree_neg] at hle
    omega
  · have hApos : 0 < A.natDegree := Nat.pos_of_ne_zero hA0
    have hdeg := polynomial_pow_sub_self_natDegree A hApos
    rw [hpoly, Polynomial.natDegree_neg] at hdeg
    have hle : p ≤ f.natDegree := by
      rw [hdeg]
      exact Nat.le_mul_of_pos_right p hApos
    omega

/-- The rational-function Artin--Schreier polynomial attached to a polynomial of degree in
`(0,p)` is irreducible. -/
theorem artinSchreierRatFuncPolynomial_irreducible
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    Irreducible (artinSchreierRatFuncPolynomial f) := by
  have heq : artinSchreierRatFuncPolynomial f =
      artinSchreierPolynomial p
        (-algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) f) := by
    simp [artinSchreierRatFuncPolynomial, artinSchreierPolynomial]
  rw [heq, artinSchreierPolynomial_irreducible_iff_no_root]
  exact no_ratFunc_artinSchreier_root f hpos hsmall

end TranslationalTilings.Stepanov
