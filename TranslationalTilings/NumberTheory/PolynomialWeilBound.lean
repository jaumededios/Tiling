import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import TranslationalTilings.NumberTheory.Stepanov.ReciprocalRoots

/-!
# Polynomial Weil bounds over prime fields

This file closes the Stepanov development by extracting the reciprocal roots
for a fixed nontrivial additive character, bounding the resulting finite sum,
and specializing to `ZMod.stdAddChar`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

open TranslationalTilings.Stepanov

namespace TranslationalTilings

/-- Reciprocal-root expansion and square-root bounds for a fixed nontrivial character. -/
theorem exists_prime_addChar_reciprocalRoots_le
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hnonconst : 0 < f.natDegree)
    (hsmall : f.natDegree < p) :
    ∃ r ≤ f.natDegree - 1, ∃ alpha : Fin r → ℂ,
      (∑ x : ZMod p, psi (f.eval x)) = -∑ i, alpha i ∧
      ∀ i, ‖alpha i‖ ≤ Real.sqrt p := by
  let _ : Fact p.Prime := ⟨hp⟩
  let g := eraseConstant f
  let roots := reciprocalRoots psi g
  let t := constantTwist psi f
  have hgdegree : g.natDegree = f.natDegree :=
    eraseConstant_natDegree f hnonconst
  have hgpos : 0 < g.natDegree := hgdegree.symm ▸ hnonconst
  have hgsmall : g.natDegree < p := hgdegree.symm ▸ hsmall
  have hroots : roots.card ≤ f.natDegree - 1 := by
    simpa [roots, g, hgdegree] using reciprocalRoots_card_le psi g
  have hrootSum : (∑ x : ZMod p, psi (g.eval x)) = -roots.sum := by
    calc
      (∑ x : ZMod p, psi (g.eval x)) =
          extensionExponentialSum psi g 1 :=
        (extensionExponentialSum_one_eq_primeSum psi g).symm
      _ = -((reciprocalRoots psi g).map fun omega ↦ omega ^ 1).sum :=
        artinLPolynomial_trace_identity psi hpsi g
          (eraseConstant_coeff_zero f) hgpos hgsmall one_ne_zero
      _ = -roots.sum := by simp [roots]
  have hsum :
      (∑ i : Fin roots.toList.length, t * roots.toList[i]) =
        t * roots.sum := by
    calc
      _ = (roots.toList.map fun z ↦ t * z).sum :=
        Fin.sum_univ_fun_getElem roots.toList (fun z ↦ t * z)
      _ = (roots.map fun z ↦ t * z).sum :=
        Multiset.sum_map_toList roots (fun z ↦ t * z)
      _ = _ := by
        simpa using
          (Multiset.sum_map_mul_left (a := t) (s := roots) (f := id))
  refine ⟨roots.toList.length, ?_, fun i ↦ t * roots.toList[i], ?_, ?_⟩
  · simpa using hroots
  · calc
      (∑ x : ZMod p, psi (f.eval x)) =
          extensionExponentialSum psi f 1 :=
        (extensionExponentialSum_one_eq_primeSum psi f).symm
      _ = t ^ 1 * extensionExponentialSum psi g 1 := by
        simpa [t, g] using
          extensionExponentialSum_eraseConstant psi f one_ne_zero
      _ = t * (-roots.sum) := by
        rw [pow_one]
        rw [extensionExponentialSum_one_eq_primeSum psi g, hrootSum]
      _ = -(t * roots.sum) := by ring
      _ = -∑ i : Fin roots.toList.length, t * roots.toList[i] := by rw [hsum]
  · intro i
    rw [norm_mul, show ‖t‖ = 1 by
      simpa [t] using norm_constantTwist_of_finite psi f, one_mul]
    apply reciprocalRoots_norm_le psi hpsi g
      (eraseConstant_coeff_zero f) hgpos hgsmall
    have hi : roots.toList[i] ∈ roots.toList := List.getElem_mem i.isLt
    have hi' : roots.toList[i] ∈ roots := Multiset.mem_toList.mp hi
    simpa [roots] using hi'

/-- Weil's bound for a polynomial sum with an explicitly nontrivial additive character. -/
theorem polynomial_addChar_sum_prime_of_ne_one
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hnonconst : 0 < f.natDegree)
    (hsmall : f.natDegree < p) :
    ‖∑ x : ZMod p, psi (f.eval x)‖ ≤
      (f.natDegree - 1 : ℝ) * Real.sqrt p := by
  obtain ⟨r, hr, alpha, hsum, halpha⟩ :=
    exists_prime_addChar_reciprocalRoots_le
      hp psi hpsi f hnonconst hsmall
  have hr' : (r : ℝ) ≤ (f.natDegree : ℝ) - 1 := by
    calc
      (r : ℝ) ≤ ((f.natDegree - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hr
      _ = (f.natDegree : ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ f.natDegree by omega)]
        norm_num
  rw [hsum, norm_neg]
  calc
    ‖∑ i, alpha i‖ ≤ ∑ i, ‖alpha i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin r, Real.sqrt p :=
      Finset.sum_le_sum fun i _ ↦ halpha i
    _ = (r : ℝ) * Real.sqrt p := by simp
    _ ≤ (f.natDegree - 1 : ℝ) * Real.sqrt p :=
      mul_le_mul_of_nonneg_right hr' (Real.sqrt_nonneg _)

/-- Weil's bound for a polynomial sum against the standard prime-field character. -/
theorem polynomial_addChar_sum_prime
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (f : Polynomial (ZMod p)) (hnonconst : 0 < f.natDegree)
    (hsmall : f.natDegree < p) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (f.eval x)‖ ≤
      (f.natDegree - 1 : ℝ) * Real.sqrt p := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hstd :
      (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
    have h := ZMod.isPrimitive_stdAddChar p
      (a := (1 : ZMod p)) one_ne_zero
    simpa using h
  exact polynomial_addChar_sum_prime_of_ne_one
    hp ZMod.stdAddChar hstd f hnonconst hsmall

end TranslationalTilings
