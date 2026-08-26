import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Newton--Waring identities for Stepanov's method

This module encodes monic polynomials by their nonleading coefficients, proves
the Newton--Waring power-sum identity over a splitting field, and develops the
multiplicative and affine-cancellation formulas used by the Artin construction.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings
namespace Stepanov

/-- Remove the constant coefficient of a polynomial. -/
noncomputable def eraseConstant {k : Type*} [CommRing k] (f : Polynomial k) :
    Polynomial k :=
  f - Polynomial.C (f.coeff 0)

/-- The additive-character factor contributed by a polynomial's constant term. -/
def constantTwist {k : Type*} [CommRing k]
    (psi : AddChar k ℂ) (f : Polynomial k) : ℂ :=
  psi (f.coeff 0)

/-- Erasing the constant term makes coefficient zero vanish. -/
theorem eraseConstant_coeff_zero {k : Type*} [CommRing k]
    (f : Polynomial k) :
    (eraseConstant f).coeff 0 = 0 := by
  simp [eraseConstant]

/-- Erasing the constant term preserves every positive natural degree. -/
theorem eraseConstant_natDegree {k : Type*} [CommRing k]
    (f : Polynomial k) (hpos : 0 < f.natDegree) :
    (eraseConstant f).natDegree = f.natDegree := by
  apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
  simpa only [Polynomial.natDegree_C] using hpos

-- The blueprint fixes this theorem's public hypothesis as `Fintype k`.
set_option linter.unusedFintypeInType false in
/-- Over a finite ring, a constant additive-character twist has norm one. -/
theorem norm_constantTwist_of_finite
    {k : Type*} [CommRing k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) :
    ‖constantTwist psi f‖ = 1 := by
  let c := f.coeff 0
  let e : ℕ := Fintype.card k
  have hcard : e • c = 0 := by
    simp [e]
  have hpow : (psi c) ^ e = 1 := by
    rw [← psi.map_nsmul_eq_pow, hcard, psi.map_zero_eq_one]
  have he : e ≠ 0 := Fintype.card_ne_zero
  simp [constantTwist, c, Complex.norm_eq_one_of_pow_eq_one hpow he]

/-- Coefficient data for a monic polynomial of a prescribed degree. -/
structure MonicDegreePolynomial (k : Type*) [CommRing k] (n : ℕ) where
  /-- The nonleading coefficients, ordered from degree `n - 1` downwards. -/
  coeff : Fin n → k
deriving Fintype

namespace MonicDegreePolynomial

/-- Reconstruct the monic polynomial represented by coefficient data. -/
noncomputable def toPolynomial {k : Type*} [CommRing k] {n : ℕ}
    (A : MonicDegreePolynomial k n) : Polynomial k :=
  Polynomial.X ^ n +
    ∑ i : Fin n, Polynomial.monomial (n - 1 - i.1) (A.coeff i)

/-- The coefficient indexed in the order used by the Waring recurrence. -/
def waringCoeff {k : Type*} [CommRing k] {n : ℕ}
    (A : MonicDegreePolynomial k n) (j : ℕ) : k :=
  if h : 1 ≤ j ∧ j ≤ n then A.coeff ⟨j - 1, by omega⟩ else 0

/-- Multiply two encoded monic polynomials. -/
noncomputable def mul {k : Type*} [CommRing k] {n m : ℕ}
    (A : MonicDegreePolynomial k n) (B : MonicDegreePolynomial k m) :
    MonicDegreePolynomial k (n + m) :=
  ⟨fun i ↦ (A.toPolynomial * B.toPolynomial).coeff (n + m - 1 - i.1)⟩

/-- The polynomial reconstructed from monic coefficient data is monic. -/
theorem toPolynomial_monic {k : Type*} [CommRing k] {n : ℕ}
    (A : MonicDegreePolynomial k n) : A.toPolynomial.Monic := by
  apply Polynomial.monic_X_pow_add
  exact (Polynomial.degree_sum_le _ _).trans_lt <|
    (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun i _hi ↦
      (Polynomial.degree_monomial_le _ _).trans_lt <|
        WithBot.coe_lt_coe.2 (show n - 1 - i.1 < n by omega)

/-- Reconstruction has the prescribed natural degree over a nontrivial ring. -/
theorem toPolynomial_natDegree {k : Type*} [CommRing k] [Nontrivial k]
    {n : ℕ} (A : MonicDegreePolynomial k n) :
    A.toPolynomial.natDegree = n := by
  have htail :
      Polynomial.degree
          (∑ i : Fin n, Polynomial.monomial (n - 1 - i.1) (A.coeff i)) < n :=
    (Polynomial.degree_sum_le _ _).trans_lt <|
      (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun i _hi ↦
        (Polynomial.degree_monomial_le _ _).trans_lt <|
          WithBot.coe_lt_coe.2 (show n - 1 - i.1 < n by omega)
  rw [toPolynomial, Polynomial.natDegree_add_eq_left_of_degree_lt (by simpa using htail),
    Polynomial.natDegree_X_pow]

end MonicDegreePolynomial

/-- Reverse the coordinates of a finite coefficient vector. -/
def reverseCoordinatesEquiv (k : Type*) (n : ℕ) :
    (Fin n → k) ≃ (Fin n → k) where
  toFun a i := a i.rev
  invFun a i := a i.rev
  left_inv a := by ext i; simp
  right_inv a := by ext i; simp

/-- Identify monic coefficient records with their coefficient vectors. -/
def MonicDegreePolynomial.coeffEquiv
    (k : Type*) [CommRing k] (n : ℕ) :
    MonicDegreePolynomial k n ≃ (Fin n → k) where
  toFun := MonicDegreePolynomial.coeff
  invFun := MonicDegreePolynomial.mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equivalence with monic polynomials of the prescribed exact degree. -/
noncomputable def monicEncodingEquiv
    (k : Type*) [CommRing k] [Nontrivial k] (n : ℕ) :
    MonicDegreePolynomial k n ≃
      {P : Polynomial k // P.Monic ∧ P.natDegree = n} :=
  (MonicDegreePolynomial.coeffEquiv k n).trans <|
    (reverseCoordinatesEquiv k n).trans <|
      (Polynomial.degreeLTEquiv k n).symm.toEquiv.trans
        (Polynomial.monicEquivDegreeLT (R := k) n).symm

/-- The polynomial component of `monicEncodingEquiv` is reconstruction. -/
theorem monicEncodingEquiv_apply
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (A : MonicDegreePolynomial k n) :
    (monicEncodingEquiv k n A).1 = A.toPolynomial := by
  ext j
  simp only [monicEncodingEquiv, MonicDegreePolynomial.coeffEquiv,
    reverseCoordinatesEquiv, Polynomial.degreeLTEquiv, LinearEquiv.symm_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Polynomial.monicEquivDegreeLT,
    Equiv.symm_mk, Equiv.trans_apply, Equiv.coe_fn_mk,
    LinearEquiv.coe_toEquiv, LinearEquiv.coe_mk, Polynomial.coeff_add,
    Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    MonicDegreePolynomial.toPolynomial, add_right_inj]
  apply Fintype.sum_equiv Fin.revPerm
  intro i
  have hi : i.1 + 1 ≤ n := i.isLt
  have hrev : n - 1 - (n - (i.1 + 1)) = i.1 := by omega
  simp [Fin.val_rev, hrev]

/-- Encode a monic polynomial whose natural degree is prescribed. -/
noncomputable def MonicDegreePolynomial.ofPolynomial
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (P : Polynomial k) (hPmonic : P.Monic)
    (hPdegree : P.natDegree = n) : MonicDegreePolynomial k n :=
  (monicEncodingEquiv k n).symm ⟨P, hPmonic, hPdegree⟩

/-- Reconstructing an encoded monic polynomial returns that polynomial. -/
theorem MonicDegreePolynomial.toPolynomial_ofPolynomial
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (P : Polynomial k) (hPmonic : P.Monic)
    (hPdegree : P.natDegree = n) :
    (MonicDegreePolynomial.ofPolynomial P hPmonic hPdegree).toPolynomial = P := by
  rw [← monicEncodingEquiv_apply]
  exact congr_arg Subtype.val ((monicEncodingEquiv k n).apply_symm_apply
    ⟨P, hPmonic, hPdegree⟩)

/-- Encoding reconstructed coefficient data returns the original data. -/
theorem MonicDegreePolynomial.ofPolynomial_toPolynomial
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (A : MonicDegreePolynomial k n) :
    MonicDegreePolynomial.ofPolynomial A.toPolynomial
      A.toPolynomial_monic A.toPolynomial_natDegree = A := by
  apply (monicEncodingEquiv k n).injective
  apply Subtype.ext
  simpa only [monicEncodingEquiv_apply] using
    MonicDegreePolynomial.toPolynomial_ofPolynomial A.toPolynomial
      A.toPolynomial_monic A.toPolynomial_natDegree

/-- Reconstruction carries encoded multiplication to polynomial multiplication. -/
theorem MonicDegreePolynomial.toPolynomial_mul
    {k : Type*} [CommRing k] {n m : ℕ}
    (A : MonicDegreePolynomial k n) (B : MonicDegreePolynomial k m) :
    (A.mul B).toPolynomial = A.toPolynomial * B.toPolynomial := by
  by_cases h : (0 : k) = 1
  · let _ : Subsingleton k := subsingleton_of_zero_eq_one h
    apply Subsingleton.elim
  · let _ : Nontrivial k := nontrivial_of_ne 0 1 h
    let P := A.toPolynomial * B.toPolynomial
    have hPmonic : P.Monic := A.toPolynomial_monic.mul B.toPolynomial_monic
    have hPdegree : P.natDegree = n + m := by
      simpa only [P, A.toPolynomial_natDegree, B.toPolynomial_natDegree] using
        A.toPolynomial_monic.natDegree_mul B.toPolynomial_monic
    change (A.mul B).toPolynomial = P
    rw [← MonicDegreePolynomial.toPolynomial_ofPolynomial P hPmonic hPdegree]
    congr 1
    apply congrArg MonicDegreePolynomial.mk
    funext i
    simp only [reverseCoordinatesEquiv, Polynomial.degreeLTEquiv,
      LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk,
      Polynomial.monicEquivDegreeLT, Equiv.symm_mk, Equiv.symm_trans,
      Equiv.trans_apply, Equiv.coe_fn_mk, LinearEquiv.coe_symm_toEquiv,
      LinearEquiv.coe_mk, Fin.val_rev, P]
    have hi : i.1 < n + m := i.isLt
    have hidx : n + m - 1 - i.1 = n + m - (i.1 + 1) := by omega
    rw [hidx, Polynomial.eraseLead_coeff_of_ne]
    simpa only [P] using (show n + m - (i.1 + 1) ≠ P.natDegree by
      rw [hPdegree]
      omega)

private noncomputable def waringVariable
    (k : Type*) [CommRing k] (n j : ℕ) : MvPolynomial (Fin n) k :=
  if h : 1 ≤ j ∧ j ≤ n then MvPolynomial.X ⟨j - 1, by omega⟩ else 0

/-- Universal Newton--Waring polynomial for the `m`-th power sum of `n` roots. -/
noncomputable def waringPowerSum (k : Type*) [CommRing k] (n m : ℕ) :
    MvPolynomial (Fin n) k :=
  if _hm : m = 0 then MvPolynomial.C (n : k)
  else -((m : MvPolynomial (Fin n) k) * waringVariable k n m +
    ∑ j : Fin (m - 1),
      waringVariable k n (j.1 + 1) *
        waringPowerSum k n (m - (j.1 + 1)))
termination_by m
decreasing_by omega

/-- Evaluate the universal Waring polynomial on monic coefficient data. -/
noncomputable def monicPowerSum {k : Type*} [CommRing k] {n : ℕ}
    (A : MonicDegreePolynomial k n) (m : ℕ) : k :=
  MvPolynomial.eval A.coeff (waringPowerSum k n m)

/-- Phase obtained by pairing polynomial coefficients with monic power sums. -/
noncomputable def monicPhase {k : Type*} [CommRing k] {n : ℕ}
    (f : Polynomial k) (A : MonicDegreePolynomial k n) : k :=
  ∑ j ∈ f.support, f.coeff j * monicPowerSum A j

/-- Additive-character weight of an encoded monic polynomial. -/
noncomputable def monicWeight {k : Type*} [CommRing k] {n : ℕ}
    (psi : AddChar k ℂ) (f : Polynomial k)
    (A : MonicDegreePolynomial k n) : ℂ :=
  psi (monicPhase f A)

/-- Degree-`n` Artin coefficient obtained by summing monic weights. -/
noncomputable def artinCoefficient {k : Type*} [CommRing k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (n : ℕ) : ℂ :=
  ∑ A : MonicDegreePolynomial k n, monicWeight psi f A

private theorem sum_antidiagonal_Ioo_eq_sum_fin
    {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → ℕ → M) :
    (∑ a ∈ Finset.antidiagonal m with a.1 ∈ Set.Ioo 0 m, f a.1 a.2) =
      ∑ j : Fin (m - 1), f (j.1 + 1) (m - (j.1 + 1)) := by
  calc
    _ = ∑ j ∈ Finset.range (m - 1), f (j + 1) (m - (j + 1)) := by
      apply Finset.sum_nbij (fun a : ℕ × ℕ ↦ a.1 - 1)
      · intro a ha
        have ha' := Finset.mem_filter.mp ha
        have haI : 0 < a.1 ∧ a.1 < m := ha'.2
        simp only [Finset.mem_range]
        omega
      · intro a ha b hb hab
        have ha' := Finset.mem_filter.mp ha
        have hb' := Finset.mem_filter.mp hb
        have haSum : a.1 + a.2 = m := Finset.mem_antidiagonal.mp ha'.1
        have hbSum : b.1 + b.2 = m := Finset.mem_antidiagonal.mp hb'.1
        have haI : 0 < a.1 ∧ a.1 < m := ha'.2
        have hbI : 0 < b.1 ∧ b.1 < m := hb'.2
        change a.1 - 1 = b.1 - 1 at hab
        apply Prod.ext
        · omega
        · omega
      · intro j hj
        have hj' : j < m - 1 := Finset.mem_range.mp hj
        refine ⟨(j + 1, m - (j + 1)), ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_antidiagonal.mpr
            omega
          · change 0 < j + 1 ∧ j + 1 < m
            omega
        · change (j + 1 : ℕ) - 1 = j
          omega
      · intro a ha
        have ha' := Finset.mem_filter.mp ha
        have haSum : a.1 + a.2 = m := Finset.mem_antidiagonal.mp ha'.1
        have haI : 0 < a.1 ∧ a.1 < m := ha'.2
        congr 2 <;> omega
    _ = _ := (Fin.sum_univ_eq_sum_range
      (fun j ↦ f (j + 1) (m - (j + 1))) (m - 1)).symm

private theorem psum_eq_neg_waring_recurrence
    (sigma : Type*) [Fintype sigma] (R : Type*) [CommRing R]
    (m : ℕ) (hm : 0 < m) :
    MvPolynomial.psum sigma R m =
      -((m : MvPolynomial sigma R) *
          ((-1) ^ m * MvPolynomial.esymm sigma R m) +
        ∑ j : Fin (m - 1),
          ((-1) ^ (j.1 + 1) * MvPolynomial.esymm sigma R (j.1 + 1)) *
            MvPolynomial.psum sigma R (m - (j.1 + 1))) := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum sigma R m hm,
    sum_antidiagonal_Ioo_eq_sum_fin m
      (fun a b ↦ (-1) ^ a * MvPolynomial.esymm sigma R a *
        MvPolynomial.psum sigma R b)]
  rw [pow_succ]
  ring

private theorem eval_waringVariable_eq
    (R : Type*) [CommRing R] {n : ℕ} (r u : Fin n → R)
    (hu : ∀ (j : ℕ) (hj : 1 ≤ j ∧ j ≤ n),
      u ⟨j - 1, by omega⟩ =
        MvPolynomial.eval r
          ((-1) ^ j * MvPolynomial.esymm (Fin n) R j))
    (j : ℕ) (hjpos : 0 < j) :
    MvPolynomial.eval u (waringVariable R n j) =
      MvPolynomial.eval r
        ((-1) ^ j * MvPolynomial.esymm (Fin n) R j) := by
  by_cases hj : 1 ≤ j ∧ j ≤ n
  · simp [waringVariable, hj, hu j hj]
  · have hnj : n < j := by omega
    have hempty : Finset.powersetCard j (Finset.univ : Finset (Fin n)) = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simpa using hnj)
    simp [waringVariable, hj, MvPolynomial.esymm, hempty]

private theorem eval_waringPowerSum_eq_psum
    (R : Type*) [CommRing R] {n : ℕ} (r u : Fin n → R)
    (hu : ∀ (j : ℕ) (hj : 1 ≤ j ∧ j ≤ n),
      u ⟨j - 1, by omega⟩ =
        MvPolynomial.eval r
          ((-1) ^ j * MvPolynomial.esymm (Fin n) R j))
    (m : ℕ) :
    MvPolynomial.eval u (waringPowerSum R n m) =
      MvPolynomial.eval r (MvPolynomial.psum (Fin n) R m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm : m = 0
      · subst m
        simp [waringPowerSum, MvPolynomial.psum]
      · rw [waringPowerSum, dif_neg hm,
          psum_eq_neg_waring_recurrence (Fin n) R m (Nat.pos_of_ne_zero hm)]
        simp only [map_neg, map_add, map_mul, map_natCast, map_sum]
        congr 2
        · rw [eval_waringVariable_eq R r u hu m (Nat.pos_of_ne_zero hm), map_mul]
        · apply Finset.sum_congr rfl
          intro j _hj
          rw [eval_waringVariable_eq R r u hu (j.1 + 1) (by omega),
            ih (m - (j.1 + 1)) (by omega), map_mul]

private theorem map_waringVariable
    {R S : Type*} [CommRing R] [CommRing S] (phi : R →+* S)
    (n j : ℕ) :
    MvPolynomial.map phi (waringVariable R n j) = waringVariable S n j := by
  by_cases h : 1 ≤ j ∧ j ≤ n <;> simp [waringVariable, h]

private theorem map_waringPowerSum
    {R S : Type*} [CommRing R] [CommRing S] (phi : R →+* S)
    (n m : ℕ) :
    MvPolynomial.map phi (waringPowerSum R n m) = waringPowerSum S n m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      rw [waringPowerSum, waringPowerSum]
      by_cases hm : m = 0
      · simp [hm]
      · simp only [dif_neg hm, map_neg, map_add, map_mul, map_natCast, map_sum,
          map_waringVariable phi]
        congr 3
        funext j
        rw [ih (m - (j.1 + 1)) (by omega)]

private theorem MonicDegreePolynomial.toPolynomial_coeff_waring
    {R : Type*} [CommRing R] {n j : ℕ}
    (A : MonicDegreePolynomial R n) (hj : 1 ≤ j ∧ j ≤ n) :
    A.toPolynomial.coeff (n - j) = A.coeff ⟨j - 1, by omega⟩ := by
  rw [MonicDegreePolynomial.toPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow, if_neg (by omega : n - j ≠ n), zero_add]
  rw [← Polynomial.lcoeff_apply, map_sum]
  change (∑ i : Fin n,
    (Polynomial.monomial (n - 1 - i.1) (A.coeff i)).coeff (n - j)) = _
  simp only [Polynomial.coeff_monomial]
  let i0 : Fin n := ⟨j - 1, by omega⟩
  calc
    _ = if n - 1 - i0.1 = n - j then A.coeff i0 else 0 :=
      Fintype.sum_eq_single i0 (by
        intro i hi
        exact if_neg (by
          intro heq
          apply hi
          apply Fin.ext
          dsimp [i0]
          omega))
    _ = _ := by
      rw [if_pos (by dsimp [i0]; omega)]

private theorem eval_psum_eq_multiset_map_sum
    {R : Type*} [CommRing R] [DecidableEq R]
    {n : ℕ} (s : Multiset R) (e : Fin n ≃ s) (m : ℕ) :
    MvPolynomial.eval (fun i ↦ (e i : R))
        (MvPolynomial.psum (Fin n) R m) =
      (s.map fun x ↦ x ^ m).sum := by
  have hr :
      (Finset.univ : Finset (Fin n)).val.map (fun i ↦ (e i : R)) = s := by
    have he : (Finset.univ : Finset (Fin n)).map e.toEmbedding =
        (Finset.univ : Finset s) := by
      ext x
      simp
    have heval : (Finset.univ : Finset (Fin n)).val.map e.toEmbedding =
        (Finset.univ : Finset s).val := by
      simpa only [Finset.map_val] using congrArg Finset.val he
    change (Finset.univ : Finset (Fin n)).val.map
      ((fun x : s ↦ (x : R)) ∘ e.toEmbedding) = s
    rw [← Multiset.map_map, heval, Multiset.map_univ_coe]
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.eval_X]
  change ((Finset.univ : Finset (Fin n)).val.map
    (fun i ↦ ((e i : R) ^ m))).sum = _
  have hmap :
      (Finset.univ : Finset (Fin n)).val.map (fun i ↦ ((e i : R) ^ m)) =
        s.map (fun x ↦ x ^ m) := by
    change (Finset.univ : Finset (Fin n)).val.map
      ((fun x : R ↦ x ^ m) ∘ fun i ↦ (e i : R)) = _
    rw [← Multiset.map_map, hr]
  rw [hmap]

/-- The encoded power sum equals the sum of powers of all roots. -/
theorem monicPowerSum_eq_sum_roots
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (A : MonicDegreePolynomial k n)
    (hA : (A.toPolynomial.map (algebraMap k K)).Splits) (m : ℕ) :
    algebraMap k K (monicPowerSum A m) =
      ((A.toPolynomial.map (algebraMap k K)).roots.map fun x ↦ x ^ m).sum := by
  classical
  let phi : k →+* K := algebraMap k K
  let q : Polynomial K := A.toPolynomial.map phi
  have hqDegree : q.natDegree = n := by
    simpa only [q, phi, A.toPolynomial_natDegree] using
      A.toPolynomial_monic.natDegree_map phi
  have hsCard : q.roots.card = n := by
    rw [(Polynomial.splits_iff_card_roots.mp hA), hqDegree]
  let e : Fin n ≃ q.roots :=
    (Fintype.equivFinOfCardEq (by simpa only [Multiset.card_coe] using hsCard)).symm
  let r : Fin n → K := fun i ↦ (e i : K)
  have hr : (Finset.univ : Finset (Fin n)).val.map r = q.roots := by
    have he : (Finset.univ : Finset (Fin n)).map e.toEmbedding =
        (Finset.univ : Finset q.roots) := by
      ext x
      simp
    have heval : (Finset.univ : Finset (Fin n)).val.map e.toEmbedding =
        (Finset.univ : Finset q.roots).val := by
      simpa only [Finset.map_val] using congrArg Finset.val he
    change (Finset.univ : Finset (Fin n)).val.map
      ((fun x : q.roots ↦ (x : K)) ∘ e.toEmbedding) = q.roots
    rw [← Multiset.map_map, heval, Multiset.map_univ_coe]
  have hu : ∀ (j : ℕ) (hj : 1 ≤ j ∧ j ≤ n),
      (phi ∘ A.coeff) ⟨j - 1, by omega⟩ =
        MvPolynomial.eval r
          ((-1) ^ j * MvPolynomial.esymm (Fin n) K j) := by
    intro j hj
    have hcoeff : q.coeff (n - j) = phi (A.coeff ⟨j - 1, by omega⟩) := by
      simp only [q, Polynomial.coeff_map, A.toPolynomial_coeff_waring hj]
    have hqMonic : q.Monic := by
      simpa only [q] using A.toPolynomial_monic.map phi
    have hvieta := Polynomial.coeff_eq_esymm_roots_of_splits hA
      (show n - j ≤ q.natDegree by rw [hqDegree]; omega)
    rw [hqDegree, Nat.sub_sub_self hj.2, hqMonic.leadingCoeff, one_mul] at hvieta
    have hesymm :
        MvPolynomial.eval r (MvPolynomial.esymm (Fin n) K j) = q.roots.esymm j := by
      simpa [MvPolynomial.aeval_def, hr] using
        (MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) K j r)
    rw [map_mul, map_pow, map_neg, map_one, hesymm]
    exact hcoeff.symm.trans hvieta
  calc
    algebraMap k K (monicPowerSum A m) =
        MvPolynomial.eval (phi ∘ A.coeff)
          (MvPolynomial.map phi (waringPowerSum k n m)) := by
      exact MvPolynomial.map_eval phi A.coeff (waringPowerSum k n m)
    _ = MvPolynomial.eval (phi ∘ A.coeff) (waringPowerSum K n m) := by
      rw [map_waringPowerSum]
    _ = MvPolynomial.eval r (MvPolynomial.psum (Fin n) K m) :=
      eval_waringPowerSum_eq_psum K r (phi ∘ A.coeff) hu m
    _ = (q.roots.map fun x ↦ x ^ m).sum :=
      eval_psum_eq_multiset_map_sum q.roots e m
    _ = _ := rfl

private theorem monicPowerSum_mul_of_splits
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    {n m : ℕ} (A : MonicDegreePolynomial k n)
    (B : MonicDegreePolynomial k m)
    (hinj : Function.Injective (algebraMap k K))
    (hA : (A.toPolynomial.map (algebraMap k K)).Splits)
    (hB : (B.toPolynomial.map (algebraMap k K)).Splits)
    (j : ℕ) :
    monicPowerSum (A.mul B) j = monicPowerSum A j + monicPowerSum B j := by
  apply hinj
  have hC : ((A.mul B).toPolynomial.map (algebraMap k K)).Splits := by
    rw [A.toPolynomial_mul B, Polynomial.map_mul]
    exact hA.mul hB
  rw [map_add]
  rw [monicPowerSum_eq_sum_roots (A.mul B) hC,
    monicPowerSum_eq_sum_roots A hA, monicPowerSum_eq_sum_roots B hB,
    A.toPolynomial_mul B, Polynomial.map_mul,
    Polynomial.roots_mul (mul_ne_zero
      (A.toPolynomial_monic.map (algebraMap k K)).ne_zero
      (B.toPolynomial_monic.map (algebraMap k K)).ne_zero),
    Multiset.map_add, Multiset.sum_add]

private theorem monicPhase_mul
    {k : Type*} [Field k] {n m : ℕ}
    (f : Polynomial k) (A : MonicDegreePolynomial k n)
    (B : MonicDegreePolynomial k m) :
    monicPhase f (A.mul B) = monicPhase f A + monicPhase f B := by
  let K := AlgebraicClosure k
  let phi : k →+* K := algebraMap k K
  have hinj : Function.Injective phi := FaithfulSMul.algebraMap_injective k K
  have hA : (A.toPolynomial.map phi).Splits := IsAlgClosed.splits _
  have hB : (B.toPolynomial.map phi).Splits := IsAlgClosed.splits _
  simp only [monicPhase]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [monicPowerSum_mul_of_splits A B hinj hA hB, mul_add]

/-- Monic weights multiply under encoded polynomial multiplication. -/
theorem monicWeight_mul
    {k : Type*} [Field k] {n m : ℕ}
    (psi : AddChar k ℂ) (f : Polynomial k)
    (A : MonicDegreePolynomial k n) (B : MonicDegreePolynomial k m) :
    monicWeight psi f (A.mul B) = monicWeight psi f A * monicWeight psi f B := by
  rw [monicWeight, monicWeight, monicWeight, monicPhase_mul,
    AddChar.map_add_eq_mul]

/-- A monic polynomial bundled with its proof of monicity. -/
def MonicPolynomial (k : Type*) [CommRing k] :=
  {P : Polynomial k // P.Monic}

namespace MonicPolynomial

/-- Encode a bundled monic polynomial in its natural degree. -/
noncomputable def encoding
    {k : Type*} [CommRing k] [Nontrivial k]
    (P : MonicPolynomial k) :
    MonicDegreePolynomial k P.1.natDegree :=
  (monicEncodingEquiv k P.1.natDegree).symm ⟨P.1, P.2, rfl⟩

/-- Reconstruction of a bundled monic polynomial's encoding is the original. -/
theorem encoding_toPolynomial
    {k : Type*} [CommRing k] [Nontrivial k]
    (P : MonicPolynomial k) : P.encoding.toPolynomial = P.1 := by
  exact MonicDegreePolynomial.toPolynomial_ofPolynomial P.1 P.2 rfl

/-- The multiset of normalized irreducible factors of a nonzero monic polynomial. -/
noncomputable def normalizedIrreducibleFactors
    {k : Type*} [Field k] (P : MonicPolynomial k) :
    Multiset (MonicPolynomial k) := by
  letI := Classical.decEq k
  exact (UniqueFactorizationMonoid.normalizedFactors P.1).attach.map
    fun G ↦
      ⟨G.1,
        ((Polynomial.mem_normalizedFactors_iff P.2.ne_zero).mp G.2).2.1⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every normalized factor of a nonconstant bundled monic polynomial is irreducible. -/
theorem normalizedIrreducibleFactors_irreducible
    {k : Type*} [Field k] (P : MonicPolynomial k)
    {G : MonicPolynomial k}
    (hG : G ∈ P.normalizedIrreducibleFactors) : Irreducible G.1 := by
  classical
  unfold normalizedIrreducibleFactors at hG
  rw [Multiset.mem_map] at hG
  obtain ⟨H, _hH, rfl⟩ := hG
  exact ((Polynomial.mem_normalizedFactors_iff P.2.ne_zero).mp H.2).1

set_option backward.isDefEq.respectTransparency false in
/-- The normalized irreducible factors multiply to the monic polynomial. -/
theorem normalizedIrreducibleFactors_prod
    {k : Type*} [Field k] (P : MonicPolynomial k) :
    (P.normalizedIrreducibleFactors.map fun G ↦ G.1).prod = P.1 := by
  classical
  unfold normalizedIrreducibleFactors
  rw [Multiset.map_map]
  change (Multiset.map Subtype.val
    (UniqueFactorizationMonoid.normalizedFactors P.1).attach).prod = _
  rw [Multiset.attach_map_val,
    UniqueFactorizationMonoid.prod_normalizedFactors_eq P.2.ne_zero,
    P.2.normalize_eq_self]

set_option backward.isDefEq.respectTransparency false in
/-- Degrees of normalized irreducible factors sum to the polynomial's degree. -/
theorem normalizedIrreducibleFactors_degree_sum
    {k : Type*} [Field k] (P : MonicPolynomial k) :
    (P.normalizedIrreducibleFactors.map fun G ↦ G.1.natDegree).sum =
      P.1.natDegree := by
  classical
  unfold normalizedIrreducibleFactors
  rw [Multiset.map_map]
  change (Multiset.map (Polynomial.natDegree ∘ Subtype.val)
    (UniqueFactorizationMonoid.normalizedFactors P.1).attach).sum = _
  rw [← Multiset.map_map, Multiset.attach_map_val]
  rw [← Polynomial.natDegree_multiset_prod
    (UniqueFactorizationMonoid.normalizedFactors P.1)
    (UniqueFactorizationMonoid.zero_notMem_normalizedFactors P.1),
    UniqueFactorizationMonoid.prod_normalizedFactors_eq P.2.ne_zero,
    P.2.normalize_eq_self]

end MonicPolynomial

/-- Additive-character weight of a bundled monic polynomial. -/
noncomputable def monicPolynomialWeight
    {k : Type*} [Field k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (P : MonicPolynomial k) : ℂ :=
  monicWeight psi f P.encoding

private theorem monicPolynomialPhase_mul
    {k : Type*} [Field k] (f : Polynomial k)
    (P Q : MonicPolynomial k) :
    let R : MonicPolynomial k := ⟨P.1 * Q.1, P.2.mul Q.2⟩
    monicPhase f R.encoding =
      monicPhase f P.encoding + monicPhase f Q.encoding := by
  let R : MonicPolynomial k := ⟨P.1 * Q.1, P.2.mul Q.2⟩
  let K := AlgebraicClosure k
  let phi : k →+* K := algebraMap k K
  have hinj : Function.Injective phi :=
    FaithfulSMul.algebraMap_injective k K
  have hP : (P.encoding.toPolynomial.map phi).Splits := IsAlgClosed.splits _
  have hQ : (Q.encoding.toPolynomial.map phi).Splits := IsAlgClosed.splits _
  have hR : (R.encoding.toPolynomial.map phi).Splits := IsAlgClosed.splits _
  dsimp only
  apply hinj
  rw [map_add]
  simp only [monicPhase, map_sum, map_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [monicPowerSum_eq_sum_roots R.encoding hR,
    monicPowerSum_eq_sum_roots P.encoding hP,
    monicPowerSum_eq_sum_roots Q.encoding hQ]
  rw [MonicPolynomial.encoding_toPolynomial,
    MonicPolynomial.encoding_toPolynomial,
    MonicPolynomial.encoding_toPolynomial]
  change phi (f.coeff j) *
      ((((P.1 * Q.1).map phi).roots.map fun x ↦ x ^ j).sum) = _
  rw [Polynomial.map_mul,
    Polynomial.roots_mul (mul_ne_zero
      (P.2.map phi).ne_zero (Q.2.map phi).ne_zero),
    Multiset.map_add, Multiset.sum_add, mul_add]

private theorem monicPolynomialWeight_mul
    {k : Type*} [Field k] (psi : AddChar k ℂ)
    (f : Polynomial k) (P Q : MonicPolynomial k) :
    monicPolynomialWeight psi f ⟨P.1 * Q.1, P.2.mul Q.2⟩ =
      monicPolynomialWeight psi f P * monicPolynomialWeight psi f Q := by
  unfold monicPolynomialWeight monicWeight
  rw [monicPolynomialPhase_mul, AddChar.map_add_eq_mul]

set_option backward.isDefEq.respectTransparency false in
private theorem monicPolynomialWeight_one
    {k : Type*} [Field k] (psi : AddChar k ℂ)
    (f : Polynomial k) :
    monicPolynomialWeight psi f ⟨1, Polynomial.monic_one⟩ = 1 := by
  let U : MonicPolynomial k := ⟨1, Polynomial.monic_one⟩
  let w : ℂ := monicPolynomialWeight psi f U
  have hUU : (⟨U.1 * U.1, U.2.mul U.2⟩ : MonicPolynomial k) = U := by
    apply Subtype.ext
    simp [U]
  have hidem : w = w * w := by
    simpa only [w, hUU] using monicPolynomialWeight_mul psi f U U
  have hwne : w ≠ 0 := by
    unfold w monicPolynomialWeight monicWeight
    intro hw
    have hunit :
        psi (monicPhase f U.encoding) *
            psi (-(monicPhase f U.encoding)) = 1 := by
      rw [← psi.map_add_eq_mul]
      simp only [add_neg_cancel, psi.map_zero_eq_one]
    rw [hw, zero_mul] at hunit
    exact zero_ne_one hunit
  change w = 1
  exact (mul_left_cancel₀ hwne (by simpa only [mul_one] using hidem)).symm

private theorem monic_multiset_prod
    {k : Type*} [Field k] (s : Multiset (MonicPolynomial k)) :
    ((s.map fun G : MonicPolynomial k ↦ G.1).prod).Monic := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons G s ih =>
      simpa only [Multiset.map_cons, Multiset.prod_cons] using G.2.mul ih

set_option backward.isDefEq.respectTransparency false in
private theorem monicPolynomialWeight_multiset_prod
    {k : Type*} [Field k] (psi : AddChar k ℂ)
    (f : Polynomial k) (s : Multiset (MonicPolynomial k)) :
    monicPolynomialWeight psi f
        ⟨(s.map fun G : MonicPolynomial k ↦ G.1).prod,
          monic_multiset_prod s⟩ =
      (s.map (monicPolynomialWeight psi f)).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      exact monicPolynomialWeight_one psi f
  | cons G s ih =>
      let Q : MonicPolynomial k :=
        ⟨(s.map (fun H : MonicPolynomial k ↦ H.1)).prod,
          monic_multiset_prod s⟩
      calc
        monicPolynomialWeight psi f
            ⟨(Multiset.map (fun H : MonicPolynomial k ↦ H.1)
                (G ::ₘ s)).prod, monic_multiset_prod (G ::ₘ s)⟩ =
            monicPolynomialWeight psi f
              ⟨G.1 * Q.1, G.2.mul Q.2⟩ := by
                apply congrArg (monicPolynomialWeight psi f)
                apply Subtype.ext
                simp [Q]
        _ = monicPolynomialWeight psi f G *
              monicPolynomialWeight psi f Q :=
            monicPolynomialWeight_mul psi f G Q
        _ = monicPolynomialWeight psi f G *
              (s.map (monicPolynomialWeight psi f)).prod := by
            exact congrArg (monicPolynomialWeight psi f G * ·) ih
        _ = ((G ::ₘ s).map (monicPolynomialWeight psi f)).prod := by
            rw [Multiset.map_cons, Multiset.prod_cons]

set_option backward.isDefEq.respectTransparency false in
/-- A monic polynomial's weight is the product of its normalized-factor weights. -/
theorem monicWeight_eq_prod_normalizedIrreducibleFactors
    {k : Type*} [Field k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (P : MonicPolynomial k) :
    monicPolynomialWeight psi f P =
      (P.normalizedIrreducibleFactors.map
        (monicPolynomialWeight psi f)).prod := by
  classical
  let s := P.normalizedIrreducibleFactors
  let Q : MonicPolynomial k :=
    ⟨(s.map fun G ↦ G.1).prod, monic_multiset_prod s⟩
  have hPQ : P = Q := by
    apply Subtype.ext
    exact P.normalizedIrreducibleFactors_prod.symm
  calc
    monicPolynomialWeight psi f P = monicPolynomialWeight psi f Q :=
      congrArg (monicPolynomialWeight psi f) hPQ
    _ = (s.map (monicPolynomialWeight psi f)).prod :=
      monicPolynomialWeight_multiset_prod psi f s
    _ = _ := rfl

private theorem eval_waringVariable_update_lt
    {k : Type*} [CommRing k] {n d j : ℕ}
    (hdpos : 0 < d) (hdn : d ≤ n) (hjpos : 0 < j) (hjd : j < d)
    (A : MonicDegreePolynomial k n) (u v : k) :
    MvPolynomial.eval
        (Function.update A.coeff ⟨d - 1, by omega⟩ u)
        (waringVariable k n j) =
      MvPolynomial.eval
        (Function.update A.coeff ⟨d - 1, by omega⟩ v)
        (waringVariable k n j) := by
  have hjn : 1 ≤ j ∧ j ≤ n := by omega
  let ij : Fin n := ⟨j - 1, by omega⟩
  let id : Fin n := ⟨d - 1, by omega⟩
  have hne : ij ≠ id := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [ij, id] at hval
    omega
  simp [waringVariable, hjn, ij, id, hne]

private theorem eval_waringVariable_update_eq
    {k : Type*} [CommRing k] {n d : ℕ}
    (hdpos : 0 < d) (hdn : d ≤ n)
    (A : MonicDegreePolynomial k n) (u : k) :
    MvPolynomial.eval
        (Function.update A.coeff ⟨d - 1, by omega⟩ u)
        (waringVariable k n d) = u := by
  have hdn' : 1 ≤ d ∧ d ≤ n := by omega
  simp [waringVariable, hdn']

private theorem eval_waringPowerSum_update_lt
    {k : Type*} [CommRing k] {n d : ℕ}
    (hdpos : 0 < d) (hdn : d ≤ n)
    (A : MonicDegreePolynomial k n) (u v : k)
    (m : ℕ) (hmd : m < d) :
    MvPolynomial.eval
        (Function.update A.coeff ⟨d - 1, by omega⟩ u)
        (waringPowerSum k n m) =
      MvPolynomial.eval
        (Function.update A.coeff ⟨d - 1, by omega⟩ v)
        (waringPowerSum k n m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      rw [waringPowerSum]
      by_cases hm : m = 0
      · simp [hm]
      · rw [dif_neg hm]
        simp only [map_neg, map_add, map_mul, map_natCast, map_sum]
        congr 2
        · rw [eval_waringVariable_update_lt hdpos hdn
            (Nat.pos_of_ne_zero hm) hmd A u v]
        · apply Finset.sum_congr rfl
          intro j _hj
          rw [eval_waringVariable_update_lt hdpos hdn (by omega)
            (by omega) A u v,
            ih (m - (j.1 + 1)) (by omega) (by omega)]

private theorem eval_waringPowerSum_update_eq
    {k : Type*} [CommRing k] {n d : ℕ}
    (hdpos : 0 < d) (hdn : d ≤ n)
    (A : MonicDegreePolynomial k n) (u : k) :
    MvPolynomial.eval
        (Function.update A.coeff ⟨d - 1, by omega⟩ u)
        (waringPowerSum k n d) =
      -(d : k) * u +
        MvPolynomial.eval
          (Function.update A.coeff ⟨d - 1, by omega⟩ 0)
          (waringPowerSum k n d) := by
  have hdne : d ≠ 0 := Nat.ne_of_gt hdpos
  rw [waringPowerSum, dif_neg hdne]
  simp only [map_neg, map_add, map_mul, map_natCast, map_sum]
  rw [eval_waringVariable_update_eq hdpos hdn A u,
    eval_waringVariable_update_eq hdpos hdn A 0]
  have hsum :
      (∑ j : Fin (d - 1),
        MvPolynomial.eval
            (Function.update A.coeff ⟨d - 1, by omega⟩ u)
            (waringVariable k n (j.1 + 1)) *
          MvPolynomial.eval
            (Function.update A.coeff ⟨d - 1, by omega⟩ u)
            (waringPowerSum k n (d - (j.1 + 1)))) =
        ∑ j : Fin (d - 1),
          MvPolynomial.eval
              (Function.update A.coeff ⟨d - 1, by omega⟩ 0)
              (waringVariable k n (j.1 + 1)) *
            MvPolynomial.eval
              (Function.update A.coeff ⟨d - 1, by omega⟩ 0)
              (waringPowerSum k n (d - (j.1 + 1))) := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [eval_waringVariable_update_lt hdpos hdn (by omega)
      (by omega) A u 0,
      eval_waringPowerSum_update_lt hdpos hdn A u 0
        (d - (j.1 + 1)) (by omega)]
  rw [hsum]
  ring

/-- The monic phase is affine in the last coefficient in the bounded-degree range. -/
theorem monicPhase_affine_last
    {k : Type*} [CommRing k] {d : ℕ}
    (f : Polynomial k) (hd : f.natDegree = d) (hdpos : 0 < d)
    (n : ℕ) (hdn : d ≤ n) :
    ∀ A : MonicDegreePolynomial k n, ∀ u : k,
      monicPhase f
          ⟨Function.update A.coeff ⟨d - 1, by omega⟩ u⟩ =
        -(d : k) * f.leadingCoeff * u +
          monicPhase f
            ⟨Function.update A.coeff ⟨d - 1, by omega⟩ 0⟩ := by
  intro A u
  have hfne : f ≠ 0 := by
    intro hf
    subst f
    simp only [Polynomial.natDegree_zero] at hd
    omega
  have hdmem : d ∈ f.support := by
    apply Polynomial.mem_support_iff.mpr
    rw [← hd, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hfne
  have hcoeff : f.coeff d = f.leadingCoeff := by
    rw [← hd, Polynomial.coeff_natDegree]
  have hterm : ∀ j ∈ f.support,
      f.coeff j *
          monicPowerSum
            (⟨Function.update A.coeff ⟨d - 1, by omega⟩ u⟩ :
              MonicDegreePolynomial k n) j =
        (if j = d then -(d : k) * f.leadingCoeff * u else 0) +
          f.coeff j *
            monicPowerSum
              (⟨Function.update A.coeff ⟨d - 1, by omega⟩ 0⟩ :
                MonicDegreePolynomial k n) j := by
    intro j hj
    have hjle : j ≤ d := by
      rw [← hd]
      exact Polynomial.le_natDegree_of_ne_zero
        (Polynomial.mem_support_iff.mp hj)
    by_cases hjd : j = d
    · subst j
      rw [if_pos rfl, hcoeff]
      unfold monicPowerSum
      rw [eval_waringPowerSum_update_eq hdpos hdn A u]
      ring
    · have hjlt : j < d := by omega
      rw [if_neg hjd, zero_add]
      unfold monicPowerSum
      exact congrArg (f.coeff j * ·)
        (eval_waringPowerSum_update_lt hdpos hdn A u 0 j hjlt)
  unfold monicPhase
  calc
    (∑ j ∈ f.support,
      f.coeff j *
        monicPowerSum
          (⟨Function.update A.coeff ⟨d - 1, by omega⟩ u⟩ :
            MonicDegreePolynomial k n) j) =
        ∑ j ∈ f.support,
          ((if j = d then -(d : k) * f.leadingCoeff * u else 0) +
            f.coeff j *
              monicPowerSum
                (⟨Function.update A.coeff ⟨d - 1, by omega⟩ 0⟩ :
                  MonicDegreePolynomial k n) j) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = (∑ j ∈ f.support,
          if j = d then -(d : k) * f.leadingCoeff * u else 0) +
        ∑ j ∈ f.support,
          f.coeff j *
            monicPowerSum
              (⟨Function.update A.coeff ⟨d - 1, by omega⟩ 0⟩ :
                MonicDegreePolynomial k n) j := by
      rw [Finset.sum_add_distrib]
    _ = -(d : k) * f.leadingCoeff * u +
        ∑ j ∈ f.support,
          f.coeff j *
            monicPowerSum
              (⟨Function.update A.coeff ⟨d - 1, by omega⟩ 0⟩ :
                MonicDegreePolynomial k n) j := by
      congr 1
      simpa only [if_pos] using
        (Finset.sum_eq_single (s := f.support)
          (f := fun j ↦
            if j = d then -(d : k) * f.leadingCoeff * u else 0) d
          (by
            intro j _hj hjd
            simp [hjd])
          (by
            intro hnot
            exact (hnot hdmem).elim))

private def coefficientTranslation
    {k : Type*} [CommRing k] {n : ℕ} (i : Fin n) (v : k) :
    MonicDegreePolynomial k n ≃ MonicDegreePolynomial k n where
  toFun A := ⟨Function.update A.coeff i (A.coeff i + v)⟩
  invFun A := ⟨Function.update A.coeff i (A.coeff i - v)⟩
  left_inv A := by
    cases A with
    | mk coeff =>
        apply congrArg MonicDegreePolynomial.mk
        funext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
  right_inv A := by
    cases A with
    | mk coeff =>
        apply congrArg MonicDegreePolynomial.mk
        funext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]

-- The public normalization hypothesis is retained, although cancellation is
-- invariant under adding a constant to `f` and the proof establishes more.
set_option linter.unusedVariables false in
/-- Artin coefficients vanish in degrees at least the positive phase degree. -/
theorem artinCoefficient_eq_zero_of_degree_le
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {n : ℕ} (hn : f.natDegree ≤ n) :
    artinCoefficient psi f n = 0 := by
  classical
  clear hf0
  let d := f.natDegree
  let i : Fin n := ⟨d - 1, by dsimp [d]; omega⟩
  let c : ZMod p := -(d : ZMod p) * f.leadingCoeff
  have hfne : f ≠ 0 := by
    intro hf
    subst f
    simp at hpos
  have hdcast : (d : ZMod p) ≠ 0 := by
    intro hd0
    have hval := congrArg ZMod.val hd0
    rw [ZMod.val_cast_of_lt (by simpa only [d] using hsmall)] at hval
    simp only [ZMod.val_zero] at hval
    omega
  have hlc : f.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hfne
  have hcne : c ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr hdcast) hlc
  have hcunit : IsUnit c := isUnit_iff_ne_zero.mpr hcne
  have hshift : psi.mulShift c ≠ 1 := by
    intro h
    apply hpsi
    exact (AddChar.mulShift_unit_eq_one_iff psi hcunit).mp h
  obtain ⟨v, hv⟩ : ∃ v : ZMod p, psi (c * v) ≠ 1 := by
    by_contra h
    push Not at h
    apply hshift
    ext v
    simpa only [AddChar.mulShift_apply, AddChar.one_apply] using h v
  let T := coefficientTranslation i v
  have hphase : ∀ A : MonicDegreePolynomial (ZMod p) n,
      monicPhase f (T A) = c * v + monicPhase f A := by
    intro A
    have haff := monicPhase_affine_last f rfl hpos n hn
    have hzero := haff A (A.coeff i)
    have htranslated := haff A (A.coeff i + v)
    change monicPhase f
        ⟨Function.update A.coeff i (A.coeff i + v)⟩ = _
    change monicPhase f
        ⟨Function.update A.coeff i (A.coeff i + v)⟩ = _ at htranslated
    change monicPhase f
        ⟨Function.update A.coeff i (A.coeff i)⟩ = _ at hzero
    rw [Function.update_eq_self] at hzero
    rw [htranslated, hzero]
    dsimp [c, d]
    ring
  have hweight : ∀ A : MonicDegreePolynomial (ZMod p) n,
      monicWeight psi f (T A) =
        psi (c * v) * monicWeight psi f A := by
    intro A
    unfold monicWeight
    rw [hphase A, psi.map_add_eq_mul]
  let S : ℂ := ∑ A : MonicDegreePolynomial (ZMod p) n,
    monicWeight psi f A
  have hsumInvariant :
      (∑ A : MonicDegreePolynomial (ZMod p) n,
          monicWeight psi f (T A)) = S := by
    exact (T.sum_comp (monicWeight psi f)).trans rfl
  have hscaled : psi (c * v) * S = S := by
    rw [Finset.mul_sum]
    calc
      (∑ A : MonicDegreePolynomial (ZMod p) n,
        psi (c * v) * monicWeight psi f A) =
          ∑ A : MonicDegreePolynomial (ZMod p) n,
            monicWeight psi f (T A) := by
        apply Finset.sum_congr rfl
        intro A _hA
        exact (hweight A).symm
      _ = S := hsumInvariant
  have hprod : (psi (c * v) - 1) * S = 0 := by
    rw [sub_mul, one_mul, hscaled, sub_self]
  have hS : S = 0 := (mul_eq_zero.mp hprod).resolve_left
    (sub_ne_zero.mpr hv)
  exact hS

end Stepanov
end TranslationalTilings
