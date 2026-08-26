import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.NatAbs
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.Analysis.Equidistribution

/-!
# An explicit Fejér separator on the unit circle

This file constructs the finite, mean-zero trigonometric polynomial used in
the polynomial-rigidity argument.  The proof expands the Fejér kernel as a
square of a finite geometric sum, obtains its circle-distance estimate from
Jordan's sine inequality, and computes the exact coefficient mass.

The exported separator has rationally controlled degree and coefficient mass.
Outside the prescribed ball it is real-valued and at least one, while its
constant Fourier coefficient vanishes.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- The positive Fejér-kernel order chosen at rational separation radius `eps`. -/
def separatorOrder (eps : ℚ) : ℕ :=
  max 1 (Int.toNat ⌈(1 : ℚ) / (2 * eps ^ 2)⌉)

/-- The Fourier degree of the Fejér separator at radius `eps`. -/
def separatorDegree (eps : ℚ) : ℕ := separatorOrder eps - 1

/-- A positive natural-number bound for the separator's coefficient `ℓ¹` mass. -/
def separatorL1NatBound (eps : ℚ) : ℕ :=
  max 1 (2 * separatorDegree eps)

/-- The triangular Fourier weight of the order-`N` Fejér kernel at frequency `k`. -/
def fejerWeight (N : ℕ) (k : ℤ) : ℚ :=
  if Int.natAbs k < N then 1 - (Int.natAbs k : ℚ) / N else 0

/-- The mean-zero Fourier coefficient of the separator centered at `c`. -/
noncomputable def fejerSeparatorCoeff
    (c : Torus) (eps : ℚ) (k : ℤ) : ℂ :=
  if k = 0 then 0 else
    -2 * (fejerWeight (separatorOrder eps) k : ℂ) *
      circlePhase ((-k) • c)

/-- The finite Fourier evaluation of the Fejér separator centered at `c`. -/
noncomputable def fejerSeparatorEval
    (c : Torus) (eps : ℚ) (x : Torus) : ℂ :=
  ∑ k ∈ Finset.Icc (-(separatorDegree eps : ℤ))
      (separatorDegree eps : ℤ),
    fejerSeparatorCoeff c eps k * circlePhase (k • x)

private theorem circlePhase_zsmul (k : ℤ) (x : Torus) :
    circlePhase (k • x) = circlePhase x ^ k := by
  rw [circlePhase, fourier_one, circlePhase, fourier_one,
    AddCircle.toCircle_zsmul, Circle.coe_zpow]

private theorem four_mul_norm_le_norm_circlePhase_sub_one (y : Torus) :
    4 * ‖y‖ ≤ ‖circlePhase y - 1‖ := by
  induction y using QuotientAddGroup.induction_on with
  | _ x =>
      let r : ℝ := x - (round x : ℝ)
      have hr : |r| ≤ 1 / 2 := by
        simpa [r, abs_sub_comm] using abs_sub_round x
      have hnorm : ‖((x : ℝ) : Torus)‖ = |r| := by
        rw [AddCircle.norm_eq]
        simp [r]
      have hcoe : ((x : ℝ) : Torus) = ((r : ℝ) : Torus) := by
        apply sub_eq_zero.mp
        rw [← AddCircle.coe_sub]
        exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
          ⟨round x, by simp [r]⟩
      rw [hnorm, hcoe, circlePhase, fourier_one, AddCircle.toCircle_apply_mk,
        Circle.coe_exp]
      simp only [div_one]
      rw [mul_comm ((2 * π * r : ℝ) : ℂ) Complex.I]
      rw [Complex.norm_exp_I_mul_ofReal_sub_one]
      have hj := Real.mul_abs_le_abs_sin
        (x := π * r) (by
          rw [abs_mul, abs_of_pos Real.pi_pos]
          nlinarith [Real.pi_pos])
      rw [abs_mul, abs_of_pos Real.pi_pos] at hj
      have hj' : 2 * |r| ≤ |Real.sin (π * r)| := by
        calc
          2 * |r| = 2 / π * (π * |r|) := by field_simp
          _ ≤ _ := hj
      rw [show 2 * π * r / 2 = π * r by ring]
      norm_num [norm_mul, Real.norm_eq_abs]
      linarith

private theorem sum_pairs_by_difference (N : ℕ) (hN : 0 < N)
    (f : ℤ → ℂ) :
    ∑ p ∈ (Finset.range N).product (Finset.range N),
        f ((p.1 : ℤ) - (p.2 : ℤ)) =
      ∑ k ∈ Finset.Icc (-((N - 1 : ℕ) : ℤ)) ((N - 1 : ℕ) : ℤ),
        ∑ _m ∈ Finset.range (N - Int.natAbs k), f k := by
  let toDiff : ℕ × ℕ → Sigma (fun _ : ℤ ↦ ℕ) := fun p ↦
    ⟨(p.1 : ℤ) - (p.2 : ℤ), min p.1 p.2⟩
  let fromDiff : Sigma (fun _ : ℤ ↦ ℕ) → ℕ × ℕ := fun p ↦
    if 0 ≤ p.1 then (p.2 + Int.natAbs p.1, p.2)
    else (p.2, p.2 + Int.natAbs p.1)
  rw [Finset.sum_sigma']
  apply Finset.sum_bij'
      (fun p _hp ↦ toDiff p) (fun p _hp ↦ fromDiff p)
  · rintro ⟨j, l⟩ hjl
    rcases Finset.mem_product.mp hjl with ⟨hj, hl⟩
    simp only [Finset.mem_range] at hj hl
    simp only [toDiff, Finset.mem_sigma, Finset.mem_Icc,
      Finset.mem_range]
    constructor
    · omega
    · by_cases hlj : l ≤ j
      · rw [min_eq_right hlj,
          Int.natAbs_natCast_sub_natCast_of_ge hlj]
        omega
      · have hjl : j ≤ l := Nat.le_of_not_ge hlj
        rw [min_eq_left hjl,
          Int.natAbs_natCast_sub_natCast_of_le hjl]
        omega
  · rintro ⟨k, m⟩ hkm
    simp only [Finset.mem_sigma, Finset.mem_Icc,
      Finset.mem_range] at hkm
    rcases hkm with ⟨hk, hm⟩
    have hmadd : m + Int.natAbs k < N := by omega
    simp only [fromDiff]
    split_ifs
    · apply Finset.mem_product.mpr
      simp only [Finset.mem_range]
      exact ⟨by omega, by omega⟩
    · apply Finset.mem_product.mpr
      simp only [Finset.mem_range]
      exact ⟨by omega, by omega⟩
  · rintro ⟨j, l⟩ hjl
    rcases Finset.mem_product.mp hjl with ⟨hj, hl⟩
    simp only [toDiff, fromDiff]
    by_cases hlj : l ≤ j
    · have hnonneg : (0 : ℤ) ≤ (j : ℤ) - (l : ℤ) := by omega
      simp only [hnonneg, if_true,
        Int.natAbs_natCast_sub_natCast_of_ge hlj]
      ext <;> omega
    · have hjl : j ≤ l := Nat.le_of_not_ge hlj
      have hneg : ¬ (0 : ℤ) ≤ (j : ℤ) - (l : ℤ) := by omega
      simp only [hneg, if_false,
        Int.natAbs_natCast_sub_natCast_of_le hjl]
      ext <;> omega
  · rintro ⟨k, m⟩ hkm
    simp only [fromDiff, toDiff]
    by_cases hk : 0 ≤ k
    · simp only [hk, if_true]
      have hab : (Int.natAbs k : ℤ) = k := by
        rw [Int.natCast_natAbs, abs_of_nonneg hk]
      ext
      · simp only [Nat.cast_add]
        rw [hab]
        omega
      · simp
    · simp only [hk, if_false]
      have hab : (Int.natAbs k : ℤ) = -k := by
        rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_ge hk)]
      ext
      · simp only [Nat.cast_add]
        rw [hab]
        omega
      · simp
  · rintro ⟨j, l⟩ hjl
    rfl

private theorem nat_mul_fejerWeight (N : ℕ) (k : ℤ)
    (hk : Int.natAbs k < N) :
    (N : ℚ) * fejerWeight N k = (N - Int.natAbs k : ℕ) := by
  rw [fejerWeight, if_pos hk]
  have hN : (N : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hk))
  rw [Nat.cast_sub hk.le]
  field_simp

private theorem fejer_sum_eq_pair_average (N : ℕ) (hN : 0 < N)
    (z : ℂ) :
    ∑ k ∈ Finset.Icc (-((N - 1 : ℕ) : ℤ)) ((N - 1 : ℕ) : ℤ),
        (fejerWeight N k : ℂ) * z ^ k =
      (N : ℂ)⁻¹ *
        ∑ p ∈ (Finset.range N).product (Finset.range N),
          z ^ ((p.1 : ℤ) - (p.2 : ℤ)) := by
  rw [sum_pairs_by_difference N hN]
  simp_rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have habs : Int.natAbs k < N := by
    simp only [Finset.mem_Icc] at hk
    have habs_le : (Int.natAbs k : ℤ) ≤ (N - 1 : ℕ) := by
      rw [Int.natCast_natAbs]
      exact abs_le.mpr ⟨by omega, hk.2⟩
    omega
  have hscale : (N : ℂ) * (fejerWeight N k : ℂ) =
      (N - Int.natAbs k : ℕ) := by
    exact_mod_cast nat_mul_fejerWeight N k habs
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  calc
    (fejerWeight N k : ℂ) * z ^ k =
        (N : ℂ)⁻¹ * ((N : ℂ) * (fejerWeight N k : ℂ)) * z ^ k := by
          field_simp
    _ = (N : ℂ)⁻¹ * ((N - Int.natAbs k : ℕ) * z ^ k) := by
          rw [hscale]
          ring

private theorem pair_phase_sum_eq_normSq (N : ℕ) (z : ℂ)
    (hz : ‖z‖ = 1) :
    ∑ p ∈ (Finset.range N).product (Finset.range N),
        z ^ ((p.1 : ℤ) - (p.2 : ℤ)) =
      (Complex.normSq (∑ j ∈ Finset.range N, z ^ j) : ℂ) := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  calc
    ∑ p ∈ (Finset.range N).product (Finset.range N),
        z ^ ((p.1 : ℤ) - (p.2 : ℤ)) =
        ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          z ^ ((j : ℤ) - (l : ℤ)) := by
            exact Finset.sum_product _ _ _
    _ = ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          z ^ j * starRingEnd ℂ (z ^ l) := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro l hl
            rw [zpow_natCast_sub_natCast₀ hz0, div_eq_mul_inv,
              ← inv_pow,
              Complex.inv_eq_conj hz, map_pow]
    _ = (∑ j ∈ Finset.range N, z ^ j) *
          starRingEnd ℂ (∑ l ∈ Finset.range N, z ^ l) := by
            rw [map_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
    _ = (Complex.normSq (∑ j ∈ Finset.range N, z ^ j) : ℂ) := by
          rw [Complex.mul_conj]

private theorem fejer_kernel_le_half (N : ℕ) (hN : 0 < N)
    (eps : ℝ) (heps : 0 < eps)
    (horder : 1 ≤ (N : ℝ) * (2 * eps ^ 2))
    (y : Torus) (hy : eps ≤ ‖y‖) :
    (N : ℝ)⁻¹ *
        Complex.normSq
          (∑ j ∈ Finset.range N, circlePhase y ^ j) ≤ 1 / 2 := by
  let z : ℂ := circlePhase y
  let A : ℂ := ∑ j ∈ Finset.range N, z ^ j
  have hz : ‖z‖ = 1 := by
    change ‖circlePhase y‖ = 1
    rw [circlePhase, fourier_one]
    exact Circle.norm_coe _
  have hgeom : A * (z - 1) = z ^ N - 1 := by
    simpa [A] using geom_sum_mul z N
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    calc
      ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz]; norm_num
  have hprod : ‖A‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    exact hnum
  have hchord : 4 * eps ≤ ‖z - 1‖ := by
    calc
      4 * eps ≤ 4 * ‖y‖ := by nlinarith
      _ ≤ ‖z - 1‖ := by
        simpa [z] using four_mul_norm_le_norm_circlePhase_sub_one y
  have hA : 4 * eps * ‖A‖ ≤ 2 := by
    calc
      4 * eps * ‖A‖ = ‖A‖ * (4 * eps) := by ring
      _ ≤ ‖A‖ * ‖z - 1‖ :=
        mul_le_mul_of_nonneg_left hchord (norm_nonneg A)
      _ ≤ 2 := hprod
  have hA_nonneg : 0 ≤ 4 * eps * ‖A‖ := by positivity
  have hA_sq : (4 * eps * ‖A‖) ^ 2 ≤ (2 : ℝ) ^ 2 :=
    (sq_le_sq₀ hA_nonneg (by positivity)).mpr hA
  have hnormSq : 2 * Complex.normSq A ≤ N := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg eps, sq_nonneg ‖A‖]
  change (N : ℝ)⁻¹ * Complex.normSq A ≤ 1 / 2
  rw [inv_mul_le_iff₀ (Nat.cast_pos.mpr hN)]
  nlinarith

private theorem separatorOrder_pos (eps : ℚ) : 0 < separatorOrder eps := by
  simp [separatorOrder]

private theorem separatorOrder_scale (eps : ℚ) (heps : 0 < eps) :
    1 ≤ (separatorOrder eps : ℝ) * (2 * (eps : ℝ) ^ 2) := by
  let q : ℚ := (1 : ℚ) / (2 * eps ^ 2)
  have hden : 0 < (2 * eps ^ 2 : ℚ) := by positivity
  have hqpos : 0 < q := div_pos zero_lt_one hden
  have hceil : q ≤ (⌈q⌉ : ℚ) := Int.le_ceil q
  have hceil0 : (0 : ℤ) ≤ ⌈q⌉ := Int.ceil_nonneg hqpos.le
  have hqnat : q ≤ (Int.toNat ⌈q⌉ : ℚ) := by
    calc
      q ≤ (⌈q⌉ : ℚ) := hceil
      _ = (Int.toNat ⌈q⌉ : ℚ) := by
        norm_cast
        exact (Int.toNat_of_nonneg hceil0).symm
  have hqN : q ≤ (separatorOrder eps : ℚ) :=
    hqnat.trans (by
      exact_mod_cast (le_max_right 1 (Int.toNat ⌈q⌉)))
  have hscaleQ : (1 : ℚ) ≤
      (separatorOrder eps : ℚ) * (2 * eps ^ 2) := by
    calc
      (1 : ℚ) = q * (2 * eps ^ 2) := by
        dsimp [q]
        field_simp
      _ ≤ (separatorOrder eps : ℚ) * (2 * eps ^ 2) :=
        mul_le_mul_of_nonneg_right hqN hden.le
  exact_mod_cast hscaleQ

private theorem fejerSeparatorEval_eq_kernel
    (c : Torus) (eps : ℚ) (x : Torus) :
    let N := separatorOrder eps
    let z := circlePhase (x - c)
    let A := ∑ j ∈ Finset.range N, z ^ j
    fejerSeparatorEval c eps x =
      -2 * ((N : ℂ)⁻¹ * (Complex.normSq A : ℂ) - 1) := by
  dsimp only
  let N := separatorOrder eps
  let z := circlePhase (x - c)
  let s := Finset.Icc (-((N - 1 : ℕ) : ℤ)) ((N - 1 : ℕ) : ℤ)
  have hN : 0 < N := separatorOrder_pos eps
  have hdegree : separatorDegree eps = N - 1 := rfl
  have hzero : (0 : ℤ) ∈ s := by
    simp [s]
  have hz : ‖z‖ = 1 := by
    change ‖circlePhase (x - c)‖ = 1
    rw [circlePhase, fourier_one]
    exact Circle.norm_coe _
  have hterm (k : ℤ) (hk : k ≠ 0) :
      fejerSeparatorCoeff c eps k * circlePhase (k • x) =
        -2 * (fejerWeight N k : ℂ) * z ^ k := by
    have hphase : circlePhase ((-k) • c) * circlePhase (k • x) = z ^ k := by
      calc
        circlePhase ((-k) • c) * circlePhase (k • x) =
            circlePhase ((-k) • c + k • x) :=
              (circlePhase_add _ _).symm
        _ = circlePhase (k • (x - c)) := by
              congr 1
              simp [sub_eq_add_neg, add_comm]
        _ = z ^ k := by
              exact circlePhase_zsmul k (x - c)
    rw [fejerSeparatorCoeff, if_neg hk]
    rw [mul_assoc, hphase]
  have heval : fejerSeparatorEval c eps x =
      -2 * ((∑ k ∈ s, (fejerWeight N k : ℂ) * z ^ k) - 1) := by
    calc
      fejerSeparatorEval c eps x =
          ∑ k ∈ s.erase 0,
            fejerSeparatorCoeff c eps k * circlePhase (k • x) := by
              rw [fejerSeparatorEval, hdegree]
              change (∑ k ∈ s,
                fejerSeparatorCoeff c eps k * circlePhase (k • x)) = _
              rw [← Finset.sum_erase_add s
                (fun k ↦ fejerSeparatorCoeff c eps k * circlePhase (k • x)) hzero]
              simp [fejerSeparatorCoeff]
      _ = ∑ k ∈ s.erase 0,
          -2 * (fejerWeight N k : ℂ) * z ^ k := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hterm k (Finset.ne_of_mem_erase hk)
      _ = -2 * ∑ k ∈ s.erase 0,
          (fejerWeight N k : ℂ) * z ^ k := by
            rw [Finset.mul_sum]
            simp only [mul_assoc]
      _ = -2 * ((∑ k ∈ s, (fejerWeight N k : ℂ) * z ^ k) - 1) := by
            rw [← Finset.sum_erase_add s
              (fun k ↦ (fejerWeight N k : ℂ) * z ^ k) hzero]
            simp [fejerWeight, hN]
  rw [heval]
  have hkernel := fejer_sum_eq_pair_average N hN z
  rw [pair_phase_sum_eq_normSq N z hz] at hkernel
  rw [hkernel]

private theorem fejerWeight_nonneg (N : ℕ) (hN : 0 < N) (k : ℤ) :
    0 ≤ fejerWeight N k := by
  rw [fejerWeight]
  split_ifs with hk
  · have hden : (0 : ℚ) < N := by exact_mod_cast hN
    have hratio : (Int.natAbs k : ℚ) / N ≤ 1 := by
      rw [div_le_one hden]
      exact_mod_cast hk.le
    linarith
  · exact le_rfl

private theorem sum_fejerWeight (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ Finset.Icc (-((N - 1 : ℕ) : ℤ)) ((N - 1 : ℕ) : ℤ),
      fejerWeight N k = N := by
  have h := fejer_sum_eq_pair_average N hN (1 : ℂ)
  norm_num [Finset.card_product] at h
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hrhs : (N : ℂ)⁻¹ * ((N : ℂ) * (N : ℂ)) = (N : ℂ) := by
    field_simp
  rw [hrhs] at h
  exact_mod_cast h

private theorem norm_fejerSeparatorCoeff_of_ne_zero
    (c : Torus) (eps : ℚ) (k : ℤ) (hk : k ≠ 0) :
    ‖fejerSeparatorCoeff c eps k‖ =
      2 * (fejerWeight (separatorOrder eps) k : ℝ) := by
  rw [fejerSeparatorCoeff, if_neg hk, norm_mul, norm_mul]
  have hphase : ‖circlePhase ((-k) • c)‖ = 1 := by
    rw [circlePhase, fourier_one]
    exact Circle.norm_coe _
  rw [hphase, mul_one]
  rw [Complex.norm_ratCast]
  norm_num only [norm_neg, Real.norm_eq_abs]
  rw [abs_of_nonneg (by
    exact_mod_cast (fejerWeight_nonneg
      (separatorOrder eps) (separatorOrder_pos eps) k))]
  norm_num

private theorem fejerSeparator_l1_le (c : Torus) (eps : ℚ) :
    (∑ k ∈ Finset.Icc (-(separatorDegree eps : ℤ))
        (separatorDegree eps : ℤ),
      ‖fejerSeparatorCoeff c eps k‖) ≤
        (separatorL1NatBound eps : ℝ) := by
  let D := separatorDegree eps
  let s := Finset.Icc (-(D : ℤ)) (D : ℤ)
  have hzero : (0 : ℤ) ∈ s := by simp [s]
  let N := separatorOrder eps
  have hN : 0 < N := separatorOrder_pos eps
  have hdegree : D = N - 1 := rfl
  have hweights : ∑ k ∈ s.erase 0, fejerWeight N k = D := by
    have hall := sum_fejerWeight N hN
    change (∑ k ∈ s, fejerWeight N k) = N at hall
    rw [← Finset.sum_erase_add s (fejerWeight N) hzero] at hall
    simp [fejerWeight, hN, hdegree] at hall ⊢
    linarith
  have hweightsR : ∑ k ∈ s.erase 0,
      (fejerWeight N k : ℝ) = D := by
    exact_mod_cast hweights
  calc
    (∑ k ∈ Finset.Icc (-(separatorDegree eps : ℤ))
        (separatorDegree eps : ℤ),
      ‖fejerSeparatorCoeff c eps k‖) =
        ∑ k ∈ s.erase 0, ‖fejerSeparatorCoeff c eps k‖ := by
          change (∑ k ∈ s, ‖fejerSeparatorCoeff c eps k‖) = _
          rw [← Finset.sum_erase_add s
            (fun k ↦ ‖fejerSeparatorCoeff c eps k‖) hzero]
          simp [fejerSeparatorCoeff]
    _ = ∑ k ∈ s.erase 0,
          2 * (fejerWeight N k : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact norm_fejerSeparatorCoeff_of_ne_zero c eps k
            (Finset.ne_of_mem_erase hk)
    _ = 2 * ∑ k ∈ s.erase 0,
          (fejerWeight N k : ℝ) := by rw [Finset.mul_sum]
    _ = (2 * D : ℕ) := by
          rw [hweightsR]
          norm_num
    _ ≤ (separatorL1NatBound eps : ℝ) := by
          exact_mod_cast (le_max_right 1 (2 * D))

/--
The Fejér separator has zero mean, degree at most `separatorDegree eps`, is
real and at least one off the ball of radius `eps` about `c`, and has
coefficient `ℓ¹` mass at most `separatorL1NatBound eps`.
-/
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
      (separatorL1NatBound eps : ℝ) := by
  have _hsmall := hsmall
  have hN : 0 < separatorOrder eps := separatorOrder_pos eps
  refine ⟨by simp [fejerSeparatorCoeff], ?_, ?_,
    fejerSeparator_l1_le c eps⟩
  · intro k hk
    rw [fejerSeparatorCoeff]
    split_ifs with hk0
    · rfl
    · have hcut : separatorOrder eps ≤ Int.natAbs k := by
        rw [separatorDegree] at hk
        omega
      rw [fejerWeight, if_neg (not_lt_of_ge hcut)]
      simp
  · intro x hx
    have hy : (eps : ℝ) ≤ ‖x - c‖ := by
      simp only [Metric.mem_ball] at hx
      rw [← dist_eq_norm]
      exact le_of_not_gt hx
    have hkernel : (separatorOrder eps : ℝ)⁻¹ *
        Complex.normSq
          (∑ j ∈ Finset.range (separatorOrder eps),
            circlePhase (x - c) ^ j) ≤ 1 / 2 := by
      exact fejer_kernel_le_half (separatorOrder eps) hN (eps : ℝ)
        (by exact_mod_cast heps) (separatorOrder_scale eps heps)
        (x - c) hy
    have heval := fejerSeparatorEval_eq_kernel c eps x
    dsimp only at heval
    rw [heval]
    constructor
    · norm_num
    · norm_num at ⊢
      nlinarith

end TranslationalTilings
