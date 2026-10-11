import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Ring.Periodic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.AtTopBot.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.OneDimensional

universe u

structure PeriodicIntEnumeration (E : Set ℝ) (p : ℝ) where
  count : ℕ
  count_pos : 0 < count
  point : ℤ → ℝ
  point_strictMono : StrictMono point
  point_range : Set.range point = E
  point_period : ∀ j : ℤ,
    point (j + Int.ofNat count) = point j + p
  fundamental_eq :
    E ∩ Ico 0 p = Set.range (fun i : Fin count ↦ point (Int.ofNat i))

private theorem periodic_mem_of_vadd_eq {S : Set ℝ} {a : ℝ}
    (h : a +ᵥ S = S) : Function.Periodic (fun x => x ∈ S) a := by
  intro x
  apply propext
  constructor
  · intro hx
    have hx' : a + x ∈ S := by simpa [add_comm] using hx
    rw [← h] at hx'
    obtain ⟨y, hy, hay⟩ := hx'
    have : y = x := by simpa using hay
    simpa [this] using hy
  · intro hx
    have hx' : a + x ∈ a +ᵥ S := ⟨x, hx, rfl⟩
    rw [h] at hx'
    simpa [add_comm] using hx'

theorem periodicIntEnumeration_exists
    (E : Set ℝ) (p : ℝ) (hp : 0 < p) (hE : E.Nonempty)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (hperiod : p +ᵥ E = E) : Nonempty (PeriodicIntEnumeration E p) := by
  classical
  let F : Set ℝ := E ∩ Ico 0 p
  have hFfin : F.Finite := hlocal (Ico 0 p) (Metric.isBounded_Ico 0 p)
  have hFnonempty : F.Nonempty := by
    obtain ⟨x, hx⟩ := hE
    let q : ℤ := Int.floor (x / p)
    let r : ℝ := x - (q : ℝ) * p
    have hr_eq : r = p * Int.fract (x / p) := by
      dsimp [r, q]
      rw [Int.fract]
      field_simp [hp.ne']
    have hr0 : 0 ≤ r := by
      rw [hr_eq]
      exact mul_nonneg hp.le (Int.fract_nonneg _)
    have hrp : r < p := by
      rw [hr_eq]
      nlinarith [Int.fract_lt_one (x / p)]
    have hrE : r ∈ E := by
      have hfun := (periodic_mem_of_vadd_eq hperiod).zsmul (-q)
      have hmem := (hfun x).mpr hx
      simpa [r, q, zsmul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc] using hmem
    exact ⟨r, hrE, hr0, hrp⟩
  let A : Finset ℝ := hFfin.toFinset
  have hAco : (A : Set ℝ) = F := hFfin.coe_toFinset
  have hAne : A.Nonempty := by
    obtain ⟨x, hx⟩ := hFnonempty
    refine ⟨x, ?_⟩
    change x ∈ (A : Set ℝ)
    exact hAco.symm ▸ hx
  have hApos : 0 < A.card := Finset.card_pos.mpr hAne
  let n : ℕ := A.card
  have hn : 0 < n := hApos
  have hsort : n = A.card := rfl
  let e : Fin n ≃o A := Finset.orderIsoOfFin A hsort.symm
  let f : Fin n → ℝ := fun i => (e i : ℝ)
  have hf_strict : StrictMono f := by
    intro i j hij
    exact e.strictMono hij
  have hf_mem (i : Fin n) : f i ∈ E ∧ 0 ≤ f i ∧ f i < p := by
    have hiA : f i ∈ (A : Set ℝ) := (e i).property
    have hiF : f i ∈ F := hAco ▸ hiA
    exact hiF
  let nn : ℤ := Int.ofNat n
  have hnn : 0 < nn := by
    change (0 : ℤ) < (n : ℤ)
    exact_mod_cast hn
  have hnn_ne : nn ≠ 0 := ne_of_gt hnn
  let rem (j : ℤ) : Fin n :=
    ⟨(j % nn).toNat, by
      apply (Int.toNat_lt (Int.emod_nonneg _ hnn_ne)).2
      simpa [nn] using (Int.emod_lt_of_pos j hnn)
    ⟩
  let quot (j : ℤ) : ℤ := j / nn
  let point (j : ℤ) : ℝ := f (rem j) + (quot j : ℝ) * p
  have hrem_nonneg (j : ℤ) : 0 ≤ j % nn := Int.emod_nonneg _ hnn_ne
  have hrem_lt (j : ℤ) : j % nn < nn := Int.emod_lt_of_pos _ hnn
  have hdecomp (j : ℤ) : j % nn + nn * (j / nn) = j :=
    Int.emod_add_mul_ediv j nn
  have hpoint_mem (j : ℤ) : point j ∈ E := by
    have hbase : f (rem j) ∈ E := (hf_mem _).1
    have hfun := (periodic_mem_of_vadd_eq hperiod).zsmul (quot j)
    have hmem := (hfun (f (rem j))).mpr hbase
    simpa [point, quot, zsmul_eq_mul, add_comm, add_left_comm, add_assoc] using hmem
  have hpoint_succ (j : ℤ) : point j < point (j + 1) := by
    let r := j % nn
    let q := j / nn
    have hr0 : 0 ≤ r := hrem_nonneg j
    have hrlt : r < nn := hrem_lt j
    have hcases : r + 1 < nn ∨ r + 1 = nn := by omega
    rcases hcases with hlt | heq
    · have hqr : (j + 1) / nn = q ∧ (j + 1) % nn = r + 1 := by
        apply (Int.ediv_emod_unique hnn).2
        constructor
        · rw [show j + 1 = (r + 1) + nn * q by
            have hj : j = r + nn * q := by
              dsimp [r, q]
              exact (hdecomp j).symm
            rw [hj]
            ring]
        · exact ⟨by omega, hlt⟩
      have hrem_lt' : rem j < rem (j + 1) := by
        apply Fin.mk_lt_mk.mpr
        rw [hqr.2]
        change r.toNat < (r + 1).toNat
        exact (Int.toNat_lt_toNat (by omega : 0 < r + 1)).2 (by omega)
      dsimp [point, quot]
      rw [hqr.1]
      have hfi := hf_strict hrem_lt'
      linarith
    · have hqr : (j + 1) / nn = q + 1 ∧ (j + 1) % nn = 0 := by
        apply (Int.ediv_emod_unique hnn).2
        constructor
        · have hj : j = r + nn * q := by
            dsimp [r, q]
            exact (hdecomp j).symm
          calc
            0 + nn * (q + 1) = nn * (q + 1) := by simp
            _ = nn + nn * q := by ring
            _ = (r + 1) + nn * q := by rw [heq]
            _ = j + 1 := by rw [hj]; ring
        · exact ⟨le_refl _, by omega⟩
      have hrem_eq : rem (j + 1) = ⟨0, hn⟩ := by
        apply Fin.ext
        dsimp [rem]
        rw [hqr.2, Int.toNat_zero]
      have hcross : f (rem j) < f (⟨0, hn⟩) + p := by
        have hlast := (hf_mem (rem j)).2.2
        have hzero := (hf_mem (⟨0, hn⟩)).2.1
        linarith
      dsimp [point, quot]
      rw [hqr.1, hrem_eq]
      rw [show j / nn = q by rfl]
      change f (rem j) + (q : ℝ) * p <
        f (⟨0, hn⟩ : Fin n) + ((q + 1 : ℤ) : ℝ) * p
      push_cast
      linarith
  have hpoint_strict : StrictMono point := strictMono_int_of_lt_succ hpoint_succ
  have hpoint_period (j : ℤ) : point (j + Int.ofNat n) = point j + p := by
    change point (j + nn) = point j + p
    have hqr : (j + nn) / nn = j / nn + 1 ∧ (j + nn) % nn = j % nn := by
      constructor
      · rw [show j + nn = j + 1 * nn by ring, Int.add_mul_ediv_right _ _ hnn_ne]
      · exact Int.add_emod_right _ _
    have hrem_eq : rem (j + nn) = rem j := by
      apply Fin.ext
      dsimp [rem]
      rw [hqr.2]
    dsimp [point, quot]
    rw [hqr.1, hrem_eq]
    push_cast
    ring
  have hpoint_nat (i : Fin n) : point (Int.ofNat i) = f i := by
    have hi0 : 0 ≤ (Int.ofNat i : ℤ) := Int.natCast_nonneg _
    have hin : (Int.ofNat i : ℤ) < nn := by
      dsimp [nn]
      exact_mod_cast i.isLt
    have hq : (Int.ofNat i : ℤ) / nn = 0 := Int.ediv_eq_zero_of_lt hi0 hin
    have hr : (Int.ofNat i : ℤ) % nn = (Int.ofNat i : ℤ) :=
      Int.emod_eq_of_lt hi0 hin
    have hrem : rem (Int.ofNat i) = i := by
      apply Fin.ext
      dsimp [rem]
      change ((Int.ofNat (i : ℕ) % nn).toNat = (i : ℕ))
      rw [hr]
      simp
    change f (rem (Int.ofNat i)) +
      (((Int.ofNat i : ℤ) / nn : ℤ) : ℝ) * p = f i
    rw [hq, hrem]
    simp
  have hpoint_range : Set.range point = E := by
    apply Set.Subset.antisymm
    · rintro y ⟨j, rfl⟩
      exact hpoint_mem j
    · intro y hy
      let q : ℤ := Int.floor (y / p)
      let r : ℝ := y - (q : ℝ) * p
      have hr_eq : r = p * Int.fract (y / p) := by
        dsimp [r, q]
        rw [Int.fract]
        field_simp [hp.ne']
      have hr0 : 0 ≤ r := by
        rw [hr_eq]
        exact mul_nonneg hp.le (Int.fract_nonneg _)
      have hrp : r < p := by
        rw [hr_eq]
        nlinarith [Int.fract_lt_one (y / p)]
      have hrE : r ∈ E := by
        have hfun := (periodic_mem_of_vadd_eq hperiod).zsmul (-q)
        have hmem := (hfun y).mpr hy
        simpa [r, q, zsmul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc] using hmem
      have hi : ∃ i : Fin n, f i = r := by
        have hrA : r ∈ (A : Set ℝ) := hAco ▸ ⟨hrE, hr0, hrp⟩
        obtain ⟨i, hi⟩ := e.surjective ⟨r, hrA⟩
        exact ⟨i, congrArg Subtype.val hi⟩
      obtain ⟨i, hiEq⟩ := hi
      let iZ : ℤ := Int.ofNat i
      let j : ℤ := iZ + nn * q
      have hi0 : 0 ≤ iZ := by
        dsimp [iZ]
        exact Int.natCast_nonneg _
      have hin : iZ < nn := by
        dsimp [iZ, nn]
        exact_mod_cast i.isLt
      have hjqr : j / nn = q ∧ j % nn = iZ := by
        apply (Int.ediv_emod_unique hnn).2
        constructor
        · dsimp [j]
        · exact ⟨hi0, hin⟩
      have hremj : rem j = i := by
        apply Fin.ext
        dsimp [rem]
        rw [hjqr.2]
        dsimp [iZ]
      refine ⟨j, ?_⟩
      dsimp [point, quot]
      rw [hjqr.1, hremj]
      rw [hiEq]
      dsimp [r, q]
      ring
  have hfund : E ∩ Ico 0 p = Set.range (fun i : Fin n ↦ point (Int.ofNat i)) := by
    apply Set.Subset.antisymm
    · rintro y ⟨hy, hy0, hyp⟩
      have hrA : y ∈ (A : Set ℝ) := by
        exact hAco.symm ▸ ⟨hy, hy0, hyp⟩
      obtain ⟨i, hi⟩ := e.surjective ⟨y, hrA⟩
      refine ⟨i, ?_⟩
      have hiEq : f i = y := congrArg Subtype.val hi
      exact (hpoint_nat i).trans hiEq
    · intro y
      rintro ⟨i, hi⟩
      rw [← hi]
      change point (Int.ofNat i) ∈ E ∩ Ico 0 p
      rw [hpoint_nat i]
      exact ⟨(hf_mem i).1, (hf_mem i).2⟩
  exact ⟨⟨n, hn, point, hpoint_strict, hpoint_range, hpoint_period, hfund⟩⟩
end Tiling.AxisParallel.OneDimensional
