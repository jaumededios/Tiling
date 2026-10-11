import Tiling.AxisParallel.OneDimensional.FiniteInterval.IntervalGeometry

/-!
# Finite endpoint coding

A finite positive alphabet of consecutive gaps gives uniform finite candidates
in every bounded window anchored at an endpoint.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function Set
noncomputable section
namespace Tiling.AxisParallel.OneDimensional.FiniteInterval

def ConsecutiveIn (E : Set ℝ) (x y : ℝ) : Prop :=
  x ∈ E ∧ y ∈ E ∧ x < y ∧ Disjoint E (Set.Ioo x y)

structure EndpointChain (E : Set ℝ) (x y : ℝ) where
  length : ℕ
  point : Fin (length + 1) → ℝ
  first : point 0 = x
  last : point (Fin.last length) = y
  consecutive : ∀ i : Fin length,
    ConsecutiveIn E (point i.castSucc) (point i.succ)

theorem endpointChain_nonempty
    {E : Set ℝ}
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    {x y : ℝ} (hx : x ∈ E) (hy : y ∈ E) (hxy : x ≤ y) :
    Nonempty (EndpointChain E x y) := by
  let S : Finset ℝ := (hlocal (Icc x y) (Metric.isBounded_Icc x y)).toFinset
  have hxS : x ∈ S := by simp [S, hx, hxy]
  have hyS : y ∈ S := by simp [S, hy, hxy]
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨x, hxS⟩
  obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 := by
    exact ⟨S.card - 1, (Nat.sub_add_cancel hcard).symm⟩
  let e : Fin (k + 1) ≃o S := Finset.orderIsoOfFin S hk
  let point : Fin (k + 1) → ℝ := fun i => (e i : ℝ)
  have hpoint_mem (i : Fin (k + 1)) : point i ∈ S := (e i).property
  have hfirst : point 0 = x := by
    apply le_antisymm
    · obtain ⟨i, hi⟩ := e.surjective ⟨x, hxS⟩
      have hei : (e i : ℝ) = x := congrArg Subtype.val hi
      rw [← hei]
      exact_mod_cast e.monotone (Fin.zero_le i)
    · have : point 0 ∈ E ∩ Icc x y := by simpa [S] using hpoint_mem 0
      have := this.2.1
      simpa [point, S] using this
  have hlast : point (Fin.last k) = y := by
    apply le_antisymm
    · have : point (Fin.last k) ∈ E ∩ Icc x y := by
        simpa [S] using hpoint_mem (Fin.last k)
      have := this.2.2
      simpa [point, S] using this
    · obtain ⟨i, hi⟩ := e.surjective ⟨y, hyS⟩
      have hei : (e i : ℝ) = y := congrArg Subtype.val hi
      rw [← hei]
      exact_mod_cast e.monotone (Fin.le_last i)
  refine ⟨⟨k, point, hfirst, hlast, ?_⟩⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : point i.castSucc ∈ E ∩ Icc x y := by simpa [S] using hpoint_mem i.castSucc
    exact this.1
  · have : point i.succ ∈ E ∩ Icc x y := by simpa [S] using hpoint_mem i.succ
    exact this.1
  · exact e.strictMono Fin.castSucc_lt_succ
  · rw [Set.disjoint_left]
    intro z hzE hzIoo
    have hzS : z ∈ S := by
      have hleft_mem : point i.castSucc ∈ E ∩ Icc x y := by
        simpa [S] using hpoint_mem i.castSucc
      have hright_mem : point i.succ ∈ E ∩ Icc x y := by
        simpa [S] using hpoint_mem i.succ
      simpa [S] using
        (show z ∈ E ∩ Icc x y from
          ⟨hzE, ⟨le_trans hleft_mem.2.1 (le_of_lt hzIoo.1),
            le_trans (le_of_lt hzIoo.2) hright_mem.2.2⟩⟩)
    obtain ⟨j, hj⟩ := e.surjective ⟨z, hzS⟩
    have hij : i.castSucc < j := by
      apply (e.lt_iff_lt).mp
      rw [hj]
      exact hzIoo.1
    have hji : j < i.succ := by
      apply (e.lt_iff_lt).mp
      rw [hj]
      exact hzIoo.2
    have hij' : i.val < j.val := by exact_mod_cast hij
    have hji' : j.val < i.val + 1 := by exact_mod_cast hji
    omega

theorem endpointChain_telescope
    {E : Set ℝ} {x y : ℝ} (C : EndpointChain E x y) :
    ∑ i : Fin C.length,
      (C.point i.succ - C.point i.castSucc) = y - x := by
  classical
  let f : ℕ → ℝ := fun i =>
    C.point ⟨min i C.length, Nat.lt_succ_of_le (Nat.min_le_right i C.length)⟩
  calc
    ∑ i : Fin C.length, (C.point i.succ - C.point i.castSucc) =
        ∑ i ∈ Finset.range C.length, (f (i + 1) - f i) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hil : i < C.length := Finset.mem_range.mp hi
      simp [f, hil, Nat.min_eq_left hil.le]
    _ = f C.length - f 0 := Finset.sum_range_sub f C.length
    _ = y - x := by
      have hlast :
          (⟨C.length, Nat.lt_succ_self C.length⟩ : Fin (C.length + 1)) =
            Fin.last C.length := Fin.ext rfl
      simp only [f, Nat.min_self, Nat.zero_le, Nat.min_eq_left]
      rw [hlast, C.last]
      simp [C.first]

theorem endpointChain_length_le_of_gapAlphabet
    {A E : Set ℝ} {x y delta : ℝ}
    (_hdelta : 0 < delta)
    (hAmin : ∀ a ∈ A, delta ≤ a)
    (hgap : ∀ u v, ConsecutiveIn E u v → v - u ∈ A)
    (C : EndpointChain E x y) :
    (C.length : ℝ) * delta ≤ y - x := by
  rw [← endpointChain_telescope C]
  calc
    (C.length : ℝ) * delta = ∑ _i : Fin C.length, delta := by simp
    _ ≤ ∑ i : Fin C.length, (C.point i.succ - C.point i.castSucc) := by
      exact Finset.sum_le_sum fun i _ => hAmin _ (hgap _ _ (C.consecutive i))

theorem finite_candidates_of_gapAlphabet
    {A : Set ℝ}
    (hAfinite : A.Finite)
    (hApositive : ∀ a ∈ A, 0 < a)
    (anchor radius : ℝ) (_hradius : 0 ≤ radius) :
    ∃ F : Finset ℝ, ∀ (E : Set ℝ),
      (∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite) →
      anchor ∈ E →
      (∀ x y, ConsecutiveIn E x y → y - x ∈ A) →
      E ∩ Icc (anchor - radius) (anchor + radius) ⊆ (F : Set ℝ) := by
  classical
  by_cases hA : A.Nonempty
  · let _ : Fintype A := hAfinite.fintype
    let AFin : Finset ℝ := hAfinite.toFinset
    have hAFin : AFin.Nonempty := by simpa [AFin] using hA
    let delta : ℝ := AFin.min' hAFin
    have hdelta_mem : delta ∈ A := by
      simpa [delta, AFin] using AFin.min'_mem hAFin
    have hdelta : 0 < delta := hApositive delta hdelta_mem
    have hdelta_min : ∀ a ∈ A, delta ≤ a := by
      intro a ha
      exact AFin.min'_le a (by simpa [AFin] using ha)
    obtain ⟨N, hN⟩ := exists_nat_gt (radius / delta)
    have hradiusN : radius < (N : ℝ) * delta := by
      have := (mul_lt_mul_of_pos_right hN hdelta)
      field_simp at this
      simpa [mul_comm] using this
    let Code := Σ k : Fin (N + 1), (Fin k.val → A)
    let total : Code → ℝ := fun u => ∑ i, ((u.2 i : A) : ℝ)
    let sums : Finset ℝ := Finset.univ.image total
    let F : Finset ℝ :=
      (sums.image fun s => anchor + s) ∪ (sums.image fun s => anchor - s)
    refine ⟨F, ?_⟩
    intro E hlocal hanchor hgap z hz
    rcases hz with ⟨hzE, hzlo, hzhi⟩
    by_cases haz : anchor ≤ z
    · obtain ⟨C⟩ := endpointChain_nonempty hlocal hanchor hzE haz
      have hbound : (C.length : ℝ) * delta ≤ radius := by
        calc
          (C.length : ℝ) * delta ≤ z - anchor :=
            endpointChain_length_le_of_gapAlphabet hdelta hdelta_min hgap C
          _ ≤ radius := by linarith
      have hlen : C.length < N + 1 := by
        have hreal : (C.length : ℝ) < (N : ℝ) := by nlinarith
        have : C.length < N := by exact_mod_cast hreal
        omega
      let code : Code :=
        ⟨⟨C.length, hlen⟩,
          fun i => ⟨C.point i.succ - C.point i.castSucc,
            hgap _ _ (C.consecutive i)⟩⟩
      have hsum : total code = z - anchor := by
        simpa [total, code] using endpointChain_telescope C
      have hmem : z - anchor ∈ sums := by
        rw [← hsum]
        exact Finset.mem_image.mpr ⟨code, Finset.mem_univ _, rfl⟩
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨z - anchor, hmem, by ring⟩
    · have hza : z ≤ anchor := le_of_not_ge haz
      obtain ⟨C⟩ := endpointChain_nonempty hlocal hzE hanchor hza
      have hbound : (C.length : ℝ) * delta ≤ radius := by
        calc
          (C.length : ℝ) * delta ≤ anchor - z :=
            endpointChain_length_le_of_gapAlphabet hdelta hdelta_min hgap C
          _ ≤ radius := by linarith
      have hlen : C.length < N + 1 := by
        have hreal : (C.length : ℝ) < (N : ℝ) := by nlinarith
        have : C.length < N := by exact_mod_cast hreal
        omega
      let code : Code :=
        ⟨⟨C.length, hlen⟩,
          fun i => ⟨C.point i.succ - C.point i.castSucc,
            hgap _ _ (C.consecutive i)⟩⟩
      have hsum : total code = anchor - z := by
        simpa [total, code] using endpointChain_telescope C
      have hmem : anchor - z ∈ sums := by
        rw [← hsum]
        exact Finset.mem_image.mpr ⟨code, Finset.mem_univ _, rfl⟩
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨anchor - z, hmem, by ring⟩
  · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    refine ⟨{anchor}, ?_⟩
    intro E hlocal hanchor hgap z hz
    have hzE := hz.1
    have haz : anchor = z := by
      rcases le_total anchor z with haz | hza
      · obtain ⟨C⟩ := endpointChain_nonempty hlocal hanchor hzE haz
        by_cases hlen : C.length = 0
        · have hfin : (0 : Fin (C.length + 1)) = Fin.last C.length := by
            apply Fin.ext
            simp [hlen]
          calc
            anchor = C.point 0 := C.first.symm
            _ = C.point (Fin.last C.length) := congrArg C.point hfin
            _ = z := C.last
        · let i : Fin C.length := ⟨0, Nat.pos_of_ne_zero hlen⟩
          have := hgap _ _ (C.consecutive i)
          rw [hAempty] at this
          exact this.elim
      · obtain ⟨C⟩ := endpointChain_nonempty hlocal hzE hanchor hza
        by_cases hlen : C.length = 0
        · have hfin : (0 : Fin (C.length + 1)) = Fin.last C.length := by
            apply Fin.ext
            simp [hlen]
          calc
            anchor = C.point (Fin.last C.length) := C.last.symm
            _ = C.point 0 := congrArg C.point hfin.symm
            _ = z := C.first
        · let i : Fin C.length := ⟨0, Nat.pos_of_ne_zero hlen⟩
          have := hgap _ _ (C.consecutive i)
          rw [hAempty] at this
          exact this.elim
    simp [haz]

end Tiling.AxisParallel.OneDimensional.FiniteInterval
