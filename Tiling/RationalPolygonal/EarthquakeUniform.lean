import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Factorial.Basic
import Tiling.RationalPolygonal.Earthquake

/-!
# Uniform periodic structure of earthquake plates

This module formalizes the pigeonhole and incomplete-orbit argument in paper Lemma 4.2.  The
uniform Greenfeld--Tao theorem is applied to finitely many auxiliary earthquake tilings on every
coset of one fixed finite-index lattice.  Repeated period choices force a quake-parallel period;
using the factorial of the number of directions makes that period independent of the plate and
the coset.  Complete directional orbits and the residual incomplete orbits then give a common
finite periodic partition of every canonical quake plate.
-/

open Set
open TranslationalTilings

namespace Tiling.RationalPolygonal

private theorem quantitative_lattice_index_ne_zero_local
    {F : Finset IntegerPlane} {ell : ℕ} (D : QuantitativeWeakPeriodData F ell) :
    D.lattice.index ≠ 0 := by
  let q := weakQ F ell
  let N := weakN D.direction
  let M := weakM D.direction
  let a := weakAvoidance D.direction
  let h₀ := D.direction ⟨0, D.number_pos⟩
  have haSpec := avoidanceVector_spec D.direction_ne_zero
  have hw₀ : wedge a h₀ ≠ 0 := by
    intro hw
    exact haSpec.2.1 ⟨0, D.number_pos⟩
      ((commensurable_iff_wedge_eq_zero haSpec.1
        (D.direction_ne_zero ⟨0, D.number_pos⟩)).2 hw)
  have hdet : wedge (weakSliceVector F ell D.direction)
      (((q * N * M : ℕ) : ℤ) • h₀) ≠ 0 := by
    rw [weakSliceVector, wedge_zsmul_left, wedge_zsmul_right]
    exact mul_ne_zero
      (by exact_mod_cast (Nat.ne_of_gt
        (Nat.mul_pos D.arithmetic.q_pos D.arithmetic.pairLCM_pos)))
      (mul_ne_zero
        (by exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos
          (Nat.mul_pos D.arithmetic.q_pos D.arithmetic.pairLCM_pos)
          D.arithmetic.avoidanceLCM_pos))) hw₀)
  change D.arithmetic.lattice.index ≠ 0
  rw [D.arithmetic.lattice_eq, weakLattice, index_generatedPair hdet]
  exact Int.natAbs_ne_zero.mpr hdet

private theorem quantitative_period_mem_local
    {F : Finset IntegerPlane} (D : QuantitativeWeakPeriodData F 1)
    (j : Fin D.numberOfDirections) :
    (D.multiplier : ℤ) • D.direction j ∈ D.lattice := by
  simpa using D.period_mem_lattice j

private theorem quantitative_period_ne_zero_local
    {F : Finset IntegerPlane} (D : QuantitativeWeakPeriodData F 1)
    (j : Fin D.numberOfDirections) :
    (D.multiplier : ℤ) • D.direction j ≠ 0 := by
  exact smul_ne_zero (Int.ofNat_ne_zero.mpr
    (Nat.ne_of_gt D.arithmetic.multiplier_pos)) (D.direction_ne_zero j)

private theorem quotientCoset_add_mem_iff_local
    (Λ : AddSubgroup IntegerPlane) (c : IntegerPlane ⧸ Λ)
    {p : IntegerPlane} (hp : p ∈ Λ) (x : IntegerPlane) :
    x + p ∈ quotientCoset Λ c ↔ x ∈ quotientCoset Λ c := by
  change QuotientAddGroup.mk' Λ (x + p) = c ↔ QuotientAddGroup.mk' Λ x = c
  have hp0 : QuotientAddGroup.mk' Λ p = 0 :=
    (QuotientAddGroup.eq_zero_iff p).2 hp
  rw [map_add, hp0, add_zero]

private noncomputable def quakeIndexedShift
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (k : Fin (D.numberOfDirections + 1)) : Set IntegerPlane :=
  quakeShiftedTranslations
    (quakeShiftExcept C (((D.lattice.index * k.val : ℕ) : ℤ)))

private theorem exists_period_on_quotientCoset
    {F : Finset IntegerPlane} {A : Set IntegerPlane}
    (D : QuantitativeWeakPeriodData F 1) (hvalid : D.ValidFor A)
    (c : IntegerPlane ⧸ D.lattice) :
    ∃ j : Fin D.numberOfDirections,
      DiscretePeriodicBy (A ∩ quotientCoset D.lattice c)
        ((D.multiplier : ℤ) • D.direction j) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective D.lattice c
  obtain ⟨j, hj⟩ := hvalid x
  refine ⟨j, ?_⟩
  intro y
  simpa [addCoset, quotientCoset, QuotientAddGroup.eq_iff_sub_mem] using hj y

private theorem exists_repeated_cosetPeriod
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (quakeIndexedShift D C k))
    (c : IntegerPlane ⧸ D.lattice) :
    ∃ (i j : Fin (D.numberOfDirections + 1))
        (r : Fin D.numberOfDirections),
      i.val < j.val ∧
      DiscretePeriodicBy (quakeIndexedShift D C i ∩ quotientCoset D.lattice c)
        ((D.multiplier : ℤ) • D.direction r) ∧
      DiscretePeriodicBy (quakeIndexedShift D C j ∩ quotientCoset D.lattice c)
        ((D.multiplier : ℤ) • D.direction r) := by
  classical
  let selected : Fin (D.numberOfDirections + 1) → Fin D.numberOfDirections :=
    fun k ↦ Classical.choose (exists_period_on_quotientCoset D (hvalid k) c)
  have hselected (k : Fin (D.numberOfDirections + 1)) :
      DiscretePeriodicBy (quakeIndexedShift D C k ∩ quotientCoset D.lattice c)
        ((D.multiplier : ℤ) • D.direction (selected k)) :=
    Classical.choose_spec (exists_period_on_quotientCoset D (hvalid k) c)
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt selected (by simp)
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact ⟨i, j, selected i, hijlt, hselected i, heq ▸ hselected j⟩
  · exact ⟨j, i, selected j, hjilt, hselected j, heq.symm ▸ hselected i⟩

private structure QuakeCosetRepeatData
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (c : IntegerPlane ⧸ D.lattice) where
  lower : Fin (D.numberOfDirections + 1)
  upper : Fin (D.numberOfDirections + 1)
  periodIndex : Fin D.numberOfDirections
  lower_lt_upper : lower.val < upper.val
  lower_periodic : DiscretePeriodicBy
    (quakeIndexedShift D C lower ∩ quotientCoset D.lattice c)
      ((D.multiplier : ℤ) • D.direction periodIndex)
  upper_periodic : DiscretePeriodicBy
    (quakeIndexedShift D C upper ∩ quotientCoset D.lattice c)
      ((D.multiplier : ℤ) • D.direction periodIndex)

private noncomputable def chosenQuakeCosetRepeatData
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (quakeIndexedShift D C k))
    (c : IntegerPlane ⧸ D.lattice) : QuakeCosetRepeatData D C c := by
  classical
  apply Classical.choice
  obtain ⟨i, j, r, hij, hi, hj⟩ := exists_repeated_cosetPeriod D C hvalid c
  exact ⟨⟨i, j, r, hij, hi, hj⟩⟩

private noncomputable def quakeUniformPeriod
    {F : Finset IntegerPlane} (D : QuantitativeWeakPeriodData F 1)
    (v : IntegerPlane) : IntegerPlane :=
  ((D.lattice.index * D.numberOfDirections.factorial : ℕ) : ℤ) • v

private theorem quakeUniformPeriod_ne_zero
    {F : Finset IntegerPlane} (D : QuantitativeWeakPeriodData F 1)
    {v : IntegerPlane} (hv : v ≠ 0) : quakeUniformPeriod D v ≠ 0 := by
  apply smul_ne_zero
  · exact Int.ofNat_ne_zero.mpr (Nat.mul_ne_zero
      (quantitative_lattice_index_ne_zero_local D) (Nat.factorial_ne_zero _))
  · exact hv

private theorem indexedShift_smul_mem_lattice
    {F : Finset IntegerPlane} (D : QuantitativeWeakPeriodData F 1)
    (v : IntegerPlane) (k : Fin (D.numberOfDirections + 1)) :
    (((D.lattice.index * k.val : ℕ) : ℤ) • v) ∈ D.lattice := by
  have hbase : (D.lattice.index : ℤ) • v ∈ D.lattice := by
    simpa using D.lattice.nsmul_index_mem v
  have hk := D.lattice.zsmul_mem hbase (k.val : ℤ)
  convert hk using 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Nat.cast_mul]
  ring

private theorem chosen_incomplete_periodic_uniform
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (hzero : 0 ∈ F) (hT : TilesUniverse F T)
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (quakeIndexedShift D C k))
    (c : IntegerPlane ⧸ D.lattice) :
    let R := chosenQuakeCosetRepeatData D C hvalid c
    DiscretePeriodicBy
      (quakeIncompleteOrbit C D.lattice c
        ((D.multiplier : ℤ) • D.direction R.periodIndex))
      (quakeUniformPeriod D v) := by
  dsimp only
  let R := chosenQuakeCosetRepeatData D C hvalid c
  let p := (D.multiplier : ℤ) • D.direction R.periodIndex
  let a : ℤ := (D.lattice.index * R.lower.val : ℕ)
  let b : ℤ := (D.lattice.index * R.upper.val : ℕ)
  have hlocal : DiscretePeriodicBy
      (quakeIncompleteOrbit C D.lattice c p) ((b - a) • v) := by
    apply quakeIncompleteOrbit_periodic_of_repeated_cosetPeriod
      hzero hT C D.lattice c p
    · exact quantitative_period_mem_local D R.periodIndex
    · exact indexedShift_smul_mem_lattice D v R.lower
    · exact indexedShift_smul_mem_lattice D v R.upper
    · simpa [quakeIndexedShift, a, p] using R.lower_periodic
    · simpa [quakeIndexedShift, b, p] using R.upper_periodic
  let d := R.upper.val - R.lower.val
  have hdpos : 0 < d := Nat.sub_pos_of_lt R.lower_lt_upper
  have hdle : d ≤ D.numberOfDirections := by
    omega
  obtain ⟨z, hz⟩ := Nat.dvd_factorial hdpos hdle
  have hmultiple : quakeUniformPeriod D v = (z : ℤ) • ((b - a) • v) := by
    have hzInt : (D.numberOfDirections.factorial : ℤ) = (d : ℤ) * (z : ℤ) := by
      exact_mod_cast hz
    have hdInt : (d : ℤ) = (R.upper.val : ℤ) - (R.lower.val : ℤ) := by
      dsimp [d]
      rw [Nat.cast_sub (Nat.le_of_lt R.lower_lt_upper)]
    dsimp [quakeUniformPeriod, a, b]
    rw [hzInt, hdInt]
    rw [sub_smul, smul_sub]
    module
  rw [hmultiple]
  exact hlocal.zsmul z

private noncomputable def quakeCompletePart
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (quakeIndexedShift D C k))
    (j : Fin D.numberOfDirections) : Set IntegerPlane :=
  {x | ∃ c : IntegerPlane ⧸ D.lattice,
    (chosenQuakeCosetRepeatData D C hvalid c).periodIndex = j ∧
    x ∈ quakePlateTranslations C ∧ x ∈ quotientCoset D.lattice c ∧
    ∀ n : ℤ, x + n • ((D.multiplier : ℤ) • D.direction j) ∈
      quakePlateTranslations C}

private noncomputable def quakeResidualPart
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (quakeIndexedShift D C k)) : Set IntegerPlane :=
  quakePlateTranslations C \ ⋃ j, quakeCompletePart D C hvalid j

private theorem quakeCompletePart_periodic
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (quakeIndexedShift D C k))
    (j : Fin D.numberOfDirections) :
    DiscretePeriodicBy (quakeCompletePart D C hvalid j)
      ((D.multiplier : ℤ) • D.direction j) := by
  let p := (D.multiplier : ℤ) • D.direction j
  have hp := quantitative_period_mem_local D j
  intro x
  constructor
  · rintro ⟨c, hcj, hxC, hxc, hfull⟩
    refine ⟨c, hcj, ?_, (quotientCoset_add_mem_iff_local D.lattice c hp x).mp hxc, ?_⟩
    · have hminus := hfull (-1)
      have heq : x + p + (-1 : ℤ) • p = x := by module
      rwa [heq] at hminus
    · intro n
      have hn := hfull (n - 1)
      have heq : x + p + (n - 1) • p = x + n • p := by
        rw [sub_smul]
        module
      rwa [heq] at hn
  · rintro ⟨c, hcj, hxC, hxc, hfull⟩
    have hxP : x + p ∈ quakePlateTranslations C := by
      simpa only [one_smul] using hfull 1
    refine ⟨c, hcj, hxP, (quotientCoset_add_mem_iff_local D.lattice c hp x).mpr hxc, ?_⟩
    intro n
    have hn := hfull (n + 1)
    have heq : x + p + n • p = x + (n + 1) • p := by
      rw [add_smul]
      module
    change x + p + n • p ∈ quakePlateTranslations C
    rw [heq]
    exact hn

private theorem mem_quakeResidualPart_iff_exists_incomplete
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (quakeIndexedShift D C k)) (x : IntegerPlane) :
    x ∈ quakeResidualPart D C hvalid ↔
      ∃ c : IntegerPlane ⧸ D.lattice,
        x ∈ quakeIncompleteOrbit C D.lattice c
          ((D.multiplier : ℤ) • D.direction
            (chosenQuakeCosetRepeatData D C hvalid c).periodIndex) := by
  classical
  constructor
  · intro hx
    let c := QuotientAddGroup.mk' D.lattice x
    let R := chosenQuakeCosetRepeatData D C hvalid c
    refine ⟨c, hx.1, rfl, ?_⟩
    by_cases hfull : ∀ n : ℤ,
        x + n • ((D.multiplier : ℤ) • D.direction R.periodIndex) ∈
          quakePlateTranslations C
    · exfalso
      apply hx.2
      apply Set.mem_iUnion.mpr
      exact ⟨R.periodIndex, c, rfl, hx.1, rfl, hfull⟩
    · exact not_forall.mp hfull
  · rintro ⟨c, hxC, hxc, n, hn⟩
    refine ⟨hxC, ?_⟩
    intro hxUnion
    obtain ⟨j, c', hc'j, hxC', hxc', hfull⟩ := Set.mem_iUnion.mp hxUnion
    have hcc' : c = c' := hxc.symm.trans hxc'
    have hselected : (chosenQuakeCosetRepeatData D C hvalid c).periodIndex = j := by
      rw [hcc']
      exact hc'j
    apply hn
    simpa [hselected] using hfull n

private theorem quakeResidualPart_periodic
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (hzero : 0 ∈ F) (hT : TilesUniverse F T)
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (quakeIndexedShift D C k)) :
    DiscretePeriodicBy (quakeResidualPart D C hvalid) (quakeUniformPeriod D v) := by
  intro x
  rw [mem_quakeResidualPart_iff_exists_incomplete D C hvalid,
    mem_quakeResidualPart_iff_exists_incomplete D C hvalid]
  constructor
  · rintro ⟨c, hx⟩
    refine ⟨c, ?_⟩
    exact (chosen_incomplete_periodic_uniform hzero hT D C hvalid c x).mp hx
  · rintro ⟨c, hx⟩
    refine ⟨c, ?_⟩
    exact (chosen_incomplete_periodic_uniform hzero hT D C hvalid c x).mpr hx

/-- A common finite period list and a corresponding periodic partition of every canonical quake
plate.  A later normalization merges any period commensurable with the quake direction. -/
structure UniformQuakePeriodicCover
    (F : Finset IntegerPlane) (T : Set IntegerPlane) (v : IntegerPlane) where
  /-- Number of common period labels. -/
  numberOfParts : ℕ
  /-- At least one period label is available. -/
  number_pos : 0 < numberOfParts
  /-- The piece with a given common label inside each quake plate. -/
  part : QuakePlate F T v → Fin numberOfParts → Set IntegerPlane
  /-- The period attached to each common label. -/
  period : Fin numberOfParts → IntegerPlane
  /-- Every common period is nonzero. -/
  period_ne_zero : ∀ j, period j ≠ 0
  /-- Every labeled piece is invariant under its common period. -/
  periodic_part : ∀ C j, DiscretePeriodicBy (part C j) (period j)
  /-- The labeled pieces of each fixed plate are pairwise disjoint. -/
  pairwiseDisjoint : ∀ C, Set.PairwiseDisjoint Set.univ (part C)
  /-- The labeled pieces cover exactly the corresponding quake plate. -/
  iUnion_parts : ∀ C, (⋃ j, part C j) = quakePlateTranslations C

private noncomputable def rawQuakePart
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (quakeIndexedShift D C k)) :
    Fin (D.numberOfDirections + 1) → Set IntegerPlane :=
  Fin.cases (quakeResidualPart D C hvalid) (quakeCompletePart D C hvalid)

private noncomputable def rawQuakePeriod
    {F : Finset IntegerPlane} (D : QuantitativeWeakPeriodData F 1)
    (v : IntegerPlane) : Fin (D.numberOfDirections + 1) → IntegerPlane :=
  Fin.cases (quakeUniformPeriod D v)
    (fun j ↦ (D.multiplier : ℤ) • D.direction j)

private theorem rawQuakePart_pairwiseDisjoint
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (quakeIndexedShift D C k)) :
    Set.PairwiseDisjoint Set.univ (rawQuakePart D C hvalid) := by
  classical
  have hdisj : ∀ i j : Fin (D.numberOfDirections + 1), i ≠ j →
      Disjoint (rawQuakePart D C hvalid i) (rawQuakePart D C hvalid j) := by
    intro i
    refine Fin.cases (motive := fun i ↦ ∀ j, i ≠ j →
      Disjoint (rawQuakePart D C hvalid i) (rawQuakePart D C hvalid j)) ?_ ?_ i
    · intro j
      refine Fin.cases ?_ (fun j _ ↦ ?_) j
      · intro hij
        exact (hij rfl).elim
      · change Disjoint (quakeResidualPart D C hvalid) (quakeCompletePart D C hvalid j)
        rw [Set.disjoint_left]
        intro x hxResidual hxComplete
        exact hxResidual.2 (Set.mem_iUnion.mpr ⟨j, hxComplete⟩)
    · intro i j
      refine Fin.cases ?_ (fun j hij ↦ ?_) j
      · intro _
        change Disjoint (quakeCompletePart D C hvalid i) (quakeResidualPart D C hvalid)
        rw [Set.disjoint_left]
        intro x hxComplete hxResidual
        exact hxResidual.2 (Set.mem_iUnion.mpr ⟨i, hxComplete⟩)
      · change Disjoint (quakeCompletePart D C hvalid i) (quakeCompletePart D C hvalid j)
        rw [Set.disjoint_left]
        intro x hxi hxj
        obtain ⟨c, hci, _hxiC, hxic, _⟩ := hxi
        obtain ⟨c', hc'j, _hxjC, hxjc', _⟩ := hxj
        have hcc' : c = c' := hxic.symm.trans hxjc'
        have hij' : i = j := by
          apply Fin.ext
          have hselected :
              (chosenQuakeCosetRepeatData D C hvalid c).periodIndex = j := by
            rw [hcc']
            exact hc'j
          exact congrArg Fin.val (hci.symm.trans hselected)
        exact hij (congrArg Fin.succ hij')
  intro i _ j _ hij
  exact hdisj i j hij

private theorem rawQuakePart_iUnion
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (D : QuantitativeWeakPeriodData F 1) (C : QuakePlate F T v)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (quakeIndexedShift D C k)) :
    (⋃ j, rawQuakePart D C hvalid j) = quakePlateTranslations C := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
    refine Fin.cases (motive := fun j ↦ x ∈ rawQuakePart D C hvalid j →
      x ∈ quakePlateTranslations C) ?_ (fun i hi ↦ ?_) j hxj
    · intro hresidual
      exact hresidual.1
    · obtain ⟨c, _hci, hxC, _hxc, _hfull⟩ := hi
      exact hxC
  · intro hxC
    by_cases hxComplete : x ∈ ⋃ j, quakeCompletePart D C hvalid j
    · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxComplete
      exact Set.mem_iUnion.mpr ⟨Fin.succ j, hxj⟩
    · exact Set.mem_iUnion.mpr ⟨0, hxC, hxComplete⟩

/-- Uniform periodic plate cover for normalized nonsingleton lattice tiles.  The common first
period is the factorial quake period; the remaining periods are the uniform Greenfeld--Tao
directions. -/
theorem exists_uniformQuakePeriodicCover_normalized
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (hzero : 0 ∈ F) (hcard : 1 < F.card) (hv : v ≠ 0)
    (hT : TilesUniverse F T) : Nonempty (UniformQuakePeriodicCover F T v) := by
  classical
  obtain ⟨D, hD⟩ := exists_quantitativeWeakPeriodData
    (F := F) (ell := 1) Nat.one_pos hzero hcard
  have huniv : SetScalarPeriodic 1 (Set.univ : Set IntegerPlane) := by
    intro x z
    simp
  let hvalid : ∀ C : QuakePlate F T v,
      ∀ k : Fin (D.numberOfDirections + 1),
        D.ValidFor (quakeIndexedShift D C k) := by
    intro C k
    apply hD Set.univ (quakeIndexedShift D C k) huniv
    exact tilesUniverse_quakeShiftedTranslations hT _
  refine ⟨{
    numberOfParts := D.numberOfDirections + 1
    number_pos := Nat.succ_pos _
    part := fun C ↦ rawQuakePart D C (hvalid C)
    period := rawQuakePeriod D v
    period_ne_zero := ?_
    periodic_part := ?_
    pairwiseDisjoint := ?_
    iUnion_parts := ?_
  }⟩
  · intro j
    refine Fin.cases (quakeUniformPeriod_ne_zero D hv) (fun i ↦ ?_) j
    exact quantitative_period_ne_zero_local D i
  · intro C j
    refine Fin.cases (quakeResidualPart_periodic hzero hT D C (hvalid C))
      (fun i ↦ quakeCompletePart_periodic D C (hvalid C) i) j
  · intro C
    exact rawQuakePart_pairwiseDisjoint D C (hvalid C)
  · intro C
    exact rawQuakePart_iUnion D C (hvalid C)

end Tiling.RationalPolygonal
