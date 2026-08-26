import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Factorial.Basic
import Tiling.RationalPolygonal.Earthquake

set_option linter.style.header false

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

/-- The exact output of paper Lemma 4.2: every quake plate is partitioned using one common finite
family of pairwise incommensurable nonzero periods. -/
structure UniformQuakePeriodicDecomposition
    (F : Finset IntegerPlane) (T : Set IntegerPlane) (v : IntegerPlane) where
  /-- Number of common, pairwise-incommensurable period labels. -/
  numberOfParts : ℕ
  /-- At least one period label is available. -/
  number_pos : 0 < numberOfParts
  /-- The piece with a given common label inside each quake plate. -/
  part : QuakePlate F T v → Fin numberOfParts → Set IntegerPlane
  /-- The common period attached to each label. -/
  period : Fin numberOfParts → IntegerPlane
  /-- Every common period is nonzero. -/
  period_ne_zero : ∀ j, period j ≠ 0
  /-- Distinct common period labels are incommensurable. -/
  pairwise_incommensurable : PairwiseIncommensurable period
  /-- Every labeled piece is invariant under its common period. -/
  periodic_part : ∀ C j, DiscretePeriodicBy (part C j) (period j)
  /-- The labeled pieces of each fixed plate are pairwise disjoint. -/
  pairwiseDisjoint : ∀ C, Set.PairwiseDisjoint Set.univ (part C)
  /-- The labeled pieces cover exactly the corresponding quake plate. -/
  iUnion_parts : ∀ C, (⋃ j, part C j) = quakePlateTranslations C

private noncomputable def quakeGraphIsoOfEq
    {F F' : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (h : quakeGraph F T v = quakeGraph F' T v) :
    quakeGraph F T v ≃g quakeGraph F' T v where
  toEquiv := Equiv.refl T
  map_rel_iff' := by
    intro a b
    change (quakeGraph F' T v).Adj a b ↔ (quakeGraph F T v).Adj a b
    rw [← h]

private theorem mem_quakePlateTranslations_isoOfEq
    {F F' : Finset IntegerPlane} {T : Set IntegerPlane} {v t : IntegerPlane}
    (h : quakeGraph F T v = quakeGraph F' T v)
    (C : QuakePlate F T v) :
    t ∈ quakePlateTranslations ((quakeGraphIsoOfEq h).connectedComponentEquiv C) ↔
      t ∈ quakePlateTranslations C := by
  constructor
  · rintro ⟨ht, hcomp⟩
    refine ⟨ht, ?_⟩
    change (quakeGraph F' T v).connectedComponentMk
        ((quakeGraphIsoOfEq h) (⟨t, ht⟩ : T)) =
      C.map (quakeGraphIsoOfEq h).toHom at hcomp
    exact SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mp hcomp
  · rintro ⟨ht, hcomp⟩
    refine ⟨ht, ?_⟩
    change (quakeGraph F' T v).connectedComponentMk
        ((quakeGraphIsoOfEq h) (⟨t, ht⟩ : T)) =
      C.map (quakeGraphIsoOfEq h).toHom
    exact SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mpr hcomp

/-- Transport a uniform plate decomposition across an equality of earthquake graphs on the same
translation set. -/
noncomputable def UniformQuakePeriodicDecomposition.transportGraph
    {F F' : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (D : UniformQuakePeriodicDecomposition F T v)
    (h : quakeGraph F T v = quakeGraph F' T v) :
    UniformQuakePeriodicDecomposition F' T v where
  numberOfParts := D.numberOfParts
  number_pos := D.number_pos
  part C j := D.part ((quakeGraphIsoOfEq h).connectedComponentEquiv.symm C) j
  period := D.period
  period_ne_zero := D.period_ne_zero
  pairwise_incommensurable := D.pairwise_incommensurable
  periodic_part C j := D.periodic_part _ j
  pairwiseDisjoint C := D.pairwiseDisjoint _
  iUnion_parts C := by
    rw [D.iUnion_parts]
    ext t
    exact mem_quakePlateTranslations_isoOfEq h.symm C

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

private noncomputable def rawUniformQuakePeriodicCover
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (hzero : 0 ∈ F) (hv : v ≠ 0) (hT : TilesUniverse F T)
    (D : QuantitativeWeakPeriodData F 1)
    (hvalid : ∀ C : QuakePlate F T v,
      ∀ k : Fin (D.numberOfDirections + 1),
        D.ValidFor (quakeIndexedShift D C k)) :
    UniformQuakePeriodicCover F T v where
  numberOfParts := D.numberOfDirections + 1
  number_pos := Nat.succ_pos _
  part := fun C ↦ rawQuakePart D C (hvalid C)
  period := rawQuakePeriod D v
  period_ne_zero := by
    intro j
    refine Fin.cases (quakeUniformPeriod_ne_zero D hv) (fun i ↦ ?_) j
    exact quantitative_period_ne_zero_local D i
  periodic_part := by
    intro C j
    refine Fin.cases (quakeResidualPart_periodic hzero hT D C (hvalid C))
      (fun i ↦ quakeCompletePart_periodic D C (hvalid C) i) j
  pairwiseDisjoint := by
    intro C
    exact rawQuakePart_pairwiseDisjoint D C (hvalid C)
  iUnion_parts := by
    intro C
    exact rawQuakePart_iUnion D C (hvalid C)

private theorem quantitative_period_pairwise_incommensurable
    {F : Finset IntegerPlane} (D : QuantitativeWeakPeriodData F 1) :
    PairwiseIncommensurable
      (fun j ↦ (D.multiplier : ℤ) • D.direction j) := by
  intro i j hij hcomm
  have hi0 := quantitative_period_ne_zero_local D i
  have hj0 := quantitative_period_ne_zero_local D j
  have hw := (commensurable_iff_wedge_eq_zero hi0 hj0).mp hcomm
  rw [wedge_zsmul_left, wedge_zsmul_right] at hw
  have hm : (D.multiplier : ℤ) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.ne_of_gt D.arithmetic.multiplier_pos)
  have hwdirection : wedge (D.direction i) (D.direction j) = 0 := by
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left hm)).resolve_left hm
  exact D.pairwise_incommensurable i j hij
    ((commensurable_iff_wedge_eq_zero (D.direction_ne_zero i)
      (D.direction_ne_zero j)).mpr hwdirection)

private theorem commensurable_symm_local {u w : IntegerPlane} :
    Commensurable u w → Commensurable w u := by
  rintro ⟨a, b, ha, hb, hab⟩
  exact ⟨b, a, hb, ha, hab.symm⟩

private theorem commensurable_trans_local {u w z : IntegerPlane} :
    Commensurable u w → Commensurable w z → Commensurable u z := by
  rintro ⟨a, b, ha, hb, hab⟩ ⟨c, d, hc, hd, hcd⟩
  refine ⟨c * a, b * d, mul_ne_zero hc ha, mul_ne_zero hb hd, ?_⟩
  calc
    (c * a) • u = c • (a • u) := by rw [mul_smul]
    _ = c • (b • w) := by rw [hab]
    _ = b • (c • w) := by rw [smul_smul, smul_smul, mul_comm]
    _ = b • (d • z) := by rw [hcd]
    _ = (b * d) • z := by rw [mul_smul]

private theorem commensurable_period_quake_of_uniformPeriod
    {F : Finset IntegerPlane} (D : QuantitativeWeakPeriodData F 1)
    {v p : IntegerPlane} (hv : v ≠ 0) (hp : p ≠ 0)
    (hcomm : Commensurable (quakeUniformPeriod D v) p) :
    Commensurable p v := by
  have hH0 := quakeUniformPeriod_ne_zero D hv
  have hw := (commensurable_iff_wedge_eq_zero hH0 hp).mp hcomm
  rw [quakeUniformPeriod, wedge_zsmul_left] at hw
  have hc : ((D.lattice.index * D.numberOfDirections.factorial : ℕ) : ℤ) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.mul_ne_zero
      (quantitative_lattice_index_ne_zero_local D) (Nat.factorial_ne_zero _))
  have hvp : wedge v p = 0 := (mul_eq_zero.mp hw).resolve_left hc
  have hpv : wedge p v = 0 := by rw [wedge_swap, hvp, neg_zero]
  exact (commensurable_iff_wedge_eq_zero hp hv).mpr hpv

private noncomputable def uniformQuakePeriodicDecomposition_of_no_parallel
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (hzero : 0 ∈ F) (hv : v ≠ 0) (hT : TilesUniverse F T)
    (D : QuantitativeWeakPeriodData F 1)
    (hvalid : ∀ C : QuakePlate F T v,
      ∀ k : Fin (D.numberOfDirections + 1),
        D.ValidFor (quakeIndexedShift D C k))
    (hnone : ∀ j : Fin D.numberOfDirections,
      ¬ Commensurable ((D.multiplier : ℤ) • D.direction j) v) :
    UniformQuakePeriodicDecomposition F T v := by
  let R := rawUniformQuakePeriodicCover hzero hv hT D hvalid
  have hpair : PairwiseIncommensurable (rawQuakePeriod D v) := by
    intro i
    refine Fin.cases (motive := fun i ↦ ∀ j, i ≠ j →
      ¬ Commensurable (rawQuakePeriod D v i) (rawQuakePeriod D v j)) ?_ ?_ i
    · intro j
      refine Fin.cases ?_ (fun j _ hcomm ↦ ?_) j
      · intro hij
        exact (hij rfl).elim
      · exact hnone j (commensurable_period_quake_of_uniformPeriod D hv
          (quantitative_period_ne_zero_local D j) hcomm)
    · intro i j
      refine Fin.cases ?_ (fun j hij hcomm ↦ ?_) j
      · intro _ hcomm
        exact hnone i (commensurable_period_quake_of_uniformPeriod D hv
          (quantitative_period_ne_zero_local D i) (commensurable_symm_local hcomm))
      · apply quantitative_period_pairwise_incommensurable D i j
        · intro hij'
          exact hij (congrArg Fin.succ hij')
        · exact hcomm
  exact {
    numberOfParts := R.numberOfParts
    number_pos := R.number_pos
    part := R.part
    period := R.period
    period_ne_zero := R.period_ne_zero
    pairwise_incommensurable := hpair
    periodic_part := R.periodic_part
    pairwiseDisjoint := R.pairwiseDisjoint
    iUnion_parts := R.iUnion_parts
  }

private noncomputable def uniformQuakePeriodicDecomposition_of_parallel
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (hzero : 0 ∈ F) (hv : v ≠ 0) (hT : TilesUniverse F T)
    (D : QuantitativeWeakPeriodData F 1)
    (hvalid : ∀ C : QuakePlate F T v,
      ∀ k : Fin (D.numberOfDirections + 1),
        D.ValidFor (quakeIndexedShift D C k))
    (j₀ : Fin D.numberOfDirections)
    (hj₀ : Commensurable ((D.multiplier : ℤ) • D.direction j₀) v) :
    UniformQuakePeriodicDecomposition F T v := by
  classical
  apply Classical.choice
  let p : Fin D.numberOfDirections → IntegerPlane :=
    fun j ↦ (D.multiplier : ℤ) • D.direction j
  let H₀ := quakeUniformPeriod D v
  let c : ℤ := ((D.lattice.index * D.numberOfDirections.factorial : ℕ) : ℤ)
  have hj₀copy := hj₀
  obtain ⟨a, b, ha, hb, hab⟩ := hj₀
  let H₁ : IntegerPlane := b • H₀
  have hc : c ≠ 0 := by
    exact Int.ofNat_ne_zero.mpr (Nat.mul_ne_zero
      (quantitative_lattice_index_ne_zero_local D) (Nat.factorial_ne_zero _))
  have hH₀ : H₀ ≠ 0 := quakeUniformPeriod_ne_zero D hv
  have hH₁ : H₁ ≠ 0 := smul_ne_zero hb hH₀
  have hH₁eq : H₁ = (c * a) • p j₀ := by
    dsimp [H₁, H₀, quakeUniformPeriod, c, p]
    calc
      b • ((D.lattice.index * D.numberOfDirections.factorial : ℕ) : ℤ) • v =
          c • (b • v) := by rw [smul_smul, smul_smul, mul_comm]
      _ = c • (a • ((D.multiplier : ℤ) • D.direction j₀)) := by rw [hab]
      _ = (c * a) • ((D.multiplier : ℤ) • D.direction j₀) := by rw [mul_smul]
  have hH₁v : Commensurable H₁ v := by
    refine ⟨1, b * c, one_ne_zero, mul_ne_zero hb hc, ?_⟩
    rw [one_smul]
    change b • (c • v) = (b * c) • v
    rw [smul_smul]
  have hparallel_unique (j : Fin D.numberOfDirections)
      (hj : Commensurable (p j) v) : j = j₀ := by
    by_contra hne
    exact quantitative_period_pairwise_incommensurable D j j₀ hne
      (commensurable_trans_local hj (commensurable_symm_local hj₀copy))
  let newPart : QuakePlate F T v → Fin D.numberOfDirections → Set IntegerPlane :=
    fun C j ↦ if j = j₀ then
      rawQuakePart D C (hvalid C) 0 ∪ rawQuakePart D C (hvalid C) (Fin.succ j₀)
    else rawQuakePart D C (hvalid C) (Fin.succ j)
  let newPeriod : Fin D.numberOfDirections → IntegerPlane :=
    fun j ↦ if j = j₀ then H₁ else p j
  have hperiod_ne_zero (j : Fin D.numberOfDirections) : newPeriod j ≠ 0 := by
    by_cases hj : j = j₀
    · simpa [newPeriod, hj] using hH₁
    · simpa [newPeriod, hj, p] using quantitative_period_ne_zero_local D j
  have hperiodic (C : QuakePlate F T v) (j : Fin D.numberOfDirections) :
      DiscretePeriodicBy (newPart C j) (newPeriod j) := by
    by_cases hj : j = j₀
    · subst j
      have hresidual := quakeResidualPart_periodic hzero hT D C (hvalid C)
      have hcomplete := quakeCompletePart_periodic D C (hvalid C) j₀
      have hresidualH₁ : DiscretePeriodicBy
          (rawQuakePart D C (hvalid C) 0) H₁ := by
        simpa [rawQuakePart, H₁, H₀] using hresidual.zsmul b
      have hcompleteH₁ : DiscretePeriodicBy
          (rawQuakePart D C (hvalid C) (Fin.succ j₀)) H₁ := by
        rw [hH₁eq]
        simpa [rawQuakePart, p] using hcomplete.zsmul (c * a)
      intro x
      simp only [newPart, newPeriod, if_pos]
      constructor
      · rintro (hx | hx)
        · exact Or.inl ((hresidualH₁ x).mp hx)
        · exact Or.inr ((hcompleteH₁ x).mp hx)
      · rintro (hx | hx)
        · exact Or.inl ((hresidualH₁ x).mpr hx)
        · exact Or.inr ((hcompleteH₁ x).mpr hx)
    · simpa [newPart, newPeriod, hj, rawQuakePart, p] using
        quakeCompletePart_periodic D C (hvalid C) j
  have hpair : PairwiseIncommensurable newPeriod := by
    intro i j hij hcomm
    by_cases hi : i = j₀
    · subst i
      have hj : j ≠ j₀ := by intro hj; exact hij hj.symm
      have hcomm' : Commensurable H₁ (p j) := by
        simpa [newPeriod, hj] using hcomm
      have hpjv := commensurable_trans_local (commensurable_symm_local hcomm') hH₁v
      exact hj (hparallel_unique j hpjv)
    · by_cases hj : j = j₀
      · subst j
        have hcomm' : Commensurable (p i) H₁ := by
          simpa [newPeriod, hi] using hcomm
        have hpiv := commensurable_trans_local hcomm' hH₁v
        exact hi (hparallel_unique i hpiv)
      · exact quantitative_period_pairwise_incommensurable D i j hij
          (by simpa [newPeriod, hi, hj, p] using hcomm)
  have hdisjoint (C : QuakePlate F T v) :
      Set.PairwiseDisjoint Set.univ (newPart C) := by
    have hraw := rawQuakePart_pairwiseDisjoint D C (hvalid C)
    intro i _ j _ hij
    change Disjoint (newPart C i) (newPart C j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    by_cases hi : i = j₀
    · subst i
      have hj : j ≠ j₀ := by intro hj; exact hij hj.symm
      simp only [newPart, if_pos, hj, if_false] at hxi hxj
      rcases hxi with hxi | hxi
      · exact (Set.disjoint_left.mp
          (hraw (Set.mem_univ 0) (Set.mem_univ (Fin.succ j))
            (Ne.symm (Fin.succ_ne_zero j)))) hxi hxj
      · exact (Set.disjoint_left.mp
          (hraw (Set.mem_univ (Fin.succ j₀)) (Set.mem_univ (Fin.succ j))
            (by simpa using hj.symm))) hxi hxj
    · by_cases hj : j = j₀
      · subst j
        simp only [newPart, hi, if_false, if_pos] at hxi hxj
        rcases hxj with hxj | hxj
        · exact (Set.disjoint_left.mp
            (hraw (Set.mem_univ (Fin.succ i)) (Set.mem_univ 0)
              (Fin.succ_ne_zero i))) hxi hxj
        · exact (Set.disjoint_left.mp
            (hraw (Set.mem_univ (Fin.succ i)) (Set.mem_univ (Fin.succ j₀))
              (by simpa using hi))) hxi hxj
      · simp only [newPart, hi, hj, if_false] at hxi hxj
        exact (Set.disjoint_left.mp
          (hraw (Set.mem_univ (Fin.succ i)) (Set.mem_univ (Fin.succ j))
            (by simpa using hij))) hxi hxj
  have hunion (C : QuakePlate F T v) :
      (⋃ j, newPart C j) = quakePlateTranslations C := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      by_cases hj : j = j₀
      · subst j
        simp only [newPart, if_pos] at hxj
        rcases hxj with hxj | hxj
        · have hall := rawQuakePart_iUnion D C (hvalid C)
          rw [← hall]
          exact Set.mem_iUnion.mpr ⟨0, hxj⟩
        · have hall := rawQuakePart_iUnion D C (hvalid C)
          rw [← hall]
          exact Set.mem_iUnion.mpr ⟨Fin.succ j₀, hxj⟩
      · have hall := rawQuakePart_iUnion D C (hvalid C)
        rw [← hall]
        exact Set.mem_iUnion.mpr ⟨Fin.succ j, by simpa [newPart, hj] using hxj⟩
    · intro hx
      have hall := rawQuakePart_iUnion D C (hvalid C)
      rw [← hall] at hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      refine Fin.cases (motive := fun j ↦ x ∈ rawQuakePart D C (hvalid C) j →
        x ∈ ⋃ j, newPart C j) ?_ (fun j hxj ↦ ?_) j hxj
      · intro hxzero
        apply Set.mem_iUnion.mpr
        refine ⟨j₀, ?_⟩
        simp only [newPart, if_pos]
        exact Or.inl hxzero
      · by_cases hj : j = j₀
        · subst j
          apply Set.mem_iUnion.mpr
          refine ⟨j₀, ?_⟩
          simp only [newPart, if_pos]
          exact Or.inr hxj
        · exact Set.mem_iUnion.mpr ⟨j, by simpa [newPart, hj] using hxj⟩
  exact ⟨{
    numberOfParts := D.numberOfDirections
    number_pos := D.number_pos
    part := newPart
    period := newPeriod
    period_ne_zero := hperiod_ne_zero
    pairwise_incommensurable := hpair
    periodic_part := hperiodic
    pairwiseDisjoint := hdisjoint
    iUnion_parts := hunion
  }⟩

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
  exact ⟨rawUniformQuakePeriodicCover hzero hv hT D hvalid⟩

/-- **Paper Lemma 4.2, normalized nonsingleton form.**  For a tile containing the origin, every
canonical quake plate admits a partition using the same finite family of pairwise
incommensurable nonzero lattice periods. -/
theorem exists_uniformQuakePeriodicDecomposition_normalized
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (hzero : 0 ∈ F) (hcard : 1 < F.card) (hv : v ≠ 0)
    (hT : TilesUniverse F T) :
    Nonempty (UniformQuakePeriodicDecomposition F T v) := by
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
  by_cases hparallel : ∃ j : Fin D.numberOfDirections,
      Commensurable ((D.multiplier : ℤ) • D.direction j) v
  · obtain ⟨j₀, hj₀⟩ := hparallel
    exact ⟨uniformQuakePeriodicDecomposition_of_parallel
      hzero hv hT D hvalid j₀ hj₀⟩
  · have hnone : ∀ j : Fin D.numberOfDirections,
        ¬ Commensurable ((D.multiplier : ℤ) • D.direction j) v :=
      not_exists.mp hparallel
    exact ⟨uniformQuakePeriodicDecomposition_of_no_parallel
      hzero hv hT D hvalid hnone⟩

private theorem exists_uniformQuakePeriodicDecomposition_singleton_zero
    {T : Set IntegerPlane} {v : IntegerPlane} (hv : v ≠ 0)
    (hT : TilesUniverse ({0} : Finset IntegerPlane) T) :
    Nonempty (UniformQuakePeriodicDecomposition ({0} : Finset IntegerPlane) T v) := by
  classical
  refine ⟨{
    numberOfParts := 1
    number_pos := Nat.one_pos
    part := fun C _ ↦ quakePlateTranslations C
    period := fun _ ↦ v
    period_ne_zero := fun _ ↦ hv
    pairwise_incommensurable := ?_
    periodic_part := ?_
    pairwiseDisjoint := ?_
    iUnion_parts := ?_
  }⟩
  · intro i j hij
    exact hij (Subsingleton.elim i j) |>.elim
  · intro C _
    have hcarrier : discreteCarrier ({0} : Finset IntegerPlane)
        (quakePlateTranslations C) = quakePlateTranslations C := by
      ext x
      simp [discreteCarrier]
    rw [← hcarrier]
    exact quakePlateCarrier_periodic hT C
  · intro C i _ j _ hij
    exact hij (Subsingleton.elim i j) |>.elim
  · intro C
    ext x
    simp

/-- Paper Lemma 4.2 for every normalized finite tile.  The singleton case is handled directly;
all nonsingleton tiles use the uniform Greenfeld--Tao/pigeonhole construction. -/
theorem exists_uniformQuakePeriodicDecomposition_of_zero_mem
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (hzero : 0 ∈ F) (hv : v ≠ 0) (hT : TilesUniverse F T) :
    Nonempty (UniformQuakePeriodicDecomposition F T v) := by
  have hFpos : 0 < F.card := Finset.card_pos.mpr ⟨0, hzero⟩
  by_cases hcard : F.card = 1
  · obtain ⟨f, hF⟩ := Finset.card_eq_one.mp hcard
    have hf : f = 0 := by
      rw [hF] at hzero
      have h0f : 0 = f := by simpa using hzero
      exact h0f.symm
    subst f
    subst F
    exact exists_uniformQuakePeriodicDecomposition_singleton_zero hv hT
  · exact exists_uniformQuakePeriodicDecomposition_normalized hzero (by omega) hv hT

/-- **Paper Lemma 4.2.** Every exact planar lattice tiling by a nonempty finite tile has one
common finite list of pairwise incommensurable nonzero periods which partitions every canonical
earthquake plate.  A chosen tile point is subtracted to reduce to the normalized theorem; this
does not change the earthquake graph. -/
theorem exists_uniformQuakePeriodicDecomposition
    {F : Finset IntegerPlane} {T : Set IntegerPlane} {v : IntegerPlane}
    (hF : F.Nonempty) (hv : v ≠ 0) (hT : TilesUniverse F T) :
    Nonempty (UniformQuakePeriodicDecomposition F T v) := by
  classical
  obtain ⟨q, hq⟩ := hF
  let F' := shiftFinset q F
  have hzero : 0 ∈ F' := by
    rw [mem_shiftFinset_iff]
    simpa only [zero_add] using hq
  have hT' : TilesUniverse F' T :=
    (tilesUniverse_shiftFinset_iff q F T).mpr hT
  obtain ⟨D⟩ :=
    exists_uniformQuakePeriodicDecomposition_of_zero_mem hzero hv hT'
  exact ⟨D.transportGraph (quakeGraph_shiftFinset q F T v)⟩

end Tiling.RationalPolygonal
