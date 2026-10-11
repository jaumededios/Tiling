import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Factorial.Basic
import Tiling.AxisParallel.Foundations.ExternalInputs
import Tiling.AxisParallel.Discrete.DiscreteTilingsAndPlates

/-!
# Uniform weak-periodic decompositions inside vertical quake plates

This is the fixed-target version of the DDGGM pigeonhole construction.  Its only external
ingredient is the uniform Greenfeld--Tao datum supplied by `gtUniformCosetwiseDirections`;
earthquake shifts retain the original periodic target by the target-relative D01 theorem.
-/

open Set
open TranslationalTilings

namespace Tiling.AxisParallel.Discrete

private theorem d02_lattice_index_ne_zero
    {F : Finset TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell) :
    D.lattice.index ≠ 0 := by
  let q := TranslationalTilings.weakQ F ell
  let N := TranslationalTilings.weakN D.direction
  let M := TranslationalTilings.weakM D.direction
  let a := TranslationalTilings.weakAvoidance D.direction
  let h₀ := D.direction ⟨0, D.number_pos⟩
  have haSpec := TranslationalTilings.avoidanceVector_spec D.direction_ne_zero
  have hw₀ : TranslationalTilings.wedge a h₀ ≠ 0 := by
    intro hw
    exact haSpec.2.1 ⟨0, D.number_pos⟩
      ((TranslationalTilings.commensurable_iff_wedge_eq_zero haSpec.1
        (D.direction_ne_zero ⟨0, D.number_pos⟩)).2 hw)
  have hdet : TranslationalTilings.wedge
      (TranslationalTilings.weakSliceVector F ell D.direction)
      (((q * N * M : ℕ) : ℤ) • h₀) ≠ 0 := by
    rw [TranslationalTilings.weakSliceVector,
      TranslationalTilings.wedge_zsmul_left,
      TranslationalTilings.wedge_zsmul_right]
    exact mul_ne_zero
      (by exact_mod_cast (Nat.ne_of_gt
        (Nat.mul_pos D.arithmetic.q_pos D.arithmetic.pairLCM_pos)))
      (mul_ne_zero
        (by exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos
          (Nat.mul_pos D.arithmetic.q_pos D.arithmetic.pairLCM_pos)
          D.arithmetic.avoidanceLCM_pos))) hw₀)
  change D.arithmetic.lattice.index ≠ 0
  rw [D.arithmetic.lattice_eq, TranslationalTilings.weakLattice,
    TranslationalTilings.index_generatedPair hdet]
  exact Int.natAbs_ne_zero.mpr hdet

private abbrev d02Period
    {F : Finset TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (j : Fin D.numberOfDirections) : TranslationalTilings.Plane :=
  ((ell * D.multiplier : ℕ) : ℤ) • D.direction j

private theorem d02_period_mem
    {F : Finset TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (j : Fin D.numberOfDirections) : d02Period D j ∈ D.lattice :=
  D.period_mem_lattice j

private theorem d02_period_ne_zero
    {F : Finset TranslationalTilings.Plane} {ell : ℕ} (hell : 0 < ell)
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (j : Fin D.numberOfDirections) : d02Period D j ≠ 0 := by
  exact smul_ne_zero (Int.ofNat_ne_zero.mpr
    (Nat.ne_of_gt (Nat.mul_pos hell D.arithmetic.multiplier_pos)))
    (D.direction_ne_zero j)

private theorem d02_quotientCoset_add_mem_iff
    (Λ : AddSubgroup TranslationalTilings.Plane)
    (c : TranslationalTilings.Plane ⧸ Λ)
    {p : TranslationalTilings.Plane} (hp : p ∈ Λ)
    (x : TranslationalTilings.Plane) :
    x + p ∈ TranslationalTilings.quotientCoset Λ c ↔
      x ∈ TranslationalTilings.quotientCoset Λ c := by
  change QuotientAddGroup.mk' Λ (x + p) = c ↔ QuotientAddGroup.mk' Λ x = c
  have hp0 : QuotientAddGroup.mk' Λ p = 0 :=
    (QuotientAddGroup.eq_zero_iff p).2 hp
  rw [map_add, hp0, add_zero]

private noncomputable def d02IndexedShift
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (k : Fin (D.numberOfDirections + 1)) : Set TranslationalTilings.Plane :=
  Tiling.RationalPolygonal.quakeShiftedTranslations
    (Tiling.RationalPolygonal.quakeShiftExcept P
      (((D.lattice.index * k.val : ℕ) : ℤ)))

private theorem d02_exists_period_on_coset
    {F : Finset TranslationalTilings.Plane}
    {B : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (hvalid : D.ValidFor B)
    (c : TranslationalTilings.Plane ⧸ D.lattice) :
    ∃ j : Fin D.numberOfDirections,
      Tiling.RationalPolygonal.DiscretePeriodicBy
        (B ∩ TranslationalTilings.quotientCoset D.lattice c) (d02Period D j) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective D.lattice c
  obtain ⟨j, hj⟩ := hvalid x
  refine ⟨j, ?_⟩
  intro y
  simpa [TranslationalTilings.addCoset, TranslationalTilings.quotientCoset,
    QuotientAddGroup.eq_iff_sub_mem, d02Period] using hj y

private theorem d02_exists_repeated_cosetPeriod
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (d02IndexedShift D P k))
    (c : TranslationalTilings.Plane ⧸ D.lattice) :
    ∃ (i j : Fin (D.numberOfDirections + 1))
        (r : Fin D.numberOfDirections),
      i.val < j.val ∧
      Tiling.RationalPolygonal.DiscretePeriodicBy
        (d02IndexedShift D P i ∩ TranslationalTilings.quotientCoset D.lattice c)
        (d02Period D r) ∧
      Tiling.RationalPolygonal.DiscretePeriodicBy
        (d02IndexedShift D P j ∩ TranslationalTilings.quotientCoset D.lattice c)
        (d02Period D r) := by
  classical
  let selected : Fin (D.numberOfDirections + 1) → Fin D.numberOfDirections :=
    fun k => Classical.choose (d02_exists_period_on_coset D (hvalid k) c)
  have hselected (k : Fin (D.numberOfDirections + 1)) :
      Tiling.RationalPolygonal.DiscretePeriodicBy
        (d02IndexedShift D P k ∩ TranslationalTilings.quotientCoset D.lattice c)
        (d02Period D (selected k)) :=
    Classical.choose_spec (d02_exists_period_on_coset D (hvalid k) c)
  obtain ⟨i, j, hij, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt selected (by simp)
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact ⟨i, j, selected i, hijlt, hselected i, heq ▸ hselected j⟩
  · exact ⟨j, i, selected j, hjilt, hselected j, heq.symm ▸ hselected i⟩

private structure D02RepeatData
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (c : TranslationalTilings.Plane ⧸ D.lattice) where
  lower : Fin (D.numberOfDirections + 1)
  upper : Fin (D.numberOfDirections + 1)
  periodIndex : Fin D.numberOfDirections
  lower_lt_upper : lower.val < upper.val
  lower_periodic : Tiling.RationalPolygonal.DiscretePeriodicBy
    (d02IndexedShift D P lower ∩ TranslationalTilings.quotientCoset D.lattice c)
      (d02Period D periodIndex)
  upper_periodic : Tiling.RationalPolygonal.DiscretePeriodicBy
    (d02IndexedShift D P upper ∩ TranslationalTilings.quotientCoset D.lattice c)
      (d02Period D periodIndex)

private noncomputable def d02Repeat
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (d02IndexedShift D P k))
    (c : TranslationalTilings.Plane ⧸ D.lattice) : D02RepeatData D P c := by
  classical
  apply Classical.choice
  obtain ⟨i, j, r, hij, hi, hj⟩ := d02_exists_repeated_cosetPeriod D P hvalid c
  exact ⟨⟨i, j, r, hij, hi, hj⟩⟩

private noncomputable def d02UniformPeriod
    {F : Finset TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell) :
    TranslationalTilings.Plane :=
  (((D.lattice.index * D.numberOfDirections.factorial : ℕ) : ℤ) •
    verticalDiscreteUnit)

private theorem d02UniformPeriod_ne_zero
    {F : Finset TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell) :
    d02UniformPeriod D ≠ 0 := by
  apply smul_ne_zero
  · exact Int.ofNat_ne_zero.mpr (Nat.mul_ne_zero
      (d02_lattice_index_ne_zero D) (Nat.factorial_ne_zero _))
  · intro h
    have := congrFun h 1
    simp [verticalDiscreteUnit] at this

private theorem d02_indexedShift_mem_lattice
    {F : Finset TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (k : Fin (D.numberOfDirections + 1)) :
    (((D.lattice.index * k.val : ℕ) : ℤ) • verticalDiscreteUnit) ∈ D.lattice := by
  have hbase : (D.lattice.index : ℤ) • verticalDiscreteUnit ∈ D.lattice := by
    simpa using D.lattice.nsmul_index_mem verticalDiscreteUnit
  have hk := D.lattice.zsmul_mem hbase (k.val : ℤ)
  convert hk using 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Nat.cast_mul]
  ring

private theorem d02_translation_eq_of_representations
    {G : Type*} [AddCommGroup G]
    {F : Finset G} {A E : Set G}
    (hTile : TranslationalTilings.Tiles F A E)
    {f g a b : G} (hf : f ∈ F) (ha : a ∈ A)
    (hg : g ∈ F) (hb : b ∈ A) (heq : f + a = g + b) : a = b := by
  classical
  have hxE : f + a ∈ E := by
    by_contra hnot
    have hcount :=
      (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp
        hTile (f + a)
    have hzeroCard : (F.filter fun q => f + a - q ∈ A).card = 0 := by
      simpa [hnot] using hcount
    have hmem : f ∈ F.filter fun q => f + a - q ∈ A := by
      simp only [Finset.mem_filter, hf, true_and]
      simpa only [add_sub_cancel_left] using ha
    rw [Finset.card_eq_zero.mp hzeroCard] at hmem
    simp at hmem
  have hcount :=
    (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp
      hTile (f + a)
  have hcard : (F.filter fun q => f + a - q ∈ A).card = 1 := by
    simpa [hxE] using hcount
  obtain ⟨q, hfilter⟩ := Finset.card_eq_one.mp hcard
  have hfrep : f ∈ F.filter fun q => f + a - q ∈ A := by
    simp only [Finset.mem_filter, hf, true_and]
    simpa only [add_sub_cancel_left] using ha
  have hgrep : g ∈ F.filter fun q => f + a - q ∈ A := by
    simp only [Finset.mem_filter, hg, true_and]
    rw [heq]
    simpa only [add_sub_cancel_left] using hb
  have hfg : f = g := by
    simpa [hfilter] using (show f = q from by simpa [hfilter] using hfrep) |>.trans
      (show g = q from by simpa [hfilter] using hgrep).symm
  rw [hfg] at heq
  exact add_left_cancel heq

private theorem d02_mem_carrier_of_mem_plate
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (hzero : 0 ∈ F)
    {P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit}
    {x : TranslationalTilings.Plane}
    (hx : x ∈ Tiling.RationalPolygonal.quakePlateTranslations P) :
    x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P) :=
  ⟨0, hzero, x, hx, (zero_add x).symm⟩

private theorem d02_not_mem_carrier_of_not_mem_plate
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hzero : 0 ∈ F) (hTile : TranslationalTilings.Tiles F A E)
    {P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit}
    {x : TranslationalTilings.Plane} (hxA : x ∈ A)
    (hxP : x ∉ Tiling.RationalPolygonal.quakePlateTranslations P) :
    x ∉ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P) := by
  rintro ⟨f, hf, s, hsP, hrep⟩
  have hxs : x = s := d02_translation_eq_of_representations hTile
    hzero hxA hf hsP.1 (by simpa using hrep)
  exact hxP (hxs ▸ hsP)

private theorem d02_mem_plate_of_mem_shiftExcept_of_mem_carrier
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hzero : 0 ∈ F) (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    {P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit}
    {x : TranslationalTilings.Plane} {k : ℤ}
    (hxShift : x ∈ Tiling.RationalPolygonal.quakeShiftedTranslations
      (Tiling.RationalPolygonal.quakeShiftExcept P k))
    (hxCarrier : x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)) :
    x ∈ Tiling.RationalPolygonal.quakePlateTranslations P := by
  obtain ⟨f, hf, s, hsP, hrep⟩ := hxCarrier
  have hsShift : s ∈ Tiling.RationalPolygonal.quakeShiftedTranslations
      (Tiling.RationalPolygonal.quakeShiftExcept P k) :=
    Tiling.RationalPolygonal.mem_quakeShiftedTranslations_quakeShiftExcept_of_mem hsP k
  have htilesShift := tilesOn_quakeShiftedTranslations hF hTile hEVertical
    (Tiling.RationalPolygonal.quakeShiftExcept P k)
  have hxs : x = s := d02_translation_eq_of_representations htilesShift
    hzero hxShift hf hsShift (by simpa using hrep)
  exact hxs ▸ hsP

private theorem d02_incomplete_forward
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hzero : 0 ∈ F) (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (Λ : AddSubgroup TranslationalTilings.Plane)
    (c : TranslationalTilings.Plane ⧸ Λ)
    (p : TranslationalTilings.Plane) (hp : p ∈ Λ) (a b : ℤ)
    (hav : a • verticalDiscreteUnit ∈ Λ)
    (hbv : b • verticalDiscreteUnit ∈ Λ)
    (hperiodA : Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.quakeShiftedTranslations
          (Tiling.RationalPolygonal.quakeShiftExcept P a) ∩
        TranslationalTilings.quotientCoset Λ c) p)
    (hperiodB : Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.quakeShiftedTranslations
          (Tiling.RationalPolygonal.quakeShiftExcept P b) ∩
        TranslationalTilings.quotientCoset Λ c) p) :
    ∀ {x}, x ∈ Tiling.RationalPolygonal.quakeIncompleteOrbit P Λ c p →
      x + (b - a) • verticalDiscreteUnit ∈
        Tiling.RationalPolygonal.quakeIncompleteOrbit P Λ c p := by
  intro x hx
  rcases hx with ⟨hxP, hxc, n, hynotP⟩
  let y := x + n • p
  have hyc : y ∈ TranslationalTilings.quotientCoset Λ c := by
    have hnp : n • p ∈ Λ := Λ.zsmul_mem hp n
    exact (d02_quotientCoset_add_mem_iff Λ c hnp x).2 hxc
  have hxA : x ∈ Tiling.RationalPolygonal.quakeShiftedTranslations
      (Tiling.RationalPolygonal.quakeShiftExcept P a) :=
    Tiling.RationalPolygonal.mem_quakeShiftedTranslations_quakeShiftExcept_of_mem hxP a
  have hxB : x ∈ Tiling.RationalPolygonal.quakeShiftedTranslations
      (Tiling.RationalPolygonal.quakeShiftExcept P b) :=
    Tiling.RationalPolygonal.mem_quakeShiftedTranslations_quakeShiftExcept_of_mem hxP b
  have hyA : y ∈ Tiling.RationalPolygonal.quakeShiftedTranslations
        (Tiling.RationalPolygonal.quakeShiftExcept P a) ∩
      TranslationalTilings.quotientCoset Λ c :=
    (hperiodA.zsmul n x).mpr ⟨hxA, hxc⟩
  have hyB : y ∈ Tiling.RationalPolygonal.quakeShiftedTranslations
        (Tiling.RationalPolygonal.quakeShiftExcept P b) ∩
      TranslationalTilings.quotientCoset Λ c :=
    (hperiodB.zsmul n x).mpr ⟨hxB, hxc⟩
  obtain ⟨t, htA, htNotP, hyt⟩ :=
    Tiling.RationalPolygonal.exists_original_of_mem_quakeShiftedTranslations_quakeShiftExcept
      hyA.1 hynotP
  let ts : A := ⟨t, htA⟩
  let Q := (Tiling.RationalPolygonal.quakeGraph
    F A verticalDiscreteUnit).connectedComponentMk ts
  have hQP : Q ≠ P := by
    intro h
    exact htNotP ⟨htA, h⟩
  have htQ : t ∈ Tiling.RationalPolygonal.quakePlateTranslations Q :=
    Tiling.RationalPolygonal.mem_quakePlateTranslations_mk ts
  have hshiftB : b • verticalDiscreteUnit + t ∈
      Tiling.RationalPolygonal.quakeShiftedTranslations
        (Tiling.RationalPolygonal.quakeShiftExcept P b) :=
    Tiling.RationalPolygonal.add_mem_quakeShiftedTranslations_quakeShiftExcept_of_mem
      hQP htQ b
  have hyDeltaShiftB : y + (b - a) • verticalDiscreteUnit ∈
      Tiling.RationalPolygonal.quakeShiftedTranslations
        (Tiling.RationalPolygonal.quakeShiftExcept P b) := by
    rw [hyt]
    convert hshiftB using 1
    rw [sub_smul]
    abel
  have hyDeltaCoset : y + (b - a) • verticalDiscreteUnit ∈
      TranslationalTilings.quotientCoset Λ c := by
    have hdelta : (b - a) • verticalDiscreteUnit ∈ Λ := by
      rw [sub_smul]
      exact Λ.sub_mem hbv hav
    exact (d02_quotientCoset_add_mem_iff Λ c hdelta y).2 hyc
  let x' := x + (b - a) • verticalDiscreteUnit
  have hx'ShiftB : x' ∈ Tiling.RationalPolygonal.quakeShiftedTranslations
        (Tiling.RationalPolygonal.quakeShiftExcept P b) ∩
      TranslationalTilings.quotientCoset Λ c := by
    have hmem := (hperiodB.zsmul (-n) (y + (b - a) • verticalDiscreteUnit)).mpr
      ⟨hyDeltaShiftB, hyDeltaCoset⟩
    convert hmem using 1
    dsimp [x', y]
    module
  have hx'Carrier : x' ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P) := by
    have hxCarrier := d02_mem_carrier_of_mem_plate hzero hxP
    have hper := (verticalPlateCarrier_periodic hF hTile hEVertical P).zsmul (b - a)
    exact (hper x).2 hxCarrier
  have hx'P : x' ∈ Tiling.RationalPolygonal.quakePlateTranslations P :=
    d02_mem_plate_of_mem_shiftExcept_of_mem_carrier
      hzero hF hTile hEVertical hx'ShiftB.1 hx'Carrier
  have htNotCarrier : t ∉ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P) :=
    d02_not_mem_carrier_of_not_mem_plate hzero hTile htA htNotP
  have hyNotCarrier : y ∉ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P) := by
    intro hyCarrier
    have hper := (verticalPlateCarrier_periodic hF hTile hEVertical P).zsmul a
    apply htNotCarrier
    apply (hper t).mp
    convert hyCarrier using 1
    rw [hyt]
    abel
  have hyDeltaNotCarrier : y + (b - a) • verticalDiscreteUnit ∉
      Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P) := by
    intro hmem
    have hper :=
      (verticalPlateCarrier_periodic hF hTile hEVertical P).zsmul (b - a)
    exact hyNotCarrier ((hper y).mp hmem)
  have hyDeltaNotP : y + (b - a) • verticalDiscreteUnit ∉
      Tiling.RationalPolygonal.quakePlateTranslations P := by
    intro hmem
    exact hyDeltaNotCarrier (d02_mem_carrier_of_mem_plate hzero hmem)
  refine ⟨hx'P, hx'ShiftB.2, n, ?_⟩
  intro hmem
  apply hyDeltaNotP
  convert hmem using 1
  dsimp [x', y]
  abel

private theorem d02_incomplete_periodic
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hzero : 0 ∈ F) (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (Λ : AddSubgroup TranslationalTilings.Plane)
    (c : TranslationalTilings.Plane ⧸ Λ)
    (p : TranslationalTilings.Plane) (hp : p ∈ Λ) (a b : ℤ)
    (hav : a • verticalDiscreteUnit ∈ Λ)
    (hbv : b • verticalDiscreteUnit ∈ Λ)
    (hperiodA : Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.quakeShiftedTranslations
          (Tiling.RationalPolygonal.quakeShiftExcept P a) ∩
        TranslationalTilings.quotientCoset Λ c) p)
    (hperiodB : Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.quakeShiftedTranslations
          (Tiling.RationalPolygonal.quakeShiftExcept P b) ∩
        TranslationalTilings.quotientCoset Λ c) p) :
    Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.quakeIncompleteOrbit P Λ c p)
      ((b - a) • verticalDiscreteUnit) := by
  intro x
  constructor
  · intro hx
    have hback := d02_incomplete_forward hzero hF hTile hEVertical P Λ c p hp b a
      hbv hav hperiodB hperiodA hx
    have heq : x + (b - a) • verticalDiscreteUnit +
        (a - b) • verticalDiscreteUnit = x := by
      rw [sub_smul, sub_smul]
      module
    rwa [heq] at hback
  · exact d02_incomplete_forward hzero hF hTile hEVertical P Λ c p hp a b
      hav hbv hperiodA hperiodB

private theorem d02_chosen_incomplete_periodic_uniform
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {ell : ℕ}
    (hzero : 0 ∈ F) (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (d02IndexedShift D P k))
    (c : TranslationalTilings.Plane ⧸ D.lattice) :
    let R := d02Repeat D P hvalid c
    Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.quakeIncompleteOrbit P D.lattice c
        (d02Period D R.periodIndex))
      (d02UniformPeriod D) := by
  dsimp only
  let R := d02Repeat D P hvalid c
  let p := d02Period D R.periodIndex
  let a : ℤ := (D.lattice.index * R.lower.val : ℕ)
  let b : ℤ := (D.lattice.index * R.upper.val : ℕ)
  have hlocal : Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.quakeIncompleteOrbit P D.lattice c p)
      ((b - a) • verticalDiscreteUnit) := by
    apply d02_incomplete_periodic hzero hF hTile hEVertical P D.lattice c p
    · exact d02_period_mem D R.periodIndex
    · exact d02_indexedShift_mem_lattice D R.lower
    · exact d02_indexedShift_mem_lattice D R.upper
    · simpa [d02IndexedShift, a, p] using R.lower_periodic
    · simpa [d02IndexedShift, b, p] using R.upper_periodic
  let d := R.upper.val - R.lower.val
  have hdpos : 0 < d := Nat.sub_pos_of_lt R.lower_lt_upper
  have hdle : d ≤ D.numberOfDirections := by omega
  obtain ⟨z, hz⟩ := Nat.dvd_factorial hdpos hdle
  have hmultiple : d02UniformPeriod D =
      (z : ℤ) • ((b - a) • verticalDiscreteUnit) := by
    have hzInt : (D.numberOfDirections.factorial : ℤ) =
        (d : ℤ) * (z : ℤ) := by
      exact_mod_cast hz
    have hdInt : (d : ℤ) =
        (R.upper.val : ℤ) - (R.lower.val : ℤ) := by
      dsimp [d]
      rw [Nat.cast_sub (Nat.le_of_lt R.lower_lt_upper)]
    dsimp [d02UniformPeriod, a, b]
    rw [hzInt, hdInt]
    rw [sub_smul, smul_sub]
    module
  rw [hmultiple]
  exact hlocal.zsmul z

private noncomputable def d02CompletePart
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (d02IndexedShift D P k))
    (j : Fin D.numberOfDirections) : Set TranslationalTilings.Plane :=
  {x | ∃ c : TranslationalTilings.Plane ⧸ D.lattice,
    (d02Repeat D P hvalid c).periodIndex = j ∧
    x ∈ Tiling.RationalPolygonal.quakePlateTranslations P ∧
    x ∈ TranslationalTilings.quotientCoset D.lattice c ∧
    ∀ n : ℤ, x + n • d02Period D j ∈
      Tiling.RationalPolygonal.quakePlateTranslations P}

private noncomputable def d02ResidualPart
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (d02IndexedShift D P k)) : Set TranslationalTilings.Plane :=
  Tiling.RationalPolygonal.quakePlateTranslations P \
    ⋃ j, d02CompletePart D P hvalid j

private theorem d02CompletePart_periodic
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (d02IndexedShift D P k))
    (j : Fin D.numberOfDirections) :
    Tiling.RationalPolygonal.DiscretePeriodicBy
      (d02CompletePart D P hvalid j) (d02Period D j) := by
  let p := d02Period D j
  have hp := d02_period_mem D j
  intro x
  constructor
  · rintro ⟨c, hcj, hxP, hxc, hfull⟩
    refine ⟨c, hcj, ?_, (d02_quotientCoset_add_mem_iff D.lattice c hp x).mp hxc, ?_⟩
    · have hminus := hfull (-1)
      have heq : x + p + (-1 : ℤ) • p = x := by module
      rwa [heq] at hminus
    · intro n
      have hn := hfull (n - 1)
      have heq : x + p + (n - 1) • p = x + n • p := by
        rw [sub_smul]
        module
      rwa [heq] at hn
  · rintro ⟨c, hcj, hxP, hxc, hfull⟩
    have hxP' : x + p ∈ Tiling.RationalPolygonal.quakePlateTranslations P := by
      simpa only [one_smul] using hfull 1
    refine ⟨c, hcj, hxP',
      (d02_quotientCoset_add_mem_iff D.lattice c hp x).mpr hxc, ?_⟩
    intro n
    have hn := hfull (n + 1)
    have heq : x + p + n • p = x + (n + 1) • p := by
      rw [add_smul]
      module
    change x + p + n • p ∈ Tiling.RationalPolygonal.quakePlateTranslations P
    rw [heq]
    exact hn

private theorem d02_mem_residual_iff_exists_incomplete
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (d02IndexedShift D P k))
    (x : TranslationalTilings.Plane) :
    x ∈ d02ResidualPart D P hvalid ↔
      ∃ c : TranslationalTilings.Plane ⧸ D.lattice,
        x ∈ Tiling.RationalPolygonal.quakeIncompleteOrbit P D.lattice c
          (d02Period D (d02Repeat D P hvalid c).periodIndex) := by
  classical
  constructor
  · intro hx
    let c := QuotientAddGroup.mk' D.lattice x
    let R := d02Repeat D P hvalid c
    refine ⟨c, hx.1, rfl, ?_⟩
    by_cases hfull : ∀ n : ℤ,
        x + n • d02Period D R.periodIndex ∈
          Tiling.RationalPolygonal.quakePlateTranslations P
    · exfalso
      apply hx.2
      apply Set.mem_iUnion.mpr
      exact ⟨R.periodIndex, c, rfl, hx.1, rfl, hfull⟩
    · exact not_forall.mp hfull
  · rintro ⟨c, hxP, hxc, n, hn⟩
    refine ⟨hxP, ?_⟩
    intro hxUnion
    obtain ⟨j, c', hc'j, _hxP', hxc', hfull⟩ := Set.mem_iUnion.mp hxUnion
    have hcc' : c = c' := hxc.symm.trans hxc'
    have hselected : (d02Repeat D P hvalid c).periodIndex = j := by
      rw [hcc']
      exact hc'j
    apply hn
    simpa [hselected] using hfull n

private theorem d02ResidualPart_periodic
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {ell : ℕ}
    (hzero : 0 ∈ F) (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (d02IndexedShift D P k)) :
    Tiling.RationalPolygonal.DiscretePeriodicBy
      (d02ResidualPart D P hvalid) (d02UniformPeriod D) := by
  intro x
  rw [d02_mem_residual_iff_exists_incomplete D P hvalid,
    d02_mem_residual_iff_exists_incomplete D P hvalid]
  constructor
  · rintro ⟨c, hx⟩
    refine ⟨c, ?_⟩
    exact (d02_chosen_incomplete_periodic_uniform
      hzero hF hTile hEVertical D P hvalid c x).mp hx
  · rintro ⟨c, hx⟩
    refine ⟨c, ?_⟩
    exact (d02_chosen_incomplete_periodic_uniform
      hzero hF hTile hEVertical D P hvalid c x).mpr hx

private noncomputable def d02RawPart
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (d02IndexedShift D P k)) :
    Fin (D.numberOfDirections + 1) → Set TranslationalTilings.Plane :=
  Fin.cases (d02ResidualPart D P hvalid) (d02CompletePart D P hvalid)

private noncomputable def d02RawPeriod
    {F : Finset TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell) :
    Fin (D.numberOfDirections + 1) → TranslationalTilings.Plane :=
  Fin.cases (d02UniformPeriod D) (d02Period D)

private theorem d02RawPart_pairwiseDisjoint
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (d02IndexedShift D P k)) :
    Set.PairwiseDisjoint Set.univ (d02RawPart D P hvalid) := by
  classical
  have hdisj : ∀ i j : Fin (D.numberOfDirections + 1), i ≠ j →
      Disjoint (d02RawPart D P hvalid i) (d02RawPart D P hvalid j) := by
    intro i
    refine Fin.cases (motive := fun i => ∀ j, i ≠ j →
      Disjoint (d02RawPart D P hvalid i) (d02RawPart D P hvalid j)) ?_ ?_ i
    · intro j
      refine Fin.cases ?_ (fun j _ => ?_) j
      · intro hij
        exact (hij rfl).elim
      · change Disjoint (d02ResidualPart D P hvalid) (d02CompletePart D P hvalid j)
        rw [Set.disjoint_left]
        intro x hxResidual hxComplete
        exact hxResidual.2 (Set.mem_iUnion.mpr ⟨j, hxComplete⟩)
    · intro i j
      refine Fin.cases ?_ (fun j hij => ?_) j
      · intro _
        change Disjoint (d02CompletePart D P hvalid i) (d02ResidualPart D P hvalid)
        rw [Set.disjoint_left]
        intro x hxComplete hxResidual
        exact hxResidual.2 (Set.mem_iUnion.mpr ⟨i, hxComplete⟩)
      · change Disjoint (d02CompletePart D P hvalid i) (d02CompletePart D P hvalid j)
        rw [Set.disjoint_left]
        intro x hxi hxj
        obtain ⟨c, hci, _hxiP, hxic, _⟩ := hxi
        obtain ⟨c', hc'j, _hxjP, hxjc', _⟩ := hxj
        have hcc' : c = c' := hxic.symm.trans hxjc'
        have hij' : i = j := by
          apply Fin.ext
          have hselected : (d02Repeat D P hvalid c).periodIndex = j := by
            rw [hcc']
            exact hc'j
          exact congrArg Fin.val (hci.symm.trans hselected)
        exact hij (congrArg Fin.succ hij')
  intro i _ j _ hij
  exact hdisj i j hij

private theorem d02RawPart_iUnion
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hvalid : ∀ k : Fin (D.numberOfDirections + 1),
      D.ValidFor (d02IndexedShift D P k)) :
    (⋃ j, d02RawPart D P hvalid j) =
      Tiling.RationalPolygonal.quakePlateTranslations P := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
    refine Fin.cases (motive := fun j => x ∈ d02RawPart D P hvalid j →
      x ∈ Tiling.RationalPolygonal.quakePlateTranslations P) ?_
      (fun i hi => ?_) j hxj
    · intro hresidual
      exact hresidual.1
    · obtain ⟨c, _hci, hxP, _hxc, _hfull⟩ := hi
      exact hxP
  · intro hxP
    by_cases hxComplete : x ∈ ⋃ j, d02CompletePart D P hvalid j
    · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxComplete
      exact Set.mem_iUnion.mpr ⟨Fin.succ j, hxj⟩
    · exact Set.mem_iUnion.mpr ⟨0, hxP, hxComplete⟩

private theorem d02_periods_pairwise_incommensurable
    {F : Finset TranslationalTilings.Plane} {ell : ℕ} (hell : 0 < ell)
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell) :
    TranslationalTilings.PairwiseIncommensurable (d02Period D) := by
  intro i j hij hcomm
  have hi0 := d02_period_ne_zero hell D i
  have hj0 := d02_period_ne_zero hell D j
  have hw := (TranslationalTilings.commensurable_iff_wedge_eq_zero hi0 hj0).mp hcomm
  rw [d02Period, TranslationalTilings.wedge_zsmul_left,
    TranslationalTilings.wedge_zsmul_right] at hw
  have hm : ((ell * D.multiplier : ℕ) : ℤ) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.ne_of_gt
      (Nat.mul_pos hell D.arithmetic.multiplier_pos))
  have hwdirection : TranslationalTilings.wedge (D.direction i) (D.direction j) = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left hm)).resolve_left hm
  exact D.pairwise_incommensurable i j hij
    ((TranslationalTilings.commensurable_iff_wedge_eq_zero
      (D.direction_ne_zero i) (D.direction_ne_zero j)).mpr hwdirection)

private theorem d02_commensurable_symm
    {u w : TranslationalTilings.Plane} :
    TranslationalTilings.Commensurable u w →
      TranslationalTilings.Commensurable w u := by
  rintro ⟨a, b, ha, hb, hab⟩
  exact ⟨b, a, hb, ha, hab.symm⟩

private theorem d02_commensurable_trans
    {u w z : TranslationalTilings.Plane} :
    TranslationalTilings.Commensurable u w →
      TranslationalTilings.Commensurable w z →
        TranslationalTilings.Commensurable u z := by
  rintro ⟨a, b, ha, hb, hab⟩ ⟨c, d, hc, hd, hcd⟩
  refine ⟨c * a, b * d, mul_ne_zero hc ha, mul_ne_zero hb hd, ?_⟩
  calc
    (c * a) • u = c • (a • u) := by rw [mul_smul]
    _ = c • (b • w) := by rw [hab]
    _ = b • (c • w) := by rw [smul_smul, smul_smul, mul_comm]
    _ = b • (d • z) := by rw [hcd]
    _ = (b * d) • z := by rw [mul_smul]

private theorem d02_commensurable_period_vertical_of_uniform
    {F : Finset TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    {p : TranslationalTilings.Plane} (hp : p ≠ 0)
    (hcomm : TranslationalTilings.Commensurable (d02UniformPeriod D) p) :
    TranslationalTilings.Commensurable p verticalDiscreteUnit := by
  have hH0 := d02UniformPeriod_ne_zero D
  have hw :=
    (TranslationalTilings.commensurable_iff_wedge_eq_zero hH0 hp).mp hcomm
  rw [d02UniformPeriod, TranslationalTilings.wedge_zsmul_left] at hw
  have hc : (((D.lattice.index * D.numberOfDirections.factorial : ℕ) : ℤ)) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.mul_ne_zero
      (d02_lattice_index_ne_zero D) (Nat.factorial_ne_zero _))
  have hvp : TranslationalTilings.wedge verticalDiscreteUnit p = 0 :=
    (mul_eq_zero.mp hw).resolve_left hc
  have hpv : TranslationalTilings.wedge p verticalDiscreteUnit = 0 := by
    rw [TranslationalTilings.wedge_swap, hvp, neg_zero]
  have hv : verticalDiscreteUnit ≠ 0 := by
    intro h
    have := congrFun h 1
    simp [verticalDiscreteUnit] at this
  exact (TranslationalTilings.commensurable_iff_wedge_eq_zero hp hv).mpr hpv

private noncomputable def d02DecompositionNoParallel
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (hvalid : ∀ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
      ∀ k : Fin (D.numberOfDirections + 1), D.ValidFor (d02IndexedShift D P k))
    (hnone : ∀ j : Fin D.numberOfDirections,
      ¬ TranslationalTilings.Commensurable (d02Period D j) verticalDiscreteUnit) :
    Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit where
  numberOfParts := D.numberOfDirections + 1
  number_pos := Nat.succ_pos _
  part P := d02RawPart D P (hvalid P)
  period := d02RawPeriod D
  period_ne_zero := by
    intro j
    refine Fin.cases (d02UniformPeriod_ne_zero D) (fun i => ?_) j
    exact d02_period_ne_zero hell D i
  pairwise_incommensurable := by
    intro i
    refine Fin.cases (motive := fun i => ∀ j, i ≠ j →
      ¬ TranslationalTilings.Commensurable (d02RawPeriod D i)
        (d02RawPeriod D j)) ?_ ?_ i
    · intro j
      refine Fin.cases ?_ (fun j _ hcomm => ?_) j
      · intro hij
        exact (hij rfl).elim
      · exact hnone j (d02_commensurable_period_vertical_of_uniform D
          (d02_period_ne_zero hell D j) hcomm)
    · intro i j
      refine Fin.cases ?_ (fun j hij hcomm => ?_) j
      · intro _ hcomm
        exact hnone i (d02_commensurable_period_vertical_of_uniform D
          (d02_period_ne_zero hell D i) (d02_commensurable_symm hcomm))
      · apply d02_periods_pairwise_incommensurable hell D i j
        · intro hij'
          exact hij (congrArg Fin.succ hij')
        · exact hcomm
  periodic_part := by
    intro P j
    refine Fin.cases
      (d02ResidualPart_periodic hzero hF hTile hEVertical D P (hvalid P))
      (fun i => d02CompletePart_periodic D P (hvalid P) i) j
  pairwiseDisjoint := by
    intro P
    exact d02RawPart_pairwiseDisjoint D P (hvalid P)
  iUnion_parts := by
    intro P
    exact d02RawPart_iUnion D P (hvalid P)

private theorem d02_existsDecompositionParallel
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hF : F.Nonempty)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (D : TranslationalTilings.QuantitativeWeakPeriodData F ell)
    (hvalid : ∀ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
      ∀ k : Fin (D.numberOfDirections + 1), D.ValidFor (d02IndexedShift D P k))
    (j₀ : Fin D.numberOfDirections)
    (hj₀ : TranslationalTilings.Commensurable
      (d02Period D j₀) verticalDiscreteUnit) :
    ∃ U : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
        F A verticalDiscreteUnit,
      ∃ j : Fin U.numberOfParts, ∃ k : ℕ,
        0 < k ∧ U.period j = (k : ℤ) • verticalDiscreteUnit := by
  classical
  let p : Fin D.numberOfDirections → TranslationalTilings.Plane := d02Period D
  let H₀ := d02UniformPeriod D
  let c : ℤ := ((D.lattice.index * D.numberOfDirections.factorial : ℕ) : ℤ)
  have hj₀copy := hj₀
  obtain ⟨a, b, ha, hb, hab⟩ := hj₀
  let s : ℤ := Int.sign b
  let a' : ℤ := s * a
  let bNat : ℕ := Int.natAbs b
  have hbNatPos : 0 < bNat := Int.natAbs_pos.mpr hb
  have hs_mul_b : s * b = (bNat : ℤ) := by
    simp [s, bNat]
  have hab' : a' • p j₀ = (bNat : ℤ) • verticalDiscreteUnit := by
    dsimp only [a', p]
    calc
      (s * a) • d02Period D j₀ = s • (a • d02Period D j₀) := by rw [mul_smul]
      _ = s • (b • verticalDiscreteUnit) := by rw [hab]
      _ = (s * b) • verticalDiscreteUnit := by rw [mul_smul]
      _ = (bNat : ℤ) • verticalDiscreteUnit := by rw [hs_mul_b]
  let H₁ : TranslationalTilings.Plane := (bNat : ℤ) • H₀
  have hc : c ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.mul_ne_zero
      (d02_lattice_index_ne_zero D) (Nat.factorial_ne_zero _))
  have hH₀ : H₀ ≠ 0 := d02UniformPeriod_ne_zero D
  have hH₁ : H₁ ≠ 0 :=
    smul_ne_zero (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hbNatPos)) hH₀
  have hH₁eq : H₁ = (c * a') • p j₀ := by
    dsimp [H₁, H₀, d02UniformPeriod, c]
    calc
      (bNat : ℤ) •
          (((D.lattice.index * D.numberOfDirections.factorial : ℕ) : ℤ) •
            verticalDiscreteUnit) =
          c • ((bNat : ℤ) • verticalDiscreteUnit) := by
            rw [smul_smul, smul_smul, mul_comm]
      _ = c • (a' • p j₀) := by rw [hab']
      _ = (c * a') • p j₀ := by module
  let k : ℕ := bNat * (D.lattice.index * D.numberOfDirections.factorial)
  have hk : 0 < k := Nat.mul_pos hbNatPos
    (Nat.mul_pos (Nat.pos_of_ne_zero (d02_lattice_index_ne_zero D))
      (Nat.factorial_pos _))
  have hH₁scalar : H₁ = (k : ℤ) • verticalDiscreteUnit := by
    dsimp [H₁, H₀, d02UniformPeriod, k]
    module
  have hH₁v : TranslationalTilings.Commensurable H₁ verticalDiscreteUnit := by
    refine ⟨1, (k : ℤ), one_ne_zero,
      Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hk), ?_⟩
    rw [one_smul, hH₁scalar]
  have hparallel_unique (j : Fin D.numberOfDirections)
      (hj : TranslationalTilings.Commensurable (p j) verticalDiscreteUnit) : j = j₀ := by
    by_contra hne
    exact d02_periods_pairwise_incommensurable hell D j j₀ hne
      (d02_commensurable_trans hj (d02_commensurable_symm hj₀copy))
  let newPart :
      Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit →
        Fin D.numberOfDirections → Set TranslationalTilings.Plane :=
    fun P j => if j = j₀ then
      d02RawPart D P (hvalid P) 0 ∪ d02RawPart D P (hvalid P) (Fin.succ j₀)
    else d02RawPart D P (hvalid P) (Fin.succ j)
  let newPeriod : Fin D.numberOfDirections → TranslationalTilings.Plane :=
    fun j => if j = j₀ then H₁ else p j
  have hperiod_ne_zero (j : Fin D.numberOfDirections) : newPeriod j ≠ 0 := by
    by_cases hj : j = j₀
    · simpa [newPeriod, hj] using hH₁
    · simpa [newPeriod, hj, p] using d02_period_ne_zero hell D j
  have hperiodic
      (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
      (j : Fin D.numberOfDirections) :
      Tiling.RationalPolygonal.DiscretePeriodicBy (newPart P j) (newPeriod j) := by
    by_cases hj : j = j₀
    · subst j
      have hresidual :=
        d02ResidualPart_periodic hzero hF hTile hEVertical D P (hvalid P)
      have hcomplete := d02CompletePart_periodic D P (hvalid P) j₀
      have hresidualH₁ : Tiling.RationalPolygonal.DiscretePeriodicBy
          (d02RawPart D P (hvalid P) 0) H₁ := by
        simpa [d02RawPart, H₁, H₀] using hresidual.zsmul (bNat : ℤ)
      have hcompleteH₁ : Tiling.RationalPolygonal.DiscretePeriodicBy
          (d02RawPart D P (hvalid P) (Fin.succ j₀)) H₁ := by
        rw [hH₁eq]
        simpa [d02RawPart, p] using hcomplete.zsmul (c * a')
      intro x
      simp only [newPart, newPeriod, if_pos]
      constructor
      · rintro (hx | hx)
        · exact Or.inl ((hresidualH₁ x).mp hx)
        · exact Or.inr ((hcompleteH₁ x).mp hx)
      · rintro (hx | hx)
        · exact Or.inl ((hresidualH₁ x).mpr hx)
        · exact Or.inr ((hcompleteH₁ x).mpr hx)
    · simpa [newPart, newPeriod, hj, d02RawPart, p] using
        d02CompletePart_periodic D P (hvalid P) j
  have hpair : TranslationalTilings.PairwiseIncommensurable newPeriod := by
    intro i j hij hcomm
    by_cases hi : i = j₀
    · subst i
      have hj : j ≠ j₀ := by intro hj; exact hij hj.symm
      have hcomm' : TranslationalTilings.Commensurable H₁ (p j) := by
        simpa [newPeriod, hj] using hcomm
      have hpjv := d02_commensurable_trans (d02_commensurable_symm hcomm') hH₁v
      exact hj (hparallel_unique j hpjv)
    · by_cases hj : j = j₀
      · subst j
        have hcomm' : TranslationalTilings.Commensurable (p i) H₁ := by
          simpa [newPeriod, hi] using hcomm
        have hpiv := d02_commensurable_trans hcomm' hH₁v
        exact hi (hparallel_unique i hpiv)
      · exact d02_periods_pairwise_incommensurable hell D i j hij
          (by simpa [newPeriod, hi, hj, p] using hcomm)
  have hdisjoint
      (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit) :
      Set.PairwiseDisjoint Set.univ (newPart P) := by
    have hraw := d02RawPart_pairwiseDisjoint D P (hvalid P)
    intro i _ j _ hij
    change Disjoint (newPart P i) (newPart P j)
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
  have hunion
      (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit) :
      (⋃ j, newPart P j) = Tiling.RationalPolygonal.quakePlateTranslations P := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      by_cases hj : j = j₀
      · subst j
        simp only [newPart, if_pos] at hxj
        rcases hxj with hxj | hxj
        · rw [← d02RawPart_iUnion D P (hvalid P)]
          exact Set.mem_iUnion.mpr ⟨0, hxj⟩
        · rw [← d02RawPart_iUnion D P (hvalid P)]
          exact Set.mem_iUnion.mpr ⟨Fin.succ j₀, hxj⟩
      · rw [← d02RawPart_iUnion D P (hvalid P)]
        exact Set.mem_iUnion.mpr
          ⟨Fin.succ j, by simpa [newPart, hj] using hxj⟩
    · intro hx
      rw [← d02RawPart_iUnion D P (hvalid P)] at hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      refine Fin.cases (motive := fun j => x ∈ d02RawPart D P (hvalid P) j →
        x ∈ ⋃ j, newPart P j) ?_ (fun j hxj => ?_) j hxj
      · intro hxzero
        exact Set.mem_iUnion.mpr ⟨j₀, by
          simp only [newPart, if_pos]
          exact Or.inl hxzero⟩
      · by_cases hj : j = j₀
        · subst j
          exact Set.mem_iUnion.mpr ⟨j₀, by
            simp only [newPart, if_pos]
            exact Or.inr hxj⟩
        · exact Set.mem_iUnion.mpr ⟨j, by simpa [newPart, hj] using hxj⟩
  let U : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit := {
    numberOfParts := D.numberOfDirections
    number_pos := D.number_pos
    part := newPart
    period := newPeriod
    period_ne_zero := hperiod_ne_zero
    pairwise_incommensurable := hpair
    periodic_part := hperiodic
    pairwiseDisjoint := hdisjoint
    iUnion_parts := hunion
  }
  let jU : Fin U.numberOfParts := ⟨j₀.val, by simp [U]⟩
  refine ⟨U, jU, k, hk, ?_⟩
  change newPeriod j₀ = (k : ℤ) • verticalDiscreteUnit
  rw [show newPeriod j₀ = H₁ by simp [newPeriod]]
  exact hH₁scalar

private theorem d02_singletonDecomposition
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hF : F.Nonempty) (hcard : F.card = 1)
    (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit) :
    ∃ U : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
        F A verticalDiscreteUnit,
      ∃ k : ℕ, 0 < k ∧ U.period ⟨0, U.number_pos⟩ =
        (k : ℤ) • verticalDiscreteUnit := by
  classical
  obtain ⟨q, hFq⟩ := Finset.card_eq_one.mp hcard
  have hqF : q ∈ F := by simp [hFq]
  have hplatePeriodic
      (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit) :
      Tiling.RationalPolygonal.DiscretePeriodicBy
        (Tiling.RationalPolygonal.quakePlateTranslations P) verticalDiscreteUnit := by
    have hcarrier := verticalPlateCarrier_periodic hF hTile hEVertical P
    have hcarrierMem (z : TranslationalTilings.Plane) :
        z ∈ Tiling.RationalPolygonal.discreteCarrier F
            (Tiling.RationalPolygonal.quakePlateTranslations P) ↔
          z - q ∈ Tiling.RationalPolygonal.quakePlateTranslations P := by
      constructor
      · rintro ⟨f, hf, a, ha, rfl⟩
        have hfq : f = q := by simpa [hFq] using hf
        subst f
        simpa only [add_sub_cancel_left] using ha
      · intro hz
        exact ⟨q, hqF, z - q, hz, by abel⟩
    intro x
    have h := hcarrier (q + x)
    rw [hcarrierMem, hcarrierMem] at h
    convert h using 1 <;> abel
  let U : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit := {
    numberOfParts := 1
    number_pos := Nat.one_pos
    part := fun P _ => Tiling.RationalPolygonal.quakePlateTranslations P
    period := fun _ => verticalDiscreteUnit
    period_ne_zero := by
      intro _ h
      have := congrFun h 1
      simp [verticalDiscreteUnit] at this
    pairwise_incommensurable := by
      intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    periodic_part := fun P _ => hplatePeriodic P
    pairwiseDisjoint := by
      intro P i _ j _ hij
      exact (hij (Subsingleton.elim i j)).elim
    iUnion_parts := by
      intro P
      ext x
      simp
  }
  refine ⟨U, 1, Nat.one_pos, ?_⟩
  simp [U]

theorem exists_verticalPlateDirectionalDecomposition
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {ell : ℕ}
    (hF : F.Nonempty) (hell : 0 < ell)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy
      E verticalDiscreteUnit)
    (hEPeriodic : TranslationalTilings.SetScalarPeriodic ell E)
    (hTile : TranslationalTilings.Tiles F A E) :
    ∃ D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
        F A verticalDiscreteUnit,
      ∃ order : Equiv.Perm (Fin D.numberOfParts),
        ∃ k : ℕ, 0 < k ∧
          D.period (order ⟨0, D.number_pos⟩) =
            (k : ℤ) • verticalDiscreteUnit := by
  classical
  by_cases hcard : F.card = 1
  · obtain ⟨U, k, hk, hperiod⟩ :=
      d02_singletonDecomposition hF hcard hTile hEVertical
    exact ⟨U, Equiv.refl _, k, hk, hperiod⟩
  · have hcardGt : 1 < F.card := by
      have hcardPos : 0 < F.card := Finset.card_pos.mpr hF
      omega
    obtain ⟨q, hqF⟩ := hF
    let F₀ : Finset TranslationalTilings.Plane :=
      Tiling.RationalPolygonal.shiftFinset q F
    let E₀ : Set TranslationalTilings.Plane :=
      TranslationalTilings.translateSet (-q) E
    have hzero : 0 ∈ F₀ := by
      change 0 ∈ Tiling.RationalPolygonal.shiftFinset q F
      rw [Tiling.RationalPolygonal.mem_shiftFinset_iff]
      simpa using hqF
    have hcardEq : F₀.card = F.card := by
      apply Nat.le_antisymm
      · apply Finset.card_le_card_of_injOn (fun z => z + q)
        · intro z hz
          exact Tiling.RationalPolygonal.mem_shiftFinset_iff.mp hz
        · exact Set.injOn_of_injective (add_left_injective q)
      · apply Finset.card_le_card_of_injOn (fun f => f - q)
        · intro f hf
          apply Tiling.RationalPolygonal.mem_shiftFinset_iff.mpr
          simpa using hf
        · exact Set.injOn_of_injective sub_left_injective
    have hF₀ : F₀.Nonempty := ⟨0, hzero⟩
    have hE₀Vertical :
        Tiling.RationalPolygonal.DiscretePeriodicBy E₀ verticalDiscreteUnit := by
      intro x
      change x + verticalDiscreteUnit - -q ∈ E ↔ x - -q ∈ E
      convert hEVertical (x + q) using 1 <;> abel
    have hE₀Periodic : TranslationalTilings.SetScalarPeriodic ell E₀ := by
      intro x z
      change x + (ell : ℤ) • z - -q ∈ E ↔ x - -q ∈ E
      convert hEPeriodic (x + q) z using 1 <;> abel
    have hTile₀ : TranslationalTilings.Tiles F₀ A E₀ := by
      intro x
      have hconv : TranslationalTilings.tileConv F₀
          (TranslationalTilings.setIndicator A) x =
          TranslationalTilings.tileConv F
            (TranslationalTilings.setIndicator A) (x + q) := by
        simp only [TranslationalTilings.tileConv]
        apply Finset.sum_equiv (Equiv.addRight q)
        · intro z
          exact Tiling.RationalPolygonal.mem_shiftFinset_iff
        · intro z _
          change TranslationalTilings.setIndicator A (x - z) =
            TranslationalTilings.setIndicator A (x + q - (z + q))
          congr 1
          abel
      rw [hconv, hTile]
      simp only [Nat.cast_one, one_mul]
      change TranslationalTilings.setIndicator E (x + q) =
        TranslationalTilings.setIndicator E₀ x
      simp only [TranslationalTilings.setIndicator, Set.indicator_apply,
        E₀, TranslationalTilings.translateSet, Set.mem_ofPred_eq]
      have harg : x - -q = x + q := by abel
      simp only [harg]
    obtain ⟨W, hW⟩ :=
      Tiling.AxisParallel.Foundations.gtUniformCosetwiseDirections
        (F := F₀) (E := E₀) hell hzero (by simpa [hcardEq] using hcardGt)
          hE₀Periodic
    let hvalid :
        ∀ P : Tiling.RationalPolygonal.QuakePlate F₀ A verticalDiscreteUnit,
          ∀ k : Fin (W.numberOfDirections + 1),
            W.ValidFor (d02IndexedShift W P k) := by
      intro P k
      apply hW
      exact tilesOn_quakeShiftedTranslations hF₀ hTile₀ hE₀Vertical
        (Tiling.RationalPolygonal.quakeShiftExcept P
          (((W.lattice.index * k.val : ℕ) : ℤ)))
    have hgraph : Tiling.RationalPolygonal.quakeGraph F₀ A verticalDiscreteUnit =
        Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit := by
      simpa only [F₀] using
        Tiling.RationalPolygonal.quakeGraph_shiftFinset q F A verticalDiscreteUnit
    by_cases hparallel : ∃ j : Fin W.numberOfDirections,
        TranslationalTilings.Commensurable (d02Period W j) verticalDiscreteUnit
    · obtain ⟨j₀, hj₀⟩ := hparallel
      obtain ⟨U₀, j, k, hk, hjperiod⟩ :=
        d02_existsDecompositionParallel hell hzero hF₀ hTile₀ hE₀Vertical
          W hvalid j₀ hj₀
      let U := U₀.transportGraph hgraph
      let jU : Fin U.numberOfParts := ⟨j.val, by
        change j.val < U₀.numberOfParts
        exact j.isLt⟩
      let zeroU : Fin U.numberOfParts := ⟨0, U.number_pos⟩
      let order : Equiv.Perm (Fin U.numberOfParts) := Equiv.swap zeroU jU
      refine ⟨U, order, k, hk, ?_⟩
      have horder : order zeroU = jU := by simp [order]
      rw [show (⟨0, U.number_pos⟩ : Fin U.numberOfParts) = zeroU from rfl,
        horder]
      exact hjperiod
    · have hnone : ∀ j : Fin W.numberOfDirections,
          ¬ TranslationalTilings.Commensurable
            (d02Period W j) verticalDiscreteUnit := not_exists.mp hparallel
      let U₀ := d02DecompositionNoParallel
        hell hzero hF₀ hTile₀ hE₀Vertical W hvalid hnone
      let U := U₀.transportGraph hgraph
      let order : Equiv.Perm (Fin U.numberOfParts) := Equiv.refl _
      let k : ℕ := W.lattice.index * W.numberOfDirections.factorial
      have hk : 0 < k := Nat.mul_pos
        (Nat.pos_of_ne_zero (d02_lattice_index_ne_zero W))
        (Nat.factorial_pos _)
      refine ⟨U, order, k, hk, ?_⟩
      simp only [order, Equiv.refl_apply]
      change d02UniformPeriod W = (k : ℤ) • verticalDiscreteUnit
      rfl

end Tiling.AxisParallel.Discrete
