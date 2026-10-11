import Tiling.AxisParallel.Discrete.DiscreteTilingsAndPlates
import Tiling.AxisParallel.Foundations.ExternalInputs
import Tiling.RationalPolygonal.EarthquakeUniform

/-!
# Directional layers of canonical discrete earthquake plates

These definitions are transparent set adapters around the production
`UniformQuakePeriodicDecomposition`; no parallel decomposition ontology is introduced.
-/

open Set
open TranslationalTilings

namespace Tiling.AxisParallel.Discrete

def orderedPlateLayer
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (j : Fin D.numberOfParts) : Set TranslationalTilings.Plane :=
  D.part P (order j)

def directionalLayerCentres
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (j : Fin D.numberOfParts) : Set TranslationalTilings.Plane :=
  ⋃ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
    orderedPlateLayer D order P j

def shiftedPlateLayer
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (shift : Tiling.RationalPolygonal.QuakePlate
      F A verticalDiscreteUnit → ℤ)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (j : Fin D.numberOfParts) : Set TranslationalTilings.Plane :=
  TranslationalTilings.translateSet
    ((shift P) • verticalDiscreteUnit) (orderedPlateLayer D order P j)

def shiftedDirectionalLayerCentres
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (shift : Tiling.RationalPolygonal.QuakePlate
      F A verticalDiscreteUnit → ℤ)
    (j : Fin D.numberOfParts) : Set TranslationalTilings.Plane :=
  ⋃ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
    shiftedPlateLayer D order shift P j

private theorem indicator_eq_iff_membership {G : Type*}
    (S : Set G) (x y : G) :
    TranslationalTilings.setIndicator S x =
        TranslationalTilings.setIndicator S y ↔ (x ∈ S ↔ y ∈ S) := by
  classical
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
    simp [TranslationalTilings.setIndicator, hx, hy]

private theorem setScalarPeriodic_of_dvd
    {d p q : ℕ} {S : Set (TranslationalTilings.Lattice d)}
    (hpq : p ∣ q) (hS : TranslationalTilings.SetScalarPeriodic p S) :
    TranslationalTilings.SetScalarPeriodic q S := by
  obtain ⟨m, rfl⟩ := hpq
  intro x z
  have h := hS x ((m : ℤ) • z)
  simpa only [Nat.cast_mul, mul_smul] using h

private theorem directionalLayerCentres_periodic
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (j : Fin D.numberOfParts) :
    Tiling.RationalPolygonal.DiscretePeriodicBy
      (directionalLayerCentres D order j) (D.period (order j)) := by
  intro x
  simp only [directionalLayerCentres, Set.mem_iUnion]
  constructor
  · rintro ⟨P, hxP⟩
    exact ⟨P, (D.periodic_part P (order j) x).mp hxP⟩
  · rintro ⟨P, hxP⟩
    exact ⟨P, (D.periodic_part P (order j) x).mpr hxP⟩

private theorem carrier_periodic_of_centres
    {F : Finset TranslationalTilings.Plane}
    {S : Set TranslationalTilings.Plane} {v : TranslationalTilings.Plane}
    (hS : Tiling.RationalPolygonal.DiscretePeriodicBy S v) :
    Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.discreteCarrier F S) v := by
  intro x
  constructor
  · rintro ⟨f, hf, a, ha, hxa⟩
    refine ⟨f, hf, a - v, (hS (a - v)).mp ?_, ?_⟩
    · simpa only [sub_add_cancel] using ha
    · calc
        x = (f + a) - v := by rw [← hxa]; abel
        _ = f + (a - v) := by abel
  · rintro ⟨f, hf, a, ha, hxa⟩
    refine ⟨f, hf, a + v, (hS a).mpr ha, ?_⟩
    rw [hxa]
    abel

private theorem translation_eq_of_eq_representations
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hTile : TranslationalTilings.Tiles F A E)
    {f g a b : TranslationalTilings.Plane}
    (hf : f ∈ F) (ha : a ∈ A) (hg : g ∈ F) (hb : b ∈ A)
    (heq : f + a = g + b) : a = b := by
  classical
  have hxE : f + a ∈ E := by
    by_contra hnot
    have hcount :=
      (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp
        hTile (f + a)
    have hzero : (F.filter fun q ↦ f + a - q ∈ A).card = 0 := by
      simpa [hnot] using hcount
    have hmem : f ∈ F.filter fun q ↦ f + a - q ∈ A := by
      simp only [Finset.mem_filter, hf, true_and]
      simpa only [add_sub_cancel_left] using ha
    rw [Finset.card_eq_zero.mp hzero] at hmem
    simp at hmem
  have hcount :=
    (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp
      hTile (f + a)
  have hcard : (F.filter fun q ↦ f + a - q ∈ A).card = 1 := by
    simpa [hxE] using hcount
  obtain ⟨q, hfilter⟩ := Finset.card_eq_one.mp hcard
  have hfmem : f ∈ F.filter fun q ↦ f + a - q ∈ A := by
    simp only [Finset.mem_filter, hf, true_and]
    simpa only [add_sub_cancel_left] using ha
  have hgmem : g ∈ F.filter fun q ↦ f + a - q ∈ A := by
    refine Finset.mem_filter.mpr ⟨hg, ?_⟩
    rw [heq]
    simpa only [add_sub_cancel_left] using hb
  have hfg : f = g := by
    have hfq : f = q := by simpa [hfilter] using hfmem
    have hgq : g = q := by simpa [hfilter] using hgmem
    exact hfq.trans hgq.symm
  rw [hfg] at heq
  exact add_left_cancel heq

private theorem orderedPlateLayerCarrier_eq_inter
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hTile : TranslationalTilings.Tiles F A E)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (j : Fin D.numberOfParts) :
    Tiling.RationalPolygonal.discreteCarrier F (orderedPlateLayer D order P j) =
      Tiling.RationalPolygonal.discreteCarrier F (directionalLayerCentres D order j) ∩
        Tiling.RationalPolygonal.discreteCarrier F
          (Tiling.RationalPolygonal.quakePlateTranslations P) := by
  apply Set.Subset.antisymm
  · rintro x ⟨f, hf, a, ha, rfl⟩
    refine ⟨⟨f, hf, a, ?_, rfl⟩, ⟨f, hf, a, ?_, rfl⟩⟩
    · exact Set.mem_iUnion.mpr ⟨P, ha⟩
    · rw [← D.iUnion_parts P]
      exact Set.mem_iUnion.mpr ⟨order j, ha⟩
  · rintro x ⟨⟨f, hf, a, haGlobal, hxfa⟩, ⟨g, hg, b, hbP, hxgb⟩⟩
    obtain ⟨Q, haQ⟩ := Set.mem_iUnion.mp haGlobal
    have haPlate : a ∈ Tiling.RationalPolygonal.quakePlateTranslations Q := by
      rw [← D.iUnion_parts Q]
      exact Set.mem_iUnion.mpr ⟨order j, haQ⟩
    have hab : a = b := translation_eq_of_eq_representations hTile hf
      (Classical.choose haPlate) hg (Classical.choose hbP) (hxfa.symm.trans hxgb)
    have hQP : Q = P := by
      by_contra hne
      exact (Set.disjoint_left.mp
        (verticalPlateCentres_pairwiseDisjoint F A hne)) haPlate (hab ▸ hbP)
    subst Q
    exact ⟨f, hf, a, haQ, hxfa⟩

private theorem discreteCarrier_translateSet
    (F : Finset TranslationalTilings.Plane)
    (t : TranslationalTilings.Plane) (S : Set TranslationalTilings.Plane) :
    Tiling.RationalPolygonal.discreteCarrier F
        (TranslationalTilings.translateSet t S) =
      TranslationalTilings.translateSet t
        (Tiling.RationalPolygonal.discreteCarrier F S) := by
  ext x
  constructor
  · rintro ⟨f, hf, a, ha, rfl⟩
    change f + a - t ∈ Tiling.RationalPolygonal.discreteCarrier F S
    exact ⟨f, hf, a - t, ha, by abel⟩
  · intro hx
    change x - t ∈ Tiling.RationalPolygonal.discreteCarrier F S at hx
    obtain ⟨f, hf, a, ha, hxa⟩ := hx
    refine ⟨f, hf, a + t, ?_, ?_⟩
    · change a + t - t ∈ S
      simpa only [add_sub_cancel_right] using ha
    · calc
        x = (x - t) + t := by abel
        _ = (f + a) + t := by rw [hxa]
        _ = f + (a + t) := by abel

private theorem setScalarPeriodic_translateSet
    {q : ℕ} {S : Set TranslationalTilings.Plane}
    (hS : TranslationalTilings.SetScalarPeriodic q S)
    (t : TranslationalTilings.Plane) :
    TranslationalTilings.SetScalarPeriodic q
      (TranslationalTilings.translateSet t S) := by
  intro x z
  change x + (q : ℤ) • z - t ∈ S ↔ x - t ∈ S
  convert hS (x - t) z using 1
  all_goals abel

private theorem plateCarriers_disjoint
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hTile : TranslationalTilings.Tiles F A E)
    {P Q : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit}
    (hPQ : P ≠ Q) :
    Disjoint
      (Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P))
      (Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations Q)) := by
  rw [Set.disjoint_left]
  intro x hxP hxQ
  obtain ⟨f, hf, a, haP, hxfa⟩ := hxP
  obtain ⟨g, hg, b, hbQ, hxgb⟩ := hxQ
  have hab : a = b := translation_eq_of_eq_representations hTile hf
    (Classical.choose haP) hg (Classical.choose hbQ) (hxfa.symm.trans hxgb)
  exact hPQ ((Classical.choose_spec haP).symm.trans (hab ▸ Classical.choose_spec hbQ))

private theorem discreteCarrier_eq_target_of_tiles
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hTile : TranslationalTilings.Tiles F A E) :
    Tiling.RationalPolygonal.discreteCarrier F A = E := by
  classical
  ext x
  constructor
  · rintro ⟨f, hf, a, ha, rfl⟩
    by_contra hnot
    have hcount :=
      (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp
        hTile (f + a)
    have hzero : (F.filter fun q ↦ f + a - q ∈ A).card = 0 := by
      simpa [hnot] using hcount
    have hmem : f ∈ F.filter fun q ↦ f + a - q ∈ A := by
      simp only [Finset.mem_filter, hf, true_and]
      simpa only [add_sub_cancel_left] using ha
    rw [Finset.card_eq_zero.mp hzero] at hmem
    simp at hmem
  · intro hxE
    have hcount :=
      (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp hTile x
    have hcard : (F.filter fun f ↦ x - f ∈ A).card = 1 := by
      simpa [hxE] using hcount
    obtain ⟨f, hf⟩ := Finset.card_pos.mp (by omega : 0 < (F.filter fun f ↦ x - f ∈ A).card)
    have hdata := Finset.mem_filter.mp hf
    exact ⟨f, hdata.1, x - f, hdata.2, by abel⟩

private theorem shiftedPlateLayer_subset_quakeShifted
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (shift : Tiling.RationalPolygonal.QuakePlate
      F A verticalDiscreteUnit → ℤ)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (j : Fin D.numberOfParts) :
    shiftedPlateLayer D order shift P j ⊆
      Tiling.RationalPolygonal.quakeShiftedTranslations shift := by
  intro x hx
  have hxPlate : x ∈ TranslationalTilings.translateSet
      ((shift P) • verticalDiscreteUnit)
      (Tiling.RationalPolygonal.quakePlateTranslations P) := by
    change x - (shift P) • verticalDiscreteUnit ∈
      Tiling.RationalPolygonal.quakePlateTranslations P
    rw [← D.iUnion_parts P]
    exact Set.mem_iUnion.mpr ⟨order j, hx⟩
  change x - (shift P) • verticalDiscreteUnit ∈
    Tiling.RationalPolygonal.quakePlateTranslations P at hxPlate
  obtain ⟨haA, haComp⟩ := hxPlate
  let a : A := ⟨x - (shift P) • verticalDiscreteUnit, haA⟩
  refine ⟨a, ?_⟩
  change shift
      ((Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).connectedComponentMk a) •
        verticalDiscreteUnit + (a : TranslationalTilings.Plane) = x
  rw [show
    (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).connectedComponentMk a =
      P from haComp]
  dsimp only [a]
  abel

theorem exists_commonDirectionalCarrierScalarPeriod
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {ell : ℕ}
    (_hF : F.Nonempty) (hell : 0 < ell)
    (_hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy
      E verticalDiscreteUnit)
    (hEPeriodic : TranslationalTilings.SetScalarPeriodic ell E)
    (hTile : TranslationalTilings.Tiles F A E)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts)) :
    ∃ N : ℕ, 0 < N ∧ ell ∣ N ∧ ∀ j,
      TranslationalTilings.SetScalarPeriodic N
        (Tiling.RationalPolygonal.discreteCarrier F
          (directionalLayerCentres D order j)) := by
  classical
  let G : TranslationalTilings.DirectionalTilingDecomposition F A E ell := {
    numberOfParts := D.numberOfParts
    number_pos := D.number_pos
    part := directionalLayerCentres D order
    direction := fun j ↦ D.period (order j)
    direction_ne_zero := fun j ↦ D.period_ne_zero (order j)
    pairwise_incommensurable := by
      intro i j hij
      exact D.pairwise_incommensurable (order i) (order j) (order.injective.ne hij)
    periodic_part := by
      intro j x
      apply (indicator_eq_iff_membership (directionalLayerCentres D order j) _ _).2
      have hp := (directionalLayerCentres_periodic D order j).zsmul (ell : ℤ)
      convert hp x using 1
    pairwiseDisjoint := by
      intro i _ j _ hij
      change Disjoint (directionalLayerCentres D order i)
        (directionalLayerCentres D order j)
      rw [Set.disjoint_left]
      intro x hxi hxj
      obtain ⟨P, hxPi⟩ := Set.mem_iUnion.mp hxi
      obtain ⟨Q, hxQj⟩ := Set.mem_iUnion.mp hxj
      by_cases hPQ : P = Q
      · subst Q
        exact (Set.disjoint_left.mp
          (D.pairwiseDisjoint P (Set.mem_univ (order i))
            (Set.mem_univ (order j)) (order.injective.ne hij))) hxPi hxQj
      · have hxP : x ∈ Tiling.RationalPolygonal.quakePlateTranslations P := by
          rw [← D.iUnion_parts P]
          exact Set.mem_iUnion.mpr ⟨order i, hxPi⟩
        have hxQ : x ∈ Tiling.RationalPolygonal.quakePlateTranslations Q := by
          rw [← D.iUnion_parts Q]
          exact Set.mem_iUnion.mpr ⟨order j, hxQj⟩
        exact (Set.disjoint_left.mp
          (verticalPlateCentres_pairwiseDisjoint F A hPQ)) hxP hxQ
    union_parts := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨j, P, hxPj⟩ := Set.mem_iUnion₂.mp hx
        rw [← iUnion_verticalPlateCentres F A]
        apply Set.mem_iUnion.mpr
        refine ⟨P, ?_⟩
        rw [← D.iUnion_parts P]
        exact Set.mem_iUnion.mpr ⟨order j, hxPj⟩
      · intro x hx
        rw [← iUnion_verticalPlateCentres F A] at hx
        obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
        rw [← D.iUnion_parts P] at hxP
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxP
        exact Set.mem_iUnion.mpr ⟨order.symm i,
          Set.mem_iUnion.mpr ⟨P, by
            change x ∈ D.part P (order (order.symm i))
            simpa only [order.apply_symm_apply] using hxi⟩⟩
    target_periodic := hEPeriodic
    tiles := hTile
  }
  obtain ⟨N, hN, hperiod⟩ :=
    Tiling.AxisParallel.Foundations.gtCommonDirectionalCarrierPeriod G hell
  refine ⟨ell * N, Nat.mul_pos hell hN, ⟨N, rfl⟩, fun j ↦ ?_⟩
  apply setScalarPeriodic_of_dvd (hS := hperiod j)
  exact ⟨ell, (Nat.mul_comm N ell).symm⟩

theorem exists_commonNonverticalPlateLayerScalarPeriod
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {ell N k : ℕ}
    (hF : F.Nonempty) (_hell : 0 < ell)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy
      E verticalDiscreteUnit)
    (_hEPeriodic : TranslationalTilings.SetScalarPeriodic ell E)
    (hTile : TranslationalTilings.Tiles F A E)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (hk : 0 < k)
    (hfirst : D.period (order ⟨0, D.number_pos⟩) =
      (k : ℤ) • verticalDiscreteUnit)
    (hN : 0 < N) (hellN : ell ∣ N)
    (hGlobal : ∀ j, TranslationalTilings.SetScalarPeriodic N
      (Tiling.RationalPolygonal.discreteCarrier F
        (directionalLayerCentres D order j))) :
    ∃ M : ℕ, 0 < M ∧ N ∣ M ∧ ell ∣ M ∧ k ∣ M ∧
      (∀ (P : Tiling.RationalPolygonal.QuakePlate
          F A verticalDiscreteUnit)
        (j : Fin D.numberOfParts),
        j ≠ ⟨0, D.number_pos⟩ →
          TranslationalTilings.SetScalarPeriodic M
            (Tiling.RationalPolygonal.discreteCarrier F
              (orderedPlateLayer D order P j))) ∧
      TranslationalTilings.SetScalarPeriodic M
        (Tiling.RationalPolygonal.discreteCarrier F
          (directionalLayerCentres D order ⟨0, D.number_pos⟩)) := by
  classical
  let first : Fin D.numberOfParts := ⟨0, D.number_pos⟩
  let J := {j : Fin D.numberOfParts // j ≠ first}
  let width : J → ℕ := fun j ↦ Int.natAbs (D.period (order j.1) 0)
  have hcoord (j : Fin D.numberOfParts) (hj : j ≠ first) :
      D.period (order j) 0 ≠ 0 := by
    intro hj0
    have hj1 : D.period (order j) 1 ≠ 0 := by
      intro hj1
      apply D.period_ne_zero (order j)
      funext i
      fin_cases i <;> assumption
    have hcomm : TranslationalTilings.Commensurable
        (D.period (order first)) (D.period (order j)) := by
      refine ⟨D.period (order j) 1, (k : ℤ), hj1,
        by exact_mod_cast (Nat.ne_of_gt hk), ?_⟩
      rw [hfirst]
      funext i
      fin_cases i
      · change D.period (order j) 1 * (k * 0) = k * D.period (order j) 0
        rw [hj0]
        ring
      · change D.period (order j) 1 * (k * 1) = k * D.period (order j) 1
        ring
    exact (D.pairwise_incommensurable (order first) (order j)
      (order.injective.ne hj.symm)) hcomm
  have hwidth (j : J) : 0 < width j := by
    exact Int.natAbs_pos.mpr (hcoord j.1 j.2)
  let Q : ℕ := ∏ j : J, width j
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact Finset.prod_pos fun j _ ↦ hwidth j
  let M := N * k * Q
  refine ⟨M, Nat.mul_pos (Nat.mul_pos hN hk) hQ, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨k * Q, by simp [M, Nat.mul_assoc]⟩
  · exact dvd_trans hellN ⟨k * Q, by simp [M, Nat.mul_assoc]⟩
  · exact ⟨N * Q, by simp [M, Nat.mul_left_comm, Nat.mul_assoc]⟩
  · intro P j hj
    let v := D.period (order j)
    let S := Tiling.RationalPolygonal.discreteCarrier F (orderedPlateLayer D order P j)
    have hRank : Tiling.RationalPolygonal.DiscretePeriodicBy S v :=
      carrier_periodic_of_centres (D.periodic_part P (order j))
    have hInter := orderedPlateLayerCarrier_eq_inter hTile D order P j
    have hVerticalN : Tiling.RationalPolygonal.DiscretePeriodicBy S
        ((N : ℤ) • verticalDiscreteUnit) := by
      dsimp only [S]
      rw [hInter]
      intro z
      constructor
      · rintro ⟨hzG, hzP⟩
        exact ⟨(hGlobal j z verticalDiscreteUnit).mp hzG,
          ((verticalPlateCarrier_periodic hF hTile hEVertical P).zsmul (N : ℤ) z).mp hzP⟩
      · rintro ⟨hzG, hzP⟩
        exact ⟨(hGlobal j z verticalDiscreteUnit).mpr hzG,
          ((verticalPlateCarrier_periodic hF hTile hEVertical P).zsmul (N : ℤ) z).mpr hzP⟩
    have hHorizontal : Tiling.RationalPolygonal.DiscretePeriodicBy S
        (((N * Int.natAbs (v 0) : ℕ) : ℤ) • horizontalDiscreteUnit) := by
      let r : ℤ := (N : ℤ) * Int.sign (v 0)
      let s : ℤ := -(Int.sign (v 0) * v 1)
      have hrank := hRank.zsmul r
      have hvert := hVerticalN.zsmul s
      intro z
      have hcombined := (hvert (z + r • v)).trans (hrank z)
      have hpoint :
          z + (((N * Int.natAbs (v 0) : ℕ) : ℤ) • horizontalDiscreteUnit) =
            (z + r • v) + s • ((N : ℤ) • verticalDiscreteUnit) := by
        funext i
        fin_cases i
        · change z 0 + (N * Int.natAbs (v 0) : ℕ) * 1 =
          (z 0 + r * v 0) + s * (N * 0)
          dsimp only [r, s]
          push_cast
          rw [← Int.sign_mul_self_eq_abs]
          ring
        · change z 1 + (N * Int.natAbs (v 0) : ℕ) * 0 =
            (z 1 + r * v 1) + s * (N * 1)
          dsimp only [r, s]
          push_cast
          ring
      rw [hpoint]
      exact hcombined
    have hScalar : TranslationalTilings.SetScalarPeriodic
        (N * Int.natAbs (v 0)) S := by
      intro z w
      have hh := hHorizontal.zsmul (w 0)
      have hv := hVerticalN.zsmul ((Int.natAbs (v 0) : ℤ) * w 1)
      have hcombined := (hv
        (z + (w 0) • (((N * Int.natAbs (v 0) : ℕ) : ℤ) •
          horizontalDiscreteUnit))).trans (hh z)
      have hpoint : z + (((N * Int.natAbs (v 0) : ℕ) : ℤ) • w) =
          (z + (w 0) • (((N * Int.natAbs (v 0) : ℕ) : ℤ) •
            horizontalDiscreteUnit)) +
            ((Int.natAbs (v 0) : ℤ) * w 1) •
              ((N : ℤ) • verticalDiscreteUnit) := by
        ext i
        simp only [Pi.add_apply, Pi.smul_apply]
        fin_cases i
        · simp [horizontalDiscreteUnit, verticalDiscreteUnit]
          ring
        · simp [horizontalDiscreteUnit, verticalDiscreteUnit]
          ring
      rw [hpoint]
      exact hcombined
    apply setScalarPeriodic_of_dvd (hS := hScalar)
    let jj : J := ⟨j, hj⟩
    have hwidthQ : width jj ∣ Q := by
      exact Finset.dvd_prod_of_mem width (Finset.mem_univ jj)
    obtain ⟨t, ht⟩ := hwidthQ
    refine ⟨k * t, ?_⟩
    dsimp only [M] at ⊢
    have hw : Int.natAbs (v 0) = width jj := rfl
    rw [hw, ht]
    ring
  · apply setScalarPeriodic_of_dvd
      (hS := hGlobal first)
    exact ⟨k * Q, by simp [M, Nat.mul_assoc]⟩

theorem quakeShift_preservesDirectionalDecomposition
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (shift : Tiling.RationalPolygonal.QuakePlate
      F A verticalDiscreteUnit → ℤ)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit) :
    Set.PairwiseDisjoint Set.univ (shiftedPlateLayer D order shift P) ∧
      (⋃ j, shiftedPlateLayer D order shift P j) =
        TranslationalTilings.translateSet
          ((shift P) • verticalDiscreteUnit)
          (Tiling.RationalPolygonal.quakePlateTranslations P) ∧
      ∀ j, Tiling.RationalPolygonal.DiscretePeriodicBy
        (shiftedPlateLayer D order shift P j) (D.period (order j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i _ j _ hij
    change Disjoint (shiftedPlateLayer D order shift P i)
      (shiftedPlateLayer D order shift P j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hbasei : x - (shift P) • verticalDiscreteUnit ∈
        D.part P (order i) := hxi
    have hbasej : x - (shift P) • verticalDiscreteUnit ∈
        D.part P (order j) := hxj
    exact (Set.disjoint_left.mp
      (D.pairwiseDisjoint P (Set.mem_univ (order i))
        (Set.mem_univ (order j)) (order.injective.ne hij))) hbasei hbasej
  · ext x
    constructor
    · intro hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      change x - (shift P) • verticalDiscreteUnit ∈
        Tiling.RationalPolygonal.quakePlateTranslations P
      rw [← D.iUnion_parts P]
      exact Set.mem_iUnion.mpr ⟨order j, hxj⟩
    · intro hx
      change x - (shift P) • verticalDiscreteUnit ∈
        Tiling.RationalPolygonal.quakePlateTranslations P at hx
      rw [← D.iUnion_parts P] at hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      apply Set.mem_iUnion.mpr
      refine ⟨order.symm i, ?_⟩
      change x - (shift P) • verticalDiscreteUnit ∈
        D.part P (order (order.symm i))
      simpa only [order.apply_symm_apply] using hxi
  · intro j x
    change
      x + D.period (order j) - (shift P) • verticalDiscreteUnit ∈
          D.part P (order j) ↔
        x - (shift P) • verticalDiscreteUnit ∈ D.part P (order j)
    convert D.periodic_part P (order j)
      (x - (shift P) • verticalDiscreteUnit) using 1
    all_goals abel

theorem quakeShift_directionalCarriers_scalarPeriodic
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {ell k M : ℕ}
    (hF : F.Nonempty) (_hell : 0 < ell)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy
      E verticalDiscreteUnit)
    (hEPeriodic : TranslationalTilings.SetScalarPeriodic ell E)
    (hTile : TranslationalTilings.Tiles F A E)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (_hk : 0 < k)
    (_hfirst : D.period (order ⟨0, D.number_pos⟩) =
      (k : ℤ) • verticalDiscreteUnit)
    (_hM : 0 < M) (hellM : ell ∣ M) (_hkM : k ∣ M)
    (hPlate : ∀ (P : Tiling.RationalPolygonal.QuakePlate
        F A verticalDiscreteUnit)
      (j : Fin D.numberOfParts),
      j ≠ ⟨0, D.number_pos⟩ →
        TranslationalTilings.SetScalarPeriodic M
          (Tiling.RationalPolygonal.discreteCarrier F
            (orderedPlateLayer D order P j)))
    (shift : Tiling.RationalPolygonal.QuakePlate
      F A verticalDiscreteUnit → ℤ) :
    (∀ (P : Tiling.RationalPolygonal.QuakePlate
        F A verticalDiscreteUnit)
      (j : Fin D.numberOfParts),
      j ≠ ⟨0, D.number_pos⟩ →
        TranslationalTilings.SetScalarPeriodic M
          (Tiling.RationalPolygonal.discreteCarrier F
            (shiftedPlateLayer D order shift P j))) ∧
      TranslationalTilings.SetScalarPeriodic M
        (Tiling.RationalPolygonal.discreteCarrier F
          (shiftedDirectionalLayerCentres D order shift
            ⟨0, D.number_pos⟩)) := by
  classical
  let first : Fin D.numberOfParts := ⟨0, D.number_pos⟩
  let J := {j : Fin D.numberOfParts // j ≠ first}
  let B := Tiling.RationalPolygonal.quakeShiftedTranslations shift
  let C := shiftedDirectionalLayerCentres D order shift first
  let R : Set TranslationalTilings.Plane :=
    ⋃ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
      ⋃ j : J, shiftedPlateLayer D order shift P j.1
  have hNonfirst (P : Tiling.RationalPolygonal.QuakePlate
      F A verticalDiscreteUnit) (j : Fin D.numberOfParts) (hj : j ≠ first) :
      TranslationalTilings.SetScalarPeriodic M
        (Tiling.RationalPolygonal.discreteCarrier F
          (shiftedPlateLayer D order shift P j)) := by
    change TranslationalTilings.SetScalarPeriodic M
      (Tiling.RationalPolygonal.discreteCarrier F
        (TranslationalTilings.translateSet ((shift P) • verticalDiscreteUnit)
          (orderedPlateLayer D order P j)))
    rw [discreteCarrier_translateSet]
    exact setScalarPeriodic_translateSet (hPlate P j hj)
      ((shift P) • verticalDiscreteUnit)
  have hCsubset : C ⊆ B := by
    intro x hx
    obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
    exact shiftedPlateLayer_subset_quakeShifted D order shift P first hxP
  have hRsubset : R ⊆ B := by
    intro x hx
    obtain ⟨P, j, hxPj⟩ := Set.mem_iUnion₂.mp hx
    exact shiftedPlateLayer_subset_quakeShifted D order shift P j.1 hxPj
  have hCover : C ∪ R = B := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx with hxC | hxR
      · exact hCsubset hxC
      · exact hRsubset hxR
    · intro x hx
      obtain ⟨a, hxa⟩ := hx
      let P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit :=
        (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).connectedComponentMk a
      have hxPlate : x ∈ TranslationalTilings.translateSet
          ((shift P) • verticalDiscreteUnit)
          (Tiling.RationalPolygonal.quakePlateTranslations P) := by
        change x - (shift P) • verticalDiscreteUnit ∈
          Tiling.RationalPolygonal.quakePlateTranslations P
        have haP := Tiling.RationalPolygonal.mem_quakePlateTranslations_mk
          (F := F) (v := verticalDiscreteUnit) a
        rw [← hxa]
        dsimp only [P]
        simpa only [add_sub_cancel_left] using haP
      rw [← (quakeShift_preservesDirectionalDecomposition D order shift P).2.1] at hxPlate
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxPlate
      by_cases hj : j = first
      · left
        exact Set.mem_iUnion.mpr ⟨P, hj ▸ hxj⟩
      · right
        exact Set.mem_iUnion.mpr ⟨P,
          Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩⟩
  have hDisjoint : Disjoint C R := by
    rw [Set.disjoint_left]
    intro x hxC hxR
    obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hxC
    obtain ⟨Q, j, hxQ⟩ := Set.mem_iUnion₂.mp hxR
    obtain ⟨f, hfF⟩ := hF
    have hxCarrierP : f + x ∈ Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P) := by
      have hbase : f + (x - (shift P) • verticalDiscreteUnit) ∈
          Tiling.RationalPolygonal.discreteCarrier F
            (Tiling.RationalPolygonal.quakePlateTranslations P) := by
        refine ⟨f, hfF, x - (shift P) • verticalDiscreteUnit, ?_, rfl⟩
        rw [← D.iUnion_parts P]
        exact Set.mem_iUnion.mpr ⟨order first, hxP⟩
      have hp := ((verticalPlateCarrier_periodic ⟨f, hfF⟩ hTile hEVertical P).zsmul
        (shift P) (f + (x - (shift P) • verticalDiscreteUnit))).2 hbase
      convert hp using 1
      all_goals abel
    have hxCarrierQ : f + x ∈ Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations Q) := by
      have hbase : f + (x - (shift Q) • verticalDiscreteUnit) ∈
          Tiling.RationalPolygonal.discreteCarrier F
            (Tiling.RationalPolygonal.quakePlateTranslations Q) := by
        refine ⟨f, hfF, x - (shift Q) • verticalDiscreteUnit, ?_, rfl⟩
        rw [← D.iUnion_parts Q]
        exact Set.mem_iUnion.mpr ⟨order j.1, hxQ⟩
      have hp := ((verticalPlateCarrier_periodic ⟨f, hfF⟩ hTile hEVertical Q).zsmul
        (shift Q) (f + (x - (shift Q) • verticalDiscreteUnit))).2 hbase
      convert hp using 1
      all_goals abel
    have hPQ : P = Q := by
      by_contra hne
      exact (Set.disjoint_left.mp (plateCarriers_disjoint hTile hne))
        hxCarrierP hxCarrierQ
    subst Q
    exact (Set.disjoint_left.mp
      (D.pairwiseDisjoint P (Set.mem_univ (order first))
        (Set.mem_univ (order j.1)) (order.injective.ne j.2.symm))) hxP hxQ
  have hCeq : C = B \ R := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hCsubset hx, fun hxR ↦ (Set.disjoint_left.mp hDisjoint) hx hxR⟩
    · rintro x ⟨hxB, hxR⟩
      have hx := hCover.symm ▸ hxB
      rcases hx with hxC | hxR'
      · exact hxC
      · exact False.elim (hxR hxR')
  have hRperiod : TranslationalTilings.SetScalarPeriodic M
      (Tiling.RationalPolygonal.discreteCarrier F R) := by
    dsimp only [R]
    rw [discreteCarrier_iUnion]
    simp_rw [discreteCarrier_iUnion]
    intro x z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨P, j, hx⟩
      exact ⟨P, j, (hNonfirst P j.1 j.2 x z).mp hx⟩
    · rintro ⟨P, j, hx⟩
      exact ⟨P, j, (hNonfirst P j.1 j.2 x z).mpr hx⟩
  refine ⟨?_, ?_⟩
  · intro P j hj
    exact hNonfirst P j hj
  · have hShiftTile := tilesOn_quakeShiftedTranslations hF hTile hEVertical shift
    have hcarrierB : Tiling.RationalPolygonal.discreteCarrier F B = E :=
      discreteCarrier_eq_target_of_tiles hShiftTile
    rw [show shiftedDirectionalLayerCentres D order shift ⟨0, D.number_pos⟩ = C from rfl,
      hCeq,
      discreteCarrier_sdiff hShiftTile (Set.Subset.rfl : B ⊆ B) hRsubset,
      hcarrierB]
    have hEperiodM := setScalarPeriodic_of_dvd hellM hEPeriodic
    intro x z
    constructor
    · rintro ⟨hxE, hxR⟩
      refine ⟨(hEperiodM x z).mp hxE, ?_⟩
      intro hx
      exact hxR ((hRperiod x z).mpr hx)
    · rintro ⟨hxE, hxR⟩
      refine ⟨(hEperiodM x z).mpr hxE, ?_⟩
      intro hx
      exact hxR ((hRperiod x z).mp hx)

end Tiling.AxisParallel.Discrete
