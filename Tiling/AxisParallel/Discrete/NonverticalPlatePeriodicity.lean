import Tiling.AxisParallel.Discrete.VerticalSliceTransport

/-!
# Scalar periodicity of plates with a nonvertical layer

Starting from the nonvertical layers, propagate whole periodic congruence slices along a
plate enumeration. Exactness of the tiling and vertical saturation keep every stage inside
the original plate. Their union exhausts its carrier and inherits one tile-uniform period.
-/

open Set TranslationalTilings

namespace Tiling.AxisParallel.Discrete

private noncomputable def propagatedCentres
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (r : ℕ ≃ {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)})
    (centre : ℕ → TranslationalTilings.Plane)
    (L : ℕ) (n : ℕ) : Set TranslationalTilings.Plane := by
  classical
  exact Nat.rec
    (⋃ j : {j : Fin D.numberOfParts // j ≠ ⟨0, D.number_pos⟩},
      orderedPlateLayer D order P j.1)
    (fun m C =>
      if (r (m + 1) : TranslationalTilings.Plane) ∈
          Tiling.RationalPolygonal.discreteCarrier F C then C
      else C ∪
        (directionalLayerCentres D order ⟨0, D.number_pos⟩ ∩
          verticalDiscreteCongruenceClass
            (firstDiscreteCoordinate (centre (m + 1))) L)) n

private theorem scalarPeriodic_of_dvd
    {d p q : ℕ} {S : Set (TranslationalTilings.Lattice d)}
    (hpq : p ∣ q) (hS : TranslationalTilings.SetScalarPeriodic p S) :
    TranslationalTilings.SetScalarPeriodic q S := by
  obtain ⟨m, rfl⟩ := hpq
  intro x z
  simpa only [Nat.cast_mul, mul_smul] using hS x ((m : ℤ) • z)

private theorem centre_eq_of_representations
    {G : Type*} [AddCommGroup G] {F : Finset G} {A E : Set G}
    (hTile : TranslationalTilings.Tiles F A E)
    {f g a b : G} (hf : f ∈ F) (ha : a ∈ A) (hg : g ∈ F) (hb : b ∈ A)
    (heq : f + a = g + b) : a = b := by
  classical
  have hcount := (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp hTile
  have hxE : f + a ∈ E := by
    by_contra hx
    have hz : (F.filter fun q => f + a - q ∈ A).card = 0 := by simpa [hx] using hcount (f + a)
    have hm : f ∈ F.filter fun q => f + a - q ∈ A := by
      simp only [Finset.mem_filter, hf, true_and]
      simpa only [add_sub_cancel_left] using ha
    rw [Finset.card_eq_zero.mp hz] at hm
    simp at hm
  have hc : (F.filter fun q => f + a - q ∈ A).card = 1 := by simpa [hxE] using hcount (f + a)
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hc
  have hfm : f ∈ F.filter fun q => f + a - q ∈ A := by
    simp only [Finset.mem_filter, hf, true_and]
    simpa only [add_sub_cancel_left] using ha
  have hgm : g ∈ F.filter fun q => f + a - q ∈ A := by
    refine Finset.mem_filter.mpr ⟨hg, ?_⟩
    rw [heq]
    simpa only [add_sub_cancel_left] using hb
  have hfq : f = q := by simpa [hq] using hfm
  have hgq : g = q := by simpa [hq] using hgm
  have hfg : f = g := hfq.trans hgq.symm
  rw [hfg] at heq
  exact add_left_cancel heq

private theorem same_firstCoordinate_vertical_shift
    {x y : TranslationalTilings.Plane}
    (h : firstDiscreteCoordinate x = firstDiscreteCoordinate y) :
    ∃ n : ℤ, x + n • verticalDiscreteUnit = y := by
  refine ⟨y 1 - x 1, ?_⟩
  funext i
  fin_cases i
  · change x 0 + (y 1 - x 1) * 0 = y 0
    change x 0 = y 0 at h
    omega
  · change x 1 + (y 1 - x 1) * 1 = y 1
    ring

private theorem nonfirstUnion_subset
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit) :
    (⋃ j : {j : Fin D.numberOfParts // j ≠ ⟨0, D.number_pos⟩},
      orderedPlateLayer D order P j.1) ⊆ Tiling.RationalPolygonal.quakePlateTranslations P := by
  intro x hx
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
  rw [← D.iUnion_parts P]
  exact Set.mem_iUnion.mpr ⟨order j.1, hxj⟩

private theorem nonfirstUnion_periodic
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane} {L : ℕ}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hLayer : ∀ j : Fin D.numberOfParts, j ≠ ⟨0, D.number_pos⟩ →
      TranslationalTilings.SetScalarPeriodic L
        (Tiling.RationalPolygonal.discreteCarrier F (orderedPlateLayer D order P j))) :
    TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier F
        (⋃ j : {j : Fin D.numberOfParts // j ≠ ⟨0, D.number_pos⟩},
          orderedPlateLayer D order P j.1)) := by
  rw [discreteCarrier_iUnion]
  intro x z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (hLayer j.1 j.2 x z).mp hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, (hLayer j.1 j.2 x z).mpr hj⟩

private theorem propagatedCentres_zero
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (r : ℕ ≃ {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)})
    (centre : ℕ → TranslationalTilings.Plane) (L : ℕ) :
    propagatedCentres D order P r centre L 0 =
      ⋃ j : {j : Fin D.numberOfParts // j ≠ ⟨0, D.number_pos⟩},
        orderedPlateLayer D order P j.1 := by
  rfl

private theorem propagatedCentres_succ_of_mem
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (r : ℕ ≃ {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)})
    (centre : ℕ → TranslationalTilings.Plane) (L n : ℕ)
    (hmem : (r (n + 1) : TranslationalTilings.Plane) ∈
      Tiling.RationalPolygonal.discreteCarrier F (propagatedCentres D order P r centre L n)) :
    propagatedCentres D order P r centre L (n + 1) = propagatedCentres D order P r centre L n := by
  classical
  change (if (r (n + 1) : TranslationalTilings.Plane) ∈
      Tiling.RationalPolygonal.discreteCarrier F
        (propagatedCentres D order P r centre L n) then
      propagatedCentres D order P r centre L n else _) = _
  rw [if_pos hmem]

private theorem propagatedCentres_succ_of_not_mem
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (r : ℕ ≃ {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)})
    (centre : ℕ → TranslationalTilings.Plane) (L n : ℕ)
    (hmem : (r (n + 1) : TranslationalTilings.Plane) ∉
      Tiling.RationalPolygonal.discreteCarrier F (propagatedCentres D order P r centre L n)) :
    propagatedCentres D order P r centre L (n + 1) =
      propagatedCentres D order P r centre L n ∪
        (directionalLayerCentres D order ⟨0, D.number_pos⟩ ∩
          verticalDiscreteCongruenceClass (firstDiscreteCoordinate (centre (n + 1))) L) := by
  classical
  change (if (r (n + 1) : TranslationalTilings.Plane) ∈
      Tiling.RationalPolygonal.discreteCarrier F
        (propagatedCentres D order P r centre L n) then _ else
      propagatedCentres D order P r centre L n ∪
        (directionalLayerCentres D order ⟨0, D.number_pos⟩ ∩
          verticalDiscreteCongruenceClass
            (firstDiscreteCoordinate (centre (n + 1))) L)) = _
  rw [if_neg hmem]

private theorem propagatedCentres_mono
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane} {L : ℕ}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (r : ℕ ≃ {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)})
    (centre : ℕ → TranslationalTilings.Plane) (n : ℕ) :
    propagatedCentres D order P r centre L n ⊆ propagatedCentres D order P r centre L (n + 1) := by
  classical
  by_cases h : (r (n + 1) : TranslationalTilings.Plane) ∈
      Tiling.RationalPolygonal.discreteCarrier F
        (propagatedCentres D order P r centre L n)
  · rw [propagatedCentres_succ_of_mem D order P r centre L n h]
  · rw [propagatedCentres_succ_of_not_mem D order P r centre L n h]
    exact Set.subset_union_left

private theorem propagatedCarrier_scalarPeriodic
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane} {L : ℕ}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (r : ℕ ≃ {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)})
    (centre : ℕ → TranslationalTilings.Plane)
    (hBase : TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier F
        (propagatedCentres D order P r centre L 0)))
    (hSlice : ∀ x : ℤ, TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier F
        (directionalLayerCentres D order ⟨0, D.number_pos⟩ ∩
          verticalDiscreteCongruenceClass x L))) :
    ∀ n, TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier F
        (propagatedCentres D order P r centre L n)) := by
  intro n
  induction n with
  | zero => exact hBase
  | succ n ih =>
      classical
      by_cases hmem : (r (n + 1) : TranslationalTilings.Plane) ∈
          Tiling.RationalPolygonal.discreteCarrier F
            (propagatedCentres D order P r centre L n)
      · rw [propagatedCentres_succ_of_mem D order P r centre L n hmem]
        exact ih
      · rw [propagatedCentres_succ_of_not_mem D order P r centre L n hmem,
          discreteCarrier_union]
        intro x z
        exact or_congr (ih x z) (hSlice (firstDiscreteCoordinate (centre (n + 1))) x z)

private theorem propagatedCarrier_iUnion_eq
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane} {L : ℕ}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (r : ℕ ≃ {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)})
    (centre : ℕ → TranslationalTilings.Plane)
    (hSub : ∀ n, propagatedCentres D order P r centre L n ⊆
      Tiling.RationalPolygonal.quakePlateTranslations P)
    (hEnum : ∀ n, (r n : TranslationalTilings.Plane) ∈
      Tiling.RationalPolygonal.discreteCarrier F
        (propagatedCentres D order P r centre L n)) :
    (⋃ n, Tiling.RationalPolygonal.discreteCarrier F
      (propagatedCentres D order P r centre L n)) =
      Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P) := by
  apply Set.Subset.antisymm
  · rintro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    obtain ⟨f, hf, c, hc, rfl⟩ := hxn
    exact ⟨f, hf, c, hSub n hc, rfl⟩
  · intro x hx
    let xs : {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P)} := ⟨x, hx⟩
    let n := r.symm xs
    have hrn : (r n : TranslationalTilings.Plane) = x := by
      exact congrArg Subtype.val (r.apply_symm_apply xs)
    exact Set.mem_iUnion.mpr ⟨n, hrn ▸ hEnum n⟩

private theorem propagatedCentres_mono_le
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane} {L : ℕ}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (r : ℕ ≃ {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)})
    (centre : ℕ → TranslationalTilings.Plane) {m n : ℕ} (hmn : m ≤ n) :
    propagatedCentres D order P r centre L m ⊆ propagatedCentres D order P r centre L n := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n hmn ih => exact ih.trans (propagatedCentres_mono D order P r centre n)

private theorem enumeratedPoint_mem_propagatedCarrier_core
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane} {L : ℕ}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (r : ℕ ≃ {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)})
    (tilePoint centre : ℕ → TranslationalTilings.Plane)
    (hrTile : ∀ n, tilePoint n ∈ F)
    (hrCentre : ∀ n, centre n ∈ Tiling.RationalPolygonal.quakePlateTranslations P)
    (hrRep : ∀ n, (r n : TranslationalTilings.Plane) = tilePoint n + centre n)
    (hrRoot : centre 0 ∈ ⋃ j : {j : Fin D.numberOfParts // j ≠ ⟨0, D.number_pos⟩},
      orderedPlateLayer D order P j.1)
    :
    ∀ n, (r n : TranslationalTilings.Plane) ∈
      Tiling.RationalPolygonal.discreteCarrier F (propagatedCentres D order P r centre L n) := by
  intro n
  induction n with
  | zero =>
      exact ⟨tilePoint 0, hrTile 0, centre 0,
        by simpa [propagatedCentres] using hrRoot, hrRep 0⟩
  | succ n ih =>
      classical
      by_cases hmem : (r (n + 1) : TranslationalTilings.Plane) ∈
          Tiling.RationalPolygonal.discreteCarrier F (propagatedCentres D order P r centre L n)
      · rwa [propagatedCentres_succ_of_mem D order P r centre L n hmem]
      · rw [propagatedCentres_succ_of_not_mem D order P r centre L n hmem]
        refine ⟨tilePoint (n + 1), hrTile (n + 1), centre (n + 1), ?_, hrRep (n + 1)⟩
        right
        refine ⟨?_, (mem_verticalDiscreteCongruenceClass_iff _ _ _).mpr ⟨0, by simp⟩⟩
        rw [← D.iUnion_parts P] at hrCentre
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hrCentre (n + 1))
        let j := order.symm i
        have hji : order j = i := order.apply_symm_apply i
        by_cases hj : j = ⟨0, D.number_pos⟩
        · apply Set.mem_iUnion.mpr
          refine ⟨P, ?_⟩
          change centre (n + 1) ∈ D.part P (order ⟨0, D.number_pos⟩)
          rw [← hj, hji]
          exact hi
        · exfalso
          have hc0 : centre (n + 1) ∈ propagatedCentres D order P r centre L 0 := by
            rw [propagatedCentres_zero]
            apply Set.mem_iUnion.mpr
            refine ⟨⟨j, hj⟩, ?_⟩
            change centre (n + 1) ∈ D.part P (order j)
            rwa [hji]
          have hcn := propagatedCentres_mono_le D order P r centre (Nat.zero_le n) hc0
          exact hmem ⟨tilePoint (n + 1), hrTile (n + 1), centre (n + 1), hcn, hrRep (n + 1)⟩

set_option linter.unusedVariables false in
private theorem enumeratedPoint_mem_propagatedCarrier
    {F : Finset TranslationalTilings.Plane} {A E : Set TranslationalTilings.Plane} {L : ℕ}
    (hF : F.Nonempty) (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (r : ℕ ≃ {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)})
    (tilePoint centre : ℕ → TranslationalTilings.Plane)
    (hrTile : ∀ n, tilePoint n ∈ F)
    (hrCentre : ∀ n, centre n ∈ Tiling.RationalPolygonal.quakePlateTranslations P)
    (hrRep : ∀ n, (r n : TranslationalTilings.Plane) = tilePoint n + centre n)
    (hrRoot : centre 0 ∈ ⋃ j : {j : Fin D.numberOfParts // j ≠ ⟨0, D.number_pos⟩},
      orderedPlateLayer D order P j.1)
    (hrStep : ∀ n, 0 < n → ∃ m, m < n ∧ ∃ g ∈ F,
      firstDiscreteCoordinate (r n : TranslationalTilings.Plane) =
        firstDiscreteCoordinate (g + centre m))
    (hSub : ∀ n, propagatedCentres D order P r centre L n ⊆
      Tiling.RationalPolygonal.quakePlateTranslations P) :
    ∀ n, (r n : TranslationalTilings.Plane) ∈
      Tiling.RationalPolygonal.discreteCarrier F (propagatedCentres D order P r centre L n) :=
  enumeratedPoint_mem_propagatedCarrier_core D order P r tilePoint centre
    hrTile hrCentre hrRep hrRoot

set_option linter.unusedVariables false in
private theorem propagatedCentres_subset_plate
    {F : Finset TranslationalTilings.Plane} {A E : Set TranslationalTilings.Plane} {L : ℕ}
    (hF : F.Nonempty) (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (r : ℕ ≃ {x // x ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P)})
    (tilePoint centre : ℕ → TranslationalTilings.Plane)
    (hrTile : ∀ n, tilePoint n ∈ F)
    (hrCentre : ∀ n, centre n ∈ Tiling.RationalPolygonal.quakePlateTranslations P)
    (hrRep : ∀ n, (r n : TranslationalTilings.Plane) = tilePoint n + centre n)
    (hrRoot : centre 0 ∈ ⋃ j : {j : Fin D.numberOfParts // j ≠ ⟨0, D.number_pos⟩},
      orderedPlateLayer D order P j.1)
    (hrStep : ∀ n, 0 < n → ∃ m, m < n ∧ ∃ g ∈ F,
      firstDiscreteCoordinate (r n : TranslationalTilings.Plane) =
        firstDiscreteCoordinate (g + centre m))
    (hNonfirst : ∃ j : Fin D.numberOfParts,
      j ≠ ⟨0, D.number_pos⟩ ∧ (orderedPlateLayer D order P j).Nonempty)
    (hLayer : ∀ j : Fin D.numberOfParts, j ≠ ⟨0, D.number_pos⟩ →
      TranslationalTilings.SetScalarPeriodic L
        (Tiling.RationalPolygonal.discreteCarrier F (orderedPlateLayer D order P j)))
    (hSlice : ∀ x : ℤ, TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier F
        (directionalLayerCentres D order ⟨0, D.number_pos⟩ ∩
          verticalDiscreteCongruenceClass x L))) :
    ∀ n, propagatedCentres D order P r centre L n ⊆
      Tiling.RationalPolygonal.quakePlateTranslations P := by
  have hBase : TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier F
        (propagatedCentres D order P r centre L 0)) := by
    rw [propagatedCentres_zero]
    exact nonfirstUnion_periodic D order P hLayer
  have hStage := propagatedCarrier_scalarPeriodic D order P r centre hBase hSlice
  have hEnum := enumeratedPoint_mem_propagatedCarrier_core (L := L) D order P r tilePoint centre
    hrTile hrCentre hrRep hrRoot
  intro n
  induction n with
  | zero =>
      rw [propagatedCentres_zero]
      exact nonfirstUnion_subset D order P
  | succ n ih =>
      classical
      by_cases hmem : (r (n + 1) : TranslationalTilings.Plane) ∈
          Tiling.RationalPolygonal.discreteCarrier F
            (propagatedCentres D order P r centre L n)
      · rw [propagatedCentres_succ_of_mem D order P r centre L n hmem]
        exact ih
      · rw [propagatedCentres_succ_of_not_mem D order P r centre L n hmem]
        intro a' ha'
        rcases ha' with haOld | ⟨haFirst, haClass⟩
        · exact ih haOld
        obtain ⟨m, hmn, g, hgF, hfirst⟩ := hrStep (n + 1) (by omega)
        have hrm := hEnum m
        obtain ⟨f, hfF, c, hc, hrepC⟩ := hrm
        have hcStage := propagatedCentres_mono_le D order P r centre
          (Nat.le_of_lt_succ hmn) hc
        have hcEq : c = centre m := centre_eq_of_representations hTile hfF
          (ih hcStage).1 (hrTile m) (hrCentre m).1 (hrepC.symm.trans (hrRep m))
        have hcentreStage : centre m ∈ propagatedCentres D order P r centre L n :=
          hcEq ▸ hcStage
        have hxStage : g + centre m ∈ Tiling.RationalPolygonal.discreteCarrier F
            (propagatedCentres D order P r centre L n) :=
          ⟨g, hgF, centre m, hcentreStage, rfl⟩
        obtain ⟨q, hq⟩ := (mem_verticalDiscreteCongruenceClass_iff a'
          (firstDiscreteCoordinate (centre (n + 1))) L).mp haClass
        let u : TranslationalTilings.Plane := q • horizontalDiscreteUnit
        have hxShift := (hStage n (g + centre m) u).mpr hxStage
        have hxPlate : g + centre m + (L : ℤ) • u ∈
            Tiling.RationalPolygonal.discreteCarrier F
              (Tiling.RationalPolygonal.quakePlateTranslations P) := by
          obtain ⟨g', hg', c', hc', heq⟩ := hxShift
          exact ⟨g', hg', c', ih hc', heq⟩
        have haA : a' ∈ A := by
          obtain ⟨Q, haQ⟩ := Set.mem_iUnion.mp haFirst
          have : a' ∈ Tiling.RationalPolygonal.quakePlateTranslations Q := by
            rw [← D.iUnion_parts Q]
            exact Set.mem_iUnion.mpr ⟨order ⟨0, D.number_pos⟩, haQ⟩
          exact this.1
        have hsame : firstDiscreteCoordinate
              (g + centre m + (L : ℤ) • u) =
            firstDiscreteCoordinate (tilePoint (n + 1) + a') := by
          dsimp only [u]
          change (g + centre m) 0 + (L : ℤ) * (q * 1) =
            tilePoint (n + 1) 0 + a' 0
          change (r (n + 1) : TranslationalTilings.Plane) 0 = (g + centre m) 0 at hfirst
          have hrep0 := congrFun (hrRep (n + 1)) 0
          change a' 0 = centre (n + 1) 0 + q * (L : ℤ) at hq
          rw [← hfirst, hrep0, hq]
          simp only [Pi.add_apply]
          ring
        obtain ⟨v, hv⟩ := same_firstCoordinate_vertical_shift hsame
        have hyPlate := ((verticalPlateCarrier_periodic hF hTile hEVertical P).zsmul v
          (g + centre m + (L : ℤ) • u)).mpr hxPlate
        rw [hv] at hyPlate
        obtain ⟨g', hg'F, p, hpP, heqp⟩ := hyPlate
        exact (centre_eq_of_representations hTile (hrTile (n + 1)) haA hg'F hpP.1
          heqp) ▸ hpP

/-- A tile-uniform scalar period for the carrier of every plate with a nonvertical layer. -/
theorem nonverticalLayer_plateCarrier_scalarPeriodic
    {F : Finset TranslationalTilings.Plane} {A E : Set TranslationalTilings.Plane}
    {ell k : ℕ} (hF : F.Nonempty) (hell : 0 < ell)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (hEPeriodic : TranslationalTilings.SetScalarPeriodic ell E)
    (hTile : TranslationalTilings.Tiles F A E)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts)) (hk : 0 < k)
    (hfirst : D.period (order ⟨0, D.number_pos⟩) = (k : ℤ) • verticalDiscreteUnit) :
    ∃ L : ℕ, 0 < L ∧ ell ∣ L ∧ k ∣ L ∧
      ∀ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
        (∃ j : Fin D.numberOfParts, j ≠ ⟨0, D.number_pos⟩ ∧
          (orderedPlateLayer D order P j).Nonempty) →
        TranslationalTilings.SetScalarPeriodic L
          (Tiling.RationalPolygonal.discreteCarrier F
            (Tiling.RationalPolygonal.quakePlateTranslations P)) := by
  classical
  obtain ⟨N, hN, hellN, hGlobal⟩ :=
    exists_commonDirectionalCarrierScalarPeriod hF hell hEVertical hEPeriodic hTile D order
  obtain ⟨M, hM, hNM, hellM, hkM, hLayers, hFirst⟩ :=
    exists_commonNonverticalPlateLayerScalarPeriod hF hell hEVertical hEPeriodic hTile
      D order hk hfirst hN hellN hGlobal
  have hShiftedFirst (shift : Tiling.RationalPolygonal.QuakePlate
      F A verticalDiscreteUnit → ℤ) :
      TranslationalTilings.SetScalarPeriodic M
        (Tiling.RationalPolygonal.discreteCarrier F
          (shiftedDirectionalLayerCentres D order shift ⟨0, D.number_pos⟩)) :=
    (quakeShift_directionalCarriers_scalarPeriodic hF hell hEVertical hEPeriodic hTile
      D order hk hfirst hM hellM hkM hLayers shift).2
  obtain ⟨K, hKdef, hK, hTransport⟩ :=
    exists_uniformVerticalSliceTransport hF hell hEVertical hEPeriodic hTile D order
      hk hfirst hM hShiftedFirst
  let L := Nat.lcm M K
  have hML : M ∣ L := Nat.dvd_lcm_left M K
  have hKL : K ∣ L := Nat.dvd_lcm_right M K
  have hL : 0 < L := Nat.lcm_pos hM hK
  have hellL : ell ∣ L := hellM.trans hML
  have hkL : k ∣ L := hkM.trans hML
  refine ⟨L, hL, hellL, hkL, ?_⟩
  intro P hNonfirst
  have hLayerL (j : Fin D.numberOfParts) (hj : j ≠ ⟨0, D.number_pos⟩) :
      TranslationalTilings.SetScalarPeriodic L
        (Tiling.RationalPolygonal.discreteCarrier F (orderedPlateLayer D order P j)) :=
    scalarPeriodic_of_dvd hML (hLayers P j hj)
  let zeroShift : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit → ℤ :=
    fun _ => 0
  have hTransportZero (x d : ℤ) :
      TranslationalTilings.translateSet ((d * (K : ℤ)) • horizontalDiscreteUnit)
          (Tiling.RationalPolygonal.discreteCarrier F
            (shiftedDirectionalLayerCentres D order zeroShift ⟨0, D.number_pos⟩ ∩
              verticalDiscreteFibre x)) =
        Tiling.RationalPolygonal.discreteCarrier F
          (shiftedDirectionalLayerCentres D order zeroShift ⟨0, D.number_pos⟩ ∩
            verticalDiscreteFibre (x + d * (K : ℤ))) :=
    hTransport zeroShift x d
  have hSliceShift (x : ℤ) := verticalSliceOrbit_scalarPeriodic D order hk hfirst
    zeroShift hK hTransportZero hL hKL hkL x
  have hSliceL (x : ℤ) : TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier F
        (directionalLayerCentres D order ⟨0, D.number_pos⟩ ∩
          verticalDiscreteCongruenceClass x L)) := by
    simpa [zeroShift, shiftedDirectionalLayerCentres, shiftedPlateLayer,
      directionalLayerCentres,
      TranslationalTilings.translateSet] using hSliceShift x
  have hNonfirst' := hNonfirst
  obtain ⟨j, hj, a0, ha0⟩ := hNonfirst
  have ha0P : a0 ∈ Tiling.RationalPolygonal.quakePlateTranslations P := by
    rw [← D.iUnion_parts P]
    exact Set.mem_iUnion.mpr ⟨order j, ha0⟩
  obtain ⟨r, tilePoint, centre, hrTile, hrCentre, hrRep, hrZero, hrStep⟩ :=
    exists_verticalPlateEnumeration hF hTile hEVertical P ⟨a0, ha0P⟩
  have hrRoot : centre 0 ∈
      ⋃ j : {j : Fin D.numberOfParts // j ≠ ⟨0, D.number_pos⟩},
        orderedPlateLayer D order P j.1 := by
    rw [hrZero]
    exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, ha0⟩
  have hSub := propagatedCentres_subset_plate hF hTile hEVertical P D order r
    tilePoint centre hrTile hrCentre hrRep hrRoot hrStep hNonfirst' hLayerL hSliceL
  have hEnum := enumeratedPoint_mem_propagatedCarrier_core (L := L) D order P r
    tilePoint centre hrTile hrCentre hrRep hrRoot
  have hUnion := propagatedCarrier_iUnion_eq D order P r centre hSub hEnum
  have hBase : TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier F
        (propagatedCentres D order P r centre L 0)) := by
    rw [propagatedCentres_zero]
    exact nonfirstUnion_periodic D order P hLayerL
  have hStages := propagatedCarrier_scalarPeriodic D order P r centre hBase hSliceL
  rw [← hUnion]
  intro x z
  simp only [Set.mem_iUnion]
  constructor <;> rintro ⟨n, hn⟩
  · exact ⟨n, (hStages n x z).mp hn⟩
  · exact ⟨n, (hStages n x z).mpr hn⟩

end Tiling.AxisParallel.Discrete
