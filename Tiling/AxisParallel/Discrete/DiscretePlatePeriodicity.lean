import Tiling.AxisParallel.Discrete.NonverticalPlatePeriodicity
import Tiling.AxisParallel.Discrete.EarthquakeWeakPeriodicity

/-!
# Uniform periodicity of noncolumn discrete plates

Fibre isolation and a shifted separator propagate noncolumn plate fibres horizontally.
Together with nonvertical-layer propagation, this yields one scalar period for every
noncolumn carrier and for the complementary union of column carriers.
-/

open Set
open TranslationalTilings

namespace Tiling.AxisParallel.Discrete

private theorem same_firstCoordinate_eq_verticalTranslate
    {x y : TranslationalTilings.Plane}
    (hxy : firstDiscreteCoordinate x = firstDiscreteCoordinate y) :
    ∃ s : ℤ, x + s • verticalDiscreteUnit = y := by
  refine ⟨y 1 - x 1, ?_⟩
  funext i
  fin_cases i
  · change x 0 + (y 1 - x 1) * 0 = y 0
    change x 0 = y 0 at hxy
    omega
  · change x 1 + (y 1 - x 1) * 1 = y 1
    ring

theorem verticalLayer_fibre_isolated
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (hTile : TranslationalTilings.Tiles F A E)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hVerticalOnly : orderedPlateLayer D order P
      ⟨0, D.number_pos⟩ =
        Tiling.RationalPolygonal.quakePlateTranslations P)
    {c : ℤ}
    (hc : (Tiling.RationalPolygonal.quakePlateTranslations P ∩
      verticalDiscreteFibre c).Nonempty) :
    directionalLayerCentres D order ⟨0, D.number_pos⟩ ∩
        verticalDiscreteFibre c =
      Tiling.RationalPolygonal.quakePlateTranslations P ∩
        verticalDiscreteFibre c := by
  classical
  apply Set.Subset.antisymm
  · rintro b ⟨hbGlobal, hbFibre⟩
    obtain ⟨Q, hbLayer⟩ := Set.mem_iUnion.mp hbGlobal
    have hbQ : b ∈ Tiling.RationalPolygonal.quakePlateTranslations Q := by
      rw [← D.iUnion_parts Q]
      exact Set.mem_iUnion.mpr ⟨order ⟨0, D.number_pos⟩, hbLayer⟩
    obtain ⟨a, haP, haFibre⟩ := hc
    obtain ⟨f, hf⟩ := hF
    have hF' : F.Nonempty := ⟨f, hf⟩
    have hcoord : firstDiscreteCoordinate (f + a) =
        firstDiscreteCoordinate (f + b) := by
      have ha := (mem_verticalDiscreteFibre_iff a c).mp haFibre
      have hb := (mem_verticalDiscreteFibre_iff b c).mp hbFibre
      change f 0 + a 0 = f 0 + b 0
      change a 0 = c at ha
      change b 0 = c at hb
      omega
    obtain ⟨s, hs⟩ := same_firstCoordinate_eq_verticalTranslate hcoord
    have hbase : f + a ∈ Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P) :=
      ⟨f, hf, a, haP, rfl⟩
    have hshift :=
      ((verticalPlateCarrier_periodic hF' hTile hEVertical P).zsmul s (f + a)).2 hbase
    have hfbP : f + b ∈ Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P) := by
      rwa [hs] at hshift
    obtain ⟨g, hg, p, hpP, hgp⟩ := hfbP
    obtain ⟨hbA, hbcomp⟩ := hbQ
    obtain ⟨hpA, hpcomp⟩ := hpP
    have hbp : b = p := by
      -- Exactness of the ambient tiling makes the centre in a representation unique.
      have hxE : f + b ∈ E := by
        have hcount :=
          (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp
            hTile (f + b)
        by_contra hnot
        have hzero : (F.filter fun q ↦ f + b - q ∈ A).card = 0 := by
          simpa [hnot] using hcount
        have hmem : f ∈ F.filter fun q ↦ f + b - q ∈ A := by
          simp only [Finset.mem_filter, hf, true_and]
          simpa only [add_sub_cancel_left] using hbA
        rw [Finset.card_eq_zero.mp hzero] at hmem
        simp at hmem
      have hcount :=
        (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp
          hTile (f + b)
      have hcard : (F.filter fun q ↦ f + b - q ∈ A).card = 1 := by
        simpa [hxE] using hcount
      obtain ⟨q, hfilter⟩ := Finset.card_eq_one.mp hcard
      have hfmem : f ∈ F.filter fun q ↦ f + b - q ∈ A := by
        simp only [Finset.mem_filter, hf, true_and]
        simpa only [add_sub_cancel_left] using hbA
      have hgmem : g ∈ F.filter fun q ↦ f + b - q ∈ A := by
        refine Finset.mem_filter.mpr ⟨hg, ?_⟩
        rw [hgp]
        simpa only [add_sub_cancel_left] using hpA
      have hfq : f = q := by simpa [hfilter] using hfmem
      have hgq : g = q := by simpa [hfilter] using hgmem
      have hfg : f = g := hfq.trans hgq.symm
      rw [hfg] at hgp
      exact add_left_cancel hgp
    exact ⟨hbp ▸ ⟨hpA, hpcomp⟩, hbFibre⟩
  · rintro b ⟨hbP, hbFibre⟩
    refine ⟨?_, hbFibre⟩
    apply Set.mem_iUnion.mpr
    refine ⟨P, ?_⟩
    rw [hVerticalOnly]
    exact hbP

theorem noncolumnPlate_has_nonfullFibre
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (hTile : TranslationalTilings.Tiles F A E)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hNoncolumn : ¬ IsDiscreteVerticalColumn P)
    {c : ℤ}
    (hc : (Tiling.RationalPolygonal.quakePlateTranslations P ∩
      verticalDiscreteFibre c).Nonempty) :
    ∃ z : TranslationalTilings.Plane, ∃ s : ℤ,
      s ≠ 0 ∧
      z ∈ Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P ∩
          verticalDiscreteFibre c) ∧
      z + s • verticalDiscreteUnit ∉
        Tiling.RationalPolygonal.discreteCarrier F
          (Tiling.RationalPolygonal.quakePlateTranslations P ∩
            verticalDiscreteFibre c) := by
  classical
  let Q := Tiling.RationalPolygonal.quakePlateTranslations P ∩ verticalDiscreteFibre c
  have hnotperiod : ¬ Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.discreteCarrier F Q) verticalDiscreteUnit := by
    intro hperiod
    have hQeq := verticalPlate_minimal hF hTile hEVertical P
      (show Q ⊆ Tiling.RationalPolygonal.quakePlateTranslations P from fun _ h ↦ h.1)
      hc hperiod
    apply hNoncolumn
    refine ⟨c, Set.Subset.antisymm ?_ ?_⟩
    · rintro y ⟨a, haP, rfl⟩
      have haQ : a ∈ Q := hQeq.symm ▸ haP
      have hac : firstDiscreteCoordinate a = c :=
        (mem_verticalDiscreteFibre_iff a c).mp haQ.2
      simp only [Set.mem_singleton_iff]
      exact hac
    · intro y hy
      have hyc : y = c := by simpa only [Set.mem_singleton_iff] using hy
      subst y
      obtain ⟨a, haP, haFibre⟩ := hc
      exact ⟨a, haP, (mem_verticalDiscreteFibre_iff a c).mp haFibre⟩
  unfold Tiling.RationalPolygonal.DiscretePeriodicBy at hnotperiod
  push Not at hnotperiod
  obtain ⟨z, hz⟩ := hnotperiod
  rcases hz with ⟨hshift, hbase⟩ | ⟨hshift, hbase⟩
  · refine ⟨z + verticalDiscreteUnit, -1, by norm_num, ?_, ?_⟩
    · simpa only [Q] using hshift
    have : z + verticalDiscreteUnit + (-1 : ℤ) • verticalDiscreteUnit = z := by
      funext i
      fin_cases i
      · change z 0 + 0 + (-1) * 0 = z 0
        ring
      · change z 1 + 1 + (-1) * 1 = z 1
        ring
    rw [this]
    simpa only [Q] using hbase
  · refine ⟨z, 1, one_ne_zero, ?_, ?_⟩
    · simpa only [Q] using hbase
    · simpa only [one_smul, Q] using hshift

private noncomputable def separatorShift
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (P0 : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (s : ℤ) :
    Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit → ℤ := by
  classical
  exact fun P => if P = P0 then s else 0

private theorem scalarPeriodic_of_dvd {p q : ℕ} {S : Set TranslationalTilings.Plane}
    (hpq : p ∣ q) (hS : TranslationalTilings.SetScalarPeriodic p S) :
    TranslationalTilings.SetScalarPeriodic q S := by
  obtain ⟨m, rfl⟩ := hpq
  intro x z
  simpa only [Nat.cast_mul, mul_smul] using hS x ((m : ℤ) • z)

private theorem scalarPeriodic_iUnion {ι : Type*} {q : ℕ}
    {S : ι → Set TranslationalTilings.Plane}
    (h : ∀ i, TranslationalTilings.SetScalarPeriodic q (S i)) :
    TranslationalTilings.SetScalarPeriodic q (⋃ i, S i) := by
  intro x z
  simp only [Set.mem_iUnion]
  constructor <;> rintro ⟨i, hi⟩
  · exact ⟨i, (h i x z).mp hi⟩
  · exact ⟨i, (h i x z).mpr hi⟩

private theorem scalarPeriodic_sdiff {q : ℕ} {S T : Set TranslationalTilings.Plane}
    (hS : TranslationalTilings.SetScalarPeriodic q S)
    (hT : TranslationalTilings.SetScalarPeriodic q T) :
    TranslationalTilings.SetScalarPeriodic q (S \ T) := by
  intro x z
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨(hS x z).mp hs, fun h => ht ((hT x z).mpr h)⟩
  · rintro ⟨hs, ht⟩
    exact ⟨(hS x z).mpr hs, fun h => ht ((hT x z).mp h)⟩

private theorem discreteCarrier_eq_target {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} (hTile : TranslationalTilings.Tiles F A E) :
    Tiling.RationalPolygonal.discreteCarrier F A = E := by
  classical
  ext x
  constructor
  · rintro ⟨f, hf, a, ha, rfl⟩
    by_contra hn
    have hc := (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp
      hTile (f + a)
    have hz : (F.filter fun q => f + a - q ∈ A).card = 0 := by simpa [hn] using hc
    have hm : f ∈ F.filter fun q => f + a - q ∈ A := by
      simp only [Finset.mem_filter, hf, true_and]
      simpa only [add_sub_cancel_left] using ha
    rw [Finset.card_eq_zero.mp hz] at hm
    simp at hm
  · intro hx
    have hc := (TranslationalTilings.tilesAtLevel_iff_representation_count F A E 1).mp hTile x
    have ho : (F.filter fun f => x - f ∈ A).card = 1 := by simpa [hx] using hc
    obtain ⟨f, hf⟩ := Finset.card_pos.mp (by omega : 0 < (F.filter fun f => x - f ∈ A).card)
    exact ⟨f, (Finset.mem_filter.mp hf).1, x - f, (Finset.mem_filter.mp hf).2, by abel⟩

private theorem columnCentres_complement {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} :
    discreteColumnUnion F A = A \ ⋃ P : {P : Tiling.RationalPolygonal.QuakePlate
        F A verticalDiscreteUnit // ¬ IsDiscreteVerticalColumn P},
      Tiling.RationalPolygonal.quakePlateTranslations P.1 := by
  classical
  ext a
  constructor
  · intro h
    change a ∈ ⋃ (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit),
      ⋃ (_ : IsDiscreteVerticalColumn P),
        Tiling.RationalPolygonal.quakePlateTranslations P at h
    obtain ⟨P, h⟩ := Set.mem_iUnion.mp h
    obtain ⟨hcol, ha⟩ := Set.mem_iUnion.mp h
    refine ⟨(iUnion_verticalPlateCentres F A).symm ▸ Set.mem_iUnion.mpr ⟨P, ha⟩, ?_⟩
    intro hn
    obtain ⟨Q, haQ⟩ := Set.mem_iUnion.mp hn
    exact Q.2 (by
      have : Q.1 = P := haQ.2.symm.trans ha.2
      simpa [this] using hcol)
  · rintro ⟨haA, hn⟩
    rw [← iUnion_verticalPlateCentres F A] at haA
    obtain ⟨P, haP⟩ := Set.mem_iUnion.mp haA
    have hcol : IsDiscreteVerticalColumn P := by
      by_contra hp
      exact hn (Set.mem_iUnion.mpr ⟨⟨P, hp⟩, haP⟩)
    exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hcol, haP⟩⟩

private theorem shiftedVerticalLayer_fibre_isolated
    {F : Finset TranslationalTilings.Plane} {A E : Set TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (hTile : TranslationalTilings.Tiles F A E)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (shift : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit → ℤ)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hVerticalOnly : orderedPlateLayer D order P ⟨0, D.number_pos⟩ =
      Tiling.RationalPolygonal.quakePlateTranslations P)
    {c : ℤ} (hc : (Tiling.RationalPolygonal.quakePlateTranslations P ∩
      verticalDiscreteFibre c).Nonempty) :
    shiftedDirectionalLayerCentres D order shift ⟨0, D.number_pos⟩ ∩
        verticalDiscreteFibre c =
      TranslationalTilings.translateSet ((shift P) • verticalDiscreteUnit)
        (Tiling.RationalPolygonal.quakePlateTranslations P ∩ verticalDiscreteFibre c) := by
  classical
  have hiso := verticalLayer_fibre_isolated hF hEVertical hTile D order P hVerticalOnly hc
  ext x
  constructor
  · rintro ⟨hx, hxf⟩
    obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hx
    let b := x - (shift Q) • verticalDiscreteUnit
    have hbLayer : b ∈ orderedPlateLayer D order Q ⟨0, D.number_pos⟩ := hxQ
    have hbf : b ∈ verticalDiscreteFibre c := by
      rw [mem_verticalDiscreteFibre_iff] at hxf ⊢
      change (x - (shift Q) • verticalDiscreteUnit) 0 = c
      change x 0 = c at hxf
      simpa [verticalDiscreteUnit] using hxf
    have hbGlobal : b ∈ directionalLayerCentres D order ⟨0, D.number_pos⟩ :=
      Set.mem_iUnion.mpr ⟨Q, hbLayer⟩
    have hbP := (Set.ext_iff.mp hiso b).mp ⟨hbGlobal, hbf⟩
    have hbQ : b ∈ Tiling.RationalPolygonal.quakePlateTranslations Q := by
      rw [← D.iUnion_parts Q]
      exact Set.mem_iUnion.mpr ⟨order ⟨0, D.number_pos⟩, hbLayer⟩
    have hQP : Q = P := by
      exact hbQ.2.symm.trans hbP.1.2
    subst Q
    change x ∈ TranslationalTilings.translateSet _ _
    unfold TranslationalTilings.translateSet
    exact ⟨hbP.1, hbf⟩
  · intro hx
    have hx' : x - (shift P) • verticalDiscreteUnit ∈
        Tiling.RationalPolygonal.quakePlateTranslations P ∩ verticalDiscreteFibre c := hx
    refine ⟨Set.mem_iUnion.mpr ⟨P, ?_⟩, ?_⟩
    · change x - (shift P) • verticalDiscreteUnit ∈ orderedPlateLayer D order P _
      rw [hVerticalOnly]
      exact hx'.1
    · rw [mem_verticalDiscreteFibre_iff]
      have hf := (mem_verticalDiscreteFibre_iff
        (x - (shift P) • verticalDiscreteUnit) c).mp hx'.2
      change x 0 = c
      change (x - (shift P) • verticalDiscreteUnit) 0 = c at hf
      simpa [verticalDiscreteUnit] using hf

private theorem separator_marker_at_base_fibre
    {F : Finset TranslationalTilings.Plane} {A E : Set TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (hTile : TranslationalTilings.Tiles F A E)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (hVerticalOnly : orderedPlateLayer D order P ⟨0, D.number_pos⟩ =
      Tiling.RationalPolygonal.quakePlateTranslations P)
    {c s : ℤ} {z : TranslationalTilings.Plane} (_hs : s ≠ 0)
    (hzmem : z ∈ Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P ∩ verticalDiscreteFibre c))
    (hznot : z + s • verticalDiscreteUnit ∉
      Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P ∩ verticalDiscreteFibre c)) :
    z + s • verticalDiscreteUnit ∈ Tiling.RationalPolygonal.discreteCarrier F
        (shiftedDirectionalLayerCentres D order (separatorShift P s)
          ⟨0, D.number_pos⟩ ∩ verticalDiscreteFibre c) ∧
      z + s • verticalDiscreteUnit ∉ Tiling.RationalPolygonal.discreteCarrier F
        (directionalLayerCentres D order ⟨0, D.number_pos⟩ ∩ verticalDiscreteFibre c) := by
  classical
  obtain ⟨f₀, hf₀, a₀, ha₀, hza₀⟩ := hzmem
  have hc : (Tiling.RationalPolygonal.quakePlateTranslations P ∩
      verticalDiscreteFibre c).Nonempty := ⟨a₀, ha₀⟩
  constructor
  · rw [shiftedVerticalLayer_fibre_isolated hF hEVertical hTile D order
      (separatorShift P s) P hVerticalOnly hc]
    refine ⟨f₀, hf₀, a₀ + s • verticalDiscreteUnit, ?_, ?_⟩
    · change (a₀ + s • verticalDiscreteUnit) -
        (separatorShift P s P) • verticalDiscreteUnit ∈
          Tiling.RationalPolygonal.quakePlateTranslations P ∩ verticalDiscreteFibre c
      rw [show separatorShift P s P = s by simp [separatorShift]]
      simpa only [add_sub_cancel_right] using ha₀
    · rw [hza₀]
      abel
  · rw [verticalLayer_fibre_isolated hF hEVertical hTile D order P hVerticalOnly
      hc]
    exact hznot

private theorem separator_marker_transport
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane}
    {K L : ℕ}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    {c s : ℤ} {z : TranslationalTilings.Plane}
    (hKL : K ∣ L)
    (hTransport : ∀ (shift : Tiling.RationalPolygonal.QuakePlate F A
        verticalDiscreteUnit → ℤ) (x d : ℤ),
      TranslationalTilings.translateSet ((d * (K : ℤ)) • horizontalDiscreteUnit)
          (Tiling.RationalPolygonal.discreteCarrier F
            (shiftedDirectionalLayerCentres D order shift ⟨0, D.number_pos⟩ ∩
              verticalDiscreteFibre x)) =
        Tiling.RationalPolygonal.discreteCarrier F
          (shiftedDirectionalLayerCentres D order shift ⟨0, D.number_pos⟩ ∩
            verticalDiscreteFibre (x + d * (K : ℤ))))
    (hbase : z + s • verticalDiscreteUnit ∈
        Tiling.RationalPolygonal.discreteCarrier F
          (shiftedDirectionalLayerCentres D order (separatorShift P s)
            ⟨0, D.number_pos⟩ ∩ verticalDiscreteFibre c) ∧
      z + s • verticalDiscreteUnit ∉
        Tiling.RationalPolygonal.discreteCarrier F
          (directionalLayerCentres D order ⟨0, D.number_pos⟩ ∩ verticalDiscreteFibre c)) :
    ∀ d : ℤ,
      z + s • verticalDiscreteUnit + (d * (L : ℤ)) • horizontalDiscreteUnit ∈
          Tiling.RationalPolygonal.discreteCarrier F
            (shiftedDirectionalLayerCentres D order (separatorShift P s)
              ⟨0, D.number_pos⟩ ∩ verticalDiscreteFibre (c + d * (L : ℤ))) ∧
        z + s • verticalDiscreteUnit + (d * (L : ℤ)) • horizontalDiscreteUnit ∉
          Tiling.RationalPolygonal.discreteCarrier F
            (directionalLayerCentres D order ⟨0, D.number_pos⟩ ∩
              verticalDiscreteFibre (c + d * (L : ℤ))) := by
  obtain ⟨t, rfl⟩ := hKL
  intro d
  have hs := hTransport (separatorShift P s) c (d * (t : ℤ))
  have hz := hTransport (fun _ => 0) c (d * (t : ℤ))
  have hzero (x : ℤ) :
      shiftedDirectionalLayerCentres D order (fun _ => 0) ⟨0, D.number_pos⟩ ∩
          verticalDiscreteFibre x =
        directionalLayerCentres D order ⟨0, D.number_pos⟩ ∩
          verticalDiscreteFibre x := by
    congr 1
    ext a
    simp [shiftedDirectionalLayerCentres, shiftedPlateLayer,
      directionalLayerCentres, TranslationalTilings.translateSet]
  constructor
  · have hleft : z + s • verticalDiscreteUnit +
        ((d * (t : ℤ)) * (K : ℤ)) • horizontalDiscreteUnit ∈
        TranslationalTilings.translateSet
          (((d * (t : ℤ)) * (K : ℤ)) • horizontalDiscreteUnit)
          (Tiling.RationalPolygonal.discreteCarrier F
            (shiftedDirectionalLayerCentres D order (separatorShift P s)
              ⟨0, D.number_pos⟩ ∩ verticalDiscreteFibre c)) := by
      change (z + s • verticalDiscreteUnit +
        ((d * (t : ℤ)) * (K : ℤ)) • horizontalDiscreteUnit) -
          ((d * (t : ℤ)) * (K : ℤ)) • horizontalDiscreteUnit ∈
        Tiling.RationalPolygonal.discreteCarrier F _
      simpa only [add_sub_cancel_right] using hbase.1
    have hout := (Set.ext_iff.mp hs _).mp hleft
    simpa only [Nat.cast_mul, mul_assoc, mul_comm,
      mul_left_comm] using hout
  · intro hm
    rw [← hzero (c + d * ((K * t : ℕ) : ℤ))] at hm
    have hm' : z + s • verticalDiscreteUnit +
        ((d * (t : ℤ)) * (K : ℤ)) • horizontalDiscreteUnit ∈
        Tiling.RationalPolygonal.discreteCarrier F
          (shiftedDirectionalLayerCentres D order (fun _ => 0) ⟨0, D.number_pos⟩ ∩
            verticalDiscreteFibre (c + (d * (t : ℤ)) * (K : ℤ))) := by
      simpa only [Nat.cast_mul, mul_assoc, mul_comm,
        mul_left_comm] using hm
    have hin := (Set.ext_iff.mp hz _).mpr hm'
    apply hbase.2
    change (z + s • verticalDiscreteUnit +
      ((d * (t : ℤ)) * (K : ℤ)) • horizontalDiscreteUnit) -
        ((d * (t : ℤ)) * (K : ℤ)) • horizontalDiscreteUnit ∈
      Tiling.RationalPolygonal.discreteCarrier F
        (shiftedDirectionalLayerCentres D order (fun _ => 0) ⟨0, D.number_pos⟩ ∩
          verticalDiscreteFibre c) at hin
    rw [hzero c] at hin
    simpa only [add_sub_cancel_right] using hin

private theorem separator_transport_forces_plate_fibre
    {F : Finset TranslationalTilings.Plane} {A E : Set TranslationalTilings.Plane}
    {L : ℕ} (_hTile : TranslationalTilings.Tiles F A E)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    {c s : ℤ} {z : TranslationalTilings.Plane}
    (hstatuses : ∀ d : ℤ,
      z + s • verticalDiscreteUnit + (d * (L : ℤ)) • horizontalDiscreteUnit ∈
          Tiling.RationalPolygonal.discreteCarrier F
            (shiftedDirectionalLayerCentres D order (separatorShift P s)
              ⟨0, D.number_pos⟩ ∩ verticalDiscreteFibre (c + d * (L : ℤ))) ∧
      z + s • verticalDiscreteUnit + (d * (L : ℤ)) • horizontalDiscreteUnit ∉
          Tiling.RationalPolygonal.discreteCarrier F
            (directionalLayerCentres D order ⟨0, D.number_pos⟩ ∩
              verticalDiscreteFibre (c + d * (L : ℤ)))) :
    ∀ d : ℤ, (Tiling.RationalPolygonal.quakePlateTranslations P ∩
      verticalDiscreteFibre (c + d * (L : ℤ))).Nonempty := by
  classical
  intro d
  obtain ⟨f, hf, b, hb, hrep⟩ := (hstatuses d).1
  obtain ⟨Q, hbQ⟩ := Set.mem_iUnion.mp hb.1
  have haQ : b - (separatorShift P s Q) • verticalDiscreteUnit ∈
      Tiling.RationalPolygonal.quakePlateTranslations Q := by
    rw [← D.iUnion_parts Q]
    apply Set.mem_iUnion.mpr
    refine ⟨order ⟨0, D.number_pos⟩, ?_⟩
    exact hbQ
  have hQP : Q = P := by
    by_contra hne
    have hshift0 : separatorShift P s Q = 0 := by
      simp [separatorShift, hne]
    apply (hstatuses d).2
    refine ⟨f, hf, b, ⟨?_, hb.2⟩, hrep⟩
    apply Set.mem_iUnion.mpr
    refine ⟨Q, ?_⟩
    simpa [shiftedPlateLayer, TranslationalTilings.translateSet, hshift0] using hbQ
  subst Q
  have hshift : separatorShift P s P = s := by
    simp [separatorShift]
  rw [hshift] at haQ
  refine ⟨b - s • verticalDiscreteUnit, haQ, ?_⟩
  rw [mem_verticalDiscreteFibre_iff]
  have hbf := (mem_verticalDiscreteFibre_iff b (c + d * (L : ℤ))).mp hb.2
  change (b - s • verticalDiscreteUnit) 0 = _
  change b 0 = _ at hbf
  simpa [verticalDiscreteUnit] using hbf

private theorem plateCarrier_periodic_of_horizontalProjection
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {L : ℕ}
    (hF : F.Nonempty) (hTile : TranslationalTilings.Tiles F A E)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy
      E verticalDiscreteUnit)
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit)
    (_hL : 0 < L)
    (hHorizontal : ∀ x : ℤ,
      x ∈ firstDiscreteCoordinate ''
          Tiling.RationalPolygonal.quakePlateTranslations P ↔
        x + (L : ℤ) ∈ firstDiscreteCoordinate ''
          Tiling.RationalPolygonal.quakePlateTranslations P) :
    TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier F
        (Tiling.RationalPolygonal.quakePlateTranslations P)) := by
  rw [verticalPlateCarrier_eq_projectionProduct hF hTile hEVertical P]
  let B := firstDiscreteCoordinate ''
    Tiling.RationalPolygonal.quakePlateTranslations P
  have hB : Function.Periodic (fun x : ℤ => x ∈ B) (L : ℤ) := by
    intro x
    apply propext
    exact (hHorizontal x).symm
  have hBz : ∀ (x n : ℤ), x + n * (L : ℤ) ∈ B ↔ x ∈ B := by
    intro x n
    simpa [smul_eq_mul, mul_comm] using hB.zsmul n x
  intro x z
  simp only [mem_verticalDiscreteCylinder_iff]
  change x 0 + (L : ℤ) * z 0 ∈ _ ↔ x 0 ∈ _
  constructor
  · intro hx
    obtain ⟨f, hf, a, ha, hsum⟩ := hx
    refine ⟨f, hf, a - (L : ℤ) * z 0, ?_, ?_⟩
    · exact (hBz (a - (L : ℤ) * z 0) (z 0)).1 (by
        convert ha using 1
        ring)
    · change f + (a - (L : ℤ) * z 0) = x 0
      change f + a = x 0 + (L : ℤ) * z 0 at hsum
      omega
  · intro hx
    obtain ⟨f, hf, a, ha, hsum⟩ := hx
    refine ⟨f, hf, a + (L : ℤ) * z 0, ?_, ?_⟩
    · change _ ∈ B
      convert (hBz a (z 0)).2 ha using 1
      ring
    · change f + (a + (L : ℤ) * z 0) = x 0 + (L : ℤ) * z 0
      change f + a = x 0 at hsum
      omega

/-- One scalar period works for all vertical-only noncolumn plate carriers. -/
theorem verticalOnlyNoncolumnPlate_periodic
    {F : Finset TranslationalTilings.Plane} {A E : Set TranslationalTilings.Plane}
    {ell k : ℕ} (hF : F.Nonempty) (hell : 0 < ell)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (hEPeriodic : TranslationalTilings.SetScalarPeriodic ell E)
    (hTile : TranslationalTilings.Tiles F A E)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts)) (hk : 0 < k)
    (hfirst : D.period (order ⟨0, D.number_pos⟩) =
      (k : ℤ) • verticalDiscreteUnit) :
    ∃ L : ℕ, 0 < L ∧ ell ∣ L ∧ k ∣ L ∧
      ∀ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
        orderedPlateLayer D order P ⟨0, D.number_pos⟩ =
            Tiling.RationalPolygonal.quakePlateTranslations P →
          ¬ IsDiscreteVerticalColumn P →
            TranslationalTilings.SetScalarPeriodic L
              (Tiling.RationalPolygonal.discreteCarrier F
                (Tiling.RationalPolygonal.quakePlateTranslations P)) := by
  classical
  obtain ⟨N, hN, hellN, hGlobal⟩ :=
    exists_commonDirectionalCarrierScalarPeriod hF hell hEVertical hEPeriodic hTile D order
  obtain ⟨M, hM, hNM, hellM, hkM, hPlate, hFirst⟩ :=
    exists_commonNonverticalPlateLayerScalarPeriod hF hell hEVertical hEPeriodic hTile
      D order hk hfirst hN hellN hGlobal
  have hShifted : ∀ shift : Tiling.RationalPolygonal.QuakePlate F A
      verticalDiscreteUnit → ℤ,
      TranslationalTilings.SetScalarPeriodic M
        (Tiling.RationalPolygonal.discreteCarrier F
          (shiftedDirectionalLayerCentres D order shift ⟨0, D.number_pos⟩)) := fun shift =>
    (quakeShift_directionalCarriers_scalarPeriodic hF hell hEVertical hEPeriodic hTile
      D order hk hfirst hM hellM hkM hPlate shift).2
  obtain ⟨K, hKdef, hK, hTransport⟩ := exists_uniformVerticalSliceTransport
    hF hell hEVertical hEPeriodic hTile D order hk hfirst hM hShifted
  let L := Nat.lcm M K
  have hML : M ∣ L := Nat.dvd_lcm_left _ _
  have hKL : K ∣ L := Nat.dvd_lcm_right _ _
  refine ⟨L, Nat.lcm_pos hM hK, hellM.trans hML, hkM.trans hML, ?_⟩
  intro P hVerticalOnly hNoncolumn
  apply plateCarrier_periodic_of_horizontalProjection hF hTile hEVertical P
    (Nat.lcm_pos hM hK)
  intro x
  constructor
  · rintro ⟨a, haP, rfl⟩
    have hc : (Tiling.RationalPolygonal.quakePlateTranslations P ∩
        verticalDiscreteFibre (firstDiscreteCoordinate a)).Nonempty :=
      ⟨a, haP, (mem_verticalDiscreteFibre_iff _ _).2 rfl⟩
    obtain ⟨z, s, hs, hz, hznot⟩ :=
      noncolumnPlate_has_nonfullFibre hF hEVertical hTile P hNoncolumn hc
    have hbase := separator_marker_at_base_fibre hF hEVertical hTile D order P
      hVerticalOnly hs hz hznot
    have hstatuses := separator_marker_transport D order P hKL hTransport hbase
    obtain ⟨b, hbP, hbf⟩ := separator_transport_forces_plate_fibre hTile D order P
      hstatuses 1
    refine ⟨b, hbP, ?_⟩
    have := (mem_verticalDiscreteFibre_iff b
      (firstDiscreteCoordinate a + (1 : ℤ) * (L : ℤ))).mp hbf
    simpa using this
  · rintro ⟨b, hbP, hb⟩
    have hc : (Tiling.RationalPolygonal.quakePlateTranslations P ∩
        verticalDiscreteFibre (firstDiscreteCoordinate b)).Nonempty :=
      ⟨b, hbP, (mem_verticalDiscreteFibre_iff _ _).2 rfl⟩
    obtain ⟨z, s, hs, hz, hznot⟩ :=
      noncolumnPlate_has_nonfullFibre hF hEVertical hTile P hNoncolumn hc
    have hbase := separator_marker_at_base_fibre hF hEVertical hTile D order P
      hVerticalOnly hs hz hznot
    have hstatuses := separator_marker_transport D order P hKL hTransport hbase
    obtain ⟨a, haP, haf⟩ := separator_transport_forces_plate_fibre hTile D order P
      hstatuses (-1)
    refine ⟨a, haP, ?_⟩
    have ha := (mem_verticalDiscreteFibre_iff a
      (firstDiscreteCoordinate b + (-1 : ℤ) * (L : ℤ))).mp haf
    omega

private theorem columnCarrier_complement
    {F : Finset TranslationalTilings.Plane} {A E : Set TranslationalTilings.Plane}
    (hTile : TranslationalTilings.Tiles F A E) :
    Tiling.RationalPolygonal.discreteCarrier F (discreteColumnUnion F A) =
      E \ ⋃ P : {P : Tiling.RationalPolygonal.QuakePlate F A
          verticalDiscreteUnit // ¬ IsDiscreteVerticalColumn P},
        Tiling.RationalPolygonal.discreteCarrier F
          (Tiling.RationalPolygonal.quakePlateTranslations P.1) := by
  rw [columnCentres_complement]
  rw [discreteCarrier_sdiff hTile]
  · rw [discreteCarrier_eq_target hTile, discreteCarrier_iUnion]
  · exact Set.Subset.rfl
  · intro a ha
    rw [← iUnion_verticalPlateCentres F A]
    obtain ⟨P, haP⟩ := Set.mem_iUnion.mp ha
    exact Set.mem_iUnion.mpr ⟨P.1, haP⟩

/-- Noncolumn carriers and the aggregate column carrier share a uniform scalar period. -/
theorem exists_discretePlatePeriodicity
    {F : Finset TranslationalTilings.Plane} {A E : Set TranslationalTilings.Plane}
    {ell : ℕ} (hF : F.Nonempty) (hell : 0 < ell)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy E verticalDiscreteUnit)
    (hEPeriodic : TranslationalTilings.SetScalarPeriodic ell E)
    (hTile : TranslationalTilings.Tiles F A E) :
    ∃ L : ℕ, 0 < L ∧ ell ∣ L ∧
      (∀ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
        ¬ IsDiscreteVerticalColumn P → TranslationalTilings.SetScalarPeriodic L
          (Tiling.RationalPolygonal.discreteCarrier F
            (Tiling.RationalPolygonal.quakePlateTranslations P))) ∧
      TranslationalTilings.SetScalarPeriodic L
        (Tiling.RationalPolygonal.discreteCarrier F (discreteColumnUnion F A)) := by
  classical
  obtain ⟨D, order, k, hk, hfirst⟩ :=
    exists_verticalPlateDirectionalDecomposition hF hell hEVertical hEPeriodic hTile
  obtain ⟨L5, hL5, hell5, hk5, hfive⟩ :=
    nonverticalLayer_plateCarrier_scalarPeriodic hF hell hEVertical hEPeriodic hTile
      D order hk hfirst
  obtain ⟨L1, hL1, hell1, hk1, hone⟩ :=
    verticalOnlyNoncolumnPlate_periodic hF hell hEVertical hEPeriodic hTile D order hk hfirst
  let L := Nat.lcm L5 L1
  have h5L : L5 ∣ L := Nat.dvd_lcm_left _ _
  have h1L : L1 ∣ L := Nat.dvd_lcm_right _ _
  have hnon : ∀ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
      ¬ IsDiscreteVerticalColumn P → TranslationalTilings.SetScalarPeriodic L
        (Tiling.RationalPolygonal.discreteCarrier F
          (Tiling.RationalPolygonal.quakePlateTranslations P)) := by
    intro P hncol
    by_cases hq : ∃ j : Fin D.numberOfParts,
        j ≠ ⟨0, D.number_pos⟩ ∧ (orderedPlateLayer D order P j).Nonempty
    · exact scalarPeriodic_of_dvd h5L (hfive P hq)
    · apply scalarPeriodic_of_dvd h1L
      apply hone P
      · apply Set.Subset.antisymm
        · intro a ha
          rw [← D.iUnion_parts P]
          exact Set.mem_iUnion.mpr ⟨order ⟨0, D.number_pos⟩, ha⟩
        · intro a ha
          rw [← D.iUnion_parts P] at ha
          obtain ⟨i, hai⟩ := Set.mem_iUnion.mp ha
          let j := order.symm i
          have haj : a ∈ orderedPlateLayer D order P j := by
            change a ∈ D.part P (order j)
            simpa [j] using hai
          have hj : j = ⟨0, D.number_pos⟩ := by
            by_contra hj
            exact hq ⟨j, hj, ⟨a, haj⟩⟩
          simpa [hj] using haj
      · exact hncol
  refine ⟨L, Nat.lcm_pos hL5 hL1, hell5.trans h5L, hnon, ?_⟩
  rw [columnCarrier_complement hTile]
  apply scalarPeriodic_sdiff (scalarPeriodic_of_dvd (hell5.trans h5L) hEPeriodic)
  exact scalarPeriodic_iUnion (fun P => hnon P.1 P.2)

end Tiling.AxisParallel.Discrete
