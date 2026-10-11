/-
Copyright (c) 2026 The Tiling Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tiling Authors
-/
import Tiling.AxisParallel.Terminal.AssemblyCore
import Tiling.AxisParallel.Foundations.LatticeOrbitRepresentatives
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Area identities for doubly periodic tilings

This file chooses finite centre-orbit representatives for a triangular period lattice,
unfolds the tile multiplicity over a fundamental domain, and compares it with the area
of a periodic vertical slab. The resulting identities also give commensurability of the
vertical periods in a mixed rationalization datum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped ENNReal Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Terminal

/-- The explicit half-open parallelogram spanned by the triangular period generators. -/
def triangularFundamentalDomain (alpha beta shear : ℝ) : Set Tiling.Plane :=
  {z | ∃ u ∈ Set.Ico (0 : ℝ) 1, ∃ v ∈ Set.Ico (0 : ℝ) 1,
    z = Complex.mk (beta * u) (shear * u + alpha * v)}

/-- The locally finite periodization of the tile indicator over chosen centre-orbit
representatives and the triangular subgroup. -/
def periodizedTileMultiplicity
    (K : Region) (R : Finset Tiling.Plane) (alpha beta shear : ℝ)
    (x : Tiling.Plane) : ℝ :=
  ∑' r : ↥R, ∑' l : ↥(triangularPeriodSubgroup alpha beta shear),
    Set.indicator ((l.1 + r.1) +ᵥ K.openCarrier) (fun _ => (1 : ℝ)) x

private noncomputable def triangularLattice
    (alpha beta shear : ℝ) (hα : 0 < alpha) (hβ : 0 < beta) :
    Tiling.AxisParallel.PlanarLattice where
  basis := ![verticalPeriodVector alpha, skewPeriodVector beta shear]
  independent := by
    rw [LinearIndependent.pair_iffₛ]
    intro s t s' t' h
    have hre := congrArg Complex.re h
    have ht : t = t' := by
      norm_num [verticalPeriodVector, skewPeriodVector] at hre
      exact hre.resolve_right hβ.ne'
    subst t'
    have him := congrArg Complex.im h
    have hs : s = s' := by
      norm_num [verticalPeriodVector, skewPeriodVector] at him
      exact him.resolve_right hα.ne'
    exact ⟨hs, rfl⟩

private theorem triangularLattice_subgroup
    (alpha beta shear : ℝ) (hα : 0 < alpha) (hβ : 0 < beta) :
    (triangularLattice alpha beta shear hα hβ).toAddSubgroup =
      triangularPeriodSubgroup alpha beta shear := by
  apply le_antisymm
  · rw [PlanarLattice.toAddSubgroup, Tiling.Polygonal.PlanarLattice.toAddSubgroup,
      AddSubgroup.closure_le]
    rintro x ⟨i, rfl⟩
    change ![verticalPeriodVector alpha, skewPeriodVector beta shear] i ∈
      triangularPeriodSubgroup alpha beta shear
    fin_cases i
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · rintro x ⟨m, n, rfl⟩
    apply add_mem
    · apply AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) m
      exact ⟨0, by simp [triangularLattice]⟩
    · apply AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) n
      exact ⟨1, by simp [triangularLattice]⟩

private theorem triangular_subgroup_le_periodGroup
    {S : Set Tiling.Plane} {alpha beta shear : ℝ}
    (hvertical : verticalPeriodVector alpha ∈ periodGroup S)
    (hskew : skewPeriodVector beta shear ∈ periodGroup S) :
    triangularPeriodSubgroup alpha beta shear ≤ periodGroup S := by
  rintro x ⟨m, n, rfl⟩
  exact add_mem ((periodGroup S).zsmul_mem hvertical m)
    ((periodGroup S).zsmul_mem hskew n)

theorem exists_finiteOrbitRepresentatives :
    ∀ {K : Region} {S D : Set Tiling.Plane} {alpha beta shear : ℝ},
      0 < alpha → 0 < beta → TilesOn K S D →
      verticalPeriodVector alpha ∈ periodGroup S →
      skewPeriodVector beta shear ∈ periodGroup S →
      ∃ R : Finset Tiling.Plane,
        (R : Set Tiling.Plane) ⊆ S ∧
        QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear) ''
            (R : Set Tiling.Plane) =
          QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear) '' S ∧
        Set.InjOn
          (QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear))
          (R : Set Tiling.Plane) := by
  intro K S D alpha beta shear hα hβ hTile hvertical hskew
  let L := triangularLattice alpha beta shear hα hβ
  have hLF := (IsPacking.locallyFinite_centres hTile.2.1).1
  have hlocal : ∀ Q, Bornology.IsBounded Q → (S ∩ Q).Finite := by
    intro Q hQ
    exact hLF Q hQ
  have hLH : L.toAddSubgroup = triangularPeriodSubgroup alpha beta shear :=
    triangularLattice_subgroup alpha beta shear hα hβ
  have hperiod : L.toAddSubgroup ≤ periodGroup S := by
    rw [hLH]
    exact triangular_subgroup_le_periodGroup hvertical hskew
  obtain ⟨R, hsub, hsurj, hinj⟩ :=
    Tiling.AxisParallel.exists_finiteOrbitRepresentatives_of_planarLattice
      L hlocal hperiod
  refine ⟨R, hsub, ?_, ?_⟩
  · rw [← hLH]
    exact hsurj
  · rw [← hLH]
    exact hinj

private noncomputable def orbitCentreEquiv
    {S : Set Tiling.Plane} {alpha beta shear : ℝ} (R : Finset Tiling.Plane)
    (hvertical : verticalPeriodVector alpha ∈ periodGroup S)
    (hskew : skewPeriodVector beta shear ∈ periodGroup S)
    (hRS : (R : Set Tiling.Plane) ⊆ S)
    (hQ : QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear) ''
        (R : Set Tiling.Plane) =
      QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear) '' S)
    (hinj : Set.InjOn
      (QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear))
      (R : Set Tiling.Plane)) :
    (↑R × ↑(triangularPeriodSubgroup alpha beta shear)) ≃ ↑S := by
  let H := triangularPeriodSubgroup alpha beta shear
  have hHS : H ≤ periodGroup S :=
    triangular_subgroup_le_periodGroup hvertical hskew
  let f : (↑R × ↑H) → ↑S := fun p ↦ ⟨p.2.1 + p.1.1, by
    have hp : p.2.1 +ᵥ S = S :=
      (periodGroup_isAddSubgroup S p.2.1).mp (hHS p.2.2)
    have hm : p.2.1 + p.1.1 ∈ p.2.1 +ᵥ S := ⟨p.1.1, hRS p.1.2, rfl⟩
    rwa [hp] at hm⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨r, l⟩ ⟨r', l'⟩ heq
    have hc : l.1 + r.1 = l'.1 + r'.1 := congrArg Subtype.val heq
    have hqr : QuotientAddGroup.mk' H r.1 = QuotientAddGroup.mk' H r'.1 := by
      apply (QuotientAddGroup.mk'_eq_mk' H).2
      refine ⟨l.1 - l'.1, sub_mem l.2 l'.2, ?_⟩
      rw [show r.1 + (l.1 - l'.1) = r'.1 by
        rw [sub_eq_add_neg]
        apply add_right_cancel (b := l'.1)
        simpa [add_assoc, add_comm, add_left_comm] using hc]
    have hrr : r = r' := Subtype.ext (hinj r.2 r'.2 hqr)
    subst r'
    have hll : l = l' := Subtype.ext (add_right_cancel hc)
    exact Prod.ext rfl hll
  · rintro ⟨s, hs⟩
    have hsQ : QuotientAddGroup.mk' H s ∈
        QuotientAddGroup.mk' H '' (R : Set Tiling.Plane) := by
      rw [hQ]
      exact ⟨s, hs, rfl⟩
    obtain ⟨r, hrR, hqr⟩ := hsQ
    obtain ⟨l, hlH, hrl⟩ := (QuotientAddGroup.mk'_eq_mk' H).mp hqr
    refine ⟨⟨⟨r, hrR⟩, ⟨l, hlH⟩⟩, ?_⟩
    apply Subtype.ext
    dsimp [f]
    rw [← hrl]
    abel

private lemma tsum_tsum_indicator_of_subsingleton
    {A B : Type*} (U : A → B → Set Tiling.Plane) (x : Tiling.Plane)
    (hsub : {p : A × B | x ∈ U p.1 p.2}.Subsingleton) :
    (∑' a : A, ∑' b : B, Set.indicator (U a b) (fun _ ↦ (1 : ℝ)) x) =
      Set.indicator {x | ∃ p : A × B, x ∈ U p.1 p.2} (fun _ ↦ (1 : ℝ)) x := by
  classical
  by_cases hex : ∃ p : A × B, x ∈ U p.1 p.2
  · obtain ⟨⟨a, b⟩, hab⟩ := hex
    have hinner : ∀ a' : A,
        (∑' b' : B, Set.indicator (U a' b') (fun _ ↦ (1 : ℝ)) x) =
          if a' = a then 1 else 0 := by
      intro a'
      by_cases haa : a' = a
      · subst a'
        rw [if_pos rfl, tsum_eq_single b]
        · simp [hab]
        · intro b' hba
          have hn : x ∉ U a b' := by
            intro hb'
            have he : (a, b') = (a, b) := hsub hb' hab
            exact hba (congrArg Prod.snd he)
          simp [hn]
      · rw [if_neg haa]
        have hz : (fun b' : B ↦
            Set.indicator (U a' b') (fun _ ↦ (1 : ℝ)) x) = fun _ ↦ 0 := by
          funext b'
          have hn : x ∉ U a' b' := by
            intro hb'
            have he : (a', b') = (a, b) := hsub hb' hab
            exact haa (congrArg Prod.fst he)
          simp [hn]
        rw [hz, tsum_zero]
    simp_rw [hinner]
    rw [tsum_ite_eq a]
    rw [Set.indicator_of_mem]
    exact ⟨(a, b), hab⟩
  · have hall : ∀ a b, x ∉ U a b := by
      intro a b hx
      exact hex ⟨(a, b), hx⟩
    have hmem : x ∉ {x | ∃ p : A × B, x ∈ U p.1 p.2} := hex
    simp only [Set.indicator, hmem, if_false]
    simp [hall]

theorem periodizedTileMultiplicity_ae_eq_slabIndicator :
    ∀ {K : Region} {S : Set Tiling.Plane} {X : Set ℝ}
      {alpha beta shear : ℝ} (R : Finset Tiling.Plane),
      0 < alpha → 0 < beta → MeasurableSet X →
      TilesOn K S {z : Tiling.Plane | z.re ∈ X} →
      verticalPeriodVector alpha ∈ periodGroup S →
      skewPeriodVector beta shear ∈ periodGroup S →
      (R : Set Tiling.Plane) ⊆ S →
      QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear) ''
          (R : Set Tiling.Plane) =
        QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear) '' S →
      Set.InjOn
        (QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear))
        (R : Set Tiling.Plane) →
      ∀ᵐ x ∂volume.restrict (triangularFundamentalDomain alpha beta shear),
        periodizedTileMultiplicity K R alpha beta shear x =
          Set.indicator {z : Tiling.Plane | z.re ∈ X}
            (fun _ => (1 : ℝ)) x := by
  intro K S X alpha beta shear R hα hβ hX hTile hvertical hskew hRS hQ hinj
  let H := triangularPeriodSubgroup alpha beta shear
  let e : (↑R × ↑H) ≃ ↑S :=
    orbitCentreEquiv R hvertical hskew hRS hQ hinj
  let U : ↑R → ↑H → Set Tiling.Plane := fun r l ↦
    (l.1 + r.1) +ᵥ K.openCarrier
  have hsingle (x : Tiling.Plane) :
      {p : ↑R × ↑H | x ∈ U p.1 p.2}.Subsingleton := by
    intro p hp q hq
    apply e.injective
    apply Subtype.ext
    by_contra hne
    have hd := (isPacking_iff_openCarrier_disjoint K S).mp hTile.2.1
      (e p).2 (e q).2 hne
    apply Set.disjoint_left.1 hd hp hq
  have hex (x : Tiling.Plane) :
      (∃ p : ↑R × ↑H, x ∈ U p.1 p.2) ↔
        ∃ s : S, x ∈ (s.1 +ᵥ K.openCarrier) := by
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨e p, hp⟩
    · rintro ⟨s, hs⟩
      refine ⟨e.symm s, ?_⟩
      change x ∈ (e (e.symm s)).1 +ᵥ K.openCarrier
      rw [e.apply_symm_apply]
      exact hs
  filter_upwards [ae_restrict_of_ae hTile.2.2] with x hx
  rw [show periodizedTileMultiplicity K R alpha beta shear x =
      ∑' r : ↑R, ∑' l : ↑H,
        Set.indicator (U r l) (fun _ ↦ (1 : ℝ)) x by rfl]
  rw [tsum_tsum_indicator_of_subsingleton U x (hsingle x)]
  by_cases hD : x.re ∈ X
  · have hp : x ∈ {x | ∃ p : ↑R × ↑H, x ∈ U p.1 p.2} :=
      (hex x).2 (hx.mp hD)
    have hD' : x ∈ {z : Tiling.Plane | z.re ∈ X} := hD
    simp only [Set.indicator, hp, hD', if_true]
  · have hn : x ∉ {x | ∃ p : ↑R × ↑H, x ∈ U p.1 p.2} := by
      intro hp
      exact hD (hx.mpr ((hex x).1 hp))
    have hD' : x ∉ {z : Tiling.Plane | z.re ∈ X} := hD
    simp only [Set.indicator, hn, hD', if_false]

private lemma mem_triangularFundamentalDomain_mk_iff
    {alpha beta shear x y : ℝ} (hα : 0 < alpha) (hβ : 0 < beta) :
    Complex.mk x y ∈ triangularFundamentalDomain alpha beta shear ↔
      x ∈ Set.Ico 0 beta ∧
        y ∈ Set.Ico (shear * (x / beta)) (shear * (x / beta) + alpha) := by
  constructor
  · rintro ⟨u, ⟨hu0, hu1⟩, v, ⟨hv0, hv1⟩, heq⟩
    have hx : x = beta * u := congrArg Complex.re heq
    have hy : y = shear * u + alpha * v := congrArg Complex.im heq
    have hu : x / beta = u := by
      rw [hx, mul_div_cancel_left₀ u hβ.ne']
    constructor
    · constructor <;> nlinarith
    · rw [hu, hy]
      constructor <;> nlinarith
  · rintro ⟨⟨hx0, hxβ⟩, hy0, hyα⟩
    let u := x / beta
    let v := (y - shear * u) / alpha
    have hu0 : 0 ≤ u := div_nonneg hx0 hβ.le
    have hu1 : u < 1 := (div_lt_one hβ).2 hxβ
    have hv0 : 0 ≤ v := div_nonneg (by simpa [u] using hy0) hα.le
    have hv1 : v < 1 := by
      rw [div_lt_one hα]
      dsimp only [u]
      linarith
    refine ⟨u, ⟨hu0, hu1⟩, v, ⟨hv0, hv1⟩, ?_⟩
    apply Complex.ext
    · dsimp only [u]
      field_simp
    · change y = shear * u + alpha * v
      dsimp only [v]
      field_simp
      ring

theorem integral_slabIndicator_triangularFundamentalDomain :
    ∀ {X : Set ℝ} {alpha beta shear : ℝ},
      0 < alpha → 0 < beta → MeasurableSet X →
      (beta +ᵥ X) =ᵐ[volume] X →
      ∫ x in triangularFundamentalDomain alpha beta shear,
          Set.indicator {z : Tiling.Plane | z.re ∈ X}
            (fun _ => (1 : ℝ)) x =
        alpha * (volume (X ∩ Set.Ico 0 beta)).toReal := by
  intro X alpha beta shear hα hβ hX _hXperiod
  let C : Set Tiling.Plane := {z | z.re ∈ X}
  let P : Set (ℝ × ℝ) := {p |
    p.1 ∈ X ∩ Set.Ico 0 beta ∧
      p.2 ∈ Set.Ico (shear * (p.1 / beta))
        (shear * (p.1 / beta) + alpha)}
  have hPm : MeasurableSet P := by
    have hx : Measurable fun p : ℝ × ℝ ↦ p.1 := measurable_fst
    have hy : Measurable fun p : ℝ × ℝ ↦ p.2 := measurable_snd
    exact ((hX.inter measurableSet_Ico).preimage hx).inter
      ((measurableSet_le (measurable_const.mul (hx.div_const beta)) hy).inter
        (measurableSet_lt hy
          ((measurable_const.mul (hx.div_const beta)).add measurable_const)))
  have hpre : Complex.measurableEquivRealProd ⁻¹' P =
      C ∩ triangularFundamentalDomain alpha beta shear := by
    ext z
    simp only [mem_preimage, Complex.measurableEquivRealProd_apply, P, C,
      mem_inter_iff, mem_ofPred_eq]
    rw [mem_triangularFundamentalDomain_mk_iff hα hβ]
    tauto
  have hmeasure : volume (C ∩ triangularFundamentalDomain alpha beta shear) =
      volume P := by
    rw [← hpre]
    exact Complex.volume_preserving_equiv_real_prod.measure_preimage
      hPm.nullMeasurableSet
  have hPvolume : volume P = ENNReal.ofReal alpha * volume (X ∩ Set.Ico 0 beta) := by
    change (volume.prod volume) P = _
    rw [Measure.prod_apply hPm]
    have hfiber (x : ℝ) : volume (Prod.mk x ⁻¹' P) =
        Set.indicator (X ∩ Set.Ico 0 beta)
          (fun _ ↦ ENNReal.ofReal alpha) x := by
      by_cases hx : x ∈ X ∩ Set.Ico 0 beta
      · rw [Set.indicator_of_mem hx]
        have heq : Prod.mk x ⁻¹' P =
            Set.Ico (shear * (x / beta)) (shear * (x / beta) + alpha) := by
          ext y
          change (x ∈ X ∩ Set.Ico 0 beta ∧
            y ∈ Set.Ico (shear * (x / beta))
              (shear * (x / beta) + alpha)) ↔ _
          exact and_iff_right hx
        rw [heq, Real.volume_Ico]
        simp
      · simp only [Set.indicator, hx, if_false]
        have heq : Prod.mk x ⁻¹' P = ∅ := by
          ext y
          change (x ∈ X ∩ Set.Ico 0 beta ∧
            y ∈ Set.Ico (shear * (x / beta))
              (shear * (x / beta) + alpha)) ↔ False
          simp [hx]
        simp [heq]
    simp_rw [hfiber]
    rw [lintegral_indicator (hX.inter measurableSet_Ico)]
    simp
  have hCm : MeasurableSet C := hX.preimage Complex.measurable_re
  change ∫ x in triangularFundamentalDomain alpha beta shear,
    C.indicator (fun _ ↦ (1 : ℝ)) x = _
  change ∫ x, C.indicator (fun _ ↦ (1 : ℝ)) x
      ∂volume.restrict (triangularFundamentalDomain alpha beta shear) = _
  rw [integral_indicator hCm, integral_const]
  rw [Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Measure.restrict_apply hCm]
  rw [hmeasure, hPvolume]
  simp [ENNReal.toReal_mul, hα.le]

private lemma triangularFundamentalDomain_eq_zspan
    (alpha beta shear : ℝ) (hα : 0 < alpha) (hβ : 0 < beta) :
    triangularFundamentalDomain alpha beta shear =
      ZSpan.fundamentalDomain
        (triangularLattice alpha beta shear hα hβ).realBasis := by
  let L := triangularLattice alpha beta shear hα hβ
  let b := L.realBasis
  ext z
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [ZSpan.mem_fundamentalDomain]
    intro i
    have heq : Complex.mk (beta * u) (shear * u + alpha * v) =
        v • b 0 + u • b 1 := by
      apply Complex.ext <;>
        simp [b, L, triangularLattice, verticalPeriodVector, skewPeriodVector] <;> ring
    rw [heq]
    change b.repr (v • b 0 + u • b 1) i ∈ Set.Ico (0 : ℝ) 1
    rw [map_add, map_smul, map_smul]
    fin_cases i
    · simpa using hv
    · simpa using hu
  · intro hz
    rw [ZSpan.mem_fundamentalDomain] at hz
    let v := b.repr z 0
    let u := b.repr z 1
    refine ⟨u, hz 1, v, hz 0, ?_⟩
    have hsum := b.sum_repr z
    have heq : z = v • b 0 + u • b 1 := by
      simpa [Fin.sum_univ_two, v, u] using hsum.symm
    rw [heq]
    apply Complex.ext <;>
      simp [b, L, triangularLattice, verticalPeriodVector, skewPeriodVector] <;> ring

private lemma periodization_norm_tsum_ne_top
    {H : AddSubgroup Tiling.Plane} [Countable ↑H] {F T : Set Tiling.Plane}
    (hfd : IsAddFundamentalDomain H F volume) (hTm : MeasurableSet T)
    (hTtop : volume T ≠ ∞) :
    (∑' l : ↑H, ∫⁻ x,
      ‖Set.indicator ((l.1 : Tiling.Plane) +ᵥ T) (fun _ ↦ (1 : ℝ)) x‖ₑ
        ∂volume.restrict F) ≠ ∞ := by
  have hmeasure := hfd.measure_eq_tsum T
  have hterm (l : ↑H) :
      ∫⁻ x, ‖Set.indicator ((l.1 : Tiling.Plane) +ᵥ T)
          (fun _ ↦ (1 : ℝ)) x‖ₑ ∂volume.restrict F =
        volume (((l.1 : Tiling.Plane) +ᵥ T) ∩ F) := by
    rw [show (fun x ↦ ‖Set.indicator ((l.1 : Tiling.Plane) +ᵥ T)
        (fun _ ↦ (1 : ℝ)) x‖ₑ) =
        Set.indicator ((l.1 : Tiling.Plane) +ᵥ T) (fun _ ↦ (1 : ℝ≥0∞)) by
      funext x
      by_cases hx : x ∈ (l.1 : Tiling.Plane) +ᵥ T <;> simp [hx]]
    rw [lintegral_indicator (hTm.const_vadd l.1), setLIntegral_one,
      Measure.restrict_apply (hTm.const_vadd l.1), inter_comm]
  simp_rw [hterm]
  exact hmeasure ▸ hTtop

private lemma tsum_integral_periodized_indicators
    {H : AddSubgroup Tiling.Plane} [Countable ↑H] {F T : Set Tiling.Plane}
    (hfd : IsAddFundamentalDomain H F volume) (hTm : MeasurableSet T)
    (hTtop : volume T ≠ ∞) :
    (∑' l : ↑H, ∫ x in F,
      Set.indicator ((l.1 : Tiling.Plane) +ᵥ T) (fun _ ↦ (1 : ℝ)) x) =
      (volume T).toReal := by
  have hmeasure := hfd.measure_eq_tsum T
  simp_rw [integral_indicator_const (1 : ℝ) (hTm.const_vadd _)]
  simp_rw [smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply (hTm.const_vadd _)]
  have htranslateTop (l : ↑H) : volume ((l.1 : Tiling.Plane) +ᵥ T) ≠ ∞ := by
    rw [MeasureTheory.measure_vadd volume]
    exact hTtop
  rw [← ENNReal.tsum_toReal_eq (f := fun l : ↑H ↦
    volume (((l.1 : Tiling.Plane) +ᵥ T) ∩ F)) (fun _ ↦
      ne_top_of_le_ne_top (htranslateTop _) (measure_mono inter_subset_left))]
  exact congrArg ENNReal.toReal hmeasure.symm

private lemma integral_periodization_over_fundamentalDomain
    {H : AddSubgroup Tiling.Plane} [Countable ↑H] {F T : Set Tiling.Plane}
    (hfd : IsAddFundamentalDomain H F volume) (hTm : MeasurableSet T)
    (hTtop : volume T ≠ ∞) :
    (∫ x in F, ∑' l : ↑H,
      Set.indicator ((l.1 : Tiling.Plane) +ᵥ T) (fun _ ↦ (1 : ℝ)) x) =
      (volume T).toReal := by
  let f : ↑H → Tiling.Plane → ℝ := fun l x ↦
    Set.indicator ((l.1 : Tiling.Plane) +ᵥ T) (fun _ ↦ (1 : ℝ)) x
  have hsumtop : (∑' l : ↑H, ∫⁻ x, ‖f l x‖ₑ ∂volume.restrict F) ≠ ∞ := by
    exact periodization_norm_tsum_ne_top hfd hTm hTtop
  have hswap := integral_tsum
    (fun (l : ↑H) ↦
      (measurable_const.indicator (hTm.const_vadd l.1)).aestronglyMeasurable)
    hsumtop
  change (∫ x in F, ∑' l : ↑H, f l x) = _
  rw [hswap]
  exact tsum_integral_periodized_indicators hfd hTm hTtop

private lemma integrable_periodization_over_fundamentalDomain
    {H : AddSubgroup Tiling.Plane} [Countable ↑H] {F T : Set Tiling.Plane}
    (hfd : IsAddFundamentalDomain H F volume) (hTm : MeasurableSet T)
    (hTtop : volume T ≠ ∞) :
    Integrable (fun x ↦ ∑' l : ↑H,
      Set.indicator ((l.1 : Tiling.Plane) +ᵥ T) (fun _ ↦ (1 : ℝ)) x)
      (volume.restrict F) := by
  let f : ↑H → Tiling.Plane → ℝ := fun l x ↦
    Set.indicator ((l.1 : Tiling.Plane) +ᵥ T) (fun _ ↦ (1 : ℝ)) x
  have hmeas (l : ↑H) : Measurable (f l) :=
    measurable_const.indicator (hTm.const_vadd l.1)
  have hsumtop := periodization_norm_tsum_ne_top hfd hTm hTtop
  refine ⟨(Measurable.tsum hmeas).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_top_iff_ne_top.mpr
  apply ne_top_of_le_ne_top hsumtop
  calc
    ∫⁻ x, ‖∑' l : ↑H, f l x‖ₑ ∂volume.restrict F ≤
        ∫⁻ x, ∑' l : ↑H, ‖f l x‖ₑ ∂volume.restrict F :=
      lintegral_mono fun x ↦ enorm_tsum_le_tsum_enorm
    _ = ∑' l : ↑H, ∫⁻ x, ‖f l x‖ₑ ∂volume.restrict F := by
      rw [lintegral_tsum]
      exact fun l ↦ (hmeas l).enorm.aemeasurable

private lemma integral_lattice_periodized_indicator
    (K : Region) (r : Tiling.Plane) {alpha beta shear : ℝ}
    (hα : 0 < alpha) (hβ : 0 < beta) :
    (∫ x in triangularFundamentalDomain alpha beta shear,
        ∑' l : ↑(triangularPeriodSubgroup alpha beta shear),
          Set.indicator ((l.1 + r) +ᵥ K.openCarrier)
            (fun _ ↦ (1 : ℝ)) x) =
      (volume K.openCarrier).toReal := by
  let L := triangularLattice alpha beta shear hα hβ
  let b := L.realBasis
  let H := triangularPeriodSubgroup alpha beta shear
  let F := triangularFundamentalDomain alpha beta shear
  have hLH : L.toAddSubgroup = H :=
    triangularLattice_subgroup alpha beta shear hα hβ
  have hspan : (Submodule.span ℤ (Set.range b)).toAddSubgroup = H := by
    rw [L.span_realBasis_toAddSubgroup, hLH]
  have hF : F = ZSpan.fundamentalDomain b :=
    triangularFundamentalDomain_eq_zspan alpha beta shear hα hβ
  have hfd : IsAddFundamentalDomain H F volume := by
    rw [hF, ← hspan]
    exact ZSpan.isAddFundamentalDomain' b volume
  have hHcountable : (H : Set Tiling.Plane).Countable := by
    apply (Set.countable_range fun p : ℤ × ℤ ↦
      p.1 • verticalPeriodVector alpha + p.2 • skewPeriodVector beta shear).mono
    rintro x ⟨m, n, rfl⟩
    exact ⟨(m, n), rfl⟩
  have hHinst : Countable ↑H := hHcountable.to_subtype
  let T : Set Tiling.Plane := r +ᵥ K.openCarrier
  have hTm : MeasurableSet T := (isOpen_interior.vadd r).measurableSet
  have hTtop : volume T ≠ ∞ := by
    exact ne_top_of_le_ne_top
      ((K.isPolygonal.isBounded.vadd r).measure_lt_top (μ := volume)).ne
      (measure_mono (by
        rintro x ⟨y, hy, rfl⟩
        exact ⟨y, interior_subset hy, rfl⟩))
  have hcore := integral_periodization_over_fundamentalDomain hfd hTm hTtop
  calc
    (∫ x in triangularFundamentalDomain alpha beta shear,
        ∑' l : ↑(triangularPeriodSubgroup alpha beta shear),
          Set.indicator ((l.1 + r) +ᵥ K.openCarrier)
            (fun _ ↦ (1 : ℝ)) x) =
        ∫ x in F, ∑' l : ↑H,
          Set.indicator ((l.1 : Tiling.Plane) +ᵥ T) (fun _ ↦ (1 : ℝ)) x := by
      apply integral_congr_ae
      filter_upwards with x
      apply tsum_congr
      intro l
      congr 1
      rw [vadd_vadd]
    _ = (volume T).toReal := hcore
    _ = (volume K.openCarrier).toReal := by
      dsimp only [T]
      rw [MeasureTheory.measure_vadd volume]

private lemma integrable_lattice_periodized_indicator
    (K : Region) (r : Tiling.Plane) {alpha beta shear : ℝ}
    (hα : 0 < alpha) (hβ : 0 < beta) :
    Integrable (fun x ↦
      ∑' l : ↑(triangularPeriodSubgroup alpha beta shear),
        Set.indicator ((l.1 + r) +ᵥ K.openCarrier) (fun _ ↦ (1 : ℝ)) x)
      (volume.restrict (triangularFundamentalDomain alpha beta shear)) := by
  let L := triangularLattice alpha beta shear hα hβ
  let b := L.realBasis
  let H := triangularPeriodSubgroup alpha beta shear
  let F := triangularFundamentalDomain alpha beta shear
  have hspan : (Submodule.span ℤ (Set.range b)).toAddSubgroup = H := by
    rw [L.span_realBasis_toAddSubgroup,
      triangularLattice_subgroup alpha beta shear hα hβ]
  have hF : F = ZSpan.fundamentalDomain b :=
    triangularFundamentalDomain_eq_zspan alpha beta shear hα hβ
  have hfd : IsAddFundamentalDomain H F volume := by
    rw [hF, ← hspan]
    exact ZSpan.isAddFundamentalDomain' b volume
  have hHcountable : (H : Set Tiling.Plane).Countable := by
    apply (Set.countable_range fun p : ℤ × ℤ ↦
      p.1 • verticalPeriodVector alpha + p.2 • skewPeriodVector beta shear).mono
    rintro x ⟨m, n, rfl⟩
    exact ⟨(m, n), rfl⟩
  have hHinst : Countable ↑H := hHcountable.to_subtype
  let T : Set Tiling.Plane := r +ᵥ K.openCarrier
  have hTm : MeasurableSet T := (isOpen_interior.vadd r).measurableSet
  have hTtop : volume T ≠ ∞ := by
    exact ne_top_of_le_ne_top
      ((K.isPolygonal.isBounded.vadd r).measure_lt_top (μ := volume)).ne
      (measure_mono (by
        rintro x ⟨y, hy, rfl⟩
        exact ⟨y, interior_subset hy, rfl⟩))
  have hc := integrable_periodization_over_fundamentalDomain hfd hTm hTtop
  apply hc.congr
  filter_upwards with x
  apply tsum_congr
  intro l
  congr 1
  rw [vadd_vadd]

theorem integral_periodizedTileMultiplicity :
    ∀ {K : Region} (R : Finset Tiling.Plane) {alpha beta shear : ℝ},
      0 < alpha → 0 < beta →
      ∫ x in triangularFundamentalDomain alpha beta shear,
          periodizedTileMultiplicity K R alpha beta shear x =
        (R.card : ℝ) * (volume K.openCarrier).toReal := by
  intro K R alpha beta shear hα hβ
  rw [show (∫ x in triangularFundamentalDomain alpha beta shear,
      periodizedTileMultiplicity K R alpha beta shear x) =
      ∫ x in triangularFundamentalDomain alpha beta shear,
        ∑ r : ↑R, ∑' l : ↑(triangularPeriodSubgroup alpha beta shear),
          Set.indicator ((l.1 + r.1) +ᵥ K.openCarrier)
            (fun _ ↦ (1 : ℝ)) x by
    congr 1
    funext x
    rw [periodizedTileMultiplicity, tsum_fintype]]
  rw [integral_finsetSum]
  · simp_rw [integral_lattice_periodized_indicator K _ hα hβ]
    simp
  · intro i hi
    exact integrable_lattice_periodized_indicator K i.1 hα hβ

theorem support_aePeriod_of_centrePeriod :
    ∀ {K : Region} {S : Set Tiling.Plane} {X : Set ℝ} {v : Tiling.Plane},
      MeasurableSet X → TilesOn K S {z : Tiling.Plane | z.re ∈ X} →
      v ∈ periodGroup S → (v.re +ᵥ X) =ᵐ[volume] X := by
  intro K S X v hX hTile hv
  let D : Set Tiling.Plane := {z | z.re ∈ X}
  have hDU : D =ᵐ[volume] openUnion K S := by
    filter_upwards [hTile.2.2] with z hz
    change (z.re ∈ X) = (z ∈ openUnion K S)
    simpa only [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier.eq_def,
      Set.mem_iUnion] using propext hz
  have hDR : D =ᵐ[volume] regularSupport K S :=
    hDU.trans (openUnion_aeEq_regularSupport hTile.2.1)
  have hRperiod : v +ᵥ regularSupport K S = regularSupport K S := by
    rw [← regularSupport_vadd, (periodGroup_isAddSubgroup S v).mp hv]
  have htranslated :=
    (quasiMeasurePreserving_add_left volume (-v)).vadd_ae_eq_of_ae_eq v hDR
  have hRperiodAE :
      (v +ᵥ regularSupport K S) =ᵐ[volume] regularSupport K S :=
    Filter.Eventually.of_forall fun z ↦ by
      change (z ∈ v +ᵥ regularSupport K S) = (z ∈ regularSupport K S)
      rw [hRperiod]
  have hplanar :
      (v +ᵥ D) =ᵐ[volume] D := by
    exact htranslated.trans (hRperiodAE.trans hDR.symm)
  have hcyl : v +ᵥ D = {z : Tiling.Plane | z.re ∈ v.re +ᵥ X} := by
    ext z
    simp only [D, Set.mem_vadd_set_iff_neg_vadd_mem, mem_ofPred_eq,
      Complex.add_re, Complex.neg_re, vadd_eq_add]
  rw [hcyl] at hplanar
  have hpull :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hplanar
  have hprod : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      (p.1 ∈ v.re +ᵥ X) = (p.1 ∈ X) := by
    filter_upwards [hpull] with p hp
    change (p.1 ∈ v.re +ᵥ X) = (p.1 ∈ X) at hp
    exact hp
  have hslices := MeasureTheory.Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hslices] with x hx
  obtain ⟨y, hy⟩ := hx.exists
  exact hy

theorem periodicTiling_torusArea_from_explicitDomain :
    ∀ {K : Region} {S : Set Tiling.Plane} {X : Set ℝ}
      {alpha beta shear : ℝ},
      0 < alpha → 0 < beta → MeasurableSet X →
      TilesOn K S {z : Tiling.Plane | z.re ∈ X} →
      verticalPeriodVector alpha ∈ periodGroup S →
      skewPeriodVector beta shear ∈ periodGroup S →
      (beta +ᵥ X) =ᵐ[volume] X →
      ∃ R : Finset Tiling.Plane,
        QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear) ''
            (R : Set Tiling.Plane) =
          QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear) '' S ∧
        Set.InjOn
          (QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear))
          (R : Set Tiling.Plane) ∧
        R.card = Set.ncard
          (QuotientAddGroup.mk'
            (triangularPeriodSubgroup alpha beta shear) '' S) ∧
        (R.card : ℝ) * (volume K.openCarrier).toReal =
          alpha * (volume (X ∩ Set.Ico 0 beta)).toReal := by
  intro K S X alpha beta shear hα hβ hX hTile hvertical hskew hXperiod
  obtain ⟨R, hRS, hQ, hinj⟩ :=
    exists_finiteOrbitRepresentatives hα hβ hTile hvertical hskew
  refine ⟨R, hQ, hinj, ?_, ?_⟩
  · rw [← hQ]
    simpa using hinj.ncard_image.symm
  · rw [← integral_periodizedTileMultiplicity R hα hβ,
      ← integral_slabIndicator_triangularFundamentalDomain hα hβ hX hXperiod]
    exact MeasureTheory.integral_congr_ae
      (periodizedTileMultiplicity_ae_eq_slabIndicator
        R hα hβ hX hTile hvertical hskew hRS hQ hinj)

theorem periodicTiling_torusArea :
    ∀ {K : Region} {S : Set Tiling.Plane} {X : Set ℝ}
      {alpha beta shear : ℝ},
    0 < alpha → 0 < beta → MeasurableSet X →
    TilesOn K S {z : Tiling.Plane | z.re ∈ X} →
    verticalPeriodVector alpha ∈ periodGroup S →
    skewPeriodVector beta shear ∈ periodGroup S →
    (beta +ᵥ X) =ᵐ[volume] X →
    ∃ r : ℕ,
      Set.Finite
        (QuotientAddGroup.mk'
          (triangularPeriodSubgroup alpha beta shear) '' S) ∧
      r = Set.ncard
        (QuotientAddGroup.mk'
          (triangularPeriodSubgroup alpha beta shear) '' S) ∧
      (r : ℝ) * (volume K.openCarrier).toReal =
        alpha * (volume (X ∩ Set.Ico 0 beta)).toReal := by
  intro K S X alpha beta shear hα hβ hX hTile hvertical hskew hXperiod
  obtain ⟨R, hQ, hinj, hcard, harea⟩ :=
    periodicTiling_torusArea_from_explicitDomain
      hα hβ hX hTile hvertical hskew hXperiod
  refine ⟨R.card, ?_, hcard, harea⟩
  rw [← hQ]
  exact R.finite_toSet.image _

theorem verticalPeriods_commensurable_of_rationalMasses :
    ∀ {alpha alphaColumn sourceCommonPeriod : ℝ},
      MixedRationalizationDatum alpha alphaColumn sourceCommonPeriod →
      0 < alpha → 0 < alphaColumn →
      ∃ q : ℚ, alpha = (q : ℝ) * alphaColumn := by
  intro alpha alphaColumn sourceCommonPeriod M hα hαc
  have hperiodN := support_aePeriod_of_centrePeriod
    M.nonColumnBase_measurable M.nonColumnTiles
    M.nonColumnHorizontalPeriod
  have hperiodC := support_aePeriod_of_centrePeriod
    M.columnBase_measurable M.columnTiles
    M.columnHorizontalPeriod
  have hperiodN' : M.rationalHorizontalPeriod +ᵥ M.nonColumnBase =ᵐ[volume]
      M.nonColumnBase := by
    simpa [skewPeriodVector] using hperiodN
  have hperiodC' : M.rationalHorizontalPeriod +ᵥ M.columnBase =ᵐ[volume]
      M.columnBase := by
    simpa [skewPeriodVector] using hperiodC
  obtain ⟨rN, -, -, hmassN⟩ := periodicTiling_torusArea
    hα M.rationalHorizontalPeriod_pos
    M.nonColumnBase_measurable M.nonColumnTiles M.nonColumnVerticalPeriod
    M.nonColumnHorizontalPeriod hperiodN'
  obtain ⟨rC, -, -, hmassC⟩ := periodicTiling_torusArea
    hαc M.rationalHorizontalPeriod_pos
    M.columnBase_measurable M.columnTiles M.columnVerticalPeriod
    M.columnHorizontalPeriod hperiodC'
  rw [M.nonColumnMass_eq] at hmassN
  rw [M.columnMass_eq] at hmassC
  have hmN : (0 : ℝ) < M.nonColumnMass := by exact_mod_cast M.nonColumnMass_pos
  have hmC : (0 : ℝ) < M.columnMass := by exact_mod_cast M.columnMass_pos
  have hrN : rN ≠ 0 := by
    intro hr
    subst rN
    have hz : alpha * (M.nonColumnMass : ℝ) = 0 := by
      simpa using hmassN.symm
    exact (mul_pos hα hmN).ne' hz
  have hrC : rC ≠ 0 := by
    intro hr
    subst rC
    have hz : alphaColumn * (M.columnMass : ℝ) = 0 := by
      simpa using hmassC.symm
    exact (mul_pos hαc hmC).ne' hz
  let q : ℚ := (rN : ℚ) * M.columnMass /
    ((rC : ℚ) * M.nonColumnMass)
  refine ⟨q, ?_⟩
  have hden : ((rC : ℝ) * (M.nonColumnMass : ℝ)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hrC) hmN.ne'
  change alpha =
    (((rN : ℚ) * M.columnMass / ((rC : ℚ) * M.nonColumnMass) : ℚ) : ℝ) *
      alphaColumn
  push_cast
  field_simp
  nlinarith [hmassN, hmassC]

end Tiling.AxisParallel.Terminal
