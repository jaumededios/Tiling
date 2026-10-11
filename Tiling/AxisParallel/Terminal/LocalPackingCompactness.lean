import Tiling.AxisParallel.Topology.FellCore
import Tiling.AxisParallel.Foundations.ExternalInputs
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.Topology.Metrizable.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.header false

open Filter Function MeasureTheory Set
open scoped BigOperators Pointwise symmDiff Topology

namespace Tiling.AxisParallel.Terminal.LocalPackingCompactness

open Tiling.AxisParallel Tiling.AxisParallel.Topology

noncomputable section

/-- The number of translated open carriers containing a point. -/
def multiplicity (K : Region) (S : Set Tiling.Plane) (z : Tiling.Plane) : ℕ :=
  Set.ncard {s : Tiling.Plane | s ∈ S ∧ z ∈ s +ᵥ K.openCarrier}

private theorem uniformSeparation_of_packings (K : Region) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Set Tiling.Plane,
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) → IsUniformlySeparated δ S := by
  obtain ⟨δ, hδ, hsep⟩ := exists_packingSeparation K
  exact ⟨δ, hδ, hsep⟩

private theorem contributingCentres_bounded (K : Region) (Q : Set Tiling.Plane)
    (hQ : Bornology.IsBounded Q) :
    ∃ Q' : Set Tiling.Plane, Bornology.IsBounded Q' ∧
      ∀ (S : Set Tiling.Plane) (s : Tiling.Plane),
        s ∈ S → volume ((s +ᵥ K.openCarrier) ∩ Q) ≠ 0 → s ∈ Q' := by
  let Q' : Set Tiling.Plane := Q - K.support
  refine ⟨Q', hQ.sub (K.isPolygonal.isCompact.isBounded), ?_⟩
  intro S s _hs hvolume
  have hne : ((s +ᵥ K.openCarrier) ∩ Q).Nonempty := by
    exact nonempty_iff_ne_empty.mpr fun hempty ↦ hvolume (hempty ▸ measure_empty)
  obtain ⟨z, hzTile, hzQ⟩ := hne
  rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzTile
  have hzTile' : z - s ∈ K.openCarrier := by
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using hzTile
  refine ⟨z, hzQ, z - s, interior_subset hzTile', ?_⟩
  abel_nf

private theorem locallyFell_eventually_exists_mem_ball
    {S : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hconv : LocallyFellConverges S L) {x : Tiling.Plane} (hx : x ∈ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ y ∈ S n, dist y x < ε := by
  rcases hconv with ⟨hS, hL, hconv⟩
  let U : Set (OnePoint Tiling.Plane) :=
    (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) '' Metric.ball x ε
  have hUopen : IsOpen U := OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball
  let V : Set (TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane)) :=
    {Q | ((Q : Set (OnePoint Tiling.Plane)) ∩ U).Nonempty}
  have hVopen : IsOpen V :=
    TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hUopen
  have hlimit : fellCompactification L hL ∈ V := by
    refine ⟨(x : OnePoint Tiling.Plane), ?_, ⟨x, ?_, rfl⟩⟩
    · simp [fellCompactification, Tiling.Topology.fellCompactification, hx]
    · exact Metric.mem_ball_self hε
  filter_upwards [hconv (hVopen.mem_nhds hlimit)] with n hn
  rcases hn with ⟨w, hwQ, hwU⟩
  rcases hwU with ⟨y, hy, rfl⟩
  refine ⟨y, ?_, Metric.mem_ball.mp hy⟩
  simpa [fellCompactification, Tiling.Topology.fellCompactification] using hwQ

private theorem locallyFell_eventually_disjoint_compact
    {S : ℕ → Set Tiling.Plane} {L C : Set Tiling.Plane}
    (hconv : LocallyFellConverges S L) (hC : IsCompact C)
    (hLC : Disjoint L C) :
    ∀ᶠ n : ℕ in atTop, Disjoint (S n) C := by
  rcases hconv with ⟨hS, hL, hconv⟩
  let C' : Set (OnePoint Tiling.Plane) :=
    (fun x : Tiling.Plane ↦ (x : OnePoint Tiling.Plane)) '' C
  have hC'closed : IsClosed C' := (hC.image OnePoint.continuous_coe).isClosed
  let U : Set (OnePoint Tiling.Plane) := C'ᶜ
  let V : Set (TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane)) :=
    {Q | (Q : Set (OnePoint Tiling.Plane)) ⊆ U}
  have hVopen : IsOpen V :=
    TopologicalSpace.NonemptyCompacts.isOpen_subsets_of_isOpen hC'closed.isOpen_compl
  have hlimit : fellCompactification L hL ∈ V := by
    intro z hzQ hzC'
    rcases hzC' with ⟨c, hcC, rfl⟩
    have hcL : c ∈ L := by
      simpa [fellCompactification, Tiling.Topology.fellCompactification] using hzQ
    exact Set.disjoint_left.mp hLC hcL hcC
  filter_upwards [hconv (hVopen.mem_nhds hlimit)] with n hn
  rw [Set.disjoint_left]
  intro x hxS hxC
  have hxQ : (x : OnePoint Tiling.Plane) ∈
      (fellCompactification (S n) (hS n) : Set (OnePoint Tiling.Plane)) := by
    simp [fellCompactification, Tiling.Topology.fellCompactification, hxS]
  exact hn hxQ ⟨x, hxC, rfl⟩

private theorem finite_inter_compact_of_uniformlySeparated
    {δ : ℝ} (hδ : 0 < δ) {S C : Set Tiling.Plane}
    (hS : IsUniformlySeparated δ S) (hC : IsCompact C) :
    (S ∩ C).Finite := by
  have hSclosed : IsClosed S := Metric.isClosed_of_pairwise_le_dist hδ hS
  have hSdiscrete : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro x hx
    refine ⟨Metric.ball x δ, Metric.isOpen_ball, ?_⟩
    ext y
    constructor
    · rintro ⟨hyball, hyS⟩
      have hyx : y = x := by
        by_contra hyx
        exact (not_lt_of_ge (hS hyS hx hyx)) (Metric.mem_ball.mp hyball)
      simp [hyx]
    · rintro rfl
      exact ⟨Metric.mem_ball_self hδ, hx⟩
  exact (hC.inter_left hSclosed).finite (hSdiscrete.mono inter_subset_left)

private theorem fell_matching_on_compact (K : Region) {δ : ℝ}
    {S : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hδ : 0 < δ)
    (hS : ∀ n, IsClosed (S n) ∧ IsUniformlySeparated δ (S n))
    (_hLclosed : IsClosed L) (hLsep : IsUniformlySeparated δ L)
    (hconv : LocallyFellConverges S L)
    (Q Q' : Set Tiling.Plane) (_hQ : IsCompact Q) (hQ' : IsCompact Q')
    (_hcontribL : ∀ s ∈ L, volume ((s +ᵥ K.openCarrier) ∩ Q) ≠ 0 → s ∈ Q')
    (hcontribS : ∀ n s, s ∈ S n →
      volume ((s +ᵥ K.openCarrier) ∩ Q) ≠ 0 → s ∈ Q') :
    ∃ N, ∀ n ≥ N, ∃ e : ↥(L ∩ Q') ↪ ↥(S n),
      (∀ s, dist (e s).1 s.1 < δ / 3) ∧
      ∀ s, s ∈ S n → volume ((s +ᵥ K.openCarrier) ∩ Q) ≠ 0 →
        ∃ a : ↥(L ∩ Q'), (e a).1 = s := by
  classical
  have hAfinite : (L ∩ Q').Finite :=
    finite_inter_compact_of_uniformlySeparated hδ hLsep hQ'
  let A := ↥(L ∩ Q')
  let _ : Fintype A := hAfinite.fintype
  have hδthird : 0 < δ / 3 := by positivity
  have hforward : ∀ᶠ n : ℕ in atTop,
      ∀ a : A, ∃! y : ↥(S n), dist y.1 a.1 < δ / 3 := by
    rw [eventually_all]
    intro a
    filter_upwards [locallyFell_eventually_exists_mem_ball hconv a.2.1 hδthird]
      with n hn
    obtain ⟨y, hyS, hya⟩ := hn
    refine ⟨⟨y, hyS⟩, hya, ?_⟩
    intro z hz
    apply Subtype.ext
    by_contra hzy
    have hsep := (hS n).2 z.2 hyS hzy
    have htri : dist z.1 y ≤ dist z.1 a.1 + dist a.1 y := dist_triangle _ _ _
    have hza : dist z.1 a.1 < δ / 3 := hz
    have hay : dist a.1 y < δ / 3 := by simpa [dist_comm] using hya
    linarith
  let D : Set Tiling.Plane :=
    Q' ∩ (⋃ a : A, Metric.ball a.1 (δ / 3))ᶜ
  have hDcompact : IsCompact D := by
    apply hQ'.inter_right
    exact isClosed_compl_iff.mpr (isOpen_iUnion fun a ↦ Metric.isOpen_ball)
  have hLD : Disjoint L D := by
    rw [Set.disjoint_left]
    intro x hxL hxD
    have hxA : x ∈ L ∩ Q' := ⟨hxL, hxD.1⟩
    exact hxD.2 (Set.mem_iUnion.mpr
      ⟨⟨x, hxA⟩, Metric.mem_ball_self hδthird⟩)
  have hmiss : ∀ᶠ n : ℕ in atTop, Disjoint (S n) D :=
    locallyFell_eventually_disjoint_compact hconv hDcompact hLD
  have hboth := hforward.and hmiss
  rw [eventually_atTop] at hboth
  obtain ⟨N, hN⟩ := hboth
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨hmatch, havoid⟩ := hN n hn
  let eFn : A → ↥(S n) := fun a ↦ Classical.choose (hmatch a)
  have eFn_spec (a : A) : dist (eFn a).1 a.1 < δ / 3 :=
    (Classical.choose_spec (hmatch a)).1
  have eFn_injective : Function.Injective eFn := by
    intro a b hab
    apply Subtype.ext
    by_contra habSource
    have hsep := hLsep a.2.1 b.2.1 habSource
    have htri : dist a.1 b.1 ≤ dist a.1 (eFn a).1 + dist (eFn a).1 b.1 :=
      dist_triangle _ _ _
    have hae : dist a.1 (eFn a).1 < δ / 3 := by
      simpa [dist_comm] using eFn_spec a
    have heb : dist (eFn a).1 b.1 < δ / 3 := by
      rw [hab]
      exact eFn_spec b
    linarith
  let e : A ↪ ↥(S n) := ⟨eFn, eFn_injective⟩
  refine ⟨e, fun a ↦ eFn_spec a, ?_⟩
  intro s hsS hsvolume
  have hsQ' : s ∈ Q' := hcontribS n s hsS hsvolume
  have hsNotD : s ∉ D := fun hsD ↦ Set.disjoint_left.mp havoid hsS hsD
  have hsUnion : s ∈ ⋃ a : A, Metric.ball a.1 (δ / 3) := by
    by_contra hs
    exact hsNotD ⟨hsQ', hs⟩
  obtain ⟨a, hsa⟩ := Set.mem_iUnion.mp hsUnion
  refine ⟨a, ?_⟩
  change (eFn a).1 = s
  exact (congrArg Subtype.val ((Classical.choose_spec (hmatch a)).2
    ⟨s, hsS⟩ (Metric.mem_ball.mp hsa))).symm

private theorem indicator_vadd_tendsto_L1 (K : Region)
    {t : ℕ → Tiling.Plane} {a : Tiling.Plane}
    (ht : Tendsto t atTop (nhds a)) :
    Tendsto (fun n => ∫ z, |indicator (t n +ᵥ K.openCarrier)
        (1 : Tiling.Plane → ℝ) z -
      indicator (a +ᵥ K.openCarrier) (1 : Tiling.Plane → ℝ) z|)
      atTop (nhds 0) := by
  let f : C(Tiling.Plane, C(Tiling.Plane, Tiling.Plane)) :=
    ContinuousMap.curry ⟨fun p ↦ -p.1 + p.2, by fun_prop⟩
  have hft : Tendsto (fun n ↦ f (t n)) atTop (nhds (f a)) :=
    (f.continuous.tendsto a).comp ht
  have hpres (u : Tiling.Plane) :
      MeasurePreserving (f u) volume volume := by
    change MeasurePreserving (fun z : Tiling.Plane ↦ -u + z) volume volume
    exact measurePreserving_add_left volume (-u)
  have hcarrierMeas : MeasurableSet K.openCarrier := K.openCarrier_regularOpen.1.measurableSet
  have hcarrierFinite : volume K.openCarrier ≠ ⊤ := by
    exact ne_top_of_le_ne_top K.isPolygonal.isCompact.measure_lt_top.ne
      (measure_mono interior_subset)
  have hmeasure := tendsto_measure_symmDiff_preimage_nhds_zero hft
    (Eventually.of_forall fun n ↦ hpres (t n)) (hpres a)
      hcarrierMeas.nullMeasurableSet hcarrierFinite
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeasure
  have hpreimage (u : Tiling.Plane) : f u ⁻¹' K.openCarrier = u +ᵥ K.openCarrier := by
    ext z
    rw [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem]
    change -u + z ∈ K.openCarrier ↔ -u +ᵥ z ∈ K.openCarrier
    simp only [vadd_eq_add]
  have hintegral (u : Tiling.Plane) :
      (∫ z, |indicator (u +ᵥ K.openCarrier) (1 : Tiling.Plane → ℝ) z -
        indicator (a +ᵥ K.openCarrier) (1 : Tiling.Plane → ℝ) z|) =
      (volume ((f u ⁻¹' K.openCarrier) ∆ (f a ⁻¹' K.openCarrier))).toReal := by
    rw [hpreimage u, hpreimage a]
    have hmeasU : MeasurableSet (u +ᵥ K.openCarrier) :=
      K.openCarrier_regularOpen.1.vadd u |>.measurableSet
    have hmeasA : MeasurableSet (a +ᵥ K.openCarrier) :=
      K.openCarrier_regularOpen.1.vadd a |>.measurableSet
    calc
      (∫ z, |indicator (u +ᵥ K.openCarrier) (1 : Tiling.Plane → ℝ) z -
          indicator (a +ᵥ K.openCarrier) (1 : Tiling.Plane → ℝ) z|) =
          ∫ z, indicator ((u +ᵥ K.openCarrier) ∆ (a +ᵥ K.openCarrier))
            (1 : Tiling.Plane → ℝ) z := by
              apply integral_congr_ae
              filter_upwards [] with z
              by_cases hzu : z ∈ u +ᵥ K.openCarrier <;>
                by_cases hza : z ∈ a +ᵥ K.openCarrier <;>
                simp [hzu, hza, Set.mem_symmDiff]
      _ = volume.real ((u +ᵥ K.openCarrier) ∆ (a +ᵥ K.openCarrier)) :=
        integral_indicator_one (hmeasU.symmDiff hmeasA)
      _ = (volume ((u +ᵥ K.openCarrier) ∆ (a +ᵥ K.openCarrier))).toReal :=
        measureReal_def volume _
  have hreal' : Tendsto (fun n ↦
      (volume ((f (t n) ⁻¹' K.openCarrier) ∆ (f a ⁻¹' K.openCarrier))).toReal)
      atTop (nhds 0) := by
    simpa [Function.comp_def] using hreal
  simpa only [hintegral] using hreal'

private theorem multiplicity_eq_finite_sum (K : Region) {S Q' : Set Tiling.Plane}
    (hfinite : (S ∩ Q').Finite) {z : Tiling.Plane}
    (hcontained : ∀ s ∈ S, z ∈ s +ᵥ K.openCarrier → s ∈ Q') :
    (multiplicity K S z : ℝ) =
      ∑ s ∈ hfinite.toFinset, indicator (s +ᵥ K.openCarrier)
        (1 : Tiling.Plane → ℝ) z := by
  classical
  let A : Set Tiling.Plane := {s | s ∈ S ∧ z ∈ s +ᵥ K.openCarrier}
  have hAfinite : A.Finite := hfinite.subset fun s hs ↦
    ⟨hs.1, hcontained s hs.1 hs.2⟩
  have hfilter : hfinite.toFinset.filter
      (fun s ↦ z ∈ s +ᵥ K.openCarrier) = hAfinite.toFinset := by
    ext s
    simp only [Finset.mem_filter, hfinite.mem_toFinset, hAfinite.mem_toFinset, A,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hsS, _hsQ'⟩, hz⟩
      exact ⟨hsS, hz⟩
    · rintro ⟨hsS, hz⟩
      exact ⟨⟨hsS, hcontained s hsS hz⟩, hz⟩
  calc
    (multiplicity K S z : ℝ) = (hAfinite.toFinset.card : ℝ) := by
      rw [multiplicity, show {s : Tiling.Plane | s ∈ S ∧
        z ∈ s +ᵥ K.openCarrier} = A from rfl,
        Set.ncard_eq_toFinset_card A hAfinite]
    _ = ∑ s ∈ hfinite.toFinset, indicator (s +ᵥ K.openCarrier)
        (1 : Tiling.Plane → ℝ) z := by
      rw [← hfilter]
      simp only [indicator_apply]
      simp

private theorem multiplicity_eq_matched_sum_ae (K : Region)
    {S Q Q' : Set Tiling.Plane} {A : Type*} [Fintype A]
    (e : A ↪ ↥S) (hfinite : (S ∩ Q').Finite)
    (hcontained : ∀ z ∈ Q, ∀ s ∈ S,
      z ∈ s +ᵥ K.openCarrier → s ∈ Q')
    (hsurj : ∀ s ∈ S, volume ((s +ᵥ K.openCarrier) ∩ Q) ≠ 0 →
      ∃ a : A, (e a).1 = s) :
    ∀ᵐ z ∂volume, z ∈ Q →
      (multiplicity K S z : ℝ) =
        ∑ a : A, indicator ((e a).1 +ᵥ K.openCarrier)
          (1 : Tiling.Plane → ℝ) z := by
  classical
  have hgood : ∀ᵐ z ∂volume, ∀ s ∈ hfinite.toFinset,
      z ∈ Q → z ∈ s +ᵥ K.openCarrier →
        volume ((s +ᵥ K.openCarrier) ∩ Q) ≠ 0 := by
    rw [eventually_all_finset]
    intro s hs
    by_cases hmeasure : volume ((s +ᵥ K.openCarrier) ∩ Q) = 0
    · rw [ae_iff]
      have hset : {z : Tiling.Plane | ¬ (z ∈ Q →
          z ∈ s +ᵥ K.openCarrier →
            volume ((s +ᵥ K.openCarrier) ∩ Q) ≠ 0)} =
          (s +ᵥ K.openCarrier) ∩ Q := by
        ext z
        simp [hmeasure, and_comm]
      rw [hset, hmeasure]
    · exact Eventually.of_forall fun _ _ _ ↦ hmeasure
  filter_upwards [hgood] with z hz zQ
  let C : Set Tiling.Plane := {s | s ∈ S ∧ z ∈ s +ᵥ K.openCarrier}
  let I : Set A := {a | z ∈ (e a).1 +ᵥ K.openCarrier}
  have hcard : I.ncard = C.ncard := Set.ncard_congr
    (fun a (_ha : a ∈ I) ↦ (e a).1)
    (fun a ha ↦ ⟨(e a).2, ha⟩)
    (fun a b _ _ hab ↦ e.injective (Subtype.ext hab))
    (by
      intro s hs
      have hsQ' : s ∈ Q' := hcontained z zQ s hs.1 hs.2
      have hsFin : s ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr ⟨hs.1, hsQ'⟩
      obtain ⟨a, ha⟩ := hsurj s hs.1 (hz s hsFin zQ hs.2)
      refine ⟨a, ?_, ha⟩
      change z ∈ (e a).1 +ᵥ K.openCarrier
      rw [ha]
      exact hs.2)
  calc
    (multiplicity K S z : ℝ) = (C.ncard : ℝ) := rfl
    _ = (I.ncard : ℝ) := by rw [hcard]
    _ = ∑ a : A, indicator ((e a).1 +ᵥ K.openCarrier)
        (1 : Tiling.Plane → ℝ) z := by
      rw [Set.ncard_eq_toFinset_card I (Set.toFinite I)]
      simp only [I, indicator_apply]
      norm_cast
      rw [Set.Finite.toFinset_ofPred]
      simp only [Pi.one_apply]
      exact_mod_cast (Finset.card_filter
        (fun a : A ↦ z ∈ (e a).1 +ᵥ K.openCarrier) Finset.univ)

private theorem locallyFell_multiplicity_tendsto (K : Region) {δ : ℝ}
    {S : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane} (hδ : 0 < δ)
    (hS : ∀ n, IsClosed (S n) ∧ IsUniformlySeparated δ (S n))
    (hLclosed : IsClosed L) (hLsep : IsUniformlySeparated δ L)
    (hconv : LocallyFellConverges S L) (Q : Set Tiling.Plane)
    (hQ : IsCompact Q) :
    Tendsto (fun n => ∫ z in Q, |(multiplicity K (S n) z : ℝ) -
      (multiplicity K L z : ℝ)|) atTop (nhds 0) := by
  classical
  let Q' : Set Tiling.Plane := Q - K.support
  have hQ' : IsCompact Q' := by
    simpa [Q', sub_eq_add_neg] using hQ.add K.isPolygonal.isCompact.neg
  have hcontained (z : Tiling.Plane) (hzQ : z ∈ Q) (T : Set Tiling.Plane)
      (s : Tiling.Plane) (_hs : s ∈ T) (hzs : z ∈ s +ᵥ K.openCarrier) :
      s ∈ Q' := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzs
    have hzK : z - s ∈ K.support := by
      have hzs' : z - s ∈ K.openCarrier := by
        simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using hzs
      exact interior_subset hzs'
    refine ⟨z, hzQ, z - s, hzK, ?_⟩
    abel_nf
  have hcontrib (T : Set Tiling.Plane) (s : Tiling.Plane) (hs : s ∈ T)
      (hvol : volume ((s +ᵥ K.openCarrier) ∩ Q) ≠ 0) : s ∈ Q' := by
    have hne : ((s +ᵥ K.openCarrier) ∩ Q).Nonempty :=
      nonempty_iff_ne_empty.mpr fun hempty ↦ hvol (hempty ▸ measure_empty)
    obtain ⟨z, hzs, hzQ⟩ := hne
    exact hcontained z hzQ T s hs hzs
  obtain ⟨N, hmatch⟩ := fell_matching_on_compact K hδ hS hLclosed hLsep
    hconv Q Q' hQ hQ' (hcontrib L) (fun n ↦ hcontrib (S n))
  have hAfinite : (L ∩ Q').Finite :=
    finite_inter_compact_of_uniformlySeparated hδ hLsep hQ'
  let A := ↥(L ∩ Q')
  let _ : Fintype A := hAfinite.fintype
  have hN (n : ℕ) : N ≤ n + N := by omega
  let e (n : ℕ) : A ↪ ↥(S (n + N)) := Classical.choose (hmatch (n + N) (hN n))
  have heclose (n : ℕ) (a : A) : dist (e n a).1 a.1 < δ / 3 :=
    (Classical.choose_spec (hmatch (n + N) (hN n))).1 a
  have hesurj (n : ℕ) (s : Tiling.Plane) (hs : s ∈ S (n + N))
      (hvol : volume ((s +ᵥ K.openCarrier) ∩ Q) ≠ 0) :
      ∃ a : A, (e n a).1 = s :=
    (Classical.choose_spec (hmatch (n + N) (hN n))).2 s hs hvol
  have hetend (a : A) : Tendsto (fun n ↦ (e n a).1) atTop (nhds a.1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let r : ℝ := min ε (δ / 4)
    have hr : 0 < r := lt_min hε (by positivity)
    have hhit := locallyFell_eventually_exists_mem_ball hconv a.2.1 hr
    rw [eventually_atTop] at hhit
    obtain ⟨M, hM⟩ := hhit
    refine ⟨M, fun n hn ↦ ?_⟩
    obtain ⟨u, huS, hua⟩ := hM (n + N) (hn.trans (Nat.le_add_right n N))
    have hue : u = (e n a).1 := by
      by_contra hne
      have hsep := (hS (n + N)).2 huS (e n a).2 hne
      have htri : dist u (e n a).1 ≤ dist u a.1 + dist a.1 (e n a).1 :=
        dist_triangle _ _ _
      have hua' : dist u a.1 < δ / 4 := hua.trans_le (min_le_right _ _)
      have hae : dist a.1 (e n a).1 < δ / 3 := by
        simpa [dist_comm] using heclose n a
      linarith
    rw [← hue]
    exact hua.trans_le (min_le_left _ _)
  let eL : A ↪ ↥L :=
    ⟨fun a ↦ ⟨a.1, a.2.1⟩, by
      intro a b hab
      apply Subtype.ext
      simpa using congrArg Subtype.val hab⟩
  have hlimitAE : ∀ᵐ z ∂volume, z ∈ Q →
      (multiplicity K L z : ℝ) =
        ∑ a : A, indicator (a.1 +ᵥ K.openCarrier)
          (1 : Tiling.Plane → ℝ) z := by
    have h := multiplicity_eq_matched_sum_ae K eL hAfinite
      (fun z hzQ s hs hzs ↦ hcontained z hzQ L s hs hzs)
      (fun s hs _ ↦ ⟨⟨s, hs, hcontrib L s hs (by assumption)⟩, rfl⟩)
    dsimp [eL] at h
    exact h
  have hseqAE (n : ℕ) : ∀ᵐ z ∂volume, z ∈ Q →
      (multiplicity K (S (n + N)) z : ℝ) =
        ∑ a : A, indicator ((e n a).1 +ᵥ K.openCarrier)
          (1 : Tiling.Plane → ℝ) z := by
    have hfinite : (S (n + N) ∩ Q').Finite :=
      finite_inter_compact_of_uniformlySeparated hδ (hS (n + N)).2 hQ'
    exact multiplicity_eq_matched_sum_ae K (e n) hfinite
      (fun z hzQ s hs hzs ↦ hcontained z hzQ (S (n + N)) s hs hzs)
      (hesurj n)
  have htileIntegrable (u : Tiling.Plane) :
      Integrable (indicator (u +ᵥ K.openCarrier)
        (1 : Tiling.Plane → ℝ)) := by
    rw [integrable_indicator_iff
      (K.openCarrier_regularOpen.1.vadd u).measurableSet]
    exact integrableOn_const
      (ne_top_of_le_ne_top (K.isPolygonal.isCompact.vadd u).measure_lt_top.ne
        (measure_mono (vadd_set_mono interior_subset))) (by simp)
  let g (n : ℕ) (a : A) (z : Tiling.Plane) : ℝ :=
    |indicator ((e n a).1 +ᵥ K.openCarrier) (1 : Tiling.Plane → ℝ) z -
      indicator (a.1 +ᵥ K.openCarrier) (1 : Tiling.Plane → ℝ) z|
  have hgIntegrable (n : ℕ) (a : A) : Integrable (g n a) :=
    (htileIntegrable (e n a).1).sub (htileIntegrable a.1) |>.abs
  have hbound (n : ℕ) :
      ∫ z in Q, |(multiplicity K (S (n + N)) z : ℝ) -
          (multiplicity K L z : ℝ)| ≤
        ∑ a : A, ∫ z, g n a z := by
    calc
      ∫ z in Q, |(multiplicity K (S (n + N)) z : ℝ) -
          (multiplicity K L z : ℝ)| =
          ∫ z in Q, |∑ a : A,
            (indicator ((e n a).1 +ᵥ K.openCarrier) (1 : Tiling.Plane → ℝ) z -
            indicator (a.1 +ᵥ K.openCarrier) (1 : Tiling.Plane → ℝ) z)| := by
            apply integral_congr_ae
            filter_upwards [(ae_restrict_iff' hQ.measurableSet).2 (hseqAE n),
              (ae_restrict_iff' hQ.measurableSet).2 hlimitAE] with z hsz hlz
            rw [hsz, hlz, Finset.sum_sub_distrib]
      _ ≤ ∫ z in Q, ∑ a : A, g n a z := by
        apply setIntegral_mono_ae_restrict
        · exact ((integrable_finsetSum Finset.univ fun a _ ↦
            (htileIntegrable (e n a).1).sub (htileIntegrable a.1))).norm.integrableOn
        · exact (integrable_finsetSum Finset.univ fun a _ ↦
            hgIntegrable n a).integrableOn
        · exact Eventually.of_forall fun z ↦ Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a : A, ∫ z in Q, g n a z := by
        rw [integral_finsetSum Finset.univ fun a _ ↦ (hgIntegrable n a).integrableOn]
      _ ≤ ∑ a : A, ∫ z, g n a z := by
        apply Finset.sum_le_sum
        intro a _
        exact setIntegral_le_integral (hgIntegrable n a)
          (Eventually.of_forall fun _ ↦ abs_nonneg _)
  have hsum : Tendsto (fun n ↦ ∑ a : A, ∫ z, g n a z) atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum Finset.univ fun a _ ↦
        indicator_vadd_tendsto_L1 K (hetend a))
  have hshift : Tendsto (fun n ↦ ∫ z in Q,
      |(multiplicity K (S (n + N)) z : ℝ) - (multiplicity K L z : ℝ)|)
      atTop (nhds 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hsum
        (Eventually.of_forall fun _ ↦ integral_nonneg fun _ ↦ abs_nonneg _)
        (Eventually.of_forall hbound)
  exact (tendsto_add_atTop_iff_nat N).mp hshift

private theorem packing_closed_under_locallyFell (K : Region) {δ : ℝ}
    {S : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane} (_hδ : 0 < δ)
    (hS : ∀ n, IsClosed (S n) ∧ IsUniformlySeparated δ (S n) ∧
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements (S n)))
    (_hLclosed : IsClosed L) (_hLsep : IsUniformlySeparated δ L)
    (hconv : LocallyFellConverges S L) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements L) := by
  rw [isPacking_iff_openCarrier_disjoint]
  intro s hsL t htL hst
  change Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.openCarrier)
  rw [Set.disjoint_left]
  intro x hxs hxt
  let U : Set Tiling.Plane := {c | x - c ∈ K.openCarrier}
  have hUopen : IsOpen U :=
    K.openCarrier_regularOpen.1.preimage (continuous_const.sub continuous_id)
  have hsU : s ∈ U := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxs
    simp only [vadd_eq_add] at hxs
    simpa only [U, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm] using hxs
  have htU : t ∈ U := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxt
    simp only [vadd_eq_add] at hxt
    simpa only [U, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm] using hxt
  obtain ⟨rs, hrs, hrsU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hsU)
  obtain ⟨rt, hrt, hrtU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds htU)
  let ε := min rs (min rt (dist s t / 3))
  have hdist : 0 < dist s t := dist_pos.mpr hst
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hrs (lt_min hrt (by positivity))
  have hεrs : ε ≤ rs := min_le_left _ _
  have hεrt : ε ≤ rt := (min_le_right _ _).trans (min_le_left _ _)
  have hεdist : ε ≤ dist s t / 3 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsEventually := locallyFell_eventually_exists_mem_ball hconv hsL hε
  have htEventually := locallyFell_eventually_exists_mem_ball hconv htL hε
  obtain ⟨n, ⟨s', hs'S, hs'dist⟩, ⟨t', ht'S, ht'dist⟩⟩ :=
    (hsEventually.and htEventually).exists
  have hs'U : s' ∈ U := hrsU (Metric.mem_ball.mpr (hs'dist.trans_le hεrs))
  have ht'U : t' ∈ U := hrtU (Metric.mem_ball.mpr (ht'dist.trans_le hεrt))
  have hs't' : s' ≠ t' := by
    intro heq
    subst t'
    have htriangle : dist s t ≤ dist s s' + dist s' t := dist_triangle _ _ _
    rw [dist_comm s s'] at htriangle
    have hsBound : dist s' s < dist s t / 3 := hs'dist.trans_le hεdist
    have htBound : dist s' t < dist s t / 3 := ht'dist.trans_le hεdist
    linarith
  have hdisjoint := (isPacking_iff_openCarrier_disjoint K (S n)).mp
    (hS n).2.2 hs'S ht'S hs't'
  apply Set.disjoint_left.mp hdisjoint
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [vadd_eq_add, U, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm]
      using hs'U
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [vadd_eq_add, U, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm]
      using ht'U

private theorem multiplicity_discrepancy_integrableOn (K : Region) {δ : ℝ}
    {L : Set Tiling.Plane} (hδ : 0 < δ) (hLsep : IsUniformlySeparated δ L)
    (Q : Set Tiling.Plane) (hQ : IsCompact Q) :
    IntegrableOn (fun z => |(multiplicity K L z : ℝ) - 1|) Q := by
  classical
  let Q' : Set Tiling.Plane := Q - K.support
  have hQ' : IsCompact Q' := by
    simpa [Q', sub_eq_add_neg] using hQ.add K.isPolygonal.isCompact.neg
  have hfinite : (L ∩ Q').Finite :=
    finite_inter_compact_of_uniformlySeparated hδ hLsep hQ'
  have hcontained (z : Tiling.Plane) (hzQ : z ∈ Q) (s : Tiling.Plane)
      (hs : s ∈ L) (hzs : z ∈ s +ᵥ K.openCarrier) : s ∈ Q' := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzs
    have hzs' : z - s ∈ K.openCarrier := by
      simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using hzs
    refine ⟨z, hzQ, z - s, interior_subset hzs', ?_⟩
    abel_nf
  let f : Tiling.Plane → ℝ := fun z ↦
    ∑ s ∈ hfinite.toFinset,
      indicator (s +ᵥ K.openCarrier) (1 : Tiling.Plane → ℝ) z
  have htileIntegrable (u : Tiling.Plane) :
      Integrable (indicator (u +ᵥ K.openCarrier)
        (1 : Tiling.Plane → ℝ)) := by
    rw [integrable_indicator_iff
      (K.openCarrier_regularOpen.1.vadd u).measurableSet]
    exact integrableOn_const
      (ne_top_of_le_ne_top (K.isPolygonal.isCompact.vadd u).measure_lt_top.ne
        (measure_mono (vadd_set_mono interior_subset))) (by simp)
  have hf : Integrable f := by
    exact integrable_finsetSum hfinite.toFinset fun s _ ↦ htileIntegrable s
  have hbase : IntegrableOn (fun z ↦ |f z - 1|) Q := by
    exact (hf.integrableOn.sub
      (integrableOn_const hQ.measure_lt_top.ne (by simp))).abs
  apply hbase.congr_fun
  · intro z hzQ
    change |f z - 1| = |(multiplicity K L z : ℝ) - 1|
    rw [multiplicity_eq_finite_sum K hfinite
      (fun s hs hzs ↦ hcontained z hzQ s hs hzs)]
  · exact hQ.measurableSet

private theorem boxCoverage_closed_under_limit (K : Region) {δ : ℝ}
    {S : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane} (hδ : 0 < δ)
    (hLsep : IsUniformlySeparated δ L) (_hconv : LocallyFellConverges S L)
    (N : Nat)
    (hmult : Tendsto (fun n => ∫ z in Metric.closedBall 0 N,
      |(multiplicity K (S n) z : ℝ) - (multiplicity K L z : ℝ)|)
      atTop (nhds 0))
    (hcover : ∀ n, ∀ᵐ z ∂volume,
      z ∈ Metric.closedBall 0 N → multiplicity K (S n) z = 1) :
    ∀ᵐ z ∂volume, z ∈ Metric.closedBall 0 N → multiplicity K L z = 1 := by
  let Q : Set Tiling.Plane := Metric.closedBall 0 N
  have hQ : IsCompact Q := isCompact_closedBall 0 N
  have hfint : IntegrableOn (fun z ↦ |(multiplicity K L z : ℝ) - 1|) Q :=
    multiplicity_discrepancy_integrableOn K hδ hLsep Q hQ
  have heq (n : ℕ) :
      (∫ z in Q, |(multiplicity K (S n) z : ℝ) -
        (multiplicity K L z : ℝ)|) =
      ∫ z in Q, |(multiplicity K L z : ℝ) - 1| := by
    apply integral_congr_ae
    have hn : ∀ᵐ z ∂volume.restrict Q, multiplicity K (S n) z = 1 :=
      (ae_restrict_iff' hQ.measurableSet).2 (hcover n)
    filter_upwards [hn] with z hz
    rw [hz]
    rw [abs_sub_comm]
    norm_num
  have htendConst : Tendsto (fun _ : ℕ ↦
      ∫ z in Q, |(multiplicity K L z : ℝ) - 1|) atTop (nhds 0) := by
    exact hmult.congr' (Eventually.of_forall heq)
  have hintegral : (∫ z in Q, |(multiplicity K L z : ℝ) - 1|) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds htendConst
  have hfzero : (fun z ↦ |(multiplicity K L z : ℝ) - 1|) =ᵐ[
      volume.restrict Q] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun _ ↦ abs_nonneg _) hfint).mp hintegral
  apply (ae_restrict_iff' hQ.measurableSet).mp
  filter_upwards [hfzero] with z hz
  have : (multiplicity K L z : ℝ) = 1 := by
    have habs : |(multiplicity K L z : ℝ) - 1| = 0 := by simpa using hz
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  exact_mod_cast this

/-- Local packing coverings on all positive integer balls produce a global tiling. -/
theorem localCoverings_compactness (K : Region)
    (hlocal : ∀ N : Nat, 0 < N → ∃ S : Set Tiling.Plane,
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) ∧
      ∀ᵐ z ∂volume, z ∈ Metric.closedBall 0 N → multiplicity K S z = 1) :
    ∃ L : Set Tiling.Plane, TilesOn K L univ := by
  classical
  choose S hSpacking hScover using fun n : ℕ ↦ hlocal (n + 1) (by omega)
  obtain ⟨δ, hδ, hseparated⟩ := uniformSeparation_of_packings K
  have hSsep (n : ℕ) : IsUniformlySeparated δ (S n) :=
    hseparated (S n) (hSpacking n)
  have hSclosed (n : ℕ) : IsClosed (S n) :=
    Metric.isClosed_of_pairwise_le_dist hδ (hSsep n)
  obtain ⟨φ, L, hφmono, hLclosed, hLsep, hconv⟩ :=
    Tiling.AxisParallel.Foundations.exists_locallyFellConvergent_subsequence
      δ hδ S hSclosed hSsep
  have hlimitPacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements L) :=
    packing_closed_under_locallyFell K hδ
      (fun n ↦ ⟨hSclosed (φ n), hSsep (φ n), hSpacking (φ n)⟩)
      hLclosed hLsep hconv
  have hbox (N : ℕ) : ∀ᵐ z ∂volume,
      z ∈ Metric.closedBall 0 N → multiplicity K L z = 1 := by
    let T : ℕ → Set Tiling.Plane := fun n ↦ S (φ (n + N))
    have hTclosedSep (n : ℕ) :
        IsClosed (T n) ∧ IsUniformlySeparated δ (T n) :=
      ⟨hSclosed _, hSsep _⟩
    have hTconv : LocallyFellConverges T L := by
      rcases hconv with ⟨hclosed, hclosedL, htend⟩
      refine ⟨fun n ↦ hclosed (n + N), hclosedL, ?_⟩
      convert htend.comp (tendsto_add_atTop_nat N) using 1
      funext n
      apply TopologicalSpace.NonemptyCompacts.ext
      rfl
    have hmult : Tendsto (fun n ↦ ∫ z in Metric.closedBall 0 N,
        |(multiplicity K (T n) z : ℝ) - (multiplicity K L z : ℝ)|)
        atTop (nhds 0) :=
      locallyFell_multiplicity_tendsto K hδ hTclosedSep hLclosed hLsep
        hTconv (Metric.closedBall 0 N) (isCompact_closedBall 0 N)
    have hTcover (n : ℕ) : ∀ᵐ z ∂volume,
        z ∈ Metric.closedBall 0 N → multiplicity K (T n) z = 1 := by
      filter_upwards [hScover (φ (n + N))] with z hz hzN
      apply hz
      have hindices : N ≤ φ (n + N) + 1 := by
        have := hφmono.id_le (n + N)
        dsimp [id] at this
        omega
      exact Metric.closedBall_subset_closedBall (mod_cast hindices) hzN
    exact boxCoverage_closed_under_limit K hδ hLsep hTconv N hmult hTcover
  have hglobalMultiplicity : ∀ᵐ z ∂volume, multiplicity K L z = 1 := by
    have hall : ∀ᵐ z ∂volume, ∀ N : ℕ,
        z ∈ Metric.closedBall 0 N → multiplicity K L z = 1 :=
      ae_all_iff.mpr hbox
    filter_upwards [hall] with z hz
    have hzmem : z ∈ ⋃ N : ℕ, Metric.closedBall 0 N := by
      rw [Metric.iUnion_closedBall_nat]
      exact Set.mem_univ z
    obtain ⟨N, hzN⟩ := Set.mem_iUnion.mp hzmem
    exact hz N hzN
  refine ⟨L, (tilesOn_iff_multiplicity K L univ).2 ⟨
    (IsPacking.locallyFinite_centres hlimitPacking).2, hlimitPacking, ?_⟩⟩
  filter_upwards [hglobalMultiplicity] with z hz
  simp only [Set.mem_univ, true_iff]
  have hcard : {s : Tiling.Plane | s ∈ L ∧ z ∈ s +ᵥ K.openCarrier}.ncard = 1 := by
    simpa only [multiplicity] using hz
  obtain ⟨s, hs⟩ := Set.ncard_eq_one.mp hcard
  have hsMem : s ∈ {t : Tiling.Plane | t ∈ L ∧ z ∈ t +ᵥ K.openCarrier} := by
    rw [hs]
    exact Set.mem_singleton s
  exact ⟨⟨s, hsMem.1⟩, hsMem.2⟩

end
end Tiling.AxisParallel.Terminal.LocalPackingCompactness
