import Tiling.AxisParallel.Core
import Tiling.AxisParallel.Topology.FellCore
import Tiling.AxisParallel.OneDimensional.Core
import Mathlib.MeasureTheory.Measure.AEDisjoint
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Bornology.BoundedOperation
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Maps.Proper.Basic

set_option linter.style.header false

open Filter Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Foundations

open Tiling.AxisParallel.OneDimensional

private theorem preimage_add_left (u : ℝ) (S : Set ℝ) :
    (fun x : ℝ ↦ -u + x) ⁻¹' S = u +ᵥ S := by
  ext x
  simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]

private theorem finite_inter_bounded_of_uniformlySeparated
    {S Q : Set ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hS : S.Pairwise fun x y ↦ delta ≤ dist x y)
    (hQ : Bornology.IsBounded Q) : (S ∩ Q).Finite := by
  have hSclosed : IsClosed S := Metric.isClosed_of_pairwise_le_dist hdelta hS
  have hSdiscrete : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro s hs
    refine ⟨Metric.ball s delta, Metric.isOpen_ball, ?_⟩
    ext t
    constructor
    · rintro ⟨htball, htS⟩
      by_cases hts : t = s
      · simp [hts]
      · have hsep := hS htS hs hts
        simp only [Metric.mem_ball] at htball
        exfalso
        exact (not_lt_of_ge (by simpa [dist_comm] using hsep)) htball
    · rintro rfl
      exact ⟨Metric.mem_ball_self hdelta, hs⟩
  obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : ℝ)
  have hcompact : IsCompact (S ∩ Metric.closedBall 0 R) :=
    Metric.isCompact_of_isClosed_isBounded
      (hSclosed.inter Metric.isClosed_closedBall)
      (Metric.isBounded_closedBall.subset inter_subset_right)
  apply (hcompact.finite (hSdiscrete.mono inter_subset_left)).subset
  exact inter_subset_inter_right S hR

/-- Positive finite-measure line tiles force uniformly separated, closed, locally finite centre
sets. -/
theorem linePacking_uniformlySeparated
    {B L X : Set ℝ}
    (hTile : LineTilesOn B L X)
    (hBfinite : MeasureTheory.volume B ≠ ⊤)
    (hBpositive : 0 < (MeasureTheory.volume B).toReal) :
    ∃ delta : ℝ, 0 < delta ∧
      Tiling.AxisParallel.Topology.IsUniformlySeparated delta L ∧
      IsClosed L ∧
      (∀ Q : Set ℝ, Bornology.IsBounded Q → (L ∩ Q).Finite) ∧
      L.Countable := by
  have hBpos : 0 < MeasureTheory.volume B :=
    (ENNReal.toReal_pos_iff.mp hBpositive).1
  obtain ⟨K, hKB, hKcompact, hKpos⟩ :=
    hTile.1.exists_lt_isCompact_of_ne_top hBfinite hBpos
  have hKne : MeasureTheory.volume K ≠ 0 := ne_of_gt hKpos
  have hevent : ∀ᶠ d : ℝ in 𝓝 0,
      MeasureTheory.volume ((d +ᵥ K) \ K) < MeasureTheory.volume K :=
    MeasureTheory.eventually_nhds_zero_measure_vadd_sdiff_lt
      hKcompact hKcompact.isClosed hKne
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hoverlap {d : ℝ} (hd : |d| < delta) :
      MeasureTheory.volume ((d +ᵥ K) ∩ K) ≠ 0 := by
    intro hzero
    have hdiff : MeasureTheory.volume ((d +ᵥ K) \ K) =
        MeasureTheory.volume (d +ᵥ K) := measure_sdiff_null' hzero
    have hlt := hball (by simpa [Real.dist_eq] using hd)
    change MeasureTheory.volume ((d +ᵥ K) \ K) < MeasureTheory.volume K at hlt
    rw [hdiff, measure_vadd] at hlt
    exact (lt_irrefl (MeasureTheory.volume K)) hlt
  have hsep : Tiling.AxisParallel.Topology.IsUniformlySeparated delta L := by
    intro s hs t ht hst
    by_contra hdist
    have hdist' : dist s t < delta := lt_of_not_ge hdist
    have hov := hoverlap (d := s - t)
      (by simpa [Real.dist_eq, abs_sub_comm] using hdist')
    have hsub : t +ᵥ (((s - t) +ᵥ K) ∩ K) ⊆
        (s +ᵥ B) ∩ (t +ᵥ B) := by
      rintro x ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
      obtain ⟨k, hk, rfl⟩ := hy₁
      constructor
      · refine ⟨k, hKB hk, ?_⟩
        simp only [vadd_eq_add]
        ring
      · refine ⟨(s - t) + k, hKB ?_, rfl⟩
        exact hy₂
    have htranslated :
        MeasureTheory.volume (t +ᵥ (((s - t) +ᵥ K) ∩ K)) ≠ 0 := by
      rw [measure_vadd]
      exact hov
    exact htranslated
      (measure_mono_null hsub (hTile.2.2.2.1 hs ht hst))
  have hclosed : IsClosed L :=
    Metric.isClosed_of_pairwise_le_dist hdelta hsep
  have hfinite : ∀ Q : Set ℝ, Bornology.IsBounded Q → (L ∩ Q).Finite :=
    fun Q hQ ↦ finite_inter_bounded_of_uniformlySeparated hdelta hsep hQ
  exact ⟨delta, hdelta, hsep, hclosed, hfinite, hTile.2.2.1⟩

theorem lineTilesOn_translate
    {B L X : Set ℝ} (hTile : LineTilesOn B L X) (u : ℝ) :
    LineTilesOn B (u +ᵥ L) (u +ᵥ X) := by
  refine ⟨hTile.1, hTile.2.1.const_vadd u, ?_, ?_, ?_⟩
  · have heq : u +ᵥ L = (fun l : ℝ ↦ u + l) '' L := by
      ext x
      simp [Set.mem_vadd_set_iff_neg_vadd_mem, add_comm]
    rw [heq]
    exact hTile.2.2.1.image _
  · intro l hl m hm hlm
    obtain ⟨l₀, hl₀, rfl⟩ := hl
    obtain ⟨m₀, hm₀, rfl⟩ := hm
    have hlm₀ : l₀ ≠ m₀ := by
      intro heq
      exact hlm (by simp [heq])
    have hd := hTile.2.2.2.1 hl₀ hm₀ hlm₀
    have hd' := hd.preimage
      (MeasureTheory.quasiMeasurePreserving_add_left MeasureTheory.volume (-u))
    rw [preimage_add_left, preimage_add_left] at hd'
    simpa [← add_vadd, add_comm] using hd'
  · have hpull :=
      (MeasureTheory.quasiMeasurePreserving_add_left MeasureTheory.volume (-u)).ae
        hTile.2.2.2.2
    filter_upwards [hpull] with x hx
    constructor
    · intro hxTarget
      have hxTarget' : -u + x ∈ X := by
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hxTarget
      obtain ⟨l, hl⟩ := hx.mp hxTarget'
      let l' : u +ᵥ L := ⟨u + l.1, by
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          neg_add_cancel_left] using l.2⟩
      refine ⟨l', ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hl ⊢
      convert hl using 1
      dsimp only [l']
      simp only [vadd_eq_add]
      ring
    · rintro ⟨l, hl⟩
      let l₀ : L := ⟨-u + l.1, by
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using l.2⟩
      have hxUnion : -u + x ∈ (l₀.1 +ᵥ B) := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hl ⊢
        convert hl using 1
        dsimp only [l₀]
        simp only [vadd_eq_add]
        ring
      have hxTarget := hx.mpr ⟨l₀, hxUnion⟩
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hxTarget

/-- Replacing the measurable one-dimensional tile by an a.e.-equal representative preserves
the tiling-on relation. -/
theorem lineTilesOn_congr_ae
    {B B' L X : Set ℝ}
    (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hBB' : B =ᵐ[MeasureTheory.volume] B') :
    LineTilesOn B L X ↔ LineTilesOn B' L X := by
  have forward {A A' : Set ℝ}
      (hA' : MeasurableSet A') (hAA' : A =ᵐ[MeasureTheory.volume] A')
      (hTile : LineTilesOn A L X) : LineTilesOn A' L X := by
    let _ : Countable L := hTile.2.2.1.to_subtype
    have hUnion :
        (⋃ l : L, (l.1 : ℝ) +ᵥ A) =ᵐ[MeasureTheory.volume]
          ⋃ l : L, (l.1 : ℝ) +ᵥ A' :=
      Filter.EventuallyEq.countable_iUnion fun l ↦
        (MeasureTheory.vadd_set_ae_eq l.1).mpr hAA'
    refine ⟨hA', hTile.2.1, hTile.2.2.1, ?_, ?_⟩
    · intro l hl m hm hlm
      exact (hTile.2.2.2.1 hl hm hlm).congr
        ((MeasureTheory.vadd_set_ae_eq l).mpr hAA').symm
        ((MeasureTheory.vadd_set_ae_eq m).mpr hAA').symm
    · filter_upwards [hTile.2.2.2.2, hUnion] with x hx hxu
      have hx' : x ∈ X ↔ x ∈ ⋃ l : L, (l.1 : ℝ) +ᵥ A := by
        simpa only [Set.mem_iUnion] using hx
      have hx'' : x ∈ X ↔ x ∈ ⋃ l : L, (l.1 : ℝ) +ᵥ A' :=
        hx'.trans (Iff.of_eq hxu)
      simpa only [Set.mem_iUnion] using hx''
  exact ⟨forward hB' hBB', forward hB hBB'.symm⟩

private theorem finiteIntervalRegion_measurable_bounded_aeClosure
    {B : Set ℝ} (hB : IsFiniteIntervalRegion B) :
    MeasurableSet B ∧ Bornology.IsBounded B ∧ B =ᵐ[volume] closure B := by
  obtain ⟨n, a, b, hab, rfl⟩ := hB
  have hmeas : MeasurableSet (⋃ i, Set.Ioo (a i) (b i)) :=
    MeasurableSet.iUnion fun _ ↦ measurableSet_Ioo
  have hbounded : Bornology.IsBounded (⋃ i, Set.Ioo (a i) (b i)) :=
    (Bornology.isBounded_iUnion).2 fun i ↦ Metric.isBounded_Ioo (a i) (b i)
  have hae : (⋃ i, Set.Ioo (a i) (b i)) =ᵐ[volume]
      ⋃ i, Set.Icc (a i) (b i) :=
    Filter.EventuallyEq.countable_iUnion fun _ ↦ MeasureTheory.Ioo_ae_eq_Icc
  have hclosure : closure (⋃ i, Set.Ioo (a i) (b i)) =
      ⋃ i, Set.Icc (a i) (b i) := by
    rw [closure_iUnion_of_finite]
    congr 1
    funext i
    exact closure_Ioo (ne_of_lt (hab i))
  exact ⟨hmeas, hbounded, hclosure.symm ▸ hae⟩

private theorem locallyFinite_closedTranslates
    {B L : Set ℝ} (hBbounded : Bornology.IsBounded B)
    (hL : ∀ Q : Set ℝ, Bornology.IsBounded Q → (L ∩ Q).Finite) :
    LocallyFinite (fun l : L ↦ (l.1 : ℝ) +ᵥ closure B) := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, ?_⟩
  let C : Set ℝ := Metric.ball x 1 - closure B
  have hCbounded : Bornology.IsBounded C :=
    isBounded_sub Metric.isBounded_ball hBbounded.closure
  have hfinite : (L ∩ C).Finite := hL C hCbounded
  apply (Finite.preimage Subtype.val_injective.injOn hfinite).subset
  intro l hl
  change (l.1 : ℝ) ∈ L ∩ C
  refine ⟨l.2, ?_⟩
  obtain ⟨z, hztranslate, hzball⟩ := hl
  obtain ⟨b, hb, rfl⟩ := hztranslate
  exact ⟨l.1 + b, hzball, b, hb, by simp⟩

theorem countable_of_locallyFinite_inter
    {L : Set ℝ}
    (hL : ∀ Q : Set ℝ, Bornology.IsBounded Q → (L ∩ Q).Finite) :
    L.Countable := by
  have hcount : (⋃ n : ℕ, L ∩ Metric.closedBall 0 n).Countable :=
    Set.countable_iUnion fun n ↦ (hL _ Metric.isBounded_closedBall).countable
  apply hcount.mono
  intro x hx
  rw [Set.mem_iUnion]
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  refine ⟨n, hx, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq]
  simpa using le_of_lt hn

/-- For a positive finite union of open intervals, the a.e. tiling convention is equivalent to
the literal closed-representative convention used by the one-dimensional source theorem. -/
theorem finiteOpenIntervals_source_iff_ae
    {B L : Set ℝ}
    (hB : IsFiniteIntervalRegion B)
    (hBpositive : 0 < (volume B).toReal) :
    LineTiles B L ↔
      (∀ Q : Set ℝ, Bornology.IsBounded Q → (L ∩ Q).Finite) ∧
      Set.Pairwise L
        (AEDisjoint volume on ((· +ᵥ closure B) : ℝ → Set ℝ)) ∧
      (⋃ l : L, l.1 +ᵥ closure B) = Set.univ := by
  obtain ⟨hBmeas, hBbounded, hBclosure⟩ :=
    finiteIntervalRegion_measurable_bounded_aeClosure hB
  have hClosureMeas : MeasurableSet (closure B) := isClosed_closure.measurableSet
  constructor
  · intro hTile
    have hBfinite : volume B ≠ ⊤ := hBbounded.measure_lt_top.ne
    obtain ⟨_, _, _, _, hlocal, _⟩ :=
      linePacking_uniformlySeparated hTile hBfinite hBpositive
    have hClosureTile : LineTiles (closure B) L :=
      (lineTilesOn_congr_ae hBmeas hClosureMeas hBclosure).mp hTile
    refine ⟨hlocal, hClosureTile.2.2.2.1, ?_⟩
    have hfamily := locallyFinite_closedTranslates hBbounded hlocal
    have hclosedUnion : IsClosed (⋃ l : L, l.1 +ᵥ closure B) :=
      hfamily.isClosed_iUnion fun _ ↦ isClosed_closure.vadd _
    have hfull : (⋃ l : L, l.1 +ᵥ closure B) =ᵐ[volume] Set.univ := by
      filter_upwards [hClosureTile.2.2.2.2] with x hx
      apply propext
      constructor
      · intro _
        exact Set.mem_univ x
      · intro _
        change x ∈ ⋃ l : L, l.1 +ᵥ closure B
        rw [Set.mem_iUnion]
        exact hx.mp (Set.mem_univ x)
    exact hclosedUnion.ae_eq_univ_iff_eq.mp hfull
  · rintro ⟨hlocal, hdisjoint, hcover⟩
    have hcount : L.Countable := countable_of_locallyFinite_inter hlocal
    have hClosureTile : LineTiles (closure B) L := by
      refine ⟨hClosureMeas, MeasurableSet.univ, hcount, hdisjoint, ?_⟩
      filter_upwards [] with x
      simp only [Set.mem_univ, true_iff]
      have hx : x ∈ ⋃ l : L, l.1 +ᵥ closure B := hcover.symm ▸ Set.mem_univ x
      simpa only [Set.mem_iUnion] using hx
    exact (lineTilesOn_congr_ae hBmeas hClosureMeas hBclosure).mpr hClosureTile

/-- A planar tiling equation restricts on almost every vertical line to a unique labelled
one-dimensional tiling equation. -/
theorem tilesOn_fubiniSlices
    {K : Tiling.AxisParallel.Region} {T D : Set Tiling.Plane}
    (hTile : Tiling.AxisParallel.TilesOn K T D) :
    ∀ᵐ x : ℝ ∂volume,
      ∀ᵐ y : ℝ ∂volume,
        ((x : ℂ) + (y : ℂ) * Complex.I ∈ D ↔
          ∃! t : T,
            y - t.1.im ∈
              {v : ℝ |
                ((x - t.1.re : ℝ) : ℂ) + (v : ℂ) * Complex.I ∈
                  K.openCarrier}) := by
  let _ : Countable T := hTile.1.to_subtype
  have hunique : ∀ᵐ z : Tiling.Plane ∂volume,
      ∀ s t : T, z ∈ s.1 +ᵥ K.openCarrier →
        z ∈ t.1 +ᵥ K.openCarrier → s = t := by
    apply ae_all_iff.mpr
    intro s
    apply ae_all_iff.mpr
    intro t
    by_cases hst : s = t
    · exact Filter.Eventually.of_forall fun _ _ _ ↦ hst
    · let i : Tiling.Placement Tiling.Plane Unit := (s.1, ())
      let j : Tiling.Placement Tiling.Plane Unit := (t.1, ())
      have hi : i ∈ K.toPolygonalRegion.placements T := s.2
      have hj : j ∈ K.toPolygonalRegion.placements T := t.2
      have hij : i ≠ j := by
        intro hij
        apply hst
        apply Subtype.ext
        exact congrArg Prod.fst hij
      have hd := hTile.2.1 hi hj hij
      have hnot : ∀ᵐ z : Tiling.Plane ∂volume,
          z ∉ (s.1 +ᵥ K.support) ∩ (t.1 +ᵥ K.support) :=
        measure_eq_zero_iff_ae_notMem.mp hd
      filter_upwards [hnot] with z hz hs ht
      exfalso
      apply hz
      exact ⟨Set.vadd_set_mono interior_subset hs,
        Set.vadd_set_mono interior_subset ht⟩
  have hplane : ∀ᵐ z : Tiling.Plane ∂volume,
      (z ∈ D ↔ ∃! t : T,
        z.im - t.1.im ∈
          {v : ℝ |
            ((z.re - t.1.re : ℝ) : ℂ) + (v : ℂ) * Complex.I ∈
              K.openCarrier}) := by
    filter_upwards [hTile.2.2, hunique] with z hcover huniq
    have hslice (t : T) :
        z.im - t.1.im ∈
            {v : ℝ |
              ((z.re - t.1.re : ℝ) : ℂ) + (v : ℂ) * Complex.I ∈
                K.openCarrier} ↔
          z ∈ t.1 +ᵥ K.openCarrier := by
      simp only [Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
      rw [show -t.1 + z =
          ((z.re - t.1.re : ℝ) : ℂ) + ((z.im - t.1.im : ℝ) : ℂ) * Complex.I by
        apply Complex.ext <;> simp <;> ring]
    constructor
    · intro hzD
      obtain ⟨t, ht⟩ := hcover.mp hzD
      refine ⟨t, (hslice t).mpr ht, ?_⟩
      intro s hs
      exact huniq s t ((hslice s).mp hs) ht
    · rintro ⟨t, ht, _⟩
      exact hcover.mpr ⟨t, (hslice t).mp ht⟩
  have hprod : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      (((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∈ D ↔
        ∃! t : T,
          p.2 - t.1.im ∈
            {v : ℝ |
              ((p.1 - t.1.re : ℝ) : ℂ) + (v : ℂ) * Complex.I ∈
                K.openCarrier}) := by
    have hpull := Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hplane
    filter_upwards [hpull] with p hp
    have heq : ({ re := p.1, im := p.2 } : ℂ) =
        (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [← heq]
    exact hp
  exact MeasureTheory.Measure.ae_ae_of_ae_prod hprod

/-- Normalizing at a chosen centre preserves the tiling and all literal periods. -/
theorem normalizeLineTiling_spec
    {B L : Set ℝ}
    (hTile : LineTiles B L)
    {l0 : ℝ} (hl0 : l0 ∈ L) :
    ∃ N : NormalizedLineTiling B,
      N.centres = normalizeLineTiling L l0 ∧
      ∀ p : ℝ, (p +ᵥ N.centres = N.centres ↔ p +ᵥ L = L) := by
  have hnormalized : LineTiles B (normalizeLineTiling L l0) := by
    have htranslated := lineTilesOn_translate hTile (-l0)
    simpa [Tiling.AxisParallel.OneDimensional.LineTiles,
      Tiling.AxisParallel.OneDimensional.normalizeLineTiling] using htranslated
  let N : NormalizedLineTiling B := {
    centres := normalizeLineTiling L l0
    tiles := hnormalized
    zero_mem := by
      change 0 ∈ (-l0) +ᵥ L
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add,
        zero_add, add_zero] using hl0 }
  refine ⟨N, rfl, ?_⟩
  intro p
  change (p +ᵥ ((-l0) +ᵥ L) = (-l0) +ᵥ L) ↔ p +ᵥ L = L
  constructor
  · intro hp
    have hp' := congrArg (fun A : Set ℝ ↦ l0 +ᵥ A) hp
    rw [← add_vadd, ← add_vadd, ← add_vadd,
      add_neg_cancel, zero_vadd] at hp'
    have hscalar : l0 + p + -l0 = p := by ring
    rw [hscalar] at hp'
    exact hp'
  · intro hp
    calc
      p +ᵥ (-l0 +ᵥ L) = (-l0) +ᵥ (p +ᵥ L) := by
        rw [← add_vadd, ← add_vadd]
        congr 1
        ring
      _ = (-l0) +ᵥ L := congrArg ((-l0) +ᵥ ·) hp

private theorem lineTilesOn_target_congr
    {B L X X' : Set ℝ}
    (hX' : MeasurableSet X') (hXX' : X =ᵐ[MeasureTheory.volume] X')
    (hTile : LineTilesOn B L X) : LineTilesOn B L X' := by
  refine ⟨hTile.1, hX', hTile.2.2.1, hTile.2.2.2.1, ?_⟩
  filter_upwards [hTile.2.2.2.2, hXX'] with x hx hxx
  exact (Iff.of_eq hxx).symm.trans hx

/-- A finite translation orbit over a periodic target supplies a positive centre period no larger
than the number of admissible tilings. -/
theorem lineTilesOn_periodic_of_finiteOrbit
    {B H X : Set ℝ} {p : ℝ}
    (_hp : 0 < p)
    (hperiod : X =ᵐ[MeasureTheory.volume] p +ᵥ X)
    (hfinite : Set.Finite {L : Set ℝ | LineTilesOn B L X})
    (hTile : LineTilesOn B H X) :
    ∃ n : ℕ, 0 < n ∧
      n ≤ Set.ncard {L : Set ℝ | LineTilesOn B L X} ∧
      ((n : ℝ) * p) +ᵥ H = H := by
  let A : Set (Set ℝ) := {L : Set ℝ | LineTilesOn B L X}
  have hstep {L : Set ℝ} (hL : LineTilesOn B L X) :
      LineTilesOn B (p +ᵥ L) X :=
    lineTilesOn_target_congr hL.2.1 hperiod.symm (lineTilesOn_translate hL p)
  have hiter : ∀ n : ℕ, LineTilesOn B (((n : ℝ) * p) +ᵥ H) X := by
    intro n
    induction n with
    | zero => simpa using hTile
    | succ n ih =>
      have hs := hstep ih
      convert hs using 1
      rw [← add_vadd]
      congr 1
      push_cast
      ring
  let F : ℕ → Set ℝ := fun n ↦ ((n : ℝ) * p) +ᵥ H
  have hmaps : Set.MapsTo F (Finset.range (A.ncard + 1) : Set ℕ) A := by
    intro n _
    exact hiter n
  have hmaps' : Set.MapsTo F (Finset.range (A.ncard + 1) : Set ℕ)
      (hfinite.toFinset : Set (Set ℝ)) := by
    intro n hn
    apply (Set.Finite.mem_toFinset hfinite).mpr
    exact hmaps hn
  have hcard : hfinite.toFinset.card < (Finset.range (A.ncard + 1)).card := by
    simp [A, Set.ncard_eq_toFinset_card _ hfinite]
  obtain ⟨i, hi, j, hj, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps'
  have hi' : i < A.ncard + 1 := Finset.mem_range.mp hi
  have hj' : j < A.ncard + 1 := Finset.mem_range.mp hj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · let n := j - i
    have hn : 0 < n := Nat.sub_pos_of_lt hijlt
    have hnle : n ≤ A.ncard := by omega
    refine ⟨n, hn, hnle, ?_⟩
    have hcancel := congrArg (fun S : Set ℝ ↦ (-(i : ℝ) * p) +ᵥ S) heq
    dsimp only [F] at hcancel
    rw [← add_vadd, ← add_vadd] at hcancel
    have hleft : -(i : ℝ) * p + (i : ℝ) * p = 0 := by ring
    have hright : -(i : ℝ) * p + (j : ℝ) * p = (n : ℝ) * p := by
      dsimp only [n]
      rw [Nat.cast_sub (Nat.le_of_lt hijlt)]
      ring
    rw [hleft, zero_vadd, hright] at hcancel
    exact hcancel.symm
  · let n := i - j
    have hn : 0 < n := Nat.sub_pos_of_lt hjilt
    have hnle : n ≤ A.ncard := by omega
    refine ⟨n, hn, hnle, ?_⟩
    have hcancel := congrArg (fun S : Set ℝ ↦ (-(j : ℝ) * p) +ᵥ S) heq.symm
    dsimp only [F] at hcancel
    rw [← add_vadd, ← add_vadd] at hcancel
    have hleft : -(j : ℝ) * p + (j : ℝ) * p = 0 := by ring
    have hright : -(j : ℝ) * p + (i : ℝ) * p = (n : ℝ) * p := by
      dsimp only [n]
      rw [Nat.cast_sub (Nat.le_of_lt hjilt)]
      ring
    rw [hleft, zero_vadd, hright] at hcancel
    exact hcancel.symm

private def verticalEmbedding (x : ℝ) : ℂ :=
  Complex.equivRealProdCLM.symm (0, x)

private theorem verticalEmbedding_isClosedEmbedding :
    Topology.IsClosedEmbedding verticalEmbedding := by
  have hp : Topology.IsClosedEmbedding (Prod.mk (0 : ℝ) : ℝ → ℝ × ℝ) := by
    refine ⟨isEmbedding_prodMkRight (0 : ℝ), ?_⟩
    have hrange : Set.range (Prod.mk (0 : ℝ) : ℝ → ℝ × ℝ) =
        ({0} : Set ℝ) ×ˢ Set.univ := by
      ext p
      simp [eq_comm, Prod.ext_iff]
    rw [hrange]
    exact isClosed_singleton.prod isClosed_univ
  unfold verticalEmbedding
  exact Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.comp hp

private theorem verticalEmbedding_tendsto_coclosedCompact :
    Tendsto verticalEmbedding (coclosedCompact ℝ) (coclosedCompact ℂ) := by
  rw [hasBasis_coclosedCompact.tendsto_right_iff]
  rintro K ⟨hKclosed, hKcompact⟩
  change verticalEmbedding ⁻¹' Kᶜ ∈ coclosedCompact ℝ
  rw [preimage_compl]
  exact hasBasis_coclosedCompact.mem_of_mem ⟨
    hKclosed.preimage verticalEmbedding_isClosedEmbedding.continuous,
    verticalEmbedding_isClosedEmbedding.isProperMap.isCompact_preimage hKcompact⟩

private theorem verticalEmbedding_onePoint_continuous :
    Continuous (OnePoint.map verticalEmbedding) :=
  OnePoint.continuous_map verticalEmbedding_isClosedEmbedding.continuous
    verticalEmbedding_tendsto_coclosedCompact

private theorem verticalEmbedding_onePoint_isClosedEmbedding :
    Topology.IsClosedEmbedding (OnePoint.map verticalEmbedding) :=
  verticalEmbedding_onePoint_continuous.isClosedEmbedding (by
    intro x y hxy
    induction x using OnePoint.rec with
    | infty =>
        induction y using OnePoint.rec with
        | infty => rfl
        | coe y => simp at hxy
    | coe x =>
        induction y using OnePoint.rec with
        | infty => simp at hxy
        | coe y =>
            simp only [OnePoint.map_some, OnePoint.coe_eq_coe] at hxy
            exact congrArg some (verticalEmbedding_isClosedEmbedding.injective hxy))

private theorem verticalImage_eq (S : Set ℝ) :
    Complex.equivRealProdCLM.symm '' Set.prod {0} S = verticalEmbedding '' S := by
  ext z
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(0, y), ⟨Set.mem_singleton 0, hy⟩, rfl⟩

private theorem verticalImage_isClosed (S : Set ℝ) (hS : IsClosed S) :
    IsClosed (Complex.equivRealProdCLM.symm '' Set.prod {0} S) := by
  rw [verticalImage_eq]
  exact verticalEmbedding_isClosedEmbedding.isClosedMap S hS

private theorem fellCompactification_verticalImage
    (S : Set ℝ) (hS : IsClosed S) :
    Tiling.AxisParallel.Topology.fellCompactification
        (Complex.equivRealProdCLM.symm '' Set.prod {0} S)
        (verticalImage_isClosed S hS) =
      (Tiling.AxisParallel.Topology.fellCompactification S hS).map
        (OnePoint.map verticalEmbedding) verticalEmbedding_onePoint_continuous := by
  apply TopologicalSpace.NonemptyCompacts.ext
  ext z
  induction z using OnePoint.rec with
  | infty => simp [Tiling.AxisParallel.Topology.fellCompactification,
      Tiling.Topology.fellCompactification]
  | coe z =>
      simp [Tiling.AxisParallel.Topology.fellCompactification,
        Tiling.Topology.fellCompactification, verticalImage_eq,
        verticalEmbedding]

/-- Embedding a closed subset of the line as the vertical axis preserves and reflects local
Fell convergence. -/
theorem verticalEmbedding_locallyFellConverges_iff
    (S : ℕ → Set ℝ) (L : Set ℝ)
    (hS : ∀ n, IsClosed (S n)) (hL : IsClosed L) :
    Tiling.AxisParallel.Topology.LocallyFellConverges S L ↔
      Tiling.AxisParallel.Topology.LocallyFellConverges
        (Set.image Complex.equivRealProdCLM.symm ∘ Set.prod {0} ∘ S)
        (Complex.equivRealProdCLM.symm '' Set.prod {0} L) := by
  let F := TopologicalSpace.NonemptyCompacts.map (OnePoint.map verticalEmbedding)
    verticalEmbedding_onePoint_continuous
  have hF : Topology.IsClosedEmbedding F := by
    dsimp only [F]
    exact verticalEmbedding_onePoint_isClosedEmbedding.nonemptyCompacts_map
  rw [Tiling.AxisParallel.Topology.LocallyFellConverges,
    Tiling.AxisParallel.Topology.LocallyFellConverges]
  constructor
  · rintro ⟨_, _, hconv⟩
    refine ⟨fun n ↦ verticalImage_isClosed (S n) (hS n),
      verticalImage_isClosed L hL, ?_⟩
    have hsource : Tendsto
        (fun n ↦ Tiling.AxisParallel.Topology.fellCompactification (S n) (hS n)) atTop
        (nhds (Tiling.AxisParallel.Topology.fellCompactification L hL)) := by
      simpa only using hconv
    have hmapped := (hF.tendsto_nhds_iff (g := fun n ↦
      Tiling.AxisParallel.Topology.fellCompactification (S n) (hS n))).mp hsource
    simpa [F, Function.comp_def, fellCompactification_verticalImage] using hmapped
  · rintro ⟨_, _, hconv⟩
    refine ⟨hS, hL, ?_⟩
    have hmapped : Tendsto
        (F ∘ fun n ↦ Tiling.AxisParallel.Topology.fellCompactification (S n) (hS n)) atTop
        (nhds (F (Tiling.AxisParallel.Topology.fellCompactification L hL))) := by
      simpa [F, Function.comp_def, fellCompactification_verticalImage] using hconv
    exact (hF.tendsto_nhds_iff (g := fun n ↦
      Tiling.AxisParallel.Topology.fellCompactification (S n) (hS n))).mpr hmapped

private theorem lineSubtilings_unique
    {B L A H X : Set ℝ}
    (hBpositive : 0 < (MeasureTheory.volume B).toReal)
    (hWhole : LineTiles B L)
    (hA : A ⊆ L) (hH : H ⊆ L)
    (hATile : LineTilesOn B A X) (hHTile : LineTilesOn B H X) :
    A = H := by
  apply Set.Subset.antisymm
  · intro a ha
    by_contra haH
    let _ : Countable H := hHTile.2.2.1.to_subtype
    let HU : Set ℝ := ⋃ h : H, (h : ℝ) +ᵥ B
    have hdisjoint : MeasureTheory.AEDisjoint MeasureTheory.volume
        (a +ᵥ B) HU := by
      dsimp only [HU]
      rw [MeasureTheory.AEDisjoint.iUnion_right_iff]
      intro h
      apply hWhole.2.2.2.1 (hA ha) (hH h.2)
      intro hah
      apply haH
      simpa only [← hah] using h.2
    have hsubset : ∀ᵐ x ∂MeasureTheory.volume,
        x ∈ a +ᵥ B → x ∈ HU := by
      filter_upwards [hATile.2.2.2.2, hHTile.2.2.2.2] with x hxA hxH
      intro hxa
      have hxX : x ∈ X := hxA.mpr ⟨⟨a, ha⟩, hxa⟩
      obtain ⟨h, hxh⟩ := hxH.mp hxX
      change x ∈ ⋃ h : H, (h : ℝ) +ᵥ B
      rw [Set.mem_iUnion]
      exact ⟨h, hxh⟩
    have hinter : (a +ᵥ B) =ᵐ[MeasureTheory.volume]
        Set.inter (a +ᵥ B) HU := by
      filter_upwards [hsubset] with x hx
      apply propext
      exact ⟨fun hxa ↦ ⟨hxa, hx hxa⟩, fun hxi ↦ hxi.1⟩
    have hzero : MeasureTheory.volume (a +ᵥ B) = 0 := by
      rw [MeasureTheory.measure_congr hinter]
      exact hdisjoint
    have hBzero : MeasureTheory.volume B = 0 := by
      simpa only [MeasureTheory.measure_vadd] using hzero
    rw [hBzero] at hBpositive
    simp at hBpositive
  · intro h hh
    by_contra hhA
    let _ : Countable A := hATile.2.2.1.to_subtype
    let AU : Set ℝ := ⋃ a : A, (a : ℝ) +ᵥ B
    have hdisjoint : MeasureTheory.AEDisjoint MeasureTheory.volume
        (h +ᵥ B) AU := by
      dsimp only [AU]
      rw [MeasureTheory.AEDisjoint.iUnion_right_iff]
      intro a
      apply hWhole.2.2.2.1 (hH hh) (hA a.2)
      intro hha
      apply hhA
      simpa only [← hha] using a.2
    have hsubset : ∀ᵐ x ∂MeasureTheory.volume,
        x ∈ h +ᵥ B → x ∈ AU := by
      filter_upwards [hHTile.2.2.2.2, hATile.2.2.2.2] with x hxH hxA
      intro hxh
      have hxX : x ∈ X := hxH.mpr ⟨⟨h, hh⟩, hxh⟩
      obtain ⟨a, hxa⟩ := hxA.mp hxX
      change x ∈ ⋃ a : A, (a : ℝ) +ᵥ B
      rw [Set.mem_iUnion]
      exact ⟨a, hxa⟩
    have hinter : (h +ᵥ B) =ᵐ[MeasureTheory.volume]
        Set.inter (h +ᵥ B) AU := by
      filter_upwards [hsubset] with x hx
      apply propext
      exact ⟨fun hxh ↦ ⟨hxh, hx hxh⟩, fun hxi ↦ hxi.1⟩
    have hzero : MeasureTheory.volume (h +ᵥ B) = 0 := by
      rw [MeasureTheory.measure_congr hinter]
      exact hdisjoint
    have hBzero : MeasureTheory.volume B = 0 := by
      simpa only [MeasureTheory.measure_vadd] using hzero
    rw [hBzero] at hBpositive
    simp at hBpositive

set_option linter.unusedVariables false

/-- A sub-tiling of a whole-line tiling inherits a period shared by the
ambient centres and its target. -/
theorem lineSubtiling_periodic_of_commonPeriod
    {B L H X : Set ℝ} {q : ℝ}
    (hBfinite : MeasureTheory.volume B ≠ ⊤)
    (hBpositive : 0 < (MeasureTheory.volume B).toReal)
    (hWhole : LineTiles B L)
    (hsub : H ⊆ L)
    (hTarget : LineTilesOn B H X)
    (hq : 0 < q) (hLperiod : q +ᵥ L = L)
    (hXperiod : X =ᵐ[MeasureTheory.volume] q +ᵥ X) :
    q +ᵥ H = H := by
  have hShiftTile : LineTilesOn B (q +ᵥ H) X :=
    lineTilesOn_target_congr hTarget.2.1 hXperiod.symm
      (lineTilesOn_translate hTarget q)
  have hShiftSub : q +ᵥ H ⊆ L := by
    intro x hx
    have hxL : x ∈ q +ᵥ L := by
      obtain ⟨h, hh, rfl⟩ := hx
      exact ⟨h, hsub hh, rfl⟩
    rwa [hLperiod] at hxL
  exact (lineSubtilings_unique hBpositive hWhole hShiftSub hsub
    hShiftTile hTarget)

set_option linter.unusedVariables true

end Tiling.AxisParallel.Foundations
