import Tiling.Geometry.PolygonalCarrier
import Tiling.Topology.LocallyFellMatching
import Mathlib.Topology.Metrizable.Basic

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology

noncomputable section

namespace Tiling.Topology

theorem boundaryLocallyStraightAt_of_disjoint_moving_packings
    (K : Tiling.RationalPolygonal.PolygonalRegion)
    {U : Set Plane} {Un : ℕ → Set Plane} {x : Plane}
    (hpacking : ∀ n, IsPacking K.prototileFamily (K.placements (Un n)))
    (hconv : LocallyFellConverges Un U)
    (hdisjoint : ∀ᶠ n in atTop, Disjoint (Un n) U)
    (hequal : ∀ᶠ n in atTop,
      Tiling.Polygonal.regularSupport K (Un n) =ᶠ[𝓝 x]
        Tiling.Polygonal.regularSupport K U)
    (hx : x ∈ frontier (Tiling.Polygonal.regularSupport K U)) :
    BoundaryLocallyStraightAt (Tiling.Polygonal.regularSupport K U) x := by
  classical
  let V := vertexSet K.support
  have hVfinite : V.Finite := K.isPolygonal.vertexSet_finite
  have heventual : ∀ᶠ n in atTop, x ∉ V + Un n := by
    have hfinite : ∀ v ∈ V, ∀ᶠ n in atTop, x - v ∉ Un n := by
      intro v hv
      by_cases hmem : x - v ∈ U
      · filter_upwards [hdisjoint] with n hdisj
        intro hxn
        exact (Set.disjoint_left.mp hdisj) hxn hmem
      · have havoid := locallyFellConverges_eventually_disjoint_compact hconv
          isCompact_singleton (by
            rw [Set.disjoint_left]
            intro z hzU hzq
            have hz : z = x - v := Set.mem_singleton_iff.mp hzq
            subst z
            exact hmem hzU)
        filter_upwards [havoid] with n hdisj hxn
        exact (Set.disjoint_left.mp hdisj) hxn rfl
    filter_upwards [(hVfinite.eventually_all).2 hfinite] with n hn
    intro h
    obtain ⟨v, hv, u, hu, hxu⟩ := (Set.mem_add.mp h)
    have : x - v ∈ Un n := by
      have hvu : x - v = u := by calc
        x - v = (v + u) - v := by rw [hxu]
        _ = u := by abel
      simpa [hvu] using hu
    exact hn v hv this
  by_contra hnot
  -- The germ statement yields proper-vertex provenance for every sufficiently late packing.
  have hgood : ∀ᶠ n in atTop,
      x ∈ Tiling.Polygonal.properVertices
        (Tiling.Polygonal.regularSupport K (Un n)) := by
    filter_upwards [hequal] with n hn
    have hproper : Tiling.Polygonal.IsProperVertex
        (Tiling.Polygonal.regularSupport K (Un n)) x :=
      (Tiling.Polygonal.isProperVertex_iff_of_eventuallyEq hn).2 ⟨hx, hnot⟩
    simpa [Tiling.Polygonal.properVertices] using hproper
  obtain ⟨n, hn⟩ := (heventual.and hgood).exists
  rcases hn with ⟨hn, hvertex⟩
  obtain ⟨v, hv, u, hu, hxu⟩ :=
    Tiling.Polygonal.properVertexProvenance (hpacking n) x hvertex
  apply hn
  apply Set.mem_add.mpr
  exact ⟨v, hv, u, hu, hxu.symm⟩


end Tiling.Topology

namespace Tiling.Polygonal.Topology

open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Topology

structure TilingSpace (K : PolygonalRegion) (E : Set Plane) where
  centres : TopologicalSpace.Closeds Plane
  tilesOn : TilesOn K (centres : Set Plane) E

def TilingSpace.translate {K : PolygonalRegion} {E : Set Plane}
    (g : aePeriodGroup E) (T : TilingSpace K E) : TilingSpace K E where
  centres := ⟨(fun x => x + (g : Plane)) '' (T.centres : Set Plane),
    (Homeomorph.addRight (g : Plane)).isClosed_image.mpr T.centres.isClosed⟩
  tilesOn := by
    let u : Plane := g
    let S : Set Plane := T.centres
    let S' : Set Plane := (fun x => x + u) '' S
    change TilesOn K S' E
    refine ⟨T.tilesOn.1.image (fun x => x + u), ?_, ?_⟩
    · intro p hp q hq hpq
      rcases p with ⟨p, _⟩
      rcases q with ⟨q, _⟩
      change p ∈ S' at hp
      change q ∈ S' at hq
      rcases hp with ⟨s, hs, rfl⟩
      rcases hq with ⟨t, ht, rfl⟩
      have hst : s ≠ t := by
        intro hst
        apply hpq
        simp [hst]
      have had := T.tilesOn.2.1
        (show (s, ()) ∈ K.placements S from hs)
        (show (t, ()) ∈ K.placements S from ht)
        (show (s, ()) ≠ (t, ()) by simpa using hst)
      change AEDisjoint volume (s +ᵥ K.support) (t +ᵥ K.support) at had
      change AEDisjoint volume ((s + u) +ᵥ K.support) ((t + u) +ᵥ K.support)
      rw [MeasureTheory.AEDisjoint] at had ⊢
      rw [show (((s + u) +ᵥ K.support) ∩ ((t + u) +ᵥ K.support)) =
          u +ᵥ ((s +ᵥ K.support) ∩ (t +ᵥ K.support)) by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_vadd_set]
        constructor
        · rintro ⟨⟨a, ha, hax⟩, b, hb, hbx⟩
          refine ⟨-u + x, ⟨?_, ?_⟩, ?_⟩
          · refine ⟨a, ha, ?_⟩
            simp only [vadd_eq_add] at hax ⊢
            rw [← hax]
            abel
          · refine ⟨b, hb, ?_⟩
            simp only [vadd_eq_add] at hbx ⊢
            rw [← hbx]
            abel
          · simp only [vadd_eq_add]
            abel
        · rintro ⟨y, ⟨⟨a, ha, hay⟩, b, hb, hby⟩, hyx⟩
          constructor
          · refine ⟨a, ha, ?_⟩
            simp only [vadd_eq_add] at hay hyx ⊢
            calc
              s + u + a = u + (s + a) := by abel
              _ = u + y := by rw [hay]
              _ = x := hyx
          · refine ⟨b, hb, ?_⟩
            simp only [vadd_eq_add] at hby hyx ⊢
            calc
              t + u + b = u + (t + b) := by abel
              _ = u + y := by rw [hby]
              _ = x := hyx]
      simpa only [MeasureTheory.measure_vadd] using had
    · have hcover :=
        (MeasureTheory.quasiMeasurePreserving_add_right volume (-u)).ae T.tilesOn.2.2
      have hcarrier : (u +ᵥ E : Set Plane) =ᵐ[volume] E := g.property
      filter_upwards [hcover, hcarrier] with x hxcover hxcarrier
      have hcarrier' : x ∈ E ↔ x - u ∈ E := by
        constructor
        · intro hx
          have hx' : x ∈ u +ᵥ E := hxcarrier.mpr hx
          rcases hx' with ⟨y, hy, hyx⟩
          have hxy : x - u = y := by
            simp only [vadd_eq_add] at hyx
            rw [← hyx]
            abel
          rwa [hxy]
        · intro hx
          apply hxcarrier.mp
          refine ⟨x - u, hx, ?_⟩
          simp only [vadd_eq_add]
          abel
      have hxcover' : x - u ∈ E ↔
          ∃ s : S, x - u ∈ (s : Plane) +ᵥ K.openCarrier := by
        simpa only [sub_eq_add_neg] using hxcover
      rw [hcarrier', hxcover']
      constructor
      · rintro ⟨s, hs⟩
        rcases hs with ⟨y, hy, hyx⟩
        refine ⟨⟨s + u, ⟨s, s.2, rfl⟩⟩, ?_⟩
        refine ⟨y, hy, ?_⟩
        simp only [vadd_eq_add] at hyx ⊢
        calc
          (s : Plane) + u + y = ((s : Plane) + y) + u := by abel
          _ = (x - u) + u := by rw [hyx]
          _ = x := sub_add_cancel x u
      · rintro ⟨s, hs⟩
        rcases s.2 with ⟨t, ht, hts⟩
        change t + u = (s : Plane) at hts
        rcases hs with ⟨y, hy, hyx⟩
        refine ⟨⟨t, ht⟩, y, hy, ?_⟩
        simp only [vadd_eq_add] at hyx ⊢
        calc
          t + y = (t + u + y) - u := by abel
          _ = ((s : Plane) + y) - u := by rw [hts]
          _ = x - u := by rw [hyx]


instance TilingSpace.instAddAction (K : PolygonalRegion) (E : Set Plane) :
    AddAction (aePeriodGroup E) (TilingSpace K E) where
  vadd := TilingSpace.translate
  zero_vadd T := by
    cases T with
    | mk centres tilesOn =>
        change TilingSpace.translate (0 : aePeriodGroup E)
          ⟨centres, tilesOn⟩ = ⟨centres, tilesOn⟩
        rw [TilingSpace.mk.injEq]
        apply TopologicalSpace.Closeds.ext
        ext x
        change x ∈ (fun y : Plane => y + 0) '' (centres : Set Plane) ↔
          x ∈ (centres : Set Plane)
        simp
  add_vadd g h T := by
    cases T with
    | mk centres tilesOn =>
        change TilingSpace.translate (g + h) ⟨centres, tilesOn⟩ =
          TilingSpace.translate g (TilingSpace.translate h ⟨centres, tilesOn⟩)
        rw [TilingSpace.mk.injEq]
        apply TopologicalSpace.Closeds.ext
        ext x
        change x ∈ (fun y : Plane => y + ((g + h :
            aePeriodGroup E) : Plane)) ''
              (centres : Set Plane) ↔
          x ∈ (fun y : Plane => y + (g : Plane)) ''
            ((fun y : Plane => y + (h : Plane)) ''
              (centres : Set Plane))
        constructor
        · rintro ⟨y, hy, rfl⟩
          refine ⟨y + (h : Plane), ⟨y, hy, rfl⟩, ?_⟩
          rw [AddSubgroup.coe_add]
          abel_nf
        · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
          refine ⟨y, hy, ?_⟩
          rw [AddSubgroup.coe_add]
          simp only [add_left_comm, add_comm]

instance TilingSpace.instMetricSpace (K : PolygonalRegion) (E : Set Plane) :
    MetricSpace (TilingSpace K E) := by
  letI : MetricSpace (OnePoint Plane) := by
    let e : OnePoint Plane ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      onePointEquivSphereOfFinrankEq (ι := Fin 3) (V := Plane) (by
        norm_num [Plane, Complex.finrank_real_complex])
    exact e.isEmbedding.comapMetricSpace
  let embedding : TilingSpace K E → TopologicalSpace.NonemptyCompacts (OnePoint Plane) :=
    fun T => Tiling.Topology.fellCompactification
      (T.centres : Set Plane) T.centres.isClosed
  exact MetricSpace.induced embedding (by
    intro T U h
    have hc : T.centres = U.centres := by
      apply TopologicalSpace.Closeds.ext
      ext x
      have hx := congrArg
        (fun C : TopologicalSpace.NonemptyCompacts (OnePoint Plane) =>
          (x : OnePoint Plane) ∈ (C : Set (OnePoint Plane))) h
      simpa [embedding, Tiling.Topology.fellCompactification] using hx
    cases T
    cases U
    simp_all) inferInstance

def orbitHull {K : PolygonalRegion} {E : Set Plane} (T : TilingSpace K E) :
    Set (TilingSpace K E) := closure (AddAction.orbit (aePeriodGroup E) T)

def IsTopologicallyMinimal {K : PolygonalRegion} {E : Set Plane}
    (Y : Set (TilingSpace K E)) : Prop :=
  Y.Nonempty ∧ IsClosed Y ∧
    (∀ g : aePeriodGroup E, TilingSpace.translate g '' Y = Y) ∧
    ∀ T ∈ Y, orbitHull T = Y

def IsMinimalTiling (K : PolygonalRegion) (S E : Set Plane) : Prop :=
  ∃ T : TilingSpace K E, (T.centres : Set Plane) = S ∧
    IsTopologicallyMinimal (orbitHull T)

private theorem isPacking_of_locallyFellConverges
    {K : PolygonalRegion}
    {A : ℕ → Set Plane} {L : Set Plane}
    (hA : ∀ n, Tiling.IsPacking K.prototileFamily
      (K.placements (A n)))
    (hconv : Tiling.Topology.LocallyFellConverges A L) :
    Tiling.IsPacking K.prototileFamily
      (K.placements L) := by
  rw [isPacking_iff_openCarrier_disjoint]
  intro s hsL t htL hst
  rw [Set.disjoint_left]
  intro x hxs hxt
  let U : Set Plane := {c | x - c ∈ K.openCarrier}
  have hUopen : IsOpen U :=
    isOpen_interior.preimage (continuous_const.sub continuous_id)
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
  let epsilon := min rs (min rt (dist s t / 3))
  have hdist : 0 < dist s t := dist_pos.mpr hst
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact lt_min hrs (lt_min hrt (by positivity))
  have heps_rs : epsilon ≤ rs := min_le_left _ _
  have heps_rt : epsilon ≤ rt := (min_le_right _ _).trans (min_le_left _ _)
  have heps_dist : epsilon ≤ dist s t / 3 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsEventually :=
    locallyFellConverges_eventually_exists_mem_ball hconv hsL hepsilon
  have htEventually :=
    locallyFellConverges_eventually_exists_mem_ball hconv htL hepsilon
  obtain ⟨n, ⟨s', hs'A, hs'dist⟩, ⟨t', ht'A, ht'dist⟩⟩ :=
    (hsEventually.and htEventually).exists
  have hs'U : s' ∈ U := hrsU (by
    rw [Metric.mem_ball]
    exact hs'dist.trans_le heps_rs)
  have ht'U : t' ∈ U := hrtU (by
    rw [Metric.mem_ball]
    exact ht'dist.trans_le heps_rt)
  have hs't' : s' ≠ t' := by
    intro heq
    subst t'
    have htriangle : dist s t ≤ dist s s' + dist s' t := dist_triangle _ _ _
    rw [dist_comm s s'] at htriangle
    have hsBound : dist s' s < dist s t / 3 := hs'dist.trans_le heps_dist
    have htBound : dist s' t < dist s t / 3 := ht'dist.trans_le heps_dist
    linarith
  have hdisjoint :=
    (isPacking_iff_openCarrier_disjoint K (A n)).mp
      (hA n) hs'A ht'A hs't'
  apply Set.disjoint_left.mp hdisjoint
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [vadd_eq_add, U, Set.mem_ofPred_eq, sub_eq_add_neg,
      add_comm] using hs'U
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [vadd_eq_add, U, Set.mem_ofPred_eq, sub_eq_add_neg,
      add_comm] using ht'U


theorem tilesOn_isClosed {K : PolygonalRegion} {E : Set Plane}
    {T : ℕ → Set Plane} {L : Set Plane} (hT : ∀ n, TilesOn K (T n) E)
    (hconv : Tiling.Topology.LocallyFellConverges T L) : TilesOn K L E := by
  have hPacking : Tiling.IsPacking K.prototileFamily
      (K.placements L) :=
    isPacking_of_locallyFellConverges (fun n ↦ (hT n).2.1) hconv
  have hLocal := packing_centres_locallyFinite hPacking
  let _ : Countable ↥L := hLocal.2.1.to_subtype
  have hBoundaryNull : MeasureTheory.volume
      (⋃ s : L, (s.1 : Plane) +ᵥ frontier K.support) = 0 := by
    apply measure_iUnion_null
    intro s
    simpa only [MeasureTheory.measure_vadd] using K.isPolygonal.volume_frontier
  have hNoBoundary : ∀ᵐ x : Plane ∂MeasureTheory.volume,
      x ∉ ⋃ s : L, (s.1 : Plane) +ᵥ frontier K.support :=
    measure_eq_zero_iff_ae_notMem.mp hBoundaryNull
  have hEveryTarget : ∀ᵐ x : Plane ∂MeasureTheory.volume,
      ∀ n : ℕ, (x ∈ E ↔ ∃ s : T n,
        x ∈ ((s : Plane) +ᵥ K.openCarrier)) :=
    ae_all_iff.mpr fun n ↦ (hT n).2.2
  refine ⟨hLocal.2.1, hPacking, ?_⟩
  filter_upwards [hEveryTarget, hNoBoundary] with x hxTarget hxBoundary
  constructor
  · intro hxE
    by_contra hxOpen
    let C : Set Plane :=
      (fun y : Plane ↦ x - y) '' K.support
    have hCcompact : IsCompact C :=
      K.isPolygonal.isCompact.image (continuous_const.sub continuous_id)
    have hLC : Disjoint L C := by
      rw [Set.disjoint_left]
      intro l hlL hlC
      rcases hlC with ⟨y, hyK, hyl⟩
      change x - y = l at hyl
      have hxy : x - l = y := by
        calc
          x - l = x - (x - y) := by rw [hyl]
          _ = y := sub_sub_cancel x y
      by_cases hyInterior : y ∈ interior K.support
      · apply hxOpen
        refine ⟨⟨l, hlL⟩, ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simp only [vadd_eq_add]
        rw [add_comm, ← sub_eq_add_neg, hxy]
        simpa only [PolygonalRegion.openCarrier] using hyInterior
      · have hyFrontier : y ∈ frontier K.support :=
          (mem_frontier_iff_notMem_interior hyK).mpr hyInterior
        apply hxBoundary
        rw [Set.mem_iUnion]
        refine ⟨⟨l, hlL⟩, ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simp only [vadd_eq_add]
        rw [add_comm, ← sub_eq_add_neg, hxy]
        exact hyFrontier
    have hEventually := locallyFellConverges_eventually_disjoint_compact
      hconv hCcompact hLC
    obtain ⟨n, hn⟩ := hEventually.exists
    obtain ⟨s, hsCover⟩ := (hxTarget n).mp hxE
    have hsC : (s : Plane) ∈ C := by
      refine ⟨x - (s : Plane), ?_, ?_⟩
      · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsCover
        simp only [vadd_eq_add] at hsCover
        exact interior_subset (by
          simpa only [PolygonalRegion.openCarrier,
            sub_eq_add_neg, add_comm] using hsCover)
      · abel_nf
    exact Set.disjoint_left.mp hn s.2 hsC
  · intro hxOpen
    change ∃ s : L, x ∈ (s : Plane) +ᵥ K.openCarrier at hxOpen
    obtain ⟨s, hsOpen⟩ := hxOpen
    let U : Set Plane := {c | x - c ∈ K.openCarrier}
    have hUopen : IsOpen U :=
      isOpen_interior.preimage (continuous_const.sub continuous_id)
    have hsU : (s : Plane) ∈ U := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsOpen
      simp only [vadd_eq_add] at hsOpen
      simpa only [U, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm] using hsOpen
    obtain ⟨epsilon, hepsilon, hballU⟩ :=
      Metric.mem_nhds_iff.mp (hUopen.mem_nhds hsU)
    have hEventually := locallyFellConverges_eventually_exists_mem_ball
      hconv s.2 hepsilon
    obtain ⟨n, y, hyT, hydist⟩ := hEventually.exists
    apply (hxTarget n).mpr
    refine ⟨⟨y, hyT⟩, ?_⟩
    have hyU : y ∈ U := hballU (Metric.mem_ball.mpr hydist)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [vadd_eq_add]
    simpa only [U, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm] using hyU

theorem locallyFell_metrizable (K : PolygonalRegion) (E : Set Plane)
    (T : ℕ → TilingSpace K E) (L : TilingSpace K E) :
    Tendsto T atTop (𝓝 L) ↔
      Tiling.Topology.LocallyFellConverges
        (fun n => ((T n).centres : Set Plane)) (L.centres : Set Plane) := by
  let compactify : TilingSpace K E →
      TopologicalSpace.NonemptyCompacts (OnePoint Plane) := fun U =>
    Tiling.Topology.fellCompactification
      (U.centres : Set Plane) U.centres.isClosed
  have hcompactify : Continuous compactify := by
    exact continuous_induced_dom
  constructor
  · intro hT
    refine ⟨fun n ↦ (T n).centres.isClosed, L.centres.isClosed, ?_⟩
    have h := (hcompactify.tendsto L).comp hT
    simpa [compactify, Function.comp_def] using h
  · rintro ⟨hclosedT, hclosedL, hT⟩
    have hT' : Filter.Tendsto (compactify ∘ T) Filter.atTop
        (nhds (compactify L)) := by
      simpa [compactify, Function.comp_def] using hT
    rw [show nhds L = Filter.comap compactify (nhds (compactify L)) by
      exact nhds_induced compactify L]
    exact (Filter.tendsto_comap_iff.mpr hT')

theorem tilingSpace_compact (K : PolygonalRegion) (E : Set Plane) :
    IsCompact (univ : Set (TilingSpace K E)) := by
  rw [isCompact_iff_isSeqCompact]
  intro U _hU
  let centres : ℕ → Set Plane := fun n ↦ (U n).centres
  obtain ⟨δ, hδ, hsep⟩ := exists_packingSeparation K
  obtain ⟨φ, L, hφ, hclosed, _hsepL, hconv⟩ :=
    Tiling.Topology.exists_locallyFellConvergent_subsequence δ hδ centres
      (fun n => (U n).centres.isClosed) (fun n => hsep _ (U n).tilesOn.2.1)
  let V : TilingSpace K E := ⟨⟨L, hclosed⟩,
    tilesOn_isClosed (fun n => (U (φ n)).tilesOn) hconv⟩
  refine ⟨V, Set.mem_univ V, φ, hφ, ?_⟩
  exact (locallyFell_metrizable K E (U ∘ φ) V).mpr hconv


theorem translationAction_continuous (K : PolygonalRegion) (E : Set Plane) :
    Continuous (fun p : aePeriodGroup E × TilingSpace K E =>
      TilingSpace.translate p.1 p.2) := by
  rw [continuous_iff_seqContinuous]
  intro p q hpq
  apply (locallyFell_metrizable K E _ _).mpr
  have hcentres := (locallyFell_metrizable K E (fun n => (p n).2) q.2).mp
    ((continuous_snd.tendsto q).comp hpq)
  have hperiods : Tendsto (fun n => ((p n).1 : Plane)) atTop (𝓝 (q.1 : Plane)) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto q).comp hpq
  have h := Tiling.Topology.locallyFell_translate hcentres hperiods
  have heq (g : aePeriodGroup E) (T : TilingSpace K E) :
      (TilingSpace.translate g T).centres = (g : Plane) +ᵥ (T.centres : Set Plane) := by
    change (fun x => x + (g : Plane)) '' (T.centres : Set Plane) =
      (g : Plane) +ᵥ (T.centres : Set Plane)
    ext x
    simp only [mem_image, mem_vadd_set, vadd_eq_add]
    constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, add_comm _ _⟩
  simpa only [Function.comp_apply, heq] using h


private theorem tilingSpace_translate_continuous
    {K : PolygonalRegion} {E : Set Plane} (g : aePeriodGroup E) :
    Continuous (TilingSpace.translate g : TilingSpace K E → TilingSpace K E) :=
  (translationAction_continuous K E).comp (continuous_const.prodMk continuous_id)

theorem orbitHull_compact {K : PolygonalRegion} {E : Set Plane}
    (T : TilingSpace K E) :
    IsCompact (orbitHull T) ∧ (orbitHull T).Nonempty ∧
      ∀ g : aePeriodGroup E, TilingSpace.translate g '' orbitHull T = orbitHull T := by
  let G := aePeriodGroup E
  let X := TilingSpace K E
  have hcompact : IsCompact (orbitHull T) :=
    (tilingSpace_compact K E).of_isClosed_subset isClosed_closure (subset_univ _)
  have hnonempty : (orbitHull T).Nonempty :=
    ⟨T, subset_closure (AddAction.mem_orbit_self T)⟩
  refine ⟨hcompact, hnonempty, fun g ↦ ?_⟩
  let e : X ≃ₜ X := {
    toFun := TilingSpace.translate g
    invFun := TilingSpace.translate (-g)
    left_inv U := by
      change (-g) +ᵥ (g +ᵥ U) = U
      rw [← add_vadd]
      simp
    right_inv U := by
      change g +ᵥ ((-g) +ᵥ U) = U
      rw [← add_vadd]
      simp
    continuous_toFun := tilingSpace_translate_continuous g
    continuous_invFun := tilingSpace_translate_continuous (-g)
  }
  change e '' closure (AddAction.orbit G T) =
    closure (AddAction.orbit G T)
  rw [e.image_closure]
  congr 1
  change g +ᵥ AddAction.orbit G T = AddAction.orbit G T
  exact AddAction.vadd_orbit g T

theorem exists_minimalInvariantSubset {K : PolygonalRegion} {E : Set Plane}
    (T : TilingSpace K E) :
    ∃ Y : Set (TilingSpace K E), Y ⊆ orbitHull T ∧ IsTopologicallyMinimal Y := by
  let G := aePeriodGroup E
  let X := TilingSpace K E
  let H : Set X := orbitHull T
  let admissible : Set (Set X) :=
    {Y | Y ⊆ H ∧ Y.Nonempty ∧ IsClosed Y ∧
      ∀ g : G, TilingSpace.translate g '' Y = Y}
  have hHcompact : IsCompact H := orbitHull_compact T |>.1
  have hHadmissible : H ∈ admissible := by
    exact ⟨Subset.rfl, (orbitHull_compact T).2.1, isClosed_closure,
      (orbitHull_compact T).2.2⟩
  obtain ⟨Y, hYH, hYminimal⟩ := zorn_superset_nonempty admissible (by
    intro c hc hchain hcne
    refine ⟨⋂₀ c, ?_, fun S hS ↦ Set.sInter_subset_of_mem hS⟩
    have hsubset : ⋂₀ c ⊆ H := by
      obtain ⟨S, hS⟩ := hcne
      exact (Set.sInter_subset_of_mem hS).trans (hc hS).1
    have hnonempty : (⋂₀ c : Set X).Nonempty := by
      let _ : Nonempty ↥c := hcne.to_subtype
      rw [Set.sInter_eq_iInter]
      apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      · exact DirectedOn.directed_val (IsChain.directedOn hchain.symm)
      · intro S
        exact (hc S.2).2.1
      · intro S
        exact hHcompact.of_isClosed_subset (hc S.2).2.2.1 (hc S.2).1
      · intro S
        exact (hc S.2).2.2.1
    have hclosed : IsClosed (⋂₀ c : Set X) :=
      isClosed_sInter fun S hS ↦ (hc hS).2.2.1
    have hinvariant (g : G) :
        TilingSpace.translate g '' (⋂₀ c : Set X) =
          ⋂₀ c := by
      apply Set.Subset.antisymm
      · rintro _ ⟨U, hU, rfl⟩
        rw [Set.mem_sInter]
        intro S hS
        have hmem : TilingSpace.translate g U ∈
            TilingSpace.translate g '' S :=
          ⟨U, Set.mem_sInter.mp hU S hS, rfl⟩
        rwa [(hc hS).2.2.2 g] at hmem
      · intro U hU
        let V : X := TilingSpace.translate (-g) U
        have hV : V ∈ ⋂₀ c := by
          rw [Set.mem_sInter]
          intro S hS
          have hmem : TilingSpace.translate (-g) U ∈
              TilingSpace.translate (-g) '' S :=
            ⟨U, Set.mem_sInter.mp hU S hS, rfl⟩
          rwa [(hc hS).2.2.2 (-g)] at hmem
        refine ⟨V, hV, ?_⟩
        change g +ᵥ ((-g) +ᵥ U) = U
        rw [← add_vadd]
        simp
    exact ⟨hsubset, hnonempty, hclosed, hinvariant⟩) H hHadmissible
  have hYdata := (minimal_iff.mp hYminimal).1
  refine ⟨Y, hYdata.1, ?_⟩
  refine ⟨hYdata.2.1, hYdata.2.2.1, hYdata.2.2.2, ?_⟩
  intro U hUY
  let Z : Set X := orbitHull U
  have hZY : Z ⊆ Y := by
    apply closure_minimal
    · rintro V ⟨g, rfl⟩
      have hmem : TilingSpace.translate g U ∈
          TilingSpace.translate g '' Y :=
        ⟨U, hUY, rfl⟩
      rwa [hYdata.2.2.2 g] at hmem
    · exact hYdata.2.2.1
  have hZadmissible : Z ∈ admissible := by
    refine ⟨hZY.trans hYdata.1, (orbitHull_compact U).2.1,
      isClosed_closure, (orbitHull_compact U).2.2⟩
  exact ((minimal_iff.mp hYminimal).2 hZadmissible hZY).symm

theorem exists_minimalTiling_in_hull {K : PolygonalRegion} {E : Set Plane}
    (T : TilingSpace K E) :
    ∃ U ∈ orbitHull T, IsTopologicallyMinimal (orbitHull U) := by
  obtain ⟨Y, hYH, hY⟩ := exists_minimalInvariantSubset T
  obtain ⟨U, hUY⟩ := hY.1
  exact ⟨U, hYH hUY, (hY.2.2.2 U hUY) ▸ hY⟩

private theorem translate_centres {K : PolygonalRegion} {E : Set Plane}
    (g : aePeriodGroup E) (T : TilingSpace K E) :
    ((TilingSpace.translate g T).centres : Set Plane) =
      (g : Plane) +ᵥ (T.centres : Set Plane) := by
  change (fun x => x + (g : Plane)) '' (T.centres : Set Plane) =
    (g : Plane) +ᵥ (T.centres : Set Plane)
  ext x
  simp only [mem_image, mem_vadd_set, vadd_eq_add]
  constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, add_comm _ _⟩

private theorem mem_orbitHull_iff_sequence {K : PolygonalRegion} {E : Set Plane}
    (T U : TilingSpace K E) :
    U ∈ orbitHull T ↔ ∃ g : ℕ → aePeriodGroup E,
      LocallyFellConverges (fun n => (g n : Plane) +ᵥ (T.centres : Set Plane))
        (U.centres : Set Plane) := by
  constructor
  · intro hU
    obtain ⟨V, hV, hlim⟩ := mem_closure_iff_seq_limit.mp hU
    choose g hg using hV
    refine ⟨g, ?_⟩
    have heq : (fun n => TilingSpace.translate (g n) T) = V := by
      funext n
      exact hg n
    have h := (locallyFell_metrizable K E _ U).mp (heq.symm ▸ hlim)
    simpa only [translate_centres] using h
  · rintro ⟨g, hconv⟩
    have hlim : Tendsto (fun n => TilingSpace.translate (g n) T) atTop (𝓝 U) :=
      (locallyFell_metrizable K E _ U).mpr (by
        simpa only [translate_centres] using hconv)
    exact isClosed_closure.mem_of_tendsto hlim
      (Eventually.of_forall fun n => subset_closure ⟨g n, rfl⟩)

private theorem orbitHull_subset_of_mem {K : PolygonalRegion} {E : Set Plane}
    {T U : TilingSpace K E} (hU : U ∈ orbitHull T) :
    orbitHull U ⊆ orbitHull T := by
  apply closure_minimal
  · rintro V ⟨g, rfl⟩
    have hm : TilingSpace.translate g U ∈ TilingSpace.translate g '' orbitHull T :=
      ⟨U, hU, rfl⟩
    rwa [(orbitHull_compact T).2.2 g] at hm
  · exact isClosed_closure

theorem isMinimalTiling_iff_returnSequences
    (K : PolygonalRegion) (S E : Set Plane) (hS : TilesOn K S E) :
    IsMinimalTiling K S E ↔
      ∀ L : Set Plane, (∃ g : ℕ → aePeriodGroup E,
        Tiling.Topology.LocallyFellConverges (fun n => (g n : Plane) +ᵥ S) L) →
        ∃ h : ℕ → aePeriodGroup E,
          Tiling.Topology.LocallyFellConverges (fun n => (h n : Plane) +ᵥ L) S := by
  constructor
  · rintro ⟨T, hTS, hminimal⟩ L ⟨g, hconv⟩
    have htiles : TilesOn K L E := tilesOn_isClosed
      (fun n => (TilingSpace.translate (g n) T).tilesOn) (by
        simpa only [translate_centres, hTS] using hconv)
    let U : TilingSpace K E :=
      ⟨⟨L, (packing_centres_locallyFinite htiles.2.1).2.2⟩, htiles⟩
    have hUH : U ∈ orbitHull T :=
      (mem_orbitHull_iff_sequence T U).mpr ⟨g, by simpa only [hTS, U,
        TopologicalSpace.Closeds.coe_mk] using hconv⟩
    have hTH : T ∈ orbitHull U := by
      rw [hminimal.2.2.2 U hUH]
      exact subset_closure (AddAction.mem_orbit_self T)
    obtain ⟨h, hh⟩ := (mem_orbitHull_iff_sequence U T).mp hTH
    exact ⟨h, by simpa only [hTS, U, TopologicalSpace.Closeds.coe_mk] using hh⟩
  · intro hreturn
    let T : TilingSpace K E :=
      ⟨⟨S, (packing_centres_locallyFinite hS.2.1).2.2⟩, hS⟩
    refine ⟨T, rfl, (orbitHull_compact T).2.1, isClosed_closure,
      (orbitHull_compact T).2.2, ?_⟩
    intro U hUH
    obtain ⟨g, hg⟩ := (mem_orbitHull_iff_sequence T U).mp hUH
    obtain ⟨h, hh⟩ := hreturn (U.centres : Set Plane) ⟨g, hg⟩
    have hTH : T ∈ orbitHull U := (mem_orbitHull_iff_sequence U T).mpr ⟨h, hh⟩
    exact (orbitHull_subset_of_mem hUH).antisymm (orbitHull_subset_of_mem hTH)


theorem hasFLC_of_mem_orbitHull {K : PolygonalRegion} {E : Set Plane}
    {T U : TilingSpace K E} (hT : HasFLC (T.centres : Set Plane))
    (hU : U ∈ orbitHull T) : HasFLC (U.centres : Set Plane) := by
  obtain ⟨g, hconv⟩ := (mem_orbitHull_iff_sequence T U).mp hU
  exact hT.locallyFell_limit_of_translates hconv

private theorem linearImage_vadd (A : Plane ≃L[ℝ] Plane) (u : Plane) (S : Set Plane) :
    A '' (u +ᵥ S) = A u +ᵥ (A '' S) := by
  ext x
  simp only [mem_image, mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨A y, ⟨y, hy, rfl⟩, (map_add A u y).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨u + y, ⟨y, hy, rfl⟩, map_add A u y⟩

private theorem affineImage_vadd (A : Plane ≃L[ℝ] Plane) (a u : Plane) (S : Set Plane) :
    affineMap A a '' (u +ᵥ S) = A u +ᵥ (affineMap A a '' S) := by
  ext x
  simp only [mem_image, mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨affineMap A a y, ⟨y, hy, rfl⟩, ?_⟩
    simp only [affineMap, map_add]
    abel
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨u + y, ⟨y, hy, rfl⟩, ?_⟩
    simp only [affineMap, map_add]
    abel

private theorem aePeriod_affine_iff (A : Plane ≃L[ℝ] Plane) (a : Plane)
    (E : Set Plane) (u : Plane) :
    A u ∈ aePeriodGroup (affineMap A a '' E) ↔ u ∈ aePeriodGroup E := by
  change (A u +ᵥ (affineMap A a '' E)) =ᵐ[volume] (affineMap A a '' E) ↔
    (u +ᵥ E) =ᵐ[volume] E
  rw [← affineImage_vadd]
  have hinj : Injective (affineMap A a) := by
    intro x y h
    exact A.injective (add_left_cancel h)
  rw [← measure_symmDiff_eq_zero_iff, ← measure_symmDiff_eq_zero_iff,
    ← Set.image_symmDiff hinj]
  exact volume_affineImage_eq_zero_iff A a _

private theorem returnSequences_linearImage
    (A : Plane ≃L[ℝ] Plane) (a : Plane) (S E : Set Plane)
    (hreturn : ∀ L : Set Plane, (∃ g : ℕ → aePeriodGroup E,
      LocallyFellConverges (fun n => (g n : Plane) +ᵥ S) L) →
      ∃ h : ℕ → aePeriodGroup E,
        LocallyFellConverges (fun n => (h n : Plane) +ᵥ L) S) :
    ∀ L : Set Plane, (∃ g : ℕ → aePeriodGroup (affineMap A a '' E),
      LocallyFellConverges (fun n => (g n : Plane) +ᵥ (A '' S)) L) →
      ∃ h : ℕ → aePeriodGroup (affineMap A a '' E),
        LocallyFellConverges (fun n => (h n : Plane) +ᵥ L) (A '' S) := by
  rintro L ⟨g, hg⟩
  let g₀ : ℕ → aePeriodGroup E := fun n =>
    ⟨A.symm (g n : Plane), (aePeriod_affine_iff A a E _).mp (by
      simpa only [A.apply_symm_apply] using (g n).property)⟩
  have hg₀ : LocallyFellConverges (fun n => (g₀ n : Plane) +ᵥ S) (A.symm '' L) := by
    have h := (locallyFell_linearImage_iff A.symm _ _).mpr hg
    simpa only [linearImage_vadd, Set.image_image, Function.comp_def,
      A.symm_apply_apply, Set.image_id', g₀] using h
  obtain ⟨h₀, hh₀⟩ := hreturn _ ⟨g₀, hg₀⟩
  let h : ℕ → aePeriodGroup (affineMap A a '' E) := fun n =>
    ⟨A (h₀ n : Plane), (aePeriod_affine_iff A a E _).mpr (h₀ n).property⟩
  refine ⟨h, ?_⟩
  have hh := (locallyFell_linearImage_iff A _ _).mpr hh₀
  simpa only [linearImage_vadd, Set.image_image, Function.comp_def,
    A.apply_symm_apply, Set.image_id', h] using hh

private theorem returnSequences_linearImage_iff
    (A : Plane ≃L[ℝ] Plane) (a : Plane) (S E : Set Plane) :
    (∀ L : Set Plane, (∃ g : ℕ → aePeriodGroup (affineMap A a '' E),
      LocallyFellConverges (fun n => (g n : Plane) +ᵥ (A '' S)) L) →
      ∃ h : ℕ → aePeriodGroup (affineMap A a '' E),
        LocallyFellConverges (fun n => (h n : Plane) +ᵥ L) (A '' S)) ↔
    (∀ L : Set Plane, (∃ g : ℕ → aePeriodGroup E,
      LocallyFellConverges (fun n => (g n : Plane) +ᵥ S) L) →
      ∃ h : ℕ → aePeriodGroup E,
        LocallyFellConverges (fun n => (h n : Plane) +ᵥ L) S) := by
  refine ⟨fun h => ?_, returnSequences_linearImage A a S E⟩
  have hback := returnSequences_linearImage A.symm (-A.symm a)
    (A '' S) (affineMap A a '' E) h
  have hE : affineMap A.symm (-A.symm a) '' (affineMap A a '' E) = E := by
    rw [Set.image_image]
    have hf : affineMap A.symm (-A.symm a) ∘ affineMap A a = id := by
      funext x
      simp [affineMap, map_add]
    change (affineMap A.symm (-A.symm a) ∘ affineMap A a) '' E = E
    rw [hf, Set.image_id]
  rw [hE] at hback
  simpa only [Set.image_image, Function.comp_def,
    A.symm_apply_apply, Set.image_id'] using hback

theorem isMinimalTiling_affineImage_iff
    (K : PolygonalRegion) (A : Plane ≃L[ℝ] Plane) (a : Plane) (S E : Set Plane) :
    IsMinimalTiling (affineImage K A a) (A '' S) (affineMap A a '' E) ↔
      IsMinimalTiling K S E := by
  constructor
  · intro hminimal
    obtain ⟨T, hTS, hm⟩ := hminimal
    have hminimal' : IsMinimalTiling (affineImage K A a) (A '' S)
        (affineMap A a '' E) := ⟨T, hTS, hm⟩
    have hS' : TilesOn (affineImage K A a) (A '' S) (affineMap A a '' E) :=
      hTS ▸ T.tilesOn
    have hS := (tilesOn_affineImage_iff K A a S E).mp hS'
    apply (isMinimalTiling_iff_returnSequences K S E hS).mpr
    exact (returnSequences_linearImage_iff A a S E).mp
      ((isMinimalTiling_iff_returnSequences _ _ _ hS').mp hminimal')
  · intro hminimal
    obtain ⟨T, hTS, hm⟩ := hminimal
    have hminimal' : IsMinimalTiling K S E := ⟨T, hTS, hm⟩
    have hS : TilesOn K S E := hTS ▸ T.tilesOn
    have hS' := (tilesOn_affineImage_iff K A a S E).mpr hS
    apply (isMinimalTiling_iff_returnSequences _ _ _ hS').mpr
    exact (returnSequences_linearImage_iff A a S E).mpr
      ((isMinimalTiling_iff_returnSequences K S E hS).mp hminimal')

theorem latticeRestricted_hull_limit {K : PolygonalRegion} {E : Set Plane}
    {T : TilingSpace K E} {S : Set Plane}
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (g : ℕ → aePeriodGroup E)
    (hconv : Tiling.Topology.LocallyFellConverges (fun n => (g n : Plane) +ᵥ
      (T.centres : Set Plane)) S)
    (L : PlanarLattice) (hL : L.toAddSubgroup ≤ aePeriodGroup E) :
    ∃ (φ : ℕ → ℕ) (ℓ : ℕ → L.toAddSubgroup) (a : aePeriodGroup E),
      StrictMono φ ∧
      Tendsto (fun n => (ℓ n : Plane) - (g (φ n) : Plane)) atTop (𝓝 (a : Plane)) ∧
      Tiling.Topology.LocallyFellConverges
        (fun n => (ℓ n : Plane) +ᵥ (T.centres : Set Plane)) ((a : Plane) +ᵥ S) := by
  classical
  obtain ⟨R, hR, hrep⟩ := planarLattice_boundedCosetRepresentative L
  choose ell hell using fun n => hrep (g n : Plane)
  let d : ℕ → Plane := fun n => (ell n : Plane) - (g n : Plane)
  have hd_bound : ∀ n, d n ∈ Metric.closedBall (0 : Plane) R := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := hell n
    simpa [d, norm_sub_rev] using h.2
  obtain ⟨a, haBall, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (0 : Plane) R).tendsto_subseq hd_bound
  let dφ : ℕ → Plane := d ∘ φ
  have hlim' : Tendsto dφ atTop (𝓝 a) := by
    simpa [dφ] using hlim
  have hperiod : ∀ n, dφ n ∈ (periodGroup E : Set Plane) := by
    intro n
    change (ell (φ n) : Plane) - (g (φ n) : Plane) ∈ _
    have hellmem : (ell (φ n) : Plane) ∈ (aePeriodGroup E : Set Plane) :=
      hL (hell (φ n)).1
    have hgm : (g (φ n) : Plane) ∈ (aePeriodGroup E : Set Plane) := (g (φ n)).property
    have hdiff : (ell (φ n) : Plane) - (g (φ n) : Plane) ∈
        (aePeriodGroup E : Set Plane) := (aePeriodGroup E).sub_mem hellmem hgm
    have heq := aePeriodGroup_eq_periodGroup_of_regularOpen hEopen hEregular
    simpa [heq, dφ, d] using hdiff
  have hclosed : IsClosed (periodGroup E : Set Plane) :=
    isClosed_periodGroup_of_regularOpen hEopen hEregular
  have hamem : (a : Plane) ∈ (periodGroup E : Set Plane) :=
    hclosed.mem_of_tendsto hlim' (Filter.Eventually.of_forall hperiod)
  let a' : aePeriodGroup E := ⟨a, by
    rw [aePeriodGroup_eq_periodGroup_of_regularOpen hEopen hEregular]
    exact hamem⟩
  have htranslate : Tiling.Topology.LocallyFellConverges
      (fun n => dφ n +ᵥ ((g (φ n) : Plane) +ᵥ (T.centres : Set Plane)))
      (a +ᵥ S) := by
    obtain ⟨hclosedSeq, hclosedS, hcompact⟩ := hconv
    have hconvφ : Tiling.Topology.LocallyFellConverges
        (fun n => (g (φ n) : Plane) +ᵥ (T.centres : Set Plane)) S :=
      ⟨fun n => hclosedSeq (φ n), hclosedS, hcompact.comp hφ.tendsto_atTop⟩
    exact Tiling.Topology.locallyFell_translate hconvφ hlim'
  refine ⟨φ, fun n => ⟨ell (φ n), (hell (φ n)).1⟩, a', hφ, ?_, ?_⟩
  · change Tendsto (d ∘ φ) atTop (𝓝 a)
    exact hlim
  · have hseq : ∀ n,
        dφ n +ᵥ ((g (φ n) : Plane) +ᵥ (T.centres : Set Plane)) =
          (ell (φ n) : Plane) +ᵥ (T.centres : Set Plane) := by
      intro n
      simp only [dφ, d, Function.comp_apply, vadd_vadd, sub_add_cancel]
    have heqseq :
        (fun n => dφ n +ᵥ ((g (φ n) : Plane) +ᵥ (T.centres : Set Plane))) =
          (fun n => (ell (φ n) : Plane) +ᵥ (T.centres : Set Plane)) :=
      funext hseq
    rw [← heqseq]
    simpa [a'] using htranslate


end Tiling.Polygonal.Topology
