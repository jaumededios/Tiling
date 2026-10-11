import Tiling.RationalSlopes.Earthquake
import Tiling.RationalSlopes.BoundaryGeometry
import Tiling.Topology.TilingHull

set_option autoImplicit false
set_option linter.style.header false
open Function Filter MeasureTheory Set
open scoped Pointwise Topology
noncomputable section
open Tiling
open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Polygonal
open Tiling.RationalSlopes

namespace Tiling.RationalSlopes

def IsProperLink (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) (a : Plane) : Prop :=
  a +ᵥ (δ : Set Plane) ⊆ ⋃ t : T, (t : Plane) +ᵥ frontier K.support

def HasProperLink (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) : Prop := ∃ a : Plane, IsProperLink K δ T a

def IsUniformlyReady (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x : Plane,
    ∃ a : Plane, IsProperLink K δ T a ∧ dist x a < R

def translatedVertices (K : PolygonalRegion) (T : Set Plane) : Set Plane :=
  vertexSet K.support + T

def HasTransverseFLC (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) : Prop :=
  ∃ ℓ : Plane →L[ℝ] ℝ, ℓ ≠ 0 ∧ LinearMap.ker ℓ.toLinearMap = δ ∧
    HasFLC (ℓ '' translatedVertices K T)

def positiveVertexGaps (K : PolygonalRegion) (ℓ : Plane →L[ℝ] ℝ) : Set ℝ :=
  {r | 0 < r ∧ ∃ v ∈ vertexSet K.support,
    ∃ w ∈ vertexSet K.support, r = ℓ (w - v)}

def IsLeftmostComponentVertex (K : PolygonalRegion) (ℓ : Plane →L[ℝ] ℝ)
    (v : Plane) : Prop :=
  v ∈ vertexSet K.support ∧ ∃ x ∈ K.openCarrier,
    v ∈ closure (connectedComponentIn K.openCarrier x) ∧
      ∀ w ∈ closure (connectedComponentIn K.openCarrier x), ℓ v ≤ ℓ w

private theorem link_frontier_vadd (u : Plane) (D : Set Plane) :
    u +ᵥ frontier D = frontier (u +ᵥ D) := by
  simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
    (Homeomorph.addLeft u).image_frontier D

private theorem link_openUnion_subset_regularSupport (K : PolygonalRegion)
    (S : Set Plane) : openUnion K S ⊆ regularSupport K S := by
  apply interior_maximal subset_closure
  exact isOpen_iUnion fun s => isOpen_interior.vadd (s : Plane)

private theorem link_regularSupport_nonempty {K : PolygonalRegion} {S : Set Plane}
    (hS : S.Nonempty) : (regularSupport K S).Nonempty := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
  refine ⟨s + x, link_openUnion_subset_regularSupport K S ?_⟩
  exact mem_iUnion.mpr ⟨⟨s, hs⟩, mem_vadd_set.mpr ⟨x, hx, rfl⟩⟩

private theorem link_frontier_regularSupport_subset {K : PolygonalRegion}
    {S : Set Plane} (hp : IsPacking K.prototileFamily (K.placements S)) :
    frontier (regularSupport K S) ⊆ ⋃ s : S, (s : Plane) +ᵥ frontier K.support := by
  intro x hx
  have hxclosed : x ∈ closure (openUnion K S) :=
    (closure_minimal interior_subset isClosed_closure) hx.1
  rw [closure_openUnion_eq_iUnion_support hp] at hxclosed
  obtain ⟨s, hs⟩ := mem_iUnion.mp hxclosed
  refine mem_iUnion.mpr ⟨s, ?_⟩
  rw [link_frontier_vadd, frontier, interior_vadd]
  refine ⟨?_, ?_⟩
  · exact subset_closure hs
  · intro hxint
    have hxU : x ∈ openUnion K S := mem_iUnion.mpr ⟨s, hxint⟩
    have hxreg := link_openUnion_subset_regularSupport K S hxU
    exact hx.2 (by simpa only [regularSupport, interior_interior] using hxreg)

private theorem link_of_proper_invariant_subfamily {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements T))
    (hS : S.Nonempty) (hST : S ⊆ T)
    (hproper : regularSupport K S ≠ univ)
    (hinv : IsInvariantAlong (regularSupport K S) δ) : HasProperLink K δ T := by
  have hpS : IsPacking K.prototileFamily (K.placements S) :=
    hp.mono (fun p hp => hST hp)
  obtain ⟨a, ha⟩ := nonempty_frontier_iff.mpr
    ⟨link_regularSupport_nonempty hS, hproper⟩
  refine ⟨a, ?_⟩
  rintro x hx
  obtain ⟨u, hu, rfl⟩ := mem_vadd_set.mp hx
  have hau : a + u ∈ frontier (regularSupport K S) := by
    rw [← hinv u hu, ← link_frontier_vadd]
    exact mem_vadd_set.mpr ⟨a, ha, by simp [vadd_eq_add, add_comm]⟩
  obtain ⟨s, hs⟩ := mem_iUnion.mp (link_frontier_regularSupport_subset hpS hau)
  exact mem_iUnion.mpr ⟨⟨s, hST s.property⟩, hs⟩

private theorem link_openCarrier_disjoint_frontiers {K : PolygonalRegion}
    {T : Set Plane} (hp : IsPacking K.prototileFamily (K.placements T))
    {t : Plane} (ht : t ∈ T) :
    Disjoint (t +ᵥ K.openCarrier) (⋃ s : T, (s : Plane) +ᵥ frontier K.support) := by
  rw [disjoint_iUnion_right]
  intro s
  rw [link_frontier_vadd]
  by_cases hst : t = s
  · subst t
    simpa only [PolygonalRegion.openCarrier, interior_vadd] using
      (disjoint_interior_frontier : Disjoint (interior (s.val +ᵥ K.support))
        (frontier (s.val +ᵥ K.support)))
  · have hd := (isPacking_iff_openCarrier_disjoint K T).mp hp ht s.property hst
    have hdclosed := hd.closure_right (isOpen_interior.vadd t)
    rw [closure_vadd, PolygonalRegion.openCarrier, K.isPolygonal.closure_interior] at hdclosed
    exact hdclosed.mono_right (K.isPolygonal.isClosed.vadd s.val).frontier_subset

private theorem link_no_openCarrier {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} {a x t : Plane}
    (hp : IsPacking K.prototileFamily (K.placements T))
    (hlink : IsProperLink K δ T a) (hx : x ∈ a +ᵥ (δ : Set Plane)) (ht : t ∈ T) :
    x ∉ t +ᵥ K.openCarrier := by
  intro hxt
  exact disjoint_left.mp (link_openCarrier_disjoint_frontiers hp ht) hxt (hlink hx)

private theorem link_translate {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} {a : Plane} (hlink : IsProperLink K δ T a) (g : Plane) :
    IsProperLink K δ (g +ᵥ T) (g + a) := by
  rintro x hx
  obtain ⟨d, hd, rfl⟩ := mem_vadd_set.mp hx
  have had : a + d ∈ a +ᵥ (δ : Set Plane) := mem_vadd_set.mpr ⟨d, hd, rfl⟩
  obtain ⟨t, ht⟩ := mem_iUnion.mp (hlink had)
  obtain ⟨v, hv, heq⟩ := mem_vadd_set.mp ht
  refine mem_iUnion.mpr ⟨⟨g + t, mem_vadd_set.mpr ⟨t, t.property, rfl⟩⟩, ?_⟩
  refine mem_vadd_set.mpr ⟨v, hv, ?_⟩
  dsimp at heq ⊢
  simpa only [vadd_eq_add, add_assoc] using congrArg (g + ·) heq

private theorem link_ready_translate {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} {R : ℝ}
    (hready : ∀ x : Plane, ∃ a, IsProperLink K δ T a ∧ dist x a < R)
    (g : Plane) : ∀ x : Plane, ∃ a, IsProperLink K δ (g +ᵥ T) a ∧ dist x a < R := by
  intro x
  obtain ⟨a, hlink, hd⟩ := hready (x - g)
  refine ⟨g + a, link_translate hlink g, ?_⟩
  have heq : dist x (g + a) = dist (x - g) a := by
    simp only [dist_eq_norm_sub]
    congr 1
    abel
  rwa [heq]

private theorem link_fell_subseq {Sn : ℕ → Set Plane} {S : Set Plane}
    (hconv : Tiling.Topology.LocallyFellConverges Sn S)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tiling.Topology.LocallyFellConverges (Sn ∘ φ) S := by
  obtain ⟨hSn, hS, hlim⟩ := hconv
  exact ⟨fun n => hSn (φ n), hS, hlim.comp hφ.tendsto_atTop⟩

private theorem link_limit {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {Sn : ℕ → Set Plane} {S : Set Plane} {a : ℕ → Plane} {b : Plane}
    (htiles : ∀ n, TilesOn K (Sn n) univ)
    (hconv : Tiling.Topology.LocallyFellConverges Sn S)
    (ha : Tendsto a atTop (𝓝 b)) (hlinks : ∀ n, IsProperLink K δ (Sn n) (a n)) :
    IsProperLink K δ S b := by
  have htileS := Tiling.Polygonal.Topology.tilesOn_isClosed htiles hconv
  have hregS : regularSupport K S = univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htileS
  rintro z hz
  obtain ⟨d, hd, rfl⟩ := mem_vadd_set.mp hz
  have hcover : b + d ∈ closure (openUnion K S) := by
    apply interior_subset
    change b + d ∈ regularSupport K S
    rw [hregS]
    trivial
  rw [closure_openUnion_eq_iUnion_support htileS.2.1] at hcover
  obtain ⟨s, hs⟩ := mem_iUnion.mp hcover
  refine mem_iUnion.mpr ⟨s, ?_⟩
  rw [link_frontier_vadd, frontier, interior_vadd]
  refine ⟨subset_closure hs, ?_⟩
  intro hzin
  have hzbase : b + d - s ∈ K.openCarrier := by
    simpa only [PolygonalRegion.openCarrier, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using hzin
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hzbase
  have heventa : ∀ᶠ n in atTop, dist (a n) b < r / 2 :=
    ha.eventually (Metric.ball_mem_nhds b (by linarith))
  have hevents := Tiling.Topology.locallyFellConverges_eventually_exists_mem_ball
    hconv s.property (show 0 < r / 2 by linarith)
  obtain ⟨n, hnA, s', hsn, hsd⟩ := (heventa.and hevents).exists
  have hzsource : a n + d - s' ∈ K.openCarrier := by
    apply hball
    rw [Metric.mem_ball]
    calc
      dist (a n + d - s') (b + d - s)
          ≤ dist (a n + d) (b + d) + dist s' s := dist_sub_sub_le _ _ _ _
      _ = dist (a n) b + dist s' s := by rw [dist_add_right]
      _ < r := by linarith
  apply link_no_openCarrier (htiles n).2.1 (hlinks n)
    (mem_vadd_set.mpr ⟨d, hd, rfl⟩) hsn
  simpa only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using hzsource

private theorem link_lineSupported_proper
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (S : Set Plane)
    (hδ : Module.finrank ℝ δ = 1)
    (hline : IsLineSupported S δ) : regularSupport K S ≠ univ := by
  have hδtop : δ < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    rw [htop] at hδ
    norm_num [Plane, Complex.finrank_real_complex] at hδ
  obtain ⟨f, hfne, hfδ⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top hδtop inferInstance
  let ℓ : Plane →L[ℝ] ℝ := LinearMap.toContinuousLinearMap f
  have hℓne : ℓ ≠ 0 := by
    intro h
    apply hfne
    ext x
    have hx := congrArg (fun g : Plane →L[ℝ] ℝ => g x) h
    simpa [ℓ] using hx
  obtain ⟨a, ha⟩ := hline
  have himageCompact : IsCompact (ℓ '' K.support) :=
    K.isPolygonal.isCompact.image ℓ.continuous
  obtain ⟨B, hB⟩ := himageCompact.bddAbove
  change ∀ y, y ∈ ℓ '' K.support → y ≤ B at hB
  let U : Set Plane := openUnion K S
  let C : ℝ := ℓ a + B
  let H : Set Plane := {x | ℓ x ≤ C}
  have hUsub : U ⊆ H := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨s, hs⟩
    have hy : x - (s : Plane) ∈ K.openCarrier := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at hs
      simpa [sub_eq_add_neg, add_comm] using hs
    have hsy : ℓ (s : Plane) = ℓ a := by
      have hsa := ha s.1 s.2
      have hzero : f ((s : Plane) - a) = 0 := by
        have : f ((s : Plane) - a) ∈ δ.map f := ⟨(s : Plane) - a, hsa, rfl⟩
        simpa [hfδ] using this
      have hsub : ℓ ((s : Plane) - a) = 0 := by simpa [ℓ] using hzero
      exact sub_eq_zero.mp (by simpa using hsub)
    have hyB : ℓ (x - (s : Plane)) ≤ B :=
      hB (ℓ (x - (s : Plane))) ⟨x - (s : Plane), interior_subset hy, rfl⟩
    dsimp [H, C]
    have hxsum : x = (s : Plane) + (x - (s : Plane)) := by abel
    rw [hxsum, map_add, hsy]
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hyB (ℓ a)
  have hHclosed : IsClosed H := isClosed_Iic.preimage ℓ.continuous
  have hclosure : closure U ⊆ H := closure_minimal hUsub hHclosed
  have hex : ∃ z : Plane, ℓ z ≠ 0 := by
    by_contra h
    push Not at h
    apply hℓne
    ext z
    exact h z
  obtain ⟨z, hz⟩ := hex
  let q : ℝ := C + 1
  let x : Plane := (q / ℓ z) • z
  have hxproj : ℓ x = q := by
    calc
      ℓ x = ℓ ((q / ℓ z) • z) := rfl
      _ = (q / ℓ z) * ℓ z := map_smul ℓ _ _
      _ = q := div_mul_cancel₀ q hz
  intro hfull
  have hxmem : x ∈ regularSupport K S := by rw [hfull]; exact Set.mem_univ x
  have hxclosure : x ∈ closure U := by
    exact (interior_subset : interior (closure U) ⊆ closure U) hxmem
  have : ℓ x ≤ C := hclosure hxclosure
  dsimp [q] at hxproj
  linarith


private theorem link_component_centres_subset {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T : Set Plane} (P : EarthquakeComponent K δ T) :
    P.centres ⊆ T := by
  rintro _ ⟨s, _, rfl⟩
  exact s.property

private theorem link_component_centres_nonempty {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T : Set Plane} (P : EarthquakeComponent K δ T) :
    P.centres.Nonempty := P.nonempty_supp.image Subtype.val

private theorem link_of_distinct_components {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T : Set Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T univ)
    (P Q : EarthquakeComponent K δ T) (hPQ : P ≠ Q) : HasProperLink K δ T := by
  have hreg : regularSupport K T = univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hinv : IsInvariantAlong (regularSupport K T) δ := by
    intro u _
    simp [hreg]
  have hdisj : Disjoint P.carrier Q.carrier :=
    components_carriers_disjoint K δ T hδ htile.2.1
      (mem_univ P) (mem_univ Q) hPQ
  have hproper : P.carrier ≠ univ := by
    intro hP
    obtain ⟨x, hx⟩ := link_regularSupport_nonempty (link_component_centres_nonempty Q)
    exact disjoint_left.mp hdisj (hP ▸ mem_univ x) hx
  exact link_of_proper_invariant_subfamily htile.2.1
    (link_component_centres_nonempty P) (link_component_centres_subset P)
    hproper (component_isInvariant K δ T hδ htile.2.1 hinv P)

-- All local bodies are constructed; inherited skeleton predecessors remain provisional.

theorem nontrivial_decomposition_hasLink :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    Module.finrank ℝ δ = 1 → TilesOn K T Set.univ →
    HasNontrivialEarthquakeDecomposition K δ T → HasProperLink K δ T
  := by
  intro K δ T hδ htile hdecomp
  rcases hdecomp with hcols | ⟨P, Q, hPQ⟩
  · by_contra hnolink
    have hsame (P Q : EarthquakeComponent K δ T) : P = Q := by
      by_contra hPQ
      exact hnolink (link_of_distinct_components hδ htile P Q hPQ)
    have hreg : regularSupport K T = univ :=
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
    have hTne : T.Nonempty := by
      by_contra hT
      have hempty : T = ∅ := not_nonempty_iff_eq_empty.mp hT
      simp [hempty, regularSupport, openUnion] at hreg
      exact (hreg.symm ▸ mem_univ (0 : Plane) : (0 : Plane) ∈ (∅ : Set Plane))
    obtain ⟨t, ht⟩ := hTne
    have htcol : t ∈ columnPart K δ T := hcols ▸ ht
    obtain ⟨P, _⟩ := mem_iUnion.mp htcol
    have hPT : P.val.centres = T := by
      apply Subset.antisymm (link_component_centres_subset P.val)
      intro s hs
      change s ∈ Subtype.val '' P.val.supp
      refine ⟨⟨s, hs⟩, ?_, rfl⟩
      exact hsame ((earthquakeGraph K δ T).connectedComponentMk ⟨s, hs⟩) P.val
    have hline : IsLineSupported T δ := by
      rw [← hPT]
      exact P.property.2.2.1
    exact link_lineSupported_proper K δ T hδ hline hreg
  · exact link_of_distinct_components hδ htile P Q hPQ

theorem positiveVertexGaps_finitePositive :
∀ (K : PolygonalRegion) (ℓ : Plane →L[ℝ] ℝ), ℓ ≠ 0 →
    (positiveVertexGaps K ℓ).Finite ∧ (positiveVertexGaps K ℓ).Nonempty ∧
      ∃ c : ℝ, 0 < c ∧ ∀ r ∈ positiveVertexGaps K ℓ, c ≤ r
  := by
  intro K ℓ hℓ
  let V : Set Plane := vertexSet K.support
  have hVfinite : V.Finite := by
    exact K.isPolygonal.vertexSet_finite
  let D : Set ℝ := (V.prod V).image (fun p : Plane × Plane => ℓ (p.2 - p.1))
  have hDfinite : D.Finite := by
    exact (hVfinite.prod hVfinite).image (fun p : Plane × Plane => ℓ (p.2 - p.1))
  have hfinite : (positiveVertexGaps K ℓ).Finite := by
    apply hDfinite.subset
    intro r hr
    rcases hr with ⟨_, v, hv, w, hw, rfl⟩
    change ℓ (w - v) ∈ (V.prod V).image
      (fun p : Plane × Plane => ℓ (p.2 - p.1))
    exact Set.mem_image_of_mem _ (show (v, w) ∈ V.prod V from ⟨hv, hw⟩)

  obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
  let O : Set Plane := connectedComponentIn (interior K.support) x
  have hO : O ∈ Tiling.interiorComponents K.support := ⟨x, hx, rfl⟩
  have hf : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext z
    have hz := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f z) h
    simpa using hz
  obtain ⟨v, hv, hvO, _, hvstrict⟩ :=
    K.isPolygonal.exists_interiorComponent_min_vertex hO ℓ.toLinearMap hf
  obtain ⟨w, hw, hwO, _, hwstrict⟩ :=
    K.isPolygonal.exists_interiorComponent_max_vertex hO ℓ.toLinearMap hf
  have hxO : x ∈ O := mem_connectedComponentIn hx
  have hproj : ℓ v < ℓ w := by
    exact lt_trans (by simpa using hvstrict x hxO) (by simpa using hwstrict x hxO)
  have hgap : ℓ (w - v) ∈ positiveVertexGaps K ℓ := by
    refine ⟨?_, v, hv, w, hw, rfl⟩
    simpa using sub_pos.mpr hproj
  have hnonempty : (positiveVertexGaps K ℓ).Nonempty := ⟨ℓ (w - v), hgap⟩
  obtain ⟨c, hc, hmin⟩ :=
    Set.exists_min_image (positiveVertexGaps K ℓ) id hfinite hnonempty
  refine ⟨hfinite, hnonempty, c, ?_, ?_⟩
  · simpa using (show c ∈ positiveVertexGaps K ℓ from hc).1
  · intro r hr
    simpa using hmin r hr


private theorem exists_small_lineMap (x z : Plane) {r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    ∃ δ : ℝ, 0 < δ ∧
      (AffineMap.lineMap x z) δ ∈ Metric.ball x r ∩ Metric.ball x q ∧
      (AffineMap.lineMap x z) (-δ) ∈ Metric.ball x r ∩ Metric.ball x q := by
  let ρ := min r q
  have hρ : 0 < ρ := lt_min hr hq
  let n := ‖z - x‖
  have hn : 0 ≤ n := norm_nonneg _
  let δ := ρ / (2 * (n + 1))
  have hden : 0 < 2 * (n + 1) := by positivity
  have hδ : 0 < δ := div_pos hρ hden
  have hδn : δ * n < ρ := by
    change (ρ / (2 * (n + 1))) * n < ρ
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  have hdist_pos : dist ((AffineMap.lineMap x z) δ) x = δ * n := by
    rw [AffineMap.lineMap_apply_module']
    simp [dist_eq_norm, n, abs_of_pos hδ]
  have hdist_neg : dist ((AffineMap.lineMap x z) (-δ)) x = δ * n := by
    rw [AffineMap.lineMap_apply_module']
    simp [dist_eq_norm, n, abs_of_pos hδ]
  refine ⟨δ, hδ, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Metric.mem_ball, hdist_pos]
    exact hδn.trans_le (min_le_left _ _)
  · rw [Metric.mem_ball, hdist_pos]
    exact hδn.trans_le (min_le_right _ _)
  · rw [Metric.mem_ball, hdist_neg]
    exact hδn.trans_le (min_le_left _ _)
  · rw [Metric.mem_ball, hdist_neg]
    exact hδn.trans_le (min_le_right _ _)

private theorem disjoint_regular_left_interior_of_aedisjoint
    {s t : Set Plane} (hregular : closure (interior s) = s)
    (had : AEDisjoint volume s t) : Disjoint s (interior t) := by
  rw [Set.disjoint_left]
  intro x hxs hxt
  rw [← hregular] at hxs
  obtain ⟨y, hyt, hys⟩ := mem_closure_iff.mp hxs (interior t) isOpen_interior hxt
  have hne : volume (interior s ∩ interior t) ≠ 0 :=
    (isOpen_interior.inter isOpen_interior).measure_ne_zero volume ⟨y, hys, hyt⟩
  exact hne (measure_mono_null
    (Set.inter_subset_inter interior_subset interior_subset) had)

private theorem locallyStraight_lines_eq_of_aedisjoint
    {s t : Set Plane} {x : Plane}
    (hsregular : closure (interior s) = s)
    (htregular : closure (interior t) = t)
    (had : AEDisjoint volume s t)
    (hxt : x ∈ frontier t)
    {Ls Lt : AffineSubspace ℝ Plane}
    (hxLs : x ∈ Ls) (hLsdim : Module.finrank ℝ Ls.direction = 1)
    (hsline : ∀ᶠ y in 𝓝 x, (y ∈ frontier s ↔ y ∈ (Ls : Set Plane)))
    (hxLt : x ∈ Lt) (hLtdim : Module.finrank ℝ Lt.direction = 1)
    (htline : ∀ᶠ y in 𝓝 x, (y ∈ frontier t ↔ y ∈ (Lt : Set Plane))) :
    Ls = Lt := by
  obtain ⟨rs, hrs, hsball⟩ := Metric.eventually_nhds_iff.mp hsline
  obtain ⟨rt, hrt, htball⟩ := Metric.eventually_nhds_iff.mp htline
  obtain ⟨ψt, hψt⟩ :=
    Tiling.AffineSubspace.exists_levelSet_coordinate Lt x hxLt hLtdim
  have htboundary (y : Plane) (hy : y ∈ Metric.ball x rt) :
      y ∈ frontier t ↔ ψt y = ψt x :=
    (htball hy).trans (hψt y)
  have htclass := Tiling.local_levelSet_dichotomy ψt hrt htregular hxt htboundary
  dsimp only at htclass
  by_contra hne
  have hz : ∃ z, z ∈ Ls ∧ z ∉ Lt := by
    by_contra h
    push Not at h
    have hle : Ls ≤ Lt := fun z hz ↦ h z hz
    have hdir : Ls.direction = Lt.direction :=
      Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
        (hLsdim.trans hLtdim.symm)
    exact hne
      (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir ⟨x, hxLs⟩ hle)
  obtain ⟨z, hzLs, hzLt⟩ := hz
  have hzψ : ψt z ≠ ψt x := fun h ↦ hzLt ((hψt z).2 h)
  obtain ⟨δ, hδ, hyposBalls, hynegBalls⟩ := exists_small_lineMap x z hrs hrt
  let ypos := (AffineMap.lineMap x z) δ
  let yneg := (AffineMap.lineMap x z) (-δ)
  have hyposLs : ypos ∈ Ls := AffineMap.lineMap_mem δ hxLs hzLs
  have hynegLs : yneg ∈ Ls := AffineMap.lineMap_mem (-δ) hxLs hzLs
  have hψline (r : ℝ) :
      ψt ((AffineMap.lineMap x z) r) = ψt x + r * (ψt z - ψt x) := by
    rw [AffineMap.lineMap_apply_module']
    simp only [map_add, map_smul, map_sub]
    ring
  have hsclosed : IsClosed s := by rw [← hsregular]; exact isClosed_closure
  have hdisj : Disjoint s (interior t) :=
    disjoint_regular_left_interior_of_aedisjoint hsregular had
  have contradict (y : Plane) (hyball : y ∈ Metric.ball x rs)
      (hyLs : y ∈ Ls) (hyt : y ∈ interior t) : False := by
    apply Set.disjoint_left.1 hdisj (hsclosed.frontier_subset ((hsball hyball).2 hyLs)) hyt
  rcases htclass with htpos | htneg
  · rcases lt_or_gt_of_ne hzψ with hzneg | hzpos
    · have hynegPos : ψt x < ψt yneg := by
        dsimp only [yneg]
        rw [hψline]
        nlinarith
      exact contradict yneg hynegBalls.1 hynegLs
        (htpos.1 ⟨hynegBalls.2, hynegPos⟩)
    · have hyposPos : ψt x < ψt ypos := by
        dsimp only [ypos]
        rw [hψline]
        nlinarith
      exact contradict ypos hyposBalls.1 hyposLs
        (htpos.1 ⟨hyposBalls.2, hyposPos⟩)
  · rcases lt_or_gt_of_ne hzψ with hzneg | hzpos
    · have hyposNeg : ψt ypos < ψt x := by
        dsimp only [ypos]
        rw [hψline]
        nlinarith
      exact contradict ypos hyposBalls.1 hyposLs
        (htneg.2 ⟨hyposBalls.2, hyposNeg⟩)
    · have hynegNeg : ψt yneg < ψt x := by
        dsimp only [yneg]
        rw [hψline]
        nlinarith
      exact contradict yneg hynegBalls.1 hynegLs
        (htneg.2 ⟨hynegBalls.2, hynegNeg⟩)

private theorem union_mem_nhds_of_regular_of_aedisjoint_of_locallyStraight
    {s t : Set Plane} {x : Plane}
    (hsregular : closure (interior s) = s)
    (htregular : closure (interior t) = t)
    (had : AEDisjoint volume s t)
    (hxs : x ∈ frontier s) (hxt : x ∈ frontier t)
    (hsstraight : BoundaryLocallyStraightAt s x)
    (htstraight : BoundaryLocallyStraightAt t x) :
    s ∪ t ∈ 𝓝 x := by
  obtain ⟨Ls, hxLs, hLsdim, hsline⟩ := hsstraight
  obtain ⟨Lt, hxLt, hLtdim, htline⟩ := htstraight
  have hlines : Ls = Lt :=
    locallyStraight_lines_eq_of_aedisjoint hsregular htregular had hxt
      hxLs hLsdim hsline hxLt hLtdim htline
  subst Lt
  obtain ⟨rs, hrs, hsball⟩ := Metric.eventually_nhds_iff.mp hsline
  obtain ⟨rt, hrt, htball⟩ := Metric.eventually_nhds_iff.mp htline
  obtain ⟨ψ, hψ⟩ :=
    Tiling.AffineSubspace.exists_levelSet_coordinate Ls x hxLs hLsdim
  have hsboundary (y : Plane) (hy : y ∈ Metric.ball x rs) :
      y ∈ frontier s ↔ ψ y = ψ x :=
    (hsball hy).trans (hψ y)
  have htboundary (y : Plane) (hy : y ∈ Metric.ball x rt) :
      y ∈ frontier t ↔ ψ y = ψ x :=
    (htball hy).trans (hψ y)
  have hsclass := Tiling.local_levelSet_dichotomy ψ hrs hsregular hxs hsboundary
  have htclass := Tiling.local_levelSet_dichotomy ψ hrt htregular hxt htboundary
  dsimp only at hsclass htclass
  let ρ := min rs rt
  have hρ : 0 < ρ := lt_min hrs hrt
  have hρs : ρ ≤ rs := min_le_left _ _
  have hρt : ρ ≤ rt := min_le_right _ _
  have hsclosed : IsClosed s := by rw [← hsregular]; exact isClosed_closure
  have hxsin : x ∈ closure (interior s) := by
    rw [hsregular]
    exact hsclosed.frontier_subset hxs
  obtain ⟨u, huball, huin⟩ :=
    mem_closure_iff.mp hxsin (Metric.ball x ρ) Metric.isOpen_ball
      (Metric.mem_ball_self hρ)
  have huballs : u ∈ Metric.ball x rs := Metric.ball_subset_ball hρs huball
  have huballt : u ∈ Metric.ball x rt := Metric.ball_subset_ball hρt huball
  have huψ : ψ u ≠ ψ x := by
    intro heq
    exact Set.disjoint_left.1 disjoint_interior_frontier huin
      ((hsboundary u huballs).2 heq)
  have hdisj : Disjoint s (interior t) :=
    disjoint_regular_left_interior_of_aedisjoint hsregular had
  have orientations :
      ((Metric.ball x rs ∩ {y | ψ x < ψ y} ⊆ interior s ∧
          Metric.ball x rs ∩ {y | ψ y < ψ x} ⊆ interior sᶜ) ∧
        (Metric.ball x rt ∩ {y | ψ x < ψ y} ⊆ interior tᶜ ∧
          Metric.ball x rt ∩ {y | ψ y < ψ x} ⊆ interior t)) ∨
      ((Metric.ball x rs ∩ {y | ψ x < ψ y} ⊆ interior sᶜ ∧
          Metric.ball x rs ∩ {y | ψ y < ψ x} ⊆ interior s) ∧
        (Metric.ball x rt ∩ {y | ψ x < ψ y} ⊆ interior t ∧
          Metric.ball x rt ∩ {y | ψ y < ψ x} ⊆ interior tᶜ)) := by
    rcases hsclass with hspos | hsneg <;> rcases htclass with htpos | htneg
    · exfalso
      rcases lt_or_gt_of_ne huψ with huneg | hupos
      · exact (interior_subset (hspos.2 ⟨huballs, huneg⟩)) (interior_subset huin)
      · exact Set.disjoint_left.1 hdisj (interior_subset huin)
          (htpos.1 ⟨huballt, hupos⟩)
    · exact Or.inl ⟨hspos, htneg⟩
    · exact Or.inr ⟨hsneg, htpos⟩
    · exfalso
      rcases lt_or_gt_of_ne huψ with huneg | hupos
      · exact Set.disjoint_left.1 hdisj (interior_subset huin)
          (htneg.2 ⟨huballt, huneg⟩)
      · exact (interior_subset (hsneg.1 ⟨huballs, hupos⟩)) (interior_subset huin)
  apply mem_of_superset (Metric.ball_mem_nhds x hρ)
  intro y hyball
  have hyballs : y ∈ Metric.ball x rs := Metric.ball_subset_ball hρs hyball
  have hyballt : y ∈ Metric.ball x rt := Metric.ball_subset_ball hρt hyball
  rcases lt_trichotomy (ψ y) (ψ x) with hyneg | hyeq | hypos
  · rcases orientations with h | h
    · exact Or.inr (interior_subset (h.2.2 ⟨hyballt, hyneg⟩))
    · exact Or.inl (interior_subset (h.1.2 ⟨hyballs, hyneg⟩))
  · exact Or.inl (hsclosed.frontier_subset ((hsboundary y hyballs).2 hyeq))
  · rcases orientations with h | h
    · exact Or.inl (interior_subset (h.1.1 ⟨hyballs, hypos⟩))
    · exact Or.inr (interior_subset (h.2.1 ⟨hyballt, hypos⟩))

private theorem frontier_eventuallyEq_of_eventuallyEq_of_isClosed
    {X : Type*} [TopologicalSpace X] {s t : Set X} {x : X}
    (hs : IsClosed s) (ht : IsClosed t) (hst : s =ᶠ[𝓝 x] t) :
    frontier s =ᶠ[𝓝 x] frontier t := by
  have hst_nhds : ∀ᶠ y in 𝓝 x, s =ᶠ[𝓝 y] t := hst.eventually_nhds
  filter_upwards [hst, hst_nhds] with y hy hynhds
  rw [hs.frontier_eq, ht.frontier_eq]
  ext
  constructor
  · rintro ⟨hys, hyint⟩
    refine ⟨?_, ?_⟩
    · change s y at hys
      change t y
      exact Eq.mp hy hys
    · exact fun hytint ↦ hyint ((hynhds.mem_interior_iff).2 hytint)
  · rintro ⟨hyt, hyint⟩
    refine ⟨?_, ?_⟩
    · change t y at hyt
      change s y
      exact Eq.mpr hy hyt
    · exact fun hysint ↦ hyint ((hynhds.mem_interior_iff).1 hysint)

private theorem placementCarrier_eventuallyEq_placedTile_of_no_vertex
    {P : Type*} [Finite P] (A : PolygonalProtoTiling P)
    (hpacking : IsPacking A.prototiles A.placements) (S : Set A.placements)
    {x : Plane} (hx : x ∈ frontier (A.placementCarrier S))
    (hnone : ∀ i : A.placements, i ∈ S → x ∉ A.placedVertexSet i) :
    ∃ i : A.placements, i ∈ S ∧ x ∈ placedTile A.prototiles i.1 ∧
      A.placementCarrier S =ᶠ[𝓝 x] placedTile A.prototiles i.1 := by
  have hclosed : IsClosed (A.placementCarrier S) := A.placementCarrier_isClosed hpacking S
  have hxmem : x ∈ A.placementCarrier S := hclosed.frontier_subset hx
  obtain ⟨i, hiS, hxi⟩ := A.mem_placementCarrier_iff.mp hxmem
  have tile_subset_carrier {k : A.placements} (hkS : k ∈ S) :
      placedTile A.prototiles k.1 ⊆ A.placementCarrier S := by
    intro y hy
    exact A.mem_placementCarrier_iff.mpr ⟨k, hkS, hy⟩
  have tile_frontier {k : A.placements} (hkS : k ∈ S)
      (hxk : x ∈ placedTile A.prototiles k.1) :
      x ∈ frontier (placedTile A.prototiles k.1) := by
    rw [(A.isClosed_placedTile k.1).frontier_eq]
    refine ⟨hxk, ?_⟩
    intro hxint
    exact Set.disjoint_left.1 disjoint_interior_frontier
      (interior_mono (tile_subset_carrier hkS) hxint) hx
  have hxiFrontier : x ∈ frontier (placedTile A.prototiles i.1) :=
    tile_frontier hiS hxi
  have hiStraight :=
    A.placedTile_boundaryLocallyStraightAt_of_not_mem_placedVertexSet i hxiFrontier
      (hnone i hiS)
  have unique_incident (k : A.placements) (hkS : k ∈ S)
      (hxk : x ∈ placedTile A.prototiles k.1) : k = i := by
    by_contra hki
    have hxkFrontier : x ∈ frontier (placedTile A.prototiles k.1) :=
      tile_frontier hkS hxk
    have hkStraight :=
      A.placedTile_boundaryLocallyStraightAt_of_not_mem_placedVertexSet k hxkFrontier
        (hnone k hkS)
    have hik : i ≠ k := Ne.symm hki
    have haed : AEDisjoint volume (placedTile A.prototiles i.1)
        (placedTile A.prototiles k.1) :=
      hpacking i.2 k.2 (fun h ↦ hik (Subtype.ext h))
    have hunion :
        placedTile A.prototiles i.1 ∪ placedTile A.prototiles k.1 ∈ 𝓝 x :=
      union_mem_nhds_of_regular_of_aedisjoint_of_locallyStraight
        (A.closure_interior_placedTile i.1)
        (A.closure_interior_placedTile k.1) haed hxiFrontier hxkFrontier
        hiStraight hkStraight
    have hcarrier : A.placementCarrier S ∈ 𝓝 x :=
      mem_of_superset hunion (union_subset (tile_subset_carrier hiS) (tile_subset_carrier hkS))
    have hxint : x ∈ interior (A.placementCarrier S) := mem_interior_iff_mem_nhds.mpr hcarrier
    exact Set.disjoint_left.1 disjoint_interior_frontier hxint hx
  have hfinite : LocallyFinite fun k : {k : A.placements // k ∈ S} ↦
      placedTile A.prototiles k.1.1 :=
    (A.locallyFinite_placedTile hpacking).comp_injective Subtype.val_injective
  have hevent := hfinite.eventually_subset
    (fun k : {k : A.placements // k ∈ S} ↦ A.isClosed_placedTile k.1.1) x
  have hcarrier_tile :
      A.placementCarrier S =ᶠ[𝓝 x] placedTile A.prototiles i.1 := by
    filter_upwards [hevent] with y hy
    apply propext
    constructor
    · intro hycarrier
      obtain ⟨k, hkS, hyk⟩ := A.mem_placementCarrier_iff.mp hycarrier
      have hxk : x ∈ placedTile A.prototiles k.1 :=
        hy (a := ⟨k, hkS⟩)
          (show y ∈ placedTile A.prototiles (⟨k, hkS⟩ : {k : A.placements // k ∈ S}).1.1
            from hyk)
      have hki : k = i := unique_incident k hkS hxk
      change placedTile A.prototiles k.1 y at hyk
      change placedTile A.prototiles i.1 y
      simpa only [hki] using hyk
    · intro hyi
      exact A.mem_placementCarrier_iff.mpr ⟨i, hiS, hyi⟩
  exact ⟨i, hiS, hxi, hcarrier_tile⟩

private theorem exists_vertex_along_kernel_ray
    {D : Set Plane} (hD : IsPolygonal D) {p v : Plane}
    (ℓ : Plane →L[ℝ] ℝ)
    (hp : p ∈ frontier D) (hvne : v ≠ 0) (hvre : ℓ v = 0)
    (hgerm : ∀ᶠ z in nhds p, z ∈ frontier D ↔ ℓ z = ℓ p) :
    ∃ b : ℝ, 0 < b ∧ p + b • v ∈ vertexSet D ∧
      ∀ t ∈ Set.Icc (0 : ℝ) b, p + t • v ∈ frontier D := by
  let φ : ℝ → Plane := fun t ↦ p + t • v
  have hφ : Continuous φ := by fun_prop
  let F : Set ℝ := φ ⁻¹' frontier D
  have hFclosed : IsClosed F := isClosed_frontier.preimage hφ
  have hzeroF : (0 : ℝ) ∈ F := by simpa [F, φ] using hp
  have hF_bddAbove : BddAbove F := by
    obtain ⟨R, hR⟩ := hD.isBounded.subset_closedBall p
    refine ⟨R / ‖v‖, fun t ht ↦ ?_⟩
    have htD : φ t ∈ D := hD.isClosed.frontier_subset ht
    have hdist := hR htD
    rw [Metric.mem_closedBall] at hdist
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    have habs : |t| * ‖v‖ ≤ R := by
      simpa [F, φ, dist_eq_norm, norm_smul, Real.norm_eq_abs] using hdist
    apply (le_div_iff₀ hvnorm).2
    exact (mul_le_mul_of_nonneg_right (le_abs_self t) hvnorm.le).trans habs
  have hparam : {t : ℝ | φ t ∈ frontier D ↔ ℓ (φ t) = ℓ p} ∈ nhds 0 := by
    change {z | z ∈ frontier D ↔ ℓ z = ℓ p} ∈ nhds p at hgerm
    have hgerm' : {z | z ∈ frontier D ↔ ℓ z = ℓ p} ∈ nhds (φ 0) := by
      simpa [φ] using hgerm
    exact hφ.continuousAt.preimage_mem_nhds hgerm'
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hparam
  obtain ⟨e, he0, heu⟩ := exists_between hu
  have heF : e ∈ F := by
    have heIoo : e ∈ Set.Ioo l u := ⟨hl.trans he0, heu⟩
    apply (hlu heIoo).mpr
    simp only [φ, map_add, map_smul, hvre, smul_zero, add_zero]
  let J : Set ℝ := connectedComponentIn F 0
  have hzeroJ : (0 : ℝ) ∈ J := mem_connectedComponentIn hzeroF
  have heJ : e ∈ J := by
    refine isPreconnected_Icc.subset_connectedComponentIn
      (left_mem_Icc.mpr he0.le) ?_ (right_mem_Icc.mpr he0.le)
    intro t ht
    have htIoo : t ∈ Set.Ioo l u := ⟨hl.trans_le ht.1, ht.2.trans_lt heu⟩
    apply (hlu htIoo).mpr
    simp only [φ, map_add, map_smul, hvre, smul_zero, add_zero]
  have hJclosed : IsClosed J := by
    dsimp only [J]
    rw [connectedComponentIn_eq_image hzeroF]
    exact hFclosed.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hJ_bddAbove : BddAbove J := hF_bddAbove.mono (connectedComponentIn_subset F 0)
  have hJnonempty : J.Nonempty := ⟨0, hzeroJ⟩
  let b : ℝ := sSup J
  have hbGreatest : IsGreatest J b := hJclosed.isGreatest_csSup hJnonempty hJ_bddAbove
  have hbJ : b ∈ J := hbGreatest.1
  have hbpos : 0 < b := he0.trans_le (hbGreatest.2 heJ)
  have hfrontier_of_mem_J {t : ℝ} (ht : t ∈ J) : φ t ∈ frontier D :=
    connectedComponentIn_subset F 0 ht
  have hbfrontier : φ b ∈ frontier D := hfrontier_of_mem_J hbJ
  have hbvertex : φ b ∈ vertexSet D := by
    by_contra hbnotvertex
    have hstraight := hD.boundaryLocallyStraightAt_of_not_mem_vertexSet
      hbfrontier hbnotvertex
    obtain ⟨L, hbL, _hdim, hlocal⟩ := hstraight
    have hlineParam : {t : ℝ | φ t ∈ frontier D ↔ φ t ∈ (L : Set Plane)} ∈
        nhds b := hφ.continuousAt.preimage_mem_nhds hlocal
    obtain ⟨l', u', ⟨hl'b, hbu'⟩, hlu'⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp hlineParam
    obtain ⟨t₁, ht₁l, ht₁b⟩ := exists_between (max_lt hl'b hbpos)
    have ht₁nonneg : 0 ≤ t₁ := (le_max_right l' 0).trans ht₁l.le
    have ht₁J : t₁ ∈ J :=
      isPreconnected_connectedComponentIn.Icc_subset hzeroJ hbJ ⟨ht₁nonneg, ht₁b.le⟩
    have ht₁L : φ t₁ ∈ L :=
      (hlu' ⟨(le_max_left l' 0).trans_lt ht₁l, ht₁b.trans hbu'⟩).mp
        (hfrontier_of_mem_J ht₁J)
    obtain ⟨t₂, hbt₂, ht₂u⟩ := exists_between hbu'
    have lineMap_eq (t : ℝ) :
        AffineMap.lineMap (φ b) (φ t₁) ((t - b) / (t₁ - b)) = φ t := by
      have ht₁bne : t₁ - b ≠ 0 := sub_ne_zero.mpr ht₁b.ne
      simp only [AffineMap.lineMap_apply, φ, vsub_eq_sub, vadd_eq_add]
      rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul,
        div_mul_cancel₀ (t - b) ht₁bne, sub_smul]
      abel
    have hintervalF : Set.Icc b t₂ ⊆ F := by
      intro t ht
      have htL : φ t ∈ L := by
        rw [← lineMap_eq t]
        exact AffineMap.lineMap_mem _ hbL ht₁L
      have htlocal : t ∈ Set.Ioo l' u' := ⟨hl'b.trans_le ht.1, ht.2.trans_lt ht₂u⟩
      exact (hlu' htlocal).mpr htL
    have ht₂_component_b : t₂ ∈ connectedComponentIn F b :=
      isPreconnected_Icc.subset_connectedComponentIn
        (left_mem_Icc.mpr hbt₂.le) hintervalF (right_mem_Icc.mpr hbt₂.le)
    have hcomponents : J = connectedComponentIn F b := connectedComponentIn_eq hbJ
    have ht₂J : t₂ ∈ J := hcomponents.symm ▸ ht₂_component_b
    exact (not_lt_of_ge (hbGreatest.2 ht₂J)) hbt₂
  refine ⟨b, hbpos, hbvertex, ?_⟩
  intro t ht
  exact hfrontier_of_mem_J
    (isPreconnected_connectedComponentIn.Icc_subset hzeroJ hbJ ht)

private theorem locallyStraight_eq_level_of_no_lower_frontier
    {D : Set Plane} {p : Plane} (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hstraight : BoundaryLocallyStraightAt D p)
    (hnoLower : ∀ z, ℓ z < ℓ p → z ∉ frontier D) :
    ∃ ρ > 0, ∀ z ∈ Metric.ball p ρ,
      (z ∈ frontier D ↔ ℓ z = ℓ p) := by
  obtain ⟨L, hpL, hLdim, hlocal⟩ := hstraight
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
  have hLle : (L : Set Plane) ⊆ {z | ℓ z = ℓ p} := by
    intro z hzL
    by_contra hne
    have hne' : ℓ z ≠ ℓ p := by simpa using hne
    obtain ⟨δ, hδ, hplus, hminus⟩ := exists_small_lineMap p z hρ hρ
    have hcoord (r : ℝ) :
        ℓ ((AffineMap.lineMap p z) r) = ℓ p + r * (ℓ z - ℓ p) := by
      rw [AffineMap.lineMap_apply_module']
      simp only [map_add, map_smul, map_sub]
      ring
    by_cases hlt : ℓ z < ℓ p
    · have hqL : (AffineMap.lineMap p z) δ ∈ L :=
        AffineMap.lineMap_mem δ hpL hzL
      have hqfront : (AffineMap.lineMap p z) δ ∈ frontier D :=
        (hball (Metric.mem_ball.mp hplus.1)).mpr hqL
      have hcoord' := hcoord δ
      exact hnoLower _ (by rw [hcoord']; nlinarith) hqfront
    · have hgt : ℓ p < ℓ z := lt_of_le_of_ne (le_of_not_gt hlt) hne'.symm
      have hqL : (AffineMap.lineMap p z) (-δ) ∈ L :=
        AffineMap.lineMap_mem (-δ) hpL hzL
      have hqfront : (AffineMap.lineMap p z) (-δ) ∈ frontier D :=
        (hball (Metric.mem_ball.mp hminus.1)).mpr hqL
      have hcoord' := hcoord (-δ)
      exact hnoLower _ (by rw [hcoord']; nlinarith) hqfront
  let H : AffineSubspace ℝ Plane := AffineSubspace.mk' p (LinearMap.ker ℓ.toLinearMap)
  have hLsub : L ≤ H := by
    intro z hz
    rw [AffineSubspace.mem_mk']
    change ℓ.toLinearMap (z - p) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hLle hz)
  have hvalue : ∃ u : Plane, ℓ.toLinearMap u = 1 := by
    have hu : ∃ u : Plane, ℓ u ≠ 0 := by
      by_contra h
      apply hℓ
      ext z
      simpa using not_exists.mp h z
    obtain ⟨u, hu⟩ := hu
    refine ⟨(ℓ u)⁻¹ • u, ?_⟩
    rw [map_smul]
    simp only [smul_eq_mul]
    exact inv_mul_cancel₀ hu
  have hsurj : Function.Surjective ℓ.toLinearMap := by
    intro r
    obtain ⟨u, hu⟩ := hvalue
    exact ⟨r • u, by rw [map_smul, hu, smul_eq_mul, mul_one]⟩
  have hkerdim : Module.finrank ℝ (LinearMap.ker ℓ.toLinearMap) = 1 := by
    have hrank := ℓ.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Complex.finrank_real_complex] at hrank
    omega
  have hHdim : Module.finrank ℝ H.direction = 1 := by
    dsimp [H]
    rw [AffineSubspace.direction_mk']
    exact hkerdim
  have hdir : L.direction = H.direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hLsub)
      (hLdim.trans hHdim.symm)
  have hLH : L = H :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir ⟨p, hpL⟩ hLsub
  refine ⟨ρ, hρ, ?_⟩
  intro z hz
  have hz' := hball (Metric.mem_ball.mp hz)
  rw [hLH] at hz'
  change (z ∈ frontier D ↔ z - p ∈ LinearMap.ker ℓ.toLinearMap) at hz'
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hz'
  exact hz'

private theorem exists_ne_zero_mem_ker (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ∃ e : Plane, e ≠ 0 ∧ ℓ e = 0 := by
  have hu : ∃ u : Plane, ℓ.toLinearMap u = 1 := by
    have hex : ∃ u : Plane, ℓ u ≠ 0 := by
      by_contra h
      apply hℓ
      ext z
      simpa using not_exists.mp h z
    obtain ⟨u, hu⟩ := hex
    refine ⟨(ℓ u)⁻¹ • u, ?_⟩
    rw [map_smul]
    simp only [smul_eq_mul]
    exact inv_mul_cancel₀ hu
  have hsurj : Function.Surjective ℓ.toLinearMap := by
    intro r
    obtain ⟨u, hu⟩ := hu
    exact ⟨r • u, by rw [map_smul, hu, smul_eq_mul, mul_one]⟩
  have hkerdim : Module.finrank ℝ (LinearMap.ker ℓ.toLinearMap) = 1 := by
    have hrank := ℓ.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Complex.finrank_real_complex] at hrank
    omega
  let _ : Nontrivial (LinearMap.ker ℓ.toLinearMap) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hkerdim]; norm_num)
  obtain ⟨e0, he0⟩ := exists_ne (0 : LinearMap.ker ℓ.toLinearMap)
  refine ⟨e0, ?_, ?_⟩
  · intro he
    apply he0
    exact Subtype.ext he
  · exact (LinearMap.mem_ker.mp e0.property)

private theorem threshold_carrier_switch
    {P : Type*} [Finite P] (A : PolygonalProtoTiling P)
    (hA : IsTiling A.prototiles A.placements)
    (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (p : Plane)
    (hp : p ∈ frontier (A.placementCarrier
      {i : A.placements | ∀ z ∈ placedTile A.prototiles i.val, ℓ p ≤ ℓ z})) :
    ∃ j : A.placements, ∃ w ∈ A.placedVertexSet j, ℓ w = ℓ p ∧
      ∃ z ∈ placedTile A.prototiles j.val, ℓ z < ℓ w := by
  classical
  let R : Set A.placements :=
    {i : A.placements | ∀ z ∈ placedTile A.prototiles i.val, ℓ p ≤ ℓ z}
  have hpR : p ∈ frontier (A.placementCarrier R) := hp
  have hRsubset : A.placementCarrier R ⊆ ℓ ⁻¹' Ici (ℓ p) := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := A.mem_placementCarrier_iff.mp hz
    exact hi z hzi
  have hnoLower : ∀ z, ℓ z < ℓ p → z ∉ frontier (A.placementCarrier R) := by
    intro z hlt hz
    have hzR := (A.placementCarrier_isClosed hA.isPacking R).frontier_subset hz
    exact (not_le_of_gt hlt) (hRsubset hzR)
  have lower_of_notR {j : A.placements} (hj : j ∉ R) :
      ∃ z ∈ placedTile A.prototiles j.val, ℓ z < ℓ p := by
    change ¬ ∀ z, z ∈ placedTile A.prototiles j.val → ℓ p ≤ ℓ z at hj
    push Not at hj
    obtain ⟨z, hz, hnot⟩ := hj
    exact ⟨z, hz, hnot⟩
  by_contra hnoSwitch
  have hnone : ∀ j : A.placements, j ∈ Rᶜ → p ∉ A.placedVertexSet j := by
    intro j hj hw
    obtain ⟨z, hz, hzl⟩ := lower_of_notR (by simpa using hj)
    exact hnoSwitch ⟨j, p, hw, rfl, z, hz, hzl⟩
  by_cases hstraight : BoundaryLocallyStraightAt (A.placementCarrier R) p
  · obtain ⟨ρ, hρ, hlevel⟩ := locallyStraight_eq_level_of_no_lower_frontier
      ℓ hℓ hstraight hnoLower
    have hDfrontier :
        frontier (A.placementCarrier Rᶜ) = frontier (A.placementCarrier R) :=
      (A.frontier_placementCarrier_compl hA R).symm
    have hDfront : p ∈ frontier (A.placementCarrier Rᶜ) := by
      rw [hDfrontier]
      exact hpR
    obtain ⟨j, hj, hpj, hcarrierTile⟩ :=
      placementCarrier_eventuallyEq_placedTile_of_no_vertex A hA.isPacking Rᶜ hDfront hnone
    have hDclosed : IsClosed (A.placementCarrier Rᶜ) :=
      A.placementCarrier_isClosed hA.isPacking Rᶜ
    have htileClosed : IsClosed (placedTile A.prototiles j.val) := A.isClosed_placedTile j.val
    have hfrontTile := frontier_eventuallyEq_of_eventuallyEq_of_isClosed
      hDclosed htileClosed hcarrierTile
    have htileLevel : ∀ᶠ z in nhds p,
        z ∈ frontier (placedTile A.prototiles j.val) ↔ ℓ z = ℓ p := by
      have hlevelEventual : ∀ᶠ z in nhds p,
          z ∈ frontier (A.placementCarrier R) ↔ ℓ z = ℓ p :=
        Metric.eventually_nhds_iff.mpr ⟨ρ, hρ, hlevel⟩
      filter_upwards [hfrontTile, hlevelEventual] with z htile hC
      rw [← hDfrontier] at hC
      exact (Iff.of_eq htile.symm).trans hC
    have hpjFront : p ∈ frontier (placedTile A.prototiles j.val) := by
      rw [(A.isClosed_placedTile j.val).frontier_eq]
      refine ⟨hpj, ?_⟩
      intro hpinterior
      have htileSubset : placedTile A.prototiles j.val ⊆ A.placementCarrier Rᶜ := by
        intro z hz
        exact A.mem_placementCarrier_iff.mpr ⟨j, hj, hz⟩
      have hpinteriorD : p ∈ interior (A.placementCarrier Rᶜ) :=
        interior_mono htileSubset hpinterior
      exact Set.disjoint_left.1 disjoint_interior_frontier hpinteriorD hDfront
    obtain ⟨e, he, hele⟩ := exists_ne_zero_mem_ker ℓ hℓ
    obtain ⟨b, hbpos, hbvertex, hbsegment⟩ :=
      exists_vertex_along_kernel_ray (A.isPolygonal_placedTile j.val) (ℓ := ℓ)
        hpjFront he hele htileLevel
    have hbPlaced : p + b • e ∈ A.placedVertexSet j := by
      have hq : p + b • e ∈ vertexSet (placedTile A.prototiles j.val) := by
        simpa only [vadd_eq_add] using hbvertex
      simpa only [A.vertexSet_placedTile'] using hq
    have hblevel : ℓ (p + b • e) = ℓ p := by
      simp only [map_add, map_smul, hele, smul_zero, add_zero]
    obtain ⟨z, hz, hzl⟩ := lower_of_notR (by simpa using hj)
    have hzl' : ℓ z < ℓ (p + b • e) := by rw [hblevel]; exact hzl
    exact hnoSwitch ⟨j, p + b • e, hbPlaced, hblevel, z, hz, hzl'⟩
  · obtain ⟨i, j, hi, hj, hpi, hpj⟩ :=
      A.exists_vertices_across_of_not_boundaryLocallyStraightAt hA R hpR hstraight
    obtain ⟨z, hz, hzl⟩ := lower_of_notR hj
    exact hnoSwitch ⟨j, p, hpj, rfl, z, hz, hzl⟩


private theorem component_vertex_subset {K : PolygonalRegion} {O : Set Plane}
    (hO : O ∈ interiorComponents K.support) :
    vertexSet (closure O) ⊆ vertexSet K.support := by
  intro v hv T
  obtain ⟨F, hFT, _, _, hclosure⟩ := T.interiorComponent_subfamily hO
  let U : Triangulation (closure O) := {
    pieces := F
    isTriangle := fun t ht => T.isTriangle t (hFT ht)
    pairwiseAEDisjoint := fun t ht u hu htu =>
      T.pairwiseAEDisjoint (hFT ht) (hFT hu) htu
    sUnion_eq := hclosure.symm }
  obtain ⟨t, ht, hvt⟩ := hv U
  exact ⟨t, hFT ht, hvt⟩

private theorem component_closure_subset {K : PolygonalRegion} {O : Set Plane}
    (hO : O ∈ interiorComponents K.support) : closure O ⊆ K.support := by
  exact K.isPolygonal.isClosed.closure_subset_iff.mpr
    ((interiorComponent_basic hO).2.2.trans interior_subset)

private def refinedPrototiling (K : PolygonalRegion) (T : Set Plane) :
    PolygonalProtoTiling {O : Set Plane // O ∈ interiorComponents K.support} where
  prototiles := fun O => {
    support := closure O.val
    measurableSet_support := isClosed_closure.measurableSet
    nonempty_support := (interiorComponent_basic O.property).2.1.nonempty.mono subset_closure }
  placements := {p | p.1 ∈ T}
  isPolygonal := fun O => K.isPolygonal.interiorComponent_closure_isPolygonal O.property

private theorem refined_isPacking {K : PolygonalRegion} {T : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements T)) :
    IsPacking (refinedPrototiling K T).prototiles (refinedPrototiling K T).placements := by
  intro i hi j hj hij
  change AEDisjoint volume (i.1 +ᵥ closure i.2.val) (j.1 +ᵥ closure j.2.val)
  by_cases hs : i.1 = j.1
  · have hO : i.2.val ≠ j.2.val := by
      intro hO
      exact hij (Prod.ext hs (Subtype.ext hO))
    have hd := K.isPolygonal.interiorComponentClosures_pairwiseAEDisjoint
      i.2.property j.2.property hO
    have hplaced := aedisjoint_vadd i.1 hd
    simpa only [hs] using hplaced
  · have hplaced := hp (x := (i.1, ())) (y := (j.1, ())) hi hj
      (fun h => hs (congrArg (fun p : Placement Plane Unit => p.1) h))
    apply hplaced.mono
    · rintro x ⟨y, hy, rfl⟩
      exact mem_vadd_set.mpr ⟨y, component_closure_subset i.2.property hy, rfl⟩
    · rintro x ⟨y, hy, rfl⟩
      exact mem_vadd_set.mpr ⟨y, component_closure_subset j.2.property hy, rfl⟩

private theorem refined_isTiling {K : PolygonalRegion} {T : Set Plane}
    (htile : TilesOn K T univ) :
    IsTiling (refinedPrototiling K T).prototiles (refinedPrototiling K T).placements := by
  let I := {O : Set Plane // O ∈ interiorComponents K.support}
  let _ : Finite I := K.isPolygonal.interiorComponents_finite.to_subtype
  let _ : Countable T := htile.1.to_subtype
  have hcount : (refinedPrototiling K T).placements.Countable := by
    have heq : (refinedPrototiling K T).placements =
        range (fun p : T × I => (p.1.val, p.2)) := by
      ext p
      constructor
      · intro hp
        exact ⟨(⟨p.1, hp⟩, p.2), rfl⟩
      · rintro ⟨p, rfl⟩
        exact p.1.property
    rw [heq]
    exact countable_range _
  refine ⟨hcount, refined_isPacking htile.2.1, ?_⟩
  filter_upwards [htile.2.2] with x hx
  obtain ⟨t, ht⟩ := hx.mp (mem_univ x)
  obtain ⟨y, hy, rfl⟩ := mem_vadd_set.mp ht
  have hyS : y ∈ K.support := interior_subset hy
  rw [← K.isPolygonal.iUnion_closure_interiorComponents] at hyS
  obtain ⟨O, hO, hyO⟩ := mem_iUnion₂.mp hyS
  refine mem_iUnion.mpr ⟨⟨(t.val, ⟨O, hO⟩), t.property⟩, ?_⟩
  exact mem_vadd_set.mpr ⟨y, hyO, rfl⟩

private theorem component_threshold_frontier {K : PolygonalRegion} {T : Set Plane}
    {ℓ : Plane →L[ℝ] ℝ} {v t x : Plane}
    (htile : TilesOn K T univ) (hℓ : ℓ ≠ 0) (ht : t ∈ T) (hx : x ∈ K.openCarrier)
    (hv : v ∈ closure (connectedComponentIn K.openCarrier x))
    (hmin : ∀ z ∈ closure (connectedComponentIn K.openCarrier x), ℓ v ≤ ℓ z) :
    let A := refinedPrototiling K T
    let R : Set A.placements := {i | ∀ z ∈ placedTile A.prototiles i.val, ℓ (v + t) ≤ ℓ z}
    v + t ∈ frontier (A.placementCarrier R) := by
  let I := {O : Set Plane // O ∈ interiorComponents K.support}
  let _ : Finite I := K.isPolygonal.interiorComponents_finite.to_subtype
  let A := refinedPrototiling K T
  let R : Set A.placements := {i | ∀ z ∈ placedTile A.prototiles i.val, ℓ (v + t) ≤ ℓ z}
  change v + t ∈ frontier (A.placementCarrier R)
  have hO : connectedComponentIn K.openCarrier x ∈ interiorComponents K.support := ⟨x, hx, rfl⟩
  let O : I := ⟨connectedComponentIn K.openCarrier x, hO⟩
  let i : A.placements := ⟨(t, O), ht⟩
  have hiR : i ∈ R := by
    rintro z hz
    obtain ⟨y, hy, rfl⟩ := mem_vadd_set.mp hz
    have hmy := hmin y hy
    simp only [vadd_eq_add, map_add]
    linarith
  have hpC : v + t ∈ A.placementCarrier R := by
    apply A.mem_placementCarrier_iff.mpr
    exact ⟨i, hiR, mem_vadd_set.mpr ⟨v, hv, by simp [i, vadd_eq_add, add_comm]⟩⟩
  have hCsub : A.placementCarrier R ⊆ ℓ ⁻¹' Ici (ℓ (v + t)) := by
    intro z hz
    obtain ⟨j, hj, hzj⟩ := A.mem_placementCarrier_iff.mp hz
    exact hj z hzj
  have hsurj : Surjective ℓ := by
    have hex : ∃ z : Plane, ℓ z ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hℓ
      ext z
      exact hn z
    obtain ⟨z, hz⟩ := hex
    intro r
    refine ⟨(r / ℓ z) • z, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ r hz]
  rw [(A.placementCarrier_isClosed (refined_isPacking htile.2.1) R).frontier_eq]
  refine ⟨hpC, ?_⟩
  intro hpin
  have himgsub : ℓ '' interior (A.placementCarrier R) ⊆ Ici (ℓ (v + t)) := by
    rintro r ⟨z, hz, rfl⟩
    exact hCsub (interior_subset hz)
  have hmem : ℓ (v + t) ∈ interior (Ici (ℓ (v + t))) :=
    interior_maximal himgsub ((ℓ.isOpenMap hsurj) _ isOpen_interior)
      ⟨v + t, hpin, rfl⟩
  simp only [interior_Ici, mem_Ioi, lt_self_iff_false] at hmem

private theorem component_switch_witness {K : PolygonalRegion} {T : Set Plane}
    {ℓ : Plane →L[ℝ] ℝ} {v t : Plane}
    (j : (refinedPrototiling K T).placements) {w : Plane}
    (hw : w ∈ (refinedPrototiling K T).placedVertexSet j)
    (hwlevel : ℓ w = ℓ (v + t))
    (hlower : ∃ z ∈ placedTile (refinedPrototiling K T).prototiles j.val, ℓ z < ℓ w) :
    ∃ s ∈ T, ∃ u ∈ vertexSet K.support, ℓ (u + s) = ℓ (v + t) ∧
      ∃ x ∈ K.openCarrier, u ∈ closure (connectedComponentIn K.openCarrier x) ∧
        ∃ y ∈ closure (connectedComponentIn K.openCarrier x), ℓ y < ℓ u := by
  obtain ⟨u, hu, rfl⟩ := mem_vadd_set.mp hw
  obtain ⟨O, hx, hOx⟩ := j.val.2.property
  obtain ⟨U⟩ := K.isPolygonal.interiorComponent_closure_isPolygonal j.val.2.property
  obtain ⟨q, hq, huq⟩ := hu U
  have huclosure : u ∈ closure j.val.2.val := by
    rw [← U.sUnion_eq]
    exact mem_sUnion.mpr ⟨q, hq, extremePoints_subset huq⟩
  obtain ⟨z, hz, hzl⟩ := hlower
  obtain ⟨y, hy, rfl⟩ := mem_vadd_set.mp hz
  change y ∈ closure j.val.2.val at hy
  refine ⟨j.val.1, j.property, u, component_vertex_subset j.val.2.property hu, ?_,
    O, hx, ?_, y, ?_, ?_⟩
  · simpa only [vadd_eq_add, add_comm] using hwlevel
  · simpa only [PolygonalRegion.openCarrier, ← hOx] using huclosure
  · simpa only [PolygonalRegion.openCarrier, ← hOx] using hy
  · simp only [vadd_eq_add, map_add] at hzl
    linarith



theorem leftmostComponentVertex_switch :
∀ (K : PolygonalRegion) (T : Set Plane) (ℓ : Plane →L[ℝ] ℝ),
    TilesOn K T Set.univ → ℓ ≠ 0 →
      ∀ t ∈ T, ∀ v : Plane, IsLeftmostComponentVertex K ℓ v →
        ∃ s ∈ T, ∃ w ∈ vertexSet K.support,
          ℓ (w + s) = ℓ (v + t) ∧
            ∃ x ∈ K.openCarrier,
              w ∈ closure (connectedComponentIn K.openCarrier x) ∧
                ∃ y ∈ closure (connectedComponentIn K.openCarrier x), ℓ y < ℓ w
  := by
  intro K T ℓ htile hℓ t ht v hleft
  obtain ⟨_, x, hx, hvO, hmin⟩ := hleft
  let I := {O : Set Plane // O ∈ interiorComponents K.support}
  let _ : Finite I := K.isPolygonal.interiorComponents_finite.to_subtype
  let A := refinedPrototiling K T
  have hA := refined_isTiling htile
  have hpfront := component_threshold_frontier htile hℓ ht hx hvO hmin
  obtain ⟨j, w, hw, hlevel, hlower⟩ :=
    threshold_carrier_switch A hA ℓ hℓ (v + t) hpfront
  exact component_switch_witness j hw hlevel hlower

private theorem link_component_on_right {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T O : Set Plane} {a t v : Plane} {ℓ : Plane →L[ℝ] ℝ}
    (hp : IsPacking K.prototileFamily (K.placements T))
    (hker : LinearMap.ker ℓ.toLinearMap = δ) (hlink : IsProperLink K δ T a)
    (ht : t ∈ T) (hO : O ∈ interiorComponents K.support)
    (hv : v ∈ closure O) (hvright : ℓ a < ℓ (v + t)) :
    ∀ w ∈ closure O, ℓ a ≤ ℓ (w + t) := by
  intro w hw
  by_contra hn
  have hwleft : ℓ (w + t) < ℓ a := lt_of_not_ge hn
  let f : Plane → ℝ := fun z => ℓ (z + t)
  have hf : Continuous f := ℓ.continuous.comp (continuous_id.add continuous_const)
  obtain ⟨p, hpleft, hpO⟩ := mem_closure_iff.mp hw
    (f ⁻¹' Iio (ℓ a)) (isOpen_Iio.preimage hf) hwleft
  obtain ⟨q, hqright, hqO⟩ := mem_closure_iff.mp hv
    (f ⁻¹' Ioi (ℓ a)) (isOpen_Ioi.preimage hf) hvright
  obtain ⟨z, hzO, hzval⟩ := (interiorComponent_basic hO).2.1.isPreconnected.intermediate_value
    hpO hqO hf.continuousOn ⟨hpleft.le, hqright.le⟩
  have hzline : z + t ∈ a +ᵥ (δ : Set Plane) := by
    refine mem_vadd_set.mpr ⟨z + t - a, ?_, ?_⟩
    · rw [← hker]
      change ℓ (z + t - a) = 0
      change ℓ (z + t) = ℓ a at hzval
      simp only [map_sub, hzval, sub_self]
    · simp only [vadd_eq_add]
      abel
  apply link_no_openCarrier hp hlink hzline ht
  exact mem_vadd_set.mpr ⟨z, (interiorComponent_basic hO).2.2 hzO,
    by simp only [vadd_eq_add, add_comm]⟩

private theorem link_vertex_component {K : PolygonalRegion} {v : Plane}
    (hv : v ∈ vertexSet K.support) :
    ∃ O ∈ interiorComponents K.support, v ∈ closure O := by
  obtain ⟨triangulation⟩ := K.isPolygonal
  obtain ⟨t, ht, hvt⟩ := hv triangulation
  have hvS : v ∈ K.support := by
    rw [← triangulation.sUnion_eq]
    exact mem_sUnion.mpr ⟨t, ht, extremePoints_subset hvt⟩
  rw [← K.isPolygonal.iUnion_closure_interiorComponents] at hvS
  obtain ⟨O, hO, hvO⟩ := mem_iUnion₂.mp hvS
  exact ⟨O, hO, hvO⟩

private theorem link_right_step {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} {a p : Plane} {ℓ : Plane →L[ℝ] ℝ}
    (htile : TilesOn K T univ) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ) (hlink : IsProperLink K δ T a)
    (hp : p ∈ translatedVertices K T) (hpa : ℓ a < ℓ p) :
    ∃ q ∈ translatedVertices K T,
      ℓ a ≤ ℓ q ∧ ℓ q < ℓ p ∧ ℓ p - ℓ q ∈ positiveVertexGaps K ℓ := by
  obtain ⟨v, hv, t, ht, rfl⟩ := hp
  obtain ⟨O, hO, hvO⟩ := link_vertex_component hv
  have hf : ℓ.toLinearMap ≠ 0 := by
    intro heq
    apply hℓ
    ext z
    exact congrArg (fun f : Plane →ₗ[ℝ] ℝ => f z) heq
  obtain ⟨w, hw, hwO, hwmin, _⟩ :=
    K.isPolygonal.exists_interiorComponent_min_vertex hO ℓ.toLinearMap hf
  change ∀ z ∈ closure O, ℓ w ≤ ℓ z at hwmin
  by_cases hwv : ℓ w < ℓ v
  · refine ⟨w + t, ⟨w, hw, t, ht, rfl⟩,
      link_component_on_right htile.2.1 hker hlink ht hO hvO hpa w hwO, ?_, ?_⟩
    · simp only [map_add]
      linarith
    · refine ⟨?_,
        w, hw, v, hv, ?_⟩
      · simp only [map_add]
        linarith
      · simp only [map_sub, map_add]
        ring
  · have hvw : ℓ v = ℓ w := le_antisymm (le_of_not_gt hwv) (hwmin v hvO)
    obtain ⟨x, hx, hOx⟩ := hO
    have hleft : IsLeftmostComponentVertex K ℓ v := by
      refine ⟨hv, x, hx, ?_, ?_⟩
      · simpa only [PolygonalRegion.openCarrier, ← hOx] using hvO
      · intro y hy
        rw [PolygonalRegion.openCarrier, ← hOx] at hy
        rw [hvw]
        exact hwmin y hy
    obtain ⟨s, hs, u, hu, hus, y, hy, huO, z, hz, hzlt⟩ :=
      leftmostComponentVertex_switch K T ℓ htile hℓ t ht v hleft
    have hO' : connectedComponentIn K.openCarrier y ∈ interiorComponents K.support :=
      ⟨y, hy, rfl⟩
    obtain ⟨m, hm, hmO, hmmin, _⟩ :=
      K.isPolygonal.exists_interiorComponent_min_vertex hO' ℓ.toLinearMap hf
    change ∀ z ∈ closure (connectedComponentIn K.openCarrier y), ℓ m ≤ ℓ z at hmmin
    have hmu : ℓ m < ℓ u := lt_of_le_of_lt (hmmin z hz) hzlt
    have huright : ℓ a < ℓ (u + s) := by rwa [hus]
    refine ⟨m + s, ⟨m, hm, s, hs, rfl⟩,
      link_component_on_right htile.2.1 hker hlink hs hO' huO huright m hmO, ?_, ?_⟩
    · rw [← hus]
      simp only [map_add]
      linarith
    · rw [← hus]
      refine ⟨?_,
        m, hm, u, hu, ?_⟩
      · simp only [map_add]
        linarith
      · simp only [map_sub, map_add]
        ring

private theorem link_right_word {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} {a : Plane} {ℓ : Plane →L[ℝ] ℝ}
    (htile : TilesOn K T univ) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ) (hlink : IsProperLink K δ T a)
    {c : ℝ} (_hc : 0 < c) (hgap : ∀ r ∈ positiveVertexGaps K ℓ, c ≤ r) :
    ∀ n : ℕ, ∀ p ∈ translatedVertices K T,
      ℓ a ≤ ℓ p → ℓ p - ℓ a < n * c →
        ∃ G : List ℝ, (∀ r ∈ G, r ∈ positiveVertexGaps K ℓ) ∧ ℓ p - ℓ a = G.sum := by
  intro n
  induction n with
  | zero =>
      intro p _ hpa hbound
      simp only [Nat.cast_zero, zero_mul] at hbound
      linarith
  | succ n ih =>
      intro p hp hpa hbound
      by_cases heq : ℓ p = ℓ a
      · exact ⟨[], by simp, by simp [heq]⟩
      · have hstrict : ℓ a < ℓ p := lt_of_le_of_ne hpa (Ne.symm heq)
        obtain ⟨q, hq, hqa, hqp, hpq⟩ := link_right_step htile hℓ hker hlink hp hstrict
        have hdecrease := hgap _ hpq
        have hqbound : ℓ q - ℓ a < n * c := by
          simp only [Nat.cast_succ] at hbound
          nlinarith
        obtain ⟨G, hG, hsum⟩ := ih q hq hqa hqbound
        refine ⟨(ℓ p - ℓ q) :: G, ?_, ?_⟩
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hpq
          · exact hG r hr
        · simp only [List.sum_cons, ← hsum]
          ring

private theorem link_positiveGaps_neg (K : PolygonalRegion) (ℓ : Plane →L[ℝ] ℝ) :
    positiveVertexGaps K (-ℓ) = positiveVertexGaps K ℓ := by
  ext r
  constructor <;> rintro ⟨hr, v, hv, w, hw, heq⟩
  · refine ⟨hr, w, hw, v, hv, ?_⟩
    rw [heq]
    simp only [map_sub, neg_apply]
    ring
  · refine ⟨hr, w, hw, v, hv, ?_⟩
    rw [heq]
    simp only [map_sub, neg_apply]
    ring

theorem link_distance_isPositiveWord :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ), Module.finrank ℝ δ = 1 → ℓ ≠ 0 →
    LinearMap.ker ℓ.toLinearMap = δ → TilesOn K T Set.univ →
      ∀ a : Plane, IsProperLink K δ T a →
        ∀ v ∈ translatedVertices K T, ℓ v ≠ ℓ a →
          ∃ G : List ℝ, G ≠ [] ∧
            (∀ r ∈ G, r ∈ positiveVertexGaps K ℓ) ∧
              |ℓ v - ℓ a| = G.sum
  := by
  intro K δ T ℓ _ hℓ hker htile a hlink v hv hne
  obtain ⟨_, _, c, hc, hgap⟩ := positiveVertexGaps_finitePositive K ℓ hℓ
  by_cases hav : ℓ a ≤ ℓ v
  · obtain ⟨n, hn⟩ := exists_nat_gt ((ℓ v - ℓ a) / c)
    have hbound : ℓ v - ℓ a < n * c := (div_lt_iff₀ hc).mp hn
    obtain ⟨G, hG, hsum⟩ := link_right_word htile hℓ hker hlink hc hgap n v hv hav hbound
    refine ⟨G, ?_, hG, ?_⟩
    · intro hempty
      simp only [hempty, List.sum_nil] at hsum
      exact hne (sub_eq_zero.mp hsum)
    · rwa [abs_of_nonneg (sub_nonneg.mpr hav)]
  · have hva : ℓ v ≤ ℓ a := (lt_of_not_ge hav).le
    have hneg : -ℓ ≠ 0 := neg_ne_zero.mpr hℓ
    have hkerneg : LinearMap.ker (-ℓ).toLinearMap = δ := by
      simpa only [ContinuousLinearMap.toLinearMap_neg, LinearMap.ker_neg] using hker
    have hgapneg : ∀ r ∈ positiveVertexGaps K (-ℓ), c ≤ r := by
      simpa only [link_positiveGaps_neg] using hgap
    obtain ⟨n, hn⟩ := exists_nat_gt ((ℓ a - ℓ v) / c)
    have hbound : (-ℓ) v - (-ℓ) a < n * c := by
      simpa only [neg_apply, neg_sub_neg] using (div_lt_iff₀ hc).mp hn
    obtain ⟨G, hG, hsum⟩ := link_right_word htile hneg hkerneg hlink hc hgapneg n v hv
      (by simpa only [neg_apply] using neg_le_neg hva) hbound
    refine ⟨G, ?_, ?_, ?_⟩
    · intro hempty
      simp only [hempty, List.sum_nil, neg_apply, neg_sub_neg] at hsum
      exact hne (sub_eq_zero.mp hsum).symm
    · simpa only [link_positiveGaps_neg] using hG
    · simpa only [abs_of_nonpos (sub_nonpos.mpr hva), neg_apply,
        neg_sub_neg, neg_sub] using hsum

private theorem link_finite_words {A : Set ℝ} (hA : A.Finite) (n : ℕ) :
    {G : List ℝ | G.length ≤ n ∧ ∀ r ∈ G, r ∈ A}.Finite := by
  induction n with
  | zero =>
      apply (finite_singleton ([] : List ℝ)).subset
      intro G hG
      have hlen : G.length = 0 := Nat.eq_zero_of_le_zero hG.1
      cases G with
      | nil => exact rfl
      | cons r G => simp at hlen
  | succ n ih =>
      apply ((finite_singleton ([] : List ℝ)).union
        ((hA.prod ih).image (fun p : ℝ × List ℝ => p.1 :: p.2))).subset
      intro G hG
      cases G with
      | nil => exact Or.inl rfl
      | cons r G =>
          apply Or.inr
          refine ⟨(r, G), ⟨hG.2 r (by simp), ?_⟩, rfl⟩
          refine ⟨by simpa using hG.1, ?_⟩
          intro s hs
          exact hG.2 s (List.mem_cons_of_mem r hs)

private theorem link_word_lowerBound {A : Set ℝ} {c : ℝ}
    (hA : ∀ r ∈ A, c ≤ r) (G : List ℝ) (hG : ∀ r ∈ G, r ∈ A) :
    G.length * c ≤ G.sum := by
  induction G with
  | nil => simp
  | cons r G ih =>
      have hr := hA r (hG r (by simp))
      have htail := ih (fun s hs => hG s (List.mem_cons_of_mem r hs))
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.sum_cons]
      nlinarith

private theorem link_bounded_offsets {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} {ℓ : Plane →L[ℝ] ℝ}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T univ) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ) (B : ℝ) :
    ∃ F : Set ℝ, F.Finite ∧ ∀ a, IsProperLink K δ T a → ∀ p ∈ translatedVertices K T,
      |ℓ p - ℓ a| ≤ B → ℓ p - ℓ a ∈ F := by
  obtain ⟨hGfinite, _, c, hc, hgap⟩ := positiveVertexGaps_finitePositive K ℓ hℓ
  obtain ⟨N, hN⟩ := exists_nat_gt (B / c)
  let W : Set (List ℝ) := {G | G.length ≤ N ∧ ∀ r ∈ G, r ∈ positiveVertexGaps K ℓ}
  let C : Set ℝ := List.sum '' W
  have hC : C.Finite := (link_finite_words hGfinite N).image List.sum
  refine ⟨C ∪ (fun r : ℝ => -r) '' C, hC.union (hC.image _), ?_⟩
  intro a hlink p hp hbound
  have habs : |ℓ p - ℓ a| ∈ C := by
    by_cases heq : ℓ p = ℓ a
    · refine ⟨[], ⟨by simp, by simp⟩, ?_⟩
      simp [heq]
    · obtain ⟨G, _, hG, hsum⟩ := link_distance_isPositiveWord K δ T ℓ hδ hℓ hker
        htile a hlink p hp heq
      have hlenlower := link_word_lowerBound hgap G hG
      have hlen : G.length ≤ N := by
        have hlenR : (G.length : ℝ) < N := by
          have hBN : B < N * c := (div_lt_iff₀ hc).mp hN
          nlinarith
        exact_mod_cast hlenR.le
      exact ⟨G, ⟨hlen, hG⟩, hsum.symm⟩
  by_cases hnonneg : 0 ≤ ℓ p - ℓ a
  · exact Or.inl (by rwa [abs_of_nonneg hnonneg] at habs)
  · refine Or.inr ⟨|ℓ p - ℓ a|, habs, ?_⟩
    simp [abs_of_nonpos (le_of_not_ge hnonneg)]

private theorem link_transverse_functional (δ : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) :
    ∃ ℓ : Plane →L[ℝ] ℝ, ℓ ≠ 0 ∧ LinearMap.ker ℓ.toLinearMap = δ := by
  have hδtop : δ < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    rw [htop] at hδ
    norm_num [Plane, Complex.finrank_real_complex] at hδ
  obtain ⟨f, hf, hfδ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hδtop inferInstance
  have hδker : δ ≤ LinearMap.ker f := by
    intro x hx
    have hfx : f x ∈ δ.map f := ⟨x, hx, rfl⟩
    simpa only [hfδ, Submodule.mem_bot, LinearMap.mem_ker] using hfx
  have hkerproper : LinearMap.ker f < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    apply hf
    ext x
    have hx : x ∈ LinearMap.ker f := htop.symm ▸ mem_univ x
    exact hx
  have hkerdim : Module.finrank ℝ (LinearMap.ker f) = 1 := by
    have hle := Submodule.finrank_mono hδker
    have hlt := Submodule.finrank_lt_finrank_of_lt hkerproper
    rw [hδ] at hle
    norm_num [Plane, Complex.finrank_real_complex] at hlt
    omega
  have hkereq : LinearMap.ker f = δ :=
    (Submodule.eq_of_le_of_finrank_eq hδker (hδ.trans hkerdim.symm)).symm
  refine ⟨LinearMap.toContinuousLinearMap f, ?_, hkereq⟩
  intro heq
  apply hf
  ext x
  exact congrArg (fun g : Plane →L[ℝ] ℝ => g x) heq

theorem uniformlyReady_transverseFLC :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    Module.finrank ℝ δ = 1 → TilesOn K T Set.univ →
      IsUniformlyReady K δ T → HasTransverseFLC K δ T
  := by
  intro K δ T hδ htile hready
  obtain ⟨R, hR, hready⟩ := hready
  obtain ⟨ℓ, hℓ, hker⟩ := link_transverse_functional δ hδ
  refine ⟨ℓ, hℓ, hker, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨B, hB⟩ := hQ.subset_closedBall (0 : ℝ)
    obtain ⟨a, ha, _⟩ := hready 0
    obtain ⟨F, hF, hOffsets⟩ := link_bounded_offsets hδ htile hℓ hker (B + |ℓ a|)
    apply (hF.image (fun r => ℓ a + r)).subset
    rintro r ⟨hr, hrQ⟩
    obtain ⟨p, hp, rfl⟩ := hr
    have hproj : |ℓ p| ≤ B := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hB hrQ
    have hbound : |ℓ p - ℓ a| ≤ B + |ℓ a| :=
      (abs_sub _ _).trans (add_le_add hproj le_rfl)
    exact ⟨ℓ p - ℓ a, hOffsets a ha p hp hbound, by ring⟩
  · intro B hB
    let C : ℝ := ‖ℓ‖ * R
    obtain ⟨F, hF, hOffsets⟩ := link_bounded_offsets hδ htile hℓ hker (C + B)
    apply (hF.sub hF).subset
    rintro r ⟨hr, hrball⟩
    obtain ⟨p', hp', q', hq', rfl⟩ := hr
    obtain ⟨p, hp, rfl⟩ := hp'
    obtain ⟨q, hq, rfl⟩ := hq'
    obtain ⟨a, ha, hdist⟩ := hready p
    have hpa : |ℓ p - ℓ a| ≤ C := by
      calc
        |ℓ p - ℓ a| = dist (ℓ p) (ℓ a) := (Real.dist_eq _ _).symm
        _ ≤ ‖ℓ‖ * dist p a := ℓ.dist_le_opNorm p a
        _ ≤ C := mul_le_mul_of_nonneg_left hdist.le (norm_nonneg _)
    have hpq : |ℓ p - ℓ q| ≤ B := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hrball
    have hqa : |ℓ q - ℓ a| ≤ C + B := by
      calc
        |ℓ q - ℓ a| ≤ |ℓ q - ℓ p| + |ℓ p - ℓ a| := abs_sub_le _ _ _
        _ = |ℓ p - ℓ q| + |ℓ p - ℓ a| := by rw [abs_sub_comm (ℓ q) (ℓ p)]
        _ ≤ B + C := add_le_add hpq hpa
        _ = C + B := add_comm _ _
    have hpa' : |ℓ p - ℓ a| ≤ C + B := hpa.trans (le_add_of_nonneg_right hB.le)
    refine ⟨ℓ p - ℓ a, hOffsets a ha p hp hpa', ℓ q - ℓ a,
      hOffsets a ha q hq hqa, ?_⟩
    ring

theorem uniformlyReady_closedUnderTranslatedLimits :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T S : Set Plane),
    Module.finrank ℝ δ = 1 → TilesOn K T Set.univ →
    IsUniformlyReady K δ T → ∀ g : ℕ → Plane,
      Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S →
        IsUniformlyReady K δ S
  := by
  intro K δ T S _ htile hready g hconv
  obtain ⟨R, hR, hready⟩ := hready
  have htiles : ∀ n, TilesOn K (g n +ᵥ T) univ := by
    intro n
    simpa using tilesOn_translate htile (g n)
  refine ⟨R + 1, by linarith, ?_⟩
  intro x
  choose a hlink hd using fun n => link_ready_translate hready (g n) x
  have hacompact : ∀ n, a n ∈ Metric.closedBall x R := by
    intro n
    simpa only [Metric.mem_closedBall, dist_comm] using (hd n).le
  obtain ⟨b, hb, φ, hφ, ha⟩ := (isCompact_closedBall x R).tendsto_subseq hacompact
  refine ⟨b, link_limit (fun n => htiles (φ n)) (link_fell_subseq hconv hφ) ha
    (fun n => hlink (φ n)), ?_⟩
  have hdist : dist x b ≤ R := by
    simpa only [Metric.mem_closedBall, dist_comm] using hb
  linarith

end Tiling.RationalSlopes

/- Kernel audit: the switch body remains an explicit local development hole.
All predecessor theorem calls listed here are provisional skeleton bodies. -/
