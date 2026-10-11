import Tiling.RationalSlopes.Approximation.RationalLineGeometry
import Tiling.RationalSlopes.Links


set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology

noncomputable section

namespace Tiling.RationalSlopes.Approximation

open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Approximation
open Tiling.Polygonal

private theorem normalEval_sub (n : RationalNormal) (x y : Plane) :
    normalEval n (x - y) = normalEval n x - normalEval n y := by
  simp [normalEval, Complex.sub_re, Complex.sub_im]
  ring

private theorem normalDirection_mem_iff (n : RationalNormal) (z : Plane) :
    z ∈ normalDirection n ↔ normalEval n z = 0 := by
  change (((n.x : ℝ) • Complex.reCLM + (n.y : ℝ) • Complex.imCLM).toLinearMap) z = 0 ↔ _
  simp [normalEval]

private theorem list_sum_deformation_bounds
    (φ : ℝ →ₗ[ℚ] ℚ) (G : List ℝ)
    (hG : ∀ r ∈ G, r / 2 ≤ (φ r : ℝ) ∧ (φ r : ℝ) ≤ 2 * r) :
    G.sum / 2 ≤ (φ G.sum : ℝ) ∧ (φ G.sum : ℝ) ≤ 2 * G.sum := by
  induction G with
  | nil => simp
  | cons r G ih =>
      have hr := hG r (by simp)
      have htail : ∀ q ∈ G, q / 2 ≤ (φ q : ℝ) ∧ (φ q : ℝ) ≤ 2 * q :=
        fun q hq => hG q (by simp [hq])
      have hsum := ih htail
      have hmap : (φ (r + G.sum) : ℝ) = (φ r : ℝ) + (φ G.sum : ℝ) := by
        exact_mod_cast (map_add φ r G.sum)
      rw [List.sum_cons, hmap]
      constructor <;> nlinarith

private theorem signed_deformation_bounds (φ : ℝ →ₗ[ℚ] ℚ) (x : ℝ)
    (hbounds : |x| / 2 ≤ (φ |x| : ℝ) ∧ (φ |x| : ℝ) ≤ 2 * |x|) :
    Real.sign (φ x : ℝ) = Real.sign x ∧
      |x| / 2 ≤ |(φ x : ℝ)| ∧ |(φ x : ℝ)| ≤ 2 * |x| := by
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · have hmap : (φ |x| : ℝ) = -(φ x : ℝ) := by simp [abs_of_neg hneg]
    have hφneg : (φ x : ℝ) < 0 := by rw [hmap] at hbounds; rw [abs_of_neg hneg] at hbounds; linarith
    refine ⟨by rw [Real.sign_of_neg hφneg, Real.sign_of_neg hneg], ?_⟩
    simpa [abs_of_neg hφneg, hmap] using hbounds
  · simp
  · have hφpos : 0 < (φ x : ℝ) := by rw [abs_of_pos hpos] at hbounds; linarith
    refine ⟨by rw [Real.sign_of_pos hφpos, Real.sign_of_pos hpos], ?_⟩
    simpa [abs_of_pos hφpos, abs_of_pos hpos] using hbounds

private theorem originalIndexedCopies_locallyFinite (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) :
    LocallyFinite (fun t : T => (t : Plane) +ᵥ K.support) := by
  obtain ⟨R, hR, hbound⟩ := K.isPolygonal.isBounded.exists_pos_norm_le
  intro x
  let A : Set Plane := T ∩ Metric.closedBall 0 (‖x‖ + 1 + R)
  have hA : A.Finite := (Tiling.Polygonal.packing_centres_locallyFinite hpack).1 _
    Metric.isBounded_closedBall
  have hfinite : {t : T | t.1 ∈ A}.Finite := hA.preimage Subtype.val_injective.injOn
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), hfinite.subset ?_⟩
  rintro t ⟨y, hyt, hyx⟩
  have hz : (-t.1 +ᵥ y) ∈ K.support := Set.mem_vadd_set_iff_neg_vadd_mem.mp hyt
  have hnormy : ‖y‖ ≤ ‖x‖ + 1 := by
    have hd : ‖y - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hyx
    have htriangle : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
    linarith
  have hnormt : ‖t.1‖ ≤ ‖x‖ + 1 + R := by
    have heq : t.1 = y - (-t.1 +ᵥ y) := by change t.1 = y - (-t.1 + y); abel
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add hnormy (hbound _ hz))
  exact ⟨t.2, by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hnormt⟩

private theorem intrinsicVertex_mem_support (K : PolygonalRegion)
    {v : Plane} (hv : v ∈ Tiling.vertexSet K.support) : v ∈ K.support := by
  obtain ⟨A⟩ := K.isPolygonal
  obtain ⟨C, hC, hvC⟩ := hv A
  rw [← A.sUnion_eq]
  exact Set.mem_sUnion.mpr ⟨C, hC, extremePoints_subset hvC⟩

private theorem originalVertexStar_finite (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) (v : Plane) :
    {t : T | v ∈ (t : Plane) +ᵥ Tiling.vertexSet K.support}.Finite := by
  apply ((originalIndexedCopies_locallyFinite K T hpack).point_finite v).subset
  intro t ht
  apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
  exact intrinsicVertex_mem_support K (Set.mem_vadd_set_iff_neg_vadd_mem.mp ht)

private theorem originalClosedCopies_coverPlane (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    (⋃ t : T, (t : Plane) +ᵥ K.support) = Set.univ := by
  rw [← Tiling.Polygonal.closure_openUnion_eq_iUnion_support htile.2.1]
  have hfull := Tiling.Polygonal.regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hsubset : Set.univ ⊆ closure (Tiling.Polygonal.openUnion K T) := by
    rw [← hfull]
    exact interior_subset
  exact Set.eq_univ_of_univ_subset hsubset

private theorem originalClosedStar_localCover (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (v : Plane) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Metric.ball v r,
      ∃ t ∈ T, v ∈ t +ᵥ K.support ∧ x ∈ t +ᵥ K.support := by
  classical
  let E : T → Set Plane := fun t =>
    if v ∈ (t : Plane) +ᵥ K.support then ∅ else (t : Plane) +ᵥ K.support
  have hEsub (t : T) : E t ⊆ (t : Plane) +ᵥ K.support := by
    dsimp [E]
    split_ifs <;> simp
  have hElf := (originalIndexedCopies_locallyFinite K T htile.2.1).subset hEsub
  have hEclosed : IsClosed (⋃ t, E t) := hElf.isClosed_iUnion (fun t => by
    dsimp [E]
    split_ifs
    · exact isClosed_empty
    · exact K.isPolygonal.isClosed.vadd _)
  have hv : v ∈ (⋃ t, E t)ᶜ := by
    intro hv
    obtain ⟨t, hvt⟩ := Set.mem_iUnion.mp hv
    dsimp [E] at hvt
    split_ifs at hvt with hvtile
    · exact hvt
    · exact hvtile hvt
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hEclosed.isOpen_compl v hv
  refine ⟨r, hr, ?_⟩
  intro x hx
  have hxcover : x ∈ ⋃ t : T, (t : Plane) +ᵥ K.support := by
    rw [originalClosedCopies_coverPlane K T htile]
    exact Set.mem_univ _
  obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hxcover
  refine ⟨t, t.2, ?_, hxt⟩
  by_contra hvnot
  apply hball hx
  exact Set.mem_iUnion.mpr ⟨t, by simpa [E, hvnot] using hxt⟩

private theorem original_openCarrier_disjoint_otherSupport (K : PolygonalRegion)
    (T : Set Plane) (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    {s t : Plane} (hs : s ∈ T) (ht : t ∈ T) (hst : s ≠ t) :
    Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.support) := by
  have hdisj := (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K T).mp hpack hs ht hst
  have h := hdisj.closure_right (isOpen_interior.vadd s)
  rw [closure_vadd] at h
  simpa only [PolygonalRegion.openCarrier, K.isPolygonal.closure_interior] using h

private theorem originalVertex_otherLabels_noninterior (K : PolygonalRegion)
    (T : Set Plane) (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    {s t v : Plane} (hs : s ∈ T) (ht : t ∈ T) (hst : s ≠ t)
    (hv : v ∈ t +ᵥ Tiling.vertexSet K.support) : v ∉ s +ᵥ K.openCarrier := by
  intro hvs
  have hvt : v ∈ t +ᵥ K.support := Set.mem_vadd_set_iff_neg_vadd_mem.mpr
    (intrinsicVertex_mem_support K (Set.mem_vadd_set_iff_neg_vadd_mem.mp hv))
  exact Set.disjoint_left.mp (original_openCarrier_disjoint_otherSupport K T hpack hs ht hst) hvs hvt

private theorem originalNonvertexStar_localHalfPlane (K : PolygonalRegion)
    (T : Set Plane) (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    {s t v : Plane} (hs : s ∈ T) (ht : t ∈ T)
    (hvt : v ∈ t +ᵥ Tiling.vertexSet K.support)
    (hvs : v ∈ s +ᵥ K.support) (hvnot : v ∉ s +ᵥ Tiling.vertexSet K.support) :
    ∃ u : Plane, u ≠ 0 ∧ ∃ r > 0,
      ((s +ᵥ K.support) ∩ Metric.ball v r = Tiling.positiveHalfPlane v u ∩ Metric.ball v r ∨
        (s +ᵥ K.support) ∩ Metric.ball v r = Tiling.negativeHalfPlane v u ∩ Metric.ball v r) := by
  have hst : s ≠ t := by
    intro heq
    subst t
    exact hvnot hvt
  have hvint := originalVertex_otherLabels_noninterior K T hpack hs ht hst hvt
  have hvfrontier : v ∈ frontier (s +ᵥ K.support) := by
    rw [(K.isPolygonal.isClosed.vadd s).frontier_eq, interior_vadd]
    exact ⟨hvs, hvint⟩
  have hpolygonal : Tiling.IsPolygonal (s +ᵥ K.support) := K.isPolygonal.vadd s
  have hvnot' : v ∉ Tiling.vertexSet (s +ᵥ K.support) := by
    simpa only [Tiling.vertexSet_vadd] using hvnot
  obtain ⟨L, hvL, hdim, hlocal⟩ :=
    hpolygonal.boundaryLocallyStraightAt_of_not_mem_vertexSet hvfrontier hvnot'
  apply Tiling.exists_local_eq_closedHalfPlane_of_affineSubspace _ hvL hdim hlocal
  rw [interior_vadd, closure_vadd, K.isPolygonal.closure_interior]

private theorem no_third_regularClosed_incident_to_two_halfPlaneGerms
    (A B C : Set Plane) (p : Plane)
    (f g : Plane →L[ℝ] ℝ)
    (rA rB : ℝ) (hrA : 0 < rA) (hrB : 0 < rB)
    (hA : ∀ q, dist q p < rA → (q ∈ A ↔ 0 ≤ f (q - p)))
    (hB : ∀ q, dist q p < rB → (q ∈ B ↔ 0 ≤ g (q - p)))
    (hAB : Disjoint (interior A) B)
    (hCA : Disjoint (interior C) A)
    (hCB : Disjoint (interior C) B)
    (hpC : p ∈ C)
    (hCreg : C ⊆ closure (interior C)) : False := by
  let ε : ℝ := min rA rB
  have hε : 0 < ε := lt_min hrA hrB
  have hnotBoth : ∀ w : Plane, ¬ (0 < f w ∧ 0 < g w) := by
    intro w hw
    have hwne : w ≠ 0 := by
      intro hzero
      subst w
      simp at hw
    have hwNorm : 0 < ‖w‖ := norm_pos_iff.mpr hwne
    obtain ⟨t, ht0, htbound⟩ := exists_between (show 0 < ε / ‖w‖ by positivity)
    let q : Plane := p + t • w
    have hqp : q - p = t • w := by simp [q]
    have hdist : dist q p < ε := by
      rw [show q = p + t • w by rfl, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      calc
        t * ‖w‖ < (ε / ‖w‖) * ‖w‖ := mul_lt_mul_of_pos_right htbound hwNorm
        _ = ε := by field_simp
    have hfq : 0 < f (q - p) := by
      rw [hqp, map_smul]
      exact mul_pos ht0 hw.1
    have hgq : 0 < g (q - p) := by
      rw [hqp, map_smul]
      exact mul_pos ht0 hw.2
    have hqballA : dist q p < rA := lt_of_lt_of_le hdist (min_le_left _ _)
    have hqballB : dist q p < rB := lt_of_lt_of_le hdist (min_le_right _ _)
    have hqA : q ∈ A := (hA q hqballA).2 (le_of_lt hfq)
    have hqB : q ∈ B := (hB q hqballB).2 (le_of_lt hgq)
    have hOopen : IsOpen (Metric.ball p rA ∩ {z | 0 < f (z - p)}) := by
      exact IsOpen.inter Metric.isOpen_ball
        (IsOpen.preimage (f.continuous.comp (continuous_id.sub continuous_const)) isOpen_Ioi)
    have hOsub : Metric.ball p rA ∩ {z | 0 < f (z - p)} ⊆ A := by
      intro z hz
      exact (hA z hz.1).2 (le_of_lt hz.2)
    have hqO : q ∈ Metric.ball p rA ∩ {z | 0 < f (z - p)} := ⟨hqballA, hfq⟩
    have hqInterior : q ∈ interior A := interior_maximal hOsub hOopen hqO
    exact (Set.disjoint_left.mp hAB) hqInterior hqB
  have hcover : ∀ q, dist q p < ε → q ∈ A ∪ B := by
    intro q hq
    by_cases hqf : 0 ≤ f (q - p)
    · exact Or.inl ((hA q (lt_of_lt_of_le hq (min_le_left _ _))).2 hqf)
    · have hqg : 0 ≤ g (q - p) := by
        by_contra hqg
        have hqfneg : f (q - p) < 0 := lt_of_not_ge hqf
        have hqgneg : g (q - p) < 0 := lt_of_not_ge hqg
        have hpos := hnotBoth (-(q - p))
        apply hpos
        constructor
        · rw [map_neg]
          linarith
        · rw [map_neg]
          linarith
      exact Or.inr ((hB q (lt_of_lt_of_le hq (min_le_right _ _))).2 hqg)
  have hpClosure : p ∈ closure (interior C) := hCreg hpC
  obtain ⟨q, hqInterior, hdistPQ⟩ := Metric.mem_closure_iff.mp hpClosure ε hε
  have hqdist : dist q p < ε := by simpa [dist_comm] using hdistPQ
  have hqAB := hcover q hqdist
  rcases hqAB with hqA | hqB
  · exact (Set.disjoint_left.mp hCA) hqInterior hqA
  · exact (Set.disjoint_left.mp hCB) hqInterior hqB

/-- Re-express the concrete `LocalLine` positive/negative half-plane germ as
the continuous-linear-functional germ used by the packing contradiction. -/
private theorem localHalfPlane_to_linearGerm
    (A : Set Plane) (p : Plane)
    (hloc : ∃ v : Plane, v ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (A ∩ Metric.ball p r = Tiling.positiveHalfPlane p v ∩ Metric.ball p r ∨
       A ∩ Metric.ball p r = Tiling.negativeHalfPlane p v ∩ Metric.ball p r)) :
    ∃ f : Plane →L[ℝ] ℝ, ∃ r : ℝ, 0 < r ∧
      ∀ q, dist q p < r → (q ∈ A ↔ 0 ≤ f (q - p)) := by
  obtain ⟨v, hv, r, hr, hcase⟩ := hloc
  have hside (q : Plane) : Tiling.signedSide p v q =
      Tiling.planarCrossCLM v (q - p) := by
    rw [Tiling.planarCrossCLM_apply]
    simp [Tiling.signedSide, Tiling.planarCross, Complex.sub_re, Complex.sub_im]
    ring
  rcases hcase with hpos | hneg
  · refine ⟨Tiling.planarCrossCLM v, r, hr, ?_⟩
    intro q hqp
    have hball : q ∈ Metric.ball p r := by
      simpa [Metric.mem_ball, dist_comm] using hqp
    have hmem : q ∈ A ↔ q ∈ Tiling.positiveHalfPlane p v := by
      have hEq := congrArg (fun S : Set Plane => q ∈ S) hpos
      simpa [Set.mem_inter_iff, hball] using hEq
    rw [hmem, Tiling.mem_positiveHalfPlane, hside]
  · refine ⟨-Tiling.planarCrossCLM v, r, hr, ?_⟩
    intro q hqp
    have hball : q ∈ Metric.ball p r := by
      simpa [Metric.mem_ball, dist_comm] using hqp
    have hmem : q ∈ A ↔ q ∈ Tiling.negativeHalfPlane p v := by
      have hEq := congrArg (fun S : Set Plane => q ∈ S) hneg
      simpa [Set.mem_inter_iff, hball] using hEq
    rw [hmem, Tiling.mem_negativeHalfPlane, hside]
    simp [map_neg]

/-- Packing form of the preceding two lemmas: two concrete local line sides
cannot meet a third regular-closed support at the same point. -/
private theorem no_third_regularClosed_incident_to_two_localHalfPlanes
    (A B C : Set Plane) (p : Plane)
    (hAline : ∃ v : Plane, v ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (A ∩ Metric.ball p r = Tiling.positiveHalfPlane p v ∩ Metric.ball p r ∨
       A ∩ Metric.ball p r = Tiling.negativeHalfPlane p v ∩ Metric.ball p r))
    (hBline : ∃ v : Plane, v ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (B ∩ Metric.ball p r = Tiling.positiveHalfPlane p v ∩ Metric.ball p r ∨
       B ∩ Metric.ball p r = Tiling.negativeHalfPlane p v ∩ Metric.ball p r))
    (hAB : Disjoint (interior A) B)
    (hCA : Disjoint (interior C) A)
    (hCB : Disjoint (interior C) B)
    (hpC : p ∈ C)
    (hCreg : C ⊆ closure (interior C)) : False := by
  obtain ⟨f, rA, hrA, hAgerm⟩ := localHalfPlane_to_linearGerm A p hAline
  obtain ⟨g, rB, hrB, hBgerm⟩ := localHalfPlane_to_linearGerm B p hBline
  exact no_third_regularClosed_incident_to_two_halfPlaneGerms
    A B C p f g rA rB hrA hrB hAgerm hBgerm hAB hCA hCB hpC hCreg

private theorem originalVertexStar_atMostOneSmoothLabel (K : PolygonalRegion)
    (T : Set Plane) (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (p t : Plane) (ht : t ∈ T) (hpt : p ∈ t +ᵥ Tiling.vertexSet K.support)
    (s u : Plane) (hs : s ∈ T) (hu : u ∈ T)
    (hps : p ∈ s +ᵥ K.support) (hpu : p ∈ u +ᵥ K.support)
    (hpsnot : p ∉ s +ᵥ Tiling.vertexSet K.support)
    (hpunot : p ∉ u +ᵥ Tiling.vertexSet K.support) : s = u := by
  by_contra hsu
  have hts : t ≠ s := by
    intro heq
    apply hpsnot
    rwa [← heq]
  have htu : t ≠ u := by
    intro heq
    apply hpunot
    rwa [← heq]
  apply no_third_regularClosed_incident_to_two_localHalfPlanes
    (s +ᵥ K.support) (u +ᵥ K.support) (t +ᵥ K.support) p
    (originalNonvertexStar_localHalfPlane K T hpack hs ht hpt hps hpsnot)
    (originalNonvertexStar_localHalfPlane K T hpack hu ht hpt hpu hpunot)
  · rw [interior_vadd]
    exact original_openCarrier_disjoint_otherSupport K T hpack hs hu hsu
  · rw [interior_vadd]
    exact original_openCarrier_disjoint_otherSupport K T hpack ht hs hts
  · rw [interior_vadd]
    exact original_openCarrier_disjoint_otherSupport K T hpack ht hu htu
  · exact Set.mem_vadd_set_iff_neg_vadd_mem.mpr
      (intrinsicVertex_mem_support K (Set.mem_vadd_set_iff_neg_vadd_mem.mp hpt))
  · rw [interior_vadd, closure_vadd, K.isPolygonal.closure_interior]

private def normalCLM (n : RationalNormal) : Plane →L[ℝ] ℝ :=
  (n.x : ℝ) • Complex.reCLM + (n.y : ℝ) • Complex.imCLM

private theorem normalCLM_apply (n : RationalNormal) (z : Plane) :
    normalCLM n z = normalEval n z := by
  simp [normalCLM, normalEval]

private theorem normalCLM_ne_zero (n : RationalNormal) : normalCLM n ≠ 0 := by
  intro h
  have hx : (n.x : ℝ) = 0 := by
    simpa [normalCLM] using congrArg (fun f : Plane →L[ℝ] ℝ => f 1) h
  have hy : (n.y : ℝ) = 0 := by
    simpa [normalCLM] using congrArg (fun f : Plane →L[ℝ] ℝ => f Complex.I) h
  rcases n.nonzero with hnx | hny
  · exact hnx (by exact_mod_cast hx)
  · exact hny (by exact_mod_cast hy)

private theorem component_normalProjection (K : PolygonalRegion) (n : RationalNormal)
    (O : Set Plane) (hO : O ∈ Tiling.interiorComponents K.support) :
    ∃ a b : Plane, a ∈ Tiling.vertexSet K.support ∧ b ∈ Tiling.vertexSet K.support ∧
      a ∈ closure O ∧ b ∈ closure O ∧
      normalEval n a < normalEval n b ∧
      normalEval n '' O = Set.Ioo (normalEval n a) (normalEval n b) := by
  let ℓ := normalCLM n
  have hℓ : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply normalCLM_ne_zero n
    ext z
    exact congrArg (fun f : Plane →ₗ[ℝ] ℝ => f z) h
  obtain ⟨a, haV, haO, _, ha⟩ :=
    K.isPolygonal.exists_interiorComponent_min_vertex hO ℓ.toLinearMap hℓ
  obtain ⟨b, hbV, hbO, _, hb⟩ :=
    K.isPolygonal.exists_interiorComponent_max_vertex hO ℓ.toLinearMap hℓ
  have hconnected := (Tiling.interiorComponent_basic hO).2.1
  obtain ⟨z, hz⟩ := hconnected.nonempty
  refine ⟨a, b, haV, hbV, haO, hbO, ?_, ?_⟩
  · simpa only [ContinuousLinearMap.coe_coe, ℓ, normalCLM_apply] using (ha z hz).trans (hb z hz)
  · haveI : NeBot (𝓝[O] a) := mem_closure_iff_nhdsWithin_neBot.mp haO
    haveI : NeBot (𝓝[O] b) := mem_closure_iff_nhdsWithin_neBot.mp hbO
    apply Set.Subset.antisymm
    · rintro r ⟨w, hw, rfl⟩
      exact ⟨by simpa only [ContinuousLinearMap.coe_coe, ℓ, normalCLM_apply] using ha w hw,
        by simpa only [ContinuousLinearMap.coe_coe, ℓ, normalCLM_apply] using hb w hw⟩
    · have hbetween := hconnected.isPreconnected.intermediate_value_Ioo
        (l₁ := 𝓝[O] a) (l₂ := 𝓝[O] b)
        (inf_le_right : 𝓝[O] a ≤ 𝓟 O)
        (inf_le_right : 𝓝[O] b ≤ 𝓟 O) ℓ.continuous.continuousOn
        (ℓ.continuous.tendsto a |>.mono_left nhdsWithin_le_nhds)
        (ℓ.continuous.tendsto b |>.mono_left nhdsWithin_le_nhds)
      simpa only [ℓ, normalCLM_apply] using hbetween

theorem openNormalProjection_finiteIntervals :
  ∀ (K : PolygonalRegion) (n : RationalNormal), ∃ I : Finset (ℝ × ℝ),
    normalEval n '' K.openCarrier = ⋃ e ∈ I, Set.Ioo e.1 e.2 ∧
    ∀ e ∈ I, e.1 < e.2 ∧
      (∃ v ∈ Tiling.vertexSet K.support, normalEval n v = e.1) ∧
      (∃ v ∈ Tiling.vertexSet K.support, normalEval n v = e.2) := by
  intro K n
  classical
  let C := Tiling.interiorComponents K.support
  have hfinite : C.Finite := K.isPolygonal.interiorComponents_finite
  letI : Fintype C := hfinite.fintype
  have hex (O : C) := component_normalProjection K n O.1 O.2
  choose a b ha hb haO hbO hab himage using hex
  let e : C → ℝ × ℝ := fun O => (normalEval n (a O), normalEval n (b O))
  refine ⟨Finset.univ.image e, ?_, ?_⟩
  · ext r
    constructor
    · rintro ⟨z, hz, rfl⟩
      let O : C := ⟨connectedComponentIn K.openCarrier z, z, hz, rfl⟩
      have hzO : z ∈ (O : Set Plane) := mem_connectedComponentIn hz
      have he : normalEval n z ∈ Set.Ioo (e O).1 (e O).2 := by
        rw [← himage O]
        exact ⟨z, hzO, rfl⟩
      exact Set.mem_iUnion.mpr ⟨e O, Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨O, Finset.mem_univ _, rfl⟩, he⟩⟩
    · intro hr
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hr
      obtain ⟨hpI, hrp⟩ := Set.mem_iUnion.mp hp
      obtain ⟨O, _, rfl⟩ := Finset.mem_image.mp hpI
      rw [← himage O] at hrp
      obtain ⟨z, hz, hzr⟩ := hrp
      exact ⟨z, (Tiling.interiorComponent_basic O.2).2.2 hz, hzr⟩
  · intro p hp
    obtain ⟨O, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hab O, ⟨a O, ha O, rfl⟩, ⟨b O, hb O, rfl⟩⟩

private theorem sign_eq_iff_nonpos {x y : ℝ} (h : Real.sign x = Real.sign y) :
    x ≤ 0 ↔ y ≤ 0 := by
  constructor
  · intro hx
    by_contra hy
    have hypos : 0 < y := lt_of_not_ge hy
    by_cases hx0 : x = 0
    · simp [hx0, Real.sign_of_pos hypos] at h
    · have hxneg : x < 0 := lt_of_le_of_ne hx hx0
      rw [Real.sign_of_neg hxneg, Real.sign_of_pos hypos] at h
      norm_num at h
  · intro hy
    by_contra hx
    have hxpos : 0 < x := lt_of_not_ge hx
    by_cases hy0 : y = 0
    · simp [hy0, Real.sign_of_pos hxpos] at h
    · have hyneg : y < 0 := lt_of_le_of_ne hy hy0
      rw [Real.sign_of_pos hxpos, Real.sign_of_neg hyneg] at h
      norm_num at h

private theorem arrangement_polyhedralSupport_transport :
    ∀ (P : PolyhedralCode) (φ : ℝ →ₗ[ℚ] ℚ) (H : Plane ≃ₜ Plane),
      (∀ l ∈ P.flatten, ∀ z,
        Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z)) →
      ∀ z, z ∈ polyhedralSupport P ↔
        H z ∈ deformedPolyhedralSupport P φ := by
  intro P φ H hsign z
  constructor
  · rintro ⟨cell, hcell, hlines⟩
    refine ⟨cell.map (deformLine φ), List.mem_map.mpr ⟨cell, hcell, rfl⟩, ?_⟩
    intro l hl
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
    exact (sign_eq_iff_nonpos (hsign l₀
      (List.mem_flatten.mpr ⟨cell, hcell, hl₀⟩) z)).mpr (hlines l₀ hl₀)
  · intro hdeformed
    change ∃ cell ∈ P.map (fun cell => cell.map (deformLine φ)),
      ∀ l ∈ cell, l.eval (H z) ≤ 0 at hdeformed
    obtain ⟨cell', hcell', hlines⟩ := hdeformed
    obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hcell'
    refine ⟨cell, hcell, ?_⟩
    intro l hl
    have hline := hlines (deformLine φ l)
      (List.mem_map.mpr ⟨l, hl, rfl⟩)
    exact (sign_eq_iff_nonpos (hsign l
      (List.mem_flatten.mpr ⟨cell, hcell, hl⟩) z)).mp hline

private theorem sign_eq_iff_pos {x y : ℝ} (h : Real.sign x = Real.sign y) :
    0 < x ↔ 0 < y := by
  simpa only [not_le] using not_congr (sign_eq_iff_nonpos h)

private theorem sign_eq_iff_neg {x y : ℝ} (h : Real.sign x = Real.sign y) :
    x < 0 ↔ y < 0 := by
  have hneg : Real.sign (-x) = Real.sign (-y) := by rw [Real.sign_neg, Real.sign_neg, h]
  simpa only [neg_pos] using sign_eq_iff_pos hneg

theorem openNormalProjection_deformation :
  ∀ (K : PolygonalRegion) (P : PolyhedralCode) (n : RationalNormal),
    polyhedralSupport P = K.support →
      ∃ I : Finset (ℝ × ℝ),
        normalEval n '' K.openCarrier = ⋃ e ∈ I, Set.Ioo e.1 e.2 ∧
        (∀ e ∈ I, e.1 < e.2 ∧
          (∃ v ∈ Tiling.vertexSet K.support, normalEval n v = e.1) ∧
          (∃ v ∈ Tiling.vertexSet K.support, normalEval n v = e.2)) ∧
        ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
          ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
            ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
              normalEval n '' Kφ.openCarrier =
                ⋃ e ∈ I, Set.Ioo (φ e.1 : ℝ) (φ e.2 : ℝ) := by
  intro K P n hP
  classical
  let C := Tiling.interiorComponents K.support
  have hfinite : C.Finite := K.isPolygonal.interiorComponents_finite
  letI : Fintype C := hfinite.fintype
  have hex (O : C) := component_normalProjection K n O.1 O.2
  choose a b ha hb haO hbO hab himage using hex
  let e : C → ℝ × ℝ := fun O => (normalEval n (a O), normalEval n (b O))
  let A : Finset Plane := Finset.univ.image a ∪ Finset.univ.image b
  let L : Finset RationalLine := P.flatten.toFinset ∪ A.image (fun v => ⟨n, normalEval n v⟩)
  have hL (v : Plane) (hv : v ∈ A) : (⟨n, normalEval n v⟩ : RationalLine) ∈ L :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  have haA (O : C) : a O ∈ A :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨O, Finset.mem_univ _, rfl⟩)
  have hbA (O : C) : b O ∈ A :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨O, Finset.mem_univ _, rfl⟩)
  refine ⟨Finset.univ.image e, ?_, ?_, ?_⟩
  · ext r
    constructor
    · rintro ⟨z, hz, rfl⟩
      let O : C := ⟨connectedComponentIn K.openCarrier z, z, hz, rfl⟩
      have hzO : z ∈ (O : Set Plane) := mem_connectedComponentIn hz
      have he : normalEval n z ∈ Set.Ioo (e O).1 (e O).2 := by
        rw [← himage O]
        exact ⟨z, hzO, rfl⟩
      exact Set.mem_iUnion.mpr ⟨e O, Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨O, Finset.mem_univ _, rfl⟩, he⟩⟩
    · intro hr
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hr
      obtain ⟨hpI, hrp⟩ := Set.mem_iUnion.mp hp
      obtain ⟨O, _, rfl⟩ := Finset.mem_image.mp hpI
      rw [← himage O] at hrp
      obtain ⟨z, hz, hzr⟩ := hrp
      exact ⟨z, (Tiling.interiorComponent_basic O.2).2.2 hz, hzr⟩
  · intro p hp
    obtain ⟨O, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hab O, ⟨a O, ha O, rfl⟩, ⟨b O, hb O, rfl⟩⟩
  · obtain ⟨F, ε, hε, harr⟩ := finiteRationalArrangement_transport L A
    refine ⟨F, ε, hε, ?_⟩
    intro φ hφ Kφ hKφ
    obtain ⟨H, hHA, hHL⟩ := harr φ hφ
    have hsupport : H '' K.support = Kφ.support := by
      have hpre : H ⁻¹' Kφ.support = K.support := by
        ext z
        rw [hP.symm, hKφ]
        exact (arrangement_polyhedralSupport_transport P φ H
          (fun l hl => hHL l (Finset.mem_union_left _ (List.mem_toFinset.mpr hl))) z).symm
      rw [← hpre]
      exact Set.image_preimage_eq _ H.surjective
    have hcarrier : H '' K.openCarrier = Kφ.openCarrier := by
      simp only [Tiling.RationalPolygonal.PolygonalRegion.openCarrier, H.image_interior, hsupport]
    have hprojection (O : C) : normalEval n '' (H '' (O : Set Plane)) =
        Set.Ioo (φ (e O).1 : ℝ) (φ (e O).2 : ℝ) := by
      have hconnected := (Tiling.interiorComponent_basic O.2).2.1
      have hconnH := hconnected.image H H.continuous.continuousOn
      have hlower (z : Plane) (hz : z ∈ (O : Set Plane)) :
          (φ (e O).1 : ℝ) < normalEval n (H z) := by
        have hzI : normalEval n z ∈ Set.Ioo (e O).1 (e O).2 := by
          rw [← himage O]; exact ⟨z, hz, rfl⟩
        have hsign := hHL ⟨n, normalEval n (a O)⟩ (hL (a O) (haA O)) z
        have hpos : 0 < (normalEval n (H z) - (φ (e O).1 : ℝ)) := by
          apply (sign_eq_iff_pos hsign).mpr
          exact sub_pos.mpr hzI.1
        exact sub_pos.mp hpos
      have hupper (z : Plane) (hz : z ∈ (O : Set Plane)) :
          normalEval n (H z) < (φ (e O).2 : ℝ) := by
        have hzI : normalEval n z ∈ Set.Ioo (e O).1 (e O).2 := by
          rw [← himage O]; exact ⟨z, hz, rfl⟩
        have hsign := hHL ⟨n, normalEval n (b O)⟩ (hL (b O) (hbA O)) z
        have hneg : (normalEval n (H z) - (φ (e O).2 : ℝ)) < 0 := by
          apply (sign_eq_iff_neg hsign).mpr
          exact sub_neg.mpr hzI.2
        exact sub_neg.mp hneg
      have haHO : H (a O) ∈ closure (H '' (O : Set Plane)) :=
        image_closure_subset_closure_image H.continuous ⟨a O, haO O, rfl⟩
      have hbHO : H (b O) ∈ closure (H '' (O : Set Plane)) :=
        image_closure_subset_closure_image H.continuous ⟨b O, hbO O, rfl⟩
      haveI : NeBot (𝓝[H '' (O : Set Plane)] H (a O)) := mem_closure_iff_nhdsWithin_neBot.mp haHO
      haveI : NeBot (𝓝[H '' (O : Set Plane)] H (b O)) := mem_closure_iff_nhdsWithin_neBot.mp hbHO
      apply Set.Subset.antisymm
      · rintro r ⟨w, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨hlower z hz, hupper z hz⟩
      · have hbetween := hconnH.isPreconnected.intermediate_value_Ioo
          (l₁ := 𝓝[H '' (O : Set Plane)] H (a O))
          (l₂ := 𝓝[H '' (O : Set Plane)] H (b O))
          (inf_le_right : 𝓝[H '' (O : Set Plane)] H (a O) ≤ 𝓟 (H '' (O : Set Plane)))
          (inf_le_right : 𝓝[H '' (O : Set Plane)] H (b O) ≤ 𝓟 (H '' (O : Set Plane)))
          (normalCLM n).continuous.continuousOn
          ((normalCLM n).continuous.tendsto (H (a O)) |>.mono_left nhdsWithin_le_nhds)
          ((normalCLM n).continuous.tendsto (H (b O)) |>.mono_left nhdsWithin_le_nhds)
        simpa only [normalCLM_apply, hHA (a O) (haA O), hHA (b O) (hbA O),
          rationalNormal_commutes] using hbetween
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← hcarrier] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      let O : C := ⟨connectedComponentIn K.openCarrier z, z, hz, rfl⟩
      have hzO : z ∈ (O : Set Plane) := mem_connectedComponentIn hz
      have hrI : normalEval n (H z) ∈ Set.Ioo (φ (e O).1 : ℝ) (φ (e O).2 : ℝ) := by
        rw [← hprojection O]
        exact ⟨H z, ⟨z, hzO, rfl⟩, rfl⟩
      exact Set.mem_iUnion.mpr ⟨e O, Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨O, Finset.mem_univ _, rfl⟩, hrI⟩⟩
    · intro hr
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hr
      obtain ⟨hpI, hrp⟩ := Set.mem_iUnion.mp hp
      obtain ⟨O, _, rfl⟩ := Finset.mem_image.mp hpI
      rw [← hprojection O] at hrp
      obtain ⟨w, ⟨z, hz, rfl⟩, hzr⟩ := hrp
      refine ⟨H z, ?_, hzr⟩
      rw [← hcarrier]
      exact ⟨z, (Tiling.interiorComponent_basic O.2).2.2 hz, rfl⟩

private theorem finite_boundedWords (A : Set ℝ) (hA : A.Finite) (N : ℕ) :
    {G : List ℝ | (∀ r ∈ G, r ∈ A) ∧ G.length ≤ N}.Finite := by
  induction N with
  | zero =>
      apply (Set.finite_singleton ([] : List ℝ)).subset
      intro G hG
      simpa using List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hG.2)
  | succ N ih =>
      apply ((Set.finite_singleton ([] : List ℝ)).union (hA.image2 List.cons ih)).subset
      intro G hG
      cases G with
      | nil => exact Or.inl rfl
      | cons r G =>
          apply Or.inr
          refine ⟨r, hG.1 r (by simp), G, ?_, rfl⟩
          refine ⟨fun q hq => hG.1 q (by simp [hq]), ?_⟩
          simpa using hG.2

private theorem list_length_mul_lower_sum (c : ℝ) (G : List ℝ)
    (hG : ∀ r ∈ G, c ≤ r) : (G.length : ℝ) * c ≤ G.sum := by
  induction G with
  | nil => simp
  | cons r G ih =>
      have hr := hG r (by simp)
      have ht := ih (fun q hq => hG q (by simp [hq]))
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.sum_cons]
      nlinarith

private theorem properLink_sourceNormalLevels_finite (K : PolygonalRegion)
    (T : Set Plane) (n : RationalNormal) (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a : Plane) (ha : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a)
    (R : ℝ) :
    {x | x ∈ normalEval n '' Tiling.RationalSlopes.translatedVertices K T ∧
      |x - normalEval n a| ≤ R}.Finite := by
  classical
  let ℓ := normalCLM n
  have hℓ : ℓ ≠ 0 := normalCLM_ne_zero n
  obtain ⟨hA, _, c, hc, hmin⟩ := Tiling.RationalSlopes.positiveVertexGaps_finitePositive K ℓ hℓ
  obtain ⟨N, hN⟩ := exists_nat_gt (R / c)
  let W : Set (List ℝ) := {G | (∀ r ∈ G, r ∈ Tiling.RationalSlopes.positiveVertexGaps K ℓ) ∧
    G.length ≤ N}
  have hW : W.Finite := finite_boundedWords _ hA N
  let sums : Set ℝ := List.sum '' W
  have hsums : sums.Finite := hW.image _
  have hfinite : ({normalEval n a} ∪
      ((fun r => normalEval n a + r) '' sums) ∪
      ((fun r => normalEval n a - r) '' sums)).Finite :=
    ((Set.finite_singleton _).union (hsums.image _)).union (hsums.image _)
  apply hfinite.subset
  rintro x ⟨⟨v, hv, rfl⟩, hvR⟩
  by_cases heq : normalEval n v = normalEval n a
  · exact Or.inl (Or.inl heq)
  · have hdim := (normalDirection_rational n).1
    obtain ⟨G, hGne, hG, hsum⟩ := Tiling.RationalSlopes.link_distance_isPositiveWord K
      (normalDirection n) T ℓ hdim hℓ (by rfl) htile a ha v hv
      (by simpa only [ℓ, normalCLM_apply] using heq)
    have hsum' : |normalEval n v - normalEval n a| = G.sum := by
      simpa only [ℓ, normalCLM_apply] using hsum
    have hlength := list_length_mul_lower_sum c G (fun r hr => hmin r (hG r hr))
    have hlenR : (G.length : ℝ) ≤ R / c := by
      apply (le_div_iff₀ hc).mpr
      rw [← hsum'] at hlength
      linarith
    have hlenN : G.length ≤ N := le_of_lt (by exact_mod_cast hlenR.trans_lt hN)
    have hGs : G.sum ∈ sums := Set.mem_image_of_mem _ (show G ∈ W from ⟨hG, hlenN⟩)
    rcases lt_or_gt_of_ne heq with hlt | hgt
    · apply Or.inr
      refine ⟨G.sum, hGs, ?_⟩
      rw [abs_of_neg (sub_neg.mpr hlt)] at hsum'
      linarith
    · apply Or.inl ∘ Or.inr
      refine ⟨G.sum, hGs, ?_⟩
      rw [abs_of_pos (sub_pos.mpr hgt)] at hsum'
      linarith

theorem properLink_normalOrderControl :
  ∀ (K : PolygonalRegion) (T : Set Plane) (n : RationalNormal),
    Tiling.RationalSlopes.HasRationalSlopes K → Tiling.Polygonal.TilesOn K T Set.univ →
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ a : Plane, Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a →
            ∀ v ∈ Tiling.RationalSlopes.translatedVertices K T,
              Real.sign (normalEval n (deformPoint φ (v - a))) =
                Real.sign (normalEval n (v - a)) ∧
              |normalEval n (v - a)| / 2 ≤
                |normalEval n (deformPoint φ (v - a))| ∧
              |normalEval n (deformPoint φ (v - a))| ≤ 2 * |normalEval n (v - a)| := by
  intro K T n _ htile
  classical
  let ℓ := normalCLM n
  obtain ⟨hfinite, _, c, hc, hclower⟩ :=
    Tiling.RationalSlopes.positiveVertexGaps_finitePositive K ℓ (normalCLM_ne_zero n)
  refine ⟨hfinite.toFinset, c / 2, by positivity, ?_⟩
  intro φ hφ a hlink v hv
  rw [rationalNormal_commutes]
  apply signed_deformation_bounds
  by_cases hzero : normalEval n (v - a) = 0
  · simp [hzero]
  · have hnormal : ℓ v - ℓ a = normalEval n (v - a) := by
      rw [normalEval_sub]
      simp [ℓ, normalCLM_apply]
    have hneq : ℓ v ≠ ℓ a := by intro h; apply hzero; rw [← hnormal, h, sub_self]
    obtain ⟨G, _, hG, hsum⟩ := Tiling.RationalSlopes.link_distance_isPositiveWord
      K (normalDirection n) T ℓ (normalDirection_rational n).1 (normalCLM_ne_zero n)
      rfl htile a hlink v hv hneq
    rw [hnormal] at hsum
    rw [hsum]
    apply list_sum_deformation_bounds
    intro r hr
    have hrgap := hG r hr
    have hcr := hclower r hrgap
    have happ := hφ.2 r (hfinite.mem_toFinset.mpr hrgap)
    have herr := abs_lt.mp happ
    constructor <;> linarith

private theorem properLink_vertexNormalGap (K : PolygonalRegion)
    (T : Set Plane) (n : RationalNormal) (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ g : ℝ, 0 < g ∧ ∀ a : Plane,
      Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a →
        ∀ v ∈ Tiling.RationalSlopes.translatedVertices K T,
          normalEval n v ≠ normalEval n a → g ≤ |normalEval n (v - a)| := by
  let ℓ := normalCLM n
  obtain ⟨_, _, c, hc, hmin⟩ :=
    Tiling.RationalSlopes.positiveVertexGaps_finitePositive K ℓ (normalCLM_ne_zero n)
  refine ⟨c, hc, ?_⟩
  intro a ha v hv hneq
  obtain ⟨G, hGne, hG, hsum⟩ := Tiling.RationalSlopes.link_distance_isPositiveWord
    K (normalDirection n) T ℓ (normalDirection_rational n).1 (normalCLM_ne_zero n)
    rfl htile a ha v hv (by simpa only [ℓ, normalCLM_apply] using hneq)
  have hsum' : |normalEval n (v - a)| = G.sum := by
    simpa only [ℓ, normalCLM_apply, normalEval_sub] using hsum
  have hlength := list_length_mul_lower_sum c G (fun r hr => hmin r (hG r hr))
  have hlen : (1 : ℝ) ≤ G.length := by
    exact_mod_cast (List.length_pos_iff.mpr hGne)
  rw [hsum']
  nlinarith

/-- The selected normal direction has a uniform vertex-free gap next to every
    old full link. This says nothing about the number of tangential image labels. -/
private theorem properLink_imageVertexNormalGap (K : PolygonalRegion)
    (T : Set Plane) (n : RationalNormal)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ F : Finset ℝ, ∃ ε g : ℝ, 0 < ε ∧ 0 < g ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ a : Plane, Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a →
          ∀ v ∈ Tiling.RationalSlopes.translatedVertices K T,
            normalEval n (deformPoint φ v) = normalEval n (deformPoint φ a) ∨
              g ≤ |normalEval n (deformPoint φ v) - normalEval n (deformPoint φ a)| := by
  obtain ⟨F, ε, hε, hcontrol⟩ := properLink_normalOrderControl K T n hrat htile
  obtain ⟨g, hg, hgap⟩ := properLink_vertexNormalGap K T n htile
  refine ⟨F, ε, g / 2, hε, by positivity, ?_⟩
  intro φ hφ a ha v hv
  by_cases heq : normalEval n v = normalEval n a
  · left
    simp only [rationalNormal_commutes, heq]
  · right
    have hb := (hcontrol φ hφ a ha v hv).2.1
    have hd := hgap a ha v hv heq
    have htarget : normalEval n (deformPoint φ (v - a)) =
        normalEval n (deformPoint φ v) - normalEval n (deformPoint φ a) := by
      simp only [rationalNormal_commutes, normalEval_sub, map_sub, Rat.cast_sub]
    rw [htarget] at hb
    linarith

private theorem properLink_imageNormalLevels_locallyFinite (K : PolygonalRegion)
    (T : Set Plane) (n : RationalNormal) (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a : Plane) (ha : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Q : Set ℝ, Bornology.IsBounded Q →
        ((normalEval n '' (deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T)) ∩ Q).Finite := by
  obtain ⟨F, ε, hε, hcontrol⟩ :=
    properLink_normalOrderControl K T n hrat htile
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Q hQ
  obtain ⟨R, hR, hRbound⟩ := hQ.exists_pos_norm_le
  have hsource := properLink_sourceNormalLevels_finite K T n htile a ha
    (2 * (R + |normalEval n (deformPoint φ a)|))
  have hfinite := hsource.image (fun r => (φ r : ℝ))
  apply hfinite.subset
  rintro _ ⟨⟨_, ⟨v, hv, rfl⟩, rfl⟩, hvQ⟩
  have hb := ((hcontrol φ hφ a ha v hv).2).1
  simp only [rationalNormal_commutes, normalEval_sub, map_sub, Rat.cast_sub] at hb
  have htarget : |(φ (normalEval n v) : ℝ) - (φ (normalEval n a) : ℝ)| ≤
      R + |normalEval n (deformPoint φ a)| := by
    have hr : |normalEval n (deformPoint φ v)| ≤ R := by
      simpa only [Real.norm_eq_abs] using hRbound _ hvQ
    have h : |normalEval n (deformPoint φ v) - normalEval n (deformPoint φ a)| ≤
        R + |normalEval n (deformPoint φ a)| := by
      linarith [abs_sub (normalEval n (deformPoint φ v)) (normalEval n (deformPoint φ a))]
    simpa only [rationalNormal_commutes] using h
  refine ⟨normalEval n v, ⟨Set.mem_image_of_mem _ hv, ?_⟩,
    (rationalNormal_commutes φ n v).symm⟩
  linarith

theorem directionalOverlap_iff_openNormalProjections :
  ∀ (K : PolygonalRegion) (n : RationalNormal) (s t : Plane),
    Tiling.RationalSlopes.DirectionalOverlap K (normalDirection n) s t ↔
      ((normalEval n '' (s +ᵥ K.openCarrier)) ∩
        (normalEval n '' (t +ᵥ K.openCarrier))).Nonempty := by
  intro K n s t
  constructor
  · rintro ⟨x, ⟨hx₁, hx₂⟩⟩
    rcases hx₂ with ⟨y, hy, hxy⟩
    refine ⟨normalEval n x, ⟨x, hx₁, rfl⟩, ⟨y, hy, ?_⟩⟩
    have hzero : normalEval n (x - y) = 0 :=
      (normalDirection_mem_iff n (x - y)).mp hxy
    rw [normalEval_sub] at hzero
    linarith
  · rintro ⟨r, ⟨x, hx, hxr⟩, ⟨y, hy, hyr⟩⟩
    have hxy : normalEval n x = normalEval n y := hxr.trans hyr.symm
    have hker : x - y ∈ normalDirection n :=
      (normalDirection_mem_iff n (x - y)).mpr (by rw [normalEval_sub, hxy]; ring)
    refine ⟨x, ⟨hx, ?_⟩⟩
    exact ⟨y, hy, hker⟩

private theorem exists_positiveGapWord
    (S : Set ℝ) (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hdense : ∀ x : ℝ, ∃ s ∈ S, dist x s < ρ) :
    ∀ a ∈ S, ∀ b ∈ S, a < b →
      ∃ G : List ℝ, G ≠ [] ∧
        (∀ r ∈ G, 0 < r ∧ r ∈ (S - S) ∩ Metric.closedBall 0 (2 * ρ)) ∧
          b - a = G.sum := by
  classical
  have recurse : ∀ n a b, (S ∩ Set.Ioo a b).ncard = n → a ∈ S → b ∈ S → a < b →
      ∃ G : List ℝ, G ≠ [] ∧
        (∀ r ∈ G, 0 < r ∧ r ∈ (S - S) ∩ Metric.closedBall 0 (2 * ρ)) ∧
          b - a = G.sum := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a b hcount ha hb hab
        let F : Set ℝ := S ∩ Set.Ioo a b
        have hF : F.Finite := (hlocal (Set.Icc a b) (Metric.isBounded_Icc a b)).subset
          (by
            intro x hx
            exact ⟨hx.1, ⟨le_of_lt hx.2.1, le_of_lt hx.2.2⟩⟩)
        by_cases hsmall : b - a ≤ 2 * ρ
        · refine ⟨[b - a], by simp, ?_, by simp⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst r
          refine ⟨by linarith, ?_⟩
          refine ⟨?_, ?_⟩
          · change b - a ∈ Set.image2 (fun x y : ℝ => x - y) S S
            exact Set.mem_image2_of_mem hb ha
          · change dist (b - a) 0 ≤ 2 * ρ
            simpa [Real.dist_eq, abs_of_pos (sub_pos.mpr hab)] using hsmall
        · have hlarge : 2 * ρ < b - a := lt_of_not_ge hsmall
          let m : ℝ := (a + b) / 2
          have ham : a < m := by dsimp [m]; linarith
          have hmb : m < b := by dsimp [m]; linarith
          obtain ⟨c, hcS, hdist⟩ := hdense m
          have hdist' : |m - c| < ρ := by simpa [Real.dist_eq, abs_sub_comm] using hdist
          rcases abs_lt.mp hdist' with ⟨hdistLo, hdistHi⟩
          have hac : a < c := by dsimp [m] at ham hmb hlarge hdistLo hdistHi ⊢; linarith
          have hcb : c < b := by dsimp [m] at ham hmb hlarge hdistLo hdistHi ⊢; linarith
          let L : Set ℝ := S ∩ Set.Ioo a c
          let R : Set ℝ := S ∩ Set.Ioo c b
          have hLfinite : L.Finite := (hlocal (Set.Icc a c) (Metric.isBounded_Icc a c)).subset
            (by
              intro x hx
              exact ⟨hx.1, ⟨le_of_lt hx.2.1, le_of_lt hx.2.2⟩⟩)
          have hRfinite : R.Finite := (hlocal (Set.Icc c b) (Metric.isBounded_Icc c b)).subset
            (by
              intro x hx
              exact ⟨hx.1, ⟨le_of_lt hx.2.1, le_of_lt hx.2.2⟩⟩)
          have hLsub : L ⊂ F := by
            apply Set.ssubset_iff_subset_ne.mpr
            constructor
            · intro x hx
              exact ⟨hx.1, ⟨hx.2.1, lt_trans hx.2.2 hcb⟩⟩
            · intro heq
              have hcF : c ∈ F := ⟨hcS, ⟨hac, hcb⟩⟩
              have hcL : c ∈ L := heq.symm ▸ hcF
              exact (lt_irrefl c) hcL.2.2
          have hRsub : R ⊂ F := by
            apply Set.ssubset_iff_subset_ne.mpr
            constructor
            · intro x hx
              exact ⟨hx.1, ⟨lt_trans hac hx.2.1, hx.2.2⟩⟩
            · intro heq
              have hcF : c ∈ F := ⟨hcS, ⟨hac, hcb⟩⟩
              have hcR : c ∈ R := heq.symm ▸ hcF
              exact (lt_irrefl c) hcR.2.1
          have hLcard : L.ncard < n := by
            rw [← hcount]
            exact Set.ncard_lt_ncard hLsub hF
          have hRcard : R.ncard < n := by
            rw [← hcount]
            exact Set.ncard_lt_ncard hRsub hF
          obtain ⟨G₁, hG₁ne, hG₁, hsum₁⟩ :=
            ih L.ncard hLcard a c (by rfl) ha hcS hac
          obtain ⟨G₂, hG₂ne, hG₂, hsum₂⟩ :=
            ih R.ncard hRcard c b (by rfl) hcS hb hcb
          refine ⟨G₁ ++ G₂, ?_, ?_, ?_⟩
          · intro hnil
            simp only [List.append_eq_nil_iff] at hnil
            exact hG₁ne hnil.1
          · intro r hr
            rcases List.mem_append.mp hr with hr | hr
            · exact hG₁ r hr
            · exact hG₂ r hr
          · rw [List.sum_append]
            calc
              b - a = (c - a) + (b - c) := by ring
              _ = G₁.sum + G₂.sum := by rw [hsum₁, hsum₂]
  intro a ha b hb hab
  exact recurse (S ∩ Set.Ioo a b).ncard a b rfl ha hb hab

private theorem finite_positive_deformation_bounds (D : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation D ε φ →
      ∀ r ∈ D, 0 < r → r / 2 ≤ (φ r : ℝ) ∧ (φ r : ℝ) ≤ 2 * r := by
  classical
  induction D using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert r D hr ih =>
      obtain ⟨ε, hε, hcontrol⟩ := ih
      by_cases hrpos : 0 < r
      · refine ⟨min ε (r / 2), lt_min hε (by positivity), ?_⟩
        intro φ hφ q hq hqpos
        have hφD : IsFiniteApproximation D ε φ := by
          refine ⟨hφ.1, ?_⟩
          intro x hx
          exact (hφ.2 x (Finset.mem_insert_of_mem hx)).trans_le (min_le_left _ _)
        rcases Finset.mem_insert.mp hq with rfl | hqD
        · have hb := abs_lt.mp ((hφ.2 q (Finset.mem_insert_self _ _)).trans_le (min_le_right _ _))
          constructor <;> linarith [hb.1, hb.2]
        · exact hcontrol φ hφD q hqD hqpos
      · refine ⟨ε, hε, ?_⟩
        intro φ hφ q hq hqpos
        have hφD : IsFiniteApproximation D ε φ :=
          ⟨hφ.1, fun x hx => hφ.2 x (Finset.mem_insert_of_mem hx)⟩
        rcases Finset.mem_insert.mp hq with rfl | hqD
        · exact (hrpos hqpos).elim
        · exact hcontrol φ hφD q hqD hqpos

private theorem hasFLC_scalarImage (S : Set ℝ) (hS : Tiling.Polygonal.HasFLC S)
    (c : ℝ) (hc : c ≠ 0) : Tiling.Polygonal.HasFLC ((fun r => c * r) '' S) := by
  have hcpos : 0 < |c| := abs_pos.mpr hc
  constructor
  · intro Q hQ
    obtain ⟨R, hR, hbound⟩ := hQ.exists_pos_norm_le
    have hfinite := (hS.1 (Metric.closedBall 0 (R / |c|)) Metric.isBounded_closedBall).image
      (fun r => c * r)
    apply hfinite.subset
    rintro _ ⟨⟨r, hr, rfl⟩, hq⟩
    refine ⟨r, ⟨hr, ?_⟩, rfl⟩
    have hb : |c| * |r| ≤ R := by simpa [Real.norm_eq_abs, abs_mul] using hbound _ hq
    simpa [Real.dist_eq, abs_sub_comm] using (le_div_iff₀ hcpos).mpr (by nlinarith [hb])
  · intro R hR
    have hfinite := (hS.2 (R / |c|) (div_pos hR hcpos)).image (fun r => c * r)
    apply hfinite.subset
    rintro x ⟨hx, hxR⟩
    obtain ⟨a, ⟨s, hs, rfl⟩, b, ⟨t, ht, rfl⟩, rfl⟩ := hx
    refine ⟨s - t, ⟨⟨s, hs, t, ht, rfl⟩, ?_⟩, by ring⟩
    have hb : |c| * |s - t| ≤ R := by
      have : |c * s - c * t| ≤ R := by simpa [Real.dist_eq] using hxR
      simpa only [← mul_sub, abs_mul] using this
    simpa [Real.dist_eq] using (le_div_iff₀ hcpos).mpr (by nlinarith [hb])

private theorem transverseFLC_normalImage (K : PolygonalRegion) (T : Set Plane)
    (n : RationalNormal)
    (hflc : Tiling.RationalSlopes.HasTransverseFLC K (normalDirection n) T) :
    Tiling.Polygonal.HasFLC (normalEval n '' Tiling.RationalSlopes.translatedVertices K T) := by
  obtain ⟨ℓ, hℓ, hker, hS⟩ := hflc
  obtain ⟨q, hq⟩ : ∃ q : Plane, normalEval n q ≠ 0 := by
    rcases n.nonzero with hx | hy
    · refine ⟨1, ?_⟩
      simpa [normalEval] using (show (n.x : ℝ) ≠ 0 by exact_mod_cast hx)
    · refine ⟨Complex.I, ?_⟩
      simpa [normalEval] using (show (n.y : ℝ) ≠ 0 by exact_mod_cast hy)
  have hqℓ : ℓ q ≠ 0 := by
    intro hzero
    have hmem : q ∈ LinearMap.ker ℓ.toLinearMap := hzero
    rw [hker] at hmem
    exact hq ((normalDirection_mem_iff n q).mp hmem)
  let c : ℝ := normalEval n q / ℓ q
  have hc : c ≠ 0 := div_ne_zero hq hqℓ
  have hprop (z : Plane) : normalEval n z = c * ℓ z := by
    have hmem : z - (ℓ z / ℓ q) • q ∈ LinearMap.ker ℓ.toLinearMap := by
      change ℓ (z - (ℓ z / ℓ q) • q) = 0
      rw [map_sub, map_smul]
      simp only [smul_eq_mul]
      field_simp [hqℓ]
      ring
    rw [hker] at hmem
    have hz := (normalDirection_mem_iff n _).mp hmem
    change normalCLM n (z - (ℓ z / ℓ q) • q) = 0 at hz
    simp only [map_sub, map_smul, smul_eq_mul, normalCLM_apply] at hz
    dsimp [c]
    rw [div_mul_eq_mul_div]
    rw [show ℓ z / ℓ q * normalEval n q = normalEval n q * ℓ z / ℓ q by ring] at hz
    linarith
  have himage : normalEval n '' Tiling.RationalSlopes.translatedVertices K T =
      (fun r => c * r) '' (ℓ '' Tiling.RationalSlopes.translatedVertices K T) := by
    rw [Set.image_image]
    congr 1
    funext z
    exact hprop z
  rw [himage]
  exact hasFLC_scalarImage _ hS c hc

private theorem translatedNormalLevels_dense (K : PolygonalRegion) (T : Set Plane)
    (n : RationalNormal) (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ,
      ∃ s ∈ normalEval n '' Tiling.RationalSlopes.translatedVertices K T, dist r s < ρ := by
  obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
  let O : Set Plane := connectedComponentIn K.openCarrier z
  have hO : O ∈ Tiling.interiorComponents K.support := ⟨z, hz, rfl⟩
  obtain ⟨u, _, hu, _, _, _, _, _⟩ := component_normalProjection K n O hO
  obtain ⟨R, hR, hbound⟩ := K.isPolygonal.isBounded.exists_pos_norm_le
  let ρ : ℝ := ‖normalCLM n‖ * (‖u‖ + R) + 1
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  refine ⟨ρ, hρ, ?_⟩
  intro r
  obtain ⟨q, hq⟩ : ∃ q : Plane, normalEval n q = r := by
    rcases n.nonzero with hx | hy
    · refine ⟨Complex.mk (r / (n.x : ℝ)) 0, ?_⟩
      have hx' : (n.x : ℝ) ≠ 0 := by exact_mod_cast hx
      change (n.x : ℝ) * (r / (n.x : ℝ)) + (n.y : ℝ) * 0 = r
      field_simp [hx']
      ring
    · refine ⟨Complex.mk 0 (r / (n.y : ℝ)), ?_⟩
      have hy' : (n.y : ℝ) ≠ 0 := by exact_mod_cast hy
      change (n.x : ℝ) * 0 + (n.y : ℝ) * (r / (n.y : ℝ)) = r
      field_simp [hy']
      ring
  have hcover : (⋃ t : T, (t : Plane) +ᵥ K.support) = Set.univ := by
    rw [← Tiling.Polygonal.closure_openUnion_eq_iUnion_support htile.2.1]
    have hfull := Tiling.Polygonal.regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
    have hsubset : Set.univ ⊆ closure (Tiling.Polygonal.openUnion K T) := by
      rw [← hfull]
      exact interior_subset
    exact Set.eq_univ_of_univ_subset hsubset
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hcover ▸ (Set.mem_univ q))
  have hw : (-t.1 +ᵥ q) ∈ K.support := Set.mem_vadd_set_iff_neg_vadd_mem.mp ht
  refine ⟨normalEval n (u + t.1), Set.mem_image_of_mem _ (Set.add_mem_add hu t.2), ?_⟩
  have hnorm : ‖q - (u + t.1)‖ ≤ R + ‖u‖ := by
    have heq : q - (u + t.1) = (-t.1 +ᵥ q) - u := by change q - (u + t.1) = -t.1 + q - u; abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith [hbound _ hw])
  have hb : ‖normalCLM n (q - (u + t.1))‖ ≤ ‖normalCLM n‖ * (R + ‖u‖) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  rw [map_sub, normalCLM_apply, normalCLM_apply, hq] at hb
  rw [Real.norm_eq_abs] at hb
  rw [dist_eq_norm]
  dsimp [ρ]
  nlinarith

theorem transverseFLC_globalOrderAndBoundedGapReflection :
  ∀ (K : PolygonalRegion) (T : Set Plane) (n : RationalNormal),
    Tiling.RationalSlopes.HasRationalSlopes K → Tiling.Polygonal.TilesOn K T Set.univ →
    Tiling.RationalSlopes.HasTransverseFLC K (normalDirection n) T →
      ∀ M : ℝ, 0 < M → ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          (∀ v ∈ Tiling.RationalSlopes.translatedVertices K T,
            ∀ w ∈ Tiling.RationalSlopes.translatedVertices K T,
              normalEval n v < normalEval n w ↔
                normalEval n (deformPoint φ v) < normalEval n (deformPoint φ w)) ∧
          (∀ a ∈ Tiling.RationalSlopes.translatedVertices K T,
            ∀ b ∈ Tiling.RationalSlopes.translatedVertices K T,
            ∀ c ∈ Tiling.RationalSlopes.translatedVertices K T,
            ∀ d ∈ Tiling.RationalSlopes.translatedVertices K T,
              |normalEval n (deformPoint φ (a - b))| < M / 2 →
              |normalEval n (deformPoint φ (c - d))| < M / 2 →
                (normalEval n (deformPoint φ (a - b)) =
                  normalEval n (deformPoint φ (c - d)) ↔
                    normalEval n (a - b) = normalEval n (c - d))) := by
  intro K T n hrat htile hflc M hM
  classical
  let S : Set ℝ := normalEval n '' Tiling.RationalSlopes.translatedVertices K T
  have hS : Tiling.Polygonal.HasFLC S := transverseFLC_normalImage K T n hflc
  obtain ⟨ρ, hρ, hdense⟩ := translatedNormalLevels_dense K T n htile
  have hD₀ : ((S - S) ∩ Metric.closedBall 0 (2 * ρ)).Finite :=
    hS.2 (2 * ρ) (by positivity)
  let D₀ : Finset ℝ := hD₀.toFinset
  obtain ⟨ε₀, hε₀, hpositive⟩ := finite_positive_deformation_bounds D₀
  have hD₁ : ((S - S) ∩ Metric.closedBall 0 M).Finite := hS.2 M hM
  let D₁ : Finset ℝ := hD₁.toFinset
  obtain ⟨F₁, ε₁, hε₁, hequality⟩ := finiteApproximation_signAndEquality D₁
  refine ⟨D₀ ∪ F₁, min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro φ hφ
  have hφ₀ := finiteApproximation_strengthen D₀ (D₀ ∪ F₁) ε₀ (min ε₀ ε₁) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφ₁ := finiteApproximation_strengthen F₁ (D₀ ∪ F₁) ε₁ (min ε₀ ε₁) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  have hscalar (x : ℝ) (hx : x ∈ S) (y : ℝ) (hy : y ∈ S) :
      Real.sign (φ (x - y) : ℝ) = Real.sign (x - y) ∧
        |x - y| / 2 ≤ |(φ (x - y) : ℝ)| ∧ |(φ (x - y) : ℝ)| ≤ 2 * |x - y| := by
    by_cases hxy : x = y
    · subst y
      simp
    obtain ⟨G, hGne, hG, hsum⟩ : ∃ G : List ℝ, G ≠ [] ∧
        (∀ r ∈ G, 0 < r ∧ r ∈ (S - S) ∩ Metric.closedBall 0 (2 * ρ)) ∧
          |x - y| = G.sum := by
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · obtain ⟨G, hGne, hG, hsum⟩ := exists_positiveGapWord S hS.1 ρ hρ hdense x hx y hy hlt
        refine ⟨G, hGne, hG, ?_⟩
        rw [abs_of_neg (sub_neg.mpr hlt)]
        linarith
      · obtain ⟨G, hGne, hG, hsum⟩ := exists_positiveGapWord S hS.1 ρ hρ hdense y hy x hx hgt
        exact ⟨G, hGne, hG, by simpa [abs_of_pos (sub_pos.mpr hgt)] using hsum⟩
    have hb := list_sum_deformation_bounds φ G (fun r hr =>
      hpositive φ hφ₀ r (hD₀.mem_toFinset.mpr (hG r hr).2) (hG r hr).1)
    rw [← hsum] at hb
    exact signed_deformation_bounds φ (x - y) hb
  constructor
  · intro v hv w hw
    have hs := (hscalar (normalEval n v) (Set.mem_image_of_mem _ hv)
      (normalEval n w) (Set.mem_image_of_mem _ hw)).1
    rw [rationalNormal_commutes, rationalNormal_commutes]
    have hneg := sign_eq_iff_neg hs
    simpa only [map_sub, Rat.cast_sub, sub_neg] using hneg.symm
  · intro a ha b hb c hc d hd hab hcd
    have habounds := (hscalar (normalEval n a) (Set.mem_image_of_mem _ ha)
      (normalEval n b) (Set.mem_image_of_mem _ hb)).2.1
    have hcdbounds := (hscalar (normalEval n c) (Set.mem_image_of_mem _ hc)
      (normalEval n d) (Set.mem_image_of_mem _ hd)).2.1
    rw [rationalNormal_commutes, normalEval_sub] at hab hcd
    have habsource : |normalEval n a - normalEval n b| < M := by linarith
    have hcdsource : |normalEval n c - normalEval n d| < M := by linarith
    have habD : normalEval n (a - b) ∈ D₁ := by
      apply hD₁.mem_toFinset.mpr
      rw [normalEval_sub]
      refine ⟨Set.mem_image2_of_mem (Set.mem_image_of_mem _ ha) (Set.mem_image_of_mem _ hb), ?_⟩
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using habsource.le
    have hcdD : normalEval n (c - d) ∈ D₁ := by
      apply hD₁.mem_toFinset.mpr
      rw [normalEval_sub]
      refine ⟨Set.mem_image2_of_mem (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd), ?_⟩
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hcdsource.le
    rw [rationalNormal_commutes, rationalNormal_commutes]
    exact_mod_cast (hequality φ hφ₁).2 _ habD _ hcdD

private theorem normalEval_add (n : RationalNormal) (x y : Plane) :
    normalEval n (x + y) = normalEval n x + normalEval n y := by
  simp [normalEval, Complex.add_re, Complex.add_im]
  ring

private theorem exists_positiveMinAbs (F : Finset ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ F, x ≠ 0 → δ ≤ |x| := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a F hnot ih =>
      obtain ⟨δ, hδ, hbound⟩ := ih
      by_cases ha : a = 0
      · refine ⟨δ, hδ, ?_⟩
        intro x hx hx0
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact (hx0 ha).elim
        · exact hbound x hx hx0
      · refine ⟨min δ |a|, lt_min hδ (abs_pos.mpr ha), ?_⟩
        intro x hx hx0
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hbound x hx hx0)

private theorem nonpos_iff_after_close_translation
    {a b u δ : ℝ} (hδ : 0 < δ) (hmargin : δ ≤ |a|)
    (hclose : |b - a| < δ / 4) (hu : |u| < δ / 4) :
    (a + u ≤ 0 ↔ b + u ≤ 0) := by
  have hane : a ≠ 0 := by
    intro hz
    have : δ ≤ 0 := by simpa [hz] using hmargin
    linarith
  rcases lt_or_gt_of_ne hane with haneg | hapoz
  · have ha : a ≤ -δ := by
      rw [abs_of_neg haneg] at hmargin
      linarith
    have hclose' := abs_lt.mp hclose
    have hu' := abs_lt.mp hu
    have hb : b < 0 := by linarith
    have hau : a + u < 0 := by linarith [ha, hu'.2]
    have hbu : b + u < 0 := by linarith [hclose'.2, hu'.2, ha]
    simp [le_of_lt hau, le_of_lt hbu]
  · have ha : δ ≤ a := by
      rw [abs_of_pos hapoz] at hmargin
      exact hmargin
    have hclose' := abs_lt.mp hclose
    have hu' := abs_lt.mp hu
    have hb : 0 < b := by linarith
    have hau : 0 < a + u := by linarith [ha, hu'.1]
    have hbu : 0 < b + u := by linarith [hclose'.1, hu'.1, ha]
    simp [not_le_of_gt hau, not_le_of_gt hbu]

private theorem normalEval_norm_bound (n : RationalNormal) (z : Plane) :
  |normalEval n z| ≤ ‖normalCLM n‖ * ‖z‖ := by
  simpa [normalCLM_apply, Real.norm_eq_abs] using
    (normalCLM n).le_opNorm z

private theorem normalEval_deformPoint_commutes_local :
    ∀ (φ : ℝ →ₗ[ℚ] ℚ) (n : RationalNormal) (z : Plane),
      normalEval n (deformPoint φ z) = (φ (normalEval n z) : ℝ) := by
  intro φ n z
  simp only [normalEval, deformPoint]
  have hx := map_smul φ n.x z.re
  have hy := map_smul φ n.y z.im
  simp only [Rat.smul_def] at hx hy
  calc
    (n.x : ℝ) * φ z.re + (n.y : ℝ) * φ z.im =
        (φ ((n.x : ℝ) * z.re + (n.y : ℝ) * z.im) : ℝ) := by
          rw [map_add, hx, hy]
          push_cast
          ring
    _ = (φ (normalEval n z) : ℝ) := rfl

private theorem finiteNormalEval_norm_bound (L : Finset RationalLine)
    (l : RationalLine) (hl : l ∈ L) :
    ‖normalCLM l.normal‖ ≤
      1 + ∑ k ∈ L, ‖normalCLM k.normal‖ := by
  classical
  induction L using Finset.induction_on generalizing l with
  | empty => simp at hl
  | @insert a L hnot ih =>
      simp only [Finset.sum_insert hnot]
      by_cases hla : l = a
      · subst l
        have hnonneg := norm_nonneg (normalCLM a.normal)
        have htail : 0 ≤ ∑ k ∈ L, ‖normalCLM k.normal‖ :=
          Finset.sum_nonneg fun k hk => norm_nonneg _
        linarith
      · have hlL : l ∈ L := (Finset.mem_insert.mp hl).resolve_left hla
        have hrec := ih l hlL
        have hnonneg := norm_nonneg (normalCLM a.normal)
        linarith

private theorem polyhedralSupport_uniformAlignedSupport :
    ∀ (P : PolyhedralCode) (W : Finset Plane),
      ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ v ∈ W, ∀ z : Plane, dist z 0 < r →
            (v + z ∈ polyhedralSupport P ↔
              deformPoint φ v + z ∈ deformedPolyhedralSupport P φ) := by
  classical
  intro P W
  let L : Finset RationalLine := P.flatten.toFinset
  let F : Finset ℝ := L.biUnion fun l => W.image (fun v => l.eval v)
  obtain ⟨δ, hδ, hδF⟩ := exists_positiveMinAbs F
  let B : ℝ := 1 + ∑ l ∈ L, ‖normalCLM l.normal‖
  have hB : 0 < B := by
    dsimp [B]
    have hsum : 0 ≤ ∑ l ∈ L, ‖normalCLM l.normal‖ :=
      Finset.sum_nonneg fun l hl => norm_nonneg _
    linarith
  let ε : ℝ := δ / 4
  let r : ℝ := δ / (4 * B)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨F, ε, r, hε, hr, ?_⟩
  intro φ hφ v hv z hz
  have hzNorm : ‖z‖ < r := by simpa [dist_eq_norm] using hz
  have lineControl : ∀ l ∈ P.flatten,
      l.eval (v + z) ≤ 0 ↔
        (deformLine φ l).eval (deformPoint φ v + z) ≤ 0 := by
    intro l hl
    have hlL : l ∈ L := by
      exact List.mem_toFinset.mpr hl
    have hvF : l.eval v ∈ F := by
      apply Finset.mem_biUnion.mpr
      refine ⟨l, hlL, ?_⟩
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    let α := l.eval v
    let u := normalEval l.normal z
    have hαF : α ∈ F := by simpa [α] using hvF
    have hsEval : l.eval (v + z) = α + u := by
      simp [α, u, RationalLine.eval, normalEval_add]
      ring
    have htEval : (deformLine φ l).eval (deformPoint φ v + z) =
        (φ α : ℝ) + u := by
      simp [α, u, RationalLine.eval, deformLine, normalEval_add,
        normalEval_deformPoint_commutes_local, map_sub]
      ring
    have hu : |u| < δ / 4 := by
      have huNorm : |normalEval l.normal z| ≤
          ‖normalCLM l.normal‖ * ‖z‖ := normalEval_norm_bound _ _
      have hcoef : ‖normalCLM l.normal‖ ≤ B := by
        exact (finiteNormalEval_norm_bound L l hlL).trans_eq (by rfl)
      have hmul : ‖normalCLM l.normal‖ * ‖z‖ < B * r := by
        calc
          ‖normalCLM l.normal‖ * ‖z‖ ≤ B * ‖z‖ := by gcongr
          _ < B * r := by exact (mul_lt_mul_of_pos_left hzNorm hB)
      have hBr : B * r = δ / 4 := by
        dsimp [r]
        field_simp
      simpa [u, hBr] using lt_of_le_of_lt huNorm hmul
    by_cases hα : α = 0
    · have hφα : (φ α : ℝ) = 0 := by simp [hα]
      rw [hsEval, htEval, hφα, hα]
    · have hmargin : δ ≤ |α| := hδF α hαF hα
      have hclose : |(φ α : ℝ) - α| < δ / 4 := by
        simpa [ε] using hφ.2 α hαF
      rw [hsEval, htEval]
      exact nonpos_iff_after_close_translation hδ hmargin hclose hu
  change (∃ cell ∈ P, ∀ l ∈ cell, l.eval (v + z) ≤ 0) ↔
    (∃ cell' ∈ P.map (fun cell => cell.map (deformLine φ)),
      ∀ l' ∈ cell', l'.eval (deformPoint φ v + z) ≤ 0)
  constructor
  · rintro ⟨cell, hcell, hlines⟩
    refine ⟨cell.map (deformLine φ), List.mem_map.mpr ⟨cell, hcell, rfl⟩, ?_⟩
    intro l' hl'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
    exact (lineControl l (List.mem_flatten.mpr ⟨cell, hcell, hl⟩)).mp (hlines l hl)
  · rintro ⟨cell', hcell', hlines⟩
    obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hcell'
    refine ⟨cell, hcell, ?_⟩
    intro l hl
    exact (lineControl l (List.mem_flatten.mpr ⟨cell, hcell, hl⟩)).mpr
      (hlines (deformLine φ l) (List.mem_map.mpr ⟨l, hl, rfl⟩))

private def polyhedralVertexCone (P : PolyhedralCode) (v : Plane) : Set Plane :=
  {z | ∃ cell ∈ P, ∀ l ∈ cell,
    l.eval v < 0 ∨ (l.eval v = 0 ∧ normalEval l.normal z ≤ 0)}

private theorem polyhedralVertexCone_isClosed (P : PolyhedralCode) (v : Plane) :
    IsClosed (polyhedralVertexCone P v) := by
  classical
  have hline (l : RationalLine) :
      IsClosed {z | l.eval v < 0 ∨ (l.eval v = 0 ∧ normalEval l.normal z ≤ 0)} := by
    by_cases hneg : l.eval v < 0
    · simpa [hneg] using (isClosed_univ : IsClosed (Set.univ : Set Plane))
    · by_cases hzero : l.eval v = 0
      · simpa [hneg, hzero, normalCLM_apply] using
          (isClosed_le (normalCLM l.normal).continuous continuous_const :
            IsClosed {z : Plane | normalCLM l.normal z ≤ 0})
      · simpa [hneg, hzero] using
          (isClosed_empty : IsClosed (∅ : Set Plane))
  have hcell (cell : List RationalLine) :
      IsClosed {z | ∀ l ∈ cell, l.eval v < 0 ∨
        (l.eval v = 0 ∧ normalEval l.normal z ≤ 0)} := by
    have heq : {z | ∀ l ∈ cell, l.eval v < 0 ∨
        (l.eval v = 0 ∧ normalEval l.normal z ≤ 0)} =
        ⋂ l ∈ cell.toFinset, {z | l.eval v < 0 ∨
          (l.eval v = 0 ∧ normalEval l.normal z ≤ 0)} := by
      ext z
      simp
    rw [heq]
    exact isClosed_iInter (fun l => isClosed_iInter (fun _ => hline l))
  have heq : polyhedralVertexCone P v =
      ⋃ cell ∈ P.toFinset, {z | ∀ l ∈ cell, l.eval v < 0 ∨
        (l.eval v = 0 ∧ normalEval l.normal z ≤ 0)} := by
    ext z
    simp [polyhedralVertexCone]
  rw [heq]
  exact isClosed_biUnion_finset (fun cell _ => hcell cell)

private theorem polyhedralVertexCone_scale (P : PolyhedralCode) (v z : Plane)
    (c : ℝ) (hc : 0 < c) :
    c • z ∈ polyhedralVertexCone P v ↔ z ∈ polyhedralVertexCone P v := by
  have hscale (n : RationalNormal) : normalEval n (c • z) ≤ 0 ↔ normalEval n z ≤ 0 := by
    rw [← normalCLM_apply, map_smul, normalCLM_apply, smul_eq_mul]
    constructor
    · intro h
      nlinarith
    · intro h
      exact mul_nonpos_of_nonneg_of_nonpos hc.le h
  constructor <;> rintro ⟨cell, hcell, hlines⟩ <;> refine ⟨cell, hcell, ?_⟩
  · intro l hl
    rcases hlines l hl with hneg | ⟨hzero, hnonpos⟩
    · exact Or.inl hneg
    · exact Or.inr ⟨hzero, (hscale l.normal).mp hnonpos⟩
  · intro l hl
    rcases hlines l hl with hneg | ⟨hzero, hnonpos⟩
    · exact Or.inl hneg
    · exact Or.inr ⟨hzero, (hscale l.normal).mpr hnonpos⟩

/-- A single radius gives the exact homogeneous cone at every chosen prototype
    vertex. Nonincident inequalities retain their strictly signed margin. -/
private theorem polyhedralSupport_uniformVertexCones (P : PolyhedralCode) (W : Finset Plane) :
    ∃ r : ℝ, 0 < r ∧ ∀ v ∈ W, ∀ z : Plane, dist z 0 < r →
      (v + z ∈ polyhedralSupport P ↔ z ∈ polyhedralVertexCone P v) := by
  classical
  let L : Finset RationalLine := P.flatten.toFinset
  let F : Finset ℝ := L.biUnion fun l => W.image (fun v => l.eval v)
  obtain ⟨δ, hδ, hδF⟩ := exists_positiveMinAbs F
  let B : ℝ := 1 + ∑ l ∈ L, ‖normalCLM l.normal‖
  have hB : 0 < B := by
    dsimp [B]
    have hsum : 0 ≤ ∑ l ∈ L, ‖normalCLM l.normal‖ :=
      Finset.sum_nonneg fun l hl => norm_nonneg _
    linarith
  let r : ℝ := δ / (4 * B)
  refine ⟨r, by dsimp [r]; positivity, ?_⟩
  intro v hv z hz
  have hzNorm : ‖z‖ < r := by simpa [dist_eq_norm] using hz
  have hline (l : RationalLine) (hl : l ∈ P.flatten) :
      l.eval (v + z) ≤ 0 ↔
        l.eval v < 0 ∨ (l.eval v = 0 ∧ normalEval l.normal z ≤ 0) := by
    have hlL : l ∈ L := List.mem_toFinset.mpr hl
    have hvF : l.eval v ∈ F := Finset.mem_biUnion.mpr
      ⟨l, hlL, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
    have hu : |normalEval l.normal z| < δ / 4 := by
      have hcoef : ‖normalCLM l.normal‖ ≤ B := finiteNormalEval_norm_bound L l hlL
      have hmul : ‖normalCLM l.normal‖ * ‖z‖ < B * r := by
        calc
          ‖normalCLM l.normal‖ * ‖z‖ ≤ B * ‖z‖ := by gcongr
          _ < B * r := mul_lt_mul_of_pos_left hzNorm hB
      have hBr : B * r = δ / 4 := by dsimp [r]; field_simp
      exact (normalEval_norm_bound _ _).trans_lt (by simpa [hBr] using hmul)
    have heval : l.eval (v + z) = l.eval v + normalEval l.normal z := by
      simp [RationalLine.eval, normalEval_add]
      ring
    rw [heval]
    by_cases hzero : l.eval v = 0
    · simp [hzero]
    · have hmargin := hδF _ hvF hzero
      have hu' := abs_lt.mp hu
      rcases lt_or_gt_of_ne hzero with hneg | hpos
      · rw [abs_of_neg hneg] at hmargin
        have hsumneg : l.eval v + normalEval l.normal z < 0 := by linarith
        simp [hneg, hsumneg.le]
      · rw [abs_of_pos hpos] at hmargin
        have hsumpos : 0 < l.eval v + normalEval l.normal z := by linarith
        simp [not_le_of_gt hsumpos, not_lt_of_ge hpos.le, hzero]
  constructor <;> rintro ⟨cell, hcell, hlines⟩ <;> refine ⟨cell, hcell, ?_⟩
  · intro l hl
    exact (hline l (List.mem_flatten.mpr ⟨cell, hcell, hl⟩)).mp (hlines l hl)
  · intro l hl
    exact (hline l (List.mem_flatten.mpr ⟨cell, hcell, hl⟩)).mpr (hlines l hl)

private theorem polyhedralSupport_uniformDeformedVertexCones
    (P : PolyhedralCode) (W : Finset Plane) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ v ∈ W, ∀ z : Plane, dist z 0 < r →
          (v + z ∈ polyhedralSupport P ↔ z ∈ polyhedralVertexCone P v) ∧
          (deformPoint φ v + z ∈ deformedPolyhedralSupport P φ ↔
            z ∈ polyhedralVertexCone P v) := by
  obtain ⟨F, ε, r₀, hε, hr₀, halign⟩ := polyhedralSupport_uniformAlignedSupport P W
  obtain ⟨r₁, hr₁, hcone⟩ := polyhedralSupport_uniformVertexCones P W
  refine ⟨F, ε, min r₀ r₁, hε, lt_min hr₀ hr₁, ?_⟩
  intro φ hφ v hv z hz
  have hsource := hcone v hv z (hz.trans_le (min_le_right _ _))
  exact ⟨hsource, (halign φ hφ v hv z (hz.trans_le (min_le_left _ _))).symm.trans hsource⟩

private theorem prototypeVertexCone_interior_nonempty (K : PolygonalRegion)
    (P : PolyhedralCode) (hP : polyhedralSupport P = K.support)
    (v : Plane) (hv : v ∈ K.support) :
    (interior (polyhedralVertexCone P v)).Nonempty := by
  classical
  obtain ⟨r, hr, hcone⟩ := polyhedralSupport_uniformVertexCones P {v}
  have hvcl : v ∈ closure K.openCarrier := by
    simpa only [PolygonalRegion.openCarrier, K.isPolygonal.closure_interior] using hv
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hvcl r hr
  let z := y - v
  have hz : z ∈ Metric.ball 0 r := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero, z, norm_sub_rev] using hdist
  have hUopen : IsOpen ((-v +ᵥ K.openCarrier) ∩ Metric.ball 0 r) :=
    (isOpen_interior.vadd (-v)).inter Metric.isOpen_ball
  have hUsub : (-v +ᵥ K.openCarrier) ∩ Metric.ball 0 r ⊆ polyhedralVertexCone P v := by
    intro w hw
    apply (hcone v (by simp) w hw.2).mp
    rw [hP]
    have hwK : v + w ∈ K.openCarrier := by
      simpa only [neg_neg, vadd_eq_add] using Set.mem_vadd_set_iff_neg_vadd_mem.mp hw.1
    exact interior_subset hwK
  refine ⟨z, interior_maximal hUsub hUopen ⟨?_, hz⟩⟩
  apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
  simpa [z, vadd_eq_add] using hy

private theorem exists_planarCrossCLM_normalizer {v : Plane} (hv : v ≠ 0) :
    ∃ u : Plane, Tiling.planarCrossCLM v u = 1 := by
  have hnorm : 0 < Complex.normSq v := Complex.normSq_pos.mpr hv
  have hcross : Tiling.planarCrossCLM v (v * Complex.I) = Complex.normSq v := by
    rw [Tiling.planarCrossCLM_apply]
    simp [Tiling.planarCross, Complex.normSq_apply, Complex.mul_I_re, Complex.mul_I_im]
  refine ⟨(1 / Complex.normSq v) • (v * Complex.I), ?_⟩
  rw [map_smul, hcross]
  change (1 / Complex.normSq v) * Complex.normSq v = 1
  field_simp [ne_of_gt hnorm]

/-- The concrete local-half-plane adapter can be normalized to take value one
on a witness vector, as required by the closed-cone extension lemma. -/
private theorem localHalfPlane_to_normalizedLinearGerm
    (A : Set Plane) (p : Plane)
    (hloc : ∃ v : Plane, v ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (A ∩ Metric.ball p r = Tiling.positiveHalfPlane p v ∩ Metric.ball p r ∨
       A ∩ Metric.ball p r = Tiling.negativeHalfPlane p v ∩ Metric.ball p r)) :
    ∃ f : Plane →L[ℝ] ℝ, ∃ u : Plane, f u = 1 ∧ ∃ r : ℝ, 0 < r ∧
      ∀ q, dist q p < r → (q ∈ A ↔ 0 ≤ f (q - p)) := by
  obtain ⟨v, hv, r, hr, hcase⟩ := hloc
  have hside (q : Plane) : Tiling.signedSide p v q =
      Tiling.planarCrossCLM v (q - p) := by
    rw [Tiling.planarCrossCLM_apply]
    simp [Tiling.signedSide, Tiling.planarCross, Complex.sub_re, Complex.sub_im]
    ring
  rcases hcase with hpos | hneg
  · let f : Plane →L[ℝ] ℝ := Tiling.planarCrossCLM v
    obtain ⟨u, hu⟩ := exists_planarCrossCLM_normalizer hv
    refine ⟨f, u, ?_, r, hr, ?_⟩
    · exact hu
    · intro q hqp
      have hball : q ∈ Metric.ball p r := by
        simpa [Metric.mem_ball, dist_comm] using hqp
      have hmem : q ∈ A ↔ q ∈ Tiling.positiveHalfPlane p v := by
        have hEq := congrArg (fun S : Set Plane => q ∈ S) hpos
        simpa [Set.mem_inter_iff, hball] using hEq
      change q ∈ A ↔ 0 ≤ Tiling.planarCrossCLM v (q - p)
      rw [hmem, Tiling.mem_positiveHalfPlane, hside]
  · let f : Plane →L[ℝ] ℝ := -Tiling.planarCrossCLM v
    obtain ⟨u₀, hu₀⟩ := exists_planarCrossCLM_normalizer hv
    let u : Plane := -u₀
    have hcrossNeg : Tiling.planarCrossCLM v (-u₀) = -1 := by
      simp [map_neg, hu₀]
    have hu : f u = 1 := by simp [f, u, hcrossNeg]
    refine ⟨f, u, hu, r, hr, ?_⟩
    intro q hqp
    have hball : q ∈ Metric.ball p r := by
      simpa [Metric.mem_ball, dist_comm] using hqp
    have hmem : q ∈ A ↔ q ∈ Tiling.negativeHalfPlane p v := by
      have hEq := congrArg (fun S : Set Plane => q ∈ S) hneg
      simpa [Set.mem_inter_iff, hball] using hEq
    change q ∈ A ↔ 0 ≤ -Tiling.planarCrossCLM v (q - p)
    rw [hmem, Tiling.mem_negativeHalfPlane, hside]
    simp


private theorem homogeneous_set_eq_univ_of_ball
    (Q : Set Plane) (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (0 : Plane) r ⊆ Q)
    (hhom : ∀ c : ℝ, 0 < c → ∀ z : Plane, (c • z ∈ Q ↔ z ∈ Q)) :
    Q = Set.univ := by
  ext z
  constructor
  · intro _
    trivial
  · intro _
    let c : ℝ := r / (2 * (‖z‖ + 1))
    have hc : 0 < c := by dsimp [c]; positivity
    have hnorm : ‖c • z‖ < r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      have hden : 0 < 2 * (‖z‖ + 1) := by positivity
      have hscaled : c * ‖z‖ < r := by
        dsimp [c]
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ hden).2
        nlinarith [norm_nonneg z, hr]
      exact hscaled
    have hmem : c • z ∈ Metric.ball (0 : Plane) r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hnorm
    exact (hhom c hc z).mp (hball hmem)

/-- A closed positive-homogeneous set with a normalized local linear half-space
germ extends to that global closed half-space. -/
private theorem closed_homogeneous_set_eq_halfspace
    (Q : Set Plane) (f : Plane →L[ℝ] ℝ) (u : Plane) (r : ℝ)
    (hr : 0 < r) (hu : f u = 1)
    (hclosed : IsClosed Q)
    (hhom : ∀ c : ℝ, 0 < c → ∀ z : Plane, (c • z ∈ Q ↔ z ∈ Q))
    (hloc : ∀ z, dist z 0 < r → f z < 0 → z ∈ Q)
    (hside : Q ⊆ {z | f z ≤ 0}) :
    Q = {z | f z ≤ 0} := by
  have hstrict : ∀ z, f z < 0 → z ∈ Q := by
    intro z hz
    have hzne : z ≠ 0 := by
      intro hzero
      subst z
      simp at hz
    have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hzne
    let c : ℝ := r / (2 * (‖z‖ + 1))
    have hc : 0 < c := by dsimp [c]; positivity
    have hnorm : ‖c • z‖ < r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      have hden : 0 < 2 * (‖z‖ + 1) := by positivity
      have hscaled : c * ‖z‖ < r := by
        dsimp [c]
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ hden).2
        nlinarith [norm_nonneg z, hr]
      exact hscaled
    have hfc : f (c • z) < 0 := by
      rw [map_smul]
      exact mul_neg_of_pos_of_neg hc hz
    have hcQ : c • z ∈ Q := hloc (c • z) (by simpa [dist_eq_norm] using hnorm) hfc
    exact (hhom c hc z).mp hcQ
  ext z
  constructor
  · intro hzQ
    exact hside hzQ
  · intro hz
    by_cases hstrictZ : f z < 0
    · exact hstrict z hstrictZ
    · have hzero : f z = 0 := le_antisymm hz (le_of_not_gt hstrictZ)
      have hzclosure : z ∈ closure Q := by
        apply Metric.mem_closure_iff.mpr
        intro δ hδ
        let t : ℝ := δ / (2 * (‖u‖ + 1))
        have ht : 0 < t := by dsimp [t]; positivity
        let y : Plane := z - t • u
        have hfy : f y < 0 := by
          rw [show y = z - t • u by rfl, map_sub, map_smul, hzero, hu]
          simp [ht]
        have hyQ : y ∈ Q := hstrict y hfy
        have hden : 0 < 2 * (‖u‖ + 1) := by positivity
        have hzy : z - y = t • u := by simp [y]
        have hdist : dist z y < δ := by
          rw [dist_eq_norm, hzy]
          simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
          have hscaled : t * ‖u‖ < δ := by
            dsimp [t]
            rw [div_mul_eq_mul_div]
            apply (div_lt_iff₀ hden).2
            nlinarith [norm_nonneg u, hδ]
          exact hscaled
        exact ⟨y, hyQ, hdist⟩
      rw [hclosed.closure_eq] at hzclosure
      exact hzclosure

private def originalVertexConeUnion (K : PolygonalRegion) (P : PolyhedralCode)
    (T : Set Plane) (p : Plane) : Set Plane :=
  ⋃ s : {s : T // p ∈ (s : Plane) +ᵥ Tiling.vertexSet K.support},
    polyhedralVertexCone P (p - (s.1 : Plane))

private theorem originalVertexConeUnion_isClosed (K : PolygonalRegion) (P : PolyhedralCode)
    (T : Set Plane) (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (p : Plane) : IsClosed (originalVertexConeUnion K P T p) := by
  let J := {s : T // p ∈ (s : Plane) +ᵥ Tiling.vertexSet K.support}
  haveI : Fintype J := (originalVertexStar_finite K T hpack p).fintype
  change IsClosed (⋃ s : J, polyhedralVertexCone P (p - (s.1 : Plane)))
  exact isClosed_iUnion_of_finite (fun _ => polyhedralVertexCone_isClosed _ _)

private theorem originalVertexConeUnion_scale (K : PolygonalRegion) (P : PolyhedralCode)
    (T : Set Plane) (p z : Plane) (c : ℝ) (hc : 0 < c) :
    c • z ∈ originalVertexConeUnion K P T p ↔ z ∈ originalVertexConeUnion K P T p := by
  simp only [originalVertexConeUnion, Set.mem_iUnion]
  exact exists_congr (fun _ => polyhedralVertexCone_scale _ _ z c hc)

private theorem originalVertexConeUnion_sourceGerm (K : PolygonalRegion)
    (P : PolyhedralCode) (T : Set Plane) (hP : polyhedralSupport P = K.support) :
    ∃ r : ℝ, 0 < r ∧ ∀ p z : Plane, dist z 0 < r →
      (p + z ∈ ⋃ s : {s : T // p ∈ (s : Plane) +ᵥ Tiling.vertexSet K.support},
          (s.1 : Plane) +ᵥ K.support ↔ z ∈ originalVertexConeUnion K P T p) := by
  classical
  let W := K.isPolygonal.vertexSet_finite.toFinset
  obtain ⟨r, hr, hcone⟩ := polyhedralSupport_uniformVertexCones P W
  refine ⟨r, hr, ?_⟩
  intro p z hz
  let J := {s : T // p ∈ (s : Plane) +ᵥ Tiling.vertexSet K.support}
  have hpoint (s : J) : p - (s.1 : Plane) ∈ W := by
    apply K.isPolygonal.vertexSet_finite.mem_toFinset.mpr
    have h := Set.mem_vadd_set_iff_neg_vadd_mem.mp s.2
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using h
  have hmem (s : J) : p + z ∈ (s.1 : Plane) +ᵥ K.support ↔
      z ∈ polyhedralVertexCone P (p - (s.1 : Plane)) := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have heq : -(s.1 : Plane) +ᵥ (p + z) = (p - (s.1 : Plane)) + z := by
      change -(s.1 : Plane) + (p + z) = _
      abel
    rw [heq]
    simpa only [hP] using hcone _ (hpoint s) z hz
  simp only [originalVertexConeUnion, Set.mem_iUnion]
  exact exists_congr hmem

private theorem originalVertexConeUnion_deformedGerm (K : PolygonalRegion)
    (P : PolyhedralCode) (T : Set Plane) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p z : Plane, dist z 0 < r →
            (deformPoint φ p + z ∈
                ⋃ s : {s : T // p ∈ (s : Plane) +ᵥ Tiling.vertexSet K.support},
                  deformPoint φ (s.1 : Plane) +ᵥ Kφ.support ↔
              z ∈ originalVertexConeUnion K P T p) := by
  classical
  let W := K.isPolygonal.vertexSet_finite.toFinset
  obtain ⟨F, ε, r, hε, hr, hcone⟩ := polyhedralSupport_uniformDeformedVertexCones P W
  refine ⟨F, ε, r, hε, hr, ?_⟩
  intro φ hφ Kφ hKφ p z hz
  let J := {s : T // p ∈ (s : Plane) +ᵥ Tiling.vertexSet K.support}
  have hpoint (s : J) : p - (s.1 : Plane) ∈ W := by
    apply K.isPolygonal.vertexSet_finite.mem_toFinset.mpr
    have h := Set.mem_vadd_set_iff_neg_vadd_mem.mp s.2
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using h
  have hmem (s : J) : deformPoint φ p + z ∈ deformPoint φ (s.1 : Plane) +ᵥ Kφ.support ↔
      z ∈ polyhedralVertexCone P (p - (s.1 : Plane)) := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have hfsub : deformPoint φ (p - (s.1 : Plane)) =
        deformPoint φ p - deformPoint φ (s.1 : Plane) :=
      (deformPointLinear φ).map_sub p (s.1 : Plane)
    have heq : -deformPoint φ (s.1 : Plane) +ᵥ (deformPoint φ p + z) =
        deformPoint φ (p - (s.1 : Plane)) + z := by
      rw [hfsub]
      change -deformPoint φ (s.1 : Plane) + (deformPoint φ p + z) = _
      abel
    rw [heq, hKφ]
    exact (hcone φ hφ _ (hpoint s) z hz).2
  simp only [originalVertexConeUnion, Set.mem_iUnion]
  exact exists_congr hmem

private theorem positiveLinearGerm_mem_interior (A : Set Plane) (p : Plane)
    (f : Plane →L[ℝ] ℝ) (r : ℝ)
    (hgerm : ∀ q, dist q p < r → (q ∈ A ↔ 0 ≤ f (q - p)))
    (q : Plane) (hq : dist q p < r) (hfq : 0 < f (q - p)) : q ∈ interior A := by
  have hopen : IsOpen (Metric.ball p r ∩ {z | 0 < f (z - p)}) :=
    Metric.isOpen_ball.inter
      (isOpen_Ioi.preimage (f.continuous.comp (continuous_id.sub continuous_const)))
  have hsub : Metric.ball p r ∩ {z | 0 < f (z - p)} ⊆ A := by
    intro z hz
    exact (hgerm z hz.1).mpr hz.2.le
  exact interior_maximal hsub hopen ⟨hq, hfq⟩

private theorem exists_positiveScaling_intoBall (z : Plane) (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ dist (c • z) 0 < r := by
  have hden : 0 < ‖z‖ + 1 := by positivity
  obtain ⟨c, hc, hcb⟩ := exists_between (div_pos hr hden)
  have hbound := (lt_div_iff₀ hden).mp hcb
  refine ⟨c, hc, ?_⟩
  rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  nlinarith [norm_nonneg z]

/-- The original genuine vertex labels fill the plane, or exactly the closed
    side opposite the unique smooth label. Local original coverage is extended
    by cone homogeneity; no image incident star is selected. -/
private theorem originalVertexConeUnion_fullOrHalfPlane (K : PolygonalRegion)
    (P : PolyhedralCode) (T : Set Plane) (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (p t : Plane) (ht : t ∈ T) (hpt : p ∈ t +ᵥ Tiling.vertexSet K.support) :
    originalVertexConeUnion K P T p = Set.univ ∨
      ∃ s ∈ T, p ∈ s +ᵥ K.support ∧ p ∉ s +ᵥ Tiling.vertexSet K.support ∧
        ∃ f : Plane →L[ℝ] ℝ, ∃ u : Plane, f u = 1 ∧
          originalVertexConeUnion K P T p = {z | f z ≤ 0} ∧
          ∃ r : ℝ, 0 < r ∧ ∀ q, dist q p < r →
            (q ∈ s +ᵥ K.support ↔ 0 ≤ f (q - p)) := by
  classical
  let Q := originalVertexConeUnion K P T p
  obtain ⟨rC, hrC, hcone⟩ := originalVertexConeUnion_sourceGerm K P T hP
  obtain ⟨rS, hrS, hcover⟩ := originalClosedStar_localCover K T htile p
  have hdist (z : Plane) : dist (p + z) p = dist z 0 := by simp [dist_eq_norm]
  have hhom (c : ℝ) (hc : 0 < c) (z : Plane) : c • z ∈ Q ↔ z ∈ Q :=
    originalVertexConeUnion_scale K P T p z c hc
  by_cases hsmooth : ∃ s ∈ T, p ∈ s +ᵥ K.support ∧
      p ∉ s +ᵥ Tiling.vertexSet K.support
  · obtain ⟨s, hs, hps, hpsnot⟩ := hsmooth
    obtain ⟨f, u, hu, rH, hrH, hgerm⟩ := localHalfPlane_to_normalizedLinearGerm
      (s +ᵥ K.support) p
      (originalNonvertexStar_localHalfPlane K T htile.2.1 hs ht hpt hps hpsnot)
    let r := min rC (min rS rH)
    have hr : 0 < r := lt_min hrC (lt_min hrS hrH)
    have hlocal : ∀ z, dist z 0 < r → f z < 0 → z ∈ Q := by
      intro z hz hfz
      have hzC : dist z 0 < rC := hz.trans_le (min_le_left _ _)
      have hzS : dist (p + z) p < rS := by
        rw [hdist]
        exact hz.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hzH : dist (p + z) p < rH := by
        rw [hdist]
        exact hz.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      obtain ⟨q, hq, hpq, hqz⟩ := hcover (p + z) hzS
      by_cases hpqV : p ∈ q +ᵥ Tiling.vertexSet K.support
      · apply (hcone p z hzC).mp
        exact Set.mem_iUnion.mpr ⟨⟨⟨q, hq⟩, hpqV⟩, hqz⟩
      · have hqs := originalVertexStar_atMostOneSmoothLabel K T htile.2.1
          p t ht hpt q s hq hs hpq hps hpqV hpsnot
        have hqS : p + z ∈ s +ᵥ K.support := by simpa only [hqs] using hqz
        have hbad := (hgerm (p + z) hzH).mp hqS
        simp only [add_sub_cancel_left] at hbad
        linarith
    have hside : Q ⊆ {z | f z ≤ 0} := by
      intro z hzQ
      by_contra hnot
      have hfz : 0 < f z := lt_of_not_ge hnot
      obtain ⟨c, hc, hcz⟩ := exists_positiveScaling_intoBall z (min rC rH) (lt_min hrC hrH)
      have hczC : dist (c • z) 0 < rC := hcz.trans_le (min_le_left _ _)
      have hczH : dist (p + c • z) p < rH := by
        rw [hdist]
        exact hcz.trans_le (min_le_right _ _)
      have hpoint : p + c • z ∈
          ⋃ q : {q : T // p ∈ (q : Plane) +ᵥ Tiling.vertexSet K.support},
            (q.1 : Plane) +ᵥ K.support := (hcone p (c • z) hczC).mpr ((hhom c hc z).mpr hzQ)
      obtain ⟨q, hpointq⟩ := Set.mem_iUnion.mp hpoint
      have hsq : s ≠ (q.1 : Plane) := by
        intro heq
        apply hpsnot
        rw [heq]
        exact q.2
      have hpointS : p + c • z ∈ s +ᵥ K.openCarrier := by
        have h := positiveLinearGerm_mem_interior (s +ᵥ K.support) p f rH hgerm
          (p + c • z) hczH
            (by simpa only [add_sub_cancel_left, map_smul, smul_eq_mul] using mul_pos hc hfz)
        rwa [interior_vadd] at h
      exact Set.disjoint_left.mp
        (original_openCarrier_disjoint_otherSupport K T htile.2.1 hs q.1.2 hsq)
        hpointS hpointq
    have hhalf : Q = {z | f z ≤ 0} := closed_homogeneous_set_eq_halfspace Q f u r hr hu
      (originalVertexConeUnion_isClosed K P T htile.2.1 p) hhom hlocal hside
    exact Or.inr ⟨s, hs, hps, hpsnot, f, u, hu, hhalf, rH, hrH, hgerm⟩
  · apply Or.inl
    apply homogeneous_set_eq_univ_of_ball Q (min rC rS) (lt_min hrC hrS) ?_ hhom
    intro z hz
    have hzC : dist z 0 < rC := hz.trans_le (min_le_left _ _)
    have hzS : dist (p + z) p < rS := by
      rw [hdist]
      exact hz.trans_le (min_le_right _ _)
    obtain ⟨q, hq, hpq, hqz⟩ := hcover (p + z) hzS
    have hpqV : p ∈ q +ᵥ Tiling.vertexSet K.support := by
      by_contra hnot
      exact hsmooth ⟨q, hq, hpq, hnot⟩
    exact (hcone p z hzC).mp (Set.mem_iUnion.mpr ⟨⟨⟨q, hq⟩, hpqV⟩, hqz⟩)

private theorem deformed_originalVertexStar_fullOrHalfBall (K : PolygonalRegion)
    (P : PolyhedralCode) (T : Set Plane) (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p t : Plane, t ∈ T → p ∈ t +ᵥ Tiling.vertexSet K.support →
            (∀ z : Plane, dist z 0 < r → deformPoint φ p + z ∈
              ⋃ s : {s : T // p ∈ (s : Plane) +ᵥ Tiling.vertexSet K.support},
                deformPoint φ (s.1 : Plane) +ᵥ Kφ.support) ∨
            ∃ s ∈ T, p ∈ s +ᵥ K.support ∧ p ∉ s +ᵥ Tiling.vertexSet K.support ∧
              ∃ f : Plane →L[ℝ] ℝ, ∃ u : Plane, f u = 1 ∧
                (∀ z : Plane, dist z 0 < r →
                  (deformPoint φ p + z ∈
                      ⋃ q : {q : T // p ∈ (q : Plane) +ᵥ Tiling.vertexSet K.support},
                        deformPoint φ (q.1 : Plane) +ᵥ Kφ.support ↔ f z ≤ 0)) ∧
                ∃ rH : ℝ, 0 < rH ∧ ∀ q, dist q p < rH →
                  (q ∈ s +ᵥ K.support ↔ 0 ≤ f (q - p)) := by
  obtain ⟨F, ε, r, hε, hr, htarget⟩ := originalVertexConeUnion_deformedGerm K P T
  refine ⟨F, ε, r, hε, hr, ?_⟩
  intro φ hφ Kφ hKφ p t ht hpt
  rcases originalVertexConeUnion_fullOrHalfPlane K P T hP htile p t ht hpt with
    hfull | ⟨s, hs, hps, hpsnot, f, u, hu, hhalf, rH, hrH, hsource⟩
  · left
    intro z hz
    apply (htarget φ hφ Kφ hKφ p z hz).mpr
    rw [hfull]
    exact Set.mem_univ _
  · right
    refine ⟨s, hs, hps, hpsnot, f, u, hu, ?_, rH, hrH, hsource⟩
    intro z hz
    have h := htarget φ hφ Kφ hKφ p z hz
    rwa [hhalf] at h

private theorem interior_mem_iff_of_ball_eq
    (A B : Set Plane) (r : ℝ) (hr : 0 < r)
    (hlocal : ∀ z, dist z 0 < r → (z ∈ A ↔ z ∈ B)) :
    ∀ z, dist z 0 < r → (z ∈ interior A ↔ z ∈ interior B) := by
  intro z hz
  have hmargin : 0 < r - dist z 0 := by linarith
  have hEq : A =ᶠ[nhds z] B := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨r - dist z 0, hmargin, ?_⟩
    intro y hy
    apply propext
    exact hlocal y (lt_of_le_of_lt (dist_triangle y z 0) (by linarith))
  exact hEq.mem_interior_iff

/-- The frontier of a compact set is no farther from an incident point than
any point outside its interior. -/
private theorem compact_frontier_infDist_le_of_notInterior
    (D : Set Plane) (hD : IsCompact D) (x y : Plane)
    (hx : x ∈ D) (hy : y ∉ interior D) :
    Metric.infDist x (frontier D) ≤ dist x y := by
  obtain ⟨z, hz, hxz⟩ := hD.exists_mem_frontier_infDist_compl_eq_dist hx
  have hycl : y ∈ closure Dᶜ := by
    simpa [closure_eq_compl_interior_compl] using hy
  calc
    Metric.infDist x (frontier D) ≤ dist x z := Metric.infDist_le_dist_of_mem hz
    _ = Metric.infDist x Dᶜ := hxz.symm
    _ = Metric.infDist x (closure Dᶜ) := by rw [Metric.infDist_closure]
    _ ≤ dist x y := Metric.infDist_le_dist_of_mem hycl


/-- Uniform local agreement of each original genuine-vertex label, including
its interior. This is indexed by the original star, not an image incident star. -/
private theorem originalVertexCopies_uniformAlignedGerm (K : PolygonalRegion)
    (P : PolyhedralCode) (T : Set Plane) (hP : polyhedralSupport P = K.support) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p s : Plane, s ∈ T → p ∈ s +ᵥ Tiling.vertexSet K.support →
            ∀ z : Plane, dist z 0 < r →
              (p + z ∈ s +ᵥ K.support ↔
                deformPoint φ p + z ∈ deformPoint φ s +ᵥ Kφ.support) ∧
              (p + z ∈ s +ᵥ K.openCarrier ↔
                deformPoint φ p + z ∈ deformPoint φ s +ᵥ Kφ.openCarrier) := by
  classical
  let W := K.isPolygonal.vertexSet_finite.toFinset
  obtain ⟨F, ε, r, hε, hr, hcone⟩ := polyhedralSupport_uniformDeformedVertexCones P W
  refine ⟨F, ε, r, hε, hr, ?_⟩
  intro φ hφ Kφ hKφ p s hs hps z hz
  have hv : p - s ∈ W := by
    apply K.isPolygonal.vertexSet_finite.mem_toFinset.mpr
    have h := Set.mem_vadd_set_iff_neg_vadd_mem.mp hps
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using h
  let A : Set Plane := (-p) +ᵥ (s +ᵥ K.support)
  let B : Set Plane := (-deformPoint φ p) +ᵥ (deformPoint φ s +ᵥ Kφ.support)
  have hlocal (w : Plane) (hw : dist w 0 < r) : w ∈ A ↔ w ∈ B := by
    have h := hcone φ hφ (p - s) hv w hw
    have hfsub : deformPoint φ (p - s) = deformPoint φ p - deformPoint φ s :=
      (deformPointLinear φ).map_sub p s
    have hsource : w ∈ A ↔ (p - s) + w ∈ polyhedralSupport P := by
      simp only [A, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, hP]
      congr 1
      abel
    have htarget : w ∈ B ↔ deformPoint φ (p - s) + w ∈
        deformedPolyhedralSupport P φ := by
      simp only [B, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, hKφ]
      rw [hfsub]
      congr 1
      abel
    exact hsource.trans (h.1.trans h.2.symm) |>.trans htarget.symm
  have hclosed := hlocal z hz
  have hopen := interior_mem_iff_of_ball_eq A B r hr hlocal z hz
  constructor
  · simpa only [A, B, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add] using hclosed
  · simpa only [A, B, interior_vadd, Set.mem_vadd_set_iff_neg_vadd_mem,
      neg_neg, vadd_eq_add, PolygonalRegion.openCarrier] using hopen

/-- Local packing on the original genuine star, obtained from aligned germs
and original packing before any image local finiteness or label injection. -/
private theorem originalVertexStar_deformedLocalPacking (K : PolygonalRegion)
    (P : PolyhedralCode) (T : Set Plane) (hP : polyhedralSupport P = K.support)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p s t z : Plane, s ∈ T → t ∈ T → s ≠ t →
            p ∈ s +ᵥ Tiling.vertexSet K.support →
            p ∈ t +ᵥ Tiling.vertexSet K.support → dist z 0 < r →
            deformPoint φ p + z ∈ deformPoint φ t +ᵥ Kφ.support →
            deformPoint φ p + z ∉ deformPoint φ s +ᵥ Kφ.openCarrier := by
  obtain ⟨F, ε, r, hε, hr, hgerm⟩ := originalVertexCopies_uniformAlignedGerm K P T hP
  refine ⟨F, ε, r, hε, hr, ?_⟩
  intro φ hφ Kφ hKφ p s t z hs ht hst hps hpt hz hzt hzs
  have hztsource := (hgerm φ hφ Kφ hKφ p t ht hpt z hz).1.mpr hzt
  have hzssource := (hgerm φ hφ Kφ hKφ p s hs hps z hz).2.mpr hzs
  exact Set.disjoint_left.mp
    (original_openCarrier_disjoint_otherSupport K T hpack hs ht hst) hzssource hztsource


/-- The star-covered branch of the labelled collar, measured against the frontier
of the full neighbouring copy. No component frontier or unlabelled image is
substituted. The queried copy itself is an original vertex-star label. -/
private theorem originalVertexStar_coveredPoint_labelledCollar (K : PolygonalRegion)
    (P : PolyhedralCode) (T : Set Plane) (hP : polyhedralSupport P = K.support)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p t : Plane, t ∈ T → p ∈ t +ᵥ Tiling.vertexSet K.support →
            ∀ x : Plane, dist x (deformPoint φ p) < r / 2 →
              x - deformPoint φ p ∈ originalVertexConeUnion K P T p →
              ∀ η : ℝ, 0 < η → η < r / 2 →
                0 < Metric.infDist x (deformPoint φ t +ᵥ Kφ.support) →
                Metric.infDist x (deformPoint φ t +ᵥ Kφ.support) < η →
                ∃ s ∈ T, s ≠ t ∧ x ∈ deformPoint φ s +ᵥ Kφ.support ∧
                  Metric.infDist x (deformPoint φ s +ᵥ frontier Kφ.support) < η := by
  obtain ⟨F₀, ε₀, r₀, hε₀, hr₀, hcone⟩ := originalVertexConeUnion_deformedGerm K P T
  obtain ⟨F₁, ε₁, r₁, hε₁, hr₁, hpackgerm⟩ :=
    originalVertexStar_deformedLocalPacking K P T hP hpack
  let r := min r₀ r₁
  refine ⟨F₀ ∪ F₁, min ε₀ ε₁, r, lt_min hε₀ hε₁, lt_min hr₀ hr₁, ?_⟩
  intro φ hφ Kφ hKφ p t ht hpt x hx hcovered η hη hηr hpos hnear
  have hφ₀ := finiteApproximation_strengthen F₀ (F₀ ∪ F₁) ε₀ (min ε₀ ε₁) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφ₁ := finiteApproximation_strengthen F₁ (F₀ ∪ F₁) ε₁ (min ε₀ ε₁) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  have hr : 0 < r := lt_min hr₀ hr₁
  have hxlocal : dist (x - deformPoint φ p) 0 < r₀ := by
    have hx' : dist x (deformPoint φ p) < r := by linarith
    simpa only [dist_eq_norm, sub_zero] using hx'.trans_le (min_le_left _ _)
  have hxstar : x ∈
      ⋃ s : {s : T // p ∈ (s : Plane) +ᵥ Tiling.vertexSet K.support},
        deformPoint φ (s.1 : Plane) +ᵥ Kφ.support := by
    have h := (hcone φ hφ₀ Kφ hKφ p (x - deformPoint φ p) hxlocal).mpr
      hcovered
    simpa only [add_sub_cancel] using h
  obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hxstar
  have hst : (s.1 : Plane) ≠ t := by
    intro heq
    have hxt : x ∈ deformPoint φ t +ᵥ Kφ.support := by simpa only [heq] using hxs
    have hinf := Metric.infDist_le_dist_of_mem (x := x) hxt
    simp only [dist_self] at hinf
    linarith
  have htNonempty : (deformPoint φ t +ᵥ Kφ.support).Nonempty := by
    obtain ⟨q, hq⟩ := Kφ.nonempty
    exact ⟨deformPoint φ t +ᵥ q, Set.vadd_mem_vadd_set hq⟩
  obtain ⟨y, hyt, hxy⟩ := (Kφ.isPolygonal.isClosed.vadd (deformPoint φ t)).exists_infDist_eq_dist
    htNonempty x
  have hynear : dist y (deformPoint φ p) < r₁ := by
    have hdxy : dist x y < η := by rwa [hxy] at hnear
    have htri := dist_triangle y x (deformPoint φ p)
    rw [dist_comm y x] at htri
    have hym : dist y (deformPoint φ p) < r := by linarith
    exact hym.trans_le (min_le_right _ _)
  have hyoutside : y ∉ interior (deformPoint φ (s.1 : Plane) +ᵥ Kφ.support) := by
    rw [interior_vadd]
    have hz : dist (y - deformPoint φ p) 0 < r₁ := by
      simpa only [dist_eq_norm, sub_zero] using hynear
    have htmem : deformPoint φ p + (y - deformPoint φ p) ∈
        deformPoint φ t +ᵥ Kφ.support := by simpa only [add_sub_cancel] using hyt
    have h := hpackgerm φ hφ₁ Kφ hKφ p (s.1 : Plane) t (y - deformPoint φ p)
      s.1.2 ht hst s.2 hpt hz htmem
    simpa only [add_sub_cancel, PolygonalRegion.openCarrier] using h
  refine ⟨s.1, s.1.2, hst, hxs, ?_⟩
  have hdist := compact_frontier_infDist_le_of_notInterior
    (deformPoint φ (s.1 : Plane) +ᵥ Kφ.support)
    (Kφ.isPolygonal.isCompact.vadd _) x y hxs hyoutside
  have hfrontier : frontier (deformPoint φ (s.1 : Plane) +ᵥ Kφ.support) =
      deformPoint φ (s.1 : Plane) +ᵥ frontier Kφ.support := by
    rw [frontier, closure_vadd, interior_vadd, ← Set.vadd_set_sdiff]
    rfl
  rw [hfrontier] at hdist
  exact hdist.trans_lt (by rwa [hxy] at hnear)

private theorem deformPoint_integerMultiple (φ : ℝ →ₗ[ℚ] ℚ) (c : ℝ)
    (z : Tiling.RationalPolygonal.IntegerPlane) :
    deformPoint φ (c • Tiling.RationalPolygonal.integerPoint z) =
      (φ c : ℝ) • Tiling.RationalPolygonal.integerPoint z := by
  have hmul (k : ℤ) : (φ (c * (k : ℝ)) : ℝ) = (φ c : ℝ) * (k : ℝ) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (φ.map_smul (k : ℚ) c)
    simpa [Rat.smul_def, mul_comm] using h
  apply Complex.ext <;>
    simp [deformPoint, Tiling.RationalPolygonal.integerPoint, hmul, mul_comm]

private theorem deformPoint_integerCarrierParameter (φ : ℝ →ₗ[ℚ] ℚ)
    (a : Plane) (r : ℝ) (z : Tiling.RationalPolygonal.IntegerPlane) :
    deformPoint φ (a + r • Tiling.RationalPolygonal.integerPoint z) =
      deformPoint φ a + (φ r : ℝ) • Tiling.RationalPolygonal.integerPoint z := by
  have hmap : deformPoint φ (a + r • Tiling.RationalPolygonal.integerPoint z) =
      deformPoint φ a + deformPoint φ (r • Tiling.RationalPolygonal.integerPoint z) :=
    (deformPointLinear φ).map_add _ _
  rw [hmap, deformPoint_integerMultiple]


private theorem rationalVector_positiveIntegerMultiple (v : Plane)
    (hv : Tiling.RationalSlopes.IsRationalVectorDirection v) :
    ∃ z : Tiling.RationalPolygonal.IntegerPlane, ∃ c : ℝ,
      0 < c ∧ v = c • Tiling.RationalPolygonal.integerPoint z := by
  obtain ⟨z, hz, c, hc, heq⟩ := (Tiling.RationalSlopes.isRationalVectorDirection_iff v).mp hv
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · refine ⟨-z, -c, neg_pos.mpr hcneg, ?_⟩
    rw [heq]
    apply Complex.ext <;> simp [Tiling.RationalPolygonal.integerPoint]
  · exact ⟨z, c, hcpos, heq⟩

private theorem finite_rational_edge_integer_alphabet
    (E : Finset (Plane × Plane))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1)) :
    ∃ Z : {e // e ∈ E} → Tiling.RationalPolygonal.IntegerPlane,
      ∃ C : {e // e ∈ E} → ℝ, ∃ D : Finset ℝ, ∃ ε : ℝ,
        (∀ i, 0 < C i ∧ Tiling.RationalPolygonal.integerPoint (Z i) ≠ 0 ∧
          i.1.2 - i.1.1 = C i • Tiling.RationalPolygonal.integerPoint (Z i)) ∧
        (∀ c ∈ D, 0 < c) ∧
        (∀ i e, e ∈ E → ∀ c, 0 < c →
          (e.2 - e.1 = c • Tiling.RationalPolygonal.integerPoint (Z i) ∨
            e.1 - e.2 = c • Tiling.RationalPolygonal.integerPoint (Z i)) → c ∈ D) ∧
        0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation D ε φ →
          ∀ i e, e ∈ E → ∀ c, 0 < c →
            (e.2 - e.1 = c • Tiling.RationalPolygonal.integerPoint (Z i) ∨
              e.1 - e.2 = c • Tiling.RationalPolygonal.integerPoint (Z i)) →
            c / 2 ≤ (φ c : ℝ) ∧ (φ c : ℝ) ≤ 2 * c := by
  classical
  let I := {e // e ∈ E}
  have hrep (i : I) := rationalVector_positiveIntegerMultiple
    (i.1.2 - i.1.1) (hrat i.1 i.2)
  choose Z C hCpos hCeq using hrep
  have hZne (i : I) : Tiling.RationalPolygonal.integerPoint (Z i) ≠ 0 := by
    intro hzero
    have hi := (hrat i.1 i.2).1
    rw [hCeq i, hzero, smul_zero] at hi
    exact hi rfl
  let Q₀ := I × (I × Bool)
  let Q := {q : Q₀ // ∃ c : ℝ, 0 < c ∧
    (if q.2.2 then q.2.1.1.2 - q.2.1.1.1
      else q.2.1.1.1 - q.2.1.1.2) = c • Tiling.RationalPolygonal.integerPoint (Z q.1)}
  let pick (q : Q) : ℝ := Classical.choose q.2
  let D : Finset ℝ := Finset.univ.image pick
  obtain ⟨ε, hε, hcontrol⟩ := finite_positive_deformation_bounds D
  have hDpos : ∀ c ∈ D, 0 < c := by
    intro c hc
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
    exact (Classical.choose_spec q.2).1
  have hAlphabet : ∀ i e, e ∈ E → ∀ c, 0 < c →
      (e.2 - e.1 = c • Tiling.RationalPolygonal.integerPoint (Z i) ∨
        e.1 - e.2 = c • Tiling.RationalPolygonal.integerPoint (Z i)) → c ∈ D := by
    intro i e heE c hc he
    rcases he with hforward | hbackward
    · let ei : I := ⟨e, heE⟩
      let q₀ : Q₀ := (i, (ei, true))
      have hqprop : ∃ c' : ℝ, 0 < c' ∧
          (if q₀.2.2 then q₀.2.1.1.2 - q₀.2.1.1.1
            else q₀.2.1.1.1 - q₀.2.1.1.2) = c' • Tiling.RationalPolygonal.integerPoint (Z q₀.1) := by
        refine ⟨c, hc, ?_⟩
        simpa [q₀] using hforward
      let q : Q := ⟨q₀, hqprop⟩
      have hchosen := Classical.choose_spec q.2
      have heq : pick q = c := by
        apply (smul_left_injective ℝ (hZne i))
        simpa [pick, q, q₀] using hchosen.2.symm.trans hforward
      exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, heq⟩
    · let ei : I := ⟨e, heE⟩
      let q₀ : Q₀ := (i, (ei, false))
      have hqprop : ∃ c' : ℝ, 0 < c' ∧
          (if q₀.2.2 then q₀.2.1.1.2 - q₀.2.1.1.1
            else q₀.2.1.1.1 - q₀.2.1.1.2) = c' • Tiling.RationalPolygonal.integerPoint (Z q₀.1) := by
        refine ⟨c, hc, ?_⟩
        simpa [q₀] using hbackward
      let q : Q := ⟨q₀, hqprop⟩
      have hchosen := Classical.choose_spec q.2
      have heq : pick q = c := by
        apply (smul_left_injective ℝ (hZne i))
        simpa [pick, q, q₀] using hchosen.2.symm.trans hbackward
      exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, heq⟩
  refine ⟨Z, C, D, ε, ?_, hDpos, hAlphabet, hε, ?_⟩
  · intro i
    exact ⟨hCpos i, hZne i, hCeq i⟩
  · intro φ hφ i e heE c hc he
    exact hcontrol φ hφ c (hAlphabet i e heE c hc he) hc


/-- Actual rational prototype edge vectors retain their orientation and a
uniform positive length. No order between vertices from different labels is
asserted; only each individual full prototype edge is controlled. -/
private theorem finiteRationalEdges_positiveHomotheties (E : Finset (Plane × Plane))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1)) :
    ∃ F : Finset ℝ, ∃ ε l : ℝ, 0 < ε ∧ 0 < l ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ e ∈ E, ∃ c : ℝ, 1 / 2 ≤ c ∧ c ≤ 2 ∧
          deformPoint φ e.2 - deformPoint φ e.1 = c • (e.2 - e.1) ∧
          l ≤ dist (deformPoint φ e.1) (deformPoint φ e.2) := by
  classical
  have hrep (e : {e // e ∈ E}) := rationalVector_positiveIntegerMultiple
    (e.1.2 - e.1.1) (hrat e.1 e.2)
  choose Z C hCpos hCeq using hrep
  let F : Finset ℝ := E.attach.image C
  obtain ⟨ε, hε, hcontrol⟩ := finite_positive_deformation_bounds F
  let D := E.image (fun e => dist e.1 e.2)
  obtain ⟨δ, hδ, hδD⟩ := exists_positiveMinAbs D
  refine ⟨F, ε, δ / 2, hε, by positivity, ?_⟩
  intro φ hφ e he
  let q : {e // e ∈ E} := ⟨e, he⟩
  have hqF : C q ∈ F := Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩
  have hbounds := hcontrol φ hφ (C q) hqF (hCpos q)
  let c : ℝ := (φ (C q) : ℝ) / C q
  have hc : 1 / 2 ≤ c ∧ c ≤ 2 := by
    dsimp [c]
    constructor
    · apply (le_div_iff₀ (hCpos q)).mpr
      linarith [hbounds.1]
    · apply (div_le_iff₀ (hCpos q)).mpr
      exact hbounds.2
  have hvec : deformPoint φ e.2 - deformPoint φ e.1 = c • (e.2 - e.1) := by
    have hfsub : deformPoint φ (e.2 - e.1) = deformPoint φ e.2 - deformPoint φ e.1 :=
      (deformPointLinear φ).map_sub e.2 e.1
    rw [← hfsub, hCeq q, deformPoint_integerMultiple,
      smul_smul]
    congr 1
    dsimp [c]
    field_simp [(hCpos q).ne']
  have hene : e.1 ≠ e.2 := fun h => (hrat e he).1 (by simp [h])
  have hed : dist e.1 e.2 ≠ 0 := (dist_pos.mpr hene).ne'
  have hdmin := hδD (dist e.1 e.2) (Finset.mem_image.mpr ⟨e, he, rfl⟩) hed
  rw [abs_of_nonneg dist_nonneg] at hdmin
  refine ⟨c, hc.1, hc.2, hvec, ?_⟩
  have hnorm : dist (deformPoint φ e.1) (deformPoint φ e.2) = c * dist e.1 e.2 := by
    rw [dist_comm, dist_eq_norm, hvec, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith [hc.1]), ← dist_eq_norm, dist_comm e.2 e.1]
  rw [hnorm]
  nlinarith [dist_nonneg (x := e.1) (y := e.2)]

private theorem finiteRationalEdges_uniformLengthRange (E : Finset (Plane × Plane))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1)) :
    ∃ F : Finset ℝ, ∃ ε l L : ℝ, 0 < ε ∧ 0 < l ∧ 0 < L ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ e ∈ E, l ≤ dist (deformPoint φ e.1) (deformPoint φ e.2) ∧
          dist (deformPoint φ e.1) (deformPoint φ e.2) ≤ L := by
  classical
  obtain ⟨F, ε, l, hε, hl, hcontrol⟩ := finiteRationalEdges_positiveHomotheties E hrat
  let L := 2 * (∑ e ∈ E, dist e.1 e.2) + 1
  have hsum : 0 ≤ ∑ e ∈ E, dist e.1 e.2 := Finset.sum_nonneg (fun _ _ => dist_nonneg)
  refine ⟨F, ε, l, L, hε, hl, by dsimp [L]; positivity, ?_⟩
  intro φ hφ e he
  obtain ⟨c, hc, hcupper, hvec, hlower⟩ := hcontrol φ hφ e he
  have hnorm : dist (deformPoint φ e.1) (deformPoint φ e.2) = c * dist e.1 e.2 := by
    rw [dist_comm, dist_eq_norm, hvec, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith), ← dist_eq_norm, dist_comm e.2 e.1]
  have heupper : dist e.1 e.2 ≤ ∑ f ∈ E, dist f.1 f.2 :=
    Finset.single_le_sum (fun _ _ => dist_nonneg) he
  refine ⟨hlower, ?_⟩
  rw [hnorm]
  dsimp [L]
  nlinarith [dist_nonneg (x := e.1) (y := e.2)]


private theorem segment_direction_mem_of_frontierGerm {D : Set Plane} {a b x : Plane}
    {δ : Submodule ℝ Plane} (hseg : segment ℝ a b ⊆ D)
    (hx : x ∈ segment ℝ a b)
    (hlocal : ∀ᶠ y in 𝓝 x, y ∈ D → y - x ∈ δ) : b - a ∈ δ := by
  have endpoint (p : Plane) (hp : p ∈ segment ℝ a b) : p - x ∈ δ := by
    let f : ℝ → Plane := fun t => t • (p - x) + x
    have ht : Tendsto f (𝓝 0) (𝓝 x) := by
      have hc : Continuous f := by fun_prop
      simpa only [f, zero_smul, zero_add] using hc.continuousAt.tendsto (x := (0 : ℝ))
    obtain ⟨l, u, hlu, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ht.eventually hlocal)
    let t : ℝ := min u 1 / 2
    have hupos : 0 < u := hlu.2
    have htpos : 0 < t := by dsimp [t]; positivity
    have htlt : t < u := by dsimp [t]; linarith [min_le_left u 1]
    have htle : t ≤ 1 := by dsimp [t]; linarith [min_le_right u 1]
    have hfseg : f t ∈ segment ℝ a b := by
      have hc := (convex_segment a b) hx hp (sub_nonneg.mpr htle)
        htpos.le (sub_add_cancel 1 t)
      convert hc using 1
      simp only [f, smul_sub, sub_smul, one_smul]
      abel
    have hscaled := hI ⟨lt_trans hlu.1 htpos, htlt⟩ (hseg hfseg)
    have := δ.smul_mem t⁻¹ hscaled
    simpa [f, smul_smul, htpos.ne'] using this
  have ha := endpoint a (left_mem_segment ℝ a b)
  have hb := endpoint b (right_mem_segment ℝ a b)
  convert δ.sub_mem hb ha using 1
  abel



/-- The actual finite intrinsic full-tile boundary cover consists of rational
directions. This does not treat a triangulation decoration as a vertex set. -/
private theorem exists_finite_interval_cutSubdivision
    (C : Finset ℝ) (hC : ∀ c ∈ C, 0 < c ∧ c < 1) :
    ∃ E : Finset (ℝ × ℝ),
      (∀ e ∈ E, 0 ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ 1) ∧
    (∀ e ∈ E, (e.1 = 0 ∨ e.1 ∈ C) ∧ (e.2 = 1 ∨ e.2 ∈ C)) ∧
    (∀ e ∈ E, ∀ c ∈ C, ¬ (e.1 < c ∧ c < e.2)) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ e ∈ E, x ∈ Set.Icc e.1 e.2) := by
  classical
  let A : Finset ℝ := insert 0 (insert 1 C)
  let E : Finset (ℝ × ℝ) := (A ×ˢ A).filter fun e =>
    (e.1 = 0 ∨ e.1 ∈ C) ∧ (e.2 = 1 ∨ e.2 ∈ C) ∧ e.1 < e.2 ∧
      ∀ c ∈ C, ¬ (e.1 < c ∧ c < e.2)
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨hprod, hprop⟩ := Finset.mem_filter.mp he
    obtain ⟨he1, he2⟩ := Finset.mem_product.mp hprod
    constructor
    · rcases hprop.1 with hz | hmem
      · simpa [hz]
      · exact (hC _ hmem).1.le
    constructor
    · exact hprop.2.2.1
    · rcases hprop.2.1 with hone | hmem
      · simpa [hone]
      · exact (hC _ hmem).2.le
  · intro e he
    obtain ⟨hprod, hprop⟩ := Finset.mem_filter.mp he
    exact ⟨hprop.1, hprop.2.1⟩
  · intro e he c hc hbetween
    exact (Finset.mem_filter.mp he).2.2.2.2 c hc hbetween
  · intro x hx
    let L : Finset ℝ := insert 0 (C.filter fun c => c < x)
    let R : Finset ℝ := insert 1 (C.filter fun c => x < c)
    have hL0 : (0 : ℝ) ∈ L := by simp [L]
    have hR1 : (1 : ℝ) ∈ R := by simp [R]
    have hLne : L.Nonempty := ⟨0, hL0⟩
    have hRne : R.Nonempty := ⟨1, hR1⟩
    let a := L.max' hLne
    let b₀ := R.min' hRne
    let b := if x ∈ C then x else b₀
    have haL : a ∈ L := Finset.max'_mem L hLne
    have hbR : b₀ ∈ R := Finset.min'_mem R hRne
    have hax : a ≤ x := Finset.max'_le L hLne x (by
      intro y hy
      simp only [L, Finset.mem_insert, Finset.mem_filter] at hy
      rcases hy with rfl | ⟨_, hlt⟩
      · exact hx.1
      · exact hlt.le)
    have hxb : x ≤ b := by
      by_cases hcutx : x ∈ C
      · simp [b, hcutx]
      · have hxle : x ≤ b₀ := Finset.le_min' R hRne x (by
          intro y hy
          simp only [R, Finset.mem_insert, Finset.mem_filter] at hy
          rcases hy with rfl | ⟨_, hlt⟩
          · exact hx.2
          · exact hlt.le)
        simpa [b, hcutx] using hxle
    have haA : a ∈ A := by
      simp only [L, Finset.mem_insert, Finset.mem_filter] at haL
      simp only [A, Finset.mem_insert]
      rcases haL with hzero | ⟨hc, _⟩
      · exact Or.inl hzero
      · exact Or.inr (Or.inr hc)
    have hbA : b ∈ A := by
      by_cases hcutx : x ∈ C
      · simp [b, hcutx, A]
      · have hprov : b₀ = 1 ∨ b₀ ∈ C := by
          simp only [R, Finset.mem_insert, Finset.mem_filter] at hbR
          rcases hbR with hone | ⟨hc, _⟩
          · exact Or.inl hone
          · exact Or.inr hc
        simp only [b, if_neg hcutx, A, Finset.mem_insert]
        rcases hprov with hone | hc
        · exact Or.inr (Or.inl hone)
        · exact Or.inr (Or.inr hc)
    have haProv : a = 0 ∨ a ∈ C := by
      simp only [L, Finset.mem_insert, Finset.mem_filter] at haL
      rcases haL with hzero | ⟨hc, _⟩
      · exact Or.inl hzero
      · exact Or.inr hc
    have hbProv : b = 1 ∨ b ∈ C := by
      by_cases hcutx : x ∈ C
      · simp [b, hcutx, hcutx]
      · have hprov : b₀ = 1 ∨ b₀ ∈ C := by
          simp only [R, Finset.mem_insert, Finset.mem_filter] at hbR
          rcases hbR with hone | ⟨hc, _⟩
          · exact Or.inl hone
          · exact Or.inr hc
        simpa [b, hcutx] using hprov
    have hab : a < b := by
      by_cases hcutx : x ∈ C
      · have haxlt : a < x := by
          simp only [L, Finset.mem_insert, Finset.mem_filter] at haL
          rcases haL with hzero | ⟨_, hlt⟩
          · rw [hzero]
            exact (hC x hcutx).1
          · exact hlt
        simpa [b, hcutx] using haxlt
      · by_contra hn
        have hab' : b₀ ≤ a := by simpa [b, hcutx] using le_of_not_gt hn
        have hxb₀ : x ≤ b₀ := by simpa [b, hcutx] using hxb
        have heq : a = x := le_antisymm hax (hxb₀.trans hab')
        have hbeq : b₀ = x := le_antisymm (hab'.trans heq.le) hxb₀
        simp only [L, Finset.mem_insert, Finset.mem_filter] at haL
        rcases haL with hzero | ⟨hc, hcx⟩
        · have hxzero : x = 0 := heq.symm.trans hzero
          rw [hxzero] at hbeq
          have hbR0 : b₀ ∈ insert 1 (C.filter fun c => (0 : ℝ) < c) := by
            simpa [R, hxzero] using hbR
          simp only [Finset.mem_insert, Finset.mem_filter] at hbR0
          rcases hbR0 with hone | ⟨hc, hlt⟩
          · have hfalse : (1 : ℝ) = 0 := hone.symm.trans hbeq
            norm_num at hfalse
          · linarith
        · exact (lt_irrefl x) (heq ▸ hcx)
    have hno : ∀ c ∈ C, ¬ (a < c ∧ c < b) := by
      intro c hc hcb
      by_cases hcx : c < x
      · have hmem : c ∈ L := by simp [L, hc, hcx]
        have hca : c ≤ a := Finset.le_max' L c hmem
        exact (not_lt_of_ge hca) hcb.1
      · have hxc : x ≤ c := le_of_not_gt hcx
        by_cases hstrict : x < c
        · have hmem : c ∈ R := by simp [R, hc, hstrict]
          have hbc₀ : b₀ ≤ c := Finset.min'_le R c hmem
          have hbc : b ≤ c := by
            by_cases hcutx : x ∈ C
            · simpa [b, hcutx] using hxc
            · simpa [b, hcutx] using hbc₀
          exact (not_lt_of_ge hbc) hcb.2
        · have hEq : x = c := le_antisymm hxc (le_of_not_gt hstrict)
          by_cases hcutx : x ∈ C
          · have hbx : b = x := by simp [b, hcutx]
            have hlt : x < b := hEq ▸ hcb.2
            rw [hbx] at hlt
            exact (lt_irrefl x) hlt
          · exact hcutx (hEq.symm ▸ hc)
    have heE : (a, b) ∈ E := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨haA, hbA⟩,
        haProv, hbProv, hab, hno⟩
    exact ⟨(a, b), heE, ⟨hax, hxb⟩⟩

private theorem lineMap_lineMap_apply (v w : Plane) (a b u : ℝ) :
    (AffineMap.lineMap ((AffineMap.lineMap v w) a) ((AffineMap.lineMap v w) b)) u =
      (AffineMap.lineMap v w) (a + u * (b - a)) := by
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  module

private theorem lineMap_interval_mem_segment
    (v w : Plane) (a b : ℝ) (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ 1) :
    segment ℝ ((AffineMap.lineMap v w) a) ((AffineMap.lineMap v w) b) ⊆
      segment ℝ v w := by
  intro x hx
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [segment_eq_image_lineMap]
  refine ⟨a + u * (b - a), ?_, ?_⟩
  · constructor <;> nlinarith [hu.1, hu.2]
  · rw [lineMap_lineMap_apply]

private theorem exists_openSegment_lineMap_parameter
    (v w x : Plane) (hx : x ∈ openSegment ℝ v w) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, x = (AffineMap.lineMap v w) t := by
  rw [openSegment_eq_image_lineMap] at hx
  rcases (Set.mem_image _ _ _).mp hx with ⟨t, ht, htx⟩
  exact ⟨t, ht, htx.symm⟩

private theorem lineMap_parameter_unique
    {v w x : Plane} (hvw : v ≠ w) {t u : ℝ}
    (ht : x = (AffineMap.lineMap v w) t)
    (hu : x = (AffineMap.lineMap v w) u) : t = u := by
  apply (AffineMap.lineMap_injective ℝ hvw)
  exact ht.symm.trans hu

private theorem exists_finite_vertexFree_subsegments
    (v w : Plane) (hvw : v ≠ w) (V : Finset Plane)
    (hv : v ∈ V) (hw : w ∈ V) :
    ∃ G : Finset (Plane × Plane),
      (∀ e ∈ G, e.1 ∈ V ∧ e.2 ∈ V ∧ e.1 ≠ e.2 ∧
        segment ℝ e.1 e.2 ⊆ segment ℝ v w ∧
        ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ (V : Set Plane)) ∧
      segment ℝ v w = ⋃ e ∈ G, segment ℝ e.1 e.2 := by
  classical
  let Vedge := V.filter fun x => x ∈ openSegment ℝ v w
  let tau : Plane → ℝ := fun x => if hx : x ∈ openSegment ℝ v w then
    Classical.choose (exists_openSegment_lineMap_parameter v w x hx) else 0
  let C := Vedge.image tau
  have hC : ∀ c ∈ C, 0 < c ∧ c < 1 := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    have hxo := (Finset.mem_filter.mp hx).2
    have hspec := Classical.choose_spec
      (exists_openSegment_lineMap_parameter v w x hxo)
    have htau : tau x = Classical.choose
        (exists_openSegment_lineMap_parameter v w x hxo) := by
      simp [tau, hxo]
    rw [htau]
    exact hspec.1
  obtain ⟨E, hEprop, hEends, hEnocut, hEcover⟩ :=
    exists_finite_interval_cutSubdivision C hC
  let G := E.image fun e =>
    ((AffineMap.lineMap v w) e.1, (AffineMap.lineMap v w) e.2)
  have hendpoint (r : ℝ) (hr : r = 0 ∨ r = 1 ∨ r ∈ C) :
      (AffineMap.lineMap v w) r ∈ V := by
    rcases hr with hz | hz | hc
    · simpa [hz] using hv
    · simpa [hz] using hw
    · obtain ⟨x, hx, hxt⟩ := Finset.mem_image.mp hc
      have hxo := (Finset.mem_filter.mp hx).2
      have hspec := Classical.choose_spec
        (exists_openSegment_lineMap_parameter v w x hxo)
      have hrt : tau x = r := by simpa [tau, hxo] using hxt
      have htx : tau x = Classical.choose
          (exists_openSegment_lineMap_parameter v w x hxo) := by
        simp [tau, hxo]
      have hrchoose : r = Classical.choose
          (exists_openSegment_lineMap_parameter v w x hxo) := hrt.symm.trans htx
      rw [hrchoose, ← hspec.2]
      exact (Finset.mem_filter.mp hx).1
  have hG : ∀ e ∈ G, e.1 ∈ V ∧ e.2 ∈ V ∧ e.1 ≠ e.2 ∧
      segment ℝ e.1 e.2 ⊆ segment ℝ v w ∧
      ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ (V : Set Plane) := by
    intro e he
    obtain ⟨ab, habE, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨ha, hab, hb⟩ := hEprop ab habE
    have hends := hEends ab habE
    have hleftV : ((AffineMap.lineMap v w) ab.1) ∈ V := by
      apply hendpoint ab.1
      rcases hends.1 with hz | hc
      · exact Or.inl hz
      · exact Or.inr (Or.inr hc)
    have hrightV : ((AffineMap.lineMap v w) ab.2) ∈ V := by
      apply hendpoint ab.2
      rcases hends.2 with hz | hc
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr hc)
    have habne : (AffineMap.lineMap v w) ab.1 ≠ (AffineMap.lineMap v w) ab.2 := by
      intro heq
      have : ab.1 = ab.2 := AffineMap.lineMap_injective ℝ hvw heq
      exact (ne_of_lt hab) this
    refine ⟨hleftV, hrightV, habne,
      lineMap_interval_mem_segment v w ab.1 ab.2 hab.le ha hb, ?_⟩
    intro p hp hpV
    rw [openSegment_eq_image_lineMap] at hp
    obtain ⟨u, hu, hpu⟩ := (Set.mem_image _ _ _).mp hp
    have hpar := lineMap_lineMap_apply v w ab.1 ab.2 u
    have hq : p = (AffineMap.lineMap v w) (ab.1 + u * (ab.2 - ab.1)) := by
      rw [← hpu, hpar]
    have hrange : 0 < ab.1 + u * (ab.2 - ab.1) ∧
        ab.1 + u * (ab.2 - ab.1) < 1 := by
      constructor <;> nlinarith [hu.1, hu.2, ha, hb]
    have hopen : (AffineMap.lineMap v w) (ab.1 + u * (ab.2 - ab.1)) ∈
        openSegment ℝ v w := by
      rw [openSegment_eq_image_lineMap]
      exact (Set.mem_image _ _ _).mpr ⟨_, hrange, rfl⟩
    have hc : ab.1 + u * (ab.2 - ab.1) ∈ C := by
      apply Finset.mem_image.mpr
      refine ⟨p, Finset.mem_filter.mpr ⟨hpV, ?_⟩, ?_⟩
      · exact hq ▸ hopen
      · have hpeq : p ∈ openSegment ℝ v w := hq ▸ hopen
        have hspec := Classical.choose_spec
          (exists_openSegment_lineMap_parameter v w p hpeq)
        have hchoose_r : Classical.choose
            (exists_openSegment_lineMap_parameter v w p hpeq) =
              ab.1 + u * (ab.2 - ab.1) :=
          lineMap_parameter_unique hvw hspec.2 hq
        have hτ : tau p = Classical.choose
            (exists_openSegment_lineMap_parameter v w p hpeq) := by
          simp [tau, hpeq]
        exact hτ.trans hchoose_r
    have hstrict : ab.1 < ab.1 + u * (ab.2 - ab.1) ∧
        ab.1 + u * (ab.2 - ab.1) < ab.2 := by
      constructor
      · have := mul_pos hu.1 (sub_pos.mpr hab)
        linarith
      · have := mul_pos (sub_pos.mpr hu.2) (sub_pos.mpr hab)
        linarith
    exact hEnocut ab habE _ hc hstrict
  refine ⟨G, hG, ?_⟩
  apply Subset.antisymm
  · intro p hp
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨t, ht, hpt⟩ := (Set.mem_image _ _ _).mp hp
    obtain ⟨ab, habE, htin⟩ := hEcover t ht
    have ⟨ha, hab, hb⟩ := hEprop ab habE
    have hsubparam : ∃ u ∈ Set.Icc (0 : ℝ) 1, t = ab.1 + u * (ab.2 - ab.1) := by
      refine ⟨(t - ab.1) / (ab.2 - ab.1), ?_, ?_⟩
      · change 0 ≤ (t - ab.1) / (ab.2 - ab.1) ∧
          (t - ab.1) / (ab.2 - ab.1) ≤ 1
        have hden : 0 < ab.2 - ab.1 := sub_pos.mpr hab
        constructor
        · exact div_nonneg (sub_nonneg.mpr htin.1) hden.le
        · apply (div_le_one_of_le₀ _ hden.le)
          linarith [htin.2]
      · have hden : ab.2 - ab.1 ≠ 0 := ne_of_gt (sub_pos.mpr hab)
        field_simp
        ring
    obtain ⟨u, hu, rfl⟩ := hsubparam
    have he : ((AffineMap.lineMap v w) (ab.1 + u * (ab.2 - ab.1))) =
        (AffineMap.lineMap ((AffineMap.lineMap v w) ab.1)
          ((AffineMap.lineMap v w) ab.2)) u := (lineMap_lineMap_apply v w ab.1 ab.2 u).symm
    apply Set.mem_iUnion₂.mpr
    refine ⟨((AffineMap.lineMap v w) ab.1, (AffineMap.lineMap v w) ab.2), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨ab, habE, rfl⟩
    · rw [segment_eq_image_lineMap]
      exact (Set.mem_image _ _ _).mpr ⟨u, hu, he.symm.trans hpt⟩
  · intro p hp
    obtain ⟨e, heG, hpe⟩ := Set.mem_iUnion₂.mp hp
    exact (hG e heG).2.2.2.1 hpe
private theorem exists_finite_vertexFree_intrinsicBoundarySegments
    {s : Set Plane} (hs : Tiling.IsPolygonal s) :
    ∃ G : Finset (Plane × Plane),
      (∀ e ∈ G, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet s ∧
        e.2 ∈ Tiling.vertexSet s ∧ segment ℝ e.1 e.2 ⊆ frontier s ∧
        ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet s) ∧
      frontier s = ⋃ e ∈ G, segment ℝ e.1 e.2 := by
  classical
  obtain ⟨F, hF, hcover⟩ := hs.exists_finite_intrinsic_boundarySegments
  let V := hs.vertexSet_finite.toFinset
  let parts : Plane × Plane → Finset (Plane × Plane) := fun e =>
    if he : e ∈ F then Classical.choose
      (exists_finite_vertexFree_subsegments e.1 e.2
        (hF e he).1 V
        (hs.vertexSet_finite.mem_toFinset.mpr (hF e he).2.1)
        (hs.vertexSet_finite.mem_toFinset.mpr (hF e he).2.2.1))
    else ∅
  have hparts (e : Plane × Plane) (he : e ∈ F) :
      (∀ g ∈ parts e, g.1 ∈ V ∧ g.2 ∈ V ∧ g.1 ≠ g.2 ∧
        segment ℝ g.1 g.2 ⊆ segment ℝ e.1 e.2 ∧
        ∀ p ∈ openSegment ℝ g.1 g.2, p ∉ (V : Set Plane)) ∧
      segment ℝ e.1 e.2 = ⋃ g ∈ parts e, segment ℝ g.1 g.2 := by
    dsimp [parts]
    rw [dif_pos he]
    exact Classical.choose_spec
      (exists_finite_vertexFree_subsegments e.1 e.2
        (hF e he).1 V
        (hs.vertexSet_finite.mem_toFinset.mpr (hF e he).2.1)
        (hs.vertexSet_finite.mem_toFinset.mpr (hF e he).2.2.1))
  let G := F.biUnion parts
  have hG : ∀ e ∈ G, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet s ∧
      e.2 ∈ Tiling.vertexSet s ∧ segment ℝ e.1 e.2 ⊆ frontier s ∧
      ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet s := by
    intro g hg
    obtain ⟨e, heF, hgparts⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨hne, hv, hw, hfront⟩ := hF e heF
    have hp := (hparts e heF).1 g hgparts
    refine ⟨hp.2.2.1, hs.vertexSet_finite.mem_toFinset.mp hp.1,
      hs.vertexSet_finite.mem_toFinset.mp hp.2.1, ?_, ?_⟩
    · exact hp.2.2.2.1.trans hfront
    · intro p hpseg hpV
      exact hp.2.2.2.2 p hpseg
        (hs.vertexSet_finite.mem_toFinset.mpr hpV)
  refine ⟨G, hG, ?_⟩
  apply Set.Subset.antisymm
  · intro p hp
    rw [hcover] at hp
    obtain ⟨e, heF, hpseg⟩ := Set.mem_iUnion₂.mp hp
    rw [(hparts e heF).2] at hpseg
    obtain ⟨g, hg, hpg⟩ := Set.mem_iUnion₂.mp hpseg
    exact Set.mem_iUnion₂.mpr ⟨g, Finset.mem_biUnion.mpr ⟨e, heF, hg⟩, hpg⟩
  · intro p hp
    obtain ⟨g, hg, hpg⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨e, heF, hgparts⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨_, _, _, hfront⟩ := hF e heF
    exact hfront (((hparts e heF).1 g hgparts).2.2.2.1 hpg)

private theorem frontierSegment_rationalDirection (K : PolygonalRegion)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K) (a b : Plane)
    (hne : a ≠ b) (hseg : segment ℝ a b ⊆ frontier K.support) :
    Tiling.RationalSlopes.IsRationalVectorDirection (b - a) := by
  have hinf : (segment ℝ a b).Infinite := by
    rw [segment_eq_image_lineMap]
    exact (Icc_infinite (by norm_num : (0 : ℝ) < 1)).image
      (AffineMap.lineMap_injective ℝ hne).injOn
  obtain ⟨x, hxseg, hxv⟩ := hinf.exists_notMem_finite K.isPolygonal.vertexSet_finite
  obtain ⟨δ, hdim, hratδ, hloc⟩ :=
    (Tiling.RationalSlopes.hasRationalSlopes_iff_localDirections K).mp hrat
      x (hseg hxseg) hxv
  have hdir := segment_direction_mem_of_frontierGerm hseg hxseg (hloc.mono fun y hy => hy.mp)
  have hdne : b - a ≠ 0 := sub_ne_zero.mpr hne.symm
  have heq := eq_span_singleton_of_mem_of_finrank_eq_one hdim hdir hdne
  exact ⟨hdne, heq ▸ hratδ⟩

private theorem rationalIntrinsicBoundarySegments (K : PolygonalRegion)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K) :
    ∃ E : Finset (Plane × Plane),
      (∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
        e.2 ∈ Tiling.vertexSet K.support ∧
        segment ℝ e.1 e.2 ⊆ frontier K.support ∧
        Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1)) ∧
      frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2 := by
  classical
  obtain ⟨E, hE, hcover⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  refine ⟨E, ?_, hcover⟩
  intro e he
  obtain ⟨hne, hv, hw, hseg⟩ := hE e he
  exact ⟨hne, hv, hw, hseg, frontierSegment_rationalDirection K hrat e.1 e.2 hne hseg⟩

private theorem rationalIntrinsicBoundaryEdges_uniformLengths (K : PolygonalRegion)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K) :
    ∃ E : Finset (Plane × Plane),
      (∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
        e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support) ∧
      frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2 ∧
      ∃ F : Finset ℝ, ∃ ε l : ℝ, 0 < ε ∧ 0 < l ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ e ∈ E, ∃ c : ℝ, 1 / 2 ≤ c ∧ c ≤ 2 ∧
            deformPoint φ e.2 - deformPoint φ e.1 = c • (e.2 - e.1) ∧
            l ≤ dist (deformPoint φ e.1) (deformPoint φ e.2) := by
  obtain ⟨E, hE, hcover⟩ := rationalIntrinsicBoundarySegments K hrat
  refine ⟨E, fun e he => ?_, hcover, ?_⟩
  · obtain ⟨hne, hv, hw, hseg, hdir⟩ := hE e he
    exact ⟨hne, hv, hw, hseg⟩
  · exact finiteRationalEdges_positiveHomotheties E (fun e he => (hE e he).2.2.2.2)


private theorem scalar_biInfinite_edgeChain
    (γ : ℤ → ℝ) (l : ℝ) (hl : 0 < l)
    (hstep : ∀ n : ℤ, γ n + l ≤ γ (n + 1)) :
    StrictMono γ ∧
      (∀ x : ℝ, ∃ n : ℤ, x < γ n) ∧
      (∀ x : ℝ, ∃ n : ℤ, γ n ≤ x) ∧
      (⋃ n : ℤ, Set.Icc (γ n) (γ (n + 1)) = Set.univ) ∧
      (∀ i j : ℤ, i ≠ j → Disjoint (Set.Ioo (γ i) (γ (i + 1)))
        (Set.Ioo (γ j) (γ (j + 1)))) := by
  have hsucc : ∀ n : ℤ, γ n < γ (n + 1) := by
    intro n
    exact lt_of_lt_of_le (lt_add_of_pos_right _ hl) (hstep n)
  have hmono : StrictMono γ := strictMono_int_of_lt_succ hsucc
  have hnat : ∀ k : ℕ, γ (k : ℤ) ≥ γ 0 + (k : ℝ) * l := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hstep (k : ℤ)
        have heq : ((↑(k + 1) : ℕ) : ℤ) = (k : ℤ) + 1 := by norm_num
        rw [heq]
        push_cast
        nlinarith [ih, hs]
  have hnegNat : ∀ k : ℕ, γ (-(k : ℤ)) ≤ γ 0 - (k : ℝ) * l := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hstep (-(k : ℤ) - 1)
        have hs' : γ (-(k : ℤ) - 1) + l ≤ γ (-(k : ℤ)) := by
          convert hs using 1 <;> norm_num
        have heq : -((↑(k + 1) : ℕ) : ℤ) = -(k : ℤ) - 1 := by omega
        rw [heq]
        push_cast
        nlinarith [ih, hs']
  have hright : ∀ x : ℝ, ∃ n : ℤ, x < γ n := by
    intro x
    obtain ⟨k, hk⟩ := exists_nat_gt ((x - γ 0) / l)
    have hk' : x < γ 0 + (k : ℝ) * l := by
      rw [div_lt_iff₀ hl] at hk
      nlinarith
    refine ⟨(k : ℤ), ?_⟩
    exact lt_of_lt_of_le hk' (hnat k)
  have hleft : ∀ x : ℝ, ∃ n : ℤ, γ n ≤ x := by
    intro x
    obtain ⟨k, hk⟩ := exists_nat_gt ((γ 0 - x) / l)
    have hk' : γ 0 - (k : ℝ) * l < x := by
      rw [div_lt_iff₀ hl] at hk
      nlinarith
    refine ⟨-(k : ℤ), ?_⟩
    exact le_of_lt (lt_of_le_of_lt (hnegNat k) hk')
  have hcover : (⋃ n : ℤ, Set.Icc (γ n) (γ (n + 1))) = Set.univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨n, hn⟩ := hleft x
      obtain ⟨m, hm⟩ := hright x
      obtain ⟨k, hk, hkmax⟩ := Int.exists_greatest_of_bdd (P := fun z : ℤ => γ z ≤ x)
        ⟨m, fun z hz => by
          by_contra hzm
          have hmn : m < z := lt_of_not_ge hzm
          have hmg : γ m < γ z := hmono hmn
          exact (not_lt_of_ge hz) (lt_trans hm hmg)
        ⟩
        ⟨n, hn⟩
      have hkNext : x < γ (k + 1) := by
        by_contra h
        have hnext : γ (k + 1) ≤ x := le_of_not_gt h
        have hkm : k + 1 ≤ k := hkmax (k + 1) hnext
        omega
      exact Set.mem_iUnion.mpr ⟨k, ⟨hk, hkNext.le⟩⟩
  have hdisj : ∀ i j : ℤ, i ≠ j → Disjoint
      (Set.Ioo (γ i) (γ (i + 1))) (Set.Ioo (γ j) (γ (j + 1))) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij' | hji
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have hijSucc : i + 1 ≤ j := by omega
      have hmid : γ (i + 1) ≤ γ j := hmono.monotone hijSucc
      exact (not_lt_of_ge hmid) (lt_trans hy.1 hx.2)
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have hjiSucc : j + 1 ≤ i := by omega
      have hmid : γ (j + 1) ≤ γ i := hmono.monotone hjiSucc
      exact (not_lt_of_ge hmid) (lt_trans hx.1 hy.2)
  exact ⟨hmono, hright, hleft, hcover, hdisj⟩

/-- The corresponding one-sided edge chain covers the closed ray from its first
vertex. -/
private theorem scalar_oneSided_edgeChain
    (γ : ℕ → ℝ) (l : ℝ) (hl : 0 < l)
    (hstep : ∀ n : ℕ, γ n + l ≤ γ (n + 1)) :
    StrictMono γ ∧
      (⋃ n : ℕ, Set.Icc (γ n) (γ (n + 1)) = Set.Ici (γ 0)) ∧
      (∀ i j : ℕ, i ≠ j → Disjoint (Set.Ioo (γ i) (γ (i + 1)))
        (Set.Ioo (γ j) (γ (j + 1)))) := by
  have hsucc : ∀ n : ℕ, γ n < γ (n + 1) := by
    intro n
    exact lt_of_lt_of_le (lt_add_of_pos_right _ hl) (hstep n)
  have hmono : StrictMono γ := strictMono_nat_of_lt_succ hsucc
  have hnat : ∀ k : ℕ, γ k ≥ γ 0 + (k : ℝ) * l := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hstep k
        push_cast
        nlinarith [ih, hs]
  have hright : ∀ x : ℝ, ∃ n : ℕ, x < γ n := by
    intro x
    obtain ⟨k, hk⟩ := exists_nat_gt ((x - γ 0) / l)
    have hk' : x < γ 0 + (k : ℝ) * l := by
      rw [div_lt_iff₀ hl] at hk
      nlinarith
    exact ⟨k, lt_of_lt_of_le hk' (hnat k)⟩
  have hcoverPoint : ∀ x : ℝ, γ 0 ≤ x →
      ∃ n : ℕ, γ n ≤ x ∧ x ≤ γ (n + 1) := by
    intro x hx0
    obtain ⟨k, hk⟩ := hright x
    have hEx : ∃ n : ℕ, x < γ n := ⟨k, hk⟩
    let kmin := Nat.find hEx
    have hkmin : x < γ kmin := Nat.find_spec hEx
    have hkminPos : 0 < kmin := by
      by_contra h
      have hkzero : kmin = 0 := by omega
      rw [hkzero] at hkmin
      exact (not_lt_of_ge hx0) hkmin
    let n := kmin - 1
    have hnk : n + 1 = kmin := by dsimp [n]; omega
    have hnlt : n < kmin := by omega
    have hprev : ¬ x < γ n := Nat.find_min hEx hnlt
    refine ⟨n, le_of_not_gt hprev, ?_⟩
    simpa [hnk] using hkmin.le
  have hcover : (⋃ n : ℕ, Set.Icc (γ n) (γ (n + 1))) = Set.Ici (γ 0) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact le_trans (hmono.monotone (Nat.zero_le n)) hn.1
    · intro hx
      obtain ⟨n, hnlo, hnhi⟩ := hcoverPoint x hx
      exact Set.mem_iUnion.mpr ⟨n, ⟨hnlo, hnhi⟩⟩
  have hdisj : ∀ i j : ℕ, i ≠ j → Disjoint
      (Set.Ioo (γ i) (γ (i + 1))) (Set.Ioo (γ j) (γ (j + 1))) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij' | hji
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have hijSucc : i + 1 ≤ j := by omega
      have hmid : γ (i + 1) ≤ γ j := hmono.monotone hijSucc
      exact (not_lt_of_ge hmid) (lt_trans hy.1 hx.2)
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have hjiSucc : j + 1 ≤ i := by omega
      have hmid : γ (j + 1) ≤ γ i := hmono.monotone hjiSucc
      exact (not_lt_of_ge hmid) (lt_trans hx.1 hy.2)
  exact ⟨hmono, hcover, hdisj⟩

/-- A finite initial segment of a one-sided edge chain covers exactly the
closed interval between its endpoint vertices. -/
private theorem scalar_oneSided_finitePrefix
    (γ : ℕ → ℝ) (l : ℝ) (hl : 0 < l)
    (hstep : ∀ n : ℕ, γ n + l ≤ γ (n + 1)) (N : ℕ) :
    (⋃ n ∈ Finset.range (N + 1), Set.Icc (γ n) (γ (n + 1))) =
      Set.Icc (γ 0) (γ (N + 1)) := by
  have hchain := scalar_oneSided_edgeChain γ l hl hstep
  have hmono := hchain.1
  have hcover := hchain.2.1
  ext x
  constructor
  · intro hx
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hn, hx⟩ := Set.mem_iUnion.mp hx
    have hnle : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    constructor
    · exact le_trans (hmono.monotone (Nat.zero_le n)) hx.1
    · exact le_trans hx.2 (hmono.monotone (Nat.succ_le_succ hnle))
  · intro hx
    by_cases heq : x = γ (N + 1)
    · subst x
      apply Set.mem_iUnion.mpr
      refine ⟨N, ?_⟩
      apply Set.mem_iUnion.mpr
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_self N), ?_⟩
      exact ⟨hmono.monotone (Nat.le_succ N), le_rfl⟩
    · have hxlt : x < γ (N + 1) := lt_of_le_of_ne hx.2 heq
      have hxunion : x ∈ ⋃ n : ℕ, Set.Icc (γ n) (γ (n + 1)) := by
        rw [hcover]
        exact hx.1
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxunion
      have hnlo := hn.1
      have hnhi := hn.2
      have hnle : n ≤ N := by
        by_contra hn
        have hNn : N + 1 ≤ n := by omega
        have hmono' : γ (N + 1) ≤ γ n := hmono.monotone hNn
        exact (not_lt_of_ge (le_trans hmono' hnlo)) hxlt
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      apply Set.mem_iUnion.mpr
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hnle), ⟨hnlo, hnhi⟩⟩


private theorem originalLabels_countable (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) : T.Countable :=
  (Tiling.Polygonal.packing_centres_locallyFinite hpack).2.1

/-- Countability is inherited from original packing. The deformed family need
not already be locally finite or injectively labelled for this null-set fact. -/
private theorem translatedFrontiers_volume_zero (K : PolygonalRegion)
    (T : Set Plane) (hT : T.Countable) (f : Plane → Plane) :
    volume (⋃ t : T, frontier (f t.1 +ᵥ K.support)) = 0 := by
  haveI : Countable T := hT.to_subtype
  exact measure_iUnion_null (fun t => (K.isPolygonal.vadd (f t.1)).volume_frontier)

private theorem exists_off_translatedFrontiers (K : PolygonalRegion)
    (T : Set Plane) (hT : T.Countable) (f : Plane → Plane)
    (U : Set Plane) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ t ∈ T, x ∉ frontier (f t +ᵥ K.support) := by
  classical
  have hzero := translatedFrontiers_volume_zero K T hT f
  by_contra h
  have hsub : U ⊆ ⋃ t : T, frontier (f t.1 +ᵥ K.support) := by
    intro x hx
    by_contra hxnot
    apply h
    refine ⟨x, hx, ?_⟩
    intro t ht hxt
    exact hxnot (Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hxt⟩)
  exact hU.measure_ne_zero volume hne (measure_mono_null hsub hzero)

private theorem intrinsicSegment_frontier_is_supportingLine
    {s : Set Plane} (hs : Tiling.IsPolygonal s) {v w : Plane}
    (hvw : v ≠ w) (hseg : openSegment ℝ v w ⊆ frontier s)
    (p : Plane) (hp : p ∈ openSegment ℝ v w)
    (hpv : p ∉ Tiling.vertexSet s) :
    ∃ r > 0, ∀ z ∈ Metric.ball p r,
      (z ∈ frontier s ↔ z ∈ Tiling.affineLine p (w - v)) := by
  have hstraight := hs.boundaryLocallyStraightAt_of_not_mem_vertexSet (hseg hp) hpv
  obtain ⟨L, hpL, hdim, hlocal⟩ := hstraight
  have hlocalDir : ∀ᶠ y in 𝓝 p, y ∈ frontier s → y - p ∈ L.direction := by
    filter_upwards [hlocal] with y hy hyfront
    exact (AffineSubspace.vsub_right_mem_direction_iff_mem hpL y).2 (hy.mp hyfront)
  have hsegClosed : segment ℝ v w ⊆ frontier s :=
    segment_subset_closure_openSegment.trans (closure_minimal hseg isClosed_frontier)
  have hdir := segment_direction_mem_of_frontierGerm hsegClosed
    (openSegment_subset_segment ℝ v w hp) hlocalDir
  have hspan : L.direction = ℝ ∙ (w - v) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim hdir (sub_ne_zero.mpr hvw.symm)
  have hLline : (L : Set Plane) = Tiling.affineLine p (w - v) := by
    ext z
    rw [Tiling.mem_affineLine_iff_exists_smul (sub_ne_zero.mpr hvw.symm)]
    constructor
    · intro hz
      have hzd : z - p ∈ L.direction := L.vsub_mem_direction hz hpL
      rw [hspan, Submodule.mem_span_singleton] at hzd
      rcases hzd with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      calc
        z = (z - p) + p := by abel
        _ = t • (w - v) + p := congrArg (fun q : Plane => q + p) ht.symm
        _ = p + t • (w - v) := by abel
    · rintro ⟨t, rfl⟩
      rw [add_comm]
      change t • (w - v) +ᵥ p ∈ L
      apply L.vadd_mem_of_mem_direction
      · rw [hspan]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · exact hpL
  have hlocalEdge : ∀ᶠ z in 𝓝 p,
      (z ∈ frontier s ↔ z ∈ Tiling.affineLine p (w - v)) := by
    simpa only [hLline] using hlocal
  obtain ⟨r, hr, hfrontier⟩ := Metric.eventually_nhds_iff.mp hlocalEdge
  refine ⟨r, hr, ?_⟩
  intro z hz
  exact hfrontier hz

/-- The actual side of a polygonal support at a vertex-free point of an
    intrinsic segment is measured using the fixed edge orientation. -/
private theorem intrinsicSegment_fixedOrientation_halfPlane
    {s : Set Plane} (hs : Tiling.IsPolygonal s) {v w : Plane}
    (hvw : v ≠ w) (hseg : openSegment ℝ v w ⊆ frontier s)
    (p : Plane) (hp : p ∈ openSegment ℝ v w)
    (hpv : p ∉ Tiling.vertexSet s) :
    ∃ r > 0,
      (s ∩ Metric.ball p r = Tiling.positiveHalfPlane p (w - v) ∩ Metric.ball p r ∨
        s ∩ Metric.ball p r = Tiling.negativeHalfPlane p (w - v) ∩ Metric.ball p r) := by
  obtain ⟨r, hr, hfrontier⟩ :=
    intrinsicSegment_frontier_is_supportingLine hs hvw hseg p hp hpv
  exact ⟨r, hr, Tiling.local_eq_closedHalfPlane (sub_ne_zero.mpr hvw.symm) hr
    hs.closure_interior hfrontier⟩

private theorem same_oriented_halfPlanes_on_line
    {p q d : Plane} (hd : d ≠ 0) (hq : q ∈ Tiling.affineLine p d) :
    Tiling.positiveHalfPlane p d = Tiling.positiveHalfPlane q d ∧
      Tiling.negativeHalfPlane p d = Tiling.negativeHalfPlane q d := by
  obtain ⟨t, rfl⟩ := Tiling.mem_affineLine_iff_exists_smul hd |>.mp hq
  have hc : Tiling.planarCross d (p + t • d) = Tiling.planarCross d p := by
    simp [Tiling.planarCross, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im]
    ring
  constructor <;> ext z <;>
    simp only [Tiling.positiveHalfPlane, Tiling.negativeHalfPlane, Set.mem_setOf_eq]
  · constructor
    · intro hz
      rw [hc]
      exact hz
    · intro hz
      rw [hc] at hz
      exact hz
  · constructor
    · intro hz
      rw [hc]
      exact hz
    · intro hz
      rw [hc] at hz
      exact hz

private theorem openSegment_points_share_line
    {v w p q : Plane} (hvw : v ≠ w)
    (hp : p ∈ openSegment ℝ v w) (hq : q ∈ openSegment ℝ v w) :
    q ∈ Tiling.affineLine p (w - v) := by
  rw [Tiling.mem_affineLine_iff_exists_smul (sub_ne_zero.mpr hvw.symm)]
  rw [openSegment_eq_image] at hp hq
  rcases hp with ⟨a, ha, rfl⟩
  rcases hq with ⟨b, hb, rfl⟩
  refine ⟨b - a, ?_⟩
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  module

private def positiveEdgeGerm (s : Set Plane) (d p : Plane) : Prop :=
  ∃ r > 0, s ∩ Metric.ball p r =
    Tiling.positiveHalfPlane p d ∩ Metric.ball p r

private def negativeEdgeGerm (s : Set Plane) (d p : Plane) : Prop :=
  ∃ r > 0, s ∩ Metric.ball p r =
    Tiling.negativeHalfPlane p d ∩ Metric.ball p r

private theorem positiveEdgeGerm_stable_nearby
    {s : Set Plane} {v w p q : Plane} (hvw : v ≠ w)
    (hp : p ∈ openSegment ℝ v w) (hq : q ∈ openSegment ℝ v w)
    (r : ℝ) (hr : 0 < r)
    (hEq : s ∩ Metric.ball p r =
      Tiling.positiveHalfPlane p (w - v) ∩ Metric.ball p r)
    (hclose : dist q p < r / 2) :
    positiveEdgeGerm s (w - v) q := by
  have hline := openSegment_points_share_line hvw hp hq
  have hhalves := same_oriented_halfPlanes_on_line
    (sub_ne_zero.mpr hvw.symm) hline
  refine ⟨r / 2, by positivity, ?_⟩
  ext z
  constructor
  · rintro ⟨hzs, hzq⟩
    have hzp : dist z p < r := by
      calc
        dist z p ≤ dist z q + dist q p := dist_triangle _ _ _
        _ < r / 2 + r / 2 := add_lt_add hzq hclose
        _ = r := by ring
    have hzhalf : z ∈ Tiling.positiveHalfPlane p (w - v) := by
      have : z ∈ (s ∩ Metric.ball p r) := ⟨hzs, hzp⟩
      rw [hEq] at this
      exact this.1
    exact ⟨by simpa [hhalves.1] using hzhalf, hzq⟩
  · rintro ⟨hzs, hzq⟩
    have hzhalf : z ∈ Tiling.positiveHalfPlane p (w - v) := by
      simpa [hhalves.1] using hzs
    have hzp : dist z p < r := by
      calc
        dist z p ≤ dist z q + dist q p := dist_triangle _ _ _
        _ < r / 2 + r / 2 := add_lt_add hzq hclose
        _ = r := by ring
    have hsource : z ∈ s := by
      have : z ∈ (s ∩ Metric.ball p r) := by rw [hEq]; exact ⟨hzhalf, hzp⟩
      exact this.1
    exact ⟨hsource, hzq⟩

private theorem negativeEdgeGerm_stable_nearby
    {s : Set Plane} {v w p q : Plane} (hvw : v ≠ w)
    (hp : p ∈ openSegment ℝ v w) (hq : q ∈ openSegment ℝ v w)
    (r : ℝ) (hr : 0 < r)
    (hEq : s ∩ Metric.ball p r =
      Tiling.negativeHalfPlane p (w - v) ∩ Metric.ball p r)
    (hclose : dist q p < r / 2) :
    negativeEdgeGerm s (w - v) q := by
  have hline := openSegment_points_share_line hvw hp hq
  have hhalves := same_oriented_halfPlanes_on_line
    (sub_ne_zero.mpr hvw.symm) hline
  refine ⟨r / 2, by positivity, ?_⟩
  ext z
  constructor
  · rintro ⟨hzs, hzq⟩
    have hzp : dist z p < r := by
      calc
        dist z p ≤ dist z q + dist q p := dist_triangle _ _ _
        _ < r / 2 + r / 2 := add_lt_add hzq hclose
        _ = r := by ring
    have hzhalf : z ∈ Tiling.negativeHalfPlane p (w - v) := by
      have : z ∈ (s ∩ Metric.ball p r) := ⟨hzs, hzp⟩
      rw [hEq] at this
      exact this.1
    exact ⟨by simpa [hhalves.2] using hzhalf, hzq⟩
  · rintro ⟨hzs, hzq⟩
    have hzhalf : z ∈ Tiling.negativeHalfPlane p (w - v) := by
      simpa [hhalves.2] using hzs
    have hzp : dist z p < r := by
      calc
        dist z p ≤ dist z q + dist q p := dist_triangle _ _ _
        _ < r / 2 + r / 2 := add_lt_add hzq hclose
        _ = r := by ring
    have hsource : z ∈ s := by
      have : z ∈ (s ∩ Metric.ball p r) := by rw [hEq]; exact ⟨hzhalf, hzp⟩
      exact this.1
    exact ⟨hsource, hzq⟩

private theorem positive_negative_edgeGerms_disjoint
    {s : Set Plane} {p d : Plane} (hd : d ≠ 0)
    (hpos : positiveEdgeGerm s d p) (hneg : negativeEdgeGerm s d p) : False := by
  obtain ⟨r, hr, hEq⟩ := hpos
  obtain ⟨s₀, hs₀, hEq₀⟩ := hneg
  let R := min r s₀
  let u := d * Complex.I
  let t := R / (2 * (‖u‖ + 1))
  let z := p + t • u
  have hR : 0 < R := lt_min hr hs₀
  have ht : 0 < t := by dsimp [t]; positivity
  have hnorm : 0 ≤ ‖u‖ := norm_nonneg _
  have hdisp : dist z p < R := by
    have hmul : t * ‖u‖ < R := by
      have hden : 0 < 2 * (‖u‖ + 1) := by positivity
      calc
        t * ‖u‖ = (R * ‖u‖) / (2 * (‖u‖ + 1)) := by
          simp [t]
          ring
        _ < R := (div_lt_iff₀ hden).2 (by nlinarith)
    have hnormz : ‖z - p‖ = t * ‖u‖ := by
      simp [z, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    simpa [dist_eq_norm, hnormz] using hmul
  have hside : 0 < Tiling.signedSide p d z := by
    rw [show z = p + t • (d * Complex.I) by rfl]
    rw [Tiling.signedSide_add_smul_mul_I]
    exact mul_pos ht (Complex.normSq_pos.mpr hd)
  have hballr : z ∈ Metric.ball p r := by
    rw [Metric.mem_ball]
    exact hdisp.trans_le (min_le_left _ _)
  have hballs : z ∈ Metric.ball p s₀ := by
    rw [Metric.mem_ball]
    exact hdisp.trans_le (min_le_right _ _)
  have hzpos : z ∈ Tiling.positiveHalfPlane p d :=
    Tiling.mem_positiveHalfPlane.mpr hside.le
  have hzsource : z ∈ s := by
    have hz := (Set.ext_iff.mp hEq z).mpr ⟨hzpos, hballr⟩
    exact hz.1
  have hzneg : z ∈ Tiling.negativeHalfPlane p d := by
    have hz := (Set.ext_iff.mp hEq₀ z).mp ⟨hzsource, hballs⟩
    exact hz.1
  exact (not_le_of_gt hside) (Tiling.mem_negativeHalfPlane.mp hzneg)

/-- Along a vertex-free intrinsic open edge, the support chooses one fixed
    side of the edge everywhere.  The local orientation alternatives are
    locally stable on the edge and the open segment is preconnected. -/
private theorem intrinsicSegment_orientation_constant
    {s : Set Plane} (hs : Tiling.IsPolygonal s) {v w : Plane}
    (hvw : v ≠ w) (hseg : openSegment ℝ v w ⊆ frontier s)
    (hvertexFree : ∀ p ∈ openSegment ℝ v w, p ∉ Tiling.vertexSet s) :
    (∀ p ∈ openSegment ℝ v w, positiveEdgeGerm s (w - v) p) ∨
      (∀ p ∈ openSegment ℝ v w, negativeEdgeGerm s (w - v) p) := by
  let S : Set Plane := openSegment ℝ v w
  let X := {x : Plane // x ∈ S}
  let U : Set X := {x | positiveEdgeGerm s (w - v) x.1}
  let V : Set X := {x | negativeEdgeGerm s (w - v) x.1}
  have hS : IsPreconnected S := (convex_openSegment v w).isPreconnected
  have hpreX : PreconnectedSpace X := by
    apply (isPreconnected_iff_preconnectedSpace).mp
    simpa [X, S] using hS
  letI := hpreX
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨r, hr, hEq⟩ := hx
    let N : Set X := Subtype.val ⁻¹' Metric.ball x.1 (r / 2)
    have hNopen : IsOpen N := Metric.isOpen_ball.preimage continuous_subtype_val
    have hxN : x ∈ N := by simp [N, hr]
    apply Filter.mem_of_superset (hNopen.mem_nhds hxN)
    intro y hy
    exact positiveEdgeGerm_stable_nearby hvw x.2 y.2 r hr hEq hy
  have hVopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨r, hr, hEq⟩ := hx
    let N : Set X := Subtype.val ⁻¹' Metric.ball x.1 (r / 2)
    have hNopen : IsOpen N := Metric.isOpen_ball.preimage continuous_subtype_val
    have hxN : x ∈ N := by simp [N, hr]
    apply Filter.mem_of_superset (hNopen.mem_nhds hxN)
    intro y hy
    exact negativeEdgeGerm_stable_nearby hvw x.2 y.2 r hr hEq hy
  have hdisj : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact positive_negative_edgeGerms_disjoint
      (sub_ne_zero.mpr hvw.symm) hx hy
  have hcover : (Set.univ : Set X) ⊆ U ∪ V := by
    intro x _
    obtain ⟨r, hr, hside⟩ := intrinsicSegment_fixedOrientation_halfPlane
      hs hvw hseg x.1 x.2 (hvertexFree x.1 x.2)
    rcases hside with hpos | hneg
    · exact Or.inl ⟨r, hr, hpos⟩
    · exact Or.inr ⟨r, hr, hneg⟩
  have hchoice := IsPreconnected.subset_or_subset (s := (Set.univ : Set X))
    hUopen hVopen hdisj hcover (isPreconnected_univ : IsPreconnected (Set.univ : Set X))
  rcases hchoice with hU | hV
  · left
    intro p hp
    have hx : (⟨p, hp⟩ : X) ∈ U := hU (Set.mem_univ _)
    exact hx
  · right
    intro p hp
    have hx : (⟨p, hp⟩ : X) ∈ V := hV (Set.mem_univ _)
    exact hx


/-- Original boundary points never lie in any original full-tile interior.
This is a packing fact, including the same-label frontier case. -/
private theorem sourceBoundaryUnion_disjoint_openCarrier (K : PolygonalRegion)
    (T : Set Plane) (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (s : Plane) (hs : s ∈ T) :
    Disjoint (⋃ t : T, (t : Plane) +ᵥ frontier K.support) (s +ᵥ K.openCarrier) := by
  apply Set.disjoint_left.mpr
  intro x hx hxs
  obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
  by_cases hst : s = (t : Plane)
  · have hxfront := Set.mem_vadd_set_iff_neg_vadd_mem.mp hxt
    have hxopen := Set.mem_vadd_set_iff_neg_vadd_mem.mp hxs
    rw [hst] at hxopen
    exact hxfront.2 hxopen
  · have hxclosed : x ∈ (t : Plane) +ᵥ K.support := by
      apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
      have h := frontier_subset_closure (Set.mem_vadd_set_iff_neg_vadd_mem.mp hxt)
      rwa [K.isPolygonal.isClosed.closure_eq] at h
    exact Set.disjoint_left.mp
      (original_openCarrier_disjoint_otherSupport K T hpack hs t.2 hst) hxs hxclosed

/-- The full-tile noninteriority of an augmented-star projection is transported
from the actual original boundary carrier. Pinched labels may have cones on
both sides; no whole-cone side-containment is asserted. -/
private theorem originalVertexStar_deformedNoninterior_atSourceBoundary
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p s z : Plane, s ∈ T → p ∈ s +ᵥ Tiling.vertexSet K.support →
            dist z 0 < r →
            p + z ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support →
            deformPoint φ p + z ∉ deformPoint φ s +ᵥ Kφ.openCarrier := by
  obtain ⟨F, ε, r, hε, hr, hgerm⟩ := originalVertexCopies_uniformAlignedGerm K P T hP
  refine ⟨F, ε, r, hε, hr, ?_⟩
  intro φ hφ Kφ hKφ p s z hs hps hz hboundary hinterior
  have hsource := (hgerm φ hφ Kφ hKφ p s hs hps z hz).2.mpr hinterior
  exact Set.disjoint_left.mp
    (sourceBoundaryUnion_disjoint_openCarrier K T hpack s hs) hboundary hsource


/-- Consecutive source-chain endpoint gaps concatenate into a finite positive
prototype word. Local finiteness is a source hypothesis; image LF is not used. -/
private theorem scalarChain_consecutiveGapWord
    (S D : Set ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → S ∩ Ioo a b = ∅ → b - a ∈ D) :
    ∀ a ∈ S, ∀ b ∈ S, a < b →
      ∃ G : List ℝ, G ≠ [] ∧ (∀ r ∈ G, 0 < r ∧ r ∈ D) ∧ b - a = G.sum := by
  classical
  have recurse : ∀ n a b, (S ∩ Ioo a b).ncard = n → a ∈ S → b ∈ S → a < b →
      ∃ G : List ℝ, G ≠ [] ∧ (∀ r ∈ G, 0 < r ∧ r ∈ D) ∧ b - a = G.sum := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a b hcount ha hb hab
        let F : Set ℝ := S ∩ Ioo a b
        have hF : F.Finite := (hlocal (Icc a b) (Metric.isBounded_Icc a b)).subset
          (by
            intro x hx
            exact ⟨hx.1, ⟨hx.2.1.le, hx.2.2.le⟩⟩)
        by_cases hempty : F = ∅
        · refine ⟨[b - a], by simp, ?_, by simp⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst r
          exact ⟨sub_pos.mpr hab, hgap a ha b hb hab hempty⟩
        · obtain ⟨c, hcS, hac, hcb⟩ := Set.nonempty_iff_ne_empty.mpr hempty
          let L : Set ℝ := S ∩ Set.Ioo a c
          let R : Set ℝ := S ∩ Set.Ioo c b
          have hLfinite : L.Finite := (hlocal (Set.Icc a c) (Metric.isBounded_Icc a c)).subset
            (by
              intro x hx
              exact ⟨hx.1, ⟨le_of_lt hx.2.1, le_of_lt hx.2.2⟩⟩)
          have hRfinite : R.Finite := (hlocal (Set.Icc c b) (Metric.isBounded_Icc c b)).subset
            (by
              intro x hx
              exact ⟨hx.1, ⟨le_of_lt hx.2.1, le_of_lt hx.2.2⟩⟩)
          have hLsub : L ⊂ F := by
            apply Set.ssubset_iff_subset_ne.mpr
            constructor
            · intro x hx
              exact ⟨hx.1, ⟨hx.2.1, lt_trans hx.2.2 hcb⟩⟩
            · intro heq
              have hcF : c ∈ F := ⟨hcS, ⟨hac, hcb⟩⟩
              have hcL : c ∈ L := heq.symm ▸ hcF
              exact (lt_irrefl c) hcL.2.2
          have hRsub : R ⊂ F := by
            apply Set.ssubset_iff_subset_ne.mpr
            constructor
            · intro x hx
              exact ⟨hx.1, ⟨lt_trans hac hx.2.1, hx.2.2⟩⟩
            · intro heq
              have hcF : c ∈ F := ⟨hcS, ⟨hac, hcb⟩⟩
              have hcR : c ∈ R := heq.symm ▸ hcF
              exact (lt_irrefl c) hcR.2.1
          have hLcard : L.ncard < n := by
            rw [← hcount]
            exact Set.ncard_lt_ncard hLsub hF
          have hRcard : R.ncard < n := by
            rw [← hcount]
            exact Set.ncard_lt_ncard hRsub hF
          obtain ⟨G₁, hG₁ne, hG₁, hsum₁⟩ :=
            ih L.ncard hLcard a c (by rfl) ha hcS hac
          obtain ⟨G₂, hG₂ne, hG₂, hsum₂⟩ :=
            ih R.ncard hRcard c b (by rfl) hcS hb hcb
          refine ⟨G₁ ++ G₂, ?_, ?_, ?_⟩
          · intro hnil
            simp only [List.append_eq_nil_iff] at hnil
            exact hG₁ne hnil.1
          · intro r hr
            rcases List.mem_append.mp hr with hr | hr
            · exact hG₁ r hr
            · exact hG₂ r hr
          · rw [List.sum_append]
            calc
              b - a = (c - a) + (b - c) := by ring
              _ = G₁.sum + G₂.sum := by rw [hsum₁, hsum₂]

  intro a ha b hb hab
  exact recurse (S ∩ Ioo a b).ncard a b rfl ha hb hab

/-- Finite positive prototype-gap controls give global endpoint order and
two-sided metric bounds on the one actual chain. This lemma still requires
the source-chain geometry to establish its consecutive-gap hypothesis. -/
private theorem scalarChain_globalEndpointControl
    (S : Set ℝ) (D : Finset ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → S ∩ Ioo a b = ∅ → b - a ∈ D) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation D ε φ →
        ∀ a ∈ S, ∀ b ∈ S, a < b →
          (b - a) / 2 ≤ (φ b : ℝ) - (φ a : ℝ) ∧
            (φ b : ℝ) - (φ a : ℝ) ≤ 2 * (b - a) := by
  obtain ⟨ε, hε, hcontrol⟩ := finite_positive_deformation_bounds D
  refine ⟨ε, hε, ?_⟩
  intro φ hφ a ha b hb hab
  obtain ⟨G, hGne, hG, hsum⟩ :=
    scalarChain_consecutiveGapWord S D hlocal hgap a ha b hb hab
  have hbnd := list_sum_deformation_bounds φ G
    (fun r hr => hcontrol φ hφ r (hG r hr).2 (hG r hr).1)
  have hmap : (φ (b - a) : ℝ) = (φ b : ℝ) - (φ a : ℝ) := by
    exact_mod_cast φ.map_sub b a
  rw [← hsum] at hbnd
  rwa [hmap] at hbnd


/-- Source genuine translated vertices are locally finite by original packing
and the finite prototype vertex set. No projection LF is inferred globally. -/
private theorem originalVertices_locallyFinite (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) :
    ∀ Q : Set Plane, Bornology.IsBounded Q →
      (Tiling.RationalSlopes.translatedVertices K T ∩ Q).Finite := by
  intro Q hQ
  obtain ⟨B, hB, hQB⟩ := hQ.exists_pos_norm_le
  obtain ⟨R, hR, hKR⟩ := K.isPolygonal.isBounded.exists_pos_norm_le
  let C := T ∩ Metric.closedBall 0 (B + R)
  have hC : C.Finite := (Tiling.Polygonal.packing_centres_locallyFinite hpack).1 _
    Metric.isBounded_closedBall
  have hfinite := K.isPolygonal.vertexSet_finite.add hC
  apply hfinite.subset
  rintro x ⟨hx, hxQ⟩
  obtain ⟨v, hv, t, ht, rfl⟩ := hx
  have hnormv := hKR v (intrinsicVertex_mem_support K hv)
  have hnormx := hQB (v + t) hxQ
  have hnormt : ‖t‖ ≤ B + R := by
    have htri := norm_sub_le (v + t) v
    have heq : (v + t) - v = t := by abel
    rw [heq] at htri
    linarith
  exact Set.mem_add.mpr ⟨v, hv, t,
    ⟨ht, by simpa [Metric.mem_closedBall, dist_eq_norm] using hnormt⟩, rfl⟩

/-- Restrict source vertices to one actual carrier parameter, rather than
projecting all plane vertices and falsely asserting longitudinal LF. -/
private theorem sourceCarrierVertices_scalarLocallyFinite
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (a d : Plane) (hd : d ≠ 0) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q →
      ({r : ℝ | a + r • d ∈ Tiling.RationalSlopes.translatedVertices K T} ∩ Q).Finite := by
  intro Q hQ
  obtain ⟨B, hB, hQB⟩ := hQ.exists_pos_norm_le
  let R := ‖a‖ + B * ‖d‖
  let f : ℝ → Plane := fun r => a + r • d
  have hfinj : Function.Injective f := by
    intro r s hrs
    exact smul_left_injective ℝ hd (add_left_cancel hrs)
  have hfinite := originalVertices_locallyFinite K T hpack (Metric.closedBall 0 R)
    Metric.isBounded_closedBall
  apply (hfinite.preimage hfinj.injOn).subset
  intro r hr
  refine ⟨hr.1, ?_⟩
  change dist (a + r • d) 0 ≤ R
  rw [dist_eq_norm, sub_zero]
  calc
    ‖a + r • d‖ ≤ ‖a‖ + ‖r • d‖ := norm_add_le _ _
    _ = ‖a‖ + ‖r‖ * ‖d‖ := by rw [norm_smul]
    _ ≤ R := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (hQB r hr.2) (norm_nonneg d))


/-- One-chain endpoint properness is a consequence of finite positive-gap
bounds. This says nothing about plane-wide image vertices or centres. -/
private theorem scalarChain_imageEndpoints_locallyFinite
    (S : Set ℝ) (D : Finset ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → S ∩ Ioo a b = ∅ → b - a ∈ D) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation D ε φ →
        ∀ Q : Set ℝ, Bornology.IsBounded Q →
          (((fun r : ℝ => (φ r : ℝ)) '' S) ∩ Q).Finite := by
  obtain ⟨ε, hε, hcontrol⟩ := scalarChain_globalEndpointControl S D hlocal hgap
  refine ⟨ε, hε, ?_⟩
  intro φ hφ Q hQ
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha⟩ := hS
    obtain ⟨B, hB, hQB⟩ := hQ.exists_pos_norm_le
    let R := 2 * (B + |(φ a : ℝ)|)
    have hfinite := hlocal (Metric.closedBall a R) Metric.isBounded_closedBall
    apply (hfinite.image (fun r : ℝ => (φ r : ℝ))).subset
    rintro y ⟨⟨x, hx, rfl⟩, hyQ⟩
    have habs : |x - a| / 2 ≤ |(φ x : ℝ) - (φ a : ℝ)| := by
      rcases lt_trichotomy a x with hax | rfl | hxa
      · have hb := (hcontrol φ hφ a ha x hx hax).1
        have hpos : 0 < (φ x : ℝ) - (φ a : ℝ) := by linarith
        simpa only [abs_of_pos (sub_pos.mpr hax), abs_of_pos hpos] using hb
      · simp
      · have hb := (hcontrol φ hφ x hx a ha hxa).1
        have hpos : 0 < (φ a : ℝ) - (φ x : ℝ) := by linarith
        rw [abs_sub_comm x a, abs_sub_comm (φ x : ℝ) (φ a : ℝ)]
        simpa only [abs_of_pos (sub_pos.mpr hxa), abs_of_pos hpos] using hb
    have htargetBound : |(φ x : ℝ) - (φ a : ℝ)| ≤ B + |(φ a : ℝ)| := by
      have hxbound : |(φ x : ℝ)| ≤ B := by simpa only [Real.norm_eq_abs] using hQB _ hyQ
      exact (abs_sub _ _).trans (add_le_add hxbound le_rfl)
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    change dist x a ≤ R
    rw [Real.dist_eq]
    dsimp [R]
    linarith
  · have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    simp [hempty]



/-- A locally finite real endpoint set has a genuine consecutive pair enclosing
any point between a lower endpoint and a strictly higher endpoint. -/
private theorem scalarSet_consecutive_enclosing (S : Set ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite)
    (lo hi x : ℝ) (hlo : lo ∈ S) (hhi : hi ∈ S) (hlx : lo ≤ x) (hxh : x < hi) :
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ a ≤ x ∧ x ≤ b ∧ S ∩ Ioo a b = ∅ := by
  classical
  have hF := hlocal (Icc lo hi) (Metric.isBounded_Icc lo hi)
  let F := hF.toFinset
  let L := F.filter (fun y => y ≤ x)
  have hloF : lo ∈ F := by
    exact hF.mem_toFinset.mpr ⟨hlo, le_rfl, hlx.trans hxh.le⟩
  have hhiF : hi ∈ F := by
    exact hF.mem_toFinset.mpr ⟨hhi, hlx.trans hxh.le, le_rfl⟩
  have hLne : L.Nonempty := ⟨lo, Finset.mem_filter.mpr ⟨hloF, hlx⟩⟩
  let a := L.max' hLne
  have haL : a ∈ L := Finset.max'_mem _ _
  have haF : a ∈ F := (Finset.mem_filter.mp haL).1
  have hax : a ≤ x := (Finset.mem_filter.mp haL).2
  have haData : a ∈ S ∩ Icc lo hi := hF.mem_toFinset.mp haF
  let R := F.filter (fun y => a < y)
  have hRne : R.Nonempty := ⟨hi, Finset.mem_filter.mpr ⟨hhiF, hax.trans_lt hxh⟩⟩
  let b := R.min' hRne
  have hbR : b ∈ R := Finset.min'_mem _ _
  have hbF : b ∈ F := (Finset.mem_filter.mp hbR).1
  have hab : a < b := (Finset.mem_filter.mp hbR).2
  have hbData : b ∈ S ∩ Icc lo hi := hF.mem_toFinset.mp hbF
  have hxb : x ≤ b := by
    by_contra h
    have hbx : b < x := lt_of_not_ge h
    have hbL : b ∈ L := Finset.mem_filter.mpr ⟨hbF, hbx.le⟩
    exact (not_lt_of_ge (Finset.le_max' L b hbL)) hab
  refine ⟨a, haData.1, b, hbData.1, hab, hax, hxb, ?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hyF : y ∈ F := hF.mem_toFinset.mpr
    ⟨hy.1, haData.2.1.trans hy.2.1.le, hy.2.2.le.trans hbData.2.2⟩
  have hyR : y ∈ R := Finset.mem_filter.mpr ⟨hyF, hy.2.1⟩
  exact (not_lt_of_ge (Finset.min'_le R y hyR)) hy.2.2



/-- The bi-infinite chain endpoint construction survives deformation: every
target scalar is enclosed by the images of consecutive source endpoints.
All image order/LF is derived here from the positive prototype-gap bounds. -/
private theorem scalarChain_deformedConsecutive_cover
    (S : Set ℝ) (D : Finset ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → S ∩ Ioo a b = ∅ → b - a ∈ D)
    (hleft : ∀ x : ℝ, ∃ a ∈ S, a ≤ x)
    (hright : ∀ x : ℝ, ∃ b ∈ S, x < b) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation D ε φ →
        ∀ x : ℝ, ∃ a ∈ S, ∃ b ∈ S, a < b ∧ S ∩ Ioo a b = ∅ ∧
          (φ a : ℝ) ≤ x ∧ x ≤ (φ b : ℝ) := by
  obtain ⟨ε₀, hε₀, hcontrol⟩ := scalarChain_globalEndpointControl S D hlocal hgap
  obtain ⟨ε₁, hε₁, himageLF⟩ := scalarChain_imageEndpoints_locallyFinite S D hlocal hgap
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro φ hφ x
  have hφ₀ : IsFiniteApproximation D ε₀ φ :=
    ⟨hφ.1, fun r hr => (hφ.2 r hr).trans_le (min_le_left _ _)⟩
  have hφ₁ : IsFiniteApproximation D ε₁ φ :=
    ⟨hφ.1, fun r hr => (hφ.2 r hr).trans_le (min_le_right _ _)⟩
  let Y : Set ℝ := (fun r : ℝ => (φ r : ℝ)) '' S
  have hYlocal := himageLF φ hφ₁
  have hmono : ∀ a ∈ S, ∀ b ∈ S, a < b → (φ a : ℝ) < (φ b : ℝ) := by
    intro a ha b hb hab
    have h := (hcontrol φ hφ₀ a ha b hb hab).1
    linarith
  obtain ⟨c, hc, hc0⟩ := hleft 0
  let R := |x - (φ c : ℝ)| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨lo, hlo, hloBound⟩ := hleft (c - 2 * R)
  obtain ⟨hi, hhi, hhiBound⟩ := hright (c + 2 * R)
  have hloc : lo < c := by linarith
  have hchi : c < hi := by linarith
  have hloTarget : (φ lo : ℝ) ≤ x := by
    have h := (hcontrol φ hφ₀ lo hlo c hc hloc).1
    have hxabs := neg_abs_le (x - (φ c : ℝ))
    dsimp [R] at hloBound
    linarith
  have hhiTarget : x < (φ hi : ℝ) := by
    have h := (hcontrol φ hφ₀ c hc hi hhi hchi).1
    have hxabs := le_abs_self (x - (φ c : ℝ))
    dsimp [R] at hhiBound
    linarith
  obtain ⟨a', ha', b', hb', hab', hax, hxb, hconsec⟩ :=
    scalarSet_consecutive_enclosing Y hYlocal (φ lo : ℝ) (φ hi : ℝ) x
      ⟨lo, hlo, rfl⟩ ⟨hi, hhi, rfl⟩ hloTarget hhiTarget
  obtain ⟨a, ha, rfl⟩ := ha'
  obtain ⟨b, hb, rfl⟩ := hb'
  have hab : a < b := by
    by_contra h
    rcases lt_or_eq_of_le (le_of_not_gt h) with hba | hba
    · exact (not_lt_of_gt (hmono b hb a ha hba)) hab'
    · simp only [hba, lt_self_iff_false] at hab'
  refine ⟨a, ha, b, hb, hab, ?_, hax, hxb⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hrY : (φ r : ℝ) ∈ Y ∩ Ioo (φ a : ℝ) (φ b : ℝ) :=
    ⟨⟨r, hr.1, rfl⟩, hmono a ha r hr.1 hr.2.1, hmono r hr.1 b hb hr.2.2⟩
  rw [hconsec] at hrY
  exact hrY


/-- The vertex-star part of an augmented inward collar has a witness measured
against its full-copy frontier. The projection need only lie on the actual
source boundary carrier; a pinched witness need not own any chain edge. -/
private theorem originalVertexStar_boundaryProjection_witness
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p z w : Plane, dist z 0 < r → dist w 0 < r →
            z ∈ originalVertexConeUnion K P T p →
            p + w ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support →
            ∃ s ∈ T, p ∈ s +ᵥ Tiling.vertexSet K.support ∧
              deformPoint φ p + z ∈ deformPoint φ s +ᵥ Kφ.support ∧
              Metric.infDist (deformPoint φ p + z)
                (deformPoint φ s +ᵥ frontier Kφ.support) ≤ dist z w := by
  obtain ⟨F₀, ε₀, r₀, hε₀, hr₀, hcone⟩ := originalVertexConeUnion_deformedGerm K P T
  obtain ⟨F₁, ε₁, r₁, hε₁, hr₁, hboundary⟩ :=
    originalVertexStar_deformedNoninterior_atSourceBoundary K P T hP hpack
  refine ⟨F₀ ∪ F₁, min ε₀ ε₁, min r₀ r₁, lt_min hε₀ hε₁, lt_min hr₀ hr₁, ?_⟩
  intro φ hφ Kφ hKφ p z w hz hw hzCone hwBoundary
  have hφ₀ := finiteApproximation_strengthen F₀ (F₀ ∪ F₁) ε₀ (min ε₀ ε₁) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφ₁ := finiteApproximation_strengthen F₁ (F₀ ∪ F₁) ε₁ (min ε₀ ε₁) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  have hz₀ := hz.trans_le (min_le_left _ _)
  have hw₁ := hw.trans_le (min_le_right _ _)
  obtain ⟨s, hsz⟩ := Set.mem_iUnion.mp ((hcone φ hφ₀ Kφ hKφ p z hz₀).mpr hzCone)
  have hnonint : deformPoint φ p + w ∉ interior (deformPoint φ (s.1 : Plane) +ᵥ Kφ.support) := by
    rw [interior_vadd]
    exact hboundary φ hφ₁ Kφ hKφ p (s.1 : Plane) w s.1.2 s.2 hw₁ hwBoundary
  have hdist := compact_frontier_infDist_le_of_notInterior
    (deformPoint φ (s.1 : Plane) +ᵥ Kφ.support) (Kφ.isPolygonal.isCompact.vadd _)
    (deformPoint φ p + z) (deformPoint φ p + w) hsz hnonint
  have hfrontier : frontier (deformPoint φ (s.1 : Plane) +ᵥ Kφ.support) =
      deformPoint φ (s.1 : Plane) +ᵥ frontier Kφ.support := by
    rw [frontier, closure_vadd, interior_vadd, ← Set.vadd_set_sdiff]
    rfl
  have hdistance : dist (deformPoint φ p + z) (deformPoint φ p + w) = dist z w := by
    simp [dist_eq_norm]
  rw [hfrontier, hdistance] at hdist
  exact ⟨s.1, s.1.2, s.2, hsz, hdist⟩

/-- Two supports with the same nontrivial inward linear germ have an actual
common interior point.  This is used only for original packing labels. -/
private theorem sameLinearGerms_interiors_overlap
    (A B : Set Plane) (p : Plane) (f : Plane →L[ℝ] ℝ)
    (u : Plane) (hu : f u = 1) (rA rB : ℝ) (hrA : 0 < rA) (hrB : 0 < rB)
    (hA : ∀ q, dist q p < rA → (q ∈ A ↔ 0 ≤ f (q - p)))
    (hB : ∀ q, dist q p < rB → (q ∈ B ↔ 0 ≤ f (q - p))) :
    (interior A ∩ interior B).Nonempty := by
  obtain ⟨c, hc, hsmall⟩ := exists_positiveScaling_intoBall u (min rA rB)
    (lt_min hrA hrB)
  let q : Plane := p + c • u
  have hdist : dist q p = dist (c • u) 0 := by simp [q, dist_eq_norm]
  have hpositive : 0 < f (q - p) := by
    simp only [q, add_sub_cancel_left, map_smul, hu, smul_eq_mul, mul_one]
    exact hc
  exact ⟨q, positiveLinearGerm_mem_interior A p f rA hA q
    (hdist.trans_lt (hsmall.trans_le (min_le_left _ _))) hpositive,
    positiveLinearGerm_mem_interior B p f rB hB q
      (hdist.trans_lt (hsmall.trans_le (min_le_right _ _))) hpositive⟩

private theorem originalSameLinearGerm_label_unique (K : PolygonalRegion)
    (T : Set Plane) (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (s t p : Plane) (hs : s ∈ T) (ht : t ∈ T)
    (f : Plane →L[ℝ] ℝ) (u : Plane) (hu : f u = 1)
    (rS rT : ℝ) (hrS : 0 < rS) (hrT : 0 < rT)
    (hS : ∀ q, dist q p < rS → (q ∈ s +ᵥ K.support ↔ 0 ≤ f (q - p)))
    (hT : ∀ q, dist q p < rT → (q ∈ t +ᵥ K.support ↔ 0 ≤ f (q - p))) :
    s = t := by
  by_contra hst
  obtain ⟨q, hqs, hqt⟩ := sameLinearGerms_interiors_overlap
    (s +ᵥ K.support) (t +ᵥ K.support) p f u hu rS rT hrS hrT hS hT
  rw [interior_vadd] at hqs hqt
  exact Set.disjoint_left.mp
    ((Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K T).mp hpack hs ht hst)
    hqs hqt

private theorem originalSamePositiveEdgeGerm_label_unique (K : PolygonalRegion)
    (T : Set Plane) (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (s t p d : Plane) (hs : s ∈ T) (ht : t ∈ T) (hd : d ≠ 0)
    (hS : positiveEdgeGerm (s +ᵥ K.support) d p)
    (hT : positiveEdgeGerm (t +ᵥ K.support) d p) : s = t := by
  obtain ⟨rS, hrS, hS⟩ := hS
  obtain ⟨rT, hrT, hT⟩ := hT
  obtain ⟨u, hu⟩ := exists_planarCrossCLM_normalizer hd
  have hside (q : Plane) : Tiling.signedSide p d q =
      Tiling.planarCrossCLM d (q - p) := by
    rw [Tiling.planarCrossCLM_apply]
    simp [Tiling.signedSide, Tiling.planarCross, Complex.sub_re, Complex.sub_im]
    ring
  apply originalSameLinearGerm_label_unique K T hpack s t p hs ht
    (Tiling.planarCrossCLM d) u hu rS rT hrS hrT
  · intro q hq
    have hball : q ∈ Metric.ball p rS := hq
    have hmem := Set.ext_iff.mp hS q
    simpa only [Set.mem_inter_iff, hball, and_true, Tiling.mem_positiveHalfPlane,
      hside] using hmem
  · intro q hq
    have hball : q ∈ Metric.ball p rT := hq
    have hmem := Set.ext_iff.mp hT q
    simpa only [Set.mem_inter_iff, hball, and_true, Tiling.mem_positiveHalfPlane,
      hside] using hmem

private theorem originalSameNegativeEdgeGerm_label_unique (K : PolygonalRegion)
    (T : Set Plane) (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (s t p d : Plane) (hs : s ∈ T) (ht : t ∈ T) (hd : d ≠ 0)
    (hS : negativeEdgeGerm (s +ᵥ K.support) d p)
    (hT : negativeEdgeGerm (t +ᵥ K.support) d p) : s = t := by
  have hhalf : Tiling.negativeHalfPlane p d = Tiling.positiveHalfPlane p (-d) := by
    ext q
    simp only [Tiling.positiveHalfPlane, Tiling.negativeHalfPlane, Set.mem_setOf_eq]
    simp [Tiling.planarCross]
    constructor <;> intro h <;> linarith
  apply originalSamePositiveEdgeGerm_label_unique K T hpack s t p (-d) hs ht
    (neg_ne_zero.mpr hd)
  · obtain ⟨r, hr, hlocal⟩ := hS
    exact ⟨r, hr, by simpa only [hhalf] using hlocal⟩
  · obtain ⟨r, hr, hlocal⟩ := hT
    exact ⟨r, hr, by simpa only [hhalf] using hlocal⟩

/-- Constructed prototype primitive edges, with actual constant inward side
and finite positive deformation-length controls on that same edge family. -/
private theorem rationalIntrinsicPrimitiveEdges (K : PolygonalRegion)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K) :
    ∃ E : Finset (Plane × Plane),
      (∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
        e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
        (∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet K.support) ∧
        Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1) ∧
        ((∀ p ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) p) ∨
          (∀ p ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) p))) ∧
      frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2 ∧
      ∃ F : Finset ℝ, ∃ ε l : ℝ, 0 < ε ∧ 0 < l ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ e ∈ E, ∃ c : ℝ, 1 / 2 ≤ c ∧ c ≤ 2 ∧
            deformPoint φ e.2 - deformPoint φ e.1 = c • (e.2 - e.1) ∧
            l ≤ dist (deformPoint φ e.1) (deformPoint φ e.2) := by
  obtain ⟨E, hE, hcover⟩ := exists_finite_vertexFree_intrinsicBoundarySegments K.isPolygonal
  have hdir : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1) := by
    intro e he
    exact frontierSegment_rationalDirection K hrat e.1 e.2 (hE e he).1 (hE e he).2.2.2.1
  refine ⟨E, ?_, hcover, finiteRationalEdges_positiveHomotheties E hdir⟩
  intro e he
  obtain ⟨hne, hv, hw, hseg, hfree⟩ := hE e he
  exact ⟨hne, hv, hw, hseg, hfree, hdir e he,
    intrinsicSegment_orientation_constant K.isPolygonal hne
      (fun _ hp => hseg (openSegment_subset_segment ℝ _ _ hp)) hfree⟩

private theorem originalVertexCopies_uniformConeGerm (K : PolygonalRegion)
    (P : PolyhedralCode) (T : Set Plane) (hP : polyhedralSupport P = K.support) :
    ∃ r : ℝ, 0 < r ∧ ∀ p s : Plane, s ∈ T →
      p ∈ s +ᵥ Tiling.vertexSet K.support → ∀ z : Plane, dist z 0 < r →
        (p + z ∈ s +ᵥ K.support ↔ z ∈ polyhedralVertexCone P (p - s)) := by
  classical
  let W := K.isPolygonal.vertexSet_finite.toFinset
  obtain ⟨r, hr, hcone⟩ := polyhedralSupport_uniformVertexCones P W
  refine ⟨r, hr, ?_⟩
  intro p s hs hps z hz
  have hv : p - s ∈ W := by
    apply K.isPolygonal.vertexSet_finite.mem_toFinset.mpr
    have h := Set.mem_vadd_set_iff_neg_vadd_mem.mp hps
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using h
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  have heq : -s +ᵥ (p + z) = (p - s) + z := by
    change -s + (p + z) = _
    abel
  rw [heq]
  simpa only [hP] using hcone _ hv z hz

/-- An intrinsic vertex on a full proper link has an actual intrinsic label
owning the requested directed frontier ray.  The half-star case uses both
directions of the full link; no individual cone is assumed one-sided. -/
private theorem sourceRay_boundaryUnion_noInterior (K : PolygonalRegion)
    (T : Set Plane) (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    {s : Plane} (hs : s ∈ T) {x : Plane}
    (hx : x ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) :
    x ∉ s +ᵥ K.openCarrier :=
  fun h => Set.disjoint_left.mp
    (sourceBoundaryUnion_disjoint_openCarrier K T hpack s hs) hx h

private theorem sourceNonvertexCopy_localHalfPlane (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    {s p : Plane}
    (hs : s ∈ T) (hps : p ∈ s +ᵥ K.support)
    (hpnot : p ∉ s +ᵥ Tiling.vertexSet K.support)
    (hpboundary : p ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) :
    ∃ u : Plane, u ≠ 0 ∧ ∃ r > 0,
      ((s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.positiveHalfPlane p u ∩ Metric.ball p r ∨
       (s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.negativeHalfPlane p u ∩ Metric.ball p r) := by
  have hpnotint : p ∉ s +ᵥ K.openCarrier :=
    sourceRay_boundaryUnion_noInterior K T hpack hs hpboundary
  have hpfrontier : p ∈ frontier (s +ᵥ K.support) := by
    rw [(K.isPolygonal.isClosed.vadd s).frontier_eq, interior_vadd]
    exact ⟨hps, hpnotint⟩
  have hpolygonal : Tiling.IsPolygonal (s +ᵥ K.support) := K.isPolygonal.vadd s
  have hpnot' : p ∉ Tiling.vertexSet (s +ᵥ K.support) := by
    simpa only [Tiling.vertexSet_vadd] using hpnot
  obtain ⟨L, hpL, hdim, hlocal⟩ :=
    hpolygonal.boundaryLocallyStraightAt_of_not_mem_vertexSet hpfrontier hpnot'
  apply Tiling.exists_local_eq_closedHalfPlane_of_affineSubspace _ hpL hdim hlocal
  rw [interior_vadd, closure_vadd, K.isPolygonal.closure_interior]

private theorem sourceRay_localHalfPlane (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (δ : Submodule ℝ Plane) (a : Plane)
    (hproper : Tiling.RationalSlopes.IsProperLink K δ T a)
    {s p : Plane} (hpa : p ∈ a +ᵥ (δ : Set Plane))
    (hs : s ∈ T) (hps : p ∈ s +ᵥ K.support)
    (hpnot : p ∉ s +ᵥ Tiling.vertexSet K.support) :
    ∃ u : Plane, u ≠ 0 ∧ ∃ r > 0,
      ((s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.positiveHalfPlane p u ∩ Metric.ball p r ∨
       (s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.negativeHalfPlane p u ∩ Metric.ball p r)  := by
  exact sourceNonvertexCopy_localHalfPlane K T hpack hs hps hpnot (hproper hpa)


private theorem sourceRay_properLine_scale (δ : Submodule ℝ Plane) (a p d : Plane)
    (hpa : p ∈ a +ᵥ (δ : Set Plane)) (hd : d ∈ δ) (c : ℝ) :
    p + c • d ∈ a +ᵥ (δ : Set Plane) := by
  obtain ⟨w, hw, hpw⟩ := Set.mem_vadd_set.mp hpa
  refine Set.mem_vadd_set.mpr ⟨w + c • d, δ.add_mem hw (δ.smul_mem c hd), ?_⟩
  change a + (w + c • d) = p + c • d
  rw [← hpw]
  simp only [vadd_eq_add]
  abel

private theorem sourceBoundary_localLinearGerm_annihilates_direction
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (s p d : Plane) (hs : s ∈ T) (f : Plane →L[ℝ] ℝ) (r : ℝ) (hr : 0 < r)
    (hgerm : ∀ q, dist q p < r → (q ∈ s +ᵥ K.support ↔ 0 ≤ f (q - p)))
    (hline : ∃ R > 0, ∀ c : ℝ, |c| < R →
      p + c • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) : f d = 0 := by
  obtain ⟨R, hR, hline⟩ := hline
  have nonpos (z : Plane)
      (hboundary : ∀ c : ℝ, |c| < R →
        p + c • z ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) : f z ≤ 0 := by
    by_contra hnot
    have hfz : 0 < f z := lt_of_not_ge hnot
    have hden : 0 < ‖z‖ + 1 := by positivity
    obtain ⟨c, hc, hcbound⟩ := exists_between (lt_min hR (div_pos hr hden))
    have hcR : |c| < R := by
      rw [abs_of_pos hc]
      exact hcbound.trans_le (min_le_left _ _)
    have hcr : c * (‖z‖ + 1) < r :=
      (lt_div_iff₀ hden).mp (hcbound.trans_le (min_le_right _ _))
    have hdist : dist (p + c • z) p < r := by
      rw [dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      nlinarith [norm_nonneg z]
    have hpositive : 0 < f ((p + c • z) - p) := by
      simp only [add_sub_cancel_left, map_smul, smul_eq_mul]
      exact mul_pos hc hfz
    have hinterior := positiveLinearGerm_mem_interior (s +ᵥ K.support) p f r hgerm
      (p + c • z) hdist hpositive
    rw [interior_vadd] at hinterior
    exact sourceRay_boundaryUnion_noInterior K T hpack hs (hboundary c hcR) hinterior
  have hpos := nonpos d hline
  have hneg := nonpos (-d) (by
    intro c hc
    have h := hline (-c) (by simpa only [abs_neg] using hc)
    simpa only [neg_smul, smul_neg] using h)
  rw [map_neg] at hneg
  linarith

private theorem sourceRay_localHalfPlane_normal_annihilates_boundaryInterval
    (K : PolygonalRegion) (T : Set Plane) (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (p d : Plane)
    {s : Plane} (hs : s ∈ T)
    (hline : ∃ R > 0, ∀ c : ℝ, |c| < R →
      p + c • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
    (hloc : ∃ u : Plane, u ≠ 0 ∧ ∃ r > 0,
      ((s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.positiveHalfPlane p u ∩ Metric.ball p r ∨
       (s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.negativeHalfPlane p u ∩ Metric.ball p r)) :
    ∃ u : Plane, u ≠ 0 ∧ ∃ r > 0,
      ((s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.positiveHalfPlane p u ∩ Metric.ball p r ∨
       (s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.negativeHalfPlane p u ∩ Metric.ball p r) ∧
      Tiling.planarCross u d = 0 := by
  obtain ⟨u, hu, r, hr, hcase⟩ := hloc
  have hside (q : Plane) : Tiling.signedSide p u q =
      Tiling.planarCrossCLM u (q - p) := by
    rw [Tiling.planarCrossCLM_apply]
    simp [Tiling.signedSide, Tiling.planarCross, Complex.sub_re, Complex.sub_im]
    ring
  let f : Plane →L[ℝ] ℝ :=
    if hpos : (s +ᵥ K.support) ∩ Metric.ball p r =
        Tiling.positiveHalfPlane p u ∩ Metric.ball p r
    then Tiling.planarCrossCLM u else -Tiling.planarCrossCLM u
  have hfgerm : ∀ q, dist q p < r →
      (q ∈ s +ᵥ K.support ↔ 0 ≤ f (q - p)) := by
    intro q hqp
    have hball : q ∈ Metric.ball p r := by
      simpa [Metric.mem_ball, dist_comm] using hqp
    dsimp [f]
    split_ifs with hpos
    · have hmem : q ∈ s +ᵥ K.support ↔ q ∈ Tiling.positiveHalfPlane p u := by
        have hEq := congrArg (fun S : Set Plane => q ∈ S) hpos
        simpa [Set.mem_inter_iff, hball] using hEq
      rw [hmem, Tiling.mem_positiveHalfPlane, hside]
    · have hneg : (s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.negativeHalfPlane p u ∩ Metric.ball p r := by
        rcases hcase with hcasepos | hcaseneg
        · exact False.elim (hpos hcasepos)
        · exact hcaseneg
      have hmem : q ∈ s +ᵥ K.support ↔ q ∈ Tiling.negativeHalfPlane p u := by
        have hEq := congrArg (fun S : Set Plane => q ∈ S) hneg
        simpa [Set.mem_inter_iff, hball] using hEq
      rw [hmem, Tiling.mem_negativeHalfPlane, hside]
      simp
  have hfd : f d = 0 := sourceBoundary_localLinearGerm_annihilates_direction
    K T hpack s p d hs f r hr hfgerm hline
  refine ⟨u, hu, r, hr, hcase, ?_⟩
  have hfd' : f d = 0 := hfd
  dsimp [f] at hfd'
  split_ifs at hfd' with hpos
  · simpa only [Tiling.planarCrossCLM_apply] using hfd'
  · have hneg : -(Tiling.planarCross u d) = 0 := by
      simpa only [neg_apply, Tiling.planarCrossCLM_apply] using hfd'
    exact neg_eq_zero.mp hneg

private theorem sourceRay_localHalfPlane_normal_annihilates_link
    (K : PolygonalRegion) (T : Set Plane) (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (δ : Submodule ℝ Plane) (a p d : Plane)
    (hproper : Tiling.RationalSlopes.IsProperLink K δ T a)
    (hpa : p ∈ a +ᵥ (δ : Set Plane)) (hd : d ∈ δ)
    {s : Plane} (hs : s ∈ T)
    (hloc : ∃ u : Plane, u ≠ 0 ∧ ∃ r > 0,
      ((s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.positiveHalfPlane p u ∩ Metric.ball p r ∨
       (s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.negativeHalfPlane p u ∩ Metric.ball p r)) :
    ∃ u : Plane, u ≠ 0 ∧ ∃ r > 0,
      ((s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.positiveHalfPlane p u ∩ Metric.ball p r ∨
       (s +ᵥ K.support) ∩ Metric.ball p r =
          Tiling.negativeHalfPlane p u ∩ Metric.ball p r) ∧
      Tiling.planarCross u d = 0 := by
  apply sourceRay_localHalfPlane_normal_annihilates_boundaryInterval K T hpack p d hs
  · refine ⟨1, by norm_num, ?_⟩
    intro c hc
    exact hproper (sourceRay_properLine_scale δ a p d hpa hd c)
  · exact hloc

private theorem sourceRay_alignedHalfPlane_orientedGerm
    {s : Set Plane} {p d u : Plane} (hu : u ≠ 0) (hd : d ≠ 0)
    (hloc : ∃ r > 0,
      (s ∩ Metric.ball p r = Tiling.positiveHalfPlane p u ∩ Metric.ball p r ∨
       s ∩ Metric.ball p r = Tiling.negativeHalfPlane p u ∩ Metric.ball p r))
    (hcross : Tiling.planarCross u d = 0) :
    positiveEdgeGerm s d p ∨ negativeEdgeGerm s d p := by
  have hcross' : Tiling.planarCross d u = 0 := by
    have hanti : Tiling.planarCross d u = -Tiling.planarCross u d := by
      simp [Tiling.planarCross]
      ring
    rw [hanti, hcross]
    simp
  have hline : u ∈ Tiling.affineLine 0 d := by
    rw [Tiling.mem_affineLine]
    change Tiling.planarCross d u - Tiling.planarCross d 0 = 0
    simpa [Tiling.planarCross] using hcross'
  obtain ⟨c, hcu⟩ := (Tiling.mem_affineLine_iff_exists_smul hd).mp hline
  have huEq : u = c • d := by simpa using hcu
  have hcne : c ≠ 0 := by
    intro hc
    have hu0 : u = 0 := by rw [huEq, hc]; simp
    exact hu hu0
  have hside (x : Plane) : Tiling.signedSide p u x =
      c * Tiling.signedSide p d x := by
    simp [Tiling.signedSide, Tiling.planarCross, huEq]
    ring
  obtain ⟨r, hr, hcase⟩ := hloc
  rcases hcase with hpos | hneg
  · rcases lt_or_gt_of_ne hcne with hcn | hcp
    · right
      refine ⟨r, hr, ?_⟩
      calc
        s ∩ Metric.ball p r = Tiling.positiveHalfPlane p u ∩ Metric.ball p r := hpos
        _ = Tiling.negativeHalfPlane p d ∩ Metric.ball p r := by
          ext x
          simp only [Set.mem_inter_iff, Tiling.mem_positiveHalfPlane,
            Tiling.mem_negativeHalfPlane]
          rw [hside]
          constructor <;> intro hx <;> constructor
          · nlinarith
          · exact hx.2
          · nlinarith
          · exact hx.2
    · left
      refine ⟨r, hr, ?_⟩
      calc
        s ∩ Metric.ball p r = Tiling.positiveHalfPlane p u ∩ Metric.ball p r := hpos
        _ = Tiling.positiveHalfPlane p d ∩ Metric.ball p r := by
          ext x
          simp only [Set.mem_inter_iff, Tiling.mem_positiveHalfPlane]
          rw [hside]
          constructor <;> intro hx <;> constructor
          · nlinarith
          · exact hx.2
          · nlinarith
          · exact hx.2
  · rcases lt_or_gt_of_ne hcne with hcn | hcp
    · left
      refine ⟨r, hr, ?_⟩
      calc
        s ∩ Metric.ball p r = Tiling.negativeHalfPlane p u ∩ Metric.ball p r := hneg
        _ = Tiling.positiveHalfPlane p d ∩ Metric.ball p r := by
          ext x
          simp only [Set.mem_inter_iff, Tiling.mem_negativeHalfPlane,
            Tiling.mem_positiveHalfPlane]
          rw [hside]
          constructor <;> intro hx <;> constructor
          · nlinarith
          · exact hx.2
          · nlinarith
          · exact hx.2
    · right
      refine ⟨r, hr, ?_⟩
      calc
        s ∩ Metric.ball p r = Tiling.negativeHalfPlane p u ∩ Metric.ball p r := hneg
        _ = Tiling.negativeHalfPlane p d ∩ Metric.ball p r := by
          ext x
          simp only [Set.mem_inter_iff, Tiling.mem_negativeHalfPlane]
          rw [hside]
          constructor <;> intro hx <;> constructor
          · nlinarith
          · exact hx.2
          · nlinarith
          · exact hx.2

/-- At a source point of a full proper link which is not an original vertex,
the two transverse open sides are owned by distinct original labels, with
genuine opposite local half-plane germs. -/
private theorem sourceNonvertexBoundaryInterval_oppositeLabelGerms
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (p d : Plane) (hdne : d ≠ 0)
    (hline : ∃ R > 0, ∀ c : ℝ, |c| < R →
      p + c • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
    (hpnot : p ∉ Tiling.RationalSlopes.translatedVertices K T) :
    ∃ s ∈ T, ∃ t ∈ T, s ≠ t ∧
      positiveEdgeGerm (s +ᵥ K.support) d p ∧
      negativeEdgeGerm (t +ᵥ K.support) d p := by
  classical
  have hpboundary : p ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support := by
    obtain ⟨R, hR, hlineR⟩ := hline
    simpa only [zero_smul, add_zero] using hlineR 0 (by simpa using hR)
  let J := {s : T // p ∈ (s : Plane) +ᵥ K.support}
  have hIncident : {s : T | p ∈ (s : Plane) +ᵥ K.support}.Finite :=
    (originalIndexedCopies_locallyFinite K T htile.2.1).point_finite p
  letI : Finite J := hIncident.to_subtype
  have hJfinite : (Set.univ : Set J).Finite := Set.toFinite _
  have hlocal (j : J) :
      ∃ u : Plane, u ≠ 0 ∧ ∃ r > 0,
        (((j.1 : Plane) +ᵥ K.support) ∩ Metric.ball p r =
            Tiling.positiveHalfPlane p u ∩ Metric.ball p r ∨
         ((j.1 : Plane) +ᵥ K.support) ∩ Metric.ball p r =
            Tiling.negativeHalfPlane p u ∩ Metric.ball p r) := by
    have hpnotLabel : p ∉ (j.1 : Plane) +ᵥ Tiling.vertexSet K.support := by
      intro hvertex
      apply hpnot
      change p ∈ Tiling.vertexSet K.support + T
      apply Set.mem_add.mpr
      refine ⟨-(j.1 : Plane) + p, ?_, (j.1 : Plane), j.1.property, ?_⟩
      · exact Set.mem_vadd_set_iff_neg_vadd_mem.mp hvertex
      · change -(j.1 : Plane) + p + (j.1 : Plane) = p
        abel
    exact sourceNonvertexCopy_localHalfPlane K T htile.2.1
      j.1.property j.2 hpnotLabel hpboundary
  have hnormal (j : J) :
      ∃ u : Plane, u ≠ 0 ∧ ∃ r > 0,
        (((j.1 : Plane) +ᵥ K.support) ∩ Metric.ball p r =
            Tiling.positiveHalfPlane p u ∩ Metric.ball p r ∨
         ((j.1 : Plane) +ᵥ K.support) ∩ Metric.ball p r =
            Tiling.negativeHalfPlane p u ∩ Metric.ball p r) ∧
          Tiling.planarCross u d = 0 := by
    exact sourceRay_localHalfPlane_normal_annihilates_boundaryInterval K T htile.2.1
      p d j.1.property hline (hlocal j)
  have horiented (j : J) :
      ∃ r > 0,
        (((j.1 : Plane) +ᵥ K.support) ∩ Metric.ball p r =
            Tiling.positiveHalfPlane p d ∩ Metric.ball p r ∨
         ((j.1 : Plane) +ᵥ K.support) ∩ Metric.ball p r =
            Tiling.negativeHalfPlane p d ∩ Metric.ball p r) := by
    obtain ⟨u, hu, r₀, hr₀, hcase, hcross⟩ := hnormal j
    rcases sourceRay_alignedHalfPlane_orientedGerm hu hdne ⟨r₀, hr₀, hcase⟩ hcross with hpos | hneg
    · obtain ⟨r, hr, heq⟩ := hpos
      exact ⟨r, hr, Or.inl heq⟩
    · obtain ⟨r, hr, heq⟩ := hneg
      exact ⟨r, hr, Or.inr heq⟩
  choose ρ hρ hside using horiented
  have hevent : ∀ᶠ q in 𝓝 p, ∀ j ∈ (Set.univ : Set J), dist q p < ρ j := by
    apply hJfinite.eventually_all.mpr
    intro j hj
    exact Metric.ball_mem_nhds p (hρ j)
  obtain ⟨rJ, hrJ, hballEvent⟩ := Metric.eventually_nhds_iff.mp hevent
  have hJball : ∀ q, dist q p < rJ → ∀ j : J, dist q p < ρ j := by
    intro q hq j
    exact hballEvent hq j (Set.mem_univ _)
  obtain ⟨rC, hrC, hcover⟩ := originalClosedStar_localCover K T htile p
  let r : ℝ := min rJ rC
  have hr : 0 < r := lt_min hrJ hrC
  let c : ℝ := r / (2 * (‖d * Complex.I‖ + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hden : 0 < 2 * (‖d * Complex.I‖ + 1) := by positivity
  have hprod : c * ‖d * Complex.I‖ < r := by
    dsimp [c]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith [norm_nonneg (d * Complex.I), hr]
  let qpos : Plane := p + c • (d * Complex.I)
  let qneg : Plane := p + c • (-(d * Complex.I))
  have hdistPos : dist qpos p < r := by
    rw [show qpos = p + c • (d * Complex.I) by rfl, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    simpa only [mul_comm] using hprod
  have hdistNeg : dist qneg p < r := by
    rw [show qneg = p + c • (-(d * Complex.I)) by rfl, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      norm_neg]
    simpa only [mul_comm] using hprod
  have hdistPosJ : dist qpos p < rJ := hdistPos.trans_le (min_le_left _ _)
  have hdistNegJ : dist qneg p < rJ := hdistNeg.trans_le (min_le_left _ _)
  have hdistPosC : dist qpos p < rC := hdistPos.trans_le (min_le_right _ _)
  have hdistNegC : dist qneg p < rC := hdistNeg.trans_le (min_le_right _ _)
  have hballPosJ : ∀ j : J, dist qpos p < ρ j := by
    exact hJball qpos hdistPosJ
  have hballNegJ : ∀ j : J, dist qneg p < ρ j := by
    exact hJball qneg hdistNegJ
  obtain ⟨s, hs, hps, hqpos⟩ := hcover qpos
    (Metric.mem_ball.mpr (by simpa [dist_comm] using hdistPosC))
  obtain ⟨t, ht, hpt, hqneg⟩ := hcover qneg
    (Metric.mem_ball.mpr (by simpa [dist_comm] using hdistNegC))
  let js : J := ⟨⟨s, hs⟩, hps⟩
  let jt : J := ⟨⟨t, ht⟩, hpt⟩
  have hqposJ : dist qpos p < ρ js := hballPosJ js
  have hqnegJ : dist qneg p < ρ jt := hballNegJ jt
  have hsidePos : 0 < Tiling.signedSide p d qpos := by
    rw [show qpos = p + c • (d * Complex.I) by rfl,
      Tiling.signedSide_add_smul_mul_I]
    exact mul_pos hc (Complex.normSq_pos.mpr hdne)
  have hsideNeg : Tiling.signedSide p d qneg < 0 := by
    have hqnegEq : qneg = p - c • (d * Complex.I) := by
      dsimp [qneg]
      ring
    rw [hqnegEq, Tiling.signedSide_sub_smul_mul_I]
    exact neg_neg_of_pos (mul_pos hc (Complex.normSq_pos.mpr hdne))
  have hposGerm : positiveEdgeGerm (s +ᵥ K.support) d p := by
    rcases hside js with hpos | hneg
    · exact ⟨ρ js, hρ js, hpos⟩
    · have hqball : qpos ∈ Metric.ball p (ρ js) :=
        Metric.mem_ball.mpr (by simpa [dist_comm] using hqposJ)
      have hmem : qpos ∈ Tiling.negativeHalfPlane p d := by
        have hEq := congrArg (fun A : Set Plane => qpos ∈ A) hneg
        exact (hEq.mp ⟨hqpos, hqball⟩).1
      exact False.elim ((not_lt_of_ge (Tiling.mem_negativeHalfPlane.mp hmem)) hsidePos)
  have hnegGerm : negativeEdgeGerm (t +ᵥ K.support) d p := by
    rcases hside jt with hpos | hneg
    · have hqball : qneg ∈ Metric.ball p (ρ jt) :=
        Metric.mem_ball.mpr (by simpa [dist_comm] using hqnegJ)
      have hmem : qneg ∈ Tiling.positiveHalfPlane p d := by
        have hEq := congrArg (fun A : Set Plane => qneg ∈ A) hpos
        exact (hEq.mp ⟨hqneg, hqball⟩).1
      exact False.elim ((not_lt_of_ge (Tiling.mem_positiveHalfPlane.mp hmem)) hsideNeg)
    · exact ⟨ρ jt, hρ jt, hneg⟩
  have hst : s ≠ t := by
    intro heq
    have hjsjt : js = jt := by
      apply Subtype.ext
      apply Subtype.ext
      exact heq
    have hqnegS : qneg ∈ s +ᵥ K.support := by simpa [heq] using hqneg
    have hsideS := hside js
    rcases hsideS with hpos | hneg
    · have hqball : qneg ∈ Metric.ball p (ρ js) :=
        Metric.mem_ball.mpr (by simpa [hjsjt, dist_comm] using hqnegJ)
      have hmem : qneg ∈ Tiling.positiveHalfPlane p d := by
        have hEq := congrArg (fun A : Set Plane => qneg ∈ A) hpos
        exact (hEq.mp ⟨hqnegS, hqball⟩).1
      exact False.elim ((not_lt_of_ge (Tiling.mem_positiveHalfPlane.mp hmem)) hsideNeg)
    · have hqball : qpos ∈ Metric.ball p (ρ js) :=
        Metric.mem_ball.mpr (by simpa [dist_comm] using hqposJ)
      have hmem : qpos ∈ Tiling.negativeHalfPlane p d := by
        have hEq := congrArg (fun A : Set Plane => qpos ∈ A) hneg
        exact (hEq.mp ⟨hqpos, hqball⟩).1
      exact False.elim ((not_lt_of_ge (Tiling.mem_negativeHalfPlane.mp hmem)) hsidePos)
  exact ⟨s, hs, t, ht, hst, hposGerm, hnegGerm⟩

private theorem sourceNonvertexLink_oppositeLabelGerms
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (δ : Submodule ℝ Plane) (a p d : Plane)
    (hproper : Tiling.RationalSlopes.IsProperLink K δ T a)
    (hpa : p ∈ a +ᵥ (δ : Set Plane)) (hd : d ∈ δ) (hdne : d ≠ 0)
    (hpnot : p ∉ Tiling.RationalSlopes.translatedVertices K T) :
    ∃ s ∈ T, ∃ t ∈ T, s ≠ t ∧
      positiveEdgeGerm (s +ᵥ K.support) d p ∧
      negativeEdgeGerm (t +ᵥ K.support) d p := by
  apply sourceNonvertexBoundaryInterval_oppositeLabelGerms K T htile p d hdne
  · refine ⟨1, by norm_num, ?_⟩
    intro c hc
    exact hproper (sourceRay_properLine_scale δ a p d hpa hd c)
  · exact hpnot

private theorem sourceVertexRay_actual (K : PolygonalRegion) (P : PolyhedralCode)
    (T : Set Plane) (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (δ : Submodule ℝ Plane) (a p d : Plane)
    (hproper : Tiling.RationalSlopes.IsProperLink K δ T a)
    (hpa : p ∈ a +ᵥ (δ : Set Plane)) (hd : d ∈ δ) (hdne : d ≠ 0)
    (hpv : p ∈ Tiling.RationalSlopes.translatedVertices K T) :
    ∃ s ∈ T, p ∈ s +ᵥ Tiling.vertexSet K.support ∧ ∃ r : ℝ, 0 < r ∧
      ∀ c : ℝ, 0 < c → c < r → p + c • d ∈ frontier (s +ᵥ K.support) := by
  classical
  have hline (z : Plane) (hz : z ∈ δ) (c : ℝ) :
      p + c • z ∈ a +ᵥ (δ : Set Plane) := by
    obtain ⟨w, hw, hpw⟩ := Set.mem_vadd_set.mp hpa
    refine Set.mem_vadd_set.mpr ⟨w + c • z, δ.add_mem hw (δ.smul_mem c hz), ?_⟩
    rw [← hpw]
    simp only [vadd_eq_add]
    abel
  obtain ⟨v, hv, t, ht, hp⟩ := hpv
  have hpt : p ∈ t +ᵥ Tiling.vertexSet K.support := by
    apply Set.mem_vadd_set.mpr
    exact ⟨v, hv, by simpa only [vadd_eq_add, add_comm] using hp⟩
  have hstarMem : d ∈ originalVertexConeUnion K P T p := by
    rcases originalVertexConeUnion_fullOrHalfPlane K P T hP htile p t ht hpt with
      hfull | ⟨s, hs, hps, hpsnot, f, u, hu, hhalf, rH, hrH, hgerm⟩
    · rw [hfull]
      exact Set.mem_univ _
    · have hnonpos (z : Plane) (hz : z ∈ δ) : f z ≤ 0 := by
        by_contra hnot
        have hfz : 0 < f z := lt_of_not_ge hnot
        obtain ⟨c, hc, hsmall⟩ := exists_positiveScaling_intoBall z rH hrH
        have hdist : dist (p + c • z) p < rH := by
          simpa [dist_eq_norm] using hsmall
        have hfpositive : 0 < f ((p + c • z) - p) := by
          simp only [add_sub_cancel_left, map_smul, smul_eq_mul]
          exact mul_pos hc hfz
        have hinterior := positiveLinearGerm_mem_interior (s +ᵥ K.support)
          p f rH hgerm (p + c • z) hdist hfpositive
        rw [interior_vadd] at hinterior
        exact Set.disjoint_left.mp (sourceBoundaryUnion_disjoint_openCarrier K T
          htile.2.1 s hs) (hproper (hline z hz c)) hinterior
      have hfd : f d = 0 := by
        have h₁ := hnonpos d hd
        have h₂ := hnonpos (-d) (δ.neg_mem hd)
        rw [map_neg] at h₂
        linarith
      rw [hhalf]
      exact hfd.le
  obtain ⟨s, hcone⟩ := Set.mem_iUnion.mp hstarMem
  obtain ⟨rC, hrC, hgerm⟩ := originalVertexCopies_uniformConeGerm K P T hP
  let r : ℝ := rC / (‖d‖ + 1)
  have hden : 0 < ‖d‖ + 1 := by positivity
  refine ⟨s.1, s.1.2, s.2, r, div_pos hrC hden, ?_⟩
  intro c hc hcr
  have hdist : dist (c • d) 0 < rC := by
    have hprod : c * (‖d‖ + 1) < rC := (lt_div_iff₀ hden).mp hcr
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    nlinarith
  have hsource : p + c • d ∈ (s.1 : Plane) +ᵥ K.support :=
    (hgerm p (s.1 : Plane) s.1.2 s.2 (c • d) hdist).mpr
      ((polyhedralVertexCone_scale P (p - (s.1 : Plane)) d c hc).mpr hcone)
  have hnonint : p + c • d ∉ interior ((s.1 : Plane) +ᵥ K.support) := by
    rw [interior_vadd]
    exact fun h => Set.disjoint_left.mp (sourceBoundaryUnion_disjoint_openCarrier K T
      htile.2.1 (s.1 : Plane) s.1.2) (hproper (hline d hd c)) h
  rw [(K.isPolygonal.isClosed.vadd (s.1 : Plane)).frontier_eq]
  exact ⟨hsource, hnonint⟩

/-- Every actual source intrinsic vertex on any proper full link has a
labelled target frontier ray of a common positive physical radius.  This is
obtained from original stars, not from target-star finiteness or packing. -/
private theorem properLinkVertex_deformedUniformFrontierRay
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ (δ : Submodule ℝ Plane) (a p d : Plane),
            Tiling.RationalSlopes.IsProperLink K δ T a →
            p ∈ a +ᵥ (δ : Set Plane) → d ∈ δ → d ≠ 0 →
            p ∈ Tiling.RationalSlopes.translatedVertices K T →
            ∃ s ∈ T, p ∈ s +ᵥ Tiling.vertexSet K.support ∧
              ∀ c : ℝ, 0 < c → dist (c • d) 0 < r →
                deformPoint φ p + c • d ∈ frontier (deformPoint φ s +ᵥ Kφ.support) := by
  obtain ⟨F, ε, rA, hε, hrA, halign⟩ := originalVertexCopies_uniformAlignedGerm K P T hP
  obtain ⟨rC, hrC, hcone⟩ := originalVertexCopies_uniformConeGerm K P T hP
  refine ⟨F, ε, min rA rC, hε, lt_min hrA hrC, ?_⟩
  intro φ hφ Kφ hKφ δ a p d hproper hpa hd hdne hpv
  obtain ⟨s, hs, hps, ρ, hρ, hray⟩ :=
    sourceVertexRay_actual K P T hP htile δ a p d hproper hpa hd hdne hpv
  have hden : 0 < ‖d‖ + 1 := by positivity
  obtain ⟨c₀, hc₀, hc₀bound⟩ := exists_between
    (lt_min hρ (div_pos hrC hden))
  have hc₀ρ := hc₀bound.trans_le (min_le_left _ _)
  have hc₀dist : dist (c₀ • d) 0 < rC := by
    have hprod : c₀ * (‖d‖ + 1) < rC :=
      (lt_div_iff₀ hden).mp (hc₀bound.trans_le (min_le_right _ _))
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hc₀]
    nlinarith
  have hsupport : p + c₀ • d ∈ s +ᵥ K.support := by
    have h := frontier_subset_closure (hray c₀ hc₀ hc₀ρ)
    rwa [(K.isPolygonal.isClosed.vadd s).closure_eq] at h
  have hconeD : d ∈ polyhedralVertexCone P (p - s) :=
    (polyhedralVertexCone_scale P (p - s) d c₀ hc₀).mp
      ((hcone p s hs hps (c₀ • d) hc₀dist).mp hsupport)
  refine ⟨s, hs, hps, ?_⟩
  intro c hc hdist
  have hsource : p + c • d ∈ s +ᵥ K.support :=
    (hcone p s hs hps (c • d) (hdist.trans_le (min_le_right _ _))).mpr
      ((polyhedralVertexCone_scale P (p - s) d c hc).mpr hconeD)
  have hlocal := halign φ hφ Kφ hKφ p s hs hps (c • d)
    (hdist.trans_le (min_le_left _ _))
  have hline : p + c • d ∈ a +ᵥ (δ : Set Plane) := by
    obtain ⟨w, hw, hpw⟩ := Set.mem_vadd_set.mp hpa
    refine Set.mem_vadd_set.mpr ⟨w + c • d, δ.add_mem hw (δ.smul_mem c hd), ?_⟩
    rw [← hpw]
    simp only [vadd_eq_add]
    abel
  have hnonint : deformPoint φ p + c • d ∉ interior (deformPoint φ s +ᵥ Kφ.support) := by
    rw [interior_vadd]
    intro h
    exact Set.disjoint_left.mp (sourceBoundaryUnion_disjoint_openCarrier K T htile.2.1 s hs)
      (hproper hline) (hlocal.2.mpr h)
  rw [(Kφ.isPolygonal.isClosed.vadd (deformPoint φ s)).frontier_eq]
  exact ⟨hlocal.1.mp hsource, hnonint⟩

private theorem sourceRay_hits_vertexFree_intrinsicEdge
    {S : Set Plane} (_hS : Tiling.IsPolygonal S) {v d : Plane}
    (hv : v ∈ Tiling.vertexSet S) (_hd : d ≠ 0)
    {R : ℝ} (hR : 0 < R)
    (hray : ∀ c : ℝ, 0 < c → c < R → v + c • d ∈ frontier S)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet S ∧
      e.2 ∈ Tiling.vertexSet S ∧ segment ℝ e.1 e.2 ⊆ frontier S ∧
      ∀ x ∈ openSegment ℝ e.1 e.2, x ∉ Tiling.vertexSet S)
    (hcover : frontier S = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ e ∈ E, (e.1 = v ∨ e.2 = v) ∧
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c < c₀ →
        v + c • d ∈ segment ℝ e.1 e.2 := by
  classical
  let B := E.filter fun e => v ≠ e.1 ∧ v ≠ e.2
  let J := {e : Plane × Plane // e ∈ B}
  let _ : Finite J := B.finite_toSet.to_subtype
  let U : Set Plane := ⋃ e : J, segment ℝ e.1.1 e.1.2
  have hUclosed : IsClosed U := by
    exact isClosed_iUnion_of_finite fun e => by
      rw [← closure_openSegment (e.1.1) (e.1.2)]
      exact isClosed_closure
  have hvU : v ∉ U := by
    intro hvU
    obtain ⟨e, hve⟩ := Set.mem_iUnion.mp hvU
    have hmemB := Finset.mem_filter.mp e.property
    have hprops := hE e.1 hmemB.1
    have hvleft : v ≠ e.1.1 := hmemB.2.1
    have hvright : v ≠ e.1.2 := hmemB.2.2
    have hvo : v ∈ openSegment ℝ e.1.1 e.1.2 :=
      mem_openSegment_of_ne_left_right hvleft.symm hvright.symm hve
    exact (hprops.2.2.2.2 v hvo) hv
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hUclosed.isOpen_compl v hvU
  let b := min R (ρ / (‖d‖ + 1))
  have hb : 0 < b := lt_min hR (by positivity)
  obtain ⟨c, hc, hcb⟩ := exists_between hb
  have hcR : c < R := lt_of_lt_of_le hcb (min_le_left _ _)
  have hcρ : c < ρ / (‖d‖ + 1) := lt_of_lt_of_le hcb (min_le_right _ _)
  have hcdist : dist (v + c • d) v < ρ := by
    rw [dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    have hbound : c * ‖d‖ < ρ := by
      calc
        c * ‖d‖ < (ρ / (‖d‖ + 1)) * ‖d‖ := by gcongr
        _ < ρ := by
          have hden : 0 < ‖d‖ + 1 := by positivity
          rw [div_mul_eq_mul_div]
          apply (div_lt_iff₀ hden).2
          nlinarith [norm_nonneg d, hρ]
    exact hbound
  have hqfront : v + c • d ∈ frontier S := hray c hc hcR
  rw [hcover] at hqfront
  obtain ⟨e, he, hqseg⟩ := Set.mem_iUnion₂.mp hqfront
  have hincident : e.1 = v ∨ e.2 = v := by
    by_contra hnot
    have hnotleft : v ≠ e.1 := by
      intro heq
      exact hnot (Or.inl heq.symm)
    have hnotright : v ≠ e.2 := by
      intro heq
      exact hnot (Or.inr heq.symm)
    have heB : e ∈ B := Finset.mem_filter.mpr ⟨he, hnotleft, hnotright⟩
    have hqU : v + c • d ∈ U := by
      exact Set.mem_iUnion.mpr ⟨⟨e, heB⟩, hqseg⟩
    have hqball : v + c • d ∈ Metric.ball v ρ := by
      simpa [Metric.mem_ball, dist_comm] using hcdist
    exact (hball hqball) hqU
  have hsegRay : ∀ {w : Plane}, v + c • d ∈ segment ℝ v w →
      ∀ c' : ℝ, 0 < c' → c' < c → v + c' • d ∈ segment ℝ v w := by
    intro w hqseg' c' hc' hc'c
    let θ : ℝ := c' / c
    have hθpos : 0 < θ := by dsimp [θ]; exact div_pos hc' hc
    have hθlt : θ < 1 := by
      dsimp [θ]
      exact (div_lt_one hc).2 hc'c
    have hθ : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨hθpos.le, hθlt.le⟩
    have hcomb := (convex_segment v w) (left_mem_segment ℝ v w) hqseg'
      (sub_nonneg.mpr hθ.2) hθ.1 (by ring)
    have hθc : θ * c = c' := by
      dsimp [θ]
      field_simp
    have hcombEq : (1 - θ) • v + θ • (v + c • d) = v + c' • d := by
      calc
        (1 - θ) • v + θ • (v + c • d) =
            ((1 - θ) • v + θ • v) + (θ * c) • d := by
          rw [smul_add, smul_smul]
          abel
        _ = ((1 - θ) + θ) • v + (θ * c) • d := by rw [← add_smul]
        _ = v + c' • d := by rw [show (1 - θ) + θ = 1 by ring, one_smul, hθc]
    rw [hcombEq] at hcomb
    exact hcomb
  rcases hincident with heleft | heright
  · refine ⟨e, he, Or.inl heleft, c, hc, ?_⟩
    intro c' hc' hc'c
    have hqseg' : v + c • d ∈ segment ℝ v e.2 := by
      simpa [heleft] using hqseg
    simpa [heleft] using hsegRay hqseg' c' hc' hc'c
  · refine ⟨e, he, Or.inr heright, c, hc, ?_⟩
    intro c' hc' hc'c
    have hqseg' : v + c • d ∈ segment ℝ v e.1 := by
      simpa [heright, segment_symm] using hqseg
    simpa [heright, segment_symm] using hsegRay hqseg' c' hc' hc'c

/-- An actual directed frontier ray at an intrinsic endpoint selects a whole
primitive edge with a positive directed endpoint coefficient.  Subsequent
finite extension uses that edge length, not the image of a real cutoff. -/
private theorem sourceRay_intrinsicEdge_positiveEndpoint
    {S : Set Plane} (hS : Tiling.IsPolygonal S) {v d : Plane}
    (hv : v ∈ Tiling.vertexSet S) (hd : d ≠ 0)
    {R : ℝ} (hR : 0 < R)
    (hray : ∀ c : ℝ, 0 < c → c < R → v + c • d ∈ frontier S)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet S ∧
      e.2 ∈ Tiling.vertexSet S ∧ segment ℝ e.1 e.2 ⊆ frontier S ∧
      ∀ x ∈ openSegment ℝ e.1 e.2, x ∉ Tiling.vertexSet S)
    (hcover : frontier S = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ e ∈ E, ∃ c : ℝ, 0 < c ∧
      ((e.1 = v ∧ e.2 = v + c • d) ∨ (e.2 = v ∧ e.1 = v + c • d)) := by
  obtain ⟨e, he, hincident, c₀, hc₀, hsmall⟩ :=
    sourceRay_hits_vertexFree_intrinsicEdge hS hv hd hR hray E hE hcover
  have hc : 0 < c₀ / 2 := by positivity
  have hseg := hsmall (c₀ / 2) hc (by linarith)
  have recover {w : Plane} (h : v + (c₀ / 2) • d ∈ segment ℝ v w) :
      ∃ c : ℝ, 0 < c ∧ w = v + c • d := by
    rw [segment_eq_image_lineMap] at h
    obtain ⟨θ, hθ, hθeq⟩ := h
    have hθpos : 0 < θ := by
      apply lt_of_le_of_ne hθ.1
      intro hzero
      have hvzero : (c₀ / 2) • d = 0 := by
        have heq := hθeq
        rw [← hzero, AffineMap.lineMap_apply_zero] at heq
        have h := congrArg (fun z : Plane => z - v) heq
        simpa only [sub_self, add_sub_cancel_left] using h.symm
      exact hd ((smul_eq_zero.mp hvzero).resolve_left (ne_of_gt hc))
    have hvec : θ • (w - v) = (c₀ / 2) • d := by
      have heq := hθeq
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at heq
      calc
        θ • (w - v) = (θ • (w - v) + v) - v := by abel
        _ = (v + (c₀ / 2) • d) - v := by rw [heq]
        _ = (c₀ / 2) • d := by abel
    refine ⟨(c₀ / 2) / θ, div_pos hc hθpos, ?_⟩
    have hscaled := congrArg (fun z : Plane => θ⁻¹ • z) hvec
    have hvw : w - v = ((c₀ / 2) / θ) • d := by
      simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hθpos), one_smul,
        div_eq_mul_inv, mul_comm] using hscaled
    rw [← hvw]
    abel
  rcases hincident with hleft | hright
  · obtain ⟨c, hc, hendpoint⟩ := recover (by simpa only [hleft] using hseg)
    exact ⟨e, he, c, hc, Or.inl ⟨hleft, hendpoint⟩⟩
  · obtain ⟨c, hc, hendpoint⟩ := recover (by simpa only [hright, segment_symm] using hseg)
    exact ⟨e, he, c, hc, Or.inr ⟨hright, hendpoint⟩⟩

private theorem planarCrossCLM_ker_eq_span {d : Plane} (hd : d ≠ 0) :
    LinearMap.ker (Tiling.planarCrossCLM d).toLinearMap =
      Submodule.span ℝ ({d} : Set Plane) := by
  ext z
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  change Tiling.planarCross d z = 0 ↔ ∃ r : ℝ, r • d = z
  constructor
  · intro hz
    have hline : z ∈ Tiling.affineLine 0 d := by
      change Tiling.planarCross d z - Tiling.planarCross d 0 = 0
      simpa [Tiling.planarCross] using hz
    rcases (Tiling.mem_affineLine_iff_exists_smul hd).mp hline with ⟨r, hr⟩
    exact ⟨r, by simpa using hr.symm⟩
  · rintro ⟨r, rfl⟩
    simp [Tiling.planarCross]
    ring

private theorem normalizedLinearMap_exists_nonzeroTangent
    (f : Plane →L[ℝ] ℝ) (u : Plane) (hu : f u = 1) :
    ∃ d : Plane, d ≠ 0 ∧ f d = 0 := by
  have hcoords (z : Plane) : z = z.re • (1 : Plane) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  have hf (z : Plane) : f z = z.re * f 1 + z.im * f Complex.I := by
    calc
      f z = f (z.re • (1 : Plane) + z.im • Complex.I) := congrArg f (hcoords z)
      _ = z.re * f 1 + z.im * f Complex.I := by simp only [map_add, map_smul, smul_eq_mul]
  let d : Plane := ⟨-f Complex.I, f 1⟩
  refine ⟨d, ?_, ?_⟩
  · intro hd
    have hI : f Complex.I = 0 := by
      have h := congrArg Complex.re hd
      change -f Complex.I = 0 at h
      exact neg_eq_zero.mp h
    have h1 : f 1 = 0 := by
      have h := congrArg Complex.im hd
      exact h
    have hfu := hf u
    rw [hI, h1, mul_zero, mul_zero, zero_add, hu] at hfu
    exact one_ne_zero hfu
  · rw [hf]
    dsimp [d]
    ring


private theorem closedLinearHalfspace_eq_directedHalfplane
    (f : Plane →L[ℝ] ℝ) (u d : Plane) (hu : f u = 1)
    (hd : d ≠ 0) (hfd : f d = 0) :
    {z : Plane | f z ≤ 0} = Tiling.positiveHalfPlane 0 d ∨
      {z : Plane | f z ≤ 0} = Tiling.negativeHalfPlane 0 d := by
  let cross : Plane →L[ℝ] ℝ := Tiling.planarCrossCLM d
  obtain ⟨v, hv⟩ := exists_planarCrossCLM_normalizer hd
  have hkernel (z : Plane) : cross z = 0 ↔ z ∈ Submodule.span ℝ ({d} : Set Plane) := by
    change (Tiling.planarCrossCLM d).toLinearMap z = 0 ↔ _
    have hmem : z ∈ LinearMap.ker (Tiling.planarCrossCLM d).toLinearMap ↔
        z ∈ Submodule.span ℝ ({d} : Set Plane) := by
      rw [planarCrossCLM_ker_eq_span hd]
    simpa only [LinearMap.mem_ker] using hmem
  have hrem (z : Plane) : z - cross z • v ∈ Submodule.span ℝ ({d} : Set Plane) := by
    apply (hkernel (z - cross z • v)).mp
    change (Tiling.planarCrossCLM d).toLinearMap (z - cross z • v) = 0
    rw [map_sub, map_smul]
    change Tiling.planarCross d z - Tiling.planarCross d z *
      Tiling.planarCross d v = 0
    rw [Tiling.planarCrossCLM_apply] at hv
    rw [hv]
    ring
  have hvanish (z : Plane) (hz : z ∈ Submodule.span ℝ ({d} : Set Plane)) : f z = 0 := by
    rw [Submodule.mem_span_singleton] at hz
    rcases hz with ⟨t, rfl⟩
    rw [map_smul, hfd]
    simp
  have hfactor (z : Plane) : f z = f v * cross z := by
    have hz := hvanish (z - cross z • v) (hrem z)
    have hsplit : z = cross z • v + (z - cross z • v) := by abel
    calc
      f z = f (cross z • v + (z - cross z • v)) := congrArg f hsplit
      _ = f (cross z • v) + f (z - cross z • v) := map_add f _ _
      _ = cross z * f v := by rw [map_smul, hz]; ring
      _ = f v * cross z := by ring
  have hvf : f v ≠ 0 := by
    intro hvf0
    have huFactor := hfactor u
    rw [hu] at huFactor
    rw [hvf0] at huFactor
    simp at huFactor
  rcases lt_or_gt_of_ne hvf with hneg | hpos
  · left
    ext z
    rw [Set.mem_setOf_eq, Tiling.mem_positiveHalfPlane]
    have hs : Tiling.signedSide 0 d z = cross z := by
      simp [cross, Tiling.signedSide, Tiling.planarCross]
    rw [hfactor, hs]
    constructor
    · intro hz
      by_contra hn
      have hz' : cross z < 0 := lt_of_not_ge hn
      have hprod : 0 < f v * cross z := mul_pos_of_neg_of_neg hneg hz'
      linarith
    · intro hz
      exact mul_nonpos_of_nonpos_of_nonneg hneg.le hz
  · right
    ext z
    rw [Set.mem_setOf_eq, Tiling.mem_negativeHalfPlane]
    have hs : Tiling.signedSide 0 d z = cross z := by
      simp [cross, Tiling.signedSide, Tiling.planarCross]
    rw [hfactor, hs]
    constructor
    · intro hz
      by_contra hn
      have hz' : 0 < cross z := lt_of_not_ge hn
      have hprod : 0 < f v * cross z := mul_pos hpos hz'
      linarith
    · intro hz
      exact mul_nonpos_of_nonneg_of_nonpos hpos.le hz

/-- A local positive-side germ at an interior point of the direction ray fixes
which directed halfplane is the global linear sublevel set. -/
private theorem localPositiveGerm_selects_linearHalfspace
    (f : Plane →L[ℝ] ℝ) (u d : Plane) (hu : f u = 1)
    (hd : d ≠ 0) (hfd : f d = 0)
    (A : Set Plane) (r : ℝ) (hr : 0 < r)
    (hA : ∀ z, dist z 0 < r → z ∈ A → f z ≤ 0)
    (c : ℝ) (hc : dist (c • d) 0 < r)
    (hgerm : ∃ ρ : ℝ, 0 < ρ ∧
      A ∩ Metric.ball (c • d) ρ =
        Tiling.positiveHalfPlane (c • d) d ∩ Metric.ball (c • d) ρ) :
    {z : Plane | f z ≤ 0} = Tiling.positiveHalfPlane 0 d := by
  obtain hpos | hneg := closedLinearHalfspace_eq_directedHalfplane
    f u d hu hd hfd
  · exact hpos
  · obtain ⟨ρ, hρ, hEq⟩ := hgerm
    let v := d * Complex.I
    have hnorm : 0 < Complex.normSq d := Complex.normSq_pos.mpr hd
    have hcross : Tiling.signedSide (c • d) d ((c • d) + v) = Complex.normSq d := by
      rw [Tiling.signedSide_add_mul_I]
    have hmargin : 0 < r - dist (c • d) 0 := by linarith
    let η := min ρ (r - dist (c • d) 0)
    have hη : 0 < η := lt_min hρ hmargin
    have hden : 0 < 2 * (‖v‖ + 1) := by positivity
    obtain ⟨t, htpos, ht⟩ := exists_between (div_pos hη hden)
    have hdisp : dist ((c • d) + t • v) (c • d) < η := by
      rw [dist_eq_norm, show (c • d + t • v) - c • d = t • v by abel,
        norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      have hbound := (lt_div_iff₀ hden).mp ht
      dsimp [η] at hbound
      have hlt : t * ‖v‖ < t * (2 * (‖v‖ + 1)) := by
        nlinarith [norm_nonneg v, mul_nonneg htpos.le (norm_nonneg v)]
      exact hlt.trans hbound
    have hnear : dist ((c • d) + t • v) (c • d) < ρ := lt_of_lt_of_le hdisp (min_le_left _ _)
    have hball0 : dist ((c • d) + t • v) 0 < r := by
      have htri := dist_triangle ((c • d) + t • v) (c • d) 0
      exact lt_of_le_of_lt htri (by
        have hdisp' : dist ((c • d) + t • v) (c • d) < r - dist (c • d) 0 :=
          lt_of_lt_of_le hdisp (min_le_right _ _)
        linarith [dist_nonneg (x := (c • d)) (y := 0)])
    have hside : ((c • d) + t • v) ∈ Tiling.positiveHalfPlane (c • d) d := by
      rw [Tiling.mem_positiveHalfPlane]
      rw [show (c • d + t • v) = (c • d) + t • (d * Complex.I) by rfl]
      rw [Tiling.signedSide_add_smul_mul_I]
      exact mul_pos htpos hnorm |>.le
    have hzA : (c • d) + t • v ∈ A := by
      have hmem := congrArg (fun X : Set Plane => (c • d + t • v) ∈ X) hEq
      have hball : (c • d + t • v) ∈ Metric.ball (c • d) ρ := by
        simpa [Metric.mem_ball, dist_comm] using hnear
      have hmem' : (c • d + t • v) ∈ A ∩ Metric.ball (c • d) ρ :=
        hmem.mpr ⟨hside, hball⟩
      exact hmem'.1
    have hsub := hA ((c • d) + t • v) hball0 hzA
    have hfpoint : f ((c • d) + t • v) = t * f v := by
      calc
        f ((c • d) + t • v) = f (c • d) + f (t • v) := map_add f _ _
        _ = c * f d + t * f v := by
          rw [map_smul, map_smul]
          simp only [smul_eq_mul]
        _ = t * f v := by rw [hfd]; ring
    have hcrosspoint : Tiling.signedSide 0 d ((c • d) + t • v) > 0 := by
      have hshift : Tiling.signedSide 0 d ((c • d) + t • (d * Complex.I)) =
          Tiling.signedSide (c • d) d ((c • d) + t • (d * Complex.I)) := by
        simp [Tiling.signedSide, Tiling.planarCross]
        ring
      rw [show v = d * Complex.I by rfl, hshift, Tiling.signedSide_add_smul_mul_I]
      exact mul_pos htpos hnorm
    have hout : ((c • d) + t • v) ∉ Tiling.negativeHalfPlane 0 d := by
      rw [Tiling.mem_negativeHalfPlane]
      exact not_le_of_gt hcrosspoint
    have hin : ((c • d) + t • v) ∈ {z : Plane | f z ≤ 0} := hsub
    rw [hneg] at hin
    exact False.elim (hout hin)

private theorem linearHalfspace_boundary_notInterior (f : Plane →L[ℝ] ℝ)
    (u z : Plane) (hu : f u = 1) (hz : f z = 0) :
    z ∉ interior {w | f w ≤ 0} := by
  intro hinterior
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hinterior
  obtain ⟨c, hc, hsmall⟩ := exists_positiveScaling_intoBall u ρ hρ
  have hpoint : z + c • u ∈ Metric.ball z ρ := by
    simpa [dist_eq_norm] using hsmall
  have hnonpos : f (z + c • u) ≤ 0 := by
    exact (interior_subset (s := {w : Plane | f w ≤ 0})) (hball hpoint)
  rw [map_add, map_smul, hz, hu] at hnonpos
  change 0 + c * 1 ≤ 0 at hnonpos
  linarith

/-- In the omitted-smooth-label case, tangent rays have an actual intrinsic
star owner with a common source/target radius.  This is a finite local carrier
extension, not a claim of properness of the entire tangent line. -/
private theorem originalHalfVertexStar_uniformTangentRays
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p t : Plane, t ∈ T → p ∈ t +ᵥ Tiling.vertexSet K.support →
            originalVertexConeUnion K P T p = Set.univ ∨
              ∃ f : Plane →L[ℝ] ℝ, ∃ u : Plane, f u = 1 ∧
                originalVertexConeUnion K P T p = {z | f z ≤ 0} ∧
                ∀ d : Plane, f d = 0 → ∃ s ∈ T,
                  p ∈ s +ᵥ Tiling.vertexSet K.support ∧
                  ∀ c : ℝ, 0 < c → dist (c • d) 0 < r →
                    p + c • d ∈ frontier (s +ᵥ K.support) ∧
                    deformPoint φ p + c • d ∈ frontier (deformPoint φ s +ᵥ Kφ.support) := by
  obtain ⟨F, ε, rA, hε, hrA, halign⟩ := originalVertexCopies_uniformAlignedGerm K P T hP
  obtain ⟨rC, hrC, hcone⟩ := originalVertexCopies_uniformConeGerm K P T hP
  refine ⟨F, ε, min rA rC, hε, lt_min hrA hrC, ?_⟩
  intro φ hφ Kφ hKφ p t ht hpt
  rcases originalVertexConeUnion_fullOrHalfPlane K P T hP htile p t ht hpt with
    hfull | ⟨t₀, ht₀, hpt₀, hpnot₀, f, u, hu, hhalf, rH, hrH, hgerm⟩
  · exact Or.inl hfull
  · right
    refine ⟨f, u, hu, hhalf, ?_⟩
    intro d hfd
    have hdQ : d ∈ originalVertexConeUnion K P T p := by
      rw [hhalf]
      exact hfd.le
    obtain ⟨s, hdCone⟩ := Set.mem_iUnion.mp hdQ
    let C : Set Plane := polyhedralVertexCone P (p - (s.1 : Plane))
    have hCsub : C ⊆ {z | f z ≤ 0} := by
      intro z hz
      rw [← hhalf]
      exact Set.mem_iUnion.mpr ⟨s, hz⟩
    let A : Set Plane := (-p) +ᵥ ((s.1 : Plane) +ᵥ K.support)
    have hlocal (z : Plane) (hz : dist z 0 < rC) : z ∈ A ↔ z ∈ C := by
      have h := hcone p (s.1 : Plane) s.1.2 s.2 z hz
      simpa only [A, C, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add] using h
    refine ⟨s.1, s.1.2, s.2, ?_⟩
    intro c hc hdist
    have hdistC := hdist.trans_le (min_le_right _ _)
    have hdistA := hdist.trans_le (min_le_left _ _)
    have hzCone : c • d ∈ C :=
      (polyhedralVertexCone_scale P (p - (s.1 : Plane)) d c hc).mpr hdCone
    have hfzero : f (c • d) = 0 := by simp only [map_smul, hfd, smul_zero]
    have hzNotInterior : c • d ∉ interior C := fun h =>
      linearHalfspace_boundary_notInterior f u (c • d) hu hfzero (interior_mono hCsub h)
    have hzNotInteriorA : c • d ∉ interior A := fun h => hzNotInterior
      ((interior_mem_iff_of_ball_eq A C rC hrC hlocal (c • d) hdistC).mp h)
    have hsourceNoninterior : p + c • d ∉ interior ((s.1 : Plane) +ᵥ K.support) := by
      simpa only [A, interior_vadd, Set.mem_vadd_set_iff_neg_vadd_mem,
        neg_neg, vadd_eq_add] using hzNotInteriorA
    have hsource := (hcone p (s.1 : Plane) s.1.2 s.2 (c • d) hdistC).mpr hzCone
    have hsourceFrontier : p + c • d ∈ frontier ((s.1 : Plane) +ᵥ K.support) := by
      rw [(K.isPolygonal.isClosed.vadd _).frontier_eq]
      exact ⟨hsource, hsourceNoninterior⟩
    have htransport := halign φ hφ Kφ hKφ p (s.1 : Plane) s.1.2 s.2 (c • d) hdistA
    have htargetNoninterior : deformPoint φ p + c • d ∉
        interior (deformPoint φ (s.1 : Plane) +ᵥ Kφ.support) := by
      rw [interior_vadd] at hsourceNoninterior ⊢
      exact fun h => hsourceNoninterior (htransport.2.mpr h)
    refine ⟨hsourceFrontier, ?_⟩
    rw [(Kφ.isPolygonal.isClosed.vadd _).frontier_eq]
    exact ⟨htransport.1.mp hsource, htargetNoninterior⟩


private theorem sourceRay_shortParameter_mem_segment
    (a b d : Plane) (hd : d ≠ 0) {c l s : ℝ}
    (hc : 0 < c) (hba : b = a + c • d)
    (hLength : l ≤ dist a b) (hs : 0 ≤ s)
    (hsLength : dist (s • d) 0 ≤ l) :
    a + s • d ∈ segment ℝ a b := by
  have hnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hdistab : dist a b = c * ‖d‖ := by
    rw [dist_eq_norm, show a - b = -(c • d) by rw [hba]; abel]
    simp [Real.norm_eq_abs, abs_of_pos hc]
  have hdiststep : dist (s • d) 0 = s * ‖d‖ := by
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  have hsc : s ≤ c := by
    rw [hdiststep] at hsLength
    rw [hdistab] at hLength
    nlinarith
  have ht : s / c ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hs hc.le
    · exact (div_le_one hc).2 hsc
  have hpoint : AffineMap.lineMap a b (s / c) = a + s • d := by
    rw [AffineMap.lineMap_apply, vadd_eq_add,
      show b -ᵥ a = c • d by rw [vsub_eq_sub, hba]; abel,
      smul_smul, div_mul_cancel₀ s hc.ne']
    abel
  rw [segment_eq_image_lineMap]
  exact ⟨s / c, ht, hpoint⟩

private theorem translatedFrontierRay_intrinsicEdge_positiveEndpoint
    (K : PolygonalRegion) (s p d : Plane)
    (hp : p ∈ s +ᵥ Tiling.vertexSet K.support) (hd : d ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (hray : ∀ c : ℝ, 0 < c → dist (c • d) 0 < r →
      p + c • d ∈ frontier (s +ᵥ K.support))
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ x ∈ openSegment ℝ e.1 e.2, x ∉ Tiling.vertexSet K.support)
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ e ∈ E, ∃ c : ℝ, 0 < c ∧
      ((s + e.1 = p ∧ s + e.2 = p + c • d) ∨
        (s + e.2 = p ∧ s + e.1 = p + c • d)) := by
  have hp' : p - s ∈ Tiling.vertexSet K.support := by
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using
      Set.mem_vadd_set_iff_neg_vadd_mem.mp hp
  let R := r / (‖d‖ + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hray' (c : ℝ) (hc : 0 < c) (hcR : c < R) :
      (p - s) + c • d ∈ frontier K.support := by
    have hdist : dist (c • d) 0 < r := by
      rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      have hbound : c * (‖d‖ + 1) < r :=
        (lt_div_iff₀ (by positivity : 0 < ‖d‖ + 1)).mp hcR
      nlinarith [norm_nonneg d]
    have h := hray c hc hdist
    rw [frontier, closure_vadd, interior_vadd, ← Set.vadd_set_sdiff] at h
    have hmem := Set.mem_vadd_set_iff_neg_vadd_mem.mp h
    simpa only [frontier, vadd_eq_add, sub_eq_add_neg, add_assoc, add_comm,
      add_left_comm] using hmem
  obtain ⟨e, he, c, hc, hends⟩ := sourceRay_intrinsicEdge_positiveEndpoint
    K.isPolygonal hp' hd hR hray' E hE hcover
  refine ⟨e, he, c, hc, ?_⟩
  rcases hends with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · left
    constructor
    · rw [hleft]; abel
    · rw [hright]; abel
  · right
    constructor
    · rw [hleft]; abel
    · rw [hright]; abel

/-- The chosen intrinsic owner of each tangent ray supplies an actual whole
primitive occurrence on that same ray.  Both directed choices are available,
including at a terminating transverse carrier; no full-star conclusion is used. -/
private theorem originalHalfVertexStar_uniformTangentPrimitiveOccurrences
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ x ∈ openSegment ℝ e.1 e.2, x ∉ Tiling.vertexSet K.support)
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p t : Plane, t ∈ T → p ∈ t +ᵥ Tiling.vertexSet K.support →
            originalVertexConeUnion K P T p = Set.univ ∨
              ∃ f : Plane →L[ℝ] ℝ, ∃ u : Plane, f u = 1 ∧
                originalVertexConeUnion K P T p = {z | f z ≤ 0} ∧
                ∀ d : Plane, d ≠ 0 → f d = 0 → ∃ s ∈ T,
                  p ∈ s +ᵥ Tiling.vertexSet K.support ∧
                  (∃ e ∈ E, ∃ c : ℝ, 0 < c ∧
                    ((s + e.1 = p ∧ s + e.2 = p + c • d) ∨
                      (s + e.2 = p ∧ s + e.1 = p + c • d))) ∧
                  ∀ c : ℝ, 0 < c → dist (c • d) 0 < r →
                    p + c • d ∈ frontier (s +ᵥ K.support) ∧
                    deformPoint φ p + c • d ∈
                      frontier (deformPoint φ s +ᵥ Kφ.support) := by
  obtain ⟨F, ε, r, hε, hr, hstar⟩ :=
    originalHalfVertexStar_uniformTangentRays K P T hP htile
  refine ⟨F, ε, r, hε, hr, ?_⟩
  intro φ hφ Kφ hKφ p t ht hpt
  rcases hstar φ hφ Kφ hKφ p t ht hpt with hfull | ⟨f, u, hu, hhalf, hrays⟩
  · exact Or.inl hfull
  · right
    refine ⟨f, u, hu, hhalf, ?_⟩
    intro d hd hfd
    obtain ⟨s, hs, hps, hray⟩ := hrays d hfd
    refine ⟨s, hs, hps, ?_, hray⟩
    exact translatedFrontierRay_intrinsicEdge_positiveEndpoint K s p d hps hd r hr
      (fun c hc hdist => (hray c hc hdist).1) E hE hcover

private theorem originalHalfVertexStar_uniformIntegerTangentChoice
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ x ∈ openSegment ℝ e.1 e.2, x ∉ Tiling.vertexSet K.support)
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (Z : {e // e ∈ E} → Tiling.RationalPolygonal.IntegerPlane)
    (C : {e // e ∈ E} → ℝ)
    (hrep : ∀ i, 0 < C i ∧ Tiling.RationalPolygonal.integerPoint (Z i) ≠ 0 ∧
      i.1.2 - i.1.1 = C i • Tiling.RationalPolygonal.integerPoint (Z i)) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p t : Plane, t ∈ T → p ∈ t +ᵥ Tiling.vertexSet K.support →
            originalVertexConeUnion K P T p = Set.univ ∨
              ∃ i : {e // e ∈ E}, ∃ positive : Bool,
                originalVertexConeUnion K P T p =
                  (if positive then Tiling.positiveHalfPlane 0
                    (Tiling.RationalPolygonal.integerPoint (Z i))
                  else Tiling.negativeHalfPlane 0 (Tiling.RationalPolygonal.integerPoint (Z i))) ∧
                (∀ sign : Bool, ∃ s ∈ T, p ∈ s +ᵥ Tiling.vertexSet K.support ∧
                  ∃ e ∈ E, ∃ c : ℝ, 0 < c ∧
                    ((s + e.1 = p ∧ s + e.2 = p + c •
                      (if sign then Tiling.RationalPolygonal.integerPoint (Z i)
                        else -Tiling.RationalPolygonal.integerPoint (Z i))) ∨
                     (s + e.2 = p ∧ s + e.1 = p + c •
                      (if sign then Tiling.RationalPolygonal.integerPoint (Z i)
                        else -Tiling.RationalPolygonal.integerPoint (Z i))))) := by
  obtain ⟨F, ε, r, hε, _, hstar⟩ :=
    originalHalfVertexStar_uniformTangentPrimitiveOccurrences K P T hP htile E hE hcover
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ p t ht hpt
  rcases hstar φ hφ Kφ hKφ p t ht hpt with hfull | ⟨f, u, hu, hhalf, hrays⟩
  · exact Or.inl hfull
  obtain ⟨d₀, hd₀, hfd₀⟩ := normalizedLinearMap_exists_nonzeroTangent f u hu
  obtain ⟨s, hs, _, ⟨e, he, c, hc, hends⟩, _⟩ := hrays d₀ hd₀ hfd₀
  let i : {e // e ∈ E} := ⟨e, he⟩
  have hfe : f (e.2 - e.1) = 0 := by
    rcases hends with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · have hdir : e.2 - e.1 = c • d₀ := by
        calc
          e.2 - e.1 = (s + e.2) - (s + e.1) := by abel
          _ = (p + c • d₀) - p := by rw [hleft, hright]
          _ = c • d₀ := by abel
      rw [hdir, map_smul, hfd₀, smul_zero]
    · have hdir : e.2 - e.1 = (-c) • d₀ := by
        calc
          e.2 - e.1 = (s + e.2) - (s + e.1) := by abel
          _ = p - (p + c • d₀) := by rw [hleft, hright]
          _ = (-c) • d₀ := by module
      rw [hdir, map_smul, hfd₀, smul_zero]
  have hdi : Tiling.RationalPolygonal.integerPoint (Z i) ≠ 0 := (hrep i).2.1
  have hfdi : f (Tiling.RationalPolygonal.integerPoint (Z i)) = 0 := by
    have h := hfe
    rw [(hrep i).2.2, map_smul] at h
    change C i * f (Tiling.RationalPolygonal.integerPoint (Z i)) = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (hrep i).1)
  have hchoices (sign : Bool) : ∃ s ∈ T, p ∈ s +ᵥ Tiling.vertexSet K.support ∧
      ∃ e ∈ E, ∃ c : ℝ, 0 < c ∧
        ((s + e.1 = p ∧ s + e.2 = p + c •
          (if sign then Tiling.RationalPolygonal.integerPoint (Z i)
            else -Tiling.RationalPolygonal.integerPoint (Z i))) ∨
         (s + e.2 = p ∧ s + e.1 = p + c •
          (if sign then Tiling.RationalPolygonal.integerPoint (Z i)
            else -Tiling.RationalPolygonal.integerPoint (Z i)))) := by
    have hd : (if sign then Tiling.RationalPolygonal.integerPoint (Z i)
        else -Tiling.RationalPolygonal.integerPoint (Z i)) ≠ 0 := by
      cases sign <;> simpa using hdi
    have hfd : f (if sign then Tiling.RationalPolygonal.integerPoint (Z i)
        else -Tiling.RationalPolygonal.integerPoint (Z i)) = 0 := by
      cases sign <;> simp [hfdi]
    obtain ⟨s, hs, hps, hocc, _⟩ := hrays _ hd hfd
    exact ⟨s, hs, hps, hocc⟩
  rcases closedLinearHalfspace_eq_directedHalfplane f u _ hu hdi hfdi with hpos | hneg
  · exact Or.inr ⟨i, true, hhalf.trans hpos, hchoices⟩
  · exact Or.inr ⟨i, false, hhalf.trans hneg, hchoices⟩


/-- Local carrier inclusion, rather than full-link properness, suffices to
identify a half-star boundary direction at an interior source-chain endpoint. -/
private theorem originalVertexStar_localBoundaryInterval_normal
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (p t d : Plane) (ht : t ∈ T) (hpt : p ∈ t +ᵥ Tiling.vertexSet K.support)
    (hline : ∃ R > 0, ∀ c : ℝ, |c| < R →
      p + c • d ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support) :
    originalVertexConeUnion K P T p = Set.univ ∨
      ∃ f : Plane →L[ℝ] ℝ, ∃ u : Plane, f u = 1 ∧
        originalVertexConeUnion K P T p = {z | f z ≤ 0} ∧ f d = 0 := by
  rcases originalVertexConeUnion_fullOrHalfPlane K P T hP htile p t ht hpt with
    hfull | ⟨s, hs, hps, hpsnot, f, u, hu, hhalf, r, hr, hgerm⟩
  · exact Or.inl hfull
  · right
    exact ⟨f, u, hu, hhalf,
      sourceBoundary_localLinearGerm_annihilates_direction K T htile.2.1
        s p d hs f r hr hgerm hline⟩

/-- Endpoint set of one oriented closed-interval family.  Opposite signed
families are kept separate, even when they occupy the same full carrier. -/
private def scalarIntervalEndpoints (E : Set (ℝ × ℝ)) : Set ℝ :=
  {x | ∃ e ∈ E, x = e.1 ∨ x = e.2}

private theorem scalarIntervalFamily_endpoint_notInterior
    (E : Set (ℝ × ℝ)) (hpositive : ∀ e ∈ E, e.1 < e.2)
    (hdisjoint : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (Ioo e.1 e.2) (Ioo f.1 f.2))
    (e : ℝ × ℝ) (he : e ∈ E) (x : ℝ) (hx : x ∈ scalarIntervalEndpoints E) :
    x ∉ Ioo e.1 e.2 := by
  obtain ⟨f, hf, hxf⟩ := hx
  by_cases hef : e = f
  · subst f
    rcases hxf with rfl | rfl <;> simp
  · have hxfClosed : x ∈ Icc f.1 f.2 := by
      rcases hxf with rfl | rfl
      · exact ⟨le_rfl, (hpositive f hf).le⟩
      · exact ⟨(hpositive f hf).le, le_rfl⟩
    have hclosedDisjoint := (hdisjoint e he f hf hef).closure_right isOpen_Ioo
    rw [closure_Ioo (ne_of_lt (hpositive f hf))] at hclosedDisjoint
    exact fun hxOpen => Set.disjoint_left.mp hclosedDisjoint hxOpen hxfClosed

private theorem scalarIntervalFamily_consecutive_edge
    (E : Set (ℝ × ℝ)) (hpositive : ∀ e ∈ E, e.1 < e.2)
    (hdisjoint : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (Ioo e.1 e.2) (Ioo f.1 f.2))
    (hcover : ∀ x : ℝ, ∃ e ∈ E, x ∈ Icc e.1 e.2)
    (a b : ℝ) (ha : a ∈ scalarIntervalEndpoints E) (hb : b ∈ scalarIntervalEndpoints E)
    (hab : a < b)
    (hconsecutive : ∀ x ∈ scalarIntervalEndpoints E, ¬ (a < x ∧ x < b)) :
    (a, b) ∈ E := by
  let x : ℝ := (a + b) / 2
  have hax : a < x := by dsimp [x]; linarith
  have hxb : x < b := by dsimp [x]; linarith
  have hxnot : x ∉ scalarIntervalEndpoints E := fun hx => hconsecutive x hx ⟨hax, hxb⟩
  obtain ⟨e, he, hxedge⟩ := hcover x
  have hlo : e.1 ∈ scalarIntervalEndpoints E := ⟨e, he, Or.inl rfl⟩
  have hhi : e.2 ∈ scalarIntervalEndpoints E := ⟨e, he, Or.inr rfl⟩
  have hlox : e.1 < x := by
    by_contra h
    have hxeq : x = e.1 := le_antisymm (le_of_not_gt h) hxedge.1
    exact hxnot (hxeq ▸ hlo)
  have hxhi : x < e.2 := by
    by_contra h
    have hxeq : x = e.2 := le_antisymm hxedge.2 (le_of_not_gt h)
    exact hxnot (hxeq ▸ hhi)
  have hloa : e.1 ≤ a := by
    by_contra h
    exact hconsecutive e.1 hlo ⟨lt_of_not_ge h, hlox.trans hxb⟩
  have hbhi : b ≤ e.2 := by
    by_contra h
    exact hconsecutive e.2 hhi ⟨hax.trans hxhi, lt_of_not_ge h⟩
  have halo : a ≤ e.1 := by
    by_contra h
    exact scalarIntervalFamily_endpoint_notInterior E hpositive hdisjoint e he a ha
      ⟨lt_of_not_ge h, hax.trans hxhi⟩
  have hhib : e.2 ≤ b := by
    by_contra h
    exact scalarIntervalFamily_endpoint_notInterior E hpositive hdisjoint e he b hb
      ⟨hlox.trans hxb, lt_of_not_ge h⟩
  have he1 : e.1 = a := le_antisymm hloa halo
  have he2 : e.2 = b := le_antisymm hhib hbhi
  have heq : e = (a, b) := Prod.ext he1 he2
  rwa [heq] at he

private theorem scalarIntervalFamily_endpoints_cofinal (E : Set (ℝ × ℝ))
    (hcover : ∀ x : ℝ, ∃ e ∈ E, x ∈ Icc e.1 e.2) :
    (∀ x : ℝ, ∃ a ∈ scalarIntervalEndpoints E, a ≤ x) ∧
      (∀ x : ℝ, ∃ b ∈ scalarIntervalEndpoints E, x < b) := by
  constructor
  · intro x
    obtain ⟨e, he, hx⟩ := hcover x
    exact ⟨e.1, ⟨e, he, Or.inl rfl⟩, hx.1⟩
  · intro x
    obtain ⟨e, he, hx⟩ := hcover (x + 1)
    exact ⟨e.2, ⟨e, he, Or.inr rfl⟩, by linarith [hx.2]⟩

/-- Actual original prototype-edge occurrences on one carrier and one signed
side.  The scalar intervals are normalized left-to-right; opposite sides are
different families and their endpoint subdivisions are never merged. -/
private def signedCarrierIntervals (K : PolygonalRegion) (T : Set Plane)
    (E : Finset (Plane × Plane)) (a d : Plane) (positive : Bool) : Set (ℝ × ℝ) :=
  {q | q.1 < q.2 ∧ ∃ t ∈ T, ∃ e ∈ E,
    ((t + e.1 = a + q.1 • d ∧ t + e.2 = a + q.2 • d) ∨
      (t + e.2 = a + q.1 • d ∧ t + e.1 = a + q.2 • d)) ∧
    ∀ r ∈ Ioo q.1 q.2,
      if positive then positiveEdgeGerm (t +ᵥ K.support) d (a + r • d)
      else negativeEdgeGerm (t +ᵥ K.support) d (a + r • d)}

private theorem signedCarrierIntervals_endpoints_areSourceVertices
    (K : PolygonalRegion) (T : Set Plane) (E : Finset (Plane × Plane))
    (hvertices : ∀ e ∈ E, e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support)
    (a d : Plane) (positive : Bool) :
    scalarIntervalEndpoints (signedCarrierIntervals K T E a d positive) ⊆
      {r | a + r • d ∈ Tiling.RationalSlopes.translatedVertices K T} := by
  rintro r ⟨q, hq, hr⟩
  obtain ⟨hlt, t, ht, e, he, hcoords, hgerm⟩ := hq
  have hV := hvertices e he
  rcases hcoords with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · rcases hr with rfl | rfl
    · exact Set.mem_add.mpr ⟨e.1, hV.1, t, ht, by simpa only [add_comm] using hleft⟩
    · exact Set.mem_add.mpr ⟨e.2, hV.2, t, ht, by simpa only [add_comm] using hright⟩
  · rcases hr with rfl | rfl
    · exact Set.mem_add.mpr ⟨e.2, hV.2, t, ht, by simpa only [add_comm] using hleft⟩
    · exact Set.mem_add.mpr ⟨e.1, hV.1, t, ht, by simpa only [add_comm] using hright⟩

private theorem signedCarrierIntervals_sourceEndpoints_locallyFinite
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (E : Finset (Plane × Plane))
    (hvertices : ∀ e ∈ E, e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support)
    (a d : Plane) (hd : d ≠ 0) (positive : Bool) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (scalarIntervalEndpoints (signedCarrierIntervals K T E a d positive) ∩ Q).Finite := by
  intro Q hQ
  apply (sourceCarrierVertices_scalarLocallyFinite K T hpack a d hd Q hQ).subset
  rintro r ⟨hr, hrQ⟩
  exact ⟨signedCarrierIntervals_endpoints_areSourceVertices K T E hvertices a d positive hr, hrQ⟩

/-- The gap alphabet depends on prototype edge vectors, not on phases of the
opposite signed subdivision or differences between arbitrary carrier vertices. -/
private theorem signedCarrierIntervals_finitePositiveGapAlphabet
    (K : PolygonalRegion) (T : Set Plane) (E : Finset (Plane × Plane))
    (a d : Plane) (hd : d ≠ 0) (positive : Bool) :
    ∃ D : Finset ℝ, (∀ r ∈ D, 0 < r) ∧
      ∀ q ∈ signedCarrierIntervals K T E a d positive, q.2 - q.1 ∈ D := by
  classical
  let B : Finset Plane := E.image (fun e => e.2 - e.1) ∪ E.image (fun e => e.1 - e.2)
  let A : Set ℝ := Ioi 0 ∩ (fun r : ℝ => r • d) ⁻¹' (B : Set Plane)
  have hpreFinite : ((fun r : ℝ => r • d) ⁻¹' (B : Set Plane)).Finite :=
    B.finite_toSet.preimage (smul_left_injective ℝ hd).injOn
  have hA : A.Finite := hpreFinite.inter_of_right (Ioi 0)
  refine ⟨hA.toFinset, ?_, ?_⟩
  · intro r hr
    exact (hA.mem_toFinset.mp hr).1
  · intro q hq
    obtain ⟨hlt, t, ht, e, he, hcoords, hgerm⟩ := hq
    apply hA.mem_toFinset.mpr
    refine ⟨sub_pos.mpr hlt, ?_⟩
    change (q.2 - q.1) • d ∈ B
    rcases hcoords with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · have heq : (q.2 - q.1) • d = e.2 - e.1 := by
        rw [sub_smul]
        calc
          q.2 • d - q.1 • d = (a + q.2 • d) - (a + q.1 • d) := by abel
          _ = (t + e.2) - (t + e.1) := by rw [← hright, ← hleft]
          _ = e.2 - e.1 := by abel
      rw [heq]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    · have heq : (q.2 - q.1) • d = e.1 - e.2 := by
        rw [sub_smul]
        calc
          q.2 • d - q.1 • d = (a + q.2 • d) - (a + q.1 • d) := by abel
          _ = (t + e.1) - (t + e.2) := by rw [← hright, ← hleft]
          _ = e.1 - e.2 := by abel
      rw [heq]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)

/-- Original interval occurrences are locally finite because their own
endpoints are locally finite and their lengths have a common upper bound. -/
private theorem scalarIntervalFamily_locallyFinite (E : Set (ℝ × ℝ))
    (hpositive : ∀ e ∈ E, e.1 < e.2) (B : ℝ)
    (hbound : ∀ e ∈ E, e.2 - e.1 ≤ B)
    (hendpointLF : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (scalarIntervalEndpoints E ∩ Q).Finite) :
    LocallyFinite (fun e : E => Icc e.1.1 e.1.2) := by
  intro x
  let Q : Set ℝ := Icc (x - 1 - B) (x + 1 + B)
  have hF : (scalarIntervalEndpoints E ∩ Q).Finite := hendpointLF Q isCompact_Icc.isBounded
  have hpairFinite := hF.prod hF
  have hfinite : {e : E | e.1 ∈ (scalarIntervalEndpoints E ∩ Q) ×ˢ
      (scalarIntervalEndpoints E ∩ Q)}.Finite := hpairFinite.preimage Subtype.val_injective.injOn
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), hfinite.subset ?_⟩
  rintro e ⟨y, hyInterval, hyBall⟩
  have hyclose : |y - x| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hyBall
  have hylower := (abs_lt.mp hyclose).1
  have hyupper := (abs_lt.mp hyclose).2
  have hepositive := hpositive e.1 e.2
  have heupper := hbound e.1 e.2
  have hloQ : e.1.1 ∈ Q := by
    constructor <;> linarith [hyInterval.1, hyInterval.2]
  have hhiQ : e.1.2 ∈ Q := by
    constructor <;> linarith [hyInterval.1, hyInterval.2]
  exact ⟨⟨⟨e.1, e.2, Or.inl rfl⟩, hloQ⟩, ⟨⟨e.1, e.2, Or.inr rfl⟩, hhiQ⟩⟩

private theorem signedCarrierIntervals_original_locallyFinite
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (E : Finset (Plane × Plane))
    (hvertices : ∀ e ∈ E, e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support)
    (a d : Plane) (hd : d ≠ 0) (positive : Bool) :
    LocallyFinite (fun q : signedCarrierIntervals K T E a d positive => Icc q.1.1 q.1.2) := by
  obtain ⟨D, hDpositive, hgap⟩ := signedCarrierIntervals_finitePositiveGapAlphabet K T E a d hd positive
  apply scalarIntervalFamily_locallyFinite (signedCarrierIntervals K T E a d positive)
    (fun _ h => h.1) (∑ r ∈ D, |r|)
  · intro q hq
    have hsingle : |q.2 - q.1| ≤ ∑ r ∈ D, |r| :=
      Finset.single_le_sum (fun r hr => abs_nonneg r) (hgap q hq)
    exact (le_abs_self _).trans hsingle
  · exact signedCarrierIntervals_sourceEndpoints_locallyFinite K T hpack E hvertices a d hd positive

private theorem signedCarrierIntervals_closedUnion
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (E : Finset (Plane × Plane))
    (hvertices : ∀ e ∈ E, e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support)
    (a d : Plane) (hd : d ≠ 0) (positive : Bool) :
    IsClosed (⋃ q : signedCarrierIntervals K T E a d positive, Icc q.1.1 q.1.2) :=
  (signedCarrierIntervals_original_locallyFinite K T hpack E hvertices a d hd positive).isClosed_iUnion
    (fun _ => isClosed_Icc)

private theorem orientedHalfPlanes_positiveScale (p d : Plane) (c : ℝ) (hc : 0 < c) :
    Tiling.positiveHalfPlane p (c • d) = Tiling.positiveHalfPlane p d ∧
      Tiling.negativeHalfPlane p (c • d) = Tiling.negativeHalfPlane p d := by
  have hside (x : Plane) : Tiling.signedSide p (c • d) x = c * Tiling.signedSide p d x := by
    simp [Tiling.signedSide, Tiling.planarCross, Complex.smul_re, Complex.smul_im]
    ring
  constructor
  · ext x
    simp only [Tiling.mem_positiveHalfPlane, hside]
    constructor <;> intro h <;> nlinarith
  · ext x
    simp only [Tiling.mem_negativeHalfPlane, hside]
    constructor <;> intro h <;> nlinarith

private theorem orientedEdgeGerms_positiveScale (S : Set Plane) (p d : Plane)
    (c : ℝ) (hc : 0 < c) :
    (positiveEdgeGerm S (c • d) p ↔ positiveEdgeGerm S d p) ∧
      (negativeEdgeGerm S (c • d) p ↔ negativeEdgeGerm S d p) := by
  have h := orientedHalfPlanes_positiveScale p d c hc
  simp only [positiveEdgeGerm, negativeEdgeGerm, h.1, h.2, iff_self, and_self]

private theorem orientedEdgeGerms_negativeDirection (S : Set Plane) (p d : Plane) :
    (positiveEdgeGerm S (-d) p ↔ negativeEdgeGerm S d p) ∧
      (negativeEdgeGerm S (-d) p ↔ positiveEdgeGerm S d p) := by
  have hside (x : Plane) : Tiling.signedSide p (-d) x = -Tiling.signedSide p d x := by
    simp [Tiling.signedSide, Tiling.planarCross]
    ring
  have hpos : Tiling.positiveHalfPlane p (-d) = Tiling.negativeHalfPlane p d := by
    ext x
    simp only [Tiling.mem_positiveHalfPlane, Tiling.mem_negativeHalfPlane, hside]
    exact neg_nonneg
  have hneg : Tiling.negativeHalfPlane p (-d) = Tiling.positiveHalfPlane p d := by
    ext x
    simp only [Tiling.mem_positiveHalfPlane, Tiling.mem_negativeHalfPlane, hside]
    exact neg_nonpos
  simp only [positiveEdgeGerm, negativeEdgeGerm, hpos, hneg, iff_self, and_self]

/-- Actual source boundary carriers are closed before any target packing or LF
is known.  This is the only closedness used to take maximal scalar components. -/
private theorem sourceBoundaryParameters_isClosed
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) (a d : Plane) :
    IsClosed {r : ℝ | a + r • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} := by
  have hLF : LocallyFinite (fun t : T => (t : Plane) +ᵥ frontier K.support) :=
    (originalIndexedCopies_locallyFinite K T hpack).subset (fun t =>
      Set.vadd_set_mono K.isPolygonal.isClosed.frontier_subset)
  have hclosed : IsClosed (⋃ t : T, (t : Plane) +ᵥ frontier K.support) :=
    hLF.isClosed_iUnion (fun t => isClosed_frontier.vadd t.1)
  exact hclosed.preimage (continuous_const.add (continuous_id.smul continuous_const))

private theorem scalarClosedComponent_isClosed (B : Set ℝ) (hB : IsClosed B)
    {r : ℝ} (hr : r ∈ B) : IsClosed (connectedComponentIn B r) := by
  apply closure_subset_iff_isClosed.mp
  exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
    (subset_closure (mem_connectedComponentIn hr))
    (hB.closure_subset_iff.mpr (connectedComponentIn_subset B r))

/-- A connected source interval which touches the chosen component is wholly
inside it; no extension of a partial carrier to a full proper link is made. -/
private theorem scalarInterval_subset_component_of_meets
    (B : Set ℝ) {r l u : ℝ} (hr : r ∈ B) (hinterval : Icc l u ⊆ B)
    (hmeets : (Icc l u ∩ connectedComponentIn B r).Nonempty) :
    Icc l u ⊆ connectedComponentIn B r := by
  obtain ⟨x, hxI, hxJ⟩ := hmeets
  have hpre : IsPreconnected (Icc l u ∪ connectedComponentIn B r) :=
    isPreconnected_Icc.union x hxI hxJ isPreconnected_connectedComponentIn
  have hsub := hpre.subset_connectedComponentIn
    (Or.inr (mem_connectedComponentIn hr))
    (union_subset hinterval (connectedComponentIn_subset B r))
  exact fun _ hx => hsub (Or.inl hx)

private theorem scalarClosedComponent_closure_interior
    (B : Set ℝ) (hB : IsClosed B) {r l u : ℝ} (hr : r ∈ B) (hlu : l < u)
    (hinterval : Icc l u ⊆ connectedComponentIn B r) :
    closure (interior (connectedComponentIn B r)) = connectedComponentIn B r := by
  have hconvex : Convex ℝ (connectedComponentIn B r) :=
    isPreconnected_connectedComponentIn.ordConnected.convex
  have hnonempty : (interior (connectedComponentIn B r)).Nonempty := by
    obtain ⟨x, hx⟩ := Set.nonempty_Ioo.mpr hlu
    refine ⟨x, ?_⟩
    apply interior_mono hinterval
    simpa only [interior_Icc] using hx
  exact (hconvex.closure_interior_eq_closure_of_nonempty_interior hnonempty).trans
    (scalarClosedComponent_isClosed B hB hr).closure_eq

/-- Interior points of the maximal source component supply precisely the local
two-sided boundary interval required by the opposite-label germ constructor. -/
private theorem scalarClosedComponent_intervalRayLine
    (B : Set ℝ) (hB : IsClosed B) (r l u : ℝ) (hr : r ∈ B)
    (hlu : l < u) (hI : Icc l u ⊆ connectedComponentIn B r) :
    (∃ A C : ℝ, A < C ∧ connectedComponentIn B r = Icc A C) ∨
    (∃ A : ℝ, connectedComponentIn B r = Ici A) ∨
    (∃ C : ℝ, connectedComponentIn B r = Iic C) ∨
    connectedComponentIn B r = Set.univ := by
  let J := connectedComponentIn B r
  have hJclosed : IsClosed J := scalarClosedComponent_isClosed B hB hr
  have hJne : J.Nonempty := ⟨r, mem_connectedComponentIn hr⟩
  have hJord : J.OrdConnected := isPreconnected_connectedComponentIn.ordConnected
  have htwo : ∃ x ∈ J, ∃ y ∈ J, x < y := by
    exact ⟨l, hI (left_mem_Icc.mpr (le_of_lt hlu)), u,
      hI (right_mem_Icc.mpr (le_of_lt hlu)), hlu⟩
  by_cases hbelow : BddBelow J
  · by_cases habove : BddAbove J
    · let A := sInf J
      let C := sSup J
      have hA : A ∈ J := by
        dsimp [A]
        exact hJclosed.csInf_mem hJne hbelow
      have hC : C ∈ J := by
        dsimp [C]
        exact hJclosed.csSup_mem hJne habove
      have hAC : A < C := by
        obtain ⟨x, hx, y, hy, hxy⟩ := htwo
        dsimp [A, C]
        exact lt_of_le_of_lt (csInf_le hbelow hx) (lt_of_lt_of_le hxy (le_csSup habove hy))
      refine Or.inl ⟨A, C, hAC, ?_⟩
      ext x
      constructor
      · intro hx
        exact ⟨csInf_le hbelow hx, le_csSup habove hx⟩
      · intro hx
        exact hJord.out hA hC hx
    · let A := sInf J
      have hA : A ∈ J := by
        dsimp [A]
        exact hJclosed.csInf_mem hJne hbelow
      refine Or.inr (Or.inl ⟨A, ?_⟩)
      ext x
      constructor
      · intro hx
        exact csInf_le hbelow hx
      · intro hx
        obtain ⟨y, hy, hxy⟩ := not_bddAbove_iff.mp habove x
        exact hJord.out hA hy ⟨hx, hxy.le⟩
  · by_cases habove : BddAbove J
    · let C := sSup J
      have hC : C ∈ J := by
        dsimp [C]
        exact hJclosed.csSup_mem hJne habove
      refine Or.inr (Or.inr (Or.inl ⟨C, ?_⟩))
      ext x
      constructor
      · intro hx
        exact le_csSup habove hx
      · intro hx
        obtain ⟨y, hy, hyx⟩ := not_bddBelow_iff.mp hbelow x
        exact hJord.out hy hC ⟨hyx.le, hx⟩
    · refine Or.inr (Or.inr (Or.inr ?_))
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        obtain ⟨y, hy, hyx⟩ := not_bddBelow_iff.mp hbelow x
        obtain ⟨z, hz, hxz⟩ := not_bddAbove_iff.mp habove x
        exact hJord.out hy hz ⟨hyx.le, hxz.le⟩

private theorem sourceBoundaryComponent_localInterval
    (K : PolygonalRegion) (T : Set Plane) (a d : Plane) (r : ℝ)
    {q : ℝ}
    (hq : q ∈ interior (connectedComponentIn
      {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r)) :
    ∃ R > 0, ∀ c : ℝ, |c| < R →
      (a + q • d) + c • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hq)
  refine ⟨R, hR, ?_⟩
  intro c hc
  have hnear : q + c ∈ Metric.ball q R := by
    simpa only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left] using hc
  have hboundary := connectedComponentIn_subset
    {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r (hball hnear)
  change a + (q + c) • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support at hboundary
  simpa only [add_smul, add_assoc] using hboundary

private theorem scalarLocallyFinite_complement_dense (S : Set ℝ)
    (hLF : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite) : Dense Sᶜ := by
  intro x
  apply Metric.mem_closure_iff.mpr
  intro r hr
  have hfinite := hLF (Icc (x - r) (x + r)) isCompact_Icc.isBounded
  have hab : x - r < x + r := by linarith
  obtain ⟨y, hy, hyNot⟩ := (Ioo_infinite hab).exists_notMem_finite hfinite
  refine ⟨y, ?_, ?_⟩
  · exact fun hyS => hyNot ⟨hyS, hy.1.le, hy.2.le⟩
  · rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]

/-- Source side coverage can be checked away from source carrier vertices;
original interval LF then supplies the endpoints by closedness. -/
private theorem signedCarrierIntervals_cover_fromNonvertices
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (E : Finset (Plane × Plane))
    (hvertices : ∀ e ∈ E, e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support)
    (a d : Plane) (hd : d ≠ 0) (positive : Bool)
    (hgeneric : ∀ r : ℝ, a + r • d ∉ Tiling.RationalSlopes.translatedVertices K T →
      ∃ q ∈ signedCarrierIntervals K T E a d positive, r ∈ Icc q.1 q.2) :
    ⋃ q : signedCarrierIntervals K T E a d positive, Icc q.1.1 q.1.2 = Set.univ := by
  let S : Set ℝ := {r | a + r • d ∈ Tiling.RationalSlopes.translatedVertices K T}
  have hdense := scalarLocallyFinite_complement_dense S
    (sourceCarrierVertices_scalarLocallyFinite K T hpack a d hd)
  have hsub : Sᶜ ⊆ ⋃ q : signedCarrierIntervals K T E a d positive, Icc q.1.1 q.1.2 := by
    intro r hr
    obtain ⟨q, hq, hrq⟩ := hgeneric r hr
    exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hrq⟩
  exact (signedCarrierIntervals_closedUnion K T hpack E hvertices a d hd positive).closure_eq.symm.trans
    (hdense.mono hsub).closure_eq

private theorem carrierParameter_mem_openSegment (a d : Plane) (lo hi r : ℝ)
    (hlohi : lo < hi) (hr : r ∈ Ioo lo hi) :
    a + r • d ∈ openSegment ℝ (a + lo • d) (a + hi • d) := by
  let u : ℝ := (r - lo) / (hi - lo)
  have hden : 0 < hi - lo := sub_pos.mpr hlohi
  have hu : u ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr hr.1) hden
    · exact (div_lt_one hden).2 (by linarith [hr.2])
  have hparameter : lo + u * (hi - lo) = r := by
    dsimp [u]
    field_simp [ne_of_gt hden]
    ring
  rw [openSegment_eq_image_lineMap]
  refine ⟨u, hu, ?_⟩
  calc
    (AffineMap.lineMap (a + lo • d) (a + hi • d)) u =
        a + (lo + u * (hi - lo)) • d := by
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    _ = a + r • d := by rw [hparameter]

private theorem carrierParameter_mem_segment (a d : Plane) (lo hi r : ℝ)
    (hlohi : lo < hi) (hr : r ∈ Icc lo hi) :
    a + r • d ∈ segment ℝ (a + lo • d) (a + hi • d) := by
  rcases eq_or_lt_of_le hr.1 with h | h
  · rw [← h]
    exact left_mem_segment ℝ _ _
  rcases eq_or_lt_of_le hr.2 with h' | h'
  · rw [h']
    exact right_mem_segment ℝ _ _
  exact openSegment_subset_segment ℝ _ _
    (carrierParameter_mem_openSegment a d lo hi r hlohi ⟨h, h'⟩)

/-- Every closed occurrence interval lies in the actual source boundary set,
including its endpoints.  The witness remains the original primitive edge. -/
private theorem signedCarrierIntervals_sourceBoundaryParameters_subset
    (K : PolygonalRegion) (T : Set Plane) (E : Finset (Plane × Plane))
    (hfrontier : ∀ e ∈ E, segment ℝ e.1 e.2 ⊆ frontier K.support)
    (a d : Plane) (positive : Bool) {q : ℝ × ℝ}
    (hq : q ∈ signedCarrierIntervals K T E a d positive) :
    Icc q.1 q.2 ⊆
      {r : ℝ | a + r • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} := by
  obtain ⟨hord, t, ht, e, he, hcoords, _⟩ := hq
  intro r hr
  have hseg := carrierParameter_mem_segment a d q.1 q.2 r hord hr
  have htranslated : a + r • d ∈ segment ℝ (t + e.1) (t + e.2) := by
    rcases hcoords with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩
    · simpa only [h₁, h₂] using hseg
    · rw [segment_symm]
      simpa only [h₁, h₂] using hseg
  have hmem : a + r • d ∈ t +ᵥ frontier K.support := by
    apply Set.vadd_set_mono (hfrontier e he)
    simpa only [vadd_segment, vadd_eq_add] using htranslated
  exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hmem⟩

private theorem signedCarrierInterval_subset_component_of_meets
    (K : PolygonalRegion) (T : Set Plane) (E : Finset (Plane × Plane))
    (hfrontier : ∀ e ∈ E, segment ℝ e.1 e.2 ⊆ frontier K.support)
    (a d : Plane) (positive : Bool) {r : ℝ} {q : ℝ × ℝ}
    (hr : a + r • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
    (hq : q ∈ signedCarrierIntervals K T E a d positive)
    (hmeets : (Icc q.1 q.2 ∩ connectedComponentIn
      {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r).Nonempty) :
    Icc q.1 q.2 ⊆ connectedComponentIn
      {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r :=
  scalarInterval_subset_component_of_meets _ hr
    (signedCarrierIntervals_sourceBoundaryParameters_subset K T E hfrontier a d positive hq)
    hmeets

/-- One signed occurrence family restricted to the very same maximal actual
source carrier.  Endpoint alphabets remain separate for the two signs. -/
private def signedCarrierComponentIntervals (K : PolygonalRegion) (T : Set Plane)
    (E : Finset (Plane × Plane)) (a d : Plane) (r : ℝ) (positive : Bool) :
    Set (ℝ × ℝ) :=
  {q | q ∈ signedCarrierIntervals K T E a d positive ∧
    Icc q.1 q.2 ⊆ connectedComponentIn
      {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r}

private theorem signedCarrierComponentIntervals_original_locallyFinite
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (E : Finset (Plane × Plane))
    (hvertices : ∀ e ∈ E, e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support)
    (a d : Plane) (hd : d ≠ 0) (r : ℝ) (positive : Bool) :
    LocallyFinite (fun q : signedCarrierComponentIntervals K T E a d r positive =>
      Icc q.1.1 q.1.2) := by
  let f : signedCarrierComponentIntervals K T E a d r positive →
      signedCarrierIntervals K T E a d positive := fun q => ⟨q.1, q.2.1⟩
  have hf : Function.Injective f := by
    intro q s h
    apply Subtype.ext
    exact congrArg (fun z : signedCarrierIntervals K T E a d positive => z.1) h
  have hLF := signedCarrierIntervals_original_locallyFinite K T hpack E hvertices a d hd positive
  have h := hLF.comp_injective hf
  simpa only [Function.comp_def, f] using h

private theorem signedCarrierComponentIntervals_closedUnion
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (E : Finset (Plane × Plane))
    (hvertices : ∀ e ∈ E, e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support)
    (a d : Plane) (hd : d ≠ 0) (r : ℝ) (positive : Bool) :
    IsClosed (⋃ q : signedCarrierComponentIntervals K T E a d r positive,
      Icc q.1.1 q.1.2) :=
  LocallyFinite.isClosed_iUnion
    (signedCarrierComponentIntervals_original_locallyFinite K T hpack E hvertices a d hd r positive)
    (fun _ => isClosed_Icc)

private theorem sourceRay_link_frontier_vadd (u : Plane) (D : Set Plane) :
    u +ᵥ frontier D = frontier (u +ᵥ D) := by
  simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
    (Homeomorph.addLeft u).image_frontier D

private theorem sourceRay_frontierGerm_line (A : Set Plane) (hAclosed : IsClosed A)
    (p d q : Plane) (hfront : q ∈ frontier A)
    (r : ℝ) (hr : 0 < r)
    (hlocal : A ∩ Metric.ball p r = Tiling.positiveHalfPlane p d ∩ Metric.ball p r ∨
      A ∩ Metric.ball p r = Tiling.negativeHalfPlane p d ∩ Metric.ball p r)
    (hqball : q ∈ Metric.ball p r) :
    Tiling.signedSide p d q = 0 := by
  rcases hlocal with heq | heq
  · have hqA : q ∈ A := by
      have h := frontier_subset_closure hfront
      rwa [hAclosed.closure_eq] at h
    have hqside : q ∈ Tiling.positiveHalfPlane p d := by
      have hmem := congrArg (fun S : Set Plane => q ∈ S) heq
      exact (hmem.mp ⟨hqA, hqball⟩).1
    have hqnotInt : q ∉ interior A := by
      intro hqi
      exact (Set.disjoint_left.mp disjoint_interior_frontier) hqi hfront
    have hsideNonneg : 0 ≤ Tiling.signedSide p d q :=
      Tiling.mem_positiveHalfPlane.mp hqside
    by_contra hzero
    have hstrict : 0 < Tiling.signedSide p d q := lt_of_le_of_ne hsideNonneg (Ne.symm hzero)
    have hopen : IsOpen (Metric.ball p r ∩ {x | 0 < Tiling.signedSide p d x}) :=
      Metric.isOpen_ball.inter (isOpen_Ioi.preimage
        (Tiling.continuous_signedSide p d))
    have hsub : Metric.ball p r ∩ {x | 0 < Tiling.signedSide p d x} ⊆ A := by
      intro x hx
      have hmem := congrArg (fun S : Set Plane => x ∈ S) heq
      have hxball : x ∈ Metric.ball p r := hx.1
      have hxpos : x ∈ Tiling.positiveHalfPlane p d :=
        Tiling.mem_positiveHalfPlane.mpr hx.2.le
      exact (hmem.mpr ⟨hxpos, hxball⟩).1
    have hqint : q ∈ interior A := interior_maximal hsub hopen ⟨hqball, hstrict⟩
    exact hqnotInt hqint
  · have hqA : q ∈ A := by
      have h := frontier_subset_closure hfront
      rwa [hAclosed.closure_eq] at h
    have hqside : q ∈ Tiling.negativeHalfPlane p d := by
      have hmem := congrArg (fun S : Set Plane => q ∈ S) heq
      exact (hmem.mp ⟨hqA, hqball⟩).1
    have hqnotInt : q ∉ interior A := by
      intro hqi
      exact (Set.disjoint_left.mp disjoint_interior_frontier) hqi hfront
    have hsideNonpos : Tiling.signedSide p d q ≤ 0 :=
      Tiling.mem_negativeHalfPlane.mp hqside
    by_contra hzero
    have hstrict : Tiling.signedSide p d q < 0 := lt_of_le_of_ne hsideNonpos hzero
    have hopen : IsOpen (Metric.ball p r ∩ {x | Tiling.signedSide p d x < 0}) :=
      Metric.isOpen_ball.inter (isOpen_Iio.preimage
        (Tiling.continuous_signedSide p d))
    have hsub : Metric.ball p r ∩ {x | Tiling.signedSide p d x < 0} ⊆ A := by
      intro x hx
      have hmem := congrArg (fun S : Set Plane => x ∈ S) heq
      have hxneg : x ∈ Tiling.negativeHalfPlane p d :=
        Tiling.mem_negativeHalfPlane.mpr hx.2.le
      exact (hmem.mpr ⟨hxneg, hx.1⟩).1
    have hqint : q ∈ interior A := interior_maximal hsub hopen ⟨hqball, hstrict⟩
    exact hqnotInt hqint

private theorem sourceRay_edgeDirection_parallel
    {A : Set Plane} (hAclosed : IsClosed A) {v w p d : Plane}
    (hvw : v ≠ w) (hp : p ∈ segment ℝ v w)
    (hseg : segment ℝ v w ⊆ frontier A) (hd : d ≠ 0)
    (hgerm : positiveEdgeGerm A d p ∨ negativeEdgeGerm A d p) :
    ∃ c : ℝ, w - v = c • d := by
  rcases hgerm with ⟨r, hr, hlocal⟩ | ⟨r, hr, hlocal⟩
  · have hnear : ∀ᶠ y in 𝓝 p, y ∈ frontier A → y - p ∈ ℝ ∙ d := by
      filter_upwards [Metric.ball_mem_nhds p hr] with y hy hfront
      have hside := sourceRay_frontierGerm_line A hAclosed p d y hfront r hr
        (Or.inl hlocal) hy
      obtain ⟨c, hc⟩ := (Tiling.mem_affineLine_iff_exists_smul hd).mp hside
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      simpa [vadd_eq_add, add_comm] using (congrArg (fun z : Plane => z - p) hc).symm
    have hdir := segment_direction_mem_of_frontierGerm hseg hp hnear
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdir
    exact ⟨c, hc.symm⟩
  · have hnear : ∀ᶠ y in 𝓝 p, y ∈ frontier A → y - p ∈ ℝ ∙ d := by
      filter_upwards [Metric.ball_mem_nhds p hr] with y hy hfront
      have hside := sourceRay_frontierGerm_line A hAclosed p d y hfront r hr
        (Or.inr hlocal) hy
      obtain ⟨c, hc⟩ := (Tiling.mem_affineLine_iff_exists_smul hd).mp hside
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      simpa [vadd_eq_add, add_comm] using (congrArg (fun z : Plane => z - p) hc).symm
    have hdir := segment_direction_mem_of_frontierGerm hseg hp hnear
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hdir
    exact ⟨c, hc.symm⟩

private theorem sourceRay_vadd_positiveEdgeGerm (A : Set Plane) (s p d : Plane)
    (h : positiveEdgeGerm A d p) :
    positiveEdgeGerm (s +ᵥ A) d (s + p) := by
  obtain ⟨r, hr, hlocal⟩ := h
  refine ⟨r, hr, ?_⟩
  ext z
  have hball : dist z (s + p) = dist (z - s) p := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have hside : Tiling.signedSide (s + p) d z = Tiling.signedSide p d (z - s) := by
    simp [Tiling.signedSide, Tiling.planarCross]
    ring
  have hA : z ∈ s +ᵥ A ↔ z - s ∈ A := by
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    congr 1
    abel
  have hhalf : z ∈ Tiling.positiveHalfPlane (s + p) d ↔
      z - s ∈ Tiling.positiveHalfPlane p d := by
    rw [Tiling.mem_positiveHalfPlane, Tiling.mem_positiveHalfPlane, hside]
  have hball' : z ∈ Metric.ball (s + p) r ↔ z - s ∈ Metric.ball p r := by
    rw [Metric.mem_ball, Metric.mem_ball, hball]
  simp only [Set.mem_inter_iff]
  rw [hA, hball', hhalf]
  simpa only [Set.mem_inter_iff] using (Set.ext_iff.mp hlocal (z - s))

private theorem sourceRay_vadd_negativeEdgeGerm (A : Set Plane) (s p d : Plane)
    (h : negativeEdgeGerm A d p) :
    negativeEdgeGerm (s +ᵥ A) d (s + p) := by
  obtain ⟨r, hr, hlocal⟩ := h
  refine ⟨r, hr, ?_⟩
  ext z
  have hball : dist z (s + p) = dist (z - s) p := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have hside : Tiling.signedSide (s + p) d z = Tiling.signedSide p d (z - s) := by
    simp [Tiling.signedSide, Tiling.planarCross]
    ring
  have hA : z ∈ s +ᵥ A ↔ z - s ∈ A := by
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    congr 1
    abel
  have hhalf : z ∈ Tiling.negativeHalfPlane (s + p) d ↔
      z - s ∈ Tiling.negativeHalfPlane p d := by
    rw [Tiling.mem_negativeHalfPlane, Tiling.mem_negativeHalfPlane, hside]
  have hball' : z ∈ Metric.ball (s + p) r ↔ z - s ∈ Metric.ball p r := by
    rw [Metric.mem_ball, Metric.mem_ball, hball]
  simp only [Set.mem_inter_iff]
  rw [hA, hball', hhalf]
  simpa only [Set.mem_inter_iff] using (Set.ext_iff.mp hlocal (z - s))

/-- A genuine signed primitive sector of an intrinsic star label fixes the
occupied half-star side at an interior local source carrier point. -/
private theorem originalVertexStar_signedLocalCarrier_positiveHalfplane
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ r : ℝ, 0 < r ∧ ∀ p s d : Plane, s ∈ T →
      p ∈ s +ᵥ Tiling.vertexSet K.support → d ≠ 0 →
      (∃ R > 0, ∀ b : ℝ, |b| < R →
        p + b • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) →
      ∀ c : ℝ, dist (c • d) 0 < r →
        positiveEdgeGerm (s +ᵥ K.support) d (p + c • d) →
          originalVertexConeUnion K P T p = Set.univ ∨
            originalVertexConeUnion K P T p = Tiling.positiveHalfPlane 0 d := by
  obtain ⟨r, hr, hcone⟩ := originalVertexCopies_uniformConeGerm K P T hP
  refine ⟨r, hr, ?_⟩
  intro p s d hs hps hd hline c hc hgerm
  rcases originalVertexStar_localBoundaryInterval_normal K P T hP htile
    p s d hs hps hline with hfull | ⟨f, u, hu, hhalf, hfd⟩
  · exact Or.inl hfull
  · right
    let A : Set Plane := (-p) +ᵥ (s +ᵥ K.support)
    have hA (z : Plane) (hz : dist z 0 < r) (hzA : z ∈ A) : f z ≤ 0 := by
      have hzcopy : p + z ∈ s +ᵥ K.support := by
        simpa only [A, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add] using hzA
      have hzcone := (hcone p s hs hps z hz).mp hzcopy
      have hzQ : z ∈ originalVertexConeUnion K P T p :=
        Set.mem_iUnion.mpr ⟨⟨⟨s, hs⟩, hps⟩, hzcone⟩
      rw [hhalf] at hzQ
      exact hzQ
    have hcenter : -p + (p + c • d) = c • d := by abel
    have hgermA : positiveEdgeGerm A d (c • d) := by
      have h := sourceRay_vadd_positiveEdgeGerm (s +ᵥ K.support) (-p) (p + c • d) d hgerm
      simpa only [A, hcenter] using h
    rw [hhalf]
    exact localPositiveGerm_selects_linearHalfspace f u d hu hd hfd A r hr hA c hc hgermA

private theorem sourceRay_germ_mem (A : Set Plane) (p d : Plane)
    (h : positiveEdgeGerm A d p ∨ negativeEdgeGerm A d p) : p ∈ A := by
  rcases h with ⟨r, hr, heq⟩ | ⟨r, hr, heq⟩
  · have hball : p ∈ Metric.ball p r := Metric.mem_ball_self hr
    have hhalf : p ∈ Tiling.positiveHalfPlane p d := by
      simp [Tiling.mem_positiveHalfPlane, Tiling.signedSide]
    exact ((Set.ext_iff.mp heq p).mpr ⟨hhalf, hball⟩).1
  · have hball : p ∈ Metric.ball p r := Metric.mem_ball_self hr
    have hhalf : p ∈ Tiling.negativeHalfPlane p d := by
      simp [Tiling.mem_negativeHalfPlane, Tiling.signedSide]
    exact ((Set.ext_iff.mp heq p).mpr ⟨hhalf, hball⟩).1

private theorem sourceRay_germ_scale_direction
    {A : Set Plane} {p d w : Plane} {c : ℝ}
    (hc : c ≠ 0) (hdir : w = c • d)
    (hgerm : positiveEdgeGerm A w p ∨ negativeEdgeGerm A w p) :
    positiveEdgeGerm A d p ∨ negativeEdgeGerm A d p := by
  have hside (z : Plane) : Tiling.signedSide p w z = c * Tiling.signedSide p d z := by
    simp [Tiling.signedSide, Tiling.planarCross, hdir]
    ring
  by_cases hcpos : 0 < c
  · have hpos : Tiling.positiveHalfPlane p w = Tiling.positiveHalfPlane p d := by
      ext z
      simp only [Tiling.mem_positiveHalfPlane]
      rw [hside]
      constructor <;> intro hz <;> nlinarith
    have hneg : Tiling.negativeHalfPlane p w = Tiling.negativeHalfPlane p d := by
      ext z
      simp only [Tiling.mem_negativeHalfPlane]
      rw [hside]
      constructor <;> intro hz <;> nlinarith
    rcases hgerm with ⟨r, hr, heq⟩ | ⟨r, hr, heq⟩
    · left
      exact ⟨r, hr, by rw [heq, hpos]⟩
    · right
      exact ⟨r, hr, by rw [heq, hneg]⟩
  · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
    have hpos : Tiling.positiveHalfPlane p w = Tiling.negativeHalfPlane p d := by
      ext z
      simp only [Tiling.mem_positiveHalfPlane, Tiling.mem_negativeHalfPlane]
      rw [hside]
      constructor <;> intro hz <;> nlinarith
    have hneg : Tiling.negativeHalfPlane p w = Tiling.positiveHalfPlane p d := by
      ext z
      simp only [Tiling.mem_negativeHalfPlane, Tiling.mem_positiveHalfPlane]
      rw [hside]
      constructor <;> intro hz <;> nlinarith
    rcases hgerm with ⟨r, hr, heq⟩ | ⟨r, hr, heq⟩
    · right
      exact ⟨r, hr, by rw [heq, hpos]⟩
    · left
      exact ⟨r, hr, by rw [heq, hneg]⟩

private theorem sourceRay_positiveGerm_scale_pos
    {A : Set Plane} {p d w : Plane} {c : ℝ} (hc : 0 < c)
    (hdir : w = c • d) (h : positiveEdgeGerm A w p) :
    positiveEdgeGerm A d p := by
  have hside (z : Plane) : Tiling.signedSide p w z = c * Tiling.signedSide p d z := by
    simp [Tiling.signedSide, Tiling.planarCross, hdir]
    ring
  have hhalf : Tiling.positiveHalfPlane p w = Tiling.positiveHalfPlane p d := by
    ext z
    simp only [Tiling.mem_positiveHalfPlane]
    rw [hside]
    constructor <;> intro hz <;> nlinarith
  rcases h with ⟨r, hr, heq⟩
  exact ⟨r, hr, by rw [heq, hhalf]⟩

private theorem sourceRay_negativeGerm_scale_pos
    {A : Set Plane} {p d w : Plane} {c : ℝ} (hc : 0 < c)
    (hdir : w = c • d) (h : negativeEdgeGerm A w p) :
    negativeEdgeGerm A d p := by
  have hside (z : Plane) : Tiling.signedSide p w z = c * Tiling.signedSide p d z := by
    simp [Tiling.signedSide, Tiling.planarCross, hdir]
    ring
  have hhalf : Tiling.negativeHalfPlane p w = Tiling.negativeHalfPlane p d := by
    ext z
    simp only [Tiling.mem_negativeHalfPlane]
    rw [hside]
    constructor <;> intro hz <;> nlinarith
  rcases h with ⟨r, hr, heq⟩
  exact ⟨r, hr, by rw [heq, hhalf]⟩

private theorem sourceRay_positiveGerm_scale_neg
    {A : Set Plane} {p d w : Plane} {c : ℝ} (hc : c < 0)
    (hdir : w = c • d) (h : positiveEdgeGerm A w p) :
    negativeEdgeGerm A d p := by
  have hside (z : Plane) : Tiling.signedSide p w z = c * Tiling.signedSide p d z := by
    simp [Tiling.signedSide, Tiling.planarCross, hdir]
    ring
  have hhalf : Tiling.positiveHalfPlane p w = Tiling.negativeHalfPlane p d := by
    ext z
    simp only [Tiling.mem_positiveHalfPlane, Tiling.mem_negativeHalfPlane]
    rw [hside]
    constructor <;> intro hz <;> nlinarith
  rcases h with ⟨r, hr, heq⟩
  exact ⟨r, hr, by rw [heq, hhalf]⟩

private theorem sourceRay_negativeGerm_scale_neg
    {A : Set Plane} {p d w : Plane} {c : ℝ} (hc : c < 0)
    (hdir : w = c • d) (h : negativeEdgeGerm A w p) :
    positiveEdgeGerm A d p := by
  have hside (z : Plane) : Tiling.signedSide p w z = c * Tiling.signedSide p d z := by
    simp [Tiling.signedSide, Tiling.planarCross, hdir]
    ring
  have hhalf : Tiling.negativeHalfPlane p w = Tiling.positiveHalfPlane p d := by
    ext z
    simp only [Tiling.mem_negativeHalfPlane, Tiling.mem_positiveHalfPlane]
    rw [hside]
    constructor <;> intro hz <;> nlinarith
  rcases h with ⟨r, hr, heq⟩
  exact ⟨r, hr, by rw [heq, hhalf]⟩

private theorem originalVertexStar_signedLocalCarrier_halfplane
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ r : ℝ, 0 < r ∧ ∀ p s d : Plane, s ∈ T →
      p ∈ s +ᵥ Tiling.vertexSet K.support → d ≠ 0 →
      (∃ R > 0, ∀ b : ℝ, |b| < R →
        p + b • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) →
      ∀ c : ℝ, dist (c • d) 0 < r → ∀ positive : Bool,
        (if positive then positiveEdgeGerm (s +ᵥ K.support) d (p + c • d)
          else negativeEdgeGerm (s +ᵥ K.support) d (p + c • d)) →
          originalVertexConeUnion K P T p = Set.univ ∨
            originalVertexConeUnion K P T p =
              (if positive then Tiling.positiveHalfPlane 0 d else Tiling.negativeHalfPlane 0 d) := by
  obtain ⟨r, hr, hpositive⟩ :=
    originalVertexStar_signedLocalCarrier_positiveHalfplane K P T hP htile
  refine ⟨r, hr, ?_⟩
  intro p s d hs hps hd hline c hc positive hgerm
  cases positive with
  | true => exact hpositive p s d hs hps hd hline c hc hgerm
  | false =>
      change negativeEdgeGerm (s +ᵥ K.support) d (p + c • d) at hgerm
      obtain ⟨R, hR, hlineR⟩ := hline
      have hline' : ∃ R > 0, ∀ b : ℝ, |b| < R →
          p + b • (-d) ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support := by
        refine ⟨R, hR, ?_⟩
        intro b hb
        have h := hlineR (-b) (by simpa only [abs_neg] using hb)
        simpa only [neg_smul, smul_neg] using h
      have hpoint : (-c) • (-d) = c • d := by simp
      have hgerm' : positiveEdgeGerm (s +ᵥ K.support) (-d) (p + (-c) • (-d)) := by
        rw [hpoint]
        exact sourceRay_negativeGerm_scale_neg (c := (-1 : ℝ)) (d := -d)
          (w := d) (by norm_num) (by simp) hgerm
      have hflip : Tiling.positiveHalfPlane 0 (-d) = Tiling.negativeHalfPlane 0 d := by
        ext z
        simp only [Tiling.mem_positiveHalfPlane, Tiling.mem_negativeHalfPlane]
        have hside : Tiling.signedSide 0 (-d) z = -Tiling.signedSide 0 d z := by
          simp [Tiling.signedSide, Tiling.planarCross]
          ring
        rw [hside]
        constructor <;> intro h <;> linarith
      have hcase := hpositive p s (-d) hs hps (neg_ne_zero.mpr hd)
        hline' (-c) (by simpa only [hpoint] using hc) hgerm'
      simpa only [Bool.false_eq_true, ↓reduceIte, hflip] using hcase

private theorem sourceRay_nonvertexBoundaryInterval_edge
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (p d : Plane) (hdne : d ≠ 0)
    (hline : ∃ R > 0, ∀ c : ℝ, |c| < R →
      p + c • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
    (hpnot : p ∉ Tiling.RationalSlopes.translatedVertices K T)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ x ∈ openSegment ℝ e.1 e.2, x ∉ Tiling.vertexSet K.support) ∧
      ((∀ x ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) x) ∨
        (∀ x ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) x)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (positive : Bool) :
    ∃ s ∈ T, ∃ e ∈ E, p ∈ s +ᵥ openSegment ℝ e.1 e.2 ∧
      (if positive then positiveEdgeGerm (s +ᵥ K.support) d p
        else negativeEdgeGerm (s +ᵥ K.support) d p) ∧
      ∃ c : ℝ, c ≠ 0 ∧ e.2 - e.1 = c • d := by
  classical
  obtain ⟨sPos, hsPos, sNeg, hsNeg, hst, hpos, hneg⟩ := sourceNonvertexBoundaryInterval_oppositeLabelGerms K T htile p d hdne hline hpnot
  let s : Plane := if positive then sPos else sNeg
  have hs : s ∈ T := by cases positive <;> simp [s, hsPos, hsNeg]
  have hsgerm : if positive then positiveEdgeGerm (s +ᵥ K.support) d p
      else negativeEdgeGerm (s +ᵥ K.support) d p := by
    cases positive <;> simp [s, hpos, hneg]
  have hsgermOr : positiveEdgeGerm (s +ᵥ K.support) d p ∨
      negativeEdgeGerm (s +ᵥ K.support) d p := by
    cases positive with
    | false => exact Or.inr (by simpa [s] using hneg)
    | true => exact Or.inl (by simpa [s] using hpos)
  have hps : p ∈ s +ᵥ K.support := sourceRay_germ_mem _ _ _ hsgermOr
  have hpboundary : p ∈ ⋃ u : T, (u : Plane) +ᵥ frontier K.support := by
    obtain ⟨R, hR, hlineR⟩ := hline
    simpa only [zero_smul, add_zero] using hlineR 0 (by simpa using hR)
  have hpnotInterior : p ∉ interior (s +ᵥ K.support) := by
    simpa only [interior_vadd, PolygonalRegion.openCarrier] using
      Set.disjoint_left.mp (sourceBoundaryUnion_disjoint_openCarrier K T htile.2.1 s hs) hpboundary
  have hpfront : p ∈ frontier (s +ᵥ K.support) := by
    rw [(K.isPolygonal.isClosed.vadd s).frontier_eq]
    exact ⟨hps, hpnotInterior⟩
  have hxfront : -(s : Plane) + p ∈ frontier K.support := by
    have hfront : p ∈ (s : Plane) +ᵥ frontier K.support := by
      rw [sourceRay_link_frontier_vadd]
      exact hpfront
    exact Set.mem_vadd_set_iff_neg_vadd_mem.mp hfront
  have hxnotVertex : -(s : Plane) + p ∉ Tiling.vertexSet K.support := by
    intro hxv
    apply hpnot
    change p ∈ Tiling.vertexSet K.support + T
    apply Set.mem_add.mpr
    refine ⟨-(s : Plane) + p, hxv, s, hs, ?_⟩
    change -(s : Plane) + p + (s : Plane) = p
    abel
  rw [hcover] at hxfront
  obtain ⟨e, he, hxseg⟩ := Set.mem_iUnion₂.mp hxfront
  have hopen : -(s : Plane) + p ∈ openSegment ℝ e.1 e.2 := by
    rw [segment_eq_image_lineMap] at hxseg
    obtain ⟨u, hu, hxu⟩ := (Set.mem_image _ _ _).mp hxseg
    have hu0 : 0 < u := by
      by_contra hnot
      have huEq : u = 0 := le_antisymm (le_of_not_gt hnot) hu.1
      apply hxnotVertex
      rw [← hxu, huEq, AffineMap.lineMap_apply_zero]
      exact (hE e he).2.1
    have hu1 : u < 1 := by
      by_contra hnot
      have huEq : u = 1 := le_antisymm hu.2 (le_of_not_gt hnot)
      apply hxnotVertex
      rw [← hxu, huEq, AffineMap.lineMap_apply_one]
      exact (hE e he).2.2.1
    rw [openSegment_eq_image_lineMap]
    exact (Set.mem_image _ _ _).mpr ⟨u, ⟨hu0, hu1⟩, hxu⟩
  have hgermK : positiveEdgeGerm K.support d (-(s : Plane) + p) ∨
      negativeEdgeGerm K.support d (-(s : Plane) + p) := by
    cases positive with
    | false =>
        have h := sourceRay_vadd_negativeEdgeGerm (s +ᵥ K.support) (-(s : Plane)) p d
          (by simpa [s] using hneg)
        simpa [vadd_vadd] using (Or.inr h)
    | true =>
        have h := sourceRay_vadd_positiveEdgeGerm (s +ᵥ K.support) (-(s : Plane)) p d
          (by simpa [s] using hpos)
        simpa [vadd_vadd] using (Or.inl h)
  obtain ⟨c, hceq⟩ := sourceRay_edgeDirection_parallel
    K.isPolygonal.isClosed (hE e he).1 hxseg (hE e he).2.2.2.1 hdne hgermK
  have hcne : c ≠ 0 := by
    intro hczero
    have hzero : e.2 - e.1 = 0 := by simp [hceq, hczero]
    exact (hE e he).1 (sub_eq_zero.mp hzero).symm
  have hpopenTile : p ∈ s +ᵥ openSegment ℝ e.1 e.2 := by
    have hx : -(s : Plane) + p ∈ openSegment ℝ e.1 e.2 := hopen
    apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
    simpa [vadd_eq_add, add_comm] using hx
  exact ⟨s, hs, e, he, hpopenTile, hsgerm, c, hcne, hceq⟩

private theorem sourceRay_boundaryInterval_edgeEndpointParameters
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a d : Plane) (hdne : d ≠ 0)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ x ∈ openSegment ℝ e.1 e.2, x ∉ Tiling.vertexSet K.support) ∧
      ((∀ x ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) x) ∨
        (∀ x ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) x)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (r : ℝ) (hrnot : a + r • d ∉ Tiling.RationalSlopes.translatedVertices K T)
    (hline : ∃ R > 0, ∀ c : ℝ, |c| < R →
      (a + r • d) + c • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
    (positive : Bool) :
    ∃ s ∈ T, ∃ e ∈ E, ∃ c : ℝ, c ≠ 0 ∧ e.2 - e.1 = c • d ∧
      ∃ α β : ℝ,
        s + e.1 = a + α • d ∧ s + e.2 = a + β • d ∧
        β = α + c ∧ (r ∈ Ioo α β ∨ r ∈ Ioo β α) ∧
        (if positive then positiveEdgeGerm (s +ᵥ K.support) d (a + r • d)
          else negativeEdgeGerm (s +ᵥ K.support) d (a + r • d)) := by
  let p : Plane := a + r • d
  obtain ⟨s, hs, e, he, hopen, hgerm, c, hcne, hceq⟩ :=
    sourceRay_nonvertexBoundaryInterval_edge K T htile p d hdne hline hrnot
      E hE hcover positive
  have hopenX : - (s : Plane) + p ∈ openSegment ℝ e.1 e.2 :=
    Set.mem_vadd_set_iff_neg_vadd_mem.mp hopen
  rw [openSegment_eq_image_lineMap] at hopenX
  obtain ⟨u, hu, hxu⟩ := (Set.mem_image _ _ _).mp hopenX
  have hline : - (s : Plane) + p = e.1 + u • (e.2 - e.1) := by
    rw [← hxu]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hpcoord : p = s + e.1 + (u * c) • d := by
    calc
      p = (s : Plane) + (- (s : Plane) + p) := by abel
      _ = (s : Plane) + (e.1 + u • (e.2 - e.1)) := by rw [hline]
      _ = (s : Plane) + e.1 + (u * c) • d := by rw [hceq]; module
  have hleft : s + e.1 = a + (r - u * c) • d := by
    calc
      s + e.1 = p - (u * c) • d := by rw [hpcoord]; module
      _ = a + (r - u * c) • d := by
        dsimp [p]
        simp only [sub_eq_add_neg, smul_eq_mul]
        push_cast
        ring_nf
  have hright : s + e.2 = a + (r - u * c + c) • d := by
    calc
      s + e.2 = (s + e.1) + (e.2 - e.1) := by abel
      _ = (a + (r - u * c) • d) + c • d := by rw [hleft, hceq]
      _ = a + (r - u * c + c) • d := by module
  have hbetween : r ∈ Ioo (r - u * c) (r - u * c + c) ∨
      r ∈ Ioo (r - u * c + c) (r - u * c) := by
    by_cases hcpos : 0 < c
    · left
      constructor <;> nlinarith [mul_pos hu.1 hcpos,
        mul_pos (sub_pos.mpr hu.2) hcpos]
    · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hcne
      right
      constructor <;> nlinarith [mul_neg_of_pos_of_neg hu.1 hcneg,
        mul_neg_of_pos_of_neg (sub_pos.mpr hu.2) hcneg]
  exact ⟨s, hs, e, he, c, hcne, hceq, r - u * c, r - u * c + c,
    hleft, hright, rfl, hbetween, by simpa [p] using hgerm⟩

private theorem sourceRay_uniformEdgeGerms_scale
    {A : Set Plane} {s p x₀ d w x₁ x₂ : Plane} {c : ℝ}
    (hdne : d ≠ 0) (hcne : c ≠ 0) (hdir : w = c • d) (positive : Bool)
    (hx₀edge : x₀ ∈ openSegment ℝ x₁ x₂)
    (hx₀ : s + x₀ = p)
    (hproto : (∀ x ∈ openSegment ℝ x₁ x₂,
        positiveEdgeGerm A w x) ∨
      (∀ x ∈ openSegment ℝ x₁ x₂,
        negativeEdgeGerm A w x))
    (hselected : if positive then positiveEdgeGerm (s +ᵥ A) d p
      else negativeEdgeGerm (s +ᵥ A) d p) :
    ∀ x ∈ openSegment ℝ x₁ x₂,
      if positive then positiveEdgeGerm (s +ᵥ A) d (s + x)
      else negativeEdgeGerm (s +ᵥ A) d (s + x) := by
  rcases hproto with hproto | hproto
  · rcases lt_or_gt_of_ne hcne.symm with hcpos | hcneg
    · have hpositive := sourceRay_positiveGerm_scale_pos hcpos hdir
        (by simpa [vadd_eq_add, hx₀] using
          sourceRay_vadd_positiveEdgeGerm A s x₀ w (hproto x₀ hx₀edge))
      cases positive
      · have hneg : negativeEdgeGerm (s +ᵥ A) d p := by simpa using hselected
        exact False.elim (positive_negative_edgeGerms_disjoint hdne hpositive hneg)
      · intro x hx
        exact sourceRay_positiveGerm_scale_pos hcpos hdir
          (by simpa [vadd_eq_add] using sourceRay_vadd_positiveEdgeGerm A s x w (hproto x hx))
    · have hnegative := sourceRay_positiveGerm_scale_neg hcneg hdir
        (by simpa [vadd_eq_add, hx₀] using
          sourceRay_vadd_positiveEdgeGerm A s x₀ w (hproto x₀ hx₀edge))
      cases positive
      · intro x hx
        exact sourceRay_positiveGerm_scale_neg hcneg hdir
          (by simpa [vadd_eq_add] using sourceRay_vadd_positiveEdgeGerm A s x w (hproto x hx))
      · have hpos : positiveEdgeGerm (s +ᵥ A) d p := by simpa using hselected
        exact False.elim (positive_negative_edgeGerms_disjoint hdne hpos hnegative)
  · rcases lt_or_gt_of_ne hcne.symm with hcpos | hcneg
    · have hnegative := sourceRay_negativeGerm_scale_pos hcpos hdir
        (by simpa [vadd_eq_add, hx₀] using
          sourceRay_vadd_negativeEdgeGerm A s x₀ w (hproto x₀ hx₀edge))
      cases positive
      · intro x hx
        exact sourceRay_negativeGerm_scale_pos hcpos hdir
          (by simpa [vadd_eq_add] using sourceRay_vadd_negativeEdgeGerm A s x w (hproto x hx))
      · have hpos : positiveEdgeGerm (s +ᵥ A) d p := by simpa using hselected
        exact False.elim (positive_negative_edgeGerms_disjoint hdne hpos hnegative)
    · have hpositive := sourceRay_negativeGerm_scale_neg hcneg hdir
        (by simpa [vadd_eq_add, hx₀] using
          sourceRay_vadd_negativeEdgeGerm A s x₀ w (hproto x₀ hx₀edge))
      cases positive
      · have hneg : negativeEdgeGerm (s +ᵥ A) d p := by simpa using hselected
        exact False.elim (positive_negative_edgeGerms_disjoint hdne hpositive hneg)
      · intro x hx
        exact sourceRay_negativeGerm_scale_neg hcneg hdir
          (by simpa [vadd_eq_add] using sourceRay_vadd_negativeEdgeGerm A s x w (hproto x hx))

private theorem sourceRay_signedCarrierIntervals_boundaryInterval_cover
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a d : Plane) (hdne : d ≠ 0)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ x ∈ openSegment ℝ e.1 e.2, x ∉ Tiling.vertexSet K.support) ∧
      ((∀ x ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) x) ∨
        (∀ x ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) x)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (r : ℝ) (hrnot : a + r • d ∉ Tiling.RationalSlopes.translatedVertices K T)
    (hline : ∃ R > 0, ∀ c : ℝ, |c| < R →
      (a + r • d) + c • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
    (positive : Bool) :
    ∃ q ∈ signedCarrierIntervals K T E a d positive, r ∈ Icc q.1 q.2 := by
  classical
  obtain ⟨s, hs, e, he, c, hcne, hceq, α, β, hleft, hright, hβ, hbetween,
      hgerm⟩ := sourceRay_boundaryInterval_edgeEndpointParameters K T htile a d hdne
        E hE hcover r hrnot hline positive
  have hcpos : 0 < c ∨ c < 0 := lt_or_gt_of_ne hcne.symm
  rcases hcpos with hcpos | hcneg
  · refine ⟨(α, β), ?_, ?_⟩
    · change α < β ∧ _
      refine ⟨by rw [hβ]; linarith, s, hs, e, he, Or.inl ⟨hleft, hright⟩, ?_⟩
      intro ρ hρ
      change ρ ∈ Ioo α β at hρ
      have hcarrier := carrierParameter_mem_openSegment a d α β ρ
        (by rw [hβ]; linarith) hρ
      rw [openSegment_eq_image_lineMap] at hcarrier
      obtain ⟨u, hu, hparam⟩ := hcarrier
      have hx : -(s : Plane) + (a + ρ • d) ∈ openSegment ℝ e.1 e.2 := by
        rw [openSegment_eq_image_lineMap]
        refine (Set.mem_image _ _ _).mpr ⟨u, hu, ?_⟩
        calc
          AffineMap.lineMap e.1 e.2 u =
              - (s : Plane) + AffineMap.lineMap (a + α • d) (a + β • d) u := by
                simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
                rw [← hleft, ← hright]
                module
          _ = -(s : Plane) + (a + ρ • d) := by rw [hparam]
      rcases hE e he with ⟨_, _, _, _, _, hproto⟩
      have hpointEdge : -(s : Plane) + (a + r • d) ∈ openSegment ℝ e.1 e.2 := by
        have hcarrier₀ := carrierParameter_mem_openSegment a d α β r
          (by rw [hβ]; linarith) (by
            rcases hbetween with h | h
            · exact h
            · exfalso
              have : α < β := by rw [hβ]; linarith
              linarith [h.1, h.2])
        rw [openSegment_eq_image_lineMap] at hcarrier₀
        obtain ⟨u₀, hu₀, hparam₀⟩ := hcarrier₀
        rw [openSegment_eq_image_lineMap]
        refine (Set.mem_image _ _ _).mpr ⟨u₀, hu₀, ?_⟩
        calc
          AffineMap.lineMap e.1 e.2 u₀ =
              -(s : Plane) + AffineMap.lineMap (a + α • d) (a + β • d) u₀ := by
                simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
                rw [← hleft, ← hright]
                module
          _ = -(s : Plane) + (a + r • d) := by rw [hparam₀]
      have hall : ∀ x ∈ openSegment ℝ e.1 e.2,
          (if positive then positiveEdgeGerm (s +ᵥ K.support) d (s + x)
            else negativeEdgeGerm (s +ᵥ K.support) d (s + x)) := by
        rcases hproto with hproto | hproto
        · exact sourceRay_uniformEdgeGerms_scale hdne hcne hceq positive
            hpointEdge (by dsimp; abel) (Or.inl hproto) hgerm
        · exact sourceRay_uniformEdgeGerms_scale hdne hcne hceq positive
            hpointEdge (by dsimp; abel) (Or.inr hproto) hgerm
      simpa only [vadd_eq_add, add_neg_cancel_left] using hall _ hx
    · rcases hbetween with hbetween | hbetween
      · exact ⟨le_of_lt hbetween.1, le_of_lt hbetween.2⟩

      · exfalso
        exact (not_lt_of_ge (le_of_lt hcpos)) (by linarith [hβ, hbetween.1, hbetween.2])
  · refine ⟨(β, α), ?_, ?_⟩
    · change β < α ∧ _
      refine ⟨by rw [hβ]; linarith, s, hs, e, he, Or.inr ⟨hright, hleft⟩, ?_⟩
      intro ρ hρ
      change ρ ∈ Ioo β α at hρ
      have hcarrier := carrierParameter_mem_openSegment a d β α ρ
        (by rw [hβ]; linarith) hρ
      rw [openSegment_eq_image_lineMap] at hcarrier
      obtain ⟨u, hu, hparam⟩ := hcarrier
      have hx : -(s : Plane) + (a + ρ • d) ∈ openSegment ℝ e.1 e.2 := by
        rw [openSegment_eq_image_lineMap]
        refine (Set.mem_image _ _ _).mpr ⟨1 - u, ?_, ?_⟩
        · constructor
          · nlinarith [hu.2]
          · nlinarith [hu.1]
        · calc
          AffineMap.lineMap e.1 e.2 (1 - u) =
              -(s : Plane) + AffineMap.lineMap (a + β • d) (a + α • d) u := by
                simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
                rw [← hright, ← hleft]
                module
          _ = -(s : Plane) + (a + ρ • d) := by rw [hparam]
      rcases hE e he with ⟨_, _, _, _, _, hproto⟩
      have hpointEdge : -(s : Plane) + (a + r • d) ∈ openSegment ℝ e.1 e.2 := by
        have hcarrier₀ := carrierParameter_mem_openSegment a d β α r
          (by rw [hβ]; linarith) (by
            rcases hbetween with h | h
            · exfalso
              have : β < α := by rw [hβ]; linarith
              linarith [h.1, h.2]
            · exact h)
        rw [openSegment_eq_image_lineMap] at hcarrier₀
        obtain ⟨u₀, hu₀, hparam₀⟩ := hcarrier₀
        rw [openSegment_eq_image_lineMap]
        refine (Set.mem_image _ _ _).mpr ⟨1 - u₀, ?_, ?_⟩
        · constructor
          · nlinarith [hu₀.2]
          · nlinarith [hu₀.1]
        · calc
          AffineMap.lineMap e.1 e.2 (1 - u₀) =
              -(s : Plane) + AffineMap.lineMap (a + β • d) (a + α • d) u₀ := by
                simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
                rw [← hright, ← hleft]
                module
          _ = -(s : Plane) + (a + r • d) := by rw [hparam₀]
      have hall : ∀ x ∈ openSegment ℝ e.1 e.2,
          (if positive then positiveEdgeGerm (s +ᵥ K.support) d (s + x)
            else negativeEdgeGerm (s +ᵥ K.support) d (s + x)) := by
        rcases hproto with hproto | hproto
        · exact sourceRay_uniformEdgeGerms_scale hdne hcne hceq positive
            hpointEdge (by dsimp; abel) (Or.inl hproto) hgerm
        · exact sourceRay_uniformEdgeGerms_scale hdne hcne hceq positive
            hpointEdge (by dsimp; abel) (Or.inr hproto) hgerm
      simpa only [vadd_eq_add, add_neg_cancel_left] using hall _ hx
    · rcases hbetween with hbetween | hbetween
      · exfalso
        exact (not_lt_of_ge (le_of_lt hcneg)) (by linarith [hβ, hbetween.1, hbetween.2])
      · exact ⟨le_of_lt hbetween.1, le_of_lt hbetween.2⟩

private theorem sourceRay_signedCarrierIntervals_fullProper_cover
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (δ : Submodule ℝ Plane) (a d : Plane) (hd : d ∈ δ) (hdne : d ≠ 0)
    (hproper : Tiling.RationalSlopes.IsProperLink K δ T a)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ x ∈ openSegment ℝ e.1 e.2, x ∉ Tiling.vertexSet K.support) ∧
      ((∀ x ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) x) ∨
        (∀ x ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) x)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (r : ℝ) (hrnot : a + r • d ∉ Tiling.RationalSlopes.translatedVertices K T)
    (positive : Bool) :
    ∃ q ∈ signedCarrierIntervals K T E a d positive, r ∈ Icc q.1 q.2 := by
  let p : Plane := a + r • d
  have hpa : p ∈ a +ᵥ (δ : Set Plane) := by
    apply Set.mem_vadd_set.mpr
    refine ⟨r • d, δ.smul_mem r hd, ?_⟩
    dsimp [p]
  have hline : ∃ R > 0, ∀ c : ℝ, |c| < R →
      p + c • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support := by
    refine ⟨1, by norm_num, ?_⟩
    intro c hc
    exact hproper (sourceRay_properLine_scale δ a p d hpa hd c)
  exact sourceRay_signedCarrierIntervals_boundaryInterval_cover K T htile a d hdne E hE
    hcover r hrnot (by simpa [p] using hline) positive

/-- The actual full-link signed occurrence family covers the whole source
carrier; source LF supplies its vertex endpoints after genuine nonvertex
ownership has been constructed. -/
private theorem signedCarrierIntervals_fullProper_closedCover
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (δ : Submodule ℝ Plane) (a d : Plane) (hd : d ∈ δ) (hdne : d ≠ 0)
    (hproper : Tiling.RationalSlopes.IsProperLink K δ T a)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ x ∈ openSegment ℝ e.1 e.2, x ∉ Tiling.vertexSet K.support) ∧
      ((∀ x ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) x) ∨
        (∀ x ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) x)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) (positive : Bool) :
    ⋃ q : signedCarrierIntervals K T E a d positive, Icc q.1.1 q.1.2 = Set.univ := by
  apply signedCarrierIntervals_cover_fromNonvertices K T htile.2.1 E
    (fun e he => ⟨(hE e he).2.1, (hE e he).2.2.1⟩) a d hdne positive
  intro r hrnot
  exact sourceRay_signedCarrierIntervals_fullProper_cover
    K T htile δ a d hd hdne hproper E hE hcover r hrnot positive

/-- BOTH source sign families cover the SAME nondegenerate maximal boundary
component.  All local ownership, interval inclusion and closure facts are
derived here from actual source tiling and genuine primitive occurrences. -/
private theorem signedCarrierComponentIntervals_closedCover
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ x ∈ openSegment ℝ e.1 e.2, x ∉ Tiling.vertexSet K.support) ∧
      ((∀ x ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) x) ∨
        (∀ x ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) x)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (a d : Plane) (hdne : d ≠ 0) (r l u : ℝ)
    (hr : a + r • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
    (hlu : l < u)
    (hinterval : Icc l u ⊆ connectedComponentIn
      {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r)
    (positive : Bool) :
    ⋃ q : signedCarrierComponentIntervals K T E a d r positive, Icc q.1.1 q.1.2 =
      connectedComponentIn
        {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r := by
  let B : Set ℝ := {s | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support}
  let J : Set ℝ := connectedComponentIn B r
  let U : Set ℝ := ⋃ q : signedCarrierComponentIntervals K T E a d r positive,
    Icc q.1.1 q.1.2
  let V : Set ℝ := {s | a + s • d ∈ Tiling.RationalSlopes.translatedVertices K T}
  have hB : IsClosed B := sourceBoundaryParameters_isClosed K T htile.2.1 a d
  have hJclosure : closure (interior J) = J :=
    scalarClosedComponent_closure_interior B hB hr hlu hinterval
  have hU : IsClosed U := signedCarrierComponentIntervals_closedUnion K T htile.2.1 E
    (fun e he => ⟨(hE e he).2.1, (hE e he).2.2.1⟩) a d hdne r positive
  have hpoint : interior J ∩ Vᶜ ⊆ U := by
    intro s hs
    obtain ⟨q, hq, hsq⟩ := sourceRay_signedCarrierIntervals_boundaryInterval_cover
      K T htile a d hdne E hE hcover s hs.2
      (sourceBoundaryComponent_localInterval K T a d r hs.1) positive
    have hqJ : Icc q.1 q.2 ⊆ J :=
      signedCarrierInterval_subset_component_of_meets K T E
        (fun e he => (hE e he).2.2.2.1) a d positive hr hq
        ⟨s, hsq, interior_subset hs.1⟩
    exact Set.mem_iUnion.mpr ⟨⟨q, hq, hqJ⟩, hsq⟩
  have hdense : Dense Vᶜ := scalarLocallyFinite_complement_dense V
    (sourceCarrierVertices_scalarLocallyFinite K T htile.2.1 a d hdne)
  have hinterior : interior J ⊆ U :=
    (hdense.open_subset_closure_inter isOpen_interior).trans
      (hU.closure_subset_iff.mpr hpoint)
  apply Set.Subset.antisymm
  · intro s hs
    obtain ⟨q, hsq⟩ := Set.mem_iUnion.mp hs
    exact q.2.2 hsq
  · intro s hs
    apply hU.closure_subset_iff.mpr hinterior
    rwa [hJclosure]

private theorem carrierEndpoint_notInterior
    (V : Set Plane) (a d t p : Plane) (alpha lo hi : ℝ) (f : Plane × Plane)
    (hlohi : lo < hi) (hinside : alpha ∈ Ioo lo hi)
    (hpeq : t + p = a + alpha • d) (hpv : p ∈ V)
    (hfcoords : (f.1 = (a - t) + lo • d ∧ f.2 = (a - t) + hi • d) ∨
      (f.2 = (a - t) + lo • d ∧ f.1 = (a - t) + hi • d))
    (hfree : ∀ z ∈ openSegment ℝ f.1 f.2, z ∉ V) : False := by
  have hp : p = (a - t) + alpha • d := by
    calc
      p = (t + p) - t := by abel
      _ = (a + alpha • d) - t := by rw [hpeq]
      _ = (a - t) + alpha • d := by abel
  have hseg : (a - t) + alpha • d ∈ openSegment ℝ f.1 f.2 := by
    rcases hfcoords with ⟨h1, h2⟩ | ⟨h2, h1⟩
    · rw [h1, h2]
      exact carrierParameter_mem_openSegment (a - t) d lo hi alpha hlohi hinside
    · rw [h1, h2, openSegment_symm]
      exact carrierParameter_mem_openSegment (a - t) d lo hi alpha hlohi hinside
  exact hfree p (hp ▸ hseg) hpv

private theorem signedCarrierIntervals_sameSide_disjoint
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (E : Finset (Plane × Plane))
    (hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧
      e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support ∧
      ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet K.support)
    (a d : Plane) (hd : d ≠ 0) (positive : Bool) :
    ∀ q ∈ signedCarrierIntervals K T E a d positive,
      ∀ r ∈ signedCarrierIntervals K T E a d positive, q ≠ r →
        Disjoint (Ioo q.1 q.2) (Ioo r.1 r.2) := by
  classical
  intro q hq r hr hne
  apply Set.disjoint_left.mpr
  intro x hxq hxr
  obtain ⟨hqord, s, hs, e, he, hqcoords, hqgerm⟩ := hq
  obtain ⟨hrord, t, ht, f, hf, hrcoords, hrgerm⟩ := hr
  have hlabels : s = t := by
    by_cases hp : positive
    · exact originalSamePositiveEdgeGerm_label_unique K T hpack s t (a + x • d) d hs ht hd
        (by simpa [hp] using hqgerm x hxq) (by simpa [hp] using hrgerm x hxr)
    · exact originalSameNegativeEdgeGerm_label_unique K T hpack s t (a + x • d) d hs ht hd
        (by simpa [hp] using hqgerm x hxq) (by simpa [hp] using hrgerm x hxr)
  subst t
  have hvertsE := hprimitive e he
  have hvertsF := hprimitive f hf
  have hqc : (e.1 = (a - s) + q.1 • d ∧ e.2 = (a - s) + q.2 • d) ∨
      (e.2 = (a - s) + q.1 • d ∧ e.1 = (a - s) + q.2 • d) := by
    have subLeft {z : Plane} (h : s + z = a + q.1 • d) :
        z = (a - s) + q.1 • d := by
      calc
        z = (s + z) - s := by abel
        _ = (a + q.1 • d) - s := by rw [h]
        _ = (a - s) + q.1 • d := by abel
    have subRight {z : Plane} (h : s + z = a + q.2 • d) :
        z = (a - s) + q.2 • d := by
      calc
        z = (s + z) - s := by abel
        _ = (a + q.2 • d) - s := by rw [h]
        _ = (a - s) + q.2 • d := by abel
    rcases hqcoords with ⟨h1, h2⟩ | ⟨h2, h1⟩
    · exact Or.inl ⟨subLeft h1, subRight h2⟩
    · exact Or.inr ⟨subLeft h2, subRight h1⟩
  have hfc : (f.1 = (a - s) + r.1 • d ∧ f.2 = (a - s) + r.2 • d) ∨
      (f.2 = (a - s) + r.1 • d ∧ f.1 = (a - s) + r.2 • d) := by
    have subLeft {z : Plane} (h : s + z = a + r.1 • d) :
        z = (a - s) + r.1 • d := by
      calc
        z = (s + z) - s := by abel
        _ = (a + r.1 • d) - s := by rw [h]
        _ = (a - s) + r.1 • d := by abel
    have subRight {z : Plane} (h : s + z = a + r.2 • d) :
        z = (a - s) + r.2 • d := by
      calc
        z = (s + z) - s := by abel
        _ = (a + r.2 • d) - s := by rw [h]
        _ = (a - s) + r.2 • d := by abel
    rcases hrcoords with ⟨h1, h2⟩ | ⟨h2, h1⟩
    · exact Or.inl ⟨subLeft h1, subRight h2⟩
    · exact Or.inr ⟨subLeft h2, subRight h1⟩
  have hnotLeft : q.1 ∉ Ioo r.1 r.2 := by
    intro hinside
    rcases hqcoords with ⟨h1, h2⟩ | ⟨h2, h1⟩
    · exact carrierEndpoint_notInterior (Tiling.vertexSet K.support) a d s e.1 q.1 r.1 r.2 f
        hrord hinside h1 hvertsE.2.1 hfc hvertsF.2.2.2
    · exact carrierEndpoint_notInterior (Tiling.vertexSet K.support) a d s e.2 q.1 r.1 r.2 f
        hrord hinside h2 hvertsE.2.2.1 hfc hvertsF.2.2.2
  have hnotRight : q.2 ∉ Ioo r.1 r.2 := by
    intro hinside
    rcases hqcoords with ⟨h1, h2⟩ | ⟨h2, h1⟩
    · exact carrierEndpoint_notInterior (Tiling.vertexSet K.support) a d s e.2 q.2 r.1 r.2 f
        hrord hinside h2 hvertsE.2.2.1 hfc hvertsF.2.2.2
    · exact carrierEndpoint_notInterior (Tiling.vertexSet K.support) a d s e.1 q.2 r.1 r.2 f
        hrord hinside h1 hvertsE.2.1 hfc hvertsF.2.2.2
  have hnotLeft' : r.1 ∉ Ioo q.1 q.2 := by
    intro hinside
    rcases hrcoords with ⟨h1, h2⟩ | ⟨h2, h1⟩
    · exact carrierEndpoint_notInterior (Tiling.vertexSet K.support) a d s f.1 r.1 q.1 q.2 e
        hqord hinside h1 hvertsF.2.1 hqc hvertsE.2.2.2
    · exact carrierEndpoint_notInterior (Tiling.vertexSet K.support) a d s f.2 r.1 q.1 q.2 e
        hqord hinside h2 hvertsF.2.2.1 hqc hvertsE.2.2.2
  have hnotRight' : r.2 ∉ Ioo q.1 q.2 := by
    intro hinside
    rcases hrcoords with ⟨h1, h2⟩ | ⟨h2, h1⟩
    · exact carrierEndpoint_notInterior (Tiling.vertexSet K.support) a d s f.2 r.2 q.1 q.2 e
        hqord hinside h2 hvertsF.2.2.1 hqc hvertsE.2.2.2
    · exact carrierEndpoint_notInterior (Tiling.vertexSet K.support) a d s f.1 r.2 q.1 q.2 e
        hqord hinside h1 hvertsF.2.1 hqc hvertsE.2.2.2
  have hleft : q.1 = r.1 := by
    rcases lt_trichotomy q.1 r.1 with h | h | h
    · have : r.1 ∈ Ioo q.1 q.2 := ⟨h, lt_trans hxr.1 hxq.2⟩
      exact False.elim (hnotLeft' this)
    · exact h
    · have : q.1 ∈ Ioo r.1 r.2 := ⟨h, lt_trans hxq.1 hxr.2⟩
      exact False.elim (hnotLeft this)
  have hright : q.2 = r.2 := by
    rcases lt_trichotomy q.2 r.2 with h | h | h
    · have : q.2 ∈ Ioo r.1 r.2 := ⟨lt_trans hxr.1 hxq.2, h⟩
      exact False.elim (hnotRight this)
    · exact h
    · have : r.2 ∈ Ioo q.1 q.2 := ⟨lt_trans hxq.1 hxr.2, h⟩
      exact False.elim (hnotRight' this)
  exact hne (Prod.ext hleft hright)

private theorem packingSol_consecutiveEdge_onSourceCarrier
    (E : Set (ℝ × ℝ)) (J : Set ℝ) (hJ : J.OrdConnected)
    (hendpoint : scalarIntervalEndpoints E ⊆ J)
    (hpositive : ∀ e ∈ E, e.1 < e.2)
    (hdisjoint : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (Ioo e.1 e.2) (Ioo f.1 f.2))
    (hcover : ∀ x ∈ J, ∃ e ∈ E, x ∈ Icc e.1 e.2)
    (a b : ℝ) (ha : a ∈ scalarIntervalEndpoints E) (hb : b ∈ scalarIntervalEndpoints E)
    (hab : a < b)
    (hconsecutive : ∀ x ∈ scalarIntervalEndpoints E, ¬ (a < x ∧ x < b)) :
    (a, b) ∈ E := by
  let x : ℝ := (a + b) / 2
  have hax : a < x := by dsimp [x]; linarith
  have hxb : x < b := by dsimp [x]; linarith
  have hxnot : x ∉ scalarIntervalEndpoints E := fun hx => hconsecutive x hx ⟨hax, hxb⟩
  obtain ⟨e, he, hxedge⟩ := hcover x (hJ.out (hendpoint ha) (hendpoint hb) ⟨hax.le, hxb.le⟩)
  have hlo : e.1 ∈ scalarIntervalEndpoints E := ⟨e, he, Or.inl rfl⟩
  have hhi : e.2 ∈ scalarIntervalEndpoints E := ⟨e, he, Or.inr rfl⟩
  have hlox : e.1 < x := by
    by_contra h
    have hxeq : x = e.1 := le_antisymm (le_of_not_gt h) hxedge.1
    exact hxnot (hxeq ▸ hlo)
  have hxhi : x < e.2 := by
    by_contra h
    have hxeq : x = e.2 := le_antisymm hxedge.2 (le_of_not_gt h)
    exact hxnot (hxeq ▸ hhi)
  have hloa : e.1 ≤ a := by
    by_contra h
    exact hconsecutive e.1 hlo ⟨lt_of_not_ge h, hlox.trans hxb⟩
  have hbhi : b ≤ e.2 := by
    by_contra h
    exact hconsecutive e.2 hhi ⟨hax.trans hxhi, lt_of_not_ge h⟩
  have halo : a ≤ e.1 := by
    by_contra h
    exact scalarIntervalFamily_endpoint_notInterior E hpositive hdisjoint e he a ha
      ⟨lt_of_not_ge h, hax.trans hxhi⟩
  have hhib : e.2 ≤ b := by
    by_contra h
    exact scalarIntervalFamily_endpoint_notInterior E hpositive hdisjoint e he b hb
      ⟨hlox.trans hxb, lt_of_not_ge h⟩
  have he1 : e.1 = a := le_antisymm hloa halo
  have he2 : e.2 = b := le_antisymm hhib hbhi
  have heq : e = (a, b) := Prod.ext he1 he2
  rwa [heq] at he

private theorem packingSol_sourceCarrier_terminalEndpoints
    (A : Set (ℝ × ℝ)) (J : Set ℝ)
    (hinside : ∀ q ∈ A, Icc q.1 q.2 ⊆ J)
    (hpositive : ∀ q ∈ A, q.1 < q.2)
    (hcover : ∀ x ∈ J, ∃ q ∈ A, x ∈ Icc q.1 q.2) :
    (∀ lo ∈ J, (∀ x ∈ J, lo ≤ x) → lo ∈ scalarIntervalEndpoints A) ∧
      (∀ hi ∈ J, (∀ x ∈ J, x ≤ hi) → hi ∈ scalarIntervalEndpoints A) := by
  constructor
  · intro lo hlo hminimal
    obtain ⟨q, hq, hlow, hhigh⟩ := hcover lo hlo
    have hleft : q.1 ∈ J := hinside q hq ⟨le_rfl, (hpositive q hq).le⟩
    have heq : lo = q.1 := le_antisymm (hminimal q.1 hleft) hlow
    exact ⟨q, hq, Or.inl heq⟩
  · intro hi hhi hmaximal
    obtain ⟨q, hq, hlow, hhigh⟩ := hcover hi hhi
    have hright : q.2 ∈ J := hinside q hq ⟨(hpositive q hq).le, le_rfl⟩
    have heq : hi = q.2 := le_antisymm hhigh (hmaximal q.2 hright)
    exact ⟨q, hq, Or.inr heq⟩

private theorem packingSol_uniformScalarEndpointControl (D : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation D ε φ →
      ∀ S : Set ℝ,
        (∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite) →
        (∀ a ∈ S, ∀ b ∈ S, a < b → S ∩ Ioo a b = ∅ → b - a ∈ D) →
        ∀ a ∈ S, ∀ b ∈ S, a < b →
          (b - a) / 2 ≤ (φ b : ℝ) - (φ a : ℝ) ∧
            (φ b : ℝ) - (φ a : ℝ) ≤ 2 * (b - a) := by
  obtain ⟨ε, hε, hcontrol⟩ := finite_positive_deformation_bounds D
  refine ⟨ε, hε, ?_⟩
  intro φ hφ S hlocal hgap a ha b hb hab
  obtain ⟨G, _, hG, hsum⟩ :=
    scalarChain_consecutiveGapWord S D hlocal hgap a ha b hb hab
  have hbnd := list_sum_deformation_bounds φ G
    (fun r hr => hcontrol φ hφ r (hG r hr).2 (hG r hr).1)
  have hmap : (φ (b - a) : ℝ) = (φ b : ℝ) - (φ a : ℝ) := by
    exact_mod_cast φ.map_sub b a
  rw [← hsum] at hbnd
  rwa [hmap] at hbnd

private theorem packingSol_endpointImageLF_of_lowerControl
    (S : Set ℝ) (φ : ℝ →ₗ[ℚ] ℚ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite)
    (hcontrol : ∀ a ∈ S, ∀ b ∈ S, a < b →
      (b - a) / 2 ≤ (φ b : ℝ) - (φ a : ℝ)) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (((fun r : ℝ => (φ r : ℝ)) '' S) ∩ Q).Finite := by
  intro Q hQ
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha⟩ := hS
    obtain ⟨B, _, hQB⟩ := hQ.exists_pos_norm_le
    let R := 2 * (B + |(φ a : ℝ)|)
    have hfinite := hlocal (Metric.closedBall a R) Metric.isBounded_closedBall
    apply (hfinite.image (fun r : ℝ => (φ r : ℝ))).subset
    rintro y ⟨⟨x, hx, rfl⟩, hyQ⟩
    have habs : |x - a| / 2 ≤ |(φ x : ℝ) - (φ a : ℝ)| := by
      rcases lt_trichotomy a x with hax | rfl | hxa
      · have hb := hcontrol a ha x hx hax
        have hpos : 0 < (φ x : ℝ) - (φ a : ℝ) := by linarith
        simpa only [abs_of_pos (sub_pos.mpr hax), abs_of_pos hpos] using hb
      · simp
      · have hb := hcontrol x hx a ha hxa
        have hpos : 0 < (φ a : ℝ) - (φ x : ℝ) := by linarith
        rw [abs_sub_comm x a, abs_sub_comm (φ x : ℝ) (φ a : ℝ)]
        simpa only [abs_of_pos (sub_pos.mpr hxa), abs_of_pos hpos] using hb
    have htargetBound : |(φ x : ℝ) - (φ a : ℝ)| ≤ B + |(φ a : ℝ)| := by
      have hxbound : |(φ x : ℝ)| ≤ B := by
        simpa only [Real.norm_eq_abs] using hQB _ hyQ
      exact (abs_sub _ _).trans (add_le_add hxbound le_rfl)
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    change dist x a ≤ R
    rw [Real.dist_eq]
    dsimp only [R]
    linarith
  · have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    simp [hempty]

private theorem packingSol_endpointSpan_of_control
    (A : Set (ℝ × ℝ)) (J : Set ℝ) (φ : ℝ →ₗ[ℚ] ℚ)
    (hJ : J.OrdConnected)
    (hendpoint : scalarIntervalEndpoints A ⊆ J)
    (hpositive : ∀ q ∈ A, q.1 < q.2)
    (hdisjoint : ∀ q ∈ A, ∀ s ∈ A, q ≠ s →
      Disjoint (Ioo q.1 q.2) (Ioo s.1 s.2))
    (hcover : ∀ x ∈ J, ∃ q ∈ A, x ∈ Icc q.1 q.2)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (scalarIntervalEndpoints A ∩ Q).Finite)
    (hcontrol : ∀ a ∈ scalarIntervalEndpoints A, ∀ b ∈ scalarIntervalEndpoints A,
      a < b → (b - a) / 2 ≤ (φ b : ℝ) - (φ a : ℝ)) :
    ∀ lo ∈ scalarIntervalEndpoints A, ∀ hi ∈ scalarIntervalEndpoints A,
      ∀ x ∈ Icc (φ lo : ℝ) (φ hi : ℝ),
        ∃ q ∈ A, x ∈ Icc (φ q.1 : ℝ) (φ q.2 : ℝ) := by
  let S := scalarIntervalEndpoints A
  have hLF := packingSol_endpointImageLF_of_lowerControl S φ hlocal hcontrol
  have hmono : ∀ a ∈ S, ∀ b ∈ S, a < b → (φ a : ℝ) < (φ b : ℝ) := by
    intro a ha b hb hab
    have h := hcontrol a ha b hb hab
    linarith
  have hweak : ∀ a ∈ S, ∀ b ∈ S, a ≤ b → (φ a : ℝ) ≤ (φ b : ℝ) := by
    intro a ha b hb hab
    rcases lt_or_eq_of_le hab with hab | rfl
    · exact (hmono a ha b hb hab).le
    · exact le_rfl
  intro lo hlo hi hhi x hx
  by_cases htop : x = (φ hi : ℝ)
  · obtain ⟨q, hq, hlow, hhigh⟩ := hcover hi (hendpoint hhi)
    refine ⟨q, hq, ?_⟩
    rw [htop]
    exact ⟨hweak q.1 ⟨q, hq, Or.inl rfl⟩ hi hhi hlow,
      hweak hi hhi q.2 ⟨q, hq, Or.inr rfl⟩ hhigh⟩
  · have hxh : x < (φ hi : ℝ) := lt_of_le_of_ne hx.2 htop
    let Y : Set ℝ := (fun r : ℝ => (φ r : ℝ)) '' S
    obtain ⟨a', ha', b', hb', hab', hax, hxb, hconsecutive⟩ :=
      scalarSet_consecutive_enclosing Y hLF (φ lo : ℝ) (φ hi : ℝ) x
        ⟨lo, hlo, rfl⟩ ⟨hi, hhi, rfl⟩ hx.1 hxh
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨b, hb, rfl⟩ := hb'
    have hab : a < b := by
      by_contra h
      rcases lt_or_eq_of_le (le_of_not_gt h) with hba | hba
      · exact (not_lt_of_gt (hmono b hb a ha hba)) hab'
      · simp only [hba, lt_self_iff_false] at hab'
    have habA : (a, b) ∈ A := by
      apply packingSol_consecutiveEdge_onSourceCarrier A J hJ hendpoint
        hpositive hdisjoint hcover a b ha hb hab
      intro s hs hbetween
      have hsY : (φ s : ℝ) ∈ Y ∩ Ioo (φ a : ℝ) (φ b : ℝ) :=
        ⟨⟨s, hs, rfl⟩, hmono a ha s hs hbetween.1, hmono s hs b hb hbetween.2⟩
      rw [hconsecutive] at hsY
      exact hsY
    exact ⟨(a, b), habA, hax, hxb⟩

private theorem packingSol_carrierCases_of_control
    (A : Set (ℝ × ℝ)) (J : Set ℝ) (φ : ℝ →ₗ[ℚ] ℚ)
    (hJ : J.OrdConnected)
    (hinside : ∀ q ∈ A, Icc q.1 q.2 ⊆ J)
    (hpositive : ∀ q ∈ A, q.1 < q.2)
    (hdisjoint : ∀ q ∈ A, ∀ s ∈ A, q ≠ s →
      Disjoint (Ioo q.1 q.2) (Ioo s.1 s.2))
    (hcover : ∀ x ∈ J, ∃ q ∈ A, x ∈ Icc q.1 q.2)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (scalarIntervalEndpoints A ∩ Q).Finite)
    (hcontrol : ∀ a ∈ scalarIntervalEndpoints A, ∀ b ∈ scalarIntervalEndpoints A,
      a < b → (b - a) / 2 ≤ (φ b : ℝ) - (φ a : ℝ)) :
    (∀ lo hi : ℝ, lo < hi → J = Icc lo hi →
      (⋃ q : A, Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ)) = Icc (φ lo : ℝ) (φ hi : ℝ)) ∧
    (∀ lo : ℝ, J = Ici lo →
      (⋃ q : A, Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ)) = Ici (φ lo : ℝ)) ∧
    (∀ hi : ℝ, J = Iic hi →
      (⋃ q : A, Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ)) = Iic (φ hi : ℝ)) ∧
    (J = Set.univ → (⋃ q : A, Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ)) = Set.univ) := by
  let S := scalarIntervalEndpoints A
  have hendpoint : S ⊆ J := by
    rintro x ⟨q, hq, rfl | rfl⟩
    · exact hinside q hq ⟨le_rfl, (hpositive q hq).le⟩
    · exact hinside q hq ⟨(hpositive q hq).le, le_rfl⟩
  have hspan := packingSol_endpointSpan_of_control A J φ hJ hendpoint hpositive
    hdisjoint hcover hlocal hcontrol
  obtain ⟨hterminalLo, hterminalHi⟩ :=
    packingSol_sourceCarrier_terminalEndpoints A J hinside hpositive hcover
  have hweak : ∀ a ∈ S, ∀ b ∈ S, a ≤ b → (φ a : ℝ) ≤ (φ b : ℝ) := by
    intro a ha b hb hab
    rcases lt_or_eq_of_le hab with hab | rfl
    · have h := hcontrol a ha b hb hab
      linarith
    · exact le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro lo hi hlohi hshape
    have hlo : lo ∈ S := hterminalLo lo (hshape.symm ▸ left_mem_Icc.mpr hlohi.le)
      (fun x hx => (show x ∈ Icc lo hi from hshape ▸ hx).1)
    have hhi : hi ∈ S := hterminalHi hi (hshape.symm ▸ right_mem_Icc.mpr hlohi.le)
      (fun x hx => (show x ∈ Icc lo hi from hshape ▸ hx).2)
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
      have hqlo : q.1.1 ∈ S := ⟨q.1, q.2, Or.inl rfl⟩
      have hqhi : q.1.2 ∈ S := ⟨q.1, q.2, Or.inr rfl⟩
      have hqloJ : q.1.1 ∈ Icc lo hi := hshape ▸ hendpoint hqlo
      have hqhiJ : q.1.2 ∈ Icc lo hi := hshape ▸ hendpoint hqhi
      exact ⟨(hweak lo hlo q.1.1 hqlo hqloJ.1).trans hxq.1,
        hxq.2.trans (hweak q.1.2 hqhi hi hhi hqhiJ.2)⟩
    · intro x hx
      obtain ⟨q, hq, hxq⟩ := hspan lo hlo hi hhi x hx
      exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hxq⟩
  · intro lo hshape
    have hlo : lo ∈ S := hterminalLo lo (hshape.symm ▸ (Set.mem_Ici.mpr le_rfl))
      (fun x hx => Set.mem_Ici.mp (hshape ▸ hx))
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
      have hqlo : q.1.1 ∈ S := ⟨q.1, q.2, Or.inl rfl⟩
      have hqloJ : lo ≤ q.1.1 := Set.mem_Ici.mp (hshape ▸ hendpoint hqlo)
      exact (hweak lo hlo q.1.1 hqlo hqloJ).trans hxq.1
    · intro x hx
      let R := |x - (φ lo : ℝ)| + 1
      have hR : 0 < R := by dsimp only [R]; positivity
      have hy : lo + 2 * R + 1 ∈ J := hshape.symm ▸ (by change lo ≤ lo + 2 * R + 1; linarith)
      obtain ⟨q, hq, _, hlarge⟩ := hcover (lo + 2 * R + 1) hy
      have hb : q.2 ∈ S := ⟨q, hq, Or.inr rfl⟩
      have hlb : lo < q.2 := by linarith
      have hbound := hcontrol lo hlo q.2 hb hlb
      have hxabs := le_abs_self (x - (φ lo : ℝ))
      have hxtarget : x ≤ (φ q.2 : ℝ) := by dsimp only [R] at hlarge; linarith
      obtain ⟨r, hr, hxr⟩ := hspan lo hlo q.2 hb x ⟨hx, hxtarget⟩
      exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hxr⟩
  · intro hi hshape
    have hhi : hi ∈ S := hterminalHi hi (hshape.symm ▸ (Set.mem_Iic.mpr le_rfl))
      (fun x hx => Set.mem_Iic.mp (hshape ▸ hx))
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
      have hqhi : q.1.2 ∈ S := ⟨q.1, q.2, Or.inr rfl⟩
      have hqhiJ : q.1.2 ≤ hi := Set.mem_Iic.mp (hshape ▸ hendpoint hqhi)
      exact hxq.2.trans (hweak q.1.2 hqhi hi hhi hqhiJ)
    · intro x hx
      let R := |x - (φ hi : ℝ)| + 1
      have hR : 0 < R := by dsimp only [R]; positivity
      have hy : hi - 2 * R - 1 ∈ J := hshape.symm ▸ (by change hi - 2 * R - 1 ≤ hi; linarith)
      obtain ⟨q, hq, hsmall, _⟩ := hcover (hi - 2 * R - 1) hy
      have ha : q.1 ∈ S := ⟨q, hq, Or.inl rfl⟩
      have hah : q.1 < hi := by linarith
      have hbound := hcontrol q.1 ha hi hhi hah
      have hxabs := neg_abs_le (x - (φ hi : ℝ))
      have hxtarget : (φ q.1 : ℝ) ≤ x := by dsimp only [R] at hsmall; linarith
      obtain ⟨r, hr, hxr⟩ := hspan q.1 ha hi hhi x ⟨hxtarget, hx⟩
      exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hxr⟩

  · intro hshape
    apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨q₀, hq₀, _, _⟩ := hcover 0 (hshape.symm ▸ Set.mem_univ 0)
    let c := q₀.1
    have hc : c ∈ S := ⟨q₀, hq₀, Or.inl rfl⟩
    let R := |x - (φ c : ℝ)| + 1
    have hR : 0 < R := by dsimp only [R]; positivity
    obtain ⟨qL, hqL, hlo, _⟩ :=
      hcover (c - 2 * R - 1) (hshape.symm ▸ Set.mem_univ _)
    obtain ⟨qH, hqH, _, hhi⟩ :=
      hcover (c + 2 * R + 1) (hshape.symm ▸ Set.mem_univ _)
    have hqLend : qL.1 ∈ S := ⟨qL, hqL, Or.inl rfl⟩
    have hqHend : qH.2 ∈ S := ⟨qH, hqH, Or.inr rfl⟩
    have hLc : qL.1 < c := by linarith
    have hcH : c < qH.2 := by linarith
    have hxlo : (φ qL.1 : ℝ) ≤ x := by
      have hbound := hcontrol qL.1 hqLend c hc hLc
      have hxabs := neg_abs_le (x - (φ c : ℝ))
      dsimp only [R] at hlo
      linarith
    have hxhi : x ≤ (φ qH.2 : ℝ) := by
      have hbound := hcontrol c hc qH.2 hqHend hcH
      have hxabs := le_abs_self (x - (φ c : ℝ))
      dsimp only [R] at hhi
      linarith
    obtain ⟨q, hq, hxq⟩ := hspan qL.1 hqLend qH.2 hqHend x ⟨hxlo, hxhi⟩
    exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hxq⟩

private theorem packingSol_uniformSignedGapAlphabet
    (K : PolygonalRegion) (T : Set Plane) (E : Finset (Plane × Plane))
    (d : Plane) (hd : d ≠ 0) :
    ∃ D : Finset ℝ, (∀ s ∈ D, 0 < s) ∧
      ∀ a : Plane, ∀ positive : Bool,
        ∀ q ∈ signedCarrierIntervals K T E a d positive, q.2 - q.1 ∈ D := by
  classical
  let B : Finset Plane := E.image (fun e => e.2 - e.1) ∪ E.image (fun e => e.1 - e.2)
  let A : Set ℝ := Ioi 0 ∩ (fun r : ℝ => r • d) ⁻¹' (B : Set Plane)
  have hpreFinite : ((fun r : ℝ => r • d) ⁻¹' (B : Set Plane)).Finite :=
    B.finite_toSet.preimage (smul_left_injective ℝ hd).injOn
  have hA : A.Finite := hpreFinite.inter_of_right (Ioi 0)
  refine ⟨hA.toFinset, ?_, ?_⟩
  · intro r hr
    exact (hA.mem_toFinset.mp hr).1
  · intro a positive q hq
    obtain ⟨hlt, t, ht, e, he, hcoords, hgerm⟩ := hq
    apply hA.mem_toFinset.mpr
    refine ⟨sub_pos.mpr hlt, ?_⟩
    change (q.2 - q.1) • d ∈ B
    rcases hcoords with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · have heq : (q.2 - q.1) • d = e.2 - e.1 := by
        rw [sub_smul]
        calc
          q.2 • d - q.1 • d = (a + q.2 • d) - (a + q.1 • d) := by abel
          _ = (t + e.2) - (t + e.1) := by rw [← hright, ← hleft]
          _ = e.2 - e.1 := by abel
      rw [heq]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    · have heq : (q.2 - q.1) • d = e.1 - e.2 := by
        rw [sub_smul]
        calc
          q.2 • d - q.1 • d = (a + q.2 • d) - (a + q.1 • d) := by abel
          _ = (t + e.1) - (t + e.2) := by rw [← hright, ← hleft]
          _ = e.1 - e.2 := by abel
      rw [heq]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)

private theorem packingSol_mappedIntervals_disjoint_of_order
    (A : Set (ℝ × ℝ)) (φ : ℝ →ₗ[ℚ] ℚ)
    (hpositive : ∀ q ∈ A, q.1 < q.2)
    (hdisjoint : ∀ q ∈ A, ∀ s ∈ A, q ≠ s → Disjoint (Ioo q.1 q.2) (Ioo s.1 s.2))
    (hweak : ∀ a ∈ scalarIntervalEndpoints A, ∀ b ∈ scalarIntervalEndpoints A,
      a ≤ b → (φ a : ℝ) ≤ (φ b : ℝ)) :
    ∀ q ∈ A, ∀ s ∈ A, q ≠ s →
      Disjoint (Ioo (φ q.1 : ℝ) (φ q.2 : ℝ))
        (Ioo (φ s.1 : ℝ) (φ s.2 : ℝ)) := by
  let S := scalarIntervalEndpoints A
  intro q hq s hs hqs
  have hqlo : q.1 ∈ S := ⟨q, hq, Or.inl rfl⟩
  have hqhi : q.2 ∈ S := ⟨q, hq, Or.inr rfl⟩
  have hslo : s.1 ∈ S := ⟨s, hs, Or.inl rfl⟩
  have hshi : s.2 ∈ S := ⟨s, hs, Or.inr rfl⟩
  apply Set.disjoint_left.mpr
  intro x hxq hxs
  rcases lt_trichotomy q.1 s.1 with hlt | heq | hgt
  · have hright : q.2 ≤ s.1 := by
      by_contra h
      exact scalarIntervalFamily_endpoint_notInterior A hpositive hdisjoint q hq s.1 hslo
        ⟨hlt, lt_of_not_ge h⟩
    have htarget := hweak q.2 hqhi s.1 hslo hright
    linarith [hxq.2, hxs.1]
  · have hsmall : q.1 < min q.2 s.2 :=
      lt_min (hpositive q hq) (by simpa only [heq] using hpositive s hs)
    obtain ⟨y, hylo, hyhi⟩ := exists_between hsmall
    exact Set.disjoint_left.mp (hdisjoint q hq s hs hqs)
      ⟨hylo, hyhi.trans_le (min_le_left _ _)⟩
      ⟨by simpa only [heq] using hylo, hyhi.trans_le (min_le_right _ _)⟩
  · have hright : s.2 ≤ q.1 := by
      by_contra h
      exact scalarIntervalFamily_endpoint_notInterior A hpositive hdisjoint s hs q.1 hqlo
        ⟨hgt, lt_of_not_ge h⟩
    have htarget := hweak s.2 hshi q.1 hqlo hright
    linarith [hxs.2, hxq.1]

private theorem packingSol_uniformActualSourceCarrierTransport
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (d : Plane) (hdne : d ≠ 0) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ a : Plane, ∀ r l u : ℝ,
      a + r • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support →
      l < u →
      Icc l u ⊆ connectedComponentIn
        {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r →
      ∀ positive : Bool,
      let J := connectedComponentIn
        {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r
      let A := signedCarrierComponentIntervals K T E a d r positive
      ((∃ lo hi : ℝ, lo < hi ∧ J = Icc lo hi) ∨
        (∃ lo : ℝ, J = Ici lo) ∨ (∃ hi : ℝ, J = Iic hi) ∨ J = Set.univ) ∧
      (∀ x ∈ scalarIntervalEndpoints A, ∀ y ∈ scalarIntervalEndpoints A, x < y →
        (y - x) / 2 ≤ (φ y : ℝ) - (φ x : ℝ) ∧
          (φ y : ℝ) - (φ x : ℝ) ≤ 2 * (y - x)) ∧
      (∀ Q : Set ℝ, Bornology.IsBounded Q →
        (((fun x : ℝ => (φ x : ℝ)) '' scalarIntervalEndpoints A) ∩ Q).Finite) ∧
      (∀ q ∈ A, ∀ s ∈ A, q ≠ s →
        Disjoint (Ioo (φ q.1 : ℝ) (φ q.2 : ℝ))
          (Ioo (φ s.1 : ℝ) (φ s.2 : ℝ))) ∧
      (∀ lo hi : ℝ, lo < hi → J = Icc lo hi →
        (⋃ q : A, Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ)) = Icc (φ lo : ℝ) (φ hi : ℝ)) ∧
      (∀ lo : ℝ, J = Ici lo →
        (⋃ q : A, Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ)) = Ici (φ lo : ℝ)) ∧
      (∀ hi : ℝ, J = Iic hi →
        (⋃ q : A, Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ)) = Iic (φ hi : ℝ)) ∧
      (J = Set.univ → (⋃ q : A, Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ)) = Set.univ) := by
  obtain ⟨D, _, hD⟩ := packingSol_uniformSignedGapAlphabet K T E d hdne
  obtain ⟨ε, hε, hcontrol⟩ := packingSol_uniformScalarEndpointControl D
  refine ⟨D, ε, hε, ?_⟩
  intro φ hφ a r l u hr hlu hinterval positive
  let B : Set ℝ := {s | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support}
  let J := connectedComponentIn B r
  let A := signedCarrierComponentIntervals K T E a d r positive
  let S := scalarIntervalEndpoints A
  change ((∃ lo hi : ℝ, lo < hi ∧ J = Icc lo hi) ∨
    (∃ lo : ℝ, J = Ici lo) ∨ (∃ hi : ℝ, J = Iic hi) ∨ J = Set.univ) ∧ _
  have hB : IsClosed B := sourceBoundaryParameters_isClosed K T htile.2.1 a d
  have hJ : J.OrdConnected := isPreconnected_connectedComponentIn.ordConnected
  have hactualCover : ⋃ q : A, Icc q.1.1 q.1.2 = J :=
    signedCarrierComponentIntervals_closedCover K T htile E hE hcover a d hdne r l u hr
      hlu hinterval positive
  have hcoverPoint : ∀ x ∈ J, ∃ q ∈ A, x ∈ Icc q.1 q.2 := by
    intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp (hactualCover.symm ▸ hx)
    exact ⟨q.1, q.2, hxq⟩
  have hpositive : ∀ q ∈ A, q.1 < q.2 := fun q hq => hq.1.1
  have hinside : ∀ q ∈ A, Icc q.1 q.2 ⊆ J := fun q hq => hq.2
  have hendpoint : S ⊆ J := by
    rintro x ⟨q, hq, rfl | rfl⟩
    · exact hinside q hq ⟨le_rfl, (hpositive q hq).le⟩
    · exact hinside q hq ⟨(hpositive q hq).le, le_rfl⟩
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support := fun e he =>
    ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1, (hE e he).2.2.2.2.1⟩
  have hdisjoint : ∀ q ∈ A, ∀ s ∈ A, q ≠ s → Disjoint (Ioo q.1 q.2) (Ioo s.1 s.2) := by
    intro q hq s hs hqs
    exact signedCarrierIntervals_sameSide_disjoint K T htile.2.1 E hprimitive a d hdne positive
      q hq.1 s hs.1 hqs
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite := by
    intro Q hQ
    have hfinite := signedCarrierIntervals_sourceEndpoints_locallyFinite K T htile.2.1 E
      (fun e he => ⟨(hE e he).2.1, (hE e he).2.2.1⟩) a d hdne positive Q hQ
    apply hfinite.subset
    rintro x ⟨⟨q, hq, hqx⟩, hxQ⟩
    exact ⟨⟨q, hq.1, hqx⟩, hxQ⟩
  have hgap : ∀ x ∈ S, ∀ y ∈ S, x < y → S ∩ Ioo x y = ∅ → y - x ∈ D := by
    intro x hx y hy hxy hconsecutive
    have hxyA : (x, y) ∈ A := by
      apply packingSol_consecutiveEdge_onSourceCarrier A J hJ hendpoint hpositive
        hdisjoint hcoverPoint x y hx hy hxy
      intro z hz hbetween
      have hfalse : z ∈ S ∩ Ioo x y := ⟨hz, hbetween⟩
      rw [hconsecutive] at hfalse
      exact hfalse
    exact hD a positive (x, y) hxyA.1
  have hbound := hcontrol φ hφ S hlocal hgap
  have hlower : ∀ x ∈ S, ∀ y ∈ S, x < y →
      (y - x) / 2 ≤ (φ y : ℝ) - (φ x : ℝ) :=
    fun x hx y hy hxy => (hbound x hx y hy hxy).1
  have hweak : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → (φ x : ℝ) ≤ (φ y : ℝ) := by
    intro x hx y hy hxy
    rcases lt_or_eq_of_le hxy with hxy | rfl
    · have h := hlower x hx y hy hxy
      linarith
    · exact le_rfl
  refine ⟨scalarClosedComponent_intervalRayLine B hB r l u hr hlu hinterval,
    hbound, packingSol_endpointImageLF_of_lowerControl S φ hlocal hlower,
    packingSol_mappedIntervals_disjoint_of_order A φ hpositive hdisjoint hweak, ?_⟩
  exact packingSol_carrierCases_of_control A J φ hJ hinside hpositive hdisjoint
    hcoverPoint hlocal hlower

/-- At an internal endpoint of ONE signed source chain, the actual original
star covers that signed side.  Local maximal-carrier inclusion supplies both
boundary rays; the occurrence witness supplies the SAME intrinsic label. -/
private theorem signedCarrierComponentInterval_internalEndpoint_starSide
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hvertices : ∀ e ∈ E, e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support)
    (a d : Plane) (hd : d ≠ 0) (r : ℝ) (positive : Bool)
    (q : ℝ × ℝ) (hq : q ∈ signedCarrierComponentIntervals K T E a d r positive)
    (x : ℝ) (hx : x = q.1 ∨ x = q.2)
    (hxJ : x ∈ interior (connectedComponentIn
      {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r)) :
    originalVertexConeUnion K P T (a + x • d) = Set.univ ∨
      originalVertexConeUnion K P T (a + x • d) =
        (if positive then Tiling.positiveHalfPlane 0 d else Tiling.negativeHalfPlane 0 d) := by
  obtain ⟨ρ, hρ, hstar⟩ := originalVertexStar_signedLocalCarrier_halfplane K P T hP htile
  obtain ⟨hlt, s, hs, e, he, hcoords, hgerms⟩ := hq.1
  have hps : a + x • d ∈ s +ᵥ Tiling.vertexSet K.support := by
    have hV := hvertices e he
    rcases hcoords with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · rcases hx with rfl | rfl
      · rw [← hleft]
        exact Set.vadd_mem_vadd_set hV.1
      · rw [← hright]
        exact Set.vadd_mem_vadd_set hV.2
    · rcases hx with rfl | rfl
      · rw [← hleft]
        exact Set.vadd_mem_vadd_set hV.2
      · rw [← hright]
        exact Set.vadd_mem_vadd_set hV.1
  have hden : 0 < ‖d‖ + 1 := by positivity
  obtain ⟨δ, hδ, hδsmall⟩ := exists_between
    (lt_min (sub_pos.mpr hlt) (div_pos hρ hden))
  have hδgap : δ < q.2 - q.1 := hδsmall.trans_le (min_le_left _ _)
  have hδnorm : dist (δ • d) 0 < ρ := by
    have hbound : δ * (‖d‖ + 1) < ρ :=
      (lt_div_iff₀ hden).mp (hδsmall.trans_le (min_le_right _ _))
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    nlinarith [norm_nonneg d]
  have hpoint : ∃ c : ℝ, dist (c • d) 0 < ρ ∧ x + c ∈ Ioo q.1 q.2 := by
    rcases hx with hx | hx
    · refine ⟨δ, hδnorm, ?_⟩
      rw [hx]
      constructor <;> linarith
    · refine ⟨-δ, ?_, ?_⟩
      · simpa only [neg_smul, dist_zero_right, norm_neg] using hδnorm
      · rw [hx]
        constructor <;> linarith
  obtain ⟨c, hc, hxq⟩ := hpoint
  have hpointEq : a + (x + c) • d = (a + x • d) + c • d := by
    rw [add_smul]
    abel
  have hgerm := hgerms (x + c) hxq
  rw [hpointEq] at hgerm
  exact hstar (a + x • d) s d hs hps hd
    (sourceBoundaryComponent_localInterval K T a d r hxJ) c hc positive hgerm

private theorem polyhedralVertexCone_interior_scale
    (P : PolyhedralCode) (v z : Plane) (c : ℝ) (hc : 0 < c) :
    c • z ∈ interior (polyhedralVertexCone P v) ↔
      z ∈ interior (polyhedralVertexCone P v) := by
  let H : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero c (ne_of_gt hc)
  have hpre : H ⁻¹' polyhedralVertexCone P v = polyhedralVertexCone P v := by
    ext w
    exact polyhedralVertexCone_scale P v w c hc
  have hi := H.preimage_interior (polyhedralVertexCone P v)
  rw [hpre] at hi
  have hmem := congrArg (fun S : Set Plane => z ∈ S) hi
  exact eq_iff_iff.mp hmem

/-- Local source boundary rays exclude the whole carrier from every original
vertex-label cone interior by positive homogeneity.  Aligned germs then give
uniform target noninteriority without extending source link properness. -/
private theorem originalVertexStar_localCarrier_uniformNoninteriority
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p s d : Plane, s ∈ T → p ∈ s +ᵥ Tiling.vertexSet K.support →
            (∃ r > 0, ∀ b : ℝ, |b| < r →
              p + b • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) →
            ∀ q : ℝ, dist (q • d) 0 < R →
              deformPoint φ p + q • d ∉ deformPoint φ s +ᵥ Kφ.openCarrier := by
  obtain ⟨F, ε, rA, hε, hrA, halign⟩ := originalVertexCopies_uniformAlignedGerm K P T hP
  obtain ⟨rC, hrC, hcone⟩ := originalVertexCopies_uniformConeGerm K P T hP
  refine ⟨F, ε, min rA rC, hε, lt_min hrA hrC, ?_⟩
  intro φ hφ Kφ hKφ p s d hs hps hline q hq hinterior
  let z := q • d
  let A : Set Plane := (-p) +ᵥ (s +ᵥ K.support)
  let C : Set Plane := polyhedralVertexCone P (p - s)
  have hlocal (w : Plane) (hw : dist w 0 < rC) : w ∈ A ↔ w ∈ C := by
    have h := hcone p s hs hps w hw
    simpa only [A, C, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add] using h
  have hzC : dist z 0 < rC := hq.trans_le (min_le_right _ _)
  have hsource := (halign φ hφ Kφ hKφ p s hs hps z
    (hq.trans_le (min_le_left _ _))).2.mpr hinterior
  have hzA : z ∈ interior A := by
    simpa only [A, interior_vadd, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg,
      vadd_eq_add, PolygonalRegion.openCarrier] using hsource
  have hzInteriorC := (interior_mem_iff_of_ball_eq A C rC hrC hlocal z hzC).mp hzA
  obtain ⟨r, hr, hlineR⟩ := hline
  have hdenq : 0 < |q| + 1 := by positivity
  have hdenz : 0 < ‖z‖ + 1 := by positivity
  obtain ⟨c, hc, hcsmall⟩ := exists_between
    (lt_min (div_pos hr hdenq) (div_pos hrC hdenz))
  have hcr : |c * q| < r := by
    have hbound := (lt_div_iff₀ hdenq).mp (hcsmall.trans_le (min_le_left _ _))
    rw [abs_mul, abs_of_pos hc]
    nlinarith [abs_nonneg q]
  have hcz : dist (c • z) 0 < rC := by
    have hbound := (lt_div_iff₀ hdenz).mp (hcsmall.trans_le (min_le_right _ _))
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    nlinarith [norm_nonneg z]
  have hscaled : c • z ∈ interior C :=
    (polyhedralVertexCone_interior_scale P (p - s) z c hc).mpr hzInteriorC
  have hscaledA := (interior_mem_iff_of_ball_eq A C rC hrC hlocal (c • z) hcz).mpr hscaled
  have hscaledCopy : p + c • z ∈ s +ᵥ K.openCarrier := by
    simpa only [A, interior_vadd, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg,
      vadd_eq_add, PolygonalRegion.openCarrier] using hscaledA
  have hboundary : p + c • z ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support := by
    simpa only [z, smul_smul] using hlineR (c * q) hcr
  exact Set.disjoint_left.mp (sourceBoundaryUnion_disjoint_openCarrier K T hpack s hs)
    hboundary hscaledCopy

private theorem originalVertexStar_boundaryRay_uniformNoninteriority
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p s z : Plane, s ∈ T → p ∈ s +ᵥ Tiling.vertexSet K.support →
            (∃ r > 0, ∀ c : ℝ, 0 ≤ c → c < r →
              p + c • z ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) →
            dist z 0 < R →
              deformPoint φ p + z ∉ deformPoint φ s +ᵥ Kφ.openCarrier := by
  obtain ⟨F, ε, rA, hε, hrA, halign⟩ := originalVertexCopies_uniformAlignedGerm K P T hP
  obtain ⟨rC, hrC, hcone⟩ := originalVertexCopies_uniformConeGerm K P T hP
  refine ⟨F, ε, min rA rC, hε, lt_min hrA hrC, ?_⟩
  intro φ hφ Kφ hKφ p s z hs hps hline hz hinterior
  let A : Set Plane := (-p) +ᵥ (s +ᵥ K.support)
  let C : Set Plane := polyhedralVertexCone P (p - s)
  have hlocal (w : Plane) (hw : dist w 0 < rC) : w ∈ A ↔ w ∈ C := by
    have h := hcone p s hs hps w hw
    simpa only [A, C, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add] using h
  have hzC : dist z 0 < rC := hz.trans_le (min_le_right _ _)
  have hsource := (halign φ hφ Kφ hKφ p s hs hps z
    (hz.trans_le (min_le_left _ _))).2.mpr hinterior
  have hzA : z ∈ interior A := by
    simpa only [A, interior_vadd, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg,
      vadd_eq_add, PolygonalRegion.openCarrier] using hsource
  have hzInteriorC := (interior_mem_iff_of_ball_eq A C rC hrC hlocal z hzC).mp hzA
  obtain ⟨r, hr, hlineR⟩ := hline
  have hdenz : 0 < ‖z‖ + 1 := by positivity
  obtain ⟨c, hc, hcsmall⟩ := exists_between (lt_min hr (div_pos hrC hdenz))
  have hcz : dist (c • z) 0 < rC := by
    have hbound := (lt_div_iff₀ hdenz).mp (hcsmall.trans_le (min_le_right _ _))
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    nlinarith [norm_nonneg z]
  have hscaled : c • z ∈ interior C :=
    (polyhedralVertexCone_interior_scale P (p - s) z c hc).mpr hzInteriorC
  have hscaledA := (interior_mem_iff_of_ball_eq A C rC hrC hlocal (c • z) hcz).mpr hscaled
  have hscaledCopy : p + c • z ∈ s +ᵥ K.openCarrier := by
    simpa only [A, interior_vadd, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg,
      vadd_eq_add, PolygonalRegion.openCarrier] using hscaledA
  exact Set.disjoint_left.mp (sourceBoundaryUnion_disjoint_openCarrier K T hpack s hs)
    (hlineR c hc.le (hcsmall.trans_le (min_le_left _ _))) hscaledCopy


private theorem originalVertexStar_uniformDirected_labelledCollar
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p z w : Plane,
            (∃ r > 0, ∀ c : ℝ, 0 ≤ c → c < r →
              p + c • z ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) →
            dist z 0 < R → dist (w - deformPoint φ p) 0 < R →
            w - deformPoint φ p ∈ originalVertexConeUnion K P T p →
            ∀ t : Plane, ∀ η : ℝ,
              0 < Metric.infDist w (deformPoint φ t +ᵥ Kφ.support) →
              dist w (deformPoint φ p + z) < η →
              ∃ s ∈ T, s ≠ t ∧ w ∈ deformPoint φ s +ᵥ Kφ.support ∧
                Metric.infDist w (deformPoint φ s +ᵥ frontier Kφ.support) < η := by
  obtain ⟨Fs, εs, Rs, hεs, hRs, hcover⟩ := originalVertexConeUnion_deformedGerm K P T
  obtain ⟨Fn, εn, Rn, hεn, hRn, hnoninterior⟩ :=
    originalVertexStar_boundaryRay_uniformNoninteriority K P T hP hpack
  refine ⟨Fs ∪ Fn, min εs εn, min Rs Rn, lt_min hεs hεn, lt_min hRs hRn, ?_⟩
  intro φ hφ Kφ hKφ p z w hray hz hw hQ t η hpos hnear
  have hφs := finiteApproximation_strengthen Fs (Fs ∪ Fn) εs (min εs εn) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφn := finiteApproximation_strengthen Fn (Fs ∪ Fn) εn (min εs εn) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  have hmem := (hcover φ hφs Kφ hKφ p (w - deformPoint φ p)
    (hw.trans_le (min_le_left _ _))).mpr hQ
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hmem
  have hws : w ∈ deformPoint φ (s.1 : Plane) +ᵥ Kφ.support := by
    simpa only [add_sub_cancel] using hs
  have hst : (s.1 : Plane) ≠ t := by
    intro hst
    rw [hst] at hws
    have hdist := Metric.infDist_le_dist_of_mem (x := w) hws
    simp only [dist_self] at hdist
    linarith
  have hnonint : deformPoint φ p + z ∉ interior (deformPoint φ (s.1 : Plane) +ᵥ Kφ.support) := by
    rw [interior_vadd]
    exact hnoninterior φ hφn Kφ hKφ p s.1 z s.1.2 s.2 hray
      (hz.trans_le (min_le_right _ _))
  have hdist := compact_frontier_infDist_le_of_notInterior
    (deformPoint φ (s.1 : Plane) +ᵥ Kφ.support) (Kφ.isPolygonal.isCompact.vadd _) w
    (deformPoint φ p + z) hws hnonint
  have hfront : frontier (deformPoint φ (s.1 : Plane) +ᵥ Kφ.support) =
      deformPoint φ (s.1 : Plane) +ᵥ frontier Kφ.support := by
    rw [frontier, closure_vadd, interior_vadd, ← Set.vadd_set_sdiff]
    rfl
  rw [hfront] at hdist
  exact ⟨s.1, s.1.2, hst, hws, hdist.trans_lt hnear⟩


/-- The augmented-chain near-endpoint branch is covered by ORIGINAL star
labels at a common target radius.  No finite image star or image packing is used. -/
private theorem signedCarrierComponent_internalEndpoint_uniformSignedStarCover
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hvertices : ∀ e ∈ E, e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ a d : Plane, d ≠ 0 → ∀ r : ℝ, ∀ positive : Bool,
            ∀ q ∈ signedCarrierComponentIntervals K T E a d r positive,
              ∀ x : ℝ, x = q.1 ∨ x = q.2 →
                x ∈ interior (connectedComponentIn
                  {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r) →
                ∀ z : Plane, dist z 0 < R →
                  z ∈ (if positive then Tiling.positiveHalfPlane 0 d
                    else Tiling.negativeHalfPlane 0 d) →
                    ∃ s ∈ T, a + x • d ∈ s +ᵥ Tiling.vertexSet K.support ∧
                      deformPoint φ (a + x • d) + z ∈
                        deformPoint φ s +ᵥ Kφ.support := by
  obtain ⟨F, ε, R, hε, hR, htarget⟩ := originalVertexConeUnion_deformedGerm K P T
  refine ⟨F, ε, R, hε, hR, ?_⟩
  intro φ hφ Kφ hKφ a d hd r positive q hq x hx hxJ z hz hside
  have hzQ : z ∈ originalVertexConeUnion K P T (a + x • d) := by
    rcases signedCarrierComponentInterval_internalEndpoint_starSide K P T hP htile E
      hvertices a d hd r positive q hq x hx hxJ with hfull | hhalf
    · rw [hfull]
      exact Set.mem_univ _
    · rw [hhalf]
      exact hside
  have hcover := (htarget φ hφ Kφ hKφ (a + x • d) z hz).mpr hzQ
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hcover
  exact ⟨s.1, s.1.2, s.2, hs⟩

/-- Actual near-internal-endpoint augmented collars have the required
DISTINCT label and distance to the FULL covering tile boundary. -/
private theorem signedCarrierComponent_internalEndpoint_labelledCollar
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hvertices : ∀ e ∈ E, e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ a d : Plane, d ≠ 0 → ∀ r : ℝ, ∀ positive : Bool,
            ∀ q ∈ signedCarrierComponentIntervals K T E a d r positive,
              ∀ x : ℝ, x = q.1 ∨ x = q.2 →
                x ∈ interior (connectedComponentIn
                  {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r) →
                ∀ w : Plane, dist w (deformPoint φ (a + x • d)) < R →
                  w - deformPoint φ (a + x • d) ∈
                    (if positive then Tiling.positiveHalfPlane 0 d else Tiling.negativeHalfPlane 0 d) →
                  ∀ c : ℝ, dist (c • d) 0 < R → ∀ t : Plane, ∀ η : ℝ,
                    0 < Metric.infDist w (deformPoint φ t +ᵥ Kφ.support) →
                    dist w (deformPoint φ (a + x • d) + c • d) < η →
                      ∃ s ∈ T, s ≠ t ∧ w ∈ deformPoint φ s +ᵥ Kφ.support ∧
                        Metric.infDist w (deformPoint φ s +ᵥ frontier Kφ.support) < η := by
  obtain ⟨Fs, εs, Rs, hεs, hRs, hcover⟩ :=
    signedCarrierComponent_internalEndpoint_uniformSignedStarCover K P T hP htile E hvertices
  obtain ⟨Fn, εn, Rn, hεn, hRn, hnoninterior⟩ :=
    originalVertexStar_localCarrier_uniformNoninteriority K P T hP htile.2.1
  refine ⟨Fs ∪ Fn, min εs εn, min Rs Rn, lt_min hεs hεn, lt_min hRs hRn, ?_⟩
  intro φ hφ Kφ hKφ a d hd r positive q hq x hx hxJ w hw hside c hc t η hpos hnear
  have hφs := finiteApproximation_strengthen Fs (Fs ∪ Fn) εs (min εs εn) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφn := finiteApproximation_strengthen Fn (Fs ∪ Fn) εn (min εs εn) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  have hw' : dist (w - deformPoint φ (a + x • d)) 0 < Rs := by
    simpa only [dist_eq_norm, sub_zero] using hw.trans_le (min_le_left _ _)
  obtain ⟨s, hs, hps, hws'⟩ := hcover φ hφs Kφ hKφ a d hd r positive q hq x hx hxJ
    (w - deformPoint φ (a + x • d)) hw' hside
  have hws : w ∈ deformPoint φ s +ᵥ Kφ.support := by
    simpa only [add_sub_cancel] using hws'
  have hst : s ≠ t := by
    intro hst
    rw [hst] at hws
    have hdist := Metric.infDist_le_dist_of_mem (x := w) hws
    simp only [dist_self] at hdist
    linarith
  have hys : deformPoint φ (a + x • d) + c • d ∉
      interior (deformPoint φ s +ᵥ Kφ.support) := by
    rw [interior_vadd]
    exact hnoninterior φ hφn Kφ hKφ (a + x • d) s d hs hps
      (sourceBoundaryComponent_localInterval K T a d r hxJ) c
      (hc.trans_le (min_le_right _ _))
  have hdist := compact_frontier_infDist_le_of_notInterior
    (deformPoint φ s +ᵥ Kφ.support) (Kφ.isPolygonal.isCompact.vadd _) w
    (deformPoint φ (a + x • d) + c • d) hws hys
  have hfront : frontier (deformPoint φ s +ᵥ Kφ.support) =
      deformPoint φ s +ᵥ frontier Kφ.support := by
    rw [frontier, closure_vadd, interior_vadd, ← Set.vadd_set_sdiff]
    rfl
  rw [hfront] at hdist
  exact ⟨s, hs, hst, hws, hdist.trans_lt hnear⟩

private theorem preconnected_avoids_frontier_constant (S U : Set Plane)
    (hS : IsClosed S) (hU : IsPreconnected U) (havoid : Disjoint U (frontier S)) :
    ∀ x ∈ U, ∀ y ∈ U, (x ∈ S ↔ y ∈ S) := by
  have hcover : U ⊆ interior S ∪ Sᶜ := by
    intro z hz
    by_cases hzS : z ∈ S
    · left
      exact (mem_interior_iff_notMem_frontier hzS).mpr
        (fun hzf => Set.disjoint_left.mp havoid hz hzf)
    · exact Or.inr hzS
  have hdisjoint : Disjoint (interior S) Sᶜ :=
    Set.disjoint_left.mpr (fun z hz hzc => hzc (interior_subset hz))
  intro x hx y hy
  by_cases hxS : x ∈ S
  · have hxint : x ∈ interior S := (mem_interior_iff_notMem_frontier hxS).mpr
      (fun hxf => Set.disjoint_left.mp havoid hx hxf)
    have hsubset := hU.subset_left_of_subset_union isOpen_interior hS.isOpen_compl
      hdisjoint hcover ⟨x, hx, hxint⟩
    exact ⟨fun _ => interior_subset (hsubset hy), fun _ => hxS⟩
  · have hsubset := hU.subset_right_of_subset_union isOpen_interior hS.isOpen_compl
      hdisjoint hcover ⟨x, hx, hxS⟩
    exact ⟨fun h => False.elim (hxS h), fun h => False.elim (hsubset hy h)⟩

private theorem linearGerm_extend_over_frontierFreeBall
    (S : Set Plane) (hS : IsClosed S) (f : Plane →L[ℝ] ℝ) (u : Plane)
    (hu : f u = 1) (r : ℝ) (hr : 0 < r)
    (hfront : ∀ z ∈ frontier S, dist z 0 < r → f z = 0)
    (hgerm : ∃ ρ > 0, ∀ z, dist z 0 < ρ → (z ∈ S ↔ 0 ≤ f z)) :
    ∀ z, dist z 0 < r → (z ∈ S ↔ 0 ≤ f z) := by
  obtain ⟨ρ, hρ, hgerm⟩ := hgerm
  let Upos : Set Plane := Metric.ball 0 r ∩ {z | 0 < f z}
  let Uneg : Set Plane := Metric.ball 0 r ∩ {z | f z < 0}
  have hposConn : IsPreconnected Upos :=
    ((convex_ball (0 : Plane) r).inter (convex_halfSpace_gt f.isLinear 0)).isPreconnected
  have hnegConn : IsPreconnected Uneg :=
    ((convex_ball (0 : Plane) r).inter (convex_halfSpace_lt f.isLinear 0)).isPreconnected
  have hposAvoid : Disjoint Upos (frontier S) := by
    apply Set.disjoint_left.mpr
    intro z hz hzf
    have hzero := hfront z hzf hz.1
    exact (ne_of_gt hz.2) hzero
  have hnegAvoid : Disjoint Uneg (frontier S) := by
    apply Set.disjoint_left.mpr
    intro z hz hzf
    have hzero := hfront z hzf hz.1
    exact (ne_of_lt hz.2) hzero
  obtain ⟨c, hc, hsmall⟩ := exists_positiveScaling_intoBall u (min r ρ) (lt_min hr hρ)
  have hcr : dist (c • u) 0 < r := hsmall.trans_le (min_le_left _ _)
  have hcρ : dist (c • u) 0 < ρ := hsmall.trans_le (min_le_right _ _)
  have hfc : f (c • u) = c := by simp only [map_smul, hu, smul_eq_mul, mul_one]
  have hcpos : c • u ∈ Upos := ⟨hcr, by change 0 < f (c • u); rwa [hfc]⟩
  have hcS : c • u ∈ S := (hgerm _ hcρ).mpr (by rw [hfc]; exact hc.le)
  have hncDist : dist (-(c • u)) 0 = dist (c • u) 0 := by simp
  have hncneg : -(c • u) ∈ Uneg := by
    refine ⟨?_, ?_⟩
    · change dist (-(c • u)) 0 < r
      rwa [hncDist]
    · change f (-(c • u)) < 0
      simp only [map_neg, hfc]
      linarith
  have hncS : -(c • u) ∉ S := by
    intro h
    have hineq := (hgerm _ (by simpa only [hncDist] using hcρ)).mp h
    simp only [map_neg, hfc] at hineq
    linarith
  have hposS : Upos ⊆ S := by
    intro z hz
    exact (preconnected_avoids_frontier_constant S Upos hS hposConn hposAvoid
      (c • u) hcpos z hz).mp hcS
  have hnegS : Uneg ⊆ Sᶜ := by
    intro z hz hzS
    exact hncS ((preconnected_avoids_frontier_constant S Uneg hS hnegConn hnegAvoid
      (-(c • u)) hncneg z hz).mpr hzS)
  intro z hz
  constructor
  · intro hzS
    by_contra hnot
    exact hnegS ⟨hz, lt_of_not_ge hnot⟩ hzS
  · intro hfz
    rcases hfz.eq_or_lt with hzero | hpositive
    · have hfzero : f z = 0 := hzero.symm
      rw [← hS.closure_eq]
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      obtain ⟨b, hb, hbsmall⟩ := exists_positiveScaling_intoBall u
        (min ε (r - dist z 0)) (lt_min hε (sub_pos.mpr hz))
      let y : Plane := z + b • u
      have hypos : 0 < f y := by
        simp only [y, map_add, map_smul, hfzero, hu, smul_eq_mul, mul_one, zero_add]
        exact hb
      have hyball : dist y 0 < r := by
        have hnorm := dist_triangle y z (0 : Plane)
        have hdyz : dist y z = dist (b • u) 0 := by simp [y, dist_eq_norm]
        rw [hdyz] at hnorm
        have hsmallr := hbsmall.trans_le (min_le_right _ _)
        linarith
      refine ⟨y, hposS ⟨hyball, hypos⟩, ?_⟩
      have hsmallε := hbsmall.trans_le (min_le_left _ _)
      simpa [y, dist_eq_norm] using hsmallε
    · exact hposS ⟨hz, hpositive⟩

private theorem finitePoints_deformedClose (W : Finset Plane) (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ v ∈ W, dist (deformPoint φ v) v < η := by
  classical
  let F := W.image Complex.re ∪ W.image Complex.im
  refine ⟨F, η / 2, by positivity, ?_⟩
  intro φ hφ v hv
  have hre := hφ.2 v.re (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
  have him := hφ.2 v.im (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
  have hnorm := Complex.norm_le_abs_re_add_abs_im (deformPoint φ v - v)
  simp only [deformPoint, Complex.sub_re, Complex.sub_im] at hnorm
  change ‖deformPoint φ v - v‖ ≤ |(φ v.re : ℝ) - v.re| + |(φ v.im : ℝ) - v.im| at hnorm
  rw [dist_eq_norm]
  linarith

private theorem lineMap_dist_le_endpointBound (a b a' b' : Plane) (t ε : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (ha : dist a' a ≤ ε) (hb : dist b' b ≤ ε) :
    dist (AffineMap.lineMap a' b' t) (AffineMap.lineMap a b t) ≤ ε := by
  have heq : AffineMap.lineMap a' b' t - AffineMap.lineMap a b t =
      (1 - t) • (a' - a) + t • (b' - b) := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [dist_eq_norm, heq]
  calc
    ‖(1 - t) • (a' - a) + t • (b' - b)‖ ≤
        ‖(1 - t) • (a' - a)‖ + ‖t • (b' - b)‖ := norm_add_le _ _
    _ = (1 - t) * dist a' a + t * dist b' b := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2),
        abs_of_nonneg ht.1, dist_eq_norm]
    _ ≤ (1 - t) * ε + t * ε :=
      add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left hb ht.1)
    _ = ε := by ring

private theorem finiteSegments_deformedClose (E : Finset (Plane × Plane))
    (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ e ∈ E, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) t)
            (AffineMap.lineMap e.1 e.2 t) < η := by
  classical
  let W := E.image Prod.fst ∪ E.image Prod.snd
  obtain ⟨F, ε, hε, hclose⟩ := finitePoints_deformedClose W (η / 2) (by positivity)
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ e he t ht
  have hleft := hclose φ hφ e.1
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩))
  have hright := hclose φ hφ e.2
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩))
  exact (lineMap_dist_le_endpointBound e.1 e.2 (deformPoint φ e.1)
    (deformPoint φ e.2) t (η / 2) ht hleft.le hright.le).trans_lt (by linarith)

private theorem segment_subset_affineDirection_of_frontierGerm
    {D : Set Plane} {a b p : Plane} {δ : Submodule ℝ Plane}
    (hseg : segment ℝ a b ⊆ D) (hp : p ∈ segment ℝ a b)
    (hlocal : ∀ᶠ y in 𝓝 p, y ∈ D → y - p ∈ δ) :
    ∀ y ∈ segment ℝ a b, y - p ∈ δ := by
  have hdir := segment_direction_mem_of_frontierGerm hseg hp hlocal
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨t, ht, htp⟩ := hp
  intro y hy
  rw [segment_eq_image_lineMap] at hy
  obtain ⟨s, hs, hsy⟩ := hy
  have heq : y - p = (s - t) • (b - a) := by
    rw [← htp, ← hsy]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [heq]
  exact δ.smul_mem (s - t) hdir

private theorem intrinsicEdge_foreignSegment_avoidsInterior
    (K : PolygonalRegion) {v w a b : Plane} (hvw : v ≠ w)
    (hquery : segment ℝ v w ⊆ frontier K.support)
    (hfree : ∀ p ∈ openSegment ℝ v w, p ∉ Tiling.vertexSet K.support)
    (hother : segment ℝ a b ⊆ frontier K.support)
    (n : RationalNormal) (hn : normalEval n (w - v) = 0)
    (hforeign : normalEval n (a - v) ≠ 0 ∨ normalEval n (b - v) ≠ 0) :
    Disjoint (openSegment ℝ v w) (segment ℝ a b) := by
  apply Set.disjoint_left.mpr
  intro p hp hpother
  obtain ⟨r, hr, hlocal⟩ := intrinsicSegment_frontier_is_supportingLine
    K.isPolygonal hvw (fun z hz => hquery (openSegment_subset_segment ℝ _ _ hz))
    p hp (hfree p hp)
  have hlocalKer : ∀ᶠ z in 𝓝 p,
      z ∈ frontier K.support → z - p ∈ normalDirection n := by
    filter_upwards [Metric.ball_mem_nhds p hr] with z hz hzfront
    obtain ⟨c, hc⟩ := (Tiling.mem_affineLine_iff_exists_smul (sub_ne_zero.mpr hvw.symm)).mp
      ((hlocal z hz).mp hzfront)
    change normalEval n (z - p) = 0
    rw [hc]
    simp only [add_sub_cancel_left]
    change normalCLM n (c • (w - v)) = 0
    simp only [map_smul, normalCLM_apply, hn, smul_zero]
  have hpoints := segment_subset_affineDirection_of_frontierGerm hother hpother hlocalKer
  have hpnormal : normalEval n (p - v) = 0 := by
    obtain ⟨c, hc, hcp⟩ := exists_openSegment_lineMap_parameter v w p hp
    rw [hcp]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_right]
    change normalCLM n (c • (w - v)) = 0
    simp only [map_smul, normalCLM_apply, hn, smul_zero]
  have hzero (z : Plane) (hz : z ∈ segment ℝ a b) : normalEval n (z - v) = 0 := by
    have hzp : normalEval n (z - p) = 0 := hpoints z hz
    have heq : z - v = (z - p) + (p - v) := by abel
    rw [heq, normalEval_add, hzp, hpnormal]
    simp
  rcases hforeign with hleft | hright
  · exact hleft (hzero a (left_mem_segment ℝ a b))
  · exact hright (hzero b (right_mem_segment ℝ a b))

private theorem finitePrimitiveEdges_uniformCentralSupportingLine
    (K : PolygonalRegion) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet K.support)
    (e : Plane × Plane) (he : e ∈ E) (n : RationalNormal)
    (hn : normalEval n (e.2 - e.1) = 0)
    (τ : ℝ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ t ∈ Icc τ (1 - τ), ∀ f ∈ E,
          ∀ q ∈ segment ℝ (deformPoint φ f.1) (deformPoint φ f.2),
            dist q (AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) t) < r →
              normalEval n (q - AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) t) = 0 := by
  classical
  let C : Set Plane := (AffineMap.lineMap e.1 e.2) '' Icc τ (1 - τ)
  let J := E.filter fun f =>
    normalEval n (f.1 - e.1) ≠ 0 ∨ normalEval n (f.2 - e.1) ≠ 0
  let B : Set Plane := ⋃ f ∈ J, segment ℝ f.1 f.2
  have hCcompact : IsCompact C := isCompact_Icc.image (by fun_prop)
  have hBclosed : IsClosed B :=
    isClosed_biUnion_finset (fun f hf => by
      rw [segment_eq_image_lineMap]
      exact (isCompact_Icc.image (by fun_prop)).isClosed)
  have hCsub : C ⊆ openSegment ℝ e.1 e.2 := by
    rintro p ⟨t, ht, rfl⟩
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, ⟨hτ.trans_le ht.1, ht.2.trans_lt (by linarith)⟩, rfl⟩
  have hCB : Disjoint C B := by
    apply Set.disjoint_left.mpr
    intro p hp hpB
    obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hpB
    obtain ⟨hfJ, hpf⟩ := Set.mem_iUnion.mp hf
    have hfE := (Finset.mem_filter.mp hfJ).1
    have hforeign := (Finset.mem_filter.mp hfJ).2
    exact Set.disjoint_left.mp
      (intrinsicEdge_foreignSegment_avoidsInterior K (hE e he).1 (hE e he).2.1
        (hE e he).2.2 (hE f hfE).2.1 n hn hforeign) (hCsub hp) hpf
  obtain ⟨δ, hδ, hsep⟩ := hCB.exists_thickenings hCcompact hBclosed
  obtain ⟨F, ε, hε, hclose⟩ := finiteSegments_deformedClose E (δ / 4) (by positivity)
  refine ⟨F, ε, δ / 4, hε, by positivity, ?_⟩
  intro φ hφ t ht f hf q hq hdist
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hτ.le.trans ht.1, ht.2.trans (by linarith)⟩
  let p := AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) t
  have hpC : p ∈ Metric.thickening δ C := by
    apply Metric.mem_thickening_iff.mpr
    refine ⟨AffineMap.lineMap e.1 e.2 t, ⟨t, ht, rfl⟩, ?_⟩
    exact (hclose φ hφ e he t ht01).trans (by linarith)
  have hfnot : f ∉ J := by
    intro hfJ
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨s, hs, hsq⟩ := hq
    have hpB : p ∈ Metric.thickening δ B := by
      apply Metric.mem_thickening_iff.mpr
      refine ⟨AffineMap.lineMap f.1 f.2 s,
        Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hfJ,
          by rw [segment_eq_image_lineMap]; exact ⟨s, hs, rfl⟩⟩⟩, ?_⟩
      have htriangle := dist_triangle p q (AffineMap.lineMap f.1 f.2 s)
      have hqclose := hclose φ hφ f hf s hs
      rw [hsq] at hqclose
      rw [dist_comm p q] at htriangle
      change dist q p < δ / 4 at hdist
      linarith
    exact Set.disjoint_left.mp hsep hpC hpB
  have hfzeros : normalEval n (f.1 - e.1) = 0 ∧ normalEval n (f.2 - e.1) = 0 := by
    have hnot : ¬ (normalEval n (f.1 - e.1) ≠ 0 ∨ normalEval n (f.2 - e.1) ≠ 0) := by
      intro hforeign
      exact hfnot (Finset.mem_filter.mpr ⟨hf, hforeign⟩)
    simpa only [not_or, not_not] using hnot
  have deformZero {v w : Plane} (hzero : normalEval n (v - w) = 0) :
      normalEval n (deformPoint φ v - deformPoint φ w) = 0 := by
    have hsub : deformPoint φ (v - w) = deformPoint φ v - deformPoint φ w :=
      (deformPointLinear φ).map_sub v w
    rw [← hsub, normalEval_deformPoint_commutes_local, hzero]
    simp
  have hqueryZero := deformZero hn
  have hleftZero := deformZero hfzeros.1
  have hrightZero := deformZero hfzeros.2
  rw [segment_eq_image_lineMap] at hq
  obtain ⟨s, hs, hsq⟩ := hq
  rw [← hsq]
  have heq : AffineMap.lineMap (deformPoint φ f.1) (deformPoint φ f.2) s -
      AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) t =
      (1 - s) • (deformPoint φ f.1 - deformPoint φ e.1) +
        s • (deformPoint φ f.2 - deformPoint φ e.1) -
          t • (deformPoint φ e.2 - deformPoint φ e.1) := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [heq]
  rw [← normalCLM_apply]
  rw [map_sub, map_add, map_smul, map_smul, map_smul]
  rw [normalCLM_apply, normalCLM_apply, normalCLM_apply,
    hqueryZero, hleftZero, hrightZero]
  simp

private theorem sign_eq_iff_eq_zero {x y : ℝ}
    (h : Real.sign x = Real.sign y) : x = 0 ↔ y = 0 := by
  have hneg : Real.sign (-x) = Real.sign (-y) := by
    rw [Real.sign_neg, Real.sign_neg, h]
  constructor
  · intro hx
    have hxle : x ≤ 0 := by rw [hx]
    have hxnle : -x ≤ 0 := by simp [hx]
    have hxy := (sign_eq_iff_nonpos h).mp hxle
    have hnegxy := (sign_eq_iff_nonpos hneg).mp hxnle
    linarith
  · intro hy
    have hyle : y ≤ 0 := by rw [hy]
    have hynle : -y ≤ 0 := by simp [hy]
    have hxy := (sign_eq_iff_nonpos h).mpr hyle
    have hnegxy := (sign_eq_iff_nonpos hneg).mpr hynle
    linarith

private theorem sign_eq_iff_nonneg {x y : ℝ}
    (h : Real.sign x = Real.sign y) : 0 ≤ x ↔ 0 ≤ y := by
  have hneg : Real.sign (-x) = Real.sign (-y) := by
    rw [Real.sign_neg, Real.sign_neg, h]
  simpa only [neg_nonpos] using sign_eq_iff_nonpos hneg

private theorem segment_iff_lineAndTwoCuts
    (v w : Plane) (g : Plane →ₗ[ℝ] ℝ) (hg : 0 < g (w - v)) (z : Plane) :
    z ∈ segment ℝ v w ↔ z - v ∈ Submodule.span ℝ ({w - v} : Set Plane) ∧
      0 ≤ g (z - v) ∧ g (z - w) ≤ 0 := by
  constructor
  · rw [segment_eq_image_lineMap]
    rintro ⟨t, ht, rfl⟩
    have hline : (AffineMap.lineMap v w t) - v = t • (w - v) := by
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    have hback : (AffineMap.lineMap v w t) - w = (t - 1) • (w - v) := by
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    refine ⟨?_, ?_, ?_⟩
    · rw [hline]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [hline, map_smul, smul_eq_mul]
      exact mul_nonneg ht.1 hg.le
    · rw [hback, map_smul, smul_eq_mul]
      nlinarith [ht.2]
  · rintro ⟨hspan, hlow, hhigh⟩
    rw [Submodule.mem_span_singleton] at hspan
    rcases hspan with ⟨t, ht⟩
    have hlow' : 0 ≤ t := by
      rw [← ht, map_smul, smul_eq_mul] at hlow
      exact (mul_nonneg_iff_of_pos_right hg).mp hlow
    have hback : z - w = (t - 1) • (w - v) := by
      calc
        z - w = (z - v) - (w - v) := by module
        _ = t • (w - v) - (w - v) := by rw [← ht]
        _ = (t - 1) • (w - v) := by module
    have hhigh' : t ≤ 1 := by
      rw [hback, map_smul, smul_eq_mul] at hhigh
      nlinarith
    have hz : z = v + t • (w - v) := by
      calc z = (z - v) + v := by abel
        _ = t • (w - v) + v := by rw [ht]
        _ = v + t • (w - v) := by abel
    rw [segment_eq_image_lineMap]
    refine ⟨t, ⟨hlow', hhigh'⟩, ?_⟩
    rw [hz]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module

private theorem homeomorph_image_segment_of_threeSigns
    (H : Plane ≃ₜ Plane) (v w v' w' : Plane)
    (f g : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ z, f z = 0 ↔ z ∈ Submodule.span ℝ ({w - v} : Set Plane))
    (hker' : ∀ z, f z = 0 ↔ z ∈ Submodule.span ℝ ({w' - v'} : Set Plane))
    (hg : 0 < g (w - v)) (hg' : 0 < g (w' - v'))
    (_hanchors : H v = v' ∧ H w = w')
    (hmid : ∀ z, Real.sign (f (H z - v')) = Real.sign (f (z - v)))
    (hstart : ∀ z, Real.sign (g (H z - v')) = Real.sign (g (z - v)))
    (hstop : ∀ z, Real.sign (g (H z - w')) = Real.sign (g (z - w))) :
    H '' segment ℝ v w = segment ℝ v' w' := by
  have hmem (z : Plane) : z ∈ segment ℝ v w ↔ H z ∈ segment ℝ v' w' := by
    rw [segment_iff_lineAndTwoCuts v w g hg z,
      segment_iff_lineAndTwoCuts v' w' g hg' (H z)]
    have hspan : z - v ∈ Submodule.span ℝ ({w - v} : Set Plane) ↔
        H z - v' ∈ Submodule.span ℝ ({w' - v'} : Set Plane) := by
      rw [← hker (z - v), ← hker' (H z - v')]
      exact sign_eq_iff_eq_zero (hmid z).symm
    have hlow : 0 ≤ g (z - v) ↔ 0 ≤ g (H z - v') :=
      (sign_eq_iff_nonneg (hstart z)).symm
    have hhigh : g (z - w) ≤ 0 ↔ g (H z - w') ≤ 0 :=
      (sign_eq_iff_nonpos (hstop z)).symm
    exact and_congr hspan (and_congr hlow hhigh)
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hmem z).mp hz
  · intro hy
    obtain ⟨z, rfl⟩ := H.surjective y
    exact ⟨z, (hmem z).mpr hy, rfl⟩

private theorem exists_positiveRationalCoordinateNormal (d : Plane) (hd : d ≠ 0) :
    ∃ m : RationalNormal, 0 < normalEval m d := by
  by_cases hre : d.re = 0
  · have him : d.im ≠ 0 := by
      intro h
      apply hd
      exact Complex.ext hre h
    rcases lt_trichotomy d.im 0 with hneg | hzero | hpos
    · refine ⟨⟨0, -1, Or.inr (by norm_num)⟩, ?_⟩
      simp [normalEval, hre]
      linarith
    · exact False.elim (him hzero)
    · refine ⟨⟨0, 1, Or.inr (by norm_num)⟩, ?_⟩
      simp [normalEval, hre]
      exact hpos
  · rcases lt_trichotomy d.re 0 with hneg | hzero | hpos
    · refine ⟨⟨-1, 0, Or.inl (by norm_num)⟩, ?_⟩
      simp [normalEval]
      linarith
    · exact False.elim (hre hzero)
    · refine ⟨⟨1, 0, Or.inl (by norm_num)⟩, ?_⟩
      simp [normalEval]
      exact hpos

private theorem span_singleton_positiveHomothety (d : Plane) (c : ℝ)
    (hc : 0 < c) : Submodule.span ℝ ({c • d} : Set Plane) =
      Submodule.span ℝ ({d} : Set Plane) := by
  ext z
  rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t * c, ?_⟩
    rw [smul_smul]
  · rintro ⟨t, ht⟩
    refine ⟨t / c, ?_⟩
    rw [smul_smul]
    rw [div_mul_cancel₀ t (ne_of_gt hc)]
    exact ht

private theorem rationalPrimitiveFrontier_transport
    (K : PolygonalRegion) (P : PolyhedralCode)
    (hP : polyhedralSupport P = K.support)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧
      Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∃ H : Plane ≃ₜ Plane,
            (∀ z ∈ E.image Prod.fst ∪ E.image Prod.snd,
              H z = deformPoint φ z) ∧
            H '' K.support = Kφ.support ∧
            (∀ e ∈ E, H '' segment ℝ e.1 e.2 =
              segment ℝ (deformPoint φ e.1) (deformPoint φ e.2)) ∧
            frontier Kφ.support = ⋃ e ∈ E,
              segment ℝ (deformPoint φ e.1) (deformPoint φ e.2) := by
  classical
  obtain ⟨Fc, εc, l, hεc, hl, hcontrol⟩ := finiteRationalEdges_positiveHomotheties E
    (fun e he => (hE e he).2)
  let nfun : {e : Plane × Plane // e ∈ E} → RationalNormal := fun e =>
    Classical.choose (rationalDirection_hasNormal
      (Submodule.span ℝ ({e.1.2 - e.1.1} : Set Plane))
      (finrank_span_singleton (sub_ne_zero.mpr (hE e.1 e.2).1.symm))
      (hE e.1 e.2).2.2)
  have hnfun (e : {e : Plane × Plane // e ∈ E}) :
      normalDirection (nfun e) = Submodule.span ℝ ({e.1.2 - e.1.1} : Set Plane) :=
    Classical.choose_spec (rationalDirection_hasNormal
      (Submodule.span ℝ ({e.1.2 - e.1.1} : Set Plane))
      (finrank_span_singleton (sub_ne_zero.mpr (hE e.1 e.2).1.symm))
      (hE e.1 e.2).2.2)
  let mfun : {e : Plane × Plane // e ∈ E} → RationalNormal := fun e =>
    Classical.choose (exists_positiveRationalCoordinateNormal
      (e.1.2 - e.1.1) (sub_ne_zero.mpr (hE e.1 e.2).1.symm))
  have hmfun (e : {e : Plane × Plane // e ∈ E}) :
      0 < normalEval (mfun e) (e.1.2 - e.1.1) :=
    Classical.choose_spec (exists_positiveRationalCoordinateNormal
      (e.1.2 - e.1.1) (sub_ne_zero.mpr (hE e.1 e.2).1.symm))
  let lineThrough : RationalNormal → Plane → RationalLine :=
    fun n v => ⟨n, normalEval n v⟩
  let edgeLines : Finset RationalLine := E.attach.biUnion fun e =>
    ({lineThrough (nfun e) e.1.1,
      lineThrough (mfun e) e.1.1,
      lineThrough (mfun e) e.1.2} : Finset RationalLine)
  let L : Finset RationalLine := P.flatten.toFinset ∪ edgeLines
  let Z : Finset Plane := E.image Prod.fst ∪ E.image Prod.snd
  obtain ⟨Fa, εa, hεa, harr⟩ := finiteRationalArrangement_transport L Z
  let F : Finset ℝ := Fa ∪ Fc
  let ε : ℝ := min εa εc
  refine ⟨F, ε, lt_min hεa hεc, ?_⟩
  intro φ hφ Kφ hKφ
  have hφa : IsFiniteApproximation Fa εa φ := by
    refine ⟨hφ.1, ?_⟩
    intro x hx
    exact (hφ.2 x (Finset.mem_union_left _ hx)).trans_le (min_le_left _ _)
  have hφc : IsFiniteApproximation Fc εc φ := by
    refine ⟨hφ.1, ?_⟩
    intro x hx
    exact (hφ.2 x (Finset.mem_union_right _ hx)).trans_le (min_le_right _ _)
  obtain ⟨H, hHA, hHL⟩ := harr φ hφa
  have hsupport : H '' K.support = Kφ.support := by
    have hpre : H ⁻¹' Kφ.support = K.support := by
      ext z
      rw [hP.symm, hKφ]
      exact (arrangement_polyhedralSupport_transport P φ H
        (fun ll hll y => hHL ll (Finset.mem_union_left _ (List.mem_toFinset.mpr hll)) y) z).symm
    rw [← hpre]
    exact Set.image_preimage_eq _ H.surjective
  have hfront : frontier Kφ.support = H '' frontier K.support := by
    calc
      frontier Kφ.support = frontier (H '' K.support) := by rw [hsupport]
      _ = H '' frontier K.support := (H.image_frontier K.support).symm
  have himageEdge (e : {e : Plane × Plane // e ∈ E}) :
      H '' segment ℝ e.1.1 e.1.2 =
        segment ℝ (deformPoint φ e.1.1) (deformPoint φ e.1.2) := by
    let v := e.1.1
    let w := e.1.2
    let d := w - v
    let n := nfun e
    let m := mfun e
    let f : Plane →ₗ[ℝ] ℝ := (normalCLM n).toLinearMap
    let g : Plane →ₗ[ℝ] ℝ := (normalCLM m).toLinearMap
    have hvZ : v ∈ Z := by
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e.1, e.2, rfl⟩)
    have hwZ : w ∈ Z := by
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.1, e.2, rfl⟩)
    have hvH := hHA v hvZ
    have hwH := hHA w hwZ
    obtain ⟨c, hc₁, hc₂, hvec, _⟩ := hcontrol φ hφc e.1 e.2
    have hker : ∀ z, f z = 0 ↔ z ∈ Submodule.span ℝ ({d} : Set Plane) := by
      intro z
      change normalEval n z = 0 ↔ _
      rw [← normalDirection_mem_iff n z, hnfun e]
    have hspan : Submodule.span ℝ ({deformPoint φ w - deformPoint φ v} : Set Plane) =
        Submodule.span ℝ ({d} : Set Plane) := by
      rw [hvec]
      exact span_singleton_positiveHomothety d c (by linarith [hc₁])
    have hker' : ∀ z, f z = 0 ↔
        z ∈ Submodule.span ℝ ({deformPoint φ w - deformPoint φ v} : Set Plane) := by
      intro z
      rw [hker, hspan]
    have hg : 0 < g d := hmfun e
    have hg' : 0 < g (deformPoint φ w - deformPoint φ v) := by
      rw [hvec, map_smul]
      exact mul_pos (by linarith [hc₁]) hg
    have hlineMem (ll : RationalLine) (hll : ll ∈
        ({lineThrough n v, lineThrough m v, lineThrough m w} : Finset RationalLine)) : ll ∈ L := by
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_attach _ _, by simpa [lineThrough, n, m, v, w] using hll⟩
    have hmid : ∀ z, Real.sign (f (H z - deformPoint φ v)) = Real.sign (f (z - v)) := by
      intro z
      have hs := hHL (lineThrough n v) (hlineMem _ (by simp)) z
      have hsource : (lineThrough n v).eval z = f (z - v) := by
        simp [lineThrough, RationalLine.eval, f, normalCLM_apply, normalEval_sub]
      have htarget : (deformLine φ (lineThrough n v)).eval (H z) =
          f (H z - deformPoint φ v) := by
        simp [lineThrough, RationalLine.eval, deformLine, f, normalCLM_apply,
          normalEval_sub, hvH, normalEval_deformPoint_commutes_local]
      rw [htarget, hsource] at hs
      exact hs
    have hstart : ∀ z, Real.sign (g (H z - deformPoint φ v)) = Real.sign (g (z - v)) := by
      intro z
      have hs := hHL (lineThrough m v) (hlineMem _ (by simp)) z
      have hsource : (lineThrough m v).eval z = g (z - v) := by
        simp [lineThrough, RationalLine.eval, g, normalCLM_apply, normalEval_sub]
      have htarget : (deformLine φ (lineThrough m v)).eval (H z) =
          g (H z - deformPoint φ v) := by
        simp [lineThrough, RationalLine.eval, deformLine, g, normalCLM_apply,
          normalEval_sub, hvH, normalEval_deformPoint_commutes_local]
      rw [htarget, hsource] at hs
      exact hs
    have hstop : ∀ z, Real.sign (g (H z - deformPoint φ w)) = Real.sign (g (z - w)) := by
      intro z
      have hs := hHL (lineThrough m w) (hlineMem _ (by simp)) z
      have hsource : (lineThrough m w).eval z = g (z - w) := by
        simp [lineThrough, RationalLine.eval, g, normalCLM_apply, normalEval_sub]
      have htarget : (deformLine φ (lineThrough m w)).eval (H z) =
          g (H z - deformPoint φ w) := by
        simp [lineThrough, RationalLine.eval, deformLine, g, normalCLM_apply,
          normalEval_sub, hwH, normalEval_deformPoint_commutes_local]
      rw [htarget, hsource] at hs
      exact hs
    exact homeomorph_image_segment_of_threeSigns H v w
      (deformPoint φ v) (deformPoint φ w) f g hker hker' hg hg'
      ⟨hvH, hwH⟩ hmid hstart hstop
  have hcoverImage : H '' frontier K.support =
      ⋃ e ∈ E, segment ℝ (deformPoint φ e.1) (deformPoint φ e.2) := by
    rw [hcover]
    rw [Set.image_iUnion]
    apply iUnion_congr
    intro e
    rw [Set.image_iUnion]
    apply iUnion_congr
    intro he
    exact himageEdge ⟨e, he⟩
  refine ⟨H, hHA, hsupport, ?_, ?_⟩
  · intro e he
    exact himageEdge ⟨e, he⟩

  · rw [hfront, hcoverImage]

private theorem affineLine_ball_mem_segment (v w : Plane) (hvw : v ≠ w)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (r : ℝ)
    (hrv : r ≤ dist (AffineMap.lineMap v w t) v)
    (hrw : r ≤ dist (AffineMap.lineMap v w t) w) :
    ∀ z, dist z (AffineMap.lineMap v w t) < r →
      z ∈ Tiling.affineLine (AffineMap.lineMap v w t) (w - v) →
        z ∈ segment ℝ v w := by
  let d := w - v
  have hd : 0 < ‖d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvw.symm)
  have hvdist : dist (AffineMap.lineMap v w t) v = t * ‖d‖ := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, dist_eq_norm,
      add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    rfl
  have hwdist : dist (AffineMap.lineMap v w t) w = (1 - t) * ‖d‖ := by
    have heq : AffineMap.lineMap v w t - w = (t - 1) • (w - v) := by
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr ht.2)]
    dsimp [d]
    ring
  intro z hz hline
  obtain ⟨c, hcz⟩ :=
    (Tiling.mem_affineLine_iff_exists_smul (sub_ne_zero.mpr hvw.symm)).mp hline
  have hdist : dist z (AffineMap.lineMap v w t) = |c| * ‖d‖ := by
    rw [hcz, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rfl
  have hlow : 0 ≤ t + c := by
    rw [hvdist] at hrv
    rw [hdist] at hz
    have hc := neg_abs_le c
    nlinarith
  have hhigh : t + c ≤ 1 := by
    rw [hwdist] at hrw
    rw [hdist] at hz
    have hc := le_abs_self c
    nlinarith
  rw [segment_eq_image_lineMap]
  refine ⟨t + c, ⟨hlow, hhigh⟩, ?_⟩
  rw [hcz]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  module

private theorem lineMap_endpointDistances (v w : Plane) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (AffineMap.lineMap v w t) v = t * dist v w ∧
      dist (AffineMap.lineMap v w t) w = (1 - t) * dist v w := by
  constructor
  · simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, dist_eq_norm,
      add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    rw [norm_sub_rev]
  · have heq : AffineMap.lineMap v w t - w = (t - 1) • (w - v) := by
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr ht.2)]
    rw [dist_eq_norm, norm_sub_rev]
    ring

private theorem segmentPoint_centralOrNearEndpoints (a b y : Plane) (L R τ : ℝ)
    (hL : 0 < L) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (hbound : dist a b ≤ L) (hmargin : τ * L < R)
    (hy : y ∈ segment ℝ a b) :
    dist y a < R ∨ dist y b < R ∨
      ∃ θ ∈ Icc τ (1 - τ), y = AffineMap.lineMap a b θ := by
  rw [segment_eq_image_lineMap] at hy
  obtain ⟨θ, hθ, rfl⟩ := hy
  obtain ⟨hleft, hright⟩ := lineMap_endpointDistances a b θ hθ
  by_cases hθlo : θ < τ
  · left
    rw [hleft]
    nlinarith [dist_nonneg (x := a) (y := b)]
  · by_cases hθhi : 1 - τ < θ
    · right; left
      rw [hright]
      nlinarith [dist_nonneg (x := a) (y := b)]
    · exact Or.inr (Or.inr ⟨θ, ⟨le_of_not_gt hθlo, le_of_not_gt hθhi⟩, rfl⟩)


private theorem integerCarrierOccurrence_targetSegment
    (φ : ℝ →ₗ[ℚ] ℚ) (a t : Plane) (z : Tiling.RationalPolygonal.IntegerPlane)
    (e : Plane × Plane) (lo hi u : ℝ)
    (hcoords : (t + e.1 = a + lo • Tiling.RationalPolygonal.integerPoint z ∧
        t + e.2 = a + hi • Tiling.RationalPolygonal.integerPoint z) ∨
      (t + e.2 = a + lo • Tiling.RationalPolygonal.integerPoint z ∧
        t + e.1 = a + hi • Tiling.RationalPolygonal.integerPoint z))
    (horder : (φ lo : ℝ) < (φ hi : ℝ))
    (hu : u ∈ Icc (φ lo : ℝ) (φ hi : ℝ)) :
    deformPoint φ a + u • Tiling.RationalPolygonal.integerPoint z ∈
      deformPoint φ t +ᵥ segment ℝ (deformPoint φ e.1) (deformPoint φ e.2) := by
  have mapEndpoint {v : Plane} {x : ℝ}
      (h : t + v = a + x • Tiling.RationalPolygonal.integerPoint z) :
      deformPoint φ t + deformPoint φ v =
        deformPoint φ a + (φ x : ℝ) • Tiling.RationalPolygonal.integerPoint z := by
    calc
      deformPoint φ t + deformPoint φ v = deformPoint φ (t + v) :=
        ((deformPointLinear φ).map_add t v).symm
      _ = deformPoint φ (a + x • Tiling.RationalPolygonal.integerPoint z) := by rw [h]
      _ = deformPoint φ a + (φ x : ℝ) • Tiling.RationalPolygonal.integerPoint z :=
        deformPoint_integerCarrierParameter φ a x z
  rw [vadd_segment]
  simp only [vadd_eq_add]
  rcases hcoords with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · rw [mapEndpoint hlo, mapEndpoint hhi]
    exact carrierParameter_mem_segment _ _ _ _ _ horder hu
  · rw [mapEndpoint hlo, mapEndpoint hhi, segment_symm]
    exact carrierParameter_mem_segment _ _ _ _ _ horder hu


private theorem normalEval_smul (n : RationalNormal) (t : ℝ) (x : Plane) :
    normalEval n (t • x) = t * normalEval n x := by
  simp [normalEval, Complex.smul_re, Complex.smul_im]
  ring

private theorem signedSide_translation (p q d z : Plane) :
    Tiling.signedSide p d (p + z) = Tiling.signedSide q d (q + z) := by
  simp [Tiling.signedSide, Tiling.planarCross, Complex.add_re, Complex.add_im]
  ring

private theorem alignedSupport_transports_positiveEdgeGerm
    (A B : Set Plane) (p q d : Plane) (R : ℝ) (hR : 0 < R)
    (halign : ∀ z, dist z 0 < R → (p + z ∈ A ↔ q + z ∈ B))
    (hsource : positiveEdgeGerm A d p) : positiveEdgeGerm B d q := by
  obtain ⟨ρ, hρ, hEq⟩ := hsource
  refine ⟨min R ρ, lt_min hR hρ, ?_⟩
  ext z
  constructor
  · rintro ⟨hzB, hzball⟩
    let u := z - q
    have hu : dist u 0 < min R ρ := by
      simpa [u, dist_eq_norm] using hzball
    have hqu : q + u = z := by dsimp [u]; abel
    have htarget : q + u ∈ B := by simpa [hqu] using hzB
    have hsourceMem := (halign u (lt_of_lt_of_le hu (min_le_left _ _))).mpr htarget
    have hsourceBall : p + u ∈ Metric.ball p ρ := by
      apply Metric.mem_ball.mpr
      have : dist (p + u) p = dist u 0 := by simp [dist_eq_norm]
      rw [this]
      exact (lt_of_lt_of_le hu (min_le_right _ _))
    have hEq' := (Set.ext_iff.mp hEq) (p + u)
    have hsourceHalf : p + u ∈ Tiling.positiveHalfPlane p d :=
      (hEq'.mp ⟨hsourceMem, hsourceBall⟩).1
    have hside := Tiling.mem_positiveHalfPlane.mp hsourceHalf
    have htrans : Tiling.signedSide p d (p + u) = Tiling.signedSide q d z := by
      rw [← hqu]
      exact signedSide_translation p q d u
    exact ⟨Tiling.mem_positiveHalfPlane.mpr (by rw [← htrans]; exact hside), hzball⟩
  · intro hz
    let u := z - q
    have hu : dist u 0 < min R ρ := by
      simpa [u, dist_eq_norm] using hz.2
    have hqu : q + u = z := by dsimp [u]; abel
    have hsourceBall : p + u ∈ Metric.ball p ρ := by
      apply Metric.mem_ball.mpr
      have : dist (p + u) p = dist u 0 := by simp [dist_eq_norm]
      rw [this]
      exact (lt_of_lt_of_le hu (min_le_right _ _))
    have hsourceHalf : p + u ∈ Tiling.positiveHalfPlane p d := by
      have hside : 0 ≤ Tiling.signedSide p d (p + u) := by
        have htrans : Tiling.signedSide p d (p + u) = Tiling.signedSide q d z := by
          have hzq : q + u = z := by dsimp [u]; abel
          rw [← hzq]
          exact signedSide_translation p q d u
        rw [htrans]
        exact Tiling.mem_positiveHalfPlane.mp hz.1
      exact Tiling.mem_positiveHalfPlane.mpr hside
    have hEq' := (Set.ext_iff.mp hEq) (p + u)
    have hsrc : p + u ∈ A := (hEq'.mpr ⟨hsourceHalf, hsourceBall⟩).1
    have htarget := (halign u (lt_of_lt_of_le hu (min_le_left _ _))).mp hsrc
    exact ⟨by simpa [hqu] using htarget, hz.2⟩

private theorem alignedSupport_transports_negativeEdgeGerm
    (A B : Set Plane) (p q d : Plane) (R : ℝ) (hR : 0 < R)
    (halign : ∀ z, dist z 0 < R → (p + z ∈ A ↔ q + z ∈ B))
    (hsource : negativeEdgeGerm A d p) : negativeEdgeGerm B d q := by
  obtain ⟨ρ, hρ, hEq⟩ := hsource
  refine ⟨min R ρ, lt_min hR hρ, ?_⟩
  ext z
  constructor
  · rintro ⟨hzB, hzball⟩
    let u := z - q
    have hu : dist u 0 < min R ρ := by simpa [u, dist_eq_norm] using hzball
    have hqu : q + u = z := by dsimp [u]; abel
    have htarget : q + u ∈ B := by simpa [hqu] using hzB
    have hsourceMem := (halign u (lt_of_lt_of_le hu (min_le_left _ _))).mpr htarget
    have hsourceBall : p + u ∈ Metric.ball p ρ := by
      apply Metric.mem_ball.mpr
      have : dist (p + u) p = dist u 0 := by simp [dist_eq_norm]
      rw [this]
      exact (lt_of_lt_of_le hu (min_le_right _ _))
    have hEq' := (Set.ext_iff.mp hEq) (p + u)
    have hsourceHalf : p + u ∈ Tiling.negativeHalfPlane p d :=
      (hEq'.mp ⟨hsourceMem, hsourceBall⟩).1
    have hside := Tiling.mem_negativeHalfPlane.mp hsourceHalf
    have htrans : Tiling.signedSide p d (p + u) = Tiling.signedSide q d z := by
      rw [← hqu]
      exact signedSide_translation p q d u
    exact ⟨Tiling.mem_negativeHalfPlane.mpr (by rw [← htrans]; exact hside), hzball⟩
  · intro hz
    let u := z - q
    have hu : dist u 0 < min R ρ := by simpa [u, dist_eq_norm] using hz.2
    have hqu : q + u = z := by dsimp [u]; abel
    have hsourceBall : p + u ∈ Metric.ball p ρ := by
      apply Metric.mem_ball.mpr
      have : dist (p + u) p = dist u 0 := by simp [dist_eq_norm]
      rw [this]
      exact (lt_of_lt_of_le hu (min_le_right _ _))
    have hsourceHalf : p + u ∈ Tiling.negativeHalfPlane p d := by
      have htrans : Tiling.signedSide p d (p + u) = Tiling.signedSide q d z := by
        rw [← hqu]
        exact signedSide_translation p q d u
      exact Tiling.mem_negativeHalfPlane.mpr (by rw [htrans]; exact Tiling.mem_negativeHalfPlane.mp hz.1)
    have hEq' := (Set.ext_iff.mp hEq) (p + u)
    have hsrc : p + u ∈ A := (hEq'.mpr ⟨hsourceHalf, hsourceBall⟩).1
    have htarget := (halign u (lt_of_lt_of_le hu (min_le_left _ _))).mp hsrc
    exact ⟨by simpa [hqu] using htarget, hz.2⟩

private theorem deformPoint_lineMap_midpoint
    (φ : ℝ →ₗ[ℚ] ℚ) (a b : Plane) :
    deformPoint φ ((AffineMap.lineMap a b) (1 / 2 : ℝ)) =
      (AffineMap.lineMap (deformPoint φ a) (deformPoint φ b)) (1 / 2 : ℝ) := by
  have hrep (x y : Plane) :
      (AffineMap.lineMap x y) (1 / 2 : ℝ) =
        (1 / 2 : ℚ) • x + (1 / 2 : ℚ) • y := by
    apply Complex.ext
    · simp [AffineMap.lineMap_apply, Complex.add_re, Complex.sub_re,
        Complex.smul_re, Rat.smul_def]
      ring
    · simp [AffineMap.lineMap_apply, Complex.add_im, Complex.sub_im,
        Complex.smul_im, Rat.smul_def]
      ring
  rw [hrep a b, hrep (deformPoint φ a) (deformPoint φ b)]
  change deformPointLinear φ ((1 / 2 : ℚ) • a + (1 / 2 : ℚ) • b) = _
  rw [map_add, map_smul, map_smul]
  rfl

private theorem rationalPrimitiveEdges_uniformMidpointGerms
    (K : PolygonalRegion) (P : PolyhedralCode)
    (hP : polyhedralSupport P = K.support) (E : Finset (Plane × Plane))
    :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ e ∈ E,
          let m := (AffineMap.lineMap e.1 e.2) (1 / 2 : ℝ)
          let mφ := deformPoint φ m
          mφ ∈ openSegment ℝ (deformPoint φ e.1) (deformPoint φ e.2) ∧
          ((∀ p ∈ openSegment ℝ e.1 e.2,
              positiveEdgeGerm K.support (e.2 - e.1) p) →
            positiveEdgeGerm (deformedPolyhedralSupport P φ) (e.2 - e.1) mφ) ∧
          ((∀ p ∈ openSegment ℝ e.1 e.2,
              negativeEdgeGerm K.support (e.2 - e.1) p) →
            negativeEdgeGerm (deformedPolyhedralSupport P φ) (e.2 - e.1) mφ) := by
  classical
  let W := E.image fun e => (AffineMap.lineMap e.1 e.2) (1 / 2 : ℝ)
  obtain ⟨F, ε, R, hε, hR, halign⟩ :=
    polyhedralSupport_uniformAlignedSupport P W
  refine ⟨F, ε, R, hε, hR, ?_⟩
  intro φ hφ e he
  let m := (AffineMap.lineMap e.1 e.2) (1 / 2 : ℝ)
  let mφ := deformPoint φ m
  have hmW : m ∈ W := Finset.mem_image.mpr ⟨e, he, rfl⟩
  have hmidOpen : m ∈ openSegment ℝ e.1 e.2 := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨1 / 2, by norm_num, rfl⟩
  have hmφOpen : mφ ∈ openSegment ℝ (deformPoint φ e.1) (deformPoint φ e.2) := by
    change deformPoint φ ((AffineMap.lineMap e.1 e.2) (1 / 2 : ℝ)) ∈ _
    rw [deformPoint_lineMap_midpoint]
    rw [openSegment_eq_image_lineMap]
    exact ⟨1 / 2, by norm_num, rfl⟩
  have hsourceAlign : ∀ z, dist z 0 < R →
      (m + z ∈ K.support ↔ deformPoint φ m + z ∈ deformedPolyhedralSupport P φ) := by
    intro z hz
    simpa [hP] using halign φ hφ m hmW z hz
  have hpos :
      (∀ p ∈ openSegment ℝ e.1 e.2,
        positiveEdgeGerm K.support (e.2 - e.1) p) →
      positiveEdgeGerm (deformedPolyhedralSupport P φ) (e.2 - e.1) mφ := by
    intro hside
    exact alignedSupport_transports_positiveEdgeGerm K.support
      (deformedPolyhedralSupport P φ) m mφ (e.2 - e.1) R hR hsourceAlign
      (hside m hmidOpen)
  have hneg :
      (∀ p ∈ openSegment ℝ e.1 e.2,
        negativeEdgeGerm K.support (e.2 - e.1) p) →
      negativeEdgeGerm (deformedPolyhedralSupport P φ) (e.2 - e.1) mφ := by
    intro hside
    exact alignedSupport_transports_negativeEdgeGerm K.support
      (deformedPolyhedralSupport P φ) m mφ (e.2 - e.1) R hR hsourceAlign
      (hside m hmidOpen)
  exact ⟨hmφOpen, hpos, hneg⟩

private theorem intrinsicSegment_orientation_constant_of_pointwise_germs
    {s : Set Plane} {v w : Plane} (hvw : v ≠ w)
    (hpoint : ∀ p ∈ openSegment ℝ v w,
      positiveEdgeGerm s (w - v) p ∨ negativeEdgeGerm s (w - v) p) :
    (∀ p ∈ openSegment ℝ v w, positiveEdgeGerm s (w - v) p) ∨
      (∀ p ∈ openSegment ℝ v w, negativeEdgeGerm s (w - v) p) := by
  let S : Set Plane := openSegment ℝ v w
  let X := {x : Plane // x ∈ S}
  let U : Set X := {x | positiveEdgeGerm s (w - v) x.1}
  let V : Set X := {x | negativeEdgeGerm s (w - v) x.1}
  have hS : IsPreconnected S := (convex_openSegment v w).isPreconnected
  have hpreX : PreconnectedSpace X := by
    apply (isPreconnected_iff_preconnectedSpace).mp
    simpa [X, S] using hS
  letI := hpreX
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨r, hr, hEq⟩ := hx
    let N : Set X := Subtype.val ⁻¹' Metric.ball x.1 (r / 2)
    have hNopen : IsOpen N := Metric.isOpen_ball.preimage continuous_subtype_val
    have hxN : x ∈ N := by simp [N, hr]
    apply Filter.mem_of_superset (hNopen.mem_nhds hxN)
    intro y hy
    exact positiveEdgeGerm_stable_nearby hvw x.2 y.2 r hr hEq hy
  have hVopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨r, hr, hEq⟩ := hx
    let N : Set X := Subtype.val ⁻¹' Metric.ball x.1 (r / 2)
    have hNopen : IsOpen N := Metric.isOpen_ball.preimage continuous_subtype_val
    have hxN : x ∈ N := by simp [N, hr]
    apply Filter.mem_of_superset (hNopen.mem_nhds hxN)
    intro y hy
    exact negativeEdgeGerm_stable_nearby hvw x.2 y.2 r hr hEq hy
  have hdisj : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact positive_negative_edgeGerms_disjoint
      (sub_ne_zero.mpr hvw.symm) hx hy
  have hcover : (Set.univ : Set X) ⊆ U ∪ V := by
    intro x _
    rcases hpoint x.1 x.2 with hpos | hneg
    · exact Or.inl hpos
    · exact Or.inr hneg
  have hchoice := IsPreconnected.subset_or_subset (s := (Set.univ : Set X))
    hUopen hVopen hdisj hcover (isPreconnected_univ : IsPreconnected (Set.univ : Set X))
  rcases hchoice with hU | hV
  · left
    intro p hp
    have hx : (⟨p, hp⟩ : X) ∈ U := hU (Set.mem_univ _)
    exact hx
  · right
    intro p hp
    have hx : (⟨p, hp⟩ : X) ∈ V := hV (Set.mem_univ _)
    exact hx

private theorem finiteSegmentUnion_frontier_locally_line
    (E : Finset (Plane × Plane)) (S : Set Plane) (v w p : Plane)
    (hfront : frontier S = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (hquery : segment ℝ v w ⊆ frontier S)
    (hp : p ∈ openSegment ℝ v w)
    (hnear : ∃ r > 0, ∀ z, dist z p < r →
      z ∈ Tiling.affineLine p (w - v) → z ∈ segment ℝ v w)
    (hclass : ∀ e ∈ E,
      (segment ℝ e.1 e.2 ⊆ Tiling.affineLine p (w - v)) ∨
        p ∉ segment ℝ e.1 e.2) :
    ∃ r > 0, ∀ z ∈ Metric.ball p r,
      (z ∈ frontier S ↔ z ∈ Tiling.affineLine p (w - v)) := by
  classical
  let B : Finset (Plane × Plane) := E.filter fun e =>
    ¬ segment ℝ e.1 e.2 ⊆ Tiling.affineLine p (w - v)
  let C : Set Plane := ⋃ e ∈ B, segment ℝ e.1 e.2
  have hBclosed : IsClosed C := by
    apply isClosed_biUnion_finset
    intro e he
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hpC : p ∉ C := by
    intro h
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp h
    obtain ⟨heB, hpe⟩ := Set.mem_iUnion.mp he
    have heE := (Finset.mem_filter.mp heB).1
    have hnotline := (Finset.mem_filter.mp heB).2
    rcases hclass e heE with hline | hmiss
    · exact hnotline hline
    · exact hmiss hpe
  obtain ⟨rB, hrB, hballB⟩ := Metric.isOpen_iff.mp hBclosed.isOpen_compl p hpC
  obtain ⟨rQ, hrQ, hnearQ⟩ := hnear
  refine ⟨min rB rQ, lt_min hrB hrQ, ?_⟩
  intro z hz
  have hzdist : dist z p < min rB rQ := by
    simpa [Metric.mem_ball, dist_comm] using hz
  have hzB : z ∉ C := by
    intro hzC
    have hz' : z ∈ Metric.ball p rB := by
      apply Metric.mem_ball.mpr
      exact lt_of_lt_of_le hzdist (min_le_left _ _)
    exact (hballB hz') hzC
  constructor
  · intro hzfront
    rw [hfront] at hzfront
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hzfront
    obtain ⟨heE, hze⟩ := Set.mem_iUnion.mp he
    by_cases hline : segment ℝ e.1 e.2 ⊆ Tiling.affineLine p (w - v)
    · exact hline hze
    · have hmemB : e ∈ B := Finset.mem_filter.mpr ⟨heE, hline⟩
      exact False.elim (hzB (Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨hmemB, hze⟩⟩))
  · intro hzline
    have hz' : dist z p < rQ := lt_of_lt_of_le hz (min_le_right _ _)
    exact hquery (hnearQ z hz' hzline)

private theorem polygonal_local_frontier_line_to_germ
    {S : Set Plane} (hS : Tiling.IsPolygonal S) {p d : Plane} (hd : d ≠ 0)
    {r : ℝ} (hr : 0 < r)
    (hline : ∀ z ∈ Metric.ball p r,
      (z ∈ frontier S ↔ z ∈ Tiling.affineLine p d)) :
    positiveEdgeGerm S d p ∨ negativeEdgeGerm S d p := by
  rcases Tiling.local_eq_closedHalfPlane hd hr hS.closure_interior hline with hpos | hneg
  · exact Or.inl ⟨r, hr, hpos⟩
  · exact Or.inr ⟨r, hr, hneg⟩

private theorem openSegment_line_neighborhood
    {v w p : Plane} (hvw : v ≠ w) (hp : p ∈ openSegment ℝ v w) :
    ∃ r > 0, ∀ z, dist z p < r → z ∈ Tiling.affineLine p (w - v) →
      z ∈ segment ℝ v w := by
  rw [openSegment_eq_image_lineMap] at hp
  rcases hp with ⟨t, ht, hpt⟩
  have hd : 0 < ‖w - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvw.symm)
  let r : ℝ := min t (1 - t) * ‖w - v‖
  have hr : 0 < r := by
    dsimp [r]
    exact mul_pos (lt_min ht.1 (by linarith [ht.2])) hd
  refine ⟨r, hr, ?_⟩
  intro z hz hzline
  obtain ⟨u, hu⟩ :=
    (Tiling.mem_affineLine_iff_exists_smul (sub_ne_zero.mpr hvw.symm)).mp hzline
  have hdistEq : dist z p = |u| * ‖w - v‖ := by
    rw [hu, dist_eq_norm]
    simp [norm_smul, Real.norm_eq_abs]
  have hdist : |u| * ‖w - v‖ < r := by
    rw [← hdistEq]
    exact hz
  have huabs : |u| < min t (1 - t) := by
    have hm := hdist
    dsimp [r] at hm
    nlinarith [hd, hm]
  have huLower : -t < u := by
    have h := abs_lt.mp huabs
    exact lt_of_le_of_lt (neg_le_neg (min_le_left t (1 - t))) h.1
  have huUpper : u < 1 - t := by
    have h := abs_lt.mp huabs
    exact lt_of_lt_of_le h.2 (min_le_right t (1 - t))
  have hparam : 0 ≤ t + u ∧ t + u ≤ 1 := by
    constructor <;> linarith
  rw [segment_eq_image_lineMap]
  refine ⟨t + u, hparam, ?_⟩
  rw [← hpt] at hu
  have hnext : AffineMap.lineMap v w (t + 1) =
      AffineMap.lineMap v w t + (w - v) := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hcomp := lineMap_lineMap_apply v w t (t + 1) u
  calc
    AffineMap.lineMap v w (t + u) =
        AffineMap.lineMap (AffineMap.lineMap v w t) (AffineMap.lineMap v w (t + 1)) u :=
      by simpa [add_sub_cancel_right] using hcomp.symm
    _ = AffineMap.lineMap v w t + u • (w - v) := by
      rw [hnext]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    _ = z := hu.symm

private theorem homeomorph_preimage_openSegment_of_segment_image
    (H : Plane ≃ₜ Plane) {v w v' w' y : Plane}
    (hvw : v ≠ w) (hv'w' : v' ≠ w')
    (himage : H '' segment ℝ v w = segment ℝ v' w')
    (hv : H v = v') (hw : H w = w')
    (hy : y ∈ openSegment ℝ v' w') :
    H.symm y ∈ openSegment ℝ v w := by
  have hySeg : y ∈ segment ℝ v' w' := openSegment_subset_segment ℝ v' w' hy
  have hyImage : y ∈ H '' segment ℝ v w := by rw [himage]; exact hySeg
  obtain ⟨x, hxSeg, hxy⟩ := hyImage
  have hx : x = H.symm y := by
    apply H.injective
    simpa using hxy
  subst x
  have hleft' : v' ∉ openSegment ℝ v' w' := by
    intro h
    have heq : v' = w' := (left_mem_openSegment_iff).mp h
    exact hv'w' heq
  have hright' : w' ∉ openSegment ℝ v' w' := by
    intro h
    have heq : v' = w' := (right_mem_openSegment_iff).mp h
    exact hv'w' heq
  have hleft : H.symm y ≠ v := by
    intro h
    have heq : y = v' := by
      calc
        y = H (H.symm y) := (H.apply_symm_apply y).symm
        _ = H v := by rw [h]
        _ = v' := hv
    exact hleft' (heq ▸ hy)
  have hright : H.symm y ≠ w := by
    intro h
    have heq : y = w' := by
      calc
        y = H (H.symm y) := (H.apply_symm_apply y).symm
        _ = H w := by rw [h]
        _ = w' := hw
    exact hright' (heq ▸ hy)
  exact mem_openSegment_of_ne_left_right hleft.symm hright.symm hxSeg

private theorem direction_mem_span_of_frontier_line_germs
    (S : Set Plane) (p d e : Plane) (hd : d ≠ 0) (he : e ≠ 0)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hfrontD : ∀ z ∈ Metric.ball p r,
      (z ∈ frontier S ↔ z ∈ Tiling.affineLine p d))
    (hfrontE : ∀ z ∈ Metric.ball p s,
      (z ∈ frontier S ↔ z ∈ Tiling.affineLine p e)) :
    d ∈ ℝ ∙ e := by
  let R := min r s
  let t := R / (2 * (‖d‖ + 1))
  let q := p + t • d
  have hR : 0 < R := lt_min hr hs
  have ht : 0 < t := by dsimp [t]; positivity
  have hdist : dist q p < R := by
    have hmul : t * ‖d‖ < R := by
      have hden : 0 < 2 * (‖d‖ + 1) := by positivity
      dsimp [t]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hden).2
      nlinarith [norm_nonneg d]
    have hnorm : dist q p = t * ‖d‖ := by
      rw [dist_eq_norm]
      dsimp [q]
      rw [add_sub_cancel_left]
      simp [Complex.norm_mul, Real.norm_ofNat, abs_of_pos ht]
    rw [hnorm]
    exact hmul
  have hballr : q ∈ Metric.ball p r := by
    rw [Metric.mem_ball]
    exact hdist.trans_le (min_le_left _ _)
  have hballs : q ∈ Metric.ball p s := by
    rw [Metric.mem_ball]
    exact hdist.trans_le (min_le_right _ _)
  have hqline : q ∈ Tiling.affineLine p d := by
    rw [Tiling.mem_affineLine_iff_exists_smul hd]
    exact ⟨t, rfl⟩
  have hqfront : q ∈ frontier S := (hfrontD q hballr).mpr hqline
  have hqlineE : q ∈ Tiling.affineLine p e := (hfrontE q hballs).mp hqfront
  obtain ⟨u, hu⟩ := (Tiling.mem_affineLine_iff_exists_smul he).mp hqlineE
  have hsmul : t • d = u • e := by
    have hqeq : p + t • d = p + u • e := by
      simpa [q] using hu
    exact add_left_cancel hqeq
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hdeq : d = (u / t) • e := by
    calc
      d = t⁻¹ • (t • d) := by rw [smul_smul]; simp [ht0]
      _ = t⁻¹ • (u • e) := by rw [hsmul]
      _ = (u / t) • e := by rw [smul_smul]; congr 1 <;> field_simp
  rw [Submodule.mem_span_singleton]
  exact ⟨u / t, hdeq.symm⟩

private theorem overlapping_vertexFree_edge_directions_parallel
    {S : Set Plane} (hS : Tiling.IsPolygonal S)
    {a b c d x : Plane} (hab : a ≠ b) (hcd : c ≠ d)
    (hfront₁ : openSegment ℝ a b ⊆ frontier S)
    (hfront₂ : openSegment ℝ c d ⊆ frontier S)
    (hfree₁ : ∀ p ∈ openSegment ℝ a b, p ∉ Tiling.vertexSet S)
    (hx₁ : x ∈ openSegment ℝ a b) (hx₂ : x ∈ openSegment ℝ c d) :
    b - a ∈ ℝ ∙ (d - c) := by
  have hxfree := hfree₁ x hx₁
  obtain ⟨r, hr, hline₁⟩ := intrinsicSegment_frontier_is_supportingLine
    hS hab hfront₁ x hx₁ hxfree
  obtain ⟨s, hs, hline₂⟩ := intrinsicSegment_frontier_is_supportingLine
    hS hcd hfront₂ x hx₂ hxfree
  exact direction_mem_span_of_frontier_line_germs S x (b - a) (d - c)
    (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hcd.symm) hr hs hline₁ hline₂

private theorem normalEval_lineMap_sub_left
    (n : RationalNormal) (a b : Plane) (t : ℝ) :
    normalEval n ((AffineMap.lineMap a b) t - a) = t * normalEval n (b - a) := by
  have hsub : (AffineMap.lineMap a b) t - a = t • (b - a) := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [hsub, normalEval_smul]

private theorem normalEval_zero_on_openEdge
    (n : RationalNormal) {a b x : Plane}
    (hzero : normalEval n (b - a) = 0)
    (hx : x ∈ openSegment ℝ a b) : normalEval n (x - a) = 0 := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  rw [normalEval_lineMap_sub_left, hzero]
  ring

private theorem normalEval_zero_on_segment
    (n : RationalNormal) {a b x o : Plane}
    (ha : normalEval n (a - o) = 0) (hb : normalEval n (b - o) = 0)
    (hx : x ∈ segment ℝ a b) : normalEval n (x - o) = 0 := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have hxa : normalEval n ((AffineMap.lineMap a b) t - a) = 0 := by
    rw [normalEval_lineMap_sub_left]
    have hbo := hb
    have hao := ha
    rw [normalEval_sub] at hbo hao
    have hdiff : normalEval n (b - a) = 0 := by
      rw [normalEval_sub]
      linarith
    rw [hdiff]
    ring
  have hsplit : (AffineMap.lineMap a b) t - o =
      ((AffineMap.lineMap a b) t - a) + (a - o) := by abel
  rw [hsplit, normalEval_add, hxa, ha]
  simp

private theorem transportedPrimitiveEdge_incidence_classification
    (K : PolygonalRegion) (E : Finset (Plane × Plane))
    (hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧
      e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support ∧
      segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet K.support)
    (H : Plane ≃ₜ Plane) (φ : ℝ →ₗ[ℚ] ℚ)
    (hanchors : ∀ z ∈ E.image Prod.fst ∪ E.image Prod.snd,
      H z = deformPoint φ z)
    (hsegments : ∀ e ∈ E, H '' segment ℝ e.1 e.2 =
      segment ℝ (deformPoint φ e.1) (deformPoint φ e.2))
    (hscale : ∀ e ∈ E, ∃ c : ℝ, 0 < c ∧
      deformPoint φ e.2 - deformPoint φ e.1 = c • (e.2 - e.1))
    (e : Plane × Plane) (he : e ∈ E) (n : RationalNormal)
    (hn : normalEval n (e.2 - e.1) = 0)
    (hker : ∀ z, normalEval n z = 0 ↔ z ∈ ℝ ∙ (e.2 - e.1))
    (y : Plane) (hy : y ∈ openSegment ℝ (deformPoint φ e.1) (deformPoint φ e.2)) :
    ∀ f ∈ E,
      (segment ℝ (deformPoint φ f.1) (deformPoint φ f.2) ⊆
        Tiling.affineLine y (e.2 - e.1)) ∨
        y ∉ segment ℝ (deformPoint φ f.1) (deformPoint φ f.2) := by
  intro f hf
  let d := e.2 - e.1
  let v := deformPoint φ e.1
  let vf := deformPoint φ f.1
  let wf := deformPoint φ f.2
  have hneE := (hprimitive e he).1
  have hfreeE := (hprimitive e he).2.2.2.2
  have hneF := (hprimitive f hf).1
  have hvF := (hprimitive f hf).2.1
  have hwF := (hprimitive f hf).2.2.1
  have hfrontE := (hprimitive e he).2.2.2.1
  have hfrontF := (hprimitive f hf).2.2.2.1
  have hfreeF := (hprimitive f hf).2.2.2.2
  obtain ⟨cE, hcE, hvecE⟩ := hscale e he
  have hvwTarget : deformPoint φ e.1 ≠ deformPoint φ e.2 := by
    intro h
    have hzero : cE • (e.2 - e.1) = 0 := by
      rw [← hvecE]
      simp [h]
    rcases smul_eq_zero.mp hzero with hc | hd
    · exact (ne_of_gt hcE) hc
    · exact hneE (sub_eq_zero.mp hd).symm
  have he1anchor : H e.1 = deformPoint φ e.1 := by
    apply hanchors
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  have he2anchor : H e.2 = deformPoint φ e.2 := by
    apply hanchors
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  have hxOpen : H.symm y ∈ openSegment ℝ e.1 e.2 :=
    homeomorph_preimage_openSegment_of_segment_image H hneE
      hvwTarget
      (hsegments e he) he1anchor he2anchor hy
  by_cases hmem : y ∈ segment ℝ vf wf
  · have hsourceF : H.symm y ∈ segment ℝ f.1 f.2 := by
      have hyimage : y ∈ H '' segment ℝ f.1 f.2 := by rw [hsegments f hf]; exact hmem
      obtain ⟨x, hx, hxy⟩ := hyimage
      have hxEq : x = H.symm y := by
        apply H.injective
        calc
          H x = y := hxy
          _ = H (H.symm y) := (H.apply_symm_apply y).symm
      simpa [hxEq] using hx
    have hxNotVertex : H.symm y ∉ Tiling.vertexSet K.support := hfreeE _ hxOpen
    have hxNeF : H.symm y ≠ f.1 := by
      intro h
      exact hxNotVertex (h ▸ hvF)
    have hxNeW : H.symm y ≠ f.2 := by
      intro h
      exact hxNotVertex (h ▸ hwF)
    have hxOpenF : H.symm y ∈ openSegment ℝ f.1 f.2 :=
      mem_openSegment_of_ne_left_right hxNeF.symm hxNeW.symm hsourceF
    have hfrontOpenE : openSegment ℝ e.1 e.2 ⊆ frontier K.support :=
      fun z hz => hfrontE (openSegment_subset_segment ℝ _ _ hz)
    have hfrontOpenF : openSegment ℝ f.1 f.2 ⊆ frontier K.support :=
      fun z hz => hfrontF (openSegment_subset_segment ℝ _ _ hz)
    have hparallel := overlapping_vertexFree_edge_directions_parallel
      K.isPolygonal hneF hneE hfrontOpenF hfrontOpenE hfreeF hxOpenF hxOpen
    obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton.mp hparallel)
    have ha' := ha.symm
    change f.2 - f.1 = a • (e.2 - e.1) at ha'
    have hdf : normalEval n (f.2 - f.1) = 0 := by
      calc
        normalEval n (f.2 - f.1) = normalEval n (a • d) := by simpa [d] using congrArg (normalEval n) ha'
        _ = a * normalEval n d := normalEval_smul n a d
        _ = 0 := by rw [hn]; ring
    have hxf : normalEval n (H.symm y - f.1) = 0 :=
      normalEval_zero_on_openEdge n hdf hxOpenF
    have hxe : normalEval n (H.symm y - e.1) = 0 :=
      normalEval_zero_on_openEdge n hn hxOpen
    have hf1x : normalEval n (f.1 - H.symm y) = 0 := by
      rw [normalEval_sub] at hxf ⊢
      linarith
    have hf1e : normalEval n (f.1 - e.1) = 0 := by
      rw [show f.1 - e.1 = (f.1 - H.symm y) + (H.symm y - e.1) by abel,
        normalEval_add, hf1x, hxe]
      simp
    have hf2e : normalEval n (f.2 - e.1) = 0 := by
      rw [show f.2 - e.1 = (f.2 - f.1) + (f.1 - e.1) by abel,
        normalEval_add, hdf, hf1e]
      simp
    have hdeformEval (a b : Plane) (hz : normalEval n (a - b) = 0) :
        normalEval n (deformPoint φ a - deformPoint φ b) = 0 := by
      have hcomm := normalEval_deformPoint_commutes_local φ n (a - b)
      have hsub : deformPoint φ a - deformPoint φ b = deformPoint φ (a - b) := by
        apply Complex.ext <;> simp [deformPoint, map_sub, Complex.sub_re, Complex.sub_im]
      rw [hsub, hcomm, hz]
      simp
    have hvf : normalEval n (vf - v) = 0 := hdeformEval f.1 e.1 hf1e
    have hwf : normalEval n (wf - v) = 0 := hdeformEval f.2 e.1 hf2e
    have hve : normalEval n (deformPoint φ e.2 - v) = 0 := hdeformEval e.2 e.1 hn
    have hyv : normalEval n (y - v) = 0 :=
      normalEval_zero_on_openEdge n hve hy
    apply Or.inl
    intro z hz
    have hzv : normalEval n (z - v) = 0 :=
      normalEval_zero_on_segment n hvf hwf hz
    have hzy : normalEval n (z - y) = 0 := by
      have heq : z - y = (z - v) - (y - v) := by abel
      rw [heq, normalEval_sub, hzv, hyv]
      simp
    have hspan : z - y ∈ ℝ ∙ d := (hker (z - y)).mp hzy
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hspan
    apply (Tiling.mem_affineLine_iff_exists_smul (sub_ne_zero.mpr hneE.symm)).mpr
    refine ⟨t, ?_⟩
    calc
      z = y + (z - y) := by abel
      _ = y + t • d := by rw [ht]
  · exact Or.inr hmem

private theorem transportedPrimitiveEdge_orientation_from_midpoint
    {S : Set Plane} (hS : Tiling.IsPolygonal S) (E : Finset (Plane × Plane))
    (v w m : Plane) (hvw : v ≠ w) (hmid : m ∈ openSegment ℝ v w)
    (hfront : frontier S = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (he : (v, w) ∈ E)
    (hclass : ∀ p ∈ openSegment ℝ v w, ∀ e ∈ E,
      (segment ℝ e.1 e.2 ⊆ Tiling.affineLine p (w - v)) ∨
        p ∉ segment ℝ e.1 e.2)
    (hmidGerm : positiveEdgeGerm S (w - v) m ∨ negativeEdgeGerm S (w - v) m) :
    (∀ p ∈ openSegment ℝ v w, positiveEdgeGerm S (w - v) p) ∨
      (∀ p ∈ openSegment ℝ v w, negativeEdgeGerm S (w - v) p) := by
  have hquery : segment ℝ v w ⊆ frontier S := by
    intro z hz
    rw [hfront]
    exact Set.mem_iUnion.mpr ⟨(v, w), Set.mem_iUnion.mpr ⟨he, hz⟩⟩
  have hpoint : ∀ p ∈ openSegment ℝ v w,
      positiveEdgeGerm S (w - v) p ∨ negativeEdgeGerm S (w - v) p := by
    intro p hp
    obtain ⟨r, hr, hlocal⟩ := finiteSegmentUnion_frontier_locally_line
      E S v w p hfront hquery hp (openSegment_line_neighborhood hvw hp)
      (fun e he => hclass p hp e he)
    exact polygonal_local_frontier_line_to_germ hS
      (sub_ne_zero.mpr hvw.symm) hr hlocal
  rcases intrinsicSegment_orientation_constant_of_pointwise_germs hvw hpoint
    with hpos | hneg
  · exact Or.inl hpos
  · rcases hmidGerm with hmidPos | hmidNeg
    · exact False.elim (positive_negative_edgeGerms_disjoint
        (sub_ne_zero.mpr hvw.symm) hmidPos (hneg m hmid))
    · exact Or.inr hneg

private theorem affineLine_smul_eq (a d : Plane) (c : ℝ)
    (hc : 0 < c) (hd : d ≠ 0) :
    Tiling.affineLine a (c • d) = Tiling.affineLine a d := by
  ext z
  rw [Tiling.mem_affineLine_iff_exists_smul (smul_ne_zero (ne_of_gt hc) hd),
    Tiling.mem_affineLine_iff_exists_smul hd]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t * c, ?_⟩
    simp only [smul_smul]
  · rintro ⟨t, rfl⟩
    refine ⟨t / c, ?_⟩
    rw [smul_smul]
    congr 1
    field_simp [ne_of_gt hc]

private theorem positiveEdgeGerm_smul_pos_iff
    (A : Set Plane) (d p : Plane) (c : ℝ) (hc : 0 < c) :
    positiveEdgeGerm A (c • d) p ↔ positiveEdgeGerm A d p := by
  have hhalf : Tiling.positiveHalfPlane p (c • d) = Tiling.positiveHalfPlane p d := by
    ext q
    have hs : Tiling.signedSide p (c • d) q = c * Tiling.signedSide p d q := by
      simp [Tiling.signedSide, Tiling.planarCross, Complex.smul_re, Complex.smul_im]
      ring
    rw [Tiling.mem_positiveHalfPlane, Tiling.mem_positiveHalfPlane, hs]
    exact (mul_nonneg_iff_of_pos_left hc)
  constructor <;> rintro ⟨r, hr, hEq⟩ <;> refine ⟨r, hr, ?_⟩
  · simpa only [hhalf] using hEq
  · simpa only [← hhalf] using hEq

private theorem negativeEdgeGerm_smul_pos_iff
    (A : Set Plane) (d p : Plane) (c : ℝ) (hc : 0 < c) :
    negativeEdgeGerm A (c • d) p ↔ negativeEdgeGerm A d p := by
  have hhalf : Tiling.negativeHalfPlane p (c • d) = Tiling.negativeHalfPlane p d := by
    ext q
    have hs : Tiling.signedSide p (c • d) q = c * Tiling.signedSide p d q := by
      simp [Tiling.signedSide, Tiling.planarCross, Complex.smul_re, Complex.smul_im]
      ring
    rw [Tiling.mem_negativeHalfPlane, Tiling.mem_negativeHalfPlane, hs]
    constructor
    · intro h
      by_contra hn
      have hx : 0 < Tiling.signedSide p d q := lt_of_not_ge hn
      nlinarith [mul_pos hc hx]
    · intro h
      exact mul_nonpos_of_nonneg_of_nonpos hc.le h
  constructor <;> rintro ⟨r, hr, hEq⟩ <;> refine ⟨r, hr, ?_⟩
  · simpa only [hhalf] using hEq
  · simpa only [← hhalf] using hEq

private theorem rationalPrimitiveEdges_uniformSameSide_transport
    (K : PolygonalRegion) (P : PolyhedralCode)
    (hP : polyhedralSupport P = K.support) (E : Finset (Plane × Plane))
    (hrat : ∀ e ∈ E,
      Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hprimitive : ∀ e ∈ E,
      e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet K.support)
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∃ H : Plane ≃ₜ Plane,
            (∀ z ∈ E.image Prod.fst ∪ E.image Prod.snd,
              H z = deformPoint φ z) ∧
            H '' K.support = Kφ.support ∧
            (∀ e ∈ E, H '' segment ℝ e.1 e.2 =
              segment ℝ (deformPoint φ e.1) (deformPoint φ e.2)) ∧
            frontier Kφ.support = ⋃ e ∈ E,
              segment ℝ (deformPoint φ e.1) (deformPoint φ e.2) ∧
            ∀ e ∈ E,
              ((∀ p ∈ openSegment ℝ e.1 e.2,
                  positiveEdgeGerm K.support (e.2 - e.1) p) →
                ∀ p ∈ openSegment ℝ (deformPoint φ e.1) (deformPoint φ e.2),
                  positiveEdgeGerm (deformedPolyhedralSupport P φ) (e.2 - e.1) p) ∧
              ((∀ p ∈ openSegment ℝ e.1 e.2,
                  negativeEdgeGerm K.support (e.2 - e.1) p) →
                ∀ p ∈ openSegment ℝ (deformPoint φ e.1) (deformPoint φ e.2),
                  negativeEdgeGerm (deformedPolyhedralSupport P φ) (e.2 - e.1) p) := by
  classical
  obtain ⟨Fc, εc, l, hεc, hl, hcontrol⟩ :=
    finiteRationalEdges_positiveHomotheties E hrat
  have hE : ∀ e ∈ E, e.1 ≠ e.2 ∧
      Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1) :=
    fun e he => ⟨(hprimitive e he).1, hrat e he⟩
  obtain ⟨Ft, εt, htε, htransport⟩ :=
    rationalPrimitiveFrontier_transport K P hP E hE hcover
  obtain ⟨Fm, εm, R, hmε, hR, hmidpoints⟩ :=
    rationalPrimitiveEdges_uniformMidpointGerms K P hP E
  let F := Ft ∪ Fm ∪ Fc
  let ε := min (min εt εm) εc
  refine ⟨F, ε, R, lt_min (lt_min htε hmε) hεc, hR, ?_⟩
  intro φ hφ Kφ hKφ
  have hφt : IsFiniteApproximation Ft εt φ := by
    refine ⟨hφ.1, ?_⟩
    intro x hx
    exact (hφ.2 x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))).trans_le
      (le_trans (min_le_left _ _) (min_le_left _ _))
  have hφm : IsFiniteApproximation Fm εm φ := by
    refine ⟨hφ.1, ?_⟩
    intro x hx
    exact (hφ.2 x (Finset.mem_union_left _ (Finset.mem_union_right _ hx))).trans_le
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have hφc : IsFiniteApproximation Fc εc φ := by
    refine ⟨hφ.1, ?_⟩
    intro x hx
    exact (hφ.2 x (Finset.mem_union_right _ hx)).trans_le (min_le_right _ _)
  obtain ⟨H, hanchors, hsupport, hsegments, hfront⟩ := htransport φ hφt Kφ hKφ
  have hscale : ∀ e ∈ E, ∃ c : ℝ, 0 < c ∧
      deformPoint φ e.2 - deformPoint φ e.1 = c • (e.2 - e.1) := by
    intro e he
    obtain ⟨c, hc₁, hc₂, hvec, _⟩ := hcontrol φ hφc e he
    exact ⟨c, lt_of_lt_of_le (by norm_num : 0 < (1 / 2 : ℝ)) hc₁, hvec⟩
  refine ⟨H, hanchors, hsupport, hsegments, hfront, ?_⟩
  intro e he
  obtain ⟨hmOpen, hmPos, hmNeg⟩ := hmidpoints φ hφm e he
  let d := e.2 - e.1
  obtain ⟨c, hc, hvec⟩ := hscale e he
  let dφ := deformPoint φ e.2 - deformPoint φ e.1
  let n : RationalNormal := Classical.choose (rationalDirection_hasNormal
    (Submodule.span ℝ ({d} : Set Plane))
    (finrank_span_singleton (sub_ne_zero.mpr (hprimitive e he).1.symm)) (hrat e he).2)
  have hnDir : normalDirection n = Submodule.span ℝ ({d} : Set Plane) :=
    Classical.choose_spec (rationalDirection_hasNormal
      (Submodule.span ℝ ({d} : Set Plane))
      (finrank_span_singleton (sub_ne_zero.mpr (hprimitive e he).1.symm)) (hrat e he).2)
  have hn : normalEval n d = 0 := by
    apply (normalDirection_mem_iff n d).mp
    rw [hnDir]
    exact Submodule.mem_span_singleton_self d
  have hker : ∀ z, normalEval n z = 0 ↔ z ∈ ℝ ∙ d := by
    intro z
    rw [← normalDirection_mem_iff n z, hnDir]
  have hclass : ∀ y ∈ openSegment ℝ (deformPoint φ e.1) (deformPoint φ e.2),
      ∀ f ∈ E,
        (segment ℝ (deformPoint φ f.1) (deformPoint φ f.2) ⊆
            Tiling.affineLine y d) ∨
          y ∉ segment ℝ (deformPoint φ f.1) (deformPoint φ f.2) := by
    intro y hy
    exact transportedPrimitiveEdge_incidence_classification K E
      (fun f hf => hprimitive f hf) H φ hanchors hsegments hscale e he n hn hker y hy
  have hneTarget : deformPoint φ e.1 ≠ deformPoint φ e.2 := by
    intro hEq
    have hzero : c • d = 0 := by rw [← hvec]; simp [hEq]
    rcases smul_eq_zero.mp hzero with hc0 | hd0
    · exact (ne_of_gt hc) hc0
    · exact (hprimitive e he).1 (sub_eq_zero.mp hd0).symm
  have hfrontImage : frontier Kφ.support =
      ⋃ g ∈ E.image (fun f => (deformPoint φ f.1, deformPoint φ f.2)),
        segment ℝ g.1 g.2 := by
    rw [hfront]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨f, hf, hz⟩
      exact ⟨(deformPoint φ f.1, deformPoint φ f.2),
        Finset.mem_image.mpr ⟨f, hf, rfl⟩, hz⟩
    · rintro ⟨g, hg, hz⟩
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
      exact ⟨f, hf, hz⟩
  have hclassImage : ∀ y ∈ openSegment ℝ (deformPoint φ e.1) (deformPoint φ e.2),
      ∀ g ∈ E.image (fun f => (deformPoint φ f.1, deformPoint φ f.2)),
        (segment ℝ g.1 g.2 ⊆ Tiling.affineLine y dφ) ∨
          y ∉ segment ℝ g.1 g.2 := by
    intro y hy g hg
    obtain ⟨f, hf, hfg⟩ := Finset.mem_image.mp hg
    have hleft := congrArg Prod.fst hfg
    have hright := congrArg Prod.snd hfg
    rw [← hleft, ← hright]
    rcases hclass y hy f hf with hsub | hmiss
    · left
      have hline := affineLine_smul_eq y d c hc
        (sub_ne_zero.mpr (hprimitive e he).1.symm)
      have hline' : Tiling.affineLine y dφ = Tiling.affineLine y d := by
        simpa [dφ, hvec] using hline
      rw [hline']
      exact hsub
    · exact Or.inr hmiss
  constructor
  · intro hsource
    have htargetMid := (positiveEdgeGerm_smul_pos_iff
      (deformedPolyhedralSupport P φ) d
      (deformPoint φ ((AffineMap.lineMap e.1 e.2) (1 / 2 : ℝ))) c hc).mpr (hmPos hsource)
    have htargetMid' : positiveEdgeGerm Kφ.support dφ
        (deformPoint φ ((AffineMap.lineMap e.1 e.2) (1 / 2 : ℝ))) := by
      simpa [hKφ, dφ, hvec] using htargetMid
    have htargetOrientation := transportedPrimitiveEdge_orientation_from_midpoint
      Kφ.isPolygonal (E.image fun f => (deformPoint φ f.1, deformPoint φ f.2))
      (deformPoint φ e.1) (deformPoint φ e.2)
      (deformPoint φ ((AffineMap.lineMap e.1 e.2) (1 / 2 : ℝ)))
      hneTarget hmOpen hfrontImage
      (Finset.mem_image.mpr ⟨e, he, rfl⟩) hclassImage
      (Or.inl htargetMid')
    rcases htargetOrientation with hpos | hneg
    · intro p hp
      have hpos' : positiveEdgeGerm Kφ.support (c • d) p := by
        simpa [dφ, hvec] using hpos p hp
      simpa [hKφ] using (positiveEdgeGerm_smul_pos_iff
        Kφ.support d p c hc).mp hpos'
    · exact False.elim (positive_negative_edgeGerms_disjoint
        (sub_ne_zero.mpr hneTarget.symm) htargetMid' (hneg _ hmOpen))
  · intro hsource
    have htargetMid := (negativeEdgeGerm_smul_pos_iff
      (deformedPolyhedralSupport P φ) d
      (deformPoint φ ((AffineMap.lineMap e.1 e.2) (1 / 2 : ℝ))) c hc).mpr (hmNeg hsource)
    have htargetMid' : negativeEdgeGerm Kφ.support dφ
        (deformPoint φ ((AffineMap.lineMap e.1 e.2) (1 / 2 : ℝ))) := by
      simpa [hKφ, dφ, hvec] using htargetMid
    have htargetOrientation := transportedPrimitiveEdge_orientation_from_midpoint
      Kφ.isPolygonal (E.image fun f => (deformPoint φ f.1, deformPoint φ f.2))
      (deformPoint φ e.1) (deformPoint φ e.2)
      (deformPoint φ ((AffineMap.lineMap e.1 e.2) (1 / 2 : ℝ)))
      hneTarget hmOpen hfrontImage
      (Finset.mem_image.mpr ⟨e, he, rfl⟩) hclassImage
      (Or.inr htargetMid')
    rcases htargetOrientation with hpos | hneg
    · exact False.elim (positive_negative_edgeGerms_disjoint
        (sub_ne_zero.mpr hneTarget.symm) (hpos _ hmOpen) htargetMid')
    · intro p hp
      have hneg' : negativeEdgeGerm Kφ.support (c • d) p := by
        simpa [dφ, hvec] using hneg p hp
      simpa [hKφ] using (negativeEdgeGerm_smul_pos_iff
        Kφ.support d p c hc).mp hneg'

private theorem deformedPrimitiveOccurrence_shortFrontierRay
    (Kφ : PolygonalRegion) (φ : ℝ →ₗ[ℚ] ℚ) (s p d : Plane) (hd : d ≠ 0)
    (e : Plane × Plane) (c k l : ℝ) (hc : 0 < c) (hk : 0 < k)
    (hends : (s + e.1 = p ∧ s + e.2 = p + c • d) ∨
      (s + e.2 = p ∧ s + e.1 = p + c • d))
    (hvec : deformPoint φ e.2 - deformPoint φ e.1 = k • (e.2 - e.1))
    (hlength : l ≤ dist (deformPoint φ e.1) (deformPoint φ e.2))
    (hfront : segment ℝ (deformPoint φ e.1) (deformPoint φ e.2) ⊆ frontier Kφ.support) :
    ∀ q : ℝ, 0 ≤ q → dist (q • d) 0 ≤ l →
      deformPoint φ p + q • d ∈ frontier (deformPoint φ s +ᵥ Kφ.support) := by
  have hmapadd (a b : Plane) : deformPoint φ (a + b) =
      deformPoint φ a + deformPoint φ b := (deformPointLinear φ).map_add a b
  have advance (v w : Plane) (hv : s + v = p) (hw : s + w = p + c • d)
      (hvw : deformPoint φ w - deformPoint φ v = k • (w - v))
      (hL : l ≤ dist (deformPoint φ v) (deformPoint φ w))
      (hF : segment ℝ (deformPoint φ v) (deformPoint φ w) ⊆ frontier Kφ.support) :
      ∀ q : ℝ, 0 ≤ q → dist (q • d) 0 ≤ l →
        deformPoint φ p + q • d ∈ frontier (deformPoint φ s +ᵥ Kφ.support) := by
    have hvφ : deformPoint φ s + deformPoint φ v = deformPoint φ p := by
      rw [← hmapadd, hv]
    have hdir : w - v = c • d := by
      calc
        w - v = (s + w) - (s + v) := by abel
        _ = (p + c • d) - p := by rw [hw, hv]
        _ = c • d := by abel
    have hwφ : deformPoint φ s + deformPoint φ w =
        deformPoint φ p + (k * c) • d := by
      rw [hdir, smul_smul] at hvw
      calc
        deformPoint φ s + deformPoint φ w =
            (deformPoint φ s + deformPoint φ v) +
              (deformPoint φ w - deformPoint φ v) := by abel
        _ = deformPoint φ p + (k * c) • d := by rw [hvφ, hvw]
    have hL' : l ≤ dist (deformPoint φ p) (deformPoint φ s + deformPoint φ w) := by
      rw [← hvφ, dist_add_left]
      exact hL
    intro q hq hqL
    have hsegment := sourceRay_shortParameter_mem_segment (deformPoint φ p)
      (deformPoint φ s + deformPoint φ w) d hd (mul_pos hk hc) hwφ hL' hq hqL
    rw [← hvφ] at hsegment
    have htranslate : segment ℝ (deformPoint φ s + deformPoint φ v)
        (deformPoint φ s + deformPoint φ w) =
          deformPoint φ s +ᵥ segment ℝ (deformPoint φ v) (deformPoint φ w) := by
      simpa only [vadd_eq_add] using
        (vadd_segment ℝ (deformPoint φ s) (deformPoint φ v) (deformPoint φ w)).symm
    rw [htranslate] at hsegment
    have hmem := Set.vadd_set_mono hF hsegment
    rw [hvφ] at hmem
    simpa only [frontier, closure_vadd, interior_vadd, ← Set.vadd_set_sdiff] using hmem
  rcases hends with ⟨hv, hw⟩ | ⟨hv, hw⟩
  · exact advance e.1 e.2 hv hw hvec hlength hfront
  · apply advance e.2 e.1 hv hw
    · calc
        deformPoint φ e.1 - deformPoint φ e.2 =
            -(deformPoint φ e.2 - deformPoint φ e.1) := by abel
        _ = -(k • (e.2 - e.1)) := congrArg Neg.neg hvec
        _ = k • (e.1 - e.2) := by rw [← smul_neg, neg_sub]
    · simpa only [dist_comm] using hlength
    · simpa only [segment_symm] using hfront

/-- Half-star tangent carriers have a uniform physical target extension,
obtained from whole actual primitive lengths rather than from mapping a source
radius.  Applying this to both `d` and `-d` covers both tangent directions. -/
private theorem originalHalfVertexStar_uniformPhysicalTangentExtension
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ x ∈ openSegment ℝ e.1 e.2, x ∉ Tiling.vertexSet K.support)
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε l : ℝ, 0 < ε ∧ 0 < l ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ p t : Plane, t ∈ T → p ∈ t +ᵥ Tiling.vertexSet K.support →
            originalVertexConeUnion K P T p = Set.univ ∨
              ∃ f : Plane →L[ℝ] ℝ, ∃ u : Plane, f u = 1 ∧
                originalVertexConeUnion K P T p = {z | f z ≤ 0} ∧
                ∀ d : Plane, d ≠ 0 → f d = 0 → ∃ s ∈ T,
                  p ∈ s +ᵥ Tiling.vertexSet K.support ∧
                  ∀ q : ℝ, 0 ≤ q → dist (q • d) 0 ≤ l →
                    deformPoint φ p + q • d ∈
                      frontier (deformPoint φ s +ᵥ Kφ.support) := by
  obtain ⟨Fs, εs, r, hεs, hr, hstar⟩ :=
    originalHalfVertexStar_uniformTangentPrimitiveOccurrences K P T hP htile E hE hcover
  obtain ⟨Fc, εc, l, hεc, hl, hlength⟩ := finiteRationalEdges_positiveHomotheties E hrat
  obtain ⟨Ft, εt, hεt, htransport⟩ := rationalPrimitiveFrontier_transport K P hP E
    (fun e he => ⟨(hE e he).1, hrat e he⟩) hcover
  let F := Fs ∪ Fc ∪ Ft
  let ε := min (min εs εc) εt
  refine ⟨F, ε, l, lt_min (lt_min hεs hεc) hεt, hl, ?_⟩
  intro φ hφ Kφ hKφ p t ht hpt
  have hφs : IsFiniteApproximation Fs εs φ := by
    refine ⟨hφ.1, ?_⟩
    intro x hx
    exact (hφ.2 x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))).trans_le
      (le_trans (min_le_left _ _) (min_le_left _ _))
  have hφc : IsFiniteApproximation Fc εc φ := by
    refine ⟨hφ.1, ?_⟩
    intro x hx
    exact (hφ.2 x (Finset.mem_union_left _ (Finset.mem_union_right _ hx))).trans_le
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have hφt : IsFiniteApproximation Ft εt φ := by
    refine ⟨hφ.1, ?_⟩
    intro x hx
    exact (hφ.2 x (Finset.mem_union_right _ hx)).trans_le (min_le_right _ _)
  obtain ⟨H, hanchors, hsupport, hsegments, hfront⟩ := htransport φ hφt Kφ hKφ
  rcases hstar φ hφs Kφ hKφ p t ht hpt with hfull | ⟨f, u, hu, hhalf, hoccurs⟩
  · exact Or.inl hfull
  · right
    refine ⟨f, u, hu, hhalf, ?_⟩
    intro d hd hfd
    obtain ⟨s, hs, hps, ⟨e, he, c, hc, hends⟩, hrays⟩ := hoccurs d hd hfd
    obtain ⟨k, hklo, hkhi, hvec, hL⟩ := hlength φ hφc e he
    refine ⟨s, hs, hps, ?_⟩
    apply deformedPrimitiveOccurrence_shortFrontierRay Kφ φ s p d hd e c k l hc
      (by linarith) hends hvec hL
    intro z hz
    rw [hfront]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩

private theorem rationalPrimitiveEdge_uniformCentralHalfPlanes
    (K : PolygonalRegion) (P : PolyhedralCode) (hP : polyhedralSupport P = K.support)
    (E : Finset (Plane × Plane))
    (hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet K.support)
    (hrational : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (e : Plane × Plane) (he : e ∈ E) (τ : ℝ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ t ∈ Icc τ (1 - τ),
            let p := AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) t
            (Kφ.support ∩ Metric.ball p r =
                Tiling.positiveHalfPlane p (e.2 - e.1) ∩ Metric.ball p r) ∨
              (Kφ.support ∩ Metric.ball p r =
                Tiling.negativeHalfPlane p (e.2 - e.1) ∩ Metric.ball p r) := by
  classical
  obtain ⟨n, hn⟩ := rationalDirection_hasNormal (ℝ ∙ (e.2 - e.1))
    (finrank_span_singleton (hrational e he).1) (hrational e he).2
  have hnormal : normalEval n (e.2 - e.1) = 0 := by
    apply (normalDirection_mem_iff n _).mp
    rw [hn]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨Fs, εs, rs, hεs, hrs, hstraight⟩ :=
    finitePrimitiveEdges_uniformCentralSupportingLine K E hprimitive e he n hnormal τ hτ hτhalf
  obtain ⟨Fa, εa, hεa, htransport⟩ := rationalPrimitiveFrontier_transport K P hP E
    (fun e he => ⟨(hprimitive e he).1, hrational e he⟩) hcover
  obtain ⟨Fl, εl, l, hεl, hl, hlength⟩ := finiteRationalEdges_positiveHomotheties E hrational
  let F := (Fs ∪ Fa) ∪ Fl
  let ε := min (min εs εa) εl
  let r := min rs (τ * l / 2)
  have hr : 0 < r := lt_min hrs (by positivity)
  refine ⟨F, ε, r, lt_min (lt_min hεs hεa) hεl, hr, ?_⟩
  intro φ hφ Kφ hKφ t ht
  have hφs : IsFiniteApproximation Fs εs φ := by
    refine ⟨hφ.1, ?_⟩
    intro x hx
    exact (hφ.2 x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))).trans_le
      ((min_le_left _ _).trans (min_le_left _ _))
  have hφa : IsFiniteApproximation Fa εa φ := by
    refine ⟨hφ.1, ?_⟩
    intro x hx
    exact (hφ.2 x (Finset.mem_union_left _ (Finset.mem_union_right _ hx))).trans_le
      ((min_le_left _ _).trans (min_le_right _ _))
  have hφl : IsFiniteApproximation Fl εl φ := by
    refine ⟨hφ.1, ?_⟩
    intro x hx
    exact (hφ.2 x (Finset.mem_union_right _ hx)).trans_le (min_le_right _ _)
  obtain ⟨H, hanchors, hsupport, hsegments, hfront⟩ := htransport φ hφa Kφ hKφ
  obtain ⟨c, hc₁, hc₂, hvec, hlen⟩ := hlength φ hφl e he
  have hc : 0 < c := by linarith
  let v := deformPoint φ e.1
  let w := deformPoint φ e.2
  let p := AffineMap.lineMap v w t
  have hwv : w - v ≠ 0 := by
    rw [hvec]
    exact smul_ne_zero hc.ne' (hrational e he).1
  have hvw : v ≠ w := by intro h; exact hwv (by rw [h]; simp)
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨hτ.trans_le ht.1, ht.2.trans_lt (by linarith)⟩
  have hrdist : r ≤ dist p v ∧ r ≤ dist p w := by
    obtain ⟨hleft, hright⟩ := lineMap_endpointDistances v w t ⟨ht01.1.le, ht01.2.le⟩
    have hdistnonneg := dist_nonneg (x := v) (y := w)
    have hleftbound : τ * l ≤ t * dist v w := by
      exact mul_le_mul ht.1 hlen hl.le ht01.1.le
    have hrightbound : τ * l ≤ (1 - t) * dist v w := by
      exact mul_le_mul (by linarith [ht.2]) hlen hl.le (sub_nonneg.mpr ht01.2.le)
    constructor
    · change r ≤ dist (AffineMap.lineMap v w t) v
      rw [hleft]
      exact (min_le_right _ _).trans ((by nlinarith : τ * l / 2 ≤ τ * l).trans hleftbound)
    · change r ≤ dist (AffineMap.lineMap v w t) w
      rw [hright]
      exact (min_le_right _ _).trans ((by nlinarith : τ * l / 2 ≤ τ * l).trans hrightbound)
  have hfrontier : ∀ z ∈ Metric.ball p r,
      (z ∈ frontier Kφ.support ↔ z ∈ Tiling.affineLine p (w - v)) := by
    intro z hz
    constructor
    · intro hzf
      rw [hfront] at hzf
      obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hzf
      obtain ⟨hfE, hzseg⟩ := Set.mem_iUnion.mp hf
      have hzero := hstraight φ hφs t ht f hfE z hzseg
        (hz.trans_le (min_le_left _ _))
      have hzker := (normalDirection_mem_iff n (z - p)).mpr hzero
      rw [hn, ← span_singleton_positiveHomothety (e.2 - e.1) c hc, ← hvec] at hzker
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hzker
      apply (Tiling.mem_affineLine_iff_exists_smul hwv).mpr
      refine ⟨s, ?_⟩
      change z = p + s • (w - v)
      rw [hs]
      abel
    · intro hzline
      have hzseg := affineLine_ball_mem_segment v w hvw t ht01 r hrdist.1 hrdist.2 z hz hzline
      rw [hfront]
      exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he, hzseg⟩⟩
  have hlocal := Tiling.local_eq_closedHalfPlane hwv hr Kφ.isPolygonal.closure_interior hfrontier
  have hplanes := orientedHalfPlanes_positiveScale p (e.2 - e.1) c hc
  change w - v = c • (e.2 - e.1) at hvec
  rw [hvec] at hlocal
  simpa only [hplanes.1, hplanes.2] using hlocal

/-- Central strips have the actual SOURCE inward sign.  The uniform radius is
the finite geometric strip radius; an unsigned disjunction is not substituted
for this signed statement. -/
private theorem rationalPrimitiveEdge_uniformCentralSameSide
    (K : PolygonalRegion) (P : PolyhedralCode) (hP : polyhedralSupport P = K.support)
    (E : Finset (Plane × Plane))
    (hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet K.support)
    (hrational : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (e : Plane × Plane) (he : e ∈ E) (τ : ℝ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (positive : Bool)
    (hsource : ∀ p ∈ openSegment ℝ e.1 e.2,
      if positive then positiveEdgeGerm K.support (e.2 - e.1) p
      else negativeEdgeGerm K.support (e.2 - e.1) p) :
    ∃ F : Finset ℝ, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ t ∈ Icc τ (1 - τ),
            let p := AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) t
            Kφ.support ∩ Metric.ball p r =
              (if positive then Tiling.positiveHalfPlane p (e.2 - e.1)
               else Tiling.negativeHalfPlane p (e.2 - e.1)) ∩ Metric.ball p r := by
  obtain ⟨F₀, ε₀, r, hε₀, hr, hstrip⟩ := rationalPrimitiveEdge_uniformCentralHalfPlanes
    K P hP E (fun e he => ⟨(hprimitive e he).1,
      (hprimitive e he).2.2.2.1, (hprimitive e he).2.2.2.2⟩)
    hrational hcover e he τ hτ hτhalf
  obtain ⟨F₁, ε₁, R, hε₁, hR, hsame⟩ :=
    rationalPrimitiveEdges_uniformSameSide_transport K P hP E hrational hprimitive hcover
  refine ⟨F₀ ∪ F₁, min ε₀ ε₁, r, lt_min hε₀ hε₁, hr, ?_⟩
  intro φ hφ Kφ hKφ t ht
  have hφ₀ := finiteApproximation_strengthen F₀ (F₀ ∪ F₁) ε₀ (min ε₀ ε₁) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφ₁ := finiteApproximation_strengthen F₁ (F₀ ∪ F₁) ε₁ (min ε₀ ε₁) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  obtain ⟨H, hanchors, hsupport, hsegments, hfront, hgerms⟩ := hsame φ hφ₁ Kφ hKφ
  let p := AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) t
  have hp : p ∈ openSegment ℝ (deformPoint φ e.1) (deformPoint φ e.2) := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, ⟨hτ.trans_le ht.1, ht.2.trans_lt (by linarith)⟩, rfl⟩
  have hd : e.2 - e.1 ≠ 0 := sub_ne_zero.mpr (hprimitive e he).1.symm
  have hlocal := hstrip φ hφ₀ Kφ hKφ t ht
  cases positive with
  | true =>
      have hpos : positiveEdgeGerm Kφ.support (e.2 - e.1) p := by
        rw [hKφ]
        exact (hgerms e he).1 (by simpa using hsource) p hp
      rcases hlocal with hposEq | hnegEq
      · exact hposEq
      · exact False.elim (positive_negative_edgeGerms_disjoint hd hpos ⟨r, hr, hnegEq⟩)
  | false =>
      have hneg : negativeEdgeGerm Kφ.support (e.2 - e.1) p := by
        rw [hKφ]
        exact (hgerms e he).2 (by simpa using hsource) p hp
      rcases hlocal with hposEq | hnegEq
      · exact False.elim (positive_negative_edgeGerms_disjoint hd ⟨r, hr, hposEq⟩ hneg)
      · exact hnegEq

/-- Central primitive strips provide actual labelled full-boundary collar
witnesses, retaining the source inward sign and the original occurrence label. -/
private theorem packingSol_constEdgeGerms_changeDirection
    (S : Set Plane) (x y d w : Plane) (c : ℝ) (hc : c ≠ 0)
    (hdir : w = c • d)
    (hproto : (∀ z ∈ openSegment ℝ x y, positiveEdgeGerm S w z) ∨
      (∀ z ∈ openSegment ℝ x y, negativeEdgeGerm S w z)) :
    (∀ z ∈ openSegment ℝ x y, positiveEdgeGerm S d z) ∨
      (∀ z ∈ openSegment ℝ x y, negativeEdgeGerm S d z) := by
  by_cases hcpos : 0 < c
  · rcases hproto with hpos | hneg
    · exact Or.inl (fun z hz => (orientedEdgeGerms_positiveScale S z d c hcpos).1.mp
        (hdir ▸ hpos z hz))
    · exact Or.inr (fun z hz => (orientedEdgeGerms_positiveScale S z d c hcpos).2.mp
        (hdir ▸ hneg z hz))
  · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
    have hdir' : w = (-c) • (-d) := by rw [hdir]; simp
    rcases hproto with hpos | hneg
    · exact Or.inr (fun z hz => (orientedEdgeGerms_negativeDirection S z d).1.mp
        ((orientedEdgeGerms_positiveScale S z (-d) (-c) (neg_pos.mpr hcneg)).1.mp
          (hdir' ▸ hpos z hz)))
    · exact Or.inl (fun z hz => (orientedEdgeGerms_negativeDirection S z d).2.mp
        ((orientedEdgeGerms_positiveScale S z (-d) (-c) (neg_pos.mpr hcneg)).2.mp
          (hdir' ▸ hneg z hz)))

private theorem packingSol_primitiveOccurrence_signedFamily
    (K : PolygonalRegion) (T : Set Plane) (E : Finset (Plane × Plane))
    (a d t : Plane) (_hd : d ≠ 0) (ht : t ∈ T)
    (e : Plane × Plane) (he : e ∈ E) (q : ℝ × ℝ) (hq : q.1 < q.2)
    (hcoords :
      (t + e.1 = a + q.1 • d ∧ t + e.2 = a + q.2 • d) ∨
      (t + e.2 = a + q.1 • d ∧ t + e.1 = a + q.2 • d))
    (hproto :
      (∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
      (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)) :
    ∃ positive : Bool, q ∈ signedCarrierIntervals K T E a d positive ∧
      ∀ u ∈ Ioo q.1 q.2,
        if positive then positiveEdgeGerm (t +ᵥ K.support) d (a + u • d)
          else negativeEdgeGerm (t +ᵥ K.support) d (a + u • d) := by
  have hdirection : ∃ c : ℝ, c ≠ 0 ∧ e.2 - e.1 = c • d := by
    rcases hcoords with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · refine ⟨q.2 - q.1, ne_of_gt (sub_pos.mpr hq), ?_⟩
      calc
        e.2 - e.1 = (t + e.2) - (t + e.1) := by abel
        _ = (a + q.2 • d) - (a + q.1 • d) := by rw [hleft, hright]
        _ = (q.2 - q.1) • d := by module
    · refine ⟨q.1 - q.2, ne_of_lt (sub_neg.mpr hq), ?_⟩
      calc
        e.2 - e.1 = (t + e.2) - (t + e.1) := by abel
        _ = (a + q.1 • d) - (a + q.2 • d) := by rw [hleft, hright]
        _ = (q.1 - q.2) • d := by module
  obtain ⟨c, hc, hdir⟩ := hdirection
  have hprotoD := packingSol_constEdgeGerms_changeDirection K.support e.1 e.2 d
    (e.2 - e.1) c hc hdir hproto
  have htranslated (u : ℝ) (hu : u ∈ Ioo q.1 q.2) :
      a + u • d ∈ t +ᵥ openSegment ℝ e.1 e.2 := by
    rw [vadd_openSegment]
    simp only [vadd_eq_add]
    rcases hcoords with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · rw [hleft, hright]
      exact carrierParameter_mem_openSegment a d q.1 q.2 u hq hu
    · rw [hleft, hright, openSegment_symm]
      exact carrierParameter_mem_openSegment a d q.1 q.2 u hq hu
  rcases hprotoD with hpos | hneg
  · have hgerm : ∀ u ∈ Ioo q.1 q.2,
        positiveEdgeGerm (t +ᵥ K.support) d (a + u • d) := by
      intro u hu
      obtain ⟨z, hz, hzu⟩ := Set.mem_vadd_set.mp (htranslated u hu)
      have hzu' : t + z = a + u • d := by simpa only [vadd_eq_add] using hzu
      simpa only [hzu'] using
        sourceRay_vadd_positiveEdgeGerm K.support t z d (hpos z hz)
    exact ⟨true, ⟨hq, t, ht, e, he, hcoords, hgerm⟩, hgerm⟩
  · have hgerm : ∀ u ∈ Ioo q.1 q.2,
        negativeEdgeGerm (t +ᵥ K.support) d (a + u • d) := by
      intro u hu
      obtain ⟨z, hz, hzu⟩ := Set.mem_vadd_set.mp (htranslated u hu)
      have hzu' : t + z = a + u • d := by simpa only [vadd_eq_add] using hzu
      simpa only [hzu'] using
        sourceRay_vadd_negativeEdgeGerm K.support t z d (hneg z hz)
    exact ⟨false, ⟨hq, t, ht, e, he, hcoords, hgerm⟩, hgerm⟩


private def packingSol_rationalTangent (n : RationalNormal) : Plane :=
  ⟨-(n.y : ℝ), (n.x : ℝ)⟩

private theorem packingSol_rationalTangent_ne_zero (n : RationalNormal) :
    packingSol_rationalTangent n ≠ 0 := by
  intro h
  have hx : (n.x : ℝ) = 0 := congrArg Complex.im h
  have hy : -(n.y : ℝ) = 0 := congrArg Complex.re h
  rcases n.nonzero with hnx | hny
  · exact hnx (by exact_mod_cast hx)
  · exact hny (by exact_mod_cast (neg_eq_zero.mp hy))

private theorem packingSol_rationalTangent_mem (n : RationalNormal) :
    packingSol_rationalTangent n ∈ normalDirection n := by
  change normalEval n (packingSol_rationalTangent n) = 0
  simp only [normalEval, packingSol_rationalTangent]
  ring

private theorem packingSol_deform_rationalTangent_smul
    (φ : ℝ →ₗ[ℚ] ℚ) (n : RationalNormal) (r : ℝ) :
    deformPoint φ (r • packingSol_rationalTangent n) =
      (φ r : ℝ) • packingSol_rationalTangent n := by
  apply Complex.ext
  · simp only [deformPoint, packingSol_rationalTangent, Complex.smul_re, smul_eq_mul]
    change (φ (r * -(n.y : ℝ)) : ℝ) = (φ r : ℝ) * -(n.y : ℝ)
    calc
      (φ (r * -(n.y : ℝ)) : ℝ) = (φ ((-n.y : ℚ) • r) : ℝ) := by
        apply congrArg (fun z : ℝ => (φ z : ℝ))
        simp only [Rat.smul_def, Rat.cast_neg]
        ring
      _ = (((-n.y : ℚ) • φ r : ℚ) : ℝ) :=
        congrArg (fun q : ℚ => (q : ℝ)) (φ.map_smul (-n.y) r)
      _ = (φ r : ℝ) * -(n.y : ℝ) := by simp [smul_eq_mul]; ring
  · simp only [deformPoint, packingSol_rationalTangent, Complex.smul_im, smul_eq_mul]
    change (φ (r * (n.x : ℝ)) : ℝ) = (φ r : ℝ) * (n.x : ℝ)
    calc
      (φ (r * (n.x : ℝ)) : ℝ) = (φ ((n.x : ℚ) • r) : ℝ) := by
        apply congrArg (fun z : ℝ => (φ z : ℝ))
        simp only [Rat.smul_def]
        ring
      _ = (((n.x : ℚ) • φ r : ℚ) : ℝ) :=
        congrArg (fun q : ℚ => (q : ℝ)) (φ.map_smul n.x r)
      _ = (φ r : ℝ) * (n.x : ℝ) := by simp [smul_eq_mul]; ring

private theorem packingSol_deform_rationalCarrierParameter
    (φ : ℝ →ₗ[ℚ] ℚ) (n : RationalNormal) (a : Plane) (r : ℝ) :
    deformPoint φ (a + r • packingSol_rationalTangent n) =
      deformPoint φ a + (φ r : ℝ) • packingSol_rationalTangent n := by
  have hmap : deformPoint φ (a + r • packingSol_rationalTangent n) =
      deformPoint φ a + deformPoint φ (r • packingSol_rationalTangent n) :=
    (deformPointLinear φ).map_add _ _
  rw [hmap, packingSol_deform_rationalTangent_smul]

private theorem occurrence_halfPlane_side_transport
    {d w : Plane} {c : ℝ} (hc : c ≠ 0) (hdir : w = c • d)
    (positive b : Bool) (hrel : b = if 0 < c then positive else !positive) :
    ∀ y z : Plane,
      (if positive then z ∈ Tiling.positiveHalfPlane y d
        else z ∈ Tiling.negativeHalfPlane y d) →
      (if b then z ∈ Tiling.positiveHalfPlane y w
        else z ∈ Tiling.negativeHalfPlane y w) := by
  have hside (y z : Plane) : Tiling.signedSide y w z = c * Tiling.signedSide y d z := by
    simp [Tiling.signedSide, Tiling.planarCross, hdir]
    ring
  by_cases hcpos : 0 < c
  · have hrel' : b = positive := by simpa [hcpos] using hrel
    subst b
    intro y z hz
    cases positive with
    | true =>
        have hz' := Tiling.mem_positiveHalfPlane.mp (by simpa using hz)
        simp [hcpos] at ⊢
        have hout : 0 ≤ Tiling.signedSide y w z := by
          rw [hside]
          exact mul_nonneg hcpos.le hz'
        simpa using Tiling.mem_positiveHalfPlane.mpr hout
    | false =>
        have hz' := Tiling.mem_negativeHalfPlane.mp (by simpa using hz)
        simp [hcpos] at ⊢
        have hout : Tiling.signedSide y w z ≤ 0 := by
          rw [hside]
          exact mul_nonpos_of_nonneg_of_nonpos hcpos.le hz'
        simpa [hcpos] using Tiling.mem_negativeHalfPlane.mpr hout
  · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
    have hrel' : b = !positive := by simpa [hcpos] using hrel
    cases positive with
    | true =>
        have hb : b = false := by simpa using hrel'
        subst b
        intro y z hz
        have hz' := Tiling.mem_positiveHalfPlane.mp (by simpa using hz)
        have hout : Tiling.signedSide y w z ≤ 0 := by
          rw [hside]
          exact mul_nonpos_of_nonpos_of_nonneg hcneg.le hz'
        simpa [hcpos] using Tiling.mem_negativeHalfPlane.mpr hout
    | false =>
        have hb : b = true := by simpa using hrel'
        subst b
        intro y z hz
        have hz' := Tiling.mem_negativeHalfPlane.mp (by simpa using hz)
        have hout : 0 ≤ Tiling.signedSide y w z := by
          rw [hside]
          exact mul_nonneg_of_nonpos_of_nonpos hcneg.le hz'
        simpa [hcpos] using Tiling.mem_positiveHalfPlane.mpr hout

private theorem actual_occurrence_side_alignment
    (K : PolygonalRegion) (a t d : Plane) (hd : d ≠ 0)
    (e : Plane × Plane) (qlo qhi : ℝ) (hlohi : qlo < qhi)
    (hcoordinates :
      (t + e.1 = a + qlo • d ∧ t + e.2 = a + qhi • d) ∨
      (t + e.2 = a + qlo • d ∧ t + e.1 = a + qhi • d))
    (hprototype :
      (∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
      (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z))
    (positive : Bool)
    (hsource : ∀ r ∈ Ioo qlo qhi,
      if positive then positiveEdgeGerm (t +ᵥ K.support) d (a + r • d)
        else negativeEdgeGerm (t +ᵥ K.support) d (a + r • d)) :
    ∃ b : Bool,
      (if b then
        ∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z
       else
        ∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z) ∧
      ∀ y z : Plane,
        (if positive then z ∈ Tiling.positiveHalfPlane y d
          else z ∈ Tiling.negativeHalfPlane y d) →
        (if b then z ∈ Tiling.positiveHalfPlane y (e.2 - e.1)
          else z ∈ Tiling.negativeHalfPlane y (e.2 - e.1)) := by
  classical
  let r : ℝ := (qlo + qhi) / 2
  let z : Plane := midpoint ℝ e.1 e.2
  have hr : r ∈ Ioo qlo qhi := by
    dsimp [r]
    constructor <;> linarith
  have hzedge : z ∈ openSegment ℝ e.1 e.2 := by
    exact midpoint_mem_openSegment (𝕜 := ℝ) e.1 e.2
  have hcenter : t + z = a + r • d := by
    change t + midpoint ℝ e.1 e.2 = a + ((qlo + qhi) / 2) • d
    have hquot : (⅟2 : ℝ) * (qlo + qhi) = (qlo + qhi) / 2 := by
      rw [invOf_eq_inv]
      field_simp
    rcases hcoordinates with hforward | hbackward
    · have hhalf : (⅟2 : ℝ) * 2 = 1 := by rw [invOf_eq_inv]; norm_num
      have hsum : (t + e.1) + (t + e.2) =
          (a + qlo • d) + (a + qhi • d) := by rw [hforward.1, hforward.2]
      have hsumvec : (t + e.1) + (t + e.2) = (2 : ℝ) • t + (e.1 + e.2) := by module
      have htargetvec : (a + qlo • d) + (a + qhi • d) =
          (2 : ℝ) • a + (qlo + qhi) • d := by module
      rw [midpoint_eq_smul_add]
      calc
        t + (⅟2 : ℝ) • (e.1 + e.2) = (⅟2 : ℝ) • ((t + e.1) + (t + e.2)) := by
          rw [hsumvec]
          simp only [smul_add, smul_smul, hhalf, one_smul]
        _ = (⅟2 : ℝ) • ((a + qlo • d) + (a + qhi • d)) := by rw [hsum]
        _ = a + ((⅟2 : ℝ) * (qlo + qhi)) • d := by
          rw [htargetvec]
          simp only [smul_add, smul_smul, hhalf, one_smul]
        _ = a + ((qlo + qhi) / 2) • d := by rw [hquot]
    · have hhalf : (⅟2 : ℝ) * 2 = 1 := by rw [invOf_eq_inv]; norm_num
      have hsum : (t + e.2) + (t + e.1) =
          (a + qlo • d) + (a + qhi • d) := by rw [hbackward.1, hbackward.2]
      have hsumvec : (t + e.2) + (t + e.1) = (2 : ℝ) • t + (e.2 + e.1) := by module
      have htargetvec : (a + qlo • d) + (a + qhi • d) =
          (2 : ℝ) • a + (qlo + qhi) • d := by module
      rw [midpoint_comm, midpoint_eq_smul_add]
      calc
        t + (⅟2 : ℝ) • (e.2 + e.1) = (⅟2 : ℝ) • ((t + e.2) + (t + e.1)) := by
          rw [hsumvec]
          simp only [smul_add, smul_smul, hhalf, one_smul]
        _ = (⅟2 : ℝ) • ((a + qlo • d) + (a + qhi • d)) := by rw [hsum]
        _ = a + ((⅟2 : ℝ) * (qlo + qhi)) • d := by
          rw [htargetvec]
          simp only [smul_add, smul_smul, hhalf, one_smul]
        _ = a + ((qlo + qhi) / 2) • d := by rw [hquot]
  have hcdir : ∃ c : ℝ, c ≠ 0 ∧ e.2 - e.1 = c • d := by
    rcases hcoordinates with hforward | hbackward
    · refine ⟨qhi - qlo, sub_ne_zero.mpr (ne_of_gt hlohi), ?_⟩
      calc
        e.2 - e.1 = (t + e.2) - (t + e.1) := by abel
        _ = (a + qhi • d) - (a + qlo • d) := by rw [hforward.2, hforward.1]
        _ = (qhi - qlo) • d := by module
    · refine ⟨qlo - qhi, sub_ne_zero.mpr (ne_of_lt hlohi), ?_⟩
      calc
        e.2 - e.1 = (t + e.2) - (t + e.1) := by abel
        _ = (a + qlo • d) - (a + qhi • d) := by rw [hbackward.1, hbackward.2]
        _ = (qlo - qhi) • d := by module
  obtain ⟨c, hc, hdir⟩ := hcdir
  have hsourceAt :
      (if positive then positiveEdgeGerm (t +ᵥ K.support) d (t + z)
        else negativeEdgeGerm (t +ᵥ K.support) d (t + z)) := by
    simpa [hcenter] using hsource r hr
  rcases hprototype with hprotoPos | hprotoNeg
  · by_cases hcpos : 0 < c
    · have htrans := sourceRay_vadd_positiveEdgeGerm K.support t z (e.2 - e.1) (hprotoPos z hzedge)
      have hscaled : positiveEdgeGerm (t +ᵥ K.support) d (t + z) :=
        sourceRay_positiveGerm_scale_pos hcpos hdir htrans
      cases positive with
      | true =>
          refine ⟨true, hprotoPos, ?_⟩
          exact occurrence_halfPlane_side_transport hc hdir true true (by simp [hcpos])
      | false =>
          exact False.elim (positive_negative_edgeGerms_disjoint hd hscaled hsourceAt)
    · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
      have hscaled : negativeEdgeGerm (t +ᵥ K.support) d (t + z) := by
        have htrans := sourceRay_vadd_positiveEdgeGerm K.support t z (e.2 - e.1) (hprotoPos z hzedge)
        exact sourceRay_positiveGerm_scale_neg hcneg hdir htrans
      cases positive with
      | true => exact False.elim (positive_negative_edgeGerms_disjoint hd hsourceAt hscaled)
      | false =>
          refine ⟨true, hprotoPos, ?_⟩
          exact occurrence_halfPlane_side_transport hc hdir false true
            (by simp [not_lt.mpr hcneg.le])
  · by_cases hcpos : 0 < c
    · have htrans := sourceRay_vadd_negativeEdgeGerm K.support t z (e.2 - e.1) (hprotoNeg z hzedge)
      have hscaled : negativeEdgeGerm (t +ᵥ K.support) d (t + z) :=
        sourceRay_negativeGerm_scale_pos hcpos hdir htrans
      cases positive with
      | true => exact False.elim (positive_negative_edgeGerms_disjoint hd hsourceAt hscaled)
      | false =>
          refine ⟨false, hprotoNeg, ?_⟩
          exact occurrence_halfPlane_side_transport hc hdir false false (by simp [hcpos])
    · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
      have htrans := sourceRay_vadd_negativeEdgeGerm K.support t z (e.2 - e.1) (hprotoNeg z hzedge)
      have hscaled : positiveEdgeGerm (t +ᵥ K.support) d (t + z) :=
        sourceRay_negativeGerm_scale_neg hcneg hdir htrans
      cases positive with
      | true =>
          refine ⟨false, hprotoNeg, ?_⟩
          exact occurrence_halfPlane_side_transport hc hdir true false
            (by simp [not_lt.mpr hcneg.le])
      | false => exact False.elim (positive_negative_edgeGerms_disjoint hd hscaled hsourceAt)



private theorem packingSol_preservedSign_scaledDirection
    (A B : Set Plane) (p q d w : Plane) (c : ℝ) (hd : d ≠ 0) (hc : c ≠ 0)
    (hdir : w = c • d) (positive : Bool)
    (hselected : if positive then positiveEdgeGerm A d p else negativeEdgeGerm A d p)
    (hpaired : (positiveEdgeGerm A w p ∧ positiveEdgeGerm B w q) ∨
      (negativeEdgeGerm A w p ∧ negativeEdgeGerm B w q)) :
    if positive then positiveEdgeGerm B d q else negativeEdgeGerm B d q := by
  rcases hpaired with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · rcases lt_or_gt_of_ne hc.symm with hpos | hneg
    · have hsource := sourceRay_positiveGerm_scale_pos hpos hdir hA
      have htarget := sourceRay_positiveGerm_scale_pos hpos hdir hB
      cases positive with
      | true => exact htarget
      | false => exact False.elim (positive_negative_edgeGerms_disjoint hd hsource hselected)
    · have hsource := sourceRay_positiveGerm_scale_neg hneg hdir hA
      have htarget := sourceRay_positiveGerm_scale_neg hneg hdir hB
      cases positive with
      | true => exact False.elim (positive_negative_edgeGerms_disjoint hd hselected hsource)
      | false => exact htarget
  · rcases lt_or_gt_of_ne hc.symm with hpos | hneg
    · have hsource := sourceRay_negativeGerm_scale_pos hpos hdir hA
      have htarget := sourceRay_negativeGerm_scale_pos hpos hdir hB
      cases positive with
      | true => exact False.elim (positive_negative_edgeGerms_disjoint hd hselected hsource)
      | false => exact htarget
    · have hsource := sourceRay_negativeGerm_scale_neg hneg hdir hA
      have htarget := sourceRay_negativeGerm_scale_neg hneg hdir hB
      cases positive with
      | true => exact htarget
      | false => exact False.elim (positive_negative_edgeGerms_disjoint hd hsource hselected)

private theorem packingSol_signedOccurrence_targetGerms
    (K : PolygonalRegion) (P : PolyhedralCode)
    (hP : polyhedralSupport P = K.support)
    (E : Finset (Plane × Plane))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support)
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ n : RationalNormal, ∀ a t : Plane, ∀ e ∈ E,
      ∀ q : ℝ × ℝ, q.1 < q.2 →
      ((t + e.1 = a + q.1 • packingSol_rationalTangent n ∧
        t + e.2 = a + q.2 • packingSol_rationalTangent n) ∨
       (t + e.2 = a + q.1 • packingSol_rationalTangent n ∧
        t + e.1 = a + q.2 • packingSol_rationalTangent n)) →
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
       (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)) →
      ∀ positive : Bool,
      (∀ u ∈ Ioo q.1 q.2,
        if positive then positiveEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
          (a + u • packingSol_rationalTangent n)
        else negativeEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
          (a + u • packingSol_rationalTangent n)) →
      ∀ u ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ),
        if positive then positiveEdgeGerm (deformPoint φ t +ᵥ Kφ.support)
          (packingSol_rationalTangent n) (deformPoint φ a + u • packingSol_rationalTangent n)
        else negativeEdgeGerm (deformPoint φ t +ᵥ Kφ.support)
          (packingSol_rationalTangent n) (deformPoint φ a + u • packingSol_rationalTangent n) := by
  obtain ⟨F, ε, _, hε, _, htransport⟩ :=
    rationalPrimitiveEdges_uniformSameSide_transport K P hP E hrat hprimitive hcover
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ n a t e he q hq hcoords hproto positive hsource u hu
  obtain ⟨_, _, _, _, _, hgerms⟩ := htransport φ hφ Kφ hKφ
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hdirection : ∃ c : ℝ, c ≠ 0 ∧ e.2 - e.1 = c • d := by
    rcases hcoords with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · refine ⟨q.2 - q.1, ne_of_gt (sub_pos.mpr hq), ?_⟩
      calc
        e.2 - e.1 = (t + e.2) - (t + e.1) := by abel
        _ = (a + q.2 • d) - (a + q.1 • d) := by rw [hleft, hright]
        _ = (q.2 - q.1) • d := by module
    · refine ⟨q.1 - q.2, ne_of_lt (sub_neg.mpr hq), ?_⟩
      calc
        e.2 - e.1 = (t + e.2) - (t + e.1) := by abel
        _ = (a + q.1 • d) - (a + q.2 • d) := by rw [hleft, hright]
        _ = (q.1 - q.2) • d := by module
  obtain ⟨c, hc, hdir⟩ := hdirection
  obtain ⟨u₀, hu₀⟩ := exists_between hq
  let z₀ : Plane := -t + (a + u₀ • d)
  have hz₀ : z₀ ∈ openSegment ℝ e.1 e.2 := by
    change -t +ᵥ (a + u₀ • d) ∈ openSegment ℝ e.1 e.2
    apply Set.mem_vadd_set_iff_neg_vadd_mem.mp
    rw [vadd_openSegment]
    simp only [vadd_eq_add]
    rcases hcoords with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · rw [hleft, hright]
      exact carrierParameter_mem_openSegment a d q.1 q.2 u₀ hq hu₀
    · rw [hleft, hright, openSegment_symm]
      exact carrierParameter_mem_openSegment a d q.1 q.2 u₀ hq hu₀
  have hselected : if positive then positiveEdgeGerm K.support d z₀
      else negativeEdgeGerm K.support d z₀ := by
    cases positive with
    | true =>
      change positiveEdgeGerm K.support d z₀
      have h := sourceRay_vadd_positiveEdgeGerm (t +ᵥ K.support) (-t) (a + u₀ • d) d
        (hsource u₀ hu₀)
      simpa only [vadd_vadd, neg_add_cancel, zero_vadd] using h
    | false =>
      change negativeEdgeGerm K.support d z₀
      have h := sourceRay_vadd_negativeEdgeGerm (t +ᵥ K.support) (-t) (a + u₀ • d) d
        (hsource u₀ hu₀)
      simpa only [vadd_vadd, neg_add_cancel, zero_vadd] using h
  have mapEndpoint {v : Plane} {x : ℝ} (h : t + v = a + x • d) :
      deformPoint φ t + deformPoint φ v = deformPoint φ a + (φ x : ℝ) • d := by
    calc
      deformPoint φ t + deformPoint φ v = deformPoint φ (t + v) :=
        ((deformPointLinear φ).map_add t v).symm
      _ = deformPoint φ (a + x • d) := by rw [h]
      _ = deformPoint φ a + (φ x : ℝ) • d :=
        packingSol_deform_rationalCarrierParameter φ n a x
  have htargetPoint : deformPoint φ a + u • d ∈
      deformPoint φ t +ᵥ openSegment ℝ (deformPoint φ e.1) (deformPoint φ e.2) := by
    rw [vadd_openSegment]
    simp only [vadd_eq_add]
    rcases hcoords with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · rw [mapEndpoint hleft, mapEndpoint hright]
      exact carrierParameter_mem_openSegment (deformPoint φ a) d
        (φ q.1 : ℝ) (φ q.2 : ℝ) u (hu.1.trans hu.2) hu
    · rw [mapEndpoint hleft, mapEndpoint hright, openSegment_symm]
      exact carrierParameter_mem_openSegment (deformPoint φ a) d
        (φ q.1 : ℝ) (φ q.2 : ℝ) u (hu.1.trans hu.2) hu
  obtain ⟨z, hz, hzu⟩ := Set.mem_vadd_set.mp htargetPoint
  have hpaired : (positiveEdgeGerm K.support (e.2 - e.1) z₀ ∧
      positiveEdgeGerm Kφ.support (e.2 - e.1) z) ∨
      (negativeEdgeGerm K.support (e.2 - e.1) z₀ ∧
      negativeEdgeGerm Kφ.support (e.2 - e.1) z) := by
    rcases hproto with hpos | hneg
    · exact Or.inl ⟨hpos z₀ hz₀, by
        simpa only [hKφ] using (hgerms e he).1 hpos z hz⟩
    · exact Or.inr ⟨hneg z₀ hz₀, by
        simpa only [hKφ] using (hgerms e he).2 hneg z hz⟩
  have htarget := packingSol_preservedSign_scaledDirection K.support Kφ.support
    z₀ z d (e.2 - e.1) c hd hc hdir positive hselected hpaired
  have hzu' : deformPoint φ t + z = deformPoint φ a + u • d := by
    simpa only [vadd_eq_add] using hzu
  cases positive with
  | true =>
    change positiveEdgeGerm (deformPoint φ t +ᵥ Kφ.support) d (deformPoint φ a + u • d)
    simpa only [hzu'] using sourceRay_vadd_positiveEdgeGerm Kφ.support (deformPoint φ t) z d htarget
  | false =>
    change negativeEdgeGerm (deformPoint φ t +ᵥ Kφ.support) d (deformPoint φ a + u • d)
    simpa only [hzu'] using sourceRay_vadd_negativeEdgeGerm Kφ.support (deformPoint φ t) z d htarget

private theorem packingSol_actualSameJ_oppositeOccurrence
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (n : RationalNormal) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ a : Plane, ∀ r l u : ℝ,
      a + r • packingSol_rationalTangent n ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support →
      l < u →
      Icc l u ⊆ connectedComponentIn
        {s : ℝ | a + s • packingSol_rationalTangent n ∈
          ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r →
      ∀ positive : Bool, ∀ q ∈ signedCarrierComponentIntervals K T E a
        (packingSol_rationalTangent n) r positive,
      ∀ t ∈ T, ∀ e ∈ E,
      ((t + e.1 = a + q.1 • packingSol_rationalTangent n ∧
        t + e.2 = a + q.2 • packingSol_rationalTangent n) ∨
       (t + e.2 = a + q.1 • packingSol_rationalTangent n ∧
        t + e.1 = a + q.2 • packingSol_rationalTangent n)) →
      (∀ x ∈ Ioo q.1 q.2,
        if positive then positiveEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
          (a + x • packingSol_rationalTangent n)
        else negativeEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
          (a + x • packingSol_rationalTangent n)) →
      ∀ lo hi : ℝ, lo < hi →
      Ioo lo hi ⊆ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ) →
      ∃ s ∈ T, s ≠ t ∧ ∃ f ∈ E,
      ∃ q' ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) r (!positive),
      ((s + f.1 = a + q'.1 • packingSol_rationalTangent n ∧
        s + f.2 = a + q'.2 • packingSol_rationalTangent n) ∨
       (s + f.2 = a + q'.1 • packingSol_rationalTangent n ∧
        s + f.1 = a + q'.2 • packingSol_rationalTangent n)) ∧
      (∀ x ∈ Ioo q'.1 q'.2,
        if !positive then positiveEdgeGerm (s +ᵥ K.support) (packingSol_rationalTangent n)
          (a + x • packingSol_rationalTangent n)
        else negativeEdgeGerm (s +ᵥ K.support) (packingSol_rationalTangent n)
          (a + x • packingSol_rationalTangent n)) ∧
      (Ioo lo hi ∩ Ioo (φ q'.1 : ℝ) (φ q'.2 : ℝ)).Nonempty := by
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨F₀, ε₀, hε₀, hchain⟩ :=
    packingSol_uniformActualSourceCarrierTransport K T htile E hE hcover d hd
  obtain ⟨F₁, ε₁, hε₁, hgerms⟩ :=
    packingSol_signedOccurrence_targetGerms K P hP E hrat hprimitive hcover
  refine ⟨F₀ ∪ F₁, min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro φ hφ Kφ hKφ a r l u hr hlu hinterval positive q hq t ht e he hcoords hsource lo hi
    hlohi hsubinterval
  have hφ₀ : IsFiniteApproximation F₀ ε₀ φ :=
    ⟨hφ.1, fun s hs => (hφ.2 s (Finset.mem_union_left _ hs)).trans_le (min_le_left _ _)⟩
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ :=
    ⟨hφ.1, fun s hs => (hφ.2 s (Finset.mem_union_right _ hs)).trans_le (min_le_right _ _)⟩
  let J := connectedComponentIn
    {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r
  let A := signedCarrierComponentIntervals K T E a d r positive
  let B := signedCarrierComponentIntervals K T E a d r (!positive)
  obtain ⟨hshape, _, _, _, hcasesA⟩ :=
    hchain φ hφ₀ a r l u hr hlu hinterval positive
  obtain ⟨_, _, hLF, _, hcasesB⟩ :=
    hchain φ hφ₀ a r l u hr hlu hinterval (!positive)
  have hequal : (⋃ z : A, Icc (φ z.1.1 : ℝ) (φ z.1.2 : ℝ)) =
      ⋃ z : B, Icc (φ z.1.1 : ℝ) (φ z.1.2 : ℝ) := by
    rcases hshape with ⟨L, H, hLH, hJ⟩ | ⟨L, hJ⟩ | ⟨H, hJ⟩ | hJ
    · exact (hcasesA.1 L H hLH hJ).trans (hcasesB.1 L H hLH hJ).symm
    · exact (hcasesA.2.1 L hJ).trans (hcasesB.2.1 L hJ).symm
    · exact (hcasesA.2.2.1 H hJ).trans (hcasesB.2.2.1 H hJ).symm
    · exact (hcasesA.2.2.2 hJ).trans (hcasesB.2.2.2 hJ).symm
  let Y : Set ℝ := (fun x : ℝ => (φ x : ℝ)) '' scalarIntervalEndpoints B
  obtain ⟨x, hx, hxNot⟩ := (Ioo_infinite hlohi).exists_notMem_finite
    (hLF (Icc lo hi) isCompact_Icc.isBounded)
  have hxY : x ∉ Y := fun hxY => hxNot ⟨hxY, hx.1.le, hx.2.le⟩
  have hxq : x ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ) := hsubinterval hx
  have hxA : x ∈ ⋃ z : A, Icc (φ z.1.1 : ℝ) (φ z.1.2 : ℝ) :=
    Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hxq.1.le, hxq.2.le⟩
  obtain ⟨z, hxz⟩ := Set.mem_iUnion.mp (hequal ▸ hxA)
  have hxzOpen : x ∈ Ioo (φ z.1.1 : ℝ) (φ z.1.2 : ℝ) := by
    constructor
    · apply lt_of_le_of_ne hxz.1
      intro heq
      exact hxY ⟨z.1.1, ⟨z.1, z.2, Or.inl rfl⟩, heq⟩
    · apply lt_of_le_of_ne hxz.2
      intro heq
      exact hxY ⟨z.1.2, ⟨z.1, z.2, Or.inr rfl⟩, heq.symm⟩
  obtain ⟨hzpos, s, hs, f, hf, hcoords', hsource'⟩ := z.2.1
  have hqueryGerm := hgerms φ hφ₁ Kφ hKφ n a t e he q hq.1.1 hcoords
    (hE e he).2.2.2.2.2 positive hsource x hxq
  have hpartnerGerm := hgerms φ hφ₁ Kφ hKφ n a s f hf z.1 hzpos hcoords'
    (hE f hf).2.2.2.2.2 (!positive) hsource' x hxzOpen
  have hst : s ≠ t := by
    intro heq
    subst s
    cases positive with
    | true => exact positive_negative_edgeGerms_disjoint hd hqueryGerm hpartnerGerm
    | false => exact positive_negative_edgeGerms_disjoint hd hpartnerGerm hqueryGerm
  exact ⟨s, hs, hst, f, hf, z.1, z.2, hcoords', hsource', x, hx, hxzOpen⟩


private theorem rationalPrimitiveEdge_uniformCentral_labelledCollar
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (E : Finset (Plane × Plane))
    (hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet K.support)
    (hrational : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (e : Plane × Plane) (he : e ∈ E) (τ : ℝ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (positive : Bool)
    (hsource : ∀ p ∈ openSegment ℝ e.1 e.2,
      if positive then positiveEdgeGerm K.support (e.2 - e.1) p
      else negativeEdgeGerm K.support (e.2 - e.1) p) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ s ∈ T, ∀ θ ∈ Icc τ (1 - τ),
            let y := deformPoint φ s +
              AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ
            ∀ w : Plane, dist w y < R →
              w ∈ (if positive then Tiling.positiveHalfPlane y (e.2 - e.1)
                else Tiling.negativeHalfPlane y (e.2 - e.1)) →
              ∀ t : Plane, ∀ η : ℝ,
                0 < Metric.infDist w (deformPoint φ t +ᵥ Kφ.support) →
                dist w y < η → ∃ u ∈ T, u ≠ t ∧ w ∈ deformPoint φ u +ᵥ Kφ.support ∧
                  Metric.infDist w (deformPoint φ u +ᵥ frontier Kφ.support) < η := by
  obtain ⟨Fs, εs, R, hεs, hR, hstrip⟩ := rationalPrimitiveEdge_uniformCentralSameSide
    K P hP E hprimitive hrational hcover e he τ hτ hτhalf positive hsource
  obtain ⟨Ft, εt, hεt, htransport⟩ := rationalPrimitiveFrontier_transport K P hP E
    (fun f hf => ⟨(hprimitive f hf).1, hrational f hf⟩) hcover
  refine ⟨Fs ∪ Ft, min εs εt, R, lt_min hεs hεt, hR, ?_⟩
  intro φ hφ Kφ hKφ s hs θ hθ
  dsimp only
  intro w hwr hside t η hpos hnear
  have hφs := finiteApproximation_strengthen Fs (Fs ∪ Ft) εs (min εs εt) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφt := finiteApproximation_strengthen Ft (Fs ∪ Ft) εt (min εs εt) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  let y0 := AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ
  have hdist : dist (w - deformPoint φ s) y0 = dist w (deformPoint φ s + y0) := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have hsideEq : Tiling.signedSide (deformPoint φ s + y0) (e.2 - e.1) w =
      Tiling.signedSide y0 (e.2 - e.1) (w - deformPoint φ s) := by
    have hpoint : y0 + (w - (deformPoint φ s + y0)) = w - deformPoint φ s := by abel
    simpa only [add_sub_cancel, hpoint] using
      signedSide_translation (deformPoint φ s + y0) y0 (e.2 - e.1)
        (w - (deformPoint φ s + y0))
  change w ∈ (if positive then Tiling.positiveHalfPlane (deformPoint φ s + y0) (e.2 - e.1)
    else Tiling.negativeHalfPlane (deformPoint φ s + y0) (e.2 - e.1)) at hside
  have hwside : w - deformPoint φ s ∈
      (if positive then Tiling.positiveHalfPlane y0 (e.2 - e.1)
        else Tiling.negativeHalfPlane y0 (e.2 - e.1)) := by
    cases positive <;>
      simpa only [Bool.false_eq_true, ↓reduceIte, Tiling.mem_positiveHalfPlane, Tiling.mem_negativeHalfPlane,
        hsideEq] using hside
  have hball : w - deformPoint φ s ∈ Metric.ball y0 R := by
    rw [Metric.mem_ball, hdist]
    exact hwr
  have hproto : w - deformPoint φ s ∈ Kφ.support := by
    have hmem : w - deformPoint φ s ∈ Kφ.support ∩ Metric.ball y0 R := by
      rw [hstrip φ hφs Kφ hKφ θ hθ]
      exact ⟨hwside, hball⟩
    exact hmem.1
  have hwcopy : w ∈ deformPoint φ s +ᵥ Kφ.support := by
    apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using hproto
  have hst : s ≠ t := by
    intro hst
    rw [hst] at hwcopy
    have hdist' := Metric.infDist_le_dist_of_mem (x := w) hwcopy
    simp only [dist_self] at hdist'
    linarith
  obtain ⟨H, hanchors, hsupport, hsegments, hfront⟩ := htransport φ hφt Kφ hKφ
  have hysegment : y0 ∈ segment ℝ (deformPoint φ e.1) (deformPoint φ e.2) := by
    rw [segment_eq_image_lineMap]
    exact ⟨θ, ⟨hτ.le.trans hθ.1, hθ.2.trans (by linarith)⟩, rfl⟩
  have hyfront : y0 ∈ frontier Kφ.support := by
    rw [hfront]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hysegment⟩
  have hycopy : deformPoint φ s + y0 ∈ deformPoint φ s +ᵥ frontier Kφ.support :=
    Set.vadd_mem_vadd_set hyfront
  exact ⟨s, hs, hst, hwcopy, (Metric.infDist_le_dist_of_mem hycopy).trans_lt hnear⟩

private theorem segment_positiveMultiple_has_initialRay
    (B : Set Plane) (p v z : Plane) (k : ℝ) (hk : 0 ≤ k)
    (hz : z = k • (v - p)) (hsegment : segment ℝ p v ⊆ B) :
    ∃ r > 0, ∀ c : ℝ, 0 ≤ c → c < r → p + c • z ∈ B := by
  refine ⟨1 / (k + 1), by positivity, ?_⟩
  intro c hc hcr
  have hck : c * k ∈ Icc (0 : ℝ) 1 := by
    have hbound : c * (k + 1) < 1 := (lt_div_iff₀ (by positivity : 0 < k + 1)).mp hcr
    exact ⟨mul_nonneg hc hk, by nlinarith⟩
  apply hsegment
  rw [segment_eq_image_lineMap]
  refine ⟨c * k, hck, ?_⟩
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, hz, smul_smul]
  abel


private theorem rationalPrimitiveVertices_uniformOccupiedStar_labelledCollar
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (E : Finset (Plane × Plane))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hfront : ∀ e ∈ E, segment ℝ e.1 e.2 ⊆ frontier K.support) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ t ∈ T, ∀ e ∈ E, ∀ p : Plane, p = t + e.1 ∨ p = t + e.2 →
            ∀ y ∈ deformPoint φ t +ᵥ segment ℝ (deformPoint φ e.1) (deformPoint φ e.2),
              dist y (deformPoint φ p) < R →
              ∀ η : ℝ, 0 < η → η < R → ∀ x : Plane,
                dist x y < η → 0 < Metric.infDist x (deformPoint φ t +ᵥ Kφ.support) →
                x - deformPoint φ p ∈ originalVertexConeUnion K P T p →
                ∃ s ∈ T, s ≠ t ∧ x ∈ deformPoint φ s +ᵥ Kφ.support ∧
                  Metric.infDist x (deformPoint φ s +ᵥ frontier Kφ.support) < η := by
  obtain ⟨Fs, εs, Rs, hεs, hRs, hstar⟩ :=
    originalVertexStar_uniformDirected_labelledCollar K P T hP hpack
  obtain ⟨Fc, εc, l, hεc, _, hlength⟩ := finiteRationalEdges_positiveHomotheties E hrat
  refine ⟨Fs ∪ Fc, min εs εc, Rs / 4, lt_min hεs hεc, by positivity, ?_⟩
  intro φ hφ Kφ hKφ t ht e he p hp y hy hyp η hη hηR x hxy hpos hQ
  have hφs := finiteApproximation_strengthen Fs (Fs ∪ Fc) εs (min εs εc) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφc := finiteApproximation_strengthen Fc (Fs ∪ Fc) εc (min εs εc) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  obtain ⟨k, hk, _, hvec, _⟩ := hlength φ hφc e he
  have hmapadd (v : Plane) : deformPoint φ (t + v) = deformPoint φ t + deformPoint φ v :=
    (deformPointLinear φ).map_add t v
  have hray : ∃ r > 0, ∀ c : ℝ, 0 ≤ c → c < r →
      p + c • (y - deformPoint φ p) ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support := by
    have build (v w : Plane) (hpv : p = t + v)
        (hvw : deformPoint φ w - deformPoint φ v = k • (w - v))
        (hyvw : y ∈ deformPoint φ t +ᵥ segment ℝ (deformPoint φ v) (deformPoint φ w))
        (hfrontvw : segment ℝ v w ⊆ frontier K.support) :
        ∃ r > 0, ∀ c : ℝ, 0 ≤ c → c < r →
          p + c • (y - deformPoint φ p) ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support := by
      rw [vadd_segment, segment_eq_image_lineMap] at hyvw
      obtain ⟨θ, hθ, hyθ⟩ := hyvw
      have hoffset : y - deformPoint φ p = (θ * k) • ((t + w) - p) := by
        rw [← hyθ, hpv, hmapadd]
        simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
        have hdiff : (deformPoint φ t + deformPoint φ w) -
            (deformPoint φ t + deformPoint φ v) = k • (w - v) := by
          simpa only [add_sub_add_left_eq_sub] using hvw
        simp only [vadd_eq_add] at *
        rw [hdiff]
        module
      apply segment_positiveMultiple_has_initialRay _ p (t + w) _ (θ * k)
        (mul_nonneg hθ.1 (by linarith)) hoffset
      have htranslate : segment ℝ (t + v) (t + w) = t +ᵥ segment ℝ v w := by
        simpa only [vadd_eq_add] using (vadd_segment ℝ t v w).symm
      rw [hpv, htranslate]
      intro z hz
      exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, Set.vadd_set_mono hfrontvw hz⟩
    rcases hp with hp | hp
    · exact build e.1 e.2 hp hvec hy (hfront e he)
    · apply build e.2 e.1 hp
      · calc
          deformPoint φ e.1 - deformPoint φ e.2 =
              -(deformPoint φ e.2 - deformPoint φ e.1) := by abel
          _ = -(k • (e.2 - e.1)) := congrArg Neg.neg hvec
          _ = k • (e.1 - e.2) := by rw [← smul_neg, neg_sub]
      · simpa only [segment_symm] using hy
      · simpa only [segment_symm] using hfront e he
  have hz : dist (y - deformPoint φ p) 0 < Rs := by
    have : dist (y - deformPoint φ p) 0 = dist y (deformPoint φ p) := by simp [dist_eq_norm]
    rw [this]
    linarith
  have hx : dist (x - deformPoint φ p) 0 < Rs := by
    have htriangle := dist_triangle x y (deformPoint φ p)
    have : dist (x - deformPoint φ p) 0 = dist x (deformPoint φ p) := by simp [dist_eq_norm]
    rw [this]
    linarith
  have hyEq : deformPoint φ p + (y - deformPoint φ p) = y := by abel
  exact hstar φ hφs Kφ hKφ p (y - deformPoint φ p) x hray hz hx hQ t η hpos
    (by simpa only [hyEq] using hxy)


private def tangentCoord (d z : Plane) : ℝ :=
  (d.re * z.re + d.im * z.im) / Complex.normSq d

private def normalCoord (d z : Plane) : ℝ :=
  Tiling.planarCross d z / Complex.normSq d

private theorem tangent_normal_decomposition {d z : Plane} (hd : d ≠ 0) :
    z = tangentCoord d z • d + normalCoord d z • (d * Complex.I) := by
  have hD : Complex.normSq d ≠ 0 := (Complex.normSq_pos.mpr hd).ne'
  have hD' : d.re ^ 2 + d.im ^ 2 ≠ 0 := by
    simpa [Complex.normSq_apply, pow_two] using hD
  have hD'' : d.re * d.re + d.im * d.im ≠ 0 := by
    simpa [Complex.normSq_apply] using hD
  have hD''' : d.im ^ 2 + d.re ^ 2 ≠ 0 := by simpa [add_comm] using hD'
  apply Complex.ext
  · change z.re = (tangentCoord d z • d).re +
      (normalCoord d z • (d * Complex.I)).re
    rw [Complex.smul_re, Complex.smul_re, Complex.mul_I_re]
    simp only [tangentCoord, normalCoord, Tiling.planarCross, Complex.normSq_apply]
    simp only [smul_eq_mul]
    field_simp [hD']
    ring
  · change z.im = (tangentCoord d z • d).im +
      (normalCoord d z • (d * Complex.I)).im
    rw [Complex.smul_im, Complex.smul_im, Complex.mul_I_im]
    simp only [tangentCoord, normalCoord, Tiling.planarCross, Complex.normSq_apply]
    simp only [smul_eq_mul]
    field_simp [hD''']
    ring

private theorem normSq_tangent_normal (d : Plane) (a b : ℝ) :
    Complex.normSq (a • d + b • (d * Complex.I)) =
      (a ^ 2 + b ^ 2) * Complex.normSq d := by
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    Complex.mul_I_re, Complex.mul_I_im]
  simp only [Complex.normSq_apply]
  ring

private theorem normSq_smul_real (a : ℝ) (z : Plane) :
    Complex.normSq (a • z) = a ^ 2 * Complex.normSq z := by
  simp [Complex.smul_re, Complex.smul_im, Complex.normSq_apply]
  ring

private theorem dist_le_of_normSq_le {x y : Plane} (h : Complex.normSq x ≤ Complex.normSq y) :
    ‖x‖ ≤ ‖y‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  exact Real.sqrt_le_sqrt h

private theorem halfspace_projection_candidate
    (p w d : Plane) (hd : d ≠ 0) (positive : Bool)
    (hw : w ∉ (if positive then Tiling.positiveHalfPlane p d
      else Tiling.negativeHalfPlane p d)) :
    ∃ q : Plane,
      q ∈ Tiling.affineLine p d ∧
      dist q p ≤ dist w p ∧
      (∀ y ∈ (if positive then Tiling.positiveHalfPlane p d
        else Tiling.negativeHalfPlane p d), dist w q ≤ dist w y) ∧
      w ∈ (if positive then Tiling.negativeHalfPlane q d
        else Tiling.positiveHalfPlane q d) := by
  let D := Complex.normSq d
  have hD : 0 < D := Complex.normSq_pos.mpr hd
  have hDne : Complex.normSq d ≠ 0 := hD.ne'
  let v := w - p
  let a := tangentCoord d v
  let b := normalCoord d v
  let q := p + a • d
  have hv : v = a • d + b • (d * Complex.I) := by
    exact tangent_normal_decomposition hd
  have hv' : w - p = a • d + b • (d * Complex.I) := by
    simpa [v] using hv
  have hqline : q ∈ Tiling.affineLine p d := by
    rw [Tiling.mem_affineLine_iff_exists_smul hd]
    exact ⟨a, rfl⟩
  have hcross (z : Plane) :
      Tiling.signedSide p d z = D * normalCoord d (z - p) := by
    simp only [Tiling.signedSide, Tiling.planarCross, normalCoord, D]
    field_simp [hDne]
    simp [Tiling.planarCross]
    <;> ring
  have hcrossq (z : Plane) :
      Tiling.signedSide q d z = Tiling.signedSide p d z := by
    have hside := Tiling.signedSide_vadd_smul p d a
    simp only [Tiling.signedSide] at hside ⊢
    simp only [q]
    linarith
  have hdistqp : dist q p = ‖a • d‖ := by
    rw [dist_eq_norm]
    simp [q]
  have hdistwp : dist w p = ‖v‖ := by
    simp [v, dist_eq_norm]
  have hnormqp : Complex.normSq (a • d) ≤ Complex.normSq v := by
    rw [hv, normSq_tangent_normal]
    simp [normSq_smul_real, Complex.normSq_apply, Complex.mul_I_re, Complex.mul_I_im]
    nlinarith [sq_nonneg b, hD]
  have hdistqp' : ‖a • d‖ ≤ ‖v‖ := by
    apply dist_le_of_normSq_le
    simpa [normSq_smul_real] using hnormqp
  refine ⟨q, hqline, ?_, ?_, ?_⟩
  · rw [hdistqp, hdistwp]
    exact hdistqp'
  · intro y hy
    by_cases hpos : positive
    · simp only [if_pos hpos] at hy
      have hwb : b < 0 := by
        have hnot : ¬ 0 ≤ Tiling.signedSide p d w := by
          intro hh
          exact hw (by simpa [hpos] using Tiling.mem_positiveHalfPlane.mpr hh)
        rw [hcross w] at hnot
        have hDb : D * b < 0 := lt_of_not_ge hnot
        by_contra hb
        have hb' : 0 ≤ b := le_of_not_gt hb
        have : 0 ≤ D * b := mul_nonneg hD.le hb'
        linarith
      have hyb : 0 ≤ normalCoord d (y - p) := by
        have hs := (Tiling.mem_positiveHalfPlane.mp hy)
        rw [hcross y] at hs
        nlinarith [hD]
      let c := tangentCoord d (y - p)
      let e := normalCoord d (y - p)
      have hydecomp : y - p = c • d + e • (d * Complex.I) :=
        tangent_normal_decomposition hd
      have hwd : w - y = (a - c) • d + (b - e) • (d * Complex.I) := by
        calc
          w - y = (w - p) - (y - p) := by abel
          _ = (a - c) • d + (b - e) • (d * Complex.I) := by rw [hv', hydecomp]; module
      have hnorm : Complex.normSq (w - q) ≤ Complex.normSq (w - y) := by
        have hwq : w - q = b • (d * Complex.I) := by
          calc
            w - q = (w - p) - a • d := by simp [q]; abel
            _ = b • (d * Complex.I) := by rw [hv']; module
        rw [hwq, hwd, normSq_smul_real, Complex.normSq_mul, Complex.normSq_I,
          normSq_tangent_normal]
        have hbe : b * e ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hwb.le hyb
        have hsquare : b ^ 2 ≤ (b - e) ^ 2 := by nlinarith [sq_nonneg e, hbe]
        calc
          b ^ 2 * (Complex.normSq d * 1) ≤ (b - e) ^ 2 * Complex.normSq d := by
            nlinarith [mul_le_mul_of_nonneg_right hsquare hD.le]
          _ ≤ ((a - c) ^ 2 + (b - e) ^ 2) * Complex.normSq d := by
            gcongr
            nlinarith [sq_nonneg (a - c)]
      have hdist : dist w q ≤ dist w y := by
        rw [dist_eq_norm, dist_eq_norm]
        exact dist_le_of_normSq_le hnorm
      exact hdist
    · have hneg : positive = false := by cases positive <;> simp_all
      simp only [hneg, Bool.false_eq_true, ↓reduceIte] at hy
      have hwb : 0 < b := by
        have hnot : ¬ Tiling.signedSide p d w ≤ 0 := by
          intro hh
          exact hw (by simpa [hneg] using Tiling.mem_negativeHalfPlane.mpr hh)
        rw [hcross w] at hnot
        have hDb : 0 < D * b := lt_of_not_ge hnot
        by_contra hb
        have hb' : b ≤ 0 := le_of_not_gt hb
        have : D * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD.le hb'
        linarith
      have hyb : normalCoord d (y - p) ≤ 0 := by
        have hs := (Tiling.mem_negativeHalfPlane.mp hy)
        rw [hcross y] at hs
        nlinarith [hD]
      let c := tangentCoord d (y - p)
      let e := normalCoord d (y - p)
      have hydecomp : y - p = c • d + e • (d * Complex.I) :=
        tangent_normal_decomposition hd
      have hwd : w - y = (a - c) • d + (b - e) • (d * Complex.I) := by
        calc
          w - y = (w - p) - (y - p) := by abel
          _ = (a - c) • d + (b - e) • (d * Complex.I) := by rw [hv', hydecomp]; module
      have hnorm : Complex.normSq (w - q) ≤ Complex.normSq (w - y) := by
        have hwq : w - q = b • (d * Complex.I) := by
          calc
            w - q = (w - p) - a • d := by simp [q]; abel
            _ = b • (d * Complex.I) := by rw [hv']; module
        rw [hwq, hwd, normSq_smul_real, Complex.normSq_mul, Complex.normSq_I,
          normSq_tangent_normal]
        have hbe : b * e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hwb.le hyb
        have hsquare : b ^ 2 ≤ (b - e) ^ 2 := by nlinarith [sq_nonneg e, hbe]
        calc
          b ^ 2 * (Complex.normSq d * 1) ≤ (b - e) ^ 2 * Complex.normSq d := by
            nlinarith [mul_le_mul_of_nonneg_right hsquare hD.le]
          _ ≤ ((a - c) ^ 2 + (b - e) ^ 2) * Complex.normSq d := by
            gcongr
            nlinarith [sq_nonneg (a - c)]
      have hdist : dist w q ≤ dist w y := by
        rw [dist_eq_norm, dist_eq_norm]
        exact dist_le_of_normSq_le hnorm
      exact hdist
  · by_cases hpos : positive
    · simp only [if_pos hpos]
      apply Tiling.mem_negativeHalfPlane.mpr
      have hwb : b < 0 := by
        have hnot : ¬ 0 ≤ Tiling.signedSide p d w := by
          intro hh
          exact hw (by simpa [hpos] using Tiling.mem_positiveHalfPlane.mpr hh)
        rw [hcross w] at hnot
        have hDb : D * b < 0 := lt_of_not_ge hnot
        by_contra hb
        have hb' : 0 ≤ b := le_of_not_gt hb
        have : 0 ≤ D * b := mul_nonneg hD.le hb'
        linarith
      rw [hcrossq w, hcross w]
      nlinarith [hD, hwb]
    · have hneg : positive = false := by cases positive <;> simp_all
      simp only [hneg, Bool.false_eq_true, ↓reduceIte]
      apply Tiling.mem_positiveHalfPlane.mpr
      have hwb : 0 < b := by
        have hnot : ¬ Tiling.signedSide p d w ≤ 0 := by
          intro hh
          exact hw (by simpa [hneg] using Tiling.mem_negativeHalfPlane.mpr hh)
        rw [hcross w] at hnot
        have hDb : 0 < D * b := lt_of_not_ge hnot
        by_contra hb
        have hb' : b ≤ 0 := le_of_not_gt hb
        have : D * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD.le hb'
        linarith
      rw [hcrossq w, hcross w]
      nlinarith [hD, hwb]


private theorem finiteApproximation_uniformPositiveRadius {ι : Type*}
    (D : Finset ι) (Q : ι → (ℝ →ₗ[ℚ] ℚ) → ℝ → Prop)
    (hmono : ∀ i ∈ D, ∀ φ r R, r ≤ R → Q i φ R → Q i φ r)
    (hlocal : ∀ i ∈ D, ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ → Q i φ R) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ → ∀ i ∈ D, Q i φ R := by
  classical
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, 1, 1, by norm_num, by norm_num, by simp⟩
  | @insert i D hi ih =>
      obtain ⟨Fi, εi, Ri, hεi, hRi, hQi⟩ := hlocal i (Finset.mem_insert_self _ _)
      obtain ⟨F, ε, R, hε, hR, hQ⟩ := ih
        (fun j hj => hmono j (Finset.mem_insert_of_mem hj))
        (fun j hj => hlocal j (Finset.mem_insert_of_mem hj))
      refine ⟨Fi ∪ F, min εi ε, min Ri R, lt_min hεi hε, lt_min hRi hR, ?_⟩
      intro φ hφ j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hmono j (Finset.mem_insert_self _ _) φ _ _ (min_le_left _ _)
          (hQi φ (finiteApproximation_strengthen Fi (Fi ∪ F) εi (min εi ε) φ
            Finset.subset_union_left (min_le_left _ _) hφ))
      · exact hmono j (Finset.mem_insert_of_mem hj) φ _ _ (min_le_right _ _)
          (hQ φ (finiteApproximation_strengthen F (Fi ∪ F) ε (min εi ε) φ
            Finset.subset_union_right (min_le_right _ _) hφ) j hj)


private theorem rationalPrimitiveEdges_uniformCentral_labelledCollar
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (E : Finset (Plane × Plane))
    (hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet K.support)
    (hrational : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (τ : ℝ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ e ∈ E, ∀ positive : Bool,
            (∀ p ∈ openSegment ℝ e.1 e.2,
              if positive then positiveEdgeGerm K.support (e.2 - e.1) p
              else negativeEdgeGerm K.support (e.2 - e.1) p) →
            ∀ s ∈ T, ∀ θ ∈ Icc τ (1 - τ),
              let y := deformPoint φ s +
                AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ
              ∀ w : Plane, dist w y < R →
                w ∈ (if positive then Tiling.positiveHalfPlane y (e.2 - e.1)
                  else Tiling.negativeHalfPlane y (e.2 - e.1)) →
                ∀ t : Plane, ∀ η : ℝ,
                  0 < Metric.infDist w (deformPoint φ t +ᵥ Kφ.support) →
                  dist w y < η → ∃ u ∈ T, u ≠ t ∧ w ∈ deformPoint φ u +ᵥ Kφ.support ∧
                    Metric.infDist w (deformPoint φ u +ᵥ frontier Kφ.support) < η := by
  classical
  let I := {e // e ∈ E} × Bool
  let Q (i : I) (φ : ℝ →ₗ[ℚ] ℚ) (R : ℝ) : Prop :=
    ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      (∀ p ∈ openSegment ℝ i.1.1.1 i.1.1.2,
        if i.2 then positiveEdgeGerm K.support (i.1.1.2 - i.1.1.1) p
        else negativeEdgeGerm K.support (i.1.1.2 - i.1.1.1) p) →
      ∀ s ∈ T, ∀ θ ∈ Icc τ (1 - τ),
        ∀ w : Plane,
          dist w (deformPoint φ s + AffineMap.lineMap
            (deformPoint φ i.1.1.1) (deformPoint φ i.1.1.2) θ) < R →
          w ∈ (if i.2 then Tiling.positiveHalfPlane
            (deformPoint φ s + AffineMap.lineMap
              (deformPoint φ i.1.1.1) (deformPoint φ i.1.1.2) θ) (i.1.1.2 - i.1.1.1)
            else Tiling.negativeHalfPlane
              (deformPoint φ s + AffineMap.lineMap
                (deformPoint φ i.1.1.1) (deformPoint φ i.1.1.2) θ) (i.1.1.2 - i.1.1.1)) →
          ∀ t : Plane, ∀ η : ℝ,
            0 < Metric.infDist w (deformPoint φ t +ᵥ Kφ.support) →
            dist w (deformPoint φ s + AffineMap.lineMap
              (deformPoint φ i.1.1.1) (deformPoint φ i.1.1.2) θ) < η →
            ∃ u ∈ T, u ≠ t ∧ w ∈ deformPoint φ u +ᵥ Kφ.support ∧
              Metric.infDist w (deformPoint φ u +ᵥ frontier Kφ.support) < η
  have hmono : ∀ i ∈ (Finset.univ : Finset I), ∀ φ r R, r ≤ R → Q i φ R → Q i φ r := by
    intro i _ φ r R hr hQ Kφ hKφ hsource s hs θ hθ w hw hside t η hpos hnear
    exact hQ Kφ hKφ hsource s hs θ hθ w (hw.trans_le hr) hside t η hpos hnear
  have hlocal : ∀ i ∈ (Finset.univ : Finset I),
      ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ → Q i φ R := by
    intro i _
    by_cases hsource : ∀ p ∈ openSegment ℝ i.1.1.1 i.1.1.2,
        if i.2 then positiveEdgeGerm K.support (i.1.1.2 - i.1.1.1) p
        else negativeEdgeGerm K.support (i.1.1.2 - i.1.1.1) p
    · obtain ⟨F, ε, R, hε, hR, hQ⟩ := rationalPrimitiveEdge_uniformCentral_labelledCollar
        K P T hP E hprimitive hrational hcover i.1.1 i.1.2 τ hτ hτhalf i.2 hsource
      refine ⟨F, ε, R, hε, hR, ?_⟩
      intro φ hφ Kφ hKφ _
      exact hQ φ hφ Kφ hKφ
    · exact ⟨∅, 1, 1, by norm_num, by norm_num,
        fun _ _ _ _ h => False.elim (hsource h)⟩
  obtain ⟨F, ε, R, hε, hR, hQ⟩ :=
    finiteApproximation_uniformPositiveRadius Finset.univ Q hmono hlocal
  refine ⟨F, ε, R, hε, hR, ?_⟩
  intro φ hφ Kφ hKφ e he positive hsource s hs θ hθ
  dsimp only
  exact hQ φ hφ (⟨e, he⟩, positive) (Finset.mem_univ _) Kφ hKφ hsource s hs θ hθ


private theorem signedCarrierComponent_uniformAugmentedCollar
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ Rs : ℝ, 0 < Rs ∧ ∀ M : ℝ, 0 < M → M ≤ Rs / 4 →
      ∀ Z : Tiling.RationalPolygonal.IntegerPlane,
      Tiling.RationalPolygonal.integerPoint Z ≠ 0 →
      ∃ F : Finset ℝ, ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
            ∀ a : Plane, ∀ r l u : ℝ,
              a + r • Tiling.RationalPolygonal.integerPoint Z ∈
                ⋃ t : T, (t : Plane) +ᵥ frontier K.support →
              l < u → Icc l u ⊆ connectedComponentIn
                {s : ℝ | a + s • Tiling.RationalPolygonal.integerPoint Z ∈
                  ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r →
              ∀ positive : Bool, ∀ v : ℝ,
                v ∈ ⋃ q : signedCarrierComponentIntervals K T E a
                  (Tiling.RationalPolygonal.integerPoint Z) r positive,
                    Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ) →
                (∀ x ∈ connectedComponentIn
                    {s : ℝ | a + s • Tiling.RationalPolygonal.integerPoint Z ∈
                      ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r,
                  x ∉ interior (connectedComponentIn
                    {s : ℝ | a + s • Tiling.RationalPolygonal.integerPoint Z ∈
                      ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r) →
                  M ≤ dist (deformPoint φ a + v • Tiling.RationalPolygonal.integerPoint Z)
                    (deformPoint φ (a + x • Tiling.RationalPolygonal.integerPoint Z))) →
                ∀ w : Plane,
                  dist w (deformPoint φ a + v • Tiling.RationalPolygonal.integerPoint Z) < ρ →
                  w ∈ (if positive then Tiling.positiveHalfPlane
                    (deformPoint φ a + v • Tiling.RationalPolygonal.integerPoint Z)
                    (Tiling.RationalPolygonal.integerPoint Z)
                  else Tiling.negativeHalfPlane
                    (deformPoint φ a + v • Tiling.RationalPolygonal.integerPoint Z)
                    (Tiling.RationalPolygonal.integerPoint Z)) →
                  ∀ t : Plane, ∀ η : ℝ,
                    0 < Metric.infDist w (deformPoint φ t +ᵥ Kφ.support) →
                    dist w (deformPoint φ a + v • Tiling.RationalPolygonal.integerPoint Z) < η →
                    ∃ s ∈ T, s ≠ t ∧ w ∈ deformPoint φ s +ᵥ Kφ.support ∧
                      Metric.infDist w (deformPoint φ s +ᵥ frontier Kφ.support) < η := by
  have hvertices : ∀ e ∈ E, e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).2.1, (hE e he).2.2.1⟩
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨Fs, εs, Rs, hεs, hRs, hstar⟩ :=
    signedCarrierComponent_internalEndpoint_labelledCollar K P T hP htile E hvertices
  obtain ⟨Fl, εl, l₀, L, hεl, _, hL, hlength⟩ := finiteRationalEdges_uniformLengthRange E hrat
  refine ⟨Rs, hRs, ?_⟩
  intro M hM hMR Z hZ
  let d := Tiling.RationalPolygonal.integerPoint Z
  let τ : ℝ := min (1 / 2) (M / (2 * L))
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hM (by positivity))
  have hτhalf : τ ≤ 1 / 2 := min_le_left _ _
  have hτmargin : τ * L < M := by
    have hbound : τ ≤ M / (2 * L) := min_le_right _ _
    have hprod : τ * (2 * L) ≤ M := (le_div_iff₀ (by positivity)).mp hbound
    nlinarith
  obtain ⟨Fc, εc, Rc, hεc, hRc, hcentral⟩ :=
    rationalPrimitiveEdges_uniformCentral_labelledCollar K P T hP E hprimitive hrat hcover τ hτ hτhalf
  obtain ⟨Fa, εa, hεa, hchain⟩ :=
    packingSol_uniformActualSourceCarrierTransport K T htile E hE hcover d hZ
  let F := Fs ∪ Fl ∪ Fc ∪ Fa
  let ε := min εs (min εl (min εc εa))
  refine ⟨F, ε, min M Rc, lt_min hεs (lt_min hεl (lt_min hεc hεa)), lt_min hM hRc, ?_⟩
  intro φ hφ Kφ hKφ a r l u hr hlu hwindow positive v hv hmargin w hw hside t η hpos hnear
  have hφs : IsFiniteApproximation Fs εs φ := by
    apply finiteApproximation_strengthen Fs F εs ε φ _ (min_le_left _ _) hφ
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have hφl : IsFiniteApproximation Fl εl φ := by
    apply finiteApproximation_strengthen Fl F εl ε φ _
      ((min_le_right _ _).trans (min_le_left _ _)) hφ
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  have hφc : IsFiniteApproximation Fc εc φ := by
    apply finiteApproximation_strengthen Fc F εc ε φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) hφ
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hφa : IsFiniteApproximation Fa εa φ := by
    apply finiteApproximation_strengthen Fa F εa ε φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) hφ
    exact Finset.subset_union_right
  let J := connectedComponentIn {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r
  let A := signedCarrierComponentIntervals K T E a d r positive
  let y := deformPoint φ a + v • d
  change dist w y < min M Rc at hw
  change w ∈ (if positive then Tiling.positiveHalfPlane y d else Tiling.negativeHalfPlane y d) at hside
  change dist w y < η at hnear
  change v ∈ ⋃ q : A, Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ) at hv
  obtain ⟨q₀, hvq⟩ := Set.mem_iUnion.mp hv
  let q := q₀.1
  have hq : q ∈ A := q₀.2
  have hword := (hchain φ hφa a r l u hr hlu hwindow positive).2.1
  have horder : (φ q.1 : ℝ) < (φ q.2 : ℝ) := by
    have h := hword q.1 ⟨q, hq, Or.inl rfl⟩ q.2 ⟨q, hq, Or.inr rfl⟩ hq.1.1
    linarith [hq.1.1]
  obtain ⟨hqpos, s, hs, e, he, hcoords, hsource⟩ := hq.1
  have mapEndpoint {b : Plane} {x : ℝ} (h : s + b = a + x • d) :
      deformPoint φ s + deformPoint φ b = deformPoint φ (a + x • d) := by
    calc
      deformPoint φ s + deformPoint φ b = deformPoint φ (s + b) :=
        ((deformPointLinear φ).map_add s b).symm
      _ = deformPoint φ (a + x • d) := congrArg (deformPoint φ) h
  have hyseg : y ∈ segment ℝ (deformPoint φ s + deformPoint φ e.1)
      (deformPoint φ s + deformPoint φ e.2) := by
    have h := integerCarrierOccurrence_targetSegment φ a s Z e q.1 q.2 v hcoords horder hvq
    simpa only [vadd_segment, vadd_eq_add] using h
  have hbound : dist (deformPoint φ s + deformPoint φ e.1)
      (deformPoint φ s + deformPoint φ e.2) ≤ L := by
    simpa only [dist_add_left] using (hlength φ hφl e he).2
  have nearEndpoint (x : ℝ) (hx : x = q.1 ∨ x = q.2)
      (hyx : dist y (deformPoint φ (a + x • d)) < M) :
      ∃ s ∈ T, s ≠ t ∧ w ∈ deformPoint φ s +ᵥ Kφ.support ∧
        Metric.infDist w (deformPoint φ s +ᵥ frontier Kφ.support) < η := by
    have hxJ : x ∈ J := hq.2 (by rcases hx with rfl | rfl <;> exact ⟨by linarith, by linarith⟩)
    have hxint : x ∈ interior J := by
      by_contra hn
      have h := hmargin x hxJ hn
      exact (not_lt_of_ge h) hyx
    have hwr : dist w (deformPoint φ (a + x • d)) < Rs := by
      have htr := dist_triangle w y (deformPoint φ (a + x • d))
      have hwy : dist w y < M := hw.trans_le (min_le_left _ _)
      linarith
    let c := v - (φ x : ℝ)
    have hyEq : y = deformPoint φ (a + x • d) + c • d := by
      have hmap : deformPoint φ (a + x • d) = deformPoint φ a + (φ x : ℝ) • d :=
        deformPoint_integerCarrierParameter φ a x Z
      rw [hmap]
      dsimp only [y, c]
      module
    have hcr : dist (c • d) 0 < Rs := by
      have hdist : dist (c • d) 0 = dist y (deformPoint φ (a + x • d)) := by
        rw [hyEq]
        simp [dist_eq_norm]
      rw [hdist]
      linarith
    have hyline : y ∈ Tiling.affineLine (deformPoint φ (a + x • d)) d :=
      (Tiling.mem_affineLine_iff_exists_smul hZ).mpr ⟨c, hyEq⟩
    have hhalves := same_oriented_halfPlanes_on_line hZ hyline
    have hside' : w - deformPoint φ (a + x • d) ∈
        (if positive then Tiling.positiveHalfPlane 0 d else Tiling.negativeHalfPlane 0 d) := by
      have hcross : Tiling.signedSide 0 d (w - deformPoint φ (a + x • d)) =
          Tiling.signedSide (deformPoint φ (a + x • d)) d w := by
        simp [Tiling.signedSide, Tiling.planarCross]
        ring
      cases positive with
      | true =>
        change w - deformPoint φ (a + x • d) ∈ Tiling.positiveHalfPlane 0 d
        have h := hside
        change w ∈ Tiling.positiveHalfPlane y d at h
        rw [← hhalves.1] at h
        apply Tiling.mem_positiveHalfPlane.mpr
        rw [hcross]
        exact Tiling.mem_positiveHalfPlane.mp h
      | false =>
        change w - deformPoint φ (a + x • d) ∈ Tiling.negativeHalfPlane 0 d
        have h := hside
        change w ∈ Tiling.negativeHalfPlane y d at h
        rw [← hhalves.2] at h
        apply Tiling.mem_negativeHalfPlane.mpr
        rw [hcross]
        exact Tiling.mem_negativeHalfPlane.mp h
    exact hstar φ hφs Kφ hKφ a d hZ r positive q hq x hx hxint w hwr hside' c hcr t η hpos
      (by simpa only [← hyEq] using hnear)
  rcases segmentPoint_centralOrNearEndpoints _ _ y L M τ hL hτ hτhalf hbound hτmargin hyseg with
    hleft | hright | ⟨θ, hθ, hyθ⟩
  · rcases hcoords with ⟨hl, _⟩ | ⟨_, hr⟩
    · exact nearEndpoint q.1 (Or.inl rfl) (by simpa only [mapEndpoint hl] using hleft)
    · exact nearEndpoint q.2 (Or.inr rfl) (by simpa only [mapEndpoint hr] using hleft)
  · rcases hcoords with ⟨_, hr⟩ | ⟨hl, _⟩
    · exact nearEndpoint q.2 (Or.inr rfl) (by simpa only [mapEndpoint hr] using hright)
    · exact nearEndpoint q.1 (Or.inl rfl) (by simpa only [mapEndpoint hl] using hright)
  · obtain ⟨b, hb, hsideB⟩ := actual_occurrence_side_alignment K a s d hZ e q.1 q.2 hqpos
      hcoords (hE e he).2.2.2.2.2 positive hsource
    have hb' : ∀ z ∈ openSegment ℝ e.1 e.2,
        if b then positiveEdgeGerm K.support (e.2 - e.1) z
        else negativeEdgeGerm K.support (e.2 - e.1) z := by
      cases b <;> simpa using hb
    have hyEq : y = deformPoint φ s +
        AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ := by
      rw [hyθ]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    have hwside : w ∈ (if b then Tiling.positiveHalfPlane y (e.2 - e.1)
        else Tiling.negativeHalfPlane y (e.2 - e.1)) := by
      have h := hsideB y w (by cases positive <;> simpa using hside)
      cases b <;> simpa using h
    have hwRc : dist w y < Rc := hw.trans_le (min_le_right _ _)
    exact hcentral φ hφc Kφ hKφ e he b hb' s hs θ hθ w
      (by simpa only [← hyEq] using hwRc) (by simpa only [← hyEq] using hwside) t η hpos
      (by simpa only [← hyEq] using hnear)


private theorem scalarCarrier_boundary_mem_endpoints
    (A : Set (ℝ × ℝ)) (J : Set ℝ)
    (hcover : ∀ x ∈ J, ∃ q ∈ A, x ∈ Icc q.1 q.2)
    (hinside : ∀ q ∈ A, Icc q.1 q.2 ⊆ J)
    {x : ℝ} (hx : x ∈ J) (hboundary : x ∉ interior J) :
    x ∈ scalarIntervalEndpoints A := by
  obtain ⟨q, hq, hxq⟩ := hcover x hx
  by_cases hleft : x = q.1
  · exact ⟨q, hq, Or.inl hleft⟩
  by_cases hright : x = q.2
  · exact ⟨q, hq, Or.inr hright⟩
  have hxopen : x ∈ Ioo q.1 q.2 :=
    ⟨lt_of_le_of_ne hxq.1 (Ne.symm hleft), lt_of_le_of_ne hxq.2 hright⟩
  have hxint : x ∈ interior (Icc q.1 q.2) := by simpa only [interior_Icc] using hxopen
  exact False.elim (hboundary (interior_mono (hinside q hq) hxint))


private theorem scalarCarrier_boundaryWindow_deformationMargin
    (A : Set (ℝ × ℝ)) (J : Set ℝ) (φ : ℝ → ℝ)
    (hcover : ∀ x ∈ J, ∃ q ∈ A, x ∈ Icc q.1 q.2)
    (hinside : ∀ q ∈ A, Icc q.1 q.2 ⊆ J)
    (horder : ∀ x ∈ scalarIntervalEndpoints A, ∀ y ∈ scalarIntervalEndpoints A,
      x ≤ y → φ x ≤ φ y)
    (lo hi : ℝ) (hlo : lo ∈ scalarIntervalEndpoints A)
    (hhi : hi ∈ scalarIntervalEndpoints A) (hwindow : Icc lo hi ⊆ J)
    (a d : Plane) (u M : ℝ) (hu : u ∈ Icc (φ lo) (φ hi))
    (hleft : M ≤ dist (a + u • d) (a + φ lo • d))
    (hright : M ≤ dist (a + u • d) (a + φ hi • d)) :
    ∀ x ∈ J, x ∉ interior J → M ≤ dist (a + u • d) (a + φ x • d) := by
  have hdist (r : ℝ) : dist (a + u • d) (a + r • d) = |u - r| * ‖d‖ := by
    rw [dist_eq_norm]
    have hsub : (a + u • d) - (a + r • d) = (u - r) • d := by module
    rw [hsub, norm_smul, Real.norm_eq_abs]
  intro x hx hboundary
  have hxS := scalarCarrier_boundary_mem_endpoints A J hcover hinside hx hboundary
  have houtside : x ≤ lo ∨ hi ≤ x := by
    by_cases hxlo : x ≤ lo
    · exact Or.inl hxlo
    · by_cases hxhi : hi ≤ x
      · exact Or.inr hxhi
      · have hxopen : x ∈ Ioo lo hi := ⟨lt_of_not_ge hxlo, lt_of_not_ge hxhi⟩
        have hxint : x ∈ interior (Icc lo hi) := by simpa only [interior_Icc] using hxopen
        exact False.elim (hboundary (interior_mono hwindow hxint))
  rcases houtside with hxlo | hxhi
  · have hφx := horder x hxS lo hlo hxlo
    rw [hdist, abs_of_nonneg (by linarith [hu.1] : 0 ≤ u - φ x)]
    rw [hdist, abs_of_nonneg (sub_nonneg.mpr hu.1)] at hleft
    exact hleft.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg d))
  · have hφx := horder hi hhi x hxS hxhi
    rw [hdist, abs_of_nonpos (by linarith [hu.2] : u - φ x ≤ 0)]
    rw [hdist, abs_of_nonpos (sub_nonpos.mpr hu.2)] at hright
    exact hright.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg d))


private theorem signedCarrierComponent_window_uniformMembershipMargin
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (Z : Tiling.RationalPolygonal.IntegerPlane)
    (hd : Tiling.RationalPolygonal.integerPoint Z ≠ 0) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ a : Plane, ∀ r l u : ℝ,
      a + r • Tiling.RationalPolygonal.integerPoint Z ∈
        ⋃ t : T, (t : Plane) +ᵥ frontier K.support →
      l < u →
      Icc l u ⊆ connectedComponentIn
        {s : ℝ | a + s • Tiling.RationalPolygonal.integerPoint Z ∈
          ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r →
      ∀ querySign : Bool,
      let J := connectedComponentIn
        {s : ℝ | a + s • Tiling.RationalPolygonal.integerPoint Z ∈
          ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r
      let A := signedCarrierComponentIntervals K T E a
        (Tiling.RationalPolygonal.integerPoint Z) r querySign
      ∀ L H : ℝ, L ∈ scalarIntervalEndpoints A → H ∈ scalarIntervalEndpoints A →
      Icc L H ⊆ J → ∀ v M : ℝ, v ∈ Icc (φ L : ℝ) (φ H : ℝ) →
      M ≤ dist (deformPoint φ a + v • Tiling.RationalPolygonal.integerPoint Z)
        (deformPoint φ (a + L • Tiling.RationalPolygonal.integerPoint Z)) →
      M ≤ dist (deformPoint φ a + v • Tiling.RationalPolygonal.integerPoint Z)
        (deformPoint φ (a + H • Tiling.RationalPolygonal.integerPoint Z)) →
      (∀ positive : Bool, v ∈ ⋃ q : signedCarrierComponentIntervals K T E a
        (Tiling.RationalPolygonal.integerPoint Z) r positive,
          Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ)) ∧
      (∀ x ∈ J, x ∉ interior J →
        M ≤ dist (deformPoint φ a + v • Tiling.RationalPolygonal.integerPoint Z)
          (deformPoint φ (a + x • Tiling.RationalPolygonal.integerPoint Z))) := by
  let d := Tiling.RationalPolygonal.integerPoint Z
  obtain ⟨F, ε, hε, htransport⟩ :=
    packingSol_uniformActualSourceCarrierTransport K T htile E hE hcover d hd
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ a r l u hr hlu hinterval querySign
  let J := connectedComponentIn
    {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r
  let A := signedCarrierComponentIntervals K T E a d r querySign
  change ∀ L H : ℝ, L ∈ scalarIntervalEndpoints A → H ∈ scalarIntervalEndpoints A →
    Icc L H ⊆ J → _
  intro L H hL hH hwindow v M hv hleft hright
  obtain ⟨hshape, hbound, _, _, hcases⟩ :=
    htransport φ hφ a r l u hr hlu hinterval querySign
  have hweak : ∀ x ∈ scalarIntervalEndpoints A, ∀ y ∈ scalarIntervalEndpoints A,
      x ≤ y → (φ x : ℝ) ≤ (φ y : ℝ) := by
    intro x hx y hy hxy
    rcases lt_or_eq_of_le hxy with hxy | rfl
    · have h := (hbound x hx y hy hxy).1
      linarith
    · exact le_rfl
  let U : Set ℝ := ⋃ q : A, Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ)
  have hUord : U.OrdConnected := by
    rcases hshape with ⟨lo, hi, hlohi, hJ⟩ | ⟨lo, hJ⟩ | ⟨hi, hJ⟩ | hJ
    · rw [show U = Icc (φ lo : ℝ) (φ hi : ℝ) from hcases.1 lo hi hlohi hJ]
      exact Set.ordConnected_Icc
    · rw [show U = Ici (φ lo : ℝ) from hcases.2.1 lo hJ]
      exact Set.ordConnected_Ici
    · rw [show U = Iic (φ hi : ℝ) from hcases.2.2.1 hi hJ]
      exact Set.ordConnected_Iic
    · rw [show U = Set.univ from hcases.2.2.2 hJ]
      exact Set.ordConnected_univ
  have hendpointMem : ∀ x ∈ scalarIntervalEndpoints A, (φ x : ℝ) ∈ U := by
    rintro x ⟨q, hq, rfl | rfl⟩
    · exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, le_rfl,
        hweak q.1 ⟨q, hq, Or.inl rfl⟩ q.2 ⟨q, hq, Or.inr rfl⟩ hq.1.1.le⟩
    · exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩,
        hweak q.1 ⟨q, hq, Or.inl rfl⟩ q.2 ⟨q, hq, Or.inr rfl⟩ hq.1.1.le, le_rfl⟩
  have hvU : v ∈ U := hUord.out (hendpointMem L hL) (hendpointMem H hH) hv
  refine ⟨?_, ?_⟩
  · intro positive
    obtain ⟨_, _, _, _, hother⟩ := htransport φ hφ a r l u hr hlu hinterval positive
    have hequal : U = ⋃ q : signedCarrierComponentIntervals K T E a d r positive,
        Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ) := by
      rcases hshape with ⟨lo, hi, hlohi, hJ⟩ | ⟨lo, hJ⟩ | ⟨hi, hJ⟩ | hJ
      · exact (hcases.1 lo hi hlohi hJ).trans (hother.1 lo hi hlohi hJ).symm
      · exact (hcases.2.1 lo hJ).trans (hother.2.1 lo hJ).symm
      · exact (hcases.2.2.1 hi hJ).trans (hother.2.2.1 hi hJ).symm
      · exact (hcases.2.2.2 hJ).trans (hother.2.2.2 hJ).symm
    exact hequal ▸ hvU
  · have hsourceCover : ∀ x ∈ J, ∃ q ∈ A, x ∈ Icc q.1 q.2 := by
      have hcoverJ := signedCarrierComponentIntervals_closedCover
        K T htile E hE hcover a d hd r l u hr hlu hinterval querySign
      change (⋃ q : A, Icc q.1.1 q.1.2) = J at hcoverJ
      intro x hx
      obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp (hcoverJ.symm ▸ hx)
      exact ⟨q.1, q.2, hxq⟩
    have hinside : ∀ q ∈ A, Icc q.1 q.2 ⊆ J := fun q hq => hq.2
    rw [deformPoint_integerCarrierParameter φ a L Z] at hleft
    rw [deformPoint_integerCarrierParameter φ a H Z] at hright
    have hmargin := scalarCarrier_boundaryWindow_deformationMargin A J
      (fun x : ℝ => (φ x : ℝ)) hsourceCover hinside hweak L H hL hH hwindow
      (deformPoint φ a) d v M hv hleft hright
    intro x hx hboundary
    rw [deformPoint_integerCarrierParameter φ a x Z]
    exact hmargin x hx hboundary


private theorem rationalPrimitiveEdge_uniformCentral_outwardSide
    (K : PolygonalRegion) (P : PolyhedralCode) (hP : polyhedralSupport P = K.support)
    (E : Finset (Plane × Plane))
    (hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet K.support)
    (hrational : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (e : Plane × Plane) (he : e ∈ E) (τ : ℝ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (positive : Bool)
    (hsource : ∀ p ∈ openSegment ℝ e.1 e.2,
      if positive then positiveEdgeGerm K.support (e.2 - e.1) p
      else negativeEdgeGerm K.support (e.2 - e.1) p) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ t : Plane, ∀ θ ∈ Icc τ (1 - τ),
      let y := deformPoint φ t +
        AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ
      ∀ w : Plane, dist w y < R →
      0 < Metric.infDist w (deformPoint φ t +ᵥ Kφ.support) →
      w ∈ (if positive then Tiling.negativeHalfPlane y (e.2 - e.1)
        else Tiling.positiveHalfPlane y (e.2 - e.1)) := by
  obtain ⟨F, ε, R, hε, hR, hstrip⟩ := rationalPrimitiveEdge_uniformCentralSameSide
    K P hP E hprimitive hrational hcover e he τ hτ hτhalf positive hsource
  refine ⟨F, ε, R, hε, hR, ?_⟩
  intro φ hφ Kφ hKφ t θ hθ
  dsimp only
  intro w hw hpos
  let y0 := AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ
  have hdist : dist (w - deformPoint φ t) y0 = dist w (deformPoint φ t + y0) := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have hsideEq : Tiling.signedSide (deformPoint φ t + y0) (e.2 - e.1) w =
      Tiling.signedSide y0 (e.2 - e.1) (w - deformPoint φ t) := by
    have hpoint : y0 + (w - (deformPoint φ t + y0)) = w - deformPoint φ t := by abel
    simpa only [add_sub_cancel, hpoint] using
      signedSide_translation (deformPoint φ t + y0) y0 (e.2 - e.1)
        (w - (deformPoint φ t + y0))
  have hnot : w - deformPoint φ t ∉
      (if positive then Tiling.positiveHalfPlane y0 (e.2 - e.1)
        else Tiling.negativeHalfPlane y0 (e.2 - e.1)) := by
    intro hside
    have hball : w - deformPoint φ t ∈ Metric.ball y0 R := by
      rw [Metric.mem_ball, hdist]
      exact hw
    have hmem : w - deformPoint φ t ∈ Kφ.support ∩ Metric.ball y0 R := by
      rw [hstrip φ hφ Kφ hKφ θ hθ]
      exact ⟨hside, hball⟩
    have hcopy : w ∈ deformPoint φ t +ᵥ Kφ.support := by
      apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
      simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using hmem.1
    have hzero := Metric.infDist_le_dist_of_mem (x := w) hcopy
    simp only [dist_self] at hzero
    linarith
  cases positive with
  | true =>
      apply Tiling.mem_negativeHalfPlane.mpr
      change Tiling.signedSide (deformPoint φ t + y0) (e.2 - e.1) w ≤ 0
      rw [hsideEq]
      exact (lt_of_not_ge (fun h => hnot (Tiling.mem_positiveHalfPlane.mpr h))).le
  | false =>
      apply Tiling.mem_positiveHalfPlane.mpr
      change 0 ≤ Tiling.signedSide (deformPoint φ t + y0) (e.2 - e.1) w
      rw [hsideEq]
      exact (lt_of_not_ge (fun h => hnot (Tiling.mem_negativeHalfPlane.mpr h))).le


private theorem rationalPrimitiveEdge_uniformCentral_actualChainCollar
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (e : Plane × Plane) (he : e ∈ E)
    (Z : Tiling.RationalPolygonal.IntegerPlane)
    (hd : Tiling.RationalPolygonal.integerPoint Z ≠ 0)
    (c : ℝ) (hc : 0 < c)
    (hvec : e.2 - e.1 = c • Tiling.RationalPolygonal.integerPoint Z)
    (τ : ℝ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (positive : Bool)
    (hsource : ∀ p ∈ openSegment ℝ e.1 e.2,
      if positive then positiveEdgeGerm K.support (e.2 - e.1) p
      else negativeEdgeGerm K.support (e.2 - e.1) p) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ t ∈ T, ∀ θ ∈ Icc τ (1 - τ),
      let y := deformPoint φ t +
        AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ
      ∀ w : Plane, dist w y < R → ∀ η : ℝ,
      0 < Metric.infDist w (deformPoint φ t +ᵥ Kφ.support) → dist w y < η →
      ∃ s ∈ T, s ≠ t ∧ w ∈ deformPoint φ s +ᵥ Kφ.support ∧
        Metric.infDist w (deformPoint φ s +ᵥ frontier Kφ.support) < η := by
  let d := Tiling.RationalPolygonal.integerPoint Z
  have hprimitive : ∀ f ∈ E, f.1 ≠ f.2 ∧ f.1 ∈ Tiling.vertexSet K.support ∧
      f.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ f.1 f.2 ⊆ frontier K.support ∧
      ∀ p ∈ openSegment ℝ f.1 f.2, p ∉ Tiling.vertexSet K.support :=
    fun f hf => ⟨(hE f hf).1, (hE f hf).2.1, (hE f hf).2.2.1,
      (hE f hf).2.2.2.1, (hE f hf).2.2.2.2.1⟩
  obtain ⟨Rs, hRs, haugmented⟩ :=
    signedCarrierComponent_uniformAugmentedCollar K P T hP htile E hE hrat hcover
  obtain ⟨Fl, εl, l₀, L₀, hεl, hl₀, _, hlength⟩ :=
    finiteRationalEdges_uniformLengthRange E hrat
  let M := min (Rs / 4) (τ * l₀)
  have hM : 0 < M := lt_min (by positivity) (mul_pos hτ hl₀)
  obtain ⟨Fa, εa, ρa, hεa, hρa, hcollar⟩ :=
    haugmented M hM (min_le_left _ _) Z hd
  obtain ⟨Fo, εo, ρo, hεo, hρo, houtward⟩ :=
    rationalPrimitiveEdge_uniformCentral_outwardSide K P hP E hprimitive hrat hcover
      e he τ hτ hτhalf positive hsource
  obtain ⟨Fw, εw, hεw, hwindow⟩ :=
    signedCarrierComponent_window_uniformMembershipMargin K T htile E hE hcover Z hd
  let F := (Fl ∪ Fa) ∪ (Fo ∪ Fw) ∪ {c}
  let ε := min εl (min εa (min εo (min εw (c / 2))))
  have hε : 0 < ε := lt_min hεl (lt_min hεa (lt_min hεo (lt_min hεw (by positivity))))
  refine ⟨F, ε, min ρa ρo, hε, lt_min hρa hρo, ?_⟩
  intro φ hφ Kφ hKφ t ht θ hθ
  dsimp only
  intro w hw η hpos hnear
  have hφl : IsFiniteApproximation Fl εl φ := by
    apply finiteApproximation_strengthen Fl F εl ε φ _ (min_le_left _ _) hφ
    intro x hx
    simp [F, hx]
  have hφa : IsFiniteApproximation Fa εa φ := by
    apply finiteApproximation_strengthen Fa F εa ε φ _
      ((min_le_right _ _).trans (min_le_left _ _)) hφ
    intro x hx
    simp [F, hx]
  have hφo : IsFiniteApproximation Fo εo φ := by
    apply finiteApproximation_strengthen Fo F εo ε φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) hφ
    intro x hx
    simp [F, hx]
  have hφw : IsFiniteApproximation Fw εw φ := by
    apply finiteApproximation_strengthen Fw F εw ε φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))) hφ
    intro x hx
    simp [F, hx]
  have hφc : 0 < (φ c : ℝ) := by
    have hclose := hφ.2 c (by simp [F])
    have hεc : ε ≤ c / 2 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    have hdiff := (abs_lt.mp (hclose.trans_le hεc)).1
    linarith
  let a := t + e.1
  let y := deformPoint φ t +
    AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ
  let v := θ * (φ c : ℝ)
  change dist w y < min ρa ρo at hw
  change dist w y < η at hnear
  have hcoords : t + e.1 = a + (0 : ℝ) • d ∧ t + e.2 = a + c • d := by
    constructor
    · simp [a]
    · dsimp only [a]
      have heq : e.2 = e.1 + c • d := by rw [← hvec]; abel
      rw [heq]
      abel
  obtain ⟨querySign, hq, _⟩ := packingSol_primitiveOccurrence_signedFamily K T E a d t hd ht
    e he (0, c) hc (Or.inl hcoords) (hE e he).2.2.2.2.2
  have hr : a + (0 : ℝ) • d ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support := by
    have hp : e.1 ∈ frontier K.support := (hE e he).2.2.2.1 (left_mem_segment ℝ e.1 e.2)
    have hmem : t + e.1 ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support :=
      Set.mem_iUnion.mpr ⟨⟨t, ht⟩, Set.vadd_mem_vadd_set hp⟩
    simpa only [zero_smul, add_zero, a] using hmem
  let J := connectedComponentIn {s : ℝ | a + s • d ∈
    ⋃ t : T, (t : Plane) +ᵥ frontier K.support} 0
  have hinterval : Icc (0 : ℝ) c ⊆ J :=
    signedCarrierInterval_subset_component_of_meets K T E
      (fun f hf => (hE f hf).2.2.2.1) a d querySign hr hq
      ⟨0, ⟨le_rfl, hc.le⟩, mem_connectedComponentIn hr⟩
  let A := signedCarrierComponentIntervals K T E a d 0 querySign
  have hqA : (0, c) ∈ A := ⟨hq, hinterval⟩
  have hyEq : y = deformPoint φ a + v • d := by
    have heq : e.2 = e.1 + c • d := by rw [← hvec]; abel
    have hmap : deformPoint φ e.2 = deformPoint φ e.1 + (φ c : ℝ) • d := by
      rw [heq]
      exact deformPoint_integerCarrierParameter φ e.1 c Z
    have hamap : deformPoint φ a = deformPoint φ t + deformPoint φ e.1 :=
      (deformPointLinear φ).map_add t e.1
    rw [hamap]
    dsimp only [y, v]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, hmap]
    module
  have hv : v ∈ Icc (φ (0 : ℝ) : ℝ) (φ c : ℝ) := by
    simp only [map_zero, Rat.cast_zero]
    have hθ0 : 0 ≤ θ := hτ.le.trans hθ.1
    have hθ1 : θ ≤ 1 := hθ.2.trans (by linarith)
    exact ⟨mul_nonneg hθ0 hφc.le, mul_le_of_le_one_left hφc.le hθ1⟩
  have hleft : M ≤ dist y (deformPoint φ (a + (0 : ℝ) • d)) := by
    have ha : deformPoint φ (a + (0 : ℝ) • d) = deformPoint φ t + deformPoint φ e.1 := by
      simp only [zero_smul, add_zero]
      exact (deformPointLinear φ).map_add t e.1
    rw [ha]
    dsimp only [y]
    have hdist : dist (AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ)
        (deformPoint φ e.1) = |θ| * dist (deformPoint φ e.1) (deformPoint φ e.2) := by
      rw [dist_eq_norm, AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, norm_smul, Real.norm_eq_abs]
      rw [← dist_eq_norm, dist_comm]
    rw [dist_add_left, hdist,
      abs_of_nonneg (hτ.le.trans hθ.1)]
    exact (min_le_right _ _).trans
      (mul_le_mul hθ.1 (hlength φ hφl e he).1 hl₀.le (hτ.le.trans hθ.1))
  have hright : M ≤ dist y (deformPoint φ (a + c • d)) := by
    have ha : deformPoint φ (a + c • d) = deformPoint φ t + deformPoint φ e.2 := by
      rw [← hcoords.2]
      exact (deformPointLinear φ).map_add t e.2
    rw [ha]
    dsimp only [y]
    have hdist : dist (AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ)
        (deformPoint φ e.2) = |1 - θ| * dist (deformPoint φ e.1) (deformPoint φ e.2) := by
      rw [dist_eq_norm, AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add]
      have hsub : θ • (deformPoint φ e.2 - deformPoint φ e.1) + deformPoint φ e.1 -
          deformPoint φ e.2 = (1 - θ) • (deformPoint φ e.1 - deformPoint φ e.2) := by module
      rw [hsub, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
    rw [dist_add_left, hdist,
      abs_of_nonneg (by linarith [hθ.2] : 0 ≤ 1 - θ)]
    exact (min_le_right _ _).trans
      (mul_le_mul (by linarith [hθ.2] : τ ≤ 1 - θ)
        (hlength φ hφl e he).1 hl₀.le (by linarith [hθ.2]))
  obtain ⟨hmember, hmargin⟩ := hwindow φ hφw a 0 0 c hr hc hinterval querySign
    0 c ⟨(0, c), hqA, Or.inl rfl⟩ ⟨(0, c), hqA, Or.inr rfl⟩ hinterval v M hv
    (by change M ≤ dist (deformPoint φ a + v • d) _; rw [← hyEq]; exact hleft)
    (by change M ≤ dist (deformPoint φ a + v • d) _; rw [← hyEq]; exact hright)
  have hside := houtward φ hφo Kφ hKφ t θ hθ w
    (hw.trans_le (min_le_right _ _)) hpos
  change w ∈ (if positive then Tiling.negativeHalfPlane y (e.2 - e.1)
    else Tiling.positiveHalfPlane y (e.2 - e.1)) at hside
  have hplanes := orientedHalfPlanes_positiveScale y d c hc
  have hside' : w ∈ (if !positive then Tiling.positiveHalfPlane y d
      else Tiling.negativeHalfPlane y d) := by
    have hvec' : e.2 - e.1 = c • d := hvec
    rw [hvec'] at hside
    cases positive <;> simpa only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, hplanes.1, hplanes.2] using hside
  exact hcollar φ hφa Kφ hKφ a 0 0 c hr hc hinterval (!positive) v (hmember (!positive))
    hmargin w (by
      change dist w (deformPoint φ a + v • d) < ρa
      rw [← hyEq]
      exact hw.trans_le (min_le_left _ _))
    (by
      change w ∈ (if !positive then Tiling.positiveHalfPlane
        (deformPoint φ a + v • d) d else Tiling.negativeHalfPlane
        (deformPoint φ a + v • d) d)
      rw [← hyEq]
      exact hside')
    t η hpos (by change dist w (deformPoint φ a + v • d) < η; rw [← hyEq]; exact hnear)


private theorem rationalPrimitiveEdges_uniformCentral_actualChainCollar
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (τ : ℝ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ e ∈ E, ∀ t ∈ T, ∀ θ ∈ Icc τ (1 - τ),
      let y := deformPoint φ t +
        AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ
      ∀ w : Plane, dist w y < R → ∀ η : ℝ,
      0 < Metric.infDist w (deformPoint φ t +ᵥ Kφ.support) → dist w y < η →
      ∃ s ∈ T, s ≠ t ∧ w ∈ deformPoint φ s +ᵥ Kφ.support ∧
        Metric.infDist w (deformPoint φ s +ᵥ frontier Kφ.support) < η := by
  classical
  let Q (e : Plane × Plane) (φ : ℝ →ₗ[ℚ] ℚ) (R : ℝ) : Prop :=
    ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
    ∀ t ∈ T, ∀ θ ∈ Icc τ (1 - τ),
    ∀ w : Plane,
      dist w (deformPoint φ t +
        AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ) < R →
    ∀ η : ℝ, 0 < Metric.infDist w (deformPoint φ t +ᵥ Kφ.support) →
      dist w (deformPoint φ t +
        AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ) < η →
    ∃ s ∈ T, s ≠ t ∧ w ∈ deformPoint φ s +ᵥ Kφ.support ∧
      Metric.infDist w (deformPoint φ s +ᵥ frontier Kφ.support) < η
  have hlocal : ∀ e ∈ E, ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ → Q e φ R := by
    intro e he
    obtain ⟨Z, c, hc, hvec⟩ := rationalVector_positiveIntegerMultiple (e.2 - e.1) (hrat e he)
    have hd : Tiling.RationalPolygonal.integerPoint Z ≠ 0 := by
      intro hz
      rw [hz, smul_zero] at hvec
      exact (hE e he).1 (sub_eq_zero.mp hvec).symm
    have hsign : ∃ positive : Bool, ∀ z ∈ openSegment ℝ e.1 e.2,
        if positive then positiveEdgeGerm K.support (e.2 - e.1) z
        else negativeEdgeGerm K.support (e.2 - e.1) z := by
      rcases (hE e he).2.2.2.2.2 with hpos | hneg
      · exact ⟨true, hpos⟩
      · exact ⟨false, hneg⟩
    obtain ⟨positive, hsource⟩ := hsign
    exact rationalPrimitiveEdge_uniformCentral_actualChainCollar K P T hP htile E hE
      hrat hcover e he Z hd c hc hvec τ hτ hτhalf positive hsource
  have hmono : ∀ e ∈ E, ∀ φ r R, r ≤ R → Q e φ R → Q e φ r := by
    intro e _ φ r R hr hQ Kφ hKφ t ht θ hθ w hw η hpos hnear
    exact hQ Kφ hKφ t ht θ hθ w (hw.trans_le hr) η hpos hnear
  obtain ⟨F, ε, R, hε, hR, hQ⟩ := finiteApproximation_uniformPositiveRadius E Q hmono hlocal
  refine ⟨F, ε, R, hε, hR, ?_⟩
  intro φ hφ Kφ hKφ e he t ht θ hθ
  exact hQ φ hφ e he Kφ hKφ t ht θ hθ


private theorem projectionWindow_deepInterior
    (p q d : Plane) (hd : d ≠ 0) (lo hi l : ℝ)
    (hlo : lo < 0) (hhi : 0 < hi) (hl : 0 < l)
    (hleft : l ≤ dist p (p + lo • d))
    (hright : l ≤ dist p (p + hi • d))
    (hq : q ∈ Tiling.affineLine p d) (hnear : dist q p < l / 4) :
    ∃ v : ℝ, q = p + v • d ∧ v ∈ Icc lo hi ∧
      3 * l / 4 ≤ dist q (p + lo • d) ∧
      3 * l / 4 ≤ dist q (p + hi • d) := by
  obtain ⟨v, hv⟩ := (Tiling.mem_affineLine_iff_exists_smul hd).mp hq
  have hN : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hleftEq : dist p (p + lo • d) = (-lo) * ‖d‖ := by
    rw [dist_eq_norm, show p - (p + lo • d) = -(lo • d) by module]
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_neg hlo]
  have hrightEq : dist p (p + hi • d) = hi * ‖d‖ := by
    rw [dist_eq_norm, show p - (p + hi • d) = -(hi • d) by module]
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hhi]
  have hnearEq : dist (p + v • d) p = |v| * ‖d‖ := by
    rw [dist_eq_norm, show p + v • d - p = v • d by module]
    rw [norm_smul, Real.norm_eq_abs]
  have hsmall : |v| * ‖d‖ < l / 4 := by simpa [hv, dist_comm] using hnear
  have hleft' : l ≤ (-lo) * ‖d‖ := by rw [← hleftEq]; exact hleft
  have hright' : l ≤ hi * ‖d‖ := by rw [← hrightEq]; exact hright
  have hvlo : lo ≤ v := by
    by_contra hnot
    have hvlt : v < lo := lt_of_not_ge hnot
    have habs : -lo < |v| := by rw [abs_of_neg (lt_trans hvlt hlo)]; linarith
    have hmul : (-lo) * ‖d‖ < |v| * ‖d‖ := mul_lt_mul_of_pos_right habs hN
    linarith
  have hvhi : v ≤ hi := by
    by_contra hnot
    have hvgt : hi < v := lt_of_not_ge hnot
    have habs : hi < |v| := by rw [abs_of_pos (lt_trans hhi hvgt)]; linarith
    have hmul : hi * ‖d‖ < |v| * ‖d‖ := mul_lt_mul_of_pos_right habs hN
    linarith
  have hleftDist : dist q (p + lo • d) = (v - lo) * ‖d‖ := by
    rw [hv, dist_eq_norm, show p + v • d - (p + lo • d) = (v - lo) • d by module]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hvlo)]
  have hrightDist : dist q (p + hi • d) = (hi - v) * ‖d‖ := by
    rw [hv, dist_eq_norm, show p + v • d - (p + hi • d) = (v - hi) • d by module]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hvhi)]
    ring
  have hleftMargin : 3 * l / 4 ≤ dist q (p + lo • d) := by
    rw [hleftDist]
    have hvN : -(|v| * ‖d‖) ≤ v * ‖d‖ := by
      nlinarith [neg_abs_le v]
    nlinarith
  have hrightMargin : 3 * l / 4 ≤ dist q (p + hi • d) := by
    rw [hrightDist]
    have hvN : v * ‖d‖ ≤ |v| * ‖d‖ := by
      nlinarith [le_abs_self v]
    nlinarith
  exact ⟨v, hv, ⟨hvlo, hvhi⟩, hleftMargin, hrightMargin⟩


private theorem positiveHalfPlane_ne_negativeHalfPlane_of_ne {d : Plane} (hd : d ≠ 0) :
    Tiling.positiveHalfPlane 0 d ≠ Tiling.negativeHalfPlane 0 d := by
  intro h
  have hz : d * Complex.I ∈ Tiling.positiveHalfPlane 0 d := by
    rw [Tiling.mem_positiveHalfPlane]
    have hs : Tiling.signedSide 0 d (d * Complex.I) = Complex.normSq d := by
      simpa only [zero_add] using Tiling.signedSide_add_mul_I 0 d
    rw [hs]
    exact le_of_lt (Complex.normSq_pos.mpr hd)
  have hbadmem : d * Complex.I ∈ Tiling.negativeHalfPlane 0 d := by
    rw [← h]
    exact hz
  have hbad := Tiling.mem_negativeHalfPlane.mp hbadmem
  have hs : Tiling.signedSide 0 d (d * Complex.I) = Complex.normSq d := by
    simpa only [zero_add] using Tiling.signedSide_add_mul_I 0 d
  rw [hs] at hbad
  exact (not_le_of_gt (Complex.normSq_pos.mpr hd)) hbad

private theorem directedHalfPlane_ne_univ {d : Plane} (hd : d ≠ 0) (positive : Bool) :
    (if positive then Tiling.positiveHalfPlane 0 d else Tiling.negativeHalfPlane 0 d) ≠
      Set.univ := by
  intro h
  by_cases hp : positive
  · have hz : -(d * Complex.I) ∉ Tiling.positiveHalfPlane 0 d := by
      rw [Tiling.mem_positiveHalfPlane]
      have hs : Tiling.signedSide 0 d (-(d * Complex.I)) = -Complex.normSq d := by
        simpa only [zero_sub] using Tiling.signedSide_sub_mul_I 0 d
      rw [hs]
      exact not_le_of_gt (neg_lt_zero.mpr (Complex.normSq_pos.mpr hd))
    have hsel : Tiling.positiveHalfPlane 0 d = Set.univ := by simpa [hp] using h
    have hmem : -(d * Complex.I) ∈ Tiling.positiveHalfPlane 0 d := by
      rw [hsel]
      simp
    exact hz hmem
  · have hz : d * Complex.I ∉ Tiling.negativeHalfPlane 0 d := by
      rw [Tiling.mem_negativeHalfPlane]
      have hs : Tiling.signedSide 0 d (d * Complex.I) = Complex.normSq d := by
        simpa only [zero_add] using Tiling.signedSide_add_mul_I 0 d
      rw [hs]
      exact not_le_of_gt (Complex.normSq_pos.mpr hd)
    have hsel : Tiling.negativeHalfPlane 0 d = Set.univ := by
      simpa [hp] using h
    have hmem : d * Complex.I ∈ Tiling.negativeHalfPlane 0 d := by
      rw [hsel]
      simp
    exact hz hmem

/-- An actual signed occurrence family at an internal source-carrier endpoint
must use the unique occupied side of the original vertex star. -/
private theorem signedCarrierComponent_bool_eq_of_halfStar
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hvertices : ∀ e ∈ E,
      e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support)
    (a d : Plane) (hd : d ≠ 0) (r : ℝ)
    (q : ℝ × ℝ) (positive : Bool)
    (hq : q ∈ signedCarrierComponentIntervals K T E a d r positive)
    (hx : 0 = q.1 ∨ 0 = q.2)
    (hxJ : 0 ∈ interior (connectedComponentIn
      {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r))
    (occupied : Bool)
    (hstar : originalVertexConeUnion K P T a =
      (if occupied then Tiling.positiveHalfPlane 0 d else Tiling.negativeHalfPlane 0 d)) :
    positive = occupied := by
  have hside := signedCarrierComponentInterval_internalEndpoint_starSide K P T hP htile
    E hvertices a d hd r positive q hq 0 hx hxJ
  rcases hside with hfull | hchosen
  · have hne := directedHalfPlane_ne_univ hd occupied
    have hfull' : originalVertexConeUnion K P T a = Set.univ := by simpa using hfull
    exact False.elim (hne (hstar.symm.trans hfull'))
  · cases positive <;> cases occupied
    · rfl
    · have heq : Tiling.negativeHalfPlane 0 d = Tiling.positiveHalfPlane 0 d := by
        have hchosen' : originalVertexConeUnion K P T a = Tiling.negativeHalfPlane 0 d := by
          simpa using hchosen
        exact hchosen'.symm.trans hstar
      exact False.elim (positiveHalfPlane_ne_negativeHalfPlane_of_ne hd heq.symm)
    · have heq : Tiling.positiveHalfPlane 0 d = Tiling.negativeHalfPlane 0 d := by
        have hchosen' : originalVertexConeUnion K P T a = Tiling.positiveHalfPlane 0 d := by
          simpa using hchosen
        exact hchosen'.symm.trans hstar
      exact False.elim (positiveHalfPlane_ne_negativeHalfPlane_of_ne hd heq)
    · rfl


private theorem twoTangentOccurrences_occupiedSourceWindow
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (a d : Plane) (hd : d ≠ 0) (occupied : Bool)
    (hstar : originalVertexConeUnion K P T a =
      (if occupied then Tiling.positiveHalfPlane 0 d else Tiling.negativeHalfPlane 0 d))
    (sMinus : Plane) (hsMinus : sMinus ∈ T)
    (eMinus : Plane × Plane) (heMinus : eMinus ∈ E) (cMinus : ℝ) (hcMinus : 0 < cMinus)
    (hendsMinus :
      (sMinus + eMinus.1 = a + (-cMinus) • d ∧ sMinus + eMinus.2 = a) ∨
      (sMinus + eMinus.2 = a + (-cMinus) • d ∧ sMinus + eMinus.1 = a))
    (sPlus : Plane) (hsPlus : sPlus ∈ T)
    (ePlus : Plane × Plane) (hePlus : ePlus ∈ E) (cPlus : ℝ) (hcPlus : 0 < cPlus)
    (hendsPlus :
      (sPlus + ePlus.1 = a ∧ sPlus + ePlus.2 = a + cPlus • d) ∨
      (sPlus + ePlus.2 = a ∧ sPlus + ePlus.1 = a + cPlus • d)) :
    Icc (-cMinus) cPlus ⊆ connectedComponentIn
      {r : ℝ | a + r • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} 0 ∧
    (-cMinus, 0) ∈ signedCarrierComponentIntervals K T E a d 0 occupied ∧
    (0, cPlus) ∈ signedCarrierComponentIntervals K T E a d 0 occupied := by
  let qMinus : ℝ × ℝ := (-cMinus, 0)
  let qPlus : ℝ × ℝ := (0, cPlus)
  have hcoordsMinus :
      (sMinus + eMinus.1 = a + qMinus.1 • d ∧ sMinus + eMinus.2 = a + qMinus.2 • d) ∨
      (sMinus + eMinus.2 = a + qMinus.1 • d ∧ sMinus + eMinus.1 = a + qMinus.2 • d) := by
    simpa [qMinus] using hendsMinus
  have hcoordsPlus :
      (sPlus + ePlus.1 = a + qPlus.1 • d ∧ sPlus + ePlus.2 = a + qPlus.2 • d) ∨
      (sPlus + ePlus.2 = a + qPlus.1 • d ∧ sPlus + ePlus.1 = a + qPlus.2 • d) := by
    simpa [qPlus] using hendsPlus
  have horderMinus : qMinus.1 < qMinus.2 := by simp [qMinus]; linarith
  have horderPlus : qPlus.1 < qPlus.2 := by simp [qPlus]; exact hcPlus
  have hproto e (he : e ∈ E) := (hE e he).2.2.2.2.2
  obtain ⟨bMinus, hqMinus, _⟩ := packingSol_primitiveOccurrence_signedFamily K T E a d
    sMinus hd hsMinus eMinus heMinus qMinus horderMinus hcoordsMinus (hproto eMinus heMinus)
  obtain ⟨bPlus, hqPlus, _⟩ := packingSol_primitiveOccurrence_signedFamily K T E a d
    sPlus hd hsPlus ePlus hePlus qPlus horderPlus hcoordsPlus (hproto ePlus hePlus)
  have hfrontier e (he : e ∈ E) : segment ℝ e.1 e.2 ⊆ frontier K.support :=
    (hE e he).2.2.2.1
  have haFront : a ∈ sMinus +ᵥ frontier K.support := by
    rcases hendsMinus with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · have heFront := hfrontier eMinus heMinus (right_mem_segment ℝ eMinus.1 eMinus.2)
      rw [← hright]
      exact Set.vadd_mem_vadd_set heFront
    · have heFront := hfrontier eMinus heMinus (left_mem_segment ℝ eMinus.1 eMinus.2)
      rw [← hright]
      exact Set.vadd_mem_vadd_set heFront
  have hbase : 0 ∈ {r : ℝ | a + r • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} := by
    simp only [Set.mem_setOf_eq, zero_smul, add_zero]
    exact Set.mem_iUnion.mpr ⟨⟨sMinus, hsMinus⟩, by simpa only [vadd_eq_add] using haFront⟩
  let J := connectedComponentIn
    {r : ℝ | a + r • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} 0
  have hJbase : 0 ∈ J := mem_connectedComponentIn hbase
  have hminusSubset : Icc qMinus.1 qMinus.2 ⊆ J := by
    apply signedCarrierInterval_subset_component_of_meets K T E hfrontier a d bMinus hbase hqMinus
    exact ⟨0, ⟨by simp [qMinus]; linarith [hcMinus], le_rfl⟩, by simpa [J] using hJbase⟩
  have hplusSubset : Icc qPlus.1 qPlus.2 ⊆ J := by
    apply signedCarrierInterval_subset_component_of_meets K T E hfrontier a d bPlus hbase hqPlus
    exact ⟨0, ⟨le_rfl, hcPlus.le⟩, by simpa [J] using hJbase⟩
  have hwindow : Icc (-cMinus) cPlus ⊆ J := by
    intro x hx
    rcases le_total x 0 with hxleft | hxright
    · exact hminusSubset ⟨hx.1, by simpa [qMinus] using hxleft⟩
    · exact hplusSubset ⟨by simpa [qPlus] using hxright, hx.2⟩
  have hzeroInterior : 0 ∈ interior J := by
    apply interior_maximal (Set.Ioo_subset_Icc_self.trans hwindow)
    · exact isOpen_Ioo
    · exact ⟨by linarith, by linarith⟩
  have hvertices : ∀ e ∈ E,
      e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).2.1, (hE e he).2.2.1⟩
  have hqCompMinus : qMinus ∈ signedCarrierComponentIntervals K T E a d 0 bMinus := by
    change qMinus ∈ signedCarrierIntervals K T E a d bMinus ∧ _
    exact ⟨hqMinus, by simpa [J] using hminusSubset⟩
  have hqCompPlus : qPlus ∈ signedCarrierComponentIntervals K T E a d 0 bPlus := by
    change qPlus ∈ signedCarrierIntervals K T E a d bPlus ∧ _
    exact ⟨hqPlus, by simpa [J] using hplusSubset⟩
  have hbMinus : bMinus = occupied :=
    signedCarrierComponent_bool_eq_of_halfStar K P T hP htile E hvertices a d hd 0
      qMinus bMinus hqCompMinus (by simp [qMinus])
      (by simpa [J] using hzeroInterior) occupied hstar
  have hbPlus : bPlus = occupied :=
    signedCarrierComponent_bool_eq_of_halfStar K P T hP htile E hvertices a d hd 0
      qPlus bPlus hqCompPlus (by simp [qPlus])
      (by simpa [J] using hzeroInterior) occupied hstar
  refine ⟨?_, ?_, ?_⟩
  · simpa [J] using hwindow
  · change qMinus ∈ signedCarrierIntervals K T E a d occupied ∧ _
    exact ⟨by simpa [hbMinus] using hqMinus, by simpa [J] using hminusSubset⟩
  · change qPlus ∈ signedCarrierIntervals K T E a d occupied ∧ _
    exact ⟨by simpa [hbPlus] using hqPlus, by simpa [J] using hplusSubset⟩


private theorem integerTangentWindow_uniformOmittedStar_labelledCollar
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (Z : Tiling.RationalPolygonal.IntegerPlane)
    (hd : Tiling.RationalPolygonal.integerPoint Z ≠ 0) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ p t : Plane, t ∈ T → p ∈ t +ᵥ Tiling.vertexSet K.support →
      ∀ occupied : Bool, originalVertexConeUnion K P T p =
        (if occupied then Tiling.positiveHalfPlane 0 (Tiling.RationalPolygonal.integerPoint Z)
          else Tiling.negativeHalfPlane 0 (Tiling.RationalPolygonal.integerPoint Z)) →
      ∀ sPlus ∈ T, ∀ ePlus ∈ E, ∀ cPlus : ℝ, 0 < cPlus →
      ((sPlus + ePlus.1 = p ∧ sPlus + ePlus.2 = p + cPlus • Tiling.RationalPolygonal.integerPoint Z) ∨
        (sPlus + ePlus.2 = p ∧ sPlus + ePlus.1 = p + cPlus • Tiling.RationalPolygonal.integerPoint Z)) →
      ∀ sMinus ∈ T, ∀ eMinus ∈ E, ∀ cMinus : ℝ, 0 < cMinus →
      ((sMinus + eMinus.1 = p ∧ sMinus + eMinus.2 = p + cMinus • (-Tiling.RationalPolygonal.integerPoint Z)) ∨
        (sMinus + eMinus.2 = p ∧ sMinus + eMinus.1 = p + cMinus • (-Tiling.RationalPolygonal.integerPoint Z))) →
      ∀ y ∈ deformPoint φ t +ᵥ Kφ.support, dist y (deformPoint φ p) < R →
      ∀ η : ℝ, 0 < η → η < R → ∀ x : Plane, dist x y < η →
      0 < Metric.infDist x (deformPoint φ t +ᵥ Kφ.support) →
      x - deformPoint φ p ∉ originalVertexConeUnion K P T p →
      ∃ s ∈ T, s ≠ t ∧ x ∈ deformPoint φ s +ᵥ Kφ.support ∧
        Metric.infDist x (deformPoint φ s +ᵥ frontier Kφ.support) < η := by
  let d := Tiling.RationalPolygonal.integerPoint Z
  obtain ⟨Rs, hRs, haugmented⟩ :=
    signedCarrierComponent_uniformAugmentedCollar K P T hP htile E hE hrat hcover
  obtain ⟨Fl, εl, l₀, L₀, hεl, hl₀, _, hlength⟩ :=
    finiteRationalEdges_uniformLengthRange E hrat
  let M := min (Rs / 4) (l₀ / 4)
  have hM : 0 < M := lt_min (by positivity) (by positivity)
  obtain ⟨Fa, εa, ρa, hεa, hρa, hcollar⟩ :=
    haugmented M hM (min_le_left _ _) Z hd
  obtain ⟨Fg, εg, rg, hεg, hrg, hgerm⟩ := originalVertexConeUnion_deformedGerm K P T
  obtain ⟨Fw, εw, hεw, hwindow⟩ :=
    signedCarrierComponent_window_uniformMembershipMargin K T htile E hE hcover Z hd
  obtain ⟨Fq, εq, hεq, hchain⟩ :=
    packingSol_uniformActualSourceCarrierTransport K T htile E hE hcover d hd
  let F := Fl ∪ Fg ∪ Fa ∪ Fw ∪ Fq
  let ε := min εl (min εg (min εa (min εw εq)))
  let R := min (rg / 4) (min (l₀ / 16) (ρa / 4))
  have hε : 0 < ε := lt_min hεl (lt_min hεg (lt_min hεa (lt_min hεw hεq)))
  have hR : 0 < R := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨F, ε, R, hε, hR, ?_⟩
  intro φ hφ Kφ hKφ p t ht hpt occupied hQ
    sPlus hsPlus ePlus hePlus cPlus hcPlus hplus sMinus hsMinus eMinus heMinus cMinus hcMinus hminus
    y hy hyp η hη hηR x hxy hpos hxQ
  change (sPlus + ePlus.1 = p ∧ sPlus + ePlus.2 = p + cPlus • d) ∨
    (sPlus + ePlus.2 = p ∧ sPlus + ePlus.1 = p + cPlus • d) at hplus
  change (sMinus + eMinus.1 = p ∧ sMinus + eMinus.2 = p + cMinus • (-d)) ∨
    (sMinus + eMinus.2 = p ∧ sMinus + eMinus.1 = p + cMinus • (-d)) at hminus
  have hφl : IsFiniteApproximation Fl εl φ := by
    apply finiteApproximation_strengthen Fl F εl ε φ _ (min_le_left _ _) hφ
    intro z hz
    simp [F, hz]
  have hφg : IsFiniteApproximation Fg εg φ := by
    apply finiteApproximation_strengthen Fg F εg ε φ _
      ((min_le_right _ _).trans (min_le_left _ _)) hφ
    intro z hz
    simp [F, hz]
  have hφa : IsFiniteApproximation Fa εa φ := by
    apply finiteApproximation_strengthen Fa F εa ε φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) hφ
    intro z hz
    simp [F, hz]
  have hφw : IsFiniteApproximation Fw εw φ := by
    apply finiteApproximation_strengthen Fw F εw ε φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))) hφ
    intro z hz
    simp [F, hz]
  have hφq : IsFiniteApproximation Fq εq φ := by
    apply finiteApproximation_strengthen Fq F εq ε φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))) hφ
    intro z hz
    simp [F, hz]
  have hminus' :
      (sMinus + eMinus.1 = p + (-cMinus) • d ∧ sMinus + eMinus.2 = p) ∨
      (sMinus + eMinus.2 = p + (-cMinus) • d ∧ sMinus + eMinus.1 = p) := by
    have heq : p + cMinus • (-d) = p + (-cMinus) • d := by simp
    rcases hminus with ⟨hb, hh⟩ | ⟨hb, hh⟩
    · exact Or.inr ⟨by simpa only [heq] using hh, hb⟩
    · exact Or.inl ⟨by simpa only [heq] using hh, hb⟩
  have hsource := twoTangentOccurrences_occupiedSourceWindow K P T hP htile E hE
    p d hd occupied hQ sMinus hsMinus eMinus heMinus cMinus hcMinus hminus' sPlus hsPlus ePlus hePlus cPlus hcPlus hplus
  let J := connectedComponentIn {s : ℝ | p + s • d ∈
    ⋃ t : T, (t : Plane) +ᵥ frontier K.support} 0
  let A := signedCarrierComponentIntervals K T E p d 0 occupied
  obtain ⟨hinterval, hminusA, hplusA⟩ := hsource
  have hr : p + (0 : ℝ) • d ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support := by
    have hp : ePlus.1 ∈ frontier K.support := (hE ePlus hePlus).2.2.2.1 (left_mem_segment ℝ _ _)
    have hpp : p ∈ sPlus +ᵥ frontier K.support := by
      rcases hplus with ⟨hl, _⟩ | ⟨hl, _⟩
      · rw [← hl]
        exact Set.vadd_mem_vadd_set hp
      · rw [← hl]
        exact Set.vadd_mem_vadd_set ((hE ePlus hePlus).2.2.2.1 (right_mem_segment ℝ _ _))
    have hmem : p ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support :=
      Set.mem_iUnion.mpr ⟨⟨sPlus, hsPlus⟩, hpp⟩
    simpa only [zero_smul, add_zero] using hmem
  have hlu : -cMinus < cPlus := by linarith
  have hbound := (hchain φ hφq p 0 (-cMinus) cPlus hr hlu hinterval occupied).2.1
  have hzeroS : (0 : ℝ) ∈ scalarIntervalEndpoints A := ⟨(0, cPlus), hplusA, Or.inl rfl⟩
  have hminusS : -cMinus ∈ scalarIntervalEndpoints A := ⟨(-cMinus, 0), hminusA, Or.inl rfl⟩
  have hplusS : cPlus ∈ scalarIntervalEndpoints A := ⟨(0, cPlus), hplusA, Or.inr rfl⟩
  have hφminus : (φ (-cMinus) : ℝ) < 0 := by
    have h := (hbound (-cMinus) hminusS 0 hzeroS (by linarith)).1
    simp only [map_zero, Rat.cast_zero] at h
    linarith
  have hφplus : 0 < (φ cPlus : ℝ) := by
    have h := (hbound 0 hzeroS cPlus hplusS hcPlus).1
    simp only [map_zero, Rat.cast_zero] at h
    linarith
  have occurrenceLength (s : Plane) (e : Plane × Plane) (he : e ∈ E)
      (b : Plane)
      (hcoords : (s + e.1 = p ∧ s + e.2 = b) ∨ (s + e.2 = p ∧ s + e.1 = b)) :
      l₀ ≤ dist (deformPoint φ p) (deformPoint φ b) := by
    have hmap (z : Plane) : deformPoint φ (s + z) = deformPoint φ s + deformPoint φ z :=
      (deformPointLinear φ).map_add s z
    rcases hcoords with ⟨hl, hh⟩ | ⟨hl, hh⟩
    · rw [← hl, ← hh, hmap, hmap, dist_add_left]
      exact (hlength φ hφl e he).1
    · rw [← hl, ← hh, hmap, hmap, dist_add_left, dist_comm]
      exact (hlength φ hφl e he).1
  have hleftLength : l₀ ≤ dist (deformPoint φ p)
      (deformPoint φ p + (φ (-cMinus) : ℝ) • d) := by
    have h := occurrenceLength sMinus eMinus heMinus (p + cMinus • (-d)) hminus
    have heq : p + cMinus • (-d) = p + (-cMinus) • d := by simp
    rw [heq, deformPoint_integerCarrierParameter φ p (-cMinus) Z] at h
    exact h
  have hrightLength : l₀ ≤ dist (deformPoint φ p)
      (deformPoint φ p + (φ cPlus : ℝ) • d) := by
    have h := occurrenceLength sPlus ePlus hePlus (p + cPlus • d) hplus
    rw [deformPoint_integerCarrierParameter φ p cPlus Z] at h
    exact h
  have htranslation (z : Plane) :
      (z - deformPoint φ p ∈ (if occupied then Tiling.positiveHalfPlane 0 d
        else Tiling.negativeHalfPlane 0 d)) ↔
      z ∈ (if occupied then Tiling.positiveHalfPlane (deformPoint φ p) d
        else Tiling.negativeHalfPlane (deformPoint φ p) d) := by
    have hcross : Tiling.signedSide 0 d (z - deformPoint φ p) =
        Tiling.signedSide (deformPoint φ p) d z := by
      simp [Tiling.signedSide, Tiling.planarCross]
      ring
    cases occupied <;> simp only [Bool.false_eq_true, ↓reduceIte,
      Tiling.mem_positiveHalfPlane, Tiling.mem_negativeHalfPlane, hcross]
  have hyQ : y - deformPoint φ p ∈ originalVertexConeUnion K P T p := by
    have hz : dist (y - deformPoint φ p) 0 < rg := by
      have heq : dist (y - deformPoint φ p) 0 = dist y (deformPoint φ p) := by simp [dist_eq_norm]
      rw [heq]
      exact hyp.trans_le ((min_le_left _ _).trans (by linarith : rg / 4 ≤ rg))
    have hmem : deformPoint φ p + (y - deformPoint φ p) ∈
        ⋃ s : {s : T // p ∈ (s : Plane) +ᵥ Tiling.vertexSet K.support},
          deformPoint φ (s.1 : Plane) +ᵥ Kφ.support := by
      simp only [add_sub_cancel]
      exact Set.mem_iUnion.mpr ⟨⟨⟨t, ht⟩, hpt⟩, hy⟩
    exact (hgerm φ hφg Kφ hKφ p (y - deformPoint φ p) hz).mp hmem
  have hySide : y ∈ (if occupied then Tiling.positiveHalfPlane (deformPoint φ p) d
      else Tiling.negativeHalfPlane (deformPoint φ p) d) :=
    (htranslation y).mp (hQ ▸ hyQ)
  have hxOutside : x ∉ (if occupied then Tiling.positiveHalfPlane (deformPoint φ p) d
      else Tiling.negativeHalfPlane (deformPoint φ p) d) := by
    intro hx
    exact hxQ (hQ.symm ▸ (htranslation x).mpr hx)
  obtain ⟨q, hqLine, hqp, hqdist, hqSide⟩ :=
    halfspace_projection_candidate (deformPoint φ p) x d hd occupied hxOutside
  have hxp : dist x (deformPoint φ p) < l₀ / 4 := by
    have htriangle := dist_triangle x y (deformPoint φ p)
    have hRl : R ≤ l₀ / 16 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  obtain ⟨v, hqEq, hv, hleftMargin, hrightMargin⟩ :=
    projectionWindow_deepInterior (deformPoint φ p) q d hd
      (φ (-cMinus) : ℝ) (φ cPlus : ℝ) l₀ hφminus hφplus hl₀ hleftLength hrightLength hqLine
      (hqp.trans_lt hxp)
  have hleftM : M ≤ dist (deformPoint φ p + v • d)
      (deformPoint φ (p + (-cMinus) • d)) := by
    rw [deformPoint_integerCarrierParameter φ p (-cMinus) Z, ← hqEq]
    exact (min_le_right _ _).trans ((by linarith : l₀ / 4 ≤ 3 * l₀ / 4).trans hleftMargin)
  have hrightM : M ≤ dist (deformPoint φ p + v • d)
      (deformPoint φ (p + cPlus • d)) := by
    rw [deformPoint_integerCarrierParameter φ p cPlus Z, ← hqEq]
    exact (min_le_right _ _).trans ((by linarith : l₀ / 4 ≤ 3 * l₀ / 4).trans hrightMargin)
  obtain ⟨hmember, hmargin⟩ := hwindow φ hφw p 0 (-cMinus) cPlus hr hlu hinterval occupied
    (-cMinus) cPlus hminusS hplusS hinterval v M hv hleftM hrightM
  have hxq : dist x q < η := (hqdist y hySide).trans_lt hxy
  have hxρ : dist x q < ρa := by
    have hRρ : R ≤ ρa / 4 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hqSide' : x ∈ (if !occupied then Tiling.positiveHalfPlane q d
      else Tiling.negativeHalfPlane q d) := by
    cases occupied <;> simpa using hqSide
  exact hcollar φ hφa Kφ hKφ p 0 (-cMinus) cPlus hr hlu hinterval (!occupied) v
    (hmember (!occupied)) hmargin x
    (by change dist x (deformPoint φ p + v • d) < ρa; rw [← hqEq]; exact hxρ)
    (by
      change x ∈ (if !occupied then Tiling.positiveHalfPlane
        (deformPoint φ p + v • d) d else Tiling.negativeHalfPlane
        (deformPoint φ p + v • d) d)
      rw [← hqEq]
      exact hqSide')
    t η hpos (by change dist x (deformPoint φ p + v • d) < η; rw [← hqEq]; exact hxq)


private theorem rationalPrimitiveVertices_uniformFullStar_labelledCollar
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε R : ℝ, 0 < ε ∧ 0 < R ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ t ∈ T, ∀ e ∈ E, ∀ p : Plane, p = t + e.1 ∨ p = t + e.2 →
      ∀ y ∈ deformPoint φ t +ᵥ segment ℝ (deformPoint φ e.1) (deformPoint φ e.2),
      dist y (deformPoint φ p) < R →
      ∀ η : ℝ, 0 < η → η < R → ∀ x : Plane, dist x y < η →
      0 < Metric.infDist x (deformPoint φ t +ᵥ Kφ.support) →
      ∃ s ∈ T, s ≠ t ∧ x ∈ deformPoint φ s +ᵥ Kφ.support ∧
        Metric.infDist x (deformPoint φ s +ᵥ frontier Kφ.support) < η := by
  classical
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨Z, C, D, εD, hrep, _, _, _, _⟩ := finite_rational_edge_integer_alphabet E hrat
  obtain ⟨Fc, εc, hεc, hchoice⟩ :=
    originalHalfVertexStar_uniformIntegerTangentChoice K P T hP htile E hprimitive hcover Z C hrep
  obtain ⟨Fs, εs, Rs, hεs, hRs, hoccupied⟩ :=
    rationalPrimitiveVertices_uniformOccupiedStar_labelledCollar K P T hP htile.2.1 E hrat
      (fun e he => (hE e he).2.2.2.1)
  let I := {e // e ∈ E}
  let Q (i : I) (φ : ℝ →ₗ[ℚ] ℚ) (R : ℝ) : Prop :=
    ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
    ∀ p t : Plane, t ∈ T → p ∈ t +ᵥ Tiling.vertexSet K.support →
    ∀ occupied : Bool, originalVertexConeUnion K P T p =
      (if occupied then Tiling.positiveHalfPlane 0 (Tiling.RationalPolygonal.integerPoint (Z i))
        else Tiling.negativeHalfPlane 0 (Tiling.RationalPolygonal.integerPoint (Z i))) →
    ∀ sPlus ∈ T, ∀ ePlus ∈ E, ∀ cPlus : ℝ, 0 < cPlus →
    ((sPlus + ePlus.1 = p ∧ sPlus + ePlus.2 = p + cPlus • Tiling.RationalPolygonal.integerPoint (Z i)) ∨
      (sPlus + ePlus.2 = p ∧ sPlus + ePlus.1 = p + cPlus • Tiling.RationalPolygonal.integerPoint (Z i))) →
    ∀ sMinus ∈ T, ∀ eMinus ∈ E, ∀ cMinus : ℝ, 0 < cMinus →
    ((sMinus + eMinus.1 = p ∧ sMinus + eMinus.2 = p + cMinus • (-Tiling.RationalPolygonal.integerPoint (Z i))) ∨
      (sMinus + eMinus.2 = p ∧ sMinus + eMinus.1 = p + cMinus • (-Tiling.RationalPolygonal.integerPoint (Z i)))) →
    ∀ y ∈ deformPoint φ t +ᵥ Kφ.support, dist y (deformPoint φ p) < R →
    ∀ η : ℝ, 0 < η → η < R → ∀ x : Plane, dist x y < η →
    0 < Metric.infDist x (deformPoint φ t +ᵥ Kφ.support) →
    x - deformPoint φ p ∉ originalVertexConeUnion K P T p →
    ∃ s ∈ T, s ≠ t ∧ x ∈ deformPoint φ s +ᵥ Kφ.support ∧
      Metric.infDist x (deformPoint φ s +ᵥ frontier Kφ.support) < η
  have hlocal : ∀ i ∈ (Finset.univ : Finset I), ∃ F : Finset ℝ, ∃ ε R : ℝ,
      0 < ε ∧ 0 < R ∧ ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ → Q i φ R := by
    intro i _
    exact integerTangentWindow_uniformOmittedStar_labelledCollar K P T hP htile E hE
      hrat hcover (Z i) (hrep i).2.1
  have hmono : ∀ i ∈ (Finset.univ : Finset I), ∀ φ r R, r ≤ R → Q i φ R → Q i φ r := by
    intro i _ φ r R hr hQ Kφ hKφ p t ht hpt occupied hstar
      sPlus hsPlus ePlus hePlus cPlus hcPlus hplus sMinus hsMinus eMinus heMinus cMinus hcMinus hminus
      y hy hyp η hη hηr x hxy hpos hxQ
    exact hQ Kφ hKφ p t ht hpt occupied hstar
      sPlus hsPlus ePlus hePlus cPlus hcPlus hplus sMinus hsMinus eMinus heMinus cMinus hcMinus hminus
      y hy (hyp.trans_le hr) η hη (hηr.trans_le hr) x hxy hpos hxQ
  obtain ⟨Fo, εo, Ro, hεo, hRo, homitted⟩ :=
    finiteApproximation_uniformPositiveRadius Finset.univ Q hmono hlocal
  obtain ⟨Ft, εt, hεt, htransport⟩ := rationalPrimitiveFrontier_transport K P hP E
    (fun e he => ⟨(hE e he).1, hrat e he⟩) hcover
  let F := Fc ∪ Fs ∪ Fo ∪ Ft
  let ε := min εc (min εs (min εo εt))
  refine ⟨F, ε, min Rs Ro, lt_min hεc (lt_min hεs (lt_min hεo hεt)), lt_min hRs hRo, ?_⟩
  intro φ hφ Kφ hKφ t ht e he p hp y hy hyp η hη hηR x hxy hpos
  have hφc : IsFiniteApproximation Fc εc φ := by
    apply finiteApproximation_strengthen Fc F εc ε φ _ (min_le_left _ _) hφ
    intro z hz
    simp [F, hz]
  have hφs : IsFiniteApproximation Fs εs φ := by
    apply finiteApproximation_strengthen Fs F εs ε φ _
      ((min_le_right _ _).trans (min_le_left _ _)) hφ
    intro z hz
    simp [F, hz]
  have hφo : IsFiniteApproximation Fo εo φ := by
    apply finiteApproximation_strengthen Fo F εo ε φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) hφ
    intro z hz
    simp [F, hz]
  have hφt : IsFiniteApproximation Ft εt φ := by
    apply finiteApproximation_strengthen Ft F εt ε φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) hφ
    intro z hz
    simp [F, hz]
  by_cases hxQ : x - deformPoint φ p ∈ originalVertexConeUnion K P T p
  · exact hoccupied φ hφs Kφ hKφ t ht e he p hp y hy
      (hyp.trans_le (min_le_left _ _)) η hη (hηR.trans_le (min_le_left _ _)) x hxy hpos hxQ
  have hpt : p ∈ t +ᵥ Tiling.vertexSet K.support := by
    rcases hp with rfl | rfl
    · exact Set.vadd_mem_vadd_set (hE e he).2.1
    · exact Set.vadd_mem_vadd_set (hE e he).2.2.1
  rcases hchoice φ hφc Kφ hKφ p t ht hpt with hfull | ⟨i, occupied, hstar, hoccurrences⟩
  · exact False.elim (hxQ (hfull.symm ▸ Set.mem_univ _))
  obtain ⟨sPlus, hsPlus, _, ePlus, hePlus, cPlus, hcPlus, hplus⟩ := hoccurrences true
  obtain ⟨sMinus, hsMinus, _, eMinus, heMinus, cMinus, hcMinus, hminus⟩ := hoccurrences false
  obtain ⟨H, hanchors, hsupport, hsegments, hfront⟩ := htransport φ hφt Kφ hKφ
  have hycopy : y ∈ deformPoint φ t +ᵥ Kφ.support := by
    apply Set.vadd_set_mono (show segment ℝ (deformPoint φ e.1) (deformPoint φ e.2) ⊆
      Kφ.support from ?_) hy
    intro z hz
    have hzfront : z ∈ frontier Kφ.support := by
      rw [hfront]
      exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩
    simpa only [Kφ.isPolygonal.isClosed.closure_eq] using frontier_subset_closure hzfront
  exact homitted φ hφo i (Finset.mem_univ _) Kφ hKφ p t ht hpt occupied hstar
    sPlus hsPlus ePlus hePlus cPlus hcPlus (by simpa only [↓reduceIte] using hplus)
    sMinus hsMinus eMinus heMinus cMinus hcMinus (by simpa only [Bool.false_eq_true, ↓reduceIte] using hminus)
    y hycopy (hyp.trans_le (min_le_right _ _)) η hη (hηR.trans_le (min_le_right _ _))
    x hxy hpos hxQ


private theorem positiveInfDist_exists_nearestFullFrontier
    (K : PolygonalRegion) (t x : Plane)
    (hpos : 0 < Metric.infDist x (t +ᵥ K.support)) :
    ∃ y ∈ t +ᵥ frontier K.support,
      dist x y = Metric.infDist x (t +ᵥ K.support) := by
  have hx : x ∈ (t +ᵥ K.support)ᶜ := by
    intro hx
    have hdist := Metric.infDist_le_dist_of_mem (x := x) hx
    simp only [dist_self] at hdist
    linarith
  have hcompl : (t +ᵥ K.support)ᶜ ≠ Set.univ := by
    intro hfull
    obtain ⟨z, hz⟩ := K.nonempty
    have hzcopy : t + z ∈ t +ᵥ K.support := Set.vadd_mem_vadd_set hz
    have hzcompl : t + z ∈ (t +ᵥ K.support)ᶜ := hfull.symm ▸ Set.mem_univ _
    exact hzcompl hzcopy
  obtain ⟨y, hy, hdist⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hcompl
  have hfront : frontier (t +ᵥ K.support) = t +ᵥ frontier K.support := by
    rw [frontier, closure_vadd, interior_vadd, ← Set.vadd_set_sdiff]
    rfl
  rw [frontier_compl, hfront] at hy
  exact ⟨y, hy, by simpa only [compl_compl] using hdist.symm⟩

private theorem normalProjection_translateIntervals :
    ∀ (n : RationalNormal) (E : Set Plane) (I : Finset (ℝ × ℝ))
      (f : ℝ → ℝ),
      normalEval n '' E = ⋃ e ∈ I, Set.Ioo (f e.1) (f e.2) →
      ∀ s : Plane,
        normalEval n '' (s +ᵥ E) =
          ⋃ e ∈ I, Set.Ioo (normalEval n s + f e.1) (normalEval n s + f e.2) := by
  intro n E I f h s
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hyE : (-s +ᵥ x) ∈ E := (Set.mem_vadd_set_iff_neg_vadd_mem.mp hx)
    have hxEval : normalEval n x = normalEval n s + normalEval n (-s +ᵥ x) := by
      simpa using normalEval_add n s (-s +ᵥ x)
    rw [hxEval]
    have hproj : normalEval n (-s +ᵥ x) ∈ ⋃ e ∈ I, Set.Ioo (f e.1) (f e.2) := by
      rw [← h]
      exact Set.mem_image_of_mem _ hyE
    rcases Set.mem_iUnion.mp hproj with ⟨e, he⟩
    rcases Set.mem_iUnion.mp he with ⟨heI, hrange⟩
    refine Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨heI, ?_⟩⟩
    change f e.1 < normalEval n (-s +ᵥ x) ∧ normalEval n (-s +ᵥ x) < f e.2 at hrange
    change normalEval n s + f e.1 < normalEval n s + normalEval n (-s +ᵥ x) ∧
      normalEval n s + normalEval n (-s +ᵥ x) < normalEval n s + f e.2
    exact ⟨by linarith [hrange.1], by linarith [hrange.2]⟩
  · intro hr
    rcases Set.mem_iUnion.mp hr with ⟨e, he⟩
    rcases Set.mem_iUnion.mp he with ⟨heI, hrange⟩
    change normalEval n s + f e.1 < r ∧ r < normalEval n s + f e.2 at hrange
    have hshift : f e.1 < r - normalEval n s ∧ r - normalEval n s < f e.2 := by
      constructor <;> linarith [hrange.1, hrange.2]
    have hproj : r - normalEval n s ∈ ⋃ e ∈ I, Set.Ioo (f e.1) (f e.2) :=
      Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨heI, hshift⟩⟩
    rw [← h] at hproj
    rcases hproj with ⟨y, hy, hyeq⟩
    refine ⟨s +ᵥ y, ?_, ?_⟩
    · exact Set.mem_vadd_set_iff_neg_vadd_mem.mpr (by simpa using hy)
    · rw [show s +ᵥ y = s + y by rfl, normalEval_add]
      rw [hyeq]
      ring

private theorem interval_overlap_iff (a b c d : ℝ) :
    (Set.Ioo a b ∩ Set.Ioo c d).Nonempty ↔ (a < b ∧ a < d) ∧ (c < b ∧ c < d) := by
  rw [Set.Ioo_inter_Ioo, Set.nonempty_Ioo]
  simp only [sup_lt_iff, lt_inf_iff]
  tauto

theorem transverseFLC_directionalOverlapReflection :
  ∀ (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane) (n : RationalNormal),
    polyhedralSupport P = K.support → Tiling.RationalSlopes.HasRationalSlopes K →
    Tiling.Polygonal.TilesOn K T Set.univ →
    Tiling.RationalSlopes.HasTransverseFLC K (normalDirection n) T →
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
            ∀ s ∈ T, ∀ t ∈ T,
              Tiling.RationalSlopes.DirectionalOverlap K (normalDirection n) s t ↔
                Tiling.RationalSlopes.DirectionalOverlap Kφ (normalDirection n)
                  (deformPoint φ s) (deformPoint φ t) := by
  intro K P T n hP hrat htile hflc
  obtain ⟨I, hI, hends, F₀, ε₀, hε₀, hdeform⟩ := openNormalProjection_deformation K P n hP
  obtain ⟨F₁, ε₁, hε₁, hcontrol⟩ :=
    transverseFLC_globalOrderAndBoundedGapReflection K T n hrat htile hflc 1 (by norm_num)
  refine ⟨F₀ ∪ F₁, min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro φ hφ Kφ hKφ s hs t ht
  have hφ₀ := finiteApproximation_strengthen F₀ (F₀ ∪ F₁) ε₀ (min ε₀ ε₁) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφ₁ := finiteApproximation_strengthen F₁ (F₀ ∪ F₁) ε₁ (min ε₀ ε₁) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  have horder := (hcontrol φ hφ₁).1
  have hcompare (s : Plane) (hs : s ∈ T) (t : Plane) (ht : t ∈ T)
      (u : Plane) (hu : u ∈ Tiling.vertexSet K.support)
      (v : Plane) (hv : v ∈ Tiling.vertexSet K.support) :
      normalEval n s + normalEval n u < normalEval n t + normalEval n v ↔
        normalEval n (deformPoint φ s) + (φ (normalEval n u) : ℝ) <
          normalEval n (deformPoint φ t) + (φ (normalEval n v) : ℝ) := by
    have h := horder (u + s) (Set.add_mem_add hu hs) (v + t) (Set.add_mem_add hv ht)
    simpa only [normalEval_add, rationalNormal_commutes, map_add, Rat.cast_add, add_comm] using h
  rw [directionalOverlap_iff_openNormalProjections, directionalOverlap_iff_openNormalProjections,
    normalProjection_translateIntervals n K.openCarrier I id hI s,
    normalProjection_translateIntervals n K.openCarrier I id hI t,
    normalProjection_translateIntervals n Kφ.openCarrier I (fun r => (φ r : ℝ))
      (hdeform φ hφ₀ Kφ hKφ) (deformPoint φ s),
    normalProjection_translateIntervals n Kφ.openCarrier I (fun r => (φ r : ℝ))
      (hdeform φ hφ₀ Kφ hKφ) (deformPoint φ t)]
  simp only [id_eq]
  simp_rw [Set.iUnion_inter, Set.inter_iUnion, Set.nonempty_iUnion]
  apply exists_congr
  intro e
  apply exists_congr
  intro he
  apply exists_congr
  intro f
  apply exists_congr
  intro hf
  obtain ⟨_, ⟨u, hu, hulo⟩, ⟨v, hv, hvhi⟩⟩ := hends e he
  obtain ⟨_, ⟨w, hw, hwlo⟩, ⟨z, hz, hzhi⟩⟩ := hends f hf
  rw [interval_overlap_iff, interval_overlap_iff]
  apply and_congr
  · apply and_congr
    · simpa only [hulo, hvhi] using hcompare s hs s hs u hu v hv
    · simpa only [hulo, hzhi] using hcompare s hs t ht u hu z hz
  · apply and_congr
    · simpa only [hwlo, hvhi] using hcompare t ht s hs w hw v hv
    · simpa only [hwlo, hzhi] using hcompare t ht t ht w hw z hz

private theorem sourceInvariantBoundary_isProperLink (K : PolygonalRegion)
    (T S : Set Plane) (δ : Submodule ℝ Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) (hST : S ⊆ T)
    (hinv : Tiling.Polygonal.IsInvariantAlong (Tiling.Polygonal.regularSupport K S) δ)
    {a : Plane} (ha : a ∈ frontier (Tiling.Polygonal.regularSupport K S)) :
    Tiling.RationalSlopes.IsProperLink K δ T a := by
  let E := Tiling.Polygonal.regularSupport K S
  let U := Tiling.Polygonal.openUnion K S
  have hpS : Tiling.IsPacking K.prototileFamily (K.placements S) := by
    apply (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K S).mpr
    intro s hs t ht hst
    exact (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K T).mp hpack (hST hs) (hST ht) hst
  have hUopen : IsOpen U := isOpen_iUnion (fun s => isOpen_interior.vadd (s : Plane))
  have hUE : U ⊆ E := interior_maximal subset_closure hUopen
  have hEopen : IsOpen E := isOpen_interior
  have hclosure : closure E = closure U := by
    apply Set.Subset.antisymm
    · exact closure_minimal interior_subset isClosed_closure
    · exact closure_mono hUE
  have hboundary {q : Plane} (hq : q ∈ frontier E) :
      ∃ s ∈ S, q ∈ s +ᵥ frontier K.support := by
    have hqclosure : q ∈ closure U := hclosure ▸ frontier_subset_closure hq
    rw [Tiling.Polygonal.closure_openUnion_eq_iUnion_support hpS] at hqclosure
    obtain ⟨s, hqs⟩ := Set.mem_iUnion.mp hqclosure
    have hqnot : q ∉ E := by
      intro hqE
      have hqi : q ∈ interior E := by simpa only [hEopen.interior_eq] using hqE
      exact Set.disjoint_left.mp disjoint_interior_frontier hqi hq
    have hqnotTile : q ∉ (s : Plane) +ᵥ K.openCarrier := by
      intro hqt
      exact hqnot (hUE (Set.mem_iUnion.mpr ⟨s, hqt⟩))
    refine ⟨s, s.2, Set.mem_vadd_set_iff_neg_vadd_mem.mpr ?_⟩
    rw [K.isPolygonal.isClosed.frontier_eq]
    exact ⟨Set.mem_vadd_set_iff_neg_vadd_mem.mp hqs,
      fun hqi => hqnotTile (Set.mem_vadd_set_iff_neg_vadd_mem.mpr hqi)⟩
  intro q hq
  have hu : (-a +ᵥ q) ∈ δ := Set.mem_vadd_set_iff_neg_vadd_mem.mp hq
  let u : Plane := -a +ᵥ q
  have hqa : u +ᵥ a = q := by dsimp [u]; change -a + q + a = q; abel
  have hclinv : u +ᵥ closure E = closure E := by
    rw [← closure_vadd, hinv u hu]
  have hqcl : q ∈ closure E := by
    rw [← hclinv, ← hqa]
    exact Set.vadd_mem_vadd_set (frontier_subset_closure ha)
  have hqnot : q ∉ E := by
    intro hqE
    have haE : a ∈ E := by
      have hneg : -u +ᵥ E = E := hinv (-u) (δ.neg_mem hu)
      have h : -u +ᵥ q ∈ -u +ᵥ E := Set.vadd_mem_vadd_set hqE
      rw [hneg, ← hqa] at h
      simpa using h
    have hai : a ∈ interior E := by simpa only [hEopen.interior_eq] using haE
    exact Set.disjoint_left.mp disjoint_interior_frontier hai ha
  have hqfront : q ∈ frontier E := ⟨hqcl, by simpa only [hEopen.interior_eq] using hqnot⟩
  obtain ⟨s, hs, hqs⟩ := hboundary hqfront
  exact Set.mem_iUnion.mpr ⟨⟨s, hST hs⟩, hqs⟩

private theorem source_otherOpenCarrier_disjoint_regularSupportClosure
    (K : PolygonalRegion) (T S : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) (hST : S ⊆ T)
    (t : Plane) (ht : t ∈ T) (htnot : t ∉ S) :
    Disjoint (t +ᵥ K.openCarrier) (closure (Tiling.Polygonal.regularSupport K S)) := by
  have hdisj : Disjoint (t +ᵥ K.openCarrier) (Tiling.Polygonal.openUnion K S) := by
    rw [Set.disjoint_left]
    intro x hxt hxS
    obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hxS
    have hts : t ≠ (s : Plane) := by
      intro heq
      apply htnot
      rw [heq]
      exact s.2
    exact Set.disjoint_left.mp
      ((Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K T).mp hpack
        ht (hST s.2) hts) hxt hxs
  apply (hdisj.closure_right (isOpen_interior.vadd t)).mono_right
  exact closure_minimal interior_subset isClosed_closure

private theorem normalCLM_surjective (n : RationalNormal) :
    Function.Surjective (normalCLM n) := by
  rcases n.nonzero with hx | hy
  · have hx' : (n.x : ℝ) ≠ 0 := by exact_mod_cast hx
    intro r
    refine ⟨(r / (n.x : ℝ)) • (1 : Plane), ?_⟩
    rw [map_smul]
    have hval : normalCLM n (1 : Plane) = (n.x : ℝ) := by simp [normalCLM]
    rw [hval, smul_eq_mul, div_mul_cancel₀ _ hx']
  · have hy' : (n.y : ℝ) ≠ 0 := by exact_mod_cast hy
    intro r
    refine ⟨(r / (n.y : ℝ)) • Complex.I, ?_⟩
    rw [map_smul]
    have hval : normalCLM n Complex.I = (n.y : ℝ) := by simp [normalCLM]
    rw [hval, smul_eq_mul, div_mul_cancel₀ _ hy']

private theorem invariant_normal_preimage (n : RationalNormal) (E : Set Plane)
    (hinv : Tiling.Polygonal.IsInvariantAlong E (normalDirection n)) :
    E = normalEval n ⁻¹' (normalEval n '' E) := by
  ext x
  constructor
  · intro hx
    exact Set.mem_image_of_mem _ hx
  · rintro ⟨y, hy, hπyx⟩
    have hxy : x - y ∈ normalDirection n :=
      (normalDirection_mem_iff n (x - y)).mpr (by rw [normalEval_sub, hπyx, sub_self])
    have hx : (x - y) +ᵥ y ∈ (x - y) +ᵥ E := Set.vadd_mem_vadd_set hy
    rw [hinv (x - y) hxy] at hx
    simpa only [vadd_eq_add, sub_add_cancel] using hx

private theorem sourceSubfamily_projectionColours
    (K : PolygonalRegion) (n : RationalNormal) (T S : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T)) (hST : S ⊆ T)
    (hinv : Tiling.Polygonal.IsInvariantAlong (Tiling.Polygonal.regularSupport K S)
      (normalDirection n)) :
    let A := normalEval n '' Tiling.Polygonal.regularSupport K S
    IsOpen A ∧
      (∀ s ∈ S, normalEval n '' (s +ᵥ K.openCarrier) ⊆ A) ∧
      (∀ t ∈ T, t ∉ S →
        Disjoint (normalEval n '' (t +ᵥ K.openCarrier)) (closure A)) ∧
      (∀ r ∈ frontier A, ∃ a : Plane, normalEval n a = r ∧
        a ∈ frontier (Tiling.Polygonal.regularSupport K S)) := by
  let E := Tiling.Polygonal.regularSupport K S
  let A := normalEval n '' E
  have hfun : (normalCLM n : Plane → ℝ) = normalEval n := funext (normalCLM_apply n)
  have hpre : E = (normalCLM n) ⁻¹' A := by
    rw [hfun]
    exact invariant_normal_preimage n E hinv
  have hUopen : IsOpen (Tiling.Polygonal.openUnion K S) :=
    isOpen_iUnion (fun s => isOpen_interior.vadd (s : Plane))
  have hUE : Tiling.Polygonal.openUnion K S ⊆ E :=
    interior_maximal subset_closure hUopen
  refine ⟨?_, ?_, ?_, ?_⟩
  · change IsOpen (normalEval n '' E)
    rw [← hfun]
    exact (normalCLM n).isOpenMap (normalCLM_surjective n) E isOpen_interior
  · intro s hs
    rintro r ⟨x, hx, rfl⟩
    exact Set.mem_image_of_mem _ (hUE (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩))
  · intro t ht htnot
    rw [Set.disjoint_left]
    rintro r ⟨x, hx, hπxr⟩ hr
    have hxE : x ∈ closure E := by
      rw [hpre, (normalCLM n).closure_preimage (normalCLM_surjective n)]
      change normalCLM n x ∈ closure A
      rw [normalCLM_apply, hπxr]
      exact hr
    exact Set.disjoint_left.mp
      (source_otherOpenCarrier_disjoint_regularSupportClosure K T S hpack hST t ht htnot)
      hx hxE
  · intro r hr
    obtain ⟨a, ha⟩ := normalCLM_surjective n r
    refine ⟨a, by simpa only [normalCLM_apply] using ha, ?_⟩
    change a ∈ frontier E
    rw [hpre, (normalCLM n).frontier_preimage (normalCLM_surjective n)]
    change normalCLM n a ∈ frontier A
    rwa [ha]

/-- A monochromatic normal fibre set regularizes to the exact subfamily carrier.
    Whole-plane density, not an image-family local-finiteness assertion, supplies
    the reverse closure inclusion. -/
private theorem regularSupport_invariant_of_noCrossProjection
    (K : PolygonalRegion) (n : RationalNormal) (T S : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (hST : S ⊆ T)
    (hcross : ∀ s ∈ S, ∀ t ∈ T, t ∉ S →
      Disjoint (normalEval n '' (s +ᵥ K.openCarrier))
        (normalEval n '' (t +ᵥ K.openCarrier))) :
    Tiling.Polygonal.IsInvariantAlong (Tiling.Polygonal.regularSupport K S)
      (normalDirection n) := by
  let U := Tiling.Polygonal.openUnion K S
  let W := Tiling.Polygonal.openUnion K (T \ S)
  let A := normalEval n '' U
  let V := normalEval n ⁻¹' A
  have hUopen : IsOpen U := isOpen_iUnion (fun s => isOpen_interior.vadd (s : Plane))
  have hfun : (normalCLM n : Plane → ℝ) = normalEval n := funext (normalCLM_apply n)
  have hopenπ : IsOpenMap (normalEval n) := by
    rw [← hfun]
    exact (normalCLM n).isOpenMap (normalCLM_surjective n)
  have hcontπ : Continuous (normalEval n) := by
    rw [← hfun]
    exact (normalCLM n).continuous
  have hVopen : IsOpen V := (hopenπ U hUopen).preimage hcontπ
  have hUV : U ⊆ V := fun x hx => Set.mem_image_of_mem _ hx
  have hVW : Disjoint V W := by
    rw [Set.disjoint_left]
    rintro x ⟨y, hy, hπyx⟩ hx
    obtain ⟨s, hys⟩ := Set.mem_iUnion.mp hy
    obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hcross s s.2 t t.2.1 t.2.2)
      ⟨y, hys, hπyx⟩ ⟨x, hxt, rfl⟩
  have hdecomp : Tiling.Polygonal.openUnion K T = U ∪ W := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
      by_cases htS : (t : Plane) ∈ S
      · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨t, htS⟩, hxt⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨t, t.2, htS⟩, hxt⟩)
    · rintro (hx | hx)
      · obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨⟨s, hST s.2⟩, hxs⟩
      · obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨⟨t, t.2.1⟩, hxt⟩
  have hfull : closure (Tiling.Polygonal.openUnion K T) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← Tiling.Polygonal.regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile]
    exact interior_subset
  have hVcl : V ⊆ closure U := by
    intro x hxV
    have hx : x ∈ closure (Tiling.Polygonal.openUnion K T) := hfull ▸ Set.mem_univ _
    rw [hdecomp, closure_union] at hx
    rcases hx with hx | hx
    · exact hx
    · exact (Set.disjoint_left.mp (hVW.closure_right hVopen) hxV hx).elim
  have hclosure : closure U = closure V :=
    (closure_mono hUV).antisymm (closure_minimal hVcl isClosed_closure)
  have hVinvariant : Tiling.Polygonal.IsInvariantAlong V (normalDirection n) := by
    intro u hu
    have hπu := (normalDirection_mem_iff n u).mp hu
    ext x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change normalEval n (-u +ᵥ x) ∈ A ↔ normalEval n x ∈ A
    have heq : -u +ᵥ x = x - u := by change -u + x = x - u; abel
    rw [heq, normalEval_sub, hπu, sub_zero]
  intro u hu
  change u +ᵥ interior (closure U) = interior (closure U)
  rw [hclosure, ← interior_vadd, ← closure_vadd, hVinvariant u hu]

private theorem properLink_endpointSide_transport (K : PolygonalRegion)
    (T : Set Plane) (n : RationalNormal) (φ : ℝ →ₗ[ℚ] ℚ)
    (hcontrol : ∀ a : Plane, Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a →
      ∀ v ∈ Tiling.RationalSlopes.translatedVertices K T,
        Real.sign (normalEval n (deformPoint φ (v - a))) =
          Real.sign (normalEval n (v - a)))
    (a : Plane) (ha : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a)
    (t : Plane) (ht : t ∈ T) (v : Plane) (hv : v ∈ Tiling.vertexSet K.support) :
    (normalEval n t + normalEval n v ≤ normalEval n a ↔
      normalEval n (deformPoint φ t) + (φ (normalEval n v) : ℝ) ≤
        normalEval n (deformPoint φ a)) ∧
    (normalEval n a ≤ normalEval n t + normalEval n v ↔
      normalEval n (deformPoint φ a) ≤
        normalEval n (deformPoint φ t) + (φ (normalEval n v) : ℝ)) := by
  have hsign := hcontrol a ha (v + t) (Set.add_mem_add hv ht)
  have hleft := sign_eq_iff_nonpos hsign
  have hsignneg :
      Real.sign (-normalEval n (deformPoint φ (v + t - a))) =
        Real.sign (-normalEval n (v + t - a)) := by
    rw [Real.sign_neg, Real.sign_neg, hsign]
  have hright := sign_eq_iff_nonpos hsignneg
  have hsource : normalEval n (v + t - a) =
      normalEval n t + normalEval n v - normalEval n a := by
    rw [normalEval_sub, normalEval_add]
    ring
  have htarget : normalEval n (deformPoint φ (v + t - a)) =
      normalEval n (deformPoint φ t) + (φ (normalEval n v) : ℝ) -
        normalEval n (deformPoint φ a) := by
    simp only [rationalNormal_commutes, normalEval_sub, normalEval_add,
      map_sub, map_add, Rat.cast_sub, Rat.cast_add]
    ring
  rw [hsource, htarget] at hleft hright
  constructor
  · simpa only [sub_nonpos] using hleft.symm
  · simpa only [neg_nonpos, sub_nonneg] using hright.symm

private theorem properLink_deformedCarrier_avoidsLabelledInteriors
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane) (n : RationalNormal)
    (hP : polyhedralSupport P = K.support)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ a : Plane, Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a →
            ∀ t ∈ T, Disjoint (deformPoint φ a +ᵥ (normalDirection n : Set Plane))
              (deformPoint φ t +ᵥ Kφ.openCarrier) := by
  obtain ⟨I, hI, hIends, F₀, ε₀, hε₀, hprojection⟩ := openNormalProjection_deformation K P n hP
  obtain ⟨F₁, ε₁, hε₁, hcontrol⟩ := properLink_normalOrderControl K T n hrat htile
  refine ⟨F₀ ∪ F₁, min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro φ hφ Kφ hKφ a ha t ht
  have hφ₀ := finiteApproximation_strengthen F₀ (F₀ ∪ F₁) ε₀ (min ε₀ ε₁) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφ₁ := finiteApproximation_strengthen F₁ (F₀ ∪ F₁) ε₁ (min ε₀ ε₁) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  have hsourceNoInterval (e : ℝ × ℝ) (he : e ∈ I) :
      ¬ (normalEval n t + e.1 < normalEval n a ∧
        normalEval n a < normalEval n t + e.2) := by
    intro hbetween
    have hlevel : normalEval n a - normalEval n t ∈ normalEval n '' K.openCarrier := by
      rw [hI]
      exact Set.mem_iUnion₂.mpr ⟨e, he, by constructor <;> linarith [hbetween.1, hbetween.2]⟩
    obtain ⟨z, hz, hπz⟩ := hlevel
    have hline : t + z ∈ a +ᵥ (normalDirection n : Set Plane) := by
      apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
      apply (normalDirection_mem_iff n _).mpr
      change normalEval n (-a + (t + z)) = 0
      have heq : -a + (t + z) = (t + z) - a := by abel
      rw [heq, normalEval_sub, normalEval_add, hπz]
      ring
    have hopen : t + z ∈ t +ᵥ K.openCarrier := Set.vadd_mem_vadd_set hz
    exact Set.disjoint_left.mp (sourceBoundaryUnion_disjoint_openCarrier K T htile.2.1 t ht)
      (ha hline) hopen
  apply Set.disjoint_left.mpr
  intro x hxline hxopen
  have hπline : normalEval n x = normalEval n (deformPoint φ a) := by
    obtain ⟨z, hz, hxz⟩ := Set.mem_vadd_set.mp hxline
    have hzero := (normalDirection_mem_iff n z).mp hz
    rw [← hxz]
    change normalEval n (deformPoint φ a + z) = _
    rw [normalEval_add, hzero, add_zero]
  have hπopen : normalEval n (x - deformPoint φ t) ∈ normalEval n '' Kφ.openCarrier := by
    refine ⟨x - deformPoint φ t, ?_, rfl⟩
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using
      Set.mem_vadd_set_iff_neg_vadd_mem.mp hxopen
  rw [hprojection φ hφ₀ Kφ hKφ] at hπopen
  obtain ⟨e, he, heTarget⟩ := Set.mem_iUnion₂.mp hπopen
  rw [normalEval_sub, hπline] at heTarget
  obtain ⟨_, ⟨v, hv, hveq⟩, ⟨w, hw, hweq⟩⟩ := hIends e he
  have hsideV := properLink_endpointSide_transport K T n φ
    (fun b hb u hu => (hcontrol φ hφ₁ b hb u hu).1) a ha t ht v hv
  have hsideW := properLink_endpointSide_transport K T n φ
    (fun b hb u hu => (hcontrol φ hφ₁ b hb u hu).1) a ha t ht w hw
  rw [hveq] at hsideV
  rw [hweq] at hsideW
  by_cases hlower : normalEval n a ≤ normalEval n t + e.1
  · have hlowerTarget := hsideV.2.mp hlower
    linarith [heTarget.1]
  · have hupper : normalEval n t + e.2 ≤ normalEval n a := by
      by_contra h
      exact hsourceNoInterval e he ⟨lt_of_not_ge hlower, lt_of_not_ge h⟩
    have hupperTarget := hsideW.1.mp hupper
    linarith [heTarget.2]

theorem deformation_labelledBoundaryCollar :
  ∀ (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane),
    polyhedralSupport P = K.support → Tiling.RationalSlopes.HasRationalSlopes K →
    Tiling.Polygonal.TilesOn K T Set.univ →
      ∃ F : Finset ℝ, ∃ ε η₀ : ℝ, 0 < ε ∧ 0 < η₀ ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
            ∀ t ∈ T, ∀ η : ℝ, 0 < η → η < η₀ → ∀ x : Plane,
              0 < Metric.infDist x (deformPoint φ t +ᵥ Kφ.support) →
              Metric.infDist x (deformPoint φ t +ᵥ Kφ.support) < η →
                ∃ s ∈ T, s ≠ t ∧ x ∈ deformPoint φ s +ᵥ Kφ.support ∧
                  Metric.infDist x (deformPoint φ s +ᵥ frontier Kφ.support) < η := by
  intro K P T hP hrat htile
  obtain ⟨E, hproto, hcover, _⟩ := rationalIntrinsicPrimitiveEdges K hrat
  have hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)) :=
    fun e he => ⟨(hproto e he).1, (hproto e he).2.1, (hproto e he).2.2.1,
      (hproto e he).2.2.2.1, (hproto e he).2.2.2.2.1, (hproto e he).2.2.2.2.2.2⟩
  have hratE : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1) :=
    fun e he => (hproto e he).2.2.2.2.2.1
  obtain ⟨Fv, εv, Rv, hεv, hRv, hvertex⟩ :=
    rationalPrimitiveVertices_uniformFullStar_labelledCollar K P T hP htile E hE hratE hcover
  obtain ⟨Fl, εl, l, L, hεl, _, hL, hlength⟩ :=
    finiteRationalEdges_uniformLengthRange E hratE
  obtain ⟨Ft, εt, hεt, htransport⟩ := rationalPrimitiveFrontier_transport K P hP E
    (fun e he => ⟨(hE e he).1, hratE e he⟩) hcover
  let τ := min (1 / 2) (Rv / (2 * L))
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hRv (by positivity))
  have hτhalf : τ ≤ 1 / 2 := min_le_left _ _
  have hτmargin : τ * L < Rv := by
    have hbound : τ ≤ Rv / (2 * L) := min_le_right _ _
    have hprod : τ * (2 * L) ≤ Rv := (le_div_iff₀ (by positivity)).mp hbound
    nlinarith
  obtain ⟨Fc, εc, Rc, hεc, hRc, hcentral⟩ :=
    rationalPrimitiveEdges_uniformCentral_actualChainCollar K P T hP htile E hE hratE
      hcover τ hτ hτhalf
  let F := Fv ∪ Fl ∪ Ft ∪ Fc
  let ε := min εv (min εl (min εt εc))
  refine ⟨F, ε, min Rv Rc, lt_min hεv (lt_min hεl (lt_min hεt hεc)),
    lt_min hRv hRc, ?_⟩
  intro φ hφ Kφ hKφ t ht η hη hη₀ x hpos hnear
  have hφv : IsFiniteApproximation Fv εv φ := by
    apply finiteApproximation_strengthen Fv F εv ε φ _ (min_le_left _ _) hφ
    intro z hz
    simp [F, hz]
  have hφl : IsFiniteApproximation Fl εl φ := by
    apply finiteApproximation_strengthen Fl F εl ε φ _
      ((min_le_right _ _).trans (min_le_left _ _)) hφ
    intro z hz
    simp [F, hz]
  have hφt : IsFiniteApproximation Ft εt φ := by
    apply finiteApproximation_strengthen Ft F εt ε φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) hφ
    intro z hz
    simp [F, hz]
  have hφc : IsFiniteApproximation Fc εc φ := by
    apply finiteApproximation_strengthen Fc F εc ε φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) hφ
    intro z hz
    simp [F, hz]
  obtain ⟨y, hy, hdist⟩ := positiveInfDist_exists_nearestFullFrontier Kφ (deformPoint φ t) x hpos
  have hxy : dist x y < η := by rw [hdist]; exact hnear
  obtain ⟨H, hanchors, hsupport, hsegments, hfront⟩ := htransport φ hφt Kφ hKφ
  have hyproto := Set.mem_vadd_set_iff_neg_vadd_mem.mp hy
  rw [hfront] at hyproto
  obtain ⟨e, he, hyedge⟩ := Set.mem_iUnion₂.mp hyproto
  have hycopy : y ∈ deformPoint φ t +ᵥ
      segment ℝ (deformPoint φ e.1) (deformPoint φ e.2) :=
    Set.mem_vadd_set_iff_neg_vadd_mem.mpr hyedge
  have hyseg : y ∈ segment ℝ (deformPoint φ t + deformPoint φ e.1)
      (deformPoint φ t + deformPoint φ e.2) := by
    simpa only [vadd_segment, vadd_eq_add] using hycopy
  have hbound : dist (deformPoint φ t + deformPoint φ e.1)
      (deformPoint φ t + deformPoint φ e.2) ≤ L := by
    simpa only [dist_add_left] using (hlength φ hφl e he).2
  rcases segmentPoint_centralOrNearEndpoints _ _ y L Rv τ hL hτ hτhalf hbound hτmargin hyseg with
    hleft | hright | ⟨θ, hθ, hyθ⟩
  · have hmap : deformPoint φ (t + e.1) = deformPoint φ t + deformPoint φ e.1 :=
      (deformPointLinear φ).map_add t e.1
    exact hvertex φ hφv Kφ hKφ t ht e he (t + e.1) (Or.inl rfl) y hycopy
      (by rw [hmap]; exact hleft) η hη (hη₀.trans_le (min_le_left _ _)) x hxy hpos
  · have hmap : deformPoint φ (t + e.2) = deformPoint φ t + deformPoint φ e.2 :=
      (deformPointLinear φ).map_add t e.2
    exact hvertex φ hφv Kφ hKφ t ht e he (t + e.2) (Or.inr rfl) y hycopy
      (by rw [hmap]; exact hright) η hη (hη₀.trans_le (min_le_left _ _)) x hxy hpos
  · have hyEq : y = deformPoint φ t +
        AffineMap.lineMap (deformPoint φ e.1) (deformPoint φ e.2) θ := by
      rw [hyθ]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    exact hcentral φ hφc Kφ hKφ e he t ht θ hθ x
      (by rw [← hyEq]; exact hxy.trans (hη₀.trans_le (min_le_right _ _))) η hpos
      (by rw [← hyEq]; exact hxy)

theorem deformation_closedCopies_coverPlane :
  ∀ (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane),
    polyhedralSupport P = K.support → Tiling.RationalSlopes.HasRationalSlopes K →
    Tiling.Polygonal.TilesOn K T Set.univ →
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
            (⋃ t : T, deformPoint φ (t : Plane) +ᵥ Kφ.support) = Set.univ := by
  intro K P T hP hrat htile
  obtain ⟨F, ε, η₀, hε, hη₀, hcollar⟩ :=
    deformation_labelledBoundaryCollar K P T hP hrat htile
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ
  let U : Set Plane := ⋃ t : T, deformPoint φ (t : Plane) +ᵥ Kφ.support
  have close_mem (x y : Plane) (hx : x ∈ U) (hxy : dist y x < η₀ / 2) : y ∈ U := by
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
    by_cases hy : y ∈ deformPoint φ t.1 +ᵥ Kφ.support
    · exact Set.mem_iUnion.mpr ⟨t, hy⟩
    · have hclosed : IsClosed (deformPoint φ t.1 +ᵥ Kφ.support) :=
        Kφ.isPolygonal.isClosed.vadd _
      have hne : (deformPoint φ t.1 +ᵥ Kφ.support).Nonempty := by
        obtain ⟨z, hz⟩ := Kφ.nonempty
        exact ⟨deformPoint φ t.1 + z, Set.vadd_mem_vadd_set hz⟩
      have hdpos := (hclosed.notMem_iff_infDist_pos hne).mp hy
      have hdlt : Metric.infDist y (deformPoint φ t.1 +ᵥ Kφ.support) < η₀ / 2 :=
        (Metric.infDist_le_dist_of_mem ht).trans_lt hxy
      obtain ⟨s, hs, _, hys, _⟩ :=
        hcollar φ hφ Kφ hKφ t.1 t.2 (η₀ / 2) (by positivity) (by linarith) y hdpos hdlt
      exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hys⟩
  have hopen : IsOpen U := by
    rw [Metric.isOpen_iff]
    intro x hx
    refine ⟨η₀ / 2, by positivity, ?_⟩
    intro y hy
    exact close_mem x y hx hy
  have hclosed : IsClosed U := by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro x hx
    refine ⟨η₀ / 2, by positivity, ?_⟩
    intro y hy hyU
    exact hx (close_mem y x hyU (by simpa [dist_comm] using hy))
  have hTne : T.Nonempty := by
    by_contra h
    have hT : T = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have ha : ∀ᵐ x : Plane ∂volume, False := by
      filter_upwards [htile.2.2] with x hx
      simpa [hT] using hx
    have : volume (Set.univ : Set Plane) = 0 := by
      simpa using (ae_iff.mp ha)
    simpa using this
  have hUne : U.Nonempty := by
    obtain ⟨t, ht⟩ := hTne
    obtain ⟨z, hz⟩ := Kφ.nonempty
    exact ⟨deformPoint φ t + z, Set.mem_iUnion.mpr ⟨⟨t, ht⟩, Set.vadd_mem_vadd_set hz⟩⟩
  exact IsClopen.eq_univ ⟨hclosed, hopen⟩ hUne

theorem deformation_componentOverlapPropagates :
  ∀ (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane),
    polyhedralSupport P = K.support → Tiling.RationalSlopes.HasRationalSlopes K →
    Tiling.Polygonal.TilesOn K T Set.univ →
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
            ∀ t ∈ T, ∀ x ∈ deformPoint φ t +ᵥ Kφ.openCarrier,
              ∀ O : Set Plane,
                O = connectedComponentIn (deformPoint φ t +ᵥ Kφ.openCarrier) x →
                (∃ s ∈ T, s ≠ t ∧ (O ∩ (deformPoint φ s +ᵥ Kφ.openCarrier)).Nonempty) →
                  O ⊆ ⋃ s : {s : Plane // s ∈ T ∧ s ≠ t},
                    deformPoint φ s.1 +ᵥ Kφ.support := by
  intro K P T hP hrat htile
  obtain ⟨F, ε, η₀, hε, hη₀, hcollar⟩ := deformation_labelledBoundaryCollar K P T hP hrat htile
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ t ht x hx O hO hoverlap
  let B : Set Plane := deformPoint φ t +ᵥ frontier Kφ.support
  have hBclosed : IsClosed B := isClosed_frontier.vadd _
  have hBne : B.Nonempty := by
    obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr
      ⟨Kφ.nonempty, Kφ.isPolygonal.isCompact.ne_univ⟩
    exact ⟨deformPoint φ t + z, Set.vadd_mem_vadd_set hz⟩
  let d : Plane → ℝ := fun y => Metric.infDist y B
  have hOsub : O ⊆ deformPoint φ t +ᵥ Kφ.openCarrier := by
    rw [hO]
    exact connectedComponentIn_subset _ _
  have hdpos (y : Plane) (hy : y ∈ O) : 0 < d y := by
    apply (hBclosed.notMem_iff_infDist_pos hBne).mp
    intro hyB
    have hyi := Set.mem_vadd_set_iff_neg_vadd_mem.mp (hOsub hy)
    have hyf := Set.mem_vadd_set_iff_neg_vadd_mem.mp hyB
    exact Set.disjoint_left.mp disjoint_interior_frontier hyi hyf
  let X : Set O := {y | ∃ s ∈ T, s ≠ t ∧ y.1 ∈ deformPoint φ s +ᵥ Kφ.support}
  have close_mem (a b : O) (η : ℝ) (hη : 0 < η) (hη₀' : η < η₀)
      (hd : η < d a.1) (hab : dist a.1 b.1 < η) (hb : b ∈ X) : a ∈ X := by
    obtain ⟨s, hs, hst, hbs⟩ := hb
    by_cases has : a.1 ∈ deformPoint φ s +ᵥ Kφ.support
    · exact ⟨s, hs, hst, has⟩
    · have hclosed : IsClosed (deformPoint φ s +ᵥ Kφ.support) := Kφ.isPolygonal.isClosed.vadd _
      have hne : (deformPoint φ s +ᵥ Kφ.support).Nonempty := by
        obtain ⟨z, hz⟩ := Kφ.nonempty
        exact ⟨deformPoint φ s + z, Set.vadd_mem_vadd_set hz⟩
      have hd₁ := (hclosed.notMem_iff_infDist_pos hne).mp has
      have hd₂ : Metric.infDist a.1 (deformPoint φ s +ᵥ Kφ.support) < η :=
        (Metric.infDist_le_dist_of_mem hbs).trans_lt hab
      obtain ⟨q, hq, hqs, haq, hboundary⟩ :=
        hcollar φ hφ Kφ hKφ s hs η hη hη₀' a.1 hd₁ hd₂
      have hqt : q ≠ t := by
        intro heq
        subst q
        exact (not_lt_of_ge hd.le) hboundary
      exact ⟨q, hq, hqt, haq⟩
  have nearby (a : O) : ∃ η : ℝ, 0 < η ∧ ∀ b : O,
      dist b a < η → (b ∈ X ↔ a ∈ X) := by
    let η : ℝ := min (η₀ / 2) (d a.1 / 3)
    have hda := hdpos a.1 a.2
    have hη : 0 < η := lt_min (by positivity) (by positivity)
    have hη₀' : η < η₀ := (min_le_left _ _).trans_lt (by linarith)
    have hηd : η < d a.1 := (min_le_right _ _).trans_lt (by linarith)
    refine ⟨η, hη, ?_⟩
    intro b hba
    have hdab : d a.1 ≤ d b.1 + dist a.1 b.1 := Metric.infDist_le_infDist_add_dist
    have hab : dist a.1 b.1 < η := by simpa only [Subtype.dist_eq, dist_comm] using hba
    have hηdb : η < d b.1 := by
      have hsmall : η ≤ d a.1 / 3 := min_le_right _ _
      linarith
    exact ⟨close_mem a b η hη hη₀' hηd hab,
      close_mem b a η hη hη₀' hηdb (by simpa [dist_comm] using hab)⟩
  have hopen : IsOpen X := by
    rw [Metric.isOpen_iff]
    intro a ha
    obtain ⟨η, hη, hnear⟩ := nearby a
    exact ⟨η, hη, fun b hb => (hnear b hb).mpr ha⟩
  have hclosed : IsClosed X := by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro a ha
    obtain ⟨η, hη, hnear⟩ := nearby a
    exact ⟨η, hη, fun b hb hbx => ha ((hnear b hb).mp hbx)⟩
  haveI : PreconnectedSpace O := isPreconnected_iff_preconnectedSpace.mp (by
    rw [hO]
    exact isPreconnected_connectedComponentIn)
  have hXne : X.Nonempty := by
    obtain ⟨s, hs, hst, y, hyO, hys⟩ := hoverlap
    refine ⟨⟨y, hyO⟩, s, hs, hst, ?_⟩
    apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
    exact interior_subset (Set.mem_vadd_set_iff_neg_vadd_mem.mp hys)
  have hXfull : X = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hXne
  intro y hy
  have hyX : (⟨y, hy⟩ : O) ∈ X := hXfull ▸ Set.mem_univ _
  obtain ⟨s, hs, hst, hys⟩ := hyX
  exact Set.mem_iUnion.mpr ⟨⟨s, hs, hst⟩, hys⟩

/-- Properness of the image of an actual source full carrier is derived only
after labelled closed-copy coverage.  No target packing or LF is used. -/
private theorem properLink_deformation_fromCoverage
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane) (n : RationalNormal)
    (hP : polyhedralSupport P = K.support)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ a : Plane, Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a →
            Tiling.RationalSlopes.IsProperLink Kφ (normalDirection n)
              (deformPoint φ '' T) (deformPoint φ a) := by
  obtain ⟨F₀, ε₀, hε₀, hcoverage⟩ := deformation_closedCopies_coverPlane K P T hP hrat htile
  obtain ⟨F₁, ε₁, hε₁, havoidance⟩ :=
    properLink_deformedCarrier_avoidsLabelledInteriors K P T n hP hrat htile
  refine ⟨F₀ ∪ F₁, min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro φ hφ Kφ hKφ a ha x hx
  have hφ₀ := finiteApproximation_strengthen F₀ (F₀ ∪ F₁) ε₀ (min ε₀ ε₁) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφ₁ := finiteApproximation_strengthen F₁ (F₀ ∪ F₁) ε₁ (min ε₀ ε₁) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  have hxcovered : x ∈ ⋃ t : T, deformPoint φ (t : Plane) +ᵥ Kφ.support := by
    rw [hcoverage φ hφ₀ Kφ hKφ]
    exact Set.mem_univ _
  obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hxcovered
  have hxnotint : x ∉ interior (deformPoint φ (t : Plane) +ᵥ Kφ.support) := by
    rw [interior_vadd]
    exact fun h => Set.disjoint_left.mp
      (havoidance φ hφ₁ Kφ hKφ a ha (t : Plane) t.2) hx h
  have hxfront : x ∈ frontier (deformPoint φ (t : Plane) +ᵥ Kφ.support) := by
    rw [(Kφ.isPolygonal.isClosed.vadd _).frontier_eq]
    exact ⟨hxt, hxnotint⟩
  have hfrontier : frontier (deformPoint φ (t : Plane) +ᵥ Kφ.support) =
      deformPoint φ (t : Plane) +ᵥ frontier Kφ.support := by
    rw [frontier, closure_vadd, interior_vadd, ← Set.vadd_set_sdiff]
    rfl
  rw [hfrontier] at hxfront
  exact Set.mem_iUnion.mpr
    ⟨⟨deformPoint φ (t : Plane), Set.mem_image_of_mem _ t.2⟩, hxfront⟩

private theorem exists_frontier_between_openIntervals
    (A : Set ℝ) (hA : IsOpen A) {a b c d : ℝ}
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hleft : Ioo a b ⊆ A)
    (hright : Disjoint (Ioo c d) (closure A)) :
    ∃ r ∈ frontier A, b ≤ r ∧ r ≤ c := by
  obtain ⟨x, hax, hxb⟩ := exists_between hab
  obtain ⟨y, hcy, hyd⟩ := exists_between hcd
  have hxy : x < y := lt_of_lt_of_le hxb (le_trans hbc hcy.le)
  let K : Set ℝ := Icc x y
  have hK : IsPreconnected K := (isConnected_Icc hxy.le).2
  have hxK : x ∈ K := ⟨le_rfl, hxy.le⟩
  have hyK : y ∈ K := ⟨hxy.le, le_rfl⟩
  have hxA : x ∈ A := hleft ⟨hax, hxb⟩
  have hyV : y ∈ interior Aᶜ := by
    apply interior_maximal ?_ (isOpen_Ioo : IsOpen (Ioo c d)) ⟨hcy, hyd⟩
    intro z hz
    exact (fun hzA =>
      (Set.disjoint_left.mp hright) hz (subset_closure hzA))
  have hsep : ∃ r ∈ K, r ∈ frontier A := by
    by_contra hn
    have hno : K ∩ frontier A = ∅ := by
      ext z
      constructor
      · intro hz
        exact False.elim (hn ⟨z, hz.1, hz.2⟩)
      · simp
    have hcover : K ⊆ A ∪ interior Aᶜ := by
      intro z hz
      have hzfront : z ∉ frontier A := by
        intro hz'
        have : z ∈ K ∩ frontier A := ⟨hz, hz'⟩
        simpa [hno] using this
      have hzsplit : z ∈ interior A ∪ interior Aᶜ := by
        rw [← compl_frontier_eq_union_interior]
        exact hzfront
      rcases hzsplit with hzA | hzAc
      · exact Or.inl (by simpa [hA.interior_eq] using hzA)
      · exact Or.inr hzAc
    obtain ⟨z, ⟨hzK, ⟨hzA, hzV⟩⟩⟩ := hK A (interior Aᶜ) hA isOpen_interior
      hcover ⟨x, hxK, hxA⟩ ⟨y, hyK, hyV⟩
    exact (interior_subset hzV) hzA
  obtain ⟨r, hrK, hrf⟩ := hsep
  refine ⟨r, hrf, ?_, ?_⟩
  · by_contra hbr
    have hrlt : r < b := lt_of_not_ge hbr
    have hrA : r ∈ A := hleft ⟨lt_of_lt_of_le hax hrK.1, hrlt⟩
    have : r ∈ A ∩ frontier A := ⟨hrA, hrf⟩
    simpa [hA.inter_frontier_eq] using this
  · by_contra hrc
    have hrc' : c < r := lt_of_not_ge hrc
    have hrd : r < d := lt_of_le_of_lt hrK.2 hyd
    have hrV : r ∈ interior Aᶜ := by
      apply interior_maximal ?_ (isOpen_Ioo : IsOpen (Ioo c d)) ⟨hrc', hrd⟩
      intro z hz
      exact (fun hzA =>
        (Set.disjoint_left.mp hright) hz (subset_closure hzA))
    rw [interior_compl] at hrV
    exact hrV (frontier_subset_closure hrf)

private def realNegHomeomorph : Homeomorph ℝ ℝ where
  toFun := fun x => -x
  invFun := fun x => -x
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  continuous_toFun := continuous_neg
  continuous_invFun := continuous_neg

private theorem exists_frontier_between_openIntervals_reverse
    (A : Set ℝ) (hA : IsOpen A) {a b c d : ℝ}
    (hab : a < b) (hda : d ≤ a) (hcd : c < d)
    (hleft : Ioo a b ⊆ A)
    (hright : Disjoint (Ioo c d) (closure A)) :
    ∃ r ∈ frontier A, d ≤ r ∧ r ≤ a := by
  let R := realNegHomeomorph
  let A' : Set ℝ := R ⁻¹' A
  have hA' : IsOpen A' := hA.preimage R.continuous
  have hclosure : closure A' = R ⁻¹' closure A :=
    (R.isOpenMap.preimage_closure_eq_closure_preimage R.continuous A).symm
  have hleft' : Ioo (-b) (-a) ⊆ A' := by
    intro x hx
    apply hleft
    change -x ∈ Ioo a b
    constructor <;> linarith [hx.1, hx.2]
  have hright' : Disjoint (Ioo (-d) (-c)) (closure A') := by
    apply Set.disjoint_left.mpr
    intro x hx hxcl
    have hx' : -x ∈ Ioo c d := by constructor <;> linarith [hx.1, hx.2]
    have hxclR : R x ∈ closure A := by
      rw [hclosure] at hxcl
      exact hxcl
    have hxcl' : -x ∈ closure A := by
      change -x ∈ closure A at hxclR
      exact hxclR
    exact (Set.disjoint_left.mp hright) hx' hxcl'
  have hfr : R ⁻¹' frontier A = frontier A' :=
    R.isOpenMap.preimage_frontier_eq_frontier_preimage R.continuous A
  obtain ⟨r', hr', hlo, hhi⟩ :=
    exists_frontier_between_openIntervals A' hA' (by linarith)
      (by linarith) (by linarith) hleft' hright'
  refine ⟨-r', ?_, ?_, ?_⟩
  · change -r' ∈ frontier A
    have hrpre : r' ∈ R ⁻¹' frontier A := by rw [hfr]; exact hr'
    change R r' ∈ frontier A at hrpre
    change -r' ∈ frontier A at hrpre
    exact hrpre
  · linarith
  · linarith

private theorem exists_frontier_between_openIntervals_full
    (A : Set ℝ) (hA : IsOpen A) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hleft : Ioo a b ⊆ A)
    (hright : Disjoint (Ioo c d) (closure A)) :
    ∃ r ∈ frontier A,
      (b ≤ r ∧ r ≤ c) ∨ (d ≤ r ∧ r ≤ a) := by
  by_cases hbc : b ≤ c
  · obtain ⟨r, hr, hbr, hrc⟩ :=
      exists_frontier_between_openIntervals A hA hab hbc hcd hleft hright
    exact ⟨r, hr, Or.inl ⟨hbr, hrc⟩⟩
  · have hda : d ≤ a := by
      by_contra h
      have had : a < d := lt_of_not_ge h
      have hcb : c < b := lt_of_not_ge hbc
      have hmax : max a c < min b d := by
        simp only [max_lt_iff, lt_min_iff]
        constructor <;> constructor <;> linarith
      obtain ⟨x, hx⟩ := exists_between hmax
      have hxAB : x ∈ Ioo a b :=
        ⟨lt_of_le_of_lt (le_max_left _ _) hx.1,
          lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
      have hxCD : x ∈ Ioo c d :=
        ⟨lt_of_le_of_lt (le_max_right _ _) hx.1,
          lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
      exact (Set.disjoint_left.mp hright) hxCD (subset_closure (hleft hxAB))
    obtain ⟨r, hr, hdr, hra⟩ :=
      exists_frontier_between_openIntervals_reverse A hA hab hda hcd hleft hright
    exact ⟨r, hr, Or.inr ⟨hdr, hra⟩⟩

theorem saturatedSubfamily_forwardTransport :
  ∀ (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane) (n : RationalNormal),
    polyhedralSupport P = K.support → Tiling.RationalSlopes.HasRationalSlopes K →
    Tiling.Polygonal.TilesOn K T Set.univ →
    Tiling.RationalSlopes.HasProperLink K (normalDirection n) T →
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
            Tiling.Polygonal.TilesOn Kφ (deformPoint φ '' T) Set.univ →
              ∀ S ⊆ T,
                Tiling.Polygonal.IsInvariantAlong (Tiling.Polygonal.regularSupport K S)
                  (normalDirection n) →
                Tiling.Polygonal.IsInvariantAlong
                  (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S))
                    (normalDirection n) := by
  intro K P T n hP hrat htile _
  obtain ⟨I, hI, hends, F₀, ε₀, hε₀, hdeform⟩ :=
    openNormalProjection_deformation K P n hP
  obtain ⟨F₁, ε₁, hε₁, hcontrol⟩ := properLink_normalOrderControl K T n hrat htile
  refine ⟨F₀ ∪ F₁, min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro φ hφ Kφ hKφ htileφ S hST hinv
  have hφ₀ := finiteApproximation_strengthen F₀ (F₀ ∪ F₁) ε₀ (min ε₀ ε₁) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφ₁ := finiteApproximation_strengthen F₁ (F₀ ∪ F₁) ε₁ (min ε₀ ε₁) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  let A := normalEval n '' Tiling.Polygonal.regularSupport K S
  obtain ⟨hA, hScolour, hTcolour, hfront⟩ :=
    sourceSubfamily_projectionColours K n T S htile.2.1 hST hinv
  apply regularSupport_invariant_of_noCrossProjection Kφ n (deformPoint φ '' T)
    (deformPoint φ '' S) htileφ (Set.image_mono hST)
  intro s' hs' t' ht' ht'not
  obtain ⟨s, hs, rfl⟩ := hs'
  obtain ⟨t, ht, rfl⟩ := ht'
  have htnot : t ∉ S := fun htS => ht'not ⟨t, htS, rfl⟩
  rw [Set.disjoint_left]
  intro r hrs hrt
  rw [normalProjection_translateIntervals n Kφ.openCarrier I (fun q => (φ q : ℝ))
    (hdeform φ hφ₀ Kφ hKφ) (deformPoint φ s)] at hrs
  rw [normalProjection_translateIntervals n Kφ.openCarrier I (fun q => (φ q : ℝ))
    (hdeform φ hφ₀ Kφ hKφ) (deformPoint φ t)] at hrt
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hrs
  obtain ⟨heI, hre⟩ := Set.mem_iUnion.mp he
  obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hrt
  obtain ⟨hfI, hrf⟩ := Set.mem_iUnion.mp hf
  obtain ⟨hepos, ⟨u, hu, hulo⟩, ⟨v, hv, hvhi⟩⟩ := hends e heI
  obtain ⟨hfpos, ⟨w, hw, hwlo⟩, ⟨z, hz, hzhi⟩⟩ := hends f hfI
  have hsI : Set.Ioo (normalEval n s + e.1) (normalEval n s + e.2) ⊆ A := by
    intro q hq
    apply hScolour s hs
    rw [normalProjection_translateIntervals n K.openCarrier I id hI s]
    simp only [id_eq]
    exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨heI, hq⟩⟩
  have htI : Disjoint (Set.Ioo (normalEval n t + f.1) (normalEval n t + f.2))
      (closure A) := by
    apply (hTcolour t ht htnot).mono_left
    intro q hq
    rw [normalProjection_translateIntervals n K.openCarrier I id hI t]
    simp only [id_eq]
    exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hfI, hq⟩⟩
  obtain ⟨b, hb, hsep⟩ := exists_frontier_between_openIntervals_full A hA
    (a := normalEval n s + e.1) (b := normalEval n s + e.2)
    (c := normalEval n t + f.1) (d := normalEval n t + f.2)
    (by linarith) (by linarith) hsI htI
  obtain ⟨a, ha, hafront⟩ := hfront b hb
  have halink := sourceInvariantBoundary_isProperLink K T S (normalDirection n)
    htile.2.1 hST hinv hafront
  have hside (p : Plane) (hp : p ∈ T) (q : Plane)
      (hq : q ∈ Tiling.vertexSet K.support) :=
    properLink_endpointSide_transport K T n φ
      (fun a ha v hv => (hcontrol φ hφ₁ a ha v hv).1) a halink p hp q hq
  rcases hsep with ⟨heb, hbf⟩ | ⟨hfb, hbe⟩
  · have hsupper := (hside s (hST hs) v hv).1.mp (by simpa only [hvhi, ha] using heb)
    have htlower := (hside t ht w hw).2.mp (by simpa only [hwlo, ha] using hbf)
    rw [hvhi] at hsupper
    rw [hwlo] at htlower
    have hrupper := hre.2
    have hrlower := hrf.1
    linarith
  · have htupper := (hside t ht z hz).1.mp (by simpa only [hzhi, ha] using hfb)
    have hslower := (hside s (hST hs) u hu).2.mp (by simpa only [hulo, ha] using hbe)
    rw [hzhi] at htupper
    rw [hulo] at hslower
    have hrupper := hrf.2
    have hrlower := hre.1
    linarith

private theorem labelledPacking_injOn (K : PolygonalRegion) (T : Set Plane)
    (f : Plane → Plane)
    (hpack : ∀ s ∈ T, ∀ t ∈ T, s ≠ t →
      Disjoint (f s +ᵥ K.openCarrier) (f t +ᵥ K.openCarrier)) : Set.InjOn f T := by
  intro s hs t ht hst
  by_contra hne
  obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hzs : f s + z ∈ f s +ᵥ K.openCarrier := Set.vadd_mem_vadd_set hz
  have hzt : f s + z ∈ f t +ᵥ K.openCarrier := by simpa [hst] using hzs
  exact Set.disjoint_left.mp (hpack s hs t ht hne) hzs hzt

private theorem labelledPacking_indexedLF (K : PolygonalRegion) (T : Set Plane)
    (f : Plane → Plane)
    (hpack : ∀ s ∈ T, ∀ t ∈ T, s ≠ t →
      Disjoint (f s +ᵥ K.openCarrier) (f t +ᵥ K.openCarrier)) :
    ∀ Q : Set Plane, Bornology.IsBounded Q → {t | t ∈ T ∧ f t ∈ Q}.Finite := by
  have hinj := labelledPacking_injOn K T f hpack
  have hp : Tiling.IsPacking K.prototileFamily (K.placements (f '' T)) := by
    apply (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K (f '' T)).mpr
    intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact hpack s hs t ht (fun hst => hxy (congrArg f hst))
  intro Q hQ
  have hfinite := (Tiling.Polygonal.packing_centres_locallyFinite hp).1 Q hQ
  have hsubset : f '' {t | t ∈ T ∧ f t ∈ Q} ⊆ (f '' T) ∩ Q := by
    rintro _ ⟨t, ⟨ht, htQ⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, htQ⟩
  exact (hfinite.subset hsubset).of_finite_image (hinj.mono fun _ ht => ht.1)

private theorem labelledPacking_image_isPacking (K : PolygonalRegion) (T : Set Plane)
    (f : Plane → Plane)
    (hpack : ∀ s ∈ T, ∀ t ∈ T, s ≠ t →
      Disjoint (f s +ᵥ K.openCarrier) (f t +ᵥ K.openCarrier)) :
    Tiling.IsPacking K.prototileFamily (K.placements (f '' T)) := by
  apply (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K (f '' T)).mpr
  intro x hx y hy hxy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  exact hpack s hs t ht (fun hst => hxy (congrArg f hst))

private theorem closedCopies_image_eq (K : PolygonalRegion) (T : Set Plane) (f : Plane → Plane) :
    (⋃ t : f '' T, (t : Plane) +ᵥ K.support) = ⋃ t : T, f t.1 +ᵥ K.support := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨s, hs⟩, hxs⟩ := Set.mem_iUnion.mp hx
    obtain ⟨t, ht, rfl⟩ := hs
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hxs⟩
  · intro hx
    obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨f t.1, ⟨t.1, t.2, rfl⟩⟩, hxt⟩

private def packingSol_singleOpenUnion
    (Kφ : PolygonalRegion) (T : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ) : Set Plane :=
  {y | ∃ t ∈ T, ∃ x ∈ deformPoint φ t +ᵥ Kφ.openCarrier,
    y ∈ connectedComponentIn (deformPoint φ t +ᵥ Kφ.openCarrier) x ∧
      ∀ s ∈ T, s ≠ t →
        Disjoint (connectedComponentIn (deformPoint φ t +ᵥ Kφ.openCarrier) x)
          (deformPoint φ s +ᵥ Kφ.openCarrier)}

/-- Once the genuinely constructed single family is dense, no open overlap
    can remain. This final reduction uses no local finiteness of all labels. -/
private theorem packingSol_denseSingle_forces_labelledDisjoint
    (Kφ : PolygonalRegion) (T : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ)
    (hdense : Dense (packingSol_singleOpenUnion Kφ T φ)) :
    ∀ s ∈ T, ∀ t ∈ T, s ≠ t →
      Disjoint (deformPoint φ s +ᵥ Kφ.openCarrier)
        (deformPoint φ t +ᵥ Kφ.openCarrier) := by
  intro s hs t ht hst
  apply Set.disjoint_left.mpr
  intro y hys hyt
  have hopen : IsOpen ((deformPoint φ s +ᵥ Kφ.openCarrier) ∩
      (deformPoint φ t +ᵥ Kφ.openCarrier)) :=
    (isOpen_interior.vadd _).inter (isOpen_interior.vadd _)
  obtain ⟨z, hzsingle, hzs, hzt⟩ := hdense.exists_mem_open hopen ⟨y, hys, hyt⟩
  obtain ⟨q, hq, x, hx, hzq, hsingle⟩ := hzsingle
  by_cases hqs : q = s
  · subst q
    exact Set.disjoint_left.mp (hsingle t ht (Ne.symm hst)) hzq hzt
  · exact Set.disjoint_left.mp (hsingle s hs (Ne.symm hqs)) hzq hzs


namespace PackingSolSingleFamily

open Tiling

private abbrev Component (K : PolygonalRegion) :=
  {O : Set Plane // O ∈ Tiling.interiorComponents K.support}

private abbrev SingleIndex (K : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane) :=
  {tc : T × Component K //
    ∀ s ∈ T, s ≠ (tc.1 : Plane) →
      Disjoint (ψ tc.1 +ᵥ tc.2.1) (ψ s +ᵥ K.openCarrier)}

private def componentPrototiles (K : PolygonalRegion) : PrototileFamily Plane (Component K) :=
  fun O => {
    support := closure O.1
    measurableSet_support := isClosed_closure.measurableSet
    nonempty_support := (Tiling.interiorComponent_basic O.2).2.1.nonempty.mono subset_closure
  }

private def physicalPlacement (K : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (i : SingleIndex K T ψ) : Placement Plane (Component K) :=
  (ψ i.1.1, i.1.2)

private theorem single_interiors_pairwise
    (K : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane) :
    Pairwise fun i j : SingleIndex K T ψ =>
      Disjoint (ψ i.1.1 +ᵥ i.1.2.1) (ψ j.1.1 +ᵥ j.1.2.1) := by
  intro i j hij
  by_cases hlabel : i.1.1 = j.1.1
  · have hcomponent : i.1.2 ≠ j.1.2 := by
      intro heq
      exact hij (Subtype.ext (Prod.ext hlabel heq))
    have hset : i.1.2.1 ≠ j.1.2.1 := by
      intro heq
      exact hcomponent (Subtype.ext heq)
    have hd := Tiling.interiorComponents_pairwiseDisjoint K.support
      i.1.2.2 j.1.2.2 hset
    rw [hlabel, Set.disjoint_left]
    intro x hxi hxj
    exact Set.disjoint_left.mp hd
      (Set.mem_vadd_set_iff_neg_vadd_mem.mp hxi)
      (Set.mem_vadd_set_iff_neg_vadd_mem.mp hxj)
  · have hlabel' : (j.1.1 : Plane) ≠ (i.1.1 : Plane) := by
      intro heq
      exact hlabel (Subtype.ext heq.symm)
    have hd := i.2 j.1.1 j.1.1.2 hlabel'
    exact hd.mono_right (vadd_set_mono (Tiling.interiorComponent_basic j.1.2.2).2.2)

private theorem single_interior_nonempty
    (K : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (i : SingleIndex K T ψ) :
    (ψ i.1.1 +ᵥ i.1.2.1).Nonempty := by
  obtain ⟨x, hx⟩ := (Tiling.interiorComponent_basic i.1.2.2).2.1.nonempty
  exact ⟨ψ i.1.1 + x, ⟨x, hx, rfl⟩⟩

/-- Singleness makes the physical-placement map injective ON the selected OLD indices.
No ambient injectivity of ψ or replacement by unlabelled image centres is used. -/
private theorem physicalPlacement_injective
    (K : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane) :
    Injective (physicalPlacement K T ψ) := by
  intro i j heq
  by_contra hij
  have hcenter : ψ i.1.1 = ψ j.1.1 :=
    congrArg (fun p : Placement Plane (Component K) => p.1) heq
  have hcomponent : i.1.2 = j.1.2 :=
    congrArg (fun p : Placement Plane (Component K) => p.2) heq
  have hopen : ψ i.1.1 +ᵥ i.1.2.1 = ψ j.1.1 +ᵥ j.1.2.1 := by
    rw [hcenter, hcomponent]
  obtain ⟨x, hx⟩ := single_interior_nonempty K T ψ i
  exact Set.disjoint_left.mp (single_interiors_pairwise K T ψ hij) hx (hopen ▸ hx)

/-- Finite component prototypes and actual singleness derive packing, rather than assume it. -/
private theorem single_component_physical_packing
    (K : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane) :
    IsPacking (componentPrototiles K) (Set.range (physicalPlacement K T ψ)) := by
  let A : PolygonalProtoTiling (Component K) := {
    prototiles := componentPrototiles K
    placements := Set.range (physicalPlacement K T ψ)
    isPolygonal := fun O => K.isPolygonal.interiorComponent_closure_isPolygonal O.2
  }
  intro p hp q hq hpq
  obtain ⟨i, rfl⟩ := hp
  obtain ⟨j, rfl⟩ := hq
  have hij : i ≠ j := fun h => hpq (congrArg (physicalPlacement K T ψ) h)
  have hd := single_interiors_pairwise K T ψ hij
  have hdi : Disjoint
      (interior (placedTile A.prototiles (physicalPlacement K T ψ i)))
      (interior (placedTile A.prototiles (physicalPlacement K T ψ j))) := by
    change Disjoint (interior (ψ i.1.1 +ᵥ closure i.1.2.1))
      (interior (ψ j.1.1 +ᵥ closure j.1.2.1))
    rw [interior_vadd, interior_vadd,
      K.isPolygonal.interiorComponent_interior_closure_eq i.1.2.2,
      K.isPolygonal.interiorComponent_interior_closure_eq j.1.2.2]
    exact hd
  exact hdi.aedisjoint.congr
    (A.isPolygonal_placedTile (physicalPlacement K T ψ i)).interior_ae_eq.symm
    (A.isPolygonal_placedTile (physicalPlacement K T ψ j)).interior_ae_eq.symm

/-- Local finiteness indexed by OLD labels and genuine prototype interior components.
Singleness is the index predicate; ψ is an arbitrary function and T is arbitrary. -/
private theorem labelled_single_component_closures_locallyFinite
    (K : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane) :
    LocallyFinite (fun i : SingleIndex K T ψ =>
      ψ i.1.1 +ᵥ closure i.1.2.1) := by
  classical
  haveI : Finite (Component K) := K.isPolygonal.interiorComponents_finite.to_subtype
  let A : PolygonalProtoTiling (Component K) := {
    prototiles := componentPrototiles K
    placements := Set.range (physicalPlacement K T ψ)
    isPolygonal := fun O => K.isPolygonal.interiorComponent_closure_isPolygonal O.2
  }
  have hp : IsPacking A.prototiles A.placements :=
    single_component_physical_packing K T ψ
  let f : SingleIndex K T ψ → A.placements := fun i =>
    ⟨physicalPlacement K T ψ i, ⟨i, rfl⟩⟩
  have hf : Injective f := by
    intro i j heq
    have heq' : physicalPlacement K T ψ i = physicalPlacement K T ψ j :=
      congrArg (fun p : A.placements => p.1) heq
    exact physicalPlacement_injective K T ψ heq'
  have hlf : LocallyFinite (fun p : A.placements => placedTile A.prototiles p.1) :=
    A.locallyFinite_placedTile hp
  have hlf' := hlf.comp_injective hf
  exact hlf'

private abbrev closedComponent (K : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (i : SingleIndex K T ψ) : Set Plane :=
  ψ i.1.1 +ᵥ closure i.1.2.1

private abbrev singleClosedUnion (K : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane) :
    Set Plane := ⋃ i : SingleIndex K T ψ, closedComponent K T ψ i

private theorem component_polygonal (K : PolygonalRegion) (T : Set Plane)
    (ψ : Plane → Plane) (i : SingleIndex K T ψ) :
    IsPolygonal (closedComponent K T ψ i) :=
  (K.isPolygonal.interiorComponent_closure_isPolygonal i.1.2.2).vadd _

private theorem closed_components_aedisjoint (K : PolygonalRegion) (T : Set Plane)
    (ψ : Plane → Plane) :
    Pairwise fun i j : SingleIndex K T ψ =>

      AEDisjoint volume (closedComponent K T ψ i) (closedComponent K T ψ j) := by
  intro i j hij
  have hd := single_interiors_pairwise K T ψ hij
  have hdi : Disjoint (interior (closedComponent K T ψ i))
      (interior (closedComponent K T ψ j)) := by
    dsimp only [closedComponent]
    rw [interior_vadd, interior_vadd,
      K.isPolygonal.interiorComponent_interior_closure_eq i.1.2.2,
      K.isPolygonal.interiorComponent_interior_closure_eq j.1.2.2]
    exact hd
  exact hdi.aedisjoint.congr (component_polygonal K T ψ i).interior_ae_eq.symm
    (component_polygonal K T ψ j).interior_ae_eq.symm

private theorem frontier_eventuallyEq_of_closed
    {s t : Set Plane} {x : Plane} (hs : IsClosed s) (ht : IsClosed t)
    (h : s =ᶠ[𝓝 x] t) : frontier s =ᶠ[𝓝 x] frontier t := by
  filter_upwards [h, h.eventually_nhds] with y hy hyn
  have hyn' : s =ᶠ[𝓝 y] t := hyn
  rw [hs.frontier_eq, ht.frontier_eq]
  ext
  exact and_congr (iff_of_eq hy) (not_congr hyn'.mem_interior_iff)

/-- Every polygonal boundary germ contains a point outside any prescribed finite set. -/
private theorem polygonal_frontier_near_avoiding
    {D V U : Set Plane} (hD : IsPolygonal D) (hV : V.Finite)
    {p : Plane} (hp : p ∈ frontier D) (hU : U ∈ 𝓝 p) :
    ∃ q ∈ frontier D, q ∈ U ∧ q ∉ V := by
  classical
  obtain ⟨F, hF, hcover⟩ := hD.exists_finite_intrinsic_boundarySegments
  obtain ⟨e, he, hpseg⟩ := Set.mem_iUnion₂.mp (hcover ▸ hp)
  have hne := (hF e he).1
  obtain ⟨a, ha, hap⟩ : ∃ a ∈ segment ℝ e.1 e.2, a ≠ p := by
    by_cases h : e.1 = p
    · exact ⟨e.2, right_mem_segment _ _ _, fun hh => hne (h.trans hh.symm)⟩
    · exact ⟨e.1, left_mem_segment _ _ _, h⟩
  let f : ℝ → Plane := fun t => p + t • (a - p)
  have hf : Continuous f := by fun_prop
  have hf0 : f 0 = p := by simp [f]
  have hpre : f ⁻¹' U ∈ 𝓝 (0 : ℝ) := hf.continuousAt.preimage_mem_nhds (hf0 ▸ hU)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let b := min r 1
  have hb : 0 < b := lt_min hr zero_lt_one
  have hinj : Injective f := by
    intro t u htu
    exact smul_left_injective ℝ (sub_ne_zero.mpr hap) (add_left_cancel htu)
  have hfin : (f ⁻¹' V).Finite := hV.preimage hinj.injOn
  obtain ⟨t, ht, htv⟩ := (Set.Ioo_infinite hb).exists_notMem_finite hfin
  have htball : t ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [sub_zero, abs_of_pos ht.1]
    exact ht.2.trans_le (min_le_left _ _)
  have htseg : f t ∈ segment ℝ p a := by
    rw [segment_eq_image']
    exact ⟨t, ⟨ht.1.le, ht.2.le.trans (min_le_right _ _)⟩, rfl⟩
  have hsub : segment ℝ p a ⊆ segment ℝ e.1 e.2 :=
    (convex_segment e.1 e.2).segment_subset hpseg ha
  exact ⟨f t, (hF e he).2.2.2 (hsub htseg), hball htball, htv⟩

/-- A generic point on the genuine OLD-labelled single-component union boundary. -/
private theorem labelled_single_union_generic_boundary
    (K : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (hne : Nonempty (SingleIndex K T ψ))
    (hproper : singleClosedUnion K T ψ ≠ Set.univ) :
    ∃ (i : SingleIndex K T ψ) (p : Plane),
      p ∈ frontier (singleClosedUnion K T ψ) ∧
      p ∈ frontier (closedComponent K T ψ i) ∧
      p ∈ frontier (ψ i.1.1 +ᵥ K.support) ∧
      p ∉ ψ i.1.1 +ᵥ Tiling.vertexSet K.support ∧
      Tiling.BoundaryLocallyStraightAt (singleClosedUnion K T ψ) p := by
  classical
  let C := singleClosedUnion K T ψ
  have hlf := labelled_single_component_closures_locallyFinite K T ψ
  have hclosed : IsClosed C := hlf.isClosed_iUnion fun i => (component_polygonal K T ψ i).isClosed
  have hCne : C.Nonempty := by
    obtain ⟨i⟩ := hne
    obtain ⟨x, hx⟩ := single_interior_nonempty K T ψ i
    exact ⟨x, Set.mem_iUnion.mpr ⟨i, (vadd_set_mono subset_closure) hx⟩⟩
  have hfrontne : (frontier C).Nonempty := by
    by_contra h
    rcases frontier_eq_empty_iff.mp (Set.not_nonempty_iff_eq_empty.mp h) with he | hu
    · exact hCne.ne_empty he
    · exact hproper hu
  obtain ⟨x, hx⟩ := hfrontne
  obtain ⟨U, hUx, hfinite⟩ := hlf x
  let J : Set (SingleIndex K T ψ) :=
    {i | (closedComponent K T ψ i ∩ U).Nonempty}
  have hJ : J.Finite := hfinite
  haveI : Fintype J := hJ.fintype
  let D : Set Plane := ⋃ i : J, closedComponent K T ψ i.1
  have hD : IsPolygonal D := by
    let τ : ∀ i : J, Triangulation (closedComponent K T ψ i.1) :=
      fun i => (component_polygonal K T ψ i.1).some
    refine ⟨Triangulation.finiteUnion τ ?_⟩
    intro i j hij
    exact closed_components_aedisjoint K T ψ (fun h => hij (Subtype.ext h))
  have heq : C =ᶠ[𝓝 x] D := by
    filter_upwards [hUx] with y hyU
    apply propext
    constructor
    · intro hy
      obtain ⟨i, hiy⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨⟨i, ⟨y, hiy, hyU⟩⟩, hiy⟩
    · intro hy
      obtain ⟨i, hiy⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨i.1, hiy⟩
  have hfeq := frontier_eventuallyEq_of_closed hclosed hD.isClosed heq
  have hxD : x ∈ frontier D := Eq.mp (hfeq.self_of_nhds) hx
  let V : Set Plane := vertexSet D ∪
    ⋃ i : J, ψ i.1.1.1 +ᵥ vertexSet K.support
  have hV : V.Finite := hD.vertexSet_finite.union
    (Set.finite_iUnion fun i : J => K.isPolygonal.vertexSet_finite.image (ψ i.1.1.1 +ᵥ ·))
  obtain ⟨p, hpD, hpN, hpV⟩ :=
    polygonal_frontier_near_avoiding hD hV hxD (hfeq.eventually_nhds.and hfeq)
  have hpC : p ∈ frontier C := Eq.mpr hpN.2 hpD
  have hpnotD : p ∉ vertexSet D := fun h => hpV (Or.inl h)
  have hpstraightD := hD.boundaryLocallyStraightAt_of_not_mem_vertexSet hpD hpnotD
  have hpstraightC : BoundaryLocallyStraightAt C p := by
    obtain ⟨L, hpL, hdim, hgerm⟩ := hpstraightD
    refine ⟨L, hpL, hdim, ?_⟩
    filter_upwards [hpN.1, hgerm] with y hy hyL
    exact (iff_of_eq hy).trans hyL
  have hpDmem : p ∈ D := hD.isClosed.frontier_subset hpD
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpDmem
  have hpcomp : p ∈ frontier (closedComponent K T ψ i.1) := by
    rw [(component_polygonal K T ψ i.1).isClosed.frontier_eq]
    refine ⟨hpi, ?_⟩
    intro hpint
    exact Set.disjoint_left.mp disjoint_interior_frontier
      (interior_mono (Set.subset_iUnion _ i) hpint) hpD
  have hpfull : p ∈ frontier (ψ i.1.1.1 +ᵥ K.support) := by
    change p ∈ frontier (ψ i.1.1.1 +ᵥ closure i.1.1.2.1) at hpcomp
    rw [frontier, closure_vadd, interior_vadd] at hpcomp ⊢
    simp only [Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem] at hpcomp ⊢
    exact K.isPolygonal.interiorComponent_frontier_subset i.1.1.2.2 hpcomp
  have hpnotfull : p ∉ ψ i.1.1.1 +ᵥ vertexSet K.support := by
    intro h
    exact hpV (Or.inr (Set.mem_iUnion.mpr ⟨i, h⟩))
  exact ⟨i.1, p, hpC, hpcomp, hpfull, hpnotfull, hpstraightC⟩

end PackingSolSingleFamily

private theorem packingSol_actualSingleComponent_index
    (Kφ : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (t : Plane) (ht : t ∈ T) (x : Plane) (hx : x ∈ ψ t +ᵥ Kφ.openCarrier)
    (hsingle : ∀ s ∈ T, s ≠ t →
      Disjoint (connectedComponentIn (ψ t +ᵥ Kφ.openCarrier) x)
        (ψ s +ᵥ Kφ.openCarrier)) :
    ∃ i : PackingSolSingleFamily.SingleIndex Kφ T ψ,
      (i.1.1 : Plane) = t ∧
      ψ t +ᵥ i.1.2.1 = connectedComponentIn (ψ t +ᵥ Kφ.openCarrier) x := by
  let x₀ : Plane := -ψ t +ᵥ x
  have hx₀ : x₀ ∈ Kφ.openCarrier := Set.mem_vadd_set_iff_neg_vadd_mem.mp hx
  let C := connectedComponentIn Kφ.openCarrier x₀
  have hC : C ∈ Tiling.interiorComponents Kφ.support := ⟨x₀, hx₀, rfl⟩
  have hxx : ψ t +ᵥ x₀ = x := by
    dsimp only [x₀]
    simp only [vadd_vadd, add_neg_cancel, zero_vadd]
  have htranslated : ψ t +ᵥ C = connectedComponentIn (ψ t +ᵥ Kφ.openCarrier) x := by
    simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd, hxx] using
      (Homeomorph.addLeft (ψ t)).image_connectedComponentIn hx₀
  let tc : T × PackingSolSingleFamily.Component Kφ := (⟨t, ht⟩, ⟨C, hC⟩)
  have htc : ∀ s ∈ T, s ≠ (tc.1 : Plane) →
      Disjoint (ψ tc.1 +ᵥ tc.2.1) (ψ s +ᵥ Kφ.openCarrier) := by
    intro s hs hst
    change Disjoint (ψ t +ᵥ C) (ψ s +ᵥ Kφ.openCarrier)
    rw [htranslated]
    exact hsingle s hs hst
  exact ⟨⟨tc, htc⟩, rfl, htranslated⟩


/-- The actual OLD-labelled indexed open components are exactly the single
open union; local finiteness then identifies its closure with the closed union. -/
private theorem packingSol_singleClosedUnion_eq_closure
    (Kφ : PolygonalRegion) (T : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ) :
    PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ) =
      closure (packingSol_singleOpenUnion Kφ T φ) := by
  let I := PackingSolSingleFamily.SingleIndex Kφ T (deformPoint φ)
  have hopenEq : (⋃ i : I, deformPoint φ i.1.1 +ᵥ i.1.2.1) =
      packingSol_singleOpenUnion Kφ T φ := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
      obtain ⟨x₀, hx₀, hcomponent⟩ := i.1.2.2
      let x : Plane := deformPoint φ i.1.1 +ᵥ x₀
      have hx : x ∈ deformPoint φ i.1.1 +ᵥ Kφ.openCarrier :=
        Set.mem_vadd_set.mpr ⟨x₀, hx₀, rfl⟩
      have htranslated : deformPoint φ i.1.1 +ᵥ i.1.2.1 =
          connectedComponentIn (deformPoint φ i.1.1 +ᵥ Kφ.openCarrier) x := by
        rw [hcomponent]
        simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd,
          x, PolygonalRegion.openCarrier] using
          (Homeomorph.addLeft (deformPoint φ i.1.1)).image_connectedComponentIn hx₀
      refine ⟨i.1.1, i.1.1.2, x, hx, htranslated ▸ hyi, ?_⟩
      intro s hs hst
      rw [← htranslated]
      exact i.2 s hs hst
    · rintro ⟨t, ht, x, hx, hy, hsingle⟩
      obtain ⟨i, hiLabel, hiComponent⟩ :=
        packingSol_actualSingleComponent_index Kφ T (deformPoint φ) t ht x hx hsingle
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [hiLabel, hiComponent]
      exact hy
  have hlf : LocallyFinite (fun i : I => deformPoint φ i.1.1 +ᵥ i.1.2.1) :=
    (PackingSolSingleFamily.labelled_single_component_closures_locallyFinite Kφ T
      (deformPoint φ)).subset (fun i => vadd_set_mono subset_closure)
  rw [← hopenEq, hlf.closure_iUnion]
  simp only [closure_vadd, PackingSolSingleFamily.singleClosedUnion,
    PackingSolSingleFamily.closedComponent]
  rfl

/-- A genuine single component and failure of density instantiate the terminal
boundary constructor, retaining its actual OLD label and full-copy vertices. -/
private theorem packingSol_notDense_actualSingleBoundary
    (Kφ : PolygonalRegion) (T : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ)
    (t : Plane) (ht : t ∈ T) (x : Plane) (hx : x ∈ deformPoint φ t +ᵥ Kφ.openCarrier)
    (hsingle : ∀ s ∈ T, s ≠ t →
      Disjoint (connectedComponentIn (deformPoint φ t +ᵥ Kφ.openCarrier) x)
        (deformPoint φ s +ᵥ Kφ.openCarrier))
    (hnotDense : ¬Dense (packingSol_singleOpenUnion Kφ T φ)) :
    ∃ (i : PackingSolSingleFamily.SingleIndex Kφ T (deformPoint φ)) (p : Plane),
      p ∈ frontier (PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ)) ∧
      p ∈ frontier (PackingSolSingleFamily.closedComponent Kφ T (deformPoint φ) i) ∧
      p ∈ frontier (deformPoint φ i.1.1 +ᵥ Kφ.support) ∧
      p ∉ deformPoint φ i.1.1 +ᵥ Tiling.vertexSet Kφ.support ∧
      Tiling.BoundaryLocallyStraightAt
        (PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ)) p := by
  obtain ⟨i, _, _⟩ :=
    packingSol_actualSingleComponent_index Kφ T (deformPoint φ) t ht x hx hsingle
  have hproper : PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ) ≠ Set.univ := by
    intro h
    rw [packingSol_singleClosedUnion_eq_closure] at h
    exact hnotDense (dense_iff_closure_eq.mpr h)
  exact PackingSolSingleFamily.labelled_single_union_generic_boundary Kφ T (deformPoint φ)
    ⟨i⟩ hproper


/-- The terminal implication reuses the already checked actual dense-single
packing reduction, rather than constructing a second boundary argument. -/
private theorem packingSol_singleClosedUnion_univ_labelledDisjoint
    (Kφ : PolygonalRegion) (T : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ)
    (hcover : PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ) = Set.univ) :
    ∀ s ∈ T, ∀ t ∈ T, s ≠ t →
      Disjoint (deformPoint φ s +ᵥ Kφ.openCarrier)
        (deformPoint φ t +ᵥ Kφ.openCarrier) := by
  rw [packingSol_singleClosedUnion_eq_closure] at hcover
  exact packingSol_denseSingle_forces_labelledDisjoint Kφ T φ
    (dense_iff_closure_eq.mpr hcover)




private theorem packingSol_scalarLevels_isClosed (V : Set ℝ)
    (hfinite : ∀ Q : Set ℝ, Bornology.IsBounded Q → (V ∩ Q).Finite) :
    IsClosed V := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro x hx
  have hF : (V ∩ Metric.closedBall x 1).Finite :=
    hfinite _ Metric.isBounded_closedBall
  have hxF : x ∈ (V ∩ Metric.closedBall x 1)ᶜ := fun h => hx h.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hF.isClosed.isOpen_compl x hxF
  refine ⟨min r 1, lt_min hr (by norm_num), ?_⟩
  intro y hy hyV
  have hyr : y ∈ Metric.ball x r :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hy).trans_le (min_le_left _ _))
  have hyone : y ∈ Metric.closedBall x 1 :=
    Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hy).trans_le (min_le_right _ _)).le
  exact hball hyr ⟨hyV, hyone⟩

/-- Local exclusion on the selected normal level combines with normal-level
local finiteness to exclude every vertex in a genuine smaller ball. -/
private theorem packingSol_parallelPatch_vertexFreeBall
    (V : Set Plane) (n : RationalNormal)
    (hlevels : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      ((normalEval n '' V) ∩ Q).Finite)
    (p : Plane) (R : ℝ) (hR : 0 < R)
    (hpatch : ∀ z ∈ Metric.ball p R,
      normalEval n z = normalEval n p → z ∉ V) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ Disjoint (Metric.ball p r) V := by
  let L : Set ℝ := (normalEval n '' V) \ {normalEval n p}
  have hLfinite : ∀ Q : Set ℝ, Bornology.IsBounded Q → (L ∩ Q).Finite := by
    intro Q hQ
    exact (hlevels Q hQ).subset (fun _ h => ⟨h.1.1, h.2⟩)
  have hLclosed : IsClosed L := packingSol_scalarLevels_isClosed L hLfinite
  have hpnot : normalEval n p ∉ L := by simp [L]
  have hopen : IsOpen ((normalCLM n) ⁻¹' Lᶜ) :=
    hLclosed.isOpen_compl.preimage (normalCLM n).continuous
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hopen p hpnot
  refine ⟨min r₀ R, lt_min hr₀ hR, min_le_right _ _, Set.disjoint_left.mpr ?_⟩
  intro z hz hzV
  have hzr₀ : z ∈ Metric.ball p r₀ :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_left _ _))
  have hzR : z ∈ Metric.ball p R :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_right _ _))
  by_cases hzero : normalEval n z = normalEval n p
  · exact hpatch z hzR hzero hzV
  · exact hball hzr₀ ⟨Set.mem_image_of_mem _ hzV, by
      simpa only [Set.mem_singleton_iff, normalCLM_apply] using hzero⟩

/-- All approximation controls are fixed before the queried parallel patch.
Only the actual equal-level local exclusion remains a geometric caller input. -/
private theorem packingSol_uniformParallelPatch_vertexFreeBall
    (K : PolygonalRegion) (T : Set Plane) (n : RationalNormal)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a : Plane) (ha : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ p : Plane, ∀ R : ℝ, 0 < R →
          (∀ z ∈ Metric.ball p R, normalEval n z = normalEval n p →
            z ∉ deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T) →
          ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
            Disjoint (Metric.ball p r)
              (deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T) := by
  obtain ⟨F, ε, hε, hlevels⟩ :=
    properLink_imageNormalLevels_locallyFinite K T n hrat htile a ha
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ p R hR hpatch
  exact packingSol_parallelPatch_vertexFreeBall
    (deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T)
    n (hlevels φ hφ) p R hR hpatch


private theorem packingSol_oneSignedChain_deformation
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (E : Finset (Plane × Plane))
    (hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧
      e.1 ∈ Tiling.vertexSet K.support ∧ e.2 ∈ Tiling.vertexSet K.support ∧
      ∀ p ∈ openSegment ℝ e.1 e.2, p ∉ Tiling.vertexSet K.support)
    (a d : Plane) (hd : d ≠ 0) (positive : Bool)
    (hcover : (⋃ q : signedCarrierIntervals K T E a d positive,
      Icc q.1.1 q.1.2) = Set.univ) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        (∀ u ∈ scalarIntervalEndpoints (signedCarrierIntervals K T E a d positive),
          ∀ v ∈ scalarIntervalEndpoints (signedCarrierIntervals K T E a d positive),
          u < v → (v - u) / 2 ≤ (φ v : ℝ) - (φ u : ℝ) ∧
            (φ v : ℝ) - (φ u : ℝ) ≤ 2 * (v - u)) ∧
        (∀ Q : Set ℝ, Bornology.IsBounded Q →
          (((fun r : ℝ => (φ r : ℝ)) '' scalarIntervalEndpoints
            (signedCarrierIntervals K T E a d positive)) ∩ Q).Finite) ∧
        ((⋃ q : signedCarrierIntervals K T E a d positive,
          Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ)) = Set.univ) ∧
        (∀ q ∈ signedCarrierIntervals K T E a d positive,
          ∀ r ∈ signedCarrierIntervals K T E a d positive, q ≠ r →
            Disjoint (Ioo (φ q.1 : ℝ) (φ q.2 : ℝ))
              (Ioo (φ r.1 : ℝ) (φ r.2 : ℝ))) := by
  let A := signedCarrierIntervals K T E a d positive
  let S := scalarIntervalEndpoints A
  have hvertices : ∀ e ∈ E, e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support := fun e he =>
    ⟨(hprimitive e he).2.1, (hprimitive e he).2.2.1⟩
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite :=
    signedCarrierIntervals_sourceEndpoints_locallyFinite K T hpack E hvertices a d hd positive
  have hpositive : ∀ q ∈ A, q.1 < q.2 := fun q hq => hq.1
  have hdisjoint : ∀ q ∈ A, ∀ r ∈ A, q ≠ r →
      Disjoint (Ioo q.1 q.2) (Ioo r.1 r.2) :=
    signedCarrierIntervals_sameSide_disjoint K T hpack E hprimitive a d hd positive
  have hcoverPoint : ∀ x : ℝ, ∃ q ∈ A, x ∈ Icc q.1 q.2 := by
    intro x
    have hx : x ∈ ⋃ q : A, Icc q.1.1 q.1.2 := hcover ▸ Set.mem_univ x
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    exact ⟨q.1, q.2, hxq⟩
  obtain ⟨D, hDpositive, hDEdge⟩ :=
    signedCarrierIntervals_finitePositiveGapAlphabet K T E a d hd positive
  have hgap : ∀ u ∈ S, ∀ v ∈ S, u < v → S ∩ Ioo u v = ∅ → v - u ∈ D := by
    intro u hu v hv huv hconsecutive
    have huvA : (u, v) ∈ A := scalarIntervalFamily_consecutive_edge A hpositive
      hdisjoint hcoverPoint u v hu hv huv (by
        intro x hx hbetween
        have h : x ∈ S ∩ Ioo u v := ⟨hx, hbetween⟩
        rw [hconsecutive] at h
        exact h)
    exact hDEdge (u, v) huvA
  obtain ⟨ε₀, hε₀, horder⟩ := scalarChain_globalEndpointControl S D hlocal hgap
  obtain ⟨ε₁, hε₁, hLF⟩ := scalarChain_imageEndpoints_locallyFinite S D hlocal hgap
  obtain ⟨hleft, hright⟩ := scalarIntervalFamily_endpoints_cofinal A hcoverPoint
  obtain ⟨ε₂, hε₂, hcoverMapped⟩ :=
    scalarChain_deformedConsecutive_cover S D hlocal hgap hleft hright
  refine ⟨D, min ε₀ (min ε₁ ε₂), lt_min hε₀ (lt_min hε₁ hε₂), ?_⟩
  intro φ hφ
  have hφ₀ : IsFiniteApproximation D ε₀ φ :=
    ⟨hφ.1, fun r hr => (hφ.2 r hr).trans_le (min_le_left _ _)⟩
  have hφ₁ : IsFiniteApproximation D ε₁ φ :=
    ⟨hφ.1, fun r hr => (hφ.2 r hr).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hφ₂ : IsFiniteApproximation D ε₂ φ :=
    ⟨hφ.1, fun r hr => (hφ.2 r hr).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hweak : ∀ u ∈ S, ∀ v ∈ S, u ≤ v → (φ u : ℝ) ≤ (φ v : ℝ) := by
    intro u hu v hv huv
    rcases lt_or_eq_of_le huv with huv | rfl
    · have h := (horder φ hφ₀ u hu v hv huv).1
      linarith
    · exact le_rfl
  refine ⟨horder φ hφ₀, hLF φ hφ₁, ?_, ?_⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨u, hu, v, hv, huv, hconsecutive, hlow, hhigh⟩ := hcoverMapped φ hφ₂ x
    have huvA : (u, v) ∈ A := scalarIntervalFamily_consecutive_edge A hpositive
      hdisjoint hcoverPoint u v hu hv huv (by
        intro y hy hbetween
        have h : y ∈ S ∩ Ioo u v := ⟨hy, hbetween⟩
        rw [hconsecutive] at h
        exact h)
    exact Set.mem_iUnion.mpr ⟨⟨(u, v), huvA⟩, hlow, hhigh⟩
  · intro q hq r hr hqr
    have hqlo : q.1 ∈ S := ⟨q, hq, Or.inl rfl⟩
    have hqhi : q.2 ∈ S := ⟨q, hq, Or.inr rfl⟩
    have hrlo : r.1 ∈ S := ⟨r, hr, Or.inl rfl⟩
    have hrhi : r.2 ∈ S := ⟨r, hr, Or.inr rfl⟩
    apply Set.disjoint_left.mpr
    intro x hxq hxr
    rcases lt_trichotomy q.1 r.1 with hlt | heq | hgt
    · have hright : q.2 ≤ r.1 := by
        by_contra h
        exact scalarIntervalFamily_endpoint_notInterior A hpositive hdisjoint q hq r.1 hrlo
          ⟨hlt, lt_of_not_ge h⟩
      have htarget := hweak q.2 hqhi r.1 hrlo hright
      linarith [hxq.2, hxr.1]
    · have hsmall : q.1 < min q.2 r.2 :=
        lt_min (hpositive q hq) (by simpa only [heq] using hpositive r hr)
      obtain ⟨y, hylo, hyhi⟩ := exists_between hsmall
      exact Set.disjoint_left.mp (hdisjoint q hq r hr hqr)
        ⟨hylo, hyhi.trans_le (min_le_left _ _)⟩
        ⟨by simpa only [heq] using hylo, hyhi.trans_le (min_le_right _ _)⟩
    · have hright : r.2 ≤ q.1 := by
        by_contra h
        exact scalarIntervalFamily_endpoint_notInterior A hpositive hdisjoint r hr q.1 hqlo
          ⟨hgt, lt_of_not_ge h⟩
      have htarget := hweak r.2 hrhi q.1 hqlo hright
      linarith [hxr.2, hxq.1]


private theorem packingSol_sourceVertex_signedEndpoint
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (δ : Submodule ℝ Plane) (a d : Plane) (hd : d ∈ δ) (hdne : d ≠ 0)
    (hproper : Tiling.RationalSlopes.IsProperLink K δ T a)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (r : ℝ) (hvertex : a + r • d ∈ Tiling.RationalSlopes.translatedVertices K T) :
    ∃ positive : Bool, r ∈ scalarIntervalEndpoints
      (signedCarrierIntervals K T E a d positive) := by
  classical
  let p := a + r • d
  have hp : p ∈ a +ᵥ (δ : Set Plane) :=
    Set.mem_vadd_set.mpr ⟨r • d, δ.smul_mem r hd, rfl⟩
  obtain ⟨s, hs, hps, R, hR, hray⟩ :=
    sourceVertexRay_actual K P T hP htile δ a p d hproper hp hd hdne hvertex
  let v : Plane := -s + p
  have hv : v ∈ Tiling.vertexSet K.support :=
    Set.mem_vadd_set_iff_neg_vadd_mem.mp hps
  have hrayV : ∀ c : ℝ, 0 < c → c < R → v + c • d ∈ frontier K.support := by
    intro c hc hcR
    have hfront : p + c • d ∈ s +ᵥ frontier K.support := by
      have h := hray c hc hcR
      rw [frontier, closure_vadd, interior_vadd, ← Set.vadd_set_sdiff] at h
      exact h
    have h := Set.mem_vadd_set_iff_neg_vadd_mem.mp hfront
    simpa only [v, vadd_eq_add, add_assoc] using h
  obtain ⟨e, he, c, hc, hends⟩ := sourceRay_intrinsicEdge_positiveEndpoint K.isPolygonal
    hv hdne hR hrayV E (fun e he =>
      ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
        (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩) hcover
  have hcoords :
      (s + e.1 = a + r • d ∧ s + e.2 = a + (r + c) • d) ∨
      (s + e.2 = a + r • d ∧ s + e.1 = a + (r + c) • d) := by
    rcases hends with ⟨hleft, hright⟩ | ⟨hright, hleft⟩
    · left
      rw [hleft, hright]
      dsimp only [v, p]
      constructor <;> module
    · right
      rw [hleft, hright]
      dsimp only [v, p]
      constructor <;> module
  have hdirection : ∃ c' : ℝ, c' ≠ 0 ∧ e.2 - e.1 = c' • d := by
    rcases hends with ⟨hleft, hright⟩ | ⟨hright, hleft⟩
    · refine ⟨c, ne_of_gt hc, ?_⟩
      rw [hleft, hright]
      module
    · refine ⟨-c, neg_ne_zero.mpr (ne_of_gt hc), ?_⟩
      rw [hleft, hright]
      module
  obtain ⟨c', hc', hdir⟩ := hdirection
  have hproto := packingSol_constEdgeGerms_changeDirection K.support e.1 e.2 d
    (e.2 - e.1) c' hc' hdir (hE e he).2.2.2.2.2
  have htranslated (u : ℝ) (hu : u ∈ Ioo r (r + c)) :
      a + u • d ∈ s +ᵥ openSegment ℝ e.1 e.2 := by
    rw [vadd_openSegment]
    simp only [vadd_eq_add]
    rcases hcoords with ⟨hleft, hright⟩ | ⟨hright, hleft⟩
    · rw [hleft, hright]
      exact carrierParameter_mem_openSegment a d r (r + c) u (by linarith) hu
    · rw [hleft, hright, openSegment_symm]
      exact carrierParameter_mem_openSegment a d r (r + c) u (by linarith) hu
  rcases hproto with hpos | hneg
  · refine ⟨true, (r, r + c), ?_, Or.inl rfl⟩
    refine ⟨by linarith, s, hs, e, he, hcoords, ?_⟩
    intro u hu
    obtain ⟨z, hz, hzu⟩ := Set.mem_vadd_set.mp (htranslated u hu)
    have hzu' : s + z = a + u • d := by simpa only [vadd_eq_add] using hzu
    simpa only [hzu', if_true] using
      sourceRay_vadd_positiveEdgeGerm K.support s z d (hpos z hz)
  · refine ⟨false, (r, r + c), ?_, Or.inl rfl⟩
    refine ⟨by linarith, s, hs, e, he, hcoords, ?_⟩
    intro u hu
    obtain ⟨z, hz, hzu⟩ := Set.mem_vadd_set.mp (htranslated u hu)
    have hzu' : s + z = a + u • d := by simpa only [vadd_eq_add] using hzu
    simpa only [hzu', Bool.false_eq_true, if_false] using
      sourceRay_vadd_negativeEdgeGerm K.support s z d (hneg z hz)


private theorem packingSol_selectedLine_imageVertices_areSignedEndpoints
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane) (n : RationalNormal)
    (hP : polyhedralSupport P = K.support)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a : Plane) (hproper : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ v ∈ Tiling.RationalSlopes.translatedVertices K T,
          deformPoint φ v ∈ deformPoint φ a +ᵥ (normalDirection n : Set Plane) →
            ∃ positive : Bool, ∃ r ∈ scalarIntervalEndpoints
              (signedCarrierIntervals K T E a (packingSol_rationalTangent n) positive),
              deformPoint φ v = deformPoint φ a + (φ r : ℝ) • packingSol_rationalTangent n := by
  obtain ⟨F, ε, hε, hnormal⟩ := properLink_normalOrderControl K T n hrat htile
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ v hv hline
  let d := packingSol_rationalTangent n
  have hd : d ∈ normalDirection n := packingSol_rationalTangent_mem n
  have hdne : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  obtain ⟨z, hz, hzv⟩ := Set.mem_vadd_set.mp hline
  have hdeform : deformPoint φ (v - a) = z := by
    have hsub : deformPoint φ (v - a) = deformPoint φ v - deformPoint φ a :=
      (deformPointLinear φ).map_sub v a
    rw [hsub]
    change deformPoint φ v - deformPoint φ a = z
    change deformPoint φ a + z = deformPoint φ v at hzv
    rw [← hzv]
    abel
  have htargetzero : normalEval n (deformPoint φ (v - a)) = 0 := by
    rw [hdeform]
    exact (normalDirection_mem_iff n z).mp hz
  have hbound := (hnormal φ hφ a hproper v hv).2.1
  have hsourcezero : normalEval n (v - a) = 0 := by
    rw [htargetzero, abs_zero] at hbound
    apply abs_nonpos_iff.mp
    linarith
  have hspan : normalDirection n = Submodule.span ℝ ({d} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one (normalDirection_rational n).1 hd hdne
  have hvline : v - a ∈ Submodule.span ℝ ({d} : Set Plane) := by
    rw [← hspan]
    exact (normalDirection_mem_iff n _).mpr hsourcezero
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hvline
  have hvcoord : v = a + r • d := by rw [hr]; abel
  obtain ⟨positive, hrendpoint⟩ := packingSol_sourceVertex_signedEndpoint K P T hP htile
    (normalDirection n) a d hd hdne hproper E hE hcover r (hvcoord ▸ hv)
  refine ⟨positive, r, hrendpoint, ?_⟩
  rw [hvcoord]
  exact packingSol_deform_rationalCarrierParameter φ n a r


private theorem packingSol_actualFull_signedEndpointLF
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (δ : Submodule ℝ Plane) (a d : Plane) (hd : d ∈ δ) (hdne : d ≠ 0)
    (hproper : Tiling.RationalSlopes.IsProperLink K δ T a)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Q : Set ℝ, Bornology.IsBounded Q →
          (((fun r : ℝ => (φ r : ℝ)) ''
            (scalarIntervalEndpoints (signedCarrierIntervals K T E a d true) ∪
             scalarIntervalEndpoints (signedCarrierIntervals K T E a d false))) ∩ Q).Finite := by
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support := fun e he =>
    ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1, (hE e he).2.2.2.2.1⟩
  have hsource (positive : Bool) := signedCarrierIntervals_fullProper_closedCover K T htile
    δ a d hd hdne hproper E hE hcover positive
  obtain ⟨Fpos, εpos, hεpos, hpos⟩ := packingSol_oneSignedChain_deformation K T htile.2.1
    E hprimitive a d hdne true (hsource true)
  obtain ⟨Fneg, εneg, hεneg, hneg⟩ := packingSol_oneSignedChain_deformation K T htile.2.1
    E hprimitive a d hdne false (hsource false)
  refine ⟨Fpos ∪ Fneg, min εpos εneg, lt_min hεpos hεneg, ?_⟩
  intro φ hφ Q hQ
  have hφpos : IsFiniteApproximation Fpos εpos φ :=
    ⟨hφ.1, fun r hr => (hφ.2 r (Finset.mem_union_left _ hr)).trans_le (min_le_left _ _)⟩
  have hφneg : IsFiniteApproximation Fneg εneg φ :=
    ⟨hφ.1, fun r hr => (hφ.2 r (Finset.mem_union_right _ hr)).trans_le (min_le_right _ _)⟩
  have hfinite := ((hpos φ hφpos).2.1 Q hQ).union ((hneg φ hφneg).2.1 Q hQ)
  apply hfinite.subset
  rintro y ⟨⟨r, hr, rfl⟩, hyQ⟩
  rcases hr with hrpos | hrneg
  · exact Or.inl ⟨⟨r, hrpos, rfl⟩, hyQ⟩
  · exact Or.inr ⟨⟨r, hrneg, rfl⟩, hyQ⟩


private theorem packingSol_selectedLine_actualVertexFreeBall
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane) (n : RationalNormal)
    (hP : polyhedralSupport P = K.support)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a : Plane) (hproper : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∃ p ∈ deformPoint φ a +ᵥ (normalDirection n : Set Plane),
          ∃ r : ℝ, 0 < r ∧ Disjoint (Metric.ball p r)
            (deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T) := by
  let d := packingSol_rationalTangent n
  have hd : d ∈ normalDirection n := packingSol_rationalTangent_mem n
  have hdne : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  obtain ⟨F₀, ε₀, hε₀, hendpoint⟩ := packingSol_selectedLine_imageVertices_areSignedEndpoints
    K P T n hP hrat htile a hproper E hE hcover
  obtain ⟨F₁, ε₁, hε₁, hLF⟩ := packingSol_actualFull_signedEndpointLF K T htile
    (normalDirection n) a d hd hdne hproper E hE hcover
  obtain ⟨F₂, ε₂, g, hε₂, hg, hgap⟩ := properLink_imageVertexNormalGap K T n hrat htile
  refine ⟨F₀ ∪ (F₁ ∪ F₂), min ε₀ (min ε₁ ε₂), lt_min hε₀ (lt_min hε₁ hε₂), ?_⟩
  intro φ hφ
  have hφ₀ : IsFiniteApproximation F₀ ε₀ φ :=
    ⟨hφ.1, fun r hr => (hφ.2 r (Finset.mem_union_left _ hr)).trans_le (min_le_left _ _)⟩
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ :=
    ⟨hφ.1, fun r hr => (hφ.2 r (Finset.mem_union_right _ (Finset.mem_union_left _ hr))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ :=
    ⟨hφ.1, fun r hr => (hφ.2 r (Finset.mem_union_right _ (Finset.mem_union_right _ hr))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))⟩
  let Y : Set ℝ := (fun r : ℝ => (φ r : ℝ)) ''
    (scalarIntervalEndpoints (signedCarrierIntervals K T E a d true) ∪
     scalarIntervalEndpoints (signedCarrierIntervals K T E a d false))
  have hYlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (Y ∩ Q).Finite := hLF φ hφ₁
  have hYclosed : IsClosed Y := packingSol_scalarLevels_isClosed Y hYlocal
  obtain ⟨u, hu, huNot⟩ := (Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finite
    (hYlocal (Icc 0 1) isCompact_Icc.isBounded)
  have huY : u ∉ Y := fun h => huNot ⟨h, hu.1.le, hu.2.le⟩
  obtain ⟨m, hm⟩ := exists_positiveRationalCoordinateNormal d hdne
  let A := deformPoint φ a
  let τ : Plane → ℝ := fun z => normalEval m (z - A) / normalEval m d
  have hτcontinuous : Continuous τ := by
    have hc : Continuous (fun z : Plane => normalEval m (z - A)) := by
      exact (normalCLM m).continuous.comp (continuous_id.sub continuous_const)
    exact hc.div_const _
  have hτline (v : ℝ) : τ (A + v • d) = v := by
    dsimp only [τ]
    rw [add_sub_cancel_left, ← normalCLM_apply, map_smul, normalCLM_apply]
    change v * normalEval m d / normalEval m d = v
    exact mul_div_cancel_right₀ v (ne_of_gt hm)
  let p := A + u • d
  have hp : p ∈ A +ᵥ (normalDirection n : Set Plane) :=
    Set.mem_vadd_set.mpr ⟨u • d, (normalDirection n).smul_mem u hd, rfl⟩
  have hpτ : τ p ∉ Y := by rw [hτline]; exact huY
  obtain ⟨r₀, hr₀, hballτ⟩ := Metric.isOpen_iff.mp
    (hYclosed.preimage hτcontinuous).isOpen_compl p hpτ
  let ℓ : Plane → ℝ := fun z => normalEval n z - normalEval n A
  have hℓcontinuous : Continuous ℓ := (normalCLM n).continuous.sub continuous_const
  have hpℓ : ℓ p = 0 := by
    dsimp only [ℓ, p]
    rw [normalEval_add, (normalDirection_mem_iff n (u • d)).mp
      ((normalDirection n).smul_mem u hd)]
    ring
  have hgapOpen : IsOpen {z : Plane | |ℓ z| < g} :=
    isOpen_Iio.preimage hℓcontinuous.abs
  have hpGap : p ∈ {z : Plane | |ℓ z| < g} := by
    change |ℓ p| < g
    simpa only [hpℓ, abs_zero] using hg
  obtain ⟨r₁, hr₁, hballGap⟩ := Metric.isOpen_iff.mp hgapOpen p hpGap
  refine ⟨p, hp, min r₀ r₁, lt_min hr₀ hr₁, Set.disjoint_left.mpr ?_⟩
  intro z hz hvertex
  obtain ⟨v, hv, rfl⟩ := hvertex
  have hzτ : deformPoint φ v ∈ Metric.ball p r₀ :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_left _ _))
  have hzGap : deformPoint φ v ∈ Metric.ball p r₁ :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_right _ _))
  have hsmall : |normalEval n (deformPoint φ v) - normalEval n A| < g := hballGap hzGap
  have hzero : normalEval n (deformPoint φ v) = normalEval n A := by
    rcases hgap φ hφ₂ a hproper v hv with heq | hlarge
    · exact heq
    · exact False.elim ((not_lt_of_ge hlarge) hsmall)
  have hvline : deformPoint φ v ∈ A +ᵥ (normalDirection n : Set Plane) := by
    refine Set.mem_vadd_set.mpr ⟨deformPoint φ v - A, ?_, ?_⟩
    · apply (normalDirection_mem_iff n _).mpr
      rw [normalEval_sub, hzero, sub_self]
    · simp only [vadd_eq_add]
      abel
  obtain ⟨positive, s, hs, hvs⟩ := hendpoint φ hφ₀ v hv hvline
  have hsY : (φ s : ℝ) ∈ Y := by
    refine ⟨s, ?_, rfl⟩
    cases positive with
    | true => exact Or.inl hs
    | false => exact Or.inr hs
  have hτv : τ (deformPoint φ v) = (φ s : ℝ) := by rw [hvs]; exact hτline _
  apply hballτ hzτ
  change τ (deformPoint φ v) ∈ Y
  rwa [hτv]


private theorem packingSol_sameSourceSignedInterval_label
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements T))
    (a d s t : Plane) (hd : d ≠ 0) (hs : s ∈ T) (ht : t ∈ T)
    (q : ℝ × ℝ) (hq : q.1 < q.2) (positive : Bool)
    (hS : ∀ u ∈ Ioo q.1 q.2,
      if positive then positiveEdgeGerm (s +ᵥ K.support) d (a + u • d)
        else negativeEdgeGerm (s +ᵥ K.support) d (a + u • d))
    (hT : ∀ u ∈ Ioo q.1 q.2,
      if positive then positiveEdgeGerm (t +ᵥ K.support) d (a + u • d)
        else negativeEdgeGerm (t +ᵥ K.support) d (a + u • d)) : s = t := by
  obtain ⟨u, hu⟩ := exists_between hq
  cases positive with
  | true =>
    exact originalSamePositiveEdgeGerm_label_unique K T hpack s t (a + u • d) d hs ht hd
      (hS u hu) (hT u hu)
  | false =>
    exact originalSameNegativeEdgeGerm_label_unique K T hpack s t (a + u • d) d hs ht hd
      (hS u hu) (hT u hu)


private theorem packingSol_frontierFree_preconnected_copyInterior
    (Kφ : PolygonalRegion) (b : Plane) (U : Set Plane)
    (hU : IsPreconnected U)
    (hfrontier : Disjoint U (frontier (b +ᵥ Kφ.support)))
    (hmeet : (U ∩ (b +ᵥ Kφ.openCarrier)).Nonempty) :
    U ⊆ b +ᵥ Kφ.openCarrier := by
  apply hU.subset_of_closure_inter_subset (isOpen_interior.vadd _) hmeet
  intro y hy
  have hySupport : y ∈ b +ᵥ Kφ.support := by
    have hclosure : closure (b +ᵥ Kφ.openCarrier) = b +ᵥ Kφ.support := by
      rw [closure_vadd, PolygonalRegion.openCarrier, Kφ.isPolygonal.closure_interior]
    exact hclosure ▸ hy.1
  by_contra hyNot
  apply Set.disjoint_left.mp hfrontier hy.2
  rw [(Kφ.isPolygonal.isClosed.vadd b).frontier_eq, interior_vadd]
  exact ⟨hySupport, hyNot⟩


private theorem packingSol_exclusiveClosedWitness_singleComponent
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ t ∈ T, ∀ x ∈ deformPoint φ t +ᵥ Kφ.openCarrier,
      (∀ s ∈ T, s ≠ t → x ∉ deformPoint φ s +ᵥ Kφ.support) →
      ∀ s ∈ T, s ≠ t →
        Disjoint (connectedComponentIn (deformPoint φ t +ᵥ Kφ.openCarrier) x)
          (deformPoint φ s +ᵥ Kφ.openCarrier) := by
  obtain ⟨F, ε, hε, hpropagate⟩ :=
    deformation_componentOverlapPropagates K P T hP hrat htile
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ t ht x hx hexclusive s hs hst
  apply Set.disjoint_left.mpr
  intro y hyO hys
  have hcovered := hpropagate φ hφ Kφ hKφ t ht x hx
    (connectedComponentIn (deformPoint φ t +ᵥ Kφ.openCarrier) x) rfl
      ⟨s, hs, hst, y, hyO, hys⟩
  have hxOther := hcovered (mem_connectedComponentIn hx)
  obtain ⟨u, hxu⟩ := Set.mem_iUnion.mp hxOther
  exact hexclusive u.1 u.2.1 u.2.2 hxu


private theorem packingSol_selectedLine_vertexParameter_reflection
    (K : PolygonalRegion) (T : Set Plane) (n : RationalNormal)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a : Plane) (hproper : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ v ∈ Tiling.RationalSlopes.translatedVertices K T,
        deformPoint φ v ∈ deformPoint φ a +ᵥ (normalDirection n : Set Plane) →
        ∃ r : ℝ, v = a + r • packingSol_rationalTangent n ∧
          deformPoint φ v = deformPoint φ a + (φ r : ℝ) • packingSol_rationalTangent n := by
  obtain ⟨F, ε, hε, hnormal⟩ := properLink_normalOrderControl K T n hrat htile
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ v hv hline
  let d := packingSol_rationalTangent n
  have hd : d ∈ normalDirection n := packingSol_rationalTangent_mem n
  have hdne : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  obtain ⟨z, hz, hzv⟩ := Set.mem_vadd_set.mp hline
  have hdeform : deformPoint φ (v - a) = z := by
    have hsub : deformPoint φ (v - a) = deformPoint φ v - deformPoint φ a :=
      (deformPointLinear φ).map_sub v a
    rw [hsub]
    change deformPoint φ a + z = deformPoint φ v at hzv
    rw [← hzv]
    abel
  have htargetzero : normalEval n (deformPoint φ (v - a)) = 0 := by
    rw [hdeform]
    exact (normalDirection_mem_iff n z).mp hz
  have hbound := (hnormal φ hφ a hproper v hv).2.1
  have hsourcezero : normalEval n (v - a) = 0 := by
    rw [htargetzero, abs_zero] at hbound
    apply abs_nonpos_iff.mp
    linarith
  have hspan : normalDirection n = Submodule.span ℝ ({d} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one (normalDirection_rational n).1 hd hdne
  have hvline : v - a ∈ Submodule.span ℝ ({d} : Set Plane) := by
    rw [← hspan]
    exact (normalDirection_mem_iff n _).mpr hsourcezero
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hvline
  have hvcoord : v = a + r • d := by rw [hr]; abel
  refine ⟨r, hvcoord, ?_⟩
  rw [hvcoord]
  exact packingSol_deform_rationalCarrierParameter φ n a r


private theorem packingSol_selectedLine_primitiveSourceOccurrence
    (K : PolygonalRegion) (T : Set Plane) (n : RationalNormal)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a : Plane) (hproper : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z))) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ t ∈ T, ∀ e ∈ E,
      deformPoint φ t + deformPoint φ e.1 ∈
        deformPoint φ a +ᵥ (normalDirection n : Set Plane) →
      deformPoint φ t + deformPoint φ e.2 ∈
        deformPoint φ a +ᵥ (normalDirection n : Set Plane) →
      ∃ positive : Bool, ∃ q ∈ signedCarrierIntervals K T E a (packingSol_rationalTangent n) positive,
        ((t + e.1 = a + q.1 • packingSol_rationalTangent n ∧
          t + e.2 = a + q.2 • packingSol_rationalTangent n) ∨
         (t + e.2 = a + q.1 • packingSol_rationalTangent n ∧
          t + e.1 = a + q.2 • packingSol_rationalTangent n)) ∧
        ∀ u ∈ Ioo q.1 q.2,
          if positive then positiveEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
            (a + u • packingSol_rationalTangent n)
          else negativeEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
            (a + u • packingSol_rationalTangent n) := by
  obtain ⟨F, ε, hε, hreflect⟩ :=
    packingSol_selectedLine_vertexParameter_reflection K T n hrat htile a hproper
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ t ht e he hleftTarget hrightTarget
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hvertex (v : Plane) (hv : v ∈ Tiling.vertexSet K.support) :
      t + v ∈ Tiling.RationalSlopes.translatedVertices K T := by
    exact Set.mem_add.mpr ⟨v, hv, t, ht, add_comm v t⟩
  have hleftLine : deformPoint φ (t + e.1) ∈
      deformPoint φ a +ᵥ (normalDirection n : Set Plane) := by
    have hadd : deformPoint φ (t + e.1) = deformPoint φ t + deformPoint φ e.1 :=
      (deformPointLinear φ).map_add t e.1
    rw [hadd]
    exact hleftTarget
  have hrightLine : deformPoint φ (t + e.2) ∈
      deformPoint φ a +ᵥ (normalDirection n : Set Plane) := by
    have hadd : deformPoint φ (t + e.2) = deformPoint φ t + deformPoint φ e.2 :=
      (deformPointLinear φ).map_add t e.2
    rw [hadd]
    exact hrightTarget
  obtain ⟨α, hα, _⟩ := hreflect φ hφ (t + e.1) (hvertex e.1 (hE e he).2.1) hleftLine
  obtain ⟨β, hβ, _⟩ := hreflect φ hφ (t + e.2) (hvertex e.2 (hE e he).2.2.1) hrightLine
  have hαβ : α ≠ β := by
    intro heq
    have hEq : t + e.1 = t + e.2 := hα.trans (heq ▸ hβ.symm)
    exact (hE e he).1 (add_left_cancel hEq)
  rcases lt_or_gt_of_ne hαβ with hlt | hgt
  · have hcoords : (t + e.1 = a + α • d ∧ t + e.2 = a + β • d) ∨
        (t + e.2 = a + α • d ∧ t + e.1 = a + β • d) := Or.inl ⟨hα, hβ⟩
    obtain ⟨positive, hq, hgerm⟩ := packingSol_primitiveOccurrence_signedFamily K T E a d t hd
      ht e he (α, β) hlt hcoords (hE e he).2.2.2
    exact ⟨positive, (α, β), hq, hcoords, hgerm⟩
  · have hcoords : (t + e.1 = a + β • d ∧ t + e.2 = a + α • d) ∨
        (t + e.2 = a + β • d ∧ t + e.1 = a + α • d) := Or.inr ⟨hβ, hα⟩
    obtain ⟨positive, hq, hgerm⟩ := packingSol_primitiveOccurrence_signedFamily K T E a d t hd
      ht e he (β, α) hgt hcoords (hE e he).2.2.2
    exact ⟨positive, (β, α), hq, hcoords, hgerm⟩


private theorem edgeGerm_contradicts_transverseLine
    {S : Set Plane} {p q d : Plane} {ℓ : Plane →L[ℝ] ℝ}
    (havoid : Disjoint {z : Plane | ℓ (z - p) = 0} (interior S))
    (hq : ℓ (q - p) = 0) (hℓd : ℓ d ≠ 0)
    (hgerm : positiveEdgeGerm S d q ∨ negativeEdgeGerm S d q) : False := by
  let e := (ℓ d) • (d * Complex.I) - (ℓ (d * Complex.I)) • d
  have hd : d ≠ 0 := fun h => hℓd (by rw [h]; simp)
  have hnormSq : 0 < Complex.normSq d := Complex.normSq_pos.mpr hd
  have heker : ℓ e = 0 := by
    simp only [e, map_sub, map_smul, smul_eq_mul]
    ring
  have hside : Tiling.signedSide q d (q + e) = ℓ d * Complex.normSq d := by
    simp [Tiling.signedSide, Tiling.planarCross, e, Complex.normSq_apply,
      Complex.mul_I_re, Complex.mul_I_im]
    ring
  have hcont : Continuous (fun z : Plane => Tiling.signedSide q d z) := by
    fun_prop [Tiling.signedSide, Tiling.planarCross]
  rcases hgerm with hpos | hneg
  · obtain ⟨ρ, hρ, heq⟩ := hpos
    let v := if 0 < ℓ d then e else -e
    have hvker : ℓ v = 0 := by
      dsimp [v]
      split_ifs <;> simp [heker]
    have hvside : 0 < Tiling.signedSide q d (q + v) := by
      dsimp [v]
      split_ifs with hp
      · rw [hside]
        exact mul_pos hp hnormSq
      · have hn : ℓ d < 0 := by
          have hle : ℓ d ≤ 0 := le_of_not_gt hp
          by_contra hnot
          exact hℓd (le_antisymm hle (le_of_not_gt hnot))
        have hsideNeg : Tiling.signedSide q d (q - e) = -(ℓ d * Complex.normSq d) := by
          simp [Tiling.signedSide, Tiling.planarCross, e, Complex.normSq_apply]
          ring
        have hvalue : 0 < -(ℓ d * Complex.normSq d) :=
          neg_pos.mpr (mul_neg_of_neg_of_pos hn hnormSq)
        change 0 < Tiling.signedSide q d (q - e)
        rw [hsideNeg]
        exact hvalue
    let τ := ρ / (2 * (‖v‖ + 1))
    let y := q + τ • v
    have hτ : 0 < τ := by dsimp [τ]; positivity
    have hdist : dist y q < ρ := by
      have hmul : τ * ‖v‖ < ρ := by
        dsimp [τ]
        have hden : 0 < 2 * (‖v‖ + 1) := by positivity
        calc
          ρ / (2 * (‖v‖ + 1)) * ‖v‖ = ρ * ‖v‖ / (2 * (‖v‖ + 1)) := by ring
          _ < ρ := (div_lt_iff₀ hden).2 (by nlinarith [norm_nonneg v, hρ])
      have : dist y q = τ * ‖v‖ := by
        simp [y, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
      rw [this]
      exact hmul
    have hyline : ℓ (y - p) = 0 := by
      dsimp [y]
      change ℓ (q + τ • v - p) = 0
      rw [show q + τ • v - p = (q - p) + τ • v by module]
      rw [map_add]
      rw [hq, zero_add]
      change ℓ (τ • v) = 0
      rw [map_smul, hvker, smul_eq_mul]
      simp
    have hyside : 0 < Tiling.signedSide q d y := by
      dsimp [y]
      change 0 < Tiling.signedSide q d (q + τ • v)
      have hscale : Tiling.signedSide q d (q + τ • v) =
          τ * Tiling.signedSide q d (q + v) := by
        simp [Tiling.signedSide, Tiling.planarCross]
        ring
      rw [hscale]
      exact mul_pos hτ hvside
    have hypos : y ∈ Tiling.positiveSide q d := Tiling.mem_positiveSide.mpr hyside
    have hyball : y ∈ Metric.ball q ρ := Metric.mem_ball.mpr hdist
    have hposSet : Tiling.positiveSide q d = {z | 0 < Tiling.signedSide q d z} := by
      ext z
      exact Tiling.mem_positiveSide
    have hopen : IsOpen (Tiling.positiveSide q d ∩ Metric.ball q ρ) := by
      rw [hposSet]
      exact (isOpen_Ioi.preimage hcont).inter Metric.isOpen_ball
    have hsubset : Tiling.positiveSide q d ∩ Metric.ball q ρ ⊆ S := by
      intro z hz
      have hzhalf : z ∈ Tiling.positiveHalfPlane q d := by
        exact Tiling.mem_positiveHalfPlane.mpr (le_of_lt (Tiling.mem_positiveSide.mp hz.1))
      exact (Set.ext_iff.mp heq z).mpr ⟨hzhalf, hz.2⟩ |>.1
    have hyinterior : y ∈ interior S := interior_maximal hsubset hopen ⟨hypos, hyball⟩
    exact (Set.disjoint_left.mp havoid) hyline hyinterior
  · obtain ⟨ρ, hρ, heq⟩ := hneg
    let v := if 0 < ℓ d then -e else e
    have hvker : ℓ v = 0 := by
      dsimp [v]
      split_ifs <;> simp [heker]
    have hvside : Tiling.signedSide q d (q + v) < 0 := by
      dsimp [v]
      split_ifs with hp
      · have hp' : 0 < ℓ d := hp
        have hsideNeg : Tiling.signedSide q d (q - e) = -(ℓ d * Complex.normSq d) := by
          simp [Tiling.signedSide, Tiling.planarCross, e, Complex.normSq_apply]
          ring
        have hvalue : -(ℓ d * Complex.normSq d) < 0 :=
          neg_neg_of_pos (mul_pos hp' hnormSq)
        change Tiling.signedSide q d (q - e) < 0
        rw [hsideNeg]
        exact hvalue
      · have hn : ℓ d < 0 := by
          have hle : ℓ d ≤ 0 := le_of_not_gt hp
          by_contra hnot
          exact hℓd (le_antisymm hle (le_of_not_gt hnot))
        rw [hside]
        exact mul_neg_of_neg_of_pos hn hnormSq
    let τ := ρ / (2 * (‖v‖ + 1))
    let y := q + τ • v
    have hτ : 0 < τ := by dsimp [τ]; positivity
    have hdist : dist y q < ρ := by
      have hmul : τ * ‖v‖ < ρ := by
        dsimp [τ]
        have hden : 0 < 2 * (‖v‖ + 1) := by positivity
        calc
          ρ / (2 * (‖v‖ + 1)) * ‖v‖ = ρ * ‖v‖ / (2 * (‖v‖ + 1)) := by ring
          _ < ρ := (div_lt_iff₀ hden).2 (by nlinarith [norm_nonneg v, hρ])
      have : dist y q = τ * ‖v‖ := by
        simp [y, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
      rw [this]
      exact hmul
    have hyline : ℓ (y - p) = 0 := by
      dsimp [y]
      change ℓ (q + τ • v - p) = 0
      rw [show q + τ • v - p = (q - p) + τ • v by module]
      rw [map_add]
      rw [hq, zero_add]
      change ℓ (τ • v) = 0
      rw [map_smul, hvker, smul_eq_mul]
      simp
    have hyside : Tiling.signedSide q d y < 0 := by
      dsimp [y]
      change Tiling.signedSide q d (q + τ • v) < 0
      have hscale : Tiling.signedSide q d (q + τ • v) =
          τ * Tiling.signedSide q d (q + v) := by
        simp [Tiling.signedSide, Tiling.planarCross]
        ring
      rw [hscale]
      exact mul_neg_of_pos_of_neg hτ hvside
    have hyneg : y ∈ Tiling.negativeSide q d := Tiling.mem_negativeSide.mpr hyside
    have hyball : y ∈ Metric.ball q ρ := Metric.mem_ball.mpr hdist
    have hnegSet : Tiling.negativeSide q d = {z | Tiling.signedSide q d z < 0} := by
      ext z
      exact Tiling.mem_negativeSide
    have hopen : IsOpen (Tiling.negativeSide q d ∩ Metric.ball q ρ) := by
      rw [hnegSet]
      exact (isOpen_Iio.preimage hcont).inter Metric.isOpen_ball
    have hsubset : Tiling.negativeSide q d ∩ Metric.ball q ρ ⊆ S := by
      intro z hz
      have hzhalf : z ∈ Tiling.negativeHalfPlane q d := by
        exact Tiling.mem_negativeHalfPlane.mpr (le_of_lt (Tiling.mem_negativeSide.mp hz.1))
      exact (Set.ext_iff.mp heq z).mpr ⟨hzhalf, hz.2⟩ |>.1
    have hyinterior : y ∈ interior S := interior_maximal hsubset hopen ⟨hyneg, hyball⟩
    exact (Set.disjoint_left.mp havoid) hyline hyinterior


private theorem packingSol_finiteSlope_frontierExclusion
    (Kφ : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (E : Finset (Plane × Plane)) (W : Finset Plane) (V : Set Plane)
    (p : Plane) (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hfrontier : ∀ t ∈ T, frontier (ψ t +ᵥ Kφ.support) =
      ⋃ e ∈ E, segment ℝ (ψ t + ψ e.1) (ψ t + ψ e.2))
    (hendpoints : ∀ t ∈ T, ∀ e ∈ E,
      ψ t + ψ e.1 ∈ V ∧ ψ t + ψ e.2 ∈ V)
    (hdirections : ∀ e ∈ E, ∃ w ∈ W, ∃ c : ℝ, c ≠ 0 ∧
      ψ e.2 - ψ e.1 = c • w)
    (hgerms : ∀ t ∈ T, ∀ e ∈ E,
      ∀ z ∈ openSegment ℝ (ψ t + ψ e.1) (ψ t + ψ e.2),
        positiveEdgeGerm (ψ t +ᵥ Kφ.support) (ψ e.2 - ψ e.1) z ∨
        negativeEdgeGerm (ψ t +ᵥ Kφ.support) (ψ e.2 - ψ e.1) z)
    (havoid : ∀ t ∈ T, Disjoint {z : Plane | ℓ (z - p) = 0}
      (ψ t +ᵥ Kφ.openCarrier))
    (R : ℝ) (hR : 0 < R) (hvertex : Disjoint (Metric.ball p R) V)
    (g : ℝ) (hg : 0 < g)
    (hgap : ∀ v ∈ V, ℓ (v - p) = 0 ∨ g ≤ |ℓ (v - p)|) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∀ t ∈ T,
      frontier (ψ t +ᵥ Kφ.support) ∩ Metric.ball p r ⊆
        {z : Plane | ℓ (z - p) = 0} := by
  let C : ℝ := ∑ w ∈ W, if ℓ w = 0 then 0 else ‖w‖ / |ℓ w|
  have hC : 0 ≤ C := by
    dsimp [C]
    apply Finset.sum_nonneg
    intro w hw
    split_ifs <;> positivity
  have hratio (w : Plane) (hw : w ∈ W) (hℓw : ℓ w ≠ 0) :
      ‖w‖ / |ℓ w| ≤ C := by
    have hsum : (if ℓ w = 0 then 0 else ‖w‖ / |ℓ w|) ≤
        ∑ x ∈ W, if ℓ x = 0 then 0 else ‖x‖ / |ℓ x| :=
      Finset.single_le_sum (f := fun x => if ℓ x = 0 then 0 else ‖x‖ / |ℓ x|)
        (fun x hx => by
          split_ifs <;> positivity) hw
    simpa [C, hℓw] using hsum
  have hnormℓ : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
  let A : ℝ := 1 + ‖ℓ‖ * C
  have hA : 0 < A := by dsimp [A]; positivity
  have hAC : ‖ℓ‖ * C ≤ A := by dsimp [A]; linarith
  let r : ℝ := min (R / 2) (min (g / (2 * ‖ℓ‖)) (R / (4 * A)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r ≤ R := by
    dsimp [r]
    have : R / 2 ≤ R := by linarith
    exact (min_le_left _ _).trans this
  have hrhalf : r ≤ R / 2 := by dsimp [r]; exact min_le_left _ _
  have hrgap : r ≤ g / (2 * ‖ℓ‖) := by
    change min (R / 2) (min (g / (2 * ‖ℓ‖)) (R / (4 * A))) ≤
      g / (2 * ‖ℓ‖)
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hrtrans : r ≤ R / (4 * A) := by
    change min (R / 2) (min (g / (2 * ‖ℓ‖)) (R / (4 * A))) ≤ R / (4 * A)
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hsmallLine : ‖ℓ‖ * r ≤ g / 2 := by
    calc
      ‖ℓ‖ * r ≤ ‖ℓ‖ * (g / (2 * ‖ℓ‖)) :=
        mul_le_mul_of_nonneg_left hrgap (norm_nonneg _)
      _ = g / 2 := by field_simp [ne_of_gt hnormℓ]
  have hsmallSlope : ‖ℓ‖ * r * C ≤ R / 4 := by
    calc
      ‖ℓ‖ * r * C ≤ (‖ℓ‖ * (R / (4 * A))) * C := by
        gcongr
      _ = (‖ℓ‖ * C) * (R / (4 * A)) := by ring
      _ ≤ A * (R / (4 * A)) := by gcongr
      _ = R / 4 := by field_simp [ne_of_gt hA]
  refine ⟨r, hr, hrR, ?_⟩
  intro t ht z hz
  change ℓ (z - p) = 0
  by_contra hOff
  have hzfront : z ∈ frontier (ψ t +ᵥ Kφ.support) := hz.1
  have hzball : dist z p < r := Metric.mem_ball.mp hz.2
  have hzballR : z ∈ Metric.ball p R :=
    Metric.mem_ball.mpr (lt_of_lt_of_le hzball hrR)
  rw [hfrontier t ht] at hzfront
  rcases Set.mem_iUnion.mp hzfront with ⟨e, he⟩
  rcases Set.mem_iUnion.mp he with ⟨heE, hzseg⟩
  let a := ψ t + ψ e.1
  let b := ψ t + ψ e.2
  have hends := hendpoints t ht e heE
  have haout : a ∉ Metric.ball p R := by
    intro ha
    exact (Set.disjoint_left.mp hvertex) ha hends.1
  have hbout : b ∉ Metric.ball p R := by
    intro hb
    exact (Set.disjoint_left.mp hvertex) hb hends.2
  have haR : R ≤ dist a p := by
    by_contra h
    exact haout (Metric.mem_ball.mpr (lt_of_not_ge h))
  have hbR : R ≤ dist b p := by
    by_contra h
    exact hbout (Metric.mem_ball.mpr (lt_of_not_ge h))
  have hzseg' : z ∈ segment ℝ a b := by simpa [a, b] using hzseg
  have hab : a ≠ b := by
    intro hab
    have hza : z = a := by
      rw [segment_eq_image_lineMap] at hzseg'
      rcases hzseg' with ⟨u, hu, hzu⟩
      simpa [hab, AffineMap.lineMap_apply] using hzu.symm
    have haBall : a ∈ Metric.ball p R := by
      simpa [hza] using hzballR
    exact haout haBall
  rw [segment_eq_image_lineMap] at hzseg'
  rcases hzseg' with ⟨u, hu, hzu⟩
  have hu0 : 0 < u := by
    by_contra h
    have huEq : u = 0 := le_antisymm (le_of_not_gt h) hu.1
    have hza : z = a := by simpa [huEq, AffineMap.lineMap_apply] using hzu.symm
    have haBall : a ∈ Metric.ball p R := by simpa [hza] using hzballR
    exact haout haBall
  have hu1 : u < 1 := by
    by_contra h
    have huEq : u = 1 := le_antisymm hu.2 (le_of_not_gt h)
    have hzb : z = b := by simpa [huEq, AffineMap.lineMap_apply] using hzu.symm
    have hbBall : b ∈ Metric.ball p R := by simpa [hzb] using hzballR
    exact hbout hbBall
  have hzOpenSeg : z ∈ openSegment ℝ a b := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨u, ⟨hu0, hu1⟩, hzu⟩
  rcases hdirections e heE with ⟨w, hw, c, hc, hdEq⟩
  have hd : b - a = c • w := by
    dsimp [a, b]
    calc
      (ψ t + ψ e.2) - (ψ t + ψ e.1) = ψ e.2 - ψ e.1 := by abel
      _ = c • w := hdEq
  have hzrep : z - a = u • (b - a) := by
    rw [← hzu]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hzaDist : dist a z = u * ‖b - a‖ := by
    rw [dist_comm, dist_eq_norm, hzrep]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
  have hzbRep : z - b = (u - 1) • (b - a) := by
    rw [← hzu]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hzbDist : dist b z = (1 - u) * ‖b - a‖ := by
    rw [dist_comm, dist_eq_norm, hzbRep, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonpos (by linarith : u - 1 ≤ 0)]
    ring
  have hmarginA : R - r < dist a z := by
    have htri := dist_triangle a z p
    linarith
  have hmarginB : R - r < dist b z := by
    have htri := dist_triangle b z p
    linarith
  have hdnonzero : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hnormd : 0 < ‖b - a‖ := norm_pos_iff.mpr hdnonzero
  have habsℓ (x : Plane) : |ℓ x| ≤ ‖ℓ‖ * ‖x‖ := by
    simpa only [Real.norm_eq_abs] using ℓ.le_opNorm x
  by_cases hpar : ℓ (b - a) = 0
  · have hzval : ℓ (z - p) = ℓ (a - p) := by
      have hzdecomp : z - p = (a - p) + u • (b - a) := by
        rw [← hzrep]
        module
      rw [hzdecomp, map_add, map_smul, hpar]
      simp
    have haNonzero : ℓ (a - p) ≠ 0 := by
      intro hz0
      exact hOff (by rw [hzval, hz0])
    have hgA := hgap a hends.1
    have hgAbs : g ≤ |ℓ (z - p)| := by
      rcases hgA with hzero | hbound
      · exact False.elim (haNonzero (by simpa [hzval] using hzero))
      · simpa [hzval] using hbound
    have habsBound : |ℓ (z - p)| ≤ ‖ℓ‖ * dist z p := by
      simpa only [Real.norm_eq_abs, dist_eq_norm] using ℓ.le_opNorm (z - p)
    have : |ℓ (z - p)| < g := by
      calc
        |ℓ (z - p)| ≤ ‖ℓ‖ * dist z p := habsBound
        _ ≤ ‖ℓ‖ * r := mul_le_mul_of_nonneg_left hzball.le (norm_nonneg _)
        _ ≤ g / 2 := hsmallLine
        _ < g := by linarith
    linarith
  · have hℓw : ℓ w ≠ 0 := by
      intro hzero
      apply hpar
      rw [hd, map_smul, hzero]
      simp
    have hℓd : ℓ (b - a) ≠ 0 := by
      rw [hd, map_smul]
      exact mul_ne_zero hc hℓw
    let γ : ℝ := ℓ (a - p) / ℓ w
    let q : Plane := a - γ • w
    have hqline : ℓ (q - p) = 0 := by
      have hqrep : q - p = (a - p) - γ • w := by dsimp [q]; module
      rw [hqrep, map_sub, map_smul]
      dsimp [γ]
      field_simp [hℓw] <;> ring
    have hzdecomp : z - p = (a - p) + u • (b - a) := by
      rw [← hzrep]
      module
    have hzval : ℓ (z - p) = ℓ (a - p) + u * c * ℓ w := by
      rw [hzdecomp, map_add, map_smul, hd, map_smul]
      simp only [smul_eq_mul]
      ring
    have hcoeff : γ + u * c = ℓ (z - p) / ℓ w := by
      rw [hzval]
      dsimp [γ]
      field_simp [hℓw]
      <;> ring
    have hqzrep : q - z = -(γ + u * c) • w := by
      have hzaw : z - a = (u * c) • w := by
        rw [hzrep, hd, smul_smul]
      have hzAdd : z = a + (u * c) • w := by
        calc
          z = a + (z - a) := by module
          _ = a + (u * c) • w := by rw [hzaw]
      calc
        q - z = (a - γ • w) - (a + (u * c) • w) := by
          dsimp [q]
          rw [hzAdd]
          apply Complex.ext <;>
            simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
              Complex.smul_re, Complex.smul_im] <;> ring
        _ = (-γ - u * c) • w := by
          apply Complex.ext <;>
            simp [Complex.smul_re, Complex.smul_im] <;> ring
        _ = -(γ + u * c) • w := by congr 1; ring
    have hdistq : dist q z = |γ + u * c| * ‖w‖ := by
      calc
        dist q z = ‖q - z‖ := dist_eq_norm q z
        _ = ‖-(γ + u * c) • w‖ := by rw [hqzrep]
        _ = ‖-(γ + u * c)‖ * ‖w‖ := norm_smul _ _
        _ = |γ + u * c| * ‖w‖ := by
          rw [Real.norm_eq_abs, abs_neg]
    have hratio' : ‖w‖ / |ℓ w| ≤ C := hratio w hw hℓw
    have hAlphaNorm : |γ + u * c| * ‖w‖ ≤ ‖ℓ‖ * dist z p * C := by
      rw [show |γ + u * c| * ‖w‖ = |ℓ (z - p)| * (‖w‖ / |ℓ w|) by
        rw [hcoeff, abs_div]
        field_simp [hℓw]
        <;> ring]
      calc
        |ℓ (z - p)| * (‖w‖ / |ℓ w|) ≤ |ℓ (z - p)| * C :=
          mul_le_mul_of_nonneg_left hratio' (abs_nonneg _)
        _ ≤ (‖ℓ‖ * dist z p) * C :=
          mul_le_mul_of_nonneg_right
            (by simpa only [Real.norm_eq_abs, dist_eq_norm] using ℓ.le_opNorm (z - p)) hC
        _ = ‖ℓ‖ * dist z p * C := by ring
    have hdistqBound : dist q z ≤ R / 4 := by
      rw [hdistq]
      calc
        |γ + u * c| * ‖w‖ ≤ ‖ℓ‖ * dist z p * C := hAlphaNorm
        _ ≤ ‖ℓ‖ * r * C := by gcongr
        _ ≤ R / 4 := hsmallSlope
    have hdistqMargin : dist q z < R - r := by
      have hRmr : R / 2 ≤ R - r := by linarith [hrhalf]
      linarith
    have hbetaD (β : ℝ) :
      dist (AffineMap.lineMap a b β) z = |β - u| * ‖b - a‖ := by
      rw [dist_eq_norm, ← hzu]
      have hdiff : (AffineMap.lineMap a b β) - (AffineMap.lineMap a b u) =
          (β - u) • (b - a) := by
        simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
        module
      rw [hdiff, norm_smul, Real.norm_eq_abs]
    let β : ℝ := -γ / c
    have hqLineMap : q = AffineMap.lineMap a b β := by
      have hsc : β * c = -γ := by
        dsimp [β]
        field_simp [hc]
      change a - γ • w = AffineMap.lineMap a b β
      rw [AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add]
      change a - γ • w = β • (b - a) + a
      rw [hd, smul_smul, hsc]
      module
    have hbetaDist : |β - u| * ‖b - a‖ = dist q z := by
      calc
        |β - u| * ‖b - a‖ = dist (AffineMap.lineMap a b β) z := (hbetaD β).symm
        _ = dist q z := by rw [hqLineMap]
    have hbetaAbs : |β - u| < u := by
      have hmul : |β - u| * ‖b - a‖ < u * ‖b - a‖ := by
        calc
          |β - u| * ‖b - a‖ = dist q z := hbetaDist
          _ < dist a z := hdistqMargin.trans hmarginA
          _ = u * ‖b - a‖ := hzaDist
      by_contra hnot
      have hle : u ≤ |β - u| := le_of_not_gt hnot
      have hmul' := mul_le_mul_of_nonneg_right hle (le_of_lt hnormd)
      linarith
    have hbetaAbsRight : |β - u| < 1 - u := by
      have hmul : |β - u| * ‖b - a‖ < (1 - u) * ‖b - a‖ := by
        calc
          |β - u| * ‖b - a‖ = dist q z := hbetaDist
          _ < dist b z := hdistqMargin.trans hmarginB
          _ = (1 - u) * ‖b - a‖ := hzbDist
      by_contra hnot
      have hle : 1 - u ≤ |β - u| := le_of_not_gt hnot
      have hmul' := mul_le_mul_of_nonneg_right hle (le_of_lt hnormd)
      linarith
    have hβ0 : 0 < β := by linarith [neg_le_abs (β - u)]
    have hβ1 : β < 1 := by linarith [le_abs_self (β - u)]
    have hqOpenSeg : q ∈ openSegment ℝ a b := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨β, ⟨hβ0, hβ1⟩, hqLineMap.symm⟩
    have hdtranslate : b - a = ψ e.2 - ψ e.1 := by
      dsimp [a, b]
      abel
    have havoid' : Disjoint {z : Plane | ℓ (z - p) = 0}
        (interior (ψ t +ᵥ Kφ.support)) := by
      simpa [PolygonalRegion.openCarrier, interior_vadd] using havoid t ht
    rcases hgerms t ht e heE q hqOpenSeg with hpos | hneg
    · exact edgeGerm_contradicts_transverseLine havoid' hqline hℓd
        (Or.inl (by simpa [hdtranslate] using hpos))
    · exact edgeGerm_contradicts_transverseLine havoid' hqline hℓd
        (Or.inr (by simpa [hdtranslate] using hneg))


private theorem packingSol_selectedLine_actualFrontierFreeHalfBall
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane) (n : RationalNormal)
    (hP : polyhedralSupport P = K.support)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a : Plane) (hproper : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hratE : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
        ∃ p ∈ deformPoint φ a +ᵥ (normalDirection n : Set Plane), ∃ r : ℝ,
          0 < r ∧ Disjoint (Metric.ball p r)
            (deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T) ∧
          ∀ t ∈ T, frontier (deformPoint φ t +ᵥ Kφ.support) ∩ Metric.ball p r ⊆
            {z | normalEval n (z - p) = 0} := by
  classical
  obtain ⟨Fs, εs, hεs, hseed⟩ := packingSol_selectedLine_actualVertexFreeBall
    K P T n hP hrat htile a hproper E hE hcover
  obtain ⟨Fg, εg, g, hεg, hg, hgap⟩ := properLink_imageVertexNormalGap K T n hrat htile
  obtain ⟨Fa, εa, hεa, havoid⟩ :=
    properLink_deformedCarrier_avoidsLabelledInteriors K P T n hP hrat htile
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨Ft, εt, _, hεt, _, htransport⟩ :=
    rationalPrimitiveEdges_uniformSameSide_transport K P hP E hratE hprimitive hcover
  obtain ⟨Fc, εc, _, hεc, _, hscale⟩ := finiteRationalEdges_positiveHomotheties E hratE
  let F := Fs ∪ (Fg ∪ (Fa ∪ (Ft ∪ Fc)))
  let ε := min εs (min εg (min εa (min εt εc)))
  refine ⟨F, ε, lt_min hεs (lt_min hεg (lt_min hεa (lt_min hεt hεc))), ?_⟩
  intro φ hφ Kφ hKφ
  have hφs : IsFiniteApproximation Fs εs φ := by
    refine ⟨hφ.1, fun x hx => (hφ.2 x (Finset.mem_union_left _ hx)).trans_le ?_⟩
    exact min_le_left _ _
  have hφg : IsFiniteApproximation Fg εg φ := by
    refine ⟨hφ.1, fun x hx => (hφ.2 x
      (Finset.mem_union_right _ (Finset.mem_union_left _ hx))).trans_le ?_⟩
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hφa : IsFiniteApproximation Fa εa φ := by
    refine ⟨hφ.1, fun x hx => (hφ.2 x
      (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_left _ hx)))).trans_le ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hφt : IsFiniteApproximation Ft εt φ := by
    refine ⟨hφ.1, fun x hx => (hφ.2 x
      (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_union_left _ hx))))).trans_le ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hφc : IsFiniteApproximation Fc εc φ := by
    refine ⟨hφ.1, fun x hx => (hφ.2 x
      (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_union_right _ hx))))).trans_le ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨p, hp, R, hR, hvertex⟩ := hseed φ hφs
  obtain ⟨_, _, _, _, hfront, hgerms⟩ := htransport φ hφt Kφ hKφ
  let V := deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T
  have hpLevel : normalEval n p = normalEval n (deformPoint φ a) := by
    obtain ⟨d, hd, hdp⟩ := Set.mem_vadd_set.mp hp
    have hd0 := (normalDirection_mem_iff n d).mp hd
    simpa only [← hdp, vadd_eq_add, normalEval_add, hd0, add_zero]
  have hline : {z : Plane | normalCLM n (z - p) = 0} =
      deformPoint φ a +ᵥ (normalDirection n : Set Plane) := by
    ext z
    constructor
    · intro hz
      refine Set.mem_vadd_set.mpr ⟨z - deformPoint φ a, ?_, by simp⟩
      apply (normalDirection_mem_iff n _).mpr
      change normalEval n (z - p) = 0 at hz
      rw [normalEval_sub] at hz ⊢
      linarith
    · rintro ⟨d, hd, hdz⟩
      change normalEval n (z - p) = 0
      have hdz' : deformPoint φ a + d = z := hdz
      rw [← hdz', normalEval_sub, normalEval_add,
        (normalDirection_mem_iff n d).mp hd, hpLevel]
      ring
  have hends : ∀ t ∈ T, ∀ e ∈ E,
      deformPoint φ t + deformPoint φ e.1 ∈ V ∧
      deformPoint φ t + deformPoint φ e.2 ∈ V := by
    intro t ht e he
    have mapVertex (v : Plane) (hv : v ∈ Tiling.vertexSet K.support) :
        deformPoint φ t + deformPoint φ v ∈ V := by
      refine ⟨t + v, Set.mem_add.mpr ⟨v, hv, t, ht, add_comm v t⟩, ?_⟩
      exact (deformPointLinear φ).map_add t v
    exact ⟨mapVertex _ (hE e he).2.1, mapVertex _ (hE e he).2.2.1⟩
  have hfrontier : ∀ t ∈ T, frontier (deformPoint φ t +ᵥ Kφ.support) =
      ⋃ e ∈ E, segment ℝ (deformPoint φ t + deformPoint φ e.1)
        (deformPoint φ t + deformPoint φ e.2) := by
    intro t _
    rw [← sourceRay_link_frontier_vadd, hfront, Set.vadd_set_iUnion]
    simp only [Set.vadd_set_iUnion, vadd_segment, vadd_eq_add]
  have hdirs : ∀ e ∈ E, ∃ w ∈ E.image (fun e => e.2 - e.1), ∃ c : ℝ,
      c ≠ 0 ∧ deformPoint φ e.2 - deformPoint φ e.1 = c • w := by
    intro e he
    obtain ⟨c, hc, _, hvec, _⟩ := hscale φ hφc e he
    exact ⟨e.2 - e.1, Finset.mem_image.mpr ⟨e, he, rfl⟩, c,
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hc), hvec⟩
  have htargetGerms : ∀ t ∈ T, ∀ e ∈ E, ∀ z ∈
      openSegment ℝ (deformPoint φ t + deformPoint φ e.1)
        (deformPoint φ t + deformPoint φ e.2),
      positiveEdgeGerm (deformPoint φ t +ᵥ Kφ.support)
        (deformPoint φ e.2 - deformPoint φ e.1) z ∨
      negativeEdgeGerm (deformPoint φ t +ᵥ Kφ.support)
        (deformPoint φ e.2 - deformPoint φ e.1) z := by
    intro t _ e he z hz
    have hz' : z ∈ deformPoint φ t +ᵥ
        openSegment ℝ (deformPoint φ e.1) (deformPoint φ e.2) := by
      simpa only [vadd_openSegment, vadd_eq_add] using hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_vadd_set.mp hz'
    have hzx' : deformPoint φ t + x = z := hzx
    obtain ⟨c, hc, _, hvec, _⟩ := hscale φ hφc e he
    have hcpos : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hc
    rcases (hE e he).2.2.2.2.2 with hpos | hneg
    · left
      have hxg : positiveEdgeGerm Kφ.support (e.2 - e.1) x := by
        simpa only [hKφ] using (hgerms e he).1 hpos x hx
      have htranslated := sourceRay_vadd_positiveEdgeGerm Kφ.support
        (deformPoint φ t) x (e.2 - e.1) hxg
      rw [hvec]
      apply (positiveEdgeGerm_smul_pos_iff _ _ _ c hcpos).2
      simpa only [hzx'] using htranslated
    · right
      have hxg : negativeEdgeGerm Kφ.support (e.2 - e.1) x := by
        simpa only [hKφ] using (hgerms e he).2 hneg x hx
      have htranslated := sourceRay_vadd_negativeEdgeGerm Kφ.support
        (deformPoint φ t) x (e.2 - e.1) hxg
      rw [hvec]
      apply (negativeEdgeGerm_smul_pos_iff _ _ _ c hcpos).2
      simpa only [hzx'] using htranslated
  have hgap' : ∀ v ∈ V, normalCLM n (v - p) = 0 ∨ g ≤ |normalCLM n (v - p)| := by
    rintro v ⟨w, hw, rfl⟩
    simpa only [normalCLM_apply, normalEval_sub, hpLevel, sub_eq_zero] using
      hgap φ hφg a hproper w hw
  have havoid' : ∀ t ∈ T, Disjoint {z : Plane | normalCLM n (z - p) = 0}
      (deformPoint φ t +ᵥ Kφ.openCarrier) := by
    intro t ht
    rw [hline]
    exact havoid φ hφa Kφ hKφ a hproper t ht
  obtain ⟨r, hr, hrR, hresult⟩ := packingSol_finiteSlope_frontierExclusion
    Kφ T (deformPoint φ) E (E.image (fun e => e.2 - e.1)) V p (normalCLM n)
    (normalCLM_ne_zero n) hfrontier hends hdirs htargetGerms havoid' R hR hvertex g hg hgap'
  refine ⟨p, hp, r, hr, ?_, ?_⟩
  · exact hvertex.mono_left (Metric.ball_subset_ball hrR)
  · simpa only [normalCLM_apply] using hresult


private theorem packingSol_uniformActualProperCarrierTransport
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (d : Plane) (hdne : d ≠ 0) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ δ : Submodule ℝ Plane, d ∈ δ → ∀ a : Plane,
      Tiling.RationalSlopes.IsProperLink K δ T a → ∀ positive : Bool,
      let A := signedCarrierIntervals K T E a d positive
      (∀ x ∈ scalarIntervalEndpoints A, ∀ y ∈ scalarIntervalEndpoints A, x < y →
        (y - x) / 2 ≤ (φ y : ℝ) - (φ x : ℝ) ∧
          (φ y : ℝ) - (φ x : ℝ) ≤ 2 * (y - x)) ∧
      (∀ q ∈ A, ∀ s ∈ A, q ≠ s →
        Disjoint (Ioo (φ q.1 : ℝ) (φ q.2 : ℝ))
          (Ioo (φ s.1 : ℝ) (φ s.2 : ℝ))) ∧
      (⋃ q : A, Icc (φ q.1.1 : ℝ) (φ q.1.2 : ℝ)) = Set.univ := by
  obtain ⟨F, ε, hε, htransport⟩ :=
    packingSol_uniformActualSourceCarrierTransport K T htile E hE hcover d hdne
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ δ hd a hproper positive
  let B : Set ℝ := {s | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support}
  have hB : B = Set.univ := by
    apply Set.eq_univ_of_forall
    intro s
    exact hproper (Set.mem_vadd_set.mpr ⟨s • d, δ.smul_mem s hd, rfl⟩)
  have hJ : connectedComponentIn B (0 : ℝ) = Set.univ := by
    rw [hB]
    exact isPreconnected_univ.connectedComponentIn (Set.mem_univ _)
  have hA : signedCarrierComponentIntervals K T E a d 0 positive =
      signedCarrierIntervals K T E a d positive := by
    ext q
    change (q ∈ signedCarrierIntervals K T E a d positive ∧
      Icc q.1 q.2 ⊆ connectedComponentIn B 0) ↔ _
    rw [hJ]
    simp only [Set.subset_univ, and_true]
  have hresult := htransport φ hφ a 0 (-1) 1
    (show a + (0 : ℝ) • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support from
      hproper (Set.mem_vadd_set.mpr ⟨(0 : ℝ) • d, δ.smul_mem 0 hd, rfl⟩))
    (by norm_num) (by rw [hJ]; exact Set.subset_univ _) positive
  have hbound := hresult.2.1
  have hdisjoint := hresult.2.2.2.1
  have hclosedCover := hresult.2.2.2.2.2.2.2 hJ
  rw [hA] at hbound hdisjoint hclosedCover
  exact ⟨hbound, hdisjoint, hclosedCover⟩


private theorem packingSol_tangent_signedSide (n : RationalNormal) (p z : Plane) :
    Tiling.signedSide p (packingSol_rationalTangent n) z = -normalEval n (z - p) := by
  simp only [Tiling.signedSide, Tiling.planarCross, packingSol_rationalTangent,
    normalEval, Complex.sub_re, Complex.sub_im]
  ring


private theorem packingSol_positiveHalfBall_point (p d : Plane) (hd : d ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    ∃ x : Plane, x ∈ Metric.ball p R ∩ Tiling.positiveSide p d := by
  let c : ℝ := R / (2 * (‖d * Complex.I‖ + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨p + c • (d * Complex.I), ?_, Tiling.mem_positiveSide.mpr ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hc]
    dsimp [c]
    have hden : 0 < 2 * (‖d * Complex.I‖ + 1) := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [norm_nonneg (d * Complex.I)]
  · rw [Tiling.signedSide_add_smul_mul_I]
    exact mul_pos hc (Complex.normSq_pos.mpr hd)


private theorem packingSol_positiveHalfBall_center_closure
    (p d : Plane) (hd : d ≠ 0) (R : ℝ) (hR : 0 < R) :
    p ∈ closure (Metric.ball p R ∩ Tiling.positiveSide p d) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨x, hxball, hxside⟩ := packingSol_positiveHalfBall_point p d hd
    (min R ε) (lt_min hR hε)
  refine ⟨x, ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp hxball).trans_le
    (min_le_left _ _)), hxside⟩, ?_⟩
  rw [dist_comm]
  exact (Metric.mem_ball.mp hxball).trans_le (min_le_right _ _)


private theorem packingSol_openCarrierParameter_reflect
    (a d : Plane) (hd : d ≠ 0) (lo hi u : ℝ) (hlohi : lo < hi)
    (hp : a + u • d ∈ openSegment ℝ (a + lo • d) (a + hi • d)) :
    u ∈ Ioo lo hi := by
  obtain ⟨c, hc, hpc⟩ := exists_openSegment_lineMap_parameter
    (a + lo • d) (a + hi • d) (a + u • d) hp
  have hpc' : a + (lo + c * (hi - lo)) • d = a + u • d := by
    calc
      a + (lo + c * (hi - lo)) • d =
          AffineMap.lineMap (a + lo • d) (a + hi • d) c := by
        simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
        module
      _ = a + u • d := hpc.symm
  have hu : lo + c * (hi - lo) = u :=
    smul_left_injective ℝ hd (add_left_cancel hpc')
  constructor
  · rw [← hu]
    linarith [mul_pos hc.1 (sub_pos.mpr hlohi)]
  · rw [← hu]
    have hmul := mul_pos (sub_pos.mpr hc.2) (sub_pos.mpr hlohi)
    nlinarith


private theorem packingSol_confinedPrimitive_endpoints
    (S : Set Plane) (p v w : Plane) (n : RationalNormal) (R : ℝ) (hR : 0 < R)
    (hsegment : segment ℝ v w ⊆ frontier S)
    (hp : p ∈ segment ℝ v w)
    (hconfined : frontier S ∩ Metric.ball p R ⊆
      {z | normalEval n (z - p) = 0}) :
    normalEval n (v - p) = 0 ∧ normalEval n (w - p) = 0 := by
  have hlocal : ∀ᶠ z in 𝓝 p, z ∈ frontier S → z - p ∈ normalDirection n := by
    filter_upwards [Metric.ball_mem_nhds p hR] with z hz hfront
    exact (normalDirection_mem_iff n _).mpr (hconfined ⟨hfront, hz⟩)
  have hdir := segment_direction_mem_of_frontierGerm hsegment hp hlocal
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨c, _, hpc⟩ := hp
  have hv : v - p = -c • (w - v) := by
    rw [← hpc]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hvδ : v - p ∈ normalDirection n := by rw [hv]; exact (normalDirection n).smul_mem _ hdir
  have hwδ : w - p ∈ normalDirection n := by
    have heq : w - p = (w - v) + (v - p) := by abel
    rw [heq]
    exact (normalDirection n).add_mem hdir hvδ
  exact ⟨(normalDirection_mem_iff n _).mp hvδ, (normalDirection_mem_iff n _).mp hwδ⟩


private theorem packingSol_selectedLine_actualBoundaryOccurrence
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane) (n : RationalNormal)
    (hP : polyhedralSupport P = K.support)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a : Plane) (hproper : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hratE : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ p ∈ deformPoint φ a +ᵥ (normalDirection n : Set Plane),
      p ∉ deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T →
      ∀ R : ℝ, 0 < R →
      (∀ t ∈ T, frontier (deformPoint φ t +ᵥ Kφ.support) ∩ Metric.ball p R ⊆
        {z | normalEval n (z - p) = 0}) →
      ∀ t ∈ T, p ∈ frontier (deformPoint φ t +ᵥ Kφ.support) →
      ∃ positive : Bool, ∃ q ∈ signedCarrierIntervals K T E a (packingSol_rationalTangent n) positive,
        (∀ v ∈ Ioo q.1 q.2,
          if positive then positiveEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
            (a + v • packingSol_rationalTangent n)
          else negativeEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
            (a + v • packingSol_rationalTangent n)) ∧
        ∃ u : ℝ, p = deformPoint φ a + u • packingSol_rationalTangent n ∧
          u ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ) ∧
          (if positive then positiveEdgeGerm (deformPoint φ t +ᵥ Kφ.support)
              (packingSol_rationalTangent n) p
            else negativeEdgeGerm (deformPoint φ t +ᵥ Kφ.support)
              (packingSol_rationalTangent n) p) := by
  classical
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hdmem : d ∈ normalDirection n := packingSol_rationalTangent_mem n
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨F₀, ε₀, _, hε₀, _, hfrontier⟩ :=
    rationalPrimitiveEdges_uniformSameSide_transport K P hP E hratE hprimitive hcover
  obtain ⟨F₁, ε₁, hε₁, hsource⟩ := packingSol_selectedLine_primitiveSourceOccurrence
    K T n hrat htile a hproper E
    (fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1, (hE e he).2.2.2.2.2⟩)
  obtain ⟨F₂, ε₂, hε₂, hchain⟩ :=
    packingSol_uniformActualProperCarrierTransport K T htile E hE hcover d hd
  obtain ⟨F₃, ε₃, hε₃, htarget⟩ :=
    packingSol_signedOccurrence_targetGerms K P hP E hratE hprimitive hcover
  refine ⟨F₀ ∪ (F₁ ∪ (F₂ ∪ F₃)), min ε₀ (min ε₁ (min ε₂ ε₃)),
    lt_min hε₀ (lt_min hε₁ (lt_min hε₂ hε₃)), ?_⟩
  intro φ hφ Kφ hKφ p hp hpnot R hR hconfined t ht hpfront
  have hφ₀ : IsFiniteApproximation F₀ ε₀ φ :=
    ⟨hφ.1, fun x hx => (hφ.2 x (Finset.mem_union_left _ hx)).trans_le (min_le_left _ _)⟩
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ :=
    ⟨hφ.1, fun x hx => (hφ.2 x (Finset.mem_union_right _ (Finset.mem_union_left _ hx))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ :=
    ⟨hφ.1, fun x hx => (hφ.2 x (Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_union_left _ hx)))).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ :=
    ⟨hφ.1, fun x hx => (hφ.2 x (Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_union_right _ hx)))).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  obtain ⟨_, _, _, _, hfront, _⟩ := hfrontier φ hφ₀ Kφ hKφ
  have hfrontt : frontier (deformPoint φ t +ᵥ Kφ.support) =
      ⋃ e ∈ E, segment ℝ (deformPoint φ t + deformPoint φ e.1)
        (deformPoint φ t + deformPoint φ e.2) := by
    rw [← sourceRay_link_frontier_vadd, hfront, Set.vadd_set_iUnion]
    simp only [Set.vadd_set_iUnion, vadd_segment, vadd_eq_add]
  obtain ⟨e, he, hpseg⟩ := Set.mem_iUnion₂.mp (hfrontt ▸ hpfront)
  have hsegment : segment ℝ (deformPoint φ t + deformPoint φ e.1)
      (deformPoint φ t + deformPoint φ e.2) ⊆ frontier (deformPoint φ t +ᵥ Kφ.support) := by
    intro z hz
    rw [hfrontt]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩
  have hvertex (v : Plane) (hv : v ∈ Tiling.vertexSet K.support) :
      deformPoint φ t + deformPoint φ v ∈
        deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T := by
    exact ⟨t + v, Set.mem_add.mpr ⟨v, hv, t, ht, add_comm v t⟩,
      (deformPointLinear φ).map_add t v⟩
  have hpOpen : p ∈ openSegment ℝ (deformPoint φ t + deformPoint φ e.1)
      (deformPoint φ t + deformPoint φ e.2) := by
    rw [← insert_endpoints_openSegment] at hpseg
    rcases hpseg with heq | heq | hopen
    · exact False.elim (hpnot (heq ▸ hvertex _ (hE e he).2.1))
    · exact False.elim (hpnot (heq ▸ hvertex _ (hE e he).2.2.1))
    · exact hopen
  obtain ⟨hleft, hright⟩ := packingSol_confinedPrimitive_endpoints _ p
    (deformPoint φ t + deformPoint φ e.1) (deformPoint φ t + deformPoint φ e.2) n R hR
    hsegment hpseg (hconfined t ht)
  have hpLevel : normalEval n p = normalEval n (deformPoint φ a) := by
    obtain ⟨v, hv, hvp⟩ := Set.mem_vadd_set.mp hp
    have hvp' : deformPoint φ a + v = p := hvp
    rw [← hvp', normalEval_add, (normalDirection_mem_iff n v).mp hv, add_zero]
  have onLine (z : Plane) (hz : normalEval n (z - p) = 0) :
      z ∈ deformPoint φ a +ᵥ (normalDirection n : Set Plane) := by
    refine Set.mem_vadd_set.mpr ⟨z - deformPoint φ a, ?_, by simp⟩
    apply (normalDirection_mem_iff n _).mpr
    rw [normalEval_sub] at hz ⊢
    linarith
  obtain ⟨positive, q, hq, hcoords, hgerm⟩ := hsource φ hφ₁ t ht e he
    (onLine _ hleft) (onLine _ hright)
  have hbound := (hchain φ hφ₂ (normalDirection n) hdmem a hproper positive).1
  have hqorder : (φ q.1 : ℝ) < (φ q.2 : ℝ) := by
    have hb := (hbound q.1 ⟨q, hq, Or.inl rfl⟩ q.2 ⟨q, hq, Or.inr rfl⟩ hq.1).1
    linarith [hq.1]
  have hspan : normalDirection n = Submodule.span ℝ ({d} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one (normalDirection_rational n).1 hdmem hd
  have hpδ : p - deformPoint φ a ∈ Submodule.span ℝ ({d} : Set Plane) := by
    rw [← hspan]
    apply (normalDirection_mem_iff n _).mpr
    rw [normalEval_sub, hpLevel, sub_self]
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hpδ
  have hpcoord : p = deformPoint φ a + u • d := by rw [hu]; abel
  have mapEndpoint {v : Plane} {x : ℝ} (hv : t + v = a + x • d) :
      deformPoint φ t + deformPoint φ v = deformPoint φ a + (φ x : ℝ) • d := by
    calc
      _ = deformPoint φ (t + v) := ((deformPointLinear φ).map_add _ _).symm
      _ = deformPoint φ (a + x • d) := by rw [hv]
      _ = _ := packingSol_deform_rationalCarrierParameter φ n a x
  have huOpen : u ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ) := by
    apply packingSol_openCarrierParameter_reflect (deformPoint φ a) d hd _ _ u hqorder
    rw [← hpcoord]
    rcases hcoords with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simpa only [mapEndpoint hl, mapEndpoint hr] using hpOpen
    · simpa only [mapEndpoint hl, mapEndpoint hr, openSegment_symm] using hpOpen
  refine ⟨positive, q, hq, hgerm, u, hpcoord, huOpen, ?_⟩
  rw [hpcoord]
  exact htarget φ hφ₃ Kφ hKφ n a t e he q hq.1 hcoords
    (hE e he).2.2.2.2.2 positive hgerm u huOpen


private theorem packingSol_positiveHalfBall_not_negativeGerm
    (S : Set Plane) (p d : Plane) (hd : d ≠ 0) (R : ℝ) (hR : 0 < R)
    (hinside : Metric.ball p R ∩ Tiling.positiveSide p d ⊆ S) :
    ¬ negativeEdgeGerm S d p := by
  rintro ⟨ρ, hρ, hEq⟩
  obtain ⟨x, hxball, hxside⟩ := packingSol_positiveHalfBall_point p d hd
    (min R ρ) (lt_min hR hρ)
  have hxR : x ∈ Metric.ball p R :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hxball).trans_le (min_le_left _ _))
  have hxρ : x ∈ Metric.ball p ρ :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hxball).trans_le (min_le_right _ _))
  have hxS := hinside ⟨hxR, hxside⟩
  have hxneg : x ∈ Tiling.negativeHalfPlane p d := by
    exact ((Set.ext_iff.mp hEq x).mp ⟨hxS, hxρ⟩).1
  exact (not_le_of_gt (Tiling.mem_positiveSide.mp hxside))
    (Tiling.mem_negativeHalfPlane.mp hxneg)


private theorem packingSol_selectedLine_exclusiveClosedWitness
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane) (n : RationalNormal)
    (hP : polyhedralSupport P = K.support)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a : Plane) (hproper : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hratE : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
        ∃ t ∈ T, ∃ x ∈ deformPoint φ t +ᵥ Kφ.openCarrier,
          ∀ s ∈ T, s ≠ t → x ∉ deformPoint φ s +ᵥ Kφ.support := by
  classical
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hdmem : d ∈ normalDirection n := packingSol_rationalTangent_mem n
  obtain ⟨F₀, ε₀, hε₀, hseed⟩ := packingSol_selectedLine_actualFrontierFreeHalfBall
    K P T n hP hrat htile a hproper E hE hratE hcover
  obtain ⟨F₁, ε₁, hε₁, hoccurrence⟩ := packingSol_selectedLine_actualBoundaryOccurrence
    K P T n hP hrat htile a hproper E hE hratE hcover
  obtain ⟨F₂, ε₂, hε₂, hchain⟩ :=
    packingSol_uniformActualProperCarrierTransport K T htile E hE hcover d hd
  obtain ⟨F₃, ε₃, hε₃, hcoverage⟩ := deformation_closedCopies_coverPlane K P T hP hrat htile
  obtain ⟨F₄, ε₄, hε₄, havoid⟩ :=
    properLink_deformedCarrier_avoidsLabelledInteriors K P T n hP hrat htile
  let F := F₀ ∪ (F₁ ∪ (F₂ ∪ (F₃ ∪ F₄)))
  let ε := min ε₀ (min ε₁ (min ε₂ (min ε₃ ε₄)))
  refine ⟨F, ε, lt_min hε₀ (lt_min hε₁ (lt_min hε₂ (lt_min hε₃ hε₄))), ?_⟩
  intro φ hφ Kφ hKφ
  have hApprox (A : Finset ℝ) (δ : ℝ) (hA : A ⊆ F) (hδ : ε ≤ δ) :
      IsFiniteApproximation A δ φ :=
    finiteApproximation_strengthen A F δ ε φ hA hδ hφ
  have hφ₀ : IsFiniteApproximation F₀ ε₀ φ := hApprox _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    (min_le_left _ _)
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := hApprox _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans (min_le_left _ _))
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ := hApprox _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ := hApprox _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hφ₄ : IsFiniteApproximation F₄ ε₄ φ := hApprox _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨p, hp, R, hR, hvertex, hconfined⟩ := hseed φ hφ₀ Kφ hKφ
  let U := Metric.ball p R ∩ Tiling.positiveSide p d
  have hUpre : IsPreconnected U := Tiling.isPreconnected_ball_inter_positiveSide p d R
  have hUfront (s : Plane) (hs : s ∈ T) :
      Disjoint U (frontier (deformPoint φ s +ᵥ Kφ.support)) := by
    apply Set.disjoint_left.mpr
    intro z hz hzfront
    have hnormal := hconfined s hs ⟨hzfront, hz.1⟩
    have hside : Tiling.signedSide p d z = 0 := by
      rw [packingSol_tangent_signedSide, hnormal, neg_zero]
    exact (ne_of_gt (Tiling.mem_positiveSide.mp hz.2)) hside
  obtain ⟨x, hxU⟩ := packingSol_positiveHalfBall_point p d hd R hR
  have hclosedToOpen (s : Plane) (hs : s ∈ T)
      (hxclosed : x ∈ deformPoint φ s +ᵥ Kφ.support) :
      x ∈ deformPoint φ s +ᵥ Kφ.openCarrier := by
    by_contra hxnot
    apply Set.disjoint_left.mp (hUfront s hs) hxU
    rw [(Kφ.isPolygonal.isClosed.vadd _).frontier_eq, interior_vadd]
    exact ⟨hxclosed, hxnot⟩
  have hpnot : p ∉ deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T := by
    intro hpV
    exact Set.disjoint_left.mp hvertex (Metric.mem_ball_self hR) hpV
  have ownerOccurrence (s : Plane) (hs : s ∈ T)
      (hxclosed : x ∈ deformPoint φ s +ᵥ Kφ.support) :
      ∃ q ∈ signedCarrierIntervals K T E a d true,
        (∀ v ∈ Ioo q.1 q.2, positiveEdgeGerm (s +ᵥ K.support) d (a + v • d)) ∧
        ∃ u : ℝ, p = deformPoint φ a + u • d ∧
          u ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ) := by
    have hxs := hclosedToOpen s hs hxclosed
    have hUinside := packingSol_frontierFree_preconnected_copyInterior Kφ
      (deformPoint φ s) U hUpre (hUfront s hs) ⟨x, hxU, hxs⟩
    have hpClosure : p ∈ closure (deformPoint φ s +ᵥ Kφ.openCarrier) :=
      closure_mono hUinside (packingSol_positiveHalfBall_center_closure p d hd R hR)
    have hpSupport : p ∈ deformPoint φ s +ᵥ Kφ.support := by
      simpa only [closure_vadd, PolygonalRegion.openCarrier,
        Kφ.isPolygonal.closure_interior] using hpClosure
    have hpFront : p ∈ frontier (deformPoint φ s +ᵥ Kφ.support) := by
      rw [(Kφ.isPolygonal.isClosed.vadd _).frontier_eq, interior_vadd]
      exact ⟨hpSupport, fun hpopen =>
        Set.disjoint_left.mp (havoid φ hφ₄ Kφ hKφ a hproper s hs) hp hpopen⟩
    obtain ⟨positive, q, hq, hsource, u, hpcoord, huOpen, htarget⟩ :=
      hoccurrence φ hφ₁ Kφ hKφ p hp hpnot R hR hconfined s hs hpFront
    cases positive with
    | true => exact ⟨q, hq, hsource, u, hpcoord, huOpen⟩
    | false =>
      exact False.elim (packingSol_positiveHalfBall_not_negativeGerm
        (deformPoint φ s +ᵥ Kφ.support) p d hd R hR
        (fun z hz => Set.vadd_set_mono interior_subset (hUinside hz)) htarget)
  have hxCovered : x ∈ ⋃ t : T, deformPoint φ (t : Plane) +ᵥ Kφ.support := by
    rw [hcoverage φ hφ₃ Kφ hKφ]
    trivial
  obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hxCovered
  obtain ⟨q, hq, hsourceT, u, hpu, huOpen⟩ := ownerOccurrence t.1 t.2 hxt
  refine ⟨t.1, t.2, x, hclosedToOpen t.1 t.2 hxt, ?_⟩
  intro s hs hst hxs
  obtain ⟨q', hq', hsourceS, v, hpv, hvOpen⟩ := ownerOccurrence s hs hxs
  have huv : u = v := smul_left_injective ℝ hd (add_left_cancel (hpu.symm.trans hpv))
  have hqq : q = q' := by
    by_contra hne
    exact Set.disjoint_left.mp
      ((hchain φ hφ₂ (normalDirection n) hdmem a hproper true).2.1 q hq q' hq' hne)
      huOpen (huv.symm ▸ hvOpen)
  subst q'
  have hlabels : t.1 = s := packingSol_sameSourceSignedInterval_label K T htile.2.1
    a d t.1 s hd t.2 hs q hq.1 true hsourceT hsourceS
  exact hst hlabels.symm


private theorem packingSol_selectedProperLine_actualSingleComponent
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane) (n : RationalNormal)
    (hP : polyhedralSupport P = K.support)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a : Plane) (hproper : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
        ∃ t ∈ T, ∃ x ∈ deformPoint φ t +ᵥ Kφ.openCarrier,
          (∀ s ∈ T, s ≠ t → x ∉ deformPoint φ s +ᵥ Kφ.support) ∧
          ∀ s ∈ T, s ≠ t →
            Disjoint (connectedComponentIn (deformPoint φ t +ᵥ Kφ.openCarrier) x)
              (deformPoint φ s +ᵥ Kφ.openCarrier) := by
  obtain ⟨E, hE, hcover, _⟩ := rationalIntrinsicPrimitiveEdges K hrat
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)) :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1, (hE e he).2.2.2.2.2.2⟩
  obtain ⟨F₀, ε₀, hε₀, hwitness⟩ := packingSol_selectedLine_exclusiveClosedWitness
    K P T n hP hrat htile a hproper E hprimitive
    (fun e he => (hE e he).2.2.2.2.2.1) hcover
  obtain ⟨F₁, ε₁, hε₁, hsingle⟩ :=
    packingSol_exclusiveClosedWitness_singleComponent K P T hP hrat htile
  refine ⟨F₀ ∪ F₁, min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro φ hφ Kφ hKφ
  have hφ₀ := finiteApproximation_strengthen F₀ (F₀ ∪ F₁) ε₀ (min ε₀ ε₁) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφ₁ := finiteApproximation_strengthen F₁ (F₀ ∪ F₁) ε₁ (min ε₀ ε₁) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  obtain ⟨t, ht, x, hx, hexclusive⟩ := hwitness φ hφ₀ Kφ hKφ
  exact ⟨t, ht, x, hx, hexclusive, hsingle φ hφ₁ Kφ hKφ t ht x hx hexclusive⟩


private theorem packingSol_halfspaceExclusion_annihilates_tangent
    (f ℓ : Plane →L[ℝ] ℝ) (d v : Plane)
    (hld : ℓ d = 0) (hlv : ℓ v < 0)
    (havoid : ∀ z : Plane, ℓ z < 0 → 0 ≤ f z) : f d = 0 := by
  by_contra hfd
  let c := (-1 - f v) / f d
  have hside : ℓ (v + c • d) < 0 := by
    simpa only [map_add, map_smul, hld, smul_zero, add_zero] using hlv
  have hvalue : f (v + c • d) = -1 := by
    rw [map_add, map_smul, smul_eq_mul]
    dsimp only [c]
    rw [div_mul_cancel₀ _ hfd]
    ring
  have hnonnegative := havoid (v + c • d) hside
  rw [hvalue] at hnonnegative
  linarith


private theorem packingSol_samePrototype_overlap_sourceCarrier
    (H : Plane ≃ₜ Plane) (a b c d a' b' c' d' x y : Plane)
    (hab : H '' segment ℝ a b = segment ℝ a' b')
    (hcd : H '' segment ℝ c d = segment ℝ c' d')
    (hxab : x ∈ segment ℝ a' b') (hxcd : x ∈ segment ℝ c' d')
    (hyab : y ∈ segment ℝ a' b') (hycd : y ∈ segment ℝ c' d')
    (hxy : x ≠ y) :
    affineSpan ℝ ({a, b} : Set Plane) = affineSpan ℝ ({c, d} : Set Plane) := by
  have hximage : x ∈ H '' segment ℝ a b := hab.symm ▸ hxab
  have hyimage : y ∈ H '' segment ℝ a b := hab.symm ▸ hyab
  obtain ⟨u, hu, hux⟩ := hximage
  obtain ⟨v, hv, hvy⟩ := hyimage
  have huCD : u ∈ segment ℝ c d := by
    obtain ⟨w, hw, hwx⟩ := (show x ∈ H '' segment ℝ c d from hcd.symm ▸ hxcd)
    have heq : u = w := H.injective (hux.trans hwx.symm)
    exact heq.symm ▸ hw
  have hvCD : v ∈ segment ℝ c d := by
    obtain ⟨w, hw, hwy⟩ := (show y ∈ H '' segment ℝ c d from hcd.symm ▸ hycd)
    have heq : v = w := H.injective (hvy.trans hwy.symm)
    exact heq.symm ▸ hw
  have huv : u ≠ v := fun h => hxy (hux.symm.trans ((congrArg H h).trans hvy))
  have hline {s t z : Plane} (hz : z ∈ segment ℝ s t) :
      z ∈ affineSpan ℝ ({s, t} : Set Plane) := by
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨r, _, rfl⟩ := hz
    exact AffineMap.lineMap_mem_affineSpan_pair r s t
  exact (affineSpan_pair_eq_of_mem_of_mem_of_ne (hline hu) (hline hv) huv).symm.trans
    (affineSpan_pair_eq_of_mem_of_mem_of_ne (hline huCD) (hline hvCD) huv)


private theorem packingSol_sourcePrimitive_overlap_endpoints
    (V : Set Plane) (a b c d p : Plane)
    (hab : a ≠ b) (hcd : c ≠ d)
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hd : d ∈ V)
    (hfreeAB : ∀ z ∈ openSegment ℝ a b, z ∉ V)
    (hfreeCD : ∀ z ∈ openSegment ℝ c d, z ∉ V)
    (hline : affineSpan ℝ ({a, b} : Set Plane) = affineSpan ℝ ({c, d} : Set Plane))
    (hpAB : p ∈ openSegment ℝ a b) (hpCD : p ∈ openSegment ℝ c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hcLine : c ∈ affineSpan ℝ ({a, b} : Set Plane) := by
    rw [hline]
    exact left_mem_affineSpan_pair ℝ c d
  have hdLine : d ∈ affineSpan ℝ ({a, b} : Set Plane) := by
    rw [hline]
    exact right_mem_affineSpan_pair ℝ c d
  obtain ⟨α, hα⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hcLine
  obtain ⟨β, hβ⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hdLine
  have hordered (s t : Plane) (lo hi : ℝ) (hlohi : lo < hi)
      (hs : AffineMap.lineMap a b lo = s) (ht : AffineMap.lineMap a b hi = t)
      (hsV : s ∈ V) (htV : t ∈ V)
      (hfreeST : ∀ z ∈ openSegment ℝ s t, z ∉ V)
      (hpST : p ∈ openSegment ℝ s t) : a = s ∧ b = t := by
    have hST : openSegment ℝ s t = (AffineMap.lineMap a b) '' Ioo lo hi := by
      rw [← hs, ← ht, ← image_openSegment, openSegment_eq_Ioo hlohi]
    obtain ⟨r, hr, hrp⟩ := (openSegment_eq_image_lineMap ℝ a b ▸ hpAB)
    obtain ⟨r', hr', hr'p⟩ := hST ▸ hpST
    have hrr' : r = r' := (AffineMap.lineMap_injective ℝ hab) (hrp.trans hr'p.symm)
    subst r'
    have hnlo : lo ∉ Ioo (0 : ℝ) 1 := by
      intro hlo
      apply hfreeAB s _ hsV
      rw [← hs]
      exact lineMap_mem_openSegment ℝ a b hlo
    have hnhi : hi ∉ Ioo (0 : ℝ) 1 := by
      intro hhi
      apply hfreeAB t _ htV
      rw [← ht]
      exact lineMap_mem_openSegment ℝ a b hhi
    have hnzero : (0 : ℝ) ∉ Ioo lo hi := by
      intro hzero
      apply hfreeST a _ ha
      rw [hST]
      exact ⟨0, hzero, by simp⟩
    have hnone : (1 : ℝ) ∉ Ioo lo hi := by
      intro hone
      apply hfreeST b _ hb
      rw [hST]
      exact ⟨1, hone, by simp⟩
    have hlozero : lo = 0 := by
      apply le_antisymm
      · by_contra h
        exact hnlo ⟨lt_of_not_ge h, hr'.1.trans hr.2⟩
      · by_contra h
        exact hnzero ⟨lt_of_not_ge h, hr.1.trans hr'.2⟩
    have hhione : hi = 1 := by
      apply le_antisymm
      · by_contra h
        exact hnone ⟨hr'.1.trans hr.2, lt_of_not_ge h⟩
      · by_contra h
        exact hnhi ⟨hr.1.trans hr'.2, lt_of_not_ge h⟩
    constructor
    · simpa only [hlozero, AffineMap.lineMap_apply_zero] using hs
    · simpa only [hhione, AffineMap.lineMap_apply_one] using ht
  rcases lt_trichotomy α β with hlt | heq | hgt
  · exact Or.inl (hordered c d α β hlt hα hβ hc hd hfreeCD hpCD)
  · exact False.elim (hcd (hα.symm.trans (heq ▸ hβ)))
  · exact Or.inr (hordered d c β α hgt hβ hα hd hc
      (by simpa only [openSegment_symm] using hfreeCD)
      (by simpa only [openSegment_symm] using hpCD))


private theorem packingSol_homeomorph_openSegment
    (H : Plane ≃ₜ Plane) (a b a' b' : Plane) (hab : a ≠ b)
    (ha : H a = a') (hb : H b = b')
    (hsegment : H '' segment ℝ a b = segment ℝ a' b') :
    H '' openSegment ℝ a b = openSegment ℝ a' b' := by
  have hab' : a' ≠ b' := fun h => hab (H.injective (ha.trans (h.trans hb.symm)))
  have hne {s t z : Plane} (hst : s ≠ t) (hz : z ∈ openSegment ℝ s t) :
      s ≠ z ∧ t ≠ z := by
    constructor
    · intro h
      rw [← h] at hz
      exact hst (left_mem_openSegment_iff.mp hz)
    · intro h
      rw [← h] at hz
      exact hst (right_mem_openSegment_iff.mp hz)
  apply Set.Subset.antisymm
  · rintro z ⟨p, hp, rfl⟩
    have hnp := hne hab hp
    apply mem_openSegment_of_ne_left_right
    · intro h
      exact hnp.1 (H.injective (ha.trans h))
    · intro h
      exact hnp.2 (H.injective (hb.trans h))
    · exact hsegment ▸ ⟨p, openSegment_subset_segment ℝ a b hp, rfl⟩
  · intro z hz
    obtain ⟨p, hp, hpz⟩ := (show z ∈ H '' segment ℝ a b from
      hsegment.symm ▸ openSegment_subset_segment ℝ a' b' hz)
    have hnz := hne hab' hz
    refine ⟨p, mem_openSegment_of_ne_left_right ?_ ?_ hp, hpz⟩
    · intro h
      exact hnz.1 (ha.symm.trans ((congrArg H h).trans hpz))
    · intro h
      exact hnz.2 (hb.symm.trans ((congrArg H h).trans hpz))


private theorem packingSol_samePrototype_overlap_occurrence
    (H : Plane ≃ₜ Plane) (V : Set Plane) (a b c d a' b' c' d' x y : Plane)
    (hab : a ≠ b) (hcd : c ≠ d)
    (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V) (hdV : d ∈ V)
    (hfreeAB : ∀ z ∈ openSegment ℝ a b, z ∉ V)
    (hfreeCD : ∀ z ∈ openSegment ℝ c d, z ∉ V)
    (ha : H a = a') (hb : H b = b') (hc : H c = c') (hd : H d = d')
    (hAB : H '' segment ℝ a b = segment ℝ a' b')
    (hCD : H '' segment ℝ c d = segment ℝ c' d')
    (hxAB : x ∈ openSegment ℝ a' b') (hxCD : x ∈ openSegment ℝ c' d')
    (hyAB : y ∈ openSegment ℝ a' b') (hyCD : y ∈ openSegment ℝ c' d')
    (hxy : x ≠ y) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hline := packingSol_samePrototype_overlap_sourceCarrier H a b c d a' b' c' d' x y
    hAB hCD (openSegment_subset_segment ℝ a' b' hxAB)
    (openSegment_subset_segment ℝ c' d' hxCD)
    (openSegment_subset_segment ℝ a' b' hyAB)
    (openSegment_subset_segment ℝ c' d' hyCD) hxy
  obtain ⟨p, hp, hpx⟩ := (show x ∈ H '' openSegment ℝ a b from
    (packingSol_homeomorph_openSegment H a b a' b' hab ha hb hAB).symm ▸ hxAB)
  obtain ⟨q, hq, hqx⟩ := (show x ∈ H '' openSegment ℝ c d from
    (packingSol_homeomorph_openSegment H c d c' d' hcd hc hd hCD).symm ▸ hxCD)
  have hpCD : p ∈ openSegment ℝ c d :=
    (H.injective (hpx.trans hqx.symm)).symm ▸ hq
  exact packingSol_sourcePrimitive_overlap_endpoints V a b c d p hab hcd
    haV hbV hcV hdV hfreeAB hfreeCD hline hp hpCD


private theorem packingSol_singleComponent_halfStar_sideExclusion
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
        ∀ p ∈ Tiling.RationalSlopes.translatedVertices K T,
        ∀ t ∈ T, ∀ x ∈ deformPoint φ t +ᵥ Kφ.openCarrier,
        (∀ s ∈ T, s ≠ t → Disjoint
          (connectedComponentIn (deformPoint φ t +ᵥ Kφ.openCarrier) x)
          (deformPoint φ s +ᵥ Kφ.openCarrier)) →
        (∀ s ∈ T, p ∈ s +ᵥ Tiling.vertexSet K.support → s ≠ t) →
        ∀ ℓ : Plane →L[ℝ] ℝ, ℓ ≠ 0 → ∀ r : ℝ, 0 < r →
        (Metric.ball (deformPoint φ p) r ∩
          {y | ℓ (y - deformPoint φ p) < 0}) ⊆
          connectedComponentIn (deformPoint φ t +ᵥ Kφ.openCarrier) x →
        ∃ f : Plane →L[ℝ] ℝ, ∃ u : Plane, f u = 1 ∧
          originalVertexConeUnion K P T p = {z | f z ≤ 0} ∧
          ∀ z : Plane, ℓ z < 0 → 0 ≤ f z := by
  classical
  obtain ⟨F, ε, ρ₀, hε, hρ₀, hdeformedGerm⟩ :=
    originalVertexConeUnion_deformedGerm K P T
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ p hp t ht x hx hsingle hstar ℓ hℓ r hr hhalfBall
  obtain ⟨v, hv, t₀, ht₀, hpEq⟩ := hp
  have hpVertex : p ∈ t₀ +ᵥ Tiling.vertexSet K.support := by
    apply Set.mem_vadd_set.mpr
    refine ⟨v, hv, ?_⟩
    simpa only [vadd_eq_add, add_comm] using hpEq
  have hshape := originalVertexConeUnion_fullOrHalfPlane K P T hP htile p t₀ ht₀ hpVertex
  let pφ := deformPoint φ p
  let Q := originalVertexConeUnion K P T p
  let R := min ρ₀ r
  have hR : 0 < R := lt_min hρ₀ hr
  have hRρ : R ≤ ρ₀ := min_le_left _ _
  have hRr : R ≤ r := min_le_right _ _
  have hcount : T.Countable := originalLabels_countable K T htile.2.1
  have hcontra (z : Plane) (hz : dist z 0 < R) (hℓz : ℓ z < 0)
      (hzinterior : z ∈ interior Q) : False := by
    let U : Set Plane := Metric.ball pφ R ∩ {y | ℓ (y - pφ) < 0} ∩
      {y | y - pφ ∈ interior Q}
    have hnegOpen : IsOpen {y : Plane | ℓ (y - pφ) < 0} :=
      isOpen_Iio.preimage (ℓ.continuous.comp (continuous_id.sub continuous_const))
    have hQOpen : IsOpen {y : Plane | y - pφ ∈ interior Q} :=
      isOpen_interior.preimage (continuous_id.sub continuous_const)
    have hUOpen : IsOpen U := by
      exact Metric.isOpen_ball.inter hnegOpen |>.inter hQOpen
    have hpz : pφ + z ∈ U := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [dist_eq_norm] using hz
      · simpa using hℓz
      · simpa using hzinterior
    obtain ⟨y, hyU, hyfront⟩ := exists_off_translatedFrontiers Kφ T hcount
      (deformPoint φ) U hUOpen ⟨pφ + z, hpz⟩
    have hyU' : y ∈ Metric.ball pφ R ∩ {y | ℓ (y - pφ) < 0} ∩
        {y | y - pφ ∈ interior Q} := hyU
    have hyoffset : dist (y - pφ) 0 < ρ₀ := by
      have hyR : dist y pφ < R := Metric.mem_ball.mp hyU'.1.1
      simpa only [dist_eq_norm, sub_zero] using hyR.trans_le hRρ
    have hyQ : y - pφ ∈ Q := interior_subset hyU'.2
    have hyStar : y ∈
        ⋃ q : {q : T // p ∈ (q : Plane) +ᵥ Tiling.vertexSet K.support},
          deformPoint φ (q.1 : Plane) +ᵥ Kφ.support := by
      have hlocal := (hdeformedGerm φ hφ Kφ hKφ p (y - pφ) hyoffset).mpr hyQ
      simpa [pφ] using hlocal
    obtain ⟨q, hyq⟩ := Set.mem_iUnion.mp hyStar
    have hqt : (q.1 : Plane) ≠ t := hstar q.1 q.1.2 q.2
    have hySupport : y ∈ deformPoint φ (q.1 : Plane) +ᵥ Kφ.support := hyq
    have hyNotFrontier : y ∉ frontier (deformPoint φ (q.1 : Plane) +ᵥ Kφ.support) :=
      hyfront q.1 q.1.2
    have hyInterior : y ∈ interior (deformPoint φ (q.1 : Plane) +ᵥ Kφ.support) := by
      by_contra hyNotInterior
      exact hyNotFrontier (by
        rw [(Kφ.isPolygonal.isClosed.vadd _).frontier_eq]
        exact ⟨hySupport, hyNotInterior⟩)
    have hyOpenCarrier : y ∈ deformPoint φ (q.1 : Plane) +ᵥ Kφ.openCarrier := by
      simpa only [PolygonalRegion.openCarrier, interior_vadd] using hyInterior
    have hyClose : dist y pφ < r := by
      exact (Metric.mem_ball.mp hyU'.1.1).trans_le hRr
    have hyComponent : y ∈ connectedComponentIn
        (deformPoint φ t +ᵥ Kφ.openCarrier) x :=
      hhalfBall ⟨Metric.mem_ball.mpr hyClose, hyU'.1.2⟩
    exact (Set.disjoint_left.mp (hsingle q.1 q.1.2 hqt)) hyComponent hyOpenCarrier
  have hnegative : ∃ z : Plane, ℓ z < 0 := by
    by_contra hnone
    have hnonneg (z : Plane) : 0 ≤ ℓ z := by
      by_contra hn
      exact hnone ⟨z, lt_of_not_ge hn⟩
    have hnonpos (z : Plane) : ℓ z ≤ 0 := by
      have h := hnonneg (-z)
      rw [map_neg] at h
      linarith
    have hzero : ℓ = 0 := by
      ext z
      exact le_antisymm (hnonpos z) (hnonneg z)
    exact hℓ hzero
  rcases hshape with hfull | ⟨s₀, hs₀, hps₀, hps₀not, f, u, hfu, hhalf, ρH, hρH, hsourceGerm⟩
  · obtain ⟨z, hℓz⟩ := hnegative
    obtain ⟨c, hc, hsmall⟩ := exists_positiveScaling_intoBall z R hR
    have hscaleNeg : ℓ (c • z) < 0 := by
      rw [map_smul]
      exact mul_neg_of_pos_of_neg hc hℓz
    have hscaleInterior : c • z ∈ interior Q := by
      change c • z ∈ interior (originalVertexConeUnion K P T p)
      rw [hfull]
      simp
    exact False.elim (hcontra (c • z) hsmall hscaleNeg hscaleInterior)
  · have hsign : ∀ z : Plane, ℓ z < 0 → 0 ≤ f z := by
      intro z hℓz
      by_contra hnot
      have hfz : f z < 0 := lt_of_not_ge hnot
      obtain ⟨c, hc, hsmall⟩ := exists_positiveScaling_intoBall z R hR
      have hscaleNeg : ℓ (c • z) < 0 := by
        rw [map_smul]
        exact mul_neg_of_pos_of_neg hc hℓz
      have hscaleF : f (c • z) < 0 := by
        rw [map_smul]
        exact mul_neg_of_pos_of_neg hc hfz
      have hscaleInterior : c • z ∈ interior Q := by
        have hopen : IsOpen {w : Plane | f w < 0} :=
          isOpen_Iio.preimage f.continuous
        have hsubset : {w : Plane | f w < 0} ⊆ Q := by
          intro w hw
          change w ∈ originalVertexConeUnion K P T p
          rw [hhalf]
          have hw' : f w < 0 := by simpa only [Set.mem_setOf_eq] using hw
          exact hw'.le
        exact interior_maximal hsubset hopen hscaleF
      exact hcontra (c • z) hsmall hscaleNeg hscaleInterior
    exact ⟨f, u, hfu, hhalf, hsign⟩


private theorem packingSol_singleComponent_halfStar_tangentRays
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) :
    ∃ F : Finset ℝ, ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ p ∈ Tiling.RationalSlopes.translatedVertices K T,
      ∀ t ∈ T, ∀ x ∈ deformPoint φ t +ᵥ Kφ.openCarrier,
      (∀ s ∈ T, s ≠ t → Disjoint
        (connectedComponentIn (deformPoint φ t +ᵥ Kφ.openCarrier) x)
        (deformPoint φ s +ᵥ Kφ.openCarrier)) →
      (∀ s ∈ T, p ∈ s +ᵥ Tiling.vertexSet K.support → s ≠ t) →
      ∀ ℓ : Plane →L[ℝ] ℝ, ℓ ≠ 0 → ∀ r : ℝ, 0 < r →
      (Metric.ball (deformPoint φ p) r ∩
        {y | ℓ (y - deformPoint φ p) < 0}) ⊆
        connectedComponentIn (deformPoint φ t +ᵥ Kφ.openCarrier) x →
      ∃ f : Plane →L[ℝ] ℝ, ∃ u : Plane, f u = 1 ∧
        originalVertexConeUnion K P T p = {z | f z ≤ 0} ∧
        (∀ d : Plane, ℓ d = 0 → f d = 0) ∧
        ∀ d : Plane, ℓ d = 0 → ∃ s ∈ T,
          p ∈ s +ᵥ Tiling.vertexSet K.support ∧
          ∀ c : ℝ, 0 < c → dist (c • d) 0 < ρ →
            p + c • d ∈ frontier (s +ᵥ K.support) ∧
            deformPoint φ p + c • d ∈ frontier (deformPoint φ s +ᵥ Kφ.support) := by
  obtain ⟨F₀, ε₀, hε₀, hexclusion⟩ :=
    packingSol_singleComponent_halfStar_sideExclusion K P T hP htile
  obtain ⟨F₁, ε₁, ρ, hε₁, hρ, hrays⟩ :=
    originalHalfVertexStar_uniformTangentRays K P T hP htile
  refine ⟨F₀ ∪ F₁, min ε₀ ε₁, ρ, lt_min hε₀ hε₁, hρ, ?_⟩
  intro φ hφ Kφ hKφ p hp t ht x hx hsingle hstar ℓ hℓ r hr hhalf
  have hφ₀ : IsFiniteApproximation F₀ ε₀ φ :=
    ⟨hφ.1, fun s hs => (hφ.2 s (Finset.mem_union_left _ hs)).trans_le (min_le_left _ _)⟩
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ :=
    ⟨hφ.1, fun s hs => (hφ.2 s (Finset.mem_union_right _ hs)).trans_le (min_le_right _ _)⟩
  obtain ⟨f₀, u₀, hfu₀, hhalf₀, hsign⟩ :=
    hexclusion φ hφ₀ Kφ hKφ p hp t ht x hx hsingle hstar ℓ hℓ r hr hhalf
  have hnegative : ∃ v : Plane, ℓ v < 0 := by
    by_contra hnone
    have hnonneg (z : Plane) : 0 ≤ ℓ z := by
      by_contra hn
      exact hnone ⟨z, lt_of_not_ge hn⟩
    have hnonpos (z : Plane) : ℓ z ≤ 0 := by
      have h := hnonneg (-z)
      rw [map_neg] at h
      linarith
    apply hℓ
    ext z
    exact le_antisymm (hnonpos z) (hnonneg z)
  obtain ⟨v, hv⟩ := hnegative
  have hker₀ : ∀ d : Plane, ℓ d = 0 → f₀ d = 0 := fun d hd =>
    packingSol_halfspaceExclusion_annihilates_tangent f₀ ℓ d v hd hv hsign
  obtain ⟨v₀, hv₀, s₀, hs₀, hpEq⟩ := hp
  have hp₀ : p ∈ s₀ +ᵥ Tiling.vertexSet K.support := by
    refine Set.mem_vadd_set.mpr ⟨v₀, hv₀, ?_⟩
    simpa only [vadd_eq_add, add_comm] using hpEq
  rcases hrays φ hφ₁ Kφ hKφ p s₀ hs₀ hp₀ with
    hfull | ⟨f, u, hfu, hhalf, hactual⟩
  · have huQ : u₀ ∈ originalVertexConeUnion K P T p := hfull.symm ▸ Set.mem_univ u₀
    rw [hhalf₀] at huQ
    change f₀ u₀ ≤ 0 at huQ
    rw [hfu₀] at huQ
    exact False.elim (by linarith)
  · have hker : ∀ d : Plane, ℓ d = 0 → f d = 0 := by
      intro d hd
      have hf₀d : f₀ d = 0 := hker₀ d hd
      have hdQ : d ∈ originalVertexConeUnion K P T p := by
        rw [hhalf₀]
        exact hf₀d.le
      have hndQ : -d ∈ originalVertexConeUnion K P T p := by
        rw [hhalf₀]
        change f₀ (-d) ≤ 0
        rw [map_neg, hf₀d]
        norm_num
      have hfd : f d ≤ 0 := by
        rw [hhalf] at hdQ
        exact hdQ
      have hfnd : f (-d) ≤ 0 := by
        rw [hhalf] at hndQ
        exact hndQ
      rw [map_neg] at hfnd
      exact le_antisymm hfd (by linarith)
    exact ⟨f, u, hfu, hhalf, hker, fun d hd => hactual d (hker d hd)⟩


private theorem packingSol_actualComponent_negativeBoundaryFrame
    (Kφ : PolygonalRegion) (b x p d : Plane)
    (hx : x ∈ b +ᵥ Kφ.openCarrier) (hd : d ≠ 0)
    (hp : p ∈ frontier (connectedComponentIn (b +ᵥ Kφ.openCarrier) x))
    (hgerm : negativeEdgeGerm (b +ᵥ Kφ.support) d p) :
    ∃ R : ℝ, 0 < R ∧
      (Metric.ball p R ∩ Tiling.negativeSide p d ⊆
        connectedComponentIn (b +ᵥ Kφ.openCarrier) x) ∧
      Tiling.affineLine p d ∩ Metric.ball p R ⊆ frontier (b +ᵥ Kφ.support) := by
  obtain ⟨R, hR, hEq⟩ := hgerm
  let S := b +ᵥ Kφ.support
  let O := connectedComponentIn (b +ᵥ Kφ.openCarrier) x
  let U := Metric.ball p R ∩ Tiling.negativeSide p d
  have hUopen : IsOpen U := Metric.isOpen_ball.inter (Tiling.isOpen_negativeSide p d)
  have hUS : U ⊆ S := by
    intro z hz
    exact ((Set.ext_iff.mp hEq z).mpr
      ⟨Tiling.mem_negativeHalfPlane.mpr (Tiling.mem_negativeSide.mp hz.2).le, hz.1⟩).1
  have hUinside : U ⊆ b +ᵥ Kφ.openCarrier := by
    simpa only [S, interior_vadd, PolygonalRegion.openCarrier] using
      hUopen.subset_interior_iff.mpr hUS
  have hlineFront : Tiling.affineLine p d ∩ Metric.ball p R ⊆ frontier S := by
    intro z hz
    have hzline : Tiling.signedSide p d z = 0 := Tiling.mem_affineLine.mp hz.1
    have hzS : z ∈ S := ((Set.ext_iff.mp hEq z).mpr
      ⟨Tiling.mem_negativeHalfPlane.mpr hzline.le, hz.2⟩).1
    have hzNot : z ∉ interior S := by
      intro hzInt
      have hneighborhood : IsOpen (Metric.ball p R ∩ interior S) :=
        Metric.isOpen_ball.inter isOpen_interior
      obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hneighborhood z ⟨hz.2, hzInt⟩
      obtain ⟨w, hwball, hwpositive⟩ := packingSol_positiveHalfBall_point z d hd ρ hρ
      have hwBoth := hball hwball
      have hwS : w ∈ S := interior_subset hwBoth.2
      have hwnegative : Tiling.signedSide p d w ≤ 0 :=
        Tiling.mem_negativeHalfPlane.mp (((Set.ext_iff.mp hEq w).mp ⟨hwS, hwBoth.1⟩).1)
      have hbase : Tiling.signedSide p d w =
          Tiling.signedSide z d w + Tiling.signedSide p d z := by
        simp only [Tiling.signedSide, Tiling.planarCross]
        ring
      have hwpositive' := Tiling.mem_positiveSide.mp hwpositive
      rw [hbase, hzline, add_zero] at hwnegative
      linarith
    rw [(Kφ.isPolygonal.isClosed.vadd b).frontier_eq]
    exact ⟨hzS, hzNot⟩
  obtain ⟨y, hyBall, hyO⟩ := mem_closure_iff.mp (frontier_subset_closure hp)
    (Metric.ball p R) Metric.isOpen_ball (Metric.mem_ball_self hR)
  have hyInside : y ∈ b +ᵥ Kφ.openCarrier := connectedComponentIn_subset _ _ hyO
  have hyInterior : y ∈ interior S := by
    simpa only [S, PolygonalRegion.openCarrier, interior_vadd] using hyInside
  have hyS : y ∈ S := interior_subset hyInterior
  have hyNegative : Tiling.signedSide p d y ≤ 0 :=
    Tiling.mem_negativeHalfPlane.mp (((Set.ext_iff.mp hEq y).mp ⟨hyS, hyBall⟩).1)
  have hyNe : Tiling.signedSide p d y ≠ 0 := by
    intro hyzero
    exact Set.disjoint_left.mp disjoint_interior_frontier hyInterior
      (hlineFront ⟨Tiling.mem_affineLine.mpr hyzero, hyBall⟩)
  have hyU : y ∈ U := ⟨hyBall, Tiling.mem_negativeSide.mpr (lt_of_le_of_ne hyNegative hyNe)⟩
  have hUcomponent : U ⊆ O := by
    change U ⊆ connectedComponentIn (b +ᵥ Kφ.openCarrier) x
    rw [connectedComponentIn_eq hyO]
    exact (Tiling.isPreconnected_ball_inter_negativeSide p d R).subset_connectedComponentIn
      hyU hUinside
  exact ⟨R, hR, hUcomponent, hlineFront⟩


private theorem packingSol_uniformSameLabel_primitiveOccurrenceRecovery
    (K : PolygonalRegion) (P : PolyhedralCode)
    (hP : polyhedralSupport P = K.support) (E : Finset (Plane × Plane))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support)
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ t : Plane, ∀ e ∈ E, ∀ f ∈ E, ∀ x y : Plane, x ≠ y →
      x ∈ openSegment ℝ (deformPoint φ t + deformPoint φ e.1)
        (deformPoint φ t + deformPoint φ e.2) →
      x ∈ openSegment ℝ (deformPoint φ t + deformPoint φ f.1)
        (deformPoint φ t + deformPoint φ f.2) →
      y ∈ openSegment ℝ (deformPoint φ t + deformPoint φ e.1)
        (deformPoint φ t + deformPoint φ e.2) →
      y ∈ openSegment ℝ (deformPoint φ t + deformPoint φ f.1)
        (deformPoint φ t + deformPoint φ f.2) →
      (e.1 = f.1 ∧ e.2 = f.2) ∨ (e.1 = f.2 ∧ e.2 = f.1) := by
  obtain ⟨F, ε, _, hε, _, htransport⟩ :=
    rationalPrimitiveEdges_uniformSameSide_transport K P hP E hrat hprimitive hcover
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ t e he f hf x y hxy hxE hxF hyE hyF
  obtain ⟨H, hanchors, _, hsegments, _, _⟩ := htransport φ hφ Kφ hKφ
  have anchorLeft (q : Plane × Plane) (hq : q ∈ E) : H q.1 = deformPoint φ q.1 :=
    hanchors q.1 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
  have anchorRight (q : Plane × Plane) (hq : q ∈ E) : H q.2 = deformPoint φ q.2 :=
    hanchors q.2 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
  have untranslated (q : Plane × Plane) (z : Plane)
      (hz : z ∈ openSegment ℝ (deformPoint φ t + deformPoint φ q.1)
        (deformPoint φ t + deformPoint φ q.2)) :
      z - deformPoint φ t ∈ openSegment ℝ (deformPoint φ q.1) (deformPoint φ q.2) := by
    have hz' : z ∈ deformPoint φ t +ᵥ
        openSegment ℝ (deformPoint φ q.1) (deformPoint φ q.2) := by
      simpa only [vadd_openSegment, vadd_eq_add] using hz
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using
      Set.mem_vadd_set_iff_neg_vadd_mem.mp hz'
  have hxy' : x - deformPoint φ t ≠ y - deformPoint φ t := by
    intro h
    exact hxy (sub_left_injective h)
  exact packingSol_samePrototype_overlap_occurrence H (Tiling.vertexSet K.support)
    e.1 e.2 f.1 f.2 (deformPoint φ e.1) (deformPoint φ e.2)
    (deformPoint φ f.1) (deformPoint φ f.2) (x - deformPoint φ t) (y - deformPoint φ t)
    (hprimitive e he).1 (hprimitive f hf).1 (hprimitive e he).2.1
    (hprimitive e he).2.2.1 (hprimitive f hf).2.1 (hprimitive f hf).2.2.1
    (hprimitive e he).2.2.2.2 (hprimitive f hf).2.2.2.2
    (anchorLeft e he) (anchorRight e he) (anchorLeft f hf) (anchorRight f hf)
    (hsegments e he) (hsegments f hf)
    (untranslated e x hxE) (untranslated f x hxF)
    (untranslated e y hyE) (untranslated f y hyF) hxy'


private theorem packingSol_compactSignedStrip
    (S C : Set Plane) (a d : Plane) (positive : Bool)
    (hC : IsCompact C) (hline : C ⊆ Tiling.affineLine a d)
    (hgerms : ∀ p ∈ C, if positive then positiveEdgeGerm S d p
      else negativeEdgeGerm S d p) :
    ∃ η : ℝ, 0 < η ∧ ∀ p ∈ C,
      S ∩ Metric.ball p η =
        (if positive then Tiling.positiveHalfPlane p d
          else Tiling.negativeHalfPlane p d) ∩ Metric.ball p η := by
  classical
  have localRadius (p : C) : ∃ r : ℝ, 0 < r ∧
      S ∩ Metric.ball p r =
        (if positive then Tiling.positiveHalfPlane p d
          else Tiling.negativeHalfPlane p d) ∩ Metric.ball p r := by
    cases positive with
    | true => exact hgerms p p.2
    | false => exact hgerms p p.2
  choose radius hpos hlocal using localRadius
  have hcover : C ⊆ ⋃ p : C, Metric.ball (p : Plane) (radius p) := by
    intro p hp
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, Metric.mem_ball_self (hpos ⟨p, hp⟩)⟩
  obtain ⟨η, hη, hballs⟩ := lebesgue_number_lemma_of_metric hC
    (fun p : C => Metric.isOpen_ball) hcover
  refine ⟨η, hη, ?_⟩
  intro p hp
  obtain ⟨q, hsub⟩ := hballs p hp
  have hcross : Tiling.planarCross d (q : Plane) = Tiling.planarCross d p := by
    have hq := Tiling.mem_affineLine.mp (hline q.2)
    have hp' := Tiling.mem_affineLine.mp (hline hp)
    dsimp only [Tiling.signedSide] at hq hp'
    linarith
  have hhalf : (if positive then Tiling.positiveHalfPlane (q : Plane) d
      else Tiling.negativeHalfPlane (q : Plane) d) =
        (if positive then Tiling.positiveHalfPlane p d else Tiling.negativeHalfPlane p d) := by
    cases positive <;> simp only [Bool.false_eq_true, if_false, if_true,
      Tiling.positiveHalfPlane, Tiling.negativeHalfPlane, hcross]
  ext z
  constructor
  · rintro ⟨hzS, hzball⟩
    have hzlocal := (Set.ext_iff.mp (hlocal q) z).mp ⟨hzS, hsub hzball⟩
    exact ⟨hhalf ▸ hzlocal.1, hzball⟩
  · rintro ⟨hzside, hzball⟩
    have hzlocal := (Set.ext_iff.mp (hlocal q) z).mpr ⟨hhalf.symm ▸ hzside, hsub hzball⟩
    exact ⟨hzlocal.1, hzball⟩


private theorem packingSol_edgeCentralSignedStrip
    (S : Set Plane) (a b d : Plane) (positive : Bool)
    (c : ℝ) (hdir : b - a = c • d)
    (hgerms : ∀ p ∈ openSegment ℝ a b, if positive then positiveEdgeGerm S d p
      else negativeEdgeGerm S d p) (R : ℝ) (hR : 0 < R) :
    ∃ η : ℝ, 0 < η ∧ ∀ p ∈ segment ℝ a b,
      R ≤ dist p a → R ≤ dist p b →
      S ∩ Metric.ball p η =
        (if positive then Tiling.positiveHalfPlane p d
          else Tiling.negativeHalfPlane p d) ∩ Metric.ball p η := by
  let C := segment ℝ a b ∩ {p : Plane | R ≤ dist p a} ∩ {p : Plane | R ≤ dist p b}
  have hcompactSegment : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  have hC : IsCompact C :=
    (hcompactSegment.inter_right (isClosed_le continuous_const (by fun_prop))).inter_right
      (isClosed_le continuous_const (by fun_prop))
  have hCopen : C ⊆ openSegment ℝ a b := by
    rintro p ⟨⟨hp, hpa⟩, hpb⟩
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    change R ≤ dist (AffineMap.lineMap a b u) a at hpa
    change R ≤ dist (AffineMap.lineMap a b u) b at hpb
    have hu0 : 0 < u := by
      by_contra h
      have hzero : u = 0 := le_antisymm (le_of_not_gt h) hu.1
      simp only [hzero, AffineMap.lineMap_apply_zero, dist_self] at hpa
      linarith
    have hu1 : u < 1 := by
      by_contra h
      have hone : u = 1 := le_antisymm hu.2 (le_of_not_gt h)
      simp only [hone, AffineMap.lineMap_apply_one, dist_self] at hpb
      linarith
    rw [openSegment_eq_image_lineMap]
    exact ⟨u, ⟨hu0, hu1⟩, rfl⟩
  have hline : C ⊆ Tiling.affineLine a d := by
    rintro p ⟨⟨hp, _⟩, _⟩
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨u, _, rfl⟩ := hp
    have heq : AffineMap.lineMap a b u = a + (u * c) • d := by
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, hdir, smul_smul]
      abel
    rw [heq]
    exact Tiling.vadd_smul_mem_affineLine a d (u * c)
  obtain ⟨η, hη, hstrip⟩ := packingSol_compactSignedStrip S C a d positive hC hline
    (fun p hp => hgerms p (hCopen hp))
  exact ⟨η, hη, fun p hp hpa hpb => hstrip p ⟨⟨hp, hpa⟩, hpb⟩⟩


private theorem packingSol_actualTargetCentralSignedStrips
    (K : PolygonalRegion) (P : PolyhedralCode)
    (hP : polyhedralSupport P = K.support) (E : Finset (Plane × Plane))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support)
    (horient : ∀ e ∈ E,
      (∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
      (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ R : ℝ, 0 < R → ∃ η : ℝ, 0 < η ∧ ∀ e ∈ E,
        ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∧
          ∀ p ∈ segment ℝ (deformPoint φ e.1) (deformPoint φ e.2),
          R ≤ dist p (deformPoint φ e.1) → R ≤ dist p (deformPoint φ e.2) →
          Kφ.support ∩ Metric.ball p η =
            Tiling.positiveHalfPlane p (e.2 - e.1) ∩ Metric.ball p η) ∨
        ((∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z) ∧
          ∀ p ∈ segment ℝ (deformPoint φ e.1) (deformPoint φ e.2),
          R ≤ dist p (deformPoint φ e.1) → R ≤ dist p (deformPoint φ e.2) →
          Kφ.support ∩ Metric.ball p η =
            Tiling.negativeHalfPlane p (e.2 - e.1) ∩ Metric.ball p η) := by
  classical
  obtain ⟨Fs, εs, _, hεs, _, htransport⟩ :=
    rationalPrimitiveEdges_uniformSameSide_transport K P hP E hrat hprimitive hcover
  obtain ⟨Fc, εc, _, hεc, _, hscale⟩ := finiteRationalEdges_positiveHomotheties E hrat
  refine ⟨Fs ∪ Fc, min εs εc, lt_min hεs hεc, ?_⟩
  intro φ hφ Kφ hKφ R hR
  have hφs : IsFiniteApproximation Fs εs φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_left _ hz)).trans_le (min_le_left _ _)
  have hφc : IsFiniteApproximation Fc εc φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_right _ hz)).trans_le (min_le_right _ _)
  obtain ⟨_, _, _, _, _, hgerms⟩ := htransport φ hφs Kφ hKφ
  let valid (e : Plane × Plane) (η : ℝ) : Prop :=
    ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∧
      ∀ p ∈ segment ℝ (deformPoint φ e.1) (deformPoint φ e.2),
      R ≤ dist p (deformPoint φ e.1) → R ≤ dist p (deformPoint φ e.2) →
      Kφ.support ∩ Metric.ball p η =
        Tiling.positiveHalfPlane p (e.2 - e.1) ∩ Metric.ball p η) ∨
    ((∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z) ∧
      ∀ p ∈ segment ℝ (deformPoint φ e.1) (deformPoint φ e.2),
      R ≤ dist p (deformPoint φ e.1) → R ≤ dist p (deformPoint φ e.2) →
      Kφ.support ∩ Metric.ball p η =
        Tiling.negativeHalfPlane p (e.2 - e.1) ∩ Metric.ball p η)
  have each (e : {e // e ∈ E}) : ∃ η : ℝ, 0 < η ∧ valid e η := by
    obtain ⟨c, _, _, hdir, _⟩ := hscale φ hφc e e.2
    rcases horient e e.2 with hpos | hneg
    · obtain ⟨η, hη, hstrip⟩ := packingSol_edgeCentralSignedStrip Kφ.support
        (deformPoint φ e.1.1) (deformPoint φ e.1.2) (e.1.2 - e.1.1) true c hdir
        (fun p hp => by simpa [hKφ] using (hgerms e e.2).1 hpos p hp) R hR
      exact ⟨η, hη, Or.inl ⟨hpos, hstrip⟩⟩
    · obtain ⟨η, hη, hstrip⟩ := packingSol_edgeCentralSignedStrip Kφ.support
        (deformPoint φ e.1.1) (deformPoint φ e.1.2) (e.1.2 - e.1.1) false c hdir
        (fun p hp => by simpa [hKφ] using (hgerms e e.2).2 hneg p hp) R hR
      exact ⟨η, hη, Or.inr ⟨hneg, hstrip⟩⟩
  choose radius hpos hvalid using each
  let D := E.attach.image radius
  obtain ⟨η, hη, hmin⟩ := exists_positiveMinAbs D
  refine ⟨η, hη, ?_⟩
  intro e he
  let i : {e // e ∈ E} := ⟨e, he⟩
  have hηradius : η ≤ radius i := by
    simpa only [abs_of_pos (hpos i)] using
      hmin (radius i) (Finset.mem_image.mpr ⟨i, Finset.mem_attach _ _, rfl⟩) (hpos i).ne'
  have shrink (p : Plane) (side : Set Plane)
      (hEq : Kφ.support ∩ Metric.ball p (radius i) = side ∩ Metric.ball p (radius i)) :
      Kφ.support ∩ Metric.ball p η = side ∩ Metric.ball p η := by
    have hsub : Metric.ball p η ⊆ Metric.ball p (radius i) :=
      Metric.ball_subset_ball hηradius
    ext z
    constructor
    · rintro ⟨hzS, hzball⟩
      exact ⟨((Set.ext_iff.mp hEq z).mp ⟨hzS, hsub hzball⟩).1, hzball⟩
    · rintro ⟨hzside, hzball⟩
      exact ⟨((Set.ext_iff.mp hEq z).mpr ⟨hzside, hsub hzball⟩).1, hzball⟩
  rcases hvalid i with ⟨hsource, hstrip⟩ | ⟨hsource, hstrip⟩
  · exact Or.inl ⟨hsource, fun p hp hpa hpb => shrink p _ (hstrip p hp hpa hpb)⟩
  · exact Or.inr ⟨hsource, fun p hp hpa hpb => shrink p _ (hstrip p hp hpa hpb)⟩


private theorem packingSol_primitiveOccurrence_actualSourceJ
    (K : PolygonalRegion) (T : Set Plane) (E : Finset (Plane × Plane))
    (hfrontier : ∀ e ∈ E, segment ℝ e.1 e.2 ⊆ frontier K.support)
    (a d t : Plane) (hd : d ≠ 0) (ht : t ∈ T)
    (e : Plane × Plane) (he : e ∈ E) (q : ℝ × ℝ) (hq : q.1 < q.2)
    (hcoords : (t + e.1 = a + q.1 • d ∧ t + e.2 = a + q.2 • d) ∨
      (t + e.2 = a + q.1 • d ∧ t + e.1 = a + q.2 • d))
    (hproto :
      (∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
      (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z))
    (r : ℝ) (hrq : r ∈ Icc q.1 q.2) :
    ∃ positive : Bool,
      a + r • d ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support ∧
      q ∈ signedCarrierComponentIntervals K T E a d r positive ∧
      ∀ u ∈ Ioo q.1 q.2,
        if positive then positiveEdgeGerm (t +ᵥ K.support) d (a + u • d)
          else negativeEdgeGerm (t +ᵥ K.support) d (a + u • d) := by
  obtain ⟨positive, hfamily, hgerms⟩ := packingSol_primitiveOccurrence_signedFamily
    K T E a d t hd ht e he q hq hcoords hproto
  have hr := signedCarrierIntervals_sourceBoundaryParameters_subset K T E hfrontier
    a d positive hfamily hrq
  have hsubset := signedCarrierInterval_subset_component_of_meets K T E hfrontier
    a d positive hr hfamily ⟨r, hrq, mem_connectedComponentIn hr⟩
  exact ⟨positive, hr, ⟨hfamily, hsubset⟩, hgerms⟩


private theorem packingSol_uniformSameJ_sameSign_labelUnique
    (K : PolygonalRegion) (T : Set Plane)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (d : Plane) (hd : d ≠ 0) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ a : Plane, ∀ r l u : ℝ,
      a + r • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support → l < u →
      Icc l u ⊆ connectedComponentIn
        {s : ℝ | a + s • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r →
      ∀ positive : Bool, ∀ q ∈ signedCarrierComponentIntervals K T E a d r positive,
      ∀ q' ∈ signedCarrierComponentIntervals K T E a d r positive,
      ∀ s ∈ T, ∀ t ∈ T,
      (∀ v ∈ Ioo q.1 q.2, if positive then positiveEdgeGerm (s +ᵥ K.support) d (a + v • d)
        else negativeEdgeGerm (s +ᵥ K.support) d (a + v • d)) →
      (∀ v ∈ Ioo q'.1 q'.2, if positive then positiveEdgeGerm (t +ᵥ K.support) d (a + v • d)
        else negativeEdgeGerm (t +ᵥ K.support) d (a + v • d)) →
      ∀ z : ℝ, z ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ) →
        z ∈ Ioo (φ q'.1 : ℝ) (φ q'.2 : ℝ) → q = q' ∧ s = t := by
  obtain ⟨F, ε, hε, hchain⟩ :=
    packingSol_uniformActualSourceCarrierTransport K T htile E hE hcover d hd
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ a r l u hr hlu hinterval positive q hq q' hq' s hs t ht hsource hsource' z hz hz'
  have hdisjoint := (hchain φ hφ a r l u hr hlu hinterval positive).2.2.2.1
  have hqq : q = q' := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisjoint q hq q' hq' hne) hz hz'
  refine ⟨hqq, ?_⟩
  rw [← hqq] at hsource'
  exact packingSol_sameSourceSignedInterval_label K T htile.2.1 a d s t hd hs ht
    q hq.1.1 positive hsource hsource'


private theorem packingSol_actualSingleComponent_inwardPartnerLabel
    (Kφ : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (t : Plane) (ht : t ∈ T) (x : Plane) (hx : x ∈ ψ t +ᵥ Kφ.openCarrier)
    (hsingle : ∀ s ∈ T, s ≠ t →
      Disjoint (connectedComponentIn (ψ t +ᵥ Kφ.openCarrier) x)
        (ψ s +ᵥ Kφ.openCarrier))
    (p d : Plane) (hd : d ≠ 0)
    (hp : p ∈ frontier (connectedComponentIn (ψ t +ᵥ Kφ.openCarrier) x))
    (hgerm : negativeEdgeGerm (ψ t +ᵥ Kφ.support) d p) :
    ∃ R : ℝ, 0 < R ∧ ∀ q ∈ Tiling.affineLine p d ∩ Metric.ball p R,
      ∀ s ∈ T, negativeEdgeGerm (ψ s +ᵥ Kφ.support) d q → s = t := by
  obtain ⟨R, hR, hinside, _⟩ := packingSol_actualComponent_negativeBoundaryFrame
    Kφ (ψ t) x p d hx hd hp hgerm
  refine ⟨R, hR, ?_⟩
  intro q hq s hs hsgerm
  by_contra hst
  obtain ⟨ρ, hρ, hEq⟩ := hsgerm
  let U := Metric.ball q ρ ∩ Tiling.negativeSide q d
  have hUopen : IsOpen U := Metric.isOpen_ball.inter (Tiling.isOpen_negativeSide q d)
  have hUS : U ⊆ ψ s +ᵥ Kφ.support := by
    intro z hz
    exact ((Set.ext_iff.mp hEq z).mpr
      ⟨Tiling.mem_negativeHalfPlane.mpr (Tiling.mem_negativeSide.mp hz.2).le, hz.1⟩).1
  have hUinside : U ⊆ ψ s +ᵥ Kφ.openCarrier := by
    simpa only [PolygonalRegion.openCarrier, interior_vadd] using
      hUopen.subset_interior_iff.mpr hUS
  have hmargin : 0 < R - dist q p := by linarith [Metric.mem_ball.mp hq.2]
  obtain ⟨z, hzball, hzpositive⟩ := packingSol_positiveHalfBall_point q (-d)
    (neg_ne_zero.mpr hd) (min ρ (R - dist q p)) (lt_min hρ hmargin)
  have hzρ : z ∈ Metric.ball q ρ :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hzball).trans_le (min_le_left _ _))
  have hzR : z ∈ Metric.ball p R := by
    have hdist := Metric.mem_ball.mp hzball
    have hsmall := hdist.trans_le (min_le_right ρ (R - dist q p))
    have htri := dist_triangle z q p
    exact Metric.mem_ball.mpr (by linarith)
  have hznegative : z ∈ Tiling.negativeSide q d := by
    have hzpos := Tiling.mem_positiveSide.mp hzpositive
    apply Tiling.mem_negativeSide.mpr
    have hneg : Tiling.signedSide q (-d) z = -Tiling.signedSide q d z := by
      simp only [Tiling.signedSide, Tiling.planarCross, Complex.neg_re, Complex.neg_im]
      ring
    rw [hneg] at hzpos
    linarith
  have hzside : z ∈ Tiling.negativeSide p d := by
    have hline := Tiling.mem_affineLine.mp hq.1
    have hzneg := Tiling.mem_negativeSide.mp hznegative
    apply Tiling.mem_negativeSide.mpr
    dsimp only [Tiling.signedSide] at hline hzneg ⊢
    linarith
  exact Set.disjoint_left.mp (hsingle s hs hst)
    (hinside ⟨hzR, hzside⟩) (hUinside ⟨hzρ, hznegative⟩)


private theorem packingSol_commonOldPoint_sourceJRecovery
    (K : PolygonalRegion) (T : Set Plane) (a b d : Plane) (r s α β : ℝ)
    (hα : α ∈ connectedComponentIn
      {u : ℝ | a + u • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r)
    (hβ : β ∈ connectedComponentIn
      {u : ℝ | b + u • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} s)
    (hpoint : a + α • d = b + β • d) :
    ∃ c : ℝ, b = a + c • d ∧
      (Homeomorph.addLeft c) '' connectedComponentIn
        {u : ℝ | b + u • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} s =
      connectedComponentIn
        {u : ℝ | a + u • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} r := by
  let c : ℝ := α - β
  have hb : b = a + c • d := by
    calc
      b = (b + β • d) - β • d := by abel
      _ = (a + α • d) - β • d := by rw [hpoint]
      _ = a + c • d := by dsimp only [c]; module
  let A : Set ℝ := {u | a + u • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support}
  let B : Set ℝ := {u | b + u • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support}
  have hBimage : (Homeomorph.addLeft c) '' B = A := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      change a + (c + v) • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support
      have heq : a + (c + v) • d = b + v • d := by rw [hb]; module
      rw [heq]
      exact hv
    · intro hu
      refine ⟨u - c, ?_, ?_⟩
      · change b + (u - c) • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support
        have heq : b + (u - c) • d = a + u • d := by rw [hb]; module
        rw [heq]
        exact hu
      · change c + (u - c) = u
        ring
  have hβB : β ∈ B := connectedComponentIn_subset B s hβ
  have hsum : c + β = α := by dsimp only [c]; ring
  refine ⟨c, hb, ?_⟩
  change (Homeomorph.addLeft c) '' connectedComponentIn B s = connectedComponentIn A r
  calc
    (Homeomorph.addLeft c) '' connectedComponentIn B s =
        (Homeomorph.addLeft c) '' connectedComponentIn B β := by
      rw [connectedComponentIn_eq hβ]
    _ = connectedComponentIn ((Homeomorph.addLeft c) '' B) ((Homeomorph.addLeft c) β) :=
      (Homeomorph.addLeft c).image_connectedComponentIn hβB
    _ = connectedComponentIn A α := by
      rw [hBimage]
      change connectedComponentIn A (c + β) = connectedComponentIn A α
      rw [hsum]
    _ = connectedComponentIn A r := (connectedComponentIn_eq hα).symm


private theorem packingSol_uniformMappedPrimitive_oldCarrierJRecovery
    (K : PolygonalRegion) (P : PolyhedralCode)
    (hP : polyhedralSupport P = K.support) (E : Finset (Plane × Plane))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support)
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ T : Set Plane, ∀ a b d t : Plane, ∀ r s : ℝ, ∀ positive negative : Bool,
      ∀ q ∈ signedCarrierComponentIntervals K T E a d r positive,
      ∀ q' ∈ signedCarrierComponentIntervals K T E b d s negative,
      ∀ e ∈ E, ∀ f ∈ E,
      ((t + e.1 = a + q.1 • d ∧ t + e.2 = a + q.2 • d) ∨
        (t + e.2 = a + q.1 • d ∧ t + e.1 = a + q.2 • d)) →
      ((t + f.1 = b + q'.1 • d ∧ t + f.2 = b + q'.2 • d) ∨
        (t + f.2 = b + q'.1 • d ∧ t + f.1 = b + q'.2 • d)) →
      ∀ x y : Plane, x ≠ y →
      x ∈ openSegment ℝ (deformPoint φ t + deformPoint φ e.1)
        (deformPoint φ t + deformPoint φ e.2) →
      x ∈ openSegment ℝ (deformPoint φ t + deformPoint φ f.1)
        (deformPoint φ t + deformPoint φ f.2) →
      y ∈ openSegment ℝ (deformPoint φ t + deformPoint φ e.1)
        (deformPoint φ t + deformPoint φ e.2) →
      y ∈ openSegment ℝ (deformPoint φ t + deformPoint φ f.1)
        (deformPoint φ t + deformPoint φ f.2) →
      ∃ c : ℝ, b = a + c • d ∧
        (Homeomorph.addLeft c) '' connectedComponentIn
          {u : ℝ | b + u • d ∈ ⋃ v : T, (v : Plane) +ᵥ frontier K.support} s =
        connectedComponentIn
          {u : ℝ | a + u • d ∈ ⋃ v : T, (v : Plane) +ᵥ frontier K.support} r := by
  obtain ⟨F, ε, hε, hrecovery⟩ :=
    packingSol_uniformSameLabel_primitiveOccurrenceRecovery K P hP E hrat hprimitive hcover
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ T a b d t r s positive negative q hq q' hq' e he f hf
    hcoords hcoords' x y hxy hxE hxF hyE hyF
  have hidentity := hrecovery φ hφ Kφ hKφ t e he f hf x y hxy hxE hxF hyE hyF
  have hα : ∃ α ∈ Icc q.1 q.2, a + α • d = t + e.1 := by
    rcases hcoords with ⟨hl, _⟩ | ⟨_, hr⟩
    · exact ⟨q.1, ⟨le_rfl, hq.1.1.le⟩, hl.symm⟩
    · exact ⟨q.2, ⟨hq.1.1.le, le_rfl⟩, hr.symm⟩
  have hβ : ∃ β ∈ Icc q'.1 q'.2, b + β • d = t + e.1 := by
    rcases hidentity with ⟨hfirst, _⟩ | ⟨hfirst, _⟩
    · rw [hfirst]
      rcases hcoords' with ⟨hl, _⟩ | ⟨_, hr⟩
      · exact ⟨q'.1, ⟨le_rfl, hq'.1.1.le⟩, hl.symm⟩
      · exact ⟨q'.2, ⟨hq'.1.1.le, le_rfl⟩, hr.symm⟩
    · rw [hfirst]
      rcases hcoords' with ⟨_, hr⟩ | ⟨hl, _⟩
      · exact ⟨q'.2, ⟨hq'.1.1.le, le_rfl⟩, hr.symm⟩
      · exact ⟨q'.1, ⟨le_rfl, hq'.1.1.le⟩, hl.symm⟩
  obtain ⟨α, hαinterval, hαpoint⟩ := hα
  obtain ⟨β, hβinterval, hβpoint⟩ := hβ
  exact packingSol_commonOldPoint_sourceJRecovery K T a b d r s α β
    (hq.2 hαinterval) (hq'.2 hβinterval) (hαpoint.trans hβpoint.symm)


private theorem packingSol_actualOccurrence_reanchor_sameJ
    (K : PolygonalRegion) (T : Set Plane) (E : Finset (Plane × Plane))
    (a b d t : Plane) (r s c : ℝ) (positive : Bool)
    (hb : b = a + c • d)
    (hJ : (Homeomorph.addLeft c) '' connectedComponentIn
      {u : ℝ | b + u • d ∈ ⋃ v : T, (v : Plane) +ᵥ frontier K.support} s =
      connectedComponentIn
        {u : ℝ | a + u • d ∈ ⋃ v : T, (v : Plane) +ᵥ frontier K.support} r)
    (ht : t ∈ T) (e : Plane × Plane) (he : e ∈ E)
    (q : ℝ × ℝ) (hq : q ∈ signedCarrierComponentIntervals K T E a d r positive)
    (hcoords : (t + e.1 = a + q.1 • d ∧ t + e.2 = a + q.2 • d) ∨
      (t + e.2 = a + q.1 • d ∧ t + e.1 = a + q.2 • d))
    (hsource : ∀ u ∈ Ioo q.1 q.2,
      if positive then positiveEdgeGerm (t +ᵥ K.support) d (a + u • d)
        else negativeEdgeGerm (t +ᵥ K.support) d (a + u • d)) :
    let q' : ℝ × ℝ := (q.1 - c, q.2 - c)
    q' ∈ signedCarrierComponentIntervals K T E b d s positive ∧
      ((t + e.1 = b + q'.1 • d ∧ t + e.2 = b + q'.2 • d) ∨
       (t + e.2 = b + q'.1 • d ∧ t + e.1 = b + q'.2 • d)) ∧
      ∀ u ∈ Ioo q'.1 q'.2,
        if positive then positiveEdgeGerm (t +ᵥ K.support) d (b + u • d)
          else negativeEdgeGerm (t +ᵥ K.support) d (b + u • d) := by
  let q' : ℝ × ℝ := (q.1 - c, q.2 - c)
  have hparam (u : ℝ) : b + u • d = a + (c + u) • d := by rw [hb]; module
  have hend (u : ℝ) : b + (u - c) • d = a + u • d := by rw [hb]; module
  have hcoords' : (t + e.1 = b + q'.1 • d ∧ t + e.2 = b + q'.2 • d) ∨
      (t + e.2 = b + q'.1 • d ∧ t + e.1 = b + q'.2 • d) := by
    simpa only [q', hend] using hcoords
  have hsource' : ∀ u ∈ Ioo q'.1 q'.2,
      if positive then positiveEdgeGerm (t +ᵥ K.support) d (b + u • d)
        else negativeEdgeGerm (t +ᵥ K.support) d (b + u • d) := by
    intro u hu
    rw [hparam]
    apply hsource (c + u)
    dsimp only [q'] at hu
    constructor <;> linarith [hu.1, hu.2]
  have hfamily : q' ∈ signedCarrierIntervals K T E b d positive :=
    ⟨by dsimp only [q']; linarith [hq.1.1], t, ht, e, he, hcoords', hsource'⟩
  have hsubset : Icc q'.1 q'.2 ⊆ connectedComponentIn
      {u : ℝ | b + u • d ∈ ⋃ v : T, (v : Plane) +ᵥ frontier K.support} s := by
    intro u hu
    have hshift : c + u ∈ Icc q.1 q.2 := by
      dsimp only [q'] at hu
      constructor <;> linarith [hu.1, hu.2]
    have hmem := hq.2 hshift
    rw [← hJ] at hmem
    obtain ⟨v, hv, hvu⟩ := hmem
    have hveq : v = u := by
      apply add_left_cancel (a := c)
      exact hvu
    simpa only [hveq] using hv
  exact ⟨⟨hfamily, hsubset⟩, hcoords', hsource'⟩


private theorem packingSol_realMappedCarrier_reanchor
    (φ : ℝ →ₗ[ℚ] ℚ) (n : RationalNormal) (a b : Plane) (c : ℝ)
    (hb : b = a + c • packingSol_rationalTangent n) :
    (∀ z : ℝ, deformPoint φ a + z • packingSol_rationalTangent n =
      deformPoint φ b + (z - (φ c : ℝ)) • packingSol_rationalTangent n) ∧
    ∀ q : ℝ × ℝ, ∀ z ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ),
      z - (φ c : ℝ) ∈ Ioo (φ (q.1 - c) : ℝ) (φ (q.2 - c) : ℝ) := by
  have hmap : deformPoint φ b = deformPoint φ a + (φ c : ℝ) • packingSol_rationalTangent n := by
    rw [hb]
    exact packingSol_deform_rationalCarrierParameter φ n a c
  refine ⟨fun z => ?_, ?_⟩
  · rw [hmap]
    module
  · intro q z hz
    have subcast (u : ℝ) : (φ (u - c) : ℝ) = (φ u : ℝ) - (φ c : ℝ) := by
      simp only [map_sub, Rat.cast_sub]
    rw [subcast, subcast]
    constructor <;> linarith [hz.1, hz.2]


private theorem packingSol_offsetInwardStrip_exclusion
    (Kφ : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (t : Plane) (x : Plane)
    (hsingle : ∀ s ∈ T, s ≠ t →
      Disjoint (connectedComponentIn (ψ t +ᵥ Kφ.openCarrier) x)
        (ψ s +ᵥ Kφ.openCarrier))
    (p d : Plane) (hd : d ≠ 0) (R : ℝ) (hR : 0 < R)
    (hinside : Metric.ball p R ∩ Tiling.negativeSide p d ⊆
      connectedComponentIn (ψ t +ᵥ Kφ.openCarrier) x)
    (hown : (ψ t +ᵥ Kφ.support) ∩ Metric.ball p R =
      Tiling.negativeHalfPlane p d ∩ Metric.ball p R)
    (s : Plane) (hs : s ∈ T) (q : Plane) (hqR : q ∈ Metric.ball p R)
    (hqpositive : q ∈ Tiling.positiveSide p d) (η : ℝ)
    (hη : dist q p < η)
    (hstrip : (ψ s +ᵥ Kφ.support) ∩ Metric.ball q η =
      Tiling.negativeHalfPlane q d ∩ Metric.ball q η) : False := by
  have hηpos : 0 < η := lt_of_le_of_lt dist_nonneg hη
  have hmargin : 0 < η - dist q p := sub_pos.mpr hη
  obtain ⟨z, hzball, hzpositive⟩ := packingSol_positiveHalfBall_point p (-d)
    (neg_ne_zero.mpr hd) (min R (η - dist q p)) (lt_min hR hmargin)
  have hzR : z ∈ Metric.ball p R :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hzball).trans_le (min_le_left _ _))
  have hzη : z ∈ Metric.ball q η := by
    have hzsmall := (Metric.mem_ball.mp hzball).trans_le (min_le_right R (η - dist q p))
    have htri := dist_triangle z p q
    rw [dist_comm p q] at htri
    exact Metric.mem_ball.mpr (by linarith)
  have hznegative : z ∈ Tiling.negativeSide p d := by
    have h := Tiling.mem_positiveSide.mp hzpositive
    apply Tiling.mem_negativeSide.mpr
    simp only [Tiling.signedSide, Tiling.planarCross, Complex.neg_re, Complex.neg_im] at h ⊢
    linarith
  have hzside : z ∈ Tiling.negativeSide q d := by
    have hpos := Tiling.mem_positiveSide.mp hqpositive
    have hneg := Tiling.mem_negativeSide.mp hznegative
    apply Tiling.mem_negativeSide.mpr
    dsimp only [Tiling.signedSide] at hpos hneg ⊢
    linarith
  let U := Metric.ball q η ∩ Tiling.negativeSide q d
  have hUopen : IsOpen U := Metric.isOpen_ball.inter (Tiling.isOpen_negativeSide q d)
  have hUS : U ⊆ ψ s +ᵥ Kφ.support := by
    intro w hw
    exact ((Set.ext_iff.mp hstrip w).mpr
      ⟨Tiling.mem_negativeHalfPlane.mpr (Tiling.mem_negativeSide.mp hw.2).le, hw.1⟩).1
  have hzopen : z ∈ ψ s +ᵥ Kφ.openCarrier := by
    have hUint := hUopen.subset_interior_iff.mpr hUS
    have hzint := hUint ⟨hzη, hzside⟩
    simpa only [PolygonalRegion.openCarrier, interior_vadd] using hzint
  have hst : s = t := by
    by_contra hst
    exact Set.disjoint_left.mp (hsingle s hs hst) (hinside ⟨hzR, hznegative⟩) hzopen
  have hqS : q ∈ ψ s +ᵥ Kφ.support :=
    ((Set.ext_iff.mp hstrip q).mpr
      ⟨Tiling.mem_negativeHalfPlane.mpr (Tiling.signedSide_self q d).le,
        Metric.mem_ball_self hηpos⟩).1
  rw [hst] at hqS
  have hqneg := ((Set.ext_iff.mp hown q).mp ⟨hqS, hqR⟩).1
  exact (not_le_of_gt (Tiling.mem_positiveSide.mp hqpositive))
    (Tiling.mem_negativeHalfPlane.mp hqneg)


private theorem packingSol_rationalPrimitive_actualSourceOccurrence
    (K : PolygonalRegion) (T : Set Plane) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (n : RationalNormal) (t : Plane) (ht : t ∈ T)
    (e : Plane × Plane) (he : e ∈ E) (hparallel : normalEval n (e.2 - e.1) = 0) :
    ∃ (a : Plane) (q : ℝ × ℝ) (positive : Bool),
      q ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) 0 positive ∧
      ((t + e.1 = a + q.1 • packingSol_rationalTangent n ∧
        t + e.2 = a + q.2 • packingSol_rationalTangent n) ∨
       (t + e.2 = a + q.1 • packingSol_rationalTangent n ∧
        t + e.1 = a + q.2 • packingSol_rationalTangent n)) ∧
      ∀ u ∈ Ioo q.1 q.2,
        if positive then positiveEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
          (a + u • packingSol_rationalTangent n)
        else negativeEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
          (a + u • packingSol_rationalTangent n) := by
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hspan : normalDirection n = Submodule.span ℝ ({d} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one (normalDirection_rational n).1
      (packingSol_rationalTangent_mem n) hd
  have hmem : e.2 - e.1 ∈ Submodule.span ℝ ({d} : Set Plane) := by
    rw [← hspan]
    exact (normalDirection_mem_iff n _).mpr hparallel
  obtain ⟨L, hL⟩ := Submodule.mem_span_singleton.mp hmem
  have hLne : L ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hL
    exact (hE e he).1 (sub_eq_zero.mp hL.symm).symm
  have hfrontier : ∀ f ∈ E, segment ℝ f.1 f.2 ⊆ frontier K.support :=
    fun f hf => (hE f hf).2.1
  rcases lt_or_gt_of_ne hLne with hneg | hpos
  · let a := t + e.2
    let q : ℝ × ℝ := (0, -L)
    have hq : q.1 < q.2 := by dsimp only [q]; linarith
    have hcoords : (t + e.1 = a + q.1 • d ∧ t + e.2 = a + q.2 • d) ∨
        (t + e.2 = a + q.1 • d ∧ t + e.1 = a + q.2 • d) := by
      right
      constructor
      · simp [a, q]
      · dsimp only [a, q]
        calc
          t + e.1 = (t + e.2) - (e.2 - e.1) := by abel
          _ = (t + e.2) + (-L) • d := by rw [← hL]; module
    obtain ⟨positive, _, hfamily, hgerms⟩ := packingSol_primitiveOccurrence_actualSourceJ
      K T E hfrontier a d t hd ht e he q hq hcoords (hE e he).2.2 0
      ⟨le_rfl, hq.le⟩
    exact ⟨a, q, positive, hfamily, hcoords, hgerms⟩
  · let a := t + e.1
    let q : ℝ × ℝ := (0, L)
    have hq : q.1 < q.2 := hpos
    have hcoords : (t + e.1 = a + q.1 • d ∧ t + e.2 = a + q.2 • d) ∨
        (t + e.2 = a + q.1 • d ∧ t + e.1 = a + q.2 • d) := by
      left
      constructor
      · simp [a, q]
      · dsimp only [a, q]
        calc
          t + e.2 = (t + e.1) + (e.2 - e.1) := by abel
          _ = (t + e.1) + L • d := by rw [← hL]
    obtain ⟨positive, _, hfamily, hgerms⟩ := packingSol_primitiveOccurrence_actualSourceJ
      K T E hfrontier a d t hd ht e he q hq hcoords (hE e he).2.2 0
      ⟨le_rfl, hq.le⟩
    exact ⟨a, q, positive, hfamily, hcoords, hgerms⟩


private theorem packingSol_uniformActualMappedPrimitiveQuery
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) (n : RationalNormal) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ t ∈ T, ∀ e ∈ E, normalEval n (e.2 - e.1) = 0 →
      ∃ (a : Plane) (q : ℝ × ℝ) (positive : Bool),
        q ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) 0 positive ∧
        ((t + e.1 = a + q.1 • packingSol_rationalTangent n ∧
          t + e.2 = a + q.2 • packingSol_rationalTangent n) ∨
         (t + e.2 = a + q.1 • packingSol_rationalTangent n ∧
          t + e.1 = a + q.2 • packingSol_rationalTangent n)) ∧
        (∀ u ∈ Ioo q.1 q.2, if positive then
          positiveEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
            (a + u • packingSol_rationalTangent n)
          else negativeEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
            (a + u • packingSol_rationalTangent n)) ∧
        (φ q.1 : ℝ) < (φ q.2 : ℝ) ∧
        (∀ z ∈ openSegment ℝ (deformPoint φ t + deformPoint φ e.1)
          (deformPoint φ t + deformPoint φ e.2), ∃ u ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ),
            z = deformPoint φ a + u • packingSol_rationalTangent n) ∧
        (∀ u ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ), if positive then
          positiveEdgeGerm (deformPoint φ t +ᵥ Kφ.support) (packingSol_rationalTangent n)
            (deformPoint φ a + u • packingSol_rationalTangent n)
          else negativeEdgeGerm (deformPoint φ t +ᵥ Kφ.support) (packingSol_rationalTangent n)
            (deformPoint φ a + u • packingSol_rationalTangent n)) := by
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨Fc, εc, hεc, hchain⟩ :=
    packingSol_uniformActualSourceCarrierTransport K T htile E hE hcover d hd
  obtain ⟨Fg, εg, hεg, hgerms⟩ :=
    packingSol_signedOccurrence_targetGerms K P hP E hrat hprimitive hcover
  refine ⟨Fc ∪ Fg, min εc εg, lt_min hεc hεg, ?_⟩
  intro φ hφ Kφ hKφ t ht e he hparallel
  have hφc : IsFiniteApproximation Fc εc φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_left _ hz)).trans_le (min_le_left _ _)
  have hφg : IsFiniteApproximation Fg εg φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_right _ hz)).trans_le (min_le_right _ _)
  obtain ⟨a, q, positive, hq, hcoords, hsource⟩ :=
    packingSol_rationalPrimitive_actualSourceOccurrence K T E
      (fun e he => ⟨(hE e he).1, (hE e he).2.2.2.1, (hE e he).2.2.2.2.2⟩)
      n t ht e he hparallel
  have hzero : (0 : ℝ) ∈
      {u : ℝ | a + u • d ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support} :=
    connectedComponentIn_nonempty_iff.mp ⟨q.1, hq.2 ⟨le_rfl, hq.1.1.le⟩⟩
  have hr : a + (0 : ℝ) • d ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support := hzero
  have hbound := (hchain φ hφc a 0 q.1 q.2 hr hq.1.1 hq.2 positive).2.1
  have horder : (φ q.1 : ℝ) < (φ q.2 : ℝ) := by
    have h := (hbound q.1 ⟨q, hq, Or.inl rfl⟩ q.2 ⟨q, hq, Or.inr rfl⟩ hq.1.1).1
    linarith [hq.1.1]
  have mapEndpoint {v : Plane} {u : ℝ} (hv : t + v = a + u • d) :
      deformPoint φ t + deformPoint φ v = deformPoint φ a + (φ u : ℝ) • d := by
    calc
      _ = deformPoint φ (t + v) := ((deformPointLinear φ).map_add _ _).symm
      _ = deformPoint φ (a + u • d) := by rw [hv]
      _ = _ := packingSol_deform_rationalCarrierParameter φ n a u
  refine ⟨a, q, positive, hq, hcoords, hsource, horder, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ openSegment ℝ (deformPoint φ a + (φ q.1 : ℝ) • d)
        (deformPoint φ a + (φ q.2 : ℝ) • d) := by
      rcases hcoords with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · simpa only [mapEndpoint hl, mapEndpoint hr] using hz
      · simpa only [mapEndpoint hl, mapEndpoint hr, openSegment_symm] using hz
    rw [openSegment_eq_image_lineMap] at hz'
    obtain ⟨v, hv, hvz⟩ := hz'
    let u : ℝ := (1 - v) * (φ q.1 : ℝ) + v * (φ q.2 : ℝ)
    have hu : u ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ) := by
      dsimp only [u]
      constructor <;> nlinarith [hv.1, hv.2, horder]
    refine ⟨u, hu, ?_⟩
    rw [← hvz]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    dsimp only [u]
    module
  · intro u hu
    exact hgerms φ hφg Kφ hKφ n a t e he q hq.1.1 hcoords
      (hE e he).2.2.2.2.2 positive hsource u hu


private theorem packingSol_negativeGerm_selects_parallelStrip
    (S : Set Plane) (p d w : Plane) (hd : d ≠ 0) (c : ℝ) (hc : c ≠ 0)
    (hdir : w = c • d) (η : ℝ) (hη : 0 < η)
    (hstrip : S ∩ Metric.ball p η = Tiling.positiveHalfPlane p w ∩ Metric.ball p η ∨
      S ∩ Metric.ball p η = Tiling.negativeHalfPlane p w ∩ Metric.ball p η)
    (hgerm : negativeEdgeGerm S d p) :
    S ∩ Metric.ball p η = Tiling.negativeHalfPlane p d ∩ Metric.ball p η := by
  have hstrip' : S ∩ Metric.ball p η = Tiling.positiveHalfPlane p d ∩ Metric.ball p η ∨
      S ∩ Metric.ball p η = Tiling.negativeHalfPlane p d ∩ Metric.ball p η := by
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · have hside (z : Plane) : Tiling.signedSide p (-d) z = -Tiling.signedSide p d z := by
        simp only [Tiling.signedSide, Tiling.planarCross, Complex.neg_re, Complex.neg_im]
        ring
      have hhalfPos : Tiling.positiveHalfPlane p (-d) = Tiling.negativeHalfPlane p d := by
        ext z
        simp only [Tiling.mem_positiveHalfPlane, Tiling.mem_negativeHalfPlane, hside]
        exact neg_nonneg
      have hhalfNeg : Tiling.negativeHalfPlane p (-d) = Tiling.positiveHalfPlane p d := by
        ext z
        simp only [Tiling.mem_positiveHalfPlane, Tiling.mem_negativeHalfPlane, hside]
        exact neg_nonpos
      have hdir' : w = (-c) • (-d) := by rw [hdir]; module
      have hscale := orientedHalfPlanes_positiveScale p (-d) (-c) (neg_pos.mpr hneg)
      simpa only [hdir', hscale.1, hscale.2, hhalfPos, hhalfNeg] using hstrip.symm
    · have hscale := orientedHalfPlanes_positiveScale p d c hpos
      simpa only [hdir, hscale.1, hscale.2] using hstrip
  rcases hstrip' with hpositive | hnegative
  · exact False.elim (positive_negative_edgeGerms_disjoint hd ⟨η, hη, hpositive⟩ hgerm)
  · exact hnegative


private theorem packingSol_negativeStrip_vadd
    (S : Set Plane) (s p d : Plane) (η : ℝ)
    (hstrip : S ∩ Metric.ball p η = Tiling.negativeHalfPlane p d ∩ Metric.ball p η) :
    (s +ᵥ S) ∩ Metric.ball (s + p) η =
      Tiling.negativeHalfPlane (s + p) d ∩ Metric.ball (s + p) η := by
  ext z
  have hball : dist z (s + p) = dist (z - s) p := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have hside : Tiling.signedSide (s + p) d z = Tiling.signedSide p d (z - s) := by
    simp only [Tiling.signedSide, Tiling.planarCross, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    ring
  have hS : z ∈ s +ᵥ S ↔ z - s ∈ S := by
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    congr 1
    abel
  simp only [Set.mem_inter_iff]
  rw [hS, Metric.mem_ball, hball, Tiling.mem_negativeHalfPlane, hside]
  simpa only [Set.mem_inter_iff, Metric.mem_ball, Tiling.mem_negativeHalfPlane] using
    (Set.ext_iff.mp hstrip (z - s))


private theorem vertexExclusionSol_sameCarrier_side
    (a d : Plane) (u v : ℝ) (z : Plane) :
    Tiling.signedSide (a + u • d) d z = Tiling.signedSide (a + v • d) d z := by
  simp only [Tiling.signedSide, Tiling.planarCross, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring


private theorem vertexExclusionSol_inwardLabel_of_frame
    (Kφ : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (c : Plane) (hc : c ∈ T) (x : Plane)
    (hsingle : ∀ s ∈ T, s ≠ c →
      Disjoint (connectedComponentIn (ψ c +ᵥ Kφ.openCarrier) x)
        (ψ s +ᵥ Kφ.openCarrier))
    (a d : Plane) (hd : d ≠ 0) (z0 : ℝ) (R : ℝ) (hR : 0 < R)
    (hframe : Metric.ball (a + z0 • d) R ∩ Tiling.negativeSide (a + z0 • d) d ⊆
      connectedComponentIn (ψ c +ᵥ Kφ.openCarrier) x)
    (v : ℝ) (hvball : a + v • d ∈ Metric.ball (a + z0 • d) R)
    (s : Plane) (hs : s ∈ T)
    (hneg : negativeEdgeGerm (ψ s +ᵥ Kφ.support) d (a + v • d)) : s = c := by
  by_contra hsc
  obtain ⟨ρ, hρ, hEq⟩ := hneg
  let p := a + z0 • d
  let q := a + v • d
  have hmargin : 0 < R - dist q p := by linarith [Metric.mem_ball.mp hvball]
  obtain ⟨w, hwball, hwside⟩ := packingSol_positiveHalfBall_point q (-d)
    (neg_ne_zero.mpr hd) (min ρ (R - dist q p)) (lt_min hρ hmargin)
  have hwρ : w ∈ Metric.ball q ρ :=
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hwball).trans_le (min_le_left _ _))
  have hwR : w ∈ Metric.ball p R := by
    have hsmall := (Metric.mem_ball.mp hwball).trans_le (min_le_right ρ (R - dist q p))
    exact Metric.mem_ball.mpr (by linarith [dist_triangle w q p])
  have hwnegative : w ∈ Tiling.negativeSide q d := by
    have hpos := Tiling.mem_positiveSide.mp hwside
    apply Tiling.mem_negativeSide.mpr
    have hn : Tiling.signedSide q (-d) w = -Tiling.signedSide q d w := by
      simp only [Tiling.signedSide, Tiling.planarCross, Complex.neg_re, Complex.neg_im]
      ring
    rw [hn] at hpos
    linarith
  have hwsidep : w ∈ Tiling.negativeSide p d := by
    apply Tiling.mem_negativeSide.mpr
    rw [vertexExclusionSol_sameCarrier_side a d z0 v]
    exact Tiling.mem_negativeSide.mp hwnegative
  let U := Metric.ball q ρ ∩ Tiling.negativeSide q d
  have hUopen : IsOpen U := Metric.isOpen_ball.inter (Tiling.isOpen_negativeSide q d)
  have hUS : U ⊆ ψ s +ᵥ Kφ.support := by
    intro z hz
    exact ((Set.ext_iff.mp hEq z).mpr
      ⟨Tiling.mem_negativeHalfPlane.mpr (Tiling.mem_negativeSide.mp hz.2).le, hz.1⟩).1
  have hUinside : U ⊆ ψ s +ᵥ Kφ.openCarrier := by
    simpa only [PolygonalRegion.openCarrier, interior_vadd] using
      hUopen.subset_interior_iff.mpr hUS
  exact Set.disjoint_left.mp (hsingle s hs hsc)
    (hframe ⟨hwR, hwsidep⟩) (hUinside ⟨hwρ, hwnegative⟩)


private theorem vertexExclusionSol_occurrence_mappedOpen
    (φ : ℝ →ₗ[ℚ] ℚ) (n : RationalNormal) (a t : Plane)
    (e : Plane × Plane) (q : ℝ × ℝ)
    (hcoords : (t + e.1 = a + q.1 • packingSol_rationalTangent n ∧
      t + e.2 = a + q.2 • packingSol_rationalTangent n) ∨
      (t + e.2 = a + q.1 • packingSol_rationalTangent n ∧
      t + e.1 = a + q.2 • packingSol_rationalTangent n))
    (u : ℝ) (hu : u ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ)) :
    deformPoint φ a + u • packingSol_rationalTangent n ∈
      openSegment ℝ (deformPoint φ t + deformPoint φ e.1)
        (deformPoint φ t + deformPoint φ e.2) := by
  have mapEnd {v : Plane} {s : ℝ} (hv : t + v = a + s • packingSol_rationalTangent n) :
      deformPoint φ t + deformPoint φ v =
        deformPoint φ a + (φ s : ℝ) • packingSol_rationalTangent n := by
    calc
      _ = deformPoint φ (t + v) := ((deformPointLinear φ).map_add t v).symm
      _ = deformPoint φ (a + s • packingSol_rationalTangent n) := by rw [hv]
      _ = _ := packingSol_deform_rationalCarrierParameter φ n a s
  rcases hcoords with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [mapEnd hl, mapEnd hr]
    exact carrierParameter_mem_openSegment _ _ _ _ u (hu.1.trans hu.2) hu
  · rw [mapEnd hl, mapEnd hr, openSegment_symm]
    exact carrierParameter_mem_openSegment _ _ _ _ u (hu.1.trans hu.2) hu


private theorem vertexExclusionSol_overlap_two_points
    {lo hi l u : ℝ} (h : (Ioo lo hi ∩ Ioo l u).Nonempty) :
    ∃ x y : ℝ, x ≠ y ∧ x ∈ Ioo lo hi ∩ Ioo l u ∧ y ∈ Ioo lo hi ∩ Ioo l u := by
  obtain ⟨z, hz⟩ := h
  have hbounds : max lo l < min hi u :=
    (max_lt_iff.mpr ⟨hz.1.1, hz.2.1⟩).trans (lt_min hz.1.2 hz.2.2)
  obtain ⟨x, hxL, hxU⟩ := exists_between hbounds
  obtain ⟨y, hxy, hyU⟩ := exists_between hxU
  refine ⟨x, y, ne_of_lt hxy, ?_, ?_⟩
  · exact ⟨⟨(le_max_left _ _).trans_lt hxL, hxU.trans_le (min_le_left _ _)⟩,
      ⟨(le_max_right _ _).trans_lt hxL, hxU.trans_le (min_le_right _ _)⟩⟩
  · exact ⟨⟨(le_max_left _ _).trans_lt (hxL.trans hxy), hyU.trans_le (min_le_left _ _)⟩,
      ⟨(le_max_right _ _).trans_lt (hxL.trans hxy), hyU.trans_le (min_le_right _ _)⟩⟩


private theorem vertexExclusionSol_uniform_patch_avoids_all_oldVertices
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (n : RationalNormal) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ a : Plane, ∀ r : ℝ, ∀ c ∈ T, ∀ b ∈ T, c ≠ b →
      ∀ eC ∈ E, ∀ eB ∈ E,
      ∀ qC ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) r false,
      ∀ qB ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) r true,
      ((c + eC.1 = a + qC.1 • packingSol_rationalTangent n ∧
        c + eC.2 = a + qC.2 • packingSol_rationalTangent n) ∨
       (c + eC.2 = a + qC.1 • packingSol_rationalTangent n ∧
        c + eC.1 = a + qC.2 • packingSol_rationalTangent n)) →
      ((b + eB.1 = a + qB.1 • packingSol_rationalTangent n ∧
        b + eB.2 = a + qB.2 • packingSol_rationalTangent n) ∨
       (b + eB.2 = a + qB.1 • packingSol_rationalTangent n ∧
        b + eB.1 = a + qB.2 • packingSol_rationalTangent n)) →
      (∀ u ∈ Ioo qC.1 qC.2, negativeEdgeGerm (c +ᵥ K.support)
        (packingSol_rationalTangent n) (a + u • packingSol_rationalTangent n)) →
      (∀ u ∈ Ioo qB.1 qB.2, positiveEdgeGerm (b +ᵥ K.support)
        (packingSol_rationalTangent n) (a + u • packingSol_rationalTangent n)) →
      ∀ x ∈ deformPoint φ c +ᵥ Kφ.openCarrier,
      (∀ s ∈ T, s ≠ c → Disjoint
        (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x)
        (deformPoint φ s +ᵥ Kφ.openCarrier)) →
      ∀ z0 R : ℝ, 0 < R →
      (Metric.ball (deformPoint φ a + z0 • packingSol_rationalTangent n) R ∩
        Tiling.negativeSide (deformPoint φ a + z0 • packingSol_rationalTangent n)
          (packingSol_rationalTangent n) ⊆
        connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x) →
      ∀ L H : ℝ, L < H →
      Ioo L H ⊆ Ioo (φ qC.1 : ℝ) (φ qC.2 : ℝ) →
      Ioo L H ⊆ Ioo (φ qB.1 : ℝ) (φ qB.2 : ℝ) →
      (∀ v ∈ Ioo L H, deformPoint φ a + v • packingSol_rationalTangent n ∈
        Metric.ball (deformPoint φ a + z0 • packingSol_rationalTangent n) R) →
      (∀ v ∈ Ioo L H, deformPoint φ a + v • packingSol_rationalTangent n ∉
        deformPoint φ c +ᵥ (deformPoint φ '' Tiling.vertexSet K.support)) →
      (∀ v ∈ Ioo L H, deformPoint φ a + v • packingSol_rationalTangent n ∉
        deformPoint φ b +ᵥ (deformPoint φ '' Tiling.vertexSet K.support)) →
      ∀ v ∈ Ioo L H, deformPoint φ a + v • packingSol_rationalTangent n ∉
        deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T := by
  classical
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨F0, ε0, ρ, hε0, hρ, hstar⟩ :=
    packingSol_singleComponent_halfStar_tangentRays K P T hP htile
  obtain ⟨F1, ε1, hε1, htarget⟩ :=
    packingSol_signedOccurrence_targetGerms K P hP E hrat hprimitive hcover
  obtain ⟨F2, ε2, hε2, hpartner⟩ :=
    packingSol_actualSameJ_oppositeOccurrence K P T hP htile E hE hrat hcover n
  obtain ⟨F3, ε3, hε3, hrecover⟩ :=
    packingSol_uniformMappedPrimitive_oldCarrierJRecovery K P hP E hrat hprimitive hcover
  obtain ⟨F4, ε4, hε4, hunique⟩ :=
    packingSol_uniformSameJ_sameSign_labelUnique K T htile E hE hcover d hd
  obtain ⟨F5, ε5, hε5, hchain⟩ :=
    packingSol_uniformActualSourceCarrierTransport K T htile E hE hcover d hd
  let F := F0 ∪ (F1 ∪ (F2 ∪ (F3 ∪ (F4 ∪ F5))))
  let ε := min ε0 (min ε1 (min ε2 (min ε3 (min ε4 ε5))))
  refine ⟨F, ε, lt_min hε0 (lt_min hε1 (lt_min hε2 (lt_min hε3 (lt_min hε4 hε5)))), ?_⟩
  intro φ hφ Kφ hKφ a r c hc b hb hcb eC heC eB heB qC hqC qB hqB
    hcoordsC hcoordsB hsourceC hsourceB x hx hsingle z0 R hR hframe L H hLH
    hsubC hsubB hball hnotC hnotB v hv
  have approx (A : Finset ℝ) (δ : ℝ) (hA : A ⊆ F) (hδ : ε ≤ δ) :
      IsFiniteApproximation A δ φ := finiteApproximation_strengthen A F δ ε φ hA hδ hφ
  have hφ0 : IsFiniteApproximation F0 ε0 φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto) (min_le_left _ _)
  have hφ1 : IsFiniteApproximation F1 ε1 φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans (min_le_left _ _))
  have hφ2 : IsFiniteApproximation F2 ε2 φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hφ3 : IsFiniteApproximation F3 ε3 φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hφ4 : IsFiniteApproximation F4 ε4 φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))
  have hφ5 : IsFiniteApproximation F5 ε5 φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))))
  intro hvertex
  obtain ⟨p, hpV, hpmap⟩ := hvertex
  have hstarNotC : ∀ s ∈ T, p ∈ s +ᵥ Tiling.vertexSet K.support → s ≠ c := by
    intro s hs hps hsc
    subst s
    obtain ⟨w, hw, hwp⟩ := Set.mem_vadd_set.mp hps
    apply hnotC v hv
    refine Set.mem_vadd_set.mpr ⟨deformPoint φ w, ⟨w, hw, rfl⟩, ?_⟩
    rw [← hpmap, ← hwp]
    exact ((deformPointLinear φ).map_add c w).symm
  let ℓ := Tiling.planarCrossCLM d
  have hℓ : ℓ ≠ 0 := by
    intro h
    have hvalue := congrArg (fun f : Plane →L[ℝ] ℝ => f (d * Complex.I)) h
    have hcross : Tiling.planarCross d (d * Complex.I) = Complex.normSq d := by
      simp [Tiling.planarCross, Complex.normSq_apply, Complex.mul_I_re, Complex.mul_I_im]
    have : Complex.normSq d = 0 := by simpa only [ℓ, Tiling.planarCrossCLM_apply,
      hcross, ContinuousLinearMap.zero_apply] using hvalue
    exact hd (Complex.normSq_eq_zero.mp this)
  have hmargin : 0 < R - dist (deformPoint φ p) (deformPoint φ a + z0 • d) := by
    rw [hpmap]
    linarith [Metric.mem_ball.mp (hball v hv)]
  have hlocalFrame : Metric.ball (deformPoint φ p)
      (R - dist (deformPoint φ p) (deformPoint φ a + z0 • d)) ∩
      {y | ℓ (y - deformPoint φ p) < 0} ⊆
      connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x := by
    intro y hy
    apply hframe
    constructor
    · have hsmall := Metric.mem_ball.mp hy.1
      have htri := dist_triangle y (deformPoint φ p) (deformPoint φ a + z0 • d)
      exact Metric.mem_ball.mpr (by linarith)
    · apply Tiling.mem_negativeSide.mpr
      rw [vertexExclusionSol_sameCarrier_side (deformPoint φ a) d z0 v]
      rw [← hpmap]
      have hside : ℓ (y - deformPoint φ p) = Tiling.signedSide (deformPoint φ p) d y := by
        simp only [ℓ, Tiling.planarCrossCLM_apply, Tiling.signedSide, Tiling.planarCross,
          Complex.sub_re, Complex.sub_im]
        ring
      rw [← hside]
      exact hy.2
  obtain ⟨f, u, hfu, hhalf, hker, hrays⟩ := hstar φ hφ0 Kφ hKφ p hpV c hc x hx
    hsingle hstarNotC ℓ hℓ _ hmargin hlocalFrame
  have hℓd : ℓ d = 0 := by simp [ℓ, Tiling.planarCross]; ring
  obtain ⟨j, hj, hpj, hray⟩ := hrays d hℓd
  have hjc : j ≠ c := hstarNotC j hj hpj
  let w := -j + p
  have hw : w ∈ Tiling.vertexSet K.support := Set.mem_vadd_set_iff_neg_vadd_mem.mp hpj
  let Rray := ρ / (‖d‖ + 1)
  have hRray : 0 < Rray := by dsimp [Rray]; positivity
  have hrayOld : ∀ t : ℝ, 0 < t → t < Rray → w + t • d ∈ frontier K.support := by
    intro t ht htR
    have hnorm : dist (t • d) 0 < ρ := by
      rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have hn := (lt_div_iff₀ (by positivity : 0 < ‖d‖ + 1)).mp htR
      nlinarith [norm_nonneg d]
    have hfr := (hray t ht hnorm).1
    rw [frontier, closure_vadd, interior_vadd, ← Set.vadd_set_sdiff] at hfr
    simpa only [w, vadd_eq_add, add_assoc, frontier] using
      Set.mem_vadd_set_iff_neg_vadd_mem.mp hfr
  obtain ⟨eJ, heJ, len, hlen, hends⟩ := sourceRay_intrinsicEdge_positiveEndpoint
    K.isPolygonal hw hd hRray hrayOld E hprimitive hcover
  have hcoordsJ : (j + eJ.1 = p + (0 : ℝ) • d ∧ j + eJ.2 = p + len • d) ∨
      (j + eJ.2 = p + (0 : ℝ) • d ∧ j + eJ.1 = p + len • d) := by
    rcases hends with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · left; rw [hl, hr]; dsimp only [w]; constructor <;> module
    · right; rw [hl, hr]; dsimp only [w]; constructor <;> module
  obtain ⟨positive, hpSource, hqJ, hsourceJ⟩ := packingSol_primitiveOccurrence_actualSourceJ
    K T E (fun e he => (hE e he).2.2.2.1) p d j hd hj eJ heJ (0, len) hlen
    hcoordsJ (hE eJ heJ).2.2.2.2.2 0 ⟨le_rfl, hlen.le⟩
  have hpositiveLen : 0 < (φ len : ℝ) := by
    have hbound := (hchain φ hφ5 p 0 0 len hpSource hlen hqJ.2 positive).2.1
      0 ⟨(0, len), hqJ, Or.inl rfl⟩ len ⟨(0, len), hqJ, Or.inr rfl⟩ hlen
    simp only [map_zero, Rat.cast_zero, sub_zero] at hbound
    linarith [hbound.1]
  let hi := min (φ len : ℝ) (H - v)
  have hhi : 0 < hi := lt_min hpositiveLen (sub_pos.mpr hv.2)
  have hsubJ : Ioo 0 hi ⊆ Ioo (φ (0 : ℝ) : ℝ) (φ len : ℝ) := by
    intro t ht
    simp only [map_zero, Rat.cast_zero]
    exact ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have hquery (t : ℝ) (ht : t ∈ Ioo 0 hi) : v + t ∈ Ioo L H := by
    exact ⟨by linarith [hv.1, ht.1], by linarith [ht.2.trans_le (min_le_right _ _)]⟩
  have hpoint (t : ℝ) : deformPoint φ p + t • d = deformPoint φ a + (v + t) • d := by
    rw [hpmap]; module
  have hsign : positive = true := by
    cases positive with
    | true => rfl
    | false =>
      obtain ⟨t, ht⟩ := Set.nonempty_Ioo.mpr hhi
      have hneg := htarget φ hφ1 Kφ hKφ n p j eJ heJ (0, len) hlen hcoordsJ
        (hE eJ heJ).2.2.2.2.2 false hsourceJ t (hsubJ ht)
      rw [hpoint] at hneg
      have heq := vertexExclusionSol_inwardLabel_of_frame Kφ T (deformPoint φ) c hc x
        hsingle (deformPoint φ a) d hd z0 R hR hframe (v + t)
        (hball _ (hquery t ht)) j hj hneg
      exact False.elim (hjc heq)
  subst positive
  obtain ⟨s, hs, hsj, eN, heN, qN, hqN, hcoordsN, hsourceN, hoverlap⟩ :=
    hpartner φ hφ2 Kφ hKφ p 0 0 len hpSource hlen hqJ.2 true (0, len) hqJ
      j hj eJ heJ hcoordsJ hsourceJ 0 hi hhi hsubJ
  obtain ⟨t, htquery, htN⟩ := hoverlap
  have hnegN := htarget φ hφ1 Kφ hKφ n p s eN heN qN hqN.1.1 hcoordsN
    (hE eN heN).2.2.2.2.2 false hsourceN t htN
  rw [hpoint] at hnegN
  have hsc := vertexExclusionSol_inwardLabel_of_frame Kφ T (deformPoint φ) c hc x
    hsingle (deformPoint φ a) d hd z0 R hR hframe (v + t)
    (hball _ (hquery t htquery)) s hs hnegN
  subst s
  obtain ⟨t1, t2, ht12, ht1, ht2⟩ := vertexExclusionSol_overlap_two_points ⟨t, htquery, htN⟩
  have hdistPoints : deformPoint φ a + (v + t1) • d ≠
      deformPoint φ a + (v + t2) • d := by
    intro h
    have hscalar := smul_left_injective ℝ hd (add_left_cancel h)
    exact ht12 (add_left_cancel hscalar)
  have hCopen (z : ℝ) (hz : z ∈ Ioo 0 hi) :
      deformPoint φ a + (v + z) • d ∈ openSegment ℝ
        (deformPoint φ c + deformPoint φ eC.1) (deformPoint φ c + deformPoint φ eC.2) :=
    vertexExclusionSol_occurrence_mappedOpen φ n a c eC qC hcoordsC _ (hsubC (hquery z hz))
  have hNopen (z : ℝ) (hz : z ∈ Ioo (φ qN.1 : ℝ) (φ qN.2 : ℝ)) :
      deformPoint φ a + (v + z) • d ∈ openSegment ℝ
        (deformPoint φ c + deformPoint φ eN.1) (deformPoint φ c + deformPoint φ eN.2) := by
    rw [← hpoint]
    exact vertexExclusionSol_occurrence_mappedOpen φ n p c eN qN hcoordsN z hz
  obtain ⟨shift, hpanchor, hJ⟩ := hrecover φ hφ3 Kφ hKφ T a p d c r 0 false false
    qC hqC qN hqN eC heC eN heN hcoordsC hcoordsN
    _ _ hdistPoints (hCopen t1 ht1.1) (hNopen t1 ht1.2)
    (hCopen t2 ht2.1) (hNopen t2 ht2.2)
  obtain ⟨hqB', hcoordsB', hsourceB'⟩ := packingSol_actualOccurrence_reanchor_sameJ
    K T E a p d b r 0 shift true hpanchor hJ hb eB heB qB hqB hcoordsB hsourceB
  have hreanchor := packingSol_realMappedCarrier_reanchor φ n a p shift hpanchor
  have hzB : v + t ∈ Ioo (φ qB.1 : ℝ) (φ qB.2 : ℝ) := hsubB (hquery t htquery)
  have hzB' := hreanchor.2 qB (v + t) hzB
  have htargetscalar : (v + t) - (φ shift : ℝ) = t := by
    have heq := (hreanchor.1 (v + t)).symm.trans (hpoint t).symm
    have heq' : deformPoint φ p + ((v + t) - (φ shift : ℝ)) • d =
        deformPoint φ p + t • d := heq
    exact smul_left_injective ℝ hd (add_left_cancel heq')
  rw [htargetscalar] at hzB'
  obtain ⟨_, hjb⟩ := hunique φ hφ4 p 0 0 len hpSource hlen hqJ.2 true
    (0, len) hqJ (qB.1 - shift, qB.2 - shift) hqB' j hj b hb hsourceJ hsourceB'
    t (hsubJ htquery) hzB'
  apply hnotB v hv
  rw [← hpmap]
  rw [hjb] at hpj
  obtain ⟨wB, hwB, hwBp⟩ := Set.mem_vadd_set.mp hpj
  refine Set.mem_vadd_set.mpr ⟨deformPoint φ wB, ⟨wB, hwB, rfl⟩, ?_⟩
  rw [← hwBp]
  exact ((deformPointLinear φ).map_add b wB).symm


private theorem packingSol_uniformActualNegativeOccurrence_near
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) (n : RationalNormal) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ a : Plane, ∀ r : ℝ, ∀ positive : Bool,
      ∀ q ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) r positive,
      ∀ t ∈ T, ∀ e ∈ E,
      ((t + e.1 = a + q.1 • packingSol_rationalTangent n ∧
        t + e.2 = a + q.2 • packingSol_rationalTangent n) ∨
       (t + e.2 = a + q.1 • packingSol_rationalTangent n ∧
        t + e.1 = a + q.2 • packingSol_rationalTangent n)) →
      (∀ u ∈ Ioo q.1 q.2, if positive then
        positiveEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
          (a + u • packingSol_rationalTangent n)
        else negativeEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
          (a + u • packingSol_rationalTangent n)) →
      ∀ p : Plane, ∀ R : ℝ, ∀ v ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ),
      deformPoint φ a + v • packingSol_rationalTangent n ∈ Metric.ball p R →
      deformPoint φ a + v • packingSol_rationalTangent n ∈
        Tiling.positiveSide p (packingSol_rationalTangent n) →
      ∃ s ∈ T, ∃ eN ∈ E,
      ∃ qN ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) r false,
        ((s + eN.1 = a + qN.1 • packingSol_rationalTangent n ∧
          s + eN.2 = a + qN.2 • packingSol_rationalTangent n) ∨
         (s + eN.2 = a + qN.1 • packingSol_rationalTangent n ∧
          s + eN.1 = a + qN.2 • packingSol_rationalTangent n)) ∧
        (∀ u ∈ Ioo qN.1 qN.2, negativeEdgeGerm (s +ᵥ K.support)
          (packingSol_rationalTangent n) (a + u • packingSol_rationalTangent n)) ∧
        ∃ u ∈ Ioo (φ qN.1 : ℝ) (φ qN.2 : ℝ),
          deformPoint φ a + u • packingSol_rationalTangent n ∈ Metric.ball p R ∧
          deformPoint φ a + u • packingSol_rationalTangent n ∈
            Tiling.positiveSide p (packingSol_rationalTangent n) ∧
          negativeEdgeGerm (deformPoint φ s +ᵥ Kφ.support)
            (packingSol_rationalTangent n)
            (deformPoint φ a + u • packingSol_rationalTangent n) := by
  let d := packingSol_rationalTangent n
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨Fp, εp, hεp, hpartner⟩ :=
    packingSol_actualSameJ_oppositeOccurrence K P T hP htile E hE hrat hcover n
  obtain ⟨Fg, εg, hεg, hgerms⟩ :=
    packingSol_signedOccurrence_targetGerms K P hP E hrat hprimitive hcover
  refine ⟨Fp ∪ Fg, min εp εg, lt_min hεp hεg, ?_⟩
  intro φ hφ Kφ hKφ a r positive q hq t ht e he hcoords hsource p R v hv hvball hvside
  have hφp : IsFiniteApproximation Fp εp φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_left _ hz)).trans_le (min_le_left _ _)
  have hφg : IsFiniteApproximation Fg εg φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_right _ hz)).trans_le (min_le_right _ _)
  cases positive with
  | false =>
    refine ⟨t, ht, e, he, q, hq, hcoords, hsource, v, hv, hvball, hvside, ?_⟩
    exact hgerms φ hφg Kφ hKφ n a t e he q hq.1.1 hcoords
      (hE e he).2.2.2.2.2 false hsource v hv
  | true =>
    let U := Ioo (φ q.1 : ℝ) (φ q.2 : ℝ) ∩
      ((fun u : ℝ => deformPoint φ a + u • d) ⁻¹'
        (Metric.ball p R ∩ Tiling.positiveSide p d))
    have hUopen : IsOpen U := isOpen_Ioo.inter
      ((Metric.isOpen_ball.inter (Tiling.isOpen_positiveSide p d)).preimage
        (continuous_const.add (continuous_id.smul continuous_const)))
    obtain ⟨lo, hi, hlohi, hsub⟩ := hUopen.exists_Ioo_subset
      (show U.Nonempty from ⟨v, hv, hvball, hvside⟩)
    have hr : a + r • d ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support := by
      have hr' : r ∈ {u : ℝ | a + u • d ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support} :=
        connectedComponentIn_nonempty_iff.mp ⟨q.1, hq.2 ⟨le_rfl, hq.1.1.le⟩⟩
      exact hr'
    obtain ⟨s, hs, _, eN, heN, qN, hqN, hcoordsN, hsourceN, hoverlap⟩ :=
      hpartner φ hφp Kφ hKφ a r q.1 q.2 hr hq.1.1 hq.2 true q hq
        t ht e he hcoords hsource lo hi hlohi (fun u hu => (hsub hu).1)
    obtain ⟨u, huwindow, huN⟩ := hoverlap
    refine ⟨s, hs, eN, heN, qN, hqN, hcoordsN, hsourceN, u, huN,
      (hsub huwindow).2.1, (hsub huwindow).2.2, ?_⟩
    exact hgerms φ hφg Kφ hKφ n a s eN heN qN hqN.1.1 hcoordsN
      (hE eN heN).2.2.2.2.2 false hsourceN u huN


private theorem packingSol_uniformActualParallelOffset_exclusion
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) (n : RationalNormal) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ c : Plane, ∀ x p : Plane, ∀ R : ℝ, 0 < R →
      (∀ s ∈ T, s ≠ c → Disjoint
        (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x)
        (deformPoint φ s +ᵥ Kφ.openCarrier)) →
      (Metric.ball p R ∩ Tiling.negativeSide p (packingSol_rationalTangent n) ⊆
        connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x) →
      ((deformPoint φ c +ᵥ Kφ.support) ∩ Metric.ball p R =
        Tiling.negativeHalfPlane p (packingSol_rationalTangent n) ∩ Metric.ball p R) →
      ∀ Rv : ℝ, 0 < Rv →
      Disjoint (Metric.ball p Rv) (deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T) →
      ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ r ≤ Rv ∧
        ∀ t ∈ T, ∀ e ∈ E, normalEval n (e.2 - e.1) = 0 →
        ∀ z ∈ openSegment ℝ (deformPoint φ t + deformPoint φ e.1)
          (deformPoint φ t + deformPoint φ e.2), z ∈ Metric.ball p r →
          z ∉ Tiling.positiveSide p (packingSol_rationalTangent n) := by
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨Fq, εq, hεq, hquery⟩ :=
    packingSol_uniformActualMappedPrimitiveQuery K P T hP htile E hE hrat hcover n
  obtain ⟨Fn, εn, hεn, hnear⟩ :=
    packingSol_uniformActualNegativeOccurrence_near K P T hP htile E hE hrat hcover n
  obtain ⟨Fs, εs, hεs, hstrips⟩ := packingSol_actualTargetCentralSignedStrips K P hP E
    hrat hprimitive (fun e he => (hE e he).2.2.2.2.2) hcover
  refine ⟨Fq ∪ (Fn ∪ Fs), min εq (min εn εs), lt_min hεq (lt_min hεn hεs), ?_⟩
  intro φ hφ Kφ hKφ c x p R hR hsingle hframe hown Rv hRv hfree
  have hφq : IsFiniteApproximation Fq εq φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_left _ hz)).trans_le (min_le_left _ _)
  have hφn : IsFiniteApproximation Fn εn φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_right _ (Finset.mem_union_left _ hz))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hφs : IsFiniteApproximation Fs εs φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_right _ (Finset.mem_union_right _ hz))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨η, hη, hcentral⟩ := hstrips φ hφs Kφ hKφ (Rv / 2) (by positivity)
  let r := min R (min (Rv / 4) (η / 2))
  have hr : 0 < r := lt_min hR (lt_min (by positivity) (by positivity))
  have hrR : r ≤ R := min_le_left _ _
  have hrRv : r ≤ Rv / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hrη : r ≤ η / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, hr, hrR, by linarith, ?_⟩
  intro t ht e he hparallel z hz hzball hzside
  obtain ⟨a, q, positive, hq, hcoords, hsource, _, hparams, _⟩ :=
    hquery φ hφq Kφ hKφ t ht e he hparallel
  obtain ⟨v, hv, hvz⟩ := hparams z hz
  rw [hvz] at hzball hzside
  obtain ⟨s, hs, eN, heN, qN, hqN, hcoordsN, hsourceN,
    u, hu, huball, huside, hnegative⟩ :=
    hnear φ hφn Kφ hKφ a 0 positive q hq t ht e he hcoords hsource p r v hv hzball hzside
  let zN := deformPoint φ a + u • d
  let ξ := zN - deformPoint φ s
  have hzNsmall : dist zN p < r := Metric.mem_ball.mp huball
  have endpointV (w : Plane) (hw : w ∈ Tiling.vertexSet K.support) :
      deformPoint φ s + deformPoint φ w ∈
        deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T := by
    refine ⟨s + w, ?_, (deformPointLinear φ).map_add s w⟩
    change s + w ∈ Tiling.vertexSet K.support + T
    exact Set.mem_add.mpr ⟨w, hw, s, hs, add_comm w s⟩
  have endpointDist (w : Plane) (hw : w ∈ Tiling.vertexSet K.support) :
      Rv / 2 ≤ dist zN (deformPoint φ s + deformPoint φ w) := by
    have hnot : deformPoint φ s + deformPoint φ w ∉ Metric.ball p Rv :=
      fun hmem => Set.disjoint_left.mp hfree hmem (endpointV w hw)
    have hlarge := not_lt.mp (fun hlt => hnot (Metric.mem_ball.mpr hlt))
    have htri := dist_triangle p zN (deformPoint φ s + deformPoint φ w)
    rw [dist_comm p zN, dist_comm p (deformPoint φ s + deformPoint φ w)] at htri
    linarith
  have hdist (w : Plane) : dist ξ (deformPoint φ w) =
      dist zN (deformPoint φ s + deformPoint φ w) := by
    simp only [ξ, dist_eq_norm]
    congr 1
    abel
  have hξopen : ξ ∈ openSegment ℝ (deformPoint φ eN.1) (deformPoint φ eN.2) := by
    have hopen := vertexExclusionSol_occurrence_mappedOpen φ n a s eN qN hcoordsN u hu
    change zN ∈ openSegment ℝ (deformPoint φ s + deformPoint φ eN.1)
      (deformPoint φ s + deformPoint φ eN.2) at hopen
    have hξeq : deformPoint φ s + ξ = zN := by dsimp only [ξ]; abel
    rw [← hξeq] at hopen
    exact (mem_openSegment_translate ℝ (deformPoint φ s)).mp hopen
  have hξ1 : Rv / 2 ≤ dist ξ (deformPoint φ eN.1) := by
    rw [hdist]
    exact endpointDist eN.1 (hE eN heN).2.1
  have hξ2 : Rv / 2 ≤ dist ξ (deformPoint φ eN.2) := by
    rw [hdist]
    exact endpointDist eN.2 (hE eN heN).2.2.1
  have hprotoStrip : Kφ.support ∩ Metric.ball ξ η =
      Tiling.positiveHalfPlane ξ (eN.2 - eN.1) ∩ Metric.ball ξ η ∨
      Kφ.support ∩ Metric.ball ξ η =
        Tiling.negativeHalfPlane ξ (eN.2 - eN.1) ∩ Metric.ball ξ η := by
    rcases hcentral eN heN with ⟨_, hpos⟩ | ⟨_, hneg⟩
    · exact Or.inl (hpos ξ (openSegment_subset_segment ℝ _ _ hξopen) hξ1 hξ2)
    · exact Or.inr (hneg ξ (openSegment_subset_segment ℝ _ _ hξopen) hξ1 hξ2)
  have hprotoNegative : negativeEdgeGerm Kφ.support d ξ := by
    have h := sourceRay_vadd_negativeEdgeGerm (deformPoint φ s +ᵥ Kφ.support)
      (-deformPoint φ s) zN d hnegative
    have hcenter : -deformPoint φ s + zN = ξ := by dsimp only [ξ]; abel
    simpa only [vadd_vadd, neg_add_cancel, zero_vadd, vadd_eq_add, hcenter] using h
  have hdir : ∃ L : ℝ, L ≠ 0 ∧ eN.2 - eN.1 = L • d := by
    rcases hcoordsN with ⟨hl, hh⟩ | ⟨hl, hh⟩
    · refine ⟨qN.2 - qN.1, (sub_pos.mpr hqN.1.1).ne', ?_⟩
      calc
        eN.2 - eN.1 = (s + eN.2) - (s + eN.1) := by abel
        _ = (qN.2 - qN.1) • d := by rw [hl, hh]; module
    · refine ⟨qN.1 - qN.2, (sub_neg.mpr hqN.1.1).ne, ?_⟩
      calc
        eN.2 - eN.1 = (s + eN.2) - (s + eN.1) := by abel
        _ = (qN.1 - qN.2) • d := by rw [hl, hh]; module
  obtain ⟨L, hL, hLdir⟩ := hdir
  have hstrip := packingSol_negativeGerm_selects_parallelStrip Kφ.support ξ d
    (eN.2 - eN.1) hd L hL hLdir η hη hprotoStrip hprotoNegative
  have hfullStrip := packingSol_negativeStrip_vadd Kφ.support (deformPoint φ s) ξ d η hstrip
  have hξeq : deformPoint φ s + ξ = zN := by dsimp only [ξ]; abel
  rw [hξeq] at hfullStrip
  exact packingSol_offsetInwardStrip_exclusion Kφ T (deformPoint φ) c x hsingle
    p d hd R hR hframe hown s hs zN
    (Metric.mem_ball.mpr (hzNsmall.trans_le hrR)) huside η
    (by linarith) hfullStrip


private theorem packingSol_singleComponent_localLineAvoidance
    (Kφ : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (t : Plane) (ht : t ∈ T) (x : Plane) (hx : x ∈ ψ t +ᵥ Kφ.openCarrier)
    (hsingle : ∀ s ∈ T, s ≠ t →
      Disjoint (connectedComponentIn (ψ t +ᵥ Kφ.openCarrier) x)
        (ψ s +ᵥ Kφ.openCarrier))
    (p d : Plane) (hd : d ≠ 0) (R : ℝ) (hR : 0 < R)
    (hside : Metric.ball p R ∩ Tiling.negativeSide p d ⊆
      connectedComponentIn (ψ t +ᵥ Kφ.openCarrier) x)
    (hownFrontier : Tiling.affineLine p d ∩ Metric.ball p R ⊆
      frontier (ψ t +ᵥ Kφ.support)) :
    ∀ s ∈ T, Disjoint (Tiling.affineLine p d ∩ Metric.ball p R)
      (ψ s +ᵥ Kφ.openCarrier) := by
  intro s hs
  apply Set.disjoint_left.mpr
  intro z hz hzOpen
  by_cases hst : s = t
  · subst s
    have hzInterior : z ∈ interior (ψ t +ᵥ Kφ.support) := by
      simpa only [PolygonalRegion.openCarrier, interior_vadd] using hzOpen
    exact Set.disjoint_left.mp disjoint_interior_frontier hzInterior (hownFrontier hz)
  · have hneighborhood : IsOpen (Metric.ball p R ∩ (ψ s +ᵥ Kφ.openCarrier)) :=
      (Metric.isOpen_ball : IsOpen (Metric.ball p R)).inter (isOpen_interior.vadd _)
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hneighborhood z ⟨hz.2, hzOpen⟩
    obtain ⟨w, hwball, hwpositive⟩ := packingSol_positiveHalfBall_point z (-d)
      (neg_ne_zero.mpr hd) ρ hρ
    have hwside : w ∈ Tiling.negativeSide p d := by
      have hzline : Tiling.signedSide p d z = 0 := Tiling.mem_affineLine.mp hz.1
      have hwp : 0 < Tiling.signedSide z (-d) w := Tiling.mem_positiveSide.mp hwpositive
      apply Tiling.mem_negativeSide.mpr
      have hbase : Tiling.signedSide p d w =
          Tiling.signedSide z d w + Tiling.signedSide p d z := by
        simp only [Tiling.signedSide, Tiling.planarCross]
        ring
      have hneg : Tiling.signedSide z (-d) w = -Tiling.signedSide z d w := by
        simp only [Tiling.signedSide, Tiling.planarCross, Complex.neg_re, Complex.neg_im]
        ring
      rw [hbase, hzline, add_zero]
      linarith
    have hwBoth := hball hwball
    exact Set.disjoint_left.mp (hsingle s hs hst) (hside ⟨hwBoth.1, hwside⟩) hwBoth.2


private theorem positiveEdgeGerm_inter_ball
    {S : Set Plane} {p q d : Plane} {R : ℝ}
    (hq : dist q p < R) (hg : positiveEdgeGerm S d q) :
    positiveEdgeGerm (S ∩ Metric.ball p R) d q := by
  obtain ⟨ρ, hρ, heq⟩ := hg
  let ρ' := min ρ (R - dist q p)
  have hmargin : 0 < R - dist q p := by linarith
  have hρ' : 0 < ρ' := by dsimp [ρ']; positivity
  have hball (z : Plane) (hz : z ∈ Metric.ball q ρ') : z ∈ Metric.ball p R := by
    have hdist := dist_triangle z q p
    rw [Metric.mem_ball] at hz ⊢
    dsimp [ρ'] at hz
    have hzρ : dist z q < ρ := hz.trans_le (min_le_left _ _)
    have hzmargin : dist z q < R - dist q p := hz.trans_le (min_le_right _ _)
    linarith
  refine ⟨ρ', hρ', ?_⟩
  ext z
  constructor
  · rintro ⟨⟨hzS, hzP⟩, hzq⟩
    have hzqρ : z ∈ Metric.ball q ρ := by
      rw [Metric.mem_ball] at hzq ⊢
      exact hzq.trans_le (min_le_left _ _)
    have hzEq := (Set.ext_iff.mp heq z).mp ⟨hzS, hzqρ⟩
    exact ⟨hzEq.1, hzq⟩
  · rintro ⟨hzhalf, hzq⟩
    have hzP : z ∈ Metric.ball p R := hball z hzq
    have hzqρ : z ∈ Metric.ball q ρ := by
      rw [Metric.mem_ball] at hzq ⊢
      exact hzq.trans_le (min_le_left _ _)
    have hzEq := (Set.ext_iff.mp heq z).mpr ⟨hzhalf, hzqρ⟩
    exact ⟨⟨hzEq.1, hzP⟩, hzq⟩


private theorem negativeEdgeGerm_inter_ball
    {S : Set Plane} {p q d : Plane} {R : ℝ}
    (hq : dist q p < R) (hg : negativeEdgeGerm S d q) :
    negativeEdgeGerm (S ∩ Metric.ball p R) d q := by
  obtain ⟨ρ, hρ, heq⟩ := hg
  let ρ' := min ρ (R - dist q p)
  have hmargin : 0 < R - dist q p := by linarith
  have hρ' : 0 < ρ' := by dsimp [ρ']; positivity
  have hball (z : Plane) (hz : z ∈ Metric.ball q ρ') : z ∈ Metric.ball p R := by
    have hdist := dist_triangle z q p
    rw [Metric.mem_ball] at hz ⊢
    dsimp [ρ'] at hz
    have hzρ : dist z q < ρ := hz.trans_le (min_le_left _ _)
    have hzmargin : dist z q < R - dist q p := hz.trans_le (min_le_right _ _)
    linarith
  refine ⟨ρ', hρ', ?_⟩
  ext z
  constructor
  · rintro ⟨⟨hzS, hzP⟩, hzq⟩
    have hzqρ : z ∈ Metric.ball q ρ := by
      rw [Metric.mem_ball] at hzq ⊢
      exact hzq.trans_le (min_le_left _ _)
    have hzEq := (Set.ext_iff.mp heq z).mp ⟨hzS, hzqρ⟩
    exact ⟨hzEq.1, hzq⟩
  · rintro ⟨hzhalf, hzq⟩
    have hzP : z ∈ Metric.ball p R := hball z hzq
    have hzqρ : z ∈ Metric.ball q ρ := by
      rw [Metric.mem_ball] at hzq ⊢
      exact hzq.trans_le (min_le_left _ _)
    have hzEq := (Set.ext_iff.mp heq z).mpr ⟨hzhalf, hzqρ⟩
    exact ⟨⟨hzEq.1, hzP⟩, hzq⟩


private theorem packingSol_localSlope_frontierExclusion
    (Kφ : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (E : Finset (Plane × Plane)) (W : Finset Plane) (V : Set Plane)
    (p : Plane) (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hfrontier : ∀ t ∈ T, frontier (ψ t +ᵥ Kφ.support) =
      ⋃ e ∈ E, segment ℝ (ψ t + ψ e.1) (ψ t + ψ e.2))
    (hendpoints : ∀ t ∈ T, ∀ e ∈ E,
      ψ t + ψ e.1 ∈ V ∧ ψ t + ψ e.2 ∈ V)
    (hdirections : ∀ e ∈ E, ∃ w ∈ W, ∃ c : ℝ, c ≠ 0 ∧
      ψ e.2 - ψ e.1 = c • w)
    (hgerms : ∀ t ∈ T, ∀ e ∈ E,
      ∀ z ∈ openSegment ℝ (ψ t + ψ e.1) (ψ t + ψ e.2),
        positiveEdgeGerm (ψ t +ᵥ Kφ.support) (ψ e.2 - ψ e.1) z ∨
        negativeEdgeGerm (ψ t +ᵥ Kφ.support) (ψ e.2 - ψ e.1) z)
    (R : ℝ) (hR : 0 < R) (hvertex : Disjoint (Metric.ball p R) V)
    (havoid : ∀ t ∈ T,
      Disjoint ({z : Plane | ℓ (z - p) = 0} ∩ Metric.ball p R)
        (ψ t +ᵥ Kφ.openCarrier)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      (∀ t ∈ T, ∀ e ∈ E, ∀ z ∈ segment ℝ (ψ t + ψ e.1) (ψ t + ψ e.2),
        z ∈ Metric.ball p r → ℓ (ψ e.2 - ψ e.1) = 0) ∧
      (∀ t ∈ T, ∀ z ∈ frontier (ψ t +ᵥ Kφ.support), z ∈ Metric.ball p r →
        ∃ e ∈ E, z ∈ segment ℝ (ψ t + ψ e.1) (ψ t + ψ e.2) ∧
          ℓ (ψ e.2 - ψ e.1) = 0) := by
  let C : ℝ := ∑ w ∈ W, if ℓ w = 0 then 0 else ‖w‖ / |ℓ w|
  have hC : 0 ≤ C := by
    dsimp [C]
    apply Finset.sum_nonneg
    intro w hw
    split_ifs <;> positivity
  have hratio (w : Plane) (hw : w ∈ W) (hℓw : ℓ w ≠ 0) :
      ‖w‖ / |ℓ w| ≤ C := by
    have hsum : (if ℓ w = 0 then 0 else ‖w‖ / |ℓ w|) ≤
        ∑ x ∈ W, if ℓ x = 0 then 0 else ‖x‖ / |ℓ x| :=
      Finset.single_le_sum (f := fun x => if ℓ x = 0 then 0 else ‖x‖ / |ℓ x|)
        (fun x hx => by split_ifs <;> positivity) hw
    simpa [C, hℓw] using hsum
  have hnormℓ : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
  let A : ℝ := 1 + ‖ℓ‖ * C
  have hA : 0 < A := by dsimp [A]; positivity
  have hAC : ‖ℓ‖ * C ≤ A := by dsimp [A]; linarith
  let r : ℝ := min (R / 2) (R / (4 * A))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r ≤ R := by
    dsimp [r]
    exact (min_le_left _ _).trans (by linarith)
  have hrhalf : r ≤ R / 2 := by dsimp [r]; exact min_le_left _ _
  have hrtrans : r ≤ R / (4 * A) := by
    dsimp [r]
    exact min_le_right _ _
  have hsmallSlope : ‖ℓ‖ * r * C ≤ R / 4 := by
    calc
      ‖ℓ‖ * r * C ≤ (‖ℓ‖ * (R / (4 * A))) * C := by gcongr
      _ = (‖ℓ‖ * C) * (R / (4 * A)) := by ring
      _ ≤ A * (R / (4 * A)) := by gcongr
      _ = R / 4 := by field_simp [ne_of_gt hA]
  have hseg : ∀ t ∈ T, ∀ e ∈ E,
      ∀ z ∈ segment ℝ (ψ t + ψ e.1) (ψ t + ψ e.2),
      z ∈ Metric.ball p r → ℓ (ψ e.2 - ψ e.1) = 0 := by
    intro t ht e heE z hzseg hzball
    by_contra hdir
    let a := ψ t + ψ e.1
    let b := ψ t + ψ e.2
    have hends := hendpoints t ht e heE
    have haout : a ∉ Metric.ball p R := fun ha =>
      (Set.disjoint_left.mp hvertex) ha hends.1
    have hbout : b ∉ Metric.ball p R := fun hb =>
      (Set.disjoint_left.mp hvertex) hb hends.2
    have haR : R ≤ dist a p := by
      by_contra h
      exact haout (Metric.mem_ball.mpr (lt_of_not_ge h))
    have hbR : R ≤ dist b p := by
      by_contra h
      exact hbout (Metric.mem_ball.mpr (lt_of_not_ge h))
    have hzdist : dist z p < r := Metric.mem_ball.mp hzball
    have hzR : z ∈ Metric.ball p R :=
      Metric.mem_ball.mpr (lt_of_lt_of_le hzdist hrR)
    have hzseg' : z ∈ segment ℝ a b := by simpa [a, b] using hzseg
    have hab : a ≠ b := by
      intro hab
      rw [segment_eq_image_lineMap] at hzseg'
      rcases hzseg' with ⟨u, hu, hzu⟩
      have hza : z = a := by simpa [hab, AffineMap.lineMap_apply] using hzu.symm
      exact haout (by simpa [hza] using hzR)
    rw [segment_eq_image_lineMap] at hzseg'
    rcases hzseg' with ⟨u, hu, hzu⟩
    have hu0 : 0 < u := by
      by_contra h
      have huEq : u = 0 := le_antisymm (le_of_not_gt h) hu.1
      have hza : z = a := by simpa [huEq, AffineMap.lineMap_apply] using hzu.symm
      exact haout (by simpa [hza] using hzR)
    have hu1 : u < 1 := by
      by_contra h
      have huEq : u = 1 := le_antisymm hu.2 (le_of_not_gt h)
      have hzb : z = b := by simpa [huEq, AffineMap.lineMap_apply] using hzu.symm
      exact hbout (by simpa [hzb] using hzR)
    have hzOpenSeg : z ∈ openSegment ℝ a b := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨u, ⟨hu0, hu1⟩, hzu⟩
    rcases hdirections e heE with ⟨w, hw, c, hc, hdEq⟩
    have hd : b - a = c • w := by
      dsimp [a, b]
      calc
        (ψ t + ψ e.2) - (ψ t + ψ e.1) = ψ e.2 - ψ e.1 := by abel
        _ = c • w := hdEq
    have hℓw : ℓ w ≠ 0 := by
      intro hzero
      apply hdir
      have : ℓ (ψ e.2 - ψ e.1) = 0 := by rw [hdEq, map_smul, hzero]; simp
      simpa using this
    have hℓd : ℓ (b - a) ≠ 0 := by
      rw [hd, map_smul]
      exact mul_ne_zero hc hℓw
    have hzrep : z - a = u • (b - a) := by
      rw [← hzu]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    have hzaDist : dist a z = u * ‖b - a‖ := by
      rw [dist_comm, dist_eq_norm, hzrep, norm_smul, Real.norm_eq_abs]
      rw [abs_of_nonneg hu.1]
    have hzbRep : z - b = (u - 1) • (b - a) := by
      rw [← hzu]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    have hzbDist : dist b z = (1 - u) * ‖b - a‖ := by
      rw [dist_comm, dist_eq_norm, hzbRep, norm_smul, Real.norm_eq_abs]
      rw [abs_of_nonpos (by linarith : u - 1 ≤ 0)]
      ring
    have hmarginA : R - r < dist a z := by linarith [dist_triangle a z p]
    have hmarginB : R - r < dist b z := by linarith [dist_triangle b z p]
    have hzdecomp : z - p = (a - p) + u • (b - a) := by
      rw [← hzrep]
      module
    have habsℓ (x : Plane) : |ℓ x| ≤ ‖ℓ‖ * ‖x‖ := by
      simpa only [Real.norm_eq_abs] using ℓ.le_opNorm x
    let γ : ℝ := ℓ (a - p) / ℓ w
    let q : Plane := a - γ • w
    have hqline : ℓ (q - p) = 0 := by
      have hqrep : q - p = (a - p) - γ • w := by dsimp [q]; module
      rw [hqrep, map_sub, map_smul]
      dsimp [γ]
      field_simp [hℓw]
      ring
    have hzval : ℓ (z - p) = ℓ (a - p) + u * c * ℓ w := by
      rw [hzdecomp, map_add, map_smul, hd, map_smul]
      simp only [smul_eq_mul]
      ring
    have hcoeff : γ + u * c = ℓ (z - p) / ℓ w := by
      rw [hzval]
      dsimp [γ]
      field_simp [hℓw]
    have hqzrep : q - z = -(γ + u * c) • w := by
      have hzaw : z - a = (u * c) • w := by rw [hzrep, hd, smul_smul]
      have hzAdd : z = a + (u * c) • w := by
        calc
          z = a + (z - a) := by module
          _ = a + (u * c) • w := by rw [hzaw]
      calc
        q - z = (a - γ • w) - (a + (u * c) • w) := by
          dsimp [q]
          rw [hzAdd]
          apply Complex.ext <;> simp <;> ring
        _ = (-γ - u * c) • w := by
          apply Complex.ext <;> simp <;> ring
        _ = -(γ + u * c) • w := by congr 1; ring
    have hdistq : dist q z = |γ + u * c| * ‖w‖ := by
      calc
        dist q z = ‖q - z‖ := dist_eq_norm q z
        _ = ‖-(γ + u * c) • w‖ := by rw [hqzrep]
        _ = ‖-(γ + u * c)‖ * ‖w‖ := norm_smul _ _
        _ = |γ + u * c| * ‖w‖ := by rw [Real.norm_eq_abs, abs_neg]
    have hratio' : ‖w‖ / |ℓ w| ≤ C := hratio w hw hℓw
    have hAlphaNorm : |γ + u * c| * ‖w‖ ≤ ‖ℓ‖ * dist z p * C := by
      rw [show |γ + u * c| * ‖w‖ = |ℓ (z - p)| * (‖w‖ / |ℓ w|) by
        rw [hcoeff, abs_div]
        field_simp [hℓw]]
      calc
        |ℓ (z - p)| * (‖w‖ / |ℓ w|) ≤ |ℓ (z - p)| * C :=
          mul_le_mul_of_nonneg_left hratio' (abs_nonneg _)
        _ ≤ (‖ℓ‖ * dist z p) * C :=
          mul_le_mul_of_nonneg_right
            (by simpa only [Real.norm_eq_abs, dist_eq_norm] using ℓ.le_opNorm (z - p)) hC
        _ = ‖ℓ‖ * dist z p * C := by ring
    have hdistqBound : dist q z ≤ R / 4 := by
      rw [hdistq]
      calc
        |γ + u * c| * ‖w‖ ≤ ‖ℓ‖ * dist z p * C := hAlphaNorm
        _ ≤ ‖ℓ‖ * r * C := by gcongr
        _ ≤ R / 4 := hsmallSlope
    have hqball : q ∈ Metric.ball p R := by
      rw [Metric.mem_ball]
      have htri := dist_triangle q z p
      linarith [hdistqBound, hzdist, hrhalf]
    have hdistqMargin : dist q z < R - r := by
      have hRmr : R / 2 ≤ R - r := by linarith [hrhalf]
      linarith
    have hbetaD (β : ℝ) :
        dist (AffineMap.lineMap a b β) z = |β - u| * ‖b - a‖ := by
      rw [dist_eq_norm, ← hzu]
      have hdiff : (AffineMap.lineMap a b β) - (AffineMap.lineMap a b u) =
          (β - u) • (b - a) := by
        simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
        module
      rw [hdiff, norm_smul, Real.norm_eq_abs]
    let β : ℝ := -γ / c
    have hqLineMap : q = AffineMap.lineMap a b β := by
      have hsc : β * c = -γ := by dsimp [β]; field_simp [hc]
      change a - γ • w = AffineMap.lineMap a b β
      rw [AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add]
      change a - γ • w = β • (b - a) + a
      rw [hd, smul_smul, hsc]
      module
    have hbetaDist : |β - u| * ‖b - a‖ = dist q z := by
      calc
        |β - u| * ‖b - a‖ = dist (AffineMap.lineMap a b β) z := (hbetaD β).symm
        _ = dist q z := by rw [hqLineMap]
    have hbetaAbs : |β - u| < u := by
      have hmul : |β - u| * ‖b - a‖ < u * ‖b - a‖ := by
        calc
          |β - u| * ‖b - a‖ = dist q z := hbetaDist
          _ < dist a z := hdistqMargin.trans hmarginA
          _ = u * ‖b - a‖ := hzaDist
      by_contra hnot
      have hle : u ≤ |β - u| := le_of_not_gt hnot
      have hmul' := mul_le_mul_of_nonneg_right hle (le_of_lt (norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)))
      linarith
    have hbetaAbsRight : |β - u| < 1 - u := by
      have hmul : |β - u| * ‖b - a‖ < (1 - u) * ‖b - a‖ := by
        calc
          |β - u| * ‖b - a‖ = dist q z := hbetaDist
          _ < dist b z := hdistqMargin.trans hmarginB
          _ = (1 - u) * ‖b - a‖ := hzbDist
      by_contra hnot
      have hle : 1 - u ≤ |β - u| := le_of_not_gt hnot
      have hmul' := mul_le_mul_of_nonneg_right hle (le_of_lt (norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)))
      linarith
    have hβ0 : 0 < β := by linarith [neg_le_abs (β - u)]
    have hβ1 : β < 1 := by linarith [le_abs_self (β - u)]
    have hqOpenSeg : q ∈ openSegment ℝ a b := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨β, ⟨hβ0, hβ1⟩, hqLineMap.symm⟩
    have hdtranslate : b - a = ψ e.2 - ψ e.1 := by dsimp [a, b]; abel
    have havoid' : Disjoint {x : Plane | ℓ (x - p) = 0}
        (interior ((ψ t +ᵥ Kφ.support) ∩ Metric.ball p R)) := by
      apply Set.disjoint_left.mpr
      intro x hxline hxint
      have hx : x ∈ (ψ t +ᵥ Kφ.support) ∩ Metric.ball p R := interior_subset hxint
      have hxopen : x ∈ ψ t +ᵥ Kφ.openCarrier := by
        have hxint' : x ∈ interior (ψ t +ᵥ Kφ.support) :=
          interior_mono (fun y hy => hy.1) hxint
        simpa [PolygonalRegion.openCarrier, interior_vadd] using hxint'
      exact (Set.disjoint_left.mp (havoid t ht)) ⟨hxline, hx.2⟩ hxopen
    rcases hgerms t ht e heE q hqOpenSeg with hpos | hneg
    · exact edgeGerm_contradicts_transverseLine havoid' hqline hℓd
        (Or.inl (positiveEdgeGerm_inter_ball (Metric.mem_ball.mp hqball)
          (by simpa [hdtranslate] using hpos)))
    · exact edgeGerm_contradicts_transverseLine havoid' hqline hℓd
        (Or.inr (negativeEdgeGerm_inter_ball (Metric.mem_ball.mp hqball)
          (by simpa [hdtranslate] using hneg)))
  refine ⟨r, hr, hrR, hseg, ?_⟩
  intro t ht z hzfront hzball
  rw [hfrontier t ht] at hzfront
  rcases Set.mem_iUnion.mp hzfront with ⟨e, he⟩
  rcases Set.mem_iUnion.mp he with ⟨heE, hzseg⟩
  exact ⟨e, heE, hzseg, hseg t ht e heE z hzseg hzball⟩


private theorem packingSol_negativeStrip_carrierFrontier
    (S : Set Plane) (p d : Plane) (hd : d ≠ 0) (R : ℝ) (hR : 0 < R)
    (hstrip : S ∩ Metric.ball p R = Tiling.negativeHalfPlane p d ∩ Metric.ball p R) :
    Tiling.affineLine p d ∩ Metric.ball p R ⊆ frontier S := by
  intro z hz
  have hzero := Tiling.mem_affineLine.mp hz.1
  have hzS : z ∈ S := ((Set.ext_iff.mp hstrip z).mpr
    ⟨Tiling.mem_negativeHalfPlane.mpr hzero.le, hz.2⟩).1
  refine ⟨subset_closure hzS, ?_⟩
  intro hzint
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_interior.inter Metric.isOpen_ball) z ⟨hzint, hz.2⟩
  obtain ⟨w, hwball, hwpos⟩ := packingSol_positiveHalfBall_point z d hd ρ hρ
  have hwBoth := hball hwball
  have hwneg := ((Set.ext_iff.mp hstrip w).mp ⟨interior_subset hwBoth.1, hwBoth.2⟩).1
  have hside : Tiling.signedSide p d w = Tiling.signedSide z d w := by
    have hsum : Tiling.signedSide p d w =
        Tiling.signedSide z d w + Tiling.signedSide p d z := by
      simp only [Tiling.signedSide, Tiling.planarCross]
      ring
    rw [hsum, hzero, add_zero]
  have hpos := Tiling.mem_positiveSide.mp hwpos
  have hneg := Tiling.mem_negativeHalfPlane.mp hwneg
  rw [hside] at hneg
  exact (not_le_of_gt hpos) hneg


private theorem packingSol_singleComponent_negativeSide_frontierFree
    (Kφ : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (c x p d : Plane) (R : ℝ)
    (hsingle : ∀ s ∈ T, s ≠ c → Disjoint
      (connectedComponentIn (ψ c +ᵥ Kφ.openCarrier) x) (ψ s +ᵥ Kφ.openCarrier))
    (hframe : Metric.ball p R ∩ Tiling.negativeSide p d ⊆
      connectedComponentIn (ψ c +ᵥ Kφ.openCarrier) x) :
    ∀ s ∈ T, Disjoint (Metric.ball p R ∩ Tiling.negativeSide p d)
      (frontier (ψ s +ᵥ Kφ.support)) := by
  have hOopen : IsOpen (connectedComponentIn (ψ c +ᵥ Kφ.openCarrier) x) :=
    (isOpen_interior.vadd (ψ c)).connectedComponentIn
  intro s hs
  apply Set.disjoint_left.mpr
  intro z hz hzfront
  by_cases hsc : s = c
  · subst s
    have hzopen := connectedComponentIn_subset _ _ (hframe hz)
    have hzint : z ∈ interior (ψ c +ᵥ Kφ.support) := by
      simpa only [PolygonalRegion.openCarrier, interior_vadd] using hzopen
    exact Set.disjoint_left.mp disjoint_interior_frontier hzint hzfront
  · have hclosedDisjoint : Disjoint (connectedComponentIn (ψ c +ᵥ Kφ.openCarrier) x)
        (ψ s +ᵥ Kφ.support) := by
      have h := (hsingle s hs hsc).closure_right hOopen
      simpa only [closure_vadd, PolygonalRegion.openCarrier,
        Kφ.isPolygonal.closure_interior] using h
    exact Set.disjoint_left.mp hclosedDisjoint (hframe hz)
      ((Kφ.isPolygonal.isClosed.vadd (ψ s)).frontier_subset hzfront)


private theorem packingSol_uniformActualLocalFrontierConfinement
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) (n : RationalNormal) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ c ∈ T, ∀ x ∈ deformPoint φ c +ᵥ Kφ.openCarrier,
      ∀ p : Plane, ∀ R : ℝ, 0 < R →
      (∀ s ∈ T, s ≠ c → Disjoint
        (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x)
        (deformPoint φ s +ᵥ Kφ.openCarrier)) →
      (Metric.ball p R ∩ Tiling.negativeSide p (packingSol_rationalTangent n) ⊆
        connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x) →
      ((deformPoint φ c +ᵥ Kφ.support) ∩ Metric.ball p R =
        Tiling.negativeHalfPlane p (packingSol_rationalTangent n) ∩ Metric.ball p R) →
      ∀ Rv : ℝ, 0 < Rv →
      Disjoint (Metric.ball p Rv) (deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T) →
      ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ r ≤ Rv ∧
        ∀ s ∈ T, frontier (deformPoint φ s +ᵥ Kφ.support) ∩ Metric.ball p r ⊆
          Tiling.affineLine p (packingSol_rationalTangent n) := by
  classical
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨Fo, εo, hεo, hoffset⟩ :=
    packingSol_uniformActualParallelOffset_exclusion K P T hP htile E hE hrat hcover n
  obtain ⟨Ft, εt, _, hεt, _, htransport⟩ :=
    rationalPrimitiveEdges_uniformSameSide_transport K P hP E hrat hprimitive hcover
  obtain ⟨Fc, εc, _, hεc, _, hscale⟩ := finiteRationalEdges_positiveHomotheties E hrat
  refine ⟨Fo ∪ (Ft ∪ Fc), min εo (min εt εc), lt_min hεo (lt_min hεt hεc), ?_⟩
  intro φ hφ Kφ hKφ c hc x hx p R hR hsingle hframe hown Rv hRv hfree
  have hφo : IsFiniteApproximation Fo εo φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_left _ hz)).trans_le (min_le_left _ _)
  have hφt : IsFiniteApproximation Ft εt φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_right _ (Finset.mem_union_left _ hz))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hφc : IsFiniteApproximation Fc εc φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_right _ (Finset.mem_union_right _ hz))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨_, _, _, _, hfront, hgerms⟩ := htransport φ hφt Kφ hKφ
  let V := deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T
  have mapVertex (s : Plane) (hs : s ∈ T) (v : Plane)
      (hv : v ∈ Tiling.vertexSet K.support) : deformPoint φ s + deformPoint φ v ∈ V := by
    refine ⟨s + v, Set.mem_add.mpr ⟨v, hv, s, hs, add_comm v s⟩, ?_⟩
    exact (deformPointLinear φ).map_add s v
  have hends : ∀ s ∈ T, ∀ e ∈ E,
      deformPoint φ s + deformPoint φ e.1 ∈ V ∧
      deformPoint φ s + deformPoint φ e.2 ∈ V :=
    fun s hs e he => ⟨mapVertex s hs e.1 (hE e he).2.1,
      mapVertex s hs e.2 (hE e he).2.2.1⟩
  have hfrontier : ∀ s ∈ T, frontier (deformPoint φ s +ᵥ Kφ.support) =
      ⋃ e ∈ E, segment ℝ (deformPoint φ s + deformPoint φ e.1)
        (deformPoint φ s + deformPoint φ e.2) := by
    intro s _
    rw [← sourceRay_link_frontier_vadd, hfront, Set.vadd_set_iUnion]
    simp only [Set.vadd_set_iUnion, vadd_segment, vadd_eq_add]
  have hdirs : ∀ e ∈ E, ∃ w ∈ E.image (fun e => e.2 - e.1), ∃ L : ℝ,
      L ≠ 0 ∧ deformPoint φ e.2 - deformPoint φ e.1 = L • w := by
    intro e he
    obtain ⟨L, hL, _, hvec, _⟩ := hscale φ hφc e he
    exact ⟨e.2 - e.1, Finset.mem_image.mpr ⟨e, he, rfl⟩, L,
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hL), hvec⟩
  have htargetGerms : ∀ s ∈ T, ∀ e ∈ E, ∀ z ∈
      openSegment ℝ (deformPoint φ s + deformPoint φ e.1)
        (deformPoint φ s + deformPoint φ e.2),
      positiveEdgeGerm (deformPoint φ s +ᵥ Kφ.support)
        (deformPoint φ e.2 - deformPoint φ e.1) z ∨
      negativeEdgeGerm (deformPoint φ s +ᵥ Kφ.support)
        (deformPoint φ e.2 - deformPoint φ e.1) z := by
    intro s _ e he z hz
    have hz' : z ∈ deformPoint φ s +ᵥ
        openSegment ℝ (deformPoint φ e.1) (deformPoint φ e.2) := by
      simpa only [vadd_openSegment, vadd_eq_add] using hz
    obtain ⟨y, hy, hyz⟩ := Set.mem_vadd_set.mp hz'
    have hyz' : deformPoint φ s + y = z := hyz
    obtain ⟨L, hL, _, hvec, _⟩ := hscale φ hφc e he
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hL
    rcases (hE e he).2.2.2.2.2 with hpos | hneg
    · left
      have hproto : positiveEdgeGerm Kφ.support (e.2 - e.1) y := by
        simpa only [hKφ] using (hgerms e he).1 hpos y hy
      rw [hvec]
      apply (positiveEdgeGerm_smul_pos_iff _ _ _ L hLpos).2
      simpa only [hyz'] using sourceRay_vadd_positiveEdgeGerm Kφ.support
        (deformPoint φ s) y (e.2 - e.1) hproto
    · right
      have hproto : negativeEdgeGerm Kφ.support (e.2 - e.1) y := by
        simpa only [hKφ] using (hgerms e he).2 hneg y hy
      rw [hvec]
      apply (negativeEdgeGerm_smul_pos_iff _ _ _ L hLpos).2
      simpa only [hyz'] using sourceRay_vadd_negativeEdgeGerm Kφ.support
        (deformPoint φ s) y (e.2 - e.1) hproto
  have hownFront := packingSol_negativeStrip_carrierFrontier
    (deformPoint φ c +ᵥ Kφ.support) p d hd R hR hown
  have havoid := packingSol_singleComponent_localLineAvoidance Kφ T (deformPoint φ)
    c hc x hx hsingle p d hd R hR hframe hownFront
  have hline : {z : Plane | normalCLM n (z - p) = 0} = Tiling.affineLine p d := by
    ext z
    rw [Tiling.mem_affineLine]
    change normalEval n (z - p) = 0 ↔ Tiling.signedSide p d z = 0
    rw [packingSol_tangent_signedSide]
    exact (neg_eq_zero).symm
  let R0 := min R Rv
  have hR0 : 0 < R0 := lt_min hR hRv
  have hfree0 : Disjoint (Metric.ball p R0) V :=
    hfree.mono_left (Metric.ball_subset_ball (min_le_right _ _))
  have havoid0 : ∀ s ∈ T, Disjoint
      ({z : Plane | normalCLM n (z - p) = 0} ∩ Metric.ball p R0)
      (deformPoint φ s +ᵥ Kφ.openCarrier) := by
    intro s hs
    rw [hline]
    exact (havoid s hs).mono_left (Set.inter_subset_inter_right _
      (Metric.ball_subset_ball (min_le_left _ _)))
  obtain ⟨rL, hrL, hrLR0, _, hlocal⟩ := packingSol_localSlope_frontierExclusion
    Kφ T (deformPoint φ) E (E.image (fun e => e.2 - e.1)) V p (normalCLM n)
    (normalCLM_ne_zero n) hfrontier hends hdirs htargetGerms R0 hR0 hfree0 havoid0
  obtain ⟨rO, hrO, hrOR, hrORv, hoffsetLocal⟩ :=
    hoffset φ hφo Kφ hKφ c x p R hR hsingle hframe hown Rv hRv hfree
  let r := min rL rO
  have hrR : r ≤ R := (min_le_left _ _).trans
    (hrLR0.trans (min_le_left _ _))
  have hrRv : r ≤ Rv := (min_le_right _ _).trans hrORv
  have hnegativeFree := packingSol_singleComponent_negativeSide_frontierFree
    Kφ T (deformPoint φ) c x p d R hsingle hframe
  refine ⟨r, lt_min hrL hrO, hrR, hrRv, ?_⟩
  intro s hs z hz
  apply Tiling.mem_affineLine.mpr
  rcases lt_trichotomy (Tiling.signedSide p d z) 0 with hneg | heq | hpos
  · exact False.elim (Set.disjoint_left.mp (hnegativeFree s hs)
      ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp hz.2).trans_le hrR),
        Tiling.mem_negativeSide.mpr hneg⟩ hz.1)
  · exact heq
  · obtain ⟨e, he, hzseg, hparallel⟩ := hlocal s hs z hz.1
      (Metric.mem_ball.mpr ((Metric.mem_ball.mp hz.2).trans_le (min_le_left _ _)))
    have hnotV : z ∉ V := fun hV => Set.disjoint_left.mp hfree
      (Metric.mem_ball.mpr ((Metric.mem_ball.mp hz.2).trans_le hrRv)) hV
    have hleft : deformPoint φ s + deformPoint φ e.1 ≠ z :=
      fun h => hnotV (h ▸ (hends s hs e he).1)
    have hright : deformPoint φ s + deformPoint φ e.2 ≠ z :=
      fun h => hnotV (h ▸ (hends s hs e he).2)
    have hzopen := mem_openSegment_of_ne_left_right hleft hright hzseg
    obtain ⟨L, hL, _, hvec, _⟩ := hscale φ hφc e he
    have hLne : L ≠ 0 := ne_of_gt
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hL)
    rw [hvec, map_smul, smul_eq_mul, normalCLM_apply] at hparallel
    have holdparallel : normalEval n (e.2 - e.1) = 0 :=
      (mul_eq_zero.mp hparallel).resolve_left hLne
    exact False.elim (hoffsetLocal s hs e he holdparallel z hzopen
      (Metric.mem_ball.mpr ((Metric.mem_ball.mp hz.2).trans_le (min_le_right _ _)))
      (Tiling.mem_positiveSide.mpr hpos))


/-- An occupied inward half-ball aligns a regular closed, locally straight
boundary with its requested direction and selects its negative closed side. -/
private theorem packingSol_regularClosed_straight_negativeHalfBall
    (U : Set Plane) (p d : Plane)
    (hregular : closure (interior U) = U) (_hp : p ∈ frontier U)
    (hstraight : Tiling.BoundaryLocallyStraightAt U p) (hd : d ≠ 0)
    (R : ℝ) (hR : 0 < R)
    (hin : Metric.ball p R ∩ Tiling.negativeSide p d ⊆ interior U) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      U ∩ Metric.ball p r =
        Tiling.negativeHalfPlane p d ∩ Metric.ball p r := by
  obtain ⟨L, hpL, hdim, hlocal⟩ := hstraight
  obtain ⟨v, hv, r₀, hr₀, hfront⟩ :=
    Tiling.AffineSubspace.exists_ball_frontier_iff_affineLine hpL hdim hlocal
  let r := min r₀ R
  have hr : 0 < r := lt_min hr₀ hR
  have hrR : r ≤ R := min_le_right _ _
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hnonneg (w : Plane) (hw : w ∈ Tiling.affineLine 0 v) :
      0 ≤ Tiling.planarCross d w := by
    by_contra h
    have hneg : Tiling.planarCross d w < 0 := lt_of_not_ge h
    obtain ⟨b, hb⟩ := (Tiling.mem_affineLine_iff_exists_smul hv).mp hw
    have hwEq : w = b • v := by simpa using hb
    obtain ⟨c, hc, hcsmall⟩ := exists_positiveScaling_intoBall w r hr
    have hzball : p + c • w ∈ Metric.ball p r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hcsmall
    have hzline : p + c • w ∈ Tiling.affineLine p v := by
      apply (Tiling.mem_affineLine_iff_exists_smul hv).mpr
      exact ⟨c * b, by rw [hwEq, smul_smul]⟩
    have hzfront : p + c • w ∈ frontier U :=
      (hfront _ (Metric.mem_ball.mpr
        ((Metric.mem_ball.mp hzball).trans_le hrr₀))).mpr hzline
    have hzside : p + c • w ∈ Tiling.negativeSide p d := by
      apply Tiling.mem_negativeSide.mpr
      have heq : Tiling.signedSide p d (p + c • w) =
          c * Tiling.planarCross d w := by
        simp only [Tiling.signedSide, Tiling.planarCross,
          Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im]
        ring
      rw [heq]
      exact mul_neg_of_pos_of_neg hc hneg
    exact Set.disjoint_left.mp disjoint_interior_frontier
      (hin ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp hzball).trans_le hrR), hzside⟩)
      hzfront
  have hvline : v ∈ Tiling.affineLine 0 v := by
    apply (Tiling.mem_affineLine_iff_exists_smul hv).mpr
    exact ⟨1, by simp⟩
  have hnvline : -v ∈ Tiling.affineLine 0 v := by
    apply (Tiling.mem_affineLine_iff_exists_smul hv).mpr
    exact ⟨-1, by simp⟩
  have hcross : Tiling.planarCross d v = 0 := by
    have hpos := hnonneg v hvline
    have hneg := hnonneg (-v) hnvline
    have heq : Tiling.planarCross d (-v) = -Tiling.planarCross d v := by
      simp only [Tiling.planarCross, Complex.neg_re, Complex.neg_im]
      ring
    rw [heq] at hneg
    linarith
  have hvD : v ∈ Tiling.affineLine 0 d := by
    simpa [Tiling.mem_affineLine, Tiling.signedSide, Tiling.planarCross] using hcross
  have hdV : d ∈ Tiling.affineLine 0 v := by
    apply Tiling.mem_affineLine.mpr
    simp only [Tiling.signedSide, Tiling.planarCross,
      Complex.zero_re, Complex.zero_im]
    dsimp only [Tiling.planarCross] at hcross
    nlinarith
  obtain ⟨c, hc⟩ := (Tiling.mem_affineLine_iff_exists_smul hd).mp hvD
  obtain ⟨b, hb⟩ := (Tiling.mem_affineLine_iff_exists_smul hv).mp hdV
  have hvEq : v = c • d := by simpa using hc
  have hdEq : d = b • v := by simpa using hb
  have hlines : Tiling.affineLine p v = Tiling.affineLine p d := by
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha⟩ := (Tiling.mem_affineLine_iff_exists_smul hv).mp hz
      apply (Tiling.mem_affineLine_iff_exists_smul hd).mpr
      exact ⟨a * c, by rw [ha, hvEq, smul_smul]⟩
    · intro hz
      obtain ⟨a, ha⟩ := (Tiling.mem_affineLine_iff_exists_smul hd).mp hz
      apply (Tiling.mem_affineLine_iff_exists_smul hv).mpr
      exact ⟨a * b, by rw [ha, hdEq, smul_smul]⟩
  have hfrontD : ∀ z ∈ Metric.ball p r,
      z ∈ frontier U ↔ z ∈ Tiling.affineLine p d := by
    intro z hz
    rw [← hlines]
    exact hfront z (Metric.mem_ball.mpr
      ((Metric.mem_ball.mp hz).trans_le hrr₀))
  rcases Tiling.local_eq_closedHalfPlane hd hr hregular hfrontD with hpos | hneg
  · obtain ⟨z, hzball, hzpositive⟩ := packingSol_positiveHalfBall_point p (-d)
      (neg_ne_zero.mpr hd) r hr
    have hznegative : z ∈ Tiling.negativeSide p d := by
      apply Tiling.mem_negativeSide.mpr
      have h := Tiling.mem_positiveSide.mp hzpositive
      simp only [Tiling.signedSide, Tiling.planarCross,
        Complex.neg_re, Complex.neg_im] at h ⊢
      linarith
    have hzU : z ∈ U := interior_subset (hin
      ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp hzball).trans_le hrR), hznegative⟩)
    have hzpos := Tiling.mem_positiveHalfPlane.mp
      ((hpos ▸ (show z ∈ U ∩ Metric.ball p r from ⟨hzU, hzball⟩)).1)
    exact False.elim (not_lt_of_ge hzpos (Tiling.mem_negativeSide.mp hznegative))
  · exact ⟨r, hr, hrR, hneg⟩


private theorem packingSol_uniformActualLocalBoundaryOccurrence
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) (n : RationalNormal) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ t ∈ T, ∀ p : Plane,
      p ∈ frontier (deformPoint φ t +ᵥ Kφ.support) →
      p ∉ deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T →
      ∀ R : ℝ, 0 < R →
      (frontier (deformPoint φ t +ᵥ Kφ.support) ∩ Metric.ball p R ⊆
        Tiling.affineLine p (packingSol_rationalTangent n)) →
      ∃ (a : Plane) (e : Plane × Plane), e ∈ E ∧
      ∃ (q : ℝ × ℝ) (positive : Bool),
        q ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) 0 positive ∧
        ((t + e.1 = a + q.1 • packingSol_rationalTangent n ∧
          t + e.2 = a + q.2 • packingSol_rationalTangent n) ∨
         (t + e.2 = a + q.1 • packingSol_rationalTangent n ∧
          t + e.1 = a + q.2 • packingSol_rationalTangent n)) ∧
        (∀ u ∈ Ioo q.1 q.2, if positive then
          positiveEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
            (a + u • packingSol_rationalTangent n)
          else negativeEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
            (a + u • packingSol_rationalTangent n)) ∧
        ∃ u ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ),
          p = deformPoint φ a + u • packingSol_rationalTangent n ∧
          (if positive then positiveEdgeGerm (deformPoint φ t +ᵥ Kφ.support)
            (packingSol_rationalTangent n) p
           else negativeEdgeGerm (deformPoint φ t +ᵥ Kφ.support)
            (packingSol_rationalTangent n) p) := by
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨Fq, εq, hεq, hquery⟩ :=
    packingSol_uniformActualMappedPrimitiveQuery K P T hP htile E hE hrat hcover n
  obtain ⟨Ft, εt, _, hεt, _, htransport⟩ :=
    rationalPrimitiveEdges_uniformSameSide_transport K P hP E hrat hprimitive hcover
  obtain ⟨Fc, εc, _, hεc, _, hscale⟩ := finiteRationalEdges_positiveHomotheties E hrat
  refine ⟨Fq ∪ (Ft ∪ Fc), min εq (min εt εc), lt_min hεq (lt_min hεt hεc), ?_⟩
  intro φ hφ Kφ hKφ t ht p hpfront hpnot R hR hconfined
  have hφq : IsFiniteApproximation Fq εq φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_left _ hz)).trans_le (min_le_left _ _)
  have hφt : IsFiniteApproximation Ft εt φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_right _ (Finset.mem_union_left _ hz))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hφc : IsFiniteApproximation Fc εc φ := by
    refine ⟨hφ.1, fun z hz => ?_⟩
    exact (hφ.2 z (Finset.mem_union_right _ (Finset.mem_union_right _ hz))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨_, _, _, _, hfront, _⟩ := htransport φ hφt Kφ hKφ
  have hfrontier : frontier (deformPoint φ t +ᵥ Kφ.support) =
      ⋃ e ∈ E, segment ℝ (deformPoint φ t + deformPoint φ e.1)
        (deformPoint φ t + deformPoint φ e.2) := by
    rw [← sourceRay_link_frontier_vadd, hfront, Set.vadd_set_iUnion]
    simp only [Set.vadd_set_iUnion, vadd_segment, vadd_eq_add]
  obtain ⟨e, he, hpseg⟩ : ∃ e ∈ E, p ∈ segment ℝ
      (deformPoint φ t + deformPoint φ e.1) (deformPoint φ t + deformPoint φ e.2) := by
    rw [hfrontier] at hpfront
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hpfront
    obtain ⟨heE, hpseg⟩ := Set.mem_iUnion.mp he
    exact ⟨e, heE, hpseg⟩
  have endpointNot (v : Plane) (hv : v ∈ Tiling.vertexSet K.support) :
      deformPoint φ t + deformPoint φ v ≠ p := by
    intro heq
    apply hpnot
    rw [← heq]
    exact ⟨t + v, Set.mem_add.mpr ⟨v, hv, t, ht, add_comm v t⟩,
      (deformPointLinear φ).map_add t v⟩
  have hpopen := mem_openSegment_of_ne_left_right
    (endpointNot e.1 (hE e he).2.1) (endpointNot e.2 (hE e he).2.2.1) hpseg
  have hsegFront : segment ℝ (deformPoint φ t + deformPoint φ e.1)
      (deformPoint φ t + deformPoint φ e.2) ⊆ frontier (deformPoint φ t +ᵥ Kφ.support) := by
    intro z hz
    rw [hfrontier]
    exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he, hz⟩⟩
  have hnormalConfined : frontier (deformPoint φ t +ᵥ Kφ.support) ∩ Metric.ball p R ⊆
      {z | normalEval n (z - p) = 0} := by
    intro z hz
    have hside := Tiling.mem_affineLine.mp (hconfined hz)
    rw [packingSol_tangent_signedSide] at hside
    exact neg_eq_zero.mp hside
  obtain ⟨hleft, hright⟩ := packingSol_confinedPrimitive_endpoints
    (deformPoint φ t +ᵥ Kφ.support) p _ _ n R hR hsegFront hpseg hnormalConfined
  have htargetParallel : normalEval n (deformPoint φ e.2 - deformPoint φ e.1) = 0 := by
    rw [normalEval_sub] at hleft hright ⊢
    rw [normalEval_add] at hleft hright
    linarith
  obtain ⟨L, hL, _, hvec, _⟩ := hscale φ hφc e he
  have hLne : L ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hL)
  rw [hvec, ← normalCLM_apply, map_smul, smul_eq_mul, normalCLM_apply] at htargetParallel
  have holdParallel : normalEval n (e.2 - e.1) = 0 :=
    (mul_eq_zero.mp htargetParallel).resolve_left hLne
  obtain ⟨a, q, positive, hq, hcoords, hsource, _, hparams, htarget⟩ :=
    hquery φ hφq Kφ hKφ t ht e he holdParallel
  obtain ⟨u, hu, hpcoord⟩ := hparams p hpopen
  refine ⟨a, e, he, q, positive, hq, hcoords, hsource, u, hu, hpcoord, ?_⟩
  rw [hpcoord]
  exact htarget u hu


/-- The retained closed-component frontier provenance selects the ACTUAL
single component in the full labelled open carrier, even for disconnected K. -/
private theorem packingSol_singleIndex_actualBoundaryComponent
    (Kφ : PolygonalRegion) (T : Set Plane) (ψ : Plane → Plane)
    (i : PackingSolSingleFamily.SingleIndex Kφ T ψ) (p : Plane)
    (hp : p ∈ frontier (PackingSolSingleFamily.closedComponent Kφ T ψ i)) :
    ∃ x ∈ ψ i.1.1 +ᵥ Kφ.openCarrier,
      p ∈ frontier (connectedComponentIn (ψ i.1.1 +ᵥ Kφ.openCarrier) x) ∧
      ∀ s ∈ T, s ≠ (i.1.1 : Plane) →
        Disjoint (connectedComponentIn (ψ i.1.1 +ᵥ Kφ.openCarrier) x)
          (ψ s +ᵥ Kφ.openCarrier) := by
  obtain ⟨x₀, hx₀, hcomponent⟩ := i.1.2.2
  let x := ψ i.1.1 + x₀
  have hx : x ∈ ψ i.1.1 +ᵥ Kφ.openCarrier :=
    Set.mem_vadd_set.mpr ⟨x₀, hx₀, rfl⟩
  have htranslated : ψ i.1.1 +ᵥ i.1.2.1 =
      connectedComponentIn (ψ i.1.1 +ᵥ Kφ.openCarrier) x := by
    rw [hcomponent]
    simpa only [x, PolygonalRegion.openCarrier, Homeomorph.coe_addLeft,
      ← vadd_eq_add, Set.image_vadd] using
      (Homeomorph.addLeft (ψ i.1.1)).image_connectedComponentIn hx₀
  have hfrontier : frontier (ψ i.1.1 +ᵥ i.1.2.1) =
      frontier (ψ i.1.1 +ᵥ closure i.1.2.1) := by
    rw [← sourceRay_link_frontier_vadd, ← sourceRay_link_frontier_vadd,
      Kφ.isPolygonal.interiorComponent_frontier_eq i.1.2.2]
  refine ⟨x, hx, ?_, ?_⟩
  · rw [← htranslated, hfrontier]
    exact hp
  · intro s hs hsc
    rw [← htranslated]
    exact i.2 s hs hsc


private theorem packingSol_uniformActualPairedOwner_label
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) (n : RationalNormal) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ a : Plane, ∀ r : ℝ, ∀ c ∈ T, ∀ b ∈ T,
      ∀ eC ∈ E, ∀ eB ∈ E,
      ∀ qC ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) r false,
      ∀ qB ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) r true,
      ((c + eC.1 = a + qC.1 • packingSol_rationalTangent n ∧
        c + eC.2 = a + qC.2 • packingSol_rationalTangent n) ∨
       (c + eC.2 = a + qC.1 • packingSol_rationalTangent n ∧
        c + eC.1 = a + qC.2 • packingSol_rationalTangent n)) →
      ((b + eB.1 = a + qB.1 • packingSol_rationalTangent n ∧
        b + eB.2 = a + qB.2 • packingSol_rationalTangent n) ∨
       (b + eB.2 = a + qB.1 • packingSol_rationalTangent n ∧
        b + eB.1 = a + qB.2 • packingSol_rationalTangent n)) →
      (∀ u ∈ Ioo qB.1 qB.2, positiveEdgeGerm (b +ᵥ K.support)
        (packingSol_rationalTangent n) (a + u • packingSol_rationalTangent n)) →
      ∀ x ∈ deformPoint φ c +ᵥ Kφ.openCarrier,
      (∀ s ∈ T, s ≠ c → Disjoint
        (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x)
        (deformPoint φ s +ᵥ Kφ.openCarrier)) →
      ∀ z0 R : ℝ, 0 < R →
      (Metric.ball (deformPoint φ a + z0 • packingSol_rationalTangent n) R ∩
        Tiling.negativeSide (deformPoint φ a + z0 • packingSol_rationalTangent n)
          (packingSol_rationalTangent n) ⊆
        connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x) →
      z0 ∈ Ioo (φ qC.1 : ℝ) (φ qC.2 : ℝ) →
      z0 ∈ Ioo (φ qB.1 : ℝ) (φ qB.2 : ℝ) →
      ∀ aS : Plane, ∀ rS : ℝ, ∀ s ∈ T, ∀ eS ∈ E,
      ∀ qS ∈ signedCarrierComponentIntervals K T E aS (packingSol_rationalTangent n) rS true,
      ((s + eS.1 = aS + qS.1 • packingSol_rationalTangent n ∧
        s + eS.2 = aS + qS.2 • packingSol_rationalTangent n) ∨
       (s + eS.2 = aS + qS.1 • packingSol_rationalTangent n ∧
        s + eS.1 = aS + qS.2 • packingSol_rationalTangent n)) →
      (∀ u ∈ Ioo qS.1 qS.2, positiveEdgeGerm (s +ᵥ K.support)
        (packingSol_rationalTangent n) (aS + u • packingSol_rationalTangent n)) →
      ∀ uS ∈ Ioo (φ qS.1 : ℝ) (φ qS.2 : ℝ),
      deformPoint φ aS + uS • packingSol_rationalTangent n =
        deformPoint φ a + z0 • packingSol_rationalTangent n → s = b := by
  classical
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨Fp, εp, hεp, hpartner⟩ :=
    packingSol_actualSameJ_oppositeOccurrence K P T hP htile E hE hrat hcover n
  obtain ⟨Fg, εg, hεg, htarget⟩ :=
    packingSol_signedOccurrence_targetGerms K P hP E hrat hprimitive hcover
  obtain ⟨Fr, εr, hεr, hrecover⟩ :=
    packingSol_uniformMappedPrimitive_oldCarrierJRecovery K P hP E hrat hprimitive hcover
  obtain ⟨Fu, εu, hεu, hunique⟩ :=
    packingSol_uniformSameJ_sameSign_labelUnique K T htile E hE hcover d hd
  let F := Fp ∪ (Fg ∪ (Fr ∪ Fu))
  let ε := min εp (min εg (min εr εu))
  refine ⟨F, ε, lt_min hεp (lt_min hεg (lt_min hεr hεu)), ?_⟩
  intro φ hφ Kφ hKφ a r c hc b hb eC heC eB heB qC hqC qB hqB
    hcoordsC hcoordsB hsourceB x hx hsingle z0 R hR hframe hzC hzB
    aS rS s hs eS heS qS hqS hcoordsS hsourceS uS huS hpS
  have approx (A : Finset ℝ) (δ : ℝ) (hA : A ⊆ F) (hδ : ε ≤ δ) :
      IsFiniteApproximation A δ φ := finiteApproximation_strengthen A F δ ε φ hA hδ hφ
  have hφp : IsFiniteApproximation Fp εp φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto) (min_le_left _ _)
  have hφg : IsFiniteApproximation Fg εg φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans (min_le_left _ _))
  have hφr : IsFiniteApproximation Fr εr φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hφu : IsFiniteApproximation Fu εu φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hpoint (v : ℝ) : deformPoint φ aS + v • d =
      deformPoint φ a + (z0 + (v - uS)) • d := by
    calc
      _ = (deformPoint φ aS + uS • d) + (v - uS) • d := by module
      _ = _ := by rw [hpS]; module
  let W := Ioo (φ qS.1 : ℝ) (φ qS.2 : ℝ) ∩
    ((fun v : ℝ => z0 + (v - uS)) ⁻¹'
      (Ioo (φ qC.1 : ℝ) (φ qC.2 : ℝ) ∩ Ioo (φ qB.1 : ℝ) (φ qB.2 : ℝ))) ∩
    ((fun v : ℝ => deformPoint φ aS + v • d) ⁻¹'
      Metric.ball (deformPoint φ a + z0 • d) R)
  have hWopen : IsOpen W := (isOpen_Ioo.inter
    ((isOpen_Ioo.inter isOpen_Ioo).preimage (by fun_prop))).inter
    (Metric.isOpen_ball.preimage (by fun_prop))
  have huW : uS ∈ W := by
    refine ⟨⟨huS, ?_⟩, ?_⟩
    · change z0 + (uS - uS) ∈
        Ioo (φ qC.1 : ℝ) (φ qC.2 : ℝ) ∩ Ioo (φ qB.1 : ℝ) (φ qB.2 : ℝ)
      simpa only [sub_self, add_zero, Set.mem_inter_iff] using And.intro hzC hzB
    · change deformPoint φ aS + uS • d ∈ Metric.ball (deformPoint φ a + z0 • d) R
      rw [hpS]
      exact Metric.mem_ball_self hR
  obtain ⟨lo, hi, hlohi, hwindow⟩ := hWopen.exists_Ioo_subset ⟨uS, huW⟩
  have hrSource : aS + rS • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support := by
    have hr' : rS ∈ {u : ℝ | aS + u • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} :=
      connectedComponentIn_nonempty_iff.mp ⟨qS.1, hqS.2 ⟨le_rfl, hqS.1.1.le⟩⟩
    exact hr'
  obtain ⟨j, hj, _, eN, heN, qN, hqN, hcoordsN, hsourceN, hoverlap⟩ :=
    hpartner φ hφp Kφ hKφ aS rS qS.1 qS.2 hrSource hqS.1.1 hqS.2 true qS hqS
      s hs eS heS hcoordsS hsourceS lo hi hlohi (fun v hv => (hwindow hv).1.1)
  obtain ⟨v, hvwindow, hvN⟩ := hoverlap
  have hneg := htarget φ hφg Kφ hKφ n aS j eN heN qN hqN.1.1 hcoordsN
    (hE eN heN).2.2.2.2.2 false hsourceN v hvN
  rw [hpoint] at hneg
  have hjc := vertexExclusionSol_inwardLabel_of_frame Kφ T (deformPoint φ) c hc x
    hsingle (deformPoint φ a) d hd z0 R hR hframe (z0 + (v - uS))
    (by rw [← hpoint]; exact (hwindow hvwindow).2) j hj hneg
  subst j
  obtain ⟨v1, v2, hv12, hv1, hv2⟩ := vertexExclusionSol_overlap_two_points ⟨v, hvwindow, hvN⟩
  have hphysicalNe : deformPoint φ aS + v1 • d ≠ deformPoint φ aS + v2 • d := by
    intro h
    exact hv12 (smul_left_injective ℝ hd (add_left_cancel h))
  have hCopen (v : ℝ) (hv : v ∈ Ioo lo hi) :
      deformPoint φ aS + v • d ∈ openSegment ℝ
        (deformPoint φ c + deformPoint φ eC.1) (deformPoint φ c + deformPoint φ eC.2) := by
    rw [hpoint]
    exact vertexExclusionSol_occurrence_mappedOpen φ n a c eC qC hcoordsC _
      (hwindow hv).1.2.1
  have hNopen (v : ℝ) (hv : v ∈ Ioo (φ qN.1 : ℝ) (φ qN.2 : ℝ)) :
      deformPoint φ aS + v • d ∈ openSegment ℝ
        (deformPoint φ c + deformPoint φ eN.1) (deformPoint φ c + deformPoint φ eN.2) :=
    vertexExclusionSol_occurrence_mappedOpen φ n aS c eN qN hcoordsN v hv
  obtain ⟨shift, hanchor, hJ⟩ := hrecover φ hφr Kφ hKφ T a aS d c r rS false false
    qC hqC qN hqN eC heC eN heN hcoordsC hcoordsN _ _ hphysicalNe
    (hCopen v1 hv1.1) (hNopen v1 hv1.2) (hCopen v2 hv2.1) (hNopen v2 hv2.2)
  obtain ⟨hqB', hcoordsB', hsourceB'⟩ := packingSol_actualOccurrence_reanchor_sameJ
    K T E a aS d b r rS shift true hanchor hJ hb eB heB qB hqB hcoordsB hsourceB
  have hreanchor := packingSol_realMappedCarrier_reanchor φ n a aS shift hanchor
  have huB' := hreanchor.2 qB z0 hzB
  have hscalar : z0 - (φ shift : ℝ) = uS := by
    have h := (hreanchor.1 z0).symm.trans hpS.symm
    exact smul_left_injective ℝ hd (add_left_cancel h)
  rw [hscalar] at huB'
  exact (hunique φ hφu aS rS qS.1 qS.2 hrSource hqS.1.1 hqS.2 true
    qS hqS (qB.1 - shift, qB.2 - shift) hqB' s hs b hb hsourceS hsourceB'
    uS huS huB').2


private theorem packingSol_componentFrame_localClosedSupport
    (Kφ : PolygonalRegion) (b x p d : Plane) (hd : d ≠ 0) (R : ℝ) (hR : 0 < R)
    (hframe : Metric.ball p R ∩ Tiling.negativeSide p d ⊆
      connectedComponentIn (b +ᵥ Kφ.openCarrier) x)
    (hown : (b +ᵥ Kφ.support) ∩ Metric.ball p R =
      Tiling.negativeHalfPlane p d ∩ Metric.ball p R) :
    closure (connectedComponentIn (b +ᵥ Kφ.openCarrier) x) ∩ Metric.ball p R =
      (b +ᵥ Kφ.support) ∩ Metric.ball p R := by
  let O := connectedComponentIn (b +ᵥ Kφ.openCarrier) x
  have hclosed : IsClosed (b +ᵥ Kφ.support) := Kφ.isPolygonal.isClosed.vadd b
  have hOS : O ⊆ b +ᵥ Kφ.support := fun z hz =>
    (Set.vadd_set_mono interior_subset) (connectedComponentIn_subset _ _ hz)
  apply Set.Subset.antisymm
  · exact Set.inter_subset_inter_left _ (closure_minimal hOS hclosed)
  · intro z hz
    refine ⟨?_, hz.2⟩
    have hnonpos := Tiling.mem_negativeHalfPlane.mp
      (((Set.ext_iff.mp hown z).mp hz).1)
    rcases lt_or_eq_of_le hnonpos with hneg | hzero
    · exact subset_closure (hframe ⟨hz.2, Tiling.mem_negativeSide.mpr hneg⟩)
    · have hmargin : 0 < R - dist z p := by linarith [Metric.mem_ball.mp hz.2]
      have hlocal : Metric.ball z (R - dist z p) ∩ Tiling.positiveSide z (-d) ⊆ O := by
        intro w hw
        apply hframe
        constructor
        · exact Metric.mem_ball.mpr (by
            linarith [Metric.mem_ball.mp hw.1, dist_triangle w z p])
        · have hpos := Tiling.mem_positiveSide.mp hw.2
          apply Tiling.mem_negativeSide.mpr
          have hbase : Tiling.signedSide p d w =
              Tiling.signedSide z d w + Tiling.signedSide p d z := by
            simp only [Tiling.signedSide, Tiling.planarCross]
            ring
          have hnegdir : Tiling.signedSide z (-d) w = -Tiling.signedSide z d w := by
            simp only [Tiling.signedSide, Tiling.planarCross, Complex.neg_re, Complex.neg_im]
            ring
          rw [hbase, hzero, add_zero]
          rw [hnegdir] at hpos
          linarith
      exact closure_mono hlocal (packingSol_positiveHalfBall_center_closure z (-d)
        (neg_ne_zero.mpr hd) _ hmargin)



private theorem packingSol_uniformActualLocalExclusiveClosedWitness
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) (n : RationalNormal) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ a : Plane, ∀ r : ℝ, ∀ c ∈ T, ∀ b ∈ T,
      ∀ eC ∈ E, ∀ eB ∈ E,
      ∀ qC ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) r false,
      ∀ qB ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) r true,
      ((c + eC.1 = a + qC.1 • packingSol_rationalTangent n ∧
        c + eC.2 = a + qC.2 • packingSol_rationalTangent n) ∨
       (c + eC.2 = a + qC.1 • packingSol_rationalTangent n ∧
        c + eC.1 = a + qC.2 • packingSol_rationalTangent n)) →
      ((b + eB.1 = a + qB.1 • packingSol_rationalTangent n ∧
        b + eB.2 = a + qB.2 • packingSol_rationalTangent n) ∨
       (b + eB.2 = a + qB.1 • packingSol_rationalTangent n ∧
        b + eB.1 = a + qB.2 • packingSol_rationalTangent n)) →
      (∀ u ∈ Ioo qB.1 qB.2, positiveEdgeGerm (b +ᵥ K.support)
        (packingSol_rationalTangent n) (a + u • packingSol_rationalTangent n)) →
      ∀ x ∈ deformPoint φ c +ᵥ Kφ.openCarrier,
      (∀ s ∈ T, s ≠ c → Disjoint
        (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x)
        (deformPoint φ s +ᵥ Kφ.openCarrier)) →
      ∀ z0 R : ℝ, 0 < R →
      (Metric.ball (deformPoint φ a + z0 • packingSol_rationalTangent n) R ∩
        Tiling.negativeSide (deformPoint φ a + z0 • packingSol_rationalTangent n)
          (packingSol_rationalTangent n) ⊆
        connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x) →
      ((deformPoint φ c +ᵥ Kφ.support) ∩
        Metric.ball (deformPoint φ a + z0 • packingSol_rationalTangent n) R =
        Tiling.negativeHalfPlane (deformPoint φ a + z0 • packingSol_rationalTangent n)
          (packingSol_rationalTangent n) ∩
        Metric.ball (deformPoint φ a + z0 • packingSol_rationalTangent n) R) →
      z0 ∈ Ioo (φ qC.1 : ℝ) (φ qC.2 : ℝ) →
      z0 ∈ Ioo (φ qB.1 : ℝ) (φ qB.2 : ℝ) →
      ∀ Rv : ℝ, 0 < Rv →
      Disjoint (Metric.ball (deformPoint φ a + z0 • packingSol_rationalTangent n) Rv)
        (deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T) →
      ∃ y ∈ deformPoint φ b +ᵥ Kφ.openCarrier,
        y ∈ Metric.ball (deformPoint φ a + z0 • packingSol_rationalTangent n) R ∧
        y ∈ Tiling.positiveSide (deformPoint φ a + z0 • packingSol_rationalTangent n)
          (packingSol_rationalTangent n) ∧
        ∀ s ∈ T, s ≠ b → y ∉ deformPoint φ s +ᵥ Kφ.support := by
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨Fc, εc, hεc, hconfine⟩ :=
    packingSol_uniformActualLocalFrontierConfinement K P T hP htile E hE hrat hcover n
  obtain ⟨Fo, εo, hεo, hoccurrence⟩ :=
    packingSol_uniformActualLocalBoundaryOccurrence K P T hP htile E hE hrat hcover n
  obtain ⟨Fl, εl, hεl, hlabel⟩ :=
    packingSol_uniformActualPairedOwner_label K P T hP htile E hE hrat hcover n
  obtain ⟨Fg, εg, hεg, htarget⟩ :=
    packingSol_signedOccurrence_targetGerms K P hP E hrat hprimitive hcover
  let F := Fc ∪ (Fo ∪ (Fl ∪ Fg))
  let ε := min εc (min εo (min εl εg))
  refine ⟨F, ε, lt_min hεc (lt_min hεo (lt_min hεl hεg)), ?_⟩
  intro φ hφ Kφ hKφ a r c hc b hb eC heC eB heB qC hqC qB hqB
    hcoordsC hcoordsB hsourceB x hx hsingle z0 R hR hframe hown hzC hzB Rv hRv hfree
  have approx (A : Finset ℝ) (δ : ℝ) (hA : A ⊆ F) (hδ : ε ≤ δ) :
      IsFiniteApproximation A δ φ := finiteApproximation_strengthen A F δ ε φ hA hδ hφ
  have hφc : IsFiniteApproximation Fc εc φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto) (min_le_left _ _)
  have hφo : IsFiniteApproximation Fo εo φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans (min_le_left _ _))
  have hφl : IsFiniteApproximation Fl εl φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hφg : IsFiniteApproximation Fg εg φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let p := deformPoint φ a + z0 • d
  obtain ⟨ρc, hρc, hρcR, _, hconfined⟩ :=
    hconfine φ hφc Kφ hKφ c hc x hx p R hR hsingle hframe hown Rv hRv hfree
  have hBgerm : positiveEdgeGerm (deformPoint φ b +ᵥ Kφ.support) d p :=
    htarget φ hφg Kφ hKφ n a b eB heB qB hqB.1.1 hcoordsB
      (hE eB heB).2.2.2.2.2 true hsourceB z0 hzB
  obtain ⟨ρb, hρb, hBstrip⟩ := hBgerm
  let ρ := min ρc ρb
  have hρ : 0 < ρ := lt_min hρc hρb
  let U := Metric.ball p ρ ∩ Tiling.positiveSide p d
  have hUopen : IsOpen U := Metric.isOpen_ball.inter (Tiling.isOpen_positiveSide p d)
  have hUpre : IsPreconnected U := Tiling.isPreconnected_ball_inter_positiveSide p d ρ
  have hUfront (s : Plane) (hs : s ∈ T) :
      Disjoint U (frontier (deformPoint φ s +ᵥ Kφ.support)) := by
    apply Set.disjoint_left.mpr
    intro z hz hzfront
    have hzline := hconfined s hs ⟨hzfront,
      Metric.mem_ball.mpr ((Metric.mem_ball.mp hz.1).trans_le (min_le_left _ _))⟩
    have hzero := Tiling.mem_affineLine.mp hzline
    exact (ne_of_gt (Tiling.mem_positiveSide.mp hz.2)) hzero
  have hUBsupport : U ⊆ deformPoint φ b +ᵥ Kφ.support := by
    intro z hz
    exact ((Set.ext_iff.mp hBstrip z).mpr
      ⟨Tiling.mem_positiveHalfPlane.mpr (Tiling.mem_positiveSide.mp hz.2).le,
        Metric.mem_ball.mpr ((Metric.mem_ball.mp hz.1).trans_le (min_le_right _ _))⟩).1
  have hUBopen : U ⊆ deformPoint φ b +ᵥ Kφ.openCarrier := by
    simpa only [PolygonalRegion.openCarrier, interior_vadd] using
      hUopen.subset_interior_iff.mpr hUBsupport
  obtain ⟨y, hyU⟩ := packingSol_positiveHalfBall_point p d hd ρ hρ
  have hownFront := packingSol_negativeStrip_carrierFrontier
    (deformPoint φ c +ᵥ Kφ.support) p d hd R hR hown
  have havoid := packingSol_singleComponent_localLineAvoidance Kφ T (deformPoint φ)
    c hc x hx hsingle p d hd R hR hframe hownFront
  have hpnot : p ∉ deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T :=
    fun hpV => Set.disjoint_left.mp hfree (Metric.mem_ball_self hRv) hpV
  refine ⟨y, hUBopen hyU,
    Metric.mem_ball.mpr ((Metric.mem_ball.mp hyU.1).trans_le
      ((min_le_left _ _).trans hρcR)), hyU.2, ?_⟩
  intro s hs hsb hyclosed
  have hyopen : y ∈ deformPoint φ s +ᵥ Kφ.openCarrier := by
    by_contra hynot
    exact Set.disjoint_left.mp (hUfront s hs) hyU (by
      rw [(Kφ.isPolygonal.isClosed.vadd _).frontier_eq, interior_vadd]
      exact ⟨hyclosed, hynot⟩)
  have hUinside := packingSol_frontierFree_preconnected_copyInterior Kφ
    (deformPoint φ s) U hUpre (hUfront s hs) ⟨y, hyU, hyopen⟩
  have hpSupport : p ∈ deformPoint φ s +ᵥ Kφ.support := by
    have h := closure_mono hUinside
      (packingSol_positiveHalfBall_center_closure p d hd ρ hρ)
    simpa only [closure_vadd, PolygonalRegion.openCarrier,
      Kφ.isPolygonal.closure_interior] using h
  have hpFront : p ∈ frontier (deformPoint φ s +ᵥ Kφ.support) := by
    rw [(Kφ.isPolygonal.isClosed.vadd _).frontier_eq, interior_vadd]
    exact ⟨hpSupport, fun hpopen => Set.disjoint_left.mp (havoid s hs)
      ⟨Tiling.mem_affineLine_self p d, Metric.mem_ball_self hR⟩ hpopen⟩
  obtain ⟨aS, eS, heS, qS, positive, hqS, hcoordsS, hsourceS, uS, huS, hpcoord, hSgerm⟩ :=
    hoccurrence φ hφo Kφ hKφ s hs p hpFront hpnot ρ hρ
      (fun z hz => hconfined s hs ⟨hz.1,
        Metric.mem_ball.mpr ((Metric.mem_ball.mp hz.2).trans_le (min_le_left _ _))⟩)
  cases positive with
  | false =>
    exact packingSol_positiveHalfBall_not_negativeGerm
      (deformPoint φ s +ᵥ Kφ.support) p d hd ρ hρ
      (fun z hz => Set.vadd_set_mono interior_subset (hUinside hz)) hSgerm
  | true =>
    have hsbEq := hlabel φ hφl Kφ hKφ a r c hc b hb eC heC eB heB
      qC hqC qB hqB hcoordsC hcoordsB hsourceB x hx hsingle z0 R hR hframe hzC hzB
      aS 0 s hs eS heS qS hqS hcoordsS hsourceS uS huS hpcoord.symm
    exact hsb hsbEq


private theorem packingSol_singleOpenUnion_isOpen
    (Kφ : PolygonalRegion) (T : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ) :
    IsOpen (packingSol_singleOpenUnion Kφ T φ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  obtain ⟨c, hc, x, hx, hyO, hsingle⟩ := hy
  have hOopen : IsOpen (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x) :=
    (isOpen_interior.vadd (deformPoint φ c)).connectedComponentIn
  exact Filter.mem_of_superset (hOopen.mem_nhds hyO)
    (fun z hz => ⟨c, hc, x, hx, hz, hsingle⟩)

private theorem packingSol_singleClosedUnion_regular
    (Kφ : PolygonalRegion) (T : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ) :
    closure (interior (PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ))) =
      PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ) := by
  rw [packingSol_singleClosedUnion_eq_closure]
  have h := closure_interior_idem (s := packingSol_singleOpenUnion Kφ T φ)
  simpa only [(packingSol_singleOpenUnion_isOpen Kφ T φ).interior_eq] using h

/-- The ACTUAL single-component frame instantiates the regular-closed union
classifier; no independent halfplane certificate for the union is assumed. -/
private theorem packingSol_singleComponent_unionNegativeGerm
    (Kφ : PolygonalRegion) (T : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ)
    (c : Plane) (hc : c ∈ T) (x : Plane) (hx : x ∈ deformPoint φ c +ᵥ Kφ.openCarrier)
    (hsingle : ∀ s ∈ T, s ≠ c → Disjoint
      (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x)
      (deformPoint φ s +ᵥ Kφ.openCarrier))
    (p d : Plane) (hd : d ≠ 0)
    (hp : p ∈ frontier (PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ)))
    (hstraight : Tiling.BoundaryLocallyStraightAt
      (PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ)) p)
    (R : ℝ) (hR : 0 < R)
    (hframe : Metric.ball p R ∩ Tiling.negativeSide p d ⊆
      connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ) ∩ Metric.ball p r =
        Tiling.negativeHalfPlane p d ∩ Metric.ball p r := by
  have hinside : Metric.ball p R ∩ Tiling.negativeSide p d ⊆
      interior (PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ)) := by
    rw [packingSol_singleClosedUnion_eq_closure]
    intro z hz
    apply (packingSol_singleOpenUnion_isOpen Kφ T φ).subset_interior_closure
    exact ⟨c, hc, x, hx, hframe hz, hsingle⟩
  exact packingSol_regularClosed_straight_negativeHalfBall _ p d
    (packingSol_singleClosedUnion_regular Kφ T φ) hp hstraight hd R hR hinside


private theorem packingSol_strip_shrink
    (S H : Set Plane) (p : Plane) (R r : ℝ) (hrR : r ≤ R)
    (hstrip : S ∩ Metric.ball p R = H ∩ Metric.ball p R) :
    S ∩ Metric.ball p r = H ∩ Metric.ball p r := by
  have hsub : Metric.ball p r ⊆ Metric.ball p R := Metric.ball_subset_ball hrR
  calc
    S ∩ Metric.ball p r = (S ∩ Metric.ball p R) ∩ Metric.ball p r := by
      rw [Set.inter_assoc, Set.inter_eq_right.mpr hsub]
    _ = (H ∩ Metric.ball p R) ∩ Metric.ball p r := by rw [hstrip]
    _ = H ∩ Metric.ball p r := by rw [Set.inter_assoc, Set.inter_eq_right.mpr hsub]

/-- A SINGLE positive neighbour contradicts the genuine union's inward germ
using one actual local positive point, not an assumed covering ball. -/
private theorem packingSol_singleComponent_point_contradicts_unionNegative
    (Kφ : PolygonalRegion) (T : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ)
    (b : Plane) (hb : b ∈ T) (y : Plane) (hy : y ∈ deformPoint φ b +ᵥ Kφ.openCarrier)
    (hsingle : ∀ s ∈ T, s ≠ b → Disjoint
      (connectedComponentIn (deformPoint φ b +ᵥ Kφ.openCarrier) y)
      (deformPoint φ s +ᵥ Kφ.openCarrier))
    (p d : Plane) (R : ℝ) (hyball : y ∈ Metric.ball p R)
    (hypositive : y ∈ Tiling.positiveSide p d)
    (hunion : PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ) ∩
        Metric.ball p R = Tiling.negativeHalfPlane p d ∩ Metric.ball p R) : False := by
  have hyunion : y ∈ packingSol_singleOpenUnion Kφ T φ :=
    ⟨b, hb, y, hy, mem_connectedComponentIn hy, hsingle⟩
  have hyclosed : y ∈ PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ) := by
    rw [packingSol_singleClosedUnion_eq_closure]
    exact subset_closure hyunion
  have hynegative := ((Set.ext_iff.mp hunion y).mp ⟨hyclosed, hyball⟩).1
  exact (not_le_of_gt (Tiling.mem_positiveSide.mp hypositive))
    (Tiling.mem_negativeHalfPlane.mp hynegative)



private theorem packingSol_nonparallelEdge_vertexFreeBall
    (K : PolygonalRegion) (T : Set Plane) (n : RationalNormal)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a : Plane) (ha : Tiling.RationalSlopes.IsProperLink K (normalDirection n) T a) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ v w : Plane, normalEval n (w - v) ≠ 0 →
          ∃ p ∈ openSegment ℝ v w, ∃ r : ℝ, 0 < r ∧
            Disjoint (Metric.ball p r)
              (deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T) := by
  obtain ⟨F, ε, hε, hlevels⟩ :=
    properLink_imageNormalLevels_locallyFinite K T n hrat htile a ha
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ v w hnonparallel
  let V : Set ℝ := normalEval n ''
    (deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T)
  have hVfinite : ∀ Q : Set ℝ, Bornology.IsBounded Q → (V ∩ Q).Finite :=
    hlevels φ hφ
  have hVclosed : IsClosed V := packingSol_scalarLevels_isClosed V hVfinite
  let Q : Set ℝ := normalEval n '' segment ℝ v w
  have hQcompact : IsCompact Q := by
    apply IsCompact.image ?_ (normalCLM n).continuous
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  have hFlevels : (V ∩ Q).Finite := hVfinite Q hQcompact.isBounded
  let g : ℝ → ℝ := fun t => normalEval n v + t * normalEval n (w - v)
  have hginj : Function.Injective g := by
    intro s t hst
    dsimp [g] at hst
    exact (mul_left_injective₀ hnonparallel) (add_left_cancel hst)
  have hbad : (g ⁻¹' (V ∩ Q)).Finite := hFlevels.preimage hginj.injOn
  obtain ⟨t, ht, htnot⟩ := (Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finite hbad
  let p : Plane := AffineMap.lineMap v w t
  have hpsegment : p ∈ openSegment ℝ v w := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  have hpg : normalEval n p = g t := by
    change normalCLM n p = g t
    simp only [p, g, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      map_add, map_smul, normalCLM_apply, smul_eq_mul]
    ring
  have hpQ : normalEval n p ∈ Q :=
    Set.mem_image_of_mem _ (openSegment_subset_segment ℝ _ _ hpsegment)
  have hpnot : normalEval n p ∉ V := by
    intro hpV
    exact htnot (show g t ∈ V ∩ Q from hpg ▸ ⟨hpV, hpQ⟩)
  have hopen : IsOpen ((normalCLM n) ⁻¹' Vᶜ) :=
    hVclosed.isOpen_compl.preimage (normalCLM n).continuous
  have hpmem : p ∈ (normalCLM n) ⁻¹' Vᶜ := hpnot
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen p hpmem
  refine ⟨p, hpsegment, r, hr, Set.disjoint_left.mpr ?_⟩
  intro z hz hvertex
  exact hball hz (Set.mem_image_of_mem _ hvertex)



private def packingSol_oppositeNormal (n : RationalNormal) : RationalNormal :=
  ⟨-n.x, -n.y, n.nonzero.imp
    (fun h => neg_ne_zero.mpr h) (fun h => neg_ne_zero.mpr h)⟩

private theorem packingSol_oppositeNormal_normalEval (n : RationalNormal) (z : Plane) :
    normalEval (packingSol_oppositeNormal n) z = -normalEval n z := by
  simp only [packingSol_oppositeNormal, normalEval, Rat.cast_neg]
  ring

private theorem packingSol_oppositeNormal_normalDirection (n : RationalNormal) :
    normalDirection (packingSol_oppositeNormal n) = normalDirection n := by
  ext z
  change normalEval (packingSol_oppositeNormal n) z = 0 ↔ normalEval n z = 0
  rw [packingSol_oppositeNormal_normalEval, neg_eq_zero]

private theorem packingSol_oppositeNormal_rationalTangent (n : RationalNormal) :
    packingSol_rationalTangent (packingSol_oppositeNormal n) =
      -packingSol_rationalTangent n := by
  apply Complex.ext <;>
    simp [packingSol_rationalTangent, packingSol_oppositeNormal]

private theorem packingSol_oppositeNormal_involutive (n : RationalNormal) :
    packingSol_oppositeNormal (packingSol_oppositeNormal n) = n := by
  cases n
  simp [packingSol_oppositeNormal]

/-- The fixed SOURCE edge family supplies finitely many normals, with BOTH
orientations chosen before any deformation or queried partial carrier. -/
private theorem packingSol_finiteSourceNormals (E : Finset (Plane × Plane))
    (hrat : ∀ e ∈ E,
      Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1)) :
    ∃ N : Finset RationalNormal, ∀ e ∈ E, ∃ n ∈ N,
      packingSol_oppositeNormal n ∈ N ∧
      normalDirection n = Submodule.span ℝ ({e.2 - e.1} : Set Plane) := by
  classical
  let chooseNormal : {e : Plane × Plane // e ∈ E} → RationalNormal := fun e =>
    Classical.choose (rationalDirection_hasNormal
      (Submodule.span ℝ ({e.1.2 - e.1.1} : Set Plane))
      (finrank_span_singleton (hrat e.1 e.2).1) (hrat e.1 e.2).2)
  have hchoose (e : {e : Plane × Plane // e ∈ E}) :
      normalDirection (chooseNormal e) =
        Submodule.span ℝ ({e.1.2 - e.1.1} : Set Plane) :=
    Classical.choose_spec (rationalDirection_hasNormal
      (Submodule.span ℝ ({e.1.2 - e.1.1} : Set Plane))
      (finrank_span_singleton (hrat e.1 e.2).1) (hrat e.1 e.2).2)
  let A := E.attach.image chooseNormal
  refine ⟨A ∪ A.image packingSol_oppositeNormal, ?_⟩
  intro e he
  let i : {e : Plane × Plane // e ∈ E} := ⟨e, he⟩
  have hi : i ∈ E.attach := Finset.mem_attach E i
  have hnA : chooseNormal i ∈ A := Finset.mem_image.mpr ⟨i, hi, rfl⟩
  refine ⟨chooseNormal i, Finset.mem_union_left _ hnA,
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨chooseNormal i, hnA, rfl⟩), ?_⟩
  exact hchoose i

/-- Combine already-constructed actual per-normal controls over one fixed
finite SOURCE family. The tests and positive threshold precede phi. -/
private theorem packingSol_finiteNormal_controls (N : Finset RationalNormal)
    (C : RationalNormal → (ℝ →ₗ[ℚ] ℚ) → Prop)
    (hlocal : ∀ n ∈ N, ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ → C n φ) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ → ∀ n ∈ N, C n φ := by
  obtain ⟨F, ε, _, hε, _, hcontrols⟩ :=
    finiteApproximation_uniformPositiveRadius N (fun n φ _ => C n φ)
      (fun _ _ _ _ _ _ h => h)
      (by
        intro n hn
        obtain ⟨Fn, εn, hεn, hCn⟩ := hlocal n hn
        exact ⟨Fn, εn, 1, hεn, by norm_num, hCn⟩)
  exact ⟨F, ε, hε, hcontrols⟩



private theorem packingSol_localIntersection_eventuallyEq
    (S U : Set Plane) (p : Plane) (R : ℝ) (hR : 0 < R)
    (hlocal : S ∩ Metric.ball p R = U ∩ Metric.ball p R) : S =ᶠ[𝓝 p] U := by
  filter_upwards [Metric.ball_mem_nhds p hR] with z hz
  apply propext
  change z ∈ S ↔ z ∈ U
  have h := Set.ext_iff.mp hlocal z
  simpa only [Set.mem_inter_iff, hz, and_true] using h

private theorem packingSol_localClosedCoincidence_genericFrontier
    (S O U : Set Plane) (hS : Tiling.IsPolygonal S) (hO : IsClosed O) (hU : IsClosed U)
    (p : Plane) (hp : p ∈ frontier S) (R : ℝ) (hR : 0 < R)
    (hSO : S ∩ Metric.ball p R = O ∩ Metric.ball p R)
    (hSU : S ∩ Metric.ball p R = U ∩ Metric.ball p R)
    (V : Set Plane) (hV : V.Finite) :
    ∃ q : Plane, q ∈ frontier S ∧ q ∈ frontier O ∧ q ∈ frontier U ∧
      q ∉ V ∧ (S =ᶠ[𝓝 q] U) := by
  have hEqSO := packingSol_localIntersection_eventuallyEq S O p R hR hSO
  have hEqSU := packingSol_localIntersection_eventuallyEq S U p R hR hSU
  have hfrontSO := PackingSolSingleFamily.frontier_eventuallyEq_of_closed hS.isClosed hO hEqSO
  have hfrontSU := PackingSolSingleFamily.frontier_eventuallyEq_of_closed hS.isClosed hU hEqSU
  have hnear : ∀ᶠ q in 𝓝 p,
      (q ∈ frontier S) = (q ∈ frontier O) ∧
      (q ∈ frontier S) = (q ∈ frontier U) ∧ (S =ᶠ[𝓝 q] U) := by
    filter_upwards [hfrontSO, hfrontSU, hEqSU.eventually_nhds] with q hqO hqU hqEq
    exact ⟨hqO, hqU, hqEq⟩
  obtain ⟨q, hqS, hqNear, hqNot⟩ :=
    PackingSolSingleFamily.polygonal_frontier_near_avoiding hS hV hp hnear
  exact ⟨q, hqS, Eq.mp hqNear.1 hqS, Eq.mp hqNear.2.1 hqS, hqNot, hqNear.2.2⟩

/-- Before choosing a SOURCE direction, genuine target geometry gives a
nearby frontier point avoiding the selected label's finite mapped OLD vertices.
Local closed-set coincidence preserves BOTH actual component and union
frontiers throughout that move. -/
private theorem packingSol_actualSingleBoundary_genericPoint
    (Kφ : PolygonalRegion) (T : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ)
    (c : Plane) (hc : c ∈ T) (x : Plane) (hx : x ∈ deformPoint φ c +ᵥ Kφ.openCarrier)
    (hsingle : ∀ s ∈ T, s ≠ c → Disjoint
      (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x)
      (deformPoint φ s +ᵥ Kφ.openCarrier))
    (p : Plane)
    (hpUnion : p ∈ frontier (PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ)))
    (hpComponent : p ∈ frontier (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x))
    (hpFull : p ∈ frontier (deformPoint φ c +ᵥ Kφ.support))
    (hpNotActual : p ∉ deformPoint φ c +ᵥ Tiling.vertexSet Kφ.support)
    (hstraight : Tiling.BoundaryLocallyStraightAt
      (PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ)) p)
    (V : Set Plane) (hV : V.Finite) :
    ∃ q : Plane,
      q ∈ frontier (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x) ∧
      q ∈ frontier (PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ)) ∧
      q ∈ frontier (deformPoint φ c +ᵥ Kφ.support) ∧ q ∉ V ∧
      ((deformPoint φ c +ᵥ Kφ.support) =ᶠ[𝓝 q]
        PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ)) := by
  let S := deformPoint φ c +ᵥ Kφ.support
  let O := connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x
  let U := PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ)
  have hS : Tiling.IsPolygonal S := Kφ.isPolygonal.vadd (deformPoint φ c)
  have hpNot : p ∉ Tiling.vertexSet S := by
    simpa only [S, Tiling.vertexSet_vadd] using hpNotActual
  obtain ⟨L, hpL, hdim, hlocal⟩ := hS.boundaryLocallyStraightAt_of_not_mem_vertexSet hpFull hpNot
  obtain ⟨v, hv, Rv, hRv, hcases⟩ :=
    Tiling.exists_local_eq_closedHalfPlane_of_affineSubspace hS.closure_interior hpL hdim hlocal
  have hnegative : ∃ d : Plane, d ≠ 0 ∧ negativeEdgeGerm S d p := by
    rcases hcases with hpositive | hnegative
    · exact ⟨-v, neg_ne_zero.mpr hv,
        (orientedEdgeGerms_negativeDirection S p v).2.mpr ⟨Rv, hRv, hpositive⟩⟩
    · exact ⟨v, hv, Rv, hRv, hnegative⟩
  obtain ⟨d, hd, hgerm⟩ := hnegative
  obtain ⟨Rf, hRf, hframe, _⟩ := packingSol_actualComponent_negativeBoundaryFrame
    Kφ (deformPoint φ c) x p d hx hd hpComponent hgerm
  obtain ⟨Rs, hRs, hstripS⟩ := hgerm
  obtain ⟨Ru, hRu, _, hstripU⟩ := packingSol_singleComponent_unionNegativeGerm
    Kφ T φ c hc x hx hsingle p d hd hpUnion hstraight Rf hRf hframe
  let R := min Rf (min Rs Ru)
  have hR : 0 < R := lt_min hRf (lt_min hRs hRu)
  have hRRf : R ≤ Rf := min_le_left _ _
  have hRRs : R ≤ Rs := (min_le_right _ _).trans (min_le_left _ _)
  have hRRu : R ≤ Ru := (min_le_right _ _).trans (min_le_right _ _)
  have hstripS' := packingSol_strip_shrink S (Tiling.negativeHalfPlane p d) p Rs R hRRs hstripS
  have hstripU' := packingSol_strip_shrink U (Tiling.negativeHalfPlane p d) p Ru R hRRu hstripU
  have hframe' : Metric.ball p R ∩ Tiling.negativeSide p d ⊆ O :=
    fun z hz => hframe ⟨Metric.ball_subset_ball hRRf hz.1, hz.2⟩
  have hSO : S ∩ Metric.ball p R = closure O ∩ Metric.ball p R :=
    (packingSol_componentFrame_localClosedSupport Kφ (deformPoint φ c) x p d hd R hR
      hframe' hstripS').symm
  have hSU : S ∩ Metric.ball p R = U ∩ Metric.ball p R := hstripS'.trans hstripU'.symm
  have hUclosed : IsClosed U := by
    change IsClosed (PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ))
    rw [packingSol_singleClosedUnion_eq_closure]
    exact isClosed_closure
  obtain ⟨q, hqFull, hqClosureO, hqUnion, hqNot, hqEq⟩ :=
    packingSol_localClosedCoincidence_genericFrontier S (closure O) U hS isClosed_closure
      hUclosed p hpFull R hR hSO hSU V hV
  have hOmembership : O ∈ Tiling.interiorComponents S := by
    refine ⟨x, ?_, ?_⟩
    · simpa only [S, interior_vadd, PolygonalRegion.openCarrier] using hx
    · simp only [S, O, interior_vadd, PolygonalRegion.openCarrier]
  have hqO : q ∈ frontier O := by
    rw [hS.interiorComponent_frontier_eq hOmembership]
    exact hqClosureO
  exact ⟨q, hqO, hqUnion, hqFull, hqNot, hqEq⟩



/-- A REAL affine interval avoiding all mapped OLD vertices has a point
with a genuine vertex-free ball. Fixed selected-link controls precede phi;
the queried interval need not extend to any full proper link. -/
private theorem packingSol_uniformRealInterval_vertexFreeBall
    (K : PolygonalRegion) (T : Set Plane) (n₀ : RationalNormal)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a₀ : Plane)
    (ha₀ : Tiling.RationalSlopes.IsProperLink K (normalDirection n₀) T a₀) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ b d : Plane, d ≠ 0 → ∀ L H : ℝ, L < H →
      (∀ u ∈ Ioo L H,
        b + u • d ∉ deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T) →
      ∃ u ∈ Ioo L H, ∃ r : ℝ, 0 < r ∧
        Disjoint (Metric.ball (b + u • d) r)
          (deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T) := by
  obtain ⟨Ft, εt, hεt, htransverse⟩ :=
    packingSol_nonparallelEdge_vertexFreeBall K T n₀ hrat htile a₀ ha₀
  obtain ⟨Fp, εp, hεp, hparallel⟩ :=
    packingSol_uniformParallelPatch_vertexFreeBall K T n₀ hrat htile a₀ ha₀
  refine ⟨Ft ∪ Fp, min εt εp, lt_min hεt hεp, ?_⟩
  intro φ hφ b d hd L H hLH havoid
  have hφt := finiteApproximation_strengthen Ft (Ft ∪ Fp) εt (min εt εp) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφp := finiteApproximation_strengthen Fp (Ft ∪ Fp) εp (min εt εp) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  by_cases hzero : normalEval n₀ d = 0
  · let u : ℝ := (L + H) / 2
    have hu : u ∈ Ioo L H := by
      dsimp only [u]
      constructor <;> linarith
    let p : Plane := b + u • d
    let R : ℝ := ((H - L) / 2) * ‖d‖
    have hnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
    have hR : 0 < R := mul_pos (by linarith) hnorm
    have hdmem : d ∈ normalDirection n₀ :=
      (normalDirection_mem_iff n₀ d).mpr hzero
    have hspan : normalDirection n₀ = Submodule.span ℝ ({d} : Set Plane) :=
      eq_span_singleton_of_mem_of_finrank_eq_one (normalDirection_rational n₀).1 hdmem hd
    have hpatch : ∀ z ∈ Metric.ball p R,
        normalEval n₀ z = normalEval n₀ p →
        z ∉ deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T := by
      intro z hz hlevel
      have hzmem : z - p ∈ Submodule.span ℝ ({d} : Set Plane) := by
        rw [← hspan]
        apply (normalDirection_mem_iff n₀ _).mpr
        rw [normalEval_sub, hlevel, sub_self]
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzmem
      have hzcoord : z = p + c • d := by rw [hc]; abel
      have hdist : dist z p = |c| * ‖d‖ := by
        rw [dist_eq_norm, ← hc, norm_smul, Real.norm_eq_abs]
      have hcabs : |c| < (H - L) / 2 := by
        have hmul : |c| * ‖d‖ < ((H - L) / 2) * ‖d‖ := by
          rw [← hdist]
          exact Metric.mem_ball.mp hz
        exact lt_of_mul_lt_mul_right hmul (norm_nonneg d)
      have huc : u + c ∈ Ioo L H := by
        obtain ⟨hclo, hchi⟩ := abs_lt.mp hcabs
        dsimp only [u]
        constructor <;> linarith
      have hzcoord' : z = b + (u + c) • d := by
        rw [hzcoord]
        dsimp only [p]
        module
      rw [hzcoord']
      exact havoid (u + c) huc
    obtain ⟨r, hr, _, hfree⟩ := hparallel φ hφp p R hR hpatch
    exact ⟨u, hu, r, hr, hfree⟩
  · have hdiff : (b + H • d) - (b + L • d) = (H - L) • d := by module
    have htrans : normalEval n₀ ((b + H • d) - (b + L • d)) ≠ 0 := by
      rw [hdiff, ← normalCLM_apply, map_smul, smul_eq_mul, normalCLM_apply]
      exact mul_ne_zero (ne_of_gt (sub_pos.mpr hLH)) hzero
    obtain ⟨q, hq, r, hr, hfree⟩ :=
      htransverse φ hφt (b + L • d) (b + H • d) htrans
    rw [openSegment_eq_image_lineMap] at hq
    obtain ⟨t, ht, htq⟩ := hq
    let u : ℝ := L + t * (H - L)
    have hu : u ∈ Ioo L H := by
      dsimp only [u]
      constructor <;> nlinarith [ht.1, ht.2]
    have hqcoord : q = b + u • d := by
      rw [← htq]
      dsimp only [u]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      module
    refine ⟨u, hu, r, hr, ?_⟩
    simpa only [hqcoord] using hfree



private theorem packingSol_realCarrier_finiteAvoidanceWindow
    (a d : Plane) (hd : d ≠ 0) (W : Set ℝ) (hW : IsOpen W) (hne : W.Nonempty)
    (V : Set Plane) (hV : V.Finite) :
    ∃ L H : ℝ, L < H ∧ ∀ u ∈ Ioo L H, u ∈ W ∧ a + u • d ∉ V := by
  let f : ℝ → Plane := fun u => a + u • d
  have hf : Function.Injective f := fun u v h =>
    smul_left_injective ℝ hd (add_left_cancel h)
  have hbad : (f ⁻¹' V).Finite := hV.preimage hf.injOn
  obtain ⟨l, h, hlh, hsub⟩ := hW.exists_Ioo_subset hne
  obtain ⟨u, hu, hnot⟩ := (Ioo_infinite hlh).exists_notMem_finite hbad
  let G := W ∩ f ⁻¹' Vᶜ
  have hG : IsOpen G := hW.inter (hV.isClosed.isOpen_compl.preimage (by fun_prop))
  have huG : u ∈ G := ⟨hsub hu, hnot⟩
  obtain ⟨L, H, hLH, hwindow⟩ := hG.exists_Ioo_subset ⟨u, huG⟩
  exact ⟨L, H, hLH, fun v hv => hwindow hv⟩

/-- A moved point on the SAME real carrier inherits the actual inward frame
and both full-support and union germs by shrinking geometric balls only. -/
private theorem packingSol_negativeFrame_recenter
    (O S U : Set Plane) (p₀ p d : Plane) (R : ℝ) (hR : 0 < R)
    (hp : p ∈ Metric.ball p₀ R)
    (hside : ∀ z, Tiling.signedSide p₀ d z = Tiling.signedSide p d z)
    (hframe : Metric.ball p₀ R ∩ Tiling.negativeSide p₀ d ⊆ O)
    (hS : S ∩ Metric.ball p₀ R = Tiling.negativeHalfPlane p₀ d ∩ Metric.ball p₀ R)
    (hU : U ∩ Metric.ball p₀ R = Tiling.negativeHalfPlane p₀ d ∩ Metric.ball p₀ R) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ Metric.ball p r ⊆ Metric.ball p₀ R ∧
      (Metric.ball p r ∩ Tiling.negativeSide p d ⊆ O) ∧
      S ∩ Metric.ball p r = Tiling.negativeHalfPlane p d ∩ Metric.ball p r ∧
      U ∩ Metric.ball p r = Tiling.negativeHalfPlane p d ∩ Metric.ball p r := by
  let r := (R - dist p p₀) / 2
  have hr : 0 < r := by dsimp [r]; linarith [Metric.mem_ball.mp hp]
  have hrR : r ≤ R := by dsimp [r]; linarith [show 0 ≤ dist p p₀ from dist_nonneg]
  have hballs : Metric.ball p r ⊆ Metric.ball p₀ R := by
    intro z hz
    have htri := dist_triangle z p p₀
    have hzdist := Metric.mem_ball.mp hz
    apply Metric.mem_ball.mpr
    dsimp [r] at hzdist
    linarith [Metric.mem_ball.mp hp]
  have hframe' : Metric.ball p r ∩ Tiling.negativeSide p d ⊆ O := by
    intro z hz
    apply hframe ⟨hballs hz.1, ?_⟩
    exact Tiling.mem_negativeSide.mpr ((hside z).symm ▸ Tiling.mem_negativeSide.mp hz.2)
  have strip (A : Set Plane)
      (hA : A ∩ Metric.ball p₀ R = Tiling.negativeHalfPlane p₀ d ∩ Metric.ball p₀ R) :
      A ∩ Metric.ball p r = Tiling.negativeHalfPlane p d ∩ Metric.ball p r := by
    ext z
    constructor
    · intro hz
      have hneg := Tiling.mem_negativeHalfPlane.mp
        (((Set.ext_iff.mp hA z).mp ⟨hz.1, hballs hz.2⟩).1)
      exact ⟨Tiling.mem_negativeHalfPlane.mpr (hside z ▸ hneg), hz.2⟩
    · intro hz
      have hneg := Tiling.mem_negativeHalfPlane.mp hz.1
      have hzA := ((Set.ext_iff.mp hA z).mpr
        ⟨Tiling.mem_negativeHalfPlane.mpr ((hside z).symm ▸ hneg), hballs hz.2⟩).1
      exact ⟨hzA, hz.2⟩
  exact ⟨r, hr, hrR, hballs, hframe', strip S hS, strip U hU⟩


private theorem packingSol_uniformActualPairedSourcePatch
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) (n : RationalNormal) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ a : Plane, ∀ r : ℝ, ∀ c ∈ T, ∀ eC ∈ E,
      ∀ qC ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) r false,
      ((c + eC.1 = a + qC.1 • packingSol_rationalTangent n ∧
        c + eC.2 = a + qC.2 • packingSol_rationalTangent n) ∨
       (c + eC.2 = a + qC.1 • packingSol_rationalTangent n ∧
        c + eC.1 = a + qC.2 • packingSol_rationalTangent n)) →
      (∀ u ∈ Ioo qC.1 qC.2, negativeEdgeGerm (c +ᵥ K.support)
        (packingSol_rationalTangent n) (a + u • packingSol_rationalTangent n)) →
      ∀ x ∈ deformPoint φ c +ᵥ Kφ.openCarrier,
      (∀ s ∈ T, s ≠ c → Disjoint
        (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x)
        (deformPoint φ s +ᵥ Kφ.openCarrier)) →
      ∀ u₀ ∈ Ioo (φ qC.1 : ℝ) (φ qC.2 : ℝ),
      deformPoint φ a + u₀ • packingSol_rationalTangent n ∈
        frontier (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x) →
      ((deformPoint φ c +ᵥ Kφ.support) =ᶠ[𝓝 (deformPoint φ a + u₀ • packingSol_rationalTangent n)]
        PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ)) →
      ∃ R : ℝ, 0 < R ∧
        (Metric.ball (deformPoint φ a + u₀ • packingSol_rationalTangent n) R ∩
          Tiling.negativeSide (deformPoint φ a + u₀ • packingSol_rationalTangent n)
            (packingSol_rationalTangent n) ⊆
          connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x) ∧
        (deformPoint φ c +ᵥ Kφ.support) ∩
            Metric.ball (deformPoint φ a + u₀ • packingSol_rationalTangent n) R =
          Tiling.negativeHalfPlane (deformPoint φ a + u₀ • packingSol_rationalTangent n)
            (packingSol_rationalTangent n) ∩
            Metric.ball (deformPoint φ a + u₀ • packingSol_rationalTangent n) R ∧
        PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ) ∩
            Metric.ball (deformPoint φ a + u₀ • packingSol_rationalTangent n) R =
          Tiling.negativeHalfPlane (deformPoint φ a + u₀ • packingSol_rationalTangent n)
            (packingSol_rationalTangent n) ∩
            Metric.ball (deformPoint φ a + u₀ • packingSol_rationalTangent n) R ∧
        ∃ b ∈ T, b ≠ c ∧ ∃ eB ∈ E,
        ∃ qB ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) r true,
        ((b + eB.1 = a + qB.1 • packingSol_rationalTangent n ∧
          b + eB.2 = a + qB.2 • packingSol_rationalTangent n) ∨
         (b + eB.2 = a + qB.1 • packingSol_rationalTangent n ∧
          b + eB.1 = a + qB.2 • packingSol_rationalTangent n)) ∧
        (∀ u ∈ Ioo qB.1 qB.2, positiveEdgeGerm (b +ᵥ K.support)
          (packingSol_rationalTangent n) (a + u • packingSol_rationalTangent n)) ∧
        ∃ L H : ℝ, L < H ∧
          Ioo L H ⊆ Ioo (φ qC.1 : ℝ) (φ qC.2 : ℝ) ∧
          Ioo L H ⊆ Ioo (φ qB.1 : ℝ) (φ qB.2 : ℝ) ∧
          (∀ u ∈ Ioo L H, deformPoint φ a + u • packingSol_rationalTangent n ∈
            Metric.ball (deformPoint φ a + u₀ • packingSol_rationalTangent n) R) ∧
          ∀ u ∈ Ioo L H, deformPoint φ a + u • packingSol_rationalTangent n ∉
            deformPoint φ '' Tiling.RationalSlopes.translatedVertices K T := by
  classical
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨Fg, εg, hεg, hgerms⟩ :=
    packingSol_signedOccurrence_targetGerms K P hP E hrat hprimitive hcover
  obtain ⟨Fp, εp, hεp, hpartner⟩ :=
    packingSol_actualSameJ_oppositeOccurrence K P T hP htile E hE hrat hcover n
  obtain ⟨Fv, εv, hεv, hvertices⟩ :=
    vertexExclusionSol_uniform_patch_avoids_all_oldVertices K P T hP htile E hE hrat hcover n
  let F := Fg ∪ Fp ∪ Fv
  let ε := min εg (min εp εv)
  refine ⟨F, ε, lt_min hεg (lt_min hεp hεv), ?_⟩
  intro φ hφ Kφ hKφ a r c hc eC heC qC hqC hcoordsC hsourceC x hx hsingle u₀ hu₀ hp hlocal
  have approx (A : Finset ℝ) (δ : ℝ) (hA : A ⊆ F) (hδ : ε ≤ δ) :
      IsFiniteApproximation A δ φ := finiteApproximation_strengthen A F δ ε φ hA hδ hφ
  have hφg : IsFiniteApproximation Fg εg φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto) (min_le_left _ _)
  have hφp : IsFiniteApproximation Fp εp φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans (min_le_left _ _))
  have hφv : IsFiniteApproximation Fv εv φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans (min_le_right _ _))
  let p := deformPoint φ a + u₀ • d
  let S := deformPoint φ c +ᵥ Kφ.support
  let U := PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ)
  have hgerm : negativeEdgeGerm S d p := hgerms φ hφg Kφ hKφ n a c eC heC qC
    hqC.1.1 hcoordsC (hE eC heC).2.2.2.2.2 false hsourceC u₀ hu₀
  obtain ⟨Rf, hRf, hframe, _⟩ := packingSol_actualComponent_negativeBoundaryFrame
    Kφ (deformPoint φ c) x p d hx hd hp hgerm
  obtain ⟨Rs, hRs, hstripS⟩ := hgerm
  obtain ⟨Re, hRe, hEq⟩ := Metric.eventually_nhds_iff.mp hlocal
  let R := min Rf (min Rs Re)
  have hR : 0 < R := lt_min hRf (lt_min hRs hRe)
  have hRRf : R ≤ Rf := min_le_left _ _
  have hRRs : R ≤ Rs := (min_le_right _ _).trans (min_le_left _ _)
  have hRRe : R ≤ Re := (min_le_right _ _).trans (min_le_right _ _)
  have hframe' : Metric.ball p R ∩ Tiling.negativeSide p d ⊆
      connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x :=
    fun z hz => hframe ⟨Metric.ball_subset_ball hRRf hz.1, hz.2⟩
  have hstripS' := packingSol_strip_shrink S (Tiling.negativeHalfPlane p d) p Rs R hRRs hstripS
  have hSU : S ∩ Metric.ball p R = U ∩ Metric.ball p R := by
    ext z
    have hpoint (hz : z ∈ Metric.ball p R) : (z ∈ S) = (z ∈ U) :=
      hEq ((Metric.mem_ball.mp hz).trans_le hRRe)
    constructor
    · intro hz
      exact ⟨Eq.mp (hpoint hz.2) hz.1, hz.2⟩
    · intro hz
      exact ⟨Eq.mpr (hpoint hz.2) hz.1, hz.2⟩
  have hstripU := hSU.symm.trans hstripS'
  let W := Ioo (φ qC.1 : ℝ) (φ qC.2 : ℝ) ∩
    ((fun u : ℝ => deformPoint φ a + u • d) ⁻¹' Metric.ball p R)
  have hW : IsOpen W := isOpen_Ioo.inter (Metric.isOpen_ball.preimage (by fun_prop))
  have huW : u₀ ∈ W := ⟨hu₀, Metric.mem_ball_self hR⟩
  obtain ⟨lo, hi, hlohi, hwindow⟩ := hW.exists_Ioo_subset ⟨u₀, huW⟩
  have hrSource : a + r • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support := by
    have hr' : r ∈ {u : ℝ | a + u • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} :=
      connectedComponentIn_nonempty_iff.mp ⟨qC.1, hqC.2 ⟨le_rfl, hqC.1.1.le⟩⟩
    exact hr'
  obtain ⟨b, hb, hbc, eB, heB, qB, hqB, hcoordsB, hsourceB, hoverlap⟩ :=
    hpartner φ hφp Kφ hKφ a r qC.1 qC.2 hrSource hqC.1.1 hqC.2 false qC hqC
      c hc eC heC hcoordsC hsourceC lo hi hlohi (fun u hu => (hwindow hu).1)
  obtain ⟨v, hv, hvB⟩ := hoverlap
  let W' := W ∩ Ioo (φ qB.1 : ℝ) (φ qB.2 : ℝ)
  have hW' : IsOpen W' := hW.inter isOpen_Ioo
  have hvW' : v ∈ W' := ⟨hwindow hv, hvB⟩
  let V := ((fun w : Plane => deformPoint φ c + deformPoint φ w) '' Tiling.vertexSet K.support) ∪
    ((fun w : Plane => deformPoint φ b + deformPoint φ w) '' Tiling.vertexSet K.support)
  have hV : V.Finite := (K.isPolygonal.vertexSet_finite.image _).union
    (K.isPolygonal.vertexSet_finite.image _)
  obtain ⟨L, H, hLH, hcommon⟩ := packingSol_realCarrier_finiteAvoidanceWindow
    (deformPoint φ a) d hd W' hW' ⟨v, hvW'⟩ V hV
  have hsubC : Ioo L H ⊆ Ioo (φ qC.1 : ℝ) (φ qC.2 : ℝ) :=
    fun u hu => (hcommon u hu).1.1.1
  have hsubB : Ioo L H ⊆ Ioo (φ qB.1 : ℝ) (φ qB.2 : ℝ) :=
    fun u hu => (hcommon u hu).1.2
  have hball : ∀ u ∈ Ioo L H, deformPoint φ a + u • d ∈ Metric.ball p R :=
    fun u hu => (hcommon u hu).1.1.2
  have hnotC : ∀ u ∈ Ioo L H, deformPoint φ a + u • d ∉
      deformPoint φ c +ᵥ (deformPoint φ '' Tiling.vertexSet K.support) := by
    intro u hu hbad
    obtain ⟨w, hw, hwu⟩ := Set.mem_vadd_set.mp hbad
    obtain ⟨z, hz, rfl⟩ := hw
    exact (hcommon u hu).2 (Or.inl ⟨z, hz, by simpa only [vadd_eq_add] using hwu⟩)
  have hnotB : ∀ u ∈ Ioo L H, deformPoint φ a + u • d ∉
      deformPoint φ b +ᵥ (deformPoint φ '' Tiling.vertexSet K.support) := by
    intro u hu hbad
    obtain ⟨w, hw, hwu⟩ := Set.mem_vadd_set.mp hbad
    obtain ⟨z, hz, rfl⟩ := hw
    exact (hcommon u hu).2 (Or.inr ⟨z, hz, by simpa only [vadd_eq_add] using hwu⟩)
  have hall := hvertices φ hφv Kφ hKφ a r c hc b hb hbc.symm eC heC eB heB qC hqC qB hqB
    hcoordsC hcoordsB hsourceC hsourceB x hx hsingle u₀ R hR hframe' L H hLH
    hsubC hsubB hball hnotC hnotB
  exact ⟨R, hR, hframe', hstripS', hstripU, b, hb, hbc, eB, heB, qB, hqB,
    hcoordsB, hsourceB, L, H, hLH, hsubC, hsubB, hball, hall⟩


private theorem packingSol_occurrence_midpoint
    (t : Plane) (e : Plane × Plane) (a d : Plane) (q : ℝ × ℝ)
    (hcoords : (t + e.1 = a + q.1 • d ∧ t + e.2 = a + q.2 • d) ∨
      (t + e.2 = a + q.1 • d ∧ t + e.1 = a + q.2 • d)) :
    t + AffineMap.lineMap e.1 e.2 (1 / 2 : ℝ) =
      a + ((q.1 + q.2) / 2) • d := by
  have hmid : t + AffineMap.lineMap e.1 e.2 (1 / 2 : ℝ) =
      (1 / 2 : ℝ) • (t + e.1) + (1 / 2 : ℝ) • (t + e.2) := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [hmid]
  rcases hcoords with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [hl, hr]
    module
  · rw [hl, hr]
    module

/-- Opposite choices from the FIXED finite SOURCE normal family select a
genuinely negative OLD occurrence; no target or approximation premise occurs. -/
private theorem packingSol_finiteNormal_negativeSourceOccurrence
    (K : PolygonalRegion) (T : Set Plane) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (N : Finset RationalNormal) (n : RationalNormal) (hn : n ∈ N)
    (hnOpp : packingSol_oppositeNormal n ∈ N)
    (t : Plane) (ht : t ∈ T) (e : Plane × Plane) (he : e ∈ E)
    (hparallel : normalEval n (e.2 - e.1) = 0) :
    ∃ m ∈ N, normalEval m (e.2 - e.1) = 0 ∧
      ∃ (a : Plane) (q : ℝ × ℝ),
        q ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent m) 0 false ∧
        ((t + e.1 = a + q.1 • packingSol_rationalTangent m ∧
          t + e.2 = a + q.2 • packingSol_rationalTangent m) ∨
         (t + e.2 = a + q.1 • packingSol_rationalTangent m ∧
          t + e.1 = a + q.2 • packingSol_rationalTangent m)) ∧
        ∀ u ∈ Ioo q.1 q.2, negativeEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent m)
          (a + u • packingSol_rationalTangent m) := by
  obtain ⟨a, q, positive, hq, hcoords, hsource⟩ :=
    packingSol_rationalPrimitive_actualSourceOccurrence K T E hE n t ht e he hparallel
  cases positive with
  | false => exact ⟨n, hn, hparallel, a, q, hq, hcoords, hsource⟩
  | true =>
      have hparallelOpp : normalEval (packingSol_oppositeNormal n) (e.2 - e.1) = 0 := by
        rw [packingSol_oppositeNormal_normalEval, hparallel, neg_zero]
      obtain ⟨b, q', opposite, hq', hcoords', hsource'⟩ :=
        packingSol_rationalPrimitive_actualSourceOccurrence K T E hE
          (packingSol_oppositeNormal n) t ht e he hparallelOpp
      cases opposite with
      | false => exact ⟨packingSol_oppositeNormal n, hnOpp, hparallelOpp, b, q',
          hq', hcoords', hsource'⟩
      | true =>
          let p := t + AffineMap.lineMap e.1 e.2 (1 / 2 : ℝ)
          have hu : (q.1 + q.2) / 2 ∈ Ioo q.1 q.2 := by
            constructor <;> linarith [hq.1.1]
          have hu' : (q'.1 + q'.2) / 2 ∈ Ioo q'.1 q'.2 := by
            constructor <;> linarith [hq'.1.1]
          have hgerm : positiveEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n) p := by
            change positiveEdgeGerm (t +ᵥ K.support) (packingSol_rationalTangent n)
              (t + AffineMap.lineMap e.1 e.2 (1 / 2 : ℝ))
            rw [packingSol_occurrence_midpoint t e a (packingSol_rationalTangent n) q hcoords]
            exact hsource _ hu
          have hgerm' : positiveEdgeGerm (t +ᵥ K.support)
              (-packingSol_rationalTangent n) p := by
            rw [← packingSol_oppositeNormal_rationalTangent]
            change positiveEdgeGerm (t +ᵥ K.support)
              (packingSol_rationalTangent (packingSol_oppositeNormal n))
              (t + AffineMap.lineMap e.1 e.2 (1 / 2 : ℝ))
            rw [packingSol_occurrence_midpoint t e b (packingSol_rationalTangent (packingSol_oppositeNormal n))
                q' hcoords']
            exact hsource' _ hu'
          exact False.elim (positive_negative_edgeGerms_disjoint
            (packingSol_rationalTangent_ne_zero n) hgerm
            ((orientedEdgeGerms_negativeDirection (t +ᵥ K.support) p
              (packingSol_rationalTangent n)).1.mp hgerm'))


private theorem packingSol_uniformActualNegativeMappedOccurrence
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane)
    (hP : polyhedralSupport P = K.support)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (E : Finset (Plane × Plane))
    (hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)))
    (hrat : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hcover : frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2) :
    ∃ N : Finset RationalNormal, ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ c ∈ T, ∀ p ∈ frontier (deformPoint φ c +ᵥ Kφ.support),
      p ∉ deformPoint φ c +ᵥ (deformPoint φ '' Tiling.vertexSet K.support) →
      ∃ n ∈ N, ∃ e ∈ E, ∃ (a : Plane) (q : ℝ × ℝ),
        q ∈ signedCarrierComponentIntervals K T E a (packingSol_rationalTangent n) 0 false ∧
        ((c + e.1 = a + q.1 • packingSol_rationalTangent n ∧
          c + e.2 = a + q.2 • packingSol_rationalTangent n) ∨
         (c + e.2 = a + q.1 • packingSol_rationalTangent n ∧
          c + e.1 = a + q.2 • packingSol_rationalTangent n)) ∧
        (∀ u ∈ Ioo q.1 q.2, negativeEdgeGerm (c +ᵥ K.support)
          (packingSol_rationalTangent n) (a + u • packingSol_rationalTangent n)) ∧
        (φ q.1 : ℝ) < (φ q.2 : ℝ) ∧
        ∃ u ∈ Ioo (φ q.1 : ℝ) (φ q.2 : ℝ),
          p = deformPoint φ a + u • packingSol_rationalTangent n ∧
          negativeEdgeGerm (deformPoint φ c +ᵥ Kφ.support) (packingSol_rationalTangent n) p := by
  classical
  obtain ⟨N, hN⟩ := packingSol_finiteSourceNormals E hrat
  choose Fq εq hεq hquery using
    (fun n : RationalNormal => packingSol_uniformActualMappedPrimitiveQuery
      K P T hP htile E hE hrat hcover n)
  obtain ⟨Fn, εn, hεn, hnormal⟩ := packingSol_finiteNormal_controls N
    (fun n φ => IsFiniteApproximation (Fq n) (εq n) φ)
    (fun n _ => ⟨Fq n, εq n, hεq n, fun _ h => h⟩)
  have hprimitive : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support :=
    fun e he => ⟨(hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
      (hE e he).2.2.2.1, (hE e he).2.2.2.2.1⟩
  obtain ⟨Fs, εs, _, hεs, _, htransport⟩ :=
    rationalPrimitiveEdges_uniformSameSide_transport K P hP E hrat hprimitive hcover
  refine ⟨N, Fn ∪ Fs, min εn εs, lt_min hεn hεs, ?_⟩
  intro φ hφ Kφ hKφ c hc p hpfront hpnot
  have hφn : IsFiniteApproximation Fn εn φ := finiteApproximation_strengthen _ _ _ _ φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφs : IsFiniteApproximation Fs εs φ := finiteApproximation_strengthen _ _ _ _ φ
    Finset.subset_union_right (min_le_right _ _) hφ
  obtain ⟨_, _, _, _, hfront, _⟩ := htransport φ hφs Kφ hKφ
  have hfrontier : frontier (deformPoint φ c +ᵥ Kφ.support) =
      ⋃ e ∈ E, segment ℝ (deformPoint φ c + deformPoint φ e.1)
        (deformPoint φ c + deformPoint φ e.2) := by
    rw [← sourceRay_link_frontier_vadd, hfront, Set.vadd_set_iUnion]
    simp only [Set.vadd_set_iUnion, vadd_segment, vadd_eq_add]
  obtain ⟨e, he, hpseg⟩ : ∃ e ∈ E, p ∈ segment ℝ
      (deformPoint φ c + deformPoint φ e.1) (deformPoint φ c + deformPoint φ e.2) := by
    rw [hfrontier] at hpfront
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hpfront
    obtain ⟨heE, hpseg⟩ := Set.mem_iUnion.mp he
    exact ⟨e, heE, hpseg⟩
  have endpointNot (v : Plane) (hv : v ∈ Tiling.vertexSet K.support) :
      deformPoint φ c + deformPoint φ v ≠ p := by
    intro heq
    apply hpnot
    exact Set.mem_vadd_set.mpr ⟨deformPoint φ v, ⟨v, hv, rfl⟩, by
      simpa only [vadd_eq_add] using heq⟩
  have hpopen := mem_openSegment_of_ne_left_right
    (endpointNot e.1 (hE e he).2.1) (endpointNot e.2 (hE e he).2.2.1) hpseg
  obtain ⟨n, hn, hnOpp, hndir⟩ := hN e he
  have hparallel : normalEval n (e.2 - e.1) = 0 := by
    apply (normalDirection_mem_iff n _).mp
    rw [hndir]
    exact Submodule.mem_span_singleton_self _
  have hsimple : ∀ e ∈ E, e.1 ≠ e.2 ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)) :=
    fun e he => ⟨(hE e he).1, (hE e he).2.2.2.1, (hE e he).2.2.2.2.2⟩
  obtain ⟨m, hm, hmparallel, a₀, q₀, hq₀, hcoords₀, hnegative₀⟩ :=
    packingSol_finiteNormal_negativeSourceOccurrence K T E hsimple N n hn hnOpp
      c hc e he hparallel
  obtain ⟨a, q, positive, hq, hcoords, hsource, horder, hparameters, htarget⟩ :=
    hquery m φ (hnormal φ hφn m hm) Kφ hKφ c hc e he hmparallel
  have hfalse : positive = false := by
    cases positive with
    | false => rfl
    | true =>
        have hu : (q.1 + q.2) / 2 ∈ Ioo q.1 q.2 := by
          constructor <;> linarith [hq.1.1]
        have hu₀ : (q₀.1 + q₀.2) / 2 ∈ Ioo q₀.1 q₀.2 := by
          constructor <;> linarith [hq₀.1.1]
        have hpos := hsource _ hu
        have hneg := hnegative₀ _ hu₀
        rw [← packingSol_occurrence_midpoint c e a (packingSol_rationalTangent m) q hcoords] at hpos
        rw [← packingSol_occurrence_midpoint c e a₀ (packingSol_rationalTangent m) q₀ hcoords₀] at hneg
        exact False.elim (positive_negative_edgeGerms_disjoint
          (packingSol_rationalTangent_ne_zero m) hpos hneg)
  subst positive
  obtain ⟨u, hu, hpu⟩ := hparameters p hpopen
  exact ⟨m, hm, e, he, a, q, hq, hcoords, hsource, horder, u, hu, hpu,
    hpu.symm ▸ htarget u hu⟩



private theorem packingSol_oneLink_denseSingle
    (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane) (n₀ : RationalNormal)
    (hP : polyhedralSupport P = K.support)
    (hrat : Tiling.RationalSlopes.HasRationalSlopes K)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (a₀ : Plane) (hproper : Tiling.RationalSlopes.IsProperLink K (normalDirection n₀) T a₀) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
        Dense (packingSol_singleOpenUnion Kφ T φ) := by
  classical
  obtain ⟨E, hEraw, hcover, _⟩ := rationalIntrinsicPrimitiveEdges K hrat
  have hE : ∀ e ∈ E, e.1 ≠ e.2 ∧ e.1 ∈ Tiling.vertexSet K.support ∧
      e.2 ∈ Tiling.vertexSet K.support ∧ segment ℝ e.1 e.2 ⊆ frontier K.support ∧
      (∀ z ∈ openSegment ℝ e.1 e.2, z ∉ Tiling.vertexSet K.support) ∧
      ((∀ z ∈ openSegment ℝ e.1 e.2, positiveEdgeGerm K.support (e.2 - e.1) z) ∨
        (∀ z ∈ openSegment ℝ e.1 e.2, negativeEdgeGerm K.support (e.2 - e.1) z)) :=
    fun e he => ⟨(hEraw e he).1, (hEraw e he).2.1, (hEraw e he).2.2.1,
      (hEraw e he).2.2.2.1, (hEraw e he).2.2.2.2.1, (hEraw e he).2.2.2.2.2.2⟩
  have hratE : ∀ e ∈ E, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1) :=
    fun e he => (hEraw e he).2.2.2.2.2.1
  obtain ⟨N, Fo, εo, hεo, hnegative⟩ :=
    packingSol_uniformActualNegativeMappedOccurrence K P T hP htile E hE hratE hcover
  choose Fp εp hεp hpaired using
    (fun n : RationalNormal => packingSol_uniformActualPairedSourcePatch
      K P T hP htile E hE hratE hcover n)
  choose Fx εx hεx hexclusive using
    (fun n : RationalNormal => packingSol_uniformActualLocalExclusiveClosedWitness
      K P T hP htile E hE hratE hcover n)
  obtain ⟨Fn, εn, hεn, hnormal⟩ := packingSol_finiteNormal_controls N
    (fun n φ => IsFiniteApproximation (Fp n) (εp n) φ ∧ IsFiniteApproximation (Fx n) (εx n) φ)
    (by
      intro n hn
      refine ⟨Fp n ∪ Fx n, min (εp n) (εx n), lt_min (hεp n) (hεx n), ?_⟩
      intro φ hφ
      exact ⟨finiteApproximation_strengthen _ _ _ _ φ Finset.subset_union_left
        (min_le_left _ _) hφ, finiteApproximation_strengthen _ _ _ _ φ
        Finset.subset_union_right (min_le_right _ _) hφ⟩)
  obtain ⟨Fa, εa, hεa, hanchor⟩ :=
    packingSol_selectedProperLine_actualSingleComponent K P T n₀ hP hrat htile a₀ hproper
  obtain ⟨Fs, εs, hεs, hsingleWitness⟩ :=
    packingSol_exclusiveClosedWitness_singleComponent K P T hP hrat htile
  obtain ⟨Fv, εv, hεv, hvertexBall⟩ :=
    packingSol_uniformRealInterval_vertexFreeBall K T n₀ hrat htile a₀ hproper
  let F := Fa ∪ (Fo ∪ (Fn ∪ (Fs ∪ Fv)))
  let ε := min εa (min εo (min εn (min εs εv)))
  refine ⟨F, ε, lt_min hεa (lt_min hεo (lt_min hεn (lt_min hεs hεv))), ?_⟩
  intro φ hφ Kφ hKφ
  have approx (A : Finset ℝ) (δ : ℝ) (hA : A ⊆ F) (hδ : ε ≤ δ) :
      IsFiniteApproximation A δ φ := finiteApproximation_strengthen A F δ ε φ hA hδ hφ
  have hφa : IsFiniteApproximation Fa εa φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto) (min_le_left _ _)
  have hφo : IsFiniteApproximation Fo εo φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans (min_le_left _ _))
  have hφn : IsFiniteApproximation Fn εn φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hφs : IsFiniteApproximation Fs εs φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hφv : IsFiniteApproximation Fv εv φ := approx _ _
    (by intro z hz; simp only [F, Finset.mem_union]; tauto)
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨t, ht, x₀, hx₀, _, hsingle₀⟩ := hanchor φ hφa Kφ hKφ
  by_contra hnotDense
  obtain ⟨i, p, hpUnion, hpComponent, hpFull, hpNot, hstraight⟩ :=
    packingSol_notDense_actualSingleBoundary Kφ T φ t ht x₀ hx₀ hsingle₀ hnotDense
  let c : Plane := i.1.1
  have hc : c ∈ T := i.1.1.2
  obtain ⟨x, hx, hpActual, hsingle⟩ :=
    packingSol_singleIndex_actualBoundaryComponent Kφ T (deformPoint φ) i p hpComponent
  let V := (fun v : Plane => deformPoint φ c + deformPoint φ v) '' Tiling.vertexSet K.support
  have hV : V.Finite := K.isPolygonal.vertexSet_finite.image _
  obtain ⟨q, hqComponent, hqUnion, hqFull, hqNot, hqEq⟩ :=
    packingSol_actualSingleBoundary_genericPoint Kφ T φ c hc x hx hsingle p hpUnion
      hpActual hpFull hpNot hstraight V hV
  have hqNotOld : q ∉ deformPoint φ c +ᵥ (deformPoint φ '' Tiling.vertexSet K.support) := by
    intro hbad
    obtain ⟨v, hv, hvq⟩ := Set.mem_vadd_set.mp hbad
    obtain ⟨w, hw, rfl⟩ := hv
    exact hqNot ⟨w, hw, by simpa only [vadd_eq_add] using hvq⟩
  obtain ⟨n, hn, eC, heC, a, qC, hqC, hcoordsC, hsourceC, _, u₀, hu₀, hpoint, _⟩ :=
    hnegative φ hφo Kφ hKφ c hc q hqFull hqNotOld
  let d := packingSol_rationalTangent n
  have hd : d ≠ 0 := packingSol_rationalTangent_ne_zero n
  rw [hpoint] at hqComponent hqEq
  obtain ⟨hφp, hφx⟩ := hnormal φ hφn n hn
  obtain ⟨R, hR, hframe, hown, hunion, b, hb, _, eB, heB, qB, hqB,
      hcoordsB, hsourceB, L, H, hLH, hsubC, hsubB, hball, hpatch⟩ :=
    hpaired n φ hφp Kφ hKφ a 0 c hc eC heC qC hqC hcoordsC hsourceC x hx
      hsingle u₀ hu₀ hqComponent hqEq
  obtain ⟨z, hz, Rv, hRv, hfree⟩ :=
    hvertexBall φ hφv (deformPoint φ a) d hd L H hLH hpatch
  obtain ⟨r, hr, _, _, hframe', hown', hunion'⟩ :=
    packingSol_negativeFrame_recenter
      (connectedComponentIn (deformPoint φ c +ᵥ Kφ.openCarrier) x)
      (deformPoint φ c +ᵥ Kφ.support)
      (PackingSolSingleFamily.singleClosedUnion Kφ T (deformPoint φ))
      (deformPoint φ a + u₀ • d) (deformPoint φ a + z • d) d R hR (hball z hz)
      (vertexExclusionSol_sameCarrier_side (deformPoint φ a) d u₀ z)
      hframe hown hunion
  obtain ⟨y, hy, hyball, hypositive, hyexclusive⟩ :=
    hexclusive n φ hφx Kφ hKφ a 0 c hc b hb eC heC eB heB qC hqC qB hqB
      hcoordsC hcoordsB hsourceB x hx hsingle z r hr hframe' hown'
      (hsubC hz) (hsubB hz) Rv hRv hfree
  have hsingleB := hsingleWitness φ hφs Kφ hKφ b hb y hy hyexclusive
  exact packingSol_singleComponent_point_contradicts_unionNegative Kφ T φ b hb y hy
    hsingleB (deformPoint φ a + z • d) d r hyball hypositive hunion'


theorem oneLink_labelledPacking :
  ∀ (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane) (n : RationalNormal),
    polyhedralSupport P = K.support → Tiling.RationalSlopes.HasRationalSlopes K →
    Tiling.Polygonal.TilesOn K T Set.univ →
    Tiling.RationalSlopes.HasProperLink K (normalDirection n) T →
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
            ∀ s ∈ T, ∀ t ∈ T, s ≠ t →
              Disjoint (deformPoint φ s +ᵥ Kφ.openCarrier)
                (deformPoint φ t +ᵥ Kφ.openCarrier) := by
  intro K P T n hP hrat htile hproper
  obtain ⟨a, ha⟩ := hproper
  obtain ⟨F, ε, hε, hdense⟩ := packingSol_oneLink_denseSingle K P T n hP hrat htile a ha
  exact ⟨F, ε, hε, fun φ hφ Kφ hKφ =>
    packingSol_denseSingle_forces_labelledDisjoint Kφ T φ (hdense φ hφ Kφ hKφ)⟩

theorem oneLink_indexedLocalFiniteness :
  ∀ (K : PolygonalRegion) (T : Set Plane) (δ : Submodule ℝ Plane),
    Module.finrank ℝ δ = 1 → Tiling.RationalSlopes.HasRationalDirection δ →
    Tiling.RationalSlopes.HasRationalSlopes K → Tiling.Polygonal.TilesOn K T Set.univ →
    Tiling.RationalSlopes.HasProperLink K δ T →
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ Q : Set Plane, Bornology.IsBounded Q →
            {t | t ∈ T ∧ deformPoint φ t ∈ Q}.Finite := by
  intro K T δ hdim hδ hrat htile hlink
  obtain ⟨n, hn⟩ := rationalDirection_hasNormal δ hdim hδ
  obtain ⟨P, hP, W, hW, hzero, F₀, ε₀, hε₀, hconstruct⟩ := rationalPolygon_construction K hrat
  obtain ⟨F₁, ε₁, hε₁, hpacking⟩ :=
    oneLink_labelledPacking K P T n hP hrat htile (by simpa only [hn] using hlink)
  refine ⟨F₀ ∪ F₁, min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro φ hφ
  have hφ₀ := finiteApproximation_strengthen F₀ (F₀ ∪ F₁) ε₀ (min ε₀ ε₁) φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφ₁ := finiteApproximation_strengthen F₁ (F₀ ∪ F₁) ε₁ (min ε₀ ε₁) φ
    Finset.subset_union_right (min_le_right _ _) hφ
  obtain ⟨Kφ, hKφ, _⟩ := hconstruct φ hφ₀
  exact labelledPacking_indexedLF Kφ T (deformPoint φ) (hpacking φ hφ₁ Kφ hKφ)

theorem oneLinkRationalDeformation :
  ∀ (K : PolygonalRegion) (T : Set Plane) (δ : Submodule ℝ Plane),
    Module.finrank ℝ δ = 1 → Tiling.RationalSlopes.HasRationalDirection δ →
    Tiling.RationalSlopes.HasRationalSlopes K → Tiling.Polygonal.TilesOn K T Set.univ →
    Tiling.RationalSlopes.HasProperLink K δ T →
      ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
        ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
          ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
            ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ ∧
              Tiling.IsRational Kφ.support ∧ Set.InjOn (deformPoint φ) T ∧
              Tiling.Polygonal.TilesOn Kφ (deformPoint φ '' T) Set.univ ∧
              (∀ S ⊆ T, Tiling.Polygonal.IsInvariantAlong (Tiling.Polygonal.regularSupport K S) δ →
                Tiling.Polygonal.IsInvariantAlong
                  (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) δ) ∧
              (∀ S ⊆ T, Tiling.Polygonal.IsCenterColumn K δ S →
                Tiling.Polygonal.IsCenterColumn Kφ δ (deformPoint φ '' S)) := by
  intro K T δ hdim hδ hrat htile hlink
  obtain ⟨n, hn⟩ := rationalDirection_hasNormal δ hdim hδ
  have hlinkn : Tiling.RationalSlopes.HasProperLink K (normalDirection n) T := by
    simpa only [hn] using hlink
  obtain ⟨P, hP, W, _, _, F₀, ε₀, hε₀, hconstruct⟩ := rationalPolygon_construction K hrat
  obtain ⟨F₁, ε₁, hε₁, hcover⟩ := deformation_closedCopies_coverPlane K P T hP hrat htile
  obtain ⟨F₂, ε₂, hε₂, hpack⟩ := oneLink_labelledPacking K P T n hP hrat htile hlinkn
  obtain ⟨F₃, ε₃, hε₃, hsat⟩ := saturatedSubfamily_forwardTransport K P T n hP hrat htile hlinkn
  refine ⟨P, hP, F₀ ∪ F₁ ∪ F₂ ∪ F₃, min ε₀ (min ε₁ (min ε₂ ε₃)),
    lt_min hε₀ (lt_min hε₁ (lt_min hε₂ hε₃)), ?_⟩
  intro φ hφ
  have hφ₀ : IsFiniteApproximation F₀ ε₀ φ := by
    apply finiteApproximation_strengthen F₀ (F₀ ∪ F₁ ∪ F₂ ∪ F₃) ε₀ _ φ _ (min_le_left _ _) hφ
    intro x hx; simp [hx]
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := by
    apply finiteApproximation_strengthen F₁ (F₀ ∪ F₁ ∪ F₂ ∪ F₃) ε₁ _ φ _
      ((min_le_right _ _).trans (min_le_left _ _)) hφ
    intro x hx; simp [hx]
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ := by
    apply finiteApproximation_strengthen F₂ (F₀ ∪ F₁ ∪ F₂ ∪ F₃) ε₂ _ φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) hφ
    intro x hx; simp [hx]
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ := by
    apply finiteApproximation_strengthen F₃ (F₀ ∪ F₁ ∪ F₂ ∪ F₃) ε₃ _ φ _
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) hφ
    intro x hx; simp [hx]
  obtain ⟨Kφ, hKφ, hKrational, _⟩ := hconstruct φ hφ₀
  have hpacking := hpack φ hφ₂ Kφ hKφ
  have hinj := labelledPacking_injOn Kφ T (deformPoint φ) hpacking
  have hp := labelledPacking_image_isPacking Kφ T (deformPoint φ) hpacking
  have hcoverφ : (⋃ t : deformPoint φ '' T, (t : Plane) +ᵥ Kφ.support) = Set.univ := by
    rw [closedCopies_image_eq]
    exact hcover φ hφ₁ Kφ hKφ
  have hfull : Tiling.Polygonal.TilesOn Kφ (deformPoint φ '' T) Set.univ := by
    have h := Tiling.Polygonal.tilesOn_regularSupport_of_packing hp
    change Tiling.Polygonal.TilesOn Kφ (deformPoint φ '' T)
      (interior (closure (Tiling.Polygonal.openUnion Kφ (deformPoint φ '' T)))) at h
    rw [Tiling.Polygonal.closure_openUnion_eq_iUnion_support hp, hcoverφ, interior_univ] at h
    exact h
  have hforward : ∀ S ⊆ T, Tiling.Polygonal.IsInvariantAlong (Tiling.Polygonal.regularSupport K S) δ →
      Tiling.Polygonal.IsInvariantAlong
        (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) δ := by
    simpa only [hn] using hsat φ hφ₃ Kφ hKφ hfull
  refine ⟨Kφ, hKφ, hKrational, hinj, hfull, hforward, ?_⟩
  intro S hST hcol
  refine ⟨labelledPacking_image_isPacking Kφ S (deformPoint φ)
    (fun s hs t ht => hpacking s (hST hs) t (hST ht)), hcol.2.1.image _, ?_, hforward S hST hcol.2.2.2⟩
  obtain ⟨a, ha⟩ := hcol.2.2.1
  refine ⟨deformPoint φ a, ?_⟩
  rintro w ⟨s, hs, rfl⟩
  rw [← hn]
  apply rationalDirection_preservesCoset φ n
  simpa only [hn] using ha s hs

private theorem invariant_regularSupport_iUnion (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    {ι : Type} (S : ι → Set Plane)
    (hinv : ∀ i, Tiling.Polygonal.IsInvariantAlong (Tiling.Polygonal.regularSupport K (S i)) δ) :
    Tiling.Polygonal.IsInvariantAlong (Tiling.Polygonal.regularSupport K (⋃ i, S i)) δ := by
  intro u hu
  rw [Tiling.Polygonal.regularSupport_iUnion]
  rw [← interior_vadd, ← closure_vadd]
  have hunion : u +ᵥ (⋃ i, Tiling.Polygonal.regularSupport K (S i)) =
      ⋃ i, u +ᵥ Tiling.Polygonal.regularSupport K (S i) := by
    ext x
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_iUnion]
  rw [hunion]
  congr 2
  apply Set.iUnion_congr
  intro i
  exact hinv i u hu

private theorem invariantSubfamily_iff_componentClosed (K : PolygonalRegion)
    (δ : Submodule ℝ Plane) (T S : Set Plane)
    (hdim : Module.finrank ℝ δ = 1) (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (hST : S ⊆ T) :
    Tiling.Polygonal.IsInvariantAlong (Tiling.Polygonal.regularSupport K S) δ ↔
      ∀ C : Tiling.RationalSlopes.EarthquakeComponent K δ T,
        Disjoint C.centres S ∨ C.centres ⊆ S := by
  have hfull : Tiling.Polygonal.IsInvariantAlong (Tiling.Polygonal.regularSupport K T) δ := by
    rw [Tiling.Polygonal.regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile]
    intro u hu
    simp
  constructor
  · intro hS
    exact Tiling.RationalSlopes.invariantSubfamily_isUnionComponents K δ T S
      hdim htile.2.1 hfull hST hS
  · intro hclosed
    let I := {C : Tiling.RationalSlopes.EarthquakeComponent K δ T // C.centres ⊆ S}
    have hS : S = ⋃ C : I, C.1.centres := by
      ext x
      constructor
      · intro hx
        let t : T := ⟨x, hST hx⟩
        let C : Tiling.RationalSlopes.EarthquakeComponent K δ T :=
          (Tiling.RationalSlopes.earthquakeGraph K δ T).connectedComponentMk t
        have hxC : x ∈ C.centres := ⟨t, rfl, rfl⟩
        have hCS : C.centres ⊆ S := by
          rcases hclosed C with hdisj | hsubset
          · exact (Set.disjoint_left.mp hdisj hxC hx).elim
          · exact hsubset
        exact Set.mem_iUnion.mpr ⟨⟨C, hCS⟩, hxC⟩
      · intro hx
        obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
        exact C.2 hxC
    rw [hS]
    apply invariant_regularSupport_iUnion
    intro C
    exact Tiling.RationalSlopes.component_isInvariant K δ T hdim htile.2.1 hfull C.1

private theorem earthquakeComponent_centres_transport
    (K Kφ : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (f : Plane → Plane) (hinj : Set.InjOn f T)
    (hadj : ∀ s ∈ T, ∀ t ∈ T,
      Tiling.RationalSlopes.DirectionalOverlap K δ s t ↔
        Tiling.RationalSlopes.DirectionalOverlap Kφ δ (f s) (f t)) :
    ∃ e : Tiling.RationalSlopes.EarthquakeComponent K δ T ≃
        Tiling.RationalSlopes.EarthquakeComponent Kφ δ (f '' T),
      ∀ C, (e C).centres = f '' C.centres := by
  classical
  let E : (T : Set Plane) ≃ (f '' T) := Equiv.Set.imageOfInjOn f T hinj
  let hgraph : Tiling.RationalSlopes.earthquakeGraph K δ T ≃g
      Tiling.RationalSlopes.earthquakeGraph Kφ δ (f '' T) := by
    refine ⟨E, ?_⟩
    intro s t
    change (E s ≠ E t ∧
        (Tiling.RationalSlopes.DirectionalOverlap Kφ δ (f s.1) (f t.1) ∨
          Tiling.RationalSlopes.DirectionalOverlap Kφ δ (f t.1) (f s.1))) ↔
      (s ≠ t ∧ (Tiling.RationalSlopes.DirectionalOverlap K δ s.1 t.1 ∨
        Tiling.RationalSlopes.DirectionalOverlap K δ t.1 s.1))
    rw [E.injective.ne_iff]
    exact and_congr Iff.rfl
      (or_congr (hadj s.1 s.2 t.1 t.2).symm (hadj t.1 t.2 s.1 s.2).symm)
  let e := hgraph.connectedComponentEquiv
  refine ⟨e, ?_⟩
  intro C
  change (Subtype.val '' (e C).supp) = f '' (Subtype.val '' C.supp)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    let y' : (e C).supp := ⟨y, hy⟩
    let x' : C.supp := (SimpleGraph.ConnectedComponent.isoEquivSupp hgraph C).symm y'
    have hval := congrArg (fun q : (e C).supp => (q.1.1 : Plane))
      ((SimpleGraph.ConnectedComponent.isoEquivSupp hgraph C).apply_symm_apply y')
    refine ⟨x'.1, ⟨x'.1, x'.2, rfl⟩, ?_⟩
    exact hval
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    let z' : C.supp := ⟨z, hz⟩
    let w' : (e C).supp := SimpleGraph.ConnectedComponent.isoEquivSupp hgraph C z'
    refine ⟨w'.1, w'.2, ?_⟩
    rfl

theorem transverseFLC_oneLinkComponentCorrespondence :
  ∀ (K : PolygonalRegion) (T : Set Plane) (δ : Submodule ℝ Plane),
    Module.finrank ℝ δ = 1 → Tiling.RationalSlopes.HasRationalDirection δ →
    Tiling.RationalSlopes.HasRationalSlopes K → Tiling.Polygonal.TilesOn K T Set.univ →
    Tiling.RationalSlopes.HasProperLink K δ T →
    Tiling.RationalSlopes.HasTransverseFLC K δ T →
      ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
        ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
          ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
            ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ ∧
              Set.InjOn (deformPoint φ) T ∧
              Tiling.Polygonal.TilesOn Kφ (deformPoint φ '' T) Set.univ ∧
              (∀ S ⊆ T,
                Tiling.Polygonal.IsInvariantAlong (Tiling.Polygonal.regularSupport K S) δ ↔
                  Tiling.Polygonal.IsInvariantAlong
                    (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) δ) ∧
              ∃ e : Tiling.RationalSlopes.EarthquakeComponent K δ T ≃
                Tiling.RationalSlopes.EarthquakeComponent Kφ δ (deformPoint φ '' T),
                ∀ C : Tiling.RationalSlopes.EarthquakeComponent K δ T,
                  (e C).centres = deformPoint φ '' C.centres ∧
                  (Tiling.Polygonal.IsCenterColumn K δ C.centres ↔
                    Tiling.Polygonal.IsCenterColumn Kφ δ (e C).centres) := by
  intro K T δ hdim hδ hrat htile hlink hflc
  obtain ⟨n, hn⟩ := rationalDirection_hasNormal δ hdim hδ
  obtain ⟨P, hP, F₀, ε₀, hε₀, hdeform⟩ :=
    oneLinkRationalDeformation K T δ hdim hδ hrat htile hlink
  have hflcn : Tiling.RationalSlopes.HasTransverseFLC K (normalDirection n) T := by
    simpa only [hn] using hflc
  obtain ⟨F₁, ε₁, hε₁, hoverlap⟩ :=
    transverseFLC_directionalOverlapReflection K P T n hP hrat htile hflcn
  obtain ⟨F₂, ε₂, hε₂, horder⟩ :=
    transverseFLC_globalOrderAndBoundedGapReflection K T n hrat htile hflcn 1 (by norm_num)
  refine ⟨P, hP, F₀ ∪ F₁ ∪ F₂, min ε₀ (min ε₁ ε₂),
    lt_min hε₀ (lt_min hε₁ hε₂), ?_⟩
  intro φ hφ
  have hφ₀ : IsFiniteApproximation F₀ ε₀ φ := by
    apply finiteApproximation_strengthen F₀ (F₀ ∪ F₁ ∪ F₂) ε₀ _ φ _ (min_le_left _ _) hφ
    intro x hx; simp [hx]
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := by
    apply finiteApproximation_strengthen F₁ (F₀ ∪ F₁ ∪ F₂) ε₁ _ φ _
      ((min_le_right _ _).trans (min_le_left _ _)) hφ
    intro x hx; simp [hx]
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ := by
    apply finiteApproximation_strengthen F₂ (F₀ ∪ F₁ ∪ F₂) ε₂ _ φ _
      ((min_le_right _ _).trans (min_le_right _ _)) hφ
    intro x hx; simp [hx]
  obtain ⟨Kφ, hKφ, _, hinj, htileφ, hforward, hcolumns⟩ := hdeform φ hφ₀
  have hadj : ∀ s ∈ T, ∀ t ∈ T,
      Tiling.RationalSlopes.DirectionalOverlap K δ s t ↔
        Tiling.RationalSlopes.DirectionalOverlap Kφ δ (deformPoint φ s) (deformPoint φ t) := by
    simpa only [hn] using hoverlap φ hφ₁ Kφ hKφ
  obtain ⟨e, hcentres⟩ := earthquakeComponent_centres_transport K Kφ δ T (deformPoint φ) hinj hadj
  have hCT (C : Tiling.RationalSlopes.EarthquakeComponent K δ T) : C.centres ⊆ T := by
    rintro x ⟨v, hv, rfl⟩
    exact v.property
  have hdisj (A B : Set Plane) (hAT : A ⊆ T) (hBT : B ⊆ T) :
      Disjoint (deformPoint φ '' A) (deformPoint φ '' B) ↔ Disjoint A B := by
    constructor
    · intro h
      rw [Set.disjoint_left] at h ⊢
      intro x hxA hxB
      exact h (Set.mem_image_of_mem _ hxA) (Set.mem_image_of_mem _ hxB)
    · intro h
      rw [Set.disjoint_left] at h ⊢
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have : b = a := hinj (hBT hb) (hAT ha) hab
      exact h ha (this ▸ hb)
  have hinvariant : ∀ S ⊆ T,
      Tiling.Polygonal.IsInvariantAlong (Tiling.Polygonal.regularSupport K S) δ ↔
        Tiling.Polygonal.IsInvariantAlong
          (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) δ := by
    intro S hST
    rw [invariantSubfamily_iff_componentClosed K δ T S hdim htile hST,
      invariantSubfamily_iff_componentClosed Kφ δ (deformPoint φ '' T)
        (deformPoint φ '' S) hdim htileφ (Set.image_mono hST)]
    constructor
    · intro h Cφ
      obtain ⟨C, rfl⟩ := e.surjective Cφ
      rw [hcentres]
      rcases h C with hd | hs
      · exact Or.inl ((hdisj C.centres S (hCT C) hST).mpr hd)
      · exact Or.inr (Set.image_mono hs)
    · intro h C
      have hc := h (e C)
      rw [hcentres C] at hc
      rcases hc with hd | hs
      · exact Or.inl ((hdisj C.centres S (hCT C) hST).mp hd)
      · exact Or.inr ((hinj.image_subset_image_iff (hCT C) hST).mp hs)
  have hcompare : ∀ s ∈ T, ∀ t ∈ T,
      normalEval n s < normalEval n t ↔
        normalEval n (deformPoint φ s) < normalEval n (deformPoint φ t) := by
    obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
    let O : Set Plane := connectedComponentIn K.openCarrier z
    have hO : O ∈ Tiling.interiorComponents K.support := ⟨z, hz, rfl⟩
    obtain ⟨u, _, hu, _, _, _, _, _⟩ := component_normalProjection K n O hO
    intro s hs t ht
    have hc := (horder φ hφ₂).1 (u + s) (Set.add_mem_add hu hs)
      (u + t) (Set.add_mem_add hu ht)
    simpa only [normalEval_add, rationalNormal_commutes, map_add,
      Rat.cast_add, add_lt_add_iff_left] using hc
  have hreflect (s : Plane) (hs : s ∈ T) (t : Plane) (ht : t ∈ T)
      (heq : normalEval n (deformPoint φ s) = normalEval n (deformPoint φ t)) :
      normalEval n s = normalEval n t := by
    rcases lt_trichotomy (normalEval n s) (normalEval n t) with hlt | he | hgt
    · have := (hcompare s hs t ht).mp hlt
      exact (not_lt_of_ge heq.ge this).elim
    · exact he
    · have := (hcompare t ht s hs).mp hgt
      exact (not_lt_of_ge heq.le this).elim
  refine ⟨Kφ, hKφ, hinj, htileφ, hinvariant, e, ?_⟩
  intro C
  refine ⟨hcentres C, ?_⟩
  rw [hcentres C]
  constructor
  · exact hcolumns C.centres (hCT C)
  · intro hcol
    have hCne : C.centres.Nonempty := C.nonempty_supp.image Subtype.val
    obtain ⟨t, ht⟩ := C.nonempty_supp.image Subtype.val
    have hline : Tiling.Polygonal.IsLineSupported C.centres δ := by
      obtain ⟨a, ha⟩ := hcol.2.2.1
      refine ⟨t, ?_⟩
      intro s hs
      have hst : deformPoint φ s - deformPoint φ t ∈ normalDirection n := by
        rw [hn]
        simpa only [sub_sub_sub_cancel_right] using
          δ.sub_mem (ha _ (Set.mem_image_of_mem _ hs)) (ha _ (Set.mem_image_of_mem _ ht))
      have heqφ : normalEval n (deformPoint φ s) = normalEval n (deformPoint φ t) := by
        have hz := (normalDirection_mem_iff n _).mp hst
        rw [normalEval_sub] at hz
        linarith
      rw [← hn]
      apply (normalDirection_mem_iff n _).mpr
      rw [normalEval_sub, hreflect s (hCT C hs) t (hCT C ht) heqφ]
      ring
    have hpack : Tiling.IsPacking K.prototileFamily (K.placements C.centres) := by
      apply (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K C.centres).mpr
      intro s hs t ht hst
      exact (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K T).mp htile.2.1
        (hCT C hs) (hCT C ht) hst
    exact ⟨hpack, hCne, hline, (hinvariant C.centres (hCT C)).mpr hcol.2.2.2⟩



-- Diagnostic only: exact project dependency closure; never used by a proof.








-- Final observational audits: small independently elaborated batches under defaults.





















end Tiling.RationalSlopes.Approximation
