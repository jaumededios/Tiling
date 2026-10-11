import Tiling.AxisParallel.Core
import Tiling.AxisParallel.Foundations.IntrinsicVertices

set_option linter.style.header false

open Filter Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel

private theorem Region.eq_of_support_eq {K L : Region}
    (h : K.support = L.support) : K = L := by
  cases K with
  | mk K hK =>
    cases L with
    | mk L hL =>
      simp only [Region.mk.injEq]
      cases K with
      | mk Ks Kp Kn =>
        cases L with
        | mk Ls Lp Ln =>
          simpa only [Tiling.RationalPolygonal.PolygonalRegion.mk.injEq] using h

/-- A regular-open axis-parallel polygon determines a unique region. -/
theorem Region.ofRegularOpen
    (Omega : Set Tiling.Plane)
    (hopen : IsOpen Omega)
    (hregular : interior (closure Omega) = Omega)
    (hbounded : Bornology.IsBounded Omega)
    (hpositive : 0 < (MeasureTheory.volume Omega).toReal)
    (hpolygonal : Tiling.IsPolygonal (closure Omega))
    (haxisParallel : Tiling.IsAxisParallel (closure Omega)) :
    ∃! K : Region, K.openCarrier = Omega := by
  have _hcontext : IsOpen Omega ∧ Bornology.IsBounded Omega := ⟨hopen, hbounded⟩
  have hmeasure : MeasureTheory.volume Omega ≠ 0 := by
    intro hzero
    rw [hzero] at hpositive
    simp at hpositive
  have hnonempty : (closure Omega).Nonempty :=
    (MeasureTheory.nonempty_of_measure_ne_zero hmeasure).mono subset_closure
  let K : Region := {
    support := closure Omega
    isPolygonal := hpolygonal
    nonempty := hnonempty
    isAxisParallel := haxisParallel }
  refine ⟨K, hregular, ?_⟩
  intro L hL
  apply Region.eq_of_support_eq
  calc
    L.support = closure (interior L.support) := L.isPolygonal.closure_interior.symm
    _ = closure L.openCarrier := rfl
    _ = closure Omega := congrArg closure hL
    _ = K.support := rfl

/-- The canonical carrier of a region is regular open. -/
theorem Region.openCarrier_regularOpen (K : Region) :
    IsOpen K.openCarrier ∧ interior (closure K.openCarrier) = K.openCarrier := by
  refine ⟨isOpen_interior, ?_⟩
  change interior (closure (interior K.support)) = interior K.support
  rw [K.isPolygonal.closure_interior]

theorem horizontalProjectionClosure_finiteClosedIntervals :
    ∀ K : Region, ∃ (n : Nat) (left right : Fin n → ℝ),
      (∀ i, left i < right i) ∧
        closure (Complex.re '' K.openCarrier) =
          ⋃ i, Set.Icc (left i) (right i) := by
  intro K
  classical
  obtain ⟨R⟩ := K.isAxisParallel
  let E := {s : Set Tiling.Plane // s ∈ R.pieces}
  let _ : Fintype E := Fintype.ofFinite E
  let e : Fin (Fintype.card E) ≃ E := Fintype.equivFin E |>.symm
  let piece : Fin (Fintype.card E) → Set Tiling.Plane := fun i ↦ (e i).1
  have hpiece (i : Fin (Fintype.card E)) : piece i ∈ R.pieces := (e i).2
  choose p q hre him hpq using fun i ↦ R.isRectangle (piece i) (hpiece i)
  let a : Fin (Fintype.card E) → ℝ := fun i ↦ min (p i).re (q i).re
  let b : Fin (Fintype.card E) → ℝ := fun i ↦ max (p i).re (q i).re
  have himagePiece (i : Fin (Fintype.card E)) :
      Complex.re '' piece i = Icc (a i) (b i) := by
    rw [hpq i]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change z ∈ Complex.reProdIm
        (Set.uIcc (p i).re (q i).re) (Set.uIcc (p i).im (q i).im) at hz
      have hzre : z.re ∈ Set.uIcc (p i).re (q i).re := hz.1
      simpa only [a, b, Set.uIcc] using hzre
    · intro hx
      let z : ℂ := Complex.mk x (p i).im
      refine ⟨z, ?_, by simp [z]⟩
      change z ∈ Complex.reProdIm
        (Set.uIcc (p i).re (q i).re) (Set.uIcc (p i).im (q i).im)
      constructor
      · change z.re ∈ Set.uIcc (p i).re (q i).re
        simpa only [z, a, b, Set.uIcc] using hx
      · change z.im ∈ Set.uIcc (p i).im (q i).im
        change (p i).im ∈ Set.uIcc (p i).im (q i).im
        exact left_mem_uIcc
  have hprojectionSupport : Complex.re '' K.support =
      ⋃ i, Complex.re '' piece i := by
    rw [← R.sUnion_eq]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨s, hsR, hzs⟩ := Set.mem_sUnion.mp hz
      let es : E := ⟨s, hsR⟩
      exact Set.mem_iUnion.2 ⟨Fintype.equivFin E es, by
        refine ⟨z, ?_, rfl⟩
        simpa [piece, e, es] using hzs⟩
    · rintro hx
      obtain ⟨i, z, hzi, rfl⟩ := Set.mem_iUnion.mp hx
      refine ⟨z, Set.mem_sUnion.2 ⟨piece i, hpiece i, hzi⟩, rfl⟩
  have hprojectionClosure : closure (Complex.re '' K.openCarrier) =
      Complex.re '' K.support := by
    apply Set.Subset.antisymm
    · apply closure_minimal
      · exact Set.image_mono interior_subset
      · exact (K.isPolygonal.isCompact.image Complex.continuous_re).isClosed
    · rw [← K.isPolygonal.closure_interior]
      exact image_closure_subset_closure_image Complex.continuous_re
  have hclosedIntervals : closure (Complex.re '' K.openCarrier) =
      ⋃ i, Icc (a i) (b i) := by
    rw [hprojectionClosure, hprojectionSupport]
    apply iUnion_congr
    exact himagePiece
  refine ⟨Fintype.card E, a, b, ?_, hclosedIntervals⟩
  intro i
  simpa [a, b] using lt_or_gt_of_ne (hre i).symm

/-- The canonical open carrier and closed polygonal support have the same frontier. -/
theorem Region.frontier_openCarrier_eq_frontier_support (K : Region) :
    frontier K.openCarrier = frontier K.support := by
  rw [frontier, frontier]
  change closure (interior K.support) \ interior (interior K.support) =
    closure K.support \ interior K.support
  rw [K.isPolygonal.closure_interior, interior_interior,
    K.isPolygonal.isClosed.closure_eq]

/-- A polygonal support and its open carrier agree almost everywhere. -/
theorem Region.openCarrier_aeEq_support (K : Region) :
    K.openCarrier =ᵐ[MeasureTheory.volume] K.support :=
  K.toPolygonalRegion.openCarrier_ae_eq

/-- Placed vertices are the intrinsic vertices translated by the placement centre. -/
theorem Region.polygonalProtoTiling_placedVertices
    (K : Region) (T : Set Tiling.Plane)
    (i : (K.polygonalProtoTiling T).placements) :
    (K.polygonalProtoTiling T).placedVertexSet i = i.1.1 +ᵥ K.vertices :=
  rfl

/-- The frontier of the open carrier is null. -/
theorem Region.volume_frontier (K : Region) :
    MeasureTheory.volume (frontier K.openCarrier) = 0 := by
  apply measure_mono_null frontier_interior_subset
  exact K.isPolygonal.volume_frontier

/-- Regularization by `interior ∘ closure` is regular open. -/
theorem regularSupport_isRegularOpen (K : Region) (S : Set Tiling.Plane) :
    IsOpen (regularSupport K S) ∧
      interior (closure (regularSupport K S)) = regularSupport K S := by
  refine ⟨isOpen_interior, ?_⟩
  simp [regularSupport, Tiling.Polygonal.regularSupport]

/-- Local equality of planar sets persists after regularization on the quarter-radius ball. -/
theorem regularSupport_eq_of_openUnion_eq_on_ball
    {U V : Set Tiling.Plane} {a : Tiling.Plane} {R : ℝ} (hR : 0 < R)
    (hUV : ∀ z ∈ Metric.ball a R, z ∈ U ↔ z ∈ V) :
    ∀ z ∈ Metric.ball a (R / 4),
      z ∈ interior (closure U) ↔ z ∈ interior (closure V) := by
  have hcl : ∀ z ∈ Metric.ball a (R / 2), z ∈ closure U ↔ z ∈ closure V := by
    intro z hz
    constructor
    · intro hzU
      apply mem_closure_iff.2
      intro O hO hzO
      let W := O ∩ Metric.ball a R
      have hWopen : IsOpen W := hO.inter Metric.isOpen_ball
      have hzW : z ∈ W := by
        constructor
        · exact hzO
        · rw [Metric.mem_ball]
          have hza : dist a z < R / 2 := by simpa [Metric.mem_ball, dist_comm] using hz
          rw [dist_comm]
          linarith
      obtain ⟨w, hwW, hwU⟩ := mem_closure_iff.mp hzU W hWopen hzW
      exact ⟨w, ⟨hwW.1, (hUV w hwW.2).mp hwU⟩⟩
    · intro hzV
      apply mem_closure_iff.2
      intro O hO hzO
      let W := O ∩ Metric.ball a R
      have hWopen : IsOpen W := hO.inter Metric.isOpen_ball
      have hzW : z ∈ W := by
        constructor
        · exact hzO
        · rw [Metric.mem_ball]
          have hza : dist a z < R / 2 := by simpa [Metric.mem_ball, dist_comm] using hz
          rw [dist_comm]
          linarith
      obtain ⟨w, hwW, hwV⟩ := mem_closure_iff.mp hzV W hWopen hzW
      exact ⟨w, ⟨hwW.1, (hUV w hwW.2).mpr hwV⟩⟩
  intro z hz
  constructor
  · intro hzU
    apply (mem_interior_iff_mem_nhds).2
    apply Metric.mem_nhds_iff.2
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      ((mem_interior_iff_mem_nhds).1 hzU)
    let ε' := min ε (R / 2 - dist a z)
    have hε' : 0 < ε' := by
      dsimp [ε']
      have hza : dist a z < R / 4 := by simpa [Metric.mem_ball, dist_comm] using hz
      exact lt_min hε (by linarith)
    refine ⟨ε', hε', ?_⟩
    intro w hw
    have hwcl : w ∈ closure U := hεsub
      (Metric.ball_subset_ball (min_le_left _ _) hw)
    apply (hcl w ?_).mp hwcl
    rw [Metric.mem_ball]
    have hza : dist a z < R / 4 := by simpa [Metric.mem_ball, dist_comm] using hz
    have hwz : dist z w < ε' := by simpa [Metric.mem_ball, dist_comm] using hw
    calc
      dist w a = dist a w := dist_comm _ _
      _ ≤ dist a z + dist z w := dist_triangle _ _ _
      _ < dist a z + (R / 2 - dist a z) :=
        add_lt_add_of_le_of_lt (le_rfl)
          (lt_of_lt_of_le hwz (min_le_right _ _))
      _ = R / 2 := by ring
  · intro hzV
    apply (mem_interior_iff_mem_nhds).2
    apply Metric.mem_nhds_iff.2
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      ((mem_interior_iff_mem_nhds).1 hzV)
    let ε' := min ε (R / 2 - dist a z)
    have hε' : 0 < ε' := by
      dsimp [ε']
      have hza : dist a z < R / 4 := by simpa [Metric.mem_ball, dist_comm] using hz
      exact lt_min hε (by linarith)
    refine ⟨ε', hε', ?_⟩
    intro w hw
    have hwcl : w ∈ closure V := hεsub
      (Metric.ball_subset_ball (min_le_left _ _) hw)
    apply (hcl w ?_).mpr hwcl
    rw [Metric.mem_ball]
    have hza : dist a z < R / 4 := by simpa [Metric.mem_ball, dist_comm] using hz
    have hwz : dist z w < ε' := by simpa [Metric.mem_ball, dist_comm] using hw
    calc
      dist w a = dist a w := dist_comm _ _
      _ ≤ dist a z + dist z w := dist_triangle _ _ _
      _ < dist a z + (R / 2 - dist a z) :=
        add_lt_add_of_le_of_lt (le_rfl)
          (lt_of_lt_of_le hwz (min_le_right _ _))
      _ = R / 2 := by ring

/-- Local equality of planar sets persists after regularization on a smaller ball. -/
theorem regularSupport_local_eq_of_openUnion_eq_on_ball
    {U V : Set Tiling.Plane} {a : Tiling.Plane} {R : ℝ} (hR : 0 < R)
    (hUV : ∀ z ∈ Metric.ball a R, z ∈ U ↔ z ∈ V) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.ball a r,
      z ∈ interior (closure U) ↔ z ∈ interior (closure V) := by
  exact ⟨R / 4, by positivity, regularSupport_eq_of_openUnion_eq_on_ball hR hUV⟩

/-- Measure-disjoint polygonal placements are exactly disjoint open carriers. -/
theorem isPacking_iff_openCarrier_disjoint (K : Region) (S : Set Tiling.Plane) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) ↔
      Set.Pairwise S
        (Disjoint on ((· +ᵥ K.openCarrier) : Tiling.Plane → Set Tiling.Plane)) := by
  let P := K.polygonalProtoTiling S
  constructor
  · intro hpacking s hs t ht hst
    let i : P.placements := ⟨(s, ()), hs⟩
    let j : P.placements := ⟨(t, ()), ht⟩
    have hij : i ≠ j := by
      intro hij
      exact hst (congrArg (fun q : P.placements ↦ q.1.1) hij)
    have hd := P.interior_placedTile_disjoint hpacking hij
    change Disjoint (interior (s +ᵥ K.support))
      (interior (t +ᵥ K.support)) at hd
    change Disjoint (s +ᵥ interior K.support) (t +ᵥ interior K.support)
    simpa only [interior_vadd] using hd
  · intro hdisjoint i hi j hj hij
    have hcent : i.1 ≠ j.1 := by
      intro hcent
      apply hij
      cases i
      cases j
      simp_all
    have hopenDisjoint := hdisjoint hi hj hcent
    let P := K.polygonalProtoTiling S
    have hinterior : Disjoint
        (interior (Tiling.placedTile P.prototiles i))
        (interior (Tiling.placedTile P.prototiles j)) := by
      change Disjoint (i.1 +ᵥ interior K.support)
        (j.1 +ᵥ interior K.support) at hopenDisjoint
      change Disjoint (interior (i.1 +ᵥ K.support))
        (interior (j.1 +ᵥ K.support))
      simpa only [interior_vadd] using hopenDisjoint
    have hsubset :
        Tiling.placedTile P.prototiles i ∩ Tiling.placedTile P.prototiles j ⊆
          frontier (Tiling.placedTile P.prototiles i) ∪
            frontier (Tiling.placedTile P.prototiles j) := by
      rintro x ⟨hxi, hxj⟩
      by_cases hxi' : x ∈ interior (Tiling.placedTile P.prototiles i)
      · right
        apply (mem_frontier_iff_notMem_interior hxj).2
        intro hxj'
        exact Set.disjoint_left.1 hinterior hxi' hxj'
      · left
        exact (mem_frontier_iff_notMem_interior hxi).2 hxi'
    apply measure_mono_null hsubset
    rw [measure_union_null]
    · exact (P.isPolygonal_placedTile i).volume_frontier
    · exact (P.isPolygonal_placedTile j).volume_frontier

/-- A packing by a fixed polygonal region has a separation constant independent of its centres. -/
theorem exists_packingSeparation (K : Region) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ S : Set Tiling.Plane,
        Tiling.IsPacking K.toPolygonalRegion.prototileFamily
            (K.toPolygonalRegion.placements S) →
        ∀ s ∈ S, ∀ t ∈ S, s ≠ t → delta ≤ dist s t := by
  obtain ⟨c, hc⟩ := K.isPolygonal.interior_nonempty K.nonempty
  change c ∈ K.openCarrier at hc
  have hnhds : K.openCarrier ∈ 𝓝 c :=
    (Region.openCarrier_regularOpen K).1.mem_nhds hc
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨r + r, add_pos hr hr, ?_⟩
  intro S hpacking s hs t ht hst
  have hdisjoint :=
    (isPacking_iff_openCarrier_disjoint K S).mp hpacking hs ht hst
  have ball_subset (a : Tiling.Plane) :
      Metric.ball (a + c) r ⊆ a +ᵥ K.openCarrier := by
    intro z hz
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    apply hball
    simpa [dist_eq_norm_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hz
  have hballs : Disjoint (Metric.ball (s + c) r) (Metric.ball (t + c) r) :=
    hdisjoint.mono (ball_subset s) (ball_subset t)
  have hdist := (disjoint_ball_ball_iff hr hr).mp hballs
  rw [show dist (s + c) (t + c) = dist s t by
    simp only [dist_eq_norm]
    congr 1
    abel] at hdist
  exact hdist

private theorem finite_inter_of_bounded_of_pairwise_le_dist
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S Q : Set E} {delta : ℝ} (hdelta : 0 < delta)
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
        linarith
    · rintro rfl
      exact ⟨Metric.mem_ball_self hdelta, hs⟩
  obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : E)
  have hcompact : IsCompact (S ∩ Metric.closedBall 0 R) :=
    Metric.isCompact_of_isClosed_isBounded
      (hSclosed.inter Metric.isClosed_closedBall)
      (Metric.isBounded_closedBall.subset inter_subset_right)
  apply (hcompact.finite (hSdiscrete.mono inter_subset_left)).subset
  exact inter_subset_inter_right S hR

/-- Packing centres are locally finite and hence countable. -/
theorem IsPacking.locallyFinite_centres
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) :
    (∀ Q : Set Tiling.Plane, Bornology.IsBounded Q → (S ∩ Q).Finite) ∧
      S.Countable := by
  obtain ⟨delta, hdelta, hsep⟩ := exists_packingSeparation K
  have hpairwise : S.Pairwise fun x y ↦ delta ≤ dist x y :=
    hsep S hpacking
  have hfinite : ∀ Q : Set Tiling.Plane, Bornology.IsBounded Q →
      (S ∩ Q).Finite := fun Q hQ ↦
    finite_inter_of_bounded_of_pairwise_le_dist hdelta hpairwise hQ
  refine ⟨hfinite, ?_⟩
  have hcover : S ⊆ ⋃ n : ℕ, S ∩ Metric.closedBall 0 n := by
    intro x hx
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt ‖x‖
    rw [Set.mem_iUnion]
    refine ⟨n, hx, ?_⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hn.le
  exact (Set.countable_iUnion fun n : ℕ ↦
    (hfinite (Metric.closedBall 0 (n : ℝ))
      Metric.isBounded_closedBall).countable).mono hcover

/-- The multiplicity-facing statement of `TilesOn` is its native definition. -/
theorem tilesOn_iff_multiplicity (K : Region) (S D : Set Tiling.Plane) :
    TilesOn K S D ↔
      S.Countable ∧
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) ∧
      ∀ᵐ x ∂MeasureTheory.volume,
        (x ∈ D ↔ ∃ s : S, x ∈ (s.1 +ᵥ K.openCarrier)) :=
  Iff.rfl

/-- Tiling the whole plane through open carriers is equivalent to the existing tiling API. -/
theorem tilesOn_univ_iff_tiles (K : Region) (S : Set Tiling.Plane) :
    TilesOn K S Set.univ ↔ K.toPolygonalRegion.Tiles S := by
  constructor
  · intro h
    refine {
      countable := K.toPolygonalRegion.placements_countable h.1
      isPacking := h.2.1
      isCover := ?_ }
    filter_upwards [h.2.2] with x hx
    obtain ⟨s, hs⟩ := hx.mp (Set.mem_univ x)
    rw [Set.mem_iUnion]
    refine ⟨⟨(s.1, ()), s.2⟩, ?_⟩
    change x ∈ s.1 +ᵥ K.support
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hs ⊢
    exact interior_subset hs
  · intro h
    let P := K.polygonalProtoTiling S
    let _ : Countable P.placements :=
      (K.toPolygonalRegion.placements_countable h.countable).to_subtype
    have hEq :
        (⋃ i : P.placements, interior (Tiling.placedTile P.prototiles i.1))
          =ᵐ[MeasureTheory.volume]
        (⋃ i : P.placements, Tiling.placedTile P.prototiles i.1) :=
      Filter.EventuallyEq.countable_iUnion fun i ↦
        (P.isPolygonal_placedTile i.1).interior_ae_eq
    refine ⟨h.countable, h.isPacking, ?_⟩
    filter_upwards [h.isCover, hEq] with x hx hxeq
    constructor
    · intro _
      have hxopen : x ∈ ⋃ i : P.placements,
          interior (Tiling.placedTile P.prototiles i.1) := hxeq.mpr hx
      rw [Set.mem_iUnion] at hxopen
      obtain ⟨i, hi⟩ := hxopen
      refine ⟨⟨i.1.1, i.2⟩, ?_⟩
      change x ∈ interior (i.1.1 +ᵥ K.support) at hi
      rw [interior_vadd] at hi
      exact hi
    · intro _
      exact Set.mem_univ x

/-- Two regular-open planar sets agreeing almost everywhere agree literally. -/
theorem regularOpen_eq_of_aeEq
    {U V : Set Tiling.Plane}
    (hU : IsOpen U) (hUregular : interior (closure U) = U)
    (hV : IsOpen V) (hVregular : interior (closure V) = V)
    (hUV : U =ᵐ[MeasureTheory.volume] V) : U = V := by
  have closure_mono_of_ae {A B : Set Tiling.Plane}
      (hA : IsOpen A) (hB : IsOpen B)
      (hAB : A =ᵐ[MeasureTheory.volume] B) : A ⊆ closure B := by
    intro x hxA
    by_contra hxB
    let W := A ∩ (closure B)ᶜ
    have hWopen : IsOpen W := hA.inter isClosed_closure.isOpen_compl
    have hxW : x ∈ W := ⟨hxA, hxB⟩
    have hWzero : MeasureTheory.volume W = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr (hAB.mono fun y hy hyW ↦ by
        have hyB : y ∈ B := Eq.mp hy hyW.1
        exact hyW.2 (subset_closure hyB))
    exact hWopen.measure_ne_zero MeasureTheory.volume ⟨x, hxW⟩ hWzero
  have hclosure : closure U = closure V := Set.Subset.antisymm
    (closure_minimal (closure_mono_of_ae hU hV hUV) isClosed_closure)
    (closure_minimal (closure_mono_of_ae hV hU hUV.symm) isClosed_closure)
  calc
    U = interior (closure U) := hUregular.symm
    _ = interior (closure V) := congrArg interior hclosure
    _ = V := hVregular

/-- The closure of the raw open union of a packing is the union of its translated supports. -/
theorem closure_openUnion_eq_iUnion_support
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) :
    closure (openUnion K S) =
      ⋃ s : S, (s : Tiling.Plane) +ᵥ K.support := by
  let P := K.polygonalProtoTiling S
  let toPlacement : S → P.placements := fun s => ⟨(s, ()), s.2⟩
  have htoPlacement : Function.Injective toPlacement := by
    intro s t hst
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) hst)
  have hloc : LocallyFinite (fun s : S ↦ (s : Tiling.Plane) +ᵥ K.support) := by
    exact (P.locallyFinite_placedTile hpacking).comp_injective htoPlacement
  have hopen : LocallyFinite (fun s : S ↦ (s : Tiling.Plane) +ᵥ K.openCarrier) :=
    hloc.subset fun s => vadd_set_mono interior_subset
  rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, hopen.closure_iUnion]
  apply iUnion_congr
  intro s
  rw [closure_vadd]
  rw [show closure K.openCarrier = K.support from K.isPolygonal.closure_interior]

private theorem locallyFinite_iUnion_localBoundaryCross
    {I : Type*} {F : I → Set Tiling.Plane}
    (hfinite : LocallyFinite F) (hclosed : ∀ i, IsClosed (F i))
    (hcross : ∀ i x, ∃ r > 0, ∀ z ∈ Metric.ball x r, z ∈ frontier (F i) →
      z.re = x.re ∨ z.im = x.im)
    (x : Tiling.Plane) :
    ∃ r > 0, ∀ z ∈ Metric.ball x r, z ∈ frontier (⋃ i, F i) →
      z.re = x.re ∨ z.im = x.im := by
  let J : Set I := {i | x ∈ F i}
  have hJfinite : J.Finite := hfinite.point_finite x
  have hincident : ∀ᶠ z in nhds x, ∀ i, z ∈ F i → i ∈ J :=
    hfinite.eventually_subset hclosed x
  have hcrossEventually (i : I) (hi : i ∈ J) :
      ∀ᶠ z in nhds x, z ∈ frontier (F i) →
        z.re = x.re ∨ z.im = x.im := by
    obtain ⟨r, hr, hball⟩ := hcross i x
    exact Filter.mem_of_superset (Metric.ball_mem_nhds x hr) hball
  have hallCross : ∀ᶠ z in nhds x, ∀ i ∈ J, z ∈ frontier (F i) →
      z.re = x.re ∨ z.im = x.im := by
    exact hJfinite.eventually_all.mpr fun i hi ↦ hcrossEventually i hi
  have hevent : ∀ᶠ z in nhds x, ∀ i, z ∈ F i →
      z ∈ frontier (⋃ i, F i) → z.re = x.re ∨ z.im = x.im := by
    filter_upwards [hincident, hallCross] with z hzIncident hzCross i hzi hzfront
    have hzNotInterior : z ∉ interior (F i) := by
      intro hzint
      exact Set.disjoint_left.1 disjoint_interior_frontier
        (interior_mono (subset_iUnion F i) hzint) hzfront
    have hzFiFrontier : z ∈ frontier (F i) := by
      rw [(hclosed i).frontier_eq]
      exact ⟨hzi, hzNotInterior⟩
    exact hzCross i (hzIncident i hzi) hzFiFrontier
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r, hr, fun z hzBall hzFrontier ↦ ?_⟩
  have hzUnion : z ∈ ⋃ i, F i :=
    (hfinite.isClosed_iUnion hclosed).frontier_subset hzFrontier
  obtain ⟨i, hzi⟩ := mem_iUnion.mp hzUnion
  exact hball hzBall i hzi hzFrontier

/-- In a packing, the raw open union agrees a.e. with its regular-open support. -/
theorem openUnion_aeEq_regularSupport
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) :
    openUnion K S =ᵐ[MeasureTheory.volume] regularSupport K S := by
  let P := K.polygonalProtoTiling S
  let C : Set Tiling.Plane :=
    ⋃ i : P.placements, Tiling.placedTile P.prototiles i.1
  have hU : openUnion K S =
      ⋃ i : P.placements, interior (Tiling.placedTile P.prototiles i.1) := by
    ext x
    constructor
    · rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion]
      rintro ⟨s, hs⟩
      rw [Set.mem_iUnion]
      refine ⟨⟨(s.1, ()), s.2⟩, ?_⟩
      change x ∈ interior (s.1 +ᵥ K.support)
      rw [interior_vadd]
      exact hs
    · rw [Set.mem_iUnion]
      rintro ⟨i, hi⟩
      rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion]
      refine ⟨⟨i.1.1, i.2⟩, ?_⟩
      change x ∈ interior (i.1.1 +ᵥ K.support) at hi
      rw [interior_vadd] at hi
      exact hi
  have hC : C = ⋃ s : S, (s : Tiling.Plane) +ᵥ K.support := by
    ext x
    constructor
    · rw [Set.mem_iUnion]
      rintro ⟨i, hi⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨i.1.1, i.2⟩, hi⟩
    · rw [Set.mem_iUnion]
      rintro ⟨s, hs⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨(s.1, ()), s.2⟩, hs⟩
  have hclosure : closure (openUnion K S) = C := by
    exact (closure_openUnion_eq_iUnion_support hpacking).trans hC.symm
  have hUC : openUnion K S ⊆ C := by
    rw [hU]
    exact iUnion_mono fun i ↦ interior_subset
  have hSCountable := (IsPacking.locallyFinite_centres hpacking).2
  let _ : Countable P.placements :=
    (K.toPolygonalRegion.placements_countable hSCountable).to_subtype
  have hAE : openUnion K S =ᵐ[MeasureTheory.volume] C := by
    rw [hU]
    exact Filter.EventuallyEq.countable_iUnion fun i ↦
      (P.isPolygonal_placedTile i.1).interior_ae_eq
  have hUInterior : openUnion K S ⊆ interior C := by
    have hUOpen : IsOpen (openUnion K S) := by
      rw [hU]
      exact isOpen_iUnion fun _ ↦ isOpen_interior
    rw [← hUOpen.interior_eq]
    exact interior_mono hUC
  rw [regularSupport, Tiling.Polygonal.regularSupport, ← openUnion, hclosure]
  filter_upwards [hAE] with x hx
  apply propext
  constructor
  · intro hxU
    exact hUInterior hxU
  · intro hxint
    rw [hx]
    exact (interior_subset : interior C ⊆ C) hxint

/-- Change only the almost-everywhere target of a tiling. -/
theorem TilesOn.congr_ae
    {K : Region} {S D E : Set Tiling.Plane}
    (hTile : TilesOn K S D) (hDE : D =ᵐ[volume] E) :
    TilesOn K S E := by
  refine ⟨hTile.1, hTile.2.1, ?_⟩
  filter_upwards [hTile.2.2, hDE] with x hx hDE
  exact (iff_of_eq hDE).symm.trans hx

/-- An open target determines the regularized support of a tiling. -/
theorem regularSupport_eq_regularization_of_tilesOn
    {K : Region} {S D : Set Tiling.Plane}
    (hDopen : IsOpen D) (hTile : TilesOn K S D) :
    regularSupport K S = interior (closure D) := by
  have hUD : openUnion K S =ᵐ[volume] D := by
    filter_upwards [hTile.2.2] with x hx
    apply propext
    change (x ∈ openUnion K S) ↔ x ∈ D
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    exact hx.symm
  have hUopen : IsOpen (openUnion K S) :=
    isOpen_iUnion fun s ↦ (Region.openCarrier_regularOpen K).1.vadd (s : Tiling.Plane)
  have subset_closure_of_ae {A B : Set Tiling.Plane}
      (hA : IsOpen A) (hAB : A =ᵐ[volume] B) : A ⊆ closure B := by
    intro x hxA
    by_contra hxB
    let W := A ∩ (closure B)ᶜ
    have hWopen : IsOpen W := hA.inter isClosed_closure.isOpen_compl
    have hxW : x ∈ W := ⟨hxA, hxB⟩
    have hWzero : volume W = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr (hAB.mono fun y hy hyW ↦ by
        have hyB : y ∈ B := Eq.mp hy hyW.1
        exact hyW.2 (subset_closure hyB))
    exact hWopen.measure_ne_zero volume ⟨x, hxW⟩ hWzero
  have hclosure : closure (openUnion K S) = closure D := Set.Subset.antisymm
    (closure_minimal (subset_closure_of_ae hUopen hUD) isClosed_closure)
    (closure_minimal (subset_closure_of_ae hDopen hUD.symm) isClosed_closure)
  exact congrArg interior hclosure

/-- A regular-open target of a tiling is the canonical regularized placement support. -/
theorem regularSupport_eq_of_tilesOn
    {K : Region} {S D : Set Tiling.Plane}
    (hDopen : IsOpen D) (hDregular : interior (closure D) = D)
    (hTile : TilesOn K S D) :
    regularSupport K S = D := by
  exact (regularSupport_eq_regularization_of_tilesOn hDopen hTile).trans hDregular

/-- Regularized supports of a countable partition of a tiling remain disjoint
and cover the target almost everywhere. -/
theorem regularSupport_pairwiseDisjoint
    {I : Type*} [Countable I]
    {K : Region} {S D : Set Tiling.Plane}
    (A : I → Set Tiling.Plane)
    (hparts : Set.PairwiseDisjoint Set.univ A)
    (hunion : (⋃ i, A i) = S)
    (hTile : TilesOn K S D) :
    Set.PairwiseDisjoint Set.univ (regularSupport K ∘ A) ∧
      (⋃ i, regularSupport K (A i)) =ᵐ[MeasureTheory.volume] D := by
  have hAS (i : I) : A i ⊆ S := by
    rw [← hunion]
    exact subset_iUnion A i
  have hpacking (i : I) :
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements (A i)) := by
    intro p hp q hq hpq
    exact hTile.2.1 (hAS i hp) (hAS i hq) hpq
  have hopenDisjoint {i j : I} (hij : i ≠ j) :
      Disjoint (openUnion K (A i)) (openUnion K (A j)) := by
    rw [Set.disjoint_left]
    intro x hxi hxj
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hxi hxj
    obtain ⟨s, hsx⟩ := hxi
    obtain ⟨t, htx⟩ := hxj
    have hst : (s : Tiling.Plane) ≠ t := by
      intro hst
      have hdisjoint := hparts (Set.mem_univ i) (Set.mem_univ j) hij
      exact Set.disjoint_left.1 hdisjoint s.2 (hst ▸ t.2)
    have hdisjoint :=
      (isPacking_iff_openCarrier_disjoint K S).mp hTile.2.1
        (hAS i s.2) (hAS j t.2) hst
    exact Set.disjoint_left.1 hdisjoint hsx htx
  refine ⟨?_, ?_⟩
  · intro i _ j _ hij
    change Disjoint (regularSupport K (A i)) (regularSupport K (A j))
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hzero : MeasureTheory.volume
        (regularSupport K (A i) ∩ regularSupport K (A j)) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards
        [openUnion_aeEq_regularSupport (hpacking i),
          openUnion_aeEq_regularSupport (hpacking j)] with y hyi hyj
      intro hy
      have hyi' : y ∈ openUnion K (A i) := by
        change openUnion K (A i) y
        rw [hyi]
        exact hy.1
      have hyj' : y ∈ openUnion K (A j) := by
        change openUnion K (A j) y
        rw [hyj]
        exact hy.2
      exact Set.disjoint_left.1 (hopenDisjoint hij) hyi' hyj'
    exact ((regularSupport_isRegularOpen K (A i)).1.inter
      (regularSupport_isRegularOpen K (A j)).1).measure_ne_zero
        MeasureTheory.volume ⟨x, hxi, hxj⟩ hzero
  · have hraw : (⋃ i, openUnion K (A i)) = openUnion K S := by
      ext x
      simp only [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion]
      constructor
      · rintro ⟨i, s, hs⟩
        exact ⟨⟨s, hAS i s.2⟩, hs⟩
      · rintro ⟨s, hs⟩
        have hsUnion : (s : Tiling.Plane) ∈ ⋃ i, A i := by
          rw [hunion]
          exact s.2
        rw [Set.mem_iUnion] at hsUnion
        obtain ⟨i, hi⟩ := hsUnion
        exact ⟨i, ⟨⟨s, hi⟩, hs⟩⟩
    have hpieces :
        (⋃ i, openUnion K (A i)) =ᵐ[MeasureTheory.volume]
          ⋃ i, regularSupport K (A i) :=
      Filter.EventuallyEq.countable_iUnion fun i ↦
        openUnion_aeEq_regularSupport (hpacking i)
    have htarget : openUnion K S =ᵐ[MeasureTheory.volume] D := by
      filter_upwards [hTile.2.2] with x hx
      change (x ∈ openUnion K S) = (x ∈ D)
      apply propext
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      exact hx.symm
    exact hpieces.symm.trans ((Filter.EventuallyEq.of_eq hraw).trans htarget)

theorem frontier_eventuallyEq_of_eventuallyEq
    {D E : Set Tiling.Plane} {x : Tiling.Plane}
    (hDE : D =ᶠ[𝓝 x] E) :
    frontier D =ᶠ[𝓝 x] frontier E := by
  have hnhds : ∀ᶠ y in 𝓝 x, D =ᶠ[𝓝 y] E := hDE.eventually_nhds
  filter_upwards [hnhds] with y hy
  apply propext
  have closureIff (A B : Set Tiling.Plane)
      (hAB : A =ᶠ[nhds y] B) :
      y ∈ closure A ↔ y ∈ closure B := by
    rw [mem_closure_iff_frequently, mem_closure_iff_frequently]
    constructor
    · intro hA
      exact (hA.and_eventually hAB).mono fun z hz ↦ Eq.mp hz.2 hz.1
    · intro hB
      exact (hB.and_eventually hAB).mono fun z hz ↦ Eq.mpr hz.2 hz.1
  have hyCompl : Dᶜ =ᶠ[nhds y] Eᶜ :=
    hy.mono fun z hz ↦ congrArg Not hz
  change y ∈ frontier D ↔ y ∈ frontier E
  rw [frontier_eq_closure_inter_closure,
    frontier_eq_closure_inter_closure, mem_inter_iff, mem_inter_iff,
    closureIff D E hy, closureIff Dᶜ Eᶜ hyCompl]

theorem isProperVertex_iff_of_eventuallyEq
    {D E : Set Tiling.Plane} {x : Tiling.Plane}
    (hDE : D =ᶠ[nhds x] E) :
    IsProperVertex D x ↔ IsProperVertex E x := by
  have hfront := frontier_eventuallyEq_of_eventuallyEq hDE
  have hfrontx : x ∈ frontier D ↔ x ∈ frontier E :=
    Iff.of_eq hfront.self_of_nhds
  have hstraight :
      Tiling.BoundaryLocallyStraightAt D x ↔
        Tiling.BoundaryLocallyStraightAt E x := by
    constructor
    · rintro ⟨L, hxL, hdim, hline⟩
      refine ⟨L, hxL, hdim, ?_⟩
      filter_upwards [hfront, hline] with y hyfront hyline
      exact (Iff.of_eq hyfront).symm.trans hyline
    · rintro ⟨L, hxL, hdim, hline⟩
      refine ⟨L, hxL, hdim, ?_⟩
      filter_upwards [hfront, hline] with y hyfront hyline
      exact (Iff.of_eq hyfront).trans hyline
  exact and_congr hfrontx (not_congr hstraight)


theorem properVertexProvenance :
    ∀ {K : Region} {S : Set Tiling.Plane},
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) →
      ∀ x ∈ properVertices (regularSupport K S),
        ∃ v ∈ K.vertices, ∃ s ∈ S, x = v + s := by
  intro K S hpacking x hx
  let A := K.polygonalProtoTiling S
  have hpack : Tiling.IsPacking A.prototiles A.placements := by
    intro i hi j hj hij
    apply hpacking
    · exact hi
    · exact hj
    · exact hij
  have hcarrier : A.placementCarrier Set.univ =
      closure (openUnion K S) := by
    rw [Tiling.PolygonalProtoTiling.placementCarrier]
    rw [closure_openUnion_eq_iUnion_support hpack]
    ext z
    constructor
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨i, hi⟩ := hz
      rw [Set.mem_iUnion]
      exact ⟨⟨i.1.1.1, i.1.2⟩, hi⟩
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨s, hs⟩ := hz
      rw [Set.mem_iUnion]
      let i : A.placements := ⟨((s : Tiling.Plane), ()), s.2⟩
      refine ⟨⟨i, trivial⟩, ?_⟩
      exact hs
  have hfrontier_eq :
      frontier (A.placementCarrier Set.univ) =
        frontier (regularSupport K S) := by
    rw [regularSupport, Tiling.Polygonal.regularSupport, ← openUnion, ← hcarrier]
    simp [frontier, A.placementCarrier_closure_interior hpack Set.univ,
      (A.placementCarrier_isClosed hpack Set.univ).closure_eq]
  have hxfrontier : x ∈ frontier (A.placementCarrier Set.univ) := by
    rw [hfrontier_eq]
    exact hx.1
  have hxnotstraight : ¬Tiling.BoundaryLocallyStraightAt
      (A.placementCarrier Set.univ) x := by
    intro hstraight
    apply hx.2
    simpa only [Tiling.BoundaryLocallyStraightAt, hfrontier_eq] using hstraight
  obtain ⟨i, hiQ, hxi⟩ :=
    A.exists_vertex_of_not_boundaryLocallyStraightAt hpack Set.univ
      hxfrontier hxnotstraight
  have hcenterS : i.1.1 ∈ S := i.2
  have hplaced : x ∈ i.1.1 +ᵥ K.vertices := by
    simpa only [A, Region.polygonalProtoTiling_placedVertices] using hxi
  obtain ⟨v, hv, hvx⟩ := Set.mem_vadd_set.mp hplaced
  refine ⟨v, hv, i.1.1, hcenterS, ?_⟩
  simpa [vadd_eq_add, add_comm] using hvx.symm


theorem frontier_vadd_eq
    (u : Tiling.Plane) (D : Set Tiling.Plane) :
    frontier (u +ᵥ D) = u +ᵥ frontier D := by
  rw [frontier, closure_vadd, interior_vadd]
  ext z
  simp only [frontier, Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem]


theorem translated_openCarrier_frontier_cross
    (K : Region) (t a : Tiling.Plane) :
    ∃ r > 0, ∀ z ∈ Metric.ball a r, z ∈ frontier (t +ᵥ K.openCarrier) →
      z.re = a.re ∨ z.im = a.im := by
  obtain ⟨r, hr, hcross⟩ := K.isAxisParallel.localBoundaryCross (a - t)
  have hfrontEq : frontier K.openCarrier = frontier K.support := by
    rw [frontier, frontier]
    change closure (interior K.support) \ interior (interior K.support) =
      closure K.support \ interior K.support
    rw [K.isPolygonal.closure_interior, interior_interior,
      K.isPolygonal.isClosed.closure_eq]
  have hfront_vadd : frontier (t +ᵥ K.openCarrier) =
      t +ᵥ frontier K.openCarrier := by
    rw [frontier, closure_vadd, interior_vadd]
    ext z
    simp only [frontier, Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem]
  refine ⟨r, hr, ?_⟩
  intro z hz hzfront
  have hz' : z - t ∈ Metric.ball (a - t) r := by
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    rw [show z - t - (a - t) = z - a by ring]
    exact hz
  have hfront' : z - t ∈ frontier K.support := by
    have hfrontOpen : z - t ∈ frontier K.openCarrier := by
      have hzv : z ∈ t +ᵥ frontier K.openCarrier := hfront_vadd ▸ hzfront
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_eq_sub] using hzv
    exact hfrontEq ▸ hfrontOpen
  obtain h | h := hcross (z - t) hz' hfront'
  · left
    simpa only [Complex.sub_re] using sub_left_inj.mp h
  · right
    simpa only [Complex.sub_im] using sub_left_inj.mp h

private theorem isAxisParallel_localBoundaryCross_vadd
    {D : Set Tiling.Plane} (hD : Tiling.IsAxisParallel D)
    (u x : Tiling.Plane) :
    ∃ r > 0, ∀ z ∈ Metric.ball x r, z ∈ frontier (u +ᵥ D) →
      z.re = x.re ∨ z.im = x.im := by
  obtain ⟨r, hr, hball⟩ := hD.localBoundaryCross (x - u)
  refine ⟨r, hr, fun z hz hzfront ↦ ?_⟩
  have hzdist : z - u ∈ Metric.ball (x - u) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have heq : z - u - (x - u) = z - x := by abel
    rw [heq]
    exact hz
  have hzsource : z - u ∈ frontier D := by
    rw [frontier_vadd_eq] at hzfront
    simpa only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hzfront
  rcases hball (z - u) hzdist hzsource with h | h
  · left
    simpa only [Complex.sub_re] using sub_left_inj.mp h
  · right
    simpa only [Complex.sub_im] using sub_left_inj.mp h

/-- Under a packing hypothesis, the frontier of a regularized union of translates is locally
contained in the coordinate cross through each point. -/
theorem regularSupport_localBoundaryCross
    {K : Region} {Q : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements Q))
    (x : Tiling.Plane) :
    ∃ r > 0, ∀ z ∈ Metric.ball x r, z ∈ frontier (regularSupport K Q) →
      z.re = x.re ∨ z.im = x.im := by
  let P := K.polygonalProtoTiling Q
  let F : Q → Set Tiling.Plane := fun q ↦ (q : Tiling.Plane) +ᵥ K.support
  let placementOf : Q → P.placements := fun q ↦ ⟨((q : Tiling.Plane), ()), q.2⟩
  have hplacementInjective : Function.Injective placementOf := by
    intro a b hab
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) hab)
  have hfinite : LocallyFinite F := by
    have h := (P.locallyFinite_placedTile hpacking).comp_injective hplacementInjective
    change LocallyFinite F at h
    exact h
  have hlocal : ∀ (i : Q) (y : Tiling.Plane),
      ∃ r > 0, ∀ z ∈ Metric.ball y r,
        z ∈ frontier (F i) → z.re = y.re ∨ z.im = y.im := by
    intro i y
    exact isAxisParallel_localBoundaryCross_vadd K.isAxisParallel i.1 y
  obtain ⟨r, hr, hball⟩ := locallyFinite_iUnion_localBoundaryCross
    hfinite (fun i ↦ K.isPolygonal.isClosed.vadd i.1) hlocal x
  refine ⟨r, hr, fun z hz hzfront ↦ hball z hz ?_⟩
  have hzfront' : z ∈ frontier (closure (openUnion K Q)) :=
    frontier_interior_subset hzfront
  rw [closure_openUnion_eq_iUnion_support hpacking] at hzfront'
  simpa only [F] using hzfront'

/-- The frontier of a vertical cylinder is the vertical cylinder over the frontier of its base. -/
theorem frontier_verticalCylinder {X : Set ℝ} :
    frontier ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) =
      {z : Tiling.Plane | z.re ∈ frontier X} := by
  change frontier (Complex.re ⁻¹' X) = Complex.re ⁻¹' frontier X
  rw [frontier, frontier, Complex.closure_preimage_re,
    Complex.interior_preimage_re, preimage_sdiff]

/-- The frontier of the base of a regular vertical cylinder tiled by `K` is locally finite. -/
theorem TilesOn.verticalCylinder_frontier_locallyFinite
    {K : Region} {S : Set Tiling.Plane} {X : Set ℝ}
    (hTile : TilesOn K S {z : Tiling.Plane | z.re ∈ X})
    (hXopen : IsOpen X) (hXregular : interior (closure X) = X) :
    ∀ C : Set ℝ, IsCompact C → (C ∩ frontier X).Finite := by
  have hcarrierOpen : IsOpen ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) :=
    hXopen.preimage Complex.continuous_re
  have hcarrierRegular :
      interior (closure ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane)) =
        {z : Tiling.Plane | z.re ∈ X} := by
    change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hXregular]
  have hsupport : regularSupport K S = {z : Tiling.Plane | z.re ∈ X} :=
    regularSupport_eq_of_tilesOn hcarrierOpen hcarrierRegular hTile
  have hcross (x : ℝ) : ∃ r > 0, ∀ z ∈ Metric.ball (x : ℂ) r,
      z ∈ frontier ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) →
        z.re = x ∨ z.im = 0 := by
    simpa only [hsupport, Complex.ofReal_re, Complex.ofReal_im] using
      regularSupport_localBoundaryCross hTile.2.1 (x : ℂ)
  have hdiscrete : IsDiscrete (frontier X) := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro x hx
    obtain ⟨r, hr, hball⟩ := hcross x
    let d : ℝ := r / 4
    refine ⟨Set.Ioo (x - d) (x + d), isOpen_Ioo, ?_⟩
    ext y
    constructor
    · rintro ⟨⟨hyLower, hyUpper⟩, hyFrontier⟩
      have hd : 0 < d := div_pos hr (by norm_num)
      let z : Tiling.Plane := (y : ℂ) + (d : ℂ) * Complex.I
      have hzball : z ∈ Metric.ball (x : ℂ) r := by
        rw [Metric.mem_ball]
        calc
          dist z (x : ℂ) ≤ dist z (y : ℂ) + dist (y : ℂ) (x : ℂ) :=
            dist_triangle _ _ _
          _ = d + dist y x := by
            congr 1
            · simp [z, abs_of_pos hd]
            · rw [dist_eq_norm, dist_eq_norm]
              rw [show (y : ℂ) - (x : ℂ) = ((y - x : ℝ) : ℂ) by norm_num,
                Complex.norm_real]
          _ < d + d := by
            gcongr
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith
          _ < r := by dsimp [d]; linarith
      have hzfrontier : z ∈ frontier
          ({w : Tiling.Plane | w.re ∈ X} : Set Tiling.Plane) := by
        rw [frontier_verticalCylinder]
        simpa [z] using hyFrontier
      rcases hball z hzball hzfrontier with hre | him
      · simpa [z] using hre
      · exfalso
        simp [z, hd.ne'] at him
    · rintro rfl
      exact ⟨⟨sub_lt_self _ (by dsimp [d]; positivity),
        lt_add_of_pos_right _ (by dsimp [d]; positivity)⟩, hx⟩
  intro C hC
  exact (hC.inter_right isClosed_frontier).finite
    (hdiscrete.mono inter_subset_right)

theorem boundaryLocallyStraightAt_vadd_iff
    (u : Tiling.Plane) (D : Set Tiling.Plane) (x : Tiling.Plane) :
    Tiling.BoundaryLocallyStraightAt (u +ᵥ D) (u + x) ↔
      Tiling.BoundaryLocallyStraightAt D x := by
  suffices ∀ (v : Tiling.Plane) (E : Set Tiling.Plane) (y : Tiling.Plane),
      Tiling.BoundaryLocallyStraightAt E y →
        Tiling.BoundaryLocallyStraightAt (v +ᵥ E) (v + y) by
    constructor
    · intro h
      have h' := this (-u) (u +ᵥ D) (u + x) h
      simpa only [neg_add_cancel_left, neg_vadd_vadd] using h'
    · exact this u D x
  intro v E y h
  obtain ⟨L, hyL, hdim, hlocal⟩ := h
  let L' : AffineSubspace ℝ Tiling.Plane := AffineSubspace.mk' (v + y) L.direction
  refine ⟨L', AffineSubspace.self_mem_mk' _ _, ?_, ?_⟩
  · dsimp only [L']
    rw [AffineSubspace.direction_mk']
    exact hdim
  · obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨r, hr, fun z hz ↦ ?_⟩
    let z' : Tiling.Plane := z - v
    have hz' : dist z' y < r := by
      have hzEq : z' - y = z - (v + y) := by dsimp only [z']; abel
      simpa only [dist_eq_norm, hzEq] using hz
    have hsource := hball hz'
    rw [frontier_vadd_eq]
    change (z ∈ v +ᵥ frontier E) ↔ z ∈ L'
    have hfrontier : z ∈ v +ᵥ frontier E ↔ z' ∈ frontier E := by
      constructor
      · rintro ⟨w, hw, hwz⟩
        have : w = z' := by
          change v + w = z at hwz
          dsimp only [z']
          rw [← hwz]
          abel
        simpa only [this] using hw
      · intro hz'E
        refine ⟨z', hz'E, ?_⟩
        change v + z' = z
        dsimp only [z']
        abel
    rw [hfrontier, hsource]
    rw [show L = AffineSubspace.mk' y L.direction from
      (AffineSubspace.mk'_eq hyL).symm]
    simp only [L', AffineSubspace.mem_mk']
    change z' - y ∈ L.direction ↔ z - (v + y) ∈ L.direction
    have hzEq : z' - y = z - (v + y) := by
      dsimp only [z']
      abel
    rw [hzEq]


theorem properVertices_vadd_eq (u : Tiling.Plane) (D : Set Tiling.Plane) :
    properVertices (u +ᵥ D) = u +ᵥ properVertices D := by
  ext x
  let y : Tiling.Plane := -u + x
  have hxy : u + y = x := by dsimp [y]; abel
  change IsProperVertex (u +ᵥ D) x ↔ x ∈ u +ᵥ properVertices D
  rw [mem_vadd_set_iff_neg_vadd_mem]
  change IsProperVertex (u +ᵥ D) x ↔ IsProperVertex D y
  change (x ∈ frontier (u +ᵥ D) ∧
      ¬Tiling.BoundaryLocallyStraightAt (u +ᵥ D) x) ↔
    y ∈ frontier D ∧ ¬Tiling.BoundaryLocallyStraightAt D y
  rw [frontier_vadd_eq]
  have hfrontier : x ∈ u +ᵥ frontier D ↔ y ∈ frontier D := by
    rw [mem_vadd_set_iff_neg_vadd_mem]
    rfl
  rw [hfrontier]
  have hstraight := boundaryLocallyStraightAt_vadd_iff u D y
  rw [hxy] at hstraight
  exact and_congr_right fun _ ↦ not_congr hstraight

def properVertexAxisVector (axis : Axis) : Tiling.Plane :=
  match axis with
  | .horizontal => 1
  | .vertical => Complex.I

theorem properVertexAxisVector_ne_zero (axis : Axis) :
    properVertexAxisVector axis ≠ 0 := by
  cases axis <;> simp [properVertexAxisVector]

noncomputable def properVertexAxisLine
    (axis : Axis) (x : Tiling.Plane) : AffineSubspace ℝ Tiling.Plane :=
  AffineSubspace.mk' x (ℝ ∙ properVertexAxisVector axis)

theorem mem_properVertexAxisLine_iff
    (axis : Axis) (x z : Tiling.Plane) :
    z ∈ properVertexAxisLine axis x ↔
      axis.transverseCoord z = axis.transverseCoord x := by
  rw [properVertexAxisLine, AffineSubspace.mem_mk',
    Submodule.mem_span_singleton]
  cases axis
  · simp only [properVertexAxisVector, Axis.transverseCoord]
    constructor
    · rintro ⟨c, hc⟩
      have h := congrArg Complex.im hc
      simp at h ⊢
      linarith
    · intro h
      refine ⟨z.re - x.re, ?_⟩
      apply Complex.ext
      · simp
      · simp [h]
  · simp only [properVertexAxisVector, Axis.transverseCoord]
    constructor
    · rintro ⟨c, hc⟩
      have h := congrArg Complex.re hc
      simp at h ⊢
      linarith
    · intro h
      refine ⟨z.im - x.im, ?_⟩
      apply Complex.ext
      · simp [h]
      · simp

private theorem segment_re_eq_of_mem
    {a b z : Tiling.Plane} (hab : a.re = b.re)
    (hz : z ∈ segment ℝ a b) : z.re = a.re := by
  rw [segment_eq_image] at hz
  obtain ⟨c, _hc, rfl⟩ := hz
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [hab]
  ring

private theorem segment_im_eq_of_mem
    {a b z : Tiling.Plane} (hab : a.im = b.im)
    (hz : z ∈ segment ℝ a b) : z.im = a.im := by
  rw [segment_eq_image] at hz
  obtain ⟨c, _hc, rfl⟩ := hz
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rw [hab]
  ring

private theorem openSegment_eq_vertical'
    (v w : Tiling.Plane) (h : v.re = w.re) :
    openSegment ℝ v w =
      (fun y : ℝ ↦ (v.re : ℂ) + (y : ℂ) * Complex.I) ''
        openSegment ℝ v.im w.im := by
  ext z
  constructor
  · rintro ⟨a, b, ha, hb, hab, hz⟩
    refine ⟨z.im, ⟨a, b, ha, hb, hab, ?_⟩, ?_⟩
    · rw [← hz]
      simp
    · rw [← hz]
      have hweighted (r : ℝ) : a * r + b * r = r := by
        rw [← add_mul, hab, one_mul]
      apply Complex.ext <;> simp [h, hweighted]
  · rintro ⟨y, ⟨a, b, ha, hb, hab, hy⟩, rfl⟩
    refine ⟨a, b, ha, hb, hab, ?_⟩
    have hweighted (r : ℝ) : a * r + b * r = r := by
      rw [← add_mul, hab, one_mul]
    apply Complex.ext
    · simp [h, hweighted]
    · simpa using hy

private theorem openSegment_eq_horizontal'
    (v w : Tiling.Plane) (h : v.im = w.im) :
    openSegment ℝ v w =
      (fun x : ℝ ↦ (x : ℂ) + (v.im : ℂ) * Complex.I) ''
        openSegment ℝ v.re w.re := by
  ext z
  constructor
  · rintro ⟨a, b, ha, hb, hab, hz⟩
    refine ⟨z.re, ⟨a, b, ha, hb, hab, ?_⟩, ?_⟩
    · rw [← hz]
      simp
    · rw [← hz]
      have hweighted (r : ℝ) : a * r + b * r = r := by
        rw [← add_mul, hab, one_mul]
      apply Complex.ext <;> simp [h, hweighted]
  · rintro ⟨x, ⟨a, b, ha, hb, hab, hx⟩, rfl⟩
    refine ⟨a, b, ha, hb, hab, ?_⟩
    have hweighted (r : ℝ) : a * r + b * r = r := by
      rw [← add_mul, hab, one_mul]
    apply Complex.ext
    · simpa using hx
    · simp [h, hweighted]

private theorem isOpen_openSegment_real_of_ne {a b : ℝ} (hab : a ≠ b) :
    IsOpen (openSegment ℝ a b) := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · rw [openSegment_eq_Ioo hab]
    exact isOpen_Ioo
  · rw [openSegment_symm ℝ a b, openSegment_eq_Ioo hba]
    exact isOpen_Ioo

private theorem eventually_verticalLine_mem_segment
    {a b x : Tiling.Plane} (hab : a ≠ b) (hre : a.re = b.re)
    (hx : x ∈ openSegment ℝ a b) :
    ∀ᶠ z in 𝓝 x, z.re = x.re → z ∈ segment ℝ a b := by
  have him : a.im ≠ b.im := by
    intro him
    apply hab
    apply Complex.ext <;> assumption
  have hxImage : x ∈
      (fun y : ℝ ↦ (a.re : ℂ) + (y : ℂ) * Complex.I) ''
        openSegment ℝ a.im b.im := by
    rw [← openSegment_eq_vertical' a b hre]
    exact hx
  obtain ⟨y, hy, hyx⟩ := hxImage
  have hxim : x.im ∈ openSegment ℝ a.im b.im := by
    have hyim : y = x.im := by
      simpa using congrArg Complex.im hyx
    rw [← hyim]
    exact hy
  have hxre : x.re = a.re := by
    have := congrArg Complex.re hyx
    simpa using this.symm
  have hevent : ∀ᶠ z in 𝓝 x, z.im ∈ openSegment ℝ a.im b.im :=
    Complex.continuous_im.continuousAt.eventually
      ((isOpen_openSegment_real_of_ne him).mem_nhds hxim)
  filter_upwards [hevent] with z hz hzx
  apply openSegment_subset_segment ℝ a b
  rw [openSegment_eq_vertical' a b hre]
  refine ⟨z.im, hz, ?_⟩
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      zero_mul, sub_zero, add_zero]
    exact (hzx.trans hxre).symm
  · simp

private theorem eventually_horizontalLine_mem_segment
    {a b x : Tiling.Plane} (hab : a ≠ b) (him : a.im = b.im)
    (hx : x ∈ openSegment ℝ a b) :
    ∀ᶠ z in 𝓝 x, z.im = x.im → z ∈ segment ℝ a b := by
  have hre : a.re ≠ b.re := by
    intro hre
    apply hab
    apply Complex.ext <;> assumption
  have hxImage : x ∈
      (fun y : ℝ ↦ (y : ℂ) + (a.im : ℂ) * Complex.I) ''
        openSegment ℝ a.re b.re := by
    rw [← openSegment_eq_horizontal' a b him]
    exact hx
  obtain ⟨y, hy, hyx⟩ := hxImage
  have hxre : x.re ∈ openSegment ℝ a.re b.re := by
    have hyre : y = x.re := by
      simpa using congrArg Complex.re hyx
    rw [← hyre]
    exact hy
  have hxim : x.im = a.im := by
    have := congrArg Complex.im hyx
    simpa using this.symm
  have hevent : ∀ᶠ z in 𝓝 x, z.re ∈ openSegment ℝ a.re b.re :=
    Complex.continuous_re.continuousAt.eventually
      ((isOpen_openSegment_real_of_ne hre).mem_nhds hxre)
  filter_upwards [hevent] with z hz hzx
  apply openSegment_subset_segment ℝ a b
  rw [openSegment_eq_horizontal' a b him]
  refine ⟨z.re, hz, ?_⟩
  apply Complex.ext
  · simp
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, mul_one, Complex.ofReal_re, Complex.I_re,
      mul_zero, zero_add]
    simpa using (hzx.trans hxim).symm

/-- The non-straight points of a locally finite rectilinear boundary are locally finite,
and translate equivariantly. -/
theorem properVertices_locallyFinite
    {D : Set Tiling.Plane} (hD : IsLocallyAxisParallelPolygonal D) :
    (∀ Q : Set Tiling.Plane, Bornology.IsBounded Q →
      (properVertices D ∩ Q).Finite) ∧
    ∀ u : Tiling.Plane, properVertices (u +ᵥ D) = u +ᵥ properVertices D := by
  classical
  obtain ⟨G, hSegments, hFrontier, hLocallyFinite⟩ := hD.2.2
  refine ⟨?_, ?_⟩
  · intro Q hQ
    obtain ⟨R, hQR⟩ := hQ.subset_closedBall (0 : Tiling.Plane)
    let radius : ℝ := max R 0 + 1
    let B : Set Tiling.Plane := Metric.closedBall 0 radius
    let A : Set (Set Tiling.Plane) :=
      {g | g ∈ G ∧ (g ∩ B).Nonempty}
    have hBbounded : Bornology.IsBounded B := Metric.isBounded_closedBall
    have hAfinite : A.Finite := hLocallyFinite B hBbounded
    let _ : Fintype A := hAfinite.fintype
    choose a b hab haxis hsegment using
      fun g : A ↦ hSegments g.1 g.2.1
    let cross (g h : A) : Tiling.Plane :=
      ((a g).re : ℂ) + ((a h).im : ℂ) * Complex.I
    let endpoints : Finset Tiling.Plane :=
      Finset.univ.biUnion fun g : A ↦ {a g, b g}
    let crossings : Finset Tiling.Plane :=
      Finset.univ.biUnion fun g : A ↦ Finset.univ.image fun h : A ↦ cross g h
    let candidates : Finset Tiling.Plane := endpoints ∪ crossings
    have ha_candidate (g : A) : a g ∈ candidates := by
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_biUnion.mpr
      exact ⟨g, Finset.mem_univ g, by simp⟩
    have hb_candidate (g : A) : b g ∈ candidates := by
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_biUnion.mpr
      exact ⟨g, Finset.mem_univ g, by simp⟩
    have hcross_candidate (g h : A) : cross g h ∈ candidates := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨g, Finset.mem_univ g, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨h, Finset.mem_univ h, rfl⟩
    apply candidates.finite_toSet.subset
    rintro x ⟨hxProper, hxQ⟩
    change IsProperVertex D x at hxProper
    have hxB : x ∈ B := by
      rw [Metric.mem_closedBall]
      have hxR := hQR hxQ
      rw [Metric.mem_closedBall] at hxR
      dsimp only [B, radius]
      exact hxR.trans (by linarith [le_max_left R 0])
    have hxFrontier := hxProper.1
    rw [hFrontier] at hxFrontier
    obtain ⟨g, hgG, hxg⟩ := Set.mem_sUnion.mp hxFrontier
    have hgA : g ∈ A := ⟨hgG, ⟨x, hxg, hxB⟩⟩
    let g₀ : A := ⟨g, hgA⟩
    have hxg₀ : x ∈ g₀.1 := hxg
    by_contra hxCandidate
    have hxa : x ≠ a g₀ := by
      intro h
      apply hxCandidate
      rw [h]
      exact ha_candidate g₀
    have hxb : x ≠ b g₀ := by
      intro h
      apply hxCandidate
      rw [h]
      exact hb_candidate g₀
    have hxSegment : x ∈ segment ℝ (a g₀) (b g₀) := by
      rw [← hsegment g₀]
      exact hxg₀
    have hxOpen : x ∈ openSegment ℝ (a g₀) (b g₀) :=
      mem_openSegment_of_ne_left_right hxa.symm hxb.symm hxSegment
    have hballB : ∀ᶠ z in 𝓝 x, z ∈ B := by
      apply Filter.mem_of_superset (Metric.ball_mem_nhds x zero_lt_one)
      intro z hz
      rw [Metric.mem_ball] at hz
      change dist z 0 ≤ radius
      have hxR := hQR hxQ
      rw [Metric.mem_closedBall] at hxR
      have htriangle := dist_triangle z x (0 : Tiling.Plane)
      dsimp only [radius]
      exact htriangle.trans (by linarith [le_max_left R 0])
    rcases haxis g₀ with hvertical | hhorizontal
    · have hinside := eventually_verticalLine_mem_segment
        (hab g₀) hvertical hxOpen
      have hall : ∀ᶠ z in 𝓝 x, ∀ h : A, z ∈ h.1 → z.re = x.re := by
        rw [Filter.eventually_all]
        intro h
        by_cases hxh : x ∈ h.1
        · have hxSegmentH : x ∈ segment ℝ (a h) (b h) := by
            rw [← hsegment h]
            exact hxh
          rcases haxis h with hverticalH | hhorizontalH
          · apply Filter.Eventually.of_forall
            intro z hz
            exact (segment_re_eq_of_mem hverticalH <| by
              rw [← hsegment h]
              exact hz).trans
                (segment_re_eq_of_mem hverticalH hxSegmentH).symm
          · have hxCross : x = cross g₀ h := by
              apply Complex.ext
              · simp only [cross, Complex.add_re, Complex.ofReal_re,
                  Complex.mul_re, Complex.I_re, mul_zero,
                  Complex.ofReal_im, Complex.I_im, zero_mul,
                  sub_zero, add_zero]
                exact segment_re_eq_of_mem hvertical hxSegment
              · simp only [cross, Complex.add_im, Complex.ofReal_im,
                  Complex.mul_im, Complex.I_im, mul_one,
                  Complex.ofReal_re, Complex.I_re, mul_zero,
                  zero_add]
                simpa using segment_im_eq_of_mem hhorizontalH hxSegmentH
            exact False.elim <| hxCandidate <| hxCross ▸ hcross_candidate g₀ h
        · have hclosed : IsClosed h.1 := by
            rw [hsegment h, segment_eq_image]
            exact (isCompact_Icc.image (by fun_prop)).isClosed
          apply Filter.mem_of_superset (hclosed.isOpen_compl.mem_nhds hxh)
          intro z hz hzmem
          exact False.elim (hz hzmem)
      apply False.elim
      apply hxProper.2
      refine ⟨properVertexAxisLine .vertical x,
        (mem_properVertexAxisLine_iff .vertical x x).2 rfl, ?_, ?_⟩
      · rw [properVertexAxisLine, AffineSubspace.direction_mk']
        exact finrank_span_singleton (properVertexAxisVector_ne_zero .vertical)
      · filter_upwards [hballB, hinside, hall] with z hzB hzInside hzAll
        constructor
        · intro hzFrontier
          rw [hFrontier] at hzFrontier
          obtain ⟨h, hhG, hzh⟩ := Set.mem_sUnion.mp hzFrontier
          have hhA : h ∈ A := ⟨hhG, ⟨z, hzh, hzB⟩⟩
          exact (mem_properVertexAxisLine_iff .vertical x z).2
            (hzAll ⟨h, hhA⟩ hzh)
        · intro hzLine
          rw [hFrontier]
          exact Set.mem_sUnion_of_mem
            (by rw [hsegment g₀]; exact
              hzInside ((mem_properVertexAxisLine_iff .vertical x z).1 hzLine))
            g₀.2.1
    · have hinside := eventually_horizontalLine_mem_segment
        (hab g₀) hhorizontal hxOpen
      have hall : ∀ᶠ z in 𝓝 x, ∀ h : A, z ∈ h.1 → z.im = x.im := by
        rw [Filter.eventually_all]
        intro h
        by_cases hxh : x ∈ h.1
        · have hxSegmentH : x ∈ segment ℝ (a h) (b h) := by
            rw [← hsegment h]
            exact hxh
          rcases haxis h with hverticalH | hhorizontalH
          · have hxCross : x = cross h g₀ := by
              apply Complex.ext
              · simp only [cross, Complex.add_re, Complex.ofReal_re,
                  Complex.mul_re, Complex.I_re, mul_zero,
                  Complex.ofReal_im, Complex.I_im, zero_mul,
                  sub_zero, add_zero]
                exact segment_re_eq_of_mem hverticalH hxSegmentH
              · simp only [cross, Complex.add_im, Complex.ofReal_im,
                  Complex.mul_im, Complex.I_im, mul_one,
                  Complex.ofReal_re, Complex.I_re, mul_zero,
                  zero_add]
                simpa using segment_im_eq_of_mem hhorizontal hxSegment
            exact False.elim <| hxCandidate <| hxCross ▸ hcross_candidate h g₀
          · apply Filter.Eventually.of_forall
            intro z hz
            exact (segment_im_eq_of_mem hhorizontalH <| by
              rw [← hsegment h]
              exact hz).trans
                (segment_im_eq_of_mem hhorizontalH hxSegmentH).symm
        · have hclosed : IsClosed h.1 := by
            rw [hsegment h, segment_eq_image]
            exact (isCompact_Icc.image (by fun_prop)).isClosed
          apply Filter.mem_of_superset (hclosed.isOpen_compl.mem_nhds hxh)
          intro z hz hzmem
          exact False.elim (hz hzmem)
      apply False.elim
      apply hxProper.2
      refine ⟨properVertexAxisLine .horizontal x,
        (mem_properVertexAxisLine_iff .horizontal x x).2 rfl, ?_, ?_⟩
      · rw [properVertexAxisLine, AffineSubspace.direction_mk']
        exact finrank_span_singleton (properVertexAxisVector_ne_zero .horizontal)
      · filter_upwards [hballB, hinside, hall] with z hzB hzInside hzAll
        constructor
        · intro hzFrontier
          rw [hFrontier] at hzFrontier
          obtain ⟨h, hhG, hzh⟩ := Set.mem_sUnion.mp hzFrontier
          have hhA : h ∈ A := ⟨hhG, ⟨z, hzh, hzB⟩⟩
          exact (mem_properVertexAxisLine_iff .horizontal x z).2
            (hzAll ⟨h, hhA⟩ hzh)
        · intro hzLine
          rw [hFrontier]
          exact Set.mem_sUnion_of_mem
            (by rw [hsegment g₀]; exact
              hzInside ((mem_properVertexAxisLine_iff .horizontal x z).1 hzLine))
            g₀.2.1
  · intro u
    ext x
    let y : Tiling.Plane := -u + x
    have hxy : u + y = x := by dsimp only [y]; abel
    change IsProperVertex (u +ᵥ D) x ↔ x ∈ u +ᵥ properVertices D
    rw [mem_vadd_set_iff_neg_vadd_mem]
    change IsProperVertex (u +ᵥ D) x ↔ IsProperVertex D y
    change (x ∈ frontier (u +ᵥ D) ∧
        ¬Tiling.BoundaryLocallyStraightAt (u +ᵥ D) x) ↔
      y ∈ frontier D ∧ ¬Tiling.BoundaryLocallyStraightAt D y
    rw [frontier_vadd_eq]
    have hfrontier : x ∈ u +ᵥ frontier D ↔ y ∈ frontier D := by
      rw [mem_vadd_set_iff_neg_vadd_mem]
      rfl
    rw [hfrontier]
    have hstraight := boundaryLocallyStraightAt_vadd_iff u D y
    rw [hxy] at hstraight
    exact and_congr_right fun _ ↦ not_congr hstraight

/-- Near any point, the frontier of a locally axis-parallel polygonal set lies in the
coordinate cross through that point. -/
theorem exists_ball_frontier_subset_axisCross
    {F : Set Tiling.Plane}
    (hF : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F)
    (x : Tiling.Plane) :
    ∃ r > 0, ∀ z ∈ Metric.ball x r, z ∈ frontier F →
      z.re = x.re ∨ z.im = x.im := by
  obtain ⟨G, hSegments, hFrontier, hLocallyFinite⟩ := hF.2.2
  let Q : Set Tiling.Plane := Metric.closedBall x 1
  let A : Set (Set Tiling.Plane) := {g | g ∈ G ∧ (g ∩ Q).Nonempty}
  have hAFinite : A.Finite := hLocallyFinite Q Metric.isBounded_closedBall
  let Bad : Set (Set Tiling.Plane) := {g | g ∈ A ∧ x ∉ g}
  have hBadFinite : Bad.Finite := hAFinite.subset fun g hg => hg.1
  have hBadClosed : IsClosed (⋃ g ∈ Bad, g) := by
    apply hBadFinite.isClosed_biUnion
    intro g hg
    obtain ⟨p, q, _hpq, _haxis, rfl⟩ := hSegments g hg.1.1
    rw [segment_eq_image]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hxBad : x ∉ ⋃ g ∈ Bad, g := by
    intro hx
    simp only [mem_iUnion] at hx
    obtain ⟨g, hgBad, hxg⟩ := hx
    exact hgBad.2 hxg
  have hEventually : ∀ᶠ z in 𝓝 x,
      z ∈ Metric.ball x 1 ∧ z ∉ ⋃ g ∈ Bad, g :=
    inter_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
      (hBadClosed.isOpen_compl.mem_nhds hxBad)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hEventually
  refine ⟨r, hr, fun z hzBall hzFrontier => ?_⟩
  have hzNear := hball hzBall
  rw [hFrontier] at hzFrontier
  obtain ⟨g, hgG, hzg⟩ := mem_sUnion.mp hzFrontier
  have hzQ : z ∈ Q := Metric.ball_subset_closedBall hzNear.1
  have hgA : g ∈ A := ⟨hgG, ⟨z, hzg, hzQ⟩⟩
  have hxg : x ∈ g := by
    by_contra hxg
    have hgBad : g ∈ Bad := ⟨hgA, hxg⟩
    exact hzNear.2 (mem_iUnion_of_mem g (mem_iUnion_of_mem hgBad hzg))
  obtain ⟨p, q, _hpq, hpqAxis, hg⟩ := hSegments g hgG
  rw [hg] at hxg hzg
  rcases hpqAxis with hpqRe | hpqIm
  · left
    have hRe {w : Tiling.Plane} (hw : w ∈ segment ℝ p q) : w.re = p.re := by
      rw [segment_eq_image] at hw
      obtain ⟨c, _hc, rfl⟩ := hw
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
      rw [hpqRe]
      ring
    exact (hRe hzg).trans (hRe hxg).symm
  · right
    have hIm {w : Tiling.Plane} (hw : w ∈ segment ℝ p q) : w.im = p.im := by
      rw [segment_eq_image] at hw
      obtain ⟨c, _hc, rfl⟩ := hw
      simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      rw [hpqIm]
      ring
    exact (hIm hzg).trans (hIm hxg).symm

/-- Translating a finite-local-complexity set preserves finite local complexity. -/
theorem HasFLC.vadd
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S : Set E} (hS : HasFLC S) (u : E) : HasFLC (u +ᵥ S) := by
  refine ⟨?_, ?_⟩
  · intro Q hQ
    have hfinite := hS.1 ((-u) +ᵥ Q) (hQ.vadd (-u))
    apply (hfinite.image fun s ↦ u + s).subset
    rintro x ⟨hxS, hxQ⟩
    obtain ⟨s, hs, rfl⟩ := hxS
    refine ⟨s, ⟨hs, ?_⟩, rfl⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add] using hxQ
  · have hdif : (u +ᵥ S) - (u +ᵥ S) = S - S := by
      ext x
      constructor
      · rintro ⟨a, ⟨s, hs, rfl⟩, b, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨s, hs, t, ht, by
          change s - t = (u + s) - (u + t)
          abel⟩
      · rintro ⟨s, hs, t, ht, rfl⟩
        exact ⟨u + s, ⟨s, hs, rfl⟩, u + t, ⟨t, ht, rfl⟩, by
          change (u + s) - (u + t) = s - t
          abel⟩
    rw [hdif]
    exact hS.2

/-- Finite local complexity supplies a uniform separation radius. -/
theorem HasFLC.uniformlyDiscrete
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S : Set E} (hS : HasFLC S) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s ∈ S, ∀ t ∈ S, s ≠ t → delta ≤ dist s t := by
  let D : Set E := ((S - S) ∩ Metric.closedBall 0 1) \ {0}
  have hDfinite : D.Finite := (hS.2 1 one_pos).subset sdiff_subset
  have h0D : (0 : E) ∉ D := by simp [D]
  have hnhds : Dᶜ ∈ 𝓝 (0 : E) :=
    hDfinite.isClosed.isOpen_compl.mem_nhds h0D
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let delta := min r 1
  have hdelta : 0 < delta := lt_min hr one_pos
  refine ⟨delta, hdelta, ?_⟩
  intro s hs t ht hst
  by_contra hdist
  have hdist_lt : dist s t < delta := lt_of_not_ge hdist
  let d := s - t
  have hdne : d ≠ 0 := sub_ne_zero.mpr hst
  have hdmem : d ∈ S - S := ⟨s, hs, t, ht, rfl⟩
  have hdnorm : ‖d‖ = dist s t := by
    simp [d, dist_eq_norm]
  have hdclosed : d ∈ Metric.closedBall (0 : E) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hdnorm]
    exact hdist_lt.le.trans (min_le_right _ _)
  have hdD : d ∈ D := ⟨⟨hdmem, hdclosed⟩, by simpa using hdne⟩
  have hdball : d ∈ Metric.ball (0 : E) r := by
    rw [Metric.mem_ball, dist_zero_right, hdnorm]
    exact hdist_lt.trans_le (min_le_left _ _)
  exact (hball hdball) hdD

private theorem HasFLC.differences_locallyFinite
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S : Set E} (hS : HasFLC S) :
    ∀ Q : Set E, Bornology.IsBounded Q → ((S - S) ∩ Q).Finite := by
  intro Q hQ
  obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : E)
  let R' := max R 0 + 1
  have hR' : 0 < R' := by dsimp [R']; linarith [le_max_right R 0]
  apply (hS.2 R' hR').subset
  exact inter_subset_inter_right _
    (hR.trans (Metric.closedBall_subset_closedBall (by
      dsimp [R']
      linarith [le_max_left R 0])))

private theorem finite_inter_add_finset
    {E : Type*} [NormedAddCommGroup E]
    {A : Set E}
    (hA : ∀ Q : Set E, Bornology.IsBounded Q → (A ∩ Q).Finite)
    (F : Finset E) (Q : Set E) (hQ : Bornology.IsBounded Q) :
    ((A + (F : Set E)) ∩ Q).Finite := by
  have hadd : A + (F : Set E) = ⋃ f : (F : Set E), (f : E) +ᵥ A := by
    ext x
    constructor
    · rintro ⟨a, ha, f, hf, rfl⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨f, hf⟩, a, ha, by simp [vadd_eq_add, add_comm]⟩
    · rw [Set.mem_iUnion]
      rintro ⟨f, a, ha, rfl⟩
      exact ⟨a, ha, f, f.2, by simp [vadd_eq_add, add_comm]⟩
  rw [hadd, iUnion_inter]
  apply Set.finite_iUnion
  intro f
  have hfinite := hA ((-(f : E)) +ᵥ Q) (hQ.vadd (-(f : E)))
  apply (hfinite.image fun a ↦ (f : E) + a).subset
  rintro x ⟨⟨a, ha, rfl⟩, hxaQ⟩
  refine ⟨a, ⟨ha, ?_⟩, rfl⟩
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simpa [vadd_eq_add] using hxaQ

/-- Adding finitely many offsets preserves finite local complexity. -/
theorem HasFLC.add_finset
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S : Set E} (hS : HasFLC S) (F : Finset E) :
    HasFLC (S + (F : Set E)) := by
  classical
  refine ⟨fun Q hQ ↦ finite_inter_add_finset hS.1 F Q hQ, ?_⟩
  intro R hR
  let G : Finset E := F.image₂ (· - ·) F
  have hsubset :
      (S + (F : Set E)) - (S + (F : Set E)) ⊆ (S - S) + (G : Set E) := by
    rintro x ⟨a, ⟨s, hs, f, hf, rfl⟩, b, ⟨t, ht, g, hg, rfl⟩, rfl⟩
    refine ⟨s - t, ⟨s, hs, t, ht, rfl⟩, f - g, ?_, ?_⟩
    · exact Finset.mem_image₂.mpr ⟨f, hf, g, hg, rfl⟩
    · change (s - t) + (f - g) = (s + f) - (t + g)
      abel
  apply (finite_inter_add_finset
    (hS.differences_locallyFinite) G (Metric.closedBall 0 R)
      Metric.isBounded_closedBall).subset
  exact inter_subset_inter_left _ hsubset

/-- Regularized placement support commutes with translation. -/
theorem regularSupport_vadd
    (K : Region) (S : Set Tiling.Plane) (u : Tiling.Plane) :
    regularSupport K (u +ᵥ S) = u +ᵥ regularSupport K S := by
  have hopen : openUnion K (u +ᵥ S) = u +ᵥ openUnion K S := by
    ext x
    constructor
    · rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion]
      rintro ⟨s, hx⟩
      obtain ⟨t, ht, hst⟩ := s.2
      rw [← hst] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨t + k, ?_, by simp [vadd_eq_add, add_assoc]⟩
      rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion]
      exact ⟨⟨t, ht⟩, k, hk, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion] at hy ⊢
      obtain ⟨t, k, hk, rfl⟩ := hy
      exact ⟨⟨u + t, ⟨t, t.2, rfl⟩⟩, k, hk, by
        simp only [vadd_eq_add]
        abel⟩
  rw [regularSupport, regularSupport, Tiling.Polygonal.regularSupport,
    Tiling.Polygonal.regularSupport, ← openUnion, ← openUnion, hopen,
    closure_vadd, interior_vadd]

/-- A vertically invariant planar set is exactly the pullback of a set of real parts. -/
theorem verticalInvariant_iff_product (D : Set Tiling.Plane) :
    (∀ a : ℝ, ((a : ℂ) * Complex.I) +ᵥ D = D) ↔
      ∃ X : Set ℝ, D = {z : Tiling.Plane | z.re ∈ X} := by
  constructor
  · intro h
    refine ⟨{r : ℝ | (r : ℂ) ∈ D}, ?_⟩
    ext z
    constructor
    · intro hz
      change (z.re : ℂ) ∈ D
      have hz' : (((-z.im : ℝ) : ℂ) * Complex.I) + z ∈ D := by
        rw [← h (-z.im)]
        exact ⟨z, hz, rfl⟩
      convert hz' using 1
      apply Complex.ext <;> simp
    · intro hz
      change (z.re : ℂ) ∈ D at hz
      rw [← h z.im]
      refine ⟨(z.re : ℂ), hz, ?_⟩
      apply Complex.ext <;> simp
  · rintro ⟨X, rfl⟩ a
    ext z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_ofPred_eq, vadd_eq_add]
    simp

/-- A horizontally invariant planar set is exactly the pullback of a set of imaginary parts. -/
theorem horizontalInvariant_iff_product (D : Set Tiling.Plane) :
    (∀ a : ℝ, (a : ℂ) +ᵥ D = D) ↔
      ∃ X : Set ℝ, D = {z : Tiling.Plane | z.im ∈ X} := by
  constructor
  · intro h
    refine ⟨{r : ℝ | (r : ℂ) * Complex.I ∈ D}, ?_⟩
    ext z
    constructor
    · intro hz
      change ((z.im : ℂ) * Complex.I) ∈ D
      have hz' : ((-z.re : ℝ) : ℂ) + z ∈ D := by
        rw [← h (-z.re)]
        exact ⟨z, hz, rfl⟩
      convert hz' using 1
      apply Complex.ext <;> simp
    · intro hz
      change ((z.im : ℂ) * Complex.I) ∈ D at hz
      rw [← h z.re]
      refine ⟨(z.im : ℂ) * Complex.I, hz, ?_⟩
      apply Complex.ext <;> simp
  · rintro ⟨X, rfl⟩ a
    ext z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_ofPred_eq, vadd_eq_add]
    simp

/-- Centres on one affine axis line have bounded transverse regular-support projection. -/
theorem regularSupportTransverseProjection_bounded :
    ∀ (axis : Axis) {K : Region} {S : Set Tiling.Plane},
      (∃ c : ℝ, ∀ s ∈ S, axis.transverseCoord s = c) →
      Bornology.IsBounded
        (axis.transverseCoord '' regularSupport K S) := by
  intro axis K S halign
  obtain ⟨c, hc⟩ := halign
  have hcoord : Bornology.IsBounded (axis.transverseCoord '' K.support) := by
    cases axis <;> simp only [Axis.transverseCoord]
    · exact K.isPolygonal.isBounded.image Complex.imCLM
    · exact K.isPolygonal.isBounded.image Complex.reCLM
  obtain ⟨R, hR⟩ := hcoord.subset_closedBall 0
  let B : Set ℝ := Metric.closedBall c R
  have hopen : openUnion K S ⊆ axis.transverseCoord ⁻¹' B := by
    intro x hx
    rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion] at hx
    obtain ⟨s, hs⟩ := hx
    rcases hs with ⟨y, hy, rfl⟩
    have hyK : y ∈ K.support := interior_subset hy
    have hyR := hR ⟨y, hyK, rfl⟩
    have hsum : axis.transverseCoord ((s : Tiling.Plane) + y) =
        c + axis.transverseCoord y := by
      have hsc := hc (s : Tiling.Plane) s.2
      cases axis <;> simp only [Axis.transverseCoord, Complex.add_im,
        Complex.add_re] at *
      · simp [hsc]
      · simp [hsc]
    change axis.transverseCoord ((s : Tiling.Plane) + y) ∈ B
    rw [hsum, Metric.mem_closedBall]
    have hyR' : |axis.transverseCoord y| ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hyR
    simpa [Real.dist_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hyR'
  have hclosed : IsClosed (axis.transverseCoord ⁻¹' B) := by
    cases axis <;> simp only [Axis.transverseCoord]
    · exact (Metric.isClosed_closedBall.preimage Complex.continuous_im)
    · exact (Metric.isClosed_closedBall.preimage Complex.continuous_re)
  have hclosure :
      closure (openUnion K S) ⊆ axis.transverseCoord ⁻¹' B :=
    closure_minimal hopen hclosed
  apply Bornology.IsBounded.subset
    (Metric.isBounded_closedBall (x := c) (r := R))
  rintro z ⟨x, hx, rfl⟩
  exact hclosure (interior_subset hx)

private theorem transverseCoord_image_openUnion
    {K : Region} {C : Set Tiling.Plane} {axis : Axis} {c : ℝ}
    (hC : C.Nonempty)
    (hcoord : ∀ z ∈ C, axis.transverseCoord z = c) :
    axis.transverseCoord '' openUnion K C =
      c +ᵥ (axis.transverseCoord '' K.openCarrier) := by
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion] at hz
    obtain ⟨s, hs⟩ := hz
    obtain ⟨k, hk, rfl⟩ := hs
    refine ⟨axis.transverseCoord k, ⟨k, hk, rfl⟩, ?_⟩
    cases axis
    · simpa [Axis.transverseCoord] using (hcoord s s.2).symm
    · simpa [Axis.transverseCoord] using (hcoord s s.2).symm
  · rintro ⟨r, ⟨k, hk, rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ := hC
    refine ⟨s + k, ?_, ?_⟩
    · rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion]
      exact ⟨⟨s, hs⟩, ⟨k, hk, rfl⟩⟩
    · cases axis
      · simpa [Axis.transverseCoord] using hcoord s hs
      · simpa [Axis.transverseCoord] using hcoord s hs

/-- The regular support of a complete centre column is the regularized
one-dimensional projection of the tile, pulled back along the transverse
coordinate. -/
theorem centerColumn_regularSupport
    {K : Region} {C : Set Tiling.Plane} {axis : Axis}
    (hC : IsCenterColumn axis K C) :
    ∃ c : ℝ,
      C.Nonempty ∧ (∀ z ∈ C, axis.transverseCoord z = c) ∧
      regularSupport K C =
        {z : Tiling.Plane |
          axis.transverseCoord z ∈
            interior (closure (c +ᵥ (axis.transverseCoord '' K.openCarrier)))} := by
  rcases hC with ⟨_hpacking, hnonempty, ⟨c, hcoord⟩, hinvariant⟩
  refine ⟨c, hnonempty, hcoord, ?_⟩
  let U := openUnion K C
  let B := c +ᵥ (axis.transverseCoord '' K.openCarrier)
  have himage : axis.transverseCoord '' U = B :=
    transverseCoord_image_openUnion hnonempty hcoord
  have hUopen : IsOpen U := by
    dsimp only [U, openUnion]
    exact isOpen_iUnion fun s ↦
      (Region.openCarrier_regularOpen K).1.vadd (s : Tiling.Plane)
  have hUsub : U ⊆ regularSupport K C := by
    change U ⊆ interior (closure U)
    calc
      U = interior U := hUopen.interior_eq.symm
      _ ⊆ interior (closure U) := interior_mono subset_closure
  cases axis with
  | vertical =>
      obtain ⟨X, hsupport⟩ :=
        (verticalInvariant_iff_product (regularSupport K C)).mp hinvariant
      change regularSupport K C = Complex.re ⁻¹' X at hsupport
      have hXregular : interior (closure X) = X := by
        have hpre : Complex.re ⁻¹' interior (closure X) = Complex.re ⁻¹' X := by
          calc
            Complex.re ⁻¹' interior (closure X) =
                interior (Complex.re ⁻¹' closure X) :=
              (Complex.interior_preimage_re _).symm
            _ = interior (closure (Complex.re ⁻¹' X)) := by
              rw [Complex.closure_preimage_re]
            _ = interior (closure (regularSupport K C)) := by rw [hsupport]
            _ = regularSupport K C := (regularSupport_isRegularOpen K C).2
            _ = Complex.re ⁻¹' X := hsupport
        apply (Set.preimage_injective.mpr ?_) hpre
        intro r
        exact ⟨(r : ℂ), rfl⟩
      have hBX : B ⊆ X := by
        intro r hr
        rw [← himage] at hr
        obtain ⟨z, hzU, hzr⟩ := hr
        have hzR := hUsub hzU
        rw [hsupport] at hzR
        change z.re ∈ X at hzR
        change r ∈ X
        rwa [← hzr]
      have hXB : X ⊆ closure B := by
        intro r hr
        have hzR : (r : ℂ) ∈ regularSupport K C := by
          rw [hsupport]
          exact hr
        have hzClosure : (r : ℂ) ∈ closure U :=
          interior_subset hzR
        have hrImage : r ∈ Complex.re '' closure U :=
          ⟨(r : ℂ), hzClosure, rfl⟩
        have := image_closure_subset_closure_image Complex.continuous_re hrImage
        change Complex.re '' U = B at himage
        rw [himage] at this
        exact this
      have hXopen : IsOpen X := by
        rw [← hXregular]
        exact isOpen_interior
      have hXBint : X ⊆ interior (closure B) := interior_maximal hXB hXopen
      have hBintX : interior (closure B) ⊆ X := by
        rw [← hXregular]
        exact interior_mono (closure_mono hBX)
      have hXeq : X = interior (closure B) :=
        Set.Subset.antisymm hXBint hBintX
      rw [hsupport, hXeq]
      rfl
  | horizontal =>
      obtain ⟨X, hsupport⟩ :=
        (horizontalInvariant_iff_product (regularSupport K C)).mp hinvariant
      change regularSupport K C = Complex.im ⁻¹' X at hsupport
      have hXregular : interior (closure X) = X := by
        have hpre : Complex.im ⁻¹' interior (closure X) = Complex.im ⁻¹' X := by
          calc
            Complex.im ⁻¹' interior (closure X) =
                interior (Complex.im ⁻¹' closure X) :=
              (Complex.interior_preimage_im _).symm
            _ = interior (closure (Complex.im ⁻¹' X)) := by
              rw [Complex.closure_preimage_im]
            _ = interior (closure (regularSupport K C)) := by rw [hsupport]
            _ = regularSupport K C := (regularSupport_isRegularOpen K C).2
            _ = Complex.im ⁻¹' X := hsupport
        apply (Set.preimage_injective.mpr ?_) hpre
        intro r
        exact ⟨(r : ℂ) * Complex.I, by simp⟩
      have hBX : B ⊆ X := by
        intro r hr
        rw [← himage] at hr
        obtain ⟨z, hzU, hzr⟩ := hr
        have hzR := hUsub hzU
        rw [hsupport] at hzR
        change z.im ∈ X at hzR
        change r ∈ X
        rwa [← hzr]
      have hXB : X ⊆ closure B := by
        intro r hr
        have hzR : (r : ℂ) * Complex.I ∈ regularSupport K C := by
          rw [hsupport]
          simpa using hr
        have hzClosure : (r : ℂ) * Complex.I ∈ closure U :=
          interior_subset hzR
        have hrImage : r ∈ Complex.im '' closure U :=
          ⟨(r : ℂ) * Complex.I, hzClosure, by simp⟩
        have := image_closure_subset_closure_image Complex.continuous_im hrImage
        change Complex.im '' U = B at himage
        rw [himage] at this
        exact this
      have hXopen : IsOpen X := by
        rw [← hXregular]
        exact isOpen_interior
      have hXBint : X ⊆ interior (closure B) := interior_maximal hXB hXopen
      have hBintX : interior (closure B) ⊆ X := by
        rw [← hXregular]
        exact interior_mono (closure_mono hBX)
      have hXeq : X = interior (closure B) :=
        Set.Subset.antisymm hXBint hBintX
      rw [hsupport, hXeq]
      rfl

/-- On a regular-open carrier, almost-everywhere and literal periods coincide. -/
theorem aePeriodGroup_eq_periodGroup_of_regularOpen
    {S : Set Tiling.Plane} (hopen : IsOpen S)
    (hregular : interior (closure S) = S) :
    aePeriodGroup S = periodGroup S := by
  ext u
  change (u +ᵥ S =ᵐ[MeasureTheory.volume] S) ↔ u +ᵥ S = S
  constructor
  · intro hu
    apply regularOpen_eq_of_aeEq (hopen.vadd u) _ hopen hregular hu
    rw [closure_vadd, interior_vadd, hregular]
  · intro hu
    rw [hu]
    exact Filter.EventuallyEq.rfl

private theorem add_vadd_set (a b : Tiling.Plane) (S : Set Tiling.Plane) :
    a +ᵥ (b +ᵥ S) = (a + b) +ᵥ S := by
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  constructor <;> intro hx
  · convert hx using 1
    abel_nf
  · convert hx using 1
    abel_nf

/-- Translating both the centre set and target preserves a tiling-on relation. -/
theorem tilesOn_translate
    {K : Region} {S D : Set Tiling.Plane}
    (hTile : TilesOn K S D) (u : Tiling.Plane) :
    TilesOn K (u +ᵥ S) (u +ᵥ D) := by
  refine ⟨?_, ?_, ?_⟩
  · have hset : u +ᵥ S = (fun s : Tiling.Plane ↦ u + s) '' S := by
      ext x
      constructor
      · intro hx
        exact ⟨-u + x, by
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hx,
          by simp⟩
      · rintro ⟨s, hs, rfl⟩
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          neg_add_cancel_left] using hs
    rw [hset]
    exact hTile.1.image _
  · intro i hi j hj hij
    let i₀ : Tiling.Placement Tiling.Plane Unit := (-u + i.1, ())
    let j₀ : Tiling.Placement Tiling.Plane Unit := (-u + j.1, ())
    have hi₀ : i₀ ∈ K.toPolygonalRegion.placements S := by
      change -u + i.1 ∈ S
      change i.1 ∈ u +ᵥ S at hi
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hi
    have hj₀ : j₀ ∈ K.toPolygonalRegion.placements S := by
      change -u + j.1 ∈ S
      change j.1 ∈ u +ᵥ S at hj
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hj
    have hij₀ : i₀ ≠ j₀ := by
      intro heq
      apply hij
      apply Prod.ext
      · have heq' := congrArg Prod.fst heq
        dsimp only [i₀, j₀] at heq'
        have := congrArg (fun z : Tiling.Plane ↦ u + z) heq'
        simpa only [add_assoc, add_neg_cancel_left] using this
      · exact Subsingleton.elim _ _
    have hd := hTile.2.1 hi₀ hj₀ hij₀
    have hd' := Tiling.aedisjoint_vadd u hd
    have hiTile : u +ᵥ ((-u + i.1) +ᵥ K.support) = i.1 +ᵥ K.support := by
      rw [add_vadd_set]
      congr 1
      abel
    have hjTile : u +ᵥ ((-u + j.1) +ᵥ K.support) = j.1 +ᵥ K.support := by
      rw [add_vadd_set]
      congr 1
      abel
    change MeasureTheory.AEDisjoint MeasureTheory.volume
      (i.1 +ᵥ K.support) (j.1 +ᵥ K.support)
    rw [← hiTile, ← hjTile]
    exact hd'
  · have hpull :=
      (MeasureTheory.quasiMeasurePreserving_add_left MeasureTheory.volume (-u)).ae hTile.2.2
    filter_upwards [hpull] with x hx
    have htarget : x ∈ u +ᵥ D ↔ -u + x ∈ D := by
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    have hunion :
        (∃ s : u +ᵥ S, x ∈ ((s : Tiling.Plane) +ᵥ K.openCarrier)) ↔
          ∃ s : S, -u + x ∈ ((s : Tiling.Plane) +ᵥ K.openCarrier) := by
      constructor
      · rintro ⟨s, hsx⟩
        let s₀ : S := ⟨-u + s.1, by
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using s.2⟩
        refine ⟨s₀, ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsx ⊢
        convert hsx using 1
        all_goals simp only [s₀, vadd_eq_add]
        all_goals abel
      · rintro ⟨s, hsx⟩
        let s' : u +ᵥ S := ⟨u + s.1, by
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
            neg_add_cancel_left] using s.2⟩
        refine ⟨s', ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsx ⊢
        convert hsx using 1
        all_goals simp only [s', vadd_eq_add]
        all_goals abel
    exact htarget.trans (hx.trans hunion.symm)

private def coordinateSwapIsometry : Tiling.Plane ≃ₗᵢ[ℝ] Tiling.Plane where
  toLinearEquiv := coordinateSwap.toLinearEquiv
  norm_map' z := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring

private theorem coordinateSwap_image_eq_preimage' (A : Set Tiling.Plane) :
    coordinateSwap '' A = coordinateSwap ⁻¹' A := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨coordinateSwap z, hz, coordinateSwap_apply_apply z⟩

theorem coordinateSwap_image_vadd
    (u : Tiling.Plane) (A : Set Tiling.Plane) :
    coordinateSwap '' (u +ᵥ A) =
      coordinateSwap u +ᵥ (coordinateSwap '' A) := by
  ext z
  constructor
  · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨coordinateSwap a, ⟨a, ha, rfl⟩, ?_⟩
    exact coordinateSwap.map_add u a
  · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨u + a, ⟨a, ha, rfl⟩, ?_⟩
    exact coordinateSwap.map_add u a

theorem coordinateSwap_openCarrier (K : Region) :
    K.coordinateSwap.openCarrier = coordinateSwap '' K.openCarrier := by
  change interior (coordinateSwap '' K.support) =
    coordinateSwap '' interior K.support
  exact (coordinateSwap.toHomeomorph.image_interior K.support).symm

/-- Coordinate interchange commutes with regularizing a union of translated carriers. -/
theorem regularSupport_coordinateSwap (K : Region) (Q : Set Tiling.Plane) :
    regularSupport K.coordinateSwap (coordinateSwap '' Q) =
      coordinateSwap '' regularSupport K Q := by
  have hopen :
      openUnion K.coordinateSwap (coordinateSwap '' Q) =
        coordinateSwap '' openUnion K Q := by
    ext z
    constructor
    · rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      rintro ⟨q, hz⟩
      obtain ⟨q₀, hq₀, hq⟩ := q.2
      rw [coordinateSwap_openCarrier, ← hq,
        ← coordinateSwap_image_vadd] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      refine ⟨w, ?_, rfl⟩
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      exact ⟨⟨q₀, hq₀⟩, hw⟩
    · rintro ⟨w, hw, rfl⟩
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hw ⊢
      obtain ⟨q, hw⟩ := hw
      let q' : coordinateSwap '' Q :=
        ⟨coordinateSwap q, ⟨q, q.2, rfl⟩⟩
      refine ⟨q', ?_⟩
      rw [coordinateSwap_openCarrier, ← coordinateSwap_image_vadd]
      exact ⟨w, hw, rfl⟩
  rw [regularSupport, regularSupport, Tiling.Polygonal.regularSupport,
    Tiling.Polygonal.regularSupport, ← openUnion, ← openUnion, hopen]
  change interior (closure (coordinateSwap.toHomeomorph '' openUnion K Q)) =
    coordinateSwap.toHomeomorph '' interior (closure (openUnion K Q))
  rw [← coordinateSwap.toHomeomorph.image_closure]
  exact (coordinateSwap.toHomeomorph.image_interior _).symm

/-- Swapping both coordinates transports a target-relative tiling exactly. -/
theorem tilesOn_coordinateSwap
    {K : Region} {S D : Set Tiling.Plane}
    (hTile : TilesOn K S D) :
    TilesOn K.coordinateSwap (coordinateSwap '' S) (coordinateSwap '' D) := by
  refine ⟨hTile.1.image coordinateSwap, ?_, ?_⟩
  · intro p hp q hq hpq
    obtain ⟨s, hs, hps⟩ := hp
    obtain ⟨t, ht, hqt⟩ := hq
    have hst : s ≠ t := by
      intro hst
      apply hpq
      apply Prod.ext
      · calc
          p.1 = coordinateSwap s := hps.symm
          _ = coordinateSwap t := by rw [hst]
          _ = q.1 := hqt
      · exact Subsingleton.elim _ _
    let p₀ : Tiling.Placement Tiling.Plane Unit := (s, ())
    let q₀ : Tiling.Placement Tiling.Plane Unit := (t, ())
    have hp₀q₀ : p₀ ≠ q₀ := by
      intro hpq₀
      exact hst
        (congrArg (fun r : Tiling.Placement Tiling.Plane Unit ↦ r.1) hpq₀)
    have hd := hTile.2.1 hs ht hp₀q₀
    have hpre := hd.preimage
      coordinateSwapIsometry.measurePreserving.quasiMeasurePreserving
    change MeasureTheory.AEDisjoint MeasureTheory.volume
      (p.1 +ᵥ K.coordinateSwap.support)
      (q.1 +ᵥ K.coordinateSwap.support)
    rw [← hps, ← hqt]
    change MeasureTheory.AEDisjoint MeasureTheory.volume
      (coordinateSwap s +ᵥ (coordinateSwap '' K.support))
      (coordinateSwap t +ᵥ (coordinateSwap '' K.support))
    rw [← coordinateSwap_image_vadd, ← coordinateSwap_image_vadd]
    rw [coordinateSwap_image_eq_preimage', coordinateSwap_image_eq_preimage']
    exact hpre
  · have hpull :=
      coordinateSwapIsometry.measurePreserving.quasiMeasurePreserving.ae hTile.2.2
    filter_upwards [hpull] with x hx
    constructor
    · intro hxD
      obtain ⟨d, hd, hdx⟩ := hxD
      have hswapD : coordinateSwap x ∈ D := by
        rw [← hdx]
        simpa using hd
      obtain ⟨s, hsx⟩ := hx.mp hswapD
      let s' : coordinateSwap '' S :=
        ⟨coordinateSwap s, ⟨s, s.2, rfl⟩⟩
      refine ⟨s', ?_⟩
      change x ∈ (s' : Tiling.Plane) +ᵥ K.coordinateSwap.openCarrier
      rw [coordinateSwap_openCarrier]
      rw [← coordinateSwap_image_vadd]
      exact ⟨coordinateSwap x, hsx, coordinateSwap_apply_apply x⟩
    · rintro ⟨s', hsx⟩
      obtain ⟨s, hs, hss'⟩ := s'.2
      change x ∈ (s' : Tiling.Plane) +ᵥ K.coordinateSwap.openCarrier at hsx
      rw [coordinateSwap_openCarrier, ← hss',
        ← coordinateSwap_image_vadd] at hsx
      obtain ⟨y, hy, hxy⟩ := hsx
      have hy' : coordinateSwap x ∈ (s : Tiling.Plane) +ᵥ K.openCarrier := by
        have hswap : coordinateSwap x = y := by
          rw [← hxy]
          exact coordinateSwap_apply_apply y
        rw [hswap]
        exact hy
      have hxD : coordinateSwap x ∈ D := hx.mpr ⟨⟨s, hs⟩, hy'⟩
      exact ⟨coordinateSwap x, hxD, coordinateSwap_apply_apply x⟩

theorem setPeriodicBy_iff_vadd_eq
    (S : Set Tiling.Plane) (u : Tiling.Plane) :
    Tiling.RationalPolygonal.SetPeriodicBy S u ↔ u +ᵥ S = S := by
  constructor
  · intro h
    ext x
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    simpa [add_comm, add_left_comm, add_assoc] using (h (-u + x)).symm
  · intro h x
    have hx := Set.ext_iff.mp h (x + u)
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      add_comm, add_left_comm, add_assoc] using hx.symm

theorem coordinateSwap_periodGroup :
    ∀ {S : Set Tiling.Plane} {p : Tiling.Plane},
      p ∈ periodGroup S →
        coordinateSwap p ∈ periodGroup (coordinateSwap '' S) := by
  intro S p hp
  apply (periodGroup_isAddSubgroup (coordinateSwap '' S) (coordinateSwap p)).mpr
  rw [← Tiling.AxisParallel.coordinateSwap_image_vadd]
  rw [(periodGroup_isAddSubgroup S p).mp hp]

theorem coordinateSwap_weaklyPeriodic :
    ∀ {S : Set Tiling.Plane},
      Tiling.RationalPolygonal.WeaklyPeriodic S →
        Tiling.RationalPolygonal.WeaklyPeriodic (coordinateSwap '' S) := by
  rintro S ⟨D⟩
  refine ⟨{
    numberOfParts := D.numberOfParts
    part := fun i ↦ coordinateSwap '' D.part i
    period := fun i ↦ coordinateSwap (D.period i)
    period_ne_zero := ?_
    periodic_part := ?_
    pairwiseDisjoint := ?_
    iUnion_parts := ?_ }⟩
  · intro i hi
    apply D.period_ne_zero i
    apply coordinateSwap.injective
    simpa using hi
  · intro i
    apply (Tiling.AxisParallel.setPeriodicBy_iff_vadd_eq _ _).mpr
    rw [← Tiling.AxisParallel.coordinateSwap_image_vadd]
    rw [(Tiling.AxisParallel.setPeriodicBy_iff_vadd_eq _ _).mp (D.periodic_part i)]
  · intro i hi j hj hij
    refine Set.disjoint_left.2 ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hzy⟩
    have hxy : x = y := coordinateSwap.injective hzy.symm
    exact Set.disjoint_left.mp (D.pairwiseDisjoint (by simp) (by simp) hij) hx
      (hxy ▸ hy)
  · ext z
    have hunion : (⋃ i, D.part i) = S := D.iUnion_parts
    have hsub : (⋃ i, D.part i) ⊆ S := by
      rw [hunion]
    have hsub' : S ⊆ ⋃ i, D.part i := by
      rw [hunion]
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨x, hx, hzx⟩ := hi
      refine ⟨x, ?_, hzx⟩
      exact hsub (Set.mem_iUnion.mpr ⟨i, hx⟩)
    · rintro ⟨x, hx, hzx⟩
      have hx' : x ∈ ⋃ i, D.part i := hsub' hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
      exact Set.mem_iUnion.mpr ⟨i, ⟨x, hi, hzx⟩⟩

theorem coordinateSwap_latticePeriodic :
    ∀ {S : Set Tiling.Plane},
      IsLatticePeriodic S → IsLatticePeriodic (coordinateSwap '' S) := by
  rintro S ⟨L, hL⟩
  let Lσ : PlanarLattice := {
    basis := fun i ↦ coordinateSwap (L.basis i)
    independent := L.independent.map' coordinateSwap.toLinearMap coordinateSwap.ker }
  refine ⟨Lσ, ?_⟩
  intro z hz
  refine AddSubgroup.closure_induction (p := fun z _ ↦ z ∈ periodGroup (coordinateSwap '' S))
    ?_ ?_ ?_ ?_ hz
  · rintro z ⟨i, rfl⟩
    apply (periodGroup_isAddSubgroup (coordinateSwap '' S) (coordinateSwap (L.basis i))).mpr
    rw [← Tiling.AxisParallel.coordinateSwap_image_vadd]
    rw [(periodGroup_isAddSubgroup S (L.basis i)).mp
      (hL (AddSubgroup.subset_closure (Set.mem_range_self i)))]
  · exact (periodGroup (coordinateSwap '' S)).zero_mem
  · intro a b ha hb hpa hpb
    exact (periodGroup (coordinateSwap '' S)).add_mem hpa hpb
  · intro a ha hpa
    exact (periodGroup (coordinateSwap '' S)).neg_mem hpa

theorem Region.coordinateSwap_involutive (K : Region) :
    K.coordinateSwap.coordinateSwap = K := by
  apply Region.eq_of_support_eq
  change Tiling.AxisParallel.coordinateSwap ''
    (Tiling.AxisParallel.coordinateSwap '' K.support) = K.support
  ext z
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    simpa using hu
  · intro hz
    exact ⟨Tiling.AxisParallel.coordinateSwap z, ⟨z, hz, rfl⟩,
      coordinateSwap_apply_apply z⟩

/-- The subgroup formulation of full-rank periodicity matches the existing two-period API. -/
theorem isLatticePeriodic_iff_doublyPeriodic (S : Set Tiling.Plane) :
    IsLatticePeriodic S ↔ Tiling.RationalPolygonal.DoublyPeriodic S := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨L.basis 0, L.basis 1, ?_, ?_, ?_⟩
    · have heq : ![L.basis 0, L.basis 1] = L.basis := by
        funext i
        fin_cases i <;> rfl
      rw [heq]
      exact L.independent
    · apply (setPeriodicBy_iff_vadd_eq S (L.basis 0)).mpr
      exact hL (AddSubgroup.subset_closure (Set.mem_range_self 0))
    · apply (setPeriodicBy_iff_vadd_eq S (L.basis 1)).mpr
      exact hL (AddSubgroup.subset_closure (Set.mem_range_self 1))
  · rintro ⟨h₁, h₂, hind, hp₁, hp₂⟩
    let L : PlanarLattice := {
      basis := ![h₁, h₂]
      independent := hind }
    refine ⟨L, ?_⟩
    apply (AddSubgroup.closure_le _).mpr
    rintro u ⟨i, rfl⟩
    fin_cases i
    · exact (setPeriodicBy_iff_vadd_eq S h₁).mp hp₁
    · exact (setPeriodicBy_iff_vadd_eq S h₂).mp hp₂

/-- A finite disjoint union of lattice-periodic pieces is weakly periodic. -/
theorem isQuasiPeriodic_weaklyPeriodic
    {S : Set Tiling.Plane} (hS : IsQuasiPeriodic S) :
    Tiling.RationalPolygonal.WeaklyPeriodic S := by
  rcases hS with ⟨n, part, hpart, hdisjoint, hunion⟩
  choose L hL using fun i ↦ (hpart i).2
  refine ⟨{
    numberOfParts := n
    part := part
    period := fun i ↦ (L i).basis 0
    period_ne_zero := ?_
    periodic_part := ?_
    pairwiseDisjoint := hdisjoint
    iUnion_parts := hunion }⟩
  · intro i
    exact (L i).independent.ne_zero 0
  · intro i
    apply (setPeriodicBy_iff_vadd_eq (part i) ((L i).basis 0)).mpr
    exact hL i (AddSubgroup.subset_closure (Set.mem_range_self 0))

end Tiling.AxisParallel


namespace Tiling.AxisParallel

universe u v

/-- Regularizing every member of an arbitrary open family before taking its union does not
change the regularization of the union. -/
theorem interior_closure_iUnion_interior_closure
    {X : Type u} [TopologicalSpace X] {I : Type v}
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) :
    interior (closure (⋃ i, U i)) =
      interior (closure (⋃ i, interior (closure (U i)))) := by
  have hforward : (⋃ i, U i) ⊆ ⋃ i, interior (closure (U i)) := by
    apply Set.iUnion_mono
    intro i
    exact (hU i).subset_interior_closure
  have hbackward : (⋃ i, interior (closure (U i))) ⊆ closure (⋃ i, U i) := by
    apply Set.iUnion_subset
    intro i
    exact interior_subset.trans
      (closure_mono (Set.subset_iUnion U i))
  have hclosure : closure (⋃ i, U i) =
      closure (⋃ i, interior (closure (U i))) := by
    apply Set.Subset.antisymm
    · exact closure_mono hforward
    · exact closure_minimal hbackward isClosed_closure
  rw [hclosure]

private theorem openUnion_iUnion
    {I : Type u} (K : Region) (S : I → Set Tiling.Plane) :
    openUnion K (⋃ i, S i) = ⋃ i, openUnion K (S i) := by
  ext x
  simp only [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨i, hsi⟩ := Set.mem_iUnion.mp s.2
    exact ⟨i, ⟨⟨s.1, hsi⟩, hs⟩⟩
  · rintro ⟨i, s, hs⟩
    exact ⟨⟨s.1, Set.mem_iUnion.mpr ⟨i, s.2⟩⟩, hs⟩

/-- The regular support of an arbitrary union is the regularized union of the individual
regular supports. -/
theorem regularSupport_iUnion
    {I : Type u} (K : Region) (S : I → Set Tiling.Plane) :
    regularSupport K (⋃ i, S i) =
      interior (closure (⋃ i, regularSupport K (S i))) := by
  have hopen (i : I) : IsOpen (openUnion K (S i)) := by
    apply isOpen_iUnion
    intro s
    change IsOpen ((Homeomorph.addLeft (s : Tiling.Plane)) '' K.openCarrier)
    exact (Homeomorph.addLeft (s : Tiling.Plane)).isOpenMap _ isOpen_interior
  rw [regularSupport, Tiling.Polygonal.regularSupport, ← openUnion, openUnion_iUnion]
  exact interior_closure_iUnion_interior_closure
    (fun i ↦ openUnion K (S i)) hopen

end Tiling.AxisParallel

open Filter Set Topology
open scoped Pointwise
namespace Tiling.AxisParallel

/-- Proper-vertex status depends only on membership at corresponding offsets. -/
theorem isProperVertex_iff_of_offset_germ
    {D E : Set Tiling.Plane} {x y : Tiling.Plane}
    (h : ∀ᶠ d in 𝓝 (0 : Tiling.Plane), (x + d ∈ D ↔ y + d ∈ E)) :
    IsProperVertex D x ↔ IsProperVertex E y := by
  let a : Tiling.Plane := y - x
  have hShift : Tendsto (fun z : Tiling.Plane => z - y) (𝓝 y)
      (𝓝 (0 : Tiling.Plane)) := by
    have hc : Tendsto (fun z : Tiling.Plane => z - y)
        (𝓝 y) (𝓝 (y - y)) :=
      ((continuous_id : Continuous fun z : Tiling.Plane => z).sub
        (continuous_const : Continuous fun _ : Tiling.Plane => y)).continuousAt
    simpa only [sub_self] using hc
  have hLocal : (a +ᵥ D) =ᶠ[𝓝 y] E := by
    filter_upwards [hShift.eventually h] with z hz
    apply propext
    change z ∈ a +ᵥ D ↔ z ∈ E
    rw [mem_vadd_set_iff_neg_vadd_mem]
    change -a + z ∈ D ↔ z ∈ E
    have hsource : -a + z = x + (z - y) := by dsimp [a]; abel
    have htarget : y + (z - y) = z := by abel
    rw [hsource]
    simpa only [htarget] using hz
  have hTranslate : IsProperVertex (a +ᵥ D) y ↔ IsProperVertex D x := by
    change y ∈ properVertices (a +ᵥ D) ↔ x ∈ properVertices D
    rw [properVertices_vadd_eq, mem_vadd_set_iff_neg_vadd_mem]
    change -a + y ∈ properVertices D ↔ x ∈ properVertices D
    have hsource : -a + y = x := by dsimp [a]; abel
    rw [hsource]
  exact hTranslate.symm.trans (isProperVertex_iff_of_eventuallyEq hLocal)

end Tiling.AxisParallel

namespace Tiling.AxisParallel

/-- A frontier point of a packed regularized union belongs to the frontier of
at least one translated tile.  This is deliberately a small interface over the
canonical packing closure identity; it does not duplicate its local-finiteness
proof. -/
private theorem regularSupport_frontier_subset_tileFrontiers
    {K : Region} {S : Set Tiling.Plane}
    (hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) :
    frontier (regularSupport K S) ⊆
      ⋃ s : S, (s : Tiling.Plane) +ᵥ frontier K.support := by
  intro z hz
  have hzcl : z ∈ closure (openUnion K S) := by
    have h := frontier_subset_closure hz
    exact closure_minimal interior_subset isClosed_closure h
  rw [closure_openUnion_eq_iUnion_support hpack] at hzcl
  obtain ⟨s, hs⟩ := mem_iUnion.mp hzcl
  have hznot : z ∉ regularSupport K S := by
    have hznotInterior : z ∉ interior (regularSupport K S) := hz.2
    simpa only [(regularSupport_isRegularOpen K S).1.interior_eq] using hznotInterior
  have hsnot : z ∉ (s : Tiling.Plane) +ᵥ K.openCarrier := by
    intro hzs
    apply hznot
    have hUopen : IsOpen (openUnion K S) := by
      change IsOpen (⋃ t : S, (t : Tiling.Plane) +ᵥ K.openCarrier)
      exact isOpen_iUnion (fun t =>
        ((Homeomorph.addLeft (t : Tiling.Plane)).isOpenMap _ isOpen_interior))
    apply hUopen.subset_interior_closure
    exact mem_iUnion.mpr ⟨s, hzs⟩
  rw [mem_iUnion]
  refine ⟨s, ?_⟩
  rw [← frontier_vadd_eq]
  rw [frontier, closure_vadd, interior_vadd]
  refine ⟨?_, ?_⟩
  · simpa only [K.isPolygonal.isClosed.closure_eq] using hs
  · change z ∉ (s : Tiling.Plane) +ᵥ interior K.support at hsnot
    exact hsnot

/-- Canonical intrinsic-edge incidence supplies a closed tile segment at every
frontier point, including intrinsic vertices. -/
private theorem region_frontier_mem_vertexSegment (K : Region)
    {x : Tiling.Plane} (hx : x ∈ frontier K.support) :
    ∃ v w : ↥K.vertices, v ≠ w ∧ x ∈ segment ℝ v.1 w.1 := by
  classical
  by_cases hv : x ∈ K.vertices
  · let v : ↥K.vertices := ⟨x, hv⟩
    obtain ⟨w, hne, _, _⟩ :=
      IntrinsicVertices.intrinsicVertex_incident_axisEdge K Axis.horizontal v
    refine ⟨v, w, ?_, ?_⟩
    · exact fun h => hne (congrArg Subtype.val h).symm
    · exact left_mem_segment ℝ _ _
  · obtain ⟨_, v, w, hne, _, hseg, _⟩ :=
      IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge K x hx hv
    exact ⟨v, w, fun h => hne (congrArg Subtype.val h),
      openSegment_subset_segment ℝ _ _ hseg⟩

/-- The translated version is the sole polygonal geometry needed to turn the
frontier cover into a tile-segment cover. -/
private theorem tileFrontier_mem_translatedVertexSegment (K : Region)
    (s x : Tiling.Plane) (hx : x ∈ s +ᵥ frontier K.support) :
    ∃ v w : ↥K.vertices, v ≠ w ∧
      x ∈ segment ℝ (v.1 + s) (w.1 + s) := by
  obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hx
  obtain ⟨v, w, hne, hyseg⟩ := region_frontier_mem_vertexSegment K hy
  refine ⟨v, w, hne, ?_⟩
  have h : s +ᵥ y ∈ s +ᵥ segment ℝ v.1 w.1 :=
    Set.vadd_mem_vadd_set hyseg
  rw [vadd_segment] at h
  simpa only [vadd_eq_add, add_comm] using h

/-- Every packed regular-support frontier point is on a translated intrinsic
vertex-pair segment.  This is a consequence of the two small interfaces above,
not an independent support or local-frontier kernel. -/
theorem regularSupport_frontier_mem_translatedVertexSegment
    {K : Region} {S : Set Tiling.Plane}
    (hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    {x : Tiling.Plane} (hx : x ∈ frontier (regularSupport K S)) :
    ∃ (s : S) (v w : ↥K.vertices), v ≠ w ∧
      x ∈ segment ℝ (v.1 + s.1) (w.1 + s.1) := by
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp
    (regularSupport_frontier_subset_tileFrontiers hpack hx)
  obtain ⟨v, w, hne, hmem⟩ :=
    tileFrontier_mem_translatedVertexSegment K s.1 x hs
  exact ⟨s, v, w, hne, hmem⟩

end Tiling.AxisParallel

open Function
namespace Tiling.AxisParallel
private noncomputable def Region.vadd (K : Region) (a : Tiling.Plane) : Region where
  support := a +ᵥ K.support
  isPolygonal := K.isPolygonal.vadd a
  nonempty := by
    obtain ⟨x, hx⟩ := K.nonempty
    exact ⟨a + x, by simpa only [Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_cancel_left] using hx⟩
  isAxisParallel := by
    obtain ⟨R⟩ := K.isAxisParallel
    exact ⟨Tiling.Rectangulation.vadd R a⟩

/-- A finite nonempty almost-disjoint family of axis-parallel regions is again
an axis-parallel region.  This construction performs all boundary cancellation
inside the canonical region abstraction. -/
private noncomputable def Region.finiteUnion
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (K : ι → Region)
    (hpair : Pairwise (AEDisjoint volume on fun i => (K i).support)) : Region where
  support := ⋃ i, (K i).support
  isPolygonal := ⟨Tiling.Triangulation.finiteUnion
    (fun i => Classical.choice (K i).isPolygonal) hpair⟩
  nonempty := by
    let i : ι := Classical.choice inferInstance
    obtain ⟨x, hx⟩ := (K i).nonempty
    exact ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩⟩
  isAxisParallel := ⟨Tiling.Rectangulation.finiteUnion
    (fun i => Classical.choice (K i).isAxisParallel) hpair⟩

/-- Finite nonempty packings have an exact finite axis-segment frontier after
regularization.  Clipping and cancellation are absorbed by the merged region's
intrinsic boundary. -/
private theorem finitePacking_regularSupport_exactSegments
    {K : Region} {S : Set Tiling.Plane}
    (hfinite : S.Finite) (hne : S.Nonempty)
    (hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) :
    ∃ G : Set (Set Tiling.Plane), G.Finite ∧
      (∀ g ∈ G, ∃ a b : Tiling.Plane,
        a ≠ b ∧ (a.re = b.re ∨ a.im = b.im) ∧
          g = segment ℝ a b) ∧
      frontier (regularSupport K S) = ⋃₀ G := by
  classical
  let : Finite S := hfinite.to_subtype
  let : Fintype S := Fintype.ofFinite S
  let : Nonempty S := hne.to_subtype
  have hpair : Pairwise (AEDisjoint volume on
      fun s : S => (Region.vadd K s.1).support) := by
    intro s t hst
    let i : Tiling.Placement Tiling.Plane Unit := (s.1, ())
    let j : Tiling.Placement Tiling.Plane Unit := (t.1, ())
    have hi : i ∈ K.toPolygonalRegion.placements S := s.2
    have hj : j ∈ K.toPolygonalRegion.placements S := t.2
    have hij : i ≠ j := by
      intro h
      apply hst
      exact Subtype.ext (congrArg Prod.fst h)
    change AEDisjoint volume (s.1 +ᵥ K.support) (t.1 +ᵥ K.support)
    simpa only [Function.onFun,
      Tiling.RationalPolygonal.PolygonalRegion.placedTile_eq, i, j]
      using hpack hi hj hij
  let M : Region := Region.finiteUnion (fun s : S => Region.vadd K s.1) hpair
  have hreg : regularSupport K S = interior M.support := by
    rw [regularSupport, Tiling.Polygonal.regularSupport, ← openUnion,
      closure_openUnion_eq_iUnion_support hpack]
    rfl
  have hfront : frontier (regularSupport K S) = frontier M.support := by
    rw [hreg]
    exact M.frontier_openCarrier_eq_frontier_support
  obtain ⟨G, hGfinite, hGshape, hGeq⟩ :=
    M.exists_finite_frontier_intrinsicSegments
  exact ⟨G, hGfinite, (fun g hg => by
    obtain ⟨a, b, hne, halign, hseg, _⟩ := hGshape g hg
    exact ⟨a, b, hne, halign, hseg⟩), hfront.trans hGeq⟩

private theorem frontier_congr_on_open
    {U A B : Set Tiling.Plane} (hU : IsOpen U)
    (hEq : U ∩ A = U ∩ B) :
    U ∩ frontier A = U ∩ frontier B := by
  ext x
  by_cases hx : x ∈ U
  · have hAB : A =ᶠ[𝓝 x] B := by
      filter_upwards [hU.mem_nhds hx] with y hy
      have hmem : y ∈ A ↔ y ∈ B := by
        have := Set.ext_iff.mp hEq y
        simpa only [Set.mem_inter_iff, hy, true_and] using this
      exact propext hmem
    have hABc : Aᶜ =ᶠ[𝓝 x] Bᶜ := by
      filter_upwards [hU.mem_nhds hx] with y hy
      have hmem : y ∈ A ↔ y ∈ B := by
        have := Set.ext_iff.mp hEq y
        simpa only [Set.mem_inter_iff, hy, true_and] using this
      exact propext (not_congr hmem)
    simp only [Set.mem_inter_iff, hx, true_and,
      frontier_eq_inter_compl_interior, Set.mem_compl_iff]
    exact and_congr hAB.mem_interior_iff.not hABc.mem_interior_iff.not
  · simp [hx]

/-- On any bounded open window, a packing's frontier is exactly the frontier
of a finite subfamily.  This does not yet split the surviving pieces of each
intrinsic edge into nondegenerate boundary segments. -/
private theorem regularSupport_frontier_finiteReduction_on_boundedOpen
    {K : Region} {S U : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U) :
    ∃ T : Set Tiling.Plane, T.Finite ∧ T ⊆ S ∧
      U ∩ frontier (regularSupport K S) =
        U ∩ frontier (regularSupport K T) := by
  classical
  let A : Set S := {s | ((s.1 +ᵥ K.support) ∩ U).Nonempty}
  have hA : A.Finite := by
    apply Set.Finite.of_injOn (f := Subtype.val)
      (t := S ∩ (U - K.support))
    · intro s hs
      refine ⟨s.2, ?_⟩
      obtain ⟨z, hzTile, hzU⟩ := hs
      obtain ⟨k, hk, rfl⟩ := Set.mem_vadd_set.mp hzTile
      have hsub : (s.1 +ᵥ k) - k ∈ U - K.support :=
        Set.sub_mem_sub hzU hk
      simpa only [vadd_eq_add, add_sub_cancel_right] using hsub
    · intro s _ t _ h
      exact Subtype.ext h
    · exact (IsPacking.locallyFinite_centres hpacking).1 _
        (hUbounded.sub K.isPolygonal.isBounded)
  let T : Set Tiling.Plane := Subtype.val '' A
  have hTfinite : T.Finite := hA.image _
  have hTsub : T ⊆ S := by
    rintro z ⟨s, _, rfl⟩
    exact s.2
  have hsupportEq : U ∩ (⋃ s : S, (s : Tiling.Plane) +ᵥ K.support) =
      U ∩ (⋃ t : T, (t : Tiling.Plane) +ᵥ K.support) := by
    ext z
    constructor
    · rintro ⟨hzU, hz⟩
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
      have hsA : s ∈ A := ⟨z, hs, hzU⟩
      exact ⟨hzU, Set.mem_iUnion.mpr
        ⟨⟨s.1, ⟨s, hsA, rfl⟩⟩, hs⟩⟩
    · rintro ⟨hzU, hz⟩
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hz
      exact ⟨hzU, Set.mem_iUnion.mpr ⟨⟨t.1, hTsub t.2⟩, ht⟩⟩
  have hregEq : U ∩ regularSupport K S = U ∩ regularSupport K T := by
    rw [regularSupport, regularSupport, Tiling.Polygonal.regularSupport,
      Tiling.Polygonal.regularSupport, ← openUnion, ← openUnion,
      closure_openUnion_eq_iUnion_support hpacking]
    have hpackT : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements T) := by
      intro a ha b hb hab
      exact hpacking (hTsub ha) (hTsub hb) hab
    rw [closure_openUnion_eq_iUnion_support hpackT]
    ext x
    by_cases hx : x ∈ U
    · have hEq :
          (⋃ s : S, (s : Tiling.Plane) +ᵥ K.support) =ᶠ[𝓝 x]
          (⋃ t : T, (t : Tiling.Plane) +ᵥ K.support) := by
        filter_upwards [hUopen.mem_nhds hx] with y hy
        have := Set.ext_iff.mp hsupportEq y
        have hmem : y ∈ (⋃ s : S, (s : Tiling.Plane) +ᵥ K.support) ↔
            y ∈ (⋃ t : T, (t : Tiling.Plane) +ᵥ K.support) := by
          simpa only [Set.mem_inter_iff, hy, true_and] using this
        exact propext hmem
      simpa only [Set.mem_inter_iff, hx, true_and] using
        hEq.mem_interior_iff
    · simp [hx]
  exact ⟨T, hTfinite, hTsub, frontier_congr_on_open hUopen hregEq⟩


end Tiling.AxisParallel

namespace Tiling.AxisParallel

/-- A finite packed reduction gives an exact finite family of globally valid
segments on the interior of a nested coordinate box.  The outer window is
where its frontier agrees with the original infinite packing; the inner box
clips away all points outside that window. -/
private theorem finitePacking_frontier_clippedSegments_on_box
    {K : Region} {S T U : Set Tiling.Plane}
    {x₀ x₁ y₀ y₁ : ℝ}
    (hTfinite : T.Finite) (hTne : T.Nonempty)
    (hTpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements T))
    (hfrontEq : U ∩ frontier (regularSupport K S) =
      U ∩ frontier (regularSupport K T))
    (hQsub : IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁ ⊆ U)
    (hx : x₀ < x₁) (hy : y₀ < y₁) :
    ∃ G : Set (Set Tiling.Plane), G.Finite ∧
      (∀ g ∈ G, ∃ a b : Tiling.Plane,
        a ≠ b ∧ (a.re = b.re ∨ a.im = b.im) ∧
          g = segment ℝ a b) ∧
      (∀ g ∈ G, g ⊆ frontier (regularSupport K S)) ∧
      (∀ g ∈ G, g ⊆ IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁) ∧
      frontier (regularSupport K S) ∩
          interior (IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁) ⊆ ⋃₀ G := by
  classical
  obtain ⟨E, hEfinite, hEshape, hEeq⟩ :=
    finitePacking_regularSupport_exactSegments hTfinite hTne hTpack
  let Q := IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁
  let A : Set (Set Tiling.Plane) :=
    {e | e ∈ E ∧ (e ∩ interior Q).Nonempty}
  let G : Set (Set Tiling.Plane) := (fun e => e ∩ Q) '' A
  have hAfinite : A.Finite := hEfinite.subset fun e he => he.1
  have hGfinite : G.Finite := hAfinite.image _
  refine ⟨G, hGfinite, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨e, ⟨heE, ⟨z, hze, hzQ⟩⟩, rfl⟩ := hg
    obtain ⟨a, b, hab, haxis, rfl⟩ := hEshape e heE
    exact axisSegment_inter_closedAxisBox_of_interiorPoint hab haxis
      hx hy hze hzQ
  · intro g hg z hz
    obtain ⟨e, ⟨heE, _⟩, rfl⟩ := hg
    have hzT : z ∈ frontier (regularSupport K T) := by
      rw [hEeq]
      exact mem_sUnion.mpr ⟨e, heE, hz.1⟩
    have hzU : z ∈ U := hQsub hz.2
    have hmem := Set.ext_iff.mp hfrontEq z
    have hziff : z ∈ frontier (regularSupport K S) ↔
        z ∈ frontier (regularSupport K T) := by
      simpa only [mem_inter_iff, hzU, true_and] using hmem
    exact hziff.mpr hzT
  · intro g hg z hz
    obtain ⟨e, _, rfl⟩ := hg
    exact hz.2
  · intro z hz
    have hzU : z ∈ U := hQsub (interior_subset hz.2)
    have hmem := Set.ext_iff.mp hfrontEq z
    have hziff : z ∈ frontier (regularSupport K S) ↔
        z ∈ frontier (regularSupport K T) := by
      simpa only [mem_inter_iff, hzU, true_and] using hmem
    have hzT : z ∈ frontier (regularSupport K T) :=
      hziff.mp hz.1
    rw [hEeq] at hzT
    obtain ⟨e, heE, hze⟩ := mem_sUnion.mp hzT
    exact mem_sUnion.mpr ⟨e ∩ Q,
      ⟨e, ⟨heE, ⟨z, hze, hz.2⟩⟩, rfl⟩,
      ⟨hze, interior_subset hz.2⟩⟩

/-- The same local family exists when the finite reduction is empty: then the
frontier is absent on the outer window. -/
private theorem finiteReduction_frontier_clippedSegments_on_box
    {K : Region} {S T U : Set Tiling.Plane}
    {x₀ x₁ y₀ y₁ : ℝ}
    (hTfinite : T.Finite)
    (hTpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements T))
    (hfrontEq : U ∩ frontier (regularSupport K S) =
      U ∩ frontier (regularSupport K T))
    (hQsub : IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁ ⊆ U)
    (hx : x₀ < x₁) (hy : y₀ < y₁) :
    ∃ G : Set (Set Tiling.Plane), G.Finite ∧
      (∀ g ∈ G, ∃ a b : Tiling.Plane,
        a ≠ b ∧ (a.re = b.re ∨ a.im = b.im) ∧
          g = segment ℝ a b) ∧
      (∀ g ∈ G, g ⊆ frontier (regularSupport K S)) ∧
      (∀ g ∈ G, g ⊆ IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁) ∧
      frontier (regularSupport K S) ∩
          interior (IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁) ⊆ ⋃₀ G := by
  by_cases hne : T.Nonempty
  · exact finitePacking_frontier_clippedSegments_on_box hTfinite hne
      hTpack hfrontEq hQsub hx hy
  · have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨∅, Set.finite_empty, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · intro z hz
      have hzU : z ∈ U := hQsub (interior_subset hz.2)
      have hmem := Set.ext_iff.mp hfrontEq z
      have hzT : z ∈ frontier (regularSupport K T) := by
        have hziff : z ∈ frontier (regularSupport K S) ↔
            z ∈ frontier (regularSupport K T) := by
          simpa only [mem_inter_iff, hzU, true_and] using hmem
        exact hziff.mp hz.1
      simp [hTempty, regularSupport, Tiling.Polygonal.regularSupport, openUnion,
        Tiling.Polygonal.openUnion] at hzT

private theorem placedTile_mem_interior_axisBox
    {K : Region} {R r : ℝ} (hK : K.support ⊆ Metric.closedBall 0 R)
    (hRr : R < r) (s : Tiling.Plane) {z : Tiling.Plane}
    (hz : z ∈ s +ᵥ K.support) :
    z ∈ interior (IntrinsicVertices.closedAxisBox
      (s.re - r) (s.re + r) (s.im - r) (s.im + r)) := by
  obtain ⟨k, hk, rfl⟩ := Set.mem_vadd_set.mp hz
  have hkdist : ‖k‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hK hk
  have hkre : |k.re| ≤ R := (Complex.abs_re_le_norm k).trans hkdist
  have hkim : |k.im| ≤ R := (Complex.abs_im_le_norm k).trans hkdist
  change s + k ∈ interior
    (Icc (s.re - r) (s.re + r) ×ℂ Icc (s.im - r) (s.im + r))
  rw [Complex.interior_reProdIm, interior_Icc, interior_Icc]
  rw [Complex.mem_reProdIm]
  simp only [Complex.add_re, Complex.add_im, mem_Ioo]
  rcases abs_le.mp hkre with ⟨hkrel, hkrer⟩
  rcases abs_le.mp hkim with ⟨hkiml, hkimr⟩
  constructor <;> constructor <;> linarith

/-- The exact packed frontier has a globally exact, tile-indexed, locally
finite family of nondegenerate closed axis segments. -/
theorem packing_regularSupport_isLocallyAxisParallelPolygonal
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) :
    IsLocallyAxisParallelPolygonal (regularSupport K S) := by
  classical
  let D := regularSupport K S
  obtain ⟨R, hK⟩ := K.isPolygonal.isBounded.subset_closedBall (0 : Tiling.Plane)
  let r : ℝ := max R 0 + 1
  have hrR : R < r := by dsimp [r]; linarith [le_max_left R 0]
  have hrpos : 0 < r := by dsimp [r]; linarith [le_max_right R 0]
  let Q : S → Set Tiling.Plane := fun s => IntrinsicVertices.closedAxisBox
    (s.1.re - r) (s.1.re + r) (s.1.im - r) (s.1.im + r)
  let U : S → Set Tiling.Plane := fun s =>
    Ioo (s.1.re - (r + 1)) (s.1.re + (r + 1)) ×ℂ
      Ioo (s.1.im - (r + 1)) (s.1.im + (r + 1))
  have hUopen : ∀ s, IsOpen (U s) := fun s => isOpen_Ioo.reProdIm isOpen_Ioo
  have hUbounded : ∀ s, Bornology.IsBounded (U s) :=
    fun s => (Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _)
  have hQsub : ∀ s, Q s ⊆ U s := by
    intro s z hz
    change z.re ∈ Icc (s.1.re - r) (s.1.re + r) ∧
      z.im ∈ Icc (s.1.im - r) (s.1.im + r) at hz
    rw [Complex.mem_reProdIm]
    rcases hz with ⟨⟨hrelo, hrehi⟩, ⟨himlo, himhi⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hTileIn : ∀ s : S, s.1 +ᵥ K.support ⊆ interior (Q s) := by
    intro s z hz
    exact placedTile_mem_interior_axisBox hK hrR s.1 hz
  have hlocal : ∀ s : S, ∃ G : Set (Set Tiling.Plane),
      G.Finite ∧
      (∀ g ∈ G, ∃ a b : Tiling.Plane,
        a ≠ b ∧ (a.re = b.re ∨ a.im = b.im) ∧ g = segment ℝ a b) ∧
      (∀ g ∈ G, g ⊆ frontier D) ∧
      (∀ g ∈ G, g ⊆ Q s) ∧
      frontier D ∩ interior (Q s) ⊆ ⋃₀ G := by
    intro s
    obtain ⟨T, hTfinite, hTsub, hfrontEq⟩ :=
      regularSupport_frontier_finiteReduction_on_boundedOpen hpacking
        (hUopen s) (hUbounded s)
    have hTpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements T) := by
      intro a ha b hb hab
      exact hpacking (hTsub ha) (hTsub hb) hab
    exact finiteReduction_frontier_clippedSegments_on_box hTfinite
      hTpack hfrontEq (hQsub s) (by linarith [hrpos])
      (by linarith [hrpos])
  choose G hGfinite hGshape hGfront hGbox hGcover using hlocal
  let Gtotal : Set (Set Tiling.Plane) := ⋃ s : S, G s
  have hGtotalShape : ∀ g ∈ Gtotal, ∃ a b : Tiling.Plane,
      a ≠ b ∧ (a.re = b.re ∨ a.im = b.im) ∧ g = segment ℝ a b := by
    intro g hg
    obtain ⟨s, hgs⟩ := mem_iUnion.mp hg
    exact hGshape s g hgs
  have hGtotalSub : ⋃₀ Gtotal ⊆ frontier D := by
    rintro z ⟨g, hg, hzg⟩
    obtain ⟨s, hgs⟩ := mem_iUnion.mp hg
    exact hGfront s g hgs hzg
  have hFcover : frontier D ⊆ ⋃ s : S, s.1 +ᵥ K.support := by
    intro z hz
    obtain ⟨s, hzs⟩ := mem_iUnion.mp
      (regularSupport_frontier_subset_tileFrontiers hpacking hz)
    obtain ⟨k, hk, rfl⟩ := Set.mem_vadd_set.mp hzs
    exact mem_iUnion.mpr ⟨s, Set.mem_vadd_set.mpr
      ⟨k, K.isPolygonal.isClosed.frontier_subset hk, rfl⟩⟩
  have hGtotalCover : frontier D ⊆ ⋃₀ Gtotal := by
    intro z hz
    obtain ⟨s, hzs⟩ := mem_iUnion.mp (hFcover hz)
    have hzG := hGcover s ⟨hz, hTileIn s hzs⟩
    obtain ⟨g, hg, hzg⟩ := mem_sUnion.mp hzG
    exact mem_sUnion.mpr ⟨g, mem_iUnion.mpr ⟨s, hg⟩, hzg⟩
  have hGtotalEq : frontier D = ⋃₀ Gtotal :=
    Subset.antisymm hGtotalCover hGtotalSub
  refine ⟨(regularSupport_isRegularOpen K S).1,
    (regularSupport_isRegularOpen K S).2,
    Gtotal, hGtotalShape, hGtotalEq, ?_⟩
  intro W hW
  let B : Set Tiling.Plane := IntrinsicVertices.closedAxisBox (-r) r (-r) r
  have hBbounded : Bornology.IsBounded B :=
    (Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _)
  let A : Set S := {s | ∃ g ∈ G s, (g ∩ W).Nonempty}
  have hAsub : Subtype.val '' A ⊆ S ∩ (W - B) := by
    rintro t ⟨s, hs, rfl⟩
    obtain ⟨g, hg, z, hzg, hzW⟩ := hs
    have hzbox : z ∈ Q s := hGbox s g hg hzg
    have hzB : z - s.1 ∈ B := by
      change (z - s.1).re ∈ Icc (-r) r ∧
        (z - s.1).im ∈ Icc (-r) r
      change z.re ∈ Icc (s.1.re - r) (s.1.re + r) ∧
        z.im ∈ Icc (s.1.im - r) (s.1.im + r) at hzbox
      simp only [Complex.sub_re, Complex.sub_im, mem_Icc] at hzbox ⊢
      constructor <;> constructor <;> linarith [hzbox.1.1, hzbox.1.2,
        hzbox.2.1, hzbox.2.2]
    refine ⟨s.2, ?_⟩
    have hsSub : z - (z - s.1) ∈ W - B := Set.sub_mem_sub hzW hzB
    have heq : z - (z - s.1) = s.1 := by ring
    simpa only [heq] using hsSub
  have hAfin : A.Finite := by
    apply Set.Finite.of_injOn (f := Subtype.val)
      (t := S ∩ (W - B))
    · intro s hs
      exact hAsub ⟨s, hs, rfl⟩
    · intro s _ t _ h
      exact Subtype.ext h
    · exact (IsPacking.locallyFinite_centres hpacking).1 _
        (hW.sub hBbounded)
  have hfiniteUnion : (⋃ s ∈ A, G s).Finite :=
    hAfin.biUnion fun s _ => hGfinite s
  apply hfiniteUnion.subset
  intro g hg
  obtain ⟨hgG, hmeet⟩ := hg
  obtain ⟨s, hgs⟩ := mem_iUnion.mp hgG
  exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨⟨g, hgs, hmeet⟩, hgs⟩⟩

end Tiling.AxisParallel
