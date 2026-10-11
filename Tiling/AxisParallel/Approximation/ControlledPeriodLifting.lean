import Tiling.AxisParallel.Approximation.FiniteLocalComplexityControl
import Tiling.AxisParallel.Approximation.FLCMetricAndRelationRigidity
import Tiling.AxisParallel.Approximation.GoodApproximationPreservesTilings
import Tiling.AxisParallel.Foundations.IntrinsicVertices

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.header false
set_option warningAsError true

open Set
open scoped Pointwise
noncomputable section

namespace Tiling.AxisParallel.Approximation

/-- A planar displacement whose two coordinates belong to the approximation coordinate space. -/
abbrev ControlledDisplacement (C : ApproximationContext.{0}) :=
  {z : Tiling.Plane //
    z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}

def IndexedShortEdgeConnected (C : ApproximationContext.{0})
    (G : ℝ) (S : Set ↥C.centres) : Prop :=
  ∀ x ∈ Subtype.val '' S, ∀ y ∈ Subtype.val '' S,
    Relation.ReflTransGen
      (fun u v : Tiling.Plane ↦
        u ∈ Subtype.val '' S ∧ v ∈ Subtype.val '' S ∧ dist u v < G) x y

theorem properVertices_regularSupport_image_subset_translatedVertices :
    ∀ (C : ApproximationContext.{0})
      (_hTiles : TilesOn C.region C.centres C.target)
      (S : Set ↥C.centres),
    properVertices (regularSupport C.region (Subtype.val '' S)) ⊆
      C.translatedVertices :=by
  intro C _hTiles S x hx
  let A := C.region.polygonalProtoTiling (Subtype.val '' S)
  have hpack : Tiling.IsPacking A.prototiles A.placements := by
    intro i hi j hj hij
    apply _hTiles.2.1
    · change i.1 ∈ C.centres
      change i.1 ∈ Subtype.val '' S at hi
      rcases hi with ⟨s, hs, hsi⟩
      exact hsi ▸ s.2
    · change j.1 ∈ C.centres
      change j.1 ∈ Subtype.val '' S at hj
      rcases hj with ⟨s, hs, hsj⟩
      exact hsj ▸ s.2
    · exact hij
  have hcarrier : A.placementCarrier Set.univ =
      closure (openUnion C.region (Subtype.val '' S)) := by
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
        frontier (regularSupport C.region (Subtype.val '' S)) := by
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
    A.exists_vertex_of_not_boundaryLocallyStraightAt hpack Set.univ hxfrontier hxnotstraight
  have hcenterS : i.1.1 ∈ Subtype.val '' S := i.2
  have hplaced : x ∈ i.1.1 +ᵥ C.region.vertices := by
    simpa only [A, Region.polygonalProtoTiling_placedVertices] using hxi
  rw [ApproximationContext.translatedVertices]
  obtain ⟨v, hv, hvx⟩ := Set.mem_vadd_set.mp hplaced
  rw [Set.mem_add]
  refine ⟨v, hv, i.1.1, ?_, ?_⟩
  · rcases hcenterS with ⟨s, hs, hsi⟩
    exact hsi ▸ s.2
  · rw [add_comm]
    exact hvx


private theorem mapPoint_sub
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}) :
    mapPoint phi ⟨x.1 - y.1, C.coordinateSpace.sub_mem x.2.1 y.2.1,
      C.coordinateSpace.sub_mem x.2.2 y.2.2⟩ = mapPoint phi x - mapPoint phi y := by
  apply Complex.ext
  · simp only [mapPoint, mapScalar, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      add_zero]
    exact_mod_cast (map_sub phi
      (⟨x.1.re, x.2.1⟩ : C.coordinateSpace)
      (⟨y.1.re, y.2.1⟩ : C.coordinateSpace))
  · simp only [mapPoint, mapScalar, Complex.sub_re, Complex.sub_im,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      add_zero, zero_add]
    exact_mod_cast (map_sub phi
      (⟨x.1.im, x.2.2⟩ : C.coordinateSpace)
      (⟨y.1.im, y.2.2⟩ : C.coordinateSpace))

private theorem mapPoint_add_indexed
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}) :
    mapPoint phi ⟨x.1 + y.1, C.coordinateSpace.add_mem x.2.1 y.2.1,
      C.coordinateSpace.add_mem x.2.2 y.2.2⟩ = mapPoint phi x + mapPoint phi y := by
  apply Complex.ext
  · simp only [mapPoint, mapScalar, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one]
    norm_num
    norm_cast
    exact_mod_cast (map_add phi
      (⟨x.1.re, x.2.1⟩ : C.coordinateSpace)
      (⟨y.1.re, y.2.1⟩ : C.coordinateSpace))
  · simp only [mapPoint, mapScalar, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
    exact_mod_cast (map_add phi
      (⟨x.1.im, x.2.2⟩ : C.coordinateSpace)
      (⟨y.1.im, y.2.2⟩ : C.coordinateSpace))

private def centre_vertex
    {C : ApproximationContext} (s : ↥C.centres) : ↥C.translatedVertices :=
  ⟨s, ⟨0, C.zero_mem_vertices, s, s.2, zero_add (s : Tiling.Plane)⟩⟩

private theorem centre_vertex_map
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (s : ↥C.centres) :
    mapTranslatedVertex phi (centre_vertex s) = Tphi s := by
  rw [mapTranslatedVertex]
  have hpoint : C.translatedVertexPoint (centre_vertex s) = C.centrePoint s.1 s.2 := by
    apply Subtype.ext
    rfl
  rw [hpoint, ← hTphi s]

private theorem dist_map_centres_lt_half
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    {s t : ↥C.centres} (hst : dist (s : Tiling.Plane) t < P.scale)
    (hmargin : dist (s : Tiling.Plane) t + P.localError < P.scale / 2) :
    dist (Tphi s) (Tphi t) < P.scale / 2 := by
  let a := centre_vertex s
  let b := centre_vertex t
  have hst' : dist (a : Tiling.Plane) b < P.scale := by
    simpa [a, b, centre_vertex] using hst
  have hlocal := P.local_accuracy phi hphi a b hst'
  have htriangle : dist (mapTranslatedVertex phi a - mapTranslatedVertex phi b) 0 ≤
      dist (mapTranslatedVertex phi a - mapTranslatedVertex phi b)
        ((a : Tiling.Plane) - (b : Tiling.Plane)) +
      dist ((a : Tiling.Plane) - (b : Tiling.Plane)) 0 :=
    dist_triangle _ _ _
  have hdist : dist (mapTranslatedVertex phi a) (mapTranslatedVertex phi b) ≤
      dist (mapTranslatedVertex phi a - mapTranslatedVertex phi b)
        ((a : Tiling.Plane) - (b : Tiling.Plane)) + dist (s : Tiling.Plane) t := by
    simpa [a, b, centre_vertex, dist_eq_norm] using htriangle
  calc
    dist (Tphi s) (Tphi t) = dist (mapTranslatedVertex phi a) (mapTranslatedVertex phi b) := by
      rw [centre_vertex_map phi Tphi hTphi, centre_vertex_map phi Tphi hTphi]
    _ ≤ dist (mapTranslatedVertex phi a - mapTranslatedVertex phi b)
          ((a : Tiling.Plane) - (b : Tiling.Plane)) + dist (s : Tiling.Plane) t := hdist
    _ < P.localError + dist (s : Tiling.Plane) t := by
      simpa [add_comm] using add_lt_add_right hlocal (dist (s : Tiling.Plane) t)
    _ < P.scale / 2 := by linarith

private theorem indexedPeriod_forward
    {C : ApproximationContext} (Tphi : ↥C.centres ↪ Tiling.Plane)
    (S : Set ↥C.centres) (imagePeriod : Tiling.Plane)
    (hperiod : imagePeriod +ᵥ (Tphi '' S) = Tphi '' S) :
    ∀ s : ↥S, ∃ t : ↥S, Tphi t.1 = imagePeriod + Tphi s.1 := by
  intro s
  have hsV : Tphi s.1 ∈ Tphi '' S := ⟨s.1, s.2, rfl⟩
  have hi : imagePeriod + Tphi s.1 ∈ Tphi '' S := by
    exact (Set.ext_iff.mp hperiod _).mp ⟨Tphi s.1, hsV, rfl⟩
  rcases hi with ⟨t, ht, hteq⟩
  refine ⟨⟨t, ht⟩, ?_⟩
  exact hteq

private theorem indexedPeriod_neg
    {C : ApproximationContext} (Tphi : ↥C.centres ↪ Tiling.Plane)
    (S : Set ↥C.centres) (imagePeriod : Tiling.Plane)
    (hperiod : imagePeriod +ᵥ (Tphi '' S) = Tphi '' S) :
    (-imagePeriod) +ᵥ (Tphi '' S) = Tphi '' S := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    have hy' : y ∈ imagePeriod +ᵥ (Tphi '' S) :=
      (Set.ext_iff.mp hperiod y).mpr hy
    rcases hy' with ⟨z, hz, hzy⟩
    have heq : -imagePeriod + y = z := by
      change imagePeriod + z = y at hzy
      rw [← hzy]
      abel
    change -imagePeriod + y = x at hxy
    rw [← hxy]
    change -imagePeriod + y ∈ Tphi '' S
    rw [heq]
    exact hz
  · intro x hx
    have hz : imagePeriod + x ∈ Tphi '' S :=
      (Set.ext_iff.mp hperiod (imagePeriod + x)).mp ⟨x, hx, rfl⟩
    refine ⟨imagePeriod + x, hz, ?_⟩
    change -imagePeriod + (imagePeriod + x) = x
    abel

private theorem indexedPeriodPermutation
    {C : ApproximationContext} (Tphi : ↥C.centres ↪ Tiling.Plane)
    (S : Set ↥C.centres) (imagePeriod : Tiling.Plane)
    (hperiod : imagePeriod +ᵥ (Tphi '' S) = Tphi '' S) :
    ∃ sigma : ↥S ≃ ↥S,
      ∀ s : ↥S, Tphi (sigma s).1 = imagePeriod + Tphi s.1 := by
  have hforward : ∀ s : ↥S, ∃ t : ↥S,
      Tphi t.1 = imagePeriod + Tphi s.1 :=
    indexedPeriod_forward Tphi S imagePeriod hperiod
  choose sigma hsig using hforward
  have hneg := indexedPeriod_neg Tphi S imagePeriod hperiod
  have hback : ∀ s : ↥S, ∃ t : ↥S,
      Tphi t.1 = -imagePeriod + Tphi s.1 := by
    intro s
    exact indexedPeriod_forward Tphi S (-imagePeriod) (by simpa using hneg) s
  choose tau htau using hback
  have hinj : Function.Injective sigma := by
    intro s t hst
    apply Subtype.ext
    apply Tphi.injective
    have h := congrArg (fun z : ↥S => Tphi z.1) hst
    rw [hsig, hsig] at h
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have hsurj : Function.Surjective sigma := by
    intro s
    refine ⟨tau s, ?_⟩
    apply Subtype.ext
    apply Tphi.injective
    calc
      Tphi (sigma (tau s)).1 = imagePeriod + Tphi (tau s).1 := hsig (tau s)
      _ = imagePeriod + (-imagePeriod + Tphi s.1) := by rw [htau]
      _ = Tphi s.1 := by abel
  exact ⟨Equiv.ofBijective sigma ⟨hinj, hsurj⟩, hsig⟩


theorem connectedIndexedPeriodLift :
    ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (S : Set ↥C.centres) (G : ℝ),
      S.Nonempty → IndexedShortEdgeConnected C G S →
      G < P.scale → G + P.localError < P.scale / 2 →
    ∀ imagePeriod : Tiling.Plane,
      imagePeriod ≠ 0 →
      imagePeriod +ᵥ deformedCenterCarrierOn Tphi S =
        deformedCenterCarrierOn Tphi S →
      ∃ alpha : ControlledDisplacement C,
        alpha.1 ≠ 0 ∧
        mapPoint phi alpha = imagePeriod ∧
        alpha.1 +ᵥ Subtype.val '' S = Subtype.val '' S :=by
  intro C P phi hphi Tphi hTphi S G hSne hconn hG hmargin imagePeriod hne hperiod
  obtain ⟨sigma, hsig⟩ := indexedPeriodPermutation Tphi S imagePeriod hperiod
  have edge_disp : ∀ {s t : ↥S},
      dist (s : Tiling.Plane) t < G →
      (sigma s : Tiling.Plane) - (s : Tiling.Plane) =
        (sigma t : Tiling.Plane) - (t : Tiling.Plane) := by
    intro s t hstG
    let a_s := centre_vertex s.1
    let a_t := centre_vertex t.1
    let a_ss := centre_vertex (sigma s).1
    let a_tt := centre_vertex (sigma t).1
    have hst : dist (s : Tiling.Plane) t < P.scale := lt_trans hstG hG
    have h0 := dist_map_centres_lt_half P phi hphi Tphi hTphi hst
      (lt_trans (add_lt_add_left hstG P.localError) hmargin)
    have h1 : dist (mapTranslatedVertex phi a_ss) (mapTranslatedVertex phi a_tt) <
        P.scale / 2 := by
      rw [centre_vertex_map phi Tphi hTphi, centre_vertex_map phi Tphi hTphi,
        hsig, hsig]
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h0
    have h0' : dist (mapTranslatedVertex phi a_t) (mapTranslatedVertex phi a_s) <
        P.scale / 2 := by
      rw [centre_vertex_map phi Tphi hTphi, centre_vertex_map phi Tphi hTphi]
      simpa [dist_comm] using h0
    have h1' : dist (mapTranslatedVertex phi a_tt) (mapTranslatedVertex phi a_ss) <
        P.scale / 2 := by simpa [dist_comm] using h1
    have hh := deformation_reflectsBoundedCoordinateDisplacement P phi hphi
      Axis.horizontal a_s a_t a_ss a_tt h0' h1' (by
        rw [centre_vertex_map phi Tphi hTphi, centre_vertex_map phi Tphi hTphi,
          centre_vertex_map phi Tphi hTphi, centre_vertex_map phi Tphi hTphi,
          hsig, hsig]
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc])
    have hv := deformation_reflectsBoundedCoordinateDisplacement P phi hphi
      Axis.vertical a_s a_t a_ss a_tt h0' h1' (by
        rw [centre_vertex_map phi Tphi hTphi, centre_vertex_map phi Tphi hTphi,
          centre_vertex_map phi Tphi hTphi, centre_vertex_map phi Tphi hTphi,
          hsig, hsig]
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc])
    have hh' : (t : Tiling.Plane).re - (s : Tiling.Plane).re =
        (sigma t : Tiling.Plane).re - (sigma s : Tiling.Plane).re := by
      simpa only [a_s, a_t, a_ss, a_tt, centre_vertex, Axis.coord, Complex.sub_re]
        using hh
    have hv' : (t : Tiling.Plane).im - (s : Tiling.Plane).im =
        (sigma t : Tiling.Plane).im - (sigma s : Tiling.Plane).im := by
      simpa only [a_s, a_t, a_ss, a_tt, centre_vertex, Axis.coord, Complex.sub_im]
        using hv
    apply Complex.ext
    · change (sigma s : Tiling.Plane).re - (s : Tiling.Plane).re =
        (sigma t : Tiling.Plane).re - (t : Tiling.Plane).re
      linarith
    · change (sigma s : Tiling.Plane).im - (s : Tiling.Plane).im =
        (sigma t : Tiling.Plane).im - (t : Tiling.Plane).im
      linarith
  let U : Set Tiling.Plane := Subtype.val '' S
  have u_image (u : ↥U) : u.1 ∈ Subtype.val '' S := by
    simp [U] at u ⊢
  have sourceWitness (u : ↥U) : ∃ s : ↥S, (s : Tiling.Plane) = u.1 := by
    rcases u_image u with ⟨s, hs, hsu⟩
    exact ⟨⟨s, hs⟩, hsu⟩
  let sourceAt : ∀ u : ↥U, ↥S := fun u => Classical.choose (sourceWitness u)
  have sourceAt_spec (u : ↥U) : (sourceAt u : Tiling.Plane) = u.1 := by
    exact Classical.choose_spec (sourceWitness u)
  let dispOf : ∀ (x : Tiling.Plane), x ∈ U → Tiling.Plane := fun x hx =>
    (sigma (sourceAt ⟨x, hx⟩) : Tiling.Plane) - x
  have path_disp : ∀ {x y : Tiling.Plane}
      (hp : Relation.ReflTransGen
        (fun u v : Tiling.Plane ↦
          u ∈ U ∧ v ∈ U ∧ dist u v < G) x y),
      ∀ hx : x ∈ U, ∀ hy : y ∈ U,
        dispOf x hx = dispOf y hy := by
    intro x y hp
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro hx hy
        rfl
    | head edge htail ih =>
        intro hx hy
        rcases edge with ⟨hxmid, hymid, hxy⟩
        have hst : dist (sourceAt ⟨_, hxmid⟩ : Tiling.Plane)
            (sourceAt ⟨_, hymid⟩ : Tiling.Plane) < G := by
          simpa only [sourceAt_spec] using hxy
        have hedge := edge_disp hst
        have hfirst : dispOf _ hxmid = dispOf _ hymid := by
          simpa only [dispOf, sourceAt_spec] using hedge
        exact hfirst.trans (ih hymid hy)
  obtain ⟨s0c, hs0c⟩ := hSne
  let s₀ : ↥S := ⟨s0c, hs0c⟩
  let alpha : ControlledDisplacement C := by
    refine ⟨(sigma s₀ : Tiling.Plane) - (s₀ : Tiling.Plane), ?_, ?_⟩
    · exact C.coordinateSpace.sub_mem
        (C.centre_re_mem (sigma s₀).1 (sigma s₀).1.2)
        (C.centre_re_mem s₀.1 s₀.1.2)
    · exact C.coordinateSpace.sub_mem
        (C.centre_im_mem (sigma s₀).1 (sigma s₀).1.2)
        (C.centre_im_mem s₀.1 s₀.1.2)
  have hdisp : ∀ s : ↥S,
      (sigma s : Tiling.Plane) - (s : Tiling.Plane) = alpha.1 := by
    intro s
    have hp := hconn (s₀ : Tiling.Plane) ⟨s₀, s₀.2, rfl⟩
      (s : Tiling.Plane) ⟨s, s.2, rfl⟩
    have hpath := path_disp hp ⟨s₀, s₀.2, rfl⟩ ⟨s, s.2, rfl⟩
    have hsource₀ : sourceAt ⟨(s₀ : Tiling.Plane), ⟨s₀, s₀.2, rfl⟩⟩ = s₀ := by
      apply Subtype.ext
      apply Subtype.ext
      exact sourceAt_spec _
    have hsources : sourceAt ⟨(s : Tiling.Plane), ⟨s, s.2, rfl⟩⟩ = s := by
      apply Subtype.ext
      apply Subtype.ext
      exact sourceAt_spec _
    simpa [dispOf, alpha, hsource₀, hsources] using hpath.symm
  have hmap : mapPoint phi alpha = imagePeriod := by
    have hsub := mapPoint_sub phi
      (C.centrePoint (sigma s₀).1 (sigma s₀).1.2)
      (C.centrePoint s₀.1 s₀.1.2)
    calc
      mapPoint phi alpha = mapPoint phi
          ⟨(sigma s₀ : Tiling.Plane) - (s₀ : Tiling.Plane),
            C.coordinateSpace.sub_mem
              (C.centre_re_mem (sigma s₀).1 (sigma s₀).1.2)
              (C.centre_re_mem s₀.1 s₀.1.2),
            C.coordinateSpace.sub_mem
              (C.centre_im_mem (sigma s₀).1 (sigma s₀).1.2)
              (C.centre_im_mem s₀.1 s₀.1.2)⟩ := by congr 1
      _ = mapPoint phi (C.centrePoint (sigma s₀).1 (sigma s₀).1.2) -
          mapPoint phi (C.centrePoint s₀.1 s₀.1.2) := hsub
      _ = imagePeriod := by
        rw [← hTphi (sigma s₀), ← hTphi s₀, hsig]
        abel
  refine ⟨alpha, ?_, hmap, ?_⟩
  · intro hzero
    apply hne
    calc
      imagePeriod = mapPoint phi alpha := hmap.symm
      _ = 0 := by
        have hz : alpha =
            (⟨0, C.coordinateSpace.zero_mem,
              C.coordinateSpace.zero_mem⟩ : ControlledDisplacement C) := by
          apply Subtype.ext
          exact hzero
        rw [hz]
        apply Complex.ext <;>
          simp only [mapPoint, mapScalar, Complex.add_re, Complex.add_im,
            Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
        all_goals
          have hq : ∀ h : (0 : ℝ) ∈ C.coordinateSpace, phi ⟨0, h⟩ = 0 := by
            intro h
            have hzq : (⟨0, h⟩ : C.coordinateSpace) = 0 := by
              apply Subtype.ext
              rfl
            rw [hzq, map_zero]
          simp [hq]
  · apply Set.Subset.antisymm
    · intro x hx
      rcases hx with ⟨y, hy, hxy⟩
      rcases hy with ⟨s, hs, hsy⟩
      have hd := hdisp ⟨s, hs⟩
      refine ⟨(sigma ⟨s, hs⟩).1, (sigma ⟨s, hs⟩).2, ?_⟩
      calc
        (sigma ⟨s, hs⟩ : Tiling.Plane) = alpha.1 + (s : Tiling.Plane) := by
          rw [← hd]
          abel
        _ = alpha.1 + y := by rw [hsy]
        _ = x := by simpa [vadd_eq_add] using hxy
    · intro x hx
      rcases hx with ⟨s, hs, hsx⟩
      let t : ↥S := sigma.symm ⟨s, hs⟩
      have hd := hdisp t
      refine ⟨(t : Tiling.Plane), ⟨t.1, t.2, rfl⟩, ?_⟩
      calc
        alpha.1 + (t : Tiling.Plane) = (sigma t : Tiling.Plane) := by
          rw [← hd]
          abel
        _ = (s : Tiling.Plane) := by
          rw [show sigma t = ⟨s, hs⟩ by exact sigma.apply_symm_apply _]
        _ = x := hsx



theorem connectedAlignedIndexedPeriodLift :
    ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (axis : Axis) (S : Set ↥C.centres) (G : ℝ),
      S.Nonempty → IndexedShortEdgeConnected C G S →
      (∃ c, ∀ s : S, axis.transverseCoord (Tphi s.1) = c) →
      G < P.scale → G + P.localError < P.scale / 2 →
    ∀ imagePeriod : Tiling.Plane,
      imagePeriod ≠ 0 →
      axis.transverseCoord imagePeriod = 0 →
      imagePeriod +ᵥ deformedCenterCarrierOn Tphi S =
        deformedCenterCarrierOn Tphi S →
      ∃ alpha : ControlledDisplacement C,
        alpha.1 ≠ 0 ∧
        axis.transverseCoord alpha.1 = 0 ∧
        mapPoint phi alpha = imagePeriod ∧
        alpha.1 +ᵥ Subtype.val '' S = Subtype.val '' S :=by
  intro C P phi hphi Tphi hTphi axis S G hSne hconn hcol hG hmargin
    imagePeriod hne haxis hperiod
  obtain ⟨alpha, halpha_ne, halpha_map, halpha_set⟩ :=
    connectedIndexedPeriodLift P phi hphi Tphi hTphi S G hSne hconn hG hmargin
      imagePeriod hne hperiod
  obtain ⟨s0c, hs0c⟩ := hSne
  let s0 : ↥S := ⟨s0c, hs0c⟩
  obtain ⟨c, hc⟩ := hcol
  obtain ⟨sigma, hsig⟩ := indexedPeriodPermutation Tphi S imagePeriod hperiod
  let U : Set Tiling.Plane := Subtype.val '' S
  have u_image (u : ↥U) : u.1 ∈ Subtype.val '' S := by
    simp [U] at u ⊢
  have sourceWitness (u : ↥U) : ∃ s : ↥S, (s : Tiling.Plane) = u.1 := by
    rcases u_image u with ⟨s, hs, hsu⟩
    exact ⟨⟨s, hs⟩, hsu⟩
  let sourceAt : ∀ u : ↥U, ↥S := fun u => Classical.choose (sourceWitness u)
  have sourceAt_spec (u : ↥U) : (sourceAt u : Tiling.Plane) = u.1 := by
    exact Classical.choose_spec (sourceWitness u)
  have edge_trans : ∀ {s t : ↥S}, dist (s : Tiling.Plane) t < G →
      axis.transverseCoord ((s : Tiling.Plane) - (t : Tiling.Plane)) = 0 := by
    intro s t hst
    let a_s := centre_vertex s.1
    let a_t := centre_vertex t.1
    have hst' : dist (s : Tiling.Plane) t < P.scale := lt_trans hst hG
    have hm := dist_map_centres_lt_half P phi hphi Tphi hTphi hst'
      (lt_trans (add_lt_add_left hst P.localError) hmargin)
    have hm' : dist (mapTranslatedVertex phi a_s) (mapTranslatedVertex phi a_t) <
        P.scale / 2 := by
      rw [centre_vertex_map phi Tphi hTphi, centre_vertex_map phi Tphi hTphi]
      exact hm
    have hzmap : axis.transverseCoord
        (mapTranslatedVertex phi a_s - mapTranslatedVertex phi a_t) = 0 := by
      rw [centre_vertex_map phi Tphi hTphi, centre_vertex_map phi Tphi hTphi]
      have hs := hc s
      have ht := hc t
      cases axis <;> simp only [Axis.transverseCoord, Complex.sub_re, Complex.sub_im] at hs ht ⊢
      · linarith
      · linarith
    have hz := (deformation_reflectsAxisCoset P phi hphi axis a_s a_t hm').mpr hzmap
    simpa [a_s, a_t, centre_vertex, Axis.transverseCoord, Complex.sub_re,
      Complex.sub_im] using hz
  have path_trans : ∀ {x y : Tiling.Plane}
      (hp : Relation.ReflTransGen
        (fun u v : Tiling.Plane ↦ u ∈ U ∧ v ∈ U ∧ dist u v < G) x y),
      ∀ hx : x ∈ U, ∀ hy : y ∈ U,
        axis.transverseCoord (sourceAt ⟨x, hx⟩ : Tiling.Plane) =
          axis.transverseCoord (sourceAt ⟨y, hy⟩ : Tiling.Plane) := by
    intro x y hp
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro hx hy
        rfl
    | head edge htail ih =>
        intro hx hy
        rcases edge with ⟨hxmid, hymid, hdist⟩
        have hst : dist (sourceAt ⟨_, hxmid⟩ : Tiling.Plane)
            (sourceAt ⟨_, hymid⟩ : Tiling.Plane) < G := by
          simpa only [sourceAt_spec] using hdist
        have hz := edge_trans hst
        have hzero : axis.transverseCoord
            (sourceAt ⟨_, hxmid⟩ : Tiling.Plane) =
            axis.transverseCoord (sourceAt ⟨_, hymid⟩ : Tiling.Plane) := by
          cases axis <;> simp only [Axis.transverseCoord, Complex.sub_re, Complex.sub_im] at hz ⊢
          · linarith
          · linarith
        exact hzero.trans (ih hymid hy)
  have hsource_sigma : axis.transverseCoord (s0 : Tiling.Plane) =
      axis.transverseCoord (sigma s0 : Tiling.Plane) := by
    have hp := hconn (s0 : Tiling.Plane) ⟨s0.1, s0.2, rfl⟩
      (sigma s0 : Tiling.Plane) ⟨sigma s0, (sigma s0).2, rfl⟩
    have hpath := path_trans hp ⟨s0, s0.2, rfl⟩ ⟨sigma s0, (sigma s0).2, rfl⟩
    have hs0 : sourceAt ⟨(s0 : Tiling.Plane), ⟨s0, s0.2, rfl⟩⟩ = s0 := by
      apply Subtype.ext
      apply Subtype.ext
      exact sourceAt_spec _
    have hss : sourceAt ⟨(sigma s0 : Tiling.Plane), ⟨sigma s0, (sigma s0).2, rfl⟩⟩ = sigma s0 := by
      apply Subtype.ext
      apply Subtype.ext
      exact sourceAt_spec _
    simpa [hs0, hss] using hpath
  have hmem : alpha.1 + (s0 : Tiling.Plane) ∈ U := by
    have hs0U : (s0 : Tiling.Plane) ∈ Subtype.val '' S :=
      ⟨s0.1, s0.2, rfl⟩
    exact (Set.ext_iff.mp halpha_set _).mp ⟨s0, hs0U, rfl⟩
  rcases hmem with ⟨t, ht, hteq⟩
  let tS : ↥S := ⟨t, ht⟩
  have ht_sigma : (⟨t, ht⟩ : ↥S) = sigma s0 := by
    apply Subtype.ext
    apply Tphi.injective
    have hsum : Tphi t = imagePeriod + Tphi s0 := by
      calc
        Tphi tS = mapPoint phi (C.centrePoint t t.2) := hTphi _
        _ = mapPoint phi (⟨alpha.1 + (s0 : Tiling.Plane),
            C.coordinateSpace.add_mem alpha.2.1 (C.centre_re_mem s0.1 s0.1.2),
            C.coordinateSpace.add_mem alpha.2.2
              (C.centre_im_mem s0.1 s0.1.2)⟩ : ControlledDisplacement C) := by
          congr 1
          apply Subtype.ext
          change (t : Tiling.Plane) = alpha.1 + (s0 : Tiling.Plane)
          exact hteq
        _ = mapPoint phi alpha + mapPoint phi (C.centrePoint s0.1 s0.1.2) := by
          have hadd := mapPoint_add_indexed phi alpha (C.centrePoint s0.1 s0.1.2)
          exact hadd
        _ = imagePeriod + Tphi s0 := by rw [halpha_map, hTphi]
    exact hsum.trans (hsig s0).symm
  have halpha_axis : axis.transverseCoord alpha.1 = 0 := by
    have ht_sigma_val : (t : Tiling.Plane) = (sigma s0 : Tiling.Plane) := by
      exact congrArg (fun q : ↥S => (q : Tiling.Plane)) ht_sigma
    have hdiff : alpha.1 = (sigma s0 : Tiling.Plane) - (s0 : Tiling.Plane) := by
      calc
        alpha.1 = (alpha.1 + (s0 : Tiling.Plane)) - (s0 : Tiling.Plane) := by abel
        _ = (t : Tiling.Plane) - (s0 : Tiling.Plane) := by rw [hteq]
        _ = (sigma s0 : Tiling.Plane) - (s0 : Tiling.Plane) := by rw [ht_sigma_val]
    rw [hdiff]
    cases axis <;>
      simp only [Axis.transverseCoord, Complex.sub_re, Complex.sub_im] at hsource_sigma ⊢
    · linarith [hsource_sigma]
    · linarith [hsource_sigma]
  exact ⟨alpha, halpha_ne, halpha_axis, halpha_map, halpha_set⟩


private theorem mapPoint_add (C : ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y : ControlledDisplacement C) :
    mapPoint phi ⟨(x.1 + y.1),
      C.coordinateSpace.add_mem x.2.1 y.2.1,
      C.coordinateSpace.add_mem x.2.2 y.2.2⟩ =
      mapPoint phi x + mapPoint phi y := by
  apply Complex.ext <;>
    simp only [mapPoint, mapScalar, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add] <;>
    norm_cast
  all_goals
    rw [← map_add]
    rfl

private theorem mapPoint_three_add (C : ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y z : ControlledDisplacement C) :
    mapPoint phi ⟨(x.1 + y.1 + z.1),
      C.coordinateSpace.add_mem (C.coordinateSpace.add_mem x.2.1 y.2.1) z.2.1,
      C.coordinateSpace.add_mem (C.coordinateSpace.add_mem x.2.2 y.2.2) z.2.2⟩ =
      mapPoint phi x + mapPoint phi y + mapPoint phi z := by
  let xy : ControlledDisplacement C :=
    ⟨x.1 + y.1, C.coordinateSpace.add_mem x.2.1 y.2.1,
      C.coordinateSpace.add_mem x.2.2 y.2.2⟩
  calc
    _ = mapPoint phi xy + mapPoint phi z := by
      simpa [xy, add_assoc] using (mapPoint_add C phi xy z)
    _ = _ := by
      rw [show mapPoint phi xy =
        mapPoint phi ⟨x.1 + y.1,
          C.coordinateSpace.add_mem x.2.1 y.2.1,
          C.coordinateSpace.add_mem x.2.2 y.2.2⟩ by rfl]
      exact congrArg (fun t => t + mapPoint phi z) (mapPoint_add C phi x y)

private theorem mapTranslatedVertex_eq_mapPoint
    (C : ApproximationContext) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (z : Tiling.Plane) (hz : z ∈ C.translatedVertices) :
    mapTranslatedVertex phi ⟨z, hz⟩ =
      mapPoint phi (C.translatedVertexPoint ⟨z, hz⟩) := rfl


theorem periodLifts_eq_of_properVertexShift :
    ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (S₀ S₁ : Set ↥C.centres)
      (alpha₀ alpha₁ beta : ControlledDisplacement C)
      (imagePeriod : Tiling.Plane),
      mapPoint phi alpha₀ = imagePeriod →
      mapPoint phi alpha₁ = imagePeriod →
      alpha₀.1 +ᵥ Subtype.val '' S₀ = Subtype.val '' S₀ →
      alpha₁.1 +ᵥ Subtype.val '' S₁ = Subtype.val '' S₁ →
      properVertices (regularSupport C.region (Subtype.val '' S₀)) ⊆
        C.translatedVertices →
      properVertices (regularSupport C.region (Subtype.val '' S₁)) ⊆
        C.translatedVertices →
      (∀ w, w ∈ properVertices
          (regularSupport C.region (Subtype.val '' S₀)) →
        beta.1 + w ∈ properVertices
          (regularSupport C.region (Subtype.val '' S₁))) →
      (properVertices
        (regularSupport C.region (Subtype.val '' S₀))).Nonempty →
      alpha₀ = alpha₁ :=by
  intro C P phi hphi S₀ S₁ alpha₀ alpha₁ beta imagePeriod hmap₀ hmap₁
    hper₀ hper₁ hprov₀ hprov₁ hbeta hne
  have hregperiod (S : Set ↥C.centres) (a : ControlledDisplacement C)
      (hper : a.1 +ᵥ Subtype.val '' S = Subtype.val '' S) :
      a.1 +ᵥ regularSupport C.region (Subtype.val '' S) =
        regularSupport C.region (Subtype.val '' S) := by
    rw [← regularSupport_vadd, hper]
  have hproperperiod (S : Set ↥C.centres) (a : ControlledDisplacement C)
      (hper : a.1 +ᵥ Subtype.val '' S = Subtype.val '' S)
      {w : Tiling.Plane}
      (hw : w ∈ properVertices (regularSupport C.region (Subtype.val '' S))) :
      w + a.1 ∈ properVertices (regularSupport C.region (Subtype.val '' S)) := by
    have hs := Tiling.AxisParallel.properVertices_vadd_eq a.1
      (regularSupport C.region (Subtype.val '' S))
    rw [hregperiod S a hper] at hs
    have : w + a.1 ∈ a.1 +ᵥ properVertices
        (regularSupport C.region (Subtype.val '' S)) := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [add_comm, add_left_comm, add_assoc] using hw
    exact hs ▸ this
  obtain ⟨w, hw⟩ := hne
  have hw₀ : w + alpha₀.1 ∈ properVertices
      (regularSupport C.region (Subtype.val '' S₀)) :=
    hproperperiod S₀ alpha₀ hper₀ hw
  have hp : w + alpha₀.1 + beta.1 ∈ properVertices
      (regularSupport C.region (Subtype.val '' S₁)) := by
    simpa [add_comm] using hbeta (w + alpha₀.1) hw₀
  have hq : w + beta.1 + alpha₁.1 ∈ properVertices
      (regularSupport C.region (Subtype.val '' S₁)) :=
    hproperperiod S₁ alpha₁ hper₁ (by simpa [add_comm] using hbeta w hw)
  have hpTV : w + alpha₀.1 + beta.1 ∈ C.translatedVertices := hprov₁ hp
  have hqTV : w + beta.1 + alpha₁.1 ∈ C.translatedVertices := hprov₁ hq
  let aw : ControlledDisplacement C :=
    C.translatedVertexPoint ⟨w, hprov₀ hw⟩
  have hmap : mapTranslatedVertex phi ⟨w + alpha₀.1 + beta.1, hpTV⟩ =
      mapTranslatedVertex phi ⟨w + beta.1 + alpha₁.1, hqTV⟩ := by
    rw [mapTranslatedVertex_eq_mapPoint, mapTranslatedVertex_eq_mapPoint]
    have hleft : C.translatedVertexPoint ⟨w + alpha₀.1 + beta.1, hpTV⟩ =
        ⟨aw.1 + alpha₀.1 + beta.1,
          C.coordinateSpace.add_mem (C.coordinateSpace.add_mem aw.2.1 alpha₀.2.1) beta.2.1,
          C.coordinateSpace.add_mem (C.coordinateSpace.add_mem aw.2.2 alpha₀.2.2) beta.2.2⟩ := by
      apply Subtype.ext
      change w + alpha₀.1 + beta.1 = (aw : Tiling.Plane) + alpha₀.1 + beta.1
      dsimp [aw, ApproximationContext.translatedVertexPoint]
    have hright : C.translatedVertexPoint ⟨w + beta.1 + alpha₁.1, hqTV⟩ =
        ⟨aw.1 + beta.1 + alpha₁.1,
          C.coordinateSpace.add_mem (C.coordinateSpace.add_mem aw.2.1 beta.2.1) alpha₁.2.1,
          C.coordinateSpace.add_mem (C.coordinateSpace.add_mem aw.2.2 beta.2.2) alpha₁.2.2⟩ := by
      apply Subtype.ext
      change w + beta.1 + alpha₁.1 = (aw : Tiling.Plane) + beta.1 + alpha₁.1
      dsimp [aw, ApproximationContext.translatedVertexPoint]
    rw [hleft, hright, mapPoint_three_add, mapPoint_three_add, hmap₀, hmap₁]
    ac_rfl
  have hpqsub : (⟨w + alpha₀.1 + beta.1, hpTV⟩ : ↥C.translatedVertices) =
      ⟨w + beta.1 + alpha₁.1, hqTV⟩ :=
    deformation_injectiveOnTranslatedVertices P phi hphi hmap
  have hpq : w + alpha₀.1 + beta.1 = w + beta.1 + alpha₁.1 :=
    congrArg (fun z : ↥C.translatedVertices => (z : Tiling.Plane)) hpqsub
  apply Subtype.ext
  have hcancel := congrArg (fun z : Tiling.Plane => z - w - beta.1) hpq
  simpa [add_assoc, add_left_comm, add_comm] using hcancel


theorem periodLifts_synchronizeFamily :
    ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ {I : Type} (base : I) (phase : I → Set ↥C.centres)
      (alpha beta : I → ControlledDisplacement C)
      (imagePeriod : Tiling.Plane),
      (∀ i, mapPoint phi (alpha i) = imagePeriod) →
      (∀ i, (alpha i).1 +ᵥ Subtype.val '' phase i =
        Subtype.val '' phase i) →
      (∀ i, regularSupport C.region (Subtype.val '' phase i) =
        (beta i).1 +ᵥ regularSupport C.region (Subtype.val '' phase base)) →
      (properVertices (regularSupport C.region
        (Subtype.val '' phase base))).Nonempty →
      ∀ i, alpha i = alpha base := by
  intro C P phi hphi I base phase alpha beta imagePeriod hmap hperiod hsupp hnonempty i
  have heq : alpha base = alpha i := by
    refine periodLifts_eq_of_properVertexShift P phi hphi
      (phase base) (phase i) (alpha base) (alpha i) (beta i) imagePeriod
      (hmap base) (hmap i) (hperiod base) (hperiod i)
      (properVertices_regularSupport_image_subset_translatedVertices C P.source_tilesOn
        (phase base))
      (properVertices_regularSupport_image_subset_translatedVertices C P.source_tilesOn
        (phase i)) ?_ hnonempty
    intro w hw
    have hproper := Tiling.AxisParallel.properVertices_vadd_eq (beta i).1
      (regularSupport C.region (Subtype.val '' phase base))
    have hsprop := congrArg properVertices (hsupp i)
    rw [hsprop, hproper]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [add_comm, add_left_comm, add_assoc] using hw
  exact heq.symm


end Tiling.AxisParallel.Approximation
