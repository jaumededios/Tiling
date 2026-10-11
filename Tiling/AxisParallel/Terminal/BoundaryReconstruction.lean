import Tiling.AxisParallel.Terminal.BoundaryCore
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.Geometry.LocalLine
import Tiling.Geometry.PolygonalTopology
import Mathlib.Topology.Connected.Basic

/-!
# Boundary reconstruction

The elementary extensionality statement for the public boundary code is proved here.  The geometric
reconstruction theorem is intentionally kept out of the definition-only core.
-/

open Filter Set Topology
open scoped Pointwise

namespace Tiling.AxisParallel.Terminal

private def inOpenQuadrant
    (x z : Tiling.Plane) (q : Bool × Bool) : Prop :=
  (if q.1 then x.re < z.re else z.re < x.re) ∧
    (if q.2 then x.im < z.im else z.im < x.im)

private theorem mem_localCone_iff
    {F : Set Tiling.Plane} {x : Tiling.Plane}
    (hF : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F)
    (hx : Tiling.AxisParallel.IsProperVertex F x) (q : Bool × Bool) :
    q ∈ localCone F x hF hx ↔
      ∃ r : ℝ, 0 < r ∧ ∀ z : Tiling.Plane,
        z ∈ Metric.ball x r → inOpenQuadrant x z q → z ∈ F := by
  rfl

private theorem BoundaryCode.eq_of_components
    {B C : BoundaryCode}
    (hvertices : B.properVertexSet = C.properVertexSet)
    (hcones : B.coneGraph = C.coneGraph)
    (hlines : B.completeLines = C.completeLines) : B = C := by
  cases B with
  | mk verticesB coneB linesB =>
    cases C with
    | mk verticesC coneC linesC =>
      change verticesB = verticesC at hvertices
      change linesB = linesC at hlines
      change (BoundaryCode.mk verticesB coneB linesB).coneGraph =
        (BoundaryCode.mk verticesC coneC linesC).coneGraph at hcones
      subst verticesC
      subst linesC
      congr
      funext x
      have hx : (x.1, coneB x) ∈
          (BoundaryCode.mk verticesB coneB linesB).coneGraph :=
        ⟨x.property, rfl⟩
      rw [hcones] at hx
      rcases hx with ⟨_hxmem, hxeq⟩
      simpa only [Subtype.coe_eta] using hxeq

private theorem eq_of_frontier_eq_of_eventually_mem_iff
    {S T : Set Tiling.Plane}
    (hSOpen : IsOpen S) (hTOpen : IsOpen T)
    (hFrontier : frontier S = frontier T)
    (hLocal : ∀ x ∈ frontier S, ∀ᶠ z in 𝓝 x, (z ∈ S ↔ z ∈ T))
    (hFrontierNonempty : (frontier S).Nonempty) : S = T := by
  let A : Set Tiling.Plane := {x | x ∈ S ↔ x ∈ T}
  have hAOpen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro x hxA
    by_cases hxFrontier : x ∈ frontier S
    · change ∀ᶠ z in 𝓝 x, (z ∈ S ↔ z ∈ T)
      exact hLocal x hxFrontier
    · have hxNotFrontierT : x ∉ frontier T := by simpa only [← hFrontier]
      have hxSCases : x ∈ interior S ∨ x ∈ interior Sᶜ := by
        have hx : x ∈ (frontier S)ᶜ := hxFrontier
        rwa [compl_frontier_eq_union_interior, mem_union] at hx
      have hxTCases : x ∈ interior T ∨ x ∈ interior Tᶜ := by
        have hx : x ∈ (frontier T)ᶜ := hxNotFrontierT
        rwa [compl_frontier_eq_union_interior, mem_union] at hx
      rcases hxSCases with hxS | hxSc <;> rcases hxTCases with hxT | hxTc
      · apply Filter.mem_of_superset (inter_mem (IsOpen.mem_nhds isOpen_interior hxS)
          (IsOpen.mem_nhds isOpen_interior hxT))
        rintro z ⟨hzS, hzT⟩
        exact ⟨fun _ => interior_subset hzT, fun _ => interior_subset hzS⟩
      · exact False.elim ((interior_subset hxTc) (hxA.mp (interior_subset hxS)))
      · exact False.elim ((interior_subset hxSc) (hxA.mpr (interior_subset hxT)))
      · apply Filter.mem_of_superset (inter_mem (IsOpen.mem_nhds isOpen_interior hxSc)
          (IsOpen.mem_nhds isOpen_interior hxTc))
        rintro z ⟨hzSc, hzTc⟩
        exact ⟨fun hzS => False.elim ((interior_subset hzSc) hzS),
          fun hzT => False.elim ((interior_subset hzTc) hzT)⟩
  have hAComplOpen : IsOpen Aᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hxAc
    have hxNotA : ¬(x ∈ S ↔ x ∈ T) := by
      simpa only [A, mem_compl_iff, mem_ofPred_eq] using hxAc
    have hxNotFrontier : x ∉ frontier S := by
      intro hxFrontier
      have hxNotS : x ∉ S := by
        intro hxS
        exact Set.disjoint_left.1 disjoint_interior_frontier
          (hSOpen.mem_nhds hxS |> mem_interior_iff_mem_nhds.mpr) hxFrontier
      have hxNotT : x ∉ T := by
        intro hxT
        have hxFrontierT : x ∈ frontier T := hFrontier ▸ hxFrontier
        exact Set.disjoint_left.1 disjoint_interior_frontier
          (hTOpen.mem_nhds hxT |> mem_interior_iff_mem_nhds.mpr) hxFrontierT
      exact hxNotA ⟨fun hxS => (hxNotS hxS).elim, fun hxT => (hxNotT hxT).elim⟩
    have hxNotFrontierT : x ∉ frontier T := by simpa only [← hFrontier]
    have hxSCases : x ∈ interior S ∨ x ∈ interior Sᶜ := by
      have hx : x ∈ (frontier S)ᶜ := hxNotFrontier
      rwa [compl_frontier_eq_union_interior, mem_union] at hx
    have hxTCases : x ∈ interior T ∨ x ∈ interior Tᶜ := by
      have hx : x ∈ (frontier T)ᶜ := hxNotFrontierT
      rwa [compl_frontier_eq_union_interior, mem_union] at hx
    rcases hxSCases with hxS | hxSc <;> rcases hxTCases with hxT | hxTc
    · exact False.elim (hxNotA ⟨fun _ => interior_subset hxT, fun _ => interior_subset hxS⟩)
    · apply Filter.mem_of_superset (inter_mem (IsOpen.mem_nhds isOpen_interior hxS)
          (IsOpen.mem_nhds isOpen_interior hxTc))
      rintro z ⟨hzS, hzTc⟩
      change ¬(z ∈ S ↔ z ∈ T)
      intro h
      exact (interior_subset hzTc) (h.mp (interior_subset hzS))
    · apply Filter.mem_of_superset (inter_mem (IsOpen.mem_nhds isOpen_interior hxSc)
          (IsOpen.mem_nhds isOpen_interior hxT))
      rintro z ⟨hzSc, hzT⟩
      change ¬(z ∈ S ↔ z ∈ T)
      intro h
      exact (interior_subset hzSc) (h.mpr (interior_subset hzT))
    · exact False.elim (hxNotA ⟨
        fun hxS => False.elim ((interior_subset hxSc) hxS),
        fun hxT => False.elim ((interior_subset hxTc) hxT)⟩)
  have hAClosed : IsClosed A := by simpa using hAComplOpen.isClosed_compl
  have hAClopen : IsClopen A := ⟨hAClosed, hAOpen⟩
  have hANonempty : A.Nonempty := by
    obtain ⟨x, hx⟩ := hFrontierNonempty
    refine ⟨x, ?_⟩
    have hxT : x ∈ frontier T := hFrontier ▸ hx
    have hxNotS : x ∉ S := fun hxS =>
      Set.disjoint_left.1 disjoint_interior_frontier
        (mem_interior_iff_mem_nhds.mpr (hSOpen.mem_nhds hxS)) hx
    have hxNotT : x ∉ T := fun hxMemT =>
      Set.disjoint_left.1 disjoint_interior_frontier
        (mem_interior_iff_mem_nhds.mpr (hTOpen.mem_nhds hxMemT)) hxT
    exact ⟨fun hxS => (hxNotS hxS).elim, fun hxT => (hxNotT hxT).elim⟩
  have hAUniv : A = Set.univ := IsClopen.eq_univ hAClopen hANonempty
  ext x
  exact (show x ∈ A from hAUniv.symm ▸ Set.mem_univ x)

private theorem isPreconnected_ball_inter_openQuadrant
    (x : Tiling.Plane) (q : Bool × Bool) (r : ℝ) :
    IsPreconnected (Metric.ball x r ∩ {z | inOpenQuadrant x z q}) := by
  rcases q with ⟨qre, qim⟩
  cases qre <;> cases qim
  · simpa only [inOpenQuadrant, Bool.false_eq_true, ↓reduceIte, ofPred_and,
      Complex.reLm_coe, Complex.imLm_coe, inter_assoc] using
      ((convex_ball x r).inter
        ((convex_halfSpace_lt Complex.reLm.isLinear x.re).inter
          (convex_halfSpace_lt Complex.imLm.isLinear x.im))).isPreconnected
  · simpa only [inOpenQuadrant, Bool.false_eq_true, ↓reduceIte, ofPred_and,
      Complex.reLm_coe, Complex.imLm_coe, inter_assoc] using
      ((convex_ball x r).inter
        ((convex_halfSpace_lt Complex.reLm.isLinear x.re).inter
          (convex_halfSpace_gt Complex.imLm.isLinear x.im))).isPreconnected
  · simpa only [inOpenQuadrant, Bool.false_eq_true, ↓reduceIte, ofPred_and,
      Complex.reLm_coe, Complex.imLm_coe, inter_assoc] using
      ((convex_ball x r).inter
        ((convex_halfSpace_gt Complex.reLm.isLinear x.re).inter
          (convex_halfSpace_lt Complex.imLm.isLinear x.im))).isPreconnected
  · simpa only [inOpenQuadrant, ↓reduceIte, ofPred_and,
      Complex.reLm_coe, Complex.imLm_coe, inter_assoc] using
      ((convex_ball x r).inter
        ((convex_halfSpace_gt Complex.reLm.isLinear x.re).inter
          (convex_halfSpace_gt Complex.imLm.isLinear x.im))).isPreconnected

private theorem ball_inter_openQuadrant_nonempty
    (x : Tiling.Plane) (q : Bool × Bool) {r : ℝ} (hr : 0 < r) :
    (Metric.ball x r ∩ {z | inOpenQuadrant x z q}).Nonempty := by
  let d : ℝ := r / 4
  have hd : 0 < d := div_pos hr (by norm_num)
  rcases q with ⟨qre, qim⟩
  let w : Tiling.Plane :=
    ⟨if qre then d else -d, if qim then d else -d⟩
  cases qre <;> cases qim
  all_goals
    refine ⟨x + w, ?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have hwNorm : ‖w‖ < r := by
        rw [Complex.norm_def, Real.sqrt_lt' hr]
        simp only [w, Bool.false_eq_true, ↓reduceIte, Complex.normSq_apply,
          neg_mul_neg]
        dsimp only [d]
        nlinarith [sq_pos_of_pos hr]
      simpa only [add_sub_cancel_left] using hwNorm
    · dsimp only [w]
      simp only [inOpenQuadrant, Bool.false_eq_true, ↓reduceIte, mem_ofPred_eq,
        Complex.add_re, Complex.add_im]
      constructor <;> linarith

private theorem ne_coordinates_of_inOpenQuadrant
    {x z : Tiling.Plane} {q : Bool × Bool}
    (hz : inOpenQuadrant x z q) : z.re ≠ x.re ∧ z.im ≠ x.im := by
  rcases q with ⟨qre, qim⟩
  cases qre <;> cases qim <;>
    simp only [inOpenQuadrant, Bool.false_eq_true, ↓reduceIte] at hz <;>
    constructor <;> linarith

private theorem eventually_mem_iff_mem_localCone_at_proper
    {F : Set Tiling.Plane} {x : Tiling.Plane}
    (hF : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F)
    (hx : Tiling.AxisParallel.IsProperVertex F x) (q : Bool × Bool) :
    ∀ᶠ z in 𝓝 x,
      inOpenQuadrant x z q → (z ∈ F ↔ q ∈ localCone F x hF hx) := by
  obtain ⟨r, hr, hCross⟩ :=
    Tiling.AxisParallel.exists_ball_frontier_subset_axisCross hF x
  let C : Set Tiling.Plane := Metric.ball x r ∩ {z | inOpenQuadrant x z q}
  have hCDisjoint : Disjoint C (frontier F) := by
    refine Set.disjoint_left.2 fun z hzC hzFrontier => ?_
    have hzCross := hCross z hzC.1 hzFrontier
    have hzNe := ne_coordinates_of_inOpenQuadrant hzC.2
    exact hzCross.elim (fun h => hzNe.1 h) (fun h => hzNe.2 h)
  have hCases : C ⊆ interior F ∨ C ⊆ interior Fᶜ :=
    IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      (isPreconnected_ball_inter_openQuadrant x q r) hCDisjoint
  rcases hCases with hInside | hOutside
  · have hq : q ∈ localCone F x hF hx := by
      apply (mem_localCone_iff hF hx q).2
      exact ⟨r, hr, fun z hzBall hzQuadrant =>
        interior_subset (hInside ⟨hzBall, hzQuadrant⟩)⟩
    filter_upwards [Metric.ball_mem_nhds x hr] with z hzBall hzQuadrant
    exact ⟨fun _ => hq, fun _ => interior_subset (hInside ⟨hzBall, hzQuadrant⟩)⟩
  · have hnq : q ∉ localCone F x hF hx := by
      intro hq
      obtain ⟨s, hs, hqInside⟩ := (mem_localCone_iff hF hx q).1 hq
      have hmin : 0 < min r s := lt_min hr hs
      obtain ⟨z, hzBall, hzQuadrant⟩ :=
        ball_inter_openQuadrant_nonempty x q hmin
      have hzBallR : z ∈ Metric.ball x r :=
        Metric.ball_subset_ball (min_le_left r s) hzBall
      have hzBallS : z ∈ Metric.ball x s :=
        Metric.ball_subset_ball (min_le_right r s) hzBall
      exact (interior_subset (hOutside ⟨hzBallR, hzQuadrant⟩))
        (hqInside z hzBallS hzQuadrant)
    filter_upwards [Metric.ball_mem_nhds x hr] with z hzBall hzQuadrant
    exact ⟨fun hzF => False.elim ((interior_subset
      (hOutside ⟨hzBall, hzQuadrant⟩)) hzF), fun hq => False.elim (hnq hq)⟩

private theorem localCone_eq_of_boundaryCode_eq_vadd
    {F₀ F₁ : Set Tiling.Plane} {a x : Tiling.Plane}
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hx₀ : Tiling.AxisParallel.IsProperVertex F₀ x)
    (hx₁ : Tiling.AxisParallel.IsProperVertex F₁ (a + x))
    (hCode : boundaryCode F₁ hF₁ = (boundaryCode F₀ hF₀).vadd a) :
    localCone F₁ (a + x) hF₁ hx₁ = localCone F₀ x hF₀ hx₀ := by
  have hGraph := congrArg BoundaryCode.coneGraph hCode
  have hmem :
      (a + x, localCone F₁ (a + x) hF₁ hx₁) ∈
        (boundaryCode F₁ hF₁).coneGraph := by
    exact ⟨hx₁, rfl⟩
  rw [hGraph] at hmem
  obtain ⟨_hx, heq⟩ := hmem
  have hxSource : Tiling.AxisParallel.IsProperVertex F₀ (a + x - a) := by
    change a + x - a ∈ Tiling.AxisParallel.properVertices F₀
    rcases _hx with ⟨y, hy, hxy⟩
    change y ∈ Tiling.AxisParallel.properVertices F₀ at hy
    rw [← hxy]
    simpa only [vadd_eq_add, add_sub_cancel_left] using hy
  change localCone F₁ (a + x) hF₁ hx₁ =
    localCone F₀ (a + x - a) hF₀ hxSource at heq
  have hax : a + x - a = x := by abel
  simpa only [localCone, hax] using heq

private def HasAxisBoundaryGerm
    (axis : Tiling.AxisParallel.Axis) (F : Set Tiling.Plane)
    (x : Tiling.Plane) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.ball x r,
    (z ∈ frontier F ↔
      axis.transverseCoord z = axis.transverseCoord x)

private theorem HasAxisBoundaryGerm.mem_frontier
    {axis : Tiling.AxisParallel.Axis} {F : Set Tiling.Plane}
    {x : Tiling.Plane} (h : HasAxisBoundaryGerm axis F x) :
    x ∈ frontier F := by
  obtain ⟨r, hr, h⟩ := h
  exact (h x (Metric.mem_ball_self hr)).2 rfl

private theorem affineLine_eq_horizontal
    {x v : Tiling.Plane} (hv : v ≠ 0) (hvim : v.im = 0) :
    Tiling.affineLine x v = {z | z.im = x.im} := by
  have hvre : v.re ≠ 0 := by
    intro hvre
    apply hv
    apply Complex.ext <;> simp [hvre, hvim]
  ext z
  simp only [Tiling.mem_affineLine, Tiling.signedSide, Tiling.planarCross,
    mem_ofPred_eq, hvim, zero_mul, sub_zero]
  constructor
  · intro h
    apply (mul_left_cancel₀ hvre)
    linarith
  · intro h
    rw [h]
    ring

private theorem affineLine_eq_vertical
    {x v : Tiling.Plane} (hv : v ≠ 0) (hvre : v.re = 0) :
    Tiling.affineLine x v = {z | z.re = x.re} := by
  have hvim : v.im ≠ 0 := by
    intro hvim
    apply hv
    apply Complex.ext <;> simp [hvre, hvim]
  ext z
  simp only [Tiling.mem_affineLine, Tiling.signedSide, Tiling.planarCross,
    mem_ofPred_eq, hvre, zero_mul, zero_sub]
  constructor
  · intro h
    apply (mul_left_cancel₀ hvim)
    linarith
  · intro h
    rw [h]
    ring

private theorem exists_axisBoundaryGerm_of_not_proper
    {F : Set Tiling.Plane}
    (hF : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F)
    {x : Tiling.Plane} (hxFrontier : x ∈ frontier F)
    (hxNotProper : ¬Tiling.AxisParallel.IsProperVertex F x) :
    HasAxisBoundaryGerm Tiling.AxisParallel.Axis.horizontal F x ∨
      HasAxisBoundaryGerm Tiling.AxisParallel.Axis.vertical F x := by
  have hxStraight : Tiling.BoundaryLocallyStraightAt F x := by
    by_contra hx
    exact hxNotProper ⟨hxFrontier, hx⟩
  obtain ⟨L, hxL, hdim, hlocal⟩ := hxStraight
  obtain ⟨v, hv, r, hr, hline⟩ :=
    Tiling.AffineSubspace.exists_ball_frontier_iff_affineLine hxL hdim hlocal
  obtain ⟨s, hs, hcross⟩ :=
    Tiling.AxisParallel.exists_ball_frontier_subset_axisCross hF x
  let t : ℝ := min r s / (2 * (‖v‖ + 1))
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have htNorm : t * ‖v‖ < min r s := by
    dsimp only [t]
    have hvnorm : 0 ≤ ‖v‖ := norm_nonneg v
    have hmin : 0 < min r s := lt_min hr hs
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (‖v‖ + 1))).2
    nlinarith
  let z : Tiling.Plane := x + t • v
  have hzDist : dist z x = t * ‖v‖ := by
    simp only [z, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht]
  have hzBallR : z ∈ Metric.ball x r := by
    rw [Metric.mem_ball, hzDist]
    exact htNorm.trans_le (min_le_left r s)
  have hzBallS : z ∈ Metric.ball x s := by
    rw [Metric.mem_ball, hzDist]
    exact htNorm.trans_le (min_le_right r s)
  have hzFrontier : z ∈ frontier F :=
    (hline z hzBallR).2 (Tiling.vadd_smul_mem_affineLine x v t)
  have hzCross := hcross z hzBallS hzFrontier
  have hvCoord : v.re = 0 ∨ v.im = 0 := by
    rcases hzCross with hzre | hzim
    · left
      have : t * v.re = 0 := by
        simpa only [z, Complex.add_re, Complex.smul_re, smul_eq_mul,
          add_eq_left] using hzre
      exact (mul_eq_zero.mp this).resolve_left ht.ne'
    · right
      have : t * v.im = 0 := by
        simpa only [z, Complex.add_im, Complex.smul_im, smul_eq_mul,
          add_eq_left] using hzim
      exact (mul_eq_zero.mp this).resolve_left ht.ne'
  rcases hvCoord with hvre | hvim
  · right
    refine ⟨min r s, lt_min hr hs, fun w hw => ?_⟩
    have hwR := Metric.ball_subset_ball (min_le_left r s) hw
    simpa only [Tiling.AxisParallel.Axis.transverseCoord,
      affineLine_eq_vertical hv hvre, mem_ofPred_eq] using hline w hwR
  · left
    refine ⟨min r s, lt_min hr hs, fun w hw => ?_⟩
    have hwR := Metric.ball_subset_ball (min_le_left r s) hw
    simpa only [Tiling.AxisParallel.Axis.transverseCoord,
      affineLine_eq_horizontal hv hvim, mem_ofPred_eq] using hline w hwR

private theorem HasAxisBoundaryGerm.of_mem_ball_of_transverseCoord_eq
    {axis : Tiling.AxisParallel.Axis} {F : Set Tiling.Plane}
    {x y : Tiling.Plane} {r : ℝ}
    (h : ∀ z ∈ Metric.ball x r,
      (z ∈ frontier F ↔
        axis.transverseCoord z = axis.transverseCoord x))
    (hy : y ∈ Metric.ball x r)
    (hyCoord : axis.transverseCoord y = axis.transverseCoord x) :
    HasAxisBoundaryGerm axis F y := by
  let s : ℝ := r - dist y x
  have hs : 0 < s := by
    dsimp only [s]
    apply sub_pos.mpr
    simpa only [Metric.mem_ball] using hy
  refine ⟨s, hs, fun z hz => ?_⟩
  have hzX : z ∈ Metric.ball x r := by
    rw [Metric.mem_ball] at hz ⊢
    calc
      dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ < s + dist y x := by linarith
      _ = r := by simp [s]
  rw [h z hzX, hyCoord]

private theorem not_both_axisBoundaryGerms
    {F : Set Tiling.Plane} {x : Tiling.Plane} :
    ¬(HasAxisBoundaryGerm Tiling.AxisParallel.Axis.horizontal F x ∧
      HasAxisBoundaryGerm Tiling.AxisParallel.Axis.vertical F x) := by
  rintro ⟨hHorizontal, hVertical⟩
  obtain ⟨r, hr, hHorizontal⟩ := hHorizontal
  obtain ⟨s, hs, hVertical⟩ := hVertical
  let d : ℝ := min r s / 2
  have hd : 0 < d := div_pos (lt_min hr hs) (by norm_num)
  let z : Tiling.Plane := x + ⟨d, 0⟩
  have hzDist : dist z x = d := by
    rw [dist_eq_norm]
    simp only [z, add_sub_cancel_left, Complex.norm_def,
      Complex.normSq_apply, mul_zero, add_zero]
    rw [show d * d = d ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_pos hd]
  have hzBallR : z ∈ Metric.ball x r := by
    rw [Metric.mem_ball, hzDist]
    exact (half_lt_self (lt_min hr hs)).trans_le (min_le_left r s)
  have hzBallS : z ∈ Metric.ball x s := by
    rw [Metric.mem_ball, hzDist]
    exact (half_lt_self (lt_min hr hs)).trans_le (min_le_right r s)
  have hzFrontier : z ∈ frontier F := by
    apply (hHorizontal z hzBallR).2
    simp [Tiling.AxisParallel.Axis.transverseCoord, z]
  have hzRe := (hVertical z hzBallS).1 hzFrontier
  simp only [Tiling.AxisParallel.Axis.transverseCoord, z, Complex.add_re] at hzRe
  linarith

private theorem HasAxisBoundaryGerm.boundaryLocallyStraightAt
    {axis : Tiling.AxisParallel.Axis} {F : Set Tiling.Plane}
    {x : Tiling.Plane} (h : HasAxisBoundaryGerm axis F x) :
    Tiling.BoundaryLocallyStraightAt F x := by
  obtain ⟨r, hr, hlocal⟩ := h
  refine ⟨Tiling.AxisParallel.properVertexAxisLine axis x,
    (Tiling.AxisParallel.mem_properVertexAxisLine_iff axis x x).2 rfl, ?_, ?_⟩
  · rw [Tiling.AxisParallel.properVertexAxisLine, AffineSubspace.direction_mk']
    exact finrank_span_singleton (Tiling.AxisParallel.properVertexAxisVector_ne_zero axis)
  · filter_upwards [Metric.ball_mem_nhds x hr] with z hz
    rw [hlocal z hz]
    exact (Tiling.AxisParallel.mem_properVertexAxisLine_iff axis x z).symm

private theorem HasAxisBoundaryGerm.not_isProperVertex
    {axis : Tiling.AxisParallel.Axis} {F : Set Tiling.Plane}
    {x : Tiling.Plane} (h : HasAxisBoundaryGerm axis F x) :
    ¬Tiling.AxisParallel.IsProperVertex F x := by
  exact fun hx => hx.2 h.boundaryLocallyStraightAt

private def axisPoint
    (axis : Tiling.AxisParallel.Axis) (level t : ℝ) : Tiling.Plane :=
  match axis with
  | .horizontal => (t : ℂ) + (level : ℂ) * Complex.I
  | .vertical => (level : ℂ) + (t : ℂ) * Complex.I

@[simp] private theorem axisPoint_coord
    (axis : Tiling.AxisParallel.Axis) (level t : ℝ) :
    axis.coord (axisPoint axis level t) = t := by
  cases axis <;> simp [axisPoint, Tiling.AxisParallel.Axis.coord]

@[simp] private theorem axisPoint_transverseCoord
    (axis : Tiling.AxisParallel.Axis) (level t : ℝ) :
    axis.transverseCoord (axisPoint axis level t) = level := by
  cases axis <;> simp [axisPoint, Tiling.AxisParallel.Axis.transverseCoord]

private theorem dist_axisPoint
    (axis : Tiling.AxisParallel.Axis) (level s t : ℝ) :
    dist (axisPoint axis level s) (axisPoint axis level t) = dist s t := by
  rw [dist_eq_norm, Real.dist_eq]
  cases axis
  · rw [show axisPoint .horizontal level s - axisPoint .horizontal level t =
        ((s - t : ℝ) : ℂ) by
      apply Complex.ext <;> simp [axisPoint]]
    rw [Complex.norm_real, Real.norm_eq_abs]
  · rw [show axisPoint .vertical level s - axisPoint .vertical level t =
        ((s - t : ℝ) : ℂ) * Complex.I by
      apply Complex.ext <;> simp [axisPoint]]
    rw [norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I,
      mul_one]

private theorem continuous_axisPoint
    (axis : Tiling.AxisParallel.Axis) (level : ℝ) :
    Continuous (axisPoint axis level) := by
  cases axis
  · change Continuous (fun u : ℝ =>
        (u : ℂ) + (level : ℂ) * Complex.I)
    exact Complex.continuous_ofReal.add continuous_const
  · change Continuous (fun u : ℝ =>
        (level : ℂ) + (u : ℂ) * Complex.I)
    exact continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const)

private theorem eventually_axisBoundaryGerm_iff_of_not_proper
    {F : Set Tiling.Plane}
    (hF : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F)
    (axis : Tiling.AxisParallel.Axis) (level t : ℝ)
    (ht : ¬Tiling.AxisParallel.IsProperVertex F (axisPoint axis level t)) :
    ∀ᶠ s in nhds t,
      (HasAxisBoundaryGerm axis F (axisPoint axis level s) ↔
        HasAxisBoundaryGerm axis F (axisPoint axis level t)) := by
  by_cases hGerm : HasAxisBoundaryGerm axis F (axisPoint axis level t)
  · have hGermAt := hGerm
    obtain ⟨r, hr, hlocal⟩ := hGerm
    filter_upwards [Metric.ball_mem_nhds t hr] with s hs
    constructor
    · intro _
      exact hGermAt
    · intro _
      apply HasAxisBoundaryGerm.of_mem_ball_of_transverseCoord_eq hlocal
      · rw [Metric.mem_ball, dist_axisPoint]
        simpa only [Metric.mem_ball] using hs
      · simp
  · have hxCases : axisPoint axis level t ∉ frontier F ∨
        HasAxisBoundaryGerm axis.swap F (axisPoint axis level t) := by
      by_cases hxFrontier : axisPoint axis level t ∈ frontier F
      · right
        have hAxes := exists_axisBoundaryGerm_of_not_proper hF hxFrontier ht
        cases axis with
        | horizontal =>
            exact hAxes.resolve_left hGerm
        | vertical =>
            exact hAxes.resolve_right hGerm
      · exact Or.inl hxFrontier
    rcases hxCases with hxNotFrontier | hOther
    · have hEventually : ∀ᶠ s in nhds t,
          axisPoint axis level s ∉ frontier F := by
        have hOpen : IsOpen (frontier F)ᶜ := isClosed_frontier.isOpen_compl
        exact (continuous_axisPoint axis level).continuousAt.eventually
          (hOpen.mem_nhds hxNotFrontier)
      filter_upwards [hEventually] with s hs
      constructor
      · intro hsGerm
        exact (hs hsGerm.mem_frontier).elim
      · intro htGerm
        exact (hGerm htGerm).elim
    · obtain ⟨r, hr, hOtherLocal⟩ := hOther
      filter_upwards [Metric.ball_mem_nhds t hr] with s hs
      constructor
      · intro hsGerm
        have hsFrontier := hsGerm.mem_frontier
        have hsOtherCoord :
            axis.swap.transverseCoord (axisPoint axis level s) =
              axis.swap.transverseCoord (axisPoint axis level t) := by
          apply (hOtherLocal _ ?_).1 hsFrontier
          rw [Metric.mem_ball, dist_axisPoint]
          simpa only [Metric.mem_ball] using hs
        have hst : s = t := by
          cases axis <;> simpa [Tiling.AxisParallel.Axis.swap,
            Tiling.AxisParallel.Axis.transverseCoord, axisPoint] using hsOtherCoord
        subst s
        exact (hGerm hsGerm).elim
      · intro htGerm
        exact (hGerm htGerm).elim

private theorem isClosed_properVertices (F : Set Tiling.Plane) :
    IsClosed (Tiling.AxisParallel.properVertices F) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  change ¬Tiling.AxisParallel.IsProperVertex F x at hx
  by_cases hxFrontier : x ∈ frontier F
  · have hxStraight : Tiling.BoundaryLocallyStraightAt F x := by
      by_contra h
      exact hx ⟨hxFrontier, h⟩
    obtain ⟨L, hxL, hdim, hlocal⟩ := hxStraight
    obtain ⟨U, hUsub, hUOpen, hxU⟩ := mem_nhds_iff.mp hlocal
    apply Filter.mem_of_superset (hUOpen.mem_nhds hxU)
    intro y hyU
    change ¬Tiling.AxisParallel.IsProperVertex F y
    rintro ⟨hyFrontier, hyNotStraight⟩
    apply hyNotStraight
    refine ⟨L, (hUsub hyU).mp hyFrontier, hdim, ?_⟩
    exact Filter.mem_of_superset (hUOpen.mem_nhds hyU) hUsub
  · apply Filter.mem_of_superset
      (isClosed_frontier.isOpen_compl.mem_nhds hxFrontier)
    intro y hy
    change ¬Tiling.AxisParallel.IsProperVertex F y
    exact fun h => hy h.1

private theorem axisBoundaryGerm_iff_of_uIcc_no_proper
    {F : Set Tiling.Plane}
    (hF : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F)
    (axis : Tiling.AxisParallel.Axis) (level u v : ℝ)
    (hNoProper : ∀ t ∈ Set.uIcc u v,
      ¬Tiling.AxisParallel.IsProperVertex F (axisPoint axis level t)) :
    HasAxisBoundaryGerm axis F (axisPoint axis level u) ↔
      HasAxisBoundaryGerm axis F (axisPoint axis level v) := by
  let G : Set ℝ :=
    {t | HasAxisBoundaryGerm axis F (axisPoint axis level t)}
  have hInterior (t : ℝ) (ht : t ∈ Set.uIcc u v) :
      t ∈ interior G ∨ t ∈ interior Gᶜ := by
    have hlocal := eventually_axisBoundaryGerm_iff_of_not_proper
      hF axis level t (hNoProper t ht)
    by_cases htGerm : HasAxisBoundaryGerm axis F (axisPoint axis level t)
    · left
      apply mem_interior_iff_mem_nhds.mpr
      filter_upwards [hlocal] with s hs
      change HasAxisBoundaryGerm axis F (axisPoint axis level s)
      exact hs.mpr htGerm
    · right
      apply mem_interior_iff_mem_nhds.mpr
      filter_upwards [hlocal] with s hs
      change ¬HasAxisBoundaryGerm axis F (axisPoint axis level s)
      exact fun h => htGerm (hs.mp h)
  have hCover : Set.uIcc u v ⊆ interior G ∪ interior Gᶜ := by
    intro t ht
    exact hInterior t ht
  have noMismatch
      (hu : HasAxisBoundaryGerm axis F (axisPoint axis level u))
      (hv : ¬HasAxisBoundaryGerm axis F (axisPoint axis level v)) : False := by
    have huInterior : u ∈ interior G := by
      rcases hInterior u Set.left_mem_uIcc with huI | huIc
      · exact huI
      · exact False.elim ((interior_subset huIc) hu)
    have hvInterior : v ∈ interior Gᶜ := by
      rcases hInterior v Set.right_mem_uIcc with hvI | hvIc
      · exact False.elim (hv (show v ∈ G from interior_subset hvI))
      · exact hvIc
    obtain ⟨w, _hwS, hwG, hwGc⟩ := isPreconnected_uIcc
      (interior G) (interior Gᶜ) isOpen_interior isOpen_interior hCover
      ⟨u, Set.left_mem_uIcc, huInterior⟩
      ⟨v, Set.right_mem_uIcc, hvInterior⟩
    exact (interior_subset hwGc) (interior_subset hwG)
  constructor
  · intro hu
    by_contra hv
    exact noMismatch hu hv
  · intro hv
    by_contra hu
    have hvInterior : v ∈ interior G := by
      rcases hInterior v Set.right_mem_uIcc with hvI | hvIc
      · exact hvI
      · exact False.elim ((interior_subset hvIc) hv)
    have huInterior : u ∈ interior Gᶜ := by
      rcases hInterior u Set.left_mem_uIcc with huI | huIc
      · exact False.elim (hu (show u ∈ G from interior_subset huI))
      · exact huIc
    obtain ⟨w, _hwS, hwG, hwGc⟩ := isPreconnected_uIcc
      (interior G) (interior Gᶜ) isOpen_interior isOpen_interior hCover
      ⟨v, Set.right_mem_uIcc, hvInterior⟩
      ⟨u, Set.left_mem_uIcc, huInterior⟩
    exact (interior_subset hwGc) (interior_subset hwG)

private theorem dense_ne_coordinates (p : Tiling.Plane) :
    Dense {z : Tiling.Plane | z.re ≠ p.re ∧ z.im ≠ p.im} := by
  rw [dense_iff_inter_open]
  intro U hU hUNonempty
  obtain ⟨w, hwU⟩ := hUNonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU w hwU
  by_cases hre : p.re ≤ w.re <;> by_cases him : p.im ≤ w.im
  · obtain ⟨z, hzBall, hzQ⟩ :=
      ball_inter_openQuadrant_nonempty w (true, true) hr
    refine ⟨z, hball hzBall, ?_⟩
    simp only [inOpenQuadrant, ↓reduceIte] at hzQ ⊢
    exact ⟨ne_of_gt (hre.trans_lt hzQ.1), ne_of_gt (him.trans_lt hzQ.2)⟩
  · obtain ⟨z, hzBall, hzQ⟩ :=
      ball_inter_openQuadrant_nonempty w (true, false) hr
    refine ⟨z, hball hzBall, ?_⟩
    simp only [inOpenQuadrant, Bool.false_eq_true, ↓reduceIte] at hzQ
    have hwim : w.im < p.im := lt_of_not_ge him
    exact ⟨ne_of_gt (hre.trans_lt hzQ.1), ne_of_lt (hzQ.2.trans hwim)⟩
  · obtain ⟨z, hzBall, hzQ⟩ :=
      ball_inter_openQuadrant_nonempty w (false, true) hr
    refine ⟨z, hball hzBall, ?_⟩
    simp only [inOpenQuadrant, Bool.false_eq_true, ↓reduceIte] at hzQ
    have hwre : w.re < p.re := lt_of_not_ge hre
    exact ⟨ne_of_lt (hzQ.1.trans hwre), ne_of_gt (him.trans_lt hzQ.2)⟩
  · obtain ⟨z, hzBall, hzQ⟩ :=
      ball_inter_openQuadrant_nonempty w (false, false) hr
    refine ⟨z, hball hzBall, ?_⟩
    simp only [inOpenQuadrant, Bool.false_eq_true, ↓reduceIte] at hzQ
    have hwre : w.re < p.re := lt_of_not_ge hre
    have hwim : w.im < p.im := lt_of_not_ge him
    exact ⟨ne_of_lt (hzQ.1.trans hwre), ne_of_lt (hzQ.2.trans hwim)⟩

private theorem eventually_mem_iff_of_regularOpen_of_off_cross
    {S T : Set Tiling.Plane} {p : Tiling.Plane}
    (hSOpen : IsOpen S) (hTOpen : IsOpen T)
    (hSRegular : interior (closure S) = S)
    (hTRegular : interior (closure T) = T)
    (hOffCross : ∀ᶠ z in nhds p,
      z.re ≠ p.re ∧ z.im ≠ p.im → (z ∈ S ↔ z ∈ T)) :
    ∀ᶠ z in nhds p, (z ∈ S ↔ z ∈ T) := by
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp hOffCross
  have oneDirection
      {A B : Set Tiling.Plane}
      (hAOpen : IsOpen A)
      (hBRegular : interior (closure B) = B)
      (hLocal : ∀ z ∈ Metric.ball p R,
        z.re ≠ p.re ∧ z.im ≠ p.im → (z ∈ A → z ∈ B)) :
      ∀ z ∈ Metric.ball p (R / 2), z ∈ A → z ∈ B := by
    intro z hzBall hzA
    obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.mp hAOpen z hzA
    have hzR : dist z p < R := by
      rw [Metric.mem_ball] at hzBall
      linarith
    let δ : ℝ := min (ε / 2) ((R - dist z p) / 2)
    have hδ : 0 < δ := by
      dsimp only [δ]
      exact lt_min (half_pos hε) (half_pos (sub_pos.mpr hzR))
    have hBallClosure : Metric.ball z δ ⊆ closure B := by
      intro w hwBall
      rw [mem_closure_iff]
      intro U hU hwU
      have hVOpen : IsOpen (U ∩ Metric.ball z δ) :=
        hU.inter Metric.isOpen_ball
      have hVNonempty : (U ∩ Metric.ball z δ).Nonempty :=
        ⟨w, hwU, hwBall⟩
      obtain ⟨y, hyD, hyU, hyBall⟩ :=
        (dense_ne_coordinates p).exists_mem_open hVOpen hVNonempty
      refine ⟨y, hyU, ?_⟩
      apply hLocal y
      · rw [Metric.mem_ball] at hyBall ⊢
        calc
          dist y p ≤ dist y z + dist z p := dist_triangle _ _ _
          _ < δ + dist z p := by linarith
          _ ≤ (R - dist z p) / 2 + dist z p := by
            gcongr
            exact min_le_right _ _
          _ < R := by linarith
      · exact hyD
      · apply hεA
        rw [Metric.mem_ball] at hyBall ⊢
        calc
          dist y z < δ := hyBall
          _ ≤ ε / 2 := min_le_left _ _
          _ < ε := half_lt_self hε
    rw [← hBRegular]
    exact interior_maximal hBallClosure Metric.isOpen_ball
      (Metric.mem_ball_self hδ)
  filter_upwards [Metric.ball_mem_nhds p (half_pos hR)] with z hzBall
  constructor
  · exact oneDirection hSOpen hTRegular (fun w hwR hwD =>
      (hball (by simpa only [Metric.mem_ball] using hwR) hwD).mp) z hzBall
  · exact oneDirection hTOpen hSRegular (fun w hwR hwD =>
      (hball (by simpa only [Metric.mem_ball] using hwR) hwD).mpr) z hzBall

private theorem mem_vadd_set_iff_vsub_mem
    {F : Set Tiling.Plane} (a z : Tiling.Plane) :
    z ∈ a +ᵥ F ↔ z - a ∈ F := by
  constructor
  · rintro ⟨y, hy, hay⟩
    rw [← hay]
    simpa only [vadd_eq_add, add_sub_cancel_left] using hy
  · intro hz
    refine ⟨z - a, hz, ?_⟩
    simp only [vadd_eq_add]
    abel

private theorem inOpenQuadrant_vsub
    (a x z : Tiling.Plane) (q : Bool × Bool) :
    inOpenQuadrant (a + x) z q ↔ inOpenQuadrant x (z - a) q := by
  rcases q with ⟨qre, qim⟩
  cases qre <;> cases qim <;>
    simp only [inOpenQuadrant, Bool.false_eq_true, ↓reduceIte,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;>
    constructor <;> rintro ⟨hre, him⟩ <;> constructor <;> linarith

private theorem exists_openQuadrant_of_ne_coordinates
    {x z : Tiling.Plane} (h : z.re ≠ x.re ∧ z.im ≠ x.im) :
    ∃ q : Bool × Bool, inOpenQuadrant x z q := by
  rcases lt_or_gt_of_ne h.1 with hre | hre <;>
    rcases lt_or_gt_of_ne h.2 with him | him
  · exact ⟨(false, false), hre, him⟩
  · exact ⟨(false, true), hre, him⟩
  · exact ⟨(true, false), hre, him⟩
  · exact ⟨(true, true), hre, him⟩

private theorem properVertex_vadd_iff_of_boundaryCode_eq
    {F₀ F₁ : Set Tiling.Plane} {a x : Tiling.Plane}
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hCode : boundaryCode F₁ hF₁ = (boundaryCode F₀ hF₀).vadd a) :
    Tiling.AxisParallel.IsProperVertex F₁ (a + x) ↔
      Tiling.AxisParallel.IsProperVertex F₀ x := by
  have hvertices := congrArg BoundaryCode.properVertexSet hCode
  change Tiling.AxisParallel.properVertices F₁ =
    a +ᵥ Tiling.AxisParallel.properVertices F₀ at hvertices
  change a + x ∈ Tiling.AxisParallel.properVertices F₁ ↔
    x ∈ Tiling.AxisParallel.properVertices F₀
  rw [hvertices]
  constructor
  · rintro ⟨y, hy, hay⟩
    have hyx : y = x := by
      change a + y = a + x at hay
      exact add_left_cancel hay
    simpa only [hyx] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem eventually_mem_iff_vadd_at_proper
    {F₀ F₁ : Set Tiling.Plane} {a x : Tiling.Plane}
    (hF₀Open : IsOpen F₀) (hF₁Open : IsOpen F₁)
    (hF₀Regular : interior (closure F₀) = F₀)
    (hF₁Regular : interior (closure F₁) = F₁)
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hx₀ : Tiling.AxisParallel.IsProperVertex F₀ x)
    (hx₁ : Tiling.AxisParallel.IsProperVertex F₁ (a + x))
    (hCode : boundaryCode F₁ hF₁ = (boundaryCode F₀ hF₀).vadd a) :
    ∀ᶠ z in nhds (a + x), (z ∈ F₁ ↔ z ∈ a +ᵥ F₀) := by
  have hCone := localCone_eq_of_boundaryCode_eq_vadd
    hF₀ hF₁ hx₀ hx₁ hCode
  have h₁All : ∀ᶠ z in nhds (a + x), ∀ q : Bool × Bool,
      inOpenQuadrant (a + x) z q →
        (z ∈ F₁ ↔ q ∈ localCone F₁ (a + x) hF₁ hx₁) := by
    rw [Filter.eventually_all]
    exact fun q => eventually_mem_iff_mem_localCone_at_proper hF₁ hx₁ q
  have h₀All : ∀ᶠ z in nhds x, ∀ q : Bool × Bool,
      inOpenQuadrant x z q →
        (z ∈ F₀ ↔ q ∈ localCone F₀ x hF₀ hx₀) := by
    rw [Filter.eventually_all]
    exact fun q => eventually_mem_iff_mem_localCone_at_proper hF₀ hx₀ q
  have hShift : Tendsto (fun z : Tiling.Plane => z - a)
      (nhds (a + x)) (nhds x) := by
    have hc : Tendsto (fun z : Tiling.Plane => z - a)
        (nhds (a + x)) (nhds ((a + x) - a)) :=
      ((continuous_id : Continuous fun z : Tiling.Plane => z).sub
        (continuous_const : Continuous fun _ : Tiling.Plane => a)).continuousAt
    have hax : a + x - a = x := by abel
    simpa only [hax] using hc
  have h₀Shift := hShift.eventually h₀All
  have hOffCross : ∀ᶠ z in nhds (a + x),
      z.re ≠ (a + x).re ∧ z.im ≠ (a + x).im →
        (z ∈ F₁ ↔ z ∈ a +ᵥ F₀) := by
    filter_upwards [h₁All, h₀Shift] with z hz₁ hz₀ hne
    obtain ⟨q, hq₁⟩ := exists_openQuadrant_of_ne_coordinates hne
    have hq₀ : inOpenQuadrant x (z - a) q :=
      (inOpenQuadrant_vsub a x z q).mp hq₁
    rw [mem_vadd_set_iff_vsub_mem]
    calc
      z ∈ F₁ ↔ q ∈ localCone F₁ (a + x) hF₁ hx₁ := hz₁ q hq₁
      _ ↔ q ∈ localCone F₀ x hF₀ hx₀ := by rw [hCone]
      _ ↔ z - a ∈ F₀ := (hz₀ q hq₀).symm
  apply eventually_mem_iff_of_regularOpen_of_off_cross
    hF₁Open (hF₀Open.vadd a) hF₁Regular
  · rw [closure_vadd, interior_vadd, hF₀Regular]
  · exact hOffCross

private def HasLabelledAxisBoundaryGerm
    (axis : Tiling.AxisParallel.Axis) (positive : Bool)
    (F : Set Tiling.Plane) (x : Tiling.Plane) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.ball x r,
    (z ∈ F ↔ if positive then
      axis.transverseCoord x < axis.transverseCoord z
    else
      axis.transverseCoord z < axis.transverseCoord x)

private theorem affineLine_axisVector
    (axis : Tiling.AxisParallel.Axis) (x : Tiling.Plane) :
    Tiling.affineLine x (Tiling.AxisParallel.properVertexAxisVector axis) =
      {z | axis.transverseCoord z = axis.transverseCoord x} := by
  cases axis
  · simpa [Tiling.AxisParallel.properVertexAxisVector,
      Tiling.AxisParallel.Axis.transverseCoord] using
      (affineLine_eq_horizontal (x := x) (v := (1 : Tiling.Plane))
        one_ne_zero (by simp))
  · simpa [Tiling.AxisParallel.properVertexAxisVector,
      Tiling.AxisParallel.Axis.transverseCoord] using
      (affineLine_eq_vertical (x := x) (v := Complex.I)
        Complex.I_ne_zero (by simp))

private theorem exists_labelledAxisBoundaryGerm
    {F : Set Tiling.Plane}
    (hFOpen : IsOpen F) (hFRegular : interior (closure F) = F)
    {axis : Tiling.AxisParallel.Axis} {x : Tiling.Plane}
    (hGerm : HasAxisBoundaryGerm axis F x) :
    ∃ positive : Bool, HasLabelledAxisBoundaryGerm axis positive F x := by
  obtain ⟨r, hr, hfrontier⟩ := hGerm
  have hFrontierClosure : frontier (closure F) = frontier F := by
    rw [frontier, closure_closure, hFRegular]
    symm
    rw [frontier, hFOpen.interior_eq]
  have hfrontier' : ∀ z ∈ Metric.ball x r,
      (z ∈ frontier (closure F) ↔
        z ∈ Tiling.affineLine x (Tiling.AxisParallel.properVertexAxisVector axis)) := by
    intro z hz
    rw [hFrontierClosure, hfrontier z hz, affineLine_axisVector]
    simp only [mem_ofPred_eq]
  have hClosedRegular : closure (interior (closure F)) = closure F := by
    rw [hFRegular]
  have hHalf := Tiling.local_eq_closedHalfPlane
    (Tiling.AxisParallel.properVertexAxisVector_ne_zero axis) hr hClosedRegular hfrontier'
  have positiveFormula
      (hpos : closure F ∩ Metric.ball x r =
        Tiling.positiveHalfPlane x (Tiling.AxisParallel.properVertexAxisVector axis) ∩
          Metric.ball x r) :
      ∀ z ∈ Metric.ball x r,
        (z ∈ F ↔
          z ∈ Tiling.positiveSide x (Tiling.AxisParallel.properVertexAxisVector axis)) := by
    intro z hzBall
    constructor
    · intro hzF
      have hzHalf :
          z ∈ Tiling.positiveHalfPlane x (Tiling.AxisParallel.properVertexAxisVector axis) := by
        have hzClosure : z ∈ closure F := subset_closure hzF
        have :
            z ∈ Tiling.positiveHalfPlane x (Tiling.AxisParallel.properVertexAxisVector axis) ∩
            Metric.ball x r := hpos ▸ ⟨hzClosure, hzBall⟩
        exact this.1
      rw [Tiling.mem_positiveHalfPlane] at hzHalf
      apply Tiling.mem_positiveSide.mpr
      exact lt_of_le_of_ne hzHalf fun hzZero => by
        have hzFrontier : z ∈ frontier F := by
          apply (hfrontier z hzBall).2
          cases axis <;>
            simp only [Tiling.AxisParallel.Axis.transverseCoord] at hzZero ⊢ <;>
            simp only [Tiling.AxisParallel.properVertexAxisVector, Tiling.signedSide,
              Tiling.planarCross, Complex.one_re, Complex.one_im, Complex.I_re,
              Complex.I_im] at hzZero <;>
            linarith
        exact Set.disjoint_left.1 disjoint_interior_frontier
          (by rw [hFOpen.interior_eq]; exact hzF) hzFrontier
    · intro hzPositive
      rw [← hFRegular]
      apply interior_maximal (s := closure F)
        (t := Tiling.positiveSide x (Tiling.AxisParallel.properVertexAxisVector axis) ∩
          Metric.ball x r)
      · intro w hw
        have hw' : w ∈ closure F ∩ Metric.ball x r := by
          rw [hpos]
          exact ⟨Tiling.mem_positiveHalfPlane.mpr
            (Tiling.mem_positiveSide.mp hw.1).le, hw.2⟩
        exact hw'.1
      · exact
          (Tiling.isOpen_positiveSide x (Tiling.AxisParallel.properVertexAxisVector axis)).inter
            Metric.isOpen_ball
      · exact ⟨hzPositive, hzBall⟩
  have negativeFormula
      (hneg : closure F ∩ Metric.ball x r =
        Tiling.negativeHalfPlane x (Tiling.AxisParallel.properVertexAxisVector axis) ∩
          Metric.ball x r) :
      ∀ z ∈ Metric.ball x r,
        (z ∈ F ↔
          z ∈ Tiling.negativeSide x (Tiling.AxisParallel.properVertexAxisVector axis)) := by
    intro z hzBall
    constructor
    · intro hzF
      have hzHalf :
          z ∈ Tiling.negativeHalfPlane x (Tiling.AxisParallel.properVertexAxisVector axis) := by
        have hzClosure : z ∈ closure F := subset_closure hzF
        have :
            z ∈ Tiling.negativeHalfPlane x (Tiling.AxisParallel.properVertexAxisVector axis) ∩
            Metric.ball x r := hneg ▸ ⟨hzClosure, hzBall⟩
        exact this.1
      rw [Tiling.mem_negativeHalfPlane] at hzHalf
      apply Tiling.mem_negativeSide.mpr
      exact lt_of_le_of_ne hzHalf fun hzZero => by
        have hzFrontier : z ∈ frontier F := by
          apply (hfrontier z hzBall).2
          cases axis <;>
            simp only [Tiling.AxisParallel.Axis.transverseCoord] at hzZero ⊢ <;>
            simp only [Tiling.AxisParallel.properVertexAxisVector, Tiling.signedSide,
              Tiling.planarCross, Complex.one_re, Complex.one_im, Complex.I_re,
              Complex.I_im] at hzZero <;>
            linarith
        exact Set.disjoint_left.1 disjoint_interior_frontier
          (by rw [hFOpen.interior_eq]; exact hzF) hzFrontier
    · intro hzNegative
      rw [← hFRegular]
      apply interior_maximal (s := closure F)
        (t := Tiling.negativeSide x (Tiling.AxisParallel.properVertexAxisVector axis) ∩
          Metric.ball x r)
      · intro w hw
        have hw' : w ∈ closure F ∩ Metric.ball x r := by
          rw [hneg]
          exact ⟨Tiling.mem_negativeHalfPlane.mpr
            (Tiling.mem_negativeSide.mp hw.1).le, hw.2⟩
        exact hw'.1
      · exact
          (Tiling.isOpen_negativeSide x (Tiling.AxisParallel.properVertexAxisVector axis)).inter
            Metric.isOpen_ball
      · exact ⟨hzNegative, hzBall⟩
  rcases hHalf with hpos | hneg
  · have hformula := positiveFormula hpos
    cases axis
    · refine ⟨true, r, hr, fun z hz => ?_⟩
      simpa [HasLabelledAxisBoundaryGerm, Tiling.AxisParallel.properVertexAxisVector,
        Tiling.positiveSide, Tiling.planarCross,
        Tiling.AxisParallel.Axis.transverseCoord] using hformula z hz
    · refine ⟨false, r, hr, fun z hz => ?_⟩
      simpa [HasLabelledAxisBoundaryGerm, Tiling.AxisParallel.properVertexAxisVector,
        Tiling.positiveSide, Tiling.planarCross,
        Tiling.AxisParallel.Axis.transverseCoord] using hformula z hz
  · have hformula := negativeFormula hneg
    cases axis
    · refine ⟨false, r, hr, fun z hz => ?_⟩
      simpa [HasLabelledAxisBoundaryGerm, Tiling.AxisParallel.properVertexAxisVector,
        Tiling.negativeSide, Tiling.planarCross,
        Tiling.AxisParallel.Axis.transverseCoord] using hformula z hz
    · refine ⟨true, r, hr, fun z hz => ?_⟩
      simpa [HasLabelledAxisBoundaryGerm, Tiling.AxisParallel.properVertexAxisVector,
        Tiling.negativeSide, Tiling.planarCross,
        Tiling.AxisParallel.Axis.transverseCoord] using hformula z hz

private theorem mem_frontier_iff_of_eventually_mem_iff
    {S T : Set Tiling.Plane} {x : Tiling.Plane}
    (h : ∀ᶠ z in nhds x, (z ∈ S ↔ z ∈ T)) :
    x ∈ frontier S ↔ x ∈ frontier T := by
  have closureIff (A B : Set Tiling.Plane)
      (hAB : ∀ᶠ z in nhds x, (z ∈ A ↔ z ∈ B)) :
      x ∈ closure A ↔ x ∈ closure B := by
    rw [mem_closure_iff_frequently, mem_closure_iff_frequently]
    constructor
    · intro hA
      exact (hA.and_eventually hAB).mono fun z hz => hz.2.mp hz.1
    · intro hB
      exact (hB.and_eventually hAB).mono fun z hz => hz.2.mpr hz.1
  rw [frontier_eq_closure_inter_closure,
    frontier_eq_closure_inter_closure, mem_inter_iff, mem_inter_iff,
    closureIff S T h, closureIff Sᶜ Tᶜ (h.mono fun _ hz => not_congr hz)]

private theorem eventually_frontier_iff_of_eventually_mem_iff
    {S T : Set Tiling.Plane} {x : Tiling.Plane}
    (h : ∀ᶠ z in nhds x, (z ∈ S ↔ z ∈ T)) :
    ∀ᶠ y in nhds x, (y ∈ frontier S ↔ y ∈ frontier T) := by
  obtain ⟨U, hUsub, hUOpen, hxU⟩ := mem_nhds_iff.mp h
  filter_upwards [hUOpen.mem_nhds hxU] with y hyU
  apply mem_frontier_iff_of_eventually_mem_iff
  exact Filter.mem_of_superset (hUOpen.mem_nhds hyU) hUsub

private theorem HasLabelledAxisBoundaryGerm.axisBoundaryGerm
    {axis : Tiling.AxisParallel.Axis} {positive : Bool}
    {F : Set Tiling.Plane} {x : Tiling.Plane}
    (h : HasLabelledAxisBoundaryGerm axis positive F x) :
    HasAxisBoundaryGerm axis F x := by
  obtain ⟨r, hr, hmem⟩ := h
  let H : Set Tiling.Plane :=
    {z | if positive then
      axis.transverseCoord x < axis.transverseCoord z
    else
      axis.transverseCoord z < axis.transverseCoord x}
  have hEventuallyMem : ∀ᶠ z in nhds x, (z ∈ F ↔ z ∈ H) := by
    filter_upwards [Metric.ball_mem_nhds x hr] with z hz
    exact hmem z hz
  have hEventuallyFrontier :=
    eventually_frontier_iff_of_eventually_mem_iff hEventuallyMem
  obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff.mp hEventuallyFrontier
  refine ⟨s, hs, fun z hz => ?_⟩
  have hzFrontier := hball (by simpa only [Metric.mem_ball] using hz)
  apply hzFrontier.trans
  cases axis <;> cases positive <;>
    simp [H, Tiling.AxisParallel.Axis.transverseCoord,
      Complex.frontier_setOfPred_re_lt, Complex.frontier_setOfPred_lt_re,
      Complex.frontier_setOfPred_im_lt, Complex.frontier_setOfPred_lt_im]

private theorem HasLabelledAxisBoundaryGerm.not_isProperVertex
    {axis : Tiling.AxisParallel.Axis} {positive : Bool}
    {F : Set Tiling.Plane} {x : Tiling.Plane}
    (h : HasLabelledAxisBoundaryGerm axis positive F x) :
    ¬Tiling.AxisParallel.IsProperVertex F x :=
  h.axisBoundaryGerm.not_isProperVertex

private theorem HasLabelledAxisBoundaryGerm.of_mem_ball_of_transverseCoord_eq
    {axis : Tiling.AxisParallel.Axis} {positive : Bool}
    {F : Set Tiling.Plane} {x y : Tiling.Plane} {r : ℝ}
    (h : ∀ z ∈ Metric.ball x r,
      (z ∈ F ↔ if positive then
        axis.transverseCoord x < axis.transverseCoord z
      else
        axis.transverseCoord z < axis.transverseCoord x))
    (hy : y ∈ Metric.ball x r)
    (hyCoord : axis.transverseCoord y = axis.transverseCoord x) :
    HasLabelledAxisBoundaryGerm axis positive F y := by
  let s : ℝ := r - dist y x
  have hs : 0 < s := by
    dsimp only [s]
    apply sub_pos.mpr
    simpa only [Metric.mem_ball] using hy
  refine ⟨s, hs, fun z hz => ?_⟩
  have hzX : z ∈ Metric.ball x r := by
    rw [Metric.mem_ball] at hz ⊢
    calc
      dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ < s + dist y x := by linarith
      _ = r := by simp [s]
  simpa only [hyCoord] using h z hzX

private theorem not_both_labelledAxisBoundaryGerms
    {axis : Tiling.AxisParallel.Axis} {F : Set Tiling.Plane}
    {x : Tiling.Plane} :
    ¬(HasLabelledAxisBoundaryGerm axis false F x ∧
      HasLabelledAxisBoundaryGerm axis true F x) := by
  rintro ⟨hneg, hpos⟩
  obtain ⟨r, hr, hneg⟩ := hneg
  obtain ⟨s, hs, hpos⟩ := hpos
  let d : ℝ := min r s / 2
  have hd : 0 < d := half_pos (lt_min hr hs)
  let z : Tiling.Plane := match axis with
    | .horizontal => x + (d : ℂ) * Complex.I
    | .vertical => x + d
  have hzDist : dist z x = d := by
    rw [dist_eq_norm]
    cases axis
    · simp only [z, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hd, Complex.norm_I, mul_one]
    · simp only [z, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hd]
  have hzBallR : z ∈ Metric.ball x r := by
    rw [Metric.mem_ball, hzDist]
    exact (half_lt_self (lt_min hr hs)).trans_le (min_le_left r s)
  have hzBallS : z ∈ Metric.ball x s := by
    rw [Metric.mem_ball, hzDist]
    exact (half_lt_self (lt_min hr hs)).trans_le (min_le_right r s)
  have hzPositive : axis.transverseCoord x < axis.transverseCoord z := by
    cases axis <;>
      simp only [z, Tiling.AxisParallel.Axis.transverseCoord,
        Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_one, zero_mul, add_zero, Complex.add_re] <;> linarith
  have hzF : z ∈ F := by
    simpa only [Bool.true_eq, ↓reduceIte] using (hpos z hzBallS).mpr hzPositive
  have hzNotF : z ∉ F := by
    intro hz
    have := (hneg z hzBallR).mp hz
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    linarith
  exact hzNotF hzF

private theorem eventually_labelledAxisBoundaryGerm_iff_of_not_proper
    {F : Set Tiling.Plane}
    (hFOpen : IsOpen F) (hFRegular : interior (closure F) = F)
    (hF : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F)
    (axis : Tiling.AxisParallel.Axis) (positive : Bool)
    (level t : ℝ)
    (ht : ¬Tiling.AxisParallel.IsProperVertex F (axisPoint axis level t)) :
    ∀ᶠ s in nhds t,
      (HasLabelledAxisBoundaryGerm axis positive F (axisPoint axis level s) ↔
        HasLabelledAxisBoundaryGerm axis positive F (axisPoint axis level t)) := by
  by_cases hLabel : HasLabelledAxisBoundaryGerm axis positive F
      (axisPoint axis level t)
  · have hLabelAt := hLabel
    obtain ⟨r, hr, hlocal⟩ := hLabel
    filter_upwards [Metric.ball_mem_nhds t hr] with s hs
    constructor
    · intro _
      exact hLabelAt
    · intro _
      apply HasLabelledAxisBoundaryGerm.of_mem_ball_of_transverseCoord_eq hlocal
      · rw [Metric.mem_ball, dist_axisPoint]
        simpa only [Metric.mem_ball] using hs
      · simp
  · have hAxisLocal := eventually_axisBoundaryGerm_iff_of_not_proper
      hF axis level t ht
    by_cases hAxis : HasAxisBoundaryGerm axis F (axisPoint axis level t)
    · obtain ⟨other, hOther⟩ :=
        exists_labelledAxisBoundaryGerm hFOpen hFRegular hAxis
      have hOtherNe : other ≠ positive := by
        intro hEq
        subst other
        exact hLabel hOther
      have hOtherAt := hOther
      obtain ⟨r, hr, hOtherLocal⟩ := hOther
      filter_upwards [Metric.ball_mem_nhds t hr] with s hs
      have hsOther : HasLabelledAxisBoundaryGerm axis other F
          (axisPoint axis level s) := by
        apply HasLabelledAxisBoundaryGerm.of_mem_ball_of_transverseCoord_eq
          hOtherLocal
        · rw [Metric.mem_ball, dist_axisPoint]
          simpa only [Metric.mem_ball] using hs
        · simp
      constructor
      · intro hsLabel
        cases positive <;> cases other
        all_goals simp_all only [Bool.false_eq_true]
        · exact (not_both_labelledAxisBoundaryGerms ⟨hsLabel, hsOther⟩).elim
        · exact (not_both_labelledAxisBoundaryGerms ⟨hsOther, hsLabel⟩).elim
      · intro htLabel
        exact (hLabel htLabel).elim
    · filter_upwards [hAxisLocal] with s hs
      constructor
      · intro hsLabel
        exact (hAxis (hs.mp hsLabel.axisBoundaryGerm)).elim
      · intro htLabel
        exact (hLabel htLabel).elim

private theorem labelledAxisBoundaryGerm_congr_of_eventually_mem_iff
    {axis : Tiling.AxisParallel.Axis} {positive : Bool}
    {S T : Set Tiling.Plane} {x : Tiling.Plane}
    (h : ∀ᶠ z in nhds x, (z ∈ S ↔ z ∈ T)) :
    HasLabelledAxisBoundaryGerm axis positive S x ↔
      HasLabelledAxisBoundaryGerm axis positive T x := by
  obtain ⟨s, hs, hEq⟩ := Metric.eventually_nhds_iff.mp h
  constructor
  · rintro ⟨r, hr, hS⟩
    refine ⟨min r s, lt_min hr hs, fun z hz => ?_⟩
    have hzR := Metric.ball_subset_ball (min_le_left r s) hz
    have hzS := Metric.ball_subset_ball (min_le_right r s) hz
    rw [← hEq (by simpa only [Metric.mem_ball] using hzS)]
    exact hS z hzR
  · rintro ⟨r, hr, hT⟩
    refine ⟨min r s, lt_min hr hs, fun z hz => ?_⟩
    have hzR := Metric.ball_subset_ball (min_le_left r s) hz
    have hzS := Metric.ball_subset_ball (min_le_right r s) hz
    rw [hEq (by simpa only [Metric.mem_ball] using hzS)]
    exact hT z hzR

private theorem labelledAxisBoundaryGerm_vadd_iff
    {axis : Tiling.AxisParallel.Axis} {positive : Bool}
    {F : Set Tiling.Plane} (a x : Tiling.Plane) :
    HasLabelledAxisBoundaryGerm axis positive (a +ᵥ F) (a + x) ↔
      HasLabelledAxisBoundaryGerm axis positive F x := by
  have hTransverseSub (z : Tiling.Plane) :
      axis.transverseCoord (z - a) =
        axis.transverseCoord z - axis.transverseCoord a := by
    cases axis <;> simp [Tiling.AxisParallel.Axis.transverseCoord]
  have hTransverseAdd (z : Tiling.Plane) :
      axis.transverseCoord (a + z) =
        axis.transverseCoord a + axis.transverseCoord z := by
    cases axis <;> simp [Tiling.AxisParallel.Axis.transverseCoord]
  constructor
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, fun z hz => ?_⟩
    have hz' : a + z ∈ Metric.ball (a + x) r := by
      rw [Metric.mem_ball, dist_add_left]
      simpa only [Metric.mem_ball] using hz
    have hm := h (a + z) hz'
    rw [mem_vadd_set_iff_vsub_mem] at hm
    have hsub : a + z - a = z := by abel
    rw [hsub] at hm
    rw [hTransverseAdd, hTransverseAdd] at hm
    cases positive <;>
      simpa only [Bool.false_eq_true, ↓reduceIte,
        add_lt_add_iff_left] using hm
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, fun z hz => ?_⟩
    rw [mem_vadd_set_iff_vsub_mem]
    have hz' : z - a ∈ Metric.ball x r := by
      rw [Metric.mem_ball]
      have hax : a + x - a = x := by abel
      rw [← hax, dist_sub_right]
      simpa only [Metric.mem_ball] using hz
    have hm := h (z - a) hz'
    have hCenter : axis.transverseCoord (a + x) =
        axis.transverseCoord a + axis.transverseCoord x := hTransverseAdd x
    cases positive
    · simp only [Bool.false_eq_true, ↓reduceIte] at hm ⊢
      constructor
      · intro hzF
        have hi := hm.mp hzF
        rw [hTransverseSub] at hi
        rw [hCenter]
        linarith
      · intro hi
        apply hm.mpr
        rw [hTransverseSub]
        rw [hCenter] at hi
        linarith
    · simp only [↓reduceIte] at hm ⊢
      constructor
      · intro hzF
        have hi := hm.mp hzF
        rw [hTransverseSub] at hi
        rw [hCenter]
        linarith
      · intro hi
        apply hm.mpr
        rw [hTransverseSub]
        rw [hCenter] at hi
        linarith

private theorem axisPoint_vadd_vsub_coord
    (axis : Tiling.AxisParallel.Axis) (a : Tiling.Plane)
    (level t : ℝ) :
    axisPoint axis (level + axis.transverseCoord a) t =
      a + axisPoint axis level (t - axis.coord a) := by
  cases axis <;>
    apply Complex.ext <;>
    simp [axisPoint, Tiling.AxisParallel.Axis.coord,
      Tiling.AxisParallel.Axis.transverseCoord] <;> ring

private theorem axisPoint_coord_transverse
    (axis : Tiling.AxisParallel.Axis) (z : Tiling.Plane) :
    axisPoint axis (axis.transverseCoord z) (axis.coord z) = z := by
  cases axis <;>
    apply Complex.ext <;>
    simp [axisPoint, Tiling.AxisParallel.Axis.coord,
      Tiling.AxisParallel.Axis.transverseCoord]

private theorem completeBoundaryLine_mem_iff_forall_labelled
    {F : Set Tiling.Plane}
    (hF : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F)
    (axis : Tiling.AxisParallel.Axis) (level : ℝ) (positive : Bool) :
    ({ axis := axis, level := level,
        insideOnPositiveSide := positive } : CompleteBoundaryLine) ∈
        completeBoundaryLines F hF ↔
      ∀ t : ℝ, HasLabelledAxisBoundaryGerm axis positive F
        (axisPoint axis level t) := by
  constructor
  · intro hLine t
    rcases hLine.2 (axisPoint axis level t) (by
      simp [CompleteBoundaryLine.carrier]) with ⟨r, hr, hlocal⟩
    exact ⟨r, hr, by
      simpa only [axisPoint_transverseCoord] using hlocal⟩
  · intro hAll
    constructor
    · intro z hz
      change axis.transverseCoord z = level at hz
      have hLabel := hAll (axis.coord z)
      have hzPoint : axisPoint axis level (axis.coord z) = z := by
        rw [← hz]
        exact axisPoint_coord_transverse axis z
      rw [hzPoint] at hLabel
      exact hLabel.axisBoundaryGerm.mem_frontier
    · intro z hz
      change axis.transverseCoord z = level at hz
      have hLabel := hAll (axis.coord z)
      have hzPoint : axisPoint axis level (axis.coord z) = z := by
        rw [← hz]
        exact axisPoint_coord_transverse axis z
      rw [hzPoint] at hLabel
      rcases hLabel with ⟨r, hr, hlocal⟩
      exact ⟨r, hr, by simpa only [hz] using hlocal⟩

private theorem eventually_labelled_match_iff_of_boundaryCode_eq
    {F₀ F₁ : Set Tiling.Plane} {a : Tiling.Plane}
    (hF₀Open : IsOpen F₀) (hF₁Open : IsOpen F₁)
    (hF₀Regular : interior (closure F₀) = F₀)
    (hF₁Regular : interior (closure F₁) = F₁)
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hCode : boundaryCode F₁ hF₁ = (boundaryCode F₀ hF₀).vadd a)
    (axis : Tiling.AxisParallel.Axis) (positive : Bool)
    (level t : ℝ) :
    ∀ᶠ s in nhds t,
      ((HasLabelledAxisBoundaryGerm axis positive F₁
          (axisPoint axis (level + axis.transverseCoord a) s) ↔
        HasLabelledAxisBoundaryGerm axis positive F₀
          (axisPoint axis level (s - axis.coord a))) ↔
       (HasLabelledAxisBoundaryGerm axis positive F₁
          (axisPoint axis (level + axis.transverseCoord a) t) ↔
        HasLabelledAxisBoundaryGerm axis positive F₀
          (axisPoint axis level (t - axis.coord a)))) := by
  let x₀ := axisPoint axis level (t - axis.coord a)
  let x₁ := axisPoint axis (level + axis.transverseCoord a) t
  have hx : x₁ = a + x₀ := by
    exact axisPoint_vadd_vsub_coord axis a level t
  by_cases hProper₁ : Tiling.AxisParallel.IsProperVertex F₁ x₁
  · have hProper₀ : Tiling.AxisParallel.IsProperVertex F₀ x₀ := by
      apply (properVertex_vadd_iff_of_boundaryCode_eq hF₀ hF₁ hCode).mp
      simpa only [← hx] using hProper₁
    have hLocal := eventually_mem_iff_vadd_at_proper
      hF₀Open hF₁Open hF₀Regular hF₁Regular hF₀ hF₁
      hProper₀ (hx ▸ hProper₁) hCode
    obtain ⟨U, hUsub, hUOpen, hxU⟩ := mem_nhds_iff.mp hLocal
    have hPathContinuous : Continuous
        (axisPoint axis (level + axis.transverseCoord a)) :=
      continuous_axisPoint axis (level + axis.transverseCoord a)
    have hPathAt : axisPoint axis (level + axis.transverseCoord a) t = x₁ := rfl
    have hEventuallyU : ∀ᶠ s in nhds t,
        axisPoint axis (level + axis.transverseCoord a) s ∈ U := by
      exact hPathContinuous.continuousAt.eventually
        (hUOpen.mem_nhds (by rw [hPathAt, hx]; exact hxU))
    filter_upwards [hEventuallyU] with s hsU
    have hEqAt : ∀ᶠ z in nhds
        (axisPoint axis (level + axis.transverseCoord a) s),
        (z ∈ F₁ ↔ z ∈ a +ᵥ F₀) :=
      Filter.mem_of_superset (hUOpen.mem_nhds hsU) hUsub
    have hCongr := labelledAxisBoundaryGerm_congr_of_eventually_mem_iff
      (axis := axis) (positive := positive) hEqAt
    have hPoint := axisPoint_vadd_vsub_coord axis a level s
    have hTranslated := labelledAxisBoundaryGerm_vadd_iff
      (axis := axis) (positive := positive) (F := F₀) a
      (axisPoint axis level (s - axis.coord a))
    rw [← hPoint] at hTranslated
    have hsMatch := hCongr.trans hTranslated
    have htFalse₁ : ¬HasLabelledAxisBoundaryGerm axis positive F₁ x₁ :=
      fun h => h.not_isProperVertex hProper₁
    have htFalse₀ : ¬HasLabelledAxisBoundaryGerm axis positive F₀ x₀ :=
      fun h => h.not_isProperVertex hProper₀
    tauto
  · have hProper₀ : ¬Tiling.AxisParallel.IsProperVertex F₀ x₀ := by
      intro h
      apply hProper₁
      rw [hx]
      exact (properVertex_vadd_iff_of_boundaryCode_eq hF₀ hF₁ hCode).mpr h
    have h₁Local := eventually_labelledAxisBoundaryGerm_iff_of_not_proper
      hF₁Open hF₁Regular hF₁ axis positive
      (level + axis.transverseCoord a) t hProper₁
    have h₀Local := eventually_labelledAxisBoundaryGerm_iff_of_not_proper
      hF₀Open hF₀Regular hF₀ axis positive level
      (t - axis.coord a) hProper₀
    have hSubContinuous : Continuous (fun s : ℝ => s - axis.coord a) :=
      continuous_id.sub continuous_const
    have h₀Shift := hSubContinuous.continuousAt.eventually h₀Local
    filter_upwards [h₁Local, h₀Shift] with s hs₁ hs₀
    tauto

private theorem all_or_all_not_of_eventually_iff
    (P Q : ℝ → Prop)
    (hLocal : ∀ t : ℝ, ∀ᶠ s in nhds t,
      ((P s ↔ Q s) ↔ (P t ↔ Q t))) :
    (∀ t, P t ↔ Q t) ∨ ∀ t, ¬(P t ↔ Q t) := by
  let E : Set ℝ := {t | P t ↔ Q t}
  have hEOpen : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    filter_upwards [hLocal t] with s hs
    exact hs.mpr ht
  have hEcOpen : IsOpen Eᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    change ¬(P t ↔ Q t) at ht
    filter_upwards [hLocal t] with s hs
    change ¬(P s ↔ Q s)
    exact fun h => ht (hs.mp h)
  have hEClopen : IsClopen E :=
    ⟨by simpa using hEcOpen.isClosed_compl, hEOpen⟩
  by_cases hENonempty : E.Nonempty
  · left
    have hEUniv := IsClopen.eq_univ hEClopen hENonempty
    intro t
    exact (show t ∈ E from hEUniv.symm ▸ Set.mem_univ t)
  · right
    intro t ht
    exact hENonempty ⟨t, ht⟩

private theorem completeBoundaryLine_vadd_iff_of_boundaryCode_eq
    {F₀ F₁ : Set Tiling.Plane} {a : Tiling.Plane}
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hCode : boundaryCode F₁ hF₁ = (boundaryCode F₀ hF₀).vadd a)
    (axis : Tiling.AxisParallel.Axis) (level : ℝ) (positive : Bool) :
    ({ axis := axis
       level := level + axis.transverseCoord a
       insideOnPositiveSide := positive } : CompleteBoundaryLine) ∈
        completeBoundaryLines F₁ hF₁ ↔
      ({ axis := axis
         level := level
         insideOnPositiveSide := positive } : CompleteBoundaryLine) ∈
        completeBoundaryLines F₀ hF₀ := by
  let L₀ : CompleteBoundaryLine :=
    { axis := axis, level := level, insideOnPositiveSide := positive }
  let L₁ : CompleteBoundaryLine :=
    { axis := axis, level := level + axis.transverseCoord a,
      insideOnPositiveSide := positive }
  have hlines := congrArg BoundaryCode.completeLines hCode
  change completeBoundaryLines F₁ hF₁ =
    (fun L => L.vadd a) '' completeBoundaryLines F₀ hF₀ at hlines
  have hvadd : L₀.vadd a = L₁ := by rfl
  change L₁ ∈ completeBoundaryLines F₁ hF₁ ↔
    L₀ ∈ completeBoundaryLines F₀ hF₀
  rw [hlines]
  constructor
  · rintro ⟨L, hL, hLa⟩
    have hAxis := congrArg CompleteBoundaryLine.axis hLa
    have hLevel := congrArg CompleteBoundaryLine.level hLa
    have hPositive := congrArg CompleteBoundaryLine.insideOnPositiveSide hLa
    change L.axis = axis at hAxis
    change L.level + L.axis.transverseCoord a =
      level + axis.transverseCoord a at hLevel
    change L.insideOnPositiveSide = positive at hPositive
    have hLevel' : L.level = level := by
      rw [hAxis] at hLevel
      exact add_right_cancel hLevel
    have hLEq : L = L₀ := by
      rcases L with ⟨Laxis, Llevel, Lpositive⟩
      simp_all only [L₀]
    simpa only [hLEq] using hL
  · intro hL₀
    exact ⟨L₀, hL₀, hvadd⟩

private theorem all_or_all_not_of_eventually_self
    (P : ℝ → Prop)
    (hLocal : ∀ t : ℝ, ∀ᶠ s in nhds t, (P s ↔ P t)) :
    (∀ t, P t) ∨ ∀ t, ¬P t := by
  have hDichotomy := all_or_all_not_of_eventually_iff P (fun _ => True) (by
    intro t
    filter_upwards [hLocal t] with s hs
    simpa only [iff_true] using hs)
  rcases hDichotomy with hAll | hNone
  · left
    intro t
    exact (hAll t).mpr trivial
  · right
    intro t ht
    exact hNone t ⟨fun _ => trivial, fun _ => ht⟩

private theorem all_labelled_match_of_boundaryCode_eq
    {F₀ F₁ : Set Tiling.Plane} {a : Tiling.Plane}
    (hF₀Open : IsOpen F₀) (hF₁Open : IsOpen F₁)
    (hF₀Regular : interior (closure F₀) = F₀)
    (hF₁Regular : interior (closure F₁) = F₁)
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hCode : boundaryCode F₁ hF₁ = (boundaryCode F₀ hF₀).vadd a)
    (axis : Tiling.AxisParallel.Axis) (positive : Bool) (level : ℝ) :
    ∀ t : ℝ,
      HasLabelledAxisBoundaryGerm axis positive F₁
          (axisPoint axis (level + axis.transverseCoord a) t) ↔
        HasLabelledAxisBoundaryGerm axis positive F₀
          (axisPoint axis level (t - axis.coord a)) := by
  let P : ℝ → Prop := fun t =>
    HasLabelledAxisBoundaryGerm axis positive F₁
      (axisPoint axis (level + axis.transverseCoord a) t)
  let Q : ℝ → Prop := fun t =>
    HasLabelledAxisBoundaryGerm axis positive F₀
      (axisPoint axis level (t - axis.coord a))
  have hLocal : ∀ t : ℝ, ∀ᶠ s in nhds t,
      ((P s ↔ Q s) ↔ (P t ↔ Q t)) := by
    intro t
    exact eventually_labelled_match_iff_of_boundaryCode_eq
      hF₀Open hF₁Open hF₀Regular hF₁Regular hF₀ hF₁ hCode
      axis positive level t
  rcases all_or_all_not_of_eventually_iff P Q hLocal with hAll | hNone
  · exact hAll
  · exfalso
    have hNoProper₀ : ∀ t : ℝ,
        ¬Tiling.AxisParallel.IsProperVertex F₀
          (axisPoint axis level (t - axis.coord a)) := by
      intro t ht₀
      have ht₁ : Tiling.AxisParallel.IsProperVertex F₁
          (axisPoint axis (level + axis.transverseCoord a) t) := by
        rw [axisPoint_vadd_vsub_coord axis a level t]
        exact (properVertex_vadd_iff_of_boundaryCode_eq hF₀ hF₁ hCode).mpr ht₀
      apply hNone t
      constructor
      · intro ht
        exact False.elim (ht.not_isProperVertex ht₁)
      · intro ht
        exact False.elim (ht.not_isProperVertex ht₀)
    have hNoProper₁ : ∀ t : ℝ,
        ¬Tiling.AxisParallel.IsProperVertex F₁
          (axisPoint axis (level + axis.transverseCoord a) t) := by
      intro t ht₁
      apply hNoProper₀ t
      apply (properVertex_vadd_iff_of_boundaryCode_eq hF₀ hF₁ hCode).mp
      rw [← axisPoint_vadd_vsub_coord axis a level t]
      exact ht₁
    have hPLocal : ∀ t : ℝ, ∀ᶠ s in nhds t, (P s ↔ P t) := by
      intro t
      exact eventually_labelledAxisBoundaryGerm_iff_of_not_proper
        hF₁Open hF₁Regular hF₁ axis positive
        (level + axis.transverseCoord a) t (hNoProper₁ t)
    have hQLocal : ∀ t : ℝ, ∀ᶠ s in nhds t, (Q s ↔ Q t) := by
      intro t
      have h₀Local := eventually_labelledAxisBoundaryGerm_iff_of_not_proper
        hF₀Open hF₀Regular hF₀ axis positive level
        (t - axis.coord a) (hNoProper₀ t)
      have hSubContinuous : Continuous (fun s : ℝ => s - axis.coord a) :=
        continuous_id.sub continuous_const
      exact hSubContinuous.continuousAt.eventually h₀Local
    rcases all_or_all_not_of_eventually_self P hPLocal with hP | hnP <;>
      rcases all_or_all_not_of_eventually_self Q hQLocal with hQ | hnQ
    · exact hNone 0 ⟨fun _ => hQ 0, fun _ => hP 0⟩
    · have hTargetLine :
          ({ axis := axis
             level := level + axis.transverseCoord a
             insideOnPositiveSide := positive } : CompleteBoundaryLine) ∈
            completeBoundaryLines F₁ hF₁ :=
        (completeBoundaryLine_mem_iff_forall_labelled hF₁ axis
          (level + axis.transverseCoord a) positive).mpr hP
      have hSourceLine :
          ({ axis := axis
             level := level
             insideOnPositiveSide := positive } : CompleteBoundaryLine) ∈
            completeBoundaryLines F₀ hF₀ :=
        (completeBoundaryLine_vadd_iff_of_boundaryCode_eq
          hF₀ hF₁ hCode axis level positive).mp hTargetLine
      have hSourceAll :=
        (completeBoundaryLine_mem_iff_forall_labelled
          hF₀ axis level positive).mp hSourceLine
      exact hnQ 0 (hSourceAll (0 - axis.coord a))
    · have hSourceAll : ∀ u : ℝ,
          HasLabelledAxisBoundaryGerm axis positive F₀
            (axisPoint axis level u) := by
        intro u
        have hu := hQ (u + axis.coord a)
        change HasLabelledAxisBoundaryGerm axis positive F₀
          (axisPoint axis level
            ((u + axis.coord a) - axis.coord a)) at hu
        simpa only [add_sub_cancel_right] using hu
      have hSourceLine :
          ({ axis := axis
             level := level
             insideOnPositiveSide := positive } : CompleteBoundaryLine) ∈
            completeBoundaryLines F₀ hF₀ :=
        (completeBoundaryLine_mem_iff_forall_labelled
          hF₀ axis level positive).mpr hSourceAll
      have hTargetLine :
          ({ axis := axis
             level := level + axis.transverseCoord a
             insideOnPositiveSide := positive } : CompleteBoundaryLine) ∈
            completeBoundaryLines F₁ hF₁ :=
        (completeBoundaryLine_vadd_iff_of_boundaryCode_eq
          hF₀ hF₁ hCode axis level positive).mpr hSourceLine
      have hTargetAll :=
        (completeBoundaryLine_mem_iff_forall_labelled
          hF₁ axis (level + axis.transverseCoord a) positive).mp hTargetLine
      exact hnP 0 (hTargetAll 0)
    · exact hNone 0 ⟨fun h => False.elim (hnP 0 h),
        fun h => False.elim (hnQ 0 h)⟩

private theorem labelledAxisBoundaryGerm_vadd_iff_of_boundaryCode_eq
    {F₀ F₁ : Set Tiling.Plane} {a x : Tiling.Plane}
    (hF₀Open : IsOpen F₀) (hF₁Open : IsOpen F₁)
    (hF₀Regular : interior (closure F₀) = F₀)
    (hF₁Regular : interior (closure F₁) = F₁)
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hCode : boundaryCode F₁ hF₁ = (boundaryCode F₀ hF₀).vadd a)
    (axis : Tiling.AxisParallel.Axis) (positive : Bool) :
    HasLabelledAxisBoundaryGerm axis positive F₁ (a + x) ↔
      HasLabelledAxisBoundaryGerm axis positive F₀ x := by
  have hCoord : axis.coord (a + x) = axis.coord a + axis.coord x := by
    cases axis <;> rfl
  have hTransverse : axis.transverseCoord (a + x) =
      axis.transverseCoord a + axis.transverseCoord x := by
    cases axis <;> rfl
  have hTarget : axisPoint axis
      (axis.transverseCoord x + axis.transverseCoord a)
      (axis.coord (a + x)) = a + x := by
    calc
      axisPoint axis (axis.transverseCoord x + axis.transverseCoord a)
          (axis.coord (a + x)) =
        axisPoint axis (axis.transverseCoord (a + x))
          (axis.coord (a + x)) := by rw [hTransverse, add_comm]
      _ = a + x := axisPoint_coord_transverse axis (a + x)
  have hSource : axisPoint axis (axis.transverseCoord x)
      (axis.coord (a + x) - axis.coord a) = x := by
    rw [hCoord, add_sub_cancel_left]
    exact axisPoint_coord_transverse axis x
  have hMatch := all_labelled_match_of_boundaryCode_eq
    hF₀Open hF₁Open hF₀Regular hF₁Regular hF₀ hF₁ hCode
    axis positive (axis.transverseCoord x) (axis.coord (a + x))
  simpa only [hTarget, hSource] using hMatch

private theorem eventually_mem_iff_of_same_labelledAxisBoundaryGerm
    {axis : Tiling.AxisParallel.Axis} {positive : Bool}
    {S T : Set Tiling.Plane} {x : Tiling.Plane}
    (hS : HasLabelledAxisBoundaryGerm axis positive S x)
    (hT : HasLabelledAxisBoundaryGerm axis positive T x) :
    ∀ᶠ z in nhds x, (z ∈ S ↔ z ∈ T) := by
  rcases hS with ⟨r, hr, hS⟩
  rcases hT with ⟨s, hs, hT⟩
  filter_upwards [Metric.ball_mem_nhds x hr,
    Metric.ball_mem_nhds x hs] with z hzR hzS
  rw [hS z hzR, hT z hzS]

private theorem mem_frontier_vadd_iff_of_boundaryCode_eq
    {F₀ F₁ : Set Tiling.Plane} {a x : Tiling.Plane}
    (hF₀Open : IsOpen F₀) (hF₁Open : IsOpen F₁)
    (hF₀Regular : interior (closure F₀) = F₀)
    (hF₁Regular : interior (closure F₁) = F₁)
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hCode : boundaryCode F₁ hF₁ = (boundaryCode F₀ hF₀).vadd a) :
    a + x ∈ frontier F₁ ↔ x ∈ frontier F₀ := by
  constructor
  · intro hx₁
    by_cases hProper₁ : Tiling.AxisParallel.IsProperVertex F₁ (a + x)
    · exact ((properVertex_vadd_iff_of_boundaryCode_eq
        hF₀ hF₁ hCode).mp hProper₁).1
    · rcases exists_axisBoundaryGerm_of_not_proper hF₁ hx₁ hProper₁ with
        hGerm | hGerm
      · obtain ⟨positive, hLabel₁⟩ :=
          exists_labelledAxisBoundaryGerm hF₁Open hF₁Regular hGerm
        exact ((labelledAxisBoundaryGerm_vadd_iff_of_boundaryCode_eq
          hF₀Open hF₁Open hF₀Regular hF₁Regular hF₀ hF₁ hCode
          .horizontal positive).mp hLabel₁).axisBoundaryGerm.mem_frontier
      · obtain ⟨positive, hLabel₁⟩ :=
          exists_labelledAxisBoundaryGerm hF₁Open hF₁Regular hGerm
        exact ((labelledAxisBoundaryGerm_vadd_iff_of_boundaryCode_eq
          hF₀Open hF₁Open hF₀Regular hF₁Regular hF₀ hF₁ hCode
          .vertical positive).mp hLabel₁).axisBoundaryGerm.mem_frontier
  · intro hx₀
    by_cases hProper₀ : Tiling.AxisParallel.IsProperVertex F₀ x
    · exact ((properVertex_vadd_iff_of_boundaryCode_eq
        hF₀ hF₁ hCode).mpr hProper₀).1
    · rcases exists_axisBoundaryGerm_of_not_proper hF₀ hx₀ hProper₀ with
        hGerm | hGerm
      · obtain ⟨positive, hLabel₀⟩ :=
          exists_labelledAxisBoundaryGerm hF₀Open hF₀Regular hGerm
        exact ((labelledAxisBoundaryGerm_vadd_iff_of_boundaryCode_eq
          hF₀Open hF₁Open hF₀Regular hF₁Regular hF₀ hF₁ hCode
          .horizontal positive).mpr hLabel₀).axisBoundaryGerm.mem_frontier
      · obtain ⟨positive, hLabel₀⟩ :=
          exists_labelledAxisBoundaryGerm hF₀Open hF₀Regular hGerm
        exact ((labelledAxisBoundaryGerm_vadd_iff_of_boundaryCode_eq
          hF₀Open hF₁Open hF₀Regular hF₁Regular hF₀ hF₁ hCode
          .vertical positive).mpr hLabel₀).axisBoundaryGerm.mem_frontier

private theorem frontier_eq_vadd_of_boundaryCode_eq
    {F₀ F₁ : Set Tiling.Plane} {a : Tiling.Plane}
    (hF₀Open : IsOpen F₀) (hF₁Open : IsOpen F₁)
    (hF₀Regular : interior (closure F₀) = F₀)
    (hF₁Regular : interior (closure F₁) = F₁)
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hCode : boundaryCode F₁ hF₁ = (boundaryCode F₀ hF₀).vadd a) :
    frontier F₁ = a +ᵥ frontier F₀ := by
  ext z
  constructor
  · intro hz
    let x := z - a
    have hzx : z = a + x := by dsimp only [x]; abel
    refine ⟨x, ?_, hzx.symm⟩
    apply (mem_frontier_vadd_iff_of_boundaryCode_eq
      hF₀Open hF₁Open hF₀Regular hF₁Regular hF₀ hF₁ hCode).mp
    simpa only [← hzx] using hz
  · rintro ⟨x, hx, rfl⟩
    exact (mem_frontier_vadd_iff_of_boundaryCode_eq
      hF₀Open hF₁Open hF₀Regular hF₁Regular hF₀ hF₁ hCode).mpr hx

private theorem eventually_mem_iff_vadd_at_frontier
    {F₀ F₁ : Set Tiling.Plane} {a x : Tiling.Plane}
    (hF₀Open : IsOpen F₀) (hF₁Open : IsOpen F₁)
    (hF₀Regular : interior (closure F₀) = F₀)
    (hF₁Regular : interior (closure F₁) = F₁)
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hCode : boundaryCode F₁ hF₁ = (boundaryCode F₀ hF₀).vadd a)
    (hx : x ∈ frontier F₀) :
    ∀ᶠ z in nhds (a + x), (z ∈ F₁ ↔ z ∈ a +ᵥ F₀) := by
  by_cases hProper₀ : Tiling.AxisParallel.IsProperVertex F₀ x
  · exact eventually_mem_iff_vadd_at_proper
      hF₀Open hF₁Open hF₀Regular hF₁Regular hF₀ hF₁ hProper₀
      ((properVertex_vadd_iff_of_boundaryCode_eq
        hF₀ hF₁ hCode).mpr hProper₀) hCode
  · rcases exists_axisBoundaryGerm_of_not_proper hF₀ hx hProper₀ with
      hGerm | hGerm
    · obtain ⟨positive, hLabel₀⟩ :=
        exists_labelledAxisBoundaryGerm hF₀Open hF₀Regular hGerm
      have hLabel₁ := (labelledAxisBoundaryGerm_vadd_iff_of_boundaryCode_eq
        hF₀Open hF₁Open hF₀Regular hF₁Regular hF₀ hF₁ hCode
        .horizontal positive).mpr hLabel₀
      have hLabelVadd := (labelledAxisBoundaryGerm_vadd_iff
        (axis := Tiling.AxisParallel.Axis.horizontal) (positive := positive)
        a x).mpr hLabel₀
      exact eventually_mem_iff_of_same_labelledAxisBoundaryGerm
        hLabel₁ hLabelVadd
    · obtain ⟨positive, hLabel₀⟩ :=
        exists_labelledAxisBoundaryGerm hF₀Open hF₀Regular hGerm
      have hLabel₁ := (labelledAxisBoundaryGerm_vadd_iff_of_boundaryCode_eq
        hF₀Open hF₁Open hF₀Regular hF₁Regular hF₀ hF₁ hCode
        .vertical positive).mpr hLabel₀
      have hLabelVadd := (labelledAxisBoundaryGerm_vadd_iff
        (axis := Tiling.AxisParallel.Axis.vertical) (positive := positive)
        a x).mpr hLabel₀
      exact eventually_mem_iff_of_same_labelledAxisBoundaryGerm
        hLabel₁ hLabelVadd

theorem eq_vadd_of_boundaryCode
    {F₀ F₁ : Set Tiling.Plane} {a : Tiling.Plane}
    (hF₀Open : IsOpen F₀) (hF₁Open : IsOpen F₁)
    (hF₀Regular : interior (closure F₀) = F₀)
    (hF₁Regular : interior (closure F₁) = F₁)
    (hF₀Nonempty : F₀.Nonempty) (hF₁Nonempty : F₁.Nonempty)
    (hF₀Proper : F₀ ≠ Set.univ) (hF₁Proper : F₁ ≠ Set.univ)
    (hF₀Polygonal : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁Polygonal : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hCode : boundaryCode F₁ hF₁Polygonal =
      (boundaryCode F₀ hF₀Polygonal).vadd a) :
    F₁ = a +ᵥ F₀ := by
  have hFrontier := frontier_eq_vadd_of_boundaryCode_eq
    hF₀Open hF₁Open hF₀Regular hF₁Regular
    hF₀Polygonal hF₁Polygonal hCode
  have hFrontierVadd : frontier (a +ᵥ F₀) = a +ᵥ frontier F₀ := by
    rw [frontier, closure_vadd, interior_vadd]
    ext z
    simp only [frontier, Set.mem_sdiff, mem_vadd_set_iff_vsub_mem]
  apply eq_of_frontier_eq_of_eventually_mem_iff
    hF₁Open (hF₀Open.vadd a) (hFrontier.trans hFrontierVadd.symm)
  · intro y hy
    let x := y - a
    have hyx : y = a + x := by dsimp only [x]; abel
    have hx : x ∈ frontier F₀ := by
      apply (mem_frontier_vadd_iff_of_boundaryCode_eq
        hF₀Open hF₁Open hF₀Regular hF₁Regular
        hF₀Polygonal hF₁Polygonal hCode).mp
      simpa only [← hyx] using hy
    simpa only [← hyx] using eventually_mem_iff_vadd_at_frontier
      hF₀Open hF₁Open hF₀Regular hF₁Regular
      hF₀Polygonal hF₁Polygonal hCode hx
  · have _hSourceFrontier : (frontier F₀).Nonempty :=
      nonempty_frontier_iff.mpr ⟨hF₀Nonempty, hF₀Proper⟩
    exact nonempty_frontier_iff.mpr ⟨hF₁Nonempty, hF₁Proper⟩

theorem boundaryCode_eq_vadd_iff
    {F₀ F₁ : Set Tiling.Plane}
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (a : Tiling.Plane) :
    boundaryCode F₁ hF₁ = (boundaryCode F₀ hF₀).vadd a ↔
      (boundaryCode F₁ hF₁).properVertexSet =
          ((boundaryCode F₀ hF₀).vadd a).properVertexSet ∧
      (boundaryCode F₁ hF₁).coneGraph =
          ((boundaryCode F₀ hF₀).vadd a).coneGraph ∧
      (boundaryCode F₁ hF₁).completeLines =
          ((boundaryCode F₀ hF₀).vadd a).completeLines := by
  constructor
  · intro h
    exact ⟨congrArg BoundaryCode.properVertexSet h,
      congrArg BoundaryCode.coneGraph h,
      congrArg BoundaryCode.completeLines h⟩
  · rintro ⟨hvertices, hcones, hlines⟩
    exact BoundaryCode.eq_of_components hvertices hcones hlines

end Tiling.AxisParallel.Terminal

open Bornology Set
namespace Tiling.AxisParallel

private def axisPoint (axis : Axis) (level coord : ℝ) : Tiling.Plane :=
  match axis with
  | .horizontal => ⟨coord, level⟩
  | .vertical => ⟨level, coord⟩

private theorem axisPoint_transverse (axis : Axis) (level coord : ℝ) :
    axis.transverseCoord (axisPoint axis level coord) = level := by
  cases axis <;> rfl

private theorem axisPoint_coord (axis : Axis) (level coord : ℝ) :
    axis.coord (axisPoint axis level coord) = coord := by
  cases axis <;> rfl

private theorem axis_transverse_smul_add (axis : Axis) (a b : ℝ)
    (v w : Tiling.Plane) :
    axis.transverseCoord (a • v + b • w) =
      a * axis.transverseCoord v + b * axis.transverseCoord w := by
  cases axis <;>
    simp only [Axis.transverseCoord, Complex.add_im, Complex.add_re,
      Complex.smul_im, Complex.smul_re, smul_eq_mul]

private theorem axisPoint_injective (axis : Axis) (level : ℝ) :
    Function.Injective (axisPoint axis level) := by
  intro x y h
  exact (axisPoint_coord axis level x).symm.trans
    ((congrArg axis.coord h).trans (axisPoint_coord axis level y))

private theorem axisPoint_not_mem_nonaxis_segment
    (axis : Axis) (level : ℝ) (v w : Tiling.Plane)
    (hnot : ¬ segment ℝ v w ⊆ {z | axis.transverseCoord z = level}) :
    {r : ℝ | axisPoint axis level r ∈ segment ℝ v w}.Subsingleton := by
  intro r hr t ht
  obtain ⟨a, b, _, _, hab, hrepr⟩ := hr
  obtain ⟨c, d, _, _, hcd, hrepr'⟩ := ht
  have hcoord : level = a * axis.transverseCoord v +
      b * axis.transverseCoord w := by
    have := congrArg axis.transverseCoord hrepr.symm
    simpa only [axisPoint_transverse, axis_transverse_smul_add] using this
  have hcoord' : level = c * axis.transverseCoord v +
      d * axis.transverseCoord w := by
    have := congrArg axis.transverseCoord hrepr'.symm
    simpa only [axisPoint_transverse, axis_transverse_smul_add] using this
  have htrans : axis.transverseCoord v ≠ axis.transverseCoord w := by
    intro heq
    have hl : axis.transverseCoord v = level := by
      calc
        axis.transverseCoord v =
            (a + b) * axis.transverseCoord v := by rw [hab]; ring
        _ = a * axis.transverseCoord v + b * axis.transverseCoord w := by
          rw [← heq]; ring
        _ = level := hcoord.symm
    apply hnot
    intro z hz
    obtain ⟨p, q, _, _, hpq, rfl⟩ := hz
    calc
      axis.transverseCoord (p • v + q • w) =
          p * axis.transverseCoord v + q * axis.transverseCoord w :=
            axis_transverse_smul_add axis p q v w
      _ = (p + q) * axis.transverseCoord v := by rw [← heq]; ring
      _ = level := by simp [hpq, hl]
  have hb : b = 1 - a := by linarith
  have hd : d = 1 - c := by linarith
  rw [hb] at hcoord
  rw [hd] at hcoord'
  have hfactor : (a - c) *
      (axis.transverseCoord v - axis.transverseCoord w) = 0 := by
    nlinarith [hcoord, hcoord']
  have hac : a = c := sub_eq_zero.mp
    ((mul_eq_zero.mp hfactor).resolve_right (sub_ne_zero.mpr htrans))
  have hbd : b = d := by linarith
  apply axisPoint_injective axis level
  calc
    axisPoint axis level r = a • v + b • w := hrepr.symm
    _ = c • v + d • w := by rw [hac, hbd]
    _ = axisPoint axis level t := hrepr'

private theorem axisPoint_norm_ge_coord (axis : Axis) (level coord : ℝ) :
    |coord| ≤ ‖axisPoint axis level coord‖ := by
  cases axis with
  | horizontal =>
      simpa [axisPoint] using
        Complex.abs_re_le_norm (axisPoint Axis.horizontal level coord)
  | vertical =>
      simpa [axisPoint] using
        Complex.abs_im_le_norm (axisPoint Axis.vertical level coord)

/-- A countable segment family cannot cover a whole axis line if only finitely
many of its segments are contained in that line. -/
theorem axisLine_not_subset_countableSegments
    {E : Type*} [Countable E] (v w : E → Tiling.Plane)
    (axis : Axis) (level : ℝ)
    (haligned : {e : E | segment ℝ (v e) (w e) ⊆
      {z | axis.transverseCoord z = level}}.Finite) :
    ¬ ({z : Tiling.Plane | axis.transverseCoord z = level} ⊆
      ⋃ e : E, segment ℝ (v e) (w e)) := by
  classical
  let A : Set E := {e | segment ℝ (v e) (w e) ⊆
    {z | axis.transverseCoord z = level}}
  let B : Set Tiling.Plane := ⋃ e ∈ A, segment ℝ (v e) (w e)
  have hB : Bornology.IsBounded B := by
    apply (isBounded_biUnion haligned).2
    intro e he
    have hfin : ({v e, w e} : Set Tiling.Plane).Finite := by simp
    exact ((hfin.isCompact_convexHull ℝ).isBounded).subset
      (segment_subset_convexHull (by simp) (by simp))
  obtain ⟨R, hR⟩ := hB.subset_closedBall (0 : Tiling.Plane)
  let g : ℝ → ℝ := fun t => |R| + |level| + Real.exp t + 1
  have hgInjective : Function.Injective g := by
    intro x y hxy
    apply Real.exp_injective
    dsimp only [g] at hxy
    linarith
  have hgOutside (t : ℝ) : axisPoint axis level (g t) ∉ B := by
    intro ht
    have hnorm : ‖axisPoint axis level (g t)‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR ht
    have hcoord := axisPoint_norm_ge_coord axis level (g t)
    have hgpos : 0 < g t := by dsimp [g]; positivity
    rw [abs_of_pos hgpos] at hcoord
    have hexp := Real.exp_pos t
    dsimp [g] at hcoord
    linarith [abs_nonneg level, le_abs_self R]
  let X : Set ℝ := ⋃ e : E,
    if e ∈ A then ∅ else {t | axisPoint axis level t ∈ segment ℝ (v e) (w e)}
  have hX : X.Countable := by
    apply Set.countable_iUnion
    intro e
    by_cases he : e ∈ A
    · simp [he]
    · simpa [he] using
        (axisPoint_not_mem_nonaxis_segment axis level (v e) (w e) he).countable
  intro hcover
  have hmap : g '' (Set.univ : Set ℝ) ⊆ X := by
    rintro r ⟨t, _, rfl⟩
    have hline : axisPoint axis level (g t) ∈
        {z | axis.transverseCoord z = level} := axisPoint_transverse axis level (g t)
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp (hcover hline)
    have hnotA : e ∉ A := by
      intro hea
      exact hgOutside t (Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨hea, he⟩⟩)
    apply Set.mem_iUnion.mpr
    refine ⟨e, ?_⟩
    simp [hnotA, he]
  have hcount : (Set.univ : Set ℝ).Countable :=
    Set.countable_of_injective_of_countable_image hgInjective.injOn
      (hX.mono hmap)
  exact Set.not_countable_univ hcount

end Tiling.AxisParallel
