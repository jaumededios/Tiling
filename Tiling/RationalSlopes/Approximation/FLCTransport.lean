import Tiling.RationalSlopes.Approximation.RationalLineGeometry
import Tiling.RationalSlopes.Approximation.FLCControl
import Tiling.RationalSlopes.SlicesAndColumns

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology
open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Approximation
open Tiling.RationalSlopes.Approximation
open Tiling.Polygonal (RelativeDense)

noncomputable section

namespace Tiling.RationalSlopes.Approximation

private theorem properVertex_iff_of_sameGerm
    {D E : Set Plane} {x y : Plane} (h : Tiling.Polygonal.SameGermAt D x E y) :
    x ∈ Tiling.Polygonal.properVertices D ↔ y ∈ Tiling.Polygonal.properVertices E := by
  have hlocal := Tiling.Polygonal.isProperVertex_iff_of_eventuallyEq h
  change (x ∈ Tiling.Polygonal.properVertices D ↔
    x ∈ Tiling.Polygonal.properVertices ((x - y) +ᵥ E)) at hlocal
  rw [Tiling.Polygonal.properVertices_vadd] at hlocal
  simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hlocal

private theorem interior_germ_of_support_germ
    {D E : Set Plane} {x : Plane} (h : D =ᶠ[𝓝 x] E) :
    interior D =ᶠ[𝓝 x] interior E := by
  filter_upwards [h.eventuallyEq_nhds] with z hz
  exact propext hz.mem_interior_iff

private theorem halfspace_sign_germ (n : RationalNormal) (w : Plane) (c c' : ℝ)
    (hs : Real.sign c' = Real.sign c) :
    {z : Plane | normalEval n (z - w) + c ≤ 0} =ᶠ[𝓝 w]
      {z : Plane | normalEval n (z - w) + c' ≤ 0} := by
  have hf : Continuous (fun z : Plane => normalEval n (z - w) + c) := by
    unfold normalEval
    fun_prop
  have hg : Continuous (fun z : Plane => normalEval n (z - w) + c') := by
    unfold normalEval
    fun_prop
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hc' : c' < 0 := by
      unfold Real.sign at hs
      split_ifs at hs <;> norm_num at hs
      all_goals linarith
    have hfc : normalEval n (w - w) + c < 0 := by simpa [normalEval] using hc
    have hgc : normalEval n (w - w) + c' < 0 := by simpa [normalEval] using hc'
    filter_upwards [hf.continuousAt.eventually_lt continuousAt_const hfc,
      hg.continuousAt.eventually_lt continuousAt_const hgc] with z hz hz'
    exact propext (iff_of_true hz.le hz'.le)
  · have hc' : c' = 0 := Real.sign_eq_zero_iff.mp (by simpa using hs)
    subst c'
    exact Filter.EventuallyEq.rfl
  · have hc' : 0 < c' := by
      unfold Real.sign at hs
      split_ifs at hs <;> norm_num at hs <;> linarith
    have hfc : 0 < normalEval n (w - w) + c := by simpa [normalEval] using hc
    have hgc : 0 < normalEval n (w - w) + c' := by simpa [normalEval] using hc'
    filter_upwards [continuousAt_const.eventually_lt hf.continuousAt hfc,
      continuousAt_const.eventually_lt hg.continuousAt hgc] with z hz hz'
    exact propext (iff_of_false (not_le.mpr hz) (not_le.mpr hz'))

private theorem deformLine_eval (φ : ℝ →ₗ[ℚ] ℚ) (l : RationalLine) (z : Plane) :
    (deformLine φ l).eval (deformPoint φ z) = (φ (l.eval z) : ℝ) := by
  dsimp only [RationalLine.eval, deformLine]
  rw [rationalNormal_commutes, map_sub, Rat.cast_sub]

private theorem eval_shift (l : RationalLine) (z w : Plane) :
    l.eval z = normalEval l.normal (z - w) + l.eval w := by
  simp only [RationalLine.eval, normalEval, Complex.sub_re, Complex.sub_im]
  ring

private theorem translated_halfspace_germ
    (φ : ℝ →ₗ[ℚ] ℚ) (l : RationalLine) (d w : Plane)
    (hs : Real.sign (φ (l.eval (w - d)) : ℝ) = Real.sign (l.eval (w - d))) :
    {z : Plane | l.eval (z - d) ≤ 0} =ᶠ[𝓝 w]
      {z : Plane | (deformLine φ l).eval
        (z - (w - deformPoint φ w) - deformPoint φ d) ≤ 0} := by
  have ha (z : Plane) : l.eval (z - d) =
      normalEval l.normal (z - w) + l.eval (w - d) := by
    rw [eval_shift l (z - d) (w - d)]
    congr 2
    abel
  have hb (z : Plane) : (deformLine φ l).eval
      (z - (w - deformPoint φ w) - deformPoint φ d) =
      normalEval l.normal (z - w) + (φ (l.eval (w - d)) : ℝ) := by
    rw [eval_shift (deformLine φ l) _ (deformPoint φ (w - d)), deformLine_eval]
    change normalEval l.normal _ + _ = _
    congr 2
    have hsub := (deformPointLinear φ).map_sub w d
    change deformPoint φ (w - d) = deformPoint φ w - deformPoint φ d at hsub
    rw [hsub]
    abel
  have h := halfspace_sign_germ l.normal w
    (l.eval (w - d)) (φ (l.eval (w - d)) : ℝ) hs
  filter_upwards [h] with z hz
  change (l.eval (z - d) ≤ 0) =
    ((deformLine φ l).eval (z - (w - deformPoint φ w) - deformPoint φ d) ≤ 0)
  rw [ha z, hb z]
  exact hz

private theorem mem_deformedSupport (P : PolyhedralCode) (φ : ℝ →ₗ[ℚ] ℚ) (z : Plane) :
    z ∈ deformedPolyhedralSupport P φ ↔
      ∃ cell ∈ P, ∀ l ∈ cell, (deformLine φ l).eval z ≤ 0 := by
  simp [deformedPolyhedralSupport, polyhedralSupport]

private theorem packing_subfamily {K : PolygonalRegion} {S T : Set Plane}
    (hp : Tiling.IsPacking K.prototileFamily (K.placements T)) (hST : S ⊆ T) :
    Tiling.IsPacking K.prototileFamily (K.placements S) := by
  apply (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K S).mpr
  intro s hs t ht hst
  exact (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K T).mp hp
    (hST hs) (hST ht) hst

private theorem cloud_hasFLC {W : Finset Plane} {T : Set Plane}
    (hT : Tiling.Polygonal.HasFLC T) : Tiling.Polygonal.HasFLC (decoratedCloud W T) := by
  simpa only [decoratedCloud, add_comm] using hT.add_finset W

private theorem cloud_relativeDense {W : Finset Plane} {T : Set Plane}
    (hW : W.Nonempty) (hT : RelativeDense T) : RelativeDense (decoratedCloud W T) := by
  obtain ⟨w, hw⟩ := hW
  obtain ⟨ρ, hρ, hT⟩ := hT
  refine ⟨ρ, hρ, ?_⟩
  intro z
  obtain ⟨t, ht, hdist⟩ := hT (z - w)
  refine ⟨w + t, Set.mem_add.mpr ⟨w, hw, t, ht, rfl⟩, ?_⟩
  have heq : dist z (w + t) = dist (z - w) t := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  rwa [heq]

private theorem same_sign_nonpos {x y : ℝ} (h : Real.sign x = Real.sign y) :
    x ≤ 0 ↔ y ≤ 0 := by
  unfold Real.sign at h
  split_ifs at h <;> norm_num at h <;> constructor <;> intro hle <;> linarith

private theorem code_image_of_signs (P : PolyhedralCode)
    (φ : ℝ →ₗ[ℚ] ℚ) (H : Plane ≃ₜ Plane)
    (hs : ∀ l ∈ P.flatten, ∀ z : Plane,
      Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z)) :
    H '' polyhedralSupport P = deformedPolyhedralSupport P φ := by
  ext y
  rw [mem_deformedSupport]
  constructor
  · rintro ⟨x, ⟨cell, hc, hcell⟩, rfl⟩
    refine ⟨cell, hc, ?_⟩
    intro l hl
    exact (same_sign_nonpos (hs l (List.mem_flatten.mpr ⟨cell, hc, hl⟩) x)).mpr
      (hcell l hl)
  · rintro ⟨cell, hc, hcell⟩
    refine ⟨H.symm y, ⟨cell, hc, ?_⟩, H.apply_symm_apply y⟩
    intro l hl
    apply (same_sign_nonpos (hs l (List.mem_flatten.mpr ⟨cell, hc, hl⟩) (H.symm y))).mp
    simpa only [H.apply_symm_apply] using hcell l hl

private theorem approximation_fixes_nat (φ : ℝ →ₗ[ℚ] ℚ) (hφ : φ 1 = 1) (N : ℕ) :
    (φ (N : ℝ) : ℝ) = N := by
  have h := φ.map_smul (N : ℚ) (1 : ℝ)
  simpa [Rat.smul_def, hφ] using congrArg (fun q : ℚ => (q : ℝ)) h

private theorem code_uniformBound (K : PolygonalRegion) (P : PolyhedralCode)
    (hP : polyhedralSupport P = K.support) :
    ∃ B : ℝ, 0 < B ∧ K.support ⊆ Metric.closedBall 0 B ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
            Kφ.support ⊆ Metric.closedBall 0 B := by
  classical
  obtain ⟨b, hb, hbound⟩ := K.isPolygonal.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt b
  let l₁ : RationalLine := ⟨⟨1, 0, Or.inl one_ne_zero⟩, N⟩
  let l₂ : RationalLine := ⟨⟨-1, 0, Or.inl (by norm_num)⟩, N⟩
  let l₃ : RationalLine := ⟨⟨0, 1, Or.inr one_ne_zero⟩, N⟩
  let l₄ : RationalLine := ⟨⟨0, -1, Or.inr (by norm_num)⟩, N⟩
  let L := P.flatten.toFinset ∪ {l₁, l₂, l₃, l₄}
  obtain ⟨F, ε, hε, htransport⟩ := finiteRationalArrangement_transport L ∅
  have hB : 0 < 2 * (N : ℝ) + 1 := by linarith
  refine ⟨2 * (N : ℝ) + 1, hB, ?_, F, ε, hε, ?_⟩
  · intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [hbound z hz]
  · intro φ hφ Kφ hKφ y hy
    obtain ⟨H, _, hs⟩ := htransport φ hφ
    have hbase : H '' K.support = Kφ.support := by
      rw [← hP, hKφ]
      apply code_image_of_signs P φ H
      intro l hl z
      exact hs l (Finset.mem_union_left _ (List.mem_toFinset.mpr hl)) z
    obtain ⟨x, hx, rfl⟩ := hbase.symm ▸ hy
    have hxnorm := hbound x hx
    have hfix := approximation_fixes_nat φ hφ.1 N
    have hineq (l : RationalLine) (hl : l ∈ ({l₁, l₂, l₃, l₄} : Finset RationalLine))
        (heval : l.eval x ≤ 0) : (deformLine φ l).eval (H x) ≤ 0 :=
      (same_sign_nonpos (hs l (Finset.mem_union_right _ hl) x)).mpr heval
    have h₁ : (H x).re ≤ N := by
      have hx₁ : l₁.eval x ≤ 0 := by
        simp [l₁, RationalLine.eval, normalEval]
        linarith [Complex.re_le_norm x]
      have h := hineq l₁ (by simp) hx₁
      simpa [l₁, deformLine, RationalLine.eval, normalEval, hfix] using h
    have h₂ : -(N : ℝ) ≤ (H x).re := by
      have hx₂ : l₂.eval x ≤ 0 := by
        simp [l₂, RationalLine.eval, normalEval]
        linarith [neg_le_abs x.re, Complex.abs_re_le_norm x]
      have h := hineq l₂ (by simp) hx₂
      have : -(H x).re - (N : ℝ) ≤ 0 := by
        simpa [l₂, deformLine, RationalLine.eval, normalEval, hfix] using h
      linarith
    have h₃ : (H x).im ≤ N := by
      have hx₃ : l₃.eval x ≤ 0 := by
        simp [l₃, RationalLine.eval, normalEval]
        linarith [Complex.im_le_norm x]
      have h := hineq l₃ (by simp) hx₃
      simpa [l₃, deformLine, RationalLine.eval, normalEval, hfix] using h
    have h₄ : -(N : ℝ) ≤ (H x).im := by
      have hx₄ : l₄.eval x ≤ 0 := by
        simp [l₄, RationalLine.eval, normalEval]
        linarith [neg_le_abs x.im, Complex.abs_im_le_norm x]
      have h := hineq l₄ (by simp) hx₄
      have : -(H x).im - (N : ℝ) ≤ 0 := by
        simpa [l₄, deformLine, RationalLine.eval, normalEval, hfix] using h
      linarith
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |(H x).re| ≤ N := abs_le.mpr ⟨h₂, h₁⟩
    have him : |(H x).im| ≤ N := abs_le.mpr ⟨h₄, h₃⟩
    linarith [Complex.norm_le_abs_re_add_abs_im (H x)]

private theorem pair_disjoint_iff (K : PolygonalRegion) (s t : Plane) :
    Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.openCarrier) ↔
      Disjoint K.openCarrier ((t - s) +ᵥ K.openCarrier) := by
  rw [Set.disjoint_vadd_set_left, vadd_vadd]
  have heq : -s + t = t - s := by abel
  rw [heq]

private theorem overlap_distance_bound (K : PolygonalRegion) (B : ℝ)
    (hbound : K.support ⊆ Metric.closedBall 0 B) (s t : Plane)
    (hoverlap : ¬Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.openCarrier)) :
    dist s t ≤ 2 * B := by
  obtain ⟨x, hx, hy⟩ := Set.not_disjoint_iff.mp hoverlap
  have hx' : x - s ∈ K.openCarrier := by
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hx
  have hy' : x - t ∈ K.openCarrier := by
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hy
  have hxB := hbound (interior_subset hx')
  have hyB := hbound (interior_subset hy')
  simp only [Metric.mem_closedBall, dist_zero_right] at hxB hyB
  calc
    dist s t ≤ dist s x + dist x t := dist_triangle s x t
    _ = ‖x - s‖ + ‖x - t‖ := by rw [dist_comm s x, dist_eq_norm, dist_eq_norm]
    _ ≤ 2 * B := by linarith

private theorem points_uniformBound (W : Finset Plane) :
    ∃ B : ℝ, 0 < B ∧ (∀ w ∈ W, ‖w‖ ≤ B) ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ w ∈ W, ‖deformPoint φ w‖ ≤ B := by
  classical
  obtain ⟨b, hb, hbound⟩ := W.finite_toSet.isBounded.exists_pos_norm_le
  let F := W.biUnion fun w => {w.re, w.im}
  refine ⟨2 * b + 2, by linarith, ?_, F, 1, by norm_num, ?_⟩
  · intro w hw
    linarith [hbound w hw]
  · intro φ hφ w hw
    have hre : |(φ w.re : ℝ) - w.re| < 1 := hφ.2 _
      (Finset.mem_biUnion.mpr ⟨w, hw, by simp⟩)
    have him : |(φ w.im : ℝ) - w.im| < 1 := hφ.2 _
      (Finset.mem_biUnion.mpr ⟨w, hw, by simp⟩)
    have hre' : |(φ w.re : ℝ)| ≤ |(φ w.re : ℝ) - w.re| + |w.re| := by
      simpa only [sub_add_cancel] using abs_add_le ((φ w.re : ℝ) - w.re) w.re
    have him' : |(φ w.im : ℝ)| ≤ |(φ w.im : ℝ) - w.im| + |w.im| := by
      simpa only [sub_add_cancel] using abs_add_le ((φ w.im : ℝ) - w.im) w.im
    have hnorm := Complex.norm_le_abs_re_add_abs_im (deformPoint φ w)
    change ‖deformPoint φ w‖ ≤ |(φ w.re : ℝ)| + |(φ w.im : ℝ)| at hnorm
    linarith [Complex.abs_re_le_norm w, Complex.abs_im_le_norm w, hbound w hw]

private def supportUnion (K : PolygonalRegion) (S : Set Plane) : Set Plane :=
  {z | ∃ s ∈ S, z - s ∈ K.support}

private theorem regularSupport_eq_interior_supportUnion (K : PolygonalRegion) (S : Set Plane)
    (hp : Tiling.IsPacking K.prototileFamily (K.placements S)) :
    Tiling.Polygonal.regularSupport K S = interior (supportUnion K S) := by
  unfold Tiling.Polygonal.regularSupport
  rw [Tiling.Polygonal.closure_openUnion_eq_iUnion_support hp]
  congr 1
  ext z
  rw [Set.mem_iUnion]
  change (∃ s : S, z ∈ (s : Plane) +ᵥ K.support) ↔ ∃ s ∈ S, z - s ∈ K.support
  constructor
  · rintro ⟨⟨s, hs⟩, hz⟩
    refine ⟨s, hs, ?_⟩
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hz
  · rintro ⟨s, hs, hz⟩
    refine ⟨⟨s, hs⟩, ?_⟩
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hz

private theorem coarse_lower_of_relativeError
    (φ : ℝ →ₗ[ℚ] ℚ) (x : Plane)
    (h : ‖deformPoint φ x - x‖ ≤ (1 / 2 : ℝ) * ‖x‖) :
    ‖x‖ ≤ 2 * ‖deformPoint φ x‖ := by
  have htriangle : ‖x‖ ≤ ‖deformPoint φ x‖ + ‖deformPoint φ x - x‖ := by
    have h := norm_sub_le (deformPoint φ x) (deformPoint φ x - x)
    simpa only [sub_sub_cancel] using h
  linarith

private theorem finiteStar_support_germs :
  ∀ (K : PolygonalRegion) (P : PolyhedralCode), polyhedralSupport P = K.support →
    ∀ D W : Finset Plane, ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ d ∈ D, ∀ w ∈ W,
            Tiling.Polygonal.SameGermAt (d +ᵥ K.support) w
              (deformPoint φ d +ᵥ Kφ.support) (deformPoint φ w) := by
  classical
  intro K P hP D W
  let Z := D.biUnion fun d => W.biUnion fun w =>
    P.flatten.toFinset.image fun l => l.eval (w - d)
  obtain ⟨F, ε, hε, hF⟩ := finiteApproximation_signAndEquality Z
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ d hd w hw
  have hl : ∀ l ∈ P.flatten.toFinset,
      {z : Plane | l.eval (z - d) ≤ 0} =ᶠ[𝓝 w]
        {z : Plane | (deformLine φ l).eval
          (z - (w - deformPoint φ w) - deformPoint φ d) ≤ 0} := by
    intro l hl
    apply translated_halfspace_germ φ l d w
    apply (hF φ hφ).1
    exact Finset.mem_biUnion.mpr ⟨d, hd,
      Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩⟩
  have hall := (P.flatten.toFinset.eventually_all).mpr hl
  change (d +ᵥ K.support) =ᶠ[𝓝 w]
    ((w - deformPoint φ w) +ᵥ (deformPoint φ d +ᵥ Kφ.support))
  filter_upwards [hall] with z hz
  apply propext
  change z ∈ (d +ᵥ K.support) ↔
    z ∈ ((w - deformPoint φ w) +ᵥ (deformPoint φ d +ᵥ Kφ.support))
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  rw [← hP, hKφ, mem_deformedSupport]
  have hza : -d + z = z - d := by abel
  have hzb : -deformPoint φ d + (-(w - deformPoint φ w) + z) =
      z - (w - deformPoint φ w) - deformPoint φ d := by abel
  rw [hza, hzb]
  change (∃ cell ∈ P, ∀ l ∈ cell, l.eval (z - d) ≤ 0) ↔ _
  constructor
  · rintro ⟨cell, hc, hcell⟩
    refine ⟨cell, hc, ?_⟩
    intro l hl
    have hflat : l ∈ P.flatten.toFinset := List.mem_toFinset.mpr
      (List.mem_flatten.mpr ⟨cell, hc, hl⟩)
    exact (eq_iff_iff.mp (hz l hflat)).mp (hcell l hl)
  · rintro ⟨cell, hc, hcell⟩
    refine ⟨cell, hc, ?_⟩
    intro l hl
    have hflat : l ∈ P.flatten.toFinset := List.mem_toFinset.mpr
      (List.mem_flatten.mpr ⟨cell, hc, hl⟩)
    exact (eq_iff_iff.mp (hz l hflat)).mpr (hcell l hl)

theorem finiteStar_germs :
  ∀ (K : PolygonalRegion) (P : PolyhedralCode), polyhedralSupport P = K.support →
    ∀ D W : Finset Plane, ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ d ∈ D, ∀ w ∈ W,
            Tiling.Polygonal.SameGermAt (d +ᵥ K.openCarrier) w
              (deformPoint φ d +ᵥ Kφ.openCarrier) (deformPoint φ w) := by
  intro K P hP D W
  obtain ⟨F, ε, hε, hsupport⟩ := finiteStar_support_germs K P hP D W
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ d hd w hw
  have h := interior_germ_of_support_germ (hsupport φ hφ Kφ hKφ d hd w hw)
  simpa only [Tiling.Polygonal.SameGermAt, interior_vadd,
    Tiling.RationalPolygonal.PolygonalRegion.openCarrier] using h

/-- Pairwise interior disjointness is preserved for each finite candidate displacement.
This is labelled packing, so equal image centres cannot be silently quotiented out. -/
private def translatedLine (d : Plane) (l : RationalLine) : RationalLine :=
  ⟨l.normal, l.offset + normalEval l.normal d⟩

private def translatedCode (d : Plane) (P : PolyhedralCode) : PolyhedralCode :=
  P.map (fun cell => cell.map (translatedLine d))

private theorem eval_sub (n : RationalNormal) (z d : Plane) :
    normalEval n (z - d) = normalEval n z - normalEval n d := by
  simp [normalEval, Complex.sub_re, Complex.sub_im]
  ring

private theorem translatedLine_eval (d z : Plane) (l : RationalLine) :
    (translatedLine d l).eval z = l.eval (z - d) := by
  simp [translatedLine, RationalLine.eval, eval_sub]
  ring

private theorem translatedCode_support (d : Plane) (P : PolyhedralCode) :
    polyhedralSupport (translatedCode d P) = d +ᵥ polyhedralSupport P := by
  ext z
  change (∃ cell ∈ translatedCode d P, ∀ l ∈ cell, l.eval z ≤ 0) ↔
    z ∈ d +ᵥ polyhedralSupport P
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
  simp only [translatedCode, List.mem_map]
  constructor
  · rintro ⟨cell', ⟨cell, hcell, rfl⟩, hineq⟩
    refine ⟨cell, hcell, ?_⟩
    intro l hl
    have := hineq (translatedLine d l) (List.mem_map.mpr ⟨l, hl, rfl⟩)
    simpa [translatedLine_eval] using this
  · rintro ⟨cell, hcell, hineq⟩
    refine ⟨cell.map (translatedLine d), ⟨cell, hcell, rfl⟩, ?_⟩
    intro l hl
    rcases List.mem_map.mp hl with ⟨l₀, hl₀, rfl⟩
    rw [translatedLine_eval]
    simpa using hineq l₀ hl₀

private theorem deform_translatedLine (φ : ℝ →ₗ[ℚ] ℚ) (d : Plane)
    (l : RationalLine) :
    deformLine φ (translatedLine d l) = translatedLine (deformPoint φ d) (deformLine φ l) := by
  cases l with
  | mk n offset =>
    simp only [translatedLine, deformLine]
    apply congrArg (fun r : ℝ => ({ normal := n, offset := r } : RationalLine))
    simp [map_add, rationalNormal_commutes]

private theorem deform_translatedCode (φ : ℝ →ₗ[ℚ] ℚ) (d : Plane)
    (P : PolyhedralCode) :
    (translatedCode d P).map (fun cell => cell.map (deformLine φ)) =
      translatedCode (deformPoint φ d) (P.map (fun cell => cell.map (deformLine φ))) := by
  simp [translatedCode, List.map_map, deform_translatedLine]

private theorem sign_le_zero_iff {x y : ℝ} (h : Real.sign x = Real.sign y) :
    (x ≤ 0 ↔ y ≤ 0) := by
  constructor
  · intro hx
    by_contra hy
    have hy' : 0 < y := lt_of_not_ge hy
    have hs : Real.sign y = 1 := Real.sign_of_pos hy'
    have hx' : x < 0 ∨ x = 0 := le_iff_lt_or_eq.mp hx
    rcases hx' with hx' | rfl
    · have : Real.sign x = -1 := Real.sign_of_neg hx'
      rw [this, hs] at h
      norm_num at h
    · rw [Real.sign_zero, hs] at h
      norm_num at h
  · intro hy
    by_contra hx
    have hx' : 0 < x := lt_of_not_ge hx
    have hs : Real.sign x = 1 := Real.sign_of_pos hx'
    have hy' : y < 0 ∨ y = 0 := le_iff_lt_or_eq.mp hy
    rcases hy' with hy' | rfl
    · have : Real.sign y = -1 := Real.sign_of_neg hy'
      rw [hs, this] at h
      norm_num at h
    · rw [hs, Real.sign_zero] at h
      norm_num at h

private theorem support_image_of_signs (P : PolyhedralCode)
    (φ : ℝ →ₗ[ℚ] ℚ) (H : Plane ≃ₜ Plane)
    (hsign : ∀ l ∈ P.flatten, ∀ z : Plane,
      Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z)) :
    H '' polyhedralSupport P =
      polyhedralSupport (P.map (fun cell => cell.map (deformLine φ))) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨cell, hcell, hineq⟩
    refine ⟨cell.map (deformLine φ), List.mem_map.mpr ⟨cell, hcell, rfl⟩, ?_⟩
    intro l hl
    rcases List.mem_map.mp hl with ⟨l₀, hl₀, rfl⟩
    apply (sign_le_zero_iff (hsign l₀ (List.mem_flatten.mpr ⟨cell, hcell, hl₀⟩) x)).2
    exact hineq l₀ hl₀
  · intro hy
    rcases hy with ⟨cell', hcell', hineq⟩
    rcases List.mem_map.mp hcell' with ⟨cell, hcell, rfl⟩
    refine ⟨H.symm y, ?_, ?_⟩
    · refine ⟨cell, hcell, ?_⟩
      · intro l hl
        apply (sign_le_zero_iff (hsign l (List.mem_flatten.mpr ⟨cell, hcell, hl⟩) (H.symm y))).1
        simpa using hineq (deformLine φ l) (List.mem_map.mpr ⟨l, hl, rfl⟩)
    · simp

private theorem image_disjoint_of_injective {α β : Type*} {A B : Set α}
    (f : α → β) (hf : Function.Injective f) (hAB : Disjoint A B) :
    Disjoint (f '' A) (f '' B) := by
  rw [Set.disjoint_left]
  rintro y ⟨a, ha, rfl⟩ ⟨b, hb, hy⟩
  exact (Set.disjoint_left.mp hAB) ha (hf hy ▸ hb)

theorem finitePair_packing :
  ∀ (K : PolygonalRegion) (P : PolyhedralCode), polyhedralSupport P = K.support →
    ∀ D : Finset Plane, ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
      ∀ d ∈ D, Disjoint K.openCarrier (d +ᵥ K.openCarrier) →
            Disjoint Kφ.openCarrier (deformPoint φ d +ᵥ Kφ.openCarrier) := by
  classical
  intro K P hKP D
  let L : Finset RationalLine :=
    P.flatten.toFinset ∪ D.biUnion (fun d => (P.flatten.map (translatedLine d)).toFinset)
  obtain ⟨F, ε, hε, htransport⟩ := finiteRationalArrangement_transport L ∅
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ d hd hdisj
  obtain ⟨H, _, hsign⟩ := htransport φ hφ
  have hbaseSign : ∀ l ∈ P.flatten, ∀ z : Plane,
      Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z) := by
    intro l hl z
    exact hsign l (Finset.mem_union.mpr (Or.inl (List.mem_toFinset.mpr hl))) z
  have hbase := support_image_of_signs P φ H hbaseSign
  have htranslatedSign : ∀ l ∈ (translatedCode d P).flatten, ∀ z : Plane,
      Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z) := by
    intro l hl z
    change l ∈ List.flatten (P.map (fun cell => cell.map (translatedLine d))) at hl
    rcases List.mem_flatten.mp hl with ⟨cell', hcell', hline⟩
    rcases List.mem_map.mp hcell' with ⟨cell, hcell, rfl⟩
    rcases List.mem_map.mp hline with ⟨l₀, hl₀, rfl⟩
    have hmem : translatedLine d l₀ ∈ L := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨d, hd, ?_⟩
      have hlflat : l₀ ∈ P.flatten := List.mem_flatten.mpr ⟨cell, hcell, hl₀⟩
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l₀, hlflat, rfl⟩)
    simpa using hsign (translatedLine d l₀) hmem z
  have htrans := support_image_of_signs (translatedCode d P) φ H htranslatedSign
  rw [deform_translatedCode] at htrans
  have hsrcTrans := translatedCode_support d P
  have htgtTrans := translatedCode_support (deformPoint φ d)
    (P.map (fun cell => cell.map (deformLine φ)))
  have htargetEq :
      polyhedralSupport (P.map (fun cell => cell.map (deformLine φ))) = Kφ.support := by
    simpa [deformedPolyhedralSupport] using hKφ.symm
  have hbaseInterior : H '' K.openCarrier = Kφ.openCarrier := by
    change H '' interior K.support = interior Kφ.support
    calc
      H '' interior K.support = interior (H '' K.support) := H.image_interior _
      _ = interior (polyhedralSupport (P.map (fun cell => cell.map (deformLine φ)))) := by
        rw [← hKP, hbase]
      _ = interior Kφ.support := by rw [htargetEq]
  have htransInterior :
      H '' (d +ᵥ K.openCarrier) = deformPoint φ d +ᵥ Kφ.openCarrier := by
    change H '' (d +ᵥ interior K.support) =
      deformPoint φ d +ᵥ interior Kφ.support
    rw [← interior_vadd, H.image_interior, ← hKP, ← hsrcTrans, htrans, htgtTrans, htargetEq,
      interior_vadd]
  simpa only [hbaseInterior, htransInterior] using
    image_disjoint_of_injective H H.injective hdisj

theorem flcPackingTransport :
  ∀ (K : PolygonalRegion) (P : PolyhedralCode) (T : Set Plane),
    polyhedralSupport P = K.support → Tiling.Polygonal.HasFLC T → RelativeDense T →
    Tiling.IsPacking K.prototileFamily (K.placements T) →
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
            Tiling.IsPacking Kφ.prototileFamily (Kφ.placements (deformPoint φ '' T)) ∧
              Set.InjOn (deformPoint φ) T := by
  classical
  intro K P T hP hT hdense hp
  obtain ⟨B, hB, _, F₁, ε₁, hε₁, hbound⟩ := code_uniformBound K P hP
  let M := 4 * B + 2
  have hM : 0 < M := by dsimp [M]; linarith
  let D := (hT.2 M hM).toFinset
  obtain ⟨F₂, ε₂, hε₂, hpairs⟩ := finitePair_packing K P hP D
  obtain ⟨F₃, ε₃, hε₃, hmetric⟩ :=
    approximation_boundedMetricAndRelationControl T hT hdense M 1 ∅ hM (by norm_num)
  refine ⟨F₁ ∪ F₂ ∪ F₃, min ε₁ (min ε₂ ε₃),
    lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro φ hφ Kφ hKφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ :=
    finiteApproximation_strengthen _ _ _ _ φ
      (by intro x hx; simp only [Finset.mem_union]; tauto) (min_le_left _ _) hφ
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ :=
    finiteApproximation_strengthen _ _ _ _ φ
      (by intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (min_le_left _ _)) hφ
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ :=
    finiteApproximation_strengthen _ _ _ _ φ
      (by intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (min_le_right _ _)) hφ
  have hboundφ := hbound φ hφ₁ Kφ hKφ
  obtain ⟨hinj, _, hinverse, _⟩ := hmetric φ hφ₃
  refine ⟨(Tiling.Polygonal.isPacking_iff_openCarrier_disjoint Kφ _).mpr ?_, hinj⟩
  rintro y ⟨s, hs, rfl⟩ z ⟨t, ht, rfl⟩ hstφ
  have hst : s ≠ t := fun h => hstφ (congrArg (deformPoint φ) h)
  by_contra hoverlap
  have himage := overlap_distance_bound Kφ B hboundφ
    (deformPoint φ s) (deformPoint φ t) hoverlap
  have hshort : dist (deformPoint φ s) (deformPoint φ t) < M / 2 := by
    dsimp [M]
    linarith
  have hsource := hinverse s hs t ht hshort
  have hd : t - s ∈ D := by
    apply (hT.2 M hM).mem_toFinset.mpr
    refine ⟨Set.mem_sub.mpr ⟨t, ht, s, hs, rfl⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm, dist_comm]
    exact hsource.le
  have hsrc := (pair_disjoint_iff K s t).mp
    ((Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K T).mp hp hs ht hst)
  have htarget := hpairs φ hφ₂ Kφ hKφ (t - s) hd hsrc
  have hsub := (deformPointLinear φ).map_sub t s
  change deformPoint φ (t - s) = deformPoint φ t - deformPoint φ s at hsub
  rw [hsub] at htarget
  exact hoverlap ((pair_disjoint_iff Kφ _ _).mpr htarget)

private theorem masterStar_regularGerms
    (K Kφ : PolygonalRegion) (T : Set Plane) (W D : Finset Plane)
    (φ : ℝ →ₗ[ℚ] ℚ) (B A : ℝ) (hB : 0 < B) (hA : 0 < A)
    (hK : ∀ z ∈ K.support, ‖z‖ ≤ B) (hKφ : ∀ z ∈ Kφ.support, ‖z‖ ≤ B)
    (hW : ∀ w ∈ W, ‖w‖ ≤ A) (hWφ : ∀ w ∈ W, ‖deformPoint φ w‖ ≤ A)
    (hD : ∀ d ∈ T - T, ‖d‖ ≤ 2 * (1 + A + B) → d ∈ D)
    (hlower : ∀ s ∈ T, ∀ t ∈ T, ‖s - t‖ ≤ 2 * ‖deformPoint φ (s - t)‖)
    (hp : Tiling.IsPacking K.prototileFamily (K.placements T))
    (hpφ : Tiling.IsPacking Kφ.prototileFamily (Kφ.placements (deformPoint φ '' T)))
    (hstar : ∀ d ∈ D, ∀ w ∈ W,
      Tiling.Polygonal.SameGermAt (d +ᵥ K.support) w
        (deformPoint φ d +ᵥ Kφ.support) (deformPoint φ w)) :
    ∀ S ⊆ T, ∀ v ∈ decoratedCloud W T,
      Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K S) v
        (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) (deformPoint φ v) := by
  classical
  intro S hST v hv
  obtain ⟨w, hw, t, ht, rfl⟩ := Set.mem_add.mp hv
  have hvmap : deformPoint φ (w + t) = deformPoint φ w + deformPoint φ t :=
    (deformPointLinear φ).map_add w t
  have hcont : Tendsto (fun z : Plane => z - t) (𝓝 (w + t)) (𝓝 w) := by
    have h := (continuous_id.sub continuous_const :
      Continuous (fun z : Plane => z - t)).continuousAt (x := w + t)
    have htend : Tendsto (fun z : Plane => z - t) (𝓝 (w + t)) (𝓝 ((w + t) - t)) := h.tendsto
    simpa only [add_sub_cancel_right] using htend
  have hevents : ∀ d ∈ D, ∀ᶠ z in 𝓝 (w + t),
      (z - t - d ∈ K.support) ↔
        (z - t - (w - deformPoint φ w) - deformPoint φ d ∈ Kφ.support) := by
    intro d hd
    have h := (hstar d hd w hw).comp_tendsto hcont
    filter_upwards [h] with z hz
    change ((z - t) ∈ d +ᵥ K.support) =
      ((z - t) ∈ (w - deformPoint φ w) +ᵥ (deformPoint φ d +ᵥ Kφ.support)) at hz
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hz
    have ha : -d + (z - t) = z - t - d := by abel
    have hb : -deformPoint φ d + (-(w - deformPoint φ w) + (z - t)) =
        z - t - (w - deformPoint φ w) - deformPoint φ d := by abel
    rw [ha, hb] at hz
    exact eq_iff_iff.mp hz
  have hall := D.eventually_all.mpr hevents
  have hball : ∀ᶠ z in 𝓝 (w + t), dist z (w + t) < 1 :=
    Metric.ball_mem_nhds (w + t) (by norm_num)
  have hsource (z s : Plane) (hs : s ∈ T) (hz : dist z (w + t) < 1)
      (hmem : z - s ∈ K.support) : s - t ∈ D := by
    apply hD (s - t) (Set.mem_sub.mpr ⟨s, hs, t, ht, rfl⟩)
    have hz' : ‖z - (w + t)‖ < 1 := by rwa [dist_eq_norm] at hz
    have heq : s - t = (z - (w + t)) + w - (z - s) := by abel
    have hn : ‖s - t‖ ≤ ‖z - (w + t)‖ + ‖w‖ + ‖z - s‖ := by
      rw [heq]
      linarith [norm_sub_le (z - (w + t) + w) (z - s),
        norm_add_le (z - (w + t)) w]
    linarith [hW w hw, hK (z - s) hmem]
  have himage (z s : Plane) (hs : s ∈ T) (hz : dist z (w + t) < 1)
      (hmem : z - (w + t - deformPoint φ (w + t)) - deformPoint φ s ∈ Kφ.support) :
      s - t ∈ D := by
    apply hD (s - t) (Set.mem_sub.mpr ⟨s, hs, t, ht, rfl⟩)
    have hz' : ‖z - (w + t)‖ < 1 := by rwa [dist_eq_norm] at hz
    have hsub : deformPoint φ (s - t) = deformPoint φ s - deformPoint φ t :=
      (deformPointLinear φ).map_sub s t
    have heq : deformPoint φ (s - t) = (z - (w + t)) + deformPoint φ w -
        (z - (w + t - deformPoint φ (w + t)) - deformPoint φ s) := by
      rw [hsub, hvmap]
      abel
    have hn : ‖deformPoint φ (s - t)‖ ≤ ‖z - (w + t)‖ + ‖deformPoint φ w‖ +
        ‖z - (w + t - deformPoint φ (w + t)) - deformPoint φ s‖ := by
      rw [heq]
      linarith [norm_sub_le (z - (w + t) + deformPoint φ w)
        (z - (w + t - deformPoint φ (w + t)) - deformPoint φ s),
        norm_add_le (z - (w + t)) (deformPoint φ w)]
    linarith [hWφ w hw, hKφ _ hmem, hlower s hs t ht]
  change Tiling.Polygonal.regularSupport K S =ᶠ[𝓝 (w + t)]
    ((w + t - deformPoint φ (w + t)) +ᵥ
      Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S))
  rw [regularSupport_eq_interior_supportUnion K S (packing_subfamily hp hST),
    regularSupport_eq_interior_supportUnion Kφ _ (packing_subfamily hpφ (Set.image_mono hST)),
    ← interior_vadd]
  apply interior_germ_of_support_germ
  filter_upwards [hall, hball] with z hz hdist
  apply propext
  change (∃ s ∈ S, z - s ∈ K.support) ↔
    z ∈ ((w + t - deformPoint φ (w + t)) +ᵥ supportUnion Kφ (deformPoint φ '' S))
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  change (∃ s ∈ S, z - s ∈ K.support) ↔
    ∃ y ∈ deformPoint φ '' S, (-(w + t - deformPoint φ (w + t)) +ᵥ z) - y ∈ Kφ.support
  have hdiff (s : Plane) : z - t - (s - t) = z - s := by abel
  have hdiffφ (s : Plane) : z - t - (w - deformPoint φ w) - deformPoint φ (s - t) =
      (-(w + t - deformPoint φ (w + t)) +ᵥ z) - deformPoint φ s := by
    have hsub : deformPoint φ (s - t) = deformPoint φ s - deformPoint φ t :=
      (deformPointLinear φ).map_sub s t
    rw [hvmap, hsub]
    change _ = (-(w + t - (deformPoint φ w + deformPoint φ t)) + z) - deformPoint φ s
    abel
  constructor
  · rintro ⟨s, hs, hmem⟩
    refine ⟨deformPoint φ s, ⟨s, hs, rfl⟩, ?_⟩
    have h := (hz (s - t) (hsource z s (hST hs) hdist hmem)).mp
      ((hdiff s).symm ▸ hmem)
    rwa [hdiffφ s] at h
  · rintro ⟨y, ⟨s, hs, rfl⟩, hmem⟩
    have hm : z - (w + t - deformPoint φ (w + t)) - deformPoint φ s ∈ Kφ.support := by
      simpa only [vadd_eq_add, neg_add_eq_sub] using hmem
    have h := (hz (s - t) (himage z s (hST hs) hdist hm)).mpr
      ((hdiffφ s).symm ▸ hmem)
    exact ⟨s, hs, (hdiff s) ▸ h⟩

private theorem finitePairs_packing_of_coarseLower
    (K Kφ : PolygonalRegion) (T : Set Plane) (D : Finset Plane)
    (φ : ℝ →ₗ[ℚ] ℚ) (B : ℝ)
    (hbound : Kφ.support ⊆ Metric.closedBall 0 B)
    (hD : ∀ d ∈ T - T, ‖d‖ ≤ 4 * B → d ∈ D)
    (hlower : ∀ s ∈ T, ∀ t ∈ T, ‖s - t‖ ≤ 2 * ‖deformPoint φ (s - t)‖)
    (hp : Tiling.IsPacking K.prototileFamily (K.placements T))
    (hpairs : ∀ d ∈ D, Disjoint K.openCarrier (d +ᵥ K.openCarrier) →
      Disjoint Kφ.openCarrier (deformPoint φ d +ᵥ Kφ.openCarrier)) :
    Tiling.IsPacking Kφ.prototileFamily (Kφ.placements (deformPoint φ '' T)) := by
  apply (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint Kφ _).mpr
  rintro y ⟨s, hs, rfl⟩ z ⟨t, ht, rfl⟩ hstφ
  have hst : s ≠ t := fun h => hstφ (congrArg (deformPoint φ) h)
  by_contra hoverlap
  have himage := overlap_distance_bound Kφ B hbound
    (deformPoint φ s) (deformPoint φ t) hoverlap
  have hsub : deformPoint φ (t - s) = deformPoint φ t - deformPoint φ s :=
    (deformPointLinear φ).map_sub t s
  have hd : t - s ∈ D := by
    apply hD (t - s) (Set.mem_sub.mpr ⟨t, ht, s, hs, rfl⟩)
    have hlower' := hlower t ht s hs
    rw [hsub] at hlower'
    have hnormimage : ‖deformPoint φ t - deformPoint φ s‖ ≤ 2 * B := by
      simpa only [dist_eq_norm, norm_sub_rev] using himage
    linarith
  have hsrc := (pair_disjoint_iff K s t).mp
    ((Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K T).mp hp hs ht hst)
  have htarget := hpairs (t - s) hd hsrc
  rw [hsub] at htarget
  exact hoverlap ((pair_disjoint_iff Kφ _ _).mpr htarget)

private theorem injOn_of_relativeError
    (φ : ℝ →ₗ[ℚ] ℚ) (Y : Set Plane)
    (hrelative : ∀ x ∈ Y, ∀ y ∈ Y,
      ‖deformPoint φ (x - y) - (x - y)‖ ≤ (1 / 2 : ℝ) * dist x y) :
    Set.InjOn (deformPoint φ) Y := by
  intro x hx y hy hxy
  have h := coarse_lower_of_relativeError φ (x - y)
    (by simpa only [dist_eq_norm] using hrelative x hx y hy)
  have hsub : deformPoint φ (x - y) = deformPoint φ x - deformPoint φ y :=
    (deformPointLinear φ).map_sub x y
  rw [hsub, hxy, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

theorem flcAllSubfamilyGerms :
  ∀ (K : PolygonalRegion) (P : PolyhedralCode) (W : Finset Plane) (T : Set Plane),
    polyhedralSupport P = K.support → W.Nonempty →
    Tiling.Polygonal.HasFLC T → RelativeDense T →
    Tiling.IsPacking K.prototileFamily (K.placements T) →
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
            ∀ S ⊆ T, ∀ v ∈ decoratedCloud W T,
              Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K S) v
                (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) (deformPoint φ v) := by
  classical
  intro K P W T hP _ hT hdense hp
  obtain ⟨B, hB, hKbound, F₁, ε₁, hε₁, hbound⟩ := code_uniformBound K P hP
  obtain ⟨A, hA, hWbound, F₂, ε₂, hε₂, hWimage⟩ := points_uniformBound W
  let R := 2 * (1 + A + B)
  have hR : 0 < R := by dsimp [R]; positivity
  let D := (hT.2 R hR).toFinset
  obtain ⟨F₃, ε₃, hε₃, hstars⟩ := finiteStar_support_germs K P hP D W
  obtain ⟨F₄, ε₄, hε₄, hpacking⟩ := flcPackingTransport K P T hP hT hdense hp
  obtain ⟨F₅, ε₅, hε₅, hrelative⟩ :=
    approximation_globalRelativeError T hT hdense (1 / 2) (by norm_num) (by norm_num)
  let F := F₁ ∪ F₂ ∪ F₃ ∪ F₄ ∪ F₅
  let ε := min ε₁ (min ε₂ (min ε₃ (min ε₄ ε₅)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ :=
    finiteApproximation_strengthen F₁ F ε₁ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (min_le_left _ _) hφ
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ :=
    finiteApproximation_strengthen F₂ F ε₂ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (min_le_left _ _)) hφ
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ :=
    finiteApproximation_strengthen F₃ F ε₃ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))) hφ
  have hφ₄ : IsFiniteApproximation F₄ ε₄ φ :=
    finiteApproximation_strengthen F₄ F ε₄ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))) hφ
  have hφ₅ : IsFiniteApproximation F₅ ε₅ φ :=
    finiteApproximation_strengthen F₅ F ε₅ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))) hφ
  have htarget := hbound φ hφ₁ Kφ hKφ
  have hKnorm : ∀ z ∈ K.support, ‖z‖ ≤ B := by
    simpa only [Set.subset_def, Metric.mem_closedBall, dist_zero_right] using hKbound
  have hKφnorm : ∀ z ∈ Kφ.support, ‖z‖ ≤ B := by
    simpa only [Set.subset_def, Metric.mem_closedBall, dist_zero_right] using htarget
  apply masterStar_regularGerms K Kφ T W D φ B A hB hA hKnorm hKφnorm
    hWbound (hWimage φ hφ₂) ?_ ?_ hp (hpacking φ hφ₄ Kφ hKφ).1
    (hstars φ hφ₃ Kφ hKφ)
  · intro d hd hnorm
    exact (hT.2 R hR).mem_toFinset.mpr
      ⟨hd, by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm⟩
  · intro s hs t ht
    apply coarse_lower_of_relativeError φ (s - t)
    simpa only [dist_eq_norm] using hrelative φ hφ₅ s hs t ht

/-- Once both real decorations and local germs are proved, provenance recovers exactly the
proper vertices; it does not postulate an exact intrinsic vertex-set identification. -/
theorem decoratedProperVertices_transport :
  ∀ (K Kφ : PolygonalRegion) (W : Finset Plane) (S : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ),
    Decorates K W → Decorates Kφ (W.image (deformPoint φ)) →
    Tiling.IsPacking K.prototileFamily (K.placements S) →
    Tiling.IsPacking Kφ.prototileFamily (Kφ.placements (deformPoint φ '' S)) →
    (∀ v ∈ decoratedCloud W S,
      Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K S) v
        (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) (deformPoint φ v)) →
      Tiling.Polygonal.properVertices
        (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) =
          deformPoint φ '' Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport K S) := by
  intro K Kφ W S φ hW hWφ hp hpφ hg
  have sourceMark : ∀ x ∈ Tiling.Polygonal.properVertices
      (Tiling.Polygonal.regularSupport K S), x ∈ decoratedCloud W S := by
    intro x hx
    obtain ⟨v, hv, s, hs, rfl⟩ := Tiling.Polygonal.properVertexProvenance hp x hx
    exact Set.mem_add.mpr ⟨v, decorates_intrinsicVertices K W hW hv, s, hs, rfl⟩
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨v, hv, s, hs, hys⟩ := Tiling.Polygonal.properVertexProvenance hpφ y hy
    have hvW := decorates_intrinsicVertices Kφ (W.image (deformPoint φ)) hWφ hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hvW
    obtain ⟨t, ht, hts⟩ := hs
    have hx : w + t ∈ decoratedCloud W S :=
      Set.mem_add.mpr ⟨w, hw, t, ht, rfl⟩
    have hmap : deformPoint φ (w + t) = y := by
      rw [hys, ← hwv, ← hts]
      exact (deformPointLinear φ).map_add w t
    refine ⟨w + t, ?_, hmap⟩
    exact (properVertex_iff_of_sameGerm (hg (w + t) hx)).mpr (hmap.symm ▸ hy)
  · rintro y ⟨x, hx, rfl⟩
    exact (properVertex_iff_of_sameGerm (hg x (sourceMark x hx))).mp hx

/-- The initial and persistent fibre constructor is a real line-relative-density theorem,
not a wrapper assuming that a planar FLC deformation already exists. -/
theorem finiteFLCFibre_germEquivalence :
  ∀ (K : PolygonalRegion) (S : Set Plane) (δ : Submodule ℝ Plane) (a : Plane),
    Tiling.RationalSlopes.HasRationalSlopes K → Module.finrank ℝ δ = 1 →
    Tiling.RationalSlopes.HasRationalDirection δ → Tiling.Polygonal.HasFLC S →
    (∀ s ∈ S, s - a ∈ δ) →
    (∃ ρ : ℝ, 0 < ρ ∧ ∀ z : Plane, z - a ∈ δ →
      ∃ s ∈ S, dist z s < ρ) →
    Tiling.Polygonal.TilesOn K S (Tiling.Polygonal.regularSupport K S) →
      ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
        ∃ W : Finset Plane, Decorates K W ∧ 0 ∈ W ∧
          ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
            ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
              ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ ∧
                Tiling.IsRational Kφ.support ∧ Tiling.RationalSlopes.HasRationalSlopes Kφ ∧
                Decorates Kφ (W.image (deformPoint φ)) ∧
                Set.InjOn (deformPoint φ) (decoratedCloud W S) ∧
                Tiling.Polygonal.TilesOn Kφ (deformPoint φ '' S)
                  (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) ∧
                (∀ U ⊆ S, ∀ v ∈ decoratedCloud W S,
                  Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K U) v
                    (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' U))
                      (deformPoint φ v)) ∧
                (∀ U ⊆ S, Tiling.Polygonal.properVertices
                  (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' U)) =
                    deformPoint φ '' Tiling.Polygonal.properVertices
                      (Tiling.Polygonal.regularSupport K U)) := by
  classical
  intro K S δ a hK hδ hrat hS hline hdense htile
  obtain ⟨n, hn⟩ := rationalDirection_hasNormal δ hδ hrat
  have hlineN : ∀ s ∈ S, normalEval n (s - a) = 0 := by
    intro s hs
    have h := hline s hs
    rw [← hn] at h
    simpa [normalDirection, normalEval, LinearMap.mem_ker] using h
  have hdenseN : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : Plane, normalEval n (z - a) = 0 →
      ∃ s ∈ S, dist z s < ρ := by
    obtain ⟨ρ, hρ, hdense⟩ := hdense
    refine ⟨ρ, hρ, ?_⟩
    intro z hz
    apply hdense z
    rw [← hn]
    simpa [normalDirection, normalEval, LinearMap.mem_ker] using hz
  obtain ⟨P, hP, W, hW, hzero, F₁, ε₁, hε₁, hpolygon⟩ := rationalPolygon_construction K hK
  have hWne : W.Nonempty := ⟨0, hzero⟩
  obtain ⟨B, hB, hKbound, F₂, ε₂, hε₂, hbound⟩ := code_uniformBound K P hP
  obtain ⟨A, hA, hWbound, F₃, ε₃, hε₃, hWimage⟩ := points_uniformBound W
  obtain ⟨F₄, ε₄, hε₄, hrelative⟩ := approximation_lineRelativeError S W n a
    hWne hS hlineN hdenseN (1 / 2) (by norm_num) (by norm_num)
  let R := 4 * (1 + A + B)
  have hR : 0 < R := by dsimp [R]; positivity
  let D := (hS.2 R hR).toFinset
  obtain ⟨F₅, ε₅, hε₅, hstars⟩ := finiteStar_support_germs K P hP D W
  obtain ⟨F₆, ε₆, hε₆, hpairs⟩ := finitePair_packing K P hP D
  let F := F₁ ∪ F₂ ∪ F₃ ∪ F₄ ∪ F₅ ∪ F₆
  let ε := min ε₁ (min ε₂ (min ε₃ (min ε₄ (min ε₅ ε₆))))
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨P, hP, W, hW, hzero, F, ε, hε, ?_⟩
  intro φ hφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ :=
    finiteApproximation_strengthen F₁ F ε₁ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (min_le_left _ _) hφ
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ :=
    finiteApproximation_strengthen F₂ F ε₂ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (min_le_left _ _)) hφ
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ :=
    finiteApproximation_strengthen F₃ F ε₃ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))) hφ
  have hφ₄ : IsFiniteApproximation F₄ ε₄ φ :=
    finiteApproximation_strengthen F₄ F ε₄ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))) hφ
  have hφ₅ : IsFiniteApproximation F₅ ε₅ φ :=
    finiteApproximation_strengthen F₅ F ε₅ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))) hφ
  have hφ₆ : IsFiniteApproximation F₆ ε₆ φ :=
    finiteApproximation_strengthen F₆ F ε₆ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))) hφ
  obtain ⟨Kφ, hKφ, hrational, hslopes, hWφ, _⟩ := hpolygon φ hφ₁
  have hcloudRelative := hrelative φ hφ₄
  have hcentres : S ⊆ decoratedCloud W S := by
    intro s hs
    exact Set.mem_add.mpr ⟨0, hzero, s, hs, zero_add s⟩
  have hlower : ∀ s ∈ S, ∀ t ∈ S, ‖s - t‖ ≤ 2 * ‖deformPoint φ (s - t)‖ := by
    intro s hs t ht
    apply coarse_lower_of_relativeError φ (s - t)
    simpa only [dist_eq_norm] using hcloudRelative s (hcentres hs) t (hcentres ht)
  have hD : ∀ d ∈ S - S, ‖d‖ ≤ R → d ∈ D := by
    intro d hd hnorm
    exact (hS.2 R hR).mem_toFinset.mpr
      ⟨hd, by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm⟩
  have htarget := hbound φ hφ₂ Kφ hKφ
  have hp := htile.2.1
  have hpφ := finitePairs_packing_of_coarseLower K Kφ S D φ B htarget
    (fun d hd hnorm => hD d hd (by dsimp [R]; linarith)) hlower hp
    (hpairs φ hφ₆ Kφ hKφ)
  have hKnorm : ∀ z ∈ K.support, ‖z‖ ≤ B := by
    simpa only [Set.subset_def, Metric.mem_closedBall, dist_zero_right] using hKbound
  have hKφnorm : ∀ z ∈ Kφ.support, ‖z‖ ≤ B := by
    simpa only [Set.subset_def, Metric.mem_closedBall, dist_zero_right] using htarget
  have hg := masterStar_regularGerms K Kφ S W D φ B A hB hA hKnorm hKφnorm
    hWbound (hWimage φ hφ₃)
    (fun d hd hnorm => hD d hd (by dsimp [R]; linarith)) hlower hp hpφ
    (hstars φ hφ₅ Kφ hKφ)
  refine ⟨Kφ, hKφ, hrational, hslopes, hWφ,
    injOn_of_relativeError φ (decoratedCloud W S) hcloudRelative,
    Tiling.Polygonal.tilesOn_regularSupport_of_packing hpφ, hg, ?_⟩
  intro U hUS
  apply decoratedProperVertices_transport K Kφ W U φ hW hWφ
    (packing_subfamily hp hUS) (packing_subfamily hpφ (Set.image_mono hUS))
  intro v hv
  exact hg U hUS v (Set.add_subset_add_left hUS hv)

theorem flcRationalDeformation :
  ∀ (K : PolygonalRegion) (T : Set Plane), Tiling.RationalSlopes.HasRationalSlopes K →
    Tiling.Polygonal.HasFLC T → RelativeDense T →
    Tiling.Polygonal.TilesOn K T (Tiling.Polygonal.regularSupport K T) →
      ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
        ∃ W : Finset Plane, Decorates K W ∧ 0 ∈ W ∧
        ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
          ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
            ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ ∧
              Tiling.IsRational Kφ.support ∧ Tiling.RationalSlopes.HasRationalSlopes Kφ ∧
              Decorates Kφ (W.image (deformPoint φ)) ∧
              Set.InjOn (deformPoint φ) (decoratedCloud W T) ∧
              Tiling.Polygonal.TilesOn Kφ (deformPoint φ '' T)
                (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' T)) ∧
              Tiling.Polygonal.HasFLC (deformPoint φ '' T) ∧
              (∀ S ⊆ T, ∀ v ∈ decoratedCloud W T,
                Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K S) v
                  (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) (deformPoint φ v)) ∧
              (∀ S ⊆ T, Tiling.Polygonal.properVertices
                (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) =
                  deformPoint φ '' Tiling.Polygonal.properVertices
                    (Tiling.Polygonal.regularSupport K S)) := by
  classical
  intro K T hK hT hdense htile
  obtain ⟨P, hP, W, hW, hzero, F₁, ε₁, hε₁, hpolygon⟩ :=
    rationalPolygon_construction K hK
  have hWne : W.Nonempty := ⟨0, hzero⟩
  have hp := htile.2.1
  obtain ⟨F₂, ε₂, hε₂, hpacking⟩ := flcPackingTransport K P T hP hT hdense hp
  obtain ⟨F₃, ε₃, hε₃, hgerms⟩ := flcAllSubfamilyGerms K P W T hP hWne hT hdense hp
  obtain ⟨F₄, ε₄, hε₄, hcloud⟩ := approximation_boundedMetricAndRelationControl
    (decoratedCloud W T) (cloud_hasFLC hT) (cloud_relativeDense hWne hdense)
    1 1 ∅ (by norm_num) (by norm_num)
  obtain ⟨F₅, ε₅, hε₅, hflc⟩ := approximation_preservesFLC T hT hdense
  let F := F₁ ∪ F₂ ∪ F₃ ∪ F₄ ∪ F₅
  let ε := min ε₁ (min ε₂ (min ε₃ (min ε₄ ε₅)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨P, hP, W, hW, hzero, F, ε, hε, ?_⟩
  intro φ hφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ :=
    finiteApproximation_strengthen F₁ F ε₁ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (min_le_left _ _) hφ
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ :=
    finiteApproximation_strengthen F₂ F ε₂ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (min_le_left _ _)) hφ
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ :=
    finiteApproximation_strengthen F₃ F ε₃ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))) hφ
  have hφ₄ : IsFiniteApproximation F₄ ε₄ φ :=
    finiteApproximation_strengthen F₄ F ε₄ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))) hφ
  have hφ₅ : IsFiniteApproximation F₅ ε₅ φ :=
    finiteApproximation_strengthen F₅ F ε₅ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))) hφ
  obtain ⟨Kφ, hKφ, hrational, hslopes, hWφ, _⟩ := hpolygon φ hφ₁
  have hpφ := (hpacking φ hφ₂ Kφ hKφ).1
  have hg := hgerms φ hφ₃ Kφ hKφ
  refine ⟨Kφ, hKφ, hrational, hslopes, hWφ, (hcloud φ hφ₄).1,
    Tiling.Polygonal.tilesOn_regularSupport_of_packing hpφ, hflc φ hφ₅, hg, ?_⟩
  intro S hST
  apply decoratedProperVertices_transport K Kφ W S φ hW hWφ
    (packing_subfamily hp hST) (packing_subfamily hpφ (Set.image_mono hST))
  intro v hv
  apply hg S hST v
  exact Set.add_subset_add_left hST hv

private def incidenceCoord (w z : Plane) : ℝ :=
  if w.re ≠ 0 then z.re else z.im

private theorem incidenceCoord_self_ne {w : Plane} (hw : w ≠ 0) :
    incidenceCoord w w ≠ 0 := by
  by_cases hre : w.re ≠ 0
  · simp [incidenceCoord, hre]
  · have him : w.im ≠ 0 := by
      intro him
      apply hw
      apply Complex.ext
      · exact not_ne_iff.mp hre
      · exact him
    simp [incidenceCoord, hre, him]

private theorem incidenceCoord_smul (w : Plane) (r : ℝ) :
    incidenceCoord w (r • w) = r * incidenceCoord w w := by
  by_cases hre : w.re ≠ 0
  · simp [incidenceCoord, hre]
  · simp [incidenceCoord, hre]

private theorem pos_of_same_sign_mul {r x : ℝ} (hx : x ≠ 0)
    (hs : Real.sign (r * x) = Real.sign x) : 0 < r := by
  rcases lt_trichotomy x 0 with hxneg | rfl | hxpos
  · rcases lt_trichotomy r 0 with hrneg | rfl | hrpos
    · have hp : 0 < r * x := mul_pos_of_neg_of_neg hrneg hxneg
      rw [Real.sign_of_pos hp, Real.sign_of_neg hxneg] at hs
      norm_num at hs
    · simp [Real.sign_zero, Real.sign_of_neg hxneg] at hs
    · exact hrpos
  · exact (hx rfl).elim
  · rcases lt_trichotomy r 0 with hrneg | rfl | hrpos
    · have hn : r * x < 0 := mul_neg_of_neg_of_pos hrneg hxpos
      rw [Real.sign_of_neg hn, Real.sign_of_pos hxpos] at hs
      norm_num at hs
    · simp [Real.sign_zero, Real.sign_of_pos hxpos] at hs
    · exact hrpos

private theorem openSegment_iff_span_sign {a b v : Plane} (hab : a ≠ b) :
    v ∈ openSegment ℝ a b ↔
      v - a ∈ Submodule.span ℝ ({b - a} : Set Plane) ∧
      b - v ∈ Submodule.span ℝ ({b - a} : Set Plane) ∧
      Real.sign (incidenceCoord (b - a) (v - a)) =
        Real.sign (incidenceCoord (b - a) (b - a)) ∧
      Real.sign (incidenceCoord (b - a) (b - v)) =
        Real.sign (incidenceCoord (b - a) (b - a)) := by
  constructor
  · intro h
    rcases h with ⟨s, t, hs, ht, hst, hv⟩
    have hu : v - a = t • (b - a) := by
      rw [← hv]
      have hs' : s = 1 - t := by linarith
      rw [hs']
      module
    have hq : b - v = s • (b - a) := by
      rw [← hv]
      have ht' : t = 1 - s := by linarith
      rw [ht']
      module
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hu]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [hq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [hu, incidenceCoord_smul]
      rcases lt_or_gt_of_ne (incidenceCoord_self_ne (sub_ne_zero.mpr hab.symm)) with hc | hc
      · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg ht hc), Real.sign_of_neg hc]
      · rw [Real.sign_of_pos (mul_pos ht hc), Real.sign_of_pos hc]
    · rw [hq, incidenceCoord_smul]
      rcases lt_or_gt_of_ne (incidenceCoord_self_ne (sub_ne_zero.mpr hab.symm)) with hc | hc
      · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hs hc), Real.sign_of_neg hc]
      · rw [Real.sign_of_pos (mul_pos hs hc), Real.sign_of_pos hc]
  · rintro ⟨hu, hq, hsu, hsq⟩
    obtain ⟨r, hrvec⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨s, hsvec⟩ := Submodule.mem_span_singleton.mp hq
    have huv : v - a = r • (b - a) := hrvec.symm
    have hqv : b - v = s • (b - a) := hsvec.symm
    have hw : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    have hc : incidenceCoord (b - a) (b - a) ≠ 0 := incidenceCoord_self_ne hw
    have hr : 0 < r := by
      apply pos_of_same_sign_mul hc
      rw [huv, incidenceCoord_smul] at hsu
      change Real.sign (r * incidenceCoord (b - a) (b - a)) =
        Real.sign (incidenceCoord (b - a) (b - a)) at hsu
      exact hsu
    have hs : 0 < s := by
      apply pos_of_same_sign_mul hc
      rw [hqv, incidenceCoord_smul] at hsq
      change Real.sign (s * incidenceCoord (b - a) (b - a)) =
        Real.sign (incidenceCoord (b - a) (b - a)) at hsq
      exact hsq
    have hsumvec : (r + s - 1) • (b - a) = 0 := by
      have h : r • (b - a) + s • (b - a) = b - a := by
        rw [← huv, ← hqv]
        abel
      rw [sub_smul, add_smul, h]
      simp
    have hsum : r + s = 1 := by
      rcases smul_eq_zero.mp hsumvec with h | h
      · linarith
      · exact (hw h).elim
    have hsum' : s + r = 1 := by linarith
    refine ⟨s, r, hs, hr, hsum', ?_⟩
    have hv : v = a + r • (b - a) := by calc
      v = a + (v - a) := by abel
      _ = a + r • (b - a) := by rw [huv]
    rw [hv, show b = a + (b - a) by abel]
    rw [smul_add]
    simp only [add_sub_cancel_left]
    rw [← add_assoc, ← add_smul, hsum', one_smul]

private theorem incidence_upper_of_relativeError
    (φ : ℝ →ₗ[ℚ] ℚ) (x : Plane)
    (h : ‖deformPoint φ x - x‖ ≤ (1 / 2 : ℝ) * ‖x‖) :
    ‖deformPoint φ x‖ ≤ (3 / 2 : ℝ) * ‖x‖ := by
  have htriangle := norm_add_le (deformPoint φ x - x) x
  rw [sub_add_cancel] at htriangle
  linarith

private theorem incidence_segment_normBounds {a b v : Plane}
    (h : v ∈ openSegment ℝ a b) :
    ‖v - a‖ ≤ ‖b - a‖ ∧ ‖b - v‖ ≤ ‖b - a‖ := by
  rcases h with ⟨s, t, hs, ht, hst, hv⟩
  have hu : v - a = t • (b - a) := by
    rw [← hv]
    have hs' : s = 1 - t := by linarith
    rw [hs']
    module
  have hq : b - v = s • (b - a) := by
    rw [← hv]
    have ht' : t = 1 - s := by linarith
    rw [ht']
    module
  rw [hu, hq, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ht, abs_of_pos hs]
  constructor <;> nlinarith [norm_nonneg (b - a)]

private def incidence_normalFor (w : Plane) : RationalNormal := by
  classical
  exact if hw : Tiling.RationalSlopes.IsRationalVectorDirection w then
    Classical.choose (rationalDirection_hasNormal
      (Submodule.span ℝ ({w} : Set Plane)) (finrank_span_singleton hw.1) hw.2)
  else ⟨1, 0, by norm_num⟩

private theorem incidence_normalFor_spec {w : Plane}
    (hw : Tiling.RationalSlopes.IsRationalVectorDirection w) :
    normalDirection (incidence_normalFor w) = Submodule.span ℝ ({w} : Set Plane) := by
  classical
  simp only [incidence_normalFor, dif_pos hw]
  exact Classical.choose_spec (rationalDirection_hasNormal
    (Submodule.span ℝ ({w} : Set Plane)) (finrank_span_singleton hw.1) hw.2)

private theorem incidence_test_preserves (D : Finset Plane) (φ : ℝ →ₗ[ℚ] ℚ)
    {a b v : Plane} (hab : a ≠ b) (habφ : deformPoint φ a ≠ deformPoint φ b)
    (hw : Tiling.RationalSlopes.IsRationalVectorDirection (b - a))
    (hwd : b - a ∈ D) (hud : v - a ∈ D) (hqd : b - v ∈ D)
    (hre : ∀ z ∈ D, Real.sign (deformPoint φ z).re = Real.sign z.re)
    (him : ∀ z ∈ D, Real.sign (deformPoint φ z).im = Real.sign z.im)
    (hnormal : ∀ z ∈ D,
      Real.sign (normalEval (incidence_normalFor (b - a)) (deformPoint φ z)) =
        Real.sign (normalEval (incidence_normalFor (b - a)) z)) :
    v ∈ openSegment ℝ a b ↔
      deformPoint φ v ∈ openSegment ℝ (deformPoint φ a) (deformPoint φ b) := by
  let n := incidence_normalFor (b - a)
  have hn : normalDirection n = Submodule.span ℝ ({b - a} : Set Plane) :=
    incidence_normalFor_spec hw
  have hzero (z : Plane) (hz : z ∈ D) :
      normalEval n (deformPoint φ z) = 0 ↔ normalEval n z = 0 := by
    rw [← Real.sign_eq_zero_iff, hnormal z hz, Real.sign_eq_zero_iff]
  have hwN : b - a ∈ normalDirection n := by
    rw [hn]
    exact Submodule.subset_span (by simp)
  have hwφN : deformPoint φ (b - a) ∈ normalDirection n := by
    change normalEval n (deformPoint φ (b - a)) = 0
    apply (hzero _ hwd).mpr
    exact hwN
  have hsub (x y : Plane) : deformPoint φ (x - y) = deformPoint φ x - deformPoint φ y :=
    (deformPointLinear φ).map_sub x y
  have hwφne : deformPoint φ (b - a) ≠ 0 := by
    rw [hsub]
    exact sub_ne_zero.mpr habφ.symm
  have hnφ : normalDirection n =
      Submodule.span ℝ ({deformPoint φ (b - a)} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (normalDirection_rational n).1 hwφN hwφne
  have hspan (z : Plane) (hz : z ∈ D) :
      z ∈ Submodule.span ℝ ({b - a} : Set Plane) ↔
        deformPoint φ z ∈ Submodule.span ℝ ({deformPoint φ (b - a)} : Set Plane) := by
    rw [← hn, ← hnφ]
    exact (hzero z hz).symm
  have hreZero : (deformPoint φ (b - a)).re = 0 ↔ (b - a).re = 0 := by
    rw [← Real.sign_eq_zero_iff, hre _ hwd, Real.sign_eq_zero_iff]
  have hcoord (z : Plane) (hz : z ∈ D) :
      Real.sign (incidenceCoord (deformPoint φ (b - a)) (deformPoint φ z)) =
        Real.sign (incidenceCoord (b - a) z) := by
    by_cases hwre : (b - a).re ≠ 0
    · have hwφre : (deformPoint φ (b - a)).re ≠ 0 :=
        fun h => hwre (hreZero.mp h)
      simpa only [incidenceCoord, if_pos hwre, if_pos hwφre] using hre z hz
    · have hwφre : ¬ (deformPoint φ (b - a)).re ≠ 0 := by
        intro h
        exact h (hreZero.mpr (not_ne_iff.mp hwre))
      simpa only [incidenceCoord, if_neg hwre, if_neg hwφre] using him z hz
  rw [openSegment_iff_span_sign hab, openSegment_iff_span_sign habφ,
    ← hsub v a, ← hsub b v, ← hsub b a]
  rw [hcoord _ hud, hcoord _ hqd, hcoord _ hwd]
  exact and_congr (hspan _ hud) (and_congr (hspan _ hqd) Iff.rfl)

theorem flcDeformation_preservesIncidences :
  ∀ (T : Set Plane) (W : Finset Plane) (R : ℝ), W.Nonempty → 0 < R →
    Tiling.Polygonal.HasFLC T → RelativeDense T →
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ v ∈ decoratedCloud W T, ∀ a ∈ decoratedCloud W T,
            ∀ b ∈ decoratedCloud W T, Tiling.RationalSlopes.IsRationalVectorDirection (b - a) →
              dist a b < R →
                (v ∈ openSegment ℝ a b ↔
                  deformPoint φ v ∈ openSegment ℝ (deformPoint φ a) (deformPoint φ b)) := by
  classical
  intro T W R hW hR hT hdense
  let Y := decoratedCloud W T
  have hY : Tiling.Polygonal.HasFLC Y := cloud_hasFLC hT
  have hdenseY : RelativeDense Y := cloud_relativeDense hW hdense
  have hM : 0 < 10 * R := by positivity
  let D := (hY.2 (10 * R) hM).toFinset
  let normals := D.image incidence_normalFor
  let Z := (D.image Complex.re ∪ D.image Complex.im) ∪
    normals.biUnion (fun n => D.image (normalEval n))
  obtain ⟨F₁, ε₁, hε₁, hrelative⟩ :=
    approximation_globalRelativeError Y hY hdenseY (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨F₂, ε₂, hε₂, hsign⟩ := finiteApproximation_signAndEquality Z
  refine ⟨F₁ ∪ F₂, min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro φ hφ v hv a ha b hb hw hdist
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ :=
    finiteApproximation_strengthen _ _ _ _ φ Finset.subset_union_left (min_le_left _ _) hφ
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ :=
    finiteApproximation_strengthen _ _ _ _ φ Finset.subset_union_right (min_le_right _ _) hφ
  have herr := hrelative φ hφ₁
  have hinj := injOn_of_relativeError φ Y herr
  have hsub (x y : Plane) : deformPoint φ (x - y) = deformPoint φ x - deformPoint φ y :=
    (deformPointLinear φ).map_sub x y
  have hlow (x : Plane) (hx : x ∈ Y) (y : Plane) (hy : y ∈ Y) :
      ‖x - y‖ ≤ 2 * ‖deformPoint φ (x - y)‖ :=
    coarse_lower_of_relativeError φ (x - y) (by simpa only [dist_eq_norm] using herr x hx y hy)
  have hupper : ‖deformPoint φ (b - a)‖ ≤ (3 / 2 : ℝ) * ‖b - a‖ :=
    incidence_upper_of_relativeError φ (b - a)
      (by simpa only [dist_eq_norm] using herr b hb a ha)
  have hwbound : ‖b - a‖ < R := by
    simpa only [dist_eq_norm, norm_sub_rev] using hdist
  have hmemD (x : Plane) (hx : x ∈ Y) (y : Plane) (hy : y ∈ Y)
      (hbound : ‖x - y‖ ≤ 10 * R) : x - y ∈ D := by
    apply (hY.2 (10 * R) hM).mem_toFinset.mpr
    refine ⟨Set.mem_sub.mpr ⟨x, hx, y, hy, rfl⟩, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound
  have hwd : b - a ∈ D := hmemD b hb a ha (by linarith)
  have hs := (hsign φ hφ₂).1
  have hre (z : Plane) (hz : z ∈ D) :
      Real.sign (deformPoint φ z).re = Real.sign z.re := by
    have hz' : z.re ∈ Z := Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨z, hz, rfl⟩))))
    exact hs z.re hz'
  have him (z : Plane) (hz : z ∈ D) :
      Real.sign (deformPoint φ z).im = Real.sign z.im := by
    have hz' : z.im ∈ Z := Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨z, hz, rfl⟩))))
    exact hs z.im hz'
  have hnormal (z : Plane) (hz : z ∈ D) :
      Real.sign (normalEval (incidence_normalFor (b - a)) (deformPoint φ z)) =
        Real.sign (normalEval (incidence_normalFor (b - a)) z) := by
    rw [rationalNormal_commutes]
    apply hs
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
      ⟨incidence_normalFor (b - a), Finset.mem_image.mpr ⟨b - a, hwd, rfl⟩,
        Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩))
  have hab : a ≠ b := fun h => hw.1 (by simp [h])
  have habφ : deformPoint φ a ≠ deformPoint φ b := fun h => hab (hinj ha hb h)
  constructor
  · intro hsource
    have hbounds := incidence_segment_normBounds hsource
    have hud := hmemD v hv a ha (by linarith [hbounds.1])
    have hqd := hmemD b hb v hv (by linarith [hbounds.2])
    exact (incidence_test_preserves D φ hab habφ hw hwd hud hqd hre him hnormal).mp hsource
  · intro htarget
    have hbounds := incidence_segment_normBounds htarget
    have huφ : ‖deformPoint φ (v - a)‖ ≤ ‖deformPoint φ (b - a)‖ :=
      by simpa only [hsub] using hbounds.1
    have hqφ : ‖deformPoint φ (b - v)‖ ≤ ‖deformPoint φ (b - a)‖ :=
      by simpa only [hsub] using hbounds.2
    have hud := hmemD v hv a ha (by nlinarith [hlow v hv a ha])
    have hqd := hmemD b hb v hv (by nlinarith [hlow b hb v hv])
    exact (incidence_test_preserves D φ hab habφ hw hwd hud hqd hre him hnormal).mpr htarget

private theorem code_alignedGerm_of_signs (P : PolyhedralCode) (φ : ℝ →ₗ[ℚ] ℚ)
    (x y : Plane)
    (hs : ∀ l ∈ P.flatten,
      Real.sign ((deformLine φ l).eval y) = Real.sign (l.eval x)) :
    Tiling.Polygonal.SameGermAt (polyhedralSupport P) x (deformedPolyhedralSupport P φ) y := by
  classical
  have hlines : ∀ l ∈ P.flatten.toFinset, ∀ᶠ z in 𝓝 x,
      (l.eval z ≤ 0) ↔ ((deformLine φ l).eval (z - (x - y)) ≤ 0) := by
    intro l hl
    have h := halfspace_sign_germ l.normal x (l.eval x) ((deformLine φ l).eval y)
      (hs l (List.mem_toFinset.mp hl))
    filter_upwards [h] with z hz
    change (normalEval l.normal (z - x) + l.eval x ≤ 0) =
      (normalEval l.normal (z - x) + (deformLine φ l).eval y ≤ 0) at hz
    rw [← eval_shift l z x] at hz
    have heq : (deformLine φ l).eval (z - (x - y)) =
        normalEval l.normal (z - x) + (deformLine φ l).eval y := by
      rw [eval_shift (deformLine φ l) _ y]
      change normalEval l.normal _ + _ = _
      congr 2
      abel
    rw [← heq] at hz
    exact eq_iff_iff.mp hz
  have hall := P.flatten.toFinset.eventually_all.mpr hlines
  change polyhedralSupport P =ᶠ[𝓝 x] ((x - y) +ᵥ deformedPolyhedralSupport P φ)
  filter_upwards [hall] with z hz
  apply propext
  change (∃ cell ∈ P, ∀ l ∈ cell, l.eval z ≤ 0) ↔
    z ∈ (x - y) +ᵥ deformedPolyhedralSupport P φ
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, mem_deformedSupport]
  constructor
  · rintro ⟨cell, hc, hcell⟩
    exact ⟨cell, hc, fun l hl => (hz l (List.mem_toFinset.mpr
      (List.mem_flatten.mpr ⟨cell, hc, hl⟩))).mp (hcell l hl)⟩
  · rintro ⟨cell, hc, hcell⟩
    exact ⟨cell, hc, fun l hl => (hz l (List.mem_toFinset.mpr
      (List.mem_flatten.mpr ⟨cell, hc, hl⟩))).mpr (hcell l hl)⟩

private theorem sameGerm_vadd
    {D E : Set Plane} {x y : Plane} (h : Tiling.Polygonal.SameGermAt D x E y)
    (u v : Plane) : Tiling.Polygonal.SameGermAt (u +ᵥ D) (u + x) (v +ᵥ E) (v + y) := by
  have ht : Tendsto (fun z : Plane => z - u) (𝓝 (u + x)) (𝓝 x) := by
    have hcont := (continuous_id.sub continuous_const :
      Continuous (fun z : Plane => z - u)).continuousAt (x := u + x)
    have h' : Tendsto (fun z : Plane => z - u) (𝓝 (u + x)) (𝓝 ((u + x) - u)) := hcont.tendsto
    simpa only [add_sub_cancel_left] using h'
  have hh := h.comp_tendsto ht
  change (u +ᵥ D) =ᶠ[𝓝 (u + x)] (((u + x) - (v + y)) +ᵥ (v +ᵥ E))
  filter_upwards [hh] with z hz
  change ((z - u) ∈ D) = ((z - u) ∈ (x - y) +ᵥ E) at hz
  change (z ∈ u +ᵥ D) = (z ∈ ((u + x) - (v + y)) +ᵥ (v +ᵥ E))
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hz ⊢
  have ha : -u + z = z - u := by abel
  have hb : -v + (-((u + x) - (v + y)) + z) = -(x - y) + (z - u) := by abel
  rwa [ha, hb]

private theorem frontier_vadd_set (u : Plane) (E : Set Plane) :
    frontier (u +ᵥ E) = u +ᵥ frontier E := by
  simp only [← Set.image_vadd]
  exact ((Homeomorph.addLeft u).image_frontier E).symm

private theorem sameGerm_symm
    {D E : Set Plane} {x y : Plane} (h : Tiling.Polygonal.SameGermAt D x E y) :
    Tiling.Polygonal.SameGermAt E y D x := by
  have hh := sameGerm_vadd h (y - x) 0
  have heq : (y - x) + x = y := by abel
  rw [heq, zero_add, zero_vadd] at hh
  change ((y - x) +ᵥ D) =ᶠ[𝓝 y] ((y - y) +ᵥ E) at hh
  simpa only [Tiling.Polygonal.SameGermAt, sub_self, zero_vadd] using hh.symm

private theorem directionalSegment_of_twoGerms
    (D₁ D₂ E₁ E₂ : Set Plane) (η : Submodule ℝ Plane)
    (hlocal : ∀ x : Plane, ∃ y : Plane,
      Tiling.Polygonal.SameGermAt D₁ x E₁ y ∧ Tiling.Polygonal.SameGermAt D₂ x E₂ y)
    (a b : Plane) (hab : a ≠ b) (hη : b - a ∈ η)
    (hsegment : openSegment ℝ a b ⊆ frontier D₁ ∩ frontier D₂) :
    ∃ a' b' : Plane, a' ≠ b' ∧ b' - a' ∈ η ∧
      openSegment ℝ a' b' ⊆ frontier E₁ ∩ frontier E₂ := by
  let e := b - a
  let x := a + (1 / 2 : ℝ) • e
  obtain ⟨y, hg₁, hg₂⟩ := hlocal x
  have hf₁ := Tiling.Polygonal.frontier_eventuallyEq_of_eventuallyEq hg₁
  have hf₂ := Tiling.Polygonal.frontier_eventuallyEq_of_eventuallyEq hg₂
  rw [frontier_vadd_set] at hf₁ hf₂
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff.mp (hf₁.and hf₂)
  let κ := min (1 / 4 : ℝ) (r / (4 * (‖e‖ + 1)))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκsmall : κ ≤ 1 / 4 := min_le_left _ _
  have hκr : κ * (‖e‖ + 1) ≤ r / 4 := by
    have hle : κ ≤ r / (4 * (‖e‖ + 1)) := min_le_right _ _
    have hden : 0 < 4 * (‖e‖ + 1) := by positivity
    have h := (le_div_iff₀ hden).mp hle
    nlinarith
  let p := x - κ • e
  let q := x + κ • e
  have hp : p ∈ openSegment ℝ a b := by
    rw [openSegment_eq_image']
    refine ⟨1 / 2 - κ, ⟨by linarith, by linarith⟩, ?_⟩
    change a + (1 / 2 - κ : ℝ) • e = (a + (1 / 2 : ℝ) • e) - κ • e
    rw [sub_smul]
    abel
  have hq : q ∈ openSegment ℝ a b := by
    rw [openSegment_eq_image']
    refine ⟨1 / 2 + κ, ⟨by linarith, by linarith⟩, ?_⟩
    change a + (1 / 2 + κ : ℝ) • e = (a + (1 / 2 : ℝ) • e) + κ • e
    rw [add_smul]
    abel
  have hpball : p ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : p - x = -(κ • e) := by dsimp [p]; abel
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
    nlinarith [norm_nonneg e]
  have hqball : q ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : q - x = κ • e := by dsimp [q]; abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
    nlinarith [norm_nonneg e]
  have hdiff : q - p = (2 * κ) • e := by
    calc
      q - p = κ • e + κ • e := by dsimp [p, q]; abel
      _ = (2 * κ) • e := by rw [← add_smul]; congr 1; ring
  have hpq : p ≠ q := by
    intro heq
    have hnonzero : (2 * κ) • e ≠ 0 := smul_ne_zero (by positivity)
      (sub_ne_zero.mpr hab.symm)
    rw [heq, sub_self] at hdiff
    exact hnonzero hdiff.symm
  have hsubsegment : openSegment ℝ p q ⊆ openSegment ℝ a b :=
    (convex_openSegment (𝕜 := ℝ) a b).openSegment_subset hp hq
  have hsubball : openSegment ℝ p q ⊆ Metric.ball x r :=
    (convex_ball x r).openSegment_subset hpball hqball
  refine ⟨(y - x) + p, (y - x) + q, ?_, ?_, ?_⟩
  · exact fun h => hpq (add_left_cancel h)
  · rw [add_sub_add_left_eq_sub, hdiff]
    exact η.smul_mem (2 * κ) hη
  · intro z hz
    have hz' : z ∈ (y - x) +ᵥ openSegment ℝ p q := by
      simpa only [vadd_openSegment, vadd_eq_add] using hz
    obtain ⟨c, hc, rfl⟩ := Set.mem_vadd_set.mp hz'
    have hfront := hsegment (hsubsegment hc)
    have hnear' := hnear (Metric.mem_ball.mp (hsubball hc))
    have h₁ : c ∈ (x - y) +ᵥ frontier E₁ := (eq_iff_iff.mp hnear'.1).mp hfront.1
    have h₂ : c ∈ (x - y) +ᵥ frontier E₂ := (eq_iff_iff.mp hnear'.2).mp hfront.2
    have heq : -(x - y) +ᵥ c = (y - x) +ᵥ c := by change _ + c = _ + c; abel
    exact ⟨heq ▸ Set.mem_vadd_set_iff_neg_vadd_mem.mp h₁,
      heq ▸ Set.mem_vadd_set_iff_neg_vadd_mem.mp h₂⟩

private theorem finitePair_supportGerms
    (K : PolygonalRegion) (P : PolyhedralCode) (hP : polyhedralSupport P = K.support)
    (D : Finset Plane) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ d ∈ D, ∃ H : Plane ≃ₜ Plane, ∀ x : Plane,
            Tiling.Polygonal.SameGermAt K.support x Kφ.support (H x) ∧
            Tiling.Polygonal.SameGermAt (d +ᵥ K.support) x
              (deformPoint φ d +ᵥ Kφ.support) (H x) := by
  classical
  let L := P.flatten.toFinset ∪ D.biUnion (fun d => (P.flatten.map (translatedLine d)).toFinset)
  obtain ⟨F, ε, hε, htransport⟩ := finiteRationalArrangement_transport L ∅
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ Kφ hKφ d hd
  obtain ⟨H, _, hs⟩ := htransport φ hφ
  refine ⟨H, ?_⟩
  intro x
  constructor
  · rw [← hP, hKφ]
    apply code_alignedGerm_of_signs P φ x (H x)
    intro l hl
    exact hs l (Finset.mem_union_left _ (List.mem_toFinset.mpr hl)) x
  · have hg := code_alignedGerm_of_signs (translatedCode d P) φ x (H x) ?_
    · have htarget : deformedPolyhedralSupport (translatedCode d P) φ =
          deformPoint φ d +ᵥ Kφ.support := by
        unfold deformedPolyhedralSupport
        rw [deform_translatedCode, translatedCode_support]
        congr 1
        exact hKφ.symm
      rw [translatedCode_support, hP, htarget] at hg
      exact hg
    · intro l hl
      change l ∈ List.flatten (P.map (fun cell => cell.map (translatedLine d))) at hl
      obtain ⟨cell', hc', hl'⟩ := List.mem_flatten.mp hl
      obtain ⟨cell, hc, rfl⟩ := List.mem_map.mp hc'
      obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl'
      apply hs _ _ x
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨d, hd, ?_⟩
      exact List.mem_toFinset.mpr (List.mem_map.mpr
        ⟨l₀, List.mem_flatten.mpr ⟨cell, hc, hl₀⟩, rfl⟩)

private theorem properContact_of_pairGerms
    (K Kφ : PolygonalRegion) (φ : ℝ →ₗ[ℚ] ℚ) (s t : Plane) (H : Plane ≃ₜ Plane)
    (hg : ∀ x : Plane, Tiling.Polygonal.SameGermAt K.support x Kφ.support (H x) ∧
      Tiling.Polygonal.SameGermAt ((t - s) +ᵥ K.support) x
        (deformPoint φ (t - s) +ᵥ Kφ.support) (H x))
    (η : Submodule ℝ Plane) :
    Tiling.RationalSlopes.ProperEdgeContactAlong K η s t ↔
      Tiling.RationalSlopes.ProperEdgeContactAlong Kφ η (deformPoint φ s) (deformPoint φ t) := by
  have hlocal (x : Plane) :
      Tiling.Polygonal.SameGermAt (s +ᵥ K.support) x
        (deformPoint φ s +ᵥ Kφ.support) (deformPoint φ s + H (x - s)) ∧
      Tiling.Polygonal.SameGermAt (t +ᵥ K.support) x
        (deformPoint φ t +ᵥ Kφ.support) (deformPoint φ s + H (x - s)) := by
    have h₁ := sameGerm_vadd (hg (x - s)).1 s (deformPoint φ s)
    have h₂ := sameGerm_vadd (hg (x - s)).2 s (deformPoint φ s)
    have hx : s + (x - s) = x := by abel
    have hst : s + (t - s) = t := by abel
    have hmap : deformPoint φ s + deformPoint φ (t - s) = deformPoint φ t := by
      have hsub : deformPoint φ (t - s) = deformPoint φ t - deformPoint φ s :=
        (deformPointLinear φ).map_sub t s
      rw [hsub]
      abel
    rw [hx] at h₁
    rw [hx, vadd_vadd, vadd_vadd, hst, hmap] at h₂
    exact ⟨h₁, h₂⟩
  have hforward : ∀ x : Plane, ∃ y : Plane,
      Tiling.Polygonal.SameGermAt (s +ᵥ K.support) x (deformPoint φ s +ᵥ Kφ.support) y ∧
      Tiling.Polygonal.SameGermAt (t +ᵥ K.support) x (deformPoint φ t +ᵥ Kφ.support) y :=
    fun x => ⟨_, hlocal x⟩
  have hreverse : ∀ y : Plane, ∃ x : Plane,
      Tiling.Polygonal.SameGermAt (deformPoint φ s +ᵥ Kφ.support) y (s +ᵥ K.support) x ∧
      Tiling.Polygonal.SameGermAt (deformPoint φ t +ᵥ Kφ.support) y (t +ᵥ K.support) x := by
    intro y
    let x := s + H.symm (y - deformPoint φ s)
    have heq : deformPoint φ s + H (x - s) = y := by
      dsimp [x]
      rw [add_sub_cancel_left, H.apply_symm_apply]
      abel
    have hh := hlocal x
    rw [heq] at hh
    exact ⟨x, sameGerm_symm hh.1, sameGerm_symm hh.2⟩
  constructor
  · rintro ⟨a, b, hab, hη, hsegment⟩
    exact directionalSegment_of_twoGerms _ _ _ _ η hforward a b hab hη hsegment
  · rintro ⟨a, b, hab, hη, hsegment⟩
    exact directionalSegment_of_twoGerms _ _ _ _ η hreverse a b hab hη hsegment

private theorem contact_distance_bound
    (K : PolygonalRegion) (B : ℝ) (hbound : ∀ z ∈ K.support, ‖z‖ ≤ B)
    (s t : Plane) (η : Submodule ℝ Plane)
    (hcontact : Tiling.RationalSlopes.ProperEdgeContactAlong K η s t) : dist s t ≤ 2 * B := by
  obtain ⟨a, b, _, _, hsegment⟩ := hcontact
  let x := midpoint ℝ a b
  have hx := hsegment (midpoint_mem_openSegment a b)
  have hxs : x - s ∈ frontier K.support := by
    have h := hx.1
    rw [frontier_vadd_set] at h
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using h
  have hxt : x - t ∈ frontier K.support := by
    have h := hx.2
    rw [frontier_vadd_set] at h
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using h
  have hxs' : x - s ∈ K.support := by
    have h := frontier_subset_closure hxs
    rwa [K.isPolygonal.isClosed.closure_eq] at h
  have hxt' : x - t ∈ K.support := by
    have h := frontier_subset_closure hxt
    rwa [K.isPolygonal.isClosed.closure_eq] at h
  calc
    dist s t ≤ dist s x + dist x t := dist_triangle s x t
    _ = ‖x - s‖ + ‖x - t‖ := by rw [dist_comm s x, dist_eq_norm, dist_eq_norm]
    _ ≤ 2 * B := by linarith [hbound _ hxs', hbound _ hxt']

/-- Proper edge contact includes positive overlap of straight boundary segments. Physical
FT states the equivalent lower segment/collar predicate to avoid importing Part II Links. -/
theorem flcDeformation_preservesProperContacts :
  ∀ (K : PolygonalRegion) (T : Set Plane), Tiling.RationalSlopes.HasRationalSlopes K →
    Tiling.Polygonal.HasFLC T → RelativeDense T →
    Tiling.Polygonal.TilesOn K T (Tiling.Polygonal.regularSupport K T) →
      ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
        ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
          ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
            ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ ∧
              ∀ s ∈ T, ∀ t ∈ T, ∀ η : Submodule ℝ Plane,
                Module.finrank ℝ η = 1 →
                  (Tiling.RationalSlopes.ProperEdgeContactAlong K η s t ↔
                    Tiling.RationalSlopes.ProperEdgeContactAlong Kφ η
                      (deformPoint φ s) (deformPoint φ t)) := by
  classical
  intro K T hK hT hdense _
  obtain ⟨P, hP, _, _, _, F₁, ε₁, hε₁, hpolygon⟩ := rationalPolygon_construction K hK
  obtain ⟨B, hB, hboundK, F₂, ε₂, hε₂, hbound⟩ := code_uniformBound K P hP
  let R := 4 * B
  have hR : 0 < R := by dsimp [R]; positivity
  let D := (hT.2 R hR).toFinset
  obtain ⟨F₃, ε₃, hε₃, hrelative⟩ :=
    approximation_globalRelativeError T hT hdense (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨F₄, ε₄, hε₄, hpairs⟩ := finitePair_supportGerms K P hP D
  let F := F₁ ∪ F₂ ∪ F₃ ∪ F₄
  let ε := min ε₁ (min ε₂ (min ε₃ ε₄))
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨P, hP, F, ε, hε, ?_⟩
  intro φ hφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ :=
    finiteApproximation_strengthen F₁ F ε₁ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (min_le_left _ _) hφ
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ :=
    finiteApproximation_strengthen F₂ F ε₂ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (min_le_left _ _)) hφ
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ :=
    finiteApproximation_strengthen F₃ F ε₃ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))) hφ
  have hφ₄ : IsFiniteApproximation F₄ ε₄ φ :=
    finiteApproximation_strengthen F₄ F ε₄ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))) hφ
  obtain ⟨Kφ, hKφ, _⟩ := hpolygon φ hφ₁
  have htarget := hbound φ hφ₂ Kφ hKφ
  have hKnorm : ∀ z ∈ K.support, ‖z‖ ≤ B := by
    simpa only [Set.subset_def, Metric.mem_closedBall, dist_zero_right] using hboundK
  have hKφnorm : ∀ z ∈ Kφ.support, ‖z‖ ≤ B := by
    simpa only [Set.subset_def, Metric.mem_closedBall, dist_zero_right] using htarget
  have hD : ∀ d ∈ T - T, ‖d‖ ≤ R → d ∈ D := by
    intro d hd hnorm
    exact (hT.2 R hR).mem_toFinset.mpr
      ⟨hd, by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm⟩
  refine ⟨Kφ, hKφ, ?_⟩
  intro s hs t ht η _
  have hdiff : t - s ∈ T - T := Set.mem_sub.mpr ⟨t, ht, s, hs, rfl⟩
  have htransfer (hd : t - s ∈ D) :
      Tiling.RationalSlopes.ProperEdgeContactAlong K η s t ↔
        Tiling.RationalSlopes.ProperEdgeContactAlong Kφ η (deformPoint φ s) (deformPoint φ t) := by
    obtain ⟨H, hg⟩ := hpairs φ hφ₄ Kφ hKφ (t - s) hd
    exact properContact_of_pairGerms K Kφ φ s t H hg η
  constructor
  · intro hcontact
    have hdist := contact_distance_bound K B hKnorm s t η hcontact
    have hd : t - s ∈ D := by
      apply hD _ hdiff
      rw [← dist_eq_norm, dist_comm]
      dsimp [R]
      linarith
    exact (htransfer hd).mp hcontact
  · intro hcontact
    have hdist := contact_distance_bound Kφ B hKφnorm
      (deformPoint φ s) (deformPoint φ t) η hcontact
    have hlower := coarse_lower_of_relativeError φ (t - s)
      (by simpa only [dist_eq_norm] using hrelative φ hφ₃ t ht s hs)
    have hsub : deformPoint φ (t - s) = deformPoint φ t - deformPoint φ s :=
      (deformPointLinear φ).map_sub t s
    have hd : t - s ∈ D := by
      apply hD _ hdiff
      rw [hsub] at hlower
      have hnormimage : ‖deformPoint φ t - deformPoint φ s‖ ≤ 2 * B := by
        simpa only [dist_eq_norm, norm_sub_rev] using hdist
      dsimp [R]
      linarith
    exact (htransfer hd).mpr hcontact

private theorem column_denseSegmentChain
    (Y : Set Plane) (rho L R : ℝ) (hrho : 0 < rho) (hL : 0 < L)
    (hLR : L + 2 * rho < R)
    (a b : ↥Y)
    (hdense : ∀ s : ℝ, ∃ y ∈ Y, dist ((a : Plane) + s • ((b : Plane) - a)) y < rho)
    (hLab : L < dist (a : Plane) b) :
    ∃ N : ℕ, 0 < N ∧ ∃ point : Fin (N + 1) → ↥Y,
      point 0 = a ∧ point (Fin.last N) = b ∧
      (∀ i : Fin N, dist (point i.castSucc : Plane) (point i.succ) < R) ∧
      (N : ℝ) ≤ dist (a : Plane) b / L + 1 := by
  let D := dist (a : Plane) b
  let N := Nat.ceil (D / L)
  have hDL : 1 < D / L := by
    apply (lt_div_iff₀ hL).2
    simpa [D] using hLab
  have hNpos : 0 < N := Nat.ceil_pos.mpr (lt_trans zero_lt_one hDL)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hstepLe : D / (N : ℝ) ≤ L := by
    have hceil : D / L ≤ (N : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hNreal]
    have := (div_le_iff₀ hL).mp hceil
    nlinarith
  have hNle : (N : ℝ) ≤ D / L + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (div_nonneg (by simp [D]) hL.le))
  let c : Fin (N + 1) → Plane := fun i ↦
    (a : Plane) + ((i : ℝ) / (N : ℝ)) •
      ((b : Plane) - (a : Plane))
  choose q hqY hqdist using fun i : Fin (N + 1) ↦ hdense ((i : ℝ) / (N : ℝ))
  let p : Fin (N + 1) → Plane := fun i ↦
    if i = 0 then a else if i = Fin.last N then b else q i
  have hpY (i : Fin (N + 1)) : p i ∈ Y := by
    simp only [p]
    split
    · exact a.2
    · split
      · exact b.2
      · exact hqY i
  have hcZero : c 0 = a := by simp [c]
  have hcLast : c (Fin.last N) = b := by
    change (a : Plane) + ((N : ℝ) / (N : ℝ)) •
      ((b : Plane) - (a : Plane)) = b
    rw [div_self (ne_of_gt hNreal), one_smul]
    abel
  have hpClose (i : Fin (N + 1)) : dist (p i) (c i) < rho := by
    by_cases hi0 : i = 0
    · subst i
      rw [hcZero]
      simp [p, hrho]
    · by_cases hilast : i = Fin.last N
      · subst i
        rw [hcLast]
        have hlast0 : Fin.last N ≠ (0 : Fin (N + 1)) := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_zero] at this
          omega
        simp [p, hlast0, hrho]
      · simpa [p, c, hi0, hilast, dist_comm] using hqdist i
  have hcStep (i : Fin N) :
      dist (c i.succ) (c i.castSucc) = D / (N : ℝ) := by
    rw [dist_eq_norm]
    change ‖((a : Plane) + (((i.val + 1 : ℕ) : ℝ) / (N : ℝ)) •
        ((b : Plane) - (a : Plane))) -
      ((a : Plane) + ((i.val : ℝ) / (N : ℝ)) •
        ((b : Plane) - (a : Plane)))‖ = D / (N : ℝ)
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    have hcoef : (((i.val + 1 : ℕ) : ℝ) / (N : ℝ)) -
        (i.val : ℝ) / (N : ℝ) = (N : ℝ)⁻¹ := by
      push_cast
      field_simp
      ring
    rw [hcoef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNreal),
      show ‖(b : Plane) - (a : Plane)‖ = D by
        rw [norm_sub_rev]
        simp [D, dist_eq_norm], div_eq_mul_inv]
    ring
  have hpStep (i : Fin N) :
      dist (p i.castSucc) (p i.succ) < R := by
    calc
      dist (p i.castSucc) (p i.succ) ≤
          dist (p i.castSucc) (c i.castSucc) +
            dist (c i.castSucc) (c i.succ) + dist (c i.succ) (p i.succ) :=
        dist_triangle4 _ _ _ _
      _ < rho + (D / (N : ℝ)) + rho := by
        rw [dist_comm (c i.castSucc) (c i.succ), hcStep]
        have hlast := hpClose i.succ
        rw [dist_comm] at hlast
        linarith [hpClose i.castSucc, hlast]
      _ ≤ rho + L + rho := by linarith
      _ < R := by linarith
  let point : Fin (N + 1) → ↥Y := fun i ↦ ⟨p i, hpY i⟩
  refine ⟨N, hNpos, point, ?_, ?_, ?_, hNle⟩
  · apply Subtype.ext
    simp [point, p]
  · apply Subtype.ext
    have hlast0 : Fin.last N ≠ (0 : Fin (N + 1)) := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_zero] at this
      omega
    simp [point, p, hlast0]
  · exact hpStep

private theorem lineSupported_reflects_shortSteps
    (T S : Set Plane) (δ : Submodule ℝ Plane) (φ : ℝ →ₗ[ℚ] ℚ) (ρ R : ℝ)
    (hρ : 0 < ρ) (hR : 3 * ρ < R) (hST : S ⊆ T) (hS : S.Nonempty)
    (hinj : Set.InjOn (deformPoint φ) T)
    (hline : Tiling.Polygonal.IsLineSupported (deformPoint φ '' S) δ)
    (hdense : ∀ x ∈ deformPoint φ '' S, ∀ z : Plane, z - x ∈ δ →
      ∃ y ∈ deformPoint φ '' S, dist z y < ρ)
    (hstep : ∀ s ∈ S, ∀ t ∈ S, dist (deformPoint φ s) (deformPoint φ t) < R → s - t ∈ δ) :
    Tiling.Polygonal.IsLineSupported S δ := by
  classical
  obtain ⟨s₀, hs₀⟩ := hS
  refine ⟨s₀, ?_⟩
  intro s hs
  by_cases hshort : dist (deformPoint φ s) (deformPoint φ s₀) ≤ ρ
  · apply hstep s hs s₀ hs₀
    linarith
  have hlong : ρ < dist (deformPoint φ s₀) (deformPoint φ s) := by
    simpa only [dist_comm] using lt_of_not_ge hshort
  have hdiff : deformPoint φ s - deformPoint φ s₀ ∈ δ := by
    obtain ⟨a, ha⟩ := hline
    have h₀ := ha (deformPoint φ s₀) ⟨s₀, hs₀, rfl⟩
    have h₁ := ha (deformPoint φ s) ⟨s, hs, rfl⟩
    have heq : deformPoint φ s - deformPoint φ s₀ =
        (deformPoint φ s - a) - (deformPoint φ s₀ - a) := by abel
    rw [heq]
    exact δ.sub_mem h₁ h₀
  have hsegmentDense : ∀ r : ℝ, ∃ y ∈ deformPoint φ '' S,
      dist (deformPoint φ s₀ + r • (deformPoint φ s - deformPoint φ s₀)) y < ρ := by
    intro r
    apply hdense (deformPoint φ s₀) ⟨s₀, hs₀, rfl⟩
    simpa only [add_sub_cancel_left] using δ.smul_mem r hdiff
  obtain ⟨N, _, p, hp₀, hpN, hpstep, _⟩ := column_denseSegmentChain
    (deformPoint φ '' S) ρ ρ R hρ hρ (by linarith)
    ⟨deformPoint φ s₀, ⟨s₀, hs₀, rfl⟩⟩ ⟨deformPoint φ s, ⟨s, hs, rfl⟩⟩
    hsegmentDense hlong
  choose q hqS hqmap using fun i : Fin (N + 1) => (p i).2
  have hq₀ : q 0 = s₀ := by
    apply hinj (hST (hqS 0)) (hST hs₀)
    rw [hqmap]
    exact congrArg Subtype.val hp₀
  have hqN : q (Fin.last N) = s := by
    apply hinj (hST (hqS (Fin.last N))) (hST hs)
    rw [hqmap]
    exact congrArg Subtype.val hpN
  have hqδ : ∀ i : Fin (N + 1), q i - s₀ ∈ δ := by
    intro i
    refine Fin.induction ?_ ?_ i
    · rw [hq₀, sub_self]
      exact δ.zero_mem
    · intro j hj
      have hlocal : q j.succ - q j.castSucc ∈ δ := by
        apply hstep _ (hqS j.succ) _ (hqS j.castSucc)
        rw [hqmap, hqmap, dist_comm]
        exact hpstep j
      have heq : q j.succ - s₀ = (q j.succ - q j.castSucc) + (q j.castSucc - s₀) := by abel
      rw [heq]
      exact δ.add_mem hlocal hj
  simpa only [hqN] using hqδ (Fin.last N)

private theorem rationalLineSupported_image
    (S : Set Plane) (δ : Submodule ℝ Plane) (φ : ℝ →ₗ[ℚ] ℚ)
    (hδ : Module.finrank ℝ δ = 1) (hrat : Tiling.RationalSlopes.HasRationalDirection δ)
    (hline : Tiling.Polygonal.IsLineSupported S δ) :
    Tiling.Polygonal.IsLineSupported (deformPoint φ '' S) δ := by
  obtain ⟨n, hn⟩ := rationalDirection_hasNormal δ hδ hrat
  obtain ⟨a, ha⟩ := hline
  refine ⟨deformPoint φ a, ?_⟩
  rintro z ⟨s, hs, rfl⟩
  rw [← hn]
  apply rationalDirection_preservesCoset φ n s a
  rw [hn]
  exact ha s hs

private theorem column_forward_of_properVertices
    (K Kφ : PolygonalRegion) (S : Set Plane) (δ : Submodule ℝ Plane) (φ : ℝ →ₗ[ℚ] ℚ)
    (hδ : Module.finrank ℝ δ = 1) (hrat : Tiling.RationalSlopes.HasRationalDirection δ)
    (hpφ : Tiling.IsPacking Kφ.prototileFamily (Kφ.placements (deformPoint φ '' S)))
    (hproper : Tiling.Polygonal.properVertices
      (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) =
        deformPoint φ '' Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport K S))
    (hcol : Tiling.Polygonal.IsCenterColumn K δ S) :
    Tiling.Polygonal.IsCenterColumn Kφ δ (deformPoint φ '' S) := by
  have hnone := (Tiling.Polygonal.lineCarrier_noProperVertices_iff_column
    hδ hcol.2.1 hcol.1 hcol.2.2.1).mpr hcol
  apply (Tiling.Polygonal.lineCarrier_noProperVertices_iff_column
    hδ (hcol.2.1.image _) hpφ (rationalLineSupported_image S δ φ hδ hrat hcol.2.2.1)).mp
  rw [hproper, hnone, Set.image_empty]

private theorem column_lineRelativeDense
    (K : PolygonalRegion) (S : Set Plane) (δ : Submodule ℝ Plane) (B : ℝ)
    (hbound : ∀ z ∈ K.support, ‖z‖ ≤ B)
    (hcol : Tiling.Polygonal.IsCenterColumn K δ S) :
    ∀ s₀ ∈ S, ∀ z : Plane, z - s₀ ∈ δ →
      ∃ s ∈ S, dist z s < 2 * B + 1 := by
  intro s₀ hs₀ z hz
  obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hreg := regularSupport_eq_interior_supportUnion K S hcol.1
  have hsubset : s₀ +ᵥ K.support ⊆ supportUnion K S := by
    intro x hx
    refine ⟨s₀, hs₀, ?_⟩
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hx
  have hstart : s₀ + k ∈ Tiling.Polygonal.regularSupport K S := by
    rw [hreg]
    apply interior_mono hsubset
    rw [interior_vadd]
    exact Set.mem_vadd_set.mpr ⟨k, hk, rfl⟩
  have hcover : z + k ∈ Tiling.Polygonal.regularSupport K S := by
    rw [← hcol.2.2.2 (z - s₀) hz]
    apply Set.mem_vadd_set.mpr
    refine ⟨s₀ + k, hstart, ?_⟩
    change z - s₀ + (s₀ + k) = z + k
    abel
  rw [hreg] at hcover
  obtain ⟨s, hs, hks⟩ := interior_subset hcover
  refine ⟨s, hs, ?_⟩
  have heq : z - s = (z + k - s) - k := by abel
  rw [dist_eq_norm, heq]
  have hkB := hbound k (interior_subset hk)
  have hksB := hbound (z + k - s) hks
  linarith [norm_sub_le (z + k - s) k]

private theorem boundaryDirection_of_column
    (K : PolygonalRegion) (S : Set Plane) (δ : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) (hcol : Tiling.Polygonal.IsCenterColumn K δ S) :
    Tiling.Polygonal.HasBoundaryDirection K δ := by
  by_contra hboundary
  obtain ⟨A, _, hnear⟩ := Tiling.Polygonal.lineCarrier_nonboundary_nearProperVertex K
  obtain ⟨s, hs⟩ := hcol.2.1
  obtain ⟨v, hv, _⟩ := hnear δ hδ hboundary S hcol.1 hcol.2.2.1 s hs
  have hnone := (Tiling.Polygonal.lineCarrier_noProperVertices_iff_column
    hδ hcol.2.1 hcol.1 hcol.2.2.1).mpr hcol
  rw [hnone] at hv
  exact hv

private theorem boundaryDirection_normals (K : PolygonalRegion)
    (hK : Tiling.RationalSlopes.HasRationalSlopes K) :
    ∃ normals : Finset RationalNormal,
      ∀ δ : Submodule ℝ Plane, Tiling.Polygonal.HasBoundaryDirection K δ →
        ∃ n ∈ normals, normalDirection n = δ := by
  classical
  let Δ := {δ : Submodule ℝ Plane | Tiling.Polygonal.HasBoundaryDirection K δ}
  have hΔ : Δ.Finite := Tiling.Polygonal.boundaryDirections_finite K
  let := hΔ.fintype
  have hex (δ : Δ) : ∃ n : RationalNormal, normalDirection n = (δ : Submodule ℝ Plane) := by
    have hdim : Module.finrank ℝ (δ : Submodule ℝ Plane) = 1 := by
      obtain ⟨a, b, hab, _, heq⟩ := δ.2
      rw [heq]
      exact finrank_span_singleton (sub_ne_zero.mpr hab.symm)
    exact rationalDirection_hasNormal δ hdim
      (Tiling.Polygonal.hasRationalDirection_of_hasBoundaryDirection hK δ.2)
  choose n hn using hex
  refine ⟨Finset.univ.image n, ?_⟩
  intro δ hδ
  refine ⟨n ⟨δ, hδ⟩, Finset.mem_image.mpr ⟨⟨δ, hδ⟩, Finset.mem_univ _, rfl⟩, hn _⟩

private theorem polygonalRegion_eq_of_support {K L : PolygonalRegion}
    (h : K.support = L.support) : K = L := by
  cases K
  cases L
  cases h
  rfl

theorem flcDeformation_preservesColumns :
  ∀ (K : PolygonalRegion) (T : Set Plane), Tiling.RationalSlopes.HasRationalSlopes K →
    Tiling.Polygonal.HasFLC T → RelativeDense T →
    Tiling.Polygonal.TilesOn K T (Tiling.Polygonal.regularSupport K T) →
      ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
        ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
          ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
            ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ ∧
              ∀ S ⊆ T, ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
                Tiling.RationalSlopes.HasRationalDirection δ →
                  (Tiling.Polygonal.IsCenterColumn K δ S ↔
                    Tiling.Polygonal.IsCenterColumn Kφ δ (deformPoint φ '' S)) := by
  classical
  intro K T hK hT hdense htile
  obtain ⟨P₁, hP₁, W, _, hzero, F₁, ε₁, hε₁, hdeform⟩ :=
    flcRationalDeformation K T hK hT hdense htile
  obtain ⟨P₂, hP₂, _, _, _, B, L, hB, _, F₂, ε₂, hε₂, hboundary⟩ :=
    rationalPolygon_uniformBoundaryControl K hK
  obtain ⟨F₃, ε₃, hε₃, hcode⟩ := polyhedralDeformation_independentOfCode K P₁ P₂ hP₁ hP₂
  obtain ⟨normals, hnormals⟩ := boundaryDirection_normals K hK
  let ρ := 2 * B + 1
  let R := 4 * ρ
  let M := 2 * R
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hM : 0 < M := by dsimp [M, R]; positivity
  obtain ⟨F₄, ε₄, hε₄, hmetric⟩ := approximation_boundedMetricAndRelationControl
    T hT hdense M 1 normals hM (by norm_num)
  let F := F₁ ∪ F₂ ∪ F₃ ∪ F₄
  let ε := min ε₁ (min ε₂ (min ε₃ ε₄))
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨P₁, hP₁, F, ε, hε, ?_⟩
  intro φ hφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ :=
    finiteApproximation_strengthen F₁ F ε₁ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (min_le_left _ _) hφ
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ :=
    finiteApproximation_strengthen F₂ F ε₂ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (min_le_left _ _)) hφ
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ :=
    finiteApproximation_strengthen F₃ F ε₃ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))) hφ
  have hφ₄ : IsFiniteApproximation F₄ ε₄ φ :=
    finiteApproximation_strengthen F₄ F ε₄ ε φ
      (by dsimp [F]; intro x hx; simp only [Finset.mem_union]; tauto)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))) hφ
  obtain ⟨Kφ, hKφ, _, _, _, _, htileφ, _, _, hproper⟩ := hdeform φ hφ₁
  obtain ⟨Kψ, hKψ, hbound, _, hdirections⟩ := hboundary φ hφ₂
  have hsame : Kφ = Kψ := polygonalRegion_eq_of_support
    (hKφ.trans ((hcode φ hφ₃).trans hKψ.symm))
  subst Kψ
  obtain ⟨hinj, _, _, hreflect⟩ := hmetric φ hφ₄
  refine ⟨Kφ, hKφ, ?_⟩
  intro S hST δ hδ hrat
  have hpφ := packing_subfamily htileφ.2.1 (Set.image_mono hST)
  constructor
  · exact column_forward_of_properVertices K Kφ S δ φ hδ hrat hpφ (hproper S hST)
  · intro hcol
    have hS : S.Nonempty := (Set.image_nonempty.mp hcol.2.1)
    have hsourceDirection := (hdirections δ).mp (boundaryDirection_of_column Kφ _ δ hδ hcol)
    obtain ⟨n, hn, hnδ⟩ := hnormals δ hsourceDirection
    have hKnorm : ∀ z ∈ Kφ.support, ‖z‖ ≤ B := by
      simpa only [Set.subset_def, Metric.mem_closedBall, dist_zero_right] using hbound
    have hline : Tiling.Polygonal.IsLineSupported S δ := by
      apply lineSupported_reflects_shortSteps T S δ φ ρ R hρ
        (by dsimp [R]; linarith) hST hS hinj hcol.2.2.1
        (column_lineRelativeDense Kφ _ δ B hKnorm hcol)
      intro s hs t ht hdist
      have hshort : dist (deformPoint φ s) (deformPoint φ t) < M / 2 := by
        dsimp [M]
        linarith
      have himage : deformPoint φ s - deformPoint φ t ∈ δ := by
        obtain ⟨a, ha⟩ := hcol.2.2.1
        have hsδ := ha (deformPoint φ s) ⟨s, hs, rfl⟩
        have htδ := ha (deformPoint φ t) ⟨t, ht, rfl⟩
        have heq : deformPoint φ s - deformPoint φ t =
            (deformPoint φ s - a) - (deformPoint φ t - a) := by abel
        rw [heq]
        exact δ.sub_mem hsδ htδ
      have himageN : normalEval n (deformPoint φ s - deformPoint φ t) = 0 := by
        rw [← hnδ] at himage
        simpa [normalDirection, normalEval, LinearMap.mem_ker] using himage
      have hsourceN := (hreflect s (hST hs) t (hST ht) hshort n hn).mp himageN
      rw [← hnδ]
      simpa [normalDirection, normalEval, LinearMap.mem_ker] using hsourceN
    have hp := packing_subfamily htile.2.1 hST
    apply (Tiling.Polygonal.lineCarrier_noProperVertices_iff_column hδ hS hp hline).mp
    have hnone := (Tiling.Polygonal.lineCarrier_noProperVertices_iff_column
      hδ hcol.2.1 hcol.1 hcol.2.2.1).mpr hcol
    have heq := hproper S hST
    rw [hnone] at heq
    exact Set.image_eq_empty.mp heq.symm

end Tiling.RationalSlopes.Approximation

-- All owned bodies are complete; inherited predecessor sorryAx keeps this provisional.
