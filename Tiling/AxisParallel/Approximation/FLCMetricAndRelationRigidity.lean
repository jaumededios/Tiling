import Tiling.AxisParallel.Approximation.FiniteLocalComplexityControl

open Set

namespace Tiling.AxisParallel.Approximation

noncomputable section

private def projectedVertexDifferenceScalar (C : ApproximationContext)
    (axis : Tiling.AxisParallel.Axis)
    (e : ↑C.region.vertices × ↑C.region.vertices) : C.coordinateSpace := by
  cases axis with
  | horizontal =>
      exact ⟨(e.2 : Tiling.Plane).re - (e.1 : Tiling.Plane).re,
        C.coordinateSpace.sub_mem
          (C.vertex_re_mem e.2 e.2.2) (C.vertex_re_mem e.1 e.1.2)⟩
  | vertical =>
      exact ⟨(e.2 : Tiling.Plane).im - (e.1 : Tiling.Plane).im,
        C.coordinateSpace.sub_mem
          (C.vertex_im_mem e.2 e.2.2) (C.vertex_im_mem e.1 e.1.2)⟩

private def projectedVertexPairLengthScalar (C : ApproximationContext)
    (axis : Tiling.AxisParallel.Axis)
    (e : ↑C.region.vertices × ↑C.region.vertices) : C.coordinateSpace := by
  let d := projectedVertexDifferenceScalar C axis e
  by_cases hd : 0 ≤ (d : ℝ)
  · exact ⟨|(d : ℝ)|, by
      rw [abs_of_nonneg hd]
      exact d.2⟩
  · exact ⟨|(d : ℝ)|, by
      rw [abs_of_neg (lt_of_not_ge hd)]
      exact C.coordinateSpace.neg_mem d.2⟩

private theorem coe_projectedVertexPairLengthScalar (C : ApproximationContext)
    (axis : Tiling.AxisParallel.Axis)
    (e : ↑C.region.vertices × ↑C.region.vertices) :
    (projectedVertexPairLengthScalar C axis e : ℝ) =
      projectedVertexPairLength C axis e := by
  simp only [projectedVertexPairLengthScalar, projectedVertexPairLength]
  split <;> cases axis <;> rfl

private theorem positive_of_same_sign {x y : ℝ}
    (h : Real.sign x = Real.sign y) (hy : 0 < y) : 0 < x := by
  rw [Real.sign_of_pos hy] at h
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx] at h
    norm_num at h
  · simp at h
  · exact hx

private theorem negative_of_same_sign {x y : ℝ}
    (h : Real.sign x = Real.sign y) (hy : y < 0) : x < 0 := by
  rw [Real.sign_of_neg hy] at h
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · exact hx
  · simp at h
  · rw [Real.sign_of_pos hx] at h
    norm_num at h

private theorem map_projectedVertexPairLengthScalar
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hgood : IsGoodApproximation C phi) (axis : Tiling.AxisParallel.Axis)
    (e : ↑C.region.vertices × ↑C.region.vertices) :
    mapScalar phi (projectedVertexPairLengthScalar C axis e) =
      mappedProjectedVertexPairLength phi axis e := by
  let d := projectedVertexDifferenceScalar C axis e
  let md := Tiling.AxisParallel.Axis.coord axis
    (mapPoint phi (C.vertexPoint e.2.1 e.2.2) -
      mapPoint phi (C.vertexPoint e.1.1 e.1.2))
  have hdval : (d : ℝ) = Tiling.AxisParallel.Axis.coord axis
      ((e.2 : Tiling.Plane) - (e.1 : Tiling.Plane)) := by cases axis <;> rfl
  have hmap : mapScalar phi d = md := by
    cases axis <;>
      simp only [d, projectedVertexDifferenceScalar, md, mapPoint, mapScalar,
        Tiling.AxisParallel.Axis.coord, Complex.sub_re, Complex.sub_im,
        Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, add_zero, zero_add]
    all_goals
      norm_cast
      rw [← map_sub]
      rfl
  have hsign : Real.sign md = Real.sign (d : ℝ) := by
    rw [hdval]
    exact hgood.preservesVertexCoordinateSign axis e.2 e.1 e.2.2 e.1.2
  change mapScalar phi (projectedVertexPairLengthScalar C axis e) = |md|
  by_cases hd : 0 ≤ (d : ℝ)
  · rw [show projectedVertexPairLengthScalar C axis e = d by
      apply Subtype.ext
      simp [projectedVertexPairLengthScalar, d, hd, abs_of_nonneg hd]]
    rw [hmap]
    rcases hd.eq_or_lt with hd0 | hdpos
    · have hmd0 : md = 0 := by
        apply Real.sign_eq_zero_iff.mp
        rw [hsign, ← hd0, Real.sign_zero]
      rw [hmd0, abs_zero]
    · rw [abs_of_pos (positive_of_same_sign hsign hdpos)]
  · have hdneg := lt_of_not_ge hd
    rw [show projectedVertexPairLengthScalar C axis e = -d by
      apply Subtype.ext
      simp [projectedVertexPairLengthScalar, d, hd, abs_of_neg hdneg]]
    simp only [mapScalar, map_neg, Rat.cast_neg]
    change -mapScalar phi d = |md|
    rw [hmap, abs_of_neg (negative_of_same_sign hsign hdneg)]

theorem deformation_injectiveOnCentres
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi) :
    Function.Injective
      (fun t : ↑C.centres ↦ mapPoint phi (C.centrePoint t.1 t.2)) := by
  intro s t hst
  let a : ↑C.translatedVertices := ⟨s.1, by
    exact ⟨0, C.zero_mem_vertices, s.1, s.2, zero_add s.1⟩⟩
  let b : ↑C.translatedVertices := ⟨t.1, by
    exact ⟨0, C.zero_mem_vertices, t.1, t.2, zero_add t.1⟩⟩
  have haPoint : C.translatedVertexPoint a = C.centrePoint s.1 s.2 := by
    apply Subtype.ext
    rfl
  have hbPoint : C.translatedVertexPoint b = C.centrePoint t.1 t.2 := by
    apply Subtype.ext
    rfl
  have hab : mapTranslatedVertex phi a = mapTranslatedVertex phi b := by
    rw [mapTranslatedVertex, mapTranslatedVertex, haPoint, hbPoint]
    exact hst
  have := deformation_injectiveOnTranslatedVertices P phi hphi hab
  apply Subtype.ext
  exact congrArg (fun x : ↑C.translatedVertices ↦ (x : Tiling.Plane)) this

theorem deformation_reflectsAxisCoset
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (axis : Tiling.AxisParallel.Axis)
    (v w : ↑C.translatedVertices)
    (hvw : dist (mapTranslatedVertex phi v)
      (mapTranslatedVertex phi w) < P.scale / 2) :
    Tiling.AxisParallel.Axis.transverseCoord axis
        ((v : Tiling.Plane) - (w : Tiling.Plane)) = 0 ↔
      Tiling.AxisParallel.Axis.transverseCoord axis
        (mapTranslatedVertex phi v - mapTranslatedVertex phi w) = 0 := by
  have hsource := deformation_coarselyProper P phi hphi v w hvw
  have hcontrol : dist (v : Tiling.Plane) w < P.controlRadius :=
    lt_trans hsource P.scale_lt_controlRadius
  cases axis with
  | horizontal =>
      exact (deformation_reflectsFiniteValues P phi hphi
        Tiling.AxisParallel.Axis.vertical v w v w hcontrol hcontrol).2.1.symm
  | vertical =>
      exact (deformation_reflectsFiniteValues P phi hphi
        Tiling.AxisParallel.Axis.horizontal v w v w hcontrol hcontrol).2.1.symm

theorem deformation_reflectsBoundedCoordinateDisplacement
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (axis : Tiling.AxisParallel.Axis)
    (v0 w0 v1 w1 : ↑C.translatedVertices)
    (h0 : dist (mapTranslatedVertex phi w0)
      (mapTranslatedVertex phi v0) < P.scale / 2)
    (h1 : dist (mapTranslatedVertex phi w1)
      (mapTranslatedVertex phi v1) < P.scale / 2)
    (hImage :
      Tiling.AxisParallel.Axis.coord axis
          (mapTranslatedVertex phi w0 - mapTranslatedVertex phi v0) =
        Tiling.AxisParallel.Axis.coord axis
          (mapTranslatedVertex phi w1 - mapTranslatedVertex phi v1)) :
    Tiling.AxisParallel.Axis.coord axis
        ((w0 : Tiling.Plane) - (v0 : Tiling.Plane)) =
      Tiling.AxisParallel.Axis.coord axis
        ((w1 : Tiling.Plane) - (v1 : Tiling.Plane)) := by
  have hs0 := deformation_coarselyProper P phi hphi w0 v0 h0
  have hs1 := deformation_coarselyProper P phi hphi w1 v1 h1
  exact (deformation_reflectsFiniteValues P phi hphi axis w0 v0 w1 v1
    (lt_trans hs0 P.scale_lt_controlRadius)
    (lt_trans hs1 P.scale_lt_controlRadius)).2.2 hImage

theorem deformation_reflectsShortProjectedEdgeSum
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (axis : Tiling.AxisParallel.Axis)
    (n m : ℕ)
    (hn : (n : ℝ) < P.scale) (hm : (m : ℝ) < P.scale)
    (e : Fin n → (↑C.region.vertices × ↑C.region.vertices))
    (f : Fin m → (↑C.region.vertices × ↑C.region.vertices))
    (he : ∀ j : Fin n,
      (e j).1 ≠ (e j).2 ∧
        openSegment ℝ ((e j).1 : Tiling.Plane)
            ((e j).2 : Tiling.Plane) ⊆ frontier C.region.openCarrier ∧
        ∀ u : ↑C.region.vertices,
          (u : Tiling.Plane) ∉
            openSegment ℝ ((e j).1 : Tiling.Plane)
              ((e j).2 : Tiling.Plane))
    (hf : ∀ j : Fin m,
      (f j).1 ≠ (f j).2 ∧
        openSegment ℝ ((f j).1 : Tiling.Plane)
            ((f j).2 : Tiling.Plane) ⊆ frontier C.region.openCarrier ∧
        ∀ u : ↑C.region.vertices,
          (u : Tiling.Plane) ∉
            openSegment ℝ ((f j).1 : Tiling.Plane)
              ((f j).2 : Tiling.Plane))
    (hImage :
      Finset.univ.sum
          (mappedProjectedVertexPairLength phi axis ∘ e) =
        Finset.univ.sum
          (mappedProjectedVertexPairLength phi axis ∘ f)) :
    Finset.univ.sum (projectedVertexPairLength C axis ∘ e) =
      Finset.univ.sum (projectedVertexPairLength C axis ∘ f) := by
  let se : C.coordinateSpace :=
    ∑ j : Fin n, projectedVertexPairLengthScalar C axis (e j)
  let sf : C.coordinateSpace :=
    ∑ j : Fin m, projectedVertexPairLengthScalar C axis (f j)
  let z : C.coordinateSpace := se - sf
  have hseVal : (se : ℝ) =
      Finset.univ.sum (projectedVertexPairLength C axis ∘ e) := by
    simp only [se, Submodule.coe_sum, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro j hj
    exact coe_projectedVertexPairLengthScalar C axis (e j)
  have hsfVal : (sf : ℝ) =
      Finset.univ.sum (projectedVertexPairLength C axis ∘ f) := by
    simp only [sf, Submodule.coe_sum, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro j hj
    exact coe_projectedVertexPairLengthScalar C axis (f j)
  have hzShort : z ∈ shortProjectedEdgeSumDifferences C P.scale := by
    refine ⟨axis, n, m, hn, hm, e, f, he, hf, ?_⟩
    change (se : ℝ) - (sf : ℝ) = _
    rw [hseVal, hsfVal]
  have hzEdge : z ∈ P.edgeSumAlphabet := by
    have hzSet : z ∈ (P.edgeSumAlphabet : Set C.coordinateSpace) := by
      rw [P.edgeSumAlphabet_exact]
      exact hzShort
    exact hzSet
  have hzControl : z ∈ P.scalarAlphabet ∪ P.edgeSumAlphabet :=
    Finset.mem_union_right _ hzEdge
  have hmapSe : mapScalar phi se =
      Finset.univ.sum (mappedProjectedVertexPairLength phi axis ∘ e) := by
    simp only [se, mapScalar, map_sum, Rat.cast_sum, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro j hj
    exact map_projectedVertexPairLengthScalar phi (P.forces_good phi hphi) axis (e j)
  have hmapSf : mapScalar phi sf =
      Finset.univ.sum (mappedProjectedVertexPairLength phi axis ∘ f) := by
    simp only [sf, mapScalar, map_sum, Rat.cast_sum, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro j hj
    exact map_projectedVertexPairLengthScalar phi (P.forces_good phi hphi) axis (f j)
  have hmapZero : mapScalar phi z = 0 := by
    simp only [z, mapScalar, map_sub, Rat.cast_sub]
    change mapScalar phi se - mapScalar phi sf = 0
    rw [hmapSe, hmapSf, sub_eq_zero]
    exact hImage
  have hzZero : (z : ℝ) = 0 :=
    (P.scalar_zero_iff phi hphi z hzControl).mp hmapZero
  change (se : ℝ) - (sf : ℝ) = 0 at hzZero
  rw [hseVal, hsfVal, sub_eq_zero] at hzZero
  exact hzZero

end

end Tiling.AxisParallel.Approximation
