import Tiling.AxisParallel.Foundations.IntrinsicVertices

/-!
# Intrinsic-ended boundary edges

The finite pairs of distinct intrinsic vertices joined by an axis-parallel
boundary segment cover the entire frontier, including junction vertices.
-/

set_option autoImplicit false

open Set Tiling

noncomputable section

namespace Tiling.AxisParallel.Region

private theorem segment_subset_frontier_of_openSegment
    {K : Region} {a b : Plane}
    (h : openSegment ℝ a b ⊆ frontier K.support) :
    segment ℝ a b ⊆ frontier K.support := by
  rw [← closure_openSegment a b]
  exact closure_minimal h isClosed_frontier

def intrinsicBoundaryEdges (K : Region) :
    Set (Plane × Plane) :=
  {e | e.1 ∈ K.vertices ∧ e.2 ∈ K.vertices ∧ e.1 ≠ e.2 ∧
    (e.1.re = e.2.re ∨ e.1.im = e.2.im) ∧
    segment ℝ e.1 e.2 ⊆ frontier K.support}

theorem intrinsicBoundaryEdges_finite (K : Region) :
    (intrinsicBoundaryEdges K).Finite := by
  apply Set.Finite.subset
    (K.isPolygonal.vertexSet_finite.prod K.isPolygonal.vertexSet_finite)
  intro e he
  exact ⟨he.1, he.2.1⟩

theorem frontier_eq_intrinsicBoundaryEdges (K : Region) :
    frontier K.support = ⋃ e ∈ intrinsicBoundaryEdges K, segment ℝ e.1 e.2 := by
  classical
  ext x
  constructor
  · intro hx
    by_cases hv : x ∈ K.vertices
    · obtain ⟨w, hne, halign, hopen⟩ :=
        Tiling.AxisParallel.IntrinsicVertices.intrinsicVertex_incident_axisEdge
          K .horizontal ⟨x, hv⟩
      have hopen' : openSegment ℝ x w.1 ⊆ frontier K.support :=
        fun z hz => (hopen hz).1
      have hseg := segment_subset_frontier_of_openSegment hopen'
      have hmem : (x, w.1) ∈ intrinsicBoundaryEdges K := by
        refine ⟨hv, w.2, (fun h => hne h.symm), ?_, hseg⟩
        exact Or.inr (by simpa [Tiling.AxisParallel.Axis.transverseCoord] using halign.symm)
      exact mem_iUnion.mpr ⟨(x, w.1), mem_iUnion.mpr ⟨hmem, left_mem_segment ℝ _ _⟩⟩
    · obtain ⟨axis, v, w, hne, halign, hxseg, hopen⟩ :=
        Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge
          K x hx hv
      have hopen' : openSegment ℝ v.1 w.1 ⊆ frontier K.support :=
        fun z hz => (hopen hz).1
      have hseg := segment_subset_frontier_of_openSegment hopen'
      have hmem : (v.1, w.1) ∈ intrinsicBoundaryEdges K := by
        refine ⟨v.2, w.2, hne, ?_, hseg⟩
        cases axis with
        | horizontal => exact Or.inr halign
        | vertical => exact Or.inl halign
      exact mem_iUnion.mpr ⟨(v.1, w.1), mem_iUnion.mpr ⟨hmem,
        openSegment_subset_segment ℝ _ _ hxseg⟩⟩
  · intro hx
    obtain ⟨e, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨he, hx⟩ := Set.mem_iUnion.mp hx
    exact he.2.2.2.2 hx

end Tiling.AxisParallel.Region
