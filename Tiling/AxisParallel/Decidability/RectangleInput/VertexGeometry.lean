import Tiling.AxisParallel.Decidability.RectangleInput.Vertices
import Tiling.AxisParallel.Decidability.RectangleInput.Geometry
import Tiling.AxisParallel.SetFormulation.VertexQuadrants

set_option autoImplicit false

open Set

noncomputable section

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput

def pointValue (V : List Plane) (p : PointLabel) : Plane :=
  ⟨(V.getD p.1 0).re, (V.getD p.2 0).im⟩

@[simp] theorem coordinate_pointValue (V : List Plane) (p : PointLabel) (vertical : Bool) :
    coordinate (axis vertical) (pointValue V p) =
      coordinate (axis vertical) (V.getD (bif vertical then p.2 else p.1) 0) := by
  cases vertical <;> rfl

theorem sideCovered_correct {V : List Plane} {history : List Bool}
    (h : TableCorrect V history) {a b i : ℕ} (ha : a < V.length)
    (hb : b < V.length) (hi : i < V.length) (vertical negative : Bool) :
    sideCovered V.length history vertical negative a b i = true ↔
      (if negative then
        coordinate (axis vertical) (V.getD a 0) < coordinate (axis vertical) (V.getD i 0) ∧
          coordinate (axis vertical) (V.getD i 0) ≤ coordinate (axis vertical) (V.getD b 0)
      else
        coordinate (axis vertical) (V.getD a 0) ≤ coordinate (axis vertical) (V.getD i 0) ∧
          coordinate (axis vertical) (V.getD i 0) < coordinate (axis vertical) (V.getD b 0)) := by
  cases negative <;>
    simp only [sideCovered, Bool.cond_false, Bool.cond_true, Bool.and_eq_true,
      Bool.false_eq_true, ↓reduceIte] <;>
    rw [h vertical _ _ (by assumption) (by assumption),
      strictLevel_correct h (by assumption) (by assumption) vertical]

theorem quadrantRectangle_correct {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history) {p : PointLabel} {k : ℕ}
    (hp : p.1 < 2 * R.length ∧ p.2 < 2 * R.length) (hk : k < R.length)
    (west south : Bool) :
    quadrantRectangle (R.length, history) p west south k = true ↔
      rectangleReachesQuadrant (R.getD k (0, 0)) (pointValue (cornerList R) p) west south := by
  have ha : 2 * k < (cornerList R).length := by rw [cornerList_length]; omega
  have hb : 2 * k + 1 < (cornerList R).length := by rw [cornerList_length]; omega
  have hi : p.1 < (cornerList R).length := by simpa only [cornerList_length] using hp.1
  have hj : p.2 < (cornerList R).length := by simpa only [cornerList_length] using hp.2
  simp only [quadrantRectangle, ← cornerList_length, Bool.and_eq_true]
  rw [sideCovered_correct h ha hb hi false west, sideCovered_correct h ha hb hj true south,
    cornerList_getD_left R hk, cornerList_getD_right R hk]
  cases west <;> cases south <;> rfl

theorem quadrantOccupiedBool_correct {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history) {p : PointLabel}
    (hp : p.1 < 2 * R.length ∧ p.2 < 2 * R.length) (west south : Bool) :
    quadrantOccupiedBool (R.length, history) p west south = true ↔
      quadrantOccupied R (pointValue (cornerList R) p) west south := by
  rw [quadrantOccupiedBool, anyBelow_eq_true]
  constructor
  · rintro ⟨k, hk, hq⟩
    refine ⟨R.getD k (0, 0), ?_, (quadrantRectangle_correct h hp hk west south).1 hq⟩
    rw [List.getD_eq_getElem R (0, 0) hk]
    exact List.getElem_mem hk
  · rintro ⟨r, hr, hq⟩
    obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hr
    refine ⟨k, hk, (quadrantRectangle_correct h hp hk west south).2 ?_⟩
    rwa [List.getD_eq_getElem R (0, 0) hk, heq]

private theorem xor_true_iff (a b : Bool) :
    Bool.xor a b = true ↔ quadrantDifferent (a = true) (b = true) := by
  cases a <;> cases b <;> simp [quadrantDifferent]

theorem vertexFlag_correct {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) {p : PointLabel}
    (hp : p.1 < 2 * R.length ∧ p.2 < 2 * R.length) :
    vertexFlag (R.length, history) p = true ↔ pointValue (cornerList R) p ∈ vertices Ω := by
  rw [mem_vertices_iff_quadrantChanges hR]
  simp only [vertexFlag, Bool.and_eq_true, Bool.or_eq_true, xor_true_iff,
    quadrantOccupiedBool_correct h hp, hasBothAxisQuadrantChanges]

theorem pointValue_injective_on_vertexLabels {R : List (Plane × Plane)}
    {history : List Bool} (h : TableCorrect (cornerList R) history) :
    Set.InjOn (pointValue (cornerList R)) {p | p ∈ vertexLabels (R.length, history)} := by
  intro p hp q hq heq
  have hpm := mem_vertexLabels.mp hp
  have hqm := mem_vertexLabels.mp hq
  have hpc := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hpm.2.2).1)
  have hqc := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hqm.2.2).1)
  rw [← cornerList_length] at hpm hqm hpc hqc
  apply Prod.ext
  · have hre := congrArg Complex.re heq
    exact canonical_injective h hpm.1 hqm.1 hpc.1 hqc.1 hre
  · have him := congrArg Complex.im heq
    exact canonical_injective h hpm.2.1 hqm.2.1 hpc.2 hqc.2 him

theorem vertexLabels_sound {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) {p : PointLabel}
    (hp : p ∈ vertexLabels (R.length, history)) : pointValue (cornerList R) p ∈ vertices Ω := by
  have hpm := mem_vertexLabels.mp hp
  exact (vertexFlag_correct hR h ⟨hpm.1, hpm.2.1⟩).1
    ((Bool.and_eq_true_iff.mp hpm.2.2).2)

theorem vertexLabels_complete_of_levels {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) {v : Plane} (hv : v ∈ vertices Ω)
    (hx : v.re ∈ levels (cornerList R) false)
    (hy : v.im ∈ levels (cornerList R) true) :
    ∃ p ∈ vertexLabels (R.length, history), pointValue (cornerList R) p = v := by
  obtain ⟨i, hi, hix, hci⟩ := canonical_representative h hx
  obtain ⟨j, hj, hjy, hcj⟩ := canonical_representative h hy
  let p : PointLabel := (i, j)
  have hvalue : pointValue (cornerList R) p = v := Complex.ext hix hjy
  have hbounds : p.1 < 2 * R.length ∧ p.2 < 2 * R.length := by
    simpa only [cornerList_length] using And.intro hi hj
  refine ⟨p, mem_vertexLabels.mpr ⟨hbounds.1, hbounds.2, ?_⟩, hvalue⟩
  simp only [vertexAccepted, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, (vertexFlag_correct hR h hbounds).2 (hvalue.symm ▸ hv)⟩
  · simpa only [cornerList_length] using hci
  · simpa only [cornerList_length] using hcj

theorem rectangleRealLevels_eq_levels (R : List (Plane × Plane)) :
    rectangleRealLevels R = levels (cornerList R) false := by
  classical
  ext x
  simp only [rectangleRealLevels, Finset.mem_union, Finset.mem_image,
    List.mem_toFinset, levels, cornerList, List.mem_flatMap, List.mem_cons,
    coordinate, axis, Bool.false_eq_true, ↓reduceIte]
  aesop

theorem vertex_im_coordinate_mem_levels {R : List (Plane × Plane)} {Ω : Set Plane}
    (hR : RectanglePresentation R Ω) {v : Plane} (hv : v ∈ vertices Ω) :
    v.im ∈ levels (cornerList R) true := by
  classical
  by_contra hnot
  have hneqLo (r : Plane × Plane) (hr : r ∈ R) : r.1.im ≠ v.im := by
    intro heq
    apply hnot
    rw [← heq]
    apply Finset.mem_image.mpr
    refine ⟨r.1, List.mem_toFinset.mpr ?_, rfl⟩
    exact List.mem_flatMap.mpr ⟨r, hr, by simp⟩
  have hneqHi (r : Plane × Plane) (hr : r ∈ R) : r.2.im ≠ v.im := by
    intro heq
    apply hnot
    rw [← heq]
    apply Finset.mem_image.mpr
    refine ⟨r.2, List.mem_toFinset.mpr ?_, rfl⟩
    exact List.mem_flatMap.mpr ⟨r, hr, by simp⟩
  have hsame (west : Bool) :
      quadrantOccupied R v west true = quadrantOccupied R v west false := by
    apply propext
    constructor
    · rintro ⟨r, hr, hreach⟩
      change (if west then r.1.re < v.re ∧ v.re ≤ r.2.re
        else r.1.re ≤ v.re ∧ v.re < r.2.re) ∧ (r.1.im < v.im ∧ v.im ≤ r.2.im) at hreach
      exact ⟨r, hr, hreach.1, hreach.2.1.le,
        lt_of_le_of_ne hreach.2.2 (hneqHi r hr).symm⟩
    · rintro ⟨r, hr, hreach⟩
      change (if west then r.1.re < v.re ∧ v.re ≤ r.2.re
        else r.1.re ≤ v.re ∧ v.re < r.2.re) ∧ (r.1.im ≤ v.im ∧ v.im < r.2.im) at hreach
      exact ⟨r, hr, hreach.1, lt_of_le_of_ne hreach.2.1 (hneqLo r hr), hreach.2.2.le⟩
  have hchanges := (mem_vertices_iff_quadrantChanges hR v).1 hv
  rcases hchanges.1 with hwest | heast
  · simp only [quadrantDifferent, hsame true, and_not_self, not_and_self, or_self] at hwest
  · simp only [quadrantDifferent, hsame false, and_not_self, not_and_self, or_self] at heast

/-- The primitive-recursive list enumerates exactly the intrinsic vertices, in
canonical coordinate-label order, without repeated points. -/
theorem vertexLabels_exact {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) (v : Plane) :
    (∃ p ∈ vertexLabels (R.length, history), pointValue (cornerList R) p = v) ↔
      v ∈ vertices Ω := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact vertexLabels_sound hR h hp
  · intro hv
    exact vertexLabels_complete_of_levels hR h hv
      (rectangleRealLevels_eq_levels R ▸ vertex_real_coordinate_mem_rectangleLevels hR hv)
      (vertex_im_coordinate_mem_levels hR hv)

theorem vertexLabels_nonempty {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) : 0 < (vertexLabels (R.length, history)).length := by
  let K := regionOfTile Ω (RectanglePresentation.isAxisParallelTile hR)
  obtain ⟨v, hv, _⟩ := Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair K
  have hv' : v ∈ vertices Ω := by
    rwa [vertices_eq_native Ω (RectanglePresentation.isAxisParallelTile hR)]
  obtain ⟨p, hp, _⟩ := (vertexLabels_exact hR h v).2 hv'
  exact List.length_pos_of_mem hp

end Tiling.AxisParallel.Decidability.RectangleInput
