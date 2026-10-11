import Tiling.AxisParallel.Core
import Tiling.Geometry.PolygonalTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel

/-- A positive similarity with an explicit affine anchor. -/
def positiveSimilarity (s : ℝ) (b z : Tiling.Plane) : Tiling.Plane :=
  s • z + b

def positiveSimilarityHomeomorph (s : ℝ) (b : Tiling.Plane) (hs : 0 < s) :
    Tiling.Plane ≃ₜ Tiling.Plane :=
  (Homeomorph.smulOfNeZero s (ne_of_gt hs)).trans (Homeomorph.addRight b)

@[simp] theorem positiveSimilarityHomeomorph_apply
    (s : ℝ) (b z : Tiling.Plane) (hs : 0 < s) :
    positiveSimilarityHomeomorph s b hs z = positiveSimilarity s b z := by
  rfl

theorem positiveSimilarity_injective
    {s : ℝ} {b : Tiling.Plane} (hs : 0 < s) :
    Function.Injective (positiveSimilarity s b) := by
  intro x y hxy
  exact (positiveSimilarityHomeomorph s b hs).injective hxy

theorem positiveSimilarity_surjective
    {s : ℝ} {b : Tiling.Plane} (hs : 0 < s) :
    Function.Surjective (positiveSimilarity s b) := by
  intro z
  exact ⟨(positiveSimilarityHomeomorph s b hs).symm z,
    (positiveSimilarityHomeomorph s b hs).apply_symm_apply z⟩

theorem positiveSimilarity_image_eq_vadd_smul
    {U : Set Tiling.Plane} {s : ℝ} {b : Tiling.Plane} :
    positiveSimilarity s b '' U = b +ᵥ (s • U) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Set.mem_vadd_set.mpr ⟨s • y,
      Set.mem_smul_set.mpr ⟨y, hy, rfl⟩, ?_⟩
    simp only [positiveSimilarity, vadd_eq_add]
    abel
  · rintro hx
    rcases Set.mem_vadd_set.mp hx with ⟨y, hy, rfl⟩
    rcases Set.mem_smul_set.mp hy with ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    simp only [positiveSimilarity, vadd_eq_add]
    abel

theorem positiveSimilarity_vadd_image_of_carrier
    {U V : Set Tiling.Plane} {t : Tiling.Plane} {s : ℝ}
    {r c : Tiling.Plane}
    (hcarrier : V = positiveSimilarity s r '' U) :
    positiveSimilarity s c t +ᵥ V =
      positiveSimilarity s (r + c) '' (t +ᵥ U) := by
  rw [hcarrier]
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with ⟨y, hy, rfl⟩
    refine ⟨t + y, Set.mem_vadd_set.mpr ⟨y, hy, rfl⟩, ?_⟩
    simp only [positiveSimilarity, vadd_eq_add, smul_add]
    abel
  · rintro ⟨z, hz, rfl⟩
    rcases Set.mem_vadd_set.mp hz with ⟨w, hw, rfl⟩
    refine Set.mem_vadd_set.mpr ⟨positiveSimilarity s r w,
      ⟨w, hw, rfl⟩, ?_⟩
    simp only [positiveSimilarity, vadd_eq_add, smul_add]
    abel

theorem positiveSimilarity_openUnion_image
    {K R : Region} {S : Set Tiling.Plane} {s : ℝ}
    {r c : Tiling.Plane}
    (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier) :
    openUnion R (positiveSimilarity s c '' S) =
      positiveSimilarity s (r + c) '' openUnion K S := by
  ext x
  constructor
  · rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion]
    rintro ⟨q, hx⟩
    obtain ⟨t, ht, hqt⟩ := q.2
    rw [hqt.symm] at hx
    change x ∈ positiveSimilarity s c t +ᵥ R.openCarrier at hx
    rw [positiveSimilarity_vadd_image_of_carrier (t := t) hcarrier] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion]
    exact ⟨⟨t, ht⟩, hy⟩
  · rintro ⟨y, hy, rfl⟩
    rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion] at hy
    obtain ⟨q, hy⟩ := hy
    rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion]
    refine ⟨⟨positiveSimilarity s c q.1, ?_⟩, ?_⟩
    · exact ⟨q, q.2, rfl⟩
    · change positiveSimilarity s (r + c) y ∈
        positiveSimilarity s c q.1 +ᵥ R.openCarrier
      rw [positiveSimilarity_vadd_image_of_carrier (t := q.1) hcarrier]
      exact ⟨y, hy, rfl⟩

theorem positiveSimilarity_support_image
    {K R : Region} {s : ℝ} {r : Tiling.Plane} (hs : 0 < s)
    (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier) :
    R.support = positiveSimilarity s r '' K.support := by
  let H := positiveSimilarityHomeomorph s r hs
  have hopen : R.openCarrier = H '' K.openCarrier := by
    change R.openCarrier = positiveSimilarity s r '' K.openCarrier
    exact hcarrier
  rw [← R.isPolygonal.closure_interior, ← K.isPolygonal.closure_interior]
  change closure R.openCarrier = H '' closure K.openCarrier
  rw [hopen, H.image_closure]

theorem positiveSimilarity_regularSupport_image
    {K R : Region} {S : Set Tiling.Plane} {s : ℝ}
    {r c : Tiling.Plane} (hs : 0 < s)
    (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier) :
    regularSupport R (positiveSimilarity s c '' S) =
      positiveSimilarity s (r + c) '' regularSupport K S := by
  rw [regularSupport, regularSupport, Tiling.Polygonal.regularSupport,
    Tiling.Polygonal.regularSupport]
  change interior (closure (openUnion R (positiveSimilarity s c '' S))) =
    positiveSimilarity s (r + c) '' interior (closure (openUnion K S))
  rw [positiveSimilarity_openUnion_image hcarrier]
  let H := positiveSimilarityHomeomorph s (r + c) hs
  change interior (closure (H '' openUnion K S)) =
    H '' interior (closure (openUnion K S))
  rw [H.image_interior, H.image_closure]

theorem positiveSimilarity_vertices_image
    {K R : Region} {s : ℝ} {r : Tiling.Plane} (hs : 0 < s)
    (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier) :
    R.vertices = positiveSimilarity s r '' K.vertices := by
  calc
    R.vertices = Tiling.vertexSet R.support := R.vertices_eq_vertexSet
    _ = Tiling.vertexSet (positiveSimilarity s r '' K.support) := by
      rw [positiveSimilarity_support_image hs hcarrier]
    _ = Tiling.vertexSet (r +ᵥ (s • K.support)) := by
      rw [positiveSimilarity_image_eq_vadd_smul]
    _ = r +ᵥ Tiling.vertexSet (s • K.support) :=
      Tiling.vertexSet_vadd r (s • K.support)
    _ = r +ᵥ (s • Tiling.vertexSet K.support) := by
      rw [Tiling.vertexSet_smul s (ne_of_gt hs) K.support]
    _ = positiveSimilarity s r '' K.vertices := by
      rw [positiveSimilarity_image_eq_vadd_smul, K.vertices_eq_vertexSet]

private theorem positiveSimilarity_quasiMeasurePreserving
    {s : ℝ} {b : Tiling.Plane} (hs : 0 < s) :
    Measure.QuasiMeasurePreserving (positiveSimilarity s b)
      MeasureTheory.volume MeasureTheory.volume := by
  convert
    (MeasureTheory.quasiMeasurePreserving_add_left MeasureTheory.volume b).comp
      (MeasureTheory.volume.quasiMeasurePreserving_smul (ne_of_gt hs)) using 1
  funext z
  simp [positiveSimilarity, add_comm]

private theorem positiveSimilarity_aedisjoint_image
    {A B : Set Tiling.Plane} {s : ℝ} {b : Tiling.Plane} (hs : 0 < s) :
    MeasureTheory.AEDisjoint MeasureTheory.volume
        (positiveSimilarity s b '' A) (positiveSimilarity s b '' B) ↔
      MeasureTheory.AEDisjoint MeasureTheory.volume A B := by
  let H := positiveSimilarityHomeomorph s b hs
  have hqi : Measure.QuasiMeasurePreserving H.symm
      MeasureTheory.volume MeasureTheory.volume := by
    -- The inverse has the same affine form with positive scale `s⁻¹`.
    have hs' : 0 < s⁻¹ := inv_pos.mpr hs
    let b' : Tiling.Plane := -(s⁻¹ • b)
    have hform : (fun z : Tiling.Plane => s⁻¹ • z + b') = H.symm := by
      funext z
      apply H.injective
      rw [H.apply_symm_apply]
      change positiveSimilarity s b (s⁻¹ • z + b') = z
      have hsb : s • (s⁻¹ • b) = b := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
      have hsz : s • (s⁻¹ • z) = z := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
      simp only [positiveSimilarity, b', smul_add]
      simp only [smul_neg]
      rw [hsz, hsb]
      simp
    rw [← hform]
    exact positiveSimilarity_quasiMeasurePreserving hs'
  constructor
  · intro h
    change MeasureTheory.AEDisjoint MeasureTheory.volume (H '' A) (H '' B) at h
    have hqH : Measure.QuasiMeasurePreserving H
        MeasureTheory.volume MeasureTheory.volume := by
      change Measure.QuasiMeasurePreserving (positiveSimilarity s b)
        MeasureTheory.volume MeasureTheory.volume
      exact positiveSimilarity_quasiMeasurePreserving hs
    have hp := h.preimage hqH
    simpa only [H.preimage_image] using hp
  · intro h
    have hp := h.preimage hqi
    change MeasureTheory.AEDisjoint MeasureTheory.volume (H '' A) (H '' B)
    simpa only [H.preimage_symm] using hp

private theorem positiveSimilarity_isPacking_iff
    {K R : Region} {S : Set Tiling.Plane} {s : ℝ}
    {r c : Tiling.Plane} (hs : 0 < s)
    (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier) :
    Tiling.IsPacking R.toPolygonalRegion.prototileFamily
        (R.toPolygonalRegion.placements (positiveSimilarity s c '' S)) ↔
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) := by
  constructor
  · intro hpack
    change (K.toPolygonalRegion.placements S).Pairwise
      (MeasureTheory.AEDisjoint MeasureTheory.volume on
        Tiling.placedTile K.toPolygonalRegion.prototileFamily)
    intro i hi j hj hij
    change i.1 ∈ S at hi
    change j.1 ∈ S at hj
    let i' : R.toPolygonalRegion.placements (positiveSimilarity s c '' S) :=
      ⟨(positiveSimilarity s c i.1, ()), ⟨i.1, hi, rfl⟩⟩
    let j' : R.toPolygonalRegion.placements (positiveSimilarity s c '' S) :=
      ⟨(positiveSimilarity s c j.1, ()), ⟨j.1, hj, rfl⟩⟩
    have hij' : i' ≠ j' := by
      intro heq
      apply hij
      apply Prod.ext
      · have hcentres := congrArg
          (fun p : Tiling.Placement Tiling.Plane Unit => p.1)
          (congrArg Subtype.val heq)
        exact positiveSimilarity_injective hs (by simpa [i', j'] using hcentres)
      · exact Subsingleton.elim _ _
    have hij'raw : (i'.1 : Tiling.Placement Tiling.Plane Unit) ≠ j'.1 := by
      intro heq
      exact hij' (Subtype.ext heq)
    have h' := hpack i'.2 j'.2 hij'raw
    have hiTile :
        Tiling.placedTile R.toPolygonalRegion.prototileFamily i' =
          positiveSimilarity s (r + c) ''
            Tiling.placedTile K.toPolygonalRegion.prototileFamily i := by
      change (positiveSimilarity s c i.1) +ᵥ R.support = _
      rw [positiveSimilarity_support_image hs hcarrier]
      rw [positiveSimilarity_vadd_image_of_carrier
        (t := i.1) (U := K.support) (V := positiveSimilarity s r '' K.support) rfl]
      rfl
    have hjTile :
        Tiling.placedTile R.toPolygonalRegion.prototileFamily j' =
          positiveSimilarity s (r + c) ''
            Tiling.placedTile K.toPolygonalRegion.prototileFamily j := by
      change (positiveSimilarity s c j.1) +ᵥ R.support = _
      rw [positiveSimilarity_support_image hs hcarrier]
      rw [positiveSimilarity_vadd_image_of_carrier
        (t := j.1) (U := K.support) (V := positiveSimilarity s r '' K.support) rfl]
      rfl
    change MeasureTheory.AEDisjoint MeasureTheory.volume
      (Tiling.placedTile R.toPolygonalRegion.prototileFamily i')
      (Tiling.placedTile R.toPolygonalRegion.prototileFamily j') at h'
    rw [hiTile, hjTile] at h'
    exact (positiveSimilarity_aedisjoint_image hs).mp h'
  · intro hpack
    change (R.toPolygonalRegion.placements (positiveSimilarity s c '' S)).Pairwise
      (MeasureTheory.AEDisjoint MeasureTheory.volume on
        Tiling.placedTile R.toPolygonalRegion.prototileFamily)
    intro i hi j hj hij
    change i.1 ∈ positiveSimilarity s c '' S at hi
    change j.1 ∈ positiveSimilarity s c '' S at hj
    have hiS : i.1 ∈ positiveSimilarity s c '' S := hi
    have hjS : j.1 ∈ positiveSimilarity s c '' S := hj
    obtain ⟨a, ha, hia⟩ := hiS
    obtain ⟨b, hb, hjb⟩ := hjS
    let i₀ : K.toPolygonalRegion.placements S := ⟨(a, ()), ha⟩
    let j₀ : K.toPolygonalRegion.placements S := ⟨(b, ()), hb⟩
    have hij₀ : i₀ ≠ j₀ := by
      intro heq
      apply hij
      apply Prod.ext
      · have heq' := congrArg (fun p : Tiling.Placement Tiling.Plane Unit => p.1)
          (congrArg Subtype.val heq)
        rw [← hia, ← hjb]
        exact congrArg (positiveSimilarity s c) (by simpa [i₀, j₀] using heq')
      · exact Subsingleton.elim _ _
    have hij₀raw : (i₀.1 : Tiling.Placement Tiling.Plane Unit) ≠ j₀.1 := by
      intro heq
      exact hij₀ (Subtype.ext heq)
    have h' := hpack i₀.2 j₀.2 hij₀raw
    have hiTile :
        Tiling.placedTile R.toPolygonalRegion.prototileFamily i =
          positiveSimilarity s (r + c) ''
            Tiling.placedTile K.toPolygonalRegion.prototileFamily i₀ := by
      change i.1 +ᵥ R.support = _
      rw [positiveSimilarity_support_image hs hcarrier]
      rw [← hia, positiveSimilarity_vadd_image_of_carrier
        (t := a) (U := K.support) (V := positiveSimilarity s r '' K.support) rfl]
      rfl
    have hjTile :
        Tiling.placedTile R.toPolygonalRegion.prototileFamily j =
          positiveSimilarity s (r + c) ''
            Tiling.placedTile K.toPolygonalRegion.prototileFamily j₀ := by
      change j.1 +ᵥ R.support = _
      rw [positiveSimilarity_support_image hs hcarrier]
      rw [← hjb, positiveSimilarity_vadd_image_of_carrier
        (t := b) (U := K.support) (V := positiveSimilarity s r '' K.support) rfl]
      rfl
    change MeasureTheory.AEDisjoint MeasureTheory.volume
      (Tiling.placedTile R.toPolygonalRegion.prototileFamily i)
      (Tiling.placedTile R.toPolygonalRegion.prototileFamily j)
    rw [hiTile, hjTile]
    exact (positiveSimilarity_aedisjoint_image hs).mpr h'

theorem tilesOn_positiveSimilarity_iff
    {K R : Region} {S D : Set Tiling.Plane} {s : ℝ}
    {r c : Tiling.Plane} (hs : 0 < s)
    (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier) :
    TilesOn R (positiveSimilarity s c '' S)
        (positiveSimilarity s (r + c) '' D) ↔
      TilesOn K S D := by
  let H := positiveSimilarityHomeomorph s (r + c) hs
  have hpoint (y : Tiling.Plane) (U : Set Tiling.Plane) :
      H y ∈ H '' U ↔ y ∈ U := by
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := H.injective hzy
      rw [hzy'] at hz
      exact hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have htile (y t : Tiling.Plane) :
      H y ∈ positiveSimilarity s c t +ᵥ R.openCarrier ↔
        y ∈ t +ᵥ K.openCarrier := by
    rw [positiveSimilarity_vadd_image_of_carrier (t := t) hcarrier]
    exact hpoint y _
  have hqi : Measure.QuasiMeasurePreserving H.symm
      MeasureTheory.volume MeasureTheory.volume := by
    have hs' : 0 < s⁻¹ := inv_pos.mpr hs
    let b' : Tiling.Plane := -(s⁻¹ • (r + c))
    have hform : (fun z : Tiling.Plane => s⁻¹ • z + b') = H.symm := by
      funext z
      apply H.injective
      rw [H.apply_symm_apply]
      change positiveSimilarity s (r + c) (s⁻¹ • z + b') = z
      have hsb : s • (s⁻¹ • (r + c)) = r + c := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
      have hsz : s • (s⁻¹ • z) = z := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
      have hsum : s • (s⁻¹ • r) + s • (s⁻¹ • c) = r + c := by
        rw [← smul_add, ← smul_add, smul_smul,
          mul_inv_cancel₀ (ne_of_gt hs), one_smul]
      simp only [positiveSimilarity, b', smul_add, smul_neg]
      rw [hsz, hsum]
      abel
    rw [← hform]
    exact positiveSimilarity_quasiMeasurePreserving hs'
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact Set.countable_of_injective_of_countable_image
        (positiveSimilarity_injective hs).injOn h.1
    · exact (positiveSimilarity_isPacking_iff hs hcarrier).mp h.2.1
    · have hcov :=
        (positiveSimilarity_quasiMeasurePreserving (b := r + c) hs).ae h.2.2
      filter_upwards [hcov] with y hy
      change (y ∈ D ↔ ∃ t : S, y ∈ (t : Tiling.Plane) +ᵥ K.openCarrier)
      constructor
      · intro hyD
        have hFy : H y ∈ H '' D := ⟨y, hyD, rfl⟩
        obtain ⟨q, hq⟩ := hy.mp hFy
        obtain ⟨t, ht, hqt⟩ := q.2
        refine ⟨⟨t, ht⟩, ?_⟩
        apply (htile y t).mp
        change H y ∈ (q : Tiling.Plane) +ᵥ R.openCarrier at hq
        simpa [hqt] using hq
      · rintro ⟨t, ht⟩
        apply (hpoint y D).mp
        apply hy.mpr
        refine ⟨⟨positiveSimilarity s c t,
          ⟨t, t.2, rfl⟩⟩, ?_⟩
        change H y ∈ _
        exact (htile y t).mpr ht
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact h.1.image (positiveSimilarity s c)
    · exact (positiveSimilarity_isPacking_iff hs hcarrier).mpr h.2.1
    · have hcov := hqi.ae h.2.2
      filter_upwards [hcov] with y hy
      constructor
      · intro hDy
        have hyD : H.symm y ∈ D := by
          apply (hpoint (H.symm y) D).mp
          change y ∈ H '' D at hDy
          simpa only [H.apply_symm_apply] using hDy
        obtain ⟨t, ht⟩ := hy.mp hyD
        refine ⟨⟨positiveSimilarity s c t,
          ⟨t, t.2, rfl⟩⟩, ?_⟩
        simpa only [H.apply_symm_apply, Region.openCarrier] using (htile (H.symm y) t).mpr ht
      · rintro ⟨q, hq⟩
        obtain ⟨t, ht, hqt⟩ := q.2
        have hpre : H.symm y ∈ D := by
          apply hy.mpr
          refine ⟨⟨t, ht⟩, ?_⟩
          apply (htile (H.symm y) t).mp
          have hq' : H (H.symm y) ∈
              (q : Tiling.Plane) +ᵥ R.openCarrier := by
            simpa only [H.apply_symm_apply, Region.openCarrier] using hq
          simpa [hqt] using hq'
        change y ∈ H '' D
        exact ⟨H.symm y, hpre, H.apply_symm_apply y⟩

end Tiling.AxisParallel
