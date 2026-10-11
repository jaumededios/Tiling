import Tiling.RationalSlopes.Links
import Tiling.RationalSlopes.BoundaryGeometry
import Tiling.RationalSlopes.Approximation.LinkTransport
import Tiling.RationalSlopes.Approximation.FLCTransport
import Tiling.RationalSlopes.DirectionalRaster
import Tiling.RationalSlopes.EarthquakePeriodicity
import Tiling.RationalSlopes.SlicesAndColumns
-- Root-approved 2026-10-06: acyclic existing product-period provider; also
-- exposes the existing generic finite closed-interval merger.
import Tiling.AxisParallel.Structure.ProductRigidity

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

def properContactDisplacements (K : PolygonalRegion) (η : Submodule ℝ Plane)
    (T : Set Plane) : Set Plane :=
  {d | ∃ s ∈ T, ∃ t ∈ T, s ≠ t ∧ d = s - t ∧ ProperEdgeContactAlong K η s t}

def HasFiniteOffDirectionContacts (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) : Prop :=
  ∀ η : Submodule ℝ Plane, Module.finrank ℝ η = 1 →
    HasBoundaryDirection K η → η ≠ δ → (properContactDisplacements K η T).Finite

def IsProductAlong (K : PolygonalRegion) (δ η : Submodule ℝ Plane) : Prop :=
  K.support = directionalSaturation δ K.support ∩ directionalSaturation η K.support

def SupportClose (ε : ℝ) (K L : PolygonalRegion) : Prop :=
  (∀ x ∈ K.support, ∃ y ∈ L.support, dist x y < ε) ∧
    (∀ y ∈ L.support, ∃ x ∈ K.support, dist x y < ε)

structure PersistentColumnData (K : PolygonalRegion) (T : Set Plane)
    (η : Submodule ℝ Plane) where
  anchor : Plane
  anchor_mem_source : anchor ∈ T
  movingCentre : ℕ → Plane
  movingCentre_mem_source : ∀ n, movingCentre n ∈ T
  limitCentres : Set Plane
  converges : Tiling.Topology.LocallyFellConverges
    (fun n => (anchor - movingCentre n) +ᵥ T) limitCentres
  column : Set Plane
  column_subset : column ⊆ limitCentres
  column_isColumn : IsCenterColumn K η column
  anchor_mem_column : anchor ∈ column
  persistent : ∀ u ∈ column, ∀ᶠ n in atTop,
    u - (anchor - movingCentre n) ∈ T

/-! Actual finite old-contact data. No condition is imposed on a pair that has
no old positive-length contact. -/

private def oldOffDirectionContactAlphabet (K : PolygonalRegion)
    (δ : Submodule ℝ Plane) (T : Set Plane) : Set Plane :=
  ⋃ η ∈ {η : Submodule ℝ Plane | Module.finrank ℝ η = 1 ∧
    HasBoundaryDirection K η ∧ η ≠ δ}, properContactDisplacements K η T

private theorem oldOffDirectionContactAlphabet_finite
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    (h : HasFiniteOffDirectionContacts K δ T) :
    (oldOffDirectionContactAlphabet K δ T).Finite := by
  have hdirs : {η : Submodule ℝ Plane | Module.finrank ℝ η = 1 ∧
      HasBoundaryDirection K η ∧ η ≠ δ}.Finite :=
    (boundaryDirections_finite K).subset (fun _ hη => hη.2.1)
  exact hdirs.biUnion fun η hη => h η hη.1 hη.2.1 hη.2.2

/-- Endpoint offsets for actual old contacts: a tile vertex minus the old
contact displacement minus an intrinsic edge endpoint. Noncontacts are absent. -/
private def oldContactEndpointAlphabet (K : PolygonalRegion)
    (δ : Submodule ℝ Plane) (T : Set Plane) : Set Plane :=
  (vertexSet K.support - oldOffDirectionContactAlphabet K δ T) - vertexSet K.support

private theorem oldContactEndpointAlphabet_finite
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    (h : HasFiniteOffDirectionContacts K δ T) :
    (oldContactEndpointAlphabet K δ T).Finite := by
  exact (K.isPolygonal.vertexSet_finite.sub
    (oldOffDirectionContactAlphabet_finite h)).sub K.isPolygonal.vertexSet_finite

private theorem actualOldContact_vertexEndpoint_offset_mem
    {K : PolygonalRegion} {δ η : Submodule ℝ Plane} {T : Set Plane}
    (hη : Module.finrank ℝ η = 1) (hb : HasBoundaryDirection K η)
    (hne : η ≠ δ) {s t w b : Plane}
    (hs : s ∈ T) (ht : t ∈ T) (hst : s ≠ t)
    (hcontact : ProperEdgeContactAlong K η s t)
    (hw : w ∈ vertexSet K.support) (hbv : b ∈ vertexSet K.support) :
    w - (s - t) - b ∈ oldContactEndpointAlphabet K δ T := by
  have hd : s - t ∈ oldOffDirectionContactAlphabet K δ T := by
    apply Set.mem_iUnion.mpr
    refine ⟨η, Set.mem_iUnion.mpr ⟨⟨hη, hb, hne⟩, ?_⟩⟩
    exact ⟨s, hs, t, ht, hst, rfl, hcontact⟩
  exact Set.mem_sub.mpr ⟨w - (s - t), Set.mem_sub.mpr ⟨w, hw,
    s - t, hd, rfl⟩, b, hbv, rfl⟩

/- Contact differences have bounded prototype support, independently of the
distance or density of the ambient centre family. -/
open Tiling.Approximation in
/-- Actual old-contact endpoint offsets supply finite rational-normal tests.
The statement is restricted to offsets of old positive-length contacts; it
asserts nothing about arbitrary near-contact or noncontact pairs. -/
private theorem oldContactEndpoint_finiteNormalTests
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hfinite : HasFiniteOffDirectionContacts K δ T) (N : Finset RationalNormal) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ d ∈ oldContactEndpointAlphabet K δ T, ∀ n ∈ N,
          Real.sign (normalEval n (deformPoint φ d)) = Real.sign (normalEval n d) ∧
            (normalEval n (deformPoint φ d) = 0 ↔ normalEval n d = 0) := by
  classical
  let D := (oldContactEndpointAlphabet_finite hfinite).toFinset
  let Z : Finset ℝ := (D.product N).image (fun p => normalEval p.2 p.1)
  obtain ⟨F, ε, hε, htests⟩ := finiteApproximation_signAndEquality Z
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ d hd n hn
  have hdD : d ∈ D := (oldContactEndpointAlphabet_finite hfinite).mem_toFinset.mpr hd
  have hz : normalEval n d ∈ Z :=
    Finset.mem_image.mpr ⟨(d, n), Finset.mem_product.mpr ⟨hdD, hn⟩, rfl⟩
  have hsign := (htests φ hφ).1 _ hz
  rw [← rationalNormal_commutes φ n d] at hsign
  refine ⟨hsign, ?_⟩
  constructor
  · intro h
    apply Real.sign_eq_zero_iff.mp
    rw [← hsign]
    exact Real.sign_eq_zero_iff.mpr h
  · intro h
    apply Real.sign_eq_zero_iff.mp
    rw [hsign]
    exact Real.sign_eq_zero_iff.mpr h

private theorem properContactDisplacements_subset_supportDifference
    (K : PolygonalRegion) (η : Submodule ℝ Plane) (T : Set Plane) :
    properContactDisplacements K η T ⊆ K.support - K.support := by
  rintro d ⟨s, _, t, _, _, rfl, a, b, _, _, hedge⟩
  have hm := hedge (midpoint_mem_openSegment (𝕜 := ℝ) a b)
  have hms : midpoint ℝ a b ∈ s +ᵥ K.support := by
    exact (K.isPolygonal.isClosed.vadd s).closure_eq ▸ frontier_subset_closure hm.1
  have hmt : midpoint ℝ a b ∈ t +ᵥ K.support := by
    exact (K.isPolygonal.isClosed.vadd t).closure_eq ▸ frontier_subset_closure hm.2
  obtain ⟨x, hx, hxs⟩ := hms
  obtain ⟨y, hy, hyt⟩ := hmt
  refine Set.mem_sub.mpr ⟨y, hy, x, hx, ?_⟩
  change s + x = midpoint ℝ a b at hxs
  change t + y = midpoint ℝ a b at hyt
  have hxy : s + x = t + y := hxs.trans hyt.symm
  linear_combination -hxy

private theorem supportClose_self (K : PolygonalRegion) {ε : ℝ} (hε : 0 < ε) :
    SupportClose ε K K := by
  constructor <;> intro x hx <;> exact ⟨x, hx, by simpa using hε⟩

private theorem supportClose_symm {K L : PolygonalRegion} {ε : ℝ}
    (h : SupportClose ε K L) : SupportClose ε L K := by
  constructor
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := h.2 x hx
    exact ⟨y, hy, by simpa [dist_comm] using hxy⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := h.1 y hy
    exact ⟨x, hx, by simpa [dist_comm] using hxy⟩

private theorem supportClose_triangle {K L M : PolygonalRegion} {ε ζ : ℝ}
    (hKL : SupportClose ε K L) (hLM : SupportClose ζ L M) :
    SupportClose (ε + ζ) K M := by
  constructor
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hKL.1 x hx
    obtain ⟨z, hz, hyz⟩ := hLM.1 y hy
    exact ⟨z, hz, lt_of_le_of_lt (dist_triangle x y z) (add_lt_add hxy hyz)⟩
  · intro z hz
    obtain ⟨y, hy, hyz⟩ := hLM.2 z hz
    obtain ⟨x, hx, hxy⟩ := hKL.2 y hy
    exact ⟨x, hx, lt_of_le_of_lt (dist_triangle x y z) (add_lt_add hxy hyz)⟩

/-- The stationary case is an explicit anchored orbit and exact-membership
construction. The nonstationary paired-limit constructor belongs to UR. -/
private def persistentColumnData_of_column
    {K : PolygonalRegion} {T C : Set Plane} {η : Submodule ℝ Plane}
    (hT : IsClosed T) (hCT : C ⊆ T) (hC : IsCenterColumn K η C)
    (a : Plane) (ha : a ∈ C) : PersistentColumnData K T η where
  anchor := a
  anchor_mem_source := hCT ha
  movingCentre := fun _ => a
  movingCentre_mem_source := fun _ => hCT ha
  limitCentres := T
  converges := by
    simp only [sub_self, zero_vadd]
    exact ⟨fun _ => hT, hT, tendsto_const_nhds⟩
  column := C
  column_subset := hCT
  column_isColumn := hC
  anchor_mem_column := ha
  persistent := by
    intro u hu
    exact Filter.Eventually.of_forall (fun _ => by simpa using hCT hu)

/-- The intersection operation retains centre labels in one common packing.
Regularization is justified by the regular-open intersection law. -/
private theorem regularSupport_inter_of_commonPacking
    {K : PolygonalRegion} {T C D : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements T))
    (hCT : C ⊆ T) (hDT : D ⊆ T) :
    regularSupport K C ∩ regularSupport K D = regularSupport K (C ∩ D) := by
  have hpair := (isPacking_iff_openCarrier_disjoint K T).mp hp
  have hpC : IsPacking K.prototileFamily (K.placements C) :=
    (isPacking_iff_openCarrier_disjoint K C).mpr fun s hs t ht hst =>
      hpair (hCT hs) (hCT ht) hst
  have hpD : IsPacking K.prototileFamily (K.placements D) :=
    (isPacking_iff_openCarrier_disjoint K D).mpr fun s hs t ht hst =>
      hpair (hDT hs) (hDT ht) hst
  have hpCD : IsPacking K.prototileFamily (K.placements (C ∩ D)) :=
    (isPacking_iff_openCarrier_disjoint K (C ∩ D)).mpr fun s hs t ht hst =>
      hpair (hCT hs.1) (hCT ht.1) hst
  have hraw : openUnion K C ∩ openUnion K D = openUnion K (C ∩ D) := by
    ext x
    simp only [mem_inter_iff, openUnion, mem_iUnion]
    constructor
    · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
      have hst : (s : Plane) = t := by
        by_contra hne
        exact Set.disjoint_left.mp (hpair (hCT s.2) (hDT t.2) hne) hs ht
      exact ⟨⟨s, s.2, hst.symm ▸ t.2⟩, hs⟩
    · rintro ⟨s, hs⟩
      exact ⟨⟨⟨s, s.2.1⟩, hs⟩, ⟨⟨s, s.2.2⟩, hs⟩⟩
  have hCreg := regularSupport_isRegularOpen K C
  have hDreg := regularSupport_isRegularOpen K D
  have hCDreg := regularSupport_isRegularOpen K (C ∩ D)
  have hreg : interior (closure (regularSupport K C ∩ regularSupport K D)) =
      regularSupport K C ∩ regularSupport K D := by
    apply subset_antisymm
    · calc
        interior (closure (regularSupport K C ∩ regularSupport K D)) ⊆
            interior (closure (regularSupport K C) ∩ closure (regularSupport K D)) :=
          interior_mono closure_inter_subset
        _ = regularSupport K C ∩ regularSupport K D := by
          rw [interior_inter, hCreg.2, hDreg.2]
    · exact (hCreg.1.inter hDreg.1).subset_interior_closure
  apply regularOpen_eq_of_aeEq (hCreg.1.inter hDreg.1) hreg hCDreg.1 hCDreg.2
  filter_upwards [openUnion_aeEq_regularSupport hpC,
    openUnion_aeEq_regularSupport hpD, openUnion_aeEq_regularSupport hpCD]
    with x hxC hxD hxCD
  change (x ∈ regularSupport K C ∩ regularSupport K D) =
    (x ∈ regularSupport K (C ∩ D))
  change (x ∈ openUnion K C) = (x ∈ regularSupport K C) at hxC
  change (x ∈ openUnion K D) = (x ∈ regularSupport K D) at hxD
  change (x ∈ openUnion K (C ∩ D)) = (x ∈ regularSupport K (C ∩ D)) at hxCD
  rw [mem_inter_iff, ← hxC, ← hxD, ← hxCD]
  exact congrArg (fun E : Set Plane => x ∈ E) hraw

private theorem directionalSaturation_support_isClosed
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) :
    IsClosed (directionalSaturation δ K.support) := by
  have heq : directionalSaturation δ K.support = K.support + (δ : Set Plane) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact Set.mem_add.mpr ⟨y, hy, x - y, hxy, by abel⟩
    · rintro ⟨y, hy, u, hu, rfl⟩
      exact ⟨y, hy, by simpa using hu⟩
  rw [heq]
  exact (Submodule.closed_of_finiteDimensional δ).add_left_of_isCompact
    K.isPolygonal.isCompact

private theorem closure_regularSupport_eq_supportUnion
    {K : PolygonalRegion} {C : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements C)) :
    closure (regularSupport K C) = ⋃ s : C, (s : Plane) +ᵥ K.support := by
  rw [← closure_openUnion_eq_iUnion_support hp]
  apply subset_antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · apply closure_mono
    exact (isOpen_iUnion fun s : C => isOpen_interior.vadd (s : Plane)).subset_interior_closure

private theorem closure_columnCarrier_eq_saturation
    {K : PolygonalRegion} {C : Set Plane} {δ : Submodule ℝ Plane}
    (hC : IsCenterColumn K δ C) {s : Plane} (hs : s ∈ C) :
    closure (regularSupport K C) = s +ᵥ directionalSaturation δ K.support := by
  have hinv : IsInvariantAlong (closure (regularSupport K C)) δ := by
    intro u hu
    rw [← closure_vadd]
    exact congrArg closure (hC.2.2.2 u hu)
  obtain ⟨a, hline⟩ := hC.2.2.1
  have hcs : ∀ c ∈ C, c - s ∈ δ := by
    intro c hc
    convert δ.sub_mem (hline c hc) (hline s hs) using 1
    abel
  apply subset_antisymm
  · rw [closure_regularSupport_eq_supportUnion hC.1]
    intro x hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
    obtain ⟨y, hy, rfl⟩ := hc
    refine ⟨(c - s) + y, ⟨y, hy, ?_⟩, ?_⟩
    · simpa using hcs c c.2
    · change s + (((c : Plane) - s) + y) = (c : Plane) + y
      abel
  · rintro x ⟨z, ⟨y, hy, hzy⟩, rfl⟩
    have hsy : s + y ∈ closure (regularSupport K C) := by
      rw [closure_regularSupport_eq_supportUnion hC.1]
      exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, Set.vadd_mem_vadd_set hy⟩
    have hmem : (z - y) + (s + y) ∈ closure (regularSupport K C) := by
      rw [← hinv (z - y) hzy]
      exact Set.vadd_mem_vadd_set hsy
    change s + z ∈ closure (regularSupport K C)
    convert hmem using 1
    abel

private theorem distinct_lineDirections_isCompl
    (δ η : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) (hη : Module.finrank ℝ η = 1)
    (hne : δ ≠ η) : IsCompl δ η := by
  have hinf : δ ⊓ η = ⊥ := by
    apply le_antisymm
    · intro x hx
      rcases eq_or_ne x 0 with rfl | hx0
      · exact zero_mem _
      have hδspan := eq_span_singleton_of_mem_of_finrank_eq_one hδ hx.1 hx0
      have hηspan := eq_span_singleton_of_mem_of_finrank_eq_one hη hx.2 hx0
      exact (hne (hδspan.trans hηspan.symm)).elim
    · exact bot_le
  apply (Submodule.isCompl_iff_disjoint δ η (by
    simp [Plane, Complex.finrank_real_complex, hδ, hη])).2
  rw [disjoint_iff_inf_le, hinf]

private def realPairToPlane : (ℝ × ℝ) ≃ₗ[ℝ] Plane where
  toFun p := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  invFun z := (z.re, z.im)
  left_inv p := by simp
  right_inv z := by
    change ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z
    exact Complex.ext_iff.mpr (by simp)
  map_add' p q := by
    change ((p.1 + q.1 : ℝ) : ℂ) + ((p.2 + q.2 : ℝ) : ℂ) * Complex.I = _
    simp [add_mul]
    abel
  map_smul' c p := by
    change ((c * p.1 : ℝ) : ℂ) + ((c * p.2 : ℝ) : ℂ) * Complex.I = _
    simp [Complex.ofReal_mul, mul_assoc]

private theorem exists_real_straightening
    (δ η : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) (hη : Module.finrank ℝ η = 1)
    (hne : δ ≠ η) :
    ∃ A : Plane ≃L[ℝ] Plane,
      (∀ x, x ∈ δ ↔ (A x).re = 0) ∧
      (∀ x, x ∈ η ↔ (A x).im = 0) := by
  let hcompl := distinct_lineDirections_isCompl δ η hδ hη hne
  let eδ : δ ≃ₗ[ℝ] ℝ := LinearEquiv.ofFinrankEq δ ℝ (by simp [hδ])
  let eη : η ≃ₗ[ℝ] ℝ := LinearEquiv.ofFinrankEq η ℝ (by simp [hη])
  let C : Plane ≃ₗ[ℝ] δ × η := (Submodule.prodEquivOfIsCompl δ η hcompl).symm
  let A : Plane ≃ₗ[ℝ] Plane :=
    C.trans ((LinearEquiv.prodComm ℝ δ η).trans ((eη.prodCongr eδ).trans realPairToPlane))
  refine ⟨A.toContinuousLinearEquiv, ?_, ?_⟩
  · intro x
    change x ∈ δ ↔ (A x).re = 0
    have hA : A x = realPairToPlane (eη (C x).2, eδ (C x).1) := rfl
    rw [hA]
    change x ∈ δ ↔
      (((eη (C x).2 : ℝ) : ℂ) + ((eδ (C x).1 : ℝ) : ℂ) * Complex.I).re = 0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero]
    simp only [zero_mul, sub_self, add_zero]
    rw [eη.map_eq_zero_iff]
    exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero δ η hcompl).symm
  · intro x
    change x ∈ η ↔ (A x).im = 0
    have hA : A x = realPairToPlane (eη (C x).2, eδ (C x).1) := rfl
    rw [hA]
    change x ∈ η ↔
      (((eη (C x).2 : ℝ) : ℂ) + ((eδ (C x).1 : ℝ) : ℂ) * Complex.I).im = 0
    simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, zero_mul, add_zero]
    simp only [zero_add, mul_one]
    rw [eδ.map_eq_zero_iff]
    exact (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero δ η hcompl).symm

private theorem transverseColumns_inter_singleton
    {K : PolygonalRegion} {T C D : Set Plane} {δ η : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) (hη : Module.finrank ℝ η = 1) (hne : δ ≠ η)
    (hp : IsPacking K.prototileFamily (K.placements T))
    (hCT : C ⊆ T) (hDT : D ⊆ T)
    (hC : IsCenterColumn K δ C) (hD : IsCenterColumn K η D) :
    ∃ s : Plane, s ∈ C ∧ s ∈ D ∧ C ∩ D = {s} := by
  classical
  have hnotdisj : ¬ Disjoint C D := fun hd =>
    hne (disjoint_columns_parallel hδ hη hp hCT hDT hd hC hD)
  obtain ⟨s, hsC, hsD⟩ := Set.not_disjoint_iff.mp hnotdisj
  refine ⟨s, hsC, hsD, ?_⟩
  have hcompl := distinct_lineDirections_isCompl δ η hδ hη hne
  obtain ⟨a, hlineC⟩ := hC.2.2.1
  obtain ⟨b, hlineD⟩ := hD.2.2.1
  ext x
  constructor
  · intro hx
    have hxδ : x - s ∈ δ := by
      convert δ.sub_mem (hlineC x hx.1) (hlineC s hsC) using 1
      abel
    have hxη : x - s ∈ η := by
      convert η.sub_mem (hlineD x hx.2) (hlineD s hsD) using 1
      abel
    have hx0 : x - s ∈ δ ⊓ η := ⟨hxδ, hxη⟩
    rw [hcompl.disjoint.eq_bot] at hx0
    exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp hx0)
  · rintro rfl
    exact ⟨hsC, hsD⟩

private theorem distinct_lineDirections_continuousProjections
    (δ η : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) (hη : Module.finrank ℝ η = 1)
    (hne : δ ≠ η) :
    ∃ Pδ Pη : Plane →L[ℝ] Plane,
      (∀ x, Pδ x + Pη x = x) ∧
      (∀ x, Pδ x ∈ δ) ∧ (∀ x, Pη x ∈ η) ∧
      (∀ x ∈ η, Pδ x = 0) ∧ (∀ x ∈ δ, Pη x = 0) := by
  let hcompl := distinct_lineDirections_isCompl δ η hδ hη hne
  let Pδ : Plane →L[ℝ] Plane := (δ.projection η hcompl).toContinuousLinearMap
  let Pη : Plane →L[ℝ] Plane := (η.projection δ hcompl.symm).toContinuousLinearMap
  refine ⟨Pδ, Pη, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change δ.projection η hcompl x + η.projection δ hcompl.symm x = x
    exact Submodule.projection_add_projection_eq_self hcompl x
  · intro x
    change δ.projection η hcompl x ∈ δ
    exact Submodule.projection_apply_mem hcompl x
  · intro x
    change η.projection δ hcompl.symm x ∈ η
    exact Submodule.projection_apply_mem hcompl.symm x
  · intro x hx
    change δ.projection η hcompl x = 0
    exact Submodule.projection_apply_right hcompl ⟨x, hx⟩
  · intro x hx
    change η.projection δ hcompl.symm x = 0
    exact Submodule.projection_apply_right hcompl.symm ⟨x, hx⟩

/-- Complementary cylinders have no spurious boundary-only intersection. The
recombination of two nearby points is continuous and preserves each cylinder. -/
private theorem invariantCylinder_closure_inter
    {A B : Set Plane} {δ η : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) (hη : Module.finrank ℝ η = 1) (hne : δ ≠ η)
    (hA : IsInvariantAlong A δ) (hB : IsInvariantAlong B η) :
    closure (A ∩ B) = closure A ∩ closure B := by
  let hcompl := distinct_lineDirections_isCompl δ η hδ hη hne
  let Pδ : Plane →L[ℝ] Plane := (δ.projection η hcompl).toContinuousLinearMap
  let Pη : Plane →L[ℝ] Plane := (η.projection δ hcompl.symm).toContinuousLinearMap
  have hsum : ∀ x, Pδ x + Pη x = x := by
    intro x
    exact Submodule.projection_add_projection_eq_self hcompl x
  let f : Plane × Plane → Plane := fun p => Pδ p.2 + Pη p.1
  have hf : Continuous f :=
    (Pδ.continuous.comp continuous_snd).add (Pη.continuous.comp continuous_fst)
  have hfsubset : f '' (A ×ˢ B) ⊆ A ∩ B := by
    rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    have hdδ : Pδ b + Pη a - a ∈ δ := by
      have heq : Pδ b + Pη a - a = Pδ (b - a) := by
        calc
          Pδ b + Pη a - a = (Pδ b + Pη a) - (Pδ a + Pη a) := by rw [hsum a]
          _ = Pδ (b - a) := by rw [map_sub]; abel
      rw [heq]
      exact Submodule.projection_apply_mem hcompl (b - a)
    have hdη : Pδ b + Pη a - b ∈ η := by
      have heq : Pδ b + Pη a - b = Pη (a - b) := by
        calc
          Pδ b + Pη a - b = (Pδ b + Pη a) - (Pδ b + Pη b) := by rw [hsum b]
          _ = Pη (a - b) := by rw [map_sub]; abel
      rw [heq]
      exact Submodule.projection_apply_mem hcompl.symm (a - b)
    constructor
    · have hz : (Pδ b + Pη a - a) + a ∈ A := by
        rw [← hA _ hdδ]
        exact Set.vadd_mem_vadd_set ha
      simpa using hz
    · have hz : (Pδ b + Pη a - b) + b ∈ B := by
        rw [← hB _ hdη]
        exact Set.vadd_mem_vadd_set hb
      simpa using hz
  apply subset_antisymm closure_inter_subset
  intro x hx
  have hxx : (x, x) ∈ closure (A ×ˢ B) := by
    rw [closure_prod_eq]
    exact hx
  have hfx : f (x, x) ∈ closure (f '' (A ×ˢ B)) :=
    image_closure_subset_closure_image hf ⟨(x, x), hxx, rfl⟩
  have hx' := closure_mono hfsubset hfx
  simpa only [f, hsum] using hx'

private theorem nonzeroFunctional_surjective
    (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) : Function.Surjective ℓ := by
  have hℓlin : ℓ.toLinearMap ≠ 0 := by
    intro hzero
    apply hℓ
    ext x
    exact DFunLike.congr_fun hzero x
  exact surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (by simp) hℓlin

private theorem invariantClosed_hasTransverseMinimum
    {E : Set Plane} {δ : Submodule ℝ Plane} (hEclosed : IsClosed E)
    (hE : E.Nonempty) (hinv : IsInvariantAlong E δ)
    (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ)
    (hbound : ∃ a : ℝ, ∀ x ∈ E, a ≤ ℓ x) :
    ∃ x ∈ E, ∀ y ∈ E, ℓ x ≤ ℓ y := by
  obtain ⟨w, hw⟩ := nonzeroFunctional_surjective ℓ hℓ (1 : ℝ)
  have heq : ℓ '' E = (fun r : ℝ => r • w) ⁻¹' E := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hshift : ℓ x • w - x ∈ δ := by
        rw [← hker]
        change ℓ (ℓ x • w - x) = 0
        simp only [map_sub, map_smul, hw, smul_eq_mul, mul_one, sub_self]
      have hx' : (ℓ x • w - x) + x ∈ E := by
        rw [← hinv _ hshift]
        exact Set.vadd_mem_vadd_set hx
      simpa using hx'
    · intro hr
      exact ⟨r • w, hr, by rw [map_smul, hw]; simp only [smul_eq_mul, mul_one]⟩
  have hclosed : IsClosed (ℓ '' E) := by
    rw [heq]
    exact hEclosed.preimage (continuous_id.smul continuous_const)
  have hbelow : BddBelow (ℓ '' E) := by
    obtain ⟨a, ha⟩ := hbound
    refine ⟨a, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    exact ha x hx
  obtain ⟨x, hx, hxinf⟩ := hclosed.csInf_mem (hE.image ℓ) hbelow
  refine ⟨x, hx, ?_⟩
  intro y hy
  rw [hxinf]
  exact csInf_le hbelow (Set.mem_image_of_mem ℓ hy)

/-- Attainment comes from a fixed longitudinal section of the closed invariant
support, not from local finiteness of the projected centre set. -/
private theorem invariantPacking_centresMinimum
    {K : PolygonalRegion} {S : Set Plane} {δ : Submodule ℝ Plane}
    (hS : S.Nonempty) (hp : IsPacking K.prototileFamily (K.placements S))
    (hinv : IsInvariantAlong (regularSupport K S) δ)
    (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ)
    (hbound : ∃ a : ℝ, ∀ s ∈ S, a ≤ ℓ s) :
    ∃ t ∈ S, ∀ s ∈ S, ℓ t ≤ ℓ s := by
  obtain ⟨k, hk, hkmin⟩ := K.isPolygonal.isCompact.exists_isMinOn K.nonempty ℓ.continuous.continuousOn
  have hclosedInv : IsInvariantAlong (closure (regularSupport K S)) δ := by
    intro u hu
    rw [← closure_vadd]
    exact congrArg closure (hinv u hu)
  have hsupport := closure_regularSupport_eq_supportUnion hp
  have hE : (closure (regularSupport K S)).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    refine ⟨s + k, ?_⟩
    rw [hsupport]
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, Set.vadd_mem_vadd_set hk⟩
  have hEbound : ∃ a : ℝ, ∀ x ∈ closure (regularSupport K S), a ≤ ℓ x := by
    obtain ⟨a, ha⟩ := hbound
    refine ⟨a + ℓ k, ?_⟩
    intro x hx
    rw [hsupport] at hx
    obtain ⟨s, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    change a + ℓ k ≤ ℓ ((s : Plane) + y)
    rw [map_add]
    exact add_le_add (ha s s.2) (hkmin hy)
  obtain ⟨x, hx, hxminimum⟩ := invariantClosed_hasTransverseMinimum
    isClosed_closure hE hclosedInv ℓ hℓ hker hEbound
  rw [hsupport] at hx
  obtain ⟨t, y, hy, hty⟩ := Set.mem_iUnion.mp hx
  change (t : Plane) + y = x at hty
  refine ⟨t, t.2, ?_⟩
  have htk : (t : Plane) + k ∈ closure (regularSupport K S) := by
    rw [hsupport]
    exact Set.mem_iUnion.mpr ⟨t, Set.vadd_mem_vadd_set hk⟩
  have hxmin := hxminimum ((t : Plane) + k) htk
  have hminy : ℓ k ≤ ℓ y := hkmin hy
  have hxval : ℓ x = ℓ t + ℓ k := by
    rw [← hty, map_add] at hxmin ⊢
    rw [map_add] at hxmin
    linarith
  intro s hs
  have hsk : s + k ∈ closure (regularSupport K S) := by
    rw [hsupport]
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, Set.vadd_mem_vadd_set hk⟩
  have h := hxminimum (s + k) hsk
  rw [hxval, map_add] at h
  linarith

/-- A filled collar gives relative density on the centre coset itself. No
plane-relative-density hypothesis is used or inferred for a line fibre. -/
private theorem collarFibre_lineRelativeDense
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (S : Set Plane)
    (t v : Plane) (ℓ : Plane →L[ℝ] ℝ) (c : ℝ)
    (hℓ : ℓ ≠ 0) (hker : LinearMap.ker ℓ.toLinearMap = δ) (hc : 0 < c)
    (hcollar : ∀ x : Plane, ℓ (v + t) < ℓ x → ℓ x < ℓ (v + t) + c →
      ∃ s ∈ lineFibre δ S t, x ∈ s +ᵥ K.support) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : Plane, z - t ∈ δ →
      ∃ s ∈ lineFibre δ S t, dist z s < ρ := by
  obtain ⟨w, hw⟩ := nonzeroFunctional_surjective ℓ hℓ (c / 2)
  obtain ⟨R, hRpos, hR⟩ := K.isPolygonal.isCompact.isBounded.exists_pos_norm_lt
  refine ⟨R + ‖v + w‖, by positivity, ?_⟩
  intro z hz
  have hzℓ : ℓ z = ℓ t := by
    have hz0 : ℓ (z - t) = 0 := by
      change z - t ∈ LinearMap.ker ℓ.toLinearMap
      rwa [hker]
    simpa only [map_sub, sub_eq_zero] using hz0
  have hlow : ℓ (v + t) < ℓ (z + v + w) := by
    simp only [map_add, hzℓ, hw]
    linarith
  have hupp : ℓ (z + v + w) < ℓ (v + t) + c := by
    simp only [map_add, hzℓ, hw]
    linarith
  obtain ⟨s, hs, y, hy, hsy⟩ := hcollar (z + v + w) hlow hupp
  refine ⟨s, hs, ?_⟩
  change s + y = z + v + w at hsy
  have heq : z - s = y - (v + w) := by linear_combination -hsy
  rw [dist_eq_norm, heq]
  exact (norm_sub_le y (v + w)).trans_lt (by linarith [hR y hy])

/-- Nonempty positive words cannot approach zero. This uses the actual
prototype vertex alphabet, rather than a hypothetical transverse FLC bound. -/
private theorem properLink_vertexGap
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ) (hδ : Module.finrank ℝ δ = 1) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ) (htile : TilesOn K T Set.univ) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Plane, IsProperLink K δ T a →
      ∀ x ∈ translatedVertices K T, ℓ x ≠ ℓ a → c ≤ |ℓ x - ℓ a| := by
  obtain ⟨_, _, c, hc, hcgap⟩ := positiveVertexGaps_finitePositive K ℓ hℓ
  refine ⟨c, hc, ?_⟩
  intro a ha x hx hxa
  obtain ⟨G, hGne, hG, heq⟩ :=
    link_distance_isPositiveWord K δ T ℓ hδ hℓ hker htile a ha x hx hxa
  rw [heq]
  cases G with
  | nil => exact (hGne rfl).elim
  | cons r G =>
    have hr : c ≤ r := hcgap r (hG r (by simp))
    have htail : 0 ≤ G.sum := List.sum_nonneg fun q hq =>
      (le_of_lt hc).trans (hcgap q (hG q (by simp [hq])))
    simpa only [List.sum_cons] using le_trans hr (le_add_of_nonneg_right htail)

private theorem minimumFibre_transverseGap
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ) (hδ : Module.finrank ℝ δ = 1) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ) (htile : TilesOn K T Set.univ)
    (t v : Plane) (hv : v ∈ vertexSet K.support)
    (hlink : IsProperLink K δ T (v + t)) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ T, ℓ t < ℓ s → c ≤ ℓ s - ℓ t := by
  obtain ⟨c, hc, hgap⟩ := properLink_vertexGap K δ T ℓ hδ hℓ hker htile
  refine ⟨c, hc, ?_⟩
  intro s hs hts
  have hcloud : v + s ∈ translatedVertices K T := Set.add_mem_add hv hs
  have hneq : ℓ (v + s) ≠ ℓ (v + t) := by
    simp only [map_add, ne_eq, add_right_inj]
    exact ne_of_gt hts
  have hb := hgap (v + t) hlink (v + s) hcloud hneq
  simpa only [map_add, add_sub_add_left_eq_sub, abs_of_pos (sub_pos.mpr hts)] using hb

private theorem oneSided_component_centresMinimum
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ) (hδ : Module.finrank ℝ δ = 1) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ) (htile : TilesOn K T Set.univ)
    (P : EarthquakeComponent K δ T)
    (hbound : ∃ a : ℝ, ∀ s ∈ P.centres, a ≤ ℓ s) :
    ∃ t ∈ P.centres, ∀ s ∈ P.centres, ℓ t ≤ ℓ s := by
  have hsubset : P.centres ⊆ T := by
    rintro s ⟨t, _, rfl⟩
    exact t.2
  have hp : IsPacking K.prototileFamily (K.placements P.centres) := by
    intro p hp q hq hpq
    exact htile.2.1 (hsubset hp) (hsubset hq) hpq
  have hwhole : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hwholeInv : IsInvariantAlong (regularSupport K T) δ := by
    rw [hwhole]
    intro u _
    exact Set.vadd_set_univ
  have hinv := component_isInvariant K δ T hδ htile.2.1 hwholeInv P
  exact invariantPacking_centresMinimum (P.nonempty_supp.image Subtype.val)
    hp hinv ℓ hℓ hker hbound

private theorem intrinsic_minimumVertex
    (K : PolygonalRegion) (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ∃ v ∈ vertexSet K.support, ∀ z ∈ K.support, ℓ v ≤ ℓ z := by
  obtain ⟨k, hk, hkmin⟩ := K.isPolygonal.isCompact.exists_isMinOn K.nonempty ℓ.continuous.continuousOn
  have hℓlin : ℓ.toLinearMap ≠ 0 := by
    intro hzero
    apply hℓ
    ext x
    exact DFunLike.congr_fun hzero x
  have hkUnion : k ∈ ⋃ O ∈ interiorComponents K.support, closure O := by
    rw [K.isPolygonal.iUnion_closure_interiorComponents]
    exact hk
  obtain ⟨O, hO, hkO⟩ := Set.mem_iUnion₂.mp hkUnion
  obtain ⟨v, hv, _, hvmin, _⟩ :=
    K.isPolygonal.exists_interiorComponent_min_vertex hO ℓ.toLinearMap hℓlin
  refine ⟨v, hv, ?_⟩
  intro z hz
  exact (hvmin k hkO).trans (hkmin hz)

private theorem openSet_hasLowerFunctionalPoint
    {D : Set Plane} (hD : IsOpen D) {x : Plane} (hx : x ∈ D)
    (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ∃ y ∈ D, ℓ y < ℓ x := by
  obtain ⟨w, hw⟩ := nonzeroFunctional_surjective ℓ hℓ (1 : ℝ)
  let f : ℝ → Plane := fun r => x - r • w
  have hf : Continuous f := continuous_const.sub (continuous_id.smul continuous_const)
  have hpre : f ⁻¹' D ∈ 𝓝 (0 : ℝ) := by
    apply hf.continuousAt
    simpa [f] using hD.mem_nhds hx
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  have hhalf : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  refine ⟨f (ε / 2), hεsub hhalf, ?_⟩
  change ℓ (x - (ε / 2) • w) < ℓ x
  rw [map_sub, map_smul, hw, smul_eq_mul, mul_one]
  linarith

private theorem intrinsicVertex_mem_support
    {K : PolygonalRegion} {v : Plane} (hv : v ∈ vertexSet K.support) :
    v ∈ K.support := by
  obtain ⟨triangulation⟩ := K.isPolygonal
  obtain ⟨f, hf, hvf⟩ := hv triangulation
  rw [← triangulation.sUnion_eq]
  exact Set.mem_sUnion.mpr ⟨f, hf, extremePoints_subset hvf⟩

private theorem minimumFibre_extremalProperLink
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T S : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ) (htile : TilesOn K T Set.univ)
    (hST : S ⊆ T) (hinv : IsInvariantAlong (regularSupport K S) δ)
    (t : Plane) (ht : t ∈ S) (hminT : ∀ s ∈ S, ℓ t ≤ ℓ s)
    (v : Plane) (hv : v ∈ K.support) (hminK : ∀ z ∈ K.support, ℓ v ≤ ℓ z) :
    IsProperLink K δ T (v + t) := by
  have hp : IsPacking K.prototileFamily (K.placements S) := by
    intro p hp q hq hpq
    exact htile.2.1 (hST hp) (hST hq) hpq
  have hsupp := closure_regularSupport_eq_supportUnion hp
  have hraw : closure (openUnion K S) = closure (regularSupport K S) := by
    rw [closure_openUnion_eq_iUnion_support hp, hsupp]
  have hclosedInv : IsInvariantAlong (closure (regularSupport K S)) δ := by
    intro u hu
    rw [← closure_vadd]
    exact congrArg closure (hinv u hu)
  have hbase : v + t ∈ closure (regularSupport K S) := by
    rw [hsupp]
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, by simpa [add_comm] using Set.vadd_mem_vadd_set (a := t) hv⟩
  have hbound : ∀ y ∈ closure (regularSupport K S), ℓ (v + t) ≤ ℓ y := by
    intro y hy
    rw [hsupp] at hy
    obtain ⟨s, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
    change ℓ (v + t) ≤ ℓ ((s : Plane) + z)
    rw [map_add, map_add]
    linarith [hminT s s.2, hminK z hz]
  have hcover : (⋃ s : T, (s : Plane) +ᵥ K.support) = Set.univ := by
    rw [← closure_regularSupport_eq_supportUnion htile.2.1,
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile, closure_univ]
  change (v + t) +ᵥ (δ : Set Plane) ⊆ ⋃ s : T, (s : Plane) +ᵥ frontier K.support
  intro x hx
  obtain ⟨u, hu, hux⟩ := hx
  change (v + t) + u = x at hux
  have hxclosure : x ∈ closure (regularSupport K S) := by
    rw [← hux, add_comm (v + t) u, ← hclosedInv u hu]
    exact Set.vadd_mem_vadd_set hbase
  have hxval : ℓ x = ℓ (v + t) := by
    rw [← hux]
    have hu0 : ℓ u = 0 := by
      change u ∈ LinearMap.ker ℓ.toLinearMap
      rwa [hker]
    rw [map_add, hu0, add_zero]
  have hxnoInterior : ∀ s ∈ T, x ∉ s +ᵥ K.openCarrier := by
    intro s hs hxs
    by_cases hsS : s ∈ S
    · obtain ⟨y, hy, hlt⟩ := openSet_hasLowerFunctionalPoint
        (isOpen_interior.vadd s) hxs ℓ hℓ
      obtain ⟨z, hz, rfl⟩ := hy
      have hyclosure : s + z ∈ closure (regularSupport K S) := by
        rw [hsupp]
        exact Set.mem_iUnion.mpr ⟨⟨s, hsS⟩, Set.vadd_mem_vadd_set (interior_subset hz)⟩
      have hb := hbound (s + z) hyclosure
      change ℓ (s + z) < ℓ x at hlt
      rw [hxval] at hlt
      linarith
    · have hd : Disjoint (s +ᵥ K.openCarrier) (openUnion K S) := by
        rw [Set.disjoint_left]
        intro y hy hys
        obtain ⟨r, hyr⟩ := Set.mem_iUnion.mp hys
        have hsr : s ≠ (r : Plane) := fun heq => hsS (heq.symm ▸ r.2)
        exact Set.disjoint_left.mp
          ((isPacking_iff_openCarrier_disjoint K T).mp htile.2.1 hs (hST r.2) hsr) hy hyr
      have hdcl := hd.closure_right (isOpen_interior.vadd s)
      rw [hraw] at hdcl
      exact Set.disjoint_left.mp hdcl hxs hxclosure
  have hxcovered : x ∈ ⋃ s : T, (s : Plane) +ᵥ K.support := by rw [hcover]; trivial
  obtain ⟨s, y, hy, hsy⟩ := Set.mem_iUnion.mp hxcovered
  have hyfrontier : y ∈ frontier K.support := by
    rw [frontier, K.isPolygonal.isClosed.closure_eq]
    refine ⟨hy, ?_⟩
    intro hyinterior
    apply hxnoInterior s s.2
    rw [← hsy]
    exact Set.vadd_mem_vadd_set hyinterior
  exact Set.mem_iUnion.mpr ⟨s, ⟨y, hyfrontier, hsy⟩⟩

private theorem frontier_vadd_eq (u : Plane) (D : Set Plane) :
    frontier (u +ᵥ D) = u +ᵥ frontier D := by
  rw [frontier, closure_vadd, interior_vadd]
  ext z
  simp only [frontier, Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem]

/-- Every genuine frontier point of a saturated subfamily lies on an ambient
proper link. Packing excludes interior owners on both sides of its boundary. -/
private theorem invariantCarrier_frontier_isProperLink
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T S : Set Plane)
    (htile : TilesOn K T Set.univ) (hST : S ⊆ T)
    (hinv : IsInvariantAlong (regularSupport K S) δ)
    (a : Plane) (ha : a ∈ frontier (regularSupport K S)) : IsProperLink K δ T a := by
  have hp : IsPacking K.prototileFamily (K.placements S) := by
    intro s hs t ht hst
    exact htile.2.1 (hST hs) (hST ht) hst
  have hraw : closure (openUnion K S) = closure (regularSupport K S) := by
    rw [closure_openUnion_eq_iUnion_support hp,
      closure_regularSupport_eq_supportUnion hp]
  have hfrontierInv : IsInvariantAlong (frontier (regularSupport K S)) δ := by
    intro u hu
    rw [← frontier_vadd_eq, hinv u hu]
  have hcover : (⋃ s : T, (s : Plane) +ᵥ K.support) = Set.univ := by
    rw [← closure_regularSupport_eq_supportUnion htile.2.1,
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile, closure_univ]
  intro x hx
  obtain ⟨u, hu, hux⟩ := hx
  change a + u = x at hux
  have hxfrontier : x ∈ frontier (regularSupport K S) := by
    rw [← hux, add_comm a u, ← hfrontierInv u hu]
    exact Set.vadd_mem_vadd_set ha
  have hxclosure : x ∈ closure (regularSupport K S) := frontier_subset_closure hxfrontier
  have hxnoInterior : ∀ s ∈ T, x ∉ s +ᵥ K.openCarrier := by
    intro s hs hxs
    by_cases hsS : s ∈ S
    · have hopen : IsOpen (openUnion K S) :=
        isOpen_iUnion fun r : S => isOpen_interior.vadd (r : Plane)
      have hxraw : x ∈ openUnion K S := Set.mem_iUnion.mpr ⟨⟨s, hsS⟩, hxs⟩
      have hxreg : x ∈ regularSupport K S := hopen.subset_interior_closure hxraw
      exact Set.disjoint_left.mp disjoint_interior_frontier
        (by simpa only [regularSupport, interior_interior] using hxreg) hxfrontier
    · have hd : Disjoint (s +ᵥ K.openCarrier) (openUnion K S) := by
        rw [Set.disjoint_left]
        intro y hy hys
        obtain ⟨r, hyr⟩ := Set.mem_iUnion.mp hys
        have hsr : s ≠ (r : Plane) := fun heq => hsS (heq.symm ▸ r.2)
        exact Set.disjoint_left.mp
          ((isPacking_iff_openCarrier_disjoint K T).mp htile.2.1 hs (hST r.2) hsr) hy hyr
      have hdcl := hd.closure_right (isOpen_interior.vadd s)
      rw [hraw] at hdcl
      exact Set.disjoint_left.mp hdcl hxs hxclosure
  have hxcovered : x ∈ ⋃ s : T, (s : Plane) +ᵥ K.support := by rw [hcover]; trivial
  obtain ⟨s, y, hy, hsy⟩ := Set.mem_iUnion.mp hxcovered
  have hyfrontier : y ∈ frontier K.support := by
    rw [frontier, K.isPolygonal.isClosed.closure_eq]
    refine ⟨hy, ?_⟩
    intro hyinterior
    apply hxnoInterior s s.2
    rw [← hsy]
    exact Set.vadd_mem_vadd_set hyinterior
  exact Set.mem_iUnion.mpr ⟨s, ⟨y, hyfrontier, hsy⟩⟩

/-- A genuine transverse period of a nonempty subfamily frontier constructs
uniformly nearby ambient links by integer reduction, rather than assuming a
readiness certificate. -/
private theorem invariantCarrier_transversePeriod_uniformlyReady
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T S : Set Plane)
    (htile : TilesOn K T Set.univ) (hST : S ⊆ T)
    (hinv : IsInvariantAlong (regularSupport K S) δ)
    (hfrontier : (frontier (regularSupport K S)).Nonempty)
    (ℓ : Plane →L[ℝ] ℝ) (hker : LinearMap.ker ℓ.toLinearMap = δ)
    (q : Plane) (hqδ : q ∉ δ) (hqperiod : q ∈ periodGroup (regularSupport K S)) :
    IsUniformlyReady K δ T := by
  obtain ⟨a, ha⟩ := hfrontier
  have hqeval : ℓ q ≠ 0 := by
    intro h
    apply hqδ
    rw [← hker]
    exact h
  have hfrontierInv : IsInvariantAlong (frontier (regularSupport K S)) δ := by
    intro u hu
    rw [← frontier_vadd_eq, hinv u hu]
  refine ⟨‖q‖ + 1, by positivity, ?_⟩
  intro z
  let c : ℝ := ℓ (z - a) / ℓ q
  let n : ℤ := ⌊c⌋
  let u : Plane := z - a - c • q
  have hu : u ∈ δ := by
    rw [← hker]
    change ℓ (z - a - c • q) = 0
    simp only [map_sub, map_smul, smul_eq_mul]
    dsimp [c]
    rw [div_mul_cancel₀ _ hqeval, map_sub]
    ring
  let b : Plane := u + (n • q + a)
  have hnperiod : (n • q) +ᵥ regularSupport K S = regularSupport K S :=
    AddAction.mem_stabilizer_iff.mp ((periodGroup (regularSupport K S)).zsmul_mem hqperiod n)
  have hnfrontier : (n • q) +ᵥ frontier (regularSupport K S) =
      frontier (regularSupport K S) := by rw [← frontier_vadd_eq, hnperiod]
  have hbfrontier : b ∈ frontier (regularSupport K S) := by
    have hna : n • q + a ∈ frontier (regularSupport K S) := by
      rw [← hnfrontier]
      exact Set.vadd_mem_vadd_set ha
    rw [show b = u + (n • q + a) from rfl, ← hfrontierInv u hu]
    exact Set.vadd_mem_vadd_set hna
  refine ⟨b, invariantCarrier_frontier_isProperLink K δ T S htile hST hinv b hbfrontier, ?_⟩
  have hdiff : z - b = (c - (n : ℝ)) • q := by
    change z - (z - a - c • q + (n • q + a)) = (c - (n : ℝ)) • q
    rw [← Int.cast_smul_eq_zsmul ℝ, sub_smul]
    abel
  have hlow : 0 ≤ c - (n : ℝ) := sub_nonneg.mpr (Int.floor_le c)
  have hhigh : c - (n : ℝ) < 1 := by
    change c - (⌊c⌋ : ℝ) < 1
    linarith [Int.lt_floor_add_one c]
  rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlow]
  have hbound : (c - (n : ℝ)) * ‖q‖ ≤ ‖q‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hhigh.le (norm_nonneg q)
  linarith

private theorem intrinsicMinimum_initialProjectionInterval
    (K : PolygonalRegion) (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (v : Plane) (hv : v ∈ vertexSet K.support)
    (hminK : ∀ z ∈ K.support, ℓ v ≤ ℓ z) :
    ∃ r : ℝ, 0 < r ∧ ∀ a : ℝ, ℓ v < a → a < ℓ v + r →
      ∃ z ∈ K.openCarrier, ℓ z = a := by
  obtain ⟨triangulation⟩ := K.isPolygonal
  obtain ⟨f, hf, hvf⟩ := hv triangulation
  have hfK : f ⊆ K.support := by
    intro x hx
    rw [← triangulation.sUnion_eq]
    exact Set.mem_sUnion.mpr ⟨f, hf, hx⟩
  have htriangle := triangulation.isTriangle f hf
  have hconvex : Convex ℝ f := by
    obtain ⟨a, b, c, _, rfl⟩ := htriangle
    exact convex_convexHull ℝ _
  obtain ⟨q, hq⟩ := htriangle.interior_nonempty
  have hvf' : v ∈ f := extremePoints_subset hvf
  have hqstrict : ℓ v < ℓ q := by
    by_contra h
    obtain ⟨z, hz, hzlt⟩ := openSet_hasLowerFunctionalPoint isOpen_interior hq ℓ hℓ
    have hminz := hminK z (hfK (interior_subset hz))
    have hqle : ℓ q ≤ ℓ v := le_of_not_gt h
    linarith
  refine ⟨ℓ q - ℓ v, sub_pos.mpr hqstrict, ?_⟩
  intro a ha hqa
  have hD : 0 < ℓ q - ℓ v := sub_pos.mpr hqstrict
  let θ : ℝ := (a - ℓ v) / (ℓ q - ℓ v)
  have hθpos : 0 < θ := div_pos (sub_pos.mpr ha) hD
  have hθlt : θ < 1 := by
    apply (div_lt_one hD).mpr
    linarith
  let z : Plane := (1 - θ) • v + θ • q
  have hzsegment : z ∈ openSegment ℝ v q :=
    ⟨1 - θ, θ, sub_pos.mpr hθlt, hθpos, by ring, rfl⟩
  have hz : z ∈ K.openCarrier :=
    interior_mono hfK (hconvex.openSegment_self_interior_subset_interior hvf' hq hzsegment)
  refine ⟨z, hz, ?_⟩
  change ℓ ((1 - θ : ℝ) • v + θ • q) = a
  rw [map_add, map_smul, map_smul]
  change (1 - θ) * ℓ v + θ * ℓ q = a
  dsimp [θ]
  field_simp
  ring

theorem oneSided_minimumFibre_collar :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ), Module.finrank ℝ δ = 1 → ℓ ≠ 0 →
    LinearMap.ker ℓ.toLinearMap = δ → TilesOn K T Set.univ →
      ∀ P : EarthquakeComponent K δ T,
        (∃ a : ℝ, ∀ s ∈ P.centres, a ≤ ℓ s) →
          ∃ t ∈ P.centres, ∃ v ∈ vertexSet K.support,
            (∀ s ∈ P.centres, ℓ t ≤ ℓ s) ∧
            (∀ z ∈ K.support, ℓ v ≤ ℓ z) ∧ IsProperLink K δ T (v + t) ∧
              ∃ c : ℝ, 0 < c ∧ ∀ x : Plane,
                ℓ (v + t) < ℓ x → ℓ x < ℓ (v + t) + c →
                  ∃ s ∈ lineFibre δ P.centres t, x ∈ s +ᵥ K.support
  := by
  intro K δ T ℓ hδ hℓ hker htile P hbound
  obtain ⟨t, ht, hminT⟩ :=
    oneSided_component_centresMinimum K δ T ℓ hδ hℓ hker htile P hbound
  obtain ⟨v, hv, hminK⟩ := intrinsic_minimumVertex K ℓ hℓ
  have hsubset : P.centres ⊆ T := by
    rintro s ⟨u, _, rfl⟩
    exact u.2
  have hp : IsPacking K.prototileFamily (K.placements P.centres) := by
    intro p hp q hq hpq
    exact htile.2.1 (hsubset hp) (hsubset hq) hpq
  have hwhole : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hwholeInv : IsInvariantAlong (regularSupport K T) δ := by
    rw [hwhole]
    intro u _
    exact Set.vadd_set_univ
  have hinv := component_isInvariant K δ T hδ htile.2.1 hwholeInv P
  change IsInvariantAlong (regularSupport K P.centres) δ at hinv
  have hlink := minimumFibre_extremalProperLink K δ T P.centres ℓ hℓ hker
    htile hsubset hinv t ht hminT v (intrinsicVertex_mem_support hv) hminK
  obtain ⟨c₀, hc₀, hgap⟩ := minimumFibre_transverseGap K δ T ℓ hδ hℓ hker htile t v hv hlink
  obtain ⟨r, hr, hprojection⟩ := intrinsicMinimum_initialProjectionInterval K ℓ hℓ v hv hminK
  refine ⟨t, ht, v, hv, hminT, hminK, hlink, min r c₀, lt_min hr hc₀, ?_⟩
  intro x hlow hupp
  have haLow : ℓ v < ℓ x - ℓ t := by
    rw [map_add] at hlow
    linarith
  have haUpp : ℓ x - ℓ t < ℓ v + r := by
    rw [map_add] at hupp
    linarith [min_le_left r c₀]
  obtain ⟨z, hz, hzval⟩ := hprojection (ℓ x - ℓ t) haLow haUpp
  have htz : t + z ∈ regularSupport K P.centres := by
    apply (isOpen_iUnion fun s : P.centres => isOpen_interior.vadd (s : Plane)).subset_interior_closure
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, Set.vadd_mem_vadd_set hz⟩
  have hshift : x - (t + z) ∈ δ := by
    rw [← hker]
    change ℓ (x - (t + z)) = 0
    rw [map_sub, map_add, hzval]
    ring
  have hxcarrier : x ∈ regularSupport K P.centres := by
    have h := Set.vadd_mem_vadd_set (a := x - (t + z)) htz
    rw [hinv _ hshift] at h
    simpa using h
  have hxclosure := subset_closure hxcarrier
  rw [closure_regularSupport_eq_supportUnion hp] at hxclosure
  obtain ⟨s, y, hy, hsy⟩ := Set.mem_iUnion.mp hxclosure
  change (s : Plane) + y = x at hsy
  have hsval : ℓ (s : Plane) = ℓ t := by
    by_contra hne
    have hts : ℓ t < ℓ s := lt_of_le_of_ne (hminT s s.2) (Ne.symm hne)
    have hgs := hgap s (hsubset s.2) hts
    have hky := hminK y hy
    have hxval : ℓ x = ℓ s + ℓ y := by rw [← hsy, map_add]
    rw [map_add] at hupp
    linarith [min_le_right r c₀]
  have hsfibre : (s : Plane) ∈ lineFibre δ P.centres t := by
    refine ⟨s.2, ?_⟩
    have hs0 : (s : Plane) - t ∈ LinearMap.ker ℓ.toLinearMap := by
      change ℓ ((s : Plane) - t) = 0
      rw [map_sub, hsval, sub_self]
    exact hker ▸ hs0
  exact ⟨s, hsfibre, ⟨y, hy, hsy⟩⟩

private theorem scalarFLC_of_lineSupport
    {S : Set Plane} {δ : Submodule ℝ Plane} {anchor : Plane}
    (hline : ∀ x ∈ S, x - anchor ∈ δ)
    (f : Plane →L[ℝ] ℝ)
    (hkernel : ∀ x ∈ δ, f x = 0 → x = 0)
    (himage : Tiling.Polygonal.HasFLC (f '' S)) :
    Tiling.Polygonal.HasFLC S := by
  constructor
  · intro Q hQ
    have hQimage : Bornology.IsBounded (f '' Q) := f.lipschitz.isBounded_image hQ
    have himageFinite : (f '' S ∩ f '' Q).Finite := himage.1 _ hQimage
    have hlocalImage : (f '' (S ∩ Q)).Finite := himageFinite.subset (by
      rintro y ⟨x, ⟨hxS, hxQ⟩, rfl⟩
      exact ⟨⟨x, hxS, rfl⟩, ⟨x, hxQ, rfl⟩⟩)
    apply Set.Finite.of_finite_image hlocalImage
    intro x hx y hy hxy
    have hδxy : x - y ∈ δ := by
      have hxδ := hline x hx.1
      have hyδ := hline y hy.1
      have hsub : (x - anchor) - (y - anchor) ∈ δ := δ.sub_mem hxδ hyδ
      simpa [sub_sub_sub_cancel_right] using hsub
    have hzero : f (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hxyzero := hkernel (x - y) hδxy hzero
    exact sub_eq_zero.mp hxyzero
  · intro R hR
    let D : Set Plane := (S - S) ∩ Metric.closedBall 0 R
    let R' : ℝ := (‖f‖ + 1) * R
    have hR' : 0 < R' := by dsimp [R']; positivity
    have himageFinite : ((f '' S - f '' S) ∩ Metric.closedBall 0 R').Finite :=
      himage.2 R' hR'
    have hdiffImage : (f '' D).Finite := himageFinite.subset (by
      rintro y ⟨d, ⟨hdiff, hdBound⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨x, hxS, z, hzS, rfl⟩ := Set.mem_sub.mp hdiff
        exact Set.mem_sub.mpr ⟨f x, ⟨x, hxS, rfl⟩, f z, ⟨z, hzS, rfl⟩, by simp⟩
      · rw [Metric.mem_closedBall]
        have hnorm : ‖f d‖ ≤ ‖f‖ * ‖d‖ := f.le_opNorm d
        have hd : ‖d‖ ≤ R := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hdBound
        have hbound : ‖f‖ * ‖d‖ ≤ (‖f‖ + 1) * R := by
          nlinarith [norm_nonneg f, mul_nonneg (norm_nonneg f) hR.le]
        simpa only [dist_zero_right] using hnorm.trans hbound)
    apply Set.Finite.of_finite_image hdiffImage
    intro x hx y hy hxy
    have hδx : x ∈ δ := by
      obtain ⟨a, haS, b, hbS, rfl⟩ := Set.mem_sub.mp hx.1
      have h := δ.sub_mem (hline a haS) (hline b hbS)
      simpa [sub_sub_sub_cancel_right] using h
    have hδy : y ∈ δ := by
      obtain ⟨a, haS, b, hbS, rfl⟩ := Set.mem_sub.mp hy.1
      have h := δ.sub_mem (hline a haS) (hline b hbS)
      simpa [sub_sub_sub_cancel_right] using h
    have hδxy := δ.sub_mem hδx hδy
    have hzero : f (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hxyzero := hkernel (x - y) hδxy hzero
    exact sub_eq_zero.mp hxyzero

private theorem scalarLineTiles_hasFLC
    {B L : Set ℝ}
    (hB : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion B)
    (hpos : 0 < (MeasureTheory.volume B).toReal)
    (htile : Tiling.AxisParallel.OneDimensional.LineTiles B L) :
    Tiling.Polygonal.HasFLC L := by
  let P := Tiling.AxisParallel.OneDimensional.FiniteInterval.IntervalPresentation.ofIsFiniteIntervalRegion hB
  obtain ⟨δ, hδ, hseparated, hclosed, hlocal, hcountable⟩ :=
    Tiling.AxisParallel.Foundations.linePacking_uniformlySeparated htile
      P.volume_ne_top hpos
  constructor
  · exact hlocal
  · intro R hR
    obtain ⟨F, hF⟩ :=
      Tiling.AxisParallel.OneDimensional.FiniteInterval.finite_centerCandidates
        P hpos R (le_of_lt hR)
    apply F.finite_toSet.subset
    intro d hd
    obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_sub.mp hd.1
    have hnormalizedTile : Tiling.AxisParallel.OneDimensional.LineTiles B ((-t) +ᵥ L) := by
      simpa [Tiling.AxisParallel.OneDimensional.LineTiles] using
        Tiling.AxisParallel.Foundations.lineTilesOn_translate htile (-t)
    have hzero : 0 ∈ (-t) +ᵥ L := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [neg_neg] using ht
    have hdcenter : s - t ∈ (-t) +ᵥ L := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg]
      change t + (s - t) ∈ L
      simpa using hs
    have hdinterval : s - t ∈ Set.Icc (-R) R := by
      have hnorm : ‖s - t‖ ≤ R := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hd.2
      have habs : |s - t| ≤ R := by simpa only [Real.norm_eq_abs] using hnorm
      exact abs_le.mp habs
    exact hF _ hnormalizedTile hzero ⟨hdcenter, hdinterval⟩

private theorem initialFibre_polygonalClosedSection (K : PolygonalRegion)
    (k u : Plane) (hu : u ≠ 0) :
    ∃ (n : ℕ) (a b : Fin n → ℝ), (∀ i, a i ≤ b i) ∧
      {r : ℝ | k + r • u ∈ K.support} = ⋃ i, Set.Icc (a i) (b i) := by
  classical
  obtain ⟨F⟩ := K.isPolygonal
  let f : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap k (k + u)
  have hf (r : ℝ) : f r = k + r • u := by
    simp [f, AffineMap.lineMap_apply_module', add_comm]
  have hfclosed : Topology.IsClosedEmbedding f := by
    have hsmul : Topology.IsClosedEmbedding (fun r : ℝ => r • u) := isClosedEmbedding_smul_left hu
    have h := (Homeomorph.addLeft k).isClosedEmbedding.comp hsmul
    convert h using 1
    funext r
    exact hf r
  let J := {t : {t : Set Plane // t ∈ F.pieces} // (f ⁻¹' t.1).Nonempty}
  have hpresentation (j : J) : ∃ a b : ℝ, a ≤ b ∧ f ⁻¹' j.1.1 = Set.Icc a b := by
    have htriangle := F.isTriangle j.1.1 j.1.2
    have hcompact := hfclosed.isCompact_preimage htriangle.isCompact
    have hconvex : Convex ℝ j.1.1 := by
      obtain ⟨a, b, c, _, heq⟩ := htriangle
      rw [heq]
      exact convex_convexHull ℝ _
    have hconnected : IsConnected (f ⁻¹' j.1.1) :=
      ⟨j.2, (hconvex.affine_preimage f).isPreconnected⟩
    refine ⟨sInf (f ⁻¹' j.1.1), sSup (f ⁻¹' j.1.1), ?_,
      eq_Icc_of_connected_compact hconnected hcompact⟩
    exact (hcompact.isLeast_sInf j.2).2 (hcompact.sSup_mem j.2)
  choose a b hab heq using hpresentation
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, a ∘ e, b ∘ e, fun i => hab (e i), ?_⟩
  ext r
  constructor
  · intro hr
    have hrF : f r ∈ ⋃₀ (F.pieces : Set (Set Plane)) := by
      rw [F.sUnion_eq, hf]
      exact hr
    obtain ⟨t, ht, hrt⟩ := Set.mem_sUnion.mp hrF
    let j : J := ⟨⟨t, ht⟩, ⟨r, hrt⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨e.symm j, ?_⟩
    change r ∈ Set.Icc (a (e (e.symm j))) (b (e (e.symm j)))
    rw [e.apply_symm_apply, ← heq j]
    exact hrt
  · intro hr
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hr
    have hri : f r ∈ (e i).1.1 := by
      change r ∈ f ⁻¹' (e i).1.1
      rw [heq (e i)]
      exact hi
    change k + r • u ∈ K.support
    rw [← hf, ← F.sUnion_eq]
    exact Set.mem_sUnion.mpr ⟨(e i).1.1, (e i).1.2, hri⟩

/-- A noncritical affine section meets each intrinsic boundary edge at most once.
This is the finite exceptional set needed for actual one-dimensional coverage. -/
private theorem polygonal_noncriticalSection_boundaryFinite
    (K : PolygonalRegion) (ℓ : Plane →L[ℝ] ℝ) (k e : Plane)
    (he : e ≠ 0) (hℓe : ℓ e = 0)
    (hcritical : ℓ k ∉ ℓ '' vertexSet K.support) :
    {r : ℝ | k + r • e ∈ frontier K.support}.Finite := by
  classical
  obtain ⟨F, hF, hboundary⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  have hsegment (a b : Plane) (ha : a ∈ vertexSet K.support)
      (hb : b ∈ vertexSet K.support) :
      {r : ℝ | k + r • e ∈ segment ℝ a b}.Finite := by
    apply Set.Subsingleton.finite
    intro r hr s hs
    rw [segment_eq_image_lineMap] at hr hs
    obtain ⟨u, _, hu⟩ := hr
    obtain ⟨v, _, hv⟩ := hs
    have hline (q : ℝ) : ℓ (k + q • e) = ℓ k := by
      rw [map_add, map_smul, hℓe, smul_zero, add_zero]
    have huℓ := congrArg ℓ hu
    have hvℓ := congrArg ℓ hv
    rw [AffineMap.lineMap_apply_module] at huℓ hvℓ
    simp only [map_add, map_smul, smul_eq_mul, hline] at huℓ hvℓ
    have hab : ℓ a ≠ ℓ b := by
      intro hab
      have hak : ℓ a = ℓ k := by rw [hab] at huℓ; nlinarith
      exact hcritical ⟨a, ha, hak⟩
    have huv : u = v := by
      have hdiff : (u - v) * (ℓ b - ℓ a) = 0 := by nlinarith [huℓ, hvℓ]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right (sub_ne_zero.mpr hab.symm))
    have hrs : k + r • e = k + s • e := by rw [← hu, ← hv, huv]
    exact smul_left_injective ℝ he (add_left_cancel hrs)
  have hfinite : (⋃ q ∈ F, {r : ℝ | k + r • e ∈ segment ℝ q.1 q.2}).Finite :=
    F.finite_toSet.biUnion fun q hq => hsegment q.1 q.2 (hF q hq).2.1 (hF q hq).2.2.1
  apply hfinite.subset
  intro r hr
  change k + r • e ∈ frontier K.support at hr
  rw [hboundary, Set.mem_iUnion] at hr
  obtain ⟨q, hq⟩ := hr
  rw [Set.mem_iUnion] at hq
  obtain ⟨hqF, hrq⟩ := hq
  exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hqF, hrq⟩⟩

private theorem polygonal_noncriticalOpenSection_frontierFinite
    (K : PolygonalRegion) (ℓ : Plane →L[ℝ] ℝ) (k e : Plane)
    (he : e ≠ 0) (hℓe : ℓ e = 0)
    (hcritical : ℓ k ∉ ℓ '' vertexSet K.support) :
    (frontier {r : ℝ | k + r • e ∈ K.openCarrier}).Finite := by
  have hcont : Continuous (fun r : ℝ => k + r • e) := by fun_prop
  have hfinite := polygonal_noncriticalSection_boundaryFinite K ℓ k e he hℓe hcritical
  apply hfinite.subset
  intro r hr
  have h := hcont.frontier_preimage_subset K.openCarrier hr
  change k + r • e ∈ frontier K.openCarrier at h
  exact frontier_interior_subset h

/-- Exact collar coverage and finitely many section-boundary points give a
genuine whole-line measure tiling by the open polygonal section. -/
private theorem collarSection_actualLineTiles
    (K : PolygonalRegion) (S : Set Plane) (t k e : Plane)
    (he : e ≠ 0) (hS : S.Countable)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : ∀ s ∈ S, ∃ q : ℝ, s = t + q • e)
    (hboundary : {r : ℝ | k + r • e ∈ frontier K.support}.Finite)
    (hcover : ∀ r : ℝ, ∃ s ∈ S, t + k + r • e ∈ s +ᵥ K.support) :
    Tiling.AxisParallel.OneDimensional.LineTiles
      {r : ℝ | k + r • e ∈ K.openCarrier}
      {q : ℝ | t + q • e ∈ S} := by
  let B : Set ℝ := {r | k + r • e ∈ K.openCarrier}
  let L : Set ℝ := {q | t + q • e ∈ S}
  let E : Set ℝ := L + {r : ℝ | k + r • e ∈ frontier K.support}
  have hL : L.Countable := hS.preimage (by
    intro r s hrs
    exact smul_left_injective ℝ he (add_left_cancel hrs))
  have hE : E.Countable := hL.image2 hboundary.countable (· + ·)
  have hcont : Continuous (fun r : ℝ => k + r • e) := by fun_prop
  have hBopen : IsOpen B := isOpen_interior.preimage hcont
  have hplaced {q r : ℝ} (hr : r ∈ q +ᵥ B) :
      t + k + r • e ∈ (t + q • e) +ᵥ K.openCarrier := by
    obtain ⟨z, hz, hzr⟩ := hr
    change q + z = r at hzr
    refine ⟨k + z • e, hz, ?_⟩
    change t + q • e + (k + z • e) = t + k + r • e
    rw [← hzr, add_smul]
    abel
  refine ⟨hBopen.measurableSet, MeasurableSet.univ, hL, ?_, ?_⟩
  · intro q hq u hu hqu
    have hcentres : t + q • e ≠ t + u • e := by
      intro heq
      exact hqu (smul_left_injective ℝ he (add_left_cancel heq))
    have hdisj := (isPacking_iff_openCarrier_disjoint K S).mp hp hq hu hcentres
    have hreal : Disjoint (q +ᵥ B) (u +ᵥ B) := by
      rw [Set.disjoint_left]
      intro r hrq hru
      exact Set.disjoint_left.mp hdisj (hplaced hrq) (hplaced hru)
    exact hreal.aedisjoint
  · have havoid : ∀ᵐ r : ℝ ∂volume, r ∉ E := by
      rw [ae_iff]
      simpa using hE.measure_zero volume
    filter_upwards [havoid] with r hrE
    constructor
    · intro _
      obtain ⟨s, hs, z, hz, hsz⟩ := hcover r
      obtain ⟨q, hsq⟩ := hline s hs
      have hq : q ∈ L := by change t + q • e ∈ S; rw [← hsq]; exact hs
      have hzEq : z = k + (r - q) • e := by
        change s + z = t + k + r • e at hsz
        rw [hsq] at hsz
        rw [sub_smul]
        linear_combination hsz
      have hzInterior : z ∈ K.openCarrier := by
        by_contra hn
        have hfront : z ∈ frontier K.support := by
          rw [frontier, K.isPolygonal.isClosed.closure_eq]
          exact ⟨hz, hn⟩
        apply hrE
        exact Set.mem_add.mpr ⟨q, hq, r - q, by
          change k + (r - q) • e ∈ frontier K.support
          rw [← hzEq]; exact hfront,
          by ring⟩
      refine ⟨⟨q, hq⟩, ?_⟩
      refine ⟨r - q, ?_, ?_⟩
      · change k + (r - q) • e ∈ K.openCarrier
        rw [← hzEq]
        exact hzInterior
      · change q + (r - q) = r
        ring
    · intro _
      trivial

private theorem collarSection_regularizedLineTiles
    (K : PolygonalRegion) (S : Set Plane) (t k e : Plane)
    (he : e ≠ 0) (hS : S.Countable)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : ∀ s ∈ S, ∃ q : ℝ, s = t + q • e)
    (hboundary : {r : ℝ | k + r • e ∈ frontier K.support}.Finite)
    (hcover : ∀ r : ℝ, ∃ s ∈ S, t + k + r • e ∈ s +ᵥ K.support) :
    Tiling.AxisParallel.OneDimensional.LineTiles
      (interior {r : ℝ | k + r • e ∈ K.support})
      {q : ℝ | t + q • e ∈ S} := by
  have ht := collarSection_actualLineTiles K S t k e he hS hp hline hboundary hcover
  let B : Set ℝ := {r | k + r • e ∈ K.openCarrier}
  let C : Set ℝ := {r | k + r • e ∈ K.support}
  have hcont : Continuous (fun r : ℝ => k + r • e) := by fun_prop
  have hBopen : IsOpen B := isOpen_interior.preimage hcont
  have hBsub : B ⊆ interior C := by
    apply hBopen.subset_interior_iff.mpr
    intro r hr
    change k + r • e ∈ K.openCarrier at hr
    change k + r • e ∈ K.support
    exact interior_subset hr
  have havoid : ∀ᵐ r : ℝ ∂volume, k + r • e ∉ frontier K.support := by
    rw [ae_iff]
    simpa using hboundary.measure_zero volume
  have hBB' : B =ᵐ[volume] interior C := by
    filter_upwards [havoid] with r hr
    apply propext
    constructor
    · intro hrB
      exact hBsub hrB
    · intro hri
      have hC := interior_subset hri
      change k + r • e ∈ K.support at hC
      exact (mem_interior_iff_notMem_frontier hC).mpr hr
  exact (Tiling.AxisParallel.Foundations.lineTilesOn_congr_ae
    hBopen.measurableSet isOpen_interior.measurableSet hBB').mp ht

/-- The selected height avoids the finite intrinsic vertex alphabet. All
coverage, packing, and countability inputs are constructed from the collar. -/
private theorem oneSided_minimumFibre_sectionTiling
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ) (hδ : Module.finrank ℝ δ = 1) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ) (htile : TilesOn K T Set.univ)
    (P : EarthquakeComponent K δ T)
    (hbound : ∃ a : ℝ, ∀ s ∈ P.centres, a ≤ ℓ s) :
    ∃ t ∈ P.centres, (∀ s ∈ P.centres, ℓ t ≤ ℓ s) ∧
      ∃ e ∈ δ, e ≠ 0 ∧ ∃ k : Plane,
        Tiling.AxisParallel.OneDimensional.LineTiles
          (interior {r : ℝ | k + r • e ∈ K.support})
          {q : ℝ | t + q • e ∈ lineFibre δ P.centres t} := by
  obtain ⟨t, ht, v, _, hmin, _, _, c, hc, hcover⟩ :=
    oneSided_minimumFibre_collar K δ T ℓ hδ hℓ hker htile P hbound
  have hcritical : (ℓ '' vertexSet K.support).Finite := K.isPolygonal.vertexSet_finite.image ℓ
  obtain ⟨q, hq, hqcrit⟩ :=
    (Set.Ioo_infinite (show ℓ v < ℓ v + c by linarith)).exists_notMem_finite hcritical
  obtain ⟨k, hk⟩ := nonzeroFunctional_surjective ℓ hℓ q
  obtain ⟨u, hu⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := δ)).mp
    (by rw [hδ]; norm_num)
  let e : Plane := u
  have he : e ≠ 0 := by
    intro hezero
    apply hu
    exact Subtype.ext hezero
  have heδ : e ∈ δ := u.property
  have hℓe : ℓ e = 0 := by
    have h := hker ▸ heδ
    exact h
  have hspan : δ = Submodule.span ℝ ({e} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ heδ he
  let S : Set Plane := lineFibre δ P.centres t
  have hST : S ⊆ T := by
    rintro s ⟨⟨a, _, rfl⟩, _⟩
    exact a.property
  have hp : IsPacking K.prototileFamily (K.placements S) := by
    intro a ha b hb hab
    exact htile.2.1 (hST ha) (hST hb) hab
  have hline : ∀ s ∈ S, ∃ r : ℝ, s = t + r • e := by
    intro s hs
    have hsmem : s - t ∈ Submodule.span ℝ ({e} : Set Plane) := hspan ▸ hs.2
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hsmem
    refine ⟨r, ?_⟩
    rw [hr]
    abel
  have hboundary := polygonal_noncriticalSection_boundaryFinite K ℓ k e he hℓe
    (by rw [hk]; exact hqcrit)
  have hlinecover : ∀ r : ℝ, ∃ s ∈ S, t + k + r • e ∈ s +ᵥ K.support := by
    intro r
    apply hcover
    · simp only [map_add, map_smul, hℓe, smul_zero, add_zero, hk]
      linarith [hq.1]
    · simp only [map_add, map_smul, hℓe, smul_zero, add_zero, hk]
      linarith [hq.2]
  exact ⟨t, ht, hmin, e, heδ, he, k,
    collarSection_regularizedLineTiles K S t k e he (htile.1.mono hST)
      hp hline hboundary hlinecover⟩

private theorem nonzeroVector_normalizedFunctional (e : Plane) (he : e ≠ 0) :
    ∃ f : Plane →L[ℝ] ℝ, f e = 1 := by
  by_cases hre : e.re = 0
  · have him : e.im ≠ 0 := by
      intro him
      apply he
      exact Complex.ext hre him
    refine ⟨(e.im)⁻¹ • Complex.imCLM, ?_⟩
    simp [him]
  · refine ⟨(e.re)⁻¹ • Complex.reCLM, ?_⟩
    simp [hre]

theorem oneSided_minimumFibre_hasFLC :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ), Module.finrank ℝ δ = 1 → ℓ ≠ 0 →
    LinearMap.ker ℓ.toLinearMap = δ → TilesOn K T Set.univ →
      ∀ P : EarthquakeComponent K δ T,
        (∃ a : ℝ, ∀ s ∈ P.centres, a ≤ ℓ s) →
          ∃ t ∈ P.centres, (∀ s ∈ P.centres, ℓ t ≤ ℓ s) ∧
            HasFLC (lineFibre δ P.centres t)
  := by
  intro K δ T ℓ hδ hℓ hker htile P hbound
  obtain ⟨t, ht, hmin, e, heδ, he, k, hlineTile⟩ :=
    oneSided_minimumFibre_sectionTiling K δ T ℓ hδ hℓ hker htile P hbound
  let S : Set Plane := lineFibre δ P.centres t
  let B : Set ℝ := interior {r : ℝ | k + r • e ∈ K.support}
  let L : Set ℝ := {q | t + q • e ∈ S}
  have hTile : Tiling.AxisParallel.OneDimensional.LineTiles B L := hlineTile
  obtain ⟨n, a, b, _, hclosedSection⟩ := initialFibre_polygonalClosedSection K k e he
  obtain ⟨presentation⟩ :=
    Tiling.AxisParallel.Foundations.GenericSlices.finiteClosedIntervals_merge a b
  have hB : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion B := by
    refine ⟨presentation.n, presentation.left, presentation.right,
      presentation.lt, ?_⟩
    change interior {r : ℝ | k + r • e ∈ K.support} =
      ⋃ i, Set.Ioo (presentation.left i) (presentation.right i)
    rw [hclosedSection]
    exact presentation.union_eq
  have hBnonempty : B.Nonempty := by
    have hcoverage : ∀ᵐ r : ℝ ∂volume, ∃ q : L, r ∈ (q : ℝ) +ᵥ B := by
      filter_upwards [hTile.2.2.2.2] with r hr
      exact hr.mp (Set.mem_univ r)
    obtain ⟨r, q, z, hz, _⟩ := hcoverage.exists
    exact ⟨z, hz⟩
  let BP := Tiling.AxisParallel.OneDimensional.FiniteInterval.IntervalPresentation.ofIsFiniteIntervalRegion hB
  have hBpos : 0 < (volume B).toReal :=
    ENNReal.toReal_pos (isOpen_interior.measure_ne_zero volume hBnonempty) BP.volume_ne_top
  have hLflc := scalarLineTiles_hasFLC hB hBpos hTile
  obtain ⟨f, hfe⟩ := nonzeroVector_normalizedFunctional e he
  have hspan : δ = Submodule.span ℝ ({e} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ heδ he
  have hcoords : ∀ s ∈ S, ∃ q : ℝ, s = t + q • e := by
    intro s hs
    obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hs.2)
    refine ⟨q, ?_⟩
    rw [hq]
    abel
  have himage : f '' S = f t +ᵥ L := by
    apply Set.Subset.antisymm
    · rintro y ⟨s, hs, rfl⟩
      obtain ⟨q, hq⟩ := hcoords s hs
      refine ⟨q, ?_, ?_⟩
      · change t + q • e ∈ S
        rw [← hq]
        exact hs
      · change f t + q = f s
        rw [hq, map_add, map_smul, hfe, smul_eq_mul, mul_one]
    · rintro y ⟨q, hq, rfl⟩
      refine ⟨t + q • e, hq, ?_⟩
      change f (t + q • e) = f t + q
      rw [map_add, map_smul, hfe, smul_eq_mul, mul_one]
  have hkernel : ∀ x ∈ δ, f x = 0 → x = 0 := by
    intro x hx hfx
    obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hx)
    have hqzero : q = 0 := by
      rw [← hq, map_smul, hfe, smul_eq_mul, mul_one] at hfx
      exact hfx
    rw [← hq, hqzero, zero_smul]
  refine ⟨t, ht, hmin, ?_⟩
  apply scalarFLC_of_lineSupport (anchor := t) (δ := δ) (fun s hs => hs.2) f hkernel
  rw [himage]
  exact hLflc.vadd (f t)

private theorem lineFibre_eq_of_baseDifference_mem
    (δ : Submodule ℝ Plane) (S : Set Plane) {a b : Plane}
    (hab : a - b ∈ δ) : lineFibre δ S a = lineFibre δ S b := by
  ext s
  constructor
  · rintro ⟨hs, hsa⟩
    refine ⟨hs, ?_⟩
    convert δ.add_mem hsa hab using 1
    abel
  · rintro ⟨hs, hsb⟩
    refine ⟨hs, ?_⟩
    convert δ.sub_mem hsb hab using 1
    abel

private theorem oneSided_minimumFibre_lineFLCGeometry
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ) (hδ : Module.finrank ℝ δ = 1) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ) (htile : TilesOn K T Set.univ)
    (P : EarthquakeComponent K δ T)
    (hbound : ∃ a : ℝ, ∀ s ∈ P.centres, a ≤ ℓ s) :
    ∃ t ∈ P.centres, (∀ s ∈ P.centres, ℓ t ≤ ℓ s) ∧
      HasFLC (lineFibre δ P.centres t) ∧
      (∃ ρ : ℝ, 0 < ρ ∧ ∀ z : Plane, z - t ∈ δ →
        ∃ s ∈ lineFibre δ P.centres t, dist z s < ρ) ∧
      TilesOn K (lineFibre δ P.centres t) (regularSupport K (lineFibre δ P.centres t)) := by
  obtain ⟨t, ht, hmin, hflc⟩ :=
    oneSided_minimumFibre_hasFLC K δ T ℓ hδ hℓ hker htile P hbound
  obtain ⟨a, ha, v, _, hamin, _, _, c, hc, hcollar⟩ :=
    oneSided_minimumFibre_collar K δ T ℓ hδ hℓ hker htile P hbound
  have hat : a - t ∈ δ := by
    have heq : ℓ a = ℓ t := le_antisymm (hamin t ht) (hmin a ha)
    have hzero : a - t ∈ LinearMap.ker ℓ.toLinearMap := by
      change ℓ (a - t) = 0
      rw [map_sub, heq, sub_self]
    exact hker ▸ hzero
  have hfibres := lineFibre_eq_of_baseDifference_mem δ P.centres hat
  obtain ⟨ρ, hρ, hdense⟩ := collarFibre_lineRelativeDense K δ P.centres a v ℓ c hℓ hker hc hcollar
  have hdenseT : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : Plane, z - t ∈ δ →
      ∃ s ∈ lineFibre δ P.centres t, dist z s < ρ := by
    refine ⟨ρ, hρ, ?_⟩
    intro z hz
    have hza : z - a ∈ δ := by
      convert δ.sub_mem hz hat using 1
      abel
    obtain ⟨s, hs, hzs⟩ := hdense z hza
    exact ⟨s, hfibres ▸ hs, hzs⟩
  have hsub : lineFibre δ P.centres t ⊆ T := by
    rintro s ⟨⟨u, _, rfl⟩, _⟩
    exact u.property
  have hp : IsPacking K.prototileFamily (K.placements (lineFibre δ P.centres t)) := by
    intro s hs u hu hsu
    exact htile.2.1 (hsub hs) (hsub hu) hsu
  exact ⟨t, ht, hmin, hflc, hdenseT, tilesOn_regularSupport_of_packing hp⟩

open Tiling.Approximation Tiling.RationalSlopes.Approximation in
/-- The initial fibre is genuinely constructed before invoking FT. Its density
is relative to one affine line, not to the plane. The FT dependency is currently
provisional and is explicitly listed in the axiom/dependency receipt. -/
private theorem oneSided_minimumFibre_finiteGerms
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ) (hK : HasRationalSlopes K)
    (hδ : Module.finrank ℝ δ = 1) (hb : HasBoundaryDirection K δ) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ) (htile : TilesOn K T Set.univ)
    (P : EarthquakeComponent K δ T)
    (hbound : ∃ a : ℝ, ∀ s ∈ P.centres, a ≤ ℓ s) :
    ∃ t ∈ P.centres, (∀ s ∈ P.centres, ℓ t ≤ ℓ s) ∧
      ∃ Q : PolyhedralCode, polyhedralSupport Q = K.support ∧
        ∃ W : Finset Plane, Decorates K W ∧ 0 ∈ W ∧
          ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
            ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
              ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport Q φ ∧
                Tiling.IsRational Kφ.support ∧ Tiling.RationalSlopes.HasRationalSlopes Kφ ∧
                Decorates Kφ (W.image (deformPoint φ)) ∧
                Set.InjOn (deformPoint φ) (decoratedCloud W (lineFibre δ P.centres t)) ∧
                Tiling.Polygonal.TilesOn Kφ (deformPoint φ '' (lineFibre δ P.centres t))
                  (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' (lineFibre δ P.centres t))) ∧
                (∀ U ⊆ (lineFibre δ P.centres t), ∀ v ∈ decoratedCloud W (lineFibre δ P.centres t),
                  Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K U) v
                    (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' U))
                      (deformPoint φ v)) ∧
                (∀ U ⊆ (lineFibre δ P.centres t), Tiling.Polygonal.properVertices
                  (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' U)) =
                    deformPoint φ '' Tiling.Polygonal.properVertices
                      (Tiling.Polygonal.regularSupport K U)) := by
  obtain ⟨t, ht, hmin, hflc, hdense, htS⟩ :=
    oneSided_minimumFibre_lineFLCGeometry K δ T ℓ hδ hℓ hker htile P hbound
  refine ⟨t, ht, hmin, ?_⟩
  exact Tiling.RationalSlopes.Approximation.finiteFLCFibre_germEquivalence
    K (lineFibre δ P.centres t) δ t hK hδ
    (hasRationalDirection_of_hasBoundaryDirection hK hb) hflc
    (fun s hs => hs.2) hdense htS

private theorem sourceColumn_of_exactProperVertexTransport
    (K L : PolygonalRegion) (δ : Submodule ℝ Plane) (hδ : Module.finrank ℝ δ = 1)
    (S : Set Plane) (hS : S.Nonempty)
    (hp : IsPacking K.prototileFamily (K.placements S)) (hline : IsLineSupported S δ)
    (f : Plane → Plane)
    (htransport : properVertices (regularSupport L (f '' S)) =
      f '' properVertices (regularSupport K S))
    (hnewColumn : IsCenterColumn L δ (f '' S)) : IsCenterColumn K δ S := by
  have hnewEmpty : properVertices (regularSupport L (f '' S)) = ∅ :=
    (lineCarrier_noProperVertices_iff_column hδ (hS.image f)
      hnewColumn.1 hnewColumn.2.2.1).mpr hnewColumn
  have hsourceEmpty : properVertices (regularSupport K S) = ∅ :=
    Set.image_eq_empty.mp (htransport.symm.trans hnewEmpty)
  exact (lineCarrier_noProperVertices_iff_column hδ hS hp hline).mp hsourceEmpty

private theorem column_lineRelativeDense
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (C : Set Plane)
    (hc : IsCenterColumn K δ C) (t : Plane) (ht : t ∈ C) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : Plane, z - t ∈ δ →
      ∃ s ∈ C, dist z s < ρ := by
  obtain ⟨v, hv⟩ := K.nonempty
  obtain ⟨R, hR, hbound⟩ := K.isPolygonal.isCompact.isBounded.exists_pos_norm_lt
  have hclosedInv : IsInvariantAlong (closure (regularSupport K C)) δ := by
    intro u hu
    rw [← closure_vadd]
    exact congrArg closure (hc.2.2.2 u hu)
  have hclosedCarrier := closure_regularSupport_eq_supportUnion hc.1
  have hbase : t + v ∈ closure (regularSupport K C) := by
    rw [hclosedCarrier]
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, Set.vadd_mem_vadd_set hv⟩
  refine ⟨R + ‖v‖, by positivity, ?_⟩
  intro z hz
  have hcovered : z + v ∈ closure (regularSupport K C) := by
    rw [← hclosedInv (z - t) hz]
    refine ⟨t + v, hbase, ?_⟩
    change z - t + (t + v) = z + v
    abel
  rw [hclosedCarrier] at hcovered
  obtain ⟨s, y, hy, hsy⟩ := Set.mem_iUnion.mp hcovered
  refine ⟨s, s.property, ?_⟩
  change (s : Plane) + y = z + v at hsy
  have hdiff : z - s = y - v := by linear_combination -hsy
  rw [dist_eq_norm, hdiff]
  exact (norm_sub_le y v).trans_lt (by linarith [hbound y hy])

private theorem periodicLinePacking_hasFLC
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {C : Set Plane} {q : Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (hp : IsPacking K.prototileFamily (K.placements C))
    (hline : IsLineSupported C δ) (hqδ : q ∈ δ) (hq : q ≠ 0)
    (hper : q ∈ periodGroup C) : HasFLC C := by
  obtain ⟨hloc, _, _⟩ := packing_centres_locallyFinite hp
  have hδspan : δ = Submodule.span ℝ ({q} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ hqδ hq
  constructor
  · exact hloc
  · intro R hR
    obtain ⟨anchor, hanchor⟩ := hline
    let W : Set Plane := C ∩ Metric.closedBall anchor (R + ‖q‖)
    have hW : W.Finite := hloc _ Metric.isBounded_closedBall
    apply (hW.sub hW).subset
    intro d hd
    obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_sub.mp hd.1
    rcases Submodule.mem_span_singleton.mp
        (by rw [← hδspan]; exact hanchor t ht) with ⟨r, hr⟩
    have htRep : t = anchor + r • q := by
      calc
        t = (t - anchor) + anchor := by abel
        _ = r • q + anchor := by rw [← hr]
        _ = anchor + r • q := by ac_rfl
    let n : ℤ := -⌊r⌋
    let v : Plane := n • q
    have hperiodv : v +ᵥ C = C := by
      have hv := (periodGroup C).zsmul_mem hper n
      simpa only [Tiling.AxisParallel.periodGroup_isAddSubgroup, v] using hv
    let s' : Plane := v + s
    let t' : Plane := v + t
    have hs' : s' ∈ C := by
      have hs'v : s' ∈ v +ᵥ C := ⟨s, hs, rfl⟩
      simpa [hperiodv] using hs'v
    have ht' : t' ∈ C := by
      have ht'v : t' ∈ v +ᵥ C := ⟨t, ht, rfl⟩
      simpa [hperiodv] using ht'v
    have hdiff : s' - t' = s - t := by dsimp [s', t']; abel
    have hfloorlo : 0 ≤ r - (⌊r⌋ : ℝ) := by linarith [Int.floor_le r]
    have hfloorhi : r - (⌊r⌋ : ℝ) < 1 := by linarith [Int.lt_floor_add_one r]
    have ht'Rep : t' = anchor + (r - (⌊r⌋ : ℝ)) • q := by
      dsimp [t', v, n]
      rw [htRep]
      simp only [zsmul_eq_mul, Int.cast_neg]
      simp
      simp only [Int.fract]
      push_cast
      ring
    have ht'bound : dist t' anchor ≤ ‖q‖ := by
      rw [dist_eq_norm, show t' - anchor =
        (r - (⌊r⌋ : ℝ)) • q by rw [ht'Rep]; abel]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfloorlo]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hfloorhi.le (norm_nonneg q)
    have hdBound : dist (s - t) 0 ≤ R := by
      simpa only [Metric.mem_closedBall] using hd.2
    have hs'bound : dist s' anchor ≤ R + ‖q‖ := by
      calc
        dist s' anchor = ‖s' - anchor‖ := dist_eq_norm s' anchor
        _ = ‖(s' - t') + (t' - anchor)‖ := by congr 1; abel
        _ ≤ ‖s' - t'‖ + ‖t' - anchor‖ := norm_add_le _ _
        _ = dist (s - t) 0 + dist t' anchor := by
          rw [dist_eq_norm (s - t) 0, dist_eq_norm t' anchor, hdiff]
          simp
        _ ≤ R + ‖q‖ := add_le_add hdBound ht'bound
    exact Set.mem_sub.mpr ⟨s', ⟨hs', Metric.mem_closedBall.mpr hs'bound⟩,
      t', ⟨ht', Metric.mem_closedBall.mpr
        (ht'bound.trans (le_add_of_nonneg_left hR.le))⟩, hdiff⟩

/-- The persistent fibre's FLC is derived from its actual one-dimensional
column period, independently of any planar FLC hypothesis. -/
private theorem persistentColumn_hasFLC
    (K : PolygonalRegion) (T : Set Plane) (η : Submodule ℝ Plane)
    (hη : Module.finrank ℝ η = 1) (data : PersistentColumnData K T η) :
    HasFLC data.column := by
  obtain ⟨q, hqη, hq, hqper⟩ := column_universal_period K η hη
  exact periodicLinePacking_hasFLC hη data.column_isColumn.1
    data.column_isColumn.2.2.1 hqη hq (hqper _ data.column_isColumn)

open Tiling.Approximation Tiling.RationalSlopes.Approximation in
/-- Actual persistent-column finite germs. No extra conclusion is stored in
PersistentColumnData: FLC, relative density and the local tiling are proved. -/
private theorem persistentColumn_finiteGerms
    (K : PolygonalRegion) (T : Set Plane) (η : Submodule ℝ Plane)
    (hK : HasRationalSlopes K) (hη : Module.finrank ℝ η = 1)
    (hηrat : HasRationalDirection η) (data : PersistentColumnData K T η) :
    ∃ Q : PolyhedralCode, polyhedralSupport Q = K.support ∧
      ∃ W : Finset Plane, Decorates K W ∧ 0 ∈ W ∧
        ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
          ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
            ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport Q φ ∧
              Tiling.IsRational Kφ.support ∧ HasRationalSlopes Kφ ∧
              Decorates Kφ (W.image (deformPoint φ)) ∧
              Set.InjOn (deformPoint φ) (decoratedCloud W data.column) ∧
              TilesOn Kφ (deformPoint φ '' data.column)
                (regularSupport Kφ (deformPoint φ '' data.column)) ∧
              (∀ U ⊆ data.column, ∀ v ∈ decoratedCloud W data.column,
                SameGermAt (regularSupport K U) v
                  (regularSupport Kφ (deformPoint φ '' U)) (deformPoint φ v)) ∧
              (∀ U ⊆ data.column, properVertices
                (regularSupport Kφ (deformPoint φ '' U)) =
                  deformPoint φ '' properVertices (regularSupport K U)) := by
  have hline : ∀ s ∈ data.column, s - data.anchor ∈ η := by
    obtain ⟨a, ha⟩ := data.column_isColumn.2.2.1
    intro s hs
    convert η.sub_mem (ha s hs) (ha data.anchor data.anchor_mem_column) using 1
    abel
  exact finiteFLCFibre_germEquivalence K data.column η data.anchor hK hη hηrat
    (persistentColumn_hasFLC K T η hη data) hline
    (column_lineRelativeDense K η data.column data.column_isColumn
      data.anchor data.anchor_mem_column)
    (tilesOn_regularSupport_of_packing data.column_isColumn.1)

private theorem polygonalRegion_eq_of_support_eq {K L : PolygonalRegion}
    (h : K.support = L.support) : K = L := by
  cases K
  cases L
  cases h
  rfl

open Tiling.Approximation Tiling.RationalSlopes.Approximation in
/-- Combine the genuinely constructed fibre germs with the global forward
one-link deformation. Code independence is tested before choosing φ, so the
two independently constructed polygons are literally the same region. -/
private theorem lineFLC_jointOneLinkDeformation
    (K : PolygonalRegion) (T S : Set Plane) (n : RationalNormal) (a : Plane)
    (hK : HasRationalSlopes K) (htile : TilesOn K T Set.univ)
    (hlink : HasProperLink K (normalDirection n) T)
    (hflc : HasFLC S) (hline : ∀ s ∈ S, s - a ∈ normalDirection n)
    (hdense : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : Plane, z - a ∈ normalDirection n →
      ∃ s ∈ S, dist z s < ρ)
    (htS : TilesOn K S (regularSupport K S)) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∃ L : PolygonalRegion, Tiling.IsRational L.support ∧ HasRationalSlopes L ∧
          Set.InjOn (deformPoint φ) T ∧ TilesOn L (deformPoint φ '' T) Set.univ ∧
          (∀ U ⊆ T, IsInvariantAlong (regularSupport K U) (normalDirection n) →
            IsInvariantAlong (regularSupport L (deformPoint φ '' U)) (normalDirection n)) ∧
          (∀ U ⊆ S, properVertices (regularSupport L (deformPoint φ '' U)) =
            deformPoint φ '' properVertices (regularSupport K U)) ∧
          (∀ b : Plane, IsProperLink K (normalDirection n) T b →
            ∀ v ∈ translatedVertices K T,
              Real.sign (normalEval n (deformPoint φ (v - b))) =
                Real.sign (normalEval n (v - b)) ∧
              |normalEval n (v - b)| / 2 ≤
                |normalEval n (deformPoint φ (v - b))| ∧
              |normalEval n (deformPoint φ (v - b))| ≤ 2 * |normalEval n (v - b)|) := by
  classical
  obtain ⟨hδ, hδrat⟩ := normalDirection_rational n
  obtain ⟨P, hP, F₁, ε₁, hε₁, hglobal⟩ :=
    oneLinkRationalDeformation K T (normalDirection n) hδ hδrat hK htile hlink
  obtain ⟨Q, hQ, W, hW, hWzero, F₂, ε₂, hε₂, hfibre⟩ :=
    finiteFLCFibre_germEquivalence K S (normalDirection n) a hK hδ hδrat
      hflc hline hdense htS
  obtain ⟨F₃, ε₃, hε₃, hcodes⟩ :=
    polyhedralDeformation_independentOfCode K P Q hP hQ
  obtain ⟨F₄, ε₄, hε₄, horder⟩ := properLink_normalOrderControl K T n hK htile
  let F := (F₁ ∪ F₂) ∪ (F₃ ∪ F₄)
  let ε := min (min ε₁ ε₂) (min ε₃ ε₄)
  refine ⟨F, ε, lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄), ?_⟩
  intro φ hφ
  have h₁ : IsFiniteApproximation F₁ ε₁ φ :=
    finiteApproximation_strengthen F₁ F ε₁ ε φ
      (by intro x hx; simp [F, hx])
      ((min_le_left _ _).trans (min_le_left _ _)) hφ
  have h₂ : IsFiniteApproximation F₂ ε₂ φ :=
    finiteApproximation_strengthen F₂ F ε₂ ε φ
      (by intro x hx; simp [F, hx])
      ((min_le_left _ _).trans (min_le_right _ _)) hφ
  have h₃ : IsFiniteApproximation F₃ ε₃ φ :=
    finiteApproximation_strengthen F₃ F ε₃ ε φ
      (by intro x hx; simp [F, hx])
      ((min_le_right _ _).trans (min_le_left _ _)) hφ
  have h₄ : IsFiniteApproximation F₄ ε₄ φ :=
    finiteApproximation_strengthen F₄ F ε₄ ε φ
      (by intro x hx; simp [F, hx])
      ((min_le_right _ _).trans (min_le_right _ _)) hφ
  obtain ⟨L, hL, hLrat, hinj, htileL, hinvL, hcolumnsL⟩ := hglobal φ h₁
  obtain ⟨M, hM, hMrat, hMslopes, hMW, hMinj, hMtile, hMgerms, hMvertices⟩ :=
    hfibre φ h₂
  have hLM : L = M := polygonalRegion_eq_of_support_eq
    (hL.trans ((hcodes φ h₃).trans hM.symm))
  subst M
  exact ⟨L, hLrat, hMslopes, hinj, htileL, hinvL, hMvertices,
    horder φ h₄⟩

private theorem sameKernel_functionals_proportional
    (ℓ π : Plane →L[ℝ] ℝ) (hπ : π ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = LinearMap.ker π.toLinearMap) :
    ∃ c : ℝ, ∀ z : Plane, ℓ z = c * π z := by
  obtain ⟨x, hx⟩ := nonzeroFunctional_surjective π hπ 1
  refine ⟨ℓ x, ?_⟩
  intro z
  have hz : z - π z • x ∈ LinearMap.ker π.toLinearMap := by
    change π (z - π z • x) = 0
    rw [map_sub, map_smul, hx]
    simp
  have hzero : ℓ (z - π z • x) = 0 := by
    change z - π z • x ∈ LinearMap.ker ℓ.toLinearMap
    rwa [hker]
  simp only [map_sub, map_smul, smul_eq_mul] at hzero
  nlinarith

private theorem sign_eq_preserves_nonneg {x y : ℝ}
    (h : Real.sign y = Real.sign x) (hx : 0 ≤ x) : 0 ≤ y := by
  by_contra hy
  have hyneg : y < 0 := lt_of_not_ge hy
  rcases hx.eq_or_lt with hzero | hpos
  · rw [← hzero, Real.sign_zero, Real.sign_of_neg hyneg] at h
    norm_num at h
  · rw [Real.sign_of_pos hpos, Real.sign_of_neg hyneg] at h
    norm_num at h

open Tiling.Approximation in
/-- Global sign control is used only relative to an actual old proper link.
This lemma does not assert order reflection for arbitrary pairs of centres. -/
private theorem normalSign_preservesFunctional_nonneg
    (n : RationalNormal) (ℓ : Plane →L[ℝ] ℝ)
    (hker : LinearMap.ker ℓ.toLinearMap = normalDirection n)
    (φ : ℝ →ₗ[ℚ] ℚ) (z : Plane)
    (hsign : Real.sign (normalEval n (deformPoint φ z)) = Real.sign (normalEval n z))
    (hz : 0 ≤ ℓ z) : 0 ≤ ℓ (deformPoint φ z) := by
  let π : Plane →L[ℝ] ℝ := (n.x : ℝ) • Complex.reCLM + (n.y : ℝ) • Complex.imCLM
  have hπeval : ∀ w : Plane, π w = normalEval n w := by intro w; rfl
  have hπ : π ≠ 0 := by
    intro hzero
    have hx : (n.x : ℝ) = 0 := by simpa [π] using DFunLike.congr_fun hzero 1
    have hy : (n.y : ℝ) = 0 := by simpa [π] using DFunLike.congr_fun hzero Complex.I
    have hx' : n.x = 0 := by exact_mod_cast hx
    have hy' : n.y = 0 := by exact_mod_cast hy
    exact n.nonzero.elim (fun h => h hx') (fun h => h hy')
  obtain ⟨c, hc⟩ := sameKernel_functionals_proportional ℓ π hπ hker
  rw [hc] at hz ⊢
  rw [hπeval] at hz ⊢
  by_cases hcnonneg : 0 ≤ c
  · by_cases hc0 : c = 0
    · simp [hc0]
    · have hcpos : 0 < c := lt_of_le_of_ne hcnonneg (Ne.symm hc0)
      exact mul_nonneg hcnonneg
        (sign_eq_preserves_nonneg hsign ((mul_nonneg_iff_of_pos_left hcpos).mp hz))
  · have hcneg : c < 0 := lt_of_not_ge hcnonneg
    have hznonpos : normalEval n z ≤ 0 := by
      by_contra h
      exact (mul_neg_of_neg_of_pos hcneg (lt_of_not_ge h)).not_ge hz
    have hsignneg : Real.sign (-normalEval n (deformPoint φ z)) =
        Real.sign (-normalEval n z) := by simpa only [Real.sign_neg] using congrArg Neg.neg hsign
    have hnewnonpos : normalEval n (deformPoint φ z) ≤ 0 := by
      simpa only [neg_nonneg] using sign_eq_preserves_nonneg hsignneg (neg_nonneg.mpr hznonpos)
    exact mul_nonneg_of_nonpos_of_nonpos hcneg.le hnewnonpos

open Tiling.Approximation in
private theorem normalSign_preservesFunctional_zero_iff
    (n : RationalNormal) (ℓ : Plane →L[ℝ] ℝ)
    (hker : LinearMap.ker ℓ.toLinearMap = normalDirection n)
    (φ : ℝ →ₗ[ℚ] ℚ) (z : Plane)
    (hsign : Real.sign (normalEval n (deformPoint φ z)) = Real.sign (normalEval n z)) :
    ℓ (deformPoint φ z) = 0 ↔ ℓ z = 0 := by
  have hzero : normalEval n (deformPoint φ z) = 0 ↔ normalEval n z = 0 := by
    constructor
    · intro h
      apply Real.sign_eq_zero_iff.mp
      rw [← hsign]
      exact Real.sign_eq_zero_iff.mpr h
    · intro h
      apply Real.sign_eq_zero_iff.mp
      rw [hsign]
      exact Real.sign_eq_zero_iff.mpr h
  change deformPoint φ z ∈ LinearMap.ker ℓ.toLinearMap ↔
    z ∈ LinearMap.ker ℓ.toLinearMap
  rw [hker]
  exact hzero

open Tiling.Approximation in
/-- The exact minimum fibre is identified by sign tests relative to its old
extremal link, rather than by a global converse deformation on all pairs. -/
private theorem labelledMinimum_fibreImage
    (S : Set Plane) (n : RationalNormal) (ℓ : Plane →L[ℝ] ℝ)
    (hker : LinearMap.ker ℓ.toLinearMap = normalDirection n)
    (φ : ℝ →ₗ[ℚ] ℚ) (t : Plane)
    (hmin : ∀ s ∈ S, ℓ t ≤ ℓ s)
    (hsign : ∀ s ∈ S, Real.sign (normalEval n (deformPoint φ (s - t))) =
      Real.sign (normalEval n (s - t))) :
    (∀ s ∈ S, ℓ (deformPoint φ t) ≤ ℓ (deformPoint φ s)) ∧
      lineFibre (normalDirection n) (deformPoint φ '' S) (deformPoint φ t) =
        deformPoint φ '' lineFibre (normalDirection n) S t := by
  have hsub : ∀ s : Plane, deformPoint φ (s - t) =
      deformPoint φ s - deformPoint φ t := fun s => (deformPointLinear φ).map_sub s t
  constructor
  · intro s hs
    have hz : 0 ≤ ℓ (s - t) := by rw [map_sub]; linarith [hmin s hs]
    have hnew := normalSign_preservesFunctional_nonneg n ℓ hker φ (s - t)
      (hsign s hs) hz
    rw [hsub, map_sub] at hnew
    linarith
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, hδ⟩
      refine ⟨s, ⟨hs, ?_⟩, rfl⟩
      have hnew : ℓ (deformPoint φ (s - t)) = 0 := by
        rw [hsub]
        change deformPoint φ s - deformPoint φ t ∈ LinearMap.ker ℓ.toLinearMap
        rwa [hker]
      have hold := (normalSign_preservesFunctional_zero_iff n ℓ hker φ (s - t)
        (hsign s hs)).mp hnew
      change s - t ∈ normalDirection n
      rw [← hker]
      exact hold
    · rintro x ⟨s, ⟨hs, hδ⟩, rfl⟩
      exact ⟨⟨s, hs, rfl⟩, rationalDirection_preservesCoset φ n s t hδ⟩

private theorem rationalSupport_isRelativelyRational
    (K : PolygonalRegion) (hK : Tiling.IsRational K.support) :
    Tiling.RationalPolygonal.IsRelativelyRational K := by
  obtain ⟨v, hv, _⟩ := intrinsic_minimumVertex K Complex.reCLM (by
    intro h
    have h1 := DFunLike.congr_fun h 1
    norm_num at h1)
  refine ⟨v, hv, ?_⟩
  intro w hw
  obtain ⟨a, b, ha, hb⟩ := hK.2 w hw
  obtain ⟨c, d, hc, hd⟩ := hK.2 v hv
  refine ⟨a - c, b - d, ?_, ?_⟩ <;>
    simp only [Complex.sub_re, Complex.sub_im, ha, hb, hc, hd, Rat.cast_sub]

private theorem period_boundedBelow_forcesFunctional_zero
    {E : Set Plane} {ℓ : Plane →L[ℝ] ℝ} {p : Plane}
    (hE : E.Nonempty)
    (hp : p ∈ Tiling.Polygonal.periodGroup E)
    (hlower : ∃ a : ℝ, ∀ x ∈ E, a ≤ ℓ x) :
    ℓ p = 0 := by
  obtain ⟨a, hlower⟩ := hlower
  have hnonneg (q : Plane) (hq : q ∈ Tiling.Polygonal.periodGroup E) :
      0 ≤ ℓ q := by
    obtain ⟨x, hx⟩ := hE
    by_contra hnot
    have hqneg : ℓ q < 0 := lt_of_not_ge hnot
    have hqpos : 0 < -ℓ q := neg_pos.mpr hqneg
    obtain ⟨n, hn⟩ := exists_nat_gt ((ℓ x - a) / (-ℓ q))
    have hlarge : ℓ x - a < (n : ℝ) * (-ℓ q) :=
      (div_lt_iff₀ hqpos).mp hn
    have htranslate (n : ℕ) : (n • q) +ᵥ E = E := by
      exact (Tiling.AxisParallel.periodGroup_isAddSubgroup E (n • q)).mp
        ((Tiling.Polygonal.periodGroup E).nsmul_mem hq n)
    have hxshift (n : ℕ) : x + n • q ∈ E := by
      have hx' : (n • q) + x ∈ (n • q) +ᵥ E := ⟨x, hx, rfl⟩
      rw [htranslate n] at hx'
      simpa [add_comm] using hx'
    have hbound := hlower (x + n • q) (hxshift n)
    have hbound' : a ≤ ℓ x + (n : ℝ) * ℓ q := by
      rw [map_add, map_nsmul] at hbound
      simpa [nsmul_eq_mul] using hbound
    nlinarith
  have hpneg : -p ∈ Tiling.Polygonal.periodGroup E :=
    (Tiling.Polygonal.periodGroup E).neg_mem hp
  have hleft := hnonneg p hp
  have hright : 0 ≤ -ℓ p := by simpa using hnonneg (-p) hpneg
  linarith

private theorem rational_oneSided_invariantFibre_isColumn
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T S : Set Plane}
    (hK : Tiling.RationalPolygonal.IsRelativelyRational K)
    (hδrank : Module.finrank ℝ δ = 1)
    (hδrat : Tiling.RationalSlopes.HasRationalDirection δ)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (hST : S ⊆ T)
    (hSinv : Tiling.Polygonal.IsInvariantAlong
      (Tiling.Polygonal.regularSupport K S) δ)
    (ℓ : Plane →L[ℝ] ℝ)
    (hker : LinearMap.ker ℓ.toLinearMap = δ)
    (hbound : ∃ a : ℝ, ∀ s ∈ S, a ≤ ℓ s)
    {t : Plane} (ht : t ∈ S) :
    Tiling.Polygonal.IsCenterColumn K δ
      (Tiling.Polygonal.lineFibre δ S t) := by
  classical
  let hpack : Tiling.IsPacking K.prototileFamily (K.placements T) := htile.2.1
  have hTreg : Tiling.Polygonal.regularSupport K T = Set.univ :=
    Tiling.Polygonal.regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hTinv : Tiling.Polygonal.IsInvariantAlong
      (Tiling.Polygonal.regularSupport K T) δ := by
    intro u hu
    rw [hTreg]
    simp
  obtain ⟨v, hvδ, hvcol, hvcomponent⟩ :=
    Tiling.RationalSlopes.rational_wholePlane_commonCarrierPeriod
      K δ T hK hδrank hδrat htile
  let G : SimpleGraph {x : Plane // x ∈ T} :=
    Tiling.RationalSlopes.earthquakeGraph K δ T
  let P : Tiling.RationalSlopes.EarthquakeComponent K δ T :=
    G.connectedComponentMk ⟨t, hST ht⟩
  have htP : t ∈ P.centres := by
    exact ⟨⟨t, hST ht⟩, rfl, rfl⟩
  have hsplit := Tiling.RationalSlopes.invariantSubfamily_isUnionComponents
    K δ T S hδrank hpack hTinv hST hSinv P
  have hPsubset : P.centres ⊆ S := by
    rcases hsplit with hdisj | hsub
    · have hfalse := (Set.disjoint_left.mp hdisj) htP ht
      exact False.elim hfalse
    · exact hsub
  have hpackP : Tiling.IsPacking K.prototileFamily (K.placements P.centres) := by
    intro s hs u hu hsu
    exact htile.2.1 (hST (hPsubset hs)) (hST (hPsubset hu)) hsu
  have hminK : ∃ k ∈ K.support, ∀ z ∈ K.support, ℓ k ≤ ℓ z := by
    exact K.isPolygonal.isCompact.exists_isMinOn K.nonempty ℓ.continuous.continuousOn
  obtain ⟨k, hk, hkmin⟩ := hminK
  have hcarrierLower : ∃ b : ℝ, ∀ x ∈ P.carrier, b ≤ ℓ x := by
    obtain ⟨a, ha⟩ := hbound
    refine ⟨a + ℓ k, ?_⟩
    intro x hx
    have hclosure := Tiling.Polygonal.closure_openUnion_eq_iUnion_support hpackP
    have hxclosure : x ∈ closure (Tiling.Polygonal.openUnion K P.centres) :=
      interior_subset hx
    rw [hclosure] at hxclosure
    obtain ⟨s, y, hy, rfl⟩ := Set.mem_iUnion.mp hxclosure
    have hsS : (s : Plane) ∈ S := hPsubset s.2
    simpa only [vadd_eq_add, map_add] using
      (add_le_add (ha s hsS) (hkmin y hy))
  have hPne : P.carrier.Nonempty := by
    obtain ⟨c, hc⟩ := K.isPolygonal.interior_nonempty K.nonempty
    change c ∈ K.openCarrier at hc
    refine ⟨(t : Plane) + c, ?_⟩
    have hopen : IsOpen (Tiling.Polygonal.openUnion K P.centres) :=
      isOpen_iUnion fun s : {s : Plane // s ∈ P.centres} =>
        isOpen_interior.vadd (s : Plane)
    have htileOpen : (t : Plane) + c ∈ Tiling.Polygonal.openUnion K P.centres := by
      exact Set.mem_iUnion.mpr ⟨⟨t, htP⟩, ⟨c, hc, rfl⟩⟩
    change (t : Plane) + c ∈ interior (closure (Tiling.Polygonal.openUnion K P.centres))
    exact hopen.subset_interior_closure htileOpen
  have hPcol : Tiling.Polygonal.IsCenterColumn K δ P.centres := by
    by_contra hnot
    have hPnoncol : P ∈ Tiling.RationalSlopes.noncolumnComponents K δ T := by
      exact hnot
    have hvperiod : v ∈ Tiling.Polygonal.periodGroup P.carrier :=
      hvcomponent P hPnoncol
    have hvzero := period_boundedBelow_forcesFunctional_zero hPne hvperiod hcarrierLower
    have hvker : v ∈ LinearMap.ker ℓ.toLinearMap := LinearMap.mem_ker.mpr hvzero
    have hvdelta : v ∈ δ := hker ▸ hvker
    exact hvδ hvdelta
  have hfibreT := Tiling.Polygonal.column_maximal_in_fibre
    hδrank hpack (fun x hx => hST (hPsubset hx)) hPcol t htP
  have heq : Tiling.Polygonal.lineFibre δ S t = P.centres := by
    apply Set.Subset.antisymm
    · intro s hs
      have hsT : s ∈ T := hST hs.1
      have hsF : s ∈ Tiling.Polygonal.lineFibre δ T t := ⟨hsT, hs.2⟩
      rw [hfibreT] at hsF
      exact hsF
    · intro s hs
      have hsF : s ∈ Tiling.Polygonal.lineFibre δ T t := by
        rw [hfibreT]
        exact hs
      exact ⟨hPsubset hs, hsF.2⟩
  rw [heq]
  exact hPcol

-- The rational model's exact minimum fibre is reflected only by FT's genuine
-- one-dimensional proper-vertex transport, not by any global inverse theorem.
open Tiling.Approximation Tiling.RationalSlopes.Approximation in
theorem oneSidedComponent_isColumn :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ), HasRationalSlopes K → Module.finrank ℝ δ = 1 →
    HasBoundaryDirection K δ → ℓ ≠ 0 → LinearMap.ker ℓ.toLinearMap = δ →
    TilesOn K T Set.univ → HasNontrivialEarthquakeDecomposition K δ T →
      ∀ P : EarthquakeComponent K δ T,
        (∃ a : ℝ, ∀ t ∈ P.centres, a ≤ ℓ t) → IsCenterColumn K δ P.centres
  := by
  intro K δ T ℓ hK hδ hboundary hℓ hker htile _hnontrivial P hbound
  obtain ⟨n, rfl⟩ := Tiling.RationalSlopes.Approximation.rationalDirection_hasNormal
    δ hδ (hasRationalDirection_of_hasBoundaryDirection hK hboundary)
  obtain ⟨t, ht, hmin, hflc, hdense, htS⟩ :=
    oneSided_minimumFibre_lineFLCGeometry K (normalDirection n) T ℓ
      hδ hℓ hker htile P hbound
  let S : Set Plane := lineFibre (normalDirection n) P.centres t
  have hPsub : P.centres ⊆ T := by
    rintro s ⟨u, _, rfl⟩
    exact u.property
  have hST : S ⊆ T := fun s hs => hPsub hs.1
  have hwhole : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hwholeInv : IsInvariantAlong (regularSupport K T) (normalDirection n) := by
    rw [hwhole]
    intro u _
    exact Set.vadd_set_univ
  have hPinv : IsInvariantAlong (regularSupport K P.centres) (normalDirection n) :=
    component_isInvariant K (normalDirection n) T hδ htile.2.1 hwholeInv P
  obtain ⟨v, hv, hvmin⟩ := intrinsic_minimumVertex K ℓ hℓ
  have hlink : IsProperLink K (normalDirection n) T (v + t) :=
    minimumFibre_extremalProperLink K (normalDirection n) T P.centres ℓ hℓ hker
      htile hPsub hPinv t ht hmin v (intrinsicVertex_mem_support hv) hvmin
  obtain ⟨F, ε, hε, hmodel⟩ := lineFLC_jointOneLinkDeformation K T S n t hK htile
    ⟨v + t, hlink⟩ hflc (fun s hs => hs.2) hdense htS
  obtain ⟨φ, hφ⟩ := exists_finiteApproximation F ε hε
  obtain ⟨L, hLrat, _hLslopes, _hinj, htileL, hinvL, hvertices, horder⟩ := hmodel φ hφ
  have hsign : ∀ s ∈ P.centres,
      Real.sign (normalEval n (deformPoint φ (s - t))) =
        Real.sign (normalEval n (s - t)) := by
    intro s hs
    have hvs : v + s ∈ translatedVertices K T :=
      Set.mem_add.mpr ⟨v, hv, s, hPsub hs, rfl⟩
    have h := (horder (v + t) hlink (v + s) hvs).1
    have hdiff : (v + s) - (v + t) = s - t := by abel
    rwa [hdiff] at h
  obtain ⟨himageMin, hfibre⟩ :=
    labelledMinimum_fibreImage P.centres n ℓ hker φ t hmin hsign
  have hnewInv : IsInvariantAlong (regularSupport L (deformPoint φ '' P.centres))
      (normalDirection n) := hinvL P.centres hPsub hPinv
  have htImage : deformPoint φ t ∈ deformPoint φ '' P.centres := ⟨t, ht, rfl⟩
  have hnewColumn := rational_oneSided_invariantFibre_isColumn
    (rationalSupport_isRelativelyRational L hLrat) hδ (normalDirection_rational n).2
    htileL (Set.image_mono hPsub) hnewInv ℓ hker
    (show ∃ a : ℝ, ∀ s ∈ deformPoint φ '' P.centres, a ≤ ℓ s from
      ⟨ℓ (deformPoint φ t), by
        rintro s ⟨u, hu, rfl⟩
        exact himageMin u hu⟩) htImage
  have himageColumn : IsCenterColumn L (normalDirection n) (deformPoint φ '' S) := by
    rw [← hfibre]
    exact hnewColumn
  have htFibre : t ∈ S := ⟨ht, by simp⟩
  have hsourceColumn : IsCenterColumn K (normalDirection n) S :=
    sourceColumn_of_exactProperVertexTransport K L (normalDirection n) hδ S
      ⟨t, htFibre⟩ htS.2.1 ⟨t, fun s hs => hs.2⟩ (deformPoint φ)
      (hvertices S (Set.Subset.refl S)) himageColumn
  obtain ⟨Q, hQ⟩ := column_isComponent K (normalDirection n) T S
    hδ htile.2.1 hST hsourceColumn
  have htQ : t ∈ Q.centres := by rw [hQ]; exact htFibre
  obtain ⟨u, hu, hut⟩ := ht
  obtain ⟨w, hw, hwt⟩ := htQ
  have huw : u = w := Subtype.ext (hut.trans hwt.symm)
  have huQ : u ∈ Q.supp := by rw [huw]; exact hw
  have hPQ : P = Q := SimpleGraph.ConnectedComponent.eq_of_common_vertex hu huQ
  rw [hPQ, hQ]
  exact hsourceColumn

theorem noncolumnComponent_twoSided :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ), HasRationalSlopes K → Module.finrank ℝ δ = 1 →
    HasBoundaryDirection K δ → ℓ ≠ 0 → LinearMap.ker ℓ.toLinearMap = δ →
    TilesOn K T Set.univ → HasNontrivialEarthquakeDecomposition K δ T →
      ∀ P ∈ noncolumnComponents K δ T, ∀ a : ℝ,
        (∃ t ∈ P.centres, ℓ t < a) ∧ (∃ t ∈ P.centres, a < ℓ t)
  := by
  intro K δ T ℓ hK hδ hboundary hℓ hker htile hnontrivial P hP a
  have hnotcolumn : ¬ IsCenterColumn K δ P.centres := hP
  constructor
  · by_contra h
    apply hnotcolumn
    apply oneSidedComponent_isColumn K δ T ℓ hK hδ hboundary hℓ hker
      htile hnontrivial P
    refine ⟨a, ?_⟩
    intro t ht
    exact le_of_not_gt (fun hlt => h ⟨t, ht, hlt⟩)
  · by_contra h
    have hneg : (-ℓ : Plane →L[ℝ] ℝ) ≠ 0 := neg_ne_zero.mpr hℓ
    have hnegker : LinearMap.ker (-ℓ).toLinearMap = δ := by
      rw [← hker]
      ext x
      simp
    apply hnotcolumn
    apply oneSidedComponent_isColumn K δ T (-ℓ) hK hδ hboundary hneg
      hnegker htile hnontrivial P
    refine ⟨-a, ?_⟩
    intro t ht
    have hle : ℓ t ≤ a := le_of_not_gt (fun hgt => h ⟨t, ht, hgt⟩)
    simpa using neg_le_neg hle

private theorem noncolumnComponent_transverseDense
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    (_hK : Tiling.RationalSlopes.HasRationalSlopes K)
    (_hδ : Module.finrank ℝ δ = 1)
    (_hboundary : Tiling.Polygonal.HasBoundaryDirection K δ)
    (ℓ : Plane →L[ℝ] ℝ) (_hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ)
    (_htile : Tiling.Polygonal.TilesOn K T Set.univ)
    (_hnontrivial : Tiling.RationalSlopes.HasNontrivialEarthquakeDecomposition K δ T)
    (P : Tiling.RationalSlopes.EarthquakeComponent K δ T)
    (_hPnoncol : P ∈ Tiling.RationalSlopes.noncolumnComponents K δ T)
    (htwo : ∀ a : ℝ,
      (∃ s ∈ P.centres, ℓ s < a) ∧ (∃ s ∈ P.centres, a < ℓ s)) :
    ∃ M : ℝ, 0 < M ∧ ∀ a : ℝ, ∃ s ∈ P.centres, |ℓ s - a| ≤ M := by
  classical
  obtain ⟨klo, hklo, hklo_min⟩ :=
    K.isPolygonal.isCompact.exists_isMinOn K.nonempty ℓ.continuous.continuousOn
  obtain ⟨khi, hkhi, hkhi_max⟩ :=
    K.isPolygonal.isCompact.exists_isMaxOn K.nonempty ℓ.continuous.continuousOn
  let M : ℝ := ℓ khi - ℓ klo + 1
  have hM : 0 < M := by
    dsimp [M]
    have hle : ℓ klo ≤ ℓ khi := hklo_min hkhi
    linarith
  let G : SimpleGraph {s : Plane // s ∈ T} :=
    Tiling.RationalSlopes.earthquakeGraph K δ T
  have overlapBound (s t : Plane)
      (hst : Tiling.RationalSlopes.DirectionalOverlap K δ s t) :
      |ℓ s - ℓ t| ≤ M := by
    rcases hst with ⟨z, hz⟩
    rcases hz with ⟨hzOpen, hzSat⟩
    obtain ⟨x, hx, rfl⟩ := Set.mem_vadd_set.mp hzOpen
    obtain ⟨y, hy, hzy⟩ := hzSat
    obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.mp hy
    have hzero : ℓ ((s + x) - (t + u)) = 0 := by
      have hmem : (s + x) - (t + u) ∈ LinearMap.ker ℓ.toLinearMap := hker ▸ hzy
      exact LinearMap.mem_ker.mp hmem
    have heq : ℓ s - ℓ t = ℓ u - ℓ x := by
      rw [map_sub, map_add, map_add] at hzero
      linarith
    have hxlo : ℓ klo ≤ ℓ x := hklo_min (interior_subset hx)
    have hxhi : ℓ x ≤ ℓ khi := hkhi_max (interior_subset hx)
    have hilo : ℓ klo ≤ ℓ u := hklo_min (interior_subset hu)
    have hihi : ℓ u ≤ ℓ khi := hkhi_max (interior_subset hu)
    rw [abs_le]
    constructor <;> dsimp [M] <;> rw [heq] <;> linarith
  have hedgeBound (s t : {s : Plane // s ∈ T}) (hst : G.Adj s t) :
      |ℓ s.1 - ℓ t.1| ≤ M := by
    have hrel : s ≠ t ∧
        (Tiling.RationalSlopes.DirectionalOverlap K δ s.1 t.1 ∨
          Tiling.RationalSlopes.DirectionalOverlap K δ t.1 s.1) := by
      simpa [G, Tiling.RationalSlopes.earthquakeGraph] using hst
    rcases hrel.2 with hst' | hts'
    · exact overlapBound s.1 t.1 hst'
    · have hrev : |ℓ t.1 - ℓ s.1| ≤ M := by
        exact overlapBound t.1 s.1 hts'
      simpa [abs_sub_comm] using hrev
  have walkCrosses : ∀ (a : ℝ) {s t : {s : Plane // s ∈ T}} (p : G.Walk s t),
      ℓ s.1 < a → a < ℓ t.1 →
        ∃ u : {s : Plane // s ∈ T}, G.Reachable s u ∧ |ℓ u.1 - a| ≤ M := by
    intro a s t p
    induction p with
    | nil =>
        intro hs ht
        linarith
    | @cons s u t hsu p ih =>
        intro hs ht
        by_cases hcross : a ≤ ℓ u.1
        · refine ⟨u, hsu.reachable, ?_⟩
          have hb := hedgeBound s u hsu
          rw [abs_le] at hb
          rw [abs_le]
          constructor <;> dsimp [M] at * <;> linarith
        · have hbelow : ℓ u.1 < a := lt_of_not_ge hcross
          obtain ⟨w, hreach, hw⟩ := ih hbelow ht
          exact ⟨w, hsu.reachable.trans hreach, hw⟩
  refine ⟨M, hM, ?_⟩
  intro a
  obtain ⟨⟨s, hs, hsa⟩, ⟨t, ht, hat⟩⟩ := htwo a
  obtain ⟨s', hs', rfl⟩ := (Set.mem_image _ _ _).mp hs
  obtain ⟨t', ht', rfl⟩ := (Set.mem_image _ _ _).mp ht
  have hsP : G.connectedComponentMk s' = P :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff P s').mp hs'
  have htP : G.connectedComponentMk t' = P :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff P t').mp ht'
  have hreach : G.Reachable s' t' :=
    SimpleGraph.ConnectedComponent.eq.mp (hsP.trans htP.symm)
  obtain ⟨p⟩ := hreach
  obtain ⟨u, huReach, huBound⟩ := walkCrosses a p hsa hat
  have huP : G.connectedComponentMk u = P := by
    exact (SimpleGraph.ConnectedComponent.sound huReach).symm.trans hsP
  have huSupp : u ∈ P.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff P u).mpr huP
  exact ⟨u.1, ⟨u, huSupp, rfl⟩, huBound⟩

private theorem twoDisjointCylinders_frontierNear
    {D E : Set Plane} {δ : Submodule ℝ Plane}
    (ℓ : Plane →L[ℝ] ℝ) (hker : LinearMap.ker ℓ.toLinearMap = δ)
    (q : Plane) (hq : ℓ q = 1)
    (_hDopen : IsOpen D) (_hEopen : IsOpen E)
    (hdisj : Disjoint D E)
    (hDinv : Tiling.Polygonal.IsInvariantAlong D δ)
    (hEinv : Tiling.Polygonal.IsInvariantAlong E δ)
    (hDdense : ∃ M : ℝ, 0 < M ∧
      ∀ a : ℝ, ∃ s ∈ D, |ℓ s - a| ≤ M)
    (hEdense : ∃ M : ℝ, 0 < M ∧
      ∀ a : ℝ, ∃ s ∈ E, |ℓ s - a| ≤ M) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : Plane,
      ∃ a ∈ frontier D, dist z a < R := by
  obtain ⟨MD, hMD, hD⟩ := hDdense
  obtain ⟨ME, hME, hE⟩ := hEdense
  let M : ℝ := max MD ME
  have hM : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le hMD (le_max_left MD ME)
  have hDM : ∀ a : ℝ, ∃ s ∈ D, |ℓ s - a| ≤ M := by
    intro a
    obtain ⟨s, hs, hsbound⟩ := hD a
    exact ⟨s, hs, hsbound.trans (le_max_left MD ME)⟩
  have hEM : ∀ a : ℝ, ∃ s ∈ E, |ℓ s - a| ≤ M := by
    intro a
    obtain ⟨s, hs, hsbound⟩ := hE a
    exact ⟨s, hs, hsbound.trans (le_max_right MD ME)⟩
  let R : ℝ := M * ‖q‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have nearSet (F : Set Plane)
      (hinv : Tiling.Polygonal.IsInvariantAlong F δ)
      (hdense : ∀ a : ℝ, ∃ s ∈ F, |ℓ s - a| ≤ M)
      (z : Plane) : ∃ y ∈ F, y ∈ Metric.ball z R := by
    obtain ⟨s, hs, hbound⟩ := hdense (ℓ z)
    let y : Plane := z + (ℓ s - ℓ z) • q
    have hyval : ℓ y = ℓ s := by
      dsimp [y]
      change ℓ (z + (ℓ s - ℓ z) • q) = ℓ s
      calc
        ℓ (z + (ℓ s - ℓ z) • q) = ℓ z + (ℓ s - ℓ z) • ℓ q := by
          rw [map_add, map_smul]
        _ = ℓ s := by rw [hq]; ring
    have hdelta : y - s ∈ δ := by
      rw [← hker]
      apply LinearMap.mem_ker.mpr
      change ℓ (y - s) = 0
      rw [map_sub, hyval]
      simp
    have hy : y ∈ F := by
      have hshift : (y - s) +ᵥ s ∈ (y - s) +ᵥ F :=
        Set.vadd_mem_vadd_set hs
      rw [hinv (y - s) hdelta] at hshift
      have heq : (y - s) +ᵥ s = y := by
        simp only [vadd_eq_add]
        abel
      rw [heq] at hshift
      exact hshift
    have hdist : dist z y ≤ M * ‖q‖ := by
      calc
        dist z y = ‖z - y‖ := dist_eq_norm z y
        _ = ‖-((ℓ s - ℓ z) • q)‖ := by dsimp [y]; congr 1; abel
        _ = |ℓ s - ℓ z| * ‖q‖ := by rw [norm_neg, norm_smul, Real.norm_eq_abs]
        _ ≤ M * ‖q‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg q)
    have hdist' : dist y z ≤ M * ‖q‖ := by simpa [dist_comm] using hdist
    exact ⟨y, hy, Metric.mem_ball.mpr (by dsimp [R]; linarith)⟩
  refine ⟨R, hR, ?_⟩
  intro z
  obtain ⟨d, hdD, hdBall⟩ := nearSet D hDinv hDM z
  obtain ⟨e, heE, heBall⟩ := nearSet E hEinv hEM z
  by_contra hnoFrontier
  have hballDisj : Disjoint (Metric.ball z R) (frontier D) :=
    Set.disjoint_left.mpr (by
      intro x hxBall hxFrontier
      exact hnoFrontier ⟨x, hxFrontier, by
        simpa [dist_comm] using Metric.mem_ball.mp hxBall⟩)
  rcases (Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      (convex_ball z R).isPreconnected hballDisj) with hinside | houtside
  · exact (Set.disjoint_left.mp hdisj)
      (interior_subset (hinside heBall)) heE
  · have hdnot : d ∉ D := by
      have hcompl : d ∈ Dᶜ := interior_subset (houtside hdBall)
      simpa using hcompl
    exact hdnot hdD

private theorem allColumns_uniformlyReady
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ)
    (htile : TilesOn K T Set.univ) (hcol : IsUnionOfColumns K δ T) :
    IsUniformlyReady K δ T := by
  obtain ⟨v, hv, hvmin⟩ := K.isPolygonal.isCompact.exists_isMinOn
    K.nonempty ℓ.continuous.continuousOn
  obtain ⟨R, hR, hbound⟩ := K.isPolygonal.isCompact.isBounded.exists_pos_norm_lt
  have hcover : (⋃ s : T, (s : Plane) +ᵥ K.support) = Set.univ := by
    rw [← closure_regularSupport_eq_supportUnion htile.2.1,
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile, closure_univ]
  refine ⟨R + ‖v‖, by positivity, ?_⟩
  intro x
  have hx : x ∈ ⋃ s : T, (s : Plane) +ᵥ K.support := by rw [hcover]; trivial
  obtain ⟨t, y, hy, hty⟩ := Set.mem_iUnion.mp hx
  let C := lineFibre δ T t
  have htC : (t : Plane) ∈ C := ⟨t.property, by simp⟩
  have hC : IsCenterColumn K δ C := hcol t t.property
  have hmin : ∀ s ∈ C, ℓ t ≤ ℓ s := by
    intro s hs
    have hs0 : ℓ (s - t) = 0 := by
      change s - t ∈ LinearMap.ker ℓ.toLinearMap
      rw [hker]
      exact hs.2
    rw [map_sub] at hs0
    linarith
  refine ⟨v + t, minimumFibre_extremalProperLink K δ T C ℓ hℓ hker htile
    (fun s hs => hs.1) hC.2.2.2 t htC hmin v hv hvmin, ?_⟩
  change (t : Plane) + y = x at hty
  have hdiff : x - (v + t) = y - v := by rw [← hty]; abel
  rw [dist_eq_norm, hdiff]
  exact (norm_sub_le y v).trans_lt (by linarith [hbound y hy])

private theorem unionColumns_carrier_isInvariant
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (S : Set Plane)
    (hcol : Tiling.Polygonal.IsUnionOfColumns K δ S) :
    Tiling.Polygonal.IsInvariantAlong
      (Tiling.Polygonal.regularSupport K S) δ := by
  classical
  let fibre : S → Set Plane := fun t => Tiling.Polygonal.lineFibre δ S t
  have hUnion : (⋃ t : S, fibre t) = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
      exact ht.1
    · intro hx
      refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      exact ⟨hx, by simp⟩
  let U : Set Plane := ⋃ t : S,
    Tiling.Polygonal.regularSupport K (fibre t)
  have hUinv : Tiling.Polygonal.IsInvariantAlong U δ := by
    intro u hu
    ext x
    constructor
    · rintro ⟨y, hyU, hxy⟩
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hyU
      have hxF : x ∈ u +ᵥ Tiling.Polygonal.regularSupport K (fibre t) :=
        Set.mem_vadd_set.mpr ⟨y, ht, hxy⟩
      exact Set.mem_iUnion.mpr
        ⟨t, ((hcol t.1 t.2).2.2.2 u hu).subset hxF⟩
    · intro hxU
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hxU
      have hxF : x ∈ u +ᵥ Tiling.Polygonal.regularSupport K (fibre t) :=
        ((hcol t.1 t.2).2.2.2 u hu).symm.subset ht
      obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.mp hxF
      exact Set.mem_vadd_set.mpr ⟨y, Set.mem_iUnion.mpr ⟨t, hy⟩, hxy⟩
  have hreg : Tiling.Polygonal.regularSupport K S = interior (closure U) := by
    calc
      Tiling.Polygonal.regularSupport K S =
          Tiling.Polygonal.regularSupport K (⋃ t : S, fibre t) := by
            exact congrArg (Tiling.Polygonal.regularSupport K) hUnion.symm
      _ = interior (closure U) := by
        simpa [U, fibre] using Tiling.Polygonal.regularSupport_iUnion K fibre
  intro u hu
  rw [hreg]
  calc
    u +ᵥ interior (closure U) = interior (u +ᵥ closure U) := by
      exact (interior_vadd u (closure U)).symm
    _ = interior (closure (u +ᵥ U)) := by rw [closure_vadd]
    _ = interior (closure U) := by rw [hUinv u hu]

private theorem componentCarrier_transverseDense
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (P : EarthquakeComponent K δ T) (ℓ : Plane →L[ℝ] ℝ)
    (hdense : ∃ M : ℝ, 0 < M ∧ ∀ a : ℝ, ∃ s ∈ P.centres, |ℓ s - a| ≤ M) :
    ∃ M : ℝ, 0 < M ∧ ∀ a : ℝ, ∃ s ∈ P.carrier, |ℓ s - a| ≤ M := by
  obtain ⟨v, hv⟩ := K.isPolygonal.interior_nonempty K.nonempty
  obtain ⟨M, hM, hpoints⟩ := hdense
  refine ⟨M, hM, ?_⟩
  intro a
  obtain ⟨s, hs, hsa⟩ := hpoints (a - ℓ v)
  have hraw : s + v ∈ openUnion K P.centres :=
    Set.mem_iUnion.mpr ⟨⟨s, hs⟩, Set.vadd_mem_vadd_set hv⟩
  have hopen : IsOpen (openUnion K P.centres) :=
    isOpen_iUnion fun s : P.centres => isOpen_interior.vadd (s : Plane)
  refine ⟨s + v, hopen.subset_interior_closure hraw, ?_⟩
  rw [map_add]
  have h : ℓ s + ℓ v - a = ℓ s - (a - ℓ v) := by ring
  rw [h]
  exact hsa

private theorem twoNoncolumns_uniformlyReady
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ) (hK : HasRationalSlopes K)
    (hδ : Module.finrank ℝ δ = 1) (hboundary : HasBoundaryDirection K δ)
    (hℓ : ℓ ≠ 0) (hker : LinearMap.ker ℓ.toLinearMap = δ)
    (htile : TilesOn K T Set.univ) (hnontrivial : HasNontrivialEarthquakeDecomposition K δ T)
    (P Q : EarthquakeComponent K δ T)
    (hP : P ∈ noncolumnComponents K δ T) (hQ : Q ∈ noncolumnComponents K δ T)
    (hPQ : P ≠ Q) : IsUniformlyReady K δ T := by
  have htwo := noncolumnComponent_twoSided K δ T ℓ hK hδ hboundary hℓ hker htile hnontrivial
  have hPdense := noncolumnComponent_transverseDense hK hδ hboundary ℓ hℓ hker
    htile hnontrivial P hP (htwo P hP)
  have hQdense := noncolumnComponent_transverseDense hK hδ hboundary ℓ hℓ hker
    htile hnontrivial Q hQ (htwo Q hQ)
  have hwhole : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hwholeInv : IsInvariantAlong (regularSupport K T) δ := by
    rw [hwhole]
    intro u _
    exact Set.vadd_set_univ
  have hPinv := component_isInvariant K δ T hδ htile.2.1 hwholeInv P
  have hQinv := component_isInvariant K δ T hδ htile.2.1 hwholeInv Q
  have hdisj : Disjoint P.carrier Q.carrier :=
    components_carriers_disjoint K δ T hδ htile.2.1 (Set.mem_univ P) (Set.mem_univ Q) hPQ
  obtain ⟨q, hq⟩ := nonzeroFunctional_surjective ℓ hℓ 1
  obtain ⟨R, hR, hnear⟩ := twoDisjointCylinders_frontierNear ℓ hker q hq
    isOpen_interior isOpen_interior hdisj hPinv hQinv
    (componentCarrier_transverseDense K δ T P ℓ hPdense)
    (componentCarrier_transverseDense K δ T Q ℓ hQdense)
  refine ⟨R, hR, ?_⟩
  intro z
  obtain ⟨a, ha, hza⟩ := hnear z
  have hPsub : P.centres ⊆ T := by rintro s ⟨u, _, rfl⟩; exact u.property
  exact ⟨a, invariantCarrier_frontier_isProperLink K δ T P.centres htile hPsub hPinv a ha, hza⟩

open Tiling.Approximation Tiling.RationalSlopes.Approximation in
/-- The old endpoint fans are actually constructed by FT on a finite alphabet
of realized old contacts together with the prototype's zero-displacement fan.
This has no global FLC or new-contact reflection premise. -/
private theorem oldContacts_finiteStars
    (K : PolygonalRegion) (P : PolyhedralCode) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hP : polyhedralSupport P = K.support) (hfinite : HasFiniteOffDirectionContacts K δ T) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ L : PolygonalRegion, L.support = deformedPolyhedralSupport P φ →
          (∀ w ∈ vertexSet K.support,
            SameGermAt K.openCarrier w L.openCarrier (deformPoint φ w)) ∧
          (∀ d ∈ oldOffDirectionContactAlphabet K δ T, ∀ w ∈ vertexSet K.support,
            SameGermAt (d +ᵥ K.openCarrier) w
              (deformPoint φ d +ᵥ L.openCarrier) (deformPoint φ w)) := by
  classical
  let D := insert 0 (oldOffDirectionContactAlphabet_finite hfinite).toFinset
  let W := K.isPolygonal.vertexSet_finite.toFinset
  obtain ⟨F, ε, hε, hstars⟩ := finiteStar_germs K P hP D W
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ L hL
  have hwW : ∀ w ∈ vertexSet K.support, w ∈ W :=
    fun w hw => K.isPolygonal.vertexSet_finite.mem_toFinset.mpr hw
  constructor
  · intro w hw
    have h := hstars φ hφ L hL 0 (by simp [D]) w (hwW w hw)
    have hzero : deformPoint φ 0 = 0 := (deformPointLinear φ).map_zero
    simpa only [zero_vadd, hzero] using h
  · intro d hd w hw
    have hdD : d ∈ D := Finset.mem_insert_of_mem
      ((oldOffDirectionContactAlphabet_finite hfinite).mem_toFinset.mpr hd)
    exact hstars φ hφ L hL d hdD w (hwW w hw)

private theorem regularSupport_nonempty
    (K : PolygonalRegion) (S : Set Plane) (hS : S.Nonempty) :
    (regularSupport K S).Nonempty := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨v, hv⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hopen : IsOpen (openUnion K S) :=
    isOpen_iUnion fun t : S => isOpen_interior.vadd (t : Plane)
  exact ⟨s + v, hopen.subset_interior_closure
    (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, Set.vadd_mem_vadd_set hv⟩)⟩

/-- Every nontrivial rational model is ready: an actual noncolumn carrier has
a transverse DR period and a nonempty frontier, while the all-column case
uses the direct extremal-link construction. This is independent of NR-2. -/
private theorem rational_nontrivial_uniformlyReady
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ)
    (hK : Tiling.RationalPolygonal.IsRelativelyRational K)
    (hδ : Module.finrank ℝ δ = 1) (hratδ : HasRationalDirection δ)
    (htile : TilesOn K T Set.univ)
    (hnontrivial : HasNontrivialEarthquakeDecomposition K δ T) :
    IsUniformlyReady K δ T := by
  classical
  by_cases hcol : T = columnPart K δ T
  · apply allColumns_uniformlyReady K δ T ℓ hℓ hker htile
    rw [hcol]
    exact columnPart_isUnionColumns K δ T hδ htile.2.1
  have hNC : ∃ P : EarthquakeComponent K δ T,
      P ∈ noncolumnComponents K δ T := by
    by_contra hnone
    apply hcol
    ext t
    constructor
    · intro ht
      let P : EarthquakeComponent K δ T :=
        (earthquakeGraph K δ T).connectedComponentMk ⟨t, ht⟩
      have hP : IsCenterColumn K δ P.centres := by
        by_contra hP
        exact hnone ⟨P, hP⟩
      exact Set.mem_iUnion.mpr ⟨⟨P, hP⟩, ⟨⟨t, ht⟩, rfl, rfl⟩⟩
    · intro ht
      obtain ⟨P, s, _, rfl⟩ := Set.mem_iUnion.mp ht
      exact s.property
  obtain ⟨P, hP⟩ := hNC
  obtain ⟨A, B, hAB⟩ := hnontrivial.resolve_left hcol
  obtain ⟨Q, hPQ⟩ : ∃ Q : EarthquakeComponent K δ T, P ≠ Q := by
    by_cases hPA : P = A
    · exact ⟨B, hPA ▸ hAB⟩
    · exact ⟨A, hPA⟩
  have hPinv : IsInvariantAlong P.carrier δ :=
    component_isInvariant K δ T hδ htile.2.1
      (by rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile]; intro u hu; simp) P
  have hPsub : P.centres ⊆ T := by rintro s ⟨u, _, rfl⟩; exact u.property
  have hproper : P.carrier ≠ Set.univ := by
    intro h
    have hdisj := components_carriers_disjoint K δ T hδ htile.2.1
      (Set.mem_univ P) (Set.mem_univ Q) hPQ
    change Disjoint P.carrier Q.carrier at hdisj
    obtain ⟨x, hx⟩ := regularSupport_nonempty K Q.centres
      (Q.nonempty_supp.image Subtype.val)
    exact Set.disjoint_left.mp hdisj (by rw [h]; trivial) hx
  have hfrontier : (frontier P.carrier).Nonempty := nonempty_frontier_iff.mpr
    ⟨regularSupport_nonempty K P.centres (P.nonempty_supp.image Subtype.val), hproper⟩
  obtain ⟨q, hq⟩ := rational_wholePlane_commonCarrierPeriod K δ T hK hδ hratδ htile
  exact invariantCarrier_transversePeriod_uniformlyReady K δ T P.centres htile
    hPsub hPinv hfrontier ℓ hker q hq.1 (hq.2.2 P hP)

/-- Indexed injectivity and forward saturation preserve an actual nontrivial
split. Only the forward invariant-subfamily partition is used; no converse
component correspondence is required. -/
private theorem twoComponents_forwardTransport
    (K L : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hδ : Module.finrank ℝ δ = 1)
    (htile : TilesOn K T Set.univ) (f : Plane → Plane) (hinj : Set.InjOn f T)
    (hmodel : TilesOn L (f '' T) Set.univ)
    (hforward : ∀ S ⊆ T, IsInvariantAlong (regularSupport K S) δ →
      IsInvariantAlong (regularSupport L (f '' S)) δ)
    (htwo : ∃ P Q : EarthquakeComponent K δ T, P ≠ Q) :
    ∃ A B : EarthquakeComponent L δ (f '' T), A ≠ B := by
  classical
  obtain ⟨P, Q, hPQ⟩ := htwo
  obtain ⟨x, hx⟩ := P.nonempty_supp
  obtain ⟨y, hy⟩ := Q.nonempty_supp
  have hPsub : P.centres ⊆ T := by rintro s ⟨u, _, rfl⟩; exact u.property
  have hyP : (y : Plane) ∉ P.centres := by
    rintro ⟨z, hz, hzy⟩
    have hzy' : z = y := Subtype.ext hzy
    rw [hzy'] at hz
    exact hPQ (SimpleGraph.ConnectedComponent.eq_of_common_vertex hz hy)
  have hfull : IsInvariantAlong (regularSupport K T) δ := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile]
    intro u hu
    simp
  have hPinv := component_isInvariant K δ T hδ htile.2.1 hfull P
  have hSsub : f '' P.centres ⊆ f '' T := Set.image_mono hPsub
  have hSinv := hforward P.centres hPsub hPinv
  let X : {s : Plane // s ∈ f '' T} := ⟨f x, Set.mem_image_of_mem f x.property⟩
  let Y : {s : Plane // s ∈ f '' T} := ⟨f y, Set.mem_image_of_mem f y.property⟩
  let A : EarthquakeComponent L δ (f '' T) := (earthquakeGraph L δ (f '' T)).connectedComponentMk X
  let B : EarthquakeComponent L δ (f '' T) := (earthquakeGraph L δ (f '' T)).connectedComponentMk Y
  have hxA : f x ∈ A.centres := ⟨X, rfl, rfl⟩
  have hxS : f x ∈ f '' P.centres := Set.mem_image_of_mem f ⟨x, hx, rfl⟩
  have hmodelFull : IsInvariantAlong (regularSupport L (f '' T)) δ := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) hmodel]
    intro u hu
    simp
  have hAS : A.centres ⊆ f '' P.centres := by
    obtain hdisj | hsub := invariantSubfamily_isUnionComponents L δ (f '' T)
      (f '' P.centres) hδ hmodel.2.1 hmodelFull hSsub hSinv A
    · exact (Set.disjoint_left.mp hdisj hxA hxS).elim
    · exact hsub
  refine ⟨A, B, ?_⟩
  intro hAB
  have hyA : f y ∈ A.centres := hAB.symm ▸ (show f y ∈ B.centres from ⟨Y, rfl, rfl⟩)
  obtain ⟨z, hz, hzy⟩ := hAS hyA
  exact hyP (hinj (hPsub hz) y.property hzy ▸ hz)

open Tiling.Approximation in
/-- A model-ready family with genuine old proper-link lifts gives source
readiness using only LT's estimate relative to those old links. An arbitrary
source point is compared to an actual nearby translated intrinsic vertex;
no global order or inverse-deformation assertion is used. -/
private theorem uniformlyReady_of_actualLinkLifts
    (K L : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hker : LinearMap.ker ℓ.toLinearMap = δ)
    (htile : TilesOn K T Set.univ) (φ : ℝ →ₗ[ℚ] ℚ)
    (hmodel : IsUniformlyReady L δ (deformPoint φ '' T))
    (hlift : ∀ b : Plane, IsProperLink L δ (deformPoint φ '' T) b →
      ∃ a : Plane, IsProperLink K δ T a ∧ deformPoint φ a - b ∈ δ)
    (hlower : ∀ a : Plane, IsProperLink K δ T a →
      ∀ v ∈ translatedVertices K T,
        |ℓ (v - a)| / 2 ≤ |ℓ (deformPoint φ (v - a))|) :
    IsUniformlyReady K δ T := by
  obtain ⟨w, hw, _⟩ := intrinsic_minimumVertex K ℓ hℓ
  obtain ⟨B, hB, hbound⟩ := K.isPolygonal.isCompact.isBounded.exists_pos_norm_lt
  obtain ⟨R, hR, hnear⟩ := hmodel
  obtain ⟨q, hq⟩ := nonzeroFunctional_surjective ℓ hℓ 1
  let D := ‖ℓ‖ * (B + ‖w‖ + 2 * R)
  have hcover : (⋃ t : T, (t : Plane) +ᵥ K.support) = Set.univ := by
    rw [← closure_regularSupport_eq_supportUnion htile.2.1,
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile, closure_univ]
  refine ⟨D * ‖q‖ + 1, by dsimp [D]; positivity, ?_⟩
  intro x
  have hx : x ∈ ⋃ t : T, (t : Plane) +ᵥ K.support := by rw [hcover]; trivial
  obtain ⟨t, k, hk, htk⟩ := Set.mem_iUnion.mp hx
  let v : Plane := w + t
  have hv : v ∈ translatedVertices K T := Set.mem_add.mpr ⟨w, hw, t, t.property, rfl⟩
  obtain ⟨b, hb, hvb⟩ := hnear (deformPoint φ v)
  obtain ⟨a, ha, hab⟩ := hlift b hb
  have habzero : ℓ (deformPoint φ a - b) = 0 := by
    exact LinearMap.mem_ker.mp (hker.symm ▸ hab)
  have himage : ℓ (deformPoint φ (v - a)) = ℓ (deformPoint φ v - b) := by
    change ℓ ((deformPointLinear φ) (v - a)) = ℓ (deformPoint φ v - b)
    rw [(deformPointLinear φ).map_sub, map_sub, map_sub]
    change ℓ (deformPoint φ v) - ℓ (deformPoint φ a) = ℓ (deformPoint φ v) - ℓ b
    rw [map_sub] at habzero
    linarith
  have hsmall : |ℓ (deformPoint φ (v - a))| ≤ ‖ℓ‖ * R := by
    rw [himage]
    calc
      |ℓ (deformPoint φ v - b)| = ‖ℓ (deformPoint φ v - b)‖ := Real.norm_eq_abs _ |>.symm
      _ ≤ ‖ℓ‖ * ‖deformPoint φ v - b‖ := ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * R := mul_le_mul_of_nonneg_left
        (le_of_lt (by simpa [dist_eq_norm] using hvb)) (norm_nonneg ℓ)
  have hsource : |ℓ (v - a)| ≤ 2 * ‖ℓ‖ * R := by
    have h := hlower a ha v hv
    linarith
  have hxv : ‖x - v‖ ≤ B + ‖w‖ := by
    change (t : Plane) + k = x at htk
    have hdiff : x - v = k - w := by dsimp [v]; rw [← htk]; abel
    rw [hdiff]
    exact (norm_sub_le _ _).trans (by linarith [hbound k hk])
  have hxa : |ℓ (x - a)| ≤ D := by
    have hxnorm : |ℓ (x - v)| ≤ ‖ℓ‖ * ‖x - v‖ := by
      simpa only [Real.norm_eq_abs] using ℓ.le_opNorm (x - v)
    have heq : ℓ (x - a) = ℓ (x - v) + ℓ (v - a) := by rw [map_sub, map_sub, map_sub]; ring
    rw [heq]
    calc
      |ℓ (x - v) + ℓ (v - a)| ≤ |ℓ (x - v)| + |ℓ (v - a)| := abs_add_le _ _
      _ ≤ ‖ℓ‖ * (B + ‖w‖) + 2 * ‖ℓ‖ * R := add_le_add
        (hxnorm.trans
          (mul_le_mul_of_nonneg_left hxv (norm_nonneg ℓ))) hsource
      _ = D := by dsimp [D]; ring
  let y := x - ℓ (x - a) • q
  have hya : y - a ∈ δ := by
    rw [← hker]
    change ℓ (y - a) = 0
    change ℓ ((x - ℓ (x - a) • q) - a) = 0
    rw [map_sub, map_sub, map_smul, hq, map_sub]
    ring
  have hyproper : IsProperLink K δ T y := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.mp hz
    apply ha
    refine Set.mem_vadd_set.mpr ⟨(y - a) + u, δ.add_mem hya hu, ?_⟩
    change a + ((y - a) + u) = y + u
    abel
  refine ⟨y, hyproper, ?_⟩
  calc
    dist x y = |ℓ (x - a)| * ‖q‖ := by
      rw [dist_eq_norm]
      have heq : x - y = ℓ (x - a) • q := by dsimp [y]; abel
      rw [heq, norm_smul, Real.norm_eq_abs]
    _ ≤ D * ‖q‖ := mul_le_mul_of_nonneg_right hxa (norm_nonneg q)
    _ < D * ‖q‖ + 1 := by linarith

/-- A locally finite closed union has locally finite boundary if every
member has finite boundary. This is applied to actual scalar edge sections,
not to the generally infinite set of plane boundary points. -/
private theorem locallyFinite_closedUnion_finiteLocalFrontier
    {ι : Type*} (S : ι → Set ℝ) (hclosed : ∀ i, IsClosed (S i))
    (hloc : LocallyFinite S) (hfinite : ∀ i, (frontier (S i)).Finite) :
    IsClosed (⋃ i, S i) ∧
      ∀ x : ℝ, ∃ r : ℝ, 0 < r ∧
        (frontier (⋃ i, S i) ∩ Metric.ball x r).Finite := by
  have hUclosed : IsClosed (⋃ i, S i) := hloc.isClosed_iUnion hclosed
  refine ⟨hUclosed, ?_⟩
  intro x
  obtain ⟨V, hV, hVfinite⟩ := hloc x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r, hr, (hVfinite.biUnion fun i _ => hfinite i).subset ?_⟩
  intro y hy
  have hyU : y ∈ ⋃ i, S i := hUclosed.closure_subset hy.1.1
  obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyU
  apply Set.mem_iUnion.mpr
  refine ⟨i, Set.mem_iUnion.mpr ⟨⟨y, hyi, hball hy.2⟩, ?_⟩⟩
  refine ⟨subset_closure hyi, ?_⟩
  intro hyint
  exact hy.1.2 (interior_mono (Set.subset_iUnion S i) hyint)

private theorem packing_tileSupports_locallyFinite
    (K : PolygonalRegion) (T : Set Plane)
    (hp : IsPacking K.prototileFamily (K.placements T)) :
    LocallyFinite (fun t : T => (t : Plane) +ᵥ K.support) := by
  let P : PolygonalProtoTiling Unit :=
    { prototiles := K.prototileFamily
      placements := K.placements T
      isPolygonal := fun _ => K.isPolygonal }
  let toPlacement : T → P.placements := fun t => ⟨(t, ()), t.2⟩
  have hinj : Function.Injective toPlacement := by
    intro s t hst
    exact Subtype.ext (congrArg (fun i : P.placements => i.1.1) hst)
  exact (P.locallyFinite_placedTile hp).comp_injective hinj

private theorem packing_tileBoundaries_isClosed
    (K : PolygonalRegion) (T : Set Plane)
    (hp : IsPacking K.prototileFamily (K.placements T)) :
    IsClosed (⋃ t : T, (t : Plane) +ᵥ frontier K.support) := by
  have hloc := packing_tileSupports_locallyFinite K T hp
  have hfront : LocallyFinite (fun t : T => (t : Plane) +ᵥ frontier K.support) :=
    hloc.subset fun t => Set.vadd_set_mono K.isPolygonal.isClosed.frontier_subset
  exact hfront.isClosed_iUnion fun t => isClosed_frontier.vadd (t : Plane)

private theorem compactConvexLineSection_frontier_finite
    (D : Set Plane) (hcompact : IsCompact D) (hconvex : Convex ℝ D)
    (a e : Plane) (he : e ≠ 0) :
    (frontier {r : ℝ | a + r • e ∈ D}).Finite := by
  let f : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap a (a + e)
  have hf (r : ℝ) : f r = a + r • e := by
    simp [f, AffineMap.lineMap_apply_module', add_comm]
  have hclosedEmbedding : Topology.IsClosedEmbedding f := by
    have hsmul : Topology.IsClosedEmbedding (fun r : ℝ => r • e) :=
      isClosedEmbedding_smul_left he
    have h := (Homeomorph.addLeft a).isClosedEmbedding.comp hsmul
    convert h using 1
    funext r
    exact hf r
  have hprecompact := hclosedEmbedding.isCompact_preimage hcompact
  by_cases hne : (f ⁻¹' D).Nonempty
  · have hconnected : IsConnected (f ⁻¹' D) :=
      ⟨hne, (hconvex.affine_preimage f).isPreconnected⟩
    have heq := eq_Icc_of_connected_compact hconnected hprecompact
    have hle : sInf (f ⁻¹' D) ≤ sSup (f ⁻¹' D) :=
      (hprecompact.isLeast_sInf hne).2 (hprecompact.sSup_mem hne)
    have hfinite : (frontier (f ⁻¹' D)).Finite := by
      rw [heq, frontier_Icc hle]
      exact Set.toFinite _
    simpa only [Set.preimage, hf] using hfinite
  · have hempty : f ⁻¹' D = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hfinite : (frontier (f ⁻¹' D)).Finite := by rw [hempty]; simp
    simpa only [Set.preimage, hf] using hfinite

/-- Actual old boundary sections are locally finite unions of closed
intervals and points: the pieces are scalar preimages of the intrinsic
finite boundary segments in the locally finite packing. -/
private theorem packing_boundaryLineSection_localFiniteFrontier
    (K : PolygonalRegion) (T : Set Plane)
    (hp : IsPacking K.prototileFamily (K.placements T))
    (a e : Plane) (he : e ≠ 0) :
    let A : Set ℝ := {r | a + r • e ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support}
    IsClosed A ∧ ∀ x : ℝ, ∃ r : ℝ, 0 < r ∧ (frontier A ∩ Metric.ball x r).Finite := by
  classical
  obtain ⟨F, hF, hboundary⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  let E := {d : Plane × Plane // d ∈ F}
  let D : T × E → Set Plane := fun i =>
    (i.1 : Plane) +ᵥ segment ℝ i.2.1.1 i.2.1.2
  have hDsub (i : T × E) : D i ⊆ (i.1 : Plane) +ᵥ K.support :=
    Set.vadd_set_mono ((hF i.2.1 i.2.2).2.2.2.trans K.isPolygonal.isClosed.frontier_subset)
  have hDloc : LocallyFinite D := by
    intro z
    obtain ⟨V, hV, hVfinite⟩ := packing_tileSupports_locallyFinite K T hp z
    refine ⟨V, hV, (hVfinite.prod (Set.toFinite (Set.univ : Set E))).subset ?_⟩
    intro i hi
    obtain ⟨w, hw, hwV⟩ := hi
    exact ⟨⟨w, hDsub i hw, hwV⟩, Set.mem_univ _⟩
  have hunion : (⋃ i, D i) = ⋃ t : T, (t : Plane) +ᵥ frontier K.support := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨t, d⟩, hz⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨t,
        Set.vadd_set_mono (hF d.1 d.2).2.2.2 hz⟩
    · intro hz
      obtain ⟨t, k, hk, htk⟩ := Set.mem_iUnion.mp hz
      rw [hboundary] at hk
      obtain ⟨d, hd, hkd⟩ := Set.mem_iUnion₂.mp hk
      exact Set.mem_iUnion.mpr ⟨(t, ⟨d, hd⟩),
        Set.mem_vadd_set.mpr ⟨k, hkd, htk⟩⟩
  let p : ℝ → Plane := fun r => a + r • e
  have hpcont : Continuous p := continuous_const.add (continuous_id.smul continuous_const)
  have hDcompact (i : T × E) : IsCompact (D i) := by
    have hsegment : IsCompact (segment ℝ i.2.1.1 i.2.1.2) := by
      rw [segment_eq_image_lineMap]
      exact isCompact_Icc.image AffineMap.lineMap_continuous
    exact hsegment.vadd (i.1 : Plane)
  have hsections := locallyFinite_closedUnion_finiteLocalFrontier
    (fun i => p ⁻¹' D i)
    (fun i => (hDcompact i).isClosed.preimage hpcont)
    (hDloc.preimage_continuous hpcont)
    (fun i => compactConvexLineSection_frontier_finite (D i)
      (hDcompact i)
      ((convex_segment (𝕜 := ℝ) i.2.1.1 i.2.1.2).vadd (i.1 : Plane)) a e he)
  have hscalar : (⋃ i, p ⁻¹' D i) =
      {r : ℝ | a + r • e ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support} := by
    rw [← Set.preimage_iUnion, hunion]
    rfl
  simpa only [hscalar] using hsections

/-- The genuine one-dimensional endpoint alternative at an isolated boundary
value. Isolated points of the closed section are deliberately excluded by
working with the frontier of its interior. -/
private theorem closedScalarSection_endpointRays
    (A : Set ℝ) (hA : IsClosed A) (x r : ℝ) (hr : 0 < r)
    (hx : x ∈ frontier (interior A))
    (hisolated : ∀ y ∈ Set.Ioo (x - r) (x + r), y ∈ frontier A → y = x) :
    (Set.Ioo (x - r) x ⊆ A ∧ Set.Ioo x (x + r) ⊆ Aᶜ) ∨
      (Set.Ioo (x - r) x ⊆ Aᶜ ∧ Set.Ioo x (x + r) ⊆ A) := by
  have hxA : x ∈ A := hA.closure_subset (closure_mono interior_subset hx.1)
  have hxnot : x ∉ interior A := by simpa only [interior_interior] using hx.2
  have hleft : Disjoint (Set.Ioo (x - r) x) (frontier A) := by
    apply Set.disjoint_left.mpr
    intro y hy hyf
    exact (ne_of_lt hy.2) (hisolated y ⟨hy.1, by linarith [hy.2]⟩ hyf)
  have hright : Disjoint (Set.Ioo x (x + r)) (frontier A) := by
    apply Set.disjoint_left.mpr
    intro y hy hyf
    exact (ne_of_gt hy.1) (hisolated y ⟨by linarith [hy.1], hy.2⟩ hyf)
  have hL := Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
    (isPreconnected_Ioo : IsPreconnected (Set.Ioo (x - r) x)) hleft
  have hR := Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
    (isPreconnected_Ioo : IsPreconnected (Set.Ioo x (x + r))) hright
  rcases hL with hLin | hLout <;> rcases hR with hRin | hRout
  · have hwhole : Set.Ioo (x - r) (x + r) ⊆ A := by
      intro y hy
      rcases lt_trichotomy y x with hlt | heq | hgt
      · exact interior_subset (hLin ⟨hy.1, hlt⟩)
      · exact heq ▸ hxA
      · exact interior_subset (hRin ⟨hgt, hy.2⟩)
    exact (hxnot (interior_maximal hwhole isOpen_Ioo ⟨by linarith, by linarith⟩)).elim
  · exact Or.inl ⟨fun y hy => interior_subset (hLin hy),
      fun y hy => interior_subset (hRout hy)⟩
  · exact Or.inr ⟨fun y hy => interior_subset (hLout hy),
      fun y hy => interior_subset (hRin hy)⟩
  · obtain ⟨y, hy, hyA⟩ := mem_closure_iff.mp hx.1
      (Set.Ioo (x - r) (x + r)) isOpen_Ioo ⟨by linarith, by linarith⟩
    rcases lt_trichotomy y x with hlt | heq | hgt
    · exact (interior_subset (hLout ⟨hy.1, hlt⟩) (interior_subset hyA)).elim
    · exact (hxnot (heq ▸ hyA)).elim
    · exact (interior_subset (hRout ⟨hgt, hy.2⟩) (interior_subset hyA)).elim

/-- Local finite-boundary sections with an interior seed cannot stop if all
their actual one-sided endpoint alternatives have been excluded. -/
private theorem closedScalarSection_eq_univ_of_no_endpoint
    (A : Set ℝ) (hA : IsClosed A)
    (hlocal : ∀ x : ℝ, ∃ r : ℝ, 0 < r ∧ (frontier A ∩ Metric.ball x r).Finite)
    (hseed : (interior A).Nonempty)
    (hno : ∀ x r : ℝ, 0 < r →
      ((Set.Ioo (x - r) x ⊆ A ∧ Set.Ioo x (x + r) ⊆ Aᶜ) ∨
        (Set.Ioo (x - r) x ⊆ Aᶜ ∧ Set.Ioo x (x + r) ⊆ A)) → False) :
    A = Set.univ := by
  have hfrontierEmpty : frontier (interior A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨R, hR, hfinite⟩ := hlocal x
    let F := (frontier A ∩ Metric.ball x R) \ {x}
    have hF : IsClosed F := hfinite.sdiff.isClosed
    have hxF : x ∈ Fᶜ := by simp [F]
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF.isOpen_compl x hxF
    let r := min R ε
    have hr : 0 < r := lt_min hR hε
    have hisolated : ∀ y ∈ Set.Ioo (x - r) (x + r), y ∈ frontier A → y = x := by
      intro y hy hyf
      by_contra hyx
      have hdist : dist y x < r := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hy.1, hy.2]
      have hyR : y ∈ Metric.ball x R := Metric.mem_ball.mpr
        (hdist.trans_le (min_le_left _ _))
      have hyε : y ∈ Metric.ball x ε := Metric.mem_ball.mpr
        (hdist.trans_le (min_le_right _ _))
      exact hball hyε ⟨⟨hyf, hyR⟩, by simpa using hyx⟩
    exact hno x r hr (closedScalarSection_endpointRays A hA x r hr hx hisolated)
  have hclopen : IsClopen (interior A) := isClopen_iff_frontier_eq_empty.mpr hfrontierEmpty
  have hinterior := hclopen.eq_univ hseed
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← hinterior]
  exact interior_subset

private theorem sameGerm_shortRay
    {D E : Set Plane} {x y e : Plane} {R : ℝ}
    (hg : Tiling.Polygonal.SameGermAt D x E y) (hR : 0 < R)
    (hray : ∀ q ∈ Set.Ioo (0 : ℝ) R, x + q • e ∈ D) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Set.Ioo (0 : ℝ) r, y + q • e ∈ E := by
  change D =ᶠ[𝓝 x] ((x - y) +ᵥ E) at hg
  obtain ⟨ε, hε, heq⟩ := Metric.eventually_nhds_iff.mp hg
  let r := min R (ε / (‖e‖ + 1))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min hR (div_pos hε (by positivity))
  refine ⟨r, hr, ?_⟩
  intro q hq
  have hqR : q ∈ Set.Ioo (0 : ℝ) R := ⟨hq.1, lt_of_lt_of_le hq.2 (min_le_left _ _)⟩
  have hnorm : dist x (x + q • e) < ε := by
    rw [dist_eq_norm]
    have hnorm' : ‖x - (x + q • e)‖ = q * ‖e‖ := by
      rw [show x - (x + q • e) = -(q • e) by abel, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos hq.1]
    rw [hnorm']
    have hqε : q < ε / (‖e‖ + 1) := lt_of_lt_of_le hq.2 (min_le_right _ _)
    calc
      q * ‖e‖ ≤ q * (‖e‖ + 1) := by nlinarith [hq.1, norm_nonneg e]
      _ < ε := (lt_div_iff₀ (by positivity : 0 < ‖e‖ + 1)).mp hqε
  have hmem := heq (Metric.mem_ball.mpr (by simpa only [dist_comm] using hnorm))
  have htranslated : x + q • e ∈ (x - y) +ᵥ E := hmem.mp (hray q hqR)
  have htranslated' : -(x - y) + (x + q • e) ∈ E :=
    (Set.mem_vadd_set_iff_neg_vadd_mem).mp htranslated
  have hpoint : -(x - y) + (x + q • e) = y + q • e := by abel
  rwa [hpoint] at htranslated'

private theorem properLink_noInteriorOwner
    {L : PolygonalRegion} {T : Set Plane} {δ : Submodule ℝ Plane}
    {b z t : Plane} (htile : Tiling.Polygonal.TilesOn L T Set.univ)
    (hlink : IsProperLink L δ T b) (hzline : z ∈ b +ᵥ (δ : Set Plane))
    (ht : t ∈ T) (hzopen : z ∈ t +ᵥ L.openCarrier) : False := by
  have hp := htile.2.1
  have hzfrontUnion : z ∈ ⋃ s : T, (s : Plane) +ᵥ frontier L.support := hlink hzline
  have hdisj : Disjoint (t +ᵥ L.openCarrier)
      (⋃ s : T, (s : Plane) +ᵥ frontier L.support) := by
    rw [Set.disjoint_iUnion_right]
    intro s
    have hfront : (s : Plane) +ᵥ frontier L.support =
        frontier ((s : Plane) +ᵥ L.support) := by
      change ⇑(Homeomorph.addLeft (s : Plane)) '' frontier L.support =
        frontier (⇑(Homeomorph.addLeft (s : Plane)) '' L.support)
      exact (Homeomorph.addLeft (s : Plane)).image_frontier L.support
    rw [hfront]
    by_cases hst : t = (s : Plane)
    · subst t
      simpa only [PolygonalRegion.openCarrier, interior_vadd] using
        (disjoint_interior_frontier : Disjoint
          (interior ((s : Plane) +ᵥ L.support))
          (frontier ((s : Plane) +ᵥ L.support)))
    · have hd := (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint L T).mp
        hp ht s.property hst
      have hdclosed := hd.closure_right (isOpen_interior.vadd t)
      rw [closure_vadd, PolygonalRegion.openCarrier, L.isPolygonal.closure_interior] at hdclosed
      exact hdclosed.mono_right (L.isPolygonal.isClosed.vadd s.val).frontier_subset
  exact (Set.disjoint_left.mp hdisj) hzopen hzfrontUnion

private theorem endpointRay_germs_contradict_properLink
    (K L : PolygonalRegion) (T Tnew : Set Plane) (δ : Submodule ℝ Plane)
    (φ : ℝ →ₗ[ℚ] ℚ) (v e b : Plane) (R : ℝ)
    (hδ : Module.finrank ℝ δ = 1) (he : e ∈ δ) (he0 : e ≠ 0)
    (htile : Tiling.Polygonal.TilesOn K T Set.univ) (hR : 0 < R)
    (hin : ∀ q ∈ Set.Ioo (0 : ℝ) R,
      v - q • e ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
    (hout : ∀ q ∈ Set.Ioo (0 : ℝ) R,
      v + q • e ∉ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
    (htileNew : Tiling.Polygonal.TilesOn L Tnew Set.univ)
    (hTnew : Tnew = Tiling.Approximation.deformPoint φ '' T)
    (hlink : IsProperLink L δ Tnew b)
    (hbase : Tiling.Approximation.deformPoint φ v - b ∈ δ)
    (hsingle : ∀ w ∈ vertexSet K.support,
      Tiling.Polygonal.SameGermAt K.openCarrier w L.openCarrier
        (Tiling.Approximation.deformPoint φ w))
    (hcontactGerm : ∀ η : Submodule ℝ Plane, Module.finrank ℝ η = 1 →
      Tiling.Polygonal.HasBoundaryDirection K η → η ≠ δ →
      ∀ u s : Plane, u ∈ T → s ∈ T → u ≠ s →
      ProperEdgeContactAlong K η u s → ∀ w ∈ vertexSet K.support,
      Tiling.Polygonal.SameGermAt ((u - s) +ᵥ K.openCarrier) w
        ((Tiling.Approximation.deformPoint φ (u - s)) +ᵥ L.openCarrier)
        (Tiling.Approximation.deformPoint φ w)) :
    False := by
  obtain ⟨u, hu, _, ⟨r, hr, hownerRay⟩, hcase⟩ :=
    Tiling.RationalSlopes.endpointRay_ownedInterior_withContact K δ T v e R
      hδ he he0 htile hR hin hout
  by_cases hvVertex : v ∈ (u : Plane) +ᵥ vertexSet K.support
  · obtain ⟨w, hw, hvw⟩ := Set.mem_vadd_set.mp hvVertex
    have hvw' : v = (u : Plane) + w := hvw.symm
    have hsource : ∀ q ∈ Set.Ioo (0 : ℝ) r, w + q • e ∈ K.openCarrier := by
      intro q hq
      have howner := hownerRay q hq
      have heq : v + q • e = (u : Plane) + (w + q • e) := by rw [hvw']; abel
      rw [heq] at howner
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using howner
    obtain ⟨r', hr', htarget⟩ := sameGerm_shortRay (hsingle w hw) hr hsource
    let q := min r' R / 2
    have hqpos : 0 < q := by dsimp [q]; positivity
    have hqr' : q < r' := by dsimp [q]; have := min_le_left r' R; linarith
    have hqR : q < R := by dsimp [q]; have := min_le_right r' R; linarith
    have hqmem : q ∈ Set.Ioo (0 : ℝ) r' := ⟨hqpos, hqr'⟩
    have hline : Tiling.Approximation.deformPoint φ v + q • e ∈
        b +ᵥ (δ : Set Plane) := by
      apply Set.mem_vadd_set.mpr
      refine ⟨Tiling.Approximation.deformPoint φ v - b + q • e, δ.add_mem hbase (δ.smul_mem q he), ?_⟩
      simp only [vadd_eq_add]
      abel
    have hnewopen : Tiling.Approximation.deformPoint φ v + q • e ∈
        (Tiling.Approximation.deformPoint φ u) +ᵥ L.openCarrier := by
      have hwopen := htarget q hqmem
      have hvmap : Tiling.Approximation.deformPoint φ v =
          Tiling.Approximation.deformPoint φ u + Tiling.Approximation.deformPoint φ w := by
        rw [hvw']
        exact (Tiling.Approximation.deformPointLinear φ).map_add u w
      apply Set.mem_vadd_set.mpr
      refine ⟨Tiling.Approximation.deformPoint φ w + q • e, hwopen, ?_⟩
      rw [vadd_eq_add, hvmap]
      abel
    have huNew : Tiling.Approximation.deformPoint φ u ∈ Tnew := by
      rw [hTnew]
      exact Set.mem_image_of_mem _ hu
    exact properLink_noInteriorOwner htileNew hlink hline huNew hnewopen
  · rcases hcase with hvertex | ⟨η, hη, hηboundary, hηδ, s, hs, hvs,
      hcontact, _, _, _, _, _, _⟩
    · exact hvVertex hvertex
    · have hus : u ≠ s := by
        intro hus
        apply hvVertex
        simpa [hus] using hvs
      obtain ⟨w, hw, hvsw⟩ := Set.mem_vadd_set.mp hvs
      have hvsw' : v = (s : Plane) + w := hvsw.symm
      have hsource : ∀ q ∈ Set.Ioo (0 : ℝ) r,
          w + q • e ∈ (u - s) +ᵥ K.openCarrier := by
        intro q hq
        have howner := hownerRay q hq
        have hK : v + q • e - u ∈ K.openCarrier := by
          have heq : v + q • e = (u : Plane) + (v + q • e - u) := by abel
          rw [heq] at howner
          have howner' : -(u : Plane) + (v + q • e) ∈ K.openCarrier := by
            simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using howner
          have heq' : -(u : Plane) + (v + q • e) = v + q • e - u := by abel
          rw [heq'] at howner'
          exact howner'
        apply Set.mem_vadd_set.mpr
        refine ⟨v + q • e - u, hK, ?_⟩
        change (u - s) + (v + q • e - u) = w + q • e
        rw [hvsw']
        abel
      obtain ⟨r', hr', htarget⟩ :=
        sameGerm_shortRay
          (hcontactGerm η hη hηboundary hηδ u s hu hs hus hcontact w hw) hr hsource
      let q := min r' R / 2
      have hqpos : 0 < q := by dsimp [q]; positivity
      have hqr' : q < r' := by dsimp [q]; have := min_le_left r' R; linarith
      have hqR : q < R := by dsimp [q]; have := min_le_right r' R; linarith
      have hqmem : q ∈ Set.Ioo (0 : ℝ) r' := ⟨hqpos, hqr'⟩
      have hline : Tiling.Approximation.deformPoint φ v + q • e ∈
          b +ᵥ (δ : Set Plane) := by
        apply Set.mem_vadd_set.mpr
        refine ⟨Tiling.Approximation.deformPoint φ v - b + q • e,
          δ.add_mem hbase (δ.smul_mem q he), ?_⟩
        simp only [vadd_eq_add]
        abel
      have hnewopen : Tiling.Approximation.deformPoint φ v + q • e ∈
          (Tiling.Approximation.deformPoint φ u) +ᵥ L.openCarrier := by
        have hwopen := htarget q hqmem
        have hvmap : Tiling.Approximation.deformPoint φ v =
            Tiling.Approximation.deformPoint φ s + Tiling.Approximation.deformPoint φ w := by
          rw [hvsw']
          exact (Tiling.Approximation.deformPointLinear φ).map_add s w
        have husmap : Tiling.Approximation.deformPoint φ (u - s) =
            Tiling.Approximation.deformPoint φ u - Tiling.Approximation.deformPoint φ s :=
            (Tiling.Approximation.deformPointLinear φ).map_sub u s
        have hwshift :
            -(Tiling.Approximation.deformPoint φ (u - s)) +
              (Tiling.Approximation.deformPoint φ w + q • e) ∈ L.openCarrier :=
          Set.mem_vadd_set_iff_neg_vadd_mem.mp hwopen
        have hshiftEq :
            -(Tiling.Approximation.deformPoint φ (u - s)) +
              (Tiling.Approximation.deformPoint φ w + q • e) =
                -(Tiling.Approximation.deformPoint φ u) +
                  (Tiling.Approximation.deformPoint φ v + q • e) := by
          rw [husmap, hvmap]
          abel
        rw [hshiftEq] at hwshift
        apply Set.mem_vadd_set.mpr
        refine ⟨-(Tiling.Approximation.deformPoint φ u) +
          (Tiling.Approximation.deformPoint φ v + q • e), hwshift, ?_⟩
        simp only [vadd_eq_add]
        abel
      have huNew : Tiling.Approximation.deformPoint φ u ∈ Tnew := by
        rw [hTnew]
        exact Set.mem_image_of_mem _ hu
      exact properLink_noInteriorOwner htileNew hlink hline huNew hnewopen

open Tiling.Approximation in
/-- An actual old boundary interval on the rational-normal preimage of a
model proper link continues to the whole old line. The proof constructs the
locally finite scalar section and excludes both orientations of each real
endpoint with the prototype and realized-old-contact fans. -/
private theorem boundaryLine_seed_isProperLink
    (K L : PolygonalRegion) (T : Set Plane) (δ : Submodule ℝ Plane)
    (n : RationalNormal) (hn : normalDirection n = δ) (φ : ℝ →ₗ[ℚ] ℚ)
    (a e b : Plane) (hδ : Module.finrank ℝ δ = 1) (he : e ∈ δ) (he0 : e ≠ 0)
    (htile : TilesOn K T Set.univ) (htileNew : TilesOn L (deformPoint φ '' T) Set.univ)
    (hlink : IsProperLink L δ (deformPoint φ '' T) b)
    (hbase : deformPoint φ a - b ∈ δ)
    (hseed : (interior {r : ℝ | a + r • e ∈
      ⋃ t : T, (t : Plane) +ᵥ frontier K.support}).Nonempty)
    (hsingle : ∀ w ∈ vertexSet K.support,
      SameGermAt K.openCarrier w L.openCarrier (deformPoint φ w))
    (hstars : ∀ d ∈ oldOffDirectionContactAlphabet K δ T, ∀ w ∈ vertexSet K.support,
      SameGermAt (d +ᵥ K.openCarrier) w
        (deformPoint φ d +ᵥ L.openCarrier) (deformPoint φ w)) :
    IsProperLink K δ T a := by
  let A : Set ℝ := {r | a + r • e ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support}
  obtain ⟨hAclosed, hAlocal⟩ := packing_boundaryLineSection_localFiniteFrontier
    K T htile.2.1 a e he0
  have hcontact : ∀ η : Submodule ℝ Plane, Module.finrank ℝ η = 1 →
      HasBoundaryDirection K η → η ≠ δ →
      ∀ u s : Plane, u ∈ T → s ∈ T → u ≠ s →
      ProperEdgeContactAlong K η u s → ∀ w ∈ vertexSet K.support,
      SameGermAt ((u - s) +ᵥ K.openCarrier) w
        (deformPoint φ (u - s) +ᵥ L.openCarrier) (deformPoint φ w) := by
    intro η hη hηboundary hηδ u s hu hs hus hcontact w hw
    apply hstars (u - s) _ w hw
    apply Set.mem_iUnion.mpr
    refine ⟨η, Set.mem_iUnion.mpr ⟨⟨hη, hηboundary, hηδ⟩, ?_⟩⟩
    exact ⟨u, hu, s, hs, hus, rfl, hcontact⟩
  have hAuniv : A = Set.univ := by
    apply closedScalarSection_eq_univ_of_no_endpoint A hAclosed hAlocal hseed
    intro x r hr hcases
    let v := a + x • e
    have hva : v - a ∈ δ := by
      have heq : v - a = x • e := by dsimp [v]; abel
      rw [heq]
      exact δ.smul_mem x he
    have hbasev : deformPoint φ v - b ∈ δ := by
      have hcoset := rationalDirection_preservesCoset φ n v a (hn.symm ▸ hva)
      rw [hn] at hcoset
      convert δ.add_mem hcoset hbase using 1
      abel
    have hcontra (d : Plane) (hd : d ∈ δ) (hd0 : d ≠ 0)
        (hin : ∀ q ∈ Set.Ioo (0 : ℝ) r,
          v - q • d ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
        (hout : ∀ q ∈ Set.Ioo (0 : ℝ) r,
          v + q • d ∉ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) : False :=
      endpointRay_germs_contradict_properLink K L T (deformPoint φ '' T) δ
        φ v d b r hδ hd hd0 htile hr hin hout htileNew rfl hlink hbasev hsingle hcontact
    rcases hcases with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · apply hcontra e he he0
      · intro q hq
        have h := hleft (show x - q ∈ Set.Ioo (x - r) x by constructor <;> linarith [hq.1, hq.2])
        change a + (x - q) • e ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support at h
        have heq : v - q • e = a + (x - q) • e := by
          change (a + x • e) - q • e = a + (x - q) • e
          rw [sub_smul]
          abel
        rwa [heq]
      · intro q hq
        have h := hright (show x + q ∈ Set.Ioo x (x + r) by constructor <;> linarith [hq.1, hq.2])
        change a + (x + q) • e ∉ ⋃ t : T, (t : Plane) +ᵥ frontier K.support at h
        have heq : v + q • e = a + (x + q) • e := by
          change (a + x • e) + q • e = a + (x + q) • e
          rw [add_smul]
          abel
        rwa [heq]
    · apply hcontra (-e) (δ.neg_mem he) (neg_ne_zero.mpr he0)
      · intro q hq
        have h := hright (show x + q ∈ Set.Ioo x (x + r) by constructor <;> linarith [hq.1, hq.2])
        change a + (x + q) • e ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support at h
        have heq : v - q • (-e) = a + (x + q) • e := by
          change (a + x • e) - q • (-e) = a + (x + q) • e
          rw [smul_neg, sub_neg_eq_add, add_smul]
          abel
        rwa [heq]
      · intro q hq
        have h := hleft (show x - q ∈ Set.Ioo (x - r) x by constructor <;> linarith [hq.1, hq.2])
        change a + (x - q) • e ∉ ⋃ t : T, (t : Plane) +ᵥ frontier K.support at h
        have heq : v + q • (-e) = a + (x - q) • e := by
          change (a + x • e) + q • (-e) = a + (x - q) • e
          rw [smul_neg, sub_smul]
          abel
        rwa [heq]
  intro z hz
  obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.mp hz
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hδ he he0] at hu
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hu
  have h : r ∈ A := by rw [hAuniv]; trivial
  change a + r • e ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support at h
  simpa only [hr, vadd_eq_add] using h

open Tiling.Approximation Tiling.RationalSlopes.Approximation in
/-- All readiness-deformation controls are imposed before selecting φ.
FT's actual finite old-contact stars and RG's actual finite arrangement use
the very same LT prototype code, so no extra code-equality premise is needed. -/
private theorem finiteContacts_jointOneLinkDeformation
    (K : PolygonalRegion) (T : Set Plane) (n : RationalNormal)
    (hK : HasRationalSlopes K) (htile : TilesOn K T Set.univ)
    (hlink : HasProperLink K (normalDirection n) T)
    (hfinite : HasFiniteOffDirectionContacts K (normalDirection n) T) :
    ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∃ L : PolygonalRegion, ∃ H : Plane ≃ₜ Plane,
            L.support = deformedPolyhedralSupport P φ ∧ Tiling.IsRational L.support ∧
            Set.InjOn (deformPoint φ) T ∧ TilesOn L (deformPoint φ '' T) Set.univ ∧
            (∀ U ⊆ T, IsInvariantAlong (regularSupport K U) (normalDirection n) →
              IsInvariantAlong (regularSupport L (deformPoint φ '' U)) (normalDirection n)) ∧
            (∀ w ∈ vertexSet K.support,
              SameGermAt K.openCarrier w L.openCarrier (deformPoint φ w)) ∧
            (∀ d ∈ oldOffDirectionContactAlphabet K (normalDirection n) T,
              ∀ w ∈ vertexSet K.support, SameGermAt (d +ᵥ K.openCarrier) w
                (deformPoint φ d +ᵥ L.openCarrier) (deformPoint φ w)) ∧
            (∀ a : Plane, IsProperLink K (normalDirection n) T a →
              ∀ v ∈ translatedVertices K T,
                |normalEval n (v - a)| / 2 ≤ |normalEval n (deformPoint φ (v - a))|) ∧
            (∀ l ∈ P.flatten, ∀ z : Plane,
              Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z)) := by
  classical
  obtain ⟨hδ, hδrat⟩ := normalDirection_rational n
  obtain ⟨P, hP, F₁, ε₁, hε₁, hglobal⟩ :=
    oneLinkRationalDeformation K T (normalDirection n) hδ hδrat hK htile hlink
  obtain ⟨F₂, ε₂, hε₂, hstars⟩ := oldContacts_finiteStars K P (normalDirection n) T hP hfinite
  obtain ⟨F₃, ε₃, hε₃, horder⟩ := properLink_normalOrderControl K T n hK htile
  obtain ⟨F₄, ε₄, hε₄, harrangement⟩ := finiteRationalArrangement_transport P.flatten.toFinset ∅
  let F := (F₁ ∪ F₂) ∪ (F₃ ∪ F₄)
  let ε := min (min ε₁ ε₂) (min ε₃ ε₄)
  refine ⟨P, hP, F, ε, lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄), ?_⟩
  intro φ hφ
  have h₁ : IsFiniteApproximation F₁ ε₁ φ :=
    finiteApproximation_strengthen F₁ F ε₁ ε φ
      (by intro x hx; simp [F, hx])
      ((min_le_left _ _).trans (min_le_left _ _)) hφ
  have h₂ : IsFiniteApproximation F₂ ε₂ φ :=
    finiteApproximation_strengthen F₂ F ε₂ ε φ
      (by intro x hx; simp [F, hx])
      ((min_le_left _ _).trans (min_le_right _ _)) hφ
  have h₃ : IsFiniteApproximation F₃ ε₃ φ :=
    finiteApproximation_strengthen F₃ F ε₃ ε φ
      (by intro x hx; simp [F, hx])
      ((min_le_right _ _).trans (min_le_left _ _)) hφ
  have h₄ : IsFiniteApproximation F₄ ε₄ φ :=
    finiteApproximation_strengthen F₄ F ε₄ ε φ
      (by intro x hx; simp [F, hx])
      ((min_le_right _ _).trans (min_le_right _ _)) hφ
  obtain ⟨L, hL, hLrat, hinj, hLtile, hforward, _⟩ := hglobal φ h₁
  obtain ⟨H, _, hsign⟩ := harrangement φ h₄
  have hfans := hstars φ h₂ L hL
  refine ⟨L, H, hL, hLrat, hinj, hLtile, hforward, hfans.1, hfans.2, ?_, ?_⟩
  · intro a ha v hv
    exact (horder φ h₃ a ha v hv).2.1
  · intro l hl z
    exact hsign l (List.mem_toFinset.mpr hl) z

/-- A preconnected set supported on an actual affine one-dimensional
subspace is convex. The scalar coordinate is constructed from a nonzero
difference of two points, so no openness of the ambient set is assumed. -/
private theorem preconnected_oneDimensional_isConvex
    (δ : Submodule ℝ Plane) (hδ : Module.finrank ℝ δ = 1)
    (C : Set Plane) (hC : IsPreconnected C) (a : Plane)
    (hline : ∀ z ∈ C, z - a ∈ δ) : Convex ℝ C := by
  rw [convex_iff_segment_subset]
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simpa only [segment_same] using (Set.singleton_subset_iff.mpr hx)
  let e := y - x
  have he : e ≠ 0 := sub_ne_zero.mpr (fun hyx => hxy hyx.symm)
  have heδ : e ∈ δ := by
    convert δ.sub_mem (hline y hy) (hline x hx) using 1
    dsimp [e]
    abel
  have hspan : δ = Submodule.span ℝ ({e} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ heδ he
  obtain ⟨τ, hτ⟩ := nonzeroVector_normalizedFunctional e he
  have hτC : Convex ℝ (τ '' C) :=
    (hC.image τ τ.continuous.continuousOn).convex
  intro p hp
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  have hparam : AffineMap.lineMap x y r = x + r • e := by
    rw [AffineMap.lineMap_apply_module']
    change r • (y - x) + x = x + r • (y - x)
    abel
  rw [hparam]
  have hτp : τ (x + r • e) ∈ τ '' C := by
    apply hτC.segment_subset (Set.mem_image_of_mem τ hx) (Set.mem_image_of_mem τ hy)
    rw [segment_eq_image_lineMap]
    refine ⟨r, hr, ?_⟩
    rw [AffineMap.lineMap_apply_module', map_add, map_smul]
    rw [← map_sub]
    change r • τ e + τ x = τ x + r • τ e
    abel
  obtain ⟨z, hz, hzp⟩ := hτp
  have hzx : z - x ∈ δ := by
    convert δ.sub_mem (hline z hz) (hline x hx) using 1
    abel
  have hzpoint : z - (x + r • e) ∈ δ := by
    convert δ.sub_mem hzx (δ.smul_mem r heδ) using 1
    abel
  rw [hspan] at hzpoint
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzpoint
  have hc0 : c = 0 := by
    have h := congrArg τ hc
    have hleft : τ (c • e) = c := by
      calc
        τ (c • e) = c • τ e := τ.map_smul c e
        _ = c := by simp only [hτ, smul_eq_mul, mul_one]
    have hright : τ (z - (x + r • e)) = 0 := by
      rw [map_sub, hzp, sub_self]
    exact hleft.symm.trans (h.trans hright)
  have hzEq : z = x + r • e := by
    rw [hc0, zero_smul] at hc
    exact sub_eq_zero.mp hc.symm
  exact hzEq ▸ hz

open Tiling.Approximation in
/-- The genuine preconnected old boundary set obtained from an arrangement
pullback supplies the scalar interval seed used by line continuation. -/
private theorem preconnected_oldBoundaryInterval_seed
    (K : PolygonalRegion) (T : Set Plane) (δ : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) (C : Set Plane) (hCpre : IsPreconnected C)
    (htwo : ∃ x ∈ C, ∃ y ∈ C, x ≠ y) (c : Plane)
    (hline : ∀ z ∈ C, z - c ∈ δ) (hfront : C ⊆ frontier K.support)
    (t : Plane) (ht : t ∈ T) (φ : ℝ →ₗ[ℚ] ℚ) (b : Plane)
    (hmap : ∀ z ∈ C, deformPoint φ (t + z) - b ∈ δ) :
    ∃ a e : Plane, e ∈ δ ∧ e ≠ 0 ∧ deformPoint φ a - b ∈ δ ∧
      (interior {r : ℝ | a + r • e ∈
        ⋃ s : T, (s : Plane) +ᵥ frontier K.support}).Nonempty := by
  obtain ⟨x, hx, y, hy, hxy⟩ := htwo
  have hconvex := preconnected_oneDimensional_isConvex δ hδ C hCpre c hline
  let e := y - x
  let a := t + x
  have he : e ≠ 0 := sub_ne_zero.mpr (fun hyx => hxy hyx.symm)
  have heδ : e ∈ δ := by
    convert δ.sub_mem (hline y hy) (hline x hx) using 1
    dsimp [e]
    abel
  refine ⟨a, e, heδ, he, hmap x hx, ?_⟩
  have hinterval : Set.Ioo (0 : ℝ) 1 ⊆
      {r : ℝ | a + r • e ∈ ⋃ s : T, (s : Plane) +ᵥ frontier K.support} := by
    intro r hr
    have hp : x + r • e ∈ segment ℝ x y := by
      rw [segment_eq_image_lineMap]
      refine ⟨r, ⟨hr.1.le, hr.2.le⟩, ?_⟩
      rw [AffineMap.lineMap_apply_module']
      change r • (y - x) + x = x + r • (y - x)
      abel
    have hpfront := hfront (hconvex.segment_subset hx hy hp)
    apply Set.mem_iUnion.mpr
    refine ⟨⟨t, ht⟩, Set.mem_vadd_set.mpr ⟨x + r • e, hpfront, ?_⟩⟩
    change t + (x + r • e) = (t + x) + r • e
    abel
  refine ⟨1 / 2, interior_maximal hinterval isOpen_Ioo ?_⟩
  norm_num

private theorem sign_eq_preserves_nonpos {x y : ℝ}
    (h : Real.sign y = Real.sign x) (hx : x ≤ 0) : y ≤ 0 := by
  have hneg : Real.sign (-y) = Real.sign (-x) := by
    rw [Real.sign_neg, Real.sign_neg, h]
  exact neg_nonneg.mp (sign_eq_preserves_nonneg hneg (neg_nonneg.mpr hx))

open Tiling.Approximation Tiling.RationalSlopes.Approximation in
/-- The actual finite-arrangement homeomorphism sends the chosen old
polyhedral support onto its same-code deformed support. -/
private theorem arrangement_support_image
    (K L : PolygonalRegion) (P : PolyhedralCode) (φ : ℝ →ₗ[ℚ] ℚ)
    (H : Plane ≃ₜ Plane) (hP : polyhedralSupport P = K.support)
    (hL : L.support = deformedPolyhedralSupport P φ)
    (hsign : ∀ l ∈ P.flatten, ∀ z : Plane,
      Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z)) :
    H '' K.support = L.support := by
  rw [← hP, hL]
  ext y
  constructor
  · rintro ⟨x, ⟨cell, hcell, hineq⟩, rfl⟩
    refine ⟨cell.map (deformLine φ), List.mem_map.mpr ⟨cell, hcell, rfl⟩, ?_⟩
    intro l hl
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
    exact sign_eq_preserves_nonpos
      (hsign l₀ (List.mem_flatten.mpr ⟨cell, hcell, hl₀⟩) x) (hineq l₀ hl₀)
  · rintro ⟨cell', hcell', hineq⟩
    obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hcell'
    refine ⟨H.symm y, ⟨cell, hcell, ?_⟩, H.apply_symm_apply y⟩
    intro l hl
    have h := sign_eq_preserves_nonpos
      (hsign l (List.mem_flatten.mpr ⟨cell, hcell, hl⟩) (H.symm y)).symm
      (show (deformLine φ l).eval (H (H.symm y)) ≤ 0 by
        simpa only [H.apply_symm_apply] using hineq (deformLine φ l)
          (List.mem_map.mpr ⟨l, hl, rfl⟩))
    exact h

private theorem finiteArrangement_oldBoundaryLineSeed
    (K L : PolygonalRegion) (P : Tiling.RationalSlopes.Approximation.PolyhedralCode)
    (φ : ℝ →ₗ[ℚ] ℚ) (H : Plane ≃ₜ Plane)
    (himage : H '' K.support = L.support)
    (hsign : ∀ l ∈ P.flatten, ∀ z : Plane,
      Real.sign ((Tiling.RationalSlopes.Approximation.deformLine φ l).eval (H z)) =
        Real.sign (l.eval z))
    (l : Tiling.RationalSlopes.Approximation.RationalLine) (hl : l ∈ P.flatten)
    (δ : Submodule ℝ Plane) (hδ : Tiling.Approximation.normalDirection l.normal = δ)
    (t b : Plane) (J : Set Plane)
    (hJpre : IsPreconnected J) (hJne : J.Nonempty)
    (hJtwo : ∃ y₁ ∈ J, ∃ y₂ ∈ J, y₁ ≠ y₂)
    (hJfront : J ⊆ frontier L.support)
    (hJline : ∀ y ∈ J, (Tiling.RationalSlopes.Approximation.deformLine φ l).eval y = 0)
    (hlinkline : (Tiling.RationalSlopes.Approximation.deformLine φ l).eval
      (b - Tiling.Approximation.deformPoint φ t) = 0) :
    ∃ C : Set Plane, IsPreconnected C ∧ C.Nonempty ∧
      (∃ x ∈ C, ∃ y ∈ C, x ≠ y) ∧ C ⊆ frontier K.support ∧
      ∀ z ∈ C, l.eval z = 0 ∧
        Tiling.Approximation.deformPoint φ (t + z) - b ∈ δ := by
  let C : Set Plane := H.symm '' J
  have hfront : H '' frontier K.support = frontier L.support := by
    have h := H.image_frontier K.support
    rw [himage] at h
    exact h
  refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
  · exact hJpre.image H.symm H.symm.continuous.continuousOn
  · obtain ⟨y, hy⟩ := hJne
    exact ⟨H.symm y, Set.mem_image_of_mem _ hy⟩
  · obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := hJtwo
    refine ⟨H.symm y₁, Set.mem_image_of_mem _ hy₁,
      H.symm y₂, Set.mem_image_of_mem _ hy₂, ?_⟩
    intro heq
    exact hne (H.symm.injective heq)
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := (Set.mem_image _ _ _).mp hz
    have hyimage : y ∈ H '' frontier K.support := by rw [hfront]; exact hJfront hy
    obtain ⟨x, hx, hxy⟩ := (Set.mem_image _ _ _).mp hyimage
    have hxEq : x = H.symm y := by
      apply H.injective
      simpa using hxy
    simpa [hxEq] using hx
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := (Set.mem_image _ _ _).mp hz
    have hsignz := hsign l hl (H.symm y)
    rw [H.apply_symm_apply] at hsignz
    have hzerosign : Real.sign ((Tiling.RationalSlopes.Approximation.deformLine φ l).eval y) = 0 := by
      rw [hJline y hy]
      exact Real.sign_zero
    have hsourcezero : Real.sign (l.eval (H.symm y)) = 0 := hsignz.symm.trans hzerosign
    have hyzero : l.eval (H.symm y) = 0 := Real.sign_eq_zero_iff.mp hsourcezero
    have hdelta : Tiling.Approximation.deformPoint φ (t + H.symm y) - b ∈ δ := by
      rw [← hδ]
      change Tiling.Approximation.normalEval l.normal
        (Tiling.Approximation.deformPoint φ (t + H.symm y) - b) = 0
      have hzEval : Tiling.Approximation.normalEval l.normal (H.symm y) = l.offset := by
        have := hyzero
        dsimp [Tiling.RationalSlopes.Approximation.RationalLine.eval] at this
        linarith
      have hbaseEval : Tiling.Approximation.normalEval l.normal b -
          (φ (Tiling.Approximation.normalEval l.normal t) : ℝ) = (φ l.offset : ℝ) := by
        have hh : Tiling.Approximation.normalEval l.normal
            (b - Tiling.Approximation.deformPoint φ t) - (φ l.offset : ℝ) = 0 := by
          simpa [Tiling.RationalSlopes.Approximation.RationalLine.eval,
            Tiling.RationalSlopes.Approximation.deformLine] using hlinkline
        rw [show Tiling.Approximation.normalEval l.normal
            (b - Tiling.Approximation.deformPoint φ t) =
              Tiling.Approximation.normalEval l.normal b -
                Tiling.Approximation.normalEval l.normal
                  (Tiling.Approximation.deformPoint φ t) by
            simp [Tiling.Approximation.normalEval]; ring,
          Tiling.Approximation.rationalNormal_commutes] at hh
        linarith
      rw [show Tiling.Approximation.normalEval l.normal
          (Tiling.Approximation.deformPoint φ (t + H.symm y) - b) =
          Tiling.Approximation.normalEval l.normal
            (Tiling.Approximation.deformPoint φ (t + H.symm y)) -
              Tiling.Approximation.normalEval l.normal b by
            simp [Tiling.Approximation.normalEval]; ring]
      rw [Tiling.Approximation.rationalNormal_commutes]
      have hsum : Tiling.Approximation.normalEval l.normal (t + H.symm y) =
          Tiling.Approximation.normalEval l.normal t +
            Tiling.Approximation.normalEval l.normal (H.symm y) := by
        simp [Tiling.Approximation.normalEval]
        ring
      rw [hsum, map_add, Rat.cast_add, hzEval]
      linarith
    exact ⟨hyzero, hdelta⟩

open Tiling.Approximation Tiling.RationalSlopes.Approximation in
/-- The checked same-code arrangement pullback is converted into the exact
old interval-seed data required by continuation. -/
private theorem modelBoundarySet_oldIntervalSeed
    (K L : PolygonalRegion) (T : Set Plane) (P : PolyhedralCode)
    (φ : ℝ →ₗ[ℚ] ℚ) (H : Plane ≃ₜ Plane) (himage : H '' K.support = L.support)
    (hsign : ∀ l ∈ P.flatten, ∀ z : Plane,
      Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z))
    (l : RationalLine) (hl : l ∈ P.flatten) (δ : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) (hdir : normalDirection l.normal = δ)
    (t b : Plane) (ht : t ∈ T) (J : Set Plane)
    (hJpre : IsPreconnected J) (hJne : J.Nonempty)
    (hJtwo : ∃ y₁ ∈ J, ∃ y₂ ∈ J, y₁ ≠ y₂)
    (hJfront : J ⊆ frontier L.support)
    (hJline : ∀ y ∈ J, (deformLine φ l).eval y = 0)
    (hlinkline : (deformLine φ l).eval (b - deformPoint φ t) = 0) :
    ∃ a e : Plane, e ∈ δ ∧ e ≠ 0 ∧ deformPoint φ a - b ∈ δ ∧
      (interior {r : ℝ | a + r • e ∈
        ⋃ s : T, (s : Plane) +ᵥ frontier K.support}).Nonempty := by
  obtain ⟨C, hCpre, hCne, hCtwo, hCfront, hCpoints⟩ :=
    finiteArrangement_oldBoundaryLineSeed K L P φ H himage hsign l hl δ hdir
      t b J hJpre hJne hJtwo hJfront hJline hlinkline
  obtain ⟨c, hc⟩ := hCne
  have hline : ∀ z ∈ C, z - c ∈ δ := by
    intro z hz
    rw [← hdir]
    change normalEval l.normal (z - c) = 0
    have hzeval := (hCpoints z hz).1
    have hceval := (hCpoints c hc).1
    dsimp only [RationalLine.eval] at hzeval hceval
    have heval : normalEval l.normal (z - c) =
        normalEval l.normal z - normalEval l.normal c := by
      simp only [normalEval, Complex.sub_re, Complex.sub_im]
      ring
    rw [heval]
    linarith
  exact preconnected_oldBoundaryInterval_seed K T δ hδ C hCpre hCtwo c
    hline hCfront t ht φ b (fun z hz => (hCpoints z hz).2)

private theorem properLink_hasTileBoundaryInterval
    (L : PolygonalRegion) (T : Set Plane) (δ : Submodule ℝ Plane)
    (b e : Plane) (he : e ∈ δ) (_he0 : e ≠ 0)
    (htile : Tiling.Polygonal.TilesOn L T Set.univ)
    (hlink : IsProperLink L δ T b) :
    ∃ t ∈ T, ∃ c ρ : ℝ, 0 < ρ ∧
      ∀ r ∈ Set.Ioo (c - ρ) (c + ρ),
        b + r • e ∈ (t : Plane) +ᵥ frontier L.support := by
  let f (t : T) : Set ℝ :=
    {r | b + r • e ∈ (t : Plane) +ᵥ frontier L.support}
  let : Countable T := htile.1.to_subtype
  have hclosed : ∀ t : T, IsClosed (f t) := by
    intro t
    have hcont : Continuous (fun r : ℝ => b + r • e) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact (isClosed_frontier.vadd (t : Plane)).preimage hcont
  have hcover : (⋃ t : T, f t) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro r
    have hline : b + r • e ∈ b +ᵥ (δ : Set Plane) := by
      exact Set.mem_vadd_set.mpr ⟨r • e, δ.smul_mem r he, by simp [vadd_eq_add]⟩
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hlink hline)
    exact Set.mem_iUnion.mpr ⟨t, ht⟩
  obtain ⟨t, ⟨c, hc⟩⟩ :=
    nonempty_interior_of_iUnion_of_closed hclosed hcover
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  refine ⟨t, t.property, c, ρ / 2, by positivity, ?_⟩
  intro r hr
  have hdist : dist r c < ρ := by
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith [hr.1, hr.2]
  have hrf : r ∈ f t := interior_subset (hball (Metric.mem_ball.mpr hdist))
  exact hrf

private theorem finiteCodeSupport_frontier_lines
    (P : Tiling.RationalSlopes.Approximation.PolyhedralCode) :
    ∀ z ∈ frontier (Tiling.RationalSlopes.Approximation.polyhedralSupport P),
      ∃ l ∈ P.flatten, l.eval z = 0 := by
  classical
  let cellSet (cell : List Tiling.RationalSlopes.Approximation.RationalLine) : Set Plane :=
    {z | ∀ l ∈ cell, l.eval z ≤ 0}
  let strictCell (cell : List Tiling.RationalSlopes.Approximation.RationalLine) : Set Plane :=
    {z | ∀ l ∈ cell, l.eval z < 0}
  have heval (l : Tiling.RationalSlopes.Approximation.RationalLine) :
      Continuous l.eval := by
    change Continuous (fun z : Plane =>
      (l.normal.x : ℝ) * z.re + (l.normal.y : ℝ) * z.im - l.offset)
    fun_prop
  have hstrict (cell : List Tiling.RationalSlopes.Approximation.RationalLine) :
      IsOpen (strictCell cell) := by
    induction cell with
    | nil => simp [strictCell]
    | cons l cell ih =>
      have heq : strictCell (l :: cell) = {z | l.eval z < 0} ∩ strictCell cell := by
        ext z
        simp [strictCell]
      rw [heq]
      exact (isOpen_lt (heval l) continuous_const).inter ih
  have hclosedCell (cell : List Tiling.RationalSlopes.Approximation.RationalLine) :
      IsClosed (cellSet cell) := by
    induction cell with
    | nil => simp [cellSet]
    | cons l cell ih =>
      have heq : cellSet (l :: cell) = {z | l.eval z ≤ 0} ∩ cellSet cell := by
        ext z
        simp [cellSet]
      rw [heq]
      exact (isClosed_le (heval l) continuous_const).inter ih
  have hclosed : IsClosed (Tiling.RationalSlopes.Approximation.polyhedralSupport P) := by
    induction P with
    | nil => simp [Tiling.RationalSlopes.Approximation.polyhedralSupport]
    | cons cell P ih =>
      have heq : Tiling.RationalSlopes.Approximation.polyhedralSupport (cell :: P) =
          cellSet cell ∪ Tiling.RationalSlopes.Approximation.polyhedralSupport P := by
        ext z
        simp [Tiling.RationalSlopes.Approximation.polyhedralSupport, cellSet]
      rw [heq]
      exact (hclosedCell cell).union ih
  intro z hz
  have hzmem : z ∈ Tiling.RationalSlopes.Approximation.polyhedralSupport P := by
    have hzcl := frontier_subset_closure hz
    rw [hclosed.closure_eq] at hzcl
    exact hzcl
  obtain ⟨cell, hcell, hineq⟩ := hzmem
  by_contra hzero
  push Not at hzero
  have hzstrict : z ∈ strictCell cell := by
    intro l hl
    exact lt_of_le_of_ne (hineq l hl) (fun heq => hzero l (List.mem_flatten.mpr ⟨cell, hcell, hl⟩) heq)
  have hsubset : strictCell cell ⊆ Tiling.RationalSlopes.Approximation.polyhedralSupport P := by
    intro x hx
    exact ⟨cell, hcell, fun l hl => (hx l hl).le⟩
  have hinterior : z ∈ interior (Tiling.RationalSlopes.Approximation.polyhedralSupport P) :=
    mem_interior_iff_mem_nhds.mpr <| Filter.mem_of_superset ((hstrict cell).mem_nhds hzstrict) hsubset
  exact hz.2 hinterior

private theorem normalDirection_finrank_one_local
    (n : Tiling.Approximation.RationalNormal) :
    Module.finrank ℝ (Tiling.Approximation.normalDirection n) = 1 := by
  let f : Plane →ₗ[ℝ] ℝ :=
    (((n.x : ℝ) • Complex.reCLM + (n.y : ℝ) • Complex.imCLM).toLinearMap)
  have hsurj : Function.Surjective f := by
    intro r
    rcases n.nonzero with hx | hy
    · have hx' : (n.x : ℝ) ≠ 0 := by exact_mod_cast hx
      refine ⟨Complex.mk (r / (n.x : ℝ)) 0, ?_⟩
      change (n.x : ℝ) * (r / (n.x : ℝ)) + (n.y : ℝ) * 0 = r
      field_simp
      ring
    · have hy' : (n.y : ℝ) ≠ 0 := by exact_mod_cast hy
      refine ⟨Complex.mk 0 (r / (n.y : ℝ)), ?_⟩
      change (n.x : ℝ) * 0 + (n.y : ℝ) * (r / (n.y : ℝ)) = r
      field_simp
      ring
  have hrange : Module.finrank ℝ f.range = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  have hsum := f.finrank_range_add_finrank_ker
  have htotal : Module.finrank ℝ Plane = 2 := by
    simp [Plane, Complex.finrank_real_complex]
  change Module.finrank ℝ f.ker = 1
  rw [hrange, htotal] at hsum
  omega

private theorem properLink_interval_on_deformedCodeLine
    (P : Tiling.RationalSlopes.Approximation.PolyhedralCode)
    (φ : ℝ →ₗ[ℚ] ℚ) (δ : Submodule ℝ Plane) (hδ : Module.finrank ℝ δ = 1)
    (b e : Plane) (he : e ∈ δ) (c d : ℝ) (hcd : c < d) (he0 : e ≠ 0)
    (hfront : ∀ r ∈ Set.Ioo c d,
      b + r • e ∈ frontier (Tiling.RationalSlopes.Approximation.deformedPolyhedralSupport P φ)) :
    ∃ l ∈ P.flatten,
      Tiling.Approximation.normalDirection l.normal = δ ∧
      ∀ r ∈ Set.Ioo c d,
        (Tiling.RationalSlopes.Approximation.deformLine φ l).eval (b + r • e) = 0 := by
  classical
  let F : Finset Tiling.RationalSlopes.Approximation.RationalLine := P.flatten.toFinset
  let Q : Tiling.RationalSlopes.Approximation.PolyhedralCode :=
    P.map (fun cell => cell.map (Tiling.RationalSlopes.Approximation.deformLine φ))
  have hroot (l : Tiling.RationalSlopes.Approximation.RationalLine)
      (hcoef : Tiling.Approximation.normalEval l.normal e ≠ 0) :
      {r : ℝ | (Tiling.RationalSlopes.Approximation.deformLine φ l).eval
        (b + r • e) = 0}.Finite := by
    have hlinear (s : ℝ) :
        (Tiling.RationalSlopes.Approximation.deformLine φ l).eval (b + s • e) =
          (Tiling.RationalSlopes.Approximation.deformLine φ l).eval b +
            s * Tiling.Approximation.normalEval l.normal e := by
      simp [Tiling.RationalSlopes.Approximation.RationalLine.eval,
        Tiling.RationalSlopes.Approximation.deformLine,
        Tiling.Approximation.normalEval]
      ring
    apply Set.Finite.subset (Set.finite_singleton
      (-((Tiling.RationalSlopes.Approximation.deformLine φ l).eval b) /
        Tiling.Approximation.normalEval l.normal e))
    intro r hr
    change (Tiling.RationalSlopes.Approximation.deformLine φ l).eval
      (b + r • e) = 0 at hr
    rw [hlinear r] at hr
    have : r = -((Tiling.RationalSlopes.Approximation.deformLine φ l).eval b) /
        Tiling.Approximation.normalEval l.normal e := by
      apply (eq_div_iff hcoef).2
      linarith
    simp [this]
  let roots (l : Tiling.RationalSlopes.Approximation.RationalLine) : Set ℝ :=
    if h : Tiling.Approximation.normalEval l.normal e ≠ 0 then
      {r | (Tiling.RationalSlopes.Approximation.deformLine φ l).eval (b + r • e) = 0}
    else ∅
  have hfiniteUnion : (⋃ l ∈ (F : Set _), roots l).Finite :=
    F.finite_toSet.biUnion (fun l hl => by
      by_cases hc : Tiling.Approximation.normalEval l.normal e ≠ 0
      · simpa [roots, hc] using hroot l hc
      · have hc0 : Tiling.Approximation.normalEval l.normal e = 0 := by simpa using hc
        simp [roots, hc0])
  obtain ⟨r, hr, hrnot⟩ := (Set.Ioo_infinite hcd).sdiff hfiniteUnion |>.nonempty
  obtain ⟨l', hl', hz'⟩ := finiteCodeSupport_frontier_lines Q (b + r • e) (by
    simpa [Q, Tiling.RationalSlopes.Approximation.deformedPolyhedralSupport] using hfront r hr)
  obtain ⟨cell', hcell', hlcell'⟩ := List.mem_flatten.mp hl'
  obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hcell'
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hlcell'
  have hsource : l ∈ P.flatten := List.mem_flatten.mpr ⟨cell, hcell, hl⟩
  have hevalZeroAtR : (Tiling.RationalSlopes.Approximation.deformLine φ l).eval
      (b + r • e) = 0 := hz'
  have hcoef : Tiling.Approximation.normalEval l.normal e = 0 := by
    by_contra hc
    have hsourceF : l ∈ (F : Set _) := by simpa [F] using hsource
    have hrootAt : (Tiling.RationalSlopes.Approximation.deformLine φ l).eval
        (b + r • e) = 0 := by simpa using hevalZeroAtR
    exact hrnot (Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr
      ⟨hsourceF, by simpa [roots, hc] using hrootAt⟩⟩)
  have hevalZero : ∀ s ∈ Set.Ioo c d,
      (Tiling.RationalSlopes.Approximation.deformLine φ l).eval (b + s • e) = 0 := by
    intro s hs
    have hlinear (u : ℝ) :
        (Tiling.RationalSlopes.Approximation.deformLine φ l).eval (b + u • e) =
          (Tiling.RationalSlopes.Approximation.deformLine φ l).eval b +
            u * Tiling.Approximation.normalEval l.normal e := by
      dsimp [Tiling.RationalSlopes.Approximation.RationalLine.eval,
        Tiling.RationalSlopes.Approximation.deformLine]
      simp [Tiling.Approximation.normalEval]
      ring
    calc
      (Tiling.RationalSlopes.Approximation.deformLine φ l).eval (b + s • e) =
          (Tiling.RationalSlopes.Approximation.deformLine φ l).eval b +
            s * Tiling.Approximation.normalEval l.normal e := hlinear s
      _ = (Tiling.RationalSlopes.Approximation.deformLine φ l).eval b := by rw [hcoef]; ring
      _ = (Tiling.RationalSlopes.Approximation.deformLine φ l).eval (b + r • e) := by
        rw [hlinear r, hcoef]
        ring
      _ = 0 := hevalZeroAtR
  have heNorm : e ∈ Tiling.Approximation.normalDirection l.normal := by
    change Tiling.Approximation.normalEval l.normal e = 0
    exact hcoef
  have hspanδ : δ = Submodule.span ℝ {e} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ he he0
  have hspanl : Tiling.Approximation.normalDirection l.normal =
      Submodule.span ℝ {e} := by
    have hrank := normalDirection_finrank_one_local l.normal
    exact eq_span_singleton_of_mem_of_finrank_eq_one hrank heNorm he0
  exact ⟨l, hsource, hspanl.trans hspanδ.symm, hevalZero⟩

open Tiling.Approximation Tiling.RationalSlopes.Approximation in
/-- Every actual model proper link has a genuine old interval seed: Baire
supplies one model tile-boundary interval, the finite code identifies its
parallel supporting line, and the actual arrangement pulls it back. -/
private theorem modelLink_hasOldIntervalSeed
    (K L : PolygonalRegion) (T : Set Plane) (P : PolyhedralCode)
    (φ : ℝ →ₗ[ℚ] ℚ) (H : Plane ≃ₜ Plane)
    (hP : polyhedralSupport P = K.support) (hL : L.support = deformedPolyhedralSupport P φ)
    (hsign : ∀ l ∈ P.flatten, ∀ z : Plane,
      Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z))
    (δ : Submodule ℝ Plane) (hδ : Module.finrank ℝ δ = 1)
    (htile : TilesOn L (deformPoint φ '' T) Set.univ)
    (b : Plane) (hlink : IsProperLink L δ (deformPoint φ '' T) b) :
    ∃ a e : Plane, e ∈ δ ∧ e ≠ 0 ∧ deformPoint φ a - b ∈ δ ∧
      (interior {r : ℝ | a + r • e ∈
        ⋃ t : T, (t : Plane) +ᵥ frontier K.support}).Nonempty := by
  have hδne : δ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hδ
    norm_num at hδ
  obtain ⟨e, heδ, he⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδne
  obtain ⟨u, hu, c, ρ, hρ, hinterval⟩ := properLink_hasTileBoundaryInterval L
    (deformPoint φ '' T) δ b e heδ he htile hlink
  obtain ⟨t, ht, rfl⟩ := hu
  let B := b - deformPoint φ t
  have hfront : ∀ r ∈ Set.Ioo (c - ρ) (c + ρ), B + r • e ∈ frontier L.support := by
    intro r hr
    have h := hinterval r hr
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at h
    convert h using 1
    change (b - deformPoint φ t) + r • e = -deformPoint φ t + (b + r • e)
    abel
  obtain ⟨l, hl, hdir, heval⟩ := properLink_interval_on_deformedCodeLine P φ δ hδ
    B e heδ (c - ρ) (c + ρ) (by linarith) he (by rw [← hL]; exact hfront)
  let f : ℝ → Plane := fun r => B + r • e
  let J := f '' Set.Ioo (c - ρ) (c + ρ)
  have hfcont : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hJpre : IsPreconnected J := isPreconnected_Ioo.image f hfcont.continuousOn
  have hJne : J.Nonempty := (Set.nonempty_Ioo.mpr (by linarith : c - ρ < c + ρ)).image f
  have hfinj : Function.Injective f := by
    have hsmul : Topology.IsClosedEmbedding (fun r : ℝ => r • e) := isClosedEmbedding_smul_left he
    exact (Homeomorph.addLeft B).injective.comp hsmul.injective
  have hJtwo : ∃ y₁ ∈ J, ∃ y₂ ∈ J, y₁ ≠ y₂ := by
    refine ⟨f (c - ρ / 2), Set.mem_image_of_mem f ⟨by linarith, by linarith⟩,
      f (c + ρ / 2), Set.mem_image_of_mem f ⟨by linarith, by linarith⟩, ?_⟩
    intro h
    have h := hfinj h
    linarith
  have hJfront : J ⊆ frontier L.support := by
    rintro y ⟨r, hr, rfl⟩
    exact hfront r hr
  have hJline : ∀ y ∈ J, (deformLine φ l).eval y = 0 := by
    rintro y ⟨r, hr, rfl⟩
    exact heval r hr
  have hcoef : normalEval l.normal e = 0 := by
    change e ∈ normalDirection l.normal
    rw [hdir]
    exact heδ
  have hlinkline : (deformLine φ l).eval B = 0 := by
    have hzero := heval c ⟨by linarith, by linarith⟩
    have hlinear : (deformLine φ l).eval (B + c • e) =
        (deformLine φ l).eval B + c * normalEval l.normal e := by
      simp only [RationalLine.eval, deformLine, normalEval, Complex.add_re,
        Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
      ring
    rw [hlinear, hcoef, mul_zero, add_zero] at hzero
    exact hzero
  exact modelBoundarySet_oldIntervalSeed K L T P φ H
    (arrangement_support_image K L P φ H hP hL hsign) hsign l hl δ hδ hdir
    t b ht J hJpre hJne hJtwo hJfront hJline hlinkline

theorem finiteOffDirectionContacts_uniformlyReady :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    HasRationalSlopes K → Module.finrank ℝ δ = 1 → HasBoundaryDirection K δ →
    TilesOn K T Set.univ → HasNontrivialEarthquakeDecomposition K δ T →
      HasFiniteOffDirectionContacts K δ T → IsUniformlyReady K δ T
  := by
  intro K δ T hK hδ hboundary htile hnontrivial hfinite
  classical
  obtain ⟨n, hn⟩ := Tiling.RationalSlopes.Approximation.rationalDirection_hasNormal
    δ hδ (hasRationalDirection_of_hasBoundaryDirection hK hboundary)
  subst δ
  let ℓ : Plane →L[ℝ] ℝ := (n.x : ℝ) • Complex.reCLM + (n.y : ℝ) • Complex.imCLM
  have hℓ : ℓ ≠ 0 := by
    intro hzero
    have hx : (n.x : ℝ) = 0 := by simpa [ℓ] using DFunLike.congr_fun hzero 1
    have hy : (n.y : ℝ) = 0 := by simpa [ℓ] using DFunLike.congr_fun hzero Complex.I
    have hx' : n.x = 0 := by exact_mod_cast hx
    have hy' : n.y = 0 := by exact_mod_cast hy
    exact n.nonzero.elim (fun h => h hx') (fun h => h hy')
  have hker : LinearMap.ker ℓ.toLinearMap = Tiling.Approximation.normalDirection n := rfl
  by_cases hcol : T = columnPart K (Tiling.Approximation.normalDirection n) T
  · apply allColumns_uniformlyReady K (Tiling.Approximation.normalDirection n) T
      ℓ hℓ hker htile
    rw [hcol]
    exact columnPart_isUnionColumns K (Tiling.Approximation.normalDirection n) T hδ htile.2.1
  have htwo := hnontrivial.resolve_left hcol
  have hlink := nontrivial_decomposition_hasLink K (Tiling.Approximation.normalDirection n)
    T hδ htile hnontrivial
  obtain ⟨P, hP, F, ε, hε, hdeformation⟩ := finiteContacts_jointOneLinkDeformation
    K T n hK htile hlink hfinite
  obtain ⟨φ, hφ⟩ := Tiling.Approximation.exists_finiteApproximation F ε hε
  obtain ⟨L, H, hL, hLrat, hinj, hmodel, hforward, hsingle, hstars, hlower, hsign⟩ :=
    hdeformation φ hφ
  have hmodelTwo := twoComponents_forwardTransport K L (Tiling.Approximation.normalDirection n)
    T hδ htile (Tiling.Approximation.deformPoint φ) hinj hmodel hforward htwo
  have hmodelReady := rational_nontrivial_uniformlyReady L (Tiling.Approximation.normalDirection n)
    (Tiling.Approximation.deformPoint φ '' T) ℓ hℓ hker
    (rationalSupport_isRelativelyRational L hLrat) hδ
    (Tiling.RationalSlopes.Approximation.normalDirection_rational n).2 hmodel (Or.inr hmodelTwo)
  have hseeds : ∀ b : Plane,
      IsProperLink L (Tiling.Approximation.normalDirection n)
        (Tiling.Approximation.deformPoint φ '' T) b →
      ∃ a e : Plane, e ∈ Tiling.Approximation.normalDirection n ∧ e ≠ 0 ∧
        Tiling.Approximation.deformPoint φ a - b ∈ Tiling.Approximation.normalDirection n ∧
        (interior {r : ℝ | a + r • e ∈
          ⋃ t : T, (t : Plane) +ᵥ frontier K.support}).Nonempty := by
    intro b hb
    exact modelLink_hasOldIntervalSeed K L T P φ H hP hL hsign
      (Tiling.Approximation.normalDirection n) hδ hmodel b hb
  apply uniformlyReady_of_actualLinkLifts K L (Tiling.Approximation.normalDirection n)
    T ℓ hℓ hker htile φ hmodelReady
  · intro b hb
    obtain ⟨a, e, heδ, he, hab, hseed⟩ := hseeds b hb
    exact ⟨a, boundaryLine_seed_isProperLink K L T (Tiling.Approximation.normalDirection n)
      n rfl φ a e b hδ heδ he htile hmodel hb hab hseed hsingle hstars, hab⟩
  · intro a ha v hv
    exact hlower a ha v hv

/-- This is precisely the alphabet consequence of failure of readiness, not a
reflection statement for new contacts of a rational approximation. -/
private theorem nonReady_hasInfiniteOldContactAlphabet
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    (hK : HasRationalSlopes K) (hδ : Module.finrank ℝ δ = 1)
    (hboundary : HasBoundaryDirection K δ) (htile : TilesOn K T Set.univ)
    (hnontrivial : HasNontrivialEarthquakeDecomposition K δ T)
    (hnotready : ¬ IsUniformlyReady K δ T) :
    ∃ η : Submodule ℝ Plane, Module.finrank ℝ η = 1 ∧
      HasBoundaryDirection K η ∧ η ≠ δ ∧
        ¬ (properContactDisplacements K η T).Finite := by
  classical
  by_contra h
  apply hnotready
  apply finiteOffDirectionContacts_uniformlyReady K δ T hK hδ hboundary
    htile hnontrivial
  intro η hη hηboundary hηδ
  by_contra hinfinite
  exact h ⟨η, hη, hηboundary, hηδ, hinfinite⟩

-- The actual rigidity core below is independent of the still-open finite-
-- contact endpoint; only the final alphabet consequence uses that endpoint.
private theorem columnPart_subset_source
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane) :
    columnPart K δ T ⊆ T := by
  intro s hs
  obtain ⟨P, hsP⟩ := Set.mem_iUnion.mp hs
  obtain ⟨t, _, rfl⟩ := hsP
  exact t.property

private theorem columnPart_disjoint_noncolumn
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (P : EarthquakeComponent K δ T) (hP : P ∈ noncolumnComponents K δ T) :
    Disjoint (columnPart K δ T) P.centres := by
  rw [Set.disjoint_left]
  intro x hxC hxP
  obtain ⟨⟨Q, hQcol⟩, hxQ⟩ := Set.mem_iUnion.mp hxC
  obtain ⟨s, hsP, hsx⟩ := hxP
  obtain ⟨t, htQ, htx⟩ := hxQ
  have hst : s = t := Subtype.ext (hsx.trans htx.symm)
  have hsQ : s ∈ Q.supp := by rw [hst]; exact htQ
  have hPQ : P = Q := SimpleGraph.ConnectedComponent.eq_of_common_vertex hsP hsQ
  apply hP
  rw [hPQ]
  exact hQcol

/-- The rigidity core is independent of the finite-contact readiness endpoint.
Its period-group equality is proved using actual frontier links and integer
translates, not a stored stabilization certificate. -/
private theorem nonReady_rigidityCore
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (ℓ : Plane →L[ℝ] ℝ) (hK : HasRationalSlopes K)
    (hδ : Module.finrank ℝ δ = 1) (hboundary : HasBoundaryDirection K δ)
    (hℓ : ℓ ≠ 0) (hker : LinearMap.ker ℓ.toLinearMap = δ)
    (htile : TilesOn K T Set.univ) (hnontrivial : HasNontrivialEarthquakeDecomposition K δ T)
    (hnotready : ¬ IsUniformlyReady K δ T) :
    (∃ P : EarthquakeComponent K δ T, noncolumnComponents K δ T = {P}) ∧
      (columnPart K δ T).Nonempty ∧
      periodGroup (regularSupport K (columnPart K δ T)) = δ.toAddSubgroup := by
  classical
  let C := columnPart K δ T
  have hCcol : IsUnionOfColumns K δ C := columnPart_isUnionColumns K δ T hδ htile.2.1
  have hCT : C ⊆ T := columnPart_subset_source K δ T
  have hTneC : T ≠ C := by
    intro h
    apply hnotready
    exact allColumns_uniformlyReady K δ T ℓ hℓ hker htile (h.symm ▸ hCcol)
  have hexists : ∃ P : EarthquakeComponent K δ T, P ∈ noncolumnComponents K δ T := by
    by_contra hnone
    have hall : ∀ P : EarthquakeComponent K δ T, IsCenterColumn K δ P.centres := by
      intro P
      by_contra hP
      exact hnone ⟨P, hP⟩
    apply hTneC
    apply Set.Subset.antisymm
    · intro t ht
      let P : EarthquakeComponent K δ T := (earthquakeGraph K δ T).connectedComponentMk ⟨t, ht⟩
      have htP : t ∈ P.centres := ⟨⟨t, ht⟩, rfl, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨P, hall P⟩, htP⟩
    · exact hCT
  obtain ⟨P, hP⟩ := hexists
  have hunique : ∀ Q ∈ noncolumnComponents K δ T, Q = P := by
    intro Q hQ
    by_contra hQP
    exact hnotready (twoNoncolumns_uniformlyReady K δ T ℓ hK hδ hboundary
      hℓ hker htile hnontrivial Q P hQ hP hQP)
  have hNC : noncolumnComponents K δ T = {P} := by
    ext Q
    constructor
    · intro hQ
      exact Set.mem_singleton_iff.mpr (hunique Q hQ)
    · intro hQ
      rw [Set.mem_singleton_iff] at hQ
      subst Q
      exact hP
  have hCne : C.Nonempty := by
    rcases hnontrivial with hTcol | ⟨A, B, hAB⟩
    · exact (hTneC hTcol).elim
    · by_cases hA : IsCenterColumn K δ A.centres
      · obtain ⟨t, ht⟩ := A.nonempty_supp.image Subtype.val
        exact ⟨t, Set.mem_iUnion.mpr ⟨⟨A, hA⟩, ht⟩⟩
      · by_cases hB : IsCenterColumn K δ B.centres
        · obtain ⟨t, ht⟩ := B.nonempty_supp.image Subtype.val
          exact ⟨t, Set.mem_iUnion.mpr ⟨⟨B, hB⟩, ht⟩⟩
        · exact (hAB ((hunique A hA).trans (hunique B hB).symm)).elim
  have hCinv : IsInvariantAlong (regularSupport K C) δ :=
    unionColumns_carrier_isInvariant K δ C hCcol
  have hPsub : P.centres ⊆ T := by rintro s ⟨u, _, rfl⟩; exact u.property
  have hCPdisj : Disjoint (regularSupport K C) P.carrier :=
    regularSupport_disjoint_of_disjoint_subfamilies htile.2.1 hCT hPsub
      (columnPart_disjoint_noncolumn K δ T P hP)
  have hCproper : regularSupport K C ≠ Set.univ := by
    intro h
    obtain ⟨x, hx⟩ := regularSupport_nonempty K P.centres (P.nonempty_supp.image Subtype.val)
    exact Set.disjoint_left.mp hCPdisj (by rw [h]; trivial) hx
  have hfrontier : (frontier (regularSupport K C)).Nonempty :=
    nonempty_frontier_iff.mpr ⟨regularSupport_nonempty K C hCne, hCproper⟩
  have hperiods : periodGroup (regularSupport K C) = δ.toAddSubgroup := by
    ext q
    constructor
    · intro hq
      by_contra hqδ
      exact hnotready (invariantCarrier_transversePeriod_uniformlyReady K δ T C
        htile hCT hCinv hfrontier ℓ hker q hqδ hq)
    · intro hq
      exact AddAction.mem_stabilizer_iff.mpr (hCinv q hq)
  exact ⟨⟨P, hNC⟩, hCne, hperiods⟩

theorem nonReady_characterization :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    HasRationalSlopes K → Module.finrank ℝ δ = 1 → HasBoundaryDirection K δ →
    TilesOn K T Set.univ → HasNontrivialEarthquakeDecomposition K δ T →
    ¬IsUniformlyReady K δ T →
      (∃ P : EarthquakeComponent K δ T, noncolumnComponents K δ T = {P}) ∧
      (columnPart K δ T).Nonempty ∧
      periodGroup (regularSupport K (columnPart K δ T)) = δ.toAddSubgroup ∧
      ∃ η : Submodule ℝ Plane, Module.finrank ℝ η = 1 ∧
        HasBoundaryDirection K η ∧ η ≠ δ ∧
          ¬(properContactDisplacements K η T).Finite
  := by
  intro K δ T hK hδ hboundary htile hnontrivial hnotready
  obtain ⟨n, hn⟩ := Tiling.RationalSlopes.Approximation.rationalDirection_hasNormal
    δ hδ (hasRationalDirection_of_hasBoundaryDirection hK hboundary)
  let ℓ : Plane →L[ℝ] ℝ :=
    (n.x : ℝ) • Complex.reCLM + (n.y : ℝ) • Complex.imCLM
  have hℓ : ℓ ≠ 0 := by
    intro hzero
    have hx : (n.x : ℝ) = 0 := by simpa [ℓ] using DFunLike.congr_fun hzero 1
    have hy : (n.y : ℝ) = 0 := by simpa [ℓ] using DFunLike.congr_fun hzero Complex.I
    have hx' : n.x = 0 := by exact_mod_cast hx
    have hy' : n.y = 0 := by exact_mod_cast hy
    exact n.nonzero.elim (fun h => h hx') (fun h => h hy')
  have hker : LinearMap.ker ℓ.toLinearMap = δ := hn
  have hcore := nonReady_rigidityCore K δ T ℓ hK hδ hboundary hℓ hker
    htile hnontrivial hnotready
  exact ⟨hcore.1, hcore.2.1, hcore.2.2,
    nonReady_hasInfiniteOldContactAlphabet hK hδ hboundary htile hnontrivial hnotready⟩

theorem simultaneousColumns_product :
∀ (K : PolygonalRegion) (T C D : Set Plane) (δ η : Submodule ℝ Plane),
    Module.finrank ℝ δ = 1 → Module.finrank ℝ η = 1 → δ ≠ η →
    IsPacking K.prototileFamily (K.placements T) → C ⊆ T → D ⊆ T →
      IsCenterColumn K δ C → IsCenterColumn K η D → IsProductAlong K δ η
  := by
  intro K T C D δ η hδ hη hne hp hCT hDT hC hD
  obtain ⟨s, hsC, hsD, hinter⟩ :=
    transverseColumns_inter_singleton hδ hη hne hp hCT hDT hC hD
  have hpCD : IsPacking K.prototileFamily (K.placements (C ∩ D)) :=
    (isPacking_iff_openCarrier_disjoint K (C ∩ D)).mpr fun u hu v hv huv =>
      (isPacking_iff_openCarrier_disjoint K T).mp hp (hCT hu.1) (hCT hv.1) huv
  have hcl : closure (regularSupport K C ∩ regularSupport K D) = s +ᵥ K.support := by
    rw [regularSupport_inter_of_commonPacking hp hCT hDT,
      closure_regularSupport_eq_supportUnion hpCD]
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
      have hts : (t : Plane) = s := by simpa only [hinter, Set.mem_singleton_iff] using t.2
      simpa only [hts] using ht
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨s, hsC, hsD⟩, hx⟩
  have hE : s +ᵥ K.support =
      (s +ᵥ directionalSaturation δ K.support) ∩
        (s +ᵥ directionalSaturation η K.support) := by
    calc
      s +ᵥ K.support = closure (regularSupport K C ∩ regularSupport K D) := hcl.symm
      _ = closure (regularSupport K C) ∩ closure (regularSupport K D) :=
        invariantCylinder_closure_inter hδ hη hne hC.2.2.2 hD.2.2.2
      _ = (s +ᵥ directionalSaturation δ K.support) ∩
          (s +ᵥ directionalSaturation η K.support) := by
        rw [closure_columnCarrier_eq_saturation hC hsC,
          closure_columnCarrier_eq_saturation hD hsD]
  rw [← Set.vadd_set_inter] at hE
  have hcancel := congrArg (fun E : Set Plane => (-s) +ᵥ E) hE
  change K.support = directionalSaturation δ K.support ∩ directionalSaturation η K.support
  simpa only [vadd_vadd, neg_add_cancel, zero_vadd] using hcancel

theorem product_closedUnderSupportApproximation :
∀ (K : PolygonalRegion) (δ η : Submodule ℝ Plane),
    Module.finrank ℝ δ = 1 → Module.finrank ℝ η = 1 → δ ≠ η →
    (∀ ε : ℝ, 0 < ε → ∃ L : PolygonalRegion,
      SupportClose ε K L ∧ IsProductAlong L δ η) → IsProductAlong K δ η
  := by
  intro K δ η hδ hη hne happrox
  change K.support = directionalSaturation δ K.support ∩ directionalSaturation η K.support
  have hprojections := distinct_lineDirections_continuousProjections δ η hδ hη hne
  rcases hprojections with ⟨Pδ, Pη, hsum, hPδmem, hPηmem, hPδvan, hPηvan⟩
  have hKclosed : IsClosed K.support := K.isPolygonal.isClosed
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨⟨x, hx, by simp⟩, ⟨x, hx, by simp⟩⟩
  · intro x hx
    change x ∈ directionalSaturation δ K.support ∩ directionalSaturation η K.support at hx
    rcases hx.1 with ⟨yδ, hyδ, hxyδ⟩
    rcases hx.2 with ⟨yη, hyη, hxyη⟩
    have hyηx : yη - x ∈ η := by
      have h := η.neg_mem hxyη
      simpa using h
    have hyδx : yδ - x ∈ δ := by
      have h := δ.neg_mem hxyδ
      simpa using h
    have hPδeq : Pδ yη = Pδ x := by
      have hzero := hPδvan (yη - x) hyηx
      simpa only [map_sub, sub_eq_zero] using hzero
    have hPηeq : Pη yδ = Pη x := by
      have hzero := hPηvan (yδ - x) hyδx
      simpa only [map_sub, sub_eq_zero] using hzero
    have hxclosure : x ∈ closure K.support := by
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      have hFcont : Continuous (fun p : Plane × Plane => Pδ p.1 + Pη p.2) := by
        fun_prop
      have hbase : Pδ yη + Pη yδ = x := by
        rw [hPδeq, hPηeq]
        exact hsum x
      let F : Plane × Plane → Plane := fun p => Pδ p.1 + Pη p.2
      have hpre : F ⁻¹' Metric.ball x (ε / 2) ∈ 𝓝 (yη, yδ) := by
        have h := hFcont.continuousAt
          (Metric.ball_mem_nhds (F (yη, yδ)) (half_pos hε))
        convert h using 1
        simp [F, hbase]
      obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hpre
      obtain ⟨rU, hrU, hrUsub⟩ := Metric.mem_nhds_iff.mp hU
      obtain ⟨rV, hrV, hrVsub⟩ := Metric.mem_nhds_iff.mp hV
      let ρ : ℝ := min rU (min rV (ε / 2))
      have hρ : 0 < ρ := by dsimp [ρ]; positivity
      obtain ⟨L, hclose, hproduct⟩ := happrox ρ hρ
      change L.support = directionalSaturation δ L.support ∩ directionalSaturation η L.support at hproduct
      obtain ⟨a, haL, haNear⟩ := hclose.1 yδ hyδ
      obtain ⟨b, hbL, hbNear⟩ := hclose.1 yη hyη
      have hbU : b ∈ U := hrUsub (Metric.mem_ball.mpr (by
        have hdist := hbNear
        rw [dist_comm] at hdist
        exact lt_of_lt_of_le hdist (by dsimp [ρ]; exact min_le_left _ _)))
      have haV : a ∈ V := hrVsub (Metric.mem_ball.mpr (by
        have hdist := haNear
        rw [dist_comm] at hdist
        exact lt_of_lt_of_le hdist (by dsimp [ρ]; exact le_trans (min_le_right _ _) (min_le_left _ _))))
      let z : Plane := Pδ b + Pη a
      have hza : z - a = Pδ (b - a) := by
        dsimp [z]
        calc
          Pδ b + Pη a - a = (Pδ b + Pη a) - (Pδ a + Pη a) := by rw [hsum a]
          _ = Pδ b - Pδ a := by abel
          _ = Pδ (b - a) := by rw [map_sub]
      have hzb : z - b = Pη (a - b) := by
        dsimp [z]
        calc
          Pδ b + Pη a - b = (Pδ b + Pη a) - (Pδ b + Pη b) := by rw [hsum b]
          _ = Pη a - Pη b := by abel
          _ = Pη (a - b) := by rw [map_sub]
      have hzδ : z ∈ directionalSaturation δ L.support := by
        refine ⟨a, haL, ?_⟩
        rw [hza]
        exact hPδmem (b - a)
      have hzη : z ∈ directionalSaturation η L.support := by
        refine ⟨b, hbL, ?_⟩
        rw [hzb]
        exact hPηmem (a - b)
      have hzL : z ∈ L.support := by
        rw [hproduct]
        exact ⟨hzδ, hzη⟩
      have hzball : F (b, a) ∈ Metric.ball x (ε / 2) := hUV ⟨hbU, haV⟩
      have hzdist : dist x z < ε / 2 := by
        simpa [F, z, dist_comm] using hzball
      obtain ⟨k, hkK, hzk⟩ := hclose.2 z hzL
      refine ⟨k, hkK, ?_⟩
      have hρeps : ρ ≤ ε / 2 := by
        dsimp [ρ]
        exact le_trans (min_le_right rU _) (min_le_right rV _)
      calc
        dist x k ≤ dist x z + dist z k := dist_triangle x z k
        _ < ε / 2 + ρ := add_lt_add hzdist (by simpa [dist_comm] using hzk)
        _ ≤ ε / 2 + ε / 2 := add_le_add_right hρeps _
        _ = ε := by ring
    exact hKclosed.closure_subset hxclosure

private theorem finiteStrictIntervalProducts_isAxisParallel
    {n m : ℕ} (a b : Fin n → ℝ) (c d : Fin m → ℝ)
    (hab : ∀ i, a i < b i) (hcd : ∀ j, c j < d j)
    (hsepA : ∀ i i', i ≠ i' → b i < a i' ∨ b i' < a i)
    (hsepC : ∀ j j', j ≠ j' → d j < c j' ∨ d j' < c j) :
    Tiling.IsAxisParallel
      {z : Plane | z.re ∈ ⋃ i, Set.Icc (a i) (b i) ∧
        z.im ∈ ⋃ j, Set.Icc (c j) (d j)} := by
  classical
  let rect : Fin n × Fin m → Set Plane := fun p =>
    Complex.Rectangle (Complex.mk (a p.1) (c p.2))
      (Complex.mk (b p.1) (d p.2))
  have hrect_mem (p : Fin n × Fin m) (z : Plane) :
      z ∈ rect p ↔ z.re ∈ Set.Icc (a p.1) (b p.1) ∧
        z.im ∈ Set.Icc (c p.2) (d p.2) := by
    simp [rect, Complex.Rectangle, Complex.mem_reProdIm,
      Set.uIcc_of_lt (hab p.1), Set.uIcc_of_lt (hcd p.2)]
  have hrectDisjoint (p q : Fin n × Fin m) (hpq : p ≠ q) :
      Disjoint (rect p) (rect q) := by
    rw [Set.disjoint_left]
    intro z hp hq
    have hp' := (hrect_mem p z).mp hp
    have hq' := (hrect_mem q z).mp hq
    by_cases hx : p.1 = q.1
    · have hy : p.2 ≠ q.2 := by
        intro h
        exact hpq (Prod.ext hx h)
      rcases hsepC p.2 q.2 hy with hgap | hgap
      · exact (not_lt_of_ge (le_trans hq'.2.1 hp'.2.2)) hgap
      · exact (not_lt_of_ge (le_trans hp'.2.1 hq'.2.2)) hgap
    · rcases hsepA p.1 q.1 hx with hgap | hgap
      · exact (not_lt_of_ge (le_trans hq'.1.1 hp'.1.2)) hgap
      · exact (not_lt_of_ge (le_trans hp'.1.1 hq'.1.2)) hgap
  refine ⟨{
    pieces := Finset.univ.image rect
    isRectangle := ?_
    pairwiseAEDisjoint := ?_
    sUnion_eq := ?_ }⟩
  · intro R hR
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hR
    refine ⟨Complex.mk (a p.1) (c p.2), Complex.mk (b p.1) (d p.2), ?_, ?_, rfl⟩
    · simpa using ne_of_lt (hab p.1)
    · simpa using ne_of_lt (hcd p.2)
  · intro R hR S hS hRS
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hS
    have hpq : p ≠ q := by
      intro hpq
      exact hRS (congrArg rect hpq)
    exact (hrectDisjoint p q hpq).aedisjoint
  · ext z
    constructor
    · intro hz
      rcases Set.mem_sUnion.mp hz with ⟨R, hR, hzR⟩
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hR
      have hz' := (hrect_mem p z).mp hzR
      exact ⟨Set.mem_iUnion.mpr ⟨p.1, hz'.1⟩,
        Set.mem_iUnion.mpr ⟨p.2, hz'.2⟩⟩
    · rintro ⟨hx, hy⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_sUnion.mpr ⟨rect (i, j), Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩,
        (hrect_mem (i, j) z).mpr ⟨hi, hj⟩⟩

private def coordinatePlaneProduct (X Y : Set ℝ) : Set Plane :=
  {z | z.re ∈ X ∧ z.im ∈ Y}

private theorem coordinatePlaneProduct_interior (X Y : Set ℝ) :
    interior (coordinatePlaneProduct X Y) =
      coordinatePlaneProduct (interior X) (interior Y) := by
  let H := Complex.equivRealProdCLM.toHomeomorph
  change interior (H ⁻¹' (X ×ˢ Y)) = H ⁻¹' (interior X ×ˢ interior Y)
  rw [← H.preimage_interior, interior_prod_eq]

private theorem coordinatePlaneProduct_closure (X Y : Set ℝ) :
    closure (coordinatePlaneProduct X Y) =
      coordinatePlaneProduct (closure X) (closure Y) := by
  let H := Complex.equivRealProdCLM.toHomeomorph
  change closure (H ⁻¹' (X ×ˢ Y)) = H ⁻¹' (closure X ×ˢ closure Y)
  rw [← H.preimage_closure, closure_prod_eq]

private theorem coordinateProduct_factors_regularClosed
    (K : PolygonalRegion) (X Y : Set ℝ)
    (hX : IsClosed X) (hY : IsClosed Y)
    (hproduct : K.support = coordinatePlaneProduct X Y) :
    closure (interior X) = X ∧ closure (interior Y) = Y := by
  obtain ⟨z, hz⟩ := K.nonempty
  have hzXY : z.re ∈ X ∧ z.im ∈ Y := by
    have hzP : z ∈ coordinatePlaneProduct X Y := by rw [← hproduct]; exact hz
    exact hzP
  have hreg : coordinatePlaneProduct (closure (interior X)) (closure (interior Y)) =
      coordinatePlaneProduct X Y := by
    rw [← coordinatePlaneProduct_closure, ← coordinatePlaneProduct_interior, ← hproduct]
    exact K.isPolygonal.closure_interior
  constructor
  · apply Set.Subset.antisymm
    · exact closure_minimal interior_subset hX
    · intro r hr
      have hmem : Complex.mk r z.im ∈ coordinatePlaneProduct X Y := ⟨hr, hzXY.2⟩
      rw [← hreg] at hmem
      exact hmem.1
  · apply Set.Subset.antisymm
    · exact closure_minimal interior_subset hY
    · intro r hr
      have hmem : Complex.mk z.re r ∈ coordinatePlaneProduct X Y := ⟨hzXY.1, hr⟩
      rw [← hreg] at hmem
      exact hmem.2

/-- Arbitrary REAL straightening turns the exact support identity into a
coordinate product. No rationality is added to this general statement. -/
private theorem straightenedProduct_support
    (K : PolygonalRegion) (δ η : Submodule ℝ Plane) (A : Plane ≃L[ℝ] Plane)
    (hAδ : ∀ x, x ∈ δ ↔ (A x).re = 0)
    (hAη : ∀ x, x ∈ η ↔ (A x).im = 0)
    (hproduct : IsProductAlong K δ η) :
    A '' K.support = coordinatePlaneProduct
      (Complex.re '' (A '' K.support)) (Complex.im '' (A '' K.support)) := by
  apply Set.Subset.antisymm
  · intro z hz
    exact ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩
  · rintro z ⟨⟨u, ⟨x, hx, hxu⟩, hure⟩, ⟨v, ⟨y, hy, hyv⟩, hvim⟩⟩
    have hxδ : A.symm z - x ∈ δ := by
      apply (hAδ _).mpr
      rw [map_sub, A.apply_symm_apply, Complex.sub_re, hxu, hure, sub_self]
    have hyη : A.symm z - y ∈ η := by
      apply (hAη _).mpr
      rw [map_sub, A.apply_symm_apply, Complex.sub_im, hyv, hvim, sub_self]
    have hzK : A.symm z ∈ K.support := by
      rw [hproduct]
      exact ⟨⟨x, hx, hxδ⟩, ⟨y, hy, hyη⟩⟩
    exact ⟨A.symm z, hzK, A.apply_symm_apply z⟩

private theorem coordinateProduct_isAxisParallel
    (K : PolygonalRegion)
    (hproduct : K.support = coordinatePlaneProduct
      (Complex.re '' K.support) (Complex.im '' K.support)) :
    IsAxisParallel K.support := by
  let X := Complex.re '' K.support
  let Y := Complex.im '' K.support
  have hXclosed : IsClosed X := (K.isPolygonal.isCompact.image Complex.continuous_re).isClosed
  have hYclosed : IsClosed Y := (K.isPolygonal.isCompact.image Complex.continuous_im).isClosed
  obtain ⟨z, hz⟩ := K.nonempty
  have hzX : z.re ∈ X := ⟨z, hz, rfl⟩
  have hzY : z.im ∈ Y := ⟨z, hz, rfl⟩
  have hsectionX : {r : ℝ | Complex.mk 0 z.im + r • (1 : Plane) ∈ K.support} = X := by
    ext r
    change Complex.mk 0 z.im + r • (1 : Plane) ∈ K.support ↔ r ∈ X
    rw [hproduct]
    change (Complex.mk 0 z.im + r • (1 : Plane)).re ∈ X ∧
      (Complex.mk 0 z.im + r • (1 : Plane)).im ∈ Y ↔ r ∈ X
    simpa using (and_iff_left hzY)
  have hsectionY : {r : ℝ | Complex.mk z.re 0 + r • Complex.I ∈ K.support} = Y := by
    ext r
    change Complex.mk z.re 0 + r • Complex.I ∈ K.support ↔ r ∈ Y
    rw [hproduct]
    change (Complex.mk z.re 0 + r • Complex.I).re ∈ X ∧
      (Complex.mk z.re 0 + r • Complex.I).im ∈ Y ↔ r ∈ Y
    simpa using (and_iff_right hzX)
  obtain ⟨n, a, b, _, hXraw⟩ := initialFibre_polygonalClosedSection K (Complex.mk 0 z.im)
    (1 : Plane) (by norm_num)
  obtain ⟨m, c, d, _, hYraw⟩ := initialFibre_polygonalClosedSection K (Complex.mk z.re 0)
    Complex.I Complex.I_ne_zero
  rw [hsectionX] at hXraw
  rw [hsectionY] at hYraw
  obtain ⟨PX⟩ := Tiling.AxisParallel.Foundations.GenericSlices.finiteClosedIntervals_merge a b
  obtain ⟨PY⟩ := Tiling.AxisParallel.Foundations.GenericSlices.finiteClosedIntervals_merge c d
  obtain ⟨hXreg, hYreg⟩ := coordinateProduct_factors_regularClosed K X Y hXclosed hYclosed hproduct
  have hXpresent : X = ⋃ i, Set.Icc (PX.left i) (PX.right i) := by
    rw [← hXreg, hXraw]
    exact PX.closure_eq
  have hYpresent : Y = ⋃ i, Set.Icc (PY.left i) (PY.right i) := by
    rw [← hYreg, hYraw]
    exact PY.closure_eq
  have hrect := finiteStrictIntervalProducts_isAxisParallel PX.left PX.right PY.left PY.right
    PX.lt PY.lt PX.pairwise_gap PY.pairwise_gap
  rw [hproduct]
  change IsAxisParallel (coordinatePlaneProduct X Y)
  rw [hXpresent, hYpresent]
  exact hrect

private theorem coordinateProduct_openProduct
    (K : PolygonalRegion)
    (hproduct : K.support = coordinatePlaneProduct
      (Complex.re '' K.support) (Complex.im '' K.support)) :
    K.openCarrier = coordinatePlaneProduct
      (interior (closure (Complex.re '' K.openCarrier)))
      (interior (closure (Complex.im '' K.openCarrier))) := by
  let X := Complex.re '' K.support
  let Y := Complex.im '' K.support
  have hXclosed : IsClosed X := (K.isPolygonal.isCompact.image Complex.continuous_re).isClosed
  have hYclosed : IsClosed Y := (K.isPolygonal.isCompact.image Complex.continuous_im).isClosed
  have hopen : K.openCarrier = coordinatePlaneProduct (interior X) (interior Y) := by
    rw [PolygonalRegion.openCarrier, hproduct, coordinatePlaneProduct_interior]
  obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hzXY : z.re ∈ interior X ∧ z.im ∈ interior Y := by
    have hzm : z ∈ coordinatePlaneProduct (interior X) (interior Y) := by rw [← hopen]; exact hz
    exact hzm
  have hprojX : Complex.re '' K.openCarrier = interior X := by
    apply Set.Subset.antisymm
    · rintro r ⟨w, hw, rfl⟩
      rw [hopen] at hw
      exact hw.1
    · intro r hr
      refine ⟨Complex.mk r z.im, ?_, rfl⟩
      rw [hopen]
      exact ⟨hr, hzXY.2⟩
  have hprojY : Complex.im '' K.openCarrier = interior Y := by
    apply Set.Subset.antisymm
    · rintro r ⟨w, hw, rfl⟩
      rw [hopen] at hw
      exact hw.2
    · intro r hr
      refine ⟨Complex.mk z.re r, ?_, rfl⟩
      rw [hopen]
      exact ⟨hzXY.1, hr⟩
  obtain ⟨hXreg, hYreg⟩ := coordinateProduct_factors_regularClosed K X Y hXclosed hYclosed hproduct
  rw [hprojX, hprojY, hXreg, hYreg]
  exact hopen

private theorem linearEquiv_image_vadd (A : Plane ≃L[ℝ] Plane)
    (u : Plane) (D : Set Plane) : A '' (u +ᵥ D) = A u +ᵥ (A '' D) := by
  apply Set.Subset.antisymm
  · rintro z ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨A d, ⟨d, hd, rfl⟩, by change A u + A d = A (u + d); rw [map_add]⟩
  · rintro z ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨u + d, Set.vadd_mem_vadd_set hd,
      by change A (u + d) = A u + A d; rw [map_add]⟩

private theorem affineImage_regularSupport (K : PolygonalRegion)
    (A : Plane ≃L[ℝ] Plane) (S : Set Plane) :
    regularSupport (affineImage K A 0) (A '' S) = A '' regularSupport K S := by
  have hmap : Tiling.Polygonal.affineMap A 0 = (A : Plane → Plane) := by
    funext x
    exact zero_add (A x)
  have hopen : (affineImage K A 0).openCarrier = A '' K.openCarrier := by
    have h := affineImage_openCarrier K A 0
    rw [hmap] at h
    exact h
  have hraw : openUnion (affineImage K A 0) (A '' S) = A '' openUnion K S := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
      obtain ⟨t, ht, hts⟩ := s.property
      have hzs : z ∈ A t +ᵥ (A '' K.openCarrier) := by rw [hopen, ← hts] at hs; exact hs
      rw [← linearEquiv_image_vadd] at hzs
      obtain ⟨x, hx, hAx⟩ := hzs
      exact ⟨x, Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hx⟩, hAx⟩
    · rintro z ⟨x, hx, rfl⟩
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      apply Set.mem_iUnion.mpr
      refine ⟨⟨A s, ⟨s, s.property, rfl⟩⟩, ?_⟩
      rw [hopen, ← linearEquiv_image_vadd]
      exact ⟨x, hs, rfl⟩
  rw [regularSupport, hraw]
  change interior (closure (A.toHomeomorph '' openUnion K S)) =
    A.toHomeomorph '' interior (closure (openUnion K S))
  rw [← A.toHomeomorph.image_closure, ← A.toHomeomorph.image_interior]

private theorem affineImage_centerColumn_iff
    (K : PolygonalRegion) (A : Plane ≃L[ℝ] Plane)
    (δ ε : Submodule ℝ Plane) (hdir : ∀ u, u ∈ δ ↔ A u ∈ ε)
    (C : Set Plane) (hp : IsPacking K.prototileFamily (K.placements C)) :
    IsCenterColumn K δ C ↔ IsCenterColumn (affineImage K A 0) ε (A '' C) := by
  have hmap : Tiling.Polygonal.affineMap A 0 = (A : Plane → Plane) := by
    funext x
    exact zero_add (A x)
  have htC : TilesOn (affineImage K A 0) (A '' C) (A '' regularSupport K C) := by
    have h := (tilesOn_affineImage_iff K A 0 C (regularSupport K C)).mpr
      (tilesOn_regularSupport_of_packing hp)
    rw [hmap] at h
    exact h
  constructor
  · rintro ⟨_, hCne, ⟨a, ha⟩, hinv⟩
    refine ⟨htC.2.1, hCne.image A, ⟨A a, ?_⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_sub]
      exact (hdir _).mp (ha x hx)
    · intro v hv
      have hu : A.symm v ∈ δ := (hdir _).mpr (by simpa using hv)
      rw [affineImage_regularSupport]
      calc
        v +ᵥ (A '' regularSupport K C) =
            A (A.symm v) +ᵥ (A '' regularSupport K C) := by rw [A.apply_symm_apply]
        _ = A '' (A.symm v +ᵥ regularSupport K C) :=
          (linearEquiv_image_vadd A _ _).symm
        _ = A '' regularSupport K C := by rw [hinv _ hu]
  · rintro ⟨_, hCne, ⟨a, ha⟩, hinv⟩
    have hsourceNe : C.Nonempty := by
      obtain ⟨_, x, hx, _⟩ := hCne
      exact ⟨x, hx⟩
    refine ⟨hp, hsourceNe, ⟨A.symm a, ?_⟩, ?_⟩
    · intro x hx
      apply (hdir _).mpr
      rw [map_sub, A.apply_symm_apply]
      exact ha (A x) ⟨x, hx, rfl⟩
    · intro u hu
      have h := hinv (A u) ((hdir _).mp hu)
      rw [affineImage_regularSupport, ← linearEquiv_image_vadd] at h
      exact A.injective.image_injective h

private theorem verticalDirection_mem_iff (z : Plane) :
    z ∈ Tiling.RationalSlopes.DirectionalRaster.verticalDirection ↔ z.re = 0 := by
  rw [Tiling.RationalSlopes.DirectionalRaster.verticalDirection,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    simp
  · intro hz
    refine ⟨z.im, ?_⟩
    apply Complex.ext
    · simp [hz]
    · simp

private theorem axisVertical_isCenterColumn_iff
    (R : Tiling.AxisParallel.Region) (C : Set Plane) :
    Tiling.AxisParallel.IsCenterColumn Tiling.AxisParallel.Axis.vertical R C ↔
      Tiling.Polygonal.IsCenterColumn R.toPolygonalRegion
        Tiling.RationalSlopes.DirectionalRaster.verticalDirection C := by
  constructor
  · rintro ⟨hpack, hne, ⟨c, hc⟩, hinv⟩
    refine ⟨hpack, hne, ?_, ?_⟩
    · refine ⟨(c : ℂ), ?_⟩
      intro z hz
      apply (verticalDirection_mem_iff (z - (c : ℂ))).mpr
      have hzcoord : z.re = c := by simpa [Tiling.AxisParallel.Axis.transverseCoord] using hc z hz
      simp [hzcoord]
    · intro u hu
      have hu' := (verticalDirection_mem_iff u).mp hu
      have heq : u = (u.im : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [hu']
        · simp
      change ∀ a : ℝ,
        (a : ℂ) * Complex.I +ᵥ Tiling.AxisParallel.regularSupport R C =
          Tiling.AxisParallel.regularSupport R C at hinv
      calc
        u +ᵥ Tiling.AxisParallel.regularSupport R C =
            (u.im : ℂ) * Complex.I +ᵥ Tiling.AxisParallel.regularSupport R C := by
              exact congrArg (fun v : Plane => v +ᵥ Tiling.AxisParallel.regularSupport R C) heq
        _ = Tiling.AxisParallel.regularSupport R C := hinv u.im
  · rintro ⟨hpack, hne, ⟨a, ha⟩, hinv⟩
    refine ⟨hpack, hne, ?_, ?_⟩
    · refine ⟨a.re, ?_⟩
      intro z hz
      have hz' := (verticalDirection_mem_iff (z - a)).mp (ha z hz)
      change z.re = a.re
      change z.re - a.re = 0 at hz'
      linarith
    · intro r
      have hu : (r : ℂ) * Complex.I ∈
          Tiling.RationalSlopes.DirectionalRaster.verticalDirection := by
        apply (verticalDirection_mem_iff ((r : ℂ) * Complex.I)).mpr
        simp
      simpa using hinv ((r : ℂ) * Complex.I) hu

private theorem columnPart_eq_verticalColumnCentres
    (R : Tiling.AxisParallel.Region) (T : Set Plane)
    (htile : Tiling.AxisParallel.TilesOn R T Set.univ) :
    Tiling.RationalSlopes.columnPart R.toPolygonalRegion
        Tiling.RationalSlopes.DirectionalRaster.verticalDirection T =
      Tiling.AxisParallel.Continuous.verticalColumnCentres R T := by
  classical
  have hδ : Module.finrank ℝ
      Tiling.RationalSlopes.DirectionalRaster.verticalDirection = 1 := by
    rw [Tiling.RationalSlopes.DirectionalRaster.verticalDirection,
      finrank_span_singleton Complex.I_ne_zero]
  have hpacking : Tiling.IsPacking R.toPolygonalRegion.prototileFamily
      (R.toPolygonalRegion.placements T) := htile.2.1
  ext x
  constructor
  · intro hx
    rw [Tiling.RationalSlopes.columnPart, Set.mem_iUnion] at hx
    obtain ⟨P, hxP⟩ := hx
    have hAxis := (axisVertical_isCenterColumn_iff R P.1.centres).2 P.2
    have hPsub : P.1.centres ⊆ T := by
      rintro z ⟨t, _, rfl⟩
      exact t.2
    obtain ⟨Q, hQcolumn, hxQ, hQeq⟩ :=
      Tiling.AxisParallel.Continuous.completeColumn_eq_verticalPlateThrough
        htile hAxis hPsub hxP
    rw [Tiling.AxisParallel.Continuous.verticalColumnCentres_eq, Set.mem_iUnion]
    exact ⟨⟨Q, hQcolumn⟩, hQeq ▸ hxQ⟩
  · intro hx
    rw [Tiling.AxisParallel.Continuous.verticalColumnCentres_eq, Set.mem_iUnion] at hx
    obtain ⟨⟨P, hPcolumn⟩, hxP⟩ := hx
    have hAxis :=
      Tiling.AxisParallel.Continuous.VerticalPlate.isCenterColumn_of_isVerticalColumn
        htile P hPcolumn
    have hGeneric := (axisVertical_isCenterColumn_iff R P.centres).mp hAxis
    have hPsub : P.centres ⊆ T := by
      rintro z ⟨t, _, rfl⟩
      exact t.2
    obtain ⟨Q, hQeq⟩ := Tiling.RationalSlopes.column_isComponent
      R.toPolygonalRegion Tiling.RationalSlopes.DirectionalRaster.verticalDirection
      T P.centres hδ hpacking hPsub hGeneric
    have hQgeneric : Tiling.Polygonal.IsCenterColumn R.toPolygonalRegion
        Tiling.RationalSlopes.DirectionalRaster.verticalDirection Q.centres := by
      simpa [hQeq] using hGeneric
    rw [Tiling.RationalSlopes.columnPart, Set.mem_iUnion]
    have hxQ : x ∈ Q.centres := by rw [hQeq]; exact hxP
    exact ⟨⟨Q, hQgeneric⟩, hxQ⟩

private theorem affineImage_wholePlaneTiles (K : PolygonalRegion)
    (A : Plane ≃L[ℝ] Plane) (T : Set Plane) (ht : TilesOn K T Set.univ) :
    TilesOn (affineImage K A 0) (A '' T) Set.univ := by
  have hwhole : Tiling.Polygonal.affineMap A 0 '' (Set.univ : Set Plane) = Set.univ := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · intro x _
      refine ⟨A.symm x, Set.mem_univ _, ?_⟩
      change (0 : Plane) + A (A.symm x) = x
      rw [zero_add, A.apply_symm_apply]
  have h := (tilesOn_affineImage_iff K A 0 T Set.univ).mpr ht
  rw [hwhole] at h
  exact h

private theorem affineImage_columnPart
    (K : PolygonalRegion) (A : Plane ≃L[ℝ] Plane)
    (δ ε : Submodule ℝ Plane) (hδ : Module.finrank ℝ δ = 1)
    (hε : Module.finrank ℝ ε = 1) (hdir : ∀ u, u ∈ δ ↔ A u ∈ ε)
    (T : Set Plane) (ht : TilesOn K T Set.univ) :
    A '' columnPart K δ T = columnPart (affineImage K A 0) ε (A '' T) := by
  classical
  let L := affineImage K A 0
  have himageTile := affineImage_wholePlaneTiles K A T ht
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [columnPart, Set.mem_iUnion] at hx
    obtain ⟨P, hxP⟩ := hx
    have hPsub : P.1.centres ⊆ T := by
      rintro s ⟨t, _, rfl⟩
      exact t.property
    have himageCol : IsCenterColumn L ε (A '' P.1.centres) :=
      (affineImage_centerColumn_iff K A δ ε hdir P.1.centres P.2.1).mp P.2
    obtain ⟨Q, hQ⟩ := column_isComponent L ε (A '' T) (A '' P.1.centres)
      hε himageTile.2.1 (Set.image_mono hPsub) himageCol
    have hQcol : IsCenterColumn L ε Q.centres := by rw [hQ]; exact himageCol
    rw [columnPart, Set.mem_iUnion]
    refine ⟨⟨Q, hQcol⟩, ?_⟩
    rw [hQ]
    exact ⟨x, hxP, rfl⟩
  · intro y hy
    rw [columnPart, Set.mem_iUnion] at hy
    obtain ⟨P, hyP⟩ := hy
    let C : Set Plane := A.symm '' P.1.centres
    have hPsub : P.1.centres ⊆ A '' T := by
      rintro s ⟨t, _, rfl⟩
      exact t.property
    have hCT : C ⊆ T := by
      rintro x ⟨d, hd, rfl⟩
      obtain ⟨t, htT, htd⟩ := hPsub hd
      rw [← htd, A.symm_apply_apply]
      exact htT
    have hpC : IsPacking K.prototileFamily (K.placements C) := by
      intro s hs t htC hst
      exact ht.2.1 (hCT hs) (hCT htC) hst
    have hAC : A '' C = P.1.centres := by
      apply Set.Subset.antisymm
      · rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
        simpa using hd
      · intro d hd
        exact ⟨A.symm d, ⟨d, hd, rfl⟩, A.apply_symm_apply d⟩
    have hCcol : IsCenterColumn K δ C := by
      apply (affineImage_centerColumn_iff K A δ ε hdir C hpC).mpr
      rw [hAC]
      exact P.2
    obtain ⟨Q, hQ⟩ := column_isComponent K δ T C hδ ht.2.1 hCT hCcol
    have hQcol : IsCenterColumn K δ Q.centres := by rw [hQ]; exact hCcol
    refine ⟨A.symm y, ?_, A.apply_symm_apply y⟩
    rw [columnPart, Set.mem_iUnion]
    refine ⟨⟨Q, hQcol⟩, ?_⟩
    rw [hQ]
    exact ⟨y, hyP, rfl⟩

theorem product_columnPart_universalTransversePeriod :
∀ (K : PolygonalRegion) (δ η : Submodule ℝ Plane),
    Module.finrank ℝ δ = 1 → Module.finrank ℝ η = 1 → δ ≠ η →
    IsProductAlong K δ η →
      ∃ periodVec : Plane, periodVec ∉ δ ∧ ∀ T : Set Plane, TilesOn K T Set.univ →
        (columnPart K δ T).Nonempty →
          periodVec ∈ periodGroup (regularSupport K (columnPart K δ T))
  := by
  intro K δ η hδ hη hne hproduct
  obtain ⟨A, hAδ, hAη⟩ := exists_real_straightening δ η hδ hη hne
  let L := affineImage K A 0
  have hLsupport : L.support = A '' K.support := by
    change Tiling.Polygonal.affineMap A 0 '' K.support = A '' K.support
    congr 1
    funext x
    exact zero_add (A x)
  have hLproduct : L.support = coordinatePlaneProduct
      (Complex.re '' L.support) (Complex.im '' L.support) := by
    rw [hLsupport]
    exact straightenedProduct_support K δ η A hAδ hAη hproduct
  let R : Tiling.AxisParallel.Region :=
    { toPolygonalRegion := L
      isAxisParallel := coordinateProduct_isAxisParallel L hLproduct }
  have hRproduct : Tiling.AxisParallel.Structure.IsProductRegion R :=
    coordinateProduct_openProduct L hLproduct
  obtain ⟨β, hβ, hperiod⟩ :=
    Tiling.AxisParallel.Structure.productRegion_columnUnion_horizontalPeriodic R hRproduct
  refine ⟨A.symm (β : Plane), ?_, ?_⟩
  · intro hpδ
    have hzero := (hAδ _).mp hpδ
    rw [A.apply_symm_apply, Complex.ofReal_re] at hzero
    exact (ne_of_gt hβ) hzero
  · intro T ht hcolumns
    let U := A '' T
    let C := columnPart K δ T
    have hTileR : Tiling.AxisParallel.TilesOn R U Set.univ :=
      affineImage_wholePlaneTiles K A T ht
    have hε : Module.finrank ℝ DirectionalRaster.verticalDirection = 1 := by
      rw [DirectionalRaster.verticalDirection, finrank_span_singleton Complex.I_ne_zero]
    have hdir : ∀ u, u ∈ δ ↔ A u ∈ DirectionalRaster.verticalDirection := by
      intro u
      rw [verticalDirection_mem_iff]
      exact hAδ u
    have haggregate : A '' C = Tiling.AxisParallel.Continuous.verticalColumnCentres R U :=
      (affineImage_columnPart K A δ DirectionalRaster.verticalDirection hδ hε hdir T ht).trans
        (columnPart_eq_verticalColumnCentres R U hTileR)
    have hcolumnsR : (Tiling.AxisParallel.Continuous.verticalColumnCentres R U).Nonempty := by
      rw [← haggregate]
      exact hcolumns.image A
    have hcarrier : Tiling.AxisParallel.regularSupport R
        (Tiling.AxisParallel.Continuous.verticalColumnCentres R U) = A '' regularSupport K C := by
      change regularSupport L (Tiling.AxisParallel.Continuous.verticalColumnCentres R U) =
        A '' regularSupport K C
      rw [← haggregate]
      exact affineImage_regularSupport K A C
    have hmembership := hperiod U hTileR hcolumnsR
    rw [hcarrier] at hmembership
    have himagePeriod : (β : Plane) +ᵥ (A '' regularSupport K C) = A '' regularSupport K C := by
      ext x
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change -(β : Plane) + x ∈ A '' regularSupport K C ↔ x ∈ A '' regularSupport K C
      have h := hmembership (x - (β : Plane))
      rw [sub_add_cancel] at h
      simpa only [sub_eq_add_neg, add_comm] using h.symm
    apply AddAction.mem_stabilizer_iff.mpr
    apply A.injective.image_injective
    rw [linearEquiv_image_vadd, A.apply_symm_apply]
    exact himagePeriod

-- Native axiom audit: owned public declarations, substantive constructed
-- branches, and the exact imported providers used at the fragile seams.

end Tiling.RationalSlopes
