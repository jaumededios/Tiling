import Tiling.AxisParallel.Continuous.PlateCore
import Tiling.AxisParallel.Foundations.PositiveSimilarityTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Continuous

open Tiling.AxisParallel

private def positiveSimilarityAffineMap (s : ℝ) (b : Tiling.Plane) :
    Tiling.Plane →ᵃ[ℝ] Tiling.Plane where
  toFun := positiveSimilarity s b
  linear := s • LinearMap.id
  map_vadd' p v := by
    simp [positiveSimilarity, vadd_eq_add, smul_add]
    abel

private theorem positiveSimilarity_openSegment_image
    (s : ℝ) (b x y : Tiling.Plane) :
    positiveSimilarity s b '' openSegment ℝ x y =
      openSegment ℝ (positiveSimilarity s b x) (positiveSimilarity s b y) := by
  simpa [positiveSimilarityAffineMap] using
    (image_openSegment ℝ (positiveSimilarityAffineMap s b) x y)

private theorem positiveSimilarity_im
    (s : ℝ) (b z : Tiling.Plane) :
    (positiveSimilarity s b z).im = s * z.im + b.im := by
  simp [positiveSimilarity]

theorem horizontalProperContact_positiveSimilarity_iff
    {K R : Region} {s : ℝ} {r c : Tiling.Plane} (hs : 0 < s)
    (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (a b : Tiling.Plane) :
    HorizontalProperContact K a b ↔
      HorizontalProperContact R
        (positiveSimilarity s c a) (positiveSimilarity s c b) := by
  have hsupport : R.support = positiveSimilarity s r '' K.support :=
    positiveSimilarity_support_image hs hcarrier
  have hvertices : R.vertices = positiveSimilarity s r '' K.vertices :=
    positiveSimilarity_vertices_image hs hcarrier
  let G : Tiling.Plane → Tiling.Plane := positiveSimilarity s (r + c)
  let H := positiveSimilarityHomeomorph s (r + c) hs
  have hsupport_image (t : Tiling.Plane) :
      positiveSimilarity s c t +ᵥ R.support = G '' (t +ᵥ K.support) := by
    rw [hsupport]
    exact positiveSimilarity_vadd_image_of_carrier (t := t) (c := c)
      (U := K.support) (V := positiveSimilarity s r '' K.support) rfl
  have hvertices_image (t : Tiling.Plane) :
      positiveSimilarity s c t +ᵥ R.vertices = G '' (t +ᵥ K.vertices) := by
    rw [hvertices]
    exact positiveSimilarity_vadd_image_of_carrier (t := t) (c := c)
      (U := K.vertices) (V := positiveSimilarity s r '' K.vertices) rfl
  have hfrontier_image (t : Tiling.Plane) :
      frontier (positiveSimilarity s c t +ᵥ R.support) =
        G '' frontier (t +ᵥ K.support) := by
    rw [hsupport_image]
    simpa [G, H] using (H.image_frontier (t +ᵥ K.support)).symm
  have hopenSegment_image (x y : Tiling.Plane) :
      G '' openSegment ℝ x y = openSegment ℝ (G x) (G y) := by
    simpa [G] using positiveSimilarity_openSegment_image s (r + c) x y
  have him (x y : Tiling.Plane) (hxy : x.im = y.im) :
      (G x).im = (G y).im := by
    rw [positiveSimilarity_im, positiveSimilarity_im, hxy]
  constructor
  · rintro ⟨x, y, hxy, himxy, hsub⟩
    refine ⟨G x, G y, ?_, him x y himxy, ?_⟩
    · intro heq
      apply hxy
      exact positiveSimilarity_injective hs heq
    · intro z hz
      rw [← hopenSegment_image] at hz
      rcases hz with ⟨w, hw, rfl⟩
      have hsource := hsub hw
      rw [hfrontier_image a, hfrontier_image b,
        hvertices_image a, hvertices_image b]
      refine ⟨⟨⟨w, hsource.1.1, rfl⟩, ⟨w, hsource.1.2, rfl⟩⟩, ?_⟩
      intro hv
      rcases hv with hv | hv
      · rcases hv with ⟨u, hu, huu⟩
        have huw : u = w := positiveSimilarity_injective hs huu
        exact hsource.2 (Or.inl (huw ▸ hu))
      · rcases hv with ⟨u, hu, huu⟩
        have huw : u = w := positiveSimilarity_injective hs huu
        exact hsource.2 (Or.inr (huw ▸ hu))
  · rintro ⟨x', y', hxy', himxy', hsub'⟩
    obtain ⟨x, hx⟩ := positiveSimilarity_surjective hs x'
    obtain ⟨y, hy⟩ := positiveSimilarity_surjective hs y'
    refine ⟨x, y, ?_, ?_, ?_⟩
    · intro hxy
      apply hxy'
      rw [← hx, ← hy, hxy]
    · have hGx : G x = x' := by simpa [G] using hx
      have hGy : G y = y' := by simpa [G] using hy
      have himxy'' : (G x).im = (G y).im := by
        rw [hGx, hGy]
        exact himxy'
      rw [positiveSimilarity_im, positiveSimilarity_im] at himxy''
      have hmul : s * x.im = s * y.im := by
        linarith [himxy'']
      exact mul_left_cancel₀ (ne_of_gt hs) hmul
    · intro z hz
      have hzG : G z ∈ openSegment ℝ x' y' := by
        rw [← hx, ← hy, ← hopenSegment_image]
        exact ⟨z, hz, rfl⟩
      have htarget := hsub' hzG
      have hfrontx : G z ∈ G '' frontier (a +ᵥ K.support) := by
        rw [← hfrontier_image a]
        exact htarget.1.1
      have hfronty : G z ∈ G '' frontier (b +ᵥ K.support) := by
        rw [← hfrontier_image b]
        exact htarget.1.2
      rcases hfrontx with ⟨u, hu, huz⟩
      have huz' : u = z := positiveSimilarity_injective hs huz
      have hsourcex : z ∈ frontier (a +ᵥ K.support) := huz' ▸ hu
      rcases hfronty with ⟨v, hv, hvz⟩
      have hvz' : v = z := positiveSimilarity_injective hs hvz
      have hsourcey : z ∈ frontier (b +ᵥ K.support) := hvz' ▸ hv
      refine ⟨⟨hsourcex, hsourcey⟩, ?_⟩
      intro hv
      apply htarget.2
      rcases hv with hv | hv
      · apply Or.inl
        rw [hvertices_image a]
        exact ⟨z, hv, rfl⟩
      · apply Or.inr
        rw [hvertices_image b]
        exact ⟨z, hv, rfl⟩

noncomputable def positiveSimilarityCentreEquiv
    {T : Set Tiling.Plane} {s : ℝ} (hs : 0 < s) (c : Tiling.Plane) :
    T ≃ (positiveSimilarity s c '' T) :=
  Equiv.Set.image (positiveSimilarity s c) T (positiveSimilarity_injective hs)

theorem positiveSimilarityCentreEquiv_apply
    {T : Set Tiling.Plane} {s : ℝ} (hs : 0 < s) (c : Tiling.Plane)
    (t : T) :
    (positiveSimilarityCentreEquiv hs c t : Tiling.Plane) =
      positiveSimilarity s c t.1 := by
  rfl

private theorem graphIso_mem_supp
    {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (P : G.ConnectedComponent) (v : V) :
    v ∈ P.supp ↔ e v ∈ (e.connectedComponentEquiv P).supp := by
  constructor
  · intro hv
    have hP : G.connectedComponentMk v = P :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff P v).mp hv
    have hQ : H.connectedComponentMk (e v) = e.connectedComponentEquiv P := by
      rw [← hP]
      rfl
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff
      (e.connectedComponentEquiv P) (e v)).mpr hQ
  · intro hv
    have hQ : H.connectedComponentMk (e v) = e.connectedComponentEquiv P :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff
        (e.connectedComponentEquiv P) (e v)).mp hv
    have hP := (SimpleGraph.ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map
      (φ := e) (C := P) (v' := e v)).mpr hQ
    change G.connectedComponentMk (e.symm (e v)) = P at hP
    simpa using hP

noncomputable def verticalPlateGraph_positiveSimilarityIso
    {K R : Region} {T : Set Tiling.Plane} {s : ℝ} {r : Tiling.Plane}
    (hs : 0 < s) (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (c : Tiling.Plane) :
    verticalPlateGraph K T ≃g
      verticalPlateGraph R (positiveSimilarity s c '' T) := by
  let f := positiveSimilarityCentreEquiv hs c (T := T)
  refine ⟨f, ?_⟩
  intro a b
  simp only [verticalPlateGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hrel⟩
    refine ⟨fun heq => hne (congrArg f heq), ?_⟩
    rcases hrel with hab | hba
    · exact Or.inl ((horizontalProperContact_positiveSimilarity_iff hs hcarrier
        a.1 b.1).mpr hab)
    · exact Or.inr ((horizontalProperContact_positiveSimilarity_iff hs hcarrier
        b.1 a.1).mpr hba)
  · rintro ⟨hne, hrel⟩
    refine ⟨fun heq => hne (f.injective heq), ?_⟩
    rcases hrel with hab | hba
    · exact Or.inl ((horizontalProperContact_positiveSimilarity_iff hs hcarrier
        a.1 b.1).mp hab)
    · exact Or.inr ((horizontalProperContact_positiveSimilarity_iff hs hcarrier
        b.1 a.1).mp hba)

theorem verticalPlateGraph_positiveSimilarityIso_apply
    {K R : Region} {T : Set Tiling.Plane} {s : ℝ} {r : Tiling.Plane}
    (hs : 0 < s) (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (c : Tiling.Plane) (t : T) :
    (verticalPlateGraph_positiveSimilarityIso hs hcarrier c t : Tiling.Plane) =
      positiveSimilarity s c t.1 := by
  change (positiveSimilarityCentreEquiv hs c t : Tiling.Plane) = _
  rfl

noncomputable def verticalPlate_positiveSimilarityEquiv
    {K R : Region} {T : Set Tiling.Plane} {s : ℝ} {r : Tiling.Plane}
    (hs : 0 < s) (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (c : Tiling.Plane) :
    VerticalPlate K T ≃ VerticalPlate R (positiveSimilarity s c '' T) :=
  (verticalPlateGraph_positiveSimilarityIso hs hcarrier c).connectedComponentEquiv

theorem verticalPlate_positiveSimilarityEquiv_mem_centres
    {K R : Region} {T : Set Tiling.Plane} {s : ℝ} {r : Tiling.Plane}
    (hs : 0 < s) (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (c : Tiling.Plane) (P : VerticalPlate K T) (t : T) :
    t.1 ∈ P.centres ↔
      (positiveSimilarity s c t.1) ∈
        (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).centres := by
  let e : verticalPlateGraph K T ≃g
      verticalPlateGraph R (positiveSimilarity s c '' T) :=
    verticalPlateGraph_positiveSimilarityIso hs hcarrier c
  have h := graphIso_mem_supp (e := e) P t
  change t.1 ∈ Subtype.val '' P.supp ↔
    (positiveSimilarity s c t.1) ∈
      Subtype.val '' (e.connectedComponentEquiv P).supp
  constructor
  · rintro ⟨u, hu, hut⟩
    have hut' : (u : T) = t := Subtype.ext hut
    have ht : t ∈ P.supp := hut' ▸ hu
    have hmap := h.mp ht
    exact ⟨e t, hmap, rfl⟩
  · rintro ⟨u, hu, hut⟩
    have hut' : (u : (positiveSimilarity s c '' T)) = e t := Subtype.ext hut
    have hmap : e t ∈ (e.connectedComponentEquiv P).supp := hut' ▸ hu
    have ht : t ∈ P.supp := h.mpr hmap
    exact ⟨t, ht, rfl⟩

theorem verticalPlate_positiveSimilarityEquiv_centres_image
    {K R : Region} {T : Set Tiling.Plane} {s : ℝ} {r : Tiling.Plane}
    (hs : 0 < s) (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (c : Tiling.Plane) (P : VerticalPlate K T) :
    (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).centres =
      positiveSimilarity s c '' P.centres := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨u, hu, huz⟩
    let t : T := (positiveSimilarityCentreEquiv hs c).symm u
    have htarget : u.1 ∈
        (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).centres :=
      ⟨u, hu, rfl⟩
    have htarg : (positiveSimilarity s c t.1) ∈
        (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).centres := by
      have hut := (positiveSimilarityCentreEquiv hs c).apply_symm_apply u
      have hut' : (positiveSimilarityCentreEquiv hs c t : Tiling.Plane) = u :=
        congrArg Subtype.val hut
      change (positiveSimilarityCentreEquiv hs c t : Tiling.Plane) ∈
        (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).centres
      rw [hut']
      exact htarget
    have hsource : t.1 ∈ P.centres :=
      (verticalPlate_positiveSimilarityEquiv_mem_centres hs hcarrier c P t).mpr
        htarg
    refine ⟨t.1, hsource, ?_⟩
    have hut := (positiveSimilarityCentreEquiv hs c).apply_symm_apply u
    have hut' : (positiveSimilarityCentreEquiv hs c t : Tiling.Plane) = u :=
      congrArg Subtype.val hut
    have hF : positiveSimilarity s c t.1 = u.1 := by
      simpa [positiveSimilarityCentreEquiv_apply] using hut'
    exact hF.trans huz
  · rintro ⟨z₀, hz₀, rfl⟩
    rcases hz₀ with ⟨t, ht, rfl⟩
    have hP : t.1 ∈ P.centres := ⟨t, ht, rfl⟩
    exact (verticalPlate_positiveSimilarityEquiv_mem_centres
      hs hcarrier c P t).mp hP

theorem verticalPlate_positiveSimilarityEquiv_support_image
    {K R : Region} {T : Set Tiling.Plane} {s : ℝ} {r : Tiling.Plane}
    (hs : 0 < s) (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (c : Tiling.Plane) (P : VerticalPlate K T) :
    (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).support =
      positiveSimilarity s (r + c) '' P.support := by
  change regularSupport R
      (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).centres =
    positiveSimilarity s (r + c) '' regularSupport K P.centres
  rw [verticalPlate_positiveSimilarityEquiv_centres_image]
  exact positiveSimilarity_regularSupport_image hs hcarrier

theorem verticalPlate_positiveSimilarityEquiv_base_affine_real_image
    {K R : Region} {T : Set Tiling.Plane} {s : ℝ} {r : Tiling.Plane}
    (hs : 0 < s) (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (c : Tiling.Plane) (P : VerticalPlate K T) :
    (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).base =
      (fun x : ℝ => s * x + (r + c).re) '' P.base := by
  change Complex.re ''
      (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).support =
    (fun x : ℝ => s * x + (r + c).re) '' (Complex.re '' P.support)
  ext y
  constructor
  · rintro ⟨w, hw, hwy⟩
    have hw' : w ∈ positiveSimilarity s (r + c) '' P.support := by
      rw [← verticalPlate_positiveSimilarityEquiv_support_image hs hcarrier c P]
      exact hw
    rcases hw' with ⟨z, hz, rfl⟩
    refine ⟨z.re, ⟨z, hz, rfl⟩, ?_⟩
    simpa [positiveSimilarity] using hwy
  · rintro ⟨x, ⟨z, hz, hzx⟩, hy⟩
    have hFz : positiveSimilarity s (r + c) z ∈
        (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).support := by
      rw [verticalPlate_positiveSimilarityEquiv_support_image hs hcarrier c P]
      exact ⟨z, hz, rfl⟩
    refine ⟨positiveSimilarity s (r + c) z, hFz, ?_⟩
    simpa [positiveSimilarity, hzx] using hy

theorem verticalPlate_positiveSimilarityEquiv_isVerticalColumn
    {K R : Region} {T : Set Tiling.Plane} {s : ℝ} {r : Tiling.Plane}
    (hs : 0 < s) (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (c : Tiling.Plane) (P : VerticalPlate K T) :
    IsVerticalColumn P ↔
      IsVerticalColumn (verticalPlate_positiveSimilarityEquiv hs hcarrier c P) := by
  change (∃ x : ℝ, P.centres ⊆ {z : Tiling.Plane | z.re = x}) ↔
    (∃ y : ℝ,
      (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).centres ⊆
        {z : Tiling.Plane | z.re = y})
  have hreal (z : Tiling.Plane) :
      (positiveSimilarity s c z).re = s * z.re + c.re := by
    simp [positiveSimilarity]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨s * x + c.re, ?_⟩
    intro z hz
    rw [verticalPlate_positiveSimilarityEquiv_centres_image hs hcarrier c P] at hz
    rcases hz with ⟨z₀, hz₀, hzz⟩
    rw [← hzz]
    change (positiveSimilarity s c z₀).re = s * x + c.re
    rw [hreal, hx hz₀]
  · rintro ⟨y, hy⟩
    refine ⟨(y - c.re) / s, ?_⟩
    intro z hz
    rcases hz with ⟨t, ht, hzt⟩
    have hz' : positiveSimilarity s c t.1 ∈
        (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).centres :=
      (verticalPlate_positiveSimilarityEquiv_mem_centres
        hs hcarrier c P t).mp ⟨t, ht, rfl⟩
    have hcoord := hy hz'
    change (positiveSimilarity s c t.1).re = y at hcoord
    rw [hreal] at hcoord
    rw [← hzt]
    change t.1.re = (y - c.re) / s
    apply (eq_div_iff (ne_of_gt hs)).2
    nlinarith [hcoord]

theorem verticalColumnCentres_positiveSimilarity_image
    {K R : Region} {T : Set Tiling.Plane} {s : ℝ} {r : Tiling.Plane}
    (hs : 0 < s) (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (c : Tiling.Plane) :
    verticalColumnCentres R (positiveSimilarity s c '' T) =
      positiveSimilarity s c '' verticalColumnCentres K T := by
  ext z
  constructor
  · intro hz
    change z ∈ ⋃ Q : {Q : VerticalPlate R (positiveSimilarity s c '' T) //
      IsVerticalColumn Q}, Q.1.centres at hz
    rcases Set.mem_iUnion.mp hz with ⟨Q, hzQ⟩
    rcases hzQ with ⟨u, hu, huz⟩
    let e : verticalPlateGraph K T ≃g
        verticalPlateGraph R (positiveSimilarity s c '' T) :=
      verticalPlateGraph_positiveSimilarityIso hs hcarrier c
    let pe := e.connectedComponentEquiv
    let P : VerticalPlate K T := pe.symm Q.1
    let t : T := (positiveSimilarityCentreEquiv hs c).symm u
    have hQmem : u.1 ∈ Q.1.centres := ⟨u, hu, rfl⟩
    have hPcol : IsVerticalColumn P := by
      have hEq : pe P = Q.1 := pe.apply_symm_apply Q.1
      exact (verticalPlate_positiveSimilarityEquiv_isVerticalColumn
        hs hcarrier c P).mpr (hEq ▸ Q.2)
    have hPmem : t.1 ∈ P.centres :=
      (verticalPlate_positiveSimilarityEquiv_mem_centres
        hs hcarrier c P t).mpr (by
          have hut := (positiveSimilarityCentreEquiv hs c).apply_symm_apply u
          have hut' : (positiveSimilarityCentreEquiv hs c t : Tiling.Plane) = u :=
            congrArg Subtype.val hut
          have hEq : verticalPlate_positiveSimilarityEquiv hs hcarrier c P = Q.1 := by
            exact pe.apply_symm_apply Q.1
          change (positiveSimilarityCentreEquiv hs c t : Tiling.Plane) ∈
            (verticalPlate_positiveSimilarityEquiv hs hcarrier c P).centres
          rw [hEq]
          rw [hut']
          exact hQmem)
    refine ⟨t.1, ?_, ?_⟩
    · change t.1 ∈ ⋃ P : {P : VerticalPlate K T // IsVerticalColumn P}, P.1.centres
      rw [Set.mem_iUnion]
      exact ⟨⟨P, hPcol⟩, hPmem⟩
    · have hut := (positiveSimilarityCentreEquiv hs c).apply_symm_apply u
      have hut' : (positiveSimilarityCentreEquiv hs c t : Tiling.Plane) = u :=
        congrArg Subtype.val hut
      have hF : positiveSimilarity s c t.1 = u.1 := by
        simpa [positiveSimilarityCentreEquiv_apply] using hut'
      exact hF.trans huz
  · intro hz
    change z ∈ positiveSimilarity s c '' verticalColumnCentres K T at hz
    rcases hz with ⟨z₀, hz₀, hzEq⟩
    change z₀ ∈ ⋃ P : {P : VerticalPlate K T // IsVerticalColumn P}, P.1.centres at hz₀
    rcases Set.mem_iUnion.mp hz₀ with ⟨P, htP⟩
    rcases htP with ⟨t, ht, hzt⟩
    have hQcol : IsVerticalColumn
        (verticalPlate_positiveSimilarityEquiv hs hcarrier c P.1) :=
      (verticalPlate_positiveSimilarityEquiv_isVerticalColumn
        hs hcarrier c P.1).mp P.2
    have htQ : positiveSimilarity s c t.1 ∈
        (verticalPlate_positiveSimilarityEquiv hs hcarrier c P.1).centres :=
      (verticalPlate_positiveSimilarityEquiv_mem_centres hs hcarrier c P.1 t).mp
        ⟨t, ht, rfl⟩
    have hzfinal : z = positiveSimilarity s c t.1 := by
      calc
        z = positiveSimilarity s c z₀ := hzEq.symm
        _ = positiveSimilarity s c t.1 := by rw [hzt]
    rw [hzfinal]
    change positiveSimilarity s c t.1 ∈
      ⋃ Q : {Q : VerticalPlate R (positiveSimilarity s c '' T) //
        IsVerticalColumn Q}, Q.1.centres
    rw [Set.mem_iUnion]
    exact ⟨⟨verticalPlate_positiveSimilarityEquiv hs hcarrier c P.1, hQcol⟩, htQ⟩

theorem verticalColumnSupport_positiveSimilarity_image
    {K R : Region} {T : Set Tiling.Plane} {s : ℝ} {r : Tiling.Plane}
    (hs : 0 < s) (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (c : Tiling.Plane) :
    regularSupport R (verticalColumnCentres R (positiveSimilarity s c '' T)) =
      positiveSimilarity s (r + c) '' regularSupport K (verticalColumnCentres K T) := by
  rw [verticalColumnCentres_positiveSimilarity_image hs hcarrier c]
  exact positiveSimilarity_regularSupport_image hs hcarrier

end Tiling.AxisParallel.Continuous
