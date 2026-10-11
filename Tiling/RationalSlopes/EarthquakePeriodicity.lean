import Tiling.RationalSlopes.Links
import Tiling.RationalSlopes.Approximation.LinkTransport
import Tiling.RationalSlopes.DirectionalRaster
-- ROOT APPROVED focused generic order provider, shared read-only CP proof pattern.
import Mathlib.Order.SuccPred.LinearLocallyFinite

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

private theorem integer_gap_shift (x : ℤ → ℝ) (k : ℤ)
    (hgap : ∀ i : ℤ,
      x (i + 1) - x i = x (i + k + 1) - x (i + k)) :
    ∀ i : ℤ, x (i + k) - x i = x k - x 0 := by
  let displacement : ℤ → ℝ := fun i => x (i + k) - x i
  have hdisplacement_succ (i : ℤ) : displacement (i + 1) = displacement i := by
    dsimp [displacement]
    have hindex : i + 1 + k = i + k + 1 := by omega
    rw [hindex]
    linarith [hgap i]
  have hdisplacement (i : ℤ) : displacement i = displacement 0 := by
    refine Int.inductionOn' i 0 rfl ?_ ?_
    · intro j _hj hj
      exact (hdisplacement_succ j).trans hj
    · intro j _hj hj
      calc
        displacement (j - 1) = displacement ((j - 1) + 1) :=
          (hdisplacement_succ (j - 1)).symm
        _ = displacement j := by congr 1; omega
        _ = displacement 0 := hj
  intro i
  simpa [displacement] using hdisplacement i

private theorem strict_mono_surjective_int_shift (f : ℤ → ℤ)
    (hf : StrictMono f) (hsurj : Function.Surjective f) :
    ∀ i : ℤ, f i = i + f 0 := by
  have hstep (i : ℤ) : f (i + 1) = f i + 1 := by
    have hstrict : f i < f (i + 1) := hf (by omega)
    by_contra hne
    have hgap : f i + 1 < f (i + 1) := by omega
    obtain ⟨j, hj⟩ := hsurj (f i + 1)
    by_cases hji : j ≤ i
    · have hmono := hf.monotone hji
      rw [hj] at hmono
      omega
    · have hij : i + 1 ≤ j := by omega
      have hmono := hf.monotone hij
      rw [hj] at hmono
      omega
  let displacement : ℤ → ℤ := fun i => f i - i
  have hdisplacement_succ (i : ℤ) : displacement (i + 1) = displacement i := by
    dsimp [displacement]
    rw [hstep i]
    omega
  have hdisplacement (i : ℤ) : displacement i = displacement 0 := by
    refine Int.inductionOn' i 0 rfl ?_ ?_
    · intro j _hj hj
      exact (hdisplacement_succ j).trans hj
    · intro j _hj hj
      calc
        displacement (j - 1) = displacement ((j - 1) + 1) :=
          (hdisplacement_succ (j - 1)).symm
        _ = displacement j := by congr 1; omega
        _ = displacement 0 := hj
  intro i
  dsimp [displacement] at hdisplacement
  linarith [hdisplacement i]

private theorem integer_chain_period_shift (x : ℤ → ℝ) (hx : StrictMono x)
    (β : ℝ) (hβ : β ≠ 0) (hperiod : β ∈ periodGroup (Set.range x)) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ i : ℤ, x (i + k) = x i + β := by
  have hshift : β +ᵥ Set.range x = Set.range x := by
    change β ∈ AddAction.stabilizer ℝ (Set.range x) at hperiod
    exact AddAction.mem_stabilizer_iff.mp hperiod
  have hex (i : ℤ) : ∃ j : ℤ, x j = x i + β := by
    have hmem : x i + β ∈ Set.range x := by
      rw [← hshift]
      exact ⟨x i, Set.mem_range_self i, by simp only [vadd_eq_add]; ring⟩
    exact hmem
  choose f hf using hex
  have hfmono : StrictMono f := by
    intro i j hij
    apply hx.lt_iff_lt.mp
    rw [hf i, hf j]
    linarith [hx hij]
  have hfsurj : Function.Surjective f := by
    intro j
    have hmem : x j ∈ β +ᵥ Set.range x := by rw [hshift]; exact Set.mem_range_self j
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hmem
    refine ⟨i, hx.injective ?_⟩
    rw [hf i]
    simpa only [vadd_eq_add, add_comm] using hi
  have hfshift := strict_mono_surjective_int_shift f hfmono hfsurj
  refine ⟨f 0, ?_, ?_⟩
  · intro hk
    have hh := hf 0
    rw [hk] at hh
    exact hβ (by linarith)
  · intro i
    rw [← hfshift i]
    exact hf i

private theorem exists_outside_direction (δ : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) : ∃ v : Plane, v ∉ δ := by
  classical
  by_contra h
  push Not at h
  have htop : δ = ⊤ := top_unique (fun v _ => h v)
  rw [htop, finrank_top, Complex.finrank_real_complex] at hδ
  norm_num at hδ

/-- If the column aggregate contains every centre, each graph component is a column.
This is a quotient/partition fact and does not require an interval-period provider. -/
private theorem all_components_columns_of_columnPart_eq
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    (hcol : T = columnPart K δ T) :
    ∀ P : EarthquakeComponent K δ T, IsCenterColumn K δ P.centres := by
  intro P
  obtain ⟨t, ht⟩ := P.nonempty_supp
  have htc : (t : Plane) ∈ columnPart K δ T := by
    rw [← hcol]
    exact t.property
  obtain ⟨Q, hQ⟩ := Set.mem_iUnion.mp htc
  obtain ⟨s, hs, hst⟩ := hQ
  have hst' : s = t := Subtype.ext hst
  subst s
  have hPQ : P = Q.1 :=
    SimpleGraph.ConnectedComponent.eq_of_common_vertex ht hs
  simpa only [hPQ] using Q.property

private theorem exists_noncolumn_of_ne_columnPart
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    (hcol : T ≠ columnPart K δ T) :
    ∃ P : EarthquakeComponent K δ T, P ∈ noncolumnComponents K δ T := by
  classical
  have hcolT : columnPart K δ T ⊆ T := by
    intro t ht
    obtain ⟨Q, hQ⟩ := Set.mem_iUnion.mp ht
    obtain ⟨s, _hs, rfl⟩ := hQ
    exact s.property
  have hnot : ¬T ⊆ columnPart K δ T := by
    intro h
    exact hcol (Set.Subset.antisymm h hcolT)
  obtain ⟨t, ht, htnot⟩ := Set.not_subset.mp hnot
  let s : T := ⟨t, ht⟩
  let P := (earthquakeGraph K δ T).connectedComponentMk s
  refine ⟨P, ?_⟩
  intro hP
  apply htnot
  exact Set.mem_iUnion.mpr ⟨⟨P, hP⟩, ⟨s, rfl, rfl⟩⟩

private theorem columnPart_eq_commonCarrierPeriod
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (hcol : T = columnPart K δ T) :
    ∃ periodVec : Plane, IsCommonCarrierPeriod K δ T periodVec := by
  obtain ⟨v, hv⟩ := exists_outside_direction δ hδ
  have hsupport : regularSupport K (columnPart K δ T) = Set.univ := by
    rw [← hcol]
    exact regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  refine ⟨v, hv, ?_, ?_⟩
  · rw [hsupport]
    simp [periodGroup]
  · intro P hP
    exact (hP : ¬IsCenterColumn K δ P.centres)
      (all_components_columns_of_columnPart_eq hcol P) |>.elim

private theorem relativelyRational_of_rationalSupport
    (K : PolygonalRegion) (hK : Tiling.IsRational K.support) :
    Tiling.RationalPolygonal.IsRelativelyRational K := by
  obtain ⟨x, hx⟩ := K.nonempty
  rw [← K.isPolygonal.iUnion_closure_interiorComponents] at hx
  obtain ⟨O, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hO, _hx⟩ := Set.mem_iUnion.mp hx
  have hre : Complex.reCLM.toLinearMap ≠ 0 := by
    intro h
    have h1 := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f 1) h
    norm_num at h1
  obtain ⟨v, hv, _⟩ :=
    K.isPolygonal.exists_interiorComponent_min_vertex hO Complex.reCLM.toLinearMap hre
  refine ⟨v, hv, ?_⟩
  intro w hw
  obtain ⟨a, b, ha, hb⟩ := hK.2 w hw
  obtain ⟨c, d, hc, hd⟩ := hK.2 v hv
  refine ⟨a - c, b - d, ?_, ?_⟩
  · simp only [Complex.sub_re, ha, hc, Rat.cast_sub]
  · simp only [Complex.sub_im, hb, hd, Rat.cast_sub]

private theorem invariantAlong_projection_preimage
    (D : Set Plane) (δ : Submodule ℝ Plane) (π : Plane →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker π = δ) (hD : IsInvariantAlong D δ) :
    π ⁻¹' (π '' D) = D := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hδ : x - y ∈ δ := by
      rw [← hker, LinearMap.mem_ker, map_sub, hxy, sub_self]
    rw [← hD (x - y) hδ]
    exact ⟨y, hy, by simp [vadd_eq_add]⟩
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem transverse_projection_locallyFinite
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hflc : HasTransverseFLC K δ T) (π : Plane →L[ℝ] ℝ)
    (hπ : Function.Surjective π) (hker : LinearMap.ker π.toLinearMap = δ) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q →
      ((π '' translatedVertices K T) ∩ Q).Finite := by
  obtain ⟨ℓ, hℓne, hℓker, hℓflc⟩ := hflc
  obtain ⟨e, he⟩ := hπ 1
  have hformula (u : Plane) : ℓ u = π u * ℓ e := by
    have hδ : u - π u • e ∈ δ := by
      rw [← hker, LinearMap.mem_ker]
      simp only [ContinuousLinearMap.coe_coe, map_sub, map_smul, he, smul_eq_mul, mul_one, sub_self]
    have hzero : ℓ (u - π u • e) = 0 := by
      exact LinearMap.mem_ker.mp (hℓker.symm ▸ hδ)
    simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] using hzero
  have hρne : ℓ e ≠ 0 := by
    intro hzero
    apply hℓne
    ext u
    change ℓ u = 0
    simpa only [hzero, mul_zero] using hformula u
  intro Q hQ
  obtain ⟨R, _hR, hbound⟩ := hQ.exists_pos_norm_le
  have hfinite := hℓflc.1 (Metric.closedBall 0 (R * |ℓ e|)) Metric.isBounded_closedBall
  apply (hfinite.image (fun r : ℝ => r / ℓ e)).subset
  rintro y ⟨⟨u, hu, rfl⟩, hyQ⟩
  refine ⟨ℓ u, ⟨⟨u, hu, rfl⟩, ?_⟩, ?_⟩
  · simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    rw [hformula u, abs_mul]
    exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hbound _ hyQ)
      (abs_nonneg _)
  · change ℓ u / ℓ e = π u
    rw [hformula u, mul_div_cancel_right₀ _ hρne]

private theorem exists_ordered_integer_chain
    (Y : Set ℝ) (hfinite : ∀ a b : ℝ, (Y ∩ Set.Icc a b).Finite)
    (habove : ∀ r : ℝ, ∃ a ∈ Y, r < a) (hbelow : ∀ r : ℝ, ∃ a ∈ Y, a < r) :
    ∃ y : ℤ → ℝ, Set.range y = Y ∧ StrictMono y := by
  classical
  obtain ⟨y0, hy0⟩ := habove 0
  let α := {x : ℝ // x ∈ Y}
  have hIccFinite : ∀ a b : α, (Set.Icc a b).Finite := by
    intro a b
    have hreal : (Y ∩ Set.Icc (a : ℝ) (b : ℝ)).Finite := hfinite _ _
    have hpre : ((fun x : α => (x : ℝ)) ⁻¹' (Y ∩ Set.Icc (a : ℝ) (b : ℝ))).Finite :=
      hreal.preimage (by
        intro x hx z hz hxz
        exact Subtype.ext hxz)
    apply hpre.subset
    intro x hx
    change a ≤ x ∧ x ≤ b at hx
    change (x : ℝ) ∈ Y ∩ Set.Icc (a : ℝ) (b : ℝ)
    exact ⟨x.2, hx⟩
  let : LocallyFiniteOrder α := LocallyFiniteOrder.ofFiniteIcc hIccFinite
  have : Nonempty α := ⟨⟨y0, hy0.1⟩⟩
  have : NoMaxOrder α := ⟨fun a => by
    obtain ⟨z, hzY, haz⟩ := habove (a : ℝ)
    exact ⟨⟨z, hzY⟩, haz⟩⟩
  have : NoMinOrder α := ⟨fun a => by
    obtain ⟨z, hzY, hza⟩ := hbelow (a : ℝ)
    exact ⟨⟨z, hzY⟩, hza⟩⟩
  let : SuccOrder α := LinearLocallyFiniteOrder.succOrder α
  let : PredOrder α := LinearLocallyFiniteOrder.predOrder α
  let e : α ≃o ℤ := orderIsoIntOfLinearSuccPredArch
  refine ⟨fun n => (e.symm n : ℝ), ?_, ?_⟩
  · apply Set.eq_of_subset_of_subset
    · rintro x ⟨n, rfl⟩
      exact (e.symm n).2
    · intro x hx
      let a : α := ⟨x, hx⟩
      exact ⟨e a, by simp [a, e]⟩
  · intro a b hab
    exact_mod_cast e.symm.strictMono hab

-- Reuse canonical intrinsic frontier provenance from PolygonalCarrier.
private theorem ep_frontier_level_has_translatedVertex
    (K : PolygonalRegion) (S : Set Plane)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (π : Plane →ₗ[ℝ] ℝ) (a e : Plane) (he : e ≠ 0) (hπe : π e = 0)
    (hline : {y | π y = π a} ⊆ frontier (regularSupport K S)) :
    ∃ v ∈ vertexSet K.support, ∃ s ∈ S, π (v + s) = π a := by
  obtain ⟨_, _, hvertex⟩ :=
    Tiling.Polygonal.frontierLevel_has_bounded_intrinsicVertex K S hp π e he hπe
  obtain ⟨v, s, hv, hs, hlevel, _⟩ := hvertex a hline
  exact ⟨v, hv, s, hs, hlevel⟩

private theorem invariantAlong_frontier (D : Set Plane) (δ : Submodule ℝ Plane)
    (hD : IsInvariantAlong D δ) : IsInvariantAlong (frontier D) δ := by
  intro u hu
  have h := (Homeomorph.addLeft u).image_frontier D
  change u +ᵥ frontier D = frontier (u +ᵥ D) at h
  rwa [hD u hu] at h

private theorem invariant_carrier_boundaryLevels_subset_translatedVertices
    (K : PolygonalRegion) (S : Set Plane) (δ : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (π : Plane →ₗ[ℝ] ℝ) (hker : LinearMap.ker π = δ)
    (hD : IsInvariantAlong (regularSupport K S) δ) :
    π '' frontier (regularSupport K S) ⊆ π '' translatedVertices K S := by
  have : Nontrivial δ := Module.nontrivial_of_finrank_eq_succ hδ
  obtain ⟨e, he⟩ := exists_ne (0 : δ)
  have he' : (e : Plane) ≠ 0 := by
    intro h
    exact he (Subtype.ext h)
  have hπe : π (e : Plane) = 0 := LinearMap.mem_ker.mp (hker.symm ▸ e.property)
  have hfront := invariantAlong_frontier (regularSupport K S) δ hD
  rintro r ⟨x, hx, hxr⟩
  have hline : {y | π y = π x} ⊆ frontier (regularSupport K S) := by
    intro y hy
    have hdiff : y - x ∈ δ := by
      rw [← hker, LinearMap.mem_ker, map_sub, hy, sub_self]
    rw [← hfront (y - x) hdiff]
    exact ⟨x, hx, by simp [vadd_eq_add]⟩
  obtain ⟨v, hv, s, hs, hvs⟩ :=
    ep_frontier_level_has_translatedVertex K S hp π x e he' hπe hline
  exact ⟨v + s, ⟨v, hv, s, hs, rfl⟩, hvs.trans hxr⟩

private theorem invariantAlong_regularize (D : Set Plane) (δ : Submodule ℝ Plane)
    (hD : IsInvariantAlong D δ) : IsInvariantAlong (interior (closure D)) δ := by
  intro u hu
  rw [← interior_vadd, ← closure_vadd, hD u hu]

private theorem invariantAlong_iUnion {ι : Type*} (D : ι → Set Plane)
    (δ : Submodule ℝ Plane) (hD : ∀ i, IsInvariantAlong (D i) δ) :
    IsInvariantAlong (⋃ i, D i) δ := by
  intro u hu
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [← hD i u hu]
    exact ⟨y, hyi, rfl⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [← hD i u hu] at hxi
    obtain ⟨y, hy, rfl⟩ := hxi
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, rfl⟩

private theorem periodGroup_map_eq_of_isInvariantAlong
    (D : Set Plane) (δ : Submodule ℝ Plane)
    (π : Plane →ₗ[ℝ] ℝ) (hker : LinearMap.ker π = δ)
    (hD : IsInvariantAlong D δ) (v : Plane) :
    v ∈ periodGroup D ↔ π v ∈ periodGroup (π '' D) := by
  have htranslateInvariant (u : Plane) : IsInvariantAlong (u +ᵥ D) δ := by
    intro w hw
    calc
      w +ᵥ (u +ᵥ D) = u +ᵥ (w +ᵥ D) := by
        ext p
        simp [Set.mem_vadd_set, vadd_eq_add, add_left_comm]
      _ = u +ᵥ D := by rw [hD w hw]
  have himage (u : Plane) : π '' (u +ᵥ D) = π u +ᵥ (π '' D) := by
    ext z
    simp [Set.mem_vadd_set, vadd_eq_add, map_add]
  change v ∈ AddAction.stabilizer Plane D ↔ π v ∈ AddAction.stabilizer ℝ (π '' D)
  simp only [AddAction.mem_stabilizer_iff]
  constructor
  · intro hv
    rw [← himage v, hv]
  · intro hv
    have hpre : π ⁻¹' (π '' (v +ᵥ D)) = π ⁻¹' (π '' D) := by
      rw [himage v, hv]
    rw [invariantAlong_projection_preimage (v +ᵥ D) δ π hker (htranslateInvariant v),
      invariantAlong_projection_preimage D δ π hker hD] at hpre
    exact hpre

private theorem component_centres_subset {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (P : EarthquakeComponent K δ T) : P.centres ⊆ T := by
  rintro x ⟨s, _hs, rfl⟩
  exact s.property

private theorem packing_subfamily {K : PolygonalRegion} {T S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements T)) (hST : S ⊆ T) :
    IsPacking K.prototileFamily (K.placements S) := by
  apply (isPacking_iff_openCarrier_disjoint K S).mpr
  exact ((isPacking_iff_openCarrier_disjoint K T).mp hp).mono hST

private theorem wholePlane_components_invariant
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ) :
    (∀ P : EarthquakeComponent K δ T, IsInvariantAlong P.carrier δ) ∧
      IsInvariantAlong (regularSupport K (columnPart K δ T)) δ := by
  have hsupport : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hinv : IsInvariantAlong (regularSupport K T) δ := by
    rw [hsupport]
    intro u _hu
    simp
  have hcomp := component_isInvariant K δ T hδ htile.2.1 hinv
  refine ⟨hcomp, ?_⟩
  rw [columnPart, regularSupport_iUnion]
  apply invariantAlong_regularize
  apply invariantAlong_iUnion
  intro P
  exact hcomp P.1

private def colouredCentres (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane) :
    Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T} → Set Plane
  | none => columnPart K δ T
  | some P => P.1.centres

private def colouredCarrier (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) : Set Plane :=
  regularSupport K (colouredCentres K δ T c)

private theorem colouredCentres_subset (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane)
    (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
    colouredCentres K δ T c ⊆ T := by
  rcases c with _ | P
  · intro x hx
    obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
    exact component_centres_subset P.1 hxP
  · exact component_centres_subset P.1

private theorem colouredCarrier_invariant (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
    IsInvariantAlong (colouredCarrier K δ T c) δ := by
  have hinv := wholePlane_components_invariant K δ T hδ htile
  rcases c with _ | P
  · exact hinv.2
  · exact hinv.1 P.1

private def boundaryLevels (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (π : Plane →ₗ[ℝ] ℝ) : Set ℝ :=
    ⋃ c, π '' frontier (colouredCarrier K δ T c)

private def componentColourEquiv
    {K K' : PolygonalRegion} {δ : Submodule ℝ Plane} {T T' : Set Plane}
    (e : EarthquakeComponent K δ T ≃ EarthquakeComponent K' δ T')
    (hcol : ∀ P : EarthquakeComponent K δ T,
      IsCenterColumn K δ P.centres ↔ IsCenterColumn K' δ (e P).centres) :
    Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T} ≃
      Option {P : EarthquakeComponent K' δ T' // P ∈ noncolumnComponents K' δ T'} :=
  Equiv.optionCongr (e.subtypeEquiv fun P => not_congr (hcol P))

private theorem componentColourEquiv_centres
    {K K' : PolygonalRegion} {δ : Submodule ℝ Plane} {T T' : Set Plane}
    (e : EarthquakeComponent K δ T ≃ EarthquakeComponent K' δ T')
    (hcol : ∀ P : EarthquakeComponent K δ T,
      IsCenterColumn K δ P.centres ↔ IsCenterColumn K' δ (e P).centres)
    (d : Plane → Plane)
    (hcentres : ∀ P : EarthquakeComponent K δ T, (e P).centres = d '' P.centres)
    (hcolumn : columnPart K' δ T' = d '' columnPart K δ T)
    (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
    colouredCentres K' δ T' (componentColourEquiv e hcol c) = d '' colouredCentres K δ T c := by
  cases c with
  | none => exact hcolumn
  | some c => exact hcentres c.1

private theorem boundaryLevels_subset_translatedVertices
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (π : Plane →ₗ[ℝ] ℝ) (hker : LinearMap.ker π = δ) :
    boundaryLevels K δ T π ⊆ π '' translatedVertices K T := by
  have hinv := wholePlane_components_invariant K δ T hδ htile
  have hcolT : columnPart K δ T ⊆ T := by
    intro x hx
    obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
    exact component_centres_subset P.1 hxP
  rintro r hr
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hr
  rcases c with _ | P
  · obtain ⟨v, hv, hvr⟩ :=
      invariant_carrier_boundaryLevels_subset_translatedVertices
        K (columnPart K δ T) δ hδ (packing_subfamily htile.2.1 hcolT) π hker hinv.2 hc
    refine ⟨v, ?_, hvr⟩
    exact Set.add_subset_add_left hcolT hv
  · obtain ⟨v, hv, hvr⟩ :=
      invariant_carrier_boundaryLevels_subset_translatedVertices
        K P.1.centres δ hδ (packing_subfamily htile.2.1 (component_centres_subset P.1))
        π hker (hinv.1 P.1) hc
    refine ⟨v, ?_, hvr⟩
    exact Set.add_subset_add_left (component_centres_subset P.1) hv

private theorem boundaryLevels_locallyFinite
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (hflc : HasTransverseFLC K δ T) (π : Plane →L[ℝ] ℝ)
    (hπ : Function.Surjective π) (hker : LinearMap.ker π.toLinearMap = δ) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (boundaryLevels K δ T π.toLinearMap ∩ Q).Finite := by
  intro Q hQ
  apply (transverse_projection_locallyFinite K δ T hflc π hπ hker Q hQ).subset
  exact Set.inter_subset_inter_left Q (boundaryLevels_subset_translatedVertices K δ T hδ htile
    π.toLinearMap hker)

private theorem invariant_subfamily_frontier_isProperLink
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T S : Set Plane)
    (htile : TilesOn K T Set.univ) (hST : S ⊆ T)
    (hD : IsInvariantAlong (regularSupport K S) δ)
    {a : Plane} (ha : a ∈ frontier (regularSupport K S)) : IsProperLink K δ T a := by
  have hp := packing_subfamily htile.2.1 hST
  have hfront := invariantAlong_frontier (regularSupport K S) δ hD
  rintro y ⟨u, hu, rfl⟩
  have hy : a + u ∈ frontier (regularSupport K S) := by
    rw [← hfront u hu]
    exact ⟨a, ha, by simp [vadd_eq_add, add_comm]⟩
  obtain ⟨s, hs, hsb⟩ :=
    Tiling.Polygonal.exists_tile_frontier_of_mem_frontier_regularSupport K hp hy
  apply Set.mem_iUnion.mpr
  refine ⟨⟨s, hST hs⟩, (a + u) - s, hsb, ?_⟩
  simp [vadd_eq_add]

private theorem boundaryLevel_has_vertexLink
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (π : Plane →ₗ[ℝ] ℝ) (hker : LinearMap.ker π = δ)
    {r : ℝ} (hr : r ∈ boundaryLevels K δ T π) :
    ∃ v ∈ translatedVertices K T, π v = r ∧ IsProperLink K δ T v := by
  obtain ⟨c, x, hx, hxr⟩ := Set.mem_iUnion.mp hr
  have hST := colouredCentres_subset K δ T c
  have hD := colouredCarrier_invariant K δ T hδ htile c
  obtain ⟨v, hv, hvr⟩ := invariant_carrier_boundaryLevels_subset_translatedVertices
    K (colouredCentres K δ T c) δ hδ (packing_subfamily htile.2.1 hST) π hker hD ⟨x, hx, rfl⟩
  have hdiff : v - x ∈ δ := by
    rw [← hker, LinearMap.mem_ker, map_sub, hvr, sub_self]
  have hvfront : v ∈ frontier (colouredCarrier K δ T c) := by
    rw [← invariantAlong_frontier _ δ hD (v - x) hdiff]
    exact ⟨x, hx, by simp [vadd_eq_add]⟩
  refine ⟨v, Set.add_subset_add_left hST hv, hvr.trans hxr, ?_⟩
  exact invariant_subfamily_frontier_isProperLink K δ T (colouredCentres K δ T c)
    htile hST hD hvfront

private def normalProjection (n : Tiling.Approximation.RationalNormal) : Plane →L[ℝ] ℝ :=
  (n.x : ℝ) • Complex.reCLM + (n.y : ℝ) • Complex.imCLM

private theorem normalProjection_apply (n : Tiling.Approximation.RationalNormal) (x : Plane) :
    normalProjection n x = Tiling.Approximation.normalEval n x := rfl

private theorem normalProjection_surjective (n : Tiling.Approximation.RationalNormal) :
    Function.Surjective (normalProjection n) := by
  intro r
  rcases n.nonzero with hx | hy
  · have hx' : (n.x : ℝ) ≠ 0 := by exact_mod_cast hx
    refine ⟨Complex.mk (r / (n.x : ℝ)) 0, ?_⟩
    simp [normalProjection]
    field_simp
  · have hy' : (n.y : ℝ) ≠ 0 := by exact_mod_cast hy
    refine ⟨Complex.mk 0 (r / (n.y : ℝ)), ?_⟩
    simp [normalProjection]
    field_simp

private theorem normalProjection_deformed_sub
    (φ : ℝ →ₗ[ℚ] ℚ) (n : Tiling.Approximation.RationalNormal) (a b : Plane) :
    Tiling.Approximation.normalEval n (Tiling.Approximation.deformPoint φ (a - b)) =
      (φ (normalProjection n a) : ℝ) - (φ (normalProjection n b) : ℝ) := by
  rw [Tiling.Approximation.rationalNormal_commutes]
  change (φ (normalProjection n (a - b)) : ℝ) = _
  rw [map_sub, map_sub, Rat.cast_sub]

private theorem component_carrier_nonempty {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (P : EarthquakeComponent K δ T) : P.carrier.Nonempty := by
  obtain ⟨t, ht⟩ := P.nonempty_supp
  obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hop : IsOpen (openUnion K P.centres) := by
    apply isOpen_iUnion
    intro s
    exact (Homeomorph.addLeft (s : Plane)).isOpenMap _ isOpen_interior
  refine ⟨(t : Plane) + x, ?_⟩
  apply interior_maximal subset_closure hop
  apply Set.mem_iUnion.mpr
  refine ⟨⟨t, ⟨t, ht, rfl⟩⟩, x, hx, rfl⟩

private theorem component_carrier_proper_of_distinct
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (P Q : EarthquakeComponent K δ T) (hPQ : P ≠ Q) : P.carrier ≠ Set.univ := by
  intro hPfull
  obtain ⟨x, hx⟩ := component_carrier_nonempty Q
  have hd := components_carriers_disjoint K δ T hδ htile.2.1
    (Set.mem_univ P) (Set.mem_univ Q) hPQ
  exact Set.disjoint_left.mp hd (by
    change x ∈ P.carrier
    rw [hPfull]
    exact Set.mem_univ x) hx

private theorem boundaryLevels_nonempty_of_noncolumn
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (hnontrivial : ∃ P Q : EarthquakeComponent K δ T, P ≠ Q)
    (P : EarthquakeComponent K δ T) (hP : P ∈ noncolumnComponents K δ T)
    (π : Plane →ₗ[ℝ] ℝ) : (boundaryLevels K δ T π).Nonempty := by
  obtain ⟨Q, R, hQR⟩ := hnontrivial
  have hex : ∃ Q : EarthquakeComponent K δ T, P ≠ Q := by
    by_cases hPQ : P = Q
    · exact ⟨R, hPQ ▸ hQR⟩
    · exact ⟨Q, hPQ⟩
  obtain ⟨Q, hPQ⟩ := hex
  have hfront := nonempty_frontier_iff.mpr ⟨component_carrier_nonempty P,
    component_carrier_proper_of_distinct hδ htile P Q hPQ⟩
  obtain ⟨x, hx⟩ := hfront
  exact ⟨π x, Set.mem_iUnion.mpr ⟨some ⟨P, hP⟩, x, hx, rfl⟩⟩

private theorem invariant_regularize_projection
    (U : Set Plane) (hU : IsOpen U) (δ : Submodule ℝ Plane)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hC : IsInvariantAlong (interior (closure U)) δ) :
    π '' interior (closure U) = interior (closure (π '' U)) := by
  have hopen : IsOpenMap π := π.toLinearMap.isOpenMap_of_finiteDimensional hπ
  have hpre := invariantAlong_projection_preimage (interior (closure U)) δ
    π.toLinearMap hker hC
  have hUC : U ⊆ interior (closure U) := interior_maximal subset_closure hU
  have hsat : π ⁻¹' (π '' U) ⊆ interior (closure U) := by
    rw [← hpre]
    exact Set.preimage_mono (Set.image_mono hUC)
  have hclosures : closure (π ⁻¹' (π '' U)) = closure U := by
    apply Set.Subset.antisymm
    · exact closure_minimal (hsat.trans interior_subset) isClosed_closure
    · exact closure_mono (Set.subset_preimage_image _ _)
  have heq : π ⁻¹' interior (closure (π '' U)) = interior (closure U) := by
    rw [hopen.preimage_interior_eq_interior_preimage π.continuous,
      hopen.preimage_closure_eq_closure_preimage π.continuous, hclosures]
  rw [← heq, Set.image_preimage_eq _ hπ]

private theorem invariant_frontier_projection
    (D : Set Plane) (δ : Submodule ℝ Plane) (π : Plane →L[ℝ] ℝ)
    (hπ : Function.Surjective π) (hker : LinearMap.ker π.toLinearMap = δ)
    (hD : IsInvariantAlong D δ) : π '' frontier D = frontier (π '' D) := by
  have hopen : IsOpenMap π := π.toLinearMap.isOpenMap_of_finiteDimensional hπ
  have hpre := invariantAlong_projection_preimage D δ π.toLinearMap hker hD
  change π ⁻¹' (π '' D) = D at hpre
  have heq : π ⁻¹' frontier (π '' D) = frontier D := by
    rw [hopen.preimage_frontier_eq_frontier_preimage π.continuous, hpre]
  rw [← heq, Set.image_preimage_eq _ hπ]

private theorem openUnion_projection_intervals
    (K : PolygonalRegion) (S : Set Plane) (π : Plane →ₗ[ℝ] ℝ)
    (I : Finset (ℝ × ℝ))
    (hI : π '' K.openCarrier = ⋃ e ∈ I, Set.Ioo e.1 e.2) :
    π '' openUnion K S = ⋃ s : S, ⋃ e ∈ I,
      Set.Ioo (π s + e.1) (π s + e.2) := by
  have htranslate (s : Plane) : π '' (s +ᵥ K.openCarrier) =
      (fun r : ℝ => π s + r) '' (π '' K.openCarrier) := by
    ext r
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨π x, ⟨x, hx, rfl⟩, (map_add π s x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨s + x, ⟨x, hx, rfl⟩, map_add π s x⟩
  simp only [openUnion, Set.image_iUnion, htranslate, hI, Set.image_const_add_Ioo]

private theorem invariant_carrier_projection_intervals
    (K : PolygonalRegion) (S : Set Plane) (δ : Submodule ℝ Plane)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hD : IsInvariantAlong (regularSupport K S) δ)
    (I : Finset (ℝ × ℝ))
    (hI : π '' K.openCarrier = ⋃ e ∈ I, Set.Ioo e.1 e.2) :
    π '' regularSupport K S = interior (closure (⋃ s : S, ⋃ e ∈ I,
      Set.Ioo (π s + e.1) (π s + e.2))) := by
  have hU : IsOpen (openUnion K S) := isOpen_iUnion fun s =>
    (Homeomorph.addLeft (s : Plane)).isOpenMap _ isOpen_interior
  rw [regularSupport, invariant_regularize_projection (openUnion K S) hU δ π hπ hker hD]
  have hprojection := openUnion_projection_intervals K S π.toLinearMap I hI
  change π '' openUnion K S = _ at hprojection
  rw [hprojection]
  rfl

private theorem deformed_openUnion_projection_intervals
    (Kφ : PolygonalRegion) (S : Set Plane) (n : Tiling.Approximation.RationalNormal)
    (φ : ℝ →ₗ[ℚ] ℚ) (I : Finset (ℝ × ℝ))
    (hIφ : Tiling.Approximation.normalEval n '' Kφ.openCarrier =
      ⋃ e ∈ I, Set.Ioo (φ e.1 : ℝ) (φ e.2 : ℝ)) :
    normalProjection n '' openUnion Kφ (Tiling.Approximation.deformPoint φ '' S) =
      ⋃ s : S, ⋃ e ∈ I,
        Set.Ioo (φ (normalProjection n s + e.1) : ℝ)
          (φ (normalProjection n s + e.2) : ℝ) := by
  let J : Finset (ℝ × ℝ) := I.image (fun e => ((φ e.1 : ℝ), (φ e.2 : ℝ)))
  have hJ : normalProjection n '' Kφ.openCarrier = ⋃ e ∈ J, Set.Ioo e.1 e.2 := by
    change Tiling.Approximation.normalEval n '' Kφ.openCarrier = _
    rw [hIφ]
    ext x
    simp only [Set.mem_iUnion, J, Finset.mem_image]
    constructor
    · rintro ⟨e, he, hx⟩
      exact ⟨_, ⟨e, he, rfl⟩, hx⟩
    · rintro ⟨_, ⟨e, he, rfl⟩, hx⟩
      exact ⟨e, he, hx⟩
  have hprojection := openUnion_projection_intervals Kφ
    (Tiling.Approximation.deformPoint φ '' S) (normalProjection n).toLinearMap J hJ
  change normalProjection n '' openUnion Kφ (Tiling.Approximation.deformPoint φ '' S) = _
    at hprojection
  rw [hprojection]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨s, e, he, hx⟩
    obtain ⟨t, ht, hts⟩ := s.property
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    refine ⟨⟨t, ht⟩, q, hq, ?_⟩
    have hπs : normalProjection n s = (φ (normalProjection n t) : ℝ) := by
      rw [← hts]
      exact Tiling.Approximation.rationalNormal_commutes φ n t
    change (normalProjection n).toLinearMap s = (φ (normalProjection n t) : ℝ) at hπs
    change _ < x ∧ x < _ at hx ⊢
    simpa only [hπs, map_add, Rat.cast_add] using hx
  · rintro ⟨s, e, he, hx⟩
    let t : Tiling.Approximation.deformPoint φ '' S :=
      ⟨Tiling.Approximation.deformPoint φ s, ⟨s, s.property, rfl⟩⟩
    refine ⟨t, _, Finset.mem_image.mpr ⟨e, he, rfl⟩, ?_⟩
    have hπt : normalProjection n t = (φ (normalProjection n s) : ℝ) :=
      Tiling.Approximation.rationalNormal_commutes φ n s
    change (normalProjection n).toLinearMap t = (φ (normalProjection n s) : ℝ) at hπt
    change _ < x ∧ x < _ at hx ⊢
    simpa only [hπt, map_add, Rat.cast_add] using hx

private theorem commonCarrierPeriod_boundaryLevels_period
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (π : Plane →ₗ[ℝ] ℝ) (v : Plane) (hv : IsCommonCarrierPeriod K δ T v) :
    π v ∈ periodGroup (boundaryLevels K δ T π) := by
  have hc (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      v ∈ periodGroup (colouredCarrier K δ T c) := by
    cases c with
    | none => exact hv.2.1
    | some c => exact hv.2.2 c.1 c.2
  have hf (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      v +ᵥ frontier (colouredCarrier K δ T c) = frontier (colouredCarrier K δ T c) := by
    have h := (Homeomorph.addLeft v).image_frontier (colouredCarrier K δ T c)
    change v +ᵥ frontier (colouredCarrier K δ T c) =
      frontier (v +ᵥ colouredCarrier K δ T c) at h
    have hc' := hc c
    change v ∈ AddAction.stabilizer Plane (colouredCarrier K δ T c) at hc'
    rw [AddAction.mem_stabilizer_iff] at hc'
    rwa [hc'] at h
  change π v ∈ AddAction.stabilizer ℝ (boundaryLevels K δ T π)
  rw [AddAction.mem_stabilizer_iff]
  have hi (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      π v +ᵥ (π '' frontier (colouredCarrier K δ T c)) =
        π '' frontier (colouredCarrier K δ T c) := by
    calc
      π v +ᵥ (π '' frontier (colouredCarrier K δ T c)) =
          π '' (v +ᵥ frontier (colouredCarrier K δ T c)) := by
        ext r
        simp [Set.mem_vadd_set, vadd_eq_add, map_add]
      _ = π '' frontier (colouredCarrier K δ T c) := by rw [hf c]
  change π v +ᵥ (⋃ c, π '' frontier (colouredCarrier K δ T c)) = _
  calc
    π v +ᵥ (⋃ c, π '' frontier (colouredCarrier K δ T c)) =
        ⋃ c, π v +ᵥ (π '' frontier (colouredCarrier K δ T c)) := by
      ext r
      simp [Set.mem_vadd_set]
    _ = ⋃ c, π '' frontier (colouredCarrier K δ T c) := by simp_rw [hi]

private theorem exists_relative_dense_radius_of_period
    (B : Set ℝ) (hB : B.Nonempty) (β : ℝ) (hβ : β ≠ 0)
    (hperiod : β ∈ periodGroup B) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, ∃ b ∈ B, |r - b| < ρ := by
  obtain ⟨a, ha⟩ := hB
  let ρ : ℝ := |β|
  have hρ : 0 < ρ := abs_pos.mpr hβ
  have hρperiod : ρ ∈ periodGroup B := by
    by_cases hβnonneg : 0 ≤ β
    · simpa [ρ, abs_of_nonneg hβnonneg] using hperiod
    · simpa [ρ, abs_of_neg (lt_of_not_ge hβnonneg)] using (periodGroup B).neg_mem hperiod
  refine ⟨ρ, hρ, ?_⟩
  intro r
  let n : ℤ := ⌊(r - a) / ρ⌋
  let b : ℝ := a + (n : ℝ) * ρ
  have hnlow : (n : ℝ) ≤ (r - a) / ρ := Int.floor_le _
  have hnhigh : (r - a) / ρ < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hnρ : (n : ℝ) * ρ ≤ r - a := (le_div_iff₀ hρ).mp hnlow
  have hrρ : r - a < ((n : ℝ) + 1) * ρ := (div_lt_iff₀ hρ).mp hnhigh
  have hnperiod : (n : ℝ) * ρ ∈ periodGroup B := by
    simpa only [zsmul_eq_mul] using (periodGroup B).zsmul_mem hρperiod n
  have hb : b ∈ B := by
    have hshift : (n : ℝ) * ρ +ᵥ B = B := by
      change (n : ℝ) * ρ ∈ AddAction.stabilizer ℝ B at hnperiod
      exact AddAction.mem_stabilizer_iff.mp hnperiod
    rw [← hshift]
    exact ⟨a, ha, by simp only [vadd_eq_add]; dsimp [b]; ring⟩
  refine ⟨b, hb, abs_lt.mpr ?_⟩
  constructor <;> dsimp [b] <;> nlinarith

private theorem finite_bounded_windows_isClosed (A : Set ℝ)
    (hA : ∀ Q : Set ℝ, Bornology.IsBounded Q → (A ∩ Q).Finite) : IsClosed A := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hfin := hA (Metric.closedBall x 1) Metric.isBounded_closedBall
  have havoid : (A ∩ Metric.closedBall x 1)ᶜ ∈ 𝓝 x :=
    hfin.isClosed.isOpen_compl.mem_nhds (fun h => hx h.1)
  filter_upwards [havoid, Metric.ball_mem_nhds x zero_lt_one] with y hy hyball
  intro hyA
  exact hy ⟨hyA, Metric.ball_subset_closedBall hyball⟩

private theorem coercive_image_finite_bounded_windows
    (A : Set ℝ) (f : ℝ → ℝ) (a : ℝ)
    (hA : ∀ Q : Set ℝ, Bornology.IsBounded Q → (A ∩ Q).Finite)
    (hcoercive : ∀ x ∈ A, |x - a| / 2 ≤ |f x - f a|) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q → ((f '' A) ∩ Q).Finite := by
  intro Q hQ
  obtain ⟨C, hC⟩ := hQ.exists_norm_le
  let R := 2 * (C + |f a|)
  have hfin := hA (Set.Icc (a - R) (a + R)) isCompact_Icc.isBounded
  apply (hfin.image f).subset
  rintro _ ⟨⟨x, hx, rfl⟩, hfx⟩
  refine ⟨x, ⟨hx, ?_⟩, rfl⟩
  have hnorm : |f x| ≤ C := by simpa only [Real.norm_eq_abs] using hC _ hfx
  have htriangle : |f x - f a| ≤ |f x| + |f a| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (f x) (f a)
  have hd : |x - a| ≤ R := by dsimp [R]; linarith [hcoercive x hx]
  have hh := abs_le.mp hd
  constructor <;> linarith

private theorem regularized_interval_endpoints_unbounded
    {ι : Type*} (a b : ι → ℝ) (A : Set ℝ)
    (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ A)
    (hfull : interior (closure (⋃ i, Set.Ioo (a i) (b i))) = Set.univ) :
    (∀ r : ℝ, ∃ x ∈ A, r < x) ∧ (∀ r : ℝ, ∃ x ∈ A, x < r) := by
  constructor
  · intro r
    by_contra h
    push Not at h
    have hsub : (⋃ i, Set.Ioo (a i) (b i)) ⊆ Set.Iic r := by
      rintro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hi.2.le.trans (h _ (hb i))
    have hreg := interior_subset.trans (closure_minimal hsub isClosed_Iic)
    rw [hfull] at hreg
    have hh := hreg (Set.mem_univ (r + 1))
    change r + 1 ≤ r at hh
    linarith
  · intro r
    by_contra h
    push Not at h
    have hsub : (⋃ i, Set.Ioo (a i) (b i)) ⊆ Set.Ici r := by
      rintro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact (h _ (ha i)).trans hi.1.le
    have hreg := interior_subset.trans (closure_minimal hsub isClosed_Ici)
    rw [hfull] at hreg
    have hh := hreg (Set.mem_univ (r - 1))
    change r ≤ r - 1 at hh
    linarith

private theorem translatedVertices_projection_unbounded
    (K : PolygonalRegion) (T : Set Plane) (htile : TilesOn K T Set.univ)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π) (I : Finset (ℝ × ℝ))
    (hI : π '' K.openCarrier = ⋃ e ∈ I, Set.Ioo e.1 e.2)
    (hvertices : ∀ e ∈ I,
      (∃ v ∈ vertexSet K.support, π v = e.1) ∧
      (∃ v ∈ vertexSet K.support, π v = e.2)) :
    (∀ r : ℝ, ∃ x ∈ π '' translatedVertices K T, r < x) ∧
      (∀ r : ℝ, ∃ x ∈ π '' translatedVertices K T, x < r) := by
  let δ := LinearMap.ker π.toLinearMap
  have hfull : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hinv : IsInvariantAlong (regularSupport K T) δ := by
    rw [hfull]
    intro u _
    simp
  have hproj := invariant_carrier_projection_intervals K T δ π hπ rfl hinv I hI
  rw [hfull, Set.image_univ_of_surjective hπ] at hproj
  let J := T × {e : ℝ × ℝ // e ∈ I}
  let a : J → ℝ := fun j => π j.1 + j.2.1.1
  let b : J → ℝ := fun j => π j.1 + j.2.1.2
  have hindexed : (⋃ j : J, Set.Ioo (a j) (b j)) =
      ⋃ s : T, ⋃ e ∈ I, Set.Ioo (π s + e.1) (π s + e.2) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨s, e⟩, hx⟩
      exact ⟨s, e, e.property, hx⟩
    · rintro ⟨s, e, he, hx⟩
      exact ⟨⟨s, ⟨e, he⟩⟩, hx⟩
  have hA (j : J) : a j ∈ π '' translatedVertices K T := by
    obtain ⟨v, hv, he⟩ := (hvertices j.2.1 j.2.2).1
    refine ⟨v + j.1, ⟨v, hv, j.1, j.1.property, rfl⟩, ?_⟩
    dsimp [a]
    rw [map_add, he, add_comm]
  have hB (j : J) : b j ∈ π '' translatedVertices K T := by
    obtain ⟨v, hv, he⟩ := (hvertices j.2.1 j.2.2).2
    refine ⟨v + j.1, ⟨v, hv, j.1, j.1.property, rfl⟩, ?_⟩
    dsimp [b]
    rw [map_add, he, add_comm]
  apply regularized_interval_endpoints_unbounded a b (π '' translatedVertices K T) hA hB
  rw [hindexed]
  exact hproj.symm

private theorem finite_windows_no_endpoints_unbounded
    (B : Set ℝ) (hB : B.Nonempty)
    (hfinite : ∀ a b : ℝ, (B ∩ Set.Icc a b).Finite)
    (hmax : ∀ b ∈ B, ∃ c ∈ B, b < c)
    (hmin : ∀ b ∈ B, ∃ c ∈ B, c < b) :
    (∀ r : ℝ, ∃ b ∈ B, r < b) ∧ (∀ r : ℝ, ∃ b ∈ B, b < r) := by
  obtain ⟨b₀, hb₀⟩ := hB
  constructor
  · intro r
    by_contra h
    push Not at h
    have hb₀r := h b₀ hb₀
    obtain ⟨b, hb, hgreatest⟩ := Set.exists_max_image (B ∩ Set.Icc b₀ r) id
      (hfinite b₀ r) ⟨b₀, hb₀, le_rfl, hb₀r⟩
    obtain ⟨c, hc, hbc⟩ := hmax b hb.1
    have hcb := hgreatest c ⟨hc, hb.2.1.trans hbc.le, h c hc⟩
    exact (not_lt_of_ge hcb) hbc
  · intro r
    by_contra h
    push Not at h
    have hrb₀ := h b₀ hb₀
    obtain ⟨b, hb, hleast⟩ := Set.exists_min_image (B ∩ Set.Icc r b₀) id
      (hfinite r b₀) ⟨b₀, hb₀, hrb₀, le_rfl⟩
    obtain ⟨c, hc, hcb⟩ := hmin b hb.1
    have hbc := hleast c ⟨hc, h c hc, hcb.le.trans hb.2.2⟩
    exact (not_lt_of_ge hbc) hcb

private theorem iUnion_finset_reindex {ι α : Type*} (I : Finset α)
    (U : ι → α → Set ℝ) :
    (⋃ p : ι × {e : α // e ∈ I}, U p.1 p.2.1) = ⋃ i, ⋃ e ∈ I, U i e := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, e⟩, hx⟩
    exact ⟨i, e.1, e.2, hx⟩
  · rintro ⟨i, e, he, hx⟩
    exact ⟨⟨i, ⟨e, he⟩⟩, hx⟩

private theorem normal_interval_endpoints_mem_translatedVertices
    (K : PolygonalRegion) (T : Set Plane) (π : Plane →ₗ[ℝ] ℝ)
    (I : Finset (ℝ × ℝ))
    (hvertices : ∀ e ∈ I,
      (∃ v ∈ vertexSet K.support, π v = e.1) ∧
      (∃ v ∈ vertexSet K.support, π v = e.2))
    {s : Plane} (hs : s ∈ T) {e : ℝ × ℝ} (he : e ∈ I) :
    (π s + e.1 ∈ π '' translatedVertices K T) ∧
      (π s + e.2 ∈ π '' translatedVertices K T) := by
  constructor
  · obtain ⟨v, hv, heval⟩ := (hvertices e he).1
    refine ⟨v + s, ⟨v, hv, s, hs, rfl⟩, ?_⟩
    rw [map_add, heval, add_comm]
  · obtain ⟨v, hv, heval⟩ := (hvertices e he).2
    refine ⟨v + s, ⟨v, hv, s, hs, rfl⟩, ?_⟩
    rw [map_add, heval, add_comm]

private theorem mem_iff_of_no_frontier_on_interval
    (D : Set ℝ) (hD : IsOpen D) (x y : ℝ) (hxy : x ≤ y)
    (hno : Set.Icc x y ∩ frontier D = ∅) : x ∈ D ↔ y ∈ D := by
  have hinterval : IsPreconnected (Set.Icc x y) := isPreconnected_Icc
  have hdisjoint : Disjoint D (closure D)ᶜ := by
    apply disjoint_compl_right.mono_right
    intro z hz hzd
    exact hz (subset_closure hzd)
  have hnoFrontier (z : ℝ) (hz : z ∈ Set.Icc x y) : z ∉ frontier D := by
    intro hzf
    have hzmem : z ∈ Set.Icc x y ∩ frontier D := ⟨hz, hzf⟩
    rw [hno] at hzmem
    exact hzmem
  have hpartition : Set.Icc x y ⊆ D ∪ (closure D)ᶜ := by
    intro z hz
    by_cases hzd : z ∈ D
    · exact Or.inl hzd
    · right
      have hzfront := hnoFrontier z hz
      have hzcl : z ∉ closure D := by
        intro hzc
        apply hzfront
        rw [hD.frontier_eq]
        exact ⟨hzc, hzd⟩
      exact hzcl
  by_cases hxD : x ∈ D
  · have hIccD : Set.Icc x y ⊆ D :=
      hinterval.subset_left_of_subset_union hD isClosed_closure.isOpen_compl hdisjoint
        hpartition ⟨x, ⟨le_rfl, hxy⟩, hxD⟩
    constructor
    · intro _
      exact hIccD ⟨hxy, le_rfl⟩
    · intro _
      exact hxD
  · have hxcl : x ∈ (closure D)ᶜ := by
      have hxfront := hnoFrontier x ⟨le_rfl, hxy⟩
      by_contra hxc
      apply hxfront
      rw [hD.frontier_eq]
      exact ⟨by simpa using hxc, hxD⟩
    have hIccOutside : Set.Icc x y ⊆ (closure D)ᶜ :=
      hinterval.subset_right_of_subset_union hD isClosed_closure.isOpen_compl hdisjoint
        hpartition ⟨x, ⟨le_rfl, hxy⟩, hxcl⟩
    constructor
    · intro hx
      exact (hxD hx).elim
    · intro hy
      have hycl : y ∈ closure D := subset_closure hy
      exact False.elim ((hIccOutside ⟨hxy, le_rfl⟩) hycl)

private theorem integer_chain_cell_avoids_range (x : ℤ → ℝ) (hx : StrictMono x)
    (i : ℤ) : Disjoint (Set.Ioo (x i) (x (i + 1))) (Set.range x) := by
  rw [Set.disjoint_left]
  rintro _ hh ⟨j, rfl⟩
  have hij : i < j := hx.lt_iff_lt.mp hh.1
  have hji : j < i + 1 := hx.lt_iff_lt.mp hh.2
  omega

private theorem mem_iff_of_same_integer_chain_cell (x : ℤ → ℝ) (hx : StrictMono x)
    (D : Set ℝ) (hD : IsOpen D) (hfront : frontier D ⊆ Set.range x)
    (i : ℤ) {r s : ℝ} (hr : r ∈ Set.Ioo (x i) (x (i + 1)))
    (hs : s ∈ Set.Ioo (x i) (x (i + 1))) : r ∈ D ↔ s ∈ D := by
  have hno {a b : ℝ} (ha : a ∈ Set.Ioo (x i) (x (i + 1)))
      (hb : b ∈ Set.Ioo (x i) (x (i + 1))) : Set.Icc a b ∩ frontier D = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro t ⟨ht, htf⟩
    exact Set.disjoint_left.mp (integer_chain_cell_avoids_range x hx i)
      ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩ (hfront htf)
  by_cases hrs : r ≤ s
  · exact mem_iff_of_no_frontier_on_interval D hD r s hrs (hno hr hs)
  · exact (mem_iff_of_no_frontier_on_interval D hD s r (le_of_not_ge hrs) (hno hs hr)).symm

private theorem outside_integer_chain_range_mem_cell (B : Set ℝ)
    (hfinite : ∀ a b : ℝ, (B ∩ Set.Icc a b).Finite)
    (hbelow : ∀ r : ℝ, ∃ b ∈ B, b < r)
    (x : ℤ → ℝ) (hxB : Set.range x = B) (hx : StrictMono x)
    {r : ℝ} (hr : r ∉ B) : ∃ i : ℤ, r ∈ Set.Ioo (x i) (x (i + 1)) := by
  obtain ⟨b₀, hb₀, hb₀r⟩ := hbelow r
  obtain ⟨b, hb, hgreatest⟩ := Set.exists_max_image (B ∩ Set.Icc b₀ r) id
    (hfinite b₀ r) ⟨b₀, hb₀, le_rfl, hb₀r.le⟩
  have hbRange : b ∈ Set.range x := hxB.symm ▸ hb.1
  obtain ⟨i, rfl⟩ := hbRange
  have hir : x i < r := lt_of_le_of_ne hb.2.2 (fun he => hr (he ▸ hb.1))
  refine ⟨i, hir, ?_⟩
  by_contra h
  have hnB : x (i + 1) ∈ B := hxB ▸ Set.mem_range_self (i + 1)
  have hnext := hx (show i < i + 1 by omega)
  have hh := hgreatest (x (i + 1)) ⟨hnB, hb.2.1.trans hnext.le, le_of_not_gt h⟩
  exact (not_lt_of_ge hh) hnext

private theorem finite_bounded_windows_dense_compl (B : Set ℝ)
    (hfinite : ∀ Q : Set ℝ, Bornology.IsBounded Q → (B ∩ Q).Finite) : Dense Bᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hfin := hfinite (Metric.closedBall x ε) Metric.isBounded_closedBall
  have hsub : Set.Ioo (x - ε) (x + ε) ⊆ B ∩ Metric.closedBall x ε := by
    intro y hy
    have hyball : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      apply abs_lt.mpr
      constructor <;> linarith [hy.1, hy.2]
    exact ⟨interior_subset (hball hyball), Metric.ball_subset_closedBall hyball⟩
  exact Set.Ioo_infinite (show x - ε < x + ε by linarith) (hfin.subset hsub)

private theorem regularopen_eq_of_agree_on_dense
    (U V C : Set ℝ) (hC : Dense C) (hU : IsOpen U) (hV : IsOpen V)
    (hUreg : interior (closure U) = U) (hVreg : interior (closure V) = V)
    (hagree : ∀ r ∈ C, r ∈ U ↔ r ∈ V) : U = V := by
  have hUV : U ⊆ closure V := (hC.open_subset_closure_inter hU).trans
    (closure_mono (fun r hr => (hagree r hr.2).mp hr.1))
  have hVU : V ⊆ closure U := (hC.open_subset_closure_inter hV).trans
    (closure_mono (fun r hr => (hagree r hr.2).mpr hr.1))
  have hcl : closure U = closure V :=
    Set.Subset.antisymm (closure_minimal hUV isClosed_closure)
      (closure_minimal hVU isClosed_closure)
  rw [← hUreg, ← hVreg, hcl]

private theorem relatively_dense_integer_chain_gap_bound
    (x : ℤ → ℝ) (hx : StrictMono x) (ρ : ℝ)
    (hdense : ∀ r : ℝ, ∃ y ∈ Set.range x, |r - y| < ρ) :
    ∀ i : ℤ, x (i + 1) - x i < 2 * ρ := by
  intro i
  obtain ⟨_, ⟨j, rfl⟩, hdist⟩ := hdense (x i + ρ)
  have hlow : x i < x j := by linarith [(abs_lt.mp hdist).2]
  have hij : i < j := hx.lt_iff_lt.mp hlow
  have hnext := hx.monotone (show i + 1 ≤ j by omega)
  have hhigh : x j < x i + 2 * ρ := by linarith [(abs_lt.mp hdist).1]
  linarith

private theorem regularopen_period_of_integer_chain_cell_shift
    (x : ℤ → ℝ) (hx : StrictMono x)
    (hfinite : ∀ Q : Set ℝ, Bornology.IsBounded Q → (Set.range x ∩ Q).Finite)
    (hbelow : ∀ r : ℝ, ∃ j : ℤ, x j < r)
    (D : Set ℝ) (hD : IsOpen D) (hDreg : interior (closure D) = D)
    (k : ℤ) (β : ℝ) (hshift : ∀ i : ℤ, x (i + k) = x i + β)
    (hcell : ∀ i : ℤ, ∀ r ∈ Set.Ioo (x i) (x (i + 1)),
      ∀ s ∈ Set.Ioo (x (i + k)) (x (i + k + 1)), r ∈ D ↔ s ∈ D) :
    β ∈ periodGroup D := by
  have htranslatedOpen : IsOpen (β +ᵥ D) := (Homeomorph.addLeft β).isOpenMap _ hD
  have htranslatedReg : interior (closure (β +ᵥ D)) = β +ᵥ D := by
    rw [closure_vadd, interior_vadd, hDreg]
  have hagree (r : ℝ) (hr : r ∈ (Set.range x)ᶜ) : r ∈ β +ᵥ D ↔ r ∈ D := by
    obtain ⟨i, hi⟩ := outside_integer_chain_range_mem_cell (Set.range x)
      (fun a b => hfinite _ isCompact_Icc.isBounded)
      (fun r => by obtain ⟨j, hj⟩ := hbelow r; exact ⟨x j, Set.mem_range_self j, hj⟩)
      x rfl hx hr
    have hindices : i - k + k = i := by omega
    have hindices' : i - k + 1 + k = i + 1 := by omega
    have hleft := hshift (i - k)
    have hright := hshift (i - k + 1)
    rw [hindices] at hleft
    rw [hindices'] at hright
    have hpre : r - β ∈ Set.Ioo (x (i - k)) (x (i - k + 1)) := by
      constructor <;> linarith [hi.1, hi.2]
    have hmem := hcell (i - k) (r - β) hpre r
      (by simpa only [hindices, add_assoc] using hi)
    constructor
    · rintro ⟨y, hy, hyr⟩
      have hyeq : y = r - β := by change β + y = r at hyr; linarith
      exact hmem.mp (hyeq ▸ hy)
    · intro hrD
      exact ⟨r - β, hmem.mpr hrD, by simp only [vadd_eq_add]; ring⟩
  have heq := regularopen_eq_of_agree_on_dense (β +ᵥ D) D (Set.range x)ᶜ
    (finite_bounded_windows_dense_compl _ hfinite) htranslatedOpen hD htranslatedReg hDreg hagree
  change β ∈ AddAction.stabilizer ℝ D
  exact AddAction.mem_stabilizer_iff.mpr heq

private theorem frontier_interior_closure_union_openIntervals_subset_closedEndpoints
    {ι : Type*} (a b : ι → ℝ) (A : Set ℝ) (hA : IsClosed A)
    (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ A) :
    frontier (interior (closure (⋃ i, Set.Ioo (a i) (b i)))) ⊆ A := by
  let U : Set ℝ := ⋃ i, Set.Ioo (a i) (b i)
  let K : Set ℝ := interior (closure U)
  intro x hxFront
  by_contra hxA
  have hAcompl : IsOpen Aᶜ := hA.isOpen_compl
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp hAcompl x hxA
  let J : Set ℝ := Set.Ioo (x - r) (x + r)
  have hJopen : IsOpen J := isOpen_Ioo
  have hJball : J ⊆ Metric.ball x r := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq]
    apply abs_lt.mpr
    change x - r < y ∧ y < x + r at hy
    rcases hy with ⟨hyl, hyu⟩
    constructor <;> linarith
  have hJavoid : J ⊆ Aᶜ := hJball.trans hrball
  have hendpointSide (c : ℝ) (hcA : c ∈ A) : c ≤ x - r ∨ x + r ≤ c := by
    by_cases hleft : c ≤ x - r
    · exact Or.inl hleft
    · right
      by_contra hright
      have hcJ : c ∈ J := ⟨lt_of_not_ge hleft, lt_of_not_ge hright⟩
      exact (hJavoid hcJ) hcA
  have hleftCmp (c : ℝ) (hcA : c ∈ A) (y : ℝ) (hy : y ∈ J) :
      (c < y ↔ c < x) := by
    change x - r < y ∧ y < x + r at hy
    rcases hy with ⟨hyl, hyu⟩
    rcases hendpointSide c hcA with hleft | hright
    · have hcy : c < y := by linarith
      have hcx : c < x := by linarith [hr]
      exact ⟨fun _ => hcx, fun _ => hcy⟩
    · have hyc : y < c := by linarith
      have hxc : x < c := by linarith [hr]
      constructor <;> intro h <;> linarith
  have hrightCmp (c : ℝ) (hcA : c ∈ A) (y : ℝ) (hy : y ∈ J) :
      (y < c ↔ x < c) := by
    change x - r < y ∧ y < x + r at hy
    rcases hy with ⟨hyl, hyu⟩
    rcases hendpointSide c hcA with hleft | hright
    · have hcy : c < y := by linarith
      have hcx : c < x := by linarith [hr]
      constructor <;> intro h <;> linarith
    · have hyc : y < c := by linarith
      have hxc : x < c := by linarith [hr]
      exact ⟨fun _ => hxc, fun _ => hyc⟩
  have hinterval (i : ι) (y : ℝ) (hy : y ∈ J) :
      y ∈ Set.Ioo (a i) (b i) ↔ x ∈ Set.Ioo (a i) (b i) := by
    change (a i < y ∧ y < b i) ↔ (a i < x ∧ x < b i)
    exact and_congr (hleftCmp (a i) (ha i) y hy) (hrightCmp (b i) (hb i) y hy)
  have hU (y : ℝ) (hy : y ∈ J) : y ∈ U ↔ x ∈ U := by
    simp only [U, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (hinterval i y hy).mp hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (hinterval i y hy).mpr hi⟩
  have hxJ : x ∈ J := by
    change x - r < x ∧ x < x + r
    exact ⟨by linarith, by linarith⟩
  have hxNotFront : x ∉ frontier K := by
    by_cases hxU : x ∈ U
    · have hJsubU : J ⊆ U := by
        intro y hy
        exact (hU y hy).mpr hxU
      have hJK : J ⊆ K := by
        dsimp [K]
        exact hJopen.subset_interior_iff.mpr (hJsubU.trans subset_closure)
      rw [show frontier K = closure K \ K from isOpen_interior.frontier_eq]
      exact fun h => h.2 (hJK hxJ)
    · have hdisj : Disjoint J U := by
        rw [Set.disjoint_iff_inter_eq_empty]
        ext y
        constructor
        · rintro ⟨hyJ, hyU⟩
          exact False.elim (hxU ((hU y hyJ).mp hyU))
        · intro hy
          simp at hy
      have hxNotClosureU : x ∉ closure U := by
        intro hxClosure
        have hempty := Set.disjoint_iff_inter_eq_empty.mp (hdisj.closure_right hJopen)
        have hmem : x ∈ J ∩ closure U := ⟨hxJ, hxClosure⟩
        rw [hempty] at hmem
        exact hmem
      intro hxKFront
      apply hxNotClosureU
      apply closure_minimal interior_subset isClosed_closure
      exact frontier_subset_closure hxKFront
  exact hxNotFront hxFront


private theorem mem_frontier_interior_closure_iff_sides_differ
    (U : Set ℝ) (hU : IsOpen U) (l x r : ℝ) (hlx : l < x) (hxr : x < r)
    (L R : Prop)
    (hleft : ∀ y ∈ Set.Ioo l x, (y ∈ U ↔ L))
    (hright : ∀ y ∈ Set.Ioo x r, (y ∈ U ↔ R)) :
    x ∈ frontier (interior (closure U)) ↔ (L ∧ ¬ R) ∨ (R ∧ ¬ L) := by
  let K : Set ℝ := interior (closure U)
  have hKopen : IsOpen K := isOpen_interior
  have hKsub : K ⊆ closure U := interior_subset
  have hUsubK : U ⊆ K := hU.subset_interior_iff.mpr subset_closure
  have hleftK (hL : L) : Set.Ioo l x ⊆ K := by
    intro y hy
    exact hUsubK ((hleft y hy).mpr hL)
  have hrightK (hR : R) : Set.Ioo x r ⊆ K := by
    intro y hy
    exact hUsubK ((hright y hy).mpr hR)
  have hxClosureK_of_left (hL : L) : x ∈ closure K := by
    have hxleft : x ∈ closure (Set.Ioo l x) := by
      rw [closure_Ioo (ne_of_lt hlx)]
      exact ⟨hlx.le, le_rfl⟩
    exact (closure_mono (hleftK hL)) hxleft
  have hxClosureK_of_right (hR : R) : x ∈ closure K := by
    have hxright : x ∈ closure (Set.Ioo x r) := by
      rw [closure_Ioo (ne_of_lt hxr)]
      exact ⟨le_rfl, hxr.le⟩
    exact (closure_mono (hrightK hR)) hxright
  have hxK_of_both (hL : L) (hR : R) : x ∈ K := by
    have hJsub : Set.Ioo l r ⊆ closure U := by
      intro y hy
      rcases lt_trichotomy y x with h | h | h
      · exact subset_closure ((hleft y ⟨hy.1, h⟩).mpr hL)
      · subst y
        have hxleft : x ∈ closure (Set.Ioo l x) := by
          rw [closure_Ioo (ne_of_lt hlx)]
          exact ⟨hlx.le, le_rfl⟩
        exact (closure_mono (fun z hz => (hleft z hz).mpr hL)) hxleft
      · exact subset_closure ((hright y ⟨h, hy.2⟩).mpr hR)
    have hxJ : x ∈ Set.Ioo l r := ⟨hlx, hxr⟩
    exact isOpen_Ioo.subset_interior_iff.mpr hJsub hxJ
  have hnotRightClosure (hR : ¬ R) (y : ℝ) (hy : y ∈ Set.Ioo x r) :
      y ∉ closure U := by
    have hdisj : Disjoint (Set.Ioo x r) U := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext z
      constructor
      · rintro ⟨hz, hzu⟩
        exact False.elim (hR ((hright z hz).mp hzu))
      · intro hz
        simp at hz
    have hempty := Set.disjoint_iff_inter_eq_empty.mp
      (hdisj.closure_right isOpen_Ioo)
    intro hyclosure
    have hmem : y ∈ Set.Ioo x r ∩ closure U := ⟨hy, hyclosure⟩
    rw [hempty] at hmem
    exact hmem
  have hnotLeftClosure (hL : ¬ L) (y : ℝ) (hy : y ∈ Set.Ioo l x) :
      y ∉ closure U := by
    have hdisj : Disjoint (Set.Ioo l x) U := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext z
      constructor
      · rintro ⟨hz, hzu⟩
        exact False.elim (hL ((hleft z hz).mp hzu))
      · intro hz
        simp at hz
    have hempty := Set.disjoint_iff_inter_eq_empty.mp
      (hdisj.closure_right isOpen_Ioo)
    intro hyclosure
    have hmem : y ∈ Set.Ioo l x ∩ closure U := ⟨hy, hyclosure⟩
    rw [hempty] at hmem
    exact hmem
  have hxNotK_of_notRight (hR : ¬ R) : x ∉ K := by
    intro hxK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hKopen x hxK
    let δ : ℝ := min (r - x) ε
    let y : ℝ := x + δ / 2
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact lt_min (by linarith) hε
    have hδr : δ ≤ r - x := min_le_left _ _
    have hδε : δ ≤ ε := min_le_right _ _
    have hyRight : y ∈ Set.Ioo x r := by
      constructor <;> dsimp [y] <;> nlinarith
    have hyBall : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      apply abs_lt.mpr
      constructor <;> dsimp [y] <;> nlinarith
    have hyK : y ∈ K := hball hyBall
    exact hnotRightClosure hR y hyRight (hKsub hyK)
  have hxNotK_of_notLeft (hL : ¬ L) : x ∉ K := by
    intro hxK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hKopen x hxK
    let δ : ℝ := min (x - l) ε
    let y : ℝ := x - δ / 2
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact lt_min (by linarith) hε
    have hδl : δ ≤ x - l := min_le_left _ _
    have hδε : δ ≤ ε := min_le_right _ _
    have hyLeft : y ∈ Set.Ioo l x := by
      constructor <;> dsimp [y] <;> nlinarith
    have hyBall : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      apply abs_lt.mpr
      constructor <;> dsimp [y] <;> nlinarith
    have hyK : y ∈ K := hball hyBall
    exact hnotLeftClosure hL y hyLeft (hKsub hyK)
  have hxNotU_of_notLeft (hL : ¬ L) : x ∉ U := by
    intro hxU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
    let δ : ℝ := min (x - l) ε
    let y : ℝ := x - δ / 2
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact lt_min (by linarith) hε
    have hδl : δ ≤ x - l := min_le_left _ _
    have hδε : δ ≤ ε := min_le_right _ _
    have hyLeft : y ∈ Set.Ioo l x := by
      constructor <;> dsimp [y] <;> nlinarith
    have hyBall : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      apply abs_lt.mpr
      constructor <;> dsimp [y] <;> nlinarith
    exact hL ((hleft y hyLeft).mp (hball hyBall))
  have hxNotClosureU_of_noSides (hL : ¬ L) (hR : ¬ R) : x ∉ closure U := by
    have hxNotU := hxNotU_of_notLeft hL
    have hJdisj : Disjoint (Set.Ioo l r) U := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext y
      constructor
      · rintro ⟨hy, hyU⟩
        rcases lt_trichotomy y x with h | h | h
        · exact False.elim (hL ((hleft y ⟨hy.1, h⟩).mp hyU))
        · exact False.elim (hxNotU (h ▸ hyU))
        · exact False.elim (hR ((hright y ⟨h, hy.2⟩).mp hyU))
      · intro hy
        simp at hy
    have hempty := Set.disjoint_iff_inter_eq_empty.mp
      (hJdisj.closure_right isOpen_Ioo)
    have hxJ : x ∈ Set.Ioo l r := ⟨hlx, hxr⟩
    intro hxClosure
    have hmem : x ∈ Set.Ioo l r ∩ closure U := ⟨hxJ, hxClosure⟩
    rw [hempty] at hmem
    exact hmem
  have hfrontier : frontier K = closure K \ K := hKopen.frontier_eq
  rw [hfrontier, Set.mem_sdiff]
  by_cases hL : L <;> by_cases hR : R
  · constructor
    · rintro ⟨_, hxnotK⟩
      exact False.elim (hxnotK (hxK_of_both hL hR))
    · intro h
      rcases h with h | h
      · exact False.elim (h.2 hR)
      · exact False.elim (h.2 hL)
  · constructor
    · rintro ⟨hxClosureK, _⟩
      exact Or.inl ⟨hL, hR⟩
    · intro _
      exact ⟨hxClosureK_of_left hL, hxNotK_of_notRight hR⟩
  · constructor
    · rintro ⟨hxClosureK, _⟩
      exact Or.inr ⟨hR, hL⟩
    · intro _
      exact ⟨hxClosureK_of_right hR, hxNotK_of_notLeft hL⟩
  · constructor
    · rintro ⟨hxClosureK, _⟩
      exact (hxNotClosureU_of_noSides hL hR (closure_minimal hKsub isClosed_closure hxClosureK)).elim
    · intro h
      rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · exact False.elim (hL h)
      · exact False.elim (hR h)

private theorem mem_frontier_interior_closure_iff_of_endpoint_order
    {ι : Type*} (A : Set ℝ) (f : ℝ → ℝ)
    (horder : ∀ s ∈ A, ∀ t ∈ A, s < t ↔ f s < f t)
    (l x r : ℝ) (hlA : l ∈ A) (hxA : x ∈ A) (hrA : r ∈ A)
    (hlx : l < x) (hxr : x < r)
    (hgap : ∀ z ∈ A, l < z → z < r → z = x)
    (a b : ι → ℝ) (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ A) :
    x ∈ frontier (interior (closure (⋃ i, Set.Ioo (a i) (b i)))) ↔
      f x ∈ frontier (interior (closure (⋃ i, Set.Ioo (f (a i)) (f (b i))))) := by
  let U : Set ℝ := ⋃ i, Set.Ioo (a i) (b i)
  let V : Set ℝ := ⋃ i, Set.Ioo (f (a i)) (f (b i))
  let mL : ℝ := (l + x) / 2
  let mR : ℝ := (x + r) / 2
  let nL : ℝ := (f l + f x) / 2
  let nR : ℝ := (f x + f r) / 2
  have hlmL : l < mL := by dsimp [mL]; linarith
  have hmLx : mL < x := by dsimp [mL]; linarith
  have hxmR : x < mR := by dsimp [mR]; linarith
  have hmRr : mR < r := by dsimp [mR]; linarith
  have hflfx : f l < f x := (horder l hlA x hxA).mp hlx
  have hfxfr : f x < f r := (horder x hxA r hrA).mp hxr
  have hfnL : f l < nL := by dsimp [nL]; linarith
  have hnLfx : nL < f x := by dsimp [nL]; linarith
  have hfxnR : f x < nR := by dsimp [nR]; linarith
  have hnRfr : nR < f r := by dsimp [nR]; linarith
  have hle (s t : ℝ) (hs : s ∈ A) (ht : t ∈ A) :
      (s ≤ t ↔ f s ≤ f t) := by
    constructor
    · intro hst
      by_contra hnot
      have hts : f t < f s := lt_of_not_ge hnot
      have : t < s := (horder t ht s hs).mpr hts
      linarith
    · intro hst
      by_contra hnot
      have hts : t < s := lt_of_not_ge hnot
      have : f t < f s := (horder t ht s hs).mp hts
      linarith
  have hleftClass (c : ℝ) (hc : c ∈ A) : c ≤ l ∨ x ≤ c := by
    by_cases hcl : c ≤ l
    · exact Or.inl hcl
    · right
      by_contra hxc
      have hlc : l < c := lt_of_not_ge hcl
      have hcx : c < x := lt_of_not_ge hxc
      have heq := hgap c hc hlc (lt_trans hcx hxr)
      linarith
  have hrightClass (c : ℝ) (hc : c ∈ A) : c ≤ x ∨ r ≤ c := by
    by_cases hcx : c ≤ x
    · exact Or.inl hcx
    · right
      by_contra hrc
      have hxc : x < c := lt_of_not_ge hcx
      have hcr : c < r := lt_of_not_ge hrc
      have heq := hgap c hc (lt_trans hlx hxc) hcr
      linarith
  have hleftLower (c : ℝ) (hc : c ∈ A) (y : ℝ) (hy : y ∈ Set.Ioo l x) :
      (c < y ↔ c < mL) := by
    rcases hy with ⟨hyl, hyx⟩
    rcases hleftClass c hc with hcl | hxc
    · constructor
      · intro _
        exact lt_of_le_of_lt hcl hlmL
      · intro _
        exact lt_of_le_of_lt hcl hyl
    · constructor
      · intro h
        exact False.elim (by linarith)
      · intro h
        exact False.elim (by linarith)
  have hleftUpper (c : ℝ) (hc : c ∈ A) (y : ℝ) (hy : y ∈ Set.Ioo l x) :
      (y < c ↔ mL < c) := by
    rcases hy with ⟨hyl, hyx⟩
    rcases hleftClass c hc with hcl | hxc
    · constructor
      · intro h
        exact False.elim (by linarith)
      · intro h
        exact False.elim (by linarith)
    · constructor
      · intro _
        exact lt_of_lt_of_le hmLx hxc
      · intro _
        exact lt_of_lt_of_le hyx hxc
  have hrightLower (c : ℝ) (hc : c ∈ A) (y : ℝ) (hy : y ∈ Set.Ioo x r) :
      (c < y ↔ c < mR) := by
    rcases hy with ⟨hyx, hyr⟩
    rcases hrightClass c hc with hcx | hrc
    · constructor
      · intro _
        exact lt_of_le_of_lt hcx hxmR
      · intro _
        exact lt_of_le_of_lt hcx hyx
    · constructor
      · intro h
        exact False.elim (by linarith)
      · intro h
        exact False.elim (by linarith)
  have hrightUpper (c : ℝ) (hc : c ∈ A) (y : ℝ) (hy : y ∈ Set.Ioo x r) :
      (y < c ↔ mR < c) := by
    rcases hy with ⟨hyx, hyr⟩
    rcases hrightClass c hc with hcx | hrc
    · constructor
      · intro h
        exact False.elim (by linarith)
      · intro h
        exact False.elim (by linarith)
    · constructor
      · intro _
        exact lt_of_lt_of_le hmRr hrc
      · intro _
        exact lt_of_lt_of_le hyr hrc
  have hleftFClass (c : ℝ) (hc : c ∈ A) : f c ≤ f l ∨ f x ≤ f c := by
    rcases hleftClass c hc with hcl | hxc
    · exact Or.inl ((hle c l hc hlA).mp hcl)
    · exact Or.inr ((hle x c hxA hc).mp hxc)
  have hrightFClass (c : ℝ) (hc : c ∈ A) : f c ≤ f x ∨ f r ≤ f c := by
    rcases hrightClass c hc with hcx | hrc
    · exact Or.inl ((hle c x hc hxA).mp hcx)
    · exact Or.inr ((hle r c hrA hc).mp hrc)
  have hleftFLower (c : ℝ) (hc : c ∈ A) (y : ℝ) (hy : y ∈ Set.Ioo (f l) (f x)) :
      (f c < y ↔ f c < nL) := by
    rcases hy with ⟨hyl, hyx⟩
    rcases hleftFClass c hc with hcl | hxc
    · constructor
      · intro _; exact lt_of_le_of_lt hcl hfnL
      · intro _; exact lt_of_le_of_lt hcl hyl
    · constructor
      · intro h
        exact False.elim (by linarith)
      · intro h
        exact False.elim (by linarith)
  have hleftFUpper (c : ℝ) (hc : c ∈ A) (y : ℝ) (hy : y ∈ Set.Ioo (f l) (f x)) :
      (y < f c ↔ nL < f c) := by
    rcases hy with ⟨hyl, hyx⟩
    rcases hleftFClass c hc with hcl | hxc
    · constructor
      · intro h
        exact False.elim (by linarith)
      · intro h
        exact False.elim (by linarith)
    · constructor
      · intro _; exact lt_of_lt_of_le hnLfx hxc
      · intro _; exact lt_of_lt_of_le hyx hxc
  have hrightFLower (c : ℝ) (hc : c ∈ A) (y : ℝ) (hy : y ∈ Set.Ioo (f x) (f r)) :
      (f c < y ↔ f c < nR) := by
    rcases hy with ⟨hyx, hyr⟩
    rcases hrightFClass c hc with hcx | hrc
    · constructor
      · intro _; exact lt_of_le_of_lt hcx hfxnR
      · intro _; exact lt_of_le_of_lt hcx hyx
    · constructor
      · intro h
        exact False.elim (by linarith)
      · intro h
        exact False.elim (by linarith)
  have hrightFUpper (c : ℝ) (hc : c ∈ A) (y : ℝ) (hy : y ∈ Set.Ioo (f x) (f r)) :
      (y < f c ↔ nR < f c) := by
    rcases hy with ⟨hyx, hyr⟩
    rcases hrightFClass c hc with hcx | hrc
    · constructor
      · intro h
        exact False.elim (by linarith)
      · intro h
        exact False.elim (by linarith)
    · constructor
      · intro _; exact lt_of_lt_of_le hnRfr hrc
      · intro _; exact lt_of_lt_of_le hyr hrc
  have hleftMidLower (c : ℝ) (hc : c ∈ A) : c < mL ↔ f c < nL := by
    have hs : c < mL ↔ c ≤ l := by
      rcases hleftClass c hc with hcl | hxc
      · constructor
        · intro _; exact hcl
        · intro _; exact lt_of_le_of_lt hcl hlmL
      · constructor
        · intro h
          exact False.elim (by linarith)
        · intro h
          exact False.elim (by linarith)
    have ht : f c < nL ↔ f c ≤ f l := by
      rcases hleftFClass c hc with hcl | hxc
      · constructor
        · intro _; exact hcl
        · intro _; exact lt_of_le_of_lt hcl hfnL
      · constructor
        · intro h
          exact False.elim (by linarith)
        · intro h
          exact False.elim (by linarith)
    exact hs.trans ((hle c l hc hlA).trans ht.symm)
  have hleftMidUpper (c : ℝ) (hc : c ∈ A) : mL < c ↔ nL < f c := by
    have hs : mL < c ↔ x ≤ c := by
      rcases hleftClass c hc with hcl | hxc
      · constructor
        · intro h
          exact False.elim (by linarith)
        · intro h
          exact False.elim (by linarith)
      · constructor
        · intro _; exact hxc
        · intro _; exact lt_of_lt_of_le hmLx hxc
    have ht : nL < f c ↔ f x ≤ f c := by
      rcases hleftFClass c hc with hcl | hxc
      · constructor
        · intro h
          exact False.elim (by linarith)
        · intro h
          exact False.elim (by linarith)
      · constructor
        · intro _; exact hxc
        · intro _; exact lt_of_lt_of_le hnLfx hxc
    exact hs.trans ((hle x c hxA hc).trans ht.symm)
  have hrightMidLower (c : ℝ) (hc : c ∈ A) : c < mR ↔ f c < nR := by
    have hs : c < mR ↔ c ≤ x := by
      rcases hrightClass c hc with hcx | hrc
      · constructor
        · intro _; exact hcx
        · intro _; exact lt_of_le_of_lt hcx hxmR
      · constructor
        · intro h
          exact False.elim (by linarith)
        · intro h
          exact False.elim (by linarith)
    have ht : f c < nR ↔ f c ≤ f x := by
      rcases hrightFClass c hc with hcx | hrc
      · constructor
        · intro _; exact hcx
        · intro _; exact lt_of_le_of_lt hcx hfxnR
      · constructor
        · intro h
          exact False.elim (by linarith)
        · intro h
          exact False.elim (by linarith)
    exact hs.trans ((hle c x hc hxA).trans ht.symm)
  have hrightMidUpper (c : ℝ) (hc : c ∈ A) : mR < c ↔ nR < f c := by
    have hs : mR < c ↔ r ≤ c := by
      rcases hrightClass c hc with hcx | hrc
      · constructor
        · intro h
          exact False.elim (by linarith)
        · intro h
          exact False.elim (by linarith)
      · constructor
        · intro _; exact hrc
        · intro _; exact lt_of_lt_of_le hmRr hrc
    have ht : nR < f c ↔ f r ≤ f c := by
      rcases hrightFClass c hc with hcx | hrc
      · constructor
        · intro h
          exact False.elim (by linarith)
        · intro h
          exact False.elim (by linarith)
      · constructor
        · intro _; exact hrc
        · intro _; exact lt_of_lt_of_le hnRfr hrc
    exact hs.trans ((hle r c hrA hc).trans ht.symm)
  have hmL : mL ∈ Set.Ioo l x := ⟨hlmL, hmLx⟩
  have hmR : mR ∈ Set.Ioo x r := ⟨hxmR, hmRr⟩
  have hnL : nL ∈ Set.Ioo (f l) (f x) := ⟨hfnL, hnLfx⟩
  have hnR : nR ∈ Set.Ioo (f x) (f r) := ⟨hfxnR, hnRfr⟩
  have hUopen : IsOpen U := isOpen_iUnion fun i => isOpen_Ioo
  have hVopen : IsOpen V := isOpen_iUnion fun i => isOpen_Ioo
  have hleftU (y : ℝ) (hy : y ∈ Set.Ioo l x) : y ∈ U ↔ mL ∈ U := by
    simp only [U, Set.mem_iUnion, Set.mem_Ioo]
    constructor
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hleftLower (a i) (ha i) y hy).mp hai,
        (hleftUpper (b i) (hb i) y hy).mp hib⟩⟩
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hleftLower (a i) (ha i) y hy).mpr hai,
        (hleftUpper (b i) (hb i) y hy).mpr hib⟩⟩
  have hrightU (y : ℝ) (hy : y ∈ Set.Ioo x r) : y ∈ U ↔ mR ∈ U := by
    simp only [U, Set.mem_iUnion, Set.mem_Ioo]
    constructor
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hrightLower (a i) (ha i) y hy).mp hai,
        (hrightUpper (b i) (hb i) y hy).mp hib⟩⟩
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hrightLower (a i) (ha i) y hy).mpr hai,
        (hrightUpper (b i) (hb i) y hy).mpr hib⟩⟩
  have hleftV (y : ℝ) (hy : y ∈ Set.Ioo (f l) (f x)) : y ∈ V ↔ nL ∈ V := by
    simp only [V, Set.mem_iUnion, Set.mem_Ioo]
    constructor
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hleftFLower (a i) (ha i) y hy).mp hai,
        (hleftFUpper (b i) (hb i) y hy).mp hib⟩⟩
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hleftFLower (a i) (ha i) y hy).mpr hai,
        (hleftFUpper (b i) (hb i) y hy).mpr hib⟩⟩
  have hrightV (y : ℝ) (hy : y ∈ Set.Ioo (f x) (f r)) : y ∈ V ↔ nR ∈ V := by
    simp only [V, Set.mem_iUnion, Set.mem_Ioo]
    constructor
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hrightFLower (a i) (ha i) y hy).mp hai,
        (hrightFUpper (b i) (hb i) y hy).mp hib⟩⟩
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hrightFLower (a i) (ha i) y hy).mpr hai,
        (hrightFUpper (b i) (hb i) y hy).mpr hib⟩⟩
  have hleftMid : mL ∈ U ↔ nL ∈ V := by
    simp only [U, V, Set.mem_iUnion, Set.mem_Ioo]
    constructor
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hleftMidLower (a i) (ha i)).mp hai,
        (hleftMidUpper (b i) (hb i)).mp hib⟩⟩
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hleftMidLower (a i) (ha i)).mpr hai,
        (hleftMidUpper (b i) (hb i)).mpr hib⟩⟩
  have hrightMid : mR ∈ U ↔ nR ∈ V := by
    simp only [U, V, Set.mem_iUnion, Set.mem_Ioo]
    constructor
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hrightMidLower (a i) (ha i)).mp hai,
        (hrightMidUpper (b i) (hb i)).mp hib⟩⟩
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hrightMidLower (a i) (ha i)).mpr hai,
        (hrightMidUpper (b i) (hb i)).mpr hib⟩⟩
  have hsource := mem_frontier_interior_closure_iff_sides_differ
    U hUopen l x r hlx hxr (mL ∈ U) (mR ∈ U) hleftU hrightU
  have htarget := mem_frontier_interior_closure_iff_sides_differ
    V hVopen (f l) (f x) (f r) hflfx hfxfr (nL ∈ V) (nR ∈ V) hleftV hrightV
  calc
    x ∈ frontier (interior (closure U)) ↔
        (mL ∈ U ∧ ¬ mR ∈ U) ∨ (mR ∈ U ∧ ¬ mL ∈ U) := hsource
    _ ↔ (nL ∈ V ∧ ¬ nR ∈ V) ∨ (nR ∈ V ∧ ¬ nL ∈ V) := by
      simp [hleftMid, hrightMid]
    _ ↔ f x ∈ frontier (interior (closure V)) := htarget.symm

private theorem image_frontier_interior_closure_union_intervals_eq_of_ordered_enumeration
    {ι : Type*} (A : Set ℝ) (f : ℝ → ℝ) (hA : IsClosed A)
    (hAf : IsClosed (f '' A))
    (horder : ∀ s ∈ A, ∀ t ∈ A, s < t ↔ f s < f t)
    (a b : ι → ℝ) (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ A)
    (z : ℤ → ℝ) (hzMono : StrictMono z) (hzRange : Set.range z = A) :
    f '' frontier (interior (closure (⋃ i, Set.Ioo (a i) (b i)))) =
      frontier (interior (closure (⋃ i, Set.Ioo (f (a i)) (f (b i))))) := by
  let U : Set ℝ := ⋃ i, Set.Ioo (a i) (b i)
  let V : Set ℝ := ⋃ i, Set.Ioo (f (a i)) (f (b i))
  have hsourceFrontier : frontier (interior (closure U)) ⊆ A :=
    frontier_interior_closure_union_openIntervals_subset_closedEndpoints
      a b A hA ha hb
  have hfa : ∀ i, f (a i) ∈ f '' A := fun i => ⟨a i, ha i, rfl⟩
  have hfb : ∀ i, f (b i) ∈ f '' A := fun i => ⟨b i, hb i, rfl⟩
  have htargetFrontier : frontier (interior (closure V)) ⊆ f '' A :=
    frontier_interior_closure_union_openIntervals_subset_closedEndpoints
      (fun i => f (a i)) (fun i => f (b i)) (f '' A) hAf hfa hfb
  have hz_mem (j : ℤ) : z j ∈ A := by
    rw [← hzRange]
    exact ⟨j, rfl⟩
  have hgap (j : ℤ) : ∀ w ∈ A, z (j - 1) < w → w < z (j + 1) → w = z j := by
    intro w hw hlw hwr
    have hwRange : w ∈ Set.range z := by
      rw [hzRange]
      exact hw
    obtain ⟨n, hn⟩ := Set.mem_range.mp hwRange
    have hleftIndex : j - 1 < n := by
      by_contra hnot
      have hni : n ≤ j - 1 := by omega
      have hmono := hzMono.monotone hni
      rw [hn] at hmono
      exact (not_lt_of_ge hmono) hlw
    have hrightIndex : n < j + 1 := by
      by_contra hnot
      have hni : j + 1 ≤ n := by omega
      have hmono := hzMono.monotone hni
      rw [hn] at hmono
      exact (not_lt_of_ge hmono) hwr
    have hindex : n = j := by omega
    subst n
    exact hn.symm
  have hlocal (j : ℤ) :
      z j ∈ frontier (interior (closure U)) ↔
        f (z j) ∈ frontier (interior (closure V)) := by
    have hlx : z (j - 1) < z j := hzMono (by omega)
    have hxr : z j < z (j + 1) := hzMono (by omega)
    exact mem_frontier_interior_closure_iff_of_endpoint_order
      A f horder (z (j - 1)) (z j) (z (j + 1)) (hz_mem (j - 1)) (hz_mem j)
      (hz_mem (j + 1)) hlx hxr (hgap j) a b ha hb
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hxA : x ∈ A := hsourceFrontier hx
    have hxRange : x ∈ Set.range z := by
      rw [hzRange]
      exact hxA
    obtain ⟨j, hj⟩ := Set.mem_range.mp hxRange
    have hx' : z j ∈ frontier (interior (closure U)) := by simpa [hj] using hx
    have hy' := (hlocal j).mp hx'
    simpa [hj] using hy'
  · intro y hy
    have hyA : y ∈ f '' A := htargetFrontier hy
    obtain ⟨x, hxA, hxy⟩ := hyA
    have hxRange : x ∈ Set.range z := by
      rw [hzRange]
      exact hxA
    obtain ⟨j, hj⟩ := Set.mem_range.mp hxRange
    have hy' : f x ∈ frontier (interior (closure V)) := by simpa [hxy] using hy
    have hxFront : z j ∈ frontier (interior (closure U)) := by
      apply (hlocal j).mpr
      simpa [hj] using hy'
    refine ⟨z j, hxFront, ?_⟩
    rw [hj]
    exact hxy

private theorem mem_union_cell_midpoint_iff_of_endpoint_order
    {ι : Type*} (A : Set ℝ) (f : ℝ → ℝ)
    (horder : ∀ s ∈ A, ∀ t ∈ A, s < t ↔ f s < f t)
    (l r : ℝ) (hlA : l ∈ A) (hrA : r ∈ A) (hlr : l < r)
    (hgap : ∀ z ∈ A, l < z → z < r → False)
    (a b : ι → ℝ) (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ A) :
    ((l + r) / 2 ∈ ⋃ i, Set.Ioo (a i) (b i)) ↔
      ((f l + f r) / 2 ∈ ⋃ i, Set.Ioo (f (a i)) (f (b i))) := by
  let m : ℝ := (l + r) / 2
  let n : ℝ := (f l + f r) / 2
  have hlm : l < m := by dsimp [m]; linarith
  have hmr : m < r := by dsimp [m]; linarith
  have hflfr : f l < f r := (horder l hlA r hrA).mp hlr
  have hfn : f l < n := by dsimp [n]; linarith
  have hnf : n < f r := by dsimp [n]; linarith
  have hle (s t : ℝ) (hs : s ∈ A) (ht : t ∈ A) :
      (s ≤ t ↔ f s ≤ f t) := by
    constructor
    · intro hst
      by_contra hnot
      have hts : f t < f s := lt_of_not_ge hnot
      have : t < s := (horder t ht s hs).mpr hts
      linarith
    · intro hst
      by_contra hnot
      have hts : t < s := lt_of_not_ge hnot
      have : f t < f s := (horder t ht s hs).mp hts
      linarith
  have hleftClass (c : ℝ) (hc : c ∈ A) : c ≤ l ∨ r ≤ c := by
    by_cases hcl : c ≤ l
    · exact Or.inl hcl
    · right
      by_contra hrc
      have hlc : l < c := lt_of_not_ge hcl
      have hcr : c < r := lt_of_not_ge hrc
      exact hgap c hc hlc hcr
  have hleftFClass (c : ℝ) (hc : c ∈ A) : f c ≤ f l ∨ f r ≤ f c := by
    rcases hleftClass c hc with hcl | hxc
    · exact Or.inl ((hle c l hc hlA).mp hcl)
    · exact Or.inr ((hle r c hrA hc).mp hxc)
  have hlow (c : ℝ) (hc : c ∈ A) : c < m ↔ c ≤ l := by
    rcases hleftClass c hc with hcl | hxc
    · constructor
      · intro _; exact hcl
      · intro _; exact lt_of_le_of_lt hcl hlm
    · constructor
      · intro h; exact False.elim (by linarith)
      · intro h; exact False.elim (by linarith)
  have hhigh (c : ℝ) (hc : c ∈ A) : m < c ↔ r ≤ c := by
    rcases hleftClass c hc with hcl | hxc
    · constructor
      · intro h; exact False.elim (by linarith)
      · intro h; exact False.elim (by linarith)
    · constructor
      · intro _; exact hxc
      · intro _; exact lt_of_lt_of_le hmr hxc
  have hflow (c : ℝ) (hc : c ∈ A) : f c < n ↔ f c ≤ f l := by
    rcases hleftFClass c hc with hcl | hxc
    · constructor
      · intro _; exact hcl
      · intro _; exact lt_of_le_of_lt hcl hfn
    · constructor
      · intro h; exact False.elim (by linarith)
      · intro h; exact False.elim (by linarith)
  have hfhigh (c : ℝ) (hc : c ∈ A) : n < f c ↔ f r ≤ f c := by
    rcases hleftFClass c hc with hcl | hxc
    · constructor
      · intro h; exact False.elim (by linarith)
      · intro h; exact False.elim (by linarith)
    · constructor
      · intro _; exact hxc
      · intro _; exact lt_of_lt_of_le hnf hxc
  have hcell (i : ι) :
      (a i < m ∧ m < b i) ↔ (f (a i) < n ∧ n < f (b i)) := by
    exact and_congr
      ((hlow (a i) (ha i)).trans ((hle (a i) l (ha i) hlA).trans (hflow (a i) (ha i)).symm))
      ((hhigh (b i) (hb i)).trans ((hle r (b i) hrA (hb i)).trans (hfhigh (b i) (hb i)).symm))
  simp only [Set.mem_iUnion, Set.mem_Ioo]
  constructor
  · rintro ⟨i, hai, hib⟩
    have hi := (hcell i).mp ⟨hai, hib⟩
    exact ⟨i, hi.1, hi.2⟩
  · rintro ⟨i, hai, hib⟩
    have hi := (hcell i).mpr ⟨hai, hib⟩
    exact ⟨i, hi.1, hi.2⟩

private theorem image_frontier_iUnion_finset_intervals
    {ι : Type*} (A : Set ℝ) (f : ℝ → ℝ) (hA : IsClosed A)
    (hAf : IsClosed (f '' A))
    (horder : ∀ s ∈ A, ∀ t ∈ A, s < t ↔ f s < f t)
    (q : ι → ℝ) (I : Finset (ℝ × ℝ))
    (hendpoints : ∀ i, ∀ e ∈ I, (q i + e.1 ∈ A) ∧ (q i + e.2 ∈ A))
    (z : ℤ → ℝ) (hz : StrictMono z) (hzA : Set.range z = A) :
    f '' frontier (interior (closure (⋃ i, ⋃ e ∈ I, Set.Ioo (q i + e.1) (q i + e.2)))) =
      frontier (interior (closure (⋃ i, ⋃ e ∈ I,
        Set.Ioo (f (q i + e.1)) (f (q i + e.2))))) := by
  let J := ι × {e : ℝ × ℝ // e ∈ I}
  have hgen := image_frontier_interior_closure_union_intervals_eq_of_ordered_enumeration
    A f hA hAf horder (fun j : J => q j.1 + j.2.1.1)
      (fun j : J => q j.1 + j.2.1.2)
      (fun j => (hendpoints j.1 j.2.1 j.2.2).1)
      (fun j => (hendpoints j.1 j.2.1 j.2.2).2) z hz hzA
  change f '' frontier (interior (closure (⋃ j : J,
    Set.Ioo (q j.1 + j.2.1.1) (q j.1 + j.2.1.2)))) =
      frontier (interior (closure (⋃ j : J,
        Set.Ioo (f (q j.1 + j.2.1.1)) (f (q j.1 + j.2.1.2))))) at hgen
  rw [iUnion_finset_reindex I (fun i e => Set.Ioo (q i + e.1) (q i + e.2)),
    iUnion_finset_reindex I (fun i e => Set.Ioo (f (q i + e.1)) (f (q i + e.2)))] at hgen
  exact hgen

private theorem mem_interior_closure_iff_mem_union_at_endpoint_free_midpoint
    {ι : Type*} (A : Set ℝ) (a b : ι → ℝ)
    (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ A)
    (l r : ℝ) (hlr : l < r)
    (hgap : ∀ z ∈ A, l < z → z < r → False) :
    ((l + r) / 2 ∈ interior (closure (⋃ i, Set.Ioo (a i) (b i)))) ↔
      ((l + r) / 2 ∈ ⋃ i, Set.Ioo (a i) (b i) ) := by
  let U : Set ℝ := ⋃ i, Set.Ioo (a i) (b i)
  let m : ℝ := (l + r) / 2
  have hlm : l < m := by dsimp [m]; linarith
  have hmr : m < r := by dsimp [m]; linarith
  have hclass (c : ℝ) (hc : c ∈ A) : c ≤ l ∨ r ≤ c := by
    by_cases hcl : c ≤ l
    · exact Or.inl hcl
    · right
      by_contra hrc
      exact hgap c hc (lt_of_not_ge hcl) (lt_of_not_ge hrc)
  have hlower (c : ℝ) (hc : c ∈ A) (y : ℝ) (hy : y ∈ Set.Ioo l r) :
      (c < y ↔ c < m) := by
    rcases hy with ⟨hyl, hyr⟩
    rcases hclass c hc with hcl | hrc
    · constructor
      · intro _; exact lt_of_le_of_lt hcl hlm
      · intro _; exact lt_of_le_of_lt hcl hyl
    · constructor
      · intro h; exact False.elim (by linarith)
      · intro h; exact False.elim (by linarith)
  have hupper (c : ℝ) (hc : c ∈ A) (y : ℝ) (hy : y ∈ Set.Ioo l r) :
      (y < c ↔ m < c) := by
    rcases hy with ⟨hyl, hyr⟩
    rcases hclass c hc with hcl | hrc
    · constructor
      · intro h; exact False.elim (by linarith)
      · intro h; exact False.elim (by linarith)
    · constructor
      · intro _; exact lt_of_lt_of_le hmr hrc
      · intro _; exact lt_of_lt_of_le hyr hrc
  have hconst (y : ℝ) (hy : y ∈ Set.Ioo l r) : y ∈ U ↔ m ∈ U := by
    simp only [U, Set.mem_iUnion, Set.mem_Ioo]
    constructor
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hlower (a i) (ha i) y hy).mp hai,
        (hupper (b i) (hb i) y hy).mp hib⟩⟩
    · rintro ⟨i, ⟨hai, hib⟩⟩
      exact ⟨i, ⟨(hlower (a i) (ha i) y hy).mpr hai,
        (hupper (b i) (hb i) y hy).mpr hib⟩⟩
  have hUopen : IsOpen U := isOpen_iUnion fun i => isOpen_Ioo
  constructor
  · intro hmInterior
    by_contra hmU
    have hdisj : Disjoint (Set.Ioo l r) U := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext y
      constructor
      · rintro ⟨hy, hyU⟩
        exact False.elim (hmU ((hconst y hy).mp hyU))
      · intro hy
        simp at hy
    have hempty := Set.disjoint_iff_inter_eq_empty.mp
      (hdisj.closure_right isOpen_Ioo)
    have hmInterval : m ∈ Set.Ioo l r := ⟨hlm, hmr⟩
    have hmClosure : m ∈ closure U := interior_subset hmInterior
    have hmem : m ∈ Set.Ioo l r ∩ closure U := ⟨hmInterval, hmClosure⟩
    rw [hempty] at hmem
    exact hmem
  · intro hmU
    have hUsub : U ⊆ interior (closure U) :=
      hUopen.subset_interior_iff.mpr subset_closure
    exact hUsub hmU

private theorem mem_regularized_cell_midpoint_iff_of_endpoint_order
    {ι : Type*} (A : Set ℝ) (f : ℝ → ℝ)
    (horder : ∀ s ∈ A, ∀ t ∈ A, s < t ↔ f s < f t)
    (l r : ℝ) (hlA : l ∈ A) (hrA : r ∈ A) (hlr : l < r)
    (hgap : ∀ z ∈ A, l < z → z < r → False)
    (a b : ι → ℝ) (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ A) :
    ((l + r) / 2 ∈ interior (closure (⋃ i, Set.Ioo (a i) (b i)))) ↔
      ((f l + f r) / 2 ∈ interior (closure (⋃ i, Set.Ioo (f (a i)) (f (b i))))) := by
  have hgapf : ∀ z ∈ f '' A, f l < z → z < f r → False := by
    rintro _ ⟨z, hz, rfl⟩ hlz hzr
    exact hgap z hz ((horder l hlA z hz).mpr hlz) ((horder z hz r hrA).mpr hzr)
  calc
    _ ↔ ((l + r) / 2 ∈ ⋃ i, Set.Ioo (a i) (b i)) :=
      mem_interior_closure_iff_mem_union_at_endpoint_free_midpoint A a b ha hb l r hlr hgap
    _ ↔ ((f l + f r) / 2 ∈ ⋃ i, Set.Ioo (f (a i)) (f (b i))) :=
      mem_union_cell_midpoint_iff_of_endpoint_order A f horder l r hlA hrA hlr hgap a b ha hb
    _ ↔ _ := (mem_interior_closure_iff_mem_union_at_endpoint_free_midpoint
      (f '' A) (f ∘ a) (f ∘ b) (fun i => ⟨a i, ha i, rfl⟩) (fun i => ⟨b i, hb i, rfl⟩)
      (f l) (f r) ((horder l hlA r hrA).mp hlr) hgapf).symm

private theorem mem_regularized_finset_cell_midpoint_iff
    {ι : Type*} (A : Set ℝ) (f : ℝ → ℝ)
    (horder : ∀ s ∈ A, ∀ t ∈ A, s < t ↔ f s < f t)
    (q : ι → ℝ) (I : Finset (ℝ × ℝ))
    (hendpoints : ∀ i, ∀ e ∈ I, (q i + e.1 ∈ A) ∧ (q i + e.2 ∈ A))
    (l r : ℝ) (hlA : l ∈ A) (hrA : r ∈ A) (hlr : l < r)
    (hgap : ∀ z ∈ A, l < z → z < r → False) :
    ((l + r) / 2 ∈ interior (closure (⋃ i, ⋃ e ∈ I, Set.Ioo (q i + e.1) (q i + e.2)))) ↔
      ((f l + f r) / 2 ∈ interior (closure (⋃ i, ⋃ e ∈ I,
        Set.Ioo (f (q i + e.1)) (f (q i + e.2))))) := by
  let J := ι × {e : ℝ × ℝ // e ∈ I}
  have hgen := mem_regularized_cell_midpoint_iff_of_endpoint_order A f horder l r hlA hrA
    hlr hgap (fun j : J => q j.1 + j.2.1.1) (fun j : J => q j.1 + j.2.1.2)
      (fun j => (hendpoints j.1 j.2.1 j.2.2).1) (fun j => (hendpoints j.1 j.2.1 j.2.2).2)
  change ((l + r) / 2 ∈ interior (closure (⋃ j : J,
    Set.Ioo (q j.1 + j.2.1.1) (q j.1 + j.2.1.2)))) ↔
      ((f l + f r) / 2 ∈ interior (closure (⋃ j : J,
        Set.Ioo (f (q j.1 + j.2.1.1)) (f (q j.1 + j.2.1.2))))) at hgen
  rw [iUnion_finset_reindex I (fun i e => Set.Ioo (q i + e.1) (q i + e.2)),
    iUnion_finset_reindex I (fun i e => Set.Ioo (f (q i + e.1)) (f (q i + e.2)))] at hgen
  exact hgen

private theorem mem_iff_of_periodic_cell_colours
    (z x : ℤ → ℝ) (hzMono : StrictMono z) (hxMono : StrictMono x)
    (hxRange : Set.range x ⊆ Set.range z) (f : ℝ → ℝ)
    (horder : ∀ s ∈ Set.range z, ∀ t ∈ Set.range z, s < t ↔ f s < f t)
    (D E : Set ℝ) (hD : IsOpen D) (hE : IsOpen E)
    (hDfront : frontier D ⊆ Set.range x)
    (hEfront : frontier E ⊆ Set.range (fun i => f (x i)))
    (hmid : ∀ j : ℤ,
      ((z j + z (j + 1)) / 2 ∈ D ↔
        (f (z j) + f (z (j + 1))) / 2 ∈ E))
    (k : ℤ) (β : ℝ)
    (hshift : ∀ i : ℤ, f (x (i + k)) = f (x i) + β)
    (hβ : β ∈ periodGroup E) :
    ∀ i : ℤ, ∀ r ∈ Set.Ioo (x i) (x (i + 1)),
      ∀ s ∈ Set.Ioo (x (i + k)) (x (i + k + 1)), r ∈ D ↔ s ∈ D := by
  let g : ℤ → ℝ := fun i => f (x i)
  have hxInRangeZ (i : ℤ) : x i ∈ Set.range z := hxRange ⟨i, rfl⟩
  have hGMono : StrictMono g := by
    intro i j hij
    exact (horder (x i) (hxInRangeZ i) (x j) (hxInRangeZ j)).mp (hxMono hij)
  have hle (a b : ℝ) (ha : a ∈ Set.range z) (hb : b ∈ Set.range z)
      (hab : a ≤ b) : f a ≤ f b := by
    by_contra hnot
    have hba : f b < f a := lt_of_not_ge hnot
    have : b < a := (horder b hb a ha).mpr hba
    linarith
  have hcellConst {C : Set ℝ} (hC : IsOpen C) (w : ℤ → ℝ)
      (hwMono : StrictMono w) (hfront : frontier C ⊆ Set.range w)
      (i : ℤ) (u v : ℝ)
      (hu : u ∈ Set.Ioo (w i) (w (i + 1)))
      (hv : v ∈ Set.Ioo (w i) (w (i + 1))) : u ∈ C ↔ v ∈ C := by
    have hno (p q : ℝ) (hp : p ∈ Set.Ioo (w i) (w (i + 1)))
        (hq : q ∈ Set.Ioo (w i) (w (i + 1))) (hpq : p ≤ q) :
        Set.Icc p q ∩ frontier C = ∅ := by
      ext y
      constructor
      · rintro ⟨⟨hpy, hyq⟩, hyfront⟩
        obtain ⟨n, hn⟩ := Set.mem_range.mp (hfront hyfront)
        have hleftIndex : i < n := by
          by_contra hnot
          have hni : n ≤ i := by omega
          have hmono := hwMono.monotone hni
          rw [hn] at hmono
          exact (not_lt_of_ge hmono) (lt_of_lt_of_le hp.1 hpy)
        have hrightIndex : n < i + 1 := by
          by_contra hnot
          have hni : i + 1 ≤ n := by omega
          have hmono := hwMono.monotone hni
          rw [hn] at hmono
          exact (not_lt_of_ge hmono) (lt_of_le_of_lt hyq hq.2)
        omega
      · intro hy
        simp at hy
    by_cases huv : u ≤ v
    · exact mem_iff_of_no_frontier_on_interval C hC u v huv (hno u v hu hv huv)
    · have hvu : v ≤ u := le_of_not_ge huv
      exact (mem_iff_of_no_frontier_on_interval C hC v u hvu (hno v u hv hu hvu)).symm
  have hperiodSet : β +ᵥ E = E := by
    change β ∈ AddAction.stabilizer ℝ E at hβ
    exact AddAction.mem_stabilizer_iff.mp hβ
  have hperiodPoint (y : ℝ) : y ∈ E ↔ y + β ∈ E := by
    constructor
    · intro hy
      rw [← hperiodSet]
      exact ⟨y, hy, by simp [vadd_eq_add, add_comm]⟩
    · intro hy
      rw [← hperiodSet] at hy
      rcases hy with ⟨y', hy', heq⟩
      have heq' : β + y' = y + β := by simpa [vadd_eq_add] using heq
      have hy'y : y' = y := by linarith [heq']
      simpa [hy'y] using hy'
  have hcellData (i : ℤ) : ∃ j : ℤ, z j = x i ∧ z (j + 1) ≤ x (i + 1) := by
    have hxi : x i ∈ Set.range z := hxInRangeZ i
    have hxn : x (i + 1) ∈ Set.range z := hxInRangeZ (i + 1)
    obtain ⟨j, hj⟩ := Set.mem_range.mp hxi
    obtain ⟨j', hj'⟩ := Set.mem_range.mp hxn
    have hindex : j < j' := by
      by_contra hnot
      have hj'j : j' ≤ j := by omega
      have hmono := hzMono.monotone hj'j
      rw [hj', hj] at hmono
      exact (not_lt_of_ge hmono) (hxMono (by omega))
    have hnext := hzMono.monotone (show j + 1 ≤ j' by omega)
    rw [hj'] at hnext
    exact ⟨j, hj, hnext⟩
  have hmidpointCell (i j : ℤ) (hj : z j = x i)
    (hjn : z (j + 1) ≤ x (i + 1)) :
      (z j + z (j + 1)) / 2 ∈ Set.Ioo (x i) (x (i + 1)) ∧
        (f (z j) + f (z (j + 1))) / 2 ∈ Set.Ioo (g i) (g (i + 1)) := by
    let m : ℝ := (z j + z (j + 1)) / 2
    let n : ℝ := (f (z j) + f (z (j + 1))) / 2
    have hstep : z j < z (j + 1) := hzMono (by omega)
    have hfstep : f (z j) < f (z (j + 1)) :=
      (horder (z j) ⟨j, rfl⟩ (z (j + 1)) ⟨j + 1, rfl⟩).mp hstep
    have hnext : f (z (j + 1)) ≤ f (x (i + 1)) :=
      hle (z (j + 1)) (x (i + 1)) ⟨j + 1, rfl⟩ (hxInRangeZ (i + 1)) hjn
    have hmlo : x i < m := by
      dsimp [m]
      rw [hj]
      linarith
    have hmhi : m < x (i + 1) := by
      dsimp [m]
      linarith
    have hnlo : g i < n := by
      change f (x i) < n
      dsimp [n]
      rw [hj]
      have hfstep' : f (x i) < f (z (j + 1)) := by rw [← hj]; exact hfstep
      linarith
    have hnhi : n < g (i + 1) := by
      change n < f (x (i + 1))
      dsimp [n]
      linarith
    exact ⟨⟨hmlo, hmhi⟩, ⟨hnlo, hnhi⟩⟩
  have hshiftLeft (i : ℤ) : g (i + k) = g i + β := hshift i
  have hshiftRight (i : ℤ) : g (i + k + 1) = g (i + 1) + β := by
    calc
      g (i + k + 1) = g ((i + 1) + k) := by congr 1; omega
      _ = g (i + 1) + β := hshift (i + 1)
  intro i r hr s hs
  obtain ⟨j, hj, hjn⟩ := hcellData i
  obtain ⟨j', hj', hj'n⟩ := hcellData (i + k)
  let m : ℝ := (z j + z (j + 1)) / 2
  let n : ℝ := (f (z j) + f (z (j + 1))) / 2
  let m' : ℝ := (z j' + z (j' + 1)) / 2
  let n' : ℝ := (f (z j') + f (z (j' + 1))) / 2
  have hbaseCell := hmidpointCell i j hj hjn
  have hshiftedCell := hmidpointCell (i + k) j' hj' hj'n
  have hrD : r ∈ D ↔ m ∈ D :=
    hcellConst hD x hxMono hDfront i r m hr hbaseCell.1
  have hmD : m ∈ D ↔ n ∈ E := hmid j
  have hsD : s ∈ D ↔ m' ∈ D :=
    hcellConst hD x hxMono hDfront (i + k) s m' hs hshiftedCell.1
  have hnE : n ∈ E ↔ n + β ∈ E := hperiodPoint n
  rcases hbaseCell.2 with ⟨hbaseLo, hbaseHi⟩
  change g i < n at hbaseLo
  change n < g (i + 1) at hbaseHi
  have htransCell : n + β ∈ Set.Ioo (g (i + k)) (g (i + k + 1)) := by
    rw [hshiftLeft, hshiftRight]
    exact ⟨by linarith, by linarith⟩
  have hnShiftE : n + β ∈ E ↔ n' ∈ E :=
    hcellConst hE g hGMono hEfront (i + k) (n + β) n' htransCell hshiftedCell.2
  have hm'D : m' ∈ D ↔ n' ∈ E := hmid j'
  calc
    r ∈ D ↔ m ∈ D := hrD
    _ ↔ n ∈ E := hmD
    _ ↔ n + β ∈ E := hnE
    _ ↔ n' ∈ E := hnShiftE
    _ ↔ m' ∈ D := hm'D.symm
    _ ↔ s ∈ D := hsD.symm

private theorem finiteApproximation_tests_mono
    (F G : Finset ℝ) (ε η : ℝ) (φ : ℝ →ₗ[ℚ] ℚ)
    (hFG : F ⊆ G) (hηε : η ≤ ε)
    (hφ : Tiling.Approximation.IsFiniteApproximation G η φ) :
    Tiling.Approximation.IsFiniteApproximation F ε φ :=
  ⟨hφ.1, fun x hx => (hφ.2 x (hFG hx)).trans_le hηε⟩

theorem uniformlyReady_commonCarrierPeriod :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    HasRationalSlopes K → Module.finrank ℝ δ = 1 → HasBoundaryDirection K δ →
    TilesOn K T Set.univ → IsUniformlyReady K δ T →
    HasNontrivialEarthquakeDecomposition K δ T →
      ∃ periodVec : Plane, IsCommonCarrierPeriod K δ T periodVec
  := by
  intro K δ T hK hδ hboundary htile hready hnontrivial
  classical
  by_cases hcol : T = columnPart K δ T
  · exact columnPart_eq_commonCarrierPeriod hδ htile hcol
  obtain ⟨P₀, hP₀⟩ := exists_noncolumn_of_ne_columnPart hcol
  have hratδ : HasRationalDirection δ :=
    hasRationalDirection_of_hasBoundaryDirection hK hboundary
  by_cases hratK : Tiling.RationalPolygonal.IsRelativelyRational K
  · exact rational_wholePlane_commonCarrierPeriod K δ T hratK hδ hratδ htile
  have hlink : HasProperLink K δ T :=
    nontrivial_decomposition_hasLink K δ T hδ htile hnontrivial
  have htransverse : HasTransverseFLC K δ T :=
    uniformlyReady_transverseFLC K δ T hδ htile hready
  obtain ⟨P, hP, F, ε, hε, hdeformation⟩ :=
    Approximation.oneLinkRationalDeformation K T δ hδ hratδ hK htile hlink
  obtain ⟨Q, hQ, Fc, εc, hεc, hcorrespondence⟩ :=
    Approximation.transverseFLC_oneLinkComponentCorrespondence
      K T δ hδ hratδ hK htile hlink htransverse
  obtain ⟨Fe, εe, hεe, hcode⟩ :=
    Approximation.polyhedralDeformation_independentOfCode K P Q hP hQ
  obtain ⟨n, hn⟩ := Approximation.rationalDirection_hasNormal δ hδ hratδ
  let π := normalProjection n
  have hπ : Function.Surjective π := normalProjection_surjective n
  have hπker : LinearMap.ker π.toLinearMap = δ := hn
  have hboundaryFinite := boundaryLevels_locallyFinite K δ T hδ htile htransverse π hπ hπker
  have hboundaryNonempty := boundaryLevels_nonempty_of_noncolumn K δ T hδ htile
    (hnontrivial.resolve_left hcol) P₀ hP₀ π.toLinearMap
  have hboundaryLinks (r : ℝ) (hr : r ∈ boundaryLevels K δ T π.toLinearMap) :=
    boundaryLevel_has_vertexLink K δ T hδ htile π.toLinearMap hπker hr
  have htransverse_n : HasTransverseFLC K (Tiling.Approximation.normalDirection n) T := by
    rwa [hn]
  obtain ⟨Fo, εo, hεo, horder⟩ :=
    Approximation.transverseFLC_globalOrderAndBoundedGapReflection
      K T n hK htile htransverse_n 1 zero_lt_one
  obtain ⟨I, hI, hIvertices, Fp, εp, hεp, hprojection⟩ :=
    Approximation.openNormalProjection_deformation K P n hP
  obtain ⟨Fn, εn, hεn, hnormalControl⟩ :=
    Approximation.properLink_normalOrderControl K T n hK htile
  -- The initial model has one common set of tests: no independently selected
  -- constructor choices are silently identified.
  let Ftotal := F ∪ Fc ∪ Fe ∪ Fo ∪ Fp ∪ Fn
  let εtotal := min (min (min ε εc) (min εe εo)) (min εp εn)
  have hεtotal : 0 < εtotal :=
    lt_min (lt_min (lt_min hε hεc) (lt_min hεe hεo)) (lt_min hεp hεn)
  obtain ⟨φ, hφ⟩ := Tiling.Approximation.exists_finiteApproximation Ftotal εtotal hεtotal
  have hφF : Tiling.Approximation.IsFiniteApproximation F ε φ := by
    apply finiteApproximation_tests_mono F Ftotal ε εtotal φ ?_ ?_ hφ
    · intro x hx; simp only [Ftotal, Finset.mem_union]; tauto
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hφFc : Tiling.Approximation.IsFiniteApproximation Fc εc φ := by
    apply finiteApproximation_tests_mono Fc Ftotal εc εtotal φ ?_ ?_ hφ
    · intro x hx; simp only [Ftotal, Finset.mem_union]; tauto
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hφFe : Tiling.Approximation.IsFiniteApproximation Fe εe φ := by
    apply finiteApproximation_tests_mono Fe Ftotal εe εtotal φ ?_ ?_ hφ
    · intro x hx; simp only [Ftotal, Finset.mem_union]; tauto
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hφFo : Tiling.Approximation.IsFiniteApproximation Fo εo φ := by
    apply finiteApproximation_tests_mono Fo Ftotal εo εtotal φ ?_ ?_ hφ
    · intro x hx; simp only [Ftotal, Finset.mem_union]; tauto
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hφFp : Tiling.Approximation.IsFiniteApproximation Fp εp φ := by
    apply finiteApproximation_tests_mono Fp Ftotal εp εtotal φ ?_ ?_ hφ
    · intro x hx; simp only [Ftotal, Finset.mem_union]; tauto
    · exact (min_le_right _ _).trans (min_le_left _ _)
  have hφFn : Tiling.Approximation.IsFiniteApproximation Fn εn φ := by
    apply finiteApproximation_tests_mono Fn Ftotal εn εtotal φ ?_ ?_ hφ
    · intro x hx; simp only [Ftotal, Finset.mem_union]; tauto
    · exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Kφ, hKφsupport, hKφrat, _hφinj, hKφtile, _hφinvariant, _hφcolumn⟩ :=
    hdeformation φ hφF
  obtain ⟨Kψ, hKψsupport, _hψinj, _hψtile, _hψinvariant, e, he⟩ :=
    hcorrespondence φ hφFc
  have hsupport : Kφ.support = Kψ.support :=
    hKφsupport.trans ((hcode φ hφFe).trans hKψsupport.symm)
  have hKφψ : Kφ = Kψ := by
    cases Kφ
    cases Kψ
    cases hsupport
    rfl
  subst Kψ
  obtain ⟨hvertexOrder, hboundedGaps⟩ := horder φ hφFo
  have hIφ := hprojection φ hφFp Kφ hKφsupport
  have hnormal := hnormalControl φ hφFn
  let A : Set ℝ := π '' translatedVertices K T
  let f : ℝ → ℝ := fun r => (φ r : ℝ)
  have hAfinite : ∀ Q : Set ℝ, Bornology.IsBounded Q → (A ∩ Q).Finite :=
    transverse_projection_locallyFinite K δ T htransverse π hπ hπker
  have hAclosed : IsClosed A := finite_bounded_windows_isClosed A hAfinite
  have hAunbounded := translatedVertices_projection_unbounded K T htile π hπ I hI
    (fun e he => (hIvertices e he).2)
  obtain ⟨z, hzA, hzmono⟩ := exists_ordered_integer_chain A
    (fun a b => hAfinite _ isCompact_Icc.isBounded) hAunbounded.1 hAunbounded.2
  have hfOrder : ∀ s ∈ A, ∀ t ∈ A, s < t ↔ f s < f t := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    change Tiling.Approximation.normalEval n v < Tiling.Approximation.normalEval n w ↔
      (φ (Tiling.Approximation.normalEval n v) : ℝ) <
        (φ (Tiling.Approximation.normalEval n w) : ℝ)
    rw [← Tiling.Approximation.rationalNormal_commutes φ n v,
      ← Tiling.Approximation.rationalNormal_commutes φ n w]
    exact hvertexOrder v hv w hw
  obtain ⟨r₀, hr₀⟩ := hboundaryNonempty
  obtain ⟨a₀, ha₀, hπa₀, hproper₀⟩ := hboundaryLinks r₀ hr₀
  have hproper₀n : IsProperLink K (Tiling.Approximation.normalDirection n) T a₀ := by
    rwa [hn]
  have hcoercive : ∀ x ∈ A, |x - π a₀| / 2 ≤ |f x - f (π a₀)| := by
    rintro _ ⟨v, hv, rfl⟩
    have hh := (hnormal a₀ hproper₀n v hv).2.1
    rw [Tiling.Approximation.rationalNormal_commutes] at hh
    have heval : Tiling.Approximation.normalEval n (v - a₀) = π v - π a₀ :=
      map_sub π v a₀
    rw [heval, map_sub, Rat.cast_sub] at hh
    exact hh
  have hAfFinite := coercive_image_finite_bounded_windows A f (π a₀) hAfinite hcoercive
  have hAfClosed : IsClosed (f '' A) := finite_bounded_windows_isClosed _ hAfFinite
  have hcolumnImage : columnPart Kφ δ (Tiling.Approximation.deformPoint φ '' T) =
      Tiling.Approximation.deformPoint φ '' columnPart K δ T := by
    ext x
    constructor
    · intro hx
      obtain ⟨C, hC⟩ := Set.mem_iUnion.mp hx
      let D := e.symm C.1
      have hDcol : IsCenterColumn K δ D.centres :=
        (he D).2.mpr (by simpa only [D, e.apply_symm_apply] using C.property)
      have hcentres : C.1.centres = Tiling.Approximation.deformPoint φ '' D.centres := by
        simpa only [D, e.apply_symm_apply] using (he D).1
      rw [hcentres] at hC
      obtain ⟨t, ht, rfl⟩ := hC
      exact ⟨t, Set.mem_iUnion.mpr ⟨⟨D, hDcol⟩, ht⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨C, hC⟩ := Set.mem_iUnion.mp ht
      apply Set.mem_iUnion.mpr
      refine ⟨⟨e C.1, (he C.1).2.mp C.property⟩, ?_⟩
      rw [(he C.1).1]
      exact ⟨t, hC, rfl⟩
  let ec := componentColourEquiv e (fun P => (he P).2)
  have hcolourCentres (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      colouredCentres Kφ δ (Tiling.Approximation.deformPoint φ '' T) (ec c) =
        Tiling.Approximation.deformPoint φ '' colouredCentres K δ T c :=
    componentColourEquiv_centres e (fun P => (he P).2)
      (Tiling.Approximation.deformPoint φ) (fun P => (he P).1) hcolumnImage c
  have hsourceIntervals
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      π '' colouredCarrier K δ T c = interior (closure
        (⋃ s : colouredCentres K δ T c, ⋃ e ∈ I,
          Set.Ioo (π s + e.1) (π s + e.2))) :=
    invariant_carrier_projection_intervals K (colouredCentres K δ T c) δ π hπ hπker
      (colouredCarrier_invariant K δ T hδ htile c) I hI
  have htargetIntervals
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      π '' colouredCarrier Kφ δ (Tiling.Approximation.deformPoint φ '' T) (ec c) =
        interior (closure (⋃ s : colouredCentres K δ T c, ⋃ e ∈ I,
          Set.Ioo (f (π s + e.1)) (f (π s + e.2)))) := by
    have hinv := colouredCarrier_invariant Kφ δ
      (Tiling.Approximation.deformPoint φ '' T) hδ hKφtile (ec c)
    change IsInvariantAlong (regularSupport Kφ
      (colouredCentres Kφ δ (Tiling.Approximation.deformPoint φ '' T) (ec c))) δ at hinv
    rw [hcolourCentres c] at hinv
    have hopen : IsOpen (openUnion Kφ
        (Tiling.Approximation.deformPoint φ '' colouredCentres K δ T c)) :=
      isOpen_iUnion fun s => (Homeomorph.addLeft (s : Plane)).isOpenMap _ isOpen_interior
    change π '' regularSupport Kφ
      (colouredCentres Kφ δ (Tiling.Approximation.deformPoint φ '' T) (ec c)) = _
    rw [hcolourCentres c, regularSupport,
      invariant_regularize_projection _ hopen δ π hπ hπker hinv]
    have hproj := deformed_openUnion_projection_intervals Kφ
      (colouredCentres K δ T c) n φ I hIφ
    change π '' openUnion Kφ
      (Tiling.Approximation.deformPoint φ '' colouredCentres K δ T c) = _ at hproj
    rw [hproj]
  have hcolourBoundary
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      f '' (π '' frontier (colouredCarrier K δ T c)) =
        π '' frontier (colouredCarrier Kφ δ (Tiling.Approximation.deformPoint φ '' T) (ec c)) := by
    rw [invariant_frontier_projection _ δ π hπ hπker
      (colouredCarrier_invariant K δ T hδ htile c),
      invariant_frontier_projection _ δ π hπ hπker
        (colouredCarrier_invariant Kφ δ _ hδ hKφtile (ec c)),
      hsourceIntervals c, htargetIntervals c]
    apply image_frontier_iUnion_finset_intervals A f hAclosed hAfClosed hfOrder
      (fun s : colouredCentres K δ T c => π s) I ?_ z hzmono hzA
    intro s e heI
    exact normal_interval_endpoints_mem_translatedVertices K T π.toLinearMap I
      (fun e he => (hIvertices e he).2)
      (colouredCentres_subset K δ T c s.property) heI
  have hboundaryImage : f '' boundaryLevels K δ T π.toLinearMap =
      boundaryLevels Kφ δ (Tiling.Approximation.deformPoint φ '' T) π.toLinearMap := by
    ext r
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp ha
      apply Set.mem_iUnion.mpr
      refine ⟨ec c, ?_⟩
      change f a ∈ π '' frontier (colouredCarrier Kφ δ _ (ec c))
      rw [← hcolourBoundary c]
      exact ⟨a, hc, rfl⟩
    · intro hr
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hr
      obtain ⟨b, rfl⟩ := ec.surjective c
      change r ∈ π '' frontier (colouredCarrier Kφ δ _ (ec b)) at hc
      rw [← hcolourBoundary b] at hc
      obtain ⟨a, ha, har⟩ := hc
      exact ⟨a, Set.mem_iUnion.mpr ⟨b, ha⟩, har⟩
  obtain ⟨vφ, hvφ⟩ := rational_wholePlane_commonCarrierPeriod
    Kφ δ (Tiling.Approximation.deformPoint φ '' T)
    (relativelyRational_of_rationalSupport Kφ hKφrat) hδ hratδ hKφtile
  have hP₀φ : e P₀ ∈ noncolumnComponents Kφ δ (Tiling.Approximation.deformPoint φ '' T) := by
    intro hcolφ
    exact hP₀ ((he P₀).2.mpr hcolφ)
  have htwoφ : ∃ P Q : EarthquakeComponent Kφ δ (Tiling.Approximation.deformPoint φ '' T),
      P ≠ Q := by
    obtain ⟨A, B, hAB⟩ := hnontrivial.resolve_left hcol
    exact ⟨e A, e B, fun h => hAB (e.injective h)⟩
  have hBφnonempty := boundaryLevels_nonempty_of_noncolumn Kφ δ
    (Tiling.Approximation.deformPoint φ '' T) hδ hKφtile htwoφ (e P₀) hP₀φ π.toLinearMap
  have hβφ : π vφ ≠ 0 := by
    intro hz
    exact hvφ.1 (hπker ▸ LinearMap.mem_ker.mpr hz)
  obtain ⟨ρφ, hρφ, hdenseφ⟩ := exists_relative_dense_radius_of_period _ hBφnonempty
    (π vφ) hβφ (commonCarrierPeriod_boundaryLevels_period Kφ δ
      (Tiling.Approximation.deformPoint φ '' T) π.toLinearMap vφ hvφ)
  let B := boundaryLevels K δ T π.toLinearMap
  have hBsubset : B ⊆ A := boundaryLevels_subset_translatedVertices K δ T hδ htile
    π.toLinearMap hπker
  have hBmax (b : ℝ) (hb : b ∈ B) : ∃ c ∈ B, b < c := by
    obtain ⟨_, hc, hdist⟩ := hdenseφ (f b + ρφ)
    rw [← hboundaryImage] at hc
    obtain ⟨c, hc, rfl⟩ := hc
    refine ⟨c, hc, (hfOrder b (hBsubset hb) c (hBsubset hc)).mpr ?_⟩
    linarith [(abs_lt.mp hdist).2]
  have hBmin (b : ℝ) (hb : b ∈ B) : ∃ c ∈ B, c < b := by
    obtain ⟨_, hc, hdist⟩ := hdenseφ (f b - ρφ)
    rw [← hboundaryImage] at hc
    obtain ⟨c, hc, rfl⟩ := hc
    refine ⟨c, hc, (hfOrder c (hBsubset hc) b (hBsubset hb)).mpr ?_⟩
    linarith [(abs_lt.mp hdist).1]
  have hBunbounded := finite_windows_no_endpoints_unbounded B ⟨r₀, hr₀⟩
    (fun a b => hboundaryFinite _ isCompact_Icc.isBounded) hBmax hBmin
  obtain ⟨x, hxB, hxmono⟩ := exists_ordered_integer_chain B
    (fun a b => hboundaryFinite _ isCompact_Icc.isBounded) hBunbounded.1 hBunbounded.2
  let xφ : ℤ → ℝ := f ∘ x
  have hxφmono : StrictMono xφ := by
    intro i j hij
    have hiB : x i ∈ B := hxB ▸ Set.mem_range_self i
    have hjB : x j ∈ B := hxB ▸ Set.mem_range_self j
    exact (hfOrder _ (hBsubset hiB) _ (hBsubset hjB)).mp (hxmono hij)
  have hxφB : Set.range xφ = boundaryLevels Kφ δ
      (Tiling.Approximation.deformPoint φ '' T) π.toLinearMap := by
    change Set.range (f ∘ x) = _
    rw [Set.range_comp, hxB]
    exact hboundaryImage
  have htargetGap : ∀ i : ℤ, f (x (i + 1)) - f (x i) < 2 * ρφ :=
    relatively_dense_integer_chain_gap_bound xφ hxφmono ρφ (fun r => by
      obtain ⟨y, hy, hd⟩ := hdenseφ r
      exact ⟨y, hxφB.symm ▸ hy, hd⟩)
  have hsourceGap : ∀ i : ℤ, x (i + 1) - x i < 4 * ρφ := by
    intro i
    have hiB : x i ∈ B := hxB ▸ Set.mem_range_self i
    have hnB : x (i + 1) ∈ B := hxB ▸ Set.mem_range_self (i + 1)
    obtain ⟨a, ha, hπa, hproper⟩ := hboundaryLinks (x i) hiB
    obtain ⟨b, hb, hπb⟩ := hBsubset hnB
    have hpropern : IsProperLink K (Tiling.Approximation.normalDirection n) T a := by
      rwa [hn]
    have hh := (hnormal a hpropern b hb).2.1
    rw [Tiling.Approximation.rationalNormal_commutes] at hh
    have heval : Tiling.Approximation.normalEval n (b - a) = x (i + 1) - x i := by
      change π a = x i at hπa
      change π b = x (i + 1) at hπb
      change π (b - a) = _
      rw [map_sub, hπa, hπb]
    rw [heval, map_sub, Rat.cast_sub] at hh
    have hxpos : 0 < x (i + 1) - x i := sub_pos.mpr (hxmono (by omega))
    have hfxpos : 0 < f (x (i + 1)) - f (x i) := sub_pos.mpr (hxφmono (by omega))
    change |x (i + 1) - x i| / 2 ≤ |f (x (i + 1)) - f (x i)| at hh
    rw [abs_of_pos hxpos, abs_of_pos hfxpos] at hh
    linarith [htargetGap i]
  let M := 16 * ρφ + 1
  have hM : 0 < M := by dsimp [M]; linarith
  obtain ⟨Ff, εf, hεf, hreflection⟩ :=
    Approximation.transverseFLC_globalOrderAndBoundedGapReflection
      K T n hK htile htransverse_n M hM
  let Ffine := F ∪ Fc ∪ Fe ∪ Ff ∪ Fp ∪ Fn
  let εfine := min (min (min ε εc) (min εe εf)) (min εp εn)
  have hεfine : 0 < εfine :=
    lt_min (lt_min (lt_min hε hεc) (lt_min hεe hεf)) (lt_min hεp hεn)
  obtain ⟨χ, hχ⟩ := Tiling.Approximation.exists_finiteApproximation Ffine εfine hεfine
  have hχF : Tiling.Approximation.IsFiniteApproximation F ε χ := by
    apply finiteApproximation_tests_mono F Ffine ε εfine χ ?_ ?_ hχ
    · intro x hx; simp only [Ffine, Finset.mem_union]; tauto
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hχFc : Tiling.Approximation.IsFiniteApproximation Fc εc χ := by
    apply finiteApproximation_tests_mono Fc Ffine εc εfine χ ?_ ?_ hχ
    · intro x hx; simp only [Ffine, Finset.mem_union]; tauto
    · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hχFe : Tiling.Approximation.IsFiniteApproximation Fe εe χ := by
    apply finiteApproximation_tests_mono Fe Ffine εe εfine χ ?_ ?_ hχ
    · intro x hx; simp only [Ffine, Finset.mem_union]; tauto
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hχFf : Tiling.Approximation.IsFiniteApproximation Ff εf χ := by
    apply finiteApproximation_tests_mono Ff Ffine εf εfine χ ?_ ?_ hχ
    · intro x hx; simp only [Ffine, Finset.mem_union]; tauto
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hχFp : Tiling.Approximation.IsFiniteApproximation Fp εp χ := by
    apply finiteApproximation_tests_mono Fp Ffine εp εfine χ ?_ ?_ hχ
    · intro x hx; simp only [Ffine, Finset.mem_union]; tauto
    · exact (min_le_right _ _).trans (min_le_left _ _)
  have hχFn : Tiling.Approximation.IsFiniteApproximation Fn εn χ := by
    apply finiteApproximation_tests_mono Fn Ffine εn εfine χ ?_ ?_ hχ
    · intro x hx; simp only [Ffine, Finset.mem_union]; tauto
    · exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Kχ, hKχsupport, hKχrat, _hχinj, hKχtile, _hχinvariant, _hχcolumn⟩ :=
    hdeformation χ hχF
  obtain ⟨Kξ, hKξsupport, _hξinj, _hξtile, _hξinvariant, eχ, heχ⟩ :=
    hcorrespondence χ hχFc
  have hsupport : Kχ.support = Kξ.support :=
    hKχsupport.trans ((hcode χ hχFe).trans hKξsupport.symm)
  have hKχξ : Kχ = Kξ := by
    cases Kχ
    cases Kξ
    cases hsupport
    rfl
  subst Kξ
  obtain ⟨hvertexOrderχ, hboundedGapsχ⟩ := hreflection χ hχFf
  have hIχ := hprojection χ hχFp Kχ hKχsupport
  have hnormalχ := hnormalControl χ hχFn
  let g : ℝ → ℝ := fun r => (χ r : ℝ)
  have hgOrder : ∀ s ∈ A, ∀ t ∈ A, s < t ↔ g s < g t := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    change Tiling.Approximation.normalEval n v < Tiling.Approximation.normalEval n w ↔
      (χ (Tiling.Approximation.normalEval n v) : ℝ) <
        (χ (Tiling.Approximation.normalEval n w) : ℝ)
    rw [← Tiling.Approximation.rationalNormal_commutes χ n v,
      ← Tiling.Approximation.rationalNormal_commutes χ n w]
    exact hvertexOrderχ v hv w hw
  have hgcoercive : ∀ x ∈ A, |x - π a₀| / 2 ≤ |g x - g (π a₀)| := by
    rintro _ ⟨v, hv, rfl⟩
    have hh := (hnormalχ a₀ hproper₀n v hv).2.1
    rw [Tiling.Approximation.rationalNormal_commutes] at hh
    have heval : Tiling.Approximation.normalEval n (v - a₀) = π v - π a₀ :=
      map_sub π v a₀
    rw [heval, map_sub, Rat.cast_sub] at hh
    exact hh
  have hAgFinite := coercive_image_finite_bounded_windows A g (π a₀) hAfinite hgcoercive
  have hAgClosed : IsClosed (g '' A) := finite_bounded_windows_isClosed _ hAgFinite
  have hcolumnImageχ : columnPart Kχ δ (Tiling.Approximation.deformPoint χ '' T) =
      Tiling.Approximation.deformPoint χ '' columnPart K δ T := by
    ext x
    constructor
    · intro hx
      obtain ⟨C, hC⟩ := Set.mem_iUnion.mp hx
      let D := eχ.symm C.1
      have hDcol : IsCenterColumn K δ D.centres :=
        (heχ D).2.mpr (by simpa only [D, eχ.apply_symm_apply] using C.property)
      have hcentres : C.1.centres = Tiling.Approximation.deformPoint χ '' D.centres := by
        simpa only [D, eχ.apply_symm_apply] using (heχ D).1
      rw [hcentres] at hC
      obtain ⟨t, ht, rfl⟩ := hC
      exact ⟨t, Set.mem_iUnion.mpr ⟨⟨D, hDcol⟩, ht⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨C, hC⟩ := Set.mem_iUnion.mp ht
      apply Set.mem_iUnion.mpr
      refine ⟨⟨eχ C.1, (heχ C.1).2.mp C.property⟩, ?_⟩
      rw [(heχ C.1).1]
      exact ⟨t, hC, rfl⟩
  let ecχ := componentColourEquiv eχ (fun P => (heχ P).2)
  have hcolourCentresχ (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      colouredCentres Kχ δ (Tiling.Approximation.deformPoint χ '' T) (ecχ c) =
        Tiling.Approximation.deformPoint χ '' colouredCentres K δ T c :=
    componentColourEquiv_centres eχ (fun P => (heχ P).2)
      (Tiling.Approximation.deformPoint χ) (fun P => (heχ P).1) hcolumnImageχ c
  have hsourceIntervalsχ
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      π '' colouredCarrier K δ T c = interior (closure
        (⋃ s : colouredCentres K δ T c, ⋃ eχ ∈ I,
          Set.Ioo (π s + eχ.1) (π s + eχ.2))) :=
    invariant_carrier_projection_intervals K (colouredCentres K δ T c) δ π hπ hπker
      (colouredCarrier_invariant K δ T hδ htile c) I hI
  have htargetIntervalsχ
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      π '' colouredCarrier Kχ δ (Tiling.Approximation.deformPoint χ '' T) (ecχ c) =
        interior (closure (⋃ s : colouredCentres K δ T c, ⋃ eχ ∈ I,
          Set.Ioo (g (π s + eχ.1)) (g (π s + eχ.2)))) := by
    have hinv := colouredCarrier_invariant Kχ δ
      (Tiling.Approximation.deformPoint χ '' T) hδ hKχtile (ecχ c)
    change IsInvariantAlong (regularSupport Kχ
      (colouredCentres Kχ δ (Tiling.Approximation.deformPoint χ '' T) (ecχ c))) δ at hinv
    rw [hcolourCentresχ c] at hinv
    have hopen : IsOpen (openUnion Kχ
        (Tiling.Approximation.deformPoint χ '' colouredCentres K δ T c)) :=
      isOpen_iUnion fun s => (Homeomorph.addLeft (s : Plane)).isOpenMap _ isOpen_interior
    change π '' regularSupport Kχ
      (colouredCentres Kχ δ (Tiling.Approximation.deformPoint χ '' T) (ecχ c)) = _
    rw [hcolourCentresχ c, regularSupport,
      invariant_regularize_projection _ hopen δ π hπ hπker hinv]
    have hproj := deformed_openUnion_projection_intervals Kχ
      (colouredCentres K δ T c) n χ I hIχ
    change π '' openUnion Kχ
      (Tiling.Approximation.deformPoint χ '' colouredCentres K δ T c) = _ at hproj
    rw [hproj]
  have hcolourBoundaryχ
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      g '' (π '' frontier (colouredCarrier K δ T c)) =
        π '' frontier (colouredCarrier Kχ δ (Tiling.Approximation.deformPoint χ '' T) (ecχ c)) := by
    rw [invariant_frontier_projection _ δ π hπ hπker
      (colouredCarrier_invariant K δ T hδ htile c),
      invariant_frontier_projection _ δ π hπ hπker
        (colouredCarrier_invariant Kχ δ _ hδ hKχtile (ecχ c)),
      hsourceIntervalsχ c, htargetIntervalsχ c]
    apply image_frontier_iUnion_finset_intervals A g hAclosed hAgClosed hgOrder
      (fun s : colouredCentres K δ T c => π s) I ?_ z hzmono hzA
    intro s eχ heI
    exact normal_interval_endpoints_mem_translatedVertices K T π.toLinearMap I
      (fun eχ heχ => (hIvertices eχ heχ).2)
      (colouredCentres_subset K δ T c s.property) heI
  have hboundaryImageχ : g '' boundaryLevels K δ T π.toLinearMap =
      boundaryLevels Kχ δ (Tiling.Approximation.deformPoint χ '' T) π.toLinearMap := by
    ext r
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp ha
      apply Set.mem_iUnion.mpr
      refine ⟨ecχ c, ?_⟩
      change g a ∈ π '' frontier (colouredCarrier Kχ δ _ (ecχ c))
      rw [← hcolourBoundaryχ c]
      exact ⟨a, hc, rfl⟩
    · intro hr
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hr
      obtain ⟨b, rfl⟩ := ecχ.surjective c
      change r ∈ π '' frontier (colouredCarrier Kχ δ _ (ecχ b)) at hc
      rw [← hcolourBoundaryχ b] at hc
      obtain ⟨a, ha, har⟩ := hc
      exact ⟨a, Set.mem_iUnion.mpr ⟨b, ha⟩, har⟩
  let xχ : ℤ → ℝ := g ∘ x
  have hxχmono : StrictMono xχ := by
    intro i j hij
    have hiB : x i ∈ B := hxB ▸ Set.mem_range_self i
    have hjB : x j ∈ B := hxB ▸ Set.mem_range_self j
    exact (hgOrder _ (hBsubset hiB) _ (hBsubset hjB)).mp (hxmono hij)
  have hxχB : Set.range xχ = boundaryLevels Kχ δ
      (Tiling.Approximation.deformPoint χ '' T) π.toLinearMap := by
    change Set.range (g ∘ x) = _
    rw [Set.range_comp, hxB]
    exact hboundaryImageχ
  obtain ⟨vχ, hvχ⟩ := rational_wholePlane_commonCarrierPeriod
    Kχ δ (Tiling.Approximation.deformPoint χ '' T)
    (relativelyRational_of_rationalSupport Kχ hKχrat) hδ hratδ hKχtile
  have hβχ : π vχ ≠ 0 := by
    intro hz
    exact hvχ.1 (hπker ▸ LinearMap.mem_ker.mpr hz)
  have hperiodχ : π vχ ∈ periodGroup (Set.range xχ) := by
    rw [hxχB]
    exact commonCarrierPeriod_boundaryLevels_period Kχ δ
      (Tiling.Approximation.deformPoint χ '' T) π.toLinearMap vχ hvχ
  obtain ⟨k, hk, hshiftχ⟩ := integer_chain_period_shift xχ hxχmono (π vχ) hβχ hperiodχ
  have hχGap : ∀ i : ℤ, |g (x (i + 1)) - g (x i)| < M / 2 := by
    intro i
    have hiB : x i ∈ B := hxB ▸ Set.mem_range_self i
    have hnB : x (i + 1) ∈ B := hxB ▸ Set.mem_range_self (i + 1)
    obtain ⟨a, ha, hπa, hproper⟩ := hboundaryLinks (x i) hiB
    obtain ⟨b, hb, hπb⟩ := hBsubset hnB
    have hpropern : IsProperLink K (Tiling.Approximation.normalDirection n) T a := by
      rwa [hn]
    have hh := (hnormalχ a hpropern b hb).2.2
    rw [normalProjection_deformed_sub] at hh
    change π a = x i at hπa
    change π b = x (i + 1) at hπb
    have heval : Tiling.Approximation.normalEval n (b - a) = x (i + 1) - x i := by
      change π (b - a) = _
      rw [map_sub, hπa, hπb]
    change |g (π b) - g (π a)| ≤ 2 * |Tiling.Approximation.normalEval n (b - a)| at hh
    rw [hπa, hπb, heval, abs_of_pos (sub_pos.mpr (hxmono (by omega)))] at hh
    dsimp [M]
    linarith [hsourceGap i]
  have htargetEqual (i : ℤ) : g (x (i + 1)) - g (x i) =
      g (x (i + k + 1)) - g (x (i + k)) := by
    have h₀ := hshiftχ i
    have h₁ := hshiftχ (i + 1)
    change g (x (i + k)) = g (x i) + π vχ at h₀
    change g (x (i + 1 + k)) = g (x (i + 1)) + π vχ at h₁
    have hi : i + 1 + k = i + k + 1 := by omega
    rw [hi] at h₁
    linarith
  have hgap : ∀ i : ℤ, x (i + 1) - x i = x (i + k + 1) - x (i + k) := by
    intro i
    obtain ⟨a, ha, hπa⟩ := hBsubset (hxB ▸ Set.mem_range_self (i + 1))
    obtain ⟨b, hb, hπb⟩ := hBsubset (hxB ▸ Set.mem_range_self i)
    obtain ⟨c, hc, hπc⟩ := hBsubset (hxB ▸ Set.mem_range_self (i + k + 1))
    obtain ⟨d, hd, hπd⟩ := hBsubset (hxB ▸ Set.mem_range_self (i + k))
    change π a = x (i + 1) at hπa
    change π b = x i at hπb
    change π c = x (i + k + 1) at hπc
    change π d = x (i + k) at hπd
    have hAB : Tiling.Approximation.normalEval n
        (Tiling.Approximation.deformPoint χ (a - b)) = g (x (i + 1)) - g (x i) := by
      rw [normalProjection_deformed_sub]
      change g (π a) - g (π b) = _
      rw [hπa, hπb]
    have hCD : Tiling.Approximation.normalEval n
        (Tiling.Approximation.deformPoint χ (c - d)) =
          g (x (i + k + 1)) - g (x (i + k)) := by
      rw [normalProjection_deformed_sub]
      change g (π c) - g (π d) = _
      rw [hπc, hπd]
    have hh := (hboundedGapsχ a ha b hb c hc d hd
      (by rw [hAB]; exact hχGap i) (by rw [hCD]; exact hχGap (i + k))).mp
        (by rw [hAB, hCD]; exact htargetEqual i)
    change π (a - b) = π (c - d) at hh
    rw [map_sub, map_sub, hπa, hπb, hπc, hπd] at hh
    exact hh
  let β := x k - x 0
  have hβ : β ≠ 0 := by
    intro hz
    exact hk (hxmono.injective (sub_eq_zero.mp hz))
  have hdisplacement := integer_gap_shift x k hgap
  have hshiftSource : ∀ i : ℤ, x (i + k) = x i + β := by
    intro i
    have hh := hdisplacement i
    dsimp [β]
    linarith
  have hsourceOpen
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      IsOpen (π '' colouredCarrier K δ T c) := by
    rw [hsourceIntervalsχ c]
    exact isOpen_interior
  have htargetOpen
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      IsOpen (π '' colouredCarrier Kχ δ (Tiling.Approximation.deformPoint χ '' T) (ecχ c)) := by
    rw [htargetIntervalsχ c]
    exact isOpen_interior
  have hsourceReg
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      interior (closure (π '' colouredCarrier K δ T c)) = π '' colouredCarrier K δ T c := by
    rw [hsourceIntervalsχ c]
    exact interior_closure_idem
  have hsourceFront
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      frontier (π '' colouredCarrier K δ T c) ⊆ Set.range x := by
    rw [← invariant_frontier_projection _ δ π hπ hπker
      (colouredCarrier_invariant K δ T hδ htile c)]
    intro r hr
    have hrB : r ∈ B := Set.mem_iUnion.mpr ⟨c, hr⟩
    exact hxB.symm ▸ hrB
  have htargetFront
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      frontier (π '' colouredCarrier Kχ δ (Tiling.Approximation.deformPoint χ '' T) (ecχ c)) ⊆
        Set.range xχ := by
    rw [← invariant_frontier_projection _ δ π hπ hπker
      (colouredCarrier_invariant Kχ δ _ hδ hKχtile (ecχ c))]
    intro r hr
    have hrB : r ∈ boundaryLevels Kχ δ (Tiling.Approximation.deformPoint χ '' T) π.toLinearMap :=
      Set.mem_iUnion.mpr ⟨ecχ c, hr⟩
    exact hxχB.symm ▸ hrB
  have hmidAgreement
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) (j : ℤ) :
      ((z j + z (j + 1)) / 2 ∈ π '' colouredCarrier K δ T c) ↔
        ((g (z j) + g (z (j + 1))) / 2 ∈
          π '' colouredCarrier Kχ δ (Tiling.Approximation.deformPoint χ '' T) (ecχ c)) := by
    rw [hsourceIntervalsχ c, htargetIntervalsχ c]
    have hendpoints (s : colouredCentres K δ T c) (e : ℝ × ℝ) (heI : e ∈ I) :
        (π s + e.1 ∈ A) ∧ (π s + e.2 ∈ A) := by
      exact normal_interval_endpoints_mem_translatedVertices K T π.toLinearMap I
        (fun e he => (hIvertices e he).2) (colouredCentres_subset K δ T c s.property) heI
    have hgapZ : ∀ r ∈ A, z j < r → r < z (j + 1) → False := by
      intro r hr hlr hrr
      exact Set.disjoint_left.mp (integer_chain_cell_avoids_range z hzmono j)
        ⟨hlr, hrr⟩ (hzA.symm ▸ hr)
    exact mem_regularized_finset_cell_midpoint_iff A g hgOrder
      (fun s : colouredCentres K δ T c => π s) I hendpoints (z j) (z (j + 1))
        (hzA ▸ Set.mem_range_self j) (hzA ▸ Set.mem_range_self (j + 1)) (hzmono (by omega)) hgapZ
  have hcolourPeriodχ
      (c : Option {P : EarthquakeComponent Kχ δ (Tiling.Approximation.deformPoint χ '' T) //
        P ∈ noncolumnComponents Kχ δ (Tiling.Approximation.deformPoint χ '' T)}) :
      vχ ∈ periodGroup (colouredCarrier Kχ δ (Tiling.Approximation.deformPoint χ '' T) c) := by
    cases c with
    | none => exact hvχ.2.1
    | some c => exact hvχ.2.2 c.1 c.2
  have hscalarPeriodχ
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      π vχ ∈ periodGroup
        (π '' colouredCarrier Kχ δ (Tiling.Approximation.deformPoint χ '' T) (ecχ c)) :=
    (periodGroup_map_eq_of_isInvariantAlong _ δ π.toLinearMap hπker
      (colouredCarrier_invariant Kχ δ _ hδ hKχtile (ecχ c)) vχ).mp (hcolourPeriodχ (ecχ c))
  have hcellColours
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      ∀ i : ℤ, ∀ r ∈ Set.Ioo (x i) (x (i + 1)),
        ∀ s ∈ Set.Ioo (x (i + k)) (x (i + k + 1)),
          r ∈ π '' colouredCarrier K δ T c ↔ s ∈ π '' colouredCarrier K δ T c := by
    apply mem_iff_of_periodic_cell_colours z x hzmono hxmono ?_ g ?_
      (π '' colouredCarrier K δ T c)
      (π '' colouredCarrier Kχ δ (Tiling.Approximation.deformPoint χ '' T) (ecχ c))
      (hsourceOpen c) (htargetOpen c) (hsourceFront c) (htargetFront c)
      (hmidAgreement c) k (π vχ) hshiftχ (hscalarPeriodχ c)
    · intro r hr
      rw [hzA]
      exact hBsubset (hxB ▸ hr)
    · intro s hs t ht
      exact hgOrder s (hzA ▸ hs) t (hzA ▸ ht)
  have hscalarPeriod
      (c : Option {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
      β ∈ periodGroup (π '' colouredCarrier K δ T c) := by
    apply regularopen_period_of_integer_chain_cell_shift x hxmono ?_ ?_
      (π '' colouredCarrier K δ T c) (hsourceOpen c) (hsourceReg c) k β hshiftSource (hcellColours c)
    · intro Q hQ
      rw [hxB]
      exact hboundaryFinite Q hQ
    · intro r
      obtain ⟨b, hb, hbr⟩ := hBunbounded.2 r
      obtain ⟨j, rfl⟩ := hxB.symm ▸ hb
      exact ⟨j, hbr⟩
  obtain ⟨w, hw⟩ := hπ β
  refine ⟨w, ?_, ?_, ?_⟩
  · intro hwd
    have hwzero : π w = 0 := LinearMap.mem_ker.mp (hπker.symm ▸ hwd)
    exact hβ (hw.symm.trans hwzero)
  · change w ∈ periodGroup (colouredCarrier K δ T none)
    apply (periodGroup_map_eq_of_isInvariantAlong _ δ π.toLinearMap hπker
      (colouredCarrier_invariant K δ T hδ htile none) w).mpr
    change π w ∈ periodGroup (π '' colouredCarrier K δ T none)
    rw [hw]
    exact hscalarPeriod none
  · intro P hP
    change w ∈ periodGroup (colouredCarrier K δ T (some ⟨P, hP⟩))
    apply (periodGroup_map_eq_of_isInvariantAlong _ δ π.toLinearMap hπker
      (colouredCarrier_invariant K δ T hδ htile (some ⟨P, hP⟩)) w).mpr
    change π w ∈ periodGroup (π '' colouredCarrier K δ T (some ⟨P, hP⟩))
    rw [hw]
    exact hscalarPeriod (some ⟨P, hP⟩)


-- Exact consumed predecessor statements are retained in the validation stdout.

end Tiling.RationalSlopes
