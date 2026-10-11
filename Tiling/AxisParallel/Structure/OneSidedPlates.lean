import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.OneDimensional.ColumnSlices
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Structure.HorizontalBoundaryChains
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Approximation.GoodApproximationPreservesTilings
import Tiling.AxisParallel.Continuous.PositiveSimilarityPlates
import Tiling.AxisParallel.OneDimensional.FiniteInterval.WholeLine
import Tiling.AxisParallel.Foundations.OneDimensionalTilings
import Tiling.AxisParallel.Continuous.RationalSlabPeriodicity

/-!
# One-sided vertical plates

Projection gaps, normalized rational approximations, transported extremal
columns, slice-mass comparison, and the lower and upper column criteria for
one-sided vertical plates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Function MeasureTheory Set
open scoped Pointwise Topology
noncomputable section

namespace Tiling.AxisParallel.Structure

open Tiling
open Tiling.AxisParallel
open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.ColumnSlices

private theorem plateBaseBounds_projectedCentres :
    ∀ {K : Region} {T : Set Tiling.Plane},
      ∀ P : Continuous.VerticalPlate K T,
        (BddBelow P.base → BddBelow (Complex.re '' P.centres)) ∧
        (BddAbove P.base → BddAbove (Complex.re '' P.centres)) := by
  intro K T P
  rcases K.isPolygonal.interior_nonempty K.nonempty with ⟨u, hu⟩
  have hopen : IsOpen (openUnion K P.centres) := by
    rw [openUnion]
    exact isOpen_iUnion fun t : P.centres ↦ K.openCarrier_regularOpen.1.vadd t.1
  have hmem (t : Tiling.Plane) (ht : t ∈ P.centres) :
      t +ᵥ u ∈ P.support := by
    rw [Continuous.VerticalPlate.support_eq_regularSupport, regularSupport]
    apply hopen.subset_interior_closure
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
    refine ⟨⟨t, ht⟩, ?_⟩
    exact ⟨u, hu, rfl⟩
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b - u.re, ?_⟩
    rintro x ⟨t, ht, rfl⟩
    have hbase : (t +ᵥ u).re ∈ P.base := by
      rw [Continuous.VerticalPlate.base_eq]
      exact ⟨t +ᵥ u, hmem t ht, rfl⟩
    have := hb hbase
    simp only [vadd_eq_add, Complex.add_re] at this
    linarith
  · rintro ⟨b, hb⟩
    refine ⟨b - u.re, ?_⟩
    rintro x ⟨t, ht, rfl⟩
    have hbase : (t +ᵥ u).re ∈ P.base := by
      rw [Continuous.VerticalPlate.base_eq]
      exact ⟨t +ᵥ u, hmem t ht, rfl⟩
    have := hb hbase
    simp only [vadd_eq_add, Complex.add_re] at this
    linarith

private theorem locallyFiniteSet_hasExtremumAndGap :
    ∀ Z : Set ℝ,
      Z.Nonempty →
      (∀ Q : Set ℝ, Bornology.IsBounded Q → (Z ∩ Q).Finite) →
      (BddBelow Z →
        ∃ a eta : ℝ, 0 < eta ∧ IsLeast Z a ∧
          ∀ x ∈ Z, a < x → a + eta ≤ x) ∧
      (BddAbove Z →
        ∃ a eta : ℝ, 0 < eta ∧ IsGreatest Z a ∧
          ∀ x ∈ Z, x < a → x ≤ a - eta) := by
  intro Z hZ hfinite
  obtain ⟨z₀, hz₀⟩ := hZ
  constructor
  · rintro ⟨b, hb⟩
    let F := (hfinite (Icc b z₀) (Metric.isBounded_Icc b z₀)).toFinset
    have hzF : z₀ ∈ F := by simp [F, hz₀, hb hz₀]
    have hFne : F.Nonempty := ⟨z₀, hzF⟩
    let a := F.min' hFne
    have haF : a ∈ F := F.min'_mem hFne
    have haMem : a ∈ Z ∩ Icc b z₀ := by simpa [F] using haF
    have haLeast : IsLeast Z a := by
      refine ⟨haMem.1, ?_⟩
      intro x hx
      by_cases hxz : x ≤ z₀
      · apply F.min'_le
        simp [F, hx, hb hx, hxz]
      · exact haMem.2.2.trans (le_of_not_ge hxz)
    let G := (hfinite (Ioc a (a + 1)) (Metric.isBounded_Ioc a (a + 1))).toFinset
    by_cases hGne : G.Nonempty
    · let m := G.min' hGne
      have hmG : m ∈ G := G.min'_mem hGne
      have hmMem : m ∈ Z ∩ Ioc a (a + 1) := by simpa [G] using hmG
      refine ⟨a, m - a, sub_pos.mpr hmMem.2.1, haLeast, ?_⟩
      intro x hx hax
      by_cases hx1 : x ≤ a + 1
      · have hmx : m ≤ x := by
          apply G.min'_le
          simp [G, hx, hax, hx1]
        linarith
      · linarith [hmMem.2.2]
    · refine ⟨a, 1, zero_lt_one, haLeast, ?_⟩
      intro x hx hax
      by_contra hnot
      have hx1 : x ≤ a + 1 := by linarith
      exact hGne ⟨x, by simp [G, hx, hax, hx1]⟩
  · rintro ⟨b, hb⟩
    let F := (hfinite (Icc z₀ b) (Metric.isBounded_Icc z₀ b)).toFinset
    have hzF : z₀ ∈ F := by simp [F, hz₀, hb hz₀]
    have hFne : F.Nonempty := ⟨z₀, hzF⟩
    let a := F.max' hFne
    have haF : a ∈ F := F.max'_mem hFne
    have haMem : a ∈ Z ∩ Icc z₀ b := by simpa [F] using haF
    have haGreatest : IsGreatest Z a := by
      refine ⟨haMem.1, ?_⟩
      intro x hx
      by_cases hzx : z₀ ≤ x
      · apply Finset.le_max'
        simp [F, hx, hzx, hb hx]
      · exact (le_of_not_ge hzx).trans haMem.2.1
    let G := (hfinite (Ico (a - 1) a) (Metric.isBounded_Ico (a - 1) a)).toFinset
    by_cases hGne : G.Nonempty
    · let m := G.max' hGne
      have hmG : m ∈ G := G.max'_mem hGne
      have hmMem : m ∈ Z ∩ Ico (a - 1) a := by simpa [G] using hmG
      refine ⟨a, a - m, sub_pos.mpr hmMem.2.2, haGreatest, ?_⟩
      intro x hx hxa
      by_cases h1x : a - 1 ≤ x
      · have hxm : x ≤ m := by
          apply Finset.le_max'
          simp [G, hx, h1x, hxa]
        linarith
      · linarith [hmMem.2.1]
    · refine ⟨a, 1, zero_lt_one, haGreatest, ?_⟩
      intro x hx hxa
      by_contra hnot
      have h1x : a - 1 ≤ x := by linarith
      exact hGne ⟨x, by simp [G, hx, h1x, hxa]⟩

theorem oneSidedPlate_hasProjectionGap :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ P : Continuous.VerticalPlate K T,
        (BddBelow P.base →
          ∃ a eta : ℝ, 0 < eta ∧
            IsLeast (Complex.re '' P.centres) a ∧
              ∀ x ∈ Complex.re '' P.centres,
                a < x → a + eta ≤ x) ∧
        (BddAbove P.base →
          ∃ a eta : ℝ, 0 < eta ∧
            IsGreatest (Complex.re '' P.centres) a ∧
              ∀ x ∈ Complex.re '' P.centres,
                x < a → x ≤ a - eta) := by
  intro K T hTile P
  have hPne : P.centres.Nonempty := by
    obtain ⟨p, hp⟩ := P.nonempty_supp
    exact ⟨p, p, hp, rfl⟩
  have hfull_base : ∀ Q : Continuous.VerticalPlate K T,
      Q.centres = T → Q.base = (Set.univ : Set ℝ) := by
    intro Q hQT
    rw [Continuous.VerticalPlate.base_eq,
      Continuous.VerticalPlate.support_eq_regularSupport, hQT,
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile]
    simp
  have hnontrivial_of_lower (hbelow : BddBelow P.base) :
      ¬ ∃ Q : Continuous.VerticalPlate K T,
        ¬ Continuous.IsVerticalColumn Q ∧ Q.centres = T := by
    rintro ⟨Q, hQnoncolumn, hQT⟩
    obtain ⟨p, hp⟩ := hPne
    obtain ⟨s, hsP, rfl⟩ := hp
    have hsQ : (s : Tiling.Plane) ∈ Q.centres := hQT.symm ▸ s.2
    obtain ⟨q, hqQ, hsq⟩ := hsQ
    have hsq' : q = s := Subtype.ext hsq
    have hsQsupp : s ∈ Q.supp := by simpa [hsq'] using hqQ
    have hPQ : P = Q :=
      SimpleGraph.ConnectedComponent.eq_of_common_vertex hsP hsQsupp
    have hQbound : BddBelow Q.base := by simpa [hPQ] using hbelow
    rw [hfull_base Q hQT] at hQbound
    rcases hQbound with ⟨b, hb⟩
    have h₀ := hb (a := (0 : ℝ)) (Set.mem_univ _)
    have h₁ := hb (a := b - 1) (Set.mem_univ _)
    linarith
  have hnontrivial_of_upper (habove : BddAbove P.base) :
      ¬ ∃ Q : Continuous.VerticalPlate K T,
        ¬ Continuous.IsVerticalColumn Q ∧ Q.centres = T := by
    rintro ⟨Q, hQnoncolumn, hQT⟩
    obtain ⟨p, hp⟩ := hPne
    obtain ⟨s, hsP, rfl⟩ := hp
    have hsQ : (s : Tiling.Plane) ∈ Q.centres := hQT.symm ▸ s.2
    obtain ⟨q, hqQ, hsq⟩ := hsQ
    have hsq' : q = s := Subtype.ext hsq
    have hsQsupp : s ∈ Q.supp := by simpa [hsq'] using hqQ
    have hPQ : P = Q :=
      SimpleGraph.ConnectedComponent.eq_of_common_vertex hsP hsQsupp
    have hQbound : BddAbove Q.base := by simpa [hPQ] using habove
    rw [hfull_base Q hQT] at hQbound
    rcases hQbound with ⟨b, hb⟩
    have h₀ := hb (a := (0 : ℝ)) (Set.mem_univ _)
    have h₁ := hb (a := b + 1) (Set.mem_univ _)
    linarith
  have hPsub : P.centres ⊆ T := by
    rintro p ⟨s, hs, rfl⟩
    exact s.2
  have hZne : (Complex.re '' P.centres).Nonempty := hPne.image _
  have hbounds := plateBaseBounds_projectedCentres P
  constructor
  · intro hbelow
    have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
        ((Complex.re '' P.centres) ∩ Q).Finite := by
      intro Q hQ
      exact (projectedCentres_closedLocallyFinite hTile
        (hnontrivial_of_lower hbelow)).2 Q hQ |>.subset
        (inter_subset_inter (image_mono hPsub) subset_rfl)
    have hgap := locallyFiniteSet_hasExtremumAndGap
      (Complex.re '' P.centres) hZne hlocal
    exact hgap.1 (hbounds.1 hbelow)
  · intro habove
    have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
        ((Complex.re '' P.centres) ∩ Q).Finite := by
      intro Q hQ
      exact (projectedCentres_closedLocallyFinite hTile
        (hnontrivial_of_upper habove)).2 Q hQ |>.subset
        (inter_subset_inter (image_mono hPsub) subset_rfl)
    have hgap := locallyFiniteSet_hasExtremumAndGap
      (Complex.re '' P.centres) hZne hlocal
    exact hgap.2 (hbounds.2 habove)


private theorem extremePoint_mem_vertexSet {S : Set Tiling.Plane} {x : Tiling.Plane}
    (hx : x ∈ S.extremePoints ℝ) : x ∈ Tiling.vertexSet S := by
  rw [mem_extremePoints_iff_left] at hx
  intro T
  have hxu : x ∈ ⋃₀ (T.pieces : Set (Set Tiling.Plane)) := by
    rw [T.sUnion_eq]; exact hx.1
  obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp hxu
  refine ⟨t, ht, ?_⟩
  rw [mem_extremePoints_iff_left]
  refine ⟨hxt, ?_⟩
  intro y hy z hz hseg
  apply hx.2 y
  · rw [← T.sUnion_eq]; exact Set.mem_sUnion_of_mem hy ht
  · rw [← T.sUnion_eq]; exact Set.mem_sUnion_of_mem hz ht
  · exact hseg

private theorem exists_extremePoint_isMin_re {S : Set Tiling.Plane}
    (hcompact : IsCompact S) (hne : S.Nonempty) :
    ∃ x ∈ S.extremePoints ℝ, ∀ y ∈ S, x.re ≤ y.re := by
  obtain ⟨x, hx, hmin⟩ := hcompact.exists_isMinOn hne Complex.continuous_re.continuousOn
  let F : Set Tiling.Plane := S ∩ {z | z.re = x.re}
  have hFc : IsCompact F :=
    hcompact.inter_right (isClosed_eq Complex.continuous_re continuous_const)
  have hFn : F.Nonempty := ⟨x, hx, rfl⟩
  obtain ⟨p, hp, hpmax⟩ := hFc.exists_isMaxOn hFn Complex.continuous_im.continuousOn
  refine ⟨p, ?_, ?_⟩
  · rw [mem_extremePoints_iff_left]
    refine ⟨hp.1, ?_⟩
    intro y hy z hz hseg
    rcases hseg with ⟨a,b,ha,hb,hab,hpseg⟩
    have hpre := congrArg Complex.re hpseg
    have hpim := congrArg Complex.im hpseg
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at hpre
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at hpim
    have hyre : p.re ≤ y.re := by rw [hp.2]; exact hmin hy
    have hzre : p.re ≤ z.re := by rw [hp.2]; exact hmin hz
    have hsum : a*(y.re-p.re)+b*(z.re-p.re)=0 := by
      calc
        _ = a*y.re + b*z.re - (a+b)*p.re := by ring
        _ = 0 := by rw [hpre, hab]; ring
    have hyzero : a*(y.re-p.re)=0 := by
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hyre),
        mul_nonneg hb.le (sub_nonneg.mpr hzre)]
    have hzzero : b*(z.re-p.re)=0 := by
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hyre),
        mul_nonneg hb.le (sub_nonneg.mpr hzre)]
    have hyre' : y.re = p.re := by rcases mul_eq_zero.mp hyzero with h|h <;> nlinarith
    have hzre' : z.re = p.re := by rcases mul_eq_zero.mp hzzero with h|h <;> nlinarith
    have hyim : y.im ≤ p.im := hpmax ⟨hy, hyre'.trans hp.2⟩
    have hzim : z.im ≤ p.im := hpmax ⟨hz, hzre'.trans hp.2⟩
    have himsum : a*(p.im-y.im)+b*(p.im-z.im)=0 := by
      calc
        _ = (a+b)*p.im - (a*y.im + b*z.im) := by ring
        _ = 0 := by rw [hpim, hab]; ring
    have hyim0 : a*(p.im-y.im)=0 := by
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hyim),
        mul_nonneg hb.le (sub_nonneg.mpr hzim)]
    have hyim' : y.im = p.im := by rcases mul_eq_zero.mp hyim0 with h|h <;> nlinarith
    exact Complex.ext hyre' hyim'
  · intro y hy; rw [hp.2]; exact hmin hy

private theorem exists_extremePoint_isMax_re {S : Set Tiling.Plane}
    (hcompact : IsCompact S) (hne : S.Nonempty) :
    ∃ x ∈ S.extremePoints ℝ, ∀ y ∈ S, y.re ≤ x.re := by
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn hne Complex.continuous_re.continuousOn
  let F : Set Tiling.Plane := S ∩ {z | z.re = x.re}
  have hFc : IsCompact F :=
    hcompact.inter_right (isClosed_eq Complex.continuous_re continuous_const)
  have hFn : F.Nonempty := ⟨x, hx, rfl⟩
  obtain ⟨p, hp, hpmin⟩ := hFc.exists_isMinOn hFn Complex.continuous_im.continuousOn
  refine ⟨p, ?_, ?_⟩
  · rw [mem_extremePoints_iff_left]
    refine ⟨hp.1, ?_⟩
    intro y hy z hz hseg
    rcases hseg with ⟨a,b,ha,hb,hab,hpseg⟩
    have hpre := congrArg Complex.re hpseg
    have hpim := congrArg Complex.im hpseg
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at hpre
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at hpim
    have hyre : y.re ≤ p.re := by rw [hp.2]; exact hmax hy
    have hzre : z.re ≤ p.re := by rw [hp.2]; exact hmax hz
    have hsum : a*(p.re-y.re)+b*(p.re-z.re)=0 := by
      calc
        _ = (a+b)*p.re - (a*y.re+b*z.re) := by ring
        _ = 0 := by rw [hpre, hab]; ring
    have hyzero : a*(p.re-y.re)=0 := by
      nlinarith [hsum, mul_nonneg ha.le (sub_nonneg.mpr hyre),
        mul_nonneg hb.le (sub_nonneg.mpr hzre)]
    have hzzero : b*(p.re-z.re)=0 := by
      nlinarith [hsum, mul_nonneg ha.le (sub_nonneg.mpr hyre),
        mul_nonneg hb.le (sub_nonneg.mpr hzre)]
    have hyre' : y.re = p.re := by rcases mul_eq_zero.mp hyzero with h|h <;> nlinarith
    have hzre' : z.re = p.re := by rcases mul_eq_zero.mp hzzero with h|h <;> nlinarith
    have hyim : p.im ≤ y.im := hpmin ⟨hy, hyre'.trans hp.2⟩
    have hzim : p.im ≤ z.im := hpmin ⟨hz, hzre'.trans hp.2⟩
    have himsum : a*(y.im-p.im)+b*(z.im-p.im)=0 := by
      calc
        _ = a*y.im+b*z.im-(a+b)*p.im := by ring
        _ = 0 := by rw [hpim, hab]; ring
    have hyim0 : a*(y.im-p.im)=0 := by
      nlinarith [himsum, mul_nonneg ha.le (sub_nonneg.mpr hyim),
        mul_nonneg hb.le (sub_nonneg.mpr hzim)]
    have hyim' : y.im = p.im := by rcases mul_eq_zero.mp hyim0 with h|h <;> nlinarith
    exact Complex.ext hyre' hyim'
  · intro y hy; rw [hp.2]; exact hmax hy

private theorem exists_nearby_openSegment_point {a b p : Tiling.Plane} (hab : a ≠ b)
    (hp : p ∈ openSegment ℝ a b) {r : ℝ} (hr : 0 < r) :
    ∃ q ∈ openSegment ℝ a b, q ≠ p ∧ q ∈ Metric.ball p r := by
  rw [openSegment_eq_image_lineMap] at hp
  obtain ⟨θ,hθ,rfl⟩ := hp
  let δ := min ((1-θ)/2) (r/(2*dist a b))
  have hd : 0 < δ :=
    lt_min (half_pos (sub_pos.mpr hθ.2))
      (div_pos hr (mul_pos zero_lt_two (dist_pos.mpr hab)))
  have hθδ : θ+δ ∈ Ioo (0:ℝ) 1 := by
    constructor
    · linarith [hθ.1, hd]
    · have := min_le_left ((1-θ)/2) (r/(2*dist a b)); linarith
  refine ⟨AffineMap.lineMap a b (θ+δ), lineMap_mem_openSegment ℝ a b hθδ, ?_, ?_⟩
  · intro heq; have := AffineMap.lineMap_injective ℝ hab heq; linarith
  · rw [Metric.mem_ball, dist_eq_norm]
    have hdif : AffineMap.lineMap a b (θ+δ)-AffineMap.lineMap a b θ = δ • (b-a) := by
      rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]; module
    rw [hdif, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    have hn : ‖b-a‖ = dist a b := by
      rw [dist_eq_norm]
      simpa only [norm_neg] using congrArg norm (by abel : b-a = -(a-b))
    rw [hn]
    calc
      δ*dist a b ≤ (r/(2*dist a b))*dist a b :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (dist_pos.mpr hab).le
      _ = r/2 := by field_simp [ne_of_gt (dist_pos.mpr hab)]
      _ < r := half_lt_self hr

private theorem frontier_support_eq_open (K : Region) :
    frontier K.openCarrier = frontier K.support := by
  exact K.frontier_openCarrier_eq_frontier_support

private theorem re_eq_of_mem_openSegment_vertical {a b p : Tiling.Plane}
    (hab : a.re = b.re) (hp : p ∈ openSegment ℝ a b) : p.re = a.re := by
  rw [openSegment_eq_image] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [hab]
  ring

private theorem germ_of_vertical_edge {K : Region} {v p w : Tiling.Plane}
    (hp : p ∈ frontier K.support) (hpnv : p ∉ Tiling.vertexSet K.support)
    (hpw : p ∈ openSegment ℝ v w) (hvert : v.re = w.re) (hvw : v ≠ w) :
    (openSegment ℝ v w ⊆ frontier K.support) →
    Tiling.BoundaryLocallyStraightAt K.openCarrier p ∧
      (∀ᶠ z in nhds p, z ∈ frontier K.support ↔ z.re = p.re) := by
  intro hedge
  have hstraight' := K.isPolygonal.boundaryLocallyStraightAt_of_not_mem_vertexSet hp hpnv
  obtain ⟨L,hpL,hLdim,hlocal⟩ := hstraight'
  have hstraightFinal : Tiling.BoundaryLocallyStraightAt K.openCarrier p := by
    refine ⟨L, hpL, hLdim, ?_⟩
    filter_upwards [hlocal] with z hz
    simpa only [frontier_support_eq_open K] using hz
  obtain ⟨d,hd,hLline⟩ := Tiling.AffineSubspace.exists_affineLine_eq hpL hLdim
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (by simpa [hLline] using hlocal)
  obtain ⟨q,hqseg,hqp,hqball⟩ := exists_nearby_openSegment_point
    hvw hpw hr
  have hqfront : q ∈ frontier K.support := hedge hqseg
  have hqre : q.re = p.re := (re_eq_of_mem_openSegment_vertical hvert hqseg).trans
    (re_eq_of_mem_openSegment_vertical hvert hpw).symm
  have hqL : q ∈ L := by
    change q ∈ (L : Set Tiling.Plane)
    rw [hLline]
    exact (mem_affineLine.mpr ((hball hqball).mp hqfront))
  have hqLine : q ∈ affineLine p d := by rw [← hLline]; exact hqL
  obtain ⟨t, ht⟩ := (mem_affineLine_iff_exists_smul hd).mp hqLine
  have htne : t ≠ 0 := by
    intro ht0
    apply hqp
    simpa [ht0] using ht
  have hdre : d.re = 0 := by
    have := congrArg Complex.re ht
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at this
    rw [hqre] at this
    exact (mul_eq_zero.mp (by linarith : t * d.re = 0)).resolve_left htne
  have hdim : d.im ≠ 0 := by
    intro him
    apply hd
    apply Complex.ext
    · simp [hdre]
    · simp [him]
  refine ⟨hstraightFinal, ?_⟩
  filter_upwards [Metric.ball_mem_nhds p hr] with z hz
  rw [hball hz]
  rw [← mem_affineLine]
  rw [mem_affineLine_iff_exists_smul hd]
  constructor
  · rintro ⟨s, rfl⟩
    simp [hdre]
  · intro hzre
    refine ⟨(z.im - p.im) / d.im, ?_⟩
    apply Complex.ext
    · simpa [Complex.add_re, Complex.smul_re, smul_eq_mul, hdre] using hzre
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      field_simp [hdim]
      ring

private theorem lowerExtremalIntrinsicVerticalEdge :
    ∀ K : Region, ∃ (v w : ↥K.vertices) (p : Tiling.Plane),
      (∀ z ∈ K.support, v.1.re ≤ z.re) ∧ w.1 ≠ v.1 ∧ w.1.re = v.1.re ∧
      p ∈ openSegment ℝ v.1 w.1 ∧ p ∉ K.vertices ∧
      openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices ∧
      Tiling.BoundaryLocallyStraightAt K.openCarrier p ∧
      (∀ᶠ z in nhds p, z ∈ frontier K.support ↔ z.re = p.re) :=by
  intro K
  obtain ⟨x,hxext,hxmin⟩ := exists_extremePoint_isMin_re K.isPolygonal.isCompact K.nonempty
  let v : ↥K.vertices := ⟨x, extremePoint_mem_vertexSet hxext⟩
  obtain ⟨w,hne,htrans,hedge⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.intrinsicVertex_incident_axisEdge
      K .vertical v
  have hvert : w.1.re = v.1.re := htrans
  let p : Tiling.Plane := AffineMap.lineMap v.1 w.1 (1 / 2 : ℝ)
  have hpseg : p ∈ openSegment ℝ v.1 w.1 := by
    dsimp [p]
    exact lineMap_mem_openSegment ℝ v.1 w.1 ⟨by norm_num, by norm_num⟩
  have hpfront : p ∈ frontier K.support := (hedge hpseg).1
  have hpnv : p ∉ Tiling.vertexSet K.support := by
    simpa only [K.vertices_eq_vertexSet] using (hedge hpseg).2
  have hmin : ∀ z ∈ K.support, v.1.re ≤ z.re := by
    intro z hz
    exact hxmin z hz
  obtain ⟨hstraight,hgerm⟩ := germ_of_vertical_edge hpfront hpnv hpseg hvert.symm hne.symm
    (fun z hz => (hedge hz).1)
  refine ⟨v,w,p,hmin,hne,hvert,hpseg,hpnv,?_,hstraight,hgerm⟩
  exact hedge


private theorem upperExtremalIntrinsicVerticalEdge :
    ∀ K : Region, ∃ (v w : ↥K.vertices) (p : Tiling.Plane),
      (∀ z ∈ K.support, z.re ≤ v.1.re) ∧ w.1 ≠ v.1 ∧ w.1.re = v.1.re ∧
      p ∈ openSegment ℝ v.1 w.1 ∧ p ∉ K.vertices ∧
      openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices ∧
      Tiling.BoundaryLocallyStraightAt K.openCarrier p ∧
      (∀ᶠ z in nhds p, z ∈ frontier K.support ↔ z.re = p.re) :=by
  intro K
  obtain ⟨x,hxext,hxmax⟩ := exists_extremePoint_isMax_re K.isPolygonal.isCompact K.nonempty
  let v : ↥K.vertices := ⟨x, extremePoint_mem_vertexSet hxext⟩
  obtain ⟨w,hne,htrans,hedge⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.intrinsicVertex_incident_axisEdge
      K .vertical v
  have hvert : w.1.re = v.1.re := htrans
  let p : Tiling.Plane := AffineMap.lineMap v.1 w.1 (1 / 2 : ℝ)
  have hpseg : p ∈ openSegment ℝ v.1 w.1 := by
    dsimp [p]
    exact lineMap_mem_openSegment ℝ v.1 w.1 ⟨by norm_num, by norm_num⟩
  have hpfront : p ∈ frontier K.support := (hedge hpseg).1
  have hpnv : p ∉ Tiling.vertexSet K.support := by
    simpa only [K.vertices_eq_vertexSet] using (hedge hpseg).2
  have hmax : ∀ z ∈ K.support, z.re ≤ v.1.re := by
    intro z hz
    exact hxmax z hz
  obtain ⟨hstraight,hgerm⟩ := germ_of_vertical_edge hpfront hpnv hpseg hvert.symm hne.symm
    (fun z hz => (hedge hz).1)
  refine ⟨v,w,p,hmax,hne,hvert,hpseg,hpnv,?_,hstraight,hgerm⟩
  exact hedge


private def verticalSlice (K : Region) (r : ℝ) : Set ℝ :=
  {y : ℝ | (r : ℂ) + (y : ℂ) * Complex.I ∈ K.openCarrier}

private theorem genericSliceMass_eq_of_columnLimits :
    ∀ (K : Region) (Kₙ : ℕ → Region) (Cₙ : ℕ → Set Tiling.Plane)
      (r s : ℝ) (rₙ sₙ : ℕ → ℝ),
    (∀ n, IsCenterColumn Axis.vertical (Kₙ n) (Cₙ n)) →
    (∀ n, rₙ n ∉ (Kₙ n).vertexFinset.image Complex.re) →
    (∀ n, sₙ n ∉ (Kₙ n).vertexFinset.image Complex.re) →
    (∀ n, (verticalSlice (Kₙ n) (rₙ n)).Nonempty) →
    (∀ n, (verticalSlice (Kₙ n) (sₙ n)).Nonempty) →
    Tendsto (fun n ↦ (volume (verticalSlice (Kₙ n) (rₙ n))).toReal)
      atTop (nhds (volume (verticalSlice K r)).toReal) →
    Tendsto (fun n ↦ (volume (verticalSlice (Kₙ n) (sₙ n))).toReal)
      atTop (nhds (volume (verticalSlice K s)).toReal) →
    (volume (verticalSlice K r)).toReal = (volume (verticalSlice K s)).toReal :=by
  intro K Kₙ Cₙ r s rₙ sₙ hColumn hr hs hnonemptyR hnonemptyS hlimR hlimS
  have hEq : ∀ n : ℕ,
      (volume (verticalSlice (Kₙ n) (rₙ n))).toReal =
        (volume (verticalSlice (Kₙ n) (sₙ n))).toReal := by
    intro n
    have h := Tiling.AxisParallel.Foundations.centerColumn_genericSlice_measure_eq
      (hColumn n) (hr n) (hs n) (hnonemptyR n) (hnonemptyS n)
    simpa only [verticalSlice,
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice] using h
  have hlimS' : Tendsto
      (fun n ↦ (volume (verticalSlice (Kₙ n) (sₙ n))).toReal)
      atTop (nhds (volume (verticalSlice K r)).toReal) := by
    exact hlimR.congr' (Eventually.of_forall fun n ↦ hEq n)
  exact tendsto_nhds_unique hlimS' hlimS

/-! The public disjunction theorem is only logical assembly once the two
orientation-specific S02 theorems are available. -/
/-! C01 minimality identifies any complete centre-column subfamily contained
in a vertical plate with that plate.  The support witness is supplied by the
regular-support formula for a complete column. -/

private theorem verticalPlate_eq_of_centerColumnSubfamily :
    ∀ {K : Region} {T C : Set Tiling.Plane}, TilesOn K T Set.univ →
    ∀ P : Continuous.VerticalPlate K T,
      C ⊆ P.centres → IsCenterColumn Axis.vertical K C → C = P.centres :=by
  intro K T C hTile P hCP hCcolumn
  rcases Tiling.AxisParallel.Continuous.VerticalPlate.minimal hTile P with
    ⟨_, hPsub, _, hPminimal⟩
  apply hPminimal C hCcolumn.2.1 hCP
  obtain ⟨c, _hCnonempty, _hcoord, hSupport⟩ :=
    Tiling.AxisParallel.centerColumn_regularSupport hCcolumn
  let X : Set ℝ :=
    interior (closure (c +ᵥ (Complex.re '' K.openCarrier)))
  refine ⟨X, ?_, ?_⟩
  · dsimp only [X]
    exact interior_closure_idem.symm
  · rw [hSupport]
    ext z
    rfl


open Tiling.AxisParallel.Approximation

open Tiling.AxisParallel.Foundations.GenericSlices



open Tiling
open Tiling.AxisParallel

private theorem verticalPlate_isCenterColumn
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : Continuous.VerticalPlate K T)
    (hcolumn : Continuous.IsVerticalColumn P) :
    IsCenterColumn Axis.vertical K P.centres := by
  exact Continuous.VerticalPlate.isCenterColumn_of_isVerticalColumn hTile P hcolumn

private theorem singleAxis_saturatedColumnUnion_isCenterColumn
    {K : Region} {T S : Set Tiling.Plane} {a : ℝ}
    (hTile : TilesOn K T Set.univ) (hSsub : S ⊆ T) (hSne : S.Nonempty)
    (hSaxis : ∀ z ∈ S, z.re = a)
    (hplates : ∀ Q : Continuous.VerticalPlate K T,
      (Q.centres ∩ S).Nonempty →
        Q.centres ⊆ S ∧ Continuous.IsVerticalColumn Q) :
    IsCenterColumn Axis.vertical K S := by
  have hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) := by
    intro p hp q hq hpq
    exact hTile.2.1 (hSsub hp) (hSsub hq) hpq
  have hcentre : ∀ t : ↥T,
      (t : Tiling.Plane) ∈
        (Continuous.VerticalPlate.ofCentre (K := K) t).centres := by
    intro t
    refine ⟨t, ?_, rfl⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 rfl
  obtain ⟨s, hs⟩ := hSne
  let t₀ : ↥T := ⟨s, hSsub hs⟩
  let P : Continuous.VerticalPlate K T := Continuous.VerticalPlate.ofCentre t₀
  have hsP : s ∈ P.centres := by
    exact hcentre t₀
  have hPmeet : (P.centres ∩ S).Nonempty := ⟨s, hsP, hs⟩
  obtain ⟨hPsub, hPcolumn⟩ := hplates P hPmeet
  have hPaxis : P.centres ⊆ {z : Tiling.Plane | z.re = a} := by
    intro z hz
    exact hSaxis z (hPsub hz)
  let A : ↥S → Set Tiling.Plane := fun u ↦
    (Continuous.VerticalPlate.ofCentre (K := K)
      (⟨u.1, hSsub u.2⟩ : ↥T)).centres
  have hAeq : (⋃ u : ↥S, A u) = S := by
    ext z
    constructor
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨u, hz⟩ := hz
      exact (hplates
        (Continuous.VerticalPlate.ofCentre (K := K)
          (⟨u.1, hSsub u.2⟩ : ↥T))
        ⟨u.1, hcentre _, u.2⟩).1 hz
    · intro hz
      rw [Set.mem_iUnion]
      refine ⟨⟨z, hz⟩, ?_⟩
      exact hcentre ⟨z, hSsub (by exact hz)⟩
  have hAreg (u : ↥S) : regularSupport K (A u) = P.support := by
    let Q : Continuous.VerticalPlate K T :=
      Continuous.VerticalPlate.ofCentre (K := K)
        (⟨u.1, hSsub u.2⟩ : ↥T)
    have hQmeet : (Q.centres ∩ S).Nonempty := by
      refine ⟨u.1, hcentre _, u.2⟩
    obtain ⟨hQsub, hQcolumn⟩ := hplates Q hQmeet
    have hQaxis : Q.centres ⊆ {z : Tiling.Plane | z.re = a} := by
      intro z hz
      exact hSaxis z (hQsub hz)
    have hQsupport :=
      Continuous.verticalColumn_regularSupport hTile Q hQcolumn hQaxis
    have hPsupport' :=
      Continuous.verticalColumn_regularSupport hTile P hPcolumn hPaxis
    change regularSupport K Q.centres = P.support
    rw [← Continuous.VerticalPlate.support_eq_regularSupport]
    rw [hQsupport.2, hPsupport'.2]
    rw [hQsupport.1, hPsupport'.1]
  have hPsupport : regularSupport K S = P.support := by
    rw [← hAeq, regularSupport_iUnion]
    have hUnion : (⋃ u : ↥S, regularSupport K (A u)) = P.support := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_iUnion] at hz
        obtain ⟨u, hz⟩ := hz
        rw [hAreg u] at hz
        exact hz
      · intro hz
        rw [Set.mem_iUnion]
        refine ⟨⟨s, hs⟩, ?_⟩
        rw [hAreg ⟨s, hs⟩]
        exact hz
    rw [hUnion]
    rw [P.support_eq_regularSupport]
    exact (regularSupport_isRegularOpen K P.centres).2
  refine ⟨hpack, ⟨s, hs⟩, ⟨a, ?_⟩, ?_⟩
  · exact hSaxis
  · intro b
    rw [hPsupport]
    obtain ⟨hbase, hsupport⟩ :=
      Continuous.verticalColumn_regularSupport hTile P hPcolumn hPaxis
    rw [hsupport]
    ext z
    simp only [Set.mem_vadd_set, Set.mem_preimage]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hz
      refine ⟨z - (b : Tiling.Plane) * Complex.I, ?_, ?_⟩
      · simpa using hz
      · simp [vadd_eq_add]



private abbrev VerticalSlicePresentationConstructor :=
  ∀ (K : Region) {x : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
      Nonempty (VerticalGenericSlicePresentation K x)

private def presentationLowerCoord
    {C : ApproximationContext} {x : ℝ}
    (S : VerticalGenericSlicePresentation C.region x) (i : Fin S.n) : C.coordinateSpace :=
  ⟨S.left i, by
    rw [← S.lowerVertex_coord i]
    exact C.vertex_im_mem (S.lowerVertex i).1 (S.lowerVertex i).2⟩

private def presentationUpperCoord
    {C : ApproximationContext} {x : ℝ}
    (S : VerticalGenericSlicePresentation C.region x) (i : Fin S.n) : C.coordinateSpace :=
  ⟨S.right i, by
    rw [← S.upperVertex_coord i]
    exact C.vertex_im_mem (S.upperVertex i).1 (S.upperVertex i).2⟩

private def mappedPresentationMass
    {C : ApproximationContext} {x : ℝ}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (S : VerticalGenericSlicePresentation C.region x) : ℝ :=
  ∑ i, (mapScalar phi (presentationUpperCoord S i) -
    mapScalar phi (presentationLowerCoord S i))

private theorem verticalSliceIntrinsicPresentation_exists
    (presentation : VerticalSlicePresentationConstructor)
    (K : Region) {x : ℝ}
    (hx : x ∉ K.vertexFinset.image Complex.re) :
    Nonempty (VerticalGenericSlicePresentation K x) := by
  exact presentation K hx

private theorem deformedVerticalSlice_eq_mappedPresentation
    {C : ApproximationContext} {x : ℝ}
    (S : VerticalGenericSlicePresentation C.region x)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) :
    verticalSlice D.deformedRegion (D.firstHomeomorph x) =
      ⋃ i : Fin S.n,
        Ioo (mapScalar phi (presentationLowerCoord S i))
          (mapScalar phi (presentationUpperCoord S i)) := by
  have hslice : verticalSlice D.deformedRegion (D.firstHomeomorph x) =
      D.secondHomeomorph '' verticalSlice C.region x := by
    ext y
    constructor
    · intro hy
      rw [verticalSlice, D.deformedRegion_openCarrier] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have hzre : z.re = x := by
        have h := congrArg Complex.re hzy
        rw [D.planarHomeomorph_apply] at h
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at h
        apply D.firstHomeomorph.injective
        simpa using h
      have hzim : D.secondHomeomorph z.im = y := by
        have h := congrArg Complex.im hzy
        rw [D.planarHomeomorph_apply] at h
        simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, sub_zero,
          add_zero, zero_add, mul_one] using h
      refine ⟨z.im, ?_, hzim⟩
      change (x : ℂ) + (z.im : ℂ) * Complex.I ∈ C.region.openCarrier
      rw [← hzre]
      simpa using hz
    · rintro ⟨z, hz, rfl⟩
      rw [verticalSlice, D.deformedRegion_openCarrier]
      refine ⟨(x : ℂ) + (z : ℂ) * Complex.I, ?_, ?_⟩
      · change (x : ℂ) + (z : ℂ) * Complex.I ∈ C.region.openCarrier at hz
        exact hz
      · rw [D.planarHomeomorph_apply]
        apply Complex.ext <;> simp
  rw [hslice]
  calc
    D.secondHomeomorph '' verticalSlice C.region x =
        D.secondHomeomorph '' (⋃ i : Fin S.n, Ioo (S.left i) (S.right i)) :=
      congrArg (fun U : Set ℝ => D.secondHomeomorph '' U) (by
        have hrepr (y : ℝ) :
            (x : ℂ) + (y : ℂ) * Complex.I = Complex.mk x y := by
          apply Complex.ext <;> simp
        have heq : verticalSlice C.region x =
            Foundations.GenericSlices.verticalSlice C.region x := by
          ext y
          change ((x : ℂ) + (y : ℂ) * Complex.I ∈ C.region.openCarrier) ↔
            (Complex.mk x y ∈ C.region.openCarrier)
          rw [hrepr]
        rw [heq]
        exact S.union_eq)
    _ = ⋃ i : Fin S.n, D.secondHomeomorph '' Ioo (S.left i) (S.right i) := by
      rw [Set.image_iUnion]
    _ = ⋃ i : Fin S.n,
        Ioo (mapScalar phi (presentationLowerCoord S i))
          (mapScalar phi (presentationUpperCoord S i)) := by
      apply iUnion_congr
      intro i
      rw [D.secondHomeomorph.continuous.image_Ioo_of_strictMono
        D.secondHomeomorph_strictMono]
      have hlow : D.secondHomeomorph (S.left i) =
          mapScalar phi (presentationLowerCoord S i) := by
        have hv := D.vertex_agreement (S.lowerVertex i).1 (S.lowerVertex i).2
        rw [D.planarHomeomorph_apply] at hv
        have him := congrArg Complex.im hv
        have hleft : S.left i = (S.lowerVertex i).1.im :=
          (S.lowerVertex_coord i).symm
        have hcoord : presentationLowerCoord S i =
            ⟨(S.lowerVertex i).1.im, C.vertex_im_mem (S.lowerVertex i).1
              (S.lowerVertex i).2⟩ := by
          apply Subtype.ext
          exact (S.lowerVertex_coord i).symm
        rw [hleft, hcoord]
        simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using him
      have hupp : D.secondHomeomorph (S.right i) =
          mapScalar phi (presentationUpperCoord S i) := by
        have hv := D.vertex_agreement (S.upperVertex i).1 (S.upperVertex i).2
        rw [D.planarHomeomorph_apply] at hv
        have him := congrArg Complex.im hv
        have hright : S.right i = (S.upperVertex i).1.im :=
          (S.upperVertex_coord i).symm
        have hcoord : presentationUpperCoord S i =
            ⟨(S.upperVertex i).1.im, C.vertex_im_mem (S.upperVertex i).1
              (S.upperVertex i).2⟩ := by
          apply Subtype.ext
          exact (S.upperVertex_coord i).symm
        rw [hright, hcoord]
        simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using him
      rw [hlow, hupp]

private theorem deformedVerticalSlice_mass_eq_finiteSum
    {C : ApproximationContext} {x : ℝ}
    (S : VerticalGenericSlicePresentation C.region x)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) :
    (volume (verticalSlice D.deformedRegion (D.firstHomeomorph x))).toReal =
      mappedPresentationMass phi S := by
  rw [deformedVerticalSlice_eq_mappedPresentation S D]
  let f : Fin S.n → Set ℝ := fun i ↦
    Ioo (mapScalar phi (presentationLowerCoord S i))
      (mapScalar phi (presentationUpperCoord S i))
  have hlow (i : Fin S.n) :
      D.secondHomeomorph (S.left i) =
        mapScalar phi (presentationLowerCoord S i) := by
    have hv := D.vertex_agreement (S.lowerVertex i).1 (S.lowerVertex i).2
    rw [D.planarHomeomorph_apply] at hv
    have him := congrArg Complex.im hv
    have hleft : S.left i = (S.lowerVertex i).1.im :=
      (S.lowerVertex_coord i).symm
    have hcoord : presentationLowerCoord S i =
        ⟨(S.lowerVertex i).1.im, C.vertex_im_mem (S.lowerVertex i).1
          (S.lowerVertex i).2⟩ := by
      apply Subtype.ext
      exact (S.lowerVertex_coord i).symm
    rw [hleft, hcoord]
    simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using him
  have hupp (i : Fin S.n) :
      D.secondHomeomorph (S.right i) =
        mapScalar phi (presentationUpperCoord S i) := by
    have hv := D.vertex_agreement (S.upperVertex i).1 (S.upperVertex i).2
    rw [D.planarHomeomorph_apply] at hv
    have him := congrArg Complex.im hv
    have hright : S.right i = (S.upperVertex i).1.im :=
      (S.upperVertex_coord i).symm
    have hcoord : presentationUpperCoord S i =
        ⟨(S.upperVertex i).1.im, C.vertex_im_mem (S.upperVertex i).1
          (S.upperVertex i).2⟩ := by
      apply Subtype.ext
      exact (S.upperVertex_coord i).symm
    rw [hright, hcoord]
    simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using him
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro i j hij
    rcases S.pairwise_gap i j hij with hgap | hgap
    · have hlow (k : Fin S.n) :
          D.secondHomeomorph (S.left k) =
            mapScalar phi (presentationLowerCoord S k) := hlow k
      have hgap' :
          mapScalar phi (presentationUpperCoord S i) <
            mapScalar phi (presentationLowerCoord S j) := by
        calc
          mapScalar phi (presentationUpperCoord S i) =
              D.secondHomeomorph (S.right i) := (hupp i).symm
          _ < D.secondHomeomorph (S.left j) :=
            D.secondHomeomorph_strictMono hgap
          _ = mapScalar phi (presentationLowerCoord S j) := hlow j
      apply Set.disjoint_left.2
      intro y hyi hyj
      change y ∈ Ioo (mapScalar phi (presentationLowerCoord S i))
          (mapScalar phi (presentationUpperCoord S i)) at hyi
      change y ∈ Ioo (mapScalar phi (presentationLowerCoord S j))
          (mapScalar phi (presentationUpperCoord S j)) at hyj
      rcases hyi with ⟨hyiL, hyiU⟩
      rcases hyj with ⟨hyjL, hyjU⟩
      linarith
    · have hgap' :
          mapScalar phi (presentationUpperCoord S j) <
            mapScalar phi (presentationLowerCoord S i) := by
        calc
          mapScalar phi (presentationUpperCoord S j) =
              D.secondHomeomorph (S.right j) := (hupp j).symm
          _ < D.secondHomeomorph (S.left i) :=
            D.secondHomeomorph_strictMono hgap
          _ = mapScalar phi (presentationLowerCoord S i) := hlow i
      apply Set.disjoint_left.2
      intro y hyi hyj
      change y ∈ Ioo (mapScalar phi (presentationLowerCoord S i))
          (mapScalar phi (presentationUpperCoord S i)) at hyi
      change y ∈ Ioo (mapScalar phi (presentationLowerCoord S j))
          (mapScalar phi (presentationUpperCoord S j)) at hyj
      rcases hyi with ⟨hyiL, hyiU⟩
      rcases hyj with ⟨hyjL, hyjU⟩
      linarith
  have hmeas : ∀ i, MeasurableSet (f i) := by
    intro i
    exact (isOpen_Ioo.measurableSet)
  rw [measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [f, Real.volume_Ioo]
  have hsum := ENNReal.toReal_sum
    (s := Finset.univ)
    (f := fun i : Fin S.n ↦
      ENNReal.ofReal
        (mapScalar phi (presentationUpperCoord S i) -
          mapScalar phi (presentationLowerCoord S i))) (by
      intro i hi
      exact ENNReal.ofReal_ne_top)
  have hnonneg (i : Fin S.n) :
      0 ≤ mapScalar phi (presentationUpperCoord S i) -
        mapScalar phi (presentationLowerCoord S i) := by
    have hlt : mapScalar phi (presentationLowerCoord S i) <
        mapScalar phi (presentationUpperCoord S i) := by
      calc
        mapScalar phi (presentationLowerCoord S i) =
            D.secondHomeomorph (S.left i) := (hlow i).symm
        _ < D.secondHomeomorph (S.right i) :=
          D.secondHomeomorph_strictMono (S.lt i)
        _ = mapScalar phi (presentationUpperCoord S i) := hupp i
    linarith
  simpa [mappedPresentationMass, ENNReal.toReal_ofReal, hnonneg] using hsum

private theorem deformedVerticalSlice_mass_tendsto
    {C : ApproximationContext} {x : ℝ}
    (S : VerticalGenericSlicePresentation C.region x)
    (phi : ℕ → C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : ∀ n : ℕ, CoordinateDeformation C (phi n))
    (hphi : ∀ z : C.coordinateSpace,
      Tendsto (fun n ↦ mapScalar (phi n) z) atTop (nhds (z : ℝ))) :
      Tendsto
      (fun n ↦ (volume
        (verticalSlice (D n).deformedRegion ((D n).firstHomeomorph x))).toReal)
      atTop (nhds (volume (verticalSlice C.region x)).toReal) := by
  have hmass : ∀ n : ℕ,
      (volume (verticalSlice (D n).deformedRegion
        ((D n).firstHomeomorph x))).toReal = mappedPresentationMass (phi n) S := by
    intro n
    exact deformedVerticalSlice_mass_eq_finiteSum S (D n)
  have hsourceDisj :
      Pairwise (Function.onFun Disjoint (fun i : Fin S.n ↦ Ioo (S.left i) (S.right i))) := by
    intro i j hij
    rcases S.pairwise_gap i j hij with hgap | hgap
    · apply Set.disjoint_left.2
      intro y hyi hyj
      rcases hyi with ⟨hyiL, hyiU⟩
      rcases hyj with ⟨hyjL, hyjU⟩
      linarith
    · apply Set.disjoint_left.2
      intro y hyi hyj
      rcases hyi with ⟨hyiL, hyiU⟩
      rcases hyj with ⟨hyjL, hyjU⟩
      linarith
  have hsourceMeas : ∀ i : Fin S.n,
      MeasurableSet (Ioo (S.left i) (S.right i)) := by
    intro i
    exact isOpen_Ioo.measurableSet
  have heqSource : verticalSlice C.region x =
      ⋃ i : Fin S.n, Ioo (S.left i) (S.right i) := by
    have hrepr (y : ℝ) :
        (x : ℂ) + (y : ℂ) * Complex.I = Complex.mk x y := by
      apply Complex.ext <;> simp
    have heq : verticalSlice C.region x =
        Foundations.GenericSlices.verticalSlice C.region x := by
      ext y
      change ((x : ℂ) + (y : ℂ) * Complex.I ∈ C.region.openCarrier) ↔
        (Complex.mk x y ∈ C.region.openCarrier)
      rw [hrepr]
    rw [heq]
    exact S.union_eq
  have hsourceMass :
      (volume (verticalSlice C.region x)).toReal =
        ∑ i : Fin S.n, (S.right i - S.left i) := by
    rw [heqSource, measure_iUnion hsourceDisj hsourceMeas, tsum_fintype]
    simp only [Real.volume_Ioo]
    have hsum := ENNReal.toReal_sum
      (s := Finset.univ)
      (f := fun i : Fin S.n ↦ ENNReal.ofReal (S.right i - S.left i)) (by
        intro i hi
        exact ENNReal.ofReal_ne_top)
    have hnonneg : ∀ i : Fin S.n, 0 ≤ S.right i - S.left i := by
      intro i
      linarith [S.lt i]
    simpa [ENNReal.toReal_ofReal, hnonneg] using hsum
  have hterm : ∀ i : Fin S.n,
      Tendsto
        (fun n ↦ mapScalar (phi n) (presentationUpperCoord S i) -
          mapScalar (phi n) (presentationLowerCoord S i))
        atTop
        (nhds ((presentationUpperCoord S i : ℝ) -
          (presentationLowerCoord S i : ℝ))) := by
    intro i
    exact (hphi (presentationUpperCoord S i)).sub
      (hphi (presentationLowerCoord S i))
  have hsumlim : Tendsto
      (fun n ↦ mappedPresentationMass (phi n) S)
      atTop
      (nhds (∑ i : Fin S.n,
        ((presentationUpperCoord S i : ℝ) -
          (presentationLowerCoord S i : ℝ)))) := by
    simpa [mappedPresentationMass] using
      (tendsto_finsetSum (s := Finset.univ)
        (fun i _hi ↦ hterm i))
  have hsourceEndpoints :
      (∑ i : Fin S.n,
        ((presentationUpperCoord S i : ℝ) -
          (presentationLowerCoord S i : ℝ))) =
        ∑ i : Fin S.n, (S.right i - S.left i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  rw [hsourceMass, ← hsourceEndpoints]
  apply hsumlim.congr'
  exact Filter.Eventually.of_forall (fun n ↦ (hmass n).symm)



private theorem frontier_regularSupport_subset_tileFrontiers
    {K : Region} {T S : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (hST : S ⊆ T) :
    frontier (regularSupport K S) ⊆
      ⋃ s : ↥S, frontier ((s.1 : Tiling.Plane) +ᵥ K.support) := by
  have hpackingS : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K S).mpr
    intro s hs t ht hst
    exact (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp
      hTile.2.1 (hST hs) (hST ht) hst
  intro p hp
  have hpclosure : p ∈ closure (openUnion K S) := by
    have hp' := frontier_interior_subset hp
    simpa only [closure_closure] using frontier_subset_closure hp'
  rw [closure_openUnion_eq_iUnion_support hpackingS] at hpclosure
  obtain ⟨s, hps⟩ := Set.mem_iUnion.mp hpclosure
  apply Set.mem_iUnion_of_mem s
  rw [frontier, (K.isPolygonal.vadd s.1).isClosed.closure_eq]
  refine ⟨hps, ?_⟩
  intro hpint
  have hpreg : p ∈ regularSupport K S := by
    apply interior_mono ?_ hpint
    rw [closure_openUnion_eq_iUnion_support hpackingS]
    exact subset_iUnion (fun q : ↥S ↦ (q.1 : Tiling.Plane) +ᵥ K.support) s
  rw [frontier] at hp
  apply hp.2
  change p ∈ interior (interior (closure (openUnion K S)))
  simpa only [regularSupport, Tiling.Polygonal.regularSupport,
    ← openUnion.eq_def, interior_interior] using hpreg



private theorem lowerExtremalBoundaryLine :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ (P : Continuous.VerticalPlate K T) (a : ℝ),
        IsLeast (Complex.re '' P.centres) a → BddBelow P.base →
        ∃ v : ↥K.vertices,
          (∀ w ∈ K.support, v.1.re ≤ w.re) ∧
          v.1.re + a ∈ frontier P.base ∧
          {z : Tiling.Plane | z.re = v.1.re + a} ⊆
            ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
  intro K T hTile P a ha hbelow
  obtain ⟨x, hxext, hx⟩ :=
    exists_extremePoint_isMin_re K.isPolygonal.isCompact K.nonempty
  let v : ↥K.vertices := ⟨x, extremePoint_mem_vertexSet hxext⟩
  have hv : ∀ z ∈ K.support, v.1.re ≤ z.re := by
    intro z hz
    exact hx z hz
  have hST : P.centres ⊆ T := by
    rintro _ ⟨t, ht, rfl⟩
    exact t.2
  have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P.centres) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K P.centres).mpr
    intro s hs t ht hst
    exact (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp
      hTile.2.1 (hST hs) (hST ht) hst
  have hsuppLower : ∀ z ∈ P.support, v.1.re + a ≤ z.re := by
    intro z hz
    rw [P.support_eq_regularSupport, regularSupport] at hz
    have hzcl : z ∈ closure (openUnion K P.centres) := interior_subset hz
    rw [closure_openUnion_eq_iUnion_support hpacking] at hzcl
    obtain ⟨s, hzs⟩ := Set.mem_iUnion.mp hzcl
    rw [mem_vadd_set] at hzs
    obtain ⟨u, hu, rfl⟩ := hzs
    have haS : a ≤ s.1.re := ha.2 ⟨s.1, s.2, rfl⟩
    have hvU := hv u hu
    simp only [vadd_eq_add, Complex.add_re] at *
    linarith
  obtain ⟨t, htP, htRe⟩ := ha.1
  have htvcl : t +ᵥ v.1 ∈ closure (openUnion K P.centres) := by
    rw [closure_openUnion_eq_iUnion_support hpacking]
    apply Set.mem_iUnion_of_mem ⟨t, htP⟩
    rw [mem_vadd_set]
    have hvSupport : v.1 ∈ K.support := by
      have h := frontier_subset_closure
        (Tiling.AxisParallel.IntrinsicVertices.region_vertices_subset_frontier K v.2)
      change v.1 ∈ closure (interior K.support) at h
      rw [K.isPolygonal.closure_interior] at h
      exact h
    exact ⟨v.1, hvSupport, rfl⟩
  have hopenSub : openUnion K P.centres ⊆ P.support := by
    rw [P.support_eq_regularSupport, regularSupport]
    exact (isOpen_iUnion fun s : P.centres ↦ isOpen_interior.vadd s.1).subset_interior_closure
  have htvSupport : t +ᵥ v.1 ∈ closure P.support :=
    closure_mono hopenSub htvcl
  have hclosure : closure P.support = Complex.re ⁻¹' closure P.base := by
    rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2,
      Complex.closure_preimage_re]
  have hccl : v.1.re + a ∈ closure P.base := by
    have h := hclosure ▸ htvSupport
    change (t +ᵥ v.1).re ∈ closure P.base at h
    simpa [vadd_eq_add, Complex.add_re, htRe, add_comm] using h
  have hcnot : v.1.re + a ∉ P.base := by
    intro hc
    have hopen : IsOpen P.base := by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).1]
      exact isOpen_interior
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hc)
    let q : ℝ := v.1.re + a - r / 2
    have hq : q ∈ P.base := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [q]
      rw [show (v.1.re + a - r / 2 - (v.1.re + a)) = -(r / 2) by ring,
        abs_neg, abs_of_pos (half_pos hr)]
      linarith)
    have hqSupport : (q : ℂ) ∈ P.support := by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2]
      exact hq
    have hqLower := hsuppLower (q : ℂ) hqSupport
    dsimp [q] at hqLower
    linarith
  have hcfront : v.1.re + a ∈ frontier P.base := by
    rw [frontier]
    refine ⟨hccl, ?_⟩
    intro hcint
    exact hcnot (interior_subset hcint)
  refine ⟨v, hv, hcfront, ?_⟩
  intro z hz
  have hzP : z ∈ frontier P.support := by
    rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2]
    change z ∈ frontier ({w : Tiling.Plane | w.re ∈ P.base} : Set Tiling.Plane)
    rw [frontier_verticalCylinder]
    change z.re ∈ frontier P.base
    change z.re = v.1.re + a at hz
    rw [hz]
    exact hcfront
  have hzP' : z ∈ frontier (regularSupport K P.centres) := by
    simpa only [P.support_eq_regularSupport] using hzP
  have hfront := frontier_regularSupport_subset_tileFrontiers hTile hST hzP'
  rw [Set.mem_iUnion] at hfront
  obtain ⟨s, hsz⟩ := hfront
  apply Set.mem_iUnion_of_mem ⟨s.1, hST s.2⟩
  exact hsz

private theorem upperExtremalBoundaryLine :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ (P : Continuous.VerticalPlate K T) (a : ℝ),
        IsGreatest (Complex.re '' P.centres) a → BddAbove P.base →
        ∃ v : ↥K.vertices,
          (∀ w ∈ K.support, w.re ≤ v.1.re) ∧
          v.1.re + a ∈ frontier P.base ∧
          {z : Tiling.Plane | z.re = v.1.re + a} ⊆
            ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
  intro K T hTile P a ha habove
  obtain ⟨x, hxext, hx⟩ :=
    exists_extremePoint_isMax_re K.isPolygonal.isCompact K.nonempty
  let v : ↥K.vertices := ⟨x, extremePoint_mem_vertexSet hxext⟩
  have hv : ∀ z ∈ K.support, z.re ≤ v.1.re := by
    intro z hz
    exact hx z hz
  have hST : P.centres ⊆ T := by
    rintro _ ⟨t, ht, rfl⟩
    exact t.2
  have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P.centres) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K P.centres).mpr
    intro s hs t ht hst
    exact (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp
      hTile.2.1 (hST hs) (hST ht) hst
  have hsuppUpper : ∀ z ∈ P.support, z.re ≤ v.1.re + a := by
    intro z hz
    rw [P.support_eq_regularSupport, regularSupport] at hz
    have hzcl : z ∈ closure (openUnion K P.centres) := interior_subset hz
    rw [closure_openUnion_eq_iUnion_support hpacking] at hzcl
    obtain ⟨s, hzs⟩ := Set.mem_iUnion.mp hzcl
    rw [mem_vadd_set] at hzs
    obtain ⟨u, hu, rfl⟩ := hzs
    have hsA : s.1.re ≤ a := ha.2 ⟨s.1, s.2, rfl⟩
    have huV := hv u hu
    simp only [vadd_eq_add, Complex.add_re] at *
    linarith
  obtain ⟨t, htP, htRe⟩ := ha.1
  have htvcl : t +ᵥ v.1 ∈ closure (openUnion K P.centres) := by
    rw [closure_openUnion_eq_iUnion_support hpacking]
    apply Set.mem_iUnion_of_mem ⟨t, htP⟩
    rw [mem_vadd_set]
    have hvSupport : v.1 ∈ K.support := by
      have h := frontier_subset_closure
        (Tiling.AxisParallel.IntrinsicVertices.region_vertices_subset_frontier K v.2)
      change v.1 ∈ closure (interior K.support) at h
      rw [K.isPolygonal.closure_interior] at h
      exact h
    exact ⟨v.1, hvSupport, rfl⟩
  have hopenSub : openUnion K P.centres ⊆ P.support := by
    rw [P.support_eq_regularSupport, regularSupport]
    exact (isOpen_iUnion fun s : P.centres ↦ isOpen_interior.vadd s.1).subset_interior_closure
  have htvSupport : t +ᵥ v.1 ∈ closure P.support :=
    closure_mono hopenSub htvcl
  have hclosure : closure P.support = Complex.re ⁻¹' closure P.base := by
    rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2,
      Complex.closure_preimage_re]
  have hccl : v.1.re + a ∈ closure P.base := by
    have h := hclosure ▸ htvSupport
    change (t +ᵥ v.1).re ∈ closure P.base at h
    simpa [vadd_eq_add, Complex.add_re, htRe, add_comm] using h
  have hcnot : v.1.re + a ∉ P.base := by
    intro hc
    have hopen : IsOpen P.base := by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).1]
      exact isOpen_interior
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hc)
    let q : ℝ := v.1.re + a + r / 2
    have hq : q ∈ P.base := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [q]
      rw [show (v.1.re + a + r / 2 - (v.1.re + a)) = r / 2 by ring,
        abs_of_pos (half_pos hr)]
      linarith)
    have hqSupport : (q : ℂ) ∈ P.support := by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2]
      exact hq
    have hqUpper := hsuppUpper (q : ℂ) hqSupport
    dsimp [q] at hqUpper
    linarith
  have hcfront : v.1.re + a ∈ frontier P.base := by
    rw [frontier]
    refine ⟨hccl, ?_⟩
    intro hcint
    exact hcnot (interior_subset hcint)
  refine ⟨v, hv, hcfront, ?_⟩
  intro z hz
  have hzP : z ∈ frontier P.support := by
    rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2]
    change z ∈ frontier ({w : Tiling.Plane | w.re ∈ P.base} : Set Tiling.Plane)
    rw [frontier_verticalCylinder]
    change z.re ∈ frontier P.base
    change z.re = v.1.re + a at hz
    rw [hz]
    exact hcfront
  have hzP' : z ∈ frontier (regularSupport K P.centres) := by
    simpa only [P.support_eq_regularSupport] using hzP
  have hfront := frontier_regularSupport_subset_tileFrontiers hTile hST hzP'
  rw [Set.mem_iUnion] at hfront
  obtain ⟨s, hsz⟩ := hfront
  apply Set.mem_iUnion_of_mem ⟨s.1, hST s.2⟩
  exact hsz



open Tiling.AxisParallel.Approximation

theorem horizontalStep_mem_coordinateSpace
    (C : Approximation.ApproximationContext) {d : ℝ}
    (hd : d ∈ C.region.horizontalStepAlphabet) : d ∈ C.coordinateSpace := by
  obtain ⟨u, hu, v, hv, hdiff, _⟩ :=
    C.region.mem_horizontalStepAlphabet_iff d |>.mp hd
  subst d
  exact C.coordinateSpace.sub_mem (C.vertex_re_mem v hv) (C.vertex_re_mem u hu)

private theorem lowerExtremalGap_survivesGoodApproximation :
    ∀ (C : Approximation.ApproximationContext.{0}),
      TilesOn C.region C.centres Set.univ →
      ∀ (P : Continuous.VerticalPlate C.region C.centres),
        BddBelow P.base →
        ∃ t₀ : ↑C.centres,
          (t₀.1 : Tiling.Plane) ∈ P.centres ∧
          IsLeast (Complex.re '' P.centres) t₀.1.re ∧
          ∃ epsilon eta : ℝ, 0 < epsilon ∧ 0 < eta ∧
            ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
              Approximation.IsEpsilonApproximation C epsilon phi →
              Approximation.IsGoodApproximation C phi →
              ∀ t : ↑C.centres,
                (t.1 : Tiling.Plane) ∈ P.centres →
                t₀.1.re < t.1.re →
                (Approximation.mapPoint phi (C.centrePoint t₀.1 t₀.2)).re + eta ≤
                  (Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re := by
  intro C hTile P hbelow
  obtain ⟨a, _η₀, _hη₀, ha, _hgap⟩ :=
    (oneSidedPlate_hasProjectionGap hTile P).1 hbelow
  obtain ⟨t0, ht0P, ht0re⟩ := ha.1
  obtain ⟨t₀, ht₀C, rfl⟩ := ht0P
  have ht₀P : (t₀.1 : Tiling.Plane) ∈ P.centres := ⟨t₀, ht₀C, rfl⟩
  have ht₀re : t₀.1.re = a := ht0re
  obtain ⟨dmin, hdmin⟩ := C.region.horizontalStepAlphabet_nonempty
  have hAne : C.region.horizontalStepAlphabet.Nonempty := ⟨dmin, hdmin⟩
  let δ : ℝ := C.region.horizontalStepAlphabet.min' hAne
  have hδpos : 0 < δ := C.region.horizontalStepAlphabet_pos
    (C.region.horizontalStepAlphabet.min'_mem hAne)
  have hδle : ∀ d ∈ C.region.horizontalStepAlphabet, δ ≤ d := by
    intro d hd
    exact C.region.horizontalStepAlphabet.min'_le d hd
  let A : Finset C.coordinateSpace :=
    C.region.horizontalStepAlphabet.attach.image (fun d ↦
      (⟨d.1, horizontalStep_mem_coordinateSpace C d.2⟩ : C.coordinateSpace))
  have hA_mem : ∀ (d : ℝ) (hd : d ∈ C.region.horizontalStepAlphabet),
      (⟨d, horizontalStep_mem_coordinateSpace C hd⟩ : C.coordinateSpace) ∈ A := by
    intro d hd
    exact Finset.mem_image.mpr ⟨⟨d, hd⟩, by simp, Subtype.ext rfl⟩
  obtain ⟨epsilon, hepsilon, hclose⟩ :=
    Approximation.approximation_uniformOn_finset C A (δ / 2) (half_pos hδpos)
  refine ⟨t₀, ht₀P, ?_, epsilon, δ / 2, hepsilon, half_pos hδpos, ?_⟩
  · simpa [ht₀re] using ha
  intro phi hphi _hgood t htP htt
  obtain ⟨v, _hv, _hcfront, hline⟩ :=
    lowerExtremalBoundaryLine hTile P a ha hbelow
  have hneq : (v.1 + (t.1 : Tiling.Plane)).re ≠ v.1.re + a := by
    simp only [Complex.add_re]
    linarith [htt, ht₀re]
  obtain ⟨n, hn, step, hstep, hsum⟩ :=
    horizontalBoundaryDistance_eq_stepSum hTile hline v t hneq
  have hsum' : (∑ i, step i) = t.1.re - t₀.1.re := by
    have hpos : 0 < (v.1 + (t.1 : Tiling.Plane)).re - (v.1.re + a) := by
      simp only [Complex.add_re]
      linarith [htt, ht₀re]
    rw [abs_of_pos hpos] at hsum
    simp only [Complex.add_re] at hsum
    linarith [hsum]
  let stepCoord : Fin n → C.coordinateSpace := fun i ↦
    ⟨step i, horizontalStep_mem_coordinateSpace C (hstep i)⟩
  have hsumCoord : (∑ i, stepCoord i) =
      (⟨t.1.re - t₀.1.re,
        C.coordinateSpace.sub_mem (C.centre_re_mem t.1 t.2)
          (C.centre_re_mem t₀.1 t₀.2)⟩ : C.coordinateSpace) := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, stepCoord] using hsum'
  have hmap := congrArg phi hsumCoord
  have hmap' := congrArg (fun q : ℚ ↦ (q : ℝ)) hmap
  simp only [map_sum, Rat.cast_sum] at hmap'
  have hstepLower : ∀ i : Fin n, δ / 2 ≤ mapScalar phi (stepCoord i) := by
    intro i
    have hc := hclose phi hphi (stepCoord i) (hA_mem (step i) (hstep i))
    have hraw := hδle (step i) (hstep i)
    rw [abs_lt] at hc
    linarith
  have hsumLower : δ / 2 ≤ ∑ i, mapScalar phi (stepCoord i) := by
    let i0 : Fin n := ⟨0, hn⟩
    have hsumge : mapScalar phi (stepCoord i0) ≤
        ∑ i, mapScalar phi (stepCoord i) := by
      simpa using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin n)))
          (fun i _ ↦ le_of_lt (lt_of_lt_of_le (half_pos hδpos) (hstepLower i)))
          (Finset.mem_univ i0))
    exact (hstepLower i0).trans hsumge
  have hdiffmap : δ / 2 ≤
      Approximation.mapScalar phi (⟨t.1.re - t₀.1.re,
        C.coordinateSpace.sub_mem (C.centre_re_mem t.1 t.2)
          (C.centre_re_mem t₀.1 t₀.2)⟩ : C.coordinateSpace) := by
    calc
      δ / 2 ≤ ∑ i, mapScalar phi (stepCoord i) := hsumLower
      _ = (phi (⟨t.1.re - t₀.1.re,
          C.coordinateSpace.sub_mem (C.centre_re_mem t.1 t.2)
            (C.centre_re_mem t₀.1 t₀.2)⟩) : ℚ) := hmap'
  have hcenter :
      Approximation.mapScalar phi (⟨t.1.re - t₀.1.re,
        C.coordinateSpace.sub_mem (C.centre_re_mem t.1 t.2)
          (C.centre_re_mem t₀.1 t₀.2)⟩ : C.coordinateSpace) =
        (Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
          (Approximation.mapPoint phi (C.centrePoint t₀.1 t₀.2)).re := by
    have hsub : (⟨t.1.re - t₀.1.re,
        C.coordinateSpace.sub_mem (C.centre_re_mem t.1 t.2)
          (C.centre_re_mem t₀.1 t₀.2)⟩ : C.coordinateSpace) =
        (⟨t.1.re, C.centre_re_mem t.1 t.2⟩ : C.coordinateSpace) -
          (⟨t₀.1.re, C.centre_re_mem t₀.1 t₀.2⟩ : C.coordinateSpace) := by
      apply Subtype.ext
      rfl
    rw [hsub]
    change ((phi ((⟨t.1.re, C.centre_re_mem t.1 t.2⟩ : C.coordinateSpace) -
        (⟨t₀.1.re, C.centre_re_mem t₀.1 t₀.2⟩ : C.coordinateSpace)) : ℚ) : ℝ) = _
    rw [map_sub]
    simp only [Rat.cast_sub]
    change ((phi (⟨t.1.re, C.centre_re_mem t.1 t.2⟩ : C.coordinateSpace) : ℚ) : ℝ) -
        ((phi (⟨t₀.1.re, C.centre_re_mem t₀.1 t₀.2⟩ : C.coordinateSpace) : ℚ) : ℝ) = _
    simp [Approximation.mapPoint, Approximation.mapScalar,
      ApproximationContext.centrePoint]
  rw [hcenter] at hdiffmap
  linarith

private theorem upperExtremalGap_survivesGoodApproximation :
    ∀ (C : Approximation.ApproximationContext.{0}),
      TilesOn C.region C.centres Set.univ →
      ∀ (P : Continuous.VerticalPlate C.region C.centres),
        BddAbove P.base →
        ∃ t₀ : ↑C.centres,
          (t₀.1 : Tiling.Plane) ∈ P.centres ∧
          IsGreatest (Complex.re '' P.centres) t₀.1.re ∧
          ∃ epsilon eta : ℝ, 0 < epsilon ∧ 0 < eta ∧
            ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
              Approximation.IsEpsilonApproximation C epsilon phi →
              Approximation.IsGoodApproximation C phi →
              ∀ t : ↑C.centres,
                (t.1 : Tiling.Plane) ∈ P.centres →
                t.1.re < t₀.1.re →
                (Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re + eta ≤
                  (Approximation.mapPoint phi (C.centrePoint t₀.1 t₀.2)).re := by
  intro C hTile P habove
  obtain ⟨a, _η₀, _hη₀, ha, _hgap⟩ :=
    (oneSidedPlate_hasProjectionGap hTile P).2 habove
  obtain ⟨t0, ht0P, ht0re⟩ := ha.1
  obtain ⟨t₀, ht₀C, rfl⟩ := ht0P
  have ht₀P : (t₀.1 : Tiling.Plane) ∈ P.centres := ⟨t₀, ht₀C, rfl⟩
  have ht₀re : t₀.1.re = a := ht0re
  obtain ⟨dmin, hdmin⟩ := C.region.horizontalStepAlphabet_nonempty
  have hAne : C.region.horizontalStepAlphabet.Nonempty := ⟨dmin, hdmin⟩
  let δ : ℝ := C.region.horizontalStepAlphabet.min' hAne
  have hδpos : 0 < δ := C.region.horizontalStepAlphabet_pos
    (C.region.horizontalStepAlphabet.min'_mem hAne)
  have hδle : ∀ d ∈ C.region.horizontalStepAlphabet, δ ≤ d := by
    intro d hd
    exact C.region.horizontalStepAlphabet.min'_le d hd
  let A : Finset C.coordinateSpace :=
    C.region.horizontalStepAlphabet.attach.image (fun d ↦
      (⟨d.1, horizontalStep_mem_coordinateSpace C d.2⟩ : C.coordinateSpace))
  have hA_mem : ∀ (d : ℝ) (hd : d ∈ C.region.horizontalStepAlphabet),
      (⟨d, horizontalStep_mem_coordinateSpace C hd⟩ : C.coordinateSpace) ∈ A := by
    intro d hd
    exact Finset.mem_image.mpr ⟨⟨d, hd⟩, by simp, Subtype.ext rfl⟩
  obtain ⟨epsilon, hepsilon, hclose⟩ :=
    Approximation.approximation_uniformOn_finset C A (δ / 2) (half_pos hδpos)
  refine ⟨t₀, ht₀P, ?_, epsilon, δ / 2, hepsilon, half_pos hδpos, ?_⟩
  · simpa [ht₀re] using ha
  intro phi hphi _hgood t htP htt
  obtain ⟨v, _hv, _hcfront, hline⟩ :=
    upperExtremalBoundaryLine hTile P a ha habove
  have hneq : (v.1 + (t.1 : Tiling.Plane)).re ≠ v.1.re + a := by
    simp only [Complex.add_re]
    linarith [htt, ht₀re]
  obtain ⟨n, hn, step, hstep, hsum⟩ :=
    horizontalBoundaryDistance_eq_stepSum hTile hline v t hneq
  have hsum' : (∑ i, step i) = t₀.1.re - t.1.re := by
    have hneg : (v.1 + (t.1 : Tiling.Plane)).re - (v.1.re + a) < 0 := by
      simp only [Complex.add_re]
      linarith [htt, ht₀re]
    rw [abs_of_neg hneg] at hsum
    simp only [Complex.add_re] at hsum
    linarith [hsum]
  let stepCoord : Fin n → C.coordinateSpace := fun i ↦
    ⟨step i, horizontalStep_mem_coordinateSpace C (hstep i)⟩
  have hsumCoord : (∑ i, stepCoord i) =
      (⟨t₀.1.re - t.1.re,
        C.coordinateSpace.sub_mem (C.centre_re_mem t₀.1 t₀.2)
          (C.centre_re_mem t.1 t.2)⟩ : C.coordinateSpace) := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, stepCoord] using hsum'
  have hmap := congrArg phi hsumCoord
  have hmap' := congrArg (fun q : ℚ ↦ (q : ℝ)) hmap
  simp only [map_sum, Rat.cast_sum] at hmap'
  have hstepLower : ∀ i : Fin n, δ / 2 ≤ mapScalar phi (stepCoord i) := by
    intro i
    have hc := hclose phi hphi (stepCoord i) (hA_mem (step i) (hstep i))
    have hraw := hδle (step i) (hstep i)
    rw [abs_lt] at hc
    linarith
  have hsumLower : δ / 2 ≤ ∑ i, mapScalar phi (stepCoord i) := by
    let i0 : Fin n := ⟨0, hn⟩
    have hsumge : mapScalar phi (stepCoord i0) ≤
        ∑ i, mapScalar phi (stepCoord i) := by
      simpa using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin n)))
          (fun i _ ↦ le_of_lt (lt_of_lt_of_le (half_pos hδpos) (hstepLower i)))
          (Finset.mem_univ i0))
    exact (hstepLower i0).trans hsumge
  have hdiffmap : δ / 2 ≤
      Approximation.mapScalar phi (⟨t₀.1.re - t.1.re,
        C.coordinateSpace.sub_mem (C.centre_re_mem t₀.1 t₀.2)
          (C.centre_re_mem t.1 t.2)⟩ : C.coordinateSpace) := by
    calc
      δ / 2 ≤ ∑ i, mapScalar phi (stepCoord i) := hsumLower
      _ = (phi (⟨t₀.1.re - t.1.re,
          C.coordinateSpace.sub_mem (C.centre_re_mem t₀.1 t₀.2)
            (C.centre_re_mem t.1 t.2)⟩) : ℚ) := hmap'
  have hcenter :
      Approximation.mapScalar phi (⟨t₀.1.re - t.1.re,
        C.coordinateSpace.sub_mem (C.centre_re_mem t₀.1 t₀.2)
          (C.centre_re_mem t.1 t.2)⟩ : C.coordinateSpace) =
        (Approximation.mapPoint phi (C.centrePoint t₀.1 t₀.2)).re -
          (Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re := by
    have hsub : (⟨t₀.1.re - t.1.re,
        C.coordinateSpace.sub_mem (C.centre_re_mem t₀.1 t₀.2)
          (C.centre_re_mem t.1 t.2)⟩ : C.coordinateSpace) =
        (⟨t₀.1.re, C.centre_re_mem t₀.1 t₀.2⟩ : C.coordinateSpace) -
          (⟨t.1.re, C.centre_re_mem t.1 t.2⟩ : C.coordinateSpace) := by
      apply Subtype.ext
      rfl
    rw [hsub]
    change ((phi ((⟨t₀.1.re, C.centre_re_mem t₀.1 t₀.2⟩ : C.coordinateSpace) -
        (⟨t.1.re, C.centre_re_mem t.1 t.2⟩ : C.coordinateSpace)) : ℚ) : ℝ) = _
    rw [map_sub]
    simp only [Rat.cast_sub]
    change ((phi (⟨t₀.1.re, C.centre_re_mem t₀.1 t₀.2⟩ : C.coordinateSpace) : ℚ) : ℝ) -
        ((phi (⟨t.1.re, C.centre_re_mem t.1 t.2⟩ : C.coordinateSpace) : ℚ) : ℝ) = _
    simp [Approximation.mapPoint, Approximation.mapScalar,
      ApproximationContext.centrePoint]
  rw [hcenter] at hdiffmap
  linarith


private def extremalFibre
    {K : Region} {T : Set Tiling.Plane}
    (P : Continuous.VerticalPlate K T) (a : ℝ) : Set Tiling.Plane :=
  {t : Tiling.Plane | t ∈ P.centres ∧ t.re = a}


private theorem lowerSeedInterval
    {B : Set ℝ} {c eta : ℝ} (hopen : IsOpen B)
    (hccl : c ∈ closure B) (hcnot : c ∉ B)
    (hsub : B ⊆ Set.Ici c) (heta : 0 < eta) :
    ∃ l r : ℝ, l < r ∧ Set.Ioo l r ⊆ B ∧
      Set.Ioo l r ⊆ Set.Ioo c (c + eta) := by
  obtain ⟨q, hqB, hqdist⟩ :=
    Metric.mem_closure_iff.mp hccl (eta / 4) (by linarith)
  have hqc : c < q := lt_of_le_of_ne (hsub hqB) (Ne.symm (by
    intro h
    exact hcnot (h ▸ hqB)))
  obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hqB)
  have hqeta : q < c + eta := by
    have := (Metric.mem_ball.mp hqdist)
    rw [Real.dist_eq] at this
    rw [abs_lt] at this
    linarith [hqc]
  let d := min (rho / 2) (min ((q - c) / 2) ((c + eta - q) / 2))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  refine ⟨q - d, q + d, by linarith, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨hxl, hxr⟩
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [min_le_left (rho / 2)
        (min ((q - c) / 2) ((c + eta - q) / 2))]
    · linarith [min_le_left (rho / 2)
        (min ((q - c) / 2) ((c + eta - q) / 2))]
  · intro x hx
    rcases hx with ⟨hxl, hxr⟩
    constructor
    · have hdq : d ≤ (q - c) / 2 := min_le_of_right_le (min_le_left _ _)
      linarith
    · have hdq : d ≤ (c + eta - q) / 2 := min_le_of_right_le (min_le_right _ _)
      linarith

private theorem upperSeedInterval
    {B : Set ℝ} {c eta : ℝ} (hopen : IsOpen B)
    (hccl : c ∈ closure B) (hcnot : c ∉ B)
    (hsub : B ⊆ Set.Iic c) (heta : 0 < eta) :
    ∃ l r : ℝ, l < r ∧ Set.Ioo l r ⊆ B ∧
      Set.Ioo l r ⊆ Set.Ioo (c - eta) c := by
  obtain ⟨q, hqB, hqdist⟩ :=
    Metric.mem_closure_iff.mp hccl (eta / 4) (by linarith)
  have hqc : q < c := by
    have hle := hsub hqB
    have hneq : q ≠ c := by
      intro h
      exact hcnot (h ▸ hqB)
    exact lt_of_le_of_ne hle hneq
  obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hqB)
  have hqeta : c - eta < q := by
    have := (Metric.mem_ball.mp hqdist)
    rw [Real.dist_eq] at this
    rw [abs_lt] at this
    linarith [hqc]
  let d := min (rho / 2) (min ((c - q) / 2) ((q - (c - eta)) / 2))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  refine ⟨q - d, q + d, by linarith, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨hxl, hxr⟩
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [min_le_left (rho / 2)
        (min ((c - q) / 2) ((q - (c - eta)) / 2))]
    · linarith [min_le_left (rho / 2)
        (min ((c - q) / 2) ((q - (c - eta)) / 2))]
  · intro x hx
    rcases hx with ⟨hxl, hxr⟩
    constructor
    · have hdq : d ≤ (q - (c - eta)) / 2 := min_le_of_right_le (min_le_right _ _)
      linarith
    · have hdq : d ≤ (c - q) / 2 := min_le_of_right_le (min_le_left _ _)
      linarith

private theorem lineTiles_of_fubini
    {K : Region} {S : Set Tiling.Plane} {a x : ℝ}
    {Y : Set ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    {D : Set Tiling.Plane}
    (hsupport : ∀ y : ℝ,
      ((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ D)
    (hgood : ∀ᵐ y : ℝ ∂volume,
      (((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
          D ↔
        ∃! t : S,
          y - t.1.im ∈
            {v : ℝ |
              ((x - t.1.re : ℝ) : ℂ) + (v : ℂ) * Complex.I ∈ K.openCarrier}))
    (hcenter : ∀ (t : S) (q : ℝ),
      q - t.1.im ∈
          {v : ℝ |
            ((x - t.1.re : ℝ) : ℂ) + (v : ℂ) * Complex.I ∈ K.openCarrier} →
      t.1.re = a)
    (hY : Y = Complex.im '' {t : Tiling.Plane | t ∈ (S : Set Tiling.Plane) ∧ t.re = a}) :
    OneDimensional.LineTiles (verticalSlice K (x - a)) Y := by
  have hopenB : IsOpen (verticalSlice K (x - a)) := by
    apply K.openCarrier_regularOpen.1.preimage
    fun_prop
  have hcountS : S.Countable :=
    (Tiling.AxisParallel.IsPacking.locallyFinite_centres hpacking).2
  have hcountY : Y.Countable := by
    rw [hY]
    have hcountExt : {t : Tiling.Plane |
        t ∈ (S : Set Tiling.Plane) ∧ t.re = a}.Countable := hcountS.mono (by
      intro t ht
      exact ht.1)
    exact hcountExt.image Complex.im
  refine ⟨hopenB.measurableSet, MeasurableSet.univ, hcountY, ?_, ?_⟩
  · intro y hy z hz hyz
    rw [hY] at hy hz
    rcases hy with ⟨t, ht, rfl⟩
    rcases hz with ⟨u, hu, rfl⟩
    apply Disjoint.aedisjoint
    exact disjoint_left.mpr (by
      intro q hq hq'
      have hq'B : q - t.im ∈ verticalSlice K (x - a) := by
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg, add_comm] using hq
      have hq''B : q - u.im ∈ verticalSlice K (x - a) := by
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg, add_comm] using hq'
      have htu : (t : Tiling.Plane) ≠ u := by
        intro h
        apply hyz
        simp [h]
      have hdisj := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K S).mp
        hpacking ht.1 hu.1 htu
      have hmemt : (((x : ℝ) : ℂ) + (q : ℂ) * Complex.I) ∈
          (t : Tiling.Plane) +ᵥ K.openCarrier := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        change -((t : Tiling.Plane)) +
            (((x : ℝ) : ℂ) + (q : ℂ) * Complex.I) ∈ K.openCarrier
        change (((x - a : ℝ) : ℂ) + ((q - t.im : ℝ) : ℂ) * Complex.I) ∈
          K.openCarrier at hq'B
        convert hq'B using 1
        all_goals apply Complex.ext
        all_goals simp [ht.2]
        all_goals ring
      have hmemu : (((x : ℝ) : ℂ) + (q : ℂ) * Complex.I) ∈
          (u : Tiling.Plane) +ᵥ K.openCarrier := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        change -((u : Tiling.Plane)) +
            (((x : ℝ) : ℂ) + (q : ℂ) * Complex.I) ∈ K.openCarrier
        change (((x - a : ℝ) : ℂ) + ((q - u.im : ℝ) : ℂ) * Complex.I) ∈
          K.openCarrier at hq''B
        convert hq''B using 1
        all_goals apply Complex.ext
        all_goals simp [hu.2]
        all_goals ring
      have hdisj2 : Disjoint ((t : Tiling.Plane) +ᵥ K.openCarrier)
          ((u : Tiling.Plane) +ᵥ K.openCarrier) := hdisj
      apply (Set.disjoint_left.1 hdisj2 hmemt)
      exact hmemu)
  filter_upwards [hgood] with y hy
  constructor
  · intro _
    obtain ⟨t, ht, hut⟩ := hy.mp (hsupport y)
    have hta : t.1.re = a := hcenter t y ht
    have hYmem : t.1.im ∈ Y := by
      rw [hY]
      exact ⟨t.1, ⟨t.2, hta⟩, rfl⟩
    refine ⟨⟨t.1.im, hYmem⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change -t.1.im + y ∈ verticalSlice K (x - a)
    rw [sub_eq_add_neg, add_comm]
    change (((-a + x : ℝ) : ℂ) + ((-t.1.im + y : ℝ) : ℂ) * Complex.I) ∈
      K.openCarrier
    simpa [hta, sub_eq_add_neg, add_comm] using ht
  · intro _
    simp


private theorem lowerExtremalFibre_hasSeedLineTiling :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ (P : Continuous.VerticalPlate K T) (a eta : ℝ),
        BddBelow P.base → 0 < eta →
        IsLeast (Complex.re '' P.centres) a →
        (∀ x ∈ Complex.re '' P.centres, a < x → a + eta ≤ x) →
        ∃ r₀ : ℝ,
          r₀ ∉ K.vertexFinset.image Complex.re ∧
          (verticalSlice K r₀).Nonempty ∧
          OneDimensional.LineTiles (verticalSlice K r₀)
            (Complex.im '' extremalFibre P a) :=by
  intro K T hTile P a eta hbelow heta ha hgap
  obtain ⟨v, hvSupport, hvMin⟩ :=
    K.isPolygonal.isCompact.exists_isMinOn K.nonempty
      Complex.continuous_re.continuousOn
  have hST : P.centres ⊆ T := by
    rintro _ ⟨t, ht, rfl⟩
    exact t.2
  have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P.centres) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K P.centres).mpr
    intro s hs t ht hst
    exact (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp
      hTile.2.1 (hST hs) (hST ht) hst
  have hTileP : TilesOn K P.centres P.support := by
    refine ⟨(Tiling.AxisParallel.IsPacking.locallyFinite_centres hpacking).2,
      hpacking, ?_⟩
    rw [P.support_eq_regularSupport]
    filter_upwards [(Tiling.AxisParallel.openUnion_aeEq_regularSupport hpacking).symm]
      with z hz
    constructor
    · intro h
      have hopen := hz.mp h
      change z ∈ ⋃ s : P.centres, (s.1 : Tiling.Plane) +ᵥ K.openCarrier at hopen
      exact Set.mem_iUnion.mp hopen
    · intro h
      apply hz.mpr
      change z ∈ ⋃ s : P.centres, (s.1 : Tiling.Plane) +ᵥ K.openCarrier
      exact Set.mem_iUnion.mpr h
  have hsuppLower : ∀ z ∈ P.support, v.re + a ≤ z.re := by
    intro z hz
    rw [P.support_eq_regularSupport, regularSupport] at hz
    have hzcl : z ∈ closure (openUnion K P.centres) := interior_subset hz
    rw [closure_openUnion_eq_iUnion_support hpacking] at hzcl
    obtain ⟨s, hzs⟩ := Set.mem_iUnion.mp hzcl
    rw [mem_vadd_set] at hzs
    obtain ⟨u, hu, rfl⟩ := hzs
    have haS : a ≤ s.1.re := ha.2 ⟨s.1, s.2, rfl⟩
    have hvU := hvMin hu
    simp only [vadd_eq_add, Complex.add_re] at *
    change v.re ≤ u.re at hvU
    linarith
  obtain ⟨t, htP, htRe⟩ := ha.1
  have htvcl : t +ᵥ v ∈ closure (openUnion K P.centres) := by
    rw [closure_openUnion_eq_iUnion_support hpacking]
    apply Set.mem_iUnion_of_mem ⟨t, htP⟩
    rw [mem_vadd_set]
    exact ⟨v, hvSupport, rfl⟩
  have hopenSub : openUnion K P.centres ⊆ P.support := by
    rw [P.support_eq_regularSupport, regularSupport]
    exact (isOpen_iUnion fun s : P.centres ↦ isOpen_interior.vadd s.1).subset_interior_closure
  have htvSupport : t +ᵥ v ∈ closure P.support := closure_mono hopenSub htvcl
  have hclosure : closure P.support = Complex.re ⁻¹' closure P.base := by
    rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2,
      Complex.closure_preimage_re]
  let c : ℝ := v.re + a
  have hccl : c ∈ closure P.base := by
    have h := hclosure ▸ htvSupport
    change (t +ᵥ v).re ∈ closure P.base at h
    simpa [c, vadd_eq_add, Complex.add_re, htRe, add_comm] using h
  have hcnot : c ∉ P.base := by
    intro hc
    have hopen : IsOpen P.base := by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).1]
      exact isOpen_interior
    obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hc)
    let q : ℝ := c - rho / 2
    have hq : q ∈ P.base := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [q]
      rw [show (c - rho / 2 - c) = -(rho / 2) by ring,
        abs_neg, abs_of_pos (half_pos hrho)]
      linarith)
    have hqSupport : (q : ℂ) ∈ P.support := by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2]
      exact hq
    have hqLower := hsuppLower (q : ℂ) hqSupport
    dsimp [q, c] at hqLower
    linarith
  have hbaseSub : P.base ⊆ Set.Ici c := by
    intro q hq
    have hqSupport : (q : ℂ) ∈ P.support := by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2]
      exact hq
    exact hsuppLower (q : ℂ) hqSupport
  obtain ⟨l, r, hlr, hJsub, hJcollar⟩ :=
    lowerSeedInterval (by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).1]
      exact isOpen_interior) hccl hcnot hbaseSub heta
  let F : Set ℝ := (fun z : ℝ => a + z) ''
    (K.vertexFinset.image Complex.re : Set ℝ)
  have hFfinite : F.Finite := by
    exact (K.vertexFinset.image Complex.re).finite_toSet.image (fun z : ℝ => a + z)
  have hFzero : volume F = 0 := hFfinite.measure_zero volume
  have hJpos : volume (Set.Ioo l r) ≠ 0 := by
    rw [Real.volume_Ioo]
    positivity
  have hUpos : volume ((Set.Ioo l r) \ F) ≠ 0 := by
    rw [measure_sdiff_null hFzero]
    exact hJpos
  have hUne : ((Set.Ioo l r) \ F).Nonempty :=
    MeasureTheory.nonempty_of_measure_ne_zero hUpos
  have hFub := Tiling.AxisParallel.Foundations.tilesOn_fubiniSlices hTileP
  have hdense := volume.dense_of_ae hFub
  have hUopen : IsOpen ((Set.Ioo l r) \ F) := isOpen_Ioo.sdiff hFfinite.isClosed
  obtain ⟨x, hxgood, hxU⟩ := hdense.exists_mem_open hUopen hUne
  have hxbase : x ∈ P.base := hJsub hxU.1
  have hsupport : ∀ y : ℝ,
      ((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ P.support := by
    intro y
    rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2]
    simpa using hxbase
  have hcenter : ∀ (s : P.centres) (q : ℝ),
      q - s.1.im ∈
          {v : ℝ | ((x - s.1.re : ℝ) : ℂ) + (v : ℂ) * Complex.I ∈ K.openCarrier} →
      s.1.re = a := by
    intro s q hq
    have hq' : -((s : Tiling.Plane)) +
        (((x : ℝ) : ℂ) + (q : ℂ) * Complex.I) ∈ K.openCarrier := by
      change (((x - s.1.re : ℝ) : ℂ) + ((q - s.1.im : ℝ) : ℂ) * Complex.I) ∈
        K.openCarrier at hq
      convert hq using 1
      all_goals apply Complex.ext
      all_goals simp
      all_goals ring
    have hqSupport : -((s : Tiling.Plane)) +
        (((x : ℝ) : ℂ) + (q : ℂ) * Complex.I) ∈ K.support :=
      interior_subset hq'
    have hvq := hvMin hqSupport
    change v.re ≤ (-((s : Tiling.Plane)) +
      (((x : ℝ) : ℂ) + (q : ℂ) * Complex.I)).re at hvq
    have hsa : a ≤ s.1.re := ha.2 ⟨s.1, s.2, rfl⟩
    have hxc : x < c + eta := hJcollar hxU.1 |>.2
    by_contra hne
    have hsa' : a < s.1.re := lt_of_le_of_ne hsa (Ne.symm hne)
    have hgap' := hgap s.1.re ⟨s.1, s.2, rfl⟩ hsa'
    have hvq' : v.re ≤ x - s.1.re := by
      calc
        v.re ≤ (-((s : Tiling.Plane)) +
          (((x : ℝ) : ℂ) + (q : ℂ) * Complex.I)).re := hvq
        _ = x - s.1.re := by simp; ring
    dsimp [c] at hxc
    linarith [hvq', hgap']
  have hxgeneric : x - a ∉ (K.vertexFinset.image Complex.re : Set ℝ) := by
    intro hxv
    have hxF : x ∈ F := by
      exact ⟨x - a, hxv, by ring⟩
    exact hxU.2 hxF
  have hBne : (verticalSlice K (x - a)).Nonempty := by
    change ∀ᵐ y : ℝ, _ at hxgood
    obtain ⟨y, hy⟩ := (Filter.Eventually.exists hxgood)
    obtain ⟨s, hs, _⟩ := hy.mp (hsupport y)
    have hta := hcenter s y hs
    have hs' : y - s.1.im ∈ verticalSlice K (x - a) := by
      change (((x - a : ℝ) : ℂ) + ((y - s.1.im : ℝ) : ℂ) * Complex.I) ∈
        K.openCarrier
      change (((x - s.1.re : ℝ) : ℂ) + ((y - s.1.im : ℝ) : ℂ) * Complex.I) ∈
        K.openCarrier at hs
      simpa [hta] using hs
    exact ⟨y - s.1.im, hs'⟩
  refine ⟨x - a, hxgeneric, hBne, ?_⟩
  apply lineTiles_of_fubini hpacking hsupport hxgood hcenter
  rfl



private theorem upperExtremalFibre_hasSeedLineTiling :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ (P : Continuous.VerticalPlate K T) (a eta : ℝ),
        BddAbove P.base → 0 < eta →
        IsGreatest (Complex.re '' P.centres) a →
        (∀ x ∈ Complex.re '' P.centres, x < a → x ≤ a - eta) →
        ∃ r₀ : ℝ,
          r₀ ∉ K.vertexFinset.image Complex.re ∧
          (verticalSlice K r₀).Nonempty ∧
          OneDimensional.LineTiles (verticalSlice K r₀)
            (Complex.im '' extremalFibre P a) :=by
  intro K T hTile P a eta habove heta ha hgap
  obtain ⟨v, hvSupport, hvMax⟩ :=
    K.isPolygonal.isCompact.exists_isMaxOn K.nonempty
      Complex.continuous_re.continuousOn
  have hST : P.centres ⊆ T := by
    rintro _ ⟨t, ht, rfl⟩
    exact t.2
  have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P.centres) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K P.centres).mpr
    intro s hs t ht hst
    exact (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp
      hTile.2.1 (hST hs) (hST ht) hst
  have hTileP : TilesOn K P.centres P.support := by
    refine ⟨(Tiling.AxisParallel.IsPacking.locallyFinite_centres hpacking).2,
      hpacking, ?_⟩
    rw [P.support_eq_regularSupport]
    filter_upwards [(Tiling.AxisParallel.openUnion_aeEq_regularSupport hpacking).symm]
      with z hz
    constructor
    · intro h
      have hopen := hz.mp h
      change z ∈ ⋃ s : P.centres, (s.1 : Tiling.Plane) +ᵥ K.openCarrier at hopen
      exact Set.mem_iUnion.mp hopen
    · intro h
      apply hz.mpr
      change z ∈ ⋃ s : P.centres, (s.1 : Tiling.Plane) +ᵥ K.openCarrier
      exact Set.mem_iUnion.mpr h
  have hsuppUpper : ∀ z ∈ P.support, z.re ≤ v.re + a := by
    intro z hz
    rw [P.support_eq_regularSupport, regularSupport] at hz
    have hzcl : z ∈ closure (openUnion K P.centres) := interior_subset hz
    rw [closure_openUnion_eq_iUnion_support hpacking] at hzcl
    obtain ⟨s, hzs⟩ := Set.mem_iUnion.mp hzcl
    rw [mem_vadd_set] at hzs
    obtain ⟨u, hu, rfl⟩ := hzs
    have hsA : s.1.re ≤ a := ha.2 ⟨s.1, s.2, rfl⟩
    have hvU := hvMax hu
    simp only [vadd_eq_add, Complex.add_re] at *
    change u.re ≤ v.re at hvU
    linarith
  obtain ⟨t, htP, htRe⟩ := ha.1
  have htvcl : t +ᵥ v ∈ closure (openUnion K P.centres) := by
    rw [closure_openUnion_eq_iUnion_support hpacking]
    apply Set.mem_iUnion_of_mem ⟨t, htP⟩
    rw [mem_vadd_set]
    exact ⟨v, hvSupport, rfl⟩
  have hopenSub : openUnion K P.centres ⊆ P.support := by
    rw [P.support_eq_regularSupport, regularSupport]
    exact (isOpen_iUnion fun s : P.centres ↦ isOpen_interior.vadd s.1).subset_interior_closure
  have htvSupport : t +ᵥ v ∈ closure P.support := closure_mono hopenSub htvcl
  have hclosure : closure P.support = Complex.re ⁻¹' closure P.base := by
    rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2,
      Complex.closure_preimage_re]
  let c : ℝ := v.re + a
  have hccl : c ∈ closure P.base := by
    have h := hclosure ▸ htvSupport
    change (t +ᵥ v).re ∈ closure P.base at h
    simpa [c, vadd_eq_add, Complex.add_re, htRe, add_comm] using h
  have hcnot : c ∉ P.base := by
    intro hc
    have hopen : IsOpen P.base := by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).1]
      exact isOpen_interior
    obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hc)
    let q : ℝ := c + rho / 2
    have hq : q ∈ P.base := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [q]
      rw [show (c + rho / 2 - c) = rho / 2 by ring,
        abs_of_pos (half_pos hrho)]
      linarith)
    have hqSupport : (q : ℂ) ∈ P.support := by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2]
      exact hq
    have hqUpper := hsuppUpper (q : ℂ) hqSupport
    dsimp [q, c] at hqUpper
    linarith
  have hbaseSub : P.base ⊆ Set.Iic c := by
    intro q hq
    have hqSupport : (q : ℂ) ∈ P.support := by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2]
      exact hq
    exact hsuppUpper (q : ℂ) hqSupport
  obtain ⟨l, r, hlr, hJsub, hJcollar⟩ :=
    upperSeedInterval (by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).1]
      exact isOpen_interior) hccl hcnot hbaseSub heta
  let F : Set ℝ := (fun z : ℝ => a + z) ''
    (K.vertexFinset.image Complex.re : Set ℝ)
  have hFfinite : F.Finite := by
    exact (K.vertexFinset.image Complex.re).finite_toSet.image (fun z : ℝ => a + z)
  have hFzero : volume F = 0 := hFfinite.measure_zero volume
  have hJpos : volume (Set.Ioo l r) ≠ 0 := by
    rw [Real.volume_Ioo]
    positivity
  have hUpos : volume ((Set.Ioo l r) \ F) ≠ 0 := by
    rw [measure_sdiff_null hFzero]
    exact hJpos
  have hUne : ((Set.Ioo l r) \ F).Nonempty :=
    MeasureTheory.nonempty_of_measure_ne_zero hUpos
  have hFub := Tiling.AxisParallel.Foundations.tilesOn_fubiniSlices hTileP
  have hdense := volume.dense_of_ae hFub
  have hUopen : IsOpen ((Set.Ioo l r) \ F) := isOpen_Ioo.sdiff hFfinite.isClosed
  obtain ⟨x, hxgood, hxU⟩ := hdense.exists_mem_open hUopen hUne
  have hxbase : x ∈ P.base := hJsub hxU.1
  have hsupport : ∀ y : ℝ,
      ((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ P.support := by
    intro y
    rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).2]
    simpa using hxbase
  have hcenter : ∀ (s : P.centres) (q : ℝ),
      q - s.1.im ∈
          {v : ℝ | ((x - s.1.re : ℝ) : ℂ) + (v : ℂ) * Complex.I ∈ K.openCarrier} →
      s.1.re = a := by
    intro s q hq
    have hq' : -((s : Tiling.Plane)) +
        (((x : ℝ) : ℂ) + (q : ℂ) * Complex.I) ∈ K.openCarrier := by
      change (((x - s.1.re : ℝ) : ℂ) + ((q - s.1.im : ℝ) : ℂ) * Complex.I) ∈
        K.openCarrier at hq
      convert hq using 1
      all_goals apply Complex.ext
      all_goals simp
      all_goals ring
    have hqSupport : -((s : Tiling.Plane)) +
        (((x : ℝ) : ℂ) + (q : ℂ) * Complex.I) ∈ K.support :=
      interior_subset hq'
    have hvq := hvMax hqSupport
    change (-((s : Tiling.Plane)) +
      (((x : ℝ) : ℂ) + (q : ℂ) * Complex.I)).re ≤ v.re at hvq
    have hsa : s.1.re ≤ a := ha.2 ⟨s.1, s.2, rfl⟩
    have hxc : c - eta < x := (hJcollar hxU.1).1
    by_contra hne
    have hsa' : s.1.re ≤ a - eta := hgap s.1.re ⟨s.1, s.2, rfl⟩
      (lt_of_le_of_ne hsa hne)
    have hvq' : x - s.1.re ≤ v.re := by
      calc
        x - s.1.re = (-((s : Tiling.Plane)) +
          (((x : ℝ) : ℂ) + (q : ℂ) * Complex.I)).re := by simp; ring
        _ ≤ v.re := hvq
    dsimp [c] at hxc
    linarith [hvq', hsa']
  have hxgeneric : x - a ∉ (K.vertexFinset.image Complex.re : Set ℝ) := by
    intro hxv
    have hxF : x ∈ F := by
      exact ⟨x - a, hxv, by ring⟩
    exact hxU.2 hxF
  have hBne : (verticalSlice K (x - a)).Nonempty := by
    change ∀ᵐ y : ℝ, _ at hxgood
    obtain ⟨y, hy⟩ := (Filter.Eventually.exists hxgood)
    obtain ⟨s, hs, _⟩ := hy.mp (hsupport y)
    have hta := hcenter s y hs
    have hs' : y - s.1.im ∈ verticalSlice K (x - a) := by
      change (((x - a : ℝ) : ℂ) + ((y - s.1.im : ℝ) : ℂ) * Complex.I) ∈
        K.openCarrier
      change (((x - s.1.re : ℝ) : ℂ) + ((y - s.1.im : ℝ) : ℂ) * Complex.I) ∈
        K.openCarrier at hs
      simpa [hta] using hs
    exact ⟨y - s.1.im, hs'⟩
  refine ⟨x - a, hxgeneric, hBne, ?_⟩
  apply lineTiles_of_fubini hpacking hsupport hxgood hcenter
  rfl


private theorem columnPacking_slicePacking
    {K : Region} {c : ℝ} {Y : Set ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y})) :
    ∀ r : ℝ, Set.Pairwise Y
      (MeasureTheory.AEDisjoint volume on
        ((· +ᵥ verticalSlice K r) : ℝ → Set ℝ)) := by
  intro r y hy y' hy' hyy'
  apply Disjoint.aedisjoint
  rw [Set.disjoint_left]
  intro x hxy hxy'
  let sy : Tiling.Plane := (c : ℂ) + (y : ℂ) * Complex.I
  let sy' : Tiling.Plane := (c : ℂ) + (y' : ℂ) * Complex.I
  have hsy : sy ∈ {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
    exact ⟨by simp [sy], by simpa [sy] using hy⟩
  have hsy' : sy' ∈ {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
    exact ⟨by simp [sy'], by simpa [sy'] using hy'⟩
  have hsysy' : sy ≠ sy' := by
    intro heq
    apply hyy'
    simpa [sy, sy'] using congrArg Complex.im heq
  have hd : Disjoint (sy +ᵥ K.openCarrier) (sy' +ᵥ K.openCarrier) :=
    (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K _).mp hpacking
      hsy hsy' hsysy'
  rw [Set.disjoint_left] at hd
  refine hd (a := (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I)) ?_ ?_
  · change x ∈ y +ᵥ verticalSlice K r at hxy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxy ⊢
    rw [verticalSlice] at hxy
    change r + ((-y + x : ℝ) : ℂ) * Complex.I ∈ K.openCarrier at hxy
    have heq : -sy + (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I) =
        r + ((-y + x : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [sy]
    change -sy + (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I) ∈ K.openCarrier
    rwa [heq]
  · change x ∈ y' +ᵥ verticalSlice K r at hxy'
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxy' ⊢
    rw [verticalSlice] at hxy'
    change r + ((-y' + x : ℝ) : ℂ) * Complex.I ∈ K.openCarrier at hxy'
    have heq : -sy' + (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I) =
        r + ((-y' + x : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [sy']
    change -sy' + (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I) ∈ K.openCarrier
    rwa [heq]

private theorem reconstruct_extremalFibre
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : Continuous.VerticalPlate K T) (a r₀ : ℝ)
    (hr₀ : r₀ ∉ K.vertexFinset.image Complex.re)
    (hB₀ : (verticalSlice K r₀).Nonempty)
    (hseed : LineTiles (verticalSlice K r₀)
        (Complex.im '' extremalFibre P a))
    (hMass : ∀ r s : ℝ,
      r ∉ K.vertexFinset.image Complex.re →
      s ∉ K.vertexFinset.image Complex.re →
      (verticalSlice K r).Nonempty →
      (verticalSlice K s).Nonempty →
      (volume (verticalSlice K r)).toReal =
        (volume (verticalSlice K s)).toReal) :
    IsCenterColumn Axis.vertical K (extremalFibre P a) := by
  let C : Set Tiling.Plane := extremalFibre P a
  let Y : Set ℝ := Complex.im '' C
  have hY : Y.Nonempty := by
    obtain ⟨x, hx⟩ := hseed.2.2.2.2.exists
    obtain ⟨y, hy⟩ := hx.mp (Set.mem_univ x)
    obtain ⟨z, hz, hzy⟩ := y.property
    refine ⟨z.im, ?_⟩
    exact ⟨z, hz, rfl⟩
  have hCY : C = {z : Tiling.Plane | z.re = a ∧ z.im ∈ Y} := by
    ext z
    constructor
    · intro hz
      change z ∈ P.centres ∧ z.re = a at hz
      refine ⟨hz.2, ?_⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨hzre, ⟨w, hwC, hwim⟩⟩
      change w ∈ P.centres ∧ w.re = a at hwC
      have hzim : z.im = w.im := hwim.symm
      have hz : z = w := by
        apply Complex.ext
        · simp [hzre, hwC.2]
        · exact hzim
      change z ∈ P.centres ∧ z.re = a
      simpa [hz] using hwC
  have hCsubT : C ⊆ T := by
    intro z hz
    change z ∈ P.centres ∧ z.re = a at hz
    rcases hz.1 with ⟨t, ht, rfl⟩
    exact t.2
  have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements C) := by
    intro p hp q hq hpq
    have hpT : p ∈ K.toPolygonalRegion.placements T := by
      change p.1 ∈ T
      exact hCsubT hp
    have hqT : q ∈ K.toPolygonalRegion.placements T := by
      change q.1 ∈ T
      exact hCsubT hq
    exact hTile.2.1 hpT hqT hpq
  have hpair : ∀ r : ℝ, Set.Pairwise Y
      (MeasureTheory.AEDisjoint volume on
        ((· +ᵥ verticalSlice K r) : ℝ → Set ℝ)) := by
    intro r
    exact columnPacking_slicePacking (K := K) (c := a) (Y := Y)
      (hCY ▸ hpacking) r
  have hBfinite : IsFiniteIntervalRegion (verticalSlice K r₀) :=
    (Region.verticalSlice_finiteIntervals K hr₀).1
  have hBpositive : 0 < (volume (verticalSlice K r₀)).toReal :=
    ColumnSlices.finiteIntervalRegion_volume_toReal_pos hBfinite hB₀
  obtain ⟨p, hp, hperiod⟩ :=
    FiniteInterval.exists_positiveLinePeriod hBfinite hBpositive hseed
  have htiles : ∀ r : ℝ,
      r ∉ K.vertexFinset.image Complex.re →
      (verticalSlice K r).Nonempty → LineTiles (verticalSlice K r) Y := by
    intro r hr hBr
    have hB'r := (Region.verticalSlice_finiteIntervals K hr).1
    have hpackr := hpair r
    apply Foundations.periodicPacking_tiles_of_measure_eq
      hBfinite hB'r hseed hp hperiod hpackr
    exact (hMass r₀ r hr₀ hr hB₀ hBr).symm
  apply (Foundations.centerColumn_iff_genericSlices
    (C := C) (c := a) (Y := Y) hCY hY hpacking).mpr
  intro r hr hBr
  simpa only [verticalSlice, ColumnSlices.verticalSlice] using htiles r hr hBr

private theorem extremalFibre_isCenterColumn_of_equalSliceMass
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : Continuous.VerticalPlate K T) (a r₀ : ℝ)
    (_ha : IsLeast (Complex.re '' P.centres) a)
    (hr₀ : r₀ ∉ K.vertexFinset.image Complex.re)
    (hB₀ : (verticalSlice K r₀).Nonempty)
    (hseed : LineTiles (verticalSlice K r₀)
        (Complex.im '' extremalFibre P a))
    (hMass : ∀ r s : ℝ,
      r ∉ K.vertexFinset.image Complex.re →
      s ∉ K.vertexFinset.image Complex.re →
      (verticalSlice K r).Nonempty →
      (verticalSlice K s).Nonempty →
      (volume (verticalSlice K r)).toReal =
        (volume (verticalSlice K s)).toReal) :
    IsCenterColumn Axis.vertical K (extremalFibre P a) := by
  exact reconstruct_extremalFibre hTile P a r₀ hr₀ hB₀ hseed hMass

private theorem upperExtremalFibre_isCenterColumn_of_equalSliceMass
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : Continuous.VerticalPlate K T) (a r₀ : ℝ)
    (_ha : IsGreatest (Complex.re '' P.centres) a)
    (hr₀ : r₀ ∉ K.vertexFinset.image Complex.re)
    (hB₀ : (verticalSlice K r₀).Nonempty)
    (hseed : LineTiles (verticalSlice K r₀)
        (Complex.im '' extremalFibre P a))
    (hMass : ∀ r s : ℝ,
      r ∉ K.vertexFinset.image Complex.re →
      s ∉ K.vertexFinset.image Complex.re →
      (verticalSlice K r).Nonempty →
      (verticalSlice K s).Nonempty →
      (volume (verticalSlice K r)).toReal =
        (volume (verticalSlice K s)).toReal) :
    IsCenterColumn Axis.vertical K (extremalFibre P a) := by
  exact reconstruct_extremalFibre hTile P a r₀ hr₀ hB₀ hseed hMass



private structure NormalizedPlateData
    (K : Region) (T : Set Tiling.Plane)
    (P : Continuous.VerticalPlate K T)
    (v0 t0 : Tiling.Plane)
    (C : Approximation.ApproximationContext.{0}) where
  centreEquiv : ↥T ≃ ↥C.centres
  centreEquiv_apply : ∀ t : ↥T,
    (centreEquiv t : Tiling.Plane) = -t0 + t.1
  properContact_iff : ∀ s t : ↥T,
    Continuous.HorizontalProperContact K s.1 t.1 ↔
      Continuous.HorizontalProperContact C.region
        (centreEquiv s).1 (centreEquiv t).1
  normalizedPlate : Continuous.VerticalPlate C.region C.centres
  normalized_centres : normalizedPlate.centres = (-t0) +ᵥ P.centres
  normalized_support : normalizedPlate.support =
    (-(v0 + t0)) +ᵥ P.support
  normalized_base : normalizedPlate.base =
    {x : ℝ | ∃ y ∈ P.base, x = y - (v0 + t0).re}
  bddBelow_iff : BddBelow normalizedPlate.base ↔ BddBelow P.base
  bddAbove_iff : BddAbove normalizedPlate.base ↔ BddAbove P.base
  least_iff : ∀ a : ℝ,
    IsLeast (Complex.re '' normalizedPlate.centres) (a - t0.re) ↔
      IsLeast (Complex.re '' P.centres) a
  greatest_iff : ∀ a : ℝ,
    IsGreatest (Complex.re '' normalizedPlate.centres) (a - t0.re) ↔
      IsGreatest (Complex.re '' P.centres) a
  extremalFibre_eq : ∀ a : ℝ,
    extremalFibre normalizedPlate (a - t0.re) =
      (-t0) +ᵥ extremalFibre P a
  verticalSlice_eq : ∀ r : ℝ,
    verticalSlice C.region (r - v0.re) =
      (-v0.im) +ᵥ verticalSlice K r
  verticalSlice_generic_iff : ∀ r : ℝ,
    r - v0.re ∉ C.region.vertexFinset.image Complex.re ↔
      r ∉ K.vertexFinset.image Complex.re
  verticalSlice_nonempty_iff : ∀ r : ℝ,
    (verticalSlice C.region (r - v0.re)).Nonempty ↔
      (verticalSlice K r).Nonempty
  verticalSlice_mass_eq : ∀ r : ℝ,
    (volume (verticalSlice C.region (r - v0.re))).toReal =
      (volume (verticalSlice K r)).toReal
  normalized_tilesOn : TilesOn C.region C.centres Set.univ

private theorem point_vadd_univ (b : Tiling.Plane) :
    b +ᵥ (Set.univ : Set Tiling.Plane) = Set.univ := by
  ext z
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_univ]

private theorem translated_slice_point
    (v0 : Tiling.Plane) (r y : ℝ) :
    -(-v0) + ((r - v0.re : ℂ) + (y : ℂ) * Complex.I) =
      (r : ℂ) + ((y + v0.im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  · ring
  · ring

private theorem verticalSlice_eq_translate
    {K C : Region} (v0 : Tiling.Plane) (r : ℝ)
    (hcarrier : C.openCarrier = (-v0) +ᵥ K.openCarrier) :
    verticalSlice C (r - v0.re) = (-v0.im) +ᵥ verticalSlice K r := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change (-(-v0.im) + y) ∈ verticalSlice K r
    rw [show -(-v0.im) + y = y + v0.im by ring]
    have hyC : ((r - v0.re : ℂ) + (y : ℂ) * Complex.I) ∈ C.openCarrier := by
      simpa [verticalSlice] using hy
    rw [hcarrier] at hyC
    have hyK : -(-v0) + ((r - v0.re : ℂ) + (y : ℂ) * Complex.I) ∈ K.openCarrier :=
      Set.mem_vadd_set_iff_neg_vadd_mem.mp hyC
    rw [translated_slice_point] at hyK
    simpa [verticalSlice] using hyK
  · intro hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    change (-(-v0.im) + y) ∈ verticalSlice K r at hy
    rw [show -(-v0.im) + y = y + v0.im by ring] at hy
    have hyK : (r : ℂ) + ((y + v0.im : ℝ) : ℂ) * Complex.I ∈ K.openCarrier := by
      simpa [verticalSlice] using hy
    have hyK' : -(-v0) + ((r - v0.re : ℂ) + (y : ℂ) * Complex.I) ∈ K.openCarrier := by
      rw [translated_slice_point]
      exact hyK
    have hyC' : ((r - v0.re : ℂ) + (y : ℂ) * Complex.I) ∈ (-v0) +ᵥ K.openCarrier :=
      Set.mem_vadd_set_iff_neg_vadd_mem.mpr hyK'
    have hyC : ((r - v0.re : ℂ) + (y : ℂ) * Complex.I) ∈ C.openCarrier := by
      rw [hcarrier]
      exact hyC'
    simpa [verticalSlice] using hyC

private theorem verticalSlice_nonempty_iff
    {K C : Region} (v0 : Tiling.Plane) (r : ℝ)
    (hcarrier : C.openCarrier = (-v0) +ᵥ K.openCarrier) :
    (verticalSlice C (r - v0.re)).Nonempty ↔ (verticalSlice K r).Nonempty := by
  rw [verticalSlice_eq_translate v0 r hcarrier]
  constructor
  · rintro ⟨y, hy⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    exact ⟨-(-v0.im) + y, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨-v0.im + y, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa using hy

private theorem verticalSlice_mass_eq
    {K C : Region} (v0 : Tiling.Plane) (r : ℝ)
    (hcarrier : C.openCarrier = (-v0) +ᵥ K.openCarrier) :
    (volume (verticalSlice C (r - v0.re))).toReal =
      (volume (verticalSlice K r)).toReal := by
  rw [verticalSlice_eq_translate v0 r hcarrier]
  rw [MeasureTheory.measure_vadd]

private theorem bddBelow_translate_set (Z : Set ℝ) (d : ℝ) :
    BddBelow {x : ℝ | ∃ y ∈ Z, x = y - d} ↔ BddBelow Z := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b + d, ?_⟩
    intro y hy
    have h := hb (show y - d ∈ {x : ℝ | ∃ z ∈ Z, x = z - d} from ⟨y, hy, rfl⟩)
    linarith
  · rintro ⟨b, hb⟩
    refine ⟨b - d, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    linarith [hb hy]

private theorem bddAbove_translate_set (Z : Set ℝ) (d : ℝ) :
    BddAbove {x : ℝ | ∃ y ∈ Z, x = y - d} ↔ BddAbove Z := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b + d, ?_⟩
    intro y hy
    have h := hb (show y - d ∈ {x : ℝ | ∃ z ∈ Z, x = z - d} from ⟨y, hy, rfl⟩)
    linarith
  · rintro ⟨b, hb⟩
    refine ⟨b - d, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    linarith [hb hy]

private theorem isLeast_translate_set (Z : Set ℝ) (d a : ℝ) :
    IsLeast {x : ℝ | ∃ y ∈ Z, x = y - d} (a - d) ↔ IsLeast Z a := by
  constructor
  · rintro ⟨ha, hle⟩
    refine ⟨?_, ?_⟩
    · rcases ha with ⟨y, hy, hya⟩
      have hya' : y = a := by linarith
      exact hya' ▸ hy
    · intro y hy
      have h := hle (show y - d ∈ {x : ℝ | ∃ z ∈ Z, x = z - d} from ⟨y, hy, rfl⟩)
      linarith
  · rintro ⟨ha, hle⟩
    refine ⟨(show a - d ∈ {x : ℝ | ∃ y ∈ Z, x = y - d} from ⟨a, ha, rfl⟩), ?_⟩
    rintro x ⟨y, hy, rfl⟩
    linarith [hle hy]

private theorem isGreatest_translate_set (Z : Set ℝ) (d a : ℝ) :
    IsGreatest {x : ℝ | ∃ y ∈ Z, x = y - d} (a - d) ↔ IsGreatest Z a := by
  constructor
  · rintro ⟨ha, hle⟩
    refine ⟨?_, ?_⟩
    · rcases ha with ⟨y, hy, hya⟩
      have hya' : y = a := by linarith
      exact hya' ▸ hy
    · intro y hy
      have h := hle (show y - d ∈ {x : ℝ | ∃ z ∈ Z, x = z - d} from ⟨y, hy, rfl⟩)
      linarith
  · rintro ⟨ha, hle⟩
    refine ⟨(show a - d ∈ {x : ℝ | ∃ y ∈ Z, x = y - d} from ⟨a, ha, rfl⟩), ?_⟩
    rintro x ⟨y, hy, rfl⟩
    linarith [hle hy]

private theorem normalizedPlateData_exists :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ (P : Continuous.VerticalPlate K T)
        (v0 : Tiling.Plane) (_hv0 : v0 ∈ K.vertices)
        (t0 : Tiling.Plane) (_ht0 : t0 ∈ T)
        (C : Approximation.ApproximationContext.{0}),
        C.region.openCarrier = (-v0) +ᵥ K.openCarrier →
        C.centres = (-t0) +ᵥ T →
        C.target = (-(v0 + t0)) +ᵥ (Set.univ : Set Tiling.Plane) →
        (TilesOn K T Set.univ ↔ TilesOn C.region C.centres C.target) →
        Nonempty (NormalizedPlateData
          K T P v0 t0 C) := by
  intro K T hTile P v0 _hv0 t0 _ht0 C hcarrier hcentres htarget hiff
  let hcarrier' : C.region.openCarrier =
      Tiling.AxisParallel.positiveSimilarity 1 (-v0) '' K.openCarrier := by
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
    exact hcarrier
  let hImage : Tiling.AxisParallel.positiveSimilarity 1 (-t0) '' T = C.centres := by
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
    exact hcentres.symm
  let e₀ := Continuous.positiveSimilarityCentreEquiv one_pos (-t0) (T := T)
  let e : (T : Set Tiling.Plane) ≃ (C.centres : Set Tiling.Plane) :=
    e₀.trans (Equiv.setCongr hImage)
  have heapply : ∀ t : T, (e t : Tiling.Plane) = -t0 + t.1 := by
    intro t
    change (Continuous.positiveSimilarityCentreEquiv one_pos (-t0) t :
      Tiling.Plane) = _
    simp only [Continuous.positiveSimilarityCentreEquiv_apply,
      Tiling.AxisParallel.positiveSimilarity, one_smul, add_comm]
  let g : Continuous.verticalPlateGraph K T ≃g
      Continuous.verticalPlateGraph C.region C.centres := by
    refine { toEquiv := e, map_rel_iff' := ?_ }
    intro a b
    simp only [Continuous.verticalPlateGraph, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, hrel⟩
      refine ⟨?_, ?_⟩
      · intro hab
        apply hne
        exact congrArg e hab
      · rcases hrel with hab | hba
        · exact Or.inl ((Continuous.horizontalProperContact_positiveSimilarity_iff
            (K := K) (R := C.region) (s := 1) (r := -v0) (c := -t0) one_pos
            hcarrier' a.1 b.1).mpr hab)
        · exact Or.inr ((Continuous.horizontalProperContact_positiveSimilarity_iff
            (K := K) (R := C.region) (s := 1) (r := -v0) (c := -t0) one_pos
            hcarrier' b.1 a.1).mpr hba)
    · rintro ⟨hne, hrel⟩
      refine ⟨?_, ?_⟩
      · intro hab
        apply hne
        exact e.injective hab
      · rcases hrel with hab | hba
        · exact Or.inl ((Continuous.horizontalProperContact_positiveSimilarity_iff
            (K := K) (R := C.region) (s := 1) (r := -v0) (c := -t0) one_pos
            hcarrier' a.1 b.1).mp hab)
        · exact Or.inr ((Continuous.horizontalProperContact_positiveSimilarity_iff
            (K := K) (R := C.region) (s := 1) (r := -v0) (c := -t0) one_pos
            hcarrier' b.1 a.1).mp hba)
  let Q : Continuous.VerticalPlate C.region C.centres := g.connectedComponentEquiv P
  have hQcentres : Q.centres = (-t0) +ᵥ P.centres := by
    have hmem : ∀ (A : SimpleGraph.ConnectedComponent
        (Continuous.verticalPlateGraph K T))
        (u : T), u ∈ A.supp ↔ g u ∈ (g.connectedComponentEquiv A).supp := by
      intro A u
      constructor
      · intro hu
        have hA : (Continuous.verticalPlateGraph K T).connectedComponentMk u = A :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff A u).mp hu
        have hB : (Continuous.verticalPlateGraph C.region C.centres).connectedComponentMk
            (g u) = g.connectedComponentEquiv A := by
          rw [← hA]
          rfl
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff
          (g.connectedComponentEquiv A) (g u)).mpr hB
      · intro hu
        have hB : (Continuous.verticalPlateGraph C.region C.centres).connectedComponentMk
            (g u) = g.connectedComponentEquiv A :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff
            (g.connectedComponentEquiv A) (g u)).mp hu
        have hA := (SimpleGraph.ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map
          (φ := g) (C := A) (v' := g u)).mpr hB
        change (Continuous.verticalPlateGraph K T).connectedComponentMk
          (g.symm (g u)) = A at hA
        simpa using hA
    ext z
    constructor
    · intro hz
      rcases hz with ⟨u, hu, huz⟩
      let t : T := e.symm u
      have het : e t = u := e.apply_symm_apply u
      have hQt : g t ∈ Q.supp := by
        change e t ∈ Q.supp
        rw [het]
        exact hu
      have hPt : t ∈ P.supp := (hmem P t).mpr hQt
      have hPt' : t.1 ∈ P.centres := ⟨t, hPt, rfl⟩
      refine ⟨t.1, hPt', ?_⟩
      have het' : (e t : Tiling.Plane) = u.1 := congrArg Subtype.val het
      rw [← huz, ← het']
      simpa [vadd_eq_add] using (heapply t).symm
    · intro hz
      rcases Set.mem_vadd_set.mp hz with ⟨w, hw, hzw⟩
      rcases hw with ⟨t, ht, rfl⟩
      let u : C.centres := e t
      have hPt : t ∈ P.supp := ht
      have hQt : g t ∈ Q.supp := (hmem P t).mp hPt
      refine ⟨u, hQt, ?_⟩
      change (e t : Tiling.Plane) = z
      calc
        (e t : Tiling.Plane) = -t0 + t.1 := heapply t
        _ = z := hzw
  have hQsupport : Q.support = (-(v0 + t0)) +ᵥ P.support := by
    change regularSupport C.region Q.centres = _
    rw [hQcentres]
    have h := Tiling.AxisParallel.positiveSimilarity_regularSupport_image
      (K := K) (R := C.region) (S := P.centres) (s := 1) (r := -v0)
      (c := -t0) one_pos hcarrier'
    have hadd : -v0 + -t0 = -(v0 + t0) := by abel
    rw [hadd] at h
    rw [P.support_eq_regularSupport]
    simpa only [positiveSimilarity_image_eq_vadd_smul, one_smul] using h
  have hQbase : Q.base = {x : ℝ | ∃ y ∈ P.base, x = y - (v0 + t0).re} := by
    change Complex.re '' Q.support = _
    rw [hQsupport]
    ext x
    simp only [Set.mem_image, Complex.add_re, Set.mem_ofPred_eq, sub_eq_add_neg]
    constructor
    · rintro ⟨w, hw, hwx⟩
      rcases Set.mem_vadd_set.mp hw with ⟨z, hz, hwz⟩
      refine ⟨z.re, ⟨z, hz, rfl⟩, ?_⟩
      rw [← hwz] at hwx
      change (-(v0 + t0) + z).re = x at hwx
      simp only [Complex.add_re, Complex.neg_re] at hwx
      linarith
    · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
      refine ⟨-(v0 + t0) + z, ?_, ?_⟩
      · exact Set.mem_vadd_set.mpr ⟨z, hz, rfl⟩
      · simp only [Complex.add_re, Complex.neg_re]
        linarith
  have hreal : Complex.re '' Q.centres =
      {x : ℝ | ∃ y ∈ Complex.re '' P.centres, x = y - t0.re} := by
    rw [hQcentres]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases Set.mem_vadd_set.mp hz with ⟨y, hy, rfl⟩
      refine ⟨y.re, ⟨y, hy, rfl⟩, ?_⟩
      simp only [vadd_eq_add, Complex.add_re, Complex.neg_re]
      ring
    · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
      refine ⟨-t0 + z, ?_, ?_⟩
      · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa using hz
      · simp only [Complex.add_re, Complex.neg_re]
        linarith
  have hverts : C.region.vertices = (-v0) +ᵥ K.vertices := by
    calc
      C.region.vertices = Tiling.AxisParallel.positiveSimilarity 1 (-v0) '' K.vertices := by
        apply Tiling.AxisParallel.positiveSimilarity_vertices_image one_pos
        exact hcarrier'
      _ = (-v0) +ᵥ K.vertices := by
        rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
  have hgeneric : ∀ r : ℝ,
      r - v0.re ∉ C.region.vertexFinset.image Complex.re ↔
        r ∉ K.vertexFinset.image Complex.re := by
    intro r
    constructor
    · intro hC hrK
      apply hC
      rcases Finset.mem_image.mp hrK with ⟨q, hq, hqr⟩
      have hqv : q ∈ K.vertices := by
        have hq' : q ∈ (K.vertexFinset : Set Tiling.Plane) := hq
        rw [K.coe_vertexFinset] at hq'
        exact hq'
      have hcv : -v0 + q ∈ C.region.vertices := by
        rw [hverts]
        apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
        simpa [vadd_eq_add, add_assoc] using hqv
      have hcvf : -v0 + q ∈ C.region.vertexFinset := by
        have hcv' : -v0 + q ∈ (C.region.vertexFinset : Set Tiling.Plane) := by
          rw [C.region.coe_vertexFinset]
          exact hcv
        exact hcv'
      refine Finset.mem_image.mpr ⟨-v0 + q, hcvf, ?_⟩
      simp only [Complex.add_re, Complex.neg_re]
      linarith
    · intro hK hrC
      apply hK
      rcases Finset.mem_image.mp hrC with ⟨v, hv, hvr⟩
      have hvv : v ∈ C.region.vertices := by
        have hv' : v ∈ (C.region.vertexFinset : Set Tiling.Plane) := hv
        rw [C.region.coe_vertexFinset] at hv'
        exact hv'
      have hqv : -(-v0) + v ∈ K.vertices := by
        rw [hverts] at hvv
        have hvv' := Set.mem_vadd_set_iff_neg_vadd_mem.mp hvv
        simpa [vadd_eq_add] using hvv'
      have hqf : -(-v0) + v ∈ K.vertexFinset := by
        have hq' : -(-v0) + v ∈ (K.vertexFinset : Set Tiling.Plane) := by
          rw [K.coe_vertexFinset]
          exact hqv
        exact hq'
      refine Finset.mem_image.mpr ⟨-(-v0) + v, hqf, ?_⟩
      simp only [Complex.add_re, Complex.neg_re]
      linarith
  have htiles : TilesOn C.region C.centres Set.univ := by
    have h := hiff.mp hTile
    rw [htarget, point_vadd_univ] at h
    exact h
  refine ⟨{
    centreEquiv := e
    centreEquiv_apply := heapply
    properContact_iff := by
      intro s t
      have h := Continuous.horizontalProperContact_positiveSimilarity_iff
        (K := K) (R := C.region) (s := 1) (r := -v0) (c := -t0) one_pos
        hcarrier' s.1 t.1
      rw [heapply s, heapply t]
      simpa only [Tiling.AxisParallel.positiveSimilarity, one_smul, add_comm] using h
    normalizedPlate := Q
    normalized_centres := hQcentres
    normalized_support := hQsupport
    normalized_base := hQbase
    bddBelow_iff := by rw [hQbase]; exact bddBelow_translate_set P.base (v0 + t0).re
    bddAbove_iff := by rw [hQbase]; exact bddAbove_translate_set P.base (v0 + t0).re
    least_iff := by
      intro a
      rw [hreal]
      exact isLeast_translate_set (Complex.re '' P.centres) t0.re a
    greatest_iff := by
      intro a
      rw [hreal]
      exact isGreatest_translate_set (Complex.re '' P.centres) t0.re a
    extremalFibre_eq := by
      intro a
      ext z
      constructor
      · intro hz
        change z ∈ Q.centres ∧ z.re = a - t0.re at hz
        have hzQ : z ∈ Q.centres := hz.1
        have hzre : z.re = a - t0.re := hz.2
        rw [hQcentres] at hzQ
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        change -(-t0) + z ∈ extremalFibre P a
        refine ⟨Set.mem_vadd_set_iff_neg_vadd_mem.mp hzQ, ?_⟩
        simp only [Complex.add_re, Complex.neg_re] at hzre ⊢
        linarith
      · intro hz
        change z ∈ (-t0) +ᵥ extremalFibre P a at hz
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz
        change -(-t0) + z ∈ extremalFibre P a at hz
        change z ∈ Q.centres ∧ z.re = a - t0.re
        rw [hQcentres]
        refine ⟨Set.mem_vadd_set_iff_neg_vadd_mem.mpr hz.1, ?_⟩
        have hzre := hz.2
        change (-(-t0) + z).re = a at hzre
        simp only [Complex.add_re, Complex.neg_re] at hzre
        linarith
    verticalSlice_eq := by
      intro r
      simpa only [verticalSlice] using
        verticalSlice_eq_translate v0 r hcarrier
    verticalSlice_generic_iff := hgeneric
    verticalSlice_nonempty_iff := by
      intro r
      simpa only [verticalSlice] using
        verticalSlice_nonempty_iff v0 r hcarrier
    verticalSlice_mass_eq := by
      intro r
      simpa only [verticalSlice] using
        verticalSlice_mass_eq v0 r hcarrier
    normalized_tilesOn := htiles
  }⟩


private def transportedPlateCentres
    {C : Approximation.ApproximationContext.{0}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : Approximation.CoordinateDeformation C phi}
    (R : Approximation.TwoStageDeformationSupportTransport C phi D)
    (P : Continuous.VerticalPlate C.region C.centres) : Set Tiling.Plane :=
  Approximation.deformedCenterCarrierOn R.fullCenters
    {t : ↥C.centres | (t : Tiling.Plane) ∈ P.centres}

private theorem lowerTransportedPlateBase_bound :
  ∀ {C : Approximation.ApproximationContext.{0}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : Approximation.CoordinateDeformation C phi}
    (R : Approximation.TwoStageDeformationSupportTransport C phi D)
    (P : Continuous.VerticalPlate C.region C.centres)
    (t0 : ↥C.centres) (Xphi : Set ℝ),
    (∀ z ∈ transportedPlateCentres R P, (R.fullCenters t0).re ≤ z.re) →
    regularSupport D.deformedRegion (transportedPlateCentres R P) =
      Complex.re ⁻¹' Xphi →
    BddBelow Xphi := by
  intro C phi D R P t0 Xphi hcentres hsupport
  let S := transportedPlateCentres R P
  have hSsub : S ⊆ Approximation.deformedCenterCarrier R.fullCenters := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨t, rfl⟩
  have hpack : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements S) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint D.deformedRegion S).mpr
    intro s hs t ht hst
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint D.deformedRegion
      (Approximation.deformedCenterCarrier R.fullCenters)).mp R.full_tilesOn.2.1
    · exact hSsub hs
    · exact hSsub ht
    · exact hst
  obtain ⟨u, hu, huv⟩ :=
    D.deformedRegion.isPolygonal.isCompact.exists_isMinOn
      D.deformedRegion.nonempty Complex.continuous_re.continuousOn
  have hregSub : regularSupport D.deformedRegion S ⊆
      closure (openUnion D.deformedRegion S) := by
    intro z hz
    exact interior_subset hz
  have hbound : ∀ x ∈ Xphi, u.re + (R.fullCenters t0).re ≤ x := by
    intro x hx
    have hz : ((x : ℝ) : ℂ) ∈ regularSupport D.deformedRegion S := by
      rw [hsupport]
      simp [hx]
    have hzcl : ((x : ℝ) : ℂ) ∈ closure (openUnion D.deformedRegion S) :=
      hregSub hz
    rw [closure_openUnion_eq_iUnion_support hpack] at hzcl
    obtain ⟨s, hzs⟩ := Set.mem_iUnion.mp hzcl
    rw [mem_vadd_set] at hzs
    obtain ⟨w, hw, hzw⟩ := hzs
    have hsc := hcentres s.1 (by
      change s.1 ∈ S
      exact s.2)
    have hwmin := huv hw
    change u.re ≤ w.re at hwmin
    have hre := congrArg Complex.re hzw
    simp only [vadd_eq_add, Complex.add_re] at hre
    have hxre : (↑x : ℂ).re = x := by simp
    rw [hxre] at hre
    have hsum := add_le_add hsc hwmin
    rw [hre] at hsum
    linarith [hsum]
  exact ⟨u.re + (R.fullCenters t0).re, hbound⟩

private theorem upperTransportedPlateBase_bound :
  ∀ {C : Approximation.ApproximationContext.{0}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : Approximation.CoordinateDeformation C phi}
    (R : Approximation.TwoStageDeformationSupportTransport C phi D)
    (P : Continuous.VerticalPlate C.region C.centres)
    (t0 : ↥C.centres) (Xphi : Set ℝ),
    (∀ z ∈ transportedPlateCentres R P, z.re ≤ (R.fullCenters t0).re) →
    regularSupport D.deformedRegion (transportedPlateCentres R P) =
      Complex.re ⁻¹' Xphi →
    BddAbove Xphi := by
  intro C phi D R P t0 Xphi hcentres hsupport
  let S := transportedPlateCentres R P
  have hSsub : S ⊆ Approximation.deformedCenterCarrier R.fullCenters := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨t, rfl⟩
  have hpack : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements S) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint D.deformedRegion S).mpr
    intro s hs t ht hst
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint D.deformedRegion
      (Approximation.deformedCenterCarrier R.fullCenters)).mp R.full_tilesOn.2.1
    · exact hSsub hs
    · exact hSsub ht
    · exact hst
  obtain ⟨u, hu, huv⟩ :=
    D.deformedRegion.isPolygonal.isCompact.exists_isMaxOn
      D.deformedRegion.nonempty Complex.continuous_re.continuousOn
  have hregSub : regularSupport D.deformedRegion S ⊆
      closure (openUnion D.deformedRegion S) := by
    intro z hz
    exact interior_subset hz
  have hbound : ∀ x ∈ Xphi, x ≤ u.re + (R.fullCenters t0).re := by
    intro x hx
    have hz : ((x : ℝ) : ℂ) ∈ regularSupport D.deformedRegion S := by
      rw [hsupport]
      simp [hx]
    have hzcl : ((x : ℝ) : ℂ) ∈ closure (openUnion D.deformedRegion S) :=
      hregSub hz
    rw [closure_openUnion_eq_iUnion_support hpack] at hzcl
    obtain ⟨s, hzs⟩ := Set.mem_iUnion.mp hzcl
    rw [mem_vadd_set] at hzs
    obtain ⟨w, hw, hzw⟩ := hzs
    have hsc := hcentres s.1 (by
      change s.1 ∈ S
      exact s.2)
    have hwmax := huv hw
    change w.re ≤ u.re at hwmax
    have hre := congrArg Complex.re hzw
    simp only [vadd_eq_add, Complex.add_re] at hre
    have hxre : (↑x : ℂ).re = x := by simp
    rw [hxre] at hre
    have hsum := add_le_add hwmax hsc
    have hsum' : x ≤ u.re + (R.fullCenters t0).re := by
      calc
        x = (s.1 : Tiling.Plane).re + w.re := hre.symm
        _ ≤ u.re + (R.fullCenters t0).re := by simpa [add_comm] using hsum
    linarith [hsum']
  exact ⟨u.re + (R.fullCenters t0).re, hbound⟩




open Tiling Tiling.AxisParallel
open Tiling.AxisParallel.Approximation

private abbrev hSaturates_telescope : Prop :=
  ∀ {K : Region} {T S : Set Tiling.Plane} {X : Set ℝ},
    TilesOn K T Set.univ →
    Tiling.RationalPolygonal.IsRelativelyRational K.toPolygonalRegion →
    S ⊆ T → IsOpen X → interior (closure X) = X →
    regularSupport K S = Complex.re ⁻¹' X →
    (BddBelow X ∨ BddAbove X) →
    ∀ Q : Continuous.VerticalPlate K T,
      (Q.centres ∩ S).Nonempty →
        Q.centres ⊆ S ∧ Continuous.IsVerticalColumn Q

private theorem deformedRegion_isRelativelyRational
    {C : Approximation.ApproximationContext}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : Approximation.CoordinateDeformation C phi) :
    Tiling.RationalPolygonal.IsRelativelyRational D.deformedRegion.toPolygonalRegion := by
  obtain ⟨v, hv, w, hw, hmax, hdiam⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair D.deformedRegion
  refine ⟨v, hv, ?_⟩
  intro z hz
  obtain ⟨vx, vy, hvx, hvy⟩ := D.rational_vertices v hv
  obtain ⟨zx, zy, hzx, hzy⟩ := D.rational_vertices z hz
  refine ⟨zx - vx, zy - vy, ?_, ?_⟩
  · rw [Complex.sub_re, hvx, hzx]
    norm_num
  · rw [Complex.sub_im, hvy, hzy]
    norm_num

open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous

/-! A slab can only meet one side of the continuous plate partition.  The
remaining (genuine) point in this helper is that a non-column plate has a
positive horizontal period, supplied by C04; a one-sided base cannot contain
all of its translates. -/
private theorem rationalOneSidedSlab_saturatesColumns :
    ∀ {K : Region} {T S : Set Tiling.Plane} {X : Set ℝ},
      TilesOn K T Set.univ →
      Tiling.RationalPolygonal.IsRelativelyRational K.toPolygonalRegion →
      S ⊆ T → IsOpen X → interior (closure X) = X →
    regularSupport K S = Complex.re ⁻¹' X →
      (BddBelow X ∨ BddAbove X) →
      ∀ Q : Continuous.VerticalPlate K T,
        (Q.centres ∩ S).Nonempty →
          Q.centres ⊆ S ∧ Continuous.IsVerticalColumn Q := by
  exact Tiling.AxisParallel.Continuous.rationalOneSidedSlab_saturatesColumns

private abbrev RationalDeformationConstructor :=
  ∀ (C : Approximation.ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    Approximation.IsGoodApproximation C phi →
      Nonempty (Approximation.CoordinateDeformation C phi)

private abbrev SupportTransportConstructor :=
  ∀ (C : Approximation.ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Approximation.CoordinateDeformation C phi),
    TilesOn C.region C.centres Set.univ →
      Nonempty (Approximation.TwoStageDeformationSupportTransport C phi D)

private def transportedExtremalFibre
    {C : Approximation.ApproximationContext}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : Approximation.CoordinateDeformation C phi}
    (R : Approximation.TwoStageDeformationSupportTransport C phi D)
    (P : Continuous.VerticalPlate C.region C.centres) (a : ℝ) : Set Tiling.Plane :=
  Approximation.deformedCenterCarrierOn R.fullCenters
    {t : ↥C.centres | (t : Tiling.Plane) ∈ P.centres ∧ t.1.re = a}

private abbrev SubfamilySupportTransportTheorem :=
  ∀ {C : Approximation.ApproximationContext.{0}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : Approximation.CoordinateDeformation C phi}
    (R : Approximation.TwoStageDeformationSupportTransport C phi D)
    (S : Set Tiling.Plane) (_hS : S ⊆ C.centres)
    (X : Set ℝ) (_hXopen : IsOpen X)
    (_hXregular : interior (closure X) = X)
    (_hSupport : regularSupport C.region S = Complex.re ⁻¹' X),
    ∃ (Xphi : Set ℝ) (boundaryLift : ↥(frontier X) → C.coordinateSpace),
      IsOpen Xphi ∧ interior (closure Xphi) = Xphi ∧
      (∀ x, (boundaryLift x : ℝ) = x.1) ∧
      regularSupport D.deformedRegion
        (Approximation.deformedCenterCarrierOn R.fullCenters
          {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) =
        Complex.re ⁻¹' Xphi ∧
      frontier Xphi = Approximation.mapScalarSet phi (Set.range boundaryLift) ∧
      ∀ a b : ↥(frontier X), a.1 < b.1 →
        Ioo a.1 b.1 ∩ frontier X = ∅ →
        (Ioo a.1 b.1 ⊆ X ↔
          Ioo (Approximation.mapScalar phi (boundaryLift a))
            (Approximation.mapScalar phi (boundaryLift b)) ⊆ Xphi)


private abbrev LowerTransportedExtremalFibreBridge :=
  ∀ (_supportTransport : SubfamilySupportTransportTheorem)
    {C : Approximation.ApproximationContext.{0}}
    (_hTile : TilesOn C.region C.centres Set.univ)
    (P : Continuous.VerticalPlate C.region C.centres)
    (t0 : ↥C.centres) (_ht0 : (t0.1 : Tiling.Plane) ∈ P.centres)
    (_hLeast : IsLeast (Complex.re '' P.centres) t0.1.re)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : Approximation.CoordinateDeformation C phi)
    (R : Approximation.TwoStageDeformationSupportTransport C phi D)
    (_hBaseOpen : IsOpen P.base)
    (_hBaseRegular : interior (closure P.base) = P.base)
    (_hSupport : regularSupport C.region P.centres = Complex.re ⁻¹' P.base)
    (eta : ℝ) (_hEta : 0 < eta)
    (_hGap : ∀ t : ↥C.centres,
      (t.1 : Tiling.Plane) ∈ P.centres → t0.1.re < t.1.re →
      (R.fullCenters t0).re + eta ≤ (R.fullCenters t).re),
    ∃ (Xphi : Set ℝ) (boundaryLift : ↥(frontier P.base) → C.coordinateSpace),
      IsOpen Xphi ∧ interior (closure Xphi) = Xphi ∧
      (∀ x, (boundaryLift x : ℝ) = x.1) ∧
      regularSupport D.deformedRegion (transportedPlateCentres R P) =
        Complex.re ⁻¹' Xphi ∧
      frontier Xphi = Approximation.mapScalarSet phi (Set.range boundaryLift) ∧
      (∀ a b : ↥(frontier P.base), a.1 < b.1 →
        Ioo a.1 b.1 ∩ frontier P.base = ∅ →
        (Ioo a.1 b.1 ⊆ P.base ↔
          Ioo (Approximation.mapScalar phi (boundaryLift a))
            (Approximation.mapScalar phi (boundaryLift b)) ⊆ Xphi)) ∧
      BddBelow Xphi ∧
      transportedExtremalFibre R P t0.1.re =
        {z ∈ transportedPlateCentres R P | z.re = (R.fullCenters t0).re} ∧
      IsCenterColumn Axis.vertical D.deformedRegion
        (transportedExtremalFibre R P t0.1.re)

private abbrev UpperTransportedExtremalFibreBridge :=
  ∀ (_supportTransport : SubfamilySupportTransportTheorem)
    {C : Approximation.ApproximationContext.{0}}
    (_hTile : TilesOn C.region C.centres Set.univ)
    (P : Continuous.VerticalPlate C.region C.centres)
    (t0 : ↥C.centres) (_ht0 : (t0.1 : Tiling.Plane) ∈ P.centres)
    (_hGreatest : IsGreatest (Complex.re '' P.centres) t0.1.re)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : Approximation.CoordinateDeformation C phi)
    (R : Approximation.TwoStageDeformationSupportTransport C phi D)
    (_hBaseOpen : IsOpen P.base)
    (_hBaseRegular : interior (closure P.base) = P.base)
    (_hSupport : regularSupport C.region P.centres = Complex.re ⁻¹' P.base)
    (eta : ℝ) (_hEta : 0 < eta)
    (_hGap : ∀ t : ↥C.centres,
      (t.1 : Tiling.Plane) ∈ P.centres → t.1.re < t0.1.re →
      (R.fullCenters t).re + eta ≤ (R.fullCenters t0).re),
    ∃ (Xphi : Set ℝ) (boundaryLift : ↥(frontier P.base) → C.coordinateSpace),
      IsOpen Xphi ∧ interior (closure Xphi) = Xphi ∧
      (∀ x, (boundaryLift x : ℝ) = x.1) ∧
      regularSupport D.deformedRegion (transportedPlateCentres R P) =
        Complex.re ⁻¹' Xphi ∧
      frontier Xphi = Approximation.mapScalarSet phi (Set.range boundaryLift) ∧
      (∀ a b : ↥(frontier P.base), a.1 < b.1 →
        Ioo a.1 b.1 ∩ frontier P.base = ∅ →
        (Ioo a.1 b.1 ⊆ P.base ↔
          Ioo (Approximation.mapScalar phi (boundaryLift a))
            (Approximation.mapScalar phi (boundaryLift b)) ⊆ Xphi)) ∧
      BddAbove Xphi ∧
      transportedExtremalFibre R P t0.1.re =
        {z ∈ transportedPlateCentres R P | z.re = (R.fullCenters t0).re} ∧
      IsCenterColumn Axis.vertical D.deformedRegion
        (transportedExtremalFibre R P t0.1.re)

private def basisWeight
    (C : Approximation.ApproximationContext.{0}) (z : C.coordinateSpace) : ℝ :=
  ∑ j ∈ (C.basis.repr z).support, |((C.basis.repr z j) : ℝ)|

private theorem mapScalar_sub_eq_sum
    (C : Approximation.ApproximationContext.{0})
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) (z : C.coordinateSpace) :
    Approximation.mapScalar φ z - (z : ℝ) =
      ∑ j ∈ (C.basis.repr z).support,
        ((C.basis.repr z j) : ℝ) *
          (Approximation.mapScalar φ (C.basis j) -
            ((C.basis j : C.coordinateSpace) : ℝ)) := by
  have hz :
      ∑ j ∈ (C.basis.repr z).support,
        (C.basis.repr z j) • C.basis j = z := by
    simpa only [C.basis.repr_symm_apply, Finsupp.linearCombination_apply,
      Finsupp.sum] using C.basis.repr.symm_apply_apply z
  have hφrat := congrArg φ hz
  have hcoe := congrArg (fun w : C.coordinateSpace ↦ (w : ℝ)) hz
  have hφ :
      ((φ z) : ℝ) = ∑ j ∈ (C.basis.repr z).support,
        ((C.basis.repr z j) : ℝ) * ((φ (C.basis j)) : ℝ) := by
    rw [← hφrat]
    simp only [map_sum, LinearMap.map_smul_of_tower, Rat.smul_def,
      Rat.cast_sum, Rat.cast_mul, Rat.cast_id]
  have hval :
      (z : ℝ) = ∑ j ∈ (C.basis.repr z).support,
        ((C.basis.repr z j) : ℝ) * ((C.basis j : C.coordinateSpace) : ℝ) := by
    rw [← hcoe]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Rat.smul_def]
  simp only [Approximation.mapScalar]
  rw [hφ, hval]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

private theorem mapScalar_tendsto_identity_of_epsilon
    (C : Approximation.ApproximationContext.{0})
    (epsilon : ℕ → ℝ) (phi : ∀ _n, C.coordinateSpace →ₗ[ℚ] ℚ)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hphi : ∀ n, Approximation.IsEpsilonApproximation C (epsilon n) (phi n))
    (z : C.coordinateSpace) :
    Tendsto (fun n ↦ Approximation.mapScalar (phi n) z)
      atTop (nhds (z : ℝ)) := by
  have hdiff (j : C.basisIndex) :
      Tendsto
        (fun n ↦ Approximation.mapScalar (phi n) (C.basis j) -
          ((C.basis j : C.coordinateSpace) : ℝ))
        atTop (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero
      (fun n ↦ Approximation.mapScalar (phi n) (C.basis j) -
        ((C.basis j : C.coordinateSpace) : ℝ))).mpr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    · simpa using hepsilon.neg
    · exact hepsilon
    · intro n
      rw [neg_le_iff_add_nonneg]
      change 0 ≤
        |Approximation.mapScalar (phi n) (C.basis j) -
          ((C.basis j : C.coordinateSpace) : ℝ)| + epsilon n
      exact add_nonneg (abs_nonneg _) (le_of_lt (hphi n).epsilon_pos)
    · intro n
      exact le_of_lt ((hphi n).basis_close j)
  have hsum := tendsto_finsetSum
    (s := (C.basis.repr z).support)
    (fun j hj ↦ (hdiff j).const_mul ((C.basis.repr z j : ℚ) : ℝ))
  have hzero :
      Tendsto
        (fun n ↦ ∑ j ∈ (C.basis.repr z).support,
          ((C.basis.repr z j : ℚ) : ℝ) *
            (Approximation.mapScalar (phi n) (C.basis j) -
              ((C.basis j : C.coordinateSpace) : ℝ)))
        atTop (nhds 0) := by
    convert hsum using 1
    simp only [mul_zero, Finset.sum_const_zero]
  have hsub :
      Tendsto
        (fun n ↦ Approximation.mapScalar (phi n) z - (z : ℝ))
        atTop (nhds 0) := by
    have hfunSub :
        (fun n ↦ Approximation.mapScalar (phi n) z - (z : ℝ)) =
          (fun n ↦ ∑ j ∈ (C.basis.repr z).support,
            ((C.basis.repr z j : ℚ) : ℝ) *
              (Approximation.mapScalar (phi n) (C.basis j) -
                ((C.basis j : C.coordinateSpace) : ℝ))) := by
      funext n
      exact mapScalar_sub_eq_sum C (phi n) z
    rw [hfunSub]
    exact hzero
  have hadd := (tendsto_const_nhds.add hsub :
    Tendsto (fun n ↦ (z : ℝ) +
      (Approximation.mapScalar (phi n) z - (z : ℝ)))
      atTop (nhds ((z : ℝ) + 0)))
  have hfun :
      (fun n ↦ (z : ℝ) +
        (Approximation.mapScalar (phi n) z - (z : ℝ))) =
        (fun n ↦ Approximation.mapScalar (phi n) z) := by
    funext n
    ring
  rw [← hfun]
  simpa only [add_zero] using hadd

private theorem firstHomeomorph_generic
    {C : Approximation.ApproximationContext.{0}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
  (D : Approximation.CoordinateDeformation C phi)
    {r : ℝ} (hr : r ∉ C.region.vertexFinset.image Complex.re) :
    D.firstHomeomorph r ∉ D.deformedRegion.vertexFinset.image Complex.re := by
  intro h
  have h' : D.firstHomeomorph r ∈ D.deformedRegion.vertexFinset.image Complex.re := h
  rcases Finset.mem_image.mp h' with ⟨w, hw, hwr⟩
  have hw' : w ∈ D.deformedRegion.vertices := by
    rw [← D.deformedRegion.coe_vertexFinset]
    exact hw
  rw [D.vertices_image] at hw'
  rcases hw' with ⟨v, hv, hvw⟩
  have hcoord : D.firstHomeomorph v.re = D.firstHomeomorph r := by
    calc
      D.firstHomeomorph v.re = (D.planarHomeomorph v).re := by
        simp [D.planarHomeomorph_apply]
      _ = w.re := by rw [hvw]
      _ = D.firstHomeomorph r := hwr
  have : v.re = r := D.firstHomeomorph.injective hcoord
  apply hr
  have hv' : v ∈ C.region.vertexFinset := by
    change v ∈ (C.region.vertexFinset : Set Tiling.Plane)
    rw [C.region.coe_vertexFinset]
    exact hv
  exact Finset.mem_image.mpr ⟨v, hv', this⟩

private theorem deformedVerticalSlice_nonempty_of_source
    {C : Approximation.ApproximationContext.{0}} {x : ℝ}
    (S : VerticalGenericSlicePresentation C.region x)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : Approximation.CoordinateDeformation C phi)
    (hsource : (verticalSlice C.region x).Nonempty) :
    (verticalSlice D.deformedRegion (D.firstHomeomorph x)).Nonempty := by
  rw [deformedVerticalSlice_eq_mappedPresentation S D]
  obtain ⟨y, hy⟩ := hsource
  have hy' : y ∈ Foundations.GenericSlices.verticalSlice C.region x := by
    change (x : ℂ) + (y : ℂ) * Complex.I ∈ C.region.openCarrier at hy
    change Complex.mk x y ∈ C.region.openCarrier
    convert hy using 1
    apply Complex.ext <;> simp
  rw [S.union_eq] at hy'
  simp only [Set.mem_iUnion] at hy'
  obtain ⟨i, hyi⟩ := hy'
  have hlow : D.secondHomeomorph (S.left i) =
      Approximation.mapScalar phi (presentationLowerCoord S i) := by
    have hv := D.vertex_agreement (S.lowerVertex i).1 (S.lowerVertex i).2
    rw [D.planarHomeomorph_apply] at hv
    have him := congrArg Complex.im hv
    have hcoord : presentationLowerCoord S i =
        ⟨(S.lowerVertex i).1.im,
          C.vertex_im_mem (S.lowerVertex i).1 (S.lowerVertex i).2⟩ := by
      apply Subtype.ext
      exact (S.lowerVertex_coord i).symm
    rw [hcoord]
    simpa [S.lowerVertex_coord, Approximation.mapScalar,
      Approximation.mapPoint, Approximation.ApproximationContext.vertexPoint] using him
  have hupp : D.secondHomeomorph (S.right i) =
      Approximation.mapScalar phi (presentationUpperCoord S i) := by
    have hv := D.vertex_agreement (S.upperVertex i).1 (S.upperVertex i).2
    rw [D.planarHomeomorph_apply] at hv
    have him := congrArg Complex.im hv
    have hcoord : presentationUpperCoord S i =
        ⟨(S.upperVertex i).1.im,
          C.vertex_im_mem (S.upperVertex i).1 (S.upperVertex i).2⟩ := by
      apply Subtype.ext
      exact (S.upperVertex_coord i).symm
    rw [hcoord]
    simpa [S.upperVertex_coord, Approximation.mapScalar,
      Approximation.mapPoint, Approximation.ApproximationContext.vertexPoint] using him
  refine ⟨D.secondHomeomorph y, Set.mem_iUnion.mpr ⟨i, ?_⟩⟩
  rw [← hlow, ← hupp]
  exact ⟨D.secondHomeomorph_strictMono hyi.1,
    D.secondHomeomorph_strictMono hyi.2⟩

private structure DeformedColumnComparisonSequence
    (C : Approximation.ApproximationContext.{0})
    (P : Continuous.VerticalPlate C.region C.centres)
    (t0 : ↥C.centres) (r s : ℝ) where
  epsilon : ℕ → ℝ
  epsilon_pos : ∀ n, 0 < epsilon n
  epsilon_tendsto_zero : Tendsto epsilon atTop (nhds 0)
  phi : ∀ _n, C.coordinateSpace →ₗ[ℚ] ℚ
  phi_isApproximation : ∀ n,
    Approximation.IsEpsilonApproximation C (epsilon n) (phi n)
  phi_good : ∀ n, Approximation.IsGoodApproximation C (phi n)
  phi_tendsto_identity : ∀ x : C.coordinateSpace,
    Tendsto (fun n ↦ Approximation.mapScalar (phi n) x) atTop (nhds (x : ℝ))
  deformation : ∀ n, Approximation.CoordinateDeformation C (phi n)
  transport : ∀ n,
    Approximation.TwoStageDeformationSupportTransport C (phi n) (deformation n)
  base : ℕ → Set ℝ
  boundaryLift : ∀ _n, ↥(frontier P.base) → C.coordinateSpace
  base_open : ∀ n, IsOpen (base n)
  base_regular : ∀ n, interior (closure (base n)) = base n
  boundaryLift_coe : ∀ n x, (boundaryLift n x : ℝ) = x.1
  transported_support : ∀ n,
    regularSupport (deformation n).deformedRegion
      (transportedPlateCentres (transport n) P) = Complex.re ⁻¹' base n
  transported_frontier : ∀ n,
    frontier (base n) =
      Approximation.mapScalarSet (phi n) (Set.range (boundaryLift n))
  transported_chambers : ∀ n (x y : ↥(frontier P.base)), x.1 < y.1 →
    Ioo x.1 y.1 ∩ frontier P.base = ∅ →
    (Ioo x.1 y.1 ⊆ P.base ↔
      Ioo (Approximation.mapScalar (phi n) (boundaryLift n x))
        (Approximation.mapScalar (phi n) (boundaryLift n y)) ⊆ base n)
  extremal_fibre_exact : ∀ n,
    transportedExtremalFibre (transport n) P t0.1.re =
      {z ∈ transportedPlateCentres (transport n) P |
        z.re = ((transport n).fullCenters t0).re}
  extremal_column : ∀ n,
    IsCenterColumn Axis.vertical (deformation n).deformedRegion
      (transportedExtremalFibre (transport n) P t0.1.re)
  rPresentation : VerticalGenericSlicePresentation C.region r
  sPresentation : VerticalGenericSlicePresentation C.region s
  rCoord : ℕ → ℝ
  sCoord : ℕ → ℝ
  rCoord_eq : ∀ n, rCoord n = (deformation n).firstHomeomorph r
  sCoord_eq : ∀ n, sCoord n = (deformation n).firstHomeomorph s
  r_generic : ∀ n,
    rCoord n ∉ (deformation n).deformedRegion.vertexFinset.image Complex.re
  s_generic : ∀ n,
    sCoord n ∉ (deformation n).deformedRegion.vertexFinset.image Complex.re
  r_nonempty : ∀ n,
    (verticalSlice (deformation n).deformedRegion (rCoord n)).Nonempty
  s_nonempty : ∀ n,
    (verticalSlice (deformation n).deformedRegion (sCoord n)).Nonempty
  r_mass_tendsto : Tendsto
    (fun n ↦ (volume
      (verticalSlice (deformation n).deformedRegion (rCoord n))).toReal)
    atTop (nhds (volume (verticalSlice C.region r)).toReal)
  s_mass_tendsto : Tendsto
    (fun n ↦ (volume
      (verticalSlice (deformation n).deformedRegion (sCoord n))).toReal)
    atTop (nhds (volume (verticalSlice C.region s)).toReal)

private theorem lowerDeformedColumnComparisonSequence_exists
    (a02 : RationalDeformationConstructor)
    (a03 : SupportTransportConstructor)
    (subfamilySupport : SubfamilySupportTransportTheorem)
    (supportTransport : LowerTransportedExtremalFibreBridge)
    (genericSlices : VerticalSlicePresentationConstructor)
    (C : Approximation.ApproximationContext.{0})
    (hTile : TilesOn C.region C.centres Set.univ)
    (P : Continuous.VerticalPlate C.region C.centres)
    (t0 : ↥C.centres) (ht0 : (t0.1 : Tiling.Plane) ∈ P.centres)
    (hLeast : IsLeast (Complex.re '' P.centres) t0.1.re)
    (epsilon eta : ℝ) (hEpsilon : 0 < epsilon) (hEta : 0 < eta)
    (hBaseOpen : IsOpen P.base)
    (hBaseRegular : interior (closure P.base) = P.base)
    (hSupport : P.support = Complex.re ⁻¹' P.base)
    (hGap : ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
      Approximation.IsEpsilonApproximation C epsilon phi →
      Approximation.IsGoodApproximation C phi →
      ∀ t : ↥C.centres, (t.1 : Tiling.Plane) ∈ P.centres →
        t0.1.re < t.1.re →
        (Approximation.mapPoint phi (C.centrePoint t0.1 t0.2)).re + eta ≤
          (Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re)
    (r s : ℝ)
    (hr : r ∉ C.region.vertexFinset.image Complex.re)
    (hs : s ∉ C.region.vertexFinset.image Complex.re)
    (hrne : (verticalSlice C.region r).Nonempty)
    (hsne : (verticalSlice C.region s).Nonempty) :
    ∃ Q : DeformedColumnComparisonSequence C P t0 r s,
      (∀ n, Q.epsilon n ≤ epsilon) ∧ ∀ n, BddBelow (Q.base n) := by
  obtain ⟨εgood, hεgood, hgood⟩ :=
    Approximation.isGoodApproximation_of_sufficientlyFine C
  let ε : ℕ → ℝ := fun n ↦ min epsilon εgood / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    exact div_pos (lt_min hEpsilon hεgood) (by positivity)
  have hεle : ∀ n, ε n ≤ epsilon := by
    intro n
    dsimp [ε]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [min_le_left epsilon εgood]
  have hεgoodle : ∀ n, ε n ≤ εgood := by
    intro n
    dsimp [ε]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [min_le_right epsilon εgood]
  have hεzero : Tendsto ε atTop (nhds 0) := by
    have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact tendsto_const_nhds.div_atTop hden
  choose phi hphi using fun n ↦
    Approximation.exists_epsilonApproximation C (ε n) (hεpos n)
  have hgoodphi : ∀ n, Approximation.IsGoodApproximation C (phi n) := by
    intro n
    apply hgood (phi n)
    refine {
      epsilon_pos := (hphi n).epsilon_pos.trans_le (hεgoodle n)
      fixesRational := (hphi n).fixesRational
      basis_close := fun j ↦ ((hphi n).basis_close j).trans_le (hεgoodle n) }
  let D : ∀ n, Approximation.CoordinateDeformation C (phi n) :=
    fun n ↦ (a02 C (phi n) (hgoodphi n)).some
  let R : ∀ n,
      Approximation.TwoStageDeformationSupportTransport C (phi n) (D n) :=
    fun n ↦ (a03 C (phi n) (D n) hTile).some
  let Sr : VerticalGenericSlicePresentation C.region r :=
    (genericSlices C.region hr).some
  let Ss : VerticalGenericSlicePresentation C.region s :=
    (genericSlices C.region hs).some
  have hPsub : P.centres ⊆ C.centres := by
    rintro z ⟨t, ht, rfl⟩
    exact t.2
  have hbridge : ∀ n, ∃ (X : Set ℝ)
      (b : ↥(frontier P.base) → C.coordinateSpace),
      IsOpen X ∧ interior (closure X) = X ∧
      (∀ x, (b x : ℝ) = x.1) ∧
      regularSupport (D n).deformedRegion (transportedPlateCentres (R n) P) =
        Complex.re ⁻¹' X ∧
      frontier X = Approximation.mapScalarSet (phi n) (Set.range b) ∧
      (∀ a b' : ↥(frontier P.base), a.1 < b'.1 →
        Ioo a.1 b'.1 ∩ frontier P.base = ∅ →
        (Ioo a.1 b'.1 ⊆ P.base ↔
          Ioo (Approximation.mapScalar (phi n) (b a))
            (Approximation.mapScalar (phi n) (b b')) ⊆ X)) ∧
      BddBelow X ∧
      transportedExtremalFibre (R n) P t0.1.re =
        {z ∈ transportedPlateCentres (R n) P |
          z.re = ((R n).fullCenters t0).re} ∧
      IsCenterColumn Axis.vertical (D n).deformedRegion
        (transportedExtremalFibre (R n) P t0.1.re) := by
    intro n
    refine supportTransport subfamilySupport hTile P t0 ht0 hLeast (D n) (R n)
      hBaseOpen hBaseRegular ?_ eta hEta ?_
    · simpa [Continuous.VerticalPlate.support] using hSupport
    · intro t ht hlt
      have hphiE : Approximation.IsEpsilonApproximation C epsilon (phi n) := {
        epsilon_pos := (hphi n).epsilon_pos.trans_le (hεle n)
        fixesRational := (hphi n).fixesRational
        basis_close := fun j ↦ ((hphi n).basis_close j).trans_le (hεle n) }
      have hgap' := hGap (phi n) hphiE (hgoodphi n) t ht hlt
      simpa [(R n).fullCenters_apply] using hgap'
  choose X b hb using hbridge
  have hcenterLower : ∀ n,
      ∀ z ∈ transportedPlateCentres (R n) P,
        ((R n).fullCenters t0).re ≤ z.re := by
    intro n z hz
    rcases hz with ⟨t, ht, rfl⟩
    have hle : t0.1.re ≤ t.1.re := hLeast.2 ⟨t.1, ht, rfl⟩
    rcases hle.eq_or_lt with heq | hlt
    · have heq' : ((R n).fullCenters t0).re = ((R n).fullCenters t).re := by
        rw [(R n).fullCenters_apply, (R n).fullCenters_apply]
        simp [Approximation.mapPoint, Approximation.mapScalar,
          Approximation.ApproximationContext.centrePoint, heq]
      exact heq'.le
    · have hphiE : Approximation.IsEpsilonApproximation C epsilon (phi n) := {
        epsilon_pos := (hphi n).epsilon_pos.trans_le (hεle n)
        fixesRational := (hphi n).fixesRational
        basis_close := fun j ↦ ((hphi n).basis_close j).trans_le (hεle n) }
      have hgap' := hGap (phi n) hphiE (hgoodphi n) t ht hlt
      have hgapR : ((R n).fullCenters t0).re + eta ≤
          ((R n).fullCenters t).re := by
        simpa [(R n).fullCenters_apply] using hgap'
      linarith
  refine ⟨{
    epsilon := ε
    epsilon_pos := hεpos
    epsilon_tendsto_zero := hεzero
    phi := phi
    phi_isApproximation := hphi
    phi_good := hgoodphi
    phi_tendsto_identity := fun z ↦
      mapScalar_tendsto_identity_of_epsilon C ε phi hεzero hphi z
    deformation := D
    transport := R
    base := X
    boundaryLift := b
    base_open := fun n ↦ by
      rcases hb n with ⟨hopen, _, _, _, _, _, _, _, _⟩
      exact hopen
    base_regular := fun n ↦ by
      rcases hb n with ⟨_, hreg, _, _, _, _, _, _, _⟩
      exact hreg
    boundaryLift_coe := fun n x ↦ by
      rcases hb n with ⟨_, _, hcoe, _, _, _, _, _, _⟩
      exact hcoe x
    transported_support := fun n ↦ by
      rcases hb n with ⟨_, _, _, hsup, _, _, _, _, _⟩
      exact hsup
    transported_frontier := fun n ↦ by
      rcases hb n with ⟨_, _, _, _, hfront, _, _, _, _⟩
      exact hfront
    transported_chambers := fun n x y hxy hdisj ↦ by
      rcases hb n with ⟨_, _, _, _, _, hch, _, _, _⟩
      exact hch x y hxy hdisj
    extremal_fibre_exact := fun n ↦ by
      rcases hb n with ⟨_, _, _, _, _, _, _, hfibre, _⟩
      exact hfibre
    extremal_column := fun n ↦ by
      rcases hb n with ⟨_, _, _, _, _, _, _, _, hcolumn⟩
      exact hcolumn
    rPresentation := Sr
    sPresentation := Ss
    rCoord := fun n ↦ (D n).firstHomeomorph r
    sCoord := fun n ↦ (D n).firstHomeomorph s
    rCoord_eq := fun n ↦ rfl
    sCoord_eq := fun n ↦ rfl
    r_generic := fun n ↦ firstHomeomorph_generic (D n) hr
    s_generic := fun n ↦ firstHomeomorph_generic (D n) hs
    r_nonempty := fun n ↦
      deformedVerticalSlice_nonempty_of_source Sr (D n) hrne
    s_nonempty := fun n ↦
      deformedVerticalSlice_nonempty_of_source Ss (D n) hsne
    r_mass_tendsto := deformedVerticalSlice_mass_tendsto Sr phi D
      (mapScalar_tendsto_identity_of_epsilon C ε phi hεzero hphi)
    s_mass_tendsto := deformedVerticalSlice_mass_tendsto Ss phi D
      (mapScalar_tendsto_identity_of_epsilon C ε phi hεzero hphi) },
    hεle, fun n ↦ by
      rcases hb n with ⟨_, _, _, _, _, _, hbelow, _, _⟩
      exact hbelow ⟩

private theorem upperDeformedColumnComparisonSequence_exists
    (a02 : RationalDeformationConstructor)
    (a03 : SupportTransportConstructor)
    (subfamilySupport : SubfamilySupportTransportTheorem)
    (supportTransport : UpperTransportedExtremalFibreBridge)
    (genericSlices : VerticalSlicePresentationConstructor)
    (C : Approximation.ApproximationContext.{0})
    (hTile : TilesOn C.region C.centres Set.univ)
    (P : Continuous.VerticalPlate C.region C.centres)
    (t0 : ↥C.centres) (ht0 : (t0.1 : Tiling.Plane) ∈ P.centres)
    (hGreatest : IsGreatest (Complex.re '' P.centres) t0.1.re)
    (epsilon eta : ℝ) (hEpsilon : 0 < epsilon) (hEta : 0 < eta)
    (hBaseOpen : IsOpen P.base)
    (hBaseRegular : interior (closure P.base) = P.base)
    (hSupport : P.support = Complex.re ⁻¹' P.base)
    (hGap : ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
      Approximation.IsEpsilonApproximation C epsilon phi →
      Approximation.IsGoodApproximation C phi →
      ∀ t : ↥C.centres, (t.1 : Tiling.Plane) ∈ P.centres →
        t.1.re < t0.1.re →
        (Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re + eta ≤
          (Approximation.mapPoint phi (C.centrePoint t0.1 t0.2)).re)
    (r s : ℝ)
    (hr : r ∉ C.region.vertexFinset.image Complex.re)
    (hs : s ∉ C.region.vertexFinset.image Complex.re)
    (hrne : (verticalSlice C.region r).Nonempty)
    (hsne : (verticalSlice C.region s).Nonempty) :
    ∃ Q : DeformedColumnComparisonSequence C P t0 r s,
      (∀ n, Q.epsilon n ≤ epsilon) ∧ ∀ n, BddAbove (Q.base n) := by
  obtain ⟨εgood, hεgood, hgood⟩ :=
    Approximation.isGoodApproximation_of_sufficientlyFine C
  let ε : ℕ → ℝ := fun n ↦ min epsilon εgood / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    exact div_pos (lt_min hEpsilon hεgood) (by positivity)
  have hεle : ∀ n, ε n ≤ epsilon := by
    intro n
    dsimp [ε]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [min_le_left epsilon εgood]
  have hεgoodle : ∀ n, ε n ≤ εgood := by
    intro n
    dsimp [ε]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [min_le_right epsilon εgood]
  have hεzero : Tendsto ε atTop (nhds 0) := by
    have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact tendsto_const_nhds.div_atTop hden
  choose phi hphi using fun n ↦
    Approximation.exists_epsilonApproximation C (ε n) (hεpos n)
  have hgoodphi : ∀ n, Approximation.IsGoodApproximation C (phi n) := by
    intro n
    apply hgood (phi n)
    refine {
      epsilon_pos := (hphi n).epsilon_pos.trans_le (hεgoodle n)
      fixesRational := (hphi n).fixesRational
      basis_close := fun j ↦ ((hphi n).basis_close j).trans_le (hεgoodle n) }
  let D : ∀ n, Approximation.CoordinateDeformation C (phi n) :=
    fun n ↦ (a02 C (phi n) (hgoodphi n)).some
  let R : ∀ n,
      Approximation.TwoStageDeformationSupportTransport C (phi n) (D n) :=
    fun n ↦ (a03 C (phi n) (D n) hTile).some
  let Sr : VerticalGenericSlicePresentation C.region r :=
    (genericSlices C.region hr).some
  let Ss : VerticalGenericSlicePresentation C.region s :=
    (genericSlices C.region hs).some
  have hbridge : ∀ n, ∃ (X : Set ℝ)
      (b : ↥(frontier P.base) → C.coordinateSpace),
      IsOpen X ∧ interior (closure X) = X ∧
      (∀ x, (b x : ℝ) = x.1) ∧
      regularSupport (D n).deformedRegion (transportedPlateCentres (R n) P) =
        Complex.re ⁻¹' X ∧
      frontier X = Approximation.mapScalarSet (phi n) (Set.range b) ∧
      (∀ a b' : ↥(frontier P.base), a.1 < b'.1 →
        Ioo a.1 b'.1 ∩ frontier P.base = ∅ →
        (Ioo a.1 b'.1 ⊆ P.base ↔
          Ioo (Approximation.mapScalar (phi n) (b a))
            (Approximation.mapScalar (phi n) (b b')) ⊆ X)) ∧
      BddAbove X ∧
      transportedExtremalFibre (R n) P t0.1.re =
        {z ∈ transportedPlateCentres (R n) P |
          z.re = ((R n).fullCenters t0).re} ∧
      IsCenterColumn Axis.vertical (D n).deformedRegion
        (transportedExtremalFibre (R n) P t0.1.re) := by
    intro n
    refine supportTransport subfamilySupport hTile P t0 ht0 hGreatest (D n) (R n)
      hBaseOpen hBaseRegular ?_ eta hEta ?_
    · simpa [Continuous.VerticalPlate.support] using hSupport
    · intro t ht hlt
      have hphiE : Approximation.IsEpsilonApproximation C epsilon (phi n) := {
        epsilon_pos := (hphi n).epsilon_pos.trans_le (hεle n)
        fixesRational := (hphi n).fixesRational
        basis_close := fun j ↦ ((hphi n).basis_close j).trans_le (hεle n) }
      have hgap' := hGap (phi n) hphiE (hgoodphi n) t ht hlt
      simpa [(R n).fullCenters_apply] using hgap'
  choose X b hb using hbridge
  have hcenterUpper : ∀ n,
      ∀ z ∈ transportedPlateCentres (R n) P,
        z.re ≤ ((R n).fullCenters t0).re := by
    intro n z hz
    rcases hz with ⟨t, ht, rfl⟩
    have hle : t.1.re ≤ t0.1.re := hGreatest.2 ⟨t.1, ht, rfl⟩
    rcases hle.eq_or_lt with heq | hlt
    · have heq' : ((R n).fullCenters t).re = ((R n).fullCenters t0).re := by
        rw [(R n).fullCenters_apply, (R n).fullCenters_apply]
        simp [Approximation.mapPoint, Approximation.mapScalar,
          Approximation.ApproximationContext.centrePoint, heq]
      exact heq'.le
    · have hphiE : Approximation.IsEpsilonApproximation C epsilon (phi n) := {
        epsilon_pos := (hphi n).epsilon_pos.trans_le (hεle n)
        fixesRational := (hphi n).fixesRational
        basis_close := fun j ↦ ((hphi n).basis_close j).trans_le (hεle n) }
      have hgap' := hGap (phi n) hphiE (hgoodphi n) t ht hlt
      have hgapR : ((R n).fullCenters t).re + eta ≤
          ((R n).fullCenters t0).re := by
        simpa [(R n).fullCenters_apply] using hgap'
      linarith
  refine ⟨{
    epsilon := ε
    epsilon_pos := hεpos
    epsilon_tendsto_zero := hεzero
    phi := phi
    phi_isApproximation := hphi
    phi_good := hgoodphi
    phi_tendsto_identity := fun z ↦
      mapScalar_tendsto_identity_of_epsilon C ε phi hεzero hphi z
    deformation := D
    transport := R
    base := X
    boundaryLift := b
    base_open := fun n ↦ by
      rcases hb n with ⟨hopen, _, _, _, _, _, _, _, _⟩
      exact hopen
    base_regular := fun n ↦ by
      rcases hb n with ⟨_, hreg, _, _, _, _, _, _, _⟩
      exact hreg
    boundaryLift_coe := fun n x ↦ by
      rcases hb n with ⟨_, _, hcoe, _, _, _, _, _, _⟩
      exact hcoe x
    transported_support := fun n ↦ by
      rcases hb n with ⟨_, _, _, hsup, _, _, _, _, _⟩
      exact hsup
    transported_frontier := fun n ↦ by
      rcases hb n with ⟨_, _, _, _, hfront, _, _, _, _⟩
      exact hfront
    transported_chambers := fun n x y hxy hdisj ↦ by
      rcases hb n with ⟨_, _, _, _, _, hch, _, _, _⟩
      exact hch x y hxy hdisj
    extremal_fibre_exact := fun n ↦ by
      rcases hb n with ⟨_, _, _, _, _, _, _, hfibre, _⟩
      exact hfibre
    extremal_column := fun n ↦ by
      rcases hb n with ⟨_, _, _, _, _, _, _, _, hcolumn⟩
      exact hcolumn
    rPresentation := Sr
    sPresentation := Ss
    rCoord := fun n ↦ (D n).firstHomeomorph r
    sCoord := fun n ↦ (D n).firstHomeomorph s
    rCoord_eq := fun n ↦ rfl
    sCoord_eq := fun n ↦ rfl
    r_generic := fun n ↦ firstHomeomorph_generic (D n) hr
    s_generic := fun n ↦ firstHomeomorph_generic (D n) hs
    r_nonempty := fun n ↦ deformedVerticalSlice_nonempty_of_source Sr (D n) hrne
    s_nonempty := fun n ↦ deformedVerticalSlice_nonempty_of_source Ss (D n) hsne
    r_mass_tendsto := deformedVerticalSlice_mass_tendsto Sr phi D
      (mapScalar_tendsto_identity_of_epsilon C ε phi hεzero hphi)
    s_mass_tendsto := deformedVerticalSlice_mass_tendsto Ss phi D
      (mapScalar_tendsto_identity_of_epsilon C ε phi hεzero hphi) },
    hεle, fun n ↦ by
      rcases hb n with ⟨_, _, _, _, _, _, habove, _, _⟩
      exact habove ⟩


private theorem transportedExtremalFibre_isCenterColumn_of_saturation
    {K : Region} {T S S₀ : Set Tiling.Plane} {X : Set ℝ} {a : ℝ}
    (hTile : TilesOn K T Set.univ)
    (hRat : Tiling.RationalPolygonal.IsRelativelyRational K.toPolygonalRegion)
    (hSsub : S ⊆ T) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    (hSupport : regularSupport K S = Complex.re ⁻¹' X)
    (hBound : BddBelow X ∨ BddAbove X)
    (hS₀sub : S₀ ⊆ S) (hS₀axis : ∀ z ∈ S₀, z.re = a)
    (hS₀eq : S₀ = {z : Tiling.Plane | z ∈ S ∧ z.re = a})
    (hS₀ne : S₀.Nonempty) :
    IsCenterColumn Axis.vertical K S₀ := by
  have hSaturates : hSaturates_telescope := by
    intro K T S X hTile hRat hSsub hXopen hXregular hSupport hBound Q hmeet
    exact rationalOneSidedSlab_saturatesColumns
      hTile hRat hSsub hXopen hXregular hSupport hBound Q hmeet
  have hplates : ∀ Q : Continuous.VerticalPlate K T,
      (Q.centres ∩ S₀).Nonempty →
        Q.centres ⊆ S₀ ∧ Continuous.IsVerticalColumn Q := by
    intro Q hmeet
    have hmeetS : (Q.centres ∩ S).Nonempty := by
      obtain ⟨z, hzQ, hz₀⟩ := hmeet
      exact ⟨z, hzQ, hS₀sub hz₀⟩
    obtain ⟨hQsub, hQcolumn⟩ := hSaturates hTile hRat hSsub hXopen
      hXregular hSupport hBound Q hmeetS
    refine ⟨?_, hQcolumn⟩
    rw [hS₀eq]
    intro z hzQ
    refine ⟨hQsub hzQ, ?_⟩
    obtain ⟨c, hc⟩ := hQcolumn
    obtain ⟨z₀, hz₀Q, hz₀S₀⟩ := hmeet
    have hc' : c = a := by
      exact (hc hz₀Q).symm.trans (hS₀axis z₀ hz₀S₀)
    simpa [hc'] using hc hzQ
  apply singleAxis_saturatedColumnUnion_isCenterColumn hTile
    (hS₀sub.trans hSsub) hS₀ne hS₀axis hplates

private theorem lowerTransportedExtremalFibre_isCenterColumn :
  ∀ (_supportTransport : SubfamilySupportTransportTheorem)
    {C : Approximation.ApproximationContext.{0}}
    (_hTile : TilesOn C.region C.centres Set.univ)
    (P : Continuous.VerticalPlate C.region C.centres)
    (t0 : ↥C.centres) (_ht0 : (t0.1 : Tiling.Plane) ∈ P.centres)
    (_hLeast : IsLeast (Complex.re '' P.centres) t0.1.re)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : Approximation.CoordinateDeformation C phi)
    (R : Approximation.TwoStageDeformationSupportTransport C phi D)
    (_hBaseOpen : IsOpen P.base)
    (_hBaseRegular : interior (closure P.base) = P.base)
    (_hSupport : P.support = Complex.re ⁻¹' P.base)
    (eta : ℝ) (_hEta : 0 < eta)
    (_hGap : ∀ t : ↥C.centres,
      (t.1 : Tiling.Plane) ∈ P.centres → t0.1.re < t.1.re →
      (R.fullCenters t0).re + eta ≤ (R.fullCenters t).re),
    ∃ (Xphi : Set ℝ) (boundaryLift : ↥(frontier P.base) → C.coordinateSpace),
      IsOpen Xphi ∧ interior (closure Xphi) = Xphi ∧
      (∀ x, (boundaryLift x : ℝ) = x.1) ∧
      regularSupport D.deformedRegion (transportedPlateCentres R P) =
        Complex.re ⁻¹' Xphi ∧
      frontier Xphi = Approximation.mapScalarSet phi (Set.range boundaryLift) ∧
      (∀ a b : ↥(frontier P.base), a.1 < b.1 →
        Ioo a.1 b.1 ∩ frontier P.base = ∅ →
        (Ioo a.1 b.1 ⊆ P.base ↔
          Ioo (Approximation.mapScalar phi (boundaryLift a))
            (Approximation.mapScalar phi (boundaryLift b)) ⊆ Xphi)) ∧
      BddBelow Xphi ∧
      transportedExtremalFibre R P t0.1.re =
        {z ∈ transportedPlateCentres R P | z.re = (R.fullCenters t0).re} ∧
      IsCenterColumn Axis.vertical D.deformedRegion
        (transportedExtremalFibre R P t0.1.re) := by
  have hSaturates : hSaturates_telescope := by
    intro K T S X hTile hRat hSsub hXopen hXregular hSupport hBound Q hmeet
    exact rationalOneSidedSlab_saturatesColumns
      hTile hRat hSsub hXopen hXregular hSupport hBound Q hmeet
  intro supportTransport C hTile P t0 ht0 hLeast phi D R hBaseOpen hBaseRegular
    hSupport eta hEta hGap
  have hPsub : P.centres ⊆ C.centres := by
    rintro z ⟨t, ht, rfl⟩
    exact t.2
  have hSupport' : regularSupport C.region P.centres = Complex.re ⁻¹' P.base := by
    rw [← Continuous.VerticalPlate.support_eq_regularSupport]
    exact hSupport
  obtain ⟨Xphi, boundaryLift, hXopen, hXregular, hLift, hXsupport,
      hFrontier, hChambers⟩ := supportTransport R P.centres hPsub P.base
    hBaseOpen hBaseRegular hSupport'
  have hmapEq : ∀ s t : ↥C.centres, s.1.re = t.1.re →
      (R.fullCenters s).re = (R.fullCenters t).re := by
    intro s t hst
    rw [R.fullCenters_apply, R.fullCenters_apply]
    simp [Approximation.mapPoint, Approximation.mapScalar,
      Approximation.ApproximationContext.centrePoint, hst]
  have hcentres : ∀ z ∈ transportedPlateCentres R P,
      (R.fullCenters t0).re ≤ z.re := by
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    have htP : (t.1 : Tiling.Plane) ∈ P.centres := ht
    have htge : t0.1.re ≤ t.1.re := hLeast.2 ⟨t.1, htP, rfl⟩
    rcases eq_or_lt_of_le htge with hEq | htl
    · exact le_of_eq (hmapEq t0 t hEq)
    · have hgap' := hGap t htP htl
      exact le_trans (le_add_of_nonneg_right (le_of_lt hEta)) hgap'
  have hBdd : BddBelow Xphi :=
    lowerTransportedPlateBase_bound R P t0 Xphi hcentres (by
      change regularSupport D.deformedRegion
        (Approximation.deformedCenterCarrierOn R.fullCenters
          {t : ↥C.centres | (t : Tiling.Plane) ∈ P.centres}) =
        Complex.re ⁻¹' Xphi
      exact hXsupport)
  have hExtEq : transportedExtremalFibre R P t0.1.re =
      {z ∈ transportedPlateCentres R P | z.re = (R.fullCenters t0).re} := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, ht.1, rfl⟩, ?_⟩
      have htr := ht.2
      exact hmapEq t t0 htr
    · rintro ⟨⟨t, ht, rfl⟩, hz⟩
      have htP : (t.1 : Tiling.Plane) ∈ P.centres := ht
      have htge : t0.1.re ≤ t.1.re := hLeast.2 ⟨t.1, htP, rfl⟩
      rcases eq_or_lt_of_le htge with hteq | htl
      · exact ⟨t, ⟨ht, hteq.symm⟩, rfl⟩
      · have hgap' := hGap t htP htl
        have hcontra : (R.fullCenters t0).re + eta ≤ (R.fullCenters t0).re := by
          simpa [hz] using hgap'
        have : eta ≤ 0 := by linarith [hcontra]
        exact False.elim ((not_le_of_gt hEta) this)
  have hAxis : ∀ z ∈ transportedExtremalFibre R P t0.1.re, z.re =
      (R.fullCenters t0).re := by
    intro z hz
    exact (hExtEq ▸ hz).2
  have hExtNe : (transportedExtremalFibre R P t0.1.re).Nonempty := by
    refine ⟨R.fullCenters t0, ?_⟩
    change R.fullCenters t0 ∈
      Approximation.deformedCenterCarrierOn R.fullCenters
        {t : ↥C.centres | (t : Tiling.Plane) ∈ P.centres ∧ t.1.re = t0.1.re}
    exact ⟨t0, ⟨ht0, rfl⟩, rfl⟩
  have hcenter := transportedExtremalFibre_isCenterColumn_of_saturation
    R.full_tilesOn (deformedRegion_isRelativelyRational D)
    (by
      rintro z ⟨t, ht, rfl⟩
      exact ⟨t, rfl⟩)
    hXopen hXregular (by
      simpa only [transportedPlateCentres] using hXsupport) (Or.inl hBdd)
    (by exact fun z hz => (hExtEq ▸ hz).1) hAxis hExtEq hExtNe
  exact ⟨Xphi, boundaryLift, hXopen, hXregular, hLift, hXsupport,
    hFrontier, hChambers, hBdd, hExtEq, hcenter⟩

private theorem upperTransportedExtremalFibre_isCenterColumn :
  ∀ (_supportTransport : SubfamilySupportTransportTheorem)
    {C : Approximation.ApproximationContext.{0}}
    (_hTile : TilesOn C.region C.centres Set.univ)
    (P : Continuous.VerticalPlate C.region C.centres)
    (t0 : ↥C.centres) (_ht0 : (t0.1 : Tiling.Plane) ∈ P.centres)
    (_hGreatest : IsGreatest (Complex.re '' P.centres) t0.1.re)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : Approximation.CoordinateDeformation C phi)
    (R : Approximation.TwoStageDeformationSupportTransport C phi D)
    (_hBaseOpen : IsOpen P.base)
    (_hBaseRegular : interior (closure P.base) = P.base)
    (_hSupport : P.support = Complex.re ⁻¹' P.base)
    (eta : ℝ) (_hEta : 0 < eta)
    (_hGap : ∀ t : ↥C.centres,
      (t.1 : Tiling.Plane) ∈ P.centres → t.1.re < t0.1.re →
      (R.fullCenters t).re + eta ≤ (R.fullCenters t0).re),
    ∃ (Xphi : Set ℝ) (boundaryLift : ↥(frontier P.base) → C.coordinateSpace),
      IsOpen Xphi ∧ interior (closure Xphi) = Xphi ∧
      (∀ x, (boundaryLift x : ℝ) = x.1) ∧
      regularSupport D.deformedRegion (transportedPlateCentres R P) =
        Complex.re ⁻¹' Xphi ∧
      frontier Xphi = Approximation.mapScalarSet phi (Set.range boundaryLift) ∧
      (∀ a b : ↥(frontier P.base), a.1 < b.1 →
        Ioo a.1 b.1 ∩ frontier P.base = ∅ →
        (Ioo a.1 b.1 ⊆ P.base ↔
          Ioo (Approximation.mapScalar phi (boundaryLift a))
            (Approximation.mapScalar phi (boundaryLift b)) ⊆ Xphi)) ∧
      BddAbove Xphi ∧
      transportedExtremalFibre R P t0.1.re =
        {z ∈ transportedPlateCentres R P | z.re = (R.fullCenters t0).re} ∧
      IsCenterColumn Axis.vertical D.deformedRegion
        (transportedExtremalFibre R P t0.1.re) := by
  have hSaturates : hSaturates_telescope := by
    intro K T S X hTile hRat hSsub hXopen hXregular hSupport hBound Q hmeet
    exact rationalOneSidedSlab_saturatesColumns
      hTile hRat hSsub hXopen hXregular hSupport hBound Q hmeet
  intro supportTransport C hTile P t0 ht0 hGreatest phi D R hBaseOpen hBaseRegular
    hSupport eta hEta hGap
  have hPsub : P.centres ⊆ C.centres := by
    rintro z ⟨t, ht, rfl⟩
    exact t.2
  have hSupport' : regularSupport C.region P.centres = Complex.re ⁻¹' P.base := by
    rw [← Continuous.VerticalPlate.support_eq_regularSupport]
    exact hSupport
  obtain ⟨Xphi, boundaryLift, hXopen, hXregular, hLift, hXsupport,
      hFrontier, hChambers⟩ := supportTransport R P.centres hPsub P.base
    hBaseOpen hBaseRegular hSupport'
  have hmapEq : ∀ s t : ↥C.centres, s.1.re = t.1.re →
      (R.fullCenters s).re = (R.fullCenters t).re := by
    intro s t hst
    rw [R.fullCenters_apply, R.fullCenters_apply]
    simp [Approximation.mapPoint, Approximation.mapScalar,
      Approximation.ApproximationContext.centrePoint, hst]
  have hcentres : ∀ z ∈ transportedPlateCentres R P,
      z.re ≤ (R.fullCenters t0).re := by
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    have htP : (t.1 : Tiling.Plane) ∈ P.centres := ht
    have htle : t.1.re ≤ t0.1.re := hGreatest.2 ⟨t.1, htP, rfl⟩
    rcases eq_or_lt_of_le htle with hEq | htl
    · exact le_of_eq (hmapEq t t0 hEq)
    · have hgap' := hGap t htP htl
      linarith [hgap']
  have hBdd : BddAbove Xphi :=
    upperTransportedPlateBase_bound R P t0 Xphi hcentres (by
      change regularSupport D.deformedRegion
        (Approximation.deformedCenterCarrierOn R.fullCenters
          {t : ↥C.centres | (t : Tiling.Plane) ∈ P.centres}) =
        Complex.re ⁻¹' Xphi
      exact hXsupport)
  have hExtEq : transportedExtremalFibre R P t0.1.re =
      {z ∈ transportedPlateCentres R P | z.re = (R.fullCenters t0).re} := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, ht.1, rfl⟩, ?_⟩
      exact hmapEq t t0 ht.2
    · rintro ⟨⟨t, ht, rfl⟩, hz⟩
      have htP : (t.1 : Tiling.Plane) ∈ P.centres := ht
      have htle : t.1.re ≤ t0.1.re := hGreatest.2 ⟨t.1, htP, rfl⟩
      rcases eq_or_lt_of_le htle with hteq | htl
      · exact ⟨t, ⟨ht, hteq⟩, rfl⟩
      · have hgap' := hGap t htP htl
        have hcontra : (R.fullCenters t).re + eta ≤ (R.fullCenters t).re := by
          simpa [hz] using hgap'
        have : eta ≤ 0 := by linarith [hcontra]
        exact False.elim ((not_le_of_gt hEta) this)
  have hAxis : ∀ z ∈ transportedExtremalFibre R P t0.1.re, z.re =
      (R.fullCenters t0).re := by
    intro z hz
    exact (hExtEq ▸ hz).2
  have hExtNe : (transportedExtremalFibre R P t0.1.re).Nonempty := by
    refine ⟨R.fullCenters t0, ?_⟩
    change R.fullCenters t0 ∈
      Approximation.deformedCenterCarrierOn R.fullCenters
        {t : ↥C.centres | (t : Tiling.Plane) ∈ P.centres ∧ t.1.re = t0.1.re}
    exact ⟨t0, ⟨ht0, rfl⟩, rfl⟩
  have hcenter := transportedExtremalFibre_isCenterColumn_of_saturation
    R.full_tilesOn (deformedRegion_isRelativelyRational D)
    (by
      rintro z ⟨t, ht, rfl⟩
      exact ⟨t, rfl⟩)
    hXopen hXregular (by
      simpa only [transportedPlateCentres] using hXsupport) (Or.inr hBdd)
    (by exact fun z hz => (hExtEq ▸ hz).1) hAxis hExtEq hExtNe
  exact ⟨Xphi, boundaryLift, hXopen, hXregular, hLift, hXsupport,
    hFrontier, hChambers, hBdd, hExtEq, hcenter⟩

private theorem oneSidedPlate_genericSliceMass_eq :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ P : Continuous.VerticalPlate K T,
        (BddBelow P.base ∨ BddAbove P.base) →
        ∀ r s : ℝ,
          r ∉ K.vertexFinset.image Complex.re →
          s ∉ K.vertexFinset.image Complex.re →
          (verticalSlice K r).Nonempty →
          (verticalSlice K s).Nonempty →
          (volume (verticalSlice K r)).toReal =
            (volume (verticalSlice K s)).toReal := by
  intro K T hTile P hOneSided r s hr hs hBr hBs
  rcases hOneSided with hBelow | hAbove
  · rcases (oneSidedPlate_hasProjectionGap hTile P).1 hBelow with
      ⟨a, _eta, _heta, hLeast, _hgap⟩
    rcases hLeast.1 with ⟨t0, ht0P, _ht0a⟩
    have ht0T : t0 ∈ T := by
      rcases ht0P with ⟨u, hu, rfl⟩
      exact u.2
    obtain ⟨v0, hv0, _hvmin, _hrest⟩ := lowerExtremalIntrinsicVerticalEdge K
    obtain ⟨C, hcarrier, hcentres, htarget, hiff⟩ :=
      Approximation.normalizeApproximationContext K T Set.univ v0.1 v0.2 t0 ht0T
    obtain ⟨N⟩ := normalizedPlateData_exists hTile P v0.1 v0.2 t0 ht0T C
      hcarrier hcentres htarget hiff
    have hTileN := N.normalized_tilesOn
    obtain ⟨tN, htNP, hLeastN, epsilon, eta, hepsilon, heta, hgapN⟩ :=
      lowerExtremalGap_survivesGoodApproximation C hTileN N.normalizedPlate
        (N.bddBelow_iff.mpr hBelow)
    have hBaseReg :=
      (Continuous.VerticalPlate.support_isVerticalSlab hTileN N.normalizedPlate).1
    have hSupport :=
      (Continuous.VerticalPlate.support_isVerticalSlab hTileN N.normalizedPlate).2
    have hBaseOpen : IsOpen N.normalizedPlate.base := by
      rw [hBaseReg]
      exact isOpen_interior
    have hrN := (N.verticalSlice_generic_iff r).2 hr
    have hsN := (N.verticalSlice_generic_iff s).2 hs
    have hBrN := (N.verticalSlice_nonempty_iff r).2 hBr
    have hBsN := (N.verticalSlice_nonempty_iff s).2 hBs
    obtain ⟨Q, _hQeps, _hQbase⟩ :=
      lowerDeformedColumnComparisonSequence_exists
        Approximation.exists_rationalPolygonDeformation
        Approximation.exists_twoStageDeformationSupportTransport
        Approximation.coordinateDeformation_subfamilySupport
        lowerTransportedExtremalFibre_isCenterColumn
        Foundations.GenericSlices.verticalGenericSlicePresentation_exists
        C hTileN N.normalizedPlate tN htNP hLeastN epsilon eta
        hepsilon heta hBaseOpen hBaseReg.symm hSupport hgapN
        (r - v0.1.re) (s - v0.1.re) hrN hsN hBrN hBsN
    let Kₙ : ℕ → Region := fun n => (Q.deformation n).deformedRegion
    let Cₙ : ℕ → Set Tiling.Plane := fun n =>
      transportedExtremalFibre (Q.transport n) N.normalizedPlate tN.1.re
    have hColumns : ∀ n, IsCenterColumn Axis.vertical (Kₙ n) (Cₙ n) := by
      intro n
      exact Q.extremal_column n
    have hrGeneric : ∀ n, Q.rCoord n ∉ (Kₙ n).vertexFinset.image Complex.re := by
      intro n
      exact Q.r_generic n
    have hsGeneric : ∀ n, Q.sCoord n ∉ (Kₙ n).vertexFinset.image Complex.re := by
      intro n
      exact Q.s_generic n
    have hrNonempty : ∀ n, (verticalSlice (Kₙ n) (Q.rCoord n)).Nonempty := by
      intro n
      exact Q.r_nonempty n
    have hsNonempty : ∀ n, (verticalSlice (Kₙ n) (Q.sCoord n)).Nonempty := by
      intro n
      exact Q.s_nonempty n
    have hrLimit : Tendsto
        (fun n => (volume (verticalSlice (Kₙ n) (Q.rCoord n))).toReal)
        atTop (nhds (volume (verticalSlice C.region (r - v0.1.re))).toReal) := by
      simpa [Kₙ] using Q.r_mass_tendsto
    have hsLimit : Tendsto
        (fun n => (volume (verticalSlice (Kₙ n) (Q.sCoord n))).toReal)
        atTop (nhds (volume (verticalSlice C.region (s - v0.1.re))).toReal) := by
      simpa [Kₙ] using Q.s_mass_tendsto
    have hEq := genericSliceMass_eq_of_columnLimits C.region Kₙ Cₙ
      (r - v0.1.re) (s - v0.1.re) Q.rCoord Q.sCoord
      hColumns hrGeneric hsGeneric hrNonempty hsNonempty hrLimit hsLimit
    calc
      (volume (verticalSlice K r)).toReal =
          (volume (verticalSlice C.region (r - v0.1.re))).toReal :=
        (N.verticalSlice_mass_eq r).symm
      _ = (volume (verticalSlice C.region (s - v0.1.re))).toReal := hEq
      _ = (volume (verticalSlice K s)).toReal := N.verticalSlice_mass_eq s
  · rcases (oneSidedPlate_hasProjectionGap hTile P).2 hAbove with
      ⟨a, _eta, _heta, hGreatest, _hgap⟩
    rcases hGreatest.1 with ⟨t0, ht0P, _ht0a⟩
    have ht0T : t0 ∈ T := by
      rcases ht0P with ⟨u, hu, rfl⟩
      exact u.2
    obtain ⟨v0, hv0, _hvmax, _hrest⟩ := upperExtremalIntrinsicVerticalEdge K
    obtain ⟨C, hcarrier, hcentres, htarget, hiff⟩ :=
      Approximation.normalizeApproximationContext K T Set.univ v0.1 v0.2 t0 ht0T
    obtain ⟨N⟩ := normalizedPlateData_exists hTile P v0.1 v0.2 t0 ht0T C
      hcarrier hcentres htarget hiff
    have hTileN := N.normalized_tilesOn
    obtain ⟨tN, htNP, hGreatestN, epsilon, eta, hepsilon, heta, hgapN⟩ :=
      upperExtremalGap_survivesGoodApproximation C hTileN N.normalizedPlate
        (N.bddAbove_iff.mpr hAbove)
    have hBaseReg :=
      (Continuous.VerticalPlate.support_isVerticalSlab hTileN N.normalizedPlate).1
    have hSupport :=
      (Continuous.VerticalPlate.support_isVerticalSlab hTileN N.normalizedPlate).2
    have hBaseOpen : IsOpen N.normalizedPlate.base := by
      rw [hBaseReg]
      exact isOpen_interior
    have hrN := (N.verticalSlice_generic_iff r).2 hr
    have hsN := (N.verticalSlice_generic_iff s).2 hs
    have hBrN := (N.verticalSlice_nonempty_iff r).2 hBr
    have hBsN := (N.verticalSlice_nonempty_iff s).2 hBs
    obtain ⟨Q, _hQeps, _hQbase⟩ :=
      upperDeformedColumnComparisonSequence_exists
        Approximation.exists_rationalPolygonDeformation
        Approximation.exists_twoStageDeformationSupportTransport
        Approximation.coordinateDeformation_subfamilySupport
        upperTransportedExtremalFibre_isCenterColumn
        Foundations.GenericSlices.verticalGenericSlicePresentation_exists
        C hTileN N.normalizedPlate tN htNP hGreatestN epsilon eta
        hepsilon heta hBaseOpen hBaseReg.symm hSupport hgapN
        (r - v0.1.re) (s - v0.1.re) hrN hsN hBrN hBsN
    let Kₙ : ℕ → Region := fun n => (Q.deformation n).deformedRegion
    let Cₙ : ℕ → Set Tiling.Plane := fun n =>
      transportedExtremalFibre (Q.transport n) N.normalizedPlate tN.1.re
    have hColumns : ∀ n, IsCenterColumn Axis.vertical (Kₙ n) (Cₙ n) := by
      intro n
      exact Q.extremal_column n
    have hrGeneric : ∀ n, Q.rCoord n ∉ (Kₙ n).vertexFinset.image Complex.re := by
      intro n
      exact Q.r_generic n
    have hsGeneric : ∀ n, Q.sCoord n ∉ (Kₙ n).vertexFinset.image Complex.re := by
      intro n
      exact Q.s_generic n
    have hrNonempty : ∀ n, (verticalSlice (Kₙ n) (Q.rCoord n)).Nonempty := by
      intro n
      exact Q.r_nonempty n
    have hsNonempty : ∀ n, (verticalSlice (Kₙ n) (Q.sCoord n)).Nonempty := by
      intro n
      exact Q.s_nonempty n
    have hrLimit : Tendsto
        (fun n => (volume (verticalSlice (Kₙ n) (Q.rCoord n))).toReal)
        atTop (nhds (volume (verticalSlice C.region (r - v0.1.re))).toReal) := by
      simpa [Kₙ] using Q.r_mass_tendsto
    have hsLimit : Tendsto
        (fun n => (volume (verticalSlice (Kₙ n) (Q.sCoord n))).toReal)
        atTop (nhds (volume (verticalSlice C.region (s - v0.1.re))).toReal) := by
      simpa [Kₙ] using Q.s_mass_tendsto
    have hEq := genericSliceMass_eq_of_columnLimits C.region Kₙ Cₙ
      (r - v0.1.re) (s - v0.1.re) Q.rCoord Q.sCoord
      hColumns hrGeneric hsGeneric hrNonempty hsNonempty hrLimit hsLimit
    calc
      (volume (verticalSlice K r)).toReal =
          (volume (verticalSlice C.region (r - v0.1.re))).toReal :=
        (N.verticalSlice_mass_eq r).symm
      _ = (volume (verticalSlice C.region (s - v0.1.re))).toReal := hEq
      _ = (volume (verticalSlice K s)).toReal := N.verticalSlice_mass_eq s


end Tiling.AxisParallel.Structure

namespace Tiling.AxisParallel.Continuous.VerticalPlate

open Tiling.AxisParallel
open Tiling.AxisParallel.Structure

theorem isColumn_of_bddBelow
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : VerticalPlate K T)
    (hbounded : BddBelow P.base) :
    Continuous.IsVerticalColumn P := by
  rcases (oneSidedPlate_hasProjectionGap hTile P).1 hbounded with
    ⟨a, eta, hEta, hLeast, hGap⟩
  obtain ⟨r₀, hr₀, hB₀, hseed⟩ :=
    lowerExtremalFibre_hasSeedLineTiling hTile P a eta hbounded hEta hLeast hGap
  have hMass : ∀ r s : ℝ,
      r ∉ K.vertexFinset.image Complex.re →
      s ∉ K.vertexFinset.image Complex.re →
      (verticalSlice K r).Nonempty →
      (verticalSlice K s).Nonempty →
      (volume (verticalSlice K r)).toReal =
        (volume (verticalSlice K s)).toReal := by
    intro r s hr hs hBr hBs
    exact oneSidedPlate_genericSliceMass_eq hTile P (Or.inl hbounded)
      r s hr hs hBr hBs
  have hColumn := extremalFibre_isCenterColumn_of_equalSliceMass
    hTile P a r₀ hLeast hr₀ hB₀ hseed hMass
  have hSub : extremalFibre P a ⊆ P.centres := by
    intro z hz
    exact hz.1
  have hEq : extremalFibre P a = P.centres :=
    verticalPlate_eq_of_centerColumnSubfamily hTile P hSub hColumn
  rcases hColumn.2.2.1 with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro z hz
  apply hc z
  rw [hEq]
  exact hz

theorem isColumn_of_bddAbove
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : VerticalPlate K T)
    (hbounded : BddAbove P.base) :
    Continuous.IsVerticalColumn P := by
  rcases (oneSidedPlate_hasProjectionGap hTile P).2 hbounded with
    ⟨a, eta, hEta, hGreatest, hGap⟩
  obtain ⟨r₀, hr₀, hB₀, hseed⟩ :=
    upperExtremalFibre_hasSeedLineTiling hTile P a eta hbounded hEta
      hGreatest hGap
  have hMass : ∀ r s : ℝ,
      r ∉ K.vertexFinset.image Complex.re →
      s ∉ K.vertexFinset.image Complex.re →
      (verticalSlice K r).Nonempty →
      (verticalSlice K s).Nonempty →
      (volume (verticalSlice K r)).toReal =
        (volume (verticalSlice K s)).toReal := by
    intro r s hr hs hBr hBs
    exact oneSidedPlate_genericSliceMass_eq hTile P (Or.inr hbounded)
      r s hr hs hBr hBs
  have hColumn := upperExtremalFibre_isCenterColumn_of_equalSliceMass
    hTile P a r₀ hGreatest hr₀ hB₀ hseed hMass
  have hSub : extremalFibre P a ⊆ P.centres := by
    intro z hz
    exact hz.1
  have hEq : extremalFibre P a = P.centres :=
    verticalPlate_eq_of_centerColumnSubfamily hTile P hSub hColumn
  rcases hColumn.2.2.1 with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro z hz
  apply hc z
  rw [hEq]
  exact hz

theorem isColumn_of_oneSidedBase
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : VerticalPlate K T)
    (hOneSided : BddBelow P.base ∨ BddAbove P.base) :
    Continuous.IsVerticalColumn P := by
  exact hOneSided.elim (isColumn_of_bddBelow hTile P)
    (isColumn_of_bddAbove hTile P)

end Tiling.AxisParallel.Continuous.VerticalPlate
