import Tiling.AxisParallel.Foundations.GenericSlices
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel.Foundations.FilledSliceChains

open Tiling.AxisParallel
open Tiling.AxisParallel.Foundations.GenericSlices

def axisInterval (axis : Axis) (q a b : ℝ) : Set Tiling.Plane := match axis with
  | .horizontal => {z | z.im = q ∧ z.re ∈ Ioo a b}
  | .vertical => {z | z.re = q ∧ z.im ∈ Ioo a b}

def slicePoint (axis : Axis) (q x : ℝ) : Tiling.Plane := match axis with
  | .horizontal => (x : ℂ) + (q : ℂ) * Complex.I
  | .vertical => (q : ℂ) + (x : ℂ) * Complex.I

def sliceEndpointSet (K : Region) (S : Set Tiling.Plane)
    (axis : Axis) (q : ℝ) : Set ℝ :=
  frontier {x : ℝ | slicePoint axis q x ∈ openUnion K S}

def IsFilledIndexedSliceChain (K : Region) (S : Set Tiling.Plane) (axis : Axis)
    (q : ℝ) {n : ℕ} (x : Fin (n + 1) → ℝ) (owner : Fin n → S) : Prop :=
  StrictMono x ∧ ∀ i : Fin n,
    ∃ v w : Tiling.Plane, v ∈ K.vertices ∧ w ∈ K.vertices ∧
      x i.castSucc = axis.coord (v + (owner i).1) ∧
      x i.succ = axis.coord (w + (owner i).1) ∧
      0 < axis.coord (w - v) ∧
      axisInterval axis q (x i.castSucc) (x i.succ) ⊆
        (owner i).1 +ᵥ K.openCarrier

/-- Transverse levels containing a translated intrinsic tile vertex. -/
def translatedVertexLevels
    (K : Region) (S : Set Tiling.Plane) (axis : Axis) : Set ℝ :=
  Set.range fun p : S × ↥K.vertices =>
    axis.transverseCoord ((p.1 : Tiling.Plane) + p.2.1)

private theorem translatedVertexLevels_countable
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) (axis : Axis) :
    (translatedVertexLevels K S axis).Countable := by
  have hS : S.Countable := (IsPacking.locallyFinite_centres hpacking).2
  have hV : K.vertices.Countable := by
    rw [← K.coe_vertexFinset]
    exact K.vertexFinset.finite_toSet.countable
  let _ : Countable S := hS.to_subtype
  let _ : Countable ↥K.vertices := hV.to_subtype
  exact Set.countable_range _

/-- Almost every slice avoids every translated intrinsic vertex level. -/
private theorem eventually_avoids_translatedVertexLevels
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) (axis : Axis) :
    ∀ᵐ q : ℝ ∂volume, q ∉ translatedVertexLevels K S axis := by
  exact (translatedVertexLevels_countable hpacking axis).ae_notMem volume

private def placedSupportSlice (K : Region) (axis : Axis) (q : ℝ)
    (t : Tiling.Plane) : Set ℝ :=
  (slicePoint axis q) ⁻¹' (t +ᵥ K.support)

private def placedOpenSlice (K : Region) (axis : Axis) (q : ℝ)
    (t : Tiling.Plane) : Set ℝ :=
  (slicePoint axis q) ⁻¹' (t +ᵥ K.openCarrier)

private theorem continuous_slicePoint (axis : Axis) (q : ℝ) :
    Continuous (slicePoint axis q) := by
  cases axis <;> unfold slicePoint <;> fun_prop

private theorem locallyFinite_placedSupportSlice
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) (axis : Axis) (q : ℝ) :
    LocallyFinite (fun t : S ↦ placedSupportSlice K axis q t.1) := by
  let P := K.polygonalProtoTiling S
  let toPlacement : S → P.placements := fun s => ⟨(s, ()), s.2⟩
  have htoPlacement : Function.Injective toPlacement := by
    intro s t hst
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) hst)
  have hloc : LocallyFinite (fun s : S ↦ (s : Tiling.Plane) +ᵥ K.support) := by
    exact (P.locallyFinite_placedTile hpacking).comp_injective htoPlacement
  exact hloc.preimage_continuous (continuous_slicePoint axis q)

private theorem locallyFinite_placedOpenSlice
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) (axis : Axis) (q : ℝ) :
    LocallyFinite (fun t : S ↦ placedOpenSlice K axis q t.1) := by
  exact (locallyFinite_placedSupportSlice hpacking axis q).subset fun t =>
    preimage_mono (vadd_set_mono interior_subset)

theorem frontier_iUnion_subset_iUnion_frontier
    {ι X : Type*} [TopologicalSpace X] {f : ι → Set X}
    (hloc : LocallyFinite f) :
    frontier (⋃ i, f i) ⊆ ⋃ i, frontier (f i) := by
  intro x hx
  have hxcl : x ∈ closure (⋃ i, f i) := frontier_subset_closure hx
  rw [hloc.closure_iUnion] at hxcl
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxcl
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [frontier]
  refine ⟨hxi, ?_⟩
  intro hxint
  exact disjoint_interior_frontier.le_bot ⟨interior_mono (subset_iUnion f i) hxint, hx⟩

private theorem sliceFiber_eq_iUnion_placedOpenSlice
    (K : Region) (S : Set Tiling.Plane) (axis : Axis) (q : ℝ) :
    {x : ℝ | slicePoint axis q x ∈ openUnion K S} =
      ⋃ t : S, placedOpenSlice K axis q t.1 := by
  ext x
  simp only [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier.eq_def,
    Set.mem_iUnion, placedOpenSlice, Set.mem_preimage]
  rfl

private theorem sliceEndpointSet_subset_tileFrontiers
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) (axis : Axis) (q : ℝ) :
    sliceEndpointSet K S axis q ⊆
      ⋃ t : S, frontier (placedOpenSlice K axis q t.1) := by
  rw [sliceEndpointSet, sliceFiber_eq_iUnion_placedOpenSlice]
  exact frontier_iUnion_subset_iUnion_frontier
    (locallyFinite_placedOpenSlice hpacking axis q)

private theorem frontier_finite_of_finiteIntervalRegion
    {B : Set ℝ} (hB : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion B) :
    (frontier B).Finite := by
  obtain ⟨n, a, b, hab, rfl⟩ := hB
  apply (Set.finite_iUnion fun i : Fin n => Set.toFinite {a i, b i}).subset
  intro x hx
  have hx' := frontier_iUnion_subset_iUnion_frontier
    (locallyFinite_of_finite fun i : Fin n => Ioo (a i) (b i)) hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx'
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [frontier_Ioo (hab i)] at hxi
  exact hxi

private theorem isFiniteIntervalRegion_vadd
    {B : Set ℝ} (hB : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion B)
    (c : ℝ) :
    Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion (c +ᵥ B) := by
  obtain ⟨n, a, b, hab, rfl⟩ := hB
  refine ⟨n, fun i => c + a i, fun i => c + b i,
    fun i => add_lt_add_right (hab i) c, ?_⟩
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, Set.mem_iUnion,
    Set.mem_Ioo]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by constructor <;> linarith [hi.1, hi.2]⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by constructor <;> linarith [hi.1, hi.2]⟩

private theorem isFiniteIntervalRegion_isBounded
    {B : Set ℝ} (hB : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion B) :
    Bornology.IsBounded B := by
  obtain ⟨n, a, b, _, rfl⟩ := hB
  rw [Bornology.isBounded_iUnion]
  exact fun i => Metric.isBounded_Ioo (a i) (b i)

private theorem placedOpenSlice_frontier_finite
    {K : Region} {S : Set Tiling.Plane} {axis : Axis} {q : ℝ}
    (hq : q ∉ translatedVertexLevels K S axis) (t : S) :
    (frontier (placedOpenSlice K axis q t.1)).Finite := by
  cases axis with
  | horizontal =>
      have hgeneric : q - t.1.im ∉ K.vertexFinset.image Complex.im := by
        intro h
        obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp h
        apply hq
        rw [translatedVertexLevels]
        refine ⟨(t, ⟨v, ?_⟩), ?_⟩
        · rw [← K.coe_vertexFinset]
          exact hv
        · simp only [Axis.transverseCoord, Complex.add_im]
          linarith [hvq]
      have hfinite := horizontalSlice_isFiniteIntervalRegion K hgeneric
      have heq : placedOpenSlice K Axis.horizontal q t.1 =
          t.1.re +ᵥ
            horizontalSlice K
              (q - t.1.im) := by
        ext x
        simp only [placedOpenSlice, slicePoint, Set.mem_preimage,
          horizontalSlice,
          Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
        constructor <;> intro hx
        · convert hx using 1
          apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
        · convert hx using 1
          apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
      rw [heq]
      exact frontier_finite_of_finiteIntervalRegion
        (isFiniteIntervalRegion_vadd hfinite t.1.re)
  | vertical =>
      have hgeneric : q - t.1.re ∉ K.vertexFinset.image Complex.re := by
        intro h
        obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp h
        apply hq
        rw [translatedVertexLevels]
        refine ⟨(t, ⟨v, ?_⟩), ?_⟩
        · rw [← K.coe_vertexFinset]
          exact hv
        · simp only [Axis.transverseCoord, Complex.add_re]
          linarith [hvq]
      have hfinite := verticalSlice_isFiniteIntervalRegion K hgeneric
      have heq : placedOpenSlice K Axis.vertical q t.1 =
          t.1.im +ᵥ
            verticalSlice K
              (q - t.1.re) := by
        ext x
        simp only [placedOpenSlice, slicePoint, Set.mem_preimage,
          verticalSlice,
          Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
        constructor <;> intro hx
        · convert hx using 1
          apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
        · convert hx using 1
          apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
      rw [heq]
      exact frontier_finite_of_finiteIntervalRegion
        (isFiniteIntervalRegion_vadd hfinite t.1.im)

private theorem frontier_placedOpenSlice_subset_support
    (K : Region) (axis : Axis) (q : ℝ) (t : Tiling.Plane) :
    frontier (placedOpenSlice K axis q t) ⊆ placedSupportSlice K axis q t := by
  apply frontier_subset_closure.trans
  apply closure_minimal
  · exact preimage_mono (vadd_set_mono interior_subset)
  · exact ((K.isPolygonal.isClosed.vadd t).preimage
      (continuous_slicePoint axis q))

theorem genericSliceEndpointSet_locallyFinite :
    ∀ (K : Region) (S : Set Tiling.Plane), TilesOn K S univ →
      ∀ axis : Axis, ∀ᵐ q : ℝ ∂volume,
        ∀ Q : Set ℝ, Bornology.IsBounded Q →
          (sliceEndpointSet K S axis q ∩ Q).Finite := by
  intro K S hTile axis
  filter_upwards [eventually_avoids_translatedVertexLevels hTile.2.1 axis] with q hq
  intro Q hQ
  obtain ⟨R, hQR⟩ := hQ.subset_closedBall (0 : ℝ)
  let C : Set ℝ := Metric.closedBall 0 R
  have hCcompact : IsCompact C := isCompact_closedBall 0 R
  have hloc := locallyFinite_placedSupportSlice hTile.2.1 axis q
  let active : Set S :=
    {t | (placedSupportSlice K axis q t.1 ∩ C).Nonempty}
  have hactive : active.Finite := by
    exact hloc.finite_nonempty_inter_compact hCcompact
  apply (hactive.biUnion fun t _ =>
    placedOpenSlice_frontier_finite hq t).subset
  rintro x ⟨hxEndpoint, hxQ⟩
  have hxTiles := sliceEndpointSet_subset_tileFrontiers hTile.2.1 axis q hxEndpoint
  obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hxTiles
  refine Set.mem_biUnion ?_ hxt
  have hxSupport := frontier_placedOpenSlice_subset_support K axis q t.1 hxt
  exact ⟨x, hxSupport, hQR hxQ⟩

private theorem eventually_sliceFiber_ae_univ
    {K : Region} {S : Set Tiling.Plane} (hTile : TilesOn K S univ)
    (axis : Axis) :
    ∀ᵐ q : ℝ ∂volume,
      {x : ℝ | slicePoint axis q x ∈ openUnion K S} =ᵐ[volume] univ := by
  have hplane : ∀ᵐ z : Tiling.Plane ∂volume, z ∈ openUnion K S := by
    filter_upwards [hTile.2.2] with z hz
    change z ∈ (Set.univ : Set Tiling.Plane) ↔ ∃ t : S,
      z ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier at hz
    simpa only [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier.eq_def,
      Set.mem_iUnion] using hz.mp (Set.mem_univ z)
  have hpull :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hplane
  cases axis with
  | vertical =>
      have hslices := MeasureTheory.Measure.ae_ae_of_ae_prod
        (μ := volume) (ν := volume) hpull
      filter_upwards [hslices] with q hq
      filter_upwards [hq] with x hx
      apply propext
      constructor
      · intro _
        exact Set.mem_univ x
      · intro _
        change slicePoint Axis.vertical q x ∈ openUnion K S
        have heq : slicePoint Axis.vertical q x =
            Complex.measurableEquivRealProd.symm (q, x) := by
          apply Complex.ext <;> simp [slicePoint]
        rw [heq]
        exact hx
  | horizontal =>
      have hswap :=
        MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae hpull
      have hslices := MeasureTheory.Measure.ae_ae_of_ae_prod
        (μ := volume) (ν := volume) hswap
      filter_upwards [hslices] with q hq
      filter_upwards [hq] with x hx
      apply propext
      constructor
      · intro _
        exact Set.mem_univ x
      · intro _
        change slicePoint Axis.horizontal q x ∈ openUnion K S
        have heq : slicePoint Axis.horizontal q x =
            Complex.measurableEquivRealProd.symm (q, x).swap := by
          apply Complex.ext <;> simp [slicePoint]
        rw [heq]
        exact hx

private theorem frontier_not_bddAbove_of_bounded_disjoint_openCover
    {ι : Type*} {U : Set ℝ} {f : ι → Set ℝ}
    (hUae : U =ᵐ[volume] univ) (hopen : ∀ i, IsOpen (f i))
    (hbdd : ∀ i, Bornology.IsBounded (f i))
    (hpair : Set.Pairwise Set.univ (Disjoint on f)) (hU : U = ⋃ i, f i) :
    ¬ BddAbove (frontier U) := by
  intro hfront
  obtain ⟨c, hc⟩ := hfront
  have hdisj : Disjoint (Ioi c) (frontier U) := by
    rw [Set.disjoint_left]
    intro x hxc hxf
    exact (not_lt_of_ge (hc hxf)) hxc
  have htailCases :=
    Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Ioi hdisj
  have htail : Ioi c ⊆ U := by
    rcases htailCases with hinside | houtside
    · exact hinside.trans interior_subset
    · exfalso
      have hcomp0 : volume Uᶜ = 0 := ae_eq_univ.mp hUae
      have hIoi0 : volume (Ioi c) = 0 := measure_mono_null
        (houtside.trans interior_subset) hcomp0
      exact (isOpen_Ioi.measure_ne_zero volume ⟨c + 1, by simp⟩) hIoi0
  have hxU : c + 1 ∈ U := htail (by simp)
  rw [hU, Set.mem_iUnion] at hxU
  obtain ⟨i, hxi⟩ := hxU
  obtain ⟨d, hd⟩ := (hbdd i).bddAbove
  let y := max c d + 1
  have hyTail : y ∈ Ioi c := by
    change c < y
    dsimp [y]
    linarith [le_max_left c d]
  have hyNot : y ∉ f i := by
    intro hy
    dsimp [y] at hyTail ⊢
    linarith [hd hy, le_max_right c d]
  let V : Set ℝ := ⋃ j : {j : ι // j ≠ i}, f j.1
  have hVopen : IsOpen V := isOpen_iUnion fun j => hopen j.1
  have hiV : Disjoint (f i) V := by
    rw [Set.disjoint_left]
    intro z hzi hzV
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzV
    exact Set.disjoint_left.mp (hpair (Set.mem_univ i) (Set.mem_univ j.1) j.2.symm) hzi hzj
  have htailCover : Ioi c ⊆ f i ∪ V := by
    intro z hz
    have hzU := htail hz
    rw [hU, Set.mem_iUnion] at hzU
    obtain ⟨j, hzj⟩ := hzU
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hzj)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hzj⟩)
  rcases isPreconnected_Ioi.subset_or_subset (hopen i) hVopen hiV htailCover with hi | hV
  · exact hyNot (hi hyTail)
  · have hxNotV : c + 1 ∉ V := by
      intro hxV
      exact Set.disjoint_left.mp hiV hxi hxV
    exact hxNotV (hV (by simp))

private theorem frontier_not_bddBelow_of_bounded_disjoint_openCover
    {ι : Type*} {U : Set ℝ} {f : ι → Set ℝ}
    (hUae : U =ᵐ[volume] univ) (hopen : ∀ i, IsOpen (f i))
    (hbdd : ∀ i, Bornology.IsBounded (f i))
    (hpair : Set.Pairwise Set.univ (Disjoint on f)) (hU : U = ⋃ i, f i) :
    ¬ BddBelow (frontier U) := by
  intro hbelow
  obtain ⟨c, hc⟩ := hbelow
  have hdisj : Disjoint (Iio c) (frontier U) := by
    rw [Set.disjoint_left]
    intro x hxc hxf
    exact (not_lt_of_ge (hc hxf)) hxc
  have htailCases :=
    Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Iio hdisj
  have htail : Iio c ⊆ U := by
    rcases htailCases with hinside | houtside
    · exact hinside.trans interior_subset
    · exfalso
      have hcomp0 : volume Uᶜ = 0 := ae_eq_univ.mp hUae
      have hIio0 : volume (Iio c) = 0 := measure_mono_null
        (houtside.trans interior_subset) hcomp0
      exact (isOpen_Iio.measure_ne_zero volume ⟨c - 1, by simp⟩) hIio0
  have hxU : c - 1 ∈ U := htail (by simp)
  rw [hU, Set.mem_iUnion] at hxU
  obtain ⟨i, hxi⟩ := hxU
  obtain ⟨d, hd⟩ := (hbdd i).bddBelow
  let y := min c d - 1
  have hyTail : y ∈ Iio c := by
    change y < c
    dsimp [y]
    linarith [min_le_left c d]
  have hyNot : y ∉ f i := by
    intro hy
    have hdy : d ≤ y := hd hy
    dsimp [y] at hdy
    linarith [min_le_right c d]
  let V : Set ℝ := ⋃ j : {j : ι // j ≠ i}, f j.1
  have hVopen : IsOpen V := isOpen_iUnion fun j => hopen j.1
  have hiV : Disjoint (f i) V := by
    rw [Set.disjoint_left]
    intro z hzi hzV
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzV
    exact Set.disjoint_left.mp (hpair (Set.mem_univ i) (Set.mem_univ j.1) j.2.symm) hzi hzj
  have htailCover : Iio c ⊆ f i ∪ V := by
    intro z hz
    have hzU := htail hz
    rw [hU, Set.mem_iUnion] at hzU
    obtain ⟨j, hzj⟩ := hzU
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hzj)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hzj⟩)
  rcases isPreconnected_Iio.subset_or_subset (hopen i) hVopen hiV htailCover with hi | hV
  · exact hyNot (hi hyTail)
  · have hxNotV : c - 1 ∉ V := by
      intro hxV
      exact Set.disjoint_left.mp hiV hxi hxV
    exact hxNotV (hV (by simp))

theorem genericSliceEndpointSet_unbounded :
    ∀ (K : Region) (S : Set Tiling.Plane), TilesOn K S univ →
      ∀ axis : Axis, ∀ᵐ q : ℝ ∂volume,
        ¬ BddAbove (sliceEndpointSet K S axis q) ∧
          ¬ BddBelow (sliceEndpointSet K S axis q) := by
  intro K S hTile axis
  filter_upwards [eventually_avoids_translatedVertexLevels hTile.2.1 axis,
    eventually_sliceFiber_ae_univ hTile axis] with q hq hfull
  let U : Set ℝ := {x | slicePoint axis q x ∈ openUnion K S}
  let f : S → Set ℝ := fun t => placedOpenSlice K axis q t.1
  have hU : U = ⋃ t, f t := sliceFiber_eq_iUnion_placedOpenSlice K S axis q
  have hopen : ∀ t, IsOpen (f t) := fun t =>
    (isOpen_interior.vadd t.1).preimage (continuous_slicePoint axis q)
  have hbdd : ∀ t, Bornology.IsBounded (f t) := fun t => by
    exact isFiniteIntervalRegion_isBounded
      (by
        cases axis with
        | horizontal =>
            have hgeneric : q - t.1.im ∉ K.vertexFinset.image Complex.im := by
              intro h
              obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp h
              apply hq
              rw [translatedVertexLevels]
              refine ⟨(t, ⟨v, ?_⟩), ?_⟩
              · rw [← K.coe_vertexFinset]
                exact hv
              · simp only [Axis.transverseCoord, Complex.add_im]
                linarith [hvq]
            have hfinite := horizontalSlice_isFiniteIntervalRegion K hgeneric
            have heq : f t = t.1.re +ᵥ
                horizontalSlice K
                  (q - t.1.im) := by
              change placedOpenSlice K Axis.horizontal q t.1 = _
              ext x
              simp only [placedOpenSlice, slicePoint, Set.mem_preimage,
                horizontalSlice,
                Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
              constructor <;> intro hx
              · convert hx using 1
                apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
              · convert hx using 1
                apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
            rw [heq]
            exact isFiniteIntervalRegion_vadd hfinite t.1.re
        | vertical =>
            have hgeneric : q - t.1.re ∉ K.vertexFinset.image Complex.re := by
              intro h
              obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp h
              apply hq
              rw [translatedVertexLevels]
              refine ⟨(t, ⟨v, ?_⟩), ?_⟩
              · rw [← K.coe_vertexFinset]
                exact hv
              · simp only [Axis.transverseCoord, Complex.add_re]
                linarith [hvq]
            have hfinite := verticalSlice_isFiniteIntervalRegion K hgeneric
            have heq : f t = t.1.im +ᵥ
                verticalSlice K
                  (q - t.1.re) := by
              change placedOpenSlice K Axis.vertical q t.1 = _
              ext x
              simp only [placedOpenSlice, slicePoint, Set.mem_preimage,
                verticalSlice,
                Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
              constructor <;> intro hx
              · convert hx using 1
                apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
              · convert hx using 1
                apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
            rw [heq]
            exact isFiniteIntervalRegion_vadd hfinite t.1.im)
  have hpair : Set.Pairwise Set.univ (Disjoint on f) := by
    intro s _ t _ hst
    change Disjoint (f s) (f t)
    rw [Set.disjoint_left]
    intro x hxs hxt
    have hp := (isPacking_iff_openCarrier_disjoint K S).mp hTile.2.1
    apply Set.disjoint_left.mp (hp s.2 t.2 (fun h => hst (Subtype.ext h)))
    · exact hxs
    · exact hxt
  change ¬ BddAbove (frontier U) ∧ ¬ BddBelow (frontier U)
  exact ⟨frontier_not_bddAbove_of_bounded_disjoint_openCover
      hfull hopen hbdd hpair hU,
    frontier_not_bddBelow_of_bounded_disjoint_openCover
      hfull hopen hbdd hpair hU⟩

private theorem openInterval_subset_of_ae_univ_of_disjoint_frontier
    {U : Set ℝ} {l r : ℝ} (hlr : l < r) (hfull : U =ᵐ[volume] univ)
    (hdisj : Disjoint (Ioo l r) (frontier U)) : Ioo l r ⊆ U := by
  rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Ioo hdisj with hin | hout
  · exact hin.trans interior_subset
  · exfalso
    have hcomp0 : volume Uᶜ = 0 := ae_eq_univ.mp hfull
    have hIoo0 : volume (Ioo l r) = 0 :=
      measure_mono_null (hout.trans interior_subset) hcomp0
    exact (isOpen_Ioo.measure_ne_zero volume
      ⟨(l + r) / 2, by constructor <;> linarith⟩) hIoo0

private theorem one_member_contains_openInterval
    {I : Type*} {f : I → Set ℝ} {l r : ℝ} (hlr : l < r)
    (hopen : ∀ i, IsOpen (f i))
    (hpair : Set.Pairwise Set.univ (Disjoint on f))
    (hcover : Ioo l r ⊆ ⋃ i, f i) :
    ∃ i, Ioo l r ⊆ f i := by
  let m := (l + r) / 2
  have hm : m ∈ Ioo l r := by dsimp [m]; constructor <;> linarith
  obtain ⟨i, hmi⟩ := Set.mem_iUnion.mp (hcover hm)
  let V : Set ℝ := ⋃ j : {j : I // j ≠ i}, f j.1
  have hVopen : IsOpen V := isOpen_iUnion fun j => hopen j.1
  have hiV : Disjoint (f i) V := by
    rw [Set.disjoint_left]
    intro z hzi hzV
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzV
    exact Set.disjoint_left.mp
      (hpair (Set.mem_univ i) (Set.mem_univ j.1) j.2.symm) hzi hzj
  have hcover' : Ioo l r ⊆ f i ∪ V := by
    intro z hz
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp (hcover hz)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hzj)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hzj⟩)
  rcases isPreconnected_Ioo.subset_or_subset (hopen i) hVopen hiV hcover' with hi | hV
  · exact ⟨i, hi⟩
  · exact False.elim (Set.disjoint_left.mp hiV hmi (hV hm))

private theorem endpoints_mem_frontier_of_interval_subset
    {U F : Set ℝ} {l r : ℝ} (hlr : l < r)
    (hl : l ∈ frontier U) (hr : r ∈ frontier U)
    (hFU : F ⊆ U) (hgap : Ioo l r ⊆ F) :
    l ∈ frontier F ∧ r ∈ frontier F := by
  have hcl : closure (Ioo l r) ⊆ closure F := closure_mono hgap
  have hends : Icc l r ⊆ closure F := by
    rwa [closure_Ioo (ne_of_lt hlr)] at hcl
  constructor <;> rw [frontier] <;> constructor
  · exact hends (left_mem_Icc.mpr (le_of_lt hlr))
  · intro hli
    exact disjoint_interior_frontier.le_bot
      ⟨interior_mono hFU hli, hl⟩
  · exact hends (right_mem_Icc.mpr (le_of_lt hlr))
  · intro hri
    exact disjoint_interior_frontier.le_bot
      ⟨interior_mono hFU hri, hr⟩

private theorem filledGap
    {K : Region} {S : Set Tiling.Plane} (hTile : TilesOn K S univ)
    {axis : Axis} {q l r : ℝ}
    (hq : q ∉ translatedVertexLevels K S axis)
    (hfull : {x : ℝ | slicePoint axis q x ∈ openUnion K S} =ᵐ[volume] univ)
    (hl : l ∈ sliceEndpointSet K S axis q)
    (hr : r ∈ sliceEndpointSet K S axis q) (hlr : l < r)
    (hnone : Disjoint (sliceEndpointSet K S axis q) (Ioo l r)) :
    ∃ t : S, ∃ v w : Tiling.Plane, v ∈ K.vertices ∧ w ∈ K.vertices ∧
      l = axis.coord (v + t.1) ∧ r = axis.coord (w + t.1) ∧
      0 < axis.coord (w - v) ∧ axisInterval axis q l r ⊆ t.1 +ᵥ K.openCarrier := by
  let U : Set ℝ := {x | slicePoint axis q x ∈ openUnion K S}
  let f : S → Set ℝ := fun t => placedOpenSlice K axis q t.1
  have hU : U = ⋃ t, f t := sliceFiber_eq_iUnion_placedOpenSlice K S axis q
  have hopen : ∀ t, IsOpen (f t) := fun t =>
    (isOpen_interior.vadd t.1).preimage (continuous_slicePoint axis q)
  have hpair : Set.Pairwise Set.univ (Disjoint on f) := by
    intro s _ t _ hst
    change Disjoint (f s) (f t)
    rw [Set.disjoint_left]
    intro x hxs hxt
    exact Set.disjoint_left.mp
      ((isPacking_iff_openCarrier_disjoint K S).mp hTile.2.1 s.2 t.2
        (fun h => hst (Subtype.ext h))) hxs hxt
  have hgapU : Ioo l r ⊆ U :=
    openInterval_subset_of_ae_univ_of_disjoint_frontier hlr hfull (by
      simpa [sliceEndpointSet, U] using hnone.symm)
  obtain ⟨t, hgap⟩ := one_member_contains_openInterval hlr hopen hpair
    (hgapU.trans_eq hU)
  have hfront : l ∈ frontier (f t) ∧ r ∈ frontier (f t) :=
    endpoints_mem_frontier_of_interval_subset hlr hl hr
      (by
        intro x hx
        change x ∈ U
        rw [hU]
        exact Set.mem_iUnion.mpr ⟨t, hx⟩) hgap
  cases axis with
  | horizontal =>
      have hgeneric : q - t.1.im ∉ K.vertexFinset.image Complex.im := by
        intro h
        obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp h
        apply hq
        refine ⟨(t, ⟨v, ?_⟩), ?_⟩
        · rw [← K.coe_vertexFinset]; exact hv
        · simp only [Axis.transverseCoord, Complex.add_im]
          linarith [hvq]
      have heq : f t = t.1.re +ᵥ
          horizontalSlice K (q - t.1.im) := by
        ext x
        simp only [f, placedOpenSlice, slicePoint, Set.mem_preimage,
          horizontalSlice,
          Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
        constructor <;> intro hx
        · convert hx using 1; apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
        · convert hx using 1; apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
      have hgap' : Ioo (l - t.1.re) (r - t.1.re) ⊆
          horizontalSlice K (q - t.1.im) := by
        intro x hx
        have := hgap (show x + t.1.re ∈ Ioo l r by constructor <;> linarith [hx.1, hx.2])
        rw [heq] at this
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm] using this
      have hf' : l - t.1.re ∈ frontier
            (horizontalSlice K (q - t.1.im)) ∧
          r - t.1.re ∈ frontier
            (horizontalSlice K (q - t.1.im)) := by
        rw [heq] at hfront
        have htranslate := (Homeomorph.addLeft t.1.re).image_frontier
          (horizontalSlice K (q - t.1.im))
        simp only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] at htranslate
        rw [← htranslate] at hfront
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg,
          add_comm] using hfront
      obtain ⟨v, w, hv, hw⟩ := horizontalSlice_componentEndpoints K hgeneric
        (by linarith) hgap' hf'.1 hf'.2
      refine ⟨t, v.1, w.1, v.2, w.2, ?_, ?_, ?_, ?_⟩
      · simp only [Axis.coord, Complex.add_re]; linarith [hv]
      · simp only [Axis.coord, Complex.add_re]; linarith [hw]
      · simp only [Axis.coord, Complex.sub_re]; linarith [hv, hw, hlr]
      · intro z hz
        have := hgap hz.2
        change slicePoint Axis.horizontal q z.re ∈ t.1 +ᵥ K.openCarrier at this
        convert this using 1
        apply Complex.ext <;> simp [slicePoint, hz.1]
  | vertical =>
      have hgeneric : q - t.1.re ∉ K.vertexFinset.image Complex.re := by
        intro h
        obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp h
        apply hq
        refine ⟨(t, ⟨v, ?_⟩), ?_⟩
        · rw [← K.coe_vertexFinset]; exact hv
        · simp only [Axis.transverseCoord, Complex.add_re]
          linarith [hvq]
      have heq : f t = t.1.im +ᵥ
          verticalSlice K (q - t.1.re) := by
        ext x
        simp only [f, placedOpenSlice, slicePoint, Set.mem_preimage,
          verticalSlice,
          Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
        constructor <;> intro hx
        · convert hx using 1; apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
        · convert hx using 1; apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
      have hgap' : Ioo (l - t.1.im) (r - t.1.im) ⊆
          verticalSlice K (q - t.1.re) := by
        intro x hx
        have := hgap (show x + t.1.im ∈ Ioo l r by constructor <;> linarith [hx.1, hx.2])
        rw [heq] at this
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm] using this
      have hf' : l - t.1.im ∈ frontier
            (verticalSlice K (q - t.1.re)) ∧
          r - t.1.im ∈ frontier
            (verticalSlice K (q - t.1.re)) := by
        rw [heq] at hfront
        have htranslate := (Homeomorph.addLeft t.1.im).image_frontier
          (verticalSlice K (q - t.1.re))
        simp only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] at htranslate
        rw [← htranslate] at hfront
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg,
          add_comm] using hfront
      obtain ⟨v, w, hv, hw⟩ := verticalSlice_componentEndpoints K hgeneric
        (by linarith) hgap' hf'.1 hf'.2
      refine ⟨t, v.1, w.1, v.2, w.2, ?_, ?_, ?_, ?_⟩
      · simp only [Axis.coord, Complex.add_im]; linarith [hv]
      · simp only [Axis.coord, Complex.add_im]; linarith [hw]
      · simp only [Axis.coord, Complex.sub_im]; linarith [hv, hw, hlr]
      · intro z hz
        have := hgap hz.2
        change slicePoint Axis.vertical q z.im ∈ t.1 +ᵥ K.openCarrier at this
        convert this using 1
        apply Complex.ext <;> simp [slicePoint, hz.1]

theorem genericSliceChain_betweenEndpoints_with_endpoints :
    ∀ (K : Region) (S : Set Tiling.Plane), TilesOn K S univ →
      ∀ axis : Axis, ∀ᵐ q : ℝ ∂volume,
        ∀ a ∈ sliceEndpointSet K S axis q,
          ∀ b ∈ sliceEndpointSet K S axis q, a < b →
            ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
              (owner : Fin n → S), x 0 = a ∧ x (Fin.last n) = b ∧
                IsFilledIndexedSliceChain K S axis q x owner ∧
                (∀ i, x i ∈ sliceEndpointSet K S axis q) := by
  classical
  intro K S hTile axis
  filter_upwards [eventually_avoids_translatedVertexLevels hTile.2.1 axis,
    eventually_sliceFiber_ae_univ hTile axis,
    genericSliceEndpointSet_locallyFinite K S hTile axis] with q hq hfull hlocal
  intro a ha b hb hab
  let E := sliceEndpointSet K S axis q
  let endpoints : Finset ℝ :=
    (hlocal (Icc a b) (Metric.isBounded_Icc a b)).toFinset
  have haS : a ∈ endpoints := by simp [endpoints, ha, hab.le]
  have hbS : b ∈ endpoints := by simp [endpoints, hb, hab.le]
  have hcard : 0 < endpoints.card := Finset.card_pos.mpr ⟨a, haS⟩
  obtain ⟨n, hncard⟩ : ∃ n, endpoints.card = n + 1 :=
    ⟨endpoints.card - 1, (Nat.sub_add_cancel hcard).symm⟩
  let e : Fin (n + 1) ≃o endpoints := Finset.orderIsoOfFin endpoints hncard
  let x : Fin (n + 1) → ℝ := fun i => (e i : ℝ)
  have hxmem (i : Fin (n + 1)) : x i ∈ endpoints := (e i).property
  have hxE (i : Fin (n + 1)) : x i ∈ E := by
    exact (show x i ∈ E ∩ Icc a b by simpa [endpoints] using hxmem i).1
  have hfirst : x 0 = a := by
    apply le_antisymm
    · obtain ⟨i, hi⟩ := e.surjective ⟨a, haS⟩
      have hei : (e i : ℝ) = a := congrArg Subtype.val hi
      rw [← hei]
      exact_mod_cast e.monotone (Fin.zero_le i)
    · exact (show x 0 ∈ E ∩ Icc a b by simpa [endpoints] using hxmem 0).2.1
  have hlast : x (Fin.last n) = b := by
    apply le_antisymm
    · exact (show x (Fin.last n) ∈ E ∩ Icc a b by
        simpa [endpoints] using hxmem (Fin.last n)).2.2
    · obtain ⟨i, hi⟩ := e.surjective ⟨b, hbS⟩
      have hei : (e i : ℝ) = b := congrArg Subtype.val hi
      rw [← hei]
      exact_mod_cast e.monotone (Fin.le_last i)
  have hn : 0 < n := by
    by_contra hn0
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    have hz : (0 : Fin 1) = Fin.last 0 := Subsingleton.elim _ _
    linarith [hfirst, hlast, congrArg x hz]
  have hlt (i : Fin n) : x i.castSucc < x i.succ :=
    e.strictMono Fin.castSucc_lt_succ
  have hnone (i : Fin n) : Disjoint E (Ioo (x i.castSucc) (x i.succ)) := by
    rw [Set.disjoint_left]
    intro z hzE hzI
    have hzS : z ∈ endpoints := by
      simp only [endpoints, Finite.mem_toFinset]
      refine ⟨hzE, ⟨?_, ?_⟩⟩
      · exact le_trans
          (show a ≤ x i.castSucc from
            (show x i.castSucc ∈ E ∩ Icc a b by
              simpa [endpoints] using hxmem i.castSucc).2.1) hzI.1.le
      · exact le_trans hzI.2.le
          (show x i.succ ≤ b from
            (show x i.succ ∈ E ∩ Icc a b by
              simpa [endpoints] using hxmem i.succ).2.2)
    obtain ⟨j, hj⟩ := e.surjective ⟨z, hzS⟩
    have hij : i.castSucc < j := (e.lt_iff_lt).mp (by
      change (e i.castSucc : ℝ) < (e j : ℝ)
      simpa [hj] using hzI.1)
    have hji : j < i.succ := (e.lt_iff_lt).mp (by
      change (e j : ℝ) < (e i.succ : ℝ)
      simpa [hj] using hzI.2)
    have hij' : i.val < j.val := by exact_mod_cast hij
    have hji' : j.val < i.val + 1 := by exact_mod_cast hji
    omega
  have hfilled (i : Fin n) := filledGap hTile hq hfull
    (hxE i.castSucc) (hxE i.succ) (hlt i) (hnone i)
  let owner : Fin n → S := fun i => (hfilled i).choose
  refine ⟨n, hn, x, owner, hfirst, hlast, ⟨e.strictMono, ?_⟩, hxE⟩
  intro i
  simpa only [owner] using (hfilled i).choose_spec

theorem genericSliceChain_betweenEndpoints :
    ∀ (K : Region) (S : Set Tiling.Plane), TilesOn K S univ →
      ∀ axis : Axis, ∀ᵐ q : ℝ ∂volume,
        ∀ a ∈ sliceEndpointSet K S axis q,
          ∀ b ∈ sliceEndpointSet K S axis q, a < b →
            ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
              (owner : Fin n → S), x 0 = a ∧ x (Fin.last n) = b ∧
                IsFilledIndexedSliceChain K S axis q x owner := by
  intro K S hTile axis
  filter_upwards [genericSliceChain_betweenEndpoints_with_endpoints K S hTile axis]
    with q hq
  intro a ha b hb hab
  obtain ⟨n, hn, x, owner, hfirst, hlast, hchain, _hendpoints⟩ :=
    hq a ha b hb hab
  exact ⟨n, hn, x, owner, hfirst, hlast, hchain⟩

theorem genericIndexedSliceChain_with_endpoints :
    ∀ (K : Region) (S : Set Tiling.Plane), TilesOn K S univ →
      ∀ axis : Axis, ∀ᵐ q : ℝ ∂volume,
        ∀ a b : ℝ, a < b →
          ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
            (owner : Fin n → S),
            x 0 ≤ a ∧ b ≤ x (Fin.last n) ∧
              IsFilledIndexedSliceChain K S axis q x owner ∧
              (∀ i, x i ∈ sliceEndpointSet K S axis q) := by
  intro K S hTile axis
  filter_upwards [genericSliceEndpointSet_unbounded K S hTile axis,
    genericSliceChain_betweenEndpoints_with_endpoints K S hTile axis]
      with q hunbounded hbetween
  intro a b hab
  obtain ⟨l, hlE, hla⟩ := not_bddBelow_iff.mp hunbounded.2 a
  obtain ⟨r, hrE, hbr⟩ := not_bddAbove_iff.mp hunbounded.1 b
  obtain ⟨n, hn, x, owner, hx0, hxlast, hchain, hendpoints⟩ :=
    hbetween l hlE r hrE (lt_trans hla (lt_trans hab hbr))
  refine ⟨n, hn, x, owner, ?_, ?_, hchain, hendpoints⟩
  · rw [hx0]
    exact hla.le
  · rw [hxlast]
    exact hbr.le

theorem genericIndexedSliceChain :
    ∀ (K : Region) (S : Set Tiling.Plane), TilesOn K S univ →
      ∀ axis : Axis, ∀ᵐ q : ℝ ∂volume,
        ∀ a b : ℝ, a < b →
          ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
            (owner : Fin n → S),
            x 0 ≤ a ∧ b ≤ x (Fin.last n) ∧
              IsFilledIndexedSliceChain K S axis q x owner := by
  intro K S hTile axis
  filter_upwards [genericIndexedSliceChain_with_endpoints K S hTile axis] with q hq
  intro a b hab
  obtain ⟨n, hn, x, owner, hleft, hright, hchain, _hendpoints⟩ := hq a b hab
  exact ⟨n, hn, x, owner, hleft, hright, hchain⟩



/-- A generic fixed fibre has finitely many actual endpoints in every bounded window. -/
theorem genericSliceEndpointSet_locallyFinite_fixed
    {K : Region} {S : Set Tiling.Plane} {axis : Axis} {q : ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (hq : q ∉ translatedVertexLevels K S axis) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (sliceEndpointSet K S axis q ∩ Q).Finite := by
  intro Q hQ
  obtain ⟨R, hQR⟩ := hQ.subset_closedBall (0 : ℝ)
  let C : Set ℝ := Metric.closedBall 0 R
  have hCcompact : IsCompact C := isCompact_closedBall 0 R
  have hloc := locallyFinite_placedSupportSlice hpacking axis q
  let active : Set S :=
    {t | (placedSupportSlice K axis q t.1 ∩ C).Nonempty}
  have hactive : active.Finite := by
    exact hloc.finite_nonempty_inter_compact hCcompact
  apply (hactive.biUnion fun t _ => placedOpenSlice_frontier_finite hq t).subset
  rintro x ⟨hxEndpoint, hxQ⟩
  have hxTiles := sliceEndpointSet_subset_tileFrontiers hpacking axis q hxEndpoint
  obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hxTiles
  refine Set.mem_biUnion ?_ hxt
  have hxSupport := frontier_placedOpenSlice_subset_support K axis q t.1 hxt
  exact ⟨x, hxSupport, hQR hxQ⟩

private theorem genericSliceEndpointSet_locallyFinite_of_packing
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) (axis : Axis) :
    ∀ᵐ q : ℝ ∂volume,
      ∀ Q : Set ℝ, Bornology.IsBounded Q →
        (sliceEndpointSet K S axis q ∩ Q).Finite := by
  filter_upwards [eventually_avoids_translatedVertexLevels hpacking axis] with q hq
  exact genericSliceEndpointSet_locallyFinite_fixed hpacking hq

private theorem exists_mem_Ioo_of_ae_real {P : ℝ → Prop} {a b : ℝ}
    (hab : a < b) (hP : ∀ᵐ x : ℝ ∂volume, P x) :
    ∃ x ∈ Ioo a b, P x := by
  have hμ : volume.restrict (Ioo a b) ≠ 0 := by
    intro hz
    have : volume (Ioo a b) = 0 := by
      rw [← Measure.restrict_apply_univ (Ioo a b), hz]
      simp
    rw [Real.volume_Ioo] at this
    simp [ENNReal.ofReal_eq_zero, not_le.mpr (sub_pos.mpr hab)] at this
  let hne : (ae (volume.restrict (Ioo a b))).NeBot := ae_neBot.mpr hμ
  have hp' : ∀ᵐ x ∂volume.restrict (Ioo a b), P x :=
    hP.filter_mono ae_restrict_le
  rcases @Filter.Eventually.exists ℝ _ (ae (volume.restrict (Ioo a b))) hne
      (hp'.and (ae_restrict_mem measurableSet_Ioo)) with ⟨x, hp, hx⟩
  exact ⟨x, hx, hp⟩


private theorem openInterval_subset_of_local_ae
    {U : Set ℝ} {l r : ℝ} (hlr : l < r)
    (hfull : ∀ᵐ x : ℝ ∂volume, x ∈ Ioo l r → x ∈ U)
    (hdisj : Disjoint (Ioo l r) (frontier U)) : Ioo l r ⊆ U := by
  rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Ioo hdisj with hin | hout
  · exact hin.trans interior_subset
  · obtain ⟨x, hx, hUx⟩ := exists_mem_Ioo_of_ae_real hlr hfull
    exact False.elim ((interior_subset (hout hx)) (hUx hx))


theorem filledGap_of_local_ae
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) {axis : Axis} {q l r : ℝ}
    (hq : q ∉ translatedVertexLevels K S axis)
    (hfull : ∀ᵐ x : ℝ ∂volume,
      x ∈ Ioo l r → slicePoint axis q x ∈ openUnion K S)
    (hl : l ∈ sliceEndpointSet K S axis q)
    (hr : r ∈ sliceEndpointSet K S axis q) (hlr : l < r)
    (hnone : Disjoint (sliceEndpointSet K S axis q) (Ioo l r)) :
    ∃ t : S, ∃ v w : Tiling.Plane, v ∈ K.vertices ∧ w ∈ K.vertices ∧
      l = axis.coord (v + t.1) ∧ r = axis.coord (w + t.1) ∧
      0 < axis.coord (w - v) ∧
      axisInterval axis q l r ⊆ t.1 +ᵥ K.openCarrier := by
  let U : Set ℝ := {x | slicePoint axis q x ∈ openUnion K S}
  let f : S → Set ℝ := fun t => placedOpenSlice K axis q t.1
  have hU : U = ⋃ t, f t := sliceFiber_eq_iUnion_placedOpenSlice K S axis q
  have hopen : ∀ t, IsOpen (f t) := fun t =>
    (isOpen_interior.vadd t.1).preimage (continuous_slicePoint axis q)
  have hpair : Set.Pairwise Set.univ (Disjoint on f) := by
    intro s _ t _ hst
    change Disjoint (f s) (f t)
    rw [Set.disjoint_left]
    intro x hxs hxt
    exact Set.disjoint_left.mp
      ((isPacking_iff_openCarrier_disjoint K S).mp
        hpacking s.2 t.2 (fun h => hst (Subtype.ext h))) hxs hxt
  have hgapU : Ioo l r ⊆ U := by
    apply openInterval_subset_of_local_ae hlr
      (by simpa [U] using hfull)
    simpa [sliceEndpointSet, U] using hnone.symm
  obtain ⟨t, hgap⟩ := one_member_contains_openInterval hlr hopen hpair
    (hgapU.trans_eq hU)
  have hfront : l ∈ frontier (f t) ∧ r ∈ frontier (f t) :=
    endpoints_mem_frontier_of_interval_subset hlr hl hr
      (by
        intro x hx
        change x ∈ U
        rw [hU]
        exact Set.mem_iUnion.mpr ⟨t, hx⟩) hgap
  cases axis with
  | horizontal =>
      have hgeneric : q - t.1.im ∉ K.vertexFinset.image Complex.im := by
        intro h
        obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp h
        apply hq
        refine ⟨(t, ⟨v, ?_⟩), ?_⟩
        · rw [← K.coe_vertexFinset]; exact hv
        · simp only [Axis.transverseCoord, Complex.add_im]
          linarith [hvq]
      have heq : f t = t.1.re +ᵥ horizontalSlice K (q - t.1.im) := by
        ext x
        simp only [f, placedOpenSlice, slicePoint, Set.mem_preimage,
          horizontalSlice, Set.mem_ofPred_eq,
          Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
        constructor <;> intro hx
        · convert hx using 1
          apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
        · convert hx using 1
          apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
      have hgap' : Ioo (l - t.1.re) (r - t.1.re) ⊆
          horizontalSlice K (q - t.1.im) := by
        intro x hx
        have hx' := hgap (show x + t.1.re ∈ Ioo l r by
          constructor <;> linarith [hx.1, hx.2])
        rw [heq] at hx'
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm] using hx'
      have hf' : l - t.1.re ∈ frontier
            (horizontalSlice K (q - t.1.im)) ∧
          r - t.1.re ∈ frontier (horizontalSlice K (q - t.1.im)) := by
        rw [heq] at hfront
        have htranslate := (Homeomorph.addLeft t.1.re).image_frontier
          (horizontalSlice K (q - t.1.im))
        simp only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] at htranslate
        rw [← htranslate] at hfront
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          sub_eq_add_neg, add_comm] using hfront
      obtain ⟨v, w, hv, hw⟩ := horizontalSlice_componentEndpoints K hgeneric
        (by linarith) hgap' hf'.1 hf'.2
      refine ⟨t, v.1, w.1, v.2, w.2, ?_, ?_, ?_, ?_⟩
      · simp only [Axis.coord, Complex.add_re]; linarith [hv]
      · simp only [Axis.coord, Complex.add_re]; linarith [hw]
      · simp only [Axis.coord, Complex.sub_re]; linarith [hv, hw, hlr]
      · intro z hz
        have hz' := hgap hz.2
        change slicePoint Axis.horizontal q z.re ∈ t.1 +ᵥ K.openCarrier at hz'
        convert hz' using 1
        apply Complex.ext <;> simp [slicePoint, hz.1]
  | vertical =>
      have hgeneric : q - t.1.re ∉ K.vertexFinset.image Complex.re := by
        intro h
        obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp h
        apply hq
        refine ⟨(t, ⟨v, ?_⟩), ?_⟩
        · rw [← K.coe_vertexFinset]; exact hv
        · simp only [Axis.transverseCoord, Complex.add_re]
          linarith [hvq]
      have heq : f t = t.1.im +ᵥ verticalSlice K (q - t.1.re) := by
        ext x
        simp only [f, placedOpenSlice, slicePoint, Set.mem_preimage,
          verticalSlice, Set.mem_ofPred_eq,
          Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
        constructor <;> intro hx
        · convert hx using 1
          apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
        · convert hx using 1
          apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
      have hgap' : Ioo (l - t.1.im) (r - t.1.im) ⊆
          verticalSlice K (q - t.1.re) := by
        intro x hx
        have hx' := hgap (show x + t.1.im ∈ Ioo l r by
          constructor <;> linarith [hx.1, hx.2])
        rw [heq] at hx'
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm] using hx'
      have hf' : l - t.1.im ∈ frontier
            (verticalSlice K (q - t.1.re)) ∧
          r - t.1.im ∈ frontier (verticalSlice K (q - t.1.re)) := by
        rw [heq] at hfront
        have htranslate := (Homeomorph.addLeft t.1.im).image_frontier
          (verticalSlice K (q - t.1.re))
        simp only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] at htranslate
        rw [← htranslate] at hfront
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          sub_eq_add_neg, add_comm] using hfront
      obtain ⟨v, w, hv, hw⟩ := verticalSlice_componentEndpoints K hgeneric
        (by linarith) hgap' hf'.1 hf'.2
      refine ⟨t, v.1, w.1, v.2, w.2, ?_, ?_, ?_, ?_⟩
      · simp only [Axis.coord, Complex.add_im]; linarith [hv]
      · simp only [Axis.coord, Complex.add_im]; linarith [hw]
      · simp only [Axis.coord, Complex.sub_im]; linarith [hv, hw, hlr]
      · intro z hz
        have hz' := hgap hz.2
        change slicePoint Axis.vertical q z.im ∈ t.1 +ᵥ K.openCarrier at hz'
        convert hz' using 1
        apply Complex.ext <;> simp [slicePoint, hz.1]

/-- Construct a filled chain between actual endpoints at a specified generic level.
Only local almost-everywhere coverage between the endpoints is required. -/
theorem genericSliceChain_betweenEndpoints_fixed_of_local_ae
    {K : Region} {S : Set Tiling.Plane} {axis : Axis} {q : ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (hq : q ∉ translatedVertexLevels K S axis)
    {a b : ℝ} (ha : a ∈ sliceEndpointSet K S axis q)
    (hb : b ∈ sliceEndpointSet K S axis q) (hab : a < b)
    (hfull : ∀ᵐ x : ℝ ∂volume,
      x ∈ Ioo a b → slicePoint axis q x ∈ openUnion K S) :
    ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
      (owner : Fin n → S), x 0 = a ∧ x (Fin.last n) = b ∧
        IsFilledIndexedSliceChain K S axis q x owner ∧
        (∀ i, x i ∈ sliceEndpointSet K S axis q) := by
  have hlocal := genericSliceEndpointSet_locallyFinite_fixed hpacking hq
  let E := sliceEndpointSet K S axis q
  let endpoints : Finset ℝ :=
    (hlocal (Icc a b) (Metric.isBounded_Icc a b)).toFinset
  have haS : a ∈ endpoints := by simp [endpoints, ha, hab.le]
  have hbS : b ∈ endpoints := by simp [endpoints, hb, hab.le]
  have hcard : 0 < endpoints.card := Finset.card_pos.mpr ⟨a, haS⟩
  obtain ⟨n, hncard⟩ : ∃ n, endpoints.card = n + 1 :=
    ⟨endpoints.card - 1, (Nat.sub_add_cancel hcard).symm⟩
  let e : Fin (n + 1) ≃o endpoints := Finset.orderIsoOfFin endpoints hncard
  let x : Fin (n + 1) → ℝ := fun i => (e i : ℝ)
  have hxmem (i : Fin (n + 1)) : x i ∈ endpoints := (e i).property
  have hxE (i : Fin (n + 1)) : x i ∈ E := by
    exact (show x i ∈ E ∩ Icc a b by simpa [endpoints] using hxmem i).1
  have hfirst : x 0 = a := by
    apply le_antisymm
    · obtain ⟨i, hi⟩ := e.surjective ⟨a, haS⟩
      have hei : (e i : ℝ) = a := congrArg Subtype.val hi
      rw [← hei]
      exact_mod_cast e.monotone (Fin.zero_le i)
    · exact (show x 0 ∈ E ∩ Icc a b by simpa [endpoints] using hxmem 0).2.1
  have hlast : x (Fin.last n) = b := by
    apply le_antisymm
    · exact (show x (Fin.last n) ∈ E ∩ Icc a b by
        simpa [endpoints] using hxmem (Fin.last n)).2.2
    · obtain ⟨i, hi⟩ := e.surjective ⟨b, hbS⟩
      have hei : (e i : ℝ) = b := congrArg Subtype.val hi
      rw [← hei]
      exact_mod_cast e.monotone (Fin.le_last i)
  have hn : 0 < n := by
    by_contra hn0
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    have hz : (0 : Fin 1) = Fin.last 0 := Subsingleton.elim _ _
    linarith [hfirst, hlast, congrArg x hz]
  have hlt (i : Fin n) : x i.castSucc < x i.succ :=
    e.strictMono Fin.castSucc_lt_succ
  have hnone (i : Fin n) : Disjoint E (Ioo (x i.castSucc) (x i.succ)) := by
    rw [Set.disjoint_left]
    intro z hzE hzI
    have hzS : z ∈ endpoints := by
      simp only [endpoints, Finite.mem_toFinset]
      refine ⟨hzE, ⟨?_, ?_⟩⟩
      · exact le_trans
          (show a ≤ x i.castSucc from
            (show x i.castSucc ∈ E ∩ Icc a b by
              simpa [endpoints] using hxmem i.castSucc).2.1) hzI.1.le
      · exact le_trans hzI.2.le
          (show x i.succ ≤ b from
            (show x i.succ ∈ E ∩ Icc a b by
              simpa [endpoints] using hxmem i.succ).2.2)
    obtain ⟨j, hj⟩ := e.surjective ⟨z, hzS⟩
    have hij : i.castSucc < j := (e.lt_iff_lt).mp (by
      change (e i.castSucc : ℝ) < (e j : ℝ)
      simpa [hj] using hzI.1)
    have hji : j < i.succ := (e.lt_iff_lt).mp (by
      change (e j : ℝ) < (e i.succ : ℝ)
      simpa [hj] using hzI.2)
    have hij' : i.val < j.val := by exact_mod_cast hij
    have hji' : j.val < i.val + 1 := by exact_mod_cast hji
    omega
  have hfilled (i : Fin n) := filledGap_of_local_ae hpacking hq
    (by
      filter_upwards [hfull] with y hy
      intro hyI
      apply hy
      have hxi : x i.castSucc ≤ y := le_of_lt hyI.1
      have hxs : y ≤ x i.succ := le_of_lt hyI.2
      exact ⟨lt_of_le_of_lt
          ((show x i.castSucc ∈ E ∩ Icc a b by
            simpa [endpoints] using hxmem i.castSucc).2.1) hyI.1,
        lt_of_lt_of_le hyI.2
          ((show x i.succ ∈ E ∩ Icc a b by
            simpa [endpoints] using hxmem i.succ).2.2)⟩)
      (hxE i.castSucc) (hxE i.succ) (hlt i) (hnone i)
  let owner : Fin n → S := fun i => (hfilled i).choose
  refine ⟨n, hn, x, owner, hfirst, hlast, ⟨e.strictMono, ?_⟩, hxE⟩
  intro i
  simpa only [owner] using (hfilled i).choose_spec


theorem genericSliceChain_betweenEndpoints_of_local_ae :
    ∀ (K : Region) (S : Set Tiling.Plane),
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) →
      ∀ axis : Axis, ∀ᵐ q : ℝ ∂volume,
        ∀ a ∈ sliceEndpointSet K S axis q,
          ∀ b ∈ sliceEndpointSet K S axis q, a < b →
            (∀ᵐ x : ℝ ∂volume,
              x ∈ Ioo a b → slicePoint axis q x ∈ openUnion K S) →
            ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
              (owner : Fin n → S), x 0 = a ∧ x (Fin.last n) = b ∧
                IsFilledIndexedSliceChain K S axis q x owner ∧
                (∀ i, x i ∈ sliceEndpointSet K S axis q) := by
  intro K S hpacking axis
  filter_upwards [eventually_avoids_translatedVertexLevels hpacking axis] with q hq
  intro a ha b hb hab hfull
  exact genericSliceChain_betweenEndpoints_fixed_of_local_ae hpacking hq ha hb hab hfull

theorem frontier_unbounded_of_ae_univ
    {K : Region} {S : Set Tiling.Plane} {axis : Axis} {q : ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (hq : q ∉ translatedVertexLevels K S axis)
    (hfull : {x : ℝ | slicePoint axis q x ∈ openUnion K S} =ᵐ[volume] univ) :
    ¬ BddAbove (sliceEndpointSet K S axis q) ∧
      ¬ BddBelow (sliceEndpointSet K S axis q) := by
  let U : Set ℝ := {x : ℝ | slicePoint axis q x ∈ openUnion K S}
  let f : S → Set ℝ := fun t => placedOpenSlice K axis q t.1
  have hU : U = ⋃ t, f t := sliceFiber_eq_iUnion_placedOpenSlice K S axis q
  have hopen : ∀ t, IsOpen (f t) := fun t =>
    (isOpen_interior.vadd t.1).preimage (continuous_slicePoint axis q)
  have hbdd : ∀ t, Bornology.IsBounded (f t) := fun t => by
    cases axis with
    | horizontal =>
        have hgeneric : q - t.1.im ∉ K.vertexFinset.image Complex.im := by
          intro h
          obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp h
          apply hq
          rw [translatedVertexLevels]
          refine ⟨(t, ⟨v, ?_⟩), ?_⟩
          · rw [← K.coe_vertexFinset]
            exact hv
          · simp only [Axis.transverseCoord, Complex.add_im]
            linarith [hvq]
        have hfinite := horizontalSlice_isFiniteIntervalRegion K hgeneric
        have heq : f t = t.1.re +ᵥ horizontalSlice K (q - t.1.im) := by
          change placedOpenSlice K Axis.horizontal q t.1 = _
          ext x
          simp only [placedOpenSlice, slicePoint, Set.mem_preimage,
            horizontalSlice, Set.mem_ofPred_eq,
            Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
          constructor <;> intro hx
          · convert hx using 1
            apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
          · convert hx using 1
            apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
        rw [heq]
        exact isFiniteIntervalRegion_isBounded
          (isFiniteIntervalRegion_vadd hfinite t.1.re)
    | vertical =>
        have hgeneric : q - t.1.re ∉ K.vertexFinset.image Complex.re := by
          intro h
          obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp h
          apply hq
          rw [translatedVertexLevels]
          refine ⟨(t, ⟨v, ?_⟩), ?_⟩
          · rw [← K.coe_vertexFinset]
            exact hv
          · simp only [Axis.transverseCoord, Complex.add_re]
            linarith [hvq]
        have hfinite := verticalSlice_isFiniteIntervalRegion K hgeneric
        have heq : f t = t.1.im +ᵥ verticalSlice K (q - t.1.re) := by
          change placedOpenSlice K Axis.vertical q t.1 = _
          ext x
          simp only [placedOpenSlice, slicePoint, Set.mem_preimage,
            verticalSlice, Set.mem_ofPred_eq,
            Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
          constructor <;> intro hx
          · convert hx using 1
            apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
          · convert hx using 1
            apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
        rw [heq]
        exact isFiniteIntervalRegion_isBounded
          (isFiniteIntervalRegion_vadd hfinite t.1.im)
  have hpair : Set.Pairwise Set.univ (Disjoint on f) := by
    intro s _ t _ hst
    change Disjoint (f s) (f t)
    rw [Set.disjoint_left]
    intro x hxs hxt
    have hp := (isPacking_iff_openCarrier_disjoint K S).mp hpacking
    apply Set.disjoint_left.mp (hp s.2 t.2 (fun h => hst (Subtype.ext h)))
    · exact hxs
    · exact hxt
  change ¬ BddAbove (frontier U) ∧ ¬ BddBelow (frontier U)
  exact ⟨frontier_not_bddAbove_of_bounded_disjoint_openCover
      hfull hopen hbdd hpair hU,
    frontier_not_bddBelow_of_bounded_disjoint_openCover
      hfull hopen hbdd hpair hU⟩

theorem genericIndexedSliceChain_of_ae_univ :
    ∀ (K : Region) (S : Set Tiling.Plane),
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) →
      ∀ axis : Axis, ∀ᵐ q : ℝ ∂volume,
        ({x : ℝ | slicePoint axis q x ∈ openUnion K S} =ᵐ[volume] univ) →
        ∀ a b : ℝ, a < b →
          ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
            (owner : Fin n → S),
            x 0 ≤ a ∧ b ≤ x (Fin.last n) ∧
              IsFilledIndexedSliceChain K S axis q x owner ∧
              (∀ i, x i ∈ sliceEndpointSet K S axis q) := by
  intro K S hpacking axis
  filter_upwards [
    genericSliceChain_betweenEndpoints_of_local_ae K S hpacking axis,
    eventually_avoids_translatedVertexLevels hpacking axis] with q hbetween hq
  intro hfull a b hab
  obtain ⟨hunbddAbove, hunbddBelow⟩ :=
    frontier_unbounded_of_ae_univ hpacking hq hfull
  obtain ⟨l, hlE, hla⟩ := not_bddBelow_iff.mp hunbddBelow a
  obtain ⟨r, hrE, hbr⟩ := not_bddAbove_iff.mp hunbddAbove b
  obtain ⟨n, hn, x, owner, hx0, hxlast, hchain, hendpoints⟩ :=
    hbetween l hlE r hrE (lt_trans hla (lt_trans hab hbr)) (by
      filter_upwards [hfull] with y hy
      intro hyI
      exact hy.mpr (Set.mem_univ y))
  refine ⟨n, hn, x, owner, ?_, ?_, hchain, hendpoints⟩
  · rw [hx0]
    exact hla.le
  · rw [hxlast]
    exact hbr.le


end Tiling.AxisParallel.Foundations.FilledSliceChains
