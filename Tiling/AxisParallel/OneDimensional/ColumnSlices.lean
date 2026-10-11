import Tiling.AxisParallel.Foundations.GenericSlices
import Tiling.AxisParallel.Foundations.OneDimensionalTilings
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.OneDimensional.FiniteInterval.WholeLine
import Tiling.AxisParallel.OneDimensional.FiniteInterval.PeriodMass

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.OneDimensional.ColumnSlices

open Tiling.AxisParallel
open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.FiniteInterval

/-- The vertical section of a planar region at horizontal coordinate `r`. -/
def verticalSlice (K : Region) (r : ℝ) : Set ℝ :=
  {y : ℝ | (r : ℂ) + (y : ℂ) * Complex.I ∈ K.openCarrier}

/-- Multiplicity of translates of `B` by `Y`; used only under countability obtained from a
whole-line tiling or periodic local finiteness. -/
private def lineMultiplicity (B Y : Set ℝ) (x : ℝ) : ENNReal :=
  ∑' y : Y, (y.1 +ᵥ B).indicator (1 : ℝ → ENNReal) x

private theorem verticalSlice_eq_generic (K : Region) (r : ℝ) :
    verticalSlice K r =
      Tiling.AxisParallel.Foundations.GenericSlices.verticalSlice K r := by
  ext y
  change (r + (y : ℂ) * Complex.I ∈ K.openCarrier) ↔
    Complex.mk r y ∈ K.openCarrier
  have heq : (r : ℂ) + (y : ℂ) * Complex.I = Complex.mk r y := by
    apply Complex.ext <;> simp
  rw [heq]

theorem finiteClosedIntervals_interior_isFiniteIntervalRegion :
    ∀ {n : ℕ} (a b : Fin n → ℝ),
      IsFiniteIntervalRegion (interior (⋃ i, Set.Icc (a i) (b i))) := by
  intro n a b
  obtain ⟨P⟩ := Tiling.AxisParallel.Foundations.GenericSlices.finiteClosedIntervals_merge a b
  exact ⟨P.n, P.left, P.right, P.lt, P.union_eq⟩

private theorem verticalSlice_closedRectangulationPresentation :
    ∀ (K : Region) {r : ℝ}, r ∉ K.vertexFinset.image Complex.re →
      ∃ (n : ℕ) (a b : Fin n → ℝ),
        closure (verticalSlice K r) = ⋃ i, Set.Icc (a i) (b i) ∧
        verticalSlice K r = interior (⋃ i, Set.Icc (a i) (b i)) := by
  intro K r hr
  rw [verticalSlice_eq_generic]
  exact Tiling.AxisParallel.Foundations.GenericSlices.verticalSlice_closedIntervals K hr

private theorem verticalSlice_locallyConstant_offVertexLevels :
    ∀ (K : Region) {r : ℝ},
      r ∉ K.vertexFinset.image Complex.re →
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - r| < ε →
        verticalSlice K s = verticalSlice K r := by
  intro K r hr
  simpa only [verticalSlice_eq_generic] using
    Tiling.AxisParallel.Foundations.GenericSlices.verticalSlice_locallyConstant K hr

private theorem verticalSlice_finiteIntervals_proof :
    ∀ (K : Region) {r : ℝ},
      r ∉ K.vertexFinset.image Complex.re →
      IsFiniteIntervalRegion (verticalSlice K r) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - r| < ε →
        verticalSlice K s = verticalSlice K r := by
  intro K r hr
  constructor
  · rw [verticalSlice_eq_generic]
    exact Tiling.AxisParallel.Foundations.GenericSlices.verticalSlice_isFiniteIntervalRegion K hr
  · exact verticalSlice_locallyConstant_offVertexLevels K hr

private theorem columnPacking_iff_slicePacking :
    ∀ {K : Region} {c : ℝ} {Y : Set ℝ},
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements
            {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) ↔
      ∀ r : ℝ, Set.Pairwise Y
        (MeasureTheory.AEDisjoint volume on
          ((· +ᵥ verticalSlice K r) : ℝ → Set ℝ)) := by
  intro K c Y
  rw [Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint]
  constructor
  · intro hpacking r y hyY y' hy'Y hyy'
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro x hxy hxy'
    let sy : Tiling.Plane := (c : ℂ) + (y : ℂ) * Complex.I
    let sy' : Tiling.Plane := (c : ℂ) + (y' : ℂ) * Complex.I
    have hsy : sy ∈ {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
      exact ⟨by simp [sy], by simpa [sy] using hyY⟩
    have hsy' : sy' ∈ {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
      exact ⟨by simp [sy'], by simpa [sy'] using hy'Y⟩
    have hsysy' : sy ≠ sy' := by
      intro heq
      apply hyy'
      simpa [sy, sy'] using congrArg Complex.im heq
    have hd : Disjoint (sy +ᵥ K.openCarrier) (sy' +ᵥ K.openCarrier) :=
      hpacking hsy hsy' hsysy'
    rw [Set.disjoint_left] at hd
    refine hd (a := (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I)) ?_ ?_
    · change x ∈ y +ᵥ verticalSlice K r at hxy
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxy
      rw [verticalSlice] at hxy
      change r + ((-y + x : ℝ) : ℂ) * Complex.I ∈ K.openCarrier at hxy
      have heq : -sy + (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I) =
          r + ((-y + x : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [sy]
      change -sy + (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I) ∈ K.openCarrier
      rwa [heq]
    · change x ∈ y' +ᵥ verticalSlice K r at hxy'
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxy'
      rw [verticalSlice] at hxy'
      change r + ((-y' + x : ℝ) : ℂ) * Complex.I ∈ K.openCarrier at hxy'
      have heq : -sy' + (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I) =
          r + ((-y' + x : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [sy']
      change -sy' + (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I) ∈ K.openCarrier
      rwa [heq]
  · intro hslices s hs t ht hst
    change Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.openCarrier)
    rw [Set.disjoint_left]
    intro z hzs hzt
    obtain ⟨hsre, hsY⟩ := hs
    obtain ⟨htre, htY⟩ := ht
    have hsimne : s.im ≠ t.im := by
      intro him
      apply hst
      exact Complex.ext (hsre.trans htre.symm) him
    let r : ℝ := z.re - c
    let x : ℝ := z.im
    have hxs : x ∈ s.im +ᵥ verticalSlice K r := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      rw [verticalSlice]
      change r + ((-s.im + x : ℝ) : ℂ) * Complex.I ∈ K.openCarrier
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzs
      convert hzs using 1
      apply Complex.ext
      · simp [r, x, hsre]
        ring
      · simp [r, x]
    have hxt : x ∈ t.im +ᵥ verticalSlice K r := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      rw [verticalSlice]
      change r + ((-t.im + x : ℝ) : ℂ) * Complex.I ∈ K.openCarrier
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzt
      convert hzt using 1
      apply Complex.ext
      · simp [r, x, htre]
        ring
      · simp [r, x]
    have hopenSlice : IsOpen (verticalSlice K r) := by
      apply K.openCarrier_regularOpen.1.preimage
      fun_prop
    have hopenInter : IsOpen
        ((s.im +ᵥ verticalSlice K r) ∩ (t.im +ᵥ verticalSlice K r)) :=
      (hopenSlice.vadd s.im).inter (hopenSlice.vadd t.im)
    have hzero := (hslices r hsY htY hsimne).eq
    exact (ne_of_gt (hopenInter.measure_pos volume ⟨x, hxs, hxt⟩)) hzero

private theorem periodicPacking_multiplicity_le_one :
    ∀ {B' Y : Set ℝ},
      Set.Pairwise Y
        (MeasureTheory.AEDisjoint volume on ((· +ᵥ B') : ℝ → Set ℝ)) →
      Y.Countable → ∀ᵐ x ∂volume, lineMultiplicity B' Y x ≤ 1 := by
  intro B' Y hpacking hcountable
  let _ : Countable Y := hcountable
  have hover : ∀ᵐ x ∂volume, ∀ y z : Y, y ≠ z →
      ¬ (x ∈ y.1 +ᵥ B' ∧ x ∈ z.1 +ᵥ B') := by
    apply ae_all_iff.mpr
    intro y
    apply ae_all_iff.mpr
    intro z
    by_cases hyz : y = z
    · filter_upwards [] with x
      simp [hyz]
    · have hz : volume ((y.1 +ᵥ B') ∩ (z.1 +ᵥ B')) = 0 :=
        hpacking y.2 z.2 (fun h ↦ hyz (Subtype.ext h))
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx
      intro _
      simpa only [mem_inter_iff, not_and] using hx
  filter_upwards [hover] with x hx
  rw [lineMultiplicity]
  by_cases hnone : ∀ y : Y, x ∉ y.1 +ᵥ B'
  · simp [hnone]
  · have hex : ∃ y : Y, x ∈ y.1 +ᵥ B' := by
      simpa only [not_not] using not_forall.mp hnone
    obtain ⟨y, hy⟩ := hex
    rw [tsum_eq_single y]
    · simp [hy]
    · intro z hzy
      have hz : x ∉ z.1 +ᵥ B' := fun hz ↦ hx y z (Ne.symm hzy) ⟨hy, hz⟩
      simp [hz]

private theorem mem_openUnion_column_iff
    (K : Region) (c r y : ℝ) (Y : Set ℝ) :
    ((c + r : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
        openUnion K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} ↔
      ∃ t : Y, y ∈ t.1 +ᵥ verticalSlice K r := by
  rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
  constructor
  · rw [Set.mem_iUnion]
    rintro ⟨⟨z, hzre, hzY⟩, hz⟩
    refine ⟨⟨z.im, hzY⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, verticalSlice]
    change r + ((-z.im + y : ℝ) : ℂ) * Complex.I ∈ K.openCarrier
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz
    convert hz using 1
    apply Complex.ext
    · simp [hzre]
    · simp
  · rintro ⟨t, ht⟩
    let z : Tiling.Plane := (c : ℂ) + (t.1 : ℂ) * Complex.I
    rw [Set.mem_iUnion]
    refine ⟨⟨z, by simp [z], by simp [z, t.2]⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, verticalSlice] at ht
    change -z + (((c + r : ℝ) : ℂ) + (y : ℂ) * Complex.I) ∈ K.openCarrier
    change r + ((-t.1 + y : ℝ) : ℂ) * Complex.I ∈ K.openCarrier at ht
    convert ht using 1
    apply Complex.ext <;> simp [z]

private theorem openUnion_column_fubini
    {K : Region} {c : ℝ} {Y : Set ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y})) :
    ∀ᵐ x : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume,
      ((((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
          openUnion K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) ↔
        (((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
          regularSupport K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y})) := by
  have hae := Tiling.AxisParallel.openUnion_aeEq_regularSupport hpacking
  have hpull :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hae
  have hprod : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      (((p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈
          openUnion K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) ↔
        ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈
          regularSupport K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y})) := by
    filter_upwards [hpull] with p hp
    have heq : ({ re := p.1, im := p.2 } : ℂ) =
        (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    change (({ re := p.1, im := p.2 } : ℂ) ∈
      openUnion K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) =
      (({ re := p.1, im := p.2 } : ℂ) ∈
        regularSupport K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) at hp
    rw [heq] at hp
    exact Iff.of_eq hp
  exact MeasureTheory.Measure.ae_ae_of_ae_prod hprod

private theorem column_centres_countable
    {K : Region} {c : ℝ} {Y : Set ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y})) : Y.Countable := by
  let Q : Set Tiling.Plane := {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}
  let P := K.polygonalProtoTiling Q
  let F : Q → Set Tiling.Plane := fun q ↦ (q : Tiling.Plane) +ᵥ K.support
  let placementOf : Q → P.placements := fun q ↦ ⟨((q : Tiling.Plane), ()), q.2⟩
  have hinj : Function.Injective placementOf := by
    intro a b hab
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) hab)
  have hloc : LocallyFinite F := by
    have h := (P.locallyFinite_placedTile hpacking).comp_injective hinj
    change LocallyFinite F at h
    exact h
  have hne : ∀ q : Q, (F q).Nonempty := by
    intro q
    obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
    exact ⟨q.1 + x, ⟨x, interior_subset hx, rfl⟩⟩
  let _ : Countable Q := Set.countable_univ_iff.mp (hloc.countable_univ hne)
  let e : Y → Q := fun y ↦
    ⟨(c : ℂ) + (y.1 : ℂ) * Complex.I, by simp [Q, y.2]⟩
  have he : Function.Injective e := by
    intro y z hyz
    apply Subtype.ext
    simpa [e] using congrArg (fun w : Q ↦ w.1.im) hyz
  let _ : Countable Y := he.countable
  exact Set.countable_coe_iff.mp inferInstance

/-- A complete vertical centre column tiles every nonempty generic vertical slice. -/
theorem genericSliceTilings_of_completeColumn :
    ∀ {K : Region} {c : ℝ} {Y : Set ℝ}, Y.Nonempty →
      IsCenterColumn Axis.vertical K
        {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} →
      ∀ r : ℝ, r ∉ K.vertexFinset.image Complex.re →
        (verticalSlice K r).Nonempty → LineTiles (verticalSlice K r) Y := by
  intro K c Y hY hC r hr hBr
  let C : Set Tiling.Plane := {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}
  have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements C) := hC.1
  have hpair := (columnPacking_iff_slicePacking (K := K) (c := c) (Y := Y)).mp hpacking
  have hcount : Y.Countable := column_centres_countable hpacking
  have hopenB : IsOpen (verticalSlice K r) := by
    apply K.openCarrier_regularOpen.1.preimage
    fun_prop
  refine ⟨hopenB.measurableSet, MeasurableSet.univ, hcount, hpair r, ?_⟩
  obtain ⟨ε, hε, hconst⟩ :=
    verticalSlice_locallyConstant_offVertexLevels K hr
  have hfub := openUnion_column_fubini hpacking
  have hdense : Dense {x : ℝ | ∀ᵐ y : ℝ ∂volume,
      ((((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ openUnion K C) ↔
        (((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ regularSupport K C))} :=
    volume.dense_of_ae hfub
  have hopenI : IsOpen (Set.Ioo (c + r - ε) (c + r + ε)) := isOpen_Ioo
  have hneI : (Set.Ioo (c + r - ε) (c + r + ε)).Nonempty := by
    refine ⟨c + r, ?_⟩
    simp only [Set.mem_Ioo]
    constructor <;> linarith
  obtain ⟨x, hxgood, hxI⟩ := hdense.exists_mem_open hopenI hneI
  let s := x - c
  have hsclose : |s - r| < ε := by
    rw [abs_lt]
    change -ε < x - c - r ∧ x - c - r < ε
    simp only [Set.mem_Ioo] at hxI
    constructor <;> linarith
  have hslice : verticalSlice K s = verticalSlice K r := hconst s hsclose
  have hBs : (verticalSlice K s).Nonempty := hslice.symm ▸ hBr
  have hsupport : ∀ y : ℝ,
      ((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ regularSupport K C := by
    intro y
    obtain ⟨t, htY⟩ := hY
    obtain ⟨b, hb⟩ := hBs
    let y₀ := t + b
    have hopenmem : ((c + s : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I ∈ openUnion K C :=
      (mem_openUnion_column_iff K c s y₀ Y).2 ⟨⟨t, htY⟩, by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa [y₀] using hb⟩
    have hseed : ((c + s : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I ∈
        regularSupport K C := by
      change _ ∈ interior (closure (openUnion K C))
      have hopenU : IsOpen (openUnion K C) :=
        isOpen_iUnion fun q ↦ K.openCarrier_regularOpen.1.vadd q.1
      have hint : ((c + s : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I ∈
          interior (openUnion K C) := by
        rw [hopenU.interior_eq]
        exact hopenmem
      exact interior_mono subset_closure hint
    have hinv := hC.2.2.2 (y - y₀)
    have hv : ((y - y₀ : ℝ) : ℂ) * Complex.I +ᵥ
        (((c + s : ℝ) : ℂ) + (y₀ : ℂ) * Complex.I) ∈
          ((y - y₀ : ℝ) : ℂ) * Complex.I +ᵥ regularSupport K C :=
      ⟨_, hseed, rfl⟩
    rw [hinv] at hv
    convert hv using 1
    apply Complex.ext <;> simp [s]
  filter_upwards [hxgood] with y hy
  simp only [Set.mem_univ, true_iff]
  have hopenmem : ((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ openUnion K C :=
    hy.mpr (hsupport y)
  have h := (mem_openUnion_column_iff K c s y Y).1 (by
    convert hopenmem using 1
    apply Complex.ext <;> simp [s])
  simpa only [hslice] using h

private theorem openUnion_column_vertical_vadd_ae
    {K : Region} {c a : ℝ} {Y : Set ℝ}
    (_hYcount : Y.Countable)
    (htiles : ∀ r : ℝ, r ∉ K.vertexFinset.image Complex.re →
      (verticalSlice K r).Nonempty → LineTiles (verticalSlice K r) Y) :
    (((a : ℂ) * Complex.I) +ᵥ
        openUnion K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) =ᵐ[volume]
      openUnion K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
  let C : Set Tiling.Plane := {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}
  let E : Set ℝ := c +ᵥ (K.vertexFinset.image Complex.re : Set ℝ)
  have hEfinite : E.Finite := by
    have hfin : ((K.vertexFinset.image Complex.re : Finset ℝ) : Set ℝ).Finite :=
      (K.vertexFinset.image Complex.re).finite_toSet
    have h := hfin.image (fun t : ℝ ↦ c + t)
    convert h using 1
    ext x
    change x ∈ c +ᵥ (K.vertexFinset.image Complex.re : Set ℝ) ↔ _
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change (-c + x ∈ (K.vertexFinset.image Complex.re : Set ℝ)) ↔
      x ∈ (fun t : ℝ ↦ c + t) '' (K.vertexFinset.image Complex.re : Set ℝ)
    constructor
    · intro hv
      exact ⟨-c + x, hv, by linarith⟩
    · rintro ⟨v, hv, hvx⟩
      convert hv using 1
      linarith
  have hgeneric : ∀ᵐ x : ℝ ∂volume,
      x - c ∉ K.vertexFinset.image Complex.re := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hEfinite.measure_zero volume)] with x hx
    intro hbad
    apply hx
    refine ⟨x - c, ?_, ?_⟩
    · simpa using hbad
    · simp
  have hiter : ∀ᵐ x : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume,
      (((x : ℂ) + (y : ℂ) * Complex.I ∈ ((a : ℂ) * Complex.I) +ᵥ openUnion K C) ↔
        ((x : ℂ) + (y : ℂ) * Complex.I ∈ openUnion K C)) := by
    filter_upwards [hgeneric] with x hxgen
    let r := x - c
    by_cases hB : (verticalSlice K r).Nonempty
    · have ht := htiles r hxgen hB
      have hcov : ∀ᵐ y : ℝ ∂volume, ∃ t : Y, y ∈ t.1 +ᵥ verticalSlice K r := by
        filter_upwards [ht.2.2.2.2] with y hy
        exact hy.mp (Set.mem_univ y)
      have hcovShift := (quasiMeasurePreserving_add_left volume (-a)).ae hcov
      filter_upwards [hcov, hcovShift] with y hy hyshift
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change (-((a : ℂ) * Complex.I) +
          ((x : ℂ) + (y : ℂ) * Complex.I) ∈ openUnion K C) ↔ _
      have hx : x = c + r := by simp [r]
      rw [show -((a : ℂ) * Complex.I) + ((x : ℂ) + (y : ℂ) * Complex.I) =
          (x : ℂ) + ((y - a : ℝ) : ℂ) * Complex.I by
        apply Complex.ext <;> simp
        ring]
      constructor
      · intro _
        rw [hx]
        exact (mem_openUnion_column_iff K c r y Y).2 hy
      · intro _
        rw [hx]
        apply (mem_openUnion_column_iff K c r (y - a) Y).2
        simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using hyshift
    · filter_upwards [] with y
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change (-((a : ℂ) * Complex.I) +
          ((x : ℂ) + (y : ℂ) * Complex.I) ∈ openUnion K C) ↔ _
      have hx : x = c + r := by simp [r]
      rw [show -((a : ℂ) * Complex.I) + ((x : ℂ) + (y : ℂ) * Complex.I) =
          (x : ℂ) + ((y - a : ℝ) : ℂ) * Complex.I by
        apply Complex.ext <;> simp
        ring]
      rw [hx, mem_openUnion_column_iff K c r (y - a) Y,
        mem_openUnion_column_iff K c r y Y]
      simp [not_nonempty_iff_eq_empty.mp hB]
  have hmeas : MeasurableSet {p : ℝ × ℝ |
      (((p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈ ((a : ℂ) * Complex.I) +ᵥ openUnion K C) ↔
        ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈ openUnion K C))} := by
    let f : ℝ × ℝ → Tiling.Plane := fun p ↦
      (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
    have hf : Measurable f := by fun_prop
    apply MeasurableSet.iff
    · exact (((isOpen_iUnion fun q : C ↦
          K.openCarrier_regularOpen.1.vadd q.1).vadd _).measurableSet.preimage hf)
    · exact ((isOpen_iUnion fun q : C ↦
          K.openCarrier_regularOpen.1.vadd q.1).measurableSet.preimage hf)
  have hprod := (MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas).2 hiter
  have hpull := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hprod
  filter_upwards [hpull] with z hz
  change (z ∈ ((a : ℂ) * Complex.I) +ᵥ openUnion K C) = (z ∈ openUnion K C)
  have heq : ((Complex.measurableEquivRealProd z).1 : ℂ) +
      ((Complex.measurableEquivRealProd z).2 : ℂ) * Complex.I = z := by
    apply Complex.ext <;> simp
  rw [heq] at hz
  exact propext hz

private theorem completeColumn_of_genericSliceTilings :
    ∀ {K : Region} {c : ℝ} {Y : Set ℝ}, Y.Nonempty →
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements
          {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) →
      (∀ r : ℝ, r ∉ K.vertexFinset.image Complex.re →
        (verticalSlice K r).Nonempty → LineTiles (verticalSlice K r) Y) →
      IsCenterColumn Axis.vertical K
        {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
  intro K c Y hY hpacking htiles
  let C : Set Tiling.Plane := {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}
  have hcount : Y.Countable := column_centres_countable hpacking
  refine ⟨hpacking, ?_, ⟨c, ?_⟩, ?_⟩
  · obtain ⟨y, hy⟩ := hY
    exact ⟨(c : ℂ) + (y : ℂ) * Complex.I, by simp [hy]⟩
  · intro z hz
    exact hz.1
  · intro a
    let v : Tiling.Plane := (a : ℂ) * Complex.I
    have hraw : v +ᵥ openUnion K C =ᵐ[volume] openUnion K C :=
      openUnion_column_vertical_vadd_ae hcount htiles
    have hUR : openUnion K C =ᵐ[volume] regularSupport K C :=
      Tiling.AxisParallel.openUnion_aeEq_regularSupport hpacking
    have hshift :=
      (quasiMeasurePreserving_add_left volume (-v)).vadd_ae_eq_of_ae_eq v hUR
    have hae : v +ᵥ regularSupport K C =ᵐ[volume] regularSupport K C :=
      hshift.symm.trans (hraw.trans hUR)
    have hopenL : IsOpen (v +ᵥ regularSupport K C) :=
      (Tiling.AxisParallel.regularSupport_isRegularOpen K C).1.vadd v
    have hregL : interior (closure (v +ᵥ regularSupport K C)) =
        v +ᵥ regularSupport K C := by
      rw [closure_vadd, interior_vadd,
        (Tiling.AxisParallel.regularSupport_isRegularOpen K C).2]
    have heq := Tiling.AxisParallel.regularOpen_eq_of_aeEq hopenL hregL
      (Tiling.AxisParallel.regularSupport_isRegularOpen K C).1
      (Tiling.AxisParallel.regularSupport_isRegularOpen K C).2 hae
    simpa only [v, C] using heq

private theorem centerColumn_iff_genericSlices_proof :
    ∀ {K : Region} {C : Set Tiling.Plane} {c : ℝ} {Y : Set ℝ},
      C = {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} → Y.Nonempty →
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements C) →
      (IsCenterColumn Axis.vertical K C ↔
        ∀ r : ℝ, r ∉ K.vertexFinset.image Complex.re →
          (verticalSlice K r).Nonempty → LineTiles (verticalSlice K r) Y) := by
  intro K C c Y hC hY hpacking
  subst C
  constructor
  · exact genericSliceTilings_of_completeColumn hY
  · exact completeColumn_of_genericSliceTilings hY hpacking

theorem finiteIntervalRegion_measurable_bounded
    {B : Set ℝ} (hB : IsFiniteIntervalRegion B) :
    IsOpen B ∧ MeasurableSet B ∧ Bornology.IsBounded B := by
  rcases hB with ⟨n, left, right, _hlt, rfl⟩
  have hopen : IsOpen (⋃ i, Set.Ioo (left i) (right i)) :=
    isOpen_iUnion fun _ ↦ isOpen_Ioo
  exact ⟨hopen, hopen.measurableSet,
    Bornology.isBounded_iUnion.mpr fun i ↦ Metric.isBounded_Ioo (left i) (right i)⟩

theorem finiteIntervalRegion_volume_toReal_pos
    {B : Set ℝ} (hB : IsFiniteIntervalRegion B) (hBne : B.Nonempty) :
    0 < (volume B).toReal := by
  obtain ⟨hBopen, _hBmeas, hBbounded⟩ := finiteIntervalRegion_measurable_bounded hB
  apply ENNReal.toReal_pos
  · exact hBopen.measure_ne_zero volume hBne
  · exact hBbounded.measure_lt_top.ne

private theorem centerColumn_literal_reconstruction
    {K : Region} {C : Set Tiling.Plane}
    (hC : IsCenterColumn Axis.vertical K C) :
    ∃ (c : ℝ) (Y : Set ℝ), Y.Nonempty ∧
      C = {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
  obtain ⟨c, hc⟩ := hC.2.2.1
  let Y : Set ℝ := {y : ℝ | (c : ℂ) + (y : ℂ) * Complex.I ∈ C}
  have hCY : C = {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
    ext z
    constructor
    · intro hz
      have hzre : z.re = c := by
        simpa [Axis.transverseCoord] using hc z hz
      refine ⟨hzre, ?_⟩
      change (c : ℂ) + (z.im : ℂ) * Complex.I ∈ C
      convert hz using 1
      apply Complex.ext <;> simp [hzre]
    · rintro ⟨hzre, hzim⟩
      change (c : ℂ) + (z.im : ℂ) * Complex.I ∈ C at hzim
      convert hzim using 1
      apply Complex.ext <;> simp [hzre]
  have hY : Y.Nonempty := by
    obtain ⟨z, hz⟩ := hC.2.1
    exact ⟨z.im, hCY.subset hz |>.2⟩
  exact ⟨c, Y, hY, hCY⟩

private theorem genericSlice_exists_positivePeriod :
    ∀ {K : Region} {C : Set Tiling.Plane},
      IsCenterColumn Axis.vertical K C →
      ∀ {r : ℝ}, r ∉ K.vertexFinset.image Complex.re →
        (verticalSlice K r).Nonempty →
        ∃ (Y : Set ℝ) (p : ℝ), 0 < p ∧ p +ᵥ Y = Y ∧
          LineTiles (verticalSlice K r) Y ∧
          ∀ s : ℝ, s ∉ K.vertexFinset.image Complex.re →
            (verticalSlice K s).Nonempty → LineTiles (verticalSlice K s) Y := by
  intro K C hC r hr hBr
  obtain ⟨c, Y, hY, hCY⟩ := centerColumn_literal_reconstruction hC
  have hall := genericSliceTilings_of_completeColumn hY (hCY ▸ hC)
  have htile := hall r hr hBr
  have hBfinite := verticalSlice_finiteIntervals_proof K hr |>.1
  have hBpos := finiteIntervalRegion_volume_toReal_pos hBfinite hBr
  obtain ⟨p, hp, hperiod⟩ := exists_positiveLinePeriod hBfinite hBpos htile
  exact ⟨Y, p, hp, hperiod, htile, hall⟩

private theorem centerColumn_genericSlice_measure_eq_proof :
    ∀ {K : Region} {C : Set Tiling.Plane},
      IsCenterColumn Axis.vertical K C →
      ∀ {r s : ℝ}, r ∉ K.vertexFinset.image Complex.re →
        s ∉ K.vertexFinset.image Complex.re →
        (verticalSlice K r).Nonempty → (verticalSlice K s).Nonempty →
        (volume (verticalSlice K r)).toReal =
          (volume (verticalSlice K s)).toReal := by
  intro K C hC r s hr hs hBr hBs
  obtain ⟨c, Y, hY, hCY⟩ := centerColumn_literal_reconstruction hC
  have hall := genericSliceTilings_of_completeColumn hY (hCY ▸ hC)
  have htr := hall r hr hBr
  have hts := hall s hs hBs
  have hfr := verticalSlice_finiteIntervals_proof K hr |>.1
  have hfs := verticalSlice_finiteIntervals_proof K hs |>.1
  have hpr := finiteIntervalRegion_volume_toReal_pos hfr hBr
  have hps := finiteIntervalRegion_volume_toReal_pos hfs hBs
  obtain ⟨p, hp, hperiod⟩ := exists_positiveLinePeriod hfr hpr htr
  have hmr := Tiling.AxisParallel.Foundations.linePeriod_mass
    (finiteIntervalRegion_measurable_bounded hfr).2.2 hpr htr hp hperiod
  have hms := Tiling.AxisParallel.Foundations.linePeriod_mass
    (finiteIntervalRegion_measurable_bounded hfs).2.2 hps hts hp hperiod
  have hnpos : 0 < (Set.ncard (Y ∩ Set.Ico 0 p) : ℝ) := by
    exact_mod_cast (Set.ncard_pos hmr.1).mpr hmr.2.1
  nlinarith [hmr.2.2, hms.2.2]

private theorem finite_inter_bounded_of_separated
    {S Q : Set ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hS : S.Pairwise fun x y ↦ delta ≤ dist x y)
    (hQ : Bornology.IsBounded Q) : (S ∩ Q).Finite := by
  have hSclosed : IsClosed S := Metric.isClosed_of_pairwise_le_dist hdelta hS
  have hSdiscrete : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro s hs
    refine ⟨Metric.ball s delta, Metric.isOpen_ball, ?_⟩
    ext t
    constructor
    · rintro ⟨htball, htS⟩
      by_cases hts : t = s
      · simp [hts]
      · simp only [Metric.mem_ball] at htball
        exact False.elim ((not_lt_of_ge (by simpa [dist_comm] using hS htS hs hts)) htball)
    · rintro rfl
      exact ⟨Metric.mem_ball_self hdelta, hs⟩
  obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : ℝ)
  have hcompact : IsCompact (S ∩ Metric.closedBall 0 R) :=
    Metric.isCompact_of_isClosed_isBounded
      (hSclosed.inter Metric.isClosed_closedBall)
      (Metric.isBounded_closedBall.subset inter_subset_right)
  exact (hcompact.finite (hSdiscrete.mono inter_subset_left)).subset
    (inter_subset_inter_right S hR)

private theorem periodicPacking_residues_finite :
    ∀ {B' Y : Set ℝ} {p : ℝ}, IsFiniteIntervalRegion B' →
      0 < (volume B').toReal → 0 < p →
      p +ᵥ Y = Y →
      Set.Pairwise Y (MeasureTheory.AEDisjoint volume on ((· +ᵥ B') : ℝ → Set ℝ)) →
      (Y ∩ Set.Ico 0 p).Finite := by
  intro B' Y p hB hBpos hp _hperiod hpack
  obtain ⟨a, _b, eta, _etaR, _hab, heta, _hetaR, _hbound, hcollar, _⟩ :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.IsFiniteIntervalRegion.extremeCollars
      hB hBpos
  have hsep : Y.Pairwise fun y z ↦ eta ≤ dist y z := by
    intro y hy z hz hyz
    by_contra hlt
    have hyzdist : dist y z < eta := lt_of_not_ge hlt
    let lo := max (y + a) (z + a)
    let hi := min (y + a + eta) (z + a + eta)
    have hlohi : lo < hi := by
      simp only [lo, hi, max_lt_iff, lt_min_iff]
      rw [Real.dist_eq] at hyzdist
      have habs := abs_lt.mp hyzdist
      constructor <;> constructor <;> linarith [habs.1, habs.2]
    have hsub : Set.Ioo lo hi ⊆ (y +ᵥ B') ∩ (z +ᵥ B') := by
      intro x hx
      simp only [Set.mem_inter_iff, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
      apply And.intro <;> apply hcollar <;> simp only [Set.mem_Ioo] at hx ⊢
      · constructor <;> linarith [le_max_left (y + a) (z + a), min_le_left
          (y + a + eta) (z + a + eta)]
      · constructor <;> linarith [le_max_right (y + a) (z + a), min_le_right
          (y + a + eta) (z + a + eta)]
    have hpos : 0 < volume ((y +ᵥ B') ∩ (z +ᵥ B')) :=
      lt_of_lt_of_le (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hlohi))
        (measure_mono hsub)
    exact hpos.ne' (hpack hy hz hyz)
  exact finite_inter_bounded_of_separated heta hsep (Metric.isBounded_Ico 0 p)

private theorem periodicPacking_cellIntegral :
    ∀ {B' Y : Set ℝ} {p : ℝ}, IsFiniteIntervalRegion B' → 0 < p →
      p +ᵥ Y = Y → (Y ∩ Set.Ico 0 p).Finite →
      ∫⁻ x in Set.Ico 0 p, lineMultiplicity B' Y x ∂volume =
        Set.ncard (Y ∩ Set.Ico 0 p) * volume B' := by
  intro B' Y p hB hp hperiod hfinite
  simpa only [lineMultiplicity] using
    (periodicMultiplicity_cellIntegral
      (finiteIntervalRegion_measurable_bounded hB).2.1 hp hperiod hfinite)

private theorem lineTiles_multiplicity_eq_one
    {B Y : Set ℝ} (hTile : LineTiles B Y) :
    ∀ᵐ x ∂volume, lineMultiplicity B Y x = 1 := by
  let _ : Countable Y := hTile.2.2.1
  have hover : ∀ᵐ x ∂volume, ∀ y z : Y, y ≠ z →
      ¬ (x ∈ y.1 +ᵥ B ∧ x ∈ z.1 +ᵥ B) := by
    apply ae_all_iff.mpr
    intro y
    apply ae_all_iff.mpr
    intro z
    by_cases hyz : y = z
    · filter_upwards [] with x
      simp [hyz]
    · have hz := hTile.2.2.2.1 y.2 z.2 (fun h ↦ hyz (Subtype.ext h))
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx
      intro _
      simpa only [Set.mem_inter_iff, not_and] using hx
  filter_upwards [hTile.2.2.2.2, hover] with x hcover hdisj
  obtain ⟨y, hy⟩ := hcover.mp (Set.mem_univ x)
  rw [lineMultiplicity, tsum_eq_single y]
  · simp [hy]
  · intro z hzy
    have hz : x ∉ z.1 +ᵥ B := fun hz ↦ hdisj y z (Ne.symm hzy) ⟨hy, hz⟩
    simp [hz]

private theorem lineMultiplicity_aemeasurable
    {B Y : Set ℝ} (hB : MeasurableSet B) (hY : Y.Countable) :
    AEMeasurable (lineMultiplicity B Y) volume := by
  let _ : Countable Y := hY.to_subtype
  apply AEMeasurable.tsum
  intro y
  apply AEMeasurable.indicator aemeasurable_const
  have hm := hB.preimage
    (show Measurable (fun x : ℝ ↦ x - y.1) from measurable_id.sub measurable_const)
  have heq : y.1 +ᵥ B = (fun x : ℝ ↦ x - y.1) ⁻¹' B := by
    ext x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change (-y.1 + x ∈ B) ↔ (x - y.1 ∈ B)
    ring_nf
  rw [heq]
  exact hm

private theorem lineMultiplicity_add_period
    {B Y : Set ℝ} {q : ℝ} (hq : q +ᵥ Y = Y) (x : ℝ) :
    lineMultiplicity B Y (x + q) = lineMultiplicity B Y x := by
  have hn : (-q) +ᵥ Y = Y := (periodGroup Y).neg_mem hq
  let e : Y ≃ Y := {
    toFun := fun y ↦ ⟨q + y.1, by
      have : q + y.1 ∈ q +ᵥ Y := ⟨y.1, y.2, rfl⟩
      rwa [hq] at this⟩
    invFun := fun y ↦ ⟨-q + y.1, by
      have : -q + y.1 ∈ (-q) +ᵥ Y := ⟨y.1, y.2, rfl⟩
      rwa [hn] at this⟩
    left_inv := by intro y; apply Subtype.ext; simp
    right_inv := by intro y; apply Subtype.ext; simp }
  rw [lineMultiplicity, lineMultiplicity, ← e.tsum_eq]
  apply tsum_congr
  intro y
  change ((q + y.1) +ᵥ B).indicator (1 : ℝ → ENNReal) (x + q) =
    (y.1 +ᵥ B).indicator (1 : ℝ → ENNReal) x
  by_cases hy : x ∈ y.1 +ᵥ B
  · have hy' : x + q ∈ (q + y.1) +ᵥ B := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy ⊢
      convert hy using 1
      simp only [vadd_eq_add]
      ring_nf
    simp [hy, hy']
  · have hy' : x + q ∉ (q + y.1) +ᵥ B := by
      intro h
      apply hy
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at h ⊢
      convert h using 1
      simp only [vadd_eq_add]
      ring_nf
    simp [hy, hy']

private theorem periodicPacking_tiles_of_measure_eq_proof :
    ∀ {B B' Y : Set ℝ} {p : ℝ},
      IsFiniteIntervalRegion B → IsFiniteIntervalRegion B' →
      LineTiles B Y → 0 < p → p +ᵥ Y = Y →
      Set.Pairwise Y (MeasureTheory.AEDisjoint volume on ((· +ᵥ B') : ℝ → Set ℝ)) →
      (volume B').toReal = (volume B).toReal → LineTiles B' Y := by
  intro B B' Y p hB hB' hTile hp hperiod hpack hmass
  obtain ⟨hBopen, hBmeas, hBbounded⟩ := finiteIntervalRegion_measurable_bounded hB
  obtain ⟨hB'open, hB'meas, hB'bounded⟩ := finiteIntervalRegion_measurable_bounded hB'
  have hBpos : 0 < (volume B).toReal := by
    have hBne : B.Nonempty := by
      obtain ⟨x, hx⟩ := hTile.2.2.2.2.exists
      obtain ⟨y, hy⟩ := (hx.mp (Set.mem_univ x))
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
      exact ⟨_, hy⟩
    exact finiteIntervalRegion_volume_toReal_pos hB hBne
  have hB'pos : 0 < (volume B').toReal := hmass.symm ▸ hBpos
  have hFmass := Tiling.AxisParallel.Foundations.linePeriod_mass
    hBbounded hBpos hTile hp hperiod
  have hF : (Y ∩ Set.Ico 0 p).Finite :=
    periodicPacking_residues_finite hB' hB'pos hp hperiod hpack
  have hcellB := periodicPacking_cellIntegral hB hp hperiod hFmass.1
  have hcellB' := periodicPacking_cellIntegral hB' hp hperiod hF
  have hvol : volume B' = volume B := by
    apply (ENNReal.toReal_eq_toReal_iff' hB'bounded.measure_lt_top.ne
      hBbounded.measure_lt_top.ne).mp
    exact hmass
  have hintegral :
      (∫⁻ x in Set.Ico 0 p, lineMultiplicity B' Y x ∂volume) =
        ∫⁻ x in Set.Ico 0 p, (1 : ENNReal) ∂volume := by
    rw [hcellB', hvol, ← hcellB]
    apply setLIntegral_congr_fun_ae measurableSet_Ico
    filter_upwards [lineTiles_multiplicity_eq_one hTile] with x hx
    intro _
    exact hx
  have hle := periodicPacking_multiplicity_le_one hpack hTile.2.2.1
  have hleCell : lineMultiplicity B' Y ≤ᵐ[volume.restrict (Set.Ico 0 p)] 1 :=
    ae_restrict_of_ae hle
  have hmAE := lineMultiplicity_aemeasurable hB'meas hTile.2.2.1
  have hfiniteIntegral :
      (∫⁻ x, lineMultiplicity B' Y x ∂volume.restrict (Set.Ico 0 p)) ≠ ⊤ := by
    rw [hintegral, MeasureTheory.setLIntegral_one]
    exact (Metric.isBounded_Ico 0 p).measure_lt_top.ne
  have hcellOne : lineMultiplicity B' Y =ᵐ[volume.restrict (Set.Ico 0 p)] 1 :=
    ae_eq_of_ae_le_of_lintegral_le hleCell hfiniteIntegral
      aemeasurable_const hintegral.ge
  have hbase : ∀ᵐ x ∂volume,
      x ∈ Set.Ico 0 p → lineMultiplicity B' Y x = 1 :=
    (ae_restrict_iff' measurableSet_Ico).mp hcellOne
  have hallCells : ∀ᵐ x ∂volume, ∀ n : ℤ,
      x ∈ ((n : ℝ) * p) +ᵥ Set.Ico 0 p → lineMultiplicity B' Y x = 1 := by
    apply ae_all_iff.mpr
    intro n
    let q : ℝ := (n : ℝ) * p
    have hq : ((n : ℝ) * p) +ᵥ Y = Y := by
      simpa only [periodGroup_isAddSubgroup, zsmul_eq_mul] using
        (periodGroup Y).zsmul_mem hperiod n
    have htranslated := (quasiMeasurePreserving_add_left volume (-q)).ae hbase
    filter_upwards [htranslated] with x hx
    intro hxcell
    have hx0 : -q + x ∈ Set.Ico 0 p := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxcell
      exact hxcell
    have hm := hx hx0
    rw [← hm]
    have hh := lineMultiplicity_add_period (B := B') hq (-q + x)
    have heq : -q + x + q = x := by ring
    rw [heq] at hh
    exact hh
  have hglobal : ∀ᵐ x ∂volume, lineMultiplicity B' Y x = 1 := by
    filter_upwards [hallCells] with x hx
    let n : ℤ := Int.floor (x / p)
    apply hx n
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_Ico]
    have hlo := Int.floor_le (x / p)
    have hhi := Int.lt_floor_add_one (x / p)
    have hlo' := (le_div_iff₀ hp).mp hlo
    have hhi' := (div_lt_iff₀ hp).mp hhi
    dsimp [n]
    constructor <;> linarith
  refine ⟨hB'meas, MeasurableSet.univ, hTile.2.2.1, hpack, ?_⟩
  filter_upwards [hglobal] with x hx
  simp only [Set.mem_univ, true_iff]
  by_contra hnone
  have hz : lineMultiplicity B' Y x = 0 := by
    rw [lineMultiplicity]
    have hf : (fun y : Y ↦ (y.1 +ᵥ B').indicator (1 : ℝ → ENNReal) x) = 0 := by
      funext y
      simp only [Set.indicator, Pi.one_apply]
      split_ifs with hy
      · exact False.elim (hnone ⟨y, hy⟩)
      · rfl
    rw [hf]
    simp
  rw [hz] at hx
  exact zero_ne_one hx


end Tiling.AxisParallel.OneDimensional.ColumnSlices

namespace Tiling.AxisParallel.Region

/-- A generic vertical slice of an axis-parallel region is a finite union of intervals and is
locally constant away from intrinsic vertex levels. -/
theorem verticalSlice_finiteIntervals
    (K : Region) {r : ℝ} (hr : r ∉ K.vertexFinset.image Complex.re) :
    OneDimensional.IsFiniteIntervalRegion
        (OneDimensional.ColumnSlices.verticalSlice K r) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - r| < ε →
        OneDimensional.ColumnSlices.verticalSlice K s =
          OneDimensional.ColumnSlices.verticalSlice K r :=
  OneDimensional.ColumnSlices.verticalSlice_finiteIntervals_proof K hr

end Tiling.AxisParallel.Region

namespace Tiling.AxisParallel.Foundations

/-- A vertical centre column is equivalent to tiling every nonempty generic slice. -/
theorem centerColumn_iff_genericSlices :
    ∀ {K : Region} {C : Set Tiling.Plane} {c : ℝ} {Y : Set ℝ},
      C = {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} → Y.Nonempty →
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements C) →
      (IsCenterColumn Axis.vertical K C ↔
        ∀ r : ℝ, r ∉ K.vertexFinset.image Complex.re →
          (OneDimensional.ColumnSlices.verticalSlice K r).Nonempty →
            OneDimensional.LineTiles
              (OneDimensional.ColumnSlices.verticalSlice K r) Y) :=
  OneDimensional.ColumnSlices.centerColumn_iff_genericSlices_proof

/-- Generic slices through one complete centre column have equal one-dimensional measure. -/
theorem centerColumn_genericSlice_measure_eq :
    ∀ {K : Region} {C : Set Tiling.Plane},
      IsCenterColumn Axis.vertical K C →
      ∀ {r s : ℝ}, r ∉ K.vertexFinset.image Complex.re →
        s ∉ K.vertexFinset.image Complex.re →
        (OneDimensional.ColumnSlices.verticalSlice K r).Nonempty →
        (OneDimensional.ColumnSlices.verticalSlice K s).Nonempty →
        (volume (OneDimensional.ColumnSlices.verticalSlice K r)).toReal =
          (volume (OneDimensional.ColumnSlices.verticalSlice K s)).toReal :=
  OneDimensional.ColumnSlices.centerColumn_genericSlice_measure_eq_proof

/-- A periodic packing by a finite-interval region of the correct mass is a line tiling. -/
theorem periodicPacking_tiles_of_measure_eq :
    ∀ {B B' Y : Set ℝ} {p : ℝ},
      OneDimensional.IsFiniteIntervalRegion B →
      OneDimensional.IsFiniteIntervalRegion B' →
      OneDimensional.LineTiles B Y → 0 < p → p +ᵥ Y = Y →
      Set.Pairwise Y
        (MeasureTheory.AEDisjoint volume on ((· +ᵥ B') : ℝ → Set ℝ)) →
      (volume B').toReal = (volume B).toReal →
      OneDimensional.LineTiles B' Y :=
  OneDimensional.ColumnSlices.periodicPacking_tiles_of_measure_eq_proof

end Tiling.AxisParallel.Foundations
