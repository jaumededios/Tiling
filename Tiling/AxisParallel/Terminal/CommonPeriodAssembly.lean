import Tiling.AxisParallel.Terminal.AssemblyCore
import Tiling.AxisParallel.Terminal.CommonPeriodAssembly.DisjointLinePeriods
import Tiling.AxisParallel.Terminal.CommonPeriodAssembly.TorusArea
import Tiling.AxisParallel.Terminal.CommonPeriodAssembly.VerticalSlabNormalForm
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Period groups of vertical slabs and common-period assembly

The lower modules prove the analytic period-group and torus-area results. This facade retains
the free-shear construction and assembles a common lattice from `CommonPeriodAssemblyData`,
including empty and unmixed cases. Constructing that input datum from an arbitrary manuscript
tiling belongs to the upstream geometric development, not to this assembly theorem.
-/

open Function MeasureTheory Set
open scoped Pointwise

namespace Tiling.AxisParallel.Terminal

private theorem exists_positive_common_multiple
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hcomm : ∃ q : ℚ, y = (q : ℝ) * x) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * x = (n : ℝ) * y := by
  obtain ⟨q, rfl⟩ := hcomm
  have hqreal : 0 < (q : ℝ) := (mul_pos_iff_of_pos_right hx).mp hy
  have hq : 0 < q := Rat.cast_pos.mp hqreal
  let m : ℕ := q.num.natAbs
  let n : ℕ := q.den
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have hm : 0 < m := by
    simpa only [m, Int.natAbs_pos] using hnum.ne'
  have hn : 0 < n := q.pos
  refine ⟨m, n, hm, hn, ?_⟩
  dsimp only [m, n]
  have hcast : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    simp only [Nat.cast_natAbs, Int.cast_abs,
      abs_of_pos (Int.cast_pos.mpr hnum)]
  rw [hcast, Rat.cast_def]
  field_simp

/-- The triangular subgroup packaged by its evident rank-two real basis. -/
private noncomputable def triangularPlanarLattice
    (alpha beta shear : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    Tiling.AxisParallel.PlanarLattice where
  basis := ![verticalPeriodVector alpha, skewPeriodVector beta shear]
  independent := by
    rw [LinearIndependent.pair_iffₛ]
    intro s t s' t' h
    have hre := congrArg Complex.re h
    have ht : t = t' := by
      norm_num [verticalPeriodVector, skewPeriodVector] at hre
      exact hre.resolve_right hbeta.ne'
    subst t'
    have him := congrArg Complex.im h
    have hs : s = s' := by
      norm_num [verticalPeriodVector, skewPeriodVector] at him
      exact him.resolve_right halpha.ne'
    exact ⟨hs, rfl⟩

private theorem triangularPlanarLattice_toAddSubgroup
    (alpha beta shear : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (triangularPlanarLattice alpha beta shear halpha hbeta).toAddSubgroup =
      triangularPeriodSubgroup alpha beta shear := by
  apply le_antisymm
  · rw [Tiling.AxisParallel.PlanarLattice.toAddSubgroup,
      Tiling.Polygonal.PlanarLattice.toAddSubgroup, AddSubgroup.closure_le]
    rintro x ⟨i, rfl⟩
    change ![verticalPeriodVector alpha, skewPeriodVector beta shear] i ∈
      triangularPeriodSubgroup alpha beta shear
    fin_cases i
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · intro x hx
    rcases hx with ⟨m, n, rfl⟩
    apply add_mem
    · apply AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) m
      exact ⟨0, by simp [triangularPlanarLattice]⟩
    · apply AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) n
      exact ⟨1, by simp [triangularPlanarLattice]⟩

theorem triangularPeriodSubgroup_mem_iff
    {alpha beta shear : ℝ} {v : Tiling.Plane} :
    v ∈ triangularPeriodSubgroup alpha beta shear ↔
      ∃ m n : ℤ,
        v = m • verticalPeriodVector alpha +
          n • skewPeriodVector beta shear :=
  Iff.rfl

theorem exists_freeShear_commonSublattice
    {Lambda : Tiling.AxisParallel.PlanarLattice}
    (F : VerticalSlabLatticeForm Lambda)
    {alphaColumn betaColumn : ℝ}
    (halphaColumn : 0 < alphaColumn) (hbetaColumn : 0 < betaColumn)
    (hvertical : ∃ q : ℚ,
      alphaColumn = (q : ℝ) * F.verticalPeriod)
    (hhorizontal : ∃ q : ℚ,
      betaColumn = (q : ℝ) * F.horizontalPeriod) :
    ∃ (shear : ℝ) (common : Tiling.AxisParallel.PlanarLattice),
      0 < shear ∧
      common.toAddSubgroup ≤ Lambda.toAddSubgroup ∧
      common.toAddSubgroup ≤
        triangularPeriodSubgroup alphaColumn betaColumn shear := by
  obtain ⟨mv, nv, hmv, hnv, hvcommon⟩ :=
    exists_positive_common_multiple F.verticalPeriod_pos halphaColumn hvertical
  obtain ⟨mh, nh, hmh, hnh, hhcommon⟩ :=
    exists_positive_common_multiple F.horizontalPeriod_pos hbetaColumn hhorizontal
  obtain ⟨j : ℕ, hj⟩ :=
    exists_nat_gt (-((mh : ℝ) * F.shear) / F.verticalPeriod)
  have hnumerator :
      0 < (mh : ℝ) * F.shear + (j : ℝ) * F.verticalPeriod := by
    have hmul := mul_lt_mul_of_pos_right hj F.verticalPeriod_pos
    rw [div_mul_cancel₀ _ F.verticalPeriod_pos.ne'] at hmul
    nlinarith
  let shear : ℝ :=
    ((mh : ℝ) * F.shear + (j : ℝ) * F.verticalPeriod) / (nh : ℝ)
  have hshear : 0 < shear :=
    div_pos hnumerator (Nat.cast_pos.mpr hnh)
  have hcommonVertical : 0 < (mv : ℝ) * F.verticalPeriod :=
    mul_pos (Nat.cast_pos.mpr hmv) F.verticalPeriod_pos
  have hcommonHorizontal : 0 < (mh : ℝ) * F.horizontalPeriod :=
    mul_pos (Nat.cast_pos.mpr hmh) F.horizontalPeriod_pos
  let common := triangularPlanarLattice
    ((mv : ℝ) * F.verticalPeriod)
    ((mh : ℝ) * F.horizontalPeriod)
    ((mh : ℝ) * F.shear + (j : ℝ) * F.verticalPeriod)
    hcommonVertical hcommonHorizontal
  refine ⟨shear, common, hshear, ?_, ?_⟩
  · rw [show common.toAddSubgroup =
        triangularPeriodSubgroup
          ((mv : ℝ) * F.verticalPeriod)
          ((mh : ℝ) * F.horizontalPeriod)
          ((mh : ℝ) * F.shear + (j : ℝ) * F.verticalPeriod) by
      exact triangularPlanarLattice_toAddSubgroup _ _ _ _ _]
    have hV : verticalPeriodVector ((mv : ℝ) * F.verticalPeriod) ∈
        Lambda.toAddSubgroup := by
      rw [F.subgroup_eq]
      have heq : verticalPeriodVector ((mv : ℝ) * F.verticalPeriod) =
          (mv : ℤ) • verticalPeriodVector F.verticalPeriod := by
        apply Complex.ext <;> norm_num [verticalPeriodVector]
      rw [heq]
      exact AddSubgroup.zsmul_mem _
        (show verticalPeriodVector F.verticalPeriod ∈
          triangularPeriodSubgroup F.verticalPeriod F.horizontalPeriod F.shear from
          ⟨1, 0, by simp⟩) (mv : ℤ)
    have hH : skewPeriodVector
        ((mh : ℝ) * F.horizontalPeriod)
        ((mh : ℝ) * F.shear + (j : ℝ) * F.verticalPeriod) ∈
        Lambda.toAddSubgroup := by
      rw [F.subgroup_eq]
      have hvbase : verticalPeriodVector F.verticalPeriod ∈
          triangularPeriodSubgroup F.verticalPeriod F.horizontalPeriod F.shear :=
        ⟨1, 0, by simp⟩
      have hhbase : skewPeriodVector F.horizontalPeriod F.shear ∈
          triangularPeriodSubgroup F.verticalPeriod F.horizontalPeriod F.shear :=
        ⟨0, 1, by simp⟩
      have heq : skewPeriodVector
          ((mh : ℝ) * F.horizontalPeriod)
          ((mh : ℝ) * F.shear + (j : ℝ) * F.verticalPeriod) =
          (mh : ℤ) • skewPeriodVector F.horizontalPeriod F.shear +
            (j : ℤ) • verticalPeriodVector F.verticalPeriod := by
        apply Complex.ext <;> norm_num [verticalPeriodVector, skewPeriodVector]
      rw [heq]
      exact AddSubgroup.add_mem _
        (AddSubgroup.zsmul_mem _ hhbase (mh : ℤ))
        (AddSubgroup.zsmul_mem _ hvbase (j : ℤ))
    rintro x ⟨p, q, rfl⟩
    exact AddSubgroup.add_mem _
      (AddSubgroup.zsmul_mem _ hV p) (AddSubgroup.zsmul_mem _ hH q)
  · rw [show common.toAddSubgroup =
        triangularPeriodSubgroup
          ((mv : ℝ) * F.verticalPeriod)
          ((mh : ℝ) * F.horizontalPeriod)
          ((mh : ℝ) * F.shear + (j : ℝ) * F.verticalPeriod) by
      exact triangularPlanarLattice_toAddSubgroup _ _ _ _ _]
    have hV : verticalPeriodVector ((mv : ℝ) * F.verticalPeriod) ∈
        triangularPeriodSubgroup alphaColumn betaColumn shear := by
      have hveq : verticalPeriodVector ((mv : ℝ) * F.verticalPeriod) =
          (nv : ℤ) • verticalPeriodVector alphaColumn := by
        apply Complex.ext
        · norm_num [verticalPeriodVector]
        · norm_num [verticalPeriodVector] at hvcommon ⊢
          exact hvcommon
      rw [hveq]
      exact AddSubgroup.zsmul_mem _
        (show verticalPeriodVector alphaColumn ∈
          triangularPeriodSubgroup alphaColumn betaColumn shear from
          ⟨1, 0, by simp⟩) (nv : ℤ)
    have hH : skewPeriodVector
        ((mh : ℝ) * F.horizontalPeriod)
        ((mh : ℝ) * F.shear + (j : ℝ) * F.verticalPeriod) ∈
        triangularPeriodSubgroup alphaColumn betaColumn shear := by
      have hheq : skewPeriodVector
          ((mh : ℝ) * F.horizontalPeriod)
          ((mh : ℝ) * F.shear + (j : ℝ) * F.verticalPeriod) =
          (nh : ℤ) • skewPeriodVector betaColumn shear := by
        have hshearEq : (nh : ℝ) * shear =
            (mh : ℝ) * F.shear + (j : ℝ) * F.verticalPeriod := by
          dsimp only [shear]
          field_simp
        apply Complex.ext
        · norm_num [skewPeriodVector] at hhcommon ⊢
          exact hhcommon
        · norm_num [skewPeriodVector] at hshearEq ⊢
          exact hshearEq.symm
      rw [hheq]
      exact AddSubgroup.zsmul_mem _
        (show skewPeriodVector betaColumn shear ∈
          triangularPeriodSubgroup alphaColumn betaColumn shear from
          ⟨0, 1, by simp⟩) (nh : ℤ)
    rintro x ⟨p, q, rfl⟩
    exact AddSubgroup.add_mem _
      (AddSubgroup.zsmul_mem _ hV p) (AddSubgroup.zsmul_mem _ hH q)

private theorem ae_comp_re {p : ℝ → Prop} (h : ∀ᵐ x ∂volume, p x) :
    ∀ᵐ z : Tiling.Plane ∂volume, p z.re := by
  have hp : ∀ᵐ z : ℝ × ℝ ∂volume, p z.1 :=
    Measure.quasiMeasurePreserving_fst.ae h
  have hc := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hp
  simpa only [Complex.measurableEquivRealProd_apply] using hc

private theorem ae_eq_cylinder {X Y : Set ℝ} (h : X =ᵐ[volume] Y) :
    {z : Tiling.Plane | z.re ∈ X} =ᵐ[volume] {z : Tiling.Plane | z.re ∈ Y} :=
  ae_comp_re h

theorem tilesOn_finite_iUnion_of_aePartition
    {n : ℕ} {K : Region} {S : Fin n → Set Tiling.Plane}
    {X : Fin n → Set ℝ} {Y : Set ℝ}
    (hTile : ∀ i, TilesOn K (S i) {z : Tiling.Plane | z.re ∈ X i})
    (hDisjoint : ∀ i j, i ≠ j → AEDisjoint volume (X i) (X j))
    (hCover : (⋃ i, X i) =ᵐ[volume] Y) :
    TilesOn K (⋃ i, S i) {z : Tiling.Plane | z.re ∈ Y} := by
  have hcount : (⋃ i, S i).Countable := Set.countable_iUnion fun i => (hTile i).1
  have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (⋃ i, S i)) := by
    rw [isPacking_iff_openCarrier_disjoint]
    intro s hs t ht hst
    rw [Set.mem_iUnion] at hs ht
    obtain ⟨i, hsi⟩ := hs
    obtain ⟨j, htj⟩ := ht
    by_cases hij : i = j
    · subst j
      exact (isPacking_iff_openCarrier_disjoint K (S i)).mp (hTile i).2.1 hsi htj hst
    · change Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.openCarrier)
      rw [Set.disjoint_left]
      intro x hxs hxt
      have haeBase : ∀ᵐ r ∂volume, r ∉ X i ∩ X j :=
        measure_eq_zero_iff_ae_notMem.mp (hDisjoint i j hij)
      have haeNot : ∀ᵐ z ∂volume,
          z ∉ (s +ᵥ K.openCarrier) ∩ (t +ᵥ K.openCarrier) := by
        filter_upwards [(hTile i).2.2, (hTile j).2.2,
          ae_comp_re haeBase]
          with z hxi hxj hd
        intro hz
        have hi : z.re ∈ X i := hxi.mpr ⟨⟨s, hsi⟩, hz.1⟩
        have hj : z.re ∈ X j := hxj.mpr ⟨⟨t, htj⟩, hz.2⟩
        exact hd ⟨hi, hj⟩
      have hzero : volume
          ((s +ᵥ K.openCarrier) ∩ (t +ᵥ K.openCarrier)) = 0 :=
        measure_eq_zero_iff_ae_notMem.mpr haeNot
      have hpos := ((isOpen_interior.vadd s).inter
        (isOpen_interior.vadd t)).measure_pos volume ⟨x, hxs, hxt⟩
      change 0 < volume ((s +ᵥ K.openCarrier) ∩ (t +ᵥ K.openCarrier)) at hpos
      rw [hzero] at hpos
      exact (lt_irrefl 0 hpos).elim
  refine ⟨hcount, hpacking, ?_⟩
  have hAll : ∀ᵐ x ∂volume, ∀ i, (x ∈ {z : Tiling.Plane | z.re ∈ X i} ↔
      ∃ s : S i, x ∈ (s : Tiling.Plane) +ᵥ K.openCarrier) :=
    ae_all_iff.mpr fun i => (hTile i).2.2
  filter_upwards [ae_eq_cylinder hCover, hAll] with x hxY hx
  constructor
  · intro hy
    have hu : x.re ∈ ⋃ i, X i := (iff_of_eq hxY.symm).mp hy
    rw [Set.mem_iUnion] at hu
    obtain ⟨i, hxi⟩ := hu
    obtain ⟨s, hs⟩ := (hx i).mp hxi
    exact ⟨⟨s, Set.mem_iUnion_of_mem i s.2⟩, hs⟩
  · rintro ⟨s, hs⟩
    obtain ⟨i, hsi⟩ := Set.mem_iUnion.mp s.2
    have hu : x.re ∈ ⋃ i, X i :=
      Set.mem_iUnion_of_mem i ((hx i).mpr ⟨⟨s.1, hsi⟩, hs⟩)
    exact (iff_of_eq hxY).mp hu

theorem iUnion_periodGroup_of_common_subgroup
    {ι : Type*} {S : ι → Set Tiling.Plane} {L : AddSubgroup Tiling.Plane}
    (h : ∀ i, L ≤ periodGroup (S i)) : L ≤ periodGroup (⋃ i, S i) := by
  intro v hv
  rw [periodGroup_isAddSubgroup]
  rw [Set.vadd_set_iUnion]
  congr 1
  funext i
  exact (periodGroup_isAddSubgroup (S i) v).mp (h i hv)

theorem rational_commensurable_symm
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∃ q : ℚ, a = (q : ℝ) * b) :
    ∃ q : ℚ, b = (q : ℝ) * a := by
  obtain ⟨q, rfl⟩ := h
  have hq : (q : ℝ) ≠ 0 := by
    intro hq
    simp [hq] at ha
  refine ⟨q⁻¹, ?_⟩
  push_cast
  field_simp

private theorem tilesOn_congr_cylinder_ae {K : Region} {S : Set Tiling.Plane}
    {X Y : Set ℝ} (h : TilesOn K S {z : Tiling.Plane | z.re ∈ X})
    (hXY : X =ᵐ[volume] Y) :
    TilesOn K S {z : Tiling.Plane | z.re ∈ Y} :=
  ⟨h.1, h.2.1, by
    filter_upwards [h.2.2, ae_eq_cylinder hXY] with z hz hzy
    exact (iff_of_eq hzy.symm).trans hz ⟩

private theorem triangular_periods
    {S : Set Tiling.Plane} {alpha beta shear : ℝ}
    (hv : verticalPeriodVector alpha ∈ periodGroup S)
    (hh : skewPeriodVector beta shear ∈ periodGroup S) :
    triangularPeriodSubgroup alpha beta shear ≤ periodGroup S := by
  rintro v ⟨m, n, rfl⟩
  exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ hv m)
    (AddSubgroup.zsmul_mem _ hh n)

private theorem tilesOn_union
    {K : Region} {S T : Set Tiling.Plane} {X Z Y : Set ℝ}
    (hS : TilesOn K S {z : Tiling.Plane | z.re ∈ X})
    (hT : TilesOn K T {z : Tiling.Plane | z.re ∈ Z})
    (hdis : AEDisjoint volume X Z) (hcover : Set.union X Z =ᵐ[volume] Y) :
    TilesOn K (S ∪ T) {z : Tiling.Plane | z.re ∈ Y} := by
  let SS : Fin 2 → Set Tiling.Plane := ![S, T]
  let XX : Fin 2 → Set ℝ := ![X, Z]
  have ht : ∀ i, TilesOn K (SS i) {z : Tiling.Plane | z.re ∈ XX i} := by
    intro i
    fin_cases i <;> assumption
  have hd : ∀ i j, i ≠ j → AEDisjoint volume (XX i) (XX j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hij rfl).elim
  have hXX : (⋃ i, XX i) = Set.union X Z := by
    ext x
    constructor
    · rintro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hx | hx)
      · exact Set.mem_iUnion_of_mem 0 hx
      · exact Set.mem_iUnion_of_mem 1 hx
  have hSS : (⋃ i, SS i) = Set.union S T := by
    ext x
    constructor
    · rintro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hx | hx)
      · exact Set.mem_iUnion_of_mem 0 hx
      · exact Set.mem_iUnion_of_mem 1 hx
  have hc : (⋃ i, XX i) =ᵐ[volume] Y := hXX ▸ hcover
  rw [show S ∪ T = ⋃ i, SS i from hSS.symm]
  exact tilesOn_finite_iUnion_of_aePartition ht hd hc

private noncomputable def emptyAssemblyLattice : PlanarLattice where
  basis := ![(1 : Tiling.Plane), Complex.I]
  independent := by
    rw [LinearIndependent.pair_iffₛ]
    intro s t s' t' h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    norm_num at hre him
    exact ⟨hre, him⟩

theorem periodicAssembly_empty (K : Region) :
    Nonempty (PeriodicAssembly K ∅) := by
  let A : PeriodicAssembly K ∅ := {
    centres := ∅
    tiles := by
      refine ⟨Set.countable_empty, ?_, ?_⟩
      · rw [isPacking_iff_openCarrier_disjoint]
        intro s hs
        simp at hs
      · filter_upwards [] with x
        simp
    lattice := emptyAssemblyLattice
    lattice_periods := by
      intro v hv
      rw [periodGroup_isAddSubgroup]
      simp }
  exact ⟨A⟩

theorem exists_completeCommonPeriodAssembly
    {K : Region} {Y : Set ℝ}
    (D : CommonPeriodAssemblyData K Y) : Nonempty (PeriodicAssembly K Y) := by
  let N : Set Tiling.Plane := ⋃ i, D.nonColumnCentres i
  let X : Set ℝ := ⋃ i, D.nonColumnBase i
  by_cases hn : D.numberOfNonColumnPieces = 0
  · by_cases hc : D.column = none
    · have hXempty : X = ∅ := by
        ext x
        simp only [X, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
        rintro ⟨i, -⟩
        exact Fin.elim0 (hn ▸ i)
      have hY : Y =ᵐ[volume] (∅ : Set ℝ) := by
        have h := D.bases_cover.symm
        change Y =ᵐ[volume]
          Set.union X ({x : ℝ | ∃ C, D.column = some C ∧ x ∈ C.base} : Set ℝ) at h
        have hcol : ({x : ℝ | ∃ C, D.column = some C ∧ x ∈ C.base} : Set ℝ) = ∅ := by
          ext x
          simp [hc]
        filter_upwards [h] with x hx
        have he : X.union
            {x : ℝ | ∃ C, D.column = some C ∧ x ∈ C.base} = (∅ : Set ℝ) := by
          rw [hXempty, hcol]
          exact Set.empty_union ∅
        exact hx.trans (congrFun he x)
      obtain ⟨A⟩ := periodicAssembly_empty K
      exact ⟨{ A with tiles := tilesOn_congr_cylinder_ae A.tiles hY.symm }⟩
    · obtain ⟨C, hC⟩ := Option.ne_none_iff_exists'.mp hc
      have hXempty : X = ∅ := by
        ext x
        simp only [X, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
        rintro ⟨i, -⟩
        exact Fin.elim0 (hn ▸ i)
      have hcover : C.base =ᵐ[volume] Y := by
        have h := D.bases_cover
        change Set.union X
          ({x : ℝ | ∃ C, D.column = some C ∧ x ∈ C.base} : Set ℝ) =ᵐ[volume] Y at h
        have hcol : ({x : ℝ | ∃ C', D.column = some C' ∧ x ∈ C'.base} : Set ℝ) =
            C.base := by
          ext x
          constructor
          · rintro ⟨C', hC', hx⟩
            have : C' = C := Option.some.inj (hC'.symm.trans hC)
            simpa [this] using hx
          · exact fun hx => ⟨C, hC, hx⟩
        filter_upwards [h] with x hx
        have he : X.union
            {x : ℝ | ∃ C, D.column = some C ∧ x ∈ C.base} = C.base := by
          rw [hXempty, hcol]
          exact Set.empty_union C.base
        exact (congrFun he x).symm.trans hx
      let L := triangularPlanarLattice C.verticalPeriod C.axisPeriod 0
        C.verticalPeriod_pos C.axisPeriod_pos
      refine ⟨{
        centres := C.replacement 0
        tiles := tilesOn_congr_cylinder_ae (C.replacement_tiles 0) hcover
        lattice := L
        lattice_periods := ?_ }⟩
      rw [show L.toAddSubgroup = triangularPeriodSubgroup
          C.verticalPeriod C.axisPeriod 0 by
        exact triangularPlanarLattice_toAddSubgroup _ _ _ _ _]
      exact triangular_periods (C.replacement_verticalPeriod 0)
        (C.replacement_axisPeriod 0)
  · have hnpos : 0 < D.numberOfNonColumnPieces := Nat.pos_of_ne_zero hn
    obtain ⟨Lambda, hLambda⟩ : ∃ Lambda, D.commonNonColumnLattice = some Lambda := by
      exact Option.ne_none_iff_exists'.mp
        (D.commonNonColumnLattice_isSome_iff.mpr hnpos)
    have hNTiles : TilesOn K N {z : Tiling.Plane | z.re ∈ X} := by
      apply tilesOn_finite_iUnion_of_aePartition D.nonColumn_tiles
        D.bases_pairwise_aeDisjoint.1
      exact Filter.EventuallyEq.rfl
    have hNperiod : Lambda.toAddSubgroup ≤ periodGroup N := by
      apply iUnion_periodGroup_of_common_subgroup
      intro i
      exact fun v hv => D.nonColumn_periodic i
        (D.commonNonColumnLattice_le Lambda hLambda i hv)
    by_cases hc : D.column = none
    · have hcover : X =ᵐ[volume] Y := by
        have h := D.bases_cover
        change Set.union X
          ({x : ℝ | ∃ C, D.column = some C ∧ x ∈ C.base} : Set ℝ) =ᵐ[volume] Y at h
        have hcol : ({x : ℝ | ∃ C, D.column = some C ∧ x ∈ C.base} : Set ℝ) = ∅ := by
          ext x
          simp [hc]
        filter_upwards [h] with x hx
        have he : X.union
            {x : ℝ | ∃ C, D.column = some C ∧ x ∈ C.base} = X := by
          rw [hcol]
          exact Set.union_empty X
        exact (congrFun he x).symm.trans hx
      exact ⟨{
        centres := N
        tiles := tilesOn_congr_cylinder_ae hNTiles hcover
        lattice := Lambda
        lattice_periods := hNperiod }⟩
    · obtain ⟨C, hC⟩ := Option.ne_none_iff_exists'.mp hc
      have hdis : AEDisjoint volume X C.base := by
        rw [MeasureTheory.AEDisjoint, iUnion_inter]
        exact measure_iUnion_null fun i => D.bases_pairwise_aeDisjoint.2 C hC i
      obtain ⟨IN, hINbounded, hINpos⟩ := D.mixed_nonColumnBase_positive hnpos hc
      have hXne : volume X ≠ 0 := by
        intro hzero
        have hz : volume (X ∩ IN) = 0 := measure_mono_null inter_subset_left hzero
        rw [hz] at hINpos
        simp at hINpos
      obtain ⟨IC, hICbounded, hICpos⟩ := D.mixed_columnBase_positive hnpos C hC
      have hCne : volume C.base ≠ 0 := by
        intro hzero
        have hz : volume (C.base ∩ IC) = 0 := measure_mono_null inter_subset_left hzero
        rw [hz] at hICpos
        simp at hICpos
      have hXcompl : volume Xᶜ ≠ 0 := by
        intro hzero
        have hae : C.base ≤ᵐ[volume] Xᶜ := by
          filter_upwards [measure_eq_zero_iff_ae_notMem.mp hdis] with x hx hxc
          exact fun hxX => hx ⟨hxX, hxc⟩
        exact hCne (measure_mono_null_ae hae hzero)
      have hLambdaAE : Lambda.toAddSubgroup ≤
          aePeriodGroup {z : Tiling.Plane | z.re ∈ X} := by
        intro v hv
        exact slab_aePeriod_iff_re_aePeriod.mpr
          (support_aePeriod_of_centrePeriod
            (MeasurableSet.iUnion D.nonColumnBase_measurable) hNTiles (hNperiod hv))
      obtain ⟨F⟩ := exists_verticalSlabNormalForm
        (MeasurableSet.iUnion D.nonColumnBase_measurable) hXne hXcompl hLambdaAE
      have hhN : skewPeriodVector F.horizontalPeriod F.shear ∈ periodGroup N := by
        apply hNperiod
        rw [F.subgroup_eq]
        exact ⟨0, 1, by simp⟩
      have hhorizontal := disjointPeriodicLineSets_periods_commensurable
        (MeasurableSet.iUnion D.nonColumnBase_measurable) C.base_measurable
        ⟨IN, hINbounded, hINpos⟩ ⟨IC, hICbounded, hICpos⟩ hdis
        F.horizontalPeriod_pos C.axisPeriod_pos
        (by
          simpa [skewPeriodVector] using
            support_aePeriod_of_centrePeriod
              (MeasurableSet.iUnion D.nonColumnBase_measurable) hNTiles
              hhN)
        (by
          simpa [skewPeriodVector] using
            support_aePeriod_of_centrePeriod C.base_measurable
              (C.replacement_tiles 0) (C.replacement_axisPeriod 0))
      have hh' : ∃ q : ℚ, C.axisPeriod = (q : ℝ) * F.horizontalPeriod :=
        rational_commensurable_symm F.horizontalPeriod_pos C.axisPeriod_pos hhorizontal
      obtain ⟨mh, nh, hmh, hnh, hB⟩ := exists_positive_common_multiple
        F.horizontalPeriod_pos C.axisPeriod_pos hh'
      let B := (mh : ℝ) * F.horizontalPeriod
      have hBpos : 0 < B := mul_pos (Nat.cast_pos.mpr hmh) F.horizontalPeriod_pos
      obtain ⟨R⟩ := D.mixed_rationalization Lambda C hLambda hC F B hBpos
        ⟨mh, hmh, rfl⟩ ⟨nh, hnh, hB⟩
      have hv := verticalPeriods_commensurable_of_rationalMasses R
        F.verticalPeriod_pos C.verticalPeriod_pos
      have hv' := rational_commensurable_symm F.verticalPeriod_pos
        C.verticalPeriod_pos hv
      obtain ⟨shear, common, _hshear, hcommonN, hcommonC⟩ :=
        exists_freeShear_commonSublattice F C.verticalPeriod_pos C.axisPeriod_pos hv' hh'
      have hcover : Set.union X C.base =ᵐ[volume] Y := by
        have h := D.bases_cover
        change Set.union X
          ({x : ℝ | ∃ C, D.column = some C ∧ x ∈ C.base} : Set ℝ) =ᵐ[volume] Y at h
        filter_upwards [h] with x hx
        simpa [hC] using hx
      refine ⟨{
        centres := N ∪ C.replacement shear
        tiles := tilesOn_union hNTiles (C.replacement_tiles shear) hdis hcover
        lattice := common
        lattice_periods := ?_ }⟩
      intro v hvv
      rw [periodGroup_isAddSubgroup, Set.vadd_set_union]
      congr 1
      · exact (periodGroup_isAddSubgroup N v).mp (hNperiod (hcommonN hvv))
      · exact (periodGroup_isAddSubgroup (C.replacement shear) v).mp
          (triangular_periods (C.replacement_verticalPeriod shear)
            (C.replacement_axisPeriod shear) (hcommonC hvv))

end Tiling.AxisParallel.Terminal
