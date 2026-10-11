import Tiling.AxisParallel.Structure.MinimalTilingStructure
import Tiling.AxisParallel.Terminal.PeriodicCarrierContinuousSlabs
import Tiling.AxisParallel.Terminal.SimultaneousSlabRationalization
import Tiling.AxisParallel.Terminal.FiniteLocalComplexityPeriodicity
import Tiling.AxisParallel.Continuous.CoordinateSwapTilings
import Tiling.RationalPolygonal.WeakPeriodicity
import Tiling.AxisParallel.Terminal.CommonPeriodAssembly
import Tiling.AxisParallel.Terminal.NormalFormCore
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open Tiling.AxisParallel
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Terminal


private theorem tilingSpace_of_tilesOn :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
        ∃ S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ,
          (S.centres : Set Tiling.Plane) = T := by
  intro K T hT
  obtain ⟨delta, hdelta, hsep⟩ := exists_packingSeparation K
  have hpairwise : T.Pairwise (fun x y ↦ delta ≤ dist x y) := hsep T hT.2.1
  have hclosed : IsClosed T := Metric.isClosed_of_pairwise_le_dist hdelta hpairwise
  let c : TopologicalSpace.Closeds Tiling.Plane := ⟨T, hclosed⟩
  exact ⟨{ centres := c, tilesOn := hT }, rfl⟩

private theorem exists_positive_common_multiple_local
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

private theorem exists_commonPositiveNatMultiple_aux :
    ∀ n : ℕ, ∀ (a : Fin n → ℝ), 0 < n → (∀ i, 0 < a i) →
      (∀ i j, ∃ q : ℚ, a i = (q : ℝ) * a j) →
        ∃ A : ℝ, 0 < A ∧ ∃ m : Fin n → ℕ,
          (∀ i, 0 < m i) ∧ ∀ i, A = (m i : ℝ) * a i := by
  intro n
  induction n with
  | zero =>
      intro a hn
      omega
  | succ n ih =>
      intro a hn ha hcomm
      cases n with
      | zero =>
          refine ⟨a 0, ha 0, (fun _ => 1), (by intro i; simp), ?_⟩
          intro i
          fin_cases i
          simp
      | succ n =>
          let b : Fin (Nat.succ n) → ℝ := fun i => a i.succ
          have hb : ∀ i, 0 < b i := by
            intro i
            exact ha i.succ
          have hbcomm : ∀ i j, ∃ q : ℚ, b i = (q : ℝ) * b j := by
            intro i j
            exact hcomm i.succ j.succ
          obtain ⟨B, hB, m, hm, hBm⟩ := ih b (by omega) hb hbcomm
          have hq0 : ∃ q : ℚ, b 0 = (q : ℝ) * a 0 := by
            obtain ⟨q, hq⟩ := hcomm 0 (Fin.succ 0)
            obtain ⟨q', hq'⟩ := rational_commensurable_symm (ha 0) (hb 0) ⟨q, hq⟩
            exact ⟨q', hq'⟩
          obtain ⟨qB, hqB⟩ : ∃ q : ℚ, B = (q : ℝ) * a 0 := by
            obtain ⟨q, hq⟩ := hq0
            refine ⟨(m 0 : ℚ) * q, ?_⟩
            rw [hBm 0, hq]
            push_cast
            ring
          obtain ⟨r, s, hr, hs, hrs⟩ :=
            exists_positive_common_multiple_local (ha 0) hB ⟨qB, hqB⟩
          let A : ℝ := (r : ℝ) * a 0
          let M : Fin (Nat.succ (Nat.succ n)) → ℕ :=
            Fin.cases r (fun i => s * m i)
          refine ⟨A, ?_, M, ?_, ?_⟩
          · dsimp [A]
            exact mul_pos (Nat.cast_pos.mpr hr) (ha 0)
          · intro i
            refine Fin.cases (by exact hr) (fun j => ?_) i
            exact Nat.mul_pos hs (hm j)
          · intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · simp [A, M]
            · dsimp [A, M]
              calc
                (r : ℝ) * a 0 = (s : ℝ) * B := hrs
                _ = (s : ℝ) * ((m j : ℝ) * b j) := by rw [hBm j]
                _ = ((s * m j : ℕ) : ℝ) * a j.succ := by
                  dsimp [b]
                  push_cast
                  ring

private theorem exists_commonPositiveNatMultiple
    {n : ℕ} {a : Fin n → ℝ}
    (hn : 0 < n) (ha : ∀ i, 0 < a i)
    (hcomm : ∀ i j, ∃ q : ℚ, a i = (q : ℝ) * a j) :
    ∃ A : ℝ, 0 < A ∧ ∃ m : Fin n → ℕ,
      (∀ i, 0 < m i) ∧ ∀ i, A = (m i : ℝ) * a i :=
  exists_commonPositiveNatMultiple_aux n a hn ha hcomm

private theorem normalizeShear_mod_verticalPeriod
    {alpha beta shear : ℝ} (halpha : 0 < alpha) :
    ∃ shear0 : ℝ, 0 ≤ shear0 ∧ shear0 < alpha ∧
      triangularPeriodSubgroup alpha beta shear =
        triangularPeriodSubgroup alpha beta shear0 := by
  let k : ℤ := Int.floor (shear / alpha)
  let shear0 : ℝ := shear - (k : ℝ) * alpha
  have hlo : (k : ℝ) ≤ shear / alpha := by
    exact_mod_cast (Int.floor_le (shear / alpha))
  have hhi : shear / alpha < (k : ℝ) + 1 := by
    exact_mod_cast (Int.lt_floor_add_one (shear / alpha))
  have hmul : (shear / alpha) * alpha = shear := by
    field_simp
  have h0 : 0 ≤ shear0 := by
    dsimp [shear0]
    have h := mul_le_mul_of_nonneg_right hlo (le_of_lt halpha)
    rw [hmul] at h
    linarith
  have hlt : shear0 < alpha := by
    dsimp [shear0]
    have h := mul_lt_mul_of_pos_right hhi halpha
    rw [hmul] at h
    linarith
  refine ⟨shear0, h0, hlt, ?_⟩
  apply le_antisymm
  · intro v hv
    rw [triangularPeriodSubgroup_mem_iff] at hv ⊢
    obtain ⟨m, n, rfl⟩ := hv
    refine ⟨m + n * k, n, ?_⟩
    apply Complex.ext <;> (simp [verticalPeriodVector, skewPeriodVector, shear0] <;> ring)
  · intro v hv
    rw [triangularPeriodSubgroup_mem_iff] at hv ⊢
    obtain ⟨m, n, rfl⟩ := hv
    refine ⟨m - n * k, n, ?_⟩
    apply Complex.ext <;> (simp [verticalPeriodVector, skewPeriodVector, shear0] <;> ring)

private theorem ae_comp_re_local {p : ℝ → Prop} (h : ∀ᵐ x ∂volume, p x) :
    ∀ᵐ z : Tiling.Plane ∂volume, p z.re := by
  have hp : ∀ᵐ z : ℝ × ℝ ∂volume, p z.1 :=
    Measure.quasiMeasurePreserving_fst.ae h
  have hc := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hp
  simpa only [Complex.measurableEquivRealProd_apply] using hc

private theorem tilesOn_congr_cylinder_ae_local {K : Region} {S : Set Tiling.Plane}
    {X Y : Set ℝ} (h : TilesOn K S {z : Tiling.Plane | z.re ∈ X})
    (hXY : X =ᵐ[volume] Y) :
    TilesOn K S {z : Tiling.Plane | z.re ∈ Y} :=
  ⟨h.1, h.2.1, by
    filter_upwards [h.2.2, ae_comp_re_local hXY] with z hz hzy
    exact (iff_of_eq hzy.symm).trans hz⟩

private theorem singletonSelectedPiece_wholePlaneLattice
    {K : Region} {S : Set Tiling.Plane} {X : Set ℝ}
    (hTile : TilesOn K S (Complex.re ⁻¹' X))
    (hX : X =ᵐ[volume] Set.univ)
    (hS : IsLatticePeriodic S) :
    Nonempty (PeriodicReplacement K Set.univ) := by
  let L : PlanarLattice := Classical.choose hS
  have hL : L.toAddSubgroup ≤ periodGroup S := Classical.choose_spec hS
  exact ⟨{
    centres := S
    tiles := tilesOn_congr_cylinder_ae_local hTile hX
    lattice := L
    lattice_periods := hL }⟩

private theorem periodicTilingNormalForm_to_quasiPeriodic
    {K : Region} (P : PeriodicTilingNormalForm K) :
    ∃ S : Set Tiling.Plane,
      TilesOn K S Set.univ ∧ IsQuasiPeriodic S ∧
      ∃ p : Tiling.Plane, p ≠ 0 ∧ p ∈ periodGroup S := by
  cases P with
  | wholePlaneLattice P =>
      have hne : P.centres.Nonempty := by
        by_contra hempty
        have hS : P.centres = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
        have hfalse : ∀ᵐ z : Tiling.Plane ∂volume, False := by
          filter_upwards [P.tiles.2.2] with z hz
          have hz' := hz.mp (Set.mem_univ z)
          obtain ⟨s, hs⟩ := hz'
          exact hempty ⟨s, s.property⟩
        obtain ⟨z, hz⟩ := Filter.Eventually.exists hfalse
        exact hz.elim
      let p := P.lattice.basis 0
      have hp : p ≠ 0 := P.lattice.independent.ne_zero 0
      refine ⟨P.centres, P.tiles, ?_, p, hp, ?_⟩
      · refine ⟨1, (fun _ => P.centres), ?_, ?_, ?_⟩
        · intro i
          exact ⟨hne, ⟨P.lattice, P.lattice_periods⟩⟩
        · rw [Set.pairwiseDisjoint_iff]
          intro i hi j hj hinter
          exact Subsingleton.elim _ _
        · simp only [Set.iUnion_const]
      · exact P.lattice_periods (AddSubgroup.subset_closure (Set.mem_range_self 0))
  | orientedSlabs C =>
      let S := C.originalCentres
      have hpieces : ∀ j, (C.originalPiece j).Nonempty ∧
          IsLatticePeriodic (C.originalPiece j) := by
        intro j
        refine ⟨?_, ?_⟩
        · rw [C.originalPiece_eq j]
          by_cases h : C.orientation
          · rw [if_pos h]
            exact (C.selectedPiece_nonempty j).image coordinateSwap
          · rw [if_neg h]
            exact C.selectedPiece_nonempty j
        · let v : Tiling.Plane := if C.orientation then
              coordinateSwap (verticalPeriodVector C.commonVerticalPeriod)
            else verticalPeriodVector C.commonVerticalPeriod
          let w : Tiling.Plane := if C.orientation then
              coordinateSwap (skewPeriodVector C.commonHorizontalPeriod (C.normalizedShear j))
            else skewPeriodVector C.commonHorizontalPeriod (C.normalizedShear j)
          have hv : v ∈ periodGroup (C.originalPiece j) := by
            simpa [v] using C.original_verticalPeriod j
          have hw : w ∈ periodGroup (C.originalPiece j) := by
            simpa [w] using C.original_skewPeriod j
          refine ⟨{ basis := ![v, w], independent := ?_ }, ?_⟩
          · rw [LinearIndependent.pair_iffₛ]
            intro a b c d hab
            have hre := congrArg Complex.re hab
            have him := congrArg Complex.im hab
            by_cases h : C.orientation
            · simp [v, w, h, verticalPeriodVector, skewPeriodVector] at hre him
              have hbd : b = d := him.resolve_right
                (ne_of_gt C.commonHorizontalPeriod_pos)
              subst d
              constructor
              · nlinarith [hre, C.commonVerticalPeriod_pos]
              · rfl
            · simp [v, w, h, verticalPeriodVector, skewPeriodVector] at hre him
              have hbd : b = d := hre.resolve_right
                (ne_of_gt C.commonHorizontalPeriod_pos)
              subst d
              constructor
              · nlinarith [him, C.commonVerticalPeriod_pos]
              · rfl
          · rw [Tiling.Polygonal.PlanarLattice.toAddSubgroup]
            apply (AddSubgroup.closure_le (periodGroup (C.originalPiece j))).mpr
            rintro v ⟨i, rfl⟩
            fin_cases i
            · exact hv
            · exact hw
      refine ⟨S, C.original_tiles, ?_, ?_⟩
      · refine ⟨C.numberOfPieces, C.originalPiece, hpieces, ?_, C.originalPieces_union⟩
        intro i hi j hj hij
        change Disjoint (C.originalPiece i) (C.originalPiece j)
        by_cases h : C.orientation
        · rw [C.originalPiece_eq i, C.originalPiece_eq j, if_pos h, if_pos h]
          exact (Set.disjoint_image_iff coordinateSwap.injective).mpr
            (C.selectedPiece_pairwiseDisjoint hi hj hij)
        · rw [C.originalPiece_eq i, C.originalPiece_eq j, if_neg h, if_neg h]
          exact C.selectedPiece_pairwiseDisjoint hi hj hij
      · let v : Tiling.Plane := if C.orientation then
              coordinateSwap (verticalPeriodVector C.commonVerticalPeriod)
            else verticalPeriodVector C.commonVerticalPeriod
        refine ⟨v, ?_, ?_⟩
        · have hv0 : verticalPeriodVector C.commonVerticalPeriod ≠ 0 := by
            intro hz
            have := congrArg Complex.im hz
            norm_num [verticalPeriodVector] at this
            exact (ne_of_gt C.commonVerticalPeriod_pos) this
          by_cases h : C.orientation
          · intro hz
            apply hv0
            apply coordinateSwap.injective
            simpa [v, h] using hz
          · simpa [v, h] using hv0
        · simpa [v] using C.original_commonPeriod

private structure MinimalColumnReplacement
    {K : Region} {T : Topology.TilingSpace K Set.univ}
    (D : Structure.MinimalTilingStructureData K T) where
  family : ColumnReplacementFamily D.selectedRegion
  family_base : family.base = D.columnBase
  family_source : family.sourceCentres = D.columnPart

private theorem minimalStructure_pieceReplacement
    {K : Region} {T : Topology.TilingSpace K Set.univ}
    (D : Structure.MinimalTilingStructureData K T) (j : Fin D.numberOfPieces) :
    Nonempty (PeriodicReplacement D.selectedRegion (Complex.re ⁻¹' D.base j)) := by
  exact exists_flcPeriodicReplacement
    (D.base_open j) D.horizontalPeriod_pos
    (D.base_periodic j) (D.piece_tiles j) (D.piece_hasFLC j)

private theorem minimalStructure_columnReplacementFamily
    {K : Region} {T : Topology.TilingSpace K Set.univ}
    (D : Structure.MinimalTilingStructureData K T) (hcolumn : D.columnPart.Nonempty) :
    Nonempty (MinimalColumnReplacement D) := by
  have hNonFLC : ¬ HasFLC (D.selectedTiling.centres : Set Tiling.Plane) := by
    intro hFLC
    rw [(D.finiteComplexity_normalForm hFLC).1] at hcolumn
    exact Set.not_nonempty_empty hcolumn
  have hcolumnEq := (D.nonFLC_components hNonFLC).1
  let X : PeriodicVerticalCarrier := {
    base := Set.univ
    base_open := isOpen_univ
    base_regular := by simp
    base_nonnull := by simp
    period := 1
    period_pos := by norm_num
    base_periodic := by simp }
  obtain ⟨_, _, _, _, alpha, beta, halpha, hbeta, _, _, hfree⟩ :=
    periodicColumnBase_freeShear X (by simpa [X, PeriodicVerticalCarrier.carrier]
      using D.selectedTiling.tilesOn)
      (hcolumnEq ▸ hcolumn) D.horizontalPeriod_pos
      (by simpa only [← hcolumnEq] using D.columnSupport_periodic)
  let replacement : ℝ → Set Tiling.Plane := fun w ↦ Classical.choose (hfree w)
  have hspec (w : ℝ) := Classical.choose_spec (hfree w)
  have htiles (w : ℝ) :
      TilesOn D.selectedRegion (replacement w) (Complex.re ⁻¹' D.columnBase) := by
    have hpack := (hspec w).1
    refine ⟨(IsPacking.locallyFinite_centres hpack).2, hpack, ?_⟩
    have hsupport : regularSupport D.selectedRegion (replacement w) =
        Complex.re ⁻¹' D.columnBase :=
      (hspec w).2.1.trans ((congrArg (regularSupport D.selectedRegion) hcolumnEq).symm.trans
        D.columnSupport_eq)
    filter_upwards [openUnion_aeEq_regularSupport hpack] with z hz
    change (z ∈ Complex.re ⁻¹' D.columnBase ↔
      ∃ s : replacement w, z ∈ ((s : Tiling.Plane) +ᵥ D.selectedRegion.openCarrier))
    rw [← hsupport]
    exact (Iff.of_eq hz.symm).trans (by rw [openUnion]; exact Set.mem_iUnion)
  refine ⟨⟨{
    base := D.columnBase
    base_measurable := D.columnBase_open.measurableSet
    sourceCentres := D.columnPart
    source_nonempty := hcolumn
    source_tiles := D.column_tiles
    verticalPeriod := alpha
    axisPeriod := beta
    verticalPeriod_pos := halpha
    axisPeriod_pos := hbeta
    replacement := replacement
    replacement_tiles := htiles
    replacement_verticalPeriod := ?_
    replacement_axisPeriod := ?_ }, rfl, rfl⟩⟩
  · intro w
    exact (setPeriodicBy_iff_vadd_eq _ _).mp (hspec w).2.2.1
  · intro w
    exact (setPeriodicBy_iff_vadd_eq _ _).mp (hspec w).2.2.2.1

private theorem weaklyPeriodic_finite_iUnion_local
    {I : Type} [Finite I] {S : I → Set Tiling.Plane}
    (hweak : ∀ i, Tiling.RationalPolygonal.WeaklyPeriodic (S i))
    (hdisj : Set.PairwiseDisjoint Set.univ S) :
    Tiling.RationalPolygonal.WeaklyPeriodic (⋃ i, S i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let D (i : I) : Tiling.RationalPolygonal.WeakPeriodicDecomposition (S i) :=
    Classical.choice (hweak i)
  let J := (i : I) × Fin (D i).numberOfParts
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  have hpartSub (i : I) (j : Fin (D i).numberOfParts) : (D i).part j ⊆ S i := by
    intro z hz
    exact (D i).iUnion_parts ▸ Set.mem_iUnion.mpr ⟨j, hz⟩
  have hpartsDisj (a b : J) (hab : a ≠ b) :
      Disjoint ((D a.1).part a.2) ((D b.1).part b.2) := by
    rcases a with ⟨i, j⟩
    rcases b with ⟨i', j'⟩
    by_cases hii : i = i'
    · subst i'
      exact (D i).pairwiseDisjoint (Set.mem_univ j) (Set.mem_univ j')
        (fun hjj ↦ hab (by cases hjj; rfl))
    · exact (hdisj (Set.mem_univ i) (Set.mem_univ i') hii).mono
        (hpartSub i j) (hpartSub i' j')
  refine ⟨{
    numberOfParts := Fintype.card J
    part := fun j ↦ (D (e.symm j).1).part (e.symm j).2
    period := fun j ↦ (D (e.symm j).1).period (e.symm j).2
    period_ne_zero := fun j ↦ (D (e.symm j).1).period_ne_zero (e.symm j).2
    periodic_part := fun j ↦ (D (e.symm j).1).periodic_part (e.symm j).2
    pairwiseDisjoint := fun i _ j _ hij ↦ hpartsDisj (e.symm i) (e.symm j)
      (fun h ↦ hij (e.symm.injective h))
    iUnion_parts := ?_ }⟩
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨(e.symm j).1, hpartSub _ _ hj⟩
  · rintro ⟨i, hi⟩
    rw [← (D i).iUnion_parts] at hi
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
    refine ⟨e ⟨i, j⟩, ?_⟩
    rw [e.symm_apply_apply]
    exact hj

private theorem minimalStructure_weaklyPeriodic
    {K : Region} {T : Topology.TilingSpace K Set.univ}
    (D : Structure.MinimalTilingStructureData K T) :
    Tiling.RationalPolygonal.WeaklyPeriodic (D.selectedTiling.centres : Set Tiling.Plane) ∧
      Tiling.RationalPolygonal.WeaklyPeriodic (T.centres : Set Tiling.Plane) := by
  classical
  have hpieces (j : Fin D.numberOfPieces) :
      Tiling.RationalPolygonal.WeaklyPeriodic (D.piece j) :=
    flcTiling_weaklyPeriodic (D.base_open j) D.horizontalPeriod_pos
      (D.base_periodic j) (D.piece_tiles j) (D.piece_hasFLC j)
  have hcolumn : Tiling.RationalPolygonal.WeaklyPeriodic D.columnPart := by
    by_cases hne : D.columnPart.Nonempty
    · have hNonFLC : ¬ HasFLC (D.selectedTiling.centres : Set Tiling.Plane) := by
        intro hFLC
        rw [(D.finiteComplexity_normalForm hFLC).1] at hne
        exact Set.not_nonempty_empty hne
      have hcolumnEq := (D.nonFLC_components hNonFLC).1
      let X : PeriodicVerticalCarrier := {
        base := Set.univ
        base_open := isOpen_univ
        base_regular := by simp
        base_nonnull := by simp
        period := 1
        period_pos := by norm_num
        base_periodic := by simp }
      obtain ⟨H, Y, _, hformula, alpha, _, halpha, _, _, hfibre, _⟩ :=
        periodicColumnBase_freeShear X (by simpa [X, PeriodicVerticalCarrier.carrier]
          using D.selectedTiling.tilesOn) (hcolumnEq ▸ hne) D.horizontalPeriod_pos
          (by simpa only [← hcolumnEq] using D.columnSupport_periodic)
      have hperiod : Tiling.RationalPolygonal.SetPeriodicBy D.columnPart
          (verticalPeriodVector alpha) := by
        rw [hcolumnEq, hformula]
        intro z
        simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.add_im,
          verticalPeriodVector, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
          sub_zero, mul_one, add_zero]
        constructor
        · rintro ⟨h, hh, hz, hy⟩
          refine ⟨h, hh, hz, ?_⟩
          have hy' : z.im + alpha ∈ alpha +ᵥ Y h := by
            rw [hfibre h hh]
            exact hy
          simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hy'
        · rintro ⟨h, hh, hz, hy⟩
          refine ⟨h, hh, hz, ?_⟩
          rw [← hfibre h hh]
          exact ⟨z.im, hy, by simp [add_comm]⟩
      have hzero : verticalPeriodVector alpha ≠ 0 := by
        intro hz
        have hh := congrArg Complex.im hz
        apply halpha.ne'
        simpa [verticalPeriodVector] using hh
      refine ⟨{
        numberOfParts := 1
        part := fun _ ↦ D.columnPart
        period := fun _ ↦ verticalPeriodVector alpha
        period_ne_zero := fun _ ↦ hzero
        periodic_part := fun _ ↦ hperiod
        pairwiseDisjoint := ?_
        iUnion_parts := by simp only [Set.iUnion_const] }⟩
      intro i _ j _ hij
      exact (hij (Subsingleton.elim i j)).elim
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact ⟨{
        numberOfParts := 0
        part := Fin.elim0
        period := Fin.elim0
        period_ne_zero := fun i ↦ Fin.elim0 i
        periodic_part := fun i ↦ Fin.elim0 i
        pairwiseDisjoint := by intro i; exact Fin.elim0 i
        iUnion_parts := by simp }⟩
  let part : Option (Fin D.numberOfPieces) → Set Tiling.Plane :=
    fun i ↦ i.elim D.columnPart D.piece
  have hselected : Tiling.RationalPolygonal.WeaklyPeriodic
      (D.selectedTiling.centres : Set Tiling.Plane) := by
    have hdisj : Set.PairwiseDisjoint Set.univ part := by
      intro i _ j _ hij
      cases i with
      | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some j => exact D.column_disjoint_piece j
      | some i =>
        cases j with
        | none => exact (D.column_disjoint_piece i).symm
        | some j =>
          exact D.pieces_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _)
            (fun h ↦ hij (congrArg some h))
    have hw := weaklyPeriodic_finite_iUnion_local
      (S := part) (fun i ↦ by cases i with | none => exact hcolumn | some j => exact hpieces j)
      hdisj
    have hunion : (⋃ i, part i) = D.columnPart ∪ ⋃ j, D.piece j := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        cases i with
        | none => exact Or.inl hi
        | some j => exact Or.inr ⟨j, hi⟩
      · rintro (hz | ⟨j, hz⟩)
        · exact ⟨none, hz⟩
        · exact ⟨some j, hz⟩
    rw [hunion, D.centres_partition] at hw
    exact hw
  refine ⟨hselected, ?_⟩
  rcases D.orientation_spec with ⟨_, _, hcentres⟩ | ⟨_, _, hcentres⟩
  · rwa [hcentres] at hselected
  · have hw := coordinateSwap_weaklyPeriodic hselected
    have hswap : coordinateSwap '' (coordinateSwap '' (T.centres : Set Tiling.Plane)) =
        (T.centres : Set Tiling.Plane) := by
      ext z
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        simpa only [coordinateSwap_apply_apply] using hx
      · intro hz
        refine ⟨coordinateSwap z, ⟨z, hz, rfl⟩, ?_⟩
        exact coordinateSwap_apply_apply z
    rwa [hcentres, hswap] at hw

/-- Every given topologically minimal plane tiling is weakly periodic.
This records the original-coordinate conclusion of manuscript cor:MainLocallyFin. -/
theorem topologicallyMinimalTiling_weaklyPeriodic
    {K : Region} (T : Topology.TilingSpace K Set.univ)
    (hminimal : Topology.IsTopologicallyMinimal (Topology.orbitHull T)) :
    Tiling.RationalPolygonal.WeaklyPeriodic (T.centres : Set Tiling.Plane) := by
  obtain ⟨D⟩ := Structure.exists_minimalTilingStructureData T hminimal
  exact (minimalStructure_weaklyPeriodic D).2

theorem minimalTiling_weaklyPeriodic (K : Region)
    (htileable : ∃ T : Set Tiling.Plane, TilesOn K T Set.univ) :
    ∃ T : Set Tiling.Plane, TilesOn K T Set.univ ∧
      Tiling.RationalPolygonal.WeaklyPeriodic T := by
  obtain ⟨T, hT⟩ := htileable
  obtain ⟨S, _⟩ := tilingSpace_of_tilesOn hT
  obtain ⟨M, _, hM⟩ := Structure.exists_topologicallyMinimalOrbitPoint S
  obtain ⟨D⟩ := Structure.exists_minimalTilingStructureData M hM
  exact ⟨M.centres, M.tilesOn, (minimalStructure_weaklyPeriodic D).2⟩

private structure ReplacementSlabFamily (K : Region) where
  numberOfPieces : ℕ
  atLeastTwoPieces : 2 ≤ numberOfPieces
  base : Fin numberOfPieces → Set ℝ
  base_nonempty : ∀ j, (base j).Nonempty
  base_proper : ∀ j, base j ≠ Set.univ
  base_open : ∀ j, IsOpen (base j)
  base_regular : ∀ j, interior (closure (base j)) = base j
  base_periodic : ∀ j, ∃ b : ℝ, 0 < b ∧ ∀ x, x + b ∈ base j ↔ x ∈ base j
  bases_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ base
  bases_cover : (⋃ j, base j) =ᵐ[volume] Set.univ
  replacement : ∀ j, PeriodicReplacement K (Complex.re ⁻¹' base j)

private theorem triangularPeriods_replacement
    {K : Region} {X : Set ℝ} {S : Set Tiling.Plane} {alpha beta shear : ℝ}
    (hTiles : TilesOn K S (Complex.re ⁻¹' X)) (ha : 0 < alpha) (hb : 0 < beta)
    (hv : verticalPeriodVector alpha ∈ periodGroup S)
    (hw : skewPeriodVector beta shear ∈ periodGroup S) :
    Nonempty (PeriodicReplacement K (Complex.re ⁻¹' X)) := by
  let L : PlanarLattice := {
    basis := ![verticalPeriodVector alpha, skewPeriodVector beta shear]
    independent := by
      rw [LinearIndependent.pair_iffₛ]
      intro a b c d hab
      have hre := congrArg Complex.re hab
      have him := congrArg Complex.im hab
      simp [verticalPeriodVector, skewPeriodVector] at hre him
      have hbd : b = d := hre.resolve_right (ne_of_gt hb)
      subst d
      constructor
      · nlinarith [him, ha]
      · rfl }
  refine ⟨{ centres := S, tiles := hTiles, lattice := L, lattice_periods := ?_ }⟩
  rw [PlanarLattice.toAddSubgroup]
  apply (AddSubgroup.closure_le (periodGroup S)).mpr
  rintro v ⟨i, rfl⟩
  fin_cases i
  · exact hv
  · exact hw

private theorem minimalStructure_replacementSlabFamily
    {K : Region} {T : Topology.TilingSpace K Set.univ}
    (D : Structure.MinimalTilingStructureData K T)
    (hsurvivors : (D.columnPart.Nonempty ∧ 0 < D.numberOfPieces) ∨
      2 ≤ D.numberOfPieces) : Nonempty (ReplacementSlabFamily D.selectedRegion) := by
  classical
  let R (j : Fin D.numberOfPieces) :=
    Classical.choice (minimalStructure_pieceReplacement D j)
  by_cases hcolumn : D.columnPart.Nonempty
  · have hn : 0 < D.numberOfPieces := by
      rcases hsurvivors with h | h
      · exact h.2
      · omega
    obtain ⟨C⟩ := minimalStructure_columnReplacementFamily D hcolumn
    obtain ⟨Rcolumn⟩ := triangularPeriods_replacement
      (C.family.replacement_tiles 0) C.family.verticalPeriod_pos C.family.axisPeriod_pos
      (C.family.replacement_verticalPeriod 0) (C.family.replacement_axisPeriod 0)
    let X : Fin (D.numberOfPieces + 1) → Set ℝ := Fin.cases D.columnBase D.base
    let P : ∀ j, PeriodicReplacement D.selectedRegion (Complex.re ⁻¹' X j) :=
      Fin.cases (by simpa only [X, Fin.cases_zero, C.family_base] using Rcolumn) R
    have hdisj : Set.PairwiseDisjoint Set.univ X := by
      intro i _ j _
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · refine Fin.cases ?_ (fun j' ↦ ?_) j
        · intro hij
          exact (hij rfl).elim
        · intro _
          exact D.columnBase_disjoint_base j'
      · refine Fin.cases ?_ (fun j' ↦ ?_) j
        · intro _
          exact (D.columnBase_disjoint_base i').symm
        · intro hij
          exact D.bases_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _)
            (fun h ↦ hij (congrArg Fin.succ h))
    have hcover : (⋃ j, X j) =ᵐ[volume] Set.univ := by
      have hX : (⋃ j, X j) = D.columnBase ∪ ⋃ j, D.base j := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_union]
        constructor
        · rintro ⟨j, hj⟩
          refine Fin.cases (fun h ↦ Or.inl h) (fun j' h ↦ Or.inr ⟨j', h⟩) j hj
        · rintro (h | ⟨j, hj⟩)
          · exact ⟨0, h⟩
          · exact ⟨j.succ, hj⟩
      rw [hX]
      exact D.bases_cover
    refine ⟨{ numberOfPieces := D.numberOfPieces + 1, atLeastTwoPieces := by omega
              base := X, base_nonempty := ?_, base_proper := ?_, base_open := ?_
              base_regular := ?_, base_periodic := ?_, bases_pairwiseDisjoint := hdisj
              bases_cover := hcover, replacement := P }⟩
    · intro j
      exact Fin.cases (D.columnBase_nonempty_iff.mpr hcolumn) D.base_nonempty j
    · intro j
      exact Fin.cases (D.columnBase_proper_of_piece ⟨⟨0, hn⟩⟩)
        (fun j' ↦ D.base_proper_of_multiple j' (Or.inl hcolumn)) j
    · intro j
      exact Fin.cases D.columnBase_open D.base_open j
    · intro j
      exact Fin.cases D.columnBase_regular D.base_regular j
    · intro j
      refine ⟨D.horizontalPeriod, D.horizontalPeriod_pos, ?_⟩
      exact Fin.cases D.columnBase_periodic D.base_periodic j
  · have hn : 2 ≤ D.numberOfPieces := hsurvivors.resolve_left (fun h ↦ hcolumn h.1)
    have hbase : D.columnBase = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (fun h ↦ hcolumn (D.columnBase_nonempty_iff.mp h))
    refine ⟨{ numberOfPieces := D.numberOfPieces, atLeastTwoPieces := hn
              base := D.base, base_nonempty := D.base_nonempty
              base_proper := fun j ↦ D.base_proper_of_multiple j (Or.inr hn)
              base_open := D.base_open, base_regular := D.base_regular
              base_periodic := fun j ↦ ⟨D.horizontalPeriod, D.horizontalPeriod_pos,
                D.base_periodic j⟩
              bases_pairwiseDisjoint := D.bases_pairwiseDisjoint
              bases_cover := ?_, replacement := R }⟩
    simpa only [hbase, Set.empty_union] using D.bases_cover

private theorem regularOpen_proper_complement_nonnull
    {X : Set ℝ} (hregular : interior (closure X) = X) (hproper : X ≠ Set.univ) :
    volume Xᶜ ≠ 0 := by
  have hclosure : closure X ≠ Set.univ := by
    intro h
    apply hproper
    rw [← hregular, h, interior_univ]
  have hne : (closure X)ᶜ.Nonempty := Set.nonempty_compl.mpr hclosure
  have hpos := isClosed_closure.isOpen_compl.measure_pos volume hne
  exact ne_of_gt (lt_of_lt_of_le hpos (measure_mono (Set.compl_subset_compl.mpr subset_closure)))

private theorem triangularSubgroup_le_periodGroup
    {S : Set Tiling.Plane} {alpha beta shear : ℝ}
    (hv : verticalPeriodVector alpha ∈ periodGroup S)
    (hw : skewPeriodVector beta shear ∈ periodGroup S) :
    triangularPeriodSubgroup alpha beta shear ≤ periodGroup S := by
  rintro v ⟨m, n, rfl⟩
  exact (periodGroup S).add_mem ((periodGroup S).zsmul_mem hv m)
    ((periodGroup S).zsmul_mem hw n)

private theorem replacementSlabFamily_certificate
    {K Kselected : Region} (F : ReplacementSlabFamily Kselected)
    (orientation : Bool) (hregion : Kselected = if orientation then K.coordinateSwap else K) :
    Nonempty (SlabCertificate K) := by
  classical
  let S : Fin F.numberOfPieces → Set Tiling.Plane := fun j ↦ (F.replacement j).centres
  have hFpos : 0 < F.numberOfPieces := lt_of_lt_of_le (by norm_num : 0 < 2) F.atLeastTwoPieces
  have htiles (j) : TilesOn Kselected (S j) (Complex.re ⁻¹' F.base j) :=
    (F.replacement j).tiles
  have hsupport (j) : regularSupport Kselected (S j) = Complex.re ⁻¹' F.base j := by
    apply regularSupport_eq_of_tilesOn ((F.base_open j).preimage Complex.continuous_re)
      _ (htiles j)
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, F.base_regular j]
  have hnonempty (j) : (S j).Nonempty := by
    by_contra h
    have hS := Set.not_nonempty_iff_eq_empty.mp h
    obtain ⟨x, hx⟩ := F.base_nonempty j
    have hz : (x : ℂ) ∈ regularSupport Kselected (S j) := by
      rw [hsupport j]
      simpa only [Set.mem_preimage, Complex.ofReal_re] using hx
    rw [hS, regularSupport, Tiling.Polygonal.regularSupport,
      Tiling.Polygonal.openUnion] at hz
    simp at hz
  have hpieceDisj : Set.PairwiseDisjoint Set.univ S := by
    intro i hi j hj hij
    change Disjoint (S i) (S j)
    rw [Set.disjoint_left]
    intro s hsi hsj
    obtain ⟨u, hu⟩ := Kselected.isPolygonal.interior_nonempty Kselected.nonempty
    have hmem (a) (hsa : s ∈ S a) : (s + u).re ∈ F.base a := by
      have hopen : IsOpen (openUnion Kselected (S a)) := by
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
        exact isOpen_iUnion fun t ↦ isOpen_interior.vadd (t : Tiling.Plane)
      have hz : s + u ∈ regularSupport Kselected (S a) := by
        apply hopen.subset_interior_closure
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        exact ⟨⟨s, hsa⟩, Set.mem_vadd_set.mpr ⟨u, hu, rfl⟩⟩
      rwa [hsupport a] at hz
    exact Set.disjoint_left.mp (F.bases_pairwiseDisjoint hi hj hij)
      (hmem i hsi) (hmem j hsj)
  let L (j) := (F.replacement j).lattice
  have hnormal (j) : Nonempty (VerticalSlabLatticeForm (L j)) := by
    apply exists_verticalSlabNormalForm (F.base_open j).measurableSet
      ((F.base_open j).measure_pos volume (F.base_nonempty j)).ne'
      (regularOpen_proper_complement_nonnull (F.base_regular j) (F.base_proper j))
    intro v hv
    have hvS := (F.replacement j).lattice_periods hv
    have hperiod := support_aePeriod_of_centrePeriod (F.base_open j).measurableSet
      (htiles j) hvS
    exact slab_aePeriod_iff_re_aePeriod.mpr hperiod
  let N (j) := Classical.choice (hnormal j)
  have htriangular (j) : triangularPeriodSubgroup (N j).verticalPeriod
      (N j).horizontalPeriod (N j).shear ≤ periodGroup (S j) := by
    rw [← (N j).subgroup_eq]
    exact (F.replacement j).lattice_periods
  have hv (j) : verticalPeriodVector (N j).verticalPeriod ∈ periodGroup (S j) :=
    htriangular j ⟨1, 0, by simp⟩
  have hw (j) : skewPeriodVector (N j).horizontalPeriod (N j).shear ∈ periodGroup (S j) :=
    htriangular j ⟨0, 1, by simp⟩
  have hbasePeriod (j) : (N j).horizontalPeriod +ᵥ F.base j =ᵐ[volume] F.base j := by
    simpa [skewPeriodVector] using
      support_aePeriod_of_centrePeriod (F.base_open j).measurableSet (htiles j) (hw j)
  have hpositive (j) : ∃ I : Set ℝ, Bornology.IsBounded I ∧
      0 < (volume (F.base j ∩ I)).toReal := by
    obtain ⟨A, _, hAbounded, hA, hApos⟩ := exists_boundedPositive_measurable_subset
      (F.base_open j).measurableSet ((F.base_open j).measure_pos volume (F.base_nonempty j)).ne'
    exact ⟨A, hAbounded, by rwa [Set.inter_eq_right.mpr hA]⟩
  have hhorizontalComm (i j) : ∃ q : ℚ,
      (N i).horizontalPeriod = (q : ℝ) * (N j).horizontalPeriod := by
    by_cases hij : i = j
    · subst j
      exact ⟨1, by simp⟩
    · exact disjointPeriodicLineSets_periods_commensurable
        (F.base_open i).measurableSet (F.base_open j).measurableSet (hpositive i) (hpositive j)
        (F.bases_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) hij).aedisjoint
        (N i).horizontalPeriod_pos (N j).horizontalPeriod_pos (hbasePeriod i) (hbasePeriod j)
  obtain ⟨B, hB, m, hm, hBm⟩ := exists_commonPositiveNatMultiple
    hFpos (fun j ↦ (N j).horizontalPeriod_pos) hhorizontalComm
  let shearB (j) : ℝ := (m j : ℝ) * (N j).shear
  have hwB (j) : skewPeriodVector B (shearB j) ∈ periodGroup (S j) := by
    have h := (periodGroup (S j)).nsmul_mem (hw j) (m j)
    have heq : (m j) • skewPeriodVector (N j).horizontalPeriod (N j).shear =
        skewPeriodVector B (shearB j) := by
      rw [hBm j]
      apply Complex.ext <;> simp [skewPeriodVector, shearB, nsmul_eq_mul]
    rwa [heq] at h
  have hselectedTiles : TilesOn Kselected (⋃ j, S j) Set.univ := by
    simpa only [Set.mem_univ, Set.ofPred_true] using tilesOn_finite_iUnion_of_aePartition
      htiles (fun i j hij ↦
        (F.bases_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) hij).aedisjoint) F.bases_cover
  have hmeasureDisj : Set.PairwiseDisjoint Set.univ
      (fun j ↦ volume.restrict (F.base j)) := by
    intro i hi j hj hij
    apply Measure.MutuallySingular.disjoint
    refine ⟨(F.base i)ᶜ, (F.base_open i).measurableSet.compl, ?_, ?_⟩
    · rw [Measure.restrict_apply (F.base_open i).measurableSet.compl,
        Set.compl_inter_self, measure_empty]
    · rw [compl_compl, Measure.restrict_apply (F.base_open i).measurableSet,
        Set.disjoint_iff_inter_eq_empty.mp (F.bases_pairwiseDisjoint hi hj hij), measure_empty]
  let P : FiniteSlabPartition Kselected (⋃ j, S j) := {
    carrierBase := Set.univ
    carrierBase_open := isOpen_univ
    carrierBase_regular := by simp
    carrierBase_nonnull := by simp
    source_tiles := by simpa only [Set.preimage_univ] using hselectedTiles
    numberOfParts := F.numberOfPieces
    numberOfParts_pos := hFpos
    partCentres := S
    partCentres_nonempty := hnonempty
    partCentres_pairwise := hpieceDisj
    partCentres_union := rfl
    partBase := F.base
    partBase_open := F.base_open
    partBase_regular := F.base_regular
    partBase_ae_disjoint := hmeasureDisj
    partBase_ae_partition := by
      rw [← Measure.restrict_congr_set F.bases_cover,
        Measure.restrict_iUnion
          (fun i j hij ↦ F.bases_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) hij)
          (fun j ↦ (F.base_open j).measurableSet), Measure.sum_fintype]
    part_tiles := htiles
    commonPeriod := B
    commonPeriod_pos := hB
    carrierBase_periodic := by simp
    verticalPeriod := fun j ↦ (N j).verticalPeriod
    verticalPeriod_pos := fun j ↦ (N j).verticalPeriod_pos
    shear := shearB
    part_vertical_period := hv
    part_skew_period := hwB }
  -- One deformation supplies rational masses for every replacement, including the column.
  obtain ⟨R⟩ := exists_simultaneousSlabRationalization P
  have hverticalComm (i j) : ∃ q : ℚ,
      (N i).verticalPeriod = (q : ℝ) * (N j).verticalPeriod := by
    -- Both torus-area identities use the same deformed tile, so its area cancels.
    let M : MixedRationalizationDatum (N i).verticalPeriod (N j).verticalPeriod B := {
      deformedRegion := R.deformation.firstRegion
      nonColumnCentres := R.deformedPartCentres i
      columnCentres := R.deformedPartCentres j
      nonColumnBase := R.deformedPartBase i
      columnBase := R.deformedPartBase j
      nonColumnBase_measurable := (R.deformedPartBase_open i).measurableSet
      columnBase_measurable := (R.deformedPartBase_open j).measurableSet
      rationalHorizontalPeriod := (R.rationalHorizontalPeriod : ℝ)
      nonColumnShear := shearB i
      columnShear := shearB j
      sourceCommonPeriod_pos := hB
      rationalHorizontalPeriod_pos := by exact_mod_cast R.rationalHorizontalPeriod_pos
      nonColumnTiles := R.deformed_part_tiles i
      columnTiles := R.deformed_part_tiles j
      nonColumnVerticalPeriod := R.deformed_part_vertical_period i
      nonColumnHorizontalPeriod := R.deformed_part_skew_period i
      columnVerticalPeriod := R.deformed_part_vertical_period j
      columnHorizontalPeriod := R.deformed_part_skew_period j
      nonColumnMass := R.rationalMass i
      columnMass := R.rationalMass j
      nonColumnMass_pos := R.rationalMass_pos i
      columnMass_pos := R.rationalMass_pos j
      nonColumnMass_eq := R.rationalMass_eq i
      columnMass_eq := R.rationalMass_eq j }
    exact verticalPeriods_commensurable_of_rationalMasses M
      (N i).verticalPeriod_pos (N j).verticalPeriod_pos
  obtain ⟨A, hA, n, hn, hAn⟩ := exists_commonPositiveNatMultiple
    hFpos (fun j ↦ (N j).verticalPeriod_pos) hverticalComm
  have hvA (j) : verticalPeriodVector A ∈ periodGroup (S j) := by
    have h := (periodGroup (S j)).nsmul_mem (hv j) (n j)
    have heq : (n j) • verticalPeriodVector (N j).verticalPeriod = verticalPeriodVector A := by
      rw [hAn j]
      apply Complex.ext <;> simp [verticalPeriodVector, nsmul_eq_mul]
    rwa [heq] at h
  have hnormalize (j) := normalizeShear_mod_verticalPeriod (beta := B) (shear := shearB j) hA
  let shear0 (j) : ℝ := Classical.choose (hnormalize j)
  have hshear0 (j) := Classical.choose_spec (hnormalize j)
  have hw0 (j) : skewPeriodVector B (shear0 j) ∈ periodGroup (S j) := by
    have hsub := triangularSubgroup_le_periodGroup (hvA j) (hwB j)
    rw [(hshear0 j).2.2] at hsub
    exact hsub ⟨0, 1, by simp [shear0]⟩
  have hselectedCommon : verticalPeriodVector A ∈ periodGroup (⋃ j, S j) := by
    rw [periodGroup_isAddSubgroup, Set.vadd_set_iUnion]
    congr 1
    funext j
    exact (periodGroup_isAddSubgroup _ _).mp (hvA j)
  let originalPiece (j) : Set Tiling.Plane := if orientation then coordinateSwap '' S j else S j
  let originalCentres : Set Tiling.Plane := if orientation then coordinateSwap '' (⋃ j, S j)
    else ⋃ j, S j
  have horiginalUnion : (⋃ j, originalPiece j) = originalCentres := by
    cases orientation <;> simp only [originalPiece, originalCentres, Bool.false_eq_true,
      ↓reduceIte, Set.image_iUnion]
  have horiginalTiles : TilesOn K originalCentres Set.univ := by
    cases orientation with
    | false =>
      simpa only [Bool.false_eq_true, ↓reduceIte, originalCentres, hregion] using hselectedTiles
    | true =>
      have h := tilesOn_coordinateSwap hselectedTiles
      simpa only [hregion, Region.coordinateSwap_involutive,
        Set.image_univ_of_surjective coordinateSwap.surjective, originalCentres, ↓reduceIte] using h
  have horiginalPieceTiles (j) : TilesOn K (originalPiece j)
      (if orientation then {z : Tiling.Plane | z.im ∈ F.base j}
        else {z : Tiling.Plane | z.re ∈ F.base j}) := by
    cases orientation with
    | false => simpa only [Bool.false_eq_true, ↓reduceIte, originalPiece, hregion,
        Set.preimage, Set.mem_ofPred_eq] using htiles j
    | true =>
      have himage : coordinateSwap '' (Complex.re ⁻¹' F.base j) =
          {z : Tiling.Plane | z.im ∈ F.base j} := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          simpa only [Set.mem_preimage, Set.mem_ofPred_eq, coordinateSwap_im] using hw
        · intro hz
          exact ⟨coordinateSwap z, by simpa only [Set.mem_preimage, Set.mem_ofPred_eq,
            coordinateSwap_re] using hz,
            coordinateSwap_apply_apply z⟩
      have h := tilesOn_coordinateSwap (htiles j)
      simpa only [hregion, Region.coordinateSwap_involutive, originalPiece, ↓reduceIte,
        himage] using h
  refine ⟨{
    orientation := orientation
    selectedRegion := Kselected
    selectedRegion_eq := hregion
    numberOfPieces := F.numberOfPieces
    atLeastTwoPieces := F.atLeastTwoPieces
    selectedCentres := ⋃ j, S j
    selectedPiece := S
    selectedPiece_nonempty := hnonempty
    selectedPiece_pairwiseDisjoint := hpieceDisj
    selectedPieces_union := rfl
    selected_tiles := hselectedTiles
    base := F.base
    base_nonempty := F.base_nonempty
    base_proper := F.base_proper
    base_open := F.base_open
    base_regular := F.base_regular
    base_periodic := F.base_periodic
    piece_tiles := htiles
    bases_pairwise_aeDisjoint := F.bases_pairwiseDisjoint.aedisjoint
    bases_cover := F.bases_cover
    verticalPeriod := fun j ↦ (N j).verticalPeriod
    horizontalPeriod := fun j ↦ (N j).horizontalPeriod
    shear := fun j ↦ (N j).shear
    verticalPeriod_pos := fun j ↦ (N j).verticalPeriod_pos
    horizontalPeriod_pos := fun j ↦ (N j).horizontalPeriod_pos
    individual_verticalPeriod := hv
    individual_skewPeriod := hw
    vertical_commensurable := hverticalComm
    horizontal_commensurable := hhorizontalComm
    commonVerticalPeriod := A
    commonHorizontalPeriod := B
    commonVerticalPeriod_pos := hA
    commonHorizontalPeriod_pos := hB
    verticalMultiplier := n
    horizontalMultiplier := m
    verticalMultiplier_pos := hn
    horizontalMultiplier_pos := hm
    commonVerticalPeriod_eq := hAn
    commonHorizontalPeriod_eq := hBm
    normalizedShear := shear0
    normalizedShear_nonnegative := fun j ↦ (hshear0 j).1
    normalizedShear_lt := fun j ↦ (hshear0 j).2.1
    common_verticalPeriod := hvA
    common_skewPeriod := hw0
    selected_commonPeriod := hselectedCommon
    originalCentres := originalCentres
    originalPiece := originalPiece
    originalCentres_eq := rfl
    originalPiece_eq := fun _ ↦ rfl
    originalPieces_union := horiginalUnion
    original_tiles := horiginalTiles
    originalPiece_tiles := horiginalPieceTiles
    original_verticalPeriod := ?_
    original_skewPeriod := ?_
    original_commonPeriod := ?_ }⟩
  · intro j
    cases orientation with
    | false => exact hvA j
    | true => exact coordinateSwap_periodGroup (hvA j)
  · intro j
    cases orientation with
    | false => exact hw0 j
    | true => exact coordinateSwap_periodGroup (hw0 j)
  · cases orientation with
    | false => exact hselectedCommon
    | true => exact coordinateSwap_periodGroup hselectedCommon

private theorem minimalStructure_slabCertificate
    {K : Region} {T : Topology.TilingSpace K Set.univ}
    (D : Structure.MinimalTilingStructureData K T) :
    ¬ HasFLC (D.selectedTiling.centres : Set Tiling.Plane) →
    ((D.columnPart.Nonempty ∧ 0 < D.numberOfPieces) ∨ 2 ≤ D.numberOfPieces) →
    Nonempty (SlabCertificate K) := by
  intro _ hsurvivors
  obtain ⟨F⟩ := minimalStructure_replacementSlabFamily D hsurvivors
  rcases D.orientation_spec with ⟨_, hregion, _⟩ | ⟨_, hregion, _⟩
  · exact replacementSlabFamily_certificate F false hregion
  · exact replacementSlabFamily_certificate F true hregion

private theorem minimalStructure_periodicTilingNormalForm
    {K : Region} {T : Topology.TilingSpace K Set.univ}
    (D : Structure.MinimalTilingStructureData K T) :
    Nonempty (PeriodicTilingNormalForm K) := by
  classical
  by_cases hslab :
      (D.columnPart.Nonempty ∧ 0 < D.numberOfPieces) ∨ 2 ≤ D.numberOfPieces
  · have hNonFLC : ¬ HasFLC (D.selectedTiling.centres : Set Tiling.Plane) := by
      intro hFLC
      obtain ⟨hcolumn, hnumber, _⟩ := D.finiteComplexity_normalForm hFLC
      rcases hslab with ⟨hcolumnNonempty, _⟩ | htwo
      · rw [hcolumn] at hcolumnNonempty
        exact Set.not_nonempty_empty hcolumnNonempty
      · omega
    obtain ⟨C⟩ := minimalStructure_slabCertificate
      D hNonFLC hslab
    exact ⟨PeriodicTilingNormalForm.orientedSlabs C⟩
  have hselected : Nonempty (PeriodicReplacement D.selectedRegion Set.univ) := by
    by_cases hzero : D.numberOfPieces = 0
    · have hcolumn : D.columnPart.Nonempty := by
        rcases D.somePart_nonempty with hcolumn | hj
        · exact hcolumn
        · obtain ⟨j⟩ := hj
          exact Fin.elim0 (hzero ▸ j)
      obtain ⟨C⟩ := minimalStructure_columnReplacementFamily D hcolumn
      have hbaseUnion : (⋃ j, D.base j) = ∅ := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
        rintro ⟨j, _⟩
        exact Fin.elim0 (hzero ▸ j)
      have hcover : C.family.base =ᵐ[volume] Set.univ := by
        rw [C.family_base]
        simpa only [hbaseUnion, Set.union_empty] using D.bases_cover
      obtain ⟨P⟩ := triangularPeriods_replacement
        (C.family.replacement_tiles 0) C.family.verticalPeriod_pos C.family.axisPeriod_pos
        (C.family.replacement_verticalPeriod 0) (C.family.replacement_axisPeriod 0)
      exact singletonSelectedPiece_wholePlaneLattice P.tiles hcover
        ⟨P.lattice, P.lattice_periods⟩
    · have hpos : 0 < D.numberOfPieces := Nat.pos_of_ne_zero hzero
      have hcolumn : D.columnPart = ∅ := by
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hcolumn
        exact hslab (Or.inl ⟨hcolumn, hpos⟩)
      have hone : D.numberOfPieces = 1 := by
        have hnotTwo : ¬ 2 ≤ D.numberOfPieces := fun htwo ↦ hslab (Or.inr htwo)
        omega
      let j : Fin D.numberOfPieces := ⟨0, hpos⟩
      have hbaseUnion : (⋃ k, D.base k) = D.base j := by
        let : Nonempty (Fin D.numberOfPieces) := ⟨j⟩
        have hindex : ∀ k : Fin D.numberOfPieces, k = j := by
          intro k
          apply Fin.ext
          have hk := k.isLt
          dsimp only [j]
          omega
        simp only [hindex, Set.iUnion_const]
      have hcolumnBase : D.columnBase = ∅ := by
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hne
        have hc := D.columnBase_nonempty_iff.mp hne
        rw [hcolumn] at hc
        exact Set.not_nonempty_empty hc
      have hcover : D.base j =ᵐ[volume] Set.univ := by
        simpa only [hcolumnBase, hbaseUnion, Set.empty_union] using D.bases_cover
      obtain ⟨P⟩ := minimalStructure_pieceReplacement D j
      exact ⟨{ P with tiles := tilesOn_congr_cylinder_ae_local P.tiles hcover }⟩
  obtain ⟨P⟩ := hselected
  rcases D.orientation_spec with ⟨_, hregion, _⟩ | ⟨_, hregion, _⟩
  · exact ⟨PeriodicTilingNormalForm.wholePlaneLattice (hregion ▸ P)⟩
  · let L : PlanarLattice := {
      basis := fun i ↦ coordinateSwap (P.lattice.basis i)
      independent := P.lattice.independent.map' coordinateSwap.toLinearMap
        coordinateSwap.ker }
    refine ⟨PeriodicTilingNormalForm.wholePlaneLattice {
      centres := coordinateSwap '' P.centres
      tiles := ?_
      lattice := L
      lattice_periods := ?_ }⟩
    · have htiles := tilesOn_coordinateSwap P.tiles
      simpa only [hregion, Region.coordinateSwap_involutive,
        Set.image_univ, coordinateSwap.surjective.range_eq] using htiles
    · rw [PlanarLattice.toAddSubgroup]
      apply (AddSubgroup.closure_le (periodGroup (coordinateSwap '' P.centres))).mpr
      rintro v ⟨i, rfl⟩
      exact coordinateSwap_periodGroup
        (P.lattice_periods (AddSubgroup.subset_closure (Set.mem_range_self i)))

theorem exists_periodicTilingNormalForm (K : Region) :
    (∃ T : Set Tiling.Plane, TilesOn K T Set.univ) →
      Nonempty (PeriodicTilingNormalForm K) := by
  intro htileable
  obtain ⟨T, hT⟩ := htileable
  obtain ⟨S, _⟩ := tilingSpace_of_tilesOn hT
  obtain ⟨M, _, hM⟩ := Structure.exists_topologicallyMinimalOrbitPoint S
  obtain ⟨D⟩ := Structure.exists_minimalTilingStructureData M hM
  exact minimalStructure_periodicTilingNormalForm D

theorem exists_quasiPeriodicTiling_commonPeriod (K : Region) :
    (∃ T : Set Tiling.Plane, TilesOn K T Set.univ) →
      ∃ S : Set Tiling.Plane, TilesOn K S Set.univ ∧ IsQuasiPeriodic S ∧
        ∃ p : Tiling.Plane, p ≠ 0 ∧ p ∈ periodGroup S := by
  intro htileable
  obtain ⟨P⟩ := exists_periodicTilingNormalForm K htileable
  exact periodicTilingNormalForm_to_quasiPeriodic P


set_option linter.hashCommand false in
#print axioms tilingSpace_of_tilesOn
set_option linter.hashCommand false in
#print axioms exists_commonPositiveNatMultiple
set_option linter.hashCommand false in
#print axioms normalizeShear_mod_verticalPeriod
set_option linter.hashCommand false in
#print axioms singletonSelectedPiece_wholePlaneLattice
set_option linter.hashCommand false in
#print axioms periodicTilingNormalForm_to_quasiPeriodic
set_option linter.hashCommand false in
#print axioms minimalStructure_pieceReplacement
set_option linter.hashCommand false in
#print axioms minimalStructure_columnReplacementFamily
set_option linter.hashCommand false in
#print axioms minimalStructure_weaklyPeriodic
set_option linter.hashCommand false in
#print axioms minimalTiling_weaklyPeriodic

set_option linter.hashCommand false in
#print axioms minimalStructure_slabCertificate
set_option linter.hashCommand false in
#print axioms minimalStructure_periodicTilingNormalForm
set_option linter.hashCommand false in
#print axioms exists_periodicTilingNormalForm
set_option linter.hashCommand false in
#print axioms exists_quasiPeriodicTiling_commonPeriod

end Tiling.AxisParallel.Terminal
