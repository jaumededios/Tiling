import Tiling.AxisParallel.Continuous.PositiveSimilarityPlates
import Mathlib.Data.Fin.VecNotation
import Tiling.AxisParallel.Approximation.RectangularRegionImage
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Foundations.GenericSlices
import Tiling.AxisParallel.Foundations.FilledSliceChains
import Tiling.AxisParallel.Foundations.RationalMeshRaster
import Tiling.AxisParallel.Discrete.DiscretePlatePeriodicity
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.ApproximationPreservesEarthquakes
import Tiling.RationalPolygonal.Raster

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true


/-!
# Rational continuous slab periodicity

The plate-compatible integerization certificate and its exact component-membership consequence.
The geometric integralization and periodicity constructions are proved below.
-/

open MeasureTheory Set Filter
open scoped Matrix Pointwise Topology

namespace Tiling.AxisParallel.Continuous

structure PlateCompatibleIntegerization
    (K : Region) (T : Set Tiling.Plane) where
  scale : ℕ
  scale_pos : 0 < scale
  tileAnchor : Tiling.Plane
  tileAnchor_mem : tileAnchor ∈ K.vertices
  commonHorizontalShift : ℝ
  plateVerticalShift : VerticalPlate K T → ℝ
  integerRegion : Region
  integerRegion_openCarrier :
    integerRegion.openCarrier =
      (scale : ℝ) • (-tileAnchor +ᵥ K.openCarrier)
  integerVertices : ∀ v ∈ integerRegion.vertices,
    Tiling.RationalPolygonal.IsIntegerPoint v
  discreteTile : Finset TranslationalTilings.Plane
  discreteTile_nonempty : discreteTile.Nonempty
  discreteTile_realizes_integerRegion :
    integerRegion.openCarrier =ᵐ[MeasureTheory.volume]
      ⋃ f : discreteTile,
        Tiling.RationalPolygonal.integerPoint
            (f : TranslationalTilings.Plane) +ᵥ
          interior (Complex.Rectangle 0 (1 + Complex.I))
  discreteCentres : Set TranslationalTilings.Plane
  discrete_tiling :
    TranslationalTilings.Tiles discreteTile discreteCentres Set.univ
  centreEquiv : T ≃ discreteCentres
  centreEquiv_apply : ∀ t : T,
    Tiling.RationalPolygonal.integerPoint
        ((centreEquiv t : discreteCentres) : TranslationalTilings.Plane) =
      (scale : ℝ) •
          ((t : Tiling.Plane) + tileAnchor +
            (((commonHorizontalShift : ℝ) : ℂ))) +
        (((plateVerticalShift (VerticalPlate.ofCentre t) : ℝ) : ℂ) *
          Complex.I)
  plateEquiv : VerticalPlate K T ≃
    Tiling.RationalPolygonal.QuakePlate
      discreteTile discreteCentres
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit
  centreEquiv_mem_plate : ∀ P : VerticalPlate K T, ∀ t : T,
    (t : Tiling.Plane) ∈ P.centres ↔
      ((centreEquiv t : discreteCentres) : TranslationalTilings.Plane) ∈
        Tiling.RationalPolygonal.quakePlateTranslations (plateEquiv P)
  column_iff : ∀ P : VerticalPlate K T,
    IsVerticalColumn P ↔
      Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn (plateEquiv P)
  carrier_eq : ∀ P : VerticalPlate K T,
    regularSupport integerRegion
      (Tiling.RationalPolygonal.integerPoint ''
        Tiling.RationalPolygonal.quakePlateTranslations (plateEquiv P)) =
      (scale : ℝ) •
        (((commonHorizontalShift : ℝ) : ℂ) +ᵥ P.support)
  columnAggregate_centres_eq :
    centreEquiv ''
        {t : T | (t : Tiling.Plane) ∈ verticalColumnCentres K T} =
      {a : discreteCentres |
        (a : TranslationalTilings.Plane) ∈
          Tiling.AxisParallel.Discrete.discreteColumnUnion
            discreteTile discreteCentres}
  columnAggregate_carrier_eq :
    regularSupport integerRegion
        (Tiling.RationalPolygonal.integerPoint ''
          Tiling.AxisParallel.Discrete.discreteColumnUnion
            discreteTile discreteCentres) =
      (scale : ℝ) •
        (((commonHorizontalShift : ℝ) : ℂ) +ᵥ
          regularSupport K (verticalColumnCentres K T))

theorem continuousDiscretePlateEquiv
    {K : Region} {T : Set Tiling.Plane}
    (I : PlateCompatibleIntegerization K T)
    (P : VerticalPlate K T) :
    I.centreEquiv ''
      {t : T | (t : Tiling.Plane) ∈ P.centres} =
      {a : I.discreteCentres |
        (a : TranslationalTilings.Plane) ∈
          Tiling.RationalPolygonal.quakePlateTranslations (I.plateEquiv P)} := by
  ext a
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (I.centreEquiv_mem_plate P t).mp ht
  · intro ha
    refine ⟨I.centreEquiv.symm a, ?_, I.centreEquiv.apply_symm_apply a⟩
    apply (I.centreEquiv_mem_plate P (I.centreEquiv.symm a)).mpr
    simpa using ha

end Tiling.AxisParallel.Continuous

open MeasureTheory Set
open scoped Matrix Pointwise Topology
noncomputable section

namespace Tiling.AxisParallel.Continuous

open Tiling
open Tiling.AxisParallel
open Tiling.AxisParallel.RationalMesh
open Tiling.RationalPolygonal
open Tiling.AxisParallel.Foundations.FilledSliceChains

private structure IntegralTileNormalization (K : Region) where
  scale : ℕ
  scale_pos : 0 < scale
  anchor : Tiling.Plane
  anchor_mem : anchor ∈ K.vertices
  region : Region
  carrier_eq : region.openCarrier = (scale : ℝ) • (-anchor +ᵥ K.openCarrier)
  vertices_integer : ∀ v ∈ region.vertices,
    Tiling.RationalPolygonal.IsIntegerPoint v

private theorem integralTileNormalization_exists :
    ∀ (K : Region),
      Tiling.RationalPolygonal.IsRelativelyRational K.toPolygonalRegion →
        Nonempty (IntegralTileNormalization K) := by
  classical
  intro K hrat
  obtain ⟨anchor, hanchor, hrat⟩ := hrat
  have hanchorK : anchor ∈ K.vertices := hanchor
  let V : Finset Tiling.Plane := K.vertexFinset
  let q : Tiling.Plane → ℚ × ℚ := fun v =>
    if hv : v ∈ K.vertices then
      let h := show ∃ x y : ℚ, (v - anchor).re = x ∧ (v - anchor).im = y
        from hrat v hv
      (Classical.choose h, Classical.choose (Classical.choose_spec h))
    else (0, 0)
  have hq (v : Tiling.Plane) (hv : v ∈ K.vertices) :
      (v - anchor).re = (q v).1 ∧ (v - anchor).im = (q v).2 := by
    dsimp [q]
    rw [dif_pos hv]
    let h := show ∃ x y : ℚ, (v - anchor).re = x ∧ (v - anchor).im = y
      from hrat v hv
    exact Classical.choose_spec (Classical.choose_spec h)
  let d : ℕ := ∏ v ∈ V, (q v).1.den * (q v).2.den
  have hdpos : 0 < d := by
    dsimp [d]
    exact Finset.prod_pos (fun v hv ↦ Nat.mul_pos (Rat.den_pos _) (Rat.den_pos _))
  have hvV (v : Tiling.Plane) (hv : v ∈ K.vertices) : v ∈ V := by
    dsimp [V]
    change v ∈ (K.vertexFinset : Set Tiling.Plane)
    rw [K.coe_vertexFinset]
    exact hv
  have hden1 (v : Tiling.Plane) (hv : v ∈ K.vertices) :
      (q v).1.den ∣ d := by
    apply (dvd_mul_right ((q v).1.den) ((q v).2.den)).trans
    exact Finset.dvd_prod_of_mem (fun w ↦ (q w).1.den * (q w).2.den) (hvV v hv)
  have hden2 (v : Tiling.Plane) (hv : v ∈ K.vertices) :
      (q v).2.den ∣ d := by
    apply (dvd_mul_right ((q v).2.den) ((q v).1.den)).trans
    simpa [Nat.mul_comm] using
      (Finset.dvd_prod_of_mem (fun w ↦ (q w).1.den * (q w).2.den) (hvV v hv))
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
  have hInt (v : Tiling.Plane) (hv : v ∈ K.vertices) :
      Tiling.RationalPolygonal.IsIntegerPoint
        ((d : ℝ) • (-anchor +ᵥ v)) := by
    obtain ⟨k₁, hk₁⟩ := hden1 v hv
    obtain ⟨k₂, hk₂⟩ := hden2 v hv
    rw [Tiling.RationalPolygonal.IsIntegerPoint]
    apply Tiling.RationalPolygonal.mem_integerLattice_iff.mpr
    let z : TranslationalTilings.Plane := fun i =>
      if i = 0 then (q v).1.num * k₁ else (q v).2.num * k₂
    refine ⟨z, ?_⟩
    apply Complex.ext
    · simp only [Tiling.RationalPolygonal.integerPoint_re, Fin.isValue, vadd_eq_add,
        smul_add, smul_neg, Complex.real_smul, Complex.ofReal_natCast,
        Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re,
        Complex.natCast_im, zero_mul, sub_zero, z]
      have hcoord := (hq v hv).1
      rw [Rat.cast_def] at hcoord
      rw [hk₁]
      field_simp [Rat.den_nz] at hcoord
      push_cast
      simp only [Complex.sub_re] at hcoord ⊢
      linear_combination -k₁ * hcoord
    · simp only [Tiling.RationalPolygonal.integerPoint_im, Fin.isValue, vadd_eq_add,
        smul_add, smul_neg, Complex.real_smul, Complex.ofReal_natCast,
        Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.natCast_re,
        Complex.natCast_im, zero_mul, add_zero, z]
      have hcoord := (hq v hv).2
      rw [Rat.cast_def] at hcoord
      rw [hk₂]
      field_simp [Rat.den_nz] at hcoord
      push_cast
      simp only [Complex.sub_im] at hcoord ⊢
      linear_combination -k₂ * hcoord
  let dx : ℝ ≃ₜ ℝ :=
    (Homeomorph.addLeft (-anchor.re)).trans
      (Homeomorph.smulOfNeZero (d : ℝ) hdne)
  let dy : ℝ ≃ₜ ℝ :=
    (Homeomorph.addLeft (-anchor.im)).trans
      (Homeomorph.smulOfNeZero (d : ℝ) hdne)
  have hdx : StrictMono dx := by
    have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
    intro x y hxy
    change (d : ℝ) * (-anchor.re + x) < (d : ℝ) * (-anchor.re + y)
    nlinarith
  have hdy : StrictMono dy := by
    have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
    intro x y hxy
    change (d : ℝ) * (-anchor.im + x) < (d : ℝ) * (-anchor.im + y)
    nlinarith
  obtain ⟨L, hLsupport, hLopen, hLvertices⟩ :=
    Tiling.AxisParallel.Approximation.exists_coordinateProductImageRegion K dx dy hdx hdy
  have hH (x : Tiling.Plane) :
      Tiling.AxisParallel.Approximation.coordinateProductHomeomorph dx dy x =
        (d : ℝ) • (-anchor +ᵥ x) := by
    rw [Tiling.AxisParallel.Approximation.coordinateProductHomeomorph_apply]
    apply Complex.ext <;> simp [dx, dy]
    · ring
    · ring
  refine ⟨⟨d, hdpos, anchor, hanchorK, L, ?_, ?_⟩⟩
  · rw [hLopen]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨-anchor +ᵥ y, ⟨y, hy, rfl⟩, (hH y).symm⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz⟩ := hy
      refine ⟨z, hz, ?_⟩
      rw [hH]
      change (d : ℝ) • (-anchor +ᵥ z) = (d : ℝ) • y
      rw [← hxz]
  · intro v hv
    rw [hLvertices] at hv
    obtain ⟨w, hw, hvw⟩ := hv
    rw [← hvw, hH]
    exact hInt w hw

private theorem integerRegion_gridCells :
    ∀ (K : Region),
    (∀ v ∈ K.vertices, Tiling.RationalPolygonal.IsIntegerPoint v) →
    ∃ F : Finset TranslationalTilings.Plane, F.Nonempty ∧
      K.openCarrier =ᵐ[volume] ⋃ f : F,
        Tiling.RationalPolygonal.integerPoint
            (f : TranslationalTilings.Plane) +ᵥ
          interior (Complex.Rectangle 0 (1 + Complex.I)) := by
  intro K hK
  have hmesh : OnRationalMesh 1 K.vertices := by
    intro v hv
    obtain ⟨z, hz⟩ := mem_integerLattice_iff.mp (hK v hv)
    refine ⟨z, ?_⟩
    apply Complex.ext
    · simpa [rationalScale, integerPoint] using congrArg Complex.re hz
    · simpa [rationalScale, integerPoint] using congrArg Complex.im hz
  obtain ⟨F, hFne, hFraster, hae, _hreg⟩ :=
    Tiling.AxisParallel.RationalMesh.exists_regionRaster (K := K) (d := 1)
      (by simp) hmesh
  refine ⟨F, hFne, ?_⟩
  have hcell (z : ZPlane) :
      meshCell 1 z = integerPoint z +ᵥ interior (Complex.Rectangle 0 (1 + Complex.I)) := by
    have hunit : interior (Complex.Rectangle 0 (1 + Complex.I)) =
        {w : Tiling.Plane | 0 < w.re ∧ w.re < 1 ∧ 0 < w.im ∧ w.im < 1} := by
      have hrect : Complex.Rectangle 0 (1 + Complex.I) = Icc 0 1 ×ℂ Icc 0 1 := by
        ext w
        simp [Complex.Rectangle]
      rw [hrect]
      rw [Complex.interior_reProdIm]
      ext w
      change (w.re ∈ interior (Icc 0 1) ∧ w.im ∈ interior (Icc 0 1)) ↔ _
      simp [interior_Icc]
      tauto
    ext x
    rw [hunit]
    simp [meshCell, rationalScale, integerPoint,
      Set.mem_vadd_set_iff_neg_vadd_mem]
  have hunion :
      (⋃ f : F, meshCell 1 (f : ZPlane)) =
        ⋃ f : F, integerPoint (f : ZPlane) +ᵥ
          interior (Complex.Rectangle 0 (1 + Complex.I)) := by
    apply iUnion_congr
    intro f
    exact hcell f
  rw [← hunion]
  exact hae

private theorem c04_verticalPlate_centres_nonempty
    {K : Region} {T : Set Tiling.Plane} (P : VerticalPlate K T) :
    P.centres.Nonempty := by
  obtain ⟨t, ht⟩ := P.nonempty_supp
  exact ⟨t.1, t, ht, rfl⟩

private theorem c04_verticalPlate_base_nonempty
    {K : Region} {T : Set Tiling.Plane} (P : VerticalPlate K T) :
    P.base.Nonempty := by
  obtain ⟨t, htP⟩ := c04_verticalPlate_centres_nonempty P
  obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
  refine ⟨(t + u).re, ?_⟩
  rw [VerticalPlate.base_eq]
  refine ⟨t + u, ?_, rfl⟩
  change t + u ∈ regularSupport K P.centres
  have hopen : IsOpen (openUnion K P.centres) := by
    apply isOpen_iUnion
    intro s
    exact isOpen_interior.vadd s.1
  apply interior_mono subset_closure
  rw [hopen.interior_eq]
  apply Set.mem_iUnion_of_mem ⟨t, htP⟩
  rw [mem_vadd_set]
  exact ⟨u, hu, rfl⟩

private theorem c04_eventually_sliceFiber_ae_univ
    {K : Region} {S : Set Tiling.Plane} (hTile : TilesOn K S univ)
    (axis : Axis) :
    ∀ᵐ q : ℝ ∂volume,
      {x : ℝ | slicePoint axis q x ∈ openUnion K S} =ᵐ[volume] univ := by
  have hplane : ∀ᵐ z : Tiling.Plane ∂volume, z ∈ openUnion K S := by
    filter_upwards [hTile.2.2] with z hz
    change z ∈ (Set.univ : Set Tiling.Plane) ↔ ∃ s : S,
      z ∈ (s.1 : Tiling.Plane) +ᵥ K.openCarrier at hz
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

private theorem c04_mem_closure_of_ae_univ
    {U : Set ℝ} (hU : U =ᵐ[volume] univ) (c : ℝ) :
    c ∈ closure U := by
  rw [mem_closure_iff]
  intro V hVopen hcV
  obtain ⟨r, hr, hVball⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hcV)
  let I : Set ℝ := Ioo (c - r / 2) (c + r / 2)
  have hI : volume I ≠ 0 := by
    rw [Real.volume_Ioo]
    simp [ENNReal.ofReal_eq_zero]
    linarith
  have haeU : ∀ᵐ x : ℝ ∂volume, x ∈ U :=
    hU.mono fun x hx ↦ hx.mpr (Set.mem_univ x)
  obtain ⟨x, hxI, hxU⟩ :=
    MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hI
      (haeU.filter_mono MeasureTheory.ae_restrict_le)
  refine ⟨x, hVball ?_, hxU⟩
  rw [Metric.mem_ball, Real.dist_eq]
  rw [abs_lt]
  constructor <;> linarith [hxI.1, hxI.2]

private def c04_translatedVertexLevels
    (K : Region) (S : Set Tiling.Plane) (axis : Axis) : Set ℝ :=
  Set.range fun p : S × K.vertices =>
    axis.transverseCoord ((p.1 : Tiling.Plane) + p.2.1)

private theorem c04_eventually_avoids_translatedVertexLevels
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) (axis : Axis) :
    ∀ᵐ q : ℝ ∂volume, q ∉ c04_translatedVertexLevels K S axis := by
  have hS : S.Countable := (IsPacking.locallyFinite_centres hpacking).2
  have hV : K.vertices.Countable := by
    rw [← K.coe_vertexFinset]
    exact K.vertexFinset.finite_toSet.countable
  let _ : Countable S := hS.to_subtype
  let _ : Countable K.vertices := hV.to_subtype
  exact (Set.countable_range _).ae_notMem volume

private theorem c04_filledChain_difference_integer
    {K : Region} {T : Set Tiling.Plane}
    (hInteger : ∀ v ∈ K.vertices, Tiling.RationalPolygonal.IsIntegerPoint v)
    {q : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ} {owner : Fin n → T}
    (hchain : IsFilledIndexedSliceChain K T Axis.horizontal q x owner) :
    ∃ z : ℤ, x (Fin.last n) - x 0 = z := by
  have hVertexRe : ∀ (v : K.vertices), ∃ z : ℤ, v.1.re = z := by
    intro v
    obtain ⟨z, hz⟩ :=
      Tiling.RationalPolygonal.mem_integerLattice_iff.mp
        (hInteger v.1 v.2)
    refine ⟨z 0, ?_⟩
    rw [← hz]
    exact Tiling.RationalPolygonal.integerPoint_re z
  obtain ⟨hmono, hsteps⟩ := hchain
  have hstep (i : Fin n) : ∃ z : ℤ,
      x i.succ - x i.castSucc = z := by
    obtain ⟨v, w, hv, hw, hleft, hright, _hpos, _hgap⟩ := hsteps i
    obtain ⟨zv, hzv⟩ := hVertexRe ⟨v, hv⟩
    obtain ⟨zw, hzw⟩ := hVertexRe ⟨w, hw⟩
    refine ⟨zw - zv, ?_⟩
    simp only [Axis.coord, Complex.add_re] at hleft hright
    rw [Int.cast_sub]
    linarith
  choose z hz using hstep
  have hsum : (∑ i : Fin n, (x i.succ - x i.castSucc)) =
      (∑ i : Fin n, (z i : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact hz i
  have htel_aux : ∀ (m : ℕ) (y : Fin (m + 1) → ℝ),
      (∑ i : Fin m, (y i.succ - y i.castSucc)) =
        y (Fin.last m) - y 0 := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
        intro y
        rw [Fin.sum_univ_succ]
        have htail := ih (fun i => y i.succ)
        have hlast : (Fin.last m).succ = Fin.last (m + 1) := by
          ext
          simp
        rw [hlast] at htail
        have htail' :
            (∑ i : Fin m, (y i.succ.succ - y i.succ.castSucc)) =
              y (Fin.last (m + 1)) - y 1 := by
          convert htail using 1 <;> simp
        simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
        rw [htail']
        ring
  have htel := htel_aux n x
  refine ⟨∑ i : Fin n, z i, ?_⟩
  rw [← htel, hsum, ← Int.cast_sum]

private theorem c04_filledChain_owner_eq_of_mem
    {K : Region} {T : Set Tiling.Plane} (hT : TilesOn K T univ)
    {q : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ} {owner : Fin n → ↥T}
    (hchain : IsFilledIndexedSliceChain K T Axis.horizontal q x owner)
    (i : Fin n) (t : ↥T) {z : Tiling.Plane}
    (hzi : z ∈ axisInterval Axis.horizontal (q : ℝ) (x i.castSucc) (x i.succ))
    (hzt : z ∈ (t : Tiling.Plane) +ᵥ K.openCarrier) : owner i = t := by
  by_contra hne
  have hd := (isPacking_iff_openCarrier_disjoint K T).mp hT.2.1
    (owner i).2 t.2 (fun h => hne (Subtype.ext h))
  obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 i
  exact Set.disjoint_left.mp hd (hinside hzi) hzt

private theorem c04_strictMono_exists_gap {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) {a : ℝ} (hleft : x 0 < a)
    (hright : a < x (Fin.last n)) (hne : ∀ k, a ≠ x k) :
    ∃ i : Fin n, a ∈ Ioo (x i.castSucc) (x i.succ) := by
  induction n with
  | zero => exfalso; simpa using (lt_asymm hleft hright)
  | succ n ih =>
      rcases lt_trichotomy a (x 1) with ha | ha | ha
      · exact ⟨⟨0, Nat.succ_pos _⟩, hleft, ha⟩
      · exact False.elim (hne 1 ha)
      · let y : Fin (n + 1) → ℝ := fun k => x k.succ
        have hy : StrictMono y := by
          intro i j hij
          apply hx
          simpa using hij
        have hylast : a < y (Fin.last n) := by
          simpa [y] using hright
        have hyne : ∀ k, a ≠ y k := fun k => hne k.succ
        obtain ⟨i, hi⟩ := ih y hy ha hylast hyne
        refine ⟨i.succ, ?_⟩
        simpa [y] using hi

private theorem totalPlateBoundary_nonempty
    : ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ¬ Subsingleton (VerticalPlate K T) →
      (⋃ P : VerticalPlate K T, frontier P.base).Nonempty := by
  intro K T hTile hNonSub
  have hcentres_subset (P : VerticalPlate K T) : P.centres ⊆ T := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hcentres_eq_of_support_eq_univ (P : VerticalPlate K T)
      (hfull : P.support = Set.univ) : P.centres = T := by
    apply Set.Subset.antisymm (hcentres_subset P)
    intro t htT
    by_contra htP
    obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have htuint : t + u ∈ interior (closure (openUnion K P.centres)) := by
      change t + u ∈ P.support
      rw [hfull]
      trivial
    have hopenTile : IsOpen (t +ᵥ K.openCarrier) := isOpen_interior.vadd t
    have hmeet :
        ((t +ᵥ K.openCarrier) ∩ openUnion K P.centres).Nonempty := by
      apply mem_closure_iff.mp (interior_subset htuint)
      · exact hopenTile
      · rw [mem_vadd_set]
        exact ⟨u, hu, rfl⟩
    obtain ⟨q, hqtile, hqraw⟩ := hmeet
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hqraw
    obtain ⟨s, hqs⟩ := hqraw
    have hst : (s : Tiling.Plane) ≠ t := by
      intro heq
      exact htP (heq ▸ s.2)
    have hdis := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp
      hTile.2.1 (hcentres_subset P s.2) htT hst
    exact Set.disjoint_left.mp hdis hqs hqtile
  have hslab (P : VerticalPlate K T) :
      P.base = interior (closure P.base) ∧
        P.support = Complex.re ⁻¹' P.base :=
    VerticalPlate.support_isVerticalSlab hTile P
  have hPQ : ∃ P Q : VerticalPlate K T, P ≠ Q := by
    by_contra h
    apply hNonSub
    constructor
    intro P Q
    by_contra hne
    exact h ⟨P, Q, hne⟩
  obtain ⟨P, Q, hPQ⟩ := hPQ
  have hproperP : P.base ≠ Set.univ := by
    intro hbase
    have hfull : P.support = Set.univ := by
      rw [hslab P |>.2, hbase]
      simp
    have hcentres : P.centres = T := hcentres_eq_of_support_eq_univ P hfull
    obtain ⟨q, hq⟩ := c04_verticalPlate_centres_nonempty Q
    obtain ⟨qT, hqT, rfl⟩ := hq
    have hqP : (qT : Tiling.Plane) ∈ P.centres := hcentres.symm ▸ qT.2
    obtain ⟨pT, hpT, hpEq⟩ := hqP
    have hpEq' : pT = qT := Subtype.ext hpEq
    subst qT
    exact hPQ (SimpleGraph.ConnectedComponent.eq_of_common_vertex hpT hqT)
  have hbaseNonempty := c04_verticalPlate_base_nonempty P
  have hfront : (frontier P.base).Nonempty := by
    exact nonempty_frontier_iff.mpr ⟨hbaseNonempty, hproperP⟩
  obtain ⟨c, hc⟩ := hfront
  exact ⟨c, Set.mem_iUnion_of_mem P hc⟩

private theorem plateBoundary_mem_horizontalSliceEndpoint
    : ∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T Set.univ →
      ∀ᵐ q : ℝ ∂volume, ∀ c : ℝ,
        c ∈ ⋃ P : VerticalPlate K T, frontier P.base →
          c ∈ sliceEndpointSet K T Axis.horizontal q := by
  intro K T hTile
  let _ : Countable T := hTile.1.to_subtype
  let _ : Countable (VerticalPlate K T) := by
    apply Function.Surjective.countable
      (f := fun t : T ↦ VerticalPlate.ofCentre (K := K) t)
    intro P
    obtain ⟨p, hp⟩ := P.nonempty_supp
    refine ⟨p, ?_⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff P p).1 hp
  have hslab (P : VerticalPlate K T) :
      P.base = interior (closure P.base) ∧
        P.support = Complex.re ⁻¹' P.base :=
    VerticalPlate.support_isVerticalSlab hTile P
  have hpartition := Tiling.AxisParallel.regularSupport_pairwiseDisjoint
    (@VerticalPlate.centres K T)
      (verticalPlateCentres_pairwiseDisjoint K T)
      (iUnion_verticalPlateCentres K T) hTile
  have hq := c04_eventually_sliceFiber_ae_univ hTile Axis.horizontal
  have hqAvoid := c04_eventually_avoids_translatedVertexLevels
    hTile.2.1 Axis.horizontal
  filter_upwards [hq, hqAvoid] with q hq _hqAvoid
  intro c hc
  obtain ⟨P₀, hcP₀⟩ := Set.mem_iUnion.mp hc
  let U : Set ℝ := {x : ℝ | slicePoint Axis.horizontal q x ∈ openUnion K T}
  have hUae : U =ᵐ[volume] univ := by simpa [U] using hq
  have hcClosure : c ∈ closure U := c04_mem_closure_of_ae_univ hUae c
  have hcNot : slicePoint Axis.horizontal q c ∉ openUnion K T := by
    intro hcU
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hcU
    obtain ⟨s, hs⟩ := hcU
    let Q : VerticalPlate K T := VerticalPlate.ofCentre s
    have hzQ : slicePoint Axis.horizontal q c ∈ Q.support := by
      change slicePoint Axis.horizontal q c ∈ regularSupport K Q.centres
      have hopen : IsOpen (openUnion K Q.centres) := by
        apply isOpen_iUnion
        intro t
        exact isOpen_interior.vadd t.1
      apply interior_mono subset_closure
      rw [hopen.interior_eq]
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      refine ⟨⟨s.1, VerticalPlate.mem_centres_ofCentre s⟩, ?_⟩
      exact hs
    have hcQ : c ∈ Q.base := by
      have hzQ' : slicePoint Axis.horizontal q c ∈ Complex.re ⁻¹' Q.base := by
        rw [← hslab Q |>.2]
        exact hzQ
      simpa [slicePoint] using hzQ'
    by_cases hQP : Q = P₀
    · exact (by
        subst P₀
        have hInt : c ∈ interior Q.base := by
          have hQopen : IsOpen Q.base := by
            rw [(hslab Q).1]
            exact isOpen_interior
          rw [hQopen.interior_eq]
          exact hcQ
        exact disjoint_interior_frontier.le_bot ⟨hInt, hcP₀⟩)
    · have hdisj := hpartition.1 (Set.mem_univ Q)
        (Set.mem_univ P₀) hQP
      have hPclosure : c ∈ closure P₀.base := frontier_subset_closure hcP₀
      have hQopen : IsOpen Q.base := by
        rw [(hslab Q).1]
        exact isOpen_interior
      obtain ⟨x, hxP, hxQ⟩ := mem_closure_iff.mp hPclosure
        Q.base hQopen hcQ
      have hzP : slicePoint Axis.horizontal q x ∈
          P₀.support := by
        rw [(hslab P₀).2]
        simpa [slicePoint] using hxQ
      have hzQ' : slicePoint Axis.horizontal q x ∈ Q.support := by
        rw [(hslab Q).2]
        simpa [slicePoint] using hxP
      exact Set.disjoint_left.mp hdisj hzQ' hzP
  have hcEndpoint : c ∈ frontier U := by
    rw [frontier]
    refine ⟨hcClosure, ?_⟩
    intro hcInt
    exact hcNot (by simpa [U] using interior_subset hcInt)
  simpa [sliceEndpointSet, U] using hcEndpoint

private theorem plateBoundaryCoordinates_mem_intCoset
    : ∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T Set.univ →
      (∀ v ∈ K.vertices, Tiling.RationalPolygonal.IsIntegerPoint v) →
      ¬ Subsingleton (VerticalPlate K T) →
      ∃ x₀ : ℝ, x₀ ∈ ⋃ P : VerticalPlate K T, frontier P.base ∧
        ⋃ P : VerticalPlate K T, frontier P.base ⊆
          {x : ℝ | ∃ n : ℤ, x = x₀ + n} := by
  intro K T hTile hInteger hNonSub
  obtain ⟨x₀, hx₀⟩ := totalPlateBoundary_nonempty hTile hNonSub
  have hBoundary := plateBoundary_mem_horizontalSliceEndpoint hTile
  have hChain :=
    genericSliceChain_betweenEndpoints_with_endpoints K T hTile Axis.horizontal
  obtain ⟨q, hq⟩ := (hBoundary.and hChain).exists
  obtain ⟨hBoundary, hChain⟩ := hq
  refine ⟨x₀, hx₀, ?_⟩
  intro c hc
  have hx₀e := hBoundary x₀ hx₀
  have hce := hBoundary c hc
  rcases lt_trichotomy x₀ c with hlt | heq | hgt
  · obtain ⟨n, _hn, x, _owner, hxfirst, hxlast, hfilled, _hendpoints⟩ :=
      hChain x₀ hx₀e c hce hlt
    obtain ⟨z, hz⟩ := c04_filledChain_difference_integer hInteger hfilled
    refine ⟨z, ?_⟩
    rw [hxlast, hxfirst] at hz
    linarith
  · refine ⟨0, ?_⟩
    rw [heq]
    ring
  · obtain ⟨n, _hn, x, _owner, hxfirst, hxlast, hfilled, _hendpoints⟩ :=
      hChain c hce x₀ hx₀e hgt
    obtain ⟨z, hz⟩ := c04_filledChain_difference_integer hInteger hfilled
    refine ⟨-z, ?_⟩
    rw [hxlast, hxfirst] at hz
    rw [Int.cast_neg]
    linarith

private theorem integralBoundaryDifference_of_filledChain
    : ∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T Set.univ →
      (∀ v ∈ K.vertices, Tiling.RationalPolygonal.IsIntegerPoint v) →
      ∀ a b : ℝ,
        a ∈ ⋃ P : VerticalPlate K T, frontier P.base →
        b ∈ ⋃ P : VerticalPlate K T, frontier P.base →
        ∃ n : ℤ, b - a = n := by
  intro K T hTile hInteger a b ha hb
  have hBoundary := plateBoundary_mem_horizontalSliceEndpoint hTile
  have hChain :=
    genericSliceChain_betweenEndpoints_with_endpoints K T hTile Axis.horizontal
  obtain ⟨q, hBoundary, hChain⟩ := (hBoundary.and hChain).exists
  have hae := hBoundary a ha
  have hbe := hBoundary b hb
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨n, _hn, x, _owner, hxfirst, hxlast, hfilled, _hendpoints⟩ :=
      hChain a hae b hbe hab
    obtain ⟨z, hz⟩ := c04_filledChain_difference_integer hInteger hfilled
    refine ⟨z, ?_⟩
    simpa [hxfirst, hxlast] using hz
  · refine ⟨0, ?_⟩
    simp [hab]
  · obtain ⟨n, _hn, x, _owner, hxfirst, hxlast, hfilled, _hendpoints⟩ :=
      hChain b hbe a hae hab
    obtain ⟨z, hz⟩ := c04_filledChain_difference_integer hInteger hfilled
    refine ⟨-z, ?_⟩
    rw [Int.cast_neg]
    rw [hxlast, hxfirst] at hz
    linarith

private theorem c04_im_eq_of_mem_openSegment_horizontal
    {a b p : Tiling.Plane} (hab : a.im = b.im)
    (hp : p ∈ openSegment ℝ a b) : p.im = a.im := by
  rw [openSegment_eq_image] at hp
  obtain ⟨r, _hr, rfl⟩ := hp
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rw [hab]
  ring





private theorem c04_mem_openSegment_sub_iff
    {a b t z : Tiling.Plane} :
    z ∈ openSegment ℝ (a - t) (b - t) ↔ z + t ∈ openSegment ℝ a b := by
  rw [show a = t +ᵥ (a - t) by simp [vadd_eq_add, sub_eq_add_neg],
    show b = t +ᵥ (b - t) by simp [vadd_eq_add, sub_eq_add_neg],
    ← vadd_openSegment ℝ]
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  constructor <;> intro h
  · simpa [add_assoc] using h
  · simpa [add_assoc] using h

private theorem c04_properHorizontalContact_imagDifference
    {K : Region} {T : Set Tiling.Plane} (t s : T)
    (_hts : t ≠ s) (hcontact : HorizontalProperContact K t.1 s.1) :
    ∃ a a' : K.vertices,
      ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).im = a.1.im - a'.1.im := by
  obtain ⟨c, d, hcd, hcdIm, hcontact⟩ := hcontact
  let p : Tiling.Plane := midpoint ℝ c d
  have hpCD : p ∈ openSegment ℝ c d := midpoint_mem_openSegment c d
  have hpContact := hcontact hpCD
  have hpTFrontier : p - t.1 ∈ frontier K.support :=
    by
      simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, neg_add_eq_sub] using hpContact.1.1
  have hpTNotVertex : p - t.1 ∉ K.vertices := by
    intro hpVertex
    apply hpContact.2
    left
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hpVertex
  have hpSFrontier : p - s.1 ∈ frontier K.support :=
    by
      simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, neg_add_eq_sub] using hpContact.1.2
  have hpSNotVertex : p - s.1 ∉ K.vertices := by
    intro hpVertex
    apply hpContact.2
    right
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hpVertex
  obtain ⟨axisT, a, b, hab, habCoord, hpAB, habEdge⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge
      K (p - t.1) hpTFrontier hpTNotVertex
  have habIm : a.1.im = b.1.im := by
    cases axisT with
    | horizontal => simpa [Axis.transverseCoord] using habCoord
    | vertical =>
        exfalso
        apply hpTNotVertex
        apply K.isPolygonal.mem_vertexSet_of_perpendicular_openSegments
          (c := c - t.1) (d := d - t.1) (p := p - t.1)
          (v := a.1) (w := b.1)
        · exact fun h ↦ hcd (sub_left_inj.mp h)
        · simp only [Complex.sub_im]; linarith
        · intro z hz
          have hzPlaced := c04_mem_openSegment_sub_iff.mp hz
          simpa [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
            vadd_eq_add, neg_add_eq_sub] using (hcontact hzPlaced).1.1
        · apply c04_mem_openSegment_sub_iff.mpr
          simpa using hpCD
        · exact hab
        · exact habCoord
        · exact hpAB
        · exact fun z hz ↦ (habEdge hz).1
  obtain ⟨axisS, a', b', ha'b', ha'b'Coord, hpA'B', ha'b'Edge⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge
      K (p - s.1) hpSFrontier hpSNotVertex
  have ha'b'Im : a'.1.im = b'.1.im := by
    cases axisS with
    | horizontal => simpa [Axis.transverseCoord] using ha'b'Coord
    | vertical =>
        exfalso
        apply hpSNotVertex
        apply K.isPolygonal.mem_vertexSet_of_perpendicular_openSegments
          (c := c - s.1) (d := d - s.1) (p := p - s.1)
          (v := a'.1) (w := b'.1)
        · exact fun h ↦ hcd (sub_left_inj.mp h)
        · simp only [Complex.sub_im]; linarith
        · intro z hz
          have hzPlaced := c04_mem_openSegment_sub_iff.mp hz
          simpa [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
            vadd_eq_add, neg_add_eq_sub] using (hcontact hzPlaced).1.2
        · apply c04_mem_openSegment_sub_iff.mpr
          simpa using hpCD
        · exact ha'b'
        · exact ha'b'Coord
        · exact hpA'B'
        · exact fun z hz ↦ (ha'b'Edge hz).1
  refine ⟨a, a', ?_⟩
  have hpIm := c04_im_eq_of_mem_openSegment_horizontal hcdIm hpCD
  have hpTIm := c04_im_eq_of_mem_openSegment_horizontal habIm hpAB
  have hpSIm := c04_im_eq_of_mem_openSegment_horizontal ha'b'Im hpA'B'
  simp only [Complex.sub_im] at hpTIm hpSIm ⊢
  linarith

private theorem plateSecondCoordinates_mem_intCoset :
    ∀ {K : Region} {T : Set Tiling.Plane},
      (∀ v ∈ K.vertices, Tiling.RationalPolygonal.IsIntegerPoint v) →
      ∀ P : VerticalPlate K T, ∃ theta : ℝ,
        ∀ t ∈ P.centres, ∃ n : ℤ, t.im = theta + n := by
  intro K T hInteger P
  have hVertexImag : ∀ (v : K.vertices), ∃ n : ℤ, v.1.im = n := by
    intro v
    obtain ⟨z, hz⟩ :=
      Tiling.RationalPolygonal.mem_integerLattice_iff.mp
        (hInteger v.1 v.2)
    refine ⟨z 1, ?_⟩
    rw [← hz]
    exact Tiling.RationalPolygonal.integerPoint_im z
  have hAdj : ∀ {u v : T},
      (verticalPlateGraph K T).Adj u v →
        ∃ n : ℤ, v.1.im = u.1.im + n := by
    intro u v huv
    obtain ⟨huv_ne, hcontact⟩ := (verticalPlateGraph_adj_iff u v).mp huv
    obtain ⟨a, a', hdiff⟩ :=
      c04_properHorizontalContact_imagDifference u v huv_ne hcontact
    obtain ⟨m, hm⟩ := hVertexImag a
    obtain ⟨m', hm'⟩ := hVertexImag a'
    refine ⟨m - m', ?_⟩
    rw [Complex.sub_im] at hdiff
    rw [hm, hm'] at hdiff
    rw [Int.cast_sub]
    linarith
  have hWalk : ∀ {u v : T} (p : (verticalPlateGraph K T).Walk u v),
      ∃ n : ℤ, v.1.im = u.1.im + n := by
    intro u v p
    induction p with
    | nil => exact ⟨0, by simp⟩
    | @cons u v w huv p ih =>
        obtain ⟨m, hm⟩ := hAdj huv
        obtain ⟨n, hn⟩ := ih
        refine ⟨m + n, ?_⟩
        rw [hn, hm, Int.cast_add]
        ring
  obtain ⟨u, hu⟩ := P.nonempty_supp
  refine ⟨u.1.im, ?_⟩
  intro t ht
  obtain ⟨v, hv, rfl⟩ := ht
  obtain ⟨p⟩ := P.reachable_of_mem_supp hu hv
  exact hWalk p

private theorem exists_mem_open_of_ae_local {U : Set Tiling.Plane}
    {P : Tiling.Plane → Prop} (hU : IsOpen U) (hUne : U.Nonempty)
    (hP : ∀ᵐ z ∂volume, P z) : ∃ z ∈ U, P z := by
  have hμ : volume.restrict U ≠ 0 := by
    intro hz
    have hzero : volume U = 0 := by
      rw [← Measure.restrict_apply_univ U, hz]
      simp
    exact hU.measure_ne_zero volume hUne hzero
  let hne : (ae (volume.restrict U)).NeBot := ae_neBot.mpr hμ
  have hP' : ∀ᵐ z ∂volume.restrict U, P z := hP.filter_mono ae_restrict_le
  rcases @Filter.Eventually.exists Tiling.Plane _ (ae (volume.restrict U)) hne
      (hP'.and (ae_restrict_mem hU.measurableSet)) with ⟨z, hzP, hzU⟩
  exact ⟨z, hzU, hzP⟩

private theorem meshCell_union_finset_eq_of_ae_eq
    {F G : Finset TranslationalTilings.Plane}
    (hFG : (⋃ f : F, meshCell 1 (f : TranslationalTilings.Plane)) =ᵐ[volume]
      ⋃ g : G, meshCell 1 (g : TranslationalTilings.Plane)) :
    (F : Set TranslationalTilings.Plane) = G := by
  ext f
  constructor
  · intro hf
    have hopen : IsOpen (meshCell 1 (f : TranslationalTilings.Plane)) := by
      simp only [meshCell]
      exact (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          ((isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const)))
    have hne : (meshCell 1 (f : TranslationalTilings.Plane)).Nonempty :=
      meshCell_nonempty (by simp) _
    obtain ⟨x, hxf, hxgood⟩ := exists_mem_open_of_ae_local hopen hne hFG
    have hxG : x ∈ ⋃ g : G, meshCell 1 (g : TranslationalTilings.Plane) :=
      by
        change (⋃ g : G, meshCell 1 (g : TranslationalTilings.Plane)) x
        rw [← hxgood]
        exact Set.mem_iUnion_of_mem ⟨f, hf⟩ hxf
    rcases Set.mem_iUnion.mp hxG with ⟨g, hxg⟩
    by_contra hnefg
    have hdisj : Disjoint (meshCell 1 (f : TranslationalTilings.Plane))
        (meshCell 1 (g : TranslationalTilings.Plane)) := by
      refine meshCell_pairwiseDisjoint (d := 1) (by simp)
        (Set.mem_univ f) (Set.mem_univ g) ?_
      intro hfg
      apply hnefg
      exact hfg ▸ g.property
    exact Set.disjoint_left.mp hdisj hxf hxg
  · intro hg
    have hopen : IsOpen (meshCell 1 (f : TranslationalTilings.Plane)) := by
      simp only [meshCell]
      exact (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          ((isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const)))
    have hne : (meshCell 1 (f : TranslationalTilings.Plane)).Nonempty :=
      meshCell_nonempty (by simp) _
    obtain ⟨x, hxf, hxgood⟩ := exists_mem_open_of_ae_local hopen hne hFG.symm
    have hxF : x ∈ ⋃ f : F, meshCell 1 (f : TranslationalTilings.Plane) :=
      by
        change (⋃ f : F, meshCell 1 (f : TranslationalTilings.Plane)) x
        rw [← hxgood]
        exact Set.mem_iUnion_of_mem ⟨f, hg⟩ hxf
    rcases Set.mem_iUnion.mp hxF with ⟨f', hxf'⟩
    by_contra hnefg
    have hdisj : Disjoint (meshCell 1 (f : TranslationalTilings.Plane))
        (meshCell 1 (f' : TranslationalTilings.Plane)) := by
      refine meshCell_pairwiseDisjoint (d := 1) (by simp)
        (Set.mem_univ f) (Set.mem_univ f') ?_
      intro hfg
      apply hnefg
      exact hfg ▸ f'.property
    exact Set.disjoint_left.mp hdisj hxf hxf'

private theorem integerRegion_discreteTile_eq_raster
    {K : Region} {T : Set Tiling.Plane}
    (I : PlateCompatibleIntegerization K T) :
    (I.discreteTile : Set TranslationalTilings.Plane) =
      rasterCells 1 I.integerRegion.openCarrier := by
  have hmesh : OnRationalMesh 1 I.integerRegion.vertices := by
    intro v hv
    obtain ⟨z, hz⟩ := mem_integerLattice_iff.mp (I.integerVertices v hv)
    refine ⟨z, ?_⟩
    apply Complex.ext
    · simpa [rationalScale, integerPoint] using congrArg Complex.re hz
    · simpa [rationalScale, integerPoint] using congrArg Complex.im hz
  obtain ⟨F, hFne, hFraster, hae, _hreg⟩ :=
    exists_regionRaster (K := I.integerRegion) (d := 1) (by simp) hmesh
  have hcell (z : TranslationalTilings.Plane) :
      meshCell 1 z = integerPoint z +ᵥ interior (Complex.Rectangle 0 (1 + Complex.I)) := by
    have hunit : interior (Complex.Rectangle 0 (1 + Complex.I)) =
        {w : Tiling.Plane | 0 < w.re ∧ w.re < 1 ∧ 0 < w.im ∧ w.im < 1} := by
      have hrect : Complex.Rectangle 0 (1 + Complex.I) = Icc 0 1 ×ℂ Icc 0 1 := by
        ext w
        simp [Complex.Rectangle]
      rw [hrect, Complex.interior_reProdIm]
      ext w
      change (w.re ∈ interior (Icc 0 1) ∧ w.im ∈ interior (Icc 0 1)) ↔ _
      simp [interior_Icc]
      tauto
    ext x
    rw [hunit]
    simp [meshCell, rationalScale, integerPoint,
      Set.mem_vadd_set_iff_neg_vadd_mem]
  have hIae : I.integerRegion.openCarrier =ᵐ[volume]
      ⋃ f : I.discreteTile, meshCell 1 (f : TranslationalTilings.Plane) := by
    have hunionI : (⋃ f : I.discreteTile, meshCell 1 (f : TranslationalTilings.Plane)) =
        ⋃ f : I.discreteTile,
          integerPoint (f : TranslationalTilings.Plane) +ᵥ
            interior (Complex.Rectangle 0 (1 + Complex.I)) := by
      apply iUnion_congr
      intro f
      exact hcell f
    filter_upwards [I.discreteTile_realizes_integerRegion] with x hx
    rw [hunionI]
    exact hx
  have hFae : I.integerRegion.openCarrier =ᵐ[volume]
      ⋃ f : F, meshCell 1 (f : TranslationalTilings.Plane) := by
    exact hae
  have hEq := meshCell_union_finset_eq_of_ae_eq (hIae.symm.trans hFae)
  rw [hEq, hFraster]

private theorem regularSupport_eq_regularizedCellUnion
    {K : Region} {T : Set Tiling.Plane}
    (I : PlateCompatibleIntegerization K T)
    {S : Set TranslationalTilings.Plane} :
    regularSupport I.integerRegion (integerPoint '' S) =
      regularizedCellUnion 1 (discreteCarrier I.discreteTile S) := by
  have hmesh : OnRationalMesh 1 I.integerRegion.vertices := by
    intro v hv
    obtain ⟨z, hz⟩ := mem_integerLattice_iff.mp (I.integerVertices v hv)
    refine ⟨z, ?_⟩
    apply Complex.ext
    · simpa [rationalScale, integerPoint] using congrArg Complex.re hz
    · simpa [rationalScale, integerPoint] using congrArg Complex.im hz
  obtain ⟨F, -, hFraster, -, -⟩ :=
    exists_regionRaster (K := I.integerRegion) (d := 1) (by simp) hmesh
  have hEq : (I.discreteTile : Set TranslationalTilings.Plane) = F := by
    exact (integerRegion_discreteTile_eq_raster I).trans hFraster.symm
  have himage : rationalScale 1 '' S = integerPoint '' S := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s, hs, ?_⟩
      apply Complex.ext <;> simp [rationalScale, integerPoint]
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s, hs, ?_⟩
      apply Complex.ext <;> simp [rationalScale, integerPoint]
  calc
    regularSupport I.integerRegion (integerPoint '' S) =
        regularSupport I.integerRegion (rationalScale 1 '' S) := by rw [himage]
    _ = regularizedCellUnion 1 (discreteCarrier F S) :=
      regularSupport_rationalScale_image (by simp) hmesh F hFraster S
    _ = regularizedCellUnion 1 (discreteCarrier I.discreteTile S) := by
      have hFin : I.discreteTile = F := Finset.coe_injective hEq
      subst F
      rfl

private theorem discretePeriod_regularizedCellUnion
    {A : Set TranslationalTilings.Plane} {L : ℕ}
    (hperiod : TranslationalTilings.SetScalarPeriodic L A) :
    SetPeriodicBy (regularizedCellUnion 1 A) (L : ℂ) := by
  let e₀ : TranslationalTilings.Plane := ![1, 0]
  let U : Set Tiling.Plane := ⋃ q : A, meshCell 1 q.1
  have hUperiod (z : Tiling.Plane) : z + (L : ℂ) ∈ U ↔ z ∈ U := by
    constructor
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨q, hq⟩
      let q' : TranslationalTilings.Plane := q.1 - (L : ℤ) • e₀
      have hqshift : q' + (L : ℤ) • e₀ = q.1 := by
        dsimp [q', e₀]
        ext i
        fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, Pi.add_apply]
      have hq'A : q' ∈ A := by
        apply (hperiod q' e₀).mp
        rw [hqshift]
        exact q.2
      refine Set.mem_iUnion.mpr ⟨⟨q', hq'A⟩, ?_⟩
      have hcell := meshCell_add (d := 1) (by simp)
        q' ((L : ℤ) • e₀)
      have hscalar : rationalScale 1 ((L : ℤ) • e₀) = (L : ℂ) := by
        apply Complex.ext <;> simp [rationalScale, e₀]
      rw [← hqshift] at hq
      rw [hcell] at hq
      rw [hscalar] at hq
      change z ∈ meshCell 1 q'
      simpa [e₀, rationalScale, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        add_comm, add_left_comm, add_assoc] using hq
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨q, hq⟩
      let q' : TranslationalTilings.Plane := q.1 + (L : ℤ) • e₀
      have hqshift : q.1 + (L : ℤ) • e₀ = q' := by rfl
      have hq'A : q' ∈ A := by
        rw [← hqshift]
        exact (hperiod q.1 e₀).mpr q.2
      refine Set.mem_iUnion.mpr ⟨⟨q', hq'A⟩, ?_⟩
      have hcell := meshCell_add (d := 1) (by simp)
        q.1 ((L : ℤ) • e₀)
      have hscalar : rationalScale 1 ((L : ℤ) • e₀) = (L : ℂ) := by
        apply Complex.ext <;> simp [rationalScale, e₀]
      change z + (L : ℂ) ∈ meshCell 1 q'
      rw [← hqshift, hcell]
      rw [hscalar]
      simpa [e₀, rationalScale, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        add_comm, add_left_comm, add_assoc] using hq
  have hUshift : ((L : ℂ) +ᵥ U) = U := by
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using (hUperiod (z - (L : ℂ))).symm
  have hRshift : ((L : ℂ) +ᵥ regularizedCellUnion 1 A) =
      regularizedCellUnion 1 A := by
    change ((L : ℂ) +ᵥ interior (closure U)) = interior (closure U)
    calc
      (L : ℂ) +ᵥ interior (closure U) = interior ((L : ℂ) +ᵥ closure U) := by
        rw [interior_vadd]
      _ = interior (closure ((L : ℂ) +ᵥ U)) := by rw [closure_vadd]
      _ = interior (closure U) := by rw [hUshift]
  intro z
  simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using
    (Set.ext_iff.mp hRshift (z + (L : ℂ))).symm

private theorem affine_period_pullback
    {R S : Set Tiling.Plane} {L : ℕ} {s c : ℝ}
    (hs : 0 < s)
    (hR : R = (s : ℝ) • (((c : ℝ) : ℂ) +ᵥ S))
    (hRperiod : Tiling.RationalPolygonal.SetPeriodicBy R (L : ℂ)) :
    Tiling.RationalPolygonal.SetPeriodicBy S
      ((((L : ℝ) / s : ℝ) : ℂ)) := by
  have hs0 : (s : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hs)
  have hmap (y : Tiling.Plane) :
      (s : ℝ) • (((c : ℝ) : ℂ) + y) ∈ R ↔ y ∈ S := by
    constructor
    · intro hy
      rw [hR] at hy
      rcases Set.mem_smul_set.mp hy with ⟨z, hz, hzy⟩
      have hzv : z = (((c : ℝ) : ℂ) + y) :=
        (smul_right_injective ℂ hs0) hzy
      rcases Set.mem_vadd_set.mp hz with ⟨y', hy', hyy'⟩
      have hyy : y' = y := by
        apply add_left_cancel
        calc
          ((c : ℝ) : ℂ) + y' = z := by simpa [vadd_eq_add] using hyy'
          _ = ((c : ℝ) : ℂ) + y := hzv
      simpa [hyy] using hy'
    · intro hy
      rw [hR]
      refine Set.mem_smul_set.mpr ⟨((c : ℝ) : ℂ) + y, ?_, rfl⟩
      exact Set.mem_vadd_set.mpr ⟨y, hy, rfl⟩
  intro x
  have hp := hRperiod ((s : ℝ) • (((c : ℝ) : ℂ) + x))
  have hscalar :
      (s : ℝ) • ((((L : ℝ) / s : ℝ) : ℂ)) = (L : ℂ) := by
    apply Complex.ext
    · norm_num [smul_eq_mul]
      field_simp
    · norm_num [smul_eq_mul]
  have hshift :
      (s : ℝ) • (((c : ℝ) : ℂ) +
          (x + ((((L : ℝ) / s : ℝ) : ℂ)))) =
        (s : ℝ) • (((c : ℝ) : ℂ) + x) + (L : ℂ) := by
    rw [← add_assoc, smul_add, hscalar]
  rw [← hshift] at hp
  rw [hmap, hmap] at hp
  exact hp

theorem discreteSupportPeriod_liftsContinuousSupportPeriod
    {K : Region} {T : Set Tiling.Plane}
    (I : PlateCompatibleIntegerization K T) (P : VerticalPlate K T)
    {L : ℕ} : 0 < L →
    TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier I.discreteTile
        (Tiling.RationalPolygonal.quakePlateTranslations (I.plateEquiv P))) →
    Tiling.RationalPolygonal.SetPeriodicBy P.support
      ((((L : ℝ) / I.scale : ℝ) : ℂ)) := by
  intro hL hperiod
  have hs : (0 : ℝ) < (I.scale : ℝ) := by exact_mod_cast I.scale_pos
  apply affine_period_pullback hs
    (I.carrier_eq P)
  have hreg := regularSupport_eq_regularizedCellUnion I
    (S := Tiling.RationalPolygonal.quakePlateTranslations (I.plateEquiv P))
  rw [hreg]
  exact discretePeriod_regularizedCellUnion hperiod

theorem discreteColumnSupportPeriod_liftsContinuousColumnSupportPeriod
    {K : Region} {T : Set Tiling.Plane}
    (I : PlateCompatibleIntegerization K T) {L : ℕ} : 0 < L →
    TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier I.discreteTile
        (Tiling.AxisParallel.Discrete.discreteColumnUnion
          I.discreteTile I.discreteCentres)) →
    Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K (verticalColumnCentres K T))
      ((((L : ℝ) / I.scale : ℝ) : ℂ)) := by
  intro hL hperiod
  have hs : (0 : ℝ) < (I.scale : ℝ) := by exact_mod_cast I.scale_pos
  apply affine_period_pullback hs
    I.columnAggregate_carrier_eq
  have hreg := regularSupport_eq_regularizedCellUnion I
    (S := Tiling.AxisParallel.Discrete.discreteColumnUnion
      I.discreteTile I.discreteCentres)
  rw [hreg]
  exact discretePeriod_regularizedCellUnion hperiod

theorem discreteCentrePeriod_liftsContinuousCentrePeriod
    {K : Region} {T : Set Tiling.Plane}
    (I : PlateCompatibleIntegerization K T) (P : VerticalPlate K T)
    {L : ℕ} : 0 < L →
    Tiling.RationalPolygonal.DiscretePeriodicBy
      (Tiling.RationalPolygonal.quakePlateTranslations (I.plateEquiv P))
      (![(L : ℤ), 0] : TranslationalTilings.Plane) →
    Tiling.RationalPolygonal.SetPeriodicBy P.centres
      ((((L : ℝ) / I.scale : ℝ) : ℂ)) := by
  intro hL hperiod x
  let w : TranslationalTilings.Plane := ![(L : ℤ), 0]
  have hw : Tiling.RationalPolygonal.integerPoint w = (L : ℂ) := by
    apply Complex.ext <;> simp [w, Tiling.RationalPolygonal.integerPoint]
  have hscale : (I.scale : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt I.scale_pos)
  have hformula (t : T) :
      Tiling.RationalPolygonal.integerPoint (I.centreEquiv t) =
        (I.scale : ℝ) •
            ((t : Tiling.Plane) + I.tileAnchor +
              (((I.commonHorizontalShift : ℝ) : ℂ))) +
          (((I.plateVerticalShift (VerticalPlate.ofCentre t) : ℝ) : ℂ) *
            Complex.I) :=
    I.centreEquiv_apply t
  constructor
  · intro hx
    obtain ⟨t', ht', htx⟩ := hx
    have ht'cent : (t' : Tiling.Plane) ∈ P.centres := ⟨t', ht', rfl⟩
    have hmem' :
        ((I.centreEquiv t' : I.discreteCentres) : TranslationalTilings.Plane) ∈
          Tiling.RationalPolygonal.quakePlateTranslations (I.plateEquiv P) :=
      (I.centreEquiv_mem_plate P t').mp ht'cent
    let a' : TranslationalTilings.Plane := I.centreEquiv t'
    let a : TranslationalTilings.Plane := a' - w
    have hmem : a ∈
        Tiling.RationalPolygonal.quakePlateTranslations (I.plateEquiv P) := by
      apply (hperiod (a' - w)).mp
      change a' - w + w ∈ _
      simpa [a, a'] using hmem'
    obtain ⟨haT, haP⟩ := hmem
    let t : T := I.centreEquiv.symm ⟨a, haT⟩
    have hct : I.centreEquiv t = (⟨a, haT⟩ : I.discreteCentres) := by
      exact I.centreEquiv.apply_symm_apply _
    have htmem : (t : Tiling.Plane) ∈ P.centres := by
      apply (I.centreEquiv_mem_plate P t).mpr
      rw [hct]
      exact ⟨haT, haP⟩
    have hplate_t : VerticalPlate.ofCentre t = P := by
      rcases htmem with ⟨u, hu, huv⟩
      have hut : u = t := Subtype.ext huv
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff P t).mp (by simpa [hut] using hu)
    have hplate_t' : VerticalPlate.ofCentre t' = P := by
      rcases ht'cent with ⟨u, hu, huv⟩
      have hut : u = t' := Subtype.ext huv
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff P t').mp (by simpa [hut] using hu)
    have haformula := hformula t
    have hapformula := hformula t'
    have hkey :
        Tiling.RationalPolygonal.integerPoint (I.centreEquiv t) =
          Tiling.RationalPolygonal.integerPoint (I.centreEquiv t') -
            Tiling.RationalPolygonal.integerPoint w := by
      rw [hct]
      dsimp [a, a']
      rw [Tiling.RationalPolygonal.integerPoint_sub]
    have hkeyformula :
        (I.scale : ℝ) •
            ((t : Tiling.Plane) + I.tileAnchor +
              (((I.commonHorizontalShift : ℝ) : ℂ))) +
          (((I.plateVerticalShift (VerticalPlate.ofCentre t) : ℝ) : ℂ) *
            Complex.I) =
        ((I.scale : ℝ) •
            ((t' : Tiling.Plane) + I.tileAnchor +
              (((I.commonHorizontalShift : ℝ) : ℂ))) +
          (((I.plateVerticalShift (VerticalPlate.ofCentre t') : ℝ) : ℂ) *
            Complex.I)) - (L : ℂ) := by
      calc
        _ = Tiling.RationalPolygonal.integerPoint (I.centreEquiv t) := haformula.symm
        _ = Tiling.RationalPolygonal.integerPoint (I.centreEquiv t') -
              Tiling.RationalPolygonal.integerPoint w := hkey
        _ = _ := by rw [hapformula, hw]
    have hta : (t : Tiling.Plane) = x := by
      have hshift : I.plateVerticalShift (VerticalPlate.ofCentre t) =
          I.plateVerticalShift (VerticalPlate.ofCentre t') := by rw [hplate_t, hplate_t']
      apply Complex.ext
      · have hre := congrArg Complex.re hkeyformula
        have htx' := congrArg Complex.re htx
        norm_num [hshift, Complex.add_re, Complex.smul_re, smul_eq_mul,
          Complex.sub_re] at hre htx' ⊢
        rw [htx'] at hre
        field_simp [hscale] at hre
        have hspos : 0 < (I.scale : ℝ) := by exact_mod_cast I.scale_pos
        nlinarith
      · have him := congrArg Complex.im hkeyformula
        have htx' := congrArg Complex.im htx
        norm_num [hshift, Complex.add_im, Complex.smul_im, smul_eq_mul,
          Complex.sub_im] at him htx' ⊢
        rw [htx'] at him
        rcases him with him | hzero
        · exact him
        · have hzero' : (I.scale : ℝ) = 0 := by exact_mod_cast hzero
          exact (hscale hzero').elim
    rw [← hta]
    exact htmem
  · intro hx
    obtain ⟨t, ht, htx⟩ := hx
    have htcent : (t : Tiling.Plane) ∈ P.centres := ⟨t, ht, rfl⟩
    have hmem :
        ((I.centreEquiv t : I.discreteCentres) : TranslationalTilings.Plane) ∈
          Tiling.RationalPolygonal.quakePlateTranslations (I.plateEquiv P) :=
      (I.centreEquiv_mem_plate P t).mp htcent
    let a : TranslationalTilings.Plane := I.centreEquiv t
    let a' : TranslationalTilings.Plane := a + w
    have hmem' : a' ∈
        Tiling.RationalPolygonal.quakePlateTranslations (I.plateEquiv P) := by
      change a + w ∈ _
      exact (hperiod a).mpr (by simpa [a] using hmem)
    obtain ⟨haT, haP⟩ := hmem'
    let t' : T := I.centreEquiv.symm ⟨a', haT⟩
    have hct' : I.centreEquiv t' = (⟨a', haT⟩ : I.discreteCentres) := by
      exact I.centreEquiv.apply_symm_apply _
    have ht'mem : (t' : Tiling.Plane) ∈ P.centres := by
      apply (I.centreEquiv_mem_plate P t').mpr
      rw [hct']
      exact ⟨haT, haP⟩
    have hplate_t : VerticalPlate.ofCentre t = P := by
      rcases htcent with ⟨u, hu, huv⟩
      have hut : u = t := Subtype.ext huv
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff P t).mp (by simpa [hut] using hu)
    have hplate_t' : VerticalPlate.ofCentre t' = P := by
      rcases ht'mem with ⟨u, hu, huv⟩
      have hut : u = t' := Subtype.ext huv
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff P t').mp (by simpa [hut] using hu)
    have haformula := hformula t
    have hapformula := hformula t'
    have hkey :
        Tiling.RationalPolygonal.integerPoint (I.centreEquiv t') =
          Tiling.RationalPolygonal.integerPoint (I.centreEquiv t) +
            Tiling.RationalPolygonal.integerPoint w := by
      rw [hct']
      dsimp [a, a']
      rw [Tiling.RationalPolygonal.integerPoint_add]
    have hkeyformula :
        (I.scale : ℝ) •
            ((t' : Tiling.Plane) + I.tileAnchor +
              (((I.commonHorizontalShift : ℝ) : ℂ))) +
          (((I.plateVerticalShift (VerticalPlate.ofCentre t') : ℝ) : ℂ) *
            Complex.I) =
        ((I.scale : ℝ) •
            ((t : Tiling.Plane) + I.tileAnchor +
              (((I.commonHorizontalShift : ℝ) : ℂ))) +
          (((I.plateVerticalShift (VerticalPlate.ofCentre t) : ℝ) : ℂ) *
            Complex.I)) + (L : ℂ) := by
      calc
        _ = Tiling.RationalPolygonal.integerPoint (I.centreEquiv t') := hapformula.symm
        _ = Tiling.RationalPolygonal.integerPoint (I.centreEquiv t) +
              Tiling.RationalPolygonal.integerPoint w := hkey
        _ = _ := by rw [haformula, hw]
    have hta : (t' : Tiling.Plane) = x + ((((L : ℝ) / I.scale : ℝ) : ℂ)) := by
      have hshift : I.plateVerticalShift (VerticalPlate.ofCentre t) =
          I.plateVerticalShift (VerticalPlate.ofCentre t') := by rw [hplate_t, hplate_t']
      apply Complex.ext
      · have hre := congrArg Complex.re hkeyformula
        have htx' := congrArg Complex.re htx
        norm_num [hshift, Complex.add_re, Complex.smul_re, smul_eq_mul,
          Complex.sub_re] at hre htx' ⊢
        rw [htx'] at hre
        have hspos : 0 < (I.scale : ℝ) := by exact_mod_cast I.scale_pos
        field_simp [hscale] at ⊢
        nlinarith
      · have him := congrArg Complex.im hkeyformula
        have htx' := congrArg Complex.im htx
        norm_num [hshift, Complex.add_im, Complex.smul_im, smul_eq_mul,
          Complex.sub_im] at him htx' ⊢
        rw [htx'] at him
        rcases him with him | hzero
        · exact him
        · have hzero' : (I.scale : ℝ) = 0 := by exact_mod_cast hzero
          exact (hscale hzero').elim
    rw [← hta]
    exact ht'mem


private theorem c04_plateBoundary_mem_horizontalSliceEndpoint
    : ∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T Set.univ →
      ∀ᵐ q : ℝ ∂volume, ∀ c : ℝ,
        c ∈ ⋃ P : VerticalPlate K T, frontier P.base →
          c ∈ sliceEndpointSet K T Axis.horizontal q := by
  intro K T hTile
  let _ : Countable T := hTile.1.to_subtype
  let _ : Countable (VerticalPlate K T) := by
    apply Function.Surjective.countable
      (f := fun t : T ↦ VerticalPlate.ofCentre (K := K) t)
    intro P
    obtain ⟨p, hp⟩ := P.nonempty_supp
    refine ⟨p, ?_⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff P p).1 hp
  have hslab (P : VerticalPlate K T) :
      P.base = interior (closure P.base) ∧
        P.support = Complex.re ⁻¹' P.base :=
    VerticalPlate.support_isVerticalSlab hTile P
  have hpartition := Tiling.AxisParallel.regularSupport_pairwiseDisjoint
    (@VerticalPlate.centres K T)
      (verticalPlateCentres_pairwiseDisjoint K T)
      (iUnion_verticalPlateCentres K T) hTile
  have hq := c04_eventually_sliceFiber_ae_univ hTile Axis.horizontal
  have hqAvoid := c04_eventually_avoids_translatedVertexLevels
    hTile.2.1 Axis.horizontal
  filter_upwards [hq, hqAvoid] with q hq _hqAvoid
  intro c hc
  obtain ⟨P₀, hcP₀⟩ := Set.mem_iUnion.mp hc
  let U : Set ℝ := {x : ℝ | slicePoint Axis.horizontal q x ∈ openUnion K T}
  have hUae : U =ᵐ[volume] univ := by simpa [U] using hq
  have hcClosure : c ∈ closure U := c04_mem_closure_of_ae_univ hUae c
  have hcNot : slicePoint Axis.horizontal q c ∉ openUnion K T := by
    intro hcU
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hcU
    obtain ⟨s, hs⟩ := hcU
    let Q : VerticalPlate K T := VerticalPlate.ofCentre s
    have hzQ : slicePoint Axis.horizontal q c ∈ Q.support := by
      change slicePoint Axis.horizontal q c ∈ regularSupport K Q.centres
      have hopen : IsOpen (openUnion K Q.centres) := by
        apply isOpen_iUnion
        intro t
        exact isOpen_interior.vadd t.1
      apply interior_mono subset_closure
      rw [hopen.interior_eq]
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      refine ⟨⟨s.1, VerticalPlate.mem_centres_ofCentre s⟩, ?_⟩
      exact hs
    have hcQ : c ∈ Q.base := by
      have hzQ' : slicePoint Axis.horizontal q c ∈ Complex.re ⁻¹' Q.base := by
        rw [← hslab Q |>.2]
        exact hzQ
      simpa [slicePoint] using hzQ'
    by_cases hQP : Q = P₀
    · subst P₀
      have hInt : c ∈ interior Q.base := by
        have hQopen : IsOpen Q.base := by
          rw [(hslab Q).1]
          exact isOpen_interior
        rw [hQopen.interior_eq]
        exact hcQ
      exact (disjoint_interior_frontier.le_bot ⟨hInt, hcP₀⟩)
    · have hdisj := hpartition.1 (Set.mem_univ Q)
        (Set.mem_univ P₀) hQP
      have hPclosure : c ∈ closure P₀.base := frontier_subset_closure hcP₀
      have hQopen : IsOpen Q.base := by
        rw [(hslab Q).1]
        exact isOpen_interior
      obtain ⟨x, hxP, hxQ⟩ := mem_closure_iff.mp hPclosure
        Q.base hQopen hcQ
      have hzP : slicePoint Axis.horizontal q x ∈ P₀.support := by
        rw [(hslab P₀).2]
        simpa [slicePoint] using hxQ
      have hzQ' : slicePoint Axis.horizontal q x ∈ Q.support := by
        rw [(hslab Q).2]
        simpa [slicePoint] using hxP
      exact Set.disjoint_left.mp hdisj hzQ' hzP
  have hcEndpoint : c ∈ frontier U := by
    rw [frontier]
    refine ⟨hcClosure, ?_⟩
    intro hcInt
    exact hcNot (by simpa [U] using interior_subset hcInt)
  simpa [sliceEndpointSet, U] using hcEndpoint

private theorem centreOwnedGapInEndpointChain
    : ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ¬ Subsingleton (VerticalPlate K T) → ∀ t : ↥T,
    ∃ c ∈ ⋃ P : VerticalPlate K T, frontier P.base,
      ∃ d q : ℝ, ∃ (n : ℕ) (x : Fin (n + 1) → ℝ)
      (owner : Fin n → ↥T) (i : Fin n),
      c ∈ sliceEndpointSet K T Axis.horizontal q ∧
      d ∈ sliceEndpointSet K T Axis.horizontal q ∧
      ((c < d ∧ x 0 = c ∧ x (Fin.last n) = d) ∨
        (d < c ∧ x 0 = d ∧ x (Fin.last n) = c)) ∧
      IsFilledIndexedSliceChain K T Axis.horizontal q x owner ∧
      owner i = t := by
  intro K T hTile hNonSub t
  obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
  let f : ℝ → Tiling.Plane := fun q =>
    (z.re : ℂ) + ((q - t.1.im : ℝ) : ℂ) * Complex.I
  have hf : Continuous f := by
    fun_prop
  have hfz : f (t.1.im + z.im) = z := by
    apply Complex.ext <;> simp [f]
  have hfnhds : f ⁻¹' K.openCarrier ∈ 𝓝 (t.1.im + z.im) := by
    apply hf.continuousAt.preimage_mem_nhds
    rw [hfz]
    exact isOpen_interior.mem_nhds hz
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hfnhds
  let J : Set ℝ := Ioo (t.1.im + z.im - δ / 2) (t.1.im + z.im + δ / 2)
  have hJ : volume J ≠ 0 := by
    rw [Real.volume_Ioo]
    simp [ENNReal.ofReal_eq_zero]
    linarith
  have hBoundary := c04_plateBoundary_mem_horizontalSliceEndpoint hTile
  have hUnbounded := genericSliceEndpointSet_unbounded K T hTile Axis.horizontal
  have hChain := genericSliceChain_betweenEndpoints_with_endpoints K T hTile Axis.horizontal
  have hAvoid := c04_eventually_avoids_translatedVertexLevels
    hTile.2.1 Axis.horizontal
  obtain ⟨q, hqJ, hqBoundary, hqUnbounded, hqChain, hqAvoid⟩ :=
    MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hJ
      ((hBoundary.and (hUnbounded.and (hChain.and hAvoid))).filter_mono
        MeasureTheory.ae_restrict_le)
  have hqmem : q ∈ f ⁻¹' K.openCarrier := by
    apply hδsub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hqJ.1, hqJ.2]
  have hpoint : slicePoint Axis.horizontal q (t.1.re + z.re) ∈
      (t.1 : Tiling.Plane) +ᵥ K.openCarrier := by
    rw [mem_vadd_set]
    refine ⟨f q, hqmem, ?_⟩
    apply Complex.ext <;> simp [f, slicePoint, vadd_eq_add]
  obtain ⟨c, hc⟩ := totalPlateBoundary_nonempty hTile hNonSub
  have hce : c ∈ sliceEndpointSet K T Axis.horizontal q := hqBoundary c hc
  let U : Set ℝ := {a : ℝ |
    slicePoint Axis.horizontal q a ∈ openUnion K T}
  have hcont : Continuous (slicePoint Axis.horizontal q) := by
    unfold slicePoint
    fun_prop
  have hUopen : IsOpen U := by
    change IsOpen ((slicePoint Axis.horizontal q) ⁻¹' openUnion K T)
    apply IsOpen.preimage
    · exact hcont
    · unfold openUnion
      apply isOpen_iUnion
      intro s
      exact isOpen_interior.vadd s.1
  have haU : t.1.re + z.re ∈ U := by
    change slicePoint Axis.horizontal q (t.1.re + z.re) ∈ openUnion K T
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    exact ⟨t, hpoint⟩
  have hcNotU : c ∉ U := by
    intro hcU
    have hcInt : c ∈ interior U := by
      rw [hUopen.interior_eq]
      exact hcU
    exact Set.disjoint_left.mp disjoint_interior_frontier hcInt hce
  have haNotEndpoint : t.1.re + z.re ∉
      sliceEndpointSet K T Axis.horizontal q := by
    intro haE
    have haInt : t.1.re + z.re ∈ interior U := by
      rw [hUopen.interior_eq]
      exact haU
    exact Set.disjoint_left.mp disjoint_interior_frontier haInt haE
  rcases lt_trichotomy c (t.1.re + z.re) with hca | hca | hac
  · obtain ⟨d, hdE, had⟩ := not_bddAbove_iff.mp hqUnbounded.1 (t.1.re + z.re)
    obtain ⟨n, hn, x, owner, hx0, hxlast, hfilled, hendpoints⟩ :=
      hqChain c hce d hdE (lt_trans hca had)
    have hleft : x 0 < t.1.re + z.re := by rw [hx0]; exact hca
    have hright : t.1.re + z.re < x (Fin.last n) := by rw [hxlast]; exact had
    have hne : ∀ k, t.1.re + z.re ≠ x k := by
      intro k heq
      exact haNotEndpoint (heq ▸ hendpoints k)
    obtain ⟨i, hi⟩ := c04_strictMono_exists_gap x hfilled.1 hleft hright hne
    have hzi : slicePoint Axis.horizontal q (t.1.re + z.re) ∈
        axisInterval Axis.horizontal q (x i.castSucc) (x i.succ) := by
      exact ⟨by simp [slicePoint], by simpa [slicePoint] using hi⟩
    have howner := c04_filledChain_owner_eq_of_mem hTile hfilled i t hzi hpoint
    exact ⟨c, hc, d, q, n, x, owner, i, hce, hdE,
      Or.inl ⟨lt_trans hca had, hx0, hxlast⟩, hfilled, howner⟩
  · exact False.elim (hcNotU (hca ▸ haU))
  · obtain ⟨d, hdE, hdc⟩ := not_bddBelow_iff.mp hqUnbounded.2
      (min c (t.1.re + z.re))
    obtain ⟨n, hn, x, owner, hx0, hxlast, hfilled, hendpoints⟩ :=
      hqChain d hdE c hce (lt_of_lt_of_le hdc (min_le_left c _))
    have hleft : x 0 < t.1.re + z.re := by
      rw [hx0]
      exact lt_of_lt_of_le hdc (min_le_right c _)
    have hright : t.1.re + z.re < x (Fin.last n) := by rw [hxlast]; exact hac
    have hne : ∀ k, t.1.re + z.re ≠ x k := by
      intro k heq
      exact haNotEndpoint (heq ▸ hendpoints k)
    obtain ⟨i, hi⟩ := c04_strictMono_exists_gap x hfilled.1 hleft hright hne
    have hzi : slicePoint Axis.horizontal q (t.1.re + z.re) ∈
        axisInterval Axis.horizontal q (x i.castSucc) (x i.succ) := by
      exact ⟨by simp [slicePoint], by simpa [slicePoint] using hi⟩
    have howner := c04_filledChain_owner_eq_of_mem hTile hfilled i t hzi hpoint
    exact ⟨c, hc, d, q, n, x, owner, i, hce, hdE,
      Or.inr ⟨lt_of_lt_of_le hdc (min_le_left c _), hx0, hxlast⟩,
        hfilled, howner⟩

private theorem c04_filledChain_prefix_integer
    {K : Region} {T : Set Tiling.Plane}
    (hInteger : ∀ v ∈ K.vertices, Tiling.RationalPolygonal.IsIntegerPoint v)
    {q : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ} {owner : Fin n → T}
    (hchain : IsFilledIndexedSliceChain K T Axis.horizontal q x owner) :
    ∀ k : Fin (n + 1), ∃ z : ℤ, x k - x 0 = z := by
  have hVertexRe : ∀ (v : K.vertices), ∃ z : ℤ, v.1.re = z := by
    intro v
    obtain ⟨z, hz⟩ :=
      Tiling.RationalPolygonal.mem_integerLattice_iff.mp
        (hInteger v.1 v.2)
    refine ⟨z 0, ?_⟩
    rw [← hz]
    exact Tiling.RationalPolygonal.integerPoint_re z
  obtain ⟨hmono, hsteps⟩ := hchain
  have hstep (i : Fin n) : ∃ z : ℤ,
      x i.succ - x i.castSucc = z := by
    obtain ⟨v, w, hv, hw, hleft, hright, _hpos, _hgap⟩ := hsteps i
    obtain ⟨zv, hzv⟩ := hVertexRe ⟨v, hv⟩
    obtain ⟨zw, hzw⟩ := hVertexRe ⟨w, hw⟩
    refine ⟨zw - zv, ?_⟩
    simp only [Axis.coord, Complex.add_re] at hleft hright
    rw [Int.cast_sub]
    linarith
  have hprefix : ∀ k : Fin (n + 1), ∃ p : ℤ, x k - x 0 = p := by
    intro k
    refine Fin.induction ?_ (fun k ih => ?_) k
    · exact ⟨0, by simp⟩
    · obtain ⟨e, he⟩ := hstep k
      obtain ⟨p, hp⟩ := ih
      refine ⟨p + e, ?_⟩
      calc
        x k.succ - x 0 = (x k.castSucc - x 0) +
            (x k.succ - x k.castSucc) := by
              simp
        _ = (p : ℝ) + (e : ℝ) := by rw [hp, he]
        _ = (p + e : ℤ) := by exact (Int.cast_add p e).symm
  exact hprefix

private theorem centreDifferenceFromBoundary_integer
    : ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (∀ v ∈ K.vertices, Tiling.RationalPolygonal.IsIntegerPoint v) →
      ¬ Subsingleton (VerticalPlate K T) →
      ∀ t : ↥T, ∃ b ∈ ⋃ P : VerticalPlate K T, frontier P.base,
        ∃ n : ℤ, t.1.re - b = n := by
  intro K T hTile hInteger hNonSub t
  obtain ⟨c, hc, d, q, n, x, owner, i, hce, hde, horder, hfilled, howner⟩ :=
    centreOwnedGapInEndpointChain hTile hNonSub t
  obtain ⟨v, w, hv, hw, hleft, hright, _hpositive, _hinside⟩ := hfilled.2 i
  have hVertexRe : ∀ (v : K.vertices), ∃ z : ℤ, v.1.re = z := by
    intro v
    obtain ⟨z, hz⟩ :=
      Tiling.RationalPolygonal.mem_integerLattice_iff.mp
        (hInteger v.1 v.2)
    refine ⟨z 0, ?_⟩
    rw [← hz]
    exact Tiling.RationalPolygonal.integerPoint_re z
  obtain ⟨zv, hzv⟩ := hVertexRe ⟨v, hv⟩
  have hprefix := c04_filledChain_prefix_integer hInteger hfilled
  have hxc : ∃ z : ℤ, x i.castSucc - c = z := by
    rcases horder with horder | horder
    · obtain ⟨z, hz⟩ := hprefix i.castSucc
      refine ⟨z, ?_⟩
      calc
        x i.castSucc - c = x i.castSucc - x 0 := by rw [horder.2.1]
        _ = z := hz
    · obtain ⟨zi, hzi⟩ := hprefix i.castSucc
      obtain ⟨zl, hzl⟩ := hprefix (Fin.last n)
      refine ⟨zi - zl, ?_⟩
      rw [Int.cast_sub]
      calc
        x i.castSucc - c = (x i.castSucc - x 0) -
            (x (Fin.last n) - x 0) := by rw [horder.2.2]; ring
        _ = (zi : ℝ) - zl := by rw [hzi, hzl]
  have hcenter : x i.castSucc = v.re + t.1.re := by
    rw [← howner]
    simpa only [Axis.coord, Complex.add_re] using hleft
  refine ⟨c, hc, ?_⟩
  obtain ⟨z, hz⟩ := hxc
  refine ⟨z - zv, ?_⟩
  rw [Int.cast_sub]
  linarith

private theorem translationFirstCoordinates_mem_intCoset
    : ∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T Set.univ →
      (∀ v ∈ K.vertices, Tiling.RationalPolygonal.IsIntegerPoint v) →
      ¬ Subsingleton (VerticalPlate K T) →
      ∃ x₀ : ℝ, ∀ t ∈ T, ∃ n : ℤ, t.re = x₀ + n := by
  intro K T hTile hInteger hNonSub
  obtain ⟨x₀, hx₀, hxBoundary⟩ :=
    plateBoundaryCoordinates_mem_intCoset hTile hInteger hNonSub
  refine ⟨x₀, ?_⟩
  intro t ht
  obtain ⟨b, hb, z, hz⟩ := centreDifferenceFromBoundary_integer
    hTile hInteger hNonSub (⟨t, ht⟩ : ↥T)
  obtain ⟨m, hm⟩ := hxBoundary hb
  refine ⟨m + z, ?_⟩
  rw [Int.cast_add]
  linarith

private theorem meshLines_volume_zero_local :
    ∀ {d : ℕ}, 0 < d → volume (meshLines d) = 0 := by
  intro d hd
  have hline_re (c : ℝ) : volume {x : Tiling.Plane | x.re = c} = 0 := by
    have hset : {x : Tiling.Plane | x.re = c} =
        Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (Set.univ : Set ℝ)) := by
      ext x
      simp
    rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage]
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
    · exact ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet
  have hline_im (c : ℝ) : volume {x : Tiling.Plane | x.im = c} = 0 := by
    have hset : {x : Tiling.Plane | x.im = c} =
        Complex.measurableEquivRealProd ⁻¹' ((Set.univ : Set ℝ) ×ˢ {c}) := by
      ext x
      simp
    rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage]
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
    · exact (MeasurableSet.univ.prod (measurableSet_singleton c)).nullMeasurableSet
  have hlines : meshLines d =
      (⋃ n : ℤ, {x : Tiling.Plane |
        x.re = (((n : ℚ) / (d : ℚ)) : ℝ)}) ∪
        (⋃ n : ℤ, {x : Tiling.Plane |
          x.im = (((n : ℚ) / (d : ℚ)) : ℝ)}) := by
    ext x
    simp [meshLines]
  rw [hlines, measure_union_null]
  · exact measure_iUnion_null fun n ↦ hline_re _
  · exact measure_iUnion_null fun n ↦ hline_im _

private theorem offMesh_exists_local :
    ∀ {d : ℕ}, 0 < d → ∀ x : Tiling.Plane,
      x ∉ meshLines d → ∃ z : TranslationalTilings.Plane, x ∈ meshCell d z := by
  intro d hd x hx
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hxre (n : ℤ) : x.re ≠ (((n : ℚ) / (d : ℚ)) : ℝ) := by
    intro hn
    exact hx (Or.inl ⟨n, hn⟩)
  have hxim (n : ℤ) : x.im ≠ (((n : ℚ) / (d : ℚ)) : ℝ) := by
    intro hn
    exact hx (Or.inr ⟨n, hn⟩)
  let z : TranslationalTilings.Plane := fun i ↦
    if i = 0 then ⌊(d : ℝ) * x.re⌋ else ⌊(d : ℝ) * x.im⌋
  have hz0 : z 0 = ⌊(d : ℝ) * x.re⌋ := by simp [z]
  have hz1 : z 1 = ⌊(d : ℝ) * x.im⌋ := by simp [z]
  have hrelo : (z 0 : ℝ) / (d : ℝ) < x.re := by
    have hlo : (z 0 : ℝ) / (d : ℝ) ≤ x.re := by
      apply (div_le_iff₀ hdR).2
      rw [hz0]
      simpa [mul_comm] using Int.floor_le ((d : ℝ) * x.re)
    apply lt_of_le_of_ne hlo
    intro heq
    apply hxre (z 0)
    rw [← heq]
    norm_num
  have hrehi : x.re < (z 0 : ℝ) / (d : ℝ) + 1 / (d : ℝ) := by
    rw [← add_div]
    apply (lt_div_iff₀ hdR).2
    rw [hz0]
    simp [mul_comm]
  have himlo : (z 1 : ℝ) / (d : ℝ) < x.im := by
    have hlo : (z 1 : ℝ) / (d : ℝ) ≤ x.im := by
      apply (div_le_iff₀ hdR).2
      rw [hz1]
      simpa [mul_comm] using Int.floor_le ((d : ℝ) * x.im)
    apply lt_of_le_of_ne hlo
    intro heq
    apply hxim (z 1)
    rw [← heq]
    norm_num
  have himhi : x.im < (z 1 : ℝ) / (d : ℝ) + 1 / (d : ℝ) := by
    rw [← add_div]
    apply (lt_div_iff₀ hdR).2
    rw [hz1]
    simp [mul_comm]
  refine ⟨z, ?_⟩
  change (rationalScale d z).re < x.re ∧
    x.re < (rationalScale d z).re + 1 / (d : ℝ) ∧
    (rationalScale d z).im < x.im ∧
    x.im < (rationalScale d z).im + 1 / (d : ℝ)
  norm_num [rationalScale] at hrelo hrehi himlo himhi ⊢
  exact ⟨hrelo, hrehi, himlo, himhi⟩

private theorem regularizedCellUnion_univ_local :
    regularizedCellUnion 1 (Set.univ : Set TranslationalTilings.Plane) =
      (Set.univ : Set Tiling.Plane) := by
  let U : Set Tiling.Plane := ⋃ z : TranslationalTilings.Plane, meshCell 1 z
  have hUopen : IsOpen U := by
    apply isOpen_iUnion
    intro z
    simp only [meshCell]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hUae : U =ᵐ[volume] (Set.univ : Set Tiling.Plane) := by
    apply ae_iff.mpr
    apply measure_mono_null _ (meshLines_volume_zero_local (d := 1) (by simp))
    intro x hxneq
    by_contra hxline
    apply hxneq
    apply propext
    change (x ∈ U) ↔ x ∈ (Set.univ : Set Tiling.Plane)
    constructor
    · intro hxU
      trivial
    · intro _
      obtain ⟨z, hxz⟩ := offMesh_exists_local (d := 1) (by simp) x hxline
      exact Set.mem_iUnion_of_mem z hxz
  have hUdense : Dense U := by
    rw [dense_iff_inter_open]
    intro O hO hOne
    have hUall : ∀ᵐ x ∂volume, x ∈ U := by
      filter_upwards [hUae] with x hx
      exact hx.mpr trivial
    obtain ⟨x, hxO, hxU⟩ := exists_mem_open_of_ae_local hO hOne hUall
    exact ⟨x, hxO, hxU⟩
  have hclosure : closure U = (Set.univ : Set Tiling.Plane) :=
    dense_iff_closure_eq.mp hUdense
  simpa [regularizedCellUnion, U] using congrArg interior hclosure

private theorem offMesh_unique_local {d : ℕ} (hd : 0 < d) {x : Tiling.Plane}
    {z w : TranslationalTilings.Plane}
    (hz : x ∈ meshCell d z) (hw : x ∈ meshCell d w) : z = w := by
  funext i
  fin_cases i
  · have hfloor (u : TranslationalTilings.Plane) (hu : x ∈ meshCell d u) :
        ⌊(d : ℝ) * x.re⌋ = u 0 := by
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      rcases hu with ⟨hlo, hhi, -, -⟩
      simp only [rationalScale] at hlo hhi
      have hlo' : (u 0 : ℝ) < (d : ℝ) * x.re := by
        have := (div_lt_iff₀ hdR).mp hlo
        simpa [mul_comm] using this
      have hhi' : (d : ℝ) * x.re < (u 0 : ℝ) + 1 := by
        have hxhi' : x.re < ((u 0 : ℝ) + 1) / (d : ℝ) := by
          rw [add_div]
          exact hhi
        have := (lt_div_iff₀ hdR).mp hxhi'
        simpa [mul_comm] using this
      exact Int.floor_eq_iff.mpr ⟨hlo'.le, hhi'⟩
    exact (hfloor z hz).symm.trans (hfloor w hw)
  · have hfloor (u : TranslationalTilings.Plane) (hu : x ∈ meshCell d u) :
        ⌊(d : ℝ) * x.im⌋ = u 1 := by
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      rcases hu with ⟨-, -, hlo, hhi⟩
      simp only [rationalScale] at hlo hhi
      have hlo' : (u 1 : ℝ) < (d : ℝ) * x.im := by
        have := (div_lt_iff₀ hdR).mp hlo
        simpa [mul_comm] using this
      have hhi' : (d : ℝ) * x.im < (u 1 : ℝ) + 1 := by
        have hxhi' : x.im < ((u 1 : ℝ) + 1) / (d : ℝ) := by
          rw [add_div]
          exact hhi
        have := (lt_div_iff₀ hdR).mp hxhi'
        simpa [mul_comm] using this
      exact Int.floor_eq_iff.mpr ⟨hlo'.le, hhi'⟩
    exact (hfloor z hz).symm.trans (hfloor w hw)

private theorem offMesh_mem_regularized_local {d : ℕ} (hd : 0 < d)
    {B : Set TranslationalTilings.Plane} {x : Tiling.Plane}
    (hx : x ∉ meshLines d) :
    (x ∈ regularizedCellUnion d B ↔
      ∃ z ∈ B, x ∈ meshCell d z) := by
  let U : Set Tiling.Plane := ⋃ z : B, meshCell d z.1
  have hUopen : IsOpen U := by
    apply isOpen_iUnion
    intro z
    simp only [meshCell]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  constructor
  · intro hxreg
    obtain ⟨z, hxz⟩ := offMesh_exists_local hd x hx
    refine ⟨z, ?_, hxz⟩
    by_contra hzB
    have hxcl : x ∈ closure U := interior_subset hxreg
    have hcellopen : IsOpen (meshCell d z) := by
      simp only [meshCell]
      exact (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          ((isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const)))
    rcases (mem_closure_iff.mp hxcl) (meshCell d z) hcellopen hxz with
      ⟨y, hyz, hyU⟩
    rcases Set.mem_iUnion.mp hyU with ⟨w, hyw⟩
    exact hzB (offMesh_unique_local hd hyz hyw ▸ w.property)
  · rintro ⟨z, hzB, hxz⟩
    change x ∈ interior (closure U)
    apply (hUopen.subset_interior_iff.mpr subset_closure)
    exact Set.mem_iUnion_of_mem ⟨z, hzB⟩ hxz

private theorem raw_regularized_ae_local {d : ℕ} (hd : 0 < d)
    (B : Set TranslationalTilings.Plane) :
    (⋃ z : B, meshCell d z.1) =ᵐ[volume] regularizedCellUnion d B := by
  apply ae_iff.mpr
  apply measure_mono_null _ (meshLines_volume_zero_local hd)
  intro x hxneq
  by_contra hxline
  apply hxneq
  apply propext
  constructor
  · intro hxU
    rcases Set.mem_iUnion.mp hxU with ⟨z, hxz⟩
    exact (meshCell_subset_regularizedCellUnion_iff hd B z.1).mpr z.property hxz
  · intro hxR
    rcases (offMesh_mem_regularized_local hd hxline).mp hxR with ⟨z, hzB, hxz⟩
    exact Set.mem_iUnion_of_mem ⟨z, hzB⟩ hxz

private theorem meshCell_re_floor_local {d : ℕ} (hd : 0 < d)
    {q : TranslationalTilings.Plane} {x : Tiling.Plane}
    (hx : x ∈ meshCell d q) : ⌊(d : ℝ) * x.re⌋ = q 0 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rcases hx with ⟨hlo, hhi, -, -⟩
  simp only [rationalScale] at hlo hhi
  have hlo' : (q 0 : ℝ) < (d : ℝ) * x.re := by
    have h := (div_lt_iff₀ hdR).mp hlo
    simpa [mul_comm] using h
  have hhi' : (d : ℝ) * x.re < (q 0 : ℝ) + 1 := by
    have hxhi' : x.re < ((q 0 : ℝ) + 1) / (d : ℝ) := by
      rw [add_div]
      exact hhi
    have h := (lt_div_iff₀ hdR).mp hxhi'
    simpa [mul_comm] using h
  exact Int.floor_eq_iff.mpr ⟨hlo'.le, hhi'⟩

private theorem vertical_cell_index_difference
    {y : ℝ}
    {x : Tiling.Plane} {q q' : TranslationalTilings.Plane}
    (hq : x - (y : ℂ) * Complex.I ∈ meshCell 1 q)
    (hq' : x ∈ meshCell 1 q') :
    ∃ k : ℤ, q' = q + k • Tiling.AxisParallel.Discrete.verticalDiscreteUnit := by
  have hq0 := meshCell_re_floor_local (d := 1) (by simp) hq
  have hq'0 := meshCell_re_floor_local (d := 1) (by simp) hq'
  have hreal : (x - (y : ℂ) * Complex.I).re = x.re := by
    simp
  have hzero : q' 0 = q 0 := by
    rw [← hq'0, ← hq0]
    simp [hreal]
  let k : ℤ := q' 1 - q 1
  refine ⟨k, ?_⟩
  funext i
  fin_cases i
  · simpa [Pi.add_apply, Pi.smul_apply,
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit] using hzero
  · simp [k, Tiling.AxisParallel.Discrete.verticalDiscreteUnit]

private theorem raw_vadd_ae_local
    {B : Set TranslationalTilings.Plane}
    (hB : Tiling.RationalPolygonal.DiscretePeriodicBy B
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit)
    (y : ℝ) :
    ((y : ℂ) * Complex.I) +ᵥ (⋃ z : B, meshCell 1 z.1) =ᵐ[volume]
      ⋃ z : B, meshCell 1 z.1 := by
  let v : Tiling.Plane := (y : ℂ) * Complex.I
  have hline : ∀ᵐ x : Tiling.Plane ∂volume, x ∉ meshLines 1 := by
    apply ae_iff.mpr
    have heq : {x : Tiling.Plane | ¬ x ∉ meshLines 1} = meshLines 1 := by
      ext x
      simp
    rw [heq]
    exact meshLines_volume_zero_local (d := 1) (by simp)
  have hline' : ∀ᵐ x : Tiling.Plane ∂volume, x - v ∉ meshLines 1 := by
    have hs := (quasiMeasurePreserving_add_left volume (-v)).ae hline
    simpa [v, vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using hs
  filter_upwards [hline, hline'] with x hxline hxline'
  apply propext
  constructor
  · intro hx
    change x ∈ v +ᵥ (⋃ z : B, meshCell 1 z.1) at hx
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
    have hxsrc : x - v ∈ ⋃ z : B, meshCell 1 z.1 := by
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        v] using hx
    rcases Set.mem_iUnion.mp hxsrc with ⟨q, hq⟩
    obtain ⟨q', hxq'⟩ := offMesh_exists_local (d := 1) (by simp) x hxline
    obtain ⟨k, hqq'⟩ := vertical_cell_index_difference hq hxq'
    have hqB : q' ∈ B := by
      rw [hqq']
      exact ((Tiling.RationalPolygonal.DiscretePeriodicBy.zsmul hB k) q.1).mpr q.property
    exact Set.mem_iUnion_of_mem ⟨q', hqB⟩ hxq'
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨q, hq⟩
    obtain ⟨q', hxq'⟩ := offMesh_exists_local (d := 1) (by simp) (x - v) hxline'
    obtain ⟨k, hqq'⟩ := vertical_cell_index_difference hxq' hq
    have hqB : q' ∈ B := by
      apply ((Tiling.RationalPolygonal.DiscretePeriodicBy.zsmul hB k) q').mp
      rw [← hqq']
      exact q.property
    have hresult : x - v ∈ ⋃ z : B, meshCell 1 z.1 :=
      Set.mem_iUnion_of_mem ⟨q', hqB⟩ hxq'
    change x ∈ v +ᵥ (⋃ z : B, meshCell 1 z.1)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      v] using hresult

private theorem regularized_vertical_period_local
    {B : Set TranslationalTilings.Plane}
    (hB : Tiling.RationalPolygonal.DiscretePeriodicBy B
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit)
    (y : ℝ) :
    ((y : ℂ) * Complex.I) +ᵥ regularizedCellUnion 1 B =
      regularizedCellUnion 1 B := by
  let v : Tiling.Plane := (y : ℂ) * Complex.I
  let U : Set Tiling.Plane := ⋃ i ∈ B, meshCell 1 i
  have hUeq : U = ⋃ z : B, meshCell 1 z.1 := by
    ext x
    simp [U]
  have hUR : U =ᵐ[volume] regularizedCellUnion 1 B := by
    rw [hUeq]
    exact raw_regularized_ae_local (d := 1) (by simp) B
  have hraw : v +ᵥ U =ᵐ[volume] U := by
    simpa [v] using raw_vadd_ae_local hB y
  have hshift :=
    (quasiMeasurePreserving_add_left volume (-v)).vadd_ae_eq_of_ae_eq v hUR
  have hae : v +ᵥ regularizedCellUnion 1 B =ᵐ[volume]
      regularizedCellUnion 1 B := hshift.symm.trans (hraw.trans hUR)
  apply Tiling.AxisParallel.regularOpen_eq_of_aeEq
    (isOpen_interior.vadd v) (by
      rw [closure_vadd, interior_vadd]
      simp)
    isOpen_interior (by simp)
  simpa [regularizedCellUnion, U, v] using hae

private theorem integerPoint_image_preimage_of_integer
    {A : Set Tiling.Plane}
    (hA : ∀ a ∈ A, Tiling.RationalPolygonal.IsIntegerPoint a) :
    Tiling.RationalPolygonal.integerPoint ''
        (Tiling.RationalPolygonal.integerPoint ⁻¹' A) = A := by
  ext a
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro ha
    obtain ⟨z, hz⟩ := mem_integerLattice_iff.mp (hA a ha)
    have hzA : Tiling.RationalPolygonal.integerPoint z ∈ A := hz.symm ▸ ha
    exact ⟨z, hzA, hz⟩

private theorem closure_eq_of_open_ae_local
    {U V : Set Tiling.Plane} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U =ᵐ[volume] V) : closure U = closure V := by
  have hmono : ∀ {P Q : Set Tiling.Plane}, IsOpen P → IsOpen Q →
      P =ᵐ[volume] Q → P ⊆ closure Q := by
    intro P Q hP hQ hPQ x hxP
    by_contra hxQ
    let W : Set Tiling.Plane := P ∩ (closure Q)ᶜ
    have hWopen : IsOpen W := hP.inter isClosed_closure.isOpen_compl
    have hxW : x ∈ W := ⟨hxP, hxQ⟩
    have hWzero : volume W = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr (hPQ.mono fun y hy hyW ↦ by
        have hyQ : y ∈ Q := Eq.mp hy hyW.1
        exact hyW.2 (subset_closure hyQ))
    exact hWopen.measure_ne_zero volume ⟨x, hxW⟩ hWzero
  apply Set.Subset.antisymm
  · exact closure_minimal (hmono hU hV hUV) isClosed_closure
  · exact closure_minimal (hmono hV hU hUV.symm) isClosed_closure

private theorem gridCellTiling_iff_discreteTiling
    {K : Region} {A : Set Tiling.Plane}
    {F : Finset TranslationalTilings.Plane} :
    F.Nonempty →
    (∀ v ∈ K.vertices, Tiling.RationalPolygonal.IsIntegerPoint v) →
    K.openCarrier =ᵐ[volume] ⋃ f : F,
      Tiling.RationalPolygonal.integerPoint
          (f : TranslationalTilings.Plane) +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I)) →
    (∀ a ∈ A, Tiling.RationalPolygonal.IsIntegerPoint a) →
    (TilesOn K A Set.univ ↔
      TranslationalTilings.Tiles F
        {z : TranslationalTilings.Plane |
          Tiling.RationalPolygonal.integerPoint z ∈ A} Set.univ) := by
  intro hFne hKint hKae hAint
  let Aint : Set TranslationalTilings.Plane :=
    Tiling.RationalPolygonal.integerPoint ⁻¹' A
  have himage : rationalScale 1 '' Aint = A := by
    have himage0 : rationalScale 1 '' Aint =
        Tiling.RationalPolygonal.integerPoint '' Aint := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, by
          apply Complex.ext <;> simp [rationalScale, integerPoint]⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, by
          apply Complex.ext <;> simp [rationalScale, integerPoint]⟩
    rw [himage0, integerPoint_image_preimage_of_integer hAint]
  have hmesh : OnRationalMesh 1 K.vertices := by
    intro v hv
    obtain ⟨z, hz⟩ := mem_integerLattice_iff.mp (hKint v hv)
    refine ⟨z, ?_⟩
    apply Complex.ext
    · simpa [rationalScale] using congrArg Complex.re hz
    · simpa [rationalScale] using congrArg Complex.im hz
  have hmeshA : OnRationalMesh 1 (rationalScale 1 '' Aint) := by
    rintro a ⟨z, hz, rfl⟩
    exact ⟨z, rfl⟩
  have hregular : (Set.univ : Set Tiling.Plane) =
      regularizedCellUnion 1 (rasterCells 1 (Set.univ : Set Tiling.Plane)) := by
    have hraster : rasterCells 1 (Set.univ : Set Tiling.Plane) =
        (Set.univ : Set TranslationalTilings.Plane) := by
      ext z
      simp [rasterCells]
    rw [hraster]
    exact regularizedCellUnion_univ_local.symm
  obtain ⟨G, hGne, hGraster, hiff⟩ :=
    tilesOn_rationalScale_image_iff_raster (K := K) (A := Aint) (E := Set.univ) (d := 1)
      (by simp) hmesh isOpen_univ (by simp) hregular
  have hFG : (F : Set TranslationalTilings.Plane) = G := by
    have hcell (z : TranslationalTilings.Plane) :
        meshCell 1 z = integerPoint z +ᵥ interior (Complex.Rectangle 0 (1 + Complex.I)) := by
      ext x
      have hrect : interior (Complex.Rectangle 0 (1 + Complex.I)) =
          {w : Tiling.Plane | 0 < w.re ∧ w.re < 1 ∧ 0 < w.im ∧ w.im < 1} := by
        have hr : Complex.Rectangle 0 (1 + Complex.I) = Icc 0 1 ×ℂ Icc 0 1 := by
          ext w
          simp [Complex.Rectangle]
        rw [hr, Complex.interior_reProdIm]
        ext w
        change (w.re ∈ interior (Icc 0 1) ∧ w.im ∈ interior (Icc 0 1)) ↔ _
        simp [interior_Icc]
        tauto
      rw [hrect]
      simp [meshCell, rationalScale, integerPoint,
        Set.mem_vadd_set_iff_neg_vadd_mem]
    have hFae : K.openCarrier =ᵐ[volume] ⋃ f : F,
        meshCell 1 (f : TranslationalTilings.Plane) := by
      have hu : (⋃ f : F, integerPoint (f : TranslationalTilings.Plane) +ᵥ
          interior (Complex.Rectangle 0 (1 + Complex.I))) =
          ⋃ f : F, meshCell 1 (f : TranslationalTilings.Plane) := by
        apply iUnion_congr
        intro f
        exact (hcell f).symm
      filter_upwards [hKae] with x hx
      exact hx.trans (congrFun hu x)
    have hGae : K.openCarrier =ᵐ[volume] ⋃ g : G, meshCell 1 (g : TranslationalTilings.Plane) := by
      obtain ⟨H, -, hHras, hHae, -⟩ := exists_regionRaster (K := K) (d := 1) (by simp) hmesh
      have hGH : (G : Set TranslationalTilings.Plane) = H := hGraster.trans hHras.symm
      have hu : (⋃ g : G, meshCell 1 (g : TranslationalTilings.Plane)) =
          ⋃ h : H, meshCell 1 (h : TranslationalTilings.Plane) := by
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.mp hx with ⟨g, hxg⟩
          have hgH : (g : TranslationalTilings.Plane) ∈ (H : Set _) := by
            rw [← hGH]
            exact g.property
          exact Set.mem_iUnion_of_mem ⟨g.1, hgH⟩ hxg
        · intro hx
          rcases Set.mem_iUnion.mp hx with ⟨h, hxh⟩
          have hhG : (h : TranslationalTilings.Plane) ∈ (G : Set _) := by
            rw [hGH]
            exact h.property
          exact Set.mem_iUnion_of_mem ⟨h.1, hhG⟩ hxh
      rw [hu]
      exact hHae
    apply meshCell_union_finset_eq_of_ae_eq
    filter_upwards [hFae, hGae] with x hxF hxG
    exact hxF.symm.trans hxG
  have hraster : rasterCells 1 (Set.univ : Set Tiling.Plane) =
      (Set.univ : Set TranslationalTilings.Plane) := by
    ext z
    simp [rasterCells]
  have hFG' : F = G := Finset.coe_injective hFG
  subst G
  rw [himage, hraster] at hiff
  change TilesOn K A Set.univ ↔
    TranslationalTilings.Tiles F Aint Set.univ
  exact hiff

private theorem continuousDiscreteVerticalInvariant_iff
    {K : Region} {A S : Set Tiling.Plane}
    {F : Finset TranslationalTilings.Plane} :
    F.Nonempty →
    K.openCarrier =ᵐ[volume] ⋃ f : F,
      Tiling.RationalPolygonal.integerPoint
          (f : TranslationalTilings.Plane) +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I)) →
    (∀ a ∈ A, Tiling.RationalPolygonal.IsIntegerPoint a) → S ⊆ A →
    ((∀ y : ℝ, ((y : ℂ) * Complex.I) +ᵥ regularSupport K S =
        regularSupport K S) ↔
      Tiling.RationalPolygonal.DiscretePeriodicBy
        (Tiling.RationalPolygonal.discreteCarrier F
          (Tiling.RationalPolygonal.integerPoint ⁻¹' S))
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit) := by
  intro hFne hKae hAint hSsub
  let Aint : Set TranslationalTilings.Plane :=
    Tiling.RationalPolygonal.integerPoint ⁻¹' S
  let E : Set TranslationalTilings.Plane :=
    Tiling.RationalPolygonal.discreteCarrier F Aint
  have hSint : ∀ s ∈ S, Tiling.RationalPolygonal.IsIntegerPoint s := by
    intro s hs
    exact hAint s (hSsub hs)
  have himage : Tiling.RationalPolygonal.integerPoint '' Aint = S :=
    integerPoint_image_preimage_of_integer hSint
  have hScount : S.Countable := by
    rw [← himage]
    exact (Set.to_countable Aint).image Tiling.RationalPolygonal.integerPoint
  let _ : Countable S := hScount.to_subtype
  have hcell_shift (f a : TranslationalTilings.Plane) :
      Tiling.RationalPolygonal.integerPoint a +ᵥ meshCell 1 f =
        meshCell 1 (f + a) := by
    rw [meshCell_add (d := 1) (by simp)]
    congr 1
    apply Complex.ext <;> simp [rationalScale,
      Tiling.RationalPolygonal.integerPoint]
  have hcell (z : TranslationalTilings.Plane) :
      meshCell 1 z = Tiling.RationalPolygonal.integerPoint z +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I)) := by
    ext x
    have hrect : interior (Complex.Rectangle 0 (1 + Complex.I)) =
        {w : Tiling.Plane | 0 < w.re ∧ w.re < 1 ∧ 0 < w.im ∧ w.im < 1} := by
      have hr : Complex.Rectangle 0 (1 + Complex.I) = Icc 0 1 ×ℂ Icc 0 1 := by
        ext w
        simp [Complex.Rectangle]
      rw [hr, Complex.interior_reProdIm]
      ext w
      change (w.re ∈ interior (Icc 0 1) ∧ w.im ∈ interior (Icc 0 1)) ↔ _
      simp [interior_Icc]
      tauto
    rw [hrect]
    simp [meshCell, rationalScale,
      Tiling.RationalPolygonal.integerPoint,
      Set.mem_vadd_set_iff_neg_vadd_mem]
  let U : Set Tiling.Plane := ⋃ z : E, meshCell 1 z.1
  have hUopen : IsOpen U := by
    apply isOpen_iUnion
    intro z
    simp only [meshCell]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hraw : openUnion K S =ᵐ[volume] U := by
    have hKcell : K.openCarrier =ᵐ[volume] ⋃ f : F,
        meshCell 1 (f : TranslationalTilings.Plane) := by
      have hu : (⋃ f : F, Tiling.RationalPolygonal.integerPoint
          (f : TranslationalTilings.Plane) +ᵥ
          interior (Complex.Rectangle 0 (1 + Complex.I))) =
          ⋃ f : F, meshCell 1 (f : TranslationalTilings.Plane) := by
        apply iUnion_congr
        intro f
        exact (hcell f).symm
      filter_upwards [hKae] with x hx
      exact hx.trans (congrFun hu x)
    have hshift (s : S) :
        (s : Tiling.Plane) +ᵥ K.openCarrier =ᵐ[volume]
          (s : Tiling.Plane) +ᵥ (⋃ f : F, meshCell 1 (f : TranslationalTilings.Plane)) := by
      exact (quasiMeasurePreserving_add_left volume (-(s : Tiling.Plane))).vadd_ae_eq_of_ae_eq
        (s : Tiling.Plane) hKcell
    have hraw0 : openUnion K S =ᵐ[volume]
        ⋃ s : S, (s : Tiling.Plane) +ᵥ
          (⋃ f : F, meshCell 1 (f : TranslationalTilings.Plane)) := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
      apply Filter.EventuallyEq.countable_iUnion
      intro s
      simpa only [Set.vadd_iUnion] using hshift s
    have hUF : (⋃ s : S, (s : Tiling.Plane) +ᵥ
          (⋃ f : F, meshCell 1 (f : TranslationalTilings.Plane))) = U := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨s, hx⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
        rcases Set.mem_iUnion.mp hx with ⟨f, hxf⟩
        have hs : (s : Tiling.Plane) ∈ S := s.property
        have hs' : (s : Tiling.Plane) ∈
            Tiling.RationalPolygonal.integerPoint '' Aint := by
          exact himage.symm ▸ hs
        obtain ⟨a, ha, hsa⟩ := hs'
        have hza : f.1 + a ∈ E := by
          change f.1 + a ∈ Tiling.RationalPolygonal.discreteCarrier F Aint
          exact ⟨f.1, f.property, a, ha, rfl⟩
        refine Set.mem_iUnion_of_mem ⟨f.1 + a, hza⟩ ?_
        rw [← hcell_shift f.1 a]
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa [hsa, vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc] using hxf
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨z, hxz⟩
        rcases (Tiling.RationalPolygonal.mem_discreteCarrier_iff.mp z.property) with
          ⟨f, hf, a, ha, hz⟩
        have hsa : Tiling.RationalPolygonal.integerPoint a ∈ S :=
          himage ▸ ⟨a, ha, rfl⟩
        refine Set.mem_iUnion_of_mem ⟨Tiling.RationalPolygonal.integerPoint a, hsa⟩ ?_
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        refine Set.mem_iUnion_of_mem ⟨f, hf⟩ ?_
        rw [hz] at hxz
        rw [← hcell_shift f a] at hxz
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxz
        simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc] using hxz
    exact hraw0.trans (Filter.EventuallyEq.of_eq hUF)
  have hcl : closure (openUnion K S) = closure U :=
    closure_eq_of_open_ae_local
      (isOpen_iUnion fun s : S ↦ (K.openCarrier_regularOpen.1).vadd (s : Tiling.Plane))
      hUopen hraw
  have hreg : regularSupport K S = regularizedCellUnion 1 E := by
    change interior (closure (openUnion K S)) = interior (closure U)
    rw [hcl]
  constructor
  · intro hperiod
    rw [hreg] at hperiod
    let R : Set Tiling.Plane := regularizedCellUnion 1 E
    let u : TranslationalTilings.Plane :=
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit
    have hscalar (a : ℤ) : rationalScale 1 (a • u) = (a : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp [rationalScale, u,
          Tiling.AxisParallel.Discrete.verticalDiscreteUnit]
    have hstep : ∀ (a : ℤ),
        rationalScale 1 (a • u) +ᵥ R = R →
        ∀ q, q ∈ E → q + a • u ∈ E := by
      intro a ha q hq
      apply (meshCell_subset_regularizedCellUnion_iff (by exact Nat.zero_lt_succ 0) E
        (q + a • u)).mp
      intro x hx
      have hcell' := meshCell_add (d := 1) (by simp) q (a • u)
      rw [hcell'] at hx
      have hqcell : meshCell 1 q ⊆ R := by
        exact (meshCell_subset_regularizedCellUnion_iff (by simp) E q).mpr hq
      have hx' : x ∈ rationalScale 1 (a • u) +ᵥ R :=
        Set.vadd_set_mono hqcell hx
      rw [ha] at hx'
      exact hx'
    have hplus : rationalScale 1 ((1 : ℤ) • u) +ᵥ R = R := by
      rw [hscalar]
      simpa [R] using hperiod 1
    have hminus : rationalScale 1 ((-1 : ℤ) • u) +ᵥ R = R := by
      rw [hscalar]
      simpa [R] using hperiod (-1)
    change ∀ q, q + u ∈ E ↔ q ∈ E
    intro q
    constructor
    · intro hq
      have := hstep (-1 : ℤ) hminus (q + u) hq
      have hcancel : (q + u) + (-1 : ℤ) • u = q := by
        ext i
        fin_cases i <;>
          (simp [u, Pi.add_apply,
            Tiling.AxisParallel.Discrete.verticalDiscreteUnit] ; rfl)
      rw [hcancel] at this
      exact this
    · intro hq
      have := hstep (1 : ℤ) hplus q hq
      simpa [u] using this
  · intro hperiod y
    rw [hreg]
    exact regularized_vertical_period_local hperiod y

private theorem c04_offsets
    (s h : ℝ) (anchor : Tiling.Plane) :
    (-(s : ℝ) • anchor) +ᵥ (s : ℝ) • (anchor + (h : Tiling.Plane)) =
      (s : ℝ) • (h : Tiling.Plane) := by
  simp only [vadd_eq_add, smul_add]
  rw [← add_assoc, ← add_smul]
  norm_num
open Tiling.AxisParallel.Continuous

private def normalizedCentre {K : Region} {T : Set Tiling.Plane}
    (N : IntegralTileNormalization K)
    (h : ℝ) (sigma : VerticalPlate K T → ℝ) (t : ↥T) : Tiling.Plane :=
  (N.scale : ℝ) • ((t.1 : Tiling.Plane) + N.anchor + (h : ℂ)) +
    (sigma (VerticalPlate.ofCentre t) : ℂ) * Complex.I

private structure IntegralPlateTiling (K : Region) (T : Set Tiling.Plane)
    (N : IntegralTileNormalization K) where
  commonHorizontalShift : ℝ
  plateVerticalShift : VerticalPlate K T → ℝ
  centres : Set Tiling.Plane
  centres_eq : centres = Set.range
    (normalizedCentre (T := T) N commonHorizontalShift plateVerticalShift)
  centre_injective : Function.Injective
    (normalizedCentre (T := T) N commonHorizontalShift plateVerticalShift)
  centres_integer : ∀ a ∈ centres,
    Tiling.RationalPolygonal.IsIntegerPoint a
  tiles : TilesOn N.region centres Set.univ
  plateEquiv : VerticalPlate K T ≃ VerticalPlate N.region centres
  mem_plate : ∀ (P : VerticalPlate K T) (t : ↥T),
    (t.1 : Tiling.Plane) ∈ P.centres ↔
      normalizedCentre (T := T) N commonHorizontalShift plateVerticalShift t ∈
        (plateEquiv P).centres
  column_iff : ∀ P : VerticalPlate K T,
    IsVerticalColumn P ↔ IsVerticalColumn (plateEquiv P)
  support_eq : ∀ P : VerticalPlate K T,
    (plateEquiv P).support =
      (N.scale : ℝ) • ((commonHorizontalShift : ℂ) +ᵥ P.support)
  columnAggregate_support_eq :
    regularSupport N.region
      (verticalColumnCentres N.region centres) =
        (N.scale : ℝ) • ((commonHorizontalShift : ℂ) +ᵥ
          regularSupport K (verticalColumnCentres K T))

/-!  A private, exact interface for sliding the continuous vertical plates. -/

private def shiftedPlateCentre
    {K : Region} {T : Set Tiling.Plane}
    (σ : VerticalPlate K T → ℝ) (t : T) : Tiling.Plane :=
  (((σ (VerticalPlate.ofCentre t) : ℝ) : ℂ) * Complex.I) + t.1

private theorem shiftedPlateCentre_apply
    {K : Region} {T : Set Tiling.Plane}
    (σ : VerticalPlate K T → ℝ) (t : T) :
    shiftedPlateCentre σ t =
      (((σ (VerticalPlate.ofCentre t) : ℝ) : ℂ) * Complex.I) + t.1 := by
  rfl

private theorem shiftedPlateCentre_mem
    {K : Region} {T : Set Tiling.Plane}
    (σ : VerticalPlate K T → ℝ) (t : T) :
    shiftedPlateCentre σ t ∈ shiftVerticalPlates K T σ := by
  rw [shiftVerticalPlates_eq, Set.mem_iUnion]
  refine ⟨VerticalPlate.ofCentre t, ?_⟩
  exact ⟨t.1, VerticalPlate.mem_centres_ofCentre t, rfl⟩

private theorem shiftedPlateCentre_eq_of_mem
    {K : Region} {T : Set Tiling.Plane}
    (P : VerticalPlate K T) {t : T} (ht : t.1 ∈ P.centres) :
    VerticalPlate.ofCentre t = P := by
  obtain ⟨u, hu, hut⟩ := ht
  have hut' : u = t := Subtype.ext hut
  subst u
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff P t).mp hu

private theorem shiftedSupport_invariant
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : VerticalPlate K T) (r : ℝ) :
    (((r : ℝ) : ℂ) * Complex.I) +ᵥ P.support = P.support := by
  have hslab := (relativeCarrier_verticalPlates
    (K := K) (T := T) (E := Set.univ) (X₀ := Set.univ) hTile
    (by ext z; simp) (by ext x; simp) (by intro a b; simp)).1 P
  rw [hslab.2]
  ext z
  simp [Set.mem_vadd_set_iff_neg_vadd_mem]

private theorem shiftedTile_support
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : VerticalPlate K T) (r : ℝ) :
    regularSupport K ((((r : ℝ) : ℂ) * Complex.I) +ᵥ P.centres) = P.support := by
  rw [regularSupport_vadd]
  change (((r : ℝ) : ℂ) * Complex.I) +ᵥ regularSupport K P.centres = P.support
  rw [VerticalPlate.support_eq_regularSupport]
  exact shiftedSupport_invariant hTile P r

private theorem shiftedOpenCarrier_subset
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : VerticalPlate K T) (r : ℝ)
    {s : Tiling.Plane}
    (hs : s ∈ (((r : ℝ) : ℂ) * Complex.I) +ᵥ P.centres) :
    s +ᵥ K.openCarrier ⊆ P.support := by
  have hreg := shiftedTile_support hTile P r
  intro z hz
  rw [← hreg]
  apply interior_maximal subset_closure
  · rw [Tiling.Polygonal.openUnion, ← Region.openCarrier]
    exact isOpen_iUnion fun q ↦
      (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _
        K.openCarrier_regularOpen.1
  · rw [Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨s, hs⟩, hz⟩

private theorem plateSlide_placedSupport_subset
    (K : Region) {A : Set Tiling.Plane} {s : Tiling.Plane} (hs : s ∈ A) :
    s +ᵥ K.support ⊆ closure (regularSupport K A) := by
  rw [K.isPolygonal.closure_interior.symm, ← closure_vadd s (interior K.support)]
  apply closure_mono
  intro z hz
  rw [regularSupport]
  apply (isOpen_iUnion fun i : A ↦ isOpen_interior.vadd (i : Tiling.Plane)).subset_interior_closure
  change z ∈ ⋃ i : A, (i : Tiling.Plane) +ᵥ K.openCarrier
  exact Set.mem_iUnion_of_mem ⟨s, hs⟩ hz

theorem plateSlide_noCrossing
    {K : Region} {A B : Set Tiling.Plane} {Y0 Y1 : Set ℝ}
    (hreg0 : interior (closure Y0) = Y0)
    (hreg1 : interior (closure Y1) = Y1)
    (hdisj : Disjoint (regularSupport K A) (regularSupport K B))
    (hA : regularSupport K A = Complex.re ⁻¹' Y0)
    (hB : regularSupport K B = Complex.re ⁻¹' Y1)
    {s t : Tiling.Plane} (hs : s ∈ A) (ht : t ∈ B) :
    ¬ HorizontalProperContact K s t := by
  rintro ⟨a, b, hab, him, hseg⟩
  have hre : a.re ≠ b.re := by
    intro hre
    apply hab
    exact Complex.ext hre him
  let J : Set ℝ := openSegment ℝ a.re b.re
  have hJopen : IsOpen J := by
    change IsOpen (openSegment ℝ a.re b.re)
    rcases lt_or_gt_of_ne hre with hlt | hgt
    · rw [openSegment_eq_Ioo hlt]
      exact isOpen_Ioo
    · rw [openSegment_symm, openSegment_eq_Ioo hgt]
      exact isOpen_Ioo
  have hplacedA {z : Tiling.Plane} (hu : z ∈ s +ᵥ K.support) :
      z ∈ closure (regularSupport K A) := by
    exact plateSlide_placedSupport_subset K hs hu
  have hplacedB {z : Tiling.Plane} (hu : z ∈ t +ᵥ K.support) :
      z ∈ closure (regularSupport K B) := by
    exact plateSlide_placedSupport_subset K ht hu
  have hJ0 : J ⊆ closure Y0 := by
    intro q hq
    change q ∈ openSegment ℝ a.re b.re at hq
    rw [openSegment_eq_image] at hq
    obtain ⟨u, hu, rfl⟩ := hq
    have hz := hseg (lineMap_mem_openSegment ℝ a b hu)
    have hzsupport := frontier_subset_closure hz.1.1
    rw [(K.isPolygonal.isClosed.vadd s).closure_eq] at hzsupport
    have hzcl := hplacedA hzsupport
    rw [hA] at hzcl
    rw [Complex.closure_preimage_re] at hzcl
    change (AffineMap.lineMap a b u).re ∈ closure Y0 at hzcl
    change (1 - u) * a.re + u * b.re ∈ closure Y0
    rw [show (1 - u) * a.re + u * b.re = u * (b.re - a.re) + a.re by ring]
    simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul] using hzcl
  have hJ1 : J ⊆ closure Y1 := by
    intro q hq
    change q ∈ openSegment ℝ a.re b.re at hq
    rw [openSegment_eq_image] at hq
    obtain ⟨u, hu, rfl⟩ := hq
    have hz := hseg (lineMap_mem_openSegment ℝ a b hu)
    have hzsupport := frontier_subset_closure hz.1.2
    rw [(K.isPolygonal.isClosed.vadd t).closure_eq] at hzsupport
    have hzcl := hplacedB hzsupport
    rw [hB] at hzcl
    rw [Complex.closure_preimage_re] at hzcl
    change (AffineMap.lineMap a b u).re ∈ closure Y1 at hzcl
    change (1 - u) * a.re + u * b.re ∈ closure Y1
    rw [show (1 - u) * a.re + u * b.re = u * (b.re - a.re) + a.re by ring]
    simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul] using hzcl
  have hmJ : midpoint ℝ a.re b.re ∈ J := midpoint_mem_openSegment _ _
  have hm0 : midpoint ℝ a.re b.re ∈ Y0 := by
    rw [← hreg0]
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hJopen.mem_nhds hmJ) hJ0)
  have hm1 : midpoint ℝ a.re b.re ∈ Y1 := by
    rw [← hreg1]
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hJopen.mem_nhds hmJ) hJ1)
  have hz0 : ((midpoint ℝ a.re b.re : ℝ) : ℂ) ∈ regularSupport K A := by
    simpa [hA] using hm0
  have hz1 : ((midpoint ℝ a.re b.re : ℝ) : ℂ) ∈ regularSupport K B := by
    simpa [hB] using hm1
  exact Set.disjoint_left.1 hdisj hz0 hz1

private theorem plateSlide_contact_vadd_iff
    {K : Region} {u s t : Tiling.Plane} :
    HorizontalProperContact K s t ↔
      HorizontalProperContact K (u +ᵥ s) (u +ᵥ t) := by
  constructor
  · rintro ⟨a, b, hab, him, hseg⟩
    refine ⟨u +ᵥ a, u +ᵥ b, ?_, ?_, ?_⟩
    · intro h
      exact hab (add_left_cancel h)
    · simpa [Complex.add_im] using him
    · have hfront (X : Set Tiling.Plane) :
      frontier (u +ᵥ X) = u +ᵥ frontier X := by
        rw [frontier, closure_vadd, interior_vadd]
        ext z
        constructor
        · rintro ⟨hz0, hz1⟩
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz0 hz1
          exact ⟨hz0, hz1⟩
        · intro hz
          rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz
          refine ⟨Set.mem_vadd_set_iff_neg_vadd_mem.mpr hz.1, ?_⟩
          intro hznot
          apply hz.2
          exact Set.mem_vadd_set_iff_neg_vadd_mem.mp hznot
      simp only [vadd_assoc]
      rw [hfront, hfront]
      intro z hz
      have hz' : z - u ∈ openSegment ℝ a b := by
        have hz'' : z ∈ u +ᵥ openSegment ℝ a b := by
          rw [vadd_openSegment]
          simpa [vadd_eq_add] using hz
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz''
        simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hz''
      have hzK := hseg hz'
      refine ⟨?_, ?_⟩
      · exact ⟨by simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using
            (Set.mem_vadd_set_iff_neg_vadd_mem.mpr
              (by simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hzK.1.1)),
          by simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using
            (Set.mem_vadd_set_iff_neg_vadd_mem.mpr
              (by simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hzK.1.2))⟩
      · intro hzv
        rcases hzv with hzv | hzv
        · exact hzK.2 (Or.inl (by simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using
            (Set.mem_vadd_set_iff_neg_vadd_mem.mp hzv)))
        · exact hzK.2 (Or.inr (by simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using
            (Set.mem_vadd_set_iff_neg_vadd_mem.mp hzv)))
  · rintro ⟨a, b, hab, him, hseg⟩
    refine ⟨(-u) +ᵥ a, (-u) +ᵥ b, ?_, ?_, ?_⟩
    · intro h
      exact hab (add_left_cancel h)
    · simpa [Complex.sub_im] using him
    · have hfront (X : Set Tiling.Plane) :
      frontier (u +ᵥ X) = u +ᵥ frontier X := by
        rw [frontier, closure_vadd, interior_vadd]
        ext z
        constructor
        · rintro ⟨hz0, hz1⟩
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz0 hz1
          exact ⟨hz0, hz1⟩
        · intro hz
          rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz
          refine ⟨Set.mem_vadd_set_iff_neg_vadd_mem.mpr hz.1, ?_⟩
          intro hznot
          apply hz.2
          exact Set.mem_vadd_set_iff_neg_vadd_mem.mp hznot
      simp only [vadd_assoc] at hseg
      rw [hfront, hfront] at hseg
      intro z hz
      have hz' : u +ᵥ z ∈ openSegment ℝ a b := by
        have ha : u +ᵥ ((-u) +ᵥ a) = a := by simp [vadd_eq_add]
        have hb : u +ᵥ ((-u) +ᵥ b) = b := by simp [vadd_eq_add]
        rw [← ha, ← hb, ← vadd_openSegment ℝ]
        exact ⟨z, hz, rfl⟩
      have hzK := hseg hz'
      refine ⟨?_, ?_⟩
      · exact ⟨by simpa [vadd_eq_add, add_assoc] using
            (Set.mem_vadd_set_iff_neg_vadd_mem.mp hzK.1.1),
          by simpa [vadd_eq_add, add_assoc] using
            (Set.mem_vadd_set_iff_neg_vadd_mem.mp hzK.1.2)⟩
      · intro hzv
        rcases hzv with hzv | hzv
        · exact hzK.2 (Or.inl (Set.mem_vadd_set_iff_neg_vadd_mem.mpr
            (by simpa [vadd_eq_add, add_assoc] using hzv)))
        · exact hzK.2 (Or.inr (Set.mem_vadd_set_iff_neg_vadd_mem.mpr
            (by simpa [vadd_eq_add, add_assoc] using hzv)))

private theorem plateSlide_slab
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (P : VerticalPlate K T) :
    P.base = interior (closure P.base) ∧
      P.support = Complex.re ⁻¹' P.base := by
  exact (relativeCarrier_verticalPlates
    (K := K) (T := T) (E := Set.univ) (X₀ := Set.univ) hTile
    (by ext z; simp) (by ext x; simp) (by intro a b; simp)).1 P

private theorem plateSlide_support_disjoint
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) {P Q : VerticalPlate K T} (hPQ : P ≠ Q) :
    Disjoint P.support Q.support := by
  let _ : Countable T := hTile.1.to_subtype
  let _ : Countable (VerticalPlate K T) := by
    apply Function.Surjective.countable
      (f := fun t : T ↦ VerticalPlate.ofCentre (K := K) t)
    intro P
    obtain ⟨p, hp⟩ := P.nonempty_supp
    refine ⟨p, ?_⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff P p).1 hp
  have hpartition := regularSupport_pairwiseDisjoint
    (@VerticalPlate.centres K T)
      (verticalPlateCentres_pairwiseDisjoint K T)
      (iUnion_verticalPlateCentres K T) hTile
  exact hpartition.1 (Set.mem_univ P) (Set.mem_univ Q) hPQ

private theorem plateSlide_contact_iff
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (σ : VerticalPlate K T → ℝ) (s t : T) :
    HorizontalProperContact K s.1 t.1 ↔
      HorizontalProperContact K (shiftedPlateCentre σ s)
        (shiftedPlateCentre σ t) := by
  let P : VerticalPlate K T := VerticalPlate.ofCentre s
  let Q : VerticalPlate K T := VerticalPlate.ofCentre t
  by_cases hPQ : P = Q
  · subst Q
    have hst : shiftedPlateCentre σ s =
        (((σ P : ℝ) : ℂ) * Complex.I) + s.1 := by rfl
    have htt : shiftedPlateCentre σ t =
        (((σ P : ℝ) : ℂ) * Complex.I) + t.1 := by
      have htP : VerticalPlate.ofCentre t = P := by exact hPQ.symm
      simp only [shiftedPlateCentre]
      rw [htP]
    rw [hst, htt]
    exact plateSlide_contact_vadd_iff
  · have hst : s ≠ t := by
      intro h
      apply hPQ
      simp [P, Q, h]
    have horig : ¬ HorizontalProperContact K s.1 t.1 := by
      intro hc
      apply hPQ
      apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      exact (verticalPlateGraph_adj_iff s t).mpr ⟨hst, hc⟩
    have hshift : ¬ HorizontalProperContact K
        (shiftedPlateCentre σ s) (shiftedPlateCentre σ t) := by
      let A : Set Tiling.Plane :=
        (((σ P : ℝ) : ℂ) * Complex.I) +ᵥ P.centres
      let B : Set Tiling.Plane :=
        (((σ Q : ℝ) : ℂ) * Complex.I) +ᵥ Q.centres
      have hA : regularSupport K A = Complex.re ⁻¹' P.base := by
        dsimp [A]
        rw [shiftedTile_support hTile P (σ P)]
        exact (plateSlide_slab hTile P).2
      have hB : regularSupport K B = Complex.re ⁻¹' Q.base := by
        dsimp [B]
        rw [shiftedTile_support hTile Q (σ Q)]
        exact (plateSlide_slab hTile Q).2
      have hPslab := plateSlide_slab hTile P
      have hQslab := plateSlide_slab hTile Q
      have hdisj := plateSlide_support_disjoint hTile hPQ
      have hAS := shiftedTile_support hTile P (σ P)
      have hBS := shiftedTile_support hTile Q (σ Q)
      have hdisjAB : Disjoint (regularSupport K A) (regularSupport K B) := by
        rw [hAS, hBS]
        exact hdisj
      have hno := plateSlide_noCrossing (K := K) (A := A) (B := B)
        (Y0 := P.base) (Y1 := Q.base)
        (s := shiftedPlateCentre σ s) (t := shiftedPlateCentre σ t)
        hPslab.1.symm hQslab.1.symm hdisjAB
        hA hB
      intro h
      exact hno (by
        exact ⟨s.1, VerticalPlate.mem_centres_ofCentre s, rfl⟩)
        (by
          exact ⟨t.1, VerticalPlate.mem_centres_ofCentre t, rfl⟩) h
    exact ⟨fun h => (horig h).elim, fun h => (hshift h).elim⟩

private theorem shiftedPlateCentre_range
    {K : Region} {T : Set Tiling.Plane}
    (σ : VerticalPlate K T → ℝ) :
    Set.range (shiftedPlateCentre σ) = shiftVerticalPlates K T σ := by
  apply Set.Subset.antisymm
  · rintro z ⟨t, rfl⟩
    exact shiftedPlateCentre_mem σ t
  · rw [shiftVerticalPlates_eq]
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨P, hz⟩
    rcases hz with ⟨t, ht, rfl⟩
    obtain ⟨u, hu, rfl⟩ := ht
    refine ⟨⟨u, u.2⟩, ?_⟩
    have huP : VerticalPlate.ofCentre u = P :=
      shiftedPlateCentre_eq_of_mem P ⟨u, hu, rfl⟩
    simp [shiftedPlateCentre, huP, vadd_eq_add]

private theorem shiftedPlateCentre_injective
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (σ : VerticalPlate K T → ℝ) :
    Function.Injective (shiftedPlateCentre σ) := by
  intro s t hst
  let P : VerticalPlate K T := VerticalPlate.ofCentre s
  let Q : VerticalPlate K T := VerticalPlate.ofCentre t
  by_cases hPQ : P = Q
  · have hσ : σ P = σ Q := congrArg σ hPQ
    have : (((σ P : ℝ) : ℂ) * Complex.I) + s.1 =
        (((σ P : ℝ) : ℂ) * Complex.I) + t.1 := by
      simpa [shiftedPlateCentre, P, Q, hσ] using hst
    exact Subtype.ext (add_left_cancel this)
  · have hdisj := plateSlide_support_disjoint hTile hPQ
    have hKne : K.openCarrier.Nonempty := K.isPolygonal.interior_nonempty K.nonempty
    obtain ⟨k, hk⟩ := hKne
    have hsP : shiftedPlateCentre σ s ∈
        (((σ P : ℝ) : ℂ) * Complex.I) +ᵥ P.centres := by
      refine ⟨s.1, ?_, rfl⟩
      exact VerticalPlate.mem_centres_ofCentre s
    have htQ : shiftedPlateCentre σ t ∈
        (((σ Q : ℝ) : ℂ) * Complex.I) +ᵥ Q.centres := by
      refine ⟨t.1, ?_, rfl⟩
      exact VerticalPlate.mem_centres_ofCentre t
    have hzP := shiftedOpenCarrier_subset hTile P (σ P) hsP
    have hzQ := shiftedOpenCarrier_subset hTile Q (σ Q) htQ
    have hzP' : shiftedPlateCentre σ s +ᵥ k ∈ P.support := hzP ⟨k, hk, rfl⟩
    have hzQ' : shiftedPlateCentre σ t +ᵥ k ∈ Q.support := hzQ ⟨k, hk, rfl⟩
    apply False.elim
    apply Set.disjoint_left.1 hdisj
    · exact hzP'
    · simpa [hst]

private noncomputable def plateSlideCentreEquiv
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (σ : VerticalPlate K T → ℝ) :
    T ≃ shiftVerticalPlates K T σ := by
  apply Equiv.ofBijective (fun t ↦
    ⟨shiftedPlateCentre σ t, shiftedPlateCentre_mem σ t⟩)
  refine ⟨?_, ?_⟩
  · intro s t hst
    exact shiftedPlateCentre_injective hTile σ (congrArg Subtype.val hst)
  · intro z
    rcases z with ⟨z, hz⟩
    rw [← shiftedPlateCentre_range σ] at hz
    rcases hz with ⟨t, rfl⟩
    exact ⟨t, rfl⟩

private theorem plateSlideCentreEquiv_apply
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (σ : VerticalPlate K T → ℝ) (t : T) :
    ((plateSlideCentreEquiv hTile σ t : shiftVerticalPlates K T σ) : Tiling.Plane) =
      shiftedPlateCentre σ t := by
  rfl

private noncomputable def plateSlideGraphIso
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (σ : VerticalPlate K T → ℝ) :
    verticalPlateGraph K T ≃g
      verticalPlateGraph K (shiftVerticalPlates K T σ) := by
  let f := plateSlideCentreEquiv hTile σ
  refine { toEquiv := f, map_rel_iff' := ?_ }
  intro s t
  rw [verticalPlateGraph_adj_iff, verticalPlateGraph_adj_iff]
  constructor
  · rintro ⟨hst, hc⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hst (congrArg f h)
    · simpa only [plateSlideCentreEquiv_apply] using
        (plateSlide_contact_iff hTile σ s t).mpr hc
  · rintro ⟨hst, hc⟩
    refine ⟨?_, ?_⟩
    · intro h
      exact hst (f.injective h)
    · change HorizontalProperContact K (shiftedPlateCentre σ s)
        (shiftedPlateCentre σ t)
      exact (plateSlide_contact_iff hTile σ s t).mp hc

private noncomputable def plateSlideEquiv
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (σ : VerticalPlate K T → ℝ) :
    VerticalPlate K T ≃ VerticalPlate K (shiftVerticalPlates K T σ) :=
  (plateSlideGraphIso hTile σ).connectedComponentEquiv

private theorem plateSlide_component_support_image
    {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (g : G ≃g H) (P : G.ConnectedComponent) :
    (g.connectedComponentEquiv P).supp =
      (g.toEquiv : α → β) '' (↑P.supp : Set α) := by
  ext z
  constructor
  · intro hz
    let q : P.supp ≃ (g.connectedComponentEquiv P).supp :=
      SimpleGraph.ConnectedComponent.isoEquivSupp g P
    let x : P.supp := q.symm ⟨z, hz⟩
    refine ⟨x.1, x.property, ?_⟩
    exact congrArg Subtype.val (q.apply_symm_apply ⟨z, hz⟩)
  · rintro ⟨x, hx, rfl⟩
    let q : P.supp ≃ (g.connectedComponentEquiv P).supp :=
      SimpleGraph.ConnectedComponent.isoEquivSupp g P
    change g.toEquiv x ∈ (g.connectedComponentEquiv P).supp
    simpa [q, SimpleGraph.ConnectedComponent.isoEquivSupp] using
      (q ⟨x, hx⟩).property

private theorem plateSlide_centres_eq
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (σ : VerticalPlate K T → ℝ)
    (P : VerticalPlate K T) :
    (plateSlideEquiv hTile σ P).centres =
      (((σ P : ℝ) : ℂ) * Complex.I) +ᵥ P.centres := by
  let gi := plateSlideGraphIso hTile σ
  change Subtype.val '' (gi.connectedComponentEquiv P).supp = _
  rw [plateSlide_component_support_image gi P]
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases ht with ⟨u, hu, rfl⟩
    have htC : (u : T).1 ∈ P.centres := ⟨u, hu, rfl⟩
    have hP : VerticalPlate.ofCentre u = P :=
      shiftedPlateCentre_eq_of_mem P htC
    refine ⟨u.1, htC, ?_⟩
    symm
    rw [show (gi.toEquiv u : Tiling.Plane) = shiftedPlateCentre σ u by rfl]
    simp [shiftedPlateCentre, hP, vadd_eq_add]
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hz
    have htC : (t : T).1 ∈ P.centres := ⟨t, ht, rfl⟩
    have hP : VerticalPlate.ofCentre t = P :=
      shiftedPlateCentre_eq_of_mem P htC
    refine ⟨gi.toEquiv t, ⟨t, ht, rfl⟩, ?_⟩
    · rw [show (gi.toEquiv t : Tiling.Plane) = shiftedPlateCentre σ t by rfl]
      simp [shiftedPlateCentre, hP, vadd_eq_add]

private theorem plateSlide_support_eq
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (σ : VerticalPlate K T → ℝ)
    (P : VerticalPlate K T) :
    (plateSlideEquiv hTile σ P).support = P.support := by
  rw [VerticalPlate.support_eq_regularSupport, plateSlide_centres_eq hTile σ P]
  exact shiftedTile_support hTile P (σ P)

private theorem plateSlide_isVerticalColumn_iff
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (σ : VerticalPlate K T → ℝ)
    (P : VerticalPlate K T) :
    IsVerticalColumn (plateSlideEquiv hTile σ P) ↔ IsVerticalColumn P := by
  rw [isVerticalColumn_iff, isVerticalColumn_iff,
    plateSlide_centres_eq hTile σ P]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro z hz
    have hz' : (((σ P : ℝ) : ℂ) * Complex.I) +ᵥ z ∈
        (((σ P : ℝ) : ℂ) * Complex.I) +ᵥ P.centres := by
      exact ⟨z, hz, rfl⟩
    have := hx hz'
    simpa [Complex.add_re] using this
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    have hw' := hx hw
    simpa [Complex.add_re] using hw'

private theorem plateSlide_tilesOn
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (σ : VerticalPlate K T → ℝ) :
    TilesOn K (shiftVerticalPlates K T σ) Set.univ := by
  apply tilesOn_shiftVerticalPlates (K := K) (T := T) (E := Set.univ)
    (X₀ := Set.univ) hTile
  · ext z
    simp
  · ext x
    simp
  · intro a b
    simp

private theorem plateSlide_centre_mem_iff
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (σ : VerticalPlate K T → ℝ)
    (P : VerticalPlate K T) (t : T) :
    shiftedPlateCentre σ t ∈ (plateSlideEquiv hTile σ P).centres ↔
      t.1 ∈ P.centres := by
  rw [plateSlide_centres_eq hTile σ P]
  constructor
  · rintro ⟨z, hz, hzt⟩
    rcases hz with ⟨u, hu, hzu⟩
    have huC : (u : T).1 ∈ P.centres := ⟨u, hu, rfl⟩
    have hP : VerticalPlate.ofCentre u = P :=
      shiftedPlateCentre_eq_of_mem P huC
    have hEq : shiftedPlateCentre σ t = shiftedPlateCentre σ u := by
      simpa [shiftedPlateCentre, hP, hzu, vadd_eq_add] using hzt.symm
    have htu : t = u := shiftedPlateCentre_injective hTile σ hEq
    simpa [htu] using huC
  · intro ht
    have hP : VerticalPlate.ofCentre t = P := shiftedPlateCentre_eq_of_mem P ht
    refine ⟨t.1, ht, ?_⟩
    simp [shiftedPlateCentre, hP, vadd_eq_add]

private theorem plateSlide_column_support_iUnion
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (σ : VerticalPlate K T → ℝ) :
    (⋃ P : {P : VerticalPlate K T // IsVerticalColumn P}, P.1.support) =
      ⋃ Q : {Q : VerticalPlate K (shiftVerticalPlates K T σ) //
        IsVerticalColumn Q}, Q.1.support := by
  ext z
  constructor
  · rw [Set.mem_iUnion]
    rintro ⟨P, hz⟩
    let Q : {Q : VerticalPlate K (shiftVerticalPlates K T σ) //
        IsVerticalColumn Q} :=
      ⟨plateSlideEquiv hTile σ P.1,
        (plateSlide_isVerticalColumn_iff hTile σ P.1).mpr P.2⟩
    refine Set.mem_iUnion.mpr ⟨Q, ?_⟩
    simpa [Q] using (plateSlide_support_eq hTile σ P.1 ▸ hz)
  · rw [Set.mem_iUnion]
    rintro ⟨Q, hz⟩
    let P : {P : VerticalPlate K T // IsVerticalColumn P} :=
      ⟨(plateSlideEquiv hTile σ).symm Q.1,
        (plateSlide_isVerticalColumn_iff hTile σ _).mp (by simpa using Q.2)⟩
    refine Set.mem_iUnion.mpr ⟨P, ?_⟩
    have heq := plateSlide_support_eq hTile σ P.1
    have hQ : plateSlideEquiv hTile σ P.1 = Q.1 := by
      exact (plateSlideEquiv hTile σ).apply_symm_apply Q.1
    have heq' : Q.1.support = P.1.support := by
      rw [← hQ]
      exact heq
    rw [← heq']
    exact hz

open Tiling.AxisParallel.Foundations.FilledSliceChains

/-!
Dependency-closed integration prefix for the frozen integralPlateTiling_exists
statement. The accepted PlateSlides.lean is intentionally unchanged. Its
private block is copied locally because Lean does not export private names
across modules; the bridge package below exposes only the unresolved
constructor-side data.
-/

private theorem normalizedCentre_re_local
    {K : Region} {T : Set Tiling.Plane}
    (N : IntegralTileNormalization K) (h : ℝ)
    (sigma : VerticalPlate K T → ℝ) (t : ↥T) :
    (normalizedCentre N h sigma t).re =
      (N.scale : ℝ) * (t.1.re + N.anchor.re + h) := by
  norm_num [normalizedCentre, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

private theorem normalizedCentre_im_local
    {K : Region} {T : Set Tiling.Plane}
    (N : IntegralTileNormalization K) (h : ℝ)
    (sigma : VerticalPlate K T → ℝ) (t : ↥T) :
    (normalizedCentre N h sigma t).im =
      (N.scale : ℝ) * (t.1.im + N.anchor.im) + sigma (VerticalPlate.ofCentre t) := by
  norm_num [normalizedCentre, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

private theorem integralPoint_of_re_im_local
    {z : Tiling.Plane} (hr : ∃ n : ℤ, z.re = n)
    (hi : ∃ n : ℤ, z.im = n) :
    Tiling.RationalPolygonal.IsIntegerPoint z := by
  obtain ⟨nr, hnr⟩ := hr
  obtain ⟨ni, hni⟩ := hi
  apply Tiling.RationalPolygonal.mem_integerLattice_iff.mpr
  refine ⟨![nr, ni], ?_⟩
  apply Complex.ext <;> simp [Tiling.RationalPolygonal.integerPoint, hnr, hni]

private theorem normalizedCentre_integer_of_cosets
    {K : Region} {T : Set Tiling.Plane}
    (N : IntegralTileNormalization K) (h : ℝ)
    (sigma : VerticalPlate K T → ℝ) (x₀ : ℝ)
    (hx₀ : ∀ t ∈ T, ∃ n : ℤ, t.re = x₀ + n)
    (theta : VerticalPlate K T → ℝ)
    (htheta : ∀ P : VerticalPlate K T, ∀ t ∈ P.centres,
      ∃ n : ℤ, t.im = theta P + n)
    (hh : h = -(x₀ + N.anchor.re))
    (hsigma : ∀ P : VerticalPlate K T,
      sigma P = -(N.scale : ℝ) * (theta P + N.anchor.im)) :
    ∀ a ∈ Set.range (normalizedCentre (T := T) N h sigma),
      Tiling.RationalPolygonal.IsIntegerPoint a := by
  intro a ha
  obtain ⟨t, rfl⟩ := ha
  obtain ⟨nr, hnr⟩ := hx₀ t.1 t.2
  have hmem : (t.1 : Tiling.Plane) ∈
      (VerticalPlate.ofCentre t).centres :=
    VerticalPlate.mem_centres_ofCentre (K := K) t
  obtain ⟨ni, hni⟩ := htheta (VerticalPlate.ofCentre t) t.1 hmem
  apply integralPoint_of_re_im_local
  · refine ⟨N.scale * nr, ?_⟩
    rw [normalizedCentre_re_local]
    rw [hh]
    norm_num [hnr]
  · refine ⟨N.scale * ni, ?_⟩
    rw [normalizedCentre_im_local]
    rw [hsigma]
    norm_num [hni]
    ring

/-! Concrete data still needed after normalization and plate slides. -/

private structure IntegralPlateTilingPostSlideData
    {K : Region} {T : Set Tiling.Plane}
    (N : IntegralTileNormalization K)
    (h : ℝ) (sigma : VerticalPlate K T → ℝ) where
  centres : Set Tiling.Plane
  centres_eq : centres = Set.range
      (normalizedCentre (T := T) N h sigma)
  centres_integer : ∀ a ∈ centres,
      Tiling.RationalPolygonal.IsIntegerPoint a
  tiles : TilesOn N.region centres Set.univ
  plateEquiv : VerticalPlate K T ≃
    VerticalPlate N.region centres
  mem_plate : ∀ (P : VerticalPlate K T) (t : ↥T),
    (t.1 : Tiling.Plane) ∈ P.centres ↔
      normalizedCentre (T := T) N h sigma t ∈
        (plateEquiv P).centres
  column_iff : ∀ P : VerticalPlate K T,
    IsVerticalColumn P ↔ IsVerticalColumn (plateEquiv P)
  support_eq : ∀ P : VerticalPlate K T,
    (plateEquiv P).support =
      (N.scale : ℝ) • ((h : ℂ) +ᵥ P.support)
  columnAggregate_support_eq :
    regularSupport N.region
      (verticalColumnCentres N.region
        centres) =
      (N.scale : ℝ) • ((h : ℂ) +ᵥ
        regularSupport K (verticalColumnCentres K T))

private theorem l2_plateSlide_tilesOn
    {K R : Region} {T : Set Tiling.Plane} {s : ℝ} {r c : Tiling.Plane}
    (hs : 0 < s)
    (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (hTile : TilesOn K T Set.univ)
    (shift : VerticalPlate R (positiveSimilarity s c '' T) → ℝ) :
    TilesOn R (shiftVerticalPlates R (positiveSimilarity s c '' T) shift)
      Set.univ := by
  have hbase : TilesOn R (positiveSimilarity s c '' T) Set.univ := by
    have hrange : Set.range (positiveSimilarity s (r + c)) = Set.univ :=
      Set.range_eq_univ.mpr (positiveSimilarity_surjective hs)
    simpa [Set.image_univ, hrange] using
      ((tilesOn_positiveSimilarity_iff (s := s) (r := r) (c := c)
        hs hcarrier).mpr hTile)
  exact plateSlide_tilesOn hbase shift

private theorem positiveSimilarity_tilesOn
    {K R : Region} {T : Set Tiling.Plane} {s : ℝ} {r c : Tiling.Plane}
    (hs : 0 < s)
    (hcarrier : R.openCarrier = positiveSimilarity s r '' K.openCarrier)
    (hTile : TilesOn K T Set.univ) :
    TilesOn R (positiveSimilarity s c '' T) Set.univ := by
  have hbase : TilesOn R (positiveSimilarity s c '' T) Set.univ := by
    have hbase' :=
      ((tilesOn_positiveSimilarity_iff (s := s) (r := r) (c := c)
        hs hcarrier).mpr hTile)
    have huniv : positiveSimilarity s (r + c) ''
        (Set.univ : Set Tiling.Plane) = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ.mpr
        (positiveSimilarity_surjective hs)]
    rw [huniv] at hbase'
    simpa [Set.image_univ] using hbase'
  exact hbase

private theorem normalizedCentre_range_eq_slideRange
    {K : Region} {T : Set Tiling.Plane}
    (N : IntegralTileNormalization K) (h : ℝ)
    (sigma : VerticalPlate K T → ℝ)
    (hs : 0 < (N.scale : ℝ))
    (hcarrier : N.region.openCarrier =
      positiveSimilarity (N.scale : ℝ)
        (-(N.scale : ℝ) • N.anchor) '' K.openCarrier) :
    Set.range (normalizedCentre (T := T) N h sigma) =
      shiftVerticalPlates N.region
        (positiveSimilarity (N.scale : ℝ)
          ((N.scale : ℝ) • (N.anchor + (h : Tiling.Plane))) '' T)
        (fun Q => sigma ((verticalPlate_positiveSimilarityEquiv hs hcarrier
          ((N.scale : ℝ) • (N.anchor + (h : Tiling.Plane)))).symm Q)) := by
  let c : Tiling.Plane := (N.scale : ℝ) •
    (N.anchor + (h : Tiling.Plane))
  let U : Set Tiling.Plane := positiveSimilarity (N.scale : ℝ) c '' T
  let e₀ : VerticalPlate K T ≃ VerticalPlate N.region U :=
    verticalPlate_positiveSimilarityEquiv hs hcarrier c
  let b : T ≃ U := positiveSimilarityCentreEquiv hs c
  let shift₀ : VerticalPlate N.region U → ℝ :=
    fun Q => sigma (e₀.symm Q)
  have hpoint (t : T) :
      normalizedCentre N h sigma t =
        shiftedPlateCentre shift₀ (b t) := by
    have hmem : (b t : Tiling.Plane) ∈
        (e₀ (VerticalPlate.ofCentre t)).centres := by
      exact (verticalPlate_positiveSimilarityEquiv_mem_centres
        hs hcarrier c (VerticalPlate.ofCentre t) t).mp
        (VerticalPlate.mem_centres_ofCentre t)
    have hplate : VerticalPlate.ofCentre (b t) =
        e₀ (VerticalPlate.ofCentre t) :=
      shiftedPlateCentre_eq_of_mem _ hmem
    have hσ : sigma (e₀.symm (VerticalPlate.ofCentre (b t))) =
        sigma (VerticalPlate.ofCentre t) := by
      rw [hplate]
      exact congrArg sigma (e₀.symm_apply_apply _)
    rw [normalizedCentre, shiftedPlateCentre]
    change (N.scale : ℝ) • (t.1 + N.anchor + (h : ℂ)) +
      (((sigma (VerticalPlate.ofCentre t) : ℝ) : ℂ) * Complex.I) =
      (((shift₀ (VerticalPlate.ofCentre (K := N.region) (b t)) : ℝ) : ℂ) *
        Complex.I) + (b t : Tiling.Plane)
    dsimp [shift₀]
    rw [hσ]
    dsimp [b, c]
    rw [positiveSimilarityCentreEquiv_apply]
    simp only [positiveSimilarity]
    norm_num [smul_eq_mul]
    ring
  apply Set.Subset.antisymm
  · rintro z ⟨t, rfl⟩
    rw [shiftVerticalPlates_eq]
    refine Set.mem_iUnion_of_mem (VerticalPlate.ofCentre (b t)) ?_
    refine ⟨(b t : Tiling.Plane), VerticalPlate.mem_centres_ofCentre _, ?_⟩
    exact (hpoint t).symm
  · rw [shiftVerticalPlates_eq]
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨Q, hzQ⟩
    rcases hzQ with ⟨u, hu, rfl⟩
    rcases hu with ⟨uU, huU, rfl⟩
    let t : T := b.symm uU
    have huQ : (uU : Tiling.Plane) ∈ Q.centres := ⟨uU, huU, rfl⟩
    have hQ : VerticalPlate.ofCentre uU = Q :=
      shiftedPlateCentre_eq_of_mem Q huQ
    have hb : b t = uU := b.apply_symm_apply uU
    have hmem : (b t : Tiling.Plane) ∈
        (e₀ (VerticalPlate.ofCentre t)).centres := by
      exact (verticalPlate_positiveSimilarityEquiv_mem_centres
        hs hcarrier c (VerticalPlate.ofCentre t) t).mp
        (VerticalPlate.mem_centres_ofCentre t)
    have hplateT : VerticalPlate.ofCentre (b t) =
        e₀ (VerticalPlate.ofCentre t) :=
      shiftedPlateCentre_eq_of_mem _ hmem
    have hplateQ : e₀ (VerticalPlate.ofCentre t) = Q := by
      rw [← hplateT, hb, hQ]
    have hσ : shift₀ Q = sigma (VerticalPlate.ofCentre t) := by
      dsimp [shift₀]
      rw [← hplateQ]
      exact congrArg sigma (e₀.symm_apply_apply _)
    refine ⟨t, ?_⟩
    rw [hpoint t]
    change (((shift₀ (VerticalPlate.ofCentre (K := N.region) (b t)) : ℝ) : ℂ) *
        Complex.I) + (b t : Tiling.Plane) =
      (((shift₀ Q : ℝ) : ℂ) * Complex.I) + (uU : Tiling.Plane)
    rw [hplateT, hplateQ, hσ, hb]

private theorem normalizedCentre_eq_slideCentre
    {K : Region} {T : Set Tiling.Plane}
    (N : IntegralTileNormalization K) (h : ℝ)
    (sigma : VerticalPlate K T → ℝ)
    (hs : 0 < (N.scale : ℝ))
    (hcarrier : N.region.openCarrier =
      positiveSimilarity (N.scale : ℝ)
        (-(N.scale : ℝ) • N.anchor) '' K.openCarrier)
    (t : T) :
    normalizedCentre N h sigma t =
      shiftedPlateCentre
        (fun Q => sigma ((verticalPlate_positiveSimilarityEquiv hs hcarrier
          ((N.scale : ℝ) • (N.anchor + (h : Tiling.Plane)))).symm Q))
        ⟨positiveSimilarity (N.scale : ℝ)
          ((N.scale : ℝ) • (N.anchor + (h : Tiling.Plane))) t.1,
          ⟨t.1, t.2, rfl⟩⟩ := by
  let c : Tiling.Plane := (N.scale : ℝ) •
    (N.anchor + (h : Tiling.Plane))
  let U : Set Tiling.Plane := positiveSimilarity (N.scale : ℝ) c '' T
  let e₀ : VerticalPlate K T ≃ VerticalPlate N.region U :=
    verticalPlate_positiveSimilarityEquiv hs hcarrier c
  let b : T ≃ U := positiveSimilarityCentreEquiv hs c
  have hmem : (b t : Tiling.Plane) ∈
      (e₀ (VerticalPlate.ofCentre t)).centres := by
    exact (verticalPlate_positiveSimilarityEquiv_mem_centres
      hs hcarrier c (VerticalPlate.ofCentre t) t).mp
      (VerticalPlate.mem_centres_ofCentre t)
  have hplate : VerticalPlate.ofCentre (b t) =
      e₀ (VerticalPlate.ofCentre t) :=
    shiftedPlateCentre_eq_of_mem _ hmem
  have hσ : sigma (e₀.symm (VerticalPlate.ofCentre (b t))) =
      sigma (VerticalPlate.ofCentre t) := by
    rw [hplate]
    exact congrArg sigma (e₀.symm_apply_apply _)
  rw [normalizedCentre, shiftedPlateCentre]
  change (N.scale : ℝ) • (t.1 + N.anchor + (h : ℂ)) +
      (((sigma (VerticalPlate.ofCentre t) : ℝ) : ℂ) * Complex.I) =
    (((sigma (e₀.symm (VerticalPlate.ofCentre (b t))) : ℝ) : ℂ) *
      Complex.I) + (b t : Tiling.Plane)
  rw [hσ]
  dsimp [b, c, e₀]
  rw [positiveSimilarityCentreEquiv_apply]
  simp only [positiveSimilarity]
  norm_num [smul_eq_mul]
  ring

private theorem verticalColumnSupport_slide_eq
    {R : Region} {U : Set Tiling.Plane}
    (hbase : TilesOn R U Set.univ)
    (shift : VerticalPlate R U → ℝ) :
      regularSupport R
        (verticalColumnCentres R (shiftVerticalPlates R U shift)) =
      regularSupport R (verticalColumnCentres R U) := by
  change regularSupport R
      (⋃ P : {P : VerticalPlate R (shiftVerticalPlates R U shift) //
        IsVerticalColumn P}, P.1.centres) =
    regularSupport R
      (⋃ P : {P : VerticalPlate R U // IsVerticalColumn P}, P.1.centres)
  rw [regularSupport_iUnion, regularSupport_iUnion]
  simp_rw [← VerticalPlate.support_eq_regularSupport]
  exact congrArg (fun S : Set Tiling.Plane => interior (closure S))
    (plateSlide_column_support_iUnion hbase shift).symm

private theorem normalization_carrier_positiveSimilarity
    {K : Region} (N : IntegralTileNormalization K) :
    N.region.openCarrier = positiveSimilarity (N.scale : ℝ)
        (-(N.scale : ℝ) • N.anchor) '' K.openCarrier := by
  rw [N.carrier_eq]
  ext z
  constructor
  · intro hz
    rcases Set.mem_smul_set.mp hz with ⟨w, hw, rfl⟩
    rcases Set.mem_vadd_set.mp hw with ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp only [positiveSimilarity, vadd_eq_add, smul_add, smul_neg]
    abel_nf
    module
  · rintro ⟨x, hx, rfl⟩
    rw [positiveSimilarity]
    refine Set.mem_smul_set.mpr ⟨-N.anchor +ᵥ x,
      Set.mem_vadd_set.mpr ⟨x, hx, rfl⟩, ?_⟩
    simp only [vadd_eq_add, smul_add, smul_neg]
    abel_nf
    module

private def postSlideData_of_l2
    {K : Region} {T : Set Tiling.Plane}
    (N : IntegralTileNormalization K) (h : ℝ)
    (sigma : VerticalPlate K T → ℝ)
    (hs : 0 < (N.scale : ℝ))
    (hcarrier : N.region.openCarrier =
      positiveSimilarity (N.scale : ℝ)
        (-(N.scale : ℝ) • N.anchor) '' K.openCarrier)
    (hTile : TilesOn K T Set.univ)
    (hcentres_integer : ∀ a ∈ Set.range
      (normalizedCentre (T := T) N h sigma),
      Tiling.RationalPolygonal.IsIntegerPoint a)
    (haggregate :
      regularSupport N.region
        (verticalColumnCentres N.region
          (Set.range (normalizedCentre (T := T) N h sigma))) =
        (N.scale : ℝ) • ((h : ℂ) +ᵥ
          regularSupport K (verticalColumnCentres K T))) :
    IntegralPlateTilingPostSlideData N h sigma := by
  let c : Tiling.Plane := (N.scale : ℝ) •
    (N.anchor + (h : Tiling.Plane))
  let U : Set Tiling.Plane := positiveSimilarity (N.scale : ℝ) c '' T
  let e₀ : VerticalPlate K T ≃ VerticalPlate N.region U :=
    verticalPlate_positiveSimilarityEquiv hs hcarrier c
  let b : T ≃ U := positiveSimilarityCentreEquiv hs c
  let shift₀ : VerticalPlate N.region U → ℝ := fun Q => sigma (e₀.symm Q)
  have hbase : TilesOn N.region U Set.univ := by
    have hbase' :=
      ((tilesOn_positiveSimilarity_iff (s := (N.scale : ℝ))
        (r := -(N.scale : ℝ) • N.anchor) (c := c) hs hcarrier).mpr hTile)
    have huniv : positiveSimilarity (N.scale : ℝ)
        ((-(N.scale : ℝ) • N.anchor) + c) ''
        (Set.univ : Set Tiling.Plane) = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ.mpr
        (positiveSimilarity_surjective hs)]
    rw [huniv] at hbase'
    simpa [U] using hbase'
  have hslide : TilesOn N.region (shiftVerticalPlates N.region U shift₀)
      Set.univ := plateSlide_tilesOn hbase shift₀
  have hrange' := normalizedCentre_range_eq_slideRange N h sigma hs hcarrier
  have hrange : Set.range (normalizedCentre (T := T) N h sigma) =
      shiftVerticalPlates N.region U shift₀ := by
    simpa [U, c, e₀, shift₀] using hrange'
  let slideE : VerticalPlate N.region U ≃
      VerticalPlate N.region (shiftVerticalPlates N.region U shift₀) :=
    plateSlideEquiv hbase shift₀
  let e : VerticalPlate K T ≃
      VerticalPlate N.region (shiftVerticalPlates N.region U shift₀) :=
    e₀.trans slideE
  have hinj : Function.Injective
      (normalizedCentre (T := T) N h sigma) := by
    intro s t hst
    apply b.injective
    apply shiftedPlateCentre_injective hbase shift₀
    rw [normalizedCentre_eq_slideCentre N h sigma hs hcarrier s,
      normalizedCentre_eq_slideCentre N h sigma hs hcarrier t] at hst
    exact hst
  refine {
    centres := shiftVerticalPlates N.region U shift₀
    centres_eq := hrange.symm
    centres_integer := ?_
    tiles := ?_
    plateEquiv := ?_
    mem_plate := ?_
    column_iff := ?_
    support_eq := ?_
    columnAggregate_support_eq := ?_ }
  · rw [← hrange]
    exact hcentres_integer
  · exact hslide
  · exact e
  · intro P t
    rw [normalizedCentre_eq_slideCentre N h sigma hs hcarrier t]
    have hbt :
        (⟨positiveSimilarity (N.scale : ℝ) c t.1,
          ⟨t.1, t.2, rfl⟩⟩ : U) = b t := by
      apply Subtype.ext
      change positiveSimilarity (N.scale : ℝ) c t.1 =
        (positiveSimilarityCentreEquiv hs c t : Tiling.Plane)
      exact (positiveSimilarityCentreEquiv_apply hs c t).symm
    rw [hbt]
    change (t.1 ∈ P.centres) ↔
      shiftedPlateCentre shift₀ (b t) ∈ (slideE (e₀ P)).centres
    exact (verticalPlate_positiveSimilarityEquiv_mem_centres
      hs hcarrier c P t).trans
      (plateSlide_centre_mem_iff hbase shift₀ (e₀ P) (b t)).symm
  · intro P
    simpa [e, slideE, U, c, e₀, shift₀] using
      (verticalPlate_positiveSimilarityEquiv_isVerticalColumn
      hs hcarrier c P).trans
      (plateSlide_isVerticalColumn_iff hbase shift₀ (e₀ P)).symm
  · intro P
    have hslideP := plateSlide_support_eq hbase shift₀ (e₀ P)
    have hsimP := verticalPlate_positiveSimilarityEquiv_support_image
      hs hcarrier c P
    have hoff : (-(N.scale : ℝ) • N.anchor) + c =
        (N.scale : ℝ) • (h : Tiling.Plane) := by
      dsimp [c]
      push_cast
      ring
    have hsupport : (slideE (e₀ P)).support =
        (N.scale : ℝ) • ((h : ℂ) +ᵥ P.support) := by
      rw [hslideP, hsimP, positiveSimilarity_image_eq_vadd_smul, hoff]
      ext z
      simp only [Set.mem_vadd_set, Set.mem_smul_set, vadd_eq_add]
      constructor
      · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨h + y, ⟨y, hy, rfl⟩, ?_⟩
        rw [smul_add]
      · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨(N.scale : ℝ) • y, ⟨y, hy, rfl⟩, ?_⟩
        rw [smul_add]
    simpa [e, slideE] using hsupport
  · rw [← hrange]
    exact haggregate


private theorem integralPlateTiling_of_postSlideData
    {K : Region} {T : Set Tiling.Plane}
    (N : IntegralTileNormalization K) (h : ℝ)
    (sigma : VerticalPlate K T → ℝ)
    (hinj : Function.Injective
      (normalizedCentre (T := T) N h sigma))
    (x₀ : ℝ)
    (hx₀ : ∀ t ∈ T, ∃ n : ℤ, t.re = x₀ + n)
    (theta : VerticalPlate K T → ℝ)
    (htheta : ∀ P : VerticalPlate K T, ∀ t ∈ P.centres,
      ∃ n : ℤ, t.im = theta P + n)
    (hh : h = -(x₀ + N.anchor.re))
    (hsigma : ∀ P : VerticalPlate K T,
      sigma P = -(N.scale : ℝ) * (theta P + N.anchor.im))
    (_hTile : TilesOn K T Set.univ)
    (B : IntegralPlateTilingPostSlideData N h sigma) :
    Nonempty (IntegralPlateTiling K T N) := by
  refine ⟨{
    commonHorizontalShift := h
    plateVerticalShift := sigma
    centres := B.centres
    centres_eq := B.centres_eq
    centre_injective := hinj
    centres_integer := ?_
    tiles := ?_
    plateEquiv := ?_
    mem_plate := ?_
    column_iff := ?_
    support_eq := ?_
    columnAggregate_support_eq := ?_ }⟩
  · rw [B.centres_eq]
    exact normalizedCentre_integer_of_cosets N h sigma x₀ hx₀ theta htheta hh hsigma
  · exact B.tiles
  · exact B.plateEquiv
  · exact B.mem_plate
  · exact B.column_iff
  · exact B.support_eq
  · exact B.columnAggregate_support_eq

private theorem integralPlateTiling_exists_of_cosets
    {K : Region} {T : Set Tiling.Plane}
    (N : IntegralTileNormalization K) (h : ℝ)
    (sigma : VerticalPlate K T → ℝ)
    (hs : 0 < (N.scale : ℝ))
    (hcarrier : N.region.openCarrier =
      positiveSimilarity (N.scale : ℝ)
        (-(N.scale : ℝ) • N.anchor) '' K.openCarrier)
    (hTile : TilesOn K T Set.univ)
    (x₀ : ℝ) (hx₀ : ∀ t ∈ T, ∃ n : ℤ, t.re = x₀ + n)
    (theta : VerticalPlate K T → ℝ)
    (htheta : ∀ P : VerticalPlate K T, ∀ t ∈ P.centres,
      ∃ n : ℤ, t.im = theta P + n)
    (hh : h = -(x₀ + N.anchor.re))
    (hsigma : ∀ P : VerticalPlate K T,
      sigma P = -(N.scale : ℝ) * (theta P + N.anchor.im)) :
    Nonempty (IntegralPlateTiling K T N) := by
  let c : Tiling.Plane := (N.scale : ℝ) •
    (N.anchor + (h : Tiling.Plane))
  let U : Set Tiling.Plane := positiveSimilarity (N.scale : ℝ) c '' T
  let e₀ : VerticalPlate K T ≃ VerticalPlate N.region U :=
    verticalPlate_positiveSimilarityEquiv hs hcarrier c
  let shift₀ : VerticalPlate N.region U → ℝ := fun Q => sigma (e₀.symm Q)
  have hbase : TilesOn N.region U Set.univ := by
    have hbase' :=
      ((tilesOn_positiveSimilarity_iff (s := (N.scale : ℝ))
        (r := -(N.scale : ℝ) • N.anchor) (c := c) hs hcarrier).mpr hTile)
    have huniv : positiveSimilarity (N.scale : ℝ)
        ((-(N.scale : ℝ) • N.anchor) + c) ''
        (Set.univ : Set Tiling.Plane) = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ.mpr
        (positiveSimilarity_surjective hs)]
    rw [huniv] at hbase'
    simpa [U] using hbase'
  have hrange : Set.range (normalizedCentre (T := T) N h sigma) =
      shiftVerticalPlates N.region U shift₀ := by
    have hrange' := normalizedCentre_range_eq_slideRange N h sigma hs hcarrier
    simpa [U, c, e₀, shift₀] using hrange'
  have hoff : (-(N.scale : ℝ) • N.anchor) + c =
      (N.scale : ℝ) • (h : Tiling.Plane) := by
    dsimp [c]
    push_cast
    ring
  have hsim : positiveSimilarity (N.scale : ℝ)
        ((-(N.scale : ℝ) • N.anchor) + c) ''
        regularSupport K (verticalColumnCentres K T) =
      (N.scale : ℝ) • ((h : ℂ) +ᵥ
        regularSupport K (verticalColumnCentres K T)) := by
    rw [positiveSimilarity_image_eq_vadd_smul, hoff]
    ext z
    simp only [Set.mem_vadd_set, Set.mem_smul_set, vadd_eq_add]
    constructor
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨h + y, ⟨y, hy, rfl⟩, ?_⟩
      rw [smul_add]
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨(N.scale : ℝ) • y, ⟨y, hy, rfl⟩, ?_⟩
      rw [smul_add]
  have haggregate :
      regularSupport N.region
        (verticalColumnCentres N.region
          (Set.range (normalizedCentre (T := T) N h sigma))) =
        (N.scale : ℝ) • ((h : ℂ) +ᵥ
          regularSupport K (verticalColumnCentres K T)) := by
    calc
      regularSupport N.region
          (verticalColumnCentres N.region
            (Set.range (normalizedCentre (T := T) N h sigma))) =
          regularSupport N.region
            (verticalColumnCentres N.region
              (shiftVerticalPlates N.region U shift₀)) := by rw [hrange]
      _ = regularSupport N.region (verticalColumnCentres N.region U) :=
        verticalColumnSupport_slide_eq hbase shift₀
      _ = positiveSimilarity (N.scale : ℝ)
          ((-(N.scale : ℝ) • N.anchor) + c) ''
          regularSupport K (verticalColumnCentres K T) :=
        verticalColumnSupport_positiveSimilarity_image hs hcarrier c
      _ = (N.scale : ℝ) • ((h : ℂ) +ᵥ
          regularSupport K (verticalColumnCentres K T)) := hsim
  have hcentres_integer : ∀ a ∈ Set.range
      (normalizedCentre (T := T) N h sigma),
      Tiling.RationalPolygonal.IsIntegerPoint a :=
    normalizedCentre_integer_of_cosets N h sigma x₀ hx₀ theta htheta hh hsigma
  let B := postSlideData_of_l2 N h sigma hs hcarrier hTile
    hcentres_integer haggregate
  have hinj : Function.Injective
      (normalizedCentre (T := T) N h sigma) := by
    let b : T ≃ U := positiveSimilarityCentreEquiv hs c
    intro s t hst
    apply b.injective
    apply shiftedPlateCentre_injective hbase shift₀
    rw [normalizedCentre_eq_slideCentre N h sigma hs hcarrier s,
      normalizedCentre_eq_slideCentre N h sigma hs hcarrier t] at hst
    exact hst
  exact integralPlateTiling_of_postSlideData N h sigma hinj x₀ hx₀ theta
    htheta hh hsigma hTile B

private theorem integralPlateTiling_exists_of_coordinate_cosets
    {K : Region} {T : Set Tiling.Plane}
    (N : IntegralTileNormalization K)
    (hTile : TilesOn K T Set.univ)
    (_hNonSub : ¬ Subsingleton (VerticalPlate K T))
    (hfirst : ∃ x₀ : ℝ, ∀ t ∈ T, ∃ n : ℤ, t.re = x₀ + n)
    (hsecond : ∀ P : VerticalPlate K T, ∃ theta : ℝ,
      ∀ t ∈ P.centres, ∃ n : ℤ, t.im = theta + n) :
    Nonempty (IntegralPlateTiling K T N) := by
  obtain ⟨x₀, hx₀⟩ := hfirst
  let theta : VerticalPlate K T → ℝ := fun P => Classical.choose (hsecond P)
  have htheta (P : VerticalPlate K T) (t : Tiling.Plane) (ht : t ∈ P.centres) :
      ∃ n : ℤ, t.im = theta P + n := by
    exact Classical.choose_spec (hsecond P) t ht
  let h : ℝ := -(x₀ + N.anchor.re)
  let sigma : VerticalPlate K T → ℝ := fun P =>
    -(N.scale : ℝ) * (theta P + N.anchor.im)
  have hs : 0 < (N.scale : ℝ) := by exact_mod_cast N.scale_pos
  have hcarrier := normalization_carrier_positiveSimilarity N
  exact integralPlateTiling_exists_of_cosets N h sigma hs hcarrier hTile
    x₀ hx₀ theta htheta (by rfl) (by intro P; rfl)

private theorem integralPlateTiling_exists_of_integerAggregate
    {K : Region} {T : Set Tiling.Plane}
    (N : IntegralTileNormalization K) (h : ℝ)
    (sigma : VerticalPlate K T → ℝ)
    (hs : 0 < (N.scale : ℝ))
    (hcarrier : N.region.openCarrier =
      positiveSimilarity (N.scale : ℝ)
        (-(N.scale : ℝ) • N.anchor) '' K.openCarrier)
    (hTile : TilesOn K T Set.univ)
    (hcentres_integer : ∀ a ∈ Set.range
      (normalizedCentre (T := T) N h sigma),
      Tiling.RationalPolygonal.IsIntegerPoint a)
    (haggregate :
      regularSupport N.region
        (verticalColumnCentres N.region
          (Set.range (normalizedCentre (T := T) N h sigma))) =
        (N.scale : ℝ) • ((h : ℂ) +ᵥ
          regularSupport K (verticalColumnCentres K T))) :
    Nonempty (IntegralPlateTiling K T N) := by
  let c : Tiling.Plane := (N.scale : ℝ) •
    (N.anchor + (h : Tiling.Plane))
  let U : Set Tiling.Plane := positiveSimilarity (N.scale : ℝ) c '' T
  let e₀ : VerticalPlate K T ≃ VerticalPlate N.region U :=
    verticalPlate_positiveSimilarityEquiv hs hcarrier c
  let shift₀ : VerticalPlate N.region U → ℝ := fun Q => sigma (e₀.symm Q)
  have hbase : TilesOn N.region U Set.univ :=
    positiveSimilarity_tilesOn hs hcarrier hTile
  have hrange : Set.range (normalizedCentre (T := T) N h sigma) =
      shiftVerticalPlates N.region U shift₀ := by
    have hrange' := normalizedCentre_range_eq_slideRange N h sigma hs hcarrier
    simpa [U, c, e₀, shift₀] using hrange'
  have hinj : Function.Injective
      (normalizedCentre (T := T) N h sigma) := by
    let b : T ≃ U := positiveSimilarityCentreEquiv hs c
    intro s t hst
    apply b.injective
    apply shiftedPlateCentre_injective hbase (fun Q => sigma (e₀.symm Q))
    rw [normalizedCentre_eq_slideCentre N h sigma hs hcarrier s,
      normalizedCentre_eq_slideCentre N h sigma hs hcarrier t] at hst
    exact hst
  let B := postSlideData_of_l2 N h sigma hs hcarrier hTile
    hcentres_integer haggregate
  refine ⟨{
    commonHorizontalShift := h
    plateVerticalShift := sigma
    centres := B.centres
    centres_eq := B.centres_eq
    centre_injective := hinj
    centres_integer := ?_
    tiles := B.tiles
    plateEquiv := B.plateEquiv
    mem_plate := B.mem_plate
    column_iff := B.column_iff
    support_eq := B.support_eq
    columnAggregate_support_eq := B.columnAggregate_support_eq }⟩
  rw [B.centres_eq]
  exact hcentres_integer

private theorem integralPlateTiling_exists
    {K : Region} {T : Set Tiling.Plane} (N : IntegralTileNormalization K)
    (hTile : TilesOn K T Set.univ)
    (hNonSub : ¬ Subsingleton (VerticalPlate K T)) :
    Nonempty (IntegralPlateTiling K T N) := by
  have hs : 0 < (N.scale : ℝ) := by exact_mod_cast N.scale_pos
  have hcarrier := normalization_carrier_positiveSimilarity N
  let c₀ : Tiling.Plane := (N.scale : ℝ) • N.anchor
  let U₀ : Set Tiling.Plane := positiveSimilarity (N.scale : ℝ) c₀ '' T
  have hbase₀ : TilesOn N.region U₀ Set.univ := by
    exact positiveSimilarity_tilesOn hs hcarrier hTile
  let e₀₀ : VerticalPlate K T ≃ VerticalPlate N.region U₀ :=
    verticalPlate_positiveSimilarityEquiv hs hcarrier c₀
  have hNonSub₀ : ¬ Subsingleton (VerticalPlate N.region U₀) := by
    intro hsub
    apply hNonSub
    constructor
    intro P Q
    apply e₀₀.injective
    exact Subsingleton.elim (e₀₀ P) (e₀₀ Q)
  obtain ⟨x₀, hx₀⟩ :=
    translationFirstCoordinates_mem_intCoset hbase₀ N.vertices_integer hNonSub₀
  let h : ℝ := -(x₀ / (N.scale : ℝ))
  let c : Tiling.Plane := (N.scale : ℝ) •
    (N.anchor + (h : Tiling.Plane))
  let U : Set Tiling.Plane := positiveSimilarity (N.scale : ℝ) c '' T
  have hbase : TilesOn N.region U Set.univ := by
    exact positiveSimilarity_tilesOn hs hcarrier hTile
  let e₀ : VerticalPlate K T ≃ VerticalPlate N.region U :=
    verticalPlate_positiveSimilarityEquiv hs hcarrier c
  let b : T ≃ U := positiveSimilarityCentreEquiv hs c
  let theta : VerticalPlate N.region U → ℝ := fun Q =>
    Classical.choose (plateSecondCoordinates_mem_intCoset N.vertices_integer Q)
  have htheta (Q : VerticalPlate N.region U) (u : Tiling.Plane)
      (hu : u ∈ Q.centres) : ∃ n : ℤ, u.im = theta Q + n := by
    exact Classical.choose_spec (plateSecondCoordinates_mem_intCoset
      N.vertices_integer Q) u hu
  let sigma : VerticalPlate K T → ℝ := fun P => -theta (e₀ P)
  have hreal (t : T) : ∃ n : ℤ,
      (positiveSimilarity (N.scale : ℝ) c t.1).re = n := by
    obtain ⟨n, hn⟩ := hx₀ (positiveSimilarity (N.scale : ℝ) c₀ t.1) (by
      exact ⟨t, t.2, rfl⟩)
    have hn' : (positiveSimilarity (N.scale : ℝ) c₀ t.1).re =
        x₀ + n := by
      exact hn
    refine ⟨n, ?_⟩
    have hshift : positiveSimilarity (N.scale : ℝ) c t.1 =
        positiveSimilarity (N.scale : ℝ) c₀ t.1 - x₀ := by
      dsimp [positiveSimilarity, c, c₀, h]
      apply Complex.ext <;>
        simp
      field_simp [ne_of_gt hs]
      ring
    rw [hshift]
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith [hn']
  have hmem (t : T) : (b t : Tiling.Plane) ∈
      (e₀ (VerticalPlate.ofCentre t)).centres := by
    exact (verticalPlate_positiveSimilarityEquiv_mem_centres
      hs hcarrier c (VerticalPlate.ofCentre t) t).mp
      (VerticalPlate.mem_centres_ofCentre t)
  have himag (t : T) : ∃ n : ℤ,
      (normalizedCentre N h sigma t).im = n := by
    obtain ⟨n, hn⟩ := htheta (e₀ (VerticalPlate.ofCentre t))
      (b t) (hmem t)
    have hbim : (b t : Tiling.Plane).im =
        (N.scale : ℝ) * (t.1.im + N.anchor.im) := by
      dsimp [b, c]
      rw [positiveSimilarityCentreEquiv_apply]
      simp [positiveSimilarity]
      ring
    refine ⟨n, ?_⟩
    rw [normalizedCentre_im_local]
    dsimp [sigma]
    rw [← hbim]
    linarith
  have hcentres_integer : ∀ a ∈ Set.range
      (normalizedCentre (T := T) N h sigma),
      Tiling.RationalPolygonal.IsIntegerPoint a := by
    intro a ha
    obtain ⟨t, rfl⟩ := ha
    apply integralPoint_of_re_im_local
    · obtain ⟨n, hn⟩ := hreal t
      refine ⟨n, ?_⟩
      have hbre : (normalizedCentre N h sigma t).re =
          (positiveSimilarity (N.scale : ℝ) c t.1).re := by
        rw [normalizedCentre_re_local]
        dsimp [positiveSimilarity, c, h]
        simp
        ring
      rw [hbre]
      exact hn
    · obtain ⟨n, hn⟩ := himag t
      exact ⟨n, hn⟩
  have haggregate :
      regularSupport N.region
        (verticalColumnCentres N.region
          (Set.range (normalizedCentre (T := T) N h sigma))) =
        (N.scale : ℝ) • ((h : ℂ) +ᵥ
          regularSupport K (verticalColumnCentres K T)) := by
    let shift₀ : VerticalPlate N.region U → ℝ := fun Q => sigma (e₀.symm Q)
    have hrange : Set.range (normalizedCentre (T := T) N h sigma) =
        shiftVerticalPlates N.region U shift₀ := by
      have hrange' := normalizedCentre_range_eq_slideRange N h sigma hs hcarrier
      simpa [U, c, e₀, shift₀] using hrange'
    have hsim : positiveSimilarity (N.scale : ℝ)
          ((-(N.scale : ℝ) • N.anchor) + c) ''
          regularSupport K (verticalColumnCentres K T) =
        (N.scale : ℝ) • ((h : ℂ) +ᵥ
          regularSupport K (verticalColumnCentres K T)) := by
      have hoff : (-(N.scale : ℝ) • N.anchor) + c =
          (N.scale : ℝ) • (h : Tiling.Plane) := by
        dsimp [c]
        push_cast
        ring
      rw [positiveSimilarity_image_eq_vadd_smul, hoff]
      ext z
      simp only [Set.mem_vadd_set, Set.mem_smul_set, vadd_eq_add]
      constructor
      · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨h + y, ⟨y, hy, rfl⟩, ?_⟩
        rw [smul_add]
      · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨(N.scale : ℝ) • y, ⟨y, hy, rfl⟩, ?_⟩
        rw [smul_add]
    calc
      regularSupport N.region
          (verticalColumnCentres N.region
            (Set.range (normalizedCentre (T := T) N h sigma))) =
          regularSupport N.region
            (verticalColumnCentres N.region
              (shiftVerticalPlates N.region U shift₀)) := by rw [hrange]
      _ = regularSupport N.region (verticalColumnCentres N.region U) :=
        verticalColumnSupport_slide_eq hbase shift₀
      _ = positiveSimilarity (N.scale : ℝ)
          ((-(N.scale : ℝ) • N.anchor) + c) ''
          regularSupport K (verticalColumnCentres K T) :=
        verticalColumnSupport_positiveSimilarity_image hs hcarrier c
      _ = (N.scale : ℝ) • ((h : ℂ) +ᵥ
          regularSupport K (verticalColumnCentres K T)) := hsim
  exact integralPlateTiling_exists_of_integerAggregate N h sigma hs hcarrier
    hTile hcentres_integer haggregate

end Tiling.AxisParallel.Continuous

namespace Tiling.AxisParallel.RationalMesh

private theorem local_offMesh_existsUnique_meshCell
    {d : ℕ} (hd : 0 < d) (x : Tiling.Plane) (hx : x ∉ meshLines d) :
    ∃! z : ZPlane, x ∈ meshCell d z := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hxre : ∀ n : ℤ, x.re ≠ (((n : ℚ) / (d : ℚ)) : ℝ) := by
    intro n hn
    apply hx
    exact Or.inl ⟨n, hn⟩
  have hxim : ∀ n : ℤ, x.im ≠ (((n : ℚ) / (d : ℚ)) : ℝ) := by
    intro n hn
    apply hx
    exact Or.inr ⟨n, hn⟩
  let z : ZPlane := fun i =>
    if i = 0 then ⌊(d : ℝ) * x.re⌋ else ⌊(d : ℝ) * x.im⌋
  have hz0 : z 0 = ⌊(d : ℝ) * x.re⌋ := by simp [z]
  have hz1 : z 1 = ⌊(d : ℝ) * x.im⌋ := by simp [z]
  have hrelo_le : (z 0 : ℝ) / (d : ℝ) ≤ x.re := by
    apply (div_le_iff₀ hdR).2
    rw [hz0]
    simpa [mul_comm] using (Int.floor_le ((d : ℝ) * x.re))
  have hrelo : (z 0 : ℝ) / (d : ℝ) < x.re := by
    apply lt_of_le_of_ne hrelo_le
    intro heq
    apply hxre (z 0)
    rw [← heq]
    norm_num
  have hrehi : x.re < (z 0 : ℝ) / (d : ℝ) + 1 / (d : ℝ) := by
    rw [← add_div]
    apply (lt_div_iff₀ hdR).2
    rw [hz0]
    simp [mul_comm]
  have himlo_le : (z 1 : ℝ) / (d : ℝ) ≤ x.im := by
    apply (div_le_iff₀ hdR).2
    rw [hz1]
    simpa [mul_comm] using (Int.floor_le ((d : ℝ) * x.im))
  have himlo : (z 1 : ℝ) / (d : ℝ) < x.im := by
    apply lt_of_le_of_ne himlo_le
    intro heq
    apply hxim (z 1)
    rw [← heq]
    norm_num
  have himhi : x.im < (z 1 : ℝ) / (d : ℝ) + 1 / (d : ℝ) := by
    rw [← add_div]
    apply (lt_div_iff₀ hdR).2
    rw [hz1]
    simp [mul_comm]
  refine ⟨z, ?_, ?_⟩
  · change (rationalScale d z).re < x.re ∧
      x.re < (rationalScale d z).re + (1 / d : ℝ) ∧
      (rationalScale d z).im < x.im ∧
      x.im < (rationalScale d z).im + (1 / d : ℝ)
    simp only [rationalScale]
    exact ⟨hrelo, hrehi, himlo, himhi⟩
  · intro w hw
    funext i
    fin_cases i
    · have hlo := hw.1
      have hhi := hw.2.1
      have hwfloor : ⌊(d : ℝ) * x.re⌋ = w 0 := by
        apply Int.floor_eq_iff.mpr
        constructor
        · have := (div_lt_iff₀ hdR).mp hlo
          simpa [rationalScale, mul_comm] using this.le
        · have hhi' : x.re < ((w 0 : ℝ) + 1) / (d : ℝ) := by
            rw [add_div]
            exact hhi
          have := (lt_div_iff₀ hdR).mp hhi'
          simpa [mul_comm] using this
      exact hwfloor.symm.trans hz0
    · have hlo := hw.2.2.1
      have hhi := hw.2.2.2
      have hwfloor : ⌊(d : ℝ) * x.im⌋ = w 1 := by
        apply Int.floor_eq_iff.mpr
        constructor
        · have := (div_lt_iff₀ hdR).mp hlo
          simpa [rationalScale, mul_comm] using this.le
        · have hhi' : x.im < ((w 1 : ℝ) + 1) / (d : ℝ) := by
            rw [add_div]
            exact hhi
          have := (lt_div_iff₀ hdR).mp hhi'
          simpa [mul_comm] using this
      exact hwfloor.symm.trans hz1

private theorem local_volume_re_eq_zero (c : ℝ) :
    volume {x : Tiling.Plane | x.re = c} = 0 := by
  have hset : {x : Tiling.Plane | x.re = c} =
      Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (Set.univ : Set ℝ)) := by
    ext x
    simp
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage]
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  · exact ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet

private theorem local_volume_im_eq_zero (c : ℝ) :
    volume {x : Tiling.Plane | x.im = c} = 0 := by
  have hset : {x : Tiling.Plane | x.im = c} =
      Complex.measurableEquivRealProd ⁻¹' ((Set.univ : Set ℝ) ×ˢ {c}) := by
    ext x
    simp
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage]
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  · exact (MeasurableSet.univ.prod (measurableSet_singleton c)).nullMeasurableSet

private theorem local_meshLines_volume_zero {d : ℕ} (_hd : 0 < d) :
    volume (meshLines d) = 0 := by
  have hlines : meshLines d =
      (⋃ n : ℤ, {x : Tiling.Plane | x.re = (((n : ℚ) / (d : ℚ)) : ℝ)}) ∪
        (⋃ n : ℤ, {x : Tiling.Plane | x.im = (((n : ℚ) / (d : ℚ)) : ℝ)}) := by
    ext x
    simp [meshLines]
  rw [hlines, measure_union_null]
  · exact measure_iUnion_null fun n ↦ local_volume_re_eq_zero _
  · exact measure_iUnion_null fun n ↦ local_volume_im_eq_zero _

private theorem local_rawCellUnion_aeEq_regularizedCellUnion {d : ℕ} (hd : 0 < d)
    (A : Set ZPlane) :
    (⋃ z : A, meshCell d z.1) =ᵐ[volume] regularizedCellUnion d A := by
  let U : Set Tiling.Plane := ⋃ z : A, meshCell d z.1
  have hUopen : IsOpen U := isOpen_iUnion fun z ↦ by
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hcellopen : ∀ z : ZPlane, IsOpen (meshCell d z) := by
    intro z
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  apply ae_iff.mpr
  apply measure_mono_null _ (local_meshLines_volume_zero hd)
  intro x hx
  by_contra hxline
  apply hx
  apply propext
  change (x ∈ U) ↔ x ∈ regularizedCellUnion d A
  constructor
  · intro hxU
    exact (hUopen.subset_interior_iff.mpr subset_closure) hxU
  · intro hxreg
    obtain ⟨z, hxz, _hzunique⟩ := local_offMesh_existsUnique_meshCell hd x hxline
    have hxcl : x ∈ closure U := interior_subset hxreg
    rcases (mem_closure_iff.mp hxcl) (meshCell d z) (hcellopen z) hxz with
      ⟨y, hyz, hyU⟩
    rcases Set.mem_iUnion.mp hyU with ⟨w, hyw⟩
    have hzw : z = w.1 := by
      by_contra hne
      have hdisj := meshCell_pairwiseDisjoint hd
        (show z ∈ (Set.univ : Set ZPlane) by simp)
        (show w.1 ∈ (Set.univ : Set ZPlane) by simp) hne
      exact Set.disjoint_left.mp hdisj hyz hyw
    change x ∈ ⋃ z : A, meshCell d z.1
    let za : A := ⟨z, hzw ▸ w.2⟩
    exact Set.mem_iUnion_of_mem za hxz

private theorem local_offMesh_mem_regularizedCellUnion_iff
    {d : ℕ} (hd : 0 < d) (A : Set ZPlane) (x : Tiling.Plane)
    (hx : x ∉ meshLines d) :
    (x ∈ regularizedCellUnion d A ↔
      ∃ z ∈ A, x ∈ meshCell d z) := by
  let U : Set Tiling.Plane := ⋃ z : A, meshCell d z.1
  have hUopen : IsOpen U := isOpen_iUnion fun z ↦ by
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  obtain ⟨z, hxz, _hzunique⟩ := local_offMesh_existsUnique_meshCell hd x hx
  constructor
  · intro hxreg
    have hxcl : x ∈ closure U := interior_subset hxreg
    rcases (mem_closure_iff.mp hxcl) (meshCell d z)
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          ((isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const)))) hxz with
      ⟨y, hyz, hyU⟩
    rcases Set.mem_iUnion.mp hyU with ⟨w, hyw⟩
    have hzw : z = w.1 := by
      by_contra hne
      exact Set.disjoint_left.mp
        (meshCell_pairwiseDisjoint hd
          (show z ∈ (Set.univ : Set ZPlane) by simp)
          (show w.1 ∈ (Set.univ : Set ZPlane) by simp) hne) hyz hyw
    exact ⟨z, hzw ▸ w.2, hxz⟩
  · rintro ⟨z, hzA, hxz⟩
    change x ∈ interior (closure U)
    apply hUopen.subset_interior_iff.mpr subset_closure
    exact Set.mem_iUnion_of_mem ⟨z, hzA⟩ hxz

private theorem openCarrier_eq_regularizedCellUnion_of_unitCell_ae
    {K : Region} {F : Finset ZPlane}
    (hAE : K.openCarrier =ᵐ[volume] ⋃ f : F,
      Tiling.RationalPolygonal.integerPoint (f : ZPlane) +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I))) :
    K.openCarrier = regularizedCellUnion 1 (F : Set ZPlane) := by
  have hcell (z : ZPlane) :
      meshCell 1 z = Tiling.RationalPolygonal.integerPoint z +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I)) := by
    ext x
    have hrect : interior (Complex.Rectangle 0 (1 + Complex.I)) =
        {w : Tiling.Plane | 0 < w.re ∧ w.re < 1 ∧ 0 < w.im ∧ w.im < 1} := by
      have hr : Complex.Rectangle 0 (1 + Complex.I) = Icc 0 1 ×ℂ Icc 0 1 := by
        ext w
        simp [Complex.Rectangle]
      rw [hr, Complex.interior_reProdIm]
      ext w
      change (w.re ∈ interior (Icc 0 1) ∧ w.im ∈ interior (Icc 0 1)) ↔ _
      simp [interior_Icc]
      tauto
    rw [hrect]
    simp [meshCell, rationalScale, Tiling.RationalPolygonal.integerPoint,
      Set.mem_vadd_set_iff_neg_vadd_mem]
  have hraw : K.openCarrier =ᵐ[volume] ⋃ f : F,
      meshCell 1 (f : ZPlane) := by
    have hu : (⋃ f : F,
        Tiling.RationalPolygonal.integerPoint (f : ZPlane) +ᵥ
          interior (Complex.Rectangle 0 (1 + Complex.I))) =
        ⋃ f : F, meshCell 1 (f : ZPlane) := by
      apply iUnion_congr
      intro f
      exact (hcell f.1).symm
    exact hAE.trans (Filter.EventuallyEq.of_eq hu)
  apply regularOpen_eq_of_aeEq K.openCarrier_regularOpen.1
    K.openCarrier_regularOpen.2 isOpen_interior
  · change interior (closure (interior (closure
      (⋃ i : (F : Set ZPlane), meshCell 1 i)))) =
      interior (closure (⋃ i : (F : Set ZPlane), meshCell 1 i))
    exact interior_closure_idem
  · exact hraw.trans (local_rawCellUnion_aeEq_regularizedCellUnion (d := 1)
      (by simp) (F : Set ZPlane))

private theorem local_discrete_representation_exists
    {K : Region} {A : Set Tiling.Plane} {F : Finset ZPlane}
    (_hFne : F.Nonempty) (hAint : ∀ a ∈ A,
      Tiling.RationalPolygonal.IsIntegerPoint a)
    (hTile : TilesOn K A Set.univ)
    (hKreg : K.openCarrier = regularizedCellUnion 1 (F : Set ZPlane))
    (q : ZPlane) :
    ∃ f ∈ F, q - f ∈ Tiling.RationalPolygonal.integerPoint ⁻¹' A := by
  let Cover : Set Tiling.Plane := ⋃ s : A,
    (s : Tiling.Plane) +ᵥ K.openCarrier
  let Bad : Set Tiling.Plane := {x | x ∉ Cover}
  let MeshBad : Set Tiling.Plane := ⋃ s : A,
    (s : Tiling.Plane) +ᵥ meshLines 1
  let _ : Countable A := hTile.1.to_subtype
  have hcover : ∀ᵐ x ∂volume, x ∈ Cover := by
    filter_upwards [hTile.2.2] with x hx
    rcases hx.mp (Set.mem_univ x) with ⟨s, hs⟩
    exact Set.mem_iUnion.mpr ⟨s, hs⟩
  have hbad : volume Bad = 0 := by
    apply ae_iff.mp hcover
  have hmeshbad : volume MeshBad = 0 := by
    apply measure_iUnion_null
    intro s
    simpa only [MeasureTheory.measure_vadd] using
      (local_meshLines_volume_zero (d := 1) (by simp))
  have hcellopen : IsOpen (meshCell 1 q) := by
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hcellpos : volume (meshCell 1 q) ≠ 0 :=
    hcellopen.measure_ne_zero volume (meshCell_nonempty (by simp) q)
  have hsel : ∃ x ∈ meshCell 1 q, x ∉ Bad ∪ MeshBad := by
    by_contra hnone
    have hsub : meshCell 1 q ⊆ Bad ∪ MeshBad := by
      intro x hx
      by_contra hnot
      exact hnone ⟨x, hx, hnot⟩
    have hzero : volume (Bad ∪ MeshBad) = 0 := measure_union_null hbad hmeshbad
    exact hcellpos (measure_mono_null hsub hzero)
  obtain ⟨x, hxq, hxnot⟩ := hsel
  have hxCover : x ∈ Cover := by
    by_contra hnot
    exact hxnot (Or.inl hnot)
  rcases Set.mem_iUnion.mp hxCover with ⟨a, hxa⟩
  have hxoff : x - (a : Tiling.Plane) ∉ meshLines 1 := by
    intro hline
    apply hxnot
    apply Or.inr
    apply Set.mem_iUnion_of_mem a
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hline
  have hxaK : x - (a : Tiling.Plane) ∈ K.openCarrier := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hxa
  have hxaReg : x - (a : Tiling.Plane) ∈ regularizedCellUnion 1 (F : Set ZPlane) := by
    rw [← hKreg]
    exact hxaK
  obtain ⟨f, hfF, hxf⟩ :=
    (local_offMesh_mem_regularizedCellUnion_iff (d := 1) (by simp)
      (F : Set ZPlane) (x - (a : Tiling.Plane)) hxoff).mp hxaReg
  obtain ⟨a₀, ha₀⟩ :=
    Tiling.RationalPolygonal.mem_integerLattice_iff.mp
      (hAint (a : Tiling.Plane) a.property)
  have hcellvadd : x ∈ Tiling.RationalPolygonal.integerPoint a₀ +ᵥ meshCell 1 f := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [ha₀, vadd_eq_add, sub_eq_add_neg, add_comm] using hxf
  have hcelladd : meshCell 1 (f + a₀) =
      Tiling.RationalPolygonal.integerPoint a₀ +ᵥ meshCell 1 f := by
    have hscale : rationalScale 1 a₀ =
        Tiling.RationalPolygonal.integerPoint a₀ := by
      apply Complex.ext <;>
        simp [rationalScale, Tiling.RationalPolygonal.integerPoint]
    rw [← hscale]
    exact meshCell_add (d := 1) (by simp) f a₀
  have hxfq : x ∈ meshCell 1 (f + a₀) := by
    rw [hcelladd]
    exact hcellvadd
  have hqeq : q = f + a₀ := by
    by_contra hne
    exact Set.disjoint_left.mp
      (meshCell_pairwiseDisjoint (d := 1) (by simp)
        (show q ∈ (Set.univ : Set ZPlane) by simp)
        (show f + a₀ ∈ (Set.univ : Set ZPlane) by simp) hne) hxq hxfq
  have hqa : q - f = a₀ := by rw [hqeq]; abel
  refine ⟨f, hfF, ?_⟩
  change Tiling.RationalPolygonal.integerPoint (q - f) ∈ A
  rw [hqa, ha₀]
  exact a.property

private theorem local_discrete_representation_unique
    {K : Region} {A : Set Tiling.Plane} {F : Finset ZPlane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A))
    (hKreg : K.openCarrier = regularizedCellUnion 1 (F : Set ZPlane))
    {q f g : ZPlane} (hfF : f ∈ F)
    (hfA : q - f ∈ Tiling.RationalPolygonal.integerPoint ⁻¹' A)
    (hgF : g ∈ F)
    (hgA : q - g ∈ Tiling.RationalPolygonal.integerPoint ⁻¹' A) :
    f = g := by
  obtain ⟨x, hx⟩ := meshCell_nonempty (d := 1) (by simp) q
  have hcellf : meshCell 1 (f + (q - f)) =
      Tiling.RationalPolygonal.integerPoint (q - f) +ᵥ meshCell 1 f := by
    have hscale : rationalScale 1 (q - f) =
        Tiling.RationalPolygonal.integerPoint (q - f) := by
      apply Complex.ext <;>
        simp [rationalScale, Tiling.RationalPolygonal.integerPoint]
    rw [← hscale]
    exact meshCell_add (d := 1) (by simp) f (q - f)
  have hcellg : meshCell 1 (g + (q - g)) =
      Tiling.RationalPolygonal.integerPoint (q - g) +ᵥ meshCell 1 g := by
    have hscale : rationalScale 1 (q - g) =
        Tiling.RationalPolygonal.integerPoint (q - g) := by
      apply Complex.ext <;>
        simp [rationalScale, Tiling.RationalPolygonal.integerPoint]
    rw [← hscale]
    exact meshCell_add (d := 1) (by simp) g (q - g)
  have hxf : x ∈ Tiling.RationalPolygonal.integerPoint (q - f) +ᵥ
      meshCell 1 f := by
    rw [← hcellf]
    simpa only [add_sub_cancel] using hx
  have hxg : x ∈ Tiling.RationalPolygonal.integerPoint (q - g) +ᵥ
      meshCell 1 g := by
    rw [← hcellg]
    simpa only [add_sub_cancel] using hx
  have hsubf : meshCell 1 f ⊆ regularizedCellUnion 1 (F : Set ZPlane) :=
    (meshCell_subset_regularizedCellUnion_iff (d := 1) (by simp)
      (F : Set ZPlane) f).mpr hfF
  have hsubg : meshCell 1 g ⊆ regularizedCellUnion 1 (F : Set ZPlane) :=
    (meshCell_subset_regularizedCellUnion_iff (d := 1) (by simp)
      (F : Set ZPlane) g).mpr hgF
  have hxfK : x ∈ (Tiling.RationalPolygonal.integerPoint (q - f)) +ᵥ
      K.openCarrier := by
    rw [hKreg]
    exact Set.vadd_set_mono hsubf hxf
  have hxgK : x ∈ (Tiling.RationalPolygonal.integerPoint (q - g)) +ᵥ
      K.openCarrier := by
    rw [hKreg]
    exact Set.vadd_set_mono hsubg hxg
  by_contra hfg
  have hcent : Tiling.RationalPolygonal.integerPoint (q - f) ≠
      Tiling.RationalPolygonal.integerPoint (q - g) := by
    intro heq
    have hsubeq : q - f = q - g :=
      Tiling.RationalPolygonal.integerPoint_injective heq
    exact hfg (sub_right_injective hsubeq)
  have hdisj := (isPacking_iff_openCarrier_disjoint K A).mp hpacking
    (show Tiling.RationalPolygonal.integerPoint (q - f) ∈ A from hfA)
    (show Tiling.RationalPolygonal.integerPoint (q - g) ∈ A from hgA)
    hcent
  exact Set.disjoint_left.mp hdisj hxfK hxgK

private theorem gridCellTiling_of_unitCell_ae
    {K : Region} {A : Set Tiling.Plane} {F : Finset ZPlane}
    (hFne : F.Nonempty)
    (hAint : ∀ a ∈ A, Tiling.RationalPolygonal.IsIntegerPoint a)
    (hTile : TilesOn K A Set.univ)
    (hAE : K.openCarrier =ᵐ[volume] ⋃ f : F,
      Tiling.RationalPolygonal.integerPoint (f : ZPlane) +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I))) :
    TranslationalTilings.Tiles F
      (Tiling.RationalPolygonal.integerPoint ⁻¹' A) Set.univ := by
  have hKreg := openCarrier_eq_regularizedCellUnion_of_unitCell_ae hAE
  apply Tiling.RationalPolygonal.tilesUniverse_of_existsUnique
  intro q
  obtain ⟨f, hfF, hfA⟩ :=
    local_discrete_representation_exists hFne hAint hTile hKreg q
  refine ⟨f, ⟨hfF, hfA⟩, ?_⟩
  intro g hg
  exact (local_discrete_representation_unique (q := q) (f := f) (g := g)
    hTile.2.1 hKreg hfF hfA hg.1 hg.2).symm

end Tiling.AxisParallel.RationalMesh

namespace Tiling.AxisParallel.Continuous

open Tiling.AxisParallel
open Tiling.AxisParallel.RationalMesh
open Tiling.RationalPolygonal

private theorem gridCertificate_regularized_eq
    {K : Region} {F : Finset TranslationalTilings.Plane}
    (hKae : K.openCarrier =ᵐ[volume] ⋃ f : F,
      integerPoint (f : TranslationalTilings.Plane) +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I))) :
    K.openCarrier = regularizedCellUnion 1 (F : Set TranslationalTilings.Plane) := by
  let U : Set Tiling.Plane := ⋃ f : F, meshCell 1 (f : TranslationalTilings.Plane)
  have hcell (z : TranslationalTilings.Plane) :
      meshCell 1 z = integerPoint z +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I)) := by
    have hrect : interior (Complex.Rectangle 0 (1 + Complex.I)) =
        {w : Tiling.Plane | 0 < w.re ∧ w.re < 1 ∧ 0 < w.im ∧ w.im < 1} := by
      have hr : Complex.Rectangle 0 (1 + Complex.I) = Icc 0 1 ×ℂ Icc 0 1 := by
        ext w
        simp [Complex.Rectangle]
      rw [hr, Complex.interior_reProdIm]
      ext w
      change (w.re ∈ interior (Icc 0 1) ∧ w.im ∈ interior (Icc 0 1)) ↔ _
      simp [interior_Icc]
      tauto
    ext x
    rw [hrect]
    simp [meshCell, rationalScale, integerPoint,
      Set.mem_vadd_set_iff_neg_vadd_mem]
  have hUeq : U = ⋃ f : F,
      integerPoint (f : TranslationalTilings.Plane) +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I)) := by
    apply iUnion_congr
    intro f
    exact hcell f
  have hUae : K.openCarrier =ᵐ[volume] U := by
    filter_upwards [hKae] with x hx
    exact hx.trans (congrFun hUeq.symm x)
  have hVopen : IsOpen (regularizedCellUnion 1 (F : Set TranslationalTilings.Plane)) :=
    isOpen_interior
  have hclosure := closure_eq_of_open_ae_local K.openCarrier_regularOpen.1
    (by exact isOpen_iUnion (fun (_f : F) => by
      simp only [meshCell]
      exact (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          ((isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const))))) hUae
  change K.openCarrier = interior (closure U)
  rw [← K.openCarrier_regularOpen.2, hclosure]

private theorem vertex_one_coordinate_integral_of_grid_certificate
    {K : Region} {F : Finset TranslationalTilings.Plane}
    (hKae : K.openCarrier =ᵐ[volume] ⋃ f : F,
      integerPoint (f : TranslationalTilings.Plane) +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I))) :
    ∀ v ∈ K.vertices,
      (∃ n : ℤ, v.re = n) ∨ ∃ n : ℤ, v.im = n := by
  intro v hv
  have hfront : frontier K.openCarrier ⊆ meshLines 1 := by
    rw [gridCertificate_regularized_eq hKae]
    exact frontier_regularizedCellUnion_subset_meshLines (d := 1) (by norm_num)
      (F : Set TranslationalTilings.Plane)
  have hvfront := Tiling.AxisParallel.IntrinsicVertices.region_vertices_subset_frontier K hv
  have hline := hfront hvfront
  change (∃ n : ℤ, v.re = (((n : ℚ) / (1 : ℚ)) : ℝ)) ∨
    ∃ n : ℤ, v.im = (((n : ℚ) / (1 : ℚ)) : ℝ) at hline
  rcases hline with ⟨n, hn⟩ | ⟨n, hn⟩
  · left
    refine ⟨n, ?_⟩
    norm_num at hn ⊢
    exact hn
  · right
    refine ⟨n, ?_⟩
    norm_num at hn ⊢
    exact hn

private def coordinateSwapInteger_seam :
    TranslationalTilings.Plane → TranslationalTilings.Plane :=
  fun z i => if i = 0 then z 1 else z 0

private theorem coordinateSwap_integerPoint_seam (z : TranslationalTilings.Plane) :
    Tiling.AxisParallel.coordinateSwap (integerPoint z) = integerPoint
      (coordinateSwapInteger_seam z) := by
  apply Complex.ext <;> simp [Tiling.AxisParallel.coordinateSwap,
    coordinateSwapInteger_seam, integerPoint]

private theorem coordinateSwap_unitRectangle_seam :
    Tiling.AxisParallel.coordinateSwap ''
        interior (Complex.Rectangle 0 (1 + Complex.I)) =
      interior (Complex.Rectangle 0 (1 + Complex.I)) := by
  have hrect : interior (Complex.Rectangle 0 (1 + Complex.I)) =
      {w : Tiling.Plane | 0 < w.re ∧ w.re < 1 ∧ 0 < w.im ∧ w.im < 1} := by
    have hr : Complex.Rectangle 0 (1 + Complex.I) = Icc 0 1 ×ℂ Icc 0 1 := by
      ext w
      simp [Complex.Rectangle]
    rw [hr, Complex.interior_reProdIm]
    ext w
    change (w.re ∈ interior (Icc 0 1) ∧ w.im ∈ interior (Icc 0 1)) ↔ _
    simp [interior_Icc]
    tauto
  rw [hrect]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [Set.mem_ofPred_eq] at hw ⊢
    simpa [Tiling.AxisParallel.coordinateSwap] using
      (show 0 < w.im ∧ w.im < 1 ∧ 0 < w.re ∧ w.re < 1 from
        ⟨hw.2.2.1, hw.2.2.2, hw.1, hw.2.1⟩)
  · intro hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    refine ⟨Tiling.AxisParallel.coordinateSwap z, ?_,
      Tiling.AxisParallel.coordinateSwap_apply_apply z⟩
    simpa [Tiling.AxisParallel.coordinateSwap] using
      (show 0 < z.im ∧ z.im < 1 ∧ 0 < z.re ∧ z.re < 1 from
        ⟨hz.2.2.1, hz.2.2.2, hz.1, hz.2.1⟩)


private theorem coordinateSwap_unitCell_seam
    (z : TranslationalTilings.Plane) :
    Tiling.AxisParallel.coordinateSwap ''
        (integerPoint z +ᵥ interior (Complex.Rectangle 0 (1 + Complex.I))) =
      integerPoint (coordinateSwapInteger_seam z) +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I)) := by
  rw [Tiling.AxisParallel.coordinateSwap_image_vadd, coordinateSwap_integerPoint_seam,
    coordinateSwap_unitRectangle_seam]

private theorem integerRegion_is_raster_of_certificate
    {K : Region} {T : Set Tiling.Plane}
    (I : PlateCompatibleIntegerization K T) :
    (I.discreteTile : Set TranslationalTilings.Plane) =
      rasterCells 1 I.integerRegion.openCarrier := by
  have hmesh : OnRationalMesh 1 I.integerRegion.vertices := by
    intro v hv
    obtain ⟨z, hz⟩ := mem_integerLattice_iff.mp (I.integerVertices v hv)
    refine ⟨z, ?_⟩
    apply Complex.ext
    · simpa [rationalScale] using congrArg Complex.re hz
    · simpa [rationalScale] using congrArg Complex.im hz
  obtain ⟨G, hGne, hGraster, hGae, _hGreg⟩ :=
    exists_regionRaster (K := I.integerRegion) (d := 1) (by simp) hmesh
  have hcell (z : TranslationalTilings.Plane) :
      meshCell 1 z = integerPoint z +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I)) := by
    have hrect : interior (Complex.Rectangle 0 (1 + Complex.I)) =
        {w : Tiling.Plane | 0 < w.re ∧ w.re < 1 ∧ 0 < w.im ∧ w.im < 1} := by
      have hr : Complex.Rectangle 0 (1 + Complex.I) = Icc 0 1 ×ℂ Icc 0 1 := by
        ext w
        simp [Complex.Rectangle]
      rw [hr, Complex.interior_reProdIm]
      ext w
      change (w.re ∈ interior (Icc 0 1) ∧ w.im ∈ interior (Icc 0 1)) ↔ _
      simp [interior_Icc]
      tauto
    ext x
    rw [hrect]
    simp [meshCell, rationalScale, integerPoint,
      Set.mem_vadd_set_iff_neg_vadd_mem]
  have hFae : I.integerRegion.openCarrier =ᵐ[volume]
      ⋃ f : I.discreteTile, meshCell 1 (f : TranslationalTilings.Plane) := by
    have hu : (⋃ f : I.discreteTile,
        integerPoint (f : TranslationalTilings.Plane) +ᵥ
          interior (Complex.Rectangle 0 (1 + Complex.I))) =
        ⋃ f : I.discreteTile, meshCell 1 (f : TranslationalTilings.Plane) := by
      apply iUnion_congr
      intro f
      exact (hcell f).symm
    filter_upwards [I.discreteTile_realizes_integerRegion] with x hx
    exact hx.trans (congrFun hu x)
  have hEq : (I.discreteTile : Set TranslationalTilings.Plane) = G := by
    apply meshCell_union_finset_eq_of_ae_eq
    filter_upwards [hFae, hGae] with x hxF hxG
    exact hxF.symm.trans hxG
  exact hEq.trans hGraster

private theorem normalized_carrier_support_eq
    {K : Region} {T : Set Tiling.Plane}
    (I : PlateCompatibleIntegerization K T)
    (S : Set TranslationalTilings.Plane) :
    regularSupport I.integerRegion (integerPoint '' S) =
      regularizedCellUnion 1 (discreteCarrier I.discreteTile S) := by
  have hmesh : OnRationalMesh 1 I.integerRegion.vertices := by
    intro v hv
    obtain ⟨z, hz⟩ := mem_integerLattice_iff.mp (I.integerVertices v hv)
    refine ⟨z, ?_⟩
    apply Complex.ext
    · simpa [rationalScale] using congrArg Complex.re hz
    · simpa [rationalScale] using congrArg Complex.im hz
  have hF := integerRegion_is_raster_of_certificate I
  have hscale : rationalScale 1 '' S = integerPoint '' S := by
    ext z
    constructor <;> rintro ⟨a, ha, rfl⟩ <;> refine ⟨a, ha, ?_⟩ <;>
      apply Complex.ext <;> simp [rationalScale, integerPoint]
  rw [← hscale]
  exact regularSupport_rationalScale_image (K := I.integerRegion)
    (d := 1) (by simp) hmesh I.discreteTile hF S

private theorem slab_of_vertical_invariant
    {K : Region} {S : Set Tiling.Plane}
    (hS : ∀ y : ℝ, ((y : ℂ) * Complex.I) +ᵥ regularSupport K S =
      regularSupport K S) :
    ∃ X : Set ℝ, X = interior (closure X) ∧
      regularSupport K S = Complex.re ⁻¹' X := by
  obtain ⟨X, hX⟩ := (verticalInvariant_iff_product (regularSupport K S)).mp hS
  have hXreg : interior (closure X) = X := by
    have hpre : Complex.re ⁻¹' interior (closure X) = Complex.re ⁻¹' X := by
      calc
        Complex.re ⁻¹' interior (closure X) =
            interior (Complex.re ⁻¹' closure X) :=
          (Complex.interior_preimage_re _).symm
        _ = interior (closure (Complex.re ⁻¹' X)) := by
          rw [Complex.closure_preimage_re]
        _ = interior (closure (regularSupport K S)) := by
          change interior (closure {z : Tiling.Plane | z.re ∈ X}) = _
          rw [hX]
        _ = regularSupport K S := (regularSupport_isRegularOpen K S).2
        _ = Complex.re ⁻¹' X := hX
    apply (Set.preimage_injective.mpr ?_) hpre
    intro r
    exact ⟨(r : ℂ), rfl⟩
  exact ⟨X, hXreg.symm, hX⟩

private theorem centres_nonempty_local
    {K : Region} {A : Set Tiling.Plane} (P : VerticalPlate K A) :
    P.centres.Nonempty := by
  obtain ⟨t, ht⟩ := P.nonempty_supp
  exact ⟨t.1, t, ht, rfl⟩

private theorem plate_image_eq_of_invariant_bridge
    {K : Region} {A : Set Tiling.Plane}
    {F : Finset TranslationalTilings.Plane}
    (hTile : TilesOn K A Set.univ)
    (hTiles : TranslationalTilings.Tiles F
      (integerPoint ⁻¹' A) Set.univ)
    (hA : ∀ a ∈ A, IsIntegerPoint a)
    (hbridge : ∀ S : Set Tiling.Plane, S ⊆ A →
      ((∀ y : ℝ, ((y : ℂ) * Complex.I) +ᵥ regularSupport K S =
          regularSupport K S) ↔
        DiscretePeriodicBy (discreteCarrier F (integerPoint ⁻¹' S))
          Tiling.AxisParallel.Discrete.verticalDiscreteUnit))
    (P : VerticalPlate K A) :
    ∃ C : QuakePlate F (integerPoint ⁻¹' A)
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit,
      P.centres = integerPoint '' quakePlateTranslations C := by
  let Aint : Set TranslationalTilings.Plane := integerPoint ⁻¹' A
  let v : TranslationalTilings.Plane :=
    Tiling.AxisParallel.Discrete.verticalDiscreteUnit
  have hPsub : P.centres ⊆ A := by
    rintro x ⟨t, ht, rfl⟩
    exact t.property
  obtain ⟨t, htP⟩ := centres_nonempty_local P
  have htA : t ∈ A := hPsub htP
  obtain ⟨z, hz⟩ := mem_integerLattice_iff.mp (hA t htA)
  let a : Aint := ⟨z, by
    change integerPoint z ∈ A
    rw [hz]
    exact htA⟩
  have haP : integerPoint (a : TranslationalTilings.Plane) ∈ P.centres := by
    simpa [a, hz] using htP
  let C : QuakePlate F Aint v :=
    (quakeGraph F Aint v).connectedComponentMk a
  let D : Set TranslationalTilings.Plane := integerPoint ⁻¹' P.centres
  have hDsub : D ⊆ Aint := by
    intro b hb
    change integerPoint (b : TranslationalTilings.Plane) ∈ P.centres at hb
    change integerPoint (b : TranslationalTilings.Plane) ∈ A
    exact hPsub hb
  have hPinv : ∀ y : ℝ,
      ((y : ℂ) * Complex.I) +ᵥ regularSupport K P.centres =
        regularSupport K P.centres := by
    obtain ⟨hbase, hX⟩ := VerticalPlate.support_isVerticalSlab hTile P
    have hreg : regularSupport K P.centres = P.support :=
      P.support_eq_regularSupport.symm
    have hs : ∀ y : ℝ, ((y : ℂ) * Complex.I) +ᵥ P.support = P.support :=
      (verticalInvariant_iff_product P.support).mpr ⟨P.base, hX⟩
    intro y
    calc
      ((y : ℂ) * Complex.I) +ᵥ regularSupport K P.centres =
          ((y : ℂ) * Complex.I) +ᵥ P.support := congrArg _ hreg
      _ = P.support := hs y
      _ = regularSupport K P.centres := hreg.symm
  have hDperiod : DiscretePeriodicBy (discreteCarrier F D) v := by
    apply (hbridge P.centres hPsub).mp hPinv
  have hCsub : quakePlateTranslations C ⊆ D := by
    apply quakePlateTranslations_subset_of_mem_periodic hTiles C hDsub hDperiod
      (p := (a : TranslationalTilings.Plane))
    · exact mem_quakePlateTranslations_mk a
    · change integerPoint (a : TranslationalTilings.Plane) ∈ P.centres
      exact haP
  let Q : Set Tiling.Plane := integerPoint '' quakePlateTranslations C
  have hQsub : Q ⊆ P.centres := by
    intro x hx
    rcases hx with ⟨b, hb, hbx⟩
    have hbP : integerPoint (b : TranslationalTilings.Plane) ∈ P.centres := by
      simpa [D] using hCsub hb
    simpa [hbx] using hbP
  have hQne : Q.Nonempty := by
    exact ⟨integerPoint (a : TranslationalTilings.Plane),
      ⟨a, mem_quakePlateTranslations_mk a, rfl⟩⟩
  have hpre : integerPoint ⁻¹' Q = quakePlateTranslations C := by
    ext b
    constructor
    · rintro ⟨c, hc, hcb⟩
      have hbc : b = c := (integerPoint_injective hcb).symm
      simpa [hbc] using hc
    · intro hb
      exact ⟨b, hb, rfl⟩
  have hQperiod : DiscretePeriodicBy (discreteCarrier F (integerPoint ⁻¹' Q)) v := by
    rw [hpre]
    exact quakePlateCarrier_periodic hTiles C
  obtain ⟨X, hXreg, hX⟩ := slab_of_vertical_invariant
    ((hbridge Q (hQsub.trans hPsub)).mpr hQperiod)
  obtain ⟨hPne, hPsub', _, hPmin⟩ := VerticalPlate.minimal hTile P
  have hPQ := hPmin Q hQne hQsub ⟨X, hXreg, hX⟩
  exact ⟨C, hPQ.symm⟩

private theorem vertical_plate_eq_of_centres_local
    {K : Region} {A : Set Tiling.Plane}
    {P Q : VerticalPlate K A} (hPQ : P.centres = Q.centres) : P = Q := by
  obtain ⟨t, ht⟩ := centres_nonempty_local P
  rcases ht with ⟨tA, ht, rfl⟩
  have hP := (SimpleGraph.ConnectedComponent.mem_supp_iff P tA).mp ht
  have hQmem : (tA : Tiling.Plane) ∈ Q.centres := by
    rw [← hPQ]
    exact ⟨tA, ht, rfl⟩
  rcases hQmem with ⟨u, hu, hut⟩
  have hut' : u = tA := Subtype.ext hut
  subst u
  have hQ := (SimpleGraph.ConnectedComponent.mem_supp_iff Q tA).mp hu
  exact hP.symm.trans hQ

private theorem quake_plate_eq_of_translation_sets_local
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    {v : TranslationalTilings.Plane}
    {C D : QuakePlate F A v}
    (hCD : quakePlateTranslations C = quakePlateTranslations D) : C = D := by
  obtain ⟨a, ha⟩ := C.nonempty_supp
  have haC : (a : TranslationalTilings.Plane) ∈ quakePlateTranslations C := by
    exact ⟨a.property, (SimpleGraph.ConnectedComponent.mem_supp_iff C a).mp ha⟩
  have haD : (a : TranslationalTilings.Plane) ∈ quakePlateTranslations D := by
    rw [← hCD]
    exact haC
  have hC := (SimpleGraph.ConnectedComponent.mem_supp_iff C a).mp ha
  have hD := (SimpleGraph.ConnectedComponent.mem_supp_iff D a).mp
    (haD.2)
  exact hC.symm.trans hD

private theorem plate_equiv_of_invariant_bridge
    {K : Region} {A : Set Tiling.Plane}
    {F : Finset TranslationalTilings.Plane}
    (hTile : TilesOn K A Set.univ)
    (hTiles : TranslationalTilings.Tiles F (integerPoint ⁻¹' A) Set.univ)
    (hA : ∀ a ∈ A, IsIntegerPoint a)
    (hbridge : ∀ S : Set Tiling.Plane, S ⊆ A →
      ((∀ y : ℝ, ((y : ℂ) * Complex.I) +ᵥ regularSupport K S =
          regularSupport K S) ↔
        DiscretePeriodicBy (discreteCarrier F (integerPoint ⁻¹' S))
          Tiling.AxisParallel.Discrete.verticalDiscreteUnit)) :
    ∃ e : VerticalPlate K A ≃ QuakePlate F (integerPoint ⁻¹' A)
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit,
      ∀ P : VerticalPlate K A, ∀ a : integerPoint ⁻¹' A,
        integerPoint (a : TranslationalTilings.Plane) ∈ P.centres ↔
          (a : TranslationalTilings.Plane) ∈ quakePlateTranslations (e P) := by
  let v := Tiling.AxisParallel.Discrete.verticalDiscreteUnit
  let f : VerticalPlate K A → QuakePlate F (integerPoint ⁻¹' A) v :=
    fun P => Classical.choose (plate_image_eq_of_invariant_bridge hTile hTiles hA
      hbridge P)
  have hf (P : VerticalPlate K A) :
      P.centres = integerPoint '' quakePlateTranslations (f P) :=
    Classical.choose_spec (plate_image_eq_of_invariant_bridge hTile hTiles hA
      hbridge P)
  have hinj : Function.Injective f := by
    intro P Q hPQ
    apply vertical_plate_eq_of_centres_local
    calc
      P.centres = integerPoint '' quakePlateTranslations (f P) := hf P
      _ = integerPoint '' quakePlateTranslations (f Q) := by rw [hPQ]
      _ = Q.centres := (hf Q).symm
  have hsurj : Function.Surjective f := by
    intro C
    obtain ⟨a, ha⟩ := C.nonempty_supp
    have haC : (a : TranslationalTilings.Plane) ∈ quakePlateTranslations C :=
      ⟨a.property, (SimpleGraph.ConnectedComponent.mem_supp_iff C a).mp ha⟩
    let t : A := ⟨integerPoint (a : TranslationalTilings.Plane), a.property⟩
    let P : VerticalPlate K A := VerticalPlate.ofCentre t
    have haP : integerPoint (a : TranslationalTilings.Plane) ∈ P.centres := by
      exact VerticalPlate.mem_centres_ofCentre t
    have haF : (a : TranslationalTilings.Plane) ∈
        quakePlateTranslations (f P) := by
      obtain ⟨b, hb, hba⟩ := (hf P).symm ▸ haP
      have hab : a = b := integerPoint_injective hba.symm
      simpa [hab] using hb
    have hcompC := (SimpleGraph.ConnectedComponent.mem_supp_iff C a).mp ha
    obtain ⟨haFmem, hcompF⟩ := haF
    have hCF : C = f P := hcompC.symm.trans hcompF
    exact ⟨P, hCF.symm⟩
  let e : VerticalPlate K A ≃ QuakePlate F (integerPoint ⁻¹' A) v :=
    Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, ?_⟩
  intro P a
  constructor
  · intro haP
    have haP' : integerPoint (a : TranslationalTilings.Plane) ∈
        integerPoint '' quakePlateTranslations (f P) := (hf P).symm ▸ haP
    obtain ⟨b, hb, hba⟩ := haP'
    have hab : a = b := integerPoint_injective hba.symm
    change (a : TranslationalTilings.Plane) ∈ quakePlateTranslations (f P)
    simpa [hab] using hb
  · intro haC
    have haC' : integerPoint (a : TranslationalTilings.Plane) ∈
        integerPoint '' quakePlateTranslations (f P) := ⟨a, haC, rfl⟩
    exact (hf P).symm ▸ haC'

private theorem column_iff_of_invariant_bridge
    {K : Region} {A : Set Tiling.Plane}
    {F : Finset TranslationalTilings.Plane}
    (hTile : TilesOn K A Set.univ)
    (hTiles : TranslationalTilings.Tiles F (integerPoint ⁻¹' A) Set.univ)
    (hA : ∀ a ∈ A, IsIntegerPoint a)
    (hbridge : ∀ S : Set Tiling.Plane, S ⊆ A →
      ((∀ y : ℝ, ((y : ℂ) * Complex.I) +ᵥ regularSupport K S =
          regularSupport K S) ↔
        DiscretePeriodicBy (discreteCarrier F (integerPoint ⁻¹' S))
          Tiling.AxisParallel.Discrete.verticalDiscreteUnit)) :
    ∃ e : VerticalPlate K A ≃ QuakePlate F (integerPoint ⁻¹' A)
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit,
      (∀ P : VerticalPlate K A, ∀ a : integerPoint ⁻¹' A,
        integerPoint (a : TranslationalTilings.Plane) ∈ P.centres ↔
          (a : TranslationalTilings.Plane) ∈ quakePlateTranslations (e P)) ∧
      (∀ P : VerticalPlate K A, IsVerticalColumn P ↔
        Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn (e P)) := by
  obtain ⟨e, hmem⟩ := plate_equiv_of_invariant_bridge hTile hTiles hA hbridge
  refine ⟨e, hmem, ?_⟩
  intro P
  constructor
  · intro hPcol
    rcases (isVerticalColumn_iff P).mp hPcol with ⟨x, hx⟩
    let C := e P
    obtain ⟨a, ha⟩ := C.nonempty_supp
    have haC : (a : TranslationalTilings.Plane) ∈ quakePlateTranslations C :=
      ⟨a.property, (SimpleGraph.ConnectedComponent.mem_supp_iff C a).mp ha⟩
    have haP : integerPoint (a : TranslationalTilings.Plane) ∈ P.centres :=
      (hmem P a).mpr haC
    have hax : (integerPoint (a : TranslationalTilings.Plane)).re = x := hx haP
    refine ⟨(a : TranslationalTilings.Plane) 0, ?_⟩
    ext n
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hbP : integerPoint (b : TranslationalTilings.Plane) ∈ P.centres :=
        (hmem P ⟨b, hb.1⟩).mpr hb
      have hbx := hx hbP
      have hcoord : (b 0 : ℝ) = ((a : TranslationalTilings.Plane) 0 : ℝ) := by
        simpa [integerPoint] using hbx.trans hax.symm
      exact_mod_cast hcoord
    · intro hn
      have hna : n = (a : TranslationalTilings.Plane) 0 := by simpa using hn
      subst n
      exact ⟨a, haC, rfl⟩
  · intro hCcol
    rcases hCcol with ⟨c, hc⟩
    apply (isVerticalColumn_iff P).mpr
    refine ⟨(c : ℝ), ?_⟩
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hz
    have htA : (t : Tiling.Plane) ∈ A := t.property
    obtain ⟨a, ha⟩ := mem_integerLattice_iff.mp (hA t htA)
    let ai : integerPoint ⁻¹' A := ⟨a, by
      change integerPoint a ∈ A
      rw [ha]
      exact htA⟩
    have hza : integerPoint (ai : TranslationalTilings.Plane) = (t : Tiling.Plane) := by
      simpa [ai] using ha
    have haiP : integerPoint (ai : TranslationalTilings.Plane) ∈ P.centres := by
      exact hza ▸ ⟨t, ht, rfl⟩
    have haiC := (hmem P ai).mp haiP
    have hfirst : (ai : TranslationalTilings.Plane) 0 ∈
        Tiling.AxisParallel.Discrete.firstDiscreteCoordinate ''
        quakePlateTranslations (e P) := ⟨ai, haiC, rfl⟩
    rw [hc] at hfirst
    have hfirst' : (ai : TranslationalTilings.Plane) 0 = c := by
      simpa using hfirst
    rw [← hza]
    simp [integerPoint, hfirst']

private theorem integral_equivalence_data_of_invariant_bridge
    {K : Region} {A : Set Tiling.Plane}
    {F : Finset TranslationalTilings.Plane}
    (hTile : TilesOn K A Set.univ)
    (hTiles : TranslationalTilings.Tiles F (integerPoint ⁻¹' A) Set.univ)
    (hA : ∀ a ∈ A, IsIntegerPoint a)
    (hbridge : ∀ S : Set Tiling.Plane, S ⊆ A →
      ((∀ y : ℝ, ((y : ℂ) * Complex.I) +ᵥ regularSupport K S =
          regularSupport K S) ↔
        DiscretePeriodicBy (discreteCarrier F (integerPoint ⁻¹' S))
          Tiling.AxisParallel.Discrete.verticalDiscreteUnit)) :
    ∃ e : VerticalPlate K A ≃ QuakePlate F (integerPoint ⁻¹' A)
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit,
      (∀ P : VerticalPlate K A, ∀ a : integerPoint ⁻¹' A,
        integerPoint (a : TranslationalTilings.Plane) ∈ P.centres ↔
          (a : TranslationalTilings.Plane) ∈ quakePlateTranslations (e P)) ∧
      (∀ P : VerticalPlate K A, IsVerticalColumn P ↔
        Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn (e P)) ∧
      (∀ P : VerticalPlate K A, regularSupport K P.centres =
        regularSupport K (integerPoint '' quakePlateTranslations (e P))) ∧
      regularSupport K (verticalColumnCentres K A) =
        regularSupport K (integerPoint ''
          (Tiling.AxisParallel.Discrete.discreteColumnUnion F
            (integerPoint ⁻¹' A))) := by
  obtain ⟨e, hmem, hcolumn⟩ :=
    column_iff_of_invariant_bridge hTile hTiles hA hbridge
  have hplate (P : VerticalPlate K A) :
      P.centres = integerPoint '' quakePlateTranslations (e P) := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, htx⟩ := hx
      obtain ⟨a, ha⟩ := mem_integerLattice_iff.mp (hA t.1 t.2)
      let ai : integerPoint ⁻¹' A := ⟨a, by
        change integerPoint a ∈ A
        rw [ha]
        exact t.2⟩
      have htip : integerPoint (ai : TranslationalTilings.Plane) ∈ P.centres := by
        exact ⟨t, ht, by simp [ai, ha] at htx ⊢⟩
      have hai : (ai : TranslationalTilings.Plane) ∈ quakePlateTranslations (e P) :=
        (hmem P ai).mp htip
      exact ⟨ai, hai, (ha.trans htx)⟩
    · rintro ⟨a, ha, hax⟩
      obtain ⟨haA, -⟩ := mem_quakePlateTranslations_iff.mp ha
      have hcentre := (hmem P ⟨a, haA⟩).mpr ha
      simpa [hax] using hcentre
  have hcolumns : verticalColumnCentres K A =
      integerPoint '' (Tiling.AxisParallel.Discrete.discreteColumnUnion F
        (integerPoint ⁻¹' A)) := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨P, hx⟩
      rcases hx with ⟨t, ht, htx⟩
      have hPcol : IsVerticalColumn P.1 := P.2
      have hdisc : Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn (e P.1) :=
        (hcolumn P.1).mp hPcol
      obtain ⟨a, ha⟩ := mem_integerLattice_iff.mp (hA t.1 t.2)
      let ai : integerPoint ⁻¹' A := ⟨a, by
        change integerPoint a ∈ A
        rw [ha]
        exact t.2⟩
      have htip : integerPoint (ai : TranslationalTilings.Plane) ∈ P.1.centres := by
        exact ⟨t, ht, by simp [ai, ha] at htx ⊢⟩
      have hai : (ai : TranslationalTilings.Plane) ∈
          quakePlateTranslations (e P.1) :=
        (hmem P.1 ai).mp htip
      refine ⟨ai, Set.mem_iUnion_of_mem (e P.1)
        (Set.mem_iUnion_of_mem hdisc hai), ?_⟩
      exact (ha.trans htx)
    · rintro ⟨a, ha, hax⟩
      rcases Set.mem_iUnion.mp ha with ⟨Q, ha⟩
      rcases Set.mem_iUnion.mp ha with ⟨hQcol, haQ⟩
      let P := e.symm Q
      have hPcol : IsVerticalColumn P := by
        apply (hcolumn P).mpr
        simpa [P] using hQcol
      have haQ' : (a : TranslationalTilings.Plane) ∈
          quakePlateTranslations (e P) := by simpa [P] using haQ
      have haA : a ∈ integerPoint ⁻¹' A := (mem_quakePlateTranslations_iff.mp haQ').1
      have hcentre := (hmem P ⟨a, haA⟩).mpr haQ'
      refine Set.mem_iUnion_of_mem ⟨P, hPcol⟩ ?_
      obtain ⟨t, ht, hta⟩ := hcentre
      exact ⟨t, ht, by simpa [hax] using hta⟩
  refine ⟨e, hmem, hcolumn, ?_, ?_⟩
  · intro P
    rw [hplate P]
  · rw [hcolumns]

private theorem integralContinuousDiscretePlateEquivalence
    {K : Region} {A : Set Tiling.Plane}
    {F : Finset TranslationalTilings.Plane} :
    F.Nonempty → TilesOn K A Set.univ →
    K.openCarrier =ᵐ[volume] ⋃ f : F,
      integerPoint (f : TranslationalTilings.Plane) +ᵥ
        interior (Complex.Rectangle 0 (1 + Complex.I)) →
    (∀ a ∈ A, IsIntegerPoint a) →
    let Aint := integerPoint ⁻¹' A
    ∃ e : VerticalPlate K A ≃ QuakePlate F Aint
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit,
      (∀ P : VerticalPlate K A, ∀ a : Aint,
        integerPoint (a : TranslationalTilings.Plane) ∈ P.centres ↔
          (a : TranslationalTilings.Plane) ∈ quakePlateTranslations (e P)) ∧
      (∀ P : VerticalPlate K A, IsVerticalColumn P ↔
        Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn (e P)) ∧
      (∀ P : VerticalPlate K A, regularSupport K P.centres = regularSupport K
        (integerPoint '' quakePlateTranslations (e P))) ∧
      regularSupport K (verticalColumnCentres K A) = regularSupport K
        (integerPoint ''
          (Tiling.AxisParallel.Discrete.discreteColumnUnion F Aint)) := by
  intro hFne hTile hKae hA
  let Aint : Set TranslationalTilings.Plane := integerPoint ⁻¹' A
  have hTiles : TranslationalTilings.Tiles F Aint Set.univ := by
    change TranslationalTilings.Tiles F (integerPoint ⁻¹' A) Set.univ
    exact Tiling.AxisParallel.RationalMesh.gridCellTiling_of_unitCell_ae
      hFne hA hTile hKae
  have hbridge : ∀ S : Set Tiling.Plane, S ⊆ A →
      ((∀ y : ℝ, ((y : ℂ) * Complex.I) +ᵥ regularSupport K S =
          regularSupport K S) ↔
        DiscretePeriodicBy (discreteCarrier F (integerPoint ⁻¹' S))
          Tiling.AxisParallel.Discrete.verticalDiscreteUnit) := by
    intro S hSsub
    exact continuousDiscreteVerticalInvariant_iff hFne hKae hA hSsub
  exact integral_equivalence_data_of_invariant_bridge hTile hTiles hA hbridge

/-!
The mutual-minimality construction above uses the exact carrier-invariant
bridge, rather than a frontier-contact equivalence: carrier periodicity gives
the discrete component inclusion, while slab reconstruction and
`VerticalPlate.minimal` give equality.  The final public target is obtained by
supplying the already proved `continuousDiscreteVerticalInvariant_iff` to the
local `hbridge` argument.
-/


private theorem c04_overlay_hcell (z : TranslationalTilings.Plane) :
    meshCell 1 z = integerPoint z +ᵥ
      interior (Complex.Rectangle 0 (1 + Complex.I)) := by
  have hrect : interior (Complex.Rectangle 0 (1 + Complex.I)) =
      {w : Plane | 0 < w.re ∧ w.re < 1 ∧ 0 < w.im ∧ w.im < 1} := by
    have hr : Complex.Rectangle 0 (1 + Complex.I) = Icc 0 1 ×ℂ Icc 0 1 := by
      ext w
      simp [Complex.Rectangle]
    rw [hr, Complex.interior_reProdIm]
    ext w
    change (w.re ∈ interior (Icc 0 1) ∧ w.im ∈ interior (Icc 0 1)) ↔ _
    simp [interior_Icc]
    tauto
  ext x
  rw [hrect]
  simp [meshCell, rationalScale, integerPoint,
    Set.mem_vadd_set_iff_neg_vadd_mem]

private theorem c04_overlay_exists_mem_open_of_ae_local {U : Set Plane}
    {P : Plane → Prop} (hU : IsOpen U) (hUne : U.Nonempty)
    (hP : ∀ᵐ z ∂volume, P z) : ∃ z ∈ U, P z := by
  have hμ : volume.restrict U ≠ 0 := by
    intro hz
    have hzero : volume U = 0 := by
      rw [← Measure.restrict_apply_univ U, hz]
      simp
    exact hU.measure_ne_zero volume hUne hzero
  let hne : (ae (volume.restrict U)).NeBot := ae_neBot.mpr hμ
  have hP' : ∀ᵐ z ∂volume.restrict U, P z := hP.filter_mono ae_restrict_le
  rcases @Filter.Eventually.exists Plane _ (ae (volume.restrict U)) hne
      (hP'.and (ae_restrict_mem hU.measurableSet)) with ⟨z, hzP, hzU⟩
  exact ⟨z, hzU, hzP⟩

private theorem c04_overlay_mesh
    {K : Region} (N : IntegralTileNormalization K) :
    OnRationalMesh 1 N.region.vertices := by
  intro v hv
  obtain ⟨z, hz⟩ := mem_integerLattice_iff.mp (N.vertices_integer v hv)
  refine ⟨z, ?_⟩
  apply Complex.ext
  · simpa [rationalScale, integerPoint] using congrArg Complex.re hz
  · simpa [rationalScale, integerPoint] using congrArg Complex.im hz

private theorem c04_overlay_raster
    {K : Region} {A : Set Tiling.Plane}
    (N : IntegralTileNormalization K)
    (_hA : ∀ a ∈ A, IsIntegerPoint a)
    (_hTiles : TilesOn N.region A Set.univ) :
    ∃ F : Finset TranslationalTilings.Plane,
      F.Nonempty ∧
      N.region.openCarrier =ᵐ[volume] ⋃ f : F,
        integerPoint (f : TranslationalTilings.Plane) +ᵥ
          interior (Complex.Rectangle 0 (1 + Complex.I)) := by
  obtain ⟨F, hFne, hFraster, hFae, _⟩ :=
    exists_regionRaster (K := N.region) (d := 1) (by simp)
      (c04_overlay_mesh N)
  refine ⟨F, hFne, ?_⟩
  filter_upwards [hFae] with x hx
  exact hx.trans (by
    apply congrFun
    apply iUnion_congr
    intro f
    exact c04_overlay_hcell f)

private def overlayCentreIndex
    {K : Region} {T : Set Plane} (N : IntegralTileNormalization K)
    (B : IntegralPlateTiling K T N) (t : T) : TranslationalTilings.Plane :=
  Classical.choose (mem_integerLattice_iff.mp
    (B.centres_integer _ (by rw [B.centres_eq]; exact ⟨t, rfl⟩)))

private theorem overlayCentreIndex_spec
    {K : Region} {T : Set Plane} (N : IntegralTileNormalization K)
    (B : IntegralPlateTiling K T N) (t : T) :
    integerPoint (overlayCentreIndex N B t) = normalizedCentre N
      B.commonHorizontalShift B.plateVerticalShift t := by
  exact Classical.choose_spec (mem_integerLattice_iff.mp
    (B.centres_integer _ (by rw [B.centres_eq]; exact ⟨t, rfl⟩)))

private def overlayCentreEquiv
    {K : Region} {T : Set Plane} (N : IntegralTileNormalization K)
    (B : IntegralPlateTiling K T N) :
    T ≃ integerPoint ⁻¹' B.centres := by
  let f : T → integerPoint ⁻¹' B.centres := fun t =>
    ⟨overlayCentreIndex N B t, by
      change integerPoint (overlayCentreIndex N B t) ∈ B.centres
      rw [overlayCentreIndex_spec N B t, B.centres_eq]
      exact ⟨t, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro s t hst
    have hidx : overlayCentreIndex N B s = overlayCentreIndex N B t :=
      congrArg (fun a : integerPoint ⁻¹' B.centres =>
        (a : TranslationalTilings.Plane)) hst
    apply B.centre_injective
    rw [← overlayCentreIndex_spec N B s, ← overlayCentreIndex_spec N B t]
    exact congrArg integerPoint hidx
  · intro a
    have ha : integerPoint (a : TranslationalTilings.Plane) ∈ B.centres := a.property
    have ha' : integerPoint (a : TranslationalTilings.Plane) ∈
        Set.range (normalizedCentre N B.commonHorizontalShift B.plateVerticalShift) :=
      by
        exact B.centres_eq ▸ ha
    obtain ⟨t, ht⟩ := ha'
    refine ⟨t, ?_⟩
    apply Subtype.ext
    exact integerPoint_injective (by
      rw [overlayCentreIndex_spec N B t]
      exact ht)

private theorem overlay_column_centres_eq
    {K : Region} {T : Set Plane}
    {F : Finset TranslationalTilings.Plane}
    (N : IntegralTileNormalization K)
    (B : IntegralPlateTiling K T N)
    (e : VerticalPlate N.region B.centres ≃
      QuakePlate F (integerPoint ⁻¹' B.centres)
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit)
    (ce : T ≃ integerPoint ⁻¹' B.centres)
    (hmem : ∀ (P : VerticalPlate N.region B.centres)
      (a : integerPoint ⁻¹' B.centres),
      integerPoint (a : TranslationalTilings.Plane) ∈ P.centres ↔
        (a : TranslationalTilings.Plane) ∈ quakePlateTranslations (e P))
    (hcolumn : ∀ P : VerticalPlate N.region B.centres,
      IsVerticalColumn P ↔
        Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn (e P))
    (hce : ∀ t : T,
      integerPoint (ce t : TranslationalTilings.Plane) =
        normalizedCentre N B.commonHorizontalShift B.plateVerticalShift t) :
    ce '' {t : T | (t : Plane) ∈ verticalColumnCentres K T} =
      {a : integerPoint ⁻¹' B.centres |
        (a : TranslationalTilings.Plane) ∈
          Tiling.AxisParallel.Discrete.discreteColumnUnion F
            (integerPoint ⁻¹' B.centres)} := by
  ext a
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases Set.mem_iUnion.mp ht with ⟨Q, htQ⟩
    change (ce t : TranslationalTilings.Plane) ∈
      Tiling.AxisParallel.Discrete.discreteColumnUnion F
        (integerPoint ⁻¹' B.centres)
    rw [Tiling.AxisParallel.Discrete.discreteColumnUnion]
    refine Set.mem_iUnion.mpr ⟨e (B.plateEquiv Q.1), ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
    · exact (hcolumn (B.plateEquiv Q.1)).mp ((B.column_iff Q.1).mp Q.2)
    · have hnorm := (B.mem_plate Q.1 t).mp htQ
      have hidx : integerPoint (ce t) =
          normalizedCentre N B.commonHorizontalShift B.plateVerticalShift t := by
        exact hce t
      apply (hmem (B.plateEquiv Q.1) (ce t)).mp
      rw [hidx]
      exact hnorm
  · intro ha
    change (a : TranslationalTilings.Plane) ∈
      Tiling.AxisParallel.Discrete.discreteColumnUnion F
        (integerPoint ⁻¹' B.centres) at ha
    rw [Tiling.AxisParallel.Discrete.discreteColumnUnion] at ha
    rcases Set.mem_iUnion.mp ha with ⟨R, haR⟩
    rcases Set.mem_iUnion.mp haR with ⟨hRcol, haR⟩
    let Q : VerticalPlate K T :=
      B.plateEquiv.symm (e.symm R)
    have hQcol : IsVerticalColumn Q := by
      apply (B.column_iff Q).mpr
      apply (hcolumn (B.plateEquiv Q)).mpr
      simpa [Q] using hRcol
    have hQa : integerPoint (a : TranslationalTilings.Plane) ∈
        (B.plateEquiv Q).centres := by
      apply (hmem (B.plateEquiv Q) a).mpr
      simpa [Q] using haR
    have hQaB : integerPoint (a : TranslationalTilings.Plane) ∈ B.centres := by
      have hu : integerPoint (a : TranslationalTilings.Plane) ∈
          ⋃ R : VerticalPlate N.region B.centres, R.centres :=
        Set.mem_iUnion.mpr ⟨B.plateEquiv Q, hQa⟩
      have heq := congrArg (fun S : Set Tiling.Plane =>
        integerPoint (a : TranslationalTilings.Plane) ∈ S)
        (iUnion_verticalPlateCentres N.region B.centres)
      exact heq.mp hu
    have hQa' : integerPoint (a : TranslationalTilings.Plane) ∈
        Set.range (normalizedCentre N B.commonHorizontalShift B.plateVerticalShift) := by
      exact B.centres_eq ▸ hQaB
    obtain ⟨t, ht⟩ := hQa'
    refine ⟨t, ?_, ?_⟩
    · exact Set.mem_iUnion_of_mem ⟨Q, hQcol⟩
        ((B.mem_plate Q t).mpr (by
          rw [ht]
          exact hQa))
    · apply Subtype.ext
      exact integerPoint_injective (by
        have hidx : integerPoint (ce t) =
            normalizedCentre N B.commonHorizontalShift B.plateVerticalShift t := by
          exact hce t
        exact hidx.trans ht)

theorem exists_plateCompatibleIntegerization
    {K : Region} {T : Set Plane} (hTile : TilesOn K T Set.univ)
    (hRational : Tiling.RationalPolygonal.IsRelativelyRational K.toPolygonalRegion)
    (hNonSub : ¬ Subsingleton (VerticalPlate K T)) :
    Nonempty (PlateCompatibleIntegerization K T) := by
  obtain ⟨Nc⟩ := integralTileNormalization_exists K hRational
  let N : IntegralTileNormalization K := {
    scale := Nc.scale
    scale_pos := Nc.scale_pos
    anchor := Nc.anchor
    anchor_mem := Nc.anchor_mem
    region := Nc.region
    carrier_eq := Nc.carrier_eq
    vertices_integer := Nc.vertices_integer }
  obtain ⟨B⟩ := integralPlateTiling_exists N hTile hNonSub
  obtain ⟨F, hFne, hFae⟩ := c04_overlay_raster N B.centres_integer B.tiles
  have hDiscrete : TranslationalTilings.Tiles F
      (integerPoint ⁻¹' B.centres) Set.univ :=
    (gridCellTiling_iff_discreteTiling hFne N.vertices_integer hFae
      B.centres_integer).mp B.tiles
  obtain ⟨e, hmem, hcolumn, hplate, haggregate⟩ :=
    integralContinuousDiscretePlateEquivalence hFne B.tiles hFae
      B.centres_integer
  let ce := overlayCentreEquiv N B
  let pe : VerticalPlate K T ≃
      QuakePlate F (integerPoint ⁻¹' B.centres)
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit :=
    B.plateEquiv.trans e
  refine ⟨{
    scale := N.scale
    scale_pos := N.scale_pos
    tileAnchor := N.anchor
    tileAnchor_mem := N.anchor_mem
    commonHorizontalShift := B.commonHorizontalShift
    plateVerticalShift := B.plateVerticalShift
    integerRegion := N.region
    integerRegion_openCarrier := N.carrier_eq
    integerVertices := N.vertices_integer
    discreteTile := F
    discreteTile_nonempty := hFne
    discreteTile_realizes_integerRegion := hFae
    discreteCentres := integerPoint ⁻¹' B.centres
    discrete_tiling := hDiscrete
    centreEquiv := ce
    centreEquiv_apply := ?_
    plateEquiv := pe
    centreEquiv_mem_plate := ?_
    column_iff := ?_
    carrier_eq := ?_
    columnAggregate_centres_eq :=
      overlay_column_centres_eq N B e ce hmem hcolumn (by
        intro t
        change integerPoint (overlayCentreIndex N B t) = _
        exact overlayCentreIndex_spec N B t)
    columnAggregate_carrier_eq := ?_ }⟩
  · intro t
    exact overlayCentreIndex_spec N B t
  · intro P t
    change (t : Plane) ∈ P.centres ↔
      (ce t : TranslationalTilings.Plane) ∈ quakePlateTranslations (pe P)
    rw [B.mem_plate P t]
    have hce : integerPoint (ce t : TranslationalTilings.Plane) =
        normalizedCentre N B.commonHorizontalShift B.plateVerticalShift t := by
      change integerPoint (overlayCentreIndex N B t) = _
      exact overlayCentreIndex_spec N B t
    rw [← hce]
    simpa [pe] using hmem (B.plateEquiv P) (ce t)
  · intro P
    simpa [pe] using (B.column_iff P).trans (hcolumn (B.plateEquiv P))
  · intro P
    change regularSupport N.region
        (integerPoint '' quakePlateTranslations (e (B.plateEquiv P))) = _
    calc
      _ = regularSupport N.region (B.plateEquiv P).centres :=
        (hplate (B.plateEquiv P)).symm
      _ = _ := B.support_eq P
  · rw [← haggregate]
    exact B.columnAggregate_support_eq

private theorem c04_overlay_common_period
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (hF : F.Nonempty)
    (hTiles : TranslationalTilings.Tiles F A Set.univ) :
    ∃ L : ℕ, 0 < L ∧
      (∀ P : QuakePlate F A Tiling.AxisParallel.Discrete.verticalDiscreteUnit,
        ¬ Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn P →
        TranslationalTilings.SetScalarPeriodic L
          (discreteCarrier F (quakePlateTranslations P))) ∧
      TranslationalTilings.SetScalarPeriodic L
        (discreteCarrier F
          (Tiling.AxisParallel.Discrete.discreteColumnUnion F A)) := by
  have hEVertical : DiscretePeriodicBy (Set.univ : Set TranslationalTilings.Plane)
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit := by
    simp [Tiling.RationalPolygonal.DiscretePeriodicBy]
  have hEPeriodic : TranslationalTilings.SetScalarPeriodic 1
      (Set.univ : Set TranslationalTilings.Plane) := by
    simp [TranslationalTilings.SetScalarPeriodic]
  obtain ⟨L, hL, _hdiv, hplates, hcolumn⟩ :=
    Tiling.AxisParallel.Discrete.exists_discretePlatePeriodicity hF
      (by norm_num) hEVertical hEPeriodic hTiles
  exact ⟨L, hL, hplates, hcolumn⟩

theorem rationalVerticalPlateSupport_periodic
    {K : Region} {T : Set Plane} (hTile : TilesOn K T Set.univ)
    (hRational : Tiling.RationalPolygonal.IsRelativelyRational K.toPolygonalRegion) :
    ∃ beta : ℝ, 0 < beta ∧
      SetPeriodicBy (regularSupport K (verticalColumnCentres K T))
        ((beta : ℝ) : ℂ) ∧
      ∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
        SetPeriodicBy P.support ((beta : ℝ) : ℂ) := by
  by_cases hsub : Subsingleton (VerticalPlate K T)
  · have hKopen : K.openCarrier.Nonempty :=
      K.isPolygonal.interior_nonempty K.nonempty
    have hAE : ∀ᵐ z : Tiling.Plane ∂volume, z ∈ openUnion K T := by
      filter_upwards [hTile.2.2] with z hz
      change z ∈ ⋃ s : T, (s : Tiling.Plane) +ᵥ K.openCarrier
      rcases hz.mp (by simp) with ⟨s, hs⟩
      exact Set.mem_iUnion.mpr ⟨s, hs⟩
    obtain ⟨z, hzK, hzAE⟩ := exists_mem_open_of_ae_local
      (P := fun z : Tiling.Plane => z ∈ openUnion K T)
      K.openCarrier_regularOpen.1 hKopen hAE
    change z ∈ openUnion K T at hzAE
    rw [openUnion] at hzAE
    obtain ⟨t, _ht⟩ := Set.mem_iUnion.mp hzAE
    have hTne : T.Nonempty := ⟨t, t.property⟩
    obtain ⟨t₀, ht₀⟩ := hTne
    let t₀ : T := ⟨t₀, ht₀⟩
    let P₀ : VerticalPlate K T := VerticalPlate.ofCentre t₀
    have hPall (P : VerticalPlate K T) : P = P₀ := hsub.elim P P₀
    have hcentres : P₀.centres = T := by
      apply Set.Subset.antisymm
      · rintro x ⟨t, _ht, rfl⟩
        exact t.property
      · intro x hx
        let t : T := ⟨x, hx⟩
        have ht : (t : Tiling.Plane) ∈
            (VerticalPlate.ofCentre (K := K) t).centres :=
          VerticalPlate.mem_centres_ofCentre (K := K) t
        have hEq := hPall (VerticalPlate.ofCentre (K := K) t)
        rw [hEq] at ht
        simpa [t] using ht
    have hwhole : regularSupport K T = Set.univ :=
      Tiling.AxisParallel.regularSupport_eq_of_tilesOn isOpen_univ
        (by simp) hTile
    have hPwhole : P₀.support = Set.univ := by
      rw [VerticalPlate.support_eq_regularSupport, hcentres, hwhole]
    by_cases hcol : IsVerticalColumn P₀
    · have hagg : verticalColumnCentres K T = T := by
        change (⋃ Q : {Q : VerticalPlate K T // IsVerticalColumn Q}, Q.1.centres) = T
        apply Set.Subset.antisymm
        · intro x hx
          rcases Set.mem_iUnion.mp hx with ⟨Q, hxQ⟩
          have hQP : Q.1 = P₀ := hPall Q.1
          rw [hQP] at hxQ
          rw [← hcentres]
          exact hxQ
        · intro x hx
          let Q : {Q : VerticalPlate K T // IsVerticalColumn Q} := ⟨P₀, hcol⟩
          have hxP : x ∈ P₀.centres := by
            rw [hcentres]
            exact hx
          exact Set.mem_iUnion_of_mem Q hxP
      refine ⟨1, by norm_num, ?_, ?_⟩
      · rw [hagg, hwhole]
        intro x
        simp
      · intro P hP
        have hPQ : IsVerticalColumn P := by
          have hPP : P = P₀ := hPall P
          simpa [hPP] using hcol
        exact (hP hPQ).elim
    · have hagg : verticalColumnCentres K T = ∅ := by
        change (⋃ Q : {Q : VerticalPlate K T // IsVerticalColumn Q}, Q.1.centres) = ∅
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.mp hx with ⟨Q, _hxQ⟩
          have hQP : Q.1 = P₀ := hPall Q.1
          have hcol' : IsVerticalColumn P₀ := hQP ▸ Q.2
          exact (hcol hcol').elim
        · intro hx
          simp at hx
      refine ⟨1, by norm_num, ?_, ?_⟩
      · rw [hagg]
        intro x
        simp [regularSupport, Tiling.Polygonal.regularSupport, Tiling.Polygonal.openUnion]
      · intro P hP
        have hPP : P = P₀ := hPall P
        have hPsupport : P.support = Set.univ := by
          rw [hPP, hPwhole]
        rw [hPsupport]
        intro x
        simp
  · obtain ⟨I⟩ := exists_plateCompatibleIntegerization hTile hRational hsub
    obtain ⟨L, hL, hPlatePeriod, hColumnPeriod⟩ :=
      c04_overlay_common_period I.discreteTile_nonempty I.discrete_tiling
    let beta : ℝ := (L : ℝ) / I.scale
    have hscale : (0 : ℝ) < I.scale := by exact_mod_cast I.scale_pos
    have hbeta : 0 < beta := by
      dsimp [beta]
      positivity
    refine ⟨beta, hbeta, ?_, ?_⟩
    · simpa [beta] using
        discreteColumnSupportPeriod_liftsContinuousColumnSupportPeriod I hL
          (hColumnPeriod)
    · intro P hP
      have hP' : ¬ Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn
          (I.plateEquiv P) := by
        intro h
        exact hP ((I.column_iff P).mpr h)
      simpa [beta] using
        discreteSupportPeriod_liftsContinuousSupportPeriod I P hL
          (hPlatePeriod (I.plateEquiv P) hP')
end Tiling.AxisParallel.Continuous
namespace Tiling.AxisParallel.Continuous

open Tiling
open Tiling.AxisParallel

/-! Public extraction of the one-sided rational-slab saturation argument. -/
theorem rationalOneSidedSlab_saturatesColumns :
    ∀ {K : Region} {T S : Set Plane} {X : Set ℝ},
      TilesOn K T Set.univ →
      Tiling.RationalPolygonal.IsRelativelyRational K.toPolygonalRegion →
      S ⊆ T → IsOpen X → interior (closure X) = X →
      regularSupport K S = Complex.re ⁻¹' X →
      (BddBelow X ∨ BddAbove X) →
      ∀ Q : VerticalPlate K T,
        (Q.centres ∩ S).Nonempty →
          Q.centres ⊆ S ∧ IsVerticalColumn Q := by
  intro K T S X hTile hRat hST hXopen hXregular hSsupport hXone Q hmeet
  have hTslab : ∃ Y : Set ℝ, Y = interior (closure Y) ∧
      regularSupport K T = Complex.re ⁻¹' Y := by
    refine ⟨Set.univ, by simp, ?_⟩
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile]
    simp
  obtain ⟨XB, hXBregular, hBsupport⟩ := verticalSlab_sdiff hTile
    (Subset.refl T) hST hTslab ⟨X, hXregular.symm, hSsupport⟩
  let parts : Bool → Set Plane
    | false => S
    | true => T \ S
  have hparts : Set.PairwiseDisjoint Set.univ parts := by
    intro i _ j _ hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact Set.disjoint_left.2 fun _ hi hj => hj.2 hi
    · exact Set.disjoint_left.2 fun _ hi hj => hi.2 hj
    · exact (hij rfl).elim
  have hunion : (⋃ i, parts i) = T := by
    ext z
    constructor
    · simp only [Set.mem_iUnion]
      rintro ⟨i, hi⟩
      cases i
      · exact hST hi
      · exact hi.1
    · intro hz
      by_cases hzS : z ∈ S
      · exact Set.mem_iUnion.2 ⟨false, hzS⟩
      · exact Set.mem_iUnion.2 ⟨true, hz, hzS⟩
  have hpair := (regularSupport_pairwiseDisjoint parts hparts hunion hTile).1
  have hdisj : Disjoint (regularSupport K S) (regularSupport K (T \ S)) := by
    have h := hpair (Set.mem_univ false) (Set.mem_univ true) (by decide)
    change Disjoint (regularSupport K S) (regularSupport K (T \ S)) at h
    exact h
  have hsat := verticalPlates_saturated_of_slabPartition K
    (show S ∪ (T \ S) = T by
      ext z
      constructor
      · rintro (hz | hz)
        · exact hST hz
        · exact hz.1
      · intro hz
        by_cases hzS : z ∈ S
        · exact Or.inl hzS
        · exact Or.inr ⟨hz, hzS⟩)
    hdisj hXregular hXBregular.symm hSsupport hBsupport
  have hQsub : Q.centres ⊆ S := hsat.1 Q hmeet
  refine ⟨hQsub, ?_⟩
  by_contra hQnoncolumn
  obtain ⟨beta, hbeta, _hColumnPeriod, hNonColumnPeriod⟩ :=
    rationalVerticalPlateSupport_periodic hTile hRat
  have hQperiod := hNonColumnPeriod Q hQnoncolumn
  have hopenSub : openUnion K Q.centres ⊆ openUnion K S := by
    intro z hz
    rw [openUnion] at hz ⊢
    rcases Set.mem_iUnion.mp hz with ⟨t, ht⟩
    exact Set.mem_iUnion.mpr
      ⟨⟨(t : Plane), hQsub t.property⟩, ht⟩
  have hQsupport_sub : Q.support ⊆ regularSupport K S := by
    rw [VerticalPlate.support, regularSupport, regularSupport]
    exact interior_mono (closure_mono hopenSub)
  obtain ⟨p, hp⟩ := Q.nonempty_supp
  have hpcentre : (p : Plane) ∈ Q.centres := ⟨p, hp, rfl⟩
  obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hopen : IsOpen (openUnion K Q.centres) := by
    rw [openUnion]
    exact isOpen_iUnion fun t : Q.centres => K.openCarrier_regularOpen.1.vadd t.1
  have hz0 : (p : Plane) +ᵥ u ∈ Q.support := by
    rw [VerticalPlate.support, regularSupport]
    apply hopen.subset_interior_closure
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, mem_iUnion]
    exact ⟨⟨p, hpcentre⟩, by
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_assoc,
        Region.openCarrier, Tiling.RationalPolygonal.PolygonalRegion.openCarrier] using hu⟩
  rcases hXone with ⟨b, hb⟩ | ⟨b, hb⟩
  · obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (((((p : Plane) +ᵥ u).re - b) / beta))
    have hzshift : ∀ n : ℕ,
        ((p : Plane) +ᵥ u) - ((n : ℝ) : ℂ) * (beta : ℂ) ∈ Q.support := by
      intro m
      induction m with
      | zero => simpa using hz0
      | succ m ih =>
          have hp' := hQperiod
            (((p : Plane) +ᵥ u) - ((m : ℝ) : ℂ) * (beta : ℂ) - (beta : ℂ))
          rw [show (((p : Plane) +ᵥ u) - ((m : ℝ) : ℂ) * (beta : ℂ) -
              (beta : ℂ)) + (beta : ℂ) =
              ((p : Plane) +ᵥ u) - ((m : ℝ) : ℂ) * (beta : ℂ) by ring] at hp'
          have hi := hp'.mp ih
          have heq :
              ((p : Plane) +ᵥ u) - ((m.succ : ℝ) : ℂ) * (beta : ℂ) =
                ((p : Plane) +ᵥ u) - ((m : ℝ) : ℂ) * (beta : ℂ) -
                  (beta : ℂ) := by
            push_cast
            ring
          rw [heq]
          exact hi
    have hzmem := hQsupport_sub (hzshift n)
    rw [hSsupport] at hzmem
    have hbound := hb hzmem
    have hreal : (((p : Plane) +ᵥ u) - ((n : ℝ) : ℂ) * (beta : ℂ)).re =
        ((p : Plane) +ᵥ u).re - (n : ℝ) * beta := by
      simp only [Complex.sub_re, Complex.mul_re, vadd_eq_add, Complex.add_re]
      norm_num
    rw [hreal] at hbound
    have hn' : (((p : Plane) +ᵥ u).re - b) < (n : ℝ) * beta :=
      (div_lt_iff₀ hbeta).mp hn
    nlinarith
  · obtain ⟨n : ℕ, hn⟩ := exists_nat_gt ((b - ((p : Plane) +ᵥ u).re) / beta)
    have hzshift : ∀ n : ℕ,
        ((p : Plane) +ᵥ u) + ((n : ℝ) : ℂ) * (beta : ℂ) ∈ Q.support := by
      intro m
      induction m with
      | zero => simpa using hz0
      | succ m ih =>
          have hp' := hQperiod
            (((p : Plane) +ᵥ u) + ((m : ℝ) : ℂ) * (beta : ℂ))
          have hp'' := hp'.mpr ih
          simpa [Nat.cast_succ, add_mul, add_assoc] using hp''
    have hzmem := hQsupport_sub (hzshift n)
    rw [hSsupport] at hzmem
    have hbound := hb hzmem
    have hreal : (((p : Plane) +ᵥ u) + ((n : ℝ) : ℂ) * (beta : ℂ)).re =
        ((p : Plane) +ᵥ u).re + (n : ℝ) * beta := by
      simp only [Complex.add_re, Complex.mul_re, vadd_eq_add]
      norm_num
    rw [hreal] at hbound
    have hn' : (b - ((p : Plane) +ᵥ u).re) < (n : ℝ) * beta :=
      (div_lt_iff₀ hbeta).mp hn
    nlinarith

end Tiling.AxisParallel.Continuous
