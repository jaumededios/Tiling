import Tiling.AxisParallel.Structure.HorizontalComplexityCharacterization.FiniteContactTransport
import Tiling.AxisParallel.Continuous.PositiveSimilarityPlates
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.HorizontalComplexityCore
import Tiling.AxisParallel.OneDimensional.ColumnSlices
import Tiling.AxisParallel.OneDimensional.FiniteInterval.WholeLine
import Tiling.AxisParallel.Structure.PlateThickness
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.OneDimensional.FiniteInterval.TargetGeometry
import Tiling.AxisParallel.Structure.HorizontalComplexityCharacterization.BoundaryDensity
import Tiling.AxisParallel.Continuous.ContinuousSlabPeriodicity

/-!
# Column-base characterization

Production-shaped implementation for the horizontal-complexity/column-base characterization.
All construction details remain private; the final four-way characterization is the public
consumer interface.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Bornology Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Structure

open Tiling.AxisParallel
open Tiling.AxisParallel.OneDimensional.FiniteInterval

private def horizontalFootprint (K : Region) : Set ℝ :=
  interior (closure (Complex.re '' K.openCarrier))

private structure AllColumnAxisData (K : Region) (T : Set Tiling.Plane) where
  axis : Continuous.VerticalPlate K T → ℝ
  centres_on_axis : ∀ P,
    P.centres ⊆ {z : Tiling.Plane | z.re = axis P}
  axis_unique : ∀ P x,
    P.centres ⊆ {z : Tiling.Plane | z.re = x} → x = axis P
  base_eq : ∀ P, P.base = axis P +ᵥ horizontalFootprint K

private theorem horizontalFootprint_nonempty_local (K : Region) :
    (horizontalFootprint K).Nonempty := by
  have hCarrierNonempty : K.openCarrier.Nonempty :=
    K.isPolygonal.interior_nonempty K.nonempty
  have hProjectionNonempty : (Complex.re '' K.openCarrier).Nonempty :=
    hCarrierNonempty.image Complex.re
  have hProjectionOpen : IsOpen (Complex.re '' K.openCarrier) :=
    Complex.isOpenMap_re K.openCarrier isOpen_interior
  exact ⟨_, hProjectionOpen.subset_interior_closure hProjectionNonempty.choose_spec⟩

private theorem axisBase_formula_local
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : Continuous.VerticalPlate K T)
    (hPcolumn : Continuous.IsVerticalColumn P) {x : ℝ}
    (hx : P.centres ⊆ {z : Tiling.Plane | z.re = x}) :
    P.base = x +ᵥ horizontalFootprint K := by
  obtain ⟨hbase, _⟩ := Continuous.verticalColumn_regularSupport
    hTile P hPcolumn hx
  have hset :
      (Complex.re '' K.openCarrier) + {x} =
        x +ᵥ (Complex.re '' K.openCarrier) := by
    ext r
    constructor
    · rintro ⟨u, hu, z, hz, rfl⟩
      simp only [Set.mem_singleton_iff] at hz
      subst z
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa using hu
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      intro hu
      exact ⟨-x +ᵥ r, hu, x, Set.mem_singleton x, by simp [vadd_eq_add]
        ⟩
  rw [hbase, hset, closure_vadd, interior_vadd]
  rfl

private theorem allColumnAxisData_exists :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (∀ P : Continuous.VerticalPlate K T, Continuous.IsVerticalColumn P) →
      Nonempty (AllColumnAxisData K T) := by
  intro K T hTile hAll
  classical
  let axis : Continuous.VerticalPlate K T → ℝ := fun P ↦
    Classical.choose ((Continuous.isVerticalColumn_iff P).mp (hAll P))
  have hAxis : ∀ P : Continuous.VerticalPlate K T,
      P.centres ⊆ {z : Tiling.Plane | z.re = axis P} := by
    intro P
    exact (Classical.choose_spec
      ((Continuous.isVerticalColumn_iff P).mp (hAll P)))
  have hUnique : ∀ (P : Continuous.VerticalPlate K T) (x : ℝ),
      P.centres ⊆ {z : Tiling.Plane | z.re = x} → x = axis P := by
    intro P x hx
    obtain ⟨t, ht⟩ := P.nonempty_supp
    have htP : (t : Tiling.Plane) ∈ P.centres := by
      exact ⟨t, (SimpleGraph.ConnectedComponent.mem_supp_iff P t).1 ht, rfl⟩
    have htx := hx htP
    have hta := hAxis P htP
    exact htx.symm.trans hta
  refine ⟨⟨axis, hAxis, hUnique, ?_⟩⟩
  intro P
  exact axisBase_formula_local hTile P (hAll P) (hAxis P)

private theorem allColumnAxis_injective :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (∀ P : Continuous.VerticalPlate K T, Continuous.IsVerticalColumn P) →
      ∀ A : AllColumnAxisData K T, Function.Injective A.axis := by
  intro K T hTile hAll A P Q haxes
  classical
  by_contra hPQ
  let _ : Countable T := hTile.1.to_subtype
  let _ : Countable (Continuous.VerticalPlate K T) := by
    apply Function.Surjective.countable
      (f := fun t : T ↦ Continuous.VerticalPlate.ofCentre (K := K) t)
    intro R
    obtain ⟨r, hr⟩ := R.nonempty_supp
    refine ⟨r, ?_⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff R r).1 hr
  have hPart := regularSupport_pairwiseDisjoint
    (@Continuous.VerticalPlate.centres K T)
    (Continuous.verticalPlateCentres_pairwiseDisjoint K T)
    (Continuous.iUnion_verticalPlateCentres K T) hTile
  have hFoot := horizontalFootprint_nonempty_local K
  obtain ⟨u, hu⟩ := hFoot
  have huP : A.axis P + u ∈ P.base := by
    rw [A.base_eq P, Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa using hu
  have huQ : A.axis P + u ∈ Q.base := by
    rw [A.base_eq Q, ← haxes, Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa using hu
  obtain ⟨-, hPsupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile P
  obtain ⟨-, hQsupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile Q
  have hPz : (⟨A.axis P + u, 0⟩ : Tiling.Plane) ∈ P.support := by
    rw [hPsupport]
    exact huP
  have hQz : (⟨A.axis P + u, 0⟩ : Tiling.Plane) ∈ Q.support := by
    rw [hQsupport]
    exact huQ
  exact Set.disjoint_left.mp
      (hPart.1 (Set.mem_univ P) (Set.mem_univ Q) hPQ) hPz hQz

private theorem allColumnAxes_eq_projection :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (∀ P : Continuous.VerticalPlate K T, Continuous.IsVerticalColumn P) →
      ∀ A : AllColumnAxisData K T,
        Set.range A.axis = Continuous.horizontalCentreProjection T := by
  intro K T hTile hAll A
  ext x
  constructor
  · rintro ⟨P, rfl⟩
    obtain ⟨t, ht⟩ := P.nonempty_supp
    have htP : (t : Tiling.Plane) ∈ P.centres := by
      exact ⟨t, (SimpleGraph.ConnectedComponent.mem_supp_iff P t).1 ht, rfl⟩
    have htT : (t : Tiling.Plane) ∈ T := t.2
    have htx := A.centres_on_axis P htP
    exact ⟨t, htT, htx⟩
  · rintro ⟨t, htT, rfl⟩
    have htUnion : t ∈ ⋃ P : Continuous.VerticalPlate K T, P.centres := by
      rw [Continuous.iUnion_verticalPlateCentres]
      exact htT
    obtain ⟨P, hPt⟩ := Set.mem_iUnion.mp htUnion
    exact ⟨P, (A.centres_on_axis P hPt).symm⟩

private theorem verticalPlates_countable :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ → Countable (Continuous.VerticalPlate K T) := by
  intro K T hTile
  let _ : Countable T := hTile.1.to_subtype
  apply Function.Surjective.countable
    (f := fun t : T ↦ Continuous.VerticalPlate.ofCentre (K := K) t)
  intro R
  obtain ⟨r, hr⟩ := R.nonempty_supp
  refine ⟨r, ?_⟩
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff R r).1 hr

private theorem interior_finiteClosedIntervals_isFiniteIntervalRegion :
    ∀ {n : Nat} (left right : Fin n → ℝ),
      (∀ i, left i < right i) →
        Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
          (interior (⋃ i, Set.Icc (left i) (right i))) := by
  intro n left right hlt
  obtain ⟨P⟩ := Tiling.AxisParallel.Foundations.GenericSlices.finiteClosedIntervals_merge
    left right
  exact ⟨P.n, P.left, P.right, P.lt, P.union_eq⟩

private theorem horizontalFootprint_finiteIntervals :
    (∀ K : Region, ∃ (n : Nat) (left right : Fin n → ℝ),
      (∀ i, left i < right i) ∧
        closure (Complex.re '' K.openCarrier) =
          ⋃ i, Set.Icc (left i) (right i)) →
    (∀ {n : Nat} (left right : Fin n → ℝ),
      (∀ i, left i < right i) →
        Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
          (interior (⋃ i, Set.Icc (left i) (right i)))) →
    ∀ K : Region,
      Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
        (horizontalFootprint K) := by
  intro hClosure hInterior K
  obtain ⟨n, left, right, hlt, hclosed⟩ := hClosure K
  rw [show horizontalFootprint K =
      interior (⋃ i, Icc (left i) (right i)) by
        rw [horizontalFootprint, hclosed]]
  exact hInterior left right hlt

private theorem horizontalFootprint_nonempty :
    ∀ K : Region, (horizontalFootprint K).Nonempty :=
  horizontalFootprint_nonempty_local

private theorem allColumnBases_pairwiseAEDisjoint :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (∀ P : Continuous.VerticalPlate K T, Continuous.IsVerticalColumn P) →
      ∀ A : AllColumnAxisData K T,
        Set.Pairwise (Set.range A.axis)
          (AEDisjoint volume on fun x : ℝ => x +ᵥ horizontalFootprint K) := by
  intro K T hTile hAll A x hx y hy hxy
  obtain ⟨P, rfl⟩ := hx
  obtain ⟨Q, rfl⟩ := hy
  have hPQ : P ≠ Q := by
    intro h
    apply hxy
    exact congrArg A.axis h
  let _ : Countable T := hTile.1.to_subtype
  let _ : Countable (Continuous.VerticalPlate K T) := by
    apply Function.Surjective.countable
      (f := fun t : T ↦ Continuous.VerticalPlate.ofCentre (K := K) t)
    intro R
    obtain ⟨r, hr⟩ := R.nonempty_supp
    refine ⟨r, ?_⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff R r).1 hr
  have hPart := regularSupport_pairwiseDisjoint
    (@Continuous.VerticalPlate.centres K T)
    (Continuous.verticalPlateCentres_pairwiseDisjoint K T)
    (Continuous.iUnion_verticalPlateCentres K T) hTile
  have hSupportDisjoint : Disjoint P.support Q.support := by
    rw [Continuous.VerticalPlate.support_eq_regularSupport,
      Continuous.VerticalPlate.support_eq_regularSupport]
    exact hPart.1 (Set.mem_univ P) (Set.mem_univ Q) hPQ
  obtain ⟨-, hPsupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile P
  obtain ⟨-, hQsupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile Q
  have hBaseDisjoint : Disjoint P.base Q.base := by
    rw [Set.disjoint_left]
    intro z hzP hzQ
    apply Set.disjoint_left.mp hSupportDisjoint
      (show (⟨z, 0⟩ : Tiling.Plane) ∈ P.support by
        rw [hPsupport]
        exact hzP)
    rw [hQsupport]
    exact hzQ
  change AEDisjoint volume (A.axis P +ᵥ horizontalFootprint K)
    (A.axis Q +ᵥ horizontalFootprint K)
  rw [← A.base_eq P, ← A.base_eq Q]
  exact hBaseDisjoint.aedisjoint

private theorem allColumnBases_aeCover :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (∀ P : Continuous.VerticalPlate K T, Continuous.IsVerticalColumn P) →
      ∀ A : AllColumnAxisData K T,
        ∀ᵐ x ∂volume,
          ∃ a : ↥(Set.range A.axis), x ∈ (a.1 +ᵥ horizontalFootprint K) := by
  intro K T hTile hAll A
  have hopen : ∀ᵐ z : Tiling.Plane ∂volume, z ∈ openUnion K T := by
    filter_upwards [hTile.2.2] with z hz
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    exact hz.mp trivial
  have hpull :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hopen
  have hprod : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      (p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈ openUnion K T := by
    filter_upwards [hpull] with p hp
    have heq : ({ re := p.1, im := p.2 } : ℂ) =
        (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    change ({ re := p.1, im := p.2 } : ℂ) ∈ openUnion K T at hp
    rw [heq] at hp
    exact hp
  have hprod' := MeasureTheory.Measure.ae_ae_of_ae_prod hprod
  have hUV : openUnion K T ⊆
      {z : Tiling.Plane |
        ∃ a : ↥(Set.range A.axis), z.re ∈ a.1 +ᵥ horizontalFootprint K} := by
    intro z hz
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hz
    obtain ⟨s, hs⟩ := hz
    obtain ⟨w, hw, rfl⟩ := hs
    have hsUnion : (s : Tiling.Plane) ∈
        ⋃ P : Continuous.VerticalPlate K T, P.centres := by
      rw [Continuous.iUnion_verticalPlateCentres]
      exact s.2
    obtain ⟨P, hPs⟩ := Set.mem_iUnion.mp hsUnion
    have haxis := A.centres_on_axis P hPs
    change (s : Tiling.Plane).re = A.axis P at haxis
    have hwproj : w.re ∈ horizontalFootprint K := by
      exact (Complex.isOpenMap_re K.openCarrier isOpen_interior).subset_interior_closure
        ⟨w, hw, rfl⟩
    refine ⟨⟨A.axis P, ⟨P, rfl⟩⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change -(A.axis P) + ((s : Tiling.Plane).re + w.re) ∈ horizontalFootprint K
    rw [haxis]
    simpa [vadd_eq_add] using hwproj
  filter_upwards [hprod'] with x hx
  obtain ⟨y, hy⟩ := Filter.Eventually.exists hx
  obtain ⟨a, ha⟩ := hUV hy
  exact ⟨a, by simpa using ha⟩

private theorem allColumnAxes_lineTiles :
    ((∀ K : Region, ∃ (n : Nat) (left right : Fin n → ℝ),
        (∀ i, left i < right i) ∧
          closure (Complex.re '' K.openCarrier) =
            ⋃ i, Set.Icc (left i) (right i)) →
      (∀ {n : Nat} (left right : Fin n → ℝ),
        (∀ i, left i < right i) →
          Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
            (interior (⋃ i, Set.Icc (left i) (right i)))) →
      ∀ K : Region,
        Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
          (horizontalFootprint K)) →
    (∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ → Countable (Continuous.VerticalPlate K T)) →
    (∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (∀ P : Continuous.VerticalPlate K T, Continuous.IsVerticalColumn P) →
      ∀ A : AllColumnAxisData K T,
        Set.Pairwise (Set.range A.axis)
          (AEDisjoint volume on fun x : ℝ => x +ᵥ horizontalFootprint K)) →
    (∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (∀ P : Continuous.VerticalPlate K T, Continuous.IsVerticalColumn P) →
      ∀ A : AllColumnAxisData K T,
        ∀ᵐ x ∂volume,
          ∃ a : ↥(Set.range A.axis), x ∈ (a.1 +ᵥ horizontalFootprint K)) →
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (∀ P : Continuous.VerticalPlate K T, Continuous.IsVerticalColumn P) →
      ∀ A : AllColumnAxisData K T,
        Tiling.AxisParallel.OneDimensional.LineTiles
          (horizontalFootprint K) (Set.range A.axis) := by
  intro hFootprint hCount hPair hCover K T hTile hAll A
  have hB : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
      (horizontalFootprint K) :=
    hFootprint Tiling.AxisParallel.horizontalProjectionClosure_finiteClosedIntervals
      interior_finiteClosedIntervals_isFiniteIntervalRegion K
  let _ : Countable (Continuous.VerticalPlate K T) := hCount hTile
  have hBmeas : MeasurableSet (horizontalFootprint K) := by
    obtain ⟨n, a, b, hab, hEq⟩ := hB
    rw [hEq]
    exact MeasurableSet.iUnion (fun i ↦ measurableSet_Ioo)
  have hCountable : (Set.range A.axis).Countable := Set.countable_range _
  have hCover' := hCover hTile hAll A
  refine ⟨hBmeas, MeasurableSet.univ, hCountable, hPair hTile hAll A, ?_⟩
  filter_upwards [hCover'] with x hx
  constructor
  · intro _
    exact hx
  · intro _
    exact Set.mem_univ x

private structure AllColumnsLineData (K : Region) (T : Set Tiling.Plane) where
  axes : Set ℝ
  axes_eq_projection : axes = Continuous.horizontalCentreProjection T
  footprint_nonempty : (horizontalFootprint K).Nonempty
  footprint_finiteIntervals :
    Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
      (horizontalFootprint K)
  lineTiles : Tiling.AxisParallel.OneDimensional.LineTiles
    (horizontalFootprint K) axes

private theorem allColumnsLineData_exists :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ →
      (∀ P : Continuous.VerticalPlate K T, Continuous.IsVerticalColumn P) →
      Nonempty (AllColumnsLineData K T) := by
  intro K T hTile hAll
  obtain ⟨A⟩ := allColumnAxisData_exists hTile hAll
  have hline := allColumnAxes_lineTiles
    horizontalFootprint_finiteIntervals
    verticalPlates_countable
    allColumnBases_pairwiseAEDisjoint allColumnBases_aeCover hTile hAll A
  refine ⟨⟨Set.range A.axis, allColumnAxes_eq_projection hTile hAll A,
    horizontalFootprint_nonempty K,
    horizontalFootprint_finiteIntervals
      Tiling.AxisParallel.horizontalProjectionClosure_finiteClosedIntervals
      interior_finiteClosedIntervals_isFiniteIntervalRegion K, ?_⟩⟩
  exact hline

private theorem hasFLC_of_localFinite_positivePeriod
    {S : Set ℝ}
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite)
    {p : ℝ} (hp : 0 < p) (hperiod : p +ᵥ S = S) : HasFLC S := by
  have hpgroup : p ∈ Tiling.AxisParallel.periodGroup S :=
    (Tiling.AxisParallel.periodGroup_isAddSubgroup S p).mpr hperiod
  have hperiodInt : ∀ n : ℤ, (n : ℝ) * p +ᵥ S = S := by
    intro n
    have hn := (Tiling.AxisParallel.periodGroup S).zsmul_mem hpgroup n
    have hn' := (Tiling.AxisParallel.periodGroup_isAddSubgroup S _).mp hn
    simpa [smul_eq_mul] using hn'
  refine ⟨hlocal, ?_⟩
  intro R hR
  let Q : Set ℝ := Set.Icc (-R) (p + R)
  have hQfin : (S ∩ Q).Finite := hlocal Q (Metric.isBounded_Icc _ _)
  have hdiffFin : ((S ∩ Q) - (S ∩ Q)).Finite := hQfin.sub hQfin
  apply hdiffFin.subset
  rintro d ⟨hdSub, hdBall⟩
  rcases hdSub with ⟨a, ha, b, hb, rfl⟩
  have haS := ha
  have hbS := hb
  let n : ℤ := -Int.floor (a / p)
  have hncast : (n : ℝ) = -(Int.floor (a / p) : ℝ) := by
    simp [n]
  have hfloor_le : (Int.floor (a / p) : ℝ) ≤ a / p :=
    Int.floor_le (a / p)
  have hlt_floor : a / p < (Int.floor (a / p) : ℝ) + 1 :=
    Int.lt_floor_add_one (a / p)
  have hpa : (a / p) * p = a := by
    field_simp
  have hfloor_nonneg : 0 ≤ a / p - (Int.floor (a / p) : ℝ) :=
    sub_nonneg.mpr hfloor_le
  have hfloor_lt_one : a / p - (Int.floor (a / p) : ℝ) < 1 := by
    linarith
  have hAnonneg : 0 ≤ a + (n : ℝ) * p := by
    rw [hncast]
    calc
      0 ≤ (a / p - (Int.floor (a / p) : ℝ)) * p :=
        mul_nonneg hfloor_nonneg hp.le
      _ = a + (-(Int.floor (a / p) : ℝ)) * p := by
        calc
          _ = (a / p) * p - (Int.floor (a / p) : ℝ) * p := by ring
          _ = _ := by rw [hpa]; ring
  have hAless : a + (n : ℝ) * p < p := by
    rw [hncast]
    calc
      a + (-(Int.floor (a / p) : ℝ)) * p =
          (a / p - (Int.floor (a / p) : ℝ)) * p := by
            calc
              _ = (a / p) * p - (Int.floor (a / p) : ℝ) * p := by
                rw [hpa]
                ring
              _ = _ := by ring
      _ < 1 * p :=
        mul_lt_mul_of_pos_right hfloor_lt_one hp
      _ = p := one_mul p
  have hdAbs : |b - a| ≤ R := by
    simpa [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] using hdBall
  have hdiffLower : -R ≤ b - a := by
    have := (abs_le.mp hdAbs)
    linarith
  have hdiffUpper : b - a ≤ R := by
    have := (abs_le.mp hdAbs)
    linarith
  have hBnonneg : -R ≤ b + (n : ℝ) * p := by
    linarith
  have hBless : b + (n : ℝ) * p ≤ p + R := by
    linarith
  have hAshift : a + (n : ℝ) * p ∈ S := by
    have hz : (n : ℝ) * p +ᵥ a ∈ (n : ℝ) * p +ᵥ S :=
      ⟨a, haS, rfl⟩
    rw [hperiodInt n] at hz
    simpa [vadd_eq_add, add_comm] using hz
  have hBshift : b + (n : ℝ) * p ∈ S := by
    have hz : (n : ℝ) * p +ᵥ b ∈ (n : ℝ) * p +ᵥ S :=
      ⟨b, hbS, rfl⟩
    rw [hperiodInt n] at hz
    simpa [vadd_eq_add, add_comm] using hz
  refine ⟨a + (n : ℝ) * p,
    ⟨hAshift, ⟨le_trans (neg_nonpos.mpr hR.le) hAnonneg,
      le_trans (le_of_lt hAless) (le_add_of_nonneg_right hR.le)⟩⟩,
    b + (n : ℝ) * p,
    ⟨hBshift, ⟨hBnonneg, hBless⟩⟩, ?_⟩
  ring

private theorem periodicLineTiles_hasFLC :
    ∀ {B Z : Set ℝ},
      Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion B →
      B.Nonempty →
      Tiling.AxisParallel.OneDimensional.LineTiles B Z →
      (∃ p : ℝ, 0 < p ∧ p +ᵥ Z = Z) → HasFLC Z := by
  intro B Z hB hBne hTile hper
  let P : IntervalPresentation B := IntervalPresentation.ofIsFiniteIntervalRegion hB
  have hBpositive : 0 < (volume B).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨P.isOpen.measure_pos volume hBne,
      (lt_top_iff_ne_top.mpr P.volume_ne_top)⟩
  obtain ⟨p, hp, hperiod⟩ := hper
  exact hasFLC_of_localFinite_positivePeriod
    (finiteInterval_lineTilesOn_centres_locallyFinite hB hBpositive hTile)
    hp hperiod

private theorem allVerticalPlatesColumns_finiteHorizontalComplexity :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ →
      (∀ P : Continuous.VerticalPlate K T, Continuous.IsVerticalColumn P) →
      Continuous.HasFiniteHorizontalComplexity T := by
  intro K T hTile hAll
  obtain ⟨D⟩ := allColumnsLineData_exists hTile hAll
  let P : IntervalPresentation (horizontalFootprint K) :=
    IntervalPresentation.ofIsFiniteIntervalRegion D.footprint_finiteIntervals
  have hBpositive : 0 < (volume (horizontalFootprint K)).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨P.isOpen.measure_pos volume D.footprint_nonempty,
      lt_top_iff_ne_top.mpr P.volume_ne_top⟩
  obtain ⟨p, hp, hperiod⟩ :=
    exists_positiveLinePeriod D.footprint_finiteIntervals hBpositive D.lineTiles
  have hFLC : HasFLC D.axes :=
    periodicLineTiles_hasFLC D.footprint_finiteIntervals
      D.footprint_nonempty D.lineTiles ⟨p, hp, hperiod⟩
  simpa [Continuous.HasFiniteHorizontalComplexity, D.axes_eq_projection] using hFLC

private def columnAggregateBase (K : Region) (T : Set Tiling.Plane) : Set ℝ :=
  Complex.re '' (regularSupport K (Continuous.verticalColumnCentres K T))

private theorem columnAggregate_support_isCylinder :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ →
      regularSupport K (Continuous.verticalColumnCentres K T) =
        Complex.re ⁻¹' columnAggregateBase K T := by
  intro K T hTile
  let D := regularSupport K (Continuous.verticalColumnCentres K T)
  have hInvariant : ∀ y : ℝ, (((y : ℂ) * Complex.I) +ᵥ D) = D := by
    intro y
    dsimp only [D]
    rw [Continuous.verticalColumnCentres_eq, regularSupport_iUnion]
    rw [← interior_vadd, ← closure_vadd]
    congr 2
    ext z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_iUnion]
    constructor
    · rintro ⟨P, hzP⟩
      refine ⟨P, ?_⟩
      have hinv := (Continuous.VerticalPlate.isCenterColumn_of_isVerticalColumn
        hTile P.1 P.2).2.2.2 y
      have hmem := Set.ext_iff.mp hinv z
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem] at hmem
      exact hmem.mp hzP
    · rintro ⟨P, hzP⟩
      refine ⟨P, ?_⟩
      have hinv := (Continuous.VerticalPlate.isCenterColumn_of_isVerticalColumn
        hTile P.1 P.2).2.2.2 y
      have hmem := Set.ext_iff.mp hinv z
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem] at hmem
      exact hmem.mpr hzP
  obtain ⟨X, hDX⟩ := (verticalInvariant_iff_product D).mp hInvariant
  have hbase : columnAggregateBase K T = X := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change z ∈ {w : Tiling.Plane | w.re ∈ X}
      rw [← hDX]
      exact hz
    · intro hx
      refine ⟨(x : ℂ), ?_, by simp⟩
      change (x : ℂ) ∈ D
      rw [hDX]
      simpa
  rw [hbase]
  exact hDX

private theorem columnAggregate_frontier_subset_componentBoundarySet :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ →
      frontier (columnAggregateBase K T) ⊆
        Tiling.AxisParallel.Structure.componentBoundarySet K T := by
  intro K T hTile x hx
  by_contra hxBoundary
  have hclosed := componentBoundarySet_closed hTile
  have hxCompl : x ∈ (componentBoundarySet K T)ᶜ := hxBoundary
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl x hxCompl
  let J : Set ℝ := Metric.ball x ε
  have hJboundary : Disjoint J (componentBoundarySet K T) := by
    rw [Set.disjoint_left]
    intro y hyJ hyB
    exact (hball hyJ) hyB
  have hxClosure : x ∈ closure (columnAggregateBase K T) :=
    frontier_subset_closure hx
  have hJopen : IsOpen J := Metric.isOpen_ball
  obtain ⟨y, hyJ, hyBase⟩ :=
    (mem_closure_iff.mp hxClosure) J hJopen (Metric.mem_ball_self hε)
  let z : Tiling.Plane := (y : ℂ)
  have hzSupport : z ∈ regularSupport K
      (Continuous.verticalColumnCentres K T) := by
    rw [columnAggregate_support_isCylinder hTile]
    exact hyBase
  have hzClosure : z ∈ closure
      (openUnion K (Continuous.verticalColumnCentres K T)) := by
    exact interior_subset hzSupport
  let O : Set Tiling.Plane := Complex.re ⁻¹' J
  have hOopen : IsOpen O := hJopen.preimage Complex.continuous_re
  have hzO : z ∈ O := by exact hyJ
  obtain ⟨w, hwO, hwUnion⟩ :=
    (mem_closure_iff.mp hzClosure) O hOopen hzO
  rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hwUnion
  obtain ⟨s, hsPlaced⟩ := hwUnion
  have hsColumn' : s.1 ∈
      ⋃ P : {P : Continuous.VerticalPlate K T | Continuous.IsVerticalColumn P},
        P.1.centres := by
    rw [← Continuous.verticalColumnCentres_eq]
    exact s.2
  rw [Set.mem_iUnion] at hsColumn'
  obtain ⟨P, hsP⟩ := hsColumn'
  have hwOpenP : w ∈ openUnion K P.1.centres := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨s.1, hsP⟩, hsPlaced⟩
  have hwSupportP : w ∈ P.1.support := by
    rw [Continuous.VerticalPlate.support_eq_regularSupport]
    unfold regularSupport
    have hopen : IsOpen (openUnion K P.1.centres) := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
      exact isOpen_iUnion fun t : P.1.centres ↦ isOpen_interior.vadd t.1
    exact hopen.subset_interior_closure hwOpenP
  obtain ⟨-, hPSupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile P.1
  have hwBaseP : w.re ∈ P.1.base := by
    rw [hPSupport] at hwSupportP
    exact hwSupportP
  have hJfrontierP : Disjoint J (frontier P.1.base) := by
    apply hJboundary.mono_right
    intro q hq
    rw [componentBoundarySet_eq, Set.mem_iUnion]
    exact ⟨P.1, hq⟩
  have hJpre : IsPreconnected J := (convex_ball x ε).isPreconnected
  rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      hJpre hJfrontierP with hinside | houtside
  · have hxBaseP : x ∈ P.1.base := by
      exact interior_subset (hinside (Metric.mem_ball_self hε))
    have hxColumnSupport : (x : ℂ) ∈ regularSupport K
        (Continuous.verticalColumnCentres K T) := by
      rw [Continuous.verticalColumnCentres_eq, regularSupport_iUnion]
      apply mem_interior_iff_mem_nhds.mpr
      have hxP : (x : ℂ) ∈ P.1.support := by
        rw [hPSupport]
        exact hxBaseP
      have hPopen : IsOpen P.1.support := by
        rw [Continuous.VerticalPlate.support_eq_regularSupport]
        exact isOpen_interior
      apply Filter.mem_of_superset (hPopen.mem_nhds hxP)
      exact (Set.subset_iUnion (fun Q : {Q : Continuous.VerticalPlate K T |
        Continuous.IsVerticalColumn Q} ↦ Q.1.support) P).trans subset_closure
    have hxAggregate : x ∈ columnAggregateBase K T :=
      ⟨(x : ℂ), hxColumnSupport, by simp⟩
    have hAggregateOpen : IsOpen (columnAggregateBase K T) := by
      exact Complex.isOpenMap_re _ isOpen_interior
    exact hx.2 (by rwa [hAggregateOpen.interior_eq])
  · have hwOutside := interior_subset (houtside hwO)
    exact hwOutside hwBaseP

private theorem properPeriodicRegularOpen_frontierRelativelyDense :
    ∀ {X : Set ℝ} {p : ℝ}, IsOpen X → interior (closure X) = X →
      X.Nonempty → X ≠ univ → p ≠ 0 →
      Tiling.RationalPolygonal.SetPeriodicBy (Complex.re ⁻¹' X) ((p : ℝ) : ℂ) →
      ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ,
        (frontier X ∩ Icc x (x + M)).Nonempty := by
  intro X p hXopen hXregular hXne hXproper hp hperiod
  have hfront : (frontier X).Nonempty := by
    by_contra hempty
    have hfrontEmpty := Set.not_nonempty_iff_eq_empty.mp hempty
    rcases frontier_eq_empty_iff.mp hfrontEmpty with h | h
    · exact hXne.ne_empty h
    · exact hXproper h
  obtain ⟨c, hc⟩ := hfront
  have hbasePeriod : ∀ t : ℝ, t + p ∈ X ↔ t ∈ X := by
    intro t
    have h := hperiod (t : ℂ)
    simpa using h
  have hbaseVadd : p +ᵥ X = X := by
    ext t
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [sub_eq_add_neg, add_comm] using (hbasePeriod (t - p)).symm
  have hfrontPeriod : p +ᵥ frontier X = frontier X := by
    have hi := (Homeomorph.vaddConst p).image_frontier X
    have himage (S : Set ℝ) : (Homeomorph.vaddConst p : ℝ → ℝ) '' S = p +ᵥ S := by
      ext t
      simp only [Set.mem_image, Set.mem_vadd_set_iff_neg_vadd_mem,
        Homeomorph.vaddConst_apply, vadd_eq_add]
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa [add_comm] using hu
      · intro ht
        exact ⟨t - p, by simpa [sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc] using ht, by simp⟩
    rw [himage, himage, hbaseVadd] at hi
    exact hi
  let q := |p|
  have hq : 0 < q := abs_pos.mpr hp
  refine ⟨q, hq, ?_⟩
  intro x
  let n : ℤ := ⌈(x - c) / q⌉
  let y : ℝ := c + n * q
  have hylo : x ≤ y := by
    dsimp [y, n]
    have hn : (x - c) / q ≤ (⌈(x - c) / q⌉ : ℤ) := Int.le_ceil _
    have hmul := (mul_le_mul_of_nonneg_right hn hq.le)
    calc
      x = c + ((x - c) / q) * q := by field_simp; ring
      _ ≤ c + ((⌈(x - c) / q⌉ : ℤ) : ℝ) * q := by gcongr
      _ = y := rfl
  have hyhi : y ≤ x + q := by
    dsimp [y, n]
    have hn : ((⌈(x - c) / q⌉ : ℤ) : ℝ) < (x - c) / q + 1 := Int.ceil_lt_add_one _
    have hmul := (mul_lt_mul_of_pos_right hn hq)
    exact (calc
      y < c + (((x - c) / q) + 1) * q := by
        dsimp [y, n]
        gcongr
      _ = x + q := by field_simp; ring
      ).le
  have hqperiod : q +ᵥ frontier X = frontier X := by
    rcases abs_choice p with hpnonneg | hpneg
    · simpa [q, hpnonneg] using hfrontPeriod
    · have hneg : (-p) +ᵥ frontier X = frontier X := by
        calc
          (-p) +ᵥ frontier X = (-p) +ᵥ (p +ᵥ frontier X) := by rw [hfrontPeriod]
          _ = frontier X := by simp only [vadd_vadd, neg_add_cancel, zero_vadd]
      simpa [q, hpneg] using hneg
  have hyfront : y ∈ frontier X := by
    have hf : Function.Periodic (fun t : ℝ ↦ t ∈ frontier X) q := by
      intro t
      have ht := Set.ext_iff.mp hqperiod (q + t)
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm] using ht.symm
    have := hf.zsmul n c
    simpa [y, zsmul_eq_mul, add_comm, mul_comm] using (this.mpr hc)
  exact ⟨y, hyfront, hylo, hyhi⟩

private theorem genericHeight_near_local
    (K : Region) (y ε : ℝ) (hε : 0 < ε) :
    ∃ y', y' ∈ Ioo (y - ε / 2) (y + ε / 2) ∧
      y' ∉ K.vertexFinset.image Complex.im := by
  let J : Set ℝ := Ioo (y - ε / 2) (y + ε / 2)
  have hJNotCountable : ¬ J.Countable := by
    change ¬ (Ioo (y - ε / 2) (y + ε / 2)).Countable
    rw [Cardinal.Real.Ioo_countable_iff]
    linarith
  by_contra hNo
  push Not at hNo
  have hSubset : J ⊆ (K.vertexFinset.image Complex.im : Set ℝ) := by
    intro z hz
    exact hNo z hz
  exact hJNotCountable
    ((K.vertexFinset.image Complex.im).finite_toSet.countable.mono hSubset)

private theorem maximal_right_mem_frontier_local {B : Set ℝ}
    (P : Tiling.AxisParallel.Foundations.GenericSlices.MaximalIntervalPresentation B)
    (i : Fin P.n) : P.right i ∈ frontier B := by
  have hcl : P.right i ∈ closure B := by
    rw [P.closure_eq]
    exact mem_iUnion.2 ⟨i, ⟨(P.lt i).le, le_rfl⟩⟩
  rw [frontier]
  refine ⟨hcl, ?_⟩
  intro hint
  have hmem : P.right i ∈ B := interior_subset hint
  have hmem' : P.right i ∈ ⋃ j, Ioo (P.left j) (P.right j) :=
    P.union_eq ▸ hmem
  rcases mem_iUnion.1 hmem' with ⟨j, hj⟩
  by_cases hij : i = j
  · subst j
    exact (lt_irrefl _ hj.2)
  · rcases P.pairwise_gap i j hij with hgap | hgap
    · linarith [hj.1]
    · linarith [P.lt i, hj.2]

private theorem wideComponent_hasDeepTranslatedVerticalSide :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ (P : Continuous.VerticalPlate K T)
        (c d : ↥(componentBoundarySet K T)),
      c.1 < d.1 → Ioo c.1 d.1 ⊆ P.base →
      Ioo c.1 d.1 ∩ componentBoundarySet K T = ∅ →
      ∀ R : ℝ, 0 < R → R < d.1 - c.1 →
      ∃ (t : ↥T) (v w : ↥K.vertices),
        (t.1 : Tiling.Plane) ∈ P.centres ∧
        v.1 ≠ w.1 ∧ v.1.re = w.1.re ∧
        openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices ∧
        c.1 + R < (v.1 + (t.1 : Tiling.Plane)).re ∧
        (v.1 + (t.1 : Tiling.Plane)).re ≤ d.1 := by
  intro K T hTile P c d hcd hBase hGap R hR hRgap
  let x : ℝ := (c.1 + R + d.1) / 2
  have hx : x ∈ Ioo (c.1 + R) d.1 := by
    constructor <;> dsimp [x] <;> linarith
  have hxGap : x ∈ Ioo c.1 d.1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hPsub : P.centres ⊆ T := by
    rintro s ⟨q, hq, rfl⟩
    exact q.2
  obtain ⟨hPRegular, hPsupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile P
  have hPsupportRegular : P.support = regularSupport K P.centres :=
    Continuous.VerticalPlate.support_eq_regularSupport P
  let D : Set Tiling.Plane := Complex.re ⁻¹' Ioo (c.1 + R) d.1
  let q0 : Tiling.Plane := ⟨x, 0⟩
  have hDOpen : IsOpen D := isOpen_Ioo.preimage Complex.continuous_re
  have hq0D : q0 ∈ D := by
    change x ∈ Ioo (c.1 + R) d.1
    exact hx
  have hq0Support : q0 ∈ P.support := by
    rw [hPsupport]
    change x ∈ P.base
    exact hBase hxGap
  have hq0Closure : q0 ∈ closure (openUnion K P.centres) := by
    rw [hPsupportRegular, regularSupport] at hq0Support
    exact interior_subset hq0Support
  have hMeet : (D ∩ openUnion K P.centres).Nonempty :=
    (mem_closure_iff.mp hq0Closure) D hDOpen hq0D
  obtain ⟨q, hqD, hqOpen⟩ := hMeet
  rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hqOpen
  obtain ⟨tP, hqt⟩ := hqOpen
  let t : ↥T := ⟨tP.1, hPsub tP.2⟩
  have htP : (t.1 : Tiling.Plane) ∈ P.centres := tP.2
  have hqp : q = t.1 + (q - t.1) := by simp
  let p : Tiling.Plane := q - t.1
  have hpOpen : p ∈ K.openCarrier := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hqt
    simpa only [p, vadd_eq_add, neg_add_eq_sub] using hqt
  obtain ⟨ε, hε, hBall⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) p hpOpen
  obtain ⟨y, hyNear, hyGeneric⟩ := genericHeight_near_local K p.im ε hε
  let p' : Tiling.Plane := Complex.mk p.re y
  have hp'Ball : p' ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Complex.dist_of_re_eq]
    · rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hyNear.1, hyNear.2]
    · rfl
  have hp'Open : p' ∈ K.openCarrier := hBall hp'Ball
  obtain ⟨H⟩ :=
    Tiling.AxisParallel.Foundations.GenericSlices.horizontalGenericSlicePresentation_exists
      K hyGeneric
  have hp'Slice : p.re ∈
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K y := by
    change Complex.mk p.re y ∈ K.openCarrier
    exact hp'Open
  rw [H.union_eq, Set.mem_iUnion] at hp'Slice
  obtain ⟨i, hpi⟩ := hp'Slice
  let v₀ : ↑K.vertices := H.leftVertex i
  let w₀ : ↑K.vertices := H.rightVertex i
  have hvCoord : v₀.1.re = H.left i := H.leftVertex_coord i
  have hwCoord : w₀.1.re = H.right i := H.rightVertex_coord i
  have hvw₀ : v₀.1.re < w₀.1.re := by
    rw [hvCoord, hwCoord]
    exact H.lt i
  have hSlice : Ioo v₀.1.re w₀.1.re ⊆
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K y := by
    intro r hr
    have hr' : r ∈ Ioo (H.left i) (H.right i) := by
      rwa [← hvCoord, ← hwCoord]
    rw [H.union_eq, Set.mem_iUnion]
    exact ⟨i, hr'⟩
  have hwFrontierSlice : H.right i ∈ frontier
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K y) :=
    maximal_right_mem_frontier_local H.toMaximalIntervalPresentation i
  have hwFrontier : Complex.mk w₀.1.re y ∈ frontier K.support := by
    rw [hwCoord]
    exact Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice_frontier_lifts
      K hyGeneric hwFrontierSlice
  have hTranslatedSliceBase :
      Ioo (v₀.1.re + t.1.re) (w₀.1.re + t.1.re) ⊆ P.base := by
    intro r hr
    have hrSource : r - t.1.re ∈ Ioo v₀.1.re w₀.1.re := by
      constructor <;> linarith [hr.1, hr.2]
    have hrCarrier := hSlice hrSource
    have htwOpen : Complex.mk r (y + t.1.im) ∈ openUnion K P.centres := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      refine ⟨tP, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change Complex.mk (r - t.1.re) y ∈ K.openCarrier at hrCarrier
      change -(t.1 : Tiling.Plane) + Complex.mk r (y + t.1.im) ∈ K.openCarrier
      have heq : -(t.1 : Tiling.Plane) + Complex.mk r (y + t.1.im) =
          Complex.mk (r - t.1.re) y := by
        apply Complex.ext
        · simp
          ring
        · simp
      rw [heq]
      exact hrCarrier
    have hOpenUnionP : IsOpen (openUnion K P.centres) := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
      exact isOpen_iUnion fun q : ↥P.centres ↦
        (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _ isOpen_interior
    have htwSupport : Complex.mk r (y + t.1.im) ∈ P.support := by
      rw [hPsupportRegular, regularSupport]
      exact hOpenUnionP.subset_interior_closure htwOpen
    rw [P.base_eq]
    exact ⟨Complex.mk r (y + t.1.im), htwSupport, rfl⟩
  have haNotBase := componentBoundary_not_mem_plateBase hTile c.2 P
  have hbNotBase := componentBoundary_not_mem_plateBase hTile d.2 P
  have hqReGap : q.re ∈ Ioo (c.1 + R) d.1 := hqD
  have hpReInterval : p.re ∈ Ioo v₀.1.re w₀.1.re := by
    rwa [hvCoord, hwCoord]
  have hqReInterval : q.re ∈
      Ioo (v₀.1.re + t.1.re) (w₀.1.re + t.1.re) := by
    have hqRe := congrArg Complex.re hqp
    simp only [Complex.add_re] at hqRe
    constructor <;> linarith [hpReInterval.1, hpReInterval.2]
  have hTranslatedInside :
      Ioo (v₀.1.re + t.1.re) (w₀.1.re + t.1.re) ⊆ Ioo c.1 d.1 := by
    intro r hr
    constructor
    · by_contra hra
      apply haNotBase
      apply hTranslatedSliceBase
      exact ⟨by linarith [hr.1], by linarith [hqReInterval.2, hqReGap.1]⟩
    · by_contra hrb
      apply hbNotBase
      apply hTranslatedSliceBase
      exact ⟨by linarith [hqReInterval.1, hqReGap.2], by linarith [hr.2]⟩
  have hwNotVertex : Complex.mk w₀.1.re y ∉ K.vertices := by
    intro hw
    apply hyGeneric
    exact Finset.mem_image.mpr
      ⟨Complex.mk w₀.1.re y,
        (K.isPolygonal.vertexSet_finite.mem_toFinset).2 hw, rfl⟩
  obtain ⟨axis, v, w, hvw, htrans, hpoint, hseg⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge
      K (Complex.mk w₀.1.re y)
      hwFrontier hwNotVertex
  have haxis : axis = Axis.vertical := by
    cases axis with
    | horizontal =>
        have him : v.1.im = w.1.im := by
          simpa [Axis.transverseCoord] using htrans
        rw [openSegment_eq_image] at hpoint
        obtain ⟨u, hu, hupt⟩ := hpoint
        have hzim : (Complex.mk w₀.1.re y).im = v.1.im := by
          rw [← hupt]
          simp [him]
          ring
        apply False.elim
        apply hyGeneric
        apply Finset.mem_image.mpr
        refine ⟨v.1, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 v.2, ?_⟩
        simpa using hzim.symm
    | vertical => rfl
  subst axis
  have hvwRe : v.1.re = w.1.re := by
    simpa [Axis.transverseCoord] using htrans
  have hpointRe : v.1.re = w₀.1.re := by
    rw [openSegment_eq_image] at hpoint
    obtain ⟨u, hu, hupt⟩ := hpoint
    have hre := congrArg Complex.re hupt
    simp [hvwRe] at hre
    ring_nf at hre
    exact hvwRe.trans hre
  have hleft : c.1 + R < (v.1 + (t.1 : Tiling.Plane)).re := by
    simp only [Complex.add_re]
    rw [hpointRe]
    linarith [hqReGap.1, hqReInterval.2]
  have hright : (v.1 + (t.1 : Tiling.Plane)).re ≤ d.1 := by
    simp only [Complex.add_re]
    rw [hpointRe]
    have hlt : v₀.1.re + t.1.re < w₀.1.re + t.1.re := by linarith
    exact (Set.Ioo_subset_Ioo_iff hlt).mp hTranslatedInside |>.2
  exact ⟨t, v, w, htP, hvw, hvwRe, hseg, hleft, hright⟩

open Tiling.AxisParallel.Approximation
private theorem mappedHorizontalStep_min :
    ∀ (C : ApproximationContext.{0})
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (D : CoordinateDeformation C phi),
      ∃ eta : ℝ, 0 < eta ∧
        ∀ a b : ↥C.region.vertices, a.1.re < b.1.re →
          eta ≤ (D.planarHomeomorph b.1).re -
            (D.planarHomeomorph a.1).re := by
  intro C phi D
  classical
  let pairs : Finset (↥C.region.vertexFinset × ↥C.region.vertexFinset) :=
    (Finset.univ.product Finset.univ).filter
      (fun ab ↦ ab.1.1.re < ab.2.1.re)
  let gaps : Finset ℝ := pairs.image (fun ab ↦
    (D.planarHomeomorph ab.2.1).re - (D.planarHomeomorph ab.1.1).re)
  by_cases hpairs : pairs.Nonempty
  · have hgaps : gaps.Nonempty := Finset.image_nonempty.mpr hpairs
    refine ⟨gaps.min' hgaps, ?_, ?_⟩
    · obtain ⟨g, hg, hgeq⟩ := Finset.mem_image.mp (Finset.min'_mem gaps hgaps)
      rw [← hgeq]
      have hlt : g.1.1.re < g.2.1.re := (Finset.mem_filter.mp hg).2
      rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
      simpa using sub_pos.mpr (D.firstHomeomorph_strictMono hlt)
    · intro a b hab
      apply Finset.min'_le
      apply Finset.mem_image.mpr
      let a' : ↥C.region.vertexFinset :=
        ⟨a.1, (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 a.2⟩
      let b' : ↥C.region.vertexFinset :=
        ⟨b.1, (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 b.2⟩
      refine ⟨(a', b'), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hab⟩
      · rfl
  · refine ⟨1, zero_lt_one, ?_⟩
    intro a b hab
    exfalso
    apply hpairs
    let a' : ↥C.region.vertexFinset :=
      ⟨a.1, (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 a.2⟩
    let b' : ↥C.region.vertexFinset :=
      ⟨b.1, (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 b.2⟩
    exact ⟨(a', b'), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hab⟩⟩

private theorem longBoundaryWord_mappedLength :
    ∀ {m : ℕ} (d dphi : Fin m → ℝ) {Dmax eta L : ℝ},
      0 < Dmax → 0 < eta → 0 ≤ L →
      (∀ i, 0 < d i ∧ d i ≤ Dmax) →
      (∀ i, eta ≤ dphi i) →
      Dmax * (L / eta + 1) < ∑ i, d i →
      L < ∑ i, dphi i := by
  intro m d dphi Dmax eta L hD hEta hL hd hdphi hlong
  have hsumD : ∑ i, d i ≤ ∑ _i : Fin m, Dmax :=
    Finset.sum_le_sum fun i _ ↦ (hd i).2
  have hsumPhi : ∑ _i : Fin m, eta ≤ ∑ i, dphi i :=
    Finset.sum_le_sum fun i _ ↦ hdphi i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsumD hsumPhi
  have hEtaNe : eta ≠ 0 := ne_of_gt hEta
  have hquot : L / eta * eta = L := by field_simp
  have hcount : Dmax * (L / eta + 1) < (m : ℝ) * Dmax :=
    lt_of_lt_of_le hlong hsumD
  have hbase : L < (m : ℝ) * eta := by
    nlinarith
  exact lt_of_lt_of_le hbase hsumPhi

private abbrev NontrivialDecomposition
    (K : Region) (T : Set Tiling.Plane) : Prop :=
  ¬ ∃ P : Continuous.VerticalPlate K T,
    ¬ Continuous.IsVerticalColumn P ∧ P.centres = T

private theorem periodicColumnAggregate_finiteHorizontalComplexity :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ → NontrivialDecomposition K T →
      (columnAggregateBase K T).Nonempty →
      (∃ p : ℝ, p ≠ 0 ∧
        Tiling.RationalPolygonal.SetPeriodicBy
          (regularSupport K (Continuous.verticalColumnCentres K T))
          ((p : ℝ) : ℂ)) →
      Continuous.HasFiniteHorizontalComplexity T := by
  intro K T hTile hNontrivial hbaseNonempty hperiod
  by_cases hall : ∀ P : Continuous.VerticalPlate K T,
      Continuous.IsVerticalColumn P
  · exact allVerticalPlatesColumns_finiteHorizontalComplexity hTile hall
  push Not at hall
  obtain ⟨P, hPnoncolumn⟩ := hall
  have hSupport := columnAggregate_support_isCylinder hTile
  have hbaseOpen : IsOpen (columnAggregateBase K T) := by
    have hopen : IsOpen (Complex.re ⁻¹' columnAggregateBase K T) := by
      rw [← hSupport]
      exact (regularSupport_isRegularOpen K
        (Continuous.verticalColumnCentres K T)).1
    have hsection : Continuous (fun x : ℝ ↦ (x : ℂ)) := by fun_prop
    have hopen' := hopen.preimage hsection
    convert hopen' using 1
    ext x
    simp
  have hbaseRegular : interior (closure (columnAggregateBase K T)) =
      columnAggregateBase K T := by
    have hreg := (regularSupport_isRegularOpen K
      (Continuous.verticalColumnCentres K T)).2
    rw [hSupport, Complex.closure_preimage_re,
      Complex.interior_preimage_re] at hreg
    ext x
    have hx := Set.ext_iff.mp hreg (x : ℂ)
    simpa using hx
  have hbaseProper : columnAggregateBase K T ≠ univ := by
    intro hbaseAll
    obtain ⟨t, ht⟩ := P.nonempty_supp
    have htP : (t.1 : Tiling.Plane) ∈ P.centres :=
      ⟨t, (SimpleGraph.ConnectedComponent.mem_supp_iff P t).1 ht, rfl⟩
    obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hpointP : (t.1 : Tiling.Plane) + u ∈ P.support := by
      rw [P.support_eq_regularSupport]
      unfold regularSupport
      have hopen : IsOpen (openUnion K P.centres) := by
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
        exact isOpen_iUnion fun s ↦ isOpen_interior.vadd s.1
      apply hopen.subset_interior_closure
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      exact ⟨⟨t.1, htP⟩, u, hu, rfl⟩
    have hpointAgg : (t.1 : Tiling.Plane) + u ∈
        regularSupport K (Continuous.verticalColumnCentres K T) := by
      rw [hSupport, hbaseAll]
      trivial
    let _ : Countable T := hTile.1.to_subtype
    let _ : Countable (Continuous.VerticalPlate K T) :=
      verticalPlates_countable hTile
    have hpart := regularSupport_pairwiseDisjoint
      (@Continuous.VerticalPlate.centres K T)
      (Continuous.verticalPlateCentres_pairwiseDisjoint K T)
      (Continuous.iUnion_verticalPlateCentres K T) hTile
    let U := ⋃ Q : {Q : Continuous.VerticalPlate K T |
      Continuous.IsVerticalColumn Q}, regularSupport K Q.1.centres
    have hdisj : Disjoint U P.support := by
      rw [Set.disjoint_iUnion_left]
      intro Q
      rw [P.support_eq_regularSupport]
      have hQP : Q.1 ≠ P := fun h ↦ hPnoncolumn (h ▸ Q.2)
      exact hpart.1 (Set.mem_univ Q.1) (Set.mem_univ P) hQP
    have hPopen : IsOpen P.support := by
      rw [P.support_eq_regularSupport]
      exact isOpen_interior
    have hdisjClosure : Disjoint P.support (closure U) :=
      hdisj.symm.closure_right hPopen
    have hpointClosure : (t.1 : Tiling.Plane) + u ∈ closure U := by
      apply interior_subset
      simpa only [U, Continuous.verticalColumnCentres_eq,
        regularSupport_iUnion] using hpointAgg
    exact Set.disjoint_left.mp hdisjClosure hpointP hpointClosure
  obtain ⟨p, hp, hpSupport⟩ := hperiod
  have hpBase : Tiling.RationalPolygonal.SetPeriodicBy
      (Complex.re ⁻¹' columnAggregateBase K T) ((p : ℝ) : ℂ) := by
    rwa [← hSupport]
  obtain ⟨M, hM, hfront⟩ :=
    properPeriodicRegularOpen_frontierRelativelyDense
      hbaseOpen hbaseRegular hbaseNonempty hbaseProper hp hpBase
  apply finiteHorizontalComplexity_of_relativelyDenseBoundaries
    hTile hNontrivial
  refine ⟨M, hM, ?_⟩
  intro x
  obtain ⟨y, hyfront, hyIcc⟩ := hfront x
  exact ⟨y, columnAggregate_frontier_subset_componentBoundarySet hTile hyfront,
    hyIcc⟩

private theorem twoNoncolumnPlates_boundariesRelativelyDense
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (hTwo : ∃ P Q : Continuous.VerticalPlate K T,
      P ≠ Q ∧ ¬ Continuous.IsVerticalColumn P ∧
        ¬ Continuous.IsVerticalColumn Q) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ,
      (componentBoundarySet K T ∩ Icc x (x + M)).Nonempty := by
  exact componentBoundarySet_relativelyDense_of_two_noncolumnPlates hTile hTwo

private theorem columnAggregate_empty_hasTwoNoncolumnPlates :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ → NontrivialDecomposition K T →
      columnAggregateBase K T = ∅ →
      ∃ P Q : Continuous.VerticalPlate K T,
        P ≠ Q ∧ ¬ Continuous.IsVerticalColumn P ∧
          ¬ Continuous.IsVerticalColumn Q := by
  intro K T hTile hNontrivial hbaseEmpty
  have hNoColumn (P : Continuous.VerticalPlate K T) :
      ¬ Continuous.IsVerticalColumn P := by
    intro hPcolumn
    obtain ⟨t, ht⟩ := P.nonempty_supp
    have htP : (t.1 : Tiling.Plane) ∈ P.centres :=
      ⟨t, (SimpleGraph.ConnectedComponent.mem_supp_iff P t).1 ht, rfl⟩
    have htColumn : (t.1 : Tiling.Plane) ∈
        Continuous.verticalColumnCentres K T := by
      rw [Continuous.verticalColumnCentres_eq, Set.mem_iUnion]
      exact ⟨⟨P, hPcolumn⟩, htP⟩
    obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hpoint : t.1 + u ∈ regularSupport K
        (Continuous.verticalColumnCentres K T) := by
      unfold regularSupport
      have hopen : IsOpen (openUnion K (Continuous.verticalColumnCentres K T)) := by
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
        exact isOpen_iUnion fun s ↦ isOpen_interior.vadd s.1
      apply hopen.subset_interior_closure
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      exact ⟨⟨t.1, htColumn⟩, u, hu, rfl⟩
    have : (t.1 + u).re ∈ columnAggregateBase K T := ⟨t.1 + u, hpoint, rfl⟩
    simp [hbaseEmpty] at this
  have hTne : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hwhole : regularSupport K T = Set.univ :=
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile
    rw [hTempty, regularSupport, Tiling.Polygonal.regularSupport,
      Tiling.Polygonal.openUnion] at hwhole
    have hemptyUniv : (∅ : Set Tiling.Plane) = univ := by simpa using hwhole
    have hz : (0 : Tiling.Plane) ∈ (∅ : Set Tiling.Plane) := by
      rw [hemptyUniv]
      trivial
    simp at hz
  obtain ⟨t, htT⟩ := hTne
  let P := Continuous.VerticalPlate.ofCentre (K := K) ⟨t, htT⟩
  have htP : t ∈ P.centres := Continuous.VerticalPlate.mem_centres_ofCentre ⟨t, htT⟩
  have hPproper : P.centres ≠ T := by
    intro hPT
    exact hNontrivial ⟨P, hNoColumn P, hPT⟩
  have hPsub : P.centres ⊆ T := by
    rintro s ⟨q, hq, rfl⟩
    exact q.2
  obtain ⟨q, hqT, hqP⟩ := Set.not_subset.mp (fun hTP ↦
    hPproper (Set.Subset.antisymm hPsub hTP))
  let Q := Continuous.VerticalPlate.ofCentre (K := K) ⟨q, hqT⟩
  have hqQ : q ∈ Q.centres := Continuous.VerticalPlate.mem_centres_ofCentre ⟨q, hqT⟩
  have hPQ : P ≠ Q := by
    intro h
    apply hqP
    rwa [h]
  exact ⟨P, Q, hPQ, hNoColumn P, hNoColumn Q⟩

private theorem notFiniteComplexity_implies_columnBaseAperiodic :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ → NontrivialDecomposition K T →
      ¬ Continuous.HasFiniteHorizontalComplexity T →
      (regularSupport K (Continuous.verticalColumnCentres K T)).Nonempty ∧
        ∀ beta : ℝ, beta ≠ 0 →
          ¬ Tiling.RationalPolygonal.SetPeriodicBy
            (regularSupport K (Continuous.verticalColumnCentres K T)) ((beta : ℝ) : ℂ) := by
  intro K T hTile hNontrivial hInfinite
  have hSupportNonempty :
      (regularSupport K (Continuous.verticalColumnCentres K T)).Nonempty := by
    by_contra hEmpty
    have hbaseEmpty : columnAggregateBase K T = ∅ := by
      unfold columnAggregateBase
      rw [Set.not_nonempty_iff_eq_empty.mp hEmpty]
      simp
    obtain ⟨P, Q, hPQ, hP, hQ⟩ :=
      columnAggregate_empty_hasTwoNoncolumnPlates hTile hNontrivial hbaseEmpty
    apply hInfinite
    apply finiteHorizontalComplexity_of_relativelyDenseBoundaries hTile hNontrivial
    exact twoNoncolumnPlates_boundariesRelativelyDense hTile ⟨P, Q, hPQ, hP, hQ⟩
  refine ⟨hSupportNonempty, ?_⟩
  intro beta hbeta hperiod
  apply hInfinite
  apply periodicColumnAggregate_finiteHorizontalComplexity hTile hNontrivial
  · exact hSupportNonempty.image Complex.re
  · exact ⟨beta, hbeta, hperiod⟩
private theorem uniqueNoncolumn_notWide_boundariesRelativelyDense :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ →
      ∀ P : Continuous.VerticalPlate K T,
        ¬ Continuous.IsVerticalColumn P →
        (∀ Q : Continuous.VerticalPlate K T,
          ¬ Continuous.IsVerticalColumn Q → Q = P) →
        (∃ R : ℝ, 0 < R ∧ ∀ a : ℝ,
          ¬ Ioo a (a + 2 * R) ⊆ P.base) →
        ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ,
          (componentBoundarySet K T ∩ Icc x (x + M)).Nonempty := by
  intro K T hTile P hPnoncolumn _hUnique
  rintro ⟨R, hR, hNotWide⟩
  let W : ℝ := 8 * Metric.diam
    (closure (interior (closure (Complex.re '' K.openCarrier))))
  have hW : 0 < W := by
    have hpos := noncolumnPlate_thickness hTile P hPnoncolumn 0
    change 1 / 2 * (volume (interior
      (closure (Complex.re '' K.openCarrier)))).toReal <
        (volume (P.base ∩ Ioo 0 (0 + W))).toReal at hpos
    by_contra h
    have hWle : W ≤ 0 := le_of_not_gt h
    have hI : Ioo 0 (0 + W) = ∅ := Ioo_eq_empty (by linarith)
    rw [hI, inter_empty, measure_empty, ENNReal.toReal_zero] at hpos
    have hnonneg : 0 ≤ (volume
      (interior (closure (Complex.re '' K.openCarrier)))).toReal := ENNReal.toReal_nonneg
    linarith
  let M := max W (2 * R)
  refine ⟨M, lt_of_lt_of_le hW (le_max_left _ _), ?_⟩
  intro x
  have hthick := noncolumnPlate_thickness hTile P hPnoncolumn x
  change 1 / 2 * (volume (interior
    (closure (Complex.re '' K.openCarrier)))).toReal <
      (volume (P.base ∩ Ioo x (x + W))).toReal at hthick
  have hmeet : (P.base ∩ Ioo x (x + W)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, measure_empty, ENNReal.toReal_zero] at hthick
    have hnonneg : 0 ≤ (volume
        (interior (closure (Complex.re '' K.openCarrier)))).toReal := ENNReal.toReal_nonneg
    linarith
  obtain ⟨p, hpBase, hpI⟩ := hmeet
  obtain ⟨q, hqI, hqNot⟩ := Set.not_subset.mp (hNotWide x)
  let lo := min p q
  let hi := max p q
  have hpIcc : p ∈ Icc lo hi := ⟨min_le_left _ _, le_max_left _ _⟩
  have hqIcc : q ∈ Icc lo hi := ⟨min_le_right _ _, le_max_right _ _⟩
  have hnotSubset : ¬ Icc lo hi ⊆ P.base := fun h ↦ hqNot (h hqIcc)
  have hPopen : IsOpen P.base :=
    (Continuous.VerticalPlate.support_isVerticalSlab hTile P).1 ▸ isOpen_interior
  have hclosureNotSubset : ¬ closure P.base ∩ Icc lo hi ⊆ P.base := by
    intro h
    apply hnotSubset
    exact isPreconnected_Icc.subset_of_closure_inter_subset
      hPopen ⟨p, hpIcc, hpBase⟩ h
  obtain ⟨z, hz, hzNot⟩ := Set.not_subset.mp hclosureNotSubset
  have hzFront : z ∈ frontier P.base := by
    refine ⟨hz.1, ?_⟩
    simpa [hPopen.interior_eq] using hzNot
  refine ⟨z, ?_, ?_⟩
  · rw [componentBoundarySet_eq, Set.mem_iUnion]
    exact ⟨P, hzFront⟩
  · constructor
    · exact le_trans (le_min hpI.1.le hqI.1.le) hz.2.1
    · apply hz.2.2.trans
      apply max_le
      · apply hpI.2.le.trans
        have h := add_le_add_left (le_max_left W (2 * R)) x
        dsimp [M]
        linarith
      · apply hqI.2.le.trans
        have h := add_le_add_left (le_max_right W (2 * R)) x
        dsimp [M]
        linarith

private theorem columnBaseAperiodic_implies_uniqueWideNoncolumn :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ → NontrivialDecomposition K T →
      (regularSupport K (Continuous.verticalColumnCentres K T)).Nonempty →
      (∀ beta : ℝ, beta ≠ 0 →
        ¬ Tiling.RationalPolygonal.SetPeriodicBy
          (regularSupport K (Continuous.verticalColumnCentres K T))
          ((beta : ℝ) : ℂ)) →
      ∃ P : Continuous.VerticalPlate K T,
        ¬ Continuous.IsVerticalColumn P ∧
        (∀ Q : Continuous.VerticalPlate K T,
          ¬ Continuous.IsVerticalColumn Q → Q = P) ∧
        ∀ R : ℝ, 0 < R → ∃ a : ℝ,
          Ioo a (a + 2 * R) ⊆ P.base := by
  intro K T hTile hNontrivial _hSupportNe hAperiodic
  have period_contra (hFHC : Continuous.HasFiniteHorizontalComplexity T) : False := by
    obtain ⟨beta, hbeta, hperiod⟩ :=
      Continuous.continuousVerticalPlateSupport_periodic hTile hFHC
    exact hAperiodic beta hbeta.ne' hperiod.1
  have hExists : ∃ P : Continuous.VerticalPlate K T,
      ¬ Continuous.IsVerticalColumn P := by
    by_contra h
    push Not at h
    have hcentres : Continuous.verticalColumnCentres K T = T := by
      rw [Continuous.verticalColumnCentres_eq]
      apply Set.Subset.antisymm
      · rintro t ht
        obtain ⟨P, htP⟩ := Set.mem_iUnion.mp ht
        rcases htP with ⟨q, hq, rfl⟩
        exact q.2
      · intro t ht
        rw [Set.mem_iUnion]
        let P := Continuous.VerticalPlate.ofCentre (K := K) ⟨t, ht⟩
        exact ⟨⟨P, h P⟩,
          Continuous.VerticalPlate.mem_centres_ofCentre ⟨t, ht⟩⟩
    have hwhole : regularSupport K (Continuous.verticalColumnCentres K T) = univ := by
      rw [hcentres]
      exact regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile
    apply hAperiodic 1 one_ne_zero
    rw [hwhole]
    intro z
    simp
  obtain ⟨P, hPnoncolumn⟩ := hExists
  have hUnique : ∀ Q : Continuous.VerticalPlate K T,
      ¬ Continuous.IsVerticalColumn Q → Q = P := by
    intro Q hQ
    by_contra hQP
    have hdense := twoNoncolumnPlates_boundariesRelativelyDense
      hTile ⟨P, Q, Ne.symm hQP, hPnoncolumn, hQ⟩
    exact period_contra
      (finiteHorizontalComplexity_of_relativelyDenseBoundaries hTile hNontrivial hdense)
  refine ⟨P, hPnoncolumn, hUnique, ?_⟩
  intro R hR
  by_contra hwide
  push Not at hwide
  have hdense := uniqueNoncolumn_notWide_boundariesRelativelyDense
    hTile P hPnoncolumn hUnique ⟨R, hR, hwide⟩
  exact period_contra
    (finiteHorizontalComplexity_of_relativelyDenseBoundaries hTile hNontrivial hdense)


private structure NormalizedWidePlateData
    (K : Region) (T : Set Tiling.Plane)
    (P : Continuous.VerticalPlate K T) where
  vertexAnchor : ↥K.vertices
  centerAnchor : ↥T
  context : ApproximationContext.{0}
  region_openCarrier : context.region.openCarrier =
    (-vertexAnchor.1) +ᵥ K.openCarrier
  centres : context.centres = (-centerAnchor.1) +ᵥ T
  target : context.target = univ
  normalized_tiles : TilesOn context.region context.centres univ
  centreEquiv : ↥T ≃ ↥context.centres
  centre_formula : ∀ t : ↥T,
    (centreEquiv t : Tiling.Plane) = -centerAnchor.1 + t.1
  properContact_iff : ∀ s t : ↥T,
    Continuous.HorizontalProperContact K s.1 t.1 ↔
      Continuous.HorizontalProperContact context.region
        (centreEquiv s).1 (centreEquiv t).1
  normalizedPlate : Continuous.VerticalPlate context.region context.centres
  normalized_centres : normalizedPlate.centres =
    (-centerAnchor.1) +ᵥ P.centres
  normalized_base : normalizedPlate.base =
    {x : ℝ | ∃ y ∈ P.base,
      x = y - (vertexAnchor.1 + centerAnchor.1).re}
  normalized_noncolumn : ¬ Continuous.IsVerticalColumn normalizedPlate
  normalized_unique : ∀ Q : Continuous.VerticalPlate context.region context.centres,
    ¬ Continuous.IsVerticalColumn Q → Q = normalizedPlate
  normalized_wide : ∀ R : ℝ, 0 < R →
    ∃ a : ℝ, Ioo a (a + 2 * R) ⊆ normalizedPlate.base
  normalized_nontrivial : NontrivialDecomposition context.region context.centres
  normalized_contact_finite :
    ∀ a b a' b' : ↥context.region.vertices,
      (horizontalContactDisplacements context.region context.centres a b a' b').Finite

private theorem openSegment_commonTranslation
    (c x y : Tiling.Plane) :
    openSegment ℝ (c + x) (c + y) = c +ᵥ openSegment ℝ x y := by
  simpa only [vadd_eq_add] using (vadd_openSegment ℝ c x y).symm

private theorem horizontalOverlapWitness_commonTranslation_iff
    (c a b a' b' t s : Tiling.Plane) :
    (∃ u v : Tiling.Plane,
      u ≠ v ∧ u.im = v.im ∧
      openSegment ℝ u v ⊆
        openSegment ℝ (c + (a + t)) (c + (b + t)) ∩
          openSegment ℝ (c + (a' + s)) (c + (b' + s))) ↔
    (∃ u v : Tiling.Plane,
      u ≠ v ∧ u.im = v.im ∧
      openSegment ℝ u v ⊆
        openSegment ℝ (a + t) (b + t) ∩
          openSegment ℝ (a' + s) (b' + s)) := by
  constructor
  · rintro ⟨u, v, huv, him, hsub⟩
    refine ⟨-c + u, -c + v, ?_, ?_, ?_⟩
    · intro h
      apply huv
      have h' := congrArg (fun z ↦ c + z) h
      simpa only [add_neg_cancel_left] using h'
    · simp only [Complex.add_im, Complex.neg_im]
      linarith
    · intro z hz
      rw [openSegment_commonTranslation] at hz
      rcases hz with ⟨w, hw, rfl⟩
      have hzShift : c + (-c + w) ∈ openSegment ℝ u v := by
        simpa only [add_neg_cancel_left] using hw
      have hboth := hsub hzShift
      rw [openSegment_commonTranslation, openSegment_commonTranslation] at hboth
      constructor
      · have hleft := hboth.1
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hleft
        simpa [vadd_eq_add] using hleft
      · have hright := hboth.2
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hright
        simpa [vadd_eq_add] using hright
  · rintro ⟨u, v, huv, him, hsub⟩
    refine ⟨c + u, c + v, fun h ↦ huv (add_left_cancel h), ?_, ?_⟩
    · simp only [Complex.add_im]
      linarith
    · intro z hz
      rw [openSegment_commonTranslation] at hz
      rcases hz with ⟨w, hw, rfl⟩
      have hboth := hsub hw
      constructor
      · rw [openSegment_commonTranslation]
        exact ⟨w, hboth.1, rfl⟩
      · rw [openSegment_commonTranslation]
        exact ⟨w, hboth.2, rfl⟩

private theorem horizontalEdgeCondition_commonTranslation_iff
    (r a b : Tiling.Plane) (S V : Set Tiling.Plane) :
    (a ≠ b ∧ a.im = b.im ∧
      openSegment ℝ a b ⊆ frontier S \ V) ↔
    (r + a ≠ r + b ∧ (r + a).im = (r + b).im ∧
      openSegment ℝ (r + a) (r + b) ⊆
        frontier (r +ᵥ S) \ (r +ᵥ V)) := by
  constructor
  · rintro ⟨hab, him, hedge⟩
    refine ⟨fun h ↦ hab (add_left_cancel h), ?_, ?_⟩
    · simp only [Complex.add_im]
      linarith
    · intro z hz
      rw [openSegment_commonTranslation] at hz
      rcases hz with ⟨w, hw, rfl⟩
      rcases hedge hw with ⟨hwFrontier, hwNotVertex⟩
      refine ⟨?_, ?_⟩
      · rw [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa only [vadd_eq_add, neg_add_cancel_left] using hwFrontier
      · intro hwVertex
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hwVertex
        exact hwNotVertex (by simpa [vadd_eq_add] using hwVertex)
  · rintro ⟨hab, him, hedge⟩
    refine ⟨fun h ↦ hab (by simpa using congrArg (fun z : Tiling.Plane ↦ r + z) h), ?_, ?_⟩
    · simp only [Complex.add_im] at him ⊢
      linarith
    · intro w hw
      have hz : r + w ∈ openSegment ℝ (r + a) (r + b) := by
        rw [openSegment_commonTranslation]
        exact ⟨w, hw, rfl⟩
      rcases hedge hz with ⟨hwFrontier, hwNotVertex⟩
      rw [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem] at hwFrontier
      refine ⟨by simpa only [vadd_eq_add, neg_add_cancel_left] using hwFrontier, ?_⟩
      intro hwVertex
      have htranslated : r + w ∈ r +ᵥ V := by
        refine ⟨w, hwVertex, ?_⟩
        simp [vadd_eq_add]
      exact hwNotVertex htranslated

private theorem unitTranslation_horizontalContactDisplacements_eq
    {K R : Region} {T : Set Tiling.Plane} (r c : Tiling.Plane)
    (hcarrier : R.openCarrier = positiveSimilarity 1 r '' K.openCarrier)
    (a b a' b' : ↥K.vertices) :
    let eV : ↥K.vertices ≃ ↥R.vertices :=
      Equiv.Set.image (positiveSimilarity 1 r) K.vertices
        (positiveSimilarity_injective one_pos) |>.trans
          (Equiv.setCongr (positiveSimilarity_vertices_image one_pos hcarrier).symm)
    horizontalContactDisplacements R (positiveSimilarity 1 c '' T)
        (eV a) (eV b) (eV a') (eV b') =
      horizontalContactDisplacements K T a b a' b' := by
  let eV : ↥K.vertices ≃ ↥R.vertices :=
    Equiv.Set.image (positiveSimilarity 1 r) K.vertices
      (positiveSimilarity_injective one_pos) |>.trans
        (Equiv.setCongr (positiveSimilarity_vertices_image one_pos hcarrier).symm)
  have heV (x : ↥K.vertices) : (eV x).1 = x.1 + r := by
    change positiveSimilarity 1 r x.1 = x.1 + r
    simp only [positiveSimilarity, one_smul]
  have hSupport : R.support = r +ᵥ K.support := by
    rw [positiveSimilarity_support_image one_pos hcarrier,
      positiveSimilarity_image_eq_vadd_smul, one_smul]
  have hVertices : R.vertices = r +ᵥ K.vertices := by
    rw [positiveSimilarity_vertices_image one_pos hcarrier,
      positiveSimilarity_image_eq_vadd_smul, one_smul]
  have hEdge (x y : ↥K.vertices) :
      (x.1 ≠ y.1 ∧ x.1.im = y.1.im ∧
        openSegment ℝ x.1 y.1 ⊆ frontier K.support \ K.vertices) ↔
      ((eV x).1 ≠ (eV y).1 ∧ (eV x).1.im = (eV y).1.im ∧
        openSegment ℝ (eV x).1 (eV y).1 ⊆ frontier R.support \ R.vertices) := by
    simpa only [heV, hSupport, hVertices, add_comm] using
      horizontalEdgeCondition_commonTranslation_iff r x.1 y.1 K.support K.vertices
  have hEndpoint (x t : Tiling.Plane) :
      (x + r) + positiveSimilarity 1 c t = (r + c) + (x + t) := by
    simp only [positiveSimilarity, one_smul]
    abel
  change horizontalContactDisplacements R (positiveSimilarity 1 c '' T)
    (eV a) (eV b) (eV a') (eV b') = _
  ext delta
  rw [horizontalContactDisplacements_iff, horizontalContactDisplacements_iff]
  constructor
  · rintro ⟨hab, himab, hsegab, hab', himab', hsegab', t, s,
      hdelta, u, v, huv, him, hsub⟩
    obtain ⟨t₀, ht₀, htEq⟩ := t.2
    obtain ⟨s₀, hs₀, hsEq⟩ := s.2
    have hDelta : delta = (s₀ - t₀).re := by
      rw [← htEq, ← hsEq] at hdelta
      simpa only [positiveSimilarity, one_smul, add_sub_add_right_eq_sub] using hdelta
    have hOverlap : ∃ u v : Tiling.Plane, u ≠ v ∧ u.im = v.im ∧
        openSegment ℝ u v ⊆ openSegment ℝ (a.1 + t₀) (b.1 + t₀) ∩
          openSegment ℝ (a'.1 + s₀) (b'.1 + s₀) := by
      apply (horizontalOverlapWitness_commonTranslation_iff (r + c)
        a.1 b.1 a'.1 b'.1 t₀ s₀).mp
      refine ⟨u, v, huv, him, ?_⟩
      simpa only [heV, ← htEq, ← hsEq, hEndpoint] using hsub
    have hAB := (hEdge a b).mpr ⟨hab, himab, hsegab⟩
    have hAB' := (hEdge a' b').mpr ⟨hab', himab', hsegab'⟩
    exact ⟨hAB.1, hAB.2.1, hAB.2.2, hAB'.1, hAB'.2.1, hAB'.2.2,
      ⟨t₀, ht₀⟩, ⟨s₀, hs₀⟩, hDelta, hOverlap⟩
  · rintro ⟨hab, himab, hsegab, hab', himab', hsegab', t, s,
      hdelta, hOverlap⟩
    have hAB := (hEdge a b).mp ⟨hab, himab, hsegab⟩
    have hAB' := (hEdge a' b').mp ⟨hab', himab', hsegab'⟩
    refine ⟨hAB.1, hAB.2.1, hAB.2.2, hAB'.1, hAB'.2.1, hAB'.2.2,
      ⟨positiveSimilarity 1 c t.1, ⟨t.1, t.2, rfl⟩⟩,
      ⟨positiveSimilarity 1 c s.1, ⟨s.1, s.2, rfl⟩⟩, ?_, ?_⟩
    · simpa only [positiveSimilarity, one_smul, add_sub_add_right_eq_sub] using hdelta
    · simpa only [heV, hEndpoint] using
        (horizontalOverlapWitness_commonTranslation_iff (r + c)
          a.1 b.1 a'.1 b'.1 t.1 s.1).mpr hOverlap

private theorem normalizedWidePlateData_exists :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ → NontrivialDecomposition K T →
      ∀ (P : Continuous.VerticalPlate K T),
        ¬ Continuous.IsVerticalColumn P →
        (∀ Q : Continuous.VerticalPlate K T,
          ¬ Continuous.IsVerticalColumn Q → Q = P) →
        (∀ R : ℝ, 0 < R →
          ∃ a : ℝ, Ioo a (a + 2 * R) ⊆ P.base) →
        (∀ a b a' b' : ↥K.vertices,
          (horizontalContactDisplacements K T a b a' b').Finite) →
        Nonempty (NormalizedWidePlateData K T P) := by
  intro K T hTile hNontrivial P hNoncolumn hUnique hWide hFinite
  classical
  obtain ⟨v, hv, _⟩ := IntrinsicVertices.exists_intrinsicDiameterPair K
  obtain ⟨t, _ht⟩ := P.nonempty_supp
  obtain ⟨C : ApproximationContext.{0}, hRegion, hCentres, hTarget, hTiles⟩ :=
    normalizeApproximationContext K T univ v hv t.1 t.2
  have hTarget' : C.target = univ := by simpa using hTarget
  have hCarrier : C.region.openCarrier =
      positiveSimilarity 1 (-v) '' K.openCarrier := by
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
    exact hRegion
  have hImage : positiveSimilarity 1 (-t.1) '' T = C.centres := by
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
    exact hCentres.symm
  let eC : T ≃ C.centres :=
    (Continuous.positiveSimilarityCentreEquiv one_pos (-t.1)).trans
      (Equiv.setCongr hImage)
  let eP : Continuous.VerticalPlate K T ≃
      Continuous.VerticalPlate C.region C.centres :=
    (Continuous.verticalPlate_positiveSimilarityEquiv one_pos hCarrier (-t.1)).trans
      (Equiv.cast (congrArg (Continuous.VerticalPlate C.region) hImage))
  have hCast (S U : Set Tiling.Plane) (h : S = U)
      (Q : Continuous.VerticalPlate C.region S) :
      (Equiv.cast (congrArg (Continuous.VerticalPlate C.region) h) Q).centres = Q.centres ∧
      (Equiv.cast (congrArg (Continuous.VerticalPlate C.region) h) Q).base = Q.base ∧
      (Continuous.IsVerticalColumn Q ↔
        Continuous.IsVerticalColumn
          (Equiv.cast (congrArg (Continuous.VerticalPlate C.region) h) Q)) := by
    subst U
    exact ⟨rfl, rfl, Iff.rfl⟩
  have hCentresImage (Q : Continuous.VerticalPlate K T) :
      (eP Q).centres = positiveSimilarity 1 (-t.1) '' Q.centres := by
    exact (hCast _ _ hImage _).1.trans
      (Continuous.verticalPlate_positiveSimilarityEquiv_centres_image
        one_pos hCarrier (-t.1) Q)
  have hColumn (Q : Continuous.VerticalPlate K T) :
      Continuous.IsVerticalColumn Q ↔ Continuous.IsVerticalColumn (eP Q) := by
    exact (Continuous.verticalPlate_positiveSimilarityEquiv_isVerticalColumn
      one_pos hCarrier (-t.1) Q).trans (hCast _ _ hImage _).2.2
  have hBase : (eP P).base =
      (fun x : ℝ ↦ x - (v + t.1).re) '' P.base := by
    change (Equiv.cast (congrArg (Continuous.VerticalPlate C.region) hImage)
      (Continuous.verticalPlate_positiveSimilarityEquiv one_pos hCarrier (-t.1) P)).base = _
    rw [(hCast _ _ hImage _).2.1]
    convert Continuous.verticalPlate_positiveSimilarityEquiv_base_affine_real_image
      one_pos hCarrier (-t.1) P using 1
    congr 1
    funext x
    simp only [one_mul, Complex.add_re, Complex.neg_re]
    ring
  refine ⟨{
    vertexAnchor := ⟨v, hv⟩
    centerAnchor := t
    context := C
    region_openCarrier := hRegion
    centres := hCentres
    target := hTarget'
    normalized_tiles := by simpa only [hTarget'] using hTiles.mp hTile
    centreEquiv := eC
    centre_formula := ?_
    properContact_iff := ?_
    normalizedPlate := eP P
    normalized_centres := ?_
    normalized_base := ?_
    normalized_noncolumn := fun h ↦ hNoncolumn ((hColumn P).mpr h)
    normalized_unique := ?_
    normalized_wide := ?_
    normalized_nontrivial := ?_
    normalized_contact_finite := ?_ }⟩
  · intro u
    change positiveSimilarity 1 (-t.1) u.1 = -t.1 + u.1
    simp only [positiveSimilarity, one_smul, add_comm]
  · intro s u
    exact Continuous.horizontalProperContact_positiveSimilarity_iff
      one_pos hCarrier s.1 u.1
  · rw [hCentresImage, positiveSimilarity_image_eq_vadd_smul, one_smul]
  · rw [hBase]
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, hxy.symm⟩
  · intro Q hQ
    have hPre : ¬ Continuous.IsVerticalColumn (eP.symm Q) := by
      intro h
      exact hQ (eP.apply_symm_apply Q ▸ (hColumn (eP.symm Q)).mp h)
    rw [← eP.apply_symm_apply Q, hUnique (eP.symm Q) hPre]
  · intro R hR
    obtain ⟨a, ha⟩ := hWide R hR
    refine ⟨a - (v + t.1).re, ?_⟩
    intro x hx
    rw [hBase]
    refine ⟨x + (v + t.1).re, ha ?_, by ring⟩
    rcases hx with ⟨hx₁, hx₂⟩
    constructor <;> linarith
  · rintro ⟨Q, hQ, hQT⟩
    apply hNontrivial
    refine ⟨eP.symm Q, ?_, ?_⟩
    · intro h
      exact hQ (eP.apply_symm_apply Q ▸ (hColumn (eP.symm Q)).mp h)
    · apply (Set.image_eq_image (positiveSimilarity_injective one_pos)).mp
      rw [← hCentresImage, eP.apply_symm_apply, hQT, hImage]
  · rw [← hImage]
    intro a b a' b'
    let eV : ↥K.vertices ≃ ↥C.region.vertices :=
      Equiv.Set.image (positiveSimilarity 1 (-v)) K.vertices
        (positiveSimilarity_injective one_pos) |>.trans
          (Equiv.setCongr (positiveSimilarity_vertices_image one_pos hCarrier).symm)
    have hEq := unitTranslation_horizontalContactDisplacements_eq (T := T) (-v) (-t.1)
      hCarrier (eV.symm a) (eV.symm b) (eV.symm a') (eV.symm b')
    change horizontalContactDisplacements C.region (positiveSimilarity 1 (-t.1) '' T)
      (eV (eV.symm a)) (eV (eV.symm b)) (eV (eV.symm a')) (eV (eV.symm b')) = _ at hEq
    simp only [Equiv.apply_symm_apply] at hEq
    rw [hEq]
    exact hFinite (eV.symm a) (eV.symm b) (eV.symm a') (eV.symm b')




private theorem properPeriodicRegularOpen_components_bounded :
    ∀ {X : Set ℝ} {p : ℝ}, IsOpen X → interior (closure X) = X →
      X.Nonempty → X ≠ univ → 0 < p →
      Tiling.RationalPolygonal.SetPeriodicBy (Complex.re ⁻¹' X) ((p : ℝ) : ℂ) →
      (∀ c : ℝ, ¬ Ioi c ⊆ X) ∧
      (∀ c : ℝ, ¬ Iio c ⊆ X) ∧
      ∃ L : ℝ, 0 < L ∧ ∀ a b : ℝ,
        a < b → Ioo a b ⊆ X → Ioo a b ∩ frontier X = ∅ → b - a ≤ L := by
  intro X p hOpen hRegular hne hproper hp hperiod
  obtain ⟨M, hM, hdense⟩ := properPeriodicRegularOpen_frontierRelativelyDense
    hOpen hRegular hne hproper hp.ne' hperiod
  have hfront_not_mem {y : ℝ} (hy : y ∈ frontier X) : y ∉ X := by
    rw [frontier] at hy
    intro hyX
    apply hy.2
    rwa [hOpen.interior_eq]
  have hright : ∀ c : ℝ, ¬ Ioi c ⊆ X := by
    intro c hc
    obtain ⟨y, hyF, hyI⟩ := hdense (c + 1)
    apply hfront_not_mem hyF
    apply hc
    change c < y
    linarith [hyI.1]
  have hleft : ∀ c : ℝ, ¬ Iio c ⊆ X := by
    intro c hc
    obtain ⟨y, hyF, hyI⟩ := hdense (c - M - 1)
    apply hfront_not_mem hyF
    apply hc
    change y < c
    linarith [hyI.2, hM]
  refine ⟨hright, hleft, 2 * M, by positivity, ?_⟩
  intro a b hab hsub hgap
  by_contra hnot
  have hlong : 2 * M < b - a := lt_of_not_ge hnot
  let x := (a + b - M) / 2
  obtain ⟨y, hyF, hyI⟩ := hdense x
  have hyab : y ∈ Ioo a b := by
    dsimp [x] at hyI
    constructor <;> linarith [hyI.1, hyI.2, hM]
  have : y ∈ Ioo a b ∩ frontier X := ⟨hyab, hyF⟩
  rw [hgap] at this
  exact this


private theorem transportedUniqueNoncolumnPlate_proper
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (R : TwoStageDeformationSupportTransport C phi D)
    (plateEquiv : Continuous.VerticalPlate C.region C.centres ≃
      Continuous.VerticalPlate D.deformedRegion (deformedCenterCarrier R.fullCenters))
    (centre_mem : ∀ (Q : Continuous.VerticalPlate C.region C.centres)
      (t : ↥C.centres),
      (t.1 : Tiling.Plane) ∈ Q.centres ↔
        R.fullCenters t ∈ (plateEquiv Q).centres)
    (column_iff : ∀ Q : Continuous.VerticalPlate C.region C.centres,
      Continuous.IsVerticalColumn Q ↔
        Continuous.IsVerticalColumn (plateEquiv Q))
    (Q : Continuous.VerticalPlate C.region C.centres)
    (hNontrivial : NontrivialDecomposition C.region C.centres)
    (hQnoncolumn : ¬ Continuous.IsVerticalColumn Q)
    (_hUnique : ∀ Q' : Continuous.VerticalPlate C.region C.centres,
      ¬ Continuous.IsVerticalColumn Q' → Q' = Q) :
    ¬ Continuous.IsVerticalColumn (plateEquiv Q) ∧
      (plateEquiv Q).base ≠ univ := by
  constructor
  · intro hColumn
    exact hQnoncolumn ((column_iff Q).mpr hColumn)
  · intro hBase
    apply hNontrivial
    refine ⟨Q, hQnoncolumn, ?_⟩
    have hSupport : (plateEquiv Q).support = Set.univ := by
      have hSlab := (plateEquiv Q).support_isVerticalSlab R.full_tilesOn
      rw [hSlab.2, hBase]
      simp
    have hTargetCentres : (plateEquiv Q).centres = deformedCenterCarrier R.fullCenters :=
      Continuous.plate_centres_eq_of_support_eq_univ R.full_tilesOn (plateEquiv Q) hSupport
    ext t
    constructor
    · intro ht
      rcases ht with ⟨s, hs, rfl⟩
      exact s.2
    · intro ht
      have hTarget : R.fullCenters ⟨t, ht⟩ ∈ (plateEquiv Q).centres := by
        rw [hTargetCentres]
        exact ⟨⟨t, ht⟩, rfl⟩
      exact (centre_mem Q ⟨t, ht⟩).mpr hTarget


private theorem rationalTransportedPlate_periodicComponentBound :
    ∀ (C : Tiling.AxisParallel.Approximation.ApproximationContext.{0})
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
      (R : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport
        C phi D)
      (Q : Tiling.AxisParallel.Continuous.VerticalPlate D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier R.fullCenters)),
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn Q → Q.base ≠ univ →
      ∃ p L : ℝ, 0 < p ∧ 0 < L ∧
        Tiling.RationalPolygonal.SetPeriodicBy Q.support ((p : ℝ) : ℂ) ∧
        (∀ c : ℝ, ¬ Ioi c ⊆ Q.base) ∧
        (∀ c : ℝ, ¬ Iio c ⊆ Q.base) ∧
        ∀ a b : ℝ, a < b → Ioo a b ⊆ Q.base →
          Ioo a b ∩ frontier Q.base = ∅ → b - a ≤ L := by
  intro C phi D R Q hQnoncolumn hQproper
  have hRational : Tiling.RationalPolygonal.IsRelativelyRational
      D.deformedRegion.toPolygonalRegion := by
    obtain ⟨v, hv, _w, _hw, _hmax, _hdiam⟩ :=
      IntrinsicVertices.exists_intrinsicDiameterPair D.deformedRegion
    refine ⟨v, hv, ?_⟩
    intro w hw
    obtain ⟨wx, wy, hwre, hwim⟩ := D.rational_vertices w hw
    obtain ⟨vx, vy, hvre, hvim⟩ := D.rational_vertices v hv
    exact ⟨wx - vx, wy - vy,
      by simp only [Complex.sub_re, hwre, hvre, Rat.cast_sub],
      by simp only [Complex.sub_im, hwim, hvim, Rat.cast_sub]⟩
  obtain ⟨p, hp, _hcolumnPeriod, hnoncolumnPeriod⟩ :=
    Tiling.AxisParallel.Continuous.rationalVerticalPlateSupport_periodic
      R.full_tilesOn hRational
  have hperiod := hnoncolumnPeriod Q hQnoncolumn
  have hslab := Q.support_isVerticalSlab R.full_tilesOn
  have hbaseOpen : IsOpen Q.base := by
    rw [hslab.1]
    exact isOpen_interior
  have hbaseRegular : interior (closure Q.base) = Q.base := hslab.1.symm
  have hbaseNonempty : Q.base.Nonempty := by
    obtain ⟨t, ht⟩ := Q.nonempty_supp
    obtain ⟨u, hu⟩ := D.deformedRegion.isPolygonal.interior_nonempty
      D.deformedRegion.nonempty
    refine ⟨(t.1 + u).re, t.1 + u, ?_, rfl⟩
    rw [Q.support_eq_regularSupport]
    change t.1 + u ∈
      Tiling.AxisParallel.regularSupport D.deformedRegion Q.centres
    have hopen : IsOpen (Tiling.AxisParallel.openUnion D.deformedRegion Q.centres) := by
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
      exact isOpen_iUnion fun s => isOpen_interior.vadd s.1
    apply hopen.subset_interior_closure
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion,
      ← Region.openCarrier, Set.mem_iUnion]
    refine ⟨⟨t.1, ⟨t, ht, rfl⟩⟩, ?_⟩
    exact ⟨u, hu, rfl⟩
  have hpreimagePeriod :
      Tiling.RationalPolygonal.SetPeriodicBy (Complex.re ⁻¹' Q.base)
        ((p : ℝ) : ℂ) := by
    rw [← hslab.2]
    exact hperiod
  obtain ⟨hright, hleft, L, hL, hbound⟩ :=
    properPeriodicRegularOpen_components_bounded
      hbaseOpen hbaseRegular hbaseNonempty hQproper hp hpreimagePeriod
  exact ⟨p, L, hp, hL, hperiod, hright, hleft, hbound⟩


private theorem iio_subset_plateBase_of_no_boundary_below
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T univ)
    (P : Continuous.VerticalPlate K T) (x : ℝ) (hx : x ∈ P.base)
    (hno : ¬ ∃ c ∈ componentBoundarySet K T, c ≤ x) : Iio x ⊆ P.base := by
  have hfront : frontier P.base ⊆ componentBoundarySet K T := by
    intro c hc
    rw [componentBoundarySet_eq, Set.mem_iUnion]
    exact ⟨P, hc⟩
  have hdisj : Disjoint (Iio x) (frontier P.base) := by
    rw [Set.disjoint_left]
    intro c hcx hc
    exact hno ⟨c, hfront hc, hcx.le⟩
  rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Iio hdisj with hin | hout
  · intro y hy
    exact interior_subset (hin hy)
  · exfalso
    have hopen : IsOpen P.base := by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).1]
      exact isOpen_interior
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hx
    let y := x - ε / 2
    have hyIio : y ∈ Iio x := by change x - ε / 2 < x; linarith
    have hyBase : y ∈ P.base := hball (by
      rw [Real.ball_eq_Ioo]
      dsimp [y]
      constructor <;> linarith)
    exact (interior_subset (hout hyIio)) hyBase

private theorem ioi_subset_plateBase_of_no_boundary_above
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T univ)
    (P : Continuous.VerticalPlate K T) (x : ℝ) (hx : x ∈ P.base)
    (hno : ¬ ∃ c ∈ componentBoundarySet K T, x ≤ c) : Ioi x ⊆ P.base := by
  have hfront : frontier P.base ⊆ componentBoundarySet K T := by
    intro c hc
    rw [componentBoundarySet_eq, Set.mem_iUnion]
    exact ⟨P, hc⟩
  have hdisj : Disjoint (Ioi x) (frontier P.base) := by
    rw [Set.disjoint_left]
    intro c hxc hc
    exact hno ⟨c, hfront hc, hxc.le⟩
  rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Ioi hdisj with hin | hout
  · intro y hy
    exact interior_subset (hin hy)
  · exfalso
    have hopen : IsOpen P.base := by
      rw [(Continuous.VerticalPlate.support_isVerticalSlab hTile P).1]
      exact isOpen_interior
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hx
    let y := x + ε / 2
    have hyIoi : y ∈ Ioi x := by change x < x + ε / 2; linarith
    have hyBase : y ∈ P.base := hball (by
      rw [Real.ball_eq_Ioo]
      dsimp [y]
      constructor <;> linarith)
    exact (interior_subset (hout hyIoi)) hyBase

private theorem widePlate_hasLongBoundedComponent :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ →
      ∀ (P : Continuous.VerticalPlate K T),
      (∀ R : ℝ, 0 < R → ∃ a : ℝ, Ioo a (a + 2 * R) ⊆ P.base) →
      (∀ c : ℝ, ¬ (Ioi c ⊆ P.base ∧
        Ioi c ∩ componentBoundarySet K T = ∅)) →
      (∀ c : ℝ, ¬ (Iio c ⊆ P.base ∧
        Iio c ∩ componentBoundarySet K T = ∅)) →
      ∀ L : ℝ, 0 < L →
        ∃ c d : ↥(componentBoundarySet K T),
          c.1 < d.1 ∧ L < d.1 - c.1 ∧
          Ioo c.1 d.1 ⊆ P.base ∧
          Ioo c.1 d.1 ∩ componentBoundarySet K T = ∅ := by
  intro K T hTile P hwide hnoright hnoleft L hL
  let R : ℝ := max (L + 1) 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨a, haBase⟩ := hwide R hR
  let x : ℝ := a + R
  have hxWide : x ∈ Ioo a (a + 2 * R) := by
    dsimp [x]
    constructor <;> linarith
  have hxBase : x ∈ P.base := haBase hxWide
  have hbelow : ∃ c ∈ componentBoundarySet K T, c ≤ x := by
    by_contra hno
    have hfill := iio_subset_plateBase_of_no_boundary_below hTile P x hxBase hno
    apply hnoleft x
    refine ⟨hfill, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro c ⟨hcx, hcE⟩
    exact hno ⟨c, hcE, hcx.le⟩
  have habove : ∃ d ∈ componentBoundarySet K T, x ≤ d := by
    by_contra hno
    have hfill := ioi_subset_plateBase_of_no_boundary_above hTile P x hxBase hno
    apply hnoright x
    refine ⟨hfill, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro d ⟨hxd, hdE⟩
    exact hno ⟨d, hdE, hxd.le⟩
  have hlocal := componentBoundarySet_locallyFinite hTile
  obtain ⟨c, hcE, hcx, hcmax⟩ :=
    Approximation.exists_greatest_mem_le_of_boundedWindowFinite hlocal hbelow
  obtain ⟨d, hdE, hxd, hdmin⟩ :=
    Approximation.exists_least_mem_ge_of_boundedWindowFinite hlocal habove
  have hca : c ≤ a := by
    by_contra h
    have hca' : a < c := lt_of_not_ge h
    exact componentBoundary_not_mem_plateBase hTile hcE P
      (haBase ⟨hca', lt_of_le_of_lt hcx hxWide.2⟩)
  have had : a + 2 * R ≤ d := by
    by_contra h
    have had' : d < a + 2 * R := lt_of_not_ge h
    exact componentBoundary_not_mem_plateBase hTile hdE P
      (haBase ⟨lt_of_lt_of_le hxWide.1 hxd, had'⟩)
  have hcx' : c < x := lt_of_le_of_ne hcx (by
    intro h
    apply componentBoundary_not_mem_plateBase hTile hcE P
    rwa [h])
  have hxd' : x < d := lt_of_le_of_ne hxd (by
    intro h
    apply componentBoundary_not_mem_plateBase hTile hdE P
    rwa [← h])
  have hcd : c < d := hcx'.trans hxd'
  have hgap : Ioo c d ∩ componentBoundarySet K T = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hzE⟩
    rcases le_total z x with hzx | hxz
    · exact (not_le_of_gt hz.1) (hcmax z hzE hzx)
    · exact (not_le_of_gt hz.2) (hdmin z hzE hxz)
  have hfront : frontier P.base ⊆ componentBoundarySet K T := by
    intro z hz
    rw [componentBoundarySet_eq, Set.mem_iUnion]
    exact ⟨P, hz⟩
  have hdisj : Disjoint (Ioo c d) (frontier P.base) := by
    rw [Set.disjoint_left]
    intro z hz hzfront
    have : z ∈ Ioo c d ∩ componentBoundarySet K T := ⟨hz, hfront hzfront⟩
    rw [hgap] at this
    exact this
  have hbase : Ioo c d ⊆ P.base := by
    rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
        isPreconnected_Ioo hdisj with hin | hout
    · exact hin.trans interior_subset
    · exfalso
      exact (interior_subset (hout ⟨hcx', hxd'⟩)) hxBase
  refine ⟨⟨c, hcE⟩, ⟨d, hdE⟩, hcd, ?_, hbase, hgap⟩
  have hRL : L < 2 * R := by
    dsimp [R]
    have : L + 1 ≤ max (L + 1) 1 := le_max_left _ _
    linarith
  linarith



private theorem mappedHorizontalStep_ge
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) {eta d : ℝ}
    (hEta : ∀ a b : ↥C.region.vertices, a.1.re < b.1.re →
      eta ≤ (D.planarHomeomorph b.1).re - (D.planarHomeomorph a.1).re)
    (hd : d ∈ C.region.horizontalStepAlphabet) :
    eta ≤ mapScalar phi ⟨d, horizontalStep_mem_coordinateSpace C hd⟩ := by
  obtain ⟨a, ha, b, hb, hEq, hpos⟩ :=
    (Region.mem_horizontalStepAlphabet_iff C.region d).mp hd
  have hab : a.re < b.re := by rw [hEq] at hpos; exact sub_pos.mp hpos
  have hscalar : (⟨d, horizontalStep_mem_coordinateSpace C hd⟩ : C.coordinateSpace) =
      ⟨b.re, C.vertex_re_mem b hb⟩ - ⟨a.re, C.vertex_re_mem a ha⟩ := by
    apply Subtype.ext
    exact hEq
  have hmapped : mapScalar phi ⟨d, horizontalStep_mem_coordinateSpace C hd⟩ =
      (D.planarHomeomorph b).re - (D.planarHomeomorph a).re := by
    rw [hscalar, D.vertex_agreement b hb, D.vertex_agreement a ha]
    simp only [mapScalar, map_sub, Rat.cast_sub, mapPoint,
      ApproximationContext.vertexPoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
  rw [hmapped]
  exact hEta ⟨a, ha⟩ ⟨b, hb⟩ hab

private theorem mappedTranslatedVertex_eq
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (R : TwoStageDeformationSupportTransport C phi D)
    (v : ↥C.region.vertices) (t : ↥C.centres) :
    mapScalar phi ⟨(v.1 + t.1).re, by
      rw [Complex.add_re]
      exact C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2)
        (C.centre_re_mem t.1 t.2)⟩ =
      (D.planarHomeomorph v.1 + R.fullCenters t).re := by
  have hscalar : (⟨(v.1 + t.1).re, by
      rw [Complex.add_re]
      exact C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2)
        (C.centre_re_mem t.1 t.2)⟩ : C.coordinateSpace) =
      ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ +
        ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
    apply Subtype.ext
    exact Complex.add_re _ _
  rw [hscalar, D.vertex_agreement v.1 v.2, R.fullCenters_apply t]
  simp only [mapScalar, map_add, Rat.cast_add, mapPoint,
    ApproximationContext.vertexPoint, ApproximationContext.centrePoint,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

private theorem rightRay_extends_to_boundary
    {E B : Set ℝ} (hE : E.Nonempty)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (hfront : frontier B ⊆ E) (havoid : ∀ z ∈ E, z ∉ B)
    {c : ℝ} (hc : Ioi c ⊆ B) :
    ∃ a : ↥E, Ioi a.1 ⊆ B ∧ Ioi a.1 ∩ E = ∅ := by
  obtain ⟨z, hz⟩ := hE
  let x : ℝ := max c z + 1
  have hcx : c < x := by dsimp [x]; linarith [le_max_left c z]
  have hzx : z ≤ x := by dsimp [x]; linarith [le_max_right c z]
  obtain ⟨a, ha, hax, hamax⟩ :=
    Approximation.exists_greatest_mem_le_of_boundedWindowFinite hlocal ⟨z, hz, hzx⟩
  have hax' : a < x := lt_of_le_of_ne hax (by
    intro h
    exact havoid a ha (h.symm ▸ hc hcx))
  have hgap : Ioi a ∩ E = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hay, hy⟩
    by_cases hyx : y ≤ x
    · exact (not_le_of_gt hay) (hamax y hy hyx)
    · exact havoid y hy (hc (hcx.trans (lt_of_not_ge hyx)))
  have hdisj : Disjoint (Ioi a) (frontier B) := by
    rw [Set.disjoint_left]
    intro y hy hyF
    have hyGap : y ∈ Ioi a ∩ E := ⟨hy, hfront hyF⟩
    rw [hgap] at hyGap
    exact hyGap
  refine ⟨⟨a, ha⟩, ?_, hgap⟩
  rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Ioi hdisj with hin | hout
  · exact hin.trans interior_subset
  · exact False.elim ((interior_subset (hout hax')) (hc hcx))

private theorem leftRay_extends_to_boundary
    {E B : Set ℝ} (hE : E.Nonempty)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (hfront : frontier B ⊆ E) (havoid : ∀ z ∈ E, z ∉ B)
    {c : ℝ} (hc : Iio c ⊆ B) :
    ∃ a : ↥E, Iio a.1 ⊆ B ∧ Iio a.1 ∩ E = ∅ := by
  obtain ⟨z, hz⟩ := hE
  let x : ℝ := min c z - 1
  have hxc : x < c := by dsimp [x]; linarith [min_le_left c z]
  have hxz : x ≤ z := by dsimp [x]; linarith [min_le_right c z]
  obtain ⟨a, ha, hxa, hamin⟩ :=
    Approximation.exists_least_mem_ge_of_boundedWindowFinite hlocal ⟨z, hz, hxz⟩
  have hxa' : x < a := lt_of_le_of_ne hxa (by
    intro h
    exact havoid a ha (h ▸ hc hxc))
  have hgap : Iio a ∩ E = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hya, hy⟩
    by_cases hxy : x ≤ y
    · exact (not_le_of_gt hya) (hamin y hy hxy)
    · exact havoid y hy (hc ((lt_of_not_ge hxy).trans hxc))
  have hdisj : Disjoint (Iio a) (frontier B) := by
    rw [Set.disjoint_left]
    intro y hy hyF
    have hyGap : y ∈ Iio a ∩ E := ⟨hy, hfront hyF⟩
    rw [hgap] at hyGap
    exact hyGap
  refine ⟨⟨a, ha⟩, ?_, hgap⟩
  rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Iio hdisj with hin | hout
  · exact hin.trans interior_subset
  · exact False.elim ((interior_subset (hout hxa')) (hc hxc))

private theorem uniqueWideNoncolumn_implies_infiniteContactDisplacement :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ → NontrivialDecomposition K T →
      (∃ P : Continuous.VerticalPlate K T,
        ¬ Continuous.IsVerticalColumn P ∧
        (∀ Q : Continuous.VerticalPlate K T,
          ¬ Continuous.IsVerticalColumn Q → Q = P) ∧
        ∀ R : ℝ, 0 < R → ∃ a : ℝ,
          Ioo a (a + 2 * R) ⊆ P.base) →
      ∃ a b a' b' : ↥K.vertices,
        (horizontalContactDisplacements K T a b a' b').Infinite := by
  intro K T hTile hNontrivial hwide
  by_contra hfinite
  push Not at hfinite
  obtain ⟨P, hPnoncolumn, hUnique, hPwide⟩ := hwide
  obtain ⟨N⟩ := normalizedWidePlateData_exists
    hTile hNontrivial P hPnoncolumn hUnique hPwide hfinite
  let C := N.context
  obtain ⟨ef, hef, hFCT⟩ :=
    finiteContactWitnesses C N.normalized_tiles N.normalized_contact_finite
  obtain ⟨eg, heg, hgood⟩ := isGoodApproximation_of_sufficientlyFine C
  obtain ⟨phi, hphi⟩ := exists_epsilonApproximation C (min ef eg) (lt_min hef heg)
  have hphif : IsEpsilonApproximation C ef phi := by
    refine ⟨lt_of_lt_of_le hphi.epsilon_pos (min_le_left _ _), hphi.fixesRational, ?_⟩
    intro j
    exact lt_of_lt_of_le (hphi.basis_close j) (min_le_left _ _)
  have hphig : IsEpsilonApproximation C eg phi := by
    refine ⟨lt_of_lt_of_le hphi.epsilon_pos (min_le_right _ _), hphi.fixesRational, ?_⟩
    intro j
    exact lt_of_lt_of_le (hphi.basis_close j) (min_le_right _ _)
  obtain ⟨D⟩ := exists_rationalPolygonDeformation C phi (hgood phi hphig)
  obtain ⟨R⟩ := exists_twoStageDeformationSupportTransport C phi D N.normalized_tiles
  obtain ⟨_hcontact, plateEquiv, boundaryLift, boundaryEquiv,
    hlift, hboundary, hboundaryMono, hcentre, hcolumn,
    hchamber, hright, hleft, hside⟩ := hFCT phi hphif D R
  obtain ⟨hQnoncolumn, hQproper⟩ := transportedUniqueNoncolumnPlate_proper
    C phi D R plateEquiv hcentre hcolumn N.normalizedPlate
    N.normalized_nontrivial N.normalized_noncolumn N.normalized_unique
  obtain ⟨_p, L, _hp, hL, _hperiod, hnoright, hnoleft, hbound⟩ :=
    rationalTransportedPlate_periodicComponentBound C phi D R
      (plateEquiv N.normalizedPlate) hQnoncolumn hQproper
  have hSourceProper : N.normalizedPlate.base ≠ univ := by
    intro hbase
    apply N.normalized_nontrivial
    refine ⟨N.normalizedPlate, N.normalized_noncolumn, ?_⟩
    apply Continuous.plate_centres_eq_of_support_eq_univ N.normalized_tiles
    rw [(N.normalizedPlate.support_isVerticalSlab N.normalized_tiles).2, hbase]
    simp
  have hSourceBaseNe : N.normalizedPlate.base.Nonempty := by
    obtain ⟨a, ha⟩ := N.normalized_wide 1 zero_lt_one
    exact ⟨a + 1, ha (by constructor <;> linarith)⟩
  have hSourceFrontNe : (frontier N.normalizedPlate.base).Nonempty := by
    by_contra hno
    rcases frontier_eq_empty_iff.mp (Set.not_nonempty_iff_eq_empty.mp hno) with h | h
    · exact hSourceBaseNe.ne_empty h
    · exact hSourceProper h
  have hSourceFront : frontier N.normalizedPlate.base ⊆
      componentBoundarySet C.region C.centres := by
    intro c hc
    rw [componentBoundarySet_eq, Set.mem_iUnion]
    exact ⟨N.normalizedPlate, hc⟩
  have hSourceBoundaryNe := hSourceFrontNe.mono hSourceFront
  have hSourceAvoid : ∀ z ∈ componentBoundarySet C.region C.centres,
      z ∉ N.normalizedPlate.base := fun z hz ↦
    componentBoundary_not_mem_plateBase (c := z)
      N.normalized_tiles hz N.normalizedPlate
  have hSourceLocal := componentBoundarySet_locallyFinite N.normalized_tiles
  have hSourceRight : ∀ c : ℝ, ¬ (Ioi c ⊆ N.normalizedPlate.base ∧
      Ioi c ∩ componentBoundarySet C.region C.centres = ∅) := by
    intro c hc
    obtain ⟨a, ha⟩ := rightRay_extends_to_boundary hSourceBoundaryNe
      hSourceLocal hSourceFront hSourceAvoid hc.1
    exact hnoright _ ((hright N.normalizedPlate a).mp ha).1
  have hSourceLeft : ∀ c : ℝ, ¬ (Iio c ⊆ N.normalizedPlate.base ∧
      Iio c ∩ componentBoundarySet C.region C.centres = ∅) := by
    intro c hc
    obtain ⟨a, ha⟩ := leftRay_extends_to_boundary hSourceBoundaryNe
      hSourceLocal hSourceFront hSourceAvoid hc.1
    exact hnoleft _ ((hleft N.normalizedPlate a).mp ha).1
  obtain ⟨eta, hEta, hStepLower⟩ := mappedHorizontalStep_min C phi D
  let Dmax := C.region.horizontalStepAlphabet.max'
    (Region.horizontalStepAlphabet_nonempty C.region)
  have hDmax : 0 < Dmax := Region.horizontalStepAlphabet_pos C.region
    (Finset.max'_mem _ _)
  let cutoff := Dmax * (L / eta + 1)
  have hCutoff : 0 < cutoff := by dsimp [cutoff]; positivity
  obtain ⟨c, d, hcd, hlong, hbase, hgap⟩ := widePlate_hasLongBoundedComponent
    N.normalized_tiles N.normalizedPlate N.normalized_wide hSourceRight hSourceLeft
      cutoff hCutoff
  obtain ⟨t, v, w, ht, hvw, hvwre, hsideSegment, hdeep, hsideLe⟩ :=
    wideComponent_hasDeepTranslatedVerticalSide N.normalized_tiles
      N.normalizedPlate c d hcd hbase hgap cutoff hCutoff hlong
  let endpoint : C.coordinateSpace := ⟨(v.1 + t.1).re, by
    rw [Complex.add_re]
    exact C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2)
      (C.centre_re_mem t.1 t.2)⟩
  have hendpoint := mappedTranslatedVertex_eq C phi D R v t
  change mapScalar phi endpoint = _ at hendpoint
  have hsideGt : c.1 < (v.1 + t.1).re := by linarith
  obtain ⟨n, _hn, step, hstep, hstepSum⟩ := horizontalBoundaryDistance_eq_stepSum
    N.normalized_tiles (componentBoundaryLine_subset_translatedFrontiers
      N.normalized_tiles c.1 c.2) v t (ne_of_gt hsideGt)
  rw [abs_of_pos (sub_pos.mpr hsideGt)] at hstepSum
  let stepLift : Fin n → C.coordinateSpace :=
    fun i ↦ ⟨step i, horizontalStep_mem_coordinateSpace C (hstep i)⟩
  have hLiftSum : endpoint - boundaryLift c = ∑ i, stepLift i := by
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_sum, hlift c]
    exact hstepSum
  have hMappedSum : mapScalar phi endpoint - mapScalar phi (boundaryLift c) =
      ∑ i, mapScalar phi (stepLift i) := by
    have hPhi := congrArg phi hLiftSum
    simp only [map_sub, map_sum] at hPhi
    change ((phi endpoint : ℚ) : ℝ) - ((phi (boundaryLift c) : ℚ) : ℝ) =
      ∑ i, ((phi (stepLift i) : ℚ) : ℝ)
    exact_mod_cast hPhi
  have hMappedLong : L < ∑ i, mapScalar phi (stepLift i) := by
    apply longBoundaryWord_mappedLength step (fun i ↦ mapScalar phi (stepLift i))
      hDmax hEta hL.le
    · intro i
      exact ⟨Region.horizontalStepAlphabet_pos C.region (hstep i),
        Finset.le_max' _ _ (hstep i)⟩
    · intro i
      exact mappedHorizontalStep_ge C phi D hStepLower (hstep i)
    · rw [← hstepSum]
      exact (lt_sub_iff_add_lt').mpr hdeep
  have hsideTargetLe : (D.planarHomeomorph v.1 + R.fullCenters t).re ≤
      (boundaryEquiv d).1 := by
    rcases hsideLe.eq_or_lt with heq | hlt
    · have hLiftD : endpoint = boundaryLift d := by
        apply Subtype.ext
        exact heq.trans (hlift d).symm
      rw [← hendpoint, hLiftD, ← hboundary d]
    · exact (hside N.normalizedPlate t v w c d ht hvw hvwre hsideSegment
        hcd hgap hbase hsideGt hlt).2.le
  have htargetBase := (hchamber N.normalizedPlate c d hcd hgap).mp hbase
  have htargetGap : Ioo (boundaryEquiv c).1 (boundaryEquiv d).1 ∩
      frontier (plateEquiv N.normalizedPlate).base = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hxF⟩
    have hopen : IsOpen (plateEquiv N.normalizedPlate).base := by
      rw [((plateEquiv N.normalizedPlate).support_isVerticalSlab R.full_tilesOn).1]
      exact isOpen_interior
    exact hxF.2 (by rw [hopen.interior_eq]; exact htargetBase hx)
  have hTargetBound := hbound _ _ (hboundaryMono hcd) htargetBase htargetGap
  rw [← hMappedSum, hendpoint, ← hboundary c] at hMappedLong
  linarith



private theorem infiniteContactDisplacement_notFiniteComplexity :
    ∀ {K : Region} {T : Set Tiling.Plane},
      Continuous.HasFiniteHorizontalComplexity T →
      ∀ a b a' b' : ↥K.vertices,
        ¬ (horizontalContactDisplacements K T a b a' b').Infinite := by
  intro K T hFLC a b a' b'
  have hbounded := horizontalContactDisplacements_bounded K T a b a' b'
  rw [Metric.isBounded_iff_subset_closedBall 0] at hbounded
  obtain ⟨R, hsub⟩ := hbounded
  let R' := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hfinite :
      ((Continuous.horizontalCentreProjection T -
          Continuous.horizontalCentreProjection T) ∩
        Metric.closedBall 0 R').Finite := by
    exact hFLC.2 R' hR'
  have htarget : horizontalContactDisplacements K T a b a' b' ⊆
      (Continuous.horizontalCentreProjection T -
          Continuous.horizontalCentreProjection T) ∩
        Metric.closedBall 0 R' := by
    intro delta hdelta
    have hballR := hsub hdelta
    rw [horizontalContactDisplacements_iff] at hdelta
    obtain ⟨_, _, _, _, _, _, t, s, rfl, _⟩ := hdelta
    constructor
    · refine ⟨(s.1 : Tiling.Plane).re, ⟨s.1, s.2, rfl⟩,
        (t.1 : Tiling.Plane).re, ⟨t.1, t.2, rfl⟩, ?_⟩
      rfl
    · rw [Metric.mem_closedBall] at hballR ⊢
      exact hballR.trans (le_max_left R 1)
  exact (hfinite.subset htarget).not_infinite


/-- In a nontrivial whole-plane plate decomposition, failure of finite horizontal complexity is
equivalent to column-base aperiodicity, to a unique arbitrarily wide noncolumn plate, and to an
infinite labelled horizontal contact-displacement set. -/
theorem infiniteHorizontalComplexity_iff_columnBaseAperiodic :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ →
      (¬ ∃ P : Continuous.VerticalPlate K T,
        ¬ Continuous.IsVerticalColumn P ∧ P.centres = T) →
      ((¬ Continuous.HasFiniteHorizontalComplexity T) ↔
        ((regularSupport K (Continuous.verticalColumnCentres K T)).Nonempty ∧
          ∀ beta : ℝ, beta ≠ 0 →
            ¬ Tiling.RationalPolygonal.SetPeriodicBy
              (regularSupport K (Continuous.verticalColumnCentres K T))
              ((beta : ℝ) : ℂ))) ∧
      ((¬ Continuous.HasFiniteHorizontalComplexity T) ↔
        ∃ P : Continuous.VerticalPlate K T,
          ¬ Continuous.IsVerticalColumn P ∧
          (∀ Q : Continuous.VerticalPlate K T,
            ¬ Continuous.IsVerticalColumn Q → Q = P) ∧
          ∀ R : ℝ, 0 < R →
            ∃ a : ℝ, Ioo a (a + 2 * R) ⊆ P.base) ∧
      ((¬ Continuous.HasFiniteHorizontalComplexity T) ↔
        ∃ a b a' b' : ↥K.vertices,
          (horizontalContactDisplacements K T a b a' b').Infinite) := by
  intro K T hTile hNontrivial
  have aperiodic_of_notFinite :=
    notFiniteComplexity_implies_columnBaseAperiodic hTile hNontrivial
  have wide_of_aperiodic :=
    columnBaseAperiodic_implies_uniqueWideNoncolumn hTile hNontrivial
  have infinite_of_wide :=
    uniqueWideNoncolumn_implies_infiniteContactDisplacement
      hTile hNontrivial
  have notFinite_of_infinite :
      (∃ a b a' b' : ↥K.vertices,
        (horizontalContactDisplacements K T a b a' b').Infinite) →
      ¬ Continuous.HasFiniteHorizontalComplexity T := by
    rintro ⟨a, b, a', b', hInfinite⟩ hFinite
    exact infiniteContactDisplacement_notFiniteComplexity hFinite a b a' b' hInfinite
  refine ⟨⟨aperiodic_of_notFinite, ?_⟩, ⟨?_, ?_⟩, ⟨?_, notFinite_of_infinite⟩⟩
  · rintro ⟨hne, haperiodic⟩
    exact notFinite_of_infinite (infinite_of_wide (wide_of_aperiodic hne haperiodic))
  · intro hnotFinite
    obtain ⟨hne, haperiodic⟩ := aperiodic_of_notFinite hnotFinite
    exact wide_of_aperiodic hne haperiodic
  · intro hwide
    exact notFinite_of_infinite (infinite_of_wide hwide)
  · intro hnotFinite
    obtain ⟨hne, haperiodic⟩ := aperiodic_of_notFinite hnotFinite
    exact infinite_of_wide (wide_of_aperiodic hne haperiodic)


end Tiling.AxisParallel.Structure
