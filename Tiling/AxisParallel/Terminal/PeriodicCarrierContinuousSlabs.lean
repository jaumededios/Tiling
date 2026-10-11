import Tiling.AxisParallel.Structure.HorizontalBoundaryChains
import Tiling.AxisParallel.Structure.HorizontalComplexityCharacterization.ColumnBaseCharacterization
import Tiling.AxisParallel.Continuous.ContinuousSlabPeriodicity
import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Terminal.PeriodicCarrierRationalSlabs
import Tiling.AxisParallel.Approximation.PeriodicBandDeformation
import Tiling.AxisParallel.Approximation.FiniteLocalComplexityControl
import Tiling.AxisParallel.Continuous.HorizontalFLCAlphabet
import Tiling.AxisParallel.Approximation.GoodApproximationPreservesTilings
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Mathlib.Algebra.Order.Floor.Ring
import Tiling.AxisParallel.OneDimensional.ColumnSlices
import Tiling.AxisParallel.OneDimensional.FiniteInterval.PeriodConsequences
import Tiling.AxisParallel.OneDimensional.FiniteInterval.PeriodicTarget
import Mathlib.Topology.Algebra.Module.Cardinality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Continuous slabs over a periodic vertical carrier

The certificate below records the literal centre and regular-support decomposition used by the
terminal assembly.  It deliberately stores the finite list of noncolumn plates directly and uses
the native continuous plate type throughout.
-/

open Set
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel.Terminal

/-- The first-coordinate base of the aggregate support of all column plates. -/
def aggregateColumnBase
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane) : Set ℝ :=
  Complex.re '' Tiling.AxisParallel.regularSupport K
    (Tiling.AxisParallel.Continuous.verticalColumnCentres K T)

/-- Carrier, noncolumn-plate, and aggregate-column boundaries used by the slab code. -/
def totalSlabBoundary
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane)
    (X : PeriodicVerticalCarrier) : Set ℝ :=
  frontier X.base ∪
    (⋃ P : {P : Tiling.AxisParallel.Continuous.VerticalPlate K T |
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P}, frontier P.1.base) ∪
    frontier (aggregateColumnBase K T)

/-- A finite noncolumn-slab decomposition together with the aggregate column interface. -/
structure PeriodicCarrierSlabDecomposition
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane)
    (X : PeriodicVerticalCarrier) where
  source_tiles : Tiling.AxisParallel.TilesOn K T X.carrier
  numberOfNonColumnPlates : ℕ
  nonColumnPlate : Fin numberOfNonColumnPlates →
    Tiling.AxisParallel.Continuous.VerticalPlate K T
  nonColumnPlate_noncolumn : ∀ i,
    ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn (nonColumnPlate i)
  nonColumnPlate_injective : Function.Injective nonColumnPlate
  nonColumnPlate_complete :
    ∀ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P →
        ∃ i, nonColumnPlate i = P
  columnCentres : Set Tiling.Plane
  columnCentres_eq : columnCentres =
    Tiling.AxisParallel.Continuous.verticalColumnCentres K T
  centres_partition :
    columnCentres ∪ (⋃ i, (nonColumnPlate i).centres) = T
  nonColumnCentres_pairwise :
    Set.PairwiseDisjoint Set.univ (fun i ↦ (nonColumnPlate i).centres)
  column_nonColumn_disjoint : ∀ i,
    Disjoint columnCentres (nonColumnPlate i).centres
  commonSupportPeriod : ℝ
  commonSupportPeriod_pos : 0 < commonSupportPeriod
  nonColumnSupport_periodic : ∀ i,
    Tiling.RationalPolygonal.SetPeriodicBy (nonColumnPlate i).support
      (commonSupportPeriod : ℂ)
  columnBase : Set ℝ
  columnBase_regular : interior (closure columnBase) = columnBase
  columnSupport_eq :
    Tiling.AxisParallel.regularSupport K columnCentres =
      Complex.re ⁻¹' columnBase
  columnSupport_periodic :
    Tiling.RationalPolygonal.SetPeriodicBy
      (Tiling.AxisParallel.regularSupport K columnCentres)
      (commonSupportPeriod : ℂ)
  nonColumnSupports_pairwise :
    Set.PairwiseDisjoint Set.univ (fun i ↦ (nonColumnPlate i).support)
  column_nonColumnSupport_disjoint : ∀ i,
    Disjoint (Tiling.AxisParallel.regularSupport K columnCentres)
      (nonColumnPlate i).support
  supports_cover :
    interior (closure
      (Tiling.AxisParallel.regularSupport K columnCentres ∪
        ⋃ i, (nonColumnPlate i).support)) = X.carrier
  nonColumn_minimal : ∀ i,
    Tiling.AxisParallel.Continuous.IsMinimalVerticalSlabSubfamily
      K T (nonColumnPlate i).centres
  columnAxes : Set ℝ
  columnFibre : ℝ → Set ℝ
  columnCentres_formula :
    columnCentres = {z : Tiling.Plane |
      ∃ h ∈ columnAxes, z.re = h ∧ z.im ∈ columnFibre h}
  columnInterface : columnCentres.Nonempty →
    columnAxes.Nonempty ∧
      (∀ h ∈ columnAxes,
        Tiling.AxisParallel.IsCenterColumn
          Tiling.AxisParallel.Axis.vertical K
          {z : Tiling.Plane | z.re = h ∧ z.im ∈ columnFibre h}) ∧
      ∃ alpha beta : ℝ, 0 < alpha ∧ 0 < beta ∧
        beta +ᵥ columnAxes = columnAxes ∧
        (∀ h ∈ columnAxes, alpha +ᵥ columnFibre h = columnFibre h) ∧
        ∀ w : ℝ, ∃ S : Set Tiling.Plane,
          Tiling.IsPacking K.toPolygonalRegion.prototileFamily
            (K.toPolygonalRegion.placements S) ∧
          Tiling.AxisParallel.regularSupport K S =
            Tiling.AxisParallel.regularSupport K columnCentres ∧
          Tiling.RationalPolygonal.SetPeriodicBy S
            ((alpha : ℂ) * Complex.I) ∧
          Tiling.RationalPolygonal.SetPeriodicBy S
            ((beta : ℂ) + (w : ℂ) * Complex.I) ∧
          Tiling.AxisParallel.IsLatticePeriodic S

/-- The aggregate column base is definitionally the real projection of its support. -/
theorem aggregateColumnBase_eq
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane) :
    aggregateColumnBase K T = Complex.re ''
      Tiling.AxisParallel.regularSupport K
        (Tiling.AxisParallel.Continuous.verticalColumnCentres K T) :=
  rfl

/-- The total slab boundary unfolds to its three native boundary families. -/
theorem totalSlabBoundary_eq
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane)
    (X : PeriodicVerticalCarrier) :
    totalSlabBoundary K T X = frontier X.base ∪
      (⋃ P : {P : Tiling.AxisParallel.Continuous.VerticalPlate K T |
        ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P}, frontier P.1.base) ∪
      frontier (aggregateColumnBase K T) :=
  rfl

/-- Regularization commutes with an arbitrary union after regularizing once more. -/
theorem regularSupport_iUnion
    {I : Type*} {K : Tiling.AxisParallel.Region}
    (S : I → Set Tiling.Plane) :
    Tiling.AxisParallel.regularSupport K (⋃ i, S i) =
      interior (closure (⋃ i, Tiling.AxisParallel.regularSupport K (S i))) := by
  have hopenUnion (i : I) : IsOpen (Tiling.AxisParallel.openUnion K (S i)) := by
    apply isOpen_iUnion
    intro s
    change IsOpen ((Homeomorph.addLeft (s : Tiling.Plane)) '' K.openCarrier)
    exact (Homeomorph.addLeft (s : Tiling.Plane)).isOpenMap _ isOpen_interior
  have hopen : Tiling.AxisParallel.openUnion K (⋃ i, S i) =
      ⋃ i, Tiling.AxisParallel.openUnion K (S i) := by
    ext x
    simp only [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion,
      ← Region.openCarrier.eq_def, Set.mem_iUnion]
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨i, hsi⟩ := Set.mem_iUnion.mp s.2
      exact ⟨i, ⟨⟨s.1, hsi⟩, hs⟩⟩
    · rintro ⟨i, s, hs⟩
      exact ⟨⟨s.1, Set.mem_iUnion.mpr ⟨i, s.2⟩⟩, hs⟩
  have hforward :
      (⋃ i, Tiling.AxisParallel.openUnion K (S i)) ⊆
        ⋃ i, Tiling.AxisParallel.regularSupport K (S i) := by
    apply Set.iUnion_mono
    intro i
    exact (hopenUnion i).subset_interior_closure
  have hbackward :
      (⋃ i, Tiling.AxisParallel.regularSupport K (S i)) ⊆
        closure (⋃ i, Tiling.AxisParallel.openUnion K (S i)) := by
    apply Set.iUnion_subset
    intro i
    exact interior_subset.trans
      (closure_mono (Set.subset_iUnion
        (fun j ↦ Tiling.AxisParallel.openUnion K (S j)) i))
  have hclosure :
      closure (⋃ i, Tiling.AxisParallel.openUnion K (S i)) =
        closure (⋃ i, Tiling.AxisParallel.regularSupport K (S i)) := by
    apply Set.Subset.antisymm
    · exact closure_mono hforward
    · exact closure_minimal hbackward isClosed_closure
  rw [Tiling.AxisParallel.regularSupport, Tiling.Polygonal.regularSupport,
    ← openUnion, hopen, hclosure]

/-- Preserving all strict horizontal comparisons preserves the corresponding difference signs. -/
theorem carrierVerticalEdgeOrder
    {C : Tiling.AxisParallel.Approximation.ApproximationContext}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (hOrder : ∀ (v w : C.region.vertices) (s t : C.centres),
      ((v.1 + (s.1 : Tiling.Plane)).re < (w.1 + (t.1 : Tiling.Plane)).re ↔
        (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint v.1 v.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint s.1 s.2)).re <
          (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint w.1 w.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint t.1 t.2)).re)) :
    ∀ (v w : C.region.vertices) (s t : C.centres),
      Real.sign ((v.1 + (s.1 : Tiling.Plane)).re -
        (w.1 + (t.1 : Tiling.Plane)).re) =
      Real.sign
        ((Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint v.1 v.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint s.1 s.2)).re -
          (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint w.1 w.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint t.1 t.2)).re) := by
  intro v w s t
  let a := (v.1 + (s.1 : Tiling.Plane)).re
  let b := (w.1 + (t.1 : Tiling.Plane)).re
  let a' :=
    (Tiling.AxisParallel.Approximation.mapPoint phi
        (C.vertexPoint v.1 v.2) +
      Tiling.AxisParallel.Approximation.mapPoint phi
        (C.centrePoint s.1 s.2)).re
  let b' :=
    (Tiling.AxisParallel.Approximation.mapPoint phi
        (C.vertexPoint w.1 w.2) +
      Tiling.AxisParallel.Approximation.mapPoint phi
        (C.centrePoint t.1 t.2)).re
  have hab : a < b ↔ a' < b' := by
    simpa only [a, b, a', b'] using hOrder v w s t
  have hba : b < a ↔ b' < a' := by
    simpa only [a, b, a', b'] using hOrder w v t s
  change Real.sign (a - b) = Real.sign (a' - b')
  rcases lt_trichotomy a b with hablt | habeq | hbalt
  · rw [Real.sign_of_neg (sub_neg.mpr hablt),
      Real.sign_of_neg (sub_neg.mpr (hab.mp hablt))]
  · have hab' : a' = b' := by
      apply le_antisymm
      · exact le_of_not_gt fun hb'a' ↦ by
          have := hba.mpr hb'a'
          linarith
      · exact le_of_not_gt fun ha'b' ↦ by
          have := hab.mpr ha'b'
          linarith
    simp [habeq, hab']
  · rw [Real.sign_of_pos (sub_pos.mpr hbalt),
      Real.sign_of_pos (sub_pos.mpr (hba.mp hbalt))]

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Terminal

private def PreservesHorizontalTranslatedVertexSigns
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) : Prop :=
  ∀ v w : C.region.vertices, ∀ s t : C.centres,
    Real.sign ((w.1 + (t : Tiling.Plane)).re -
      (v.1 + (s : Tiling.Plane)).re) =
    Real.sign
      ((mapPoint phi (C.vertexPoint w.1 w.2) +
          mapPoint phi (C.centrePoint t.1 t.2)).re -
        (mapPoint phi (C.vertexPoint v.1 v.2) +
          mapPoint phi (C.centrePoint s.1 s.2)).re)

private def ControlsHorizontalTranslatedVertexDistances
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) : Prop :=
  ∀ v w : C.region.vertices, ∀ s t : C.centres,
    (1 / 2 : ℝ) *
        |(w.1 + (t : Tiling.Plane)).re - (v.1 + (s : Tiling.Plane)).re| ≤
      |(mapPoint phi (C.vertexPoint w.1 w.2) +
          mapPoint phi (C.centrePoint t.1 t.2)).re -
        (mapPoint phi (C.vertexPoint v.1 v.2) +
          mapPoint phi (C.centrePoint s.1 s.2)).re| ∧
    |(mapPoint phi (C.vertexPoint w.1 w.2) +
        mapPoint phi (C.centrePoint t.1 t.2)).re -
      (mapPoint phi (C.vertexPoint v.1 v.2) +
        mapPoint phi (C.centrePoint s.1 s.2)).re| ≤
      2 * |(w.1 + (t : Tiling.Plane)).re - (v.1 + (s : Tiling.Plane)).re|

private theorem periodicBandFineness_mono :
    ∀ {C : ApproximationContext.{0}}
      (P : PeriodicBandData C) {epsilon delta : ℝ},
      IsPeriodicBandFineness P epsilon → 0 < delta → delta ≤ epsilon →
        IsPeriodicBandFineness P delta := by
  intro C P epsilon delta hFine hdelta hδε
  refine {
    epsilon_pos := hdelta
    forces_good := fun phi hphi => hFine.forces_good phi
      (hphi.of_le hδε)
    preserves_gap_positivity := ?_ }
  intro phi hphi g hg
  exact hFine.preserves_gap_positivity phi
    (hphi.of_le hδε) g hg

private theorem translatedVertices_horizontal_relativelyDense
    (C : ApproximationContext.{0}) (X : PeriodicVerticalCarrier)
    (htarget : C.target = X.carrier)
    (hTile : Tiling.AxisParallel.TilesOn C.region C.centres C.target) :
    ∃ L : ℝ, 0 < L ∧ ∀ x : ℝ,
      ∃ a ∈ horizontalTranslatedVertices C.region C.centres, |a - x| < L := by
  obtain ⟨rho, hrho, hdense, _hcentres⟩ :=
    translatedVertices_relativelyDense C X.base X.period
      (MeasureTheory.nonempty_of_measure_ne_zero X.base_nonnull) X.base_open
      X.period_pos X.base_periodic htarget hTile
  refine ⟨rho, hrho, ?_⟩
  intro x
  obtain ⟨a, ha, hza⟩ := hdense (x : Tiling.Plane)
  change a ∈ C.region.vertices + C.centres at ha
  obtain ⟨v, hv, t, ht, hvt⟩ := ha
  refine ⟨a.re, ?_, ?_⟩
  · rw [horizontalTranslatedVertices_eq]
    exact ⟨v, hv, t, ht, hvt.symm ▸ rfl⟩
  · have hproj : |a.re - x| ≤ dist (x : Tiling.Plane) a := by
      simpa [Real.dist_eq, dist_eq_norm, abs_sub_comm] using
        (Complex.abs_re_le_norm ((x : Tiling.Plane) - a))
    exact hproj.trans_lt hza

private theorem carrierApproximation_globalDistortion :
    ∀ (C : ApproximationContext.{0}) (X : PeriodicVerticalCarrier),
      C.target = X.carrier →
      Tiling.AxisParallel.TilesOn C.region C.centres C.target →
      HasFiniteHorizontalComplexity C.centres →
      ∃ epsilon > 0, ∀ phi : C.coordinateSpace →ₗ[ℚ] ℚ,
        IsEpsilonApproximation C epsilon phi →
          ControlsHorizontalTranslatedVertexDistances C phi := by
  intro C X htarget hTile hFHC
  let A : Set ℝ := horizontalTranslatedVertices C.region C.centres
  have hAflc : HasFLC A := by
    dsimp only [A]
    rw [Tiling.AxisParallel.Continuous.horizontalTranslatedVertices_eq_projection_add_vertices]
    exact hFHC.add_finset (C.region.vertexFinset.image Complex.re)
  obtain ⟨delta, hdelta, hseparated⟩ := hAflc.uniformlyDiscrete
  have hDense : ∃ L : ℝ, 0 < L ∧
      ∀ x : ℝ, ∃ a ∈ A, |a - x| < L := by
    simpa [A] using translatedVertices_horizontal_relativelyDense C X htarget hTile
  have hBounded : ∀ R : ℝ, (horizontalBoundedDifferences A R).Finite := by
    intro R
    simpa [A] using horizontalBoundedDifferences_finite hFHC R
  have horder : Nonempty (HorizontalOrderData A) := by
    apply Tiling.AxisParallel.Continuous.delone_has_integerOrderData
    · refine ⟨delta, hdelta, ?_⟩
      intro x hx y hy hxy
      simpa only [Real.dist_eq] using hseparated x hx y hy hxy
    · exact hDense
    · exact hBounded
  let order : HorizontalOrderData A := Classical.choice horder
  have hpointMem : ∀ i : ℤ, order.point i ∈ C.coordinateSpace := by
    intro i
    have hiA : order.point i ∈ A := by
      exact Eq.mp
        (congrArg (fun S : Set ℝ ↦ order.point i ∈ S) order.point_range)
        (Set.mem_range_self i)
    obtain ⟨v, hv, t, ht, hit⟩ := hiA
    rw [hit, Complex.add_re]
    exact C.coordinateSpace.add_mem
      (C.vertex_re_mem v hv) (C.centre_re_mem t ht)
  let pointLift : ℤ → C.coordinateSpace :=
    fun i ↦ ⟨order.point i, hpointMem i⟩
  have hgapMem : ∀ g ∈ order.gapAlphabet, g ∈ C.coordinateSpace := by
    intro g hg
    obtain ⟨i, hi⟩ := order.gap_complete g hg
    rw [hi]
    exact C.coordinateSpace.sub_mem (hpointMem (i + 1)) (hpointMem i)
  have hgapNonempty : order.gapAlphabet.Nonempty := by
    exact ⟨order.point (0 + 1) - order.point 0, order.gap_mem 0⟩
  let gmin : ℝ := order.gapAlphabet.min' hgapNonempty
  have hgmin_mem : gmin ∈ order.gapAlphabet := by
    exact order.gapAlphabet.min'_mem hgapNonempty
  have hgmin_pos : 0 < gmin := order.gap_pos gmin hgmin_mem
  obtain ⟨epsilon, hepsilon, hcontrol⟩ :=
    approximation_uniformOnHorizontalAlphabet C order.gapAlphabet hgapMem
      (half_pos hgmin_pos)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro phi hphi
  have hgapLower : ∀ g : ↑order.gapAlphabet,
      (1 / 2 : ℝ) * (g : ℝ) < mapScalar phi (⟨(g : ℝ), hgapMem g g.2⟩) := by
    intro g
    have herr := hcontrol phi hphi (g : ℝ) g.2
    have hminle : gmin ≤ (g : ℝ) :=
      order.gapAlphabet.min'_le (g : ℝ) g.2
    have hpos := order.gap_pos (g : ℝ) g.2
    have herr' := (abs_lt.mp herr).1
    linarith
  have hgapUpper : ∀ g : ↑order.gapAlphabet,
      mapScalar phi (⟨(g : ℝ), hgapMem g g.2⟩) < 2 * (g : ℝ) := by
    intro g
    have herr := hcontrol phi hphi (g : ℝ) g.2
    have hminle : gmin ≤ (g : ℝ) :=
      order.gapAlphabet.min'_le (g : ℝ) g.2
    have hpos := order.gap_pos (g : ℝ) g.2
    have herr' := (abs_lt.mp herr).2
    linarith
  have hindexed :=
    Tiling.AxisParallel.Continuous.finitePositiveGaps_control_indexedDifferences
    C order phi pointLift (fun i ↦ rfl)
      (fun g ↦ ⟨(g : ℝ), hgapMem g g.2⟩) (fun g ↦ rfl)
      hgapLower hgapUpper
  have hmapAt : ∀ (v : C.region.vertices) (t : C.centres),
      ∀ i : ℤ, order.point i = (v.1 + (t : Tiling.Plane)).re →
      mapScalar phi (pointLift i) =
        (mapPoint phi (C.vertexPoint v.1 v.2) +
          mapPoint phi (C.centrePoint t.1 t.2)).re := by
    intro v t i hi
    have hpoint : pointLift i =
        ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ +
          ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
      apply Subtype.ext
      simp [pointLift, hi, Complex.add_re]
    have hadd : mapScalar phi
          (⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ +
            ⟨t.1.re, C.centre_re_mem t.1 t.2⟩) =
        mapScalar phi ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ +
          mapScalar phi ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
      change ((phi (_ + _) : ℚ) : ℝ) =
        ((phi _ : ℚ) : ℝ) + ((phi _ : ℚ) : ℝ)
      rw [map_add, Rat.cast_add]
    rw [hpoint, hadd]
    simp [mapScalar, mapPoint, ApproximationContext.vertexPoint,
      ApproximationContext.centrePoint]
  have hstrict : ∀ (v w : C.region.vertices) (s t : C.centres),
      (v.1 + (s : Tiling.Plane)).re <
        (w.1 + (t : Tiling.Plane)).re →
      (1 / 2 : ℝ) * ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) ≤
        |(mapPoint phi (C.vertexPoint w.1 w.2) +
            mapPoint phi (C.centrePoint t.1 t.2)).re -
          (mapPoint phi (C.vertexPoint v.1 v.2) +
            mapPoint phi (C.centrePoint s.1 s.2)).re| ∧
      |(mapPoint phi (C.vertexPoint w.1 w.2) +
          mapPoint phi (C.centrePoint t.1 t.2)).re -
        (mapPoint phi (C.vertexPoint v.1 v.2) +
          mapPoint phi (C.centrePoint s.1 s.2)).re| ≤
        2 * ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) := by
    intro v w s t hvw
    have hvA : (v.1 + (s : Tiling.Plane)).re ∈ A := by
      exact ⟨v.1, v.2, s.1, s.2, rfl⟩
    have hwA : (w.1 + (t : Tiling.Plane)).re ∈ A := by
      exact ⟨w.1, w.2, t.1, t.2, rfl⟩
    obtain ⟨i, hi⟩ : ∃ i, order.point i =
        (v.1 + (s : Tiling.Plane)).re := by
      exact order.point_range.symm.subset hvA
    obtain ⟨j, hj⟩ : ∃ j, order.point j =
        (w.1 + (t : Tiling.Plane)).re := by
      exact order.point_range.symm.subset hwA
    have hij : i < j := order.point_strictMono.lt_iff_lt.mp
      (hi.trans_lt (hvw.trans_eq hj.symm))
    have hbounds := hindexed i j hij
    have hmi := hmapAt v s i hi
    have hmj := hmapAt w t j hj
    rw [hi, hj, hmi, hmj] at hbounds
    have hsourcepos : 0 <
        (w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re := sub_pos.mpr hvw
    have hpos : 0 <
        (mapPoint phi (C.vertexPoint w.1 w.2) +
            mapPoint phi (C.centrePoint t.1 t.2)).re -
          (mapPoint phi (C.vertexPoint v.1 v.2) +
            mapPoint phi (C.centrePoint s.1 s.2)).re := by linarith [hbounds.1]
    rw [abs_of_pos hpos]
    constructor <;> linarith
  intro v w s t
  rcases lt_trichotomy
    ((v.1 + (s : Tiling.Plane)).re) ((w.1 + (t : Tiling.Plane)).re) with hvw | heq | hwv
  · have hsourcepos : 0 <
        (w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re := sub_pos.mpr hvw
    rw [abs_of_pos hsourcepos]
    exact hstrict v w s t hvw
  · have hmapzero :
        (mapPoint phi (C.vertexPoint w.1 w.2) +
            mapPoint phi (C.centrePoint t.1 t.2)).re -
          (mapPoint phi (C.vertexPoint v.1 v.2) +
            mapPoint phi (C.centrePoint s.1 s.2)).re = 0 := by
      have hsource : (w.1 + (t : Tiling.Plane)).re =
          (v.1 + (s : Tiling.Plane)).re := by linarith
      have hwa : (w.1 + (t : Tiling.Plane)).re ∈ A := ⟨w.1, w.2, t.1, t.2, rfl⟩
      have hva : (v.1 + (s : Tiling.Plane)).re ∈ A := ⟨v.1, v.2, s.1, s.2, rfl⟩
      obtain ⟨i, hi⟩ := order.point_range.symm.subset hva
      obtain ⟨j, hj⟩ := order.point_range.symm.subset hwa
      have hij : i = j := order.point_strictMono.injective (by linarith [hi, hj])
      have hvs := hmapAt v s i hi
      have hwt := hmapAt w t j hj
      rw [← hij] at hwt
      rw [hvs] at hwt
      linarith
    rw [hmapzero, abs_zero, heq, sub_self]
    exact ⟨by norm_num, by norm_num⟩
  · have hsourcepos : 0 <
        (v.1 + (s : Tiling.Plane)).re -
          (w.1 + (t : Tiling.Plane)).re := sub_pos.mpr hwv
    have hrev := hstrict w v t s hwv
    rw [abs_of_neg (sub_neg.mpr hwv)]
    convert hrev using 1 <;> simp only [abs_sub_comm] <;> ring_nf

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Approximation

private theorem verticalPlateBase_regularizedProjection
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier)
    (P : VerticalPlate K T) :
    P.base = interior (closure
      (Complex.re '' openUnion K P.centres)) := by
  have hslab :=
    (relativeCarrier_verticalPlates hTile
      (periodicVerticalCarrier_carrier_eq X) X.base_regular.symm
      (fun a b ↦ by
        simpa only [inter_comm] using hTile.verticalCylinder_frontier_locallyFinite
          X.base_open X.base_regular (Icc a b) isCompact_Icc)).1 P
  let U : Set Tiling.Plane := openUnion K P.centres
  let A : Set ℝ := Complex.re '' U
  have hopenU : IsOpen U := by
    change IsOpen (openUnion K P.centres)
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
    exact isOpen_iUnion fun s ↦
      (Homeomorph.addLeft (s : Tiling.Plane)).isOpenMap _
        K.openCarrier_regularOpen.1
  have hraw : U ⊆ P.support := by
    dsimp only [U, VerticalPlate.support, regularSupport]
    exact interior_maximal subset_closure hopenU
  have hclosure : P.support ⊆ closure U := by
    dsimp only [U, VerticalPlate.support, regularSupport]
    exact interior_subset
  have hA : A ⊆ P.base := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨z, hraw hz, rfl⟩
  have hbase_closure : P.base ⊆ closure A := by
    rintro x ⟨z, hz, rfl⟩
    have hzcl : z ∈ closure U := hclosure hz
    exact image_closure_subset_closure_image Complex.continuous_re
      ⟨z, hzcl, rfl⟩
  have hbase_open : IsOpen P.base := by
    rw [hslab.1]
    exact isOpen_interior
  have hAeq : P.base = interior (closure A) := by
    apply Subset.antisymm
    · exact interior_maximal hbase_closure hbase_open
    · rw [hslab.1]
      exact interior_mono (closure_mono hA)
  exact hAeq

private theorem aggregateColumnBase_regularizedProjection
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) :
    aggregateColumnBase K T = interior (closure
      (Complex.re '' openUnion K (verticalColumnCentres K T))) := by
  let I := {P : VerticalPlate K T // IsVerticalColumn P}
  let S : I → Set Tiling.Plane := fun P ↦ P.1.centres
  have hslab : ∀ P : I,
      P.1.support = Complex.re ⁻¹' P.1.base := by
    intro P
    exact ((relativeCarrier_verticalPlates hTile
      (periodicVerticalCarrier_carrier_eq X) X.base_regular.symm
      (fun a b ↦ by
        simpa only [inter_comm] using hTile.verticalCylinder_frontier_locallyFinite
          X.base_open X.base_regular (Icc a b) isCompact_Icc)).1 P.1).2
  have hcentres : verticalColumnCentres K T = ⋃ P : I, S P := by
    rw [verticalColumnCentres_eq]
    rfl
  have hreg : regularSupport K (⋃ P : I, S P) =
      interior (closure (⋃ P : I, regularSupport K (S P))) := by
    exact regularSupport_iUnion S
  have hsupport : regularSupport K (verticalColumnCentres K T) =
      Complex.re ⁻¹' (interior (closure (⋃ P : I, P.1.base))) := by
    rw [hcentres, hreg]
    have hpre : (⋃ P : I, regularSupport K (S P)) =
        Complex.re ⁻¹' (⋃ P : I, P.1.base) := by
      have hslab' : ∀ P : I,
          regularSupport K (S P) = Complex.re ⁻¹' P.1.base := by
        intro P
        exact hslab P
      ext z
      simp only [Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨P, hz⟩
        rw [hslab' P] at hz
        exact ⟨P, hz⟩
      · rintro ⟨P, hz⟩
        have hz' : z ∈ regularSupport K (S P) := by
          rw [hslab' P]
          exact hz
        exact ⟨P, hz'⟩
    rw [hpre, Complex.closure_preimage_re, Complex.interior_preimage_re]
  have hbase_open : IsOpen (aggregateColumnBase K T) := by
    rw [aggregateColumnBase_eq, hsupport]
    have himage : ∀ B : Set ℝ, Complex.re '' (Complex.re ⁻¹' B) = B := by
      intro B
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hx
        exact ⟨(x : ℂ), hx, by simp⟩
    rw [himage]
    exact isOpen_interior
  let U : Set Tiling.Plane := openUnion K (verticalColumnCentres K T)
  let A : Set ℝ := Complex.re '' U
  have hopenU : IsOpen U := by
    change IsOpen (openUnion K (verticalColumnCentres K T))
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
    exact isOpen_iUnion fun s ↦
      (Homeomorph.addLeft (s : Tiling.Plane)).isOpenMap _
        K.openCarrier_regularOpen.1
  have hraw : U ⊆ regularSupport K (verticalColumnCentres K T) := by
    dsimp only [U, regularSupport]
    exact interior_maximal subset_closure hopenU
  have hclosure : regularSupport K (verticalColumnCentres K T) ⊆ closure U := by
    dsimp only [U, regularSupport]
    exact interior_subset
  have hA : A ⊆ aggregateColumnBase K T := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨z, hraw hz, rfl⟩
  have hbase_closure : aggregateColumnBase K T ⊆ closure A := by
    rw [aggregateColumnBase_eq]
    rintro x ⟨z, hz, rfl⟩
    exact image_closure_subset_closure_image Complex.continuous_re
      ⟨z, hclosure hz, rfl⟩
  have hbase_regular : interior (closure (aggregateColumnBase K T)) =
      aggregateColumnBase K T := by
    rw [aggregateColumnBase_eq, hsupport]
    have himage : ∀ B : Set ℝ, Complex.re '' (Complex.re ⁻¹' B) = B := by
      intro B
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hx
        exact ⟨(x : ℂ), hx, by simp⟩
    rw [himage, interior_closure_idem]
  apply Subset.antisymm
  · exact interior_maximal hbase_closure hbase_open
  · rw [← hbase_regular]
    exact interior_mono (closure_mono hA)

private theorem placedTileHorizontalProjection_image
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (imageCenters : ↑C.centres ↪ Tiling.Plane) (H : ℝ ≃ₜ ℝ)
    (hH : StrictMono H)
    (_hCenters : ∀ t, imageCenters t = mapPoint phi (C.centrePoint t.1 t.2))
    (hEndpoints : ∀ (v : C.region.vertices) (t : C.centres),
      H (v.1 + (t : Tiling.Plane)).re =
        (mapPoint phi (C.vertexPoint v.1 v.2) + imageCenters t).re)
    (t : C.centres) :
      H '' (Complex.re '' ((t : Tiling.Plane) +ᵥ C.region.support)) =
        Complex.re '' (imageCenters t +ᵥ D.deformedRegion.support) := by
  let F : ℝ ≃ₜ ℝ :=
    ((Homeomorph.addRight (t : Tiling.Plane).re).trans H).trans
      (Homeomorph.addLeft (-(imageCenters t).re))
  have hF : StrictMono F := by
    intro a b hab
    dsimp [F]
    simpa [sub_eq_add_neg, add_comm] using
      add_lt_add_left (hH (add_lt_add_right hab (t : Tiling.Plane).re))
        (-(imageCenters t).re)
  have hD : D.planarHomeomorph =
      coordinateProductHomeomorph D.firstHomeomorph D.secondHomeomorph := by
    apply Homeomorph.ext
    intro z
    rw [D.planarHomeomorph_apply,
      coordinateProductHomeomorph_apply D.firstHomeomorph D.secondHomeomorph z]
  have hopen :
      coordinateProductHomeomorph F D.secondHomeomorph '' C.region.openCarrier =
        coordinateProductHomeomorph D.firstHomeomorph D.secondHomeomorph ''
          C.region.openCarrier := by
    apply coordinateProductImage_openCarrier_unique C.region
      F D.secondHomeomorph D.firstHomeomorph D.secondHomeomorph
      hF D.secondHomeomorph_strictMono D.firstHomeomorph_strictMono
      D.secondHomeomorph_strictMono
    · intro v hv
      have he := hEndpoints ⟨v, hv⟩ t
      have hvD := D.vertex_agreement v hv
      rw [D.planarHomeomorph_apply] at hvD
      have hre := congrArg Complex.re hvD
      calc
        F v.re = H (v.re + (t : Tiling.Plane).re) - (imageCenters t).re := by
          simp [F, sub_eq_add_neg, add_comm]
        _ = (mapPoint phi (C.vertexPoint v hv)).re :=
          sub_eq_iff_eq_add.mpr he
        _ = D.firstHomeomorph v.re := by
          simpa [coordinateProductHomeomorph_apply] using hre.symm
    · intro v hv
      rfl
  have hsupp :
      coordinateProductHomeomorph F D.secondHomeomorph '' C.region.support =
        coordinateProductHomeomorph D.firstHomeomorph D.secondHomeomorph ''
          C.region.support := by
    have hs : C.region.support = closure C.region.openCarrier :=
      C.region.isPolygonal.closure_interior.symm
    calc
      coordinateProductHomeomorph F D.secondHomeomorph '' C.region.support =
          coordinateProductHomeomorph F D.secondHomeomorph ''
            closure C.region.openCarrier := by rw [hs]
      _ = closure (coordinateProductHomeomorph F D.secondHomeomorph ''
          C.region.openCarrier) :=
        (coordinateProductHomeomorph F D.secondHomeomorph).image_closure
          C.region.openCarrier
      _ = closure (coordinateProductHomeomorph D.firstHomeomorph
          D.secondHomeomorph '' C.region.openCarrier) := congrArg closure hopen
      _ = coordinateProductHomeomorph D.firstHomeomorph D.secondHomeomorph ''
          closure C.region.openCarrier :=
        ((coordinateProductHomeomorph D.firstHomeomorph
          D.secondHomeomorph).image_closure C.region.openCarrier).symm
      _ = coordinateProductHomeomorph D.firstHomeomorph D.secondHomeomorph ''
          C.region.support := by rw [hs]
  have hcoord_re (A B : ℝ ≃ₜ ℝ) (S : Set Tiling.Plane) :
      Complex.re '' (coordinateProductHomeomorph A B '' S) =
        A '' (Complex.re '' S) := by
    ext x
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w.re, ⟨w, hw, rfl⟩, by
        simp [coordinateProductHomeomorph_apply]⟩
    · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨coordinateProductHomeomorph A B w, ⟨w, hw, rfl⟩, by
        simp [coordinateProductHomeomorph_apply]⟩
  have hproj :
      F '' (Complex.re '' C.region.support) =
        D.firstHomeomorph '' (Complex.re '' C.region.support) := by
    rw [← hcoord_re F D.secondHomeomorph, ← hcoord_re D.firstHomeomorph
      D.secondHomeomorph]
    exact congrArg (fun s : Set Tiling.Plane => Complex.re '' s) hsupp
  have hDsupport : D.deformedRegion.support =
      D.planarHomeomorph '' C.region.support :=
    region_support_image_of_openCarrier_image C.region D.deformedRegion
      D.planarHomeomorph D.deformedRegion_openCarrier
  have hDsupport' : D.deformedRegion.support =
      coordinateProductHomeomorph D.firstHomeomorph D.secondHomeomorph ''
        C.region.support := by
    rw [hDsupport, hD]
  rw [hDsupport']
  have htranslate_re (c : Tiling.Plane) (A : Set Tiling.Plane) :
      Complex.re '' (c +ᵥ A) = c.re +ᵥ (Complex.re '' A) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨w.re, ⟨w, hw, rfl⟩, by simp [vadd_eq_add]⟩
    · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨c +ᵥ w, ⟨w, hw, rfl⟩, by simp [vadd_eq_add]⟩
  have hsource : H '' (Complex.re ''
      ((t : Tiling.Plane) +ᵥ C.region.support)) =
      (imageCenters t).re +ᵥ (F '' (Complex.re '' C.region.support)) := by
    rw [htranslate_re]
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨F z, ⟨z, hz, rfl⟩, ?_⟩
      dsimp [F]
      ring_nf
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨(t : Tiling.Plane).re + z, ⟨z, hz, rfl⟩, ?_⟩
      dsimp [F]
      ring_nf
  have htarget : Complex.re '' (imageCenters t +ᵥ
      (coordinateProductHomeomorph D.firstHomeomorph D.secondHomeomorph ''
        C.region.support)) =
      (imageCenters t).re +ᵥ
        (D.firstHomeomorph '' (Complex.re '' C.region.support)) := by
    rw [htranslate_re, hcoord_re]
  exact hsource.trans (by rw [hproj, ← htarget])
end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open MeasureTheory Function

private structure CompleteColumnFamilyData
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane) where
  axes : Set ℝ
  fibre : ℝ → Set ℝ
  centres_formula :
    Tiling.AxisParallel.Continuous.verticalColumnCentres K T =
      {z : Tiling.Plane | ∃ h ∈ axes, z.re = h ∧ z.im ∈ fibre h}
  columnCentres_packing :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        (Tiling.AxisParallel.Continuous.verticalColumnCentres K T))
  axes_nonempty : axes.Nonempty
  fibre_columns : ∀ h ∈ axes,
    Tiling.AxisParallel.IsCenterColumn Tiling.AxisParallel.Axis.vertical K
      {z : Tiling.Plane | z.re = h ∧ z.im ∈ fibre h}
  verticalPeriod : ℝ
  verticalPeriod_pos : 0 < verticalPeriod
  fibre_periodic : ∀ h ∈ axes,
    verticalPeriod +ᵥ fibre h = fibre h
  horizontalPeriod : ℝ
  horizontalPeriod_pos : 0 < horizontalPeriod
  axes_periodic : horizontalPeriod +ᵥ axes = axes

private def orbitIndex (p h : ℝ) : ℤ := Int.floor (h / p)

private def orbitRepresentative (p h : ℝ) : ℝ :=
  h - (orbitIndex p h : ℝ) * p

private def shearedFibre {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w h : ℝ) : Set ℝ :=
  ((orbitIndex D.horizontalPeriod h : ℝ) * w) +ᵥ
    D.fibre (orbitRepresentative D.horizontalPeriod h)

private def shearedCentres {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w : ℝ) : Set Tiling.Plane :=
  {z : Tiling.Plane |
    ∃ h ∈ D.axes, z.re = h ∧ z.im ∈ shearedFibre D w h}

private theorem orbitIndex_shift
    {p h : ℝ} (hp : 0 < p) :
    orbitIndex p (h + p) = orbitIndex p h + 1 := by
  unfold orbitIndex
  rw [show (h + p) / p = h / p + 1 by field_simp]
  simpa only [Int.cast_one] using (Int.floor_add_intCast (h / p) (1 : ℤ))

private theorem orbitRepresentative_shift
    {p h : ℝ} (hp : 0 < p) :
    orbitRepresentative p (h + p) = orbitRepresentative p h := by
  unfold orbitRepresentative
  rw [orbitIndex_shift hp]
  simp only [Int.cast_add, Int.cast_one]
  ring_nf

private theorem axes_zsmul_period
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {D : CompleteColumnFamilyData K T} (n : ℤ) :
    (n : ℝ) * D.horizontalPeriod +ᵥ D.axes = D.axes := by
  have hp : D.horizontalPeriod ∈ Tiling.AxisParallel.periodGroup D.axes := by
    exact (Tiling.AxisParallel.periodGroup_isAddSubgroup D.axes _).mpr D.axes_periodic
  have hn := (Tiling.AxisParallel.periodGroup D.axes).zsmul_mem hp n
  apply (Tiling.AxisParallel.periodGroup_isAddSubgroup D.axes _).mp at hn
  simpa [smul_eq_mul] using hn

private theorem representative_mem_axes
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {D : CompleteColumnFamilyData K T} {h : ℝ} (hh : h ∈ D.axes) :
    orbitRepresentative D.horizontalPeriod h ∈ D.axes := by
  unfold orbitRepresentative
  have hshift := axes_zsmul_period (D := D) (-orbitIndex D.horizontalPeriod h)
  have hm : ((-orbitIndex D.horizontalPeriod h : ℤ) : ℝ) *
      D.horizontalPeriod + h ∈
      ((-orbitIndex D.horizontalPeriod h : ℤ) : ℝ) *
        D.horizontalPeriod +ᵥ D.axes := ⟨h, hh, rfl⟩
  rw [hshift] at hm
  simpa [vadd_eq_add, sub_eq_add_neg, add_comm, mul_comm]
    using hm

private theorem shearedFibre_shift
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {D : CompleteColumnFamilyData K T} {w h : ℝ} :
    shearedFibre D w (h + D.horizontalPeriod) =
      w +ᵥ shearedFibre D w h := by
  unfold shearedFibre
  rw [orbitIndex_shift D.horizontalPeriod_pos,
    orbitRepresentative_shift D.horizontalPeriod_pos]
  ext y
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  constructor <;> intro hy
  · convert hy using 1
    all_goals norm_num [Int.cast_add]
    all_goals ring_nf
  · convert hy using 1
    all_goals norm_num [Int.cast_add]
    all_goals ring_nf

private theorem shearedCentres_vertical_period
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w : ℝ) :
    ((D.verticalPeriod : ℂ) * Complex.I) +ᵥ shearedCentres D w =
      shearedCentres D w := by
  ext z
  constructor
  · intro hz
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz
    change ∃ h ∈ D.axes, (-((D.verticalPeriod : ℂ) * Complex.I) + z).re = h ∧
      (-((D.verticalPeriod : ℂ) * Complex.I) + z).im ∈ shearedFibre D w h at hz
    rcases hz with ⟨h, hh, hzre, hzim⟩
    refine ⟨h, hh, ?_, ?_⟩
    · convert hzre using 1
      simp
    let F := shearedFibre D w h
    have hper : D.verticalPeriod +ᵥ F = F := by
      dsimp [F, shearedFibre]
      rw [← add_vadd]
      rw [show D.verticalPeriod +
          (orbitIndex D.horizontalPeriod h : ℝ) * w =
          (orbitIndex D.horizontalPeriod h : ℝ) * w + D.verticalPeriod by ring_nf]
      rw [add_vadd]
      rw [D.fibre_periodic (orbitRepresentative D.horizontalPeriod h)
        (representative_mem_axes (D := D) hh)]
    have hz' : z.im ∈ D.verticalPeriod +ᵥ F := by
      refine ⟨(-((D.verticalPeriod : ℂ) * Complex.I) + z).im, ?_, ?_⟩
      · simpa [F] using hzim
      · simp only [vadd_eq_add]
        norm_num
    rw [hper] at hz'
    simpa [F] using hz'
  · intro hz
    rcases hz with ⟨h, hh, hzre, hzim⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change ∃ h' ∈ D.axes, (-((D.verticalPeriod : ℂ) * Complex.I) + z).re = h' ∧
      (-((D.verticalPeriod : ℂ) * Complex.I) + z).im ∈ shearedFibre D w h'
    refine ⟨h, hh, ?_, ?_⟩
    · convert hzre using 1
      simp
    · let F := shearedFibre D w h
      have hper : D.verticalPeriod +ᵥ F = F := by
        dsimp [F, shearedFibre]
        rw [← add_vadd]
        rw [show D.verticalPeriod +
            (orbitIndex D.horizontalPeriod h : ℝ) * w =
            (orbitIndex D.horizontalPeriod h : ℝ) * w + D.verticalPeriod by ring_nf]
        rw [add_vadd]
        rw [D.fibre_periodic (orbitRepresentative D.horizontalPeriod h)
          (representative_mem_axes (D := D) hh)]
      have hz' : z.im ∈ D.verticalPeriod +ᵥ F := by
        rw [hper]
        simpa [F] using hzim
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz'
      simpa [F] using hz'

private theorem shearedCentres_skew_period
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w : ℝ) :
    ((D.horizontalPeriod : ℂ) + (w : ℂ) * Complex.I) +ᵥ shearedCentres D w =
      shearedCentres D w := by
  ext z
  constructor
  · intro hz
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz
    change ∃ h ∈ D.axes,
      (-((D.horizontalPeriod : ℂ) + (w : ℂ) * Complex.I) + z).re = h ∧
      (-((D.horizontalPeriod : ℂ) + (w : ℂ) * Complex.I) + z).im ∈ shearedFibre D w h at hz
    rcases hz with ⟨h, hh, hzre, hzim⟩
    have hh' : h + D.horizontalPeriod ∈ D.axes := by
      rw [← D.axes_periodic]
      exact ⟨h, hh, by
          change D.horizontalPeriod + h = h + D.horizontalPeriod
          ring_nf
        ⟩
    refine ⟨h + D.horizontalPeriod, hh', ?_, ?_⟩
    · have hzre' : -D.horizontalPeriod + z.re = h := by
        simpa using hzre
      linarith
    · rw [shearedFibre_shift (D := D) (w := w) (h := h)]
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [vadd_eq_add, add_assoc, add_comm, add_left_comm] using hzim
  · intro hz
    rcases hz with ⟨h, hh, hzre, hzim⟩
    have hprev : h - D.horizontalPeriod ∈ D.axes := by
      have hshift := axes_zsmul_period (D := D) (-1)
      have hm : (-D.horizontalPeriod) + h ∈
          (-D.horizontalPeriod) +ᵥ D.axes := ⟨h, hh, rfl⟩
      have hshift' : (-D.horizontalPeriod) +ᵥ D.axes = D.axes := by
        simpa [smul_eq_mul] using hshift
      rw [hshift'] at hm
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hm
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change ∃ h' ∈ D.axes,
      (-((D.horizontalPeriod : ℂ) + (w : ℂ) * Complex.I) + z).re = h' ∧
      (-((D.horizontalPeriod : ℂ) + (w : ℂ) * Complex.I) + z).im ∈ shearedFibre D w h'
    refine ⟨h - D.horizontalPeriod, hprev, ?_, ?_⟩
    · have hzre' : z.re = h := by
        simpa using hzre
      norm_num at ⊢
      linarith
    · have hf := shearedFibre_shift (D := D) (w := w)
        (h := h - D.horizontalPeriod)
      have hf' : shearedFibre D w h =
          w +ᵥ shearedFibre D w (h - D.horizontalPeriod) := by
        convert hf using 1
        ring_nf
      rw [hf'] at hzim
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzim
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzim

open Tiling.AxisParallel
open Tiling.AxisParallel.Terminal
open Tiling.AxisParallel.OneDimensional.FiniteInterval

private def carrierAxes (K : Region) (T : Set Tiling.Plane) : Set ℝ :=
  Complex.re '' Tiling.AxisParallel.Continuous.verticalColumnCentres K T

private def carrierFibre (K : Region) (T : Set Tiling.Plane) (h : ℝ) : Set ℝ :=
  {y : ℝ | (h : ℂ) + (y : ℂ) * Complex.I ∈
    Tiling.AxisParallel.Continuous.verticalColumnCentres K T}

private def carrierHorizontalFootprint (K : Region) : Set ℝ :=
  interior (closure (Complex.re '' K.openCarrier))

private theorem carrierCentres_formula (K : Region) (T : Set Tiling.Plane) :
    Tiling.AxisParallel.Continuous.verticalColumnCentres K T =
      {z : Tiling.Plane | ∃ h ∈ carrierAxes K T,
        z.re = h ∧ z.im ∈ carrierFibre K T h} := by
  ext z
  constructor
  · intro hz
    refine ⟨z.re, ⟨z, hz, rfl⟩, rfl, ?_⟩
    simp only [carrierFibre]
    simpa using hz
  · rintro ⟨h, -, hzh, hz⟩
    simp only [carrierFibre] at hz
    have heq : z = (h : ℂ) + (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hzh]
    rw [heq]
    exact hz

private theorem carrierFibre_nonempty
    {K : Region} {T : Set Tiling.Plane} {h : ℝ}
    (hh : h ∈ carrierAxes K T) : (carrierFibre K T h).Nonempty := by
  rcases hh with ⟨z, hz, rfl⟩
  refine ⟨z.im, ?_⟩
  simp only [carrierFibre]
  simpa using hz

private theorem carrierFibre_centres_subset
    {K : Region} {T : Set Tiling.Plane} (h : ℝ) :
    {z : Tiling.Plane | z.re = h ∧ z.im ∈ carrierFibre K T h} ⊆
      Tiling.AxisParallel.Continuous.verticalColumnCentres K T := by
  intro z hz
  simp only [carrierFibre] at hz
  have heq : z = (h : ℂ) + (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hz.1]
  rw [heq]
  exact hz.2

private theorem carrierFibre_packing
    {K : Region} {T X : Set Tiling.Plane}
    (hTile : TilesOn K T X) (h : ℝ) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        {z : Tiling.Plane | z.re = h ∧ z.im ∈ carrierFibre K T h}) := by
  apply (isPacking_iff_openCarrier_disjoint K _).mpr
  intro s hs t ht hst
  exact (isPacking_iff_openCarrier_disjoint K _).mp hTile.2.1
    (Continuous.verticalColumnCentres_subset K T (carrierFibre_centres_subset h hs))
    (Continuous.verticalColumnCentres_subset K T (carrierFibre_centres_subset h ht)) hst

private theorem carrierFibre_regularSupport
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier) (hTile : TilesOn K T X.carrier)
    {h : ℝ} (hh : h ∈ carrierAxes K T) :
    ∃ B : Set ℝ, B = interior (closure B) ∧
      regularSupport K
        {z : Tiling.Plane | z.re = h ∧ z.im ∈ carrierFibre K T h} =
          Complex.re ⁻¹' B := by
  let C : Set Tiling.Plane :=
    {z : Tiling.Plane | z.re = h ∧ z.im ∈ carrierFibre K T h}
  obtain ⟨z, hzcol, hzr⟩ := hh
  rw [Tiling.AxisParallel.Continuous.verticalColumnCentres_eq,
    Set.mem_iUnion] at hzcol
  obtain ⟨P, hzP⟩ := hzcol
  have hrelative := Tiling.AxisParallel.Continuous.relativeCarrier_verticalPlates
    hTile (periodicVerticalCarrier_carrier_eq X) X.base_regular.symm
      (fun a b ↦ by
        simpa only [inter_comm] using hTile.verticalCylinder_frontier_locallyFinite
          X.base_open X.base_regular (Icc a b) isCompact_Icc)
  have hPslab := hrelative.1 P.1
  have hPformula := hrelative.2.2.2 P.1 P.2 h
  have hPaxis : P.1.centres ⊆ {z : Tiling.Plane | z.re = h} := by
    obtain ⟨c, hc⟩ := P.2
    have hch : c = h := by
      have := hc hzP
      simpa [hzr] using this.symm
    intro s hs
    simpa [hch] using hc hs
  have hPformula' := hPformula hPaxis
  refine ⟨P.1.base, hPslab.1, ?_⟩
  have hPC : P.1.centres ⊆ C := by
    intro s hs
    refine ⟨hPaxis hs, ?_⟩
    change (h : ℂ) + (s.im : ℂ) * Complex.I ∈
      Tiling.AxisParallel.Continuous.verticalColumnCentres K T
    have hscol : s ∈ Tiling.AxisParallel.Continuous.verticalColumnCentres K T := by
      rw [Tiling.AxisParallel.Continuous.verticalColumnCentres_eq,
        Set.mem_iUnion]
      exact ⟨P, hs⟩
    have heq : s = (h : ℂ) + (s.im : ℂ) * Complex.I := by
      apply Complex.ext
      · simpa using hPaxis hs
      · simp
    rw [← heq]
    exact hscol
  apply le_antisymm
  · rw [regularSupport, Tiling.Polygonal.regularSupport, ← openUnion]
    have hopenSub : openUnion K C ⊆ P.1.support := by
      intro x hx
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hx
      obtain ⟨s, hxs⟩ := hx
      have hscol := carrierFibre_centres_subset h s.2
      rw [Tiling.AxisParallel.Continuous.verticalColumnCentres_eq,
        Set.mem_iUnion] at hscol
      obtain ⟨Q, hsQ⟩ := hscol
      have hQaxis : Q.1.centres ⊆ {z : Tiling.Plane | z.re = h} := by
        obtain ⟨c, hc⟩ := Q.2
        have hch : c = h := by
          have := hc hsQ
          simpa [s.2.1] using this.symm
        intro t ht
        simpa [hch] using hc ht
      have hQformula := hrelative.2.2.2 Q.1 Q.2 h hQaxis
      have htileQ : (s : Tiling.Plane) +ᵥ K.openCarrier ⊆ Q.1.support := by
        intro y hy
        change y ∈ interior (closure (openUnion K Q.1.centres))
        apply interior_maximal subset_closure
        · rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
          exact isOpen_iUnion fun q ↦
            (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _
              K.openCarrier_regularOpen.1
        · rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
          exact ⟨⟨s, hsQ⟩, hy⟩
      rw [hPformula'.2]
      rw [hQformula.2] at htileQ
      simpa [hPformula'.1, hQformula.1] using htileQ hxs
    have hPreg : interior (closure P.1.support) = P.1.support := by
      rw [hPslab.2, Complex.closure_preimage_re,
        Complex.interior_preimage_re, ← hPslab.1]
    calc
      interior (closure (openUnion K C)) ⊆ interior (closure P.1.support) :=
        interior_mono (closure_mono hopenSub)
      _ = P.1.support := hPreg
      _ = Complex.re ⁻¹' P.1.base := hPslab.2
  · rw [← hPslab.2]
    change regularSupport K P.1.centres ⊆ regularSupport K C
    unfold regularSupport Tiling.Polygonal.regularSupport
    exact interior_mono (closure_mono (by
      intro x hx
      rw [Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hx ⊢
      obtain ⟨s, hxs⟩ := hx
      exact ⟨⟨s.1, hPC s.2⟩, hxs⟩))

private theorem carrierFibre_isCenterColumn
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier) (hTile : TilesOn K T X.carrier)
    {h : ℝ} (hh : h ∈ carrierAxes K T) :
    IsCenterColumn Axis.vertical K
      {z : Tiling.Plane | z.re = h ∧ z.im ∈ carrierFibre K T h} := by
  obtain ⟨B, hBreg, hsupport⟩ := carrierFibre_regularSupport X hTile hh
  refine ⟨carrierFibre_packing hTile h, ?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := carrierFibre_nonempty hh
    exact ⟨(h : ℂ) + (y : ℂ) * Complex.I, by simp [hy]⟩
  · refine ⟨h, ?_⟩
    intro z hz
    simpa [Axis.transverseCoord] using hz.1
  · intro a
    rw [hsupport]
    ext z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_preimage,
      vadd_eq_add]
    simp [Complex.add_re]

private theorem genericVerticalSlice_exists (K : Region) :
    ∃ r : ℝ, r ∉ K.vertexFinset.image Complex.re ∧
      (Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r).Nonempty := by
  have hopen : IsOpen (Complex.re '' K.openCarrier) :=
    Complex.isOpenMap_re _ K.openCarrier_regularOpen.1
  have hne : (Complex.re '' K.openCarrier).Nonempty := by
    obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
    exact ⟨z.re, z, hz, rfl⟩
  have hcount : (K.vertexFinset.image Complex.re : Set ℝ).Countable :=
    (K.vertexFinset.image Complex.re).finite_toSet.countable
  have hdense : Dense ((K.vertexFinset.image Complex.re : Set ℝ)ᶜ) :=
    hcount.dense_compl ℝ
  obtain ⟨r, hr, hrproj⟩ := hdense.exists_mem_open hopen hne
  refine ⟨r, hr, ?_⟩
  rcases hrproj with ⟨z, hz, hzr⟩
  refine ⟨z.im, ?_⟩
  change (r : ℂ) + (z.im : ℂ) * Complex.I ∈ K.openCarrier
  convert hz using 1
  apply Complex.ext <;> simp [hzr]

private theorem commonCarrierFibrePeriod_exists
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier) (hTile : TilesOn K T X.carrier) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∀ h ∈ carrierAxes K T, alpha +ᵥ carrierFibre K T h = carrierFibre K T h := by
  obtain ⟨r, hrgeneric, hBne⟩ := genericVerticalSlice_exists K
  let B := Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r
  have hBfinite : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion B :=
    (K.verticalSlice_finiteIntervals hrgeneric).1
  have hBpos : 0 < (volume B).toReal :=
    OneDimensional.ColumnSlices.finiteIntervalRegion_volume_toReal_pos hBfinite hBne
  obtain ⟨alpha, halpha, -, hcommon⟩ :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.exists_commonLinePeriod
      hBfinite hBpos
  refine ⟨alpha, halpha, ?_⟩
  intro h hh
  apply hcommon
  exact Tiling.AxisParallel.OneDimensional.ColumnSlices.genericSliceTilings_of_completeColumn
    (carrierFibre_nonempty hh) (carrierFibre_isCenterColumn X hTile hh)
      r hrgeneric hBne

private def endpointSection {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w h : ℝ) : Set Tiling.Plane :=
  {z : Tiling.Plane | z.re = h ∧ z.im ∈ shearedFibre D w h}

private def sourceFibre {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (h : ℝ) : Set Tiling.Plane :=
  {z : Tiling.Plane | z.re = h ∧ z.im ∈ D.fibre h}

private def fibreSupport {K : Region} (h : ℝ) : Set Tiling.Plane :=
  {z : Tiling.Plane |
    z.re ∈ interior (closure (h +ᵥ (Complex.re '' K.openCarrier)))}

private theorem endpointSection_translate
    {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w h : ℝ) :
    endpointSection D w h =
      (((h - orbitRepresentative D.horizontalPeriod h : ℝ) : ℂ) +
        (((orbitIndex D.horizontalPeriod h : ℝ) * w : ℝ) : ℂ) *
          Complex.I) +ᵥ
        sourceFibre D (orbitRepresentative D.horizontalPeriod h) := by
  ext z
  simp only [endpointSection, shearedFibre, sourceFibre, Set.mem_ofPred_eq,
    Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  constructor
  · rintro ⟨hzr, hzi⟩
    constructor
    · simp only [Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
        mul_zero, zero_mul, sub_zero, Complex.neg_re]
      linarith
    · simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_im, Complex.ofReal_re, Complex.I_re,
        mul_one, zero_mul, zero_add]
      simpa [sub_eq_add_neg, add_comm] using hzi
  · rintro ⟨hzr, hzi⟩
    constructor
    · simp only [Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
        mul_zero, zero_mul, sub_zero, Complex.neg_re] at hzr
      linarith
    · simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_im, Complex.ofReal_re, Complex.I_re,
        mul_one, zero_mul, zero_add] at hzi
      simpa [sub_eq_add_neg, add_comm] using hzi

private theorem sourceFibre_support
    {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) {h : ℝ} (hh : h ∈ D.axes) :
    regularSupport K (sourceFibre D h) = fibreSupport (K := K) h := by
  obtain ⟨c, -, hcoord, hsupport⟩ :=
    centerColumn_regularSupport (D.fibre_columns h hh)
  have hc : c = h := by
    rcases (D.fibre_columns h hh).2.1 with ⟨z, hz⟩
    have hzc : z.re = c := by
      simpa [Axis.transverseCoord] using hcoord (z : Tiling.Plane) hz
    linarith [hz.1, hzc]
  change regularSupport K {z : Tiling.Plane |
      z.re = h ∧ z.im ∈ D.fibre h} = _
  rw [hsupport, hc]
  rfl

private theorem fibreSupport_translate
    {K : Region} {q h a : ℝ} :
    (((h - q : ℝ) : ℂ) + (a : ℂ) * Complex.I) +ᵥ
      fibreSupport (K := K) q = fibreSupport (K := K) h := by
  ext z
  simp only [fibreSupport, Set.mem_vadd_set_iff_neg_vadd_mem,
    Set.mem_ofPred_eq, vadd_eq_add, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero,
    zero_mul, sub_zero]
  have hset : (h - q) +ᵥ interior (closure (q +ᵥ (Complex.re '' K.openCarrier))) =
      interior (closure (h +ᵥ (Complex.re '' K.openCarrier))) := by
    rw [closure_vadd, interior_vadd, closure_vadd, interior_vadd]
    ext x
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    constructor <;> intro hx
    · ring_nf at hx ⊢
      exact hx
    · ring_nf at hx ⊢
      exact hx
  constructor
  · intro hz
    change (-(h - q + 0) + z.re) ∈ interior (closure (q +ᵥ (Complex.re '' K.openCarrier))) at hz
    have hz0 : (-(h - q) + z.re) ∈ interior (closure (q +ᵥ (Complex.re '' K.openCarrier))) := by
      simpa only [sub_eq_add_neg, add_zero] using hz
    have hz' : z.re ∈ (h - q) +ᵥ
        interior (closure (q +ᵥ (Complex.re '' K.openCarrier))) := by
      exact Set.mem_vadd_set_iff_neg_vadd_mem.mpr hz0
    rw [hset] at hz'
    exact hz'
  · intro hz
    change z.re ∈ interior (closure (h +ᵥ (Complex.re '' K.openCarrier))) at hz
    rw [← hset] at hz
    simpa only [vadd_eq_add, sub_eq_add_neg, add_zero] using
      (Set.mem_vadd_set_iff_neg_vadd_mem.mp hz)

private theorem endpointSection_support
    {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w : ℝ) {h : ℝ} (hh : h ∈ D.axes) :
    regularSupport K (endpointSection D w h) = fibreSupport (K := K) h := by
  rw [endpointSection_translate, regularSupport_vadd,
    sourceFibre_support D (representative_mem_axes hh)]
  exact fibreSupport_translate

private theorem sourceFibres_pairwise_support_disjoint
    {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) {h k : ℝ}
    (hh : h ∈ D.axes) (hk : k ∈ D.axes) (hhk : h ≠ k) :
    Disjoint (fibreSupport (K := K) h) (fibreSupport (K := K) k) := by
  have hsub (r : ℝ) (hr : r ∈ D.axes) : sourceFibre D r ⊆
      Tiling.AxisParallel.Continuous.verticalColumnCentres K T := by
    rw [D.centres_formula]
    exact fun z hz ↦ ⟨r, hr, hz.1, hz.2⟩
  have hpack (r : ℝ) (hr : r ∈ D.axes) :
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements (sourceFibre D r)) := by
    apply (isPacking_iff_openCarrier_disjoint K _).mpr
    intro s hs t ht hst
    exact (isPacking_iff_openCarrier_disjoint K _).mp D.columnCentres_packing
      (hsub r hr hs) (hsub r hr ht) hst
  have hopenDisjoint : Disjoint (openUnion K (sourceFibre D h))
      (openUnion K (sourceFibre D k)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hx hy
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    have hst : (s : Tiling.Plane) ≠ t := by
      intro heq
      apply hhk
      have hsre : (s : Tiling.Plane).re = h := s.2.1
      have htre : (t : Tiling.Plane).re = k := t.2.1
      have := congrArg Complex.re heq
      linarith
    exact Set.disjoint_left.1
      ((isPacking_iff_openCarrier_disjoint K _).mp D.columnCentres_packing
        (hsub h hh s.2) (hsub k hk t.2) hst) hs ht
  rw [← sourceFibre_support D hh, ← sourceFibre_support D hk,
    Set.disjoint_left]
  intro x hxh hxk
  have hzero : volume (regularSupport K (sourceFibre D h) ∩
      regularSupport K (sourceFibre D k)) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [openUnion_aeEq_regularSupport (hpack h hh),
      openUnion_aeEq_regularSupport (hpack k hk)] with y hyh hyk
    intro hy
    have hyh' : y ∈ openUnion K (sourceFibre D h) := by
      exact Eq.mp hyh.symm hy.1
    have hyk' : y ∈ openUnion K (sourceFibre D k) := by
      exact Eq.mp hyk.symm hy.2
    exact Set.disjoint_left.1 hopenDisjoint hyh' hyk'
  exact ((regularSupport_isRegularOpen K (sourceFibre D h)).1.inter
    (regularSupport_isRegularOpen K (sourceFibre D k)).1).measure_ne_zero
      volume ⟨x, hxh, hxk⟩ hzero

private theorem fibreSupport_eq_preimage_footprint
    {K : Region} (h : ℝ) :
    fibreSupport (K := K) h =
      Complex.re ⁻¹' (h +ᵥ carrierHorizontalFootprint K) := by
  rw [fibreSupport, carrierHorizontalFootprint, closure_vadd, interior_vadd]
  rfl

private theorem carrierAxes_countable
    {K : Region} {T : Set Tiling.Plane} {X : Set Tiling.Plane}
    (hTile : TilesOn K T X) : (carrierAxes K T).Countable := by
  apply hTile.1.image Complex.re |>.mono
  rintro h ⟨z, hz, rfl⟩
  exact ⟨z, Continuous.verticalColumnCentres_subset K T hz, rfl⟩

private theorem carrierAxes_pairwise_base_disjoint
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier) (hTile : TilesOn K T X.carrier) :
    Set.Pairwise (carrierAxes K T)
      (Disjoint on fun h : ℝ => h +ᵥ carrierHorizontalFootprint K) := by
  intro h hh k hk hhk
  let Ch : Set Tiling.Plane :=
    {z : Tiling.Plane | z.re = h ∧ z.im ∈ carrierFibre K T h}
  let Ck : Set Tiling.Plane :=
    {z : Tiling.Plane | z.re = k ∧ z.im ∈ carrierFibre K T k}
  have hsub (q : ℝ) :
      {z : Tiling.Plane | z.re = q ∧ z.im ∈ carrierFibre K T q} ⊆
        Tiling.AxisParallel.Continuous.verticalColumnCentres K T :=
    carrierFibre_centres_subset q
  have hopenDisjoint : Disjoint (openUnion K Ch) (openUnion K Ck) := by
    rw [Set.disjoint_left]
    intro x hx hy
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hx hy
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    have hst : (s : Tiling.Plane) ≠ t := by
      intro heq
      apply hhk
      have hsre : (s : Tiling.Plane).re = h := s.2.1
      have htre : (t : Tiling.Plane).re = k := t.2.1
      have := congrArg Complex.re heq
      linarith
    exact Set.disjoint_left.1
      ((isPacking_iff_openCarrier_disjoint K _).mp hTile.2.1
        (Continuous.verticalColumnCentres_subset K T (hsub h s.2))
        (Continuous.verticalColumnCentres_subset K T (hsub k t.2)) hst) hs ht
  have hs : Disjoint (regularSupport K Ch) (regularSupport K Ck) := by
    rw [Set.disjoint_left]
    intro x hxh hxk
    have hzero : volume (regularSupport K Ch ∩ regularSupport K Ck) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [openUnion_aeEq_regularSupport (carrierFibre_packing hTile h),
        openUnion_aeEq_regularSupport (carrierFibre_packing hTile k)] with y hyh hyk
      intro hy
      have hy1 : regularSupport K Ch y := by
        exact hy.1
      have hy2 : regularSupport K Ck y := by
        exact hy.2
      have hyh' : y ∈ openUnion K Ch := by
        exact hyh.symm.mp hy1
      have hyk' : y ∈ openUnion K Ck := by
        exact hyk.symm.mp hy2
      exact Set.disjoint_left.1 hopenDisjoint hyh' hyk'
    exact ((regularSupport_isRegularOpen K Ch).1.inter
      (regularSupport_isRegularOpen K Ck).1).measure_ne_zero
        volume ⟨x, hxh, hxk⟩ hzero
  have hsh : regularSupport K Ch = fibreSupport (K := K) h := by
    obtain ⟨c, -, hcoord, hsupport⟩ :=
      centerColumn_regularSupport (carrierFibre_isCenterColumn X hTile hh)
    have hc : c = h := by
      obtain ⟨y, hy⟩ := carrierFibre_nonempty hh
      have hz : (h : ℂ) + (y : ℂ) * Complex.I ∈ Ch := by simp [Ch, hy]
      have := hcoord _ hz
      simpa [Axis.transverseCoord] using this.symm
    rw [hsupport, hc]
    rfl
  have hsk : regularSupport K Ck = fibreSupport (K := K) k := by
    obtain ⟨c, -, hcoord, hsupport⟩ :=
      centerColumn_regularSupport (carrierFibre_isCenterColumn X hTile hk)
    have hc : c = k := by
      obtain ⟨y, hy⟩ := carrierFibre_nonempty hk
      have hz : (k : ℂ) + (y : ℂ) * Complex.I ∈ Ck := by simp [Ck, hy]
      have := hcoord _ hz
      simpa [Axis.transverseCoord] using this.symm
    rw [hsupport, hc]
    rfl
  rw [hsh, hsk, fibreSupport_eq_preimage_footprint,
    fibreSupport_eq_preimage_footprint] at hs
  change Disjoint (h +ᵥ carrierHorizontalFootprint K)
    (k +ᵥ carrierHorizontalFootprint K)
  rw [Set.disjoint_left]
  intro x hxh hxk
  have hxh' : (x : ℂ) ∈ Complex.re ⁻¹'
      (h +ᵥ carrierHorizontalFootprint K) := by simpa using hxh
  have hxk' : (x : ℂ) ∈ Complex.re ⁻¹'
      (k +ᵥ carrierHorizontalFootprint K) := by simpa using hxk
  exact Set.disjoint_left.1 hs
    hxh' hxk'

private theorem carrierAxes_lineTilesOn_openUnion
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier) (hTile : TilesOn K T X.carrier) :
    Tiling.AxisParallel.OneDimensional.LineTilesOn
      (carrierHorizontalFootprint K) (carrierAxes K T)
      (Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion
        (carrierHorizontalFootprint K) (carrierAxes K T)) := by
  have hB : OneDimensional.IsFiniteIntervalRegion (carrierHorizontalFootprint K) := by
    obtain ⟨n, left, right, -, hclosed⟩ :=
      Tiling.AxisParallel.horizontalProjectionClosure_finiteClosedIntervals K
    rw [carrierHorizontalFootprint, hclosed]
    exact OneDimensional.ColumnSlices.finiteClosedIntervals_interior_isFiniteIntervalRegion
      left right
  have hBmeas : MeasurableSet (carrierHorizontalFootprint K) := by
    rcases hB with ⟨n, left, right, -, hEq⟩
    rw [hEq]
    exact MeasurableSet.iUnion fun _ => measurableSet_Ioo
  have hopen : IsOpen
      (Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion
        (carrierHorizontalFootprint K) (carrierAxes K T)) := by
    rw [Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion]
    exact isOpen_iUnion fun h : carrierAxes K T =>
      (by
        rcases hB with ⟨n, left, right, -, hEq⟩
        rw [hEq]
        exact (isOpen_iUnion fun _ => isOpen_Ioo).vadd (h : ℝ))
  refine ⟨hBmeas, hopen.measurableSet, carrierAxes_countable hTile,
    fun h hh k hk hhk =>
      (carrierAxes_pairwise_base_disjoint X hTile hh hk hhk).aedisjoint, ?_⟩
  filter_upwards [] with x
  rw [Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion,
    Set.mem_iUnion]

private theorem carrierAggregate_support_regularizedTarget
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier) (hTile : TilesOn K T X.carrier) :
    regularSupport K
        (Tiling.AxisParallel.Continuous.verticalColumnCentres K T) =
      Complex.re ⁻¹'
        (Tiling.AxisParallel.OneDimensional.FiniteInterval.regularizedTarget
          (carrierHorizontalFootprint K) (carrierAxes K T)) := by
  have hcentres :
      Tiling.AxisParallel.Continuous.verticalColumnCentres K T =
        ⋃ h : carrierAxes K T,
          {z : Tiling.Plane | z.re = h.1 ∧ z.im ∈ carrierFibre K T h.1} := by
    rw [carrierCentres_formula]
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h, hh, hzr, hzi⟩
      exact ⟨⟨h, hh⟩, hzr, hzi⟩
    · rintro ⟨⟨h, hh⟩, hzr, hzi⟩
      exact ⟨h, hh, hzr, hzi⟩
  rw [hcentres, Tiling.AxisParallel.Terminal.regularSupport_iUnion]
  have hsupp (h : carrierAxes K T) :
      regularSupport K
          {z : Tiling.Plane | z.re = h.1 ∧ z.im ∈ carrierFibre K T h.1} =
        Complex.re ⁻¹' (h.1 +ᵥ carrierHorizontalFootprint K) := by
    obtain ⟨c, -, hcoord, hs⟩ :=
      centerColumn_regularSupport (carrierFibre_isCenterColumn X hTile h.2)
    have hc : c = h.1 := by
      obtain ⟨y, hy⟩ := carrierFibre_nonempty h.2
      have hz : (h.1 : ℂ) + (y : ℂ) * Complex.I ∈
          {z : Tiling.Plane | z.re = h.1 ∧ z.im ∈ carrierFibre K T h.1} := by
        simp [hy]
      have := hcoord _ hz
      simpa [Axis.transverseCoord] using this.symm
    rw [hs, hc]
    change fibreSupport (K := K) h = _
    exact fibreSupport_eq_preimage_footprint h
  simp_rw [hsupp]
  rw [← Set.preimage_iUnion, Complex.closure_preimage_re,
    Complex.interior_preimage_re]
  rfl

private theorem completeColumnFamilyData_exists :
    ∀ {K : Region} {T : Set Tiling.Plane} {beta : ℝ}
      (X : PeriodicVerticalCarrier),
    TilesOn K T X.carrier →
    (Tiling.AxisParallel.Continuous.verticalColumnCentres K T).Nonempty →
    0 < beta →
    Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K
        (Tiling.AxisParallel.Continuous.verticalColumnCentres K T)) (beta : ℂ) →
      Nonempty (CompleteColumnFamilyData K T) := by
  intro K T beta X hTile hColumn hbeta hperiod
  have hAxes : (carrierAxes K T).Nonempty := by
    obtain ⟨z, hz⟩ := hColumn
    exact ⟨z.re, z, hz, rfl⟩
  obtain ⟨alpha, halpha, hAlpha⟩ := commonCarrierFibrePeriod_exists X hTile
  let B := carrierHorizontalFootprint K
  let H := carrierAxes K T
  let R := Tiling.AxisParallel.OneDimensional.FiniteInterval.regularizedTarget B H
  have hBfinite : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion B := by
    obtain ⟨n, left, right, -, hclosed⟩ :=
      Tiling.AxisParallel.horizontalProjectionClosure_finiteClosedIntervals K
    change OneDimensional.IsFiniteIntervalRegion (carrierHorizontalFootprint K)
    rw [carrierHorizontalFootprint, hclosed]
    exact OneDimensional.ColumnSlices.finiteClosedIntervals_interior_isFiniteIntervalRegion
      left right
  have hBne : B.Nonempty := by
    have hopen : IsOpen (Complex.re '' K.openCarrier) :=
      Complex.isOpenMap_re _ K.openCarrier_regularOpen.1
    have hne : (Complex.re '' K.openCarrier).Nonempty :=
      (K.isPolygonal.interior_nonempty K.nonempty).image Complex.re
    exact ⟨hne.choose, hopen.subset_interior_closure hne.choose_spec⟩
  have hBpos : 0 < (volume B).toReal :=
    OneDimensional.ColumnSlices.finiteIntervalRegion_volume_toReal_pos hBfinite hBne
  have hLine := carrierAxes_lineTilesOn_openUnion X hTile
  let P := IntervalPresentation.ofIsFiniteIntervalRegion hBfinite
  obtain ⟨-, -, -, -, hLineR, -⟩ :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.LineTilesOn.regularizedTarget
      P hLine hBpos
  have hRperiod : beta +ᵥ R = R := by
    have hsupp := carrierAggregate_support_regularizedTarget X hTile
    ext x
    have hp := hperiod (-((beta : ℂ)) + (x : ℂ))
    rw [hsupp] at hp
    simpa [R, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      add_comm, add_left_comm, add_assoc] using hp.symm
  obtain ⟨betaAxis, hbetaAxis, hAxesPeriod⟩ :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.periodicTarget_lineTiling_finiteIntervals
      hBfinite hBpos hLineR hbeta
        (Filter.Eventually.of_forall fun x =>
          propext (Set.ext_iff.mp hRperiod x))
  refine ⟨{
    axes := carrierAxes K T
    fibre := carrierFibre K T
    centres_formula := carrierCentres_formula K T
    columnCentres_packing := by
      apply (isPacking_iff_openCarrier_disjoint K _).mpr
      intro s hs t ht hst
      exact (isPacking_iff_openCarrier_disjoint K _).mp hTile.2.1
        (Continuous.verticalColumnCentres_subset K T hs)
        (Continuous.verticalColumnCentres_subset K T ht) hst
    axes_nonempty := hAxes
    fibre_columns := fun h hh => carrierFibre_isCenterColumn X hTile hh
    verticalPeriod := alpha
    verticalPeriod_pos := halpha
    fibre_periodic := hAlpha
    horizontalPeriod := betaAxis
    horizontalPeriod_pos := hbetaAxis
    axes_periodic := hAxesPeriod }⟩

private theorem endpointSection_packing
    {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w : ℝ) {h : ℝ} (hh : h ∈ D.axes) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (endpointSection D w h)) := by
  let q := orbitRepresentative D.horizontalPeriod h
  let u : Tiling.Plane :=
    ((h - q : ℝ) : ℂ) +
      (((orbitIndex D.horizontalPeriod h : ℝ) * w : ℝ) : ℂ) * Complex.I
  have hq : q ∈ D.axes := representative_mem_axes hh
  have hsource : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (sourceFibre D q)) :=
    (D.fibre_columns q hq).1
  apply (isPacking_iff_openCarrier_disjoint K _).mpr
  intro s hs t ht hst
  rw [endpointSection_translate] at hs ht
  obtain ⟨s₀, hs₀, rfl⟩ := hs
  obtain ⟨t₀, ht₀, rfl⟩ := ht
  have hne : s₀ ≠ t₀ := by
    intro heq
    apply hst
    simp [heq]
  have hd := (isPacking_iff_openCarrier_disjoint K _).mp hsource hs₀ ht₀ hne
  change Disjoint
    ((u +ᵥ s₀) +ᵥ K.openCarrier)
    ((u +ᵥ t₀) +ᵥ K.openCarrier)
  apply Set.disjoint_left.2
  intro x hxs hxt
  apply Set.disjoint_left.1 hd
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxs
    change -u + x ∈ s₀ +ᵥ K.openCarrier
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, add_assoc, add_comm, add_left_comm] using hxs
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxt
    change -u + x ∈ t₀ +ᵥ K.openCarrier
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, add_assoc, add_comm, add_left_comm] using hxt

private theorem endpointSection_tile_subset_support
    {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w : ℝ) {h : ℝ} (hh : h ∈ D.axes)
    {s : Tiling.Plane} (hs : s ∈ endpointSection D w h) :
    s +ᵥ K.openCarrier ⊆ fibreSupport (K := K) h := by
  rw [← endpointSection_support D w hh]
  intro x hx
  apply interior_maximal subset_closure
  · rw [Tiling.Polygonal.openUnion, ← Region.openCarrier]
    exact isOpen_iUnion fun q ↦
      (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _
        K.openCarrier_regularOpen.1
  · rw [Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨s, hs⟩, hx⟩

private theorem endpointCentres_packing
    {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w : ℝ) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (shearedCentres D w)) := by
  apply (isPacking_iff_openCarrier_disjoint K _).mpr
  intro s hs t ht hst
  rcases hs with ⟨h, hh, hsre, hsim⟩
  rcases ht with ⟨k, hk, htre, htim⟩
  have hs' : s ∈ endpointSection D w h := ⟨hsre, hsim⟩
  have ht' : t ∈ endpointSection D w k := ⟨htre, htim⟩
  by_cases hhk : h = k
  · have ht'' : t ∈ endpointSection D w h := by
      simpa [hhk] using ht'
    exact (isPacking_iff_openCarrier_disjoint K _).mp
      (endpointSection_packing D w hh) hs' ht'' hst
  · change Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.openCarrier)
    rw [Set.disjoint_left]
    intro x hxs hxt
    have hxH := endpointSection_tile_subset_support D w hh hs' hxs
    have hxK := endpointSection_tile_subset_support D w hk ht' hxt
    exact Set.disjoint_left.1
      (sourceFibres_pairwise_support_disjoint D hh hk hhk) hxH hxK

private theorem endpointCentres_eq_iUnion
    {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w : ℝ) :
    shearedCentres D w = ⋃ h : D.axes, endpointSection D w h := by
  ext z
  simp only [shearedCentres, endpointSection, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨h, hh, hzr, hzi⟩
    exact ⟨⟨h, hh⟩, hzr, hzi⟩
  · rintro ⟨⟨h, hh⟩, hzr, hzi⟩
    exact ⟨h, hh, hzr, hzi⟩

private theorem sourceCentres_eq_iUnion
    {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) :
    Tiling.AxisParallel.Continuous.verticalColumnCentres K T =
      ⋃ h : D.axes, sourceFibre D h := by
  rw [D.centres_formula]
  ext z
  simp only [sourceFibre, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨h, hh, hzr, hzi⟩
    exact ⟨⟨h, hh⟩, hzr, hzi⟩
  · rintro ⟨⟨h, hh⟩, hzr, hzi⟩
    exact ⟨h, hh, hzr, hzi⟩

private theorem endpointCentres_regularSupport
    {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w : ℝ) :
    regularSupport K (shearedCentres D w) =
      regularSupport K
        (Tiling.AxisParallel.Continuous.verticalColumnCentres K T) := by
  rw [endpointCentres_eq_iUnion, sourceCentres_eq_iUnion]
  calc
    regularSupport K (⋃ h : D.axes, endpointSection D w h) =
        interior (closure (⋃ h : D.axes, regularSupport K (endpointSection D w h))) :=
      Tiling.AxisParallel.Terminal.regularSupport_iUnion _
    _ = interior (closure (⋃ h : D.axes, regularSupport K (sourceFibre D h))) := by
      apply congrArg interior
      apply congrArg closure
      apply Set.iUnion_congr
      intro h
      rw [endpointSection_support D w h.2, sourceFibre_support D h.2]
    _ = regularSupport K (⋃ h : D.axes, sourceFibre D h) :=
      (Tiling.AxisParallel.Terminal.regularSupport_iUnion _).symm

private theorem endpointCentres_latticePeriodic
    {K : Region} {T : Set Tiling.Plane}
    (D : CompleteColumnFamilyData K T) (w : ℝ) :
    IsLatticePeriodic (shearedCentres D w) := by
  rw [isLatticePeriodic_iff_doublyPeriodic]
  refine ⟨(D.verticalPeriod : ℂ) * Complex.I,
    (D.horizontalPeriod : ℂ) + (w : ℂ) * Complex.I, ?_, ?_, ?_⟩
  · rw [LinearIndependent.pair_iffₛ]
    intro s t s' t' heq
    have hre := congrArg Complex.re heq
    have ht : t = t' := by
      norm_num at hre
      exact hre.resolve_right D.horizontalPeriod_pos.ne'
    subst t'
    have him := congrArg Complex.im heq
    have hs : s = s' := by
      norm_num at him
      exact him.resolve_right D.verticalPeriod_pos.ne'
    exact ⟨hs, rfl⟩
  · exact (Tiling.AxisParallel.setPeriodicBy_iff_vadd_eq _ _).mpr
      (shearedCentres_vertical_period D w)
  · exact (Tiling.AxisParallel.setPeriodicBy_iff_vadd_eq _ _).mpr
      (shearedCentres_skew_period D w)

private theorem completeColumnFamily_freeShear :
    ∀ {K : Region} {T : Set Tiling.Plane}
      (D : CompleteColumnFamilyData K T) (w : ℝ),
    ∃ S : Set Tiling.Plane,
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) ∧
      regularSupport K S = regularSupport K
        (Tiling.AxisParallel.Continuous.verticalColumnCentres K T) ∧
      Tiling.RationalPolygonal.SetPeriodicBy S
        ((D.verticalPeriod : ℂ) * Complex.I) ∧
      Tiling.RationalPolygonal.SetPeriodicBy S
        ((D.horizontalPeriod : ℂ) + (w : ℂ) * Complex.I) ∧
      IsLatticePeriodic S := by
  intro K T D w
  refine ⟨shearedCentres D w, endpointCentres_packing D w,
    endpointCentres_regularSupport D w, ?_, ?_,
    endpointCentres_latticePeriodic D w⟩
  · exact (Tiling.AxisParallel.setPeriodicBy_iff_vadd_eq _ _).mpr
      (shearedCentres_vertical_period D w)
  · exact (Tiling.AxisParallel.setPeriodicBy_iff_vadd_eq _ _).mpr
      (shearedCentres_skew_period D w)

theorem periodicColumnBase_freeShear
    {K : Region} {T : Set Tiling.Plane} {beta : ℝ}
    (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier)
    (hColumn :
      (Tiling.AxisParallel.Continuous.verticalColumnCentres K T).Nonempty)
    (hbeta : 0 < beta)
    (hperiod : Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K
        (Tiling.AxisParallel.Continuous.verticalColumnCentres K T)) (beta : ℂ)) :
    ∃ H : Set ℝ, ∃ Y : ℝ → Set ℝ, H.Nonempty ∧
      Tiling.AxisParallel.Continuous.verticalColumnCentres K T =
        {z : Tiling.Plane | ∃ h ∈ H, z.re = h ∧ z.im ∈ Y h} ∧
      ∃ alpha betaAxis : ℝ, 0 < alpha ∧ 0 < betaAxis ∧
        betaAxis +ᵥ H = H ∧
        (∀ h ∈ H, alpha +ᵥ Y h = Y h) ∧
        ∀ w : ℝ, ∃ S : Set Tiling.Plane,
          Tiling.IsPacking K.toPolygonalRegion.prototileFamily
            (K.toPolygonalRegion.placements S) ∧
          regularSupport K S = regularSupport K
            (Tiling.AxisParallel.Continuous.verticalColumnCentres K T) ∧
          Tiling.RationalPolygonal.SetPeriodicBy S
            ((alpha : ℂ) * Complex.I) ∧
          Tiling.RationalPolygonal.SetPeriodicBy S
            ((betaAxis : ℂ) + (w : ℂ) * Complex.I) ∧
          IsLatticePeriodic S := by
  obtain ⟨D⟩ := completeColumnFamilyData_exists X hTile hColumn hbeta hperiod
  refine ⟨D.axes, D.fibre, D.axes_nonempty, D.centres_formula,
    D.verticalPeriod, D.horizontalPeriod, D.verticalPeriod_pos,
    D.horizontalPeriod_pos, D.axes_periodic, D.fibre_periodic, ?_⟩
  exact completeColumnFamily_freeShear D

end Tiling.AxisParallel.Terminal

/-! Next dependency-closed target: selected-subfamily projection transport. -/
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Approximation

private theorem selectedSubfamily_regularizedProjection_image :
  ∀ (C : ApproximationContext.{0})
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (D : CoordinateDeformation C phi)
      (imageCenters : ↑C.centres ↪ Tiling.Plane) (H : ℝ ≃ₜ ℝ),
    StrictMono H →
    (∀ t, imageCenters t = mapPoint phi (C.centrePoint t.1 t.2)) →
    (∀ t : C.centres,
      H '' (Complex.re '' ((t : Tiling.Plane) +ᵥ C.region.support)) =
        Complex.re '' (imageCenters t +ᵥ D.deformedRegion.support)) →
    ∀ S : Set Tiling.Plane, S ⊆ C.centres →
      interior (closure (Complex.re '' openUnion D.deformedRegion
        (deformedCenterCarrierOn imageCenters
          {t : ↑C.centres | (t : Tiling.Plane) ∈ S}))) =
        H '' interior (closure (Complex.re '' openUnion C.region S)) := by
  intro C phi D imageCenters H _hH _hCenters hTile S hS
  have closure_projection_openUnion (K : Region) (A : Set Tiling.Plane) :
      closure (Complex.re '' openUnion K A) =
        closure (⋃ a : A, Complex.re '' ((a : Tiling.Plane) +ᵥ K.support)) := by
    apply le_antisymm
    · apply closure_mono
      rintro x ⟨z, hz, rfl⟩
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hz
      obtain ⟨a, ha⟩ := hz
      obtain ⟨w, hw, hzw⟩ := ha
      rw [Set.mem_iUnion]
      exact ⟨a, z, ⟨w, interior_subset hw, hzw⟩, rfl⟩
    · apply closure_minimal
      · rw [Set.iUnion_subset_iff]
        intro a
        rintro x ⟨z, hz, rfl⟩
        have hzcl : z ∈ closure ((a : Tiling.Plane) +ᵥ K.openCarrier) := by
          rw [closure_vadd]
          change z ∈ (a : Tiling.Plane) +ᵥ closure (interior K.support)
          rw [K.isPolygonal.closure_interior]
          exact hz
        have hxcl : z.re ∈ closure (Complex.re ''
            ((a : Tiling.Plane) +ᵥ K.openCarrier)) :=
          image_closure_subset_closure_image Complex.continuous_re
            ⟨z, hzcl, rfl⟩
        apply closure_mono (show Complex.re ''
            ((a : Tiling.Plane) +ᵥ K.openCarrier) ⊆
              Complex.re '' openUnion K A by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := hy
          exact ⟨w, by rw [openUnion, Tiling.Polygonal.openUnion,
            ← Region.openCarrier, Set.mem_iUnion]; exact ⟨a, hw⟩, rfl⟩) hxcl
      · exact isClosed_closure
  let J : Set C.centres := {t | (t : Tiling.Plane) ∈ S}
  have hsourceUnion :
      (⋃ t : J, Complex.re '' ((t.1 : Tiling.Plane) +ᵥ C.region.support)) =
        ⋃ s : S, Complex.re '' ((s.1 : Tiling.Plane) +ᵥ C.region.support) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨⟨t.1.1, t.2⟩, ht⟩
    · rintro ⟨s, hs⟩
      exact ⟨⟨⟨s.1, hS s.2⟩, s.2⟩, hs⟩
  have hclosedUnion :
      H '' (⋃ t : J,
          Complex.re '' ((t.1 : Tiling.Plane) +ᵥ C.region.support)) =
        ⋃ u : deformedCenterCarrierOn imageCenters J,
          Complex.re '' ((u.1 : Tiling.Plane) +ᵥ D.deformedRegion.support) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_iUnion] at hy
      obtain ⟨t, ht⟩ := hy
      have hi := hTile t.1
      rw [Set.mem_iUnion]
      refine ⟨⟨imageCenters t.1, ⟨t.1, t.2, rfl⟩⟩, ?_⟩
      rw [← hi]
      exact ⟨y, ht, rfl⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨u, hu⟩ := hx
      obtain ⟨t, htJ, htu⟩ := u.2
      rw [← htu] at hu
      have hi := hTile t
      rw [← hi] at hu
      obtain ⟨y, hy, rfl⟩ := hu
      refine ⟨y, ?_, rfl⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨t, htJ⟩, hy⟩
  have hclosure :
      closure (Complex.re '' openUnion D.deformedRegion
          (deformedCenterCarrierOn imageCenters J)) =
        H '' closure (Complex.re '' openUnion C.region S) := by
    calc
      closure (Complex.re '' openUnion D.deformedRegion
          (deformedCenterCarrierOn imageCenters J)) =
          closure (⋃ u : deformedCenterCarrierOn imageCenters J,
            Complex.re '' ((u.1 : Tiling.Plane) +ᵥ D.deformedRegion.support)) :=
        closure_projection_openUnion _ _
      _ = closure (H '' (⋃ t : J,
          Complex.re '' ((t.1 : Tiling.Plane) +ᵥ C.region.support))) := by
        rw [hclosedUnion]
      _ = H '' closure (⋃ t : J,
          Complex.re '' ((t.1 : Tiling.Plane) +ᵥ C.region.support)) :=
        (H.image_closure _).symm
      _ = H '' closure (Complex.re '' openUnion C.region S) := by
        rw [closure_projection_openUnion, hsourceUnion]
  rw [show {t : ↑C.centres | (t : Tiling.Plane) ∈ S} = J from rfl,
    hclosure, H.image_interior]

end Tiling.AxisParallel.Terminal

/-! Next dependency-closed target: indexed image finite horizontal complexity. -/
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation Tiling.AxisParallel.Continuous

private theorem imageCenters_finiteHorizontalComplexity :
    ∀ (C : ApproximationContext.{0})
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (imageCenters : ↑C.centres ↪ Tiling.Plane),
    HasFiniteHorizontalComplexity C.centres →
    ControlsHorizontalTranslatedVertexDistances C phi →
    (∀ t, imageCenters t = mapPoint phi (C.centrePoint t.1 t.2)) →
      HasFiniteHorizontalComplexity (deformedCenterCarrier imageCenters) := by
  intro C phi imageCenters hFHC hDistances hImage
  let A : Set ℝ := horizontalCentreProjection C.centres
  let B : Set ℝ := Complex.re '' deformedCenterCarrier imageCenters
  change HasFLC A at hFHC
  change HasFLC B
  have hzero : (0 : ℝ) ∈ B := by
    let t : ↑C.centres := ⟨0, C.zero_mem_centres⟩
    refine ⟨imageCenters t, ⟨t, rfl⟩, ?_⟩
    have hpoint : C.centrePoint t.1 t.2 =
        (⟨(0 : Tiling.Plane), C.coordinateSpace.zero_mem,
          C.coordinateSpace.zero_mem⟩ :
          {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧
            z.im ∈ C.coordinateSpace}) := by
      apply Subtype.ext
      rfl
    have hscalar :
        (⟨(0 : ℝ), C.coordinateSpace.zero_mem⟩ : C.coordinateSpace) = 0 := by
      apply Subtype.ext
      rfl
    rw [hImage t, hpoint]
    simp [mapPoint, mapScalar, hscalar]
  have hDiffAll : ∀ R : ℝ, 0 < R →
      ((B - B) ∩ Metric.closedBall (0 : ℝ) R).Finite := by
    intro R hR
    let sourceDiffs : Set ℝ :=
      (A - A) ∩ Metric.closedBall (0 : ℝ) (2 * R)
    have hSource : sourceDiffs.Finite := by
      simpa [sourceDiffs] using hFHC.2 (2 * R) (by linarith)
    let lifts : Set C.coordinateSpace := {d | (d : ℝ) ∈ sourceDiffs}
    have hLifts : lifts.Finite := by
      apply hSource.preimage Subtype.val_injective.injOn
    have hImageFinite : (mapScalar phi '' lifts).Finite :=
      hLifts.image (mapScalar phi)
    apply hImageFinite.subset
    intro d hd
    rcases hd.1 with ⟨x, hx, y, hy, rfl⟩
    change x ∈ Complex.re '' Set.range imageCenters at hx
    change y ∈ Complex.re '' Set.range imageCenters at hy
    rcases hx with ⟨_, ⟨s, rfl⟩, rfl⟩
    rcases hy with ⟨_, ⟨t, rfl⟩, rfl⟩
    have hsA : (s : Tiling.Plane).re ∈ A := ⟨s, s.property, rfl⟩
    have htA : (t : Tiling.Plane).re ∈ A := ⟨t, t.property, rfl⟩
    have hcontrol := (hDistances ⟨0, C.zero_mem_vertices⟩
      ⟨0, C.zero_mem_vertices⟩ s t).1
    rw [← hImage s, ← hImage t] at hcontrol
    have hcontrol' :
        (1 / 2 : ℝ) * |(t : Tiling.Plane).re - (s : Tiling.Plane).re| ≤
          |(imageCenters t).re - (imageCenters s).re| := by
      simpa [mapPoint, mapScalar, ApproximationContext.vertexPoint,
        ApproximationContext.centrePoint] using hcontrol
    have htargetBound :
        |(imageCenters s).re - (imageCenters t).re| ≤ R := by
      simpa [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] using hd.2
    have hsourceBound :
        |(s : Tiling.Plane).re - (t : Tiling.Plane).re| ≤ 2 * R := by
      have hcontrol'' :
          (1 / 2 : ℝ) * |(s : Tiling.Plane).re - (t : Tiling.Plane).re| ≤
            |(imageCenters s).re - (imageCenters t).re| := by
        simpa [abs_sub_comm] using hcontrol'
      nlinarith [hcontrol'', htargetBound]
    let delta : C.coordinateSpace :=
      ⟨(s : Tiling.Plane).re - (t : Tiling.Plane).re,
        C.coordinateSpace.sub_mem
          (C.centre_re_mem s s.property) (C.centre_re_mem t t.property)⟩
    have hdelta : (delta : ℝ) ∈ sourceDiffs := by
      refine ⟨⟨(s : Tiling.Plane).re, hsA,
        (t : Tiling.Plane).re, htA, ?_⟩, ?_⟩
      · simp [delta]
      · simpa [sourceDiffs, Metric.mem_closedBall, Real.dist_eq] using hsourceBound
    have htMap : mapScalar phi ⟨(t : Tiling.Plane).re,
        C.centre_re_mem t t.property⟩ = (imageCenters t).re := by
      have h := congrArg Complex.re (hImage t)
      simpa [mapPoint, mapScalar, ApproximationContext.centrePoint] using h.symm
    have hsMap : mapScalar phi ⟨(s : Tiling.Plane).re,
        C.centre_re_mem s s.property⟩ = (imageCenters s).re := by
      have h := congrArg Complex.re (hImage s)
      simpa [mapPoint, mapScalar, ApproximationContext.centrePoint] using h.symm
    have hdeltaMap : mapScalar phi delta =
        (imageCenters s).re - (imageCenters t).re := by
      change ((phi delta : ℚ) : ℝ) = _
      have hlinear : phi delta =
          phi ⟨(s : Tiling.Plane).re, C.centre_re_mem s s.property⟩ -
            phi ⟨(t : Tiling.Plane).re, C.centre_re_mem t t.property⟩ := by
        rw [← map_sub]
        apply congrArg phi
        apply Subtype.ext
        rfl
      rw [hlinear, Rat.cast_sub]
      change mapScalar phi ⟨(s : Tiling.Plane).re, _⟩ -
        mapScalar phi ⟨(t : Tiling.Plane).re, _⟩ = _
      rw [hsMap, htMap]
    refine ⟨delta, hdelta, ?_⟩
    exact hdeltaMap
  constructor
  · intro Q hQ
    obtain ⟨R, hQR⟩ := hQ.subset_closedBall (0 : ℝ)
    let R₀ := max R 1
    have hR₀ : 0 < R₀ := by
      dsimp [R₀]
      exact lt_of_lt_of_le zero_lt_one (le_max_right R 1)
    have hQR₀ : Q ⊆ Metric.closedBall (0 : ℝ) R₀ :=
      hQR.trans (Metric.closedBall_subset_closedBall (le_max_left R 1))
    have hDiff := hDiffAll R₀ hR₀
    apply hDiff.subset
    intro x hx
    refine ⟨?_, hQR₀ hx.2⟩
    exact ⟨x, hx.1, 0, hzero, by simp⟩
  · exact hDiffAll


end Tiling.AxisParallel.Terminal


/-! Global increasing extension of all translated horizontal vertex levels. -/
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation Tiling.AxisParallel.Continuous

private theorem integerSequence_covers
    (x : ℤ → ℝ) (hx : StrictMono x)
    (hbelow : ∀ z : ℝ, ∃ i : ℤ, x i ≤ z)
    (habove : ∀ z : ℝ, ∃ i : ℤ, z < x i) :
    ∀ z : ℝ, ∃ i : ℤ, x i ≤ z ∧ z < x (i + 1) := by
  intro z
  obtain ⟨b, hb⟩ := habove z
  obtain ⟨i, hi, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun i ↦ x i ≤ z)
    (⟨b, fun j hj ↦ (hx.lt_iff_lt.mp (hj.trans_lt hb)).le⟩) (hbelow z)
  refine ⟨i, hi, lt_of_not_ge ?_⟩
  intro hnext
  have := hmax (i + 1) hnext
  omega

private theorem integerSequence_homeomorph
    (x y : ℤ → ℝ) (hx : StrictMono x) (hy : StrictMono y)
    (hxc : ∀ z : ℝ, ∃ i : ℤ, x i ≤ z ∧ z < x (i + 1))
    (hyc : ∀ z : ℝ, ∃ i : ℤ, y i ≤ z ∧ z < y (i + 1)) :
    ∃ H : ℝ ≃ₜ ℝ, StrictMono H ∧ ∀ i : ℤ, H (x i) = y i := by
  classical
  let index : ℝ → ℤ := fun z ↦ Classical.choose (hxc z)
  have hindex (z : ℝ) : x (index z) ≤ z ∧ z < x (index z + 1) :=
    Classical.choose_spec (hxc z)
  have hindex_eq (z : ℝ) (i : ℤ) (hi : x i ≤ z ∧ z < x (i + 1)) :
      index z = i := by
    have h₁ : index z < i + 1 := hx.lt_iff_lt.mp ((hindex z).1.trans_lt hi.2)
    have h₂ : i < index z + 1 := hx.lt_iff_lt.mp (hi.1.trans_lt (hindex z).2)
    omega
  let affine : ℤ → ℝ → ℝ := fun i z ↦
    y i + ((y (i + 1) - y i) / (x (i + 1) - x i)) * (z - x i)
  have hdx (i : ℤ) : 0 < x (i + 1) - x i := sub_pos.mpr (hx (by omega))
  have hdy (i : ℤ) : 0 < y (i + 1) - y i := sub_pos.mpr (hy (by omega))
  have hslope (i : ℤ) :
      0 < (y (i + 1) - y i) / (x (i + 1) - x i) := div_pos (hdy i) (hdx i)
  have hleft (i : ℤ) : affine i (x i) = y i := by simp [affine]
  have hright (i : ℤ) : affine i (x (i + 1)) = y (i + 1) := by
    dsimp [affine]
    rw [div_mul_cancel₀ _ (ne_of_gt (hdx i))]
    ring
  have haffineMono (i : ℤ) : StrictMono (affine i) := by
    intro z w hzw
    simpa [affine, add_comm] using add_lt_add_left
      (mul_lt_mul_of_pos_left (sub_lt_sub_right hzw (x i)) (hslope i)) (y i)
  let g : ℝ → ℝ := fun z ↦ affine (index z) z
  have hhalf (z : ℝ) (i : ℤ) (hi : x i ≤ z ∧ z < x (i + 1)) :
      g z = affine i z := by
    dsimp only [g]
    rw [hindex_eq z i hi]
  have hknots (i : ℤ) : g (x i) = y i := by
    rw [hhalf (x i) i ⟨le_rfl, hx (by omega)⟩, hleft]
  have hcell (z : ℝ) (i : ℤ) (hi : x i ≤ z ∧ z ≤ x (i + 1)) :
      g z = affine i z := by
    rcases hi.2.eq_or_lt with heq | hlt
    · rw [heq, hknots, hright]
    · exact hhalf z i ⟨hi.1, hlt⟩
  have hbnds (z : ℝ) : y (index z) ≤ g z ∧ g z < y (index z + 1) := by
    constructor
    · rw [← hleft (index z)]
      exact (haffineMono (index z)).monotone (hindex z).1
    · rw [← hright (index z)]
      exact haffineMono (index z) (hindex z).2
  have hgmono : StrictMono g := by
    intro z w hzw
    have hij : index z ≤ index w := by
      by_contra hnot
      have hstep : index w + 1 ≤ index z := by omega
      have := (hx.monotone hstep).trans ((hindex z).1.trans hzw.le)
      exact (not_le_of_gt (hindex w).2) this
    rcases hij.eq_or_lt with heq | hlt
    · change affine (index z) z < affine (index w) w
      rw [heq]
      exact haffineMono (index w) hzw
    · calc
        g z < y (index z + 1) := (hbnds z).2
        _ ≤ y (index w) := hy.monotone (by omega)
        _ ≤ g w := (hbnds w).1
  have hgsurj : Function.Surjective g := by
    intro w
    obtain ⟨i, hlo, hhi⟩ := hyc w
    let r : ℝ := (w - y i) / (y (i + 1) - y i)
    have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hlo) (hdy i).le
    have hr1 : r < 1 := (div_lt_one (hdy i)).mpr (by linarith)
    let z : ℝ := x i + r * (x (i + 1) - x i)
    have hz : x i ≤ z ∧ z ≤ x (i + 1) := by
      dsimp only [z]
      constructor <;> nlinarith [hdx i]
    refine ⟨z, ?_⟩
    rw [hcell z i hz]
    dsimp [affine, z, r]
    field_simp [ne_of_gt (hdx i), ne_of_gt (hdy i)]
    ring
  let e : ℝ ≃o ℝ := hgmono.orderIsoOfSurjective g hgsurj
  exact ⟨e.toHomeomorph, e.strictMono, hknots⟩

private theorem translatedVertexHomeomorph_exists :
    ∀ (C : ApproximationContext.{0}) (X : PeriodicVerticalCarrier)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    C.target = X.carrier →
    Tiling.AxisParallel.TilesOn C.region C.centres C.target →
    HasFiniteHorizontalComplexity C.centres →
    PreservesHorizontalTranslatedVertexSigns C phi →
    ControlsHorizontalTranslatedVertexDistances C phi →
      ∃ H : ℝ ≃ₜ ℝ, StrictMono H ∧
        ∀ (v : C.region.vertices) (t : C.centres),
          H (v.1 + (t : Tiling.Plane)).re =
            (mapPoint phi (C.vertexPoint v.1 v.2) +
              mapPoint phi (C.centrePoint t.1 t.2)).re := by
  intro C X phi htarget hTile hFHC hSigns hDistances
  classical
  let A : Set ℝ := horizontalTranslatedVertices C.region C.centres
  have hAflc : HasFLC A := by
    dsimp only [A]
    rw [horizontalTranslatedVertices_eq_projection_add_vertices]
    exact hFHC.add_finset (C.region.vertexFinset.image Complex.re)
  obtain ⟨delta, hdelta, hseparated⟩ := hAflc.uniformlyDiscrete
  have hDense : ∃ L : ℝ, 0 < L ∧ ∀ z : ℝ, ∃ a ∈ A, |a - z| < L :=
    translatedVertices_horizontal_relativelyDense C X htarget hTile
  have horder : Nonempty (HorizontalOrderData A) := by
    apply delone_has_integerOrderData
    · refine ⟨delta, hdelta, ?_⟩
      intro a ha b hb hab
      simpa only [Real.dist_eq] using hseparated a ha b hb hab
    · exact hDense
    · exact horizontalBoundedDifferences_finite hFHC
  let order : HorizontalOrderData A := Classical.choice horder
  have hrep (i : ℤ) : ∃ v : C.region.vertices, ∃ t : C.centres,
      order.point i = (v.1 + (t : Tiling.Plane)).re := by
    have hiA : order.point i ∈ A := by
      exact order.point_range.subset (Set.mem_range_self i)
    obtain ⟨v, hv, t, ht, hit⟩ := hiA
    exact ⟨⟨v, hv⟩, ⟨t, ht⟩, hit⟩
  have hpointMem (i : ℤ) : order.point i ∈ C.coordinateSpace := by
    obtain ⟨v, t, hi⟩ := hrep i
    rw [hi, Complex.add_re]
    exact C.coordinateSpace.add_mem
      (C.vertex_re_mem v.1 v.2) (C.centre_re_mem t.1 t.2)
  let lift : ℤ → C.coordinateSpace := fun i ↦ ⟨order.point i, hpointMem i⟩
  let y : ℤ → ℝ := fun i ↦ mapScalar phi (lift i)
  have hmapAt (v : C.region.vertices) (t : C.centres) (i : ℤ)
      (hi : order.point i = (v.1 + (t : Tiling.Plane)).re) :
      y i = (mapPoint phi (C.vertexPoint v.1 v.2) +
        mapPoint phi (C.centrePoint t.1 t.2)).re := by
    have hlift : lift i =
        ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ +
          ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
      apply Subtype.ext
      simp [lift, hi, Complex.add_re]
    dsimp only [y]
    rw [hlift]
    change ((phi (_ + _) : ℚ) : ℝ) = _
    rw [map_add, Rat.cast_add]
    simp [mapPoint, mapScalar, ApproximationContext.vertexPoint,
      ApproximationContext.centrePoint]
  have hy : StrictMono y := by
    intro i j hij
    obtain ⟨v, s, hi⟩ := hrep i
    obtain ⟨w, t, hj⟩ := hrep j
    have hsign : Real.sign (order.point j - order.point i) =
        Real.sign (y j - y i) := by
      rw [hi, hj, hmapAt v s i hi, hmapAt w t j hj]
      exact hSigns v w s t
    rw [Real.sign_of_pos (sub_pos.mpr (order.point_strictMono hij))] at hsign
    rcases lt_trichotomy (y i) (y j) with hlt | heq | hgt
    · exact hlt
    · simp [heq] at hsign
    · rw [Real.sign_of_neg (sub_neg.mpr hgt)] at hsign
      norm_num at hsign
  have hdist (i j : ℤ) :
      (1 / 2 : ℝ) * |order.point j - order.point i| ≤ |y j - y i| := by
    obtain ⟨v, s, hi⟩ := hrep i
    obtain ⟨w, t, hj⟩ := hrep j
    rw [hi, hj, hmapAt v s i hi, hmapAt w t j hj]
    exact (hDistances v w s t).1
  obtain ⟨L, hL, hdense⟩ := hDense
  have hbelow (z : ℝ) : ∃ i : ℤ, order.point i ≤ z := by
    obtain ⟨a, ha, hbound⟩ := hdense (z - L)
    obtain ⟨i, rfl⟩ : ∃ i, order.point i = a := order.point_range.symm.subset ha
    refine ⟨i, ?_⟩
    have := (abs_lt.mp hbound).2
    linarith
  have habove (z : ℝ) : ∃ i : ℤ, z < order.point i := by
    obtain ⟨a, ha, hbound⟩ := hdense (z + L)
    obtain ⟨i, rfl⟩ : ∃ i, order.point i = a := order.point_range.symm.subset ha
    refine ⟨i, ?_⟩
    have := (abs_lt.mp hbound).1
    linarith
  have hybelow (z : ℝ) : ∃ i : ℤ, y i ≤ z := by
    obtain ⟨i, hi⟩ := hbelow (order.point 0 - 2 * |z - y 0| - 1)
    have hi0 : order.point i < order.point 0 := by
      nlinarith [abs_nonneg (z - y 0)]
    have hiy : y i < y 0 := hy (order.point_strictMono.lt_iff_lt.mp hi0)
    have hd := hdist 0 i
    rw [abs_of_neg (sub_neg.mpr hi0), abs_of_neg (sub_neg.mpr hiy)] at hd
    refine ⟨i, ?_⟩
    nlinarith [neg_le_abs (z - y 0)]
  have hyabove (z : ℝ) : ∃ i : ℤ, z < y i := by
    obtain ⟨i, hi⟩ := habove (order.point 0 + 2 * |z - y 0| + 1)
    have h0i : order.point 0 < order.point i := by
      nlinarith [abs_nonneg (z - y 0)]
    have hiy : y 0 < y i := hy (order.point_strictMono.lt_iff_lt.mp h0i)
    have hd := hdist 0 i
    rw [abs_of_pos (sub_pos.mpr h0i), abs_of_pos (sub_pos.mpr hiy)] at hd
    refine ⟨i, ?_⟩
    nlinarith [le_abs_self (z - y 0)]
  obtain ⟨H, hH, hknots⟩ := integerSequence_homeomorph order.point y
    order.point_strictMono hy
    (integerSequence_covers order.point order.point_strictMono hbelow habove)
    (integerSequence_covers y hy hybelow hyabove)
  refine ⟨H, hH, ?_⟩
  intro v t
  have hvt : (v.1 + (t : Tiling.Plane)).re ∈ A :=
    ⟨v.1, v.2, t.1, t.2, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, order.point i = (v.1 + (t : Tiling.Plane)).re :=
    order.point_range.symm.subset hvt
  rw [← hi, hknots i]
  exact hmapAt v t i hi


end Tiling.AxisParallel.Terminal



namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Continuous

private def ConsecutiveIn (A : Set ℝ) (a b : ℝ) : Prop :=
  a ∈ A ∧ b ∈ A ∧ a < b ∧ Ioo a b ∩ A = ∅

private theorem gap_subset_or_subset_exterior
    {A : Set ℝ} (hA : IsOpen A) {a b : ℝ}
    (hgap : Disjoint (Ioo a b) (frontier A)) :
    Ioo a b ⊆ A ∨ Ioo a b ⊆ (closure A)ᶜ := by
  apply isPreconnected_Ioo.subset_or_subset hA isClosed_closure.isOpen_compl
  · exact disjoint_compl_right.mono_right
      (compl_subset_compl.mpr subset_closure)
  · intro x hx
    by_cases hxcl : x ∈ closure A
    · left
      by_contra hxA
      apply Set.disjoint_left.mp hgap hx
      rw [frontier, hA.interior_eq]
      exact ⟨hxcl, hxA⟩
    · exact Or.inr hxcl

private theorem totalBoundary_labelTrichotomy
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier)
    {a b : ℝ} (h : ConsecutiveIn (totalSlabBoundary K T X) a b) :
    (Ioo a b ⊆ X.baseᶜ) ∨
    (∃ P : VerticalPlate K T,
      ¬ IsVerticalColumn P ∧ Ioo a b ⊆ P.base) ∨
    Ioo a b ⊆ aggregateColumnBase K T := by
  have havoid {A : Set ℝ} (hA : frontier A ⊆ totalSlabBoundary K T X) :
      Disjoint (Ioo a b) (frontier A) := by
    apply Set.disjoint_left.mpr
    intro x hx hxA
    have hxB : x ∈ Ioo a b ∩ totalSlabBoundary K T X := ⟨hx, hA hxA⟩
    rw [h.2.2.2] at hxB
    exact hxB
  have havoidX : Disjoint (Ioo a b) (frontier X.base) :=
    havoid (fun _ hx ↦ Or.inl (Or.inl hx))
  rcases gap_subset_or_subset_exterior X.base_open havoidX with hinside | houtside
  · right
    have hregularCarrier : interior (closure X.carrier) = X.carrier := by
      change interior (closure (Complex.re ⁻¹' X.base)) = Complex.re ⁻¹' X.base
      rw [Complex.closure_preimage_re, Complex.interior_preimage_re, X.base_regular]
    have hsupport : regularSupport K T = X.carrier :=
      regularSupport_eq_of_tilesOn (X.base_open.preimage Complex.continuous_re)
        hregularCarrier hTile
    let m : ℝ := (a + b) / 2
    have hm : m ∈ Ioo a b := by dsimp [m]; constructor <;> linarith [h.2.2.1]
    have hmcl : m ∈ closure (Complex.re '' openUnion K T) := by
      have hmsupp : (m : ℂ) ∈ regularSupport K T := by
        rw [hsupport]
        exact hinside hm
      have hmcl' : (m : ℂ) ∈ closure (openUnion K T) := interior_subset hmsupp
      exact image_closure_subset_closure_image Complex.continuous_re
        ⟨(m : ℂ), hmcl', by simp⟩
    obtain ⟨y, hygap, z, hzraw, hy⟩ :=
      mem_closure_iff.mp hmcl (Ioo a b) isOpen_Ioo hm
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hzraw
    obtain ⟨t, hzt⟩ := hzraw
    let P : VerticalPlate K T := VerticalPlate.ofCentre (K := K) t
    have htP : (t : Tiling.Plane) ∈ P.centres :=
      VerticalPlate.mem_centres_ofCentre t
    have hzP : z ∈ P.support := by
      change z ∈ regularSupport K P.centres
      apply interior_maximal subset_closure
        (isOpen_iUnion fun q : P.centres ↦
          (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _ isOpen_interior)
      exact Set.mem_iUnion.mpr ⟨⟨t, htP⟩, hzt⟩
    have hyP : y ∈ P.base := ⟨z, hzP, hy⟩
    by_cases hcolumn : IsVerticalColumn P
    · right
      have htcol : (t : Tiling.Plane) ∈ verticalColumnCentres K T :=
        Set.mem_iUnion.mpr ⟨⟨P, hcolumn⟩, htP⟩
      have hzcol : z ∈ regularSupport K (verticalColumnCentres K T) := by
        apply interior_maximal subset_closure
          (isOpen_iUnion fun q : verticalColumnCentres K T ↦
            (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _ isOpen_interior)
        exact Set.mem_iUnion.mpr ⟨⟨t, htcol⟩, hzt⟩
      have hycol : y ∈ aggregateColumnBase K T := ⟨z, hzcol, hy⟩
      have hcolopen : IsOpen (aggregateColumnBase K T) := by
        rw [aggregateColumnBase_regularizedProjection X hTile]
        exact isOpen_interior
      rcases gap_subset_or_subset_exterior hcolopen
          (havoid (fun _ hx ↦ Or.inr hx)) with hcol | hexterior
      · exact hcol
      · exact False.elim (hexterior hygap (subset_closure hycol))
    · left
      refine ⟨P, hcolumn, ?_⟩
      have hPopen : IsOpen P.base := by
        rw [verticalPlateBase_regularizedProjection X hTile P]
        exact isOpen_interior
      have hPfront : frontier P.base ⊆ totalSlabBoundary K T X := by
        intro x hx
        exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨P, hcolumn⟩, hx⟩))
      rcases gap_subset_or_subset_exterior hPopen (havoid hPfront) with hP | hexterior
      · exact hP
      · exact False.elim (hexterior hygap (subset_closure hyP))
  · exact Or.inl fun x hx hxX ↦ houtside hx (subset_closure hxX)

private theorem aggregateColumnSupport_eq_cylinder
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier) (hTile : TilesOn K T X.carrier) :
    regularSupport K (verticalColumnCentres K T) =
      Complex.re ⁻¹' aggregateColumnBase K T := by
  have hsupport := carrierAggregate_support_regularizedTarget X hTile
  have himage : ∀ A : Set ℝ, Complex.re '' (Complex.re ⁻¹' A) = A := by
    intro A
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨(x : ℂ), hx, by simp⟩
  rw [aggregateColumnBase_eq, hsupport, himage]

private theorem cylinderSupport_frontier_fromVertices
    {K : Region} {T S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements T))
    (hS : S ⊆ T) {A : Set ℝ}
    (hsupport : regularSupport K S = Complex.re ⁻¹' A) :
    frontier A ⊆ horizontalTranslatedVertices K T := by
  intro x hx
  have hcountT : T.Countable := (IsPacking.locallyFinite_centres hpacking).2
  have hcountV : K.vertices.Countable := by
    rw [← K.coe_vertexFinset]
    exact K.vertexFinset.finite_toSet.countable
  let _ : Countable T := hcountT.to_subtype
  let _ : Countable K.vertices := hcountV.to_subtype
  let levels : Set ℝ := Set.range fun p : T × K.vertices ↦
    ((p.1 : Tiling.Plane) + p.2.1).im
  have hlevels : levels.Countable := Set.countable_range _
  have hdiff : (Ioo (0 : ℝ) 1 \ levels).Nonempty := by
    by_contra hne
    have hsub : Ioo (0 : ℝ) 1 ⊆ levels := by
      intro q hq
      by_contra hqbad
      exact hne ⟨q, hq, hqbad⟩
    have hzero : MeasureTheory.volume (Ioo (0 : ℝ) 1) = 0 :=
      MeasureTheory.measure_mono_null hsub (hlevels.measure_zero MeasureTheory.volume)
    exact (isOpen_Ioo.measure_ne_zero MeasureTheory.volume
      ⟨(1 / 2 : ℝ), by norm_num⟩) hzero
  obtain ⟨q, -, hq⟩ := hdiff
  let z : Tiling.Plane := Complex.mk x q
  have hzfront : z ∈ frontier (regularSupport K S) := by
    rw [hsupport]
    change z ∈ frontier ({w : Tiling.Plane | w.re ∈ A})
    rw [frontier_verticalCylinder]
    exact hx
  have hSpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) := by
    intro s hs t ht hst
    exact hpacking (hS hs) (hS ht) hst
  have hzcl : z ∈ closure (openUnion K S) := by
    have hsub : regularSupport K S ⊆ closure (openUnion K S) := interior_subset
    exact closure_minimal hsub isClosed_closure (frontier_subset_closure hzfront)
  rw [closure_openUnion_eq_iUnion_support hSpacking, Set.mem_iUnion] at hzcl
  obtain ⟨s, hzs⟩ := hzcl
  have hznot : z ∉ interior ((s : Tiling.Plane) +ᵥ K.support) := by
    intro hzint
    have hzraw : z ∈ openUnion K S := by
      apply Set.mem_iUnion.mpr
      refine ⟨s, ?_⟩
      change z ∈ (s : Tiling.Plane) +ᵥ interior K.support
      simpa only [interior_vadd] using hzint
    have hzsupport : z ∈ regularSupport K S := by
      apply interior_maximal subset_closure
        (isOpen_iUnion fun t : S ↦
          (Homeomorph.addLeft (t : Tiling.Plane)).isOpenMap _ isOpen_interior)
      exact hzraw
    exact Set.disjoint_left.mp disjoint_interior_frontier
      ((regularSupport_isRegularOpen K S).1.interior_eq.symm ▸ hzsupport) hzfront
  have hztile : z - (s : Tiling.Plane) ∈ frontier K.support := by
    have hzplaced : z ∈ frontier ((s : Tiling.Plane) +ᵥ K.support) :=
      ⟨subset_closure hzs, hznot⟩
    simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_eq_sub] using hzplaced
  rcases IntrinsicVertices.frontier_subset_vertexCoordinateGrid K hztile with hreal | himag
  · obtain ⟨v, hv, hvr⟩ := hreal
    rw [horizontalTranslatedVertices_eq]
    refine ⟨v, hv, s, hS s.2, ?_⟩
    change x - (s : Tiling.Plane).re = v.re at hvr
    simp only [Complex.add_re]
    linarith
  · obtain ⟨v, hv, hvi⟩ := himag
    apply False.elim (hq ?_)
    refine ⟨(⟨s, hS s.2⟩, ⟨v, hv⟩), ?_⟩
    change q - (s : Tiling.Plane).im = v.im at hvi
    simp only [Complex.add_im]
    linarith

private theorem slabCodeBoundaries_fromVertices
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier) (hTile : TilesOn K T X.carrier) :
    totalSlabBoundary K T X ⊆ horizontalTranslatedVertices K T := by
  have hcarrierRegular : interior (closure X.carrier) = X.carrier := by
    change interior (closure (Complex.re ⁻¹' X.base)) = Complex.re ⁻¹' X.base
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, X.base_regular]
  have hcarrierSupport : regularSupport K T = Complex.re ⁻¹' X.base :=
    regularSupport_eq_of_tilesOn (X.base_open.preimage Complex.continuous_re)
      hcarrierRegular hTile
  have hslab := (relativeCarrier_verticalPlates hTile
    (periodicVerticalCarrier_carrier_eq X) X.base_regular.symm
    (fun a b ↦ by
      simpa only [inter_comm] using hTile.verticalCylinder_frontier_locallyFinite
        X.base_open X.base_regular (Icc a b) isCompact_Icc)).1
  intro x hx
  rcases hx with (hxcarrier | hxplates) | hxcolumn
  · exact cylinderSupport_frontier_fromVertices hTile.2.1 Subset.rfl hcarrierSupport hxcarrier
  · obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hxplates
    have hPsub : P.1.centres ⊆ T := by rintro _ ⟨t, -, rfl⟩; exact t.2
    exact cylinderSupport_frontier_fromVertices hTile.2.1 hPsub (hslab P).2 hxP
  · have hcolsub : verticalColumnCentres K T ⊆ T := by
      intro z hz
      obtain ⟨P, ht⟩ := Set.mem_iUnion.mp hz
      obtain ⟨t, -, rfl⟩ := ht
      exact t.2
    exact cylinderSupport_frontier_fromVertices hTile.2.1 hcolsub
      (aggregateColumnSupport_eq_cylinder X hTile) hxcolumn

private theorem carrierBase_regularizedProjection
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier) (hTile : TilesOn K T X.carrier) :
    X.base = interior (closure (Complex.re '' openUnion K T)) := by
  have hcarrierRegular : interior (closure X.carrier) = X.carrier := by
    change interior (closure (Complex.re ⁻¹' X.base)) = Complex.re ⁻¹' X.base
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, X.base_regular]
  have hsupport : regularSupport K T = X.carrier :=
    regularSupport_eq_of_tilesOn (X.base_open.preimage Complex.continuous_re)
      hcarrierRegular hTile
  have hraw : openUnion K T ⊆ regularSupport K T := by
    apply interior_maximal subset_closure
    exact isOpen_iUnion fun t : T ↦
      (Homeomorph.addLeft (t : Tiling.Plane)).isOpenMap _ isOpen_interior
  have hprojection : Complex.re '' openUnion K T ⊆ X.base := by
    rintro x ⟨z, hz, rfl⟩
    have hzsupp := hraw hz
    rw [hsupport] at hzsupp
    exact hzsupp
  apply Subset.antisymm
  · apply interior_maximal _ X.base_open
    intro x hx
    have hxsupp : (x : ℂ) ∈ regularSupport K T := by
      rw [hsupport]
      exact hx
    exact image_closure_subset_closure_image Complex.continuous_re
      ⟨(x : ℂ), interior_subset hxsupp, by simp⟩
  · rw [← X.base_regular]
    exact interior_mono (closure_mono hprojection)

private theorem ConsecutiveIn.right_unique
    {B : Set ℝ} {a b c : ℝ}
    (hb : ConsecutiveIn B a b) (hc : ConsecutiveIn B a c) : b = c := by
  rcases lt_trichotomy b c with hbc | heq | hcb
  · have hmem : b ∈ Ioo a c ∩ B := ⟨⟨hb.2.2.1, hbc⟩, hb.2.1⟩
    rw [hc.2.2.2] at hmem
    exact False.elim hmem
  · exact heq
  · have hmem : c ∈ Ioo a b ∩ B := ⟨⟨hc.2.2.1, hcb⟩, hc.2.1⟩
    rw [hb.2.2.2] at hmem
    exact False.elim hmem

end Tiling.AxisParallel.Terminal


namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation Tiling.AxisParallel.Continuous

private theorem carrierApproximation_globalSigns :
    ∀ (C : ApproximationContext.{0}) (X : PeriodicVerticalCarrier),
    C.target = X.carrier →
    Tiling.AxisParallel.TilesOn C.region C.centres C.target →
    HasFiniteHorizontalComplexity C.centres →
      ∃ epsilon > 0, ∀ phi : C.coordinateSpace →ₗ[ℚ] ℚ,
        IsEpsilonApproximation C epsilon phi →
          PreservesHorizontalTranslatedVertexSigns C phi := by
  intro C X htarget hTile hFHC
  classical
  let A : Set ℝ := horizontalTranslatedVertices C.region C.centres
  have hAflc : HasFLC A := by
    dsimp only [A]
    rw [horizontalTranslatedVertices_eq_projection_add_vertices]
    exact hFHC.add_finset (C.region.vertexFinset.image Complex.re)
  obtain ⟨delta, hdelta, hseparated⟩ := hAflc.uniformlyDiscrete
  have horder : Nonempty (HorizontalOrderData A) := by
    apply delone_has_integerOrderData
    · refine ⟨delta, hdelta, ?_⟩
      intro a ha b hb hab
      simpa only [Real.dist_eq] using hseparated a ha b hb hab
    · exact translatedVertices_horizontal_relativelyDense C X htarget hTile
    · exact horizontalBoundedDifferences_finite hFHC
  let order : HorizontalOrderData A := Classical.choice horder
  have hpointMem (i : ℤ) : order.point i ∈ C.coordinateSpace := by
    have hiA : order.point i ∈ A := order.point_range.subset (Set.mem_range_self i)
    obtain ⟨v, hv, t, ht, hi⟩ := hiA
    rw [hi, Complex.add_re]
    exact C.coordinateSpace.add_mem (C.vertex_re_mem v hv) (C.centre_re_mem t ht)
  let lift : ℤ → C.coordinateSpace := fun i ↦ ⟨order.point i, hpointMem i⟩
  have hgapMem (g : ℝ) (hg : g ∈ order.gapAlphabet) : g ∈ C.coordinateSpace := by
    obtain ⟨i, hi⟩ := order.gap_complete g hg
    rw [hi]
    exact C.coordinateSpace.sub_mem (hpointMem (i + 1)) (hpointMem i)
  have hGnonempty : order.gapAlphabet.Nonempty :=
    ⟨order.point (0 + 1) - order.point 0, order.gap_mem 0⟩
  let gmin : ℝ := order.gapAlphabet.min' hGnonempty
  have hgmin : 0 < gmin :=
    order.gap_pos gmin (order.gapAlphabet.min'_mem hGnonempty)
  obtain ⟨epsilon, hepsilon, hcontrol⟩ :=
    approximation_uniformOnHorizontalAlphabet C order.gapAlphabet hgapMem (half_pos hgmin)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro phi hphi
  let gapLift : ↑order.gapAlphabet → C.coordinateSpace :=
    fun g ↦ ⟨(g : ℝ), hgapMem g g.2⟩
  have hgapLower (g : ↑order.gapAlphabet) :
      (1 / 2 : ℝ) * (g : ℝ) < mapScalar phi (gapLift g) := by
    have herr := (abs_lt.mp (hcontrol phi hphi (g : ℝ) g.2)).1
    have hminle : gmin ≤ (g : ℝ) := order.gapAlphabet.min'_le _ g.2
    change -(gmin / 2) < mapScalar phi (gapLift g) - (g : ℝ) at herr
    linarith
  have hgapUpper (g : ↑order.gapAlphabet) :
      mapScalar phi (gapLift g) < 2 * (g : ℝ) := by
    have herr := (abs_lt.mp (hcontrol phi hphi (g : ℝ) g.2)).2
    have hminle : gmin ≤ (g : ℝ) := order.gapAlphabet.min'_le _ g.2
    have hgpos := order.gap_pos (g : ℝ) g.2
    change mapScalar phi (gapLift g) - (g : ℝ) < gmin / 2 at herr
    linarith
  have hindexed := finitePositiveGaps_control_indexedDifferences C order phi lift
    (fun _ ↦ rfl) gapLift (fun _ ↦ rfl) hgapLower hgapUpper
  let y : ℤ → ℝ := fun i ↦ mapScalar phi (lift i)
  have hy : StrictMono y := by
    intro i j hij
    have hsource : 0 < order.point j - order.point i :=
      sub_pos.mpr (order.point_strictMono hij)
    have htarget := (hindexed i j hij).1
    change (1 / 2 : ℝ) * (order.point j - order.point i) < y j - y i at htarget
    linarith
  have hmapAt (v : C.region.vertices) (t : C.centres) (i : ℤ)
      (hi : order.point i = (v.1 + (t : Tiling.Plane)).re) :
      y i = (mapPoint phi (C.vertexPoint v.1 v.2) +
        mapPoint phi (C.centrePoint t.1 t.2)).re := by
    have hlift : lift i =
        ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ +
          ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
      apply Subtype.ext
      simp [lift, hi, Complex.add_re]
    dsimp only [y]
    rw [hlift]
    change ((phi (_ + _) : ℚ) : ℝ) = _
    rw [map_add, Rat.cast_add]
    simp [mapPoint, mapScalar, ApproximationContext.vertexPoint,
      ApproximationContext.centrePoint]
  intro v w s t
  have hvs : (v.1 + (s : Tiling.Plane)).re ∈ A := ⟨v.1, v.2, s.1, s.2, rfl⟩
  have hwt : (w.1 + (t : Tiling.Plane)).re ∈ A := ⟨w.1, w.2, t.1, t.2, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, order.point i = (v.1 + (s : Tiling.Plane)).re :=
    order.point_range.symm.subset hvs
  obtain ⟨j, hj⟩ : ∃ j, order.point j = (w.1 + (t : Tiling.Plane)).re :=
    order.point_range.symm.subset hwt
  rw [← hi, ← hj, ← hmapAt v s i hi, ← hmapAt w t j hj]
  rcases lt_trichotomy i j with hij | heq | hji
  · rw [Real.sign_of_pos (sub_pos.mpr (order.point_strictMono hij)),
      Real.sign_of_pos (sub_pos.mpr (hy hij))]
  · subst j
    simp
  · rw [Real.sign_of_neg (sub_neg.mpr (order.point_strictMono hji)),
      Real.sign_of_neg (sub_neg.mpr (hy hji))]

end Tiling.AxisParallel.Terminal


namespace Tiling.AxisParallel.Terminal

open Filter MeasureTheory
open scoped _root_.Topology
open Tiling.AxisParallel Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Foundations.FilledSliceChains

private theorem cylinder_verticalSlice_ae
    {K : Region} {T : Set Tiling.Plane} {B : Set ℝ}
    (hTile : TilesOn K T (Complex.re ⁻¹' B)) :
    ∀ᵐ q : ℝ ∂volume, q ∈ B →
      ∀ᵐ y : ℝ ∂volume,
        slicePoint Axis.vertical q y ∈ openUnion K T := by
  have hpull := Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae
    hTile.2.2
  have hslices := MeasureTheory.Measure.ae_ae_of_ae_prod
    (μ := volume) (ν := volume) hpull
  filter_upwards [hslices] with q hq
  intro hqB
  filter_upwards [hq] with y hy
  have heq : slicePoint Axis.vertical q y =
      Complex.measurableEquivRealProd.symm (q, y) := by
    apply Complex.ext <;> simp [slicePoint]
  rw [heq, openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
  exact hy.mp hqB

private theorem horizontalPoint_mem_openSegment
    {a b : Tiling.Plane} (hne : a.re ≠ b.re) (hheight : a.im = b.im)
    {q : ℝ} (hq : q ∈ Ioo (min a.re b.re) (max a.re b.re)) :
    slicePoint Axis.vertical q a.im ∈ openSegment ℝ a b := by
  have hq' : q ∈ openSegment ℝ a.re b.re := by
    rwa [openSegment_eq_Ioo' hne]
  rw [openSegment_eq_image] at hq' ⊢
  obtain ⟨r, hr, hq⟩ := hq'
  refine ⟨r, hr, ?_⟩
  apply Complex.ext
  · simpa [slicePoint] using hq
  · simp only [slicePoint, Complex.add_im, Complex.ofReal_im, zero_add,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.I_re, mul_zero, add_zero, Complex.smul_im, smul_eq_mul]
    rw [hheight]
    ring

private theorem horizontalSide_sliceEndpoint_of_packing
    {K : Region} {T : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements T))
    (v w : K.vertices) (s : T) {q : ℝ}
    (hvw : v.1 ≠ w.1) (hheight : v.1.im = w.1.im)
    (hedge : openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices)
    (hq : q ∈ Ioo (min v.1.re w.1.re + s.1.re)
      (max v.1.re w.1.re + s.1.re))
    (hcover : ∀ᵐ y : ℝ ∂volume,
      slicePoint Axis.vertical q y ∈ openUnion K T) :
    (v.1 + s.1).im ∈ sliceEndpointSet K T Axis.vertical q := by
  let p : Tiling.Plane := slicePoint Axis.vertical q (v.1 + s.1).im
  have hpseg : p ∈ openSegment ℝ (v.1 + s.1) (w.1 + s.1) := by
    apply horizontalPoint_mem_openSegment
    · intro h
      exact hvw (Complex.ext (add_right_cancel h) hheight)
    · simp only [Complex.add_im, hheight]
    · simpa [Complex.add_re, min_add_add_right, max_add_add_right] using hq
  have hpminus : p - s.1 ∈ openSegment ℝ v.1 w.1 := by
    rw [show v.1 + s.1 = s.1 +ᵥ v.1 by simp [add_comm],
      show w.1 + s.1 = s.1 +ᵥ w.1 by simp [add_comm],
      ← vadd_openSegment ℝ] at hpseg
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hpseg
  have hpfront : p ∈ frontier (s.1 +ᵥ K.support) := by
    simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_eq_sub] using (hedge hpminus).1
  have hpclosure : p ∈ closure (s.1 +ᵥ K.openCarrier) := by
    rw [closure_vadd, show closure K.openCarrier = K.support from
      K.isPolygonal.closure_interior]
    exact (K.isPolygonal.isClosed.vadd s.1).frontier_subset hpfront
  have hpnot : p ∉ openUnion K T := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    rintro ⟨t, hpt⟩
    by_cases hts : t = s
    · subst t
      exact hpfront.2 (by rwa [interior_vadd])
    · have hne : t.1 ≠ s.1 := fun h => hts (Subtype.ext h)
      have hd := (isPacking_iff_openCarrier_disjoint K T).mp hpacking t.2 s.2 hne
      obtain ⟨z, hzt, hzs⟩ := mem_closure_iff.mp hpclosure
        (t.1 +ᵥ K.openCarrier) (isOpen_interior.vadd _) hpt
      exact Set.disjoint_left.mp hd hzt hzs
  let U : Set ℝ := {y | slicePoint Axis.vertical q y ∈ openUnion K T}
  have hUdense : Dense U := (volume : Measure ℝ).dense_of_ae hcover
  change (v.1 + s.1).im ∈ frontier U
  refine ⟨?_, ?_⟩
  · rw [hUdense.closure_eq]
    exact Set.mem_univ _
  · intro hy
    have hyU : (v.1 + s.1).im ∈ U := interior_subset hy
    exact hpnot hyU

private theorem openUnion_subset_cylinder
    {K : Region} {T : Set Tiling.Plane} {B : Set ℝ}
    (hB : IsOpen B) (hBreg : interior (closure B) = B)
    (hTile : TilesOn K T (Complex.re ⁻¹' B)) :
    openUnion K T ⊆ Complex.re ⁻¹' B := by
  have hreg : regularSupport K T = Complex.re ⁻¹' B :=
    regularSupport_eq_of_tilesOn (hB.preimage Complex.continuous_re)
      (by rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hBreg]) hTile
  rw [← hreg]
  apply IsOpen.subset_interior_closure
  exact isOpen_iUnion fun s => isOpen_interior.vadd s.1

private theorem sideOverlap_inter_base_nonempty
    {K : Region} {T : Set Tiling.Plane} {B : Set ℝ}
    (hB : IsOpen B) (hBreg : interior (closure B) = B)
    (hTile : TilesOn K T (Complex.re ⁻¹' B))
    (v v' w w' : K.vertices) (s t : T)
    (hvv : v.1 ≠ v'.1) (hheight : v.1.im = v'.1.im)
    (hside : openSegment ℝ v.1 v'.1 ⊆ frontier K.support \ K.vertices)
    (hoverlap : (Ioo (min v.1.re v'.1.re + s.1.re)
      (max v.1.re v'.1.re + s.1.re) ∩
      Ioo (min w.1.re w'.1.re + t.1.re)
        (max w.1.re w'.1.re + t.1.re)).Nonempty) :
    ((Ioo (min v.1.re v'.1.re + s.1.re)
      (max v.1.re v'.1.re + s.1.re) ∩
      Ioo (min w.1.re w'.1.re + t.1.re)
        (max w.1.re w'.1.re + t.1.re)) ∩ B).Nonempty := by
  obtain ⟨q, hqv, hqw⟩ := hoverlap
  have hpseg : slicePoint Axis.vertical q (v.1 + s.1).im ∈
      openSegment ℝ (v.1 + s.1) (v'.1 + s.1) := by
    apply horizontalPoint_mem_openSegment
    · intro h
      exact hvv (Complex.ext (add_right_cancel h) hheight)
    · simp only [Complex.add_im, hheight]
    · simpa [Complex.add_re, min_add_add_right, max_add_add_right] using hqv
  have hpminus : slicePoint Axis.vertical q (v.1 + s.1).im - s.1 ∈
      openSegment ℝ v.1 v'.1 := by
    rw [show v.1 + s.1 = s.1 +ᵥ v.1 by simp [add_comm],
      show v'.1 + s.1 = s.1 +ᵥ v'.1 by simp [add_comm],
      ← vadd_openSegment ℝ] at hpseg
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub, Complex.add_im, add_comm] using hpseg
  have hpclosure : slicePoint Axis.vertical q (v.1 + s.1).im ∈
      closure (openUnion K T) := by
    rw [closure_openUnion_eq_iUnion_support hTile.2.1, Set.mem_iUnion]
    refine ⟨s, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [vadd_eq_add, neg_add_eq_sub] using
      K.isPolygonal.isClosed.frontier_subset (hside hpminus).1
  have hqcl : q ∈ closure B := by
    have hp := closure_mono (openUnion_subset_cylinder hB hBreg hTile) hpclosure
    rw [Complex.closure_preimage_re] at hp
    simpa [slicePoint] using hp
  obtain ⟨r, hrI, hrB⟩ := mem_closure_iff.mp hqcl
    (Ioo (min v.1.re v'.1.re + s.1.re) (max v.1.re v'.1.re + s.1.re) ∩
      Ioo (min w.1.re w'.1.re + t.1.re) (max w.1.re w'.1.re + t.1.re))
    (isOpen_Ioo.inter isOpen_Ioo) ⟨hqv, hqw⟩
  exact ⟨r, hrI, hrB⟩

private theorem sum_finite_gaps (n : ℕ) (x : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (x i.succ - x i.castSucc) = x (Fin.last n) - x 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun i => x i.succ)
      simp only [Fin.succ_last, Fin.succ_zero_eq_one] at htail
      have htail' : ∑ i : Fin n, (x i.succ.succ - x i.succ.castSucc) =
          x (Fin.last (n + 1)) - x 1 := by
        rw [← htail]
        apply Finset.sum_congr rfl
        intro i _
        congr 2
      rw [htail']
      have hs0 : (Fin.succ 0 : Fin (n + 2)) = 1 := Fin.ext rfl
      have hc0 : (Fin.castSucc 0 : Fin (n + 2)) = 0 := Fin.ext rfl
      rw [hs0, hc0]
      ring

private theorem properCarrier_verticalGapChain
    {K : Region} {T : Set Tiling.Plane} {B : Set ℝ}
    (hB : IsOpen B) (hBreg : interior (closure B) = B)
    (hTile : TilesOn K T (Complex.re ⁻¹' B))
    (v v' w w' : K.vertices) (s t : T)
    (hvv : v.1 ≠ v'.1) (hww : w.1 ≠ w'.1)
    (hvheight : v.1.im = v'.1.im) (hwheight : w.1.im = w'.1.im)
    (hvside : openSegment ℝ v.1 v'.1 ⊆ frontier K.support \ K.vertices)
    (hwside : openSegment ℝ w.1 w'.1 ⊆ frontier K.support \ K.vertices)
    (hoverlap : (Ioo (min v.1.re v'.1.re + s.1.re)
      (max v.1.re v'.1.re + s.1.re) ∩
      Ioo (min w.1.re w'.1.re + t.1.re)
        (max w.1.re w'.1.re + t.1.re)).Nonempty)
    (horder : (v.1 + s.1).im < (w.1 + t.1).im) :
    ∃ n : ℕ, 0 < n ∧ ∃ a b : Fin n → K.vertices,
      (∀ i, (a i).1.im < (b i).1.im) ∧
      (w.1 + t.1).im - (v.1 + s.1).im =
        ∑ i : Fin n, ((b i).1.im - (a i).1.im) := by
  classical
  let U := (Ioo (min v.1.re v'.1.re + s.1.re)
      (max v.1.re v'.1.re + s.1.re) ∩
      Ioo (min w.1.re w'.1.re + t.1.re)
        (max w.1.re w'.1.re + t.1.re)) ∩ B
  have hUne : U.Nonempty := sideOverlap_inter_base_nonempty
    hB hBreg hTile v v' w w' s t hvv hvheight hvside hoverlap
  have hUopen : IsOpen U := (isOpen_Ioo.inter isOpen_Ioo).inter hB
  have hevent := (cylinder_verticalSlice_ae hTile).and
    (genericSliceChain_betweenEndpoints_of_local_ae K T hTile.2.1 Axis.vertical)
  obtain ⟨q, hqU, hq⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
    (hUopen.measure_ne_zero volume hUne) (hevent.filter_mono ae_restrict_le)
  have hcover := hq.1 hqU.2
  have hvend := horizontalSide_sliceEndpoint_of_packing hTile.2.1
    v v' s hvv hvheight hvside hqU.1.1 hcover
  have hwend := horizontalSide_sliceEndpoint_of_packing hTile.2.1
    w w' t hww hwheight hwside hqU.1.2 hcover
  obtain ⟨n, hn, x, owner, hx0, hxlast, hfilled, _⟩ := hq.2 _ hvend _ hwend horder
    (by filter_upwards [hcover] with y hy; exact fun _ => hy)
  have hpiece : ∀ i : Fin n, ∃ a b : K.vertices,
      x i.castSucc = (a.1 + (owner i).1).im ∧
      x i.succ = (b.1 + (owner i).1).im ∧ a.1.im < b.1.im := by
    intro i
    obtain ⟨a, b, ha, hb, hxa, hxb, hpos, _⟩ := hfilled.2 i
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hxa, hxb,
      by simpa [Axis.coord, Complex.sub_im] using hpos⟩
  let a : Fin n → K.vertices := fun i => (hpiece i).choose
  let b : Fin n → K.vertices := fun i => (hpiece i).choose_spec.choose
  have hab (i : Fin n) :
      x i.castSucc = ((a i).1 + (owner i).1).im ∧
      x i.succ = ((b i).1 + (owner i).1).im ∧ (a i).1.im < (b i).1.im :=
    (hpiece i).choose_spec.choose_spec
  refine ⟨n, hn, a, b, fun i => (hab i).2.2, ?_⟩
  rw [← hx0, ← hxlast, ← sum_finite_gaps n x]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hab i).1, (hab i).2.1]
  simp only [Complex.add_im]
  ring

private theorem mappedVerticalDifference_eq_sum
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (imageCenters : C.centres → Tiling.Plane)
    (hImage : ∀ t, imageCenters t = mapPoint phi (C.centrePoint t.1 t.2))
    (v w : C.region.vertices) (s t : C.centres)
    {n : ℕ} (a b : Fin n → C.region.vertices)
    (hsum : (w.1 + t.1).im - (v.1 + s.1).im =
      ∑ i : Fin n, ((b i).1.im - (a i).1.im)) :
    (mapPoint phi (C.vertexPoint w.1 w.2) + imageCenters t).im -
        (mapPoint phi (C.vertexPoint v.1 v.2) + imageCenters s).im =
      ∑ i : Fin n,
        ((mapPoint phi (C.vertexPoint (b i).1 (b i).2)).im -
          (mapPoint phi (C.vertexPoint (a i).1 (a i).2)).im) := by
  have hlinear :
      (⟨w.1.im, C.vertex_im_mem w.1 w.2⟩ : C.coordinateSpace) +
          ⟨t.1.im, C.centre_im_mem t.1 t.2⟩ -
        (⟨v.1.im, C.vertex_im_mem v.1 v.2⟩ +
          ⟨s.1.im, C.centre_im_mem s.1 s.2⟩) =
      ∑ i : Fin n,
        ((⟨(b i).1.im, C.vertex_im_mem (b i).1 (b i).2⟩ : C.coordinateSpace) -
          ⟨(a i).1.im, C.vertex_im_mem (a i).1 (a i).2⟩) := by
    apply Subtype.ext
    simpa only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_sum,
      Complex.add_im] using hsum
  have hmapReal := congrArg (fun q : ℚ => (q : ℝ)) (congrArg phi hlinear)
  rw [hImage t, hImage s]
  simpa only [map_sub, map_add, map_sum, Rat.cast_sub, Rat.cast_add,
    Rat.cast_sum, mapPoint, mapScalar, Complex.add_im,
    ApproximationContext.vertexPoint, ApproximationContext.centrePoint,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, zero_mul, mul_one, zero_add, add_zero] using hmapReal

private theorem properCarrier_horizontalSideOrder
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (imageCenters : C.centres → Tiling.Plane)
    (hImage : ∀ t, imageCenters t = mapPoint phi (C.centrePoint t.1 t.2))
    {B : Set ℝ} (hB : IsOpen B) (hBreg : interior (closure B) = B)
    (hTile : TilesOn C.region C.centres (Complex.re ⁻¹' B))
    (v v' w w' : C.region.vertices) (s t : C.centres)
    (hv : v.1 ≠ v'.1 ∧ v.1.im = v'.1.im ∧
      openSegment ℝ v.1 v'.1 ⊆ frontier C.region.support \ C.region.vertices)
    (hw : w.1 ≠ w'.1 ∧ w.1.im = w'.1.im ∧
      openSegment ℝ w.1 w'.1 ⊆ frontier C.region.support \ C.region.vertices)
    (hoverlap : (Ioo (min v.1.re v'.1.re + s.1.re)
      (max v.1.re v'.1.re + s.1.re) ∩
      Ioo (min w.1.re w'.1.re + t.1.re)
        (max w.1.re w'.1.re + t.1.re)).Nonempty)
    (horder : (v.1 + s.1).im < (w.1 + t.1).im) :
    (mapPoint phi (C.vertexPoint v.1 v.2) + imageCenters s).im <
      (mapPoint phi (C.vertexPoint w.1 w.2) + imageCenters t).im := by
  obtain ⟨n, hn, a, b, hab, hsum⟩ := properCarrier_verticalGapChain hB hBreg hTile
    v v' w w' s t hv.1 hw.1 hv.2.1 hw.2.1 hv.2.2 hw.2.2 hoverlap horder
  apply sub_pos.mp
  rw [mappedVerticalDifference_eq_sum C phi imageCenters hImage v w s t a b hsum]
  have hterm (i : Fin n) :
      0 < (mapPoint phi (C.vertexPoint (b i).1 (b i).2)).im -
        (mapPoint phi (C.vertexPoint (a i).1 (a i).2)).im := by
    rw [← D.vertex_agreement (b i).1 (b i).2,
      ← D.vertex_agreement (a i).1 (a i).2,
      D.planarHomeomorph_apply, D.planarHomeomorph_apply]
    simpa using sub_pos.mpr (D.secondHomeomorph_strictMono (hab i))
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun i _ => hterm i) Finset.univ_nonempty

private theorem properCarrier_horizontalSideHeight_iff
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (imageCenters : C.centres → Tiling.Plane)
    (hImage : ∀ t, imageCenters t = mapPoint phi (C.centrePoint t.1 t.2))
    {B : Set ℝ} (hB : IsOpen B) (hBreg : interior (closure B) = B)
    (hTile : TilesOn C.region C.centres (Complex.re ⁻¹' B))
    (v v' w w' : C.region.vertices) (s t : C.centres)
    (hv : v.1 ≠ v'.1 ∧ v.1.im = v'.1.im ∧
      openSegment ℝ v.1 v'.1 ⊆ frontier C.region.support \ C.region.vertices)
    (hw : w.1 ≠ w'.1 ∧ w.1.im = w'.1.im ∧
      openSegment ℝ w.1 w'.1 ⊆ frontier C.region.support \ C.region.vertices)
    (hoverlap : (Ioo (min v.1.re v'.1.re + s.1.re)
      (max v.1.re v'.1.re + s.1.re) ∩
      Ioo (min w.1.re w'.1.re + t.1.re)
        (max w.1.re w'.1.re + t.1.re)).Nonempty) :
    (v.1 + s.1).im = (w.1 + t.1).im ↔
      (mapPoint phi (C.vertexPoint v.1 v.2) + imageCenters s).im =
        (mapPoint phi (C.vertexPoint w.1 w.2) + imageCenters t).im := by
  constructor
  · intro heq
    have hlinear :
        (⟨v.1.im, C.vertex_im_mem v.1 v.2⟩ : C.coordinateSpace) +
            ⟨s.1.im, C.centre_im_mem s.1 s.2⟩ =
          ⟨w.1.im, C.vertex_im_mem w.1 w.2⟩ +
            ⟨t.1.im, C.centre_im_mem t.1 t.2⟩ := by
      apply Subtype.ext
      simpa only [Submodule.coe_add, Complex.add_im] using heq
    have hmapReal := congrArg (fun q : ℚ => (q : ℝ)) (congrArg phi hlinear)
    rw [hImage s, hImage t]
    simpa only [map_add, Rat.cast_add, mapPoint, mapScalar,
      ApproximationContext.vertexPoint, ApproximationContext.centrePoint,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add, add_zero] using hmapReal
  · intro heq
    rcases lt_trichotomy (v.1 + s.1).im (w.1 + t.1).im with hlt | heq' | hgt
    · exact ((properCarrier_horizontalSideOrder C phi D imageCenters hImage hB hBreg
        hTile v v' w w' s t hv hw hoverlap hlt).ne heq).elim
    · exact heq'
    · have hoverlap' : (Ioo (min w.1.re w'.1.re + t.1.re)
        (max w.1.re w'.1.re + t.1.re) ∩
        Ioo (min v.1.re v'.1.re + s.1.re)
          (max v.1.re v'.1.re + s.1.re)).Nonempty := by
        simpa only [inter_comm] using hoverlap
      exact ((properCarrier_horizontalSideOrder C phi D imageCenters hImage hB hBreg
        hTile w w' v v' t s hw hv hoverlap' hgt).ne heq.symm).elim

private theorem intrinsicHorizontalSide_vertexEquiv
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (v w : C.region.vertices) :
    (v.1 ≠ w.1 ∧ v.1.im = w.1.im ∧
      openSegment ℝ v.1 w.1 ⊆ frontier C.region.support \ C.region.vertices) ↔
    ((D.vertexEquiv v).1 ≠ (D.vertexEquiv w).1 ∧
      (D.vertexEquiv v).1.im = (D.vertexEquiv w).1.im ∧
      openSegment ℝ (D.vertexEquiv v).1 (D.vertexEquiv w).1 ⊆
        frontier D.deformedRegion.support \ D.deformedRegion.vertices) := by
  have hheight : v.1.im = w.1.im ↔
      (D.vertexEquiv v).1.im = (D.vertexEquiv w).1.im := by
    change _ ↔ (D.planarHomeomorph v.1).im = (D.planarHomeomorph w.1).im
    rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
    simp
  have hne : v.1 ≠ w.1 ↔ (D.vertexEquiv v).1 ≠ (D.vertexEquiv w).1 :=
    D.planarHomeomorph.injective.ne_iff.symm
  constructor
  · rintro ⟨hne', hheight', hside⟩
    refine ⟨hne.mp hne', hheight.mp hheight', ?_⟩
    intro z hz
    rw [D.vertexEquiv_apply, D.vertexEquiv_apply] at hz
    rw [← D.image_openSegment_of_axisAligned v.1 w.1 (Or.inr hheight')] at hz
    obtain ⟨x, hxseg, rfl⟩ := hz
    have hxside := hside hxseg
    constructor
    · rw [← D.deformedRegion.frontier_openCarrier_eq_frontier_support,
        D.frontier_image]
      refine ⟨x, ?_, rfl⟩
      rw [C.region.frontier_openCarrier_eq_frontier_support]
      exact hxside.1
    · rw [D.vertices_image]
      rintro ⟨y, hy, hxy⟩
      exact hxside.2 ((D.planarHomeomorph.injective hxy) ▸ hy)
  · rintro ⟨hne', hheight', hside⟩
    refine ⟨hne.mpr hne', hheight.mpr hheight', ?_⟩
    intro x hx
    have hzseg : D.planarHomeomorph x ∈
        openSegment ℝ (D.vertexEquiv v).1 (D.vertexEquiv w).1 := by
      rw [D.vertexEquiv_apply, D.vertexEquiv_apply]
      rw [← D.image_openSegment_of_axisAligned v.1 w.1
        (Or.inr (hheight.mpr hheight'))]
      exact ⟨x, hx, rfl⟩
    have hzside := hside hzseg
    constructor
    · have hzfront := hzside.1
      rw [← D.deformedRegion.frontier_openCarrier_eq_frontier_support,
        D.frontier_image] at hzfront
      obtain ⟨y, hy, hyx⟩ := hzfront
      have hyx' := D.planarHomeomorph.injective hyx
      rw [C.region.frontier_openCarrier_eq_frontier_support] at hy
      exact hyx' ▸ hy
    · intro hxV
      apply hzside.2
      rw [D.vertices_image]
      exact ⟨x, hxV, rfl⟩

private theorem sign_eq_one_iff_pos {r : ℝ} : Real.sign r = 1 ↔ 0 < r := by
  constructor
  · intro h
    by_contra hn
    rcases (le_of_not_gt hn).eq_or_lt with hz | hneg
    · rw [hz, Real.sign_zero] at h
      norm_num at h
    · rw [Real.sign_of_neg hneg] at h
      norm_num at h
  · exact Real.sign_of_pos

private theorem translatedHorizontalIntervals_overlap_iff
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (imageCenters : C.centres → Tiling.Plane)
    (hImage : ∀ t, imageCenters t = mapPoint phi (C.centrePoint t.1 t.2))
    (hHorizontalSign : ∀ v w : C.region.vertices, ∀ s t : C.centres,
      Real.sign ((w.1 + t.1).re - (v.1 + s.1).re) =
        Real.sign ((mapPoint phi (C.vertexPoint w.1 w.2) +
            mapPoint phi (C.centrePoint t.1 t.2)).re -
          (mapPoint phi (C.vertexPoint v.1 v.2) +
            mapPoint phi (C.centrePoint s.1 s.2)).re))
    (v v' w w' : C.region.vertices) (s t : C.centres) :
    (Ioo (min v.1.re v'.1.re + s.1.re)
        (max v.1.re v'.1.re + s.1.re) ∩
      Ioo (min w.1.re w'.1.re + t.1.re)
        (max w.1.re w'.1.re + t.1.re)).Nonempty ↔
    (Ioo (min (D.vertexEquiv v).1.re (D.vertexEquiv v').1.re + (imageCenters s).re)
        (max (D.vertexEquiv v).1.re (D.vertexEquiv v').1.re + (imageCenters s).re) ∩
      Ioo (min (D.vertexEquiv w).1.re (D.vertexEquiv w').1.re + (imageCenters t).re)
        (max (D.vertexEquiv w).1.re (D.vertexEquiv w').1.re + (imageCenters t).re)).Nonempty := by
  have hlt (a b : C.region.vertices) (p q : C.centres) :
      a.1.re + p.1.re < b.1.re + q.1.re ↔
        (D.vertexEquiv a).1.re + (imageCenters p).re <
          (D.vertexEquiv b).1.re + (imageCenters q).re := by
    have hs := hHorizontalSign a b p q
    rw [← hImage p, ← hImage q,
      ← D.vertex_agreement a.1 a.2, ← D.vertex_agreement b.1 b.2,
      ← D.vertexEquiv_apply a, ← D.vertexEquiv_apply b] at hs
    have hpos := congrArg (fun r : ℝ => r = 1) hs
    simpa only [sign_eq_one_iff_pos, sub_pos, Complex.add_re, eq_iff_iff] using hpos
  simp only [← min_add_add_right, ← max_add_add_right,
    Set.Ioo_inter_Ioo, Set.nonempty_Ioo,
    max_lt_iff, lt_min_iff, min_lt_iff, lt_max_iff]
  simp only [hlt]

private theorem properCarrier_horizontalContact_iff
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (imageCenters : C.centres ↪ Tiling.Plane)
    (hImage : ∀ t, imageCenters t = mapPoint phi (C.centrePoint t.1 t.2))
    {B : Set ℝ} (hB : IsOpen B) (hBreg : interior (closure B) = B)
    (hTile : TilesOn C.region C.centres (Complex.re ⁻¹' B))
    (hHorizontalSign : ∀ v w : C.region.vertices, ∀ s t : C.centres,
      Real.sign ((w.1 + t.1).re - (v.1 + s.1).re) =
        Real.sign ((mapPoint phi (C.vertexPoint w.1 w.2) +
            mapPoint phi (C.centrePoint t.1 t.2)).re -
          (mapPoint phi (C.vertexPoint v.1 v.2) +
            mapPoint phi (C.centrePoint s.1 s.2)).re))
    (s t : C.centres) :
    HorizontalProperContact C.region s.1 t.1 ↔
      HorizontalProperContact D.deformedRegion (imageCenters s) (imageCenters t) := by
  rw [horizontalProperContact_iff_exists_intrinsicSides,
    horizontalProperContact_iff_exists_intrinsicSides]
  constructor
  · rintro ⟨v, v', w, w', hv, hw, hheight, hoverlap⟩
    refine ⟨D.vertexEquiv v, D.vertexEquiv v', D.vertexEquiv w, D.vertexEquiv w',
      (intrinsicHorizontalSide_vertexEquiv C phi D v v').mp hv,
      (intrinsicHorizontalSide_vertexEquiv C phi D w w').mp hw, ?_,
      (translatedHorizontalIntervals_overlap_iff C phi D imageCenters hImage
        hHorizontalSign v v' w w' s t).mp hoverlap⟩
    rw [D.vertexEquiv_apply, D.vertexEquiv_apply,
      D.vertex_agreement, D.vertex_agreement]
    exact (properCarrier_horizontalSideHeight_iff C phi D imageCenters hImage
      hB hBreg hTile v v' w w' s t hv hw hoverlap).mp hheight
  · rintro ⟨V, V', W, W', hV, hW, hheight, hoverlap⟩
    obtain ⟨v, rfl⟩ := D.vertexEquiv.surjective V
    obtain ⟨v', rfl⟩ := D.vertexEquiv.surjective V'
    obtain ⟨w, rfl⟩ := D.vertexEquiv.surjective W
    obtain ⟨w', rfl⟩ := D.vertexEquiv.surjective W'
    have hv := (intrinsicHorizontalSide_vertexEquiv C phi D v v').mpr hV
    have hw := (intrinsicHorizontalSide_vertexEquiv C phi D w w').mpr hW
    have hoverlap' := (translatedHorizontalIntervals_overlap_iff C phi D imageCenters
      hImage hHorizontalSign v v' w w' s t).mpr hoverlap
    refine ⟨v, v', w, w', hv, hw, ?_, hoverlap'⟩
    apply (properCarrier_horizontalSideHeight_iff C phi D imageCenters hImage
      hB hBreg hTile v v' w w' s t hv hw hoverlap').mpr
    rw [D.vertexEquiv_apply, D.vertexEquiv_apply,
      D.vertex_agreement, D.vertex_agreement] at hheight
    exact hheight

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Set Tiling.AxisParallel Tiling.AxisParallel.Approximation Tiling.AxisParallel.Continuous
open scoped Pointwise

private inductive SlabCodeLabel (K : Region) (T : Set Tiling.Plane) where
  | outside
  | noncolumn (P : {P : VerticalPlate K T // ¬ IsVerticalColumn P})
  | columns

private def sourceGapHasLabel {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier) (a b : ℝ) : SlabCodeLabel K T → Prop
  | .outside => Ioo a b ⊆ X.baseᶜ
  | .noncolumn P => Ioo a b ⊆ P.1.base
  | .columns => Ioo a b ⊆ aggregateColumnBase K T

private structure ProperCarrierLabelledTransport
    (C : ApproximationContext.{0}) (X : PeriodicVerticalCarrier)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C phi)
    (imageCenters : ↑C.centres ↪ Tiling.Plane) (imageCarrier : PeriodicVerticalCarrier) where
  scalarHomeomorph : ℝ ≃ₜ ℝ
  scalarHomeomorph_strictMono : StrictMono scalarHomeomorph
  scalarHomeomorph_translatedVertex : ∀ (v : C.region.vertices) (t : C.centres),
    scalarHomeomorph (v.1 + (t : Tiling.Plane)).re =
      (mapPoint phi (C.vertexPoint v.1 v.2) + imageCenters t).re
  carrier_base_image : imageCarrier.base = scalarHomeomorph '' X.base
  horizontalContact_iff : ∀ s t : C.centres,
    HorizontalProperContact C.region s.1 t.1 ↔
      HorizontalProperContact D.deformedRegion (imageCenters s) (imageCenters t)
  imageNoncolumnPlate :
    {P : VerticalPlate C.region C.centres // ¬ IsVerticalColumn P} ≃
    {P : VerticalPlate D.deformedRegion (deformedCenterCarrier imageCenters) //
      ¬ IsVerticalColumn P}
  imageNoncolumnPlate_centres : ∀ P,
    (imageNoncolumnPlate P).1.centres = deformedCenterCarrierOn imageCenters
      {t : ↑C.centres | (t : Tiling.Plane) ∈ P.1.centres}
  imageNoncolumnPlate_base : ∀ P,
    (imageNoncolumnPlate P).1.base = scalarHomeomorph '' P.1.base
  aggregateColumnBase_image :
    aggregateColumnBase D.deformedRegion (deformedCenterCarrier imageCenters) =
      scalarHomeomorph '' aggregateColumnBase C.region C.centres
  boundaryMap : ↑(totalSlabBoundary C.region C.centres X) ≃o
    ↑(totalSlabBoundary D.deformedRegion (deformedCenterCarrier imageCenters) imageCarrier)
  boundaryMap_apply : ∀ x, (boundaryMap x).1 = scalarHomeomorph x.1
  sourceLabel : ↑(totalSlabBoundary C.region C.centres X) → SlabCodeLabel C.region C.centres
  imageLabel : ↑(totalSlabBoundary D.deformedRegion (deformedCenterCarrier imageCenters)
    imageCarrier) → SlabCodeLabel C.region C.centres
  labels_preserved : ∀ x, imageLabel (boundaryMap x) = sourceLabel x
  sourceLabel_geometric : ∀ {a b : ℝ}
    (h : ConsecutiveIn (totalSlabBoundary C.region C.centres X) a b),
    sourceGapHasLabel X a b (sourceLabel ⟨a, h.1⟩)
  imageLabel_geometric : ∀ {a b : ℝ}
    (ha : a ∈ totalSlabBoundary D.deformedRegion (deformedCenterCarrier imageCenters)
      imageCarrier)
    (_h : ConsecutiveIn (totalSlabBoundary D.deformedRegion
      (deformedCenterCarrier imageCenters) imageCarrier) a b),
    match imageLabel ⟨a, ha⟩ with
    | .outside => Ioo a b ⊆ imageCarrier.baseᶜ
    | .noncolumn P => Ioo a b ⊆ (imageNoncolumnPlate P).1.base
    | .columns => Ioo a b ⊆ aggregateColumnBase D.deformedRegion
        (deformedCenterCarrier imageCenters)


private structure LabelledSlabBoundaryTransport
    (K : Region) (T : Set Tiling.Plane) (X : PeriodicVerticalCarrier)
    (K' : Region) (T' : Set Tiling.Plane) (X' : PeriodicVerticalCarrier)
    (H : ℝ ≃ₜ ℝ)
    (eNC : {P : VerticalPlate K T // ¬ IsVerticalColumn P} ≃
      {P : VerticalPlate K' T' // ¬ IsVerticalColumn P}) where
  boundaryMap : ↑(totalSlabBoundary K T X) ≃o ↑(totalSlabBoundary K' T' X')
  boundaryMap_apply : ∀ x, (boundaryMap x).1 = H x.1
  sourceLabel : ↑(totalSlabBoundary K T X) → SlabCodeLabel K T
  imageLabel : ↑(totalSlabBoundary K' T' X') → SlabCodeLabel K T
  labels_preserved : ∀ x, imageLabel (boundaryMap x) = sourceLabel x
  sourceLabel_geometric : ∀ {a b : ℝ}
    (h : ConsecutiveIn (totalSlabBoundary K T X) a b),
    sourceGapHasLabel X a b (sourceLabel ⟨a, h.1⟩)
  imageLabel_geometric : ∀ {a b : ℝ}
    (ha : a ∈ totalSlabBoundary K' T' X')
    (_h : ConsecutiveIn (totalSlabBoundary K' T' X') a b),
    match imageLabel ⟨a, ha⟩ with
    | .outside => Ioo a b ⊆ X'.baseᶜ
    | .noncolumn P => Ioo a b ⊆ (eNC P).1.base
    | .columns => Ioo a b ⊆ aggregateColumnBase K' T'

/-- Transport the complete geometric gap code along one common base homeomorphism. -/
private theorem labelledSlabBoundaryTransport_exists
    {K K' : Region} {T T' : Set Tiling.Plane}
    (X X' : PeriodicVerticalCarrier) (hTile : TilesOn K T X.carrier)
    (H : ℝ ≃ₜ ℝ) (hH : StrictMono H)
    (eNC : {P : VerticalPlate K T // ¬ IsVerticalColumn P} ≃
      {P : VerticalPlate K' T' // ¬ IsVerticalColumn P})
    (hcarrierBase : X'.base = H '' X.base)
    (hplateBase : ∀ P, (eNC P).1.base = H '' P.1.base)
    (hcolumnBase : aggregateColumnBase K' T' = H '' aggregateColumnBase K T) :
    Nonempty (LabelledSlabBoundaryTransport K T X K' T' X' H eNC) := by
  classical
  let B := totalSlabBoundary K T X
  let B' := totalSlabBoundary K' T' X'
  have hboundary : B' = H '' B := by
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · rw [hcarrierBase, ← H.image_frontier] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        exact ⟨x, Or.inl (Or.inl hx), rfl⟩
      · obtain ⟨Q, hzQ⟩ := Set.mem_iUnion.mp hz
        obtain ⟨P, hPQ⟩ := eNC.surjective Q
        rw [← hPQ, hplateBase, ← H.image_frontier] at hzQ
        obtain ⟨x, hx, rfl⟩ := hzQ
        exact ⟨x, Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨P, hx⟩)), rfl⟩
      · rw [hcolumnBase, ← H.image_frontier] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        exact ⟨x, Or.inr hx, rfl⟩
    · rintro ⟨x, ((hx | hx) | hx), rfl⟩
      · left; left
        rw [hcarrierBase, ← H.image_frontier]
        exact ⟨x, hx, rfl⟩
      · left; right
        obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
        apply Set.mem_iUnion.mpr
        refine ⟨eNC P, ?_⟩
        rw [hplateBase, ← H.image_frontier]
        exact ⟨x, hxP, rfl⟩
      · right
        rw [hcolumnBase, ← H.image_frontier]
        exact ⟨x, hx, rfl⟩
  let boundaryFunction : B → B' := fun x ↦ ⟨H x.1, hboundary ▸ ⟨x.1, x.2, rfl⟩⟩
  have hboundaryMono : StrictMono boundaryFunction := fun _ _ h ↦ hH h
  have hboundarySurj : Function.Surjective boundaryFunction := by
    rintro ⟨z, hz⟩
    rw [hboundary] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨⟨x, hx⟩, rfl⟩
  let boundaryMap : B ≃o B' :=
    hboundaryMono.orderIsoOfSurjective boundaryFunction hboundarySurj
  have hboundaryApply (x : B) : (boundaryMap x).1 = H x.1 := rfl
  have hlabels (a : B) : ∃ L : SlabCodeLabel K T,
      ∀ b : ℝ, ConsecutiveIn B a.1 b → sourceGapHasLabel X a.1 b L := by
    by_cases hnext : ∃ b, ConsecutiveIn B a.1 b
    · obtain ⟨b, hb⟩ := hnext
      rcases totalBoundary_labelTrichotomy X hTile hb with hout | ⟨P, hP, hbase⟩ | hcol
      · exact ⟨.outside, fun c hc ↦ (ConsecutiveIn.right_unique hb hc) ▸ hout⟩
      · exact ⟨.noncolumn ⟨P, hP⟩, fun c hc ↦ (ConsecutiveIn.right_unique hb hc) ▸ hbase⟩
      · exact ⟨.columns, fun c hc ↦ (ConsecutiveIn.right_unique hb hc) ▸ hcol⟩
    · exact ⟨.outside, fun b hb ↦ False.elim (hnext ⟨b, hb⟩)⟩
  let sourceLabel : B → SlabCodeLabel K T := fun a ↦ (hlabels a).choose
  have hsourceLabel {a b : ℝ} (hgap : ConsecutiveIn B a b) :
      sourceGapHasLabel X a b (sourceLabel ⟨a, hgap.1⟩) :=
    (hlabels ⟨a, hgap.1⟩).choose_spec b hgap
  let imageLabel : B' → SlabCodeLabel K T := fun a ↦ sourceLabel (boundaryMap.symm a)
  refine ⟨{
    boundaryMap := boundaryMap
    boundaryMap_apply := hboundaryApply
    sourceLabel := sourceLabel
    imageLabel := imageLabel
    labels_preserved := fun x ↦ by simp [imageLabel]
    sourceLabel_geometric := hsourceLabel
    imageLabel_geometric := ?_ }⟩
  intro a b ha hgap
  let a₀ : B := boundaryMap.symm ⟨a, ha⟩
  let b₀ : B := boundaryMap.symm ⟨b, hgap.2.1⟩
  have haImage : H a₀.1 = a :=
    (hboundaryApply a₀).symm.trans
      (congrArg Subtype.val (boundaryMap.apply_symm_apply ⟨a, ha⟩))
  have hbImage : H b₀.1 = b :=
    (hboundaryApply b₀).symm.trans
      (congrArg Subtype.val (boundaryMap.apply_symm_apply ⟨b, hgap.2.1⟩))
  have hsourceGap : ConsecutiveIn B a₀.1 b₀.1 := by
    refine ⟨a₀.2, b₀.2, hH.lt_iff_lt.mp (haImage ▸ hbImage ▸ hgap.2.2.1), ?_⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxB⟩
    have hxImage : H x ∈ Ioo a b ∩ B' :=
      ⟨⟨haImage ▸ hH hx.1, hbImage ▸ hH hx.2⟩, hboundary ▸ ⟨x, hxB, rfl⟩⟩
    rw [hgap.2.2.2] at hxImage
    exact hxImage
  have hsourceGeom := hsourceLabel hsourceGap
  change match sourceLabel a₀ with
    | .outside => _
    | .noncolumn P => _
    | .columns => _
  cases hL : sourceLabel a₀ with
  | outside =>
      intro y hy hyCarrier
      rw [hcarrierBase] at hyCarrier
      obtain ⟨x, hx, rfl⟩ := hyCarrier
      have hxgap : x ∈ Ioo a₀.1 b₀.1 :=
        ⟨hH.lt_iff_lt.mp (haImage ▸ hy.1), hH.lt_iff_lt.mp (hbImage ▸ hy.2)⟩
      rw [hL] at hsourceGeom
      exact hsourceGeom hxgap hx
  | noncolumn P =>
      intro y hy
      rw [hplateBase]
      refine ⟨H.symm y, ?_, H.apply_symm_apply y⟩
      rw [hL] at hsourceGeom
      apply hsourceGeom
      constructor <;> apply hH.lt_iff_lt.mp
      · simpa [haImage] using hy.1
      · simpa [hbImage] using hy.2
  | columns =>
      intro y hy
      rw [hcolumnBase]
      refine ⟨H.symm y, ?_, H.apply_symm_apply y⟩
      rw [hL] at hsourceGeom
      apply hsourceGeom
      constructor <;> apply hH.lt_iff_lt.mp
      · simpa [haImage] using hy.1
      · simpa [hbImage] using hy.2


private theorem properCarrierLabelledTransport_exists :
    ∀ (C : ApproximationContext.{0}) (X : PeriodicVerticalCarrier)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C phi)
      (imageCenters : ↑C.centres ↪ Tiling.Plane) (imageCarrier : PeriodicVerticalCarrier),
    C.target = X.carrier → TilesOn C.region C.centres C.target →
    HasFiniteHorizontalComplexity C.centres → X.base ≠ Set.univ →
    IsGoodApproximation C phi → PreservesHorizontalTranslatedVertexSigns C phi →
    ControlsHorizontalTranslatedVertexDistances C phi →
    (∀ t, imageCenters t = mapPoint phi (C.centrePoint t.1 t.2)) →
    TilesOn D.deformedRegion (deformedCenterCarrier imageCenters) imageCarrier.carrier →
      Nonempty (ProperCarrierLabelledTransport C X phi D imageCenters imageCarrier) := by
  intro C X phi D imageCenters imageCarrier htarget hTile hFHC _hProper _hGood
    hSigns hDistances hImage hImageTile
  classical
  have hTileX : TilesOn C.region C.centres X.carrier := htarget ▸ hTile
  obtain ⟨H, hH, hvertex⟩ := translatedVertexHomeomorph_exists C X phi htarget hTile
    hFHC hSigns hDistances
  have hvertex' (v : C.region.vertices) (t : C.centres) :
      H (v.1 + (t : Tiling.Plane)).re =
        (mapPoint phi (C.vertexPoint v.1 v.2) + imageCenters t).re := by
    rw [hImage]
    exact hvertex v t
  have hprojection := placedTileHorizontalProjection_image C phi D imageCenters H
    hH hImage hvertex'
  have hselected := selectedSubfamily_regularizedProjection_image C phi D imageCenters H
    hH hImage hprojection
  have hcontact : ∀ s t : C.centres,
      HorizontalProperContact C.region s.1 t.1 ↔
        HorizontalProperContact D.deformedRegion (imageCenters s) (imageCenters t) :=
    properCarrier_horizontalContact_iff C phi D imageCenters hImage
      X.base_open X.base_regular hTileX hSigns
  let g : verticalPlateGraph C.region C.centres ≃g
      verticalPlateGraph D.deformedRegion (deformedCenterCarrier imageCenters) := {
    toEquiv := deformedCenterEquivCarrier imageCenters
    map_rel_iff' := by
      intro s t
      rw [verticalPlateGraph_adj_iff, verticalPlateGraph_adj_iff]
      exact and_congr (deformedCenterEquivCarrier imageCenters).injective.eq_iff.not
        (hcontact s t).symm }
  let e : VerticalPlate C.region C.centres ≃
      VerticalPlate D.deformedRegion (deformedCenterCarrier imageCenters) :=
    g.connectedComponentEquiv
  have hcentres (P : VerticalPlate C.region C.centres) :
      (e P).centres = deformedCenterCarrierOn imageCenters
        {t : C.centres | (t : Tiling.Plane) ∈ P.centres} := by
    change Subtype.val '' (g.connectedComponentEquiv P).supp =
      imageCenters '' {t : C.centres | (t : Tiling.Plane) ∈ P.centres}
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht⟩ := a.2
      have hat : a = g t := by apply Subtype.ext; exact ht.symm
      subst a
      refine ⟨t, ?_, rfl⟩
      exact ⟨t, (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
        (φ := g) (v := t) (C := P)).mp ha, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨g t, ?_, rfl⟩
      obtain ⟨u, hu, hut⟩ := ht
      have htu : t = u := Subtype.ext hut.symm
      subst u
      exact (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
        (φ := g) (v := t) (C := P)).mpr hu
  have hcoordinate (s t : C.centres) :
      s.1.re = t.1.re ↔ (imageCenters s).re = (imageCenters t).re := by
    let v : C.region.vertices := ⟨0, C.zero_mem_vertices⟩
    have hs := hvertex' v s
    have ht := hvertex' v t
    simp only [v, zero_add, Complex.add_re] at hs ht
    constructor
    · intro hst
      have hmap := congrArg H hst
      rw [hs, ht] at hmap
      exact add_left_cancel hmap
    · intro hst
      apply H.injective
      rw [hs, ht, hst]
  have hcolumns (P : VerticalPlate C.region C.centres) :
      IsVerticalColumn P ↔ IsVerticalColumn (e P) := by
    rw [isVerticalColumn_iff, isVerticalColumn_iff]
    obtain ⟨p, hp⟩ := P.nonempty_supp
    have hpP : (p : Tiling.Plane) ∈ P.centres := ⟨p, hp, rfl⟩
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨(imageCenters p).re, ?_⟩
      intro z hz
      rw [hcentres] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact (hcoordinate t p).mp ((hx ht).trans (hx hpP).symm)
    · rintro ⟨x, hx⟩
      refine ⟨p.1.re, ?_⟩
      rintro z ⟨t, ht, rfl⟩
      have hpImage : imageCenters p ∈ (e P).centres := by
        rw [hcentres]
        exact ⟨p, hpP, rfl⟩
      have htImage : imageCenters t ∈ (e P).centres := by
        rw [hcentres]
        exact ⟨t, ⟨t, ht, rfl⟩, rfl⟩
      exact (hcoordinate t p).mpr ((hx htImage).trans (hx hpImage).symm)
  let eNC : {P : VerticalPlate C.region C.centres // ¬ IsVerticalColumn P} ≃
      {P : VerticalPlate D.deformedRegion (deformedCenterCarrier imageCenters) //
        ¬ IsVerticalColumn P} := e.subtypeEquiv fun P ↦ (hcolumns P).not
  have hplateBase (P : VerticalPlate C.region C.centres) : (e P).base = H '' P.base := by
    rw [verticalPlateBase_regularizedProjection imageCarrier hImageTile,
      hcentres, hselected P.centres (by rintro _ ⟨t, -, rfl⟩; exact t.2),
      ← verticalPlateBase_regularizedProjection X hTileX P]
  have hcolumnCentres : verticalColumnCentres D.deformedRegion
      (deformedCenterCarrier imageCenters) = deformedCenterCarrierOn imageCenters
        {t : C.centres | (t : Tiling.Plane) ∈ verticalColumnCentres C.region C.centres} := by
    ext z
    constructor
    · intro hz
      obtain ⟨Q, hzQ⟩ := Set.mem_iUnion.mp hz
      obtain ⟨P, hPQ⟩ := e.surjective Q.1
      have hPcol : IsVerticalColumn P := (hcolumns P).mpr (hPQ ▸ Q.2)
      rw [← hPQ, hcentres] at hzQ
      obtain ⟨t, ht, rfl⟩ := hzQ
      exact ⟨t, Set.mem_iUnion.mpr ⟨⟨P, hPcol⟩, ht⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨P, htP⟩ := Set.mem_iUnion.mp ht
      apply Set.mem_iUnion.mpr
      refine ⟨⟨e P.1, (hcolumns P.1).mp P.2⟩, ?_⟩
      rw [hcentres]
      exact ⟨t, htP, rfl⟩
  have hcolumnBase : aggregateColumnBase D.deformedRegion
      (deformedCenterCarrier imageCenters) = H '' aggregateColumnBase C.region C.centres := by
    rw [aggregateColumnBase_regularizedProjection imageCarrier hImageTile, hcolumnCentres,
      hselected _ (Continuous.verticalColumnCentres_subset _ _),
      ← aggregateColumnBase_regularizedProjection X hTileX]
  have hfull : deformedCenterCarrierOn imageCenters
      {t : C.centres | (t : Tiling.Plane) ∈ C.centres} = deformedCenterCarrier imageCenters := by
    ext z
    simp only [deformedCenterCarrierOn, deformedCenterCarrier, Set.mem_image, Set.mem_range,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, -, ht⟩; exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩; exact ⟨t, t.2, ht⟩
  have hcarrierBase : imageCarrier.base = H '' X.base := by
    rw [carrierBase_regularizedProjection imageCarrier hImageTile, ← hfull,
      hselected C.centres Subset.rfl, ← carrierBase_regularizedProjection X hTileX]
  obtain ⟨labels⟩ := labelledSlabBoundaryTransport_exists X imageCarrier hTileX H hH eNC
    hcarrierBase (fun P ↦ hplateBase P.1) hcolumnBase
  refine ⟨{
    scalarHomeomorph := H
    scalarHomeomorph_strictMono := hH
    scalarHomeomorph_translatedVertex := hvertex'
    carrier_base_image := hcarrierBase
    horizontalContact_iff := hcontact
    imageNoncolumnPlate := eNC
    imageNoncolumnPlate_centres := fun P ↦ hcentres P.1
    imageNoncolumnPlate_base := fun P ↦ hplateBase P.1
    aggregateColumnBase_image := hcolumnBase
    boundaryMap := labels.boundaryMap
    boundaryMap_apply := labels.boundaryMap_apply
    sourceLabel := labels.sourceLabel
    imageLabel := labels.imageLabel
    labels_preserved := labels.labels_preserved
    sourceLabel_geometric := labels.sourceLabel_geometric
    imageLabel_geometric := ?_ }⟩
  intro a b ha hgap
  have hgeom := labels.imageLabel_geometric ha hgap
  cases hlabel : labels.imageLabel ⟨a, ha⟩ <;> simpa only [hlabel] using hgeom

private structure FirstCarrierPreAlphabetTransport
    (C : Tiling.AxisParallel.Approximation.ApproximationContext.{0})
    (X : PeriodicVerticalCarrier) where
  source_target_eq : C.target = X.carrier
  source_tiles : Tiling.AxisParallel.TilesOn C.region C.centres C.target
  source_finiteHorizontalComplexity :
    Tiling.AxisParallel.Continuous.HasFiniteHorizontalComplexity C.centres
  sourceBoundary_nonempty : (totalSlabBoundary C.region C.centres X).Nonempty
  phi : C.coordinateSpace →ₗ[ℚ] ℚ
  horizontalOrder : PreservesHorizontalTranslatedVertexSigns C phi
  deformation : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi
  imageCenters : ↑C.centres ↪ Tiling.Plane
  imageCenters_apply : ∀ t, imageCenters t =
    Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)
  imageCarrier : PeriodicVerticalCarrier
  imageTiles : Tiling.AxisParallel.TilesOn deformation.deformedRegion
    (Tiling.AxisParallel.Approximation.deformedCenterCarrier imageCenters)
    imageCarrier.carrier
  imageBoundary : Set ℝ
  imageBoundary_eq : imageBoundary = totalSlabBoundary deformation.deformedRegion
    (Tiling.AxisParallel.Approximation.deformedCenterCarrier imageCenters) imageCarrier
  boundaryMap : ↑(totalSlabBoundary C.region C.centres X) ≃o ↑imageBoundary
  boundaryLift : ↑(totalSlabBoundary C.region C.centres X) → C.coordinateSpace
  boundaryLift_coe : ∀ x, ((boundaryLift x : C.coordinateSpace) : ℝ) = x.1
  boundaryMap_formula : ∀ x, (boundaryMap x).1 =
    Tiling.AxisParallel.Approximation.mapScalar phi (boundaryLift x)
  boundaryMap_distortion : ∀ {a b : ↑(totalSlabBoundary C.region C.centres X)},
    a.1 < b.1 →
      (1 / 2 : ℝ) * (b.1 - a.1) ≤ (boundaryMap b).1 - (boundaryMap a).1 ∧
      (boundaryMap b).1 - (boundaryMap a).1 ≤ 2 * (b.1 - a.1)
  imageNoncolumnPlate :
    {P : Tiling.AxisParallel.Continuous.VerticalPlate C.region C.centres //
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P} ≃
    {P : Tiling.AxisParallel.Continuous.VerticalPlate deformation.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier imageCenters) //
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P}
  sourceLabel : ↑(totalSlabBoundary C.region C.centres X) →
    SlabCodeLabel C.region C.centres
  imageLabel : ↑imageBoundary → SlabCodeLabel C.region C.centres
  labels_preserved : ∀ x, imageLabel (boundaryMap x) = sourceLabel x
  sourceLabel_geometric : ∀ {a b : ℝ}
    (h : ConsecutiveIn (totalSlabBoundary C.region C.centres X) a b),
      sourceGapHasLabel X a b (sourceLabel ⟨a, h.1⟩)
  imageLabel_geometric : ∀ {a b : ℝ} (ha : a ∈ imageBoundary)
    (_h : ConsecutiveIn imageBoundary a b),
    match imageLabel ⟨a, ha⟩ with
    | .outside => Ioo a b ⊆ imageCarrier.baseᶜ
    | .noncolumn P => Ioo a b ⊆ (imageNoncolumnPlate P).1.base
    | .columns => Ioo a b ⊆ aggregateColumnBase deformation.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier imageCenters)

private theorem properCarrierPreAlphabetTransport_exists :
    ∀ (C : ApproximationContext.{0}) (X : PeriodicVerticalCarrier),
    C.target = X.carrier → TilesOn C.region C.centres C.target →
    HasFiniteHorizontalComplexity C.centres →
    (totalSlabBoundary C.region C.centres X).Nonempty → X.base ≠ Set.univ →
      Nonempty (FirstCarrierPreAlphabetTransport C X) := by
  intro C X htarget hTile hFHC hBoundary hProper
  classical
  obtain ⟨P, hPbase, _⟩ := exists_periodicBandData C X.base X.period
    (MeasureTheory.nonempty_of_measure_ne_zero X.base_nonnull) X.base_open X.base_regular
    hProper X.period_pos X.base_periodic htarget hTile
  obtain ⟨epsilonBand, hFineBand, _⟩ := exists_deformedBandPeriod P
  obtain ⟨epsilonSigns, hSignsPos, hSignsThreshold⟩ :=
    carrierApproximation_globalSigns C X htarget hTile hFHC
  obtain ⟨epsilonDistances, hDistancesPos, hDistancesThreshold⟩ :=
    carrierApproximation_globalDistortion C X htarget hTile hFHC
  let epsilon := min epsilonBand (min epsilonSigns epsilonDistances)
  have hepsilon : 0 < epsilon := lt_min hFineBand.epsilon_pos
    (lt_min hSignsPos hDistancesPos)
  obtain ⟨phi, hApprox⟩ := exists_epsilonApproximation C epsilon hepsilon
  have hGood : IsGoodApproximation C phi :=
    hFineBand.forces_good phi (hApprox.of_le (min_le_left _ _))
  have hSigns : PreservesHorizontalTranslatedVertexSigns C phi :=
    hSignsThreshold phi (hApprox.of_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hDistances : ControlsHorizontalTranslatedVertexDistances C phi :=
    hDistancesThreshold phi (hApprox.of_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨D⟩ := exists_rationalPolygonDeformation C phi hGood
  have hFine : IsPeriodicBandFineness P epsilon :=
    periodicBandFineness_mono P hFineBand hepsilon (min_le_left _ _)
  obtain ⟨imageCenters, base, period, hImage, hBaseOpen, hBaseRegular, hBaseNonempty,
      _hBaseProper, _hPeriodFormula, hPeriodPos, hBasePeriod, _hFrontier, _hOccupied,
      hImageTile, _hImageSupport⟩ := periodicBandDeformation P epsilon hFine phi hApprox D
  let imageCarrier : PeriodicVerticalCarrier := {
    base := base
    base_open := hBaseOpen
    base_regular := hBaseRegular
    base_nonnull := hBaseOpen.measure_ne_zero MeasureTheory.volume hBaseNonempty
    period := period
    period_pos := hPeriodPos
    base_periodic := hBasePeriod }
  obtain ⟨L⟩ := properCarrierLabelledTransport_exists C X phi D imageCenters imageCarrier
    htarget hTile hFHC hProper hGood hSigns hDistances hImage hImageTile
  have hTileX : TilesOn C.region C.centres X.carrier := htarget ▸ hTile
  let B := totalSlabBoundary C.region C.centres X
  have hrepresentation (x : B) : ∃ v : C.region.vertices, ∃ t : C.centres,
      x.1 = (v.1 + t.1).re := by
    obtain ⟨v, hv, t, ht, hvt⟩ := slabCodeBoundaries_fromVertices X hTileX x.2
    exact ⟨⟨v, hv⟩, ⟨t, ht⟩, hvt⟩
  have hcoordinate (x : B) : x.1 ∈ C.coordinateSpace := by
    obtain ⟨v, t, hvt⟩ := hrepresentation x
    rw [hvt, Complex.add_re]
    exact C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2) (C.centre_re_mem t.1 t.2)
  let lift : B → C.coordinateSpace := fun x ↦ ⟨x.1, hcoordinate x⟩
  have hformula (x : B) : (L.boundaryMap x).1 = mapScalar phi (lift x) := by
    obtain ⟨v, t, hvt⟩ := hrepresentation x
    have hlift : lift x =
        ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ + ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
      apply Subtype.ext
      simp [lift, hvt, Complex.add_re]
    rw [L.boundaryMap_apply, hvt, L.scalarHomeomorph_translatedVertex, hImage, hlift]
    have hAdd : mapScalar phi
        (⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ + ⟨t.1.re, C.centre_re_mem t.1 t.2⟩) =
        mapScalar phi ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ +
          mapScalar phi ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
      change ((phi (_ + _) : ℚ) : ℝ) = _
      rw [map_add, Rat.cast_add]
      rfl
    rw [hAdd]
    simp [mapPoint, ApproximationContext.vertexPoint, ApproximationContext.centrePoint]
  have hdistortion {a b : B} (hab : a.1 < b.1) :
      (1 / 2 : ℝ) * (b.1 - a.1) ≤ (L.boundaryMap b).1 - (L.boundaryMap a).1 ∧
      (L.boundaryMap b).1 - (L.boundaryMap a).1 ≤ 2 * (b.1 - a.1) := by
    obtain ⟨v, s, ha⟩ := hrepresentation a
    obtain ⟨w, t, hb⟩ := hrepresentation b
    have haMap : (mapPoint phi (C.vertexPoint v.1 v.2) +
        mapPoint phi (C.centrePoint s.1 s.2)).re = L.scalarHomeomorph a.1 := by
      rw [ha, L.scalarHomeomorph_translatedVertex, hImage]
    have hbMap : (mapPoint phi (C.vertexPoint w.1 w.2) +
        mapPoint phi (C.centrePoint t.1 t.2)).re = L.scalarHomeomorph b.1 := by
      rw [hb, L.scalarHomeomorph_translatedVertex, hImage]
    have hd := hDistances v w s t
    rw [← ha, ← hb, haMap, hbMap,
      abs_of_pos (sub_pos.mpr hab),
      abs_of_pos (sub_pos.mpr (L.scalarHomeomorph_strictMono hab))] at hd
    simpa only [L.boundaryMap_apply] using hd
  exact ⟨{
    source_target_eq := htarget
    source_tiles := hTile
    source_finiteHorizontalComplexity := hFHC
    sourceBoundary_nonempty := hBoundary
    phi := phi
    horizontalOrder := hSigns
    deformation := D
    imageCenters := imageCenters
    imageCenters_apply := hImage
    imageCarrier := imageCarrier
    imageTiles := hImageTile
    imageBoundary := totalSlabBoundary D.deformedRegion (deformedCenterCarrier imageCenters)
      imageCarrier
    imageBoundary_eq := rfl
    boundaryMap := L.boundaryMap
    boundaryLift := lift
    boundaryLift_coe := fun _ ↦ rfl
    boundaryMap_formula := hformula
    boundaryMap_distortion := hdistortion
    imageNoncolumnPlate := L.imageNoncolumnPlate
    sourceLabel := L.sourceLabel
    imageLabel := L.imageLabel
    labels_preserved := L.labels_preserved
    sourceLabel_geometric := L.sourceLabel_geometric
    imageLabel_geometric := L.imageLabel_geometric }⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Set Tiling.AxisParallel Tiling.AxisParallel.Approximation Tiling.AxisParallel.Continuous
open scoped Pointwise

/-- Disjoint indexed parts of a packing have disjoint regular supports. -/
private theorem carrierRegularSupports_disjoint
    {K : Region} {T S U : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) (hST : S ⊆ T) (hUT : U ⊆ T)
    (hSU : Disjoint S U) : Disjoint (regularSupport K S) (regularSupport K U) := by
  let parts : Bool → Set Tiling.Plane
    | false => S
    | true => T \ S
  have hparts : Set.PairwiseDisjoint Set.univ parts := by
    intro i _ j _ hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact Set.disjoint_left.mpr fun _ hxS hxB ↦ hxB.2 hxS
    · exact Set.disjoint_left.mpr fun _ hxB hxS ↦ hxB.2 hxS
    · exact (hij rfl).elim
  have hunion : (⋃ i, parts i) = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      cases i
      · exact hST hi
      · exact hi.1
    · intro hxT
      by_cases hxS : x ∈ S
      · exact Set.mem_iUnion.mpr ⟨false, hxS⟩
      · exact Set.mem_iUnion.mpr ⟨true, hxT, hxS⟩
  have hdisj := (regularSupport_pairwiseDisjoint parts hparts hunion hTile).1
    (Set.mem_univ false) (Set.mem_univ true) (by decide)
  have hUS : U ⊆ T \ S := fun _ hxU ↦
    ⟨hUT hxU, fun hxS ↦ Set.disjoint_left.mp hSU hxS hxU⟩
  exact hdisj.mono_right (interior_mono (closure_mono (by
    simp only [Tiling.Polygonal.openUnion]
    intro z hz
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨⟨t.1, hUS t.2⟩, ht⟩)))

private theorem carrierSlabBases_partitionFacts
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) :
    (∀ P : VerticalPlate K T, P.base ⊆ X.base) ∧
    aggregateColumnBase K T ⊆ X.base ∧
    (∀ P Q : VerticalPlate K T, P ≠ Q → Disjoint P.base Q.base) ∧
    (∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
      Disjoint P.base (aggregateColumnBase K T)) := by
  have hslab := (relativeCarrier_verticalPlates hTile rfl X.base_regular.symm
    (fun a b ↦ by
      simpa only [inter_comm] using hTile.verticalCylinder_frontier_locallyFinite
        X.base_open X.base_regular (Icc a b) isCompact_Icc)).1
  have hreg : regularSupport K T = X.carrier :=
    regularSupport_eq_of_tilesOn
      (X.base_open.preimage Complex.continuous_re)
      (by rw [PeriodicVerticalCarrier.carrier, Complex.closure_preimage_re,
        Complex.interior_preimage_re, X.base_regular]) hTile
  have hmonotone {S : Set Tiling.Plane} (hS : S ⊆ T) :
      regularSupport K S ⊆ X.carrier := by
    rw [← hreg]
    apply interior_mono (closure_mono ?_)
    intro z hz
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨⟨t.1, hS t.2⟩, ht⟩
  have hPsub (P : VerticalPlate K T) : P.centres ⊆ T := by
    rintro _ ⟨t, _, rfl⟩
    exact t.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P x hx
    have hz : (x : ℂ) ∈ P.support := by
      rw [(hslab P).2]
      simpa using hx
    have h := hmonotone (hPsub P) hz
    simpa [PeriodicVerticalCarrier.carrier] using h
  · intro x hx
    have hz : (x : ℂ) ∈ regularSupport K (verticalColumnCentres K T) := by
      rw [aggregateColumnSupport_eq_cylinder X hTile]
      simpa using hx
    have h := hmonotone (Continuous.verticalColumnCentres_subset K T) hz
    simpa [PeriodicVerticalCarrier.carrier] using h
  · intro P Q hPQ
    have hcentres := verticalPlateCentres_pairwiseDisjoint K T
      (Set.mem_univ P) (Set.mem_univ Q) hPQ
    have hsupports := carrierRegularSupports_disjoint X hTile (hPsub P) (hPsub Q) hcentres
    apply Set.disjoint_left.mpr
    intro x hxP hxQ
    have hzP : (x : ℂ) ∈ regularSupport K P.centres := by
      rw [← VerticalPlate.support_eq_regularSupport, (hslab P).2]
      simpa using hxP
    have hzQ : (x : ℂ) ∈ regularSupport K Q.centres := by
      rw [← VerticalPlate.support_eq_regularSupport, (hslab Q).2]
      simpa using hxQ
    exact Set.disjoint_left.mp hsupports hzP hzQ
  · intro P hP
    have hcentres : Disjoint P.centres (verticalColumnCentres K T) := by
      apply Set.disjoint_left.mpr
      intro z hzP hzCol
      obtain ⟨Q, hzQ⟩ := Set.mem_iUnion.mp hzCol
      have hPQ : P ≠ Q.1 := fun h ↦ hP (h ▸ Q.2)
      exact Set.disjoint_left.mp
        (verticalPlateCentres_pairwiseDisjoint K T
          (Set.mem_univ P) (Set.mem_univ Q.1) hPQ) hzP hzQ
    have hsupports := carrierRegularSupports_disjoint X hTile (hPsub P)
      (Continuous.verticalColumnCentres_subset K T) hcentres
    apply Set.disjoint_left.mpr
    intro x hxP hxCol
    have hzP : (x : ℂ) ∈ regularSupport K P.centres := by
      rw [← VerticalPlate.support_eq_regularSupport, (hslab P).2]
      simpa using hxP
    have hzCol : (x : ℂ) ∈ regularSupport K (verticalColumnCentres K T) := by
      rw [aggregateColumnSupport_eq_cylinder X hTile]
      simpa using hxCol
    exact Set.disjoint_left.mp hsupports hzP hzCol

/-- An inhabited chamber cannot carry two distinct geometric slab labels. -/
private theorem carrierGapLabel_unique
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) {a b : ℝ} (hab : a < b)
    {L M : SlabCodeLabel K T}
    (hL : sourceGapHasLabel X a b L) (hM : sourceGapHasLabel X a b M) : L = M := by
  classical
  obtain ⟨x, hx⟩ := nonempty_Ioo.mpr hab
  obtain ⟨hPsub, hColsub, hPdisj, hColdisj⟩ := carrierSlabBases_partitionFacts X hTile
  cases L with
  | outside =>
      cases M with
      | outside => rfl
      | noncolumn P => exact False.elim ((hL hx) (hPsub P.1 (hM hx)))
      | columns => exact False.elim ((hL hx) (hColsub (hM hx)))
  | noncolumn P =>
      cases M with
      | outside => exact False.elim ((hM hx) (hPsub P.1 (hL hx)))
      | noncolumn Q =>
          have hPQ : P.1 = Q.1 := by
            by_contra h
            exact Set.disjoint_left.mp (hPdisj P.1 Q.1 h) (hL hx) (hM hx)
          exact congrArg SlabCodeLabel.noncolumn (Subtype.ext hPQ)
      | columns =>
          exact False.elim (Set.disjoint_left.mp (hColdisj P.1 P.2) (hL hx) (hM hx))
  | columns =>
      cases M with
      | outside => exact False.elim ((hM hx) (hColsub (hL hx)))
      | noncolumn P =>
          exact False.elim (Set.disjoint_left.mp (hColdisj P.1 P.2) (hM hx) (hL hx))
      | columns => rfl

/-- An open labelled slab lies away from every boundary in the complete partition. -/
private theorem carrierSlabBases_avoidBoundary
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) :
    (∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
      Disjoint P.base (totalSlabBoundary K T X)) ∧
    Disjoint (aggregateColumnBase K T) (totalSlabBoundary K T X) := by
  obtain ⟨hPsub, hColsub, hPdisj, hColdisj⟩ := carrierSlabBases_partitionFacts X hTile
  have hopen (P : VerticalPlate K T) : IsOpen P.base := by
    rw [verticalPlateBase_regularizedProjection X hTile P]
    exact isOpen_interior
  have hopenCol : IsOpen (aggregateColumnBase K T) := by
    rw [aggregateColumnBase_regularizedProjection X hTile]
    exact isOpen_interior
  have hcarrier : Disjoint X.base (frontier X.base) :=
    (disjoint_frontier_iff_isOpen.mpr X.base_open).symm
  constructor
  · intro P hP
    apply Set.disjoint_left.mpr
    intro x hxP hxB
    rcases hxB with (hxX | hxN) | hxC
    · exact Set.disjoint_left.mp hcarrier (hPsub P hxP) hxX
    · obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hxN
      by_cases hPQ : P = Q.1
      · subst P
        exact Set.disjoint_left.mp
          (disjoint_frontier_iff_isOpen.mpr (hopen Q.1)).symm hxP hxQ
      · exact Set.disjoint_left.mp ((hPdisj P Q.1 hPQ).frontier_right (hopen P)) hxP hxQ
    · exact Set.disjoint_left.mp ((hColdisj P hP).frontier_right (hopen P)) hxP hxC
  · apply Set.disjoint_left.mpr
    intro x hxC hxB
    rcases hxB with (hxX | hxN) | hxCol
    · exact Set.disjoint_left.mp hcarrier (hColsub hxC) hxX
    · obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hxN
      exact Set.disjoint_left.mp ((hColdisj P.1 P.2).symm.frontier_right hopenCol) hxC hxP
    · exact Set.disjoint_left.mp
        (disjoint_frontier_iff_isOpen.mpr hopenCol).symm hxC hxCol

private theorem integerBoundary_consecutive
    {B : Set ℝ} (point : ℤ → ℝ) (hmono : StrictMono point)
    (hrange : Set.range point = B) (i : ℤ) :
    ConsecutiveIn B (point i) (point (i + 1)) := by
  refine ⟨hrange ▸ Set.mem_range_self i, hrange ▸ Set.mem_range_self (i + 1),
    hmono (by omega), ?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hxB⟩
  obtain ⟨j, rfl⟩ := hrange.symm.subset hxB
  have hi : i < j := hmono.lt_iff_lt.mp hx.1
  have hj : j < i + 1 := hmono.lt_iff_lt.mp hx.2
  omega

/-- Complete chamber decoding for an individual noncolumn slab and the column aggregate. -/
private theorem carrierSlabBase_eq_labelledIntervals
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier)
    (point : ℤ → ℝ) (hmono : StrictMono point)
    (hrange : Set.range point = totalSlabBoundary K T X)
    (hbelow : ∀ z : ℝ, ∃ i : ℤ, point i ≤ z)
    (habove : ∀ z : ℝ, ∃ i : ℤ, z < point i)
    (label : ℤ → SlabCodeLabel K T)
    (hgeom : ∀ i, sourceGapHasLabel X (point i) (point (i + 1)) (label i)) :
    (∀ P : {P : VerticalPlate K T // ¬ IsVerticalColumn P},
      P.1.base = ⋃ i : {i : ℤ // label i = .noncolumn P}, Ioo (point i.1) (point (i.1 + 1))) ∧
    aggregateColumnBase K T =
      ⋃ i : {i : ℤ // label i = .columns}, Ioo (point i.1) (point (i.1 + 1)) := by
  classical
  obtain ⟨hPavoid, hCavoid⟩ := carrierSlabBases_avoidBoundary X hTile
  have hdecode (A : Set ℝ) (hopen : IsOpen A)
      (hfrontier : frontier A ⊆ totalSlabBoundary K T X)
      (havoid : Disjoint A (totalSlabBoundary K T X)) (L : SlabCodeLabel K T)
      (hmeaning : ∀ a b, sourceGapHasLabel X a b L ↔ Ioo a b ⊆ A) :
      A = ⋃ i : {i : ℤ // label i = L}, Ioo (point i.1) (point (i.1 + 1)) := by
    ext x
    constructor
    · intro hxA
      obtain ⟨i, hix, hxi⟩ := integerSequence_covers point hmono hbelow habove x
      have hxi' : point i < x := lt_of_le_of_ne hix (by
        intro heq
        exact Set.disjoint_left.mp havoid hxA
          (heq ▸ (hrange ▸ Set.mem_range_self i)))
      have hgap := integerBoundary_consecutive point hmono hrange i
      have hgapAvoid : Disjoint (Ioo (point i) (point (i + 1))) (frontier A) := by
        apply Set.disjoint_left.mpr
        intro y hy hyFront
        have hyB : y ∈ Ioo (point i) (point (i + 1)) ∩ totalSlabBoundary K T X :=
          ⟨hy, hfrontier hyFront⟩
        rw [hgap.2.2.2] at hyB
        exact hyB
      have hgapA : Ioo (point i) (point (i + 1)) ⊆ A := by
        rcases gap_subset_or_subset_exterior hopen hgapAvoid with hin | hout
        · exact hin
        · exact False.elim ((hout ⟨hxi', hxi⟩) (subset_closure hxA))
      have hlabel : label i = L := carrierGapLabel_unique X hTile (hmono (by omega))
        (hgeom i) ((hmeaning _ _).mpr hgapA)
      exact Set.mem_iUnion.mpr ⟨⟨i, hlabel⟩, hxi', hxi⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      have hg := hgeom i.1
      rw [i.2] at hg
      exact (hmeaning _ _).mp hg hi
  constructor
  · intro P
    apply hdecode P.1.base
    · rw [verticalPlateBase_regularizedProjection X hTile P.1]
      exact isOpen_interior
    · intro x hx
      exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨P, hx⟩))
    · exact hPavoid P.1 P.2
    · intro a b
      rfl
  · apply hdecode (aggregateColumnBase K T)
    · rw [aggregateColumnBase_regularizedProjection X hTile]
      exact isOpen_interior
    · exact fun _ hx ↦ Or.inr hx
    · exact hCavoid
    · intro a b
      rfl

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Set Tiling.AxisParallel Tiling.AxisParallel.Approximation Tiling.AxisParallel.Continuous
open scoped Pointwise

/-- Prescribed whole-plane geometry, shared by exploratory and final maps. -/
private theorem wholePlanePrescribedLabelledGeometry
    (C : ApproximationContext.{0}) (X : PeriodicVerticalCarrier)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (htarget : C.target = X.carrier) (hTile : TilesOn C.region C.centres C.target)
    (hFHC : HasFiniteHorizontalComplexity C.centres) (hWhole : X.base = Set.univ)
    (hSigns : PreservesHorizontalTranslatedVertexSigns C phi)
    (hDistances : ControlsHorizontalTranslatedVertexDistances C phi) :
    Nonempty (ProperCarrierLabelledTransport C X phi D P.fullCenters X) := by
  classical
  have hTileX : TilesOn C.region C.centres X.carrier := htarget ▸ hTile
  have hImageTile : TilesOn D.deformedRegion (deformedCenterCarrier P.fullCenters)
      X.carrier := by
    simpa only [PeriodicVerticalCarrier.carrier, hWhole, Set.preimage_univ] using
      P.full_tilesOn
  obtain ⟨H, hH, hvertex⟩ := translatedVertexHomeomorph_exists C X phi htarget hTile
    hFHC hSigns hDistances
  have hvertex' (v : C.region.vertices) (t : C.centres) :
      H (v.1 + t.1).re = (mapPoint phi (C.vertexPoint v.1 v.2) + P.fullCenters t).re := by
    rw [P.fullCenters_apply]
    exact hvertex v t
  have hprojection := placedTileHorizontalProjection_image C phi D P.fullCenters H hH
    P.fullCenters_apply hvertex'
  have hselected := selectedSubfamily_regularizedProjection_image C phi D P.fullCenters H
    hH P.fullCenters_apply hprojection
  have hcontact := deformation_preservesProperHorizontalContact C phi D P hSigns
  let e := deformation_verticalPlateEquiv C phi D P hcontact
  have hcentres (Q : VerticalPlate C.region C.centres) :
      (e Q).centres = deformedCenterCarrierOn P.fullCenters
        {t : C.centres | t.1 ∈ Q.centres} :=
    deformation_verticalPlateEquiv_centres C phi D P hcontact Q
  have hcolumns (Q : VerticalPlate C.region C.centres) :
      IsVerticalColumn Q ↔ IsVerticalColumn (e Q) :=
    deformation_preservesColumns C phi D P hcontact hSigns Q
  let eNC : {Q : VerticalPlate C.region C.centres // ¬ IsVerticalColumn Q} ≃
      {Q : VerticalPlate D.deformedRegion (deformedCenterCarrier P.fullCenters) //
        ¬ IsVerticalColumn Q} := e.subtypeEquiv fun Q ↦ (hcolumns Q).not
  have hplateBase (Q : VerticalPlate C.region C.centres) : (e Q).base = H '' Q.base := by
    rw [verticalPlateBase_regularizedProjection X hImageTile, hcentres,
      hselected Q.centres (by rintro _ ⟨t, -, rfl⟩; exact t.2),
      ← verticalPlateBase_regularizedProjection X hTileX Q]
  have hcolumnCentres : verticalColumnCentres D.deformedRegion
      (deformedCenterCarrier P.fullCenters) = deformedCenterCarrierOn P.fullCenters
        {t : C.centres | t.1 ∈ verticalColumnCentres C.region C.centres} := by
    ext z
    constructor
    · intro hz
      obtain ⟨Q, hzQ⟩ := Set.mem_iUnion.mp hz
      obtain ⟨R, hRQ⟩ := e.surjective Q.1
      have hRcol : IsVerticalColumn R := (hcolumns R).mpr (hRQ ▸ Q.2)
      rw [← hRQ, hcentres] at hzQ
      obtain ⟨t, ht, rfl⟩ := hzQ
      exact ⟨t, Set.mem_iUnion.mpr ⟨⟨R, hRcol⟩, ht⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨Q, htQ⟩ := Set.mem_iUnion.mp ht
      apply Set.mem_iUnion.mpr
      refine ⟨⟨e Q.1, (hcolumns Q.1).mp Q.2⟩, ?_⟩
      rw [hcentres]
      exact ⟨t, htQ, rfl⟩
  have hcolumnBase : aggregateColumnBase D.deformedRegion
      (deformedCenterCarrier P.fullCenters) = H '' aggregateColumnBase C.region C.centres := by
    rw [aggregateColumnBase_regularizedProjection X hImageTile, hcolumnCentres,
      hselected _ (Continuous.verticalColumnCentres_subset _ _),
      ← aggregateColumnBase_regularizedProjection X hTileX]
  have hcarrierBase : X.base = H '' X.base := by simp [hWhole]
  obtain ⟨L⟩ := labelledSlabBoundaryTransport_exists X X hTileX H hH eNC hcarrierBase
    (fun Q ↦ hplateBase Q.1) hcolumnBase
  refine ⟨{
    scalarHomeomorph := H
    scalarHomeomorph_strictMono := hH
    scalarHomeomorph_translatedVertex := hvertex'
    carrier_base_image := hcarrierBase
    horizontalContact_iff := hcontact
    imageNoncolumnPlate := eNC
    imageNoncolumnPlate_centres := fun Q ↦ hcentres Q.1
    imageNoncolumnPlate_base := fun Q ↦ hplateBase Q.1
    aggregateColumnBase_image := hcolumnBase
    boundaryMap := L.boundaryMap
    boundaryMap_apply := L.boundaryMap_apply
    sourceLabel := L.sourceLabel
    imageLabel := L.imageLabel
    labels_preserved := L.labels_preserved
    sourceLabel_geometric := L.sourceLabel_geometric
    imageLabel_geometric := ?_ }⟩
  intro a b ha hgap
  have hgeom := L.imageLabel_geometric ha hgap
  cases hlabel : L.imageLabel ⟨a, ha⟩ <;> simpa only [hlabel] using hgeom

private theorem wholePlanePreAlphabetTransport_exists :
    ∀ (C : ApproximationContext.{0}) (X : PeriodicVerticalCarrier),
    C.target = X.carrier → TilesOn C.region C.centres C.target →
    HasFiniteHorizontalComplexity C.centres →
    (totalSlabBoundary C.region C.centres X).Nonempty → X.base = Set.univ →
      Nonempty (FirstCarrierPreAlphabetTransport C X) := by
  intro C X htarget hTile hFHC hBoundary hWhole
  classical
  have hTileX : TilesOn C.region C.centres X.carrier := htarget ▸ hTile
  have hTilePlane : TilesOn C.region C.centres Set.univ := by
    simpa only [PeriodicVerticalCarrier.carrier, hWhole, Set.preimage_univ] using hTileX
  obtain ⟨epsilonGood, hGoodPos, hGoodThreshold⟩ := isGoodApproximation_of_sufficientlyFine C
  obtain ⟨epsilonSigns, hSignsPos, hSignsThreshold⟩ :=
    approximation_preservesGlobalHorizontalSign C hTilePlane hFHC
  obtain ⟨epsilonDistances, hDistancesPos, hDistancesThreshold⟩ :=
    carrierApproximation_globalDistortion C X htarget hTile hFHC
  let epsilon := min epsilonGood (min epsilonSigns epsilonDistances)
  have hepsilon : 0 < epsilon := lt_min hGoodPos (lt_min hSignsPos hDistancesPos)
  obtain ⟨phi, hApprox⟩ := exists_epsilonApproximation C epsilon hepsilon
  have hGood : IsGoodApproximation C phi :=
    hGoodThreshold phi (hApprox.of_le (min_le_left _ _))
  have hSigns : PreservesHorizontalTranslatedVertexSigns C phi :=
    hSignsThreshold phi (hApprox.of_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hDistances : ControlsHorizontalTranslatedVertexDistances C phi :=
    hDistancesThreshold phi (hApprox.of_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨D⟩ := exists_rationalPolygonDeformation C phi hGood
  obtain ⟨P⟩ := exists_twoStageDeformationSupportTransport C phi D hTilePlane
  let imageCenters := P.fullCenters
  have hImage (t : C.centres) : imageCenters t = mapPoint phi (C.centrePoint t.1 t.2) :=
    P.fullCenters_apply t
  have hImageTile : TilesOn D.deformedRegion (deformedCenterCarrier imageCenters)
      X.carrier := by
    simpa only [PeriodicVerticalCarrier.carrier, hWhole, Set.preimage_univ] using
      P.full_tilesOn
  obtain ⟨L⟩ := wholePlanePrescribedLabelledGeometry C X phi D P htarget hTile
    hFHC hWhole hSigns hDistances
  let B := totalSlabBoundary C.region C.centres X
  have hrepresentation (x : B) : ∃ v : C.region.vertices, ∃ t : C.centres,
      x.1 = (v.1 + t.1).re := by
    obtain ⟨v, hv, t, ht, hvt⟩ := slabCodeBoundaries_fromVertices X hTileX x.2
    exact ⟨⟨v, hv⟩, ⟨t, ht⟩, hvt⟩
  have hcoordinate (x : B) : x.1 ∈ C.coordinateSpace := by
    obtain ⟨v, t, hvt⟩ := hrepresentation x
    rw [hvt, Complex.add_re]
    exact C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2) (C.centre_re_mem t.1 t.2)
  let lift : B → C.coordinateSpace := fun x ↦ ⟨x.1, hcoordinate x⟩
  have hformula (x : B) : (L.boundaryMap x).1 = mapScalar phi (lift x) := by
    obtain ⟨v, t, hvt⟩ := hrepresentation x
    have hlift : lift x =
        ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ + ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
      apply Subtype.ext
      simp [lift, hvt, Complex.add_re]
    rw [L.boundaryMap_apply, hvt, L.scalarHomeomorph_translatedVertex, hImage, hlift]
    simp only [mapPoint, mapScalar, ApproximationContext.vertexPoint,
      ApproximationContext.centrePoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, map_add, Rat.cast_add, add_zero]
  have hdistortion {a b : B} (hab : a.1 < b.1) :
      (1 / 2 : ℝ) * (b.1 - a.1) ≤ (L.boundaryMap b).1 - (L.boundaryMap a).1 ∧
      (L.boundaryMap b).1 - (L.boundaryMap a).1 ≤ 2 * (b.1 - a.1) := by
    obtain ⟨v, s, ha⟩ := hrepresentation a
    obtain ⟨w, t, hb⟩ := hrepresentation b
    have haMap : (mapPoint phi (C.vertexPoint v.1 v.2) +
        mapPoint phi (C.centrePoint s.1 s.2)).re = L.scalarHomeomorph a.1 := by
      rw [ha, L.scalarHomeomorph_translatedVertex, hImage]
    have hbMap : (mapPoint phi (C.vertexPoint w.1 w.2) +
        mapPoint phi (C.centrePoint t.1 t.2)).re = L.scalarHomeomorph b.1 := by
      rw [hb, L.scalarHomeomorph_translatedVertex, hImage]
    have hd := hDistances v w s t
    rw [← ha, ← hb, haMap, hbMap, abs_of_pos (sub_pos.mpr hab),
      abs_of_pos (sub_pos.mpr (L.scalarHomeomorph_strictMono hab))] at hd
    simpa only [L.boundaryMap_apply] using hd
  refine ⟨{
    source_target_eq := htarget
    source_tiles := hTile
    source_finiteHorizontalComplexity := hFHC
    sourceBoundary_nonempty := hBoundary
    phi := phi
    horizontalOrder := hSigns
    deformation := D
    imageCenters := imageCenters
    imageCenters_apply := hImage
    imageCarrier := X
    imageTiles := hImageTile
    imageBoundary := totalSlabBoundary D.deformedRegion (deformedCenterCarrier imageCenters) X
    imageBoundary_eq := rfl
    boundaryMap := L.boundaryMap
    boundaryLift := lift
    boundaryLift_coe := fun _ ↦ rfl
    boundaryMap_formula := hformula
    boundaryMap_distortion := hdistortion
    imageNoncolumnPlate := L.imageNoncolumnPlate
    sourceLabel := L.sourceLabel
    imageLabel := L.imageLabel
    labels_preserved := L.labels_preserved
    sourceLabel_geometric := L.sourceLabel_geometric
    imageLabel_geometric := ?_ }⟩
  intro a b ha hgap
  have hgeom := L.imageLabel_geometric ha hgap
  cases hlabel : L.imageLabel ⟨a, ha⟩ <;> simpa only [hlabel] using hgeom

private theorem firstCarrierPreAlphabetTransport_exists :
    ∀ (C : ApproximationContext.{0}) (X : PeriodicVerticalCarrier),
    C.target = X.carrier → TilesOn C.region C.centres C.target →
    HasFiniteHorizontalComplexity C.centres →
    (totalSlabBoundary C.region C.centres X).Nonempty →
      Nonempty (FirstCarrierPreAlphabetTransport C X) := by
  intro C X htarget hTile hFHC hBoundary
  by_cases hWhole : X.base = Set.univ
  · exact wholePlanePreAlphabetTransport_exists C X htarget hTile hFHC hBoundary hWhole
  · exact properCarrierPreAlphabetTransport_exists C X htarget hTile hFHC hBoundary hWhole

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Set Tiling.AxisParallel Tiling.AxisParallel.Approximation Tiling.AxisParallel.Continuous
open scoped Pointwise

private structure FirstImagePeriodicBoundary
    {C : Tiling.AxisParallel.Approximation.ApproximationContext.{0}}
    {X : PeriodicVerticalCarrier} (F : FirstCarrierPreAlphabetTransport C X) where
  period : ℝ
  period_pos : 0 < period
  boundary_periodic : period +ᵥ F.imageBoundary = F.imageBoundary
  boundary_relativelyDense : ∃ R > 0, ∀ x : ℝ,
    ∃ y ∈ F.imageBoundary, |y - x| < R
  noncolumnSupport_periodic : ∀ P,
    Tiling.RationalPolygonal.SetPeriodicBy (F.imageNoncolumnPlate P).1.support
      (period : ℂ)
  columnSupport_periodic : Tiling.RationalPolygonal.SetPeriodicBy
    (Tiling.AxisParallel.regularSupport F.deformation.deformedRegion
      (Tiling.AxisParallel.Continuous.verticalColumnCentres
        F.deformation.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier F.imageCenters)))
    (period : ℂ)

private structure FirstCarrierCodeTransport
    (C : Tiling.AxisParallel.Approximation.ApproximationContext.{0})
    (X : PeriodicVerticalCarrier)
    extends FirstCarrierPreAlphabetTransport C X where
  gapAlphabet : Finset ℝ
  gap_pos : ∀ g ∈ gapAlphabet, 0 < g
  gap_complete : ∀ {a b : ℝ}, ConsecutiveIn
    (totalSlabBoundary C.region C.centres X) a b → b - a ∈ gapAlphabet
  gapLift : ↑gapAlphabet → C.coordinateSpace
  gapLift_coe : ∀ g, (gapLift g : ℝ) = g.1
  boundaryMap_gap : ∀ {a b : ℝ}
    (h : ConsecutiveIn (totalSlabBoundary C.region C.centres X) a b),
    (boundaryMap ⟨b, h.2.1⟩).1 - (boundaryMap ⟨a, h.1⟩).1 =
      Tiling.AxisParallel.Approximation.mapScalar phi
        (gapLift ⟨b - a, gap_complete h⟩)

private theorem addPeriodic_iff_vadd
    {G : Type*} [AddCommGroup G] {A : Set G} {p : G} :
    (∀ x, x + p ∈ A ↔ x ∈ A) ↔ p +ᵥ A = A := by
  constructor
  · intro h
    ext x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using (h (-p + x)).symm
  · intro h x
    have hx := Set.ext_iff.mp h (x + p)
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      add_comm, add_left_comm, add_assoc] using hx.symm

private theorem planeSupportPeriod_reImage
    {A : Set Tiling.Plane} {p : ℝ}
    (hA : Tiling.RationalPolygonal.SetPeriodicBy A (p : ℂ)) :
    p +ᵥ (Complex.re '' A) = Complex.re '' A := by
  apply addPeriodic_iff_vadd.mp
  intro x
  constructor
  · rintro ⟨z, hz, hzx⟩
    refine ⟨z - (p : ℂ), ?_, ?_⟩
    · apply (hA (z - (p : ℂ))).mp
      simpa using hz
    · simp only [Complex.sub_re, Complex.ofReal_re]
      linarith
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z + (p : ℂ), (hA z).mpr hz, by simp⟩

private theorem carrierSlabSupports_commonPeriod_totalBoundary
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) {p : ℝ}
    (hplates : ∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
      Tiling.RationalPolygonal.SetPeriodicBy P.support (p : ℂ))
    (hcolumns : Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K (verticalColumnCentres K T)) (p : ℂ)) :
    p +ᵥ X.base = X.base ∧
      p +ᵥ totalSlabBoundary K T X = totalSlabBoundary K T X := by
  classical
  let NC := {P : VerticalPlate K T // ¬ IsVerticalColumn P}
  let parts : Option NC → Set Tiling.Plane
    | none => verticalColumnCentres K T
    | some P => P.1.centres
  have hcover : (⋃ i, parts i) = T := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      cases i with
      | none =>
          obtain ⟨P, hz⟩ := Set.mem_iUnion.mp hi
          obtain ⟨t, _, rfl⟩ := hz
          exact t.2
      | some P =>
          obtain ⟨t, _, rfl⟩ := hi
          exact t.2
    · intro hz
      have hzP : z ∈ ⋃ P : VerticalPlate K T, P.centres := by
        rw [iUnion_verticalPlateCentres]
        exact hz
      obtain ⟨P, hzP⟩ := Set.mem_iUnion.mp hzP
      by_cases hcol : IsVerticalColumn P
      · exact Set.mem_iUnion.mpr ⟨none, Set.mem_iUnion.mpr ⟨⟨P, hcol⟩, hzP⟩⟩
      · exact Set.mem_iUnion.mpr ⟨some ⟨P, hcol⟩, hzP⟩
  have hpartperiod (i : Option NC) : Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K (parts i)) (p : ℂ) := by
    cases i with
    | none => exact hcolumns
    | some P => exact hplates P.1 P.2
  let U : Set Tiling.Plane := ⋃ i, regularSupport K (parts i)
  have hUperiod : Tiling.RationalPolygonal.SetPeriodicBy U (p : ℂ) := by
    intro z
    simp only [U, Set.mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨i, (hpartperiod i z).mp hi⟩,
      fun ⟨i, hi⟩ ↦ ⟨i, (hpartperiod i z).mpr hi⟩⟩
  have hUeq : (p : ℂ) +ᵥ U = U := addPeriodic_iff_vadd.mp hUperiod
  have hregularPeriod : Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K T) (p : ℂ) := by
    rw [← hcover, regularSupport_iUnion]
    apply addPeriodic_iff_vadd.mpr
    change (p : ℂ) +ᵥ interior (closure U) = interior (closure U)
    rw [← interior_vadd, ← closure_vadd, hUeq]
  have hregular : interior (closure X.carrier) = X.carrier := by
    change interior (closure (Complex.re ⁻¹' X.base)) = Complex.re ⁻¹' X.base
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, X.base_regular]
  have hsupport : regularSupport K T = Complex.re ⁻¹' X.base :=
    regularSupport_eq_of_tilesOn (X.base_open.preimage Complex.continuous_re) hregular hTile
  have hre : Complex.re '' regularSupport K T = X.base := by
    rw [hsupport]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨(x : ℂ), hx, by simp⟩
  have hbase : p +ᵥ X.base = X.base := by
    rw [← hre]
    exact planeSupportPeriod_reImage hregularPeriod
  have hplateBase (P : NC) : p +ᵥ P.1.base = P.1.base :=
    planeSupportPeriod_reImage (hplates P.1 P.2)
  have hcolumnBase : p +ᵥ aggregateColumnBase K T = aggregateColumnBase K T :=
    planeSupportPeriod_reImage hcolumns
  refine ⟨hbase, addPeriodic_iff_vadd.mp ?_⟩
  have hcarrierMem := addPeriodic_iff_vadd.mpr
    (OneDimensional.FiniteInterval.frontier_periodic hbase)
  have hplateMem (P : NC) := addPeriodic_iff_vadd.mpr
    (OneDimensional.FiniteInterval.frontier_periodic (hplateBase P))
  have hcolumnMem := addPeriodic_iff_vadd.mpr
    (OneDimensional.FiniteInterval.frontier_periodic hcolumnBase)
  intro x
  simp only [totalSlabBoundary, Set.mem_union, Set.mem_iUnion,
    hcarrierMem, hplateMem, hcolumnMem]

private theorem nonempty_periodicSet_relativelyDense
    {B : Set ℝ} (hne : B.Nonempty) {p : ℝ} (hp : 0 < p)
    (hperiod : p +ᵥ B = B) :
    ∃ R > 0, ∀ x : ℝ, ∃ y ∈ B, |y - x| < R := by
  obtain ⟨a, ha⟩ := hne
  have hmem := addPeriodic_iff_vadd.mpr hperiod
  have hfun : Function.Periodic (fun x : ℝ ↦ x ∈ B) p :=
    fun x ↦ propext (hmem x)
  refine ⟨p + 1, by linarith, ?_⟩
  intro x
  let k : ℤ := ⌊(x - a) / p⌋
  refine ⟨a + (k : ℝ) * p, ?_, ?_⟩
  · have h := hfun.zsmul k a
    simpa only [zsmul_eq_mul] using (eq_iff_iff.mp h).mpr ha
  · have hlo := (le_div_iff₀ hp).mp (Int.floor_le ((x - a) / p))
    have hhi := (div_lt_iff₀ hp).mp (Int.lt_floor_add_one ((x - a) / p))
    apply abs_lt.mpr
    dsimp [k]
    constructor <;> nlinarith

private theorem firstImagePeriodicBoundary_exists
    {C : ApproximationContext.{0}} {X : PeriodicVerticalCarrier}
    (F : FirstCarrierPreAlphabetTransport C X) :
    Nonempty (FirstImagePeriodicBoundary F) := by
  obtain ⟨p, hp, hplates, hcolumns⟩ := rationalPeriodicCarrierPlate_periodic
    F.imageCarrier F.imageTiles F.deformation.rational_vertices
  have hperiod := (carrierSlabSupports_commonPeriod_totalBoundary
    F.imageCarrier F.imageTiles hplates hcolumns).2
  rw [← F.imageBoundary_eq] at hperiod
  have hnonempty : F.imageBoundary.Nonempty := by
    obtain ⟨a, ha⟩ := F.sourceBoundary_nonempty
    exact ⟨F.boundaryMap ⟨a, ha⟩, (F.boundaryMap ⟨a, ha⟩).2⟩
  exact ⟨{
    period := p
    period_pos := hp
    boundary_periodic := hperiod
    boundary_relativelyDense := nonempty_periodicSet_relativelyDense hnonempty hp hperiod
    noncolumnSupport_periodic := fun P ↦
      hplates (F.imageNoncolumnPlate P).1 (F.imageNoncolumnPlate P).2
    columnSupport_periodic := hcolumns }⟩

private theorem orderIso_consecutive
    {A B : Set ℝ} (e : A ≃o B) {a b : ℝ} (h : ConsecutiveIn A a b) :
    ConsecutiveIn B (e ⟨a, h.1⟩).1 (e ⟨b, h.2.1⟩).1 := by
  refine ⟨(e ⟨a, h.1⟩).2, (e ⟨b, h.2.1⟩).2,
    e.strictMono h.2.2.1, ?_⟩
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hz
  let c : A := e.symm ⟨z, hz.2⟩
  have hac : a < c.1 := by
    have hc := e.symm.strictMono
      (show e ⟨a, h.1⟩ < (⟨z, hz.2⟩ : B) from hz.1.1)
    have hc' : (⟨a, h.1⟩ : A) < c := by
      simpa only [OrderIso.symm_apply_apply] using hc
    exact hc'
  have hcb : c.1 < b := by
    have hc := e.symm.strictMono
      (show (⟨z, hz.2⟩ : B) < e ⟨b, h.2.1⟩ from hz.1.2)
    have hc' : c < (⟨b, h.2.1⟩ : A) := by
      simpa only [OrderIso.symm_apply_apply] using hc
    exact hc'
  have hc : c.1 ∈ Ioo a b ∩ A := ⟨⟨hac, hcb⟩, c.2⟩
  rw [h.2.2.2] at hc
  exact hc

private theorem periodicSet_consecutive_gap_le_period
    {B : Set ℝ} {p : ℝ} (hp : 0 < p) (hperiod : p +ᵥ B = B)
    {a b : ℝ} (h : ConsecutiveIn B a b) : b - a ≤ p := by
  have hshift : a + p ∈ B := (addPeriodic_iff_vadd.mpr hperiod a).mpr h.1
  by_contra hnot
  have hgap : p < b - a := lt_of_not_ge hnot
  have hx : a + p ∈ Ioo a b ∩ B := ⟨⟨by linarith, by linarith⟩, hshift⟩
  rw [h.2.2.2] at hx
  exact hx

private theorem firstCarrierCodeTransport_exists
    {C : ApproximationContext.{0}} {X : PeriodicVerticalCarrier}
    (F : FirstCarrierPreAlphabetTransport C X) (W : FirstImagePeriodicBoundary F) :
    ∃ F' : FirstCarrierCodeTransport C X,
      F'.toFirstCarrierPreAlphabetTransport = F := by
  classical
  let B : Set ℝ := totalSlabBoundary C.region C.centres X
  have hTileX : TilesOn C.region C.centres X.carrier := by
    simpa only [F.source_target_eq] using F.source_tiles
  have hgapBound {a b : ℝ} (h : ConsecutiveIn B a b) : b - a ≤ 2 * W.period := by
    have hi := periodicSet_consecutive_gap_le_period W.period_pos W.boundary_periodic
      (orderIso_consecutive F.boundaryMap h)
    have hd := (F.boundaryMap_distortion (a := ⟨a, h.1⟩)
      (b := ⟨b, h.2.1⟩) h.2.2.1).1
    dsimp only at hi hd
    linarith
  let G : Set ℝ := {g | ∃ a b : ℝ, ConsecutiveIn B a b ∧ g = b - a}
  have hGfinite : G.Finite := by
    apply (horizontalBoundedDifferences_finite (K := C.region) F.source_finiteHorizontalComplexity
      (2 * W.period)).subset
    rintro g ⟨a, b, hgap, rfl⟩
    refine ⟨a, slabCodeBoundaries_fromVertices X hTileX hgap.1,
      b, slabCodeBoundaries_fromVertices X hTileX hgap.2.1, rfl, ?_⟩
    rw [abs_of_pos (sub_pos.mpr hgap.2.2.1)]
    exact hgapBound hgap
  let alphabet : Finset ℝ := hGfinite.toFinset
  have hgapPos (g : ℝ) (hg : g ∈ alphabet) : 0 < g := by
    obtain ⟨a, b, hgap, rfl⟩ := hGfinite.mem_toFinset.mp hg
    exact sub_pos.mpr hgap.2.2.1
  have hgapComplete {a b : ℝ} (h : ConsecutiveIn B a b) : b - a ∈ alphabet :=
    hGfinite.mem_toFinset.mpr ⟨a, b, h, rfl⟩
  have hWitness (g : ↑alphabet) :
      ∃ a b : ℝ, ConsecutiveIn B a b ∧ (g : ℝ) = b - a :=
    hGfinite.mem_toFinset.mp g.2
  choose a b hgap hdelta using hWitness
  let gapLift : ↑alphabet → C.coordinateSpace := fun g ↦
    F.boundaryLift ⟨b g, (hgap g).2.1⟩ - F.boundaryLift ⟨a g, (hgap g).1⟩
  have hgapLift (g : ↑alphabet) : (gapLift g : ℝ) = g.1 := by
    simp only [gapLift, Submodule.coe_sub, F.boundaryLift_coe]
    exact (hdelta g).symm
  have hmapGap {a b : ℝ} (h : ConsecutiveIn B a b) :
      (F.boundaryMap ⟨b, h.2.1⟩).1 - (F.boundaryMap ⟨a, h.1⟩).1 =
        mapScalar F.phi (gapLift ⟨b - a, hgapComplete h⟩) := by
    have hlift : gapLift ⟨b - a, hgapComplete h⟩ =
        F.boundaryLift ⟨b, h.2.1⟩ - F.boundaryLift ⟨a, h.1⟩ := by
      apply Subtype.ext
      simp only [hgapLift, Submodule.coe_sub, F.boundaryLift_coe]
    rw [F.boundaryMap_formula, F.boundaryMap_formula, hlift]
    simp only [mapScalar, map_sub, Rat.cast_sub]
  exact ⟨{
    toFirstCarrierPreAlphabetTransport := F
    gapAlphabet := alphabet
    gap_pos := hgapPos
    gap_complete := hgapComplete
    gapLift := gapLift
    gapLift_coe := hgapLift
    boundaryMap_gap := hmapGap }, rfl⟩

private theorem totalSlabBoundary_boundedWindowFinite
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) (hFHC : HasFiniteHorizontalComplexity T) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q → (totalSlabBoundary K T X ∩ Q).Finite := by
  have hAflc : HasFLC (horizontalTranslatedVertices K T) := by
    rw [horizontalTranslatedVertices_eq_projection_add_vertices]
    exact hFHC.add_finset (K.vertexFinset.image Complex.re)
  intro Q hQ
  apply (hAflc.1 Q hQ).subset
  intro x hx
  exact ⟨slabCodeBoundaries_fromVertices X hTile hx.1, hx.2⟩

private theorem totalSlabBoundary_boundedDifferences_finite
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) (hFHC : HasFiniteHorizontalComplexity T) (R : ℝ) :
    (horizontalBoundedDifferences (totalSlabBoundary K T X) R).Finite := by
  apply (horizontalBoundedDifferences_finite (K := K) hFHC R).subset
  rintro g ⟨a, ha, b, hb, hdelta, hbound⟩
  exact ⟨a, slabCodeBoundaries_fromVertices X hTile ha,
    b, slabCodeBoundaries_fromVertices X hTile hb, hdelta, hbound⟩

private theorem totalSlabBoundary_orderData
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) (hFHC : HasFiniteHorizontalComplexity T)
    (hne : (totalSlabBoundary K T X).Nonempty)
    (hcase : X.base ≠ Set.univ ∨ ∃ p : ℝ, 0 < p ∧
      p +ᵥ totalSlabBoundary K T X = totalSlabBoundary K T X) :
    Nonempty (HorizontalOrderData (totalSlabBoundary K T X)) := by
  let A : Set ℝ := horizontalTranslatedVertices K T
  let B : Set ℝ := totalSlabBoundary K T X
  have hsub : B ⊆ A := slabCodeBoundaries_fromVertices X hTile
  have hAflc : HasFLC A := by
    dsimp only [A]
    rw [horizontalTranslatedVertices_eq_projection_add_vertices]
    exact hFHC.add_finset (K.vertexFinset.image Complex.re)
  obtain ⟨delta, hdelta, hseparated⟩ := hAflc.uniformlyDiscrete
  have hdense : ∃ R > 0, ∀ x : ℝ, ∃ y ∈ B, |y - x| < R := by
    rcases hcase with hproper | ⟨p, hp, hperiod⟩
    · have hfront : (frontier X.base).Nonempty := by
        by_contra hnot
        rcases frontier_eq_empty_iff.mp (Set.not_nonempty_iff_eq_empty.mp hnot)
          with hempty | hwhole
        · exact (MeasureTheory.nonempty_of_measure_ne_zero X.base_nonnull).ne_empty hempty
        · exact hproper hwhole
      obtain ⟨R, hR, hfrontDense⟩ := nonempty_periodicSet_relativelyDense
        hfront X.period_pos (OneDimensional.FiniteInterval.frontier_periodic X.base_periodic)
      refine ⟨R, hR, ?_⟩
      intro x
      obtain ⟨y, hy, hdist⟩ := hfrontDense x
      exact ⟨y, Or.inl (Or.inl hy), hdist⟩
    · exact nonempty_periodicSet_relativelyDense hne hp hperiod
  apply delone_has_integerOrderData
  · refine ⟨delta, hdelta, ?_⟩
    intro a ha b hb hab
    simpa only [Real.dist_eq] using hseparated a (hsub ha) b (hsub hb) hab
  · exact hdense
  · exact totalSlabBoundary_boundedDifferences_finite X hTile hFHC

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Set Tiling.AxisParallel Tiling.AxisParallel.Approximation Tiling.AxisParallel.Continuous
open scoped Pointwise

private theorem finalApproximation_afterGapAlphabet :
    ∀ {C : ApproximationContext.{0}} {X : PeriodicVerticalCarrier}
      (F : FirstCarrierCodeTransport C X),
    ∃ epsilon > 0,
      (X.base ≠ Set.univ → ∃ P : PeriodicBandData C,
        P.base = X.base ∧ IsPeriodicBandFineness P epsilon) ∧
      ∀ phi : C.coordinateSpace →ₗ[ℚ] ℚ,
        IsEpsilonApproximation C epsilon phi →
          IsEpsilonApproximation C 1 phi ∧ IsGoodApproximation C phi ∧
          PreservesHorizontalTranslatedVertexSigns C phi ∧
          ControlsHorizontalTranslatedVertexDistances C phi ∧
          Function.Injective (fun g : ↑F.gapAlphabet ↦ mapScalar phi (F.gapLift g)) := by
  intro C X F
  classical
  have hgapMem (g : ℝ) (hg : g ∈ F.gapAlphabet) : g ∈ C.coordinateSpace := by
    have hmem := (F.gapLift ⟨g, hg⟩).property
    rwa [F.gapLift_coe] at hmem
  obtain ⟨epsilonGap, hGapPos, hGapThreshold⟩ :=
    approximation_separatesHorizontalAlphabet C F.gapAlphabet hgapMem
  obtain ⟨epsilonGood, hGoodPos, hGoodThreshold⟩ := isGoodApproximation_of_sufficientlyFine C
  obtain ⟨epsilonSigns, hSignsPos, hSignsThreshold⟩ := carrierApproximation_globalSigns
    C X F.source_target_eq F.source_tiles F.source_finiteHorizontalComplexity
  obtain ⟨epsilonDistances, hDistancesPos, hDistancesThreshold⟩ :=
    carrierApproximation_globalDistortion
    C X F.source_target_eq F.source_tiles F.source_finiteHorizontalComplexity
  let epsilon₀ := min 1 (min epsilonGood (min epsilonSigns (min epsilonDistances epsilonGap)))
  have hε₀ : 0 < epsilon₀ := lt_min zero_lt_one
    (lt_min hGoodPos (lt_min hSignsPos (lt_min hDistancesPos hGapPos)))
  have hε₀one : epsilon₀ ≤ 1 := min_le_left _ _
  have hε₀good : epsilon₀ ≤ epsilonGood := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀signs : epsilon₀ ≤ epsilonSigns :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hε₀distances : epsilon₀ ≤ epsilonDistances :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_left _ _)
  have hε₀gap : epsilon₀ ≤ epsilonGap :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)
  have hproperties (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (hphi : IsEpsilonApproximation C epsilon₀ phi) :
      IsEpsilonApproximation C 1 phi ∧ IsGoodApproximation C phi ∧
        PreservesHorizontalTranslatedVertexSigns C phi ∧
        ControlsHorizontalTranslatedVertexDistances C phi ∧
        Function.Injective (fun g : ↑F.gapAlphabet ↦ mapScalar phi (F.gapLift g)) := by
    refine ⟨hphi.of_le hε₀one, hGoodThreshold phi (hphi.of_le hε₀good),
      hSignsThreshold phi (hphi.of_le hε₀signs),
      hDistancesThreshold phi (hphi.of_le hε₀distances), ?_⟩
    have hcanonical (g : ↑F.gapAlphabet) : F.gapLift g = ⟨g.1, hgapMem g.1 g.2⟩ :=
      Subtype.ext (F.gapLift_coe g)
    intro g g' hgg'
    apply Subtype.ext
    by_contra hne
    apply hGapThreshold phi (hphi.of_le hε₀gap) g.1 g.2 g'.1 g'.2 hne
    simpa only [← hcanonical] using hgg'
  by_cases hProper : X.base ≠ Set.univ
  · obtain ⟨P, hPbase, _⟩ := exists_periodicBandData C X.base X.period
      (MeasureTheory.nonempty_of_measure_ne_zero X.base_nonnull) X.base_open X.base_regular
      hProper X.period_pos X.base_periodic F.source_target_eq F.source_tiles
    obtain ⟨epsilonBand, hFineBand, _⟩ := exists_deformedBandPeriod P
    let epsilon := min epsilon₀ epsilonBand
    have hepsilon : 0 < epsilon := lt_min hε₀ hFineBand.epsilon_pos
    refine ⟨epsilon, hepsilon, ?_, ?_⟩
    · intro _
      exact ⟨P, hPbase, periodicBandFineness_mono P hFineBand hepsilon (min_le_right _ _)⟩
    · intro phi hphi
      exact hproperties phi (hphi.of_le (min_le_left _ _))
  · exact ⟨epsilon₀, hε₀, fun hProper' ↦ False.elim (hProper hProper'), hproperties⟩

private structure FinalCarrierCodeTransport
    {C : ApproximationContext.{0}} {X : PeriodicVerticalCarrier}
    (F : FirstCarrierCodeTransport C X) where
  phi : C.coordinateSpace →ₗ[ℚ] ℚ
  isApproximation : IsEpsilonApproximation C 1 phi
  isGood : IsGoodApproximation C phi
  horizontalOrder : PreservesHorizontalTranslatedVertexSigns C phi
  distanceControl : ControlsHorizontalTranslatedVertexDistances C phi
  deformation : CoordinateDeformation C phi
  imageCenters : ↑C.centres ↪ Tiling.Plane
  imageCenters_apply : ∀ t, imageCenters t = mapPoint phi (C.centrePoint t.1 t.2)
  imageCarrier : PeriodicVerticalCarrier
  imageTiles : TilesOn deformation.deformedRegion (deformedCenterCarrier imageCenters)
    imageCarrier.carrier
  image_finiteHorizontalComplexity : HasFiniteHorizontalComplexity
    (deformedCenterCarrier imageCenters)
  imageBoundary : Set ℝ
  imageBoundary_eq : imageBoundary = totalSlabBoundary deformation.deformedRegion
    (deformedCenterCarrier imageCenters) imageCarrier
  boundaryMap : ↑(totalSlabBoundary C.region C.centres X) ≃o ↑imageBoundary
  imageNoncolumnPlate :
    {P : VerticalPlate C.region C.centres // ¬ IsVerticalColumn P} ≃
    {P : VerticalPlate deformation.deformedRegion (deformedCenterCarrier imageCenters) //
      ¬ IsVerticalColumn P}
  imageLabel : ↑imageBoundary → SlabCodeLabel C.region C.centres
  labels_preserved : ∀ x, imageLabel (boundaryMap x) = F.sourceLabel x
  imageLabel_geometric : ∀ {a b : ℝ} (ha : a ∈ imageBoundary)
    (_h : ConsecutiveIn imageBoundary a b),
    match imageLabel ⟨a, ha⟩ with
    | .outside => Ioo a b ⊆ imageCarrier.baseᶜ
    | .noncolumn P => Ioo a b ⊆ (imageNoncolumnPlate P).1.base
    | .columns => Ioo a b ⊆ aggregateColumnBase deformation.deformedRegion
        (deformedCenterCarrier imageCenters)
  gap_image : ↑F.gapAlphabet → ℝ
  gap_image_apply : ∀ g, gap_image g = mapScalar phi (F.gapLift g)
  gap_image_injective : Function.Injective gap_image
  gap_image_formula : ∀ {a b : ℝ}
    (h : ConsecutiveIn (totalSlabBoundary C.region C.centres X) a b),
    (boundaryMap ⟨b, h.2.1⟩).1 - (boundaryMap ⟨a, h.1⟩).1 =
      gap_image ⟨b - a, F.gap_complete h⟩
  rational_vertices : ∀ v ∈ deformation.deformedRegion.vertices, Tiling.IsRationalPoint v

/- The geometry record supplies independently proved base images and the onto boundary map.
The code below deliberately transports F's original labels, not the labels chosen in L. -/
private theorem finalCodeTransport_fromPrescribedGeometry
    {C : ApproximationContext.{0}} {X : PeriodicVerticalCarrier}
    (F : FirstCarrierCodeTransport C X) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hApprox : IsEpsilonApproximation C 1 phi) (hGood : IsGoodApproximation C phi)
    (hOrder : PreservesHorizontalTranslatedVertexSigns C phi)
    (hControl : ControlsHorizontalTranslatedVertexDistances C phi)
    (hInjective : Function.Injective (fun g : ↑F.gapAlphabet ↦ mapScalar phi (F.gapLift g)))
    (D : CoordinateDeformation C phi) (imageCenters : ↑C.centres ↪ Tiling.Plane)
    (imageCarrier : PeriodicVerticalCarrier)
    (hImage : ∀ t, imageCenters t = mapPoint phi (C.centrePoint t.1 t.2))
    (hImageTile : TilesOn D.deformedRegion (deformedCenterCarrier imageCenters)
      imageCarrier.carrier)
    (L : ProperCarrierLabelledTransport C X phi D imageCenters imageCarrier) :
    ∃ G : FinalCarrierCodeTransport F, G.phi = phi ∧ HEq G.deformation D := by
  classical
  let B := totalSlabBoundary C.region C.centres X
  let B' := totalSlabBoundary D.deformedRegion (deformedCenterCarrier imageCenters) imageCarrier
  have hTileX : TilesOn C.region C.centres X.carrier := F.source_target_eq ▸ F.source_tiles
  have hformula (x : B) : (L.boundaryMap x).1 = mapScalar phi (F.boundaryLift x) := by
    obtain ⟨v, hv, t, ht, hvt⟩ := slabCodeBoundaries_fromVertices X hTileX x.2
    have hlift : F.boundaryLift x =
        ⟨v.re, C.vertex_re_mem v hv⟩ + ⟨t.re, C.centre_re_mem t ht⟩ := by
      apply Subtype.ext
      rw [F.boundaryLift_coe, hvt, Complex.add_re]
      rfl
    rw [L.boundaryMap_apply, hvt,
      L.scalarHomeomorph_translatedVertex ⟨v, hv⟩ ⟨t, ht⟩, hImage, hlift]
    simp only [mapPoint, mapScalar, ApproximationContext.vertexPoint,
      ApproximationContext.centrePoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, map_add, Rat.cast_add, add_zero]
  let imageLabel : B' → SlabCodeLabel C.region C.centres :=
    fun x ↦ F.sourceLabel (L.boundaryMap.symm x)
  have hgeometry {a b : ℝ} (ha : a ∈ B') (hgap : ConsecutiveIn B' a b) :
      match imageLabel ⟨a, ha⟩ with
      | .outside => Ioo a b ⊆ imageCarrier.baseᶜ
      | .noncolumn P => Ioo a b ⊆ (L.imageNoncolumnPlate P).1.base
      | .columns => Ioo a b ⊆ aggregateColumnBase D.deformedRegion
          (deformedCenterCarrier imageCenters) := by
    let a₀ : B := L.boundaryMap.symm ⟨a, ha⟩
    let b₀ : B := L.boundaryMap.symm ⟨b, hgap.2.1⟩
    have haImage : L.scalarHomeomorph a₀.1 = a :=
      (L.boundaryMap_apply a₀).symm.trans
        (congrArg Subtype.val (L.boundaryMap.apply_symm_apply ⟨a, ha⟩))
    have hbImage : L.scalarHomeomorph b₀.1 = b :=
      (L.boundaryMap_apply b₀).symm.trans
        (congrArg Subtype.val (L.boundaryMap.apply_symm_apply ⟨b, hgap.2.1⟩))
    have hsourceGap : ConsecutiveIn B a₀.1 b₀.1 := by
      refine ⟨a₀.2, b₀.2, L.scalarHomeomorph_strictMono.lt_iff_lt.mp
        (haImage ▸ hbImage ▸ hgap.2.2.1), ?_⟩
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxB⟩
      have hxImage : L.scalarHomeomorph x ∈ Ioo a b ∩ B' := by
        refine ⟨⟨haImage ▸ L.scalarHomeomorph_strictMono hx.1,
          hbImage ▸ L.scalarHomeomorph_strictMono hx.2⟩, ?_⟩
        rw [← L.boundaryMap_apply ⟨x, hxB⟩]
        exact (L.boundaryMap ⟨x, hxB⟩).2
      rw [hgap.2.2.2] at hxImage
      exact hxImage
    have hsourceGeom := F.sourceLabel_geometric hsourceGap
    change match F.sourceLabel a₀ with
      | .outside => _
      | .noncolumn P => _
      | .columns => _
    cases hlabel : F.sourceLabel a₀ with
    | outside =>
        intro y hy hyCarrier
        rw [L.carrier_base_image] at hyCarrier
        obtain ⟨x, hx, rfl⟩ := hyCarrier
        have hxgap : x ∈ Ioo a₀.1 b₀.1 :=
          ⟨L.scalarHomeomorph_strictMono.lt_iff_lt.mp (haImage ▸ hy.1),
            L.scalarHomeomorph_strictMono.lt_iff_lt.mp (hbImage ▸ hy.2)⟩
        rw [hlabel] at hsourceGeom
        exact hsourceGeom hxgap hx
    | noncolumn P =>
        intro y hy
        rw [L.imageNoncolumnPlate_base]
        refine ⟨L.scalarHomeomorph.symm y, ?_, L.scalarHomeomorph.apply_symm_apply y⟩
        rw [hlabel] at hsourceGeom
        apply hsourceGeom
        constructor <;> apply L.scalarHomeomorph_strictMono.lt_iff_lt.mp
        · simpa [haImage] using hy.1
        · simpa [hbImage] using hy.2
    | columns =>
        intro y hy
        rw [L.aggregateColumnBase_image]
        refine ⟨L.scalarHomeomorph.symm y, ?_, L.scalarHomeomorph.apply_symm_apply y⟩
        rw [hlabel] at hsourceGeom
        apply hsourceGeom
        constructor <;> apply L.scalarHomeomorph_strictMono.lt_iff_lt.mp
        · simpa [haImage] using hy.1
        · simpa [hbImage] using hy.2
  have hgapFormula {a b : ℝ} (h : ConsecutiveIn B a b) :
      (L.boundaryMap ⟨b, h.2.1⟩).1 - (L.boundaryMap ⟨a, h.1⟩).1 =
        mapScalar phi (F.gapLift ⟨b - a, F.gap_complete h⟩) := by
    have hlift : F.gapLift ⟨b - a, F.gap_complete h⟩ =
        F.boundaryLift ⟨b, h.2.1⟩ - F.boundaryLift ⟨a, h.1⟩ := by
      apply Subtype.ext
      simp only [F.gapLift_coe, Submodule.coe_sub, F.boundaryLift_coe]
    rw [hformula, hformula, hlift]
    simp only [mapScalar, map_sub, Rat.cast_sub]
  let G : FinalCarrierCodeTransport F := {
    phi := phi
    isApproximation := hApprox
    isGood := hGood
    horizontalOrder := hOrder
    distanceControl := hControl
    deformation := D
    imageCenters := imageCenters
    imageCenters_apply := hImage
    imageCarrier := imageCarrier
    imageTiles := hImageTile
    image_finiteHorizontalComplexity := imageCenters_finiteHorizontalComplexity C phi
      imageCenters F.source_finiteHorizontalComplexity hControl hImage
    imageBoundary := B'
    imageBoundary_eq := rfl
    boundaryMap := L.boundaryMap
    imageNoncolumnPlate := L.imageNoncolumnPlate
    imageLabel := imageLabel
    labels_preserved := fun x ↦ by simp [imageLabel]
    imageLabel_geometric := hgeometry
    gap_image := fun g ↦ mapScalar phi (F.gapLift g)
    gap_image_apply := fun _ ↦ rfl
    gap_image_injective := hInjective
    gap_image_formula := hgapFormula
    rational_vertices := D.rational_vertices }
  exact ⟨G, rfl, HEq.rfl⟩

private theorem properCarrierFinalCodeTransport_ofApproximation :
    ∀ {C : ApproximationContext.{0}} {X : PeriodicVerticalCarrier}
      (F : FirstCarrierCodeTransport C X) (P : PeriodicBandData C) {epsilon : ℝ}
      (_hPbase : P.base = X.base) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hFine : IsPeriodicBandFineness P epsilon)
      (_hApproxFine : IsEpsilonApproximation C epsilon phi)
      (_hApproxOne : IsEpsilonApproximation C 1 phi)
      (_hGood : IsGoodApproximation C phi)
      (_hOrder : PreservesHorizontalTranslatedVertexSigns C phi)
      (_hControl : ControlsHorizontalTranslatedVertexDistances C phi)
      (_hInjective : Function.Injective (fun g : ↑F.gapAlphabet ↦ mapScalar phi (F.gapLift g)))
      (D : CoordinateDeformation C phi),
    X.base ≠ Set.univ →
      ∃ G : FinalCarrierCodeTransport F, G.phi = phi ∧ HEq G.deformation D := by
  intro C X F P epsilon hPbase phi hFine hApproxFine hApproxOne hGood hOrder hControl
    hInjective D hProper
  classical
  obtain ⟨imageCenters, base, period, hImage, hBaseOpen, hBaseRegular, hBaseNonempty,
      _hBaseProper, _hPeriodFormula, hPeriodPos, hBasePeriod, _hFrontier, _hOccupied,
      hImageTile, _hImageSupport⟩ := periodicBandDeformation P epsilon hFine phi hApproxFine D
  let imageCarrier : PeriodicVerticalCarrier := {
    base := base
    base_open := hBaseOpen
    base_regular := hBaseRegular
    base_nonnull := hBaseOpen.measure_ne_zero MeasureTheory.volume hBaseNonempty
    period := period
    period_pos := hPeriodPos
    base_periodic := hBasePeriod }
  obtain ⟨L⟩ := properCarrierLabelledTransport_exists C X phi D imageCenters imageCarrier
    F.source_target_eq F.source_tiles F.source_finiteHorizontalComplexity hProper
    hGood hOrder hControl hImage hImageTile
  exact finalCodeTransport_fromPrescribedGeometry F phi hApproxOne hGood hOrder hControl
    hInjective D imageCenters imageCarrier hImage hImageTile L

private theorem wholePlaneFinalCodeTransport_ofApproximation :
    ∀ {C : ApproximationContext.{0}} {X : PeriodicVerticalCarrier}
      (F : FirstCarrierCodeTransport C X) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hApprox : IsEpsilonApproximation C 1 phi)
      (_hGood : IsGoodApproximation C phi)
      (_hOrder : PreservesHorizontalTranslatedVertexSigns C phi)
      (_hControl : ControlsHorizontalTranslatedVertexDistances C phi)
      (_hInjective : Function.Injective (fun g : ↑F.gapAlphabet ↦ mapScalar phi (F.gapLift g)))
      (D : CoordinateDeformation C phi),
    X.base = Set.univ →
      ∃ G : FinalCarrierCodeTransport F, G.phi = phi ∧ HEq G.deformation D := by
  intro C X F phi hApprox hGood hOrder hControl hInjective D hWhole
  classical
  have hTileX : TilesOn C.region C.centres X.carrier := F.source_target_eq ▸ F.source_tiles
  have hTilePlane : TilesOn C.region C.centres Set.univ := by
    simpa only [PeriodicVerticalCarrier.carrier, hWhole, Set.preimage_univ] using hTileX
  obtain ⟨P⟩ := exists_twoStageDeformationSupportTransport C phi D hTilePlane
  have hImageTile : TilesOn D.deformedRegion (deformedCenterCarrier P.fullCenters)
      X.carrier := by
    simpa only [PeriodicVerticalCarrier.carrier, hWhole, Set.preimage_univ] using P.full_tilesOn
  obtain ⟨L⟩ := wholePlanePrescribedLabelledGeometry C X phi D P F.source_target_eq
    F.source_tiles F.source_finiteHorizontalComplexity hWhole hOrder hControl
  exact finalCodeTransport_fromPrescribedGeometry F phi hApprox hGood hOrder hControl
    hInjective D P.fullCenters X P.fullCenters_apply hImageTile L

private theorem finalCarrierCodeTransport_exists :
    ∀ {C : ApproximationContext.{0}} {X : PeriodicVerticalCarrier}
      (F : FirstCarrierCodeTransport C X), Nonempty (FinalCarrierCodeTransport F) := by
  intro C X F
  obtain ⟨epsilon, hepsilon, hBand, hThreshold⟩ := finalApproximation_afterGapAlphabet F
  obtain ⟨phi, hApprox⟩ := exists_epsilonApproximation C epsilon hepsilon
  obtain ⟨hApproxOne, hGood, hOrder, hControl, hInjective⟩ := hThreshold phi hApprox
  obtain ⟨D⟩ := exists_rationalPolygonDeformation C phi hGood
  by_cases hWhole : X.base = Set.univ
  · obtain ⟨G, _, _⟩ := wholePlaneFinalCodeTransport_ofApproximation F phi hApproxOne
      hGood hOrder hControl hInjective D hWhole
    exact ⟨G⟩
  · obtain ⟨P, hPbase, hFine⟩ := hBand hWhole
    obtain ⟨G, _, _⟩ := properCarrierFinalCodeTransport_ofApproximation F P hPbase phi
      hFine hApprox hApproxOne hGood hOrder hControl hInjective D hWhole
    exact ⟨G⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Set Tiling.AxisParallel Tiling.AxisParallel.Approximation Tiling.AxisParallel.Continuous
open scoped Pointwise

private structure FinalTransportedPeriodicCode
    {C : ApproximationContext.{0}} {X : PeriodicVerticalCarrier}
    {F : FirstCarrierCodeTransport C X} (G : FinalCarrierCodeTransport F) where
  order : HorizontalOrderData G.imageBoundary
  period : ℝ
  period_pos : 0 < period
  shift : ℕ
  shift_pos : 0 < shift
  point_mem : ∀ i : ℤ, order.point i ∈ G.imageBoundary
  boundary_periodic : ∀ i : ℤ,
    order.point (i + Int.ofNat shift) = order.point i + period
  label_periodic : ∀ i : ℤ,
    G.imageLabel ⟨order.point (i + Int.ofNat shift), point_mem (i + Int.ofNat shift)⟩ =
      G.imageLabel ⟨order.point i, point_mem i⟩
  noncolumnSupport_periodic : ∀ P,
    Tiling.RationalPolygonal.SetPeriodicBy (G.imageNoncolumnPlate P).1.support (period : ℂ)
  columnSupport_periodic : Tiling.RationalPolygonal.SetPeriodicBy
    (regularSupport G.deformation.deformedRegion
      (verticalColumnCentres G.deformation.deformedRegion (deformedCenterCarrier G.imageCenters)))
    (period : ℂ)

private theorem carrierGapLabel_translate
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier) {p : ℝ}
    (hbase : p +ᵥ X.base = X.base)
    (hplates : ∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
      Tiling.RationalPolygonal.SetPeriodicBy P.support (p : ℂ))
    (hcolumns : Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K (verticalColumnCentres K T)) (p : ℂ))
    {a b : ℝ} (L : SlabCodeLabel K T) (hgeom : sourceGapHasLabel X a b L) :
    sourceGapHasLabel X (a + p) (b + p) L := by
  have hshift {A : Set ℝ} (hA : p +ᵥ A = A) (hAB : Ioo a b ⊆ A) :
      Ioo (a + p) (b + p) ⊆ A := by
    intro y hy
    have hx : y - p ∈ Ioo a b := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hmem := (addPeriodic_iff_vadd.mpr hA (y - p)).mpr (hAB hx)
    simpa using hmem
  cases L with
  | outside =>
      intro y hy hyX
      have hx : y - p ∈ Ioo a b := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      apply hgeom hx
      apply (addPeriodic_iff_vadd.mpr hbase (y - p)).mp
      simpa using hyX
  | noncolumn P => exact hshift (planeSupportPeriod_reImage (hplates P.1 P.2)) hgeom
  | columns => exact hshift (planeSupportPeriod_reImage hcolumns) hgeom

private theorem finalCarrierCodeTransport_period
    {C : ApproximationContext.{0}} {X : PeriodicVerticalCarrier}
    {F : FirstCarrierCodeTransport C X} (G : FinalCarrierCodeTransport F) :
    Nonempty (FinalTransportedPeriodicCode G) := by
  classical
  obtain ⟨p, hp, hplates, hcolumns⟩ := rationalPeriodicCarrierPlate_periodic
    G.imageCarrier G.imageTiles G.rational_vertices
  obtain ⟨hbase, hboundary⟩ := carrierSlabSupports_commonPeriod_totalBoundary
    G.imageCarrier G.imageTiles hplates hcolumns
  rw [← G.imageBoundary_eq] at hboundary
  have hnonempty : G.imageBoundary.Nonempty := by
    obtain ⟨a, ha⟩ := F.sourceBoundary_nonempty
    exact ⟨G.boundaryMap ⟨a, ha⟩, (G.boundaryMap ⟨a, ha⟩).2⟩
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (G.imageBoundary ∩ Q).Finite := by
    rw [G.imageBoundary_eq]
    exact totalSlabBoundary_boundedWindowFinite G.imageCarrier G.imageTiles
      G.image_finiteHorizontalComplexity
  obtain ⟨E⟩ := OneDimensional.periodicIntEnumeration_exists
    G.imageBoundary p hp hnonempty hlocal hboundary
  have hmem (i : ℤ) : E.point i ∈ G.imageBoundary := E.point_range.subset (Set.mem_range_self i)
  have hEperiod (i : ℤ) : E.point (i + (E.count : ℤ)) = E.point i + p := E.point_period i
  have hgapPos (i : ℤ) : 0 < E.point (i + 1) - E.point i :=
    sub_pos.mpr (E.point_strictMono (by omega))
  have hgapBound (i : ℤ) : E.point (i + 1) - E.point i ≤ p := by
    have hle : E.point (i + 1) ≤ E.point (i + (E.count : ℤ)) :=
      E.point_strictMono.monotone (by
        change i + 1 ≤ i + (E.count : ℤ)
        have := E.count_pos
        omega)
    rw [hEperiod] at hle
    linarith
  let gapSet : Set ℝ := {g | ∃ i : ℤ, g = E.point (i + 1) - E.point i}
  have hfinite : gapSet.Finite := by
    have hbounded := totalSlabBoundary_boundedDifferences_finite G.imageCarrier G.imageTiles
      G.image_finiteHorizontalComplexity p
    rw [← G.imageBoundary_eq] at hbounded
    apply hbounded.subset
    rintro g ⟨i, rfl⟩
    refine ⟨E.point i, hmem i, E.point (i + 1), hmem (i + 1), rfl, ?_⟩
    rw [abs_of_pos (hgapPos i)]
    exact hgapBound i
  let order : HorizontalOrderData G.imageBoundary := {
    point := E.point
    point_strictMono := E.point_strictMono
    point_range := E.point_range
    gapAlphabet := hfinite.toFinset
    gap_mem := fun i ↦ hfinite.mem_toFinset.mpr ⟨i, rfl⟩
    gap_pos := fun g hg ↦ by
      obtain ⟨i, rfl⟩ := hfinite.mem_toFinset.mp hg
      exact hgapPos i
    gap_complete := fun g hg ↦ hfinite.mem_toFinset.mp hg }
  let imageLabel : SlabCodeLabel C.region C.centres →
      SlabCodeLabel G.deformation.deformedRegion (deformedCenterCarrier G.imageCenters)
    | .outside => .outside
    | .noncolumn P => .noncolumn (G.imageNoncolumnPlate P)
    | .columns => .columns
  have hlabelInjective : Function.Injective imageLabel := by
    intro L M h
    cases L <;> cases M <;> simp_all [imageLabel, G.imageNoncolumnPlate.injective.eq_iff]
  have hgeometry {a b : ℝ} (ha : a ∈ G.imageBoundary)
      (hgap : ConsecutiveIn G.imageBoundary a b) :
      sourceGapHasLabel G.imageCarrier a b (imageLabel (G.imageLabel ⟨a, ha⟩)) := by
    have hg := G.imageLabel_geometric ha hgap
    cases hL : G.imageLabel ⟨a, ha⟩ <;> simpa [imageLabel, sourceGapHasLabel, hL] using hg
  have hlabels (i : ℤ) :
      G.imageLabel ⟨E.point (i + (E.count : ℤ)), hmem _⟩ =
        G.imageLabel ⟨E.point i, hmem i⟩ := by
    apply hlabelInjective
    have hgap := integerBoundary_consecutive E.point E.point_strictMono E.point_range i
    have hgapShift := integerBoundary_consecutive E.point E.point_strictMono E.point_range
      (i + (E.count : ℤ))
    have hOld := carrierGapLabel_translate G.imageCarrier hbase hplates hcolumns
      (imageLabel (G.imageLabel ⟨E.point i, hmem i⟩)) (hgeometry (hmem i) hgap)
    have hidx : i + 1 + (E.count : ℤ) = i + (E.count : ℤ) + 1 := by omega
    rw [← hEperiod i, ← hEperiod (i + 1), hidx] at hOld
    have hNew := hgeometry (hmem (i + (E.count : ℤ))) hgapShift
    exact carrierGapLabel_unique G.imageCarrier G.imageTiles hgapShift.2.2.1 hNew hOld
  exact ⟨{
    order := order
    period := p
    period_pos := hp
    shift := E.count
    shift_pos := E.count_pos
    point_mem := hmem
    boundary_periodic := E.point_period
    label_periodic := hlabels
    noncolumnSupport_periodic := fun P ↦ hplates (G.imageNoncolumnPlate P).1
      (G.imageNoncolumnPlate P).2
    columnSupport_periodic := hcolumns }⟩

private theorem labelledIntervals_period
    {L : Type*} (point : ℤ → ℝ) (label : ℤ → L)
    (k : ℕ) (p : ℝ)
    (hpoint : ∀ i : ℤ, point (i + (k : ℤ)) = point i + p)
    (hlabel : ∀ i : ℤ, label (i + (k : ℤ)) = label i) (l : L) :
    p +ᵥ (⋃ i : {i : ℤ // label i = l}, Ioo (point i.1) (point (i.1 + 1))) =
      ⋃ i : {i : ℤ // label i = l}, Ioo (point i.1) (point (i.1 + 1)) := by
  apply addPeriodic_iff_vadd.mp
  intro x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    let j : ℤ := i.1 - (k : ℤ)
    have hji : j + (k : ℤ) = i.1 := by omega
    have hjLabel : label j = l := by rw [← hlabel j, hji]; exact i.2
    refine Set.mem_iUnion.mpr ⟨⟨j, hjLabel⟩, ?_⟩
    have hj := hpoint j
    have hj1 := hpoint (j + 1)
    have hji1 : j + 1 + (k : ℤ) = i.1 + 1 := by omega
    rw [hji] at hj
    rw [hji1] at hj1
    constructor <;> linarith [hi.1, hi.2]
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hiLabel : label (i.1 + (k : ℤ)) = l := (hlabel i.1).trans i.2
    refine Set.mem_iUnion.mpr ⟨⟨i.1 + (k : ℤ), hiLabel⟩, ?_⟩
    have hi0 := hpoint i.1
    have hi1 := hpoint (i.1 + 1)
    have hidx : i.1 + 1 + (k : ℤ) = i.1 + (k : ℤ) + 1 := by omega
    rw [hidx] at hi1
    constructor <;> linarith [hi.1, hi.2]

private theorem finalTransportedLabelledPeriod_reflects
    {C : ApproximationContext.{0}} {X : PeriodicVerticalCarrier}
    {F : FirstCarrierCodeTransport C X} (G : FinalCarrierCodeTransport F)
    (W : FinalTransportedPeriodicCode G) :
    ∃ beta : ℝ, 0 < beta ∧
      (∀ P : VerticalPlate C.region C.centres, ¬ IsVerticalColumn P →
        Tiling.RationalPolygonal.SetPeriodicBy P.support (beta : ℂ)) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport C.region (verticalColumnCentres C.region C.centres)) (beta : ℂ) := by
  classical
  let B := totalSlabBoundary C.region C.centres X
  let sourcePoint (i : ℤ) : B := G.boundaryMap.symm ⟨W.order.point i, W.point_mem i⟩
  let point (i : ℤ) : ℝ := (sourcePoint i).1
  have hmono : StrictMono point := fun _ _ hij ↦
    G.boundaryMap.symm.strictMono (W.order.point_strictMono hij)
  have hrange : Set.range point = B := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (sourcePoint i).2
    · intro hx
      obtain ⟨i, hi⟩ := W.order.point_range.symm.subset (G.boundaryMap ⟨x, hx⟩).2
      have hs : sourcePoint i = ⟨x, hx⟩ := by
        apply G.boundaryMap.injective
        rw [OrderIso.apply_symm_apply]
        exact Subtype.ext hi
      exact ⟨i, congrArg Subtype.val hs⟩
  have hmap (i : ℤ) : (G.boundaryMap (sourcePoint i)).1 = W.order.point i := by
    simp [sourcePoint]
  have hconsecutive (i : ℤ) : ConsecutiveIn B (point i) (point (i + 1)) :=
    integerBoundary_consecutive point hmono hrange i
  let gap (i : ℤ) : ↑F.gapAlphabet :=
    ⟨point (i + 1) - point i, F.gap_complete (hconsecutive i)⟩
  have hgapFormula (i : ℤ) : W.order.point (i + 1) - W.order.point i = G.gap_image (gap i) := by
    have hi := G.gap_image_formula (hconsecutive i)
    change (G.boundaryMap (sourcePoint (i + 1))).1 - (G.boundaryMap (sourcePoint i)).1 = _ at hi
    simpa only [hmap] using hi
  have hImagePeriod (i : ℤ) : W.order.point (i + (W.shift : ℤ)) =
      W.order.point i + W.period := W.boundary_periodic i
  have hgap (i : ℤ) : point (i + (W.shift : ℤ) + 1) - point (i + (W.shift : ℤ)) =
      point (i + 1) - point i := by
    have hidx : i + 1 + (W.shift : ℤ) = i + (W.shift : ℤ) + 1 := by omega
    have heq : G.gap_image (gap (i + (W.shift : ℤ))) = G.gap_image (gap i) := by
      rw [← hgapFormula, ← hgapFormula, ← hidx, hImagePeriod, hImagePeriod]
      ring
    exact congrArg Subtype.val (G.gap_image_injective heq)
  let displacement (i : ℤ) := point (i + (W.shift : ℤ)) - point i
  have hsucc (i : ℤ) : displacement (i + 1) = displacement i := by
    dsimp [displacement]
    have hidx : i + 1 + (W.shift : ℤ) = i + (W.shift : ℤ) + 1 := by omega
    rw [hidx]
    linarith [hgap i]
  have hconstant (i : ℤ) : displacement i = displacement 0 := by
    refine Int.inductionOn' i 0 rfl ?_ ?_
    · intro j _ hj
      exact (hsucc j).trans hj
    · intro j _ hj
      calc
        displacement (j - 1) = displacement ((j - 1) + 1) := (hsucc (j - 1)).symm
        _ = displacement j := by congr 1; omega
        _ = displacement 0 := hj
  let beta := point ((W.shift : ℤ)) - point 0
  have hbeta : 0 < beta := sub_pos.mpr (hmono (by have := W.shift_pos; omega))
  have hpoint (i : ℤ) : point (i + (W.shift : ℤ)) = point i + beta := by
    have h := hconstant i
    dsimp only [displacement] at h
    simp only [zero_add] at h
    dsimp only [beta]
    linarith
  have hperiod : beta +ᵥ B = B := by
    apply addPeriodic_iff_vadd.mp
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := hrange.symm.subset hx
      have hback := hpoint (i - (W.shift : ℤ))
      have hidx : i - (W.shift : ℤ) + (W.shift : ℤ) = i := by omega
      rw [hidx, hi] at hback
      have hxPoint : point (i - (W.shift : ℤ)) = x := by linarith
      exact hxPoint ▸ (hrange ▸ Set.mem_range_self (i - (W.shift : ℤ)))
    · intro hx
      obtain ⟨i, rfl⟩ := hrange.symm.subset hx
      rw [← hpoint i]
      exact hrange ▸ Set.mem_range_self (i + (W.shift : ℤ))
  obtain ⟨R, hR, hdense⟩ := nonempty_periodicSet_relativelyDense
    (hrange ▸ Set.range_nonempty point) hbeta hperiod
  have hbelow (z : ℝ) : ∃ i : ℤ, point i ≤ z := by
    obtain ⟨a, ha, hadist⟩ := hdense (z - R)
    obtain ⟨i, rfl⟩ := hrange.symm.subset ha
    exact ⟨i, by have := (abs_lt.mp hadist).2; linarith⟩
  have habove (z : ℝ) : ∃ i : ℤ, z < point i := by
    obtain ⟨a, ha, hadist⟩ := hdense (z + R)
    obtain ⟨i, rfl⟩ := hrange.symm.subset ha
    exact ⟨i, by have := (abs_lt.mp hadist).1; linarith⟩
  let label (i : ℤ) := F.sourceLabel (sourcePoint i)
  have hlabel (i : ℤ) : label (i + (W.shift : ℤ)) = label i := by
    have hleft := G.labels_preserved (sourcePoint (i + (W.shift : ℤ)))
    have hright := G.labels_preserved (sourcePoint i)
    simp only [sourcePoint, OrderIso.apply_symm_apply] at hleft hright
    exact hleft.symm.trans ((W.label_periodic i).trans hright)
  have hgeom (i : ℤ) : sourceGapHasLabel X (point i) (point (i + 1)) (label i) :=
    F.sourceLabel_geometric (hconsecutive i)
  have hTileX : TilesOn C.region C.centres X.carrier := F.source_target_eq ▸ F.source_tiles
  obtain ⟨hPdecode, hCdecode⟩ := carrierSlabBase_eq_labelledIntervals X hTileX point hmono
    hrange hbelow habove label hgeom
  have hslab := (relativeCarrier_verticalPlates hTileX rfl X.base_regular.symm
    (fun a b ↦ by
      simpa only [inter_comm] using hTileX.verticalCylinder_frontier_locallyFinite
        X.base_open X.base_regular (Icc a b) isCompact_Icc)).1
  refine ⟨beta, hbeta, ?_, ?_⟩
  · intro P hP
    have hbase : beta +ᵥ P.base = P.base := by
      rw [hPdecode ⟨P, hP⟩]
      exact labelledIntervals_period point label W.shift beta hpoint hlabel (.noncolumn ⟨P, hP⟩)
    rw [(hslab P).2]
    intro z
    simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re] using
      addPeriodic_iff_vadd.mpr hbase z.re
  · have hbase : beta +ᵥ aggregateColumnBase C.region C.centres =
        aggregateColumnBase C.region C.centres := by
      rw [hCdecode]
      exact labelledIntervals_period point label W.shift beta hpoint hlabel .columns
    rw [aggregateColumnSupport_eq_cylinder X hTileX]
    intro z
    simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re] using
      addPeriodic_iff_vadd.mpr hbase z.re

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Set Tiling.AxisParallel Tiling.AxisParallel.Approximation Tiling.AxisParallel.Continuous
open scoped Pointwise

private theorem emptyFrontier_realSet_periodic
    {A : Set ℝ} (hA : frontier A = ∅) (p : ℝ) : p +ᵥ A = A := by
  rcases frontier_eq_empty_iff.mp hA with rfl | rfl <;> simp

private theorem approximationContextCarrierPlate_periodic
    (C : ApproximationContext.{0}) (X : PeriodicVerticalCarrier)
    (htarget : C.target = X.carrier) (hTile : TilesOn C.region C.centres C.target)
    (hFHC : HasFiniteHorizontalComplexity C.centres) :
    ∃ beta : ℝ, 0 < beta ∧
      (∀ P : VerticalPlate C.region C.centres, ¬ IsVerticalColumn P →
        Tiling.RationalPolygonal.SetPeriodicBy P.support (beta : ℂ)) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport C.region (verticalColumnCentres C.region C.centres)) (beta : ℂ) := by
  classical
  by_cases hboundary : (totalSlabBoundary C.region C.centres X).Nonempty
  · obtain ⟨F⟩ := firstCarrierPreAlphabetTransport_exists C X htarget hTile hFHC hboundary
    obtain ⟨W⟩ := firstImagePeriodicBoundary_exists F
    obtain ⟨F', _hparent⟩ := firstCarrierCodeTransport_exists F W
    obtain ⟨G⟩ := finalCarrierCodeTransport_exists F'
    obtain ⟨V⟩ := finalCarrierCodeTransport_period G
    exact finalTransportedLabelledPeriod_reflects G V
  · have hTileX : TilesOn C.region C.centres X.carrier := htarget ▸ hTile
    have hslab := (relativeCarrier_verticalPlates hTileX rfl X.base_regular.symm
      (fun a b ↦ by
        simpa only [inter_comm] using hTileX.verticalCylinder_frontier_locallyFinite
          X.base_open X.base_regular (Icc a b) isCompact_Icc)).1
    have hfrontP (P : VerticalPlate C.region C.centres) (hP : ¬ IsVerticalColumn P) :
        frontier P.base = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hboundary ⟨x, Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨P, hP⟩, hx⟩))⟩
    have hfrontC : frontier (aggregateColumnBase C.region C.centres) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hboundary ⟨x, Or.inr hx⟩
    refine ⟨1, zero_lt_one, ?_, ?_⟩
    · intro P hP
      rw [(hslab P).2]
      intro z
      simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re] using
        addPeriodic_iff_vadd.mpr (emptyFrontier_realSet_periodic (hfrontP P hP) 1) z.re
    · rw [aggregateColumnSupport_eq_cylinder X hTileX]
      intro z
      simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re] using
        addPeriodic_iff_vadd.mpr (emptyFrontier_realSet_periodic hfrontC 1) z.re

private theorem reImage_vadd (A : Set Tiling.Plane) (c : Tiling.Plane) :
    Complex.re '' (c +ᵥ A) = c.re +ᵥ (Complex.re '' A) := by
  ext x
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w.re, ⟨w, hw, rfl⟩, by simp⟩
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨c + z, ⟨z, hz, rfl⟩, by simp⟩

private def translatedPeriodicVerticalCarrier
    (X : PeriodicVerticalCarrier) (c : Tiling.Plane) : PeriodicVerticalCarrier where
  base := c.re +ᵥ X.base
  base_open := X.base_open.vadd c.re
  base_regular := by rw [closure_vadd, interior_vadd, X.base_regular]
  base_nonnull := by simpa only [MeasureTheory.measure_vadd] using X.base_nonnull
  period := X.period
  period_pos := X.period_pos
  base_periodic := by
    calc
      X.period +ᵥ (c.re +ᵥ X.base) = c.re +ᵥ (X.period +ᵥ X.base) := by
        rw [vadd_vadd, vadd_vadd, add_comm]
      _ = c.re +ᵥ X.base := by rw [X.base_periodic]

private theorem translatedPeriodicVerticalCarrier_carrier
    (X : PeriodicVerticalCarrier) (c : Tiling.Plane) :
    (translatedPeriodicVerticalCarrier X c).carrier = c +ᵥ X.carrier := by
  ext z
  simp only [translatedPeriodicVerticalCarrier, PeriodicVerticalCarrier.carrier,
    Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
    Complex.add_re, Complex.neg_re]

private theorem planeSetPeriod_of_translate
    {A : Set Tiling.Plane} {c p : Tiling.Plane}
    (hA : Tiling.RationalPolygonal.SetPeriodicBy (c +ᵥ A) p) :
    Tiling.RationalPolygonal.SetPeriodicBy A p := by
  intro z
  have h := hA (c + z)
  simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
    neg_add_cancel_left, add_assoc] using h

theorem continuousPeriodicCarrierPlate_periodic
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) (hFHC : HasFiniteHorizontalComplexity T) :
    ∃ beta : ℝ, 0 < beta ∧
      (∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
        Tiling.RationalPolygonal.SetPeriodicBy P.support (beta : ℂ)) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (verticalColumnCentres K T)) (beta : ℂ) := by
  classical
  obtain ⟨v₀, hv₀, _w, _hw, _hmax, _hdiam⟩ := IntrinsicVertices.exists_intrinsicDiameterPair K
  have hregular : interior (closure X.carrier) = X.carrier := by
    change interior (closure (Complex.re ⁻¹' X.base)) = Complex.re ⁻¹' X.base
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, X.base_regular]
  have hsupport : regularSupport K T = X.carrier :=
    regularSupport_eq_of_tilesOn (X.base_open.preimage Complex.continuous_re) hregular hTile
  have hTne : T.Nonempty := by
    by_contra hnot
    have hempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hnot
    obtain ⟨x, hx⟩ := MeasureTheory.nonempty_of_measure_ne_zero X.base_nonnull
    have hz : (x : ℂ) ∈ regularSupport K T := by rw [hsupport]; exact hx
    simp [hempty, regularSupport, Tiling.Polygonal.regularSupport, Tiling.Polygonal.openUnion] at hz
  obtain ⟨t₀, ht₀⟩ := hTne
  obtain ⟨C, hOpen, hCentres, hTarget, hTiles⟩ :=
    normalizeApproximationContext.{0} K T X.carrier v₀ hv₀ t₀ ht₀
  let Y := translatedPeriodicVerticalCarrier X (-(v₀ + t₀))
  have htarget : C.target = Y.carrier :=
    hTarget.trans (translatedPeriodicVerticalCarrier_carrier X (-(v₀ + t₀))).symm
  have hFHC' : HasFiniteHorizontalComplexity C.centres := by
    rw [hCentres]
    change HasFLC (Complex.re '' ((-t₀) +ᵥ T))
    rw [reImage_vadd]
    exact hFHC.vadd (-t₀).re
  obtain ⟨beta, hbeta, hplates, hcolumns⟩ := approximationContextCarrierPlate_periodic
    C Y htarget (hTiles.mp hTile) hFHC'
  have hOpen' : C.region.openCarrier = positiveSimilarity 1 (-v₀) '' K.openCarrier := by
    simpa only [positiveSimilarity_image_eq_vadd_smul, one_smul] using hOpen
  have hCentres' : C.centres = positiveSimilarity 1 (-t₀) '' T := by
    simpa only [positiveSimilarity_image_eq_vadd_smul, one_smul] using hCentres
  rw [hCentres'] at hplates hcolumns
  refine ⟨beta, hbeta, ?_, ?_⟩
  · intro P hP
    let e := verticalPlate_positiveSimilarityEquiv (T := T) zero_lt_one hOpen' (-t₀)
    have hnon : ¬ IsVerticalColumn (e P) := fun h ↦ hP
      ((verticalPlate_positiveSimilarityEquiv_isVerticalColumn zero_lt_one hOpen' (-t₀) P).mpr h)
    have hp := hplates (e P) hnon
    rw [verticalPlate_positiveSimilarityEquiv_support_image zero_lt_one hOpen' (-t₀) P,
      positiveSimilarity_image_eq_vadd_smul, one_smul] at hp
    exact planeSetPeriod_of_translate hp
  · rw [verticalColumnSupport_positiveSimilarity_image zero_lt_one hOpen' (-t₀),
      positiveSimilarity_image_eq_vadd_smul, one_smul] at hcolumns
    exact planeSetPeriod_of_translate hcolumns

private theorem nonempty_periodicSet_meets_fundamental
    {A : Set ℝ} (hne : A.Nonempty) {p : ℝ} (hp : 0 < p) (hperiod : p +ᵥ A = A) :
    ∃ x ∈ A, 0 ≤ x ∧ x ≤ p := by
  obtain ⟨a, ha⟩ := hne
  have hfun : Function.Periodic (fun x : ℝ ↦ x ∈ A) p :=
    fun x ↦ propext (addPeriodic_iff_vadd.mpr hperiod x)
  let k : ℤ := ⌊a / p⌋
  refine ⟨a - (k : ℝ) * p, ?_, ?_, ?_⟩
  · have h := hfun.zsmul (-k) a
    simpa only [zsmul_eq_mul, Int.cast_neg, neg_mul, sub_eq_add_neg] using
      (eq_iff_iff.mp h).mpr ha
  · have h := (le_div_iff₀ hp).mp (Int.floor_le (a / p))
    dsimp [k]
    linarith
  · have h := (div_lt_iff₀ hp).mp (Int.lt_floor_add_one (a / p))
    dsimp [k]
    linarith

theorem periodicNoncolumnPlates_finite
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) {beta : ℝ} (hbeta : 0 < beta)
    (hperiod : ∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
      Tiling.RationalPolygonal.SetPeriodicBy P.support (beta : ℂ)) :
    {P : VerticalPlate K T | ¬ IsVerticalColumn P}.Finite := by
  classical
  obtain ⟨D, hD⟩ := K.isPolygonal.isBounded.exists_norm_le
  have hslab := (relativeCarrier_verticalPlates hTile rfl X.base_regular.symm
    (fun a b ↦ by
      simpa only [inter_comm] using hTile.verticalCylinder_frontier_locallyFinite
        X.base_open X.base_regular (Icc a b) isCompact_Icc)).1
  let Q : Set T := Subtype.val ⁻¹' (T ∩ Metric.closedBall (0 : Tiling.Plane) (beta + D))
  have hQfinite : Q.Finite :=
    ((IsPacking.locallyFinite_centres hTile.2.1).1
      (Metric.closedBall (0 : Tiling.Plane) (beta + D)) Metric.isBounded_closedBall).preimage
        Subtype.val_injective.injOn
  apply (hQfinite.image fun t : T ↦ VerticalPlate.ofCentre (K := K) t).subset
  intro P hP
  have hbaseNe : P.base.Nonempty := by
    obtain ⟨t, ht⟩ := P.nonempty_supp
    obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hraw : (t : Tiling.Plane) + k ∈ openUnion K P.centres := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      exact ⟨⟨t, ⟨t, ht, rfl⟩⟩, ⟨k, hk, rfl⟩⟩
    have hopen : IsOpen (openUnion K P.centres) := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
      exact isOpen_iUnion fun s : P.centres ↦
        (Homeomorph.addLeft (s : Tiling.Plane)).isOpenMap _ isOpen_interior
    exact ⟨((t : Tiling.Plane) + k).re,
      ⟨(t : Tiling.Plane) + k, hopen.subset_interior_closure hraw, rfl⟩⟩
  obtain ⟨x, hx, hx0, hxbeta⟩ := nonempty_periodicSet_meets_fundamental
    hbaseNe hbeta (planeSupportPeriod_reImage (hperiod P hP))
  have hz : (x : ℂ) ∈ P.support := by
    rw [(hslab P).2]
    exact hx
  have hPsub : P.centres ⊆ T := by rintro _ ⟨t, _, rfl⟩; exact t.2
  have hpackingP : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P.centres) := by
    intro s hs t ht hst
    exact hTile.2.1 (hPsub hs) (hPsub ht) hst
  have hzcl : (x : ℂ) ∈ closure (openUnion K P.centres) := interior_subset hz
  rw [closure_openUnion_eq_iUnion_support hpackingP, Set.mem_iUnion] at hzcl
  obtain ⟨s, hs⟩ := hzcl
  have hu : (x : ℂ) - (s : Tiling.Plane) ∈ K.support := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hs
  have hsbound : ‖(s : Tiling.Plane)‖ ≤ beta + D := by
    calc
      ‖(s : Tiling.Plane)‖ = ‖(x : ℂ) - ((x : ℂ) - (s : Tiling.Plane))‖ := by
        congr 1
        abel
      _ ≤ ‖(x : ℂ)‖ + ‖(x : ℂ) - (s : Tiling.Plane)‖ := norm_sub_le _ _
      _ ≤ beta + D := add_le_add (by simpa [abs_of_nonneg hx0] using hxbeta) (hD _ hu)
  obtain ⟨t, ht, hts⟩ := s.2
  refine ⟨t, ?_, ?_⟩
  · refine ⟨t.2, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, hts] using hsbound
  · exact (SimpleGraph.ConnectedComponent.mem_supp_iff P t).mp ht

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Set Filter MeasureTheory Tiling.AxisParallel Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.IntrinsicVertices
open Tiling.AxisParallel.Foundations.GenericSlices
open Tiling.AxisParallel.Foundations.FilledSliceChains
open Tiling.AxisParallel.OneDimensional.FiniteInterval
open scoped Pointwise _root_.Topology

private theorem automaticCarrier_horizontalSlices
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) :
    ∀ᵐ q : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume,
      x ∈ X.base → slicePoint Axis.horizontal q x ∈ openUnion K T := by
  have hplane : ∀ᵐ z : Tiling.Plane ∂volume,
      z ∈ X.carrier → z ∈ openUnion K T := by
    filter_upwards [hTile.2.2] with z hz
    intro hcarrier
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    exact hz.mp hcarrier
  have hpull := Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae
    hplane
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hpull
  have hslices := Measure.ae_ae_of_ae_prod (μ := volume) (ν := volume) hswap
  filter_upwards [hslices] with q hq
  filter_upwards [hq] with x hx
  have heq : slicePoint Axis.horizontal q x =
      Complex.measurableEquivRealProd.symm (q, x).swap := by
    apply Complex.ext <;> simp [slicePoint]
  rw [heq]
  exact hx

private theorem automaticCarrier_frontier_sliceEndpoint
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) {q : ℝ}
    (hcover : ∀ᵐ x : ℝ ∂volume,
      x ∈ X.base → slicePoint Axis.horizontal q x ∈ openUnion K T) :
    frontier X.base ⊆ sliceEndpointSet K T Axis.horizontal q := by
  let U : Set ℝ := {x | slicePoint Axis.horizontal q x ∈ openUnion K T}
  have hUsub : U ⊆ X.base := by
    intro x hx
    have h := openUnion_subset_cylinder X.base_open X.base_regular hTile hx
    simpa [slicePoint] using h
  have hbaseClosure : X.base ⊆ closure U := by
    have hdense : Dense {x : ℝ | x ∈ X.base → x ∈ U} := volume.dense_of_ae hcover
    intro x hx
    rw [mem_closure_iff]
    intro V hV hxV
    obtain ⟨y, hy, hyV⟩ := hdense.exists_mem_open (hV.inter X.base_open) ⟨x, hxV, hx⟩
    exact ⟨y, hyV.1, hy hyV.2⟩
  intro x hx
  change x ∈ frontier U
  refine ⟨?_, ?_⟩
  · simpa only [closure_closure] using closure_mono hbaseClosure hx.1
  · intro hxU
    apply hx.2
    rw [X.base_open.interior_eq]
    exact hUsub (interior_subset hxU)

private theorem automaticCarrier_verticalSide_endpoint
    {K : Region} {T : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements T))
    (v w : K.vertices) (s : T) {q : ℝ}
    (hvw : v.1 ≠ w.1) (hcoord : v.1.re = w.1.re)
    (hedge : openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices)
    (hq : q ∈ Ioo (min v.1.im w.1.im + s.1.im)
      (max v.1.im w.1.im + s.1.im))
    (hgeneric : q - s.1.im ∉ K.vertexFinset.image Complex.im) :
    (v.1 + s.1).re ∈ sliceEndpointSet K T Axis.horizontal q := by
  let a := (v.1 + s.1).re
  let p := slicePoint Axis.horizontal q a
  have himne : v.1.im ≠ w.1.im := fun h ↦ hvw (Complex.ext hcoord h)
  have hpseg : p - s.1 ∈ openSegment ℝ v.1 w.1 := by
    have hq' : q - s.1.im ∈ openSegment ℝ v.1.im w.1.im := by
      rw [openSegment_eq_Ioo' himne]
      exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
    rw [openSegment_eq_image] at hq' ⊢
    obtain ⟨r, hr, hqr⟩ := hq'
    refine ⟨r, hr, ?_⟩
    apply Complex.ext
    · simp only [p, a, slicePoint, Complex.sub_re, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.smul_re,
        smul_eq_mul]
      rw [hcoord]
      ring
    · simpa [p, slicePoint] using hqr
  have hpfront : p ∈ frontier (s.1 +ᵥ K.support) := by
    simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_eq_sub] using (hedge hpseg).1
  have hpnot : p ∉ openUnion K T := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    rintro ⟨t, hpt⟩
    by_cases hts : t = s
    · subst t
      exact hpfront.2 (by rwa [interior_vadd])
    · have hne : t.1 ≠ s.1 := fun h ↦ hts (Subtype.ext h)
      have hd := (isPacking_iff_openCarrier_disjoint K T).mp hpacking t.2 s.2 hne
      have hpclosure : p ∈ closure (s.1 +ᵥ K.openCarrier) := by
        rw [closure_vadd, show closure K.openCarrier = K.support from
          K.isPolygonal.closure_interior]
        exact (K.isPolygonal.isClosed.vadd s.1).frontier_subset hpfront
      obtain ⟨z, hzt, hzs⟩ := mem_closure_iff.mp hpclosure
        (t.1 +ᵥ K.openCarrier) (isOpen_interior.vadd _) hpt
      exact Set.disjoint_left.mp hd hzt hzs
  have haSection : a - s.1.re ∈ closure (horizontalSlice K (q - s.1.im)) := by
    rw [← horizontalSupportSection_eq_closureSlice K hgeneric]
    have hp : p - s.1 ∈ K.support := K.isPolygonal.isClosed.frontier_subset (hedge hpseg).1
    change Complex.mk (a - s.1.re) (q - s.1.im) ∈ K.support
    have heq : Complex.mk (a - s.1.re) (q - s.1.im) = p - s.1 := by
      apply Complex.ext <;> simp [p, slicePoint]
    rwa [heq]
  let U : Set ℝ := {x | slicePoint Axis.horizontal q x ∈ openUnion K T}
  have hshift : (fun x : ℝ ↦ s.1.re + x) '' horizontalSlice K (q - s.1.im) ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    change slicePoint Axis.horizontal q (s.1.re + y) ∈ openUnion K T
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    refine ⟨s, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have heq : -s.1 +ᵥ slicePoint Axis.horizontal q (s.1.re + y) =
        Complex.mk y (q - s.1.im) := by
      apply Complex.ext <;> simp [slicePoint, vadd_eq_add, sub_eq_add_neg, add_comm]
    rw [heq]
    exact hy
  have haClosure : a ∈ closure U := by
    have hcl := (Homeomorph.addLeft s.1.re).image_closure (horizontalSlice K (q - s.1.im))
    have hmem : a ∈ (Homeomorph.addLeft s.1.re) ''
        closure (horizontalSlice K (q - s.1.im)) :=
      ⟨a - s.1.re, haSection, by simp⟩
    rw [hcl] at hmem
    exact closure_mono hshift hmem
  change a ∈ frontier U
  refine ⟨haClosure, ?_⟩
  intro hx
  have hxU : a ∈ U := interior_subset hx
  exact hpnot hxU

private theorem automaticCarrier_segment_word
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) (W : Finset ℝ)
    (hsteps : ∀ w ∈ K.horizontalStepAlphabet, w ∈ W)
    (hholes : ∀ w ∈ targetGapLengths X.base, w ∈ W)
    {q a c : ℝ}
    (hcover : ∀ᵐ x : ℝ ∂volume,
      x ∈ X.base → slicePoint Axis.horizontal q x ∈ openUnion K T)
    (hchain : ∀ x ∈ sliceEndpointSet K T Axis.horizontal q,
      ∀ y ∈ sliceEndpointSet K T Axis.horizontal q, x < y →
      (∀ᵐ z : ℝ ∂volume,
        z ∈ Ioo x y → slicePoint Axis.horizontal q z ∈ openUnion K T) →
      ∃ (n : ℕ) (_hn : 0 < n) (point : Fin (n + 1) → ℝ) (owner : Fin n → T),
        point 0 = x ∧ point (Fin.last n) = y ∧
        IsFilledIndexedSliceChain K T Axis.horizontal q point owner ∧
        (∀ i, point i ∈ sliceEndpointSet K T Axis.horizontal q))
    (ha : a ∈ sliceEndpointSet K T Axis.horizontal q)
    (haClosure : a ∈ closure X.base)
    (hc : c ∈ sliceEndpointSet K T Axis.horizontal q)
    (hcClosure : c ∈ closure X.base) (hac : a < c) :
    ∃ n : ℕ, 0 < n ∧ ∃ step : Fin n → ℝ,
      (∀ i, step i ∈ W) ∧ c - a = ∑ i, step i := by
  classical
  let E : Set ℝ := frontier X.base ∪ {a, c}
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite := by
    intro Q hQ
    obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : ℝ)
    have hF := hTile.verticalCylinder_frontier_locallyFinite X.base_open X.base_regular
      (Metric.closedBall 0 R) (isCompact_closedBall 0 R)
    have hfront : (frontier X.base ∩ Q).Finite := hF.subset
      (by rintro x ⟨hx, hxQ⟩; exact ⟨hR hxQ, hx⟩)
    have hends : (({a, c} : Set ℝ) ∩ Q).Finite :=
      (Set.toFinite ({a, c} : Set ℝ)).inter_of_left Q
    exact (hfront.union hends).subset (by
      rintro x ⟨hx | hx, hxQ⟩
      · exact Or.inl ⟨hx, hxQ⟩
      · exact Or.inr ⟨hx, hxQ⟩)
  obtain ⟨C⟩ := endpointChain_nonempty hlocal (Or.inr (by simp))
    (Or.inr (by simp)) hac.le
  have hEclosure : E ⊆ closure X.base := by
    rintro x (hx | hx)
    · exact hx.1
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact haClosure
      · exact hcClosure
  have hEendpoint : E ⊆ sliceEndpointSet K T Axis.horizontal q := by
    rintro x (hx | hx)
    · exact automaticCarrier_frontier_sliceEndpoint X hTile hcover hx
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hc
  have hwords (i : Fin C.length) : ∃ n : ℕ, 0 < n ∧ ∃ step : Fin n → ℝ,
      (∀ j, step j ∈ W) ∧ C.point i.succ - C.point i.castSucc = ∑ j, step j := by
    obtain ⟨hl, hr, hlr, hgap⟩ := C.consecutive i
    have havoid : Disjoint (Ioo (C.point i.castSucc) (C.point i.succ)) (frontier X.base) :=
      hgap.symm.mono_right (Set.subset_union_left)
    rcases gap_subset_or_subset_exterior X.base_open havoid with hfilled | hhole
    · have hfull : ∀ᵐ z : ℝ ∂volume,
          z ∈ Ioo (C.point i.castSucc) (C.point i.succ) →
            slicePoint Axis.horizontal q z ∈ openUnion K T := by
        filter_upwards [hcover] with z hz
        exact fun hzgap ↦ hz (hfilled hzgap)
      obtain ⟨n, hn, point, owner, hfirst, hlast, hindexed, _⟩ :=
        hchain _ (hEendpoint hl) _ (hEendpoint hr) hlr hfull
      refine ⟨n, hn, fun j ↦ point j.succ - point j.castSucc, ?_, ?_⟩
      · intro j
        obtain ⟨v, w, hv, hw, hleft, hright, hpositive, _⟩ := hindexed.2 j
        apply hsteps _ ((K.mem_horizontalStepAlphabet_iff _).mpr ?_)
        refine ⟨v, hv, w, hw, ?_, ?_⟩
        · simp only [Axis.coord, Complex.add_re] at hleft hright
          linarith
        · exact sub_pos.mpr (hindexed.1 j.castSucc_lt_succ)
      · rw [sum_finite_gaps, hfirst, hlast]
    · have hclosedGap :
          Icc (C.point i.castSucc) (C.point i.succ) ⊆ X.baseᶜ := by
        have hsub : Ioo (C.point i.castSucc) (C.point i.succ) ⊆ X.baseᶜ :=
          hhole.trans (compl_subset_compl.mpr subset_closure)
        have h := closure_mono hsub
        rwa [closure_Ioo hlr.ne, closure_compl, X.base_open.interior_eq] at h
      have hlF : C.point i.castSucc ∈ frontier X.base := by
        rw [frontier, X.base_open.interior_eq]
        exact ⟨hEclosure hl, hclosedGap (left_mem_Icc.mpr hlr.le)⟩
      have hrF : C.point i.succ ∈ frontier X.base := by
        rw [frontier, X.base_open.interior_eq]
        exact ⟨hEclosure hr, hclosedGap (right_mem_Icc.mpr hlr.le)⟩
      refine ⟨1, by decide, fun _ ↦ C.point i.succ - C.point i.castSucc, ?_, by simp⟩
      intro _
      exact hholes _ ⟨_, _, hlF, hrF, hlr, hhole, rfl⟩
  choose n hn step hstep hsum using hwords
  let J := Σ i : Fin C.length, Fin (n i)
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  have hCpos : 0 < C.length := by
    by_contra h
    have hzero := Nat.eq_zero_of_not_pos h
    have heq : (0 : Fin (C.length + 1)) = Fin.last C.length :=
      Fin.ext (by simp [hzero])
    exact hac.ne (C.first.symm.trans ((congrArg C.point heq).trans C.last))
  have hJ : Nonempty J := ⟨⟨⟨0, hCpos⟩, ⟨0, hn ⟨0, hCpos⟩⟩⟩⟩
  refine ⟨Fintype.card J, Fintype.card_pos_iff.mpr hJ,
    fun j ↦ step (e.symm j).1 (e.symm j).2,
    fun j ↦ hstep (e.symm j).1 (e.symm j).2, ?_⟩
  calc
    c - a = ∑ i : Fin C.length, (C.point i.succ - C.point i.castSucc) :=
      (endpointChain_telescope C).symm
    _ = ∑ i : Fin C.length, ∑ j : Fin (n i), step i j :=
      Finset.sum_congr rfl fun i _ ↦ hsum i
    _ = ∑ j : J, step j.1 j.2 :=
      (Fintype.sum_sigma (fun j : J ↦ step j.1 j.2)).symm
    _ = ∑ j : Fin (Fintype.card J), step (e.symm j).1 (e.symm j).2 :=
      Fintype.sum_equiv e _ _ (by
        intro j
        rw [e.symm_apply_apply])

private theorem carrierBoundary_finitePositiveWords :
    ∀ {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier),
    X.base ≠ Set.univ → TilesOn K T X.carrier →
    ∃ W : Finset ℝ, W.Nonempty ∧ (∀ w ∈ W, 0 < w) ∧
      ∃ delta > 0, (∀ w ∈ W, delta ≤ w) ∧
      ∀ a ∈ horizontalTranslatedVertices K T,
        ∀ c ∈ frontier X.base, a ≠ c →
          ∃ n : ℕ, 0 < n ∧ ∃ step : Fin n → ℝ,
            (∀ i, step i ∈ W) ∧ |a - c| = ∑ i, step i := by
  intro K T X _hProper hTile
  classical
  have hGfinite := targetGapLengths_finite X.period_pos X.base_periodic
    (hTile.verticalCylinder_frontier_locallyFinite X.base_open X.base_regular)
  let W := K.horizontalStepAlphabet ∪ hGfinite.toFinset
  have hWne : W.Nonempty := K.horizontalStepAlphabet_nonempty.mono (Finset.subset_union_left)
  have hWpos : ∀ w ∈ W, 0 < w := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact K.horizontalStepAlphabet_pos hw
    · exact targetGapLengths_pos (by simpa using hw)
  refine ⟨W, hWne, hWpos, W.min' hWne, hWpos _ (W.min'_mem hWne),
    fun w hw ↦ W.min'_le w hw, ?_⟩
  intro a ha c hc hac
  obtain ⟨v, hv, t, ht, rfl⟩ := ha
  obtain ⟨w, hwne, hwcoord, hwedge⟩ :=
    intrinsicVertex_incident_axisEdge K Axis.vertical ⟨v, hv⟩
  have hcoord : v.re = w.1.re := hwcoord.symm
  have himne : v.im ≠ w.1.im := fun h ↦ hwne (Complex.ext hcoord h).symm
  let F := (K.vertexFinset.image fun z ↦ z.im + t.im)
  have hgenericAE : ∀ᵐ q : ℝ ∂volume, q - t.im ∉ K.vertexFinset.image Complex.im := by
    have havoid : ∀ᵐ q : ℝ ∂volume, q ∉ (F : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp (F.finite_toSet.measure_zero volume)
    filter_upwards [havoid] with q hq
    intro h
    obtain ⟨z, hz, hzq⟩ := Finset.mem_image.mp h
    apply hq
    exact Finset.mem_image.mpr ⟨z, hz, by linarith⟩
  have hevent := (automaticCarrier_horizontalSlices X hTile).and
    ((genericSliceChain_betweenEndpoints_of_local_ae K T hTile.2.1 Axis.horizontal).and
      hgenericAE)
  let U := Ioo (min v.im w.1.im + t.im) (max v.im w.1.im + t.im)
  have hUne : U.Nonempty := nonempty_Ioo.mpr (by
    simpa using add_lt_add_right ((min_lt_max).mpr himne) t.im)
  obtain ⟨q, hqU, hq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (isOpen_Ioo.measure_ne_zero volume hUne) (hevent.filter_mono ae_restrict_le)
  have haEndpoint := automaticCarrier_verticalSide_endpoint hTile.2.1
    ⟨v, hv⟩ w ⟨t, ht⟩ hwne.symm hcoord hwedge hqU hq.2.2
  have haClosure : (v + t).re ∈ closure X.base := by
    have hfront : v ∈ frontier K.support := by
      rw [← K.frontier_openCarrier_eq_frontier_support]
      exact region_vertices_subset_frontier K hv
    have hsupport : v + t ∈ closure (openUnion K T) := by
      rw [closure_openUnion_eq_iUnion_support hTile.2.1, Set.mem_iUnion]
      exact ⟨⟨t, ht⟩, v, K.isPolygonal.isClosed.frontier_subset hfront, by simp [add_comm]⟩
    have h := closure_mono (openUnion_subset_cylinder X.base_open X.base_regular hTile) hsupport
    rwa [Complex.closure_preimage_re] at h
  have hsteps : ∀ d ∈ K.horizontalStepAlphabet, d ∈ W := fun _ hd ↦
    Finset.mem_union_left _ hd
  have hholes : ∀ d ∈ targetGapLengths X.base, d ∈ W := fun _ hd ↦
    Finset.mem_union_right _ (by simpa using hd)
  by_cases hlt : (v + t).re < c
  · obtain ⟨n, hn, step, hstep, hsum⟩ := automaticCarrier_segment_word X hTile W
      hsteps hholes hq.1 hq.2.1 haEndpoint haClosure
      (automaticCarrier_frontier_sliceEndpoint X hTile hq.1 hc) hc.1 hlt
    exact ⟨n, hn, step, hstep, by rw [abs_of_neg (sub_neg.mpr hlt)]; linarith⟩
  · have hgt : c < (v + t).re := lt_of_le_of_ne (le_of_not_gt hlt) hac.symm
    obtain ⟨n, hn, step, hstep, hsum⟩ := automaticCarrier_segment_word X hTile W
      hsteps hholes hq.1 hq.2.1
      (automaticCarrier_frontier_sliceEndpoint X hTile hq.1 hc) hc.1
      haEndpoint haClosure hgt
    exact ⟨n, hn, step, hstep, by rw [abs_of_pos (sub_pos.mpr hgt)]; exact hsum⟩

private theorem automaticPositiveWordValues
    (W : Finset ℝ) {delta R : ℝ} (hdelta : 0 < delta)
    (hminimum : ∀ w ∈ W, delta ≤ w) :
    ∃ V : Set ℝ, V.Finite ∧ 0 ∈ V ∧
      ∀ d : ℝ, |d| ≤ R →
        (∃ (n : ℕ) (step : Fin n → ℝ),
          (∀ i, step i ∈ W) ∧ |d| = ∑ i, step i) → d ∈ V := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (R / delta)
  let J := Σ n : Fin (N + 1), Fin n.1 → ↥W
  let value : J → ℝ := fun p ↦ ∑ i, (p.2 i).1
  let V : Set ℝ := Set.range value ∪ Set.range (fun p ↦ -value p) ∪ {0}
  refine ⟨V, ((Set.finite_range value).union (Set.finite_range _)).union
    (Set.finite_singleton _), Or.inr rfl, ?_⟩
  rintro d hd ⟨n, step, hstep, hsum⟩
  have hndelta : (n : ℝ) * delta ≤ ∑ i, step i := by
    calc
      (n : ℝ) * delta = ∑ _i : Fin n, delta := by simp
      _ ≤ ∑ i : Fin n, step i := Finset.sum_le_sum fun i _ ↦ hminimum _ (hstep i)
  have hnR : (n : ℝ) ≤ R / delta :=
    (le_div_iff₀ hdelta).mpr (hndelta.trans (hsum.symm ▸ hd))
  have hnN : n < N := by exact_mod_cast hnR.trans_lt hN
  let p : J := ⟨⟨n, hnN.trans (Nat.lt_succ_self N)⟩, fun i ↦ ⟨step i, hstep i⟩⟩
  have hp : value p = |d| := hsum.symm
  rcases le_total 0 d with hpos | hneg
  · exact Or.inl (Or.inl ⟨p, hp.trans (abs_of_nonneg hpos)⟩)
  · exact Or.inl (Or.inr ⟨p, by
      change -value p = d
      rw [hp, abs_of_nonpos hneg, neg_neg]⟩)

/-- A proper regular periodic carrier forces FLC of the original horizontal projection. -/
theorem properCarrier_hasFiniteHorizontalComplexity
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier) (hProper : X.base ≠ Set.univ)
    (hTile : TilesOn K T X.carrier) : HasFiniteHorizontalComplexity T := by
  classical
  obtain ⟨W, _hWne, _hWpos, delta, hdelta, hminimum, hwords⟩ :=
    carrierBoundary_finitePositiveWords X hProper hTile
  obtain ⟨v, hv, _w, _hw, _hmax, _hdiam⟩ := exists_intrinsicDiameterPair K
  have hfrontier : (frontier X.base).Nonempty :=
    frontier_nonempty_of_nonempty_proper_regularOpen
      (MeasureTheory.nonempty_of_measure_ne_zero X.base_nonnull)
      X.base_open X.base_regular hProper
  obtain ⟨c₀, hc₀⟩ := hfrontier
  have hwordValue {R : ℝ} {V : Set ℝ} (hzero : 0 ∈ V)
      (hV : ∀ d : ℝ, |d| ≤ R →
        (∃ (n : ℕ) (step : Fin n → ℝ),
          (∀ i, step i ∈ W) ∧ |d| = ∑ i, step i) → d ∈ V)
      {t : Tiling.Plane} (ht : t ∈ T) {c : ℝ} (hc : c ∈ frontier X.base)
      (hbound : |(v + t).re - c| ≤ R) : (v + t).re - c ∈ V := by
    by_cases heq : (v + t).re = c
    · simpa [heq] using hzero
    · obtain ⟨n, _hn, step, hstep, hsum⟩ :=
        hwords _ ⟨v, hv, t, ht, rfl⟩ c hc heq
      exact hV _ hbound ⟨n, step, hstep, hsum⟩
  change HasFLC (Complex.re '' T)
  constructor
  · intro Q hQ
    obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : ℝ)
    let B := |v.re| + max R 0 + |c₀| + 1
    obtain ⟨V, hVfinite, hVzero, hV⟩ := automaticPositiveWordValues W hdelta hminimum
      (R := B)
    apply (hVfinite.image (fun d ↦ c₀ - v.re + d)).subset
    rintro x ⟨⟨t, ht, htx⟩, hxQ⟩
    have hxR : |x| ≤ max R 0 := by
      have hx := hR hxQ
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx
      exact hx.trans (le_max_left _ _)
    have hbound : |(v + t).re - c₀| ≤ B := by
      rw [Complex.add_re, htx]
      calc
        |v.re + x - c₀| ≤ |v.re + x| + |c₀| := abs_sub _ _
        _ ≤ |v.re| + |x| + |c₀| := by linarith [abs_add_le v.re x]
        _ ≤ B := by dsimp [B]; linarith
    refine ⟨(v + t).re - c₀, hwordValue hVzero hV ht hc₀ hbound, ?_⟩
    simp only [Complex.add_re, htx]
    ring
  · intro R hR
    obtain ⟨L, hL, hDense⟩ := nonempty_periodicSet_relativelyDense ⟨c₀, hc₀⟩
      X.period_pos (frontier_periodic X.base_periodic)
    obtain ⟨V, hVfinite, hVzero, hV⟩ := automaticPositiveWordValues W hdelta hminimum
      (R := L + R)
    apply (hVfinite.sub hVfinite).subset
    rintro d ⟨⟨x, hx, y, hy, rfl⟩, hd⟩
    have hxy : |x - y| ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hd
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨c, hc, hcy⟩ := hDense (v.re + y)
    have htBound : |(v + t).re - c| ≤ L + R := by
      rw [Complex.add_re, hty, abs_sub_comm]
      linarith
    have hsBound : |(v + s).re - c| ≤ L + R := by
      rw [Complex.add_re, hsx]
      have heq : v.re + x - c = (x - y) + (v.re + y - c) := by ring
      rw [heq]
      calc
        |x - y + (v.re + y - c)| ≤ |x - y| + |v.re + y - c| := abs_add_le _ _
        _ ≤ L + R := by rw [abs_sub_comm (v.re + y) c]; linarith
    refine ⟨(v + s).re - c, hwordValue hVzero hV hs hc hsBound,
      (v + t).re - c, hwordValue hVzero hV ht hc htBound, ?_⟩
    simp only [Complex.add_re, hsx, hty]
    ring

/-- Automatic horizontal complexity closes the proper-carrier periodicity branch. -/
theorem properCarrierPlate_periodic
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier) (hProper : X.base ≠ Set.univ)
    (hTile : TilesOn K T X.carrier) :
    ∃ beta : ℝ, 0 < beta ∧
      (∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
        Tiling.RationalPolygonal.SetPeriodicBy P.support (beta : ℂ)) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (verticalColumnCentres K T)) (beta : ℂ) :=
  continuousPeriodicCarrierPlate_periodic X hTile
    (properCarrier_hasFiniteHorizontalComplexity X hProper hTile)

private theorem planeFLC_horizontalContactDisplacements_finite
    {K : Region} {T : Set Tiling.Plane}
    (hFLC : Tiling.AxisParallel.HasFLC T) :
    ∀ a b a' b' : ↥K.vertices,
      (Tiling.AxisParallel.Structure.horizontalContactDisplacements
        K T a b a' b').Finite := by
  intro a b a' b'
  have hbounded :=
    Tiling.AxisParallel.Structure.horizontalContactDisplacements_bounded
      K T a b a' b'
  rw [Metric.isBounded_iff_subset_closedBall 0] at hbounded
  obtain ⟨R, hR⟩ := hbounded
  let B : ℝ := |R| + |a.1.im - a'.1.im| + 1
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hfinite : ((T - T) ∩ Metric.closedBall 0 B).Finite := hFLC.2 B hB
  apply (hfinite.image Complex.re).subset
  intro delta hdeltaMem
  have hdelta :=
    (Tiling.AxisParallel.Structure.horizontalContactDisplacements_iff
      K T a b a' b' delta).mp hdeltaMem
  rcases hdelta with
    ⟨hab, habim, habedge, ha'b', ha'b'im, ha'b'edge,
      t, s, hdelta, u, v, huv, huvim, hoverlap⟩
  let p : Tiling.Plane := midpoint ℝ u v
  have hp : p ∈ openSegment ℝ u v := midpoint_mem_openSegment u v
  have hpFirst := (hoverlap hp).1
  have hpSecond := (hoverlap hp).2
  have hpFirstIm : p.im = a.1.im + (t.1 : Tiling.Plane).im := by
    rw [openSegment_eq_image] at hpFirst
    obtain ⟨r, _hr, hpr⟩ := hpFirst
    rw [← hpr]
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    rw [habim]
    ring
  have hpSecondIm : p.im = a'.1.im + (s.1 : Tiling.Plane).im := by
    rw [openSegment_eq_image] at hpSecond
    obtain ⟨r, _hr, hpr⟩ := hpSecond
    rw [← hpr]
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    rw [ha'b'im]
    ring
  let d : Tiling.Plane := (s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)
  have hdT : d ∈ T - T := ⟨s.1, s.2, t.1, t.2, rfl⟩
  have hdre : d.re = delta := by
    dsimp only [d]
    simpa only [Complex.sub_re] using hdelta.symm
  have hdim : d.im = a.1.im - a'.1.im := by
    dsimp only [d]
    simp only [Complex.sub_im]
    linarith [hpFirstIm, hpSecondIm]
  have hdeltaR : |delta| ≤ |R| := by
    have hmem := hR hdeltaMem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
    exact hmem.trans (le_abs_self R)
  have hdNorm : ‖d‖ ≤ |R| + |a.1.im - a'.1.im| := by
    calc
      ‖d‖ ≤ |d.re| + |d.im| := Complex.norm_le_abs_re_add_abs_im d
      _ = |delta| + |a.1.im - a'.1.im| := by rw [hdre, hdim]
      _ ≤ |R| + |a.1.im - a'.1.im| := add_le_add hdeltaR le_rfl
  have hdBall : d ∈ Metric.closedBall 0 B := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hdNorm.trans (by dsimp only [B]; linarith)
  exact ⟨d, ⟨hdT, hdBall⟩, hdre⟩

/-- Planar finite local complexity forces finite horizontal complexity whenever the whole-plane
vertical-plate decomposition is nontrivial. -/
theorem planeFLC_hasFiniteHorizontalComplexity
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (hFLC : Tiling.AxisParallel.HasFLC T)
    (hNontrivial : ¬ ∃ P : VerticalPlate K T,
      ¬ IsVerticalColumn P ∧ P.centres = T) :
    HasFiniteHorizontalComplexity T := by
  by_contra hnotFinite
  obtain ⟨a, b, a', b', hinfinite⟩ :=
    (Tiling.AxisParallel.Structure.infiniteHorizontalComplexity_iff_columnBaseAperiodic
        hTile hNontrivial).2.2.mp hnotFinite
  exact (planeFLC_horizontalContactDisplacements_finite hFLC a b a' b').not_infinite
    hinfinite

/-- The nontrivial whole-plane FLC branch inherits one common horizontal support period. -/
theorem nontrivialPlanePlate_periodic
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (hFLC : Tiling.AxisParallel.HasFLC T)
    (hNontrivial : ¬ ∃ P : VerticalPlate K T,
      ¬ IsVerticalColumn P ∧ P.centres = T) :
    ∃ beta : ℝ, 0 < beta ∧
      (∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
        Tiling.RationalPolygonal.SetPeriodicBy P.support (beta : ℂ)) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (verticalColumnCentres K T)) (beta : ℂ) := by
  let X : PeriodicVerticalCarrier := {
    base := Set.univ
    base_open := isOpen_univ
    base_regular := by simp
    base_nonnull := by simp
    period := 1
    period_pos := zero_lt_one
    base_periodic := by simp }
  have hTileX : TilesOn K T X.carrier := by
    simpa [X, PeriodicVerticalCarrier.carrier] using hTile
  exact continuousPeriodicCarrierPlate_periodic X hTileX
    (planeFLC_hasFiniteHorizontalComplexity hTile hFLC hNontrivial)

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Continuous

/-- The exact finite slab record, including an empty column family and a whole-plane plate. -/
theorem exists_periodicCarrierSlabDecomposition
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier)
    (hCase : X.base ≠ Set.univ ∨ Tiling.AxisParallel.HasFLC T) :
    Nonempty (PeriodicCarrierSlabDecomposition K T X) := by
  classical
  have hperiod : ∃ beta : ℝ, 0 < beta ∧
      (∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
        Tiling.RationalPolygonal.SetPeriodicBy P.support (beta : ℂ)) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (verticalColumnCentres K T)) (beta : ℂ) := by
    by_cases hProper : X.base ≠ Set.univ
    · exact properCarrierPlate_periodic X hProper hTile
    · have hWhole : X.base = Set.univ := not_ne_iff.mp hProper
      have hTilePlane : TilesOn K T Set.univ := by
        simpa [PeriodicVerticalCarrier.carrier, hWhole] using hTile
      have hFLC : Tiling.AxisParallel.HasFLC T := hCase.resolve_left hProper
      by_cases hSingle : ∃ P : VerticalPlate K T,
          ¬ IsVerticalColumn P ∧ P.centres = T
      · obtain ⟨P, hPnoncolumn, hPcentres⟩ := hSingle
        have hPsupport : P.support = Set.univ := by
          rw [P.support_eq_regularSupport, hPcentres,
            regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTilePlane]
        have hPlateEq (Q : VerticalPlate K T) : Q = P := by
          by_contra hQP
          obtain ⟨q, hq⟩ := Q.nonempty_supp
          have hqQ : (q : Tiling.Plane) ∈ Q.centres := ⟨q, hq, rfl⟩
          have hqP : (q : Tiling.Plane) ∈ P.centres := by
            rw [hPcentres]
            exact q.2
          exact Set.disjoint_left.mp
            (verticalPlateCentres_pairwiseDisjoint K T
              (Set.mem_univ Q) (Set.mem_univ P) hQP) hqQ hqP
        have hColumnEmpty : verticalColumnCentres K T = ∅ := by
          ext z
          constructor
          · intro hz
            rw [verticalColumnCentres_eq, Set.mem_iUnion] at hz
            obtain ⟨Q, _⟩ := hz
            exact (hPnoncolumn ((hPlateEq Q.1).symm ▸ Q.2)).elim
          · intro hz
            exact hz.elim
        refine ⟨1, zero_lt_one, ?_, ?_⟩
        · intro Q _
          rw [hPlateEq Q, hPsupport]
          intro z
          simp
        · rw [hColumnEmpty]
          have hempty : regularSupport K (∅ : Set Tiling.Plane) = ∅ := by
            simp [regularSupport, Tiling.Polygonal.regularSupport, Tiling.Polygonal.openUnion]
          rw [hempty]
          intro z
          simp
      · exact nontrivialPlanePlate_periodic hTilePlane hFLC hSingle
  obtain ⟨beta, hbeta, hperiodP, hperiodC⟩ := hperiod
  obtain ⟨n, plate, hplateInj, hplateRange⟩ :=
    (periodicNoncolumnPlates_finite X hTile hbeta hperiodP).fin_param
  have hplateNoncolumn (i : Fin n) : ¬ IsVerticalColumn (plate i) := by
    have hi : plate i ∈ Set.range plate := ⟨i, rfl⟩
    rw [hplateRange] at hi
    exact hi
  have hplateComplete (P : VerticalPlate K T) (hP : ¬ IsVerticalColumn P) :
      ∃ i, plate i = P := by
    have hmem : P ∈ Set.range plate := by rw [hplateRange]; exact hP
    exact hmem
  let columns := verticalColumnCentres K T
  let parts : Option (Fin n) → Set Tiling.Plane
    | none => columns
    | some i => (plate i).centres
  have hcentresCover : columns ∪ (⋃ i, (plate i).centres) = T := by
    ext z
    constructor
    · intro hz
      rcases hz with hzCol | hzPlate
      · exact verticalColumnCentres_subset K T hzCol
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzPlate
        obtain ⟨t, _, rfl⟩ := hi
        exact t.2
    · intro hz
      have hzPlate : z ∈ ⋃ P : VerticalPlate K T, P.centres := by
        rw [iUnion_verticalPlateCentres]
        exact hz
      obtain ⟨P, hzP⟩ := Set.mem_iUnion.mp hzPlate
      by_cases hcol : IsVerticalColumn P
      · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨P, hcol⟩, hzP⟩)
      · obtain ⟨i, hi⟩ := hplateComplete P hcol
        exact Or.inr (Set.mem_iUnion.mpr ⟨i, hi.symm ▸ hzP⟩)
  have hpartsCover : (⋃ i, parts i) = T := by
    simpa only [Set.iUnion_option, parts] using hcentresCover
  have hplateSubset (i : Fin n) : (plate i).centres ⊆ T := by
    rintro z ⟨t, _, rfl⟩
    exact t.2
  have hplatePairwise : Set.PairwiseDisjoint Set.univ
      (fun i : Fin n => (plate i).centres) := by
    intro i _ j _ hij
    exact verticalPlateCentres_pairwiseDisjoint K T
      (Set.mem_univ (plate i)) (Set.mem_univ (plate j))
      (fun h => hij (hplateInj h))
  have hcolumnDisjoint (i : Fin n) :
      Disjoint columns (plate i).centres := by
    apply Set.disjoint_left.mpr
    intro z hzCol hzPlate
    obtain ⟨Q, hzQ⟩ := Set.mem_iUnion.mp hzCol
    have hne : Q.1 ≠ plate i := by
      intro heq
      exact hplateNoncolumn i (heq ▸ Q.2)
    exact Set.disjoint_left.mp
      (verticalPlateCentres_pairwiseDisjoint K T
        (Set.mem_univ Q.1) (Set.mem_univ (plate i)) hne) hzQ hzPlate
  have hsupportPairwise : Set.PairwiseDisjoint Set.univ
      (fun i : Fin n => (plate i).support) := by
    intro i _ j _ hij
    change Disjoint (regularSupport K (plate i).centres)
      (regularSupport K (plate j).centres)
    exact carrierRegularSupports_disjoint X hTile
      (hplateSubset i) (hplateSubset j)
      (hplatePairwise (Set.mem_univ i) (Set.mem_univ j) hij)
  have hcolumnSupportDisjoint (i : Fin n) :
      Disjoint (regularSupport K columns) (plate i).support := by
    rw [VerticalPlate.support_eq_regularSupport]
    exact carrierRegularSupports_disjoint X hTile
      (verticalColumnCentres_subset K T) (hplateSubset i)
      (hcolumnDisjoint i)
  have hsupportsCover :
      interior (closure (regularSupport K columns ∪
        ⋃ i, (plate i).support)) = X.carrier := by
    have hsupport := regularSupport_iUnion (K := K) parts
    rw [hpartsCover] at hsupport
    simp only [Set.iUnion_option, parts] at hsupport
    change interior (closure (regularSupport K columns ∪
      ⋃ i, regularSupport K (plate i).centres)) = X.carrier
    rw [← hsupport]
    exact regularSupport_eq_of_tilesOn
      (X.base_open.preimage Complex.continuous_re)
      (by
        change interior (closure (Complex.re ⁻¹' X.base)) =
          Complex.re ⁻¹' X.base
        rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
          X.base_regular]) hTile
  have hcolumnRegular : interior (closure (aggregateColumnBase K T)) =
      aggregateColumnBase K T := by
    rw [aggregateColumnBase_regularizedProjection X hTile,
      interior_closure_idem]
  have hminimal (P : VerticalPlate K T) :
      IsMinimalVerticalSlabSubfamily K T P.centres :=
    (relativeCarrier_verticalPlates hTile rfl X.base_regular.symm
      (fun a b ↦ by
        simpa only [inter_comm] using hTile.verticalCylinder_frontier_locallyFinite
          X.base_open X.base_regular (Icc a b) isCompact_Icc)).2.1 P
  have hColumnData : ∃ (H : Set ℝ) (Y : ℝ → Set ℝ),
      columns = {z : Tiling.Plane | ∃ h ∈ H, z.re = h ∧ z.im ∈ Y h} ∧
      (columns.Nonempty → H.Nonempty ∧
        (∀ h ∈ H, IsCenterColumn Axis.vertical K
          {z : Tiling.Plane | z.re = h ∧ z.im ∈ Y h}) ∧
        ∃ alpha betaAxis : ℝ, 0 < alpha ∧ 0 < betaAxis ∧
          betaAxis +ᵥ H = H ∧
          (∀ h ∈ H, alpha +ᵥ Y h = Y h) ∧
          ∀ w : ℝ, ∃ S : Set Tiling.Plane,
            Tiling.IsPacking K.toPolygonalRegion.prototileFamily
              (K.toPolygonalRegion.placements S) ∧
            regularSupport K S = regularSupport K columns ∧
            Tiling.RationalPolygonal.SetPeriodicBy S
              ((alpha : ℂ) * Complex.I) ∧
            Tiling.RationalPolygonal.SetPeriodicBy S
              ((betaAxis : ℂ) + (w : ℂ) * Complex.I) ∧
            IsLatticePeriodic S) := by
    by_cases hCol : columns.Nonempty
    · obtain ⟨D⟩ := completeColumnFamilyData_exists X hTile hCol hbeta hperiodC
      refine ⟨D.axes, D.fibre, D.centres_formula, fun _ => ?_⟩
      exact ⟨D.axes_nonempty, D.fibre_columns,
        D.verticalPeriod, D.horizontalPeriod,
        D.verticalPeriod_pos, D.horizontalPeriod_pos,
        D.axes_periodic, D.fibre_periodic,
        completeColumnFamily_freeShear D⟩
    · refine ⟨carrierAxes K T, carrierFibre K T,
        carrierCentres_formula K T, ?_⟩
      exact fun h => (hCol h).elim
  obtain ⟨H, Y, hColumnFormula, hColumnInterface⟩ := hColumnData
  refine ⟨{
    source_tiles := hTile
    numberOfNonColumnPlates := n
    nonColumnPlate := plate
    nonColumnPlate_noncolumn := hplateNoncolumn
    nonColumnPlate_injective := hplateInj
    nonColumnPlate_complete := hplateComplete
    columnCentres := columns
    columnCentres_eq := rfl
    centres_partition := hcentresCover
    nonColumnCentres_pairwise := hplatePairwise
    column_nonColumn_disjoint := hcolumnDisjoint
    commonSupportPeriod := beta
    commonSupportPeriod_pos := hbeta
    nonColumnSupport_periodic := fun i => hperiodP (plate i) (hplateNoncolumn i)
    columnBase := aggregateColumnBase K T
    columnBase_regular := hcolumnRegular
    columnSupport_eq := aggregateColumnSupport_eq_cylinder X hTile
    columnSupport_periodic := hperiodC
    nonColumnSupports_pairwise := hsupportPairwise
    column_nonColumnSupport_disjoint := hcolumnSupportDisjoint
    supports_cover := hsupportsCover
    nonColumn_minimal := fun i => hminimal (plate i)
    columnAxes := H
    columnFibre := Y
    columnCentres_formula := hColumnFormula
    columnInterface := hColumnInterface }⟩

end Tiling.AxisParallel.Terminal
