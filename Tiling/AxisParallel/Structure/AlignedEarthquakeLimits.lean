import Tiling.AxisParallel.Continuous.HorizontalComplexityCore
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.ContinuousSlabPeriodicity
import Tiling.AxisParallel.Continuous.PositiveSimilarityPlates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Tiling.AxisParallel.Continuous.PlateCore
import Tiling.AxisParallel.Topology.HullCore

import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Continuous.WeakTilingTopology
import Tiling.AxisParallel.Structure.PlateThickness
import Tiling.AxisParallel.Structure.HorizontalComplexityUnderWeakLimits

/-!
# S10 aligned earthquake limits — FULL11 cumulative checkpoint

This production owner retains the historical owner record and four
public eliminators, the accepted private PREFIX9 blocks, the exact private
reverse-cardinality target10, and the public constructor target11.
The finite-colour and column-equality prerequisites are included as the
accepted PREFIX9 prefix; no declarations beyond target11 are included.
-/


open Filter MeasureTheory Set
open scoped Pointwise Topology
open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Topology

noncomputable section

namespace Tiling.AxisParallel.Structure

/-- A common-subsequence limit in which the column colour and every noncolumn plate colour
converge separately, while retaining their exact component decomposition. -/
structure AlignedEarthquakeLimitData
    {K : Tiling.AxisParallel.Region}
    (T S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ)
    (beta : ℝ)
    (g : ℕ → Tiling.AxisParallel.aePeriodGroup
      (Set.univ : Set Tiling.Plane)) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  ambient_converges : Tiling.AxisParallel.Topology.LocallyFellConverges
    (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
      (Tiling.AxisParallel.Topology.TilingSpace.translateSequence
        (fun n ↦ g (subsequence n)) T))
    (S.centres : Set Tiling.Plane)
  sourceNonColumn_finite :
    (Tiling.AxisParallel.Continuous.nonColumnVerticalPlates
      K (T.centres : Set Tiling.Plane)).Finite
  targetNonColumn_finite :
    (Tiling.AxisParallel.Continuous.nonColumnVerticalPlates
      K (S.centres : Set Tiling.Plane)).Finite
  columnLimit : Set Tiling.Plane
  nonColumnLimit :
    ↑(Tiling.AxisParallel.Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane)) →
      Set Tiling.Plane
  column_converges : Tiling.AxisParallel.Topology.LocallyFellConverges
    (fun n ↦ ((g (subsequence n) : Tiling.Plane) +ᵥ
      Tiling.AxisParallel.Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane)))
    columnLimit
  nonColumn_converges : ∀ P,
    Tiling.AxisParallel.Topology.LocallyFellConverges
      (fun n ↦ ((g (subsequence n) : Tiling.Plane) +ᵥ P.1.centres))
      (nonColumnLimit P)
  coloured_union :
    columnLimit ∪ (⋃ P, nonColumnLimit P) =
      (S.centres : Set Tiling.Plane)
  coloured_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ nonColumnLimit
  column_disjoint_nonColumn : ∀ P, Disjoint columnLimit (nonColumnLimit P)
  columnLimit_eq :
    columnLimit =
      Tiling.AxisParallel.Continuous.verticalColumnCentres K
        (S.centres : Set Tiling.Plane)
  plateEquiv :
    ↑(Tiling.AxisParallel.Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane)) ≃
      ↑(Tiling.AxisParallel.Continuous.nonColumnVerticalPlates K
        (S.centres : Set Tiling.Plane))
  nonColumnLimit_eq : ∀ P, nonColumnLimit P = (plateEquiv P).1.centres
  columnSupport_eq :
    Tiling.AxisParallel.regularSupport K columnLimit =
      Tiling.AxisParallel.regularSupport K
        (Tiling.AxisParallel.Continuous.verticalColumnCentres K
          (T.centres : Set Tiling.Plane))
  columnBase_eq :
    Complex.re '' Tiling.AxisParallel.regularSupport K columnLimit =
      Complex.re '' Tiling.AxisParallel.regularSupport K
        (Tiling.AxisParallel.Continuous.verticalColumnCentres K
          (T.centres : Set Tiling.Plane))
  nonColumnSupport_eq : ∀ P,
    Tiling.AxisParallel.regularSupport K (nonColumnLimit P) = P.1.support
  nonColumnBase_eq : ∀ P, (plateEquiv P).1.base = P.1.base
  targetFiniteHorizontalComplexity :
    Tiling.AxisParallel.Continuous.HasFiniteHorizontalComplexity
      (S.centres : Set Tiling.Plane)
  limit_mem_orbitHull : S ∈ Tiling.AxisParallel.Topology.orbitHull T
  limit_orbitHull_eq :
    Tiling.AxisParallel.Topology.orbitHull S =
      Tiling.AxisParallel.Topology.orbitHull T
  limit_minimal : Tiling.AxisParallel.Topology.IsTopologicallyMinimal
    (Tiling.AxisParallel.Topology.orbitHull S)
  targetColumnSupport_periodic :
    Tiling.RationalPolygonal.SetPeriodicBy
      (Tiling.AxisParallel.regularSupport K
        (Tiling.AxisParallel.Continuous.verticalColumnCentres K
          (S.centres : Set Tiling.Plane)))
      ((beta : ℝ) : ℂ)
  targetNonColumnSupport_periodic : ∀ Q :
      Tiling.AxisParallel.Continuous.VerticalPlate K
        (S.centres : Set Tiling.Plane),
    ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn Q →
      Tiling.RationalPolygonal.SetPeriodicBy Q.support ((beta : ℝ) : ℂ)

private theorem verticalPlate_centres_nonempty
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T) :
    P.centres.Nonempty := by
  obtain ⟨t, ht⟩ := P.nonempty_supp
  exact ⟨t.1, t, ht, rfl⟩

private theorem verticalPlate_centres_subset
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T) :
    P.centres ⊆ T := by
  rintro _ ⟨t, _, rfl⟩
  exact t.2

private theorem verticalPlate_eq_of_common_centre
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {P Q : Tiling.AxisParallel.Continuous.VerticalPlate K T}
    {x : Tiling.Plane} (hxP : x ∈ P.centres) (hxQ : x ∈ Q.centres) :
    P = Q := by
  obtain ⟨p, hpP, hpx⟩ := hxP
  obtain ⟨q, hqQ, hqx⟩ := hxQ
  have hpq : p = q := Subtype.ext (hpx.trans hqx.symm)
  subst q
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hpP hqQ

private structure FinitePlateColourLimitData
    {K : Region} (T S : TilingSpace K Set.univ)
    (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  ambient_converges : LocallyFellConverges
    (TilingSpace.centresSequence
      (TilingSpace.translateSequence (fun n => g (subsequence n)) T))
    (S.centres : Set Tiling.Plane)
  sourceNonColumn_finite :
    (Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)).Finite
  targetNonColumn_finite :
    (Continuous.nonColumnVerticalPlates K (S.centres : Set Tiling.Plane)).Finite
  columnLimit : Set Tiling.Plane
  nonColumnLimit :
    ↑(Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)) →
      Set Tiling.Plane
  column_converges : LocallyFellConverges
    (fun n => (g (subsequence n) : Tiling.Plane) +ᵥ
      Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane)) columnLimit
  nonColumn_converges : ∀ P, LocallyFellConverges
    (fun n => (g (subsequence n) : Tiling.Plane) +ᵥ P.1.centres) (nonColumnLimit P)
  nonColumnLimit_nonempty : ∀ P, (nonColumnLimit P).Nonempty
  coloured_union : columnLimit ∪ (⋃ P, nonColumnLimit P) = (S.centres : Set Tiling.Plane)
  coloured_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ nonColumnLimit
  column_disjoint_nonColumn : ∀ P, Disjoint columnLimit (nonColumnLimit P)
  columnSupport_eq : regularSupport K columnLimit =
    regularSupport K (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane))
  nonColumnSupport_eq : ∀ P, regularSupport K (nonColumnLimit P) = P.1.support

private def targetPlateBlock {K : Region} {T S : Topology.TilingSpace K Set.univ}
    {g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    (D : FinitePlateColourLimitData T S g)
    (P : ↑(Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane))) :
    Set ↑(Continuous.nonColumnVerticalPlates K (S.centres : Set Tiling.Plane)) :=
  {Q | Q.1.centres ⊆ D.nonColumnLimit P}

private theorem nonColumnVerticalPlates_finite :
    ∀ {K : Region} (T : TilingSpace K Set.univ),
      (Continuous.nonColumnVerticalPlates K
        (T.centres : Set Tiling.Plane)).Finite := by
  intro K T
  exact (noncolumnVerticalPlates_finite T.tilesOn).1

private theorem alignedLimit_dynamicalFacts :
    ∀ {K : Region} (T S : TilingSpace K Set.univ),
      IsTopologicallyMinimal (orbitHull T) →
      Continuous.HasFiniteHorizontalComplexity (T.centres : Set Tiling.Plane) →
      ∀ (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)),
      LocallyFellConverges
        (TilingSpace.centresSequence
          (TilingSpace.translateSequence g T)) (S.centres : Set Tiling.Plane) →
      S ∈ orbitHull T ∧ orbitHull S = orbitHull T ∧
      IsTopologicallyMinimal (orbitHull S) ∧
      Continuous.HasFiniteHorizontalComplexity (S.centres : Set Tiling.Plane) := by
  intro K T S hminimal hFHC g hconverges
  have hTend : Tendsto (fun n => TilingSpace.translate (g n) T)
      atTop (nhds S) :=
    ((locallyFell_metrizable K Set.univ).2
      (TilingSpace.translateSequence g T) S).2 hconverges
  have hSmem : S ∈ orbitHull T := by
    apply mem_closure_iff_nhds.2
    intro U hU
    have hEventually : ∀ᶠ n : ℕ in atTop,
        TilingSpace.translate (g n) T ∈ U := hTend hU
    obtain ⟨n, hn⟩ := hEventually.exists
    exact ⟨TilingSpace.translate (g n) T, hn,
      AddAction.mem_orbit T (g n)⟩
  have hHull : orbitHull S = orbitHull T :=
    hminimal.2.2.2 S hSmem
  have hMinS : IsTopologicallyMinimal (orbitHull S) := by
    rw [hHull]
    exact hminimal
  have hFHC_S := finiteHorizontalComplexity_of_translateLimit T S hFHC g hconverges
  exact ⟨hSmem, hHull, hMinS, hFHC_S⟩
private theorem verticalPlate_support_nonempty
    {K : Region} {T : Set Tiling.Plane}
    (P : Continuous.VerticalPlate K T) : P.support.Nonempty := by
  obtain ⟨t, ht⟩ := P.nonempty_supp
  obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hzt : z ∈ K.openCarrier := by
    change z ∈ interior K.support
    exact hz
  have htcentre : (t.1 : Tiling.Plane) ∈ P.centres := ⟨t, ht, rfl⟩
  have hopen : (t.1 : Tiling.Plane) +ᵥ z ∈ openUnion K P.centres := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    refine ⟨⟨t.1, htcentre⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [vadd_eq_add]
    simpa [sub_eq_add_neg, add_comm] using hzt
  refine ⟨(t.1 : Tiling.Plane) +ᵥ z, ?_⟩
  apply (isOpen_iUnion fun s : P.centres ↦
    (Homeomorph.addLeft (s : Tiling.Plane)).isOpenMap _
      K.openCarrier_regularOpen.1).subset_interior_closure
  exact hopen


private theorem tilesOn_regularSupport_of_subset
    {K : Region} {T A : Set Tiling.Plane}
    (hT : TilesOn K T Set.univ) (hA : A ⊆ T) :
    TilesOn K A (regularSupport K A) := by
  have hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K A).mpr
    intro s hs t ht hst
    exact (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp hT.2.1
      (hA hs) (hA ht) hst
  refine ⟨hT.1.mono hA, hpack, ?_⟩
  filter_upwards [Tiling.AxisParallel.openUnion_aeEq_regularSupport hpack] with x hx
  have hiff : x ∈ openUnion K A ↔ x ∈ regularSupport K A := iff_of_eq hx
  simpa only [openUnion, Tiling.Polygonal.openUnion,
    ← Region.openCarrier.eq_def, Set.mem_iUnion] using hiff.symm

private theorem tilesOn_centres_closed
    {K : Region} {A E : Set Tiling.Plane}
    (hA : TilesOn K A E) : IsClosed A := by
  obtain ⟨delta, hdelta, hseparation⟩ := Tiling.AxisParallel.exists_packingSeparation K
  apply Metric.isClosed_of_pairwise_le_dist hdelta
  intro x hx y hy hxy
  exact hseparation A hA.2.1 x hx y hy hxy

private theorem tilesOn_centres_nonempty_of_nonempty_carrier
    {K : Region} {A E : Set Tiling.Plane}
    (hA : TilesOn K A E) (hE : E.Nonempty)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E) : A.Nonempty := by
  have hreg : regularSupport K A = E :=
    regularSupport_eq_of_tilesOn hEopen hEregular hA
  by_contra hne
  have hAempty : A = ∅ := not_nonempty_iff_eq_empty.mp hne
  have hregempty : regularSupport K A = ∅ := by
    simp [hAempty, regularSupport, Tiling.Polygonal.regularSupport, Tiling.Polygonal.openUnion]
  rw [hreg] at hregempty
  exact hE.ne_empty hregempty

private theorem locallyFell_limit_subset_of_subsets
    {A B : ℕ → Set Tiling.Plane} {L M : Set Tiling.Plane}
    (hsub : ∀ n, A n ⊆ B n)
    (hA : LocallyFellConverges A L)
    (hB : LocallyFellConverges B M) : L ⊆ M := by
  intro x hxL
  by_contra hxM
  have hxMc : x ∈ Mᶜ := hxM
  obtain ⟨hBclosed, hMclosed, hBfell⟩ := hB
  have hB' : LocallyFellConverges B M := ⟨hBclosed, hMclosed, hBfell⟩
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_compl_iff.mpr hMclosed) x hxMc
  let C : Set Tiling.Plane := Metric.closedBall x (epsilon / 2)
  have hCcompact : IsCompact C := by
    exact isCompact_closedBall _ _
  have heps2 : 0 < epsilon / 2 := by positivity
  have hCM : Disjoint M C := by
    rw [Set.disjoint_left]
    intro z hzM hzC
    change dist z x ≤ epsilon / 2 at hzC
    have hzMc : z ∈ Mᶜ := hball (by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (by simpa [dist_comm] using hzC) (by linarith))
    exact hzMc hzM
  have havoid := Tiling.AxisParallel.Topology.locallyFellConverges_eventually_disjoint_compact
    hB' hCcompact hCM
  have hhit := Tiling.AxisParallel.Topology.locallyFellConverges_eventually_exists_mem_ball
    hA hxL heps2
  obtain ⟨n, ⟨y, hyA, hyx⟩, hn⟩ := (hhit.and havoid).exists
  exact Set.disjoint_left.mp hn (hsub n hyA)
    (by
      change dist y x ≤ epsilon / 2
      exact le_of_lt hyx)

set_option linter.unusedFintypeInType false in
private theorem finiteColour_union_of_partition
    {I : Type*} [Fintype I]
    {A : ℕ → I → Set Tiling.Plane} {B : ℕ → Set Tiling.Plane}
    {L : I → Set Tiling.Plane} {M : Set Tiling.Plane}
    (hpartition : ∀ n, (⋃ i, A n i) = B n)
    (hcolour : ∀ i, LocallyFellConverges (fun n => A n i) (L i))
    (hambient : LocallyFellConverges B M) :
    (⋃ i, L i) = M := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    apply locallyFell_limit_subset_of_subsets
      (fun n y hy => by
        rw [← hpartition n]
        exact Set.mem_iUnion.2 ⟨i, hy⟩)
      (hcolour i) hambient hxi
  · intro x hxM
    by_contra hxU
    let U : Set Tiling.Plane := ⋃ i, L i
    have hLiClosed : ∀ i, IsClosed (L i) := by
      intro i
      exact (Exists.choose_spec (hcolour i)).choose
    have hUclosed : IsClosed U := by
      exact isClosed_iUnion_of_finite hLiClosed
    have hxUc : x ∈ Uᶜ := hxU
    obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp
      (isOpen_compl_iff.mpr hUclosed) x hxUc
    let C : Set Tiling.Plane := Metric.closedBall x (epsilon / 2)
    have hCcompact : IsCompact C := by
      exact isCompact_closedBall _ _
    have heps2 : 0 < epsilon / 2 := by positivity
    have havoid (i : I) :=
      Tiling.AxisParallel.Topology.locallyFellConverges_eventually_disjoint_compact
        (hcolour i) hCcompact (by
          rw [Set.disjoint_left]
          intro z hzL hzC
          change dist z x ≤ epsilon / 2 at hzC
          have hzUc : z ∈ Uᶜ := hball (by
            rw [Metric.mem_ball]
            exact lt_of_le_of_lt (by simpa [dist_comm] using hzC) (by linarith))
          exact hzUc (Set.mem_iUnion.2 ⟨i, hzL⟩))
    have havoidAll : ∀ᶠ n : ℕ in atTop, ∀ i, Disjoint (A n i) C := by
      have hall := (Filter.eventually_all_finset (Finset.univ : Finset I)).2
        (fun i hi => havoid i)
      filter_upwards [hall] with n hn i
      exact hn i (Finset.mem_univ i)
    have hhit :=
      Tiling.AxisParallel.Topology.locallyFellConverges_eventually_exists_mem_ball
        hambient hxM heps2
    obtain ⟨n, ⟨y, hyB, hyx⟩, hn⟩ := (hhit.and havoidAll).exists
    rw [← hpartition n] at hyB
    rcases Set.mem_iUnion.mp hyB with ⟨i, hyA⟩
    exact Set.disjoint_left.mp (hn i) hyA (by
      change dist y x ≤ epsilon / 2
      exact le_of_lt hyx)

set_option linter.unusedFintypeInType false in
private theorem finiteColour_pairwiseDisjoint_of_separation
    {I : Type*} [Fintype I]
    {A : ℕ → I → Set Tiling.Plane} {L : I → Set Tiling.Plane}
    {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∀ n i j, i ≠ j → ∀ x ∈ A n i, ∀ y ∈ A n j,
      delta ≤ dist x y)
    (hcolour : ∀ i, LocallyFellConverges (fun n => A n i) (L i)) :
    Set.PairwiseDisjoint Set.univ L := by
  intro i _ j _ hij
  change Disjoint (L i) (L j)
  rw [Set.disjoint_left]
  intro x hxi hxj
  have heps : 0 < delta / 3 := by positivity
  have hi := Tiling.AxisParallel.Topology.locallyFellConverges_eventually_exists_mem_ball
    (hcolour i) hxi heps
  have hj := Tiling.AxisParallel.Topology.locallyFellConverges_eventually_exists_mem_ball
    (hcolour j) hxj heps
  obtain ⟨n, ⟨y, hyi, hyx⟩, ⟨z, hzj, hzx⟩⟩ := (hi.and hj).exists
  have hdist : dist y z < 2 * (delta / 3) := by
    calc
      dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
      _ < 2 * (delta / 3) := by
        have hyx' : dist y x < delta / 3 := hyx
        have hzx' : dist x z < delta / 3 := by simpa [dist_comm] using hzx
        linarith
  have hlower := hsep n i j hij y hyi z hzj
  linarith

private theorem verticalColumn_nonColumn_partition
    {K : Region} {T : Set Tiling.Plane} :
    verticalColumnCentres K T ∪
        (⋃ P : ↑(Continuous.nonColumnVerticalPlates K T), P.1.centres) = T := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hxcol | hxnon
    · rw [Continuous.verticalColumnCentres_eq] at hxcol
      rcases Set.mem_iUnion.mp hxcol with ⟨P, hxP⟩
      rw [← iUnion_verticalPlateCentres K T]
      exact Set.mem_iUnion.2 ⟨P.1, hxP⟩
    · rcases Set.mem_iUnion.mp hxnon with ⟨P, hxP⟩
      rw [← iUnion_verticalPlateCentres K T]
      exact Set.mem_iUnion.2 ⟨P.1, hxP⟩
  · intro x hx
    have hxall : x ∈ (⋃ P : Continuous.VerticalPlate K T, P.centres) := by
      rw [iUnion_verticalPlateCentres K T]
      exact hx
    rcases Set.mem_iUnion.mp hxall with ⟨P, hxP⟩
    by_cases hcol : Continuous.IsVerticalColumn P
    · exact Set.mem_union_left _ (by
        rw [Continuous.verticalColumnCentres_eq]
        exact Set.mem_iUnion.2 ⟨⟨P, hcol⟩, hxP⟩)
    · exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨⟨P, hcol⟩, hxP⟩)


set_option linter.style.haveILetI false in
private theorem sourceColour_pairwiseDisjoint
    {K : Region} {T : Set Tiling.Plane}
    (_hsource : (Continuous.nonColumnVerticalPlates K T).Finite) :
    Set.PairwiseDisjoint Set.univ
      (fun i : Option ↑(Continuous.nonColumnVerticalPlates K T) =>
        match i with
        | none => Continuous.verticalColumnCentres K T
        | some P => P.1.centres) := by
  letI : Fintype (↑(Continuous.nonColumnVerticalPlates K T)) := _hsource.fintype
  intro i _ j _ hij
  cases i with
  | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some P =>
          change Disjoint (Continuous.verticalColumnCentres K T) P.1.centres
          rw [Continuous.verticalColumnCentres_eq, Set.disjoint_left]
          intro x hxcol hxP
          rcases Set.mem_iUnion.mp hxcol with ⟨Q, hxQ⟩
          have hne : Q.1 ≠ P.1 := by
            intro heq
            exact P.2 (heq ▸ Q.2)
          have hdisj : Disjoint Q.1.centres P.1.centres := by
            apply verticalPlateCentres_pairwiseDisjoint K T
            · exact Set.mem_univ _
            · exact Set.mem_univ _
            exact hne
          exact Set.disjoint_left.mp hdisj hxQ hxP
  | some P =>
      cases j with
      | none =>
          change Disjoint P.1.centres (Continuous.verticalColumnCentres K T)
          rw [Continuous.verticalColumnCentres_eq, Set.disjoint_left]
          intro x hxP hxcol
          rcases Set.mem_iUnion.mp hxcol with ⟨Q, hxQ⟩
          have hne : P.1 ≠ Q.1 := by
            intro heq
            exact P.2 (heq ▸ Q.2)
          have hdisj : Disjoint P.1.centres Q.1.centres := by
            apply verticalPlateCentres_pairwiseDisjoint K T
            · exact Set.mem_univ _
            · exact Set.mem_univ _
            exact hne
          exact Set.disjoint_left.mp hdisj hxP hxQ
      | some Q =>
          change Disjoint P.1.centres Q.1.centres
          rw [Set.disjoint_left]
          intro x hxP hxQ
          have heq : P.1 = Q.1 := verticalPlate_eq_of_common_centre hxP hxQ
          have hpeq : P = Q := Subtype.ext heq
          exact hij (congrArg some hpeq)


private theorem vadd_vadd_set (a b : Tiling.Plane) (A : Set Tiling.Plane) :
    (a + b) +ᵥ A = a +ᵥ (b +ᵥ A) := by
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  constructor <;> intro hx
  · have heq : -(a + b) + x = -b + (-a + x) := by abel
    rw [heq] at hx
    exact hx
  · have heq : -b + (-a + x) = -(a + b) + x := by abel
    rw [heq] at hx
    exact hx

private theorem setPeriodicBy_int_vadd_eq
    {A : Set Tiling.Plane} {beta : ℝ}
    (hperiod : Tiling.RationalPolygonal.SetPeriodicBy A ((beta : ℝ) : ℂ))
    (m : ℤ) : ((m : ℝ) * beta : ℂ) +ᵥ A = A := by
  have hstep : ((beta : ℝ) : ℂ) +ᵥ A = A := by
    ext z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    simpa [Tiling.RationalPolygonal.SetPeriodicBy, add_comm, add_left_comm,
      add_assoc] using (hperiod (-((beta : ℝ) : ℂ) + z)).symm
  refine Int.induction_on m (by simp) (fun m ih => ?_) (fun m ih => ?_)
  · norm_num [Int.cast_add, add_mul]
    norm_num at ih ⊢
    rw [vadd_vadd_set, hstep, ih]
  · have hstep' : (-((beta : ℝ) : ℂ)) +ᵥ A = A := by
      calc
        (-((beta : ℝ) : ℂ)) +ᵥ A = (-((beta : ℝ) : ℂ)) +ᵥ
            (((beta : ℝ) : ℂ) +ᵥ A) := by rw [hstep]
        _ = ((-((beta : ℝ) : ℂ)) + ((beta : ℝ) : ℂ)) +ᵥ A := by
          rw [vadd_vadd_set]
        _ = A := by simp
    norm_num [Int.cast_sub, sub_mul]
    norm_num at ih ⊢
    have heq : -(↑m * (beta : ℂ)) - (beta : ℂ) =
        (-(↑m * (beta : ℂ))) + (-(beta : ℂ)) := by ring
    rw [heq, vadd_vadd_set, hstep', ih]

private theorem vertical_shift_support_eq
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : Continuous.VerticalPlate K T)
    {beta : ℝ}
    (hperiod : Tiling.RationalPolygonal.SetPeriodicBy P.support
      ((beta : ℝ) : ℂ)) (m : ℤ) (a : ℝ) :
    ((((m : ℝ) * beta : ℝ) : ℂ) + (a : ℂ) * Complex.I) +ᵥ P.support = P.support := by
  obtain ⟨hbase, hsupport⟩ := P.support_isVerticalSlab hTile
  have hhor : (((m : ℝ) * beta : ℝ) : ℂ) +ᵥ P.support = P.support := by
    simpa only [Complex.ofReal_mul] using setPeriodicBy_int_vadd_eq hperiod m
  have hsum : ((((m : ℝ) * beta : ℝ) : ℂ) + (a : ℂ) * Complex.I) +ᵥ P.support =
      ((a : ℂ) * Complex.I) +ᵥ
        ((((m : ℝ) * beta : ℝ) : ℂ) +ᵥ P.support) := by
    ext z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    constructor <;> intro hz
    · have heq : -(↑(↑m * beta) + ↑a * Complex.I) + z =
          -↑(↑m * beta) + (-(↑a * Complex.I) + z) := by abel
      rw [heq] at hz
      exact hz
    · have heq : -↑(↑m * beta) + (-(↑a * Complex.I) + z) =
          -(↑(↑m * beta) + ↑a * Complex.I) + z := by abel
      rw [heq] at hz
      exact hz
  calc
    _ = ((a : ℂ) * Complex.I) +ᵥ
        ((((m : ℝ) * beta : ℝ) : ℂ) +ᵥ P.support) := hsum
    _ = ((a : ℂ) * Complex.I) +ᵥ P.support := by rw [hhor]
    _ = P.support := by
      rw [hsupport]
      ext z
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_preimage, vadd_eq_add]
      simp

private theorem tilesOn_shifted_nonColumnColour
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : Continuous.VerticalPlate K T)
    {beta : ℝ}
    (hPperiod : Tiling.RationalPolygonal.SetPeriodicBy P.support
      ((beta : ℝ) : ℂ))
    {u : Tiling.Plane} {m : ℤ} {a : ℝ}
    (hu : u = (((m : ℝ) * beta : ℝ) : ℂ) + (a : ℂ) * Complex.I) :
    TilesOn K (u +ᵥ P.centres) P.support := by
  have hPtiles := tilesOn_regularSupport_of_subset (A := P.centres) hTile (by
    rintro x ⟨q, hq, rfl⟩
    exact q.2)
  have hsupport := vertical_shift_support_eq hTile P hPperiod m a
  have htranslated := Tiling.AxisParallel.tilesOn_translate hPtiles u
  have hPsupport : regularSupport K P.centres = P.support := rfl
  rw [hPsupport, hu, hsupport] at htranslated
  simpa only [hu] using htranslated

private theorem verticalColumnSupport_vadd
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (a : ℝ) :
    ((a : ℂ) * Complex.I) +ᵥ
        regularSupport K (Continuous.verticalColumnCentres K T) =
      regularSupport K (Continuous.verticalColumnCentres K T) := by
  rw [Continuous.verticalColumnCentres_eq, regularSupport_iUnion]
  let U : Set Tiling.Plane := ⋃ P : {P : Continuous.VerticalPlate K T //
      Continuous.IsVerticalColumn P}, regularSupport K P.1.centres
  have hU : ((a : ℂ) * Complex.I) +ᵥ U = U := by
    ext z
    simp only [U, Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_iUnion]
    constructor
    · rintro ⟨P, hz⟩
      refine ⟨P, ?_⟩
      have hC := P.1.isCenterColumn_of_isVerticalColumn hTile P.2
      have hInv : ((a : ℂ) * Complex.I) +ᵥ
          regularSupport K P.1.centres = regularSupport K P.1.centres := by
        simpa using hC.2.2.2 a
      have hz' : z ∈ ((a : ℂ) * Complex.I) +ᵥ
          regularSupport K P.1.centres := by
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using hz
      rw [hInv] at hz'
      exact hz'
    · rintro ⟨P, hz⟩
      refine ⟨P, ?_⟩
      have hC := P.1.isCenterColumn_of_isVerticalColumn hTile P.2
      have hInv : ((a : ℂ) * Complex.I) +ᵥ
          regularSupport K P.1.centres = regularSupport K P.1.centres := by
        simpa using hC.2.2.2 a
      rw [← hInv] at hz
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using hz
  change ((a : ℂ) * Complex.I) +ᵥ interior (closure U) = interior (closure U)
  calc
    ((a : ℂ) * Complex.I) +ᵥ interior (closure U) =
        interior (((a : ℂ) * Complex.I) +ᵥ closure U) :=
      (interior_vadd _ _).symm
    _ = interior (closure (((a : ℂ) * Complex.I) +ᵥ U)) := by
      rw [closure_vadd]
    _ = interior (closure U) := by rw [hU]

private theorem tilesOn_shifted_columnColour
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    {beta : ℝ}
    (hperiod : Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K (Continuous.verticalColumnCentres K T))
      ((beta : ℝ) : ℂ))
    {u : Tiling.Plane} {m : ℤ} {a : ℝ}
    (hu : u = (((m : ℝ) * beta : ℝ) : ℂ) + (a : ℂ) * Complex.I) :
    TilesOn K (u +ᵥ Continuous.verticalColumnCentres K T)
      (regularSupport K (Continuous.verticalColumnCentres K T)) := by
  let C : Set Tiling.Plane := Continuous.verticalColumnCentres K T
  have hCsub : C ⊆ T := by
    intro x hx
    change x ∈ Continuous.verticalColumnCentres K T at hx
    rw [Continuous.verticalColumnCentres_eq, Set.mem_iUnion] at hx
    obtain ⟨P, hx⟩ := hx
    rcases hx with ⟨q, hq, rfl⟩
    exact q.2
  have hCtiles := tilesOn_regularSupport_of_subset (A := C) hTile hCsub
  have hvertical := verticalColumnSupport_vadd hTile a
  have hhorizontal : (((m : ℝ) * beta : ℝ) : ℂ) +ᵥ
      regularSupport K C = regularSupport K C := by
    simpa only [Complex.ofReal_mul] using
      setPeriodicBy_int_vadd_eq hperiod m
  have hsum : ((((m : ℝ) * beta : ℝ) : ℂ) + (a : ℂ) * Complex.I) +ᵥ
      regularSupport K C = ((a : ℂ) * Complex.I) +ᵥ
        ((((m : ℝ) * beta : ℝ) : ℂ) +ᵥ regularSupport K C) := by
    ext z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    constructor <;> intro hz
    · have heq : -(↑(↑m * beta) + ↑a * Complex.I) + z =
          -↑(↑m * beta) + (-(↑a * Complex.I) + z) := by abel
      rw [heq] at hz
      exact hz
    · have heq : -↑(↑m * beta) + (-(↑a * Complex.I) + z) =
          -(↑(↑m * beta) + ↑a * Complex.I) + z := by abel
      rw [heq] at hz
      exact hz
  have hsupport : u +ᵥ regularSupport K C = regularSupport K C := by
    rw [hu, hsum, hhorizontal, hvertical]
  have htranslated := Tiling.AxisParallel.tilesOn_translate hCtiles u
  rw [hsupport] at htranslated
  simpa only [C] using htranslated

set_option linter.style.haveILetI false in
private theorem finiteColour_product_compact
    {K : Region} {I : Type} (_hI : Fintype I)
    (E : I → Set Tiling.Plane) :
    IsCompact (Set.univ : Set (∀ i, TilingSpace K (E i))) := by
  letI := _hI
  letI (i : I) : CompactSpace (TilingSpace K (E i)) :=
    ⟨tilingSpace_compact K (E i)⟩
  exact isCompact_univ

set_option linter.style.haveILetI false in
private theorem finiteColour_common_subsequence
    {K : Region} {I : Type} (_hI : Fintype I)
    (E : I → Set Tiling.Plane)
    (U : ℕ → ∀ i, TilingSpace K (E i)) :
    ∃ (φ : ℕ → ℕ) (V : ∀ i, TilingSpace K (E i)),
      StrictMono φ ∧ Tendsto (U ∘ φ) atTop (nhds V) := by
  letI := _hI
  letI (i : I) : CompactSpace (TilingSpace K (E i)) :=
    ⟨tilingSpace_compact K (E i)⟩
  letI : CompactSpace (∀ i, TilingSpace K (E i)) := inferInstance
  obtain ⟨V, _, φ, hφ, hlim⟩ :=
    (isCompact_univ.isSeqCompact
      (s := (Set.univ : Set (∀ i, TilingSpace K (E i))))
      (fun _ => Set.mem_univ _))
  exact ⟨φ, V, hφ, hlim⟩


set_option linter.style.haveILetI false in
private theorem finiteColour_spaceSequence
    {K : Region} (T S : TilingSpace K Set.univ) {beta : ℝ}
    (hcolumnPeriod : Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K (Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane))) ((beta : ℝ) : ℂ))
    (hplatePeriod : ∀ P : Continuous.VerticalPlate K (T.centres : Set Tiling.Plane),
      ¬ Continuous.IsVerticalColumn P →
        Tiling.RationalPolygonal.SetPeriodicBy P.support ((beta : ℝ) : ℂ))
    (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
    (haligned : ∀ n, ∃ m : ℤ, (g n : Tiling.Plane).re = (m : ℝ) * beta)
    (hconverges : LocallyFellConverges
      (TilingSpace.centresSequence (TilingSpace.translateSequence g T))
      (S.centres : Set Tiling.Plane)) :
    ∃ (φ : ℕ → ℕ) (V : ∀ i : Option
        ↑(Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)),
        TilingSpace K (match i with
          | none => regularSupport K (Continuous.verticalColumnCentres K
              (T.centres : Set Tiling.Plane))
          | some P => P.1.support)),
      StrictMono φ ∧
      LocallyFellConverges
        (TilingSpace.centresSequence
          (TilingSpace.translateSequence (fun n => g (φ n)) T))
        (S.centres : Set Tiling.Plane) ∧
      (∀ i, LocallyFellConverges
        (fun n => ((g (φ n) : Tiling.Plane) +ᵥ
          (match i with
            | none => Continuous.verticalColumnCentres K
                (T.centres : Set Tiling.Plane)
            | some P => P.1.centres)))
        (V i).centres) ∧
      (∀ i, regularSupport K (V i).centres =
        (match i with
          | none => regularSupport K (Continuous.verticalColumnCentres K
              (T.centres : Set Tiling.Plane))
          | some P => P.1.support)) ∧
      (∀ P : ↑(Continuous.nonColumnVerticalPlates K
          (T.centres : Set Tiling.Plane)),
        ((V (some P)).centres : Set Tiling.Plane).Nonempty) := by
  have hsource : (Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane)).Finite :=
    (noncolumnVerticalPlates_finite T.tilesOn).1
  letI : Fintype (↑(Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane))) := hsource.fintype
  let I := Option (↑(Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane)))
  let E : I → Set Tiling.Plane := fun i => match i with
    | none => regularSupport K (Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane))
    | some P => P.1.support
  let C : ℕ → I → Set Tiling.Plane := fun n i => match i with
    | none => (g n : Tiling.Plane) +ᵥ Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane)
    | some P => (g n : Tiling.Plane) +ᵥ P.1.centres
  have hTiles : ∀ (n : ℕ) (i : I), TilesOn K (C n i) (E i) := by
    intro n i
    obtain ⟨m, hm⟩ := haligned n
    have hu : (g n : Tiling.Plane) =
        (((m : ℝ) * beta : ℝ) : ℂ) + ((g n : Tiling.Plane).im : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [hm]
      · simp
    cases i with
    | none =>
        exact tilesOn_shifted_columnColour T.tilesOn hcolumnPeriod hu
    | some P =>
        exact tilesOn_shifted_nonColumnColour T.tilesOn P.1
          (hplatePeriod P.1 P.2) hu
  let U : ℕ → ∀ i : I, TilingSpace K (E i) := fun n i =>
    { centres := ⟨C n i, tilesOn_centres_closed (hTiles n i)⟩
      tilesOn := hTiles n i }
  obtain ⟨φ, V, hφ, hprod⟩ := finiteColour_common_subsequence inferInstance E U
  have hTend : Tendsto (fun n => TilingSpace.translate (g n) T)
      atTop (nhds S) :=
    ((locallyFell_metrizable K Set.univ).2
      (TilingSpace.translateSequence g T) S).2 hconverges
  have hTendφ := hTend.comp hφ.tendsto_atTop
  have hamb := ((locallyFell_metrizable K Set.univ).2
      (fun n => TilingSpace.translate (g (φ n)) T) S).1 hTendφ
  refine ⟨φ, V, hφ, hamb, ?_, ?_, ?_⟩
  · intro i
    have hcoord : Tendsto ((U ∘ φ) · i) atTop (nhds (V i)) := by
      exact (continuous_apply i).continuousAt.tendsto.comp hprod
    have hfell := ((locallyFell_metrizable K (E i)).2
        (fun n => (U (φ n)) i) (V i)).mp hcoord
    change LocallyFellConverges (fun n => C (φ n) i) (V i).centres at hfell
    cases i <;> exact hfell
  · intro i
    cases i with
    | none =>
        exact regularSupport_eq_of_tilesOn
          (regularSupport_isRegularOpen K
            (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane))).1
          (regularSupport_isRegularOpen K
            (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane))).2
          (V none).tilesOn
    | some P =>
        exact regularSupport_eq_of_tilesOn
          (regularSupport_isRegularOpen K P.1.centres).1
          (regularSupport_isRegularOpen K P.1.centres).2
          (V (some P)).tilesOn
  · intro P
    exact tilesOn_centres_nonempty_of_nonempty_carrier
      ((V (some P)).tilesOn)
      (verticalPlate_support_nonempty P.1)
      (regularSupport_isRegularOpen K P.1.centres).1
      (regularSupport_isRegularOpen K P.1.centres).2
set_option linter.style.haveILetI false in
private theorem exists_finitePlateColourLimitData :
    ∀ {K : Region} (T S : TilingSpace K Set.univ) {beta : ℝ},
      0 < beta →
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (Continuous.verticalColumnCentres K
          (T.centres : Set Tiling.Plane))) ((beta : ℝ) : ℂ) →
      (∀ P : Continuous.VerticalPlate K (T.centres : Set Tiling.Plane),
        ¬ Continuous.IsVerticalColumn P →
          Tiling.RationalPolygonal.SetPeriodicBy P.support ((beta : ℝ) : ℂ)) →
      ∀ (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)),
      (∀ n, ∃ m : ℤ, (g n : Tiling.Plane).re = (m : ℝ) * beta) →
      LocallyFellConverges
        (TilingSpace.centresSequence (TilingSpace.translateSequence g T))
        (S.centres : Set Tiling.Plane) →
      Nonempty (FinitePlateColourLimitData T S g) := by
  intro K T S beta _hbeta hcolumnPeriod hplatePeriod g haligned hconverges
  obtain ⟨φ, V, hφ, hamb, hcolour, hsupport, hnonempty⟩ :=
    finiteColour_spaceSequence T S hcolumnPeriod hplatePeriod g haligned hconverges
  have hsource : (Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane)).Finite :=
    (noncolumnVerticalPlates_finite T.tilesOn).1
  have htarget : (Continuous.nonColumnVerticalPlates K
      (S.centres : Set Tiling.Plane)).Finite :=
    (noncolumnVerticalPlates_finite S.tilesOn).1
  letI : Fintype (↑(Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane))) := hsource.fintype
  let I := Option (↑(Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane)))
  let C : ℕ → I → Set Tiling.Plane := fun n i => match i with
    | none => (g n : Tiling.Plane) +ᵥ Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane)
    | some P => (g n : Tiling.Plane) +ᵥ P.1.centres
  have hsourcePartition :
      Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane) ∪
          (⋃ P : ↑(Continuous.nonColumnVerticalPlates K
            (T.centres : Set Tiling.Plane)), P.1.centres) =
        (T.centres : Set Tiling.Plane) := verticalColumn_nonColumn_partition
  have hpart : ∀ n, (⋃ i : I, C n i) =
      (g n : Tiling.Plane) +ᵥ (T.centres : Set Tiling.Plane) := by
    intro n
    calc
      (⋃ i : I, C n i) =
          (g n : Tiling.Plane) +ᵥ
            (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane) ∪
              (⋃ P : ↑(Continuous.nonColumnVerticalPlates K
                (T.centres : Set Tiling.Plane)), P.1.centres)) := by
        ext x
        constructor
        · intro hx
          simp only [Set.mem_iUnion] at hx
          rcases hx with ⟨i, hxi⟩
          cases i with
          | none =>
              rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxi ⊢
              exact Set.mem_union_left _ hxi
          | some P =>
              rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxi ⊢
              exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨P, hxi⟩)
        · intro hx
          rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
          rcases hx with hx | hx
          · refine Set.mem_iUnion.2 ⟨none, ?_⟩
            rw [Set.mem_vadd_set_iff_neg_vadd_mem]
            exact hx
          · rcases Set.mem_iUnion.mp hx with ⟨P, hxP⟩
            refine Set.mem_iUnion.2 ⟨some P, ?_⟩
            rw [Set.mem_vadd_set_iff_neg_vadd_mem]
            exact hxP
      _ = (g n : Tiling.Plane) +ᵥ (T.centres : Set Tiling.Plane) := by
        rw [hsourcePartition]
  have htranslate (n : ℕ) :
      (TilingSpace.translate (g n) T).centres =
        (g n : Tiling.Plane) +ᵥ (T.centres : Set Tiling.Plane) := by
    ext x
    constructor <;> intro hx
    · rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp [vadd_eq_add, add_comm]⟩
    · rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp [vadd_eq_add, add_comm]⟩
  have hpart' : ∀ n, (⋃ i : I, C n i) =
      (TilingSpace.translate (g n) T).centres := by
    intro n
    rw [hpart n, htranslate n]
  have hcolourI : ∀ i : I, LocallyFellConverges
      (fun n => C (φ n) i) (V i).centres := by
    intro i
    cases i with
    | none => exact hcolour none
    | some P => exact hcolour (some P)
  have hunion := finiteColour_union_of_partition
    (I := I) (A := fun n i => C (φ n) i)
    (B := fun n => (TilingSpace.translate (g (φ n)) T).centres)
    (L := fun i => (V i).centres) (M := (S.centres : Set Tiling.Plane))
    (fun n => hpart' (φ n)) hcolourI hamb
  have hunion' := hunion
  dsimp [I] at hunion'
  rw [Set.iUnion_option] at hunion'
  obtain ⟨delta, hdelta, hseparation⟩ :=
    Tiling.AxisParallel.exists_packingSeparation K
  have hsep : ∀ n i j, i ≠ j → ∀ x ∈ C (φ n) i, ∀ y ∈ C (φ n) j,
      delta ≤ dist x y := by
    intro n i j hij x hxi y hyj
    have hxiSource : x ∈ (g (φ n) : Tiling.Plane) +ᵥ (match i with
        | none => Continuous.verticalColumnCentres K
            (T.centres : Set Tiling.Plane)
        | some P => P.1.centres) := by
      cases i with
      | none => simpa only [C] using hxi
      | some P => simpa only [C] using hxi
    have hyjSource : y ∈ (g (φ n) : Tiling.Plane) +ᵥ (match j with
        | none => Continuous.verticalColumnCentres K
            (T.centres : Set Tiling.Plane)
        | some P => P.1.centres) := by
      cases j with
      | none => simpa only [C] using hyj
      | some P => simpa only [C] using hyj
    rcases hxiSource with ⟨x₀, hx₀, rfl⟩
    rcases hyjSource with ⟨y₀, hy₀, rfl⟩
    have hsourceDisj := sourceColour_pairwiseDisjoint
      (K := K) (T := (T.centres : Set Tiling.Plane))
      hsource
    have hcolsub :
        Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane) ⊆
          (T.centres : Set Tiling.Plane) := by
      intro z hz
      rw [← verticalColumn_nonColumn_partition (K := K)
        (T := (T.centres : Set Tiling.Plane))]
      exact Set.mem_union_left _ hz
    have hplatesub (P : ↑(Continuous.nonColumnVerticalPlates K
        (T.centres : Set Tiling.Plane))) :
        P.1.centres ⊆ (T.centres : Set Tiling.Plane) := by
      rintro z ⟨q, hq, rfl⟩
      exact q.2
    have hne₀ : x₀ ≠ y₀ := by
      intro hxy
      cases i with
      | none =>
          cases j with
          | none => exact hij rfl
          | some Q =>
              have hd := hsourceDisj (Set.mem_univ _) (Set.mem_univ _)
                (show (none : Option ↑(Continuous.nonColumnVerticalPlates K
                  (T.centres : Set Tiling.Plane))) ≠ some Q from hij)
              exact (Set.disjoint_left.mp hd hx₀) (hxy ▸ hy₀)
      | some P =>
          cases j with
          | none =>
              have hd := hsourceDisj (Set.mem_univ _) (Set.mem_univ _)
                (show (some P : Option ↑(Continuous.nonColumnVerticalPlates K
                  (T.centres : Set Tiling.Plane))) ≠ none from hij)
              exact (Set.disjoint_left.mp hd hx₀) (hxy ▸ hy₀)
          | some Q =>
              have hd := hsourceDisj (Set.mem_univ _) (Set.mem_univ _)
                (show (some P : Option ↑(Continuous.nonColumnVerticalPlates K
                  (T.centres : Set Tiling.Plane))) ≠ some Q from hij)
              exact (Set.disjoint_left.mp hd hx₀) (hxy ▸ hy₀)
    have hx₀' : x₀ ∈ (T.centres : Set Tiling.Plane) := by
      cases i with
      | none => exact hcolsub hx₀
      | some P => exact hplatesub P hx₀
    have hy₀' : y₀ ∈ (T.centres : Set Tiling.Plane) := by
      cases j with
      | none => exact hcolsub hy₀
      | some P => exact hplatesub P hy₀
    simpa only [dist_vadd_cancel_left] using
      hseparation (T.centres : Set Tiling.Plane) T.tilesOn.2.1
        x₀ hx₀' y₀ hy₀' hne₀
  have hpairAll : Set.PairwiseDisjoint Set.univ
      (fun i : I => ((V i).centres : Set Tiling.Plane)) := by
    apply finiteColour_pairwiseDisjoint_of_separation
      (I := I) (A := fun n i => C (φ n) i)
      (L := fun i => ((V i).centres : Set Tiling.Plane)) hdelta hsep
    exact hcolourI
  have hpairNon : Set.PairwiseDisjoint Set.univ
      (fun P : ↑(Continuous.nonColumnVerticalPlates K
        (T.centres : Set Tiling.Plane)) =>
        ((V (some P)).centres : Set Tiling.Plane)) := by
    intro P _ Q _ hPQ
    have hsome : (some P : I) ≠ some Q := by
      simpa using hPQ
    exact hpairAll (Set.mem_univ _) (Set.mem_univ _) hsome
  have hcolNon : ∀ P : ↑(Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane)),
      Disjoint ((V none).centres : Set Tiling.Plane)
        ((V (some P)).centres : Set Tiling.Plane) := by
    intro P
    have hnone : (none : I) ≠ some P := by simp
    exact hpairAll (Set.mem_univ _) (Set.mem_univ _) hnone
  refine ⟨{
    subsequence := φ
    subsequence_strictMono := hφ
    ambient_converges := hamb
    sourceNonColumn_finite := hsource
    targetNonColumn_finite := htarget
    columnLimit := (V none).centres
    nonColumnLimit := fun P => (V (some P)).centres
    column_converges := by simpa using hcolour none
    nonColumn_converges := by
      intro P
      simpa using hcolour (some P)
    nonColumnLimit_nonempty := hnonempty
    coloured_union := hunion'
    coloured_pairwiseDisjoint := hpairNon
    column_disjoint_nonColumn := hcolNon
    columnSupport_eq := by simpa using hsupport none
    nonColumnSupport_eq := by
      intro P
      simpa using hsupport (some P)
  }⟩
private theorem regularSupport_plate_inter_colour
    {K : Region} {T S : Topology.TilingSpace K Set.univ}
    {g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    (D : FinitePlateColourLimitData T S g)
    (P : ↑(Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)))
    (Q : Continuous.VerticalPlate K (S.centres : Set Tiling.Plane)) :
    regularSupport K (Q.centres ∩ D.nonColumnLimit P) =
      Q.support ∩ regularSupport K (D.nonColumnLimit P) := by
  let A : Set Tiling.Plane := Q.centres ∩ D.nonColumnLimit P
  have hAS : A ⊆ (S.centres : Set Tiling.Plane) := by
    intro x hx
    exact verticalPlate_centres_subset Q hx.1
  have hQpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements Q.centres) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K Q.centres).mpr
    intro s hs t ht hst
    have hpack := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
      K (S.centres : Set Tiling.Plane)).mp S.tilesOn.2.1
    exact hpack (verticalPlate_centres_subset Q hs) (verticalPlate_centres_subset Q ht) hst
  have hUpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (D.nonColumnLimit P)) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K (D.nonColumnLimit P)).mpr
    intro s hs t ht hst
    have hpack := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
      K (S.centres : Set Tiling.Plane)).mp S.tilesOn.2.1
    exact hpack (by
        rw [← D.coloured_union]
        exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨P, hs⟩))
      (by
        rw [← D.coloured_union]
        exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨P, ht⟩)) hst
  have hAPack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K A).mpr
    intro s hs t ht hst
    have hpack := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
      K (S.centres : Set Tiling.Plane)).mp S.tilesOn.2.1
    exact hpack (hAS hs) (hAS ht) hst
  have hraw : openUnion K A = openUnion K Q.centres ∩
      openUnion K (D.nonColumnLimit P) := by
    ext x
    constructor
    · rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      rintro ⟨s, hs⟩
      refine ⟨?_, ?_⟩
      · rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        exact ⟨⟨s.1, s.2.1⟩, hs⟩
      · rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        exact ⟨⟨s.1, s.2.2⟩, hs⟩
    · intro hx
      change x ∈ openUnion K Q.centres ∩ openUnion K (D.nonColumnLimit P) at hx
      rcases hx with ⟨hxQ, hxU⟩
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hxQ hxU
      obtain ⟨s, hs⟩ := hxQ
      obtain ⟨t, ht⟩ := hxU
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at ⊢
      have hst : (s : Tiling.Plane) = t := by
        by_contra hne
        exact Set.disjoint_left.1
          ((Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
            K (S.centres : Set Tiling.Plane)).mp S.tilesOn.2.1
            (verticalPlate_centres_subset Q s.2) (by
              rw [← D.coloured_union]
              exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨P, t.2⟩)) hne) hs ht
      exact ⟨⟨s, ⟨s.2, hst ▸ t.2⟩⟩, hs⟩
  have hAE : openUnion K A =ᵐ[MeasureTheory.volume]
      (Set.inter Q.support (regularSupport K (D.nonColumnLimit P))) := by
    filter_upwards [Tiling.AxisParallel.openUnion_aeEq_regularSupport hQpack,
      Tiling.AxisParallel.openUnion_aeEq_regularSupport hUpack] with x hxQ hxU
    change (x ∈ openUnion K A) =
      (x ∈ Set.inter Q.support (regularSupport K (D.nonColumnLimit P)))
    rw [hraw]
    apply propext
    exact ⟨fun hx => ⟨hxQ.mp hx.1, hxU.mp hx.2⟩,
      fun hx => ⟨hxQ.mpr hx.1, hxU.mpr hx.2⟩⟩
  let R := Set.inter Q.support (regularSupport K (D.nonColumnLimit P))
  have hRopen : IsOpen R :=
    (regularSupport_isRegularOpen K Q.centres).1.inter
      (regularSupport_isRegularOpen K (D.nonColumnLimit P)).1
  have hRregular : interior (closure R) = R := by
    apply Set.Subset.antisymm
    · intro x hx
      dsimp [R] at hx ⊢
      refine ⟨?_, ?_⟩
      · have hQsupport : Q.support = regularSupport K Q.centres := rfl
        rw [hQsupport] at hx ⊢
        exact (regularSupport_isRegularOpen K Q.centres).2 ▸
          interior_mono (closure_mono inter_subset_left) hx
      · exact (regularSupport_isRegularOpen K (D.nonColumnLimit P)).2 ▸
          interior_mono (closure_mono inter_subset_right) hx
    · exact interior_maximal subset_closure hRopen
  exact Tiling.AxisParallel.regularOpen_eq_of_aeEq
    (regularSupport_isRegularOpen K A).1 (regularSupport_isRegularOpen K A).2
    hRopen hRregular
    ((Tiling.AxisParallel.openUnion_aeEq_regularSupport hAPack).symm.trans hAE)

private theorem targetPlate_subset_colour_of_mem
    {K : Region} {T S : Topology.TilingSpace K Set.univ}
    {g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    (D : FinitePlateColourLimitData T S g)
    (P : ↑(Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)))
    (Q : ↑(Continuous.nonColumnVerticalPlates K (S.centres : Set Tiling.Plane)))
    (hmeet : (Q.1.centres ∩ D.nonColumnLimit P).Nonempty) :
    Q.1.centres ⊆ D.nonColumnLimit P := by
  obtain ⟨hXreg, hXsupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab S.tilesOn Q.1
  have hinter : regularSupport K (Q.1.centres ∩ D.nonColumnLimit P) =
      Q.1.support ∩ regularSupport K (D.nonColumnLimit P) :=
    regularSupport_plate_inter_colour D P Q.1
  have hslab : ∃ X : Set ℝ,
      X = interior (closure X) ∧
        regularSupport K (Q.1.centres ∩ D.nonColumnLimit P) = Complex.re ⁻¹' X := by
    obtain ⟨hPreg, hPsupport⟩ :=
      Continuous.VerticalPlate.support_isVerticalSlab T.tilesOn P.1
    have hcolourSupport : regularSupport K (D.nonColumnLimit P) =
        Complex.re ⁻¹' P.1.base := by
      rw [D.nonColumnSupport_eq P, hPsupport]
    have hXreg' : interior (closure Q.1.base) = Q.1.base := hXreg.symm
    have hPreg' : interior (closure P.1.base) = P.1.base := hPreg.symm
    refine ⟨Q.1.base ∩ P.1.base, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · apply interior_maximal subset_closure
        rw [← hXreg', ← hPreg']
        exact isOpen_interior.inter isOpen_interior
      · intro x hx
        refine ⟨?_, ?_⟩
        · have hx' : x ∈ interior (closure Q.1.base) :=
            interior_mono (closure_mono inter_subset_left) hx
          rw [hXreg'] at hx'
          exact hx'
        · have hx' : x ∈ interior (closure P.1.base) :=
            interior_mono (closure_mono inter_subset_right) hx
          rw [hPreg'] at hx'
          exact hx'
    · rw [hinter, hXsupport, hcolourSupport, ← Set.preimage_inter]
  have hsat := (Continuous.VerticalPlate.minimal S.tilesOn Q.1).2.2.2
    (Q.1.centres ∩ D.nonColumnLimit P) hmeet inter_subset_left hslab
  intro x hx
  have hxin : x ∈ Q.1.centres ∩ D.nonColumnLimit P := hsat.symm ▸ hx
  exact hxin.2

private theorem targetPlateBlocks_partition
    {K : Region} {T S : Topology.TilingSpace K Set.univ}
    {g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    (D : FinitePlateColourLimitData T S g)
    (hcolumn : D.columnLimit =
      Continuous.verticalColumnCentres K (S.centres : Set Tiling.Plane)) :
    (∀ Q : ↑(Continuous.nonColumnVerticalPlates K (S.centres : Set Tiling.Plane)),
        ∃! P, Q ∈ targetPlateBlock D P) ∧
      ∀ P, (targetPlateBlock D P).Nonempty := by
  have hcolour_subset (P : ↑(Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane))) :
      D.nonColumnLimit P ⊆ (S.centres : Set Tiling.Plane) := by
    intro x hx
    rw [← D.coloured_union]
    exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨P, hx⟩)
  have hcolumn_not_mem (Q : ↑(Continuous.nonColumnVerticalPlates K
      (S.centres : Set Tiling.Plane))) {x : Tiling.Plane}
      (hx : x ∈ Q.1.centres) : x ∉ D.columnLimit := by
    intro hxcol
    rw [hcolumn] at hxcol
    rw [Continuous.verticalColumnCentres_eq] at hxcol
    obtain ⟨R, hxR⟩ := Set.mem_iUnion.mp hxcol
    have hQR : Q.1 = R.1 := verticalPlate_eq_of_common_centre hx hxR
    exact Q.2 (hQR ▸ R.2)
  constructor
  · intro Q
    obtain ⟨x, hxQ⟩ := verticalPlate_centres_nonempty Q.1
    have hxS : x ∈ (S.centres : Set Tiling.Plane) :=
      verticalPlate_centres_subset Q.1 hxQ
    rw [← D.coloured_union] at hxS
    rcases hxS with hxcol | hxcol
    · exact False.elim ((hcolumn_not_mem Q hxQ) hxcol)
    · obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hxcol
      have hsubset := targetPlate_subset_colour_of_mem D P Q ⟨x, hxQ, hxP⟩
      refine ⟨P, hsubset, ?_⟩
      intro R hR
      by_contra hPR
      have hne : P ≠ R := fun h => hPR h.symm
      have hdisj := D.coloured_pairwiseDisjoint
        (Set.mem_univ P) (Set.mem_univ R) hne
      exact Set.disjoint_left.1 hdisj hxP (hR hxQ)
  · intro P
    obtain ⟨x, hxP⟩ := D.nonColumnLimit_nonempty P
    have hxS : x ∈ (S.centres : Set Tiling.Plane) := hcolour_subset P hxP
    have hxnotcol : x ∉ Continuous.verticalColumnCentres K
        (S.centres : Set Tiling.Plane) := by
      intro hxcol
      apply Set.disjoint_left.1 (D.column_disjoint_nonColumn P)
        (hcolumn ▸ hxcol) hxP
    let t : (S.centres : Set Tiling.Plane) := ⟨x, hxS⟩
    let Q₀ : Continuous.VerticalPlate K (S.centres : Set Tiling.Plane) :=
      Continuous.VerticalPlate.ofCentre t
    have hxQ₀ : x ∈ Q₀.centres := by
      exact Continuous.VerticalPlate.mem_centres_ofCentre t
    have hQ₀ : ¬ Continuous.IsVerticalColumn Q₀ := by
      intro hQcol
      apply hxnotcol
      rw [Continuous.verticalColumnCentres_eq, Set.mem_iUnion]
      exact ⟨⟨Q₀, hQcol⟩, hxQ₀⟩
    let Q : ↑(Continuous.nonColumnVerticalPlates K
        (S.centres : Set Tiling.Plane)) := ⟨Q₀, hQ₀⟩
    refine ⟨Q, ?_⟩
    exact targetPlate_subset_colour_of_mem D P Q ⟨x, hxQ₀, hxP⟩

private theorem source_card_le_target_of_blocks
    {K : Region} {T S : Topology.TilingSpace K Set.univ}
    {g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    (D : FinitePlateColourLimitData T S g)
    (hpartition :
      ∀ Q : ↑(Continuous.nonColumnVerticalPlates K (S.centres : Set Tiling.Plane)),
        ∃! P, Q ∈ targetPlateBlock D P)
    (hnonempty :
      ∀ P, (targetPlateBlock D P).Nonempty) :
    Set.ncard (Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)) ≤
      Set.ncard (Continuous.nonColumnVerticalPlates K (S.centres : Set Tiling.Plane)) := by
  let source := Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)
  let target := Continuous.nonColumnVerticalPlates K (S.centres : Set Tiling.Plane)
  let _ : Fintype source := D.sourceNonColumn_finite.fintype
  let _ : Fintype target := D.targetNonColumn_finite.fintype
  let f : target → source := fun Q => Classical.choose (hpartition Q)
  have hf : Function.Surjective f := by
    intro P
    obtain ⟨Q, hQ⟩ := hnonempty P
    have hEq : f Q = P :=
      ((Classical.choose_spec (hpartition Q)).2 P hQ).symm
    exact ⟨Q, hEq⟩
  have hcard : Fintype.card source ≤ Fintype.card target :=
    Fintype.card_le_of_surjective f hf
  simpa [source, target, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] using hcard

private theorem exists_plateEquiv_of_singletonBlocks
    {K : Region} {T S : Topology.TilingSpace K Set.univ}
    {g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    (D : FinitePlateColourLimitData T S g)
    (hcolumn : D.columnLimit =
      Continuous.verticalColumnCentres K (S.centres : Set Tiling.Plane))
    (hcard :
      Set.ncard (Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)) =
        Set.ncard (Continuous.nonColumnVerticalPlates K (S.centres : Set Tiling.Plane))) :
    ∃ e : ↑(Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)) ≃
        ↑(Continuous.nonColumnVerticalPlates K (S.centres : Set Tiling.Plane)),
      ∀ P, D.nonColumnLimit P = (e P).1.centres := by
  obtain ⟨hpartition, hnonempty⟩ := targetPlateBlocks_partition D hcolumn
  let source := Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)
  let target := Continuous.nonColumnVerticalPlates K (S.centres : Set Tiling.Plane)
  let _ : Fintype source := D.sourceNonColumn_finite.fintype
  let _ : Fintype target := D.targetNonColumn_finite.fintype
  let f : source → target := fun P => Classical.choose (hnonempty P)
  have hf_inj : Function.Injective f := by
    intro P R hPR
    have hP : f P ∈ targetPlateBlock D P :=
      (Classical.choose_spec (hnonempty P))
    have hR : f R ∈ targetPlateBlock D R :=
      (Classical.choose_spec (hnonempty R))
    have hunique := (hpartition (f P)).choose_spec.2
    have hRP0 : R = (hpartition (f P)).choose :=
      hunique R (hPR ▸ hR)
    have hchoose : (hpartition (f P)).choose = P :=
      ((hpartition (f P)).choose_spec.2 P hP).symm
    exact hRP0.trans hchoose |>.symm
  have hcard' : Fintype.card source = Fintype.card target := by
    simpa [source, target, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using hcard
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard'⟩
  have hblock_singleton (P : source) {Q : target}
      (hQ : Q ∈ targetPlateBlock D P) : Q = f P := by
    obtain ⟨R, hR⟩ := hf_bij.2 Q
    have hRblock : f R ∈ targetPlateBlock D R :=
      Classical.choose_spec (hnonempty R)
    have hRP0 : R = (hpartition Q).choose :=
      (hpartition Q).choose_spec.2 R (hR ▸ hRblock)
    have hchoose : (hpartition Q).choose = P :=
      ((hpartition Q).choose_spec.2 P hQ).symm
    have hRP : R = P := hRP0.trans hchoose
    exact hR.symm.trans (congrArg f hRP)
  refine ⟨Equiv.ofBijective f hf_bij, ?_⟩
  intro P
  have hchosen : f P ∈ targetPlateBlock D P :=
    Classical.choose_spec (hnonempty P)
  apply Set.Subset.antisymm
  · intro x hx
    have hxS : x ∈ (S.centres : Set Tiling.Plane) := by
      rw [← D.coloured_union]
      exact Set.mem_union_right _ (Set.mem_iUnion.2 ⟨P, hx⟩)
    have hnot : x ∉ D.columnLimit := by
      intro hxc
      exact Set.disjoint_left.1 (D.column_disjoint_nonColumn P) hxc hx
    have hxnotcol : x ∉ Continuous.verticalColumnCentres K
        (S.centres : Set Tiling.Plane) := by
      intro hxc
      exact hnot (hcolumn ▸ hxc)
    let t : (S.centres : Set Tiling.Plane) := ⟨x, hxS⟩
    let Q₀ : Continuous.VerticalPlate K (S.centres : Set Tiling.Plane) :=
      Continuous.VerticalPlate.ofCentre t
    have hxQ₀ : x ∈ Q₀.centres :=
      Continuous.VerticalPlate.mem_centres_ofCentre t
    have hQ₀ : ¬ Continuous.IsVerticalColumn Q₀ := by
      intro hQcol
      apply hxnotcol
      rw [Continuous.verticalColumnCentres_eq, Set.mem_iUnion]
      exact ⟨⟨Q₀, hQcol⟩, hxQ₀⟩
    let Q' : target := ⟨Q₀, hQ₀⟩
    have hQtarget : Q₀.centres ⊆ D.nonColumnLimit P :=
      targetPlate_subset_colour_of_mem D P Q' ⟨x, hxQ₀, hx⟩
    have hQ' : Q' = f P := hblock_singleton P hQtarget
    have hQx : x ∈ (f P).1.centres := hQ' ▸ hxQ₀
    exact hQx
  · intro x hx
    exact hchosen hx

private theorem regularSupport_mono_local
    {K : Region} {A B : Set Tiling.Plane} (hAB : A ⊆ B) :
    regularSupport K A ⊆ regularSupport K B := by
  unfold regularSupport Tiling.Polygonal.regularSupport
  exact interior_mono (closure_mono (by
    intro x hx
    rw [Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs⟩ := hx
    exact ⟨⟨s.1, hAB s.2⟩, hs⟩))

private theorem verticalColumnCentres_vadd
    {K : Region} {T : Set Tiling.Plane} (u : Tiling.Plane) :
    Continuous.verticalColumnCentres K (u +ᵥ T) =
      u +ᵥ Continuous.verticalColumnCentres K T := by
  have hcarrier : K.openCarrier =
      positiveSimilarity 1 0 '' K.openCarrier := by
    ext z
    constructor
    · intro hz
      exact ⟨z, hz, by simp [positiveSimilarity]⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [positiveSimilarity] using hz
  have hsim (c : Tiling.Plane) (S : Set Tiling.Plane) :
      positiveSimilarity 1 c '' S = c +ᵥ S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Set.mem_vadd_set.mpr ⟨w, hw, by
        simp [positiveSimilarity, vadd_eq_add, add_comm]⟩
    · intro hz
      rcases Set.mem_vadd_set.mp hz with ⟨w, hw, hwz⟩
      refine ⟨w, hw, ?_⟩
      simpa [positiveSimilarity, vadd_eq_add, add_comm] using hwz
  rw [← hsim u T]
  rw [Continuous.verticalColumnCentres_positiveSimilarity_image
    (by norm_num) hcarrier u]
  exact hsim u _


private theorem locallyFell_strictMono_anchor
    {A : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hconv : LocallyFellConverges A L) {x : Tiling.Plane} (hx : x ∈ L) :
    ∃ (φ : ℕ → ℕ) (z : ℕ → Tiling.Plane),
      StrictMono φ ∧ (∀ n, z n ∈ A (φ n)) ∧
        Tendsto z atTop (nhds x) := by
  have hhit (n : ℕ) :
      ∀ᶠ k : ℕ in atTop, ∃ y ∈ A k, dist y x < 1 / ((n : ℝ) + 1) :=
    Tiling.AxisParallel.Topology.locallyFellConverges_eventually_exists_mem_ball
      hconv hx (by positivity)
  choose N hN using fun n => (eventually_atTop.1 (hhit n))
  let φ : ℕ → ℕ := fun n =>
    Nat.rec (N 0) (fun k p => max (p + 1) (N (k + 1))) n
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp [φ]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hφN : ∀ n, N n ≤ φ n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        dsimp [φ]
        exact le_max_right _ _
  let z : ℕ → Tiling.Plane := fun n =>
    Classical.choose (hN n (φ n) (hφN n))
  have hz : ∀ n, z n ∈ A (φ n) ∧
      dist (z n) x < 1 / ((n : ℝ) + 1) := by
    intro n
    exact Classical.choose_spec (hN n (φ n) (hφN n))
  refine ⟨φ, z, hφ, fun n => (hz n).1, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  have hsmall : 1 / ((M : ℝ) + 1) < ε := by
    have hM' : 2 / ε < (M : ℝ) + 1 := by
      exact lt_of_lt_of_le hM (by linarith)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) + 1)]
    have hM'' : 2 < ε * ((M : ℝ) + 1) := by
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hM'
    linarith
  refine ⟨M, ?_⟩
  intro n hn
  have hmn : (M : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast (Nat.add_le_add_right hn 1)
  have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
    exact one_div_le_one_div_of_le (by positivity) hmn
  exact (hz n).2.trans_le (hfrac.trans hsmall.le)

private theorem castVerticalPlate_isVerticalColumn
    {K : Region} {A B : Set Tiling.Plane} (h : A = B)
    (P : Continuous.VerticalPlate K A)
    (hP : Continuous.IsVerticalColumn P) :
    Continuous.IsVerticalColumn (h ▸ P) := by
  cases h
  exact hP

private theorem castVerticalPlate_mem_centres
    {K : Region} {A B : Set Tiling.Plane} (h : A = B)
    (P : Continuous.VerticalPlate K A) {x : Tiling.Plane}
    (hx : x ∈ P.centres) :
    x ∈ (h ▸ P).centres := by
  cases h
  exact hx

private theorem columnLimit_subset_targetVerticalColumnCentres
    {K : Region} {T S : TilingSpace K Set.univ}
    {g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    (D : FinitePlateColourLimitData T S g) :
    D.columnLimit ⊆
      Continuous.verticalColumnCentres K (S.centres : Set Tiling.Plane) := by
  intro x hx
  let V : Set Tiling.Plane :=
    Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane)
  let u : ℕ → Tiling.Plane :=
    fun n => (g (D.subsequence n) : Tiling.Plane)
  have hcarrier : K.openCarrier =
      positiveSimilarity 1 0 '' K.openCarrier := by
    ext z
    constructor
    · intro hz
      exact ⟨z, hz, by simp [positiveSimilarity]⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [positiveSimilarity] using hz
  have hsim (c : Tiling.Plane) (A : Set Tiling.Plane) :
      positiveSimilarity 1 c '' A = c +ᵥ A := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Set.mem_vadd_set.mpr ⟨w, hw, by
        simp [positiveSimilarity, vadd_eq_add, add_comm]⟩
    · intro hz
      rcases Set.mem_vadd_set.mp hz with ⟨w, hw, hwz⟩
      refine ⟨w, hw, ?_⟩
      simpa [positiveSimilarity, vadd_eq_add, add_comm] using hwz
  obtain ⟨φ, z, hφ, hz, hzlim⟩ :=
    locallyFell_strictMono_anchor
      (A := fun n => u n +ᵥ V) D.column_converges hx
  have hamb :
      LocallyFellConverges
        (TilingSpace.centresSequence
          (fun n => TilingSpace.translate (g (D.subsequence (φ n))) T))
        (S.centres : Set Tiling.Plane) := by
    have hTend : Tendsto
        (fun n => TilingSpace.translate (g (D.subsequence n)) T)
        atTop (nhds S) :=
      ((locallyFell_metrizable K Set.univ).2
        (TilingSpace.translateSequence (fun n => g (D.subsequence n)) T) S).2
        D.ambient_converges
    exact ((locallyFell_metrizable K Set.univ).2
      (fun n => TilingSpace.translate (g (D.subsequence (φ n))) T) S).1
      (hTend.comp hφ.tendsto_atTop)
  let p : ℕ → Tiling.Plane := fun n =>
    Classical.choose (Set.mem_vadd_set.mp (hz n))
  have hp (n : ℕ) : p n ∈ V :=
    (Classical.choose_spec (Set.mem_vadd_set.mp (hz n))).1
  have hzp (n : ℕ) :
      z n = u (φ n) +ᵥ p n := by
    exact (Classical.choose_spec (Set.mem_vadd_set.mp (hz n))).2.symm
  let Pidx : ∀ n, {P : Continuous.VerticalPlate K
      (T.centres : Set Tiling.Plane) //
      Continuous.IsVerticalColumn P} := fun n =>
    Classical.choose (Set.mem_iUnion.mp (hp n))
  have hPmem (n : ℕ) : p n ∈ (Pidx n).1.centres := by
    exact Classical.choose_spec (Set.mem_iUnion.mp (hp n))
  let e (n : ℕ) :=
    verticalPlate_positiveSimilarityEquiv
      (K := K) (R := K) (T := (T.centres : Set Tiling.Plane))
      (s := 1) (r := 0) (by norm_num) hcarrier (u (φ n))
  have hecent (n : ℕ) :
      (e n (Pidx n).1).centres =
        positiveSimilarity 1 (u (φ n)) '' (Pidx n).1.centres := by
    dsimp [e]
    exact verticalPlate_positiveSimilarityEquiv_centres_image
      (by norm_num) hcarrier (u (φ n)) (Pidx n).1
  have hecol (n : ℕ) : Continuous.IsVerticalColumn (e n (Pidx n).1) := by
    dsimp [e]
    exact (verticalPlate_positiveSimilarityEquiv_isVerticalColumn
      (K := K) (R := K) (T := (T.centres : Set Tiling.Plane))
      (s := 1) (r := 0) (by norm_num) hcarrier (u (φ n)) (Pidx n).1).mp
      (Pidx n).2
  let Tseq : ℕ → TilingSpace K Set.univ := fun n =>
    TilingSpace.translate (g (D.subsequence (φ n))) T
  have htranslate (n : ℕ) :
      (Tseq n).centres =
        u (φ n) +ᵥ (T.centres : Set Tiling.Plane) := by
    ext y
    constructor <;> intro hy
    · rcases hy with ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [u, vadd_eq_add, add_comm]⟩
    · rcases hy with ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [u, vadd_eq_add, add_comm]⟩
  have hEq (n : ℕ) :
      positiveSimilarity 1 (u (φ n)) '' (T.centres : Set Tiling.Plane) =
        (Tseq n).centres :=
    (hsim _ _).trans (htranslate n).symm
  let Q : ∀ n, Continuous.VerticalPlate K ((Tseq n).centres :
      Set Tiling.Plane) := fun n =>
    hEq n ▸ e n (Pidx n).1
  have hQcol (n : ℕ) : Continuous.IsVerticalColumn (Q n) := by
    change Continuous.IsVerticalColumn ((hEq n) ▸ e n (Pidx n).1)
    exact castVerticalPlate_isVerticalColumn (hEq n)
      (e n (Pidx n).1) (hecol n)
  have hanchorR (n : ℕ) : z n ∈ (e n (Pidx n).1).centres := by
    rw [hecent, hsim]
    rw [hzp n]
    exact Set.mem_vadd_set.mpr ⟨p n, hPmem n, rfl⟩
  have hanchor (n : ℕ) : z n ∈ (Q n).centres := by
    change z n ∈ ((hEq n) ▸ e n (Pidx n).1).centres
    exact castVerticalPlate_mem_centres (hEq n)
      (e n (Pidx n).1) (hanchorR n)
  obtain ⟨P, hPcol, hPx⟩ :=
    verticalColumn_survives_anchoredLimit
      Tseq S Q hQcol z hanchor x hzlim hamb
  rw [Continuous.verticalColumnCentres_eq]
  exact Set.mem_iUnion.2 ⟨⟨P, hPcol⟩, hPx⟩

private theorem exists_reverse_translateSequence
    {K : Region} (T S : TilingSpace K Set.univ)
    (hminimal : IsTopologicallyMinimal (orbitHull T))
    (hS : S ∈ orbitHull T) :
    ∃ h : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane),
      LocallyFellConverges
        (TilingSpace.centresSequence
          (TilingSpace.translateSequence h S))
        (T.centres : Set Tiling.Plane) := by
  have hHull : orbitHull S = orbitHull T :=
    hminimal.2.2.2 S hS
  have hT : T ∈ orbitHull S := by
    rw [hHull]
    exact subset_closure (AddAction.mem_orbit_self T)
  change T ∈ closure (AddAction.orbit
    (aePeriodGroup (Set.univ : Set Tiling.Plane)) S) at hT
  obtain ⟨V, hVmem, hVlim⟩ := mem_closure_iff_seq_limit.mp hT
  choose h hh using hVmem
  refine ⟨h, ?_⟩
  have hseq : TilingSpace.translateSequence h S = V := by
    funext n
    exact hh n
  rw [← hseq] at hVlim
  exact (locallyFell_metrizable K Set.univ).2
    (TilingSpace.translateSequence h S) T |>.mp hVlim

private def residueFloorIndex_local
    (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
    (beta : ℝ) : ℕ → ℤ :=
  fun n => Int.floor ((g n : Tiling.Plane).re / beta)

private def residueValue_local
    (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
    (beta : ℝ) : ℕ → ℝ :=
  fun n => (g n : Tiling.Plane).re -
    (residueFloorIndex_local g beta n : ℝ) * beta

private theorem residueValue_local_mem_Icc
    (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
    {beta : ℝ} (hbeta : 0 < beta) :
    ∀ n, residueValue_local g beta n ∈ Set.Icc (0 : ℝ) beta := by
  intro n
  have hlo : (residueFloorIndex_local g beta n : ℝ) ≤
      (g n : Tiling.Plane).re / beta := by
    dsimp [residueFloorIndex_local]
    exact Int.floor_le _
  have hhi : (g n : Tiling.Plane).re / beta <
      (residueFloorIndex_local g beta n : ℝ) + 1 := by
    dsimp [residueFloorIndex_local]
    exact Int.lt_floor_add_one _
  have hlo' : (residueFloorIndex_local g beta n : ℝ) * beta ≤
      (g n : Tiling.Plane).re := (le_div_iff₀ hbeta).mp hlo
  have hhi' : (g n : Tiling.Plane).re <
      (residueFloorIndex_local g beta n : ℝ) * beta + beta := by
    have h := (div_lt_iff₀ hbeta).mp hhi
    simpa [add_mul, mul_add, add_comm, add_left_comm, add_assoc] using h
  constructor <;> dsimp [residueValue_local] <;> linarith

private theorem residue_subsequence_exists_local
    (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
    {beta : ℝ} (hbeta : 0 < beta) :
    ∃ alpha ∈ Set.Icc (0 : ℝ) beta, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
        Tendsto (residueValue_local g beta ∘ phi) atTop (nhds alpha) := by
  obtain ⟨alpha, halpha, phi, hphi, hlim⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) beta)).tendsto_subseq
      (residueValue_local_mem_Icc g hbeta)
  exact ⟨alpha, halpha, phi, hphi, hlim⟩

private theorem translate_action_tendsto_local
    {K : Region} {q : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    {qlim : aePeriodGroup (Set.univ : Set Tiling.Plane)}
    {X : ℕ → TilingSpace K Set.univ} {U : TilingSpace K Set.univ}
    (hq : Tendsto q atTop (nhds qlim))
    (hX : Tendsto X atTop (nhds U)) :
    Tendsto (fun n => TilingSpace.translate (q n) (X n)) atTop
      (nhds (TilingSpace.translate qlim U)) := by
  have hpair : Tendsto (fun n => (q n, X n)) atTop (nhds (qlim, U)) :=
    by
      rw [nhds_prod_eq]
      exact hq.prodMk hX
  exact (translationAction_continuous K Set.univ).tendsto
    (qlim, U) |>.comp hpair

private theorem exists_alignedResidueLimit_local :
    ∀ {K : Region} (T U : TilingSpace K Set.univ)
      (g₀ : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)),
      LocallyFellConverges
        (TilingSpace.centresSequence (TilingSpace.translateSequence g₀ T))
        (U.centres : Set Tiling.Plane) →
      ∀ {beta : ℝ}, 0 < beta →
      ∃ (alpha : ℝ) (V : TilingSpace K Set.univ)
        (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)),
        0 ≤ alpha ∧ alpha < beta ∧
        (V.centres : Set Tiling.Plane) = ((-alpha : ℝ) : ℂ) +ᵥ
          (U.centres : Set Tiling.Plane) ∧
        (∀ n, ∃ m : ℤ, (g n : Tiling.Plane).re = (m : ℝ) * beta) ∧
        LocallyFellConverges
          (TilingSpace.centresSequence
            (TilingSpace.translateSequence g T))
          (V.centres : Set Tiling.Plane) := by
  intro K T U g₀ hconv₀ beta hbeta
  have hOld : Tendsto (TilingSpace.translateSequence g₀ T) atTop (nhds U) :=
    ((locallyFell_metrizable K Set.univ).2
      (TilingSpace.translateSequence g₀ T) U).mpr hconv₀
  obtain ⟨alpha, halpha, phi, hphi, hres⟩ :=
    residue_subsequence_exists_local g₀ hbeta
  have hOld' : Tendsto
      (TilingSpace.translateSequence (g₀ ∘ phi) T) atTop (nhds U) := by
    change Tendsto (TilingSpace.translateSequence g₀ T ∘ phi) atTop (nhds U)
    exact hOld.comp hphi.tendsto_atTop
  by_cases halt : alpha < beta
  · let q : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane) := fun n =>
      ⟨-((residueValue_local g₀ beta (phi n) : ℝ) : Tiling.Plane), by
        simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]
      ⟩
    let qlim : aePeriodGroup (Set.univ : Set Tiling.Plane) :=
      ⟨-alpha, by simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]⟩
    have hq : Tendsto q atTop (nhds qlim) := by
      rw [tendsto_subtype_rng]
      have hplane : Tendsto (fun n =>
          -((residueValue_local g₀ beta (phi n) : ℝ) : Tiling.Plane)) atTop
          (nhds (-((alpha : ℝ) : Tiling.Plane))) := by
        convert (Complex.continuous_ofReal.tendsto _).comp hres.neg using 1 <;>
          simp [Function.comp_def]
      simpa only [q, qlim] using hplane
    let V : TilingSpace K Set.univ := TilingSpace.translate qlim U
    let g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane) := fun n =>
      ⟨(q n : Tiling.Plane) + (g₀ (phi n) : Tiling.Plane), by
        simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]
      ⟩
    have hlim := translate_action_tendsto_local hq hOld'
    have hseq :
        TilingSpace.translateSequence g T =
          (fun n => TilingSpace.translate (q n)
            (TilingSpace.translateSequence (g₀ ∘ phi) T n)) := by
      funext n
      change TilingSpace.translate (g n) T =
        TilingSpace.translate (q n)
          (TilingSpace.translate (g₀ (phi n)) T)
      have hg : g n = q n + g₀ (phi n) := by
        apply Subtype.ext
        rfl
      rw [hg]
      exact add_vadd (q n) (g₀ (phi n)) T
    have hVcent : (V.centres : Set Tiling.Plane) =
        ((-alpha : ℝ) : ℂ) +ᵥ (U.centres : Set Tiling.Plane) := by
      ext z
      change z ∈ (fun x : Tiling.Plane => x + (qlim : Tiling.Plane)) ''
          (U.centres : Set Tiling.Plane) ↔ _
      rw [show (qlim : Tiling.Plane) = ((-alpha : ℝ) : ℂ) by
        simp [qlim]]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Set.mem_vadd_set.mpr ⟨x, hx, by
          simp [vadd_eq_add, add_comm]
          ⟩
      · intro hz
        rcases Set.mem_vadd_set.mp hz with ⟨x, hx, hxz⟩
        exact ⟨x, hx, by simpa [vadd_eq_add, add_comm] using hxz⟩
    have hconv : LocallyFellConverges
        (TilingSpace.centresSequence
          (TilingSpace.translateSequence g T))
        (V.centres : Set Tiling.Plane) := by
      rw [hseq]
      exact ((locallyFell_metrizable K Set.univ).2 _ V).mp hlim
    refine ⟨alpha, V, g, halpha.1, halt, hVcent, ?_, hconv⟩
    intro n
    refine ⟨residueFloorIndex_local g₀ beta (phi n), ?_⟩
    dsimp [g, q, residueValue_local, residueFloorIndex_local]
    ring
  · have halpha_eq : alpha = beta :=
      le_antisymm halpha.2 (not_lt.mp halt)
    let q : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane) := fun n =>
      ⟨((beta - residueValue_local g₀ beta (phi n) : ℝ) : Tiling.Plane), by
        simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]
      ⟩
    let qlim : aePeriodGroup (Set.univ : Set Tiling.Plane) :=
      ⟨0, by simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]⟩
    have hq : Tendsto q atTop (nhds qlim) := by
      rw [tendsto_subtype_rng]
      dsimp [q, qlim]
      change Tendsto (fun n =>
        ((beta - residueValue_local g₀ beta (phi n) : ℝ) : Tiling.Plane)) atTop
        (nhds (0 : Tiling.Plane))
      have hreal : Tendsto
          (fun n => beta - residueValue_local g₀ beta (phi n)) atTop (nhds 0) := by
        have h := (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => beta) atTop (nhds beta)).sub hres
        simpa [halpha_eq] using h
      convert (Complex.continuous_ofReal.tendsto 0).comp hreal using 1 <;>
        simp [Function.comp_def]
    let V : TilingSpace K Set.univ := TilingSpace.translate qlim U
    let g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane) := fun n =>
      ⟨(q n : Tiling.Plane) + (g₀ (phi n) : Tiling.Plane), by
        simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]
      ⟩
    have hlim := translate_action_tendsto_local hq hOld'
    have hseq :
        TilingSpace.translateSequence g T =
          (fun n => TilingSpace.translate (q n)
            (TilingSpace.translateSequence (g₀ ∘ phi) T n)) := by
      funext n
      change TilingSpace.translate (g n) T =
        TilingSpace.translate (q n)
          (TilingSpace.translate (g₀ (phi n)) T)
      have hg : g n = q n + g₀ (phi n) := by
        apply Subtype.ext
        rfl
      rw [hg]
      exact add_vadd (q n) (g₀ (phi n)) T
    have hVcent : (V.centres : Set Tiling.Plane) =
        ((0 : ℝ) : ℂ) +ᵥ (U.centres : Set Tiling.Plane) := by
      ext z
      change z ∈ (fun x : Tiling.Plane => x + (qlim : Tiling.Plane)) ''
          (U.centres : Set Tiling.Plane) ↔ _
      dsimp [qlim]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Set.mem_vadd_set.mpr ⟨x, hx, by simp [vadd_eq_add]
          ⟩
      · intro hz
        rcases Set.mem_vadd_set.mp hz with ⟨x, hx, hxz⟩
        exact ⟨x, hx, by simpa [vadd_eq_add] using hxz⟩
    have hconv : LocallyFellConverges
        (TilingSpace.centresSequence
          (TilingSpace.translateSequence g T))
        (V.centres : Set Tiling.Plane) := by
      rw [hseq]
      exact ((locallyFell_metrizable K Set.univ).2 _ V).mp hlim
    refine ⟨0, V, g, by norm_num, hbeta, ?_, ?_, hconv⟩
    · simpa using hVcent
    · intro n
      refine ⟨residueFloorIndex_local g₀ beta (phi n) + 1, ?_⟩
      dsimp [g, q, residueValue_local, residueFloorIndex_local]
      simp only [Int.cast_add, Int.cast_one]
      ring

private theorem target_common_column_support_period :
    ∀ {K : Region} (T S : TilingSpace K Set.univ),
      IsTopologicallyMinimal (orbitHull T) →
      Continuous.HasFiniteHorizontalComplexity (T.centres : Set Tiling.Plane) →
      ∀ (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
        (_D : FinitePlateColourLimitData T S g),
      ∃ beta' : ℝ, 0 < beta' ∧
        Tiling.RationalPolygonal.SetPeriodicBy
          (regularSupport K (Continuous.verticalColumnCentres K
            (S.centres : Set Tiling.Plane))) ((beta' : ℝ) : ℂ) := by
  intro K T S hminimal hFHC g _D
  obtain ⟨_, _, _, hFHC_S⟩ :=
    alignedLimit_dynamicalFacts T S hminimal hFHC
      (fun n => g (_D.subsequence n)) _D.ambient_converges
  obtain ⟨beta', hbeta', hperiodic⟩ :=
    continuousVerticalPlateSupport_periodic S.tilesOn hFHC_S
  exact ⟨beta', hbeta', hperiodic.1⟩

private theorem exists_reverseAlignedFiniteColourData
    {K : Region} (T S : TilingSpace K Set.univ)
    (hminimal : IsTopologicallyMinimal (orbitHull T))
    (hFHC : Continuous.HasFiniteHorizontalComplexity
      (T.centres : Set Tiling.Plane))
    (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
    (D : FinitePlateColourLimitData T S g) :
    ∃ (beta : ℝ) (alpha : ℝ) (V : TilingSpace K Set.univ)
      (g' : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)),
      0 < beta ∧ 0 ≤ alpha ∧ alpha < beta ∧
      ((V.centres : Set Tiling.Plane) =
        ((-alpha : ℝ) : ℂ) +ᵥ (T.centres : Set Tiling.Plane)) ∧
      Nonempty (FinitePlateColourLimitData S V g') := by
  obtain ⟨hS, _, _, hFHC_S⟩ :=
    alignedLimit_dynamicalFacts T S hminimal hFHC
      (fun n => g (D.subsequence n)) D.ambient_converges
  obtain ⟨beta, hbeta, hperiods⟩ :=
    continuousVerticalPlateSupport_periodic S.tilesOn hFHC_S
  obtain ⟨hreturn, hreturn_conv⟩ :=
    exists_reverse_translateSequence T S hminimal hS
  obtain ⟨alpha, V, g', hα0, hαlt, hVcent, haligned, hconv'⟩ :=
    exists_alignedResidueLimit_local S T hreturn hreturn_conv hbeta
  obtain ⟨D'⟩ :=
    exists_finitePlateColourLimitData S V hbeta hperiods.1
      (fun P hP => hperiods.2 P hP) g' haligned hconv'
  exact ⟨beta, alpha, V, g', hbeta, hα0, hαlt, hVcent, ⟨D'⟩⟩

private theorem columnSupport_sandwich
    {K : Region} {T S V : TilingSpace K Set.univ}
    {g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    {g' : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    {alpha : ℝ}
    (D : FinitePlateColourLimitData T S g)
    (D' : FinitePlateColourLimitData S V g')
    (hVcent : (V.centres : Set Tiling.Plane) =
      ((-alpha : ℝ) : ℂ) +ᵥ (T.centres : Set Tiling.Plane)) :
    regularSupport K (Continuous.verticalColumnCentres K
      (T.centres : Set Tiling.Plane)) ⊆
        regularSupport K (Continuous.verticalColumnCentres K
          (S.centres : Set Tiling.Plane)) ∧
      regularSupport K (Continuous.verticalColumnCentres K
        (S.centres : Set Tiling.Plane)) ⊆
        ((-alpha : ℝ) : ℂ) +ᵥ
          regularSupport K (Continuous.verticalColumnCentres K
            (T.centres : Set Tiling.Plane)) := by
  constructor
  · rw [← D.columnSupport_eq]
    exact regularSupport_mono_local
      (columnLimit_subset_targetVerticalColumnCentres D)
  · have hsub := regularSupport_mono_local (K := K)
      (columnLimit_subset_targetVerticalColumnCentres D')
    rw [D'.columnSupport_eq] at hsub
    rw [hVcent, verticalColumnCentres_vadd, regularSupport_vadd] at hsub
    exact hsub

private theorem verticalColumnSupport_verticalInvariant_local
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ)
    (y : ℝ) :
    (((y : ℂ) * Complex.I) +ᵥ
        regularSupport K (Continuous.verticalColumnCentres K T)) =
      regularSupport K (Continuous.verticalColumnCentres K T) := by
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

private theorem verticalColumnSupport_isVerticalSlab_local
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ) :
    ∃ X : Set ℝ, X = interior (closure X) ∧
      regularSupport K (Continuous.verticalColumnCentres K T) =
        Complex.re ⁻¹' X := by
  obtain ⟨X, hX⟩ := (verticalInvariant_iff_product
    (regularSupport K (Continuous.verticalColumnCentres K T))).mp
      (verticalColumnSupport_verticalInvariant_local hTile)
  have hreg := (regularSupport_isRegularOpen K
    (Continuous.verticalColumnCentres K T)).2
  change regularSupport K (Continuous.verticalColumnCentres K T) =
    Complex.re ⁻¹' X at hX
  rw [hX, Complex.closure_preimage_re, Complex.interior_preimage_re] at hreg
  refine ⟨X, ?_, hX⟩
  ext x
  have hx := Set.ext_iff.mp hreg (x : ℂ)
  simpa using hx.symm

private theorem columnSupport_base_periodic_local
    {K : Region} {T : TilingSpace K Set.univ} {beta : ℝ}
    (hperiod : Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K (Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane))) ((beta : ℝ) : ℂ)) :
    ∃ X : Set ℝ,
      regularSupport K (Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane)) = Complex.re ⁻¹' X ∧
      ∀ x : ℝ, x + beta ∈ X ↔ x ∈ X := by
  obtain ⟨X, _hXregular, hXreg⟩ :=
    verticalColumnSupport_isVerticalSlab_local T.tilesOn
  refine ⟨X, hXreg, ?_⟩
  intro x
  have hp := hperiod (x : ℂ)
  rw [hXreg] at hp
  simpa [Tiling.RationalPolygonal.SetPeriodicBy, Complex.add_re] using hp

private lemma aePeriod_add_local {S : Set ℝ} {a c : ℝ}
    (ha : (a +ᵥ S) =ᵐ[volume] S) (hc : (c +ᵥ S) =ᵐ[volume] S) :
    ((a + c) +ᵥ S) =ᵐ[volume] S := by
  have htranslate :=
    (quasiMeasurePreserving_add_left volume (-a)).vadd_ae_eq_of_ae_eq a hc
  have hfirst : ((a + c) +ᵥ S) =ᵐ[volume] (a +ᵥ S) := by
    simpa only [add_vadd] using htranslate
  exact hfirst.trans ha

private lemma aePeriod_neg_local {S : Set ℝ} {a : ℝ}
    (ha : (a +ᵥ S) =ᵐ[volume] S) : ((-a) +ᵥ S) =ᵐ[volume] S := by
  have hq : Measure.QuasiMeasurePreserving
      (fun x : ℝ => -(-a) + x) volume volume := by
    simpa using quasiMeasurePreserving_add_left volume a
  have htranslate := hq.vadd_ae_eq_of_ae_eq (-a) ha
  have hfirst : S =ᵐ[volume] ((-a) +ᵥ S) := by
    have hset : (-a) +ᵥ (a +ᵥ S) = S := by
      rw [vadd_vadd]
      simp
    rw [hset] at htranslate
    exact htranslate
  exact hfirst.symm

private def aePeriodGroupReal (S : Set ℝ) : AddSubgroup ℝ where
  carrier := {a | (a +ᵥ S) =ᵐ[volume] S}
  zero_mem' := by simpa using (ae_eq_refl S : S =ᵐ[volume] S)
  add_mem' := aePeriod_add_local
  neg_mem' := aePeriod_neg_local

private lemma aePeriod_zsmul_local
    {Y : Set ℝ} {b : ℝ} (hbY : (b +ᵥ Y) =ᵐ[volume] Y) (n : ℤ) :
    ((n • b) +ᵥ Y) =ᵐ[volume] Y := by
  exact (aePeriodGroupReal Y).zsmul_mem hbY n

private lemma restrict_periodic_vaddInvariant_local
    {Y : Set ℝ} {b : ℝ} (_hY : MeasurableSet Y)
    (hbY : (b +ᵥ Y) =ᵐ[volume] Y) :
    VAddInvariantMeasure (AddSubgroup.zmultiples b) ℝ
      (volume.restrict Y) := by
  constructor
  rintro ⟨c, hc⟩ s hs
  rcases hc with ⟨n, hn⟩
  have hcY : (c +ᵥ Y) =ᵐ[volume] Y := by
    rw [← hn]
    exact aePeriod_zsmul_local hbY n
  have hpre :
      (fun x : ℝ => c + x) ⁻¹' s ∩ Y =
        (fun x : ℝ => c + x) ⁻¹' (s ∩ (c +ᵥ Y)) := by
    ext x
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hxs, hxY⟩
      exact ⟨hxs, ⟨x, hxY, rfl⟩⟩
    · rintro ⟨hxs, y, hyY, hxy⟩
      have : x = y := add_left_cancel hxy.symm
      exact ⟨hxs, this ▸ hyY⟩
  change (volume.restrict Y) ((fun x : ℝ => c + x) ⁻¹' s) =
    (volume.restrict Y) s
  calc
    (volume.restrict Y) ((fun x : ℝ => c + x) ⁻¹' s) =
        volume ((fun x : ℝ => c + x) ⁻¹' s ∩ Y) :=
      Measure.restrict_apply (hs.preimage (measurable_const.add measurable_id))
    _ = volume ((fun x : ℝ => c + x) ⁻¹' (s ∩ (c +ᵥ Y))) := by rw [hpre]
    _ = volume (s ∩ (c +ᵥ Y)) := measure_preimage_add volume c _
    _ = volume (s ∩ Y) := measure_congr (ae_eq_set_inter (ae_eq_refl s) hcY)
    _ = (volume.restrict Y) s := (Measure.restrict_apply hs).symm

private lemma periodic_cell_measure_eq_local
    {Y : Set ℝ} {b : ℝ} (hY : MeasurableSet Y) (hb : 0 < b)
    (hbY : (b +ᵥ Y) =ᵐ[volume] Y) (x : ℝ) :
    volume (Y ∩ Set.Ioc (x - b) x) =
      volume (Y ∩ Set.Ioc 0 b) := by
  have hInvariant : VAddInvariantMeasure (AddSubgroup.zmultiples b) ℝ
      (volume.restrict Y) :=
    restrict_periodic_vaddInvariant_local hY hbY
  have h0 := isAddFundamentalDomain_Ioc hb 0 (volume.restrict Y)
  have hx := isAddFundamentalDomain_Ioc hb (x - b) (volume.restrict Y)
  have heq := hx.measure_eq h0
  simp only [sub_add_cancel, zero_add, Measure.restrict_apply measurableSet_Ioc] at heq
  simpa only [inter_comm] using heq

private lemma base_shift_periodic_local
    {A : Set ℝ} {beta alpha : ℝ}
    (hA : ∀ x : ℝ, x + beta ∈ A ↔ x ∈ A) :
    ∀ x : ℝ, x + beta ∈ ((-alpha) +ᵥ A) ↔ x ∈ ((-alpha) +ᵥ A) := by
  intro x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem]
  change (-( -alpha) + (x + beta) ∈ A) ↔ (-( -alpha) + x ∈ A)
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hA (x + alpha)

private lemma volume_vadd_inter_Ioc_local
    {A : Set ℝ} {t l r : ℝ} :
    volume ((t +ᵥ A) ∩ Set.Ioc l r) =
      volume (A ∩ Set.Ioc (l - t) (r - t)) := by
  rw [← measure_preimage_add volume t]
  congr 1
  ext x
  simp only [mem_preimage, mem_inter_iff, Set.mem_vadd_set_iff_neg_vadd_mem,
    vadd_eq_add, mem_Ioc]
  constructor
  · rintro ⟨hA, hxl, hxr⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [sub_eq_add_neg, add_assoc] using hA
    · linarith
    · linarith
  · rintro ⟨hxA, hxl, hxr⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [sub_eq_add_neg, add_assoc] using hxA
    · linarith
    · linarith

private theorem periodic_shift_base_aeEq_local
    {A : Set ℝ} {beta alpha : ℝ} (hbeta : 0 < beta)
    (hAmeas : MeasurableSet A)
    (hAperiod : ∀ x : ℝ, x + beta ∈ A ↔ x ∈ A)
    (hsubset : A ⊆ ((-alpha) +ᵥ A)) :
    A =ᵐ[volume] ((-alpha) +ᵥ A) := by
  let B : Set ℝ := (-alpha) +ᵥ A
  have hBperiod : ∀ x : ℝ, x + beta ∈ B ↔ x ∈ B := by
    simpa [B] using (base_shift_periodic_local hAperiod)
  have hAset : beta +ᵥ A = A := by
    ext x
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [sub_eq_add_neg, add_assoc, add_comm] using (hAperiod (x - beta)).symm
  have hAae : (beta +ᵥ A) =ᵐ[volume] A := by
    simpa [hAset] using (ae_eq_refl A : A =ᵐ[volume] A)
  have hBmeas : MeasurableSet B := by
    have hp : MeasurableSet ((fun x : ℝ => alpha + x) ⁻¹' A) :=
      hAmeas.preimage (measurable_const.add measurable_id)
    have heq : ((fun x : ℝ => alpha + x) ⁻¹' A) = B := by
      ext x
      simp [B, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    rw [← heq]
    exact hp
  have hBset : beta +ᵥ B = B := by
    ext x
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (hBperiod (x - beta)).symm
  have hBae : (beta +ᵥ B) =ᵐ[volume] B := by
    simpa [hBset] using (ae_eq_refl B : B =ᵐ[volume] B)
  have hBsub : A ⊆ B := by simpa [B] using hsubset
  have hcellAB : volume (A ∩ Set.Ioc 0 beta) =
      volume (B ∩ Set.Ioc 0 beta) := by
    have hAshift := periodic_cell_measure_eq_local hAmeas hbeta hAae
      (alpha + beta)
    have hBshift := volume_vadd_inter_Ioc_local
      (A := A) (t := -alpha) (l := 0) (r := beta)
    have hBshift' : volume (B ∩ Set.Ioc 0 beta) =
        volume (A ∩ Set.Ioc alpha (alpha + beta)) := by
      simpa [B, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hBshift
    rw [hBshift', ← hAshift]
    simp [sub_eq_add_neg, add_comm, add_assoc]
  have hcellDiff : volume ((B \ A) ∩ Set.Ioc 0 beta) = 0 := by
    have hsubcell : A ∩ Set.Ioc 0 beta ⊆ B ∩ Set.Ioc 0 beta :=
      inter_subset_inter hBsub subset_rfl
    have hdiff := measure_sdiff hsubcell
      (hAmeas.inter measurableSet_Ioc).nullMeasurableSet
      (ne_top_of_le_ne_top
        (measure_Ioc_lt_top (μ := volume) (a := (0 : ℝ)) (b := beta)).ne
        (measure_mono inter_subset_right))
    have hdiff' : volume ((B ∩ Set.Ioc 0 beta) \
        (A ∩ Set.Ioc 0 beta)) = 0 := by
      rw [hdiff, hcellAB]
      simp
    have hset : ((B \ A) ∩ Set.Ioc 0 beta : Set ℝ) =
        ((B ∩ Set.Ioc 0 beta) \ (A ∩ Set.Ioc 0 beta) : Set ℝ) :=
      Set.ext (fun x => by
        simp only [mem_inter_iff, Set.mem_sdiff]
        tauto)
    rw [hset]
    exact hdiff'
  have hCmeas : MeasurableSet (B \ A) := hBmeas.diff hAmeas
  have hCperiod : ∀ x : ℝ, x + beta ∈ (B \ A) ↔ x ∈ (B \ A) := by
    intro x
    constructor
    · intro hx
      refine ⟨(hBperiod x).mp hx.1, ?_⟩
      intro hxA
      exact hx.2 ((hAperiod x).mpr hxA)
    · intro hx
      refine ⟨(hBperiod x).mpr hx.1, ?_⟩
      intro hxA
      exact hx.2 ((hAperiod x).mp hxA)
  have hCae : (beta +ᵥ (B \ A)) =ᵐ[volume] (B \ A) := by
    have hCset : beta +ᵥ (B \ A) = B \ A := by
      ext x
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        (hCperiod (x - beta)).symm
    rw [hCset]
    exact ae_eq_refl _
  have hnull : volume (B \ A) = 0 := by
    have hcover : (⋃ n : ℤ, Set.Ioc (n • beta) ((n + 1) • beta)) =
        (Set.univ : Set ℝ) := iUnion_Ioc_zsmul hbeta
    calc
      volume (B \ A) = volume ((B \ A) ∩ Set.univ) := by simp
      _ = volume ((B \ A) ∩ (⋃ n : ℤ,
          Set.Ioc (n • beta) ((n + 1) • beta))) := by rw [hcover]
      _ = volume (⋃ n : ℤ,
          (B \ A) ∩ Set.Ioc (n • beta) ((n + 1) • beta)) := by rw [inter_iUnion]
      _ = 0 := measure_iUnion_null (fun n => by
        have hcell := periodic_cell_measure_eq_local hCmeas hbeta hCae
          (((n + 1 : ℤ) : ℝ) * beta)
        have hend : (((n + 1 : ℤ) : ℝ) * beta - beta) =
            (n : ℤ) • beta := by
          rw [zsmul_eq_mul]
          push_cast
          ring
        have hright : (((n + 1 : ℤ) : ℝ) * beta) =
            (n + 1) • beta := by
          rw [zsmul_eq_mul]
        rw [hend, hright] at hcell
        rw [hcell, hcellDiff])
  apply ae_eq_set.mpr
  constructor
  · rw [sdiff_eq_empty.mpr hBsub, measure_empty]
  · exact hnull

private theorem regularOpen_real_eq_of_aeEq_local
    {U V : Set ℝ} (hUopen : IsOpen U)
    (hUregular : interior (closure U) = U)
    (hVopen : IsOpen V)
    (hVregular : interior (closure V) = V)
    (hUV : U =ᵐ[volume] V) : U = V := by
  have closure_mono_of_ae {A B : Set ℝ} (hA : IsOpen A) (hB : IsOpen B)
      (hAB : A =ᵐ[volume] B) : A ⊆ closure B := by
    intro x hxA
    by_contra hxB
    let W := A ∩ (closure B)ᶜ
    have hWopen : IsOpen W := hA.inter isClosed_closure.isOpen_compl
    have hxW : x ∈ W := ⟨hxA, hxB⟩
    have hWzero : volume W = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr (hAB.mono fun y hy hyW => by
        have hyB : y ∈ B := Eq.mp hy hyW.1
        exact hyW.2 (subset_closure hyB))
    exact hWopen.measure_ne_zero volume ⟨x, hxW⟩ hWzero
  have hclosure : closure U = closure V := Set.Subset.antisymm
    (closure_minimal (closure_mono_of_ae hUopen hVopen hUV) isClosed_closure)
    (closure_minimal (closure_mono_of_ae hVopen hUopen hUV.symm) isClosed_closure)
  calc
    U = interior (closure U) := hUregular.symm
    _ = interior (closure V) := congrArg interior hclosure
    _ = V := hVregular

private theorem columnSupport_eq_shift_of_subset_local
    {K : Region} {T : TilingSpace K Set.univ} {beta alpha : ℝ}
    (hbeta : 0 < beta)
    (hperiod : Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K (Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane))) ((beta : ℝ) : ℂ))
    (hsubset : regularSupport K (Continuous.verticalColumnCentres K
      (T.centres : Set Tiling.Plane)) ⊆
      ((-alpha : ℝ) : ℂ) +ᵥ regularSupport K
        (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane))) :
    regularSupport K (Continuous.verticalColumnCentres K
      (T.centres : Set Tiling.Plane)) =
      ((-alpha : ℝ) : ℂ) +ᵥ regularSupport K
        (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane)) := by
  obtain ⟨X, hXregular, hXreg⟩ :=
    verticalColumnSupport_isVerticalSlab_local T.tilesOn
  have hXperiod : ∀ x : ℝ, x + beta ∈ X ↔ x ∈ X := by
    intro x
    have hp := hperiod (x : ℂ)
    rw [hXreg] at hp
    simpa [Tiling.RationalPolygonal.SetPeriodicBy, Complex.add_re] using hp
  have hXsubset : X ⊆ ((-alpha) +ᵥ X) := by
    intro x hx
    have hz : (x : ℂ) ∈ regularSupport K (Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane)) := by
      rw [hXreg]
      exact hx
    have hz' := hsubset hz
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem] at hz'
    rw [hXreg] at hz'
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [Complex.add_re, vadd_eq_add, sub_eq_add_neg, add_comm] using hz'
  have hXmeas : MeasurableSet X := by
    rw [hXregular]
    exact measurableSet_interior
  have hXae := periodic_shift_base_aeEq_local hbeta hXmeas hXperiod hXsubset
  have hXopen : IsOpen X := by rw [hXregular]; exact isOpen_interior
  have hXshift_open : IsOpen ((-alpha) +ᵥ X) := hXopen.vadd _
  have hXshift_regular : interior (closure ((-alpha) +ᵥ X)) =
      ((-alpha) +ᵥ X) := by
    calc
      interior (closure ((-alpha) +ᵥ X)) =
          (-alpha) +ᵥ interior (closure X) := by
            rw [closure_vadd, interior_vadd]
      _ = (-alpha) +ᵥ X := by rw [hXregular.symm]
  have hXeq : X = (-alpha) +ᵥ X :=
    regularOpen_real_eq_of_aeEq_local hXopen hXregular.symm hXshift_open
      hXshift_regular hXae
  rw [hXreg]
  ext z
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem]
  change z.re ∈ X ↔ (-( -alpha : ℂ) + z).re ∈ X
  have hz := Set.ext_iff.mp hXeq z.re
  simpa [Set.mem_vadd_set_iff_neg_vadd_mem, Complex.add_re, Complex.neg_re,
    vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz

private theorem columnSupport_eq_of_sandwich_local
    {X Y : Set Tiling.Plane} {u : Tiling.Plane}
    (hXY : X ⊆ Y) (hYX : Y ⊆ u +ᵥ X)
    (hshift : X = u +ᵥ X) : X = Y := by
  apply Set.Subset.antisymm hXY
  intro y hy
  rw [hshift]
  exact hYX hy

private theorem columnSupport_eq_from_data_local
    {K : Region} {T S V : TilingSpace K Set.univ}
    {g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    {g' : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    {alpha beta : ℝ}
    (hbeta : 0 < beta)
    (hperiod : Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K (Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane))) ((beta : ℝ) : ℂ))
    (D : FinitePlateColourLimitData T S g)
    (D' : FinitePlateColourLimitData S V g')
    (hVcent : (V.centres : Set Tiling.Plane) =
      ((-alpha : ℝ) : ℂ) +ᵥ (T.centres : Set Tiling.Plane)) :
    regularSupport K (Continuous.verticalColumnCentres K
      (T.centres : Set Tiling.Plane)) =
      regularSupport K (Continuous.verticalColumnCentres K
        (S.centres : Set Tiling.Plane)) := by
  have hsand := columnSupport_sandwich D D' hVcent
  have hXsubset := hsand.1.trans hsand.2
  have hshift := columnSupport_eq_shift_of_subset_local hbeta hperiod hXsubset
  exact columnSupport_eq_of_sandwich_local hsand.1 hsand.2 hshift

private theorem centres_eq_of_same_regularSupport_local
    {K : Region} {T A B : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (hAsub : A ⊆ T) (hBsub : B ⊆ T)
    (hreg : regularSupport K A = regularSupport K B) : A = B := by
  apply Set.Subset.antisymm
  · intro s hs
    by_contra hsB
    obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hzopen : z ∈ K.openCarrier := by
      change z ∈ interior K.support
      exact hz
    let U : Set Tiling.Plane := (s : Tiling.Plane) +ᵥ K.openCarrier
    have hUopen : IsOpen U := by
      dsimp [U]
      exact (Homeomorph.addLeft (s : Tiling.Plane)).isOpenMap _
        K.openCarrier_regularOpen.1
    have hxU : (s : Tiling.Plane) +ᵥ z ∈ U := by
      dsimp [U]
      exact Set.mem_vadd_set.mpr ⟨z, hzopen, rfl⟩
    have hdisj : Disjoint U (openUnion K B) := by
      apply Set.disjoint_left.2
      intro x hxU' hxB'
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier] at hxB'
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hxB'
      have hst : (s : Tiling.Plane) ≠ (t : Tiling.Plane) := by
        intro hst
        apply hsB
        exact hst.symm ▸ t.property
      have hpack :=
        (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp
          hTile.2.1 (hAsub hs) (hBsub t.property) hst
      exact Set.disjoint_left.1 hpack hxU' ht
    have hUreg : U ⊆ regularSupport K A := by
      have hUsub : U ⊆ openUnion K A := by
        intro x hx
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        exact ⟨⟨s, hs⟩, hx⟩
      unfold regularSupport
      intro x hx
      exact interior_mono (closure_mono hUsub)
        (hUopen.subset_interior_closure hx)
    have hUcl : U ⊆ closure (openUnion K B) := by
      intro x hx
      have hxreg : x ∈ regularSupport K B := hreg ▸ hUreg hx
      change x ∈ interior (closure (openUnion K B)) at hxreg
      exact interior_subset hxreg
    have hxcl : (s : Tiling.Plane) +ᵥ z ∈ closure (openUnion K B) :=
      hUcl hxU
    obtain ⟨y, hyU, hyB⟩ :=
      (mem_closure_iff_nhds.mp hxcl) U (hUopen.mem_nhds hxU)
    exact Set.disjoint_left.1 hdisj hyU hyB
  · intro s hs
    by_contra hsA
    obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hzopen : z ∈ K.openCarrier := by
      change z ∈ interior K.support
      exact hz
    let U : Set Tiling.Plane := (s : Tiling.Plane) +ᵥ K.openCarrier
    have hUopen : IsOpen U := by
      dsimp [U]
      exact (Homeomorph.addLeft (s : Tiling.Plane)).isOpenMap _
        K.openCarrier_regularOpen.1
    have hxU : (s : Tiling.Plane) +ᵥ z ∈ U := by
      dsimp [U]
      exact Set.mem_vadd_set.mpr ⟨z, hzopen, rfl⟩
    have hdisj : Disjoint U (openUnion K A) := by
      apply Set.disjoint_left.2
      intro x hxU' hxA'
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier] at hxA'
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hxA'
      have hst : (s : Tiling.Plane) ≠ (t : Tiling.Plane) := by
        intro hst
        apply hsA
        exact hst.symm ▸ t.property
      have hpack :=
        (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp
          hTile.2.1 (hBsub hs) (hAsub t.property) hst
      exact Set.disjoint_left.1 hpack hxU' ht
    have hUreg : U ⊆ regularSupport K B := by
      have hUsub : U ⊆ openUnion K B := by
        intro x hx
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        exact ⟨⟨s, hs⟩, hx⟩
      unfold regularSupport
      intro x hx
      exact interior_mono (closure_mono hUsub)
        (hUopen.subset_interior_closure hx)
    have hUcl : U ⊆ closure (openUnion K A) := by
      intro x hx
      have hxreg : x ∈ regularSupport K A := hreg.symm ▸ hUreg hx
      change x ∈ interior (closure (openUnion K A)) at hxreg
      exact interior_subset hxreg
    have hxcl : (s : Tiling.Plane) +ᵥ z ∈ closure (openUnion K A) :=
      hUcl hxU
    obtain ⟨y, hyU, hyA⟩ :=
      (mem_closure_iff_nhds.mp hxcl) U (hUopen.mem_nhds hxU)
    exact Set.disjoint_left.1 hdisj hyU hyA

private theorem columnLimit_eq_verticalColumnCentres :
    ∀ {K : Region} (T S : TilingSpace K Set.univ),
      IsTopologicallyMinimal (orbitHull T) →
      Continuous.HasFiniteHorizontalComplexity (T.centres : Set Tiling.Plane) →
      ∀ {beta : ℝ}, 0 < beta →
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (Continuous.verticalColumnCentres K
          (T.centres : Set Tiling.Plane))) ((beta : ℝ) : ℂ) →
      ∀ (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
        (D : FinitePlateColourLimitData T S g),
      (∀ n, ∃ m : ℤ, (g n : Tiling.Plane).re = (m : ℝ) * beta) →
      D.columnLimit = Continuous.verticalColumnCentres K
        (S.centres : Set Tiling.Plane) := by
  intro K T S hminimal hFHC beta hbeta hperiod g D _hg
  obtain ⟨_beta', alpha, V, g', _hbeta', _hα0, _hαlt, hVcent, ⟨D'⟩⟩ :=
    exists_reverseAlignedFiniteColourData T S hminimal hFHC g D
  have hSupportEq := columnSupport_eq_from_data_local hbeta hperiod D D' hVcent
  have hreg : regularSupport K D.columnLimit =
      regularSupport K (Continuous.verticalColumnCentres K
        (S.centres : Set Tiling.Plane)) :=
    D.columnSupport_eq.trans hSupportEq
  have hAsub : D.columnLimit ⊆ (S.centres : Set Tiling.Plane) := by
    intro x hx
    rw [← D.coloured_union]
    exact Set.mem_union_left _ hx
  have hBsub : Continuous.verticalColumnCentres K
      (S.centres : Set Tiling.Plane) ⊆ (S.centres : Set Tiling.Plane) := by
    intro z hz
    rw [Continuous.verticalColumnCentres_eq, Set.mem_iUnion] at hz
    obtain ⟨P, hzP⟩ := hz
    obtain ⟨p, hp, rfl⟩ := hzP
    exact p.2
  exact centres_eq_of_same_regularSupport_local S.tilesOn hAsub hBsub hreg


private theorem target_card_le_source_of_reverseAlignedLimit :
    ∀ {K : Region} (T S : TilingSpace K Set.univ)
      (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
      (D : FinitePlateColourLimitData T S g),
      IsTopologicallyMinimal (orbitHull T) →
      Continuous.HasFiniteHorizontalComplexity (T.centres : Set Tiling.Plane) →
      D.columnLimit = Continuous.verticalColumnCentres K (S.centres : Set Tiling.Plane) →
      Set.ncard (Continuous.nonColumnVerticalPlates K (S.centres : Set Tiling.Plane)) ≤
        Set.ncard (Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)) := by
  intro K T S g D hminimal hFHC hcolumn
  obtain ⟨hS, hHullS, hminimalS, hFHC_S⟩ :=
    alignedLimit_dynamicalFacts T S hminimal hFHC
      (fun n => g (D.subsequence n)) D.ambient_converges
  obtain ⟨beta, hbeta, hperiods⟩ :=
    continuousVerticalPlateSupport_periodic S.tilesOn hFHC_S
  obtain ⟨hreturn, hreturn_conv⟩ :=
    exists_reverse_translateSequence T S hminimal hS
  obtain ⟨alpha, V, g', hα0, hαlt, hVcent, haligned, hconv'⟩ :=
    exists_alignedResidueLimit_local S T hreturn hreturn_conv hbeta
  obtain ⟨D'⟩ :=
    exists_finitePlateColourLimitData S V hbeta hperiods.1
      (fun P hP => hperiods.2 P hP) g' haligned hconv'
  have hcolumn' : D'.columnLimit =
      Continuous.verticalColumnCentres K (V.centres : Set Tiling.Plane) := by
    apply columnLimit_eq_verticalColumnCentres S V hminimalS hFHC_S hbeta
      hperiods.1 g' D'
    exact haligned
  obtain ⟨hpartition, hnonempty⟩ := targetPlateBlocks_partition D' hcolumn'
  have hreverse := source_card_le_target_of_blocks D' hpartition hnonempty
  have hcarrier : K.openCarrier = positiveSimilarity 1 0 '' K.openCarrier := by
    ext z
    constructor
    · intro hz
      exact ⟨z, hz, by simp [positiveSimilarity]⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [positiveSimilarity] using hz
  have hsim (c : Tiling.Plane) (A : Set Tiling.Plane) :
      positiveSimilarity 1 c '' A = c +ᵥ A := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Set.mem_vadd_set.mpr ⟨w, hw, by
        simp [positiveSimilarity, vadd_eq_add, add_comm]⟩
    · intro hz
      rcases Set.mem_vadd_set.mp hz with ⟨w, hw, hwz⟩
      refine ⟨w, hw, ?_⟩
      simpa [positiveSimilarity, vadd_eq_add, add_comm] using hwz
  have hreverse' : Set.ncard (Continuous.nonColumnVerticalPlates K
      (S.centres : Set Tiling.Plane)) ≤
      Set.ncard (Continuous.nonColumnVerticalPlates K
        (positiveSimilarity 1 (((-alpha : ℝ) : ℂ)) ''
          (T.centres : Set Tiling.Plane))) := by
    calc
      _ ≤ Set.ncard (Continuous.nonColumnVerticalPlates K
          (V.centres : Set Tiling.Plane)) := hreverse
      _ = _ := by rw [hVcent, ← hsim]
  let e0 : Continuous.VerticalPlate K (T.centres : Set Tiling.Plane) ≃
      Continuous.VerticalPlate K
        (positiveSimilarity 1 (((-alpha : ℝ) : ℂ)) ''
          (T.centres : Set Tiling.Plane)) :=
    verticalPlate_positiveSimilarityEquiv
      (K := K) (R := K) (T := (T.centres : Set Tiling.Plane))
      (s := 1) (r := 0) (by norm_num) hcarrier (((-alpha : ℝ) : ℂ))
  let f :
      ↑(Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)) →
        ↑(Continuous.nonColumnVerticalPlates K
          (positiveSimilarity 1 (((-alpha : ℝ) : ℂ)) ''
            (T.centres : Set Tiling.Plane))) :=
    fun P => ⟨e0 P.1, by
      intro hcol
      exact P.2 ((verticalPlate_positiveSimilarityEquiv_isVerticalColumn
        (K := K) (R := K) (T := (T.centres : Set Tiling.Plane))
        (s := 1) (r := 0) (by norm_num) hcarrier (((-alpha : ℝ) : ℂ)) P.1).mpr hcol)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro P Q hPQ
      apply Subtype.ext
      apply e0.injective
      exact congrArg Subtype.val hPQ
    · intro Q
      let P0 := e0.symm Q.1
      have hcol0 : ¬ Continuous.IsVerticalColumn P0 := by
        intro hcol
        have hcolE : Continuous.IsVerticalColumn (e0 P0) :=
          (verticalPlate_positiveSimilarityEquiv_isVerticalColumn
            (K := K) (R := K) (T := (T.centres : Set Tiling.Plane))
            (s := 1) (r := 0) (by norm_num) hcarrier (((-alpha : ℝ) : ℂ)) P0).mp
            hcol
        have heq : e0 P0 = Q.1 := e0.apply_symm_apply Q.1
        exact Q.2 (heq ▸ hcolE)
      refine ⟨⟨P0, hcol0⟩, ?_⟩
      apply Subtype.ext
      exact e0.apply_symm_apply Q.1
  have hecard : Set.ncard (Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane)) =
      Set.ncard (Continuous.nonColumnVerticalPlates K
        (positiveSimilarity 1 (((-alpha : ℝ) : ℂ)) ''
          (T.centres : Set Tiling.Plane))) := by
    exact Set.ncard_congr' (Equiv.ofBijective f hf)
  exact hreverse'.trans_eq hecard.symm

private theorem allCentres_iff_noNonColumnPlate
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane) :
    T = Tiling.AxisParallel.Continuous.verticalColumnCentres K T ↔
      ¬ Nonempty
        ↑(Tiling.AxisParallel.Continuous.nonColumnVerticalPlates K T) := by
  constructor
  · intro hAll hNonColumn
    obtain ⟨P⟩ := hNonColumn
    obtain ⟨x, hxP⟩ := verticalPlate_centres_nonempty P.1
    have hxT : x ∈ T := verticalPlate_centres_subset P.1 hxP
    have hxColumn : x ∈
        Tiling.AxisParallel.Continuous.verticalColumnCentres K T := by
      rw [← hAll]
      exact hxT
    rw [Tiling.AxisParallel.Continuous.verticalColumnCentres_eq] at hxColumn
    obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hxColumn
    have hPQ : P.1 = Q.1 := verticalPlate_eq_of_common_centre hxP hxQ
    exact P.2 (hPQ ▸ Q.2)
  · intro hNoNonColumn
    apply Set.Subset.antisymm
    · intro x hxT
      let t : T := ⟨x, hxT⟩
      let P := Tiling.AxisParallel.Continuous.VerticalPlate.ofCentre (K := K) t
      have hPColumn : Tiling.AxisParallel.Continuous.IsVerticalColumn P := by
        by_contra hP
        exact hNoNonColumn ⟨⟨P, hP⟩⟩
      rw [Tiling.AxisParallel.Continuous.verticalColumnCentres_eq,
        Set.mem_iUnion]
      exact ⟨⟨P, hPColumn⟩,
        Tiling.AxisParallel.Continuous.VerticalPlate.mem_centres_ofCentre t⟩
    · intro x hx
      rw [Tiling.AxisParallel.Continuous.verticalColumnCentres_eq] at hx
      obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
      exact verticalPlate_centres_subset P.1 hxP

private theorem regularSupport_eq_empty_iff
    (K : Tiling.AxisParallel.Region) (S : Set Tiling.Plane) :
    Tiling.AxisParallel.regularSupport K S = ∅ ↔ S = ∅ := by
  constructor
  · intro hSupport
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hxUnion : s + x ∈ Tiling.AxisParallel.openUnion K S := by
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion,
        ← Region.openCarrier, Set.mem_iUnion]
      exact ⟨⟨s, hs⟩, x, hx, rfl⟩
    have hOpen : IsOpen (Tiling.AxisParallel.openUnion K S) := by
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
      exact isOpen_iUnion fun t ↦
        (Homeomorph.addLeft (t : Tiling.Plane)).isOpenMap _
          (K.openCarrier_regularOpen).1
    have hxSupport : s + x ∈ Tiling.AxisParallel.regularSupport K S := by
      rw [Tiling.AxisParallel.regularSupport, Tiling.Polygonal.regularSupport,
        ← openUnion, mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (hOpen.mem_nhds hxUnion) subset_closure
    rw [hSupport] at hxSupport
    exact hxSupport
  · rintro rfl
    simp [Tiling.AxisParallel.regularSupport, Tiling.Polygonal.regularSupport,
      Tiling.Polygonal.openUnion]

private theorem verticalColumnCentres_eq_empty_of_fullNonColumnPlate
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {P : Tiling.AxisParallel.Continuous.VerticalPlate K T}
    (hP : ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P)
    (hfull : P.centres = T) :
    Tiling.AxisParallel.Continuous.verticalColumnCentres K T = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hxColumn
  rw [Tiling.AxisParallel.Continuous.verticalColumnCentres_eq] at hxColumn
  obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hxColumn
  have hxT : x ∈ T := verticalPlate_centres_subset Q.1 hxQ
  have hxP : x ∈ P.centres := by rwa [hfull]
  have hPQ : P = Q.1 := verticalPlate_eq_of_common_centre hxP hxQ
  exact hP (hPQ ▸ Q.2)

private theorem not_isVerticalColumn_of_columnCentres_eq_empty
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (hEmpty : Tiling.AxisParallel.Continuous.verticalColumnCentres K T = ∅)
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T) :
    ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P := by
  intro hP
  obtain ⟨x, hxP⟩ := verticalPlate_centres_nonempty P
  have hxColumn : x ∈
      Tiling.AxisParallel.Continuous.verticalColumnCentres K T := by
    rw [Tiling.AxisParallel.Continuous.verticalColumnCentres_eq,
      Set.mem_iUnion]
    exact ⟨⟨P, hP⟩, hxP⟩
  rw [hEmpty] at hxColumn
  exact hxColumn

private theorem fullNonColumnPlate_of_equiv
    {K : Tiling.AxisParallel.Region} {A B : Set Tiling.Plane}
    (e : ↑(Tiling.AxisParallel.Continuous.nonColumnVerticalPlates K A) ≃
      ↑(Tiling.AxisParallel.Continuous.nonColumnVerticalPlates K B))
    (hNoColumns :
      Tiling.AxisParallel.Continuous.verticalColumnCentres K A = ∅ ↔
        Tiling.AxisParallel.Continuous.verticalColumnCentres K B = ∅)
    {P : Tiling.AxisParallel.Continuous.VerticalPlate K A}
    (hP : ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P)
    (hfull : P.centres = A) :
    ∃ Q : Tiling.AxisParallel.Continuous.VerticalPlate K B,
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn Q ∧ Q.centres = B := by
  let P' : ↑(Tiling.AxisParallel.Continuous.nonColumnVerticalPlates K A) := ⟨P, hP⟩
  let Q' := e P'
  have hAEmpty := verticalColumnCentres_eq_empty_of_fullNonColumnPlate hP hfull
  have hBEmpty := hNoColumns.mp hAEmpty
  refine ⟨Q'.1, Q'.2, Set.Subset.antisymm
    (verticalPlate_centres_subset Q'.1) ?_⟩
  intro x hxB
  let x' : B := ⟨x, hxB⟩
  let R := Tiling.AxisParallel.Continuous.VerticalPlate.ofCentre (K := K) x'
  have hR : ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn R :=
    not_isVerticalColumn_of_columnCentres_eq_empty hBEmpty R
  let R' : ↑(Tiling.AxisParallel.Continuous.nonColumnVerticalPlates K B) := ⟨R, hR⟩
  let U' := e.symm R'
  obtain ⟨u, huU⟩ := verticalPlate_centres_nonempty U'.1
  have huA : u ∈ A := verticalPlate_centres_subset U'.1 huU
  have huP : u ∈ P.centres := by rwa [hfull]
  have hUP : U'.1 = P := verticalPlate_eq_of_common_centre huU huP
  have hUP' : U' = P' := Subtype.ext hUP
  have hR'Q' : R' = Q' := by
    calc
      R' = e (e.symm R') := (e.apply_symm_apply R').symm
      _ = e P' := congrArg e hUP'
      _ = Q' := rfl
  have hRQ : R = Q'.1 := congrArg Subtype.val hR'Q'
  rw [← hRQ]
  exact Tiling.AxisParallel.Continuous.VerticalPlate.mem_centres_ofCentre x'

theorem AlignedEarthquakeLimitData.allColumns_iff
    {K : Tiling.AxisParallel.Region}
    {T S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ}
    {beta : ℝ}
    {g : ℕ → Tiling.AxisParallel.aePeriodGroup
      (Set.univ : Set Tiling.Plane)}
    (D : Tiling.AxisParallel.Structure.AlignedEarthquakeLimitData T S beta g) :
    (T.centres : Set Tiling.Plane) =
        Tiling.AxisParallel.Continuous.verticalColumnCentres K
          (T.centres : Set Tiling.Plane) ↔
      (S.centres : Set Tiling.Plane) =
        Tiling.AxisParallel.Continuous.verticalColumnCentres K
          (S.centres : Set Tiling.Plane) := by
  rw [allCentres_iff_noNonColumnPlate,
    allCentres_iff_noNonColumnPlate]
  exact not_congr D.plateEquiv.nonempty_congr

theorem AlignedEarthquakeLimitData.noColumns_iff
    {K : Tiling.AxisParallel.Region}
    {T S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ}
    {beta : ℝ}
    {g : ℕ → Tiling.AxisParallel.aePeriodGroup
      (Set.univ : Set Tiling.Plane)}
    (D : Tiling.AxisParallel.Structure.AlignedEarthquakeLimitData T S beta g) :
    Tiling.AxisParallel.Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane) = ∅ ↔
      Tiling.AxisParallel.Continuous.verticalColumnCentres K
        (S.centres : Set Tiling.Plane) = ∅ := by
  rw [← D.columnLimit_eq]
  rw [← regularSupport_eq_empty_iff K D.columnLimit,
    D.columnSupport_eq,
    regularSupport_eq_empty_iff]

theorem AlignedEarthquakeLimitData.trivialDecomposition_iff
    {K : Tiling.AxisParallel.Region}
    {T S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ}
    {beta : ℝ}
    {g : ℕ → Tiling.AxisParallel.aePeriodGroup
      (Set.univ : Set Tiling.Plane)}
    (D : Tiling.AxisParallel.Structure.AlignedEarthquakeLimitData T S beta g) :
    (∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K
        (T.centres : Set Tiling.Plane),
        ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧
          P.centres = (T.centres : Set Tiling.Plane)) ↔
      ∃ Q : Tiling.AxisParallel.Continuous.VerticalPlate K
          (S.centres : Set Tiling.Plane),
        ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn Q ∧
          Q.centres = (S.centres : Set Tiling.Plane) := by
  constructor
  · rintro ⟨P, hP, hfull⟩
    exact fullNonColumnPlate_of_equiv D.plateEquiv D.noColumns_iff hP hfull
  · rintro ⟨Q, hQ, hfull⟩
    exact fullNonColumnPlate_of_equiv D.plateEquiv.symm D.noColumns_iff.symm hQ hfull

theorem AlignedEarthquakeLimitData.nontrivial
    {K : Tiling.AxisParallel.Region}
    {T S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ}
    {beta : ℝ}
    {g : ℕ → Tiling.AxisParallel.aePeriodGroup
      (Set.univ : Set Tiling.Plane)}
    (D : Tiling.AxisParallel.Structure.AlignedEarthquakeLimitData T S beta g)
    (hT : ¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K
        (T.centres : Set Tiling.Plane),
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧
        P.centres = (T.centres : Set Tiling.Plane)) :
    ¬ ∃ Q : Tiling.AxisParallel.Continuous.VerticalPlate K
        (S.centres : Set Tiling.Plane),
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn Q ∧
        Q.centres = (S.centres : Set Tiling.Plane) := by
  exact fun hS ↦ hT (D.trivialDecomposition_iff.mpr hS)

theorem exists_alignedEarthquakeLimitData :
    ∀ {K : Region} (T S : TilingSpace K Set.univ)
      (_hminimal : IsTopologicallyMinimal (orbitHull T))
      (_hFHC : Continuous.HasFiniteHorizontalComplexity (T.centres : Set Tiling.Plane))
      {beta : ℝ} (_hbeta : 0 < beta)
      (_hcolumnPeriod : Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (Continuous.verticalColumnCentres K
          (T.centres : Set Tiling.Plane))) ((beta : ℝ) : ℂ))
      (_hplatePeriod : ∀ P : Continuous.VerticalPlate K
          (T.centres : Set Tiling.Plane),
        ¬ Continuous.IsVerticalColumn P →
          Tiling.RationalPolygonal.SetPeriodicBy P.support ((beta : ℝ) : ℂ))
      (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
      (_haligned : ∀ n, ∃ m : ℤ,
        (g n : Tiling.Plane).re = (m : ℝ) * beta)
      (_hconverges : LocallyFellConverges
        (TilingSpace.centresSequence
          (TilingSpace.translateSequence g T)) (S.centres : Set Tiling.Plane)),
      Nonempty (AlignedEarthquakeLimitData T S beta g) := by
  intro K T S hminimal hFHC beta hbeta hcolumnPeriod hplatePeriod g haligned hconverges
  obtain ⟨D⟩ := exists_finitePlateColourLimitData T S hbeta hcolumnPeriod
    hplatePeriod g haligned hconverges
  have hcolumn := columnLimit_eq_verticalColumnCentres T S hminimal hFHC
    hbeta hcolumnPeriod g D haligned
  obtain ⟨hpartition, hnonempty⟩ := targetPlateBlocks_partition D hcolumn
  have hsourceTarget := source_card_le_target_of_blocks D hpartition hnonempty
  have htargetSource := target_card_le_source_of_reverseAlignedLimit T S g D
    hminimal hFHC hcolumn
  have hcard : Set.ncard (Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane)) =
      Set.ncard (Continuous.nonColumnVerticalPlates K
        (S.centres : Set Tiling.Plane)) :=
    Nat.le_antisymm hsourceTarget htargetSource
  obtain ⟨e, he⟩ := exists_plateEquiv_of_singletonBlocks D hcolumn hcard
  obtain ⟨hS, hHullS, hminimalS, hFHC_S⟩ :=
    alignedLimit_dynamicalFacts T S hminimal hFHC
      (fun n => g (D.subsequence n)) D.ambient_converges
  have htargetColumnPeriod :
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (Continuous.verticalColumnCentres K
          (S.centres : Set Tiling.Plane))) ((beta : ℝ) : ℂ) := by
    rw [← hcolumn, D.columnSupport_eq]
    exact hcolumnPeriod
  have htargetPlatePeriod : ∀ Q : Continuous.VerticalPlate K
      (S.centres : Set Tiling.Plane),
      ¬ Continuous.IsVerticalColumn Q →
        Tiling.RationalPolygonal.SetPeriodicBy Q.support ((beta : ℝ) : ℂ) := by
    intro Q hQ
    obtain ⟨P, hP⟩ := e.surjective ⟨Q, hQ⟩
    have hsupport : Q.support = P.1.support := by
      have hEq : (e P).1 = Q := congrArg Subtype.val hP
      calc
        Q.support = (e P).1.support :=
          (congrArg (fun R : Continuous.VerticalPlate K
            (S.centres : Set Tiling.Plane) => R.support) hEq).symm
        _ = regularSupport K (D.nonColumnLimit P) := by
          rw [(e P).1.support_eq_regularSupport, ← he P]
        _ = P.1.support := D.nonColumnSupport_eq P
    rw [hsupport]
    exact hplatePeriod P.1 P.2
  have hbaseColumn :
      Complex.re '' regularSupport K D.columnLimit =
        Complex.re '' regularSupport K
          (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane)) := by
    exact congrArg (fun A : Set Tiling.Plane => Complex.re '' A) D.columnSupport_eq
  have hbaseNonColumn : ∀ P, (e P).1.base = P.1.base := by
    intro P
    have hsupport : (e P).1.support = P.1.support := by
      calc
        (e P).1.support = regularSupport K (D.nonColumnLimit P) := by
          rw [(e P).1.support_eq_regularSupport, ← he P]
        _ = P.1.support := D.nonColumnSupport_eq P
    rw [(e P).1.base_eq, P.1.base_eq, hsupport]
  refine ⟨{
    subsequence := D.subsequence
    subsequence_strictMono := D.subsequence_strictMono
    ambient_converges := D.ambient_converges
    sourceNonColumn_finite := D.sourceNonColumn_finite
    targetNonColumn_finite := D.targetNonColumn_finite
    columnLimit := D.columnLimit
    nonColumnLimit := D.nonColumnLimit
    column_converges := D.column_converges
    nonColumn_converges := D.nonColumn_converges
    coloured_union := D.coloured_union
    coloured_pairwiseDisjoint := D.coloured_pairwiseDisjoint
    column_disjoint_nonColumn := D.column_disjoint_nonColumn
    columnLimit_eq := hcolumn
    plateEquiv := e
    nonColumnLimit_eq := he
    columnSupport_eq := D.columnSupport_eq
    columnBase_eq := hbaseColumn
    nonColumnSupport_eq := D.nonColumnSupport_eq
    nonColumnBase_eq := hbaseNonColumn
    targetFiniteHorizontalComplexity := hFHC_S
    limit_mem_orbitHull := hS
    limit_orbitHull_eq := hHullS
    limit_minimal := hminimalS
    targetColumnSupport_periodic := htargetColumnPeriod
    targetNonColumnSupport_periodic := htargetPlatePeriod
  }⟩

end Tiling.AxisParallel.Structure
