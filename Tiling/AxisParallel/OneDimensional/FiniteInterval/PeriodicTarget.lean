import Tiling.AxisParallel.OneDimensional.FiniteInterval.WholeLine
import Tiling.AxisParallel.OneDimensional.FiniteInterval.TargetGeometry

/-!
# Periodicity for measurable targets

Finite-interval tilings of a periodic target have periodic centre sets.
For a nonempty proper regularized target, its periods are commensurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped Pointwise Topology
noncomputable section

namespace Tiling.AxisParallel.OneDimensional.FiniteInterval
open Tiling.AxisParallel.OneDimensional


/-- An adjacent global endpoint gap is either crossed by one tile or is one genuine target gap. -/
theorem consecutive_translatedEndpoint_gap_on_regularTarget
    {B H R : Set ℝ} (P : IntervalPresentation B)
    (hTile : LineTilesOn B H R) (hBpositive : 0 < (volume B).toReal)
    (hRopen : IsOpen R) (hRregular : interior (closure R) = R)
    {x y : ℝ} (hxy : ConsecutiveIn (translatedEndpointSet P H) x y) :
    y - x ∈ P.gapLengths ∪ targetGapLengths R := by
  let z : ℝ := (x + y) / 2
  have hzIoo : z ∈ Ioo x y := by
    dsimp [z]
    constructor <;> linarith [hxy.2.2.1]
  have hclosed := LineTilesOn.lineClosedUnion_eq_closure_target P hTile hBpositive
    hRopen hRregular
  by_cases hz : z ∈ lineClosedUnion B H
  · left
    rw [lineClosedUnion, Set.mem_iUnion] at hz
    obtain ⟨⟨l, hl⟩, hzl⟩ := hz
    exact consecutive_translatedEndpoint_gap_of_covered_midpoint P hTile.2.2.2.1
      hxy ⟨l, hl, hzl⟩
  · right
    have hgap : Ioo x y ⊆ (closure R)ᶜ := by
      intro w hw hwR
      rw [← hclosed, lineClosedUnion, Set.mem_iUnion] at hwR
      obtain ⟨⟨l, hl⟩, hwl⟩ := hwR
      have hwb : w - l ∈ closure B := by
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg,
          add_comm] using hwl
      have hwbOpen : w - l ∈ B := by
        by_contra hn
        have he : w - l ∈ P.endpoints :=
          P.closure_diff_subset_endpoints ⟨hwb, hn⟩
        have hwE : w ∈ translatedEndpointSet P H :=
          (mem_translatedEndpointSet_iff P).2 ⟨l, hl, w - l, he, by ring⟩
        exact (Set.disjoint_left.1 hxy.2.2.2 hwE hw)
      rw [P.union_eq, Set.mem_iUnion] at hwbOpen
      obtain ⟨i, hwi⟩ := hwbOpen
      have hleftE : l + P.left i ∈ translatedEndpointSet P H :=
        (mem_translatedEndpointSet_iff P).2 ⟨l, hl, P.left i, by
          simp [IntervalPresentation.endpoints], rfl⟩
      have hrightE : l + P.right i ∈ translatedEndpointSet P H :=
        (mem_translatedEndpointSet_iff P).2 ⟨l, hl, P.right i, by
          simp [IntervalPresentation.endpoints], rfl⟩
      have hleft : l + P.left i ≤ x := by
        by_contra hn
        have : l + P.left i ∈ Ioo x y := by
          constructor
          · exact lt_of_not_ge hn
          · linarith [hwi.1, hw.2]
        exact Set.disjoint_left.1 hxy.2.2.2 hleftE this
      have hright : y ≤ l + P.right i := by
        by_contra hn
        have : l + P.right i ∈ Ioo x y := by
          constructor
          · linarith [hw.1, hwi.2]
          · exact lt_of_not_ge hn
        exact Set.disjoint_left.1 hxy.2.2.2 hrightE this
      apply hz
      rw [lineClosedUnion, Set.mem_iUnion]
      refine ⟨⟨l, hl⟩, ?_⟩
      have hzclosed : z - l ∈ Set.Icc (P.left i) (P.right i) := by
        constructor <;> linarith [hzIoo.1, hzIoo.2]
      have : z - l ∈ closure B := by
        rw [P.closure_eq_iUnion_Icc, Set.mem_iUnion]
        exact ⟨i, hzclosed⟩
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg,
        add_comm] using this
    have hxclosure := LineTilesOn.translatedEndpointSet_subset_closure_target P hTile
      hBpositive hRopen hRregular hxy.1
    have hyclosure := LineTilesOn.translatedEndpointSet_subset_closure_target P hTile
      hBpositive hRopen hRregular hxy.2.1
    have hxnot : x ∉ R := by
      intro hxR
      obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hRopen.mem_nhds hxR)
      let u := (x + min b y) / 2
      have hxmin : x < min b y := lt_min hxb hxy.2.2.1
      have huI : u ∈ Ioo x y := by
        dsimp [u]
        constructor <;> linarith [min_le_right b y, hxmin]
      have huR : u ∈ R := hab ⟨by dsimp [u]; linarith [hax, hxmin],
        by dsimp [u]; linarith [min_le_left b y, hxb]⟩
      exact hgap huI (subset_closure huR)
    have hynot : y ∉ R := by
      intro hyR
      obtain ⟨a, b, ⟨hay, hyb⟩, hab⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hRopen.mem_nhds hyR)
      let u := (max a x + y) / 2
      have hmaxy : max a x < y := max_lt hay hxy.2.2.1
      have huI : u ∈ Ioo x y := by
        dsimp [u]
        constructor <;> linarith [le_max_right a x, hmaxy]
      have huR : u ∈ R := hab ⟨by dsimp [u]; linarith [le_max_left a x, hay],
        by dsimp [u]; linarith [hmaxy, hyb]⟩
      exact hgap huI (subset_closure huR)
    have hxfront : x ∈ frontier R := by
      rw [frontier, hRopen.interior_eq]
      exact ⟨hxclosure, hxnot⟩
    have hyfront : y ∈ frontier R := by
      rw [frontier, hRopen.interior_eq]
      exact ⟨hyclosure, hynot⟩
    exact ⟨x, y, hxfront, hyfront, hxy.2.2.1, hgap, rfl⟩

/-- Centre candidates in the rigidity window are uniform over all tilings of this fixed target. -/
theorem finite_centerCandidates_on_properPeriodicTarget
    {B R : Set ℝ} (P : IntervalPresentation B)
    (hBpositive : 0 < (volume B).toReal)
    (hRnonempty : R.Nonempty) (hRopen : IsOpen R)
    (hRregular : interior (closure R) = R) (hRproper : R ≠ Set.univ)
    {p : ℝ} (hp : 0 < p) (hperiod : p +ᵥ R = R)
    (hfrontierLocal : ∀ C : Set ℝ, IsCompact C → (C ∩ frontier R).Finite)
    (radius : ℝ) (hradius : 0 ≤ radius) :
    ∃ c : ℝ, ∃ F : Finset ℝ, ∀ H : Set ℝ, LineTilesOn B H R →
      H ∩ Icc (c - radius) (c + radius) ⊆ (F : Set ℝ) := by
  obtain ⟨x0, hx0⟩ :=
    frontier_nonempty_of_nonempty_proper_regularOpen hRnonempty hRopen hRregular hRproper
  have hBnonempty : B.Nonempty := by
    by_contra hn
    simp only [not_nonempty_iff_eq_empty] at hn
    rw [hn, measure_empty, ENNReal.toReal_zero] at hBpositive
    exact lt_irrefl 0 hBpositive
  obtain ⟨e0, he0⟩ := P.endpoints_nonempty hBnonempty
  let A : Set ℝ := P.gapLengths ∪ targetGapLengths R
  have hAfinite : A.Finite :=
    P.gapLengths_finite.union (targetGapLengths_finite hp hperiod hfrontierLocal)
  have hApositive : ∀ d ∈ A, 0 < d := by
    intro d hd
    rcases hd with hd | hd
    · exact P.gapLengths_pos hd
    · exact targetGapLengths_pos hd
  obtain ⟨FE, hFE⟩ := finite_candidates_of_gapAlphabet hAfinite hApositive
    x0 radius hradius
  refine ⟨x0 - e0, FE.image (fun z => z - e0), ?_⟩
  intro H hTile h hh
  have hHlocal := finiteInterval_lineTilesOn_centres_locallyFinite
    P.isFiniteIntervalRegion hBpositive hTile
  have hElocal := translatedEndpointSet_boundedWindowFinite P hHlocal
  have hx0E := LineTilesOn.frontier_target_subset_translatedEndpointSet P hTile
    hBpositive hRopen hRregular hx0
  have hEwindow : h + e0 ∈ translatedEndpointSet P H ∩ Icc (x0 - radius) (x0 + radius) := by
    refine ⟨(mem_translatedEndpointSet_iff P).2 ⟨h, hh.1, e0, he0, rfl⟩, ?_⟩
    constructor <;> linarith [hh.2.1, hh.2.2]
  have hmem := hFE (translatedEndpointSet P H) hElocal hx0E
    (fun x y hxy => consecutive_translatedEndpoint_gap_on_regularTarget P hTile
      hBpositive hRopen hRregular hxy)
    hEwindow
  rw [Finset.mem_coe, Finset.mem_image]
  exact ⟨h + e0, hmem, by ring⟩

/-- A positive finite-interval tile has finitely many literal tilings of a fixed proper target. -/
theorem finite_lineTilingsOn_properPeriodicTarget
    {B R : Set ℝ} (P : IntervalPresentation B)
    (hBpositive : 0 < (volume B).toReal) (hRnonempty : R.Nonempty)
    (hRopen : IsOpen R) (hRregular : interior (closure R) = R)
    (hRproper : R ≠ Set.univ) {p : ℝ} (hp : 0 < p) (hperiod : p +ᵥ R = R)
    (hfrontierLocal : ∀ C : Set ℝ, IsCompact C → (C ∩ frontier R).Finite) :
    {H : Set ℝ | LineTilesOn B H R}.Finite := by
  obtain ⟨radius, hradius, hrigid⟩ :=
    finiteInterval_lineTilingsOn_localRigidity P.isFiniteIntervalRegion hBpositive
  obtain ⟨c, F, hF⟩ := finite_centerCandidates_on_properPeriodicTarget P hBpositive hRnonempty
    hRopen hRregular hRproper hp hperiod hfrontierLocal radius hradius.le
  let A : Set (Set ℝ) := {H : Set ℝ | LineTilesOn B H R}
  let restrict : Set ℝ → Set ℝ := fun H => H ∩ Icc (c - radius) (c + radius)
  have himage : (restrict '' A).Finite := by
    apply (F.finite_toSet.finite_subsets).subset
    rintro S ⟨H, hHA, rfl⟩
    exact hF H hHA
  apply Set.Finite.of_finite_image himage
  intro H hHA H' hH'A heq
  exact hrigid H H' R c hHA hH'A heq

/-- Some positive integer multiple of the target period fixes each literal centre set. -/
theorem exists_nsmul_targetPeriod_vadd_centres_eq
    {B H R : Set ℝ} (P : IntervalPresentation B) (hTile : LineTilesOn B H R)
    (hBpositive : 0 < (volume B).toReal) (hRnonempty : R.Nonempty)
    (hRopen : IsOpen R) (hRregular : interior (closure R) = R)
    (hRproper : R ≠ Set.univ) {p : ℝ} (hp : 0 < p) (hperiod : p +ᵥ R = R)
    (hfrontierLocal : ∀ C : Set ℝ, IsCompact C → (C ∩ frontier R).Finite) :
    ∃ n : ℕ, 0 < n ∧ ((n : ℝ) * p) +ᵥ H = H := by
  have hfinite := finite_lineTilingsOn_properPeriodicTarget P hBpositive hRnonempty
    hRopen hRregular hRproper hp hperiod hfrontierLocal
  obtain ⟨n, hn, _, hfix⟩ :=
    Tiling.AxisParallel.Foundations.lineTilesOn_periodic_of_finiteOrbit
      hp hperiod.symm.eventuallyEq hfinite hTile
  exact ⟨n, hn, hfix⟩

private theorem pt_regularizedTarget_vadd_centres (B H : Set ℝ) (q : ℝ) :
    regularizedTarget B (q +ᵥ H) = q +ᵥ regularizedTarget B H := by
  have hopen : lineOpenUnion B (q +ᵥ H) = q +ᵥ lineOpenUnion B H := by
    ext x
    constructor
    · intro hx
      rw [lineOpenUnion, Set.mem_iUnion] at hx
      obtain ⟨k, hxk⟩ := hx
      obtain ⟨h, hh, hkh⟩ := k.property
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      rw [lineOpenUnion, Set.mem_iUnion]
      refine ⟨⟨h, hh⟩, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxk
      rw [← hkh] at hxk
      convert hxk using 1
      simp only [vadd_eq_add]
      ring
    · intro hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
      rw [lineOpenUnion, Set.mem_iUnion] at hx ⊢
      obtain ⟨⟨h, hh⟩, hxh⟩ := hx
      refine ⟨⟨q + h, ⟨h, hh, rfl⟩⟩, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxh
      convert hxh using 1
      simp only [vadd_eq_add]
      ring
  unfold regularizedTarget
  rw [hopen, closure_vadd, interior_vadd]

/-- Regularizing a measurable periodic target produces the full or periodic-centre case. -/
theorem lineTilesOn_measurableTarget_full_or_periodic
    {B H X : Set ℝ} (P : IntervalPresentation B) (hTile : LineTilesOn B H X)
    (hBpositive : 0 < (volume B).toReal) {p : ℝ} (hp : 0 < p)
    (hXperiod : p +ᵥ X =ᵐ[volume] X) :
    (regularizedTarget B H = Set.univ ∧ LineTiles B H) ∨
      (regularizedTarget B H ≠ Set.univ ∧
        ∃ n : ℕ, 0 < n ∧ ((n : ℝ) * p) +ᵥ H = H) := by
  let R := regularizedTarget B H
  obtain ⟨hRopen, hRregular, _, _, hTileR, hfrontierLocal⟩ :=
    LineTilesOn.regularizedTarget P hTile hBpositive
  have hRperiod : p +ᵥ R = R :=
    LineTilesOn.regularizedTarget_periodic_of_target_ae P hTile hBpositive hXperiod
  by_cases hfull : R = Set.univ
  · left
    refine ⟨hfull, ?_⟩
    change LineTilesOn B H R at hTileR
    rw [hfull] at hTileR
    exact hTileR
  · right
    refine ⟨hfull, ?_⟩
    by_cases hH : H.Nonempty
    · have hBnonempty : B.Nonempty := by
        by_contra hn
        simp only [not_nonempty_iff_eq_empty] at hn
        rw [hn, measure_empty, ENNReal.toReal_zero] at hBpositive
        exact lt_irrefl 0 hBpositive
      obtain ⟨h, hh⟩ := hH
      obtain ⟨b, hb⟩ := hBnonempty
      have hRnonempty : R.Nonempty := by
        refine ⟨h + b, ?_⟩
        apply lineOpenUnion_subset_regularizedTarget P
        rw [lineOpenUnion, Set.mem_iUnion]
        exact ⟨⟨h, hh⟩, ⟨b, hb, by simp⟩⟩
      exact exists_nsmul_targetPeriod_vadd_centres_eq P hTileR hBpositive hRnonempty
        hRopen hRregular hfull hp hRperiod hfrontierLocal
    · have hHempty : H = ∅ := not_nonempty_iff_eq_empty.mp hH
      refine ⟨1, by omega, ?_⟩
      simp [hHempty]

/-- A finite-interval tiling of a positive-periodic target has a positive centre period. -/
theorem periodicTarget_lineTiling_finiteIntervals
    {B H X : Set ℝ} (hB : IsFiniteIntervalRegion B)
    (hBpositive : 0 < (volume B).toReal) (hTile : LineTilesOn B H X)
    {p : ℝ} (hp : 0 < p) (hXperiod : p +ᵥ X =ᵐ[volume] X) :
    ∃ q : ℝ, 0 < q ∧ q +ᵥ H = H := by
  let P := IntervalPresentation.ofIsFiniteIntervalRegion hB
  rcases lineTilesOn_measurableTarget_full_or_periodic P hTile hBpositive hp hXperiod with
    hfull | hproper
  · exact exists_positiveLinePeriod hB hBpositive hfull.2
  · obtain ⟨n, hn, hfix⟩ := hproper.2
    refine ⟨(n : ℝ) * p, mul_pos (by exact_mod_cast hn) hp, hfix⟩

/-- Positive periods of a nonempty proper regular-open set are rationally commensurable. -/
theorem properPeriodicTarget_periods_commensurable
    {R : Set ℝ}
    (hRnonempty : R.Nonempty) (hRopen : IsOpen R)
    (hRregular : interior (closure R) = R) (hRproper : R ≠ Set.univ)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpperiod : p +ᵥ R = R) (hqperiod : q +ᵥ R = R)
    (hfrontierLocal : ∀ C : Set ℝ, IsCompact C → (C ∩ frontier R).Finite) :
    ∃ r : ℚ, p = (r : ℝ) * q := by
  have hfinite : (frontier R ∩ Ico 0 p).Finite := by
    apply (hfrontierLocal (Icc 0 p) isCompact_Icc).subset
    intro x hx
    exact ⟨⟨hx.2.1, hx.2.2.le⟩, hx.1⟩
  have hne := frontier_nonempty_of_nonempty_proper_regularOpen
    hRnonempty hRopen hRregular hRproper
  exact periods_commensurable_of_finite_frontier_residues hp hq hpperiod
    hqperiod hfinite hne

/-- A target period and centre period are commensurable under properness witnessed by mass. -/
theorem properPeriodicTarget_periods_commensurable_finiteIntervals
    {B H X : Set ℝ} (hB : IsFiniteIntervalRegion B)
    (hBpositive : 0 < (volume B).toReal) (hTile : LineTilesOn B H X)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hXperiod : p +ᵥ X =ᵐ[volume] X) (hHperiod : q +ᵥ H = H)
    (hXcell : 0 < (volume (X ∩ Ico 0 p)).toReal)
    (hXcomplement : ∃ I : Set ℝ, Bornology.IsBounded I ∧
      0 < (volume (I \ X)).toReal) : ∃ r : ℚ, p = (r : ℝ) * q := by
  let P := IntervalPresentation.ofIsFiniteIntervalRegion hB
  let R := regularizedTarget B H
  obtain ⟨hRopen, hRregular, _, hRX, hTileR, hfrontierLocal⟩ :=
    LineTilesOn.regularizedTarget P hTile hBpositive
  have hpR : p +ᵥ R = R :=
    LineTilesOn.regularizedTarget_periodic_of_target_ae P hTile hBpositive hXperiod
  have hRnonempty : R.Nonempty := by
    by_contra hne
    have hRempty : R = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hcellAE : (· ∈ R ∩ Ico 0 p) =ᵐ[volume] (· ∈ X ∩ Ico 0 p) := by
      filter_upwards [hRX] with x hx
      exact propext (and_congr (eq_iff_iff.mp hx) Iff.rfl)
    have hmeasure : volume (R ∩ Ico 0 p) = volume (X ∩ Ico 0 p) :=
      measure_congr hcellAE
    rw [hRempty, empty_inter, measure_empty] at hmeasure
    rw [← hmeasure, ENNReal.toReal_zero] at hXcell
    exact lt_irrefl 0 hXcell
  have hRproper : R ≠ Set.univ := by
    intro hfull
    obtain ⟨I, _, hIpositive⟩ := hXcomplement
    have hdiffAE : (· ∈ I \ R) =ᵐ[volume] (· ∈ I \ X) := by
      filter_upwards [hRX] with x hx
      exact propext (and_congr Iff.rfl (not_congr (eq_iff_iff.mp hx)))
    have hmeasure : volume (I \ R) = volume (I \ X) := measure_congr hdiffAE
    simp only [hfull, sdiff_univ, measure_empty] at hmeasure
    rw [← hmeasure, ENNReal.toReal_zero] at hIpositive
    exact lt_irrefl 0 hIpositive
  have hqR : q +ᵥ R = R := by
    change q +ᵥ regularizedTarget B H = regularizedTarget B H
    rw [← pt_regularizedTarget_vadd_centres]
    exact congrArg (regularizedTarget B) hHperiod
  exact properPeriodicTarget_periods_commensurable
    hRnonempty hRopen hRregular hRproper hp hq hpR hqR hfrontierLocal

end Tiling.AxisParallel.OneDimensional.FiniteInterval
