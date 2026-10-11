import Tiling.AxisParallel.Continuous.HorizontalComplexityCore
import Tiling.AxisParallel.Continuous.PlateCore
import Tiling.AxisParallel.Topology.HullCore
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.WeakTilingTopology
import Tiling.AxisParallel.OneDimensional.ColumnSlices
import Tiling.AxisParallel.OneDimensional.FiniteInterval.WholeLine
import Mathlib.Data.Nat.Nth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Filter Function MeasureTheory Set
open scoped Pointwise
noncomputable section

namespace Tiling.AxisParallel.Structure

open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous


private theorem locallyFellConverges_eventually_exists_mem_ball
    {E : Type*} [PseudoMetricSpace E] [T2Space E] [LocallyCompactSpace E]
    {A : ℕ → Set E} {L : Set E}
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges A L)
    {x : E} (hx : x ∈ L) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ y ∈ A n, dist y x < epsilon := by
  rcases hconv with ⟨hA, hL, hconv⟩
  let U : Set (OnePoint E) :=
    (fun y : E ↦ (y : OnePoint E)) '' Metric.ball x epsilon
  have hUopen : IsOpen U :=
    OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball
  let V : Set (TopologicalSpace.NonemptyCompacts (OnePoint E)) :=
    {K | ((K : Set (OnePoint E)) ∩ U).Nonempty}
  have hVopen : IsOpen V :=
    TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hUopen
  have hlimit : Tiling.AxisParallel.Topology.fellCompactification L hL ∈ V := by
    refine ⟨(x : OnePoint E), ?_, ⟨x, ?_, rfl⟩⟩
    · simp [Tiling.Topology.fellCompactification, hx]
    · exact Metric.mem_ball_self hepsilon
  filter_upwards [hconv (hVopen.mem_nhds hlimit)] with n hn
  rcases hn with ⟨w, hwK, hwU⟩
  rcases hwU with ⟨y, hyball, rfl⟩
  refine ⟨y, ?_, Metric.mem_ball.mp hyball⟩
  simpa [Tiling.Topology.fellCompactification] using hwK

private theorem abs_re_sub_le_dist (x y : Tiling.Plane) :
    |x.re - y.re| ≤ dist x y := by
  rw [Complex.dist_eq]
  simpa only [Complex.sub_re] using Complex.abs_re_le_norm (x - y)

theorem horizontalDifference_of_translateLimit
    {K : Tiling.AxisParallel.Region}
    (T S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ)
    (hT : Tiling.AxisParallel.Continuous.HasFiniteHorizontalComplexity
      (T.centres : Set Tiling.Plane))
    (g : ℕ → Tiling.AxisParallel.aePeriodGroup (Set.univ : Set Tiling.Plane))
    (hconverges : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
        (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T))
      (S.centres : Set Tiling.Plane))
    {s t : Tiling.Plane}
    (hs : s ∈ (S.centres : Set Tiling.Plane))
    (ht : t ∈ (S.centres : Set Tiling.Plane)) :
    ∃ u ∈ (T.centres : Set Tiling.Plane),
      ∃ v ∈ (T.centres : Set Tiling.Plane),
      (t - s).re = (v - u).re := by
  let Z : Set ℝ :=
    Tiling.AxisParallel.Continuous.horizontalCentreProjection
      (T.centres : Set Tiling.Plane)
  let d : ℝ := (t - s).re
  let R : ℝ := |d| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hTZ : Tiling.AxisParallel.HasFLC Z := by
    simpa [Z, Tiling.AxisParallel.Continuous.HasFiniteHorizontalComplexity] using hT
  let F : Set ℝ := (Z - Z) ∩ Metric.closedBall 0 R
  have hFfinite : F.Finite := hTZ.2 R hR
  have hdClosure : d ∈ closure F := by
    rw [Metric.mem_closure_iff]
    intro epsilon hepsilon
    let eta : ℝ := min (epsilon / 4) (1 / 4)
    have heta : 0 < eta := by
      dsimp [eta]
      exact lt_min (by positivity) (by norm_num)
    have hetaEpsilon : 2 * eta < epsilon := by
      have := min_le_left (epsilon / 4) (1 / 4)
      dsimp [eta]
      linarith
    have hetaOne : 2 * eta < 1 := by
      have := min_le_right (epsilon / 4) (1 / 4)
      dsimp [eta]
      linarith
    have hsEventually := locallyFellConverges_eventually_exists_mem_ball
      hconverges hs heta
    have htEventually := locallyFellConverges_eventually_exists_mem_ball
      hconverges ht heta
    obtain ⟨n, ⟨s', hs'n, hs'dist⟩, ⟨t', ht'n, ht'dist⟩⟩ :=
      (hsEventually.and htEventually).exists
    change s' ∈
      ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
        Set Tiling.Plane) at hs'n
    change t' ∈
      ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
        Set Tiling.Plane) at ht'n
    change s' ∈ (fun x : Tiling.Plane ↦ x + (g n : Tiling.Plane)) ''
      (T.centres : Set Tiling.Plane) at hs'n
    change t' ∈ (fun x : Tiling.Plane ↦ x + (g n : Tiling.Plane)) ''
      (T.centres : Set Tiling.Plane) at ht'n
    rcases hs'n with ⟨u, hu, rfl⟩
    rcases ht'n with ⟨v, hv, rfl⟩
    let e : ℝ := (v - u).re
    have heq : e =
      ((v + (g n : Tiling.Plane)).re -
          (u + (g n : Tiling.Plane)).re) := by
      dsimp [e]
      ring
    have hsre :
        |(u + (g n : Tiling.Plane)).re - s.re| < eta :=
      (abs_re_sub_le_dist _ _).trans_lt hs'dist
    have htre :
        |(v + (g n : Tiling.Plane)).re - t.re| < eta :=
      (abs_re_sub_le_dist _ _).trans_lt ht'dist
    have hed : |e - d| < 2 * eta := by
      rw [heq]
      dsimp [d]
      have htri := abs_sub_le
        ((v + (g n : Tiling.Plane)).re - t.re) 0
        ((u + (g n : Tiling.Plane)).re - s.re)
      rw [sub_zero, zero_sub, abs_neg] at htri
      calc
        |v.re + (g n : Tiling.Plane).re -
            (u.re + (g n : Tiling.Plane).re) - (t.re - s.re)| =
            |((v + (g n : Tiling.Plane)).re - t.re) -
              ((u + (g n : Tiling.Plane)).re - s.re)| := by
                congr 1
                simp only [Complex.add_re]
                ring
        _ ≤ |(v + (g n : Tiling.Plane)).re - t.re| +
            |(u + (g n : Tiling.Plane)).re - s.re| := htri
        _ < 2 * eta := by linarith
    refine ⟨e, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · refine ⟨v.re, ⟨v, hv, rfl⟩, u.re, ⟨u, hu, rfl⟩, ?_⟩
        dsimp [e]
      · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
        apply le_of_lt
        calc
          |e| ≤ |e - d| + |d| := by
            have := abs_sub_le e d 0
            simpa only [sub_zero, abs_zero] using this
          _ = |d| + |e - d| := add_comm _ _
          _ < |d| + 1 := by linarith [hed.trans hetaOne]
          _ = R := by rfl
    · rw [Real.dist_eq, abs_sub_comm]
      exact hed.trans hetaEpsilon
  have hdF : d ∈ F := hFfinite.isClosed.closure_eq ▸ hdClosure
  rcases hdF.1 with ⟨vr, ⟨v, hv, rfl⟩, ur, ⟨u, hu, rfl⟩, hd⟩
  refine ⟨u, hu, v, hv, ?_⟩
  dsimp [d] at hd
  simpa only [Complex.sub_re] using hd.symm

theorem finiteHorizontalComplexity_of_translateLimit
    {K : Tiling.AxisParallel.Region}
    (T S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ)
    (hT : Tiling.AxisParallel.Continuous.HasFiniteHorizontalComplexity
      (T.centres : Set Tiling.Plane))
    (g : ℕ → Tiling.AxisParallel.aePeriodGroup (Set.univ : Set Tiling.Plane))
    (hconverges : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
        (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T))
      (S.centres : Set Tiling.Plane)) :
    Tiling.AxisParallel.Continuous.HasFiniteHorizontalComplexity
      (S.centres : Set Tiling.Plane) := by
  change Tiling.AxisParallel.HasFLC
      (Tiling.AxisParallel.Continuous.horizontalCentreProjection
        (T.centres : Set Tiling.Plane)) at hT
  change Tiling.AxisParallel.HasFLC
    (Tiling.AxisParallel.Continuous.horizontalCentreProjection
      (S.centres : Set Tiling.Plane))
  let A : Set ℝ :=
    Tiling.AxisParallel.Continuous.horizontalCentreProjection
      (T.centres : Set Tiling.Plane)
  let B : Set ℝ :=
    Tiling.AxisParallel.Continuous.horizontalCentreProjection
      (S.centres : Set Tiling.Plane)
  have hA : Tiling.AxisParallel.HasFLC A := by simpa [A] using hT
  have hSnonempty : (S.centres : Set Tiling.Plane).Nonempty := by
    obtain ⟨x, hx⟩ := S.tilesOn.2.2.exists
    obtain ⟨s, _hs⟩ := hx.mp (Set.mem_univ x)
    exact ⟨s.1, s.2⟩
  obtain ⟨s₀, hs₀⟩ := hSnonempty
  have hLocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (B ∩ Q).Finite := by
    intro Q hQ
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hQ
    let R : ℝ := |r| + |s₀.re| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have hImage : ((fun x : ℝ ↦ x - s₀.re) '' (B ∩ Q)).Finite := by
      apply (hA.2 R hR).subset
      rintro d ⟨x, ⟨hxB, hxQ⟩, rfl⟩
      rcases hxB with ⟨t, ht, rfl⟩
      obtain ⟨u, hu, v, hv, huv⟩ :=
        horizontalDifference_of_translateLimit T S hT g hconverges hs₀ ht
      refine ⟨?_, ?_⟩
      · refine ⟨v.re, ⟨v, hv, rfl⟩, u.re, ⟨u, hu, rfl⟩, ?_⟩
        simpa only [Complex.sub_re] using huv.symm
      · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
        have htre : |t.re| ≤ r := by
          have := hr hxQ
          simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using this
        have htri : |t.re - s₀.re| ≤ |t.re| + |s₀.re| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le t.re 0 s₀.re)
        calc
          |t.re - s₀.re| ≤ |t.re| + |s₀.re| := htri
          _ ≤ |r| + |s₀.re| :=
            add_le_add (htre.trans (le_abs_self r)) le_rfl
          _ ≤ R := by dsimp [R]; linarith
    exact hImage.of_finite_image fun x _ y _ hxy ↦ by linarith
  have hDiff : ∀ R : ℝ, 0 < R →
      ((B - B) ∩ Metric.closedBall 0 R).Finite := by
    intro R hR
    apply (hA.2 R hR).subset
    intro d hd
    rcases hd.1 with ⟨tr, ⟨t, ht, rfl⟩, sr, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨u, hu, v, hv, huv⟩ :=
      horizontalDifference_of_translateLimit T S hT g hconverges hs ht
    refine ⟨?_, ?_⟩
    · refine ⟨v.re, ⟨v, hv, rfl⟩, u.re, ⟨u, hu, rfl⟩, ?_⟩
      simpa only [Complex.sub_re] using huv.symm
    · exact hd.2
  exact ⟨hLocal, hDiff⟩

/-- A common subsequence on which vertical columns have one normalized centre set and converge to
a column in the ambient Fell limit. -/
structure NormalizedVerticalColumnLimitData
    {K : Tiling.AxisParallel.Region}
    (T : ℕ → Tiling.AxisParallel.Topology.TilingSpace K Set.univ)
    (S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ)
    (C : (n : ℕ) →
      Tiling.AxisParallel.Continuous.VerticalPlate K
        ((T n).centres : Set Tiling.Plane))
    (anchor : ℕ → Tiling.Plane) (limitAnchor : Tiling.Plane) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  ambient_converges : Tiling.AxisParallel.Topology.LocallyFellConverges
    (fun n ↦ ((T (subsequence n)).centres : Set Tiling.Plane))
    (S.centres : Set Tiling.Plane)
  normalizedCentres : Set Tiling.Plane
  normalized_closed : IsClosed normalizedCentres
  normalized_nonempty : normalizedCentres.Nonempty
  zero_mem_normalized : 0 ∈ normalizedCentres
  normalized_on_verticalAxis :
    normalizedCentres ⊆ {z : Tiling.Plane | z.re = 0}
  normalized_isCenterColumn : Tiling.AxisParallel.IsCenterColumn
    Tiling.AxisParallel.Axis.vertical K normalizedCentres
  normalization_exact : ∀ n : ℕ,
    (-anchor (subsequence n)) +ᵥ
        (C (subsequence n)).centres = normalizedCentres
  limitPlate : Tiling.AxisParallel.Continuous.VerticalPlate K
    (S.centres : Set Tiling.Plane)
  limitPlate_isColumn :
    Tiling.AxisParallel.Continuous.IsVerticalColumn limitPlate
  limitAnchor_mem : limitAnchor ∈ limitPlate.centres
  column_converges : Tiling.AxisParallel.Topology.LocallyFellConverges
    (fun n ↦ (C (subsequence n)).centres) limitPlate.centres
  limitCentres_eq :
    limitPlate.centres = limitAnchor +ᵥ normalizedCentres



open Tiling.AxisParallel

private structure FixedGenericVerticalSectionData
    (K : Region) (C : ℕ → Set Tiling.Plane) (anchor : ℕ → Tiling.Plane) where
  r : ℝ
  r_generic : r ∉ K.vertexFinset.image Complex.re
  slice_nonempty :
    (OneDimensional.ColumnSlices.verticalSlice K r).Nonempty
  presentation : OneDimensional.FiniteInterval.IntervalPresentation
    (OneDimensional.ColumnSlices.verticalSlice K r)
  slice_volume_pos : 0 < (volume
    (OneDimensional.ColumnSlices.verticalSlice K r)).toReal
  lineTiles : ∀ n, OneDimensional.LineTiles
    (OneDimensional.ColumnSlices.verticalSlice K r)
    (Complex.im '' ((-anchor n) +ᵥ C n))
  zero_mem : ∀ n, 0 ∈ Complex.im '' ((-anchor n) +ᵥ C n)
  axial_reconstruction : ∀ n,
    (-anchor n) +ᵥ C n =
      {z : Tiling.Plane |
      z.re = 0 ∧ z.im ∈ Complex.im '' ((-anchor n) +ᵥ C n)}

private theorem exists_fixedGenericVerticalSectionData :
    ∀ {K : Region}
      (C : ℕ → Set Tiling.Plane)
      (_hC : ∀ n, IsCenterColumn Axis.vertical K (C n))
      (anchor : ℕ → Tiling.Plane)
      (_hanchor : ∀ n, anchor n ∈ C n),
      Nonempty (FixedGenericVerticalSectionData K C anchor) := by
  intro K C hC anchor hanchor
  obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
  change z ∈ K.openCarrier at hz
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (K.openCarrier_regularOpen.1.mem_nhds hz)
  let J : Set ℝ := Set.Ioo (z.re - ε / 2) (z.re + ε / 2)
  have hJinf : J.Infinite := by
    dsimp [J]
    exact Set.Ioo_infinite (by linarith)
  have hFfin : ((K.vertexFinset.image Complex.re : Finset ℝ) : Set ℝ).Finite :=
    (K.vertexFinset.image Complex.re).finite_toSet
  obtain ⟨r, hrJ, hrgen⟩ := (hJinf.sdiff hFfin).nonempty
  have hrabs : |r - z.re| < ε := by
    dsimp [J] at hrJ
    rw [abs_lt]
    constructor <;> linarith [hrJ.1, hrJ.2]
  let q : Tiling.Plane := (r : ℂ) + z.im * Complex.I
  have hqball : q ∈ Metric.ball z ε := by
    rw [Metric.mem_ball]
    rw [Complex.dist_eq]
    have hdiff : q - z = ((r - z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [q]
    rw [hdiff, Complex.norm_real]
    exact hrabs
  have hq : q ∈ K.openCarrier := hball hqball
  have hslice : (OneDimensional.ColumnSlices.verticalSlice K r).Nonempty := by
    change ∃ y : ℝ, ((r : ℂ) + (y : ℂ) * Complex.I) ∈ K.openCarrier
    exact ⟨z.im, by simpa [q] using hq⟩
  obtain ⟨hfinite, _hlocal⟩ :=
    Tiling.AxisParallel.Region.verticalSlice_finiteIntervals K hrgen
  let P := OneDimensional.FiniteInterval.IntervalPresentation.ofIsFiniteIntervalRegion hfinite
  have hvol := OneDimensional.ColumnSlices.finiteIntervalRegion_volume_toReal_pos hfinite hslice
  refine ⟨⟨r, hrgen, hslice, P, hvol, ?_, ?_, ?_⟩⟩
  · intro n
    let Cn := C n
    let Yn : Set ℝ := Complex.im '' ((-anchor n) +ᵥ Cn)
    obtain ⟨c, hc⟩ := (hC n).2.2.1
    have hshape : Cn = {w : Tiling.Plane | w.re = c ∧ w.im ∈ Complex.im '' Cn} := by
      ext w
      constructor
      · intro hw
        exact ⟨hc w hw, ⟨w, hw, rfl⟩⟩
      · rintro ⟨hwre, ⟨w', hw, hwim⟩⟩
        have hweq : w = w' := by
          apply Complex.ext
          · exact hwre.trans (by simpa [Axis.transverseCoord] using (hc w' hw).symm)
          · exact hwim.symm
        simpa [hweq] using hw
    have hshapeC :
        IsCenterColumn Axis.vertical K
          {w : Tiling.Plane | w.re = c ∧ w.im ∈ Complex.im '' Cn} := by
      rw [← hshape]
      exact hC n
    have hYnonempty : (Complex.im '' Cn).Nonempty := by
      obtain ⟨w, hw⟩ := (hC n).2.1
      exact ⟨w.im, ⟨w, hw, rfl⟩⟩
    have hlineOrig :=
      OneDimensional.ColumnSlices.genericSliceTilings_of_completeColumn
        hYnonempty hshapeC r hrgen hslice
    have hYeq :
        Yn = (-(anchor n).im) +ᵥ (Complex.im '' Cn) := by
      ext y
      constructor
      · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        refine ⟨v, hv, ?_⟩
        simp [vadd_eq_add]
      · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        rintro ⟨v, hv, hvy⟩
        refine ⟨(-anchor n) +ᵥ v, ⟨v, hv, rfl⟩, ?_⟩
        change -(anchor n).im + v.im = y
        have hvy' : v.im = (anchor n).im + y := by
          simpa only [vadd_eq_add, neg_neg] using hvy
        linarith
    change OneDimensional.LineTiles
      (OneDimensional.ColumnSlices.verticalSlice K r) Yn
    have hlineShift : OneDimensional.LineTiles
        (OneDimensional.ColumnSlices.verticalSlice K r)
        ((-(anchor n).im) +ᵥ (Complex.im '' Cn)) := by
      simpa [OneDimensional.LineTiles] using
        Foundations.lineTilesOn_translate hlineOrig (-(anchor n).im)
    rw [← hYeq] at hlineShift
    exact hlineShift
  · intro n
    refine ⟨(-anchor n) +ᵥ anchor n, ?_, ?_⟩
    · exact ⟨anchor n, hanchor n, rfl⟩
    · simp
  · intro n
    let D := (-anchor n) +ᵥ C n
    let Y := Complex.im '' D
    obtain ⟨c, hc⟩ := (hC n).2.2.1
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨?_, ⟨(-anchor n) +ᵥ v, ⟨v, hv, rfl⟩, rfl⟩⟩
      have ha : (anchor n).re = c := by
        simpa [Axis.transverseCoord] using hc (anchor n) (hanchor n)
      have hvre : v.re = c := by
        simpa [Axis.transverseCoord] using hc v hv
      change -(anchor n).re + v.re = 0
      linarith
    · rintro ⟨hwre, ⟨v, ⟨u, hu, rfl⟩, hv⟩⟩
      refine ⟨u, hu, ?_⟩
      apply Complex.ext
      · have ha : (anchor n).re = c := by
          simpa [Axis.transverseCoord] using hc (anchor n) (hanchor n)
        have hure : u.re = c := by
          simpa [Axis.transverseCoord] using hc u hu
        change -(anchor n).re + u.re = w.re
        linarith
      · simpa [vadd_eq_add] using hv

private theorem normalizedVerticalColumnCentres_finite :
    ∀ {K : Region}
      (C : ℕ → Set Tiling.Plane)
      (_hC : ∀ n, IsCenterColumn Axis.vertical K (C n))
      (anchor : ℕ → Tiling.Plane)
      (_hanchor : ∀ n, anchor n ∈ C n),
      Set.Finite (Set.range (fun n => (-anchor n) +ᵥ C n)) := by
  intro K C hC anchor hanchor
  obtain ⟨D⟩ := exists_fixedGenericVerticalSectionData C hC anchor hanchor
  let Y : ℕ → Set ℝ := fun n =>
    Complex.im '' ((-anchor n) +ᵥ C n)
  have hYfinite : (Set.range Y).Finite := by
    apply (OneDimensional.FiniteInterval.finite_normalizedCentreSets
      D.presentation.isFiniteIntervalRegion D.slice_volume_pos).subset
    rintro y ⟨n, rfl⟩
    exact ⟨D.lineTiles n, D.zero_mem n⟩
  let reconstruct : Set ℝ → Set Tiling.Plane := fun S =>
    {z : Tiling.Plane | z.re = 0 ∧ z.im ∈ S}
  have hsubset :
      Set.range (fun n => (-anchor n) +ᵥ C n) ⊆ reconstruct '' Set.range Y := by
    rintro A ⟨n, rfl⟩
    refine ⟨Y n, ⟨n, rfl⟩, ?_⟩
    simpa [reconstruct, Y] using (D.axial_reconstruction n).symm
  exact (hYfinite.image reconstruct).subset hsubset



open Tiling.AxisParallel

private theorem verticalPlate_isCenterColumn_of_isVerticalColumn
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : Continuous.VerticalPlate K T)
    (hcolumn : Continuous.IsVerticalColumn P) :
    IsCenterColumn Axis.vertical K P.centres := by
  exact Continuous.VerticalPlate.isCenterColumn_of_isVerticalColumn hTile P hcolumn

private theorem exists_strictMono_const_of_finite_range
    {alpha : Type} (f : Nat → alpha) (hfinite : Set.Finite (Set.range f)) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ ∀ n, f (phi n) = f (phi 0) := by
  classical
  let _ := hfinite.fintype
  let g : Nat → Set.range f := fun n ↦ ⟨f n, ⟨n, rfl⟩⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber g
  have hy' : ({n | g n = y} : Set Nat).Infinite := Set.infinite_coe_iff.mp hy
  let phi : Nat → Nat := Nat.nth (fun n ↦ g n = y)
  have hphi : StrictMono phi := Nat.nth_strictMono hy'
  have hmem (n : Nat) : g (phi n) = y :=
    Nat.nth_mem n (fun hf ↦ (hy' hf).elim)
  refine ⟨phi, hphi, fun n ↦ ?_⟩
  exact congrArg Subtype.val ((hmem n).trans (hmem 0).symm)

private theorem isClosed_of_isCenterColumn
    {K : Region} {C : Set Tiling.Plane}
    (hC : IsCenterColumn Axis.vertical K C) : IsClosed C := by
  obtain ⟨delta, hdelta, hsep⟩ := exists_packingSeparation K
  apply Metric.isClosed_of_pairwise_le_dist hdelta
  intro s hs t ht hst
  exact hsep C hC.1 s hs t ht hst

private theorem locallyFellConverges_comp_strictMono
    (A : Nat → Set Tiling.Plane) (S : Set Tiling.Plane)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconv : Topology.LocallyFellConverges A S) :
    Topology.LocallyFellConverges (fun n ↦ A (phi n)) S := by
  rcases hconv with ⟨hA, hS, hconv⟩
  exact ⟨fun n ↦ hA (phi n), hS, hconv.comp hphi.tendsto_atTop⟩

private theorem translated_normalized_subset_ambientLimit
    {K : Region}
    (T : Nat → Topology.TilingSpace K Set.univ)
    (S : Topology.TilingSpace K Set.univ)
    (N : Set Tiling.Plane) (anchor : Nat → Tiling.Plane)
    (limitAnchor : Tiling.Plane)
    (hsubset : ∀ n, anchor n +ᵥ N ⊆ ((T n).centres : Set Tiling.Plane))
    (hanchor : Filter.Tendsto anchor Filter.atTop (nhds limitAnchor))
    (hconverges : Topology.LocallyFellConverges
      (Topology.TilingSpace.centresSequence T) (S.centres : Set Tiling.Plane)) :
    limitAnchor +ᵥ N ⊆ (S.centres : Set Tiling.Plane) := by
  rintro x ⟨u, hu, rfl⟩
  apply Continuous.mem_of_locallyFellConverges_of_tendsto_mem hconverges
      (zseq := fun n ↦ anchor n + u)
  · intro n
    exact hsubset n ⟨u, hu, rfl⟩
  · simpa only [vadd_eq_add] using hanchor.add_const u



private theorem exists_strictMono_normalization_exact
    {K : Region}
    (C : ℕ → Set Tiling.Plane)
    (hC : ∀ n, IsCenterColumn Axis.vertical K (C n))
    (anchor : ℕ → Tiling.Plane)
    (hanchor : ∀ n, anchor n ∈ C n) :
    ∃ (φ : ℕ → ℕ) (N : Set Tiling.Plane),
      StrictMono φ ∧
        (∀ n, (-anchor (φ n)) +ᵥ C (φ n) = N) ∧
        N.Nonempty ∧ 0 ∈ N ∧
        N ⊆ {z : Tiling.Plane | z.re = 0} ∧
        IsCenterColumn Axis.vertical K N := by
  classical
  have hfinite := normalizedVerticalColumnCentres_finite C hC anchor hanchor
  let f : ℕ → Set Tiling.Plane := fun n ↦ (-anchor n) +ᵥ C n
  obtain ⟨φ, hφ, hφconst⟩ := exists_strictMono_const_of_finite_range f hfinite
  let N : Set Tiling.Plane := f (φ 0)
  have hNexact : ∀ n, f (φ n) = N := by
    intro n
    exact hφconst n
  have hNdef : N = (-anchor (φ 0)) +ᵥ C (φ 0) := rfl
  have hNnonempty : N.Nonempty := by
    rw [hNdef]
    obtain ⟨u, hu⟩ := (hC (φ 0)).2.1
    exact ⟨-anchor (φ 0) + u, ⟨u, hu, rfl⟩⟩
  have hNzero : (0 : Tiling.Plane) ∈ N := by
    rw [hNdef]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add] using hanchor (φ 0)
  obtain ⟨a, ha⟩ := (hC (φ 0)).2.2.1
  have hNaxis : N ⊆ {z : Tiling.Plane | z.re = 0} := by
    intro z hz
    rw [hNdef, Set.mem_vadd_set_iff_neg_vadd_mem] at hz
    have hzC : (anchor (φ 0) : Tiling.Plane) + z ∈ C (φ 0) := by
      simpa [vadd_eq_add, add_comm] using hz
    have hanchorAxis : (anchor (φ 0)).re = a :=
      ha (anchor (φ 0)) (hanchor (φ 0))
    have hzAxis : ((anchor (φ 0) : Tiling.Plane) + z).re = a :=
      ha _ hzC
    change z.re = 0
    simp only [Complex.add_re] at hzAxis
    linarith
  have hNpacking :
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements N) := by
    apply (isPacking_iff_openCarrier_disjoint K N).mpr
    intro s hs t ht hst
    have hpack := (isPacking_iff_openCarrier_disjoint K (C (φ 0))).mp
      (hC (φ 0)).1
    change Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.openCarrier)
    rw [Set.disjoint_left]
    intro z hzs hzt
    have hsC : (anchor (φ 0) : Tiling.Plane) + s ∈ C (φ 0) := by
      rw [hNdef, Set.mem_vadd_set_iff_neg_vadd_mem] at hs
      simpa [vadd_eq_add, add_comm] using hs
    have htC : (anchor (φ 0) : Tiling.Plane) + t ∈ C (φ 0) := by
      rw [hNdef, Set.mem_vadd_set_iff_neg_vadd_mem] at ht
      simpa [vadd_eq_add, add_comm] using ht
    have hstC : (anchor (φ 0) : Tiling.Plane) + s ≠
        (anchor (φ 0) : Tiling.Plane) + t := by
      intro hEq
      apply hst
      exact add_left_cancel hEq
    have hzS : (anchor (φ 0) : Tiling.Plane) + z ∈
        ((anchor (φ 0) : Tiling.Plane) + s) +ᵥ K.openCarrier := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzs ⊢
      simpa [vadd_eq_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hzs
    have hzT : (anchor (φ 0) : Tiling.Plane) + z ∈
        ((anchor (φ 0) : Tiling.Plane) + t) +ᵥ K.openCarrier := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzt ⊢
      simpa [vadd_eq_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hzt
    exact Set.disjoint_left.mp (hpack hsC htC hstC) hzS hzT
  have hNinvariant : ∀ r : ℝ,
      ((r : ℂ) * Complex.I) +ᵥ regularSupport K N = regularSupport K N := by
    intro r
    rw [hNdef, regularSupport_vadd]
    have hInv := (hC (φ 0)).2.2.2 r
    rw [vadd_vadd, add_comm]
    rw [← vadd_vadd, hInv]
  have hNcolumn : IsCenterColumn Axis.vertical K N := by
    refine ⟨hNpacking, hNnonempty, ?_, hNinvariant⟩
    exact ⟨0, by intro z hz; exact hNaxis hz⟩
  refine ⟨φ, N, hφ, ?_, hNnonempty, hNzero, hNaxis, hNcolumn⟩
  intro n
  exact hNexact n



open Tiling.AxisParallel

private def onePointTranslate'
    : Tiling.Plane × OnePoint Tiling.Plane → OnePoint Tiling.Plane
  | (_, OnePoint.infty) => OnePoint.infty
  | (g, (x : Tiling.Plane)) => ((x + g : Tiling.Plane) : OnePoint Tiling.Plane)

private theorem onePointTranslate'_continuous :
    Continuous onePointTranslate' := by
  rw [continuous_iff_continuousAt]
  rintro ⟨g, z⟩
  induction z using OnePoint.rec with
  | coe x =>
      rw [continuousAt_def]
      intro A hA
      obtain ⟨A₀, hA₀A, hA₀open, hxgA₀⟩ := mem_nhds_iff.mp hA
      let B : Set Tiling.Plane :=
        (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) ⁻¹' A₀
      have hBopen : IsOpen B := hA₀open.preimage OnePoint.continuous_coe
      have hxgB : x + g ∈ B := hxgA₀
      let H : Set (Tiling.Plane × Tiling.Plane) :=
        (fun p ↦ p.2 + p.1) ⁻¹' B
      have hHnhds : H ∈ nhds (g, x) :=
        (continuous_snd.add continuous_fst).continuousAt.preimage_mem_nhds
          (hBopen.mem_nhds hxgB)
      obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hHnhds
      let V' : Set (OnePoint Tiling.Plane) :=
        (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) '' V
      have hV' : V' ∈ nhds (x : OnePoint Tiling.Plane) := by
        rw [OnePoint.nhds_coe_eq]
        exact Filter.image_mem_map hV
      apply Filter.mem_of_superset (prod_mem_nhds hU hV')
      rintro ⟨g', z'⟩ ⟨hg', hz'⟩
      rcases hz' with ⟨x', hx', rfl⟩
      apply hA₀A
      exact hUV (show (g', x') ∈ U ×ˢ V from ⟨hg', hx'⟩)
  | infty =>
      rw [continuousAt_def]
      intro A hA
      obtain ⟨A₀, hA₀A, hA₀open, hinftyA₀⟩ := mem_nhds_iff.mp hA
      let C : Set Tiling.Plane :=
        ((fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) ⁻¹' A₀)ᶜ
      have hC : IsClosed C ∧ IsCompact C :=
        (OnePoint.isOpen_iff_of_mem hinftyA₀).mp hA₀open
      let U : Set Tiling.Plane := Metric.ball g 1
      let D : Set Tiling.Plane :=
        (fun p : Tiling.Plane × Tiling.Plane ↦ p.1 - p.2) ''
          (C ×ˢ Metric.closedBall g 1)
      have hDcompact : IsCompact D :=
        (hC.2.prod (isCompact_closedBall g 1)).image
          (continuous_fst.sub continuous_snd)
      have hDclosed : IsClosed D := hDcompact.isClosed
      let V : Set (OnePoint Tiling.Plane) :=
        (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) '' Dᶜ ∪
          {OnePoint.infty}
      have hV : V ∈ nhds (OnePoint.infty : OnePoint Tiling.Plane) := by
        exact OnePoint.hasBasis_nhds_infty.mem_iff.mpr
          ⟨D, ⟨hDclosed, hDcompact⟩, Subset.rfl⟩
      have hU : U ∈ nhds g := Metric.ball_mem_nhds g zero_lt_one
      apply Filter.mem_of_superset (prod_mem_nhds hU hV)
      rintro ⟨g', z'⟩ ⟨hg', hz'⟩
      apply hA₀A
      induction z' using OnePoint.rec with
      | infty => exact hinftyA₀
      | coe x =>
          have hxD : x ∉ D := by
            simpa [V] using hz'
          have hxgC : x + g' ∉ C := by
            intro hxgC
            apply hxD
            refine ⟨(x + g', g'), ⟨hxgC, ?_⟩, ?_⟩
            · exact Metric.mem_closedBall.mpr
                (le_of_lt (Metric.mem_ball.mp (show g' ∈ U from hg')))
            · simp only
              abel
          exact not_not.mp hxgC

private theorem fellCompactification_translate'
    {N : Set Tiling.Plane} (hN : IsClosed N) (a : Tiling.Plane) :
    Tiling.AxisParallel.Topology.fellCompactification
        (a +ᵥ N) (hN.vadd a) =
      TopologicalSpace.NonemptyCompacts.map
        ((Homeomorph.addRight a).onePointCongr)
        ((Homeomorph.addRight a).onePointCongr.continuous)
        (Tiling.AxisParallel.Topology.fellCompactification N hN) := by
  apply TopologicalSpace.NonemptyCompacts.ext
  change
    ((fun x : Tiling.Plane ↦ (x : OnePoint Tiling.Plane)) '' (a +ᵥ N) ∪
        {OnePoint.infty}) =
      ((Homeomorph.addRight a).onePointCongr ''
        (((fun x : Tiling.Plane ↦ (x : OnePoint Tiling.Plane)) '' N) ∪
          {OnePoint.infty}))
  ext z
  induction z using OnePoint.rec with
  | infty => simp
  | coe x =>
      simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff,
        OnePoint.coe_ne_infty, or_false, Homeomorph.onePointCongr]
      constructor
      · rintro ⟨y, ⟨t, ht, hty⟩, hyx⟩
        subst y
        refine ⟨(t : OnePoint Tiling.Plane), Or.inl ⟨t, ht, rfl⟩, ?_⟩
        simpa [vadd_eq_add, add_comm] using hyx
      · rintro ⟨z, hz, hzx⟩
        rcases hz with ⟨t, ht, rfl⟩ | rfl
        · exact ⟨a + t, ⟨t, ht, by simp [vadd_eq_add]⟩,
            by simpa [vadd_eq_add, add_comm] using hzx⟩
        · simp at hzx

private theorem translate_fixed_closed_locallyFellConverges
    (N : Set Tiling.Plane) (_hN : IsClosed N)
    (anchor : ℕ → Tiling.Plane) (limitAnchor : Tiling.Plane)
    (hanchor : Tendsto anchor atTop (nhds limitAnchor)) :
    Tiling.AxisParallel.Topology.LocallyFellConverges
      (fun n ↦ anchor n +ᵥ N) (limitAnchor +ᵥ N) := by
  let K₀ :=
    Tiling.AxisParallel.Topology.fellCompactification N _hN
  let mapCompact :
      Tiling.Plane × TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) →
        TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) :=
    fun p ↦ TopologicalSpace.NonemptyCompacts.map
      (fun z ↦ onePointTranslate' (p.1, z))
      (onePointTranslate'_continuous.comp
        (continuous_const.prodMk continuous_id))
      K₀
  have hmap : Continuous mapCompact := by
    apply Continuous.nonemptyCompacts_map'
    · exact continuous_const
    · apply onePointTranslate'_continuous.comp
      exact ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hinput : Tendsto (fun n ↦ (anchor n, K₀)) atTop
      (nhds (limitAnchor, K₀)) :=
    hanchor.prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ K₀) atTop (nhds K₀))
  have hmapped := (hmap.tendsto (limitAnchor, K₀)).comp hinput
  refine ⟨fun n ↦ _hN.vadd (anchor n), _hN.vadd limitAnchor, ?_⟩
  have heq (a : Tiling.Plane) :
      mapCompact (a, K₀) =
        Tiling.AxisParallel.Topology.fellCompactification
          (a +ᵥ N) (_hN.vadd a) := by
    symm
    have hfun :
        (fun z : OnePoint Tiling.Plane ↦ onePointTranslate' (a, z)) =
          (Homeomorph.addRight a).onePointCongr := by
      funext z
      induction z using OnePoint.rec with
      | infty => rfl
      | coe x => simp [onePointTranslate', Homeomorph.onePointCongr]
    have hmapeq :
        TopologicalSpace.NonemptyCompacts.map
            (fun z ↦ onePointTranslate' (a, z))
            (onePointTranslate'_continuous.comp
              (continuous_const.prodMk continuous_id)) K₀ =
          TopologicalSpace.NonemptyCompacts.map
            ((Homeomorph.addRight a).onePointCongr)
            ((Homeomorph.addRight a).onePointCongr.continuous) K₀ := by
      congr 1
    calc
      Tiling.AxisParallel.Topology.fellCompactification
          (a +ᵥ N) (_hN.vadd a) =
          TopologicalSpace.NonemptyCompacts.map
            ((Homeomorph.addRight a).onePointCongr)
            ((Homeomorph.addRight a).onePointCongr.continuous) K₀ :=
        fellCompactification_translate' _hN a
      _ = TopologicalSpace.NonemptyCompacts.map
            (fun z ↦ onePointTranslate' (a, z))
            (onePointTranslate'_continuous.comp
              (continuous_const.prodMk continuous_id)) K₀ := hmapeq.symm
      _ = mapCompact (a, K₀) := rfl
  convert hmapped using 1
  · funext n
    exact (heq (anchor n)).symm
  · exact congrArg nhds (heq limitAnchor).symm

private theorem verticalPlate_centres_subset
    {K : Region} {T : Set Tiling.Plane}
    (P : Continuous.VerticalPlate K T) : P.centres ⊆ T := by
  rintro z ⟨t, ht, rfl⟩
  exact t.2

private theorem isCenterColumn_vadd_vertical
    {K : Region} {N : Set Tiling.Plane} (u : Tiling.Plane)
    (hN : IsCenterColumn Axis.vertical K N)
    (haxis : N ⊆ {z : Tiling.Plane | z.re = 0}) :
    IsCenterColumn Axis.vertical K (u +ᵥ N) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (isPacking_iff_openCarrier_disjoint K (u +ᵥ N)).mpr
    intro s hs t ht hst
    rcases hs with ⟨s₀, hs₀, rfl⟩
    rcases ht with ⟨t₀, ht₀, rfl⟩
    have hdisj := (isPacking_iff_openCarrier_disjoint K N).mp hN.1 hs₀ ht₀
      (by intro heq; exact hst (by rw [heq]))
    change Disjoint (s₀ +ᵥ K.openCarrier) (t₀ +ᵥ K.openCarrier) at hdisj
    change Disjoint ((u + s₀) +ᵥ K.openCarrier) ((u + t₀) +ᵥ K.openCarrier)
    rw [Set.disjoint_left] at hdisj ⊢
    intro z hzS hzT
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzS hzT
    apply hdisj (a := -u + z)
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hzS
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hzT
  · rcases hN.2.1 with ⟨z, hz⟩
    exact ⟨u + z, ⟨z, hz, rfl⟩⟩
  · refine ⟨u.re, ?_⟩
    rintro z ⟨z₀, hz₀, rfl⟩
    change (u + z₀).re = u.re
    have hzre : z₀.re = 0 := haxis hz₀
    simp [hzre]
  · intro a
    change (((a : ℂ) * Complex.I) +ᵥ regularSupport K (u +ᵥ N)) =
      regularSupport K (u +ᵥ N)
    rw [regularSupport_vadd]
    calc
      ((a : ℂ) * Complex.I) +ᵥ (u +ᵥ regularSupport K N) =
          (((a : ℂ) * Complex.I) + u) +ᵥ regularSupport K N := by
            rw [vadd_vadd]
      _ = (u + (a : ℂ) * Complex.I) +ᵥ regularSupport K N := by
            rw [add_comm]
      _ = u +ᵥ (((a : ℂ) * Complex.I) +ᵥ regularSupport K N) := by
            rw [vadd_vadd]
      _ = u +ᵥ regularSupport K N := by rw [hN.2.2.2 a]


private theorem exists_normalizedVerticalColumnLimitData_of_normalization
    {K : Region}
    (T : ℕ → Topology.TilingSpace K Set.univ)
    (S : Topology.TilingSpace K Set.univ)
    (C : (n : ℕ) → Continuous.VerticalPlate K ((T n).centres : Set Tiling.Plane))
    (_hC : ∀ n : ℕ, Continuous.IsVerticalColumn (C n))
    (anchor : ℕ → Tiling.Plane)
    (_hanchor : ∀ n : ℕ, anchor n ∈ (C n).centres)
    (limitAnchor : Tiling.Plane)
    (hanchor_converges : Tendsto anchor atTop (nhds limitAnchor))
    (hconverges : Topology.LocallyFellConverges
      (Topology.TilingSpace.centresSequence T) (S.centres : Set Tiling.Plane))
    (hnormalize : ∃ (φ : ℕ → ℕ) (N : Set Tiling.Plane),
      StrictMono φ ∧
        (∀ n, (-anchor (φ n)) +ᵥ (C (φ n)).centres = N) ∧
        N.Nonempty ∧ 0 ∈ N ∧
        N ⊆ {z : Tiling.Plane | z.re = 0} ∧
        IsCenterColumn Axis.vertical K N)
    :
    Nonempty (NormalizedVerticalColumnLimitData T S C anchor limitAnchor) := by
  classical
  rcases hnormalize with ⟨φ, N, hφ, hexact, hNne, hNzero, hNaxis, hNcolumn⟩
  have hNclosed : IsClosed N := isClosed_of_isCenterColumn hNcolumn
  have hambientSub := locallyFellConverges_comp_strictMono
    (fun n ↦ ((T n).centres : Set Tiling.Plane)) (S.centres : Set Tiling.Plane)
    φ hφ hconverges
  have hsubset : ∀ n, anchor (φ n) +ᵥ N ⊆
      ((T (φ n)).centres : Set Tiling.Plane) := by
    intro n
    have heq : anchor (φ n) +ᵥ N = (C (φ n)).centres := by
      rw [← hexact n, vadd_vadd]
      simp
    rw [heq]
    exact verticalPlate_centres_subset (C (φ n))
  have hlimitSubset : limitAnchor +ᵥ N ⊆ (S.centres : Set Tiling.Plane) := by
    apply translated_normalized_subset_ambientLimit
      (fun n ↦ T (φ n)) S N (fun n ↦ anchor (φ n)) limitAnchor hsubset
      (hanchor_converges.comp hφ.tendsto_atTop) hambientSub
  have hlimitColumn' := isCenterColumn_vadd_vertical limitAnchor hNcolumn hNaxis
  have hlimitMem : limitAnchor ∈ limitAnchor +ᵥ N := by
    exact ⟨0, hNzero, by simp⟩
  obtain ⟨P, hPcolumn, hPmem, hPeq⟩ :=
    Tiling.AxisParallel.Continuous.completeColumn_eq_verticalPlateThrough
      S.tilesOn hlimitColumn' hlimitSubset hlimitMem
  have hcolumnConverges : Topology.LocallyFellConverges
      (fun n ↦ (C (φ n)).centres) P.centres := by
    rw [hPeq]
    have htranslated :=
      Tiling.AxisParallel.Structure.translate_fixed_closed_locallyFellConverges
        N hNclosed (fun n ↦ anchor (φ n)) limitAnchor
        (hanchor_converges.comp hφ.tendsto_atTop)
    have hseq : (fun n ↦ (C (φ n)).centres) =
        (fun n ↦ anchor (φ n) +ᵥ N) := by
      funext n
      exact (show anchor (φ n) +ᵥ N = (C (φ n)).centres from by
        rw [← hexact n, vadd_vadd]
        simp).symm
    rw [hseq]
    exact htranslated
  refine ⟨{
    subsequence := φ
    subsequence_strictMono := hφ
    ambient_converges := hambientSub
    normalizedCentres := N
    normalized_closed := hNclosed
    normalized_nonempty := hNne
    zero_mem_normalized := hNzero
    normalized_on_verticalAxis := hNaxis
    normalized_isCenterColumn := hNcolumn
    normalization_exact := hexact
    limitPlate := P
    limitPlate_isColumn := hPcolumn
    limitAnchor_mem := hPmem
    column_converges := hcolumnConverges
    limitCentres_eq := hPeq
  }⟩

private theorem verticalColumn_survives_anchoredLimit_of_normalization
    {K : Region}
    (T : ℕ → Topology.TilingSpace K Set.univ)
    (S : Topology.TilingSpace K Set.univ)
    (C : (n : ℕ) → Continuous.VerticalPlate K ((T n).centres : Set Tiling.Plane))
    (hC : ∀ n : ℕ, Continuous.IsVerticalColumn (C n))
    (anchor : ℕ → Tiling.Plane)
    (hanchor : ∀ n : ℕ, anchor n ∈ (C n).centres)
    (limitAnchor : Tiling.Plane)
    (hanchor_converges : Tendsto anchor atTop (nhds limitAnchor))
    (hconverges : Topology.LocallyFellConverges
      (Topology.TilingSpace.centresSequence T) (S.centres : Set Tiling.Plane))
    (hnormalize : ∃ (φ : ℕ → ℕ) (N : Set Tiling.Plane),
      StrictMono φ ∧
        (∀ n, (-anchor (φ n)) +ᵥ (C (φ n)).centres = N) ∧
        N.Nonempty ∧ 0 ∈ N ∧
        N ⊆ {z : Tiling.Plane | z.re = 0} ∧
        IsCenterColumn Axis.vertical K N)
    :
    ∃ P : Continuous.VerticalPlate K (S.centres : Set Tiling.Plane),
      Continuous.IsVerticalColumn P ∧ limitAnchor ∈ P.centres := by
  rcases exists_normalizedVerticalColumnLimitData_of_normalization
    T S C hC anchor hanchor limitAnchor hanchor_converges hconverges hnormalize
    with ⟨D⟩
  exact ⟨D.limitPlate, D.limitPlate_isColumn, D.limitAnchor_mem⟩



theorem exists_normalizedVerticalColumnLimitData
    {K : Region}
    (T : ℕ → Topology.TilingSpace K Set.univ)
    (S : Topology.TilingSpace K Set.univ)
    (C : (n : ℕ) → Continuous.VerticalPlate K ((T n).centres : Set Tiling.Plane))
    (hC : ∀ n : ℕ, Continuous.IsVerticalColumn (C n))
    (anchor : ℕ → Tiling.Plane)
    (hanchor : ∀ n, anchor n ∈ (C n).centres)
    (limitAnchor : Tiling.Plane)
    (hanchor_converges : Filter.Tendsto anchor Filter.atTop (nhds limitAnchor))
    (hconverges : Topology.LocallyFellConverges
      (Topology.TilingSpace.centresSequence T) (S.centres : Set Tiling.Plane)) :
    Nonempty (NormalizedVerticalColumnLimitData T S C anchor limitAnchor) := by
  have hCcent : ∀ n, IsCenterColumn Axis.vertical K ((C n).centres : Set Tiling.Plane) := by
    intro n
    exact verticalPlate_isCenterColumn_of_isVerticalColumn (T n).tilesOn (C n) (hC n)
  have hnormalize := exists_strictMono_normalization_exact
    (K := K) (fun n => (C n).centres) hCcent anchor hanchor
  exact exists_normalizedVerticalColumnLimitData_of_normalization
    T S C hC anchor hanchor limitAnchor hanchor_converges hconverges hnormalize

theorem verticalColumn_survives_anchoredLimit
    {K : Region}
    (T : ℕ → Topology.TilingSpace K Set.univ)
    (S : Topology.TilingSpace K Set.univ)
    (C : (n : ℕ) → Continuous.VerticalPlate K ((T n).centres : Set Tiling.Plane))
    (hC : ∀ n, Continuous.IsVerticalColumn (C n))
    (anchor : ℕ → Tiling.Plane)
    (hanchor : ∀ n, anchor n ∈ (C n).centres)
    (limitAnchor : Tiling.Plane)
    (hanchor_converges : Filter.Tendsto anchor Filter.atTop (nhds limitAnchor))
    (hconverges : Topology.LocallyFellConverges
      (Topology.TilingSpace.centresSequence T) (S.centres : Set Tiling.Plane)) :
    ∃ P : Continuous.VerticalPlate K (S.centres : Set Tiling.Plane),
      Continuous.IsVerticalColumn P ∧ limitAnchor ∈ P.centres := by
  obtain ⟨D⟩ := exists_normalizedVerticalColumnLimitData
    T S C hC anchor hanchor limitAnchor hanchor_converges hconverges
  exact ⟨D.limitPlate, D.limitPlate_isColumn, D.limitAnchor_mem⟩


end Tiling.AxisParallel.Structure
