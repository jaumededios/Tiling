import Mathlib.Topology.Sets.VietorisTopology
import TranslationalTilings.Main
import Tiling.AxisParallel.Topology.FellCore
import Tiling.RationalPolygonal.EarthquakeUniform

set_option linter.style.header false

open Function Set
open scoped Matrix

namespace Tiling.AxisParallel.Foundations

private theorem mem_discreteCarrier_iff_tileConv_ne_zero
    {G : Type*} [AddCommGroup G] (F : Finset G) (A : Set G) (x : G) :
    x ∈ Tiling.RationalPolygonal.discreteCarrier F A ↔
      TranslationalTilings.tileConv F (TranslationalTilings.setIndicator A) x ≠ 0 := by
  classical
  rw [TranslationalTilings.tileConv_indicator_eq_card]
  constructor
  · rintro ⟨f, hfF, a, haA, rfl⟩
    have hf : f ∈ F.filter fun q ↦ f + a - q ∈ A := by
      simp only [Finset.mem_filter, hfF, true_and]
      simpa only [add_sub_cancel_left] using haA
    exact_mod_cast (Finset.card_pos.mpr ⟨f, hf⟩).ne'
  · intro hne
    have hcard : 0 < (F.filter fun f ↦ x - f ∈ A).card := by
      exact Nat.pos_of_ne_zero (by exact_mod_cast hne)
    obtain ⟨f, hf⟩ := Finset.card_pos.mp hcard
    have hf' := Finset.mem_filter.mp hf
    exact ⟨f, hf'.1, x - f, hf'.2, by abel⟩

private theorem discreteCarrier_congr_of_convolutionEquivalent
    {G : Type*} [AddCommGroup G] (F : Finset G) {A B : Set G}
    (h : TranslationalTilings.tileConv F (TranslationalTilings.setIndicator A) =
      TranslationalTilings.tileConv F (TranslationalTilings.setIndicator B)) :
    Tiling.RationalPolygonal.discreteCarrier F A =
      Tiling.RationalPolygonal.discreteCarrier F B := by
  ext x
  rw [mem_discreteCarrier_iff_tileConv_ne_zero,
    mem_discreteCarrier_iff_tileConv_ne_zero, h]

private theorem translate_discreteCarrier_slice_of_setScalarPeriodic
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {M : ℕ}
    (hA : TranslationalTilings.SetScalarPeriodic M A)
    (h : TranslationalTilings.Plane)
    (line : TranslationalTilings.Plane ⧸ TranslationalTilings.directionSubgroup h)
    (v : TranslationalTilings.Plane) :
    TranslationalTilings.translateSet (((M : ℕ) : ℤ) • v)
        (Tiling.RationalPolygonal.discreteCarrier F
          (TranslationalTilings.slicePattern h line A)) =
      Tiling.RationalPolygonal.discreteCarrier F
        (TranslationalTilings.slicePattern h
          (line + QuotientAddGroup.mk'
            (TranslationalTilings.directionSubgroup h) (((M : ℕ) : ℤ) • v)) A) := by
  let p : TranslationalTilings.Plane := ((M : ℕ) : ℤ) • v
  ext x
  constructor
  · rintro ⟨f, hfF, t, ht, hxt⟩
    have ht' := (TranslationalTilings.mem_slicePattern t).1 ht
    refine ⟨f, hfF, t + p, ?_, ?_⟩
    · apply (TranslationalTilings.mem_slicePattern (t + p)).2
      refine ⟨?_, ?_⟩
      · exact (hA t v).2 ht'.1
      · simpa only [map_add, p] using congrArg
          (fun q ↦ q + QuotientAddGroup.mk'
            (TranslationalTilings.directionSubgroup h) p) ht'.2
    · change x - p = f + t at hxt
      calc
        x = (x - p) + p := by abel
        _ = (f + t) + p := by rw [hxt]
        _ = f + (t + p) := by abel
  · rintro ⟨f, hfF, t, ht, hxt⟩
    have ht' := (TranslationalTilings.mem_slicePattern t).1 ht
    refine ⟨f, hfF, t - p, ?_, ?_⟩
    · apply (TranslationalTilings.mem_slicePattern (t - p)).2
      refine ⟨?_, ?_⟩
      · apply (hA (t - p) v).1
        simpa only [p, sub_add_cancel]
          using ht'.1
      · rw [map_sub, ht'.2]
        simp [p]
    · change x - p = f + (t - p)
      rw [hxt]
      abel

private theorem setScalarPeriodic_of_dvd
    {d p q : ℕ} {A : Set (TranslationalTilings.Lattice d)}
    (hpq : p ∣ q) (hA : TranslationalTilings.SetScalarPeriodic p A) :
    TranslationalTilings.SetScalarPeriodic q A := by
  obtain ⟨m, rfl⟩ := hpq
  intro x z
  have h := hA x ((m : ℤ) • z)
  simpa only [Nat.cast_mul, mul_smul] using h

private theorem carrier_setScalarPeriodic_of_convolution_scalarPeriodic
    {d p : ℕ} {F : Finset (TranslationalTilings.Lattice d)}
    {A : Set (TranslationalTilings.Lattice d)}
    (h : TranslationalTilings.ScalarPeriodic p
      (TranslationalTilings.tileConv F (TranslationalTilings.setIndicator A))) :
    TranslationalTilings.SetScalarPeriodic p
      (Tiling.RationalPolygonal.discreteCarrier F A) := by
  intro x z
  rw [mem_discreteCarrier_iff_tileConv_ne_zero,
    mem_discreteCarrier_iff_tileConv_ne_zero, h]

private theorem discreteCarrier_eq_target_of_tiles
    {G : Type*} [AddCommGroup G] {F : Finset G} {A E : Set G}
    (hTile : TranslationalTilings.Tiles F A E) :
    Tiling.RationalPolygonal.discreteCarrier F A = E := by
  ext x
  rw [mem_discreteCarrier_iff_tileConv_ne_zero, hTile x]
  by_cases hx : x ∈ E <;>
    simp [TranslationalTilings.setIndicator, hx]

/-- The fixed-target specialization of Greenfeld--Tao's uniform quantitative theorem. -/
theorem gtUniformCosetwiseDirections
    {F : Finset TranslationalTilings.Plane}
    {E : Set TranslationalTilings.Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : TranslationalTilings.SetScalarPeriodic ell E) :
    ∃ D : TranslationalTilings.QuantitativeWeakPeriodData F ell,
      ∀ A : Set TranslationalTilings.Plane,
        TranslationalTilings.Tiles F A E → D.ValidFor A := by
  obtain ⟨D, hD⟩ := TranslationalTilings.theorem_1_4_uniform hell hzero hcard
  exact ⟨D, fun A hA ↦ hD E A hE hA⟩

/-- Total level-one Greenfeld--Tao wrapper, including the singleton-tile branch. -/
theorem gtFiniteWeakPeriodicDecomposition
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane}
    (hF : F.Nonempty) (hE : TranslationalTilings.IsPeriodic E)
    (hTile : TranslationalTilings.Tiles F A E) :
    Nonempty (TranslationalTilings.WeakPeriodicDecomposition A) :=
  TranslationalTilings.level_one_plane_weaklyPeriodic hF hE hTile

/-- Literal transport of finite-tile carriers between parallel slices. -/
theorem gtSliceTransport
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {ell k : ℕ}
    {h : TranslationalTilings.Plane}
    (hell : 0 < ell) (hk : 0 < k)
    (hh : TranslationalTilings.IsPrimitive h)
    (hA : Function.Periodic (TranslationalTilings.setIndicator A)
      (((ell * k : ℕ) : ℤ) • h))
    (hConv : TranslationalTilings.ScalarPeriodic ell
      (TranslationalTilings.tileConv F
        (TranslationalTilings.setIndicator A))) :
    ∀ (line : TranslationalTilings.Plane ⧸
        TranslationalTilings.directionSubgroup h)
      (v : TranslationalTilings.Plane),
      TranslationalTilings.translateSet
          (((TranslationalTilings.indicatorDilationModulus ell F.card * k *
              TranslationalTilings.slicingLCM F h : ℕ) : ℤ) • v)
          (Tiling.RationalPolygonal.discreteCarrier F
            (TranslationalTilings.slicePattern h line A)) =
        Tiling.RationalPolygonal.discreteCarrier F
          (TranslationalTilings.slicePattern h
            (line + QuotientAddGroup.mk'
              (TranslationalTilings.directionSubgroup h)
              (((TranslationalTilings.indicatorDilationModulus ell F.card * k *
                  TranslationalTilings.slicingLCM F h : ℕ) : ℤ) • v)) A) := by
  obtain ⟨A', hA'periodic, _, hslice⟩ :=
    TranslationalTilings.improve_onePeriodic hell hk hh hA hConv
  intro line v
  let M := TranslationalTilings.indicatorDilationModulus ell F.card * k *
    TranslationalTilings.slicingLCM F h
  let p : TranslationalTilings.Plane := ((M : ℕ) : ℤ) • v
  have hcarrier (q : TranslationalTilings.Plane ⧸
      TranslationalTilings.directionSubgroup h) :
      Tiling.RationalPolygonal.discreteCarrier F
          (TranslationalTilings.slicePattern h q A) =
        Tiling.RationalPolygonal.discreteCarrier F
          (TranslationalTilings.slicePattern h q A') :=
    discreteCarrier_congr_of_convolutionEquivalent F (hslice q)
  rw [hcarrier line]
  have htransport := translate_discreteCarrier_slice_of_setScalarPeriodic
    (F := F) hA'periodic h line v
  rw [htransport]
  exact (hcarrier
    (line + QuotientAddGroup.mk'
      (TranslationalTilings.directionSubgroup h) p)).symm

/-- Synchronize the full-rank scalar periods of all directional layer carriers. -/
theorem gtCommonDirectionalCarrierPeriod
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {ell : ℕ}
    (D : TranslationalTilings.DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) :
    ∃ N : ℕ, 0 < N ∧ ∀ j,
      TranslationalTilings.SetScalarPeriodic N
        (Tiling.RationalPolygonal.discreteCarrier F (D.part j)) := by
  classical
  by_cases hm : 2 ≤ D.numberOfParts
  · let p : Fin D.numberOfParts → ℕ := fun j ↦
      ell * TranslationalTilings.completionConvolutionMultiplier D j
    let N : ℕ := ∏ j, p j
    have hp_pos (j : Fin D.numberOfParts) : 0 < p j :=
      Nat.mul_pos hell
        (TranslationalTilings.convolution_part_scalarPeriodic D hm j).1
    have hNpos : 0 < N := by
      apply Finset.prod_pos
      intro j _
      exact hp_pos j
    refine ⟨N, hNpos, fun j ↦ ?_⟩
    have hp : TranslationalTilings.SetScalarPeriodic (p j)
        (Tiling.RationalPolygonal.discreteCarrier F (D.part j)) :=
      carrier_setScalarPeriodic_of_convolution_scalarPeriodic
        (TranslationalTilings.convolution_part_scalarPeriodic D hm j).2.2
    apply setScalarPeriodic_of_dvd (hA := hp)
    exact Finset.dvd_prod_of_mem (fun i ↦ p i) (Finset.mem_univ j)
  · have hm_le : D.numberOfParts ≤ 1 := by omega
    have hm_pos : 0 < D.numberOfParts := D.number_pos
    have hm_eq : D.numberOfParts = 1 := by omega
    have hpart (j : Fin D.numberOfParts) : D.part j = A := by
      apply Set.Subset.antisymm
      · intro x hx
        rw [← D.union_parts]
        exact Set.mem_iUnion_of_mem j hx
      · intro x hx
        rw [← D.union_parts] at hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        have hij : i = j := Fin.ext (by omega)
        simpa only [hij] using hi
    have hcarrier : Tiling.RationalPolygonal.discreteCarrier F A = E :=
      discreteCarrier_eq_target_of_tiles D.tiles
    refine ⟨ell, hell, fun j ↦ ?_⟩
    rw [hpart j, hcarrier]
    exact D.target_periodic

/-- The vertical-direction specialization of the uniform DDGGM earthquake decomposition. -/
theorem ddggmVerticalQuakeDecomposition
    {F : Finset Tiling.RationalPolygonal.IntegerPlane}
    {T : Set Tiling.RationalPolygonal.IntegerPlane}
    (hF : F.Nonempty)
    (hTile : TranslationalTilings.TilesUniverse F T) :
    Nonempty (Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F T (![0, 1] : Tiling.RationalPolygonal.IntegerPlane)) := by
  apply Tiling.RationalPolygonal.exists_uniformQuakePeriodicDecomposition hF
  · intro h
    have := congrFun h 1
    simp at this
  · exact hTile

/-- The hyperspace of nonempty compact subsets of a compact space is compact. -/
theorem nonemptyCompacts_compact
    {E : Type*} [TopologicalSpace E] [CompactSpace E] :
    IsCompact (Set.univ : Set (TopologicalSpace.NonemptyCompacts E)) :=
  isCompact_univ

/-- Uniformly separated closed planar sets admit a locally Fell-convergent subsequence. -/
theorem exists_locallyFellConvergent_subsequence
    (delta : ℝ) (hdelta : 0 < delta)
    (S : ℕ → Set Tiling.Plane) (hclosed : ∀ n, IsClosed (S n))
    (hseparated : ∀ n,
      Tiling.AxisParallel.Topology.IsUniformlySeparated delta (S n)) :
    ∃ (phi : ℕ → ℕ) (L : Set Tiling.Plane),
      StrictMono phi ∧ IsClosed L ∧
      Tiling.AxisParallel.Topology.IsUniformlySeparated delta L ∧
      Tiling.AxisParallel.Topology.LocallyFellConverges (S ∘ phi) L := by
  classical
  have hdelta_pos : 0 < delta := hdelta
  let e := onePointEquivSphereOfFinrankEq
    (ι := Fin 3) (V := Tiling.Plane) (by simp [Tiling.Plane])
  let _ : TopologicalSpace.MetrizableSpace (OnePoint Tiling.Plane) :=
    e.isEmbedding.metrizableSpace
  let _ : MetricSpace (OnePoint Tiling.Plane) :=
    TopologicalSpace.metrizableSpaceMetric (OnePoint Tiling.Plane)
  let Kseq : ℕ → TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) :=
    fun n ↦ Tiling.AxisParallel.Topology.fellCompactification (S n) (hclosed n)
  obtain ⟨K, phi, hphi, hlim⟩ := CompactSpace.tendsto_subseq Kseq
  have hinfty : OnePoint.infty ∈ (K : Set (OnePoint Tiling.Plane)) := by
    let C : Set (TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane)) :=
      {Q | ((Q : Set (OnePoint Tiling.Plane)) ∩ {OnePoint.infty}).Nonempty}
    have hCclosed : IsClosed C :=
      TopologicalSpace.NonemptyCompacts.isClosed_inter_nonempty_of_isClosed
        isClosed_singleton
    have hKC : K ∈ C := hCclosed.mem_of_tendsto hlim (by
      filter_upwards [] with n
      refine ⟨OnePoint.infty, ?_, Set.mem_singleton OnePoint.infty⟩
      simp [Kseq, Tiling.AxisParallel.Topology.fellCompactification,
        Tiling.Topology.fellCompactification])
    simpa [C] using hKC
  let L : Set Tiling.Plane :=
    {x | (x : OnePoint Tiling.Plane) ∈ (K : Set (OnePoint Tiling.Plane))}
  have hLclosed : IsClosed L := by
    exact K.isCompact.isClosed.preimage OnePoint.continuous_coe
  have hK : Tiling.Topology.fellCompactification L hLclosed = K := by
    apply TopologicalSpace.NonemptyCompacts.ext
    ext z
    refine OnePoint.rec ?_ (fun x ↦ ?_) z
    · simp [Tiling.AxisParallel.Topology.fellCompactification,
        Tiling.Topology.fellCompactification, hinfty]
    · simp [Tiling.AxisParallel.Topology.fellCompactification,
        Tiling.Topology.fellCompactification, L]
  have hLseparated :
      Tiling.AxisParallel.Topology.IsUniformlySeparated delta L := by
    intro x hx y hy hxy
    by_contra hdist
    have hdist_lt : dist x y < delta := lt_of_not_ge hdist
    have hxy_dist : 0 < dist x y := dist_pos.mpr hxy
    let eps : ℝ := min ((delta - dist x y) / 4) (dist x y / 4)
    have heps : 0 < eps := by
      dsimp [eps]
      exact lt_min (by linarith [hdelta_pos]) (by linarith)
    let U : Set (OnePoint Tiling.Plane) :=
      (fun z : Tiling.Plane ↦ (z : OnePoint Tiling.Plane)) '' Metric.ball x eps
    let V : Set (OnePoint Tiling.Plane) :=
      (fun z : Tiling.Plane ↦ (z : OnePoint Tiling.Plane)) '' Metric.ball y eps
    have hUopen : IsOpen U := by
      exact OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball
    have hVopen : IsOpen V := by
      exact OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball
    have hxK : (x : OnePoint Tiling.Plane) ∈ (K : Set (OnePoint Tiling.Plane)) := hx
    have hyK : (y : OnePoint Tiling.Plane) ∈ (K : Set (OnePoint Tiling.Plane)) := hy
    have hKhitU : ((K : Set (OnePoint Tiling.Plane)) ∩ U).Nonempty :=
      ⟨x, hxK, ⟨x, Metric.mem_ball_self heps, rfl⟩⟩
    have hKhitV : ((K : Set (OnePoint Tiling.Plane)) ∩ V).Nonempty :=
      ⟨y, hyK, ⟨y, Metric.mem_ball_self heps, rfl⟩⟩
    have hEventuallyU : ∀ᶠ n in Filter.atTop,
        (((Kseq ∘ phi) n : Set (OnePoint Tiling.Plane)) ∩ U).Nonempty :=
      hlim.eventually
        ((TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hUopen).mem_nhds
          hKhitU)
    have hEventuallyV : ∀ᶠ n in Filter.atTop,
        (((Kseq ∘ phi) n : Set (OnePoint Tiling.Plane)) ∩ V).Nonempty :=
      hlim.eventually
        ((TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hVopen).mem_nhds
          hKhitV)
    obtain ⟨n, hnU, hnV⟩ := (hEventuallyU.and hEventuallyV).exists
    obtain ⟨zu, hzuK, ⟨a, ha, rfl⟩⟩ := hnU
    obtain ⟨zv, hzvK, ⟨b, hb, rfl⟩⟩ := hnV
    have haS : a ∈ S (phi n) := by
      simpa [Kseq, Tiling.AxisParallel.Topology.fellCompactification,
        Tiling.Topology.fellCompactification] using hzuK
    have hbS : b ∈ S (phi n) := by
      simpa [Kseq, Tiling.AxisParallel.Topology.fellCompactification,
        Tiling.Topology.fellCompactification] using hzvK
    have hab : a ≠ b := by
      intro hab
      subst b
      have hxa : dist x a < eps := by
        rw [dist_comm]
        exact ha
      have hay : dist a y < eps := hb
      have heps_le : eps ≤ dist x y / 4 := min_le_right _ _
      have htri : dist x y ≤ dist x a + dist a y := dist_triangle _ _ _
      linarith
    have hsep := hseparated (phi n) haS hbS hab
    have hax : dist a x < eps := by simpa [dist_comm] using ha
    have hyb : dist y b < eps := by simpa [dist_comm] using hb
    have heps_le : eps ≤ (delta - dist x y) / 4 := min_le_left _ _
    have hab_lt : dist a b < delta := by
      calc
        dist a b ≤ dist a x + dist x y + dist y b := dist_triangle4 _ _ _ _
        _ < eps + dist x y + eps := by linarith
        _ < delta := by linarith
    exact (not_lt_of_ge hsep) hab_lt
  refine ⟨phi, L, hphi, hLclosed, hLseparated, ?_⟩
  refine ⟨fun n ↦ hclosed (phi n), hLclosed, ?_⟩
  rw [hK]
  change Filter.Tendsto (Kseq ∘ phi) Filter.atTop (nhds K)
  exact hlim

end Tiling.AxisParallel.Foundations
