import Tiling.AxisParallel.Topology.FellCore
import Tiling.Geometry.Plane

/-!
# Plane-specialized locally Fell matching

The compact Fell topology primitives used by continuous tiling arguments live in this lower
topology layer, independent of the continuous fixed-carrier tiling layer.
-/

open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Topology

/-- A point of a local Fell limit is eventually approximated in every positive ball. -/
theorem locallyFellConverges_eventually_exists_mem_ball
    {A : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges A L)
    {x : Tiling.Plane} (hx : x ∈ L) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ y ∈ A n, dist y x < epsilon := by
  rcases hconv with ⟨hA, hL, hconv⟩
  let U : Set (OnePoint Tiling.Plane) :=
    (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) '' Metric.ball x epsilon
  have hUopen : IsOpen U :=
    OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball
  let V : Set (TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane)) :=
    {Q | ((Q : Set (OnePoint Tiling.Plane)) ∩ U).Nonempty}
  have hVopen : IsOpen V :=
    TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hUopen
  have hlimit : Tiling.AxisParallel.Topology.fellCompactification L hL ∈ V := by
    refine ⟨(x : OnePoint Tiling.Plane), ?_, ⟨x, ?_, rfl⟩⟩
    · simp [Tiling.AxisParallel.Topology.fellCompactification,
        Tiling.Topology.fellCompactification, hx]
    · exact Metric.mem_ball_self hepsilon
  filter_upwards [hconv (hVopen.mem_nhds hlimit)] with n hn
  rcases hn with ⟨w, hwQ, hwU⟩
  rcases hwU with ⟨y, hy, rfl⟩
  refine ⟨y, ?_, Metric.mem_ball.mp hy⟩
  simpa [Tiling.AxisParallel.Topology.fellCompactification,
    Tiling.Topology.fellCompactification] using hwQ

/-- A compact set disjoint from a local Fell limit is eventually disjoint from the converging
sequence. -/
theorem locallyFellConverges_eventually_disjoint_compact
    {A : ℕ → Set Tiling.Plane} {L C : Set Tiling.Plane}
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges A L)
    (hC : IsCompact C) (hLC : Disjoint L C) :
    ∀ᶠ n : ℕ in Filter.atTop, Disjoint (A n) C := by
  rcases hconv with ⟨hA, hL, hconv⟩
  let C' : Set (OnePoint Tiling.Plane) :=
    (fun x : Tiling.Plane ↦ (x : OnePoint Tiling.Plane)) '' C
  have hC'closed : IsClosed C' :=
    (hC.image OnePoint.continuous_coe).isClosed
  let U : Set (OnePoint Tiling.Plane) := C'ᶜ
  let V : Set (TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane)) :=
    {Q | (Q : Set (OnePoint Tiling.Plane)) ⊆ U}
  have hVopen : IsOpen V :=
    TopologicalSpace.NonemptyCompacts.isOpen_subsets_of_isOpen hC'closed.isOpen_compl
  have hlimit : Tiling.AxisParallel.Topology.fellCompactification L hL ∈ V := by
    intro z hzQ hzC'
    rcases hzC' with ⟨c, hcC, rfl⟩
    have hcL : c ∈ L := by
      simpa [Tiling.AxisParallel.Topology.fellCompactification,
        Tiling.Topology.fellCompactification] using hzQ
    exact Set.disjoint_left.mp hLC hcL hcC
  filter_upwards [hconv (hVopen.mem_nhds hlimit)] with n hn
  rw [Set.disjoint_left]
  intro x hxA hxC
  have hxQ : (x : OnePoint Tiling.Plane) ∈
      (Tiling.AxisParallel.Topology.fellCompactification (A n) (hA n) :
        Set (OnePoint Tiling.Plane)) := by
    simp [Tiling.AxisParallel.Topology.fellCompactification,
      Tiling.Topology.fellCompactification, hxA]
  exact hn hxQ ⟨x, hxC, rfl⟩

/-- A convergent sequence of marked points in locally Fell-convergent closed sets has its limit
in the limiting closed set. -/
theorem mem_of_locallyFellConverges_of_tendsto_mem
    {A : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges A L)
    {zseq : ℕ → Tiling.Plane} {z : Tiling.Plane}
    (hzmem : ∀ n, zseq n ∈ A n)
    (hzlim : Filter.Tendsto zseq Filter.atTop (nhds z)) : z ∈ L := by
  by_contra hzL
  rcases hconv with ⟨hAclosed, hLclosed, hconv⟩
  have hcompl : Lᶜ ∈ nhds z := hLclosed.isOpen_compl.mem_nhds hzL
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hcompl
  let C : Set Tiling.Plane := Metric.closedBall z (epsilon / 2)
  have hLC : Disjoint L C := by
    rw [Set.disjoint_left]
    intro y hyL hyC
    apply (hball (Metric.mem_ball.mpr (lt_of_le_of_lt
      (Metric.mem_closedBall.mp hyC) (half_lt_self hepsilon)))).elim
    exact hyL
  have hdisjoint := locallyFellConverges_eventually_disjoint_compact
    ⟨hAclosed, hLclosed, hconv⟩ (isCompact_closedBall z (epsilon / 2)) hLC
  have hzC : ∀ᶠ n : ℕ in Filter.atTop, zseq n ∈ C := by
    apply hzlim.eventually
    exact Metric.closedBall_mem_nhds z (half_pos hepsilon)
  obtain ⟨n, hn, hzn⟩ := (hdisjoint.and hzC).exists
  exact Set.disjoint_left.1 hn (hzmem n) hzn

/-- Positive uniform separation makes a Plane set discrete. -/
theorem isDiscrete_of_uniformlySeparated
    {delta : ℝ} (hdelta : 0 < delta) {S : Set Tiling.Plane}
    (hS : Tiling.AxisParallel.Topology.IsUniformlySeparated delta S) :
    IsDiscrete S := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  refine ⟨Metric.ball x delta, Metric.isOpen_ball, ?_⟩
  ext y
  constructor
  · rintro ⟨hyball, hyS⟩
    have hyx : y = x := by
      by_contra hyx
      have hsep := hS hyS hx hyx
      rw [Metric.mem_ball] at hyball
      exact (not_lt_of_ge hsep) hyball
    simp [hyx]
  · rintro (rfl : y = x)
    exact ⟨Metric.mem_ball_self hdelta, hx⟩

/-- On uniformly separated closed sets, local Fell convergence is equivalent to eventual unique
matching in every compact window. -/
theorem locallyFell_matchingPoints
    {delta : ℝ} (hdelta : 0 < delta)
    {S : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hclosedS : ∀ n : ℕ, IsClosed (S n)) (hclosedL : IsClosed L)
    (hsepS : ∀ n : ℕ,
      Tiling.AxisParallel.Topology.IsUniformlySeparated delta (S n))
    (hsepL : Tiling.AxisParallel.Topology.IsUniformlySeparated delta L) :
    Tiling.AxisParallel.Topology.LocallyFellConverges S L ↔
      ∀ (C : Set Tiling.Plane), IsCompact C →
        ∀ epsilon : ℝ, 0 < epsilon → epsilon < delta / 3 →
          ∀ᶠ n : ℕ in Filter.atTop,
            (∀ x ∈ L ∩ C, ∃! y : Tiling.Plane,
              y ∈ S n ∧ dist x y < epsilon) ∧
            (∀ y ∈ S n ∩ C, ∃! x : Tiling.Plane,
              x ∈ L ∧ dist x y < epsilon) := by
  constructor
  · intro hconv C hC epsilon hepsilon hepsilonDelta
    have hfinite : (L ∩ C).Finite :=
      (hC.inter_left hclosedL).finite
        ((isDiscrete_of_uniformlySeparated hdelta hsepL).mono inter_subset_left)
    have hforward : ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ L ∩ C, ∃! y : Tiling.Plane,
          y ∈ S n ∧ dist x y < epsilon := by
      rw [hfinite.eventually_all]
      intro x hx
      filter_upwards [locallyFellConverges_eventually_exists_mem_ball
          hconv hx.1 hepsilon] with n hn
      obtain ⟨y, hyS, hxy⟩ := hn
      refine ⟨y, ⟨hyS, by simpa [dist_comm] using hxy⟩, ?_⟩
      intro z hz
      by_contra hzy
      have hsep := hsepS n hz.1 hyS hzy
      have htri := dist_triangle z x y
      have hzx : dist z x < epsilon := by simpa [dist_comm] using hz.2
      have hxy' : dist x y < epsilon := by simpa [dist_comm] using hxy
      have : dist z y < 2 * epsilon := lt_of_le_of_lt htri (by linarith)
      linarith
    let D : Set Tiling.Plane :=
      C ∩ (⋃ x ∈ L, Metric.ball x epsilon)ᶜ
    have hDcompact : IsCompact D := by
      apply hC.inter_right
      exact isClosed_compl_iff.mpr (isOpen_biUnion fun x _ ↦ Metric.isOpen_ball)
    have hLD : Disjoint L D := by
      rw [Set.disjoint_left]
      intro x hxL hxD
      exact hxD.2 (Set.mem_iUnion₂.mpr
        ⟨x, hxL, Metric.mem_ball_self hepsilon⟩)
    have havoid := locallyFellConverges_eventually_disjoint_compact
      hconv hDcompact hLD
    filter_upwards [hforward, havoid] with n hnforward hnavoid
    refine ⟨hnforward, ?_⟩
    intro y hy
    have hexists : ∃ x : Tiling.Plane, x ∈ L ∧ dist x y < epsilon := by
      by_contra hnone
      have hyD : y ∈ D := by
        refine ⟨hy.2, ?_⟩
        rw [mem_compl_iff]
        intro hyUnion
        obtain ⟨x, hxL, hxyball⟩ := Set.mem_iUnion₂.mp hyUnion
        apply hnone
        refine ⟨x, hxL, ?_⟩
        simpa [Metric.mem_ball, dist_comm] using hxyball
      exact Set.disjoint_left.mp hnavoid hy.1 hyD
    obtain ⟨x, hxL, hxy⟩ := hexists
    refine ⟨x, ⟨hxL, hxy⟩, ?_⟩
    intro z hz
    by_contra hzx
    have hsep := hsepL hz.1 hxL hzx
    have htri := dist_triangle z y x
    have hxy' : dist y x < epsilon := by simpa [dist_comm] using hxy
    have : dist z x < 2 * epsilon := lt_of_le_of_lt htri (by linarith)
    linarith
  · intro hmatch
    refine ⟨hclosedS, hclosedL, ?_⟩
    let Kseq : ℕ → TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) :=
      fun n ↦ Tiling.AxisParallel.Topology.fellCompactification (S n) (hclosedS n)
    let Klim : TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) :=
      Tiling.AxisParallel.Topology.fellCompactification L hclosedL
    rw [show (fun n ↦ Tiling.AxisParallel.Topology.fellCompactification
        (S n) (hclosedS n)) = Kseq from rfl]
    change Filter.Tendsto Kseq Filter.atTop (nhds Klim)
    rw [Filter.tendsto_def]
    intro N hN
    obtain ⟨B, hBbasis, hKlimB, hBN⟩ :=
      TopologicalSpace.NonemptyCompacts.isTopologicalBasis.mem_nhds_iff.mp hN
    rcases hBbasis with ⟨u, hu, rfl⟩
    rcases hu with ⟨hufinite, hunonempty, huopen⟩
    rcases hKlimB with ⟨hKsubset, hKhit⟩
    have hinftyUnion : OnePoint.infty ∈ ⋃₀ u :=
      hKsubset (by simp [Klim, Tiling.AxisParallel.Topology.fellCompactification,
        Tiling.Topology.fellCompactification])
    have hUnionOpen : IsOpen (⋃₀ u) := isOpen_sUnion huopen
    let C : Set Tiling.Plane :=
      (fun x : Tiling.Plane ↦ (x : OnePoint Tiling.Plane)) ⁻¹' (⋃₀ u)ᶜ
    have hCclosedCompact : IsClosed C ∧ IsCompact C := by
      have := (OnePoint.isOpen_iff_of_mem hinftyUnion).mp hUnionOpen
      simpa [C, preimage_compl] using this
    have hCL : Disjoint C L := by
      rw [Set.disjoint_left]
      intro x hxC hxL
      exact hxC (hKsubset (by
        simp [Klim, Tiling.AxisParallel.Topology.fellCompactification,
          Tiling.Topology.fellCompactification, hxL]))
    obtain ⟨r, hrpos, hrsep⟩ :=
      Metric.exists_pos_forall_lt_edist hCclosedCompact.2 hclosedL hCL
    let epsilon : ℝ := min ((r : ℝ) / 2) (delta / 6)
    have hepsilon : 0 < epsilon := by
      dsimp [epsilon]
      exact lt_min (by positivity) (by positivity)
    have hepsilonDelta : epsilon < delta / 3 := by
      dsimp [epsilon]
      have := min_le_right ((r : ℝ) / 2) (delta / 6)
      linarith
    have hepsilonR : epsilon < (r : ℝ) := by
      dsimp [epsilon]
      have := min_le_left ((r : ℝ) / 2) (delta / 6)
      linarith
    have hmatchingC := hmatch C hCclosedCompact.2 epsilon hepsilon hepsilonDelta
    have hsubsetEventually : ∀ᶠ n : ℕ in Filter.atTop,
        (Kseq n : Set (OnePoint Tiling.Plane)) ⊆ ⋃₀ u := by
      filter_upwards [hmatchingC] with n hn
      intro z hz
      induction z using OnePoint.rec with
      | infty => exact hinftyUnion
      | coe y =>
          have hyS : y ∈ S n := by
            simpa [Kseq, Tiling.AxisParallel.Topology.fellCompactification,
              Tiling.Topology.fellCompactification] using hz
          by_contra hyUnion
          have hyC : y ∈ C := hyUnion
          obtain ⟨x, ⟨hxL, hxy⟩, _⟩ := hn.2 y ⟨hyS, hyC⟩
          have hrxy := hrsep y hyC x hxL
          have hedist : edist y x < (r : ENNReal) := by
            rw [edist_dist, dist_comm]
            exact (ENNReal.ofReal_lt_coe_iff (dist_nonneg)).mpr
              (hxy.trans hepsilonR)
          exact (not_lt_of_ge hrxy.le) hedist
    have hhitEventually : ∀ᶠ n : ℕ in Filter.atTop,
        ∀ U ∈ u, ((Kseq n : Set (OnePoint Tiling.Plane)) ∩ U).Nonempty := by
      rw [hufinite.eventually_all]
      intro U hU
      obtain ⟨z, hzK, hzU⟩ := hKhit U hU
      induction z using OnePoint.rec with
      | infty =>
          exact Filter.Eventually.of_forall fun n ↦
            ⟨OnePoint.infty, by simp [Kseq,
              Tiling.AxisParallel.Topology.fellCompactification,
              Tiling.Topology.fellCompactification], hzU⟩
      | coe x =>
          have hxL : x ∈ L := by
            simpa [Klim, Tiling.AxisParallel.Topology.fellCompactification,
              Tiling.Topology.fellCompactification] using hzK
          have hUopen : IsOpen U := huopen U hU
          let V : Set Tiling.Plane :=
            (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) ⁻¹' U
          have hVopen : IsOpen V := hUopen.preimage OnePoint.continuous_coe
          have hxV : x ∈ V := hzU
          obtain ⟨rho, hrho, hball⟩ :=
            Metric.mem_nhds_iff.mp (hVopen.mem_nhds hxV)
          let eta : ℝ := min (rho / 2) (delta / 6)
          have heta : 0 < eta := by
            dsimp [eta]
            exact lt_min (by positivity) (by positivity)
          have hetaDelta : eta < delta / 3 := by
            dsimp [eta]
            have := min_le_right (rho / 2) (delta / 6)
            linarith
          have hetaRho : eta < rho := by
            dsimp [eta]
            have := min_le_left (rho / 2) (delta / 6)
            linarith
          filter_upwards [hmatch {x} isCompact_singleton eta heta hetaDelta] with n hn
          obtain ⟨y, ⟨hyS, hxy⟩, _⟩ := hn.1 x ⟨hxL, mem_singleton x⟩
          refine ⟨(y : OnePoint Tiling.Plane), ?_, ?_⟩
          · simp [Kseq, Tiling.AxisParallel.Topology.fellCompactification,
              Tiling.Topology.fellCompactification, hyS]
          · apply hball
            rw [Metric.mem_ball, dist_comm]
            exact hxy.trans hetaRho
    filter_upwards [hsubsetEventually, hhitEventually] with n hnsubset hnhit
    apply hBN
    exact ⟨hnsubset, hnhit⟩

end Tiling.AxisParallel.Topology
