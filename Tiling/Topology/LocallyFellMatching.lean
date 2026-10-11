import Tiling.Topology.FellCore
import Tiling.Geometry.Plane
import Tiling.Geometry.Periodicity

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology

noncomputable section

namespace Tiling.Topology

theorem locallyFellConverges_eventually_exists_mem_ball
    {A : ℕ → Set Plane} {L : Set Plane} (hconv : LocallyFellConverges A L)
    {x : Plane} (hx : x ∈ L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ y ∈ A n, dist y x < ε := by
  rcases hconv with ⟨hA, hL, hconv⟩
  let U : Set (OnePoint Tiling.Plane) :=
    (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) '' Metric.ball x ε
  have hUopen : IsOpen U :=
    OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball
  let V : Set (TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane)) :=
    {Q | ((Q : Set (OnePoint Tiling.Plane)) ∩ U).Nonempty}
  have hVopen : IsOpen V :=
    TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hUopen
  have hlimit : fellCompactification L hL ∈ V := by
    refine ⟨(x : OnePoint Tiling.Plane), ?_, ⟨x, ?_, rfl⟩⟩
    · simp [fellCompactification, hx]
    · exact Metric.mem_ball_self hε
  filter_upwards [hconv (hVopen.mem_nhds hlimit)] with n hn
  rcases hn with ⟨w, hwQ, hwU⟩
  rcases hwU with ⟨y, hy, rfl⟩
  refine ⟨y, ?_, Metric.mem_ball.mp hy⟩
  simpa [fellCompactification] using hwQ

theorem locallyFellConverges_eventually_disjoint_compact
    {A : ℕ → Set Plane} {L C : Set Plane} (hconv : LocallyFellConverges A L)
    (hC : IsCompact C) (hLC : Disjoint L C) :
    ∀ᶠ n in atTop, Disjoint (A n) C := by
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
  have hlimit : fellCompactification L hL ∈ V := by
    intro z hzQ hzC'
    rcases hzC' with ⟨c, hcC, rfl⟩
    have hcL : c ∈ L := by
      simpa [fellCompactification] using hzQ
    exact Set.disjoint_left.mp hLC hcL hcC
  filter_upwards [hconv (hVopen.mem_nhds hlimit)] with n hn
  rw [Set.disjoint_left]
  intro x hxA hxC
  have hxQ : (x : OnePoint Tiling.Plane) ∈
      (fellCompactification (A n) (hA n) :
        Set (OnePoint Tiling.Plane)) := by
    simp [fellCompactification, hxA]
  exact hn hxQ ⟨x, hxC, rfl⟩

theorem locallyFell_iff_hit_miss (S : ℕ → Set Plane) (L : Set Plane) :
    LocallyFellConverges S L ↔
      (∀ n, IsClosed (S n)) ∧ IsClosed L ∧
      (∀ x ∈ L, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∃ y ∈ S n, dist y x < ε) ∧
      (∀ C : Set Plane, IsCompact C → Disjoint L C →
        ∀ᶠ n in atTop, Disjoint (S n) C) := by
  constructor
  · rintro ⟨hS, hL, hconv⟩
    refine ⟨hS, hL, ?_, ?_⟩
    · intro x hx ε hε
      exact locallyFellConverges_eventually_exists_mem_ball
        ⟨hS, hL, hconv⟩ hx hε
    · intro C hC hLC
      exact locallyFellConverges_eventually_disjoint_compact
        ⟨hS, hL, hconv⟩ hC hLC
  · rintro ⟨hS, hL, hhit, hmiss⟩
    let Kseq : ℕ → TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) :=
      fun n ↦ fellCompactification (S n) (hS n)
    let Klim : TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) :=
      fellCompactification L hL
    refine ⟨hS, hL, ?_⟩
    change Filter.Tendsto Kseq Filter.atTop (nhds Klim)
    rw [Filter.tendsto_def]
    intro N hN
    obtain ⟨B, hBbasis, hKlimB, hBN⟩ :=
      TopologicalSpace.NonemptyCompacts.isTopologicalBasis.mem_nhds_iff.mp hN
    rcases hBbasis with ⟨u, hu, rfl⟩
    rcases hu with ⟨hufinite, hunonempty, huopen⟩
    rcases hKlimB with ⟨hKsubset, hKhit⟩
    have hinftyUnion : OnePoint.infty ∈ ⋃₀ u :=
      hKsubset (by simp [Klim, fellCompactification])
    have hUnionOpen : IsOpen (⋃₀ u) := isOpen_sUnion huopen
    let C : Set Tiling.Plane :=
      (fun x : Tiling.Plane ↦ (x : OnePoint Tiling.Plane)) ⁻¹' (⋃₀ u)ᶜ
    have hCclosedCompact : IsClosed C ∧ IsCompact C := by
      have hneigh := (OnePoint.isOpen_iff_of_mem hinftyUnion).mp hUnionOpen
      simpa [C, preimage_compl] using hneigh
    have hCL : Disjoint C L := by
      rw [Set.disjoint_left]
      intro x hxC hxL
      exact hxC (hKsubset (by simp [Klim, fellCompactification, hxL]))
    have hsubsetEventually : ∀ᶠ n in Filter.atTop,
        (Kseq n : Set (OnePoint Tiling.Plane)) ⊆ ⋃₀ u := by
      filter_upwards [hmiss C hCclosedCompact.2 hCL.symm] with n havoid
      intro z hz
      induction z using OnePoint.rec with
      | infty => exact hinftyUnion
      | coe y =>
          have hyS : y ∈ S n := by simpa [Kseq, fellCompactification] using hz
          by_contra hyUnion
          have hyC : y ∈ C := hyUnion
          exact Set.disjoint_left.mp havoid hyS hyC
    have hhitEventually : ∀ᶠ n in Filter.atTop,
        ∀ U ∈ u, ((Kseq n : Set (OnePoint Tiling.Plane)) ∩ U).Nonempty := by
      rw [hufinite.eventually_all]
      intro U hU
      obtain ⟨z, hzK, hzU⟩ := hKhit U hU
      induction z using OnePoint.rec with
      | infty =>
          exact Filter.Eventually.of_forall fun n ↦
            ⟨OnePoint.infty, by simp [Kseq, fellCompactification], hzU⟩
      | coe x =>
          have hxL : x ∈ L := by simpa [Klim, fellCompactification] using hzK
          have hUopen : IsOpen U := huopen U hU
          let V : Set Tiling.Plane :=
            (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) ⁻¹' U
          have hVopen : IsOpen V := hUopen.preimage OnePoint.continuous_coe
          have hxV : x ∈ V := hzU
          obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hxV)
          filter_upwards [hhit x hxL rho hrho] with n hn
          obtain ⟨y, hyS, hy⟩ := hn
          have hyV : y ∈ V := hball (Metric.mem_ball.mpr hy)
          exact ⟨(y : OnePoint Tiling.Plane), by simp [Kseq, fellCompactification, hyS], hyV⟩
    filter_upwards [hsubsetEventually, hhitEventually] with n hsubset hhits
    apply hBN
    exact ⟨hsubset, hhits⟩

theorem mem_of_locallyFellConverges_of_tendsto_mem
    {A : ℕ → Set Plane} {L : Set Plane} (hconv : LocallyFellConverges A L)
    {zseq : ℕ → Plane} {z : Plane} (hzmem : ∀ n, zseq n ∈ A n)
    (hzlim : Tendsto zseq atTop (𝓝 z)) : z ∈ L := by
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

private theorem isDiscrete_of_uniformlySeparated
    {δ : ℝ} (hδ : 0 < δ) {S : Set Tiling.Plane}
    (hS : IsUniformlySeparated δ S) :
    IsDiscrete S := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  refine ⟨Metric.ball x δ, Metric.isOpen_ball, ?_⟩
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
    exact ⟨Metric.mem_ball_self hδ, hx⟩


theorem locallyFell_matchingPoints
    {δ : ℝ} (hδ : 0 < δ) {S : ℕ → Set Plane} {L : Set Plane}
    (hclosedS : ∀ n, IsClosed (S n)) (hclosedL : IsClosed L)
    (hsepS : ∀ n, IsUniformlySeparated δ (S n))
    (hsepL : IsUniformlySeparated δ L) :
    LocallyFellConverges S L ↔
      ∀ C : Set Plane, IsCompact C → ∀ ε : ℝ, 0 < ε → ε < δ / 3 →
        ∀ᶠ n in atTop,
          (∀ x ∈ L ∩ C, ∃! y : Plane, y ∈ S n ∧ dist x y < ε) ∧
          (∀ y ∈ S n ∩ C, ∃! x : Plane, x ∈ L ∧ dist x y < ε) := by
  constructor
  · intro hconv C hC epsilon hepsilon hepsilonDelta
    have hfinite : (L ∩ C).Finite :=
      (hC.inter_left hclosedL).finite
        ((isDiscrete_of_uniformlySeparated hδ hsepL).mono inter_subset_left)
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
      fun n ↦ fellCompactification (S n) (hclosedS n)
    let Klim : TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) :=
      fellCompactification L hclosedL
    rw [show (fun n ↦ fellCompactification
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
      hKsubset (by simp [Klim, fellCompactification])
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
        simp [Klim, fellCompactification, hxL]))
    obtain ⟨r, hrpos, hrsep⟩ :=
      Metric.exists_pos_forall_lt_edist hCclosedCompact.2 hclosedL hCL
    let epsilon : ℝ := min ((r : ℝ) / 2) (δ / 6)
    have hepsilon : 0 < epsilon := by
      dsimp [epsilon]
      exact lt_min (by positivity) (by positivity)
    have hepsilonDelta : epsilon < δ / 3 := by
      dsimp [epsilon]
      have := min_le_right ((r : ℝ) / 2) (δ / 6)
      linarith
    have hepsilonR : epsilon < (r : ℝ) := by
      dsimp [epsilon]
      have := min_le_left ((r : ℝ) / 2) (δ / 6)
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
            simpa [Kseq, fellCompactification] using hz
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
              fellCompactification], hzU⟩
      | coe x =>
          have hxL : x ∈ L := by
            simpa [Klim, fellCompactification] using hzK
          have hUopen : IsOpen U := huopen U hU
          let V : Set Tiling.Plane :=
            (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) ⁻¹' U
          have hVopen : IsOpen V := hUopen.preimage OnePoint.continuous_coe
          have hxV : x ∈ V := hzU
          obtain ⟨rho, hrho, hball⟩ :=
            Metric.mem_nhds_iff.mp (hVopen.mem_nhds hxV)
          let eta : ℝ := min (rho / 2) (δ / 6)
          have heta : 0 < eta := by
            dsimp [eta]
            exact lt_min (by positivity) (by positivity)
          have hetaDelta : eta < δ / 3 := by
            dsimp [eta]
            have := min_le_right (rho / 2) (δ / 6)
            linarith
          have hetaRho : eta < rho := by
            dsimp [eta]
            have := min_le_left (rho / 2) (δ / 6)
            linarith
          filter_upwards [hmatch {x} isCompact_singleton eta heta hetaDelta] with n hn
          obtain ⟨y, ⟨hyS, hxy⟩, _⟩ := hn.1 x ⟨hxL, mem_singleton x⟩
          refine ⟨(y : OnePoint Tiling.Plane), ?_, ?_⟩
          · simp [Kseq, fellCompactification, hyS]
          · apply hball
            rw [Metric.mem_ball, dist_comm]
            exact hxy.trans hetaRho
    filter_upwards [hsubsetEventually, hhitEventually] with n hnsubset hnhit
    apply hBN
    exact ⟨hnsubset, hnhit⟩

theorem exists_locallyFellConvergent_subsequence
    (δ : ℝ) (hδ : 0 < δ) (S : ℕ → Set Plane)
    (hclosed : ∀ n, IsClosed (S n))
    (hsep : ∀ n, IsUniformlySeparated δ (S n)) :
    ∃ (φ : ℕ → ℕ) (L : Set Plane), StrictMono φ ∧ IsClosed L ∧
      IsUniformlySeparated δ L ∧ LocallyFellConverges (S ∘ φ) L := by
  classical
  have hδ_pos : 0 < δ := hδ
  let e := onePointEquivSphereOfFinrankEq
    (ι := Fin 3) (V := Tiling.Plane) (by simp [Tiling.Plane])
  let _ : TopologicalSpace.MetrizableSpace (OnePoint Tiling.Plane) :=
    e.isEmbedding.metrizableSpace
  let _ : MetricSpace (OnePoint Tiling.Plane) :=
    TopologicalSpace.metrizableSpaceMetric (OnePoint Tiling.Plane)
  let Kseq : ℕ → TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) :=
    fun n ↦ fellCompactification (S n) (hclosed n)
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
      simp [Kseq, fellCompactification,
        fellCompactification])
    simpa [C] using hKC
  let L : Set Tiling.Plane :=
    {x | (x : OnePoint Tiling.Plane) ∈ (K : Set (OnePoint Tiling.Plane))}
  have hLclosed : IsClosed L := by
    exact K.isCompact.isClosed.preimage OnePoint.continuous_coe
  have hK : fellCompactification L hLclosed = K := by
    apply TopologicalSpace.NonemptyCompacts.ext
    ext z
    refine OnePoint.rec ?_ (fun x ↦ ?_) z
    · simp [fellCompactification,
        fellCompactification, hinfty]
    · simp [fellCompactification,
        fellCompactification, L]
  have hLseparated :
      IsUniformlySeparated δ L := by
    intro x hx y hy hxy
    by_contra hdist
    have hdist_lt : dist x y < δ := lt_of_not_ge hdist
    have hxy_dist : 0 < dist x y := dist_pos.mpr hxy
    let eps : ℝ := min ((δ - dist x y) / 4) (dist x y / 4)
    have heps : 0 < eps := by
      dsimp [eps]
      exact lt_min (by linarith [hδ_pos]) (by linarith)
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
      simpa [Kseq, fellCompactification,
        fellCompactification] using hzuK
    have hbS : b ∈ S (phi n) := by
      simpa [Kseq, fellCompactification,
        fellCompactification] using hzvK
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
    have hsep := hsep (phi n) haS hbS hab
    have hax : dist a x < eps := by simpa [dist_comm] using ha
    have hyb : dist y b < eps := by simpa [dist_comm] using hb
    have heps_le : eps ≤ (δ - dist x y) / 4 := min_le_left _ _
    have hab_lt : dist a b < δ := by
      calc
        dist a b ≤ dist a x + dist x y + dist y b := dist_triangle4 _ _ _ _
        _ < eps + dist x y + eps := by linarith
        _ < δ := by linarith
    exact (not_lt_of_ge hsep) hab_lt
  refine ⟨phi, L, hphi, hLclosed, hLseparated, ?_⟩
  refine ⟨fun n ↦ hclosed (phi n), hLclosed, ?_⟩
  rw [hK]
  change Filter.Tendsto (Kseq ∘ phi) Filter.atTop (nhds K)
  exact hlim

theorem locallyFell_translate
    {S : ℕ → Set Plane} {L : Set Plane} (hconv : LocallyFellConverges S L)
    {g : ℕ → Plane} {u : Plane} (hg : Tendsto g atTop (𝓝 u)) :
    LocallyFellConverges (fun n => g n +ᵥ S n) (u +ᵥ L) := by
  have hsource := locallyFell_iff_hit_miss S L |>.mp hconv
  rcases hsource with ⟨hS, hL, hhit, hmiss⟩
  apply (locallyFell_iff_hit_miss (fun n => g n +ᵥ S n) (u +ᵥ L)).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact (Homeomorph.addLeft (g n)).isClosed_image.mpr (hS n)
  · exact (Homeomorph.addLeft u).isClosed_image.mpr hL
  · intro x hx ε hε
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
    have hnear : ∀ᶠ n in atTop, dist (g n) u < ε / 2 := by
      have := (Metric.tendsto_nhds.mp hg) (ε / 2) (half_pos hε)
      simpa [dist_comm] using this
    let l : Plane := -u + x
    filter_upwards [hnear, hhit l (by simpa [l] using hx) (ε / 2) (half_pos hε)] with n hgn hhitn
    obtain ⟨y, hyS, hyl⟩ := hhitn
    refine ⟨g n +ᵥ y, Set.mem_vadd_set.mpr ?_, ?_⟩
    · exact ⟨y, hyS, rfl⟩
    · have htri := dist_triangle (g n + y) (g n + l) x
      have hfirst : dist (g n + y) (g n + l) = dist y l := by
        simp [dist_eq_norm]
      have hsecond : dist (g n + l) x = dist (g n) u := by
        have harg : g n + l - x = g n - u := by dsimp [l]; abel
        simp [dist_eq_norm, harg]
      calc
        dist (g n + y) x ≤ dist (g n + y) (g n + l) + dist (g n + l) x := htri
        _ = dist y l + dist (g n) u := by rw [hfirst, hsecond]
        _ < ε := by linarith
  · intro C hC hCdisjoint
    let C' : Set Plane := (-u) +ᵥ C
    have hC'compact : IsCompact C' := by
      change IsCompact ((fun x : Plane => -u + x) '' C)
      exact hC.image (Homeomorph.addLeft (-u)).continuous
    have hLC' : Disjoint L C' := by
      rw [Set.disjoint_left]
      intro y hyL hyC'
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hyC'
      have : u +ᵥ y ∈ C := by simpa [vadd_vadd] using hyC'
      exact (Set.disjoint_left.mp hCdisjoint) (Set.mem_vadd_set.mpr ⟨y, hyL, rfl⟩) this
    obtain ⟨r, hr, hrsep⟩ := Metric.exists_pos_forall_lt_edist hC'compact hL hLC'.symm
    let ρ : ℝ := (r : ℝ) / 2
    have hρ : 0 < ρ := by dsimp [ρ]; exact half_pos (by exact_mod_cast hr)
    have hρr : ρ < (r : ℝ) := by dsimp [ρ]; exact half_lt_self (by exact_mod_cast hr)
    let D : Set Plane := C' + Metric.closedBall (0 : Plane) ρ
    have hDcompact : IsCompact D := by
      dsimp [D]
      exact hC'compact.add (isCompact_closedBall 0 ρ)
    have hLD : Disjoint L D := by
      rw [Set.disjoint_left]
      intro y hyL hyD
      rcases Set.mem_add.mp hyD with ⟨c, hcC', v, hv, rfl⟩
      have hdist : dist c (c + v) ≤ ρ := by
        simpa [dist_eq_norm, add_comm, add_left_comm, add_assoc] using
          (Metric.mem_closedBall.mp hv)
      have hdistlt : dist c (c + v) < (r : ℝ) := hdist.trans_lt hρr
      have hed : edist c (c + v) < (r : ENNReal) := by
        rw [edist_dist]
        exact (ENNReal.ofReal_lt_coe_iff (dist_nonneg)).mpr hdistlt
      exact (lt_asymm (hrsep c hcC' (c + v) hyL) hed).elim
    have havoid := hmiss D hDcompact hLD
    have hgn : ∀ᶠ n in atTop, dist (g n) u < ρ := by
      have := (Metric.tendsto_nhds.mp hg) ρ hρ
      simpa [dist_comm] using this
    filter_upwards [havoid, hgn] with n hnavoid hgn
    rw [Set.disjoint_left]
    rintro z hzImage hzC
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzImage
    have hy : -g n +ᵥ z ∈ S n := by simpa using hzImage
    have hyD : -g n +ᵥ z ∈ D := by
      apply Set.mem_add.mpr
      refine ⟨-u +ᵥ z, ?_, u - g n, ?_, ?_⟩
      · exact Set.mem_vadd_set.mpr ⟨z, hzC, rfl⟩
      · rw [Metric.mem_closedBall, dist_eq_norm]
        simpa [dist_eq_norm, norm_sub_rev] using hgn.le
      · change -u + z + (u - g n) = -g n + z
        abel
    exact Set.disjoint_left.mp hnavoid hy hyD

private theorem locallyFell_linearImage_forward
    (A : Plane ≃L[ℝ] Plane) (S : ℕ → Set Plane) (L : Set Plane)
    (hconv : LocallyFellConverges S L) :
    LocallyFellConverges (fun n => A '' S n) (A '' L) := by
  rcases (locallyFell_iff_hit_miss S L).mp hconv with
    ⟨hS, hL, hhit, hmiss⟩
  apply (locallyFell_iff_hit_miss (fun n => A '' S n) (A '' L)).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact A.isClosed_image.mpr (hS n)
  · exact A.isClosed_image.mpr hL
  · intro x hx ε hε
    rcases hx with ⟨z, hzL, rfl⟩
    let V : Set Plane := A ⁻¹' Metric.ball (A z) ε
    have hVopen : IsOpen V := Metric.isOpen_ball.preimage A.continuous
    have hzV : z ∈ V := Metric.mem_ball_self hε
    obtain ⟨ρ, hρ, hball⟩ :=
      Metric.mem_nhds_iff.mp (hVopen.mem_nhds hzV)
    filter_upwards [hhit z hzL ρ hρ] with n hn
    obtain ⟨y, hyS, hy⟩ := hn
    refine ⟨A y, ⟨y, hyS, rfl⟩, ?_⟩
    exact Metric.mem_ball.mp (hball (Metric.mem_ball.mpr hy))
  · intro C hC hCdisjoint
    let C' : Set Plane := A ⁻¹' C
    have hC'compact : IsCompact C' := by
      exact A.toHomeomorph.isCompact_preimage.mpr hC
    have hLC' : Disjoint L C' := by
      rw [Set.disjoint_left]
      intro x hxL hxC'
      exact (Set.disjoint_left.mp hCdisjoint)
        ⟨x, hxL, rfl⟩ hxC'
    filter_upwards [hmiss C' hC'compact hLC'] with n havoid
    rw [Set.disjoint_left]
    rintro z hzImage hzC
    rcases hzImage with ⟨y, hyS, rfl⟩
    exact Set.disjoint_left.mp havoid hyS hzC


theorem locallyFell_linearImage_iff (A : Plane ≃L[ℝ] Plane)
    (S : ℕ → Set Plane) (L : Set Plane) :
    LocallyFellConverges (fun n => A '' S n) (A '' L) ↔
      LocallyFellConverges S L := by
  constructor
  · intro hconv
    have hback := locallyFell_linearImage_forward A.symm
      (fun n => A '' S n) (A '' L) hconv
    simpa [Function.comp_def, Set.image_image] using hback
  · exact locallyFell_linearImage_forward A S L

theorem _root_.Tiling.Polygonal.HasFLC.locallyFell_limit_of_translates
    {S L : Set Plane} {u : ℕ → Plane} (hS : Tiling.Polygonal.HasFLC S)
    (hconv : LocallyFellConverges (fun n => u n +ᵥ S) L) :
    Tiling.Polygonal.HasFLC L := by
  classical
  obtain ⟨δ, hδ, hsep⟩ := hS.uniformlyDiscrete
  have hsepSeq : ∀ n, IsUniformlySeparated δ (u n +ᵥ S) := by
    intro n x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Set.mem_vadd_set.mp hx
    obtain ⟨b, hb, rfl⟩ := Set.mem_vadd_set.mp hy
    have hab : a ≠ b := by
      intro hab
      exact hxy (by simp [hab])
    simpa only [dist_vadd_cancel_left] using hsep ha hb hab
  have hsepL : IsUniformlySeparated δ L := by
    intro x hx y hy hxy
    by_contra hdist
    have hdist_lt : dist x y < δ := lt_of_not_ge hdist
    have hxy_dist : 0 < dist x y := dist_pos.mpr hxy
    let ε : ℝ := min ((δ - dist x y) / 4) (dist x y / 4)
    have hε : 0 < ε := by
      dsimp [ε]
      exact lt_min (by linarith) (by linarith)
    obtain ⟨n, ⟨a, ha, hax⟩, ⟨b, hb, hby⟩⟩ :=
      ((locallyFellConverges_eventually_exists_mem_ball hconv hx hε).and
        (locallyFellConverges_eventually_exists_mem_ball hconv hy hε)).exists
    have hab : a ≠ b := by
      intro hab
      subst b
      have htri := dist_triangle x a y
      have heps_le : ε ≤ dist x y / 4 := min_le_right _ _
      rw [dist_comm x a] at htri
      linarith
    have hsepab := hsepSeq n ha hb hab
    have heps_le : ε ≤ (δ - dist x y) / 4 := min_le_left _ _
    have htri := dist_triangle4 a x y b
    rw [dist_comm y b] at htri
    linarith
  have hclosedL : IsClosed L := hconv.choose_spec.choose
  refine ⟨?_, ?_⟩
  · intro Q hQ
    obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : Plane)
    have hfinite : (L ∩ Metric.closedBall 0 R).Finite :=
      ((isCompact_closedBall (0 : Plane) R).inter_left hclosedL).finite
        ((isDiscrete_of_uniformlySeparated hδ hsepL).mono inter_subset_left)
    exact hfinite.subset (inter_subset_inter_right L hR)
  · intro R hR
    let D : Set Plane := (S - S) ∩ Metric.closedBall 0 (R + 1)
    have hD : D.Finite := hS.2 (R + 1) (by linarith)
    apply hD.subset
    rintro z ⟨hz, hzR⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_sub.mp hz
    apply hD.isClosed.closure_subset
    rw [Metric.mem_closure_iff]
    intro ε hε
    let η : ℝ := min (ε / 4) (1 / 4)
    have hη : 0 < η := lt_min (by positivity) (by norm_num)
    obtain ⟨n, ⟨a, ha, hax⟩, ⟨b, hb, hby⟩⟩ :=
      ((locallyFellConverges_eventually_exists_mem_ball hconv hx hη).and
        (locallyFellConverges_eventually_exists_mem_ball hconv hy hη)).exists
    obtain ⟨a', ha', rfl⟩ := Set.mem_vadd_set.mp ha
    obtain ⟨b', hb', rfl⟩ := Set.mem_vadd_set.mp hb
    have hdiff : dist (x - y) (a' - b') < 2 * η := by
      have hdist := dist_sub_sub_le x y (u n +ᵥ a') (u n +ᵥ b')
      simp only [vadd_eq_add, add_sub_add_left_eq_sub] at hdist
      simp only [vadd_eq_add] at hax hby
      rw [dist_comm x (u n + a')] at hdist
      rw [dist_comm y (u n + b')] at hdist
      linarith
    refine ⟨a' - b', ⟨Set.sub_mem_sub ha' hb', ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall] at hzR ⊢
      have htri := dist_triangle (a' - b') (x - y) 0
      have hηle : η ≤ 1 / 4 := min_le_right _ _
      rw [dist_comm (a' - b') (x - y)] at htri
      linarith
    · have hηle : η ≤ ε / 4 := min_le_left _ _
      linarith

end Tiling.Topology
