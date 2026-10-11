import Tiling.AxisParallel.Continuous.WeakTilingTopology
import Mathlib.Analysis.Real.Cardinality

/-!
# Localizing failure of finite local complexity

This module extracts varying local displacements, classifies the horizontal symmetry group of a
proper periodic vertical carrier, constructs coarsely dense boundary anchors, and localizes
failure of finite local complexity into an anchored orbit limit with an eventually absent centre.
-/

open Function Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Continuous

/-- A non-FLC uniformly separated, locally finite set has a bounded convergent sequence of
pairwise distinct nonzero differences, none equal to its nonzero limit. -/
theorem exists_varyingDisplacement_of_not_hasFLC
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S : Set E} {delta : ℝ} (hdelta : 0 < delta)
    (hsep : Tiling.AxisParallel.Topology.IsUniformlySeparated delta S)
    (hloc : ∀ Q : Set E, Bornology.IsBounded Q → (S ∩ Q).Finite)
    (hnot : ¬ Tiling.AxisParallel.HasFLC S) :
    ∃ (R : ℝ) (t s : ℕ → E) (r : E),
      0 < R ∧
      (∀ n : ℕ, t n ∈ S ∧ s n ∈ S) ∧
      (∀ n : ℕ, 0 < dist (t n) (s n) ∧ dist (t n) (s n) ≤ R) ∧
      Function.Injective (s - t) ∧ Filter.Tendsto (s - t) Filter.atTop (nhds r) ∧
      r ≠ 0 ∧ ∀ n : ℕ, s n - t n ≠ r := by
  classical
  have hfail : ¬ ∀ R : ℝ, 0 < R → ((S - S) ∩ Metric.closedBall 0 R).Finite := by
    intro h
    exact hnot ⟨hloc, h⟩
  push Not at hfail
  obtain ⟨R, hR, hDnotfinite⟩ := hfail
  let D : Set E := (S - S) ∩ Metric.closedBall 0 R
  have hDinf : D.Infinite := Set.not_finite.mp hDnotfinite
  have hD0inf : (D \ {0}).Infinite := hDinf.sdiff (Set.finite_singleton (0 : E))
  let e : ℕ ↪ {x : E // x ∈ D \ {0}} :=
    Set.Infinite.natEmbedding (D \ {0}) hD0inf
  let d : ℕ → E := fun n ↦ e n
  have hdmem (n : ℕ) : d n ∈ S - S := (e n).2.1.1
  choose s₀ hs₀ t₀ ht₀ hst using fun n ↦ hdmem n
  have hd_eq (n : ℕ) : d n = s₀ n - t₀ n := (hst n).symm
  have hdclosed (n : ℕ) : d n ∈ Metric.closedBall 0 R := (e n).2.1.2
  obtain ⟨r, hrball, phi, hphi, hlim⟩ :=
    (isCompact_closedBall (0 : E) R).tendsto_subseq hdclosed
  let t₁ : ℕ → E := t₀ ∘ phi
  let s₁ : ℕ → E := s₀ ∘ phi
  have hdiff₁ : s₁ - t₁ = d ∘ phi := by
    funext n
    simp only [Pi.sub_apply, s₁, t₁, Function.comp_apply, hd_eq]
  have hinj₁ : Function.Injective (s₁ - t₁) := by
    rw [hdiff₁]
    intro a b hab
    apply hphi.injective
    apply e.injective
    exact Subtype.ext hab
  have hlim₁ : Filter.Tendsto (s₁ - t₁) Filter.atTop (nhds r) := by
    rw [hdiff₁]
    exact hlim
  have hdist_lower (n : ℕ) : delta ≤ dist (t₁ n) (s₁ n) := by
    apply hsep (ht₀ (phi n)) (hs₀ (phi n))
    intro heq
    have : d (phi n) = 0 := by rw [hd_eq, heq, sub_self]
    exact (e (phi n)).2.2 (by simpa [d] using this)
  have hrne : r ≠ 0 := by
    have hclosed : IsClosed {x : E | delta ≤ dist 0 x} :=
      isClosed_le continuous_const (continuous_const.dist continuous_id)
    have hrmem : r ∈ {x : E | delta ≤ dist 0 x} := hclosed.mem_of_tendsto hlim₁ <|
      Filter.Eventually.of_forall fun n ↦ by
        change delta ≤ dist 0 ((s₁ - t₁) n)
        simpa only [Pi.sub_apply, dist_zero_right, dist_eq_norm, norm_sub_rev, sub_zero]
          using hdist_lower n
    intro hr0
    rw [hr0] at hrmem
    exact (not_le_of_gt hdelta) (by simpa using hrmem)
  have package (psi : ℕ → ℕ) (hpsi : Function.Injective psi)
      (hpsiTop : Filter.Tendsto psi Filter.atTop Filter.atTop)
      (havoid : ∀ n, (s₁ - t₁) (psi n) ≠ r) :
      ∃ (R : ℝ) (t s : ℕ → E) (r : E),
        0 < R ∧ (∀ n, t n ∈ S ∧ s n ∈ S) ∧
        (∀ n, 0 < dist (t n) (s n) ∧ dist (t n) (s n) ≤ R) ∧
        Function.Injective (s - t) ∧ Filter.Tendsto (s - t) Filter.atTop (nhds r) ∧
        r ≠ 0 ∧ ∀ n, s n - t n ≠ r := by
    refine ⟨R, t₁ ∘ psi, s₁ ∘ psi, r, hR, ?_, ?_, ?_, ?_, hrne, ?_⟩
    · intro n
      exact ⟨ht₀ (phi (psi n)), hs₀ (phi (psi n))⟩
    · intro n
      have hpos := hdist_lower (psi n)
      have hupper : dist (t₁ (psi n)) (s₁ (psi n)) ≤ R := by
        have hm := hdclosed (phi (psi n))
        rw [Metric.mem_closedBall] at hm
        simpa only [hd_eq, t₁, s₁, Function.comp_apply, dist_eq_norm, sub_zero,
          norm_sub_rev]
          using hm
      exact ⟨hdelta.trans_le hpos, hupper⟩
    · have heq : (s₁ ∘ psi) - (t₁ ∘ psi) = (s₁ - t₁) ∘ psi := by
        funext n
        rfl
      rw [heq]
      exact hinj₁.comp hpsi
    · have heq : (s₁ ∘ psi) - (t₁ ∘ psi) = (s₁ - t₁) ∘ psi := by
        funext n
        rfl
      rw [heq]
      exact hlim₁.comp hpsiTop
    · intro n
      exact havoid n
  by_cases heq : ∃ k, (s₁ - t₁) k = r
  · obtain ⟨k, hk⟩ := heq
    let psi : ℕ → ℕ := fun n ↦ n + (k + 1)
    apply package psi
    · intro a b hab
      exact Nat.add_right_cancel hab
    · exact Filter.tendsto_add_atTop_nat (k + 1)
    · intro n hn
      have := hinj₁ (hn.trans hk.symm)
      have hnk : n + (k + 1) ≠ k := by omega
      exact hnk this
  · apply package id Function.injective_id Filter.tendsto_id
    intro n hn
    exact heq ⟨n, hn⟩

/-- The displacement extraction needed by localization does not use the carrier's properness or
period structure; those hypotheses are retained only by the frozen public interface. -/
theorem exists_varyingLocalDisplacement
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (_hXnonempty : X.Nonempty) (_hXopen : IsOpen X)
    (_hXregular : interior (closure X) = X) (_hXproper : X ≠ Set.univ)
    {beta0 : ℝ} (_hbeta0 : 0 < beta0)
    (_hXperiod : ∀ x : ℝ, x + beta0 ∈ X ↔ x ∈ X)
    (T : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    (hTnonFLC : ¬ Tiling.AxisParallel.HasFLC (T.centres : Set Tiling.Plane)) :
    ∃ (R : ℝ) (t s : ℕ → Tiling.Plane) (r : Tiling.Plane),
      0 < R ∧
      (∀ n : ℕ, t n ∈ (T.centres : Set Tiling.Plane) ∧
        s n ∈ (T.centres : Set Tiling.Plane)) ∧
      (∀ n : ℕ, 0 < dist (t n) (s n) ∧ dist (t n) (s n) ≤ R) ∧
      Function.Injective (s - t) ∧ Filter.Tendsto (s - t) Filter.atTop (nhds r) ∧
      r ≠ 0 ∧ ∀ n : ℕ, s n - t n ≠ r := by
  obtain ⟨delta, hdelta, hsep⟩ := tilesOn_uniformlySeparated K
  apply exists_varyingDisplacement_of_not_hasFLC hdelta
    (hsep _ _ T.tilesOn) _ hTnonFLC
  intro Q hQ
  exact (Tiling.AxisParallel.IsPacking.locallyFinite_centres T.tilesOn.2.1).1 Q hQ
private lemma cylinder_period_iff {X : Set ℝ} (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X) (g : Tiling.Plane) :
    g ∈ Tiling.AxisParallel.aePeriodGroup {z : Tiling.Plane | z.re ∈ X} ↔
      ∀ x : ℝ, x + g.re ∈ X ↔ x ∈ X := by
  rw [Tiling.AxisParallel.aePeriodGroup_eq_periodGroup_of_regularOpen]
  · change g +ᵥ ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) = _ ↔ _
    constructor
    · intro h x
      have hz := Set.ext_iff.mp h ((x + g.re : ℝ) : ℂ)
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm, add_left_comm,
        add_assoc] using hz.symm
    · intro h
      ext z
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_ofPred_eq, vadd_eq_add,
        Complex.add_re, Complex.neg_re]
      have := h (z.re - g.re)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm
  · exact hXopen.preimage Complex.continuous_re
  · change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hXregular]

/-- The a.e. period group of a nonempty proper periodic vertical cylinder has a least positive
horizontal period; its imaginary component remains unrestricted. -/
theorem properVerticalCarrier_horizontalPeriodGroup
    {X : Set ℝ} (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X) (hXproper : X ≠ Set.univ)
    {beta0 : ℝ} (hbeta0 : 0 < beta0)
    (hXperiod : ∀ x : ℝ, x + beta0 ∈ X ↔ x ∈ X) :
    ∃ beta : ℝ, 0 < beta ∧
      ∀ g : Tiling.Plane,
        g ∈ Tiling.AxisParallel.aePeriodGroup
          {z : Tiling.Plane | z.re ∈ X} ↔
        ∃ m : ℤ, g.re = (m : ℝ) * beta := by
  let D : Set Tiling.Plane := {z | z.re ∈ X}
  let H : AddSubgroup ℝ :=
    (Tiling.AxisParallel.aePeriodGroup D).comap Complex.ofRealAm.toAddMonoidHom
  have hH (a : ℝ) : a ∈ H ↔ ∀ x : ℝ, x + a ∈ X ↔ x ∈ X := by
    change (a : ℂ) ∈ Tiling.AxisParallel.aePeriodGroup D ↔ _
    exact cylinder_period_iff hXopen hXregular (a : ℂ)
  have hbeta0H : beta0 ∈ H := (hH beta0).mpr hXperiod
  rcases H.dense_or_cyclic with hHdense | ⟨a, ha⟩
  · exfalso
    obtain ⟨x0, hx0⟩ := hXnonempty
    have hsubset : x0 +ᵥ (H : Set ℝ) ⊆ X := by
      rintro y ⟨u, hu, rfl⟩
      exact ((hH u).mp hu x0).mpr hx0
    have hclosure : closure X = Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      have hy : y ∈ closure (x0 +ᵥ (H : Set ℝ)) := by
        rw [closure_vadd, hHdense.closure_eq]
        simp
      exact closure_mono hsubset hy
    apply hXproper
    rw [← hXregular, hclosure, interior_univ]
  · rw [← AddSubgroup.zmultiples_eq_closure] at ha
    have ha0 : a ≠ 0 := by
      intro ha0
      have : H = ⊥ := by simpa [ha0] using ha
      rw [this] at hbeta0H
      exact hbeta0.ne' (by simpa using hbeta0H)
    let beta := |a|
    have hbeta : 0 < beta := abs_pos.mpr ha0
    refine ⟨beta, hbeta, ?_⟩
    intro g
    have hgH : g ∈ Tiling.AxisParallel.aePeriodGroup D ↔ g.re ∈ H := by
      rw [cylinder_period_iff hXopen hXregular g, hH]
    rw [show {z : Tiling.Plane | z.re ∈ X} = D from rfl, hgH, ha]
    constructor
    · intro hg
      obtain ⟨m, hm⟩ := hg
      by_cases haPos : 0 < a
      · refine ⟨m, ?_⟩
        simpa [beta, abs_of_pos haPos] using hm.symm
      · refine ⟨-m, ?_⟩
        rw [← hm]
        simp [beta, abs_of_nonpos (le_of_not_gt haPos)]
    · rintro ⟨m, hm⟩
      by_cases haPos : 0 < a
      · refine ⟨m, ?_⟩
        simpa [beta, abs_of_pos haPos] using hm.symm
      · refine ⟨-m, ?_⟩
        rw [hm]
        simp [beta, abs_of_nonpos (le_of_not_gt haPos)]

private theorem finiteLines_vertical {D : Set Tiling.Plane} (V H : Finset ℝ)
    (hl : ∀ z ∈ frontier D, z.re ∈ V ∨ z.im ∈ H) {p : Tiling.Plane} (hpH : p.im ∉ H) :
    ∃ r > 0, ∀ z ∈ Metric.ball p r, z ∈ frontier D → z.re = p.re := by
  let B : Set ℝ := (V : Set ℝ) \ {p.re}
  have hpB : p.re ∉ B := by simp [B]
  have hBc : IsClosed B := (show B.Finite from V.finite_toSet.sdiff).isClosed
  have hHc : IsClosed (H : Set ℝ) := H.finite_toSet.isClosed
  have he : ∀ᶠ z in nhds p, z.re ∉ B ∧ z.im ∉ (H : Set ℝ) :=
    Filter.inter_mem
      (Complex.continuous_re.continuousAt.eventually (hBc.isOpen_compl.mem_nhds hpB))
      (Complex.continuous_im.continuousAt.eventually
        (hHc.isOpen_compl.mem_nhds (show p.im ∉ (H : Set ℝ) from hpH)))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r, hr, fun z hz hzf => ?_⟩
  rcases hl z hzf with hzV | hzH
  · by_contra hne; exact (hb hz).1 ⟨hzV, hne⟩
  · exact False.elim ((hb hz).2 hzH)

private theorem boundaryPoint_has_verticalEdgeAnchor
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (hXopen : IsOpen X) (hXregular : interior (closure X) = X)
    (T : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    (V H : Finset ℝ) (hlines : ∀ z ∈ frontier K.support, z.re ∈ V ∨ z.im ∈ H)
    {q : Tiling.Plane} (hq : q ∈ frontier ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane))
    (hbadV : ∀ a ∈ (T.centres : Set Tiling.Plane), ∀ v ∈ K.vertexFinset,
      q.im ≠ a.im + v.im)
    (hbadH : ∀ a ∈ (T.centres : Set Tiling.Plane), ∀ h ∈ H, q.im ≠ a.im + h) :
    ∃ a ∈ (T.centres : Set Tiling.Plane), ∃ p ∈ K.support, q = a + p ∧
      ∃ v ∈ K.vertexFinset, ∃ w ∈ K.vertexFinset, v ≠ w ∧ v.re = w.re ∧
        openSegment ℝ v w ⊆ frontier K.openCarrier ∧ v.re + a.re = q.re := by
  let D : Set Tiling.Plane := {z | z.re ∈ X}
  have hDo : IsOpen D := hXopen.preimage Complex.continuous_re
  have hDr : interior (closure D) = D := by
    change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hXregular]
  have hreg : Tiling.AxisParallel.regularSupport K (T.centres : Set Tiling.Plane) = D :=
    Tiling.AxisParallel.regularSupport_eq_of_tilesOn hDo hDr T.tilesOn
  have hqcl : q ∈ closure (Tiling.AxisParallel.openUnion K (T.centres : Set Tiling.Plane)) := by
    have h := frontier_subset_closure hq
    change q ∈ closure D at h
    rw [← hreg, Tiling.AxisParallel.regularSupport] at h
    simpa only [closure_closure] using closure_mono interior_subset h
  rw [Tiling.AxisParallel.closure_openUnion_eq_iUnion_support T.tilesOn.2.1] at hqcl
  obtain ⟨a, hqa⟩ := Set.mem_iUnion.mp hqcl
  let p := q - a.1
  have hqp : q = a.1 + p := by simp [p]
  have hp : p ∈ K.support := by
    simpa [p, mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg, add_comm] using hqa
  have hpni : p ∉ interior K.support := by
    intro hpi
    have hqo : q ∈ Tiling.AxisParallel.openUnion K (T.centres : Set Tiling.Plane) := by
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      refine ⟨a, ⟨p, hpi, hqp.symm⟩⟩
    have hopen : IsOpen (Tiling.AxisParallel.openUnion K (T.centres : Set Tiling.Plane)) := by
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier]
      exact isOpen_iUnion fun _ ↦ (isOpen_interior.vadd _)
    have hqD : q ∈ D := by
      rw [← hreg]
      exact hopen.subset_interior_closure hqo
    exact Set.disjoint_left.1 disjoint_interior_frontier (hDo.interior_eq ▸ hqD) hq
  have hpf : p ∈ frontier K.support := by
    rw [K.isPolygonal.isClosed.frontier_eq]; exact ⟨hp, hpni⟩
  have hpnv : p ∉ Tiling.vertexSet K.support := by
    intro hv
    have hvf : p ∈ K.vertexFinset := by
      change p ∈ (K.vertexFinset : Set Tiling.Plane)
      rw [K.coe_vertexFinset, K.vertices_eq_vertexSet]; exact hv
    apply hbadV a.1 a.2 p hvf
    rw [hqp]; simp
  have hpH : p.im ∉ H := by
    intro hh; apply hbadH a.1 a.2 p.im hh
    rw [hqp]; simp
  obtain ⟨r, hr, hs⟩ := finiteLines_vertical V H hlines hpH
  obtain ⟨r', hr', hg⟩ := K.isPolygonal.exists_ball_frontier_iff_verticalLine_of_subset
    hpf hpnv ⟨r, hr, hs⟩
  have hge : ∀ᶠ z in nhds p, z ∈ frontier K.support ↔ z.re = p.re :=
    Filter.mem_of_superset (Metric.ball_mem_nhds p hr') hg
  obtain ⟨v,w,hv,hw,hvw,hvert,hpseg,hedge⟩ :=
    K.isPolygonal.exists_intrinsic_vertical_edge_of_germ hpf hge
  refine ⟨a.1,a.2,p,hp,hqp,v,?_,w,?_,hvw,hvert,?_,?_⟩
  · change v ∈ (K.vertexFinset : Set Tiling.Plane)
    rw [K.coe_vertexFinset, K.vertices_eq_vertexSet]; exact hv
  · change w ∈ (K.vertexFinset : Set Tiling.Plane)
    rw [K.coe_vertexFinset, K.vertices_eq_vertexSet]; exact hw
  · rwa [K.frontier_openCarrier_eq_frontier_support]
  · have hvp : v.re = p.re := by
      rw [openSegment_eq_image] at hpseg
      obtain ⟨c, _hc, hcp⟩ := hpseg
      rw [← hcp]
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, hvert]
      ring
    rw [hqp]
    simp only [Complex.add_re]
    linarith
private theorem exists_int_period_near
    {beta : ℝ} (hbeta : 0 < beta) (x t : ℝ) :
    ∃ m : ℤ, |x + (m : ℝ) * beta - t| ≤ beta := by
  let q : ℝ := (t - x) / beta
  let m : ℤ := ⌊q⌋
  have hmle : (m : ℝ) * beta ≤ t - x := by
    exact (le_div_iff₀ hbeta).mp (Int.floor_le q)
  have hmlt : t - x < ((m : ℝ) + 1) * beta := by
    exact (div_lt_iff₀ hbeta).mp (Int.lt_floor_add_one q)
  refine ⟨m, ?_⟩
  rw [abs_of_nonpos (by linarith)]
  linarith

private theorem mem_iff_add_int_mul_period
    {X : Set ℝ} {beta : ℝ}
    (hperiod : ∀ y : ℝ, y + beta ∈ X ↔ y ∈ X) (m : ℤ) (y : ℝ) :
    y + (m : ℝ) * beta ∈ X ↔ y ∈ X := by
  induction m using Int.induction_on with
  | zero => simp
  | @succ n ih =>
      rw [Int.cast_add, Int.cast_one, add_mul, one_mul]
      rw [← add_assoc, hperiod, ih]
  | @pred n ih =>
      have hback (u : ℝ) : u - beta ∈ X ↔ u ∈ X := by
        have := hperiod (u - beta)
        simpa only [sub_add_cancel] using this.symm
      rw [Int.cast_sub, Int.cast_one, sub_mul, one_mul]
      have hb := hback (y + ((-(n : ℤ) : ℤ) : ℝ) * beta)
      convert hb.trans ih using 1
      ring_nf

private theorem frontier_add_int_mul_period
    {X : Set ℝ} {beta : ℝ}
    (hperiod : ∀ y : ℝ, y + beta ∈ X ↔ y ∈ X)
    {x : ℝ} (hx : x ∈ frontier X) (m : ℤ) :
    x + (m : ℝ) * beta ∈ frontier X := by
  let u : ℝ := (m : ℝ) * beta
  have htranslate : u +ᵥ X = X := by
    ext y
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change -u + y ∈ X ↔ y ∈ X
    have h := mem_iff_add_int_mul_period hperiod m (-u + y)
    simpa [u, add_assoc] using h.symm
  have hfrontier : u +ᵥ frontier X = frontier X := by
    have hi := (Homeomorph.vaddConst u).image_frontier X
    have hi' : u +ᵥ frontier X = frontier (u +ᵥ X) := by
      change (fun z ↦ u + z) '' frontier X = frontier ((fun z ↦ u + z) '' X)
      simpa [add_comm] using hi
    exact hi'.trans (congrArg frontier htranslate)
  rw [← hfrontier]
  exact ⟨x, hx, by simp [u, add_comm]⟩

private theorem exists_Ioo_not_mem_countable
    {B : Set ℝ} (hB : B.Countable) (t : ℝ) :
    ∃ y ∈ Set.Ioo (t - 1) (t + 1), y ∉ B := by
  by_contra h
  push Not at h
  have hsub : Set.Ioo (t - 1) (t + 1) ⊆ B := fun y hy ↦ h y hy
  have hcount : (Set.Ioo (t - 1) (t + 1)).Countable := hB.mono hsub
  rw [Cardinal.Real.Ioo_countable_iff] at hcount
  linarith


/-- Boundary edges on periodic carrier lines give uniformly nearby centre anchors. -/
theorem boundaryAnchors_coarselyDense
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (_hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X) (_hXproper : X ≠ Set.univ)
    {beta : ℝ} (hbeta : 0 < beta)
    (hXperiod : ∀ x : ℝ, x + beta ∈ X ↔ x ∈ X)
    (T : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    {x : ℝ} (hx : x ∈ frontier X) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t ∈ (T.centres : Set Tiling.Plane),
      ∃ a ∈ (T.centres : Set Tiling.Plane),
      dist a t ≤ C ∧
      ∃ v ∈ K.vertexFinset, ∃ w ∈ K.vertexFinset,
        v ≠ w ∧ v.re = w.re ∧
        openSegment ℝ v w ⊆ frontier K.openCarrier ∧
        ∃ m : ℤ, v.re + a.re = x + (m : ℝ) * beta := by
  classical
  obtain ⟨V, H, hlines⟩ := K.isAxisParallel.exists_finite_boundary_axisLines
  obtain ⟨R, hR⟩ := K.isPolygonal.isBounded.subset_closedBall (0 : Tiling.Plane)
  let F : Finset ℝ := H ∪ K.vertexFinset.image Complex.im
  let Bad : Set ℝ := (fun p : Tiling.Plane × ℝ ↦ p.1.im + p.2) ''
    ((T.centres : Set Tiling.Plane) ×ˢ (F : Set ℝ))
  have hBad : Bad.Countable := (T.tilesOn.1.prod F.finite_toSet.countable).image _
  refine ⟨max R 0 + beta + 2, by positivity, ?_⟩
  intro t _ht
  obtain ⟨m, hm⟩ := exists_int_period_near hbeta x t.re
  obtain ⟨y, hy, hyBad⟩ := exists_Ioo_not_mem_countable hBad t.im
  let q : Tiling.Plane := ((x + (m : ℝ) * beta : ℝ) : ℂ) + (y : ℂ) * Complex.I
  have hq : q ∈ frontier ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) := by
    rw [Tiling.AxisParallel.frontier_verticalCylinder]
    simpa [q] using frontier_add_int_mul_period hXperiod hx m
  have hbadV : ∀ a ∈ (T.centres : Set Tiling.Plane), ∀ v ∈ K.vertexFinset,
      q.im ≠ a.im + v.im := by
    intro a ha v hv heq
    apply hyBad
    refine ⟨(a, v.im), ⟨ha, ?_⟩, ?_⟩
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
    · simpa [q] using heq.symm
  have hbadH : ∀ a ∈ (T.centres : Set Tiling.Plane), ∀ h ∈ H,
      q.im ≠ a.im + h := by
    intro a ha h hh heq
    apply hyBad
    refine ⟨(a, h), ⟨ha, ?_⟩, ?_⟩
    · exact Finset.mem_union.mpr (Or.inl hh)
    · simpa [q] using heq.symm
  obtain ⟨a, ha, p, hp, hqp, v, hv, w, hw, hvw, hre, hedge, hanchor⟩ :=
    boundaryPoint_has_verticalEdgeAnchor hXopen hXregular T V H hlines hq hbadV hbadH
  have hpR : ‖p‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR hp
  have haq : dist a q ≤ max R 0 := by
    rw [hqp]
    have : dist a (a + p) = ‖p‖ := by simp [dist_eq_norm]
    rw [this]
    exact hpR.trans (le_max_left R 0)
  have hqt : dist q t ≤ beta + 1 := by
    rw [dist_eq_norm]
    calc
      ‖q - t‖ ≤ |(q - t).re| + |(q - t).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ beta + 1 := by
        apply add_le_add
        · simpa [q] using hm
        · have hyabs : |y - t.im| ≤ 1 := by
            rw [abs_le]
            constructor <;> linarith [hy.1, hy.2]
          simpa [q] using hyabs
  refine ⟨a, ha, ?_, v, hv, w, hw, hvw, hre, hedge, m, ?_⟩
  · exact (dist_triangle a q t).trans ((add_le_add haq hqt).trans (by linarith))
  · simpa [q] using hanchor


/-- Two centres anchored to the same vertical tile edge over one carrier-boundary orbit differ by
an a.e. carrier period. -/
theorem sameEdgeTypeAnchors_differByPeriod
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (_hXnonempty : X.Nonempty) (_hXopen : IsOpen X)
    (_hXregular : interior (closure X) = X) (_hXproper : X ≠ Set.univ)
    {beta : ℝ} (_hbeta : 0 < beta)
    (hGamma : ∀ g : Tiling.Plane,
      g ∈ Tiling.AxisParallel.aePeriodGroup {z : Tiling.Plane | z.re ∈ X} ↔
        ∃ m : ℤ, g.re = (m : ℝ) * beta)
    (T : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    {x : ℝ} (_hx : x ∈ frontier X)
    {a a' : Tiling.Plane}
    (_ha : a ∈ (T.centres : Set Tiling.Plane))
    (_ha' : a' ∈ (T.centres : Set Tiling.Plane))
    {v w : Tiling.Plane} (_hv : v ∈ K.vertexFinset) (_hw : w ∈ K.vertexFinset)
    (_hvw : v ≠ w) (_hvertical : v.re = w.re)
    (_hedge : openSegment ℝ v w ⊆ frontier K.openCarrier)
    (haAnchor : ∃ m : ℤ, v.re + a.re = x + (m : ℝ) * beta)
    (ha'Anchor : ∃ m : ℤ, v.re + a'.re = x + (m : ℝ) * beta) :
    a - a' ∈ Tiling.AxisParallel.aePeriodGroup
      {z : Tiling.Plane | z.re ∈ X} := by
  obtain ⟨m, hm⟩ := haAnchor
  obtain ⟨n, hn⟩ := ha'Anchor
  rw [hGamma]
  refine ⟨m - n, ?_⟩
  simp only [Complex.sub_re, Int.cast_sub]
  linarith

/-- Uniform separation alone makes a distinct convergent marked point eventually absent from
each set containing the corresponding sequence point. -/
theorem eventually_absent_of_uniformlySeparated
    {E : Type*} [PseudoMetricSpace E] {delta : ℝ} (hdelta : 0 < delta)
    {U : ℕ → Set E} (hsep : ∀ n,
      Tiling.AxisParallel.Topology.IsUniformlySeparated delta (U n))
    (zseq : ℕ → E) (z : E) (hzmem : ∀ n, zseq n ∈ U n)
    (hzlim : Filter.Tendsto zseq Filter.atTop (nhds z))
    (hzneq : ∀ n, zseq n ≠ z) :
    ∀ᶠ n : ℕ in Filter.atTop, z ∉ U n := by
  have hclose : ∀ᶠ n : ℕ in Filter.atTop, dist (zseq n) z < delta := by
    filter_upwards [hzlim.eventually (Metric.ball_mem_nhds z hdelta)] with n hn
    simpa only [Metric.mem_ball, dist_comm] using hn
  filter_upwards [hclose] with n hn hz
  exact (not_lt_of_ge (hsep n (hzmem n) hz (hzneq n))) hn

private theorem exists_sameLabel_injectiveRelative_subsequence
    {ι : Type*} [Finite ι] (label : ℕ → ι) (u v : ℕ → Tiling.Plane)
    (hsub : Function.Injective (u - v)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ (∃ c : ι, ∀ n, label (phi n) = c) ∧
      (Function.Injective (u ∘ phi) ∨ Function.Injective (v ∘ phi)) := by
  classical
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber label
  have hcf : ({n | label n = c} : Set ℕ).Infinite := by
    have hc' : (label ⁻¹' {c}).Infinite := Set.infinite_coe_iff.mp hc
    convert hc' using 1
    ext n
    simp
  let phi₀ : ℕ → ℕ := Nat.nth fun n ↦ label n = c
  have hphi₀ : StrictMono phi₀ := Nat.nth_strictMono hcf
  have hlabel (n : ℕ) : label (phi₀ n) = c :=
    Nat.nth_mem n (fun hf ↦ (hcf hf).elim)
  let U := u ∘ phi₀
  let V := v ∘ phi₀
  have hUV : Function.Injective (U - V) := by
    intro m n hmn
    apply hphi₀.injective
    apply hsub
    simpa only [U, V, Pi.sub_apply, Function.comp_apply] using hmn
  have hinf : (Set.range U).Infinite ∨ (Set.range V).Infinite := by
    by_contra h
    push Not at h
    have hUfin : (Set.range U).Finite := h.1
    have hVfin : (Set.range V).Finite := h.2
    have himage := (hUfin.prod hVfin).image
      (fun p : Tiling.Plane × Tiling.Plane ↦ p.1 - p.2)
    have hrange : Set.range (U - V) ⊆
        (fun p : Tiling.Plane × Tiling.Plane ↦ p.1 - p.2) ''
          (Set.range U ×ˢ Set.range V) := by
      rintro y ⟨n, rfl⟩
      exact ⟨(U n, V n), ⟨⟨n, rfl⟩, ⟨n, rfl⟩⟩, rfl⟩
    exact Set.infinite_range_of_injective hUV (himage.subset hrange)
  have select_injective {W : ℕ → Tiling.Plane} (hW : (Set.range W).Infinite) :
      ∃ theta : ℕ → ℕ, StrictMono theta ∧ Function.Injective (W ∘ theta) := by
    let _ : Infinite ↥(Set.range W) := hW.to_subtype
    let e : ℕ ↪ ↥(Set.range W) := Infinite.natEmbedding _
    let idx : ℕ → ℕ := fun n ↦ Classical.choose (e n).property
    have hidxW (n : ℕ) : W (idx n) = (e n : Tiling.Plane) :=
      Classical.choose_spec (e n).property
    have hidx : Function.Injective idx := by
      intro m n hmn
      apply e.injective
      apply Subtype.ext
      rw [← hidxW m, ← hidxW n, hmn]
    have hirange : (Set.range idx).Infinite := Set.infinite_range_of_injective hidx
    let theta : ℕ → ℕ := Nat.nth fun n ↦ n ∈ Set.range idx
    have htheta : StrictMono theta := Nat.nth_strictMono hirange
    refine ⟨theta, htheta, ?_⟩
    intro m n hmn
    obtain ⟨i, hi⟩ := Nat.nth_mem m (fun hf ↦ (hirange hf).elim)
    obtain ⟨j, hj⟩ := Nat.nth_mem n (fun hf ↦ (hirange hf).elim)
    have hi' : idx i = theta m := by simpa only [theta, Set.mem_range] using hi
    have hj' : idx j = theta n := by simpa only [theta, Set.mem_range] using hj
    apply htheta.injective
    have hWij : W (idx i) = W (idx j) := by
      rw [hi', hj']
      exact hmn
    have heij : e i = e j := by
      apply Subtype.ext
      simpa only [← hidxW i, ← hidxW j] using hWij
    exact hi'.symm.trans ((congrArg idx (e.injective heij)).trans hj')
  rcases hinf with hU | hV
  · obtain ⟨theta, htheta, hinj⟩ := select_injective hU
    refine ⟨phi₀ ∘ theta, hphi₀.comp htheta, ⟨c, fun n ↦ hlabel (theta n)⟩, Or.inl ?_⟩
    simpa only [U, Function.comp_assoc] using hinj
  · obtain ⟨theta, htheta, hinj⟩ := select_injective hV
    refine ⟨phi₀ ∘ theta, hphi₀.comp htheta, ⟨c, fun n ↦ hlabel (theta n)⟩, Or.inr ?_⟩
    simpa only [V, Function.comp_assoc] using hinj

private theorem injective_subsequence_avoiding_limit
    {f : ℕ → Tiling.Plane} {z : Tiling.Plane}
    (hinj : Function.Injective f)
    (hlim : Filter.Tendsto f Filter.atTop (nhds z)) :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ Function.Injective (f ∘ psi) ∧
      Filter.Tendsto (f ∘ psi) Filter.atTop (nhds z) ∧ ∀ n, f (psi n) ≠ z := by
  by_cases h : ∃ k, f k = z
  · obtain ⟨k, hk⟩ := h
    let psi : ℕ → ℕ := fun n ↦ n + (k + 1)
    have hpsi : StrictMono psi := strictMono_id.add_const _
    refine ⟨psi, hpsi, hinj.comp hpsi.injective, hlim.comp hpsi.tendsto_atTop, ?_⟩
    intro n hn
    have := hinj (hn.trans hk.symm)
    dsimp only [psi] at this
    omega
  · exact ⟨id, strictMono_id, hinj, by simpa using hlim,
      fun n hn ↦ h ⟨n, hn⟩⟩

private theorem exists_anchoredOrbitLimit_of_boundedMarkedCentres
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (T : Tiling.AxisParallel.Topology.TilingSpace K E)
    (g : ℕ → Tiling.AxisParallel.aePeriodGroup E)
    (a : Tiling.Plane) (zseq : ℕ → Tiling.Plane) {R : ℝ}
    (hzbound : ∀ n, zseq n ∈ Metric.closedBall a R)
    (hamem : ∀ n, a ∈
      ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
        Set Tiling.Plane))
    (hzmem : ∀ n, zseq n ∈
      ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
        Set Tiling.Plane))
    (hzinj : Function.Injective zseq) :
    ∃ (phi : ℕ → ℕ)
      (S : Tiling.AxisParallel.Topology.TilingSpace K E) (z : Tiling.Plane),
      StrictMono phi ∧
      S ∈ Tiling.AxisParallel.Topology.orbitHull T ∧
      Tiling.AxisParallel.Topology.LocallyFellConverges
        (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
          (Tiling.AxisParallel.Topology.TilingSpace.translateSequence (g ∘ phi) T))
        (S.centres : Set Tiling.Plane) ∧
      (∀ n, a ∈
        ((Tiling.AxisParallel.Topology.TilingSpace.translate (g (phi n)) T).centres :
          Set Tiling.Plane)) ∧
      a ∈ (S.centres : Set Tiling.Plane) ∧ z ∈ (S.centres : Set Tiling.Plane) ∧
      z ≠ a ∧ Function.Injective (zseq ∘ phi) ∧
      Filter.Tendsto (zseq ∘ phi) Filter.atTop (nhds z) := by
  let U : ℕ → Tiling.AxisParallel.Topology.TilingSpace K E :=
    Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T
  let _ : CompactSpace (Tiling.AxisParallel.Topology.TilingSpace K E) :=
    isCompact_univ_iff.mp (tilingSpace_compact K E)
  obtain ⟨S, phi₀, hphi₀, hUlim⟩ := CompactSpace.tendsto_subseq U
  obtain ⟨z, _hzball, phi₁, hphi₁, hzlim⟩ :=
    (isCompact_closedBall a R).tendsto_subseq (fun n ↦ hzbound (phi₀ n))
  let phi := phi₀ ∘ phi₁
  have hphi : StrictMono phi := hphi₀.comp hphi₁
  have hUlim' : Filter.Tendsto (U ∘ phi) Filter.atTop (nhds S) := by
    exact hUlim.comp hphi₁.tendsto_atTop
  have hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
        (Tiling.AxisParallel.Topology.TilingSpace.translateSequence (g ∘ phi) T))
      (S.centres : Set Tiling.Plane) := by
    apply (locallyFell_metrizable K E).2 _ S |>.mp
    change Filter.Tendsto
      (fun n ↦ Tiling.AxisParallel.Topology.TilingSpace.translate (g (phi n)) T)
      Filter.atTop (nhds S)
    simpa [U, phi, Tiling.AxisParallel.Topology.TilingSpace.translateSequence,
      Function.comp_def] using hUlim'
  have haS : a ∈ (S.centres : Set Tiling.Plane) :=
    mem_of_locallyFellConverges_of_tendsto_mem hconv
      (fun n ↦ hamem (phi n)) tendsto_const_nhds
  have hzS : z ∈ (S.centres : Set Tiling.Plane) :=
    mem_of_locallyFellConverges_of_tendsto_mem hconv
      (fun n ↦ hzmem (phi n)) (by simpa [phi, Function.comp_def] using hzlim)
  obtain ⟨delta, hdelta, hsep⟩ := tilesOn_uniformlySeparated K
  have hne : ∀ᶠ n : ℕ in Filter.atTop, zseq n ≠ a := by
    by_cases h : ∃ k, zseq k = a
    · obtain ⟨k, hk⟩ := h
      filter_upwards [Filter.eventually_gt_atTop k] with n hn hna
      exact hn.ne (hzinj (hk.trans hna.symm))
    · exact Filter.Eventually.of_forall fun n hn ↦ h ⟨n, hn⟩
  have hdist : ∀ᶠ n : ℕ in Filter.atTop,
      delta ≤ dist a ((zseq ∘ phi) n) := by
    filter_upwards [hphi.tendsto_atTop.eventually hne] with n hn
    exact hsep E _ (Tiling.AxisParallel.Topology.TilingSpace.translate (g (phi n)) T).tilesOn
      (hamem (phi n)) (hzmem (phi n)) (Ne.symm hn)
  have hdistlim : Filter.Tendsto (fun n ↦ dist a ((zseq ∘ phi) n))
      Filter.atTop (nhds (dist a z)) := (continuous_const.dist continuous_id).tendsto z |>.comp
        (by simpa [phi, Function.comp_def] using hzlim)
  have hdaz : delta ≤ dist a z :=
    isClosed_Ici.mem_of_tendsto hdistlim hdist
  have hza : z ≠ a := by
    intro h
    rw [h, dist_self] at hdaz
    exact (not_le_of_gt hdelta) hdaz
  have hShull : S ∈ Tiling.AxisParallel.Topology.orbitHull T := by
    apply isClosed_closure.mem_of_tendsto hUlim'
    filter_upwards [] with n
    apply subset_closure
    exact ⟨g (phi n), rfl⟩
  exact ⟨phi, S, z, hphi, hShull, hconv, fun n ↦ hamem (phi n), haS, hzS, hza,
    hzinj.comp hphi.injective,
    by simpa [phi, Function.comp_def] using hzlim⟩

/-- Bounded finite-labelled anchors whose equal labels differ by carrier periods localize an
injectively varying pair into one anchored orbit limit. -/
theorem exists_localizedOrbitLimit_of_boundedAnchors
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (T : Tiling.AxisParallel.Topology.TilingSpace K E)
    {ι : Type*} [Finite ι] (label : ℕ → ι)
    (t s anchor : ℕ → Tiling.Plane) {C R : ℝ}
    (ht : ∀ n, t n ∈ (T.centres : Set Tiling.Plane))
    (hs : ∀ n, s n ∈ (T.centres : Set Tiling.Plane))
    (ha : ∀ n, anchor n ∈ (T.centres : Set Tiling.Plane))
    (hanchor : ∀ n, dist (anchor n) (t n) ≤ C)
    (hpairs : ∀ n, dist (t n) (s n) ≤ R)
    (hdiff : Function.Injective (s - t))
    (hperiod : ∀ i j, label i = label j →
      anchor i - anchor j ∈ Tiling.AxisParallel.aePeriodGroup E) :
    ∃ (g : ℕ → Tiling.AxisParallel.aePeriodGroup E)
      (S : Tiling.AxisParallel.Topology.TilingSpace K E)
      (a z : Tiling.Plane) (zseq : ℕ → Tiling.Plane),
      S ∈ Tiling.AxisParallel.Topology.orbitHull T ∧
      Tiling.AxisParallel.Topology.LocallyFellConverges
        (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
          (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T))
        (S.centres : Set Tiling.Plane) ∧
      (∀ n, a ∈ ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
        Set Tiling.Plane)) ∧
      a ∈ (S.centres : Set Tiling.Plane) ∧ z ∈ (S.centres : Set Tiling.Plane) ∧ z ≠ a ∧
      (∀ n, zseq n ∈ ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
        Set Tiling.Plane)) ∧ Function.Injective zseq ∧
      Filter.Tendsto zseq Filter.atTop (nhds z) ∧ (∀ n, zseq n ≠ z) ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        z ∉ ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
          Set Tiling.Plane) := by
  classical
  let u := anchor - t
  let v := anchor - s
  have huv : u - v = s - t := by
    funext n
    simp only [u, v, Pi.sub_apply]
    abel
  have huvinj : Function.Injective (u - v) := by simpa only [huv] using hdiff
  obtain ⟨phi, hphi, ⟨c, hlabel⟩, hinj⟩ :=
    exists_sameLabel_injectiveRelative_subsequence label u v huvinj
  let q := if _branch : Function.Injective (u ∘ phi) then t else s
  have hqmem : ∀ n, q n ∈ (T.centres : Set Tiling.Plane) := by
    intro n
    dsimp only [q]
    split <;> simp_all
  let rel := anchor - q
  have hrel : Function.Injective (rel ∘ phi) := by
    dsimp only [q, rel]
    split <;> simp_all [u, v, Function.comp_def]
  let a₀ := anchor (phi 0)
  let g₀ : ℕ → Tiling.AxisParallel.aePeriodGroup E := fun n ↦
    ⟨a₀ - anchor (phi n), hperiod (phi 0) (phi n) ((hlabel 0).trans (hlabel n).symm)⟩
  let w : ℕ → Tiling.Plane := fun n ↦ q (phi n) + (g₀ n : Tiling.Plane)
  have hamem (n : ℕ) : a₀ ∈
      ((Tiling.AxisParallel.Topology.TilingSpace.translate (g₀ n) T).centres :
        Set Tiling.Plane) := by
    change a₀ ∈ (fun y ↦ y + (g₀ n : Tiling.Plane)) '' (T.centres : Set Tiling.Plane)
    refine ⟨anchor (phi n), ha (phi n), ?_⟩
    simp only [g₀]
    abel
  have hwmem (n : ℕ) : w n ∈
      ((Tiling.AxisParallel.Topology.TilingSpace.translate (g₀ n) T).centres :
        Set Tiling.Plane) := by
    change w n ∈ (fun y ↦ y + (g₀ n : Tiling.Plane)) '' (T.centres : Set Tiling.Plane)
    exact ⟨q (phi n), hqmem (phi n), rfl⟩
  have hwform (n : ℕ) : w n = a₀ - rel (phi n) := by
    simp only [w, g₀, rel, Pi.sub_apply]
    abel
  have hwinj : Function.Injective w := by
    intro i j hij
    apply hrel
    rw [hwform i, hwform j] at hij
    exact sub_right_injective hij
  have hwbounded : ∃ D : ℝ, ∀ n, w n ∈ Metric.closedBall a₀ D := by
    refine ⟨C + R, ?_⟩
    intro n
    rw [Metric.mem_closedBall, hwform, dist_eq_norm]
    simp only [sub_sub_cancel_left, norm_neg, rel, Pi.sub_apply]
    have hqcases : q (phi n) = t (phi n) ∨ q (phi n) = s (phi n) := by
      dsimp only [q]
      split <;> simp
    rcases hqcases with hqt | hqs
    · rw [hqt]
      exact (by
        simpa [dist_eq_norm] using (hanchor (phi n)).trans
          (le_add_of_nonneg_right (dist_nonneg.trans (hpairs (phi n)))))
    · rw [hqs]
      calc
        ‖anchor (phi n) - s (phi n)‖ =
            ‖(anchor (phi n) - t (phi n)) + (t (phi n) - s (phi n))‖ := by
              congr 1
              abel
        _ ≤
            ‖anchor (phi n) - t (phi n)‖ + ‖t (phi n) - s (phi n)‖ := by
              exact norm_add_le _ _
        _ ≤ C + R := add_le_add (by simpa [dist_eq_norm] using hanchor (phi n))
          (by simpa [dist_eq_norm] using hpairs (phi n))
  obtain ⟨D, hwbound⟩ := hwbounded
  obtain ⟨theta, S, z, htheta, hShull, hconv, hamem', haS, hzS, hza, hzinj, hzlim⟩ :=
    exists_anchoredOrbitLimit_of_boundedMarkedCentres T g₀ a₀ w hwbound hamem hwmem hwinj
  obtain ⟨psi, hpsi, hzinj', hzlim', hzavoid⟩ :=
    injective_subsequence_avoiding_limit hzinj hzlim
  let idx := theta ∘ psi
  let g := g₀ ∘ idx
  let zseq := w ∘ idx
  have hconv' : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
        (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T))
      (S.centres : Set Tiling.Plane) := by
    rcases hconv with ⟨hclosed, hSclosed, hc⟩
    refine ⟨fun n ↦ hclosed (psi n), hSclosed, ?_⟩
    simpa [g, idx, Tiling.AxisParallel.Topology.TilingSpace.centresSequence,
      Tiling.AxisParallel.Topology.TilingSpace.translateSequence, Function.comp_def] using
      hc.comp hpsi.tendsto_atTop
  refine ⟨g, S, a₀, z, zseq, hShull, hconv', ?_, haS, hzS, hza, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hamem' (psi n)
  · intro n
    exact hwmem (idx n)
  · exact hwinj.comp (htheta.comp hpsi).injective
  · simpa [zseq, idx, Function.comp_def] using hzlim'
  · intro n
    exact hzavoid n
  · obtain ⟨delta, hdelta, hsep⟩ := tilesOn_uniformlySeparated K
    exact eventually_absent_of_uniformlySeparated hdelta
      (fun n ↦ hsep E _
        (Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).tilesOn)
      zseq z (fun n ↦ hwmem (idx n))
      (by simpa [zseq, idx, Function.comp_def] using hzlim') hzavoid

/-- Failure of finite local complexity in a proper periodic cylinder yields an anchored orbit
limit containing a genuinely moving centre which is eventually absent exactly. -/
theorem exists_localizedNonFLCOrbitLimit
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X) (hXproper : X ≠ Set.univ)
    {beta0 : ℝ} (hbeta0 : 0 < beta0)
    (hXperiod : ∀ x : ℝ, x + beta0 ∈ X ↔ x ∈ X)
    (T : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    (hTnonFLC : ¬ Tiling.AxisParallel.HasFLC (T.centres : Set Tiling.Plane)) :
    ∃ (g : ℕ → Tiling.AxisParallel.aePeriodGroup
          {z : Tiling.Plane | z.re ∈ X})
      (S : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
      (a z : Tiling.Plane) (zseq : ℕ → Tiling.Plane),
      S ∈ Tiling.AxisParallel.Topology.orbitHull T ∧
      Tiling.AxisParallel.Topology.LocallyFellConverges
        (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
          (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T))
        (S.centres : Set Tiling.Plane) ∧
      (∀ n : ℕ, a ∈
        ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
          Set Tiling.Plane)) ∧
      a ∈ (S.centres : Set Tiling.Plane) ∧
      z ∈ (S.centres : Set Tiling.Plane) ∧ z ≠ a ∧
      (∀ n : ℕ, zseq n ∈
        ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
          Set Tiling.Plane)) ∧
      Function.Injective zseq ∧ Filter.Tendsto zseq Filter.atTop (nhds z) ∧
      (∀ n : ℕ, zseq n ≠ z) ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        z ∉ ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
          Set Tiling.Plane) := by
  classical
  obtain ⟨beta, hbeta, hGamma⟩ := properVerticalCarrier_horizontalPeriodGroup
    hXnonempty hXopen hXregular hXproper hbeta0 hXperiod
  have hbetaPeriod : ∀ y : ℝ, y + beta ∈ X ↔ y ∈ X := by
    apply (cylinder_period_iff hXopen hXregular (beta : Tiling.Plane)).mp
    apply (hGamma (beta : Tiling.Plane)).mpr
    exact ⟨1, by simp⟩
  obtain ⟨x, hx⟩ : (frontier X).Nonempty :=
    nonempty_frontier_iff.mpr ⟨hXnonempty, hXproper⟩
  obtain ⟨R, t, s, _r, _hR, hts, hpairs, hdiff, _hrlim, _hrne, _hravoid⟩ :=
    exists_varyingLocalDisplacement hXnonempty hXopen hXregular hXproper
      hbeta0 hXperiod T hTnonFLC
  obtain ⟨C, _hC, hanchors⟩ := boundaryAnchors_coarselyDense
    hXnonempty hXopen hXregular hXproper hbeta hbetaPeriod T hx
  choose anchor hanchorMem hanchorDist v hv w hw hvw hvertical hedge m hm using
    fun n ↦ hanchors (t n) (hts n).1
  let label : ℕ → (↥K.vertexFinset × ↥K.vertexFinset) := fun n ↦
    (⟨v n, hv n⟩, ⟨w n, hw n⟩)
  have hperiod : ∀ i j, label i = label j →
      anchor i - anchor j ∈
        Tiling.AxisParallel.aePeriodGroup {z : Tiling.Plane | z.re ∈ X} := by
    intro i j hij
    have hvij : v i = v j := congrArg (fun p ↦ (p.1 : Tiling.Plane)) hij
    rw [hGamma]
    refine ⟨m i - m j, ?_⟩
    simp only [Complex.sub_re, Int.cast_sub]
    have hmi := hm i
    have hmj := hm j
    rw [hvij] at hmi
    linarith
  exact exists_localizedOrbitLimit_of_boundedAnchors T label t s anchor
    (fun n ↦ (hts n).1) (fun n ↦ (hts n).2) hanchorMem hanchorDist
    (fun n ↦ (hpairs n).2) hdiff hperiod

/-- In a sequence of tilings by one fixed tile, a convergent sequence of distinct marked centres
makes its limit centre eventually absent. -/
theorem localizedLimit_eventuallyAbsent
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (_hXnonempty : X.Nonempty) (_hXopen : IsOpen X)
    (_hXregular : interior (closure X) = X) (_hXproper : X ≠ Set.univ)
    {beta0 : ℝ} (_hbeta0 : 0 < beta0)
    (_hXperiod : ∀ x : ℝ, x + beta0 ∈ X ↔ x ∈ X)
    (U : ℕ → Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    (zseq : ℕ → Tiling.Plane) (z : Tiling.Plane)
    (hzmem : ∀ n : ℕ, zseq n ∈ ((U n).centres : Set Tiling.Plane))
    (hzlim : Filter.Tendsto zseq Filter.atTop (nhds z))
    (hzneq : ∀ n : ℕ, zseq n ≠ z) :
    ∀ᶠ n : ℕ in Filter.atTop, z ∉ ((U n).centres : Set Tiling.Plane) := by
  obtain ⟨delta, hdelta, hsep⟩ := tilesOn_uniformlySeparated K
  exact eventually_absent_of_uniformlySeparated hdelta
    (fun n ↦ hsep _ _ (U n).tilesOn) zseq z hzmem hzlim hzneq

private noncomputable def latticeFloor
    (L : Tiling.AxisParallel.PlanarLattice) (x : Tiling.Plane) : Tiling.Plane :=
  ∑ i : Fin 2, (Int.floor (L.realBasis.repr x i) : ℝ) • L.basis i

private theorem latticeFloor_mem (L : Tiling.AxisParallel.PlanarLattice) (x : Tiling.Plane) :
  latticeFloor L x ∈ L.toAddSubgroup := by
  rw [latticeFloor]
  apply L.toAddSubgroup.sum_mem
  intro i _
  rw [show (Int.floor (L.realBasis.repr x i) : ℝ) • L.basis i =
      Int.floor (L.realBasis.repr x i) • L.basis i by
    simp]
  apply AddSubgroup.zsmul_mem
  rw [Tiling.AxisParallel.PlanarLattice.toAddSubgroup]
  exact AddSubgroup.subset_closure (Set.mem_range_self i)

private theorem latticeFloor_sub_norm_le (L : Tiling.AxisParallel.PlanarLattice)
    (x : Tiling.Plane) :
    ‖latticeFloor L x - x‖ ≤ ∑ i : Fin 2, ‖L.basis i‖ := by
  have hb : (L.realBasis : Fin 2 → Tiling.Plane) = L.basis := L.coe_realBasis
  let c : Fin 2 → ℝ := L.realBasis.repr x
  have hx : x = ∑ i : Fin 2, c i • L.basis i := by
    rw [← hb]
    exact (L.realBasis.sum_repr x).symm
  change ‖(∑ i : Fin 2, (Int.floor (c i) : ℝ) • L.basis i) - x‖ ≤ _
  rw [hx, ← Finset.sum_sub_distrib]
  simp only [← sub_smul]
  calc
    ‖∑ i : Fin 2, ((Int.floor (c i) : ℝ) - c i) • L.basis i‖
        ≤ ∑ i : Fin 2, ‖((Int.floor (c i) : ℝ) - c i) • L.basis i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 2, ‖L.basis i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      have hlo := Int.floor_le (c i)
      have hhi := Int.lt_floor_add_one (c i)
      have habs : |(Int.floor (c i) : ℝ) - c i| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      exact mul_le_of_le_one_left (norm_nonneg _) habs

/-- A full-rank planar lattice is coarsely dense, with an explicit covering radius obtained from
its chosen basis. -/
theorem planarLattice_coveringRadius (L : Tiling.AxisParallel.PlanarLattice) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Tiling.Plane,
      ∃ ell ∈ L.toAddSubgroup, dist ell x ≤ R := by
  refine ⟨∑ i : Fin 2, ‖L.basis i‖, Finset.sum_nonneg fun _ _ ↦ norm_nonneg _, ?_⟩
  intro x
  exact ⟨latticeFloor L x, latticeFloor_mem L x, by
    rw [dist_eq_norm]
    exact latticeFloor_sub_norm_le L x⟩

/-- Every planar sequence admits lattice approximants whose residuals converge along a
subsequence. -/
theorem planarLattice_round_subsequence
    (L : Tiling.AxisParallel.PlanarLattice) (g : ℕ → Tiling.Plane) :
    ∃ (phi : ℕ → ℕ) (lambda : ℕ → Tiling.Plane) (gamma : Tiling.Plane),
      StrictMono phi ∧
      (∀ n, lambda n ∈ L.toAddSubgroup) ∧
      Filter.Tendsto (lambda - g ∘ phi) Filter.atTop (nhds gamma) := by
  let d : ℕ → Tiling.Plane := fun n ↦ latticeFloor L (g n) - g n
  have hd : ∀ n, d n ∈ Metric.closedBall 0 (∑ i : Fin 2, ‖L.basis i‖) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact latticeFloor_sub_norm_le L (g n)
  obtain ⟨gamma, _hgamma, phi, hphi, hlim⟩ :=
    (ProperSpace.isCompact_closedBall (0 : Tiling.Plane)
      (∑ i : Fin 2, ‖L.basis i‖)).tendsto_subseq hd
  refine ⟨phi, fun n ↦ latticeFloor L (g (phi n)), gamma, hphi,
    fun n ↦ latticeFloor_mem L _, ?_⟩
  change Filter.Tendsto (fun n ↦ latticeFloor L (g (phi n)) - g (phi n))
    Filter.atTop (nhds gamma)
  exact hlim

private theorem limit_mem_aePeriodGroup_of_regularOpen
    {E : Set Tiling.Plane} (hEopen : IsOpen E)
    (hEregular : interior (closure E) = E)
    {u : ℕ → Tiling.AxisParallel.aePeriodGroup E} {v : Tiling.Plane}
    (hu : Filter.Tendsto (fun n ↦ (u n : Tiling.Plane)) Filter.atTop (nhds v)) :
    v ∈ Tiling.AxisParallel.aePeriodGroup E := by
  rw [Tiling.AxisParallel.aePeriodGroup_eq_periodGroup_of_regularOpen hEopen hEregular]
  rw [Tiling.AxisParallel.periodGroup_isAddSubgroup]
  have hsub₁ : v +ᵥ E ⊆ closure E := by
    rintro x ⟨y, hy, rfl⟩
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun n ↦ (u n : Tiling.Plane) + y, fun n ↦ ?_, ?_⟩
    · have hp : (u n : Tiling.Plane) +ᵥ E =ᵐ[MeasureTheory.volume] E := (u n).property
      have hlit : (u n : Tiling.Plane) +ᵥ E = E :=
        Tiling.AxisParallel.regularOpen_eq_of_aeEq (hEopen.vadd _) (by
          rw [closure_vadd, interior_vadd, hEregular]) hEopen hEregular hp
      exact (Set.ext_iff.mp hlit _).mp ⟨y, hy, rfl⟩
    · simpa only [vadd_eq_add] using hu.add tendsto_const_nhds
  have hsub₂ : E ⊆ closure (v +ᵥ E) := by
    intro x hx
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun n ↦ v + (x - (u n : Tiling.Plane)), fun n ↦ ?_, ?_⟩
    · refine ⟨x - (u n : Tiling.Plane), ?_, rfl⟩
      have hp : (u n : Tiling.Plane) +ᵥ E =ᵐ[MeasureTheory.volume] E := (u n).property
      have hlit : (u n : Tiling.Plane) +ᵥ E = E :=
        Tiling.AxisParallel.regularOpen_eq_of_aeEq (hEopen.vadd _) (by
          rw [closure_vadd, interior_vadd, hEregular]) hEopen hEregular hp
      rw [← hlit] at hx
      rcases hx with ⟨y, hy, hyx⟩
      convert hy using 1
      simp only [vadd_eq_add] at hyx
      rw [← hyx]
      abel
    · have hsub : Filter.Tendsto (fun n ↦ x - (u n : Tiling.Plane)) Filter.atTop
          (nhds (x - v)) := tendsto_const_nhds.sub hu
      have hvconst : Filter.Tendsto (fun _ : ℕ ↦ v) Filter.atTop (nhds v) :=
        tendsto_const_nhds
      simpa only [add_sub_cancel] using hvconst.add hsub
  have hclosures : closure (v +ᵥ E) = closure E := Set.Subset.antisymm
    (closure_minimal hsub₁ isClosed_closure)
    (closure_minimal hsub₂ isClosed_closure)
  calc
    v +ᵥ E = interior (closure (v +ᵥ E)) := by
      rw [closure_vadd, interior_vadd, hEregular]
    _ = interior (closure E) := congrArg interior hclosures
    _ = E := hEregular

/-- Rounding translations to a full-rank lattice in a regular-open carrier period group leaves a
bounded residual, whose convergent subsequence transports any tiling limit by its residual limit. -/
theorem roundTranslationsToLattice_regularOpen
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (Lambda : Tiling.AxisParallel.PlanarLattice)
    (hLambda : Lambda.toAddSubgroup ≤ Tiling.AxisParallel.aePeriodGroup E)
    (g : ℕ → Tiling.AxisParallel.aePeriodGroup E)
    (T S : Tiling.AxisParallel.Topology.TilingSpace K E)
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
        (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T))
      (S.centres : Set Tiling.Plane)) :
    ∃ (phi : ℕ → ℕ) (lambda : ℕ → Tiling.AxisParallel.aePeriodGroup E)
      (gamma : Tiling.AxisParallel.aePeriodGroup E),
      StrictMono phi ∧
      (∀ n, (lambda n : Tiling.Plane) ∈ Lambda.toAddSubgroup) ∧
      Filter.Tendsto
        (Tiling.AxisParallel.Topology.carrierTranslationSequence lambda -
          Tiling.AxisParallel.Topology.carrierTranslationSequence (g ∘ phi))
        Filter.atTop (nhds (gamma : Tiling.Plane)) ∧
      Tiling.AxisParallel.Topology.LocallyFellConverges
        (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
          (Tiling.AxisParallel.Topology.TilingSpace.translateSequence lambda T))
        ((Tiling.AxisParallel.Topology.TilingSpace.translate gamma S).centres :
          Set Tiling.Plane) := by
  obtain ⟨phi, ell, gammaPlane, hphi, hell, hres⟩ :=
    planarLattice_round_subsequence Lambda (fun n ↦ (g n : Tiling.Plane))
  have hellPeriod (n) : ell n ∈ Tiling.AxisParallel.aePeriodGroup E := hLambda (hell n)
  let lambda : ℕ → Tiling.AxisParallel.aePeriodGroup E := fun n ↦ ⟨ell n, hellPeriod n⟩
  let residual : ℕ → Tiling.AxisParallel.aePeriodGroup E := fun n ↦ lambda n - g (phi n)
  have hres' : Filter.Tendsto (fun n ↦ (residual n : Tiling.Plane)) Filter.atTop
      (nhds gammaPlane) := by
    change Filter.Tendsto (fun n ↦ ell n - (g (phi n) : Tiling.Plane))
      Filter.atTop (nhds gammaPlane)
    change Filter.Tendsto (fun n ↦ ell n - (g (phi n) : Tiling.Plane))
      Filter.atTop (nhds gammaPlane) at hres
    exact hres
  have hgamma : gammaPlane ∈ Tiling.AxisParallel.aePeriodGroup E :=
    limit_mem_aePeriodGroup_of_regularOpen hEopen hEregular hres'
  let gamma : Tiling.AxisParallel.aePeriodGroup E := ⟨gammaPlane, hgamma⟩
  refine ⟨phi, lambda, gamma, hphi, ?_, ?_, ?_⟩
  · intro n
    exact hell n
  · change Filter.Tendsto
      (fun n ↦ (lambda n : Tiling.Plane) - (g (phi n) : Tiling.Plane))
      Filter.atTop (nhds gammaPlane)
    exact hres'
  · apply ((locallyFell_metrizable K E).2 _ _).mp
    have hgconv : Filter.Tendsto
        (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T ∘ phi)
        Filter.atTop (nhds S) :=
      (((locallyFell_metrizable K E).2 _ _).mpr hconv).comp hphi.tendsto_atTop
    have hrsub : Filter.Tendsto residual Filter.atTop (nhds gamma) := by
      rw [tendsto_subtype_rng]
      simpa [gamma] using hres'
    have hpair : Filter.Tendsto
        (fun n ↦ (residual n,
          (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T ∘ phi) n))
        Filter.atTop (nhds (gamma, S)) := by
      rw [nhds_prod_eq]
      exact hrsub.prodMk hgconv
    have haction := (translationAction_continuous K E).tendsto (gamma, S)
    have hlimAction := haction.comp hpair
    have hlimAction' : Filter.Tendsto
        (fun n ↦ residual n +ᵥ
          (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T ∘ phi) n)
        Filter.atTop
        (nhds (Tiling.AxisParallel.Topology.TilingSpace.translate gamma S)) := by
      change Filter.Tendsto
        (fun n ↦ residual n +ᵥ
          Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T (phi n))
        Filter.atTop
        (nhds (Tiling.AxisParallel.Topology.TilingSpace.translate gamma S)) at hlimAction
      exact hlimAction
    convert hlimAction' using 1
    funext n
    change lambda n +ᵥ T = residual n +ᵥ (g (phi n) +ᵥ T)
    rw [← add_vadd]
    congr 1
    simp [residual]

/-- Lattice rounding for translations of a tiling of a proper periodic vertical carrier. -/
theorem roundTranslationsToLattice
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (_hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X) (_hXproper : X ≠ Set.univ)
    {beta0 : ℝ} (_hbeta0 : 0 < beta0)
    (_hXperiod : ∀ x : ℝ, x + beta0 ∈ X ↔ x ∈ X)
    (Lambda : Tiling.AxisParallel.PlanarLattice)
    (hLambda : Lambda.toAddSubgroup ≤
      Tiling.AxisParallel.aePeriodGroup {z : Tiling.Plane | z.re ∈ X})
    (g : ℕ → Tiling.AxisParallel.aePeriodGroup
      {z : Tiling.Plane | z.re ∈ X})
    (T : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    (S : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
        (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T))
      (S.centres : Set Tiling.Plane)) :
    ∃ (phi : ℕ → ℕ)
      (lambda : ℕ → Tiling.AxisParallel.aePeriodGroup
        {z : Tiling.Plane | z.re ∈ X})
      (gamma : Tiling.AxisParallel.aePeriodGroup
        {z : Tiling.Plane | z.re ∈ X}),
      StrictMono phi ∧
      (∀ n : ℕ, (lambda n : Tiling.Plane) ∈ Lambda.toAddSubgroup) ∧
      Filter.Tendsto
        (Tiling.AxisParallel.Topology.carrierTranslationSequence lambda -
          Tiling.AxisParallel.Topology.carrierTranslationSequence (g ∘ phi))
        Filter.atTop (nhds (gamma : Tiling.Plane)) ∧
      Tiling.AxisParallel.Topology.LocallyFellConverges
        (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
          (Tiling.AxisParallel.Topology.TilingSpace.translateSequence lambda T))
        ((Tiling.AxisParallel.Topology.TilingSpace.translate gamma S).centres :
          Set Tiling.Plane) := by
  have hopen : IsOpen ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) :=
    hXopen.preimage Complex.continuous_re
  have hregular : interior
      (closure ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane)) =
      {z : Tiling.Plane | z.re ∈ X} := by
    change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hXregular]
  exact roundTranslationsToLattice_regularOpen hopen hregular Lambda hLambda g T S hconv



end Tiling.AxisParallel.Continuous
