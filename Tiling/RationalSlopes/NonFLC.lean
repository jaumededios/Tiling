import Tiling.RationalSlopes.Earthquake
import Tiling.RationalSlopes.BoundaryGeometry
import Tiling.Topology.TilingHull

set_option autoImplicit false
set_option linter.style.header false
open Function Filter MeasureTheory Set
open scoped Pointwise Topology
noncomputable section
open Tiling
open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Polygonal
open Tiling.RationalSlopes


namespace Tiling.RationalSlopes

private theorem locallyFell_subsequence {V : ℕ → Set Plane} {S : Set Plane}
    (h : Tiling.Topology.LocallyFellConverges V S) {ι : ℕ → ℕ}
    (hι : StrictMono ι) : Tiling.Topology.LocallyFellConverges (V ∘ ι) S := by
  obtain ⟨hV, hS, hconv⟩ := h
  exact ⟨fun n => hV (ι n), hS, hconv.comp hι.tendsto_atTop⟩

/-- Pointwise absence can be intersected over a FINITE local patch only. -/
private theorem finite_patch_eventually_disjoint {V : ℕ → Set Plane} {U : Set Plane}
    (hU : U.Finite) (habsent : ∀ u ∈ U, ∀ᶠ n in atTop, u ∉ V n) :
    ∀ᶠ n in atTop, Disjoint (V n) U := by
  have hfinite : ∀ᶠ n in atTop, ∀ u ∈ U, u ∉ V n :=
    (Filter.eventually_all_finite hU).mpr habsent
  filter_upwards [hfinite] with n hn
  exact Set.disjoint_left.mpr fun u hu hUu => hn u hUu hu

/-- Positive separation excludes exact presence of a distinct approaching centre. -/
private theorem moving_limit_eventually_absent {V : ℕ → Set Plane} {z : ℕ → Plane}
    {s : Plane} {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ n, Tiling.Topology.IsUniformlySeparated ε (V n))
    (hzmem : ∀ n, z n ∈ V n) (hzne : ∀ n, z n ≠ s)
    (hzlim : Tendsto z atTop (𝓝 s)) : ∀ᶠ n in atTop, s ∉ V n := by
  have hnear := (Metric.tendsto_nhds.mp hzlim) ε hε
  filter_upwards [hnear] with n hn hs
  exact (not_le_of_gt hn) (hsep n (hzmem n) hs (hzne n))

private theorem eventual_part_subset (V : ℕ → Set Plane) (S : Set Plane) :
    {u | u ∈ S ∧ ∀ᶠ n in atTop, u ∈ V n} ⊆ S := fun _ hu => hu.1

private theorem transient_part_eventually_absent {V : ℕ → Set Plane} {S A : Set Plane}
    (hA : A = {u | u ∈ S ∧ ∀ᶠ n in atTop, u ∈ V n})
    (hstable : ∀ u ∈ S, (∀ᶠ n in atTop, u ∈ V n) ∨
      (∀ᶠ n in atTop, u ∉ V n)) :
    ∀ u ∈ S \ A, ∀ᶠ n in atTop, u ∉ V n := by
  intro u hu
  rcases hstable u hu.1 with hpresent | habsent
  · exact False.elim (hu.2 (hA ▸ ⟨hu.1, hpresent⟩))
  · exact habsent

private theorem open_subset_closure_of_ae_subset {U W : Set Plane} (hU : IsOpen U)
    (hUW : ∀ᵐ x ∂volume, x ∈ U → x ∈ W) : U ⊆ closure W := by
  intro x hx
  by_contra hxW
  let Q := U ∩ (closure W)ᶜ
  have hQopen : IsOpen Q := hU.inter isClosed_closure.isOpen_compl
  have hQzero : volume Q = 0 := measure_eq_zero_iff_ae_notMem.mpr
    (hUW.mono fun y hy hyQ => hyQ.2 (subset_closure (hy hyQ.1)))
  exact hQopen.measure_ne_zero volume ⟨x, hx, hxW⟩ hQzero

private theorem local_regularOpen_eq {U W : Set Plane} {x : Plane} {r R : ℝ}
    (hrR : r < R) (hU : IsOpen U) (hUreg : interior (closure U) = U)
    (hW : IsOpen W) (hWreg : interior (closure W) = W)
    (hae : ∀ᵐ z ∂volume, (z ∈ U ∩ Metric.ball x R) ↔
      (z ∈ W ∩ Metric.ball x R)) :
    U ∩ Metric.ball x r = W ∩ Metric.ball x r := by
  have forward {P Q : Set Plane} (hP : IsOpen P) (hQreg : interior (closure Q) = Q)
      (hPQ : ∀ᵐ z ∂volume, (z ∈ P ∩ Metric.ball x R) ↔
        (z ∈ Q ∩ Metric.ball x R)) :
      P ∩ Metric.ball x r ⊆ Q ∩ Metric.ball x r := by
    rintro z ⟨hzP, hzr⟩
    have hzR : z ∈ Metric.ball x R := Metric.mem_ball.mpr
      ((Metric.mem_ball.mp hzr).trans hrR)
    have hcl : P ∩ Metric.ball x R ⊆ closure Q :=
      (open_subset_closure_of_ae_subset (hP.inter Metric.isOpen_ball)
        (hPQ.mono fun y hy => hy.mp)).trans (closure_mono inter_subset_left)
    have hzInt : z ∈ interior (closure Q) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset
        ((hP.inter Metric.isOpen_ball).mem_nhds ⟨hzP, hzR⟩) hcl
    exact ⟨hQreg ▸ hzInt, hzr⟩
  exact Set.Subset.antisymm (forward hU hWreg hae)
    (forward hW hUreg (hae.mono fun _ h => h.symm))

/-- Exact subtraction of the stationary background is local: only centres in
one bounded window are required to be present on each sufficiently late index.
This is the generic port of the existing axis proof, not an axis import. -/
private theorem fixedBackground_cancel {K : PolygonalRegion} {E S A : Set Plane}
    {V : ℕ → Set Plane} (hV : ∀ n, TilesOn K (V n) E)
    (hS : TilesOn K S E) (hAS : A ⊆ S)
    (hA : ∀ a ∈ A, ∀ᶠ n in atTop, a ∈ V n) (x : Plane) :
    ∀ᶠ n in atTop, regularSupport K (V n \ A) =ᶠ[𝓝 x]
      regularSupport K (S \ A) := by
  classical
  obtain ⟨R, hR⟩ := K.isPolygonal.isBounded.subset_closedBall (0 : Plane)
  let Q : Set Plane := Metric.closedBall x (R + 2)
  have hAfin : (A ∩ Q).Finite :=
    ((packing_centres_locallyFinite hS.2.1).1 Q Metric.isBounded_closedBall).subset
      (inter_subset_inter_left Q hAS)
  have hfinite : ∀ᶠ n in atTop, ∀ a ∈ A ∩ Q, a ∈ V n :=
    (Filter.eventually_all_finite hAfin).mpr fun a ha => hA a ha.1
  filter_upwards [hfinite] with n hn
  have relevant {a z : Plane} (ha : a ∈ A) (hz : z ∈ Metric.ball x 1)
      (haz : z ∈ a +ᵥ K.openCarrier) : a ∈ V n := by
    apply hn a
    refine ⟨ha, ?_⟩
    change dist a x ≤ R + 2
    have hak : -a + z ∈ K.support := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at haz
      exact interior_subset haz
    have hbound : dist (-a + z) 0 ≤ R := hR hak
    have hd : dist a z = dist (-a + z) 0 := by
      rw [dist_comm]
      simp only [dist_eq_norm, sub_zero]
      congr 1
      abel
    calc
      dist a x ≤ dist a z + dist z x := dist_triangle _ _ _
      _ = dist (-a + z) 0 + dist z x := by rw [hd]
      _ ≤ R + 2 := by have := Metric.mem_ball.mp hz; linarith
  have residual {C : Set Plane}
      (hp : IsPacking K.prototileFamily (K.placements C))
      (hrel : ∀ a ∈ A, ∀ z ∈ Metric.ball x 1,
        z ∈ a +ᵥ K.openCarrier → a ∈ C) :
      ∀ z ∈ Metric.ball x 1, z ∈ openUnion K (C \ A) ↔
        z ∈ openUnion K C ∧ z ∉ openUnion K A := by
    intro z hz
    constructor
    · intro hzres
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hzres
      refine ⟨Set.mem_iUnion.mpr ⟨⟨t.1, t.2.1⟩, ht⟩, ?_⟩
      intro hzA
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hzA
      have haC := hrel a.1 a.2 z hz ha
      have hat : a.1 ≠ t.1 := fun heq => t.2.2 (heq ▸ a.2)
      have hd := (isPacking_iff_openCarrier_disjoint K C).mp hp haC t.2.1 hat
      exact Set.disjoint_left.mp hd ha ht
    · rintro ⟨hzC, hznotA⟩
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hzC
      refine Set.mem_iUnion.mpr ⟨⟨t.1, t.2, ?_⟩, ht⟩
      intro htA
      exact hznotA (Set.mem_iUnion.mpr ⟨⟨t.1, htA⟩, ht⟩)
  have residualV := residual (hV n).2.1 (fun a ha z hz htile => relevant ha hz htile)
  have residualS := residual hS.2.1 (fun a ha _ _ _ => hAS ha)
  have haeTotals : ∀ᵐ z ∂volume,
      (z ∈ openUnion K (V n)) ↔ (z ∈ openUnion K S) := by
    filter_upwards [(hV n).2.2, hS.2.2] with z hzV hzS
    have hzV' : z ∈ E ↔ z ∈ openUnion K (V n) := by
      simpa only [openUnion, Set.mem_iUnion] using hzV
    have hzS' : z ∈ E ↔ z ∈ openUnion K S := by
      simpa only [openUnion, Set.mem_iUnion] using hzS
    exact hzV'.symm.trans hzS'
  have haeRaw : ∀ᵐ z ∂volume,
      (z ∈ openUnion K (V n \ A) ∩ Metric.ball x 1) ↔
        (z ∈ openUnion K (S \ A) ∩ Metric.ball x 1) := by
    filter_upwards [haeTotals] with z hzTotal
    by_cases hz : z ∈ Metric.ball x 1
    · simp only [Set.mem_inter_iff, hz, and_true, residualV z hz, residualS z hz]
      exact and_congr_left fun _ => hzTotal
    · simp [hz]
  have packV : IsPacking K.prototileFamily (K.placements (V n \ A)) :=
    (hV n).2.1.mono fun _ h => h.1
  have packS : IsPacking K.prototileFamily (K.placements (S \ A)) :=
    hS.2.1.mono fun _ h => h.1
  have haeSupports : ∀ᵐ z ∂volume,
      (z ∈ regularSupport K (V n \ A) ∩ Metric.ball x 1) ↔
        (z ∈ regularSupport K (S \ A) ∩ Metric.ball x 1) := by
    filter_upwards [openUnion_aeEq_regularSupport packV,
      openUnion_aeEq_regularSupport packS, haeRaw] with z hzV hzS hz
    constructor
    · rintro ⟨hzRV, hzball⟩
      have hzOV : z ∈ openUnion K (V n \ A) := Eq.mpr hzV hzRV
      have hzOS := (hz.mp ⟨hzOV, hzball⟩).1
      exact ⟨Eq.mp hzS hzOS, hzball⟩
    · rintro ⟨hzRS, hzball⟩
      have hzOS : z ∈ openUnion K (S \ A) := Eq.mpr hzS hzRS
      have hzOV := (hz.mpr ⟨hzOS, hzball⟩).1
      exact ⟨Eq.mp hzV hzOV, hzball⟩
  have heq := local_regularOpen_eq (by norm_num : (1 / 2 : ℝ) < 1)
    (regularSupport_isRegularOpen K (V n \ A)).1
    (regularSupport_isRegularOpen K (V n \ A)).2
    (regularSupport_isRegularOpen K (S \ A)).1
    (regularSupport_isRegularOpen K (S \ A)).2 haeSupports
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  have hz' := congrArg (fun U : Set Plane => z ∈ U) heq
  have hziff : (z ∈ regularSupport K (V n \ A)) ↔
      (z ∈ regularSupport K (S \ A)) := by
    simpa only [Set.mem_inter_iff, hz, and_true] using iff_of_eq hz'
  exact propext hziff

private theorem regularSupport_union (K : PolygonalRegion) (A B : Set Plane) :
    regularSupport K (A ∪ B) =
      interior (closure (regularSupport K A ∪ regularSupport K B)) := by
  have hid : (fun b : Bool => regularSupport K (cond b A B)) =
      (fun b : Bool => cond b (regularSupport K A) (regularSupport K B)) := by
    funext b
    cases b <;> rfl
  rw [Set.union_eq_iUnion, regularSupport_iUnion, hid, ← Set.union_eq_iUnion]

private theorem regularSupport_nonempty {K : PolygonalRegion} {S : Set Plane}
    (hS : S.Nonempty) : (regularSupport K S).Nonempty := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hopen : IsOpen (openUnion K S) := isOpen_iUnion fun s => isOpen_interior.vadd s.1
  have hsub : openUnion K S ⊆ regularSupport K S :=
    interior_maximal subset_closure hopen
  refine ⟨s + k, hsub ?_⟩
  exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, Set.mem_vadd_set.mpr ⟨k, hk, rfl⟩⟩

/-- Complement invariance requires the full carrier to be invariant too. -/
private theorem invariant_regularOpen_complement {E D : Set Plane}
    {δ : Submodule ℝ Plane} (hE : IsInvariantAlong E δ)
    (hD : IsInvariantAlong D δ) : IsInvariantAlong (E \ closure D) δ := by
  intro u hu
  have hcl : u +ᵥ closure D = closure D := by rw [← closure_vadd, hD u hu]
  have he := hE u hu
  ext x
  have hxE := congrArg (fun U : Set Plane => x ∈ U) he
  have hxD := congrArg (fun U : Set Plane => x ∈ U) hcl
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_sdiff] at hxE hxD ⊢
  rw [hxE, hxD]

/-- Once the stationary finite-patch subtraction gives local germs, the
no-corner deduction uses only the finitely many centres `x - v`. In particular
there is no global eventual-disjointness assertion about `S \ A`. -/
private theorem transient_cornerFree_of_local_germs {K : PolygonalRegion}
    {V : ℕ → Set Plane} {S A : Set Plane}
    (hp : ∀ n, IsPacking K.prototileFamily (K.placements (V n)))
    (hconv : Tiling.Topology.LocallyFellConverges V S)
    (hA : A = {u | u ∈ S ∧ ∀ᶠ n in atTop, u ∈ V n})
    (hstable : ∀ u ∈ S, (∀ᶠ n in atTop, u ∈ V n) ∨
      (∀ᶠ n in atTop, u ∉ V n))
    (hgerm : ∀ x ∈ properVertices (regularSupport K (S \ A)),
      ∀ᶠ n in atTop,
        regularSupport K (V n \ A) =ᶠ[𝓝 x] regularSupport K (S \ A)) :
    properVertices (regularSupport K (S \ A)) = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hvertices := K.isPolygonal.vertexSet_finite
  have habsent : ∀ v ∈ vertexSet K.support,
      ∀ᶠ n in atTop, x - v ∉ V n \ A := by
    intro v hv
    by_cases hqA : x - v ∈ A
    · exact Eventually.of_forall fun n hq => hq.2 hqA
    · by_cases hqS : x - v ∈ S
      · filter_upwards [transient_part_eventually_absent hA hstable
          (x - v) ⟨hqS, hqA⟩] with n hn hq
        exact hn hq.1
      · have hdisj : Disjoint S ({x - v} : Set Plane) := by
          simpa using hqS
        have hmiss := Tiling.Topology.locallyFellConverges_eventually_disjoint_compact
          hconv isCompact_singleton hdisj
        filter_upwards [hmiss] with n hn hq
        exact (Set.disjoint_left.mp hn) hq.1 (Set.mem_singleton _)
  have hfinite := (Filter.eventually_all_finite hvertices).mpr habsent
  obtain ⟨n, havoid, hg⟩ := (hfinite.and (hgerm x hx)).exists
  have hx' : IsProperVertex (regularSupport K (V n \ A)) x :=
    (isProperVertex_iff_of_eventuallyEq hg).mpr hx
  have hpn : IsPacking K.prototileFamily (K.placements (V n \ A)) :=
    (hp n).mono (fun _ h => h.1)
  obtain ⟨v, hv, q, hq, heq⟩ := properVertexProvenance hpn x hx'
  have hqeq : x - v = q := by
    rw [heq]
    abel
  exact havoid v hv (hqeq ▸ hq)

/-- A lattice correction translates the nontrivial invariant part along with its limit. -/
private theorem directionalEarthquake_vadd {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {S : Set Plane} (h : HasDirectionalEarthquake K δ S)
    (a : Plane) : HasDirectionalEarthquake K δ (a +ᵥ S) := by
  obtain ⟨B, hB, hBS, hproper, hinv⟩ := h
  refine ⟨a +ᵥ B, ?_, ?_, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hB
    exact ⟨a + b, Set.mem_vadd_set.mpr ⟨b, hb, rfl⟩⟩
  · exact Set.vadd_set_mono hBS
  · intro heq
    apply hproper
    ext x
    have hx := congrArg (fun U : Set Plane => a + x ∈ U) heq
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hx
  · rw [regularSupport_vadd]
    intro u hu
    ext x
    have hx := congrArg (fun U : Set Plane => -a + x ∈ U) (hinv u hu)
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      add_comm, add_left_comm, add_assoc] using hx

/-- The arbitrary-carrier split establishes invariance of the transient part
only. No directional invariance of `E` or of the stationary complement is used. -/
private theorem stabilizedLimit_transientEarthquake {K : PolygonalRegion}
    {E S A : Set Plane} {V : ℕ → Set Plane}
    (htiles : ∀ n, TilesOn K (V n) E)
    (hconv : Tiling.Topology.LocallyFellConverges V S)
    (hA : A = {u | u ∈ S ∧ ∀ᶠ n in atTop, u ∈ V n})
    (hstable : ∀ u ∈ S, (∀ᶠ n in atTop, u ∈ V n) ∨
      (∀ᶠ n in atTop, u ∉ V n)) (hAne : A.Nonempty) (hBne : (S \ A).Nonempty) :
    ∃ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 ∧
      HasBoundaryDirection K δ ∧ HasDirectionalEarthquake K δ S := by
  have hS : TilesOn K S E := Tiling.Polygonal.Topology.tilesOn_isClosed htiles hconv
  have hAS : A ⊆ S := hA ▸ eventual_part_subset V S
  have hApresent : ∀ a ∈ A, ∀ᶠ n in atTop, a ∈ V n := by
    intro a ha
    exact (hA ▸ ha).2
  have hW : properVertices (regularSupport K (S \ A)) = ∅ :=
    transient_cornerFree_of_local_germs (fun n => (htiles n).2.1) hconv hA hstable
      (fun x _ => fixedBackground_cancel htiles hS hAS hApresent x)
  have hdisj : Disjoint (regularSupport K A) (regularSupport K (S \ A)) :=
    regularSupport_disjoint_of_disjoint_subfamilies hS.2.1 hAS Set.sdiff_subset
      Set.disjoint_sdiff_right
  have hproper : regularSupport K (S \ A) ≠ univ := by
    intro heq
    obtain ⟨x, hx⟩ := regularSupport_nonempty hAne
    exact (Set.disjoint_left.mp hdisj) hx (heq ▸ Set.mem_univ x)
  have hpB : IsPacking K.prototileFamily (K.placements (S \ A)) :=
    hS.2.1.mono fun _ h => h.1
  obtain ⟨δ, hδ, hboundary, hBinv⟩ := cornerFree_carrier_invariant hBne hpB hproper hW
  refine ⟨δ, hδ, hboundary, S \ A, hBne, Set.sdiff_subset, ?_, hBinv⟩
  intro heq
  obtain ⟨a, ha⟩ := hAne
  have hmem : a ∈ S \ A := heq.symm ▸ hAS ha
  exact hmem.2 ha

/-- In the proper-vertex carrier case, a lattice-period translate of the
carrier vertex yields a nearby tile centre and an intrinsic vertex label.
After fixing that finite label, the shift `-λ` anchors exactly at `p - v`. -/
private theorem transverse_linearMap_for_direction (δ : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) :
    ∃ (π : Plane →ₗ[ℝ] ℝ) (e : Plane), e ≠ 0 ∧ e ∈ δ ∧
      π e = 0 ∧ LinearMap.ker π = δ := by
  have hδbot : δ ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at hδ
    exact Nat.zero_ne_one hδ
  obtain ⟨e, heδ, he⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδbot
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hδ heδ he
  let π : Plane →ₗ[ℝ] ℝ :=
    { toFun := fun z => (z / e).im
      map_add' := fun z w => by simp only [add_div, Complex.add_im]
      map_smul' := fun r z => by
        simp [Complex.real_smul, mul_div_assoc, Complex.mul_im] }
  have hdecomp : ∀ z : Plane,
      z = (z / e).re • e + (z / e).im • (e * Complex.I) := by
    intro z
    symm
    calc
      (z / e).re • e + (z / e).im • (e * Complex.I) =
          ((z / e).re + (z / e).im * Complex.I) * e := by
            simp only [Complex.real_smul]
            ring
      _ = z := by rw [Complex.re_add_im, div_mul_cancel₀ _ he]
  refine ⟨π, e, he, heδ, ?_, ?_⟩
  · change (e / e).im = 0
    simp [he]
  · ext z
    rw [LinearMap.mem_ker, hspan, Submodule.mem_span_singleton]
    constructor
    · intro hz
      refine ⟨(z / e).re, ?_⟩
      have hz' : (z / e).im = 0 := hz
      simpa only [hz', zero_smul, add_zero] using (hdecomp z).symm
    · rintro ⟨r, rfl⟩
      change ((r • e) / e).im = 0
      simp [Complex.real_smul, he]

private theorem invariantAlong_frontier {D : Set Plane} {δ : Submodule ℝ Plane}
    (hD : IsInvariantAlong D δ) : IsInvariantAlong (frontier D) δ := by
  intro u hu
  have h := (Homeomorph.addLeft u).image_frontier D
  change u +ᵥ frontier D = frontier (u +ᵥ D) at h
  rwa [hD u hu] at h

private theorem properVertex_coarseTileAnchors {K : PolygonalRegion} {T E : Set Plane}
    (hT : TilesOn K T E) (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (L : PlanarLattice) (hL : L.toAddSubgroup ≤ aePeriodGroup E)
    {p : Plane} (hp : p ∈ properVertices E) :
    ∃ C : ℝ, ∀ a : Plane, ∃ (ell : L.toAddSubgroup) (v q : Plane),
      v ∈ vertexSet K.support ∧ q ∈ T ∧ q - (ell : Plane) = p - v ∧ dist q a ≤ C := by
  obtain ⟨Rl, _, hRl⟩ := planarLattice_boundedCosetRepresentative L
  obtain ⟨Rv, hRv⟩ := K.isPolygonal.vertexSet_finite.isBounded.subset_closedBall (0 : Plane)
  have hsupport : regularSupport K T = E :=
    regularSupport_eq_of_tilesOn hEopen hEregular hT
  refine ⟨Rl + Rv, ?_⟩
  intro a
  obtain ⟨ell, hell, hnear⟩ := hRl (a - p)
  let ellL : L.toAddSubgroup := ⟨ell, hell⟩
  have hellperiod : ell ∈ periodGroup E := by
    rw [← aePeriodGroup_eq_periodGroup_of_regularOpen hEopen hEregular]
    exact hL hell
  have htranslate : ell +ᵥ E = E := AddAction.mem_stabilizer_iff.mp hellperiod
  have hp' : ell + p ∈ properVertices E := by
    rw [← htranslate, properVertices_vadd]
    exact Set.mem_vadd_set.mpr ⟨p, hp, rfl⟩
  rw [← hsupport] at hp'
  obtain ⟨v, hv, q, hq, heq⟩ := properVertexProvenance hT.2.1 (ell + p) hp'
  refine ⟨ellL, v, q, hv, hq, ?_, ?_⟩
  · dsimp [ellL]
    linear_combination -heq
  · have hvbound : ‖v‖ ≤ Rv := by simpa using hRv hv
    have hnear' : ‖ell + p - a‖ ≤ Rl := by
      have hid : ell + p - a = -(a - p - ell) := by abel
      simpa only [hid, norm_neg] using hnear
    rw [dist_eq_norm]
    have hid : q - a = (ell + p - a) - v := by linear_combination -heq
    rw [hid]
    exact (norm_sub_le _ _).trans (add_le_add hnear' hvbound)

private theorem stripe_coarseTileAnchors {K : PolygonalRegion} {T E : Set Plane}
    (hT : TilesOn K T E) (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (L : PlanarLattice) (hL : L.toAddSubgroup ≤ aePeriodGroup E)
    {δ : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1)
    (hEinv : IsInvariantAlong E δ) {p : Plane} (hp : p ∈ frontier E) :
    ∃ C : ℝ, ∀ a : Plane, ∃ (ell : L.toAddSubgroup) (v q : Plane),
      v ∈ vertexSet K.support ∧ q ∈ T ∧
        q + v - p - (ell : Plane) ∈ δ ∧ dist q a ≤ C := by
  obtain ⟨π, e, he, heδ, hπe, hker⟩ := transverse_linearMap_for_direction δ hδ
  obtain ⟨Rl, _, hRl⟩ := planarLattice_boundedCosetRepresentative L
  obtain ⟨Rv, _, hRv⟩ := Tiling.Polygonal.frontierLevel_has_bounded_intrinsicVertex K T hT.2.1 π e he hπe
  have hsupport : regularSupport K T = E :=
    regularSupport_eq_of_tilesOn hEopen hEregular hT
  have hfront := invariantAlong_frontier hEinv
  refine ⟨Rv + Rl, ?_⟩
  intro a
  obtain ⟨ell, hell, hnear⟩ := hRl (a - p)
  let ellL : L.toAddSubgroup := ⟨ell, hell⟩
  have hellperiod : ell ∈ periodGroup E := by
    rw [← aePeriodGroup_eq_periodGroup_of_regularOpen hEopen hEregular]
    exact hL hell
  have htranslate : ell +ᵥ E = E := AddAction.mem_stabilizer_iff.mp hellperiod
  have hx : p + ell ∈ frontier E := by
    have hh := (Homeomorph.addLeft ell).image_frontier E
    change ell +ᵥ frontier E = frontier (ell +ᵥ E) at hh
    rw [htranslate] at hh
    rw [← hh]
    exact Set.mem_vadd_set.mpr ⟨p, hp, add_comm _ _⟩
  have hline : {y | π y = π (p + ell)} ⊆ frontier (regularSupport K T) := by
    intro y hy
    have hdiff : y - (p + ell) ∈ δ := by
      rw [← hker, LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr hy
    rw [hsupport, ← hfront (y - (p + ell)) hdiff]
    exact Set.mem_vadd_set.mpr ⟨p + ell, hx, by simp⟩
  obtain ⟨v, q, hv, hq, hlevel, hqx⟩ := hRv (p + ell) hline
  refine ⟨ellL, v, q, hv, hq, ?_, ?_⟩
  · rw [← hker, LinearMap.mem_ker]
    change π (q + v - p - ell) = 0
    simp only [map_sub, map_add] at hlevel ⊢
    linarith
  · have hxa : dist (p + ell) a ≤ Rl := by
      rw [dist_eq_norm]
      have hid : p + ell - a = -(a - p - ell) := by abel
      simpa only [hid, norm_neg] using hnear
    exact (dist_triangle q (p + ell) a).trans (add_le_add hqx hxa)

/-- Non-FLC local finiteness leaves infinitely many bounded differences. The
injective sequence is shifted past the possible single equality with its limit. -/
private theorem nonFLC_converging_differences {T : Set Plane}
    (hlocal : ∀ Q : Set Plane, Bornology.IsBounded Q → (T ∩ Q).Finite)
    (hnon : ¬HasFLC T) :
    ∃ (a b : ℕ → Plane) (d : Plane),
      (∀ n, a n ∈ T) ∧ (∀ n, b n ∈ T) ∧
      (∀ n, b n - a n ≠ d) ∧ Tendsto (fun n => b n - a n) atTop (𝓝 d) := by
  classical
  have hinf : ∃ R : ℝ, 0 < R ∧ ¬((T - T) ∩ Metric.closedBall 0 R).Finite := by
    by_contra h
    push Not at h
    exact hnon ⟨hlocal, h⟩
  obtain ⟨R, hR, hinf⟩ := hinf
  let D := (T - T) ∩ Metric.closedBall 0 R
  let f : ℕ ↪ D := Set.Infinite.natEmbedding D hinf
  have hfmem : ∀ n, (f n : Plane) ∈ Metric.closedBall 0 R := fun n => (f n).2.2
  obtain ⟨d, _, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : Plane) R).tendsto_subseq hfmem
  have hfi : Injective (fun n => (f (φ n) : Plane)) :=
    Subtype.val_injective.comp (f.injective.comp hφ.injective)
  have hne : ∀ᶠ n in atTop, (f (φ n) : Plane) ≠ d :=
    (hfi.tendsto_cofinite.mono_left atTop_le_cofinite).eventually (eventually_cofinite_ne d)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hne
  have hpairs : ∀ n, ∃ a ∈ T, ∃ b ∈ T, b - a = (f (φ (n + N)) : Plane) := by
    intro n
    obtain ⟨b, hb, a, ha, hba⟩ := Set.mem_sub.mp (f (φ (n + N))).2.1
    exact ⟨a, ha, b, hb, hba⟩
  choose a ha b hb hba using hpairs
  refine ⟨a, b, d, ha, hb, ?_, ?_⟩
  · intro n
    rw [hba n]
    exact hN (n + N) (Nat.le_add_left N n)
  · simpa only [hba, Function.comp_def] using hlim.comp (tendsto_add_atTop_nat N)

private theorem nonFLC_boundedDifferencePairs {T : Set Plane}
    (hlocal : ∀ Q : Set Plane, Bornology.IsBounded Q → (T ∩ Q).Finite)
    (hnon : ¬HasFLC T) :
    ∃ (a b : ℕ → Plane) (R : ℝ), 0 < R ∧
      (∀ n, a n ∈ T) ∧ (∀ n, b n ∈ T) ∧
      (∀ n, dist (b n) (a n) ≤ R) ∧ Injective (fun n => b n - a n) := by
  classical
  have hinf : ∃ R : ℝ, 0 < R ∧ ¬((T - T) ∩ Metric.closedBall 0 R).Finite := by
    by_contra h
    push Not at h
    exact hnon ⟨hlocal, h⟩
  obtain ⟨R, hR, hinf⟩ := hinf
  let D := (T - T) ∩ Metric.closedBall 0 R
  let f : ℕ ↪ D := Set.Infinite.natEmbedding D hinf
  have hpairs : ∀ n, ∃ a ∈ T, ∃ b ∈ T, b - a = (f n : Plane) := by
    intro n
    obtain ⟨b, hb, a, ha, heq⟩ := Set.mem_sub.mp (f n).2.1
    exact ⟨a, ha, b, hb, heq⟩
  choose a ha b hb hba using hpairs
  refine ⟨a, b, R, hR, ha, hb, ?_, ?_⟩
  · intro n
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, ← hba n] using (f n).2.2
  · intro m n heq
    apply f.injective
    apply Subtype.ext
    simpa only [← hba] using heq

private def increasingInSet {s : Set ℕ} (hs : s.Infinite) : ℕ → ℕ
  | 0 => Classical.choose (hs.exists_gt 0)
  | n + 1 => Classical.choose (hs.exists_gt (increasingInSet hs n))

private theorem increasingInSet_mem {s : Set ℕ} (hs : s.Infinite) (n : ℕ) :
    increasingInSet hs n ∈ s := by
  cases n with
  | zero => exact (Classical.choose_spec (hs.exists_gt 0)).1
  | succ n => exact (Classical.choose_spec (hs.exists_gt (increasingInSet hs n))).1

private theorem increasingInSet_strictMono {s : Set ℕ} (hs : s.Infinite) :
    StrictMono (increasingInSet hs) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Classical.choose_spec (hs.exists_gt (increasingInSet hs n))).2

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
  let phi₀ : ℕ → ℕ := increasingInSet hcf
  have hphi₀ : StrictMono phi₀ := increasingInSet_strictMono hcf
  have hlabel (n : ℕ) : label (phi₀ n) = c :=
    increasingInSet_mem hcf n
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
    let theta : ℕ → ℕ := increasingInSet hirange
    have htheta : StrictMono theta := increasingInSet_strictMono hirange
    refine ⟨theta, htheta, ?_⟩
    intro m n hmn
    obtain ⟨i, hi⟩ := increasingInSet_mem hirange m
    obtain ⟨j, hj⟩ := increasingInSet_mem hirange n
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

private theorem infinite_fiber_bool {s : Set ℕ} (hs : s.Infinite) (f : ℕ → Bool) :
    ∃ b : Bool, {n | n ∈ s ∧ f n = b}.Infinite := by
  by_contra h
  push Not at h
  have h0 : {n | n ∈ s ∧ f n = false}.Finite := by
    exact h false
  have h1 : {n | n ∈ s ∧ f n = true}.Finite := by
    exact h true
  have hunion : s = {n | n ∈ s ∧ f n = false} ∪ {n | n ∈ s ∧ f n = true} := by
    ext n
    simp only [mem_union, mem_ofPred_eq]
    constructor
    · intro hn
      cases f n <;> simp [hn]
    · intro hn
      rcases hn with hn | hn <;> exact hn.1
  exact hs (hunion ▸ h0.union h1)

private def stages (p : ℕ → ℕ → Bool) : ℕ → {s : Set ℕ // s.Infinite}
  | 0 => ⟨univ, Set.infinite_univ⟩
  | n + 1 => by
      let b := Classical.choose (infinite_fiber_bool (stages p n).property (p n))
      refine ⟨{i | i ∈ (stages p n).val ∧ p n i = b}, ?_⟩
      simpa [b] using (Classical.choose_spec
        (infinite_fiber_bool (stages p n).property (p n)))

private theorem stages_mem (p : ℕ → ℕ → Bool) (n : ℕ) :
    (stages p (n + 1)).val ⊆ (stages p n).val := by
  intro i hi
  exact hi.1

private theorem stages_down (p : ℕ → ℕ → Bool) (k n : ℕ) (h : k ≤ n) :
    (stages p n).val ⊆ (stages p k).val := by
  induction h with
  | refl => exact Subset.rfl
  | @step n h ih => exact (stages_mem p n).trans ih

private theorem stages_agree (p : ℕ → ℕ → Bool) (n i : ℕ)
    (hi : i ∈ (stages p (n + 1)).val) :
    p n i = Classical.choose (infinite_fiber_bool (stages p n).property (p n)) := hi.2

private def diagonalIndex (p : ℕ → ℕ → Bool) : ℕ → ℕ
  | 0 => Classical.choose ((stages p 0).property.exists_gt 0)
  | n + 1 => Classical.choose ((stages p (n + 1)).property.exists_gt (diagonalIndex p n))

private theorem diagonalIndex_mem (p : ℕ → ℕ → Bool) (n : ℕ) :
    diagonalIndex p n ∈ (stages p n).val := by
  induction n with
  | zero =>
      exact (Classical.choose_spec ((stages p 0).property.exists_gt 0)).1
  | succ n ih =>
      exact (Classical.choose_spec
        ((stages p (n + 1)).property.exists_gt (diagonalIndex p n))).1

private theorem diagonalIndex_strictMono (p : ℕ → ℕ → Bool) :
    StrictMono (diagonalIndex p) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Classical.choose_spec
    ((stages p (n + 1)).property.exists_gt (diagonalIndex p n))).2

private theorem diagonal_eventually_constant (p : ℕ → ℕ → Bool) (k : ℕ) :
    ∀ᶠ n in atTop, p k (diagonalIndex p n) =
      Classical.choose (infinite_fiber_bool (stages p k).property (p k)) := by
  filter_upwards [Filter.eventually_ge_atTop (k + 1)] with n hn
  have hmem : diagonalIndex p n ∈ (stages p (k + 1)).val := by
    exact stages_down p (k + 1) n hn (diagonalIndex_mem p n)
  exact stages_agree p k (diagonalIndex p n) hmem

theorem diagonal_stabilizesCentres :
∀ (A : ℕ → Set Plane) (S : Set Plane), S.Countable →
    ∃ ι : ℕ → ℕ, StrictMono ι ∧ ∀ u ∈ S,
      (∀ᶠ n in atTop, u ∈ A (ι n)) ∨ (∀ᶠ n in atTop, u ∉ A (ι n))
  := by
  intro A S hS
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨e, he⟩ := (Set.countable_iff_exists_surjective hne).mp hS
    let p : ℕ → ℕ → Bool := fun k n => decide ((e k).1 ∈ A n)
    refine ⟨diagonalIndex p, diagonalIndex_strictMono p, ?_⟩
    intro u hu
    obtain ⟨k, hk⟩ := he ⟨u, hu⟩
    have hev := diagonal_eventually_constant p k
    have hev' : ∀ᶠ n in atTop, decide (u ∈ A (diagonalIndex p n)) =
        Classical.choose (infinite_fiber_bool (stages p k).property (p k)) := by
      simpa [p, hk] using hev
    by_cases hb : Classical.choose (infinite_fiber_bool (stages p k).property (p k)) = true
    · left
      filter_upwards [hev'] with n hn
      have : decide (u ∈ A (diagonalIndex p n)) = true := hn.trans hb
      exact of_decide_eq_true this
    · right
      filter_upwards [hev'] with n hn
      have : decide (u ∈ A (diagonalIndex p n)) = false := by
        have hv := hn
        have hb' : Classical.choose (infinite_fiber_bool (stages p k).property (p k)) = false := by
          cases hc : Classical.choose (infinite_fiber_bool (stages p k).property (p k)) <;> simp_all
        rw [hb'] at hv
        exact hv
      exact of_decide_eq_false this
  · refine ⟨id, strictMono_id, ?_⟩
    intro u hu
    exact (hne ⟨u, hu⟩).elim

theorem nonFLC_anchoredWholePlaneLimit :
∀ (K : PolygonalRegion) (T : Set Plane), TilesOn K T Set.univ → ¬HasFLC T →
    ∃ (S : Set Plane) (t s : Plane) (movingCentre g : ℕ → Plane),
      t ∈ T ∧ (∀ n, movingCentre n ∈ T) ∧
      (∀ n, t ∈ g n +ᵥ T) ∧
      Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S ∧
      s ∈ S ∧ (∀ n, movingCentre n + g n ≠ s) ∧
      Tendsto (fun n => movingCentre n + g n) atTop (𝓝 s) ∧
      (∀ u ∈ S, (∀ᶠ n in atTop, u ∈ g n +ᵥ T) ∨
        (∀ᶠ n in atTop, u ∉ g n +ᵥ T))
  := by
  intro K T hT hnon
  obtain ⟨hlocal, hcount, hclosed⟩ := packing_centres_locallyFinite hT.2.1
  obtain ⟨a, b, d, ha, hb, hne, hd⟩ := nonFLC_converging_differences hlocal hnon
  let t := a 0
  let g : ℕ → Plane := fun n => t - a n
  have htile : ∀ n, TilesOn K (g n +ᵥ T) univ := by
    intro n
    simpa using tilesOn_translate hT (g n)
  obtain ⟨ε, hε, hsep⟩ := exists_packingSeparation K
  have hsepseq : ∀ n, Tiling.Topology.IsUniformlySeparated ε (g n +ᵥ T) :=
    fun n => hsep _ (htile n).2.1
  have hclosedseq : ∀ n, IsClosed (g n +ᵥ T) :=
    fun n => (packing_centres_locallyFinite (htile n).2.1).2.2
  obtain ⟨φ, S, hφ, hSclosed, hSsep, hconv⟩ :=
    Tiling.Topology.exists_locallyFellConvergent_subsequence ε hε
      (fun n => g n +ᵥ T) hclosedseq hsepseq
  have hSlim : TilesOn K S univ :=
    Tiling.Polygonal.Topology.tilesOn_isClosed (fun n => htile (φ n)) hconv
  have hfixed : ∀ n, t ∈ g n +ᵥ T := by
    intro n
    exact Set.mem_vadd_set.mpr ⟨a n, ha n, by simp [g]⟩
  have hmoving : ∀ n, b n + g n ∈ g n +ᵥ T := by
    intro n
    exact Set.mem_vadd_set.mpr ⟨b n, hb n, add_comm _ _⟩
  have hmovinglim : Tendsto (fun n => b n + g n) atTop (𝓝 (t + d)) := by
    have heq : (fun n => b n + g n) = (fun n => t + (b n - a n)) := by
      funext n
      simp only [g]
      abel
    rw [heq]
    exact tendsto_const_nhds.add hd
  have hmovingne : ∀ n, b n + g n ≠ t + d := by
    intro n heq
    apply hne n
    dsimp [g] at heq
    linear_combination heq
  have hs : t + d ∈ S :=
    Tiling.Topology.mem_of_locallyFellConverges_of_tendsto_mem hconv
      (fun n => hmoving (φ n)) (hmovinglim.comp hφ.tendsto_atTop)
  obtain ⟨ι, hι, hstable⟩ := diagonal_stabilizesCentres
    (fun n => g (φ n) +ᵥ T) S hSlim.1
  refine ⟨S, t, t + d, b ∘ φ ∘ ι, g ∘ φ ∘ ι, ha 0,
    fun n => hb (φ (ι n)), fun n => hfixed (φ (ι n)),
    locallyFell_subsequence hconv hι, hs,
    fun n => hmovingne (φ (ι n)), ?_, hstable⟩
  exact (hmovinglim.comp hφ.tendsto_atTop).comp hι.tendsto_atTop

theorem stabilizedWholePlaneLimit_earthquake :
∀ (K : PolygonalRegion) (T S A : Set Plane) (g : ℕ → Plane),
    TilesOn K T Set.univ →
    Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S →
    A = {u | u ∈ S ∧ ∀ᶠ n in atTop, u ∈ g n +ᵥ T} →
    (∀ u ∈ S, (∀ᶠ n in atTop, u ∈ g n +ᵥ T) ∨
      (∀ᶠ n in atTop, u ∉ g n +ᵥ T)) →
    A.Nonempty → (S \ A).Nonempty →
      ∃ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 ∧ HasBoundaryDirection K δ ∧
        IsInvariantAlong (regularSupport K A) δ ∧
          IsInvariantAlong (regularSupport K (S \ A)) δ
  := by
  intro K T S A g hT hconv hA hstable hAne hBne
  have htiles : ∀ n, TilesOn K (g n +ᵥ T) univ := by
    intro n
    simpa using tilesOn_translate hT (g n)
  have hS : TilesOn K S univ := Tiling.Polygonal.Topology.tilesOn_isClosed htiles hconv
  have hAS : A ⊆ S := hA ▸ eventual_part_subset (fun n => g n +ᵥ T) S
  have hApresent : ∀ a ∈ A, ∀ᶠ n in atTop, a ∈ g n +ᵥ T := by
    intro a ha
    exact (hA ▸ ha).2
  have hW : properVertices (regularSupport K (S \ A)) = ∅ :=
    transient_cornerFree_of_local_germs (fun n => (htiles n).2.1) hconv hA hstable
      (fun x _ => fixedBackground_cancel htiles hS hAS hApresent x)
  have hBS : S \ A ⊆ S := Set.sdiff_subset
  have hdisj : Disjoint (regularSupport K A) (regularSupport K (S \ A)) :=
    regularSupport_disjoint_of_disjoint_subfamilies hS.2.1 hAS hBS Set.disjoint_sdiff_right
  have hproper : regularSupport K (S \ A) ≠ univ := by
    intro heq
    obtain ⟨x, hx⟩ := regularSupport_nonempty hAne
    exact (Set.disjoint_left.mp hdisj) hx (heq ▸ Set.mem_univ x)
  have hpB : IsPacking K.prototileFamily (K.placements (S \ A)) :=
    hS.2.1.mono fun _ h => h.1
  obtain ⟨δ, hδ, hboundary, hBinv⟩ := cornerFree_carrier_invariant hBne hpB hproper hW
  have hunion : A ∪ (S \ A) = S := Set.union_sdiff_cancel hAS
  have hsupportS : regularSupport K S = univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) hS
  have hfull : univ = interior
      (closure (regularSupport K A ∪ regularSupport K (S \ A))) := by
    rw [← regularSupport_union, hunion, hsupportS]
  have hcomplement := (regularOpen_disjoint_complement
    (regularSupport_isRegularOpen K A).1 (regularSupport_isRegularOpen K A).2
    (regularSupport_isRegularOpen K (S \ A)).1
    (regularSupport_isRegularOpen K (S \ A)).2 hdisj hfull).1
  refine ⟨δ, hδ, hboundary, ?_, hBinv⟩
  rw [hcomplement]
  exact invariant_regularOpen_complement (fun _ _ => Set.vadd_set_univ) hBinv

private theorem anchoredMovingSequence_earthquakeLimit {K : PolygonalRegion}
    {E : Set Plane} {V : ℕ → Set Plane} (hV : ∀ n, TilesOn K (V n) E)
    (t : Plane) (ht : ∀ n, t ∈ V n) (z : ℕ → Plane)
    (hz : ∀ n, z n ∈ V n) (hinj : Injective z) {R : ℝ}
    (hbound : ∀ n, z n ∈ Metric.closedBall t R) :
    ∃ (φ : ℕ → ℕ) (S : Set Plane) (δ : Submodule ℝ Plane), StrictMono φ ∧
      Tiling.Topology.LocallyFellConverges (V ∘ φ) S ∧
      Module.finrank ℝ δ = 1 ∧ HasBoundaryDirection K δ ∧
      HasDirectionalEarthquake K δ S := by
  obtain ⟨s, _, φ₀, hφ₀, hzlim⟩ := (isCompact_closedBall t R).tendsto_subseq hbound
  obtain ⟨ψ, hψ, _, hzlim', hne⟩ := injective_subsequence_avoiding_limit
    (hinj.comp hφ₀.injective) hzlim
  let θ := φ₀ ∘ ψ
  have hθ : StrictMono θ := hφ₀.comp hψ
  obtain ⟨ε, hε, hsep⟩ := exists_packingSeparation K
  have hsepV : ∀ n, Tiling.Topology.IsUniformlySeparated ε (V n) :=
    fun n => hsep _ (hV n).2.1
  have hclosed : ∀ n, IsClosed (V n) :=
    fun n => (packing_centres_locallyFinite (hV n).2.1).2.2
  obtain ⟨φ₁, S, hφ₁, _, _, hconv⟩ :=
    Tiling.Topology.exists_locallyFellConvergent_subsequence ε hε
      (V ∘ θ) (fun n => hclosed (θ n)) (fun n => hsepV (θ n))
  let κ := θ ∘ φ₁
  have hκ : StrictMono κ := hθ.comp hφ₁
  have hS : TilesOn K S E :=
    Tiling.Polygonal.Topology.tilesOn_isClosed (fun n => hV (κ n)) hconv
  have hs : s ∈ S := Tiling.Topology.mem_of_locallyFellConverges_of_tendsto_mem hconv
    (fun n => hz (κ n)) (hzlim'.comp hφ₁.tendsto_atTop)
  have htS : t ∈ S := Tiling.Topology.mem_of_locallyFellConverges_of_tendsto_mem hconv
    (fun n => ht (κ n)) tendsto_const_nhds
  obtain ⟨ι, hι, hstable⟩ := diagonal_stabilizesCentres (V ∘ κ) S hS.1
  let φ := κ ∘ ι
  have hφ : StrictMono φ := hκ.comp hι
  have hconv' : Tiling.Topology.LocallyFellConverges (V ∘ φ) S :=
    locallyFell_subsequence hconv hι
  let A : Set Plane := {u | u ∈ S ∧ ∀ᶠ n in atTop, u ∈ V (φ n)}
  have hAne : A.Nonempty := ⟨t, htS, Eventually.of_forall fun n => ht (φ n)⟩
  have hzne : ∀ n, z (φ n) ≠ s := fun n => hne (φ₁ (ι n))
  have hzlim'' : Tendsto (z ∘ φ) atTop (𝓝 s) :=
    (hzlim'.comp hφ₁.tendsto_atTop).comp hι.tendsto_atTop
  have habsent : ∀ᶠ n in atTop, s ∉ V (φ n) :=
    moving_limit_eventually_absent hε (fun n => hsepV (φ n))
      (fun n => hz (φ n)) hzne hzlim''
  have hBne : (S \ A).Nonempty := by
    refine ⟨s, hs, ?_⟩
    intro hsa
    obtain ⟨n, hn⟩ := (hsa.2.and habsent).exists
    exact hn.2 hn.1
  obtain ⟨δ, hδ, hboundary, hquake⟩ := stabilizedLimit_transientEarthquake
    (fun n => hV (φ n)) hconv' rfl hstable hAne hBne
  exact ⟨φ, S, δ, hφ, hconv', hδ, hboundary, hquake⟩

private theorem lattice_correction_preserves_directionalEarthquake
    {K : PolygonalRegion} {T E S : Set Plane} {δ : Submodule ℝ Plane}
    (hT : TilesOn K T E) (hEopen : IsOpen E)
    (hEreg : interior (closure E) = E) (g : ℕ → aePeriodGroup E)
    (hconv : Tiling.Topology.LocallyFellConverges
      (fun n => (g n : Plane) +ᵥ T) S)
    (hquake : HasDirectionalEarthquake K δ S) (L : PlanarLattice)
    (hL : L.toAddSubgroup ≤ aePeriodGroup E) :
    ∃ (S' : Set Plane) (ℓ : ℕ → L.toAddSubgroup),
      Tiling.Topology.LocallyFellConverges (fun n => (ℓ n : Plane) +ᵥ T) S' ∧
      TilesOn K S' E ∧ HasDirectionalEarthquake K δ S' := by
  classical
  have hTclosed : IsClosed T := (packing_centres_locallyFinite hT.2.1).2.2
  let T0 : Tiling.Polygonal.Topology.TilingSpace K E := ⟨⟨T, hTclosed⟩, hT⟩
  have hconv0 : Tiling.Topology.LocallyFellConverges
      (fun n => (g n : Plane) +ᵥ (T0.centres : Set Plane)) S := by
    simpa [T0] using hconv
  obtain ⟨φ, ℓ, a, hφ, herror, hconv'⟩ :=
    Tiling.Polygonal.Topology.latticeRestricted_hull_limit
      hEopen hEreg g hconv0 L hL
  have hperiod : ∀ n, (ℓ n : Plane) +ᵥ E = E := by
    intro n
    have hae : (ℓ n : Plane) ∈ aePeriodGroup E := hL (ℓ n).property
    have heq : ((ℓ n : Plane) ∈ aePeriodGroup E) =
        ((ℓ n : Plane) ∈ periodGroup E) :=
      congrArg (fun G : AddSubgroup Plane => (ℓ n : Plane) ∈ G)
        (aePeriodGroup_eq_periodGroup_of_regularOpen hEopen hEreg)
    have hp : (ℓ n : Plane) ∈ periodGroup E := heq.mp hae
    exact AddAction.mem_stabilizer_iff.mp hp
  have htiles : ∀ n, TilesOn K ((ℓ n : Plane) +ᵥ T) E := by
    intro n
    have htranslated := tilesOn_translate hT (ℓ n : Plane)
    rw [hperiod n] at htranslated
    exact htranslated
  refine ⟨(a : Plane) +ᵥ S, ℓ, hconv', ?_, ?_⟩
  · exact Tiling.Polygonal.Topology.tilesOn_isClosed htiles hconv'
  · exact directionalEarthquake_vadd hquake (a : Plane)

theorem nonFLC_earthquakeLimit_inPrescribedLattice :
∀ (K : PolygonalRegion) (T E : Set Plane), TilesOn K T E → E.Nonempty →
    IsOpen E → interior (closure E) = E → ¬HasFLC T →
      ∀ L : PlanarLattice, L.toAddSubgroup ≤ aePeriodGroup E →
        ∃ (S : Set Plane) (g : ℕ → L.toAddSubgroup) (δ : Submodule ℝ Plane),
          Tiling.Topology.LocallyFellConverges (fun n => (g n : Plane) +ᵥ T) S ∧
          TilesOn K S E ∧ Module.finrank ℝ δ = 1 ∧ HasBoundaryDirection K δ ∧
          HasDirectionalEarthquake K δ S
  := by
  intro K T E hT hEne hEopen hEreg hnon L hL
  by_cases hE : E = univ
  · subst E
    obtain ⟨S, t, s, z, g, ht, hzT, hfixed, hconv, hs, hzne, hzlim, hstable⟩ :=
      nonFLC_anchoredWholePlaneLimit K T hT hnon
    let A : Set Plane := {u | u ∈ S ∧ ∀ᶠ n in atTop, u ∈ g n +ᵥ T}
    have htS : t ∈ S := Tiling.Topology.mem_of_locallyFellConverges_of_tendsto_mem
      hconv hfixed tendsto_const_nhds
    have hAne : A.Nonempty := ⟨t, htS, Eventually.of_forall hfixed⟩
    have htiles : ∀ n, TilesOn K (g n +ᵥ T) univ := by
      intro n
      simpa using tilesOn_translate hT (g n)
    obtain ⟨ε, hε, hsep⟩ := exists_packingSeparation K
    have hzmem : ∀ n, z n + g n ∈ g n +ᵥ T := by
      intro n
      exact Set.mem_vadd_set.mpr ⟨z n, hzT n, add_comm _ _⟩
    have habsent : ∀ᶠ n in atTop, s ∉ g n +ᵥ T :=
      moving_limit_eventually_absent hε (fun n => hsep _ (htiles n).2.1)
        hzmem hzne hzlim
    have hBne : (S \ A).Nonempty := by
      refine ⟨s, hs, ?_⟩
      intro hsa
      obtain ⟨n, hn⟩ := (hsa.2.and habsent).exists
      exact hn.2 hn.1
    obtain ⟨δ, hδ, hboundary, hquake⟩ := stabilizedLimit_transientEarthquake
      htiles hconv rfl hstable hAne hBne
    have hgamma : ∀ n, g n ∈ aePeriodGroup (univ : Set Plane) := by
      intro n
      rw [aePeriodGroup_eq_periodGroup_of_regularOpen isOpen_univ (by simp)]
      exact AddAction.mem_stabilizer_iff.mpr Set.vadd_set_univ
    let gΓ : ℕ → aePeriodGroup (univ : Set Plane) := fun n => ⟨g n, hgamma n⟩
    obtain ⟨S', ell, hconv', htiles', hquake'⟩ :=
      lattice_correction_preserves_directionalEarthquake hT hEopen hEreg gΓ hconv
        hquake L hL
    exact ⟨S', ell, δ, hconv', htiles', hδ, hboundary, hquake'⟩
  · by_cases hcorner : (properVertices E).Nonempty
    · classical
      obtain ⟨p, hp⟩ := hcorner
      obtain ⟨a, b, R, hR, ha, hb, hpairbound, hdiff⟩ :=
        nonFLC_boundedDifferencePairs (packing_centres_locallyFinite hT.2.1).1 hnon
      obtain ⟨C, hanchors⟩ := properVertex_coarseTileAnchors hT hEopen hEreg L hL hp
      choose ell v q hv hq hqanchor hqbound using (fun n => hanchors (a n))
      let label : ℕ → vertexSet K.support := fun n => ⟨v n, hv n⟩
      let : Finite (vertexSet K.support) := K.isPolygonal.vertexSet_finite.to_subtype
      let u := q - a
      let w := q - b
      have huv : Injective (u - w) := by
        have heq : u - w = b - a := by funext n; simp only [u, w, Pi.sub_apply]; abel
        rw [heq]
        exact hdiff
      obtain ⟨φ, hφ, ⟨c, hlabel⟩, hinj⟩ :=
        exists_sameLabel_injectiveRelative_subsequence label u w huv
      have hmark : ∃ mark : ℕ → Plane,
          (∀ n, mark n = a n ∨ mark n = b n) ∧
          Injective (fun n => q (φ n) - mark (φ n)) := by
        rcases hinj with hinj | hinj
        · exact ⟨a, fun _ => Or.inl rfl, hinj⟩
        · exact ⟨b, fun _ => Or.inr rfl, hinj⟩
      obtain ⟨mark, hmark, hrel⟩ := hmark
      let anchor := p - c.1
      let γ : ℕ → aePeriodGroup E := fun n =>
        ⟨-(ell (φ n) : Plane), hL (L.toAddSubgroup.neg_mem (ell (φ n)).2)⟩
      let V : ℕ → Set Plane := fun n => (γ n : Plane) +ᵥ T
      let z : ℕ → Plane := fun n => mark (φ n) + (γ n : Plane)
      have hperiod : ∀ n, (γ n : Plane) +ᵥ E = E := by
        intro n
        apply AddAction.mem_stabilizer_iff.mp
        change (γ n : Plane) ∈ periodGroup E
        rw [← aePeriodGroup_eq_periodGroup_of_regularOpen hEopen hEreg]
        exact (γ n).2
      have hV : ∀ n, TilesOn K (V n) E := by
        intro n
        simpa only [V, hperiod n] using tilesOn_translate hT (γ n : Plane)
      have hqfixed : ∀ n, q (φ n) + (γ n : Plane) = anchor := by
        intro n
        have hvfixed : v (φ n) = c.1 := congrArg Subtype.val (hlabel n)
        simpa only [γ, anchor, sub_eq_add_neg, hvfixed] using hqanchor (φ n)
      have hfixed : ∀ n, anchor ∈ V n := by
        intro n
        exact Set.mem_vadd_set.mpr ⟨q (φ n), hq (φ n), (add_comm _ _).trans (hqfixed n)⟩
      have hz : ∀ n, z n ∈ V n := by
        intro n
        have hm : mark (φ n) ∈ T := by
          rcases hmark (φ n) with hm | hm
          · simpa only [hm] using ha (φ n)
          · simpa only [hm] using hb (φ n)
        exact Set.mem_vadd_set.mpr ⟨mark (φ n), hm, add_comm _ _⟩
      have hzform : ∀ n, z n = anchor - (q (φ n) - mark (φ n)) := by
        intro n
        rw [← hqfixed n]
        dsimp [z]
        abel
      have hzinj : Injective z := by
        intro i j hij
        apply hrel
        rw [hzform i, hzform j] at hij
        exact sub_right_injective hij
      have hbound : ∀ n, z n ∈ Metric.closedBall anchor (C + R) := by
        intro n
        have hmarked : dist (mark (φ n)) (q (φ n)) ≤ C + R := by
          rcases hmark (φ n) with hm | hm
          · rw [hm, dist_comm]
            exact (hqbound (φ n)).trans (le_add_of_nonneg_right hR.le)
          · rw [hm]
            calc
              dist (b (φ n)) (q (φ n)) ≤ dist (b (φ n)) (a (φ n)) +
                dist (a (φ n)) (q (φ n)) := dist_triangle _ _ _
              _ ≤ R + C := add_le_add (hpairbound (φ n)) (by simpa only [dist_comm] using hqbound (φ n))
              _ = C + R := add_comm _ _
        rw [Metric.mem_closedBall, hzform n, dist_eq_norm]
        simpa only [sub_sub_cancel_left, norm_neg, dist_eq_norm, norm_sub_rev] using hmarked
      obtain ⟨ψ, S, δ, hψ, hconv, hδ, hboundary, hquake⟩ :=
        anchoredMovingSequence_earthquakeLimit hV anchor hfixed z hz hzinj hbound
      obtain ⟨S', corrected, hconv', htiles', hquake'⟩ :=
        lattice_correction_preserves_directionalEarthquake hT hEopen hEreg (γ ∘ ψ)
          hconv hquake L hL
      exact ⟨S', corrected, δ, hconv', htiles', hδ, hboundary, hquake'⟩
    · classical
      obtain ⟨a, b, R, hR, ha, hb, hpairbound, hdiff⟩ :=
        nonFLC_boundedDifferencePairs (packing_centres_locallyFinite hT.2.1).1 hnon
      have hsupport : regularSupport K T = E :=
        regularSupport_eq_of_tilesOn hEopen hEreg hT
      have hcorners : properVertices (regularSupport K T) = ∅ := by
        rw [hsupport]
        exact Set.not_nonempty_iff_eq_empty.mp hcorner
      obtain ⟨δ₀, hδ₀, _, hEinv⟩ := cornerFree_carrier_invariant
        (show T.Nonempty from ⟨a 0, ha 0⟩) hT.2.1 (by rwa [hsupport]) hcorners
      rw [hsupport] at hEinv
      obtain ⟨p, hp⟩ := nonempty_frontier_iff.mpr ⟨hEne, hE⟩
      obtain ⟨C, hanchors⟩ := stripe_coarseTileAnchors hT hEopen hEreg L hL hδ₀ hEinv hp
      choose ell v q hv hq hqdir hqbound using (fun n => hanchors (a n))
      let label : ℕ → vertexSet K.support := fun n => ⟨v n, hv n⟩
      let : Finite (vertexSet K.support) := K.isPolygonal.vertexSet_finite.to_subtype
      let u := q - a
      let w := q - b
      have huv : Injective (u - w) := by
        have heq : u - w = b - a := by funext n; simp only [u, w, Pi.sub_apply]; abel
        rw [heq]
        exact hdiff
      obtain ⟨φ, hφ, ⟨c, hlabel⟩, hinj⟩ :=
        exists_sameLabel_injectiveRelative_subsequence label u w huv
      have hmark : ∃ mark : ℕ → Plane,
          (∀ n, mark n = a n ∨ mark n = b n) ∧
          Injective (fun n => q (φ n) - mark (φ n)) := by
        rcases hinj with hinj | hinj
        · exact ⟨a, fun _ => Or.inl rfl, hinj⟩
        · exact ⟨b, fun _ => Or.inr rfl, hinj⟩
      obtain ⟨mark, hmark, hrel⟩ := hmark
      have hqperiod : ∀ n, q (φ 0) - q (φ n) ∈ aePeriodGroup E := by
        intro n
        have hv0 : v (φ 0) = c.1 := congrArg Subtype.val (hlabel 0)
        have hvn : v (φ n) = c.1 := congrArg Subtype.val (hlabel n)
        have hd : q (φ 0) - q (φ n) -
            ((ell (φ 0) : Plane) - (ell (φ n) : Plane)) ∈ δ₀ := by
          have hh := δ₀.sub_mem (hqdir (φ 0)) (hqdir (φ n))
          have heq : q (φ 0) + v (φ 0) - p - (ell (φ 0) : Plane) -
              (q (φ n) + v (φ n) - p - (ell (φ n) : Plane)) =
              q (φ 0) - q (φ n) - ((ell (φ 0) : Plane) - (ell (φ n) : Plane)) := by
            rw [hv0, hvn]
            abel
          rwa [heq] at hh
        have hdperiod : q (φ 0) - q (φ n) -
            ((ell (φ 0) : Plane) - (ell (φ n) : Plane)) ∈ aePeriodGroup E := by
          rw [aePeriodGroup_eq_periodGroup_of_regularOpen hEopen hEreg]
          exact AddAction.mem_stabilizer_iff.mpr (hEinv _ hd)
        have hellperiod : (ell (φ 0) : Plane) - (ell (φ n) : Plane) ∈ aePeriodGroup E :=
          hL (L.toAddSubgroup.sub_mem (ell (φ 0)).2 (ell (φ n)).2)
        simpa only [sub_add_cancel] using (aePeriodGroup E).add_mem hdperiod hellperiod
      let anchor := q (φ 0)
      let γ : ℕ → aePeriodGroup E := fun n => ⟨anchor - q (φ n), hqperiod n⟩
      let V : ℕ → Set Plane := fun n => (γ n : Plane) +ᵥ T
      let z : ℕ → Plane := fun n => mark (φ n) + (γ n : Plane)
      have hperiod : ∀ n, (γ n : Plane) +ᵥ E = E := by
        intro n
        apply AddAction.mem_stabilizer_iff.mp
        change (γ n : Plane) ∈ periodGroup E
        rw [← aePeriodGroup_eq_periodGroup_of_regularOpen hEopen hEreg]
        exact (γ n).2
      have hV : ∀ n, TilesOn K (V n) E := by
        intro n
        simpa only [V, hperiod n] using tilesOn_translate hT (γ n : Plane)
      have hqfixed : ∀ n, q (φ n) + (γ n : Plane) = anchor := by
        intro n
        dsimp [γ]
        abel
      have hfixed : ∀ n, anchor ∈ V n := by
        intro n
        exact Set.mem_vadd_set.mpr ⟨q (φ n), hq (φ n), (add_comm _ _).trans (hqfixed n)⟩
      have hz : ∀ n, z n ∈ V n := by
        intro n
        have hm : mark (φ n) ∈ T := by
          rcases hmark (φ n) with hm | hm
          · simpa only [hm] using ha (φ n)
          · simpa only [hm] using hb (φ n)
        exact Set.mem_vadd_set.mpr ⟨mark (φ n), hm, add_comm _ _⟩
      have hzform : ∀ n, z n = anchor - (q (φ n) - mark (φ n)) := by
        intro n
        rw [← hqfixed n]
        dsimp [z]
        abel
      have hzinj : Injective z := by
        intro i j hij
        apply hrel
        rw [hzform i, hzform j] at hij
        exact sub_right_injective hij
      have hbound : ∀ n, z n ∈ Metric.closedBall anchor (C + R) := by
        intro n
        have hmarked : dist (mark (φ n)) (q (φ n)) ≤ C + R := by
          rcases hmark (φ n) with hm | hm
          · rw [hm, dist_comm]
            exact (hqbound (φ n)).trans (le_add_of_nonneg_right hR.le)
          · rw [hm]
            calc
              dist (b (φ n)) (q (φ n)) ≤ dist (b (φ n)) (a (φ n)) +
                dist (a (φ n)) (q (φ n)) := dist_triangle _ _ _
              _ ≤ R + C := add_le_add (hpairbound (φ n)) (by simpa only [dist_comm] using hqbound (φ n))
              _ = C + R := add_comm _ _
        rw [Metric.mem_closedBall, hzform n, dist_eq_norm]
        simpa only [sub_sub_cancel_left, norm_neg, dist_eq_norm, norm_sub_rev] using hmarked
      obtain ⟨ψ, S, δ, hψ, hconv, hδ, hboundary, hquake⟩ :=
        anchoredMovingSequence_earthquakeLimit hV anchor hfixed z hz hzinj hbound
      obtain ⟨S', corrected, hconv', htiles', hquake'⟩ :=
        lattice_correction_preserves_directionalEarthquake hT hEopen hEreg (γ ∘ ψ)
          hconv hquake L hL
      exact ⟨S', corrected, δ, hconv', htiles', hδ, hboundary, hquake'⟩


end Tiling.RationalSlopes
