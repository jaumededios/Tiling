import Tiling.RationalSlopes.Basic
import Tiling.Geometry.PackingTopology
import Mathlib.Topology.Algebra.Order.Archimedean
import Tiling.AxisParallel.OneDimensional.FiniteInterval.WholeLine
import Tiling.AxisParallel.OneDimensional.FiniteInterval.PeriodMass

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology

noncomputable section

namespace Tiling.Polygonal

open Tiling.RationalPolygonal (PolygonalRegion)

/-- The centres lie on one affine line in the specified direction. -/
def IsLineSupported (S : Set Plane) (δ : Submodule ℝ Plane) : Prop :=
  ∃ a : Plane, ∀ s ∈ S, s - a ∈ δ

/-- The entire centre fibre through `t`; this definition also makes sense for `t ∉ T`. -/
def lineFibre (δ : Submodule ℝ Plane) (T : Set Plane) (t : Plane) : Set Plane :=
  {s | s ∈ T ∧ s - t ∈ δ}

/-- Membership is constant on directional segments contained in this ball. -/
def LocallySaturatedAlong (D : Set Plane) (δ : Submodule ℝ Plane)
    (x : Plane) (R : ℝ) : Prop :=
  ∀ y ∈ Metric.ball x R, ∀ z ∈ Metric.ball x R,
    z - y ∈ δ → (y ∈ D ↔ z ∈ D)

def ShortEdgeConnected (S : Set Plane) (R : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S,
    Relation.EqvGen (fun a b : Plane => a ∈ S ∧ b ∈ S ∧ dist a b < R) x y

/-- A complete straight boundary component, with proper vertices explicitly excluded. -/
def IsStraightFrontierLine (D : Set Plane) (δ : Submodule ℝ Plane)
    (a : Plane) : Prop :=
  a +ᵥ (δ : Set Plane) ⊆ frontier D ∧
    Disjoint (a +ᵥ (δ : Set Plane)) (properVertices D)

/-- Proper vertices of all whole directional centre fibres. -/
def fibreProperVertices (K : PolygonalRegion) (T : Set Plane)
    (δ : Submodule ℝ Plane) : Set Plane :=
  ⋃ t : T, properVertices (regularSupport K (lineFibre δ T t))

private theorem lineSupported_transverse_coordinate_eq
    {δ : Submodule ℝ Plane} {S : Set Plane} (π : Plane →L[ℝ] ℝ)
    (hker : LinearMap.ker π.toLinearMap = δ) (hline : IsLineSupported S δ)
    {s t : Plane} (hs : s ∈ S) (ht : t ∈ S) : π t = π s := by
  obtain ⟨a, ha⟩ := hline
  have hs0 : π (s - a) = 0 := by
    exact LinearMap.mem_ker.mp (hker.symm ▸ ha s hs)
  have ht0 : π (t - a) = 0 := by
    exact LinearMap.mem_ker.mp (hker.symm ▸ ha t ht)
  rw [map_sub] at hs0 ht0
  linarith

private theorem lineProperVertices_transverse_image_finite
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (π : Plane →L[ℝ] ℝ) (hker : LinearMap.ker π.toLinearMap = δ)
    (hp : IsPacking K.prototileFamily (K.placements S)) (hline : IsLineSupported S δ)
    {s : Plane} (hs : s ∈ S) : (π '' properVertices (regularSupport K S)).Finite := by
  apply (K.isPolygonal.vertexSet_finite.image (fun v => π v + π s)).subset
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨k, hk, t, ht, hvt⟩ := properVertexProvenance hp v hv
  refine ⟨k, hk, ?_⟩
  rw [hvt, map_add, lineSupported_transverse_coordinate_eq π hker hline hs ht]

/-! ## BoundaryGeometry owner -/

theorem straight_frontier_germ_propagates_on_line
    (ψ : Plane →ₗ[ℝ] ℝ)
    (hker : Module.finrank ℝ (LinearMap.ker ψ) = 1)
    (D : Set Plane) (a : Plane)
    (hdisj : Disjoint {x : Plane | ψ x = ψ a} (properVertices D))
    (hseed : ∃ x : Plane, ψ x = ψ a ∧
      ∀ᶠ y in 𝓝 x, (y ∈ frontier D ↔ ψ y = ψ a)) :
    {x : Plane | ψ x = ψ a} ⊆ frontier D := by
  classical
  let C : Set Plane := {x | ψ x = ψ a}
  let A : Set Plane := {x | ∀ᶠ y in 𝓝 x, (y ∈ frontier D ↔ y ∈ C)}
  have hAopen : IsOpen A := isOpen_setOfPred_eventually_nhds
  obtain ⟨x₀, hx₀C, hx₀A⟩ := hseed
  have hx₀A' : x₀ ∈ A := by
    filter_upwards [hx₀A] with y hy
    simpa [C] using hy
  have hCconvex : Convex ℝ C := by
    intro x hx y hy r s hr hs hrs
    change ψ x = ψ a at hx
    change ψ y = ψ a at hy
    change ψ (r • x + s • y) = ψ a
    simp only [map_add, map_smul]
    rw [hx, hy, ← add_smul, hrs, one_smul]
  have hCpre : IsPreconnected C := hCconvex.isPreconnected
  have hker_nebot : LinearMap.ker ψ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hker
    norm_num at hker
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (LinearMap.ker ψ)).mp hker_nebot
  have hvψ : ψ v = 0 := (LinearMap.mem_ker.mp hv)
  have hCnonisolated : ∀ q ∈ C, ∀ ε > 0, ∃ r ∈ C, r ≠ q ∧ dist r q < ε := by
    intro q hq ε hε
    let t : ℝ := ε / (2 * (‖v‖ + 1))
    have ht : 0 < t := div_pos hε (by positivity)
    refine ⟨q + t • v, ?_, ?_, ?_⟩
    · change ψ (q + t • v) = ψ a
      rw [map_add, map_smul, hvψ, smul_eq_mul, mul_zero, add_zero]
      exact hq
    · intro h
      have h' : q + t • v = q + 0 := by simpa using h
      have : t • v = 0 := add_left_cancel h'
      exact hv0 ((smul_eq_zero.mp this).resolve_left (ne_of_gt ht))
    · rw [dist_eq_norm]
      calc
        ‖(q + t • v) - q‖ = ‖t • v‖ := by congr 1 <;> abel
        _ = |t| * ‖v‖ := norm_smul t v
        _ < ε := by
          rw [abs_of_pos ht]
          dsimp [t]
          rw [div_mul_eq_mul_div]
          apply (div_lt_iff₀ (by positivity)).2
          nlinarith [norm_nonneg v]
  have hCAfront : C ∩ A ⊆ closure (frontier D) := by
    rintro q ⟨hqC, hqA⟩
    have hqgerm : ∀ᶠ y in 𝓝 q, (y ∈ frontier D ↔ y ∈ C) := hqA
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hqset : {z | z ∈ frontier D ↔ z ∈ C} ∈ 𝓝 q := hqgerm
    rw [Metric.mem_nhds_iff] at hqset
    obtain ⟨εq, hεq, hqball⟩ := hqset
    let δ := min ε εq
    have hδ : 0 < δ := lt_min hε hεq
    obtain ⟨r, hrC, hrne, hrq⟩ := hCnonisolated q hqC δ hδ
    have hrmem : r ∈ Metric.ball q εq := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hrq (min_le_right _ _)
    have hrfront : r ∈ frontier D := (hqball hrmem).2 hrC
    refine ⟨r, hrfront, ?_⟩
    exact by simpa [dist_comm] using lt_of_lt_of_le hrq (min_le_left _ _)
  have hCAclosed : IsClosed (C ∩ A) := by
    apply isClosed_of_closure_subset
    intro x hx
    have hxfront : x ∈ frontier D := by
      have hclosure : x ∈ closure (closure (frontier D)) := closure_mono hCAfront hx
      have hclosure' : x ∈ closure (frontier D) := by simpa only [closure_closure] using hclosure
      exact (isClosed_frontier : IsClosed (frontier D)).closure_subset hclosure'
    have hxC : x ∈ C := by
      have hxC' : x ∈ closure C := closure_mono Set.inter_subset_left hx
      have hclosed : IsClosed C := by
        change IsClosed (ψ ⁻¹' {ψ a})
        exact isClosed_singleton.preimage ψ.continuous_of_finiteDimensional
      exact hclosed.closure_subset hxC'
    have hxnotproper : ¬ IsProperVertex D x := by
      intro hxv
      have hmem : x ∈ properVertices D := hxv
      exact (Set.disjoint_left.mp hdisj) hxC hmem
    obtain ⟨L, hxL, hLdim, hxgerm⟩ := by
      have hstraight : BoundaryLocallyStraightAt D x := by
        by_contra h
        exact hxnotproper ⟨hxfront, h⟩
      exact hstraight
    have hLlocal : ∃ ε > 0, ∀ z, dist z x < ε →
        (z ∈ frontier D ↔ z ∈ (L : Set Plane)) := by
      have hm : {z | z ∈ frontier D ↔ z ∈ (L : Set Plane)} ∈ 𝓝 x := hxgerm
      rw [Metric.mem_nhds_iff] at hm
      exact hm
    obtain ⟨εL, hεL, hLball⟩ := hLlocal
    have hCAclose := (Metric.mem_closure_iff.mp hx) (εL / 4) (by positivity)
    obtain ⟨q, hqCA, hqx⟩ := hCAclose
    have hqC : q ∈ C := hqCA.1
    have hqA : q ∈ A := hqCA.2
    have hqevent : ∀ᶠ z in 𝓝 q, (z ∈ frontier D ↔ z ∈ C) := hqA
    have hqset : {z | z ∈ frontier D ↔ z ∈ C} ∈ 𝓝 q := hqevent
    rw [Metric.mem_nhds_iff] at hqset
    obtain ⟨εq, hεq, hqball⟩ := hqset
    let ε := min εq (εL / 4)
    have hε : 0 < ε := lt_min hεq (by positivity)
    obtain ⟨r₁, hr₁C, hr₁ne, hr₁q⟩ := hCnonisolated q hqC ε hε
    obtain ⟨r₂, hr₂C, hr₂ne, hr₂q⟩ := hCnonisolated q hqC ε hε
    have hr₁mem : r₁ ∈ Metric.ball q εq := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hr₁q (min_le_left _ _)
    have hr₂mem : r₂ ∈ Metric.ball q εq := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hr₂q (min_le_left _ _)
    have hr₁front : r₁ ∈ frontier D := (hqball hr₁mem).2 hr₁C
    have hr₂front : r₂ ∈ frontier D := (hqball hr₂mem).2 hr₂C
    have hr₁L : r₁ ∈ (L : Set Plane) := (hLball r₁ (by
      have htri : dist r₁ x ≤ dist r₁ q + dist q x := dist_triangle _ _ _
      have hqdist : dist q x < εL / 4 := by simpa [dist_comm] using hqx
      have hrq : dist r₁ q < εL / 4 := lt_of_lt_of_le hr₁q (min_le_right _ _)
      linarith)).mp hr₁front
    have hr₂L : r₂ ∈ (L : Set Plane) := (hLball r₂ (by
      have htri : dist r₂ x ≤ dist r₂ q + dist q x := dist_triangle _ _ _
      have hqdist : dist q x < εL / 4 := by simpa [dist_comm] using hqx
      have hrq : dist r₂ q < εL / 4 := lt_of_lt_of_le hr₂q (min_le_right _ _)
      linarith)).mp hr₂front
    -- Distinctness is obtained by perturbing along the nonzero kernel direction.
    have hchoose : ∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p₁ ∈ (L : Set Plane) ∧
        p₂ ∈ (L : Set Plane) ∧ p₁ ≠ p₂ := by
      by_cases heq : r₁ = r₂
      · let t := ε / (2 * (‖v‖ + 1))
        let p₁ := q + t • v
        let p₂ := q + (2 * t) • v
        have ht : 0 < t := div_pos hε (by positivity)
        have hp₁C : p₁ ∈ C := by
          change ψ (q + t • v) = ψ a
          rw [map_add, map_smul, hvψ, smul_eq_mul, mul_zero, add_zero]
          exact hqC
        have hp₂C : p₂ ∈ C := by
          change ψ (q + (2 * t) • v) = ψ a
          rw [map_add, map_smul, hvψ, smul_eq_mul, mul_zero, add_zero]
          exact hqC
        have hp₁q : dist p₁ q < ε := by
          rw [dist_eq_norm]
          calc
            ‖(q + t • v) - q‖ = |t| * ‖v‖ := by simpa [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
            _ < ε := by
              rw [abs_of_pos ht]
              calc
                t * ‖v‖ < t * (‖v‖ + 1) := mul_lt_mul_of_pos_left (by linarith [norm_nonneg v]) ht
                _ = ε / 2 := by dsimp [t]; field_simp
                _ < ε := by linarith
        have hp₂q : dist p₂ q < ε := by
          rw [dist_eq_norm]
          calc
            ‖(q + (2 * t) • v) - q‖ = |2 * t| * ‖v‖ := by simpa [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
            _ < ε := by
              rw [abs_of_pos (by positivity : 0 < 2 * t)]
              calc
                2 * t * ‖v‖ < 2 * t * (‖v‖ + 1) := mul_lt_mul_of_pos_left (by linarith [norm_nonneg v]) (by positivity)
                _ = ε := by dsimp [t]; field_simp
        have hp₁mem : p₁ ∈ Metric.ball q εq := by
          rw [Metric.mem_ball]
          exact lt_of_lt_of_le hp₁q (min_le_left _ _)
        have hp₂mem : p₂ ∈ Metric.ball q εq := by
          rw [Metric.mem_ball]
          exact lt_of_lt_of_le hp₂q (min_le_left _ _)
        have hp₁front : p₁ ∈ frontier D := (hqball hp₁mem).2 hp₁C
        have hp₂front : p₂ ∈ frontier D := (hqball hp₂mem).2 hp₂C
        have hp₁L : p₁ ∈ (L : Set Plane) := (hLball p₁ (by
          have htri : dist p₁ x ≤ dist p₁ q + dist q x := dist_triangle _ _ _
          have hqdist : dist q x < εL / 4 := by simpa [dist_comm] using hqx
          have hpq : dist p₁ q < εL / 4 := lt_of_lt_of_le hp₁q (min_le_right _ _)
          linarith)).mp hp₁front
        have hp₂L : p₂ ∈ (L : Set Plane) := (hLball p₂ (by
          have htri : dist p₂ x ≤ dist p₂ q + dist q x := dist_triangle _ _ _
          have hqdist : dist q x < εL / 4 := by simpa [dist_comm] using hqx
          have hpq : dist p₂ q < εL / 4 := lt_of_lt_of_le hp₂q (min_le_right _ _)
          linarith)).mp hp₂front
        refine ⟨p₁, p₂, hp₁C, hp₂C, hp₁L, hp₂L, ?_⟩
        intro heq'
        have : t • v = 0 := by
          have hsub := congrArg (fun z : Plane => z - q) heq'
          have hmul : t • v = (2 * t) • v := by simpa [p₁, p₂, two_smul, add_sub_cancel_left] using hsub
          have : t = 2 * t := smul_left_injective ℝ hv0 hmul
          linarith
        exact hv0 ((smul_eq_zero.mp this).resolve_left (ne_of_gt ht))
      · exact ⟨r₁, r₂, hr₁C, hr₂C, hr₁L, hr₂L, heq⟩
    obtain ⟨p₁, p₂, hp₁C, hp₂C, hp₁L, hp₂L, hpne⟩ := hchoose
    have hw : p₂ - p₁ ∈ LinearMap.ker ψ := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr (by simpa [C] using hp₂C.trans hp₁C.symm)
    have hw0 : p₂ - p₁ ≠ 0 := sub_ne_zero.mpr hpne.symm
    have hwd : p₂ - p₁ ∈ L.direction := by
      simpa using (AffineSubspace.vsub_mem_direction hp₂L hp₁L)
    have hkerSpan := eq_span_singleton_of_mem_of_finrank_eq_one hker hw hw0
    have hdirSpan := eq_span_singleton_of_mem_of_finrank_eq_one hLdim hwd hw0
    have hdir : L.direction = LinearMap.ker ψ := hdirSpan.trans hkerSpan.symm
    have hL_eq : L = AffineSubspace.mk' x (LinearMap.ker ψ) := by
      apply AffineSubspace.ext_of_direction_eq
      · simpa [hdir]
      · exact ⟨x, hxL, by simp⟩
    have hL_C : (L : Set Plane) = C := by
      rw [hL_eq]
      ext z
      change (z -ᵥ x ∈ LinearMap.ker ψ) ↔ ψ z = ψ a
      rw [LinearMap.mem_ker, vsub_eq_sub, map_sub]
      have hxC' : ψ x = ψ a := by simpa [C] using hxC
      have hp₁x : ψ p₁ = ψ a := by simpa [C] using hp₁C
      have hp₂x : ψ p₂ = ψ a := by simpa [C] using hp₂C
      rw [hxC']
      constructor <;> intro h <;> linarith
    have hxA : x ∈ A := by
      have := hxgerm
      simpa [A, hL_C] using this
    exact ⟨hxC, hxA⟩
  let B : Set C := {x | (x : Plane) ∈ A}
  have hBopen : IsOpen B := hAopen.preimage continuous_subtype_val
  have hBclosed : IsClosed B := by
    have heq : (Subtype.val : C → Plane) ⁻¹' (C ∩ A) = B := by
      ext z
      constructor
      · intro hz
        exact hz.2
      · intro hz
        exact ⟨z.2, hz⟩
    rw [← heq]
    exact hCAclosed.preimage continuous_subtype_val
  letI : PreconnectedSpace C := (isPreconnected_iff_preconnectedSpace).mp hCpre
  have hBne : B.Nonempty := ⟨⟨x₀, hx₀C⟩, hx₀A'⟩
  have hBuniv : B = Set.univ := IsClopen.eq_univ ⟨hBclosed, hBopen⟩ hBne
  intro x hx
  have hxC : x ∈ C := hx
  have hxA : x ∈ A := by
    have hxB : (⟨x, hxC⟩ : C) ∈ B := by rw [hBuniv]; trivial
    exact hxB
  have hxgerm : ∀ᶠ y in 𝓝 x, (y ∈ frontier D ↔ y ∈ C) := hxA
  have hxfront : x ∈ closure (frontier D) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hset : {z | z ∈ frontier D ↔ z ∈ C} ∈ 𝓝 x := hxgerm
    rw [Metric.mem_nhds_iff] at hset
    obtain ⟨εg, hεg, hg⟩ := hset
    let δ := min ε εg
    have hδ : 0 < δ := lt_min hε hεg
    obtain ⟨y, hyC, hyne, hydist⟩ := hCnonisolated x hxC δ hδ
    have hyballg : y ∈ Metric.ball x εg := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hydist (min_le_right _ _)
    have hyfront : y ∈ frontier D := (hg hyballg).2 hyC
    exact ⟨y, hyfront, by simpa [dist_comm] using lt_of_lt_of_le hydist (min_le_left _ _)⟩
  exact (isClosed_frontier : IsClosed (frontier D)).closure_subset hxfront

private theorem affineSubspace_eq_anchor_vadd_direction
    {L : AffineSubspace ℝ Plane} {a : Plane} (ha : a ∈ L) :
    (L : Set Plane) = a +ᵥ (L.direction : Set Plane) := by
  ext z
  constructor
  · intro hz
    exact Set.mem_vadd_set.mpr ⟨z - a, L.vsub_mem_direction hz ha, by
      simp only [vadd_eq_add]; abel⟩
  · intro hz
    obtain ⟨v, hv, rfl⟩ := Set.mem_vadd_set.mp hz
    rw [vadd_eq_add, add_comm]
    exact L.vadd_mem_of_mem_direction hv ha

private theorem straight_frontier_affine_germ_propagates
    {D : Set Plane} {L : AffineSubspace ℝ Plane} {a : Plane}
    (ha : a ∈ L) (hL : Module.finrank ℝ L.direction = 1)
    (hdisj : Disjoint (L : Set Plane) (properVertices D))
    (hg : ∀ᶠ y in 𝓝 a, y ∈ frontier D ↔ y ∈ (L : Set Plane)) :
    (L : Set Plane) ⊆ frontier D := by
  obtain ⟨ψ, hψ⟩ := Tiling.AffineSubspace.exists_levelSet_coordinate L a ha hL
  have hker : LinearMap.ker ψ.toLinearMap = L.direction := by
    ext v
    constructor
    · intro hv
      have hv0 : ψ v = 0 := LinearMap.mem_ker.mp hv
      have hva : v +ᵥ a ∈ L := (hψ _).mpr (by
        simp only [vadd_eq_add, map_add, hv0, zero_add])
      simpa only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right] using
        L.vsub_mem_direction hva ha
    · intro hv
      have hva := L.vadd_mem_of_mem_direction hv ha
      have heq := (hψ _).mp hva
      apply LinearMap.mem_ker.mpr
      change ψ v = 0
      simp only [vadd_eq_add, map_add] at heq
      linarith
  have hlevel : {y : Plane | ψ y = ψ a} = (L : Set Plane) := by
    ext y
    exact (hψ y).symm
  have hseed : ∃ x : Plane, ψ x = ψ a ∧
      ∀ᶠ y in 𝓝 x, (y ∈ frontier D ↔ ψ y = ψ a) := by
    refine ⟨a, rfl, ?_⟩
    filter_upwards [hg] with y hy
    exact hy.trans (hψ y)
  have hfull := straight_frontier_germ_propagates_on_line ψ.toLinearMap
    (by rw [hker]; exact hL) D a (by
      change Disjoint {y : Plane | ψ y = ψ a} (properVertices D)
      rw [hlevel]
      exact hdisj) hseed
  change {y : Plane | ψ y = ψ a} ⊆ frontier D at hfull
  rwa [hlevel] at hfull

private theorem frontier_ray_segment_of_no_properVertices
    {D : Set Plane} {p v : Plane} (_hv : v ≠ 0) {B : ℝ} (hB : 0 < B)
    (hp : p ∈ frontier D)
    (hg : ∀ᶠ z in 𝓝 p, z ∈ frontier D ↔
      z ∈ p +ᵥ (Submodule.span ℝ ({v} : Set Plane) : Set Plane))
    (hW : ∀ t ∈ Set.Icc (0 : ℝ) B, p + t • v ∉ properVertices D) :
    ∀ t ∈ Set.Icc (0 : ℝ) B, p + t • v ∈ frontier D := by
  let φ : ℝ → Plane := fun t => p + t • v
  have hφ : Continuous φ := by fun_prop
  let F : Set ℝ := (φ ⁻¹' frontier D) ∩ Set.Icc 0 B
  have hFclosed : IsClosed F :=
    (isClosed_frontier.preimage hφ).inter isClosed_Icc
  have hzeroF : (0 : ℝ) ∈ F := by
    exact ⟨by simpa [φ] using hp, ⟨le_rfl, hB.le⟩⟩
  have hparam : {t : ℝ | φ t ∈ frontier D} ∈ 𝓝 0 := by
    have hg' : ∀ᶠ z in 𝓝 (φ 0), z ∈ frontier D ↔
        z ∈ p +ᵥ (Submodule.span ℝ ({v} : Set Plane) : Set Plane) := by
      simpa only [φ, zero_smul, add_zero] using hg
    have hpre := hφ.continuousAt.preimage_mem_nhds hg'
    filter_upwards [hpre] with t ht
    apply ht.mpr
    exact Set.mem_vadd_set.mpr ⟨t • v,
      Submodule.smul_mem _ _ (Submodule.subset_span (by simp)), rfl⟩
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hparam
  obtain ⟨e, he0, heub⟩ := exists_between (lt_min hu hB)
  have heu : e < u := heub.trans_le (min_le_left _ _)
  have heB : e < B := heub.trans_le (min_le_right _ _)
  let J : Set ℝ := connectedComponentIn F 0
  have hzeroJ : (0 : ℝ) ∈ J := mem_connectedComponentIn hzeroF
  have heJ : e ∈ J := by
    refine isPreconnected_Icc.subset_connectedComponentIn
      (left_mem_Icc.mpr he0.le) ?_ (right_mem_Icc.mpr he0.le)
    intro t ht
    exact ⟨hlu ⟨hl.trans_le ht.1, ht.2.trans_lt heu⟩,
      ⟨ht.1, ht.2.trans heB.le⟩⟩
  have hJclosed : IsClosed J := by
    dsimp only [J]
    rw [connectedComponentIn_eq_image hzeroF]
    exact hFclosed.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hJbound : ∀ t ∈ J, t ≤ B := by
    intro t ht
    exact (connectedComponentIn_subset F 0 ht).2.2
  have hJnonempty : J.Nonempty := ⟨0, hzeroJ⟩
  let b := sSup J
  have hbGreatest : IsGreatest J b :=
    hJclosed.isGreatest_csSup hJnonempty ⟨B, hJbound⟩
  have hbJ := hbGreatest.1
  have hbpos : 0 < b := he0.trans_le (hbGreatest.2 heJ)
  have hbB : b ≤ B := hJbound b hbJ
  have hfront {t : ℝ} (ht : t ∈ J) : φ t ∈ frontier D :=
    (connectedComponentIn_subset F 0 ht).1
  have hb_eq : b = B := by
    by_contra hne
    have hb_lt : b < B := lt_of_le_of_ne hbB hne
    have hbnot : φ b ∉ properVertices D := hW b ⟨hbpos.le, hbB⟩
    have hstraight : BoundaryLocallyStraightAt D (φ b) := by
      by_contra h
      exact hbnot ⟨hfront hbJ, h⟩
    obtain ⟨L, hbL, _, hlocal⟩ := hstraight
    have hlineParam : {t : ℝ | φ t ∈ frontier D ↔ φ t ∈ (L : Set Plane)} ∈
        𝓝 b := hφ.continuousAt.preimage_mem_nhds hlocal
    obtain ⟨l', u', ⟨hl'b, hbu'⟩, hlu'⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp hlineParam
    obtain ⟨t₁, ht₁l, ht₁b⟩ := exists_between (max_lt hl'b hbpos)
    have ht₁nonneg : 0 ≤ t₁ := (le_max_right l' 0).trans ht₁l.le
    have ht₁J : t₁ ∈ J :=
      isPreconnected_connectedComponentIn.Icc_subset hzeroJ hbJ ⟨ht₁nonneg, ht₁b.le⟩
    have ht₁L : φ t₁ ∈ L :=
      (hlu' ⟨(le_max_left l' 0).trans_lt ht₁l, ht₁b.trans hbu'⟩).mp (hfront ht₁J)
    obtain ⟨t₂, hbt₂, ht₂ub⟩ := exists_between (lt_min hbu' hb_lt)
    have ht₂u := ht₂ub.trans_le (min_le_left u' B)
    have ht₂B := ht₂ub.trans_le (min_le_right u' B)
    have lineMap_eq (t : ℝ) :
        AffineMap.lineMap (φ b) (φ t₁) ((t - b) / (t₁ - b)) = φ t := by
      simp only [AffineMap.lineMap_apply, φ, vsub_eq_sub, vadd_eq_add]
      rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul,
        div_mul_cancel₀ (t - b) (sub_ne_zero.mpr ht₁b.ne), sub_smul]
      abel
    have hintervalF : Set.Icc b t₂ ⊆ F := by
      intro t ht
      have htL : φ t ∈ L := by
        rw [← lineMap_eq t]
        exact AffineMap.lineMap_mem _ hbL ht₁L
      exact ⟨(hlu' ⟨hl'b.trans_le ht.1, ht.2.trans_lt ht₂u⟩).mpr htL,
        ⟨hbpos.le.trans ht.1, ht.2.trans ht₂B.le⟩⟩
    have ht₂component : t₂ ∈ connectedComponentIn F b :=
      isPreconnected_Icc.subset_connectedComponentIn
        (left_mem_Icc.mpr hbt₂.le) hintervalF (right_mem_Icc.mpr hbt₂.le)
    have hcomponents : J = connectedComponentIn F b := connectedComponentIn_eq hbJ
    have ht₂J : t₂ ∈ J := hcomponents.symm ▸ ht₂component
    exact (not_lt_of_ge (hbGreatest.2 ht₂J)) hbt₂
  intro t ht
  apply hfront
  apply isPreconnected_connectedComponentIn.Icc_subset hzeroJ hbJ
  simpa only [hb_eq] using ht

private theorem affineLine_directions_eq_of_two_shared_points
    {L M : AffineSubspace ℝ Plane} (hL : Module.finrank ℝ L.direction = 1)
    (hM : Module.finrank ℝ M.direction = 1) {x y : Plane}
    (hxL : x ∈ L) (hyL : y ∈ L) (hxM : x ∈ M) (hyM : y ∈ M) (hxy : x ≠ y) :
    L.direction = M.direction := by
  have hv : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hL (L.vsub_mem_direction hyL hxL) hv,
    eq_span_singleton_of_mem_of_finrank_eq_one hM (M.vsub_mem_direction hyM hxM) hv]

private theorem direction_eq_of_complete_frontier_line_and_straightGerm
    {D : Set Plane} {δ : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1)
    {a x : Plane} (hxline : x ∈ a +ᵥ (δ : Set Plane))
    (hfront : a +ᵥ (δ : Set Plane) ⊆ frontier D)
    {L : AffineSubspace ℝ Plane} (hxL : x ∈ L)
    (hL : Module.finrank ℝ L.direction = 1)
    (hg : ∀ᶠ y in 𝓝 x, y ∈ frontier D ↔ y ∈ (L : Set Plane)) :
    δ = L.direction := by
  have hδbot : δ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hδ
    exact Nat.zero_ne_one hδ
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδbot
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hg
  let r : ℝ := ε / (2 * ‖w‖)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hr : 0 < r := div_pos hε (mul_pos zero_lt_two hwpos)
  have hyline : x + r • w ∈ a +ᵥ (δ : Set Plane) := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxline ⊢
    change -a + (x + r • w) ∈ δ
    have := δ.add_mem hxline (δ.smul_mem r hw)
    simpa only [vadd_eq_add, add_assoc] using this
  have hyball : x + r • w ∈ Metric.ball x ε := by
    rw [Metric.mem_ball]
    calc
      dist (x + r • w) x = ‖r • w‖ := by simp only [dist_eq_norm, add_sub_cancel_left]
      _ = r * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ = ε / 2 := by dsimp only [r]; field_simp
      _ < ε := by linarith
  have hyL := (hball (Metric.mem_ball.mp hyball)).mp (hfront hyline)
  have hscaled : r • w ∈ L.direction := by
    simpa only [vsub_eq_sub, add_sub_cancel_left] using L.vsub_mem_direction hyL hxL
  have hwL : w ∈ L.direction := by
    have := L.direction.smul_mem r⁻¹ hscaled
    simpa only [inv_smul_smul₀ hr.ne'] using this
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hδ hw hw0,
    eq_span_singleton_of_mem_of_finrank_eq_one hL hwL hw0]

private theorem segment_sub_mem_direction {a b x y : Plane}
    (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b) :
    y - x ∈ Submodule.span ℝ ({b - a} : Set Plane) := by
  rw [segment_eq_image'] at hx hy
  obtain ⟨r, _, rfl⟩ := hx
  obtain ⟨s, _, rfl⟩ := hy
  have heq : (a + s • (b - a)) - (a + r • (b - a)) = (s - r) • (b - a) := by
    rw [sub_smul]
    abel
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private theorem nonparallel_affine_lines_intersect
    {δ ε : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1)
    (hε : Module.finrank ℝ ε = 1) (hne : δ ≠ ε) (a b : Plane) :
    ∃ x : Plane, x ∈ a +ᵥ (δ : Set Plane) ∧ x ∈ b +ᵥ (ε : Set Plane) := by
  have hinf : δ ⊓ ε = ⊥ := by
    apply eq_bot_iff.mpr
    intro v hv
    change v = 0
    by_contra hv0
    exact hne ((eq_span_singleton_of_mem_of_finrank_eq_one hδ hv.1 hv0).trans
      (eq_span_singleton_of_mem_of_finrank_eq_one hε hv.2 hv0).symm)
  have hdim : Module.finrank ℝ (δ ⊔ ε : Submodule ℝ Plane) = 2 := by
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq δ ε
    rw [hinf, finrank_bot, hδ, hε] at hadd
    omega
  have hsup : δ ⊔ ε = ⊤ := Submodule.eq_top_of_finrank_eq
    (by simpa only [Complex.finrank_real_complex] using hdim)
  have hab : b - a ∈ δ ⊔ ε := by rw [hsup]; trivial
  obtain ⟨d, hd, e, he, hde⟩ := Submodule.mem_sup.mp hab
  refine ⟨a + d, Set.mem_vadd_set.mpr ⟨d, hd, rfl⟩,
    Set.mem_vadd_set.mpr ⟨-e, ε.neg_mem he, ?_⟩⟩
  have hb : b = a + (d + e) := by rw [hde]; abel
  rw [vadd_eq_add, hb]
  abel

private theorem complete_frontier_lines_parallel
    {D : Set Plane} (hlocal : ∀ x ∈ frontier D, BoundaryLocallyStraightAt D x)
    {δ ε : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1)
    (hε : Module.finrank ℝ ε = 1) {a b : Plane}
    (hfrontδ : a +ᵥ (δ : Set Plane) ⊆ frontier D)
    (hfrontε : b +ᵥ (ε : Set Plane) ⊆ frontier D) : δ = ε := by
  by_contra hne
  obtain ⟨x, hxδ, hxε⟩ := nonparallel_affine_lines_intersect hδ hε hne a b
  obtain ⟨L, hxL, hL, hg⟩ := hlocal x (hfrontδ hxδ)
  exact hne ((direction_eq_of_complete_frontier_line_and_straightGerm hδ hxδ hfrontδ hxL hL hg).trans
    (direction_eq_of_complete_frontier_line_and_straightGerm hε hxε hfrontε hxL hL hg).symm)

private theorem segment_direction_eq_of_shared_points {a b c d x y : Plane}
    (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hx' : x ∈ segment ℝ c d) (hy' : y ∈ segment ℝ c d) (hxy : x ≠ y) :
    Submodule.span ℝ ({b - a} : Set Plane) =
      Submodule.span ℝ ({d - c} : Set Plane) := by
  have hab : b - a ≠ 0 := by
    intro h
    have : a = b := (sub_eq_zero.mp h).symm
    subst b
    have hxa : x = a := by simpa using hx
    have hya : y = a := by simpa using hy
    exact hxy (hxa.trans hya.symm)
  have hcd : d - c ≠ 0 := by
    intro h
    have : c = d := (sub_eq_zero.mp h).symm
    subst d
    have hxc : x = c := by simpa using hx'
    have hyc : y = c := by simpa using hy'
    exact hxy (hxc.trans hyc.symm)
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  rw [eq_span_singleton_of_mem_of_finrank_eq_one
    (finrank_span_singleton hab) (segment_sub_mem_direction hx hy) hyx,
    eq_span_singleton_of_mem_of_finrank_eq_one
    (finrank_span_singleton hcd) (segment_sub_mem_direction hx' hy') hyx]

private theorem segment_direction_mem_finite_cover {a b : Plane} (hab : a ≠ b)
    (F : Finset (Plane × Plane))
    (hcover : segment ℝ a b ⊆ ⋃ e ∈ F, segment ℝ e.1 e.2) :
    ∃ e ∈ F, Submodule.span ℝ ({b - a} : Set Plane) =
      Submodule.span ℝ ({e.2 - e.1} : Set Plane) := by
  classical
  have hinf : (segment ℝ a b).Infinite := by
    rw [segment_eq_image']
    apply (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num)).image
    intro r _ s _ heq
    exact smul_left_injective ℝ (sub_ne_zero.mpr (Ne.symm hab))
      (add_left_cancel heq)
  by_contra h
  have hfinite : (⋃ e ∈ F, segment ℝ a b ∩ segment ℝ e.1 e.2).Finite := by
    apply F.finite_toSet.biUnion
    intro e he
    apply Set.Subsingleton.finite
    intro x hx y hy
    by_contra hxy
    exact h ⟨e, he, segment_direction_eq_of_shared_points hx.1 hy.1 hx.2 hy.2 hxy⟩
  apply hinf
  apply hfinite.subset
  intro x hx
  obtain ⟨e, he, hx'⟩ := Set.mem_iUnion₂.mp (hcover hx)
  exact Set.mem_iUnion₂.mpr ⟨e, he, hx, hx'⟩

theorem boundaryDirections_finite (K : PolygonalRegion) :
    {δ : Submodule ℝ Plane | HasBoundaryDirection K δ}.Finite := by
  classical
  obtain ⟨F, _, hfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  apply (F.finite_toSet.image (fun e : Plane × Plane =>
    Submodule.span ℝ ({e.2 - e.1} : Set Plane))).subset
  rintro δ ⟨a, b, hab, hseg, rfl⟩
  obtain ⟨e, he, heq⟩ := segment_direction_mem_finite_cover hab F (by
    simpa only [hfront] using hseg)
  exact ⟨e, he, heq.symm⟩

theorem hasRationalDirection_of_hasBoundaryDirection
    {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    (hK : Tiling.RationalSlopes.HasRationalSlopes K)
    (hboundary : HasBoundaryDirection K δ) :
    Tiling.RationalSlopes.HasRationalDirection δ := by
  obtain ⟨F, hrat, hfront⟩ := hK
  obtain ⟨a, b, hab, hseg, rfl⟩ := hboundary
  obtain ⟨e, he, heq⟩ := segment_direction_mem_finite_cover hab F (by
    simpa only [hfront] using hseg)
  rw [heq]
  exact (hrat e he).2

/-- Every actual complete frontier line uses a genuine tile boundary direction.
The proof needs only a compact line segment and finitely many local tile edges. -/
theorem straightFrontierLine_isBoundaryDirection
    {K : PolygonalRegion} {S : Set Plane} {δ : Submodule ℝ Plane} {a : Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : IsStraightFrontierLine (regularSupport K S) δ a) :
    HasBoundaryDirection K δ := by
  classical
  have hδbot : δ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hδ
    exact Nat.zero_ne_one hδ
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδbot
  let Q := segment ℝ a (a + w)
  have hQline : Q ⊆ a +ᵥ (δ : Set Plane) := by
    intro x hx
    change x ∈ segment ℝ a (a + w) at hx
    rw [segment_eq_image'] at hx
    obtain ⟨r, _, rfl⟩ := hx
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa using δ.smul_mem r hw
  have hQfront : Q ⊆ frontier (regularSupport K S) := hQline.trans hline.1
  let A : PolygonalProtoTiling Unit :=
    ⟨K.prototileFamily, K.placements S, fun _ => K.isPolygonal⟩
  let H := {i : A.placements | (placedTile A.prototiles i.1 ∩ Q).Nonempty}
  have hQcompact : IsCompact Q := by
    change IsCompact (segment ℝ a (a + w))
    rw [segment_eq_image']
    exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  have hH : H.Finite :=
    (A.locallyFinite_placedTile hp).finite_nonempty_inter_compact hQcompact
  obtain ⟨F, hFedges, hfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  let G : Finset (Plane × Plane) := (hH.toFinset ×ˢ F).image
    (fun p => (p.1.1.1 + p.2.1, p.1.1.1 + p.2.2))
  have hopen : IsOpen (openUnion K S) :=
    isOpen_iUnion (fun s : S => isOpen_interior.vadd (s : Plane))
  have hunion : openUnion K S ⊆ regularSupport K S :=
    hopen.subset_interior_iff.mpr subset_closure
  have hcover : Q ⊆ ⋃ e ∈ G, segment ℝ e.1 e.2 := by
    intro x hx
    have hxc : x ∈ closure (openUnion K S) :=
      (closure_minimal interior_subset isClosed_closure) (frontier_subset_closure (hQfront hx))
    rw [closure_openUnion_eq_iUnion_support hp] at hxc
    obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hxc
    have hxnotint : x ∉ interior ((s : Plane) +ᵥ K.support) := by
      intro hxi
      have hxunion : x ∈ openUnion K S := by
        apply Set.mem_iUnion.mpr ⟨s, ?_⟩
        simpa only [interior_vadd, RationalPolygonal.PolygonalRegion.openCarrier] using hxi
      exact (hQfront hx).2 ((regularSupport_isRegularOpen K S).1.interior_eq.symm ▸
        hunion hxunion)
    have hxfront : x ∈ frontier ((s : Plane) +ᵥ K.support) := by
      rw [(K.isPolygonal.vadd (s : Plane)).isClosed.frontier_eq]
      exact ⟨hxs, hxnotint⟩
    have hvfront : frontier ((s : Plane) +ᵥ K.support) = (s : Plane) +ᵥ frontier K.support := by
      simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
        ((Homeomorph.addLeft (s : Plane)).image_frontier K.support).symm
    rw [hvfront, Set.mem_vadd_set_iff_neg_vadd_mem, hfront] at hxfront
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hxfront
    let i : A.placements := ⟨((s : Plane), ()), s.2⟩
    have hi : i ∈ hH.toFinset := hH.mem_toFinset.mpr ⟨x, hxs, hx⟩
    refine Set.mem_iUnion₂.mpr ⟨((s : Plane) + e.1, (s : Plane) + e.2), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(i, e), Finset.mem_product.mpr ⟨hi, he⟩, rfl⟩
    · change x ∈ segment ℝ ((s : Plane) +ᵥ e.1) ((s : Plane) +ᵥ e.2)
      rw [← vadd_segment, Set.mem_vadd_set_iff_neg_vadd_mem]
      exact hxe
  obtain ⟨e, he, heq⟩ := segment_direction_mem_finite_cover
    (by simpa using hw0) G hcover
  obtain ⟨⟨i, f⟩, hif, rfl⟩ := Finset.mem_image.mp he
  have hf := (Finset.mem_product.mp hif).2
  have hdeq : δ = Submodule.span ℝ ({f.2 - f.1} : Set Plane) := by
    have hδspan := eq_span_singleton_of_mem_of_finrank_eq_one hδ hw hw0
    simpa only [add_sub_add_left_eq_sub, add_sub_cancel_left, hδspan] using heq
  exact ⟨f.1, f.2, (hFedges f hf).1, (hFedges f hf).2.2.2, hdeq⟩

theorem lineFibre_isLineSupported (δ : Submodule ℝ Plane) (T : Set Plane)
    (t : Plane) : IsLineSupported (lineFibre δ T t) δ :=
  ⟨t, fun _ hs => hs.2⟩

/-- A positive outer margin makes directional saturation survive regularization. -/
theorem locallySaturatedAlong_interiorClosure
    {D : Set Plane} {δ : Submodule ℝ Plane} {x : Plane} {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε)
    (hsat : LocallySaturatedAlong D δ x (R + ε)) :
    LocallySaturatedAlong (interior (closure D)) δ x R := by
  have _hRpos : 0 < R := hR
  intro y hy z hz hzy
  have hy' : dist y x < R := by simpa [Metric.mem_ball, dist_comm] using hy
  have hz' : dist z x < R := by simpa [Metric.mem_ball, dist_comm] using hz
  have htrans : ∀ a, dist a y < ε / 2 →
      (a ∈ D ↔ a + (z - y) ∈ D) := by
    intro a ha
    apply hsat a ?_ (a + (z - y)) ?_ ?_
    · change dist a x < R + ε
      calc
        dist a x ≤ dist a y + dist y x := dist_triangle a y x
        _ < ε / 2 + R := add_lt_add ha hy'
        _ < R + ε := by linarith
    · change dist (a + (z - y)) x < R + ε
      have hdist : dist (a + (z - y)) z = dist a y := by
        calc
          dist (a + (z - y)) z = dist (a + (z - y)) (y + (z - y)) := by
            congr 1
            abel
          _ = dist a y := dist_add_right a y (z - y)
      calc
        dist (a + (z - y)) x ≤ dist (a + (z - y)) z + dist z x :=
          dist_triangle _ _ _
        _ = dist a y + dist z x := by rw [hdist]
        _ < ε / 2 + R := add_lt_add ha hz'
        _ < R + ε := by linarith
    · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hzy
  have htransBack : ∀ a, dist a z < ε / 2 →
      (a ∈ D ↔ a - (z - y) ∈ D) := by
    intro a ha
    apply hsat a ?_ (a - (z - y)) ?_ ?_
    · change dist a x < R + ε
      calc
        dist a x ≤ dist a z + dist z x := dist_triangle a z x
        _ < ε / 2 + R := add_lt_add ha hz'
        _ < R + ε := by linarith
    · change dist (a - (z - y)) x < R + ε
      have hdist : dist (a - (z - y)) y = dist a z := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      calc
        dist (a - (z - y)) x ≤ dist (a - (z - y)) y + dist y x :=
          dist_triangle _ _ _
        _ = dist a z + dist y x := by rw [hdist]
        _ < ε / 2 + R := add_lt_add ha hy'
        _ < R + ε := by linarith
    · have hneg : -(z - y) ∈ δ := δ.neg_mem hzy
      simpa [sub_eq_add_neg] using hneg
  have closureForward : ∀ p, dist p y < ε / 4 → p ∈ closure D →
      p + (z - y) ∈ closure D := by
    intro p hp hpD
    rw [Metric.mem_closure_iff] at hpD ⊢
    intro r hr
    obtain ⟨a, haD, had⟩ := hpD (min r (ε / 4)) (lt_min hr (by linarith))
    have hap : dist a p < ε / 4 := by
      exact lt_of_lt_of_le (by simpa [dist_comm] using had) (min_le_right _ _)
    have haSmall : dist a y < ε / 2 := by
      calc
        dist a y ≤ dist a p + dist p y := dist_triangle a p y
        _ < ε / 4 + ε / 4 := add_lt_add hap hp
        _ = ε / 2 := by ring
    have haShift : a + (z - y) ∈ D := (htrans a haSmall).mp haD
    refine ⟨a + (z - y), haShift, ?_⟩
    have hdist : dist (p + (z - y)) (a + (z - y)) = dist p a := by
      simp [dist_add_right]
    rw [hdist]
    exact lt_of_lt_of_le (by simpa [dist_comm] using had) (min_le_left _ _)
  have closureBackward : ∀ p, dist p z < ε / 4 → p ∈ closure D →
      p - (z - y) ∈ closure D := by
    intro p hp hpD
    rw [Metric.mem_closure_iff] at hpD ⊢
    intro r hr
    obtain ⟨a, haD, had⟩ := hpD (min r (ε / 4)) (lt_min hr (by linarith))
    have hap : dist a p < ε / 4 := by
      exact lt_of_lt_of_le (by simpa [dist_comm] using had) (min_le_right _ _)
    have haSmall : dist a z < ε / 2 := by
      calc
        dist a z ≤ dist a p + dist p z := dist_triangle a p z
        _ < ε / 4 + ε / 4 := add_lt_add hap hp
        _ = ε / 2 := by ring
    have haShift : a - (z - y) ∈ D := (htransBack a haSmall).mp haD
    refine ⟨a - (z - y), haShift, ?_⟩
    have hdist : dist (p - (z - y)) (a - (z - y)) = dist p a := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    rw [hdist]
    exact lt_of_lt_of_le (by simpa [dist_comm] using had) (min_le_left _ _)
  constructor
  · intro hyInterior
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hyInterior
    let r := min ρ (ε / 8)
    have hr : 0 < r := lt_min hρ (by linarith)
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Metric.ball_mem_nhds z hr)
    intro q hq
    have hqdist : dist q z < r := by simpa [Metric.mem_ball] using hq
    have hpdist : dist (q - (z - y)) y < r := by
      have hdist : dist (q - (z - y)) y = dist q z := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      rw [hdist]
      exact hqdist
    have hpball : q - (z - y) ∈ Metric.ball y ρ := by
      apply Metric.mem_ball.mpr
      exact lt_of_lt_of_le hpdist (min_le_left _ _)
    have hpclose : q - (z - y) ∈ closure D := interior_subset (hball hpball)
    have hpSmall : dist (q - (z - y)) y < ε / 4 := by
      exact lt_of_lt_of_le hpdist (by linarith [min_le_right ρ (ε / 8)])
    simpa [sub_eq_add_neg, add_assoc] using closureForward _ hpSmall hpclose
  · intro hzInterior
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzInterior
    let r := min ρ (ε / 8)
    have hr : 0 < r := lt_min hρ (by linarith)
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Metric.ball_mem_nhds y hr)
    intro q hq
    have hqdist : dist q y < r := by simpa [Metric.mem_ball] using hq
    have hpdist : dist (q + (z - y)) z < r := by
      have hdist : dist (q + (z - y)) z = dist q y := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      rw [hdist]
      exact hqdist
    have hpball : q + (z - y) ∈ Metric.ball z ρ := by
      apply Metric.mem_ball.mpr
      exact lt_of_lt_of_le hpdist (min_le_left _ _)
    have hpclose : q + (z - y) ∈ closure D := interior_subset (hball hpball)
    have hpSmall : dist (q + (z - y)) z < ε / 4 := by
      exact lt_of_lt_of_le hpdist (by linarith [min_le_right ρ (ε / 8)])
    simpa [sub_eq_add_neg, add_assoc] using closureBackward _ hpSmall hpclose

/-- Quantitative version used before selecting a rational approximation. Each maximal
nonparallel edge run uses at most one translate of each base segment. -/
private theorem frontier_segment_finite_translated_edge_cover
    {K : PolygonalRegion} {S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements S))
    (F : Finset (Plane × Plane))
    (hfront : frontier K.support = ⋃ e ∈ F, segment ℝ e.1 e.2)
    {a b : Plane} (hQfront : segment ℝ a b ⊆ frontier (regularSupport K S)) :
    ∃ G : Finset (Plane × (Plane × Plane)),
      (∀ g ∈ G, g.1 ∈ S ∧ g.2 ∈ F) ∧
        segment ℝ a b ⊆ ⋃ g ∈ G, segment ℝ (g.1 + g.2.1) (g.1 + g.2.2) := by
  classical
  let Q := segment ℝ a b
  let A : PolygonalProtoTiling Unit :=
    ⟨K.prototileFamily, K.placements S, fun _ => K.isPolygonal⟩
  let H := {i : A.placements | (placedTile A.prototiles i.1 ∩ Q).Nonempty}
  have hQcompact : IsCompact Q := by
    change IsCompact (segment ℝ a b)
    rw [segment_eq_image']
    exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  have hH : H.Finite :=
    (A.locallyFinite_placedTile hp).finite_nonempty_inter_compact hQcompact
  let G : Finset (Plane × (Plane × Plane)) := (hH.toFinset ×ˢ F).image
    (fun p => (p.1.1.1, p.2))
  have hopen : IsOpen (openUnion K S) :=
    isOpen_iUnion (fun s : S => isOpen_interior.vadd (s : Plane))
  have hunion : openUnion K S ⊆ regularSupport K S :=
    hopen.subset_interior_iff.mpr subset_closure
  refine ⟨G, ?_, ?_⟩
  · intro g hg
    obtain ⟨⟨i, e⟩, hie, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨i.2, (Finset.mem_product.mp hie).2⟩
  · intro x hx
    have hxc : x ∈ closure (openUnion K S) :=
      (closure_minimal interior_subset isClosed_closure) (frontier_subset_closure (hQfront hx))
    rw [closure_openUnion_eq_iUnion_support hp] at hxc
    obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hxc
    have hxnotint : x ∉ interior ((s : Plane) +ᵥ K.support) := by
      intro hxi
      have hxunion : x ∈ openUnion K S := by
        apply Set.mem_iUnion.mpr ⟨s, ?_⟩
        simpa only [interior_vadd, RationalPolygonal.PolygonalRegion.openCarrier] using hxi
      exact (hQfront hx).2 ((regularSupport_isRegularOpen K S).1.interior_eq.symm ▸
        hunion hxunion)
    have hxfront : x ∈ frontier ((s : Plane) +ᵥ K.support) := by
      rw [(K.isPolygonal.vadd (s : Plane)).isClosed.frontier_eq]
      exact ⟨hxs, hxnotint⟩
    have hvfront : frontier ((s : Plane) +ᵥ K.support) = (s : Plane) +ᵥ frontier K.support := by
      simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
        ((Homeomorph.addLeft (s : Plane)).image_frontier K.support).symm
    rw [hvfront, Set.mem_vadd_set_iff_neg_vadd_mem, hfront] at hxfront
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hxfront
    let i : A.placements := ⟨((s : Plane), ()), s.2⟩
    have hi : i ∈ hH.toFinset := hH.mem_toFinset.mpr ⟨x, hxs, hx⟩
    refine Set.mem_iUnion₂.mpr ⟨((s : Plane), e), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(i, e), Finset.mem_product.mpr ⟨hi, he⟩, rfl⟩
    · change x ∈ segment ℝ ((s : Plane) +ᵥ e.1) ((s : Plane) +ᵥ e.2)
      rw [← vadd_segment, Set.mem_vadd_set_iff_neg_vadd_mem]
      exact hxe

private theorem unit_tangent_coordinate_exists {v : Plane} (hv : ‖v‖ = 1) :
    ∃ τ : Plane →L[ℝ] ℝ, ‖τ‖ ≤ 1 ∧ τ v = 1 := by
  refine ⟨innerSL ℝ v, ?_, ?_⟩
  · rw [innerSL_apply_norm, hv]
  · rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hv]
    norm_num

theorem frontier_segment_isBoundaryDirection
    {K : PolygonalRegion} {S : Set Plane} {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (hp : IsPacking K.prototileFamily (K.placements S))
    {a b : Plane} (hab : a ≠ b) (hba : b - a ∈ δ)
    (hQfront : segment ℝ a b ⊆ frontier (regularSupport K S)) :
    HasBoundaryDirection K δ := by
  classical
  obtain ⟨F, hF, hfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  obtain ⟨G, hG, hcover⟩ := frontier_segment_finite_translated_edge_cover hp F hfront hQfront
  let E := G.image (fun g => (g.1 + g.2.1, g.1 + g.2.2))
  have hcover' : segment ℝ a b ⊆ ⋃ e ∈ E, segment ℝ e.1 e.2 := by
    intro x hx
    obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact Set.mem_iUnion₂.mpr ⟨_, Finset.mem_image.mpr ⟨g, hg, rfl⟩, hxg⟩
  obtain ⟨e, he, heq⟩ := segment_direction_mem_finite_cover hab E hcover'
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp he
  have hδspan := eq_span_singleton_of_mem_of_finrank_eq_one hδ hba
    (sub_ne_zero.mpr hab.symm)
  have hdir : δ = Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) := by
    simpa only [add_sub_add_left_eq_sub, ← hδspan] using heq
  exact ⟨g.2.1, g.2.2, (hF _ (hG _ hg).2).1, (hF _ (hG _ hg).2).2.2.2, hdir⟩

private theorem eventuallyEq_mem_frontier_iff {D E : Set Plane} {p : Plane}
    (h : D =ᶠ[𝓝 p] E) : p ∈ frontier D ↔ p ∈ frontier E := by
  simp only [frontier_eq_closure_inter_closure, closure_eq_compl_interior_compl,
    Set.mem_inter_iff, Set.mem_compl_iff, compl_compl]
  exact and_congr (not_congr h.compl.mem_interior_iff) (not_congr h.mem_interior_iff)

private theorem frontier_translate_of_locallySaturatedAlong
    {D : Set Plane} {δ : Submodule ℝ Plane} {x p q : Plane} {R : ℝ}
    (hsat : LocallySaturatedAlong D δ x R)
    (hp : p ∈ Metric.ball x R) (hq : q ∈ Metric.ball x R)
    (hpq : q - p ∈ δ) (hpfront : p ∈ frontier D) : q ∈ frontier D := by
  let u := q - p
  let ρ := min (R - dist p x) (R - dist q x) / 2
  have hpdist := Metric.mem_ball.mp hp
  have hqdist := Metric.mem_ball.mp hq
  have hρ : 0 < ρ := div_pos (lt_min (by linarith) (by linarith)) zero_lt_two
  have hyshift (y : Plane) : dist (y + u) q = dist y p := by
    have heq : q = p + u := by dsimp only [u]; abel
    rw [heq, dist_add_right]
  have hlocal : D =ᶠ[𝓝 p] (-u +ᵥ D) := by
    filter_upwards [Metric.isOpen_ball.eventually_mem (Metric.mem_ball_self hρ)] with y hy
    have hyD : y ∈ Metric.ball x R := by
      rw [Metric.mem_ball]
      have htri := dist_triangle y p x
      have hydist := Metric.mem_ball.mp hy
      have hbound : ρ ≤ (R - dist p x) / 2 := by
        dsimp only [ρ]
        exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      linarith
    have hyuD : y + u ∈ Metric.ball x R := by
      rw [Metric.mem_ball]
      have htri := dist_triangle (y + u) q x
      rw [hyshift] at htri
      have hydist := Metric.mem_ball.mp hy
      have hbound : ρ ≤ (R - dist q x) / 2 := by
        dsimp only [ρ]
        exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith
    apply propext
    change y ∈ D ↔ y ∈ -u +ᵥ D
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [neg_neg, vadd_eq_add, add_comm] using hsat y hyD (y + u) hyuD
      (by simpa only [add_sub_cancel_left, u] using hpq)
  have hptrans := (eventuallyEq_mem_frontier_iff hlocal).mp hpfront
  have hfront : frontier (-u +ᵥ D) = -u +ᵥ frontier D := by
    simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
      ((Homeomorph.addLeft (-u)).image_frontier D).symm
  rw [hfront, Set.mem_vadd_set_iff_neg_vadd_mem] at hptrans
  have heq : -(-u) +ᵥ p = q := by dsimp only [u]; simp only [neg_neg, vadd_eq_add]; abel
  rwa [heq] at hptrans

private theorem edgeTranslate_eq_of_endpoint_mem_transverseLine
    {S : Set Plane} {δ ε : Submodule ℝ Plane} {ℓ p : Plane}
    (hδ : Module.finrank ℝ δ = 1) (hε : Module.finrank ℝ ε = 1)
    (hne : δ ≠ ε) (hS : IsLineSupported S δ)
    {s t : Plane} (hs : s ∈ S) (ht : t ∈ S)
    (hsp : p + s ∈ ℓ +ᵥ (ε : Set Plane))
    (htp : p + t ∈ ℓ +ᵥ (ε : Set Plane)) : s = t := by
  obtain ⟨c, hc⟩ := hS
  have hsδ : s - c ∈ δ := hc s hs
  have htδ : t - c ∈ δ := hc t ht
  have hstδ : s - t ∈ δ := by
    have := δ.sub_mem hsδ htδ
    convert this using 1 <;> abel
  have hspε : p + s - ℓ ∈ ε := by
    change p + s - ℓ ∈ (ε : Set Plane)
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hsp
  have htpε : p + t - ℓ ∈ ε := by
    change p + t - ℓ ∈ (ε : Set Plane)
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using htp
  have hstε : s - t ∈ ε := by
    have := ε.sub_mem hspε htpε
    convert this using 1 <;> abel
  by_contra hst
  have hne0 : s - t ≠ 0 := sub_ne_zero.mpr hst
  have hδspan := eq_span_singleton_of_mem_of_finrank_eq_one hδ hstδ hne0
  have hεspan := eq_span_singleton_of_mem_of_finrank_eq_one hε hstε hne0
  exact hne (hδspan.trans hεspan.symm)

/-- The length of a closed interval covered by finitely many closed intervals is at
most the sum of the covering interval lengths. This is the exact finite budget used
after transverse-line uniqueness has reduced each prototype edge to one translate. -/
private theorem finite_interval_cover_length_le
    {F : Finset (ℝ × ℝ)} {a b : ℝ} (hab : a ≤ b)
    (hordered : ∀ p ∈ F, p.1 ≤ p.2)
    (hcover : Set.Icc a b ⊆ ⋃ p ∈ F, Set.Icc p.1 p.2) :
    b - a ≤ ∑ p ∈ F, (p.2 - p.1) := by
  classical
  have hsub : volume (Set.Icc a b) ≤
      volume (⋃ p ∈ F, Set.Icc p.1 p.2) :=
    measure_mono hcover
  have hsum : volume (⋃ p ∈ F, Set.Icc p.1 p.2) ≤
      ∑ p ∈ F, volume (Set.Icc p.1 p.2) := by
    simpa only [Finset.set_biUnion_coe] using
      (measure_biUnion_finset_le F (fun p : ℝ × ℝ => Set.Icc p.1 p.2))
  have hleft : volume (Set.Icc a b) = ENNReal.ofReal (b - a) := by
    rw [Real.volume_Icc]
  have hright : (∑ p ∈ F, volume (Set.Icc p.1 p.2)) =
      ENNReal.ofReal (∑ p ∈ F, (p.2 - p.1)) := by
    calc
      (∑ p ∈ F, volume (Set.Icc p.1 p.2)) =
          ∑ p ∈ F, ENNReal.ofReal (p.2 - p.1) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Real.volume_Icc]
      _ = ENNReal.ofReal (∑ p ∈ F, (p.2 - p.1)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        intro p hp
        exact sub_nonneg.mpr (hordered p hp)
  have hineq := hsub.trans hsum
  rw [hleft, hright] at hineq
  have hbudget : 0 ≤ ∑ p ∈ F, (p.2 - p.1) :=
    Finset.sum_nonneg (fun p hp => sub_nonneg.mpr (hordered p hp))
  exact (ENNReal.ofReal_le_ofReal_iff hbudget).mp hineq

/-- Finite exceptional points do not change the finite interval-cover budget. -/
private theorem finite_interval_cover_length_le_exceptFinite
    {F : Finset (ℝ × ℝ)} {P : Finset ℝ} {a b : ℝ} (hab : a ≤ b)
    (hordered : ∀ p ∈ F, p.1 ≤ p.2)
    (hcover : Set.Icc a b ⊆ (⋃ p ∈ F, Set.Icc p.1 p.2) ∪ (P : Set ℝ)) :
    b - a ≤ ∑ p ∈ F, (p.2 - p.1) := by
  classical
  have hPzero : volume (P : Set ℝ) = 0 := P.finite_toSet.measure_zero volume
  have hsub : volume (Set.Icc a b) ≤
      volume ((⋃ p ∈ F, Set.Icc p.1 p.2) ∪ (P : Set ℝ)) :=
    measure_mono hcover
  have hunion : volume ((⋃ p ∈ F, Set.Icc p.1 p.2) ∪ (P : Set ℝ)) ≤
      volume (⋃ p ∈ F, Set.Icc p.1 p.2) := by
    calc
      volume ((⋃ p ∈ F, Set.Icc p.1 p.2) ∪ (P : Set ℝ)) ≤
          volume (⋃ p ∈ F, Set.Icc p.1 p.2) + volume (P : Set ℝ) :=
        measure_union_le _ _
      _ = volume (⋃ p ∈ F, Set.Icc p.1 p.2) := by rw [hPzero, add_zero]
  have hbase : volume (Set.Icc a b) ≤ volume (⋃ p ∈ F, Set.Icc p.1 p.2) :=
    hsub.trans hunion
  have hsum : volume (⋃ p ∈ F, Set.Icc p.1 p.2) ≤
      ∑ p ∈ F, volume (Set.Icc p.1 p.2) := by
    simpa only [Finset.set_biUnion_coe] using
      (measure_biUnion_finset_le F (fun p : ℝ × ℝ => Set.Icc p.1 p.2))
  have hleft : volume (Set.Icc a b) = ENNReal.ofReal (b - a) := by
    rw [Real.volume_Icc]
  have hright : (∑ p ∈ F, volume (Set.Icc p.1 p.2)) =
      ENNReal.ofReal (∑ p ∈ F, (p.2 - p.1)) := by
    calc
      (∑ p ∈ F, volume (Set.Icc p.1 p.2)) =
          ∑ p ∈ F, ENNReal.ofReal (p.2 - p.1) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Real.volume_Icc]
      _ = ENNReal.ofReal (∑ p ∈ F, (p.2 - p.1)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        intro p hp
        exact sub_nonneg.mpr (hordered p hp)
  have hineq := hbase.trans hsum
  rw [hleft, hright] at hineq
  have hbudget : 0 ≤ ∑ p ∈ F, (p.2 - p.1) :=
    Finset.sum_nonneg (fun p hp => sub_nonneg.mpr (hordered p hp))
  exact (ENNReal.ofReal_le_ofReal_iff hbudget).mp hineq

/-- A nonparallel segment meets an affine line in at most one point. -/
private theorem segment_affineLine_intersection_subsingleton
    {a b ℓ : Plane} {ε : Submodule ℝ Plane}
    (hε : Module.finrank ℝ ε = 1)
    (hne : Submodule.span ℝ ({b - a} : Set Plane) ≠ ε) :
    Set.Subsingleton (segment ℝ a b ∩ (ℓ +ᵥ (ε : Set Plane))) := by
  intro x hx y hy
  by_contra hxy
  have hab : a ≠ b := by
    intro hab
    subst b
    have hxa : x = a := by simpa using hx.1
    have hya : y = a := by simpa using hy.1
    exact hxy (hxa.trans hya.symm)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hxy0 : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hseg : y - x ∈ Submodule.span ℝ ({b - a} : Set Plane) :=
    segment_sub_mem_direction hx.1 hy.1
  have hxε : x - ℓ ∈ ε := by
    change x - ℓ ∈ (ε : Set Plane)
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hx.2
  have hyε : y - ℓ ∈ ε := by
    change y - ℓ ∈ (ε : Set Plane)
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hy.2
  have hline : y - x ∈ ε := by
    have := ε.sub_mem hyε hxε
    convert this using 1 <;> abel
  have hdim : Module.finrank ℝ (Submodule.span ℝ ({b - a} : Set Plane)) = 1 :=
    finrank_span_singleton hba
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim hseg hxy0
  have hlineSpan := eq_span_singleton_of_mem_of_finrank_eq_one hε hline hxy0
  exact hne (hspan.trans hlineSpan.symm)

/-- On a compact run, after local finiteness has reduced the translated edge family to
a finite list, all non-ε-directed edges contribute only finitely many exceptional
intersection points on the fixed ε-line. -/
private theorem finite_nonparallel_translate_intersections
    {ε : Submodule ℝ Plane} {ℓ : Plane}
    (hε : Module.finrank ℝ ε = 1)
    (G : Finset (Plane × (Plane × Plane)))
    (htransverse : ∀ g ∈ G,
      Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) ≠ ε) :
    ({x | ∃ g ∈ G,
      x ∈ segment ℝ (g.1 + g.2.1) (g.1 + g.2.2) ∧
        x ∈ ℓ +ᵥ (ε : Set Plane)} : Set Plane).Finite := by
  classical
  let inter (g : Plane × (Plane × Plane)) : Set Plane :=
    segment ℝ (g.1 + g.2.1) (g.1 + g.2.2) ∩ (ℓ +ᵥ (ε : Set Plane))
  have hinter (g : Plane × (Plane × Plane)) (hg : g ∈ G) : (inter g).Finite := by
    apply Set.Subsingleton.finite
    apply segment_affineLine_intersection_subsingleton hε
    simpa [inter, sub_add_cancel] using htransverse g hg
  have hfinite : (⋃ g ∈ (G : Set (Plane × (Plane × Plane))), inter g).Finite :=
    G.finite_toSet.biUnion (fun g hg => hinter g hg)
  apply hfinite.subset
  intro x hx
  rcases hx with ⟨g, hg, hxseg, hxline⟩
  exact Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, ⟨hxseg, hxline⟩⟩⟩

/-- Any point of a finite translated-edge cover of a line is either in one of its
line-directed translated segments or in the finite exceptional set from the transverse
segments. -/
private theorem finite_translate_cover_reduce_to_parallel_or_exception
    {ε : Submodule ℝ Plane} {ℓ x : Plane}
    (hε : Module.finrank ℝ ε = 1)
    (G : Finset (Plane × (Plane × Plane)))
    (hx : ∃ g ∈ G, x ∈ segment ℝ (g.1 + g.2.1) (g.1 + g.2.2) ∧
      x ∈ ℓ +ᵥ (ε : Set Plane)) :
    ∃ E : Set Plane, E.Finite ∧
      (x ∈ E ∨ ∃ g ∈ G,
        Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) = ε ∧
          x ∈ segment ℝ (g.1 + g.2.1) (g.1 + g.2.2)) := by
  classical
  let Gtransverse := G.filter fun g =>
    Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) ≠ ε
  have hGtransverse (g) (hg : g ∈ Gtransverse) :
      Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) ≠ ε :=
    (Finset.mem_filter.mp hg).2
  let E : Set Plane := {y | ∃ g ∈ Gtransverse,
    y ∈ segment ℝ (g.1 + g.2.1) (g.1 + g.2.2) ∧
      y ∈ ℓ +ᵥ (ε : Set Plane)}
  have hE : E.Finite := by
    apply finite_nonparallel_translate_intersections hε Gtransverse hGtransverse
  obtain ⟨g, hg, hseg, hline⟩ := hx
  by_cases hparallel : Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) = ε
  · exact ⟨E, hE, Or.inr ⟨g, hg, hparallel, hseg⟩⟩
  · have hgtransverse : g ∈ Gtransverse := Finset.mem_filter.mpr ⟨hg, hparallel⟩
    exact ⟨E, hE, Or.inl ⟨g, hgtransverse, hseg, hline⟩⟩

private theorem translated_aligned_edge_endpoint_mem_line
    {a b s x ℓ : Plane} {ε : Submodule ℝ Plane}
    (haligned : Submodule.span ℝ ({b - a} : Set Plane) = ε)
    (hxseg : x ∈ segment ℝ (a + s) (b + s))
    (hxline : x ∈ ℓ +ᵥ (ε : Set Plane)) :
    a + s ∈ ℓ +ᵥ (ε : Set Plane) := by
  have haSeg : a + s ∈ segment ℝ (a + s) (b + s) := by
    exact left_mem_segment ℝ _ _
  have hdiff : (a + s) - x ∈ Submodule.span ℝ ({b - a} : Set Plane) := by
    have := segment_sub_mem_direction hxseg haSeg
    have hvec : (b + s) - (a + s) = b - a := by abel
    rw [hvec] at this
    exact this
  have hxε : x - ℓ ∈ ε := by
    change x - ℓ ∈ (ε : Set Plane)
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hxline
  have haε : a + s - ℓ ∈ ε := by
    rw [haligned] at hdiff
    have := ε.add_mem hdiff hxε
    convert this using 1 <;> abel
  change a + s - ℓ ∈ (ε : Set Plane) at haε
  simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
    neg_add_eq_sub] using haε

/-- For one ε-parallel prototype edge, at most one translate by an affine-δ-line centre
can meet the fixed ε-line. -/
private theorem aligned_translate_center_unique_of_intersection
    {S : Set Plane} {δ ε : Submodule ℝ Plane} {a b ℓ : Plane}
    (hδ : Module.finrank ℝ δ = 1) (hε : Module.finrank ℝ ε = 1)
    (hne : δ ≠ ε) (hS : IsLineSupported S δ)
    (haligned : Submodule.span ℝ ({b - a} : Set Plane) = ε)
    {s t : Plane} (hs : s ∈ S) (ht : t ∈ S)
    (hxs : ∃ x ∈ segment ℝ (a + s) (b + s), x ∈ ℓ +ᵥ (ε : Set Plane))
    (hxt : ∃ x ∈ segment ℝ (a + t) (b + t), x ∈ ℓ +ᵥ (ε : Set Plane)) :
    s = t := by
  obtain ⟨xs, hxss, hxsl⟩ := hxs
  obtain ⟨xt, hxts, hxtl⟩ := hxt
  exact edgeTranslate_eq_of_endpoint_mem_transverseLine (ℓ := ℓ) (p := a)
    hδ hε hne hS hs ht
    (translated_aligned_edge_endpoint_mem_line haligned hxss hxsl)
    (translated_aligned_edge_endpoint_mem_line haligned hxts hxtl)

private theorem finite_indexed_interval_cover_length_le
    {ι : Type*} {F : Finset ι} {lo hi : ι → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hordered : ∀ i ∈ F, lo i ≤ hi i)
    (hcover : Set.Icc a b ⊆ ⋃ i ∈ (F : Set ι), Set.Icc (lo i) (hi i)) :
    b - a ≤ ∑ i ∈ F, (hi i - lo i) := by
  classical
  have hsub : volume (Set.Icc a b) ≤ volume (⋃ i ∈ (F : Set ι), Set.Icc (lo i) (hi i)) :=
    measure_mono hcover
  have hsum : volume (⋃ i ∈ (F : Set ι), Set.Icc (lo i) (hi i)) ≤
      ∑ i ∈ F, volume (Set.Icc (lo i) (hi i)) := by
    simpa only [Finset.set_biUnion_coe] using
      (measure_biUnion_finset_le F (fun i => Set.Icc (lo i) (hi i)))
  have hleft : volume (Set.Icc a b) = ENNReal.ofReal (b - a) := by
    rw [Real.volume_Icc]
  have hright : (∑ i ∈ F, volume (Set.Icc (lo i) (hi i))) =
      ENNReal.ofReal (∑ i ∈ F, (hi i - lo i)) := by
    calc
      (∑ i ∈ F, volume (Set.Icc (lo i) (hi i))) =
          ∑ i ∈ F, ENNReal.ofReal (hi i - lo i) := by
        apply Finset.sum_congr rfl
        intro i hiF
        rw [Real.volume_Icc]
      _ = ENNReal.ofReal (∑ i ∈ F, (hi i - lo i)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        intro i hiF
        exact sub_nonneg.mpr (hordered i hiF)
  have hineq := hsub.trans hsum
  rw [hleft, hright] at hineq
  have hbudget : 0 ≤ ∑ i ∈ F, (hi i - lo i) :=
    Finset.sum_nonneg (fun i hiF => sub_nonneg.mpr (hordered i hiF))
  exact (ENNReal.ofReal_le_ofReal_iff hbudget).mp hineq

private theorem finite_indexed_interval_cover_length_le_exceptFinite
    {ι : Type*} {F : Finset ι} {P : Finset ℝ} {lo hi : ι → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hordered : ∀ i ∈ F, lo i ≤ hi i)
    (hcover : Set.Icc a b ⊆
      (⋃ i ∈ (F : Set ι), Set.Icc (lo i) (hi i)) ∪ (P : Set ℝ)) :
    b - a ≤ ∑ i ∈ F, (hi i - lo i) := by
  classical
  have hPzero : volume (P : Set ℝ) = 0 := P.finite_toSet.measure_zero volume
  have hsub : volume (Set.Icc a b) ≤
      volume ((⋃ i ∈ (F : Set ι), Set.Icc (lo i) (hi i)) ∪ (P : Set ℝ)) :=
    measure_mono hcover
  have hunion : volume ((⋃ i ∈ (F : Set ι), Set.Icc (lo i) (hi i)) ∪ (P : Set ℝ)) ≤
      volume (⋃ i ∈ (F : Set ι), Set.Icc (lo i) (hi i)) := by
    calc
      volume ((⋃ i ∈ (F : Set ι), Set.Icc (lo i) (hi i)) ∪ (P : Set ℝ)) ≤
          volume (⋃ i ∈ (F : Set ι), Set.Icc (lo i) (hi i)) + volume (P : Set ℝ) :=
        measure_union_le _ _
      _ = volume (⋃ i ∈ (F : Set ι), Set.Icc (lo i) (hi i)) := by rw [hPzero, add_zero]
  have hsum : volume (⋃ i ∈ (F : Set ι), Set.Icc (lo i) (hi i)) ≤
      ∑ i ∈ F, volume (Set.Icc (lo i) (hi i)) := by
    simpa only [Finset.set_biUnion_coe] using
      (measure_biUnion_finset_le F (fun i => Set.Icc (lo i) (hi i)))
  have hleft : volume (Set.Icc a b) = ENNReal.ofReal (b - a) := by rw [Real.volume_Icc]
  have hright : (∑ i ∈ F, volume (Set.Icc (lo i) (hi i))) =
      ENNReal.ofReal (∑ i ∈ F, (hi i - lo i)) := by
    calc
      (∑ i ∈ F, volume (Set.Icc (lo i) (hi i))) =
          ∑ i ∈ F, ENNReal.ofReal (hi i - lo i) := by
        apply Finset.sum_congr rfl
        intro i hiF
        rw [Real.volume_Icc]
      _ = ENNReal.ofReal (∑ i ∈ F, (hi i - lo i)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        intro i hiF
        exact sub_nonneg.mpr (hordered i hiF)
  have hineq := hsub.trans (hunion.trans hsum)
  rw [hleft, hright] at hineq
  have hbudget : 0 ≤ ∑ i ∈ F, (hi i - lo i) :=
    Finset.sum_nonneg (fun i hiF => sub_nonneg.mpr (hordered i hiF))
  exact (ENNReal.ofReal_le_ofReal_iff hbudget).mp hineq

private theorem finite_line_run_cover_length_le
    {ε : Submodule ℝ Plane} {G : Finset (Plane × (Plane × Plane))}
    {p v : Plane} {B : ℝ}
    (hε : Module.finrank ℝ ε = 1)
    (hv : v ∈ ε) (hvnorm : ‖v‖ = 1)
    (τ : Plane →L[ℝ] ℝ) (hτnorm : ‖τ‖ ≤ 1) (hτv : τ v = 1)
    (hB : 0 ≤ B)
    (hcover : ∀ t ∈ Set.Icc (0 : ℝ) B,
      ∃ g ∈ G, p + t • v ∈ segment ℝ (g.1 + g.2.1) (g.1 + g.2.2)) :
    B ≤ ∑ g ∈ G.filter (fun g =>
      Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) = ε),
      dist g.2.1 g.2.2 := by
  classical
  let Gparallel := G.filter fun g =>
    Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) = ε
  let Gtransverse := G.filter fun g =>
    Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) ≠ ε
  have hGtransverse (g) (hg : g ∈ Gtransverse) :
      Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) ≠ ε :=
    (Finset.mem_filter.mp hg).2
  let E : Set Plane := {x | ∃ g ∈ Gtransverse,
    x ∈ segment ℝ (g.1 + g.2.1) (g.1 + g.2.2) ∧ x ∈ p +ᵥ (ε : Set Plane)}
  have hE : E.Finite := by
    apply finite_nonparallel_translate_intersections hε Gtransverse hGtransverse
  let P : Finset ℝ := hE.toFinset.image fun x => τ (x - p)
  let lo (g : Plane × (Plane × Plane)) :=
    min (τ (g.1 + g.2.1 - p)) (τ (g.1 + g.2.2 - p))
  let hi (g : Plane × (Plane × Plane)) :=
    max (τ (g.1 + g.2.1 - p)) (τ (g.1 + g.2.2 - p))
  have hordered : ∀ g ∈ Gparallel, lo g ≤ hi g := by
    intro g hg
    exact min_le_max
  have hparamCover : Set.Icc (0 : ℝ) B ⊆
      (⋃ g ∈ (Gparallel : Set (Plane × (Plane × Plane))), Set.Icc (lo g) (hi g)) ∪
        (P : Set ℝ) := by
    intro t ht
    obtain ⟨g, hg, hseg⟩ := hcover t ht
    have hxline : p + t • v ∈ p +ᵥ (ε : Set Plane) := by
      have htv : t • v ∈ (ε : Set Plane) := ε.smul_mem t hv
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change -p + (p + t • v) ∈ (ε : Set Plane)
      convert htv using 1 <;> abel
    have hparam : τ ((p + t • v) - p) = t := by
      have heq : (p + t • v) - p = t • v := by abel
      rw [heq, map_smul]
      simp [hτv]
    by_cases hpar : Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) = ε
    · have hgpar : g ∈ Gparallel := Finset.mem_filter.mpr ⟨hg, hpar⟩
      rw [segment_eq_image'] at hseg
      obtain ⟨r, hr, hpoint⟩ := hseg
      have hpoint' : p + t • v =
          g.1 + g.2.1 + r • (g.2.2 - g.2.1) := by
        calc
          p + t • v = (fun θ => g.1 + g.2.1 +
              θ • (g.1 + g.2.2 - (g.1 + g.2.1))) r := hpoint.symm
          _ = g.1 + g.2.1 + r • (g.2.2 - g.2.1) := by
            congr 1
            congr 1
            abel
      have hcoord : t =
          τ (g.1 + g.2.1 - p) + r *
            (τ (g.1 + g.2.2 - p) - τ (g.1 + g.2.1 - p)) := by
        calc
          t = τ ((p + t • v) - p) := hparam.symm
          _ = τ ((g.1 + g.2.1 + r • (g.2.2 - g.2.1)) - p) := by rw [hpoint']
          _ = τ (g.1 + g.2.1 - p) +
              r * (τ (g.1 + g.2.2 - p) - τ (g.1 + g.2.1 - p)) := by
            have hdiff : τ (g.1 + g.2.2 - p) - τ (g.1 + g.2.1 - p) =
                τ (g.2.2 - g.2.1) := by
              calc
                τ (g.1 + g.2.2 - p) - τ (g.1 + g.2.1 - p) =
                    τ ((g.1 + g.2.2 - p) - (g.1 + g.2.1 - p)) := by rw [← map_sub]
                _ = τ (g.2.2 - g.2.1) := by
                  congr 1
                  abel
            have hmove :
                g.1 + g.2.1 + r • (g.2.2 - g.2.1) - p =
                  (g.1 + g.2.1 - p) + r • (g.2.2 - g.2.1) := by abel
            have hcoordBase :
                τ ((g.1 + g.2.1 + r • (g.2.2 - g.2.1)) - p) =
                  τ (g.1 + g.2.1 - p) + r * τ (g.2.2 - g.2.1) := by
              rw [hmove, map_add, map_smul, smul_eq_mul]
            rw [hcoordBase, ← hdiff]
      have hr0 : 0 ≤ r := hr.1
      have hr1 : r ≤ 1 := hr.2
      have hbetween : lo g ≤ t ∧ t ≤ hi g := by
        dsimp [lo, hi]
        by_cases horder : τ (g.1 + g.2.1 - p) ≤ τ (g.1 + g.2.2 - p)
        · rw [min_eq_left horder, max_eq_right horder]
          constructor <;> nlinarith
        · have hrev : τ (g.1 + g.2.2 - p) ≤ τ (g.1 + g.2.1 - p) := le_of_not_ge horder
          rw [min_eq_right hrev, max_eq_left hrev]
          constructor <;> nlinarith
      rcases hbetween with ⟨hlt, hth⟩
      exact Or.inl (Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hgpar,
        Set.mem_Icc.mpr ⟨hlt, hth⟩⟩⟩)
    · have hgtrans : g ∈ Gtransverse := Finset.mem_filter.mpr ⟨hg, hpar⟩
      have hEpoint : p + t • v ∈ E := ⟨g, hgtrans, hseg, hxline⟩
      have htmem : t ∈ P := by
        apply Finset.mem_image.mpr
        refine ⟨p + t • v, hE.mem_toFinset.mpr hEpoint, ?_⟩
        exact hparam
      exact Or.inr htmem
  have hbudget := finite_indexed_interval_cover_length_le_exceptFinite
    hB hordered hparamCover
  have hlength (g : Plane × (Plane × Plane)) (hg : g ∈ Gparallel) :
      hi g - lo g ≤ dist g.2.1 g.2.2 := by
    dsimp [hi, lo]
    rw [max_sub_min_eq_abs]
    have hmap : τ (g.1 + g.2.2 - p) - τ (g.1 + g.2.1 - p) =
        τ (g.2.2 - g.2.1) := by
      calc
        τ (g.1 + g.2.2 - p) - τ (g.1 + g.2.1 - p) =
            τ ((g.1 + g.2.2 - p) - (g.1 + g.2.1 - p)) := by rw [← map_sub]
        _ = τ (g.2.2 - g.2.1) := by
          congr 1
          abel
    rw [hmap, ← Real.norm_eq_abs]
    calc
      ‖τ (g.2.2 - g.2.1)‖ ≤ ‖τ‖ * ‖g.2.2 - g.2.1‖ := τ.le_opNorm _
      _ ≤ 1 * ‖g.2.2 - g.2.1‖ :=
        mul_le_mul_of_nonneg_right hτnorm (norm_nonneg _)
      _ = dist g.2.1 g.2.2 := by
        rw [dist_eq_norm]
        congr 1
        simp [norm_sub_rev]
  calc
    B ≤ ∑ g ∈ Gparallel, (hi g - lo g) := by simpa using hbudget
    _ ≤ ∑ g ∈ Gparallel, dist g.2.1 g.2.2 := by
      apply Finset.sum_le_sum
      intro g hg
      exact hlength g hg
    _ = ∑ g ∈ G.filter (fun g =>
        Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) = ε),
        dist g.2.1 g.2.2 := by rfl

private theorem aligned_translated_edge_budget
    {δ ε : Submodule ℝ Plane} {S : Set Plane} {F : Finset (Plane × Plane)}
    {G : Finset (Plane × (Plane × Plane))} {p : Plane}
    (hδ : Module.finrank ℝ δ = 1) (hε : Module.finrank ℝ ε = 1)
    (hne : δ ≠ ε) (hline : IsLineSupported S δ)
    (hcentres : ∀ g ∈ G, g.1 ∈ S) (hbase : ∀ g ∈ G, g.2 ∈ F)
    (hmeet : ∀ g ∈ G, ∃ z ∈ segment ℝ (g.1 + g.2.1) (g.1 + g.2.2),
      z ∈ p +ᵥ (ε : Set Plane)) :
    (∑ g ∈ G.filter (fun g => Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) = ε),
      dist g.2.1 g.2.2) ≤ ∑ e ∈ F, dist e.1 e.2 := by
  classical
  let P := G.filter fun g => Submodule.span ℝ ({g.2.2 - g.2.1} : Set Plane) = ε
  have hinj : Set.InjOn (fun g : Plane × (Plane × Plane) => g.2) (P : Set _) := by
    intro g hg h hh hsame
    have hgG := (Finset.mem_filter.mp hg).1
    have hhG := (Finset.mem_filter.mp hh).1
    have hcent : g.1 = h.1 := aligned_translate_center_unique_of_intersection
      hδ hε hne hline (Finset.mem_filter.mp hg).2 (hcentres _ hgG) (hcentres _ hhG)
      (by simpa only [add_comm] using hmeet g hgG)
      (by simpa only [hsame, add_comm] using hmeet h hhG)
    exact Prod.ext hcent hsame
  have hsubset : P.image (fun g => g.2) ⊆ F := by
    intro e he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp he
    exact hbase g (Finset.mem_filter.mp hg).1
  calc
    (∑ g ∈ P, dist g.2.1 g.2.2) =
        ∑ e ∈ P.image (fun g => g.2), dist e.1 e.2 := by
      rw [Finset.sum_image]
      exact hinj
    _ ≤ ∑ e ∈ F, dist e.1 e.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => dist_nonneg)

private theorem nonparallel_frontier_segment_length_le
    {K : PolygonalRegion} {δ ε : Submodule ℝ Plane} {S : Set Plane}
    (F : Finset (Plane × Plane))
    (hfrontier : frontier K.support = ⋃ e ∈ F, segment ℝ e.1 e.2)
    (hδ : Module.finrank ℝ δ = 1) (hε : Module.finrank ℝ ε = 1)
    (hp : IsPacking K.prototileFamily (K.placements S)) (hline : IsLineSupported S δ)
    (hne : δ ≠ ε) {p v : Plane} (hv : v ∈ ε) (hvnorm : ‖v‖ = 1)
    {B : ℝ} (hB : 0 < B)
    (hQfront : segment ℝ p (p + B • v) ⊆ frontier (regularSupport K S)) :
    B ≤ ∑ e ∈ F, dist e.1 e.2 := by
  classical
  obtain ⟨G, hG, hcover⟩ := frontier_segment_finite_translated_edge_cover hp F hfrontier hQfront
  let H := G.filter fun g =>
    (segment ℝ (g.1 + g.2.1) (g.1 + g.2.2) ∩ (p +ᵥ (ε : Set Plane))).Nonempty
  have hcentres : ∀ g ∈ H, g.1 ∈ S := fun g hg =>
    (hG g (Finset.mem_filter.mp hg).1).1
  have hbase : ∀ g ∈ H, g.2 ∈ F := fun g hg =>
    (hG g (Finset.mem_filter.mp hg).1).2
  have hmeet : ∀ g ∈ H, ∃ z ∈ segment ℝ (g.1 + g.2.1) (g.1 + g.2.2),
      z ∈ p +ᵥ (ε : Set Plane) := by
    intro g hg
    obtain ⟨z, hzseg, hzline⟩ := (Finset.mem_filter.mp hg).2
    exact ⟨z, hzseg, hzline⟩
  have hcoverRun : ∀ t ∈ Set.Icc (0 : ℝ) B,
      ∃ g ∈ H, p + t • v ∈ segment ℝ (g.1 + g.2.1) (g.1 + g.2.2) := by
    intro t ht
    have hxQ : p + t • v ∈ segment ℝ p (p + B • v) := by
      rw [segment_eq_image']
      refine ⟨t / B, ⟨div_nonneg ht.1 (by linarith),
        (div_le_one (by linarith : 0 < B)).mpr ht.2⟩, ?_⟩
      change p + (t / B) • ((p + B • v) - p) = p + t • v
      rw [add_sub_cancel_left]
      congr 1
      rw [smul_smul, div_mul_cancel₀ _ (by linarith : B ≠ 0)]
    obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.mp (hcover hxQ)
    refine ⟨g, Finset.mem_filter.mpr ⟨hg, ?_⟩, hxg⟩
    exact ⟨p + t • v, hxg, Set.mem_vadd_set.mpr ⟨t • v, ε.smul_mem t hv, rfl⟩⟩
  obtain ⟨τ, hτnorm, hτv⟩ := unit_tangent_coordinate_exists hvnorm
  have hscalar := finite_line_run_cover_length_le
    hε hv hvnorm τ hτnorm hτv (by linarith : 0 ≤ B) hcoverRun
  have hprototype := aligned_translated_edge_budget hδ hε hne hline hcentres hbase hmeet
  exact hscalar.trans hprototype

private theorem complete_frontier_line_parallel_to_centres
    {K : PolygonalRegion} {δ ε : Submodule ℝ Plane} {S : Set Plane} {a : Plane}
    (hδ : Module.finrank ℝ δ = 1) (hε : Module.finrank ℝ ε = 1)
    (hp : IsPacking K.prototileFamily (K.placements S)) (hline : IsLineSupported S δ)
    (hfront : a +ᵥ (ε : Set Plane) ⊆ frontier (regularSupport K S)) : δ = ε := by
  classical
  obtain ⟨F, _, hFfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  let L : ℝ := ∑ e ∈ F, dist e.1 e.2
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => dist_nonneg)
  by_contra hne
  have hεbot : ε ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hε
    exact Nat.zero_ne_one hε
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hεbot
  let v : Plane := ‖w‖⁻¹ • w
  have hvnorm : ‖v‖ = 1 := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
  have hvε : v ∈ ε := ε.smul_mem _ hw
  have hQfront : segment ℝ a (a + (L + 1) • v) ⊆ frontier (regularSupport K S) := by
    intro x hx
    apply hfront
    rw [segment_eq_image'] at hx
    obtain ⟨t, _, rfl⟩ := hx
    change a + t • ((a + (L + 1) • v) - a) ∈ a +ᵥ (ε : Set Plane)
    rw [add_sub_cancel_left]
    exact Set.mem_vadd_set.mpr ⟨t • ((L + 1) • v), ε.smul_mem t (ε.smul_mem _ hvε), rfl⟩
  have hbudget := nonparallel_frontier_segment_length_le F hFfront hδ hε hp hline
    hne hvε hvnorm (by linarith : 0 < L + 1) hQfront
  change L + 1 ≤ L at hbudget
  linarith

private theorem locallySaturatedAlong_of_parallel_frontier_germs
    {D : Set Plane} (hD : IsOpen D) {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) {x : Plane} {R : ℝ}
    (hlocal : ∀ p ∈ Metric.ball x R, p ∈ frontier D →
      ∃ L : AffineSubspace ℝ Plane, p ∈ L ∧
        Module.finrank ℝ L.direction = 1 ∧ L.direction = δ ∧
          ∀ᶠ q in 𝓝 p, q ∈ frontier D ↔ q ∈ (L : Set Plane)) :
    LocallySaturatedAlong D δ x R := by
  have hW : ∀ p ∈ Metric.ball x R, p ∉ properVertices D := by
    intro p hp hpW
    obtain ⟨L, hpL, hL, _, hg⟩ := hlocal p hp hpW.1
    exact hpW.2 ⟨L, hpL, hL, hg⟩
  intro y hy z hz hzy
  have hsegball : segment ℝ y z ⊆ Metric.ball x R :=
    (convex_ball x R).segment_subset hy hz
  by_cases hdisj : Disjoint (segment ℝ y z) (frontier D)
  · rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      (convex_segment (𝕜 := ℝ) y z).isPreconnected hdisj with hin | hout
    · exact iff_of_true (interior_subset (hin (left_mem_segment ℝ y z)))
        (interior_subset (hin (right_mem_segment ℝ y z)))
    · exact iff_of_false (interior_subset (hout (left_mem_segment ℝ y z)))
        (interior_subset (hout (right_mem_segment ℝ y z)))
  · obtain ⟨p, hpseg, hpfront⟩ := Set.not_disjoint_iff.mp hdisj
    have hpball := hsegball hpseg
    obtain ⟨L, hpL, hL, hdir, hg⟩ := hlocal p hpball hpfront
    have hrepr : (L : Set Plane) = p +ᵥ (δ : Set Plane) := by
      rw [affineSubspace_eq_anchor_vadd_direction hpL, hdir]
    have hpy : p - y ∈ δ := by
      rw [segment_eq_image'] at hpseg
      obtain ⟨t, _, rfl⟩ := hpseg
      simpa only [add_sub_cancel_left] using δ.smul_mem t hzy
    have hyδ : y - p ∈ δ := by simpa only [neg_sub] using δ.neg_mem hpy
    have hzδ : z - p ∈ δ := by
      convert δ.sub_mem hzy hpy using 1 <;> abel
    have hendpoint : ∀ w ∈ Metric.ball x R, w - p ∈ δ → w ∈ frontier D := by
      intro w hw hwp
      by_cases heq : w = p
      · simpa only [heq] using hpfront
      · have hv : w - p ≠ 0 := sub_ne_zero.mpr heq
        have hspan : Submodule.span ℝ ({w - p} : Set Plane) = δ :=
          (eq_span_singleton_of_mem_of_finrank_eq_one hδ hwp hv).symm
        have hg' : ∀ᶠ q in 𝓝 p, q ∈ frontier D ↔
            q ∈ p +ᵥ (Submodule.span ℝ ({w - p} : Set Plane) : Set Plane) := by
          simpa only [hspan, ← hrepr] using hg
        have hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, p + t • (w - p) ∈ Metric.ball x R := by
          intro t ht
          apply (convex_ball x R).segment_subset hpball hw
          rw [segment_eq_image']
          exact ⟨t, ht, rfl⟩
        have hrun := frontier_ray_segment_of_no_properVertices hv zero_lt_one hpfront hg'
          (fun t ht => hW _ (hpath t ht)) 1 (by simp)
        simpa only [one_smul, add_sub_cancel] using hrun
    have hyfront := hendpoint y hy hyδ
    have hzfront := hendpoint z hz hzδ
    exact iff_of_false (fun h => hyfront.2 (hD.interior_eq.symm ▸ h))
      (fun h => hzfront.2 (hD.interior_eq.symm ▸ h))

theorem noCornerLineCarrier_localSaturation_of_boundaryLength
    {K : PolygonalRegion} (F : Finset (Plane × Plane)) (L : ℝ) (hL : 0 ≤ L)
    (hfrontier : frontier K.support = ⋃ e ∈ F, segment ℝ e.1 e.2)
    (hlength : (∑ e ∈ F, dist e.1 e.2) ≤ L)
    {δ : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1)
    {S : Set Plane} (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : IsLineSupported S δ) {x : Plane} {R : ℝ} (hR : 0 < R)
    (hcorners : Disjoint (properVertices (regularSupport K S))
      (Metric.ball x (R + L + 1))) :
    LocallySaturatedAlong (regularSupport K S) δ x R := by
  apply locallySaturatedAlong_of_parallel_frontier_germs
    (regularSupport_isRegularOpen K S).1 hδ
  intro p hpball hpfront
  have hpouter : p ∈ Metric.ball x (R + L + 1) :=
    Metric.ball_subset_ball (by linarith) hpball
  have hpW : p ∉ properVertices (regularSupport K S) :=
    fun hpW => Set.disjoint_left.mp hcorners hpW hpouter
  have hstraight : BoundaryLocallyStraightAt (regularSupport K S) p := by
    by_contra h
    exact hpW ⟨hpfront, h⟩
  obtain ⟨A, hpA, hA, hg⟩ := hstraight
  refine ⟨A, hpA, hA, ?_, hg⟩
  -- OPEN quantitative finite-edge budget: a nonparallel unit tangent run of
  -- length L+1 stays in the enlarged no-corner ball. Ray continuation makes
  -- it frontier; each aligned prototype edge contributes at most one translate,
  -- and the total available edge length is at most L.
  by_contra hne
  have hAbot : A.direction ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hA
    exact Nat.zero_ne_one hA
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hAbot
  let v : Plane := ‖w‖⁻¹ • w
  have hvnorm : ‖v‖ = 1 := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hvnorm
    exact zero_ne_one hvnorm
  have hvA : v ∈ A.direction := A.direction.smul_mem _ hw
  have hspan : Submodule.span ℝ ({v} : Set Plane) = A.direction :=
    (eq_span_singleton_of_mem_of_finrank_eq_one hA hvA hv0).symm
  have hrepr := affineSubspace_eq_anchor_vadd_direction hpA
  have hg' : ∀ᶠ q in 𝓝 p, q ∈ frontier (regularSupport K S) ↔
      q ∈ p +ᵥ (Submodule.span ℝ ({v} : Set Plane) : Set Plane) := by
    simpa only [hspan, ← hrepr] using hg
  have hrunBall : ∀ t ∈ Set.Icc (0 : ℝ) (L + 1),
      p + t • v ∈ Metric.ball x (R + L + 1) := by
    intro t ht
    rw [Metric.mem_ball]
    calc
      dist (p + t • v) x ≤ dist (p + t • v) p + dist p x := dist_triangle _ _ _
      _ = t + dist p x := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ht.1, hvnorm, mul_one]
      _ ≤ (L + 1) + dist p x := by linarith [ht.2]
      _ < R + L + 1 := by
        have hpdist : dist p x < R := Metric.mem_ball.mp hpball
        linarith
  have hrunFront := frontier_ray_segment_of_no_properVertices hv0 (by linarith : 0 < L + 1)
    hpfront hg' (fun t ht htW => Set.disjoint_left.mp hcorners htW (hrunBall t ht))
  have hQfront : segment ℝ p (p + (L + 1) • v) ⊆ frontier (regularSupport K S) := by
    intro q hq
    rw [segment_eq_image'] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    have ht' : t * (L + 1) ∈ Set.Icc (0 : ℝ) (L + 1) :=
      ⟨mul_nonneg ht.1 (by linarith), by nlinarith [ht.2]⟩
    simpa only [add_sub_cancel_left, v, smul_smul, mul_assoc] using
      hrunFront (t * (L + 1)) ht'
  -- OPEN only the compact translated-edge length budget remains here.
  have hbudget := nonparallel_frontier_segment_length_le F hfrontier hδ hA hp hline
    (Ne.symm hne) hvA hvnorm (by linarith : 0 < L + 1) hQfront
  linarith

theorem noCornerLineCarrier_localSaturation (K : PolygonalRegion) :
    ∃ A : ℝ, 0 < A ∧ ∀ (δ : Submodule ℝ Plane), Module.finrank ℝ δ = 1 →
      ∀ (S : Set Plane), IsPacking K.prototileFamily (K.placements S) →
        IsLineSupported S δ → ∀ (x : Plane) (R : ℝ), 0 < R →
          Disjoint (properVertices (regularSupport K S)) (Metric.ball x (R + A)) →
          LocallySaturatedAlong (regularSupport K S) δ x R := by
  obtain ⟨F, _, hfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  let L : ℝ := ∑ e ∈ F, dist e.1 e.2
  have hL : 0 ≤ L := Finset.sum_nonneg (fun e _ => dist_nonneg)
  refine ⟨L + 1, by linarith, ?_⟩
  intro δ hδ S hp hline x R hR hcorners
  apply noCornerLineCarrier_localSaturation_of_boundaryLength F L hL hfront le_rfl
    hδ hp hline hR
  simpa only [add_assoc] using hcorners

private theorem stripFrontierPoint
    {K : Tiling.RationalPolygonal.PolygonalRegion} {δ : Submodule ℝ Plane}
    {S : Set Plane} {B : ℝ}
    (hδ : Module.finrank ℝ δ = 1) (hB : 0 < B)
    (hbound : K.support ⊆ Metric.closedBall 0 B)
    (hp : Tiling.IsPacking K.prototileFamily (K.placements S))
    (hline : IsLineSupported S δ) {t : Plane} (ht : t ∈ S) :
    ∃ p ∈ frontier (regularSupport K S), dist p t < 2 * B + 2 := by
  have hδbot : δ ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hδ
    norm_num at hδ
  obtain ⟨v, hvδ, hvne⟩ := (Submodule.ne_bot_iff δ).mp hδbot
  let w : Plane := (‖v‖⁻¹ : ℝ) • v
  have hwδ : w ∈ δ := δ.smul_mem _ hvδ
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    simp
    field_simp [ne_of_gt (norm_pos_iff.mpr hvne)]
  have hwne : w ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hwNorm
    norm_num at hwNorm
  have hspan : Submodule.span ℝ ({w} : Set Plane) = δ := by
    apply Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_singleton_le_iff_mem _ _ |>.2 hwδ)
    rw [finrank_span_singleton hwne, hδ]
  let n : Plane := Complex.I • w
  have hnNorm : ‖n‖ = 1 := by
    dsimp [n]
    simp [hwNorm]
  have hnOrth : inner ℝ n w = 0 := by
    rw [real_inner_comm]
    dsimp [n]
    exact real_inner_I_smul_self Plane w
  let ψ : Plane →L[ℝ] ℝ := innerSL ℝ n
  have hψn : ψ n = 1 := by
    simp [ψ, innerSL_apply_apply, hnNorm]
  have hψδ : ∀ q ∈ δ, ψ q = 0 := by
    intro q hq
    rw [← hspan] at hq
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hq
    change inner ℝ n (r • w) = 0
    rw [inner_smul_right, hnOrth, mul_zero]
  obtain ⟨c, hc⟩ := hline
  have hdiffLine (s : Plane) (hs : s ∈ S) : s - t ∈ δ := by
    have hmem := δ.sub_mem (hc s hs) (hc t ht)
    simpa using hmem
  have hopenUnion (V : Set Plane) : IsOpen (openUnion K V) := by
    change IsOpen (⋃ s : V, (s : Plane) +ᵥ interior K.support)
    exact isOpen_iUnion fun s =>
      (Homeomorph.addLeft (s : Plane)).isOpen_image.mpr isOpen_interior
  obtain ⟨a, ha⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have haSupport : a ∈ K.support := interior_subset ha
  have haNorm : ‖a‖ ≤ B := by
    have hclosed := hbound haSupport
    simpa [Metric.mem_closedBall, dist_eq_norm] using hclosed
  have hyopen : t + a ∈ openUnion K S := by
    rw [openUnion]
    refine mem_iUnion.mpr ⟨⟨t, ht⟩, ?_⟩
    rw [mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, add_assoc, add_left_comm, add_comm,
      Tiling.RationalPolygonal.PolygonalRegion.openCarrier] using ha
  have hy : t + a ∈ regularSupport K S :=
    (hopenUnion S).subset_interior_closure hyopen
  let z : Plane := t + (B + 1) • n
  have hzOutside : z ∉ regularSupport K S := by
    intro hz
    have hzcl : z ∈ closure (openUnion K S) := interior_subset hz
    rw [closure_openUnion_eq_iUnion_support hp] at hzcl
    rcases mem_iUnion.mp hzcl with ⟨s, hs⟩
    rw [mem_vadd_set_iff_neg_vadd_mem] at hs
    let q : Plane := -(s : Plane) + z
    have hqSupport : q ∈ K.support := by simpa [q] using hs
    have hzEq : z = (s : Plane) + q := by dsimp [q]; abel
    have hqNorm : ‖q‖ ≤ B := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hbound hqSupport
    have hprojTile : |ψ q| ≤ B := by
      calc
        |ψ q| = ‖ψ q‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖n‖ * ‖q‖ := by
          simpa [ψ, innerSL_apply_apply] using abs_real_inner_le_norm n q
        _ ≤ B := by rw [hnNorm]; nlinarith
    have hprojLine : ψ ((s : Plane) - t) = 0 := hψδ _ (hdiffLine _ s.2)
    have hproj : ψ (z - t) = ψ q := by
      have hdecomp : z - t = ((s : Plane) - t) + q := by rw [hzEq]; abel
      rw [hdecomp, map_add, hprojLine, zero_add]
    have hprojZ : ψ (z - t) = B + 1 := by
      rw [show z - t = (B + 1) • n by dsimp [z]; abel, map_smul, hψn]
      ring
    rw [hproj] at hprojZ
    have : |ψ q| ≤ B := hprojTile
    rw [abs_of_nonneg (by linarith [hB] : 0 ≤ ψ q)] at this
    linarith
  let C := segment ℝ (t + a) z
  have hcross : (C ∩ frontier (regularSupport K S)).Nonempty := by
    by_contra hnon
    have hdisj : Disjoint C (frontier (regularSupport K S)) := by
      rw [Set.disjoint_left]
      intro y hyC hyF
      exact hnon ⟨y, hyC, hyF⟩
    have hseg := Tiling.IsPreconnected.subset_interior_of_disjoint_frontier_of_mem
      (convex_segment (t + a) z).isPreconnected hdisj
      (left_mem_segment ℝ (t + a) z) hy
    exact hzOutside (interior_subset (hseg (right_mem_segment ℝ (t + a) z)))
  obtain ⟨p, hpC, hpF⟩ := hcross
  have hyBound : dist (t + a) t < 2 * B + 2 := by
    have hdist : dist (t + a) t = ‖a‖ := by simp [dist_eq_norm]
    rw [hdist]
    linarith [haNorm, hB]
  have hzBound : dist z t < 2 * B + 2 := by
    have hdist : dist z t = B + 1 := by
      rw [show dist z t = ‖(B + 1) • n‖ by dsimp [z]; simp [dist_eq_norm]]
      rw [norm_smul, hnNorm, Real.norm_eq_abs,
        abs_of_pos (by linarith [hB] : 0 < B + 1)]
      ring
    rw [hdist]
    linarith [hB]
  have hrad : 0 < 2 * B + 2 := by linarith [hB]
  have hsegBall : C ⊆ Metric.ball t (2 * B + 2) :=
    (convex_ball t (2 * B + 2)).segment_subset
      (Metric.mem_ball.mpr hyBound) (Metric.mem_ball.mpr hzBound)
  exact ⟨p, hpF, Metric.mem_ball.mp (hsegBall hpC)⟩

private theorem saturated_frontier_segment
    {D : Set Plane} {δ : Submodule ℝ Plane} {x p : Plane} {R : ℝ}
    (hδ : Module.finrank ℝ δ = 1)
    (hsat : LocallySaturatedAlong D δ x R) (hp : p ∈ Metric.ball x R)
    (hpfront : p ∈ frontier D) :
    ∃ q : Plane, p ≠ q ∧ q - p ∈ δ ∧ segment ℝ p q ⊆ frontier D := by
  have hδbot : δ ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hδ
    norm_num at hδ
  obtain ⟨v, hvδ, hvne⟩ := (Submodule.ne_bot_iff δ).mp hδbot
  let w : Plane := (‖v‖⁻¹ : ℝ) • v
  have hwδ : w ∈ δ := δ.smul_mem _ hvδ
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    simp
    field_simp [ne_of_gt (norm_pos_iff.mpr hvne)]
  have hwne : w ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hwNorm
    norm_num at hwNorm
  let ε := (R - dist p x) / 2
  have hε : 0 < ε := by
    have hdist := Metric.mem_ball.mp hp
    dsimp [ε]
    linarith
  let q := p + ε • w
  have hpq : p ≠ q := by
    intro heq
    have hz : ε • w = 0 := by
      change p = p + ε • w at heq
      exact (add_left_cancel (show p + 0 = p + ε • w by simpa using heq)).symm
    exact (smul_ne_zero hε.ne' hwne) hz
  have hqpδ : q - p ∈ δ := by
    simpa [q] using δ.smul_mem ε hwδ
  have hqball : q ∈ Metric.ball x R := by
    apply Metric.mem_ball.mpr
    have htri := dist_triangle q p x
    have hdist : dist q p = ε := by
      simp [q, dist_eq_norm, norm_smul, hwNorm, abs_of_pos hε]
    rw [hdist] at htri
    dsimp [ε] at htri
    have hpdist := Metric.mem_ball.mp hp
    linarith
  have hsegBall : segment ℝ p q ⊆ Metric.ball x R :=
    (convex_ball x R).segment_subset hp hqball
  have hsegCoset : segment ℝ p q ⊆ p +ᵥ (δ : Set Plane) :=
    (δ.convex.vadd p).segment_subset
      ⟨0, δ.zero_mem, by simp⟩ ⟨ε • w, δ.smul_mem ε hwδ, rfl⟩
  refine ⟨q, hpq, hqpδ, ?_⟩
  intro z hz
  have hzpδ : z - p ∈ δ := by
    obtain ⟨u, hu, hzu⟩ := hsegCoset hz
    rw [← hzu]
    simpa [vadd_eq_add] using hu
  exact frontier_translate_of_locallySaturatedAlong hsat hp (hsegBall hz) hzpδ hpfront

theorem lineCarrier_nonboundary_nearProperVertex (K : PolygonalRegion) :
    ∃ A : ℝ, 0 < A ∧ ∀ (δ : Submodule ℝ Plane), Module.finrank ℝ δ = 1 →
      ¬HasBoundaryDirection K δ → ∀ (S : Set Plane),
        IsPacking K.prototileFamily (K.placements S) → IsLineSupported S δ →
        ∀ t ∈ S, ∃ v ∈ properVertices (regularSupport K S), dist t v < A := by
  obtain ⟨A₀, hA₀, hsat⟩ := noCornerLineCarrier_localSaturation K
  -- A bounded strip gives an actual frontier point. Local saturation would
  -- then produce a nondegenerate δ-directed frontier segment.
  have nonboundarySaturationImpossible : ∃ R : ℝ, 0 < R ∧
      ∀ (δ : Submodule ℝ Plane), Module.finrank ℝ δ = 1 →
        ¬HasBoundaryDirection K δ → ∀ S : Set Plane,
          IsPacking K.prototileFamily (K.placements S) → IsLineSupported S δ →
            ∀ t ∈ S, ¬LocallySaturatedAlong (regularSupport K S) δ t R := by
    obtain ⟨B₀, hB₀⟩ := K.isPolygonal.isBounded.subset_closedBall (0 : Plane)
    let B : ℝ := |B₀| + 1
    have hB : 0 < B := by dsimp only [B]; positivity
    have hbound : K.support ⊆ Metric.closedBall (0 : Plane) B :=
      hB₀.trans (Metric.closedBall_subset_closedBall (by
        dsimp only [B]; linarith [le_abs_self B₀]))
    refine ⟨2 * B + 2, by linarith, ?_⟩
    intro δ hδ hnon S hp hline t ht hsatLocal
    obtain ⟨p, hpfront, hpdist⟩ := stripFrontierPoint hδ hB hbound hp hline ht
    obtain ⟨q, hpq, hqp, hsegment⟩ := saturated_frontier_segment hδ hsatLocal
      (Metric.mem_ball.mpr hpdist) hpfront
    exact hnon (frontier_segment_isBoundaryDirection hδ hp hpq hqp hsegment)
  obtain ⟨R, hR, himpossible⟩ := nonboundarySaturationImpossible
  refine ⟨R + A₀, add_pos hR hA₀, ?_⟩
  intro δ hδ hboundary S hp hline t ht
  by_contra hnov
  have hdisj : Disjoint (properVertices (regularSupport K S)) (Metric.ball t (R + A₀)) := by
    apply Set.disjoint_left.mpr
    intro v hv hball
    exact hnov ⟨v, hv, by simpa only [Metric.mem_ball, dist_comm] using hball⟩
  exact himpossible δ hδ hboundary S hp hline t ht
    (hsat δ hδ S hp hline t R hR hdisj)

private theorem lineSupported_difference_mem
    {S : Set Plane} {δ : Submodule ℝ Plane}
    (hline : IsLineSupported S δ)
    {s t : Plane} (hs : s ∈ S) (ht : t ∈ S) : s - t ∈ δ := by
  obtain ⟨c, hc⟩ := hline
  have hsδ : s - c ∈ δ := hc s hs
  have htδ : t - c ∈ δ := hc t ht
  have hdiff := δ.sub_mem hsδ htδ
  convert hdiff using 1; abel

private theorem centre_line_meets_parallel_frontier_line
    {δ : Submodule ℝ Plane} {S : Set Plane} {a : Plane} {B : ℝ}
    (hline : IsLineSupported S δ) {s0 : Plane} (hs0 : s0 ∈ S)
    {x0 : Plane} (hx0line : x0 ∈ a +ᵥ (δ : Set Plane))
    (hx0center : dist x0 s0 ≤ B)
    {t : Plane} (ht : t ∈ S) :
    ∃ x ∈ a +ᵥ (δ : Set Plane), dist x t ≤ B := by
  have hdiff : t - s0 ∈ δ := lineSupported_difference_mem hline ht hs0
  refine ⟨x0 + (t - s0), ?_, ?_⟩
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx0line ⊢
    change -a + x0 ∈ δ at hx0line
    change -a + (x0 + (t - s0)) ∈ δ
    have hadd := δ.add_mem hx0line hdiff
    convert hadd using 1; abel
  · have hdist : dist (x0 + (t - s0)) t = dist x0 s0 := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    rw [hdist]
    exact hx0center

/-- A complete frontier line parallel to a line-supported packing connects all centres
by uniformly short steps. Its only geometric inputs are compactness of the prototype
support and the actual closure-of-open-union support cover. -/
private theorem completeFrontierLine_shortEdgeConnected
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane} {a : Plane}
    (_hδ : Module.finrank ℝ δ = 1)
    {B : ℝ} (hBpos : 0 < B)
    (hsupport : K.support ⊆ Metric.closedBall (0 : Plane) B)
    (hpacking : IsPacking K.prototileFamily (K.placements S))
    (hline : IsLineSupported S δ)
    (hfront : a +ᵥ (δ : Set Plane) ⊆ frontier (regularSupport K S)) :
    ShortEdgeConnected S (4 * B + 1) := by
  have hcover : frontier (regularSupport K S) ⊆
      ⋃ s : S, (s : Plane) +ᵥ K.support := by
    let P : PolygonalProtoTiling Unit := {
      prototiles := K.prototileFamily
      placements := K.placements S
      isPolygonal := fun _ => K.isPolygonal }
    let toPlacement : S → P.placements := fun s => ⟨(s, ()), s.2⟩
    have htoPlacement : Function.Injective toPlacement := by
      intro s t hst
      exact Subtype.ext (congrArg (fun i : P.placements => i.1.1) hst)
    have hloc : LocallyFinite (fun s : S => (s : Plane) +ᵥ K.support) := by
      exact (P.locallyFinite_placedTile hpacking).comp_injective htoPlacement
    have hclosed : IsClosed (⋃ s : S, (s : Plane) +ᵥ K.support) :=
      hloc.isClosed_iUnion fun s => by
        simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
          (Homeomorph.addLeft (s : Plane)).isClosed_image.mpr K.isPolygonal.isClosed
    have hopenSub : openUnion K S ⊆ ⋃ s : S, (s : Plane) +ᵥ K.support := by
      intro x hx
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨s, vadd_set_mono interior_subset hs⟩
    have hregSub : regularSupport K S ⊆ ⋃ s : S, (s : Plane) +ᵥ K.support :=
      interior_subset.trans (closure_minimal hopenSub hclosed)
    have hregClosure : closure (regularSupport K S) ⊆
        ⋃ s : S, (s : Plane) +ᵥ K.support := closure_minimal hregSub hclosed
    exact fun x hx => hregClosure (frontier_subset_closure hx)
  have hlineNonempty : (a +ᵥ (δ : Set Plane)).Nonempty := by
    refine ⟨a, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp
  obtain ⟨x0, hx0line⟩ := hlineNonempty
  have hx0front : x0 ∈ frontier (regularSupport K S) := hfront hx0line
  obtain ⟨s0, hs0⟩ := Set.mem_iUnion.mp (hcover hx0front)
  have hx0base : x0 - (s0 : Plane) ∈ K.support := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hs0
  have hx0bound : dist x0 (s0 : Plane) ≤ B := by
    have hbasebound := hsupport hx0base
    rw [Metric.mem_closedBall, dist_zero_right] at hbasebound
    simpa [dist_eq_norm, sub_eq_add_neg, add_comm] using hbasebound
  have hlineNear : ∀ t ∈ S, ∃ x ∈ a +ᵥ (δ : Set Plane), dist x t ≤ B := by
    intro t ht
    exact centre_line_meets_parallel_frontier_line hline s0.2 hx0line hx0bound ht
  let G : ℝ := 4 * B + 1
  have hGpos : 0 < G := by dsimp [G]; linarith
  let E : Plane → Plane → Prop := fun x y => x ∈ S ∧ y ∈ S ∧ dist x y < G
  have hballOverlap (x y : Plane) (hx : x ∈ S) (hy : y ∈ S)
      {z : Plane} (hzx : z ∈ Metric.ball x (2 * B))
      (hzy : z ∈ Metric.ball y (2 * B)) : E x y := by
    refine ⟨hx, hy, ?_⟩
    have hxz : dist x z < 2 * B := by simpa [Metric.mem_ball, dist_comm] using hzx
    have hyz : dist y z < 2 * B := by simpa [Metric.mem_ball, dist_comm] using hzy
    calc
      dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
      _ < 4 * B := by rw [dist_comm z y]; linarith
      _ < G := by dsimp [G]; linarith
  let U : Set Plane := ⋃ t : {t : Plane // t ∈ S ∧
      Relation.EqvGen E s0 t}, Metric.ball t (2 * B)
  let V : Set Plane := ⋃ t : {t : Plane // t ∈ S ∧
      ¬Relation.EqvGen E s0 t}, Metric.ball t (2 * B)
  have hUopen : IsOpen U := isOpen_iUnion fun t => Metric.isOpen_ball
  have hVopen : IsOpen V := isOpen_iUnion fun t => Metric.isOpen_ball
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    intro z hzU hzV
    obtain ⟨u, hzu⟩ := Set.mem_iUnion.mp hzU
    obtain ⟨v, hzv⟩ := Set.mem_iUnion.mp hzV
    have hedge := hballOverlap u v u.2.1 v.2.1 hzu hzv
    exact v.2.2 ((Relation.EqvGen.trans _ _ _ u.2.2
      (Relation.EqvGen.rel _ _ hedge)))
  have hlineCovered : a +ᵥ (δ : Set Plane) ⊆ U ∪ V := by
    intro x hx
    have hxfront := hfront hx
    obtain ⟨t, hxtile⟩ := Set.mem_iUnion.mp (hcover hxfront)
    have hbase : x - (t : Plane) ∈ K.support := by
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_eq_sub] using hxtile
    have hxbound : dist x (t : Plane) ≤ B := by
      have := hsupport hbase
      rw [Metric.mem_closedBall, dist_zero_right] at this
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm] using this
    have hxinball : x ∈ Metric.ball (t : Plane) (2 * B) := by
      rw [Metric.mem_ball]
      linarith [hxbound, hBpos]
    by_cases hrel : Relation.EqvGen E s0 t
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨t, t.2, hrel⟩, hxinball⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨t, t.2, hrel⟩, hxinball⟩)
  have hpre : IsPreconnected (a +ᵥ (δ : Set Plane)) :=
    ((convex_vadd a).2 δ.convex).isPreconnected
  have hx0inU : x0 ∈ U := by
    have hstrict : dist x0 (s0 : Plane) < 2 * B := by linarith [hx0bound, hBpos]
    exact Set.mem_iUnion.mpr ⟨⟨s0, s0.2, Relation.EqvGen.refl _⟩,
      Metric.mem_ball.mpr (by simpa [dist_comm] using hstrict)⟩
  have hUorV := hpre.subset_or_subset hUopen hVopen hUV hlineCovered
  have hlineInU : a +ᵥ (δ : Set Plane) ⊆ U := by
    rcases hUorV with hU | hV
    · exact hU
    · have : x0 ∈ V := hV hx0line
      exact False.elim (Set.disjoint_left.mp hUV hx0inU this)
  have hconnected : ∀ t ∈ S, Relation.EqvGen E s0 t := by
    intro t ht
    obtain ⟨x, hxline, hxt⟩ := hlineNear t ht
    have hxU := hlineInU hxline
    obtain ⟨u, hxu⟩ := Set.mem_iUnion.mp hxU
    have hxtball : x ∈ Metric.ball t (2 * B) := by
      rw [Metric.mem_ball]
      calc
        dist x t ≤ B := hxt
        _ < 2 * B := by linarith [hBpos]
    have htu := hballOverlap (u : Plane) t u.2.1 ht hxu hxtball
    exact Relation.EqvGen.trans _ _ _ u.2.2 (Relation.EqvGen.rel _ _ htu)
  intro x hx y hy
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (hconnected x hx)) (hconnected y hy)

theorem lineCarrier_fullStraightLine_shortEdgeConnected (K : PolygonalRegion) :
    ∃ G : ℝ, 0 < G ∧ ∀ (δ ε : Submodule ℝ Plane),
      Module.finrank ℝ δ = 1 → Module.finrank ℝ ε = 1 →
      ∀ (S : Set Plane), IsPacking K.prototileFamily (K.placements S) →
        IsLineSupported S δ → (∃ a : Plane, a +ᵥ (ε : Set Plane) ⊆
          frontier (regularSupport K S)) →
          δ = ε ∧ S.Nonempty ∧ ShortEdgeConnected S G := by
  obtain ⟨B₀, hB₀⟩ := K.isPolygonal.isBounded.subset_closedBall (0 : Plane)
  let B : ℝ := |B₀| + 1
  have hBpos : 0 < B := by dsimp only [B]; positivity
  have hsupport : K.support ⊆ Metric.closedBall (0 : Plane) B :=
    hB₀.trans (Metric.closedBall_subset_closedBall (by
      dsimp only [B]; linarith [le_abs_self B₀]))
  refine ⟨4 * B + 1, by linarith, ?_⟩
  intro δ ε hδ hε S hp hline hfull
  obtain ⟨a, hfront⟩ := hfull
  have hdir := complete_frontier_line_parallel_to_centres hδ hε hp hline hfront
  have hS : S.Nonempty := by
    by_contra h
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hafront := hfront (Set.mem_vadd_set.mpr ⟨0, ε.zero_mem, add_zero a⟩)
    have hopenempty : openUnion K S = ∅ := by
      ext x
      simp only [openUnion, Set.mem_iUnion]
      constructor
      · rintro ⟨s, _⟩
        simpa only [hSempty, Set.mem_empty_iff_false] using s.2
      · exact False.elim
    simpa only [regularSupport, hopenempty, closure_empty, interior_empty,
      frontier_empty, Set.mem_empty_iff_false] using hafront
  refine ⟨hdir, hS, ?_⟩
  apply completeFrontierLine_shortEdgeConnected hδ hBpos hsupport hp hline
  simpa only [hdir] using hfront

private theorem locallyStraight_level_halfSpace_germ
    {D : Set Plane} {p : Plane} (ψ : Plane →L[ℝ] ℝ)
    (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (hp : p ∈ frontier D)
    (hgerm : ∀ᶠ y in 𝓝 p, y ∈ frontier D ↔ ψ y = ψ p) :
    (D =ᶠ[𝓝 p] {y : Plane | ψ p < ψ y}) ∨
      (D =ᶠ[𝓝 p] {y : Plane | ψ y < ψ p}) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hgerm
  have hfrontier : frontier (closure D) = frontier D := by
    rw [frontier, closure_closure, hregular]
    symm
    rw [frontier, hopen.interior_eq]
  have hclosedRegular : closure (interior (closure D)) = closure D := by
    rw [hregular]
  have hboundary : ∀ y ∈ Metric.ball p r,
      y ∈ frontier (closure D) ↔ ψ y = ψ p := by
    intro y hy
    rw [hfrontier]
    exact hball hy
  have hchoice := Tiling.local_levelSet_dichotomy ψ hr hclosedRegular
    (hfrontier.symm ▸ hp) hboundary
  have honLine (y : Plane) (hy : y ∈ Metric.ball p r) (hψy : ψ y = ψ p) :
      y ∉ D := by
    intro hyD
    exact Set.disjoint_left.mp disjoint_interior_frontier
      (hopen.interior_eq.symm ▸ hyD) ((hball hy).2 hψy)
  rcases hchoice with hpositive | hnegative
  · left
    filter_upwards [Metric.ball_mem_nhds p hr] with y hy
    apply propext
    change y ∈ D ↔ ψ p < ψ y
    constructor
    · intro hyD
      rcases lt_trichotomy (ψ y) (ψ p) with hlt | heq | hgt
      · exact False.elim ((interior_subset (hpositive.2 ⟨hy, hlt⟩))
          (subset_closure hyD))
      · exact False.elim (honLine y hy heq hyD)
      · exact hgt
    · intro hgt
      simpa only [hregular] using hpositive.1 ⟨hy, hgt⟩
  · right
    filter_upwards [Metric.ball_mem_nhds p hr] with y hy
    apply propext
    change y ∈ D ↔ ψ y < ψ p
    constructor
    · intro hyD
      rcases lt_trichotomy (ψ y) (ψ p) with hlt | heq | hgt
      · exact hlt
      · exact False.elim (honLine y hy heq hyD)
      · exact False.elim ((interior_subset (hnegative.1 ⟨hy, hgt⟩))
          (subset_closure hyD))
    · intro hlt
      simpa only [hregular] using hnegative.2 ⟨hy, hlt⟩

private theorem eventuallyEq_frontier {D E : Set Plane} {p : Plane}
    (h : D =ᶠ[𝓝 p] E) : frontier D =ᶠ[𝓝 p] frontier E := by
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp h
  filter_upwards [hUopen.mem_nhds hpU] with y hyU
  exact propext (eventuallyEq_mem_frontier_iff
    (Filter.mem_of_superset (hUopen.mem_nhds hyU) hUsub))

private theorem eventuallyEq_closure {D E : Set Plane} {p : Plane}
    (h : D =ᶠ[𝓝 p] E) : closure D =ᶠ[𝓝 p] closure E := by
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp h
  filter_upwards [hUopen.mem_nhds hpU] with y hyU
  have hy : D =ᶠ[𝓝 y] E := Filter.mem_of_superset (hUopen.mem_nhds hyU) hUsub
  apply propext
  simp only [closure_eq_compl_interior_compl, Set.mem_compl_iff]
  exact not_congr hy.compl.mem_interior_iff

private theorem level_halfSpace_frontier (ψ : Plane →L[ℝ] ℝ)
    (hψ : Function.Surjective ψ) (c : ℝ) :
    frontier {y : Plane | c < ψ y} = {y : Plane | ψ y = c} := by
  change frontier (ψ ⁻¹' Set.Ioi c) = ψ ⁻¹' {c}
  rw [ψ.frontier_preimage hψ, frontier_Ioi]

private theorem halfSpace_germ_is_locallyStraight
    {D : Set Plane} {p : Plane} (ψ : Plane →L[ℝ] ℝ)
    (hψ : Function.Surjective ψ)
    (hker : Module.finrank ℝ (LinearMap.ker ψ.toLinearMap) = 1)
    (hgerm : D =ᶠ[𝓝 p] {y : Plane | ψ p < ψ y}) :
    p ∈ frontier D ∧ BoundaryLocallyStraightAt D p := by
  have hfront := eventuallyEq_frontier hgerm
  rw [level_halfSpace_frontier ψ hψ] at hfront
  have hpfront : p ∈ frontier D := by
    have hpiff := eventuallyEq_mem_frontier_iff hgerm
    rw [level_halfSpace_frontier ψ hψ] at hpiff
    exact hpiff.mpr rfl
  refine ⟨hpfront, AffineSubspace.mk' p (LinearMap.ker ψ.toLinearMap),
    by simp, by rw [AffineSubspace.direction_mk']; exact hker, ?_⟩
  filter_upwards [hfront] with y hy
  change (y ∈ frontier D) ↔ y - p ∈ LinearMap.ker ψ.toLinearMap
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
  exact Iff.of_eq hy

private theorem opposite_level_halfSpace_germs_impossible
    {D : Set Plane} {p : Plane} (ψ : Plane →L[ℝ] ℝ)
    (hψ : Function.Surjective ψ)
    (hpositive : D =ᶠ[𝓝 p] {y : Plane | ψ p < ψ y})
    (hnegative : D =ᶠ[𝓝 p] {y : Plane | ψ y < ψ p}) : False := by
  have hpclosure : p ∈ closure {y : Plane | ψ p < ψ y} := by
    change p ∈ closure (ψ ⁻¹' Set.Ioi (ψ p))
    rw [ψ.closure_preimage hψ, closure_Ioi]
    change ψ p ∈ Set.Ici (ψ p)
    exact (le_refl (ψ p) : ψ p ≤ ψ p)
  have hfrequent := mem_closure_iff_frequently.mp hpclosure
  obtain ⟨y, hypositive, hyeq⟩ :=
    (hfrequent.and_eventually (hpositive.symm.trans hnegative)).exists
  have hynegative : ψ y < ψ p := (Iff.of_eq hyeq).mp hypositive
  exact (not_lt_of_ge hypositive.le) hynegative

private theorem eventually_level_halfSpace_germ_iff_of_not_proper
    {D : Set Plane} (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (ψ : Plane →L[ℝ] ℝ) (hψ : Function.Surjective ψ)
    (hker : Module.finrank ℝ (LinearMap.ker ψ.toLinearMap) = 1)
    (a v : Plane) (hv : ψ v = 0) (t : ℝ)
    (ht : ¬IsProperVertex D (a + t • v)) :
    ∀ᶠ s in 𝓝 t,
      ((D =ᶠ[𝓝 (a + s • v)] {y : Plane | ψ a < ψ y}) ↔
        (D =ᶠ[𝓝 (a + t • v)] {y : Plane | ψ a < ψ y})) := by
  let φ : ℝ → Plane := fun r => a + r • v
  have hφ : Continuous φ := continuous_const.add (continuous_id.smul continuous_const)
  have hφlevel (r : ℝ) : ψ (φ r) = ψ a := by
    simp only [φ, map_add, map_smul, hv, smul_zero, add_zero]
  let P : ℝ → Prop := fun r => D =ᶠ[𝓝 (φ r)] {y : Plane | ψ a < ψ y}
  change ∀ᶠ s in 𝓝 t, P s ↔ P t
  have hopenGerm (E : Set Plane) : IsOpen {q : Plane | D =ᶠ[𝓝 q] E} :=
    isOpen_setOfPred_eventually_nhds
  by_cases hPt : P t
  · have hnear : ∀ᶠ s in 𝓝 t, P s :=
      hφ.continuousAt.eventually ((hopenGerm _).mem_nhds hPt)
    filter_upwards [hnear] with s hs
    exact iff_of_true hs hPt
  · have hnear : ∀ᶠ s in 𝓝 t, ¬P s := by
      by_cases hxfront : φ t ∈ frontier D
      · obtain ⟨L, hxL, hdim, hlocal⟩ := by
          have hxstraight : BoundaryLocallyStraightAt D (φ t) := by
            by_contra h
            exact ht ⟨hxfront, h⟩
          exact hxstraight
        by_cases hdir : L.direction = LinearMap.ker ψ.toLinearMap
        · have hlineLevel (y : Plane) : y ∈ L ↔ ψ y = ψ (φ t) := by
            change y ∈ (L : Set Plane) ↔ ψ y = ψ (φ t)
            rw [affineSubspace_eq_anchor_vadd_direction hxL, hdir,
              Set.mem_vadd_set_iff_neg_vadd_mem]
            change -φ t + y ∈ LinearMap.ker ψ.toLinearMap ↔ ψ y = ψ (φ t)
            rw [LinearMap.mem_ker, map_add, map_neg]
            change (-ψ (φ t) + ψ y = 0) ↔ ψ y = ψ (φ t)
            constructor <;> intro h <;> linarith
          have hlevel : ∀ᶠ y in 𝓝 (φ t), y ∈ frontier D ↔ ψ y = ψ (φ t) := by
            filter_upwards [hlocal] with y hy
            exact hy.trans (hlineLevel y)
          rcases locallyStraight_level_halfSpace_germ ψ hopen hregular hxfront hlevel
            with hpositive | hnegative
          · exact False.elim (hPt (by simpa only [P, hφlevel] using hpositive))
          · have hnegative' : D =ᶠ[𝓝 (φ t)] {y : Plane | ψ y < ψ a} := by
              simpa only [hφlevel] using hnegative
            have hnearnegative : ∀ᶠ s in 𝓝 t,
                D =ᶠ[𝓝 (φ s)] {y : Plane | ψ y < ψ a} :=
              hφ.continuousAt.eventually ((hopenGerm _).mem_nhds hnegative')
            filter_upwards [hnearnegative] with s hs hPs
            exact opposite_level_halfSpace_germs_impossible (D := D) (p := φ s) ψ hψ
              (by simpa only [P, hφlevel] using hPs)
              (by simpa only [hφlevel] using hs)
        · have hnearL := hφ.continuousAt.eventually hlocal
          filter_upwards [hnearL] with s hs hPs
          have hPs' : D =ᶠ[𝓝 (φ s)] {y : Plane | ψ (φ s) < ψ y} := by
            simpa only [P, hφlevel] using hPs
          have hsfront := (halfSpace_germ_is_locallyStraight ψ hψ hker hPs').1
          have hsL : φ s ∈ L := hs.mp hsfront
          have hs_eq : φ s = φ t := by
            by_contra hne
            have hdiffL : φ s - φ t ∈ L.direction :=
              L.vsub_mem_direction hsL hxL
            have hdiffker : φ s - φ t ∈ LinearMap.ker ψ.toLinearMap := by
              rw [LinearMap.mem_ker, map_sub]
              change ψ (φ s) - ψ (φ t) = 0
              rw [hφlevel, hφlevel, sub_self]
            have hdiffne : φ s - φ t ≠ 0 := sub_ne_zero.mpr hne
            exact hdir ((eq_span_singleton_of_mem_of_finrank_eq_one hdim hdiffL hdiffne).trans
              (eq_span_singleton_of_mem_of_finrank_eq_one hker hdiffker hdiffne).symm)
          exact hPt (by simpa only [P, hs_eq] using hPs)
      · have hnearNotFront : ∀ᶠ s in 𝓝 t, φ s ∉ frontier D :=
          hφ.continuousAt.eventually (isClosed_frontier.isOpen_compl.mem_nhds hxfront)
        filter_upwards [hnearNotFront] with s hs hPs
        apply hs
        exact (halfSpace_germ_is_locallyStraight (D := D) (p := φ s) ψ hψ hker
          (by simpa only [P, hφlevel] using hPs)).1
    filter_upwards [hnear] with s hs
    exact iff_of_false hs hPt

private theorem all_or_all_not_of_eventually_self (P : ℝ → Prop)
    (hlocal : ∀ t : ℝ, ∀ᶠ s in 𝓝 t, P s ↔ P t) :
    (∀ t, P t) ∨ (∀ t, ¬P t) := by
  let A : Set ℝ := {t | P t}
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    filter_upwards [hlocal t] with s hs
    exact hs.mpr ht
  have hAcopen : IsOpen Aᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    filter_upwards [hlocal t] with s hs
    exact fun h => ht (hs.mp h)
  by_cases hAne : A.Nonempty
  · left
    have hAclosed : IsClosed A := by simpa only [compl_compl] using hAcopen.isClosed_compl
    have hAuniv := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hAne
    intro t
    exact (show t ∈ A by rw [hAuniv]; trivial)
  · right
    intro t ht
    exact hAne ⟨t, ht⟩

private theorem halfSpace_germ_propagates_on_cornerFree_line
    {D : Set Plane} (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (ψ : Plane →L[ℝ] ℝ) (hψ : Function.Surjective ψ)
    (hker : Module.finrank ℝ (LinearMap.ker ψ.toLinearMap) = 1)
    (a v : Plane) (hv : ψ v = 0)
    (hno : ∀ r : ℝ, ¬IsProperVertex D (a + r • v))
    (hseed : D =ᶠ[𝓝 a] {y : Plane | ψ a < ψ y}) :
    ∀ r : ℝ, D =ᶠ[𝓝 (a + r • v)] {y : Plane | ψ a < ψ y} := by
  let P : ℝ → Prop := fun r => D =ᶠ[𝓝 (a + r • v)] {y : Plane | ψ a < ψ y}
  have hlocal : ∀ t : ℝ, ∀ᶠ r in 𝓝 t, P r ↔ P t := fun t =>
    eventually_level_halfSpace_germ_iff_of_not_proper hopen hregular ψ hψ hker
      a v hv t (hno t)
  rcases all_or_all_not_of_eventually_self P hlocal with hall | hnone
  · exact hall
  · exact False.elim (hnone 0 (by simpa only [P, zero_smul, add_zero] using hseed))

private theorem all_halfSpace_germs_straight_frontierLine
    {D : Set Plane} (ψ : Plane →L[ℝ] ℝ) (hψ : Function.Surjective ψ)
    (hker : Module.finrank ℝ (LinearMap.ker ψ.toLinearMap) = 1)
    (a v : Plane) (hv : ψ v = 0) (hvne : v ≠ 0)
    (hall : ∀ r : ℝ, D =ᶠ[𝓝 (a + r • v)] {y : Plane | ψ a < ψ y}) :
    IsStraightFrontierLine D (LinearMap.ker ψ.toLinearMap) a := by
  have hvker : v ∈ LinearMap.ker ψ.toLinearMap := LinearMap.mem_ker.mpr hv
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hker hvker hvne
  have hpoints : ∀ x ∈ a +ᵥ (LinearMap.ker ψ.toLinearMap : Set Plane),
      x ∈ frontier D ∧ BoundaryLocallyStraightAt D x := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.mp hx
    rw [hspan] at hu
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
    apply halfSpace_germ_is_locallyStraight ψ hψ hker
    simpa only [map_add, map_smul, hv, smul_zero, add_zero, vadd_eq_add] using hall r
  refine ⟨fun x hx => (hpoints x hx).1, Set.disjoint_left.mpr ?_⟩
  intro x hx hproper
  exact hproper.2 (hpoints x hx).2

private theorem completeFrontierLine_halfSpace_germs_constant
    {D : Set Plane} {δ : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1)
    (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ) (a : Plane)
    (hfull : IsStraightFrontierLine D δ a) :
    (∀ x ∈ a +ᵥ (δ : Set Plane), D =ᶠ[𝓝 x] {y : Plane | π a < π y}) ∨
      (∀ x ∈ a +ᵥ (δ : Set Plane), D =ᶠ[𝓝 x] {y : Plane | π y < π a}) := by
  have haLine : a ∈ a +ᵥ (δ : Set Plane) :=
    Set.mem_vadd_set.mpr ⟨0, δ.zero_mem, by simp⟩
  have haFront := hfull.1 haLine
  have haNo : ¬IsProperVertex D a := by
    intro haW
    exact Set.disjoint_left.mp hfull.2 haLine haW
  have haStraight : BoundaryLocallyStraightAt D a := by
    by_contra h
    exact haNo ⟨haFront, h⟩
  obtain ⟨L, haL, hL, hLgerm⟩ := haStraight
  have hdir := direction_eq_of_complete_frontier_line_and_straightGerm
    hδ haLine hfull.1 haL hL hLgerm
  have hLset : (L : Set Plane) = a +ᵥ (δ : Set Plane) := by
    rw [affineSubspace_eq_anchor_vadd_direction haL, ← hdir]
  have hlevel (y : Plane) : y ∈ (L : Set Plane) ↔ π y = π a := by
    rw [hLset]
    constructor
    · intro hy
      obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.mp hy
      have hu0 : π u = 0 := LinearMap.mem_ker.mp (hker.symm ▸ hu)
      simp only [vadd_eq_add, map_add, hu0, add_zero]
    · intro hy
      have hu : y - a ∈ δ := by
        rw [← hker, LinearMap.mem_ker]
        change π (y - a) = 0
        rw [map_sub, hy, sub_self]
      exact Set.mem_vadd_set.mpr ⟨y - a, hu, by simp [vadd_eq_add]⟩
  have hg : ∀ᶠ y in 𝓝 a, y ∈ frontier D ↔ π y = π a := by
    filter_upwards [hLgerm] with y hy
    exact hy.trans (hlevel y)
  have hδbot : δ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hδ
    exact Nat.zero_ne_one hδ
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδbot
  have hv0 : π v = 0 := LinearMap.mem_ker.mp (hker.symm ▸ hv)
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hδ hv hvne
  have hno (r : ℝ) : ¬IsProperVertex D (a + r • v) := by
    intro hr
    exact Set.disjoint_left.mp hfull.2
      (Set.mem_vadd_set.mpr ⟨r • v, δ.smul_mem r hv, rfl⟩) hr
  have hdim : Module.finrank ℝ (LinearMap.ker π.toLinearMap) = 1 := by
    rw [hker]; exact hδ
  rcases locallyStraight_level_halfSpace_germ π hopen hregular haFront hg with hpos | hneg
  · have hall := halfSpace_germ_propagates_on_cornerFree_line
      hopen hregular π hπ hdim a v hv0 hno hpos
    left
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.mp hx
    rw [hspan] at hu
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
    exact hall r
  · have hπneg : Function.Surjective (-π) := by
      intro r
      obtain ⟨x, hx⟩ := hπ (-r)
      exact ⟨x, by simpa using congrArg Neg.neg hx⟩
    have hkerneg : LinearMap.ker (-π).toLinearMap = δ := by
      ext x
      simp [← hker, LinearMap.mem_ker]
    have hdimneg : Module.finrank ℝ (LinearMap.ker (-π).toLinearMap) = 1 := by
      rw [hkerneg]; exact hδ
    have hvneg : (-π) v = 0 := by simp [hv0]
    have hseedneg : D =ᶠ[𝓝 a] {y : Plane | (-π) a < (-π) y} := by
      simpa only [ContinuousLinearMap.neg_apply, neg_lt_neg_iff] using hneg
    have hall := halfSpace_germ_propagates_on_cornerFree_line
      hopen hregular (-π) hπneg hdimneg a v hvneg hno hseedneg
    right
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.mp hx
    rw [hspan] at hu
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
    simpa only [vadd_eq_add, ContinuousLinearMap.neg_apply, neg_lt_neg_iff] using hall r

private theorem level_halfSpace_germs_match_on_line
    {D E : Set Plane} (hDopen : IsOpen D) (hEopen : IsOpen E)
    (hDregular : interior (closure D) = D) (hEregular : interior (closure E) = E)
    (hW : properVertices D = properVertices E)
    (hg : ∀ x ∈ properVertices D, D =ᶠ[𝓝 x] E)
    (hf : ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
      ∀ a : Plane, IsStraightFrontierLine D δ a →
        ∀ x ∈ a +ᵥ (δ : Set Plane), D =ᶠ[𝓝 x] E)
    (hb : ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
      ∀ a : Plane, IsStraightFrontierLine E δ a →
        ∀ x ∈ a +ᵥ (δ : Set Plane), E =ᶠ[𝓝 x] D)
    (ψ : Plane →L[ℝ] ℝ) (hψ : Function.Surjective ψ)
    (hker : Module.finrank ℝ (LinearMap.ker ψ.toLinearMap) = 1)
    (a v : Plane) (hv : ψ v = 0) (hvne : v ≠ 0) :
    ∀ r : ℝ, (D =ᶠ[𝓝 (a + r • v)] {y : Plane | ψ a < ψ y}) ↔
      (E =ᶠ[𝓝 (a + r • v)] {y : Plane | ψ a < ψ y}) := by
  let P : ℝ → Prop := fun r => D =ᶠ[𝓝 (a + r • v)] {y : Plane | ψ a < ψ y}
  let Q : ℝ → Prop := fun r => E =ᶠ[𝓝 (a + r • v)] {y : Plane | ψ a < ψ y}
  have hlocal : ∀ t : ℝ, ∀ᶠ s in 𝓝 t, (P s ↔ Q s) ↔ (P t ↔ Q t) := by
    intro t
    by_cases htW : a + t • v ∈ properVertices D
    · have hDE := hg _ htW
      have hopenGerm : IsOpen {x : Plane | D =ᶠ[𝓝 x] E} :=
        isOpen_setOfPred_eventually_nhds
      have hφ : Continuous (fun r : ℝ => a + r • v) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hnear := hφ.continuousAt.eventually (hopenGerm.mem_nhds hDE)
      have htmatch : P t ↔ Q t := ⟨fun h => hDE.symm.trans h, fun h => hDE.trans h⟩
      filter_upwards [hnear] with s hs
      exact iff_of_true ⟨fun h => hs.symm.trans h, fun h => hs.trans h⟩ htmatch
    · have htWE : ¬IsProperVertex E (a + t • v) := by
        intro hproper
        apply htW
        rw [hW]
        exact hproper
      have hP := eventually_level_halfSpace_germ_iff_of_not_proper
        hDopen hDregular ψ hψ hker a v hv t htW
      have hQ := eventually_level_halfSpace_germ_iff_of_not_proper
        hEopen hEregular ψ hψ hker a v hv t htWE
      filter_upwards [hP, hQ] with s hsP hsQ
      exact iff_congr hsP hsQ
  rcases all_or_all_not_of_eventually_self (fun r => P r ↔ Q r) hlocal with hall | hnone
  · exact hall
  · exfalso
    have hnoD (r : ℝ) : ¬IsProperVertex D (a + r • v) := by
      intro hproper
      have hDE := hg _ hproper
      exact hnone r ⟨fun h => hDE.symm.trans h, fun h => hDE.trans h⟩
    have hnoE (r : ℝ) : ¬IsProperVertex E (a + r • v) := by
      intro hproper
      apply hnoD r
      change a + r • v ∈ properVertices D
      rw [hW]
      exact hproper
    have hPlocal : ∀ t : ℝ, ∀ᶠ s in 𝓝 t, P s ↔ P t := fun t =>
      eventually_level_halfSpace_germ_iff_of_not_proper hDopen hDregular
        ψ hψ hker a v hv t (hnoD t)
    have hQlocal : ∀ t : ℝ, ∀ᶠ s in 𝓝 t, Q s ↔ Q t := fun t =>
      eventually_level_halfSpace_germ_iff_of_not_proper hEopen hEregular
        ψ hψ hker a v hv t (hnoE t)
    rcases all_or_all_not_of_eventually_self P hPlocal with hP | hnP <;>
      rcases all_or_all_not_of_eventually_self Q hQlocal with hQ | hnQ
    · exact hnone 0 (iff_of_true (hP 0) (hQ 0))
    · have hfull := all_halfSpace_germs_straight_frontierLine ψ hψ hker a v hv hvne hP
      have hDE := hf _ hker a hfull a
        (Set.mem_vadd_set.mpr ⟨0, (LinearMap.ker ψ.toLinearMap).zero_mem, by simp⟩)
      have hPzero : D =ᶠ[𝓝 a] {y : Plane | ψ a < ψ y} := by simpa [P] using hP 0
      exact hnQ 0 (by simpa [Q] using hDE.symm.trans hPzero)
    · have hfull := all_halfSpace_germs_straight_frontierLine ψ hψ hker a v hv hvne hQ
      have hED := hb _ hker a hfull a
        (Set.mem_vadd_set.mpr ⟨0, (LinearMap.ker ψ.toLinearMap).zero_mem, by simp⟩)
      have hQzero : E =ᶠ[𝓝 a] {y : Plane | ψ a < ψ y} := by simpa [Q] using hQ 0
      exact hnP 0 (by simpa [P] using hED.symm.trans hQzero)
    · exact hnone 0 (iff_of_false (hnP 0) (hnQ 0))

private theorem affineLine_surjective_level_coordinate
    {L : AffineSubspace ℝ Plane} {a : Plane} (ha : a ∈ L)
    (hL : Module.finrank ℝ L.direction = 1) :
    ∃ ψ : Plane →L[ℝ] ℝ, Function.Surjective ψ ∧
      LinearMap.ker ψ.toLinearMap = L.direction ∧
      ∀ y : Plane, y ∈ L ↔ ψ y = ψ a := by
  obtain ⟨ψ, hψ⟩ := Tiling.AffineSubspace.exists_levelSet_coordinate L a ha hL
  have hker : LinearMap.ker ψ.toLinearMap = L.direction := by
    ext v
    constructor
    · intro hv
      have hv0 : ψ v = 0 := LinearMap.mem_ker.mp hv
      have hva : v +ᵥ a ∈ L := (hψ _).mpr (by
        simp only [vadd_eq_add, map_add, hv0, zero_add])
      simpa only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right] using
        L.vsub_mem_direction hva ha
    · intro hv
      have hva := L.vadd_mem_of_mem_direction hv ha
      have heq := (hψ _).mp hva
      apply LinearMap.mem_ker.mpr
      change ψ v = 0
      simp only [vadd_eq_add, map_add] at heq
      linarith
  have hψne : ψ ≠ 0 := by
    intro hzero
    have hkerTop : LinearMap.ker ψ.toLinearMap = ⊤ := by
      ext v
      simp [LinearMap.mem_ker, hzero]
    have hdim : Module.finrank ℝ (LinearMap.ker ψ.toLinearMap) = 1 := by
      rw [hker]; exact hL
    rw [hkerTop, finrank_top, Complex.finrank_real_complex] at hdim
    norm_num at hdim
  have hex : ∃ e : Plane, ψ e ≠ 0 := by
    by_contra h
    push_neg at h
    apply hψne
    ext e
    exact h e
  obtain ⟨e, he⟩ := hex
  have hsurj : Function.Surjective ψ := by
    intro r
    refine ⟨(r / ψ e) • e, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ r he]
  exact ⟨ψ, hsurj, hker, hψ⟩

private theorem frontier_germs_match_of_corners_and_fullLines
    {D E : Set Plane} (hDopen : IsOpen D) (hEopen : IsOpen E)
    (hDregular : interior (closure D) = D) (hEregular : interior (closure E) = E)
    (hW : properVertices D = properVertices E)
    (hg : ∀ x ∈ properVertices D, D =ᶠ[𝓝 x] E)
    (hf : ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
      ∀ a : Plane, IsStraightFrontierLine D δ a →
        ∀ x ∈ a +ᵥ (δ : Set Plane), D =ᶠ[𝓝 x] E)
    (hb : ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
      ∀ a : Plane, IsStraightFrontierLine E δ a →
        ∀ x ∈ a +ᵥ (δ : Set Plane), E =ᶠ[𝓝 x] D) :
    ∀ p ∈ frontier D, D =ᶠ[𝓝 p] E := by
  intro p hp
  by_cases hpW : p ∈ properVertices D
  · exact hg p hpW
  · obtain ⟨L, hpL, hLdim, hLgerm⟩ := by
      have hpstraight : BoundaryLocallyStraightAt D p := by
        by_contra h
        exact hpW ⟨hp, h⟩
      exact hpstraight
    obtain ⟨ψ, hψ, hker, hlevel⟩ := affineLine_surjective_level_coordinate hpL hLdim
    have hkerdim : Module.finrank ℝ (LinearMap.ker ψ.toLinearMap) = 1 := by
      rw [hker]; exact hLdim
    have hkerbot : LinearMap.ker ψ.toLinearMap ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hkerdim
      norm_num at hkerdim
    obtain ⟨v, hvker, hvne⟩ := (Submodule.ne_bot_iff _).mp hkerbot
    have hv : ψ v = 0 := LinearMap.mem_ker.mp hvker
    have hpLevel : ∀ᶠ y in 𝓝 p, y ∈ frontier D ↔ ψ y = ψ p := by
      filter_upwards [hLgerm] with y hy
      exact hy.trans (hlevel y)
    rcases locallyStraight_level_halfSpace_germ ψ hDopen hDregular hp hpLevel
      with hpositive | hnegative
    · have hmatch := level_halfSpace_germs_match_on_line hDopen hEopen hDregular
        hEregular hW hg hf hb ψ hψ hkerdim p v hv hvne 0
      have hEpositive : E =ᶠ[𝓝 p] {y : Plane | ψ p < ψ y} :=
        (show (D =ᶠ[𝓝 p] {y : Plane | ψ p < ψ y}) ↔
          (E =ᶠ[𝓝 p] {y : Plane | ψ p < ψ y}) from
          by simpa only [zero_smul, add_zero] using hmatch).mp hpositive
      exact hpositive.trans hEpositive.symm
    · have hψneg : Function.Surjective (-ψ) := by
        intro r
        obtain ⟨x, hx⟩ := hψ (-r)
        exact ⟨x, by simpa using congrArg Neg.neg hx⟩
      have hkerneg : LinearMap.ker (-ψ).toLinearMap = LinearMap.ker ψ.toLinearMap := by
        ext x
        simp [LinearMap.mem_ker]
      have hkerdimneg : Module.finrank ℝ (LinearMap.ker (-ψ).toLinearMap) = 1 := by
        rw [hkerneg]; exact hkerdim
      have hvneg : (-ψ) v = 0 := by simp [hv]
      have hDnegative : D =ᶠ[𝓝 p] {y : Plane | (-ψ) p < (-ψ) y} := by
        simpa only [neg_apply, neg_lt_neg_iff] using hnegative
      have hmatch := level_halfSpace_germs_match_on_line hDopen hEopen hDregular
        hEregular hW hg hf hb (-ψ) hψneg hkerdimneg p v hvneg hvne 0
      have hEnegative : E =ᶠ[𝓝 p] {y : Plane | (-ψ) p < (-ψ) y} :=
        (show (D =ᶠ[𝓝 p] {y : Plane | (-ψ) p < (-ψ) y}) ↔
          (E =ᶠ[𝓝 p] {y : Plane | (-ψ) p < (-ψ) y}) from
          by simpa only [zero_smul, add_zero] using hmatch).mp hDnegative
      exact hDnegative.trans hEnegative.symm

private theorem properVertices_isClosed (D : Set Plane) :
    IsClosed (properVertices D) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  change ¬IsProperVertex D x at hx
  by_cases hxfront : x ∈ frontier D
  · have hxstraight : BoundaryLocallyStraightAt D x := by
      by_contra h
      exact hx ⟨hxfront, h⟩
    obtain ⟨L, hxL, hdim, hlocal⟩ := hxstraight
    obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hlocal
    apply Filter.mem_of_superset (hUopen.mem_nhds hxU)
    intro y hyU
    change ¬IsProperVertex D y
    rintro ⟨hyfront, hynotstraight⟩
    apply hynotstraight
    refine ⟨L, (hUsub hyU).mp hyfront, hdim, ?_⟩
    exact Filter.mem_of_superset (hUopen.mem_nhds hyU) hUsub
  · apply Filter.mem_of_superset (isClosed_frontier.isOpen_compl.mem_nhds hxfront)
    intro y hy
    change ¬IsProperVertex D y
    exact fun h => hy h.1

private theorem sets_eq_of_mutual_frontier_germs
    {D E : Set Plane}
    (hDne : D.Nonempty) (hEne : E.Nonempty)
    (hDfront : ∀ p ∈ frontier D, D =ᶠ[𝓝 p] E)
    (hEfront : ∀ p ∈ frontier E, E =ᶠ[𝓝 p] D) :
    D = E := by
  classical
  let A : Set Plane := {p | D =ᶠ[𝓝 p] E}
  have hAopen : IsOpen A := by
    simp only [A, Filter.eventuallyEq_set]
    exact isOpen_setOfPred_eventually_nhds
  have hAclosed : IsClosed A := by
    apply isClosed_of_closure_subset
    intro x hx
    by_cases hxD : x ∈ frontier D
    · exact hDfront x hxD
    by_cases hxE : x ∈ frontier E
    · exact (hEfront x hxE).symm
    have hDstable : ∀ᶠ y in 𝓝 x, (y ∈ D ↔ x ∈ D) := by
      have hx' : x ∈ interior D ∪ interior Dᶜ := by
        have hxnot : x ∈ (frontier D)ᶜ := hxD
        rw [compl_frontier_eq_union_interior] at hxnot
        exact hxnot
      rcases hx' with hxD' | hxD'
      · filter_upwards [isOpen_interior.mem_nhds hxD'] with y hy
        exact iff_of_true (interior_subset hy) (interior_subset hxD')
      · filter_upwards [isOpen_interior.mem_nhds hxD'] with y hy
        exact iff_of_false (interior_subset hy) (interior_subset hxD')
    have hEstable : ∀ᶠ y in 𝓝 x, (y ∈ E ↔ x ∈ E) := by
      have hx' : x ∈ interior E ∪ interior Eᶜ := by
        have hxnot : x ∈ (frontier E)ᶜ := hxE
        rw [compl_frontier_eq_union_interior] at hxnot
        exact hxnot
      rcases hx' with hxE' | hxE'
      · filter_upwards [isOpen_interior.mem_nhds hxE'] with y hy
        exact iff_of_true (interior_subset hy) (interior_subset hxE')
      · filter_upwards [isOpen_interior.mem_nhds hxE'] with y hy
        exact iff_of_false (interior_subset hy) (interior_subset hxE')
    let N : Set Plane := {y | (y ∈ D ↔ x ∈ D) ∧ (y ∈ E ↔ x ∈ E)}
    have hN : N ∈ 𝓝 x := hDstable.and hEstable
    obtain ⟨q, hq⟩ := (mem_closure_iff_nhds.mp hx) N hN
    have hqN : q ∈ N := hq.1
    have hqA : q ∈ A := hq.2
    have hqD : q ∈ D ↔ x ∈ D := hqN.1
    have hqE : q ∈ E ↔ x ∈ E := hqN.2
    have hqAevent : ∀ᶠ y in 𝓝 q, (y ∈ D ↔ y ∈ E) := by
      change D =ᶠ[𝓝 q] E at hqA
      exact Filter.eventuallyEq_set.mp hqA
    have hqDE : q ∈ D ↔ q ∈ E :=
      Filter.Eventually.self_of_nhds (x := q)
        (p := fun y : Plane => y ∈ D ↔ y ∈ E) hqAevent
    have hxDE : x ∈ D ↔ x ∈ E := hqD.symm.trans (hqDE.trans hqE)
    have hAatx : ∀ᶠ y in 𝓝 x, (y ∈ D ↔ y ∈ E) := by
      filter_upwards [hDstable, hEstable] with y hyD hyE
      exact hyD.trans (hxDE.trans hyE.symm)
    change D =ᶠ[𝓝 x] E
    exact Filter.eventuallyEq_set.mpr hAatx
  have hAne : A.Nonempty := by
    by_cases hDfrontne : (frontier D).Nonempty
    · obtain ⟨p, hp⟩ := hDfrontne
      exact ⟨p, hDfront p hp⟩
    · have hDfrontempty : frontier D = ∅ := Set.not_nonempty_iff_eq_empty.mp hDfrontne
      have hDclopen : IsClopen D := isClopen_iff_frontier_eq_empty.mpr hDfrontempty
      have hDuniv : D = Set.univ := IsClopen.eq_univ hDclopen hDne
      have hEfrontempty : frontier E = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hpE : ∀ᶠ y in 𝓝 p, y ∈ E := by
          filter_upwards [hEfront p hp] with y hy
          have hyD : y ∈ D := by rw [hDuniv]; simp
          exact hy.mpr hyD
        have hpinterior : p ∈ interior E := mem_interior_iff_mem_nhds.mpr hpE
        exact (Set.disjoint_left.mp disjoint_interior_frontier) hpinterior hp
      have hEclopen : IsClopen E := isClopen_iff_frontier_eq_empty.mpr hEfrontempty
      have hEuniv : E = Set.univ := IsClopen.eq_univ hEclopen hEne
      exact ⟨0, by simp [A, hDuniv, hEuniv]⟩
  have hAuniv : A = Set.univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hAne
  ext x
  have hxA : x ∈ A := by rw [hAuniv]; trivial
  have hxAevent : ∀ᶠ y in 𝓝 x, (y ∈ D ↔ y ∈ E) := by
    change D =ᶠ[𝓝 x] E at hxA
    exact Filter.eventuallyEq_set.mp hxA
  have hxEq : x ∈ D ↔ x ∈ E :=
    Filter.Eventually.self_of_nhds (x := x)
      (p := fun y : Plane => y ∈ D ↔ y ∈ E) hxAevent
  exact hxEq

private theorem straightFrontierLine_vadd
    {D : Set Plane} {δ : Submodule ℝ Plane} {a : Plane} (u : Plane)
    (hline : IsStraightFrontierLine D δ a) :
    IsStraightFrontierLine (u +ᵥ D) δ (a + u) := by
  have hfrontier : frontier (u +ᵥ D) = u +ᵥ frontier D := by
    simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
      ((Homeomorph.addLeft u).image_frontier D).symm
  have hpoint (x : Plane) (hx : x ∈ (a + u) +ᵥ (δ : Set Plane)) :
      -u +ᵥ x ∈ a +ᵥ (δ : Set Plane) := by
    obtain ⟨v, hv, rfl⟩ := Set.mem_vadd_set.mp hx
    refine Set.mem_vadd_set.mpr ⟨v, hv, ?_⟩
    simp only [vadd_eq_add]
    abel
  refine ⟨?_, Set.disjoint_left.mpr ?_⟩
  · intro x hx
    rw [hfrontier, Set.mem_vadd_set_iff_neg_vadd_mem]
    exact hline.1 (hpoint x hx)
  · intro x hx hxW
    rw [properVertices_vadd, Set.mem_vadd_set_iff_neg_vadd_mem] at hxW
    exact Set.disjoint_left.mp hline.2 (hpoint x hx) hxW

/-- Missing empty/full status in the source is repaired by nonempty subfamilies. -/
theorem properVertices_and_straightLines_determine_translate
    {K : PolygonalRegion} {S U : Set Plane} (hS : S.Nonempty) (hU : U.Nonempty)
    (hpS : IsPacking K.prototileFamily (K.placements S))
    (hpU : IsPacking K.prototileFamily (K.placements U)) (z : Plane)
    (hW : z +ᵥ properVertices (regularSupport K S) =
      properVertices (regularSupport K U))
    (hg : ∀ v ∈ properVertices (regularSupport K S),
      SameGermAt (regularSupport K S) v (regularSupport K U) (v + z))
    (hf : ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
      ∀ a : Plane, IsStraightFrontierLine (regularSupport K S) δ a →
        IsStraightFrontierLine (regularSupport K U) δ (a + z) ∧
          ∀ x ∈ a +ᵥ (δ : Set Plane),
            SameGermAt (regularSupport K S) x (regularSupport K U) (x + z))
    (hb : ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
      ∀ a : Plane, IsStraightFrontierLine (regularSupport K U) δ a →
        IsStraightFrontierLine (regularSupport K S) δ (a - z) ∧
          ∀ x ∈ a +ᵥ (δ : Set Plane),
            SameGermAt (regularSupport K U) x (regularSupport K S) (x - z)) :
    z +ᵥ regularSupport K S = regularSupport K U := by
  let D := regularSupport K S
  let E := (-z) +ᵥ regularSupport K U
  have hDopen : IsOpen D := (regularSupport_isRegularOpen K S).1
  have hDregular : interior (closure D) = D := (regularSupport_isRegularOpen K S).2
  have hEopen : IsOpen E := (regularSupport_isRegularOpen K U).1.vadd (-z)
  have hEregular : interior (closure E) = E := by
    dsimp only [E]
    rw [closure_vadd, interior_vadd, (regularSupport_isRegularOpen K U).2]
  have hW0 : properVertices D = properVertices E := by
    dsimp only [D, E]
    rw [properVertices_vadd, ← hW]
    simp only [vadd_vadd, neg_add_cancel, zero_vadd]
  have hG0 : ∀ x ∈ properVertices D, D =ᶠ[𝓝 x] E := by
    intro x hx
    have h := hg x hx
    change D =ᶠ[𝓝 x] ((x - (x + z)) +ᵥ regularSupport K U) at h
    simpa only [show x - (x + z) = -z by abel] using h
  have hF0 : ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
      ∀ a : Plane, IsStraightFrontierLine D δ a →
        ∀ x ∈ a +ᵥ (δ : Set Plane), D =ᶠ[𝓝 x] E := by
    intro δ hδ a ha x hx
    have h := (hf δ hδ a ha).2 x hx
    change D =ᶠ[𝓝 x] ((x - (x + z)) +ᵥ regularSupport K U) at h
    simpa only [show x - (x + z) = -z by abel] using h
  have hB0 : ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
      ∀ a : Plane, IsStraightFrontierLine E δ a →
        ∀ x ∈ a +ᵥ (δ : Set Plane), E =ᶠ[𝓝 x] D := by
    intro δ hδ a ha x hx
    have haU : IsStraightFrontierLine (regularSupport K U) δ (a + z) := by
      have h := straightFrontierLine_vadd z ha
      simpa only [E, vadd_vadd, add_neg_cancel, zero_vadd] using h
    have hxU : x + z ∈ (a + z) +ᵥ (δ : Set Plane) := by
      obtain ⟨v, hv, hxeq⟩ := Set.mem_vadd_set.mp hx
      refine Set.mem_vadd_set.mpr ⟨v, hv, ?_⟩
      rw [← hxeq]
      simp only [vadd_eq_add]
      abel
    have h := (hb δ hδ (a + z) haU).2 (x + z) hxU
    have h' : regularSupport K U =ᶠ[𝓝 (x + z)] z +ᵥ D := by
      change regularSupport K U =ᶠ[𝓝 (x + z)]
        (((x + z) - ((x + z) - z)) +ᵥ D) at h
      simpa only [show (x + z) - ((x + z) - z) = z by abel] using h
    have hcont : Continuous (fun y : Plane => y + z) := continuous_id.add continuous_const
    filter_upwards [hcont.continuousAt.eventually h'] with y hy
    apply propext
    change y ∈ (-z) +ᵥ regularSupport K U ↔ y ∈ D
    have hyiff : y + z ∈ regularSupport K U ↔ y + z ∈ z +ᵥ D := Iff.of_eq hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hyiff
    have hcancel : -z +ᵥ (y + z) = y := by simp only [vadd_eq_add]; abel
    rw [hcancel] at hyiff
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [neg_neg, vadd_eq_add, add_comm] using hyiff
  have hDfront : ∀ p ∈ frontier D, D =ᶠ[𝓝 p] E :=
    frontier_germs_match_of_corners_and_fullLines hDopen hEopen hDregular hEregular
      hW0 hG0 hF0 hB0
  have hEfront : ∀ p ∈ frontier E, E =ᶠ[𝓝 p] D :=
    frontier_germs_match_of_corners_and_fullLines hEopen hDopen hEregular hDregular
      hW0.symm (fun x hx => (hG0 x (hW0.symm ▸ hx)).symm) hB0 hF0
  have hcarrierNe (V : Set Plane) (hV : V.Nonempty) : (regularSupport K V).Nonempty := by
    obtain ⟨s, hs⟩ := hV
    obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hopen : IsOpen (openUnion K V) :=
      isOpen_iUnion (fun t : V => isOpen_interior.vadd (t : Plane))
    have hunion : openUnion K V ⊆ regularSupport K V :=
      hopen.subset_interior_iff.mpr subset_closure
    refine ⟨s + k, hunion (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩)⟩
    exact Set.mem_vadd_set.mpr ⟨k, hk, rfl⟩
  have hDne : D.Nonempty := hcarrierNe S hS
  have hEne : E.Nonempty := by
    obtain ⟨u, hu⟩ := hcarrierNe U hU
    exact ⟨(-z) +ᵥ u, Set.mem_vadd_set.mpr ⟨u, hu, rfl⟩⟩
  have hDE : D = E := sets_eq_of_mutual_frontier_germs hDne hEne hDfront hEfront
  change z +ᵥ D = regularSupport K U
  rw [hDE]
  simp only [E, vadd_vadd, add_neg_cancel, zero_vadd]

private theorem locallyFinite_union_eventually_subset_germ
    {ι : Type*} {F : ι → Set Plane} (hloc : LocallyFinite F)
    (hclosed : ∀ i, IsClosed (F i)) (p : Plane) (A : Set Plane)
    (hg : ∀ i, p ∈ F i → ∀ᶠ y in 𝓝 p, y ∈ F i → y ∈ A) :
    ∀ᶠ y in 𝓝 p, y ∈ ⋃ i, F i → y ∈ A := by
  have hfinite := hloc.point_finite p
  have hall : ∀ᶠ y in 𝓝 p, ∀ i ∈ {i | p ∈ F i}, y ∈ F i → y ∈ A :=
    hfinite.eventually_all.mpr hg
  filter_upwards [hloc.eventually_subset hclosed p, hall] with y hy hyall hyunion
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyunion
  exact hyall i (hy hi) hi

private theorem placed_supports_locallyFinite
    {K : PolygonalRegion} {S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements S)) :
    LocallyFinite (fun s : S => (s : Plane) +ᵥ K.support) := by
  let P : PolygonalProtoTiling Unit := {
    prototiles := K.prototileFamily
    placements := K.placements S
    isPolygonal := fun _ => K.isPolygonal }
  let toPlacement : S → P.placements := fun s => ⟨(s, ()), s.2⟩
  have htoPlacement : Function.Injective toPlacement := by
    intro s t hst
    exact Subtype.ext (congrArg (fun i : P.placements => i.1.1) hst)
  exact (P.locallyFinite_placedTile hp).comp_injective htoPlacement

private theorem placed_support_union_closed
    {K : PolygonalRegion} {S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements S)) :
    IsClosed (⋃ s : S, (s : Plane) +ᵥ K.support) := by
  let P : PolygonalProtoTiling Unit := {
    prototiles := K.prototileFamily
    placements := K.placements S
    isPolygonal := fun _ => K.isPolygonal }
  let toPlacement : S → P.placements := fun s => ⟨(s, ()), s.2⟩
  have htoPlacement : Function.Injective toPlacement := by
    intro s t hst
    exact Subtype.ext (congrArg (fun i : P.placements => i.1.1) hst)
  have hloc : LocallyFinite (fun s : S => (s : Plane) +ᵥ K.support) :=
    (P.locallyFinite_placedTile hp).comp_injective htoPlacement
  exact hloc.isClosed_iUnion fun s => by
    simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
      (Homeomorph.addLeft (s : Plane)).isClosed_image.mpr K.isPolygonal.isClosed

private theorem placed_support_union_subset_closure_regularSupport
    {K : PolygonalRegion} {S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements S)) :
    (⋃ s : S, (s : Plane) +ᵥ K.support) ⊆ closure (regularSupport K S) := by
  have hopen : IsOpen (openUnion K S) :=
    isOpen_iUnion (fun s : S => isOpen_interior.vadd (s : Plane))
  have hinc : openUnion K S ⊆ regularSupport K S :=
    hopen.subset_interior_iff.mpr subset_closure
  rw [← closure_openUnion_eq_iUnion_support hp]
  exact closure_mono hinc

private theorem closure_regularSupport_eq_placed_support_union
    {K : PolygonalRegion} {S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements S)) :
    closure (regularSupport K S) = ⋃ s : S, (s : Plane) +ᵥ K.support := by
  have hclosed := placed_support_union_closed hp
  have hopenSub : openUnion K S ⊆ ⋃ s : S, (s : Plane) +ᵥ K.support := by
    intro x hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨s, vadd_set_mono interior_subset hs⟩
  have hDsub : regularSupport K S ⊆ ⋃ s : S, (s : Plane) +ᵥ K.support :=
    interior_subset.trans (closure_minimal hopenSub hclosed)
  exact Set.Subset.antisymm (closure_minimal hDsub hclosed)
    (placed_support_union_subset_closure_regularSupport hp)

private theorem packing_centres_countable
    {K : PolygonalRegion} {S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements S)) : Countable S := by
  have hloc := placed_supports_locallyFinite hp
  have hne (s : S) : ((s : Plane) +ᵥ K.support).Nonempty := by
    obtain ⟨k, hk⟩ := K.nonempty
    exact ⟨(s : Plane) + k, Set.mem_vadd_set.mpr ⟨k, hk, rfl⟩⟩
  exact Set.countable_univ_iff.mp (hloc.countable_univ hne)

private theorem scalar_carrier_has_unique_placed_support_owner_ae
    {K : PolygonalRegion} {S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements S)) (φ : ℝ → Plane)
    (hfinite : ∀ s : S, {r : ℝ | φ r ∈ frontier ((s : Plane) +ᵥ K.support)}.Finite) :
    ∀ᵐ r : ℝ ∂volume,
      (φ r ∈ regularSupport K S ↔ ∃ s : S, φ r ∈ (s : Plane) +ᵥ K.support) ∧
        ∀ s t : S, φ r ∈ (s : Plane) +ᵥ K.support →
          φ r ∈ (t : Plane) +ᵥ K.support → s = t := by
  letI : Countable S := packing_centres_countable hp
  let E : Set ℝ := ⋃ s : S, {r : ℝ | φ r ∈ frontier ((s : Plane) +ᵥ K.support)}
  have hEcount : E.Countable := Set.countable_iUnion fun s => (hfinite s).countable
  have hopen : IsOpen (openUnion K S) :=
    isOpen_iUnion (fun s : S => isOpen_interior.vadd (s : Plane))
  have hOD : openUnion K S ⊆ regularSupport K S :=
    hopen.subset_interior_iff.mpr subset_closure
  filter_upwards [hEcount.ae_notMem volume] with r hr
  have hint (s : S) (hs : φ r ∈ (s : Plane) +ᵥ K.support) :
      φ r ∈ interior ((s : Plane) +ᵥ K.support) := by
    by_contra hnot
    apply hr
    apply Set.mem_iUnion.mpr
    refine ⟨s, ?_⟩
    change φ r ∈ frontier ((s : Plane) +ᵥ K.support)
    rw [(K.isPolygonal.vadd (s : Plane)).isClosed.frontier_eq]
    exact ⟨hs, hnot⟩
  have hopenTile (s : S) (hs : φ r ∈ (s : Plane) +ᵥ K.support) :
      φ r ∈ (s : Plane) +ᵥ K.openCarrier := by
    simpa only [interior_vadd, PolygonalRegion.openCarrier] using hint s hs
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hrD
    have hrC : φ r ∈ ⋃ s : S, (s : Plane) +ᵥ K.support := by
      rw [← closure_regularSupport_eq_placed_support_union hp]
      exact subset_closure hrD
    exact Set.mem_iUnion.mp hrC
  · rintro ⟨s, hs⟩
    exact hOD (Set.mem_iUnion.mpr ⟨s, hopenTile s hs⟩)
  · intro s t hs ht
    by_contra hne
    have hplane : (s : Plane) ≠ (t : Plane) := fun h => hne (Subtype.ext h)
    have hd := (isPacking_iff_openCarrier_disjoint K S).mp hp s.2 t.2 hplane
    exact Set.disjoint_left.mp hd (hopenTile s hs) (hopenTile t ht)

private theorem completeFrontierLine_support_halfSpace_germs
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ) (a : Plane)
    (hfull : IsStraightFrontierLine (regularSupport K S) δ a) :
    (∀ x : Plane, π x = π a → ∀ᶠ y in 𝓝 x,
      y ∈ ⋃ s : S, (s : Plane) +ᵥ K.support → π a ≤ π y) ∨
      (∀ x : Plane, π x = π a → ∀ᶠ y in 𝓝 x,
        y ∈ ⋃ s : S, (s : Plane) +ᵥ K.support → π y ≤ π a) := by
  have hxline (x : Plane) (hx : π x = π a) : x ∈ a +ᵥ (δ : Set Plane) := by
    have hu : x - a ∈ δ := by
      rw [← hker, LinearMap.mem_ker]
      change π (x - a) = 0
      rw [map_sub, hx, sub_self]
    exact Set.mem_vadd_set.mpr ⟨x - a, hu, by simp [vadd_eq_add]⟩
  have hinc := placed_support_union_subset_closure_regularSupport hp
  rcases completeFrontierLine_halfSpace_germs_constant hδ
    (regularSupport_isRegularOpen K S).1 (regularSupport_isRegularOpen K S).2
    π hπ hker a hfull with hpos | hneg
  · left
    intro x hx
    have hg := eventuallyEq_closure (hpos x (hxline x hx))
    change closure (regularSupport K S) =ᶠ[𝓝 x] closure (π ⁻¹' Set.Ioi (π a)) at hg
    rw [π.closure_preimage hπ, closure_Ioi] at hg
    filter_upwards [hg] with y hy hyunion
    exact (Iff.of_eq hy).mp (hinc hyunion)
  · right
    intro x hx
    have hg := eventuallyEq_closure (hneg x (hxline x hx))
    change closure (regularSupport K S) =ᶠ[𝓝 x] closure (π ⁻¹' Set.Iio (π a)) at hg
    rw [π.closure_preimage hπ, closure_Iio] at hg
    filter_upwards [hg] with y hy hyunion
    exact (Iff.of_eq hy).mp (hinc hyunion)

private theorem completeFrontierLine_closedCarrier_vacant_side_germs
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ) (a : Plane)
    (hfull : IsStraightFrontierLine (regularSupport K S) δ a) :
    (∀ x : Plane, π x = π a → ∃ r : ℝ, 0 < r ∧
      Metric.ball x r ∩ {y | π y < π x} ⊆ interior ((closure (regularSupport K S))ᶜ)) ∨
      (∀ x : Plane, π x = π a → ∃ r : ℝ, 0 < r ∧
        Metric.ball x r ∩ {y | π x < π y} ⊆ interior ((closure (regularSupport K S))ᶜ)) := by
  rcases completeFrontierLine_support_halfSpace_germs hδ hp π hπ hker a hfull with hpos | hneg
  · left
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hpos x hx)
    refine ⟨r, hr, ?_⟩
    rintro y ⟨hyball, hylt⟩
    rw [isClosed_closure.isOpen_compl.interior_eq]
    intro hyC
    rw [closure_regularSupport_eq_placed_support_union hp] at hyC
    have hle := hball (Metric.mem_ball.mp hyball) hyC
    rw [← hx] at hle
    exact (not_lt_of_ge hle) hylt
  · right
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hneg x hx)
    refine ⟨r, hr, ?_⟩
    rintro y ⟨hyball, hylt⟩
    rw [isClosed_closure.isOpen_compl.interior_eq]
    intro hyC
    rw [closure_regularSupport_eq_placed_support_union hp] at hyC
    have hle := hball (Metric.mem_ball.mp hyball) hyC
    rw [← hx] at hle
    exact (not_lt_of_ge hle) hylt

private theorem frontier_of_closure_and_one_sided_germ
    {D : Set Plane} {p : Plane} (π : Plane →L[ℝ] ℝ)
    (hπ : Function.Surjective π) (hp : p ∈ closure D)
    (hside : ∀ᶠ y in 𝓝 p, y ∈ D → π p ≤ π y) : p ∈ frontier D := by
  rw [frontier]
  refine ⟨hp, ?_⟩
  intro hpint
  have hDnear : ∀ᶠ y in 𝓝 p, y ∈ D :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hpint) interior_subset
  have hbelow : p ∈ closure {y : Plane | π y < π p} := by
    change p ∈ closure (π ⁻¹' Set.Iio (π p))
    rw [π.closure_preimage hπ, closure_Iio]
    exact (le_refl (π p) : π p ≤ π p)
  obtain ⟨y, hybelow, hyD, hyle⟩ :=
    ((mem_closure_iff_frequently.mp hbelow).and_eventually (hDnear.and hside)).exists
  exact (not_lt_of_ge (hyle hyD)) hybelow

private theorem smooth_frontier_level_germ_of_one_sided_closed_germ
    {D : Set Plane} {δ : Submodule ℝ Plane} {p : Plane}
    (hδ : Module.finrank ℝ δ = 1) (π : Plane →L[ℝ] ℝ)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hsmooth : BoundaryLocallyStraightAt D p)
    (hside : ∀ᶠ y in 𝓝 p, y ∈ closure D → π p ≤ π y) :
    ∀ᶠ y in 𝓝 p, y ∈ frontier D ↔ π y = π p := by
  obtain ⟨L, hpL, hLdim, hg⟩ := hsmooth
  have hforbid (w : Plane) (hwL : w ∈ L.direction) (hwπ : π w < 0) : False := by
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hg.and hside)
    let t := r / (2 * (‖w‖ + 1))
    have ht : 0 < t := div_pos hr (by positivity)
    have hdist : dist (p + t • w) p < r := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      calc
        t * ‖w‖ < t * (‖w‖ + 1) := mul_lt_mul_of_pos_left (by linarith) ht
        _ = r / 2 := by dsimp only [t]; field_simp
        _ < r := by linarith
    have hpointL : p + t • w ∈ L := by
      simpa only [vadd_eq_add, add_comm] using
        L.vadd_mem_of_mem_direction (L.direction.smul_mem t hwL) hpL
    have hfront := (hball hdist).1.mpr hpointL
    have hle := (hball hdist).2 (frontier_subset_closure hfront)
    rw [map_add, map_smul, smul_eq_mul] at hle
    have hneg : t * π w < 0 := mul_neg_of_pos_of_neg ht hwπ
    linarith
  have hLker : L.direction ≤ LinearMap.ker π.toLinearMap := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    change π v = 0
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact hforbid v hv hneg
    · exact hforbid (-v) (L.direction.neg_mem hv) (by simpa only [map_neg] using neg_neg_of_pos hpos)
  have hkerdim : Module.finrank ℝ (LinearMap.ker π.toLinearMap) = 1 := by
    rw [hker]; exact hδ
  have hdir : L.direction = LinearMap.ker π.toLinearMap :=
    Submodule.eq_of_le_of_finrank_eq hLker (hLdim.trans hkerdim.symm)
  have hlevel (y : Plane) : y ∈ (L : Set Plane) ↔ π y = π p := by
    constructor
    · intro hy
      have hv : y - p ∈ LinearMap.ker π.toLinearMap :=
        hdir ▸ L.vsub_mem_direction hy hpL
      have hz := LinearMap.mem_ker.mp hv
      change π (y - p) = 0 at hz
      rw [map_sub] at hz
      exact sub_eq_zero.mp hz
    · intro hy
      have hv : y - p ∈ LinearMap.ker π.toLinearMap := by
        rw [LinearMap.mem_ker]
        change π (y - p) = 0
        rw [map_sub, hy, sub_self]
      have hyL := L.vadd_mem_of_mem_direction (hdir.symm ▸ hv) hpL
      change y ∈ L
      simpa only [vadd_eq_add, sub_add_cancel] using hyL
  filter_upwards [hg] with y hy
  exact hy.trans (hlevel y)

private theorem aligned_placed_supports_vacant_side_transfer
    {K : PolygonalRegion} {S U : Set Plane}
    (hpU : IsPacking K.prototileFamily (K.placements U))
    (π : Plane →L[ℝ] ℝ) (c : ℝ) (s : Plane) (hs : s ∈ S)
    (hcentres : ∀ u ∈ U, π u = π s)
    (hside : ∀ x : Plane, π x = c →
      ∀ᶠ y in 𝓝 x, y ∈ ⋃ t : S, (t : Plane) +ᵥ K.support → c ≤ π y) :
    ∀ x : Plane, π x = c →
      ∀ᶠ y in 𝓝 x, y ∈ ⋃ t : U, (t : Plane) +ᵥ K.support → c ≤ π y := by
  intro x hx
  apply locallyFinite_union_eventually_subset_germ (placed_supports_locallyFinite hpU)
    (fun u => K.isPolygonal.isClosed.vadd (u : Plane)) x {y | c ≤ π y}
  intro u _hxu
  let d : Plane := s - (u : Plane)
  have hd : π d = 0 := by
    dsimp only [d]
    rw [map_sub, hcentres u u.2, sub_self]
  have hxshift : π (x + d) = c := by rw [map_add, hd, add_zero, hx]
  have hcont : Continuous (fun y : Plane => y + d) := continuous_id.add continuous_const
  filter_upwards [hcont.continuousAt.eventually (hside (x + d) hxshift)] with y hy hyu
  obtain ⟨k, hk, hyk⟩ := Set.mem_vadd_set.mp hyu
  have hyshift : y + d ∈ ⋃ t : S, (t : Plane) +ᵥ K.support := by
    apply Set.mem_iUnion.mpr
    refine ⟨⟨s, hs⟩, Set.mem_vadd_set.mpr ⟨k, hk, ?_⟩⟩
    rw [← hyk]
    simp only [vadd_eq_add, d]
    abel
  have hle := hy hyshift
  simpa only [map_add, hd, add_zero] using hle

private theorem transfer_frontier_line_with_positive_support_side
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S U : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (hpS : IsPacking K.prototileFamily (K.placements S))
    (hpU : IsPacking K.prototileFamily (K.placements U))
    (hlS : IsLineSupported S δ) (hU : U.Nonempty)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ) (a s : Plane) (hs : s ∈ S)
    (hcentres : ∀ u ∈ U, π u = π s)
    (hfullS : IsStraightFrontierLine (regularSupport K S) δ a)
    (hnoU : Disjoint (a +ᵥ (δ : Set Plane)) (properVertices (regularSupport K U)))
    (hsideS : ∀ x : Plane, π x = π a → ∀ᶠ y in 𝓝 x,
      y ∈ ⋃ t : S, (t : Plane) +ᵥ K.support → π a ≤ π y) :
    IsStraightFrontierLine (regularSupport K U) δ a ∧
      ∀ x ∈ a +ᵥ (δ : Set Plane),
        regularSupport K U =ᶠ[𝓝 x] {y : Plane | π a < π y} := by
  let E := regularSupport K U
  have hlevel (x : Plane) : x ∈ a +ᵥ (δ : Set Plane) ↔ π x = π a := by
    constructor
    · intro hx
      obtain ⟨v, hv, rfl⟩ := Set.mem_vadd_set.mp hx
      have hv0 : π v = 0 := LinearMap.mem_ker.mp (hker.symm ▸ hv)
      simp only [vadd_eq_add, map_add, hv0, add_zero]
    · intro hx
      have hv : x - a ∈ δ := by
        rw [← hker, LinearMap.mem_ker]
        change π (x - a) = 0
        rw [map_sub, hx, sub_self]
      exact Set.mem_vadd_set.mpr ⟨x - a, hv, by simp [vadd_eq_add]⟩
  have hsideU := aligned_placed_supports_vacant_side_transfer hpU π (π a) s hs hcentres hsideS
  have haFront := hfullS.1 ((hlevel a).mpr rfl)
  have haUnion : a ∈ ⋃ t : S, (t : Plane) +ᵥ K.support := by
    rw [← closure_regularSupport_eq_placed_support_union hpS]
    exact frontier_subset_closure haFront
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp haUnion
  obtain ⟨k, hk, hka⟩ := Set.mem_vadd_set.mp ht
  obtain ⟨u, hu⟩ := hU
  let q : Plane := u + k
  have hqtile : q ∈ ⋃ t : U, (t : Plane) +ᵥ K.support :=
    Set.mem_iUnion.mpr ⟨⟨u, hu⟩, Set.mem_vadd_set.mpr ⟨k, hk, rfl⟩⟩
  have hqlevel : π q = π a := by
    have htcoord := lineSupported_transverse_coordinate_eq π hker hlS hs t.2
    rw [← hka]
    change π (u + k) = π ((t : Plane) + k)
    rw [map_add, map_add, hcentres u hu, htcoord]
  have hsideq : ∀ᶠ y in 𝓝 q, y ∈ closure E → π q ≤ π y := by
    filter_upwards [hsideU q hqlevel] with y hy hyE
    rw [hqlevel]
    apply hy
    rwa [closure_regularSupport_eq_placed_support_union hpU] at hyE
  have hqclosure : q ∈ closure E :=
    placed_support_union_subset_closure_regularSupport hpU hqtile
  have hqfront : q ∈ frontier E := frontier_of_closure_and_one_sided_germ π hπ hqclosure
    (hsideq.mono fun _ hy h => hy (subset_closure h))
  have hqsmooth : BoundaryLocallyStraightAt E q := by
    by_contra h
    exact Set.disjoint_left.mp hnoU ((hlevel q).mpr hqlevel) ⟨hqfront, h⟩
  have hqgerm := smooth_frontier_level_germ_of_one_sided_closed_germ hδ π hker hqsmooth hsideq
  have hdim : Module.finrank ℝ (LinearMap.ker π.toLinearMap) = 1 := by
    rw [hker]; exact hδ
  have hnoLevel : Disjoint {x : Plane | π x = π a} (properVertices E) := by
    have hlineEq : a +ᵥ (δ : Set Plane) = {x : Plane | π x = π a} := Set.ext hlevel
    rw [← hlineEq]
    exact hnoU
  have hfrontLevel : {x : Plane | π x = π a} ⊆ frontier E := by
    change {x : Plane | π.toLinearMap x = π.toLinearMap a} ⊆ frontier E
    apply straight_frontier_germ_propagates_on_line π.toLinearMap hdim E a
    · change Disjoint {x : Plane | π x = π a} (properVertices E)
      exact hnoLevel
    · refine ⟨q, ?_, ?_⟩
      · change π q = π a
        exact hqlevel
      · change ∀ᶠ y in 𝓝 q, y ∈ frontier E ↔ π y = π a
        simpa only [hqlevel] using hqgerm
  have hfullU : IsStraightFrontierLine E δ a :=
    ⟨fun x hx => hfrontLevel ((hlevel x).mp hx), hnoU⟩
  refine ⟨hfullU, ?_⟩
  rcases completeFrontierLine_halfSpace_germs_constant hδ
    (regularSupport_isRegularOpen K U).1 (regularSupport_isRegularOpen K U).2
    π hπ hker a hfullU with hpos | hneg
  · exact hpos
  · exfalso
    have hbelow : q ∈ closure {y : Plane | π y < π a} := by
      change q ∈ closure (π ⁻¹' Set.Iio (π a))
      rw [π.closure_preimage hπ, closure_Iio]
      exact hqlevel.le
    obtain ⟨y, hybelow, hygerm, hyside⟩ :=
      ((mem_closure_iff_frequently.mp hbelow).and_eventually
        ((hneg q ((hlevel q).mpr hqlevel)).and hsideq)).exists
    have hyE : y ∈ E := (Iff.of_eq hygerm).mpr hybelow
    have hle := hyside (subset_closure hyE)
    rw [hqlevel] at hle
    exact (not_lt_of_ge hle) hybelow

private theorem aligned_centres_full_frontier_line_germs_match
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S U : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (hpS : IsPacking K.prototileFamily (K.placements S))
    (hpU : IsPacking K.prototileFamily (K.placements U))
    (hlS : IsLineSupported S δ) (hU : U.Nonempty)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ) (a s : Plane) (hs : s ∈ S)
    (hcentres : ∀ u ∈ U, π u = π s)
    (hfullS : IsStraightFrontierLine (regularSupport K S) δ a)
    (hnoU : Disjoint (a +ᵥ (δ : Set Plane)) (properVertices (regularSupport K U))) :
    IsStraightFrontierLine (regularSupport K U) δ a ∧
      ∀ x ∈ a +ᵥ (δ : Set Plane), regularSupport K S =ᶠ[𝓝 x] regularSupport K U := by
  have transfer (ψ : Plane →L[ℝ] ℝ) (hψ : Function.Surjective ψ)
      (hψker : LinearMap.ker ψ.toLinearMap = δ)
      (hψcentres : ∀ u ∈ U, ψ u = ψ s)
      (hpos : ∀ x ∈ a +ᵥ (δ : Set Plane),
        regularSupport K S =ᶠ[𝓝 x] {y : Plane | ψ a < ψ y}) :
      IsStraightFrontierLine (regularSupport K U) δ a ∧
        ∀ x ∈ a +ᵥ (δ : Set Plane), regularSupport K S =ᶠ[𝓝 x] regularSupport K U := by
    have hside : ∀ x : Plane, ψ x = ψ a → ∀ᶠ y in 𝓝 x,
        y ∈ ⋃ t : S, (t : Plane) +ᵥ K.support → ψ a ≤ ψ y := by
      intro x hx
      have hxδ : x - a ∈ δ := by
        rw [← hψker, LinearMap.mem_ker]
        change ψ (x - a) = 0
        rw [map_sub, hx, sub_self]
      have hxline : x ∈ a +ᵥ (δ : Set Plane) :=
        Set.mem_vadd_set.mpr ⟨x - a, hxδ, by simp [vadd_eq_add]⟩
      have hg := eventuallyEq_closure (hpos x hxline)
      change closure (regularSupport K S) =ᶠ[𝓝 x] closure (ψ ⁻¹' Set.Ioi (ψ a)) at hg
      rw [ψ.closure_preimage hψ, closure_Ioi] at hg
      filter_upwards [hg] with y hy hyunion
      exact (Iff.of_eq hy).mp (placed_support_union_subset_closure_regularSupport hpS hyunion)
    obtain ⟨hfullU, hUpos⟩ := transfer_frontier_line_with_positive_support_side
      hδ hpS hpU hlS hU ψ hψ hψker a s hs hψcentres hfullS hnoU hside
    exact ⟨hfullU, fun x hx => (hpos x hx).trans (hUpos x hx).symm⟩
  rcases completeFrontierLine_halfSpace_germs_constant hδ
    (regularSupport_isRegularOpen K S).1 (regularSupport_isRegularOpen K S).2
    π hπ hker a hfullS with hpos | hneg
  · exact transfer π hπ hker hcentres hpos
  · have hπneg : Function.Surjective (-π) := by
      intro r
      obtain ⟨x, hx⟩ := hπ (-r)
      exact ⟨x, by simpa using congrArg Neg.neg hx⟩
    have hkerneg : LinearMap.ker (-π).toLinearMap = δ := by
      ext x
      simp [← hker, LinearMap.mem_ker]
    exact transfer (-π) hπneg hkerneg
      (fun u hu => by simpa using congrArg Neg.neg (hcentres u hu))
      (fun x hx => by simpa only [neg_apply, neg_lt_neg_iff] using hneg x hx)

private theorem frontier_min_coordinate_corner
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : IsLineSupported S δ)
    (s : Plane) (hs : s ∈ S)
    (hnoline : ¬∃ a : Plane, IsStraightFrontierLine
      (regularSupport K S) δ a) :
    ∃ v ∈ properVertices (regularSupport K S),
      π v = π s + sInf (π '' K.support) := by
  classical
  let D := regularSupport K S
  let m := sInf (π '' K.support)
  let c := π s + m
  have hKcompact : IsCompact (π '' K.support) := K.isPolygonal.isCompact.image π.continuous
  have hKne : (π '' K.support).Nonempty := K.nonempty.image π
  obtain ⟨m₀, hm₀, hm₀min⟩ := hKcompact.exists_isMinOn hKne continuous_id.continuousOn
  have hm₀eq : m₀ = m := by
    dsimp [m]
    apply le_antisymm
    · exact le_csInf hKne hm₀min
    · exact csInf_le hKcompact.bddBelow hm₀
  obtain ⟨k, hkS, hkm⟩ := hm₀
  have hkm' : π k = m := hkm ▸ hm₀eq
  have hstrip : ∀ x ∈ D, c ≤ π x := by
    intro x hx
    have hclosed := placed_support_union_closed hp
    have hopenSub : openUnion K S ⊆ ⋃ t : S, (t : Plane) +ᵥ K.support := by
      intro y hy
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨t, vadd_set_mono interior_subset ht⟩
    have hregSub : D ⊆ ⋃ t : S, (t : Plane) +ᵥ K.support :=
      interior_subset.trans (closure_minimal hopenSub hclosed)
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hregSub hx)
    have hbase : x - (t : Plane) ∈ K.support := by
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_eq_sub] using ht
    have hmin : m ≤ π (x - (t : Plane)) :=
      csInf_le hKcompact.bddBelow (Set.mem_image_of_mem π hbase)
    have htcoord : π (t : Plane) = π s := by
      obtain ⟨a, ha⟩ := hline
      have hs0 : π (s - a) = 0 := LinearMap.mem_ker.mp (hker.symm ▸ ha s hs)
      have ht0 : π ((t : Plane) - a) = 0 := LinearMap.mem_ker.mp (hker.symm ▸ ha t t.2)
      rw [map_sub] at hs0 ht0
      linarith
    rw [map_sub] at hmin
    linarith
  have hstripClosure : ∀ x ∈ closure D, c ≤ π x := by
    apply closure_minimal hstrip
    exact isClosed_le continuous_const π.continuous
  let p := s + k
  have hpfront : p ∈ frontier D := by
    have hkplace : p ∈ s +ᵥ K.support := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change -s + p ∈ K.support
      simpa [p, vadd_eq_add] using hkS
    have hplace : p ∈ ⋃ t : S, (t : Plane) +ᵥ K.support :=
      Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hkplace⟩
    have hopen : IsOpen (openUnion K S) := isOpen_iUnion fun t : S =>
      (Homeomorph.addLeft (t : Plane)).isOpen_image.mpr isOpen_interior
    have hUsub : openUnion K S ⊆ D := by
      intro x hx
      change x ∈ interior (closure (openUnion K S))
      apply interior_mono subset_closure
      rw [mem_interior_iff_mem_nhds]
      exact hopen.mem_nhds hx
    have htileOpen : (s : Plane) +ᵥ K.openCarrier ⊆ openUnion K S := by
      intro x hx
      rw [openUnion, Set.mem_iUnion]
      exact ⟨⟨s, hs⟩, hx⟩
    have htileClosure : (s : Plane) +ᵥ K.support ⊆ closure ((s : Plane) +ᵥ K.openCarrier) := by
      change (s : Plane) +ᵥ K.support ⊆ closure ((s : Plane) +ᵥ interior K.support)
      rw [closure_vadd, K.isPolygonal.closure_interior]
    have hpclosure : p ∈ closure D :=
      closure_mono (fun x hx => hUsub (htileOpen hx)) (htileClosure hkplace)
    have hDopen : IsOpen D := isOpen_interior
    have hpnotD : p ∉ D := by
      intro hpD
      have hloc : ∃ r > 0, Metric.ball p r ⊆ D := Metric.isOpen_iff.mp hDopen p hpD
      obtain ⟨r, hr, hball⟩ := hloc
      obtain ⟨v, hv⟩ := hπ 1
      have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr (by intro h; rw [h, map_zero] at hv; norm_num at hv)
      let t := r / (2 * (‖v‖ + 1))
      have ht : 0 < t := div_pos hr (by positivity)
      have hdist : dist (p - t • v) p < r := by
        rw [dist_eq_norm]
        calc
          ‖(p - t • v) - p‖ = ‖t • v‖ := by
            rw [show (p - t • v) - p = -(t • v) by abel, norm_neg]
          _ = t * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
          _ < r := by
            calc
              t * ‖v‖ < t * (‖v‖ + 1) := mul_lt_mul_of_pos_left (by linarith [norm_nonneg v]) ht
              _ = r / 2 := by dsimp [t]; field_simp
              _ < r := by linarith
      have hlow := hstrip (p - t • v) (hball (Metric.mem_ball.mpr hdist))
      have hπp : π p = c := by simp [p, c, m, hkm', map_add]
      rw [map_sub, hπp, map_smul, hv, smul_eq_mul] at hlow
      linarith
    rw [frontier, hDopen.interior_eq]
    exact ⟨hpclosure, hpnotD⟩
  have hlevel : π p = c := by simp [p, c, m, hkm', map_add]
  by_cases hcorner : p ∈ properVertices D
  · exact ⟨p, hcorner, hlevel⟩
  · obtain ⟨L, hpL, hLdim, hLlocal⟩ := by
      have hstraight : BoundaryLocallyStraightAt D p := by
        by_contra h
        exact hcorner ⟨hpfront, h⟩
      exact hstraight
    have hLker : L.direction ≤ LinearMap.ker π.toLinearMap := by
      intro v hv
      by_contra hvker
      have hvπ : π v ≠ 0 := by
        intro hvzero
        exact hvker (LinearMap.mem_ker.mpr hvzero)
      rcases lt_or_gt_of_ne hvπ with hneg | hpos
      · let w := v
        have hwL : w ∈ L.direction := hv
        have hwπ : π w < 0 := hneg
        exact False.elim (by
          obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hLlocal
          let t := r / (2 * (‖w‖ + 1))
          have ht : 0 < t := div_pos hr (by positivity)
          have hdist : dist (p + t • w) p < r := by
            rw [dist_eq_norm]
            calc
              ‖(p + t • w) - p‖ = ‖t • w‖ := by congr 1 <;> abel
              _ = t * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
              _ < r := by
                calc
                  t * ‖w‖ < t * (‖w‖ + 1) := mul_lt_mul_of_pos_left (by linarith [norm_nonneg w]) ht
                  _ = r / 2 := by dsimp [t]; field_simp
                  _ < r := by linarith
          have hPL : p + t • w ∈ L := by
            have := L.vadd_mem_of_mem_direction (L.direction.smul_mem t hwL) hpL
            simpa [vadd_eq_add, add_comm] using this
          have hfront : p + t • w ∈ frontier D := (hball hdist).mpr hPL
          have hlow := hstripClosure (p + t • w) (frontier_subset_closure hfront)
          rw [map_add, map_smul, smul_eq_mul, hlevel] at hlow
          have hneg : t * π w < 0 := mul_neg_of_pos_of_neg ht hwπ
          linarith)
      · let w := -v
        have hwL : w ∈ L.direction := L.direction.neg_mem hv
        have hwπ : π w < 0 := by simp [w, map_neg]; linarith
        exact False.elim (by
          obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hLlocal
          let t := r / (2 * (‖w‖ + 1))
          have ht : 0 < t := div_pos hr (by positivity)
          have hdist : dist (p + t • w) p < r := by
            rw [dist_eq_norm]
            calc
              ‖(p + t • w) - p‖ = ‖t • w‖ := by congr 1 <;> abel
              _ = t * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
              _ < r := by
                calc
                  t * ‖w‖ < t * (‖w‖ + 1) := mul_lt_mul_of_pos_left (by linarith [norm_nonneg w]) ht
                  _ = r / 2 := by dsimp [t]; field_simp
                  _ < r := by linarith
          have hPL : p + t • w ∈ L := by
            have := L.vadd_mem_of_mem_direction (L.direction.smul_mem t hwL) hpL
            simpa [vadd_eq_add, add_comm] using this
          have hfront : p + t • w ∈ frontier D := (hball hdist).mpr hPL
          have hlow := hstripClosure (p + t • w) (frontier_subset_closure hfront)
          rw [map_add, map_smul, smul_eq_mul, hlevel] at hlow
          have hneg : t * π w < 0 := mul_neg_of_pos_of_neg ht hwπ
          linarith)
    have hLkerδ : L.direction ≤ δ := by simpa [hker] using hLker
    have hkerdim : Module.finrank ℝ (LinearMap.ker π.toLinearMap) = 1 := by
      rw [hker]
      exact hδ
    have hdirKer : L.direction = LinearMap.ker π.toLinearMap :=
      Submodule.eq_of_le_of_finrank_eq hLker (hLdim.trans hkerdim.symm)
    have hdir : L.direction = δ := hdirKer.trans hker
    have hLlevel : (L : Set Plane) = {x | π x = π p} := by
      ext x
      constructor
      · intro hx
        have hv := L.vsub_mem_direction hx hpL
        have hvδ : x - p ∈ δ := by simpa [hdir] using hv
        have hvker : x - p ∈ LinearMap.ker π.toLinearMap := hker.symm ▸ hvδ
        have hvzero := LinearMap.mem_ker.mp hvker
        change π (x - p) = 0 at hvzero
        rw [map_sub] at hvzero
        exact sub_eq_zero.mp hvzero
      · intro hx
        have hvker : x - p ∈ LinearMap.ker π.toLinearMap := by
          apply LinearMap.mem_ker.mpr
          change π (x - p) = 0
          rw [map_sub]
          rw [hx]
          simp
        have hvδ : x - p ∈ δ := hker ▸ hvker
        have hvL : x - p ∈ L.direction := hdir.symm ▸ hvδ
        have hmem := L.vadd_mem_of_mem_direction hvL hpL
        change (x - p) + p ∈ L at hmem
        have heq : (x - p) + p = x := by abel
        simpa [heq] using hmem
    have hseed : ∃ x : Plane, π x = π p ∧
        ∀ᶠ y in 𝓝 x, (y ∈ frontier D ↔ π y = π p) := by
      refine ⟨p, rfl, ?_⟩
      filter_upwards [hLlocal] with y hy
      exact hy.trans (by simp [hLlevel])
    by_cases hproperLine : ∃ v, v ∈ properVertices D ∧ π v = π p
    · obtain ⟨v, hv, hvπ⟩ := hproperLine
      exact ⟨v, hv, by rw [hvπ, hlevel]⟩
    · have hdisj : Disjoint {x : Plane | π x = π p} (properVertices D) := by
        rw [Set.disjoint_left]
        intro x hxC hxV
        exact hproperLine ⟨x, hxV, hxC⟩
      have hfull := straight_frontier_germ_propagates_on_line π.toLinearMap
        (by rw [hker]; exact hδ) D p hdisj hseed
      have hline : p +ᵥ (δ : Set Plane) ⊆ frontier D := by
        intro x hx
        apply hfull
        have hxker : x - p ∈ δ := by
          rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
          change -p + x ∈ δ at hx
          convert hx using 1 <;> abel
        have hxzero := LinearMap.mem_ker.mp (LinearMap.mem_ker.mpr (hker.symm ▸ hxker))
        change π (x - p) = 0 at hxzero
        rw [map_sub] at hxzero
        exact sub_eq_zero.mp hxzero
      have hnodisj : Disjoint (p +ᵥ (δ : Set Plane)) (properVertices D) := by
        rw [Set.disjoint_left]
        intro x hx hxv
        have hxker : x - p ∈ δ := by
          rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
          change -p + x ∈ δ at hx
          convert hx using 1 <;> abel
        have hxzero := LinearMap.mem_ker.mp (LinearMap.mem_ker.mpr (hker.symm ▸ hxker))
        change π (x - p) = 0 at hxzero
        rw [map_sub] at hxzero
        have hxπ : π x = π p := sub_eq_zero.mp hxzero
        exact hproperLine ⟨x, hxv, by rw [hxπ, hlevel]⟩
      exact (hnoline ⟨p, hline, hnodisj⟩).elim

private theorem frontier_max_coordinate_corner
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : IsLineSupported S δ)
    (s : Plane) (hs : s ∈ S)
    (hnoline : ¬∃ a : Plane, IsStraightFrontierLine
      (regularSupport K S) δ a) :
    ∃ v ∈ properVertices (regularSupport K S),
      π v = π s + sSup (π '' K.support) := by
  have hπneg : Function.Surjective (-π) := by
    intro r
    obtain ⟨x, hx⟩ := hπ (-r)
    exact ⟨x, by simpa using congrArg Neg.neg hx⟩
  have hkerneg : LinearMap.ker (-π).toLinearMap = δ := by
    rw [← hker]
    ext x
    simp [LinearMap.mem_ker]
  obtain ⟨v, hv, hvneg⟩ := frontier_min_coordinate_corner
    hδ (-π) hπneg hkerneg hp hline s hs hnoline
  have himage : (-π) '' K.support = -(π '' K.support) := by
    calc
      (-π) '' K.support = (fun x : Plane => -π x) '' K.support := rfl
      _ = (fun y : ℝ => -y) '' (π '' K.support) := by
        rw [Set.image_image]
      _ = -(π '' K.support) := Set.image_neg_eq_neg
  have hvneg' := hvneg
  rw [himage, Real.sInf_neg] at hvneg'
  have hval : -(π v) = -(π s + sSup (π '' K.support)) := by
    simpa [add_comm] using hvneg'
  exact ⟨v, hv, neg_injective hval⟩

/-- Without a complete vertex-free straight boundary component, the outer transverse
extrema of the tile are attained by proper carrier vertices. -/
theorem lineProperVertices_transverseExtrema_of_noStraightLine
    {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) (π : Plane →L[ℝ] ℝ)
    (hπ : Function.Surjective π) (hker : LinearMap.ker π.toLinearMap = δ)
    {S : Set Plane} (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : IsLineSupported S δ)
    (hW : (properVertices (regularSupport K S)).Nonempty)
    (hnoline : ¬∃ a : Plane, IsStraightFrontierLine (regularSupport K S) δ a)
    {s : Plane} (hs : s ∈ S) :
    sInf (π '' properVertices (regularSupport K S)) =
      π s + sInf (π '' K.support) ∧
    sSup (π '' properVertices (regularSupport K S)) =
      π s + sSup (π '' K.support) := by
  have _hδ : Module.finrank ℝ δ = 1 := hδ
  have _hπ : Function.Surjective π := hπ
  have _hnoline := hnoline
  have hKcompact : IsCompact (π '' K.support) := K.isPolygonal.isCompact.image π.continuous
  have hWfinite := lineProperVertices_transverse_image_finite π hker hp hline hs
  have hWbounds : ∀ v ∈ properVertices (regularSupport K S),
      π s + sInf (π '' K.support) ≤ π v ∧ π v ≤ π s + sSup (π '' K.support) := by
    intro v hv
    obtain ⟨k, hk, t, ht, hvt⟩ := properVertexProvenance hp v hv
    have hks : k ∈ K.support := by
      obtain ⟨T⟩ := K.isPolygonal
      obtain ⟨p, hp, hkp⟩ := hk T
      rw [← T.sUnion_eq]
      exact Set.mem_sUnion.mpr ⟨p, hp, hkp.1⟩
    have hπk : π k ∈ π '' K.support := Set.mem_image_of_mem π hks
    rw [hvt, map_add, lineSupported_transverse_coordinate_eq π hker hline hs ht]
    constructor
    · linarith [csInf_le hKcompact.bddBelow hπk]
    · linarith [le_csSup hKcompact.bddAbove hπk]
  -- Actual extreme supporting points either give a proper vertex, or their
  -- straight germ propagates to the forbidden complete vertex-free line.
  have hminCorner : ∃ v ∈ properVertices (regularSupport K S),
      π v = π s + sInf (π '' K.support) := by
    exact frontier_min_coordinate_corner hδ π hπ hker hp hline s hs hnoline
  have hmaxCorner : ∃ v ∈ properVertices (regularSupport K S),
      π v = π s + sSup (π '' K.support) := by
    exact frontier_max_coordinate_corner hδ π hπ hker hp hline s hs hnoline
  constructor
  · apply le_antisymm
    · obtain ⟨v, hv, hval⟩ := hminCorner
      exact hval ▸ csInf_le hWfinite.bddBelow (Set.mem_image_of_mem π hv)
    · apply le_csInf (hW.image π)
      rintro _ ⟨v, hv, rfl⟩
      exact (hWbounds v hv).1
  · apply le_antisymm
    · apply csSup_le (hW.image π)
      rintro _ ⟨v, hv, rfl⟩
      exact (hWbounds v hv).2
    · obtain ⟨v, hv, hval⟩ := hmaxCorner
      exact hval ▸ le_csSup hWfinite.bddAbove (Set.mem_image_of_mem π hv)

private theorem frontier_point_below_minimum_has_parallel_germ
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (π : Plane →L[ℝ] ℝ) (hker : LinearMap.ker π.toLinearMap = δ)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : IsLineSupported S δ) (s : Plane) (hs : s ∈ S)
    (b : ℝ)
    (hvertices : ∀ v ∈ properVertices (regularSupport K S), b ≤ π v)
    {q : Plane} (hqfront : q ∈ frontier (regularSupport K S)) (hqb : π q < b) :
    ∃ L : AffineSubspace ℝ Plane, q ∈ L ∧
      L.direction = δ ∧
      ∀ᶠ z in 𝓝 q, (z ∈ frontier (regularSupport K S) ↔ z ∈ (L : Set Plane)) := by
  let D := regularSupport K S
  have hKcompact : IsCompact (π '' K.support) := K.isPolygonal.isCompact.image π.continuous
  have hKne : (π '' K.support).Nonempty := K.nonempty.image π
  let c := π s + sInf (π '' K.support)
  have hstrip : ∀ x ∈ D, c ≤ π x := by
    intro x hx
    have hclosed := placed_support_union_closed hp
    have hopenSub : openUnion K S ⊆ ⋃ t : S, (t : Plane) +ᵥ K.support := by
      intro y hy
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨t, vadd_set_mono interior_subset ht⟩
    have hregSub : D ⊆ ⋃ t : S, (t : Plane) +ᵥ K.support :=
      interior_subset.trans (closure_minimal hopenSub hclosed)
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hregSub hx)
    have hbase : x - (t : Plane) ∈ K.support := by
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_eq_sub] using ht
    have hmin : sInf (π '' K.support) ≤ π (x - (t : Plane)) :=
      csInf_le hKcompact.bddBelow (Set.mem_image_of_mem π hbase)
    have htcoord : π (t : Plane) = π s := by
      obtain ⟨a, ha⟩ := hline
      have hs0 : π (s - a) = 0 := LinearMap.mem_ker.mp (hker.symm ▸ ha s hs)
      have ht0 : π ((t : Plane) - a) = 0 :=
        LinearMap.mem_ker.mp (hker.symm ▸ ha t t.2)
      rw [map_sub] at hs0 ht0
      linarith
    rw [map_sub] at hmin
    dsimp [c]
    linarith
  have hstripClosure : ∀ x ∈ closure D, c ≤ π x := by
    apply closure_minimal hstrip
    exact isClosed_le continuous_const π.continuous
  have hqnotproper : ¬IsProperVertex D q := by
    intro hqv
    have hqprop : q ∈ properVertices (regularSupport K S) := by
      change IsProperVertex (regularSupport K S) q
      exact hqv
    exact (not_lt_of_ge (hvertices q hqprop)) hqb
  have hstraight : BoundaryLocallyStraightAt D q := by
    by_contra h
    exact hqnotproper ⟨hqfront, h⟩
  obtain ⟨L, hqL, hLdim, hLlocal⟩ := hstraight
  have hLker : L.direction ≤ LinearMap.ker π.toLinearMap := by
    intro v hv
    by_contra hvker
    have hvπ : π v ≠ 0 := by
      intro hvzero
      exact hvker (LinearMap.mem_ker.mpr hvzero)
    let w : Plane := if π v < 0 then v else -v
    have hwL : w ∈ L.direction := by
      dsimp [w]
      split_ifs with h
      · exact hv
      · exact L.direction.neg_mem hv
    have hwπ : π w < 0 := by
      dsimp [w]
      split_ifs with h
      · exact h
      · simp only [map_neg]
        have : 0 < π v := lt_of_le_of_ne (le_of_not_gt h) hvπ.symm
        linarith
    have hwne : w ≠ 0 := by
      intro h
      rw [h, map_zero] at hwπ
      norm_num at hwπ
    have hqc : c ≤ π q := hstripClosure q (frontier_subset_closure hqfront)
    have hBpos : 0 < (π q - c + 1) / (-π w) :=
      div_pos (by linarith) (neg_pos.mpr hwπ)
    let B : ℝ := (π q - c + 1) / (-π w)
    have hBmul : B * (-π w) = π q - c + 1 := by
      dsimp [B]
      rw [div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hwπ))]
    have hendpoint : π (q + B • w) = c - 1 := by
      rw [map_add, map_smul, smul_eq_mul]
      nlinarith [hBmul]
    have hW : ∀ t ∈ Set.Icc (0 : ℝ) B, q + t • w ∉ properVertices D := by
      intro t ht hvertex
      have hcoord : π (q + t • w) ≤ π q := by
        rw [map_add, map_smul, smul_eq_mul]
        have hmul : t * π w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 hwπ.le
        linarith
      exact (not_lt_of_ge (hvertices (q + t • w) hvertex)) (hcoord.trans_lt hqb)
    have hlineSet : (L : Set Plane) = q +ᵥ (Submodule.span ℝ ({w} : Set Plane) : Set Plane) := by
      have hdirspan := eq_span_singleton_of_mem_of_finrank_eq_one hLdim hwL hwne
      have hLdirection : (L : Set Plane) = q +ᵥ (L.direction : Set Plane) := by
        ext z
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        change z ∈ L ↔ -q + z ∈ L.direction
        constructor
        · intro hz
          have hz' := L.vsub_mem_direction hz hqL
          change z - q ∈ L.direction at hz'
          convert hz' using 1 <;> abel
        · intro hz
          have hmem := L.vadd_mem_of_mem_direction hz hqL
          change (-q + z) + q ∈ L at hmem
          have heq : (-q + z) + q = z := by abel
          simpa [heq] using hmem
      rw [hLdirection, hdirspan]
    have hg : ∀ᶠ z in 𝓝 q, z ∈ frontier D ↔
        z ∈ q +ᵥ (Submodule.span ℝ ({w} : Set Plane) : Set Plane) := by
      filter_upwards [hLlocal] with z hz
      change z ∈ frontier D ↔ z ∈ (L : Set Plane) at hz
      simpa only [hlineSet] using hz
    have hrun := frontier_ray_segment_of_no_properVertices hwne hBpos hqfront hg hW
    have hendfront : q + B • w ∈ frontier D := hrun B ⟨le_of_lt hBpos, le_rfl⟩
    have hendstrip := hstripClosure (q + B • w) (frontier_subset_closure hendfront)
    rw [hendpoint] at hendstrip
    linarith
  have hLkerδ : L.direction ≤ δ := by simpa [hker] using hLker
  have hkerdim : Module.finrank ℝ (LinearMap.ker π.toLinearMap) = 1 := by
    rw [hker]
    exact hδ
  have hdirKer : L.direction = LinearMap.ker π.toLinearMap :=
    Submodule.eq_of_le_of_finrank_eq hLker (hLdim.trans hkerdim.symm)
  have hdir : L.direction = δ := hdirKer.trans hker
  exact ⟨L, hqL, hdir, hLlocal⟩

private theorem placed_below_minimum_slice_full_or_empty
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : IsLineSupported S δ) (s : Plane) (hs : s ∈ S)
    (b : ℝ)
    (hvertices : ∀ v ∈ properVertices (regularSupport K S), b ≤ π v)
    (p : Plane) (hpcoord : π p < b) :
    (p +ᵥ (δ : Set Plane) ⊆ regularSupport K S) ∨
      Disjoint (p +ᵥ (δ : Set Plane)) (regularSupport K S) := by
  classical
  let D := regularSupport K S
  let C : Set Plane := {x | π x = π p}
  have hCconvex : Convex ℝ C := by
    intro x hx y hy r t hr ht hrt
    change π x = π p at hx
    change π y = π p at hy
    change π (r • x + t • y) = π p
    simp only [map_add, map_smul]
    rw [hx, hy, ← add_smul, hrt, one_smul]
  have hCpre : IsPreconnected C := hCconvex.isPreconnected
  have hCker : ∀ x, x ∈ C ↔ x ∈ p +ᵥ (δ : Set Plane) := by
    intro x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change π x = π p ↔ -p + x ∈ δ
    have heq : -p + x = x - p := by abel
    rw [heq, ← hker, LinearMap.mem_ker, map_sub]
    constructor
    · intro hx
      simpa [hx]
    · exact sub_eq_zero.mp
  have hdisj : Disjoint C (properVertices D) := by
    rw [Set.disjoint_left]
    intro v hvC hvproper
    change π v = π p at hvC
    exact (not_lt_of_ge (hvertices v hvproper)) (hvC ▸ hpcoord)
  by_cases hfrontC : (C ∩ frontier D).Nonempty
  · obtain ⟨q, hqC, hqfront⟩ := hfrontC
    change π q = π p at hqC
    have hqb : π q < b := hqC ▸ hpcoord
    obtain ⟨L, hqL, hdir, hLlocal⟩ :=
      frontier_point_below_minimum_has_parallel_germ hδ π hker hp hline s hs b
        hvertices hqfront hqb
    have hLlevel : (L : Set Plane) = C := by
      ext x
      constructor
      · intro hx
        have hv := L.vsub_mem_direction hx hqL
        have hvδ : x - q ∈ δ := by simpa [hdir] using hv
        have hvker : x - q ∈ LinearMap.ker π.toLinearMap := hker.symm ▸ hvδ
        have hvzero := LinearMap.mem_ker.mp hvker
        change π (x - q) = 0 at hvzero
        rw [map_sub] at hvzero
        have hxπ : π x = π q := sub_eq_zero.mp hvzero
        exact hxπ.trans hqC
      · intro hx
        have hvker : x - q ∈ LinearMap.ker π.toLinearMap := by
          apply LinearMap.mem_ker.mpr
          change π (x - q) = 0
          rw [map_sub]
          rw [hx, hqC]
          simp
        have hvδ : x - q ∈ δ := hker ▸ hvker
        have hvL : x - q ∈ L.direction := hdir.symm ▸ hvδ
        have hmem := L.vadd_mem_of_mem_direction hvL hqL
        change (x - q) + q ∈ L at hmem
        have heq : (x - q) + q = x := by abel
        simpa [heq] using hmem
    have hseed : ∃ x : Plane, π x = π p ∧
        ∀ᶠ y in 𝓝 x, (y ∈ frontier D ↔ π y = π p) := by
      refine ⟨q, hqC, ?_⟩
      filter_upwards [hLlocal] with y hy
      change y ∈ frontier D ↔ y ∈ (L : Set Plane) at hy
      rw [hLlevel] at hy
      simpa [C] using hy
    have hfrontall := straight_frontier_germ_propagates_on_line
      π.toLinearMap (by rw [hker]; exact hδ) D p hdisj hseed
    right
    rw [Set.disjoint_left]
    intro x hxC hxD
    have hxC' : x ∈ C := (hCker x).mpr hxC
    have hxfront : x ∈ frontier D := hfrontall hxC'
    have hxinterior : x ∈ interior D := by
      change x ∈ interior (interior (closure (openUnion K S)))
      rw [isOpen_interior.interior_eq]
      exact hxD
    exact (Set.disjoint_left.mp disjoint_interior_frontier) hxinterior hxfront
  · have hnoFront : ∀ x ∈ C, x ∉ frontier D := by
      intro x hx
      exact fun hxf => hfrontC ⟨x, hx, hxf⟩
    letI : PreconnectedSpace C := (isPreconnected_iff_preconnectedSpace).mp hCpre
    let B : Set C := {x | (x : Plane) ∈ D}
    have hDopen : IsOpen D := by
      change IsOpen (interior (closure (openUnion K S)))
      exact isOpen_interior
    have hBopen : IsOpen B := hDopen.preimage continuous_subtype_val
    have hBcomplOpen : IsOpen Bᶜ := by
      have heq : Bᶜ = (Subtype.val : C → Plane) ⁻¹' interior Dᶜ := by
        ext z
        simp only [Set.mem_compl_iff, B, Set.mem_preimage]
        constructor
        · intro hz
          have hnotfront : (z : Plane) ∉ frontier D := hnoFront z z.2
          have hsplit : (z : Plane) ∈ interior D ∪ interior Dᶜ := by
            have hnot : (z : Plane) ∈ (frontier D)ᶜ := hnotfront
            rw [compl_frontier_eq_union_interior] at hnot
            exact hnot
          rcases hsplit with hDint | hDcompl
          · have hzD : (z : Plane) ∈ D := interior_subset hDint
            exact False.elim (hz hzD)
          · exact hDcompl
        · intro hzint hzD
          have hzcompl : (z : Plane) ∈ Dᶜ := interior_subset hzint
          exact hzcompl hzD
      rw [heq]
      exact isOpen_interior.preimage continuous_subtype_val
    have hBclosed : IsClosed B := by simpa only [compl_compl] using hBcomplOpen.isClosed_compl
    have hBclopen : IsClopen B := ⟨hBclosed, hBopen⟩
    by_cases hBne : B.Nonempty
    · have hBuniv : B = Set.univ := IsClopen.eq_univ hBclopen hBne
      left
      intro x hx
      have hxC : x ∈ C := (hCker x).mpr hx
      have hxB : (⟨x, hxC⟩ : C) ∈ B := by rw [hBuniv]; trivial
      exact hxB
    · right
      rw [Set.disjoint_left]
      intro x hx hxD
      exact hBne ⟨⟨x, (hCker x).mpr hx⟩, hxD⟩

private theorem centre_coordinate_of_source_extreme_witnesses
    {WS WU : Set Plane} (π : Plane →L[ℝ] ℝ)
    (z s u : Plane) (m M : ℝ)
    (hW : z +ᵥ WS = WU)
    (hUlo : ∀ v ∈ WU, π u + m ≤ π v)
    (hUhi : ∀ v ∈ WU, π v ≤ π u + M)
    (vmin vmax : Plane) (hvmin : vmin ∈ WS) (hvmax : vmax ∈ WS)
    (hmin : π vmin = π s + m) (hmax : π vmax = π s + M) :
    π u = π (s + z) := by
  have hvmin' : vmin + z ∈ WU := by
    have hv : vmin + z ∈ z +ᵥ WS := by
      apply Set.mem_vadd_set.mpr
      refine ⟨vmin, hvmin, ?_⟩
      simp [vadd_eq_add, add_comm]
    rw [← hW]
    exact hv
  have hvmax' : vmax + z ∈ WU := by
    have hv : vmax + z ∈ z +ᵥ WS := by
      apply Set.mem_vadd_set.mpr
      refine ⟨vmax, hvmax, ?_⟩
      simp [vadd_eq_add, add_comm]
    rw [← hW]
    exact hv
  have hu_le : π u ≤ π s + π z := by
    have h := hUlo (vmin + z) hvmin'
    rw [map_add, hmin] at h
    linarith
  have hs_le : π s + π z ≤ π u := by
    have h := hUhi (vmax + z) hvmax'
    rw [map_add, hmax] at h
    linarith
  rw [map_add]
  exact le_antisymm hu_le hs_le

/-- The reverse-source version of the extreme-witness bridge. -/
private theorem centre_coordinate_of_target_extreme_witnesses
    {WS WU : Set Plane} (π : Plane →L[ℝ] ℝ)
    (z s u : Plane) (m M : ℝ)
    (hW : z +ᵥ WS = WU)
    (hSlo : ∀ v ∈ WS, π s + m ≤ π v)
    (hShi : ∀ v ∈ WS, π v ≤ π s + M)
    (vmin vmax : Plane) (hvmin : vmin ∈ WU) (hvmax : vmax ∈ WU)
    (hmin : π vmin = π u + m) (hmax : π vmax = π u + M) :
    π u = π (s + z) := by
  have hWback : (-z) +ᵥ WU = WS := by
    rw [← hW]
    simp [vadd_vadd]
  have hvmin' : vmin - z ∈ WS := by
    have hv : vmin - z ∈ (-z) +ᵥ WU := by
      apply Set.mem_vadd_set.mpr
      refine ⟨vmin, hvmin, ?_⟩
      simp [vadd_eq_add, sub_eq_add_neg, add_comm]
    rw [← hWback]
    exact hv
  have hvmax' : vmax - z ∈ WS := by
    have hv : vmax - z ∈ (-z) +ᵥ WU := by
      apply Set.mem_vadd_set.mpr
      refine ⟨vmax, hvmax, ?_⟩
      simp [vadd_eq_add, sub_eq_add_neg, add_comm]
    rw [← hWback]
    exact hv
  have hu_le : π u ≤ π s + π z := by
    have h := hShi (vmax - z) hvmax'
    rw [map_sub, hmax] at h
    rw [sub_le_iff_le_add] at h
    linarith
  have hs_le : π s + π z ≤ π u := by
    have h := hSlo (vmin - z) hvmin'
    rw [map_sub, hmin] at h
    rw [le_sub_iff_add_le] at h
    linarith
  rw [map_add]
  exact le_antisymm hu_le hs_le

private theorem proper_vertex_transverse_bounds_local
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (π : Plane →L[ℝ] ℝ) (hker : LinearMap.ker π.toLinearMap = δ)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : IsLineSupported S δ) {s : Plane} (hs : s ∈ S) :
    ∀ v ∈ properVertices (regularSupport K S),
      π s + sInf (π '' K.support) ≤ π v ∧
        π v ≤ π s + sSup (π '' K.support) := by
  classical
  have hKcompact : IsCompact (π '' K.support) :=
    K.isPolygonal.isCompact.image π.continuous
  intro v hv
  obtain ⟨k, hk, t, ht, hvt⟩ := properVertexProvenance hp v hv
  have hks : k ∈ K.support := by
    obtain ⟨T⟩ := K.isPolygonal
    obtain ⟨p, hpT, hkp⟩ := hk T
    rw [← T.sUnion_eq]
    exact Set.mem_sUnion.mpr ⟨p, hpT, hkp.1⟩
  have hπk : π k ∈ π '' K.support := Set.mem_image_of_mem π hks
  have htcoord : π t = π s := by
    obtain ⟨a, ha⟩ := hline
    have hs0 : π (s - a) = 0 :=
      LinearMap.mem_ker.mp (hker.symm ▸ ha s hs)
    have ht0 : π (t - a) = 0 :=
      LinearMap.mem_ker.mp (hker.symm ▸ ha t ht)
    rw [map_sub] at hs0 ht0
    linarith
  rw [hvt, map_add, htcoord]
  constructor
  · simpa [add_comm] using
      add_le_add_left (csInf_le hKcompact.bddBelow hπk) (π s)
  · simpa [add_comm] using
      add_le_add_left (le_csSup hKcompact.bddAbove hπk) (π s)

/-- If at least one carrier has no complete vertex-free line, its actual extrema corners
and the provenance bounds on the other carrier force the transverse centre shift. -/
private theorem centre_coordinates_align_if_one_has_no_straight_line
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S U : Set Plane}
    (hδ : Module.finrank ℝ δ = 1) (π : Plane →L[ℝ] ℝ)
    (hπ : Function.Surjective π) (hker : LinearMap.ker π.toLinearMap = δ)
    (hpS : IsPacking K.prototileFamily (K.placements S))
    (hpU : IsPacking K.prototileFamily (K.placements U))
    (hlineS : IsLineSupported S δ)
    (hlineU : IsLineSupported U δ)
    (z : Plane) (hW : z +ᵥ properVertices (regularSupport K S) =
      properVertices (regularSupport K U))
    (s : Plane) (hs : s ∈ S) (u : Plane) (hu : u ∈ U)
    (hno : (¬∃ a : Plane, IsStraightFrontierLine
        (regularSupport K S) δ a) ∨
      (¬∃ a : Plane, IsStraightFrontierLine
        (regularSupport K U) δ a)) :
    π u = π (s + z) := by
  classical
  let m : ℝ := sInf (π '' K.support)
  let M : ℝ := sSup (π '' K.support)
  have hSbounds := proper_vertex_transverse_bounds_local π hker hpS hlineS hs
  have hUbounds := proper_vertex_transverse_bounds_local π hker hpU hlineU hu
  rcases hno with hnoS' | hnoU'
  · obtain ⟨vmin, hvmin, hmin⟩ :=
      frontier_min_coordinate_corner hδ π hπ hker hpS hlineS s hs hnoS'
    obtain ⟨vmax, hvmax, hmax⟩ :=
      frontier_max_coordinate_corner hδ π hπ hker hpS hlineS s hs hnoS'
    exact centre_coordinate_of_source_extreme_witnesses π z s u m M hW
      (fun v hv => (hUbounds v hv).1) (fun v hv => (hUbounds v hv).2)
      vmin vmax hvmin hvmax (by simpa [m] using hmin) (by simpa [M] using hmax)
  · obtain ⟨vmin, hvmin, hmin⟩ :=
      frontier_min_coordinate_corner hδ π hπ hker hpU hlineU u hu hnoU'
    obtain ⟨vmax, hvmax, hmax⟩ :=
      frontier_max_coordinate_corner hδ π hπ hker hpU hlineU u hu hnoU'
    exact centre_coordinate_of_target_extreme_witnesses π z s u m M hW
      (fun v hv => (hSbounds v hv).1) (fun v hv => (hSbounds v hv).2)
      vmin vmax hvmin hvmax (by simpa [m] using hmin) (by simpa [M] using hmax)

private theorem finite_line_frontier_preimage_of_endpoint_avoidance
    {D : Set Plane} (π : Plane →L[ℝ] ℝ) (k w : Plane)
    (hw : w ≠ 0) (hπw : π w = 0) (F : Finset (Plane × Plane))
    (hfront : frontier D = ⋃ p ∈ F, segment ℝ p.1 p.2)
    (hcritical : ∀ p ∈ F, π k ≠ π p.1) :
    {r : ℝ | k + r • w ∈ frontier D}.Finite := by
  classical
  have hsegment (p : Plane × Plane) (hp : p ∈ F) :
      {r : ℝ | k + r • w ∈ segment ℝ p.1 p.2}.Finite := by
    apply Set.Subsingleton.finite
    intro r hr s hs
    rw [segment_eq_image_lineMap] at hr hs
    obtain ⟨α, _, hα⟩ := hr
    obtain ⟨β, _, hβ⟩ := hs
    have hline (q : ℝ) : π (k + q • w) = π k := by
      rw [map_add, map_smul, hπw, smul_zero, add_zero]
    have hαπ := congrArg π hα
    have hβπ := congrArg π hβ
    rw [AffineMap.lineMap_apply_module] at hαπ hβπ
    simp only [map_add, map_smul, smul_eq_mul, hline] at hαπ hβπ
    have hab : π p.1 ≠ π p.2 := by
      intro hab
      have hak : π p.1 = π k := by rw [hab] at hαπ; nlinarith
      exact hcritical p hp hak.symm
    have hαβ : α = β := by
      have hdiff : (α - β) * (π p.2 - π p.1) = 0 := by nlinarith [hαπ, hβπ]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right (sub_ne_zero.mpr hab.symm))
    have hrs : k + r • w = k + s • w := by rw [← hα, ← hβ, hαβ]
    exact smul_left_injective ℝ hw (add_left_cancel hrs)
  have hfinite : (⋃ p ∈ F, {r : ℝ | k + r • w ∈ segment ℝ p.1 p.2}).Finite :=
    F.finite_toSet.biUnion hsegment
  apply hfinite.subset
  intro r hr
  change k + r • w ∈ frontier D at hr
  rw [hfront, Set.mem_iUnion] at hr
  obtain ⟨p, hp⟩ := hr
  rw [Set.mem_iUnion] at hp
  obtain ⟨hpF, hrp⟩ := hp
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpF, hrp⟩⟩

private theorem lineSupported_noncritical_tile_frontier_preimages_finite
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (π : Plane →L[ℝ] ℝ) (hker : LinearMap.ker π.toLinearMap = δ)
    (hl : IsLineSupported S δ) (s : Plane) (hs : s ∈ S) (e w : Plane)
    (he : π e = 1) (hw : w ≠ 0) (hπw : π w = 0)
    (F : Finset (Plane × Plane))
    (hfront : frontier K.support = ⋃ p ∈ F, segment ℝ p.1 p.2)
    (x : ℝ) (hcritical : ∀ p ∈ F, x ≠ π p.1) :
    ∀ t : S, {r : ℝ | s + x • e + r • w ∈
      frontier ((t : Plane) +ᵥ K.support)}.Finite := by
  intro t
  let k : Plane := s - (t : Plane) + x • e
  have htcoord := lineSupported_transverse_coordinate_eq π hker hl hs t.2
  have hπk : π k = x := by
    dsimp only [k]
    simp only [map_add, map_sub, map_smul, he, smul_eq_mul, mul_one,
      htcoord, sub_self, zero_add]
  have htv : frontier ((t : Plane) +ᵥ K.support) = (t : Plane) +ᵥ frontier K.support := by
    simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
      ((Homeomorph.addLeft (t : Plane)).image_frontier K.support).symm
  have hset : {r : ℝ | s + x • e + r • w ∈ frontier ((t : Plane) +ᵥ K.support)} =
      {r : ℝ | k + r • w ∈ frontier K.support} := by
    ext r
    change s + x • e + r • w ∈ frontier ((t : Plane) +ᵥ K.support) ↔
      k + r • w ∈ frontier K.support
    rw [htv, Set.mem_vadd_set_iff_neg_vadd_mem]
    have hpoint : -(t : Plane) +ᵥ (s + x • e + r • w) = k + r • w := by
      simp only [vadd_eq_add, k]
      abel
    rw [hpoint]
  rw [hset]
  exact finite_line_frontier_preimage_of_endpoint_avoidance π k w hw hπw F hfront
    (fun p hp => by rw [hπk]; exact hcritical p hp)

section MinimumCornerProofs

private theorem bgcorner_endpoint_finiteSupportsNear
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : IsPacking K.prototileFamily (K.placements T)) (v : Plane) :
    {t : T | v ∈ (t : Plane) +ᵥ K.support}.Finite := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp
    K.isPolygonal.isBounded
  let A : ℝ := ‖v‖ + M
  have hcentres : (T ∩ Metric.closedBall (0 : Plane) A).Finite := by
    exact (packing_centres_locallyFinite hpack).1 _ Metric.isBounded_closedBall
  have hpre : ((fun t : T => (t : Plane)) ⁻¹'
      (T ∩ Metric.closedBall (0 : Plane) A)).Finite :=
    Set.Finite.preimage (s := T ∩ Metric.closedBall (0 : Plane) A)
      (f := fun t : T => (t : Plane))
      (fun a _ b _ hab => Subtype.ext hab) hcentres
  apply hpre.subset
  intro t ht
  change v ∈ (t : Plane) +ᵥ K.support at ht
  have hy : v - (t : Plane) ∈ K.support := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using ht
  have hysub := hM hy
  have hybound : ‖v - (t : Plane)‖ ≤ M := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hysub
  have htbound : ‖(t : Plane)‖ ≤ A := by
    dsimp [A]
    calc
      ‖(t : Plane)‖ = ‖v - (v - (t : Plane))‖ := by
        congr 1
        abel
      _ ≤ ‖v‖ + ‖v - (t : Plane)‖ := norm_sub_le _ _
      _ ≤ ‖v‖ + M := add_le_add_right hybound ‖v‖
  change (t : Plane) ∈ T ∩ Metric.closedBall (0 : Plane) A
  exact ⟨t.2, by simpa [Metric.mem_closedBall, dist_eq_norm] using htbound⟩

private theorem bgcorner_endpoint_finiteSupportsMeetingBall
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : IsPacking K.prototileFamily (K.placements T)) (v : Plane) :
    {t : T | (((t : Plane) +ᵥ K.support) ∩ Metric.closedBall v 1).Nonempty}.Finite := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp
    K.isPolygonal.isBounded
  let A : ℝ := ‖v‖ + 1 + M
  have hcentres : (T ∩ Metric.closedBall (0 : Plane) A).Finite := by
    exact (packing_centres_locallyFinite hpack).1 _ Metric.isBounded_closedBall
  have hpre : ((fun t : T => (t : Plane)) ⁻¹'
      (T ∩ Metric.closedBall (0 : Plane) A)).Finite :=
    Set.Finite.preimage (s := T ∩ Metric.closedBall (0 : Plane) A)
      (f := fun t : T => (t : Plane))
      (fun a _ b _ hab => Subtype.ext hab) hcentres
  apply hpre.subset
  intro t ht
  change (((t : Plane) +ᵥ K.support) ∩ Metric.closedBall v 1).Nonempty at ht
  obtain ⟨z, hz⟩ := ht
  rcases hz with ⟨hzTile, hzBall⟩
  have hy : z - (t : Plane) ∈ K.support := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hzTile
  have hybound : ‖z - (t : Plane)‖ ≤ M := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hM hy
  have hzbound : ‖z‖ ≤ ‖v‖ + 1 := by
    have hdist : dist z v ≤ 1 := by
      simpa [Metric.mem_closedBall] using hzBall
    calc
      ‖z‖ = dist z 0 := by simp [dist_eq_norm]
      _ ≤ dist z v + dist v 0 := dist_triangle _ _ _
      _ ≤ 1 + ‖v‖ := add_le_add hdist (by simp [dist_eq_norm])
      _ = ‖v‖ + 1 := by ring
  have htbound : ‖(t : Plane)‖ ≤ A := by
    dsimp [A]
    calc
      ‖(t : Plane)‖ = ‖z - (z - (t : Plane))‖ := by congr 1 <;> abel
      _ ≤ ‖z‖ + ‖z - (t : Plane)‖ := norm_sub_le _ _
      _ ≤ (‖v‖ + 1) + M := add_le_add hzbound hybound
  change (t : Plane) ∈ T ∩ Metric.closedBall (0 : Plane) A
  exact ⟨t.2, by simpa [Metric.mem_closedBall, dist_eq_norm] using htbound⟩

private theorem bgcorner_endpoint_clearFiniteTiles
    (v : Plane) (I : Finset (Set Plane)) (hclosed : ∀ s ∈ I, IsClosed s) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s ∈ I, v ∉ s → Disjoint (Metric.ball v ρ) s := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert s I hs ih =>
      have htail : ∀ t ∈ I, IsClosed t := by
        intro t ht
        exact hclosed t (Finset.mem_insert_of_mem ht)
      obtain ⟨ρ, hρ, hρavoid⟩ := ih htail
      by_cases hvs : v ∈ s
      · refine ⟨min ρ 1, lt_min hρ (by norm_num), ?_⟩
        intro t ht hvt
        rcases Finset.mem_insert.mp ht with rfl | htI
        · exact (hvt hvs).elim
        · have hprev := hρavoid t htI hvt
          rw [Set.disjoint_left] at hprev ⊢
          intro z hzBall hzt
          apply hprev
          · exact Metric.mem_ball.mpr
              ((Metric.mem_ball.mp hzBall).trans_le (min_le_left _ _))
          · exact hzt
      · have hsClosed : IsClosed s := hclosed s (Finset.mem_insert_self s I)
        have hopen : IsOpen (sᶜ) := hsClosed.isOpen_compl
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen v hvs
        refine ⟨min ρ r, lt_min hρ hr, ?_⟩
        intro t ht hvt
        rcases Finset.mem_insert.mp ht with rfl | htI
        · rw [Set.disjoint_left]
          intro z hzBall hzS
          exact hball (Metric.mem_ball.mpr
            ((Metric.mem_ball.mp hzBall).trans_le (min_le_right _ _))) hzS
        · have hprev := hρavoid t htI hvt
          rw [Set.disjoint_left] at hprev ⊢
          intro z hzBall hzt
          apply hprev
          · exact Metric.mem_ball.mpr
              ((Metric.mem_ball.mp hzBall).trans_le (min_le_left _ _))
          · exact hzt

private theorem bgcorner_endpoint_starRadius
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : IsPacking K.prototileFamily (K.placements T)) (v : Plane) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : T,
      (((t : Plane) +ᵥ K.support) ∩ Metric.ball v ρ).Nonempty →
        v ∈ (t : Plane) +ᵥ K.support := by
  classical
  have hnear := bgcorner_endpoint_finiteSupportsMeetingBall K T hpack v
  let J := hnear.toFinset
  let I : Finset (Set Plane) := J.image fun t : T => (t : Plane) +ᵥ K.support
  have hclosed : ∀ s ∈ I, IsClosed s := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact K.isPolygonal.isClosed.vadd (t : Plane)
  obtain ⟨r, hr, havoid⟩ := bgcorner_endpoint_clearFiniteTiles v I hclosed
  refine ⟨min r 1, lt_min hr (by norm_num), ?_⟩
  intro t hmeet
  rcases hmeet with ⟨z, hz⟩
  rcases hz with ⟨hzTile, hzBall⟩
  have hzClosed : z ∈ Metric.closedBall v 1 := by
    rw [Metric.mem_closedBall]
    exact (Metric.mem_ball.mp hzBall).le.trans (min_le_right _ _)
  have htNear : t ∈ J := by
    apply hnear.mem_toFinset.mpr
    exact ⟨z, ⟨hzTile, hzClosed⟩⟩
  have htI : (t : Plane) +ᵥ K.support ∈ I :=
    Finset.mem_image.mpr ⟨t, htNear, rfl⟩
  by_contra hnot
  have hdisj := havoid ((t : Plane) +ᵥ K.support) htI hnot
  rw [Set.disjoint_left] at hdisj
  apply hdisj
  · rw [Metric.mem_ball] at hzBall ⊢
    exact hzBall.trans_le (min_le_left _ _)
  · exact hzTile

private theorem bgcorner_endpoint_finiteIncidentEdgeList
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : IsPacking K.prototileFamily (K.placements T)) (v : Plane) :
    ∃ G : Finset (T × (Plane × Plane)),
      (∀ w ∈ G, v ∈ (w.1 : Plane) +ᵥ K.support ∧
        w.2.1 ≠ w.2.2 ∧ w.2.1 ∈ vertexSet K.support ∧
          w.2.2 ∈ vertexSet K.support ∧
            segment ℝ w.2.1 w.2.2 ⊆ frontier K.support) ∧
      ∀ t : T, v ∈ (t : Plane) +ᵥ K.support →
        ∀ x ∈ frontier ((t : Plane) +ᵥ K.support),
          ∃ p : Plane × Plane, (t, p) ∈ G ∧
            x ∈ segment ℝ ((t : Plane) + p.1) ((t : Plane) + p.2) := by
  classical
  have hI := bgcorner_endpoint_finiteSupportsNear K T hpack v
  let I := hI.toFinset
  obtain ⟨F, hF, hcover⟩ :=
    Tiling.IsPolygonal.exists_finite_intrinsic_boundarySegments K.isPolygonal
  let G : Finset (T × (Plane × Plane)) := I.product F
  refine ⟨G, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwI, hwF⟩ := Finset.mem_product.mp hw
    obtain ⟨hne, ha, hb, hseg⟩ := hF w.2 hwF
    exact ⟨hI.mem_toFinset.mp hwI, hne, ha, hb, hseg⟩
  · intro t ht x hx
    have hfrontierVadd : frontier ((t : Plane) +ᵥ K.support) =
        (t : Plane) +ᵥ frontier K.support := by
      rw [frontier, closure_vadd, interior_vadd]
      ext z
      simp only [frontier, Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, neg_add_eq_sub]
    rw [hfrontierVadd] at hx
    have hxbase : x - (t : Plane) ∈ frontier K.support := by
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_eq_sub] using hx
    have hxinEdges : x - (t : Plane) ∈ ⋃ p ∈ F, segment ℝ p.1 p.2 := by
      rw [← hcover]
      exact hxbase
    obtain ⟨p, hp'⟩ := Set.mem_iUnion.mp hxinEdges
    obtain ⟨hp, hseg⟩ := Set.mem_iUnion.mp hp'
    have htI : t ∈ I := hI.mem_toFinset.mpr ht
    have htp : (t, p) ∈ G := by
      exact Finset.mem_product.mpr ⟨htI, hp⟩
    refine ⟨p, htp, ?_⟩
    have htranslate : (t : Plane) + (x - (t : Plane)) ∈
        segment ℝ ((t : Plane) + p.1) ((t : Plane) + p.2) := by
      rw [mem_segment_translate ℝ (t : Plane)]
      exact hseg
    simpa [sub_add_cancel] using htranslate

private theorem bgcorner_endpoint_localFiniteBoundaryStar
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : IsPacking K.prototileFamily (K.placements T)) (v : Plane) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ G : Finset (T × (Plane × Plane)),
      (∀ w ∈ G, v ∈ (w.1 : Plane) +ᵥ K.support ∧
        w.2.1 ≠ w.2.2 ∧ w.2.1 ∈ vertexSet K.support ∧
          w.2.2 ∈ vertexSet K.support ∧
            segment ℝ w.2.1 w.2.2 ⊆ frontier K.support) ∧
      ∀ t : T, ∀ x ∈ Metric.ball v ρ,
        x ∈ frontier ((t : Plane) +ᵥ K.support) →
          ∃ p : Plane × Plane, (t, p) ∈ G ∧
            x ∈ segment ℝ ((t : Plane) + p.1) ((t : Plane) + p.2) := by
  obtain ⟨G, hGvalid, hGcover⟩ := bgcorner_endpoint_finiteIncidentEdgeList K T hpack v
  obtain ⟨ρ, hρ, hstar⟩ := bgcorner_endpoint_starRadius K T hpack v
  refine ⟨ρ, hρ, G, hGvalid, ?_⟩
  intro t x hxball hxfront
  have hxSupport : x ∈ (t : Plane) +ᵥ K.support := by
    have hclosed := K.isPolygonal.isClosed.vadd (t : Plane)
    simpa [hclosed.closure_eq] using frontier_subset_closure hxfront
  have htincident : v ∈ (t : Plane) +ᵥ K.support :=
    hstar t ⟨x, hxSupport, hxball⟩
  exact hGcover t htincident x hxfront

private theorem bgcorner_actual_regularSupport_frontier_local_edge_cover
    (K : PolygonalRegion) (T : Set Plane)
    (hp : IsPacking K.prototileFamily (K.placements T)) (v : Plane) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ G : Finset (T × (Plane × Plane)),
      (∀ g ∈ G, v ∈ (g.1 : Plane) +ᵥ K.support ∧
        g.2.1 ≠ g.2.2 ∧ g.2.1 ∈ vertexSet K.support ∧
          g.2.2 ∈ vertexSet K.support ∧
            segment ℝ g.2.1 g.2.2 ⊆ frontier K.support) ∧
      ∀ x ∈ Metric.ball v ρ, x ∈ frontier (regularSupport K T) →
        ∃ g ∈ G, x ∈ segment ℝ ((g.1 : Plane) + g.2.1)
          ((g.1 : Plane) + g.2.2) := by
  obtain ⟨ρ, hρ, G, hvalid, hstar⟩ := bgcorner_endpoint_localFiniteBoundaryStar K T hp v
  refine ⟨ρ, hρ, G, hvalid, ?_⟩
  intro x hxball hxfront
  have hclosed := placed_support_union_closed hp
  have hopenSub : openUnion K T ⊆ ⋃ t : T, (t : Plane) +ᵥ K.support := by
    intro y hy
    obtain ⟨t, hty⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨t, vadd_set_mono interior_subset hty⟩
  have hDsub : regularSupport K T ⊆ ⋃ t : T, (t : Plane) +ᵥ K.support :=
    interior_subset.trans (closure_minimal hopenSub hclosed)
  have hxinClosure : x ∈ closure (regularSupport K T) := frontier_subset_closure hxfront
  have hxUnion : x ∈ ⋃ t : T, (t : Plane) +ᵥ K.support :=
    hclosed.closure_subset (closure_mono hDsub hxinClosure)
  obtain ⟨t, hxtile⟩ := Set.mem_iUnion.mp hxUnion
  have hxnotD : x ∉ regularSupport K T := by
    intro hxD
    have hopenD : IsOpen (regularSupport K T) := isOpen_interior
    have hxintD : x ∈ interior (regularSupport K T) := by
      rw [hopenD.interior_eq]
      exact hxD
    exact (Set.disjoint_left.mp disjoint_interior_frontier) hxintD hxfront
  have hxnotInteriorTile : x ∉ interior ((t : Plane) +ᵥ K.support) := by
    intro hxint
    have hxD : x ∈ regularSupport K T := by
      have hxopen : x ∈ (t : Plane) +ᵥ K.openCarrier := by
        simpa [interior_vadd, PolygonalRegion.openCarrier] using hxint
      have hopen : IsOpen (openUnion K T) :=
        isOpen_iUnion fun s : T => (Homeomorph.addLeft (s : Plane)).isOpen_image.mpr
          isOpen_interior
      have hunion : openUnion K T ⊆ regularSupport K T := by
        intro y hy
        change y ∈ interior (closure (openUnion K T))
        apply interior_mono subset_closure
        rw [mem_interior_iff_mem_nhds]
        exact hopen.mem_nhds hy
      exact hunion (Set.mem_iUnion.mpr ⟨t, hxopen⟩)
    exact hxnotD hxD
  have htileClosed : IsClosed ((t : Plane) +ᵥ K.support) :=
    K.isPolygonal.isClosed.vadd (t : Plane)
  have htileFront : x ∈ frontier ((t : Plane) +ᵥ K.support) := by
    rw [htileClosed.frontier_eq]
    exact ⟨hxtile, hxnotInteriorTile⟩
  obtain ⟨g, hgG, hxseg⟩ := hstar t x hxball htileFront
  exact ⟨(t, g), by simpa using hgG, hxseg⟩

private theorem bgcorner_frontier_free_halfballs_have_constant_colour
    {D : Set Plane} (π : Plane →L[ℝ] ℝ) (v : Plane) (r : ℝ)
    (hlevel : ∀ y ∈ Metric.ball v r, y ∈ frontier D → π y = π v) :
    (Metric.ball v r ∩ {y | π v < π y} ⊆ interior D ∨
      Metric.ball v r ∩ {y | π v < π y} ⊆ interior Dᶜ) ∧
    (Metric.ball v r ∩ {y | π y < π v} ⊆ interior D ∨
      Metric.ball v r ∩ {y | π y < π v} ⊆ interior Dᶜ) := by
  let P : Set Plane := Metric.ball v r ∩ {y | π v < π y}
  let M : Set Plane := Metric.ball v r ∩ {y | π y < π v}
  have hPpre : IsPreconnected P :=
    (convex_ball v r).inter (convex_halfSpace_gt π.toLinearMap.isLinear (π v)) |>.isPreconnected
  have hMpre : IsPreconnected M :=
    (convex_ball v r).inter (convex_halfSpace_lt π.toLinearMap.isLinear (π v)) |>.isPreconnected
  have hPfront : Disjoint P (frontier D) := by
    rw [Set.disjoint_left]
    intro y hy hyfront
    change y ∈ Metric.ball v r ∧ π v < π y at hy
    exact (ne_of_gt hy.2) (hlevel y hy.1 hyfront)
  have hMfront : Disjoint M (frontier D) := by
    rw [Set.disjoint_left]
    intro y hy hyfront
    change y ∈ Metric.ball v r ∧ π y < π v at hy
    exact (ne_of_lt hy.2) (hlevel y hy.1 hyfront)
  exact ⟨Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      hPpre hPfront,
    Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      hMpre hMfront⟩

private theorem bgcorner_affine_level_complement_dense
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (δ : Submodule ℝ Plane)
    (hker : LinearMap.ker π.toLinearMap = δ) (v : Plane) :
    Dense {y : Plane | π y ≠ π v} := by
  let C : Set Plane := {y | π y = π v}
  have hδne : δ ≠ ⊤ := by
    intro h
    obtain ⟨n, hn⟩ := hπ 1
    have hnδ : n ∈ δ := by rw [h]; exact Set.mem_univ n
    have hnker : n ∈ LinearMap.ker π.toLinearMap := hker.symm ▸ hnδ
    have : π n = 0 := LinearMap.mem_ker.mp hnker
    rw [hn] at this
    norm_num at this
  have hδint : interior (δ : Set Plane) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hδne (Submodule.eq_top_of_nonempty_interior' δ ⟨y, hy⟩)
  have hCline : C = v +ᵥ (δ : Set Plane) := by
    ext y
    constructor
    · intro hy
      apply Set.mem_vadd_set.mpr
      refine ⟨y - v, ?_, ?_⟩
      · rw [← hker]
        apply LinearMap.mem_ker.mpr
        change π (y - v) = 0
        rw [map_sub, hy, sub_self]
      · change v + (y - v) = y
        abel
    · rintro ⟨z, hz, rfl⟩
      change π (v + z) = π v
      rw [map_add]
      have hzker' : z ∈ LinearMap.ker π.toLinearMap := by
        rw [hker]
        exact hz
      have hzker : π z = 0 := LinearMap.mem_ker.mp hzker'
      rw [hzker]
      simp
  have hCint : interior C = ∅ := by
    rw [hCline, interior_vadd]
    simp [hδint]
  change Dense Cᶜ
  exact interior_eq_empty_iff_dense_compl.mp hCint

private theorem bgcorner_regularOpen_frontier_not_both_halfballs_occupied
    {D : Set Plane} (hregular : interior (closure D) = D)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (δ : Submodule ℝ Plane) (hker : LinearMap.ker π.toLinearMap = δ)
    (v : Plane) (hv : v ∈ frontier D) (r : ℝ) (hr : 0 < r) :
    ¬((Metric.ball v r ∩ {y | π v < π y} ⊆ D) ∧
      (Metric.ball v r ∩ {y | π y < π v} ⊆ D)) := by
  intro hbias
  have hdense := bgcorner_affine_level_complement_dense π hπ δ hker v
  have hballClosure : Metric.ball v r ⊆ closure D := by
    intro y hy
    rw [Metric.mem_closure_iff]
    intro ε hε
    let U : Set Plane := Metric.ball y ε ∩ Metric.ball v r
    have hUopen : IsOpen U := Metric.isOpen_ball.inter Metric.isOpen_ball
    have hyU : y ∈ U := ⟨Metric.mem_ball_self hε, hy⟩
    obtain ⟨z, hzU, hzoff⟩ := hdense.inter_open_nonempty U hUopen ⟨y, hyU⟩
    have hzD : z ∈ D := by
      rcases lt_or_gt_of_ne hzoff with hlt | hgt
      · exact hbias.2 ⟨hzU.2, hlt⟩
      · exact hbias.1 ⟨hzU.2, hgt⟩
    exact ⟨z, hzD, by simpa [dist_comm] using Metric.mem_ball.mp hzU.1⟩
  have hvint : v ∈ interior (closure D) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds v hr) hballClosure
  have hDopen : IsOpen D := by rw [← hregular]; exact isOpen_interior
  have hvD : v ∈ D := by rw [← hregular]; exact hvint
  have hvintD : v ∈ interior D := by rw [hDopen.interior_eq]; exact hvD
  exact (Set.disjoint_left.mp disjoint_interior_frontier) hvintD hv

private theorem bgcorner_regularOpen_frontier_not_both_halfballs_vacant
    {D : Set Plane} (hregular : interior (closure D) = D)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (δ : Submodule ℝ Plane) (hker : LinearMap.ker π.toLinearMap = δ)
    (v : Plane) (hv : v ∈ frontier D) (r : ℝ) (hr : 0 < r) :
    ¬((Metric.ball v r ∩ {y | π v < π y} ⊆ Dᶜ) ∧
      (Metric.ball v r ∩ {y | π y < π v} ⊆ Dᶜ)) := by
  intro hbias
  have hdense := bgcorner_affine_level_complement_dense π hπ δ hker v
  have hDopen : IsOpen D := by rw [← hregular]; exact isOpen_interior
  have havoid : Disjoint (Metric.ball v r) D := by
    rw [Set.disjoint_left]
    intro y hyball hyD
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hDopen.mem_nhds hyD)
    have hrmargin : 0 < r - dist y v := by
      have hdist := Metric.mem_ball.mp hyball
      linarith
    let ρ := min ε (r - dist y v)
    have hρ : 0 < ρ := lt_min hε hrmargin
    obtain ⟨z, hz, hzoff⟩ := hdense.inter_open_nonempty (Metric.ball y ρ)
      Metric.isOpen_ball ⟨y, Metric.mem_ball_self hρ⟩
    have hzball : z ∈ Metric.ball v r := by
      rw [Metric.mem_ball]
      calc
        dist z v ≤ dist z y + dist y v := dist_triangle _ _ _
        _ < ρ + dist y v := by nlinarith [Metric.mem_ball.mp hz]
        _ ≤ r := by
          dsimp [ρ]
          nlinarith [min_le_right ε (r - dist y v)]
    have hzε : dist z y < ε := lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left _ _)
    have hzD : z ∈ D := hball (by rw [Metric.mem_ball]; exact hzε)
    rcases lt_or_gt_of_ne hzoff with hlt | hgt
    · exact hbias.2 ⟨hzball, hlt⟩ hzD
    · exact hbias.1 ⟨hzball, hgt⟩ hzD
  obtain ⟨y, hyD, hyv⟩ :=
    (Metric.mem_closure_iff.mp (frontier_subset_closure hv)) r hr
  exact (Set.disjoint_left.mp havoid) (by simpa [Metric.mem_ball, dist_comm] using hyv) hyD

private theorem bgcorner_regularOpen_frontier_halfballs_have_opposite_colours
    {D : Set Plane} (hregular : interior (closure D) = D)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (δ : Submodule ℝ Plane) (hker : LinearMap.ker π.toLinearMap = δ)
    (v : Plane) (hv : v ∈ frontier D) (r : ℝ) (hr : 0 < r)
    (hlevel : ∀ y ∈ Metric.ball v r, y ∈ frontier D → π y = π v) :
    ((Metric.ball v r ∩ {y | π v < π y} ⊆ D ∧
      Metric.ball v r ∩ {y | π y < π v} ⊆ Dᶜ) ∨
     (Metric.ball v r ∩ {y | π v < π y} ⊆ Dᶜ ∧
      Metric.ball v r ∩ {y | π y < π v} ⊆ D)) := by
  have hclass := bgcorner_frontier_free_halfballs_have_constant_colour π v r hlevel
  have hP : Metric.ball v r ∩ {y | π v < π y} ⊆ D ∨
      Metric.ball v r ∩ {y | π v < π y} ⊆ Dᶜ := by
    rcases hclass.1 with h | h
    · exact Or.inl fun y hy => interior_subset (h hy)
    · exact Or.inr fun y hy => interior_subset (h hy)
  have hM : Metric.ball v r ∩ {y | π y < π v} ⊆ D ∨
      Metric.ball v r ∩ {y | π y < π v} ⊆ Dᶜ := by
    rcases hclass.2 with h | h
    · exact Or.inl fun y hy => interior_subset (h hy)
    · exact Or.inr fun y hy => interior_subset (h hy)
  have hnotD := bgcorner_regularOpen_frontier_not_both_halfballs_occupied
    hregular π hπ δ hker v hv r hr
  have hnotC := bgcorner_regularOpen_frontier_not_both_halfballs_vacant
    hregular π hπ δ hker v hv r hr
  rcases hP with hP | hP <;> rcases hM with hM | hM
  · exact False.elim (hnotD ⟨hP, hM⟩)
  · exact Or.inl ⟨hP, hM⟩
  · exact Or.inr ⟨hP, hM⟩
  · exact False.elim (hnotC ⟨hP, hM⟩)

private theorem bgcorner_affine_level_point_has_nearby_points_on_both_sides
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (y : Plane) (ε : ℝ) (hε : 0 < ε) :
    ∃ zplus zminus : Plane, dist zplus y < ε ∧ dist zminus y < ε ∧
      π y < π zplus ∧ π zminus < π y := by
  obtain ⟨n, hn⟩ := hπ 1
  let t : ℝ := ε / (‖n‖ + 1)
  have ht : 0 < t := by dsimp [t]; positivity
  have hsmall : t * ‖n‖ < ε := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < ‖n‖ + 1)).2
    nlinarith [norm_nonneg n, hε]
  refine ⟨y + t • n, y - t • n, ?_, ?_, ?_, ?_⟩
  · rw [dist_eq_norm]
    calc
      ‖(y + t • n) - y‖ = ‖t • n‖ := by congr 1 <;> abel
      _ = t * ‖n‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ < ε := hsmall
  · rw [dist_eq_norm]
    calc
      ‖(y - t • n) - y‖ = ‖-(t • n)‖ := by congr 1 <;> abel
      _ = t * ‖n‖ := by rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ < ε := hsmall
  · change π y < π (y + t • n)
    rw [map_add, map_smul, hn, smul_eq_mul, mul_one]
    exact lt_add_of_pos_right _ ht
  · change π (y - t • n) < π y
    rw [map_sub, map_smul, hn, smul_eq_mul, mul_one]
    linarith

private theorem bgcorner_opposite_halfballs_force_level_points_to_frontier
    {D : Set Plane} (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (v : Plane) (r : ℝ) (hr : 0 < r)
    (hcolours : ((Metric.ball v r ∩ {z | π v < π z} ⊆ D) ∧
      (Metric.ball v r ∩ {z | π z < π v} ⊆ Dᶜ)) ∨
      ((Metric.ball v r ∩ {z | π v < π z} ⊆ Dᶜ) ∧
      (Metric.ball v r ∩ {z | π z < π v} ⊆ D)))
    {y : Plane} (hy : y ∈ Metric.ball v (r / 2)) (hylevel : π y = π v) :
    y ∈ frontier D := by
  rw [frontier_eq_closure_inter_closure]
  constructor
  · rw [Metric.mem_closure_iff]
    intro ε hε
    have hmargin : 0 < r - dist y v := by
      have hy' := Metric.mem_ball.mp hy
      nlinarith [hr]
    let ρ := min ε (r - dist y v)
    have hρ : 0 < ρ := lt_min hε hmargin
    have hballOf : ∀ z, dist z y < ρ → z ∈ Metric.ball v r := by
      intro z hdist
      rw [Metric.mem_ball]
      calc
        dist z v ≤ dist z y + dist y v := dist_triangle _ _ _
        _ < ρ + dist y v := by nlinarith
        _ ≤ r := by dsimp [ρ]; nlinarith [min_le_right ε (r - dist y v)]
    have hcloseOf : ∀ z, dist z y < ρ → dist y z < ε := by
      intro z hdist
      have hh := lt_of_lt_of_le hdist (min_le_left ε (r - dist y v))
      simpa [dist_comm] using hh
    obtain ⟨zplus, zminus, hdistplus, hdistminus, hpos, hneg⟩ :=
      bgcorner_affine_level_point_has_nearby_points_on_both_sides π hπ y ρ hρ
    rcases hcolours with ⟨hplus, _⟩ | ⟨_, hminus⟩
    · have hzD : zplus ∈ D := hplus ⟨hballOf zplus hdistplus,
        by rw [← hylevel]; exact hpos⟩
      exact ⟨zplus, hzD, hcloseOf zplus hdistplus⟩
    · have hneg' : π zminus < π v := by rw [← hylevel]; exact hneg
      have hzD : zminus ∈ D := hminus ⟨hballOf zminus hdistminus, hneg'⟩
      exact ⟨zminus, hzD, hcloseOf zminus hdistminus⟩
  · rw [Metric.mem_closure_iff]
    intro ε hε
    have hmargin : 0 < r - dist y v := by
      have hy' := Metric.mem_ball.mp hy
      nlinarith [hr]
    let ρ := min ε (r - dist y v)
    have hρ : 0 < ρ := lt_min hε hmargin
    have hballOf : ∀ z, dist z y < ρ → z ∈ Metric.ball v r := by
      intro z hdist
      rw [Metric.mem_ball]
      calc
        dist z v ≤ dist z y + dist y v := dist_triangle _ _ _
        _ < ρ + dist y v := by nlinarith
        _ ≤ r := by dsimp [ρ]; nlinarith [min_le_right ε (r - dist y v)]
    have hcloseOf : ∀ z, dist z y < ρ → dist y z < ε := by
      intro z hdist
      have hh := lt_of_lt_of_le hdist (min_le_left ε (r - dist y v))
      simpa [dist_comm] using hh
    obtain ⟨zplus, zminus, hdistplus, hdistminus, hpos, hneg⟩ :=
      bgcorner_affine_level_point_has_nearby_points_on_both_sides π hπ y ρ hρ
    rcases hcolours with ⟨_, hminus⟩ | ⟨hplus, _⟩
    · have hneg' : π zminus < π v := by rw [← hylevel]; exact hneg
      have hzC : zminus ∈ Dᶜ := hminus ⟨hballOf zminus hdistminus, hneg'⟩
      exact ⟨zminus, hzC, hcloseOf zminus hdistminus⟩
    · have hpos' : π v < π zplus := by rw [← hylevel]; exact hpos
      have hzC : zplus ∈ Dᶜ := hplus ⟨hballOf zplus hdistplus, hpos'⟩
      exact ⟨zplus, hzC, hcloseOf zplus hdistplus⟩

private theorem bgcorner_regularOpen_frontier_locally_contained_level_is_straight
    {D : Set Plane} (hDopen : IsOpen D)
    (hregular : interior (closure D) = D)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (δ : Submodule ℝ Plane) (hδ : Module.finrank ℝ δ = 1)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (v : Plane) (hv : v ∈ frontier D) (r : ℝ) (hr : 0 < r)
    (hsubset : ∀ y ∈ Metric.ball v r, y ∈ frontier D → π y = π v) :
    Tiling.BoundaryLocallyStraightAt D v := by
  have hcolours := bgcorner_regularOpen_frontier_halfballs_have_opposite_colours
    hregular π hπ δ hker v hv r hr hsubset
  let L : AffineSubspace ℝ Plane := AffineSubspace.mk' v δ
  have hmemL : ∀ y : Plane, y ∈ L ↔ π y = π v := by
    intro y
    rw [AffineSubspace.mem_mk']
    change y - v ∈ δ ↔ π y = π v
    rw [← hker, LinearMap.mem_ker, map_sub]
    exact sub_eq_zero
  refine ⟨L, AffineSubspace.self_mem_mk' v δ, ?_, ?_⟩
  · rw [AffineSubspace.direction_mk']
    exact hδ
  · filter_upwards [Metric.ball_mem_nhds v (by linarith : 0 < r / 2)] with y hy
    constructor
    · intro hyfront
      exact (hmemL y).mpr (hsubset y (Metric.ball_subset_ball (by linarith) hy) hyfront)
    · intro hyL
      exact bgcorner_opposite_halfballs_force_level_points_to_frontier π hπ v r hr hcolours
        hy ((hmemL y).mp hyL)

private theorem bgcorner_nonStraight_frontier_point_has_offLevel_points
    {D : Set Plane} (hDopen : IsOpen D)
    (hregular : interior (closure D) = D)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (δ : Submodule ℝ Plane) (hδ : Module.finrank ℝ δ = 1)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (v : Plane) (hv : v ∈ frontier D)
    (hnonstr : ¬Tiling.BoundaryLocallyStraightAt D v) :
    ∀ r : ℝ, 0 < r → ∃ y ∈ Metric.ball v r, y ∈ frontier D ∧ π y ≠ π v := by
  intro r hr
  by_contra hnone
  have hcontained : ∀ y ∈ Metric.ball v r, y ∈ frontier D → π y = π v := by
    intro y hyball hyfront
    by_contra hneq
    exact hnone ⟨y, hyball, hyfront, hneq⟩
  exact hnonstr (bgcorner_regularOpen_frontier_locally_contained_level_is_straight
    hDopen hregular π hπ δ hδ hker v hv r hr hcontained)

private theorem bgcorner_smooth_transverse_frontier_germ_cuts_slice
    {D : Set Plane} (hregular : interior (closure D) = D)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (δ : Submodule ℝ Plane) (hδ : Module.finrank ℝ δ = 1)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (q : Plane) (hq : q ∈ frontier D)
    (L : AffineSubspace ℝ Plane) (hqL : q ∈ L)
    (hLdim : Module.finrank ℝ L.direction = 1)
    (hgerm : ∀ᶠ z in 𝓝 q, (z ∈ frontier D ↔ z ∈ L))
    (w : Plane) (hw : w ∈ δ) (hwtrans : w ∉ L.direction) :
    ∃ t : ℝ, 0 < t ∧
      ((q + t • w ∈ interior D ∧ q - t • w ∈ interior Dᶜ) ∨
       (q + t • w ∈ interior Dᶜ ∧ q - t • w ∈ interior D)) := by
  obtain ⟨ψ, hlevel⟩ := AffineSubspace.exists_levelSet_coordinate L q hqL hLdim
  have hkerψ : LinearMap.ker ψ.toLinearMap = L.direction := by
    ext x
    change ψ x = 0 ↔ x ∈ L.direction
    constructor
    · intro hx
      have hqplus : q + x ∈ L := (hlevel (q + x)).2 (by rw [map_add, hx]; simp)
      exact (AffineSubspace.vadd_mem_iff_mem_direction x hqL).mp
        (by simpa [vadd_eq_add, add_comm] using hqplus)
    · intro hx
      have hqplus := AffineSubspace.vadd_mem_of_mem_direction hx hqL
      have heq := (hlevel (q + x)).1 (by simpa [vadd_eq_add, add_comm] using hqplus)
      rw [map_add] at heq
      linarith
  have hψw : ψ w ≠ 0 := by
    intro hzero
    have hwker : w ∈ LinearMap.ker ψ.toLinearMap := LinearMap.mem_ker.mpr hzero
    exact hwtrans (hkerψ ▸ hwker)
  have hψsurj : Function.Surjective ψ := by
    intro a
    refine ⟨(a / ψ w) • w, ?_⟩
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ a hψw
  have hlocal : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.ball q r,
      z ∈ frontier D → ψ z = ψ q := by
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hgerm
    refine ⟨r, hr, ?_⟩
    intro z hzball hzfront
    have hzL := (hball hzball).mp hzfront
    exact (hlevel z).mp hzL
  obtain ⟨r, hr, hlocal⟩ := hlocal
  have hcolors := bgcorner_regularOpen_frontier_halfballs_have_opposite_colours
    hregular ψ hψsurj L.direction hkerψ q hq r hr hlocal
  have hclass := bgcorner_frontier_free_halfballs_have_constant_colour ψ q r hlocal
  have hinside : ((Metric.ball q r ∩ {z | ψ q < ψ z} ⊆ interior D) ∧
      (Metric.ball q r ∩ {z | ψ z < ψ q} ⊆ interior Dᶜ)) ∨
      ((Metric.ball q r ∩ {z | ψ q < ψ z} ⊆ interior Dᶜ) ∧
      (Metric.ball q r ∩ {z | ψ z < ψ q} ⊆ interior D)) := by
    rcases hcolors with ⟨hp, hm⟩ | ⟨hp, hm⟩
    · have hpint : Metric.ball q r ∩ {z | ψ q < ψ z} ⊆ interior D := by
        rcases hclass.1 with hi | ho
        · exact hi
        · intro z hz
          exact False.elim ((interior_subset (ho hz)) (hp hz))
      have hmint : Metric.ball q r ∩ {z | ψ z < ψ q} ⊆ interior Dᶜ := by
        rcases hclass.2 with hi | ho
        · intro z hz
          exact False.elim ((hm hz) (interior_subset (hi hz)))
        · exact ho
      exact Or.inl ⟨hpint, hmint⟩
    · have hpint : Metric.ball q r ∩ {z | ψ q < ψ z} ⊆ interior Dᶜ := by
        rcases hclass.1 with hi | ho
        · intro z hz
          exact False.elim ((hp hz) (interior_subset (hi hz)))
        · exact ho
      have hmint : Metric.ball q r ∩ {z | ψ z < ψ q} ⊆ interior D := by
        rcases hclass.2 with hi | ho
        · exact hi
        · intro z hz
          exact False.elim ((interior_subset (ho hz)) (hm hz))
      exact Or.inr ⟨hpint, hmint⟩
  let t : ℝ := r / (2 * (‖w‖ + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  have htnorm : t * ‖w‖ < r := by
    calc
      t * ‖w‖ < t * (‖w‖ + 1) := mul_lt_mul_of_pos_left (by linarith [norm_nonneg w]) ht
      _ = r / 2 := by dsimp [t]; field_simp
      _ < r := by linarith
  have hnearPlus : q + t • w ∈ Metric.ball q r := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖(q + t • w) - q‖ = ‖t • w‖ := by congr 1 <;> abel
      _ = t * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ < r := htnorm
  have hnearMinus : q - t • w ∈ Metric.ball q r := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖(q - t • w) - q‖ = ‖-(t • w)‖ := by congr 1 <;> abel
      _ = t * ‖w‖ := by rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ < r := htnorm
  rcases hinside with ⟨hplus, hminus⟩ | ⟨hplus, hminus⟩
  · rcases lt_or_gt_of_ne hψw with hneg | hpos
    · refine ⟨t, ht, Or.inr ⟨?_, ?_⟩⟩
      · apply hminus ⟨hnearPlus, ?_⟩
        change ψ (q + t • w) < ψ q
        rw [map_add, map_smul, smul_eq_mul]
        have : t * ψ w < 0 := mul_neg_of_pos_of_neg ht hneg
        linarith
      · apply hplus ⟨hnearMinus, ?_⟩
        change ψ q < ψ (q - t • w)
        rw [map_sub, map_smul, smul_eq_mul]
        have : 0 < -(t * ψ w) := by
          nlinarith [mul_pos ht (neg_pos.mpr hneg)]
        linarith
    · refine ⟨t, ht, Or.inl ⟨?_, ?_⟩⟩
      · apply hplus ⟨hnearPlus, ?_⟩
        change ψ q < ψ (q + t • w)
        rw [map_add, map_smul, smul_eq_mul]
        exact lt_add_of_pos_right _ (mul_pos ht hpos)
      · apply hminus ⟨hnearMinus, ?_⟩
        change ψ (q - t • w) < ψ q
        rw [map_sub, map_smul, smul_eq_mul]
        have : 0 < t * ψ w := mul_pos ht hpos
        linarith
  · rcases lt_or_gt_of_ne hψw with hneg | hpos
    · refine ⟨t, ht, Or.inl ⟨?_, ?_⟩⟩
      · apply hminus ⟨hnearPlus, ?_⟩
        change ψ (q + t • w) < ψ q
        rw [map_add, map_smul, smul_eq_mul]
        have : t * ψ w < 0 := mul_neg_of_pos_of_neg ht hneg
        linarith
      · apply hplus ⟨hnearMinus, ?_⟩
        change ψ q < ψ (q - t • w)
        rw [map_sub, map_smul, smul_eq_mul]
        have : 0 < -(t * ψ w) := by
          nlinarith [mul_pos ht (neg_pos.mpr hneg)]
        linarith
    · refine ⟨t, ht, Or.inr ⟨?_, ?_⟩⟩
      · apply hplus ⟨hnearPlus, ?_⟩
        change ψ q < ψ (q + t • w)
        rw [map_add, map_smul, smul_eq_mul]
        exact lt_add_of_pos_right _ (mul_pos ht hpos)
      · apply hminus ⟨hnearMinus, ?_⟩
        change ψ (q - t • w) < ψ q
        rw [map_sub, map_smul, smul_eq_mul]
        have : 0 < t * ψ w := mul_pos ht hpos
        linarith

private theorem bgcorner_open_set_contains_slice_interval
    {U : Set Plane} (hU : IsOpen U) (q w : Plane) (t : ℝ)
    (htpoint : q + t • w ∈ U) (hw : w ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, |s - t| < η → q + s • w ∈ U := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds htpoint)
  let η : ℝ := r / (‖w‖ + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro s hs
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  have hnorm : ‖(q + s • w) - (q + t • w)‖ = |s - t| * ‖w‖ := by
    rw [show (q + s • w) - (q + t • w) = (s - t) • w by module,
      norm_smul, Real.norm_eq_abs]
  rw [hnorm]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  dsimp [η] at hs ⊢
  have hratio : r / (‖w‖ + 1) * ‖w‖ < r := by
    have hsmall : ‖w‖ < ‖w‖ + 1 := by linarith [norm_nonneg w]
    have hmul := mul_lt_mul_of_pos_left hsmall (by positivity : 0 < r / (‖w‖ + 1))
    have hid : r / (‖w‖ + 1) * (‖w‖ + 1) = r := by
      rw [div_mul_cancel₀ r (by positivity : ‖w‖ + 1 ≠ 0)]
    rw [hid] at hmul
    exact hmul
  have hprod : |s - t| * ‖w‖ < r := by
    calc
      |s - t| * ‖w‖ < (r / (‖w‖ + 1)) * ‖w‖ :=
        mul_lt_mul_of_pos_right hs hwpos
      _ < r := hratio
  exact hprod

private theorem bgcorner_finite_set_has_positive_gap_around_mem
    (C : Set ℝ) (hCfinite : C.Finite) (m : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ C, x ≠ m → η ≤ |x - m| := by
  let V : Set ℝ := {x | x ∈ C ∧ x ≠ m}
  let D : Set ℝ := (fun x : ℝ => |x - m|) '' V
  have hVfinite : V.Finite := hCfinite.subset (by intro x hx; exact hx.1)
  have hDfinite : D.Finite := hVfinite.image (fun x : ℝ => |x - m|)
  by_cases hD : D.Nonempty
  · obtain ⟨a, ha, hleast⟩ := Set.exists_min_image D id hDfinite hD
    obtain ⟨y, hy, rfl⟩ := ha
    have hapos : 0 < |y - m| := abs_pos.mpr (sub_ne_zero.mpr hy.2)
    refine ⟨|y - m|, hapos, ?_⟩
    intro x hx hxne
    have hxD : |x - m| ∈ D := ⟨x, ⟨hx, hxne⟩, rfl⟩
    exact hleast _ hxD
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx hxne
    have hxD : |x - m| ∈ D := ⟨x, ⟨hx, hxne⟩, rfl⟩
    exact False.elim (hD ⟨|x - m|, hxD⟩)

private theorem bgcorner_affine_line_set_eq_anchor_span
    (L : AffineSubspace ℝ Plane) (q u : Plane) (hq : q ∈ L)
    (hLdim : Module.finrank ℝ L.direction = 1)
    (hu : u ∈ L.direction) (hune : u ≠ 0) :
    (L : Set Plane) = q +ᵥ (Submodule.span ℝ ({u} : Set Plane) : Set Plane) := by
  have hdirspan := eq_span_singleton_of_mem_of_finrank_eq_one hLdim hu hune
  have hLdirection : (L : Set Plane) = q +ᵥ (L.direction : Set Plane) := by
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change z ∈ L ↔ -q + z ∈ L.direction
    constructor
    · intro hz
      have hz' := L.vsub_mem_direction hz hq
      change z - q ∈ L.direction at hz'
      convert hz' using 1 <;> abel
    · intro hz
      have hmem := L.vadd_mem_of_mem_direction hz hq
      change (-q + z) + q ∈ L at hmem
      have heq : (-q + z) + q = z := by abel
      simpa [heq] using hmem
  rw [hLdirection, hdirspan]

private theorem bgcorner_line_parameter_segment_preimage_finite
    (π : Plane →L[ℝ] ℝ) (k w a b : Plane) (hw : w ≠ 0)
    (hπw : π w = 0) (hka : π k ≠ π a) (hkb : π k ≠ π b) :
    {r : ℝ | k + r • w ∈ segment ℝ a b}.Finite := by
  apply Set.Subsingleton.finite
  intro r hr s hs
  rw [segment_eq_image_lineMap] at hr hs
  obtain ⟨α, _, hα⟩ := hr
  obtain ⟨β, _, hβ⟩ := hs
  have hline (t : ℝ) : π (k + t • w) = π k := by
    rw [map_add, map_smul, hπw, smul_zero, add_zero]
  have hαπ := congrArg π hα
  have hβπ := congrArg π hβ
  rw [AffineMap.lineMap_apply_module] at hαπ hβπ
  simp only [map_add, map_smul, smul_eq_mul, hline] at hαπ hβπ
  have hab : π a ≠ π b := by
    intro hab
    have hak' : π a = π k := by rw [hab] at hαπ; nlinarith
    exact hka hak'.symm
  have hαβ : α = β := by
    have hdiff : (α - β) * (π b - π a) = 0 := by nlinarith [hαπ, hβπ]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right (sub_ne_zero.mpr hab.symm))
  have hrs : k + r • w = k + s • w := by rw [← hα, ← hβ, hαβ]
  exact smul_left_injective ℝ hw (add_left_cancel hrs)

private theorem bgcorner_actual_noncritical_frontier_germ_not_delta
    (K : PolygonalRegion) (T : Set Plane)
    (hp : IsPacking K.prototileFamily (K.placements T))
    (π : Plane →L[ℝ] ℝ) (δ : Submodule ℝ Plane)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hline : ∃ a : Plane, ∀ t ∈ T, t - a ∈ δ) (s : Plane) (hs : s ∈ T)
    (q : Plane) (hqfront : q ∈ frontier (regularSupport K T))
    (x : ℝ) (hqcoord : π q = π s + x)
    (hxcritical : x ∉ π '' vertexSet K.support)
    (L : AffineSubspace ℝ Plane) (hqL : q ∈ L)
    (hLdim : Module.finrank ℝ L.direction = 1)
    (hgerm : ∀ᶠ z in 𝓝 q, (z ∈ frontier (regularSupport K T) ↔ z ∈ L)) :
    L.direction ≠ δ := by
  classical
  intro hLδ
  have hδrank : Module.finrank ℝ δ = 1 := by rw [← hLδ]; exact hLdim
  have hδbot : δ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hδrank
    exact Nat.zero_ne_one hδrank
  obtain ⟨w, hw, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδbot
  have hwL : w ∈ L.direction := hLδ.symm ▸ hw
  have hπw : π w = 0 := LinearMap.mem_ker.mp (hker ▸ hw)
  obtain ⟨ρ, hρ, G, hvalid, hcover⟩ :=
    bgcorner_actual_regularSupport_frontier_local_edge_cover K T hp q
  obtain ⟨rL, hrL, hlocal⟩ := Metric.eventually_nhds_iff.mp hgerm
  let R : ℝ := min ρ rL
  let η : ℝ := R / (2 * (‖w‖ + 1))
  have hη : 0 < η := by dsimp [η, R]; positivity
  have hR : 0 < R := lt_min hρ hrL
  have hηsmall : η * ‖w‖ < R := by
    dsimp [η]
    calc
      R / (2 * (‖w‖ + 1)) * ‖w‖ <
          R / (2 * (‖w‖ + 1)) * (‖w‖ + 1) :=
        mul_lt_mul_of_pos_left (by linarith [norm_nonneg w]) (by positivity)
      _ = R / 2 := by field_simp
      _ < R := by linarith
  let P : T × (Plane × Plane) → Set ℝ := fun g =>
    {r | q + r • w ∈ segment ℝ ((g.1 : Plane) + g.2.1) ((g.1 : Plane) + g.2.2)}
  have hPfinite : ∀ g ∈ G, (P g).Finite := by
    intro g hg
    obtain ⟨a₀, ha₀⟩ := hline
    have hsδ : s - a₀ ∈ δ := ha₀ s hs
    have htδ : (g.1 : Plane) - a₀ ∈ δ := ha₀ g.1 g.1.2
    have hs0 : π (s - a₀) = 0 :=
      LinearMap.mem_ker.mp (hker.symm ▸ hsδ)
    have ht0 : π ((g.1 : Plane) - a₀) = 0 :=
      LinearMap.mem_ker.mp (hker.symm ▸ htδ)
    have htcoord : π (g.1 : Plane) = π s := by
      rw [map_sub] at hs0 ht0
      linarith
    have hkcoord : π (q - (g.1 : Plane)) = x := by
      rw [map_sub, hqcoord, htcoord]
      ring
    have hka : π (q - (g.1 : Plane)) ≠ π g.2.1 := by
      intro heq
      apply hxcritical
      refine ⟨g.2.1, hvalid g hg |>.2.2.1, ?_⟩
      rw [← hkcoord, heq]
    have hkb : π (q - (g.1 : Plane)) ≠ π g.2.2 := by
      intro heq
      apply hxcritical
      refine ⟨g.2.2, hvalid g hg |>.2.2.2.1, ?_⟩
      rw [← hkcoord, heq]
    have hfinite := bgcorner_line_parameter_segment_preimage_finite π
      (q - (g.1 : Plane)) w g.2.1 g.2.2 hwne hπw hka hkb
    apply hfinite.subset
    intro r hr
    change q + r • w ∈ segment ℝ ((g.1 : Plane) + g.2.1)
      ((g.1 : Plane) + g.2.2) at hr
    have htranslated : q - (g.1 : Plane) + r • w ∈ segment ℝ g.2.1 g.2.2 := by
      have hbase : (g.1 : Plane) + (q - (g.1 : Plane) + r • w) = q + r • w := by module
      have hr' : (g.1 : Plane) + (q - (g.1 : Plane) + r • w) ∈
          segment ℝ ((g.1 : Plane) + g.2.1) ((g.1 : Plane) + g.2.2) := by
        rw [hbase]
        exact hr
      rw [mem_segment_translate ℝ (g.1 : Plane)] at hr'
      exact hr'
    exact htranslated
  have hfiniteUnion : (⋃ g ∈ G, P g).Finite := G.finite_toSet.biUnion hPfinite
  have hinterval : Set.Ioo (-η) η ⊆ ⋃ g ∈ G, P g := by
    intro r hr
    have hrabs : |r| < η := abs_lt.mpr ⟨hr.1, hr.2⟩
    have hdist : dist (q + r • w) q < R := by
      rw [dist_eq_norm]
      have hsub : (q + r • w) - q = r • w := by module
      rw [hsub, norm_smul, Real.norm_eq_abs]
      calc
        |r| * ‖w‖ < η * ‖w‖ := mul_lt_mul_of_pos_right hrabs (norm_pos_iff.mpr hwne)
        _ < R := hηsmall
    have hballρ : q + r • w ∈ Metric.ball q ρ := by
      rw [Metric.mem_ball]
      dsimp [R] at hdist ⊢
      exact hdist.trans_le (min_le_left _ _)
    have hballL : q + r • w ∈ Metric.ball q rL := by
      rw [Metric.mem_ball]
      dsimp [R] at hdist ⊢
      exact hdist.trans_le (min_le_right _ _)
    have hrLmem : q + r • w ∈ L := by
      have hrwL : r • w ∈ L.direction := hLδ ▸ δ.smul_mem r hw
      have hdir := L.vadd_mem_of_mem_direction hrwL hqL
      simpa [vadd_eq_add, add_comm] using hdir
    have hrfront : q + r • w ∈ frontier (regularSupport K T) :=
      (hlocal hballL).2 hrLmem
    obtain ⟨g, hg, hrg⟩ := hcover (q + r • w) hballρ hrfront
    exact Set.mem_iUnion₂.mpr ⟨g, hg, hrg⟩
  have hfiniteIoo : (Set.Ioo (-η) η).Finite := hfiniteUnion.subset hinterval
  exact (Set.Ioo_infinite (by linarith)).not_finite hfiniteIoo

private theorem bgcorner_actual_minimum_corner_has_upper_transverse_germ
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : ∃ a : Plane, ∀ t ∈ S, t - a ∈ δ)
    (s : Plane) (hs : s ∈ S)
    (v : Plane) (hv : v ∈ properVertices (regularSupport K S))
    (hmin : ∀ u ∈ properVertices (regularSupport K S), π v ≤ π u) :
    ∃ η : ℝ, ∃ q : Plane, 0 < η ∧ q ∈ frontier (regularSupport K S) ∧
      π v < π q ∧ π q < π v + η ∧
      (∀ u ∈ properVertices (regularSupport K S), π v < π u → π v + η ≤ π u) ∧
      ∃ L : AffineSubspace ℝ Plane, q ∈ L ∧
        Module.finrank ℝ L.direction = 1 ∧ L.direction ≠ δ ∧
        (∀ᶠ z in 𝓝 q, (z ∈ frontier (regularSupport K S) ↔ z ∈ (L : Set Plane))) := by
  classical
  let D := regularSupport K S
  let c₀ : ℝ := π v - π s
  let C : Set ℝ := π '' vertexSet K.support
  have hCfinite : C.Finite := K.isPolygonal.vertexSet_finite.image π
  obtain ⟨ηC, hηC, hCgap⟩ := bgcorner_finite_set_has_positive_gap_around_mem C hCfinite c₀
  let W : Set ℝ := π '' properVertices (regularSupport K S)
  have hWfinite : W.Finite := lineProperVertices_transverse_image_finite π hker hp hline hs
  have hcv : π v ∈ W := Set.mem_image_of_mem π hv
  obtain ⟨ηW, hηW, hWgap⟩ := bgcorner_finite_set_has_positive_gap_around_mem W hWfinite (π v)
  let η : ℝ := min ηC ηW
  have hη : 0 < η := lt_min hηC hηW
  have hWgapAbove : ∀ u ∈ properVertices (regularSupport K S),
      π v < π u → π v + η ≤ π u := by
    intro u hu hgreater
    have hsep := hWgap (π u) (Set.mem_image_of_mem π hu) (ne_of_gt hgreater)
    have hsep' : ηW ≤ π u - π v := by
      rw [abs_of_pos (sub_pos.mpr hgreater)] at hsep
      exact hsep
    dsimp [η]
    linarith [min_le_right ηC ηW]
  have hπdist : ‖π‖ * (η / (‖π‖ + 1)) < η := by
    calc
      ‖π‖ * (η / (‖π‖ + 1)) < (‖π‖ + 1) * (η / (‖π‖ + 1)) :=
        mul_lt_mul_of_pos_right (by linarith [norm_nonneg π]) (by positivity)
      _ = η := by field_simp
  let ρ : ℝ := η / (‖π‖ + 1)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hπne : π ≠ 0 := by
    intro hz
    obtain ⟨z, hzπ⟩ := hπ 1
    rw [hz] at hzπ
    norm_num at hzπ
  have hπnorm : 0 < ‖π‖ := norm_pos_iff.mpr hπne
  have hregular : interior (closure D) = D := by simp [D, regularSupport]
  have hopend : IsOpen D := isOpen_interior
  have hnstraight : ¬BoundaryLocallyStraightAt D v := hv.2
  obtain ⟨y, hyball, hyfront, hyoff⟩ :=
    bgcorner_nonStraight_frontier_point_has_offLevel_points hopend hregular π hπ δ hδ hker
      v hv.1 hnstraight ρ hρ
  have hcoordclose : |π y - π v| < η := by
    have hdist : ‖y - v‖ < ρ := by
      have := Metric.mem_ball.mp hyball
      simpa [dist_eq_norm, dist_comm] using this
    have hopenorm : ‖π (y - v)‖ ≤ ‖π‖ * ‖y - v‖ := π.le_opNorm _
    have habs : |π y - π v| = ‖π (y - v)‖ := by
      rw [map_sub, Real.norm_eq_abs]
    rw [habs]
    calc
      ‖π (y - v)‖ ≤ ‖π‖ * ‖y - v‖ := hopenorm
      _ < ‖π‖ * ρ := mul_lt_mul_of_pos_left hdist hπnorm
      _ < η := by simpa [ρ] using hπdist
  have hycoord : π y ≠ π v := hyoff
  have hycritical : π y - π s ∉ C := by
    intro hmem
    obtain ⟨k, hk, hky⟩ := hmem
    have hneq : π k ≠ c₀ := by
      intro heq
      apply hycoord
      rw [hky] at heq
      dsimp [c₀] at heq
      linarith
    have hsep := hCgap (π k) (Set.mem_image_of_mem π hk) hneq
    have hdiff : |(π y - π s) - c₀| = |π y - π v| := by
      dsimp [c₀]
      congr 1 <;> ring
    have hsepY : ηC ≤ |(π y - π s) - c₀| := by
      rw [← hky]
      exact hsep
    rw [hdiff] at hsepY
    have hlt : |π y - π v| < ηC := lt_of_lt_of_le hcoordclose (min_le_left _ _)
    exact (not_lt_of_ge hsepY) hlt
  have hynotvertex : π y ∉ W := by
    intro hmem
    have hne : π y ≠ π v := hycoord
    have hsep := hWgap (π y) hmem hne
    have hlt : |π y - π v| < ηW := lt_of_lt_of_le hcoordclose (min_le_right _ _)
    exact (not_lt_of_ge hsep) hlt
  have hynotproper : y ∉ properVertices D := by
    intro hy
    exact hynotvertex (Set.mem_image_of_mem π hy)
  have hstraight : BoundaryLocallyStraightAt D y := by
    by_contra h
    exact hynotproper ⟨hyfront, h⟩
  obtain ⟨L, hyL, hLdim, hLlocal⟩ := hstraight
  have hnotparallel := bgcorner_actual_noncritical_frontier_germ_not_delta K S hp π δ hker
    hline s hs y hyfront (π y - π s) (by ring) hycritical
    L hyL hLdim hLlocal
  by_cases hbelow : π y < π v
  · obtain ⟨M, hyM, hMδ, hMlocal⟩ := frontier_point_below_minimum_has_parallel_germ
      hδ π hker hp hline s hs (π v) (by
        intro u hu
        exact hmin u hu) hyfront hbelow
    have hnotparallel' := bgcorner_actual_noncritical_frontier_germ_not_delta K S hp π δ hker
      hline s hs y hyfront (π y - π s) (by ring) hycritical
      M hyM (by rw [hMδ]; exact hδ) hMlocal
    exact False.elim (hnotparallel' hMδ)
  · have habove : π v < π y := lt_of_le_of_ne (le_of_not_gt hbelow) hycoord.symm
    have hybelow : π y < π v + η := by
      have hcoordclose' := hcoordclose
      rw [abs_of_pos (sub_pos.mpr habove)] at hcoordclose'
      linarith
    exact ⟨η, y, hη, hyfront, habove, hybelow, hWgapAbove,
      L, hyL, hLdim, hnotparallel, hLlocal⟩

private theorem bgcorner_actual_noncritical_frontier_point_has_slice_arcs
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : ∃ a : Plane, ∀ t ∈ S, t - a ∈ δ)
    (s : Plane) (hs : s ∈ S)
    (q : Plane) (hqfront : q ∈ frontier (regularSupport K S))
    (x : ℝ) (hqcoord : π q = π s + x)
    (hxcritical : x ∉ π '' vertexSet K.support)
    (hqnotproper : q ∉ properVertices (regularSupport K S)) :
    ∃ w : Plane, w ∈ δ ∧ w ≠ 0 ∧ ∃ t η₁ η₂ : ℝ, 0 < t ∧ 0 < η₁ ∧ 0 < η₂ ∧
      (( (∀ r : ℝ, |r - t| < η₁ → q + r • w ∈ interior (regularSupport K S)) ∧
         (∀ r : ℝ, |r + t| < η₂ → q + r • w ∈ interior (regularSupport K S)ᶜ)) ∨
       ( (∀ r : ℝ, |r - t| < η₁ → q + r • w ∈ interior (regularSupport K S)ᶜ) ∧
         (∀ r : ℝ, |r + t| < η₂ → q + r • w ∈ interior (regularSupport K S)))) := by
  classical
  let D := regularSupport K S
  have hregular : interior (closure D) = D := by simp [D, regularSupport]
  have hstraight : BoundaryLocallyStraightAt D q := by
    by_contra h
    exact hqnotproper ⟨hqfront, h⟩
  obtain ⟨L, hqL, hLdim, hLlocal⟩ := hstraight
  have hnotparallel := bgcorner_actual_noncritical_frontier_germ_not_delta K S hp π δ hker
    hline s hs q hqfront x hqcoord hxcritical L hqL hLdim hLlocal
  have hδbot : δ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hδ
    exact Nat.zero_ne_one hδ
  obtain ⟨w, hw, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδbot
  have hwtrans : w ∉ L.direction := by
    intro hwL
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hδ hw hwne
    have hle : δ ≤ L.direction := by
      rw [hspan]
      exact Submodule.span_le.mpr (by simpa using hwL)
    have heq : δ = L.direction :=
      Submodule.eq_of_le_of_finrank_eq hle (hδ.trans hLdim.symm)
    exact hnotparallel heq.symm
  obtain ⟨t, ht, hcut⟩ := bgcorner_smooth_transverse_frontier_germ_cuts_slice
    hregular π hπ δ hδ hker q hqfront L hqL hLdim hLlocal w hw hwtrans
  rcases hcut with ⟨hplus, hminus⟩ | ⟨hplus, hminus⟩
  · obtain ⟨η₁, hη₁, hplusI⟩ := bgcorner_open_set_contains_slice_interval
      isOpen_interior q w t hplus hwne
    have hminus' : q + (-t) • w ∈ interior Dᶜ := by
      simpa [neg_smul, sub_eq_add_neg] using hminus
    obtain ⟨η₂, hη₂, hminusI⟩ := bgcorner_open_set_contains_slice_interval
      isOpen_interior q w (-t) hminus' hwne
    refine ⟨w, hw, hwne, t, η₁, η₂, ht, hη₁, hη₂, Or.inl ⟨hplusI, ?_⟩⟩
    simpa [sub_neg_eq_add] using hminusI
  · obtain ⟨η₁, hη₁, hplusI⟩ := bgcorner_open_set_contains_slice_interval
      isOpen_interior q w t hplus hwne
    have hminus' : q + (-t) • w ∈ interior D := by
      simpa [neg_smul, sub_eq_add_neg] using hminus
    obtain ⟨η₂, hη₂, hminusI⟩ := bgcorner_open_set_contains_slice_interval
      isOpen_interior q w (-t) hminus' hwne
    refine ⟨w, hw, hwne, t, η₁, η₂, ht, hη₁, hη₂, Or.inr ⟨hplusI, ?_⟩⟩
    simpa [sub_neg_eq_add] using hminusI

private theorem bgcorner_actual_transverse_seed_propagates_in_vertex_gap
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (π : Plane →L[ℝ] ℝ) (hker : LinearMap.ker π.toLinearMap = δ)
    (q : Plane) (hq : q ∈ frontier (regularSupport K S))
    (m hi : ℝ) (hmq : m < π q) (hqi : π q < hi)
    (hgap : ∀ z ∈ properVertices (regularSupport K S), m < π z → hi ≤ π z)
    (hmin : ∀ z ∈ properVertices (regularSupport K S), m ≤ π z)
    (L : AffineSubspace ℝ Plane) (hqL : q ∈ L)
    (hLdim : Module.finrank ℝ L.direction = 1) (hLnotδ : L.direction ≠ δ)
    (hlocal : ∀ᶠ z in 𝓝 q,
      (z ∈ frontier (regularSupport K S) ↔ z ∈ (L : Set Plane)))
    (a : ℝ) (ham : m < a) (hai : a < hi) :
    ∃ z : Plane, z ∈ frontier (regularSupport K S) ∧ π z = a ∧
      z ∉ properVertices (regularSupport K S) := by
  classical
  let D := regularSupport K S
  have hLbot : L.direction ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hLdim
    exact Nat.zero_ne_one hLdim
  obtain ⟨e, heL, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLbot
  have heπ : π e ≠ 0 := by
    intro heπ0
    have heδ : e ∈ δ := by
      rw [← hker, LinearMap.mem_ker]
      exact heπ0
    have hspanL := eq_span_singleton_of_mem_of_finrank_eq_one hLdim heL he0
    have hle : L.direction ≤ δ := by
      rw [hspanL]
      exact Submodule.span_le.mpr (by simpa using heδ)
    have heq : L.direction = δ :=
      Submodule.eq_of_le_of_finrank_eq hle (hLdim.trans hδ.symm)
    exact hLnotδ heq
  let u : Plane := if 0 < π e then e else -e
  have huL : u ∈ L.direction := by
    dsimp [u]
    split_ifs <;> simpa using (show e ∈ L.direction from heL)
  have huπ : 0 < π u := by
    dsimp [u]
    split_ifs with h
    · exact h
    · have hneg : π e < 0 := lt_of_le_of_ne (le_of_not_gt h) heπ
      simpa using (neg_pos.mpr hneg)
  have hune : u ≠ 0 := by
    intro hz
    have : π u = 0 := by rw [hz, map_zero]
    exact (ne_of_gt huπ) this
  by_cases hsame : a = π q
  · exact ⟨q, hq, hsame.symm, by
      intro hz
      have hmq' := hmin q hz
      have hgap' := hgap q hz hmq
      linarith⟩
  · let v : Plane := if π q < a then u else -u
    let B : ℝ := |a - π q| / π u
    have hB : 0 < B := by
      dsimp [B]
      exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hsame)) huπ
    have hvL : v ∈ L.direction := by
      dsimp [v]
      split_ifs <;> simp [huL]
    have hv0 : v ≠ 0 := by
      intro hz
      have : π v = 0 := by rw [hz, map_zero]
      dsimp [v] at this
      split_ifs at this <;> simp [huπ.ne'] at this
    have hmove : B * π v = a - π q := by
      by_cases hdir : π q < a
      · have hpos : 0 < a - π q := by linarith
        simp [v, B, hdir, abs_of_pos hpos]
        field_simp [ne_of_gt huπ]
      · have hneg : a - π q < 0 := by
          exact sub_neg.mpr (lt_of_le_of_ne (le_of_not_gt hdir) hsame)
        simp [v, B, hdir, abs_of_neg hneg]
        field_simp [ne_of_gt huπ]
        ring
    have hlineSet : (L : Set Plane) = q +ᵥ
        (Submodule.span ℝ ({v} : Set Plane) : Set Plane) :=
      bgcorner_affine_line_set_eq_anchor_span L q v hqL hLdim hvL hv0
    have hg : ∀ᶠ z in 𝓝 q, z ∈ frontier D ↔
        z ∈ q +ᵥ (Submodule.span ℝ ({v} : Set Plane) : Set Plane) := by
      filter_upwards [hlocal] with z hz
      change z ∈ frontier D ↔ z ∈ (L : Set Plane) at hz
      simpa only [hlineSet] using hz
    have hW : ∀ t ∈ Set.Icc (0 : ℝ) B, q + t • v ∉ properVertices D := by
      intro t ht hz
      have hcoord : m < π (q + t • v) ∧ π (q + t • v) < hi := by
        rw [map_add, map_smul, smul_eq_mul]
        by_cases hdir : π q < a
        · have htmove : 0 ≤ t * π v ∧ t * π v ≤ a - π q := by
            simp [v, hdir]
            constructor
            · exact mul_nonneg ht.1 (le_of_lt huπ)
            · have hupper : t * π u ≤ B * π u :=
                mul_le_mul_of_nonneg_right ht.2 huπ.le
              rw [show B * π u = a - π q by simpa [v, hdir] using hmove] at hupper
              exact hupper
          constructor <;> linarith [hmq, hqi]
        · have htmove : a - π q ≤ t * π v ∧ t * π v ≤ 0 := by
            have hneg : π v < 0 := by simp [v, hdir, huπ]
            constructor
            · have hlower : B * π v ≤ t * π v :=
                mul_le_mul_of_nonpos_right ht.2 hneg.le
              rw [hmove] at hlower
              exact hlower
            · exact mul_nonpos_of_nonneg_of_nonpos ht.1 hneg.le
          constructor <;> linarith [ham, hqi]
      have hproper := hmin (q + t • v) hz
      have hgap' := hgap (q + t • v) hz hcoord.1
      linarith
    have hrun := frontier_ray_segment_of_no_properVertices hv0 hB hq hg hW
    let z : Plane := q + B • v
    have hzfront : z ∈ frontier D := by
      simpa [z] using hrun B ⟨le_of_lt hB, le_rfl⟩
    have hzcoord : π z = a := by
      calc
        π z = π q + π (B • v) := by simp [z]
        _ = π q + B * π v := by rw [map_smul, smul_eq_mul]
        _ = a := by linarith [hmove]
    have hzproper : z ∉ properVertices D := by
      intro hz
      have hmz := hmin z hz
      have hgz := hgap z hz (by rw [hzcoord]; exact ham)
      linarith
    exact ⟨z, hzfront, hzcoord, hzproper⟩

private theorem bgcorner_actual_minimum_corner_has_partial_slice_arcs
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : ∃ a : Plane, ∀ t ∈ S, t - a ∈ δ)
    (s : Plane) (hs : s ∈ S)
    (v : Plane) (hv : v ∈ properVertices (regularSupport K S))
    (hmin : ∀ u ∈ properVertices (regularSupport K S), π v ≤ π u) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : ℝ,
      π v - π s < x → x < π v - π s + η →
      x ∉ π '' vertexSet K.support →
      ∃ q : Plane, q ∈ frontier (regularSupport K S) ∧ π q = π s + x ∧
        ∃ w : Plane, w ∈ δ ∧ w ≠ 0 ∧ ∃ t η₁ η₂ : ℝ,
          0 < t ∧ 0 < η₁ ∧ 0 < η₂ ∧
          (((∀ r : ℝ, |r - t| < η₁ →
                q + r • w ∈ interior (regularSupport K S)) ∧
             (∀ r : ℝ, |r + t| < η₂ →
                q + r • w ∈ interior (regularSupport K S)ᶜ)) ∨
           ((∀ r : ℝ, |r - t| < η₁ →
                q + r • w ∈ interior (regularSupport K S)ᶜ) ∧
             (∀ r : ℝ, |r + t| < η₂ →
                q + r • w ∈ interior (regularSupport K S)))) := by
  obtain ⟨η, q₀, hη, hq₀front, hq₀above, hq₀hi, hgap,
      L, hq₀L, hLdim, hLnotδ, hlocal⟩ :=
    bgcorner_actual_minimum_corner_has_upper_transverse_germ hδ π hπ hker hp hline s hs v hv hmin
  refine ⟨η, hη, ?_⟩
  intro x hxlo hxhi hxcritical
  let a : ℝ := π s + x
  have halo : π v < a := by dsimp [a]; linarith
  have hahi : a < π v + η := by dsimp [a]; linarith
  obtain ⟨q, hqfront, hqcoord, hqnotproper⟩ :=
    bgcorner_actual_transverse_seed_propagates_in_vertex_gap hδ π hker q₀ hq₀front
      (π v) (π v + η) hq₀above hq₀hi hgap hmin L hq₀L hLdim hLnotδ hlocal
      a halo hahi
  have hqcoord' : π q = π s + x := by simpa [a] using hqcoord
  obtain ⟨w, hw, hwne, t, η₁, η₂, ht, hη₁, hη₂, harcs⟩ :=
    bgcorner_actual_noncritical_frontier_point_has_slice_arcs hδ π hπ hker hp hline s hs
      q hqfront x hqcoord' hxcritical hqnotproper
  exact ⟨q, hqfront, hqcoord', w, hw, hwne, t, η₁, η₂,
    ht, hη₁, hη₂, harcs⟩

private theorem bgcorner_actual_minimum_corner_has_partial_slice_arcs_on_fixed_direction
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : ∃ a : Plane, ∀ t ∈ S, t - a ∈ δ)
    (s : Plane) (hs : s ∈ S)
    (v : Plane) (hv : v ∈ properVertices (regularSupport K S))
    (hmin : ∀ u ∈ properVertices (regularSupport K S), π v ≤ π u)
    (w : Plane) (hw : w ∈ δ) (hwne : w ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : ℝ,
      π v - π s < x → x < π v - π s + η →
      x ∉ π '' vertexSet K.support →
      ∃ q : Plane, q ∈ frontier (regularSupport K S) ∧ π q = π s + x ∧
        ∃ r₁ r₂ ρ₁ ρ₂ : ℝ, 0 < ρ₁ ∧ 0 < ρ₂ ∧
          (( (∀ r : ℝ, |r - r₁| < ρ₁ →
                q + r • w ∈ interior (regularSupport K S)) ∧
             (∀ r : ℝ, |r - r₂| < ρ₂ →
                q + r • w ∈ interior (regularSupport K S)ᶜ)) ∨
           ((∀ r : ℝ, |r - r₁| < ρ₁ →
                q + r • w ∈ interior (regularSupport K S)ᶜ) ∧
             (∀ r : ℝ, |r - r₂| < ρ₂ →
                q + r • w ∈ interior (regularSupport K S)))) := by
  obtain ⟨η, hη, hpartial⟩ := bgcorner_actual_minimum_corner_has_partial_slice_arcs
    hδ π hπ hker hp hline s hs v hv hmin
  have hspan : δ = Submodule.span ℝ ({w} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ hw hwne
  refine ⟨η, hη, ?_⟩
  intro x hxlo hxhi hxcritical
  obtain ⟨q, hqfront, hqcoord, w', hw'δ, hw'ne, t, η₁, η₂,
      ht, hη₁, hη₂, harcs⟩ := hpartial x hxlo hxhi hxcritical
  have hw'span : w' ∈ Submodule.span ℝ ({w} : Set Plane) := by
    rw [← hspan]
    exact hw'δ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw'span
  have hcne : c ≠ 0 := by
    intro hc0
    apply hw'ne
    rw [← hc, hc0]
    simp
  have hpluspoint (hplus : ∀ r : ℝ, |r - t| < η₁ →
      q + r • w' ∈ interior (regularSupport K S)) :
      q + (t * c) • w ∈ interior (regularSupport K S) := by
    have := hplus t (by simp [hη₁])
    rw [← hc, smul_smul] at this
    simpa [mul_comm] using this
  have hminuspoint (hminus : ∀ r : ℝ, |r + t| < η₂ →
      q + r • w' ∈ interior (regularSupport K S)ᶜ) :
      q + ((-t) * c) • w ∈ interior (regularSupport K S)ᶜ := by
    have := hminus (-t) (by simp [hη₂])
    rw [← hc, smul_smul] at this
    simpa [mul_comm] using this
  have hpluspoint' (hplus : ∀ r : ℝ, |r - t| < η₁ →
      q + r • w' ∈ interior (regularSupport K S)ᶜ) :
      q + (t * c) • w ∈ interior (regularSupport K S)ᶜ := by
    have := hplus t (by simp [hη₁])
    rw [← hc, smul_smul] at this
    simpa [mul_comm] using this
  have hminuspoint' (hminus : ∀ r : ℝ, |r + t| < η₂ →
      q + r • w' ∈ interior (regularSupport K S)) :
      q + ((-t) * c) • w ∈ interior (regularSupport K S) := by
    have := hminus (-t) (by simp [hη₂])
    rw [← hc, smul_smul] at this
    simpa [mul_comm] using this
  rcases harcs with ⟨hplus, hminus⟩ | ⟨hplus, hminus⟩
  · obtain ⟨ρ₁, hρ₁, hI₁⟩ := bgcorner_open_set_contains_slice_interval
      isOpen_interior q w (t * c) (hpluspoint hplus) hwne
    obtain ⟨ρ₂, hρ₂, hI₂⟩ := bgcorner_open_set_contains_slice_interval
      isOpen_interior q w ((-t) * c) (hminuspoint hminus) hwne
    exact ⟨q, hqfront, hqcoord, t * c, (-t) * c, ρ₁, ρ₂,
      hρ₁, hρ₂, Or.inl ⟨hI₁, hI₂⟩⟩
  · obtain ⟨ρ₁, hρ₁, hI₁⟩ := bgcorner_open_set_contains_slice_interval
      isOpen_interior q w (t * c) (hpluspoint' hplus) hwne
    obtain ⟨ρ₂, hρ₂, hI₂⟩ := bgcorner_open_set_contains_slice_interval
      isOpen_interior q w ((-t) * c) (hminuspoint' hminus) hwne
    exact ⟨q, hqfront, hqcoord, t * c, (-t) * c, ρ₁, ρ₂,
      hρ₁, hρ₂, Or.inr ⟨hI₁, hI₂⟩⟩

private theorem bgcorner_actual_minimum_corner_original_scalar_arcs
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (π : Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : ∃ a : Plane, ∀ t ∈ S, t - a ∈ δ)
    (s : Plane) (hs : s ∈ S)
    (v : Plane) (hv : v ∈ properVertices (regularSupport K S))
    (hmin : ∀ u ∈ properVertices (regularSupport K S), π v ≤ π u)
    (w : Plane) (hw : w ∈ δ) (hwne : w ≠ 0)
    (e : Plane) (heπ : π e = 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ Set.Ioo (π v - π s) (π v - π s + η),
      ∃ α β γ κ : ℝ, α < β ∧
        (∀ r ∈ Set.Ioo α β, s + x • e + r • w ∈ regularSupport K S) ∧
        γ < κ ∧
        (∀ r ∈ Set.Ioo γ κ, s + x • e + r • w ∉ regularSupport K S) := by
  classical
  let m : ℝ := π v - π s
  let C : Set ℝ := π '' vertexSet K.support
  have hCfinite : C.Finite := K.isPolygonal.vertexSet_finite.image π
  obtain ⟨ηC, hηC, hCgap⟩ := bgcorner_finite_set_has_positive_gap_around_mem C hCfinite m
  obtain ⟨η₀, hη₀, hpartial⟩ :=
    bgcorner_actual_minimum_corner_has_partial_slice_arcs_on_fixed_direction
      hδ π hπ hker hp hline s hs v hv hmin w hw hwne
  let η : ℝ := min η₀ ηC
  have hη : 0 < η := lt_min hη₀ hηC
  refine ⟨η, hη, ?_⟩
  intro x hx
  have hxlo : π v - π s < x := hx.1
  have hxhi : x < π v - π s + η := hx.2
  have hxhi₀ : x < π v - π s + η₀ := by
    dsimp [η] at hxhi
    linarith [min_le_left η₀ ηC]
  have hxcritical : x ∉ C := by
    intro hxC
    obtain ⟨k, hk, hxk⟩ := hxC
    by_cases heq : π k = m
    · dsimp [m] at heq
      linarith
    · have hsep := hCgap (π k) (Set.mem_image_of_mem π hk) heq
      have hpos : 0 < π k - m := by
        rw [hxk]
        dsimp [m]
        linarith
      have hxgap : |π k - m| < ηC := by
        have hηle : η ≤ ηC := by dsimp [η]; exact min_le_right η₀ ηC
        have hposx : 0 < x - m := by dsimp [m]; linarith [hxlo]
        rw [hxk, abs_of_pos hposx]
        dsimp [m]
        linarith [hxhi, hηle]
      exact (not_lt_of_ge hsep) hxgap
  obtain ⟨q, hqfront, hqcoord, r₁, r₂, ρ₁, ρ₂, hρ₁, hρ₂, harcs⟩ :=
    hpartial x hxlo hxhi₀ hxcritical
  let b : Plane := s + x • e
  have hbcoord : π b = π s + x := by
    calc
      π b = π s + π (x • e) := by simp [b, map_add]
      _ = π s + x := by rw [map_smul, smul_eq_mul, heπ]; ring
  have hqδ : q - b ∈ δ := by
    have hcoord : π (q - b) = 0 := by
      rw [map_sub, hqcoord, hbcoord]
      abel
    have hmem : q - b ∈ LinearMap.ker π.toLinearMap := LinearMap.mem_ker.mpr hcoord
    rwa [hker] at hmem
  have hspan : δ = Submodule.span ℝ ({w} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ hw hwne
  have hqspan : q - b ∈ Submodule.span ℝ ({w} : Set Plane) := by
    rw [← hspan]
    exact hqδ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hqspan
  have hqeq : q = b + c • w := by
    calc
      q = b + (q - b) := by abel
      _ = b + c • w := by rw [hc]
  have htranslate (r r₀ ρ : ℝ)
      (harc : ∀ z : ℝ, |z - r₀| < ρ →
        q + z • w ∈ interior (regularSupport K S))
      (hr : r ∈ Set.Ioo (c + r₀ - ρ) (c + r₀ + ρ)) :
      s + x • e + r • w ∈ regularSupport K S := by
    have hrabs : |(r - c) - r₀| < ρ := by
      rw [abs_lt]
      rcases hr with ⟨hlo, hhi⟩
      constructor <;> linarith
    have hmem := interior_subset (harc (r - c) hrabs)
    have hpoint : q + (r - c) • w = b + r • w := by
      rw [hqeq]
      module
    rw [hpoint] at hmem
    simpa [b] using hmem
  have htranslateVac (r r₀ ρ : ℝ)
      (harc : ∀ z : ℝ, |z - r₀| < ρ →
        q + z • w ∈ interior (regularSupport K S)ᶜ)
      (hr : r ∈ Set.Ioo (c + r₀ - ρ) (c + r₀ + ρ)) :
      s + x • e + r • w ∉ regularSupport K S := by
    have hrabs : |(r - c) - r₀| < ρ := by
      rw [abs_lt]
      rcases hr with ⟨hlo, hhi⟩
      constructor <;> linarith
    have hmem := interior_subset (harc (r - c) hrabs)
    have hpoint : q + (r - c) • w = b + r • w := by
      rw [hqeq]
      module
    rw [hpoint] at hmem
    simpa [b] using hmem
  rcases harcs with ⟨hOcc, hVac⟩ | ⟨hVac, hOcc⟩
  · refine ⟨c + r₁ - ρ₁, c + r₁ + ρ₁,
      c + r₂ - ρ₂, c + r₂ + ρ₂, ?_, ?_, ?_, ?_⟩
    · linarith
    · intro r hr
      exact htranslate r r₁ ρ₁ hOcc hr
    · linarith
    · intro r hr
      exact htranslateVac r r₂ ρ₂ hVac hr
  · refine ⟨c + r₂ - ρ₂, c + r₂ + ρ₂,
      c + r₁ - ρ₁, c + r₁ + ρ₁, ?_, ?_, ?_, ?_⟩
    · linarith
    · intro r hr
      exact htranslate r r₂ ρ₂ hOcc hr
    · linarith
    · intro r hr
      exact htranslateVac r r₁ ρ₁ hVac hr

end MinimumCornerProofs

section TracePeriodProofs

open Tiling.AxisParallel.OneDimensional.FiniteInterval

private def bgtrace_positiveHalfGerm (D : Set Tiling.Plane) (ψ : Tiling.Plane →L[ℝ] ℝ)
    (x : Tiling.Plane) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    Metric.ball x r ∩ {y | ψ x < ψ y} ⊆ interior D

private theorem bgtrace_tile_support_avoids_vacant_germ
    {D T : Set Tiling.Plane} {ψ : Tiling.Plane →L[ℝ] ℝ}
    {x y : Tiling.Plane} {r : ℝ}
    (hTD : T ⊆ D) (hneg : Metric.ball x r ∩ {z | ψ z < ψ x} ⊆ interior Dᶜ)
    (hyT : y ∈ T) (hyball : y ∈ Metric.ball x r) :
    ¬ ψ y < ψ x := by
  intro hside
  have hout : y ∈ interior Dᶜ := hneg ⟨hyball, hside⟩
  exact (interior_subset hout) (hTD hyT)

/-- Convex polygonal pieces meeting a complete frontier line lie wholly on
the carrier's occupied side; in particular no triangle can cross the line. -/
private theorem bgtrace_convex_tile_support_stays_on_occupied_side
    {D T : Set Tiling.Plane} {ψ : Tiling.Plane →L[ℝ] ℝ} {c : ℝ}
    (hTconvex : Convex ℝ T) (hTD : T ⊆ D)
    (hneg : ∀ x, ψ x = c → ∃ r : ℝ, 0 < r ∧
      Metric.ball x r ∩ {z | ψ z < ψ x} ⊆ interior Dᶜ)
    (hlineHit : ∃ x ∈ T, ψ x = c) :
    ∀ y ∈ T, c ≤ ψ y := by
  intro y hy
  by_contra hcy
  have hyc : ψ y < c := lt_of_not_ge hcy
  obtain ⟨x, hxT, hxc⟩ := hlineHit
  obtain ⟨r, hr, hngerm⟩ := hneg x hxc
  let t : ℝ := min (1 / 2) (r / (2 * (‖y - x‖ + 1)))
  have htpos : 0 < t := by
    dsimp [t]
    positivity
  have htlt : t < 1 := by
    have htle : t ≤ 1 / 2 := min_le_left _ _
    linarith
  let z : Tiling.Plane := (1 - t) • x + t • y
  have hzT : z ∈ T := by
    apply hTconvex hxT hy (by linarith) (by linarith) (by ring)
  have hzc : ψ z < c := by
    change ψ ((1 - t) • x + t • y) < c
    have hmapx := ψ.map_smul (1 - t) x
    have hmapy := ψ.map_smul t y
    rw [ψ.map_add, hmapx, hmapy, hxc, smul_eq_mul, smul_eq_mul]
    nlinarith [htpos, hyc]
  have hdist : dist z x < r := by
    rw [dist_eq_norm_sub]
    have heq : ((1 - t) • x + t • y) - x = t • (y - x) := by
      module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hscale : t * ‖y - x‖ < r := by
      dsimp [t]
      calc
        min (1 / 2) (r / (2 * (‖y - x‖ + 1))) * ‖y - x‖ ≤
            (r / (2 * (‖y - x‖ + 1))) * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ < r := by
          have hden : 0 < 2 * (‖y - x‖ + 1) := by positivity
          rw [div_mul_eq_mul_div]
          apply (div_lt_iff₀ hden).2
          nlinarith [norm_nonneg (y - x), hr]
    exact hscale
  have hzball : z ∈ Metric.ball x r := by
    simpa only [Metric.mem_ball] using hdist
  have hzout : z ∈ interior Dᶜ := hngerm ⟨hzball, by simpa [hxc] using hzc⟩
  exact (interior_subset hzout) (hTD hzT)

/-- A locally finite tile family has a common positive-radius chart at each
point meeting only finitely many incident tiles.  This is the finite-incidence
input needed before taking one-sided polygonal section limits. -/
private theorem bgtrace_locallyFinite_ball_finite_incidence
    {ι : Type*} (F : ι → Set Tiling.Plane) (hF : LocallyFinite F)
    (x : Tiling.Plane) :
    ∃ r : ℝ, 0 < r ∧ {i | (F i ∩ Metric.ball x r).Nonempty}.Finite := by
  obtain ⟨r, hr, hfinite⟩ := hF.exists_mem_basis Metric.nhds_basis_ball
  exact ⟨r, hr, hfinite⟩

/-- A finite family of closed interval sections which covers a genuine open
line segment must contain a section of positive length; point tips alone cannot
account for a one-sided filled frontier germ. -/
private theorem bgtrace_finite_interval_sections_cover_has_positive_length
    {α : Type*} [Fintype α] (lo hi : α → ℝ) (horder : ∀ i, lo i ≤ hi i)
    {a b : ℝ} (hab : a < b)
    (hcover : Set.Ioo a b ⊆ ⋃ i : α, Set.Icc (lo i) (hi i)) :
    ∃ i : α, lo i < hi i := by
  by_contra hnone
  have heq : ∀ i, lo i = hi i := by
    intro i
    exact le_antisymm (horder i) (le_of_not_gt (fun h => hnone ⟨i, h⟩))
  have hfinite : (⋃ i : α, Set.Icc (lo i) (hi i)).Finite := by
    apply Set.finite_iUnion
    intro i
    rw [heq i]
    exact Set.toFinite _
  have hopenFinite : (Set.Ioo a b).Finite := hfinite.subset hcover
  exact (Set.Ioo_infinite hab) hopenFinite

/-- A positive-radius piece of a completely covered frontier line, together
with local finiteness, forces at least one genuinely longitudinal polygonal
incidence.  This rules out a chart made only of isolated vertex tips. -/
private theorem bgtrace_exists_negative_coordinate_point
    (ψ : Tiling.Plane →L[ℝ] ℝ) (hψ : Function.Surjective ψ)
    (x : Tiling.Plane) {r : ℝ} (hr : 0 < r) :
    ∃ y ∈ Metric.ball x r, ψ y < ψ x := by
  obtain ⟨w, hw⟩ := hψ 1
  let t : ℝ := r / (2 * (‖w‖ + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  let y : Tiling.Plane := x + (-t) • w
  have hdist : dist y x < r := by
    rw [dist_eq_norm_sub]
    simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_pos ht]
    have hden : 0 < 2 * (‖w‖ + 1) := by positivity
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith [norm_nonneg w]
  have hcoord : ψ y < ψ x := by
    change ψ (x + (-t) • w) < ψ x
    rw [map_add, map_smul, hw]
    simp only [smul_eq_mul]
    linarith [ht]
  exact ⟨y, Metric.mem_ball.mpr hdist, hcoord⟩

/-- A polygonal tile contained in a carrier cannot choose the carrier's vacant
side at a common locally straight frontier point. -/
private theorem bgtrace_tile_germ_matches_carrier_side
    {D T : Set Tiling.Plane} {ψ : Tiling.Plane →L[ℝ] ℝ}
    {x : Tiling.Plane} (hψ : Function.Surjective ψ)
    (hDvacant : ∃ r : ℝ, 0 < r ∧
      Metric.ball x r ∩ {y | ψ y < ψ x} ⊆ interior Dᶜ)
    (hTD : T ⊆ D) (hTregular : closure (interior T) = T)
    (hxT : x ∈ frontier T)
    (hTline : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball x r,
      (y ∈ frontier T ↔ ψ y = ψ x)) :
    bgtrace_positiveHalfGerm T ψ x := by
  obtain ⟨rD, hrD, hvacant⟩ := hDvacant
  obtain ⟨rT, hrT, hlineT⟩ := hTline
  let r := min rD rT
  have hr : 0 < r := lt_min hrD hrT
  have hline (y : Tiling.Plane) (hy : y ∈ Metric.ball x r) :
      (y ∈ frontier T ↔ ψ y = ψ x) :=
    hlineT y (Metric.ball_subset_ball (min_le_right rD rT) hy)
  have hchoice := Tiling.local_levelSet_dichotomy ψ hr hTregular hxT hline
  rcases hchoice with ⟨hpos, hneg⟩ | ⟨hposOut, hnegIn⟩
  · exact ⟨r, hr, hpos⟩
  · obtain ⟨y, hyball, hycoord⟩ := bgtrace_exists_negative_coordinate_point ψ hψ x hr
    have hyball : y ∈ Metric.ball x r :=
      hyball
    have hyTinterior := hnegIn ⟨hyball, hycoord⟩
    have hyballD : y ∈ Metric.ball x rD :=
      Metric.ball_subset_ball (min_le_left rD rT) hyball
    have hyDinterior := hvacant ⟨hyballD, hycoord⟩
    exact False.elim ((interior_subset hyDinterior)
      (hTD (interior_subset hyTinterior)))

/-- Two regular polygonal supports with a common locally straight boundary
line and the same occupied side cannot be almost-everywhere disjoint: a small
point in that open half-plane is interior to both, yielding an open overlap of
positive measure. -/
private theorem bgtrace_same_positive_germ_forces_interior_collision
    {A B : Set Tiling.Plane} {ψ : Tiling.Plane →L[ℝ] ℝ}
    {x : Tiling.Plane} (hψ : Function.Surjective ψ)
    (hA : bgtrace_positiveHalfGerm A ψ x) (hB : bgtrace_positiveHalfGerm B ψ x)
    (hdisj : AEDisjoint volume A B) : False := by
  obtain ⟨rA, hrA, hAgerm⟩ := hA
  obtain ⟨rB, hrB, hBgerm⟩ := hB
  obtain ⟨w, hw⟩ := hψ 1
  let r := min rA rB
  let t : ℝ := r / (2 * (‖w‖ + 1))
  let y : Tiling.Plane := x + t • w
  have hr : 0 < r := lt_min hrA hrB
  have ht : 0 < t := by dsimp [t]; positivity
  have hdist : dist y x < r := by
    rw [dist_eq_norm_sub]
    simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hden : 0 < 2 * (‖w‖ + 1) := by positivity
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith [norm_nonneg w]
  have hcoord : ψ x < ψ y := by
    change ψ (x + t • w) > ψ x
    rw [map_add, map_smul, hw]
    simp only [smul_eq_mul]
    linarith [ht]
  have hyballA : y ∈ Metric.ball x rA := by
    rw [Metric.mem_ball]
    exact lt_of_lt_of_le hdist (min_le_left rA rB)
  have hyballB : y ∈ Metric.ball x rB := by
    rw [Metric.mem_ball]
    exact lt_of_lt_of_le hdist (min_le_right rA rB)
  have hyA : y ∈ interior A := hAgerm ⟨hyballA, hcoord⟩
  have hyB : y ∈ interior B := hBgerm ⟨hyballB, hcoord⟩
  have hopen : IsOpen (interior A ∩ interior B) := isOpen_interior.inter isOpen_interior
  have hmeasure : volume (interior A ∩ interior B) ≠ 0 :=
    hopen.measure_ne_zero volume ⟨y, hyA, hyB⟩
  have hsubset : interior A ∩ interior B ⊆ A ∩ B :=
    inter_subset_inter interior_subset interior_subset
  exact hmeasure (measure_mono_null hsubset hdisj)

/-- A positive-length frontier trace on a line identifies the tile's local
straight boundary line: one distinct point of the trace supplies the common
nonzero direction vector, and both affine lines have dimension one. -/
private theorem bgtrace_two_boundary_points_identify_local_line
    {T : Set Tiling.Plane} {x z : Tiling.Plane}
    {L L' : AffineSubspace ℝ Tiling.Plane} {r : ℝ}
    (hxL : x ∈ L) (hzL : z ∈ L) (hne : x ≠ z)
    (hLdim : Module.finrank ℝ L.direction = 1)
    (hxL' : x ∈ L') (hL'dim : Module.finrank ℝ L'.direction = 1)
    (hlocal : ∀ y ∈ Metric.ball x r,
      (y ∈ frontier T ↔ y ∈ (L' : Set Tiling.Plane)))
    (hzball : z ∈ Metric.ball x r) (hzfront : z ∈ frontier T) :
    L = L' := by
  have hzL' : z ∈ L' := (hlocal z hzball).mp hzfront
  let v : Tiling.Plane := z -ᵥ x
  have hvne : v ≠ 0 := by
    intro hv
    exact hne (vsub_eq_zero_iff_eq.mp hv).symm
  have hvL : v ∈ L.direction := by
    exact AffineSubspace.vsub_mem_direction hzL hxL
  have hvL' : v ∈ L'.direction := by
    exact AffineSubspace.vsub_mem_direction hzL' hxL'
  have hspanL := eq_span_singleton_of_mem_of_finrank_eq_one hLdim hvL hvne
  have hspanL' := eq_span_singleton_of_mem_of_finrank_eq_one hL'dim hvL' hvne
  have hdir : L.direction = L'.direction := hspanL.trans hspanL'.symm
  have hle : L ≤ L' := by
    intro y hy
    apply (AffineSubspace.vsub_right_mem_direction_iff_mem hxL' y).mp
    rw [← hdir]
    exact AffineSubspace.vsub_mem_direction hy hxL
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir ⟨x, hxL⟩ hle

/-- An actual polygonal tile that lies in a carrier has the same local
frontier line as the carrier wherever a nonvertex point is accompanied by a
positive-length piece of that line in the tile support.  The trace premise is
local incidence of support points, not a prepackaged section certificate. -/
private theorem bgtrace_polygonal_tile_local_line_of_positive_trace
    {D T : Set Tiling.Plane} {x : Tiling.Plane}
    {L : AffineSubspace ℝ Tiling.Plane} {w : Tiling.Plane}
    (hTpoly : Tiling.IsPolygonal T) (hTD : T ⊆ D)
    (hLfront : (L : Set Tiling.Plane) ⊆ frontier D) (hxT : x ∈ T)
    (hxnotvertex : x ∉ Tiling.vertexSet T)
    (hxL : x ∈ L) (hLdim : Module.finrank ℝ L.direction = 1)
    (hwL : w ∈ L.direction) (hw : w ≠ 0)
    (htrace : ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ (L : Set Tiling.Plane),
      dist y x < ρ → y ∈ T) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball x r,
      (y ∈ frontier T ↔ y ∈ (L : Set Tiling.Plane)) := by
  have hTregular : closure (interior T) = T := hTpoly.closure_interior
  have hTclosed : IsClosed T := by
    rw [← hTregular]
    exact isClosed_closure
  have hxTfront : x ∈ frontier T := by
    rw [frontier, hTclosed.closure_eq]
    refine ⟨hxT, ?_⟩
    intro hxinterior
    have hxDinterior : x ∈ interior D := interior_mono hTD hxinterior
    exact (disjoint_left.mp disjoint_interior_frontier) hxDinterior (hLfront hxL)
  obtain ⟨L', hxL', hL'dim, hlocal'⟩ :=
    hTpoly.boundaryLocallyStraightAt_of_not_mem_vertexSet hxTfront hxnotvertex
  obtain ⟨r, hr, hlocal⟩ := Metric.eventually_nhds_iff.mp hlocal'
  obtain ⟨ρ, hρ, htrace⟩ := htrace
  let q : ℝ := min r ρ / (2 * (‖w‖ + 1))
  let z : Tiling.Plane := x + q • w
  have hq : 0 < q := by dsimp [q]; positivity
  have hzL : z ∈ L := by
    have hdirection : q • w ∈ L.direction := Submodule.smul_mem L.direction q hwL
    have hz' := AffineSubspace.vadd_mem_of_mem_direction hdirection hxL
    simpa [z, vadd_eq_add, add_comm] using hz'
  have hminpos : 0 < min r ρ := lt_min hr hρ
  have hqnorm : q * ‖w‖ < min r ρ := by
    dsimp [q]
    have hden : 0 < 2 * (‖w‖ + 1) := by positivity
    calc
      min r ρ / (2 * (‖w‖ + 1)) * ‖w‖ =
          (min r ρ * ‖w‖) / (2 * (‖w‖ + 1)) := by ring
      _ ≤ (min r ρ * (‖w‖ + 1)) / (2 * (‖w‖ + 1)) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w]) hminpos.le)
          hden.le
      _ = min r ρ / 2 := by field_simp
      _ < min r ρ := by linarith
  have hdist : dist z x < min r ρ := by
    rw [dist_eq_norm_sub]
    simp only [z, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    exact hqnorm
  have hzball : z ∈ Metric.ball x r := by
    rw [Metric.mem_ball]
    exact lt_of_lt_of_le hdist (min_le_left r ρ)
  have hzfront : z ∈ frontier T := by
    have hzT := htrace z hzL (lt_of_lt_of_le hdist (min_le_right r ρ))
    rw [frontier, hTclosed.closure_eq]
    refine ⟨hzT, ?_⟩
    intro hzinterior
    have hzDinterior : z ∈ interior D := interior_mono hTD hzinterior
    exact (disjoint_left.mp disjoint_interior_frontier) hzDinterior (hLfront hzL)
  have hline' (y : Tiling.Plane) (hy : y ∈ Metric.ball x r) :
      (y ∈ frontier T ↔ y ∈ (L' : Set Tiling.Plane)) := hlocal hy
  have hLines := bgtrace_two_boundary_points_identify_local_line
    hxL hzL (by
      intro heq
      have hz0 : q • w = 0 := by
        have heq' : x + q • w = x := by simpa [z] using heq.symm
        have heq'' : x + q • w = x + 0 := by simpa using heq'
        exact add_left_cancel heq''
      have : q = 0 := (smul_eq_zero.mp hz0).resolve_right hw
      exact (ne_of_gt hq) this)
    hLdim hxL' hL'dim hline' hzball hzfront
  refine ⟨r, hr, ?_⟩
  intro y hy
  rw [hLines]
  exact hlocal hy

/-- Every support point of a polygonal tile lying on the carrier frontier is
itself a tile-frontier point, since tile interiors sit inside the carrier's
interior. -/
private theorem bgtrace_polygonal_support_frontier_at_carrier_frontier
    {D T : Set Tiling.Plane} {x : Tiling.Plane}
    (hTpoly : Tiling.IsPolygonal T) (hTD : T ⊆ D)
    (hxD : x ∈ frontier D) (hxT : x ∈ T) : x ∈ frontier T := by
  have hTregular : closure (interior T) = T := hTpoly.closure_interior
  have hTclosed : IsClosed T := by
    rw [← hTregular]
    exact isClosed_closure
  rw [frontier, hTclosed.closure_eq]
  refine ⟨hxT, ?_⟩
  intro hxinterior
  have hxDinterior : x ∈ interior D := interior_mono hTD hxinterior
  exact (disjoint_left.mp disjoint_interior_frontier) hxDinterior hxD

/-- Two polygonal supports contained in a carrier cannot have a positive
longitudinal overlap at a nonvertex point of the carrier frontier.  The local
trace interval forces each tile's boundary line to be the carrier line; the
carrier's vacant-side germ then gives both supports the same occupied-side
germ, contradicting their almost-everywhere disjointness. -/
private theorem bgtrace_polygonal_positive_trace_overlap_impossible
    {D A B : Set Tiling.Plane} {x : Tiling.Plane}
    {L : AffineSubspace ℝ Tiling.Plane} {w : Tiling.Plane}
    {ψ : Tiling.Plane →L[ℝ] ℝ}
    (hApoly : Tiling.IsPolygonal A) (hBpoly : Tiling.IsPolygonal B)
    (hAD : A ⊆ D) (hBD : B ⊆ D)
    (hLfront : (L : Set Tiling.Plane) ⊆ frontier D)
    (hxL : x ∈ L) (hLdim : Module.finrank ℝ L.direction = 1)
    (hwL : w ∈ L.direction) (hw : w ≠ 0)
    (htrace : ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ (L : Set Tiling.Plane),
      dist y x < ρ → y ∈ A ∩ B)
    (hxAnv : x ∉ Tiling.vertexSet A) (hxBnv : x ∉ Tiling.vertexSet B)
    (hLψ : (L : Set Tiling.Plane) = {y | ψ y = ψ x})
    (hψ : Function.Surjective ψ)
    (hDvacant : ∃ r : ℝ, 0 < r ∧
      Metric.ball x r ∩ {y | ψ y < ψ x} ⊆ interior Dᶜ)
    (hdisj : AEDisjoint volume A B) : False := by
  obtain ⟨ρ, hρ, htrace⟩ := htrace
  have hxAB : x ∈ A ∩ B := htrace x hxL (by simpa using hρ)
  have hxA : x ∈ A := hxAB.1
  have hxB : x ∈ B := hxAB.2
  have hxAfr := bgtrace_polygonal_support_frontier_at_carrier_frontier hApoly hAD
    (hLfront hxL) hxA
  have hxBfr := bgtrace_polygonal_support_frontier_at_carrier_frontier hBpoly hBD
    (hLfront hxL) hxB
  have htraceA : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ (L : Set Tiling.Plane),
      dist y x < r → y ∈ A := ⟨ρ, hρ, fun y hyL hy => (htrace y hyL hy).1⟩
  have htraceB : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ (L : Set Tiling.Plane),
      dist y x < r → y ∈ B := ⟨ρ, hρ, fun y hyL hy => (htrace y hyL hy).2⟩
  obtain ⟨rA, hrA, hAlocal⟩ := bgtrace_polygonal_tile_local_line_of_positive_trace
    hApoly hAD hLfront hxA hxAnv hxL hLdim hwL hw htraceA
  obtain ⟨rB, hrB, hBlocal⟩ := bgtrace_polygonal_tile_local_line_of_positive_trace
    hBpoly hBD hLfront hxB hxBnv hxL hLdim hwL hw htraceB
  have hAline : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball x r,
      (y ∈ frontier A ↔ ψ y = ψ x) := by
    refine ⟨rA, hrA, fun y hy => ?_⟩
    have hlocal := hAlocal y hy
    constructor
    · intro hfront
      have hyL : y ∈ (L : Set Tiling.Plane) := hlocal.mp hfront
      have hycoord : y ∈ {z | ψ z = ψ x} := by rw [← hLψ]; exact hyL
      exact hycoord
    · intro hycoord
      have hyL : y ∈ (L : Set Tiling.Plane) := by rw [hLψ]; exact hycoord
      exact hlocal.mpr hyL
  have hBline : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball x r,
      (y ∈ frontier B ↔ ψ y = ψ x) := by
    refine ⟨rB, hrB, fun y hy => ?_⟩
    have hlocal := hBlocal y hy
    constructor
    · intro hfront
      have hyL : y ∈ (L : Set Tiling.Plane) := hlocal.mp hfront
      have hycoord : y ∈ {z | ψ z = ψ x} := by rw [← hLψ]; exact hyL
      exact hycoord
    · intro hycoord
      have hyL : y ∈ (L : Set Tiling.Plane) := by rw [hLψ]; exact hycoord
      exact hlocal.mpr hyL
  have hAgerm := bgtrace_tile_germ_matches_carrier_side hψ hDvacant hAD
    hApoly.closure_interior hxAfr hAline
  have hBgerm := bgtrace_tile_germ_matches_carrier_side hψ hDvacant hBD
    hBpoly.closure_interior hxBfr hBline
  exact bgtrace_same_positive_germ_forces_interior_collision hψ hAgerm hBgerm hdisj

/-- A positive open line interval contains a point outside two finite
polygonal vertex sets.  This is the finite-tip deletion step needed before
applying the local overlap contradiction. -/
private theorem bgtrace_exists_parameter_avoiding_two_finite_sets
    {V₁ V₂ : Set Tiling.Plane} (hV₁ : V₁.Finite) (hV₂ : V₂.Finite)
    (x w : Tiling.Plane) (hw : w ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Set.Ioo a b,
      x + r • w ∉ V₁ ∧ x + r • w ∉ V₂ := by
  let f : ℝ → Tiling.Plane := fun r => x + r • w
  have hinj : Function.Injective f := by
    intro r s hrs
    have hsmul : r • w = s • w := add_left_cancel hrs
    exact smul_left_injective ℝ hw hsmul
  have hbad : (f ⁻¹' (V₁ ∪ V₂)).Finite :=
    Set.Finite.preimage hinj.injOn (hV₁.union hV₂)
  by_contra h
  push Not at h
  have hsub : Set.Ioo a b ⊆ f ⁻¹' (V₁ ∪ V₂) := by
    intro r hr
    by_cases hV : f r ∈ V₁
    · exact Or.inl hV
    · exact Or.inr (h r hr hV)
  have hintervalFinite : (Set.Ioo a b).Finite := hbad.subset hsub
  exact (Set.Ioo_infinite hab) hintervalFinite

/-- A nonzero tangent vector parametrizes its entire affine line when that
line has dimension one. -/
private theorem bgtrace_affine_line_parameterization
    {L : AffineSubspace ℝ Tiling.Plane} {x w : Tiling.Plane}
    (hxL : x ∈ L) (hLdim : Module.finrank ℝ L.direction = 1)
    (hwL : w ∈ L.direction) (hw : w ≠ 0) :
    ∀ y ∈ (L : Set Tiling.Plane), ∃ t : ℝ, y = x + t • w := by
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hLdim hwL hw
  intro y hyL
  have hv : y -ᵥ x ∈ L.direction := AffineSubspace.vsub_mem_direction hyL hxL
  rw [hspan] at hv
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hv
  refine ⟨t, ?_⟩
  calc
    y = (y -ᵥ x) +ᵥ x := by rw [vsub_vadd]
    _ = (t • w) +ᵥ x := by rw [ht]
    _ = x + t • w := by simp [vadd_eq_add, add_comm]

/-- An open parameter interval in both polygonal supports is a genuine local
line trace at each of its interior points, not merely positive scalar measure. -/
private theorem bgtrace_open_parameter_overlap_gives_local_trace
    {A B : Set Tiling.Plane} {L : AffineSubspace ℝ Tiling.Plane}
    {x w : Tiling.Plane} (hxL : x ∈ L)
    (hLdim : Module.finrank ℝ L.direction = 1)
    (hwL : w ∈ L.direction) (hw : w ≠ 0)
    {ε : ℝ} (hε : 0 < ε)
    (htrace : ∀ t ∈ Set.Ioo (-ε) ε,
      x + t • w ∈ A ∩ B) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ (L : Set Tiling.Plane),
      dist y x < ρ → y ∈ A ∩ B := by
  let ρ : ℝ := ε * ‖w‖
  have hρ : 0 < ρ := mul_pos hε (norm_pos_iff.mpr hw)
  refine ⟨ρ, hρ, ?_⟩
  intro y hyL hyclose
  obtain ⟨t, rfl⟩ := bgtrace_affine_line_parameterization hxL hLdim hwL hw y hyL
  have hdist : dist (x + t • w) x = |t| * ‖w‖ := by
    rw [dist_eq_norm_sub]
    simp [add_sub_cancel_left, Real.norm_eq_abs]
  have habs : |t| < ε := by
    rw [hdist] at hyclose
    dsimp [ρ] at hyclose
    exact lt_of_mul_lt_mul_right hyclose (norm_nonneg w)
  exact htrace t (abs_lt.mp habs)

/-- Positive overlap of two translated open polygonal line sections would
produce an actual nonvertex frontier interval shared by the two placed
supports.  The carrier-side collision theorem therefore makes their scalar
interval sections disjoint (in particular, almost-everywhere disjoint). -/
private theorem bgtrace_translated_polygonal_open_sections_disjoint
    {K : Tiling.RationalPolygonal.PolygonalRegion} {D : Set Tiling.Plane}
    {L : AffineSubspace ℝ Tiling.Plane} {x w : Tiling.Plane}
    {ψ : Tiling.Plane →L[ℝ] ℝ} {J Z : Set ℝ}
    (hKpoly : Tiling.IsPolygonal K.support)
    (hJ : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion J)
    (hJsub : J ⊆ {r | x + r • w ∈ K.support})
    (hxL : x ∈ L) (hLdim : Module.finrank ℝ L.direction = 1)
    (hwL : w ∈ L.direction) (hw : w ≠ 0)
    (hLfront : (L : Set Tiling.Plane) ⊆ frontier D)
    (hLψ : (L : Set Tiling.Plane) = {y | ψ y = ψ x})
    (hψ : Function.Surjective ψ)
    (hDvacant : ∀ y ∈ (L : Set Tiling.Plane), ∃ r : ℝ, 0 < r ∧
      Metric.ball y r ∩ {z | ψ z < ψ y} ⊆ interior Dᶜ)
    (hsubset : ∀ z ∈ Z, (z • w) +ᵥ K.support ⊆ D)
    (hpack : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' →
      AEDisjoint volume ((z • w) +ᵥ K.support) ((z' • w) +ᵥ K.support))
    {z z' : ℝ} (hz : z ∈ Z) (hz' : z' ∈ Z) (hzz' : z ≠ z') :
    Disjoint (z +ᵥ J) (z' +ᵥ J) := by
  have hJopen : IsOpen J :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.IsFiniteIntervalRegion.isOpen hJ
  have hUopen : IsOpen ((z +ᵥ J) ∩ (z' +ᵥ J)) :=
    (hJopen.vadd z).inter (hJopen.vadd z')
  rw [Set.disjoint_left]
  intro t htz htz'
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen t ⟨htz, htz'⟩
  let a : ℝ := t - ε / 2
  let b : ℝ := t + ε / 2
  have hab : a < b := by dsimp [a, b]; linarith
  have hIoo : Set.Ioo a b ⊆ (z +ᵥ J) ∩ (z' +ᵥ J) := by
    intro u hu
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hlt : |u - t| < ε := by
      rw [abs_lt]
      constructor
      · have hu1 : t - ε / 2 < u := by simpa [a] using hu.1
        linarith
      · have hu2 : u < t + ε / 2 := by simpa [b] using hu.2
        linarith
    exact hlt
  let A : Set Tiling.Plane := (z • w) +ᵥ K.support
  let B : Set Tiling.Plane := (z' • w) +ᵥ K.support
  have hVA : (Tiling.vertexSet A).Finite :=
    (hKpoly.vadd (z • w)).vertexSet_finite
  have hVB : (Tiling.vertexSet B).Finite :=
    (hKpoly.vadd (z' • w)).vertexSet_finite
  obtain ⟨r, hrI, hrA, hrB⟩ :=
    bgtrace_exists_parameter_avoiding_two_finite_sets hVA hVB x w hw hab
  let ε' := min (r - a) (b - r)
  have hε' : 0 < ε' := by
    dsimp [ε']
    exact lt_min (sub_pos.mpr hrI.1) (sub_pos.mpr hrI.2)
  have hlocalParam (u : ℝ) (hu : u ∈ Set.Ioo (-ε') ε') :
      x + (r + u) • w ∈ A ∩ B := by
    have hu' : -ε' < u ∧ u < ε' := Set.mem_Ioo.mp hu
    have hrplus : r + u ∈ Set.Ioo a b := by
      constructor
      · have hmin : ε' ≤ r - a := min_le_left _ _
        dsimp [a, ε'] at hmin hu'
        dsimp [a]
        linarith
      · have hmin : ε' ≤ b - r := min_le_right _ _
        dsimp [b, ε'] at hmin hu'
        dsimp [b]
        linarith
    have hU' := hIoo hrplus
    rcases hU' with ⟨hUleft, hUright⟩
    have hzJ : r + u - z ∈ J := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hUleft
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hUleft
    have hz'J : r + u - z' ∈ J := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hUright
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hUright
    have hzRaw := hJsub hzJ
    have hz'Raw := hJsub hz'J
    constructor
    · change x + (r + u) • w ∈ (z • w) +ᵥ K.support
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change -(z • w) + (x + (r + u) • w) ∈ K.support
      have heq : -(z • w) + (x + (r + u) • w) = x + (r + u - z) • w := by module
      rw [heq]
      exact hzRaw
    · change x + (r + u) • w ∈ (z' • w) +ᵥ K.support
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change -(z' • w) + (x + (r + u) • w) ∈ K.support
      have heq : -(z' • w) + (x + (r + u) • w) = x + (r + u - z') • w := by module
      rw [heq]
      exact hz'Raw
  let x₀ : Tiling.Plane := x + r • w
  have hx₀L : x₀ ∈ L := by
    have hv := Submodule.smul_mem L.direction r hwL
    have hmem := AffineSubspace.vadd_mem_of_mem_direction hv hxL
    simpa [x₀, vadd_eq_add, add_comm] using hmem
  have hlocalParam' (u : ℝ) (hu : u ∈ Set.Ioo (-ε') ε') :
      x₀ + u • w ∈ A ∩ B := by
    have h := hlocalParam u hu
    have heq : x₀ + u • w = x + (r + u) • w := by
      dsimp [x₀]
      calc
        (x + r • w) + u • w = x + (r • w + u • w) := by abel
        _ = x + (r + u) • w := by rw [← add_smul]
    rw [heq]
    exact h
  have htrace := bgtrace_open_parameter_overlap_gives_local_trace
    hx₀L hLdim hwL hw hε' hlocalParam'
  have hLψ₀ : (L : Set Tiling.Plane) = {y | ψ y = ψ x₀} := by
    have hx₀coord : ψ x₀ = ψ x := by
      have hx₀mem : x₀ ∈ {y | ψ y = ψ x} := hLψ ▸ hx₀L
      exact hx₀mem
    simpa [hx₀coord] using hLψ
  have hDvacant₀ := hDvacant x₀ hx₀L
  have hx₀A : x₀ ∉ Tiling.vertexSet A := by simpa [A, x₀] using hrA
  have hx₀B : x₀ ∉ Tiling.vertexSet B := by simpa [B, x₀] using hrB
  exact False.elim (bgtrace_polygonal_positive_trace_overlap_impossible
    (hKpoly.vadd (z • w)) (hKpoly.vadd (z' • w))
    (hsubset z hz) (hsubset z' hz') hLfront hx₀L hLdim hwL hw htrace
    hx₀A hx₀B hLψ₀ hψ hDvacant₀ (hpack z hz z' hz' hzz'))

/-- A frontier point of the regular support is covered by an actual placed
closed polygonal support.  This upgrades closure of the open union using the
packing-induced local finiteness, rather than mistaking the raw open union for
the frontier carrier. -/
private theorem bgtrace_regularSupport_frontier_point_in_placed_support
    {K : Tiling.RationalPolygonal.PolygonalRegion} {S : Set Tiling.Plane}
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements S))
    {x : Tiling.Plane} (hx : x ∈ frontier (Tiling.Polygonal.regularSupport K S)) :
    ∃ s ∈ S, x ∈ s +ᵥ K.support := by
  have hxclosure : x ∈ closure (Tiling.Polygonal.openUnion K S) := by
    have hx' : x ∈ closure (Tiling.Polygonal.regularSupport K S) := frontier_subset_closure hx
    change x ∈ closure (interior (closure (Tiling.Polygonal.openUnion K S))) at hx'
    have hsub := closure_mono (interior_subset :
      interior (closure (Tiling.Polygonal.openUnion K S)) ⊆
        closure (Tiling.Polygonal.openUnion K S)) hx'
    simpa only [closure_closure] using hsub
  rw [Tiling.Polygonal.closure_openUnion_eq_iUnion_support hpack] at hxclosure
  rcases Set.mem_iUnion.mp hxclosure with ⟨s, hs⟩
  exact ⟨s.1, s.2, hs⟩

/-- The closed carrier is `closure regularSupport`; its frontier is the same
as the frontier of the regular-open support itself.  This is the right
closed-set carrier for support-containment arguments: tile boundaries need
not lie in `regularSupport` (which is open). -/
private theorem bgtrace_regularSupport_frontier_eq_closedRegularSupport_frontier
    (K : Tiling.RationalPolygonal.PolygonalRegion) (S : Set Tiling.Plane) :
    frontier (closure (Tiling.Polygonal.regularSupport K S)) =
      frontier (Tiling.Polygonal.regularSupport K S) := by
  let U := Tiling.Polygonal.openUnion K S
  have hUopen : IsOpen U := by
    dsimp [U, Tiling.Polygonal.openUnion]
    exact isOpen_iUnion fun s => isOpen_interior.vadd s.1
  have hreg : Tiling.Polygonal.regularSupport K S = interior (closure U) := rfl
  have hclosure : closure (Tiling.Polygonal.regularSupport K S) = closure U := by
    rw [hreg]
    have hinner : interior (closure U) ⊆ closure U := interior_subset
    have houter : U ⊆ interior (closure U) := hUopen.subset_interior_closure
    apply le_antisymm
    · calc
        closure (interior (closure U)) ⊆ closure (closure U) := closure_mono hinner
        _ = closure U := closure_closure
    · exact closure_mono houter
  ext x
  change x ∈ closure (closure (Tiling.Polygonal.regularSupport K S)) ∧
      x ∉ interior (closure (Tiling.Polygonal.regularSupport K S)) ↔
    x ∈ closure (Tiling.Polygonal.regularSupport K S) ∧
      x ∉ interior (Tiling.Polygonal.regularSupport K S)
  rw [closure_closure, hclosure, hreg]
  rw [interior_interior]

/-- Under packing, every actual closed placed support lies in the closed
regular carrier. -/
private theorem bgtrace_placed_support_subset_closedRegularSupport
    {K : Tiling.RationalPolygonal.PolygonalRegion} {S : Set Tiling.Plane}
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements S))
    {s : Tiling.Plane} (hs : s ∈ S) :
    s +ᵥ K.support ⊆ closure (Tiling.Polygonal.regularSupport K S) := by
  have hclosure := Tiling.Polygonal.closure_openUnion_eq_iUnion_support hpack
  have hUreg : Tiling.Polygonal.openUnion K S ⊆ Tiling.Polygonal.regularSupport K S := by
    have hUopen : IsOpen (Tiling.Polygonal.openUnion K S) := by
      dsimp [Tiling.Polygonal.openUnion]
      exact isOpen_iUnion fun t => isOpen_interior.vadd t.1
    exact hUopen.subset_interior_closure
  intro x hx
  have hxUclosure : x ∈ closure (Tiling.Polygonal.openUnion K S) := by
    rw [hclosure]
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩
  have hclreg : closure (Tiling.Polygonal.openUnion K S) ⊆
      closure (Tiling.Polygonal.regularSupport K S) := closure_mono hUreg
  exact hclreg hxUclosure

/-- Packing makes the actual centre set countable: the placed supports are
locally finite and nonempty, so the placement subtype is countable. -/
private theorem bgtrace_polygonal_packing_centres_countable
    {K : Tiling.RationalPolygonal.PolygonalRegion} {S : Set Tiling.Plane}
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements S)) :
    S.Countable := by
  let P : Tiling.PolygonalProtoTiling Unit :=
    { prototiles := K.prototileFamily
      placements := K.placements S
      isPolygonal := fun _ => K.isPolygonal }
  let F : S → Set Tiling.Plane := fun s => (s : Tiling.Plane) +ᵥ K.support
  let placementOf : S → P.placements := fun s => ⟨(s, ()), s.2⟩
  have hinj : Function.Injective placementOf := by
    intro s t hst
    exact Subtype.ext (congrArg (fun i : P.placements => i.1.1) hst)
  have hloc : LocallyFinite F := by
    have h := (P.locallyFinite_placedTile hpack).comp_injective hinj
    change LocallyFinite F at h
    exact h
  have hne : ∀ s : S, (F s).Nonempty := by
    intro s
    obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
    exact ⟨s.1 + x, ⟨x, interior_subset hx, rfl⟩⟩
  let _ : Countable S := Set.countable_univ_iff.mp (hloc.countable_univ hne)
  exact Set.countable_coe_iff.mp inferInstance

/-- The longitudinal scalar coordinates of a countable centre set are
countable; nonzero direction makes the affine coordinate unique. -/
private theorem bgtrace_longitudinal_centre_parameters_countable
    {S : Set Tiling.Plane} (hS : S.Countable)
    (s₀ w : Tiling.Plane) (hw : w ≠ 0)
    (hcentres : ∀ s ∈ S, ∃ z : ℝ, s = s₀ + z • w) :
    {z : ℝ | ∃ s ∈ S, s = s₀ + z • w}.Countable := by
  let f : S → ℝ := fun s => Classical.choose (hcentres s.1 s.2)
  have hf (s : S) : s.1 = s₀ + f s • w := Classical.choose_spec (hcentres s.1 s.2)
  let _ : Countable S := Set.countable_coe_iff.mpr hS
  have hrange : {z : ℝ | ∃ s ∈ S, s = s₀ + z • w} = Set.range f := by
    ext z
    constructor
    · rintro ⟨s, hsS, hEq⟩
      let s' : S := ⟨s, hsS⟩
      refine ⟨s', ?_⟩
      have hparam := Classical.choose_spec (hcentres s hsS)
      have hsmul : z • w = f s' • w := by
          have heq : s₀ + z • w = s₀ + f s' • w := hEq.symm.trans hparam
          exact add_left_cancel heq
      exact (smul_left_injective ℝ hw hsmul).symm
    · rintro ⟨s, rfl⟩
      exact ⟨s.1, s.2, hf s⟩
  rw [hrange]
  exact Set.countable_range f

/-- The actual placed-support cover of a complete frontier line induces a
pointwise scalar raw-section cover.  Here `hcentres` is only the affine
coordinate representation of the given one-dimensional centre set; tile
incidence itself is derived from the regular-support frontier and packing. -/
private theorem bgtrace_frontier_line_gives_raw_section_cover
    {K : Tiling.RationalPolygonal.PolygonalRegion} {S : Set Tiling.Plane}
    {Z : Set ℝ} (hpack : Tiling.IsPacking K.prototileFamily (K.placements S))
    (s₀ c w : Tiling.Plane)
    (hcentres : ∀ s ∈ S, ∃ z ∈ Z, s = s₀ + z • w)
    (hline : ∀ t : ℝ, c + t • w ∈ frontier (Tiling.Polygonal.regularSupport K S)) :
    ∀ t : ℝ, ∃ z ∈ Z,
      t ∈ z +ᵥ {r : ℝ | c - s₀ + r • w ∈ K.support} := by
  intro t
  obtain ⟨s, hsS, hsTile⟩ :=
    bgtrace_regularSupport_frontier_point_in_placed_support hpack (hline t)
  obtain ⟨z, hzZ, hsz⟩ := hcentres s hsS
  refine ⟨z, hzZ, ?_⟩
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  have hsTile' : -(s₀ + z • w) +ᵥ (c + t • w) ∈ K.support := by
    rw [hsz] at hsTile
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using hsTile
  have hsTile'' : -(s₀ + z • w) + (c + t • w) ∈ K.support := by
    simpa only [vadd_eq_add] using hsTile'
  have heq : -(s₀ + z • w) + (c + t • w) =
      (c - s₀) + (t - z) • w := by module
  have hraw : t - z ∈ {r : ℝ | c - s₀ + r • w ∈ K.support} := by
    change (c - s₀) + (t - z) • w ∈ K.support
    rw [← heq]
    exact hsTile''
  simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hraw

/--
Along a complete locally straight frontier line, a regular-closed carrier occupies
the same coordinate half-space side at every point.  The local dichotomy is applied
at each point; the two possible germs are disjoint relatively open subsets of the
connected affine line, so only one can occur.
-/
private theorem bgtrace_compact_convex_real_eq_closedInterval
    {C : Set ℝ} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hne : C.Nonempty) : ∃ a b : ℝ, C = Set.Icc a b := by
  obtain ⟨a, ha, hmin⟩ := hcompact.exists_isMinOn hne continuousOn_id
  obtain ⟨b, hb, hmax⟩ := hcompact.exists_isMaxOn hne continuousOn_id
  have hab : a ≤ b := hmin hb
  have hsubset : C ⊆ Set.Icc a b := by
    intro x hx
    exact ⟨hmin hx, hmax hx⟩
  have hreverse : Set.Icc a b ⊆ C := hconvex.isPreconnected.Icc_subset ha hb
  exact ⟨a, b, subset_antisymm hsubset hreverse⟩

/-- A compact polygonal section parametrized by a nonzero tangent vector is compact. -/
private theorem bgtrace_compact_affineLine_parameter_section
    {T : Set Tiling.Plane} (hTcompact : IsCompact T) (hTconvex : Convex ℝ T)
    (hTne : T.Nonempty) (a w : Tiling.Plane) (hw : w ≠ 0) :
    let C : Set ℝ := {r | a + r • w ∈ T}
    IsCompact C ∧ Convex ℝ C := by
  let C : Set ℝ := {r | a + r • w ∈ T}
  have hf : Continuous (fun r : ℝ => a + r • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hclosed : IsClosed C := by
    change IsClosed ((fun r : ℝ => a + r • w) ⁻¹' T)
    exact hTcompact.isClosed.preimage hf
  obtain ⟨R, hR⟩ := hTcompact.isBounded.subset_closedBall (0 : Tiling.Plane)
  have hRnonneg : 0 ≤ R := by
    obtain ⟨z, hz⟩ := hTne
    have hzR := hR hz
    rw [Metric.mem_closedBall, dist_zero_right] at hzR
    exact (norm_nonneg z).trans hzR
  have hwNorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let B : ℝ := (R + ‖a‖) / ‖w‖
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hbounded : Bornology.IsBounded C := by
    apply (Metric.isBounded_Icc (-B) B).subset
    intro r hr
    rw [mem_Icc]
    have hrT : a + r • w ∈ T := hr
    have hrNorm : ‖a + r • w‖ ≤ R := by
      have h := hR hrT
      simpa [Metric.mem_closedBall, dist_zero_right] using h
    have hmul : |r| * ‖w‖ ≤ R + ‖a‖ := by
      calc
        |r| * ‖w‖ = ‖r • w‖ := (norm_smul r w).symm
        _ = ‖(a + r • w) - a‖ := by congr 1; abel
        _ ≤ ‖a + r • w‖ + ‖a‖ := norm_sub_le _ _
        _ ≤ R + ‖a‖ := add_le_add hrNorm le_rfl
    have hquot : |r| ≤ B := (le_div_iff₀ hwNorm).2 (by simpa [B] using hmul)
    exact abs_le.mp hquot
  have hcompact : IsCompact C := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbounded⟩
  have hconvex : Convex ℝ C := by
    intro r hr s hs α β hα hβ hsum
    change a + (α * r + β * s) • w ∈ T
    have heq : a + (α * r + β * s) • w = α • (a + r • w) + β • (a + s • w) := by
      calc
        a + (α * r + β * s) • w = (α + β) • a + (α * r + β * s) • w := by
          rw [hsum]
          simp
        _ = α • (a + r • w) + β • (a + s • w) := by module
    rw [heq]
    change a + r • w ∈ T at hr
    change a + s • w ∈ T at hs
    exact hTconvex hr hs hα hβ hsum
  exact ⟨hcompact, hconvex⟩

/-- A single triangle cuts an actual affine parametrized line in an interval or ∅. -/
private theorem bgtrace_triangle_parameter_section_interval
    {T : Set Tiling.Plane} (hT : Tiling.IsTriangle T)
    (a w : Tiling.Plane) (hw : w ≠ 0) :
    ∃ l u : ℝ,
      {r : ℝ | a + r • w ∈ T} = ∅ ∨
        {r : ℝ | a + r • w ∈ T} = Set.Icc l u := by
  obtain ⟨a₀, b₀, c₀, harea, rfl⟩ := hT
  have hcompact : IsCompact (convexHull ℝ ({a₀, b₀, c₀} : Set Tiling.Plane)) :=
    (Set.toFinite {a₀, b₀, c₀}).isCompact_convexHull ℝ
  have hconvex : Convex ℝ (convexHull ℝ ({a₀, b₀, c₀} : Set Tiling.Plane)) :=
    convex_convexHull ℝ {a₀, b₀, c₀}
  have hne : (convexHull ℝ ({a₀, b₀, c₀} : Set Tiling.Plane)).Nonempty :=
    ⟨a₀, subset_convexHull ℝ _ (by simp)⟩
  have hsection := bgtrace_compact_affineLine_parameter_section hcompact hconvex hne a w hw
  let C : Set ℝ := {r : ℝ | a + r • w ∈ convexHull ℝ ({a₀, b₀, c₀} : Set Tiling.Plane)}
  by_cases hC : C = ∅
  · exact ⟨0, 0, Or.inl (by simpa [C] using hC)⟩
  · have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC
    obtain ⟨l, u, hIcc⟩ := bgtrace_compact_convex_real_eq_closedInterval hsection.1 hsection.2 hCne
    exact ⟨l, u, Or.inr (by simpa [C] using hIcc)⟩

/-- The finite triangulation gives finitely many interval-valued line sections. -/
private theorem bgtrace_polygonal_parameter_sections_finite_intervals
    {K : Tiling.RationalPolygonal.PolygonalRegion}
    (a w : Tiling.Plane) (hw : w ≠ 0) :
    ∃ F : Finset (Set Tiling.Plane),
      (∀ t ∈ F, ∃ l u : ℝ,
        {r : ℝ | a + r • w ∈ t} = ∅ ∨ {r : ℝ | a + r • w ∈ t} = Set.Icc l u) ∧
      {r : ℝ | a + r • w ∈ K.support} =
        ⋃ t ∈ (F : Set (Set Tiling.Plane)), {r : ℝ | a + r • w ∈ t} := by
  obtain ⟨T⟩ := K.isPolygonal
  refine ⟨T.pieces, ?_, ?_⟩
  · intro t ht
    exact bgtrace_triangle_parameter_section_interval (T.isTriangle t ht) a w hw
  · calc
      {r | a + r • w ∈ K.support} =
          {r | a + r • w ∈ ⋃₀ (T.pieces : Set (Set Tiling.Plane))} :=
        congrArg (fun A : Set Tiling.Plane => {r | a + r • w ∈ A}) T.sUnion_eq.symm
      _ = ⋃ t ∈ (T.pieces : Set (Set Tiling.Plane)), {r | a + r • w ∈ t} := by
        ext r
        simp only [Set.mem_ofPred_eq, mem_sUnion, Set.mem_iUnion]
        aesop

/-- A countable family of translates of a polygonal line section cannot cover
the line if every triangle section is only empty or a point.  Thus actual
frontier coverage forces a positive-length polygonal trace interval. -/
private theorem bgtrace_polygonal_raw_section_has_positive_interval_of_countable_cover
    {K : Tiling.RationalPolygonal.PolygonalRegion} {Z : Set ℝ}
    (a w : Tiling.Plane) (hw : w ≠ 0) (hZ : Z.Countable)
    (hcover : ∀ t : ℝ, ∃ z ∈ Z,
      t ∈ z +ᵥ {r : ℝ | a + r • w ∈ K.support}) :
    ∃ l u : ℝ, l < u ∧ Set.Icc l u ⊆ {r : ℝ | a + r • w ∈ K.support} := by
  classical
  by_contra hpos
  push Not at hpos
  obtain ⟨F, hsections, hUnion⟩ := bgtrace_polygonal_parameter_sections_finite_intervals a w hw
  have hpiece_sub (t : Set Tiling.Plane) (ht : t ∈ (F : Set (Set Tiling.Plane))) :
      {r : ℝ | a + r • w ∈ t} ⊆ {r | a + r • w ∈ K.support} := by
    intro r hr
    rw [hUnion]
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, hr⟩⟩
  have hpiece_finite (t : Set Tiling.Plane) (ht : t ∈ (F : Set (Set Tiling.Plane))) :
      ({r : ℝ | a + r • w ∈ t}).Finite := by
    obtain ⟨l, u, hcase⟩ := hsections t ht
    rcases hcase with hempty | hIcc
    · rw [hempty]
      exact Set.finite_empty
    · by_cases hlu : u < l
      · rw [hIcc, Set.Icc_eq_empty_of_lt hlu]
        exact Set.finite_empty
      · have hle : l ≤ u := le_of_not_gt hlu
        have hnot : ¬ l < u := by
          intro hlt
          have hIccSub : Set.Icc l u ⊆ {r : ℝ | a + r • w ∈ t} := by
            rw [← hIcc]
          exact (hpos l u hlt) (hIccSub.trans (hpiece_sub t ht))
        have heq : l = u := le_antisymm hle (le_of_not_gt hnot)
        rw [hIcc, heq, Set.Icc_self]
        exact Set.finite_singleton _
  have hRfinite : ({r : ℝ | a + r • w ∈ K.support}).Finite := by
    rw [hUnion]
    exact F.finite_toSet.biUnion hpiece_finite
  let _ : Countable Z := Set.countable_coe_iff.mpr hZ
  let _ : Countable {r : ℝ // r ∈ {r : ℝ | a + r • w ∈ K.support}} :=
    Set.countable_coe_iff.mpr hRfinite.countable
  let f : Z × {r : ℝ // r ∈ {r : ℝ | a + r • w ∈ K.support}} → ℝ :=
    fun p => p.1 + p.2.1
  have hUnivCount : (Set.univ : Set ℝ).Countable := by
    apply (Set.countable_range f).mono
    intro t ht
    obtain ⟨z, hzZ, htz⟩ := hcover t
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at htz
    let r : ℝ := -z + t
    have hr : r ∈ {r : ℝ | a + r • w ∈ K.support} := htz
    refine ⟨(⟨z, hzZ⟩, ⟨r, hr⟩), ?_⟩
    dsimp [f, r]
    linarith
  exact Set.not_countable_univ hUnivCount

/--
The raw polygonal support section has a finite-interval representative up to
null sets, with degenerate tips omitted.  This is only a measure regularization
of the closed section; no one-sided occupied-side trace interpretation is
asserted here.
-/
private theorem bgtrace_polygonal_parameter_section_regularized_interval_region
    {K : Tiling.RationalPolygonal.PolygonalRegion}
    (a w : Tiling.Plane) (hw : w ≠ 0) :
    ∃ J : Set ℝ, Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion J ∧
      J ⊆ {r | a + r • w ∈ K.support} ∧
        {r | a + r • w ∈ K.support} =ᵐ[volume] J := by
  classical
  obtain ⟨F, hsections, hUnion⟩ := bgtrace_polygonal_parameter_sections_finite_intervals a w hw
  let α := {t : Set Tiling.Plane // t ∈ (F : Set (Set Tiling.Plane))}
  let _ : Fintype α := F.finite_toSet.fintype
  let C : α → Set ℝ := fun t => {r : ℝ | a + r • w ∈ (t : Set Tiling.Plane)}
  have hBounds : ∀ t : α, (C t).Nonempty → ∃ l u : ℝ, C t = Set.Icc l u := by
    intro t hne
    obtain ⟨l, u, hcase⟩ := hsections t.1 t.2
    rcases hcase with hempty | hIcc
    · change C t = ∅ at hempty
      obtain ⟨r, hr⟩ := hne
      rw [hempty] at hr
      simp at hr
    · exact ⟨l, u, hIcc⟩
  choose lo hi hIcc using hBounds
  let lower : α → ℝ := fun t => if h : (C t).Nonempty then lo t h else 0
  let upper : α → ℝ := fun t => if h : (C t).Nonempty then hi t h else 0
  have hsection_le (t : α) : lower t ≤ upper t := by
    by_cases hne : (C t).Nonempty
    · have hEq := hIcc t hne
      have hIccne : (Set.Icc (lo t hne) (hi t hne)).Nonempty := by
        rw [← hEq]
        exact hne
      obtain ⟨r, hr⟩ := hIccne
      have horder' : lo t hne ≤ hi t hne := hr.1.trans hr.2
      simpa [lower, upper, hne] using horder'
    · simp [lower, upper, hne]
  have hcellAE (t : α) : C t =ᵐ[volume] Set.Ioo (lower t) (upper t) := by
    by_cases hne : (C t).Nonempty
    · have hEq : C t = Set.Icc (lower t) (upper t) := by
        simpa [lower, upper, hne] using hIcc t hne
      rw [hEq]
      exact MeasureTheory.Ioo_ae_eq_Icc.symm
    · have hEmpty : C t = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp [hEmpty, lower, upper]
  let G : Finset α := F.attach.filter (fun t => lower t < upper t)
  let J : Set ℝ := ⋃ t ∈ (G : Set α), Set.Ioo (lower t) (upper t)
  have hJ : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion J := by
    letI : Fintype {t : α // t ∈ (G : Set α)} := G.finite_toSet.fintype
    let n : ℕ := Fintype.card {t : α // t ∈ (G : Set α)}
    let e : Fin n ≃ {t : α // t ∈ (G : Set α)} := (Fintype.equivFin _).symm
    refine ⟨n, (fun i => lower (e i).1), (fun i => upper (e i).1), ?_, ?_⟩
    · intro i
      exact (Finset.mem_filter.mp (e i).2).2
    · ext r
      simp only [J, Set.mem_iUnion]
      constructor
      · rintro ⟨t, ht, hr⟩
        obtain ⟨i, hi⟩ := e.surjective ⟨t, ht⟩
        have hval : (e i).1 = t := congrArg Subtype.val hi
        refine ⟨i, ?_⟩
        simpa [hval] using hr
      · rintro ⟨i, hr⟩
        exact ⟨(e i).1, (e i).2, hr⟩
  have hOpenUnion : (⋃ t : α, Set.Ioo (lower t) (upper t)) = J := by
    ext r
    simp only [J, Set.mem_iUnion]
    constructor
    · rintro ⟨t, hr⟩
      by_cases hlt : lower t < upper t
      · exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hlt⟩, hr⟩
      · have heq : lower t = upper t := le_antisymm (hsection_le t) (le_of_not_gt hlt)
        rw [heq] at hr
        simp at hr
    · rintro ⟨t, ht, hr⟩
      exact ⟨t, hr⟩
  have hUnionAE : (⋃ t : α, C t) =ᵐ[volume] J := by
    rw [← hOpenUnion]
    have hall : ∀ᵐ r ∂volume, ∀ t : α,
        (r ∈ C t ↔ r ∈ Set.Ioo (lower t) (upper t)) := by
      apply ae_all_iff.mpr
      intro t
      filter_upwards [hcellAE t] with r hr
      exact Iff.of_eq hr
    filter_upwards [hall] with r hr
    apply propext
    change (r ∈ ⋃ t : α, C t) ↔
      r ∈ ⋃ t : α, Set.Ioo (lower t) (upper t)
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨t, hrt⟩
      exact ⟨t, (hr t).mp hrt⟩
    · rintro ⟨t, hrt⟩
      exact ⟨t, (hr t).mpr hrt⟩
  have hRaw : {r : ℝ | a + r • w ∈ K.support} = ⋃ t : α, C t := by
    calc
      {r : ℝ | a + r • w ∈ K.support} =
          ⋃ t ∈ (F : Set (Set Tiling.Plane)), {r : ℝ | a + r • w ∈ t} := hUnion
      _ = ⋃ t : α, C t := by
        ext r
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨t, ht, hr⟩
          exact ⟨⟨t, ht⟩, hr⟩
        · rintro ⟨t, hr⟩
          exact ⟨t.1, t.2, hr⟩
  have hJsubset : J ⊆ {r : ℝ | a + r • w ∈ K.support} := by
    rw [hRaw, ← hOpenUnion]
    intro r hr
    obtain ⟨t, hrt⟩ := Set.mem_iUnion.mp hr
    have hne : (C t).Nonempty := by
      by_contra hn
      simp [lower, upper, hn] at hrt
    have hIcc : C t = Set.Icc (lower t) (upper t) := by
      simpa [lower, upper, hne] using hIcc t hne
    have hrIcc : r ∈ Set.Icc (lower t) (upper t) := ⟨hrt.1.le, hrt.2.le⟩
    have hrC : r ∈ C t := by rw [hIcc]; exact hrIcc
    exact Set.mem_iUnion.mpr ⟨t, hrC⟩
  refine ⟨J, hJ, hJsubset, ?_⟩
  rw [hRaw]
  exact hUnionAE

/-- A finite open-interval representative AE-equal to a raw section has
positive measure whenever that raw section contains a nondegenerate interval. -/
private theorem bgtrace_finiteIntervalRegion_positive_of_ae_interval
    {J R : Set ℝ} (hJ : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion J)
    (hRAE : R =ᵐ[volume] J) {l u : ℝ} (hlu : l < u)
    (hIcc : Set.Icc l u ⊆ R) : 0 < (volume J).toReal := by
  have hIne : (Set.Ioo l u).Nonempty := ⟨(l + u) / 2, by constructor <;> linarith⟩
  have hIpos : 0 < volume (Set.Ioo l u) := isOpen_Ioo.measure_pos volume hIne
  have hJne : J.Nonempty := by
    by_contra hne
    have hJempty : J = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hRaeEmpty : R =ᵐ[volume] (∅ : Set ℝ) := by
      simpa [hJempty] using hRAE
    have hRzero : volume R = 0 := by
      have h := MeasureTheory.measure_congr hRaeEmpty
      simpa using h
    have hIle : volume (Set.Ioo l u) ≤ volume R :=
      measure_mono (fun x hx => hIcc ⟨hx.1.le, hx.2.le⟩)
    rw [hRzero] at hIle
    exact (not_lt_of_ge hIle) hIpos
  have hJopen : IsOpen J :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.IsFiniteIntervalRegion.isOpen hJ
  have hJmeasure : volume J ≠ 0 := hJopen.measure_ne_zero volume hJne
  exact ENNReal.toReal_pos hJmeasure
    (Tiling.AxisParallel.OneDimensional.FiniteInterval.IsFiniteIntervalRegion.measure_ne_top hJ)

/-- Actual pointwise frontier-line coverage by countably many polygonal
centres produces a positive finite-interval trace after zero tips are omitted. -/
private theorem bgtrace_polygonal_frontier_trace_positive_interval_region
    {K : Tiling.RationalPolygonal.PolygonalRegion} {Z : Set ℝ}
    (a w : Tiling.Plane) (hw : w ≠ 0) (hZ : Z.Countable)
    (hcover : ∀ t : ℝ, ∃ z ∈ Z,
      t ∈ z +ᵥ {r : ℝ | a + r • w ∈ K.support}) :
    ∃ J : Set ℝ, Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion J ∧
      J ⊆ {r : ℝ | a + r • w ∈ K.support} ∧
      {r : ℝ | a + r • w ∈ K.support} =ᵐ[volume] J ∧ 0 < (volume J).toReal := by
  obtain ⟨l, u, hlu, hIcc⟩ := bgtrace_polygonal_raw_section_has_positive_interval_of_countable_cover
    a w hw hZ hcover
  obtain ⟨J, hJ, hJsub, hRAE⟩ := bgtrace_polygonal_parameter_section_regularized_interval_region a w hw
  have hJpositive := bgtrace_finiteIntervalRegion_positive_of_ae_interval hJ hRAE hlu hIcc
  exact ⟨J, hJ, hJsub, hRAE, hJpositive⟩


/--
In any chosen longitudinal scalar coordinate, each triangle's line section maps
to either the empty set or one closed interval.  This isolates the affine-chart
choice from the finite-triangulation step without assuming any interval trace.
-/
private theorem bgtrace_finiteIntervalTrace_period_and_mass
    {J Z : Set ℝ}
    (hJ : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion J)
    (hJpos : 0 < (volume J).toReal)
    (hTile : Tiling.AxisParallel.OneDimensional.LineTiles J Z) :
    ∃ q : ℝ, 0 < q ∧ q +ᵥ Z = Z ∧
      (Z ∩ Set.Ico 0 q).Finite ∧ (Z ∩ Set.Ico 0 q).Nonempty ∧
        q = (volume J).toReal * Set.ncard (Z ∩ Set.Ico 0 q) := by
  obtain ⟨q, hq, hperiod⟩ :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.exists_positiveLinePeriod
      hJ hJpos hTile
  let P := IntervalPresentation.ofIsFiniteIntervalRegion hJ
  obtain ⟨hfinite, hnonempty, hmass⟩ :=
    Tiling.AxisParallel.Foundations.linePeriod_mass P.isBounded hJpos hTile hq hperiod
  exact ⟨q, hq, hperiod, hfinite, hnonempty, hmass⟩

/-- Transfer a literal pointwise raw-section cover to the finite open-interval
representative after the polygonal overlap argument has established pairwise
almost-everywhere disjointness. -/
private theorem bgtrace_rawSection_cover_to_finiteInterval_LineTiles
    {R J Z : Set ℝ} (hR : MeasurableSet R)
    (hJ : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion J)
    (hRAE : R =ᵐ[volume] J) (hZ : Z.Countable)
    (hcover : ∀ x : ℝ, ∃ z ∈ Z, x ∈ z +ᵥ R)
    (hdisj : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' →
      AEDisjoint volume (z +ᵥ R) (z' +ᵥ R)) :
    Tiling.AxisParallel.OneDimensional.LineTiles J Z := by
  have hRaw : Tiling.AxisParallel.OneDimensional.LineTilesOn R Z Set.univ := by
    refine ⟨hR, MeasurableSet.univ, hZ, ?_, ?_⟩
    · intro z hz z' hz' hne
      exact hdisj z hz z' hz' hne
    · filter_upwards [] with x
      constructor
      · intro _
        obtain ⟨z, hz, hxz⟩ := hcover x
        exact ⟨⟨z, hz⟩, hxz⟩
      · intro _
        trivial
  have hJmeas : MeasurableSet J :=
    (Tiling.AxisParallel.OneDimensional.FiniteInterval.IsFiniteIntervalRegion.isOpen
      hJ).measurableSet
  have hJTile :=
    (Tiling.AxisParallel.Foundations.lineTilesOn_congr_ae hR hJmeas hRAE).mp hRaw
  simpa only [Tiling.AxisParallel.OneDimensional.LineTiles] using hJTile

/-- A locally occupied strict halfspace of the open regular support leaves the
opposite strict halfspace in the interior of the complement of its closed
carrier.  This is the closed-carrier conversion needed by support collision
arguments; points on the frontier itself are not excluded. -/
private theorem bgtrace_actual_polygonal_frontierLine_LineTiles
    {K : Tiling.RationalPolygonal.PolygonalRegion} {S : Set Tiling.Plane}
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements S))
    (c w : Tiling.Plane) (hw : w ≠ 0)
    (hcentres : ∀ s ∈ S, ∃ z : ℝ, s = z • w)
    {L : AffineSubspace ℝ Tiling.Plane} (hcL : c ∈ L)
    (hLdim : Module.finrank ℝ L.direction = 1) (hwL : w ∈ L.direction)
    (ψ : Tiling.Plane →L[ℝ] ℝ) (hψ : Function.Surjective ψ)
    (hLψ : (L : Set Tiling.Plane) = {x | ψ x = ψ c})
    (hLfront : (L : Set Tiling.Plane) ⊆
      frontier (closure (Tiling.Polygonal.regularSupport K S)))
    (hline : ∀ t : ℝ,
      c + t • w ∈ frontier (Tiling.Polygonal.regularSupport K S))
    (hDvacant : ∀ x ∈ (L : Set Tiling.Plane), ∃ r : ℝ, 0 < r ∧
      Metric.ball x r ∩ {y | ψ y < ψ x} ⊆
        interior ((closure (Tiling.Polygonal.regularSupport K S))ᶜ)) :
    ∃ J : Set ℝ, Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion J ∧
      0 < (volume J).toReal ∧
        Tiling.AxisParallel.OneDimensional.LineTiles J
          {z : ℝ | ∃ s ∈ S, s = z • w} ∧
        ∃ q : ℝ, 0 < q ∧
          q +ᵥ {z : ℝ | ∃ s ∈ S, s = z • w} = {z : ℝ | ∃ s ∈ S, s = z • w} ∧
            ({z : ℝ | ∃ s ∈ S, s = z • w} ∩ Set.Ico 0 q).Finite ∧
              ({z : ℝ | ∃ s ∈ S, s = z • w} ∩ Set.Ico 0 q).Nonempty ∧
                q = (volume J).toReal * Set.ncard
                  ({z : ℝ | ∃ s ∈ S, s = z • w} ∩ Set.Ico 0 q) := by
  let Z : Set ℝ := {z : ℝ | ∃ s ∈ S, s = z • w}
  have hcentresZ : ∀ s ∈ S, ∃ z ∈ Z, s = 0 + z • w := by
    intro s hs
    obtain ⟨z, hsz⟩ := hcentres s hs
    refine ⟨z, ?_, ?_⟩
    · exact ⟨s, hs, hsz⟩
    · simpa using hsz
  have hSCountable := bgtrace_polygonal_packing_centres_countable hpack
  have hZCountable : Z.Countable := by
    simpa [Z] using bgtrace_longitudinal_centre_parameters_countable hSCountable 0 w hw
      (fun s hs => by simpa [zero_add] using hcentres s hs)
  have hcover0 := bgtrace_frontier_line_gives_raw_section_cover hpack 0 c w hcentresZ hline
  have hcover : ∀ t : ℝ, ∃ z ∈ Z,
      t ∈ z +ᵥ {r : ℝ | c + r • w ∈ K.support} := by
    simpa [sub_zero] using hcover0
  obtain ⟨J, hJ, hJsub, hRAE, hJpos⟩ :=
    bgtrace_polygonal_frontier_trace_positive_interval_region c w hw hZCountable hcover
  let R : Set ℝ := {r : ℝ | c + r • w ∈ K.support}
  have hRclosed : IsClosed R := by
    dsimp [R]
    exact K.isPolygonal.isClosed.preimage
      (continuous_const.add (continuous_id.smul continuous_const))
  have hRmeas : MeasurableSet R := hRclosed.measurableSet
  have hsubset : ∀ z ∈ Z, (z • w) +ᵥ K.support ⊆
      closure (Tiling.Polygonal.regularSupport K S) := by
    intro z hz
    obtain ⟨s, hs, hsz⟩ := hz
    have htile := bgtrace_placed_support_subset_closedRegularSupport hpack hs
    simpa [hsz] using htile
  have hcentresPacking : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' →
      AEDisjoint volume ((z • w) +ᵥ K.support) ((z' • w) +ᵥ K.support) := by
    intro z hz z' hz' hzz'
    obtain ⟨s, hs, hsz⟩ := hz
    obtain ⟨s', hs', hsz'⟩ := hz'
    let p : K.placements S := ⟨(z • w, ()), by simpa [hsz] using hs⟩
    let q : K.placements S := ⟨(z' • w, ()), by simpa [hsz'] using hs'⟩
    have hpq : (p : Tiling.Placement Tiling.Plane Unit) ≠ q := by
      intro hpq
      apply hzz'
      have hcentereq : z • w = z' • w := by
        have h := congrArg (fun i : Tiling.Placement Tiling.Plane Unit => i.1) hpq
        change z • w = z' • w
        exact h
      exact (smul_left_injective ℝ hw hcentereq)
    have h := hpack p.2 q.2 hpq
    change AEDisjoint volume ((z • w) +ᵥ K.support) ((z' • w) +ᵥ K.support) at h
    exact h
  have hdisj : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' →
      AEDisjoint volume (z +ᵥ R) (z' +ᵥ R) := by
    intro z hz z' hz' hzz'
    have hJdisj := bgtrace_translated_polygonal_open_sections_disjoint
      (K := K) (D := closure (Tiling.Polygonal.regularSupport K S))
      (L := L) (x := c) (w := w) (ψ := ψ) (J := J) (Z := Z)
      K.isPolygonal hJ hJsub hcL hLdim hwL hw hLfront hLψ hψ hDvacant
      hsubset hcentresPacking hz hz' hzz'
    have hJae : AEDisjoint volume (z +ᵥ J) (z' +ᵥ J) := hJdisj.aedisjoint
    have hRae : z +ᵥ R =ᵐ[volume] z +ᵥ J :=
      (quasiMeasurePreserving_add_left volume (-z)).vadd_ae_eq_of_ae_eq z hRAE
    have hR'ae : z' +ᵥ R =ᵐ[volume] z' +ᵥ J :=
      (quasiMeasurePreserving_add_left volume (-z')).vadd_ae_eq_of_ae_eq z' hRAE
    exact hJae.mono_ae hRae.le hR'ae.le
  have hTile := bgtrace_rawSection_cover_to_finiteInterval_LineTiles
    hRmeas hJ hRAE hZCountable hcover hdisj
  have hTile' : Tiling.AxisParallel.OneDimensional.LineTiles J
      {z : ℝ | ∃ s ∈ S, s = z • w} := by
    simpa [Z, R] using hTile
  obtain ⟨q, hq, hperiod, hfinite, hnonempty, hmass⟩ :=
    bgtrace_finiteIntervalTrace_period_and_mass hJ hJpos hTile'
  exact ⟨J, hJ, hJpos, hTile', q, hq, hperiod, hfinite, hnonempty, hmass⟩

/-- A period of the scalar center-coordinate set lifts to translation by the
corresponding longitudinal vector on the original center set. -/
private theorem bgtrace_scalar_period_lifts_to_vector_period
    {S : Set Tiling.Plane} {w : Tiling.Plane} {q : ℝ}
    (hcentres : ∀ s ∈ S, ∃ z : ℝ, s = z • w)
    (hperiod : q +ᵥ {z : ℝ | ∃ s ∈ S, s = z • w} =
      {z : ℝ | ∃ s ∈ S, s = z • w}) :
    (q • w) +ᵥ S = S := by
  let Z : Set ℝ := {z : ℝ | ∃ s ∈ S, s = z • w}
  have hrepr (x : Tiling.Plane) : x ∈ S ↔ ∃ z ∈ Z, x = z • w := by
    constructor
    · intro hx
      obtain ⟨z, hzx⟩ := hcentres x hx
      exact ⟨z, ⟨x, hx, hzx⟩, hzx⟩
    · rintro ⟨z, ⟨s, hs, hsz⟩, hxz⟩
      exact hxz ▸ hsz ▸ hs
  have hperiod' : q +ᵥ Z = Z := by simpa [Z] using hperiod
  ext x
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  rw [hrepr, hrepr]
  constructor
  · rintro ⟨z, hz, hx⟩
    have hqz : q + z ∈ Z := by
      rw [← hperiod']
      exact Set.mem_vadd_set.mpr ⟨z, hz, rfl⟩
    have hxadd : -(q • w) + x = z • w := by
      simpa only [vadd_eq_add] using hx
    have hx' : x = (q + z) • w := by
      calc
        x = q • w + (-(q • w) + x) := by abel
        _ = q • w + z • w := by rw [hxadd]
        _ = (q + z) • w := by module
    exact ⟨q + z, hqz, hx'⟩
  · rintro ⟨z, hz, hx⟩
    have hm : z ∈ q +ᵥ Z := by
      have htemp := hz
      rw [← hperiod'] at htemp
      exact htemp
    have hminus : -q + z ∈ Z := by
      simpa using (Set.mem_vadd_set_iff_neg_vadd_mem.mp hm)
    have hxadd : -q • w + x = (-q + z) • w := by
      rw [hx]
      module
    exact ⟨-q + z, hminus, by simpa only [vadd_eq_add, neg_smul] using hxadd⟩

/-- The two possible occupied-side orientations from the complete-frontier
halfspace dichotomy both feed the same genuine trace construction.  In the
upper-vacant case, negating the transverse coordinate preserves its kernel and
turns that vacancy into the lower-vacant convention used by the collision
argument. -/
private theorem bgtrace_actual_polygonal_frontierLine_LineTiles_of_either_vacancy
    {K : Tiling.RationalPolygonal.PolygonalRegion} {S : Set Tiling.Plane}
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements S))
    (c w : Tiling.Plane) (hw : w ≠ 0)
    (hcentres : ∀ s ∈ S, ∃ z : ℝ, s = z • w)
    {L : AffineSubspace ℝ Tiling.Plane} (hcL : c ∈ L)
    (hLdim : Module.finrank ℝ L.direction = 1) (hwL : w ∈ L.direction)
    (ψ : Tiling.Plane →L[ℝ] ℝ) (hψ : Function.Surjective ψ)
    (hLψ : (L : Set Tiling.Plane) = {x | ψ x = ψ c})
    (hLfront : (L : Set Tiling.Plane) ⊆
      frontier (closure (Tiling.Polygonal.regularSupport K S)))
    (hline : ∀ t : ℝ,
      c + t • w ∈ frontier (closure (Tiling.Polygonal.regularSupport K S)))
    (hside :
      (∀ x ∈ (L : Set Tiling.Plane), ∃ r : ℝ, 0 < r ∧
        Metric.ball x r ∩ {y | ψ x < ψ y} ⊆
          interior ((closure (Tiling.Polygonal.regularSupport K S))ᶜ)) ∨
      (∀ x ∈ (L : Set Tiling.Plane), ∃ r : ℝ, 0 < r ∧
        Metric.ball x r ∩ {y | ψ y < ψ x} ⊆
          interior ((closure (Tiling.Polygonal.regularSupport K S))ᶜ))) :
    ∃ J : Set ℝ, Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion J ∧
      0 < (volume J).toReal ∧
        Tiling.AxisParallel.OneDimensional.LineTiles J
          {z : ℝ | ∃ s ∈ S, s = z • w} ∧
        ∃ q : ℝ, 0 < q ∧
          q +ᵥ {z : ℝ | ∃ s ∈ S, s = z • w} = {z : ℝ | ∃ s ∈ S, s = z • w} ∧
              ({z : ℝ | ∃ s ∈ S, s = z • w} ∩ Set.Ico 0 q).Finite ∧
              ({z : ℝ | ∃ s ∈ S, s = z • w} ∩ Set.Ico 0 q).Nonempty ∧
                q = (volume J).toReal * Set.ncard
                  ({z : ℝ | ∃ s ∈ S, s = z • w} ∩ Set.Ico 0 q) ∧
                  (q • w) +ᵥ S = S := by
  have hfrontEq := bgtrace_regularSupport_frontier_eq_closedRegularSupport_frontier K S
  have hlineOpen : ∀ t : ℝ,
      c + t • w ∈ frontier (Tiling.Polygonal.regularSupport K S) := by
    intro t
    simpa only [hfrontEq] using hline t
  have finish_output :
      ∃ J : Set ℝ, Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion J ∧
        0 < (volume J).toReal ∧
          Tiling.AxisParallel.OneDimensional.LineTiles J
            {z : ℝ | ∃ s ∈ S, s = z • w} ∧
          ∃ q : ℝ, 0 < q ∧
            q +ᵥ {z : ℝ | ∃ s ∈ S, s = z • w} =
              {z : ℝ | ∃ s ∈ S, s = z • w} ∧
              ({z : ℝ | ∃ s ∈ S, s = z • w} ∩ Set.Ico 0 q).Finite ∧
                ({z : ℝ | ∃ s ∈ S, s = z • w} ∩ Set.Ico 0 q).Nonempty ∧
                  q = (volume J).toReal * Set.ncard
                    ({z : ℝ | ∃ s ∈ S, s = z • w} ∩ Set.Ico 0 q) := by
    rcases hside with hupper | hlower
    · have hψneg : Function.Surjective (-ψ) := by
        intro t
        obtain ⟨x, hx⟩ := hψ (-t)
        exact ⟨x, by simpa using congrArg Neg.neg hx⟩
      have hLψneg : (L : Set Tiling.Plane) = {x | (-ψ) x = (-ψ) c} := by
        rw [hLψ]
        ext x
        simp
      have hvacant : ∀ x ∈ (L : Set Tiling.Plane), ∃ r : ℝ, 0 < r ∧
          Metric.ball x r ∩ {y | (-ψ) y < (-ψ) x} ⊆
            interior ((closure (Tiling.Polygonal.regularSupport K S))ᶜ) := by
        intro x hx
        obtain ⟨r, hr, hlocal⟩ := hupper x hx
        refine ⟨r, hr, ?_⟩
        intro y hy
        apply hlocal ⟨hy.1, ?_⟩
        simpa using hy.2
      exact bgtrace_actual_polygonal_frontierLine_LineTiles hpack c w hw hcentres hcL
        hLdim hwL (-ψ) hψneg hLψneg hLfront hlineOpen hvacant
    · exact bgtrace_actual_polygonal_frontierLine_LineTiles hpack c w hw hcentres hcL
        hLdim hwL ψ hψ hLψ hLfront hlineOpen hlower
  obtain ⟨J, hJ, hJpos, hTiles, q, hq, hqperiod, hfinite, hnonempty, hmass⟩ :=
    finish_output
  have hvector := bgtrace_scalar_period_lifts_to_vector_period hcentres hqperiod
  exact ⟨J, hJ, hJpos, hTiles, q, hq, hqperiod, hfinite, hnonempty, hmass,
    hvector⟩

private theorem isPacking_centres_vadd_local
    {K : PolygonalRegion} {S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements S)) (z : Plane) :
    IsPacking K.prototileFamily (K.placements (z +ᵥ S)) := by
  apply (isPacking_iff_openCarrier_disjoint K (z +ᵥ S)).mpr
  intro s hs t ht hst
  obtain ⟨s₀, hs₀, rfl⟩ := Set.mem_vadd_set.mp hs
  obtain ⟨t₀, ht₀, rfl⟩ := Set.mem_vadd_set.mp ht
  have hne : s₀ ≠ t₀ := fun h => hst (congrArg (fun x : Plane => z +ᵥ x) h)
  have hd := (isPacking_iff_openCarrier_disjoint K S).mp hp hs₀ ht₀ hne
  apply Set.disjoint_left.mpr
  intro p hpS hpT
  have hpS' : -z +ᵥ p ∈ s₀ +ᵥ K.openCarrier := by
    apply Set.mem_vadd_set_iff_neg_vadd_mem.mp
    simpa only [vadd_vadd, vadd_eq_add] using hpS
  have hpT' : -z +ᵥ p ∈ t₀ +ᵥ K.openCarrier := by
    apply Set.mem_vadd_set_iff_neg_vadd_mem.mp
    simpa only [vadd_vadd, vadd_eq_add] using hpT
  exact Set.disjoint_left.mp hd hpS' hpT'

private theorem bgtrace_frontier_translate
    (u : Tiling.Plane) (D : Set Tiling.Plane) :
    frontier (u +ᵥ D) = u +ᵥ frontier D := by
  rw [frontier, closure_vadd, interior_vadd]
  ext x
  simp only [frontier, Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem]

/-- A strict halfspace vacancy germ is preserved when both the carrier and
the level coordinate are translated by the same vector. -/
private theorem bgtrace_translate_vacancy_germ
    {D : Set Tiling.Plane} (u a : Tiling.Plane)
    (π : Tiling.Plane →L[ℝ] ℝ) (rel : ℝ → ℝ → Prop)
    (hrel : ∀ b x y, rel (b + x) (b + y) ↔ rel x y)
    (hvacant : ∀ x : Tiling.Plane, π x = π a → ∃ r : ℝ, 0 < r ∧
      Metric.ball x r ∩ {y | rel (π x) (π y)} ⊆ interior Dᶜ) :
    ∀ x' : Tiling.Plane, π x' = π (u +ᵥ a) → ∃ r : ℝ, 0 < r ∧
      Metric.ball x' r ∩ {y' | rel (π x') (π y')} ⊆
        interior ((u +ᵥ D)ᶜ) := by
  have hcompl : (u +ᵥ D)ᶜ = u +ᵥ Dᶜ := by
    ext y
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have hinterior : interior ((u +ᵥ D)ᶜ) = u +ᵥ interior Dᶜ := by
    rw [hcompl, interior_vadd]
  intro x' hx'
  let x := -u +ᵥ x'
  have hxcoord : π x = π a := by
    have hxp : π x' = π u + π x := by
      simp [x, vadd_eq_add, map_add, map_neg]
    have hap : π (u +ᵥ a) = π u + π a := by
      simp [vadd_eq_add, map_add]
    rw [hap] at hx'
    linarith [hxp]
  obtain ⟨r, hr, hlocal⟩ := hvacant x hxcoord
  refine ⟨r, hr, ?_⟩
  intro y' hy'
  let y := -u +ᵥ y'
  rcases hy' with ⟨hyball', hyrel'⟩
  have hyball : y ∈ Metric.ball x r := by
    rw [Metric.mem_ball] at hyball' ⊢
    have hdist : dist y x = dist y' x' := by
      simp [x, y, vadd_eq_add, dist_eq_norm_sub]
    rw [hdist]
    exact hyball'
  have hpy : π y' = π u + π y := by
    simp [y, vadd_eq_add, map_add, map_neg]
  have hpx : π x' = π u + π x := by
    simp [x, vadd_eq_add, map_add, map_neg]
  have hyrel : rel (π x) (π y) := by
    apply (hrel (π u) (π x) (π y)).mp
    change rel (π x') (π y') at hyrel'
    simpa only [hpx, hpy] using hyrel'
  have hout := hlocal ⟨hyball, hyrel⟩
  have htranslated : y' ∈ u +ᵥ interior Dᶜ :=
    Set.mem_vadd_set.mpr ⟨y, hout, by simp [y, vadd_eq_add]⟩
  simpa only [hinterior] using htranslated

/-- The normalized trace-period construction in the original anchor
coordinates.  Center-line support gives centers on `ℝ • w` after translating
by `-s`; the actual complete-carrier vacancy dichotomy is transported across
that same translation, then the checked polygonal trace/period adapter yields
the vector period, which is translated back to the original center set. -/
private theorem bgtrace_original_anchor_trace_period
    {K : Tiling.RationalPolygonal.PolygonalRegion}
    {δ : Submodule ℝ Tiling.Plane} {S : Set Tiling.Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (π : Tiling.Plane →L[ℝ] ℝ) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π.toLinearMap = δ)
    (hpack : Tiling.IsPacking K.prototileFamily (K.placements S))
    (hlineSupported : ∃ b : Tiling.Plane, ∀ t ∈ S, t - b ∈ δ)
    (s : Tiling.Plane) (hs : s ∈ S)
    (w : Tiling.Plane) (hw : w ≠ 0) (hwδ : w ∈ δ)
    (a : Tiling.Plane)
    (hfrontline : a +ᵥ (δ : Set Tiling.Plane) ⊆
      frontier (Tiling.Polygonal.regularSupport K S))
    (hvacant :
      (∀ x : Tiling.Plane, π x = π a → ∃ r : ℝ, 0 < r ∧
        Metric.ball x r ∩ {y | π y < π x} ⊆
          interior ((closure (Tiling.Polygonal.regularSupport K S))ᶜ)) ∨
      (∀ x : Tiling.Plane, π x = π a → ∃ r : ℝ, 0 < r ∧
        Metric.ball x r ∩ {y | π x < π y} ⊆
          interior ((closure (Tiling.Polygonal.regularSupport K S))ᶜ))) :
    ∃ q : ℝ, 0 < q ∧ (q • w) +ᵥ S = S := by
  obtain ⟨b, hb⟩ := hlineSupported
  have hsδ : s - b ∈ δ := hb s hs
  have hcentred : ∀ t ∈ S, t - s ∈ δ := by
    intro t ht
    have h := δ.sub_mem (hb t ht) hsδ
    simpa [sub_sub] using h
  let u : Tiling.Plane := -s
  let S' : Set Tiling.Plane := u +ᵥ S
  let c : Tiling.Plane := a + u
  have hpack' : Tiling.IsPacking K.prototileFamily (K.placements S') :=
    isPacking_centres_vadd_local hpack u
  have hspan : δ = Submodule.span ℝ ({w} : Set Tiling.Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ hwδ hw
  have hcentres' : ∀ t ∈ S', ∃ z : ℝ, t = z • w := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Set.mem_vadd_set.mp ht
    have hδt : t₀ - s ∈ δ := hcentred t₀ ht₀
    have hδt' : u + t₀ ∈ δ := by
      simpa [u, sub_eq_add_neg, add_comm] using hδt
    rw [hspan] at hδt'
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hδt'
    exact ⟨z, by simpa [u, vadd_eq_add] using hz.symm⟩
  have hlineSet : c +ᵥ (δ : Set Tiling.Plane) =
      u +ᵥ (a +ᵥ (δ : Set Tiling.Plane)) := by
    dsimp [c]
    calc
      (a + u) +ᵥ (δ : Set Tiling.Plane) = (u + a) +ᵥ (δ : Set Tiling.Plane) := by
        rw [add_comm a u]
      _ = u +ᵥ (a +ᵥ (δ : Set Tiling.Plane)) := by rw [← vadd_vadd]
  have hfrontline' : c +ᵥ (δ : Set Tiling.Plane) ⊆
      frontier (Tiling.Polygonal.regularSupport K S') := by
    rw [hlineSet, show Tiling.Polygonal.regularSupport K S' =
      u +ᵥ Tiling.Polygonal.regularSupport K S by
        simpa [S'] using Tiling.Polygonal.regularSupport_vadd K S u,
      bgtrace_frontier_translate]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.mp hx
    exact Set.mem_vadd_set.mpr ⟨y, hfrontline hy, hxy⟩
  have hline' : ∀ t : ℝ,
      c + t • w ∈ frontier (Tiling.Polygonal.regularSupport K S') := by
    intro t
    apply hfrontline'
    exact Set.mem_vadd_set.mpr ⟨t • w, δ.smul_mem t hwδ, by simp [c, u, vadd_eq_add]⟩
  have hclosedShift : closure (Tiling.Polygonal.regularSupport K S') =
      u +ᵥ closure (Tiling.Polygonal.regularSupport K S) := by
    rw [show Tiling.Polygonal.regularSupport K S' =
      u +ᵥ Tiling.Polygonal.regularSupport K S by
        simpa [S'] using Tiling.Polygonal.regularSupport_vadd K S u,
      closure_vadd]
  have hside' :
      (∀ x : Tiling.Plane, π x = π c → ∃ r : ℝ, 0 < r ∧
        Metric.ball x r ∩ {y | π x < π y} ⊆
          interior ((closure (Tiling.Polygonal.regularSupport K S'))ᶜ)) ∨
      (∀ x : Tiling.Plane, π x = π c → ∃ r : ℝ, 0 < r ∧
        Metric.ball x r ∩ {y | π y < π x} ⊆
          interior ((closure (Tiling.Polygonal.regularSupport K S'))ᶜ)) := by
    rcases hvacant with hlower | hupper
    · right
      intro x hx
      have hxc : π x = π (u +ᵥ a) := by
        simpa [c, u, vadd_eq_add, add_comm] using hx
      have h := bgtrace_translate_vacancy_germ (D := closure
          (Tiling.Polygonal.regularSupport K S)) u a π (fun x y => y < x)
          (by intro b x y; constructor <;> intro h <;> linarith) hlower x hxc
      simpa only [← hclosedShift] using h
    · left
      intro x hx
      have hxc : π x = π (u +ᵥ a) := by
        simpa [c, u, vadd_eq_add, add_comm] using hx
      have h := bgtrace_translate_vacancy_germ (D := closure
          (Tiling.Polygonal.regularSupport K S)) u a π (fun x y => x < y)
          (by intro b x y; constructor <;> intro h <;> linarith) hupper x hxc
      simpa only [← hclosedShift] using h
  let L : AffineSubspace ℝ Tiling.Plane := AffineSubspace.mk' c δ
  have hcL : c ∈ L := AffineSubspace.self_mem_mk' c δ
  have hLdim : Module.finrank ℝ L.direction = 1 := by
    rw [AffineSubspace.direction_mk']
    exact hδ
  have hwL : w ∈ L.direction := by
    rw [AffineSubspace.direction_mk']
    exact hwδ
  have hLψ : (L : Set Tiling.Plane) = {x | π x = π c} := by
    ext x
    change x - c ∈ δ ↔ π x = π c
    rw [← hker, LinearMap.mem_ker, map_sub]
    exact sub_eq_zero
  have hfrontEq := bgtrace_regularSupport_frontier_eq_closedRegularSupport_frontier K S'
  have hlineClosed : ∀ t : ℝ,
      c + t • w ∈ frontier (closure (Tiling.Polygonal.regularSupport K S')) := by
    intro t
    simpa only [hfrontEq] using hline' t
  have hLfront : (L : Set Tiling.Plane) ⊆
      frontier (closure (Tiling.Polygonal.regularSupport K S')) := by
    intro x hx
    have hxline : x ∈ c +ᵥ (δ : Set Tiling.Plane) := by
      change x ∈ AffineSubspace.mk' c δ at hx
      rw [AffineSubspace.mem_mk'] at hx
      exact Set.mem_vadd_set.mpr ⟨x - c, hx, by simp [vadd_eq_add]⟩
    have h := hfrontline' hxline
    simpa only [hfrontEq] using h
  rcases hside' with hupper' | hlower'
  · have hsideLine : ∀ x ∈ (L : Set Tiling.Plane), ∃ r : ℝ, 0 < r ∧
        Metric.ball x r ∩ {y | π x < π y} ⊆
          interior ((closure (Tiling.Polygonal.regularSupport K S'))ᶜ) := by
      intro x hx
      have hx' : x ∈ {y | π y = π c} := by rw [← hLψ]; exact hx
      exact hupper' x hx'
    obtain ⟨J, hJ, hJpos, hTiles, q, hq, hqperiod, hfinite, hnonempty, hmass,
      hvector⟩ := bgtrace_actual_polygonal_frontierLine_LineTiles_of_either_vacancy
        hpack' c w hw hcentres' hcL hLdim hwL π hπ hLψ hLfront hlineClosed (Or.inl hsideLine)
    have hperiodOrig : (q • w) +ᵥ S = S := by
      have htranslated := congrArg (fun A : Set Tiling.Plane => s +ᵥ A) hvector
      simpa [S', u, vadd_vadd, add_assoc, add_comm, add_left_comm] using htranslated
    exact ⟨q, hq, hperiodOrig⟩
  · have hsideLine : ∀ x ∈ (L : Set Tiling.Plane), ∃ r : ℝ, 0 < r ∧
        Metric.ball x r ∩ {y | π y < π x} ⊆
          interior ((closure (Tiling.Polygonal.regularSupport K S'))ᶜ) := by
      intro x hx
      have hx' : x ∈ {y | π y = π c} := by rw [← hLψ]; exact hx
      exact hlower' x hx'
    obtain ⟨J, hJ, hJpos, hTiles, q, hq, hqperiod, hfinite, hnonempty, hmass,
      hvector⟩ := bgtrace_actual_polygonal_frontierLine_LineTiles_of_either_vacancy
        hpack' c w hw hcentres' hcL hLdim hwL π hπ hLψ hLfront hlineClosed (Or.inr hsideLine)
    have hperiodOrig : (q • w) +ᵥ S = S := by
      have htranslated := congrArg (fun A : Set Tiling.Plane => s +ᵥ A) hvector
      simpa [S', u, vadd_vadd, add_assoc, add_comm, add_left_comm] using htranslated
    exact ⟨q, hq, hperiodOrig⟩

end TracePeriodProofs

section GenericSliceMassProofs

open scoped ENNReal

/-- A complete line of actual half-space germs has a uniform filled collar
over any compact parameter cell. This uses the open locus of equality of
germs, not an almost-everywhere section statement. -/
private theorem complete_line_uniform_positive_collar
    {D : Set Plane} {a e w : Plane} {ψ : Plane →L[ℝ] ℝ} {c q : ℝ}
    (hopen : IsOpen D) (_hq : 0 < q) (hψa : ψ a = c)
    (hψw : ψ w = 0) (hψe : 0 < ψ e)
    (hgerm : ∀ r : ℝ,
      D =ᶠ[𝓝 (a + r • w)] {y : Plane | c < ψ y}) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ Ioo (0 : ℝ) ε, ∀ r ∈ Ico (0 : ℝ) q,
        a + x • e + r • w ∈ D := by
  let H : Set Plane := {y : Plane | c < ψ y}
  let A : Set Plane := {p : Plane | D =ᶠ[𝓝 p] H}
  have hAopen : IsOpen A := isOpen_setOfPred_eventually_nhds
  let γ : ℝ → Plane := fun r => a + r • w
  have hγcont : Continuous γ := by fun_prop
  let J : Set Plane := γ '' Icc (0 : ℝ) q
  have hJcompact : IsCompact J :=
    isCompact_Icc.image hγcont
  have hJsub : J ⊆ A := by
    rintro p ⟨r, hr, rfl⟩
    exact hgerm r
  obtain ⟨ρ, hρ, hρsub⟩ := hJcompact.exists_cthickening_subset_open hAopen hJsub
  let ε : ℝ := ρ / (‖e‖ + 1)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε, ?_⟩
  intro x hx r hr
  have hr' : r ∈ Icc (0 : ℝ) q := ⟨hr.1, hr.2.le⟩
  have hpJ : γ r ∈ J := ⟨r, hr', rfl⟩
  let z : Plane := a + x • e + r • w
  have hdist : dist z (γ r) < ρ := by
    rw [dist_eq_norm]
    have hvec : z - γ r = x • e := by
      change (a + x • e + r • w) - (a + r • w) = x • e
      module
    rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_pos hx.1]
    have hxρ : x < ρ / (‖e‖ + 1) := hx.2
    calc
      x * ‖e‖ < (ρ / (‖e‖ + 1)) * ‖e‖ :=
        mul_lt_mul_of_pos_right hxρ (norm_pos_iff.mpr (by
          intro he
          subst e
          simp at hψe))
      _ < ρ := by
        have hden : 0 < ‖e‖ + 1 := by positivity
        rw [div_mul_eq_mul_div]
        exact (div_lt_iff₀ hden).2 (by nlinarith [norm_nonneg e, hρ])
  have hzthick : z ∈ Metric.cthickening ρ J :=
    Metric.mem_cthickening_of_dist_le z (γ r) ρ J hpJ hdist.le
  have hzA : z ∈ A := hρsub hzthick
  have hzH : z ∈ H := by
    change c < ψ (a + x • e + r • w)
    simp only [map_add, map_smul, hψa, hψw, smul_eq_mul]
    nlinarith [mul_pos hx.1 hψe]
  have hEq : ∀ᶠ y in 𝓝 z, (y ∈ D ↔ y ∈ H) := by
    filter_upwards [hzA] with y hy
    exact Iff.of_eq hy
  have hHopen : IsOpen H := by
    dsimp [H]
    exact isOpen_Ioi.preimage ψ.continuous
  have hHnhds : H ∈ 𝓝 z := hHopen.mem_nhds hzH
  have hDnhds : D ∈ 𝓝 z := by
    filter_upwards [hEq, hHnhds] with y hyEq hyH
    exact hyEq.mpr hyH
  exact hopen.mem_nhds_iff.mp hDnhds

/-- Once the actual slice identity and the actual full collar are known, the
generic section supremum is forced by order alone. -/
private theorem generic_slice_supremum_of_mass_bounds
    (C : Set ℝ) (f mass : ℝ → ℝ) (q N : ℝ)
    (hC : C.Finite) (hN : 0 < N)
    (hgeneric : ∀ x ∉ C, mass x = N * f x ∧ mass x ≤ q)
    (hfull : ∃ x, x ∉ C ∧ mass x = q) :
    sSup (f '' Cᶜ) = q / N := by
  obtain ⟨x₀, _, hx₀⟩ :=
    (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finite hC
  have himage : (f '' Cᶜ).Nonempty := ⟨f x₀, ⟨x₀, hx₀, rfl⟩⟩
  have hbdd : BddAbove (f '' Cᶜ) := by
    refine ⟨q / N, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    apply (le_div_iff₀ hN).2
    calc
      f x * N = N * f x := by ring
      _ = mass x := (hgeneric x hx).1.symm
      _ ≤ q := (hgeneric x hx).2
  have hupper : sSup (f '' Cᶜ) ≤ q / N := by
    apply csSup_le himage
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    apply (le_div_iff₀ hN).2
    calc
      f x * N = N * f x := by ring
      _ = mass x := (hgeneric x hx).1.symm
      _ ≤ q := (hgeneric x hx).2
  obtain ⟨x, hxC, hxq⟩ := hfull
  have hmul : N * f x = q := by
    rw [← (hgeneric x hxC).1]
    exact hxq
  have hfx : f x = q / N := by
    apply (eq_div_iff hN.ne').2
    nlinarith [hmul]
  have hlower : q / N ≤ sSup (f '' Cᶜ) := by
    rw [← hfx]
    exact le_csSup hbdd ⟨x, hxC, rfl⟩
  exact le_antisymm hupper hlower

private def scalarCentreSet (S : Set Plane) (s w : Plane) : Set ℝ :=
  {t : ℝ | s + t • w ∈ S}

/-- In a line-supported centre family, the scalar parametrization by a
nonzero generator of the one-dimensional direction is an actual bijection. -/
private noncomputable def scalar_centres_equiv_centres
    {S : Set Plane} {δ : Submodule ℝ Plane} {s w : Plane}
    (hδ : Module.finrank ℝ δ = 1) (hline : IsLineSupported S δ)
    (hs : s ∈ S) (hw : w ∈ δ) (hw0 : w ≠ 0) :
    ↥(scalarCentreSet S s w) ≃ S := by
  have hspan : δ = Submodule.span ℝ ({w} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ hw hw0
  let φ : ↥(scalarCentreSet S s w) → S := fun t =>
    ⟨s + t.1 • w, t.2⟩
  have hinj : Function.Injective φ := by
    intro t u htu
    apply Subtype.ext
    have hplane : s + t.1 • w = s + u.1 • w := congrArg Subtype.val htu
    have hsmul : t.1 • w = u.1 • w := add_left_cancel hplane
    have hzero : (t.1 - u.1) • w = 0 := by
      rw [sub_smul, hsmul, sub_self]
    have hcoeff : t.1 - u.1 = 0 := (smul_eq_zero.mp hzero).resolve_right hw0
    linarith
  have hsurj : Function.Surjective φ := by
    intro u
    obtain ⟨a, ha⟩ := hline
    have hus : (u : Plane) - s ∈ δ := by
      have hu := ha u u.property
      have hs' := ha s hs
      have hsub : (u - a) - (s - a) ∈ δ := δ.sub_mem hu hs'
      simpa using hsub
    rw [hspan] at hus
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hus
    have hrepr : (u : Plane) = s + t • w := by
      have h := congrArg (fun z : Plane => z + s) ht
      simpa [add_comm] using h.symm
    have htL : t ∈ scalarCentreSet S s w := by
      change s + t • w ∈ S
      rw [← hrepr]
      exact u.property
    refine ⟨⟨t, htL⟩, ?_⟩
    exact Subtype.ext hrepr.symm
  exact Equiv.ofBijective φ ⟨hinj, hsurj⟩

/-- A genuinely unique actual owner turns the geometric union section into
the scalar sum of its indicator functions, almost everywhere. -/
private theorem ae_indicator_eq_tsum_of_unique_owner
    {ι : Type*} [Countable ι] (D : Set ℝ) (A : ι → Set ℝ)
    (hcover : ∀ᵐ x ∂volume, x ∈ D ↔ ∃ i, x ∈ A i)
    (hunique : ∀ᵐ x ∂volume, ∀ i j, x ∈ A i → x ∈ A j → i = j) :
    D.indicator (1 : ℝ → ℝ≥0∞) =ᵐ[volume]
      fun x => ∑' i, (A i).indicator (1 : ℝ → ℝ≥0∞) x := by
  filter_upwards [hcover, hunique] with x hxcover hxunique
  by_cases hxD : x ∈ D
  · have hex : ∃ i, x ∈ A i := hxcover.mp hxD
    obtain ⟨i, hi⟩ := hex
    rw [Set.indicator_of_mem hxD, tsum_eq_single i]
    · simp [hi]
    · intro j hji
      have hj : x ∉ A j := by
        intro hj
        exact hji (hxunique i j hi hj).symm
      simp [hj]
  · have hnone : ∀ i, x ∉ A i := by
      intro i hi
      exact hxD (hxcover.mpr ⟨i, hi⟩)
    simp [Set.indicator_of_notMem, hxD, hnone]

/-- Reindex the almost-everywhere unique actual tile owner on a transverse
section by its genuine scalar centre coordinate. -/
private theorem actual_slice_indicator_eq_scalar_sum
    {K : PolygonalRegion} {S D : Set Plane} {δ : Submodule ℝ Plane}
    {s e w : Plane} {x : ℝ}
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hδ : Module.finrank ℝ δ = 1)
    (hline : IsLineSupported S δ) (hs : s ∈ S)
    (hw : w ∈ δ) (hw0 : w ≠ 0)
    (hcover : ∀ᵐ r : ℝ ∂volume,
      s + x • e + r • w ∈ D ↔
        ∃ u : S, s + x • e + r • w ∈ (u : Plane) +ᵥ K.support)
    (hunique : ∀ᵐ r : ℝ ∂volume, ∀ u v : S,
      s + x • e + r • w ∈ (u : Plane) +ᵥ K.support →
      s + x • e + r • w ∈ (v : Plane) +ᵥ K.support → u = v) :
    {r : ℝ | s + x • e + r • w ∈ D}.indicator (1 : ℝ → ℝ≥0∞) =ᵐ[volume]
      fun r => ∑' t : scalarCentreSet S s w,
        (t.1 +ᵥ {z : ℝ | x • e + z • w ∈ K.support}).indicator
          (1 : ℝ → ℝ≥0∞) r := by
  classical
  let L := scalarCentreSet S s w
  let B : Set ℝ := {z : ℝ | x • e + z • w ∈ K.support}
  let φ : ℝ → Plane := fun r => s + x • e + r • w
  let A : S → Set ℝ := fun u => {r | φ r ∈ (u : Plane) +ᵥ K.support}
  have hcover' : ∀ᵐ r ∂volume, r ∈ {z | φ z ∈ D} ↔ ∃ u : S, r ∈ A u := by
    simpa [φ, A] using hcover
  have hunique' : ∀ᵐ r ∂volume, ∀ u v : S, r ∈ A u → r ∈ A v → u = v := by
    simpa [φ, A] using hunique
  letI : Countable S := (Tiling.Polygonal.packing_centres_locallyFinite hp).2.1
  have hsum := ae_indicator_eq_tsum_of_unique_owner {z | φ z ∈ D} A hcover' hunique'
  let E : L ≃ S := scalar_centres_equiv_centres hδ hline hs hw hw0
  have hsection (t : L) :
      {r : ℝ | φ r ∈ (s + t.1 • w) +ᵥ K.support} = t.1 +ᵥ B := by
    ext r
    constructor
    · intro hr
      have hm := (Set.mem_vadd_set_iff_neg_vadd_mem).mp hr
      simp only [vadd_eq_add] at hm
      have hm' : x • e + (r - t.1) • w ∈ K.support := by
        have heq : -(s + t.1 • w) + φ r = x • e + (r - t.1) • w := by
          change -(s + t.1 • w) + (s + x • e + r • w) =
            x • e + (r - t.1) • w
          rw [sub_smul r t.1 w]
          abel
        rw [heq] at hm
        exact hm
      change r ∈ t.1 +ᵥ B
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change x • e + (-t.1 + r) • w ∈ K.support
      simpa [sub_eq_add_neg, add_comm] using hm'
    · intro hr
      obtain ⟨z, hzB, hrz⟩ := Set.mem_vadd_set.mp hr
      change φ r ∈ (s + t.1 • w) +ᵥ K.support
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simp only [vadd_eq_add]
      have hrz' : r = t.1 + z := by simpa [vadd_eq_add] using hrz.symm
      have heq : -(s + t.1 • w) + φ r = x • e + z • w := by
        rw [hrz']
        change -(s + t.1 • w) + (s + x • e + (t.1 + z) • w) =
          x • e + z • w
        rw [add_smul t.1 z w]
        abel
      rw [heq]
      exact hzB
  have hreindex (r : ℝ) :
      (∑' u : S, (A u).indicator (1 : ℝ → ℝ≥0∞) r) =
        ∑' t : L, (t.1 +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) r := by
    rw [← E.tsum_eq]
    apply tsum_congr
    intro t
    have hA : A (E t) = t.1 +ᵥ B := by
      dsimp [A, φ]
      rw [show (E t : Plane) = s + t.1 • w by rfl]
      exact hsection t
    rw [hA]
  have hsum' : {r : ℝ | φ r ∈ D}.indicator (1 : ℝ → ℝ≥0∞) =ᵐ[volume]
      fun r => ∑' t : L, (t.1 +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) r := by
    filter_upwards [hsum] with r hr
    rw [hr, hreindex]
  simpa [φ, L, B] using hsum'

/-- The actual scalar centre set inherits the vector period and has a finite
period cell by packing local finiteness; its multiplicity is positive because
the reference centre itself is in the set. -/
private theorem scalar_centres_have_finite_positive_period_cell
    {K : PolygonalRegion} {S : Set Plane} {s w : Plane} {q : ℝ}
    (hp : IsPacking K.prototileFamily (K.placements S)) (hs : s ∈ S)
    (hw : w ≠ 0) (hq : 0 < q) (hperiod : q • w +ᵥ S = S) :
    q +ᵥ scalarCentreSet S s w = scalarCentreSet S s w ∧
      (scalarCentreSet S s w ∩ Ico (0 : ℝ) q).Finite ∧
      0 < Set.ncard (scalarCentreSet S s w ∩ Ico (0 : ℝ) q) := by
  let L := scalarCentreSet S s w
  have hshift (y : Plane) : y ∈ S ↔ q • w + y ∈ S := by
    constructor
    · intro hy
      have hmem : q • w + y ∈ q • w +ᵥ S :=
        Set.mem_vadd_set.mpr ⟨y, hy, rfl⟩
      rw [← hperiod]
      exact hmem
    · intro hy
      have hmem : q • w + y ∈ q • w +ᵥ S := by
        rw [hperiod]
        exact hy
      obtain ⟨z, hz, hzy⟩ := Set.mem_vadd_set.mp hmem
      have hzy' : z = y := add_left_cancel hzy
      simpa [hzy'] using hz
  have hLperiod : q +ᵥ L = L := by
    ext t
    simp only [Set.mem_vadd_set]
    constructor
    · rintro ⟨u, hu, rfl⟩
      change s + (q + u) • w ∈ S
      have := (hshift (s + u • w)).mp hu
      convert this using 1
      module
    · intro ht
      change s + t • w ∈ S at ht
      refine ⟨t - q, ?_, by simp⟩
      change s + (t - q) • w ∈ S
      have := (hshift (s + (t - q) • w)).mpr ?_
      · exact this
      · convert ht using 1
        module
  have hcell : (L ∩ Ico (0 : ℝ) q).Finite := by
    let φ : ℝ → Plane := fun t => s + t • w
    let Q : Set Plane := φ '' Icc (0 : ℝ) q
    have hQcompact : IsCompact Q :=
      isCompact_Icc.image (by fun_prop : Continuous φ)
    have hfiniteQ : (S ∩ Q).Finite :=
      (Tiling.Polygonal.packing_centres_locallyFinite hp).1 Q hQcompact.isBounded
    have himage : (φ '' (L ∩ Ico (0 : ℝ) q)).Finite := by
      apply hfiniteQ.subset
      rintro y ⟨t, ht, rfl⟩
      exact ⟨ht.1, ⟨t, ⟨ht.2.1, ht.2.2.le⟩, rfl⟩⟩
    have hinj : Set.InjOn φ (L ∩ Ico (0 : ℝ) q) := by
      intro t ht u hu htu
      have hsmul : t • w = u • w := by
        have := congrArg (fun z : Plane => z - s) htu
        simpa [φ] using this
      have hsub : (t - u) • w = 0 := by
        rw [sub_smul, hsmul, sub_self]
      have htu' : t - u = 0 := (smul_eq_zero.mp hsub).resolve_right hw
      linarith
    exact himage.of_finite_image hinj
  have hzero : (0 : ℝ) ∈ L ∩ Ico (0 : ℝ) q := by
    constructor
    · change s + 0 • w ∈ S
      simpa using hs
    · exact ⟨le_rfl, hq⟩
  refine ⟨hLperiod, hcell, ?_⟩
  exact (Set.ncard_pos hcell).mpr ⟨0, hzero⟩

/-- The exact generic slice-mass identity from actual closed-tile ownership,
scalar reindexing, and the period-cell integral theorem. -/
private theorem actual_generic_slice_mass_identity
    {K : PolygonalRegion} {S : Set Plane} {δ : Submodule ℝ Plane}
    {s e w : Plane} {q : ℝ} (C : Set ℝ)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hδ : Module.finrank ℝ δ = 1)
    (hline : IsLineSupported S δ) (hs : s ∈ S)
    (hw : w ∈ δ) (hw0 : w ≠ 0) (hq : 0 < q)
    (hperiod : q • w +ᵥ S = S)
    (howner : ∀ x ∉ C, ∀ᵐ r : ℝ ∂volume,
      (s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S ↔
        ∃ u : S, s + x • e + r • w ∈ (u : Plane) +ᵥ K.support) ∧
      ∀ u v : S,
        s + x • e + r • w ∈ (u : Plane) +ᵥ K.support →
        s + x • e + r • w ∈ (v : Plane) +ᵥ K.support → u = v) :
    ∃ N : ℝ, 0 < N ∧ ∀ x ∉ C,
      (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal =
          N * (volume {r : ℝ | x • e + r • w ∈ K.support}).toReal ∧
        (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
          s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal ≤ q := by
  obtain ⟨hLperiod, hLfinite, hN⟩ :=
    scalar_centres_have_finite_positive_period_cell hp hs hw0 hq hperiod
  let L := scalarCentreSet S s w
  let N : ℝ := (L ∩ Ico (0 : ℝ) q).ncard
  refine ⟨N, ?_, ?_⟩
  · dsimp [N]
    exact_mod_cast hN
  · intro x hxC
    have hown := howner x hxC
    have hcover : ∀ᵐ r : ℝ ∂volume,
        s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S ↔
          ∃ u : S, s + x • e + r • w ∈ (u : Plane) +ᵥ K.support := by
      filter_upwards [hown] with r hr
      exact hr.1
    have hunique : ∀ᵐ r : ℝ ∂volume, ∀ u v : S,
        s + x • e + r • w ∈ (u : Plane) +ᵥ K.support →
        s + x • e + r • w ∈ (v : Plane) +ᵥ K.support → u = v := by
      filter_upwards [hown] with r hr
      exact hr.2
    have hAE := actual_slice_indicator_eq_scalar_sum hp hδ hline hs hw hw0 hcover hunique
    let Dslice : Set ℝ :=
      {r : ℝ | s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S}
    let B : Set ℝ := {r : ℝ | x • e + r • w ∈ K.support}
    have hDmeas : MeasurableSet Dslice := by
      apply ((Tiling.Polygonal.regularSupport_isRegularOpen K S).1.measurableSet).preimage
      fun_prop
    have hBmeas : MeasurableSet B := by
      apply K.isPolygonal.isClosed.measurableSet.preimage
      fun_prop
    have hcellAE : Dslice.indicator (1 : ℝ → ℝ≥0∞) =ᵐ[volume]
        fun r => ∑' t : L, (t.1 +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) r := by
      simpa [Dslice, B, L] using hAE
    have hlin :
        (∫⁻ r in Ico (0 : ℝ) q, Dslice.indicator (1 : ℝ → ℝ≥0∞) r ∂volume) =
          ∫⁻ r in Ico (0 : ℝ) q,
            ∑' t : L, (t.1 +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) r ∂volume :=
      MeasureTheory.setLIntegral_congr_fun_ae measurableSet_Ico
        (hcellAE.mono fun r hr _ => hr)
    have hleft :
      (∫⁻ r in Ico (0 : ℝ) q, Dslice.indicator (1 : ℝ → ℝ≥0∞) r ∂volume) =
          volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧ r ∈ Dslice} := by
      have hset : Dslice ∩ Ico (0 : ℝ) q =
          {r : ℝ | r ∈ Ico (0 : ℝ) q ∧ r ∈ Dslice} := by
        ext r
        simp [Set.mem_Ico, and_assoc, and_comm]
      calc
        _ = ∫⁻ r in Dslice ∩ Ico (0 : ℝ) q, (1 : ℝ → ℝ≥0∞) r ∂volume :=
          MeasureTheory.setLIntegral_indicator hDmeas (1 : ℝ → ℝ≥0∞)
        _ = volume (Dslice ∩ Ico (0 : ℝ) q) := by simp
        _ = volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧ r ∈ Dslice} := congrArg volume hset
    have hsumReal := congrArg ENNReal.toReal hlin
    rw [hleft,
      Tiling.AxisParallel.OneDimensional.FiniteInterval.periodicMultiplicity_cellIntegral
        hBmeas hq hLperiod hLfinite] at hsumReal
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hsumReal
    have hmassEq :
        (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
          s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal =
            N * (volume {r : ℝ | x • e + r • w ∈ K.support}).toReal := by
      simpa [Dslice, B, N, L] using hsumReal
    have hmassLe :
        (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
          s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal ≤ q := by
      calc
        _ ≤ (volume (Ico (0 : ℝ) q)).toReal :=
          ENNReal.toReal_mono (by simp [Real.volume_Ico])
            (measure_mono (by intro r hr; exact hr.1))
        _ = q := by simp [Real.volume_Ico, hq.le]
    exact ⟨hmassEq, hmassLe⟩

private theorem actual_generic_slice_mass_and_supremum_of_full_slice
    {K : PolygonalRegion} {S : Set Plane} {δ : Submodule ℝ Plane}
    {s e w : Plane} {q : ℝ} (C : Set ℝ)
    (hC : C.Finite)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hδ : Module.finrank ℝ δ = 1)
    (hline : IsLineSupported S δ) (hs : s ∈ S)
    (hw : w ∈ δ) (hw0 : w ≠ 0) (hq : 0 < q)
    (hperiod : q • w +ᵥ S = S)
    (howner : ∀ x ∉ C, ∀ᵐ r : ℝ ∂volume,
      (s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S ↔
        ∃ u : S, s + x • e + r • w ∈ (u : Plane) +ᵥ K.support) ∧
      ∀ u v : S,
        s + x • e + r • w ∈ (u : Plane) +ᵥ K.support →
        s + x • e + r • w ∈ (v : Plane) +ᵥ K.support → u = v)
    (hfull : ∃ X, X ∉ C ∧
      (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + X • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal = q) :
    let f : ℝ → ℝ := fun x =>
      (volume {r : ℝ | x • e + r • w ∈ K.support}).toReal
    let mass : ℝ → ℝ := fun x =>
      (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal
    ∃ N : ℝ, 0 < N ∧ sSup (f '' Cᶜ) = q / N ∧
      ∀ x ∉ C, mass x = N * f x ∧ mass x ≤ q := by
  dsimp only
  let f : ℝ → ℝ := fun x =>
    (volume {r : ℝ | x • e + r • w ∈ K.support}).toReal
  let mass : ℝ → ℝ := fun x =>
    (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
      s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal
  obtain ⟨N, hN, hgeneric⟩ := actual_generic_slice_mass_identity C hp hδ
    hline hs hw hw0 hq hperiod howner
  have hsup := generic_slice_supremum_of_mass_bounds C f mass q N hC hN hgeneric hfull
  exact ⟨N, hN, by simpa [f] using hsup, hgeneric⟩

/-- Full BG-A.2 conclusion from the actual generic unique-owner theorem and a
positive occupied half-space germ along the complete frontier line. -/
private theorem actual_generic_slice_mass_and_supremum
    {K : PolygonalRegion} {S : Set Plane} {δ : Submodule ℝ Plane}
    {s e w : Plane} {q x₀ c : ℝ} {ψ : Plane →L[ℝ] ℝ} (C : Set ℝ)
    (hC : C.Finite)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hδ : Module.finrank ℝ δ = 1)
    (hline : IsLineSupported S δ) (hs : s ∈ S)
    (hw : w ∈ δ) (hw0 : w ≠ 0) (hq : 0 < q)
    (hperiod : q • w +ᵥ S = S)
    (hψbase : ψ (s + x₀ • e) = c) (hψw : ψ w = 0) (hψe : 0 < ψ e)
    (hgerm : ∀ r : ℝ,
      Tiling.Polygonal.regularSupport K S =ᶠ[𝓝 (s + x₀ • e + r • w)]
        {y : Plane | c < ψ y})
    (howner : ∀ x ∉ C, ∀ᵐ r : ℝ ∂volume,
      (s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S ↔
        ∃ u : S, s + x • e + r • w ∈ (u : Plane) +ᵥ K.support) ∧
      ∀ u v : S,
        s + x • e + r • w ∈ (u : Plane) +ᵥ K.support →
        s + x • e + r • w ∈ (v : Plane) +ᵥ K.support → u = v) :
    let f : ℝ → ℝ := fun x =>
      (volume {r : ℝ | x • e + r • w ∈ K.support}).toReal
    let mass : ℝ → ℝ := fun x =>
      (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal
    ∃ N : ℝ, 0 < N ∧ sSup (f '' Cᶜ) = q / N ∧
      ∀ x ∉ C, mass x = N * f x ∧ mass x ≤ q := by
  dsimp only
  let f : ℝ → ℝ := fun x =>
    (volume {r : ℝ | x • e + r • w ∈ K.support}).toReal
  let mass : ℝ → ℝ := fun x =>
    (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
      s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal
  have hopen : IsOpen (Tiling.Polygonal.regularSupport K S) :=
    (Tiling.Polygonal.regularSupport_isRegularOpen K S).1
  obtain ⟨ε, hε, hcollar⟩ := complete_line_uniform_positive_collar
    hopen hq hψbase hψw hψe hgerm
  obtain ⟨X, hX, hXC⟩ :=
    (Set.Ioo_infinite (show x₀ < x₀ + ε by linarith)).exists_notMem_finite hC
  have hXoffset : X - x₀ ∈ Ioo (0 : ℝ) ε := by
    have hX' : x₀ < X ∧ X < x₀ + ε := by simpa using hX
    exact ⟨by linarith, by linarith⟩
  have hfill : ∀ r ∈ Ico (0 : ℝ) q,
      s + X • e + r • w ∈ Tiling.Polygonal.regularSupport K S := by
    intro r hr
    have h := hcollar (X - x₀) hXoffset r hr
    convert h using 1
    module
  have hmassFull : mass X = q := by
    have hset : {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + X • e + r • w ∈ Tiling.Polygonal.regularSupport K S} = Ico 0 q := by
      ext r
      constructor
      · exact fun hr => hr.1
      · intro hr
        exact ⟨hr, hfill r hr⟩
    change (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
      s + X • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal = q
    rw [hset]
    simp [Real.volume_Ico, hq.le]
  exact actual_generic_slice_mass_and_supremum_of_full_slice C hC hp hδ
    hline hs hw hw0 hq hperiod howner ⟨X, hXC, hmassFull⟩

/-- The occupied side of a complete frontier line may be either orientation
of the original transverse coordinate.  The negative case uses the reversed
collar to find a full original section just below `x₀`; the section function
and exceptional set remain the original ones. -/
private theorem actual_generic_slice_mass_and_supremum_either_orientation
    {K : PolygonalRegion} {S : Set Plane} {δ : Submodule ℝ Plane}
    {s e w : Plane} {q x₀ : ℝ} {π : Plane →L[ℝ] ℝ} (C : Set ℝ)
    (hC : C.Finite)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hδ : Module.finrank ℝ δ = 1)
    (hline : IsLineSupported S δ) (hs : s ∈ S)
    (hw : w ∈ δ) (hw0 : w ≠ 0) (hq : 0 < q)
    (hperiod : q • w +ᵥ S = S)
    (hπe : π e = 1) (hπw : π w = 0)
    (horient :
      (∀ r : ℝ,
        Tiling.Polygonal.regularSupport K S =ᶠ[𝓝 (s + x₀ • e + r • w)]
          {y : Plane | π (s + x₀ • e) < π y}) ∨
      (∀ r : ℝ,
        Tiling.Polygonal.regularSupport K S =ᶠ[𝓝 (s + x₀ • e + r • w)]
          {y : Plane | π y < π (s + x₀ • e)}))
    (howner : ∀ x ∉ C, ∀ᵐ r : ℝ ∂volume,
      (s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S ↔
        ∃ u : S, s + x • e + r • w ∈ (u : Plane) +ᵥ K.support) ∧
      ∀ u v : S,
        s + x • e + r • w ∈ (u : Plane) +ᵥ K.support →
        s + x • e + r • w ∈ (v : Plane) +ᵥ K.support → u = v) :
    let f : ℝ → ℝ := fun x =>
      (volume {r : ℝ | x • e + r • w ∈ K.support}).toReal
    let mass : ℝ → ℝ := fun x =>
      (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal
    ∃ N : ℝ, 0 < N ∧ sSup (f '' Cᶜ) = q / N ∧
      ∀ x ∉ C, mass x = N * f x ∧ mass x ≤ q := by
  rcases horient with hpositive | hnegative
  · exact actual_generic_slice_mass_and_supremum C hC hp hδ hline hs hw hw0
      hq hperiod (by simp) hπw (by simpa [hπe]) hpositive howner
  · have hnegativeGerm : ∀ r : ℝ,
        Tiling.Polygonal.regularSupport K S =ᶠ[𝓝 (s + x₀ • e + r • w)]
          {y : Plane | -(π (s + x₀ • e)) < (-π) y} := by
      intro r
      have hset : {y : Plane | -(π (s + x₀ • e)) < (-π) y} =
          {y : Plane | π y < π (s + x₀ • e)} := by
        ext y
        simp [neg_lt_neg_iff]
      simpa only [hset] using hnegative r
    have hopen : IsOpen (Tiling.Polygonal.regularSupport K S) :=
      (Tiling.Polygonal.regularSupport_isRegularOpen K S).1
    obtain ⟨ε, hε, hcollar⟩ := complete_line_uniform_positive_collar
      (D := Tiling.Polygonal.regularSupport K S)
      (a := s + x₀ • e) (e := -e) (w := w) (ψ := -π)
      (c := -(π (s + x₀ • e))) (q := q)
      hopen hq (by simp) (by simp [hπw]) (by simpa [hπe]) hnegativeGerm
    obtain ⟨X, hX, hXC⟩ :=
      (Set.Ioo_infinite (show x₀ - ε < x₀ by linarith)).exists_notMem_finite hC
    have hXoffset : x₀ - X ∈ Ioo (0 : ℝ) ε := by
      have hX' : x₀ - ε < X ∧ X < x₀ := by simpa using hX
      constructor <;> linarith
    have hfill : ∀ r ∈ Ico (0 : ℝ) q,
        s + X • e + r • w ∈ Tiling.Polygonal.regularSupport K S := by
      intro r hr
      have h := hcollar (x₀ - X) hXoffset r hr
      convert h using 1
      module
    let mass : ℝ → ℝ := fun x =>
      (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + x • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal
    have hmassFull : mass X = q := by
      have hset : {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
          s + X • e + r • w ∈ Tiling.Polygonal.regularSupport K S} = Ico 0 q := by
        ext r
        constructor
        · exact fun hr => hr.1
        · intro hr
          exact ⟨hr, hfill r hr⟩
      change (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + X • e + r • w ∈ Tiling.Polygonal.regularSupport K S}).toReal = q
      rw [hset]
      simp [Real.volume_Ico, hq.le]
    exact actual_generic_slice_mass_and_supremum_of_full_slice C hC hp hδ
      hline hs hw hw0 hq hperiod howner ⟨X, hXC, by simpa [mass] using hmassFull⟩

/-- Move a real open interval by an integer multiple of a positive period
to a genuine open subinterval of the period cell. -/
private theorem exists_open_interval_translate_into_period_cell
    {α β q : ℝ} (hab : α < β) (hq : 0 < q) :
    ∃ (m : ℤ) (a b : ℝ), a < b ∧ Ioo a b ⊆ Ico 0 q ∧
      ∀ x ∈ Ioo a b, (m : ℝ) * q + x ∈ Ioo α β := by
  let z : ℝ := (α + β) / 2
  let m : ℤ := Int.floor (z / q)
  let r : ℝ := z - (m : ℝ) * q
  have hzα : α < z := by dsimp [z]; linarith
  have hzβ : z < β := by dsimp [z]; linarith
  have hr0 : 0 ≤ r := by
    dsimp [r, m]
    have hfloor := Int.floor_le (z / q)
    have := (le_div_iff₀ hq).mp hfloor
    linarith
  have hrq : r < q := by
    dsimp [r, m]
    have hfloor := Int.lt_floor_add_one (z / q)
    have := (div_lt_iff₀ hq).mp hfloor
    push_cast at this
    linarith
  by_cases hr : r = 0
  · let d : ℝ := min ((β - z) / 2) (q / 2)
    let c : ℝ := z + d
    have hd : 0 < d := by dsimp [d]; positivity
    have hdz : d < q := by
      dsimp [d]
      have : min ((β - z) / 2) (q / 2) ≤ q / 2 := min_le_right _ _
      linarith
    have hcz : c < β := by dsimp [c]; dsimp [d] at *; have := min_le_left ((β-z)/2) (q/2); linarith
    have hcα : α < c := by dsimp [c]; linarith
    have hzfloor : z = (m : ℝ) * q := by
      dsimp [r] at hr
      linarith
    have hcr0 : 0 < c - (m : ℝ) * q := by
      dsimp [c]
      calc
        0 < d := hd
        _ = z + d - (m : ℝ) * q := by rw [hzfloor]; ring
    have hcrq : c - (m : ℝ) * q < q := by
      dsimp [c]
      calc
        z + d - (m : ℝ) * q = d := by rw [hzfloor]; ring
        _ < q := hdz
    let η : ℝ := min (c - α) (min (β - c) (min (c - (m : ℝ) * q) (q - (c - (m : ℝ) * q)))) / 2
    have hη : 0 < η := by dsimp [η]; positivity
    have hηle : η ≤ min (c - α) (min (β - c) (min (c - (m : ℝ) * q) (q - (c - (m : ℝ) * q)))) := by
      dsimp [η]
      have hnon : 0 ≤ min (c - α) (min (β - c) (min (c - (m : ℝ) * q) (q - (c - (m : ℝ) * q)))) := by positivity
      linarith
    have hηmargin : η ≤ c - (m : ℝ) * q := le_trans hηle
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hηqmargin : η ≤ q - (c - (m : ℝ) * q) := le_trans hηle
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    refine ⟨m, c - (m : ℝ) * q - η, c - (m : ℝ) * q + η, by linarith, ?_, ?_⟩
    · intro x hx
      simp only [mem_Ioo] at hx
      constructor <;> linarith [hηmargin, hηqmargin]
    · intro x hx
      simp only [mem_Ioo] at hx
      have hx' : c - (m : ℝ) * q - η < x ∧ x < c - (m : ℝ) * q + η := by simpa using hx
      have hx'' : c - η < (m : ℝ) * q + x ∧ (m : ℝ) * q + x < c + η := by constructor <;> linarith [hzfloor]
      constructor <;> linarith [le_trans hηle (min_le_left _ _), le_trans (le_trans hηle (min_le_right _ _)) (min_le_left _ _)]
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    let η : ℝ := min (z - α) (min (β - z) (min r (q - r))) / 2
    have hη : 0 < η := by dsimp [η]; positivity
    have hηle : η ≤ min (z - α) (min (β - z) (min r (q - r))) := by
      dsimp [η]
      have hnon : 0 ≤ min (z - α) (min (β - z) (min r (q - r))) := by positivity
      linarith
    have hηmargin : η ≤ r := le_trans hηle
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hηqmargin : η ≤ q - r := le_trans hηle
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    refine ⟨m, r - η, r + η, by linarith, ?_, ?_⟩
    · intro x hx
      simp only [mem_Ioo] at hx
      constructor <;> linarith [hηmargin, hηqmargin]
    · intro x hx
      simp only [mem_Ioo] at hx
      have hx' : r - η < x ∧ x < r + η := by simpa using hx
      have hx'' : z - η < (m : ℝ) * q + x ∧ (m : ℝ) * q + x < z + η := by
        constructor <;> dsimp [r] at * <;> linarith
      constructor <;> linarith [le_trans hηle (min_le_left _ _), le_trans (le_trans hηle (min_le_right _ _)) (min_le_left _ _)]

/-- A periodic measurable set with open occupied and vacant intervals has
strictly intermediate measure in its half-open period cell. -/
private theorem periodic_set_period_cell_has_strict_mass
    {A : Set ℝ} {q α β γ κ : ℝ}
    (hAmeas : MeasurableSet A) (hq : 0 < q)
    (hperiod : q +ᵥ A = A)
    (hoccupied : α < β ∧ Ioo α β ⊆ A)
    (hvacant : γ < κ ∧ Ioo γ κ ⊆ Aᶜ) :
    0 < (volume (A ∩ Ico 0 q)).toReal ∧
      (volume (A ∩ Ico 0 q)).toReal < q := by
  have hshift (m : ℤ) : ((m : ℝ) * q +ᵥ A) = A := by
    simpa only [Tiling.AxisParallel.periodGroup_isAddSubgroup, zsmul_eq_mul] using
      (Tiling.AxisParallel.periodGroup A).zsmul_mem hperiod m
  have hshiftc (m : ℤ) : ((m : ℝ) * q +ᵥ Aᶜ) = Aᶜ := by
    have hvaddcompl : (((m : ℝ) * q +ᵥ A)ᶜ) = (m : ℝ) * q +ᵥ Aᶜ := by
      ext y
      simp only [mem_compl_iff, Set.mem_vadd_set_iff_neg_vadd_mem]
    have hcomp := congrArg (fun E : Set ℝ => Eᶜ) (hshift m)
    rw [hvaddcompl] at hcomp
    exact hcomp
  have hshiftMembership (m : ℤ) (z : ℝ) :
      (m : ℝ) * q + z ∈ A ↔ z ∈ A := by
    have hh := congrArg (fun E : Set ℝ => (m : ℝ) * q + z ∈ E) (hshift m)
    have hh' : ((m : ℝ) * q + z ∈ (m : ℝ) * q +ᵥ A) ↔
        ((m : ℝ) * q + z ∈ A) := Iff.of_eq hh
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_cancel_left] using hh'.symm
  have hshiftcMembership (m : ℤ) (z : ℝ) :
      (m : ℝ) * q + z ∈ Aᶜ ↔ z ∈ Aᶜ := by
    have hh := congrArg (fun E : Set ℝ => (m : ℝ) * q + z ∈ E) (hshiftc m)
    have hh' : ((m : ℝ) * q + z ∈ (m : ℝ) * q +ᵥ Aᶜ) ↔
        ((m : ℝ) * q + z ∈ Aᶜ) := Iff.of_eq hh
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_cancel_left] using hh'.symm
  obtain ⟨m₁, a₁, b₁, hab₁, hcell₁, hmove₁⟩ :=
    exists_open_interval_translate_into_period_cell hoccupied.1 hq
  have hoccCell : Ioo a₁ b₁ ⊆ A ∩ Ico 0 q := by
    intro x hx
    have hxA : (m₁ : ℝ) * q + x ∈ A := hoccupied.2 (hmove₁ x hx)
    exact ⟨(hshiftMembership m₁ x).mp hxA, hcell₁ hx⟩
  obtain ⟨m₂, a₂, b₂, hab₂, hcell₂, hmove₂⟩ :=
    exists_open_interval_translate_into_period_cell hvacant.1 hq
  have hvacCell : Ioo a₂ b₂ ⊆ Aᶜ ∩ Ico 0 q := by
    intro x hx
    have hxAc : (m₂ : ℝ) * q + x ∈ Aᶜ := hvacant.2 (hmove₂ x hx)
    exact ⟨(hshiftcMembership m₂ x).mp hxAc, hcell₂ hx⟩
  have hmassPos : 0 < (volume (A ∩ Ico 0 q)).toReal := by
    have hIpos : 0 < (volume (Ioo a₁ b₁)).toReal := by
      rw [Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab₁.le)]
      linarith
    have hle : volume (Ioo a₁ b₁) ≤ volume (A ∩ Ico 0 q) := measure_mono hoccCell
    have hfinite : volume (A ∩ Ico 0 q) ≠ ∞ :=
      ne_top_of_le_ne_top (Metric.isBounded_Ico 0 q).measure_lt_top.ne
        (measure_mono inter_subset_right)
    exact lt_of_lt_of_le hIpos (ENNReal.toReal_mono hfinite hle)
  have hVacPos : 0 < (volume (Ioo a₂ b₂)).toReal := by
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab₂.le)]
    linarith
  have hdisj : Disjoint (A ∩ Ico 0 q) (Ioo a₂ b₂) := by
    rw [Set.disjoint_left]
    intro x hx hv
    exact (hvacCell hv).1 hx.1
  have hunionSub : (A ∩ Ico 0 q) ∪ Ioo a₂ b₂ ⊆ Ico 0 q := by
    intro x hx
    rcases hx with hx | hx
    · exact hx.2
    · exact (hvacCell hx).2
  have hsum := measure_union (μ := volume) hdisj measurableSet_Ioo
  have hle : volume ((A ∩ Ico 0 q) ∪ Ioo a₂ b₂) ≤ volume (Ico 0 q) :=
    measure_mono hunionSub
  have hXfinite : volume (A ∩ Ico 0 q) ≠ ∞ :=
    ne_top_of_le_ne_top (Metric.isBounded_Ico 0 q).measure_lt_top.ne
      (measure_mono inter_subset_right)
  have hVfinite : volume (Ioo a₂ b₂) ≠ ∞ := (Metric.isBounded_Ioo a₂ b₂).measure_lt_top.ne
  have hsumReal : (volume (A ∩ Ico 0 q)).toReal +
      (volume (Ioo a₂ b₂)).toReal ≤ q := by
    calc
      _ = (volume ((A ∩ Ico 0 q) ∪ Ioo a₂ b₂)).toReal := by
        rw [hsum]
        exact (ENNReal.toReal_add hXfinite hVfinite).symm
      _ ≤ (volume (Ico 0 q)).toReal := ENNReal.toReal_mono (Metric.isBounded_Ico 0 q).measure_lt_top.ne hle
      _ = q := by simp [Real.volume_Ico, hq.le]
  exact ⟨hmassPos, by linarith⟩

end GenericSliceMassProofs

private theorem generic_slice_has_unique_placed_support_owner_ae
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (π : Plane →L[ℝ] ℝ) (hker : LinearMap.ker π.toLinearMap = δ)
    (hline : IsLineSupported S δ)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (s : Plane) (hs : s ∈ S) (e w : Plane) (he : π e = 1)
    (hw : w ≠ 0) (hπw : π w = 0)
    (F : Finset (Plane × Plane))
    (hfront : frontier K.support = ⋃ p ∈ (F : Set (Plane × Plane)), segment ℝ p.1 p.2)
    (x : ℝ)
    (hx : x ∉ π '' ((fun p : Plane × Plane => p.1) '' (F : Set (Plane × Plane)) ∪
      (fun p : Plane × Plane => p.2) '' (F : Set (Plane × Plane)))) :
    ∀ᵐ r : ℝ ∂volume,
      (s + x • e + r • w ∈ regularSupport K S ↔
        ∃ t : S, s + x • e + r • w ∈ (t : Plane) +ᵥ K.support) ∧
      ∀ t u : S, s + x • e + r • w ∈ (t : Plane) +ᵥ K.support →
        s + x • e + r • w ∈ (u : Plane) +ᵥ K.support → t = u := by
  apply scalar_carrier_has_unique_placed_support_owner_ae hp
  apply lineSupported_noncritical_tile_frontier_preimages_finite π hker hline s hs
    e w he hw hπw F hfront x
  intro p hp hxp
  apply hx
  exact ⟨p.1, Or.inl ⟨p, hp, rfl⟩, hxp.symm⟩

/-- A boundary line gives a finite-interval full-line tiling and hence a density. Its
maximal tile slice mass fixes the first deficit coordinate independently of the column
centre pattern. The nonempty-corner hypothesis excludes the constant-mass column case. -/
theorem lineProperVertices_transverseAnchor_of_straightLine
    (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) (π : Plane →L[ℝ] ℝ)
    (hπ : Function.Surjective π) (hker : LinearMap.ker π.toLinearMap = δ) :
    ∃ c : ℝ, ∀ S : Set Plane,
      IsPacking K.prototileFamily (K.placements S) → IsLineSupported S δ →
      (properVertices (regularSupport K S)).Nonempty →
      (∃ a : Plane, IsStraightFrontierLine (regularSupport K S) δ a) →
      ∀ s ∈ S, sInf (π '' properVertices (regularSupport K S)) = π s + c := by
  classical
  obtain ⟨F, hF, hfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  let C : Set ℝ := π '' ((fun p : Plane × Plane => p.1) '' (F : Set (Plane × Plane)) ∪
    (fun p : Plane × Plane => p.2) '' (F : Set (Plane × Plane)))
  have hCfinite : C.Finite :=
    ((F.finite_toSet.image _).union (F.finite_toSet.image _)).image π
  have hδbot : δ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hδ
    exact Nat.zero_ne_one hδ
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδbot
  obtain ⟨e, he⟩ := hπ 1
  let f : ℝ → ℝ := fun x =>
    (volume {r : ℝ | x • e + r • w ∈ K.support}).toReal
  let M : ℝ := sSup (f '' Cᶜ)
  let Δ : Set ℝ := {x | x ∉ C ∧ 0 < f x ∧ f x < M}
  let c : ℝ := if Δ.Nonempty then sInf Δ else 0
  refine ⟨c, ?_⟩
  intro S hp hline hW hfull s hs
  -- The actual one-sided polygonal trace gives a positive finite-interval
  -- whole-line tiling; normalize the centers, apply WholeLine, and shift back.
  have tracePeriod : ∃ q : ℝ, 0 < q ∧ (q • w) +ᵥ S = S := by
    obtain ⟨a₀, ha₀⟩ := hfull
    exact bgtrace_original_anchor_trace_period hδ π hπ hker hp hline s hs w hw0 hw
      a₀ ha₀.1 (completeFrontierLine_closedCarrier_vacant_side_germs hδ hp
        π hπ hker a₀ ha₀)
  obtain ⟨q, hq, hqperiod⟩ := tracePeriod
  let mass : ℝ → ℝ := fun x =>
    (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧ s + x • e + r • w ∈ regularSupport K S}).toReal
  -- Generic slices have unique actual closed-tile owners almost everywhere.
  -- A compact cell of literal one-sided germs supplies an actual full collar.
  have genericSliceMass : ∃ N : ℝ, 0 < N ∧ M = q / N ∧
      ∀ x ∉ C, mass x = N * f x ∧ mass x ≤ q := by
    obtain ⟨a₀, ha₀⟩ := hfull
    let x₀ : ℝ := π a₀ - π s
    have hπw : π w = 0 := LinearMap.mem_ker.mp (hker.symm ▸ hw)
    have hbase : π (s + x₀ • e) = π a₀ := by
      simp only [map_add, map_smul, he, smul_eq_mul, mul_one, x₀]
      ring
    have hpoints (r : ℝ) : s + x₀ • e + r • w ∈ a₀ +ᵥ (δ : Set Plane) := by
      have hlevel : π (s + x₀ • e + r • w - a₀) = 0 := by
        simp only [map_sub, map_add, map_smul, hbase, hπw, smul_eq_mul, mul_zero]
        ring
      exact Set.mem_vadd_set.mpr ⟨s + x₀ • e + r • w - a₀,
        hker ▸ LinearMap.mem_ker.mpr hlevel, by simp [vadd_eq_add]⟩
    have horient := completeFrontierLine_halfSpace_germs_constant hδ
      (regularSupport_isRegularOpen K S).1 (regularSupport_isRegularOpen K S).2
      π hπ hker a₀ ha₀
    have hlineGerms :
        (∀ r : ℝ, regularSupport K S =ᶠ[𝓝 (s + x₀ • e + r • w)]
          {y : Plane | π (s + x₀ • e) < π y}) ∨
        (∀ r : ℝ, regularSupport K S =ᶠ[𝓝 (s + x₀ • e + r • w)]
          {y : Plane | π y < π (s + x₀ • e)}) := by
      rcases horient with hpositive | hnegative
      · exact Or.inl (fun r => by simpa only [hbase] using hpositive _ (hpoints r))
      · exact Or.inr (fun r => by simpa only [hbase] using hnegative _ (hpoints r))
    apply actual_generic_slice_mass_and_supremum_either_orientation C hCfinite hp hδ
      hline hs hw hw0 hq hqperiod he hπw hlineGerms
    intro x hx
    exact generic_slice_has_unique_placed_support_owner_ae π hker hline hp s hs e w
      he hw0 hπw F hfront x hx
  obtain ⟨N, hN, hM, hmass⟩ := genericSliceMass
  -- The attained transverse minimum also follows from actual vertex provenance:
  -- all centre projections agree, so the projection of W is a finite set.
  have finiteTransverseVertices : (π '' properVertices (regularSupport K S)).Finite :=
    lineProperVertices_transverse_image_finite π hker hp hline hs
  obtain ⟨v, hv, hvinf⟩ := finiteTransverseVertices.isCompact.sInf_mem (hW.image π)
  let a : ℝ := π v - π s
  -- Below the attained minimum, a downward nonparallel frontier run would
  -- leave the actual bounded support strip. All directional slices are literal
  -- full or empty; this does not use a measure-only cylinder certificate.
  have belowMinimumFullOrEmpty : ∀ x : ℝ, x < a → x ∉ C → mass x = 0 ∨ mass x = q := by
    intro x hxa _hxC
    have hvertices : ∀ y ∈ properVertices (regularSupport K S), π s + a ≤ π y := by
      intro y hy
      have hyinf := csInf_le finiteTransverseVertices.bddBelow (Set.mem_image_of_mem π hy)
      dsimp only [a]
      linarith [hvinf]
    have hπp : π (s + x • e) = π s + x := by
      simp only [map_add, map_smul, he, smul_eq_mul, mul_one]
    have hpoint (r : ℝ) : s + x • e + r • w ∈
        (s + x • e) +ᵥ (δ : Set Plane) :=
      Set.mem_vadd_set.mpr ⟨r • w, δ.smul_mem r hw, rfl⟩
    rcases placed_below_minimum_slice_full_or_empty hδ π hπ hker hp hline s hs
      (π s + a) hvertices (s + x • e) (by rw [hπp]; linarith) with hfull | hempty
    · right
      have hset : {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
          s + x • e + r • w ∈ regularSupport K S} = Ico (0 : ℝ) q := by
        ext r
        exact ⟨fun h => h.1, fun hr => ⟨hr, hfull (hpoint r)⟩⟩
      change (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + x • e + r • w ∈ regularSupport K S}).toReal = q
      rw [hset]
      simp [hq.le]
    · left
      have hset : {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
          s + x • e + r • w ∈ regularSupport K S} = ∅ := by
        ext r
        constructor
        · rintro ⟨_, hr⟩
          exact False.elim (Set.disjoint_left.mp hempty (hpoint r) hr)
        · exact False.elim
      change (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + x • e + r • w ∈ regularSupport K S}).toReal = 0
      rw [hset]
      simp
  -- Actual continuation above the minimum gives both occupied and vacant
  -- open slice arcs. Periodicity moves smaller arcs inside the period cell.
  have minimalCornerPartialSlices : ∃ η : ℝ, 0 < η ∧
      ∀ x ∈ Ioo a (a + η), x ∉ C → 0 < mass x ∧ mass x < q := by
    have hmin : ∀ u ∈ properVertices (regularSupport K S), π v ≤ π u := by
      intro u hu
      have hbound := csInf_le finiteTransverseVertices.bddBelow (Set.mem_image_of_mem π hu)
      linarith [hvinf]
    obtain ⟨η, hη, harcs⟩ := bgcorner_actual_minimum_corner_original_scalar_arcs
      hδ π hπ hker hp hline s hs v hv hmin w hw hw0 e he
    have hDperiod : (q • w) +ᵥ regularSupport K S = regularSupport K S := by
      rw [← regularSupport_vadd K S (q • w), hqperiod]
    refine ⟨η, hη, ?_⟩
    intro x hx _hxC
    obtain ⟨α, β, γ, κ, hαβ, hoccupied, hγκ, hvacant⟩ := harcs x hx
    let A : Set ℝ := {r | s + x • e + r • w ∈ regularSupport K S}
    have hAmeas : MeasurableSet A := by
      apply (regularSupport_isRegularOpen K S).1.measurableSet.preimage
      fun_prop
    have hAperiod : q +ᵥ A = A := by
      ext r
      constructor
      · intro hr
        obtain ⟨r₀, hr₀, rfl⟩ := Set.mem_vadd_set.mp hr
        have hpoint : s + x • e + (q + r₀) • w ∈
            (q • w) +ᵥ regularSupport K S := by
          refine Set.mem_vadd_set.mpr ⟨s + x • e + r₀ • w, hr₀, ?_⟩
          simp only [vadd_eq_add]
          module
        rw [hDperiod] at hpoint
        exact hpoint
      · intro hr
        have hpoint : s + x • e + r • w ∈ (q • w) +ᵥ regularSupport K S := by
          rw [hDperiod]
          exact hr
        have hpre := Set.mem_vadd_set_iff_neg_vadd_mem.mp hpoint
        have hrpre : r - q ∈ A := by
          change s + x • e + (r - q) • w ∈ regularSupport K S
          convert hpre using 1 <;> simp only [vadd_eq_add] <;> module
        exact Set.mem_vadd_set.mpr ⟨r - q, hrpre, by simp [vadd_eq_add]⟩
    have hstrict := periodic_set_period_cell_has_strict_mass hAmeas hq hAperiod
      ⟨hαβ, hoccupied⟩ ⟨hγκ, hvacant⟩
    have hset : {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + x • e + r • w ∈ regularSupport K S} = A ∩ Ico (0 : ℝ) q := by
      ext r
      exact and_comm
    change 0 < (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + x • e + r • w ∈ regularSupport K S}).toReal ∧
      (volume {r : ℝ | r ∈ Ico (0 : ℝ) q ∧
        s + x • e + r • w ∈ regularSupport K S}).toReal < q
    rw [hset]
    exact hstrict
  obtain ⟨η, hη, hpartial⟩ := minimalCornerPartialSlices
  have hΔabove : ∀ x ∈ Δ, a ≤ x := by
    intro x hx
    by_contra hxa
    have hxdef : x ∉ C ∧ 0 < f x ∧ f x < M := hx
    obtain hzero | hfull := belowMinimumFullOrEmpty x (lt_of_not_ge hxa) hxdef.1
    · have hpositive : 0 < mass x := by
        rw [(hmass x hxdef.1).1]
        exact mul_pos hN hxdef.2.1
      linarith
    · have hstrict : mass x < q := by
        rw [(hmass x hxdef.1).1]
        rw [hM] at hxdef
        simpa only [mul_comm] using (lt_div_iff₀ hN).mp hxdef.2.2
      linarith
  have hΔnear : ∀ ε : ℝ, 0 < ε → ∃ x ∈ Δ, x < a + ε := by
    intro ε hε
    obtain ⟨x, hx, hxC⟩ :=
      (Set.Ioo_infinite (show a < a + min η ε by linarith [lt_min hη hε])).exists_notMem_finite hCfinite
    have hxinterval : x ∈ Ioo a (a + η) :=
      ⟨hx.1, hx.2.trans_le (by linarith [min_le_left η ε])⟩
    obtain ⟨hpos, hlt⟩ := hpartial x hxinterval hxC
    have hfxpos : 0 < f x := by
      rw [(hmass x hxC).1] at hpos
      exact (mul_pos_iff_of_pos_left hN).mp hpos
    have hfxlt : f x < M := by
      rw [hM]
      apply (lt_div_iff₀ hN).mpr
      simpa only [mul_comm] using (hmass x hxC).1 ▸ hlt
    exact ⟨x, ⟨hxC, hfxpos, hfxlt⟩, hx.2.trans_le (by linarith [min_le_right η ε])⟩
  have hΔne : Δ.Nonempty := by obtain ⟨x, hx, _⟩ := hΔnear 1 zero_lt_one; exact ⟨x, hx⟩
  have hΔinf : sInf Δ = a := by
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt hΔne hΔabove
    intro b hab
    obtain ⟨x, hx, hxb⟩ := hΔnear (b - a) (sub_pos.mpr hab)
    exact ⟨x, hx, by simpa only [add_sub_cancel] using hxb⟩
  dsimp only [c]
  rw [if_pos hΔne, hΔinf]
  dsimp only [a]
  linarith [hvinf]

private theorem translated_finite_projection_sInf
    {WS WU : Set Plane} (π : Plane →L[ℝ] ℝ) (z : Plane)
    (hWS : WS.Nonempty) (hfinite : (π '' WS).Finite)
    (hW : z +ᵥ WS = WU) :
    WU.Nonempty ∧ (π '' WU).Finite ∧
      sInf (π '' WU) = π z + sInf (π '' WS) := by
  classical
  have hWne : WU.Nonempty := by
    obtain ⟨w, hw⟩ := hWS
    have hw' : z + w ∈ z +ᵥ WS :=
      Set.mem_vadd_set.mpr ⟨w, hw, rfl⟩
    refine ⟨z + w, ?_⟩
    rw [← hW]
    exact hw'
  have himage : π '' WU = (fun r : ℝ => π z + r) '' (π '' WS) := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : v ∈ z +ᵥ WS := hW.symm ▸ hv
      obtain ⟨w, hw, hvw⟩ := Set.mem_vadd_set.mp hv'
      refine ⟨π w, Set.mem_image_of_mem π hw, ?_⟩
      rw [← hvw]
      change π z + π w = π (z + w)
      rw [map_add]
    · rintro ⟨r, ⟨w, hw, rfl⟩, rfl⟩
      have hw' : z + w ∈ WU := by
        rw [← hW]
        exact Set.mem_vadd_set.mpr ⟨w, hw, rfl⟩
      exact ⟨z + w, hw', by simp [map_add, add_comm]⟩
  have hfinite' : (π '' WU).Finite := by
    rw [himage]
    exact hfinite.image (fun r : ℝ => π z + r)
  have hAne : (π '' WS).Nonempty := hWS.image π
  obtain ⟨a, ha, hmin⟩ := Set.exists_min_image (π '' WS) id hfinite hAne
  have hAinf : sInf (π '' WS) = a := by
    apply le_antisymm
    · exact csInf_le hfinite.bddBelow ha
    · apply le_csInf hAne
      intro b hb
      exact hmin b hb
  have hBne : (π '' WU).Nonempty := hWne.image π
  have hmem : π z + a ∈ π '' WU := by
    rw [himage]
    exact ⟨a, ha, rfl⟩
  have hleast : ∀ b ∈ π '' WU, π z + a ≤ b := by
    rw [himage]
    rintro b ⟨c, hc, rfl⟩
    calc
      π z + a = a + π z := by ring
      _ ≤ c + π z := add_le_add_left (hmin c hc) (π z)
      _ = π z + c := by ring
  have hBinf : sInf (π '' WU) = π z + a := by
    apply le_antisymm
    · exact csInf_le hfinite'.bddBelow hmem
    · exact le_csInf hBne hleast
  exact ⟨hWne, hfinite', by rw [hBinf, hAinf]⟩

private theorem lineSupported_vadd_local
    {δ : Submodule ℝ Plane} {S : Set Plane} (hl : IsLineSupported S δ) (z : Plane) :
    IsLineSupported (z +ᵥ S) δ := by
  obtain ⟨a, ha⟩ := hl
  refine ⟨z + a, ?_⟩
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Set.mem_vadd_set.mp hs
  simpa only [vadd_eq_add, add_sub_add_left_eq_sub] using ha t ht

private theorem centre_coordinates_align_from_matching_vertices
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S U : Set Plane}
    (hδ : Module.finrank ℝ δ = 1) (π : Plane →L[ℝ] ℝ)
    (hπ : Function.Surjective π) (hker : LinearMap.ker π.toLinearMap = δ)
    (hpS : IsPacking K.prototileFamily (K.placements S))
    (hpU : IsPacking K.prototileFamily (K.placements U))
    (hlS : IsLineSupported S δ) (hlU : IsLineSupported U δ)
    (hWne : (properVertices (regularSupport K S)).Nonempty)
    (z : Plane) (hW : z +ᵥ properVertices (regularSupport K S) =
      properVertices (regularSupport K U))
    (s : Plane) (hs : s ∈ S) (u : Plane) (hu : u ∈ U) :
    π u = π (s + z) := by
  classical
  by_cases hfullS : ∃ a : Plane, IsStraightFrontierLine (regularSupport K S) δ a
  · by_cases hfullU : ∃ a : Plane, IsStraightFrontierLine (regularSupport K U) δ a
    · obtain ⟨hWU, _hfiniteU, hshift⟩ := translated_finite_projection_sInf π z hWne
        (lineProperVertices_transverse_image_finite π hker hpS hlS hs) hW
      obtain ⟨c, hanchor⟩ := lineProperVertices_transverseAnchor_of_straightLine
        K δ hδ π hπ hker
      have hSinf := hanchor S hpS hlS hWne hfullS s hs
      have hUinf := hanchor U hpU hlU hWU hfullU u hu
      rw [map_add]
      linarith
    · exact centre_coordinates_align_if_one_has_no_straight_line
        hδ π hπ hker hpS hpU hlS hlU z hW s hs u hu (Or.inr hfullU)
  · exact centre_coordinates_align_if_one_has_no_straight_line
      hδ π hπ hker hpS hpU hlS hlU z hW s hs u hu (Or.inl hfullS)

private theorem lineSupported_full_frontier_lines_match
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S U : Set Plane}
    (hδ : Module.finrank ℝ δ = 1) (hS : S.Nonempty) (hU : U.Nonempty)
    (hpS : IsPacking K.prototileFamily (K.placements S))
    (hpU : IsPacking K.prototileFamily (K.placements U))
    (hlS : IsLineSupported S δ) (hlU : IsLineSupported U δ)
    (hWne : (properVertices (regularSupport K S)).Nonempty)
    (z : Plane) (hW : z +ᵥ properVertices (regularSupport K S) =
      properVertices (regularSupport K U))
    (ε : Submodule ℝ Plane) (hε : Module.finrank ℝ ε = 1)
    (a : Plane) (ha : IsStraightFrontierLine (regularSupport K S) ε a) :
    IsStraightFrontierLine (regularSupport K U) ε (a + z) ∧
      ∀ x ∈ a +ᵥ (ε : Set Plane),
        SameGermAt (regularSupport K S) x (regularSupport K U) (x + z) := by
  have hdir := complete_frontier_line_parallel_to_centres hδ hε hpS hlS ha.1
  subst ε
  let L : AffineSubspace ℝ Plane := AffineSubspace.mk' (0 : Plane) δ
  have hL : Module.finrank ℝ L.direction = 1 := by
    dsimp only [L]
    rw [AffineSubspace.direction_mk']
    exact hδ
  obtain ⟨π, hπ, hkerL, _hlevelL⟩ := affineLine_surjective_level_coordinate
    (AffineSubspace.self_mem_mk' (0 : Plane) δ) hL
  have hker : LinearMap.ker π.toLinearMap = δ := by
    simpa only [L, AffineSubspace.direction_mk'] using hkerL
  obtain ⟨s, hs⟩ := hS
  let V : Set Plane := z +ᵥ S
  have hpV : IsPacking K.prototileFamily (K.placements V) := isPacking_centres_vadd_local hpS z
  have hlV : IsLineSupported V δ := lineSupported_vadd_local hlS z
  have hfullV : IsStraightFrontierLine (regularSupport K V) δ (a + z) := by
    dsimp only [V]
    rw [regularSupport_vadd]
    exact straightFrontierLine_vadd z ha
  have hW0 : properVertices (regularSupport K V) = properVertices (regularSupport K U) := by
    dsimp only [V]
    rw [regularSupport_vadd, properVertices_vadd, hW]
  have hnoU : Disjoint ((a + z) +ᵥ (δ : Set Plane)) (properVertices (regularSupport K U)) := by
    rw [← hW0]
    exact hfullV.2
  have hsV : z + s ∈ V := Set.mem_vadd_set.mpr ⟨s, hs, rfl⟩
  have hcentres : ∀ u ∈ U, π u = π (z + s) := by
    intro u hu
    simpa only [add_comm] using centre_coordinates_align_from_matching_vertices
      hδ π hπ hker hpS hpU hlS hlU hWne z hW s hs u hu
  obtain ⟨hfullU, hmatch⟩ := aligned_centres_full_frontier_line_germs_match
    hδ hpV hpU hlV hU π hπ hker (a + z) (z + s) hsV hcentres hfullV hnoU
  refine ⟨hfullU, ?_⟩
  intro x hx
  have hxU : x + z ∈ (a + z) +ᵥ (δ : Set Plane) := by
    obtain ⟨v, hv, hxeq⟩ := Set.mem_vadd_set.mp hx
    refine Set.mem_vadd_set.mpr ⟨v, hv, ?_⟩
    rw [← hxeq]
    simp only [vadd_eq_add]
    abel
  have hshift : z +ᵥ regularSupport K S =ᶠ[𝓝 (x + z)] regularSupport K U := by
    rw [← regularSupport_vadd]
    exact hmatch (x + z) hxU
  have hcont : Continuous (fun y : Plane => y + z) := continuous_id.add continuous_const
  change regularSupport K S =ᶠ[𝓝 x] ((x - (x + z)) +ᵥ regularSupport K U)
  filter_upwards [hcont.continuousAt.eventually hshift] with y hy
  apply propext
  have hyiff := Iff.of_eq hy
  change y + z ∈ z +ᵥ regularSupport K S ↔ y + z ∈ regularSupport K U at hyiff
  rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hyiff
  have hcancel : -z +ᵥ (y + z) = y := by simp only [vadd_eq_add]; abel
  rw [hcancel] at hyiff
  change y ∈ regularSupport K S ↔ y ∈ (x - (x + z)) +ᵥ regularSupport K U
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  rw [show x - (x + z) = -z by abel]
  simpa only [neg_neg, vadd_eq_add, add_comm] using hyiff

theorem lineProperVertices_determine_translate
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S U : Set Plane}
    (hδ : Module.finrank ℝ δ = 1) (hS : S.Nonempty) (hU : U.Nonempty)
    (hpS : IsPacking K.prototileFamily (K.placements S))
    (hpU : IsPacking K.prototileFamily (K.placements U))
    (hlS : IsLineSupported S δ) (hlU : IsLineSupported U δ)
    (hWne : (properVertices (regularSupport K S)).Nonempty) (z : Plane)
    (hW : z +ᵥ properVertices (regularSupport K S) =
      properVertices (regularSupport K U))
    (hg : ∀ v ∈ properVertices (regularSupport K S),
      SameGermAt (regularSupport K S) v (regularSupport K U) (v + z)) :
    z +ᵥ regularSupport K S = regularSupport K U := by
  -- OPEN BG4: compare transverse anchors (the no-line span / full-line anchor
  -- branches), then match full lines with their actual occupied-side germs.
  have forwardLines : ∀ ε : Submodule ℝ Plane, Module.finrank ℝ ε = 1 →
      ∀ a : Plane, IsStraightFrontierLine (regularSupport K S) ε a →
        IsStraightFrontierLine (regularSupport K U) ε (a + z) ∧
          ∀ x ∈ a +ᵥ (ε : Set Plane),
            SameGermAt (regularSupport K S) x (regularSupport K U) (x + z) := by
    exact lineSupported_full_frontier_lines_match hδ hS hU hpS hpU hlS hlU hWne z hW
  have backwardLines : ∀ ε : Submodule ℝ Plane, Module.finrank ℝ ε = 1 →
      ∀ a : Plane, IsStraightFrontierLine (regularSupport K U) ε a →
        IsStraightFrontierLine (regularSupport K S) ε (a - z) ∧
          ∀ x ∈ a +ᵥ (ε : Set Plane),
            SameGermAt (regularSupport K U) x (regularSupport K S) (x - z) := by
    have hWneU : (properVertices (regularSupport K U)).Nonempty := by
      obtain ⟨v, hv⟩ := hWne
      refine ⟨z + v, ?_⟩
      rw [← hW]
      exact Set.mem_vadd_set.mpr ⟨v, hv, rfl⟩
    have hWback : (-z) +ᵥ properVertices (regularSupport K U) =
        properVertices (regularSupport K S) := by
      rw [← hW]
      simp only [vadd_vadd, neg_add_cancel, zero_vadd]
    intro ε hε a ha
    simpa only [sub_eq_add_neg] using lineSupported_full_frontier_lines_match
      hδ hU hS hpU hpS hlU hlS hWneU (-z) hWback ε hε a ha
  exact properVertices_and_straightLines_determine_translate hS hU hpS hpU z hW hg
    forwardLines backwardLines

/-- Nonperiodic Part-II intermediate: a proper nonempty corner-free packing carrier
is direction-invariant; no periodicity or original line support is silently assumed. -/
theorem cornerFree_carrier_invariant
    {K : PolygonalRegion} {S : Set Plane} (hS : S.Nonempty)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hproper : regularSupport K S ≠ univ)
    (hW : properVertices (regularSupport K S) = ∅) :
    ∃ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 ∧
      HasBoundaryDirection K δ ∧ IsInvariantAlong (regularSupport K S) δ := by
  have hDopen := (regularSupport_isRegularOpen K S).1
  have hDne : (regularSupport K S).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hopen : IsOpen (openUnion K S) :=
      isOpen_iUnion (fun t : S => isOpen_interior.vadd (t : Plane))
    have hunion : openUnion K S ⊆ regularSupport K S :=
      hopen.subset_interior_iff.mpr subset_closure
    refine ⟨s + k, hunion (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩)⟩
    exact Set.mem_vadd_set.mpr ⟨k, hk, rfl⟩
  have hfrontne : (frontier (regularSupport K S)).Nonempty :=
    nonempty_frontier_iff.mpr ⟨hDne, hproper⟩
  have hlocal : ∀ x ∈ frontier (regularSupport K S),
      BoundaryLocallyStraightAt (regularSupport K S) x := by
    intro x hx
    by_contra hnot
    have hxW : x ∈ properVertices (regularSupport K S) := ⟨hx, hnot⟩
    simp only [hW, Set.mem_empty_iff_false] at hxW
  -- OPEN BG5 geometry: continue each locally straight frontier germ to a
  -- complete line; nonparallel complete components would intersect properly.
  have completeParallelFrontier : ∃ δ : Submodule ℝ Plane,
      Module.finrank ℝ δ = 1 ∧ ∀ a : Plane,
        a +ᵥ (δ : Set Plane) ⊆ frontier (regularSupport K S) ∨
          Disjoint (a +ᵥ (δ : Set Plane)) (frontier (regularSupport K S)) := by
    obtain ⟨a, ha⟩ := hfrontne
    obtain ⟨L, haL, hL, hgL⟩ := hlocal a ha
    have hLfull := straight_frontier_affine_germ_propagates haL hL
      (by simp only [hW, disjoint_empty]) hgL
    have hLrepr := affineSubspace_eq_anchor_vadd_direction haL
    refine ⟨L.direction, hL, ?_⟩
    intro b
    by_cases hdisj : Disjoint (b +ᵥ (L.direction : Set Plane))
        (frontier (regularSupport K S))
    · exact Or.inr hdisj
    · left
      obtain ⟨x, hxline, hxfront⟩ := Set.not_disjoint_iff.mp hdisj
      obtain ⟨M, hxM, hM, hgM⟩ := hlocal x hxfront
      have hMfull := straight_frontier_affine_germ_propagates hxM hM
        (by simp only [hW, disjoint_empty]) hgM
      have hMrepr := affineSubspace_eq_anchor_vadd_direction hxM
      have hdir : L.direction = M.direction := complete_frontier_lines_parallel (a := a) (b := x)
        hlocal hL hM (by simpa only [← hLrepr] using hLfull)
        (by simpa only [← hMrepr] using hMfull)
      intro y hy
      apply hMfull
      rw [hMrepr, ← hdir, Set.mem_vadd_set_iff_neg_vadd_mem]
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxline hy
      change -x + y ∈ L.direction
      have hdiff := L.direction.sub_mem hy hxline
      convert hdiff using 1 <;> simp only [vadd_eq_add] <;> abel
  obtain ⟨δ, hδ, hlines⟩ := completeParallelFrontier
  obtain ⟨a, ha⟩ := hfrontne
  have haLine : a +ᵥ (δ : Set Plane) ⊆ frontier (regularSupport K S) := by
    rcases hlines a with h | h
    · exact h
    · exact False.elim (Set.disjoint_left.mp h
        (Set.mem_vadd_set.mpr ⟨0, δ.zero_mem, add_zero a⟩) ha)
  have hstraight : IsStraightFrontierLine (regularSupport K S) δ a :=
    ⟨haLine, by simp only [hW, disjoint_empty]⟩
  refine ⟨δ, hδ, straightFrontierLine_isBoundaryDirection hδ hp hstraight, ?_⟩
  intro u hu
  ext y
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  have hy : y ∈ y +ᵥ (δ : Set Plane) :=
    Set.mem_vadd_set.mpr ⟨0, δ.zero_mem, add_zero y⟩
  have hyu : -u +ᵥ y ∈ y +ᵥ (δ : Set Plane) := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have heq : -y +ᵥ (-u +ᵥ y) = -u := by simp only [vadd_eq_add]; abel
    rw [heq]
    exact δ.neg_mem hu
  rcases hlines y with hfront | hdisj
  · constructor
    · intro hmem
      exact False.elim ((hfront hyu).2 (hDopen.interior_eq.symm ▸ hmem))
    · intro hmem
      exact False.elim ((hfront hy).2 (hDopen.interior_eq.symm ▸ hmem))
  · have hconnected : IsPreconnected (y +ᵥ (δ : Set Plane)) := (δ.convex.vadd y).isPreconnected
    rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      hconnected hdisj with
      hinside | houtside
    · exact iff_of_true (interior_subset (hinside hyu)) (interior_subset (hinside hy))
    · exact iff_of_false (interior_subset (houtside hyu)) (interior_subset (houtside hy))

/-- Part-II consumer: proper nonempty corner-free periodic carriers have a unique
stripe direction and a cyclic transverse period group. Empty/full sets are excluded. -/
theorem cornerFree_periodicCarrier_stripeStabilizer
    {K : PolygonalRegion} {S E : Set Plane} (htile : TilesOn K S E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (hEne : E.Nonempty) (hEproper : E ≠ univ) (hEper : IsLatticePeriodic E)
    (hW : properVertices E = ∅) :
    ∃ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 ∧
      HasBoundaryDirection K δ ∧ ∃ β : Plane, β ∉ δ ∧
        (periodGroup E : Set Plane) = {u | ∃ n : ℤ, u - n • β ∈ δ} := by
  classical
  have hcarrier : regularSupport K S = E :=
    regularSupport_eq_of_tilesOn hEopen hEregular htile
  have hS : S.Nonempty := by
    by_contra h
    have hSE : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hEempty : E = ∅ := by simpa [hSE, regularSupport, openUnion] using hcarrier.symm
    exact hEne.ne_empty hEempty
  obtain ⟨δ, hδ, hboundary, hinv⟩ := cornerFree_carrier_invariant hS htile.2.1
    (by simpa only [hcarrier] using hEproper) (by simpa only [hcarrier] using hW)
  have hδperiod : ∀ u ∈ δ, u ∈ periodGroup E := by
    intro u hu
    exact AddAction.mem_stabilizer_iff.mpr (by simpa only [hcarrier] using hinv u hu)
  have hδbot : δ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hδ
    exact Nat.zero_ne_one hδ
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδbot
  have hδspan := eq_span_singleton_of_mem_of_finrank_eq_one hδ hw hw0
  let e : Plane := w * Complex.I
  have he : e ∉ δ := by
    rw [hδspan]
    rw [Submodule.mem_span_singleton]
    rintro ⟨r, hr⟩
    have heq : (r : ℂ) = Complex.I := mul_right_cancel₀ hw0 (by
      simpa only [Complex.real_smul, e, mul_comm] using hr)
    have := congrArg Complex.im heq
    norm_num at this
  have hdecomp : ∀ u : Plane,
      u = (u / w).re • w + (u / w).im • e := by
    intro u
    symm
    calc
      (u / w).re • w + (u / w).im • e =
          ((u / w).re + (u / w).im * Complex.I) * w := by
            simp only [Complex.real_smul, e]
            ring
      _ = u := by rw [Complex.re_add_im, div_mul_cancel₀ _ hw0]
  let sectionMap : ℝ →+ Plane :=
    { toFun := fun r => r • e
      map_zero' := zero_smul ℝ e
      map_add' := fun r s => add_smul r s e }
  let H : AddSubgroup ℝ := (periodGroup E).comap sectionMap
  have hHclosed : IsClosed (H : Set ℝ) :=
    (isClosed_periodGroup_of_regularOpen hEopen hEregular).preimage
      (continuous_id.smul continuous_const)
  have hHnotdense : ¬Dense (H : Set ℝ) := by
    intro hdense
    have hHfull : (H : Set ℝ) = univ := by
      rw [← hHclosed.closure_eq, hdense.closure_eq]
    have hAll : ∀ u : Plane, u ∈ periodGroup E := by
      intro u
      rw [hdecomp u]
      apply (periodGroup E).add_mem
      · exact hδperiod _ (δ.smul_mem _ hw)
      · have hmem : (u / w).im ∈ H := by
          change (u / w).im ∈ (H : Set ℝ)
          rw [hHfull]
          trivial
        exact hmem
    apply hEproper
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, hx⟩ := hEne
    have hperiod := AddAction.mem_stabilizer_iff.mp (hAll (y - x))
    rw [← hperiod]
    exact Set.mem_vadd_set.mpr ⟨x, hx, sub_add_cancel y x⟩
  obtain ⟨a, hHcyclic⟩ := H.dense_or_cyclic.resolve_left hHnotdense
  have hHcyc : H = AddSubgroup.zmultiples a := by
    simpa only [AddSubgroup.zmultiples_eq_closure] using hHcyclic
  have htransversePeriod : ∃ u ∈ periodGroup E, u ∉ δ := by
    obtain ⟨L, hL⟩ := hEper
    have hsp : Submodule.span ℝ (Set.range L.basis) = ⊤ :=
      L.independent.span_eq_top_of_card_eq_finrank (by
        simp only [Fintype.card_fin, Complex.finrank_real_complex])
    by_contra h
    have hLδ : ∀ j, L.basis j ∈ δ := by
      intro j
      by_contra hj
      exact h ⟨L.basis j, hL (AddSubgroup.subset_closure ⟨j, rfl⟩), hj⟩
    have htop : (⊤ : Submodule ℝ Plane) ≤ δ := by
      rw [← hsp]
      exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hLδ j)
    have hδtop := top_unique htop
    have hdim : Module.finrank ℝ δ = 2 := by
      rw [hδtop, finrank_top, Complex.finrank_real_complex]
    omega
  have ha : a ≠ 0 := by
    intro ha0
    obtain ⟨u, hu, huδ⟩ := htransversePeriod
    have hlong : (u / w).re • w ∈ periodGroup E := hδperiod _ (δ.smul_mem _ hw)
    have hshort : (u / w).im ∈ H := by
      change (u / w).im • e ∈ periodGroup E
      have hsub := (periodGroup E).sub_mem hu hlong
      have heq : u - (u / w).re • w = (u / w).im • e := by
        nth_rw 1 [hdecomp u]
        abel
      rwa [heq] at hsub
    rw [hHcyc, ha0] at hshort
    have hzero : (u / w).im = 0 := by simpa using hshort
    apply huδ
    rw [hdecomp u, hzero, zero_smul, add_zero]
    exact δ.smul_mem _ hw
  have hβ : a • e ∉ δ := by
    intro hmem
    apply he
    have := δ.smul_mem a⁻¹ hmem
    simpa only [inv_smul_smul₀ ha] using this
  have hβperiod : a • e ∈ periodGroup E := by
    change a ∈ H
    rw [hHcyc]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩
  refine ⟨δ, hδ, hboundary, a • e, hβ, ?_⟩
  ext u
  change u ∈ periodGroup E ↔ ∃ n : ℤ, u - n • (a • e) ∈ δ
  constructor
  · intro hu
    have hlong : (u / w).re • w ∈ periodGroup E := hδperiod _ (δ.smul_mem _ hw)
    have hshort : (u / w).im ∈ H := by
      change (u / w).im • e ∈ periodGroup E
      have hsub := (periodGroup E).sub_mem hu hlong
      have heq : u - (u / w).re • w = (u / w).im • e := by
        nth_rw 1 [hdecomp u]
        abel
      rwa [heq] at hsub
    rw [hHcyc, AddSubgroup.mem_zmultiples_iff] at hshort
    obtain ⟨n, hn⟩ := hshort
    refine ⟨n, ?_⟩
    rw [← smul_assoc, hn]
    nth_rw 1 [hdecomp u]
    simpa only [add_sub_cancel_right] using δ.smul_mem (u / w).re hw
  · rintro ⟨n, hn⟩
    have hsum := (periodGroup E).add_mem (hδperiod _ hn)
      ((periodGroup E).zsmul_mem hβperiod n)
    simpa only [sub_add_cancel] using hsum

end Tiling.Polygonal

namespace Tiling.RationalSlopes

open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Polygonal

def ProperEdgeContactAlong (K : PolygonalRegion) (η : Submodule ℝ Plane)
    (s t : Plane) : Prop :=
  ∃ a b : Plane, a ≠ b ∧ b - a ∈ η ∧
    openSegment ℝ a b ⊆
      frontier (s +ᵥ K.support) ∩ frontier (t +ᵥ K.support)

private theorem one_member_contains_openInterval
    {ι : Type*} {f : ι → Set ℝ} {a b : ℝ} (hab : a < b)
    (hopen : ∀ i, IsOpen (f i))
    (hpair : Set.Pairwise Set.univ (Disjoint on f))
    (hcover : Set.Ioo a b ⊆ ⋃ i, f i) :
    ∃ i, Set.Ioo a b ⊆ f i := by
  let m := (a + b) / 2
  have hm : m ∈ Set.Ioo a b := by dsimp [m]; constructor <;> linarith
  obtain ⟨i, hmi⟩ := Set.mem_iUnion.mp (hcover hm)
  let V : Set ℝ := ⋃ j : {j : ι // j ≠ i}, f j.1
  have hVopen : IsOpen V := isOpen_iUnion fun j => hopen j.1
  have hiV : Disjoint (f i) V := by
    rw [Set.disjoint_left]
    intro z hzi hzV
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzV
    exact Set.disjoint_left.mp
      (hpair (Set.mem_univ i) (Set.mem_univ j.1) j.2.symm) hzi hzj
  have hcover' : Set.Ioo a b ⊆ f i ∪ V := by
    intro z hz
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp (hcover hz)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hzj)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hzj⟩)
  rcases isPreconnected_Ioo.subset_or_subset (hopen i) hVopen hiV hcover' with hi | hV
  · exact ⟨i, hi⟩
  · exact False.elim (Set.disjoint_left.mp hiV hmi (hV hm))

private theorem endpoint_openOwner
    {K : PolygonalRegion} {T : Set Plane} {v e : Plane} {R : ℝ}
    (hpack : IsPacking K.prototileFamily (K.placements T)) (hR : 0 < R)
    (hcover : ∀ q ∈ Set.Ioo (0 : ℝ) R,
      ∃ t : T, v + q • e ∈ (t : Plane) +ᵥ K.openCarrier) :
    ∃ u : T, ∀ q ∈ Set.Ioo (0 : ℝ) R,
      v + q • e ∈ (u : Plane) +ᵥ K.openCarrier := by
  let f : T → Set ℝ := fun t => {q | v + q • e ∈ (t : Plane) +ᵥ K.openCarrier}
  have hline : Continuous (fun q : ℝ => v + q • e) := by fun_prop
  have hopen : ∀ t : T, IsOpen (f t) := by
    intro t
    exact (isOpen_interior.vadd (t : Plane)).preimage hline
  have hpair : Set.Pairwise Set.univ (Disjoint on f) := by
    intro s _ t _ hst
    change Disjoint (f s) (f t)
    have hcarrier := (isPacking_iff_openCarrier_disjoint K T).mp hpack
    have hne : (s : Plane) ≠ (t : Plane) := fun h => hst (Subtype.ext h)
    have hdisj := hcarrier s.2 t.2 hne
    rw [Set.disjoint_left]
    intro q hqs hqt
    apply Set.disjoint_left.mp hdisj
    · simpa [f] using hqs
    · simpa [f] using hqt
  have hfcover : Set.Ioo (0 : ℝ) R ⊆ ⋃ t : T, f t := by
    intro q hq
    obtain ⟨t, hqt⟩ := hcover q hq
    exact Set.mem_iUnion.mpr ⟨t, hqt⟩
  obtain ⟨u, hu⟩ := one_member_contains_openInterval hR hopen hpair hfcover
  exact ⟨u, fun q hq => hu hq⟩

private theorem endpoint_tileFrontier_disjoint_open
    {K : PolygonalRegion} {T : Set Plane}
    (hpack : IsPacking K.prototileFamily (K.placements T)) (s t : T) :
    Disjoint (frontier ((s : Plane) +ᵥ K.support))
      ((t : Plane) +ᵥ K.openCarrier) := by
  by_cases hst : s = t
  · subst t
    rw [Set.disjoint_left]
    intro x hxfront hxopen
    have hxparts : x ∈ closure ((s : Plane) +ᵥ K.support) ∧
        x ∉ interior ((s : Plane) +ᵥ K.support) := by
      simpa only [frontier, Set.mem_sdiff] using hxfront
    have hxopen' : x ∈ interior ((s : Plane) +ᵥ K.support) := by
      change x ∈ (s : Plane) +ᵥ interior K.support at hxopen
      simpa [interior_vadd] using hxopen
    exact hxparts.2 hxopen'
  · have hdisj : Disjoint ((s : Plane) +ᵥ K.openCarrier)
        ((t : Plane) +ᵥ K.openCarrier) := by
      have hpair := (isPacking_iff_openCarrier_disjoint K T).mp hpack
      apply hpair s.2 t.2
      intro h
      exact hst (Subtype.ext h)
    have hregular : closure ((s : Plane) +ᵥ K.openCarrier) =
        (s : Plane) +ᵥ K.support := by
      change closure ((s : Plane) +ᵥ interior K.support) = _
      rw [closure_vadd]
      congr 1
      exact K.isPolygonal.closure_interior
    rw [Set.disjoint_left]
    intro x hxfront hxopen
    have hxclosed : x ∈ closure ((s : Plane) +ᵥ K.openCarrier) := by
      have hxsupport : x ∈ (s : Plane) +ᵥ K.support := by
        have hClosed := K.isPolygonal.isClosed.vadd (s : Plane)
        simpa [hClosed.closure_eq] using (frontier_subset_closure hxfront)
      exact hregular.symm ▸ hxsupport
    exact Set.disjoint_left.mp (hdisj.closure_left (isOpen_interior.vadd (t : Plane)))
      hxclosed hxopen

private theorem endpoint_translateFrontier
    {K : PolygonalRegion} {t : Plane} {x : Plane}
    (hx : x ∈ t +ᵥ frontier K.support) :
    x ∈ frontier (t +ᵥ K.support) := by
  have hbase : x - t ∈ frontier K.support := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hx
  have hbaseSupport : x - t ∈ K.support := by
    have hcl := frontier_subset_closure hbase
    simpa [K.isPolygonal.isClosed.closure_eq] using hcl
  have hsupport : x ∈ t +ᵥ K.support := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hbaseSupport
  have hnotInterior : x ∉ interior (t +ᵥ K.support) := by
    intro hInterior
    have hInterior' : x - t ∈ interior K.support := by
      simpa only [interior_vadd, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, neg_add_eq_sub] using hInterior
    have hbaseParts : x - t ∈ closure K.support ∧
        x - t ∉ interior K.support := by
      simpa only [frontier, Set.mem_sdiff] using hbase
    exact hbaseParts.2 hInterior'
  rw [frontier, Set.mem_sdiff]
  exact ⟨subset_closure hsupport, hnotInterior⟩

private theorem endpoint_frontier_translate
    {K : PolygonalRegion} {t : Plane} {x : Plane}
    (hx : x ∈ frontier (t +ᵥ K.support)) :
    x ∈ t +ᵥ frontier K.support := by
  have hparts : x ∈ closure (t +ᵥ K.support) ∧
      x ∉ interior (t +ᵥ K.support) := by
    simpa only [frontier, Set.mem_sdiff] using hx
  have hcl : x ∈ t +ᵥ closure K.support := by
    simpa only [closure_vadd] using hparts.1
  have hint : x ∉ t +ᵥ interior K.support := by
    simpa only [interior_vadd] using hparts.2
  have hclBase : x - t ∈ closure K.support := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hcl
  have hintBase : x - t ∉ interior K.support := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hint
  have hbase : x - t ∈ frontier K.support := by
    simpa only [frontier, Set.mem_sdiff] using And.intro hclBase hintBase
  simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
    neg_add_eq_sub] using hbase

private theorem endpointRay_openConclusion
    {K : PolygonalRegion} (δ : Submodule ℝ Plane) (T : Set Plane)
    (v e : Plane) (R : ℝ)
    (_hδ : Module.finrank ℝ δ = 1) (_heδ : e ∈ δ) (he : e ≠ 0)
    (htile : TilesOn K T Set.univ) (hR : 0 < R)
    (hin : ∀ q ∈ Set.Ioo (0 : ℝ) R,
      v - q • e ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
    (hout : ∀ q ∈ Set.Ioo (0 : ℝ) R,
      v + q • e ∉ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) :
    ∃ u ∈ T, v ∈ frontier (u +ᵥ K.support) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Set.Ioo (0 : ℝ) r,
        v + q • e ∈ u +ᵥ K.openCarrier := by
  let ray : ℝ → Plane := fun q => v + q • e
  have hpack : IsPacking K.prototileFamily (K.placements T) := htile.2.1
  have hreg : regularSupport K T = Set.univ := by
    apply regularSupport_eq_of_tilesOn isOpen_univ ?_ htile
    simp
  have hclosedUnion := closure_openUnion_eq_iUnion_support hpack
  have hcover : ∀ q ∈ Set.Ioo (0 : ℝ) R,
      ∃ t : T, ray q ∈ (t : Plane) +ᵥ K.openCarrier := by
    intro q hq
    have hqreg : ray q ∈ regularSupport K T := by rw [hreg]; simp
    have hqclose : ray q ∈ closure (openUnion K T) := by
      change ray q ∈ interior (closure (openUnion K T)) at hqreg
      exact interior_subset hqreg
    rw [hclosedUnion] at hqclose
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hqclose
    have hnotfront : ray q ∉ frontier ((t : Plane) +ᵥ K.support) := by
      intro hf
      apply hout q hq
      exact Set.mem_iUnion.mpr ⟨t, endpoint_frontier_translate hf⟩
    have hclosed : IsClosed ((t : Plane) +ᵥ K.support) :=
      K.isPolygonal.isClosed.vadd (t : Plane)
    have htinterior : ray q ∈ interior ((t : Plane) +ᵥ K.support) := by
      by_contra hn
      apply hnotfront
      rw [frontier, hclosed.closure_eq, Set.mem_sdiff]
      exact ⟨ht, hn⟩
    exact ⟨t, by
      change ray q ∈ (t : Plane) +ᵥ interior K.support
      simpa [interior_vadd] using htinterior⟩
  obtain ⟨u, hwhole⟩ := endpoint_openOwner hpack hR hcover
  have huclosure : v ∈ closure ((u : Plane) +ᵥ K.openCarrier) := by
    rw [Metric.mem_closure_iff]
    intro ρ hρ
    have henorm : 0 < ‖e‖ := norm_pos_iff.mpr he
    let q := min (R / 2) (ρ / (2 * ‖e‖))
    have hqpos : 0 < q := lt_min (by linarith) (div_pos hρ (by positivity))
    have hqR : q < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hqI : q ∈ Set.Ioo (0 : ℝ) R := ⟨hqpos, hqR⟩
    refine ⟨v + q • e, hwhole q hqI, ?_⟩
    calc
      dist v (v + q • e) = ‖q • e‖ := by simp [dist_eq_norm]
      _ = q * ‖e‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hqpos]
      _ ≤ (ρ / (2 * ‖e‖)) * ‖e‖ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) henorm.le
      _ < ρ := by field_simp; linarith
  have hvnotinterior : v ∉ interior ((u : Plane) +ᵥ K.support) := by
    intro hvinterior
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior v hvinterior
    have henorm : 0 < ‖e‖ := norm_pos_iff.mpr he
    let q := min (R / 2) (ρ / (2 * ‖e‖))
    have hqpos : 0 < q := lt_min (by linarith) (div_pos hρ (by positivity))
    have hqR : q < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hqI : q ∈ Set.Ioo (0 : ℝ) R := ⟨hqpos, hqR⟩
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hin q hqI)
    have hdist : dist (v - q • e) v < ρ := by
      calc
        dist (v - q • e) v = ‖-(q • e)‖ := by simp
        _ = q * ‖e‖ := by rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hqpos]
        _ ≤ (ρ / (2 * ‖e‖)) * ‖e‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) henorm.le
        _ < ρ := by field_simp; linarith
    have hwball : v - q • e ∈ Metric.ball v ρ := by
      rw [Metric.mem_ball]
      exact hdist
    have hwU : v - q • e ∈ (u : Plane) +ᵥ K.openCarrier := by
      change v - q • e ∈ (u : Plane) +ᵥ interior K.support
      simpa [interior_vadd] using hball hwball
    exact Set.disjoint_left.mp (endpoint_tileFrontier_disjoint_open hpack t u)
      (endpoint_translateFrontier ht) hwU
  refine ⟨u, u.2, ?_, R, hR, hwhole⟩
  have hregular : closure ((u : Plane) +ᵥ K.openCarrier) =
      (u : Plane) +ᵥ K.support := by
    change closure ((u : Plane) +ᵥ interior K.support) = _
    rw [closure_vadd]
    congr 1
    exact K.isPolygonal.closure_interior
  rw [frontier, Set.mem_sdiff]
  have huSupport : v ∈ (u : Plane) +ᵥ K.support := by
    rw [← hregular]
    exact huclosure
  exact ⟨subset_closure huSupport, hvnotinterior⟩

private theorem endpoint_finiteSupportsNear
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : IsPacking K.prototileFamily (K.placements T)) (v : Plane) :
    {t : T | v ∈ (t : Plane) +ᵥ K.support}.Finite := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp
    K.isPolygonal.isBounded
  let A : ℝ := ‖v‖ + M
  have hcentres : (T ∩ Metric.closedBall (0 : Plane) A).Finite := by
    exact (packing_centres_locallyFinite hpack).1 _ Metric.isBounded_closedBall
  have hpre : ((fun t : T => (t : Plane)) ⁻¹'
      (T ∩ Metric.closedBall (0 : Plane) A)).Finite :=
    Set.Finite.preimage (s := T ∩ Metric.closedBall (0 : Plane) A)
      (f := fun t : T => (t : Plane))
      (fun a _ b _ hab => Subtype.ext hab) hcentres
  apply hpre.subset
  intro t ht
  change v ∈ (t : Plane) +ᵥ K.support at ht
  have hy : v - (t : Plane) ∈ K.support := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using ht
  have hysub := hM hy
  have hybound : ‖v - (t : Plane)‖ ≤ M := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hysub
  have htbound : ‖(t : Plane)‖ ≤ A := by
    dsimp [A]
    calc
      ‖(t : Plane)‖ = ‖v - (v - (t : Plane))‖ := by
        congr 1
        abel
      _ ≤ ‖v‖ + ‖v - (t : Plane)‖ := norm_sub_le _ _
      _ ≤ ‖v‖ + M := add_le_add_right hybound ‖v‖
  change (t : Plane) ∈ T ∩ Metric.closedBall (0 : Plane) A
  exact ⟨t.2, by simpa [Metric.mem_closedBall, dist_eq_norm] using htbound⟩

private theorem endpoint_finiteSupportsMeetingBall
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : IsPacking K.prototileFamily (K.placements T)) (v : Plane) :
    {t : T | (((t : Plane) +ᵥ K.support) ∩ Metric.closedBall v 1).Nonempty}.Finite := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp
    K.isPolygonal.isBounded
  let A : ℝ := ‖v‖ + 1 + M
  have hcentres : (T ∩ Metric.closedBall (0 : Plane) A).Finite := by
    exact (packing_centres_locallyFinite hpack).1 _ Metric.isBounded_closedBall
  have hpre : ((fun t : T => (t : Plane)) ⁻¹'
      (T ∩ Metric.closedBall (0 : Plane) A)).Finite :=
    Set.Finite.preimage (s := T ∩ Metric.closedBall (0 : Plane) A)
      (f := fun t : T => (t : Plane))
      (fun a _ b _ hab => Subtype.ext hab) hcentres
  apply hpre.subset
  intro t ht
  change (((t : Plane) +ᵥ K.support) ∩ Metric.closedBall v 1).Nonempty at ht
  obtain ⟨z, hz⟩ := ht
  rcases hz with ⟨hzTile, hzBall⟩
  have hy : z - (t : Plane) ∈ K.support := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hzTile
  have hybound : ‖z - (t : Plane)‖ ≤ M := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hM hy
  have hzbound : ‖z‖ ≤ ‖v‖ + 1 := by
    have hdist : dist z v ≤ 1 := by
      simpa [Metric.mem_closedBall] using hzBall
    calc
      ‖z‖ = dist z 0 := by simp [dist_eq_norm]
      _ ≤ dist z v + dist v 0 := dist_triangle _ _ _
      _ ≤ 1 + ‖v‖ := add_le_add hdist (by simp [dist_eq_norm])
      _ = ‖v‖ + 1 := by ring
  have htbound : ‖(t : Plane)‖ ≤ A := by
    dsimp [A]
    calc
      ‖(t : Plane)‖ = ‖z - (z - (t : Plane))‖ := by congr 1 <;> abel
      _ ≤ ‖z‖ + ‖z - (t : Plane)‖ := norm_sub_le _ _
      _ ≤ (‖v‖ + 1) + M := add_le_add hzbound hybound
  change (t : Plane) ∈ T ∩ Metric.closedBall (0 : Plane) A
  exact ⟨t.2, by simpa [Metric.mem_closedBall, dist_eq_norm] using htbound⟩

private theorem endpoint_clearFiniteTiles
    (v : Plane) (I : Finset (Set Plane)) (hclosed : ∀ s ∈ I, IsClosed s) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s ∈ I, v ∉ s → Disjoint (Metric.ball v ρ) s := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert s I hs ih =>
      have htail : ∀ t ∈ I, IsClosed t := by
        intro t ht
        exact hclosed t (Finset.mem_insert_of_mem ht)
      obtain ⟨ρ, hρ, hρavoid⟩ := ih htail
      by_cases hvs : v ∈ s
      · refine ⟨min ρ 1, lt_min hρ (by norm_num), ?_⟩
        intro t ht hvt
        rcases Finset.mem_insert.mp ht with rfl | htI
        · exact (hvt hvs).elim
        · have hprev := hρavoid t htI hvt
          rw [Set.disjoint_left] at hprev ⊢
          intro z hzBall hzt
          apply hprev
          · exact Metric.mem_ball.mpr
              ((Metric.mem_ball.mp hzBall).trans_le (min_le_left _ _))
          · exact hzt
      · have hsClosed : IsClosed s := hclosed s (Finset.mem_insert_self s I)
        have hopen : IsOpen (sᶜ) := hsClosed.isOpen_compl
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen v hvs
        refine ⟨min ρ r, lt_min hρ hr, ?_⟩
        intro t ht hvt
        rcases Finset.mem_insert.mp ht with rfl | htI
        · rw [Set.disjoint_left]
          intro z hzBall hzS
          exact hball (Metric.mem_ball.mpr
            ((Metric.mem_ball.mp hzBall).trans_le (min_le_right _ _))) hzS
        · have hprev := hρavoid t htI hvt
          rw [Set.disjoint_left] at hprev ⊢
          intro z hzBall hzt
          apply hprev
          · exact Metric.mem_ball.mpr
              ((Metric.mem_ball.mp hzBall).trans_le (min_le_left _ _))
          · exact hzt

private theorem endpoint_starRadius
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : IsPacking K.prototileFamily (K.placements T)) (v : Plane) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : T,
      (((t : Plane) +ᵥ K.support) ∩ Metric.ball v ρ).Nonempty →
        v ∈ (t : Plane) +ᵥ K.support := by
  classical
  have hnear := endpoint_finiteSupportsMeetingBall K T hpack v
  let J := hnear.toFinset
  let I : Finset (Set Plane) := J.image fun t : T => (t : Plane) +ᵥ K.support
  have hclosed : ∀ s ∈ I, IsClosed s := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact K.isPolygonal.isClosed.vadd (t : Plane)
  obtain ⟨r, hr, havoid⟩ := endpoint_clearFiniteTiles v I hclosed
  refine ⟨min r 1, lt_min hr (by norm_num), ?_⟩
  intro t hmeet
  rcases hmeet with ⟨z, hz⟩
  rcases hz with ⟨hzTile, hzBall⟩
  have hzClosed : z ∈ Metric.closedBall v 1 := by
    rw [Metric.mem_closedBall]
    exact (Metric.mem_ball.mp hzBall).le.trans (min_le_right _ _)
  have htNear : t ∈ J := by
    apply hnear.mem_toFinset.mpr
    exact ⟨z, ⟨hzTile, hzClosed⟩⟩
  have htI : (t : Plane) +ᵥ K.support ∈ I :=
    Finset.mem_image.mpr ⟨t, htNear, rfl⟩
  by_contra hnot
  have hdisj := havoid ((t : Plane) +ᵥ K.support) htI hnot
  rw [Set.disjoint_left] at hdisj
  apply hdisj
  · rw [Metric.mem_ball] at hzBall ⊢
    exact hzBall.trans_le (min_le_left _ _)
  · exact hzTile

private theorem endpoint_finiteIncidentEdgeList
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : IsPacking K.prototileFamily (K.placements T)) (v : Plane) :
    ∃ G : Finset (T × (Plane × Plane)),
      (∀ w ∈ G, v ∈ (w.1 : Plane) +ᵥ K.support ∧
        w.2.1 ≠ w.2.2 ∧ w.2.1 ∈ vertexSet K.support ∧
          w.2.2 ∈ vertexSet K.support ∧
            segment ℝ w.2.1 w.2.2 ⊆ frontier K.support) ∧
      ∀ t : T, v ∈ (t : Plane) +ᵥ K.support →
        ∀ x ∈ frontier ((t : Plane) +ᵥ K.support),
          ∃ p : Plane × Plane, (t, p) ∈ G ∧
            x ∈ segment ℝ ((t : Plane) + p.1) ((t : Plane) + p.2) := by
  classical
  have hI := endpoint_finiteSupportsNear K T hpack v
  let I := hI.toFinset
  obtain ⟨F, hF, hcover⟩ :=
    Tiling.IsPolygonal.exists_finite_intrinsic_boundarySegments K.isPolygonal
  let G : Finset (T × (Plane × Plane)) := I.product F
  refine ⟨G, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwI, hwF⟩ := Finset.mem_product.mp hw
    obtain ⟨hne, ha, hb, hseg⟩ := hF w.2 hwF
    exact ⟨hI.mem_toFinset.mp hwI, hne, ha, hb, hseg⟩
  · intro t ht x hx
    have hfrontierVadd : frontier ((t : Plane) +ᵥ K.support) =
        (t : Plane) +ᵥ frontier K.support := by
      rw [frontier, closure_vadd, interior_vadd]
      ext z
      simp only [frontier, Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, neg_add_eq_sub]
    rw [hfrontierVadd] at hx
    have hxbase : x - (t : Plane) ∈ frontier K.support := by
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_eq_sub] using hx
    have hxinEdges : x - (t : Plane) ∈ ⋃ p ∈ F, segment ℝ p.1 p.2 := by
      rw [← hcover]
      exact hxbase
    obtain ⟨p, hp'⟩ := Set.mem_iUnion.mp hxinEdges
    obtain ⟨hp, hseg⟩ := Set.mem_iUnion.mp hp'
    have htI : t ∈ I := hI.mem_toFinset.mpr ht
    have htp : (t, p) ∈ G := by
      exact Finset.mem_product.mpr ⟨htI, hp⟩
    refine ⟨p, htp, ?_⟩
    have htranslate : (t : Plane) + (x - (t : Plane)) ∈
        segment ℝ ((t : Plane) + p.1) ((t : Plane) + p.2) := by
      rw [mem_segment_translate ℝ (t : Plane)]
      exact hseg
    simpa [sub_add_cancel] using htranslate

private theorem endpoint_localFiniteBoundaryStar
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : IsPacking K.prototileFamily (K.placements T)) (v : Plane) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ G : Finset (T × (Plane × Plane)),
      (∀ w ∈ G, v ∈ (w.1 : Plane) +ᵥ K.support ∧
        w.2.1 ≠ w.2.2 ∧ w.2.1 ∈ vertexSet K.support ∧
          w.2.2 ∈ vertexSet K.support ∧
            segment ℝ w.2.1 w.2.2 ⊆ frontier K.support) ∧
      ∀ t : T, ∀ x ∈ Metric.ball v ρ,
        x ∈ frontier ((t : Plane) +ᵥ K.support) →
          ∃ p : Plane × Plane, (t, p) ∈ G ∧
            x ∈ segment ℝ ((t : Plane) + p.1) ((t : Plane) + p.2) := by
  obtain ⟨G, hGvalid, hGcover⟩ := endpoint_finiteIncidentEdgeList K T hpack v
  obtain ⟨ρ, hρ, hstar⟩ := endpoint_starRadius K T hpack v
  refine ⟨ρ, hρ, G, hGvalid, ?_⟩
  intro t x hxball hxfront
  have hxSupport : x ∈ (t : Plane) +ᵥ K.support := by
    have hclosed := K.isPolygonal.isClosed.vadd (t : Plane)
    simpa [hclosed.closure_eq] using frontier_subset_closure hxfront
  have htincident : v ∈ (t : Plane) +ᵥ K.support :=
    hstar t ⟨x, hxSupport, hxball⟩
  exact hGcover t htincident x hxfront

/-- A short transverse ray can avoid every member of a finite family of
    rank-one subspaces, provided its linear-functional level is nonzero. -/
private theorem endpoint_genericTransverseParameter
    (ψ : Plane →ₗ[ℝ] ℝ) (n w : Plane) (ε : ℝ)
    (hε : 0 < ε) (hψn : ψ n = 1) (hψw : ψ w = 0) (hw : w ≠ 0)
    (F : Finset (Submodule ℝ Plane))
    (hRank : ∀ α ∈ F, Module.finrank ℝ α = 1) :
    ∃ t ∈ Set.Ioo (0 : ℝ) ε,
      ∀ α ∈ F, -n + t • w ∉ α := by
  classical
  let P (α : Submodule ℝ Plane) : Prop :=
    ∃ t ∈ Set.Ioo (0 : ℝ) ε, -n + t • w ∈ α
  let b (α : Submodule ℝ Plane) : ℝ :=
    if h : P α then Classical.choose h else 0
  have hb (α : Submodule ℝ Plane) (h : P α) :
      b α ∈ Set.Ioo (0 : ℝ) ε ∧ -n + b α • w ∈ α := by
    dsimp [b]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hψneg : ψ (-n) = -1 := by
    rw [map_neg, hψn]
  have hunique (α : Submodule ℝ Plane) (hα : α ∈ F) :
      ∀ s t : ℝ, s ∈ Set.Ioo (0 : ℝ) ε → t ∈ Set.Ioo (0 : ℝ) ε →
        -n + s • w ∈ α → -n + t • w ∈ α → s = t := by
    intro s t hs ht hsm htm
    by_contra hst
    have hdiff : (s - t) • w ∈ α := by
      have h := α.sub_mem hsm htm
      have heq : (-n + s • w) - (-n + t • w) = (s - t) • w := by
        calc
          (-n + s • w) - (-n + t • w) = s • w - t • w := by abel
          _ = (s - t) • w := by rw [sub_smul]
      exact heq ▸ h
    have hne : s - t ≠ 0 := sub_ne_zero.mpr hst
    have hwα : w ∈ α := by
      have h := α.smul_mem (s - t)⁻¹ hdiff
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at h
      exact h
    have hnα : -n ∈ α := by
      have h := α.sub_mem hsm (α.smul_mem s hwα)
      have heq : (-n + s • w) - s • w = -n := by abel
      exact heq ▸ h
    have hspan : α = Submodule.span ℝ ({w} : Set Plane) :=
      eq_span_singleton_of_mem_of_finrank_eq_one (hRank α hα) hwα hw
    have hnspan : -n ∈ Submodule.span ℝ ({w} : Set Plane) := by
      rw [← hspan]
      exact hnα
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hnspan
    have hψeq := congrArg ψ hc
    rw [map_smul, hψw, hψneg] at hψeq
    norm_num at hψeq
  let E : Finset ℝ := F.image b
  obtain ⟨t, ht, htE⟩ := (Set.Ioo_infinite hε).exists_notMem_finset E
  refine ⟨t, ht, ?_⟩
  intro α hα hmem
  have hP : P α := ⟨t, ht, hmem⟩
  have hbα := hb α hP
  have hteq : b α = t :=
    hunique α hα (b α) t hbα.1 ht hbα.2 hmem
  apply htE
  change t ∈ F.image b
  rw [Finset.mem_image]
  exact ⟨α, hα, hteq⟩

/-- The exceptional slopes against a finite incident fan form a finite set. -/
private theorem endpoint_finiteTransverseExceptions
    (ψ : Plane →ₗ[ℝ] ℝ) (n w : Plane)
    (hψn : ψ n = 1) (hψw : ψ w = 0) (hw : w ≠ 0)
    (F : Finset (Submodule ℝ Plane))
    (hRank : ∀ α ∈ F, Module.finrank ℝ α = 1) :
    ∃ E : Finset ℝ, ∀ t, t ∉ E → ∀ α ∈ F, -n + t • w ∉ α := by
  classical
  let P (α : Submodule ℝ Plane) : Prop := ∃ t : ℝ, -n + t • w ∈ α
  let b (α : Submodule ℝ Plane) : ℝ :=
    if h : P α then Classical.choose h else 0
  have hb (α : Submodule ℝ Plane) (h : P α) : -n + b α • w ∈ α := by
    dsimp [b]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hψneg : ψ (-n) = -1 := by rw [map_neg, hψn]
  have hunique (α : Submodule ℝ Plane) (hα : α ∈ F) :
      ∀ s t : ℝ, -n + s • w ∈ α → -n + t • w ∈ α → s = t := by
    intro s t hsm htm
    by_contra hst
    have hdiff : (s - t) • w ∈ α := by
      have h := α.sub_mem hsm htm
      have heq : (-n + s • w) - (-n + t • w) = (s - t) • w := by
        calc
          (-n + s • w) - (-n + t • w) = s • w - t • w := by abel
          _ = (s - t) • w := by rw [sub_smul]
      exact heq ▸ h
    have hne : s - t ≠ 0 := sub_ne_zero.mpr hst
    have hwα : w ∈ α := by
      have h := α.smul_mem (s - t)⁻¹ hdiff
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at h
      exact h
    have hnα : -n ∈ α := by
      have h := α.sub_mem hsm (α.smul_mem s hwα)
      have heq : (-n + s • w) - s • w = -n := by abel
      exact heq ▸ h
    have hspan : α = Submodule.span ℝ ({w} : Set Plane) :=
      eq_span_singleton_of_mem_of_finrank_eq_one (hRank α hα) hwα hw
    have hnspan : -n ∈ Submodule.span ℝ ({w} : Set Plane) := by
      rw [← hspan]
      exact hnα
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hnspan
    have hψeq := congrArg ψ hc
    rw [map_smul, hψw, hψneg] at hψeq
    norm_num at hψeq
  let E : Finset ℝ := F.image b
  refine ⟨E, ?_⟩
  intro t ht α hα hline
  have hP : P α := ⟨t, hline⟩
  have hteq : b α = t := hunique α hα (b α) t (hb α hP) hline
  apply ht
  change t ∈ F.image b
  rw [Finset.mem_image]
  exact ⟨α, hα, hteq⟩

/-- A linearly independent vector gives a normalized functional transverse to
    a prescribed one-dimensional subspace. -/
private theorem endpoint_transverseFunctional
    (η : Submodule ℝ Plane) (e w : Plane)
    (hη : η = Submodule.span ℝ ({w} : Set Plane))
    (heη : e ∉ η) (hw : w ≠ 0) :
    ∃ ψ : Plane →ₗ[ℝ] ℝ, ψ e = 1 ∧ ψ w = 0 := by
  classical
  let ψ₀ : Plane →ₗ[ℝ] ℝ :=
    (w.im : ℝ) • Complex.reCLM.toLinearMap -
      (w.re : ℝ) • Complex.imCLM.toLinearMap
  let det : ℝ := w.im * e.re - w.re * e.im
  have hdet : det ≠ 0 := by
    intro hdet0
    dsimp [det] at hdet0
    rcases ne_or_eq w.re 0 with hwre | hwre
    · have heη' : e ∈ Submodule.span ℝ ({w} : Set Plane) := by
        rw [Submodule.mem_span_singleton]
        refine ⟨e.re / w.re, ?_⟩
        apply Complex.ext
        · rw [Complex.smul_re, smul_eq_mul]
          field_simp
        · rw [Complex.smul_im, smul_eq_mul]
          field_simp at hdet0 ⊢
          nlinarith
      exact heη (hη ▸ heη')
    · have hwim : w.im ≠ 0 := by
        intro hwim
        apply hw
        apply Complex.ext <;> simp [hwre, hwim]
      have here : e.re = 0 := by
        have : w.im * e.re = 0 := by simpa [hwre] using hdet0
        exact (mul_eq_zero.mp this).resolve_left hwim
      have heη' : e ∈ Submodule.span ℝ ({w} : Set Plane) := by
        rw [Submodule.mem_span_singleton]
        refine ⟨e.im / w.im, ?_⟩
        apply Complex.ext
        · rw [Complex.smul_re, smul_eq_mul]
          rw [hwre, here]
          simp
        · rw [Complex.smul_im, smul_eq_mul]
          field_simp
      exact heη (hη ▸ heη')
  refine ⟨det⁻¹ • ψ₀, ?_, ?_⟩
  · have hψe : ψ₀ e = det := by
      simp [ψ₀, det, map_sub, map_smul]
    rw [LinearMap.smul_apply, hψe]
    change det⁻¹ * det = 1
    exact inv_mul_cancel₀ hdet
  · rw [LinearMap.smul_apply]
    change det⁻¹ * ψ₀ w = 0
    apply mul_eq_zero.mpr
    right
    simp [ψ₀, map_sub, map_smul]
    ring

private theorem endpoint_segmentClosed (a b : Plane) :
    IsClosed (segment ℝ a b) := by
  have hcompact : IsCompact (AffineMap.lineMap a b '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image AffineMap.lineMap_continuous
  rw [segment_eq_image_lineMap]
  exact hcompact.isClosed

private theorem endpoint_sub_mem_edgeDirection
    (a b x y : Plane) (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) :
    y - x ∈ Submodule.span ℝ ({b - a} : Set Plane) := by
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  apply Submodule.mem_span_singleton.mpr
  refine ⟨t - s, ?_⟩
  simp only [AffineMap.lineMap_apply_module]
  module

/-- A sufficiently small ball misses every finite local edge which does not
    contain its centre; edges which do contain it have their usual direction. -/
private theorem endpoint_localEdgeClearance
    (v : Plane) (T : Set Plane) (G : Finset (T × (Plane × Plane))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ G, ∀ y ∈ Metric.ball v ρ,
      y ∈ segment ℝ ((z.1 : Plane) + z.2.1) ((z.1 : Plane) + z.2.2) →
        v ∈ segment ℝ ((z.1 : Plane) + z.2.1) ((z.1 : Plane) + z.2.2) ∧
          y - v ∈ Submodule.span ℝ ({z.2.2 - z.2.1} : Set Plane) := by
  classical
  let S (z : T × (Plane × Plane)) : Set Plane :=
    segment ℝ ((z.1 : Plane) + z.2.1) ((z.1 : Plane) + z.2.2)
  let J := G.filter fun z => v ∉ S z
  let I : Finset (Set Plane) := J.image S
  have hclosed : ∀ A ∈ I, IsClosed A := by
    intro A hA
    obtain ⟨z, hzJ, rfl⟩ := Finset.mem_image.mp hA
    exact endpoint_segmentClosed _ _
  obtain ⟨ρ, hρ, havoid⟩ := endpoint_clearFiniteTiles v I hclosed
  refine ⟨ρ, hρ, ?_⟩
  intro z hz y hyball hyseg
  by_cases hv : v ∈ S z
  · refine ⟨hv, ?_⟩
    have hsub := endpoint_sub_mem_edgeDirection _ _ _ _ hv hyseg
    simpa [S, sub_add_cancel] using hsub
  · have hzJ : z ∈ J := Finset.mem_filter.mpr ⟨hz, hv⟩
    have hSI : S z ∈ I := Finset.mem_image.mpr ⟨z, hzJ, rfl⟩
    have hdisj := havoid (S z) hSI hv
    rw [Set.disjoint_left] at hdisj
    exact (hdisj hyball hyseg).elim

private theorem endpoint_tileSupports_cover
    (K : PolygonalRegion) (T : Set Plane)
    (htile : TilesOn K T Set.univ) :
    (⋃ t : T, (t : Plane) +ᵥ K.support) = Set.univ := by
  have hregular : Tiling.Polygonal.regularSupport K T = Set.univ := by
    apply Tiling.Polygonal.regularSupport_eq_of_tilesOn isOpen_univ
      (by simp) htile
  have hclosure : closure (Tiling.Polygonal.openUnion K T) = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      have hx : x ∈ Tiling.Polygonal.regularSupport K T := by
        rw [hregular]
        simp
      simpa [Tiling.Polygonal.regularSupport] using
        (interior_subset : interior (closure (Tiling.Polygonal.openUnion K T)) ⊆
          closure (Tiling.Polygonal.openUnion K T)) hx
  rw [← Tiling.Polygonal.closure_openUnion_eq_iUnion_support htile.2.1, hclosure]

private theorem endpoint_connected_wedge_has_owner
    (K : PolygonalRegion) (T : Set Plane) (v : Plane) (W : Set Plane)
    (hpack : IsPacking K.prototileFamily (K.placements T))
    (htile : TilesOn K T Set.univ) (hconn : IsConnected W)
    (hnoFront : ∀ y ∈ W, ∀ t : T,
      y ∉ frontier ((t : Plane) +ᵥ K.support))
    (hbound : W ⊆ Metric.ball v 1) :
    ∃ s : T, W ⊆ (s : Plane) +ᵥ K.openCarrier := by
  classical
  let J : Finset T :=
    (endpoint_finiteSupportsMeetingBall K T hpack v).toFinset
  let U : Finset (Set Plane) := J.image fun t : T =>
    (t : Plane) +ᵥ K.openCarrier
  have hcover : W ⊆ ⋃₀ (U : Set (Set Plane)) := by
    intro y hy
    have hyGlobal : y ∈ ⋃ t : T, (t : Plane) +ᵥ K.support := by
      rw [endpoint_tileSupports_cover K T htile]
      simp
    obtain ⟨t, hyt⟩ := Set.mem_iUnion.mp hyGlobal
    have hyball : y ∈ Metric.closedBall v 1 :=
      Metric.ball_subset_closedBall (hbound hy)
    have htJ : t ∈ J := by
      apply (endpoint_finiteSupportsMeetingBall K T hpack v).mem_toFinset.mpr
      change (((t : Plane) +ᵥ K.support) ∩ Metric.closedBall v 1).Nonempty
      exact ⟨y, ⟨hyt, hyball⟩⟩
    have hclosed : IsClosed ((t : Plane) +ᵥ K.support) :=
      K.isPolygonal.isClosed.vadd (t : Plane)
    have hyInterior : y ∈ interior ((t : Plane) +ᵥ K.support) := by
      by_contra hnot
      have hyfront : y ∈ frontier ((t : Plane) +ᵥ K.support) := by
        rw [hclosed.frontier_eq]
        exact ⟨hyt, hnot⟩
      exact hnoFront y hy t hyfront
    have hyOpen : y ∈ (t : Plane) +ᵥ K.openCarrier := by
      simpa [interior_vadd, PolygonalRegion.openCarrier] using hyInterior
    apply Set.mem_sUnion.mpr
    refine ⟨(t : Plane) +ᵥ K.openCarrier,
      Finset.mem_image.mpr ⟨t, htJ, rfl⟩, hyOpen⟩
  have hdisj : ∀ A B, A ∈ U → B ∈ U → (W ∩ (A ∩ B)).Nonempty → A = B := by
    intro A B hA hB hmeet
    obtain ⟨s, hsJ, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨t, htJ, rfl⟩ := Finset.mem_image.mp hB
    by_cases hst : s = t
    · simpa [hst]
    · obtain ⟨x, hxW, hxS, hxT⟩ := hmeet
      have hdis := (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K T).mp
        hpack s.2 t.2 (fun h => hst (Subtype.ext h))
      exact False.elim ((Set.disjoint_left.mp hdis) hxS hxT)
  have hopen : ∀ A ∈ U, IsOpen A := by
    intro A hA
    obtain ⟨t, htJ, rfl⟩ := Finset.mem_image.mp hA
    exact (Homeomorph.addLeft (t : Plane)).isOpenMap _ isOpen_interior
  obtain ⟨A, hA, hWA⟩ :=
    (isConnected_iff_sUnion_disjoint_open).mp hconn U hdisj hopen hcover
  obtain ⟨s, hsJ, rfl⟩ := Finset.mem_image.mp hA
  exact ⟨s, hWA⟩

private theorem endpoint_wedge_owner_contains_positive_edge_in_support
    (K : PolygonalRegion) (T : Set Plane) (v e w : Plane) (M c : ℝ)
    (s : T) (hM : 0 < M) (hc : 0 < c)
    (howner : (fun p : ℝ × ℝ => v - p.1 • e + p.2 • w) ''
      {p : ℝ × ℝ | 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c} ⊆
        (s : Plane) +ᵥ K.openCarrier) :
    ∀ z ∈ Set.Ioo (0 : ℝ) c, v + z • w ∈ (s : Plane) +ᵥ K.support := by
  intro z hz
  have hregular : closure ((s : Plane) +ᵥ K.openCarrier) =
      (s : Plane) +ᵥ K.support := by
    rw [closure_vadd, PolygonalRegion.openCarrier, K.isPolygonal.closure_interior]
  rw [← hregular]
  rw [Metric.mem_closure_iff]
  intro ε hε
  let q : ℝ := min (z / (2 * M)) (ε / (2 * (‖e‖ + 1)))
  have hq : 0 < q := by
    dsimp [q]
    exact lt_min (div_pos hz.1 (by positivity)) (div_pos hε (by positivity))
  have hqleft : q ≤ z / (2 * M) := by dsimp [q]; exact min_le_left _ _
  have hqright : q ≤ ε / (2 * (‖e‖ + 1)) := by
    dsimp [q]
    exact min_le_right _ _
  have hMqle : M * q ≤ z / 2 := by
    calc
      M * q ≤ M * (z / (2 * M)) := mul_le_mul_of_nonneg_left hqleft hM.le
      _ = z / 2 := by field_simp
  have hMq : M * q < z := by linarith [hz.1]
  let y : Plane := v - q • e + z • w
  have hyW : y ∈ (fun p : ℝ × ℝ => v - p.1 • e + p.2 • w) ''
      {p : ℝ × ℝ | 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c} := by
    refine ⟨(q, z), ⟨hq, hMq, hz.2⟩, ?_⟩
    simp [y]
  have hfrac : ‖e‖ / (2 * (‖e‖ + 1)) ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [norm_nonneg e]
  have hnorm : q * ‖e‖ ≤ ε / 2 := by
    calc
      q * ‖e‖ ≤ (ε / (2 * (‖e‖ + 1))) * ‖e‖ :=
        mul_le_mul_of_nonneg_right hqright (norm_nonneg e)
      _ = ε * (‖e‖ / (2 * (‖e‖ + 1))) := by ring
      _ ≤ ε / 2 := by nlinarith [hfrac, hε.le, norm_nonneg e]
  have hdist : dist (v + z • w) y = q * ‖e‖ := by
    rw [dist_eq_norm]
    have hySub : (v + z • w) - y = q • e := by
      dsimp [y]
      module
    rw [hySub, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
  refine ⟨y, howner hyW, ?_⟩
  calc
    dist (v + z • w) y = q * ‖e‖ := hdist
    _ ≤ ε / 2 := hnorm
    _ < ε := by linarith

private theorem endpoint_wedge_point_is_frontier_of_actual_owner
    (K : PolygonalRegion) (T : Set Plane) (v e w : Plane) (M c d : ℝ)
    (u s : T) (hpack : IsPacking K.prototileFamily (K.placements T))
    (hM : 0 < M) (hc : 0 < c) (hd : 0 < d) (hdc : d ≤ c)
    (howner : (fun p : ℝ × ℝ => v - p.1 • e + p.2 • w) ''
      {p : ℝ × ℝ | 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c} ⊆
        (s : Plane) +ᵥ K.openCarrier)
    (huFront : ∀ z ∈ Set.Ioo (0 : ℝ) d,
      v + z • w ∈ frontier ((u : Plane) +ᵥ K.support)) :
    ∀ z ∈ Set.Ioo (0 : ℝ) d,
      v + z • w ∈ frontier ((s : Plane) +ᵥ K.support) := by
  intro z hz
  have hzc : z ∈ Set.Ioo (0 : ℝ) c := ⟨hz.1, lt_of_lt_of_le hz.2 hdc⟩
  have hsupp := endpoint_wedge_owner_contains_positive_edge_in_support
    K T v e w M c s hM hc howner z hzc
  have hnotInterior : v + z • w ∉ interior ((s : Plane) +ᵥ K.support) := by
    intro hinterior
    by_cases hus : u = s
    · subst s
      have huParts : v + z • w ∈ closure ((u : Plane) +ᵥ K.support) ∧
          v + z • w ∉ interior ((u : Plane) +ᵥ K.support) := by
        simpa only [frontier, Set.mem_sdiff] using huFront z hz
      exact huParts.2 hinterior
    · have hdis := (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K T).mp
        hpack u.2 s.2 (fun h => hus (Subtype.ext h))
      have huBase : v + z • w - (u : Plane) ∈ K.support := by
        have huClose := frontier_subset_closure (huFront z hz)
        have huCloseBase : v + z • w - (u : Plane) ∈ closure K.support := by
          simpa [closure_vadd, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
            sub_eq_add_neg, add_comm] using huClose
        simpa [(K.isPolygonal.isClosed.closure_eq)] using huCloseBase
      have hclosureU : v + z • w ∈ closure ((u : Plane) +ᵥ K.openCarrier) := by
        rw [closure_vadd, PolygonalRegion.openCarrier, K.isPolygonal.closure_interior]
        exact Set.mem_vadd_set_iff_neg_vadd_mem.mpr (by
          simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using huBase)
      have hinteriorU : v + z • w ∈ (s : Plane) +ᵥ K.openCarrier := by
        simpa [interior_vadd, PolygonalRegion.openCarrier] using hinterior
      have hOpenS : IsOpen ((s : Plane) +ᵥ K.openCarrier) :=
        (Homeomorph.addLeft (s : Plane)).isOpenMap _ isOpen_interior
      exact (Set.disjoint_left.mp (hdis.closure_left hOpenS)) hclosureU hinteriorU
  have hclosure : v + z • w ∈ closure ((s : Plane) +ᵥ K.support) :=
    by simpa [(K.isPolygonal.isClosed.vadd (s : Plane)).closure_eq] using hsupp
  rw [frontier, Set.mem_sdiff]
  exact ⟨hclosure, hnotInterior⟩

private theorem endpoint_actual_wedge_gives_proper_edge_contact
    (K : PolygonalRegion) (η : Submodule ℝ Plane) (u s v w : Plane) (d : ℝ)
    (hw : w ≠ 0) (hηw : w ∈ η) (hd : 0 < d)
    (huFront : ∀ z ∈ Set.Ioo (0 : ℝ) d,
      v + z • w ∈ frontier (u +ᵥ K.support))
    (hsFront : ∀ z ∈ Set.Ioo (0 : ℝ) d,
      v + z • w ∈ frontier (s +ᵥ K.support)) :
    ProperEdgeContactAlong K η u s := by
  let a : Plane := v + (d / 4) • w
  let b : Plane := v + (d / 2) • w
  have hdiff : b - a = (d / 4) • w := by
    have hvec : (v + (d / 2) • w) - (v + (d / 4) • w) =
        ((d / 2) - (d / 4)) • w := by module
    rw [hvec]
    congr 1
    ring
  have hne : a ≠ b := by
    intro hab
    have hba : b - a = 0 := sub_eq_zero.mpr hab.symm
    have hz : (d / 4) • w = 0 := by rw [← hdiff, hba]
    rcases smul_eq_zero.mp hz with hd0 | hw0
    · exact (ne_of_gt (by positivity : 0 < d / 4)) hd0
    · exact hw hw0
  refine ⟨a, b, hne, ?_, ?_⟩
  · rw [hdiff]
    exact Submodule.smul_mem η (d / 4) hηw
  · intro y hy
    rw [openSegment_eq_image_lineMap] at hy
    obtain ⟨t, ht, hyline⟩ := hy
    let z : ℝ := d / 4 + t * (d / 4)
    have hz : z ∈ Set.Ioo (0 : ℝ) d := by
      constructor
      · dsimp [z]
        nlinarith [hd, ht.1]
      · dsimp [z]
        have ht0 := ht.1
        have ht1 := ht.2
        nlinarith
    have hline : AffineMap.lineMap a b t = v + z • w := by
      calc
        AffineMap.lineMap a b t = t • (b - a) + a :=
          AffineMap.lineMap_apply_module' a b t
        _ = t • ((d / 4) • w) + (v + (d / 4) • w) := by
          rw [hdiff]
        _ = (t * (d / 4) + d / 4) • w + v := by
          rw [smul_smul]
          rw [add_smul]
          abel
        _ = v + z • w := by
          have hzEq : t * (d / 4) + d / 4 = z := by
            dsimp [z]
            ring
          rw [hzEq]
          abel
    have hyPoint : y = v + z • w := hyline.symm.trans hline
    rw [hyPoint]
    exact ⟨huFront z hz, hsFront z hz⟩

private theorem endpoint_openCarrier_avoids_allFrontiers
    (K : PolygonalRegion) (T : Set Plane)
    (hpack : IsPacking K.prototileFamily (K.placements T))
    (s t : T) (y : Plane) (hy : y ∈ (s : Plane) +ᵥ K.openCarrier) :
    y ∉ frontier ((t : Plane) +ᵥ K.support) := by
  intro hfront
  by_cases hst : s = t
  · subst t
    have hyInterior : y ∈ interior ((s : Plane) +ᵥ K.support) := by
      simpa [interior_vadd, PolygonalRegion.openCarrier] using hy
    have hparts : y ∈ closure ((s : Plane) +ᵥ K.support) ∧
        y ∉ interior ((s : Plane) +ᵥ K.support) := by
      simpa only [frontier, Set.mem_sdiff] using hfront
    exact hparts.2 hyInterior
  ·
    have hsupp : y ∈ (t : Plane) +ᵥ K.support := by
      have hcl := frontier_subset_closure hfront
      simpa [(K.isPolygonal.isClosed.vadd (t : Plane)).closure_eq] using hcl
    have hsupp' : y - (t : Plane) ∈ K.support := by
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_eq_sub] using hsupp
    have hclOpen : y ∈ closure ((t : Plane) +ᵥ K.openCarrier) := by
      rw [closure_vadd]
      change y ∈ (t : Plane) +ᵥ closure (interior K.support)
      rw [K.isPolygonal.closure_interior]
      exact Set.mem_vadd_set_iff_neg_vadd_mem.mpr (by
        simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hsupp')
    have hyInterior : y ∈ interior ((s : Plane) +ᵥ K.support) := by
      simpa [interior_vadd, PolygonalRegion.openCarrier] using hy
    obtain ⟨z, hzS, hzT⟩ := mem_closure_iff.mp hclOpen
      (interior ((s : Plane) +ᵥ K.support)) isOpen_interior hyInterior
    have hdis := (Tiling.Polygonal.isPacking_iff_openCarrier_disjoint K T).mp
      hpack s.2 t.2 (fun h => hst (Subtype.ext h))
    have hzS' : z ∈ (s : Plane) +ᵥ K.openCarrier := by
      simpa [interior_vadd, PolygonalRegion.openCarrier] using hzS
    exact (Set.disjoint_left.mp hdis) hzS' hzT

/-- A connected set covered by finitely many pairwise disjoint open sets has
    one owner throughout. -/
private theorem endpoint_complementaryWedge_connected
    (v e w : Plane) (M c : ℝ) (hM : 0 < M) (hc : 0 < c) :
    IsConnected ((fun p : ℝ × ℝ => v - p.1 • e + p.2 • w) ''
      {p : ℝ × ℝ | 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c}) ∧
      ((fun p : ℝ × ℝ => v - p.1 • e + p.2 • w) ''
        {p : ℝ × ℝ | 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c}).Nonempty := by
  let P : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c}
  let f : ℝ × ℝ → Plane := fun p => v - p.1 • e + p.2 • w
  have hconv : Convex ℝ P := by
    intro p hp q hq a b ha hb hab
    change 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c at hp
    change 0 < q.1 ∧ M * q.1 < q.2 ∧ q.2 < c at hq
    change 0 < a * p.1 + b * q.1 ∧
      M * (a * p.1 + b * q.1) < a * p.2 + b * q.2 ∧
        a * p.2 + b * q.2 < c
    have weighted_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
        0 < a * x + b * y := by
      by_cases haz : a = 0
      · subst a
        have hb1 : b = 1 := by linarith
        simp [hb1]
        exact hy
      · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
        have hax : 0 < a * x := mul_pos ha' hx
        have hby : 0 ≤ b * y := mul_nonneg hb hy.le
        linarith
    constructor
    · exact weighted_pos hp.1 hq.1
    constructor
    · have hgap := weighted_pos (sub_pos.mpr hp.2.1) (sub_pos.mpr hq.2.1)
      nlinarith [hgap]
    · have hgap := weighted_pos (sub_pos.mpr hp.2.2) (sub_pos.mpr hq.2.2)
      nlinarith [hgap]
  have hPne : P.Nonempty := by
    let z : ℝ := c / 2
    let q : ℝ := z / (2 * M)
    refine ⟨(q, z), ?_⟩
    change 0 < q ∧ M * q < z ∧ z < c
    have hz : 0 < z := by dsimp [z]; linarith
    have hq : 0 < q := by dsimp [q]; positivity
    have hMq : M * q = z / 2 := by dsimp [q]; field_simp
    constructor
    · exact hq
    constructor
    · rw [hMq]
      linarith
    · dsimp [z]
      linarith
  have hfcont : Continuous (fun p : ℝ × ℝ => v - p.1 • e + p.2 • w) := by
    fun_prop
  have hconn : IsConnected P := hconv.isConnected hPne
  refine ⟨hconn.image (fun p : ℝ × ℝ => v - p.1 • e + p.2 • w)
    hfcont.continuousOn, ?_⟩
  refine ⟨(fun p : ℝ × ℝ => v - p.1 • e + p.2 • w) ⟨c / (8 * M), c / 2⟩,
    ⟨⟨c / (8 * M), c / 2⟩, ?_, rfl⟩⟩
  change 0 < c / (8 * M) ∧ M * (c / (8 * M)) < c / 2 ∧ c / 2 < c
  constructor
  · positivity
  constructor
  · have hcalc : M * (c / (8 * M)) = c / 8 := by
      field_simp
    rw [hcalc]
    linarith
  · linarith

/-- The narrow complementary wedge misses every actual tiled frontier when its
    slope lies beyond all finite-star exceptional directions. -/
private theorem endpoint_complementaryWedge_noFrontier
    (K : PolygonalRegion) (T : Set Plane) (v e w : Plane) (M c ρ : ℝ)
    (G : Finset (T × (Plane × Plane)))
    (hGcover : ∀ t : T, ∀ x ∈ Metric.ball v ρ,
      x ∈ frontier ((t : Plane) +ᵥ K.support) →
        ∃ p, (t, p) ∈ G ∧
          x ∈ segment ℝ ((t : Plane) + p.1) ((t : Plane) + p.2))
    (hclear : ∀ z ∈ G, ∀ y ∈ Metric.ball v ρ,
      y ∈ segment ℝ (z.1 + z.2.1) (z.1 + z.2.2) →
        v ∈ segment ℝ (z.1 + z.2.1) (z.1 + z.2.2) ∧
          y - v ∈ Submodule.span ℝ ({z.2.2 - z.2.1} : Set Plane))
    (hF : ∀ z ∈ G, ∀ t, M < t →
      -e + t • w ∉ Submodule.span ℝ ({z.2.2 - z.2.1} : Set Plane))
    (hBound : ∀ y ∈ ((fun p : ℝ × ℝ => v - p.1 • e + p.2 • w) ''
      {p : ℝ × ℝ | 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c}),
      y ∈ Metric.ball v ρ) :
    ∀ y ∈ ((fun p : ℝ × ℝ => v - p.1 • e + p.2 • w) ''
      {p : ℝ × ℝ | 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c}),
      ∀ t : T, y ∉ frontier ((t : Plane) +ᵥ K.support) := by
  intro y hy t hfront
  obtain ⟨p, hpG, hyp⟩ := hGcover t y (hBound y hy) hfront
  have hclearY := hclear (t, p) hpG y (hBound y hy) hyp
  change y ∈ (fun p : ℝ × ℝ => v - p.1 • e + p.2 • w) ''
    {p : ℝ × ℝ | 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c} at hy
  obtain ⟨⟨q, z⟩, hqz, rfl⟩ := hy
  have hq : 0 < q := by simpa using hqz.1
  have hz : M * q < z := by simpa using hqz.2.1
  let s : ℝ := z / q
  have hs : M < s := by
    dsimp [s]
    rw [lt_div_iff₀ hq]
    exact hz
  have hdiff : (v - q • e + z • w) - v = q • (-e + s • w) := by
    dsimp [s]
    calc
      (v - q • e + z • w) - v = -q • e + z • w := by module
      _ = q • (-e + (z / q) • w) := by
        rw [smul_add, smul_neg, smul_smul]
        have hqz : q * (z / q) = z := by field_simp
        rw [hqz]
        module
  have hdirection : -e + s • w ∈
      Submodule.span ℝ ({p.2 - p.1} : Set Plane) := by
    have hqspan : q • (-e + s • w) ∈
        Submodule.span ℝ ({p.2 - p.1} : Set Plane) := by
      rw [← hdiff]
      exact hclearY.2
    have hqne : q ≠ 0 := ne_of_gt hq
    have h := (Submodule.span ℝ ({p.2 - p.1} : Set Plane)).smul_mem q⁻¹ hqspan
    rw [smul_smul, inv_mul_cancel₀ hqne, one_smul] at h
    exact h
  exact hF (t, p) hpG s hs hdirection

/-- If a ray enters the interior from a relative interior point of a genuine
    boundary edge, its direction is not parallel to that edge. -/
private theorem endpoint_outgoing_notAlongEdge
    (K : PolygonalRegion) (u v x e : Plane) (r : ℝ)
    (a b : Plane) (_ha : a ≠ b)
    (hx : x = v - u) (hxopen : x ∈ openSegment ℝ a b)
    (hseg : segment ℝ a b ⊆ frontier K.support)
    (hr : 0 < r)
    (huOut : ∀ q ∈ Set.Ioo (0 : ℝ) r,
      v + q • e ∈ u +ᵥ K.openCarrier) :
    e ∉ Submodule.span ℝ ({b - a} : Set Plane) := by
  intro heη
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp heη
  rw [openSegment_eq_image_lineMap] at hxopen
  obtain ⟨θ, hθ, hxline⟩ := hxopen
  let B : ℝ := |c| + 1
  let q : ℝ := min (r / 2) (min (θ / (2 * B)) ((1 - θ) / (2 * B)))
  have hθ0 : 0 < θ := hθ.1
  have hB : 0 < B := by dsimp [B]; positivity
  have hq : 0 < q := by
    dsimp [q]
    apply lt_min
    · linarith
    · apply lt_min
      · exact div_pos hθ0 (by positivity)
      · exact div_pos (by linarith [hθ.2]) (by positivity)
  have hqr : q < r := by
    have : q ≤ r / 2 := min_le_left _ _
    linarith
  have hqθ : q ≤ θ / (2 * B) := by
    dsimp [q]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hqoneθ : q ≤ (1 - θ) / (2 * B) := by
    dsimp [q]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hqcθ : |q * c| ≤ θ / 2 := by
    calc
      |q * c| = q * |c| := by rw [abs_mul, abs_of_pos hq]
      _ ≤ q * B := mul_le_mul_of_nonneg_left (by dsimp [B]; linarith [abs_nonneg c]) hq.le
      _ ≤ (θ / (2 * B)) * B := mul_le_mul_of_nonneg_right hqθ hB.le
      _ = θ / 2 := by field_simp
  have hqc1θ : |q * c| ≤ (1 - θ) / 2 := by
    calc
      |q * c| = q * |c| := by rw [abs_mul, abs_of_pos hq]
      _ ≤ q * B := mul_le_mul_of_nonneg_left (by dsimp [B]; linarith [abs_nonneg c]) hq.le
      _ ≤ ((1 - θ) / (2 * B)) * B := mul_le_mul_of_nonneg_right hqoneθ hB.le
      _ = (1 - θ) / 2 := by field_simp
  have hθq : θ + q * c ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · have habs := (abs_le.mp hqcθ).1
      linarith
    · have habs := (abs_le.mp hqc1θ).2
      linarith [hθ.2]
  have hlineMapShift : AffineMap.lineMap a b (θ + q * c) =
      AffineMap.lineMap a b θ + (q * c) • (b - a) := by
    simp only [AffineMap.lineMap_apply_module]
    module
  have hpoint : u + AffineMap.lineMap a b (θ + q * c) = v + q • e := by
    rw [hlineMapShift, ← smul_smul, hc, hxline, hx]
    dsimp
    abel
  have hseg' : AffineMap.lineMap a b (θ + q * c) ∈ segment ℝ a b :=
    lineMap_mem_segment ℝ a b (Set.mem_Icc.mpr ⟨le_of_lt hθq.1, le_of_lt hθq.2⟩)
  have htranslated : u + AffineMap.lineMap a b (θ + q * c) ∈
      frontier (u +ᵥ K.support) := by
    have hfrontierVadd : frontier (u +ᵥ K.support) = u +ᵥ frontier K.support := by
      rw [frontier, closure_vadd, interior_vadd]
      ext z
      simp only [frontier, Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, neg_add_eq_sub]
    rw [hfrontierVadd]
    exact Set.mem_vadd_set_iff_neg_vadd_mem.mpr (by
      simpa [vadd_eq_add] using hseg hseg')
  have hboundary : v + q • e ∈ frontier (u +ᵥ K.support) := by
    rw [← hpoint]
    exact htranslated
  have hinterior : v + q • e ∈ interior (u +ᵥ K.support) := by
    simpa [interior_vadd, PolygonalRegion.openCarrier] using huOut q ⟨hq, hqr⟩
  have hparts : v + q • e ∈ closure (u +ᵥ K.support) ∧
      v + q • e ∉ interior (u +ᵥ K.support) := by
    simpa only [frontier, Set.mem_sdiff] using hboundary
  exact hparts.2 hinterior

/-- Finite-edge extraction at a nonvertex outgoing endpoint. The finite
    incident-edge family is constructed separately above. The remaining
    obligation is to select its complementary cone owner and prove the contact
    vertex using the incoming ray. This development hole is deliberately
    localized here. -/
private theorem contactFan_nonvertex_endpoint
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (v e : Plane) (R : ℝ)
    (hδ : Module.finrank ℝ δ = 1) (heδ : e ∈ δ) (he : e ≠ 0)
    (htile : TilesOn K T Set.univ) (hR : 0 < R)
    (hin : ∀ q ∈ Set.Ioo (0 : ℝ) R,
      v - q • e ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
    (hout : ∀ q ∈ Set.Ioo (0 : ℝ) R,
      v + q • e ∉ ⋃ t : T, (t : Plane) +ᵥ frontier K.support)
    (u : T) (huFront : v ∈ frontier ((u : Plane) +ᵥ K.support))
    (r : ℝ) (hr : 0 < r)
    (huOut : ∀ q ∈ Set.Ioo (0 : ℝ) r,
      v + q • e ∈ (u : Plane) +ᵥ K.openCarrier)
    (hnonvertex : v ∉ (u : Plane) +ᵥ vertexSet K.support) :
    ∃ η : Submodule ℝ Plane, Module.finrank ℝ η = 1 ∧
      HasBoundaryDirection K η ∧ η ≠ δ ∧
      ∃ s ∈ T, v ∈ (s : Plane) +ᵥ vertexSet K.support ∧
        ProperEdgeContactAlong K η (u : Plane) (s : Plane) ∧
          ∃ a b : Plane, a ≠ b ∧ b - a ∈ η ∧
            segment ℝ a b ⊆ frontier ((u : Plane) +ᵥ K.support) ∧
              v ∈ openSegment ℝ a b := by
  classical
  let x : Plane := v - (u : Plane)
  have hxfront : x ∈ frontier K.support := by
    have hx := huFront
    rw [frontier, Set.mem_sdiff] at hx ⊢
    rcases hx with ⟨hcl, hnot⟩
    have hcl' : x ∈ closure K.support := by
      simpa only [closure_vadd, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, neg_add_eq_sub, x] using hcl
    have hnot' : x ∉ interior K.support := by
      simpa only [interior_vadd, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, neg_add_eq_sub, x] using hnot
    constructor
    · exact hcl'
    · exact hnot'
  have hxnotvertex : x ∉ vertexSet K.support := by
    intro hx
    apply hnonvertex
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [x, vadd_eq_add, sub_eq_add_neg, add_comm] using hx
  obtain ⟨F, hF, hcover⟩ :=
    Tiling.IsPolygonal.exists_finite_intrinsic_boundarySegments K.isPolygonal
  have hxcover : x ∈ ⋃ p ∈ F, segment ℝ p.1 p.2 := by
    rw [← hcover]
    exact hxfront
  obtain ⟨p, hp'⟩ := Set.mem_iUnion.mp hxcover
  obtain ⟨hp, hxseg⟩ := Set.mem_iUnion.mp hp'
  let a : Plane := p.1
  let b : Plane := p.2
  obtain ⟨hne, ha, hb, hseg⟩ := hF p hp
  have hxa : x ≠ a := by
    intro h
    apply hxnotvertex
    rw [h]
    exact ha
  have hxb : x ≠ b := by
    intro h
    apply hxnotvertex
    rw [h]
    exact hb
  have hxopen : x ∈ openSegment ℝ a b :=
    mem_openSegment_of_ne_left_right hxa.symm hxb.symm hxseg
  let η : Submodule ℝ Plane := Submodule.span ℝ ({b - a} : Set Plane)
  have hηdir : HasBoundaryDirection K η := by
    refine ⟨a, b, hne, hseg, ?_⟩
    rfl
  have hηrank : Module.finrank ℝ η = 1 := by
    have hba : b - a ≠ (0 : Plane) := by
      intro h
      apply hne
      simpa [a, b] using (sub_eq_zero.mp h).symm
    simpa [η] using (finrank_span_singleton (K := ℝ) (v := b - a) hba)
  have heη : e ∉ η := by
    simpa [η] using endpoint_outgoing_notAlongEdge K (u : Plane) v x e r a b
      hne rfl hxopen hseg hr huOut
  have hηδ : η ≠ δ := by
    intro hEq
    exact heη (hEq ▸ heδ)
  refine ⟨η, hηrank, hηdir, hηδ, ?_⟩
  · /- Use the finite incident-edge family to choose a complementary angular
       cone, prove by connectedness and packing that it has one owner, and show
       its radial boundary segment is original contact. The incoming ray then
       forces this owner to have a proper vertex at `v`. -/
    have hηw : η = Submodule.span ℝ ({b - a} : Set Plane) := by rfl
    obtain ⟨ψ, hψe, hψw⟩ := endpoint_transverseFunctional η e (b - a) hηw heη
      (sub_ne_zero.mpr hne.symm)
    obtain ⟨ρ, hρ, G, hGvalid, hGcover⟩ :=
      endpoint_localFiniteBoundaryStar K T htile.2.1 v
    let F : Finset (Submodule ℝ Plane) := G.image fun z =>
      Submodule.span ℝ ({z.2.2 - z.2.1} : Set Plane)
    have hFrank : ∀ α ∈ F, Module.finrank ℝ α = 1 := by
      intro α hα
      obtain ⟨z, hzG, rfl⟩ := Finset.mem_image.mp hα
      have hzneq := (hGvalid z hzG).2.1
      simpa using finrank_span_singleton (K := ℝ)
        (v := z.2.2 - z.2.1) (sub_ne_zero.mpr hzneq.symm)
    obtain ⟨E, hE⟩ := endpoint_finiteTransverseExceptions ψ e (b - a)
      hψe hψw (sub_ne_zero.mpr hne.symm) F hFrank
    let M : ℝ := (∑ t ∈ E, |t|) + 1
    have hsum : 0 ≤ ∑ t ∈ E, |t| := by positivity
    have hMpos : 0 < M := by dsimp [M]; linarith
    have hMbound : ∀ t ∈ E, t < M := by
      intro t ht
      dsimp [M]
      calc
        t ≤ |t| := le_abs_self _
        _ ≤ ∑ x ∈ E, |x| := Finset.single_le_sum
          (fun x hx => abs_nonneg x) ht
        _ < (∑ x ∈ E, |x|) + 1 := by linarith
    have hAvoidTail : ∀ z ∈ G, ∀ t, M < t →
        -e + t • (b - a) ∉ Submodule.span ℝ ({z.2.2 - z.2.1} : Set Plane) := by
      intro z hz t ht hmem
      apply hE t ?_ (Submodule.span ℝ ({z.2.2 - z.2.1} : Set Plane))
        (Finset.mem_image.mpr ⟨z, hz, rfl⟩) hmem
      intro hte
      have hbound := hMbound t hte
      linarith
    obtain ⟨ρEdge, hρEdge, hclear⟩ := endpoint_localEdgeClearance v T G
    let ρ₀ : ℝ := min ρ (min ρEdge 1)
    have hρ₀ : 0 < ρ₀ := by
      dsimp [ρ₀]
      exact lt_min hρ (lt_min hρEdge (by norm_num))
    let B : ℝ := ‖e‖ / M + ‖b - a‖ + 1
    have hB : 0 < B := by dsimp [B]; positivity
    let c : ℝ := ρ₀ / (2 * B)
    have hc : 0 < c := by dsimp [c]; positivity
    let W : Set Plane := (fun p : ℝ × ℝ => v - p.1 • e + p.2 • (b - a)) ''
      {p : ℝ × ℝ | 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c}
    obtain ⟨hWconn, hWne⟩ := endpoint_complementaryWedge_connected v e (b - a) M c
      hMpos hc
    have hWbound : ∀ y ∈ W, y ∈ Metric.ball v ρ₀ := by
      intro y hy
      change y ∈ (fun p : ℝ × ℝ => v - p.1 • e + p.2 • (b - a)) ''
        {p : ℝ × ℝ | 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c} at hy
      obtain ⟨⟨q, z⟩, hqz, rfl⟩ := hy
      have hq : 0 < q := hqz.1
      have hz : M * q < z := hqz.2.1
      have hzpos : 0 < z := lt_trans (mul_pos hMpos hq) hz
      have hqle : q ≤ z / M := (le_div_iff₀ hMpos).2 (by nlinarith)
      rw [Metric.mem_ball, dist_eq_norm]
      have hnorm : ‖(v - q • e + z • (b - a)) - v‖ ≤
          q * ‖e‖ + z * ‖b - a‖ := by
        calc
          ‖(v - q • e + z • (b - a)) - v‖ = ‖-q • e + z • (b - a)‖ := by
            congr 1 <;> module
          _ ≤ ‖-q • e‖ + ‖z • (b - a)‖ := norm_add_le _ _
          _ = q * ‖e‖ + z * ‖b - a‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_neg, abs_of_pos hq, abs_of_pos hzpos]
      have hnorm' : q * ‖e‖ + z * ‖b - a‖ ≤
          z * (‖e‖ / M + ‖b - a‖) := by
        calc
          q * ‖e‖ + z * ‖b - a‖ ≤ (z / M) * ‖e‖ + z * ‖b - a‖ :=
            add_le_add (mul_le_mul_of_nonneg_right hqle (norm_nonneg e)) (le_refl _)
          _ = z * (‖e‖ / M + ‖b - a‖) := by ring
      have hfinal : z * (‖e‖ / M + ‖b - a‖) < ρ₀ := by
        calc
          z * (‖e‖ / M + ‖b - a‖) < z * B := by
            exact mul_lt_mul_of_pos_left (by dsimp [B]; linarith) hzpos
          _ < c * B := mul_lt_mul_of_pos_right hqz.2.2 hB
          _ = ρ₀ / 2 := by dsimp [c]; field_simp
          _ < ρ₀ := by linarith
      exact lt_of_le_of_lt (hnorm.trans hnorm') hfinal
    have hGcover₀ : ∀ t : T, ∀ y ∈ Metric.ball v ρ₀,
        y ∈ frontier ((t : Plane) +ᵥ K.support) →
          ∃ p, (t, p) ∈ G ∧ y ∈ segment ℝ ((t : Plane) + p.1) ((t : Plane) + p.2) := by
      intro t y hy hf
      exact hGcover t y (Metric.ball_subset_ball (min_le_left _ _) hy) hf
    have hclear₀ : ∀ z ∈ G, ∀ y ∈ Metric.ball v ρ₀,
        y ∈ segment ℝ (z.1 + z.2.1) (z.1 + z.2.2) →
          v ∈ segment ℝ (z.1 + z.2.1) (z.1 + z.2.2) ∧
            y - v ∈ Submodule.span ℝ ({z.2.2 - z.2.1} : Set Plane) := by
      intro z hz y hy hs
      have hρ₀edge : ρ₀ ≤ ρEdge := by
        dsimp [ρ₀]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      exact hclear z hz y (Metric.ball_subset_ball hρ₀edge hy) hs
    have hWnoFront : ∀ y ∈ W, ∀ t : T,
        y ∉ frontier ((t : Plane) +ᵥ K.support) := by
      apply endpoint_complementaryWedge_noFrontier K T v e (b - a) M c ρ₀
        G hGcover₀ hclear₀ hAvoidTail
      intro y hy
      exact hWbound y hy
    have hρ₀1 : ρ₀ ≤ 1 := by
      dsimp [ρ₀]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hWball1 : W ⊆ Metric.ball v 1 := by
      intro y hy
      exact Metric.ball_subset_ball hρ₀1 (hWbound y hy)
    obtain ⟨s, hsW⟩ := endpoint_connected_wedge_has_owner K T v W
      htile.2.1 htile hWconn hWnoFront hWball1
    have hsPositiveSupport : ∀ z ∈ Set.Ioo (0 : ℝ) c,
        v + z • (b - a) ∈ (s : Plane) +ᵥ K.support := by
      apply endpoint_wedge_owner_contains_positive_edge_in_support
        K T v e (b - a) M c s hMpos hc
      simpa [W] using hsW
    rw [openSegment_eq_image_lineMap] at hxopen
    obtain ⟨θ, hθ, hxline⟩ := hxopen
    let d : ℝ := min c ((1 - θ) / 2)
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min hc (by linarith [hθ.2])
    have hdc : d ≤ c := by dsimp [d]; exact min_le_left _ _
    have hfrontVadd : frontier ((u : Plane) +ᵥ K.support) =
        (u : Plane) +ᵥ frontier K.support := by
      ext y
      rw [frontier, closure_vadd, interior_vadd]
      simp only [frontier, Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem]
    have huPositiveFrontier : ∀ z ∈ Set.Ioo (0 : ℝ) d,
        v + z • (b - a) ∈ frontier ((u : Plane) +ᵥ K.support) := by
      intro z hz
      have hztheta : θ + z ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · linarith [hθ.1, hz.1]
        · have hzsmall : z < (1 - θ) / 2 := lt_of_lt_of_le hz.2 (min_le_right _ _)
          linarith [hθ.2]
      have hlineShift : AffineMap.lineMap a b (θ + z) =
          AffineMap.lineMap a b θ + z • (b - a) := by
        simp only [AffineMap.lineMap_apply_module]
        module
      have hpoint : (u : Plane) + AffineMap.lineMap a b (θ + z) =
          v + z • (b - a) := by
        rw [hlineShift, hxline]
        dsimp [x]
        module
      have hbase : - (u : Plane) + (v + z • (b - a)) =
          AffineMap.lineMap a b (θ + z) := by
        rw [← hpoint]
        module
      rw [hfrontVadd]
      apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
      change - (u : Plane) + (v + z • (b - a)) ∈ frontier K.support
      rw [hbase]
      exact hseg (lineMap_mem_segment ℝ a b hztheta)
    have hsPositiveFrontier : ∀ z ∈ Set.Ioo (0 : ℝ) d,
        v + z • (b - a) ∈ frontier ((s : Plane) +ᵥ K.support) := by
      apply endpoint_wedge_point_is_frontier_of_actual_owner
        K T v e (b - a) M c d u s htile.2.1 hMpos hc hd hdc
      · simpa [W] using hsW
      · exact huPositiveFrontier
    have hw : b - a ≠ (0 : Plane) := sub_ne_zero.mpr hne.symm
    have hηw : b - a ∈ η := Submodule.subset_span (by simp [η])
    have hproper : ProperEdgeContactAlong K η (u : Plane) (s : Plane) :=
      endpoint_actual_wedge_gives_proper_edge_contact K η (u : Plane) (s : Plane)
        v (b - a) d hw hηw hd huPositiveFrontier hsPositiveFrontier
    have hvSupport : v ∈ (s : Plane) +ᵥ K.support := by
      rw [← (K.isPolygonal.isClosed.vadd (s : Plane)).closure_eq, Metric.mem_closure_iff]
      intro ε hε
      let z : ℝ := min (d / 2) (ε / (2 * (‖b - a‖ + 1)))
      have hz : 0 < z := by
        dsimp [z]
        exact lt_min (by linarith [hd]) (by positivity)
      have hzd : z < d := by
        have : z ≤ d / 2 := by dsimp [z]; exact min_le_left _ _
        linarith
      have hzε : z * ‖b - a‖ < ε := by
        have hz' : z ≤ ε / (2 * (‖b - a‖ + 1)) := by
          dsimp [z]
          exact min_le_right _ _
        have hnonneg : 0 ≤ ‖b - a‖ := norm_nonneg _
        have hfrac : ‖b - a‖ / (2 * (‖b - a‖ + 1)) ≤ (1 : ℝ) / 2 := by
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (‖b - a‖ + 1))).2
          nlinarith
        have hle : z * ‖b - a‖ ≤ ε / 2 := by
          calc
            z * ‖b - a‖ ≤ (ε / (2 * (‖b - a‖ + 1))) * ‖b - a‖ :=
              mul_le_mul_of_nonneg_right hz' hnonneg
            _ = ε * (‖b - a‖ / (2 * (‖b - a‖ + 1))) := by ring
            _ ≤ ε * ((1 : ℝ) / 2) := mul_le_mul_of_nonneg_left hfrac hε.le
            _ = ε / 2 := by ring
        linarith
      have hdist : dist v (v + z • (b - a)) = z * ‖b - a‖ := by
        rw [dist_eq_norm]
        have hsub : v - (v + z • (b - a)) = -z • (b - a) := by module
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hz]
      refine ⟨v + z • (b - a), hsPositiveSupport z ⟨hz, lt_of_lt_of_le hzd hdc⟩, ?_⟩
      rw [hdist]
      exact hzε
    have hvNotInteriorS : v ∉ interior ((s : Plane) +ᵥ K.support) := by
      intro hvint
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior v hvint
      let q : ℝ := min (R / 2) (ε / (2 * (‖e‖ + 1)))
      have hq : 0 < q := by
        dsimp [q]
        exact lt_min (by linarith [hR]) (by positivity)
      have hqR : q < R := by
        have : q ≤ R / 2 := by dsimp [q]; exact min_le_left _ _
        linarith
      have hdist : dist v (v - q • e) = q * ‖e‖ := by
        rw [dist_eq_norm]
        have hsub : v - (v - q • e) = q • e := by module
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
      have hqball : v - q • e ∈ Metric.ball v ε := by
        rw [Metric.mem_ball]
        have hdist' : dist (v - q • e) v = q * ‖e‖ := by
          rw [dist_eq_norm]
          have hsub : (v - q • e) - v = -q • e := by module
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hq]
        rw [hdist']
        have hq' : q ≤ ε / (2 * (‖e‖ + 1)) := by
          dsimp [q]
          exact min_le_right _ _
        have hfrac : ‖e‖ / (2 * (‖e‖ + 1)) ≤ (1 : ℝ) / 2 := by
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (‖e‖ + 1))).2
          nlinarith [norm_nonneg e]
        have hle : q * ‖e‖ ≤ ε / 2 := by
          calc
            q * ‖e‖ ≤ (ε / (2 * (‖e‖ + 1))) * ‖e‖ :=
              mul_le_mul_of_nonneg_right hq' (norm_nonneg _)
            _ = ε * (‖e‖ / (2 * (‖e‖ + 1))) := by ring
            _ ≤ ε * ((1 : ℝ) / 2) := mul_le_mul_of_nonneg_left hfrac hε.le
            _ = ε / 2 := by ring
        linarith
      have hpointInterior : v - q • e ∈ interior ((s : Plane) +ᵥ K.support) :=
        hball hqball
      have hpointOpen : v - q • e ∈ (s : Plane) +ᵥ K.openCarrier := by
        simpa [interior_vadd, PolygonalRegion.openCarrier] using hpointInterior
      obtain ⟨t, htfront⟩ := Set.mem_iUnion.mp (hin q ⟨hq, hqR⟩)
      have hfrontT : frontier ((t : Plane) +ᵥ K.support) =
          (t : Plane) +ᵥ frontier K.support := by
        simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
          ((Homeomorph.addLeft (t : Plane)).image_frontier K.support).symm
      have htfront' : v - q • e ∈ frontier ((t : Plane) +ᵥ K.support) := by
        rw [hfrontT]
        exact htfront
      exact endpoint_openCarrier_avoids_allFrontiers K T htile.2.1 s t
        (v - q • e) hpointOpen htfront'
    have hvFrontierS : v ∈ frontier ((s : Plane) +ᵥ K.support) := by
      rw [(K.isPolygonal.vadd (s : Plane)).isClosed.frontier_eq]
      exact ⟨hvSupport, hvNotInteriorS⟩
    refine ⟨s, s.2, ?_, hproper, ?_⟩
    · by_contra hnotvertex
      have hnotvertex' : v ∉ vertexSet ((s : Plane) +ᵥ K.support) := by
        rw [vertexSet_vadd]
        exact hnotvertex
      have hstraight :=
        (K.isPolygonal.vadd (s : Plane)).boundaryLocallyStraightAt_of_not_mem_vertexSet
          hvFrontierS hnotvertex'
      obtain ⟨L, hvL, hLdim, hlocal⟩ := hstraight
      obtain ⟨rL, hrL, hgerm⟩ := Metric.eventually_nhds_iff.mp hlocal
      let zL : ℝ := min (d / 2) (rL / (2 * (‖b - a‖ + 1)))
      have hzL : 0 < zL := by
        dsimp [zL]
        exact lt_min (by linarith [hd]) (by positivity)
      have hzLd : zL < d := by
        have hzL' : zL ≤ d / 2 := by dsimp [zL]; exact min_le_left _ _
        linarith
      have hzLr : dist v (v + zL • (b - a)) < rL := by
        rw [dist_eq_norm]
        have hsub : v - (v + zL • (b - a)) = -zL • (b - a) := by module
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hzL]
        have hbound : zL * ‖b - a‖ ≤ rL / 2 := by
          have hzL' : zL ≤ rL / (2 * (‖b - a‖ + 1)) := by
            dsimp [zL]
            exact min_le_right _ _
          have hfrac : ‖b - a‖ / (2 * (‖b - a‖ + 1)) ≤ (1 : ℝ) / 2 := by
            apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (‖b - a‖ + 1))).2
            nlinarith [norm_nonneg (b - a)]
          calc
            zL * ‖b - a‖ ≤ (rL / (2 * (‖b - a‖ + 1))) * ‖b - a‖ :=
              mul_le_mul_of_nonneg_right hzL' (norm_nonneg _)
            _ = rL * (‖b - a‖ / (2 * (‖b - a‖ + 1))) := by ring
            _ ≤ rL * ((1 : ℝ) / 2) := mul_le_mul_of_nonneg_left hfrac hrL.le
            _ = rL / 2 := by ring
        linarith
      have hzFront : v + zL • (b - a) ∈ frontier ((s : Plane) +ᵥ K.support) :=
        hsPositiveFrontier zL ⟨hzL, hzLd⟩
      have hzLr' : dist (v + zL • (b - a)) v < rL := by
        simpa [dist_comm] using hzLr
      have hzLmem : v + zL • (b - a) ∈ (L : Set Plane) :=
        (hgerm hzLr').mp hzFront
      have hzDir : zL • (b - a) ∈ L.direction := by
        have hvsub := L.vsub_mem_direction hzLmem hvL
        have heq : (v + zL • (b - a)) -ᵥ v = zL • (b - a) := by
          simp [vsub_eq_sub]
        simpa [heq] using hvsub
      have hwDir : b - a ∈ L.direction := by
        have hzInv : zL⁻¹ • (zL • (b - a)) ∈ L.direction :=
          L.direction.smul_mem zL⁻¹ hzDir
        simpa [smul_smul, ne_of_gt hzL] using hzInv
      have hηle : η ≤ L.direction :=
        Submodule.span_le.mpr (by simpa [η] using hwDir)
      have hηeq : η = L.direction :=
        Submodule.eq_of_le_of_finrank_eq hηle (by rw [hηrank, hLdim])
      obtain ⟨ψ, hψcoord⟩ := AffineSubspace.exists_levelSet_coordinate L v hvL hLdim
      have hψw : ψ (b - a) = 0 := by
        have hvwL : v + (b - a) ∈ (L : Set Plane) := by
          simpa [vadd_eq_add, add_comm] using L.vadd_mem_of_mem_direction hwDir hvL
        have hcoord := (hψcoord (v + (b - a))).mp hvwL
        have hcoord' : ψ v + ψ (b - a) = ψ v + 0 := by
          simpa only [map_add, add_zero] using hcoord
        exact add_left_cancel hcoord'
      have hψe : ψ e ≠ 0 := by
        intro hzero
        have hveL : v + e ∈ (L : Set Plane) :=
          (hψcoord (v + e)).2 (by simp [map_add, hzero])
        have heDir : e ∈ L.direction := by
          have hvsub := L.vsub_mem_direction hveL hvL
          have heq : (v + e) -ᵥ v = e := by simp [vsub_eq_sub]
          simpa [heq] using hvsub
        exact heη (hηeq.symm ▸ heDir)
      have hregular : closure (interior ((s : Plane) +ᵥ K.support)) =
          (s : Plane) +ᵥ K.support := by
        rw [interior_vadd, closure_vadd, K.isPolygonal.closure_interior]
      have hboundary : ∀ y ∈ Metric.ball v rL,
          (y ∈ frontier ((s : Plane) +ᵥ K.support) ↔ ψ y = ψ v) := by
        intro y hy
        have hlocaly := hgerm (Metric.mem_ball.mp hy)
        exact hlocaly.trans (hψcoord y)
      have hclass := Tiling.local_levelSet_dichotomy ψ hrL hregular hvFrontierS hboundary
      let zW : ℝ := min (c / 2) (rL / (2 * B))
      let qW : ℝ := zW / (2 * M)
      have hzW : 0 < zW := by
        dsimp [zW]
        exact lt_min (by linarith [hc]) (by positivity)
      have hqW : 0 < qW := by dsimp [qW]; positivity
      have hMqW : M * qW < zW := by
        calc
          M * qW = zW / 2 := by
            dsimp [qW]
            field_simp [ne_of_gt hMpos]
          _ < zW := by linarith [hzW]
      let yW : Plane := v - qW • e + zW • (b - a)
      have hyW : yW ∈ W := by
        change yW ∈ (fun p : ℝ × ℝ => v - p.1 • e + p.2 • (b - a)) ''
          {p : ℝ × ℝ | 0 < p.1 ∧ M * p.1 < p.2 ∧ p.2 < c}
        refine ⟨(qW, zW), ⟨hqW, hMqW, ?_⟩, ?_⟩
        · dsimp [zW]
          exact lt_of_le_of_lt (min_le_left _ _) (by linarith [hc])
        · simp [yW]
      have hyWOpen : yW ∈ (s : Plane) +ᵥ K.openCarrier := hsW hyW
      have hyWInterior : yW ∈ interior ((s : Plane) +ᵥ K.support) := by
        simpa [interior_vadd, PolygonalRegion.openCarrier] using hyWOpen
      have hyWBall : yW ∈ Metric.ball v rL := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : yW - v = -qW • e + zW • (b - a) := by
          change (v - qW • e + zW • (b - a)) - v =
            -qW • e + zW • (b - a)
          rw [neg_smul]
          abel
        rw [hsub]
        calc
          ‖-qW • e + zW • (b - a)‖ ≤ qW * ‖e‖ + zW * ‖b - a‖ := by
            calc
              ‖-qW • e + zW • (b - a)‖ ≤ ‖-qW • e‖ + ‖zW • (b - a)‖ := norm_add_le _ _
              _ = qW * ‖e‖ + zW * ‖b - a‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_neg, abs_of_pos hqW, abs_of_pos hzW]
          _ ≤ zW * B := by
            have hqle : qW ≤ zW / M := by
              dsimp [qW]
              rw [show zW / (2 * M) = (zW / 2) / M by ring]
              apply (div_le_iff₀ hMpos).2
              field_simp [ne_of_gt hMpos]
              nlinarith [hzW]
            calc
              qW * ‖e‖ + zW * ‖b - a‖ ≤ (zW / M) * ‖e‖ + zW * ‖b - a‖ :=
                add_le_add (mul_le_mul_of_nonneg_right hqle (norm_nonneg _)) (le_refl _)
              _ = zW * (‖e‖ / M + ‖b - a‖) := by ring
              _ ≤ zW * B := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt hzW)
                dsimp [B]
                linarith
          _ ≤ rL / 2 := by
            have hzW' : zW ≤ rL / (2 * B) := by dsimp [zW]; exact min_le_right _ _
            calc
              zW * B ≤ (rL / (2 * B)) * B := mul_le_mul_of_nonneg_right hzW' (le_of_lt hB)
              _ = rL / 2 := by field_simp
          _ < rL := by linarith
      have hψyW : ψ yW - ψ v = -qW * ψ e := by
        calc
          ψ yW - ψ v = ψ (v - qW • e + zW • (b - a)) - ψ v := by rfl
          _ = (ψ v - qW * ψ e + zW * ψ (b - a)) - ψ v := by
            rw [map_add, map_sub, map_smul, map_smul]
            simp only [smul_eq_mul]
          _ = -qW * ψ e := by rw [hψw]; ring
      let qIn : ℝ := min (R / 2) (rL / (2 * (‖e‖ + 1)))
      have hqIn : 0 < qIn := by
        dsimp [qIn]
        exact lt_min (by linarith [hR]) (by positivity)
      have hqInR : qIn < R := by
        have : qIn ≤ R / 2 := by dsimp [qIn]; exact min_le_left _ _
        linarith
      have hIncomingBall : v - qIn • e ∈ Metric.ball v rL := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : v - qIn • e - v = -qIn • e := by module
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hqIn]
        have hq' : qIn ≤ rL / (2 * (‖e‖ + 1)) := by
          dsimp [qIn]
          exact min_le_right _ _
        have hfrac : ‖e‖ / (2 * (‖e‖ + 1)) ≤ (1 : ℝ) / 2 := by
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (‖e‖ + 1))).2
          nlinarith [norm_nonneg e]
        have hle : qIn * ‖e‖ ≤ rL / 2 := by
          calc
            qIn * ‖e‖ ≤ (rL / (2 * (‖e‖ + 1))) * ‖e‖ :=
              mul_le_mul_of_nonneg_right hq' (norm_nonneg _)
            _ = rL * (‖e‖ / (2 * (‖e‖ + 1))) := by ring
            _ ≤ rL * ((1 : ℝ) / 2) := mul_le_mul_of_nonneg_left hfrac hrL.le
            _ = rL / 2 := by ring
        linarith
      have hψIncoming : ψ (v - qIn • e) - ψ v = -qIn * ψ e := by
        rw [map_sub, map_smul]
        simp
      have hIncomingOpen : v - qIn • e ∈ (s : Plane) +ᵥ K.openCarrier := by
        rcases hclass with hpositive | hnegative
        · rcases hpositive with ⟨hpos, hneg⟩
          by_cases hypos : ψ v < ψ yW
          · have hinpos : ψ v < ψ (v - qIn • e) := by
              rw [← sub_pos, hψIncoming]
              rw [← sub_pos] at hypos
              rw [hψyW] at hypos
              nlinarith [hqIn, hqW]
            have hmem : v - qIn • e ∈ Metric.ball v rL ∩
                {y | ψ v < ψ y} := ⟨hIncomingBall, hinpos⟩
            have hinterior := hpos hmem
            simpa [interior_vadd, PolygonalRegion.openCarrier] using hinterior
          · have hyneg : ψ yW < ψ v := by
              have hne' : ψ yW ≠ ψ v := by
                intro heq
                have : -qW * ψ e = 0 := by rw [← hψyW, heq]; simp
                exact (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hqW)) hψe) this
              exact lt_of_le_of_ne (le_of_not_gt hypos) hne'
            have hmem : yW ∈ Metric.ball v rL ∩ {y | ψ y < ψ v} :=
              ⟨hyWBall, hyneg⟩
            have hinteriorNot := hneg hmem
            have hnotS : yW ∉ (s : Plane) +ᵥ K.support :=
              fun hs => (interior_subset hinteriorNot) hs
            exact False.elim (hnotS (interior_subset hyWInterior))
        · rcases hnegative with ⟨hpos, hneg⟩
          by_cases hypos : ψ v < ψ yW
          · have hmem : yW ∈ Metric.ball v rL ∩ {y | ψ v < ψ yW} :=
              ⟨hyWBall, hypos⟩
            have hinteriorNot := hpos hmem
            have hnotS : yW ∉ (s : Plane) +ᵥ K.support :=
              fun hs => (interior_subset hinteriorNot) hs
            exact False.elim (hnotS (interior_subset hyWInterior))
          · have hyneg : ψ yW < ψ v := by
              have hne' : ψ yW ≠ ψ v := by
                intro heq
                have : -qW * ψ e = 0 := by rw [← hψyW, heq]; simp
                exact (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hqW)) hψe) this
              exact lt_of_le_of_ne (le_of_not_gt hypos) hne'
            have hinneg : ψ (v - qIn • e) < ψ v := by
              have hepos : 0 < ψ e := by
                have hdiff : ψ yW - ψ v < 0 := sub_neg.mpr hyneg
                rw [hψyW] at hdiff
                nlinarith [hqW]
              have hdiff : ψ (v - qIn • e) - ψ v < 0 := by
                rw [hψIncoming]
                nlinarith [hqIn, hepos]
              exact sub_neg.mp hdiff
            have hmem : v - qIn • e ∈ Metric.ball v rL ∩
                {y | ψ y < ψ v} := ⟨hIncomingBall, hinneg⟩
            have hinterior := hneg hmem
            simpa [interior_vadd, PolygonalRegion.openCarrier] using hinterior
      obtain ⟨t, htfront⟩ := Set.mem_iUnion.mp (hin qIn ⟨hqIn, hqInR⟩)
      have hfrontT : frontier ((t : Plane) +ᵥ K.support) =
          (t : Plane) +ᵥ frontier K.support := by
        simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
          ((Homeomorph.addLeft (t : Plane)).image_frontier K.support).symm
      have htfront' : v - qIn • e ∈ frontier ((t : Plane) +ᵥ K.support) := by
        rw [hfrontT]
        exact htfront
      exact endpoint_openCarrier_avoids_allFrontiers K T htile.2.1 s t
        (v - qIn • e) hIncomingOpen htfront'
    · refine ⟨(u : Plane) + a, (u : Plane) + b, ?_, ?_, ?_, ?_⟩
      · intro hab
        apply hne
        exact add_left_cancel hab
      · have hdiff' : ((u : Plane) + b) - ((u : Plane) + a) = b - a := by module
        rw [hdiff']
        exact hηw
      · intro y hy
        rw [hfrontVadd]
        have hyBase : -(u : Plane) +ᵥ y ∈ segment ℝ a b := by
          have hvadd : (u : Plane) +ᵥ segment ℝ a b =
              segment ℝ ((u : Plane) + a) ((u : Plane) + b) := by
            simpa only [vadd_eq_add] using vadd_segment (𝕜 := ℝ) (u : Plane) a b
          have hyV : y ∈ (u : Plane) +ᵥ segment ℝ a b := by
            rw [← hvadd] at hy
            exact hy
          exact Set.mem_vadd_set_iff_neg_vadd_mem.mp hyV
        apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
        exact hseg hyBase
      · have hvopen : openSegment ℝ ((u : Plane) + a) ((u : Plane) + b) =
            (u : Plane) +ᵥ openSegment ℝ a b := by
          simpa only [vadd_eq_add] using (vadd_openSegment ℝ (u : Plane) a b).symm
        rw [hvopen]
        apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
        have hxopen' : x ∈ openSegment ℝ a b := by
          rw [openSegment_eq_image_lineMap]
          exact ⟨θ, hθ, hxline⟩
        simpa [x, vadd_eq_add, sub_eq_add_neg, add_comm] using hxopen'

theorem endpointRay_ownedInterior_withContact :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (v e : Plane) (R : ℝ), Module.finrank ℝ δ = 1 → e ∈ δ → e ≠ 0 →
    TilesOn K T Set.univ → 0 < R →
    (∀ q ∈ Set.Ioo (0 : ℝ) R,
      v - q • e ∈ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) →
    (∀ q ∈ Set.Ioo (0 : ℝ) R,
      v + q • e ∉ ⋃ t : T, (t : Plane) +ᵥ frontier K.support) →
      ∃ u ∈ T, v ∈ frontier (u +ᵥ K.support) ∧
        (∃ r : ℝ, 0 < r ∧ ∀ q ∈ Set.Ioo (0 : ℝ) r,
          v + q • e ∈ u +ᵥ K.openCarrier) ∧
        (v ∈ u +ᵥ vertexSet K.support ∨
          ∃ η : Submodule ℝ Plane, Module.finrank ℝ η = 1 ∧
            HasBoundaryDirection K η ∧ η ≠ δ ∧
              ∃ s ∈ T, v ∈ s +ᵥ vertexSet K.support ∧
                ProperEdgeContactAlong K η u s ∧
                  ∃ a b : Plane, a ≠ b ∧ b - a ∈ η ∧
                    segment ℝ a b ⊆ frontier (u +ᵥ K.support) ∧
                      v ∈ openSegment ℝ a b)
  := by
  intro K δ T v e R hδ heδ he htile hR hin hout
  obtain ⟨u, hu, hvfront, r, hr, hwhole⟩ :=
    endpointRay_openConclusion δ T v e R hδ heδ he htile hR hin hout
  refine ⟨u, hu, hvfront, ⟨r, hr, hwhole⟩, ?_⟩
  by_cases hvvertex : v ∈ u +ᵥ vertexSet K.support
  · exact Or.inl hvvertex
  · exact Or.inr (contactFan_nonvertex_endpoint K δ T v e R hδ heδ he htile hR hin hout
      ⟨u, hu⟩ hvfront r hr hwhole hvvertex)

end Tiling.RationalSlopes
