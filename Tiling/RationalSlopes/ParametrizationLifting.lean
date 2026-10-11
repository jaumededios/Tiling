import Tiling.RationalSlopes.RationalParametrization
import Tiling.RationalSlopes.CarrierPeriodicity
import Tiling.RationalSlopes.Approximation.FLCControl
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology

noncomputable section

namespace Tiling.Polygonal

open Tiling.RationalPolygonal (PolygonalRegion)

def ShortDifferenceReflection (P : Set Plane) (f : Plane →ₗ[ℚ] Plane) (R : ℝ) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, ∀ d ∈ P,
    dist (f a) (f b) < R → dist (f c) (f d) < R →
      f (b - a) = f (d - c) → b - a = d - c

private theorem equal_of_shared_nonzero
    {δ ε : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) (hε : Module.finrank ℝ ε = 1)
    {w : Plane} (hwδ : w ∈ δ) (hwε : w ∈ ε) (hw : w ≠ 0) : δ = ε := by
  have hspanδ : Submodule.span ℝ ({w} : Set Plane) ≤ δ :=
    Submodule.span_singleton_le_iff_mem _ _ |>.2 hwδ
  have hspanε : Submodule.span ℝ ({w} : Set Plane) ≤ ε :=
    Submodule.span_singleton_le_iff_mem _ _ |>.2 hwε
  have hfd : Module.finrank ℝ (Submodule.span ℝ ({w} : Set Plane)) = 1 :=
    finrank_span_singleton hw
  have hδeq : Submodule.span ℝ ({w} : Set Plane) = δ := by
    apply Submodule.eq_of_le_of_finrank_eq hspanδ
    rw [hfd, hδ]
  have hεeq : Submodule.span ℝ ({w} : Set Plane) = ε := by
    apply Submodule.eq_of_le_of_finrank_eq hspanε
    rw [hfd, hε]
  exact hδeq.symm.trans hεeq

private theorem finiteAngle_pair_bound
    {δ ε : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) (hε : Module.finrank ℝ ε = 1)
    (hne : δ ≠ ε) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ (a : Plane), a ∈ δ → ∀ (b : Plane), b ∈ ε →
      ‖a‖ + ‖b‖ ≤ J * ‖a - b‖ := by
  let f : (δ × ε) →ₗ[ℝ] Plane :=
    { toFun := fun p => (p.1 : Plane) - p.2
      map_add' := by
        intro p q
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro c p
        simp [smul_sub] }
  have hf : Function.Injective f := by
    intro p q hpq
    apply Prod.ext
    · apply Subtype.ext
      have hpq' : (p.1 : Plane) - (p.2 : Plane) =
          (q.1 : Plane) - (q.2 : Plane) := by simpa [f] using hpq
      have hdiff : (p.1 : Plane) - (q.1 : Plane) =
          (p.2 : Plane) - (q.2 : Plane) := by
        calc
          _ = ((p.1 : Plane) - p.2) - ((q.1 : Plane) - q.2) + (p.2 - q.2) := by abel
          _ = (p.2 : Plane) - q.2 := by rw [hpq']; abel
      by_contra hn
      have hw : (p.1 : Plane) - (q.1 : Plane) ≠ 0 := sub_ne_zero.mpr hn
      have hwδ : (p.1 : Plane) - (q.1 : Plane) ∈ δ := δ.sub_mem p.1.2 q.1.2
      have hwε : (p.1 : Plane) - (q.1 : Plane) ∈ ε := by
        rw [hdiff]
        exact ε.sub_mem p.2.2 q.2.2
      exact hne (equal_of_shared_nonzero hδ hε hwδ hwε hw)
    · apply Subtype.ext
      have hpq' : (p.1 : Plane) - (p.2 : Plane) =
          (q.1 : Plane) - (q.2 : Plane) := by simpa [f] using hpq
      have hdiff : (p.1 : Plane) - (q.1 : Plane) =
          (p.2 : Plane) - (q.2 : Plane) := by
        calc
          _ = ((p.1 : Plane) - p.2) - ((q.1 : Plane) - q.2) + (p.2 - q.2) := by abel
          _ = (p.2 : Plane) - q.2 := by rw [hpq']; abel
      by_contra hn
      have hw : (p.2 : Plane) - (q.2 : Plane) ≠ 0 := sub_ne_zero.mpr hn
      have hwε : (p.2 : Plane) - (q.2 : Plane) ∈ ε := ε.sub_mem p.2.2 q.2.2
      have hwδ : (p.2 : Plane) - (q.2 : Plane) ∈ δ := by
        rw [hdiff.symm]
        exact δ.sub_mem p.1.2 q.1.2
      exact hne (equal_of_shared_nonzero hδ hε hwδ hwε hw)
  obtain ⟨c, hcpos, hc⟩ := (LinearMap.injective_iff_antilipschitz f).mp hf
  let J : ℝ := max 1 (2 * (c : ℝ))
  refine ⟨J, le_max_left _ _, ?_⟩
  intro a ha b hb
  let p : δ × ε := ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hp := hc.le_mul_dist p 0
  have hp' : ‖a‖ ≤ (c : ℝ) * ‖a - b‖ ∧
      ‖b‖ ≤ (c : ℝ) * ‖a - b‖ := by
    simpa [dist_eq_norm, p, f] using hp
  have hJ : 2 * (c : ℝ) ≤ J := by exact le_max_right _ _
  dsimp [J]
  calc
    ‖a‖ + ‖b‖ ≤ (c : ℝ) * ‖a - b‖ + (c : ℝ) * ‖a - b‖ := add_le_add hp'.1 hp'.2
    _ = (2 * (c : ℝ)) * ‖a - b‖ := by ring
    _ ≤ max 1 (2 * (c : ℝ)) * ‖a - b‖ := by
      exact mul_le_mul_of_nonneg_right hJ (norm_nonneg _)

private theorem finiteAngle_uniform_bound
    (D : Finset (Submodule ℝ Plane))
    (hD : ∀ δ ∈ D, Module.finrank ℝ δ = 1) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ δ ∈ D, ∀ ε ∈ D, δ ≠ ε →
      ∀ (a : Plane), a ∈ δ → ∀ (b : Plane), b ∈ ε →
        ‖a‖ + ‖b‖ ≤ J * ‖a - b‖ := by
  let B : Submodule ℝ Plane → Submodule ℝ Plane → ℝ := fun δ ε =>
    if hδ : δ ∈ D then if hε : ε ∈ D then
      if hne : δ ≠ ε then
        Classical.choose (finiteAngle_pair_bound (hD δ hδ) (hD ε hε) hne)
      else 1 else 1 else 1
  let J : ℝ := max 1 (∑ δ ∈ D, ∑ ε ∈ D, B δ ε)
  refine ⟨J, le_max_left _ _, ?_⟩
  intro δ hδ ε hε hne a ha b hb
  have hbound := (Classical.choose_spec
    (finiteAngle_pair_bound (hD δ hδ) (hD ε hε) hne)).2 a ha b hb
  have hB : B δ ε = Classical.choose
      (finiteAngle_pair_bound (hD δ hδ) (hD ε hε) hne) := by
    simp [B, hδ, hε, hne]
  have hB_lower {δ' ε' : Submodule ℝ Plane}
      (hδ' : δ' ∈ D) (hε' : ε' ∈ D) : 1 ≤ B δ' ε' := by
    by_cases hne' : δ' ≠ ε'
    · have hrewrite : B δ' ε' = Classical.choose
          (finiteAngle_pair_bound (hD δ' hδ') (hD ε' hε') hne') := by
        simp [B, hδ', hε', hne']
      rw [hrewrite]
      exact (Classical.choose_spec
        (finiteAngle_pair_bound (hD δ' hδ') (hD ε' hε') hne')).1
    · have heq : δ' = ε' := by simpa [ne_eq] using hne'
      simp [B, hε', heq]
  have hinner_nonneg (δ' : Submodule ℝ Plane) (hδ' : δ' ∈ D) :
      0 ≤ ∑ ε' ∈ D, B δ' ε' := by
    apply Finset.sum_nonneg
    intro ε' hε'
    exact le_trans (by norm_num) (hB_lower hδ' hε')
  have hinner : ∑ ε' ∈ D, B δ ε' ≤ ∑ δ' ∈ D, ∑ ε' ∈ D, B δ' ε' :=
    Finset.single_le_sum (fun δ' hδ' => hinner_nonneg δ' hδ') hδ
  have hterm : B δ ε ≤ ∑ ε' ∈ D, B δ ε' :=
    Finset.single_le_sum (fun ε' hε' => le_trans (by norm_num) (hB_lower hδ hε')) hε
  have hsum : B δ ε ≤ ∑ δ' ∈ D, ∑ ε' ∈ D, B δ' ε' := hterm.trans hinner
  have hle : B δ ε ≤ J := hsum.trans (le_max_right _ _)
  rw [← hB] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))


private theorem finiteAngle_affineIntersection
    {δ ε : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1)
    (hε : Module.finrank ℝ ε = 1) (hne : δ ≠ ε) {J H : ℝ}
    (hangle : ∀ a ∈ δ, ∀ b ∈ ε, ‖a‖ + ‖b‖ ≤ J * ‖a - b‖)
    (hJ : 0 ≤ J) {t u x : Plane} (ht : dist t x ≤ H) (hu : dist u x ≤ H) :
    ∃ z : Plane, z - t ∈ δ ∧ z - u ∈ ε ∧ dist z x ≤ (2 * J + 1) * H := by
  let f : (δ × ε) →ₗ[ℝ] Plane :=
    { toFun := fun p => (p.1 : Plane) - p.2
      map_add' := by intros; simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      map_smul' := by intros; simp [smul_sub] }
  have hf : Function.Injective f := by
    intro p q hpq
    change (p.1 : Plane) - p.2 = (q.1 : Plane) - q.2 at hpq
    have hdiff : (p.1 : Plane) - q.1 = (p.2 : Plane) - q.2 := by
      linear_combination hpq
    have hz : (p.1 : Plane) - q.1 = 0 := by
      by_contra hn
      exact hne (equal_of_shared_nonzero hδ hε (δ.sub_mem p.1.2 q.1.2)
        (by rw [hdiff]; exact ε.sub_mem p.2.2 q.2.2) hn)
    apply Prod.ext
    · exact Subtype.ext (sub_eq_zero.mp hz)
    · exact Subtype.ext (sub_eq_zero.mp (hdiff.symm.trans hz))
  have hdim : Module.finrank ℝ (δ × ε) = Module.finrank ℝ Plane := by
    rw [Module.finrank_prod, hδ, hε, Complex.finrank_real_complex]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf
  obtain ⟨p, hp⟩ := hsurj (u - t)
  change (p.1 : Plane) - p.2 = u - t at hp
  have hzu : t + (p.1 : Plane) - u = p.2 := by linear_combination hp
  refine ⟨t + (p.1 : Plane), by simp, by rw [hzu]; exact p.2.2, ?_⟩
  have ha := hangle (p.1 : Plane) p.1.2 (p.2 : Plane) p.2.2
  rw [hp] at ha
  have htu : ‖u - t‖ ≤ 2 * H := by
    have htri := dist_triangle u x t
    rw [dist_comm x t, dist_eq_norm u t] at htri
    linarith
  have hzdist : dist (t + (p.1 : Plane)) x ≤ ‖(p.1 : Plane)‖ + H := by
    calc
      _ ≤ dist (t + (p.1 : Plane)) t + dist t x := dist_triangle _ _ _
      _ = ‖(p.1 : Plane)‖ + dist t x := by simp [dist_eq_norm]
      _ ≤ ‖(p.1 : Plane)‖ + H := add_le_add le_rfl ht
  have hmul := mul_le_mul_of_nonneg_left htu hJ
  nlinarith [norm_nonneg (p.2 : Plane)]

private theorem period_add_mem {S : Set Plane} {q t : Plane}
    (hq : q ∈ periodGroup S) (ht : t ∈ S) : t + q ∈ S := by
  have heq : q +ᵥ S = S := AddAction.mem_stabilizer_iff.mp hq
  rw [← heq]
  exact ⟨t, ht, by simp [add_comm]⟩

private theorem unionColumns_carrier_invariant
    {K : PolygonalRegion} {B : Set Plane} {δ : Submodule ℝ Plane}
    (hcol : IsUnionOfColumns K δ B) : IsInvariantAlong (regularSupport K B) δ := by
  have hsplit : (⋃ t : B, lineFibre δ B t) = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hx
      exact hx.1
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hx, by simp⟩
  intro u hu
  rw [← hsplit, regularSupport_iUnion]
  rw [← interior_vadd, ← closure_vadd]
  congr 2
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, hy⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨t, ?_⟩
    have hinv := (hcol t t.property).2.2.2 u hu
    rw [← hinv]
    exact ⟨y, hy, rfl⟩
  · intro hx
    obtain ⟨t, hx⟩ := Set.mem_iUnion.mp hx
    have hinv := (hcol t t.property).2.2.2 u hu
    rw [← hinv] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨y, Set.mem_iUnion.mpr ⟨t, hy⟩, hxy⟩

private theorem regularSupport_nonempty {K : PolygonalRegion} {S : Set Plane}
    (hS : S.Nonempty) : (regularSupport K S).Nonempty := by
  obtain ⟨t, ht⟩ := hS
  obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
  refine ⟨t + u, ?_⟩
  apply interior_mono (subset_closure : openUnion K S ⊆ closure (openUnion K S))
  have hopen : IsOpen (openUnion K S) := by
    apply isOpen_iUnion
    intro s
    exact isOpen_interior.vadd (s : Plane)
  rw [hopen.interior_eq]
  exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, u, hu, rfl⟩

private theorem iUnion_bool_cond (A B : Set Plane) :
    (⋃ b : Bool, cond b A B) = A ∪ B := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨b, hx⟩
    cases b
    · exact Or.inr hx
    · exact Or.inl hx
  · rintro (hx | hx)
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩

private theorem regularSupport_union (K : PolygonalRegion) (A B : Set Plane) :
    regularSupport K (A ∪ B) =
      interior (closure (regularSupport K A ∪ regularSupport K B)) := by
  have hs : (fun b : Bool => regularSupport K (cond b A B)) =
      (fun b : Bool => cond b (regularSupport K A) (regularSupport K B)) := by
    funext b
    cases b <;> rfl
  have hh := regularSupport_iUnion K (fun b : Bool => cond b A B)
  rwa [iUnion_bool_cond, hs, iUnion_bool_cond] at hh

private theorem polygonalRegion_eq_of_support_eq {K Q : PolygonalRegion}
    (h : K.support = Q.support) : K = Q := by
  cases K
  cases Q
  cases h
  rfl

private theorem regularSupport_germ_of_local_centres
    {K : PolygonalRegion} {A B : Set Plane} {v : Plane} {M : ℝ}
    (hbound : K.support ⊆ Metric.closedBall 0 M)
    (hpB : IsPacking K.prototileFamily (K.placements B)) (hAB : A ⊆ B)
    (hlocal : ∀ t ∈ B, dist t v < M + 1 → t ∈ A) :
    regularSupport K A =ᶠ[𝓝 v] regularSupport K B := by
  have hpA : IsPacking K.prototileFamily (K.placements A) := hpB.mono (fun _ ht => hAB ht)
  have hclosed : closure (openUnion K A) =ᶠ[𝓝 v] closure (openUnion K B) := by
    rw [closure_openUnion_eq_iUnion_support hpA, closure_openUnion_eq_iUnion_support hpB]
    filter_upwards [Metric.ball_mem_nhds v (by norm_num : (0 : ℝ) < 1)] with x hx
    apply propext
    change (x ∈ ⋃ t : A, (t : Plane) +ᵥ K.support) ↔
      (x ∈ ⋃ t : B, (t : Plane) +ᵥ K.support)
    constructor
    · intro h
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp h
      exact Set.mem_iUnion.mpr ⟨⟨t, hAB t.property⟩, ht⟩
    · intro h
      obtain ⟨t, u, hu, hxu⟩ := Set.mem_iUnion.mp h
      have huM : ‖u‖ ≤ M := by simpa [Metric.mem_closedBall, dist_eq_norm] using hbound hu
      have htx : dist (t : Plane) x ≤ M := by
        rw [← hxu]
        simpa [vadd_eq_add, dist_eq_norm] using huM
      have htv : dist (t : Plane) v < M + 1 :=
        lt_of_le_of_lt (dist_triangle _ x _) (add_lt_add_of_le_of_lt htx hx)
      exact Set.mem_iUnion.mpr ⟨⟨t, hlocal t t.property htv⟩, u, hu, hxu⟩
  filter_upwards [eventually_eventually_nhds.mpr hclosed] with x hx
  apply propext
  have hxt : closure (openUnion K A) =ᶠ[𝓝 x] closure (openUnion K B) := hx
  exact hxt.mem_interior_iff

private theorem localFibreMembership
    {K : Tiling.RationalPolygonal.PolygonalRegion} {T S : Set Plane}
    {δ : Submodule ℝ Plane} {x : Plane} {R B : ℝ}
    (hpT : Tiling.IsPacking K.prototileFamily (K.placements T))
    (hST : S ⊆ T) (_hline : IsLineSupported S δ)
    (hbound : K.support ⊆ Metric.closedBall 0 B)
    (_hB : 0 < B) (_hR : 0 < R)
    (hsat : LocallySaturatedAlong (regularSupport K S) δ x R)
    {t : Plane} (ht : t ∈ S) (htclose : dist t x + B < R)
    {u : Plane} (huT : u ∈ T) (hutδ : u - t ∈ δ)
    (huclose : dist u x + B < R) : u ∈ S := by
  by_contra huS
  obtain ⟨a, ha⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have haK : a ∈ K.support := interior_subset ha
  have haBound : dist a 0 ≤ B := hbound haK
  have hopenUnion (V : Set Plane) : IsOpen (openUnion K V) := by
    change IsOpen (⋃ s : V, (s : Plane) +ᵥ interior K.support)
    apply isOpen_iUnion
    intro s
    exact (Homeomorph.addLeft (s : Plane)).isOpen_image.mpr isOpen_interior
  have htopen : t + a ∈ openUnion K S := by
    rw [openUnion]
    refine mem_iUnion.mpr ⟨⟨t, ht⟩, ?_⟩
    rw [mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, add_assoc, add_left_comm, add_comm,
      Tiling.RationalPolygonal.PolygonalRegion.openCarrier] using ha
  have htCarrier : t + a ∈ regularSupport K S :=
    (hopenUnion S).subset_interior_closure htopen
  have huclose' : dist (u + a) x < R := by
    calc
      dist (u + a) x ≤ dist (u + a) u + dist u x := dist_triangle _ _ _
      _ = dist a 0 + dist u x := by simp [dist_eq_norm]
      _ ≤ B + dist u x := add_le_add_left haBound _
      _ < R := by nlinarith [huclose]
  have htclose' : dist (t + a) x < R := by
    calc
      dist (t + a) x ≤ dist (t + a) t + dist t x := dist_triangle _ _ _
      _ = dist a 0 + dist t x := by simp [dist_eq_norm]
      _ ≤ B + dist t x := add_le_add_left haBound _
      _ < R := by nlinarith [htclose]
  have hlocal := hsat (t + a) (Metric.mem_ball.mpr htclose')
    (u + a) (Metric.mem_ball.mpr huclose') (by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hutδ)
  have huSupport : u + a ∈ regularSupport K S := hlocal.mp htCarrier
  have huOpen : u + a ∈ openUnion K ({u} : Set Plane) := by
    rw [openUnion]
    refine mem_iUnion.mpr ⟨⟨u, by simp⟩, ?_⟩
    rw [mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, add_assoc, add_left_comm, add_comm,
      Tiling.RationalPolygonal.PolygonalRegion.openCarrier] using ha
  have huCarrier : u + a ∈ regularSupport K ({u} : Set Plane) :=
    (hopenUnion {u}).subset_interior_closure huOpen
  have huSingleton : {u} ⊆ T := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact huT
  have hdisj : Disjoint S ({u} : Set Plane) := by
    rw [Set.disjoint_left]
    intro z hzS hzu
    rw [Set.mem_singleton_iff] at hzu
    subst z
    exact huS hzS
  have hregularDisjoint := regularSupport_disjoint_of_disjoint_subfamilies
    hpT hST huSingleton hdisj
  exact (Set.disjoint_left.mp hregularDisjoint) huSupport huCarrier


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
    change ‖(‖v‖⁻¹ : ℝ) • v‖ = 1
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
      simp [q, dist_eq_norm, hwNorm, abs_of_pos hε]
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


private theorem frontier_near_centre_of_supportBound
    {K : PolygonalRegion} {S : Set Plane} {B : ℝ}
    (hbound : K.support ⊆ Metric.closedBall 0 B)
    (hp : IsPacking K.prototileFamily (K.placements S))
    {v : Plane} (hv : v ∈ frontier (regularSupport K S)) :
    ∃ u ∈ S, dist u v ≤ B := by
  have hvclosed : v ∈ closure (openUnion K S) :=
    ((closure_mono interior_subset).trans_eq closure_closure) (frontier_subset_closure hv)
  rw [closure_openUnion_eq_iUnion_support hp] at hvclosed
  obtain ⟨u, a, ha, hvu⟩ := Set.mem_iUnion.mp hvclosed
  refine ⟨u, u.property, ?_⟩
  have haB := hbound ha
  rw [← hvu]
  simpa [Metric.mem_closedBall, vadd_eq_add, dist_eq_norm, norm_neg] using haB

private theorem translated_openCarrier_mem_regularSupport
    {K : PolygonalRegion} {S : Set Plane} {t a : Plane}
    (ht : t ∈ S) (ha : a ∈ K.openCarrier) : t + a ∈ regularSupport K S := by
  have hopen : IsOpen (openUnion K S) := by
    apply isOpen_iUnion
    intro s
    exact isOpen_interior.vadd (s : Plane)
  exact hopen.subset_interior_closure (Set.mem_iUnion.mpr ⟨⟨t, ht⟩, a, ha, rfl⟩)

private theorem locallySaturated_disjointCarriers_parallel
    {K : PolygonalRegion} {T S U : Set Plane} {δ ε : Submodule ℝ Plane}
    {x t u : Plane} {B H J : ℝ}
    (hδ : Module.finrank ℝ δ = 1) (hε : Module.finrank ℝ ε = 1)
    (hJ : 1 ≤ J) (hH : 0 ≤ H)
    (hangle : ∀ a ∈ δ, ∀ b ∈ ε, ‖a‖ + ‖b‖ ≤ J * ‖a - b‖)
    (hbound : K.support ⊆ Metric.closedBall 0 B)
    (hp : IsPacking K.prototileFamily (K.placements T))
    (hST : S ⊆ T) (hUT : U ⊆ T) (hdisj : Disjoint S U)
    (hsatS : LocallySaturatedAlong (regularSupport K S) δ x ((2 * J + 1) * H + B + 1))
    (hsatU : LocallySaturatedAlong (regularSupport K U) ε x ((2 * J + 1) * H + B + 1))
    (ht : t ∈ S) (hu : u ∈ U) (htx : dist t x ≤ H) (hux : dist u x ≤ H) : δ = ε := by
  by_contra hne
  obtain ⟨z, hzt, hzu, hzx⟩ := finiteAngle_affineIntersection hδ hε hne hangle
    (by linarith) htx hux
  obtain ⟨a, ha⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have haB : ‖a‖ ≤ B := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hbound (interior_subset ha)
  have hshift (w : Plane) : dist (w + a) x ≤ dist w x + B := by
    calc
      _ ≤ dist (w + a) w + dist w x := dist_triangle _ _ _
      _ = ‖a‖ + dist w x := by simp [dist_eq_norm]
      _ ≤ dist w x + B := by linarith
  have htball : t + a ∈ Metric.ball x ((2 * J + 1) * H + B + 1) := by
    apply Metric.mem_ball.mpr
    have hh := hshift t
    nlinarith
  have huball : u + a ∈ Metric.ball x ((2 * J + 1) * H + B + 1) := by
    apply Metric.mem_ball.mpr
    have hh := hshift u
    nlinarith
  have hzball : z + a ∈ Metric.ball x ((2 * J + 1) * H + B + 1) := by
    apply Metric.mem_ball.mpr
    linarith [hshift z]
  have hzS : z + a ∈ regularSupport K S :=
    (hsatS (t + a) htball (z + a) hzball (by simpa using hzt)).mp
      (translated_openCarrier_mem_regularSupport ht ha)
  have hzU : z + a ∈ regularSupport K U :=
    (hsatU (u + a) huball (z + a) hzball (by simpa using hzu)).mp
      (translated_openCarrier_mem_regularSupport hu ha)
  exact Set.disjoint_left.mp
    (regularSupport_disjoint_of_disjoint_subfamilies hp hST hUT hdisj) hzS hzU

private theorem cornerFree_sliceAtom_localSaturation
    {K : PolygonalRegion} (F : Finset (Plane × Plane)) (L : ℝ) (hL : 0 ≤ L)
    (hfrontier : frontier K.support = ⋃ e ∈ F, segment ℝ e.1 e.2)
    (hlength : (∑ e ∈ F, dist e.1 e.2) ≤ L)
    {δ : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1)
    {T S : Set Plane} (hpT : IsPacking K.prototileFamily (K.placements T))
    (hST : S ⊆ T) (hline : IsLineSupported S δ) {x : Plane} {R C : ℝ}
    (hR : 0 < R) (hmargin : R + L + 1 ≤ C)
    (hno : ∀ v ∈ properVertices (regularSupport K S), ¬dist x v < C) :
    LocallySaturatedAlong (regularSupport K S) δ x R := by
  apply noCornerLineCarrier_localSaturation_of_boundaryLength F L hL hfrontier hlength hδ
    (hpT.mono (fun _ ht => hST ht)) hline hR
  apply Set.disjoint_left.mpr
  intro v hv hball
  apply hno v hv
  exact lt_of_lt_of_le (by simpa only [Metric.mem_ball, dist_comm] using hball) hmargin

private theorem lattice_combination_ne_zero (L : PlanarLattice) (k l : ℤ)
    (hk : k ≠ 0) : k • L.basis 0 + l • L.basis 1 ≠ 0 := by
  intro hz
  have heq : ∑ j : Fin 2, ![(k : ℝ), (l : ℝ)] j • L.basis j = 0 := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Int.cast_smul_eq_zsmul] using hz
  have hkzero := (Fintype.linearIndependent_iff.mp L.independent)
    ![(k : ℝ), (l : ℝ)] heq 0
  simp only [Matrix.cons_val_zero] at hkzero
  exact hk (by exact_mod_cast hkzero)

private theorem lattice_transverse_of_combination_mem (L : PlanarLattice)
    {δ : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1) (k l : ℤ)
    (hk : k ≠ 0) (hwithin : k • L.basis 0 + l • L.basis 1 ∈ δ) :
    L.basis 1 ∉ δ := by
  intro hgamma
  have hlam : L.basis 0 ∈ δ := by
    have hs := δ.sub_mem hwithin (δ.toAddSubgroup.zsmul_mem hgamma l)
    have hs' : (k : ℝ) • L.basis 0 ∈ δ := by
      simpa only [add_sub_cancel_right, Int.cast_smul_eq_zsmul] using hs
    exact (δ.smul_mem_iff (by exact_mod_cast hk : (k : ℝ) ≠ 0)).mp hs'
  have hle : Submodule.span ℝ (Set.range L.basis) ≤ δ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact hlam
    · exact hgamma
  have hdim := Submodule.finrank_mono hle
  rw [finrank_span_eq_card L.independent, Fintype.card_fin, hδ] at hdim
  omega

/-- Reflect short edges of the actual complete-line graph, not arbitrary real lines. -/
private theorem lineSupported_of_shortImageGraph
    {S : Set Plane} {δ : Submodule ℝ Plane} (f : Plane →ₗ[ℚ] Plane) {G : ℝ}
    (hinj : Set.InjOn f S) (hgraph : ShortEdgeConnected (f '' S) G)
    (himage : IsLineSupported (f '' S) δ)
    (hreflect : ∀ a ∈ S, ∀ b ∈ S, dist (f a) (f b) < G →
      f b - f a ∈ δ → b - a ∈ δ) : IsLineSupported S δ := by
  classical
  by_cases hSne : S.Nonempty
  · obtain ⟨w, hw⟩ := hSne
    let pre : Plane → Plane := fun x =>
      if hx : x ∈ f '' S then Classical.choose hx else 0
    have pre_spec : ∀ x ∈ f '' S, pre x ∈ S ∧ f (pre x) = x := by
      intro x hx
      simpa only [pre, dif_pos hx] using Classical.choose_spec hx
    have pre_image : ∀ s ∈ S, pre (f s) = s := by
      intro s hs
      have hpre := pre_spec (f s) (Set.mem_image_of_mem f hs)
      exact hinj hpre.1 hs hpre.2
    obtain ⟨anchor, hanchor⟩ := himage
    have paths : ∀ a b : Plane,
        Relation.EqvGen (fun x y : Plane =>
          x ∈ f '' S ∧ y ∈ f '' S ∧ dist x y < G) a b → pre b - pre a ∈ δ := by
      intro a b hpath
      induction hpath with
      | rel a b hab =>
          have ha := pre_spec a hab.1
          have hb := pre_spec b hab.2.1
          apply hreflect (pre a) ha.1 (pre b) hb.1
            (by simpa only [ha.2, hb.2] using hab.2.2)
          have hdiff := δ.sub_mem (hanchor b hab.2.1) (hanchor a hab.1)
          simpa only [ha.2, hb.2, sub_sub_sub_cancel_right] using hdiff
      | refl a => simpa only [sub_self] using δ.zero_mem
      | symm a b hab ih => simpa only [neg_sub] using δ.neg_mem ih
      | trans a b c hab hbc ihab ihbc =>
          simpa only [sub_add_sub_cancel] using δ.add_mem ihbc ihab
    refine ⟨w, fun s hs => ?_⟩
    have hp := paths (f w) (f s)
      (hgraph (f w) (Set.mem_image_of_mem f hw) (f s) (Set.mem_image_of_mem f hs))
    simpa only [pre_image w hw, pre_image s hs] using hp
  · exact ⟨0, fun s hs => (hSne ⟨s, hs⟩).elim⟩

private theorem eqvGen_chain {α : Type*} {r : α → α → Prop} {n : ℕ}
    (f : ℕ → α) (h : ∀ i < n, r (f i) (f (i + 1))) :
    Relation.EqvGen r (f 0) (f n) := by
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
      exact Relation.EqvGen.trans (f 0) (f n) (f (n + 1))
        (ih (fun i hi => h i (Nat.lt_succ_of_lt hi)))
        (Relation.EqvGen.rel (f n) (f (n + 1)) (h n (Nat.lt_succ_self n)))

theorem relativeDense_shortEdgeConnected
    {S : Set Plane} {ρ : ℝ} (hρ : 0 < ρ)
    (hdense : ∀ x : Plane, ∃ s ∈ S, dist x s < ρ) :
    ShortEdgeConnected S (5 * ρ) := by
  intro x hx y hy
  let r : Plane → Plane → Prop :=
    fun a b => a ∈ S ∧ b ∈ S ∧ dist a b < 5 * ρ
  have hdist : dist x y / ρ < (Nat.ceil (dist x y / ρ) + 1 : ℕ) := by
    have hceil : dist x y / ρ ≤ (Nat.ceil (dist x y / ρ) : ℕ) := by
      exact_mod_cast Nat.le_ceil (dist x y / ρ)
    exact lt_of_le_of_lt hceil (by exact_mod_cast Nat.lt_succ_self (Nat.ceil (dist x y / ρ)))
  let n : ℕ := Nat.ceil (dist x y / ρ) + 1
  have hnpos : (0 : ℝ) < n := by
    dsimp [n]
    positivity
  have hstep : dist x y / n < ρ := by
    have hn : dist x y / ρ < (n : ℝ) := by simpa [n] using hdist
    rw [div_lt_iff₀ hnpos]
    simpa [mul_comm] using (div_lt_iff₀ hρ).1 hn
  let v : Plane := ((n : ℝ)⁻¹) • (y - x)
  have hv : dist 0 v < ρ := by
    have hnorm : ‖v‖ = dist x y / n := by
      change ‖((n : ℝ)⁻¹) • (y - x)‖ = dist x y / n
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnpos, ← dist_eq_norm]
      simp [div_eq_mul_inv, mul_comm, dist_comm]
    simpa [dist_eq_norm] using hnorm ▸ hstep
  let z : ℕ → Plane := fun i => Classical.choose (hdense (x + (i : ℝ) • v))
  have hzmem (i : ℕ) : z i ∈ S := (Classical.choose_spec (hdense (x + (i : ℝ) • v))).1
  have hznear (i : ℕ) : dist (x + (i : ℝ) • v) (z i) < ρ :=
    (Classical.choose_spec (hdense (x + (i : ℝ) • v))).2
  have hanchor (i : ℕ) : dist (x + (i : ℝ) • v) (x + (i + 1 : ℕ) • v) < ρ := by
    rw [dist_eq_norm]
    have heq : (x + (i : ℝ) • v) - (x + (i + 1 : ℕ) • v) = -v := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul]
    rw [heq, norm_neg]
    simpa [dist_eq_norm] using hv
  let f : ℕ → Plane := fun i =>
    if i = 0 then x else if i = n + 2 then y else z (i - 1)
  have hfmem : ∀ i ≤ n + 2, f i ∈ S := by
    intro i hi
    dsimp [f]
    split_ifs with h0 hlast
    · exact hx
    · exact hy
    · exact hzmem _
  have hedge : ∀ i < n + 2, r (f i) (f (i + 1)) := by
    intro i hi
    have hi1_le : i + 1 ≤ n + 2 := by omega
    have hmem0 := hfmem i (by omega)
    have hmem1 := hfmem (i + 1) hi1_le
    refine ⟨hmem0, hmem1, ?_⟩
    change dist (if i = 0 then x else if i = n + 2 then y else z (i - 1))
      (if i + 1 = 0 then x else if i + 1 = n + 2 then y else z (i + 1 - 1)) < 5 * ρ
    by_cases h0 : i = 0
    · simp [h0]
      have hz := hznear 0
      have hz' : dist x (z 0) < ρ := by simpa using hz
      have hsmall : ρ < 5 * ρ := by nlinarith [hρ]
      exact lt_trans hz' hsmall
    · by_cases hlast : i + 1 = n + 2
      · have hi : i = n + 1 := by omega
        simp [hi]
        have heq : x + (n : ℝ) • v = y := by
          dsimp [v]
          simp
        rw [← heq]
        have hz := hznear n
        have hz' : dist (z n) (x + (n : ℝ) • v) < ρ := by
          simpa [dist_comm] using hz
        nlinarith [hz']
      · simp [h0]
        have hi_pos : 0 < i := Nat.pos_of_ne_zero h0
        have hcent : i ≤ n := by omega
        have hno : i ≠ n + 2 := by omega
        have hnotlast : i ≠ n + 1 := by omega
        change dist (if i = n + 2 then y else z (i - 1))
          (if i = n + 1 then y else z i) < 5 * ρ
        simp only [if_neg hno, if_neg hnotlast]
        have hleft := hznear (i - 1)
        have hright := hznear i
        have hleft' : dist (z (i - 1)) (x + ((i - 1 : ℕ) : ℝ) • v) < ρ := by
          simpa [dist_comm] using hleft
        have hmid := hanchor (i - 1)
        have htri := dist_triangle (z (i - 1)) (x + ((i - 1 : ℕ) : ℝ) • v)
          (x + (i : ℝ) • v)
        have htri' := dist_triangle (z (i - 1)) (x + (i : ℝ) • v) (z i)
        have heq : (i - 1 : ℕ) + 1 = i := by omega
        have hmid' : dist (x + ((i - 1 : ℕ) : ℝ) • v) (x + (i : ℝ) • v) < ρ := by
          simpa [heq] using hmid
        have hfirst := dist_triangle (z (i - 1))
          (x + ((i - 1 : ℕ) : ℝ) • v) (x + (i : ℝ) • v)
        calc
          dist (z (i - 1)) (z i) ≤ dist (z (i - 1)) (x + (i : ℝ) • v) +
              dist (x + (i : ℝ) • v) (z i) := htri'
          _ ≤ (dist (z (i - 1)) (x + ((i - 1 : ℕ) : ℝ) • v) +
              dist (x + ((i - 1 : ℕ) : ℝ) • v) (x + (i : ℝ) • v)) +
                dist (x + (i : ℝ) • v) (z i) := by
                exact add_le_add_left hfirst _
          _ < 5 * ρ := by
            have hR : dist (x + (i : ℝ) • v) (z i) < ρ := hright
            linarith
  have hchain : Relation.EqvGen r (f 0) (f (n + 2)) := eqvGen_chain f hedge
  have hstart : f 0 = x := by simp [f]
  have hfinish : f (n + 2) = y := by simp [f]
  rw [hstart, hfinish] at hchain
  exact hchain

theorem lift_period_of_denseWitnesses
    {P W : Set Plane} (f : Plane →ₗ[ℚ] Plane) {ρ : ℝ}
    (hρ : 0 < ρ) (hWP : W ⊆ P) (hinj : Set.InjOn f P)
    (hdense : ∀ x : Plane, ∃ w ∈ f '' W, dist x w < ρ)
    (hreflect : ShortDifferenceReflection P f (5 * ρ)) {p : Plane}
    (hperiod : p ∈ periodGroup (f '' W)) :
    ∃ q : Plane, f q = p ∧ q ∈ periodGroup W := by
  classical
  let pre : Plane → Plane := fun x =>
    if hx : x ∈ f '' W then Classical.choose hx else 0
  have pre_spec : ∀ x ∈ f '' W, pre x ∈ W ∧ f (pre x) = x := by
    intro x hx
    simpa only [pre, dif_pos hx] using Classical.choose_spec hx
  have pre_image : ∀ w ∈ W, pre (f w) = w := by
    intro w hw
    have hs := pre_spec (f w) (Set.mem_image_of_mem f hw)
    exact hinj (hWP hs.1) (hWP hw) hs.2
  let displacement : Plane → Plane := fun x => pre (x + p) - pre x
  have edge_constant : ∀ a b : Plane,
      a ∈ f '' W ∧ b ∈ f '' W ∧ dist a b < 5 * ρ →
        displacement a = displacement b := by
    intro a b hab
    have ha := pre_spec a hab.1
    have hb := pre_spec b hab.2.1
    have ha' := pre_spec (a + p) (period_add_mem hperiod hab.1)
    have hb' := pre_spec (b + p) (period_add_mem hperiod hab.2.1)
    have heq : f (pre b - pre a) = f (pre (b + p) - pre (a + p)) := by
      simp only [map_sub, ha.2, hb.2, ha'.2, hb'.2]
      abel
    have hr := hreflect (pre a) (hWP ha.1) (pre b) (hWP hb.1)
      (pre (a + p)) (hWP ha'.1) (pre (b + p)) (hWP hb'.1)
      (by simpa only [ha.2, hb.2] using hab.2.2)
      (by simpa only [ha'.2, hb'.2, dist_add_right] using hab.2.2) heq
    dsimp only [displacement]
    linear_combination hr
  have connected := relativeDense_shortEdgeConnected hρ hdense
  have path_constant : ∀ a b : Plane,
      Relation.EqvGen (fun x y : Plane =>
        x ∈ f '' W ∧ y ∈ f '' W ∧ dist x y < 5 * ρ) a b →
          displacement a = displacement b := by
    intro a b hpath
    induction hpath with
    | rel a b hab => exact edge_constant a b hab
    | refl a => rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  have constant : ∀ a ∈ f '' W, ∀ b ∈ f '' W,
      displacement a = displacement b := fun a ha b hb =>
    path_constant a b (connected a ha b hb)
  obtain ⟨fw₀, ⟨w₀, hw₀, rfl⟩, _⟩ := hdense 0
  let q := displacement (f w₀)
  have hshift : ∀ w ∈ W, pre (f w + p) = w + q := by
    intro w hw
    have hc := constant (f w) (Set.mem_image_of_mem f hw)
      (f w₀) (Set.mem_image_of_mem f hw₀)
    change pre (f w + p) - pre (f w) = q at hc
    rw [pre_image w hw] at hc
    linear_combination hc
  have hforward : ∀ w ∈ W, w + q ∈ W := by
    intro w hw
    rw [← hshift w hw]
    exact (pre_spec (f w + p)
      (period_add_mem hperiod (Set.mem_image_of_mem f hw))).1
  have hfq : f q = p := by
    have hs := (pre_spec (f w₀ + p)
      (period_add_mem hperiod (Set.mem_image_of_mem f hw₀))).2
    rw [hshift w₀ hw₀, map_add] at hs
    linear_combination hs
  refine ⟨q, hfq, AddAction.mem_stabilizer_iff.mpr ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨w, hw, rfl⟩
    simpa only [vadd_eq_add, add_comm] using hforward w hw
  · intro w hw
    obtain ⟨t, ht, hft⟩ := period_add_mem ((periodGroup (f '' W)).neg_mem hperiod)
      (Set.mem_image_of_mem f hw)
    have heq : t + q = w := hinj (hWP (hforward t ht)) (hWP hw) (by
      rw [map_add, hfq, hft]
      simp)
    exact ⟨t, ht, by simpa only [vadd_eq_add, add_comm] using heq⟩

theorem lift_lattice_of_denseWitnesses
    {T V W : Set Plane} (hT : HasFLC T) (hV : V.Finite)
    (f : Plane →ₗ[ℚ] Plane) {ρ : ℝ} (hρ : 0 < ρ)
    (hW : W ⊆ V + T) (hinj : Set.InjOn f (V + T))
    (hdense : ∀ x : Plane, ∃ w ∈ f '' W, dist x w < ρ)
    (hreflect : ShortDifferenceReflection (V + T) f (5 * ρ))
    (L : PlanarLattice) (hL : (L.toAddSubgroup : Set Plane) ⊆ periodGroup (f '' W)) :
    ∃ L₀ : PlanarLattice,
      (∀ j, f (L₀.basis j) = L.basis j) ∧
        (L₀.toAddSubgroup : Set Plane) ⊆ periodGroup W := by
  have hb (j : Fin 2) : L.basis j ∈ periodGroup (f '' W) :=
    hL (AddSubgroup.subset_closure ⟨j, rfl⟩)
  obtain ⟨q₀, hf₀, hq₀⟩ :=
    lift_period_of_denseWitnesses f hρ hW hinj hdense hreflect (hb 0)
  obtain ⟨q₁, hf₁, hq₁⟩ :=
    lift_period_of_denseWitnesses f hρ hW hinj hdense hreflect (hb 1)
  have hfind : LinearIndependent ℚ ![f q₀, f q₁] := by
    have heq : ![f q₀, f q₁] = L.basis := by
      ext j
      fin_cases j
      · exact hf₀
      · exact hf₁
    rw [heq]
    exact L.independent.restrict_scalars' ℚ
  obtain ⟨fw, ⟨w, hw, rfl⟩, _⟩ := hdense 0
  have hcoset : ∃ v : Plane,
      {x : Plane | ∃ m n : ℤ, x = v + m • q₀ + n • q₁} ⊆ V + T := by
    refine ⟨w, ?_⟩
    rintro x ⟨m, n, rfl⟩
    exact hW (period_add_mem ((periodGroup W).zsmul_mem hq₁ n)
      (period_add_mem ((periodGroup W).zsmul_mem hq₀ m) hw))
  let L₀ : PlanarLattice :=
    ⟨![q₀, q₁], rankTwo_of_flcCoset_and_independentRationalImages hT hV f hfind hcoset⟩
  refine ⟨L₀, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hf₀
    · exact hf₁
  · change AddSubgroup.closure (Set.range L₀.basis) ≤ periodGroup W
    apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨j, rfl⟩
    fin_cases j
    · exact hq₀
    · exact hq₁

theorem lift_subfamily_period
    {T V W A : Set Plane} (f : Plane →ₗ[ℚ] Plane)
    (hVne : V.Nonempty) (hAT : A ⊆ T) (hW : W ⊆ V + T)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hdense : ∀ x : Plane, ∃ w ∈ f '' W, dist x w < ρ)
    (hreflect : ShortDifferenceReflection (V + T) f (5 * ρ)) {q : Plane}
    (hWperiod : q ∈ periodGroup W)
    (hAperiod : f q ∈ periodGroup (f '' A)) :
    q ∈ periodGroup A := by
  classical
  obtain ⟨v, hv⟩ := hVne
  have forward : ∀ u : Plane, u ∈ periodGroup W →
      f u ∈ periodGroup (f '' A) → ∀ t ∈ A, t + u ∈ A := by
    intro u hu hfu t ht
    obtain ⟨s, hs, hfs⟩ := period_add_mem hfu (Set.mem_image_of_mem f ht)
    obtain ⟨fw, ⟨w, hw, rfl⟩, hdist⟩ := hdense (f (v + t))
    have hwt : v + t ∈ V + T := Set.mem_add.mpr ⟨v, hv, t, hAT ht, rfl⟩
    have hws : v + s ∈ V + T := Set.mem_add.mpr ⟨v, hv, s, hAT hs, rfl⟩
    have hw' : w + u ∈ W := period_add_mem hu hw
    have heq : f ((v + t) - w) = f ((v + s) - (w + u)) := by
      simp only [map_sub, map_add] at hfs ⊢
      linear_combination -hfs
    have hdist' : dist (f (w + u)) (f (v + s)) < 5 * ρ := by
      have : dist (f (w + u)) (f (v + s)) = dist (f w) (f (v + t)) := by
        simp only [map_add] at hfs ⊢
        rw [hfs]
        rw [← add_assoc, dist_add_right]
      rw [this, dist_comm]
      linarith
    have hres := hreflect w (hW hw) (v + t) hwt (w + u) (hW hw') (v + s) hws
      (by rw [dist_comm]; linarith) hdist' heq
    have hst : s = t + u := by linear_combination -hres
    rwa [hst] at hs
  apply AddAction.mem_stabilizer_iff.mpr
  apply Set.Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    simpa only [vadd_eq_add, add_comm] using forward q hWperiod hAperiod t ht
  · intro t ht
    refine ⟨t - q, ?_, by simp [vadd_eq_add]⟩
    simpa only [sub_eq_add_neg] using
      forward (-q) ((periodGroup W).neg_mem hWperiod)
        (by simpa only [map_neg] using (periodGroup (f '' A)).neg_mem hAperiod) t ht

/-- Uniform over all rational slice decompositions and over all tiles with the same
bounded boundary presentation/direction set. This avoids choosing epsilon after seeing
an approximation-dependent witness-density constant. -/
theorem sliceWitnesses_uniformRelativeDense
    (D : Finset (Submodule ℝ Plane)) (L B ρ R : ℝ)
    (hL : 0 ≤ L) (hB : 0 < B) (hρ : 0 < ρ) (hR : 0 < R)
    (hD : ∀ δ ∈ D, Module.finrank ℝ δ = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : PolygonalRegion) (F : Finset (Plane × Plane)),
      (K.support ⊆ Metric.closedBall 0 B) →
      (frontier K.support = ⋃ e ∈ F, segment ℝ e.1 e.2) →
      ((∑ e ∈ F, dist e.1 e.2) ≤ L) →
      (∀ δ : Submodule ℝ Plane, HasBoundaryDirection K δ → δ ∈ D) →
      ∀ (T : Set Plane), IsPacking K.prototileFamily (K.placements T) →
        (∀ x : Plane, ∃ t ∈ T, dist x t < ρ) →
        (∀ δ ∈ D, ∀ x : Plane,
          ∃ v ∈ fibreProperVertices K T δ, dist x v < R) →
        ∀ (ι : Type) (atom : ι → Set Plane) (direction : ι → Submodule ℝ Plane),
          (∀ j, (atom j).Nonempty) → Set.PairwiseDisjoint Set.univ atom →
          ((⋃ j, atom j) = T) →
          (∀ j, Module.finrank ℝ (direction j) = 1 ∧
            IsLineSupported (atom j) (direction j)) →
          ∀ x : Plane, ∃ j, ∃ v ∈ properVertices (regularSupport K (atom j)),
            dist x v < C := by
  classical
  obtain ⟨J, hJ, hangle⟩ := finiteAngle_uniform_bound D hD
  let H := R + ρ + 2 * B + 2
  let Q := (2 * J + 1) * H + B + 1
  let N := 2 * B + L + 4
  let C := Q + L + N + H + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have hN : 0 < N := by dsimp [N]; linarith
  have hQmin : H + B < Q := by dsimp [Q]; nlinarith
  have hQ : 0 < Q := by linarith
  have hC : 0 < C := by dsimp [C]; linarith
  have hmargin : Q + L + 1 ≤ C := by dsimp [C]; linarith
  have hCN : H + N < C := by dsimp [C]; linarith
  have hRH : R + B < H := by dsimp [H]; linarith
  have hρH : ρ < H := by dsimp [H]; linarith
  have hRC : R < C := by linarith
  refine ⟨C, hC, ?_⟩
  intro K F hbound hfrontier hlength hDirections T hp hTdense hFdense
    ι atom direction _hatomNonempty hatomDisjoint hUnion hLines x
  have hnonboundary : ∀ (δ : Submodule ℝ Plane), Module.finrank ℝ δ = 1 →
      ¬HasBoundaryDirection K δ → ∀ S : Set Plane,
        IsPacking K.prototileFamily (K.placements S) → IsLineSupported S δ →
          ∀ t ∈ S, ∃ v ∈ properVertices (regularSupport K S), dist t v < N := by
    intro δ hδ hnot S hpS hline t ht
    by_contra hnone
    let R₀ := 2 * B + 2
    have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith
    have hnoCorner : Disjoint (properVertices (regularSupport K S))
        (Metric.ball t (R₀ + L + 1)) := by
      apply Set.disjoint_left.mpr
      intro v hv hball
      apply hnone
      refine ⟨v, hv, ?_⟩
      have hd := Metric.mem_ball.mp hball
      rw [dist_comm] at hd
      dsimp [R₀, N] at hd ⊢
      linarith
    have hsat₀ := noCornerLineCarrier_localSaturation_of_boundaryLength F L hL
      hfrontier hlength hδ hpS hline hR₀ hnoCorner
    obtain ⟨p, hpfront, hpt⟩ := stripFrontierPoint hδ hB hbound hpS hline ht
    obtain ⟨q, hpq, hqp, hsegment⟩ := saturated_frontier_segment hδ hsat₀
      (show p ∈ Metric.ball t R₀ from Metric.mem_ball.mpr hpt) hpfront
    exact hnot (frontier_segment_isBoundaryDirection hδ hpS hpq hqp hsegment)
  by_contra hWitness
  have hno (j : ι) : ∀ v ∈ properVertices (regularSupport K (atom j)),
      ¬dist x v < C := by
    intro v hv hd
    exact hWitness ⟨j, v, hv, hd⟩
  have hsub (j : ι) : atom j ⊆ T := by
    intro u hu
    rw [← hUnion]
    exact Set.mem_iUnion.mpr ⟨j, hu⟩
  have hsat (j : ι) : LocallySaturatedAlong (regularSupport K (atom j))
      (direction j) x Q := cornerFree_sliceAtom_localSaturation F L hL hfrontier
    hlength (hLines j).1 hp (hsub j) (hLines j).2 hQ hmargin (hno j)
  have hactiveBoundary (j : ι) {u : Plane} (hu : u ∈ atom j) (hux : dist u x < H) :
      HasBoundaryDirection K (direction j) := by
    by_contra hnot
    obtain ⟨v, hv, huv⟩ := hnonboundary (direction j) (hLines j).1 hnot (atom j)
      (hp.mono (fun _ ht => hsub j ht)) (hLines j).2 u hu
    apply hno j v hv
    have ht := dist_triangle x u v
    rw [dist_comm x u] at ht
    linarith
  obtain ⟨t, ht, hxt⟩ := hTdense x
  have htx : dist t x < H := by rw [dist_comm] at hxt; linarith
  obtain ⟨j₀, htj⟩ := Set.mem_iUnion.mp (hUnion.symm ▸ ht)
  have hδD : direction j₀ ∈ D := hDirections _ (hactiveBoundary j₀ htj htx)
  have hparallel (j : ι) {u : Plane} (hu : u ∈ atom j) (hux : dist u x < H) :
      direction j = direction j₀ := by
    by_cases hj : j = j₀
    · subst j; rfl
    by_contra hdne
    have hεD : direction j ∈ D := hDirections _ (hactiveBoundary j hu hux)
    exact hdne (locallySaturated_disjointCarriers_parallel (hLines j).1 (hLines j₀).1
      hJ hH.le (hangle _ hεD _ hδD hdne) hbound hp (hsub j) (hsub j₀)
      (hatomDisjoint (Set.mem_univ j) (Set.mem_univ j₀) hj) (hsat j) (hsat j₀)
      hu htj hux.le htx.le)
  obtain ⟨v, hv, hxv⟩ := hFdense (direction j₀) hδD x
  obtain ⟨s, hvs⟩ := Set.mem_iUnion.mp hv
  have hpFibre : IsPacking K.prototileFamily
      (K.placements (lineFibre (direction j₀) T s)) := hp.mono (fun _ hz => hz.1)
  obtain ⟨u, hu, huv⟩ := frontier_near_centre_of_supportBound hbound hpFibre hvs.1
  have hux : dist u x < H := by
    have ht := dist_triangle u v x
    rw [dist_comm v x] at ht
    linarith
  obtain ⟨j, huj⟩ := Set.mem_iUnion.mp (hUnion.symm ▸ hu.1)
  have hdir := hparallel j huj hux
  have hline : IsLineSupported (atom j) (direction j₀) := by
    rw [← hdir]
    exact (hLines j).2
  have hdiff {w : Plane} (hw : w ∈ atom j) : w - u ∈ direction j₀ := by
    obtain ⟨a, ha⟩ := hline
    convert (direction j₀).sub_mem (ha w hw) (ha u huj) using 1
    abel
  have hsubFibre : atom j ⊆ lineFibre (direction j₀) T s := by
    intro w hw
    refine ⟨hsub j hw, ?_⟩
    convert (direction j₀).add_mem (hdiff hw) hu.2 using 1
    abel
  have hsatj : LocallySaturatedAlong (regularSupport K (atom j)) (direction j₀) x Q := by
    rw [← hdir]
    exact hsat j
  have hlocal : ∀ z ∈ lineFibre (direction j₀) T s,
      dist z v < B + 1 → z ∈ atom j := by
    intro z hz hzv
    apply localFibreMembership hp (hsub j) hline hbound hB hQ hsatj huj
      (by linarith) hz.1
    · convert (direction j₀).sub_mem hz.2 hu.2 using 1
      abel
    · have ht := dist_triangle z v x
      rw [dist_comm v x] at ht
      have hsmall : R + 2 * B + 1 < H + B := by dsimp [H]; linarith
      linarith
  have hgerm := regularSupport_germ_of_local_centres hbound hpFibre hsubFibre hlocal
  have hvj : v ∈ properVertices (regularSupport K (atom j)) :=
    (isProperVertex_iff_of_eventuallyEq hgerm).mpr hvs
  exact hno j v hvj (hxv.trans hRC)

/- The mixed branch has a genuine lattice longitudinal period for the entire column
aggregate. Merely knowing one unrelated universal real column period would not suffice. -/
end Tiling.Polygonal

namespace Tiling.RationalSlopes

open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Polygonal

private theorem mergeGoodParametrizations
    {K : PolygonalRegion} {A B : Set Plane}
    (GA : GoodParametrization K A) (GB : GoodParametrization K B)
    (hL : GA.lattice = GB.lattice) (hdisj : Disjoint A B) :
    ∃ G : GoodParametrization K (A ∪ B), G.lattice = GA.lattice := by
  classical
  let e : Fin (GA.numberOfParts + GB.numberOfParts) ≃
      (Fin GA.numberOfParts ⊕ Fin GB.numberOfParts) := finSumFinEquiv.symm
  let Raw := (Σ i : Fin GA.numberOfParts, GA.Index i) ⊕
    (Σ i : Fin GB.numberOfParts, GB.Index i)
  let tag : Raw → (Fin GA.numberOfParts ⊕ Fin GB.numberOfParts) :=
    Sum.elim (fun q => Sum.inl q.1) (fun q => Sum.inr q.1)
  let Index : Fin (GA.numberOfParts + GB.numberOfParts) → Type :=
    fun i => {q : Raw // tag q = e i}
  let atom : ∀ i, Index i → ℤ → Set Plane := fun _ a m =>
    match a.1 with
    | Sum.inl q => GA.atom q.1 q.2 m
    | Sum.inr q => GB.atom q.1 q.2 m
  let lambda : Fin (GA.numberOfParts + GB.numberOfParts) → ℤ :=
    fun i => Sum.elim GA.lambdaCoefficient GB.lambdaCoefficient (e i)
  let gamma : Fin (GA.numberOfParts + GB.numberOfParts) → ℤ :=
    fun i => Sum.elim GA.gammaCoefficient GB.gammaCoefficient (e i)
  let decode : (Σ i : Fin (GA.numberOfParts + GB.numberOfParts), Index i × ℤ) → Raw × ℤ :=
    fun q => (q.2.1.1, q.2.2)
  have decode_injective : Function.Injective decode := by
    intro x y h
    rcases x with ⟨i, a, m⟩
    rcases y with ⟨j, b, n⟩
    change (a.1, m) = (b.1, n) at h
    have hraw : a.1 = b.1 := congrArg Prod.fst h
    have hm : m = n := congrArg Prod.snd h
    have he : e i = e j := by
      calc
        e i = tag a.1 := a.2.symm
        _ = tag b.1 := congrArg tag hraw
        _ = e j := b.2
    have hij : i = j := e.injective he
    subst j
    have hab : a = b := Subtype.ext hraw
    subst b
    subst n
    rfl
  let encA : (Σ i : Fin GA.numberOfParts, GA.Index i × ℤ) → Raw × ℤ :=
    fun q => (Sum.inl ⟨q.1, q.2.1⟩, q.2.2)
  let encB : (Σ i : Fin GB.numberOfParts, GB.Index i × ℤ) → Raw × ℤ :=
    fun q => (Sum.inr ⟨q.1, q.2.1⟩, q.2.2)
  have atom_subset_A (i : Fin GA.numberOfParts) (a : GA.Index i) (m : ℤ) :
      GA.atom i a m ⊆ A := by
    intro x hx
    rw [← GA.union_eq]
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨m, hx⟩⟩⟩
  have atom_subset_B (i : Fin GB.numberOfParts) (a : GB.Index i) (m : ℤ) :
      GB.atom i a m ⊆ B := by
    intro x hx
    rw [← GB.union_eq]
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨m, hx⟩⟩⟩
  let G : GoodParametrization K (A ∪ B) := {
    lattice := GA.lattice
    numberOfParts := GA.numberOfParts + GB.numberOfParts
    Index := Index
    atom := atom
    atom_nonempty := by
      intro i a m
      cases ha : a.1 with
      | inl q => simpa [atom, ha] using GA.atom_nonempty q.1 q.2 m
      | inr q => simpa [atom, ha] using GB.atom_nonempty q.1 q.2 m
    atoms_disjoint := by
      intro x hx y hy hxy
      rcases x with ⟨i, ⟨a, m⟩⟩
      rcases y with ⟨j, ⟨b, n⟩⟩
      change Disjoint (atom i a m) (atom j b n)
      cases ha : a.1 with
      | inl qa =>
        cases hb : b.1 with
        | inl qb =>
          have hneq : (⟨qa.1, (qa.2, m)⟩ : Σ k : Fin GA.numberOfParts, GA.Index k × ℤ) ≠
              ⟨qb.1, (qb.2, n)⟩ := by
            intro hsrc
            apply hxy
            apply decode_injective
            calc
              decode ⟨i, ⟨a, m⟩⟩ = encA ⟨qa.1, (qa.2, m)⟩ := by
                simp [decode, encA, ha]
              _ = encA ⟨qb.1, (qb.2, n)⟩ := congrArg encA hsrc
              _ = decode ⟨j, ⟨b, n⟩⟩ := by simp [decode, encA, hb]
          have hpair := GA.atoms_disjoint
            (x := ⟨qa.1, (qa.2, m)⟩) (y := ⟨qb.1, (qb.2, n)⟩)
            (by trivial) (by trivial) hneq
          simpa [atom, ha, hb] using hpair
        | inr qb =>
          have hcross : Disjoint (GA.atom qa.1 qa.2 m) (GB.atom qb.1 qb.2 n) := by
            apply Set.disjoint_left.mpr
            intro z hzA hzB
            exact Set.disjoint_left.mp hdisj
              (atom_subset_A qa.1 qa.2 m hzA) (atom_subset_B qb.1 qb.2 n hzB)
          simpa [atom, ha, hb] using hcross
      | inr qa =>
        cases hb : b.1 with
        | inl qb =>
          have hcross : Disjoint (GB.atom qa.1 qa.2 m) (GA.atom qb.1 qb.2 n) := by
            apply Set.disjoint_left.mpr
            intro z hzB hzA
            exact Set.disjoint_left.mp hdisj
              (atom_subset_A qb.1 qb.2 n hzA) (atom_subset_B qa.1 qa.2 m hzB)
          simpa [atom, ha, hb] using hcross
        | inr qb =>
          have hneq : (⟨qa.1, (qa.2, m)⟩ : Σ k : Fin GB.numberOfParts, GB.Index k × ℤ) ≠
              ⟨qb.1, (qb.2, n)⟩ := by
            intro hsrc
            apply hxy
            apply decode_injective
            calc
              decode ⟨i, ⟨a, m⟩⟩ = encB ⟨qa.1, (qa.2, m)⟩ := by
                simp [decode, encB, ha]
              _ = encB ⟨qb.1, (qb.2, n)⟩ := congrArg encB hsrc
              _ = decode ⟨j, ⟨b, n⟩⟩ := by simp [decode, encB, hb]
          have hpair := GB.atoms_disjoint
            (x := ⟨qa.1, (qa.2, m)⟩) (y := ⟨qb.1, (qb.2, n)⟩)
            (by trivial) (by trivial) hneq
          simpa [atom, ha, hb] using hpair
    union_eq := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨a, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨m, hm⟩
        cases ha : a.1 with
        | inl q =>
            left
            rw [← GA.union_eq]
            exact Set.mem_iUnion.mpr ⟨q.1, Set.mem_iUnion.mpr ⟨q.2,
              Set.mem_iUnion.mpr ⟨m, by simpa [atom, ha] using hm⟩⟩⟩
        | inr q =>
            right
            rw [← GB.union_eq]
            exact Set.mem_iUnion.mpr ⟨q.1, Set.mem_iUnion.mpr ⟨q.2,
              Set.mem_iUnion.mpr ⟨m, by simpa [atom, ha] using hm⟩⟩⟩
      · intro x hx
        rcases hx with hxA | hxB
        · have hxa : x ∈ (⋃ i, ⋃ a : GA.Index i, ⋃ m : ℤ, GA.atom i a m) := by
            exact (congrArg (fun U : Set Plane => x ∈ U) GA.union_eq.symm).mp hxA
          rcases Set.mem_iUnion.mp hxa with ⟨i, hxa⟩
          rcases Set.mem_iUnion.mp hxa with ⟨a, hxa⟩
          rcases Set.mem_iUnion.mp hxa with ⟨m, hm⟩
          let q : Index (e.symm (Sum.inl i)) := ⟨Sum.inl ⟨i, a⟩, by simp [tag]⟩
          apply Set.mem_iUnion.mpr
          refine ⟨e.symm (Sum.inl i), Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨m, ?_⟩⟩⟩
          simpa [atom, q, tag] using hm
        · have hxb : x ∈ (⋃ i, ⋃ a : GB.Index i, ⋃ m : ℤ, GB.atom i a m) := by
            exact (congrArg (fun U : Set Plane => x ∈ U) GB.union_eq.symm).mp hxB
          rcases Set.mem_iUnion.mp hxb with ⟨i, hxb⟩
          rcases Set.mem_iUnion.mp hxb with ⟨a, hxb⟩
          rcases Set.mem_iUnion.mp hxb with ⟨m, hm⟩
          let q : Index (e.symm (Sum.inr i)) := ⟨Sum.inr ⟨i, a⟩, by simp [tag]⟩
          apply Set.mem_iUnion.mpr
          refine ⟨e.symm (Sum.inr i), Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨m, ?_⟩⟩⟩
          simpa [atom, q, tag] using hm
    lambdaCoefficient := lambda
    gammaCoefficient := gamma
    lambdaCoefficient_ne_zero := by
      intro i
      cases hi : e i with
      | inl j => simpa [lambda, hi] using GA.lambdaCoefficient_ne_zero j
      | inr j => simpa [lambda, hi] using GB.lambdaCoefficient_ne_zero j
    atom_periodic := by
      intro i a m
      cases ha : a.1 with
      | inl q =>
          have htag : Sum.inl q.1 = e i := by simpa [tag, ha] using a.2
          have hLam : lambda i = GA.lambdaCoefficient q.1 := by
            dsimp [lambda]
            rw [← htag]
            rfl
          have hγ : gamma i = GA.gammaCoefficient q.1 := by
            dsimp [gamma]
            rw [← htag]
            rfl
          simpa [atom, ha, hLam, hγ] using GA.atom_periodic q.1 q.2 m
      | inr q =>
          have htag : Sum.inr q.1 = e i := by simpa [tag, ha] using a.2
          have hLam : lambda i = GB.lambdaCoefficient q.1 := by
            dsimp [lambda]
            rw [← htag]
            rfl
          have hγ : gamma i = GB.gammaCoefficient q.1 := by
            dsimp [gamma]
            rw [← htag]
            rfl
          simpa [atom, ha, hLam, hγ, hL] using GB.atom_periodic q.1 q.2 m
    carrier_transport := by
      intro i a m
      cases ha : a.1 with
      | inl q => simpa [atom, ha] using GA.carrier_transport q.1 q.2 m
      | inr q => simpa [atom, ha, hL] using GB.carrier_transport q.1 q.2 m
  }
  exact ⟨G, rfl⟩

end Tiling.RationalSlopes

namespace Tiling.Polygonal

open Tiling.RationalPolygonal (PolygonalRegion)

private theorem suppliedLatticeFibreParametrization
    {K : PolygonalRegion} {T : Set Plane} {δ : Submodule ℝ Plane}
    (L : PlanarLattice) (k l : ℤ) (hk : k ≠ 0)
    (hqδ : k • L.basis 0 + l • L.basis 1 ∈ δ)
    (hqT : k • L.basis 0 + l • L.basis 1 ∈ periodGroup T)
    (hγδ : L.basis 1 ∉ δ)
    (htransport : ∀ t ∈ T, ∀ m : ℤ, ∃ s ∈ T,
      s - t - m • L.basis 1 ∈ δ ∧ regularSupport K (lineFibre δ T s) =
        m • L.basis 1 +ᵥ regularSupport K (lineFibre δ T t)) :
    ∃ G : Tiling.RationalSlopes.GoodParametrization K T, G.lattice = L := by
  classical
  let q := k • L.basis 0 + l • L.basis 1
  let γ := L.basis 1
  have hqδ : q ∈ δ := hqδ
  have hqT : q ∈ periodGroup T := hqT
  let orbitSetoid : Setoid T := {
    r := fun s t => ∃ m : ℤ, (s : Plane) - t - m • γ ∈ δ
    iseqv := ⟨?_, ?_, ?_⟩ }
  case refine_1 =>
    intro s
    exact ⟨0, by simp⟩
  case refine_2 =>
    rintro s t ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    convert δ.neg_mem hm using 1
    simp only [neg_smul]
    abel
  case refine_3 =>
    rintro s t u ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    convert δ.add_mem hm hn using 1
    simp only [add_zsmul]
    abel
  let Q := Quotient orbitSetoid
  let f : Q → ℤ → T := fun a m =>
    ⟨(htransport (a.out : Plane) a.out.property m).choose,
      (htransport (a.out : Plane) a.out.property m).choose_spec.1⟩
  have hf (a : Q) (m : ℤ) : (f a m : Plane) - a.out - m • γ ∈ δ ∧
      regularSupport K (lineFibre δ T (f a m)) =
        m • γ +ᵥ regularSupport K (lineFibre δ T a.out) :=
    (htransport (a.out : Plane) a.out.property m).choose_spec.2
  have hγmul (m : ℤ) (hm : m • γ ∈ δ) : m = 0 := by
    by_contra hm0
    have hc : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm0
    apply hγδ
    have hh := δ.smul_mem ((m : ℝ)⁻¹) hm
    simpa only [← Int.cast_smul_eq_zsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul] using hh
  have hIndices (a b : Q) (m n : ℤ) {x : Plane}
      (hx : x ∈ lineFibre δ T (f a m)) (hy : x ∈ lineFibre δ T (f b n)) :
      a = b ∧ m = n := by
    have hft : (f a m : Plane) - f b n ∈ δ := by
      convert δ.sub_mem hy.2 hx.2 using 1
      abel
    have hrel : (a.out : Plane) - b.out - (n - m) • γ ∈ δ := by
      convert δ.add_mem (δ.sub_mem hft (hf a m).1) (hf b n).1 using 1
      simp only [sub_zsmul]
      abel
    have hab : a = b := Quotient.out_equiv_out.mp ⟨n - m, hrel⟩
    subst b
    have hmn : (m - n) • γ ∈ δ := by
      convert δ.sub_mem (δ.sub_mem hft (hf a m).1) (δ.neg_mem (hf a n).1) using 1
      simp only [sub_zsmul]
      abel
    exact ⟨rfl, sub_eq_zero.mp (hγmul _ hmn)⟩
  have hqFibre (t : T) : q ∈ periodGroup (lineFibre δ T t) := by
    change q +ᵥ lineFibre δ T t = lineFibre δ T t
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · exact hqT ▸ (show q +ᵥ y ∈ q +ᵥ T from ⟨y, hy.1, rfl⟩)
      · convert δ.add_mem hqδ hy.2 using 1
        simp only [vadd_eq_add]
        abel
    · intro hx
      refine ⟨(-q) +ᵥ x, ⟨?_, ?_⟩, by simp⟩
      · exact (periodGroup T).neg_mem hqT ▸
          (show (-q) +ᵥ x ∈ (-q) +ᵥ T from ⟨x, hx.1, rfl⟩)
      · convert δ.add_mem (δ.neg_mem hqδ) hx.2 using 1
        simp only [vadd_eq_add]
        abel
  refine ⟨{
    lattice := L
    numberOfParts := 1
    Index := fun _ => Q
    atom := fun _ a m => lineFibre δ T (f a m)
    atom_nonempty := ?_
    atoms_disjoint := ?_
    union_eq := ?_
    lambdaCoefficient := fun _ => k
    gammaCoefficient := fun _ => l
    lambdaCoefficient_ne_zero := ?_
    atom_periodic := ?_
    carrier_transport := ?_ }, rfl⟩
  · intro i a m
    exact ⟨f a m, (f a m).property, by simp⟩
  · intro s _ t _ hst
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hab, hmn⟩ := hIndices s.2.1 t.2.1 s.2.2 t.2.2 hx hy
    apply hst
    have hi : s.1 = t.1 := Subsingleton.elim _ _
    cases s with | mk i am =>
      cases t with | mk j bn =>
        dsimp at hi hab hmn
        subst j
        exact congrArg (Sigma.mk i) (Prod.ext hab hmn)
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, a, m, hx⟩
      exact hx.1
    · intro hx
      let a : Q := Quotient.mk orbitSetoid ⟨x, hx⟩
      obtain ⟨m, hm⟩ := orbitSetoid.symm (Quotient.mk_out ⟨x, hx⟩)
      refine ⟨0, a, m, hx, ?_⟩
      convert δ.sub_mem hm (hf a m).1 using 1
      abel
  · intro _; exact hk
  · intro i a m
    exact hqFibre (f a m)
  · intro i a m
    have h0 := (hf a 0).2
    simp only [zero_smul, zero_vadd] at h0
    exact (hf a m).2.trans (congrArg (fun B : Set Plane => m • γ +ᵥ B) h0.symm)


private theorem columnCompanion_on_rescaled_lattice
    {K : PolygonalRegion} {A T : Set Plane} {δ : Submodule ℝ Plane}
    (G : Tiling.RationalSlopes.GoodParametrization K A)
    (k l : ℤ) (hk : k ≠ 0)
    (hqδ : k • G.lattice.basis 0 + l • G.lattice.basis 1 ∈ δ)
    (hqT : k • G.lattice.basis 0 + l • G.lattice.basis 1 ∈ periodGroup T)
    (hγδ : G.lattice.basis 1 ∉ δ)
    (n ell : ℕ) (hn : 0 < n) (hell : 0 < ell)
    (htransport : ∀ t ∈ T, ∀ m : ℤ, ∃ s ∈ T,
      s - t - m • ((n : ℤ) • ((ell : ℤ) • G.lattice.basis 1)) ∈ δ ∧
        regularSupport K (lineFibre δ T s) =
          m • ((n : ℤ) • ((ell : ℤ) • G.lattice.basis 1)) +ᵥ
            regularSupport K (lineFibre δ T t)) :
    ∃ r : ℕ, 0 < r ∧
      ∃ GA : Tiling.RationalSlopes.GoodParametrization K A,
      ∃ GT : Tiling.RationalSlopes.GoodParametrization K T,
        GT.lattice = GA.lattice ∧
          ∀ j : Fin 2, GA.lattice.basis j = (r : ℤ) • G.lattice.basis j := by
  let r := n * ell
  have hr : 0 < r := Nat.mul_pos hn hell
  obtain ⟨GA, hGA⟩ := G.rescale_basis r hr
  have hγ : GA.lattice.basis 1 =
      (n : ℤ) • ((ell : ℤ) • G.lattice.basis 1) := by
    rw [hGA 1]
    simp only [r, Nat.cast_mul, smul_smul]
  have hcomb : k • GA.lattice.basis 0 + l • GA.lattice.basis 1 =
      (r : ℤ) • (k • G.lattice.basis 0 + l • G.lattice.basis 1) := by
    rw [hGA 0, hGA 1]
    module
  have hcombδ : k • GA.lattice.basis 0 + l • GA.lattice.basis 1 ∈ δ := by
    rw [hcomb]
    exact δ.toAddSubgroup.zsmul_mem hqδ r
  have hcombT : k • GA.lattice.basis 0 + l • GA.lattice.basis 1 ∈ periodGroup T := by
    rw [hcomb]
    exact (periodGroup T).zsmul_mem hqT r
  have hGAγδ : GA.lattice.basis 1 ∉ δ := by
    rw [hGA 1]
    intro hc
    apply hγδ
    have hrreal : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
    have hh := δ.smul_mem ((r : ℝ)⁻¹) hc
    simpa only [← Int.cast_smul_eq_zsmul ℝ, smul_smul,
      Int.cast_natCast, inv_mul_cancel₀ hrreal, one_smul] using hh
  obtain ⟨GT, hGT⟩ := suppliedLatticeFibreParametrization GA.lattice k l hk
    hcombδ hcombT hGAγδ (by simpa only [hγ] using htransport)
  exact ⟨r, hr, GA, GT, hGT, hGA⟩

theorem goodParametrization_add_columns
    {K : PolygonalRegion} {A B E : Set Plane}
    (G : Tiling.RationalSlopes.GoodParametrization K A)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hdisj : Disjoint A B)
    (htile : TilesOn K (A ∪ B) E) (hEopen : IsOpen E)
    (hEregular : interior (closure E) = E) (hEper : IsLatticePeriodic E)
    {δ : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1)
    (hcol : IsUnionOfColumns K δ B) (k l : ℤ) (hk : k ≠ 0)
    (hwithin : k • G.lattice.basis 0 + l • G.lattice.basis 1 ∈ δ)
    (hperiod : k • G.lattice.basis 0 + l • G.lattice.basis 1 ∈ periodGroup B) :
    ∃ r : ℕ, 0 < r ∧ ∃ G' : Tiling.RationalSlopes.GoodParametrization K (A ∪ B),
      ∀ j : Fin 2, G'.lattice.basis j = (r : ℤ) • G.lattice.basis j := by
  have hpK := htile.2.1
  have hAT : A ⊆ A ∪ B := Set.subset_union_left
  have hBT : B ⊆ A ∪ B := Set.subset_union_right
  have hcarDisj := regularSupport_disjoint_of_disjoint_subfamilies hpK hAT hBT hdisj
  have hcarA := regularSupport_isRegularOpen K A
  have hcarB := regularSupport_isRegularOpen K B
  have hcarAne := regularSupport_nonempty (K := K) hAne
  have hcarBne := regularSupport_nonempty (K := K) hBne
  have hcarBinv := unionColumns_carrier_invariant hcol
  have hcarE : E = interior (closure (regularSupport K A ∪ regularSupport K B)) := by
    rw [← regularSupport_eq_of_tilesOn hEopen hEregular htile]
    exact regularSupport_union K A B
  -- This is the regular-open relative complement, not a difference of raw tile unions.
  have hcomplement := regularOpen_disjoint_complement hcarA.1 hcarA.2
    hcarB.1 hcarB.2 hcarDisj hcarE
  have hcarBproper : regularSupport K B ≠ Set.univ := by
    intro hfull
    obtain ⟨x, hx⟩ := hcarAne
    exact Set.disjoint_left.mp hcarDisj hx (by rw [hfull]; trivial)
  have hgamma := lattice_transverse_of_combination_mem G.lattice hδ k l hk hwithin
  let N : ℤ := G.commonMultiple
  let p : Plane := N • (k • G.lattice.basis 0 + l • G.lattice.basis 1)
  have hN : N ≠ 0 := by
    dsimp only [N]
    exact_mod_cast (ne_of_gt G.commonMultiple_pos)
  have hp : p ≠ 0 := smul_ne_zero hN (lattice_combination_ne_zero G.lattice k l hk)
  have hpδ : p ∈ δ := δ.toAddSubgroup.zsmul_mem hwithin N
  have hpApacking : IsPacking K.prototileFamily (K.placements A) :=
    hpK.mono (fun _ hx => hAT hx)
  have hcarPeriods := G.carriers_periodic hpApacking
  have hpA : p ∈ periodGroup (regularSupport K A) := by
    have hh := (periodGroup (regularSupport K A)).add_mem
      ((periodGroup (regularSupport K A)).zsmul_mem hcarPeriods.2 k)
      ((periodGroup (regularSupport K A)).zsmul_mem hcarPeriods.1 (N * l))
    convert hh using 1
    dsimp only [p, N]
    module
  obtain ⟨ell, hell, htransverse⟩ := columnComplement_transversePeriodic hδ
    hcarA.1 hcarA.2 hcarB.1 hcarB.2 hcarAne hcarBne hcarDisj hcarE hEper
    hcarBinv hgamma hcarPeriods.1 hpδ hp hpA
  have hellγδ : (ell : ℤ) • G.lattice.basis 1 ∉ δ := by
    intro hc
    apply hgamma
    have hellreal : (ell : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hell
    have hh := δ.smul_mem ((ell : ℝ)⁻¹) hc
    simpa only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast, smul_smul,
      inv_mul_cancel₀ hellreal, one_smul] using hh
  obtain ⟨n, hn, htransport⟩ := unionColumns_prescribed_transverse_multiple hδ
    (hpK.mono (fun _ hx => hBT hx)) hcol hcarBproper hellγδ htransverse
  obtain ⟨r, hr, GA, GB, hGB, hGA⟩ := columnCompanion_on_rescaled_lattice G k l hk
    hwithin hperiod hgamma n ell hn hell htransport
  obtain ⟨G', hG'⟩ := Tiling.RationalSlopes.mergeGoodParametrizations GA GB hGB.symm hdisj
  refine ⟨r, hr, G', ?_⟩
  intro j
  rw [hG']
  exact hGA j

end Tiling.Polygonal

namespace Tiling.RationalSlopes.PLPhase

open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Polygonal

private theorem lineFibre_eq_of_sub_mem
    (δ : Submodule ℝ Plane) (S : Set Plane) {s t : Plane} (hst : s - t ∈ δ) :
    lineFibre δ S s = lineFibre δ S t := by
  ext x
  constructor
  · rintro ⟨hxS, hxs⟩
    refine ⟨hxS, ?_⟩
    convert δ.add_mem hxs hst using 1
    abel
  · rintro ⟨hxS, hxt⟩
    refine ⟨hxS, ?_⟩
    convert δ.sub_mem hxt hst using 1
    abel


private theorem gamma_not_mem
    {K : PolygonalRegion} {T : Set Plane} (G : RationalSliceParametrization K T)
    (i : Fin G.numberOfParts) : G.lattice.basis 1 ∉ G.direction i := by
  intro hg
  have hk : (G.lambdaCoefficient i : ℝ) ≠ 0 := by
    exact_mod_cast G.lambdaCoefficient_ne_zero i
  have hl : G.lattice.basis 0 ∈ G.direction i := by
    apply (G.direction i).smul_mem_iff hk |>.mp
    have hm := (G.direction i).sub_mem (G.within_mem i)
      ((G.direction i).toAddSubgroup.zsmul_mem hg (G.gammaCoefficient i))
    simpa only [add_sub_cancel_right, Int.cast_smul_eq_zsmul] using hm
  let v : Fin 2 → G.direction i := fun j ↦ ⟨G.lattice.basis j, by
    fin_cases j
    · exact hl
    · exact hg⟩
  have hv : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (G.direction i).subtype G.lattice.independent
  have hd := hv.fintype_card_le_finrank
  rw [G.direction_dim] at hd
  simp only [Fintype.card_fin] at hd
  omega

private theorem toGood_lineSupported
    {K : PolygonalRegion} {T : Set Plane} (G : RationalSliceParametrization K T) :
    ∃ H : GoodParametrization K T, H.lattice = G.lattice ∧
      ∃ direction : Fin H.numberOfParts → Submodule ℝ Plane,
        (∀ i, Module.finrank ℝ (direction i) = 1) ∧
        (∀ i a m, IsLineSupported (H.atom i a m) (direction i)) ∧
        (⋃ i, ⋃ a : H.Index i, ⋃ m : ℤ,
          properVertices (regularSupport K (H.atom i a m))) =
            ⋃ i, ⋃ t ∈ G.part i,
              properVertices (regularSupport K (lineFibre (G.direction i) (G.part i) t)) := by
  classical
  let γ := G.lattice.basis 1
  let orbit : ∀ i : Fin G.numberOfParts, Setoid (G.part i) := fun i ↦ {
    r := fun x y ↦ ∃ m : ℤ, (x : Plane) - y - m • γ ∈ G.direction i
    iseqv := {
      refl := fun x ↦ ⟨0, by simp⟩
      symm := by
        rintro x y ⟨m, hm⟩
        refine ⟨-m, ?_⟩
        convert (G.direction i).neg_mem hm using 1
        module
      trans := by
        rintro x y z ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        convert (G.direction i).add_mem hm hn using 1
        module
    }
  }
  let Index := fun i ↦ Quotient (orbit i)
  let rep : ∀ i, Index i → Plane := fun i a ↦ (Quotient.out a : G.part i)
  let atom : ∀ i, Index i → ℤ → Set Plane := fun i a m ↦
    lineFibre (G.direction i) (G.part i) (rep i a + m • γ)
  have hrep (i) (a : Index i) : rep i a ∈ G.part i := (Quotient.out a).2
  have hphase (i) (a : Index i) (m : ℤ) :
      ∃ s ∈ G.part i, atom i a m = lineFibre (G.direction i) (G.part i) s ∧
        regularSupport K (atom i a m) =
          m • γ +ᵥ regularSupport K (atom i a 0) := by
    obtain ⟨s, hs, hline, hc⟩ := G.fibre_transport i (rep i a) (hrep i a) m
    have heq : atom i a m = lineFibre (G.direction i) (G.part i) s := by
      symm
      apply lineFibre_eq_of_sub_mem
      convert hline using 1
      abel
    refine ⟨s, hs, heq, ?_⟩
    rw [heq]
    simpa only [atom, zero_smul, add_zero] using hc
  refine ⟨{
    lattice := G.lattice
    numberOfParts := G.numberOfParts
    Index := Index
    atom := atom
    atom_nonempty := ?_
    atoms_disjoint := ?_
    union_eq := ?_
    lambdaCoefficient := G.lambdaCoefficient
    gammaCoefficient := G.gammaCoefficient
    lambdaCoefficient_ne_zero := G.lambdaCoefficient_ne_zero
    atom_periodic := ?_
    carrier_transport := ?_
  }, rfl, G.direction, G.direction_dim, ?_, ?_⟩
  · intro i a m
    obtain ⟨s, hs, heq, _⟩ := hphase i a m
    rw [heq]
    exact ⟨s, hs, by simp⟩
  · rintro ⟨i, a, m⟩ _ ⟨j, b, n⟩ _ hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    by_cases hij : i = j
    · subst j
      have hab : a = b := by
        apply Quotient.out_equiv_out.mp
        refine ⟨n - m, ?_⟩
        convert (G.direction i).sub_mem hy.2 hx.2 using 1
        module
      subst b
      have hmn : m = n := by
        have hmul : (m - n) • γ ∈ G.direction i := by
          convert (G.direction i).sub_mem hy.2 hx.2 using 1
          module
        by_contra hmn
        have hcast : ((m - n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn
        have hg : γ ∈ G.direction i := (G.direction i).smul_mem_iff hcast |>.mp (by
          simpa only [Int.cast_smul_eq_zsmul] using hmul)
        exact gamma_not_mem G i hg
      subst n
      exact hne rfl
    · exact Set.disjoint_left.mp
        (G.parts_disjoint (Set.mem_univ i) (Set.mem_univ j) hij) hx.1 hy.1
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hxi
      obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp hxa
      rw [← G.union_parts]
      exact Set.mem_iUnion.mpr ⟨i, hxm.1⟩
    · intro x hx
      rw [← G.union_parts] at hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      let a : Index i := Quotient.mk'' (⟨x, hxi⟩ : G.part i)
      obtain ⟨m, hm⟩ := Quotient.mk_out (s := orbit i) (⟨x, hxi⟩ : G.part i)
      refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨a,
        Set.mem_iUnion.mpr ⟨-m, hxi, ?_⟩⟩⟩
      convert (G.direction i).neg_mem hm using 1
      module
  · intro i a m
    obtain ⟨s, hs, heq, _⟩ := hphase i a m
    rw [heq]
    exact G.fibre_period i s hs
  · intro i a m
    exact (hphase i a m).choose_spec.2.2

  · intro i a m
    exact ⟨rep i a + m • γ, fun _ hx => hx.2⟩

  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨s, hs, heq, _⟩ := hphase i a m
      refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s,
        Set.mem_iUnion.mpr ⟨hs, ?_⟩⟩⟩
      simpa only [heq] using hx
    · intro x hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨ht, hx⟩ := Set.mem_iUnion.mp hx
      let a : Index i := Quotient.mk'' (⟨t, ht⟩ : G.part i)
      obtain ⟨m, hm⟩ := Quotient.mk_out (s := orbit i) (⟨t, ht⟩ : G.part i)
      have htAtom : t ∈ atom i a (-m) := by
        refine ⟨ht, ?_⟩
        convert (G.direction i).neg_mem hm using 1
        module
      have heq : atom i a (-m) = lineFibre (G.direction i) (G.part i) t := by
        dsimp only [atom]
        symm
        exact lineFibre_eq_of_sub_mem (G.direction i) (G.part i) htAtom.2
      refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨a,
        Set.mem_iUnion.mpr ⟨-m, ?_⟩⟩⟩
      simpa only [heq] using hx

private theorem period_iUnion {ι : Type} (S : ι → Set Plane) {q : Plane}
    (hq : ∀ i, q ∈ periodGroup (S i)) : q ∈ periodGroup (⋃ i, S i) := by
  change q +ᵥ (⋃ i, S i) = ⋃ i, S i
  rw [vadd_set_iUnion]
  congr 1
  funext i
  exact hq i

private theorem centrePeriod_cornerPeriod {K : PolygonalRegion} {S : Set Plane}
    {q : Plane} (hq : q ∈ periodGroup S) :
    q ∈ periodGroup (properVertices (regularSupport K S)) := by
  change q +ᵥ properVertices (regularSupport K S) = _
  change q +ᵥ S = S at hq
  rw [← properVertices_vadd, ← regularSupport_vadd, hq]

private theorem orbit_period (A : Set Plane) (γ : Plane) :
    γ ∈ periodGroup (⋃ m : ℤ, m • γ +ᵥ A) := by
  change γ +ᵥ (⋃ m : ℤ, m • γ +ᵥ A) = ⋃ m : ℤ, m • γ +ᵥ A
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, a, ha, rfl⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨m + 1, a, ha, by simp [add_smul, vadd_eq_add]; abel⟩
  · intro x hx
    obtain ⟨m, a, ha, rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨(m - 1) • γ + a, Set.mem_iUnion.mpr ⟨m - 1, a, ha, rfl⟩, ?_⟩
    simp [sub_smul, vadd_eq_add]
    abel

private theorem good_cornerWitness_periods
    {K : PolygonalRegion} {T : Set Plane} (G : GoodParametrization K T) :
    let W := ⋃ i, ⋃ a : G.Index i, ⋃ m : ℤ,
      properVertices (regularSupport K (G.atom i a m))
    G.lattice.basis 1 ∈ periodGroup W ∧
      (G.commonMultiple : ℤ) • G.lattice.basis 0 ∈ periodGroup W := by
  let Wi := fun i => ⋃ a : G.Index i, ⋃ m : ℤ,
    properVertices (regularSupport K (G.atom i a m))
  have hγi (i) : G.lattice.basis 1 ∈ periodGroup (Wi i) := by
    apply period_iUnion
    intro a
    have heq : (⋃ m : ℤ, properVertices (regularSupport K (G.atom i a m))) =
        ⋃ m : ℤ, m • G.lattice.basis 1 +ᵥ
          properVertices (regularSupport K (G.atom i a 0)) := by
      congr 1
      funext m
      rw [G.carrier_transport, properVertices_vadd]
    rw [heq]
    exact orbit_period _ _
  have hLambda (i) : (G.commonMultiple : ℤ) • G.lattice.basis 0 ∈ periodGroup (Wi i) := by
    have hp : G.lambdaCoefficient i • G.lattice.basis 0 +
        G.gammaCoefficient i • G.lattice.basis 1 ∈ periodGroup (Wi i) := by
      apply period_iUnion
      intro a
      apply period_iUnion
      intro m
      exact centrePeriod_cornerPeriod (G.atom_periodic i a m)
    obtain ⟨d, hd⟩ := G.commonMultiple_divisible i
    have h := (periodGroup (Wi i)).sub_mem
      ((periodGroup (Wi i)).zsmul_mem hp d)
      ((periodGroup (Wi i)).zsmul_mem (hγi i) (d * G.gammaCoefficient i))
    convert h using 1
    rw [hd]
    module
  exact ⟨period_iUnion Wi hγi, period_iUnion Wi hLambda⟩

private theorem rationalSlice_rescale_basis
    {K : PolygonalRegion} {T : Set Plane} (G : RationalSliceParametrization K T)
    (r : ℕ) (hr : 0 < r) :
    ∃ H : RationalSliceParametrization K T,
      (∀ j : Fin 2, H.lattice.basis j = (r : ℤ) • G.lattice.basis j) ∧
        (⋃ i, ⋃ t ∈ H.part i,
          properVertices (regularSupport K (lineFibre (H.direction i) (H.part i) t))) =
            ⋃ i, ⋃ t ∈ G.part i,
              properVertices (regularSupport K (lineFibre (G.direction i) (G.part i) t)) := by
  let b : Fin 2 → Plane := fun j => (r : ℤ) • G.lattice.basis j
  have hrreal : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hb : LinearIndependent ℝ b := by
    have h := G.lattice.independent.units_smul (fun _ : Fin 2 => Units.mk0 (r : ℝ) hrreal)
    have hreal : LinearIndependent ℝ (fun j => (r : ℝ) • G.lattice.basis j) := by
      convert h using 1
      ext j
      simp
    convert hreal using 1
    funext j
    exact (Int.cast_smul_eq_zsmul ℝ _ _).symm
  let L : PlanarLattice := ⟨b, hb⟩
  let H : RationalSliceParametrization K T := {
    lattice := L
    basis_rational := by
      intro j
      obtain ⟨q, hq⟩ := G.basis_rational j
      refine ⟨fun k => (r : ℚ) * q k, ?_⟩
      change (r : ℤ) • G.lattice.basis j = _
      rw [hq]
      apply Complex.ext <;> simp
    numberOfParts := G.numberOfParts
    part := G.part
    part_nonempty := G.part_nonempty
    parts_disjoint := G.parts_disjoint
    union_parts := G.union_parts
    direction := G.direction
    direction_dim := G.direction_dim
    lambdaCoefficient := G.lambdaCoefficient
    gammaCoefficient := G.gammaCoefficient
    lambdaCoefficient_ne_zero := G.lambdaCoefficient_ne_zero
    within_mem := by
      intro i
      have heq : G.lambdaCoefficient i • L.basis 0 +
          G.gammaCoefficient i • L.basis 1 =
          (r : ℤ) • (G.lambdaCoefficient i • G.lattice.basis 0 +
            G.gammaCoefficient i • G.lattice.basis 1) := by
        change G.lambdaCoefficient i • ((r : ℤ) • G.lattice.basis 0) +
          G.gammaCoefficient i • ((r : ℤ) • G.lattice.basis 1) = _
        module
      rw [heq]
      exact (G.direction i).toAddSubgroup.zsmul_mem (G.within_mem i) (r : ℤ)
    fibre_period := by
      intro i t ht
      convert (periodGroup (lineFibre (G.direction i) (G.part i) t)).zsmul_mem
        (G.fibre_period i t ht) (r : ℤ) using 1
      change G.lambdaCoefficient i • ((r : ℤ) • G.lattice.basis 0) +
        G.gammaCoefficient i • ((r : ℤ) • G.lattice.basis 1) = _
      module
    fibre_transport := by
      intro i t ht m
      obtain ⟨s, hs, hdir, hcarrier⟩ := G.fibre_transport i t ht (m * (r : ℤ))
      refine ⟨s, hs, ?_, ?_⟩
      · change s - t - m • ((r : ℤ) • G.lattice.basis 1) ∈ G.direction i
        simpa only [mul_smul] using hdir
      · change regularSupport K (lineFibre (G.direction i) (G.part i) s) =
          m • ((r : ℤ) • G.lattice.basis 1) +ᵥ
            regularSupport K (lineFibre (G.direction i) (G.part i) t)
        simpa only [mul_smul] using hcarrier
  }
  exact ⟨H, fun _ => rfl, rfl⟩

private theorem rescaled_phase_with_periodicWitnessCloud
    {K : PolygonalRegion} {T : Set Plane} (G : RationalSliceParametrization K T)
    (C : ℝ)
    (hdense : ∀ x : Plane, ∃ v ∈ (⋃ i, ⋃ t ∈ G.part i,
      properVertices (regularSupport K (lineFibre (G.direction i) (G.part i) t))),
        dist x v < C) :
    ∃ H : GoodParametrization K T,
      (∃ direction : Fin H.numberOfParts → Submodule ℝ Plane,
        (∀ i, Module.finrank ℝ (direction i) = 1) ∧
          ∀ i a m, IsLineSupported (H.atom i a m) (direction i)) ∧
      let W := ⋃ i, ⋃ a : H.Index i, ⋃ m : ℤ,
        properVertices (regularSupport K (H.atom i a m))
      (∀ x : Plane, ∃ v ∈ W, dist x v < C) ∧
        (H.lattice.toAddSubgroup : Set Plane) ⊆ periodGroup W := by
  classical
  obtain ⟨H₀, hH₀, _, _, _, hW₀⟩ := toGood_lineSupported G
  let N := H₀.commonMultiple
  have hN : 0 < N := H₀.commonMultiple_pos
  obtain ⟨G₁, hG₁, hwhole⟩ := rationalSlice_rescale_basis G N hN
  obtain ⟨H, hH, direction, hdim, hline, hW⟩ := toGood_lineSupported G₁
  let W₀ := ⋃ i, ⋃ a : H₀.Index i, ⋃ m : ℤ,
    properVertices (regularSupport K (H₀.atom i a m))
  let W := ⋃ i, ⋃ a : H.Index i, ⋃ m : ℤ,
    properVertices (regularSupport K (H.atom i a m))
  have hWW₀ : W = W₀ := hW.trans (hwhole.trans hW₀.symm)
  have hperiods : H₀.lattice.basis 1 ∈ periodGroup W₀ ∧
      (N : ℤ) • H₀.lattice.basis 0 ∈ periodGroup W₀ :=
    good_cornerWitness_periods H₀
  have hb (j : Fin 2) : H.lattice.basis j = (N : ℤ) • H₀.lattice.basis j := by
    rw [hH, hH₀]
    exact hG₁ j
  refine ⟨H, ⟨direction, hdim, hline⟩, ?_, ?_⟩
  · intro x
    change ∃ v ∈ W, dist x v < C
    rw [show W = (⋃ i, ⋃ t ∈ G.part i,
      properVertices (regularSupport K (lineFibre (G.direction i) (G.part i) t))) from
        hW.trans hwhole]
    exact hdense x
  · change AddSubgroup.closure (Set.range H.lattice.basis) ≤ periodGroup W
    apply (AddSubgroup.closure_le _).mpr
    rintro p ⟨j, rfl⟩
    rw [hWW₀, hb j]
    fin_cases j
    · exact hperiods.2
    · exact (periodGroup W₀).zsmul_mem hperiods.1 N

end Tiling.RationalSlopes.PLPhase

namespace Tiling.RationalSlopes

open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Polygonal

-- Sole remaining density declaration from FiniteTestDensity.lean.
open Tiling.Approximation (IsFiniteApproximation deformPoint)
open Tiling.RationalSlopes.Approximation (PolyhedralCode polyhedralSupport deformedPolyhedralSupport)

private theorem normalDirection_mem_iff (n : Tiling.Approximation.RationalNormal)
    (z : Plane) : z ∈ Tiling.Approximation.normalDirection n ↔
      Tiling.Approximation.normalEval n z = 0 := by
  rfl

/-- This reflects only the bounded centre comparisons used in a local corner germ.
It makes no claim that the inverse image of an arbitrary real line is a line. -/
private theorem bounded_normalReflection_fibre_membership
    {T : Set Plane} (φ : ℝ →ₗ[ℚ] ℚ) (n : Tiling.Approximation.RationalNormal)
    {δ : Submodule ℝ Plane} (hn : Tiling.Approximation.normalDirection n = δ)
    {s t : Plane} (_hs : s ∈ T) (ht : t ∈ T)
    (hreflect :
      Tiling.Approximation.normalEval n (deformPoint φ t - deformPoint φ s) = 0 ↔
        Tiling.Approximation.normalEval n (t - s) = 0) :
    deformPoint φ t ∈ lineFibre δ (deformPoint φ '' T) (deformPoint φ s) ↔
      t ∈ lineFibre δ T s := by
  change (deformPoint φ t ∈ deformPoint φ '' T ∧
    deformPoint φ t - deformPoint φ s ∈ δ) ↔ (t ∈ T ∧ t - s ∈ δ)
  rw [← hn, normalDirection_mem_iff, normalDirection_mem_iff, hreflect]
  exact and_congr_left (fun _ => iff_of_true (Set.mem_image_of_mem _ ht) ht)

private theorem boundaryDirection_finrank_eq_one
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} (hδ : HasBoundaryDirection K δ) :
    Module.finrank ℝ δ = 1 := by
  obtain ⟨a, b, hab, _, rfl⟩ := hδ
  exact finrank_span_singleton (sub_ne_zero.mpr hab.symm)

private theorem finiteDecoration_uniformImageBound (W : Finset Plane) :
    ∃ F : Finset ℝ, ∃ B : ℝ, 0 < B ∧ ∀ φ : ℝ →ₗ[ℚ] ℚ,
      IsFiniteApproximation F 1 φ → ∀ w ∈ W, ‖deformPoint φ w‖ ≤ B := by
  let F := W.image Complex.re ∪ W.image Complex.im
  let B := 2 * (∑ w ∈ W, ‖w‖) + 3
  refine ⟨F, B, by dsimp [B]; positivity, ?_⟩
  intro φ hφ w hw
  have hre := hφ.2 w.re (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨w, hw, rfl⟩)))
  have him := hφ.2 w.im (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨w, hw, rfl⟩)))
  have hreBound : |(φ w.re : ℝ)| ≤ |w.re| + 1 := by
    calc
      |(φ w.re : ℝ)| = |((φ w.re : ℝ) - w.re) + w.re| := by congr 1; ring
      _ ≤ |(φ w.re : ℝ) - w.re| + |w.re| := abs_add_le _ _
      _ ≤ |w.re| + 1 := by linarith
  have himBound : |(φ w.im : ℝ)| ≤ |w.im| + 1 := by
    calc
      |(φ w.im : ℝ)| = |((φ w.im : ℝ) - w.im) + w.im| := by congr 1; ring
      _ ≤ |(φ w.im : ℝ) - w.im| + |w.im| := abs_add_le _ _
      _ ≤ |w.im| + 1 := by linarith
  have hnorm := Complex.norm_le_abs_re_add_abs_im (deformPoint φ w)
  change ‖deformPoint φ w‖ ≤ |(φ w.re : ℝ)| + |(φ w.im : ℝ)| at hnorm
  have hsum : ‖w‖ ≤ ∑ w ∈ W, ‖w‖ :=
    Finset.single_le_sum (fun u _ => norm_nonneg u) hw
  dsimp only [B]
  linarith [Complex.abs_re_le_norm w, Complex.abs_im_le_norm w]

private theorem lineFibre_eq_of_mem {T : Set Plane} {δ : Submodule ℝ Plane}
    {s u : Plane} (hu : u ∈ lineFibre δ T s) : lineFibre δ T u = lineFibre δ T s := by
  ext t
  constructor
  · intro ht
    refine ⟨ht.1, ?_⟩
    simpa only [sub_add_sub_cancel] using δ.add_mem ht.2 hu.2
  · intro ht
    refine ⟨ht.1, ?_⟩
    simpa only [sub_sub_sub_cancel_right] using δ.sub_mem ht.2 hu.2

/-- PL owner. Local normal reflection aligns whole image fibres with the transported
source fibres near their corners. All radii are chosen before the scalar map. -/
theorem flcDeformation_uniformWholeFibreCornerDensity
    {K : PolygonalRegion} {T E : Set Plane}
    (hK : Tiling.RationalSlopes.HasRationalSlopes K)
    (hTne : T.Nonempty) (hFLC : HasFLC T) (htile : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (hEper : IsLatticePeriodic E)
    (hdense : ∃ R : ℝ, 0 < R ∧ ∀ δ : Submodule ℝ Plane,
      HasBoundaryDirection K δ → ∀ x : Plane,
        ∃ v ∈ fibreProperVertices K T δ, dist x v < R)
    (P : PolyhedralCode) (hP : polyhedralSupport P = K.support) :
    ∃ F : Finset ℝ, ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ →
          ∀ δ : Submodule ℝ Plane, HasBoundaryDirection K δ → ∀ x : Plane,
            ∃ v ∈ fibreProperVertices Kφ (deformPoint φ '' T) δ,
              dist x v < C := by
  classical
  obtain ⟨R, hR, hcorners⟩ := hdense
  have hcarrierE := regularSupport_eq_of_tilesOn hEopen hEregular htile
  have hrelative := periodicCarrier_centresRelativeDense K T (regularSupport K T)
    (by rw [hcarrierE]; exact htile) hTne (by rw [hcarrierE]; exact hEopen)
    (by rw [hcarrierE]; exact hEper)
  obtain ⟨Fi, εi, ρ, hεi, hρ, himageDense⟩ :=
    Approximation.approximation_uniformImageDensity T hFLC hrelative
  obtain ⟨Q, hQ, W, hW, hWzero, Fq, εq, hεq, hpolygon⟩ :=
    Approximation.rationalPolygon_construction K hK
  have hWne : W.Nonempty := ⟨0, hWzero⟩
  have hcloudFLC : HasFLC (Approximation.decoratedCloud W T) := by
    simpa only [Approximation.decoratedCloud, add_comm] using hFLC.add_finset W
  have hTcloud : T ⊆ Approximation.decoratedCloud W T := by
    intro t ht
    exact Set.mem_add.mpr ⟨0, hWzero, t, ht, zero_add t⟩
  have hcloudDense : RelativeDense (Approximation.decoratedCloud W T) := by
    obtain ⟨ρ₀, hρ₀, hdense₀⟩ := hrelative
    exact ⟨ρ₀, hρ₀, fun x => by
      obtain ⟨t, ht, hdist⟩ := hdense₀ x
      exact ⟨t, hTcloud ht, hdist⟩⟩
  obtain ⟨Fe, εe, hεe, herror⟩ := Approximation.approximation_globalRelativeError
    (Approximation.decoratedCloud W T) hcloudFLC hcloudDense (1 / 2)
      (by norm_num) (by norm_num)
  obtain ⟨Fg, εg, hεg, hgerms⟩ := Approximation.flcAllSubfamilyGerms
    K P W T hP hWne hFLC hrelative htile.2.1
  obtain ⟨Fc, εc, hεc, hcodes⟩ :=
    Approximation.polyhedralDeformation_independentOfCode K P Q hP hQ
  let D := (boundaryDirections_finite K).toFinset
  have hnormals : ∀ δ ∈ D, ∃ n : Tiling.Approximation.RationalNormal,
      Tiling.Approximation.normalDirection n = δ := by
    intro δ hδ
    have hb : HasBoundaryDirection K δ := by
      simpa only [D, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hδ
    exact Approximation.rationalDirection_hasNormal δ (boundaryDirection_finrank_eq_one hb)
      (hasRationalDirection_of_hasBoundaryDirection hK hb)
  obtain ⟨Pb, hPb, Wb, hWb, hWbzero, B, L, hB, hL, Fb, εb, hεb, hboundary⟩ :=
    Approximation.rationalPolygon_uniformBoundaryControl K hK
  obtain ⟨Fbc, εbc, hεbc, hboundCodes⟩ :=
    Approximation.polyhedralDeformation_independentOfCode K P Pb hP hPb
  obtain ⟨Fv, BV, hBV, hdecorationBound⟩ := finiteDecoration_uniformImageBound W
  obtain ⟨Fp, εp, hεp, hpacking⟩ :=
    Approximation.flcPackingTransport K P T hP hFLC hrelative htile.2.1
  let normal : {δ : Submodule ℝ Plane // δ ∈ D} → Tiling.Approximation.RationalNormal :=
    fun d => Classical.choose (hnormals d.val d.property)
  let normals := D.attach.image normal
  let M := 4 * (B + BV + 2)
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨Fm, εm, hεm, hmetric⟩ :=
    Approximation.approximation_boundedMetricAndRelationControl
      (Approximation.decoratedCloud W T) hcloudFLC hcloudDense M 1 normals hM (by norm_num)
  let F := Fi ∪ Fq ∪ Fe ∪ Fg ∪ Fc ∪ Fb ∪ Fbc ∪ Fv ∪ Fp ∪ Fm
  let ε := min (min (min (min (min (min (min (min (min (εi) (εq)) (εe)) (εg)) (εc)) (εb)) (εbc)) (1)) (εp)) (εm)
  have hε : 0 < ε := by
    simp only [ε, lt_min_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hεi, hεq⟩, hεe⟩, hεg⟩, hεc⟩, hεb⟩, hεbc⟩, by norm_num⟩, hεp⟩, hεm⟩
  refine ⟨F, ε, ρ + 2 * R + 1, hε, by positivity, ?_⟩
  intro φ hφ Kφ hKφ δ hbδ x
  have hφi := Tiling.Approximation.finiteApproximation_strengthen Fi F εi ε φ
    (by intro y hy; simp only [F, Finset.mem_union]; tauto)
    (by simp [ε]) hφ
  have hφq := Tiling.Approximation.finiteApproximation_strengthen Fq F εq ε φ
    (by intro y hy; simp only [F, Finset.mem_union]; tauto)
    (by simp [ε]) hφ
  have hφe := Tiling.Approximation.finiteApproximation_strengthen Fe F εe ε φ
    (by intro y hy; simp only [F, Finset.mem_union]; tauto)
    (by simp [ε]) hφ
  have hφg := Tiling.Approximation.finiteApproximation_strengthen Fg F εg ε φ
    (by intro y hy; simp only [F, Finset.mem_union]; tauto)
    (by simp [ε]) hφ
  have hφc := Tiling.Approximation.finiteApproximation_strengthen Fc F εc ε φ
    (by intro y hy; simp only [F, Finset.mem_union]; tauto)
    (by simp [ε]) hφ
  have hφb := Tiling.Approximation.finiteApproximation_strengthen Fb F εb ε φ
    (by intro y hy; simp only [F, Finset.mem_union]; tauto)
    (by simp [ε]) hφ
  have hφbc := Tiling.Approximation.finiteApproximation_strengthen Fbc F εbc ε φ
    (by intro y hy; simp only [F, Finset.mem_union]; tauto)
    (by simp [ε]) hφ
  have hφv := Tiling.Approximation.finiteApproximation_strengthen Fv F 1 ε φ
    (by intro y hy; simp only [F, Finset.mem_union]; tauto)
    (by simp [ε]) hφ
  have hφp := Tiling.Approximation.finiteApproximation_strengthen Fp F εp ε φ
    (by intro y hy; simp only [F, Finset.mem_union]; tauto)
    (by simp [ε]) hφ
  have hφm := Tiling.Approximation.finiteApproximation_strengthen Fm F εm ε φ
    (by intro y hy; simp only [F, Finset.mem_union]; tauto)
    (by simp [ε]) hφ
  obtain ⟨Kq, hKq, _, _, hWφ, _⟩ := hpolygon φ hφq
  have hKqφ : Kq = Kφ := Tiling.Polygonal.polygonalRegion_eq_of_support_eq
    (hKq.trans ((hcodes φ hφc).symm.trans hKφ.symm))
  subst Kq
  obtain ⟨Kb, hKb, hbound, _, _⟩ := hboundary φ hφb
  have hKbφ : Kb = Kφ := Tiling.Polygonal.polygonalRegion_eq_of_support_eq
    (hKb.trans ((hboundCodes φ hφbc).symm.trans hKφ.symm))
  subst Kb
  obtain ⟨hpackingφ, _⟩ := hpacking φ hφp Kφ hKφ
  obtain ⟨_, _, _, hnormalReflection⟩ := hmetric φ hφm
  have hδD : δ ∈ D := by
    simpa only [D, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hbδ
  let d : {δ : Submodule ℝ Plane // δ ∈ D} := ⟨δ, hδD⟩
  let n := normal d
  have hn : Tiling.Approximation.normalDirection n = δ :=
    Classical.choose_spec (hnormals δ hδD)
  have hnmem : n ∈ normals :=
    Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩
  obtain ⟨ft, ⟨t, ht, rfl⟩, hxt⟩ := himageDense φ hφi x
  obtain ⟨v, hv, htv⟩ := hcorners δ hbδ t
  obtain ⟨s, hvS⟩ := Set.mem_iUnion.mp hv
  have hpS : IsPacking K.prototileFamily (K.placements (lineFibre δ T s)) :=
    htile.2.1.mono (fun _ ht => ht.1)
  obtain ⟨a, ha, u, hu, hvu⟩ := properVertexProvenance hpS v hvS
  have haW : a ∈ W := Approximation.decorates_intrinsicVertices K W hW ha
  have huT : u ∈ T := hu.1
  have hSu := lineFibre_eq_of_mem hu
  have hvSu : v ∈ properVertices (regularSupport K (lineFibre δ T u)) := by
    rw [hSu]
    exact hvS
  have hvCloud : v ∈ Approximation.decoratedCloud W T := by
    rw [hvu]
    exact Set.mem_add.mpr ⟨a, haW, u, huT, rfl⟩
  have hsub : lineFibre δ T u ⊆ T := fun _ ht => ht.1
  have hsubImage : deformPoint φ '' lineFibre δ T u ⊆ deformPoint φ '' T := by
    rintro _ ⟨t, ht, rfl⟩
    exact Set.mem_image_of_mem _ ht.1
  have hpSu : IsPacking K.prototileFamily (K.placements (lineFibre δ T u)) :=
    htile.2.1.mono (fun _ ht => ht.1)
  have hpImageSu : IsPacking Kφ.prototileFamily
      (Kφ.placements (deformPoint φ '' lineFibre δ T u)) :=
    hpackingφ.mono (fun _ ht => hsubImage ht)
  have hsourceGerms : ∀ z ∈ Approximation.decoratedCloud W (lineFibre δ T u),
      SameGermAt (regularSupport K (lineFibre δ T u)) z
        (regularSupport Kφ (deformPoint φ '' lineFibre δ T u)) (deformPoint φ z) := by
    intro z hz
    apply hgerms φ hφg Kφ hKφ (lineFibre δ T u) hsub z
    obtain ⟨w, hw, t, ht, rfl⟩ := Set.mem_add.mp hz
    exact Set.mem_add.mpr ⟨w, hw, t, ht.1, rfl⟩
  have hvertexTransport := Approximation.decoratedProperVertices_transport
    K Kφ W (lineFibre δ T u) φ hW hWφ hpSu hpImageSu hsourceGerms
  have hvImage : deformPoint φ v ∈
      properVertices (regularSupport Kφ (deformPoint φ '' lineFibre δ T u)) := by
    rw [hvertexTransport]
    exact Set.mem_image_of_mem _ hvSu
  have hforward : deformPoint φ '' lineFibre δ T u ⊆
      lineFibre δ (deformPoint φ '' T) (deformPoint φ u) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨Set.mem_image_of_mem _ hz.1, ?_⟩
    rw [← hn] at hz ⊢
    exact Tiling.Approximation.rationalDirection_preservesCoset φ n z u hz.2
  have hfvfu : dist (deformPoint φ v) (deformPoint φ u) ≤ BV := by
    rw [hvu]
    change dist (Tiling.Approximation.deformPointLinear φ (a + u))
      (Tiling.Approximation.deformPointLinear φ u) ≤ BV
    rw [map_add]
    simp only [dist_eq_norm, add_sub_cancel_right]
    change ‖deformPoint φ a‖ ≤ BV
    exact hdecorationBound φ hφv a haW
  have hlocal : ∀ z ∈ lineFibre δ (deformPoint φ '' T) (deformPoint φ u),
      dist z (deformPoint φ v) < B + 1 →
        z ∈ deformPoint φ '' lineFibre δ T u := by
    intro z hz hzv
    obtain ⟨z₀, hz₀, rfl⟩ := hz.1
    have hzfu : dist (deformPoint φ z₀) (deformPoint φ u) < M / 2 := by
      have htri := dist_triangle (deformPoint φ z₀) (deformPoint φ v) (deformPoint φ u)
      dsimp only [M]
      linarith
    have hreflection := hnormalReflection z₀ (hTcloud hz₀) u (hTcloud huT) hzfu n hnmem
    have htarget : Tiling.Approximation.normalEval n
        (deformPoint φ z₀ - deformPoint φ u) = 0 := by
      apply (normalDirection_mem_iff n _).mp
      rw [hn]
      exact hz.2
    have hsource : z₀ - u ∈ δ := by
      rw [← hn, normalDirection_mem_iff]
      exact hreflection.mp htarget
    exact Set.mem_image_of_mem _ ⟨hz₀, hsource⟩
  have hpWhole : IsPacking Kφ.prototileFamily
      (Kφ.placements (lineFibre δ (deformPoint φ '' T) (deformPoint φ u))) :=
    hpackingφ.mono (fun _ ht => ht.1)
  have hfibreGerm := Tiling.Polygonal.regularSupport_germ_of_local_centres
    hbound hpWhole hforward hlocal
  have hvWhole : deformPoint φ v ∈ properVertices
      (regularSupport Kφ (lineFibre δ (deformPoint φ '' T) (deformPoint φ u))) :=
    (isProperVertex_iff_of_eventuallyEq hfibreGerm).mp hvImage
  refine ⟨deformPoint φ v, Set.mem_iUnion.mpr
    ⟨⟨deformPoint φ u, Set.mem_image_of_mem _ huT⟩, hvWhole⟩, ?_⟩
  have herrorvt := herror φ hφe v hvCloud t (hTcloud ht)
  have hdistvt : dist (deformPoint φ v) (deformPoint φ t) < 2 * R := by
    calc
      dist (deformPoint φ v) (deformPoint φ t) =
          ‖Tiling.Approximation.deformPointLinear φ (v - t)‖ := by
        rw [map_sub]
        exact dist_eq_norm _ _
      _ ≤ ‖deformPoint φ (v - t) - (v - t)‖ + ‖v - t‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ (1 / 2) * dist v t + dist v t :=
        by simpa only [dist_eq_norm] using add_le_add herrorvt (le_refl ‖v - t‖)
      _ < 2 * R := by rw [dist_comm] at htv; linarith
  have htri := dist_triangle x (deformPoint φ t) (deformPoint φ v)
  rw [dist_comm (deformPoint φ t) (deformPoint φ v)] at htri
  linarith

end Tiling.RationalSlopes

 namespace Tiling.Polygonal

private theorem sameGerm_lift_translation
    (f : Plane →ₗ[ℚ] Plane) {A B Aφ Bφ : Set Plane} {v q : Plane}
    (hA : SameGermAt A v Aφ (f v))
    (hB : SameGermAt B (v + q) Bφ (f (v + q)))
    (htransport : Bφ = f q +ᵥ Aφ) : SameGermAt A v B (v + q) := by
  have hA' : A =ᶠ[𝓝 v] (v - f v) +ᵥ Aφ := hA
  have hB' : B =ᶠ[𝓝 (v + q)] (v + q - f (v + q)) +ᵥ Bφ := hB
  have htendsto : Tendsto (fun x : Plane => x + q) (𝓝 v) (𝓝 (v + q)) :=
    (continuous_id.add continuous_const).tendsto v
  have hpull := hB'.comp_tendsto htendsto
  filter_upwards [hA', hpull] with x hx hy
  apply propext
  change (x ∈ A) ↔ x ∈ (v - (v + q)) +ᵥ B
  have hmask : (x + q ∈ (v + q - f (v + q)) +ᵥ Bφ) ↔
      x ∈ (v - f v) +ᵥ Aφ := by
    rw [htransport, map_add]
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    rw [show -f q + (-(v + q - (f v + f q)) + (x + q)) =
      -(v - f v) + x by abel]
  have htarget : (x ∈ (v - (v + q)) +ᵥ B) ↔ x + q ∈ B := by
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    rw [show -(v - (v + q)) + x = x + q by abel]
  exact (Iff.of_eq hx).trans (((Iff.of_eq hy).trans hmask).symm.trans htarget.symm)

end Tiling.Polygonal

namespace Tiling.Polygonal

private theorem witnessSubset_translation_of_image
    (f : Plane →ₗ[ℚ] Plane) {P W A B : Set Plane} {q : Plane}
    (hW : W ⊆ P) (hA : A ⊆ W) (hB : B ⊆ W)
    (hinj : Set.InjOn f P) (hq : q ∈ periodGroup W)
    (himage : f '' B = f q +ᵥ (f '' A)) : q +ᵥ A = B := by
  have hperiod : q +ᵥ W = W := AddAction.mem_stabilizer_iff.mp hq
  have htranslated {a : Plane} (ha : a ∈ A) : q + a ∈ W :=
    hperiod ▸ (show q + a ∈ q +ᵥ W from ⟨a, hA ha, rfl⟩)
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    have hf : f (q + a) ∈ f '' B := by
      rw [himage, map_add]
      exact ⟨f a, Set.mem_image_of_mem f ha, rfl⟩
    obtain ⟨b, hb, hfb⟩ := hf
    have heq : b = q + a := hinj (hW (hB hb)) (hW (htranslated ha)) hfb
    simpa only [vadd_eq_add, ← heq] using hb
  · intro b hb
    have hf : f b ∈ f q +ᵥ (f '' A) := himage ▸ Set.mem_image_of_mem f hb
    obtain ⟨fa, ⟨a, ha, hfa⟩, hfb⟩ := hf
    have heq : b = q + a := hinj (hW (hB hb)) (hW (htranslated ha)) (by
      rw [map_add, hfa]
      exact hfb.symm)
    exact ⟨a, ha, by simpa only [vadd_eq_add] using heq.symm⟩

private theorem sourceAtoms_image_and_partition
    {ι : Type} (f : Plane →ₗ[ℚ] Plane) {T : Set Plane} (atom : ι → Set Plane)
    (hNonempty : ∀ i, (atom i).Nonempty)
    (hDisjoint : Set.PairwiseDisjoint Set.univ atom)
    (hUnion : (⋃ i, atom i) = f '' T) :
    (∀ i, f '' (T ∩ f ⁻¹' atom i) = atom i) ∧
      (∀ i, (T ∩ f ⁻¹' atom i).Nonempty) ∧
      Set.PairwiseDisjoint Set.univ (fun i => T ∩ f ⁻¹' atom i) ∧
        (⋃ i, T ∩ f ⁻¹' atom i) = T := by
  have hImage (i : ι) : f '' (T ∩ f ⁻¹' atom i) = atom i := by
    apply Set.Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ht.2
    · intro z hz
      have hzT : z ∈ f '' T := hUnion ▸ Set.mem_iUnion.mpr ⟨i, hz⟩
      obtain ⟨t, ht, rfl⟩ := hzT
      exact ⟨t, ⟨ht, hz⟩, rfl⟩
  refine ⟨hImage, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨z, hz⟩ := hNonempty i
    rw [← hImage i] at hz
    obtain ⟨t, ht, _⟩ := hz
    exact ⟨t, ht⟩
  · intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    exact Set.disjoint_left.mp (hDisjoint hi hj hij) hti.2 htj.2
  · ext t
    constructor
    · intro ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
      exact hi.1
    · intro ht
      have hf : f t ∈ ⋃ i, atom i := hUnion.symm ▸ Set.mem_image_of_mem f ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hf
      exact Set.mem_iUnion.mpr ⟨i, ht, hi⟩

end Tiling.Polygonal

namespace Tiling.RationalSlopes

open Tiling.Approximation Tiling.Polygonal


private theorem bounded_normalDisplacementReflection
    (Y : Set Plane) (hY : HasFLC Y) (hdense : RelativeDense Y)
    (M : ℝ) (hM : 0 < M) (normals : Finset RationalNormal) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ∀ d ∈ Y,
          dist (deformPoint φ a) (deformPoint φ b) < M / 2 →
          dist (deformPoint φ c) (deformPoint φ d) < M / 2 →
            ∀ n ∈ normals,
              normalEval n (deformPoint φ a - deformPoint φ b) =
                normalEval n (deformPoint φ c - deformPoint φ d) ↔
                  normalEval n (a - b) = normalEval n (c - d) := by
  classical
  obtain ⟨F₀, ε₀, hε₀, hcontrol⟩ := Approximation.approximation_boundedMetricAndRelationControl
    Y hY hdense M 1 normals hM zero_lt_one
  have hfinite := hY.2 M hM
  let D := hfinite.toFinset
  let Z := normals.biUnion (fun n => D.image (normalEval n))
  obtain ⟨F₁, ε₁, hε₁, hequality⟩ := finiteApproximation_signAndEquality Z
  let F := F₀ ∪ F₁
  let ε := min ε₀ ε₁
  refine ⟨F, ε, lt_min hε₀ hε₁, ?_⟩
  intro φ hφ a ha b hb c hc d hd hab hcd n hn
  have hφ₀ : IsFiniteApproximation F₀ ε₀ φ := finiteApproximation_strengthen F₀ F ε₀ ε φ
    (Finset.subset_union_left) (min_le_left _ _) hφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := finiteApproximation_strengthen F₁ F ε₁ ε φ
    (Finset.subset_union_right) (min_le_right _ _) hφ
  have hinverse := (hcontrol φ hφ₀).2.2.1
  have hDmem {u v : Plane} (hu : u ∈ Y) (hv : v ∈ Y)
      (huv : dist (deformPoint φ u) (deformPoint φ v) < M / 2) : u - v ∈ D := by
    apply hfinite.mem_toFinset.mpr
    refine ⟨⟨u, hu, v, hv, rfl⟩, ?_⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using (hinverse u hu v hv huv).le
  have hZab : normalEval n (a - b) ∈ Z := Finset.mem_biUnion.mpr
    ⟨n, hn, Finset.mem_image.mpr ⟨a - b, hDmem ha hb hab, rfl⟩⟩
  have hZcd : normalEval n (c - d) ∈ Z := Finset.mem_biUnion.mpr
    ⟨n, hn, Finset.mem_image.mpr ⟨c - d, hDmem hc hd hcd, rfl⟩⟩
  have habMap : deformPoint φ (a - b) = deformPoint φ a - deformPoint φ b :=
    (deformPointLinear φ).map_sub a b
  have hcdMap : deformPoint φ (c - d) = deformPoint φ c - deformPoint φ d :=
    (deformPointLinear φ).map_sub c d
  rw [← habMap, ← hcdMap, rationalNormal_commutes, rationalNormal_commutes]
  simpa only [Rat.cast_inj] using (hequality φ hφ₁).2 _ hZab _ hZcd

end Tiling.RationalSlopes

namespace Tiling.RationalSlopes

open Tiling.Approximation Tiling.Polygonal


/-- Two bounded pairs of genuine labelled source witnesses identify the source phase
of a complete image line. No inverse of the deformation on arbitrary points is used. -/
private theorem line_phase_of_labelled_density
    (φ : ℝ →ₗ[ℚ] ℚ) (n : RationalNormal) (Y W : Set Plane)
    (hWY : W ⊆ Y) (a b q : Plane) (hq : q ∈ periodGroup W)
    (C G : ℝ) (hG : 0 < G)
    (hdense : ∀ z : Plane, ∃ w ∈ W, dist z (deformPoint φ w) < C)
    (hlabel : ∃ v ∈ Y, normalEval n v = normalEval n a)
    (hcloud : ∀ z : Plane, normalEval n z = normalEval n (deformPoint φ b) →
      ∃ u ∈ Y, normalEval n u = normalEval n b ∧
        dist z (deformPoint φ u) < G)
    (hphase : normalEval n (deformPoint φ b) =
      normalEval n (deformPoint φ a + deformPoint φ q))
    (hreflect : ∀ u ∈ Y, ∀ w ∈ Y, ∀ v ∈ Y, ∀ t ∈ Y,
      dist (deformPoint φ u) (deformPoint φ w) < C + G →
      dist (deformPoint φ v) (deformPoint φ t) < C + G →
      normalEval n (deformPoint φ u - deformPoint φ w) =
        normalEval n (deformPoint φ v - deformPoint φ t) →
      normalEval n (u - w) = normalEval n (v - t)) :
    normalEval n b = normalEval n (a + q) := by
  obtain ⟨v, hv, hvlevel⟩ := hlabel
  obtain ⟨w, hw, hwnear⟩ := hdense (deformPoint φ v)
  have hwq : w + q ∈ W := by
    have hh : q +ᵥ w ∈ q +ᵥ W := ⟨w, hw, rfl⟩
    rw [hq] at hh
    simpa only [vadd_eq_add, add_comm] using hh
  have hvimage : normalEval n (deformPoint φ v) =
      normalEval n (deformPoint φ a) := by
    rw [rationalNormal_commutes, rationalNormal_commutes, hvlevel]
  have hzlevel : normalEval n (deformPoint φ v + deformPoint φ q) =
      normalEval n (deformPoint φ b) := by
    rw [hphase, normalEval, normalEval] at *
    simp only [Complex.add_re, Complex.add_im] at *
    linarith
  obtain ⟨u, hu, hulevel, hunear⟩ :=
    hcloud (deformPoint φ v + deformPoint φ q) hzlevel
  have hmap : deformPoint φ (w + q) = deformPoint φ w + deformPoint φ q :=
    (deformPointLinear φ).map_add w q
  have hpair : dist (deformPoint φ u) (deformPoint φ (w + q)) < C + G := by
    rw [hmap]
    have htri := dist_triangle (deformPoint φ u)
      (deformPoint φ v + deformPoint φ q) (deformPoint φ w + deformPoint φ q)
    rw [dist_add_right] at htri
    have hu' := hunear
    rw [dist_comm] at hu'
    linarith
  have hshort : dist (deformPoint φ v) (deformPoint φ w) < C + G := by
    linarith
  have heval : normalEval n (deformPoint φ u - deformPoint φ (w + q)) =
      normalEval n (deformPoint φ v - deformPoint φ w) := by
    -- The image-level equality is supplied by the source-level equality and
    -- rational-normal commutation, not inferred from distance alone.
    have hunormal : normalEval n (deformPoint φ u) =
        normalEval n (deformPoint φ b) := by
      rw [rationalNormal_commutes, rationalNormal_commutes, hulevel]
    rw [hmap]
    simp only [normalEval, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im] at hunormal hzlevel ⊢
    linarith
  have hsource := hreflect u hu (w + q) (hWY hwq) v hv w (hWY hw)
    hpair hshort heval
  simp only [normalEval, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im] at hsource hvlevel hulevel ⊢
  linarith

end Tiling.RationalSlopes

namespace Tiling.Polygonal

open Tiling.RationalPolygonal (PolygonalRegion)

private theorem pullbackGood_cornerCloud
    {K Kφ : Tiling.RationalPolygonal.PolygonalRegion} {T : Set Plane}
    (f : Plane →ₗ[ℚ] Plane)
    (H : Tiling.RationalSlopes.GoodParametrization Kφ (f '' T))
    (hp : IsPacking K.prototileFamily (K.placements T))
    (V : Finset Plane) (hV : Tiling.RationalSlopes.Approximation.Decorates K V)
    (hcorners : ∀ A ⊆ T, properVertices (regularSupport Kφ (f '' A)) =
      f '' properVertices (regularSupport K A)) :
    let S := fun i a m => T ∩ f ⁻¹' H.atom i a m
    let W := ⋃ i, ⋃ a : H.Index i, ⋃ m : ℤ, properVertices (regularSupport K (S i a m))
    (∀ i a m, f '' S i a m = H.atom i a m) ∧
      (∀ i a m, (S i a m).Nonempty) ∧
      Set.PairwiseDisjoint Set.univ
        (fun s : Σ i : Fin H.numberOfParts, H.Index i × ℤ => S s.1 s.2.1 s.2.2) ∧
      (⋃ i, ⋃ a : H.Index i, ⋃ m : ℤ, S i a m) = T ∧
      W ⊆ Tiling.RationalSlopes.Approximation.decoratedCloud V T ∧
      f '' W = ⋃ i, ⋃ a : H.Index i, ⋃ m : ℤ,
        properVertices (regularSupport Kφ (H.atom i a m)) := by
  classical
  let S := fun i a m => T ∩ f ⁻¹' H.atom i a m
  let atom := fun s : Σ i : Fin H.numberOfParts, H.Index i × ℤ => H.atom s.1 s.2.1 s.2.2
  have hUnion : (⋃ s, atom s) = f '' T := by
    have hflat : (⋃ s, atom s) = ⋃ i, ⋃ a : H.Index i, ⋃ m : ℤ, H.atom i a m := by
      ext x
      simp only [atom, Set.mem_iUnion]
      constructor
      · rintro ⟨⟨i, a, m⟩, hx⟩; exact ⟨i, a, m, hx⟩
      · rintro ⟨i, a, m, hx⟩; exact ⟨⟨i, a, m⟩, hx⟩
    exact hflat.trans H.union_eq
  obtain ⟨hImage, hNonempty, hDisjoint, hSourceUnion⟩ :=
    sourceAtoms_image_and_partition f atom
      (fun s => H.atom_nonempty s.1 s.2.1 s.2.2) H.atoms_disjoint hUnion
  refine ⟨fun i a m => hImage ⟨i, a, m⟩,
    fun i a m => hNonempty ⟨i, a, m⟩, hDisjoint, ?_, ?_, ?_⟩
  · have hflat : (⋃ i, ⋃ a : H.Index i, ⋃ m : ℤ, S i a m) =
        ⋃ s, T ∩ f ⁻¹' atom s := by
      ext x
      simp only [S, atom, Set.mem_iUnion]
      constructor
      · rintro ⟨i, a, m, hx⟩; exact ⟨⟨i, a, m⟩, hx⟩
      · rintro ⟨⟨i, a, m⟩, hx⟩; exact ⟨i, a, m, hx⟩
    exact hflat.trans hSourceUnion
  · intro x hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
    have hpS : IsPacking K.prototileFamily (K.placements (S i a m)) :=
      hp.mono (fun _ ht => ht.1)
    obtain ⟨v, hv, t, ht, hxt⟩ := properVertexProvenance hpS x hx
    have hvV : v ∈ (V : Set Plane) := by
      obtain ⟨A, hA⟩ := hV
      obtain ⟨c, hc, hvc⟩ := hv A
      exact hA c hc hvc
    exact Set.mem_add.mpr ⟨v, hvV, t, ht.1, hxt.symm⟩
  · simp only [Set.image_iUnion]
    apply Set.iUnion_congr
    intro i
    apply Set.iUnion_congr
    intro a
    apply Set.iUnion_congr
    intro m
    rw [← hcorners (S i a m) (fun _ ht => ht.1), hImage ⟨i, a, m⟩]

private theorem frontierLevel_decoratedCloud_dense
    (K : PolygonalRegion) (T S : Set Plane) (W : Finset Plane)
    (hS : S ⊆ T) (hp : IsPacking K.prototileFamily (K.placements S))
    (hW : Tiling.RationalSlopes.Approximation.Decorates K W)
    (π : Plane →ₗ[ℝ] ℝ) (e : Plane) (he : ‖e‖ = 1) (hπe : π e = 0)
    (B : ℝ) (hbound : ∀ z ∈ K.support, ‖z‖ ≤ B) (a : Plane)
    (hfront : {y | π y = π a} ⊆ frontier (regularSupport K S)) :
    ∀ x : Plane, π x = π a →
      ∃ w ∈ Tiling.RationalSlopes.Approximation.decoratedCloud W T,
        π w = π a ∧ dist x w < 2 * B + 3 := by
  have he0 : e ≠ 0 := by
    intro hz
    simp only [hz, norm_zero] at he
    norm_num at he
  intro x hx
  have hlevel : {y | π y = π x} ⊆ frontier (regularSupport K S) := by
    simpa only [hx] using hfront
  obtain ⟨v, q, hv, hq, hvq, hdist⟩ :=
    frontierLevel_has_intrinsicVertex_of_supportBound K S hp π e he0 hπe B hbound x hlevel
  have hvSupport : v ∈ K.support := by
    obtain ⟨A⟩ := K.isPolygonal
    obtain ⟨t, ht, hvt⟩ := hv A
    have hvt' : v ∈ t := extremePoints_subset hvt
    rw [← A.sUnion_eq]
    exact Set.mem_sUnion.mpr ⟨t, ht, hvt'⟩
  have hvW : v ∈ (W : Set Plane) := by
    obtain ⟨A, hA⟩ := hW
    obtain ⟨t, ht, hvt⟩ := hv A
    exact hA t ht hvt
  refine ⟨v + q, ?_, hvq.trans hx, ?_⟩
  · exact Set.mem_add.mpr ⟨v, hvW, q, hS hq, rfl⟩
  · have htri := dist_triangle x q (v + q)
    have hvDist : dist q (v + q) ≤ B := by
      simpa [dist_eq_norm] using hbound v hvSupport
    rw [dist_comm q x, he] at hdist
    linarith

end Tiling.Polygonal

namespace Tiling.RationalSlopes

open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Approximation Tiling.Polygonal

private theorem simultaneous_finiteControls
    (specs : List (Finset ℝ × ℝ)) (hpos : ∀ p ∈ specs, 0 < p.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ p ∈ specs, IsFiniteApproximation p.1 p.2 φ := by
  induction specs with
  | nil => exact ⟨∅, 1, zero_lt_one, by simp⟩
  | cons p ps ih =>
    obtain ⟨F, ε, hε, hcontrol⟩ := ih (fun q hq => hpos q (List.mem_cons_of_mem p hq))
    have hp : 0 < p.2 := hpos p (List.mem_cons_self)
    refine ⟨p.1 ∪ F, min p.2 ε, lt_min hp hε, ?_⟩
    intro φ hφ q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact finiteApproximation_strengthen _ _ _ _ _
        Finset.subset_union_left (min_le_left _ _) hφ
    · apply hcontrol φ ?_ q hq
      exact finiteApproximation_strengthen _ _ _ _ _
        Finset.subset_union_right (min_le_right _ _) hφ

private theorem deformation_liesInMeshCoset
    (T : Set Plane) (hT : HasFLC T) (hdense : RelativeDense T)
    (ht : T.Nonempty) (φ : ℝ →ₗ[ℚ] ℚ) :
    LiesInRationalMeshCoset (deformPoint φ '' T) := by
  obtain ⟨a, ha⟩ := ht
  obtain ⟨steps, _, hgenerated⟩ := Approximation.boundedSteps_generate T hT hdense a ha
  obtain ⟨d, hd, hmesh⟩ := Approximation.commonMesh_of_finiteZGeneration steps φ
  refine ⟨d, hd, deformPoint φ a, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hdiff := hmesh (Set.mem_image_of_mem (deformPoint φ) (hgenerated t ht))
  obtain ⟨p, q, hpq⟩ := hdiff
  have hmap : deformPoint φ (t - a) = deformPoint φ t - deformPoint φ a :=
    (deformPointLinear φ).map_sub t a
  refine ⟨deformPoint φ (t - a), ?_, ?_⟩
  · refine ⟨![p, q], ?_⟩
    rw [hpq]
    apply Complex.ext <;>
      simp [Tiling.RationalPolygonal.integerPoint, div_eq_mul_inv, mul_comm] <;>
      field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hd] <;> simp
  · rw [hmap]
    simp only [vadd_eq_add]
    abel

private theorem normalLevel_iff (n : RationalNormal) (u v : Plane) :
    normalEval n u = normalEval n v ↔ u - v ∈ normalDirection n := by
  change normalEval n u = normalEval n v ↔ normalEval n (u - v) = 0
  simp only [normalEval, Complex.sub_re, Complex.sub_im]
  constructor <;> intro h <;> linarith

private theorem affineLevel_eq_of_sub_mem {δ : Submodule ℝ Plane} {a b : Plane}
    (hab : a - b ∈ δ) : a +ᵥ (δ : Set Plane) = b +ᵥ (δ : Set Plane) := by
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  constructor
  · intro h
    change -b + x ∈ δ
    convert δ.add_mem hab h using 1
    abel
  · intro h
    change -a + x ∈ δ
    convert δ.sub_mem h hab using 1
    abel

private theorem straightFrontierLine_vadd {D : Set Plane} {δ : Submodule ℝ Plane}
    {a : Plane} (h : IsStraightFrontierLine D δ a) (q : Plane) :
    IsStraightFrontierLine (q +ᵥ D) δ (a + q) := by
  have hcoset : (a + q) +ᵥ (δ : Set Plane) = q +ᵥ (a +ᵥ (δ : Set Plane)) := by
    rw [← add_vadd, add_comm]
  have hfront : frontier (q +ᵥ D) = q +ᵥ frontier D := by
    simp only [← Set.image_vadd]
    exact ((Homeomorph.addLeft q).image_frontier D).symm
  refine ⟨?_, ?_⟩
  · rw [hcoset, hfront]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h.1 hx, rfl⟩
  · rw [hcoset, properVertices_vadd]
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    exact Set.disjoint_left.mp h.2 hx (add_left_cancel heq ▸ hy)

/-- The straight-line branch of carrier reconstruction. Quantitative labelled image
density and four-point reflection force the backward provider's actual source line
to be the prescribed translated line, after which pointwise source germs lift. -/
private theorem lift_straightFrontier_translation
    (φ : ℝ →ₗ[ℚ] ℚ) (n : RationalNormal) (Y W : Set Plane)
    (hWY : W ⊆ Y) (q : Plane) (hq : q ∈ periodGroup W)
    (C G : ℝ) (hG : 0 < G)
    (hdense : ∀ z : Plane, ∃ w ∈ W, dist z (deformPoint φ w) < C)
    (D₀ D₁ D₀φ D₁φ : Set Plane)
    (htransport : D₁φ = deformPoint φ q +ᵥ D₀φ)
    (hforward : ∀ a : Plane, IsStraightFrontierLine D₀ (normalDirection n) a →
      IsStraightFrontierLine D₀φ (normalDirection n) (deformPoint φ a) ∧
        ∀ x ∈ a +ᵥ (normalDirection n : Set Plane),
          SameGermAt D₀ x D₀φ (deformPoint φ x))
    (hback : ∀ b : Plane, IsStraightFrontierLine D₁φ (normalDirection n) b →
      ∃ a : Plane, IsStraightFrontierLine D₁ (normalDirection n) a ∧
        b - deformPoint φ a ∈ normalDirection n ∧
          ∀ x ∈ a +ᵥ (normalDirection n : Set Plane),
            SameGermAt D₁ x D₁φ (deformPoint φ x))
    (hlabel : ∀ a : Plane, IsStraightFrontierLine D₀ (normalDirection n) a →
      ∃ v ∈ Y, normalEval n v = normalEval n a)
    (hcloud : ∀ a : Plane, IsStraightFrontierLine D₁ (normalDirection n) a →
      ∀ z : Plane, normalEval n z = normalEval n (deformPoint φ a) →
        ∃ u ∈ Y, normalEval n u = normalEval n a ∧
          dist z (deformPoint φ u) < G)
    (hreflect : ∀ u ∈ Y, ∀ w ∈ Y, ∀ v ∈ Y, ∀ t ∈ Y,
      dist (deformPoint φ u) (deformPoint φ w) < C + G →
      dist (deformPoint φ v) (deformPoint φ t) < C + G →
      normalEval n (deformPoint φ u - deformPoint φ w) =
        normalEval n (deformPoint φ v - deformPoint φ t) →
      normalEval n (u - w) = normalEval n (v - t)) :
    ∀ a : Plane, IsStraightFrontierLine D₀ (normalDirection n) a →
      IsStraightFrontierLine D₁ (normalDirection n) (a + q) ∧
        ∀ x ∈ a +ᵥ (normalDirection n : Set Plane),
          SameGermAt D₀ x D₁ (x + q) := by
  intro a ha
  obtain ⟨himage, hgerm⟩ := hforward a ha
  have htranslated : IsStraightFrontierLine D₁φ (normalDirection n)
      (deformPoint φ a + deformPoint φ q) := by
    rw [htransport]
    exact straightFrontierLine_vadd himage _
  obtain ⟨b, hb, hdiff, hgermb⟩ :=
    hback (deformPoint φ a + deformPoint φ q) htranslated
  have hphase : normalEval n (deformPoint φ b) =
      normalEval n (deformPoint φ a + deformPoint φ q) :=
    ((normalLevel_iff n _ _).mpr hdiff).symm
  have hsourcePhase := line_phase_of_labelled_density φ n Y W hWY a b q hq C G hG
    hdense (hlabel a ha) (hcloud b hb) hphase hreflect
  have hcoset : b +ᵥ (normalDirection n : Set Plane) =
      (a + q) +ᵥ (normalDirection n : Set Plane) :=
    affineLevel_eq_of_sub_mem ((normalLevel_iff n _ _).mp hsourcePhase)
  refine ⟨by simpa only [IsStraightFrontierLine, hcoset] using hb, ?_⟩
  intro x hx
  have hxq : x + q ∈ b +ᵥ (normalDirection n : Set Plane) := by
    rw [hcoset]
    obtain ⟨d, hd, rfl⟩ := hx
    exact ⟨d, hd, by simp only [vadd_eq_add]; abel⟩
  exact sameGerm_lift_translation (deformPointLinear φ) (hgerm x hx)
    (hgermb (x + q) hxq) htransport

private theorem straightFrontier_decoratedImageCloud_dense
    (K : PolygonalRegion) (T : Set Plane) (W : Finset Plane)
    (hp : IsPacking K.prototileFamily (K.placements T))
    (hW : Approximation.Decorates K W)
    (hY : HasFLC (Approximation.decoratedCloud W T))
    (B : ℝ) (hB : 0 < B) (hbound : ∀ z ∈ K.support, ‖z‖ ≤ B)
    (φ : ℝ →ₗ[ℚ] ℚ)
    (hctrl : ∀ u ∈ Approximation.decoratedCloud W T,
      ∀ v ∈ Approximation.decoratedCloud W T, dist u v < 4 * B + 6 → u ≠ v →
        ‖deformPoint φ (u - v) - (u - v)‖ < ‖u - v‖ ∧
          ‖deformPoint φ (u - v)‖ < 4 * B + 7) :
    ∀ S ⊆ T, ∀ n : RationalNormal, Module.finrank ℝ (normalDirection n) = 1 →
      ∀ a : Plane, IsStraightFrontierLine (regularSupport K S) (normalDirection n) a →
        ∀ z : Plane, normalEval n z = normalEval n (deformPoint φ a) →
          ∃ w ∈ Approximation.decoratedCloud W T,
            normalEval n w = normalEval n a ∧
              normalEval n (deformPoint φ w) = normalEval n (deformPoint φ a) ∧
                dist z (deformPoint φ w) < 4 * B + 7 := by
  intro S hS n hn a ha
  let π : Plane →ₗ[ℝ] ℝ :=
    (((n.x : ℝ) • Complex.reCLM + (n.y : ℝ) • Complex.imCLM).toLinearMap)
  have hπ (z : Plane) : π z = normalEval n z := rfl
  have hnotbot : normalDirection n ≠ ⊥ := by
    intro hh
    rw [hh, finrank_bot] at hn
    norm_num at hn
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (normalDirection n)).mp hnotbot
  let e : Plane := (‖v‖⁻¹ : ℝ) • v
  have he : ‖e‖ = 1 := by
    dsimp [e]
    simp
    field_simp [ne_of_gt (norm_pos_iff.mpr hv0)]
  have heker : e ∈ normalDirection n := (normalDirection n).smul_mem _ hv
  have hπe : π e = 0 := heker
  have hfront : {y | π y = π a} ⊆ frontier (regularSupport K S) := by
    intro y hy
    apply ha.1
    refine ⟨y - a, ?_, by simp [vadd_eq_add]⟩
    change normalEval n (y - a) = 0
    have hh : normalEval n y = normalEval n a := hy
    simp only [normalEval, Complex.sub_re, Complex.sub_im] at hh ⊢
    linarith
  have hsource := frontierLevel_decoratedCloud_dense K T S W hS (hp.mono (fun _ hx => hS hx))
    hW π e he hπe B hbound a hfront
  have hρ : 0 < 2 * B + 3 := by linarith
  have hcontrol : ∀ u ∈ Approximation.decoratedCloud W T,
      ∀ v ∈ Approximation.decoratedCloud W T,
        dist u v < 2 * (2 * B + 3) → u ≠ v →
        ‖deformPoint φ (u - v) - (u - v)‖ < ‖u - v‖ ∧
          ‖deformPoint φ (u - v)‖ < 2 * (2 * B + 3) + 1 := by
    intro u hu v hv huv hne
    obtain ⟨herr, hnorm⟩ := hctrl u hu v hv (by linarith) hne
    exact ⟨herr, by linarith⟩
  have himage := deformPoint_lineCloud_dense_of_gapControl
    (Approximation.decoratedCloud W T) hY n hn a (2 * B + 3) hρ
    (by simpa only [hπ] using hsource) φ hcontrol
  simpa only [show 2 * (2 * B + 3) + 1 = 4 * B + 7 by ring] using himage

end Tiling.RationalSlopes

namespace Tiling.Polygonal

open Tiling.RationalPolygonal (PolygonalRegion)

/-- The substantive Part I lifting theorem. No hidden `suitable carrier` premise:
periodic carrier normalization is proved by the approximation owner. -/
theorem flc_goodParametrization_of_fibreCornerDensity
    {K : PolygonalRegion} {T E : Set Plane}
    (hK : Tiling.RationalSlopes.HasRationalSlopes K)
    (hTne : T.Nonempty) (hFLC : HasFLC T) (htile : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (hEper : IsLatticePeriodic E)
    (hdense : ∃ R : ℝ, 0 < R ∧ ∀ δ : Submodule ℝ Plane,
      HasBoundaryDirection K δ → ∀ x : Plane,
        ∃ v ∈ fibreProperVertices K T δ, dist x v < R) :
    Nonempty (Tiling.RationalSlopes.GoodParametrization K T) := by
  classical
  have hrelative := Tiling.RationalSlopes.periodicCarrier_centresRelativeDense
    K T E htile hTne hEopen hEper
  have hown := tilesOn_regularSupport_of_packing htile.2.1
  obtain ⟨P, hP, Fp, εp, hεp, hperiodic⟩ :=
    Tiling.RationalSlopes.flcDeformation_preservesPeriodicCarrier
      K T E hK hFLC hTne htile hEopen hEregular hEper
  obtain ⟨Q, hQ, W, hW, hWzero, Fq, εq, hεq, hdeform⟩ :=
    Tiling.RationalSlopes.Approximation.flcRationalDeformation
      K T hK hFLC hrelative hown
  obtain ⟨Fc, εc, hεc, hcodes⟩ :=
    Tiling.RationalSlopes.Approximation.polyhedralDeformation_independentOfCode K P Q hP hQ
  obtain ⟨U, hU, _, _, _, B, L, hB, hL, Fu, εu, hεu, hboundary⟩ :=
    Tiling.RationalSlopes.Approximation.rationalPolygon_uniformBoundaryControl K hK
  obtain ⟨Pline, hPline, Fline, εline, hεline, hlines⟩ :=
    Tiling.RationalSlopes.flcDeformation_transportsStraightFrontierLines K T hK hFLC hrelative hown
  obtain ⟨FuQ, εuQ, hεuQ, hcodeuQ⟩ :=
    Tiling.RationalSlopes.Approximation.polyhedralDeformation_independentOfCode K U Q hU hQ
  obtain ⟨FlQ, εlQ, hεlQ, hcodelQ⟩ :=
    Tiling.RationalSlopes.Approximation.polyhedralDeformation_independentOfCode K Pline Q hPline hQ
  obtain ⟨Fw, εw, R, hεw, hR, hwhole⟩ :=
    Tiling.RationalSlopes.flcDeformation_uniformWholeFibreCornerDensity
      hK hTne hFLC htile hEopen hEregular hEper hdense Q hQ
  obtain ⟨Fi, εi, ρ, hεi, hρ, himageDense⟩ :=
    Tiling.RationalSlopes.Approximation.approximation_uniformImageDensity T hFLC hrelative
  let D := (boundaryDirections_finite K).toFinset
  have hDmem {δ : Submodule ℝ Plane} : δ ∈ D ↔ HasBoundaryDirection K δ :=
    (boundaryDirections_finite K).mem_toFinset
  have hDdim : ∀ δ ∈ D, Module.finrank ℝ δ = 1 := by
    intro δ hδ
    exact Tiling.RationalSlopes.boundaryDirection_finrank_eq_one (hDmem.mp hδ)
  obtain ⟨C, hC, hsliceDense⟩ :=
    sliceWitnesses_uniformRelativeDense D L B ρ R hL.le hB hρ hR hDdim
  let Y := Tiling.RationalSlopes.Approximation.decoratedCloud W T
  have hY : HasFLC Y := by
    simpa only [Y, Tiling.RationalSlopes.Approximation.decoratedCloud, add_comm] using hFLC.add_finset W
  have hTY : T ⊆ Y := by
    intro t ht
    exact Set.mem_add.mpr ⟨0, hWzero, t, ht, zero_add t⟩
  have hYdense : RelativeDense Y := by
    obtain ⟨r, hr, hd⟩ := hrelative
    exact ⟨r, hr, fun x => by
      obtain ⟨t, ht, hdist⟩ := hd x
      exact ⟨t, hTY ht, hdist⟩⟩
  obtain ⟨B₀, hB₀, hsupport⟩ := K.isPolygonal.isCompact.isBounded.exists_pos_norm_le
  have hnormal : ∀ δ ∈ D, ∃ n : Tiling.Approximation.RationalNormal,
      Tiling.Approximation.normalDirection n = δ := by
    intro δ hδ
    exact Tiling.RationalSlopes.Approximation.rationalDirection_hasNormal δ (hDdim δ hδ)
      (hasRationalDirection_of_hasBoundaryDirection hK (hDmem.mp hδ))
  choose normal hnormalEq using hnormal
  let normals := D.attach.image (fun d => normal d.1 d.2)
  obtain ⟨Fe, εe, hεe, herror⟩ :=
    Tiling.RationalSlopes.Approximation.approximation_globalRelativeError Y hY hYdense
      (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Fm, εm, hεm, hmetric⟩ :=
    Tiling.RationalSlopes.Approximation.approximation_boundedMetricAndRelationControl
      Y hY hYdense (4 * B₀ + 7) 1 normals (by linarith) zero_lt_one
  obtain ⟨Fd, εd, hεd, hdisplacement⟩ :=
    Tiling.RationalSlopes.Approximation.approximation_reflectsBoundedDisplacement
      Y hY hYdense (10 * C) (by linarith)
  obtain ⟨Fn, εn, hεn, hnormalDisplacement⟩ :=
    Tiling.RationalSlopes.bounded_normalDisplacementReflection
      Y hY hYdense (2 * (C + (4 * B₀ + 7) + 1)) (by linarith) normals
  -- The witness bound and all finite controls are fixed before selecting φ.
  let specs : List (Finset ℝ × ℝ) :=
    [(Fp, εp), (Fq, εq), (Fc, εc), (Fu, εu), (Fline, εline),
      (FuQ, εuQ), (FlQ, εlQ), (Fw, εw), (Fi, εi), (Fe, εe),
      (Fm, εm), (Fd, εd), (Fn, εn)]
  have hspecs : ∀ p ∈ specs, 0 < p.2 := by
    intro p hp
    simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  obtain ⟨F, ε, hε, hcontrols⟩ := Tiling.RationalSlopes.simultaneous_finiteControls specs hspecs
  obtain ⟨φ, hφ⟩ := Tiling.Approximation.exists_finiteApproximation F ε hε
  have htest (p : Finset ℝ × ℝ) (hp : p ∈ specs) := hcontrols φ hφ p hp
  have hφp := htest (Fp, εp) (by simp [specs])
  have hφq := htest (Fq, εq) (by simp [specs])
  have hφc := htest (Fc, εc) (by simp [specs])
  obtain ⟨Kp, hKp, hKpperiodic, _⟩ := hperiodic φ hφp
  obtain ⟨Kq, hKq, hKqrat, hKqslopes, hKqW, hinj, htileq, hFLCq, hgerms, hvertices⟩ :=
    hdeform φ hφq
  have hKpq : Kp = Kq := polygonalRegion_eq_of_support_eq
    (hKp.trans ((hcodes φ hφc).trans hKq.symm))
  subst Kp
  obtain ⟨Ku, hKu, hbound, ⟨Eedges, hedgeCover, hedgeLength⟩, hDirections⟩ :=
    hboundary φ (htest (Fu, εu) (by simp [specs]))
  have hKuq : Ku = Kq := polygonalRegion_eq_of_support_eq
    (hKu.trans ((hcodeuQ φ (htest (FuQ, εuQ) (by simp [specs]))).trans hKq.symm))
  subst Ku
  obtain ⟨Kl, hKl, hlinePacket⟩ := hlines φ (htest (Fline, εline) (by simp [specs]))
  have hKlq : Kl = Kq := polygonalRegion_eq_of_support_eq
    (hKl.trans ((hcodelQ φ (htest (FlQ, εlQ) (by simp [specs]))).trans hKq.symm))
  subst Kl
  have hwholeDense : ∀ δ ∈ D, ∀ x : Plane,
      ∃ v ∈ fibreProperVertices Kq (Tiling.Approximation.deformPoint φ '' T) δ,
        dist x v < R := by
    intro δ hδ
    exact hwhole φ (htest (Fw, εw) (by simp [specs])) Kq hKq δ (hDmem.mp hδ)
  have hcentresDense := himageDense φ (htest (Fi, εi) (by simp [specs]))
  have hmesh := Tiling.RationalSlopes.deformation_liesInMeshCoset T hFLC hrelative hTne φ
  have hregularq := regularSupport_isRegularOpen Kq (Tiling.Approximation.deformPoint φ '' T)
  obtain ⟨Gslice⟩ := Tiling.RationalSlopes.exists_rationalSliceParametrization
    hKqrat hmesh htileq hregularq.1 hregularq.2 hKpperiodic
  obtain ⟨H₀, hH₀, direction₀, hdim₀, hline₀, hW₀⟩ :=
    Tiling.RationalSlopes.PLPhase.toGood_lineSupported Gslice
  let atom₀ := fun s : Σ i : Fin H₀.numberOfParts, H₀.Index i × ℤ =>
    H₀.atom s.1 s.2.1 s.2.2
  have hUnion₀ : (⋃ s, atom₀ s) = Tiling.Approximation.deformPoint φ '' T := by
    have hflat : (⋃ s, atom₀ s) = ⋃ i, ⋃ a : H₀.Index i, ⋃ m : ℤ, H₀.atom i a m := by
      ext x
      simp only [atom₀, Set.mem_iUnion]
      constructor
      · rintro ⟨⟨i, a, m⟩, hx⟩
        exact ⟨i, a, m, hx⟩
      · rintro ⟨i, a, m, hx⟩
        exact ⟨⟨i, a, m⟩, hx⟩
    exact hflat.trans H₀.union_eq
  have hwholePartDense : ∀ x : Plane, ∃ v ∈ (⋃ i, ⋃ t ∈ Gslice.part i,
      properVertices (regularSupport Kq
        (lineFibre (Gslice.direction i) (Gslice.part i) t))), dist x v < C := by
    intro x
    obtain ⟨s, v, hv, hdist⟩ := hsliceDense Kq Eedges hbound hedgeCover hedgeLength
      (fun δ hδ => hDmem.mpr ((hDirections δ).mp hδ))
      (Tiling.Approximation.deformPoint φ '' T) htileq.2.1 hcentresDense hwholeDense
      _ atom₀ (fun s => direction₀ s.1)
      (fun s => H₀.atom_nonempty s.1 s.2.1 s.2.2)
      H₀.atoms_disjoint hUnion₀
      (fun s => ⟨hdim₀ s.1, hline₀ s.1 s.2.1 s.2.2⟩) x
    refine ⟨v, ?_, hdist⟩
    rw [← hW₀]
    exact Set.mem_iUnion.mpr ⟨s.1, Set.mem_iUnion.mpr ⟨s.2.1,
      Set.mem_iUnion.mpr ⟨s.2.2, hv⟩⟩⟩
  obtain ⟨H, ⟨direction, hdim, hline⟩, hcornerDense, hcornerPeriods⟩ :=
    Tiling.RationalSlopes.PLPhase.rescaled_phase_with_periodicWitnessCloud Gslice C hwholePartDense
  let f := Tiling.Approximation.deformPointLinear φ
  let S := fun i a m => T ∩ f ⁻¹' H.atom i a m
  let WS := ⋃ i, ⋃ a : H.Index i, ⋃ m : ℤ, properVertices (regularSupport K (S i a m))
  obtain ⟨hImageS, hSne, hSdisj, hSUnion, hWSCloud, hImageWS⟩ :=
    pullbackGood_cornerCloud f H htile.2.1 W hW hvertices
  have hWS : WS ⊆ (W : Set Plane) + T := hWSCloud
  have hImageWS' : f '' WS = ⋃ i, ⋃ a : H.Index i, ⋃ m : ℤ,
      properVertices (regularSupport Kq (H.atom i a m)) := hImageWS
  have hDenseWS : ∀ x : Plane, ∃ w ∈ f '' WS, dist x w < C := by
    rw [hImageWS']
    exact hcornerDense
  have hReflect : ShortDifferenceReflection ((W : Set Plane) + T) f (5 * C) := by
    intro a ha b hb c hc d hd hab hcd heq
    have hh := hdisplacement φ (htest (Fd, εd) (by simp [specs]))
      b hb a ha d hd c hc
        (by change dist (f b) (f a) < 10 * C / 2; rw [dist_comm]; linarith)
        (by change dist (f d) (f c) < 10 * C / 2; rw [dist_comm]; linarith)
    apply hh.2.2.mp
    change f b - f a = f d - f c
    simpa only [map_sub] using heq
  have hLimage : (H.lattice.toAddSubgroup : Set Plane) ⊆ periodGroup (f '' WS) := by
    rw [hImageWS']
    exact hcornerPeriods
  obtain ⟨L₀, hBasis, hL₀periods⟩ := lift_lattice_of_denseWitnesses hFLC W.finite_toSet
    f hC hWS hinj hDenseWS hReflect H.lattice hLimage
  have hBasisPeriods (j : Fin 2) : L₀.basis j ∈ periodGroup WS :=
    hL₀periods (AddSubgroup.subset_closure ⟨j, rfl⟩)
  have hWithinPeriods : ∀ i a m,
      H.lambdaCoefficient i • L₀.basis 0 + H.gammaCoefficient i • L₀.basis 1 ∈
        periodGroup (S i a m) := by
    intro i a m
    apply lift_subfamily_period f (show (W : Set Plane).Nonempty from ⟨0, hWzero⟩)
      (fun _ ht => ht.1) hWS hC hDenseWS hReflect
    · exact (periodGroup WS).add_mem
        ((periodGroup WS).zsmul_mem (hBasisPeriods 0) (H.lambdaCoefficient i))
        ((periodGroup WS).zsmul_mem (hBasisPeriods 1) (H.gammaCoefficient i))
    · rw [hImageS i a m, map_add, map_zsmul, map_zsmul, hBasis 0, hBasis 1]
      exact H.atom_periodic i a m
  have hGapControl : ∀ u ∈ Y, ∀ v ∈ Y, dist u v < 4 * B₀ + 6 → u ≠ v →
      ‖f (u - v) - (u - v)‖ < ‖u - v‖ ∧ ‖f (u - v)‖ < 4 * B₀ + 7 := by
    intro u hu v hv huv hne
    have herr := herror φ (htest (Fe, εe) (by simp [specs])) u hu v hv
    have hnear := (hmetric φ (htest (Fm, εm) (by simp [specs]))).2.1
      u hu v hv (by linarith)
    have hnear' : ‖f (u - v) - (u - v)‖ < 1 := by
      rw [dist_eq_norm] at hnear
      change ‖f u - f v - (u - v)‖ < 1 at hnear
      rw [map_sub]
      exact hnear
    have hdistpos : 0 < dist u v := dist_pos.mpr hne
    have hnormdist : ‖u - v‖ = dist u v := (dist_eq_norm u v).symm
    refine ⟨?_, ?_⟩
    · change ‖f (u - v) - (u - v)‖ ≤ (1 / 2) * dist u v at herr
      rw [hnormdist]
      linarith
    · have hh := norm_le_norm_sub_add (f (u - v)) (u - v)
      rw [hnormdist] at hh
      linarith
  have hImageCloud := Tiling.RationalSlopes.straightFrontier_decoratedImageCloud_dense
    K T W htile.2.1 hW hY B₀ hB₀ hsupport φ hGapControl
  have hStraightLift :
      ∀ A ⊆ T, ∀ B' ⊆ T, ∀ q : Plane, q ∈ periodGroup WS →
        regularSupport Kq (f '' B') = f q +ᵥ regularSupport Kq (f '' A) →
        ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
          ∀ a : Plane, IsStraightFrontierLine (regularSupport K A) δ a →
            IsStraightFrontierLine (regularSupport K B') δ (a + q) ∧
              ∀ x ∈ a +ᵥ (δ : Set Plane),
                SameGermAt (regularSupport K A) x (regularSupport K B') (x + q) := by
    intro A hAT B' hBT q hq htransport δ hδ a ha
    have hδboundary := straightFrontierLine_isBoundaryDirection hδ
      (htile.2.1.mono (fun _ ht => hAT ht)) ha
    have hδD := hDmem.mpr hδboundary
    let n := normal δ hδD
    have hn : Tiling.Approximation.normalDirection n = δ := hnormalEq δ hδD
    have hnDim : Module.finrank ℝ (Tiling.Approximation.normalDirection n) = 1 := by
      rw [hn]; exact hδ
    have hnRat : Tiling.RationalSlopes.HasRationalDirection
        (Tiling.Approximation.normalDirection n) := by
      rw [hn]
      exact hasRationalDirection_of_hasBoundaryDirection hK hδboundary
    have hnmem : n ∈ normals :=
      Finset.mem_image.mpr ⟨⟨δ, hδD⟩, Finset.mem_attach _ _, rfl⟩
    have hforward := (hlinePacket A hAT (Tiling.Approximation.normalDirection n) hnDim hnRat).1
    have hback := (hlinePacket B' hBT (Tiling.Approximation.normalDirection n) hnDim hnRat).2
    have hdenseLabelled : ∀ z : Plane, ∃ w ∈ WS, dist z (Tiling.Approximation.deformPoint φ w) < C := by
      intro z
      obtain ⟨fw, ⟨w, hw, rfl⟩, hdist⟩ := hDenseWS z
      exact ⟨w, hw, hdist⟩
    have hlabel : ∀ b : Plane,
        IsStraightFrontierLine (regularSupport K A) (Tiling.Approximation.normalDirection n) b →
          ∃ v ∈ Y, Tiling.Approximation.normalEval n v = Tiling.Approximation.normalEval n b := by
      intro b hb
      obtain ⟨v, hv, hvlevel, _, _⟩ := hImageCloud A hAT n hnDim b hb
        (Tiling.Approximation.deformPoint φ b) rfl
      exact ⟨v, hv, hvlevel⟩
    have hcloud : ∀ b : Plane,
        IsStraightFrontierLine (regularSupport K B') (Tiling.Approximation.normalDirection n) b →
          ∀ z : Plane, Tiling.Approximation.normalEval n z =
            Tiling.Approximation.normalEval n (Tiling.Approximation.deformPoint φ b) →
              ∃ v ∈ Y, Tiling.Approximation.normalEval n v = Tiling.Approximation.normalEval n b ∧
                dist z (Tiling.Approximation.deformPoint φ v) < 4 * B₀ + 7 := by
      intro b hb z hz
      obtain ⟨v, hv, hvlevel, _, hdist⟩ := hImageCloud B' hBT n hnDim b hb z hz
      exact ⟨v, hv, hvlevel, hdist⟩
    have hreflect : ∀ u ∈ Y, ∀ w ∈ Y, ∀ v ∈ Y, ∀ t ∈ Y,
        dist (Tiling.Approximation.deformPoint φ u) (Tiling.Approximation.deformPoint φ w) <
          C + (4 * B₀ + 7) →
        dist (Tiling.Approximation.deformPoint φ v) (Tiling.Approximation.deformPoint φ t) <
          C + (4 * B₀ + 7) →
        Tiling.Approximation.normalEval n (Tiling.Approximation.deformPoint φ u -
          Tiling.Approximation.deformPoint φ w) =
        Tiling.Approximation.normalEval n (Tiling.Approximation.deformPoint φ v -
          Tiling.Approximation.deformPoint φ t) →
        Tiling.Approximation.normalEval n (u - w) = Tiling.Approximation.normalEval n (v - t) := by
      intro u hu w hw v hv t ht huw hvt heq
      apply (hnormalDisplacement φ (htest (Fn, εn) (by simp [specs]))
        u hu w hw v hv t ht (by linarith) (by linarith) n hnmem).mp heq
    have hh := Tiling.RationalSlopes.lift_straightFrontier_translation φ n Y WS
      hWSCloud q hq C (4 * B₀ + 7) (by linarith) hdenseLabelled
      (regularSupport K A) (regularSupport K B')
      (regularSupport Kq (f '' A)) (regularSupport Kq (f '' B'))
      htransport hforward hback hlabel hcloud hreflect a (by simpa only [hn] using ha)
    simpa only [hn] using hh
  have hCarrierTransport : ∀ i a m, regularSupport K (S i a m) =
      m • L₀.basis 1 +ᵥ regularSupport K (S i a 0) := by
    intro i a m
    let A := S i a 0
    let B' := S i a m
    let q := m • L₀.basis 1
    have hAT : A ⊆ T := fun _ ht => ht.1
    have hBT : B' ⊆ T := fun _ ht => ht.1
    have hq : q ∈ periodGroup WS := (periodGroup WS).zsmul_mem (hBasisPeriods 1) m
    have htransport : regularSupport Kq (f '' B') = f q +ᵥ regularSupport Kq (f '' A) := by
      rw [hImageS i a m, hImageS i a 0, H.carrier_transport i a m]
      change m • H.lattice.basis 1 +ᵥ _ = f (m • L₀.basis 1) +ᵥ _
      rw [map_zsmul, hBasis 1]
    have hCornersA : properVertices (regularSupport K A) ⊆ WS := by
      intro v hv
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨0, hv⟩⟩⟩
    have hCornersB : properVertices (regularSupport K B') ⊆ WS := by
      intro v hv
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨m, hv⟩⟩⟩
    have hImageCorners : f '' properVertices (regularSupport K B') =
        f q +ᵥ (f '' properVertices (regularSupport K A)) := by
      have hVB : properVertices (regularSupport Kq (f '' B')) =
          f '' properVertices (regularSupport K B') := hvertices B' hBT
      have hVA : properVertices (regularSupport Kq (f '' A)) =
          f '' properVertices (regularSupport K A) := hvertices A hAT
      rw [← hVB, ← hVA, htransport, properVertices_vadd]
    have hSourceCorners : q +ᵥ properVertices (regularSupport K A) =
        properVertices (regularSupport K B') :=
      witnessSubset_translation_of_image f hWSCloud hCornersA hCornersB hinj hq hImageCorners
    have hGerm : ∀ v ∈ properVertices (regularSupport K A),
        SameGermAt (regularSupport K A) v (regularSupport K B') (v + q) := by
      intro v hv
      have hvW := hCornersA hv
      have hvqW : v + q ∈ WS := period_add_mem hq hvW
      exact sameGerm_lift_translation f (hgerms A hAT v (hWSCloud hvW))
        (hgerms B' hBT (v + q) (hWSCloud hvqW)) htransport
    have hbackTransport : regularSupport Kq (f '' A) =
        f (-q) +ᵥ regularSupport Kq (f '' B') := by
      symm
      rw [htransport, map_neg, ← add_vadd, neg_add_cancel, zero_vadd]
    have hcarrier := properVertices_and_straightLines_determine_translate
      (hSne i a 0) (hSne i a m)
      (htile.2.1.mono (fun _ ht => hAT ht)) (htile.2.1.mono (fun _ ht => hBT ht))
      q hSourceCorners hGerm (hStraightLift A hAT B' hBT q hq htransport)
      (by
        intro δ hδ b hb
        simpa only [sub_eq_add_neg] using hStraightLift B' hBT A hAT (-q)
          ((periodGroup WS).neg_mem hq) hbackTransport δ hδ b hb)
    exact hcarrier.symm
  exact ⟨{
    lattice := L₀
    numberOfParts := H.numberOfParts
    Index := H.Index
    atom := S
    atom_nonempty := hSne
    atoms_disjoint := hSdisj
    union_eq := hSUnion
    lambdaCoefficient := H.lambdaCoefficient
    gammaCoefficient := H.gammaCoefficient
    lambdaCoefficient_ne_zero := H.lambdaCoefficient_ne_zero
    atom_periodic := hWithinPeriods
    carrier_transport := hCarrierTransport
  }⟩


end Tiling.Polygonal
