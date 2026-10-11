import Mathlib.Tactic
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings

/-!
# Quadrant-germ geometry

Foundations-level neutral geometry for local quadrant germs and proper-vertex
patterns. The module depends only on the intrinsic-vertex and regular-open
foundations together with Mathlib tactics.

Public API:
* quadrant_ball_nonempty;
* Quadrant, QuadrantPattern, quadrantAt, SetOccupiesQuadrant, and
  QuadrantGermOccupancy;
* exists_quadrantPattern_germ_of_localBoundaryCross and exists_quadrantPattern_germ;
* straightPattern, nonstraightPattern, oneOrThreePattern, and
  oppositePairPattern;
* nonstraightPattern_classification and
  nonstraightPattern_has_both_axis_changes;
* properVertex_of_nonstraightPattern and
  properVertex_iff_nonstraightPattern.

The signed-ray frontier bridge is an internal implementation detail. The
dependency direction is local-cross frontier geometry to a common Boolean germ,
then pattern analysis to the proper-vertex characterization.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

open Set
open Filter Topology
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel.Foundations

open Tiling AxisParallel

inductive Quadrant
  | southwest | southeast | northwest | northeast
  deriving DecidableEq

instance : Fintype Quadrant where
  elems := {.southwest, .southeast, .northwest, .northeast}
  complete q := by cases q <;> simp

abbrev QuadrantPattern := Quadrant → Bool

def quadrantAt (q : Quadrant) (a : Tiling.Plane) : Set Tiling.Plane :=
  match q with
  | .southwest => {z | z.re < a.re ∧ z.im < a.im}
  | .southeast => {z | a.re < z.re ∧ z.im < a.im}
  | .northwest => {z | z.re < a.re ∧ a.im < z.im}
  | .northeast => {z | a.re < z.re ∧ a.im < z.im}

/-- The set contains a full punctured quadrant near the anchor. -/
def SetOccupiesQuadrant (D : Set Tiling.Plane)
    (a : Tiling.Plane) (q : Quadrant) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Metric.ball a r ∩ quadrantAt q a ⊆ D

private theorem quadrantAt_convex (q : Quadrant) (a : Tiling.Plane) :
    Convex ℝ (quadrantAt q a) := by
  intro x hx y hy α β hα hβ hαβ
  have hlt : ∀ {u v c : ℝ}, u < c → v < c → α * u + β * v < c := by
    intro u v c hu hv
    by_cases hα0 : α = 0
    · have hβ1 : β = 1 := by linarith
      simp [hα0, hβ1, hv]
    · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      have hu' := mul_lt_mul_of_pos_left hu hαpos
      have hv' := mul_le_mul_of_nonneg_left (le_of_lt hv) hβ
      have hsum : α * c + β * c = c := by
        calc
          α * c + β * c = (α + β) * c := by ring
          _ = 1 * c := by rw [hαβ]
          _ = c := by ring
      nlinarith [hαβ, hsum]
  have hgt : ∀ {u v c : ℝ}, c < u → c < v → c < α * u + β * v := by
    intro u v c hu hv
    by_cases hα0 : α = 0
    · have hβ1 : β = 1 := by linarith
      simp [hα0, hβ1, hv]
    · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      have hu' := mul_lt_mul_of_pos_left hu hαpos
      have hv' := mul_le_mul_of_nonneg_left (le_of_lt hv) hβ
      have hsum : α * c + β * c = c := by
        calc
          α * c + β * c = (α + β) * c := by ring
          _ = 1 * c := by rw [hαβ]
          _ = c := by ring
      nlinarith [hαβ, hsum]
  cases q
  · dsimp [quadrantAt] at hx ⊢
    constructor
    · simpa using hlt hx.1 hy.1
    · simpa using hlt hx.2 hy.2
  · dsimp [quadrantAt] at hx ⊢
    constructor
    · simpa using hgt hx.1 hy.1
    · simpa using hlt hx.2 hy.2
  · dsimp [quadrantAt] at hx ⊢
    constructor
    · simpa using hlt hx.1 hy.1
    · simpa using hgt hx.2 hy.2
  · dsimp [quadrantAt] at hx ⊢
    constructor
    · simpa using hgt hx.1 hy.1
    · simpa using hgt hx.2 hy.2

private theorem quadrant_constancy_of_frontier_cross
    {D : Set Tiling.Plane} {a : Tiling.Plane} (q : Quadrant)
    (hopen : IsOpen D)
    (hcross : ∃ r > 0, ∀ z ∈ Metric.ball a r, z ∈ frontier D →
      z.re = a.re ∨ z.im = a.im) :
    ∃ r > 0,
      (Metric.ball a r ∩ quadrantAt q a ⊆ D ∨
        Disjoint (Metric.ball a r ∩ quadrantAt q a) D) := by
  obtain ⟨r₀, hr₀, hcross₀⟩ := hcross
  let r := r₀ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let Q : Set Tiling.Plane := Metric.ball a r ∩ quadrantAt q a
  have hQopen : IsOpen Q := by
    apply Metric.isOpen_ball.inter
    cases q
    · exact (isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt Complex.continuous_im continuous_const)
    · exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_im continuous_const)
    · exact (isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    · exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)
  have hQpre : IsPreconnected Q := by
    apply (convex_ball a r).inter (quadrantAt_convex q a) |>.isPreconnected
  let U : Set Tiling.Plane := D ∩ Q
  let V : Set Tiling.Plane := (closure D)ᶜ ∩ Q
  have hUopen : IsOpen U := hopen.inter hQopen
  have hVopen : IsOpen V := (isClosed_closure.isOpen_compl).inter hQopen
  have hUVdisj : Disjoint U V := by
    apply Set.disjoint_left.2
    intro z hzU hzV
    exact hzV.1 (subset_closure hzU.1)
  have hQsub : Q ⊆ U ∪ V := by
    intro z hzQ
    by_cases hzD : z ∈ D
    · exact Or.inl ⟨hzD, hzQ⟩
    · right
      refine ⟨?_, hzQ⟩
      intro hzcl
      have hzfront : z ∈ frontier D := by
        change z ∈ closure D \ interior D
        exact ⟨hzcl, by simpa [hopen.interior_eq] using hzD⟩
      have hzaxis : z.re ≠ a.re ∧ z.im ≠ a.im := by
        cases q <;> dsimp [quadrantAt] at hzQ ⊢ <;>
          constructor <;> linarith [hzQ.2.1, hzQ.2.2]
      have hznear : z ∈ Metric.ball a r₀ :=
        Metric.ball_subset_ball (by dsimp [r]; linarith) hzQ.1
      obtain hzre | hzim := hcross₀ z hznear hzfront
      · exact hzaxis.1 hzre
      · exact hzaxis.2 hzim
  obtain hleft | hright := hQpre.subset_or_subset hUopen hVopen hUVdisj hQsub
  · refine ⟨r, hr, ?_⟩
    exact Or.inl (fun z hz => (hleft hz).1)
  · refine ⟨r, hr, ?_⟩
    exact Or.inr (by
      apply Set.disjoint_left.2
      intro z hzQ hzD
      exact (hright hzQ).1 (subset_closure hzD))

/-- Every positive-radius ball meets each open quadrant at its anchor. -/
theorem quadrant_ball_nonempty
    {a : Tiling.Plane} {r : ℝ} (hr : 0 < r) (q : Quadrant) :
    (Metric.ball a r ∩ quadrantAt q a).Nonempty := by
  let d : ℝ := r / 4
  have hdist (sgnRe sgnIm : ℝ) (hre : sgnRe = 1 ∨ sgnRe = -1)
      (him : sgnIm = 1 ∨ sgnIm = -1) :
      dist a (a + sgnRe * (d : ℂ) + sgnIm * (d : ℂ) * Complex.I) < r := by
    rw [dist_eq_norm, Complex.norm_def, Real.sqrt_lt' hr]
    have hnorm : Complex.normSq
        (sgnRe * (d : ℂ) + sgnIm * (d : ℂ) * Complex.I) = 2 * d ^ 2 := by
      rcases hre with rfl | rfl <;> rcases him with rfl | rfl <;>
        norm_num [Complex.normSq_apply] <;> ring_nf
    rw [show a - (a + sgnRe * (d : ℂ) + sgnIm * (d : ℂ) * Complex.I) =
      -(sgnRe * (d : ℂ) + sgnIm * (d : ℂ) * Complex.I) by ring,
      Complex.normSq_neg, hnorm]
    dsimp [d]
    nlinarith
  cases q
  · refine ⟨a - (d : ℂ) - (d : ℂ) * Complex.I, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm]
      have heq : a - (d : ℂ) - (d : ℂ) * Complex.I =
          a + (-1 : ℝ) * (d : ℂ) + (-1 : ℝ) * (d : ℂ) * Complex.I := by
        norm_num; ring
      rw [heq]
      exact hdist (-1) (-1) (Or.inr rfl) (Or.inr rfl)
    · constructor <;> simp [d, hr]
  · refine ⟨a + (d : ℂ) - (d : ℂ) * Complex.I, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm]
      have heq : a + (d : ℂ) - (d : ℂ) * Complex.I =
          a + (1 : ℝ) * (d : ℂ) + (-1 : ℝ) * (d : ℂ) * Complex.I := by
        norm_num; ring
      rw [heq]
      exact hdist 1 (-1) (Or.inl rfl) (Or.inr rfl)
    · constructor <;> simp [d, hr]
  · refine ⟨a - (d : ℂ) + (d : ℂ) * Complex.I, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm]
      have heq : a - (d : ℂ) + (d : ℂ) * Complex.I =
          a + (-1 : ℝ) * (d : ℂ) + (1 : ℝ) * (d : ℂ) * Complex.I := by
        norm_num; ring
      rw [heq]
      exact hdist (-1) 1 (Or.inr rfl) (Or.inl rfl)
    · constructor <;> simp [d, hr]
  · refine ⟨a + (d : ℂ) + (d : ℂ) * Complex.I, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm]
      have heq : a + (d : ℂ) + (d : ℂ) * Complex.I =
          a + (1 : ℝ) * (d : ℂ) + (1 : ℝ) * (d : ℂ) * Complex.I := by
        norm_num
      rw [heq]
      exact hdist 1 1 (Or.inl rfl) (Or.inl rfl)
    · constructor <;> simp [d, hr]

private theorem quadrant_mem_closure_of_weak
    (q : Quadrant) (a x : Tiling.Plane) :
    (match q with
      | .southwest => x.re ≤ a.re ∧ x.im ≤ a.im
      | .southeast => a.re ≤ x.re ∧ x.im ≤ a.im
      | .northwest => x.re ≤ a.re ∧ a.im ≤ x.im
      | .northeast => a.re ≤ x.re ∧ a.im ≤ x.im) →
      x ∈ closure (quadrantAt q a) := by
  intro h
  apply Metric.mem_closure_iff.2
  intro ε hε
  obtain ⟨y, ⟨hyball, hyq⟩⟩ := quadrant_ball_nonempty hε q
  refine ⟨y, ?_, ?_⟩
  · cases q <;> dsimp [quadrantAt] at hyq ⊢
    · exact ⟨lt_of_lt_of_le hyq.1 h.1, lt_of_lt_of_le hyq.2 h.2⟩
    · exact ⟨lt_of_le_of_lt h.1 hyq.1, lt_of_lt_of_le hyq.2 h.2⟩
    · exact ⟨lt_of_lt_of_le hyq.1 h.1, lt_of_le_of_lt h.2 hyq.2⟩
    · exact ⟨lt_of_le_of_lt h.1 hyq.1, lt_of_le_of_lt h.2 hyq.2⟩
  · simpa [Metric.mem_ball, dist_comm] using hyball

private theorem localQuadrantConstancy
    {F : Set Tiling.Plane} {a : Tiling.Plane} (hopen : IsOpen F)
    (hcross : ∃ r > 0, ∀ z ∈ Metric.ball a r, z ∈ frontier F →
      z.re = a.re ∨ z.im = a.im) :
    ∃ r > 0, ∀ q : Quadrant,
      (Metric.ball a r ∩ quadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ quadrantAt q a) F) := by
  obtain ⟨r₀, hr₀, h₀⟩ := quadrant_constancy_of_frontier_cross .southwest hopen hcross
  obtain ⟨r₁, hr₁, h₁⟩ := quadrant_constancy_of_frontier_cross .southeast hopen hcross
  obtain ⟨r₂, hr₂, h₂⟩ := quadrant_constancy_of_frontier_cross .northwest hopen hcross
  obtain ⟨r₃, hr₃, h₃⟩ := quadrant_constancy_of_frontier_cross .northeast hopen hcross
  let r := min r₀ (min r₁ (min r₂ r₃))
  refine ⟨r, lt_min hr₀ (lt_min hr₁ (lt_min hr₂ hr₃)), ?_⟩
  have hr₀' : r ≤ r₀ := min_le_left _ _
  have hr₁' : r ≤ r₁ := (min_le_right r₀ _).trans (min_le_left _ _)
  have hr₂' : r ≤ r₂ := (min_le_right r₀ _).trans
    ((min_le_right r₁ _).trans (min_le_left _ _))
  have hr₃' : r ≤ r₃ := (min_le_right r₀ _).trans
    ((min_le_right r₁ _).trans (min_le_right _ _))
  intro q
  cases q
  · rcases h₀ with h | h
    · exact Or.inl (fun z hz => h (inter_subset_inter
        (Metric.ball_subset_ball hr₀') Set.Subset.rfl hz))
    · exact Or.inr (h.mono_left (inter_subset_inter
        (Metric.ball_subset_ball hr₀') Set.Subset.rfl))
  · rcases h₁ with h | h
    · exact Or.inl (fun z hz => h (inter_subset_inter
        (Metric.ball_subset_ball hr₁')
          Set.Subset.rfl hz))
    · exact Or.inr (h.mono_left (inter_subset_inter
        (Metric.ball_subset_ball hr₁')
          Set.Subset.rfl))
  · rcases h₂ with h | h
    · exact Or.inl (fun z hz => h (inter_subset_inter
        (Metric.ball_subset_ball hr₂') Set.Subset.rfl hz))
    · exact Or.inr (h.mono_left (inter_subset_inter
        (Metric.ball_subset_ball hr₂') Set.Subset.rfl))
  · rcases h₃ with h | h
    · exact Or.inl (fun z hz => h (inter_subset_inter
        (Metric.ball_subset_ball hr₃')
          Set.Subset.rfl hz))
    · exact Or.inr (h.mono_left (inter_subset_inter
        (Metric.ball_subset_ball hr₃')
          Set.Subset.rfl))

private theorem localQuadrantOccupies_iff_full
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ} (hr : 0 < r)
    (hconst : ∀ q : Quadrant,
      (Metric.ball a r ∩ quadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ quadrantAt q a) F)) (q : Quadrant) :
    SetOccupiesQuadrant F a q ↔ Metric.ball a r ∩ quadrantAt q a ⊆ F := by
  constructor
  · intro hocc
    rcases hconst q with hfull | hdisj
    · exact hfull
    · rcases hocc with ⟨s, hs, hsub⟩
      exfalso
      obtain ⟨z, hz⟩ := quadrant_ball_nonempty (lt_min hr hs) q
      have hzsmall : z ∈ Metric.ball a r ∩ quadrantAt q a :=
        inter_subset_inter (Metric.ball_subset_ball (min_le_left _ _))
          Set.Subset.rfl hz
      have hzocc : z ∈ F := hsub (inter_subset_inter
        (Metric.ball_subset_ball (min_le_right _ _)) Set.Subset.rfl hz)
      exact Set.disjoint_left.mp hdisj hzsmall hzocc
  · intro hfull
    exact ⟨r, hr, hfull⟩

private theorem localOffAxis_membership
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hr : 0 < r)
    (hconst : ∀ q : Quadrant,
      (Metric.ball a r ∩ quadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ quadrantAt q a) F))
    {x : Tiling.Plane} (hx : x ∈ Metric.ball a r)
    (hxa : x.re ≠ a.re) (hya : x.im ≠ a.im) :
    ∃ q : Quadrant, x ∈ quadrantAt q a ∧
      (x ∈ F ↔ SetOccupiesQuadrant F a q) := by
  have hbranch (q : Quadrant) (hq : x ∈ quadrantAt q a) :
      x ∈ F ↔ SetOccupiesQuadrant F a q := by
    rcases hconst q with hfull | hdisj
    · constructor
      · intro _
        exact ⟨r, hr, hfull⟩
      · intro _
        exact hfull ⟨hx, hq⟩
    · constructor
      · intro hxf
        exact False.elim (Set.disjoint_left.mp hdisj ⟨hx, hq⟩ hxf)
      · intro hocc
        rcases hocc with ⟨s, hs, hsub⟩
        obtain ⟨z, hz⟩ := quadrant_ball_nonempty (lt_min hr hs) q
        have hzsmall : z ∈ Metric.ball a r ∩ quadrantAt q a :=
          inter_subset_inter (Metric.ball_subset_ball (min_le_left _ _))
            Set.Subset.rfl hz
        have hzocc := hsub (inter_subset_inter
          (Metric.ball_subset_ball (min_le_right _ _)) Set.Subset.rfl hz)
        exact False.elim (Set.disjoint_left.mp hdisj hzsmall hzocc)
  cases lt_or_gt_of_ne hxa with
  | inl hre =>
    cases lt_or_gt_of_ne hya with
    | inl him => exact ⟨.southwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩,
        hbranch .southwest ⟨hre, him⟩⟩
    | inr him => exact ⟨.northwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩,
        hbranch .northwest ⟨hre, him⟩⟩
  | inr hre =>
    cases lt_or_gt_of_ne hya with
    | inl him => exact ⟨.southeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩,
        hbranch .southeast ⟨hre, him⟩⟩
    | inr him => exact ⟨.northeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩,
        hbranch .northeast ⟨hre, him⟩⟩


private theorem closure_inter_open_of_mem_closure
    {S U : Set Tiling.Plane} {x : Tiling.Plane}
    (hxS : x ∈ closure S) (hU : IsOpen U) (hxU : x ∈ U) :
    x ∈ closure (S ∩ U) := by
  apply mem_closure_iff.2
  intro V hV hxV
  obtain ⟨y, hyV, hyS⟩ := mem_closure_iff.1 hxS
    (V ∩ U) (hV.inter hU) ⟨hxV, hxU⟩
  exact ⟨y, hyV.1, ⟨hyS, hyV.2⟩⟩

private theorem frontier_of_quadrant_change
    {D : Set Tiling.Plane} {a x : Tiling.Plane} {r : ℝ}
    (p : QuadrantPattern)
    {q₁ q₂ : Quadrant}
    (hchange : p q₁ ≠ p q₂)
    (hpattern : ∀ q z, z ∈ Metric.ball a r → z ∈ quadrantAt q a →
      (z ∈ D ↔ p q = true))
    (hxball : x ∈ Metric.ball a r)
    (hxq₁ : x ∈ closure (quadrantAt q₁ a))
    (hxq₂ : x ∈ closure (quadrantAt q₂ a)) :
    x ∈ frontier D := by
  have hfull (q : Quadrant) (hq : p q = true) :
      Metric.ball a r ∩ quadrantAt q a ⊆ D := by
    intro z hz
    exact (hpattern q z hz.1 hz.2).mpr hq
  have hempty (q : Quadrant) (hq : p q ≠ true) :
      Metric.ball a r ∩ quadrantAt q a ⊆ Dᶜ := by
    intro z hz hzd
    exact hq ((hpattern q z hz.1 hz.2).mp hzd)
  rw [frontier_eq_closure_inter_closure]
  by_cases hq₁' : p q₁ = true
  · have hq₂' : p q₂ ≠ true := by
      intro hq₂'
      exact hchange (hq₁'.trans hq₂'.symm)
    exact ⟨closure_mono (hfull q₁ hq₁')
        (by simpa only [inter_comm] using
          closure_inter_open_of_mem_closure hxq₁ Metric.isOpen_ball hxball),
      closure_mono (hempty q₂ hq₂')
        (by simpa only [inter_comm] using
          closure_inter_open_of_mem_closure hxq₂ Metric.isOpen_ball hxball)⟩
  · have hq₁'' : p q₁ = false := by
      rcases Bool.eq_false_or_eq_true (p q₁) with h | h
      · exact False.elim (hq₁' h)
      · exact h
    have hq₂' : p q₂ = true := by
      rcases Bool.eq_false_or_eq_true (p q₂) with h | h
      · exact h
      · exact False.elim (hchange (hq₁''.trans h.symm))
    exact ⟨closure_mono (hfull q₂ hq₂')
        (by simpa only [inter_comm] using
          closure_inter_open_of_mem_closure hxq₂ Metric.isOpen_ball hxball),
      closure_mono (hempty q₁ (by
          intro h; rw [hq₁''] at h; cases h))
        (by simpa only [inter_comm] using
          closure_inter_open_of_mem_closure hxq₁ Metric.isOpen_ball hxball)⟩

def QuadrantGermOccupancy
    (D : Set Tiling.Plane) (a : Tiling.Plane) (r : ℝ)
    (p : QuadrantPattern) : Prop :=
  ∀ q z, z ∈ Metric.ball a r → z ∈ quadrantAt q a →
    (z ∈ D ↔ p q = true)

/-- A local frontier cross determines a common Boolean germ on the four quadrants. -/
theorem exists_quadrantPattern_germ_of_localBoundaryCross
    {D : Set Tiling.Plane}
    (hopen : IsOpen D)
    (_hregular : interior (closure D) = D)
    (a : Tiling.Plane)
    (hcross : ∃ r > 0, ∀ z ∈ Metric.ball a r, z ∈ frontier D →
      z.re = a.re ∨ z.im = a.im) :
    ∃ r > 0, ∃ p : QuadrantPattern,
      QuadrantGermOccupancy D a r p ∧
        ∀ q, (p q = true ↔ SetOccupiesQuadrant D a q) := by
  classical
  obtain ⟨r, hr, hconst⟩ := localQuadrantConstancy hopen hcross
  let p : QuadrantPattern := fun q =>
    if SetOccupiesQuadrant D a q then true else false
  refine ⟨r, hr, p, ?_, ?_⟩
  · intro q z hz hq
    by_cases hocc : SetOccupiesQuadrant D a q
    · have hfull : Metric.ball a r ∩ quadrantAt q a ⊆ D :=
        (localQuadrantOccupies_iff_full hr hconst q).mp hocc
      have hp : p q = true := by
        dsimp [p]
        rw [if_pos hocc]
      rw [hp]
      constructor
      · intro _
        rfl
      · intro _
        exact hfull ⟨hz, hq⟩
    · have hdisj : Disjoint (Metric.ball a r ∩ quadrantAt q a) D := by
        rcases hconst q with hfull | hdisj
        · exact False.elim (hocc ((localQuadrantOccupies_iff_full hr hconst q).mpr hfull))
        · exact hdisj
      have hp : p q = false := by
        dsimp [p]
        rw [if_neg hocc]
      rw [hp]
      constructor
      · intro hzd
        exact False.elim (Set.disjoint_left.mp hdisj ⟨hz, hq⟩ hzd)
      · intro hfalse
        cases hfalse
  · intro q
    simp [p]

theorem exists_quadrantPattern_germ
    {D : Set Tiling.Plane}
    (hopen : IsOpen D)
    (_hregular : interior (closure D) = D)
    (hpolygonal : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal D)
    (a : Tiling.Plane) :
    ∃ r > 0, ∃ p : QuadrantPattern,
      QuadrantGermOccupancy D a r p ∧
        ∀ q, (p q = true ↔ SetOccupiesQuadrant D a q) := by
  exact exists_quadrantPattern_germ_of_localBoundaryCross hopen _hregular a
    (Tiling.AxisParallel.exists_ball_frontier_subset_axisCross hpolygonal a)

def straightPattern (p : QuadrantPattern) : Prop :=
  (p .southwest = p .southeast ∧ p .northwest = p .northeast) ∨
    (p .southwest = p .northwest ∧ p .southeast = p .northeast)

def nonstraightPattern (p : QuadrantPattern) : Prop := ¬ straightPattern p

def oneOrThreePattern (p : QuadrantPattern) : Prop :=
  (p .southwest = true ∧ p .southeast = false ∧ p .northwest = false ∧ p .northeast = false) ∨
  (p .southwest = false ∧ p .southeast = true ∧ p .northwest = false ∧ p .northeast = false) ∨
  (p .southwest = false ∧ p .southeast = false ∧ p .northwest = true ∧ p .northeast = false) ∨
  (p .southwest = false ∧ p .southeast = false ∧ p .northwest = false ∧ p .northeast = true) ∨
  (p .southwest = false ∧ p .southeast = true ∧ p .northwest = true ∧ p .northeast = true) ∨
  (p .southwest = true ∧ p .southeast = false ∧ p .northwest = true ∧ p .northeast = true) ∨
  (p .southwest = true ∧ p .southeast = true ∧ p .northwest = false ∧ p .northeast = true) ∨
  (p .southwest = true ∧ p .southeast = true ∧ p .northwest = true ∧ p .northeast = false)

def oppositePairPattern (p : QuadrantPattern) : Prop :=
  (p .southwest = true ∧ p .northeast = true ∧ p .southeast = false ∧ p .northwest = false) ∨
  (p .southwest = false ∧ p .northeast = false ∧ p .southeast = true ∧ p .northwest = true)

theorem nonstraightPattern_classification (p : QuadrantPattern)
    (h : nonstraightPattern p) :
    oneOrThreePattern p ∨ oppositePairPattern p := by
  rcases Bool.eq_false_or_eq_true (p .southwest) with hsw | hsw <;>
    rcases Bool.eq_false_or_eq_true (p .southeast) with hse | hse <;>
    rcases Bool.eq_false_or_eq_true (p .northwest) with hnw | hnw <;>
    rcases Bool.eq_false_or_eq_true (p .northeast) with hne | hne <;>
    simp [nonstraightPattern, straightPattern, oneOrThreePattern,
      oppositePairPattern, hsw, hse, hnw, hne] at h ⊢

theorem nonstraightPattern_has_both_axis_changes (p : QuadrantPattern)
    (hnon : nonstraightPattern p) :
    (p .northwest ≠ p .southwest ∨ p .northeast ≠ p .southeast) ∧
      (p .northwest ≠ p .northeast ∨ p .southwest ≠ p .southeast) := by
  constructor
  · by_contra h
    push Not at h
    exact hnon (Or.inr ⟨h.1.symm, h.2.symm⟩)
  · by_contra h
    push Not at h
    exact hnon (Or.inl ⟨h.2, h.1⟩)

private def SignedAxisFrontierGerm
    (D : Set Tiling.Plane) (a : Tiling.Plane) (r : ℝ) : Prop :=
  ∃ sx sy : ℝ, (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧
    ∀ t : ℝ, 0 < t → t < r →
      a + sx * (t : Tiling.Plane) ∈ frontier D ∧
        a + sy * (t : Tiling.Plane) * Complex.I ∈ frontier D

private theorem exists_signedAxisFrontier_of_nonstraightPattern
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (_hr : 0 < r) (p : QuadrantPattern)
    (hg : QuadrantGermOccupancy D a r p)
    (hnon : nonstraightPattern p) :
    SignedAxisFrontierGerm D a (r / 2) := by
  obtain ⟨hreal, himag⟩ := nonstraightPattern_has_both_axis_changes p hnon
  have hballRPos (t : ℝ) (ht : 0 < t) (htr : t < r / 2) :
      a + (t : Tiling.Plane) ∈ Metric.ball a r := by
    rw [Metric.mem_ball, Complex.dist_eq]
    simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
    linarith
  have hballRNeg (t : ℝ) (ht : 0 < t) (htr : t < r / 2) :
      a - (t : Tiling.Plane) ∈ Metric.ball a r := by
    rw [Metric.mem_ball, Complex.dist_eq]
    rw [show a - (t : Tiling.Plane) - a = -(t : Tiling.Plane) by ring]
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    linarith
  have hballIPos (t : ℝ) (ht : 0 < t) (htr : t < r / 2) :
      a + (t : Tiling.Plane) * Complex.I ∈ Metric.ball a r := by
    rw [Metric.mem_ball, Complex.dist_eq]
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht, Complex.norm_I, mul_one]
    linarith
  have hballINeg (t : ℝ) (ht : 0 < t) (htr : t < r / 2) :
      a - (t : Tiling.Plane) * Complex.I ∈ Metric.ball a r := by
    rw [Metric.mem_ball, Complex.dist_eq]
    rw [show a - (t : Tiling.Plane) * Complex.I - a =
      -((t : Tiling.Plane) * Complex.I) by ring]
    simp only [norm_neg, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht, Complex.norm_I, mul_one]
    linarith
  have hreal' : ∃ sx : ℝ, (sx = 1 ∨ sx = -1) ∧
      ∀ t : ℝ, 0 < t → t < r / 2 →
        a + sx * (t : Tiling.Plane) ∈ frontier D := by
    rcases hreal with h | h
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro t ht htr
      have hf := frontier_of_quadrant_change p h hg (hballRNeg t ht htr)
        (by
          apply quadrant_mem_closure_of_weak .northwest a
          dsimp
          constructor
          · linarith
          · linarith)
        (by
          apply quadrant_mem_closure_of_weak .southwest a
          dsimp
          constructor
          · linarith
          · linarith)
      convert hf using 1
      norm_num [Complex.mul_re, Complex.mul_im]
      ring
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro t ht htr
      have hf := frontier_of_quadrant_change p h hg (hballRPos t ht htr)
        (by
          apply quadrant_mem_closure_of_weak .northeast a
          dsimp
          constructor
          · linarith
          · linarith)
        (by
          apply quadrant_mem_closure_of_weak .southeast a
          dsimp
          constructor
          · linarith
          · linarith)
      convert hf using 1
      norm_num [Complex.mul_re, Complex.mul_im]
  have himag' : ∃ sy : ℝ, (sy = 1 ∨ sy = -1) ∧
      ∀ t : ℝ, 0 < t → t < r / 2 →
        a + sy * (t : Tiling.Plane) * Complex.I ∈ frontier D := by
    rcases himag with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro t ht htr
      have hf := frontier_of_quadrant_change p h hg (hballIPos t ht htr)
        (by
          apply quadrant_mem_closure_of_weak .northwest a
          dsimp
          constructor
          · norm_num [Complex.mul_re, Complex.mul_im]
          · norm_num [Complex.mul_re, Complex.mul_im]
            linarith)
        (by
          apply quadrant_mem_closure_of_weak .northeast a
          dsimp
          constructor
          · norm_num [Complex.mul_re, Complex.mul_im]
          · norm_num [Complex.mul_re, Complex.mul_im]
            linarith)
      convert hf using 1
      norm_num [Complex.mul_re, Complex.mul_im]
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro t ht htr
      have hf := frontier_of_quadrant_change p h hg (hballINeg t ht htr)
        (by
          apply quadrant_mem_closure_of_weak .southwest a
          dsimp
          constructor
          · norm_num [Complex.mul_re, Complex.mul_im]
          · have him : ((t : ℂ) * Complex.I).im = t := by norm_num
            rw [him]
            linarith)
        (by
          apply quadrant_mem_closure_of_weak .southeast a
          dsimp
          constructor
          · norm_num [Complex.mul_re, Complex.mul_im]
          · have him : ((t : ℂ) * Complex.I).im = t := by norm_num
            rw [him]
            linarith)
      convert hf using 1
      norm_num [Complex.mul_re, Complex.mul_im]
      ring
  obtain ⟨sx, hsx, hsxfront⟩ := hreal'
  obtain ⟨sy, hsy, hsyfront⟩ := himag'
  exact ⟨sx, sy, hsx, hsy, fun t ht htr => ⟨hsxfront t ht htr, hsyfront t ht htr⟩⟩

private theorem not_boundaryLocallyStraight_of_signedAxisFrontier
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hr : 0 < r) (hfront : SignedAxisFrontierGerm D a r) :
    ¬Tiling.BoundaryLocallyStraightAt D a := by
  intro hstraight
  obtain ⟨L, haL, hdim, hlocal⟩ := hstraight
  obtain ⟨sx, sy, hsx, hsy, hfront⟩ := hfront
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.mp hlocal
  let t : ℝ := min (r / 2) (ε / 2)
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (half_pos hr) (half_pos hε)
  have htR : t < r := by
    dsimp [t]
    linarith [min_le_left (r / 2) (ε / 2)]
  have htε : t < ε := by
    dsimp [t]
    linarith [min_le_right (r / 2) (ε / 2)]
  have hballR : a + (t : Tiling.Plane) ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, Complex.dist_eq]
    simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact htε
  have hballI : a + (t : Tiling.Plane) * Complex.I ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, Complex.dist_eq]
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, Complex.norm_I, mul_one]
    exact htε
  have hxL : a + (sx : Tiling.Plane) * (t : Tiling.Plane) ∈ L := by
    have hdist : dist (a + (sx : Tiling.Plane) * (t : Tiling.Plane)) a < ε := by
      rcases hsx with rfl | rfl
      · simpa [Metric.mem_ball, dist_comm] using hballR
      · have hballRneg : a - (t : Tiling.Plane) ∈ Metric.ball a ε := by
          rw [Metric.mem_ball, Complex.dist_eq]
          rw [show a - (t : Tiling.Plane) - a = -(t : Tiling.Plane) by ring]
          simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
          exact htε
        simpa [Metric.mem_ball, dist_comm] using hballRneg
    exact (hεball hdist).mp (hfront t ht htR |>.1)
  have hyL : a + (sy : Tiling.Plane) * (t : Tiling.Plane) * Complex.I ∈ L := by
    have hdist : dist (a + (sy : Tiling.Plane) * (t : Tiling.Plane) * Complex.I) a < ε := by
      rcases hsy with rfl | rfl
      · simpa [Metric.mem_ball, dist_comm] using hballI
      · have hballIneg : a - (t : Tiling.Plane) * Complex.I ∈ Metric.ball a ε := by
          rw [Metric.mem_ball, Complex.dist_eq]
          rw [show a - (t : Tiling.Plane) * Complex.I - a =
            -((t : Tiling.Plane) * Complex.I) by ring]
          simp only [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos ht, Complex.norm_I, mul_one]
          exact htε
        simpa [Metric.mem_ball, dist_comm] using hballIneg
    exact (hεball hdist).mp (hfront t ht htR |>.2)
  have hxdir : (sx : Tiling.Plane) * (t : Tiling.Plane) ∈ L.direction := by
    have h := L.vsub_mem_direction hxL haL
    rw [vsub_eq_sub] at h
    convert h using 1
    all_goals abel
  have hydir : (sy : Tiling.Plane) * (t : Tiling.Plane) * Complex.I ∈ L.direction := by
    have h := L.vsub_mem_direction hyL haL
    rw [vsub_eq_sub] at h
    convert h using 1
    all_goals abel
  have h1 : (1 : Tiling.Plane) ∈ L.direction := by
    rcases hsx with rfl | rfl
    · have h := L.direction.smul_mem (t⁻¹) hxdir
      convert h using 1
      all_goals apply Complex.ext
      all_goals norm_num
      all_goals field_simp
    · have h := L.direction.smul_mem (-t⁻¹) hxdir
      convert h using 1
      all_goals apply Complex.ext
      all_goals norm_num
      all_goals field_simp
  have hI : Complex.I ∈ L.direction := by
    rcases hsy with rfl | rfl
    · have h := L.direction.smul_mem (t⁻¹) hydir
      convert h using 1
      all_goals apply Complex.ext
      all_goals norm_num
      all_goals field_simp
    · have h := L.direction.smul_mem (-t⁻¹) hydir
      convert h using 1
      all_goals apply Complex.ext
      all_goals norm_num
      all_goals field_simp
  have htop : L.direction = ⊤ := by
    apply top_unique
    rw [← Complex.basisOneI.span_eq]
    apply Submodule.span_le.2
    intro v hv
    rcases hv with ⟨i, rfl⟩
    fin_cases i
    · simpa [Complex.coe_basisOneI] using h1
    · simpa [Complex.coe_basisOneI] using hI
  have : Module.finrank ℝ L.direction = 2 := by
    rw [htop, finrank_top, Complex.finrank_real_complex]
  omega

private theorem anchor_mem_frontier_of_nonstraightPattern
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hr : 0 < r) (p : QuadrantPattern)
    (hg : QuadrantGermOccupancy D a r p)
    (hnon : nonstraightPattern p) :
    a ∈ frontier D := by
  have htrue : ∃ q, p q = true := by
    by_contra hnone
    have hfalse (q : Quadrant) : p q = false := by
      rcases Bool.eq_false_or_eq_true (p q) with h | h
      · exact False.elim (hnone ⟨q, h⟩)
      · exact h
    exact hnon (Or.inl ⟨hfalse .southwest |>.trans (hfalse .southeast).symm,
      hfalse .northwest |>.trans (hfalse .northeast).symm⟩)
  have hfalse : ∃ q, p q ≠ true := by
    by_cases h : ∃ q, p q ≠ true
    · exact h
    · have hall (q : Quadrant) : p q = true := by
        by_contra hq
        exact h ⟨q, hq⟩
      exact False.elim (hnon (Or.inl ⟨hall .southwest |>.trans (hall .southeast).symm,
        hall .northwest |>.trans (hall .northeast).symm⟩))
  have hcl : a ∈ closure D := by
    apply Metric.mem_closure_iff.2
    intro ε hε
    obtain ⟨q, hq⟩ := htrue
    let δ : ℝ := min ε r
    have hδ : 0 < δ := lt_min hε hr
    obtain ⟨z, hzball, hzq⟩ := quadrant_ball_nonempty hδ q
    have hzballR : z ∈ Metric.ball a r :=
      Metric.ball_subset_ball (min_le_right ε r) hzball
    refine ⟨z, (hg q z hzballR hzq).mpr hq, ?_⟩
    have hdist : dist z a < δ := by simpa [Metric.mem_ball, dist_comm] using hzball
    simpa [dist_comm] using hdist.trans_le (min_le_left ε r)
  have hclc : a ∈ closure Dᶜ := by
    apply Metric.mem_closure_iff.2
    intro ε hε
    obtain ⟨q, hq⟩ := hfalse
    let δ : ℝ := min ε r
    have hδ : 0 < δ := lt_min hε hr
    obtain ⟨z, hzball, hzq⟩ := quadrant_ball_nonempty hδ q
    have hzballR : z ∈ Metric.ball a r :=
      Metric.ball_subset_ball (min_le_right ε r) hzball
    have hznot : z ∉ D := by
      intro hz
      exact hq ((hg q z hzballR hzq).mp hz)
    refine ⟨z, hznot, ?_⟩
    have hdist : dist z a < δ := by simpa [Metric.mem_ball, dist_comm] using hzball
    simpa [dist_comm] using hdist.trans_le (min_le_left ε r)
  rw [frontier_eq_closure_inter_closure]
  exact ⟨hcl, hclc⟩

theorem properVertex_of_nonstraightPattern
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hr : 0 < r) (p : QuadrantPattern)
    (hg : QuadrantGermOccupancy D a r p)
    (hnon : nonstraightPattern p) :
    Tiling.AxisParallel.IsProperVertex D a := by
  have hfront : SignedAxisFrontierGerm D a (r / 2) :=
    exists_signedAxisFrontier_of_nonstraightPattern hr p hg hnon
  refine ⟨anchor_mem_frontier_of_nonstraightPattern hr p hg hnon, ?_⟩
  exact not_boundaryLocallyStraight_of_signedAxisFrontier (half_pos hr) hfront

private theorem dense_ne_coordinates (p : Tiling.Plane) :
    Dense {z : Tiling.Plane | z.re ≠ p.re ∧ z.im ≠ p.im} := by
  rw [dense_iff_inter_open]
  intro U hU hUNonempty
  obtain ⟨w, hwU⟩ := hUNonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU w hwU
  by_cases hre : p.re ≤ w.re
  · by_cases him : p.im ≤ w.im
    · obtain ⟨z, hzBall, hzQ⟩ := quadrant_ball_nonempty hr .northeast
      refine ⟨z, hball hzBall, ?_⟩
      dsimp [quadrantAt] at hzQ ⊢
      exact ⟨ne_of_gt (hre.trans_lt hzQ.1), ne_of_gt (him.trans_lt hzQ.2)⟩
    · obtain ⟨z, hzBall, hzQ⟩ := quadrant_ball_nonempty hr .southeast
      refine ⟨z, hball hzBall, ?_⟩
      dsimp [quadrantAt] at hzQ ⊢
      have hwim : w.im < p.im := lt_of_not_ge him
      exact ⟨ne_of_gt (hre.trans_lt hzQ.1), ne_of_lt (hzQ.2.trans hwim)⟩
  · have hwre : w.re < p.re := lt_of_not_ge hre
    by_cases him : p.im ≤ w.im
    · obtain ⟨z, hzBall, hzQ⟩ := quadrant_ball_nonempty hr .northwest
      refine ⟨z, hball hzBall, ?_⟩
      dsimp [quadrantAt] at hzQ ⊢
      exact ⟨ne_of_lt (hzQ.1.trans hwre), ne_of_gt (him.trans_lt hzQ.2)⟩
    · obtain ⟨z, hzBall, hzQ⟩ := quadrant_ball_nonempty hr .southwest
      refine ⟨z, hball hzBall, ?_⟩
      dsimp [quadrantAt] at hzQ ⊢
      have hwim : w.im < p.im := lt_of_not_ge him
      exact ⟨ne_of_lt (hzQ.1.trans hwre), ne_of_lt (hzQ.2.trans hwim)⟩

theorem eventually_mem_iff_of_regularOpen_of_off_cross
    {S T : Set Tiling.Plane} {p : Tiling.Plane}
    (hSOpen : IsOpen S) (hTOpen : IsOpen T)
    (hSRegular : interior (closure S) = S)
    (hTRegular : interior (closure T) = T)
    (hOffCross : ∀ᶠ z in nhds p,
      z.re ≠ p.re ∧ z.im ≠ p.im → (z ∈ S ↔ z ∈ T)) :
    ∀ᶠ z in nhds p, (z ∈ S ↔ z ∈ T) := by
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp hOffCross
  have oneDirection
      {A B : Set Tiling.Plane}
      (hAOpen : IsOpen A)
      (hBRegular : interior (closure B) = B)
      (hLocal : ∀ z ∈ Metric.ball p R,
        z.re ≠ p.re ∧ z.im ≠ p.im → (z ∈ A → z ∈ B)) :
      ∀ z ∈ Metric.ball p (R / 2), z ∈ A → z ∈ B := by
    intro z hzBall hzA
    obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.mp hAOpen z hzA
    have hzR : dist z p < R := by
      rw [Metric.mem_ball] at hzBall
      linarith
    let δ : ℝ := min (ε / 2) ((R - dist z p) / 2)
    have hδ : 0 < δ := by
      dsimp only [δ]
      exact lt_min (half_pos hε) (half_pos (sub_pos.mpr hzR))
    have hBallClosure : Metric.ball z δ ⊆ closure B := by
      intro w hwBall
      rw [mem_closure_iff]
      intro U hU hwU
      have hVOpen : IsOpen (U ∩ Metric.ball z δ) := hU.inter Metric.isOpen_ball
      have hVNonempty : (U ∩ Metric.ball z δ).Nonempty := ⟨w, hwU, hwBall⟩
      obtain ⟨y, hyCoord, hyU, hyBall⟩ :=
        (dense_ne_coordinates p).exists_mem_open hVOpen hVNonempty
      refine ⟨y, hyU, ?_⟩
      apply hLocal y
      · rw [Metric.mem_ball] at hyBall ⊢
        calc
          dist y p ≤ dist y z + dist z p := dist_triangle _ _ _
          _ < δ + dist z p := by linarith
          _ ≤ (R - dist z p) / 2 + dist z p := by
            gcongr
            exact min_le_right _ _
          _ < R := by linarith
      · exact hyCoord
      · apply hεA
        rw [Metric.mem_ball] at hyBall ⊢
        calc
          dist y z < δ := hyBall
          _ ≤ ε / 2 := min_le_left _ _
          _ < ε := half_lt_self hε
    rw [← hBRegular]
    exact interior_maximal hBallClosure Metric.isOpen_ball (Metric.mem_ball_self hδ)
  filter_upwards [Metric.ball_mem_nhds p (half_pos hR)] with z hzBall
  constructor
  · exact oneDirection hSOpen hTRegular (fun w hwR hwD =>
      (hball (by simpa only [Metric.mem_ball] using hwR) hwD).mp) z hzBall
  · exact oneDirection hTOpen hSRegular (fun w hwR hwD =>
      (hball (by simpa only [Metric.mem_ball] using hwR) hwD).mpr) z hzBall

private theorem mem_frontier_iff_of_eventually_mem_iff
    {S T : Set Tiling.Plane} {x : Tiling.Plane}
    (h : ∀ᶠ z in nhds x, (z ∈ S ↔ z ∈ T)) :
    x ∈ frontier S ↔ x ∈ frontier T := by
  have closureIff (A B : Set Tiling.Plane)
      (hAB : ∀ᶠ z in nhds x, (z ∈ A ↔ z ∈ B)) :
      x ∈ closure A ↔ x ∈ closure B := by
    rw [mem_closure_iff_frequently, mem_closure_iff_frequently]
    constructor
    · intro hA
      exact (hA.and_eventually hAB).mono fun z hz => hz.2.mp hz.1
    · intro hB
      exact (hB.and_eventually hAB).mono fun z hz => hz.2.mpr hz.1
  rw [frontier_eq_closure_inter_closure,
    frontier_eq_closure_inter_closure, mem_inter_iff, mem_inter_iff,
    closureIff S T h, closureIff Sᶜ Tᶜ (h.mono fun _ hz => not_congr hz)]

private theorem eventually_frontier_iff_of_eventually_mem_iff
    {S T : Set Tiling.Plane} {x : Tiling.Plane}
    (h : ∀ᶠ z in nhds x, (z ∈ S ↔ z ∈ T)) :
    ∀ᶠ y in nhds x, (y ∈ frontier S ↔ y ∈ frontier T) := by
  obtain ⟨U, hUsub, hUOpen, hxU⟩ := mem_nhds_iff.mp h
  filter_upwards [hUOpen.mem_nhds hxU] with y hyU
  apply mem_frontier_iff_of_eventually_mem_iff
  exact Filter.mem_of_superset (hUOpen.mem_nhds hyU) hUsub

private theorem boundaryLocallyStraight_im_gt (a : Tiling.Plane) :
    Tiling.BoundaryLocallyStraightAt {z : Tiling.Plane | a.im < z.im} a := by
  let H : Set Tiling.Plane := {z : Tiling.Plane | a.im < z.im}
  have hmem (z : Tiling.Plane) :
      z ∈ (AffineSubspace.mk' a (ℝ ∙ (1 : Tiling.Plane)) : Set Tiling.Plane) ↔
        z.im = a.im := by
    change z -ᵥ a ∈ (ℝ ∙ (1 : Tiling.Plane)) ↔ z.im = a.im
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      have h := congrArg Complex.im hc
      simp only [vsub_eq_sub, Complex.sub_im, Complex.smul_im, Complex.one_im,
        smul_eq_mul, mul_zero] at h
      linarith
    · intro h
      refine ⟨z.re - a.re, ?_⟩
      apply Complex.ext
      · simp only [vsub_eq_sub, Complex.sub_re, Complex.smul_re, Complex.one_re,
          smul_eq_mul, mul_one]
      · simp only [vsub_eq_sub, Complex.sub_im, Complex.smul_im, Complex.one_im,
          smul_eq_mul, mul_zero]
        linarith
  refine ⟨AffineSubspace.mk' a (ℝ ∙ (1 : Tiling.Plane)), ?_, ?_, ?_⟩
  · exact AffineSubspace.self_mem_mk' a _
  · rw [AffineSubspace.direction_mk']
    exact finrank_span_singleton one_ne_zero
  · exact Filter.Eventually.of_forall (fun z => by
      rw [show frontier H = {z : Tiling.Plane | z.im = a.im} by
        ext y
        simp [H, Complex.frontier_setOfPred_lt_im]]
      simpa only [Set.mem_ofPred_eq] using (hmem z).symm)

private theorem boundaryLocallyStraight_of_eventually_eq_im_gt
    {D : Set Tiling.Plane} {a : Tiling.Plane}
    (hmem : ∀ᶠ z in nhds a,
      (z ∈ D ↔ z ∈ {z : Tiling.Plane | a.im < z.im})) :
    Tiling.BoundaryLocallyStraightAt D a := by
  obtain ⟨L, haL, hdim, hHlocal⟩ := boundaryLocallyStraight_im_gt a
  obtain hfrontEq := eventually_frontier_iff_of_eventually_mem_iff hmem
  refine ⟨L, haL, hdim, ?_⟩
  filter_upwards [hHlocal, hfrontEq] with z hzH hzEq
  exact hzEq.trans hzH

private theorem boundaryLocallyStraight_im_lt (a : Tiling.Plane) :
    Tiling.BoundaryLocallyStraightAt {z : Tiling.Plane | z.im < a.im} a := by
  let H : Set Tiling.Plane := {z : Tiling.Plane | z.im < a.im}
  have hmem (z : Tiling.Plane) :
      z ∈ (AffineSubspace.mk' a (ℝ ∙ (1 : Tiling.Plane)) : Set Tiling.Plane) ↔
        z.im = a.im := by
    change z -ᵥ a ∈ (ℝ ∙ (1 : Tiling.Plane)) ↔ z.im = a.im
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      have h := congrArg Complex.im hc
      simp only [vsub_eq_sub, Complex.sub_im, Complex.smul_im, Complex.one_im,
        smul_eq_mul, mul_zero] at h
      linarith
    · intro h
      refine ⟨z.re - a.re, ?_⟩
      apply Complex.ext
      · simp only [vsub_eq_sub, Complex.sub_re, Complex.smul_re, Complex.one_re,
          smul_eq_mul, mul_one]
      · simp only [vsub_eq_sub, Complex.sub_im, Complex.smul_im, Complex.one_im,
          smul_eq_mul, mul_zero]
        linarith
  refine ⟨AffineSubspace.mk' a (ℝ ∙ (1 : Tiling.Plane)), ?_, ?_, ?_⟩
  · exact AffineSubspace.self_mem_mk' a _
  · rw [AffineSubspace.direction_mk']
    exact finrank_span_singleton one_ne_zero
  · exact Filter.Eventually.of_forall (fun z => by
      rw [show frontier H = {z : Tiling.Plane | z.im = a.im} by
        ext y
        simp [H, Complex.frontier_setOfPred_im_lt]]
      simpa only [Set.mem_ofPred_eq] using (hmem z).symm)

private theorem boundaryLocallyStraight_of_eventually_eq_im_lt
    {D : Set Tiling.Plane} {a : Tiling.Plane}
    (hmem : ∀ᶠ z in nhds a,
      (z ∈ D ↔ z ∈ {z : Tiling.Plane | z.im < a.im})) :
    Tiling.BoundaryLocallyStraightAt D a := by
  obtain ⟨L, haL, hdim, hHlocal⟩ := boundaryLocallyStraight_im_lt a
  obtain hfrontEq := eventually_frontier_iff_of_eventually_mem_iff hmem
  refine ⟨L, haL, hdim, ?_⟩
  filter_upwards [hHlocal, hfrontEq] with z hzH hzEq
  exact hzEq.trans hzH

private theorem boundaryLocallyStraight_re_gt (a : Tiling.Plane) :
    Tiling.BoundaryLocallyStraightAt {z : Tiling.Plane | a.re < z.re} a := by
  let H : Set Tiling.Plane := {z : Tiling.Plane | a.re < z.re}
  have hmem (z : Tiling.Plane) :
      z ∈ (AffineSubspace.mk' a (ℝ ∙ Complex.I) : Set Tiling.Plane) ↔
        z.re = a.re := by
    change z -ᵥ a ∈ (ℝ ∙ Complex.I) ↔ z.re = a.re
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      have h := congrArg Complex.re hc
      simp only [vsub_eq_sub, Complex.sub_re, Complex.smul_re, Complex.I_re,
        smul_eq_mul, mul_zero] at h
      linarith
    · intro h
      refine ⟨z.im - a.im, ?_⟩
      apply Complex.ext
      · simp only [vsub_eq_sub, Complex.sub_re, Complex.smul_re, Complex.I_re,
          smul_eq_mul, mul_zero]
        linarith
      · simp only [vsub_eq_sub, Complex.sub_im, Complex.smul_im, Complex.I_im,
          smul_eq_mul, mul_one]
  refine ⟨AffineSubspace.mk' a (ℝ ∙ Complex.I), ?_, ?_, ?_⟩
  · exact AffineSubspace.self_mem_mk' a _
  · rw [AffineSubspace.direction_mk']
    exact finrank_span_singleton Complex.I_ne_zero
  · exact Filter.Eventually.of_forall (fun z => by
      rw [show frontier H = {z : Tiling.Plane | z.re = a.re} by
        ext y
        simp [H, Complex.frontier_setOfPred_lt_re]]
      simpa only [Set.mem_ofPred_eq] using (hmem z).symm)

private theorem boundaryLocallyStraight_of_eventually_eq_re_gt
    {D : Set Tiling.Plane} {a : Tiling.Plane}
    (hmem : ∀ᶠ z in nhds a,
      (z ∈ D ↔ z ∈ {z : Tiling.Plane | a.re < z.re})) :
    Tiling.BoundaryLocallyStraightAt D a := by
  obtain ⟨L, haL, hdim, hHlocal⟩ := boundaryLocallyStraight_re_gt a
  obtain hfrontEq := eventually_frontier_iff_of_eventually_mem_iff hmem
  refine ⟨L, haL, hdim, ?_⟩
  filter_upwards [hHlocal, hfrontEq] with z hzH hzEq
  exact hzEq.trans hzH

private theorem boundaryLocallyStraight_re_lt (a : Tiling.Plane) :
    Tiling.BoundaryLocallyStraightAt {z : Tiling.Plane | z.re < a.re} a := by
  let H : Set Tiling.Plane := {z : Tiling.Plane | z.re < a.re}
  have hmem (z : Tiling.Plane) :
      z ∈ (AffineSubspace.mk' a (ℝ ∙ Complex.I) : Set Tiling.Plane) ↔
        z.re = a.re := by
    change z -ᵥ a ∈ (ℝ ∙ Complex.I) ↔ z.re = a.re
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      have h := congrArg Complex.re hc
      simp only [vsub_eq_sub, Complex.sub_re, Complex.smul_re, Complex.I_re,
        smul_eq_mul, mul_zero] at h
      linarith
    · intro h
      refine ⟨z.im - a.im, ?_⟩
      apply Complex.ext
      · simp only [vsub_eq_sub, Complex.sub_re, Complex.smul_re, Complex.I_re,
          smul_eq_mul, mul_zero]
        linarith
      · simp only [vsub_eq_sub, Complex.sub_im, Complex.smul_im, Complex.I_im,
          smul_eq_mul, mul_one]
  refine ⟨AffineSubspace.mk' a (ℝ ∙ Complex.I), ?_, ?_, ?_⟩
  · exact AffineSubspace.self_mem_mk' a _
  · rw [AffineSubspace.direction_mk']
    exact finrank_span_singleton Complex.I_ne_zero
  · exact Filter.Eventually.of_forall (fun z => by
      rw [show frontier H = {z : Tiling.Plane | z.re = a.re} by
        ext y
        simp [H, Complex.frontier_setOfPred_re_lt]]
      simpa only [Set.mem_ofPred_eq] using (hmem z).symm)

private theorem boundaryLocallyStraight_of_eventually_eq_re_lt
    {D : Set Tiling.Plane} {a : Tiling.Plane}
    (hmem : ∀ᶠ z in nhds a,
      (z ∈ D ↔ z ∈ {z : Tiling.Plane | z.re < a.re})) :
    Tiling.BoundaryLocallyStraightAt D a := by
  obtain ⟨L, haL, hdim, hHlocal⟩ := boundaryLocallyStraight_re_lt a
  obtain hfrontEq := eventually_frontier_iff_of_eventually_mem_iff hmem
  refine ⟨L, haL, hdim, ?_⟩
  filter_upwards [hHlocal, hfrontEq] with z hzH hzEq
  exact hzEq.trans hzH

private theorem not_frontier_of_eventually_not_mem
    {D : Set Tiling.Plane} {a : Tiling.Plane}
    (h : ∀ᶠ z in nhds a, z ∉ D) : a ∉ frontier D := by
  have hEq : ∀ᶠ z in nhds a, (z ∈ D ↔ z ∈ (∅ : Set Tiling.Plane)) :=
    h.mono (fun z hz => by simp [hz])
  have hfront := mem_frontier_iff_of_eventually_mem_iff hEq
  simpa using hfront

private theorem not_frontier_of_eventually_mem
    {D : Set Tiling.Plane} {a : Tiling.Plane}
    (h : ∀ᶠ z in nhds a, z ∈ D) : a ∉ frontier D := by
  have hEq : ∀ᶠ z in nhds a, (z ∈ D ↔ z ∈ (Set.univ : Set Tiling.Plane)) :=
    h.mono (fun z hz => by simp [hz])
  have hfront := mem_frontier_iff_of_eventually_mem_iff hEq
  simpa using hfront

private theorem not_properVertex_of_eventually_not_mem
    {D : Set Tiling.Plane} {a : Tiling.Plane}
    (h : ∀ᶠ z in nhds a, z ∉ D) : ¬Tiling.AxisParallel.IsProperVertex D a := by
  intro hproper
  exact not_frontier_of_eventually_not_mem h hproper.1

private theorem not_properVertex_of_eventually_mem
    {D : Set Tiling.Plane} {a : Tiling.Plane}
    (h : ∀ᶠ z in nhds a, z ∈ D) : ¬Tiling.AxisParallel.IsProperVertex D a := by
  intro hproper
  exact not_frontier_of_eventually_mem h hproper.1

private theorem not_properVertex_of_horizontal_upper_germ
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (hr : 0 < r) (p : QuadrantPattern)
    (hg : QuadrantGermOccupancy D a r p)
    (hsw : p .southwest = false) (hnw : p .northwest = true)
    (hrow : p .southwest = p .southeast ∧ p .northwest = p .northeast) :
    ¬Tiling.AxisParallel.IsProperVertex D a := by
  have hoff : ∀ᶠ z in nhds a,
      z.re ≠ a.re ∧ z.im ≠ a.im →
        (z ∈ D ↔ z ∈ {w : Tiling.Plane | a.im < w.im}) := by
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz hzoff
    obtain ⟨q, hzq⟩ : ∃ q : Quadrant, z ∈ quadrantAt q a := by
      rcases lt_or_gt_of_ne hzoff.1 with hre | hre <;>
        rcases lt_or_gt_of_ne hzoff.2 with him | him
      · exact ⟨.southwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.northwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.southeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.northeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
    have hD := hg q z hz hzq
    have hse : p .southeast = false := by rw [← hrow.1]; exact hsw
    have hne : p .northeast = true := by rw [← hrow.2]; exact hnw
    cases q
    all_goals simp only [quadrantAt] at hzq
    · have hnot : ¬ a.im < z.im := not_lt_of_ge (le_of_lt hzq.2)
      simpa [hsw, hnot] using hD
    · have hnot : ¬ a.im < z.im := not_lt_of_ge (le_of_lt hzq.2)
      simpa [hse, hnot] using hD
    · have hyes : a.im < z.im := hzq.2
      simpa [hnw, hyes] using hD
    · have hyes : a.im < z.im := hzq.2
      simpa [hne, hyes] using hD
  have hmodelOpen : IsOpen {w : Tiling.Plane | a.im < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hmodelRegular : interior (closure {w : Tiling.Plane | a.im < w.im}) =
      {w : Tiling.Plane | a.im < w.im} := by
    let H : Set Tiling.Plane := {w : Tiling.Plane | a.im < w.im}
    have hconv : Convex ℝ H := by
      dsimp [H]
      exact convex_halfSpace_gt Complex.imLm.isLinear a.im
    have hopenH : IsOpen H := by
      dsimp [H]
      exact isOpen_lt continuous_const Complex.continuous_im
    have hnonempty : (interior H).Nonempty := by
      refine ⟨a + Complex.I, ?_⟩
      exact mem_interior_iff_mem_nhds.mpr (hopenH.mem_nhds (by simp [H]))
    rw [hconv.interior_closure_eq_interior_of_nonempty_interior hnonempty]
    exact hopenH.interior_eq
  have hmem := eventually_mem_iff_of_regularOpen_of_off_cross hopen hmodelOpen
    hregular hmodelRegular hoff
  exact fun hproper => hproper.2
    (boundaryLocallyStraight_of_eventually_eq_im_gt hmem)

private theorem not_properVertex_of_horizontal_lower_germ
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (hr : 0 < r) (p : QuadrantPattern)
    (hg : QuadrantGermOccupancy D a r p)
    (hsw : p .southwest = true) (hnw : p .northwest = false)
    (hrow : p .southwest = p .southeast ∧ p .northwest = p .northeast) :
    ¬Tiling.AxisParallel.IsProperVertex D a := by
  have hoff : ∀ᶠ z in nhds a,
      z.re ≠ a.re ∧ z.im ≠ a.im →
        (z ∈ D ↔ z ∈ {w : Tiling.Plane | w.im < a.im}) := by
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz hzoff
    obtain ⟨q, hzq⟩ : ∃ q : Quadrant, z ∈ quadrantAt q a := by
      rcases lt_or_gt_of_ne hzoff.1 with hre | hre <;>
        rcases lt_or_gt_of_ne hzoff.2 with him | him
      · exact ⟨.southwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.northwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.southeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.northeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
    have hD := hg q z hz hzq
    have hse : p .southeast = true := by rw [← hrow.1]; exact hsw
    have hne : p .northeast = false := by rw [← hrow.2]; exact hnw
    cases q
    all_goals simp only [quadrantAt] at hzq
    · have hyes : z.im < a.im := hzq.2
      simpa [hsw, hyes] using hD
    · have hyes : z.im < a.im := hzq.2
      simpa [hse, hyes] using hD
    · have hnot : ¬ z.im < a.im := not_lt_of_ge (le_of_lt hzq.2)
      simpa [hnw, hnot] using hD
    · have hnot : ¬ z.im < a.im := not_lt_of_ge (le_of_lt hzq.2)
      simpa [hne, hnot] using hD
  have hmodelOpen : IsOpen {w : Tiling.Plane | w.im < a.im} :=
    isOpen_lt Complex.continuous_im continuous_const
  have hmodelRegular : interior (closure {w : Tiling.Plane | w.im < a.im}) =
      {w : Tiling.Plane | w.im < a.im} := by
    let H : Set Tiling.Plane := {w : Tiling.Plane | w.im < a.im}
    have hconv : Convex ℝ H := by
      dsimp [H]
      exact convex_halfSpace_lt Complex.imLm.isLinear a.im
    have hopenH : IsOpen H := by
      dsimp [H]
      exact isOpen_lt Complex.continuous_im continuous_const
    have hnonempty : (interior H).Nonempty := by
      refine ⟨a - Complex.I, ?_⟩
      exact mem_interior_iff_mem_nhds.mpr (hopenH.mem_nhds (by simp [H]))
    rw [hconv.interior_closure_eq_interior_of_nonempty_interior hnonempty]
    exact hopenH.interior_eq
  have hmem := eventually_mem_iff_of_regularOpen_of_off_cross hopen hmodelOpen
    hregular hmodelRegular hoff
  exact fun hproper => hproper.2
    (boundaryLocallyStraight_of_eventually_eq_im_lt hmem)

private theorem not_properVertex_of_horizontal_constant_false
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (hr : 0 < r) (p : QuadrantPattern)
    (hg : QuadrantGermOccupancy D a r p)
    (hsw : p .southwest = false) (hnw : p .northwest = false)
    (hrow : p .southwest = p .southeast ∧ p .northwest = p .northeast) :
    ¬Tiling.AxisParallel.IsProperVertex D a := by
  have hoff : ∀ᶠ z in nhds a,
      z.re ≠ a.re ∧ z.im ≠ a.im → (z ∈ D ↔ z ∈ (∅ : Set Tiling.Plane)) := by
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz hzoff
    obtain ⟨q, hzq⟩ : ∃ q : Quadrant, z ∈ quadrantAt q a := by
      rcases lt_or_gt_of_ne hzoff.1 with hre | hre <;>
        rcases lt_or_gt_of_ne hzoff.2 with him | him
      · exact ⟨.southwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.northwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.southeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.northeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
    have hD := hg q z hz hzq
    have hse : p .southeast = false := by rw [← hrow.1]; exact hsw
    have hne : p .northeast = false := by rw [← hrow.2]; exact hnw
    cases q <;> simp only [quadrantAt] at hzq
    all_goals simp only [hsw, hse, hnw, hne, Bool.false_eq_true,
      mem_empty_iff_false, iff_false] at hD ⊢
    all_goals exact hD
  have hmem := eventually_mem_iff_of_regularOpen_of_off_cross hopen isOpen_empty
    hregular (by simp) hoff
  apply not_properVertex_of_eventually_not_mem
  exact hmem.mono (fun z hz => by simpa using hz)

private theorem not_properVertex_of_horizontal_constant_true
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (hr : 0 < r) (p : QuadrantPattern)
    (hg : QuadrantGermOccupancy D a r p)
    (hsw : p .southwest = true) (hnw : p .northwest = true)
    (hrow : p .southwest = p .southeast ∧ p .northwest = p .northeast) :
    ¬Tiling.AxisParallel.IsProperVertex D a := by
  have hoff : ∀ᶠ z in nhds a,
      z.re ≠ a.re ∧ z.im ≠ a.im → (z ∈ D ↔ z ∈ (Set.univ : Set Tiling.Plane)) := by
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz hzoff
    obtain ⟨q, hzq⟩ : ∃ q : Quadrant, z ∈ quadrantAt q a := by
      rcases lt_or_gt_of_ne hzoff.1 with hre | hre <;>
        rcases lt_or_gt_of_ne hzoff.2 with him | him
      · exact ⟨.southwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.northwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.southeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.northeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
    have hD := hg q z hz hzq
    have hse : p .southeast = true := by rw [← hrow.1]; exact hsw
    have hne : p .northeast = true := by rw [← hrow.2]; exact hnw
    cases q <;> simp only [quadrantAt] at hzq
    all_goals simp only [hsw, hse, hnw, hne, mem_univ, iff_true] at hD ⊢
    all_goals exact hD
  have hmem := eventually_mem_iff_of_regularOpen_of_off_cross hopen isOpen_univ
    hregular (by simp) hoff
  apply not_properVertex_of_eventually_mem
  exact hmem.mono (fun z hz => by simpa using hz)

private theorem not_properVertex_of_horizontal_straight_germ
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (hr : 0 < r) (p : QuadrantPattern)
    (hg : QuadrantGermOccupancy D a r p)
    (hrow : p .southwest = p .southeast ∧ p .northwest = p .northeast) :
    ¬Tiling.AxisParallel.IsProperVertex D a := by
  rcases Bool.eq_false_or_eq_true (p .southwest) with hsw | hsw <;>
    rcases Bool.eq_false_or_eq_true (p .northwest) with hnw | hnw
  · exact not_properVertex_of_horizontal_constant_true hopen hregular hr p hg hsw hnw hrow
  · exact not_properVertex_of_horizontal_lower_germ hopen hregular hr p hg hsw hnw hrow
  · exact not_properVertex_of_horizontal_upper_germ hopen hregular hr p hg hsw hnw hrow
  · exact not_properVertex_of_horizontal_constant_false hopen hregular hr p hg hsw hnw hrow

private theorem not_properVertex_of_vertical_right_germ
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (hr : 0 < r) (p : QuadrantPattern)
    (hg : QuadrantGermOccupancy D a r p)
    (hsw : p .southwest = false) (hse : p .southeast = true)
    (hcol : p .southwest = p .northwest ∧ p .southeast = p .northeast) :
    ¬Tiling.AxisParallel.IsProperVertex D a := by
  have hoff : ∀ᶠ z in nhds a,
      z.re ≠ a.re ∧ z.im ≠ a.im →
        (z ∈ D ↔ z ∈ {w : Tiling.Plane | a.re < w.re}) := by
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz hzoff
    obtain ⟨q, hzq⟩ : ∃ q : Quadrant, z ∈ quadrantAt q a := by
      rcases lt_or_gt_of_ne hzoff.1 with hre | hre <;>
        rcases lt_or_gt_of_ne hzoff.2 with him | him
      · exact ⟨.southwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.northwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.southeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.northeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
    have hD := hg q z hz hzq
    have hnw : p .northwest = false := by rw [← hcol.1]; exact hsw
    have hne : p .northeast = true := by rw [← hcol.2]; exact hse
    cases q
    all_goals simp only [quadrantAt] at hzq
    · have hnot : ¬ a.re < z.re := not_lt_of_ge (le_of_lt hzq.1)
      simpa [hsw, hnot] using hD
    · have hyes : a.re < z.re := hzq.1
      simpa [hse, hyes] using hD
    · have hnot : ¬ a.re < z.re := not_lt_of_ge (le_of_lt hzq.1)
      simpa [hnw, hnot] using hD
    · have hyes : a.re < z.re := hzq.1
      simpa [hne, hyes] using hD
  have hmem := eventually_mem_iff_of_regularOpen_of_off_cross hopen
    (isOpen_lt continuous_const Complex.continuous_re) hregular
    (by
      let H : Set Tiling.Plane := {w : Tiling.Plane | a.re < w.re}
      have hconv : Convex ℝ H := by
        dsimp [H]
        exact convex_halfSpace_gt Complex.reLm.isLinear a.re
      have hopenH : IsOpen H := by
        dsimp [H]
        exact isOpen_lt continuous_const Complex.continuous_re
      have hnonempty : (interior H).Nonempty := by
        refine ⟨a + 1, ?_⟩
        exact mem_interior_iff_mem_nhds.mpr (hopenH.mem_nhds (by simp [H]))
      rw [hconv.interior_closure_eq_interior_of_nonempty_interior hnonempty]
      exact hopenH.interior_eq) hoff
  exact fun hproper => hproper.2
    (boundaryLocallyStraight_of_eventually_eq_re_gt hmem)

private theorem not_properVertex_of_vertical_left_germ
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (hr : 0 < r) (p : QuadrantPattern)
    (hg : QuadrantGermOccupancy D a r p)
    (hsw : p .southwest = true) (hse : p .southeast = false)
    (hcol : p .southwest = p .northwest ∧ p .southeast = p .northeast) :
    ¬Tiling.AxisParallel.IsProperVertex D a := by
  have hoff : ∀ᶠ z in nhds a,
      z.re ≠ a.re ∧ z.im ≠ a.im →
        (z ∈ D ↔ z ∈ {w : Tiling.Plane | w.re < a.re}) := by
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz hzoff
    obtain ⟨q, hzq⟩ : ∃ q : Quadrant, z ∈ quadrantAt q a := by
      rcases lt_or_gt_of_ne hzoff.1 with hre | hre <;>
        rcases lt_or_gt_of_ne hzoff.2 with him | him
      · exact ⟨.southwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.northwest, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.southeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
      · exact ⟨.northeast, by dsimp [quadrantAt]; exact ⟨hre, him⟩⟩
    have hD := hg q z hz hzq
    have hnw : p .northwest = true := by rw [← hcol.1]; exact hsw
    have hne : p .northeast = false := by rw [← hcol.2]; exact hse
    cases q
    all_goals simp only [quadrantAt] at hzq
    · have hyes : z.re < a.re := hzq.1
      simpa [hsw, hyes] using hD
    · have hnot : ¬ z.re < a.re := not_lt_of_ge (le_of_lt hzq.1)
      simpa [hse, hnot] using hD
    · have hyes : z.re < a.re := hzq.1
      simpa [hnw, hyes] using hD
    · have hnot : ¬ z.re < a.re := not_lt_of_ge (le_of_lt hzq.1)
      simpa [hne, hnot] using hD
  have hmem := eventually_mem_iff_of_regularOpen_of_off_cross hopen
    (isOpen_lt Complex.continuous_re continuous_const) hregular
    (by
      let H : Set Tiling.Plane := {w : Tiling.Plane | w.re < a.re}
      have hconv : Convex ℝ H := by
        dsimp [H]
        exact convex_halfSpace_lt Complex.reLm.isLinear a.re
      have hopenH : IsOpen H := by
        dsimp [H]
        exact isOpen_lt Complex.continuous_re continuous_const
      have hnonempty : (interior H).Nonempty := by
        refine ⟨a - 1, ?_⟩
        exact mem_interior_iff_mem_nhds.mpr (hopenH.mem_nhds (by simp [H]))
      rw [hconv.interior_closure_eq_interior_of_nonempty_interior hnonempty]
      exact hopenH.interior_eq) hoff
  exact fun hproper => hproper.2
    (boundaryLocallyStraight_of_eventually_eq_re_lt hmem)

private theorem not_properVertex_of_vertical_straight_germ
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (hr : 0 < r) (p : QuadrantPattern)
    (hg : QuadrantGermOccupancy D a r p)
    (hcol : p .southwest = p .northwest ∧ p .southeast = p .northeast) :
    ¬Tiling.AxisParallel.IsProperVertex D a := by
  cases hsw : p .southwest <;> cases hse : p .southeast
  · have hrow : p .southwest = p .southeast ∧
        p .northwest = p .northeast := by
      constructor
      · exact hsw.trans hse.symm
      · rw [← hcol.1, ← hcol.2]
        exact hsw.trans hse.symm
    have hnw : p .northwest = false := by rw [← hcol.1]; exact hsw
    exact not_properVertex_of_horizontal_constant_false
      hopen hregular hr p hg hsw hnw hrow
  · exact not_properVertex_of_vertical_right_germ
      hopen hregular hr p hg hsw hse hcol
  · exact not_properVertex_of_vertical_left_germ
      hopen hregular hr p hg hsw hse hcol
  · have hrow : p .southwest = p .southeast ∧
        p .northwest = p .northeast := by
      constructor
      · exact hsw.trans hse.symm
      · rw [← hcol.1, ← hcol.2]
        exact hsw.trans hse.symm
    have hnw : p .northwest = true := by rw [← hcol.1]; exact hsw
    exact not_properVertex_of_horizontal_constant_true
      hopen hregular hr p hg hsw hnw hrow

/-- A common four-quadrant germ is proper exactly when its Boolean pattern is nonstraight. -/
theorem properVertex_iff_nonstraightPattern
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (hr : 0 < r) (p : QuadrantPattern)
    (hg : QuadrantGermOccupancy D a r p) :
    Tiling.AxisParallel.IsProperVertex D a ↔ nonstraightPattern p := by
  constructor
  · intro hproper
    change ¬straightPattern p
    intro hstraight
    rcases hstraight with hrow | hcol
    · exact not_properVertex_of_horizontal_straight_germ
        hopen hregular hr p hg hrow hproper
    · exact not_properVertex_of_vertical_straight_germ
        hopen hregular hr p hg hcol hproper
  · exact properVertex_of_nonstraightPattern hr p hg


end Tiling.AxisParallel.Foundations
