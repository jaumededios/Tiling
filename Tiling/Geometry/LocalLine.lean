import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Connected.Clopen
import Tiling.Geometry.Plane

set_option linter.style.header false

/-!
# Local topology near a straight planar boundary

This file provides an explicit signed-side API for affine lines in `Plane = ℂ`, together with
the topological fact needed by the tiling development: if a regular-closed set has, in a ball, the
same frontier as a line through the centre, then in that ball it is one of the two closed
half-planes bounded by the line.

The line is described by an anchor `a` and a nonzero tangent vector `v`.  This representation is
deliberately computational: it lets downstream arguments name and translate the two sides without
choosing coordinates or an orientation globally.
-/

open Metric Set Topology

namespace Tiling

/-- The determinant of the ordered pair `(v, w)`. -/
def planarCross (v w : Plane) : ℝ :=
  v.re * w.im - v.im * w.re

/-- The signed side of `z` relative to the oriented line through `a` in direction `v`. -/
def signedSide (a v z : Plane) : ℝ :=
  planarCross v z - planarCross v a

/-- The affine line through `a` with tangent vector `v`, described as a zero set. -/
def affineLine (a v : Plane) : Set Plane :=
  {z | signedSide a v z = 0}

/-- The open side to the left of the oriented line `(a, v)`. -/
def positiveSide (a v : Plane) : Set Plane :=
  {z | planarCross v a < planarCross v z}

/-- The open side to the right of the oriented line `(a, v)`. -/
def negativeSide (a v : Plane) : Set Plane :=
  {z | planarCross v z < planarCross v a}

/-- The closed side to the left of the oriented line `(a, v)`. -/
def positiveHalfPlane (a v : Plane) : Set Plane :=
  {z | planarCross v a ≤ planarCross v z}

/-- The closed side to the right of the oriented line `(a, v)`. -/
def negativeHalfPlane (a v : Plane) : Set Plane :=
  {z | planarCross v z ≤ planarCross v a}

@[simp] theorem mem_positiveSide {a v z : Plane} :
    z ∈ positiveSide a v ↔ 0 < signedSide a v z := by
  change planarCross v a < planarCross v z ↔ 0 < planarCross v z - planarCross v a
  constructor <;> intro h <;> linarith

@[simp] theorem mem_negativeSide {a v z : Plane} :
    z ∈ negativeSide a v ↔ signedSide a v z < 0 := by
  change planarCross v z < planarCross v a ↔ planarCross v z - planarCross v a < 0
  constructor <;> intro h <;> linarith

@[simp] theorem mem_positiveHalfPlane {a v z : Plane} :
    z ∈ positiveHalfPlane a v ↔ 0 ≤ signedSide a v z := by
  change planarCross v a ≤ planarCross v z ↔ 0 ≤ planarCross v z - planarCross v a
  constructor <;> intro h <;> linarith

@[simp] theorem mem_negativeHalfPlane {a v z : Plane} :
    z ∈ negativeHalfPlane a v ↔ signedSide a v z ≤ 0 := by
  change planarCross v z ≤ planarCross v a ↔ planarCross v z - planarCross v a ≤ 0
  constructor <;> intro h <;> linarith

@[simp] theorem mem_affineLine {a v z : Plane} :
    z ∈ affineLine a v ↔ signedSide a v z = 0 :=
  Iff.rfl

@[simp] theorem signedSide_self (a v : Plane) : signedSide a v a = 0 := by
  simp [signedSide, planarCross]

theorem signedSide_vadd_smul (a v : Plane) (r : ℝ) :
    signedSide a v (a + r • v) = 0 := by
  simp [signedSide, planarCross]
  ring

theorem mem_affineLine_self (a v : Plane) : a ∈ affineLine a v := by
  simp [affineLine]

theorem vadd_smul_mem_affineLine (a v : Plane) (r : ℝ) :
    a + r • v ∈ affineLine a v := by
  change signedSide a v (a + r • v) = 0
  exact signedSide_vadd_smul a v r

/-- Parameterization of a nondegenerate affine line by its tangent coordinate. -/
theorem mem_affineLine_iff_exists_smul {a v z : Plane} (hv : v ≠ 0) :
    z ∈ affineLine a v ↔ ∃ t : ℝ, z = a + t • v := by
  constructor
  · intro hz
    have hcross : planarCross v z - planarCross v a = 0 := mem_affineLine.1 hz
    by_cases hvre : v.re = 0
    · have hvim : v.im ≠ 0 := by
        intro hvim
        apply hv
        apply Complex.ext <;> simp [hvre, hvim]
      refine ⟨(z.im - a.im) / v.im, ?_⟩
      apply Complex.ext
      · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
        have hre : z.re = a.re := by
          simp only [planarCross, hvre, zero_mul, zero_sub, neg_sub_neg] at hcross
          exact (mul_left_cancel₀ hvim) (by linarith)
        simp [hre, hvre]
      · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
        field_simp
        ring
    · refine ⟨(z.re - a.re) / v.re, ?_⟩
      apply Complex.ext
      · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
        field_simp
        ring
      · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
        have him : z.im = a.im + (z.re - a.re) / v.re * v.im := by
          simp only [planarCross] at hcross
          field_simp
          linear_combination hcross
        exact him
  · rintro ⟨t, rfl⟩
    exact vadd_smul_mem_affineLine a v t

theorem affineLine_eq_range (a : Plane) {v : Plane} (hv : v ≠ 0) :
    affineLine a v = Set.range fun t : ℝ ↦ a + t • v := by
  ext z
  rw [mem_affineLine_iff_exists_smul hv]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, ht.symm⟩

/-- Turn an abstract one-dimensional affine subspace through `a` into the explicit oriented-line
representation used in this file.  The chosen orientation is intentionally unspecified. -/
theorem AffineSubspace.exists_affineLine_eq {L : AffineSubspace ℝ Plane} {a : Plane}
    (ha : a ∈ L) (hdim : Module.finrank ℝ L.direction = 1) :
    ∃ v : Plane, v ≠ 0 ∧ (L : Set Plane) = affineLine a v := by
  let _ : Nontrivial L.direction := Module.nontrivial_of_finrank_eq_succ hdim
  obtain ⟨w, hw⟩ := exists_ne (0 : L.direction)
  let v : Plane := w.1
  have hv : v ≠ 0 := by
    intro hv
    apply hw
    apply Subtype.ext
    exact hv
  have hvL : v ∈ L.direction := w.2
  have hdir : L.direction = ℝ ∙ v :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim hvL hv
  refine ⟨v, hv, ?_⟩
  ext z
  constructor
  · intro hz
    have hzdir : z - a ∈ L.direction := L.vsub_mem_direction hz ha
    rw [hdir, Submodule.mem_span_singleton] at hzdir
    obtain ⟨t, ht⟩ := hzdir
    apply (mem_affineLine_iff_exists_smul hv).2
    refine ⟨t, ?_⟩
    calc
      z = (z - a) + a := by abel
      _ = t • v + a := by rw [← ht]
      _ = a + t • v := add_comm _ _
  · intro hz
    obtain ⟨t, rfl⟩ := (mem_affineLine_iff_exists_smul hv).1 hz
    rw [show a + t • v = t • v +ᵥ a by simp [vadd_eq_add, add_comm]]
    exact L.vadd_mem_of_mem_direction (hdir.symm ▸ Submodule.smul_mem _ t
      (Submodule.mem_span_singleton_self v)) ha

/-- Extract an explicit oriented line and a metric ball from an eventually-local description by
an abstract one-dimensional affine subspace. -/
theorem AffineSubspace.exists_ball_frontier_iff_affineLine
    {s : Set Plane} {L : AffineSubspace ℝ Plane} {a : Plane}
    (ha : a ∈ L) (hdim : Module.finrank ℝ L.direction = 1)
    (hlocal : ∀ᶠ z in nhds a, (z ∈ frontier s ↔ z ∈ (L : Set Plane))) :
    ∃ v : Plane, v ≠ 0 ∧ ∃ r > 0,
      ∀ z ∈ ball a r, (z ∈ frontier s ↔ z ∈ affineLine a v) := by
  obtain ⟨v, hv, hL⟩ := Tiling.AffineSubspace.exists_affineLine_eq ha hdim
  have hlocal' : ∀ᶠ z in nhds a, (z ∈ frontier s ↔ z ∈ affineLine a v) := by
    simpa only [hL] using hlocal
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hlocal'
  exact ⟨v, hv, r, hr, hball⟩

theorem continuous_signedSide (a v : Plane) : Continuous (signedSide a v) := by
  unfold signedSide planarCross
  fun_prop

theorem continuous_planarCross (v : Plane) : Continuous (planarCross v) := by
  unfold planarCross
  fun_prop

theorem isClosed_affineLine (a v : Plane) : IsClosed (affineLine a v) := by
  exact isClosed_eq (continuous_signedSide a v) continuous_const

theorem isOpen_positiveSide (a v : Plane) : IsOpen (positiveSide a v) := by
  exact isOpen_lt continuous_const (continuous_planarCross v)

theorem isOpen_negativeSide (a v : Plane) : IsOpen (negativeSide a v) := by
  exact isOpen_lt (continuous_planarCross v) continuous_const

theorem isClosed_positiveHalfPlane (a v : Plane) : IsClosed (positiveHalfPlane a v) := by
  exact isClosed_le continuous_const (continuous_planarCross v)

theorem isClosed_negativeHalfPlane (a v : Plane) : IsClosed (negativeHalfPlane a v) := by
  exact isClosed_le (continuous_planarCross v) continuous_const

/-- The determinant against a fixed vector, as a real linear map. -/
def planarCrossLinear (v : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun := planarCross v
  map_add' := by
    intro x y
    simp [planarCross]
    ring
  map_smul' := by
    intro r x
    simp [planarCross]
    ring

/-- The determinant against a fixed vector, as a continuous real linear map. -/
def planarCrossCLM (v : Plane) : Plane →L[ℝ] ℝ :=
  { planarCrossLinear v with cont := continuous_planarCross v }

@[simp] theorem planarCrossCLM_apply (v z : Plane) :
    planarCrossCLM v z = planarCross v z :=
  rfl

/-- A one-dimensional affine subspace in the plane is a level set of a continuous linear
functional.  This form is convenient for convexity and same-side arguments. -/
theorem AffineSubspace.exists_levelSet_coordinate
    (L : AffineSubspace ℝ Plane) (a : Plane) (ha : a ∈ L)
    (hdim : Module.finrank ℝ L.direction = 1) :
    ∃ ψ : Plane →L[ℝ] ℝ, ∀ z, (z ∈ L ↔ ψ z = ψ a) := by
  obtain ⟨v, _hv, hL⟩ := Tiling.AffineSubspace.exists_affineLine_eq ha hdim
  refine ⟨planarCrossCLM v, fun z ↦ ?_⟩
  change z ∈ (L : Set Plane) ↔ planarCross v z = planarCross v a
  rw [hL]
  simp only [mem_affineLine, signedSide, sub_eq_zero]

theorem convex_positiveSide (a v : Plane) : Convex ℝ (positiveSide a v) := by
  simpa [positiveSide, planarCrossLinear] using
    convex_halfSpace_gt (planarCrossLinear v).isLinear (planarCross v a)

theorem convex_negativeSide (a v : Plane) : Convex ℝ (negativeSide a v) := by
  simpa [negativeSide, planarCrossLinear] using
    convex_halfSpace_lt (planarCrossLinear v).isLinear (planarCross v a)

theorem convex_positiveHalfPlane (a v : Plane) : Convex ℝ (positiveHalfPlane a v) := by
  simpa [positiveHalfPlane, planarCrossLinear] using
    convex_halfSpace_ge (planarCrossLinear v).isLinear (planarCross v a)

theorem convex_negativeHalfPlane (a v : Plane) : Convex ℝ (negativeHalfPlane a v) := by
  simpa [negativeHalfPlane, planarCrossLinear] using
    convex_halfSpace_le (planarCrossLinear v).isLinear (planarCross v a)

theorem isPreconnected_ball_inter_positiveSide (a v : Plane) (r : ℝ) :
    IsPreconnected (ball a r ∩ positiveSide a v) :=
  ((convex_ball a r).inter (convex_positiveSide a v)).isPreconnected

theorem isPreconnected_ball_inter_negativeSide (a v : Plane) (r : ℝ) :
    IsPreconnected (ball a r ∩ negativeSide a v) :=
  ((convex_ball a r).inter (convex_negativeSide a v)).isPreconnected

@[simp] theorem signedSide_add_mul_I (a v : Plane) :
    signedSide a v (a + v * Complex.I) = Complex.normSq v := by
  simp [signedSide, planarCross, Complex.normSq_apply]
  ring

theorem signedSide_add_smul_mul_I (a v : Plane) (t : ℝ) :
    signedSide a v (a + t • (v * Complex.I)) = t * Complex.normSq v := by
  simp [signedSide, planarCross, Complex.normSq_apply]
  ring

@[simp] theorem signedSide_sub_mul_I (a v : Plane) :
    signedSide a v (a - v * Complex.I) = -Complex.normSq v := by
  simp [signedSide, planarCross, Complex.normSq_apply]
  ring

theorem signedSide_sub_smul_mul_I (a v : Plane) (t : ℝ) :
    signedSide a v (a - t • (v * Complex.I)) = -(t * Complex.normSq v) := by
  simp [signedSide, planarCross, Complex.normSq_apply]
  ring

theorem positiveSide_nonempty (a : Plane) {v : Plane} (hv : v ≠ 0) :
    (positiveSide a v).Nonempty := by
  refine ⟨a + v * Complex.I, mem_positiveSide.2 ?_⟩
  simpa using Complex.normSq_pos.2 hv

theorem negativeSide_nonempty (a : Plane) {v : Plane} (hv : v ≠ 0) :
    (negativeSide a v).Nonempty := by
  refine ⟨a - v * Complex.I, mem_negativeSide.2 ?_⟩
  simpa using neg_neg_of_pos (Complex.normSq_pos.2 hv)

/-- Each of the two components of the complement of a nondegenerate affine line is connected. -/
theorem isConnected_positiveSide (a : Plane) {v : Plane} (hv : v ≠ 0) :
    IsConnected (positiveSide a v) :=
  (convex_positiveSide a v).isConnected (positiveSide_nonempty a hv)

/-- Each of the two components of the complement of a nondegenerate affine line is connected. -/
theorem isConnected_negativeSide (a : Plane) {v : Plane} (hv : v ≠ 0) :
    IsConnected (negativeSide a v) :=
  (convex_negativeSide a v).isConnected (negativeSide_nonempty a hv)

theorem positiveHalfPlane_eq_positiveSide_union_line (a v : Plane) :
    positiveHalfPlane a v = positiveSide a v ∪ affineLine a v := by
  ext z
  simp only [mem_positiveHalfPlane, mem_union, mem_positiveSide, mem_affineLine]
  constructor
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact h.le
    · exact h.ge

theorem negativeHalfPlane_eq_negativeSide_union_line (a v : Plane) :
    negativeHalfPlane a v = negativeSide a v ∪ affineLine a v := by
  ext z
  simp only [mem_negativeHalfPlane, mem_union, mem_negativeSide, mem_affineLine]
  exact (le_iff_lt_or_eq :
    signedSide a v z ≤ 0 ↔ signedSide a v z < 0 ∨ signedSide a v z = 0)

@[simp] theorem compl_positiveHalfPlane (a v : Plane) :
    (positiveHalfPlane a v)ᶜ = negativeSide a v := by
  ext z
  simp [mem_positiveHalfPlane, mem_negativeSide]

@[simp] theorem compl_negativeHalfPlane (a v : Plane) :
    (negativeHalfPlane a v)ᶜ = positiveSide a v := by
  ext z
  simp [mem_negativeHalfPlane, mem_positiveSide]

/-- A preconnected region avoiding a frontier lies entirely on one side of the membership
partition.  The strengthened conclusion uses interiors, which is usually what local boundary
arguments need. -/
theorem IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {c s : Set X} (hc : IsPreconnected c)
    (hdisj : Disjoint c (frontier s)) :
    c ⊆ interior s ∨ c ⊆ interior sᶜ := by
  apply hc.subset_or_subset isOpen_interior isOpen_interior
  · exact disjoint_of_subset interior_subset interior_subset disjoint_compl_right
  · intro x hx
    rw [← compl_frontier_eq_union_interior]
    exact Set.mem_compl (Set.disjoint_left.1 hdisj hx)

/-- Membership at one point determines membership throughout a connected frontier-free region.
This is the pointwise form of the preceding partition lemma. -/
theorem IsPreconnected.subset_interior_of_disjoint_frontier_of_mem
    {X : Type*} [TopologicalSpace X] {c s : Set X} (hc : IsPreconnected c)
    (hdisj : Disjoint c (frontier s)) {x : X} (hxc : x ∈ c) (hxs : x ∈ s) :
    c ⊆ interior s := by
  rcases IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier hc hdisj with
    h | h
  · exact h
  · exact False.elim ((interior_subset (h hxc)) hxs)

/-- A regular-closed set with locally level-set boundary occupies opposite open half-planes on
its interior and exterior sides.  This coordinate-free formulation is convenient when a caller
already has a continuous linear coordinate for its affine line. -/
theorem local_levelSet_dichotomy (psi : Plane →L[ℝ] ℝ)
    {s : Set Plane} {x : Plane} {r : ℝ} (hr : 0 < r)
    (hregular : closure (interior s) = s) (hx : x ∈ frontier s)
    (hboundary : ∀ y ∈ ball x r, (y ∈ frontier s ↔ psi y = psi x)) :
    let positive := ball x r ∩ {y | psi x < psi y}
    let negative := ball x r ∩ {y | psi y < psi x}
    (positive ⊆ interior s ∧ negative ⊆ interior sᶜ) ∨
      (positive ⊆ interior sᶜ ∧ negative ⊆ interior s) := by
  let positive : Set Plane := ball x r ∩ {y | psi x < psi y}
  let negative : Set Plane := ball x r ∩ {y | psi y < psi x}
  have hsClosed : IsClosed s := by
    rw [← hregular]
    exact isClosed_closure
  have hxs : x ∈ s := hsClosed.frontier_subset hx
  have hxClosure : x ∈ closure (interior s) := by simpa only [hregular] using hxs
  obtain ⟨u, huBall, hu⟩ :=
    mem_closure_iff.mp hxClosure (ball x r) isOpen_ball (mem_ball_self hr)
  have hxc : x ∈ frontier sᶜ := by simpa using hx
  have hxcClosure : x ∈ closure sᶜ := frontier_subset_closure hxc
  obtain ⟨w, hwBall, hwc⟩ :=
    mem_closure_iff.mp hxcClosure (ball x r) isOpen_ball (mem_ball_self hr)
  have hw : w ∈ interior sᶜ := by
    rw [hsClosed.isOpen_compl.interior_eq]
    exact hwc
  have huNe : psi u ≠ psi x := by
    intro heq
    exact Set.disjoint_left.1 disjoint_interior_frontier hu
      ((hboundary u huBall).2 heq)
  have hwNe : psi w ≠ psi x := by
    intro heq
    have hwf : w ∈ frontier sᶜ := by simpa using (hboundary w hwBall).2 heq
    exact Set.disjoint_left.1 disjoint_interior_frontier hw hwf
  have hposPre : IsPreconnected positive :=
    ((convex_ball x r).inter
      (convex_halfSpace_gt psi.toLinearMap.isLinear (psi x))).isPreconnected
  have hnegPre : IsPreconnected negative :=
    ((convex_ball x r).inter
      (convex_halfSpace_lt psi.toLinearMap.isLinear (psi x))).isPreconnected
  have hposDisjoint : Disjoint positive (frontier s) := by
    refine Set.disjoint_left.2 fun y hy hyf ↦ ?_
    have hypos : psi x < psi y := hy.2
    exact (ne_of_gt hypos) ((hboundary y hy.1).1 hyf)
  have hnegDisjoint : Disjoint negative (frontier s) := by
    refine Set.disjoint_left.2 fun y hy hyf ↦ ?_
    have hyneg : psi y < psi x := hy.2
    exact (ne_of_lt hyneg) ((hboundary y hy.1).1 hyf)
  have hposCases :=
    IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      hposPre hposDisjoint
  have hnegCases :=
    IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      hnegPre hnegDisjoint
  rcases lt_or_gt_of_ne huNe with huNeg | huPos
  · have huIn : u ∈ negative := ⟨huBall, huNeg⟩
    have hnegIn : negative ⊆ interior s := hnegCases.resolve_right fun h ↦
      (interior_subset (h huIn)) (interior_subset hu)
    have hwPos : psi x < psi w := by
      rcases lt_or_gt_of_ne hwNe with hwNeg | hwPos
      · exact False.elim ((interior_subset hw) (interior_subset (hnegIn ⟨hwBall, hwNeg⟩)))
      · exact hwPos
    have hposOut : positive ⊆ interior sᶜ := hposCases.resolve_left fun h ↦
      (interior_subset hw) (interior_subset (h ⟨hwBall, hwPos⟩))
    exact Or.inr ⟨hposOut, hnegIn⟩
  · have huIn : u ∈ positive := ⟨huBall, huPos⟩
    have hposIn : positive ⊆ interior s := hposCases.resolve_right fun h ↦
      (interior_subset (h huIn)) (interior_subset hu)
    have hwNeg : psi w < psi x := by
      rcases lt_or_gt_of_ne hwNe with hwNeg | hwPos
      · exact hwNeg
      · exact False.elim ((interior_subset hw) (interior_subset (hposIn ⟨hwBall, hwPos⟩)))
    have hnegOut : negative ⊆ interior sᶜ := hnegCases.resolve_left fun h ↦
      (interior_subset hw) (interior_subset (h ⟨hwBall, hwNeg⟩))
    exact Or.inl ⟨hposIn, hnegOut⟩

/-- The local closed-half-plane alternative, stated for the explicit line API above.

`hregular` is the regular-closed hypothesis.  `hfrontier` says that, throughout the ball, the
frontier of `s` is exactly the line.  No global assumption on `s` is required. -/
theorem local_eq_closedHalfPlane
    {s : Set Plane} {a v : Plane} {r : ℝ} (_hv : v ≠ 0) (hr : 0 < r)
    (hregular : closure (interior s) = s)
    (hfrontier : ∀ z ∈ ball a r, (z ∈ frontier s ↔ z ∈ affineLine a v)) :
    s ∩ ball a r = positiveHalfPlane a v ∩ ball a r ∨
      s ∩ ball a r = negativeHalfPlane a v ∩ ball a r := by
  have haBall : a ∈ ball a r := by simpa using hr
  have haFrontier : a ∈ frontier s :=
    (hfrontier a haBall).2 (mem_affineLine_self a v)
  have hsClosed : IsClosed s := by
    rw [← hregular]
    exact isClosed_closure
  have hlineS {z : Plane} (hzBall : z ∈ ball a r) (hzLine : z ∈ affineLine a v) :
      z ∈ s :=
    hsClosed.frontier_subset ((hfrontier z hzBall).2 hzLine)
  have hposDisjoint : Disjoint (ball a r ∩ positiveSide a v) (frontier s) := by
    refine Set.disjoint_left.2 fun z hz hzs ↦ ?_
    have hzLine := (hfrontier z hz.1).1 hzs
    exact (ne_of_gt (mem_positiveSide.1 hz.2)) (mem_affineLine.1 hzLine)
  have hnegDisjoint : Disjoint (ball a r ∩ negativeSide a v) (frontier s) := by
    refine Set.disjoint_left.2 fun z hz hzs ↦ ?_
    have hzLine := (hfrontier z hz.1).1 hzs
    exact (ne_of_lt (mem_negativeSide.1 hz.2)) (mem_affineLine.1 hzLine)
  have hpos :=
    IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      (isPreconnected_ball_inter_positiveSide a v r) hposDisjoint
  have hneg :=
    IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      (isPreconnected_ball_inter_negativeSide a v r) hnegDisjoint
  rcases hpos with hposIn | hposOut <;> rcases hneg with hnegIn | hnegOut
  · exfalso
    have hballS : ball a r ⊆ s := by
      intro z hzBall
      rcases lt_trichotomy (signedSide a v z) 0 with hzNeg | hzZero | hzPos
      · exact interior_subset (hnegIn ⟨hzBall, mem_negativeSide.2 hzNeg⟩)
      · exact hlineS hzBall (mem_affineLine.2 hzZero)
      · exact interior_subset (hposIn ⟨hzBall, mem_positiveSide.2 hzPos⟩)
    have haInterior : a ∈ interior s :=
      interior_maximal hballS isOpen_ball haBall
    exact Set.disjoint_left.1 disjoint_interior_frontier haInterior haFrontier
  · left
    ext z
    constructor
    · rintro ⟨hzS, hzBall⟩
      refine ⟨mem_positiveHalfPlane.2 ?_, hzBall⟩
      by_contra hz
      have hzNeg : signedSide a v z < 0 := lt_of_not_ge hz
      exact (interior_subset (hnegOut ⟨hzBall, mem_negativeSide.2 hzNeg⟩)) hzS
    · rintro ⟨hzHalf, hzBall⟩
      refine ⟨?_, hzBall⟩
      rcases (mem_positiveHalfPlane.1 hzHalf).eq_or_lt with hzZero | hzPos
      · exact hlineS hzBall (mem_affineLine.2 hzZero.symm)
      · exact interior_subset (hposIn ⟨hzBall, mem_positiveSide.2 hzPos⟩)
  · right
    ext z
    constructor
    · rintro ⟨hzS, hzBall⟩
      refine ⟨mem_negativeHalfPlane.2 ?_, hzBall⟩
      by_contra hz
      have hzPos : 0 < signedSide a v z := lt_of_not_ge hz
      exact (interior_subset (hposOut ⟨hzBall, mem_positiveSide.2 hzPos⟩)) hzS
    · rintro ⟨hzHalf, hzBall⟩
      refine ⟨?_, hzBall⟩
      rcases (mem_negativeHalfPlane.1 hzHalf).eq_or_lt with hzZero | hzNeg
      · exact hlineS hzBall (mem_affineLine.2 hzZero)
      · exact interior_subset (hnegIn ⟨hzBall, mem_negativeSide.2 hzNeg⟩)
  · exfalso
    have haS : a ∈ s := hsClosed.frontier_subset haFrontier
    have haClosure : a ∈ closure (interior s) := by
      rw [hregular]
      exact haS
    obtain ⟨z, hzInterior, hzDist⟩ := (Metric.mem_closure_iff.1 haClosure) r hr
    have hzBall : z ∈ ball a r := by simpa [dist_comm] using hzDist
    have hinterDisjoint : Disjoint (interior s) (interior sᶜ) :=
      disjoint_of_subset interior_subset interior_subset disjoint_compl_right
    rcases lt_trichotomy (signedSide a v z) 0 with hzNeg | hzZero | hzPos
    · exact Set.disjoint_left.1 hinterDisjoint hzInterior
        (hnegOut ⟨hzBall, mem_negativeSide.2 hzNeg⟩)
    · exact Set.disjoint_left.1 disjoint_interior_frontier hzInterior
        ((hfrontier z hzBall).2 (mem_affineLine.2 hzZero))
    · exact Set.disjoint_left.1 hinterDisjoint hzInterior
        (hposOut ⟨hzBall, mem_positiveSide.2 hzPos⟩)

/-- Consumer-facing form of `local_eq_closedHalfPlane` for an abstract affine line specified only
locally.  This is the shape produced directly by polygonal local-straightness arguments. -/
theorem exists_local_eq_closedHalfPlane_of_affineSubspace
    {s : Set Plane} {L : AffineSubspace ℝ Plane} {a : Plane}
    (hregular : closure (interior s) = s) (ha : a ∈ L)
    (hdim : Module.finrank ℝ L.direction = 1)
    (hlocal : ∀ᶠ z in nhds a, (z ∈ frontier s ↔ z ∈ (L : Set Plane))) :
    ∃ v : Plane, v ≠ 0 ∧ ∃ r > 0,
      (s ∩ ball a r = positiveHalfPlane a v ∩ ball a r ∨
        s ∩ ball a r = negativeHalfPlane a v ∩ ball a r) := by
  obtain ⟨v, hv, r, hr, hfrontier⟩ :=
    Tiling.AffineSubspace.exists_ball_frontier_iff_affineLine ha hdim hlocal
  exact ⟨v, hv, r, hr, local_eq_closedHalfPlane hv hr hregular hfrontier⟩

end Tiling
