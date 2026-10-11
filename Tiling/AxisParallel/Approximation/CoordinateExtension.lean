/-
Copyright (c) 2026 The Tiling Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tiling Authors
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Increasing extensions of finite real assignments

Interpolate affinely between consecutive knots and use slope-one exterior rays.
The construction handles empty and singleton knot sets and yields a global
increasing homeomorphism. This module has no project-level dependencies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

noncomputable section

namespace Tiling.AxisParallel.Approximation

/-- Adjacency in the increasing enumeration of a finite knot set. -/
def ConsecutiveKnots {s : Finset ℝ} (x y : ↥s) : Prop :=
  x.1 < y.1 ∧ ∀ z : ↥s, ¬(x.1 < z.1 ∧ z.1 < y.1)

/-- Exact slope-one exterior, affine-on-each-gap specification used to construct the finite
order extension.  For an empty knot set all clauses are vacuous. -/
def IsFinitePiecewiseAffineExtension (s : Finset ℝ) (f : ↥s → ℝ)
    (h : ℝ → ℝ) : Prop :=
  (∀ x : ↥s, h x.1 = f x) ∧
  (∀ x y : ↥s, ConsecutiveKnots x y → ∀ z ∈ Set.Icc x.1 y.1,
    h z = f x + ((f y - f x) / (y.1 - x.1)) * (z - x.1)) ∧
  (∀ x : ↥s, (∀ y : ↥s, x.1 ≤ y.1) → ∀ z ≤ x.1,
    h z = f x + (z - x.1)) ∧
  ∀ x : ↥s, (∀ y : ↥s, y.1 ≤ x.1) → ∀ z, x.1 ≤ z →
    h z = f x + (z - x.1)

private def leftKnot (s : Finset ℝ) (z : ℝ)
    (hz : ∃ x ∈ s, x < z) : ℝ :=
  Classical.choose (Finset.exists_next_left hz)

private def rightKnot (s : Finset ℝ) (z : ℝ)
    (hz : ∃ x ∈ s, z < x) : ℝ :=
  Classical.choose (Finset.exists_next_right hz)

private lemma leftKnot_spec (s : Finset ℝ) (z : ℝ)
    (hz : ∃ x ∈ s, x < z) :
    leftKnot s z hz ∈ s ∧ leftKnot s z hz < z ∧
      ∀ x ∈ s, x < z → x ≤ leftKnot s z hz :=
  Classical.choose_spec (Finset.exists_next_left hz)

private lemma rightKnot_spec (s : Finset ℝ) (z : ℝ)
    (hz : ∃ x ∈ s, z < x) :
    rightKnot s z hz ∈ s ∧ z < rightKnot s z hz ∧
      ∀ x ∈ s, z < x → rightKnot s z hz ≤ x :=
  Classical.choose_spec (Finset.exists_next_right hz)

private def knotValue {s : Finset ℝ} (f : ↑s → ℝ) (x : ℝ) (hx : x ∈ s) : ℝ :=
  f ⟨x, hx⟩

private def finiteExtension (s : Finset ℝ) (f : ↑s → ℝ) (z : ℝ) : ℝ :=
  if hz : z ∈ s then
    knotValue f z hz
  else if hl : ∃ x ∈ s, x < z then
    if hr : ∃ x ∈ s, z < x then
      let p := leftKnot s z hl
      let q := rightKnot s z hr
      knotValue f p (leftKnot_spec s z hl).1 +
        ((knotValue f q (rightKnot_spec s z hr).1 -
            knotValue f p (leftKnot_spec s z hl).1) / (q - p)) * (z - p)
    else
      let p := leftKnot s z hl
      knotValue f p (leftKnot_spec s z hl).1 + (z - p)
  else if hr : ∃ x ∈ s, z < x then
    let q := rightKnot s z hr
    knotValue f q (rightKnot_spec s z hr).1 + (z - q)
  else
    z

private lemma finiteExtension_at_knot (s : Finset ℝ) (f : ↑s → ℝ)
    (x : ↑s) : finiteExtension s f x.1 = f x := by
  rw [finiteExtension, dif_pos x.2]
  exact congr_arg f (Subtype.ext rfl)

private lemma finiteExtension_internal (s : Finset ℝ) (f : ↑s → ℝ) (z : ℝ)
    (hz : z ∉ s) (hl : ∃ x ∈ s, x < z) (hr : ∃ x ∈ s, z < x) :
    finiteExtension s f z =
      f ⟨leftKnot s z hl, (leftKnot_spec s z hl).1⟩ +
        ((f ⟨rightKnot s z hr, (rightKnot_spec s z hr).1⟩ -
            f ⟨leftKnot s z hl, (leftKnot_spec s z hl).1⟩) /
          (rightKnot s z hr - leftKnot s z hl)) * (z - leftKnot s z hl) := by
  rw [finiteExtension, dif_neg hz, dif_pos hl, dif_pos hr]
  rfl

private lemma finiteExtension_rightExterior (s : Finset ℝ) (f : ↑s → ℝ) (z : ℝ)
    (hz : z ∉ s) (hl : ∃ x ∈ s, x < z) (hr : ¬ ∃ x ∈ s, z < x) :
    finiteExtension s f z =
      f ⟨leftKnot s z hl, (leftKnot_spec s z hl).1⟩ + (z - leftKnot s z hl) := by
  rw [finiteExtension, dif_neg hz, dif_pos hl, dif_neg hr]
  rfl

private lemma finiteExtension_leftExterior (s : Finset ℝ) (f : ↑s → ℝ) (z : ℝ)
    (hz : z ∉ s) (hl : ¬ ∃ x ∈ s, x < z) (hr : ∃ x ∈ s, z < x) :
    finiteExtension s f z =
      f ⟨rightKnot s z hr, (rightKnot_spec s z hr).1⟩ + (z - rightKnot s z hr) := by
  rw [finiteExtension, dif_neg hz, dif_neg hl, dif_pos hr]
  rfl

private lemma finiteExtension_emptyZone (s : Finset ℝ) (f : ↑s → ℝ) (z : ℝ)
    (hz : z ∉ s) (hl : ¬ ∃ x ∈ s, x < z) (hr : ¬ ∃ x ∈ s, z < x) :
    finiteExtension s f z = z := by
  rw [finiteExtension, dif_neg hz, dif_neg hl, dif_neg hr]

private lemma finiteExtension_on_gap (s : Finset ℝ) (f : ↑s → ℝ)
    (x y : ↑s) (hxy : ConsecutiveKnots x y) (z : ℝ)
    (hz : z ∈ Set.Icc x.1 y.1) :
    finiteExtension s f z =
      f x + ((f y - f x) / (y.1 - x.1)) * (z - x.1) := by
  rcases hz with ⟨hxz, hzy⟩
  rcases eq_or_lt_of_le hxz with rfl | hxz
  · rw [finiteExtension_at_knot]
    ring
  rcases eq_or_lt_of_le hzy with rfl | hzy
  · rw [finiteExtension_at_knot]
    field_simp [ne_of_gt hxy.1]
    ring
  have hzs : z ∉ s := by
    intro hmem
    exact hxy.2 ⟨z, hmem⟩ ⟨hxz, hzy⟩
  have hl : ∃ a ∈ s, a < z := ⟨x.1, x.2, hxz⟩
  have hr : ∃ a ∈ s, z < a := ⟨y.1, y.2, hzy⟩
  have hp : leftKnot s z hl = x.1 := by
    apply le_antisymm
    · by_contra h
      exact hxy.2
        ⟨leftKnot s z hl, (leftKnot_spec s z hl).1⟩
        ⟨lt_of_not_ge h, (leftKnot_spec s z hl).2.1.trans hzy⟩
    · exact (leftKnot_spec s z hl).2.2 x.1 x.2 hxz
  have hq : rightKnot s z hr = y.1 := by
    apply le_antisymm
    · exact (rightKnot_spec s z hr).2.2 y.1 y.2 hzy
    · by_contra h
      exact hxy.2
        ⟨rightKnot s z hr, (rightKnot_spec s z hr).1⟩
        ⟨hxz.trans (rightKnot_spec s z hr).2.1, lt_of_not_ge h⟩
  rw [finiteExtension, dif_neg hzs, dif_pos hl, dif_pos hr]
  simp only
  simp only [knotValue, hp, hq]

private lemma finiteExtension_left (s : Finset ℝ) (f : ↑s → ℝ)
    (x : ↑s) (hx : ∀ y : ↑s, x.1 ≤ y.1) (z : ℝ) (hz : z ≤ x.1) :
    finiteExtension s f z = f x + (z - x.1) := by
  rcases eq_or_lt_of_le hz with rfl | hz
  · rw [finiteExtension_at_knot]
    ring
  have hzs : z ∉ s := by
    intro hmem
    exact (not_le_of_gt hz) (hx ⟨z, hmem⟩)
  have hnl : ¬ ∃ a ∈ s, a < z := by
    rintro ⟨a, ha, haz⟩
    exact (not_le_of_gt hz) ((hx ⟨a, ha⟩).trans haz.le)
  have hr : ∃ a ∈ s, z < a := ⟨x.1, x.2, hz⟩
  have hq : rightKnot s z hr = x.1 := by
    apply le_antisymm
    · exact (rightKnot_spec s z hr).2.2 x.1 x.2 hz
    · exact hx ⟨rightKnot s z hr, (rightKnot_spec s z hr).1⟩
  rw [finiteExtension, dif_neg hzs, dif_neg hnl, dif_pos hr]
  simp only
  simp only [knotValue, hq]

private lemma finiteExtension_right (s : Finset ℝ) (f : ↑s → ℝ)
    (x : ↑s) (hx : ∀ y : ↑s, y.1 ≤ x.1) (z : ℝ) (hz : x.1 ≤ z) :
    finiteExtension s f z = f x + (z - x.1) := by
  rcases eq_or_lt_of_le hz with rfl | hz
  · rw [finiteExtension_at_knot]
    ring
  have hzs : z ∉ s := by
    intro hmem
    exact (not_le_of_gt hz) (hx ⟨z, hmem⟩)
  have hl : ∃ a ∈ s, a < z := ⟨x.1, x.2, hz⟩
  have hnr : ¬ ∃ a ∈ s, z < a := by
    rintro ⟨a, ha, hza⟩
    exact (not_le_of_gt hz) (hza.le.trans (hx ⟨a, ha⟩))
  have hp : leftKnot s z hl = x.1 := by
    apply le_antisymm
    · exact hx ⟨leftKnot s z hl, (leftKnot_spec s z hl).1⟩
    · exact (leftKnot_spec s z hl).2.2 x.1 x.2 hz
  rw [finiteExtension, dif_neg hzs, dif_pos hl, dif_neg hnr]
  simp only
  simp only [knotValue, hp]

private lemma finiteExtension_lt_knot (s : Finset ℝ) (f : ↑s → ℝ)
    (hf : StrictMono f) (z : ℝ) (x : ↑s) (hzx : z < x.1) :
    finiteExtension s f z < f x := by
  by_cases hz : z ∈ s
  · rw [finiteExtension_at_knot s f ⟨z, hz⟩]
    exact hf hzx
  have hr : ∃ a ∈ s, z < a := ⟨x.1, x.2, hzx⟩
  by_cases hl : ∃ a ∈ s, a < z
  · rw [finiteExtension, dif_neg hz, dif_pos hl, dif_pos hr]
    simp only
    let p : ↑s := ⟨leftKnot s z hl, (leftKnot_spec s z hl).1⟩
    let q : ↑s := ⟨rightKnot s z hr, (rightKnot_spec s z hr).1⟩
    have hpz : p.1 < z := (leftKnot_spec s z hl).2.1
    have hzq : z < q.1 := (rightKnot_spec s z hr).2.1
    have hqx : q.1 ≤ x.1 := (rightKnot_spec s z hr).2.2 x.1 x.2 hzx
    have hpq : p < q := hpz.trans hzq
    have hfpq : f p < f q := hf hpq
    have hden : 0 < q.1 - p.1 := sub_pos.mpr hpq
    have hm : 0 < (f q - f p) / (q.1 - p.1) :=
      div_pos (sub_pos.mpr hfpq) hden
    have hmul : ((f q - f p) / (q.1 - p.1)) * (q.1 - p.1) = f q - f p := by
      exact div_mul_cancel₀ _ (ne_of_gt hden)
    have hinterp :
        f p + ((f q - f p) / (q.1 - p.1)) * (z - p.1) < f q := by
      nlinarith [mul_pos hm (sub_pos.mpr hzq)]
    exact hinterp.trans_le (hf.monotone hqx)
  · rw [finiteExtension, dif_neg hz, dif_neg hl, dif_pos hr]
    simp only
    let q : ↑s := ⟨rightKnot s z hr, (rightKnot_spec s z hr).1⟩
    have hzq : z < q.1 := (rightKnot_spec s z hr).2.1
    have hqx : q.1 ≤ x.1 := (rightKnot_spec s z hr).2.2 x.1 x.2 hzx
    have hleft : f q + (z - q.1) < f q := by linarith
    exact hleft.trans_le (hf.monotone hqx)

private lemma knot_lt_finiteExtension (s : Finset ℝ) (f : ↑s → ℝ)
    (hf : StrictMono f) (x : ↑s) (z : ℝ) (hxz : x.1 < z) :
    f x < finiteExtension s f z := by
  by_cases hz : z ∈ s
  · rw [finiteExtension_at_knot s f ⟨z, hz⟩]
    exact hf hxz
  have hl : ∃ a ∈ s, a < z := ⟨x.1, x.2, hxz⟩
  by_cases hr : ∃ a ∈ s, z < a
  · rw [finiteExtension, dif_neg hz, dif_pos hl, dif_pos hr]
    simp only
    let p : ↑s := ⟨leftKnot s z hl, (leftKnot_spec s z hl).1⟩
    let q : ↑s := ⟨rightKnot s z hr, (rightKnot_spec s z hr).1⟩
    have hxp : x.1 ≤ p.1 := (leftKnot_spec s z hl).2.2 x.1 x.2 hxz
    have hpz : p.1 < z := (leftKnot_spec s z hl).2.1
    have hzq : z < q.1 := (rightKnot_spec s z hr).2.1
    have hpq : p < q := hpz.trans hzq
    have hfpq : f p < f q := hf hpq
    have hden : 0 < q.1 - p.1 := sub_pos.mpr hpq
    have hm : 0 < (f q - f p) / (q.1 - p.1) :=
      div_pos (sub_pos.mpr hfpq) hden
    have hinterp :
        f p < f p + ((f q - f p) / (q.1 - p.1)) * (z - p.1) := by
      exact lt_add_of_pos_right _ (mul_pos hm (sub_pos.mpr hpz))
    exact (hf.monotone hxp).trans_lt hinterp
  · rw [finiteExtension, dif_neg hz, dif_pos hl, dif_neg hr]
    simp only
    let p : ↑s := ⟨leftKnot s z hl, (leftKnot_spec s z hl).1⟩
    have hxp : x.1 ≤ p.1 := (leftKnot_spec s z hl).2.2 x.1 x.2 hxz
    have hpz : p.1 < z := (leftKnot_spec s z hl).2.1
    have hright : f p < f p + (z - p.1) := by linarith
    exact (hf.monotone hxp).trans_lt hright

private lemma finiteExtension_lt_of_no_knot (s : Finset ℝ) (f : ↑s → ℝ)
    (hf : StrictMono f) {a b : ℝ} (hab : a < b)
    (ha : a ∉ s) (hb : b ∉ s)
    (hn : ¬ ∃ x ∈ s, a < x ∧ x ≤ b) :
    finiteExtension s f a < finiteExtension s f b := by
  have left_iff : (∃ x ∈ s, x < a) ↔ (∃ x ∈ s, x < b) := by
    constructor
    · rintro ⟨x, hx, hxa⟩
      exact ⟨x, hx, hxa.trans hab⟩
    · rintro ⟨x, hx, hxb⟩
      have hle : x ≤ a := by
        by_contra h
        exact hn ⟨x, hx, lt_of_not_ge h, hxb.le⟩
      exact ⟨x, hx, hle.lt_of_ne (fun h ↦ ha (h ▸ hx))⟩
  have right_iff : (∃ x ∈ s, a < x) ↔ (∃ x ∈ s, b < x) := by
    constructor
    · rintro ⟨x, hx, hax⟩
      have hnot : ¬ x ≤ b := fun hxb ↦ hn ⟨x, hx, hax, hxb⟩
      exact ⟨x, hx, lt_of_not_ge hnot⟩
    · rintro ⟨x, hx, hbx⟩
      exact ⟨x, hx, hab.trans hbx⟩
  by_cases hla : ∃ x ∈ s, x < a
  · have hlb := left_iff.mp hla
    have hp : leftKnot s a hla = leftKnot s b hlb := by
      apply le_antisymm
      · exact (leftKnot_spec s b hlb).2.2 _ (leftKnot_spec s a hla).1
          ((leftKnot_spec s a hla).2.1.trans hab)
      · apply (leftKnot_spec s a hla).2.2 _ (leftKnot_spec s b hlb).1
        have hle : leftKnot s b hlb ≤ a := by
          by_contra h
          exact hn ⟨leftKnot s b hlb, (leftKnot_spec s b hlb).1,
            lt_of_not_ge h, (leftKnot_spec s b hlb).2.1.le⟩
        exact hle.lt_of_ne (fun h ↦ ha (h ▸ (leftKnot_spec s b hlb).1))
    by_cases hra : ∃ x ∈ s, a < x
    · have hrb := right_iff.mp hra
      have hq : rightKnot s a hra = rightKnot s b hrb := by
        apply le_antisymm
        · exact (rightKnot_spec s a hra).2.2 _ (rightKnot_spec s b hrb).1
            (hab.trans (rightKnot_spec s b hrb).2.1)
        · apply (rightKnot_spec s b hrb).2.2 _ (rightKnot_spec s a hra).1
          have hnot : ¬ rightKnot s a hra ≤ b := fun hle ↦
            hn ⟨rightKnot s a hra, (rightKnot_spec s a hra).1,
              (rightKnot_spec s a hra).2.1, hle⟩
          exact lt_of_not_ge hnot
      rw [finiteExtension_internal s f a ha hla hra,
        finiteExtension_internal s f b hb hlb hrb]
      let p : ↑s := ⟨leftKnot s a hla, (leftKnot_spec s a hla).1⟩
      let q : ↑s := ⟨rightKnot s a hra, (rightKnot_spec s a hra).1⟩
      let p' : ↑s := ⟨leftKnot s b hlb, (leftKnot_spec s b hlb).1⟩
      let q' : ↑s := ⟨rightKnot s b hrb, (rightKnot_spec s b hrb).1⟩
      have hp' : p = p' := Subtype.ext hp
      have hq' : q = q' := Subtype.ext hq
      have hpq : p < q :=
        (leftKnot_spec s a hla).2.1.trans (rightKnot_spec s a hra).2.1
      have hm : 0 < (f q - f p) / (q.1 - p.1) :=
        div_pos (sub_pos.mpr (hf hpq)) (sub_pos.mpr hpq)
      change f p + ((f q - f p) / (q.1 - p.1)) * (a - p.1) <
        f p' + ((f q' - f p') / (q'.1 - p'.1)) * (b - p'.1)
      rw [← hp', ← hq']
      nlinarith [mul_pos hm (sub_pos.mpr hab)]
    · have hrb : ¬ ∃ x ∈ s, b < x := fun h ↦ hra (right_iff.mpr h)
      rw [finiteExtension_rightExterior s f a ha hla hra,
        finiteExtension_rightExterior s f b hb hlb hrb]
      let p : ↑s := ⟨leftKnot s a hla, (leftKnot_spec s a hla).1⟩
      let p' : ↑s := ⟨leftKnot s b hlb, (leftKnot_spec s b hlb).1⟩
      have hp' : p = p' := Subtype.ext hp
      change f p + (a - p.1) < f p' + (b - p'.1)
      rw [← hp']
      linarith
  · have hlb : ¬ ∃ x ∈ s, x < b := fun h ↦ hla (left_iff.mpr h)
    by_cases hra : ∃ x ∈ s, a < x
    · have hrb := right_iff.mp hra
      have hq : rightKnot s a hra = rightKnot s b hrb := by
        apply le_antisymm
        · exact (rightKnot_spec s a hra).2.2 _ (rightKnot_spec s b hrb).1
            (hab.trans (rightKnot_spec s b hrb).2.1)
        · apply (rightKnot_spec s b hrb).2.2 _ (rightKnot_spec s a hra).1
          have hnot : ¬ rightKnot s a hra ≤ b := fun hle ↦
            hn ⟨rightKnot s a hra, (rightKnot_spec s a hra).1,
              (rightKnot_spec s a hra).2.1, hle⟩
          exact lt_of_not_ge hnot
      rw [finiteExtension_leftExterior s f a ha hla hra,
        finiteExtension_leftExterior s f b hb hlb hrb]
      let q : ↑s := ⟨rightKnot s a hra, (rightKnot_spec s a hra).1⟩
      let q' : ↑s := ⟨rightKnot s b hrb, (rightKnot_spec s b hrb).1⟩
      have hq' : q = q' := Subtype.ext hq
      change f q + (a - q.1) < f q' + (b - q'.1)
      rw [← hq']
      linarith
    · have hrb : ¬ ∃ x ∈ s, b < x := fun h ↦ hra (right_iff.mpr h)
      rw [finiteExtension_emptyZone s f a ha hla hra,
        finiteExtension_emptyZone s f b hb hlb hrb]
      exact hab

private lemma finiteExtension_strictMono (s : Finset ℝ) (f : ↑s → ℝ)
    (hf : StrictMono f) : StrictMono (finiteExtension s f) := by
  intro a b hab
  by_cases hk : ∃ x ∈ s, a < x ∧ x ≤ b
  · obtain ⟨x, hx, hax, hxb⟩ := hk
    have hleft := finiteExtension_lt_knot s f hf a ⟨x, hx⟩ hax
    rcases hxb.eq_or_lt with rfl | hxb
    · rw [finiteExtension_at_knot s f ⟨x, hx⟩]
      exact hleft
    · exact hleft.trans (knot_lt_finiteExtension s f hf ⟨x, hx⟩ b hxb)
  · by_cases ha : a ∈ s
    · rw [finiteExtension_at_knot s f ⟨a, ha⟩]
      exact knot_lt_finiteExtension s f hf ⟨a, ha⟩ b hab
    · have hb : b ∉ s := by
        intro hb
        exact hk ⟨b, hb, hab, le_rfl⟩
      exact finiteExtension_lt_of_no_knot s f hf hab ha hb hk

private def targetKnots (s : Finset ℝ) (f : ↑s → ℝ) : Finset ℝ :=
  s.attach.image f

private def sourceKnot (s : Finset ℝ) (f : ↑s → ℝ)
    (y : ↑(targetKnots s f)) : ↑s :=
  Classical.choose (Finset.mem_image.mp y.2)

private lemma sourceKnot_value (s : Finset ℝ) (f : ↑s → ℝ)
    (y : ↑(targetKnots s f)) : f (sourceKnot s f y) = y.1 :=
  (Classical.choose_spec (Finset.mem_image.mp y.2)).2

private lemma sourceKnot_strictMono (s : Finset ℝ) (f : ↑s → ℝ)
    (hf : StrictMono f) : StrictMono (sourceKnot s f) := by
  intro y z hyz
  apply hf.lt_iff_lt.mp
  calc
    f (sourceKnot s f y) = y.1 := sourceKnot_value s f y
    _ < z.1 := hyz
    _ = f (sourceKnot s f z) := (sourceKnot_value s f z).symm

private lemma target_mem (s : Finset ℝ) (f : ↑s → ℝ) (x : ↑s) :
    f x ∈ targetKnots s f := by
  exact Finset.mem_image.mpr ⟨x, Finset.mem_attach s x, rfl⟩

private lemma source_consecutive_of_target_consecutive
    (s : Finset ℝ) (f : ↑s → ℝ) (hf : StrictMono f)
    (p q : ↑(targetKnots s f)) (hpq : ConsecutiveKnots p q) :
    ConsecutiveKnots (sourceKnot s f p) (sourceKnot s f q) := by
  constructor
  · exact sourceKnot_strictMono s f hf hpq.1
  · intro z hz
    apply hpq.2 ⟨f z, target_mem s f z⟩
    constructor
    · rw [← sourceKnot_value s f p]
      exact hf hz.1
    · rw [← sourceKnot_value s f q]
      exact hf hz.2

private lemma source_minimum_of_target_minimum
    (s : Finset ℝ) (f : ↑s → ℝ) (hf : StrictMono f)
    (q : ↑(targetKnots s f)) (hq : ∀ r : ↑(targetKnots s f), q.1 ≤ r.1) :
    ∀ x : ↑s, (sourceKnot s f q).1 ≤ x.1 := by
  intro x
  apply hf.le_iff_le.mp
  rw [sourceKnot_value s f q]
  exact hq ⟨f x, target_mem s f x⟩

private lemma source_maximum_of_target_maximum
    (s : Finset ℝ) (f : ↑s → ℝ) (hf : StrictMono f)
    (p : ↑(targetKnots s f)) (hp : ∀ r : ↑(targetKnots s f), r.1 ≤ p.1) :
    ∀ x : ↑s, x.1 ≤ (sourceKnot s f p).1 := by
  intro x
  apply hf.le_iff_le.mp
  rw [sourceKnot_value s f p]
  exact hp ⟨f x, target_mem s f x⟩

private lemma finiteExtension_surjective (s : Finset ℝ) (f : ↑s → ℝ)
    (hf : StrictMono f) : Function.Surjective (finiteExtension s f) := by
  intro y
  let t := targetKnots s f
  by_cases hy : y ∈ t
  · let Y : ↑t := ⟨y, hy⟩
    refine ⟨(sourceKnot s f Y).1, ?_⟩
    rw [finiteExtension_at_knot]
    exact sourceKnot_value s f Y
  by_cases hl : ∃ v ∈ t, v < y
  · by_cases hr : ∃ v ∈ t, y < v
    · let P : ↑t := ⟨leftKnot t y hl, (leftKnot_spec t y hl).1⟩
      let Q : ↑t := ⟨rightKnot t y hr, (rightKnot_spec t y hr).1⟩
      have hPy : P.1 < y := (leftKnot_spec t y hl).2.1
      have hyQ : y < Q.1 := (rightKnot_spec t y hr).2.1
      have hPQ : ConsecutiveKnots P Q := by
        constructor
        · exact hPy.trans hyQ
        · intro R hR
          rcases lt_trichotomy R.1 y with hRy | hEq | hyR
          · exact (not_le_of_gt hR.1) ((leftKnot_spec t y hl).2.2 R.1 R.2 hRy)
          · exact hy (hEq ▸ R.2)
          · exact (not_le_of_gt hR.2) ((rightKnot_spec t y hr).2.2 R.1 R.2 hyR)
      let p := sourceKnot s f P
      let q := sourceKnot s f Q
      have hpq : ConsecutiveKnots p q :=
        source_consecutive_of_target_consecutive s f hf P Q hPQ
      let x := p.1 + ((q.1 - p.1) / (Q.1 - P.1)) * (y - P.1)
      have hden : 0 < Q.1 - P.1 := sub_pos.mpr hPQ.1
      have hsden : 0 < q.1 - p.1 := sub_pos.mpr hpq.1
      have hm : 0 < (q.1 - p.1) / (Q.1 - P.1) := div_pos hsden hden
      have hmul : ((q.1 - p.1) / (Q.1 - P.1)) * (Q.1 - P.1) = q.1 - p.1 :=
        div_mul_cancel₀ _ (ne_of_gt hden)
      have hpx : p.1 ≤ x := by
        dsimp [x]
        exact le_add_of_nonneg_right (mul_nonneg hm.le (sub_nonneg.mpr hPy.le))
      have hxq : x ≤ q.1 := by
        dsimp [x]
        nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hyQ.le)]
      refine ⟨x, ?_⟩
      rw [finiteExtension_on_gap s f p q hpq x ⟨hpx, hxq⟩]
      rw [sourceKnot_value s f P, sourceKnot_value s f Q]
      dsimp [x]
      field_simp [ne_of_gt hden, ne_of_gt hsden]
      ring
    · let P : ↑t := ⟨leftKnot t y hl, (leftKnot_spec t y hl).1⟩
      let p := sourceKnot s f P
      have hPmax : ∀ R : ↑t, R.1 ≤ P.1 := by
        intro R
        by_contra h
        have hPR : P.1 < R.1 := lt_of_not_ge h
        have hnotRy : ¬ R.1 < y := fun hRy ↦
          (not_le_of_gt hPR) ((leftKnot_spec t y hl).2.2 R.1 R.2 hRy)
        have hyR : y < R.1 := lt_of_le_of_ne (le_of_not_gt hnotRy)
          (fun hEq ↦ hy (hEq ▸ R.2))
        exact hr ⟨R.1, R.2, hyR⟩
      have hpmax := source_maximum_of_target_maximum s f hf P hPmax
      let x := p.1 + (y - P.1)
      have hpx : p.1 ≤ x := by dsimp [x]; linarith [(leftKnot_spec t y hl).2.1]
      refine ⟨x, ?_⟩
      rw [finiteExtension_right s f p hpmax x hpx, sourceKnot_value s f P]
      dsimp [x]
      ring
  · by_cases hr : ∃ v ∈ t, y < v
    · let Q : ↑t := ⟨rightKnot t y hr, (rightKnot_spec t y hr).1⟩
      let q := sourceKnot s f Q
      have hQmin : ∀ R : ↑t, Q.1 ≤ R.1 := by
        intro R
        by_contra h
        have hRQ : R.1 < Q.1 := lt_of_not_ge h
        have hnotyR : ¬ y < R.1 := fun hyR ↦
          (not_le_of_gt hRQ) ((rightKnot_spec t y hr).2.2 R.1 R.2 hyR)
        have hRy : R.1 < y := lt_of_le_of_ne (le_of_not_gt hnotyR)
          (fun hEq ↦ hy (hEq.symm ▸ R.2))
        exact hl ⟨R.1, R.2, hRy⟩
      have hqmin := source_minimum_of_target_minimum s f hf Q hQmin
      let x := q.1 + (y - Q.1)
      have hxq : x ≤ q.1 := by dsimp [x]; linarith [(rightKnot_spec t y hr).2.1]
      refine ⟨x, ?_⟩
      rw [finiteExtension_left s f q hqmin x hxq, sourceKnot_value s f Q]
      dsimp [x]
      ring
    · have hs : s = ∅ := by
        by_contra hs
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        have htarget : f ⟨x, hx⟩ ∈ t := target_mem s f ⟨x, hx⟩
        rcases lt_trichotomy (f ⟨x, hx⟩) y with hxy | hxy | hyx
        · exact hl ⟨f ⟨x, hx⟩, htarget, hxy⟩
        · exact hy (hxy ▸ htarget)
        · exact hr ⟨f ⟨x, hx⟩, htarget, hyx⟩
      refine ⟨y, ?_⟩
      rw [finiteExtension]
      simp [hs]

/-- A finite strictly increasing assignment extends by affine interpolation and slope-one rays. -/
theorem exists_slopeOnePiecewiseAffineExtension
    (s : Finset ℝ) (f : ↑s → ℝ) (hf : StrictMono f) :
    ∃ h : ℝ → ℝ,
      IsFinitePiecewiseAffineExtension s f h ∧ StrictMono h ∧
        Function.Surjective h := by
  refine ⟨finiteExtension s f, ?_, finiteExtension_strictMono s f hf,
    finiteExtension_surjective s f hf⟩
  refine ⟨finiteExtension_at_knot s f, finiteExtension_on_gap s f, ?_, ?_⟩
  · exact finiteExtension_left s f
  · exact finiteExtension_right s f

/-- A finite strictly increasing real assignment extends to an increasing homeomorphism. -/
theorem exists_strictMonoHomeomorph_extension
    (s : Finset ℝ) (f : ↑s → ℝ) (hf : StrictMono f) :
    ∃ h : ℝ ≃ₜ ℝ, StrictMono h ∧ ∀ x : ↑s, h x = f x := by
  obtain ⟨h, hspec, hmono, hsurj⟩ :=
    exists_slopeOnePiecewiseAffineExtension s f hf
  let e : ℝ ≃o ℝ :=
    { toEquiv := Equiv.ofBijective h ⟨hmono.injective, hsurj⟩
      map_rel_iff' := hmono.le_iff_le }
  refine ⟨e.toHomeomorph, ?_, ?_⟩
  · exact e.strictMono
  · intro x
    change h x = f x
    exact hspec.1 x


end Tiling.AxisParallel.Approximation


namespace Tiling.AxisParallel.Approximation

private def periodicAffineInterpolationSpec : Prop :=
  ∀ (n : ℕ) (p q : ℝ) (x y : ℤ → ℝ),
    0 < n → 0 < p → 0 < q →
    StrictMono x → StrictMono y →
    (∀ j : ℤ, x (j + Int.ofNat n) = x j + p) →
    (∀ j : ℤ, y (j + Int.ofNat n) = y j + q) →
    (∀ z : ℝ, ∃ j : ℤ, x j ≤ z ∧ z < x (j + 1)) →
    (∀ z : ℝ, ∃ j : ℤ, y j ≤ z ∧ z < y (j + 1)) →
    ∃ H : ℝ ≃ₜ ℝ,
      StrictMono H ∧
      (∀ j : ℤ, H (x j) = y j) ∧
      (∀ z : ℝ, H (z + p) = H z + q)

theorem periodic_shift_iterate {f : ℤ → ℝ} {n : ℕ} {p : ℝ}
    (hshift : ∀ j : ℤ, f (j + Int.ofNat n) = f j + p)
    (q j : ℤ) : f (j + q * Int.ofNat n) = f j + (q : ℝ) * p := by
  induction q using Int.induction_on with
  | zero => simp
  | @succ q ih =>
      rw [show j + (q + 1) * Int.ofNat n =
        (j + q * Int.ofNat n) + Int.ofNat n by ring,
        hshift (j + q * Int.ofNat n), ih]
      push_cast
      ring_nf
  | @pred q ih =>
      have hprev := hshift (j + (-(q : ℤ) - 1) * Int.ofNat n)
      have hprev' : f (j + (-(q : ℤ) - 1) * Int.ofNat n) =
          f (j + (-(q : ℤ)) * Int.ofNat n) - p := by
        rw [show j + (-(q : ℤ) - 1) * Int.ofNat n + Int.ofNat n =
          j + (-(q : ℤ)) * Int.ofNat n by ring] at hprev
        linarith
      rw [show j + (-(q : ℤ) - (1 : ℤ)) * Int.ofNat n =
        j + (-(q : ℤ) - 1) * Int.ofNat n by ring, hprev']
      rw [ih]
      push_cast
      ring_nf

private theorem periodicAffineInterpolation_core :
    periodicAffineInterpolationSpec := by
  intro n p q x y _hn _hp hq hx hy hxp hyp hxc hyc
  let N : ℤ := Int.ofNat n
  let S : Finset ℝ := Finset.univ.image (fun i : Fin (n + 1) => x (i : ℤ))
  have hxi : Function.Injective (fun i : Fin (n + 1) => x (i : ℤ)) := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ne_of_lt (hx (show (i : ℤ) < j by exact_mod_cast hlt))) hij
    · exact (ne_of_gt (hx (show (j : ℤ) < i by exact_mod_cast hgt))) hij
  have hScard : S.card = n + 1 := by
    rw [Finset.card_image_of_injective _ hxi, Finset.card_univ]
    simp
  let index : ↥S → Fin (n + 1) := fun z =>
    Classical.choose (Finset.mem_image.mp z.property)
  have index_spec (z : ↥S) : x (index z : ℤ) = z :=
    (Classical.choose_spec (Finset.mem_image.mp z.property)).2
  let f : ↥S → ℝ := fun z => y (index z : ℤ)
  have hf : StrictMono f := by
    intro a b hab
    have hindex_le : index a ≤ index b := by
      by_contra hnot
      have hgt : index b < index a := lt_of_not_ge hnot
      have hba : b < a := by
        change (b : ℝ) < (a : ℝ)
        rw [← index_spec b, ← index_spec a]
        exact hx (by exact_mod_cast hgt)
      exact (not_lt_of_ge hab.le) hba
    have hindex_ne : index a ≠ index b := by
      intro heq
      apply hab.ne
      apply Subtype.ext
      rw [← index_spec a, ← index_spec b, heq]
    have hindex_lt : index a < index b := lt_of_le_of_ne hindex_le hindex_ne
    exact hy (by exact_mod_cast hindex_lt)
  obtain ⟨g, hgm, hge⟩ :=
    Tiling.AxisParallel.Approximation.exists_strictMonoHomeomorph_extension S f hf
  have hge' (i : Fin (n + 1)) : g (x (i : ℤ)) = y (i : ℤ) := by
    have hmem : x (i : ℤ) ∈ S := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    let z : ↥S := ⟨x (i : ℤ), hmem⟩
    rw [hge z]
    have hi : index z = i := by
      apply hxi
      change x (index z : ℤ) = x (i : ℤ)
      rw [index_spec z]
    change y (index z : ℤ) = y (i : ℤ)
    rw [hi]
  have hgn (i : Fin (n + 1)) :
      g (x (i : ℤ)) = y (i : ℤ) := hge' i
  have hleft : g (x 0) = y 0 := by simpa using hgn 0
  have hright : g (x N) = y N := by
    have hi : (n : ℤ) = N := by rfl
    simpa [hi] using hgn ⟨n, Nat.lt_succ_self n⟩
  have hxN : x N = x 0 + p := by
    simpa [N] using hxp 0
  have hyN : y N = y 0 + q := by
    simpa [N] using hyp 0
  let F : ℝ → ℝ := fun z =>
    let k : ℤ := ⌊(z - x 0) / p⌋
    let r : ℝ := z - (k : ℝ) * p
    g r + (k : ℝ) * q
  have F_period (z : ℝ) : F (z + p) = F z + q := by
    have hfloor :
        ⌊((z + p - x 0) / p : ℝ)⌋ =
          ⌊((z - x 0) / p : ℝ)⌋ + 1 := by
      rw [show (z + p - x 0) / p = (z - x 0) / p + 1 by
        field_simp
        ring, Int.floor_add_one]
    simp only [F]
    rw [hfloor]
    push_cast
    ring_nf
  have F_shift (k : ℤ) (z : ℝ) :
      F (z + (k : ℝ) * p) = F z + (k : ℝ) * q := by
    induction k using Int.induction_on with
    | zero => simp
    | @succ k ih =>
        push_cast at ih ⊢
        calc
          F (z + (k + 1 : ℝ) * p) =
              F ((z + (k : ℝ) * p) + p) := by ring_nf
          _ = F (z + (k : ℝ) * p) + q := F_period _
          _ = F z + (k + 1 : ℝ) * q := by rw [ih]; ring
    | @pred k ih =>
        push_cast at ih ⊢
        calc
          F (z + (-k - 1 : ℝ) * p) =
              F ((z + (-k - 1 : ℝ) * p) + p) - q := by
                rw [F_period]
                ring_nf
          _ = F (z + (-k : ℝ) * p) - q := by congr 1; ring_nf
          _ = F z + (-k - 1 : ℝ) * q := by rw [ih]; ring_nf
  have F_knots (j : ℤ) : F (x j) = y j := by
    let r : ℤ := j % N
    let k : ℤ := j / N
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Int.emod_nonneg _ (by
        dsimp [N]
        exact_mod_cast (ne_of_gt _hn))
    have hrN : r < N := by
      dsimp [r]
      exact Int.emod_lt_of_pos _ (by
        dsimp [N]
        exact_mod_cast _hn)
    let i : Fin n := ⟨r.toNat, by
      have : r.toNat < N.toNat := (Int.toNat_lt hr0).2 hrN
      simpa [N] using this⟩
    have hir : (i : ℤ) = r := by
      change (r.toNat : ℤ) = r
      exact Int.toNat_of_nonneg hr0
    have hj : j = (i : ℤ) + k * N := by
      have hd : r + N * k = j := Int.emod_add_mul_ediv j N
      rw [← hd, ← hir]
      ring_nf
    have hxshift : x j = x (i : ℤ) + (k : ℝ) * p := by
      rw [hj]
      simpa [N] using periodic_shift_iterate (f := x) (n := n) hxp k (i : ℤ)
    have hyshift : y j = y (i : ℤ) + (k : ℝ) * q := by
      rw [hj]
      simpa [N] using periodic_shift_iterate (f := y) (n := n) hyp k (i : ℤ)
    have hxi0 : x 0 ≤ x (i : ℤ) := by
      apply hx.monotone
      exact_mod_cast i.1.zero_le
    have hxin : x (i : ℤ) < x N := by
      apply hx
      dsimp [N]
      exact_mod_cast i.2
    have hfloor : ⌊((x (i : ℤ) - x 0) / p : ℝ)⌋ = 0 := by
      apply (Int.floor_eq_iff).2
      constructor
      · simpa using (div_nonneg (sub_nonneg.mpr hxi0) _hp.le)
      · simpa using (div_lt_one _hp).2 (by linarith [hxin, hxN])
    have hFfund : F (x (i : ℤ)) = y (i : ℤ) := by
      simp only [F]
      rw [hfloor]
      simp only [Int.cast_zero, zero_mul, sub_zero, add_zero]
      exact hgn ⟨i.1, Nat.lt_succ_of_lt i.2⟩
    rw [hxshift, F_shift, hFfund, hyshift]
  have F_strictMono : StrictMono F := by
    intro z w hzw
    let kz : ℤ := ⌊(z - x 0) / p⌋
    let kw : ℤ := ⌊(w - x 0) / p⌋
    let rz : ℝ := z - (kz : ℝ) * p
    let rw : ℝ := w - (kw : ℝ) * p
    have hFz : F z = g rz + (kz : ℝ) * q := by simp [F, kz, rz]
    have hFw : F w = g rw + (kw : ℝ) * q := by simp [F, kw, rw]
    have hk : kz ≤ kw := by
      apply Int.floor_mono
      gcongr
    have hrzlo : x 0 ≤ rz := by
      dsimp [rz, kz]
      have h := Int.floor_le ((z - x 0) / p)
      have h' := (le_div_iff₀ _hp).mp h
      linarith
    have hrzhi : rz < x 0 + p := by
      dsimp [rz, kz]
      have h := Int.lt_floor_add_one ((z - x 0) / p)
      have h' := (div_lt_iff₀ _hp).mp h
      linarith
    have hrwlo : x 0 ≤ rw := by
      dsimp [rw, kw]
      have h := Int.floor_le ((w - x 0) / p)
      have h' := (le_div_iff₀ _hp).mp h
      linarith
    have hrwhi : rw < x 0 + p := by
      dsimp [rw, kw]
      have h := Int.lt_floor_add_one ((w - x 0) / p)
      have h' := (div_lt_iff₀ _hp).mp h
      linarith
    by_cases hkeq : kz = kw
    · have hr : rz < rw := by
        dsimp [rz, rw]
        rw [hkeq]
        linarith
      rw [hFz, hFw]
      rw [hkeq]
      exact add_lt_add_left (hgm hr) _
    · have hkl : kz < kw := lt_of_le_of_ne hk hkeq
      have hgz : g rz < y 0 + q := by
        calc
          g rz < g (x N) := hgm (hrzhi.trans_eq hxN.symm)
          _ = y 0 + q := by rw [hright, hyN]
      have hgw : y 0 ≤ g rw := by
        rw [← hleft]
        apply hgm.monotone
        exact hrwlo
      rw [hFz, hFw]
      calc
        g rz + (kz : ℝ) * q < (y 0 + q) + (kz : ℝ) * q :=
          by simpa [add_assoc] using add_lt_add_left hgz ((kz : ℝ) * q)
        _ ≤ y 0 + (kw : ℝ) * q := by
          have hstep : kz + 1 ≤ kw := by omega
          have hcast : (kz + 1 : ℤ) ≤ kw := hstep
          have hmul := mul_le_mul_of_nonneg_right
            (show (kz + 1 : ℝ) ≤ kw by exact_mod_cast hcast) hq.le
          linarith
        _ ≤ g rw + (kw : ℝ) * q := by
          exact add_le_add_left hgw _
  have F_surj : Function.Surjective F := by
    let G : ℝ ≃o ℝ := hgm.orderIsoOfSurjective g g.surjective
    intro w
    let k : ℤ := ⌊(w - y 0) / q⌋
    let s : ℝ := w - (k : ℝ) * q
    have hslo : y 0 ≤ s := by
      dsimp [s, k]
      have h := Int.floor_le ((w - y 0) / q)
      have h' := (le_div_iff₀ hq).mp h
      linarith
    have hshi : s < y 0 + q := by
      dsimp [s, k]
      have h := Int.lt_floor_add_one ((w - y 0) / q)
      have h' := (div_lt_iff₀ hq).mp h
      linarith
    let t : ℝ := G.symm s
    have hGleft : G (x 0) = y 0 := hleft
    have hGright : G (x N) = y N := hright
    have htlo : x 0 ≤ t := by
      dsimp [t]
      have h := G.symm.monotone (show G (x 0) ≤ s by simpa [hGleft] using hslo)
      simpa using h
    have hthi : t < x N := by
      dsimp [t]
      have h := G.symm.strictMono (show s < G (x N) by
        simpa [hGright, hyN] using hshi)
      simpa using h
    have htfloor : ⌊((t - x 0) / p : ℝ)⌋ = 0 := by
      apply (Int.floor_eq_iff).2
      constructor
      · simpa using (div_nonneg (sub_nonneg.mpr htlo) _hp.le)
      · simpa using (div_lt_one _hp).2 (by linarith [hthi, hxN])
    have hfloor :
        ⌊(((t + (k : ℝ) * p) - x 0) / p : ℝ)⌋ = k := by
      rw [show ((t + (k : ℝ) * p) - x 0) / p =
        (t - x 0) / p + (k : ℝ) by field_simp; ring_nf]
      rw [Int.floor_add_intCast, htfloor]
      simp
    have hgt : g t = s := by
      change G t = s
      exact G.apply_symm_apply s
    refine ⟨t + (k : ℝ) * p, ?_⟩
    simp only [F]
    rw [hfloor]
    rw [show t + (k : ℝ) * p - (k : ℝ) * p = t by ring_nf, hgt]
    dsimp [s]
    ring_nf
  let E : ℝ ≃o ℝ := F_strictMono.orderIsoOfSurjective F F_surj
  refine ⟨E.toHomeomorph, E.strictMono, F_knots, ?_⟩
  simpa [E] using F_period

private theorem periodicAffineInterpolation_proof :
    periodicAffineInterpolationSpec := periodicAffineInterpolation_core


/-- Periodic affine interpolation of two strictly increasing, cofinal, periodically indexed
real sequences.  This is the reusable lower-layer contract extracted from the band deformation
proof. -/
theorem exists_periodic_strictMonoHomeomorph_extension
    (n : ℕ) (p q : ℝ) (x y : ℤ → ℝ)
    (hn : 0 < n) (hp : 0 < p) (hq : 0 < q)
    (hx : StrictMono x) (hy : StrictMono y)
    (hxp : ∀ j : ℤ, x (j + Int.ofNat n) = x j + p)
    (hyp : ∀ j : ℤ, y (j + Int.ofNat n) = y j + q)
    (hxc : ∀ z : ℝ, ∃ j : ℤ, x j ≤ z ∧ z < x (j + 1))
    (hyc : ∀ z : ℝ, ∃ j : ℤ, y j ≤ z ∧ z < y (j + 1)) :
    ∃ H : ℝ ≃ₜ ℝ,
      StrictMono H ∧
      (∀ j : ℤ, H (x j) = y j) ∧
      (∀ z : ℝ, H (z + p) = H z + q) :=
  periodicAffineInterpolation_core n p q x y hn hp hq hx hy hxp hyp hxc hyc

end Tiling.AxisParallel.Approximation
