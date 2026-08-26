import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Executable strict linear feasibility over `ℚ²`

This module supplies the exact, executable feasibility primitive needed by the rational-polygon
compiler.  A two-variable constraint is represented as

```text
a * x + b * y < c,
```

with all coefficients and witnesses in `ℚ`.  The implementation is a specialized
Fourier--Motzkin solver:

* a one-variable constraint with negative coefficient gives a strict lower bound, one with
  positive coefficient gives a strict upper bound, and a zero coefficient is checked directly;
* elimination partitions the input by the sign of `b`; every negative/positive pair produces
  the `x`-constraint
  `(u.b * l.a - l.b * u.a) * x < u.b * l.c - l.b * u.c`;
* the one-variable solver selects `max lower + 1`, `min upper - 1`, or the midpoint of the two
  extrema, according to which bounds exist;
* after solving the eliminated system, the same extremal construction chooses `y` between all
  lower and upper vertical bounds.

The main correctness endpoints are `solve_sound`, `solve_complete`, and `solve_isSome_iff`.
Thus the executable `Option` solver succeeds exactly when the finite strict system has a rational
witness.  `isFeasible_eq_true_iff` exposes the corresponding Boolean decision theorem.
-/

namespace Tiling.RationalPolygonal.LinearFeasibility

/-- A strict affine inequality `a * x + b * y < c` over the rationals. -/
@[ext]
structure StrictInequality where
  /-- Coefficient of the first variable `x`. -/
  a : ℚ
  /-- Coefficient of the second variable `y`. -/
  b : ℚ
  /-- Strict upper constant on the affine expression. -/
  c : ℚ
deriving DecidableEq, Repr

/-- A strict one-variable inequality `a * x < c`. -/
@[ext]
structure StrictInequality1 where
  /-- Coefficient of the variable `x`. -/
  a : ℚ
  /-- Strict upper constant on the linear expression. -/
  c : ℚ
deriving DecidableEq, Repr

/-- Satisfaction of a two-variable strict inequality. -/
def StrictInequality.Satisfies (q : StrictInequality) (p : ℚ × ℚ) : Prop :=
  q.a * p.1 + q.b * p.2 < q.c

/-- Satisfaction of a one-variable strict inequality. -/
def StrictInequality1.Satisfies (q : StrictInequality1) (x : ℚ) : Prop :=
  q.a * x < q.c

/-- Satisfaction of a finite two-variable system. -/
def SatisfiesAll (qs : List StrictInequality) (p : ℚ × ℚ) : Prop :=
  ∀ q ∈ qs, q.Satisfies p

/-- Satisfaction of a finite one-variable system. -/
def SatisfiesAll1 (qs : List StrictInequality1) (x : ℚ) : Prop :=
  ∀ q ∈ qs, q.Satisfies x

/-- The upper bound contributed by a positive-coefficient one-variable inequality. -/
def upperBound? (q : StrictInequality1) : Option ℚ :=
  if 0 < q.a then some (q.c / q.a) else none

/-- The lower bound contributed by a negative-coefficient one-variable inequality. -/
def lowerBound? (q : StrictInequality1) : Option ℚ :=
  if q.a < 0 then some (q.c / q.a) else none

/-- Whether the constant inequality arising from a zero coefficient is valid. -/
def constantValid (q : StrictInequality1) : Bool :=
  decide (q.a ≠ 0 ∨ 0 < q.c)

/-- All strict lower bounds in a one-variable system. -/
def lowerBounds (qs : List StrictInequality1) : List ℚ :=
  qs.filterMap lowerBound?

/-- All strict upper bounds in a one-variable system. -/
def upperBounds (qs : List StrictInequality1) : List ℚ :=
  qs.filterMap upperBound?

/-- Construct a rational strictly between all given lower and upper bounds, when possible. -/
def chooseBetween (ls us : List ℚ) : Option ℚ :=
  match ls.max?, us.min? with
  | none, none => some 0
  | some l, none => some (l + 1)
  | none, some u => some (u - 1)
  | some l, some u => if l < u then some ((l + u) / 2) else none

/-- Solve a finite system of strict one-variable rational inequalities. -/
def solve1D (qs : List StrictInequality1) : Option ℚ :=
  if qs.all constantValid then chooseBetween (lowerBounds qs) (upperBounds qs) else none

private theorem satisfies1_of_pos {q : StrictInequality1} (ha : 0 < q.a) (x : ℚ) :
    q.Satisfies x ↔ x < q.c / q.a := by
  simpa [StrictInequality1.Satisfies, mul_comm] using (lt_div_iff₀ ha).symm

private theorem satisfies1_of_neg {q : StrictInequality1} (ha : q.a < 0) (x : ℚ) :
    q.Satisfies x ↔ q.c / q.a < x := by
  constructor
  · intro h
    rw [show q.c / q.a = (-q.c) / (-q.a) by ring,
      div_lt_iff₀ (neg_pos.mpr ha)]
    simp only [StrictInequality1.Satisfies] at h
    ring_nf at h ⊢
    linarith
  · intro h
    rw [show q.c / q.a = (-q.c) / (-q.a) by ring,
      div_lt_iff₀ (neg_pos.mpr ha)] at h
    simp only [StrictInequality1.Satisfies]
    ring_nf at h ⊢
    linarith

private theorem satisfies1_of_eq_zero {q : StrictInequality1} (ha : q.a = 0) (x : ℚ) :
    q.Satisfies x ↔ 0 < q.c := by
  simp [StrictInequality1.Satisfies, ha]

private theorem mem_lowerBounds_iff {qs : List StrictInequality1} {l : ℚ} :
    l ∈ lowerBounds qs ↔ ∃ q ∈ qs, q.a < 0 ∧ q.c / q.a = l := by
  simp only [lowerBounds, List.mem_filterMap, lowerBound?]
  constructor
  · rintro ⟨q, hq, h⟩
    split at h
    · exact ⟨q, hq, ‹q.a < 0›, Option.some.inj h⟩
    · contradiction
  · rintro ⟨q, hq, ha, rfl⟩
    exact ⟨q, hq, by simp [ha]⟩

private theorem mem_upperBounds_iff {qs : List StrictInequality1} {u : ℚ} :
    u ∈ upperBounds qs ↔ ∃ q ∈ qs, 0 < q.a ∧ q.c / q.a = u := by
  simp only [upperBounds, List.mem_filterMap, upperBound?]
  constructor
  · rintro ⟨q, hq, h⟩
    split at h
    · exact ⟨q, hq, ‹0 < q.a›, Option.some.inj h⟩
    · contradiction
  · rintro ⟨q, hq, ha, rfl⟩
    exact ⟨q, hq, by simp [ha]⟩

private theorem all_constantValid_iff {qs : List StrictInequality1} :
    qs.all constantValid ↔ ∀ q ∈ qs, q.a = 0 → 0 < q.c := by
  simp only [List.all_eq_true, constantValid, decide_eq_true_eq]
  constructor
  · intro h q hq ha
    exact (h q hq).resolve_left (fun hne => hne ha)
  · intro h q hq
    by_cases ha : q.a = 0
    · exact Or.inr (h q hq ha)
    · exact Or.inl ha

private theorem satisfiesAll1_iff_bounds {qs : List StrictInequality1} {x : ℚ} :
    SatisfiesAll1 qs x ↔
      (∀ l ∈ lowerBounds qs, l < x) ∧
      (∀ u ∈ upperBounds qs, x < u) ∧
      qs.all constantValid := by
  constructor
  · intro h
    refine ⟨?_, ?_, all_constantValid_iff.mpr ?_⟩
    · intro l hl
      obtain ⟨q, hq, ha, rfl⟩ := mem_lowerBounds_iff.mp hl
      exact (satisfies1_of_neg ha x).mp (h q hq)
    · intro u hu
      obtain ⟨q, hq, ha, rfl⟩ := mem_upperBounds_iff.mp hu
      exact (satisfies1_of_pos ha x).mp (h q hq)
    · intro q hq ha
      exact (satisfies1_of_eq_zero ha x).mp (h q hq)
  · rintro ⟨hlower, hupper, hconstant⟩ q hq
    rcases lt_trichotomy q.a 0 with ha | ha | ha
    · apply (satisfies1_of_neg ha x).mpr
      apply hlower (q.c / q.a)
      exact mem_lowerBounds_iff.mpr ⟨q, hq, ha, rfl⟩
    · apply (satisfies1_of_eq_zero ha x).mpr
      exact all_constantValid_iff.mp hconstant q hq ha
    · apply (satisfies1_of_pos ha x).mpr
      apply hupper (q.c / q.a)
      exact mem_upperBounds_iff.mpr ⟨q, hq, ha, rfl⟩

private theorem midpoint_gt {l u : ℚ} (h : l < u) : l < (l + u) / 2 := by
  linarith

private theorem midpoint_lt {l u : ℚ} (h : l < u) : (l + u) / 2 < u := by
  linarith

/-- A value returned by `chooseBetween` lies strictly above every lower bound and strictly below
every upper bound. -/
theorem chooseBetween_sound {ls us : List ℚ} {x : ℚ}
    (h : chooseBetween ls us = some x) :
    (∀ l ∈ ls, l < x) ∧ (∀ u ∈ us, x < u) := by
  unfold chooseBetween at h
  cases hmax : ls.max? with
  | none =>
      have hls : ls = [] := List.min?_eq_none_iff.mp (by simpa using hmax)
      cases hmin : us.min? with
      | none =>
          have hus : us = [] := List.min?_eq_none_iff.mp hmin
          simp [hls, hus] at h ⊢
      | some u =>
          have hx : u - 1 = x := by
            simpa only [hmax, hmin, Option.some.injEq] using h
          subst x
          refine ⟨by simp [hls], ?_⟩
          intro v hv
          have huv : u ≤ v := (List.min?_eq_some_iff.mp hmin).2 v hv
          linarith
  | some l =>
      cases hmin : us.min? with
      | none =>
          have hus : us = [] := List.min?_eq_none_iff.mp hmin
          have hx : l + 1 = x := by
            simpa only [hmax, hmin, Option.some.injEq] using h
          subst x
          refine ⟨?_, by simp [hus]⟩
          intro v hv
          have hvl : v ≤ l := (List.max?_eq_some_iff.mp hmax).2 v hv
          linarith
      | some u =>
          by_cases hlu : l < u
          · have hx : (l + u) / 2 = x := by
              simpa only [hmax, hmin, if_pos hlu, Option.some.injEq] using h
            subst x
            refine ⟨?_, ?_⟩
            · intro v hv
              have hvl : v ≤ l := (List.max?_eq_some_iff.mp hmax).2 v hv
              exact lt_of_le_of_lt hvl (midpoint_gt hlu)
            · intro v hv
              have huv : u ≤ v := (List.min?_eq_some_iff.mp hmin).2 v hv
              exact lt_of_lt_of_le (midpoint_lt hlu) huv
          · simp [hmax, hmin, hlu] at h

/-- If one rational already lies between all supplied bounds, `chooseBetween` returns a witness. -/
theorem chooseBetween_complete {ls us : List ℚ} {z : ℚ}
    (hlower : ∀ l ∈ ls, l < z) (hupper : ∀ u ∈ us, z < u) :
    ∃ x, chooseBetween ls us = some x := by
  unfold chooseBetween
  cases hmax : ls.max? with
  | none =>
      cases hmin : us.min? with
      | none => exact ⟨0, rfl⟩
      | some u => exact ⟨u - 1, rfl⟩
  | some l =>
      cases hmin : us.min? with
      | none => exact ⟨l + 1, rfl⟩
      | some u =>
          have hlmem : l ∈ ls := List.max?_mem hmax
          have humem : u ∈ us := List.min?_mem hmin
          have hlu : l < u := lt_trans (hlower l hlmem) (hupper u humem)
          simp [hlu]

/-- Every witness returned by the one-variable solver satisfies the entire input system. -/
theorem solve1D_sound {qs : List StrictInequality1} {x : ℚ}
    (h : solve1D qs = some x) : SatisfiesAll1 qs x := by
  unfold solve1D at h
  split at h
  · obtain ⟨hlower, hupper⟩ := chooseBetween_sound h
    exact satisfiesAll1_iff_bounds.mpr ⟨hlower, hupper, ‹qs.all constantValid›⟩
  · contradiction

/-- Every feasible one-variable system makes `solve1D` return a rational witness. -/
theorem solve1D_complete {qs : List StrictInequality1}
    (h : ∃ x, SatisfiesAll1 qs x) : ∃ x, solve1D qs = some x := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨hlower, hupper, hconstant⟩ := satisfiesAll1_iff_bounds.mp hz
  obtain ⟨x, hx⟩ := chooseBetween_complete hlower hupper
  exact ⟨x, by simp [solve1D, hconstant, hx]⟩

/-- The one-variable solver returns some value exactly when its input system is feasible. -/
theorem solve1D_isSome_iff {qs : List StrictInequality1} :
    (∃ x, solve1D qs = some x) ↔ ∃ x, SatisfiesAll1 qs x :=
  ⟨fun ⟨x, hx⟩ => ⟨x, solve1D_sound hx⟩, solve1D_complete⟩

/-- The sublist whose eliminated coefficient is negative (the lower bounds on `y`). -/
def negativeY (qs : List StrictInequality) : List StrictInequality :=
  qs.filter fun q => decide (q.b < 0)

/-- The sublist whose eliminated coefficient is positive (the upper bounds on `y`). -/
def positiveY (qs : List StrictInequality) : List StrictInequality :=
  qs.filter fun q => decide (0 < q.b)

/-- The sublist independent of the eliminated variable `y`. -/
def zeroY (qs : List StrictInequality) : List StrictInequality :=
  qs.filter fun q => decide (q.b = 0)

/-- The one-variable constraint contributed when the eliminated coefficient is zero. -/
def zeroProjection (q : StrictInequality) : StrictInequality1 :=
  ⟨q.a, q.c⟩

/-- The one-variable constraint obtained from a negative/positive pair by eliminating `y`. -/
def pairProjection (l u : StrictInequality) : StrictInequality1 :=
  ⟨u.b * l.a - l.b * u.a, u.b * l.c - l.b * u.c⟩

/-- Fourier--Motzkin elimination of `y` from a finite strict rational system. -/
def eliminateY (qs : List StrictInequality) : List StrictInequality1 :=
  (zeroY qs).map zeroProjection ++
    (negativeY qs).flatMap fun l => (positiveY qs).map (pairProjection l)

/-- The `y`-bound represented by an inequality at a fixed value of `x`. -/
def verticalBound (q : StrictInequality) (x : ℚ) : ℚ :=
  (q.c - q.a * x) / q.b

/-- Extract a strict lower bound on `y`, when the coefficient of `y` is negative. -/
def yLowerBound? (x : ℚ) (q : StrictInequality) : Option ℚ :=
  if q.b < 0 then some (verticalBound q x) else none

/-- Extract a strict upper bound on `y`, when the coefficient of `y` is positive. -/
def yUpperBound? (x : ℚ) (q : StrictInequality) : Option ℚ :=
  if 0 < q.b then some (verticalBound q x) else none

/-- All lower bounds on `y` at a fixed `x`. -/
def yLowerBounds (qs : List StrictInequality) (x : ℚ) : List ℚ :=
  qs.filterMap (yLowerBound? x)

/-- All upper bounds on `y` at a fixed `x`. -/
def yUpperBounds (qs : List StrictInequality) (x : ℚ) : List ℚ :=
  qs.filterMap (yUpperBound? x)

/-- Construct a `y` witness once Fourier--Motzkin has certified the chosen `x`. -/
def solveY (qs : List StrictInequality) (x : ℚ) : Option ℚ :=
  chooseBetween (yLowerBounds qs x) (yUpperBounds qs x)

/-- Solve a finite system of strict affine inequalities over `ℚ²`. -/
def solve (qs : List StrictInequality) : Option (ℚ × ℚ) :=
  match solve1D (eliminateY qs) with
  | none => none
  | some x => (solveY qs x).map fun y => (x, y)

/-- Executable feasibility decision obtained by forgetting the solver's witness. -/
def isFeasible (qs : List StrictInequality) : Bool :=
  (solve qs).isSome

private theorem satisfies_of_pos {q : StrictInequality} (hb : 0 < q.b) (x y : ℚ) :
    q.Satisfies (x, y) ↔ y < verticalBound q x := by
  rw [verticalBound, lt_div_iff₀ hb]
  simp only [StrictInequality.Satisfies]
  constructor <;> intro h <;> linarith

private theorem satisfies_of_neg {q : StrictInequality} (hb : q.b < 0) (x y : ℚ) :
    q.Satisfies (x, y) ↔ verticalBound q x < y := by
  rw [verticalBound, show (q.c - q.a * x) / q.b =
    (-(q.c - q.a * x)) / (-q.b) by ring, div_lt_iff₀ (neg_pos.mpr hb)]
  simp only [StrictInequality.Satisfies]
  constructor <;> intro h <;> ring_nf at h ⊢ <;> linarith

private theorem satisfies_of_eq_zero {q : StrictInequality} (hb : q.b = 0) (x y : ℚ) :
    q.Satisfies (x, y) ↔ q.a * x < q.c := by
  simp [StrictInequality.Satisfies, hb]

private theorem pairProjection_satisfies {l u : StrictInequality}
    (hl : l.b < 0) (hu : 0 < u.b) (x : ℚ) :
    (pairProjection l u).Satisfies x ↔ verticalBound l x < verticalBound u x := by
  simp only [pairProjection, StrictInequality1.Satisfies, verticalBound]
  rw [show (l.c - l.a * x) / l.b = (-(l.c - l.a * x)) / (-l.b) by ring,
    div_lt_div_iff₀ (neg_pos.mpr hl) hu]
  ring_nf
  constructor <;> intro h <;> linarith

private theorem zeroProjection_satisfies (q : StrictInequality) (x : ℚ) :
    (zeroProjection q).Satisfies x ↔ q.a * x < q.c := by
  rfl

private theorem mem_negativeY_iff {qs : List StrictInequality} {q : StrictInequality} :
    q ∈ negativeY qs ↔ q ∈ qs ∧ q.b < 0 := by
  simp [negativeY]

private theorem mem_positiveY_iff {qs : List StrictInequality} {q : StrictInequality} :
    q ∈ positiveY qs ↔ q ∈ qs ∧ 0 < q.b := by
  simp [positiveY]

private theorem mem_zeroY_iff {qs : List StrictInequality} {q : StrictInequality} :
    q ∈ zeroY qs ↔ q ∈ qs ∧ q.b = 0 := by
  simp [zeroY]

/-- The eliminated system holds at `x` exactly when all `y`-independent constraints hold and
every lower vertical bound lies strictly below every upper vertical bound. -/
theorem eliminateY_spec {qs : List StrictInequality} {x : ℚ} :
    SatisfiesAll1 (eliminateY qs) x ↔
      (∀ q ∈ qs, q.b = 0 → q.a * x < q.c) ∧
      (∀ l ∈ qs, ∀ u ∈ qs, l.b < 0 → 0 < u.b →
        verticalBound l x < verticalBound u x) := by
  simp only [SatisfiesAll1, eliminateY, List.mem_append, List.mem_map,
    List.mem_flatMap]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro q hq hb
      exact (zeroProjection_satisfies q x).mp
        (h (zeroProjection q) (Or.inl ⟨q, mem_zeroY_iff.mpr ⟨hq, hb⟩, rfl⟩))
    · intro l hl u hu hbl hbu
      exact (pairProjection_satisfies hbl hbu x).mp
        (h (pairProjection l u) (Or.inr
          ⟨l, mem_negativeY_iff.mpr ⟨hl, hbl⟩,
            u, mem_positiveY_iff.mpr ⟨hu, hbu⟩, rfl⟩))
  · rintro ⟨hzero, hpairs⟩ q hq
    rcases hq with ⟨r, hr, rfl⟩ | ⟨l, hl, u, hu, rfl⟩
    · obtain ⟨hr, hbr⟩ := mem_zeroY_iff.mp hr
      exact (zeroProjection_satisfies r x).mpr (hzero r hr hbr)
    · obtain ⟨hl, hbl⟩ := mem_negativeY_iff.mp hl
      obtain ⟨hu, hbu⟩ := mem_positiveY_iff.mp hu
      exact (pairProjection_satisfies hbl hbu x).mpr (hpairs l hl u hu hbl hbu)

private theorem mem_yLowerBounds_iff {qs : List StrictInequality} {x l : ℚ} :
    l ∈ yLowerBounds qs x ↔
      ∃ q ∈ qs, q.b < 0 ∧ verticalBound q x = l := by
  simp only [yLowerBounds, List.mem_filterMap, yLowerBound?]
  constructor
  · rintro ⟨q, hq, h⟩
    split at h
    · exact ⟨q, hq, ‹q.b < 0›, Option.some.inj h⟩
    · contradiction
  · rintro ⟨q, hq, hb, rfl⟩
    exact ⟨q, hq, by simp [hb]⟩

private theorem mem_yUpperBounds_iff {qs : List StrictInequality} {x u : ℚ} :
    u ∈ yUpperBounds qs x ↔
      ∃ q ∈ qs, 0 < q.b ∧ verticalBound q x = u := by
  simp only [yUpperBounds, List.mem_filterMap, yUpperBound?]
  constructor
  · rintro ⟨q, hq, h⟩
    split at h
    · exact ⟨q, hq, ‹0 < q.b›, Option.some.inj h⟩
    · contradiction
  · rintro ⟨q, hq, hb, rfl⟩
    exact ⟨q, hq, by simp [hb]⟩

private theorem chooseBetween_complete_of_pairwise {ls us : List ℚ}
    (hpair : ∀ l ∈ ls, ∀ u ∈ us, l < u) :
    ∃ x, chooseBetween ls us = some x := by
  unfold chooseBetween
  cases hmax : ls.max? with
  | none =>
      cases hmin : us.min? with
      | none => exact ⟨0, rfl⟩
      | some u => exact ⟨u - 1, rfl⟩
  | some l =>
      cases hmin : us.min? with
      | none => exact ⟨l + 1, rfl⟩
      | some u =>
          have hlu := hpair l (List.max?_mem hmax) u (List.min?_mem hmin)
          simp [hlu]

private theorem eliminateY_of_satisfiesAll {qs : List StrictInequality} {x y : ℚ}
    (h : SatisfiesAll qs (x, y)) : SatisfiesAll1 (eliminateY qs) x := by
  apply eliminateY_spec.mpr
  refine ⟨?_, ?_⟩
  · intro q hq hb
    exact (satisfies_of_eq_zero hb x y).mp (h q hq)
  · intro l hl u hu hbl hbu
    exact lt_trans ((satisfies_of_neg hbl x y).mp (h l hl))
      ((satisfies_of_pos hbu x y).mp (h u hu))

/-- If `x` satisfies the eliminated system, every value returned by `solveY` completes it to a
witness of the original two-variable system. -/
theorem solveY_sound {qs : List StrictInequality} {x y : ℚ}
    (hx : SatisfiesAll1 (eliminateY qs) x) (hy : solveY qs x = some y) :
    SatisfiesAll qs (x, y) := by
  obtain ⟨hlower, hupper⟩ := chooseBetween_sound hy
  obtain ⟨hzero, _hpairs⟩ := eliminateY_spec.mp hx
  intro q hq
  rcases lt_trichotomy q.b 0 with hb | hb | hb
  · apply (satisfies_of_neg hb x y).mpr
    apply hlower (verticalBound q x)
    exact mem_yLowerBounds_iff.mpr ⟨q, hq, hb, rfl⟩
  · exact (satisfies_of_eq_zero hb x y).mpr (hzero q hq hb)
  · apply (satisfies_of_pos hb x y).mpr
    apply hupper (verticalBound q x)
    exact mem_yUpperBounds_iff.mpr ⟨q, hq, hb, rfl⟩

/-- For every `x` satisfying the eliminated system, `solveY` returns a value. -/
theorem solveY_complete {qs : List StrictInequality} {x : ℚ}
    (hx : SatisfiesAll1 (eliminateY qs) x) : ∃ y, solveY qs x = some y := by
  obtain ⟨_hzero, hpairs⟩ := eliminateY_spec.mp hx
  apply chooseBetween_complete_of_pairwise
  intro l hl u hu
  obtain ⟨ql, hql, hbl, rfl⟩ := mem_yLowerBounds_iff.mp hl
  obtain ⟨qu, hqu, hbu, rfl⟩ := mem_yUpperBounds_iff.mp hu
  exact hpairs ql hql qu hqu hbl hbu

/-- Fourier--Motzkin elimination is exact: the eliminated constraints hold at `x` if and only if
some rational `y` completes `x` to a solution of the original system. -/
theorem exists_y_satisfiesAll_iff_eliminateY {qs : List StrictInequality} {x : ℚ} :
    (∃ y, SatisfiesAll qs (x, y)) ↔ SatisfiesAll1 (eliminateY qs) x := by
  constructor
  · exact fun ⟨y, hy⟩ => eliminateY_of_satisfiesAll hy
  · intro hx
    obtain ⟨y, hy⟩ := solveY_complete hx
    exact ⟨y, solveY_sound hx hy⟩

/-- Every pair returned by the two-variable solver satisfies every input inequality. -/
theorem solve_sound {qs : List StrictInequality} {p : ℚ × ℚ}
    (h : solve qs = some p) : SatisfiesAll qs p := by
  unfold solve at h
  cases hx : solve1D (eliminateY qs) with
  | none =>
      simp only [hx] at h
      contradiction
  | some x =>
      cases hy : solveY qs x with
      | none =>
          simp only [hx, hy, Option.map_none] at h
          contradiction
      | some y =>
          have hp : (x, y) = p := by
            simpa only [hx, hy, Option.map_some, Option.some.injEq] using h
          subst p
          exact solveY_sound (solve1D_sound hx) hy

/-- Every feasible two-variable system makes `solve` return a rational witness pair. -/
theorem solve_complete {qs : List StrictInequality}
    (h : ∃ p, SatisfiesAll qs p) : ∃ p, solve qs = some p := by
  obtain ⟨⟨x, y⟩, hxy⟩ := h
  have hx : SatisfiesAll1 (eliminateY qs) x := eliminateY_of_satisfiesAll hxy
  obtain ⟨x', hx'⟩ := solve1D_complete ⟨x, hx⟩
  have hx'sat : SatisfiesAll1 (eliminateY qs) x' := solve1D_sound hx'
  obtain ⟨y', hy'⟩ := solveY_complete hx'sat
  exact ⟨(x', y'), by simp [solve, hx', hy']⟩

/-- The verified solver returns a witness exactly when the strict system is feasible. -/
theorem solve_isSome_iff {qs : List StrictInequality} :
    (∃ p, solve qs = some p) ↔ ∃ p, SatisfiesAll qs p :=
  ⟨fun ⟨p, hp⟩ => ⟨p, solve_sound hp⟩, solve_complete⟩

/-- Boolean feasibility is true exactly for systems having a rational witness. -/
theorem isFeasible_eq_true_iff {qs : List StrictInequality} :
    isFeasible qs = true ↔ ∃ p, SatisfiesAll qs p := by
  rw [isFeasible, Option.isSome_iff_exists, solve_isSome_iff]

/-- Failure of the witness solver is equivalent to infeasibility. -/
theorem solve_eq_none_iff {qs : List StrictInequality} :
    solve qs = none ↔ ¬∃ p, SatisfiesAll qs p := by
  constructor
  · intro hnone hfeasible
    obtain ⟨p, hp⟩ := solve_complete hfeasible
    rw [hnone] at hp
    contradiction
  · intro hfeasible
    cases hsolve : solve qs with
    | none => rfl
    | some p => exact False.elim (hfeasible ⟨p, solve_sound hsolve⟩)

end Tiling.RationalPolygonal.LinearFeasibility
