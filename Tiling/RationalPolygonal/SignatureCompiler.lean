import Tiling.RationalPolygonal.ComputableMarker
import Tiling.RationalPolygonal.LinearFeasibility
import Tiling.RationalPolygonal.RawInput

set_option linter.style.header false

/-!
# Executable signature compiler for rational polygonal regions

This module contains the computable core of the raw rational-polygon compiler.  It normalizes
the input triangles, enumerates a finite window of integer translates, constructs the translated
edge-line arrangement, and incrementally retains only feasible strict sign cells.  Feasibility is
decided by the verified rational Fourier--Motzkin solver in `LinearFeasibility`.

Each surviving cell supplies a rational sample point.  Exact rational orientation tests turn
these samples into a deduplicated family of finite lattice signatures.  When that family contains
a nonempty signature, `compileRaster?` orders one such signature first and invokes the production
executable planar-marker API.

This file deliberately makes no semantic completeness claim about `relevantSignatures` yet.  In
particular, the finite-window and convex-hull bridges are kept separate from this verified
executable milestone.
-/

namespace Tiling.RationalPolygonal.Raw.Compiler

open Function MeasureTheory Set
open LinearFeasibility
open scoped Pointwise

/-- The normalized integer triangles obtained from a valid raw input. -/
def normalizedTriangles (P : Code.Input) : List ZTriangle :=
  P.code.triangles.map P.normalizedTriangle

/-- The executable closed interval of integers from `lo` through `hi`. -/
def intRange (lo hi : ℤ) : List ℤ :=
  if lo ≤ hi then
    (List.range (hi - lo + 1).toNat).map fun n : ℕ ↦ lo + (n : ℤ)
  else []

/-- Membership in the executable integer interval is equivalent to the endpoint inequalities. -/
@[simp]
theorem mem_intRange_iff {lo hi z : ℤ} :
    z ∈ intRange lo hi ↔ lo ≤ z ∧ z ≤ hi := by
  simp only [intRange]
  split
  · rename_i hlohi
    rw [List.mem_map]
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hn' := List.mem_range.mp hn
      constructor
      · exact le_add_of_nonneg_right (Int.natCast_nonneg n)
      · have hcast : (n : ℤ) < hi - lo + 1 := by
          rw [← Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo + 1)]
          exact_mod_cast hn'
        omega
    · rintro ⟨hloz, hzhi⟩
      let n := (z - lo).toNat
      refine ⟨n, ?_, ?_⟩
      · have hncast : (n : ℤ) = z - lo := Int.toNat_of_nonneg (by omega)
        have hbound : (n : ℤ) < hi - lo + 1 := by omega
        rw [← Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo + 1)] at hbound
        exact List.mem_range.mpr (by exact_mod_cast hbound)
      · have hncast : (n : ℤ) = z - lo := Int.toNat_of_nonneg (by omega)
        omega
  · rename_i hnot
    simp only [List.not_mem_nil, false_iff]
    omega

/-- The horizontal vertex coordinates in a list of normalized triangles. -/
def xCoordinates (ts : List ZTriangle) : List ℤ :=
  ts.flatMap fun t ↦ [t.a.x, t.b.x, t.c.x]

/-- The vertical vertex coordinates in a list of normalized triangles. -/
def yCoordinates (ts : List ZTriangle) : List ℤ :=
  ts.flatMap fun t ↦ [t.a.y, t.b.y, t.c.y]

/-- The minimum of a finite integer list, with zero included as a default bound. -/
def minCoord (xs : List ℤ) : ℤ :=
  xs.foldl min 0

/-- The maximum of a finite integer list, with zero included as a default bound. -/
def maxCoord (xs : List ℤ) : ℤ :=
  xs.foldl max 0

/-- A padded finite lattice window used for translated-edge and signature enumeration. -/
def offsetWindow (ts : List ZTriangle) : List ZPoint :=
  (intRange (minCoord (xCoordinates ts) - 1) (maxCoord (xCoordinates ts))).flatMap fun x ↦
    (intRange (minCoord (yCoordinates ts) - 1) (maxCoord (yCoordinates ts))).map fun y ↦
      ⟨x, y⟩

/-- An integral affine line represented by the equation `A * x + B * y + C = 0`. -/
structure ZLine where
  /-- Horizontal coefficient. -/
  A : ℤ
  /-- Vertical coefficient. -/
  B : ℤ
  /-- Constant coefficient. -/
  C : ℤ
deriving DecidableEq, Repr

/-- Evaluate an integral affine line at a rational point. -/
def ZLine.eval (l : ZLine) (p : ℚ × ℚ) : ℚ :=
  l.A * p.1 + l.B * p.2 + l.C

/-- The line through `p - z` and `q - z`. -/
def edgeLine (z p q : ZPoint) : ZLine :=
  let A := q.y - p.y
  let B := p.x - q.x
  let px := p.x - z.x
  let py := p.y - z.y
  ⟨A, B, -(A * px + B * py)⟩

/-- The first translated endpoint lies on its translated edge line. -/
@[simp]
theorem edgeLine_eval_left (z p q : ZPoint) :
    (edgeLine z p q).eval (p.x - z.x, p.y - z.y) = 0 := by
  simp [edgeLine, ZLine.eval]

/-- The second translated endpoint lies on its translated edge line. -/
@[simp]
theorem edgeLine_eval_right (z p q : ZPoint) :
    (edgeLine z p q).eval (q.x - z.x, q.y - z.y) = 0 := by
  simp [edgeLine, ZLine.eval]
  ring

/-- The three translated edge lines of an integer triangle. -/
def translatedEdgeLines (t : ZTriangle) (z : ZPoint) : List ZLine :=
  [edgeLine z t.a t.b, edgeLine z t.b t.c, edgeLine z t.c t.a]

/-- All translated triangle-edge lines considered by the executable compiler. -/
def arrangementLines (ts : List ZTriangle) : List ZLine :=
  (offsetWindow ts).flatMap fun z ↦ ts.flatMap fun t ↦ translatedEdgeLines t z

/-- Every listed edge of a listed translated triangle occurs in the full arrangement. -/
theorem mem_arrangementLines_of_mem {ts : List ZTriangle} {z : ZPoint} {t : ZTriangle}
    {l : ZLine} (hz : z ∈ offsetWindow ts) (ht : t ∈ ts)
    (hl : l ∈ translatedEdgeLines t z) : l ∈ arrangementLines ts := by
  simp only [arrangementLines, List.mem_flatMap]
  exact ⟨z, hz, t, ht, hl⟩

/-- The strict rational inequality selecting one of the two sides of an affine line. -/
def sideConstraint (positive : Bool) (l : ZLine) : StrictInequality :=
  if positive then ⟨-l.A, -l.B, l.C⟩ else ⟨l.A, l.B, -l.C⟩

/-- The positive-side constraint is satisfied exactly where the line evaluates positively. -/
theorem sideConstraint_true_satisfies_iff (l : ZLine) (p : ℚ × ℚ) :
    (sideConstraint true l).Satisfies p ↔ 0 < l.eval p := by
  simp only [sideConstraint, if_true, StrictInequality.Satisfies, ZLine.eval]
  constructor <;> intro h <;> linarith

/-- The negative-side constraint is satisfied exactly where the line evaluates negatively. -/
theorem sideConstraint_false_satisfies_iff (l : ZLine) (p : ℚ × ℚ) :
    (sideConstraint false l).Satisfies p ↔ l.eval p < 0 := by
  simp only [sideConstraint, Bool.false_eq_true, if_false, StrictInequality.Satisfies,
    ZLine.eval]
  constructor <;> intro h <;> linarith

/-- The strict inequalities defining the open unit square. -/
def openUnitSquare : List StrictInequality :=
  [⟨-1, 0, 0⟩, ⟨1, 0, 1⟩, ⟨0, -1, 0⟩, ⟨0, 1, 1⟩]

/-- A feasible strict sign cell together with the solver-produced rational sample point. -/
structure SignCell where
  /-- The accumulated strict inequalities defining the cell. -/
  system : List StrictInequality
  /-- A rational point returned by the verified feasibility solver. -/
  sample : ℚ × ℚ
deriving Repr

/-- Run the verified solver and package its witness as a sign cell. -/
def cellOfSystem? (qs : List StrictInequality) : Option SignCell :=
  (solve qs).map fun p ↦ ⟨qs, p⟩

/-- A packaged cell contains the requested system and its sample satisfies that system. -/
theorem cellOfSystem_sound {qs : List StrictInequality} {cell : SignCell}
    (h : cellOfSystem? qs = some cell) :
    cell.system = qs ∧ SatisfiesAll qs cell.sample := by
  simp only [cellOfSystem?] at h
  cases hs : solve qs with
  | none =>
      rw [hs] at h
      cases h
  | some p =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst cell
      exact ⟨rfl, solve_sound hs⟩

/-- Split a feasible cell along a line and discard either infeasible open half-cell. -/
def refineCell (l : ZLine) (cell : SignCell) : List SignCell :=
  [cellOfSystem? (sideConstraint false l :: cell.system),
    cellOfSystem? (sideConstraint true l :: cell.system)].filterMap id

private theorem cellOfSystem_eq_some_of_solve {qs : List StrictInequality}
    {sample : ℚ × ℚ} (hsample : solve qs = some sample) :
    cellOfSystem? qs = some ⟨qs, sample⟩ := by
  rw [cellOfSystem?, hsample]
  rfl

/-- A boundary-avoiding point in a cell survives in one of the two feasible refinements. -/
theorem refineCell_complete {l : ZLine} {cell : SignCell} {p : ℚ × ℚ}
    (hp : SatisfiesAll cell.system p) (hoff : l.eval p ≠ 0) :
    ∃ child ∈ refineCell l cell, SatisfiesAll child.system p := by
  by_cases hpos : 0 < l.eval p
  · let qs := sideConstraint true l :: cell.system
    have hpqs : SatisfiesAll qs p := by
      intro q hq
      have hmem : q = sideConstraint true l ∨ q ∈ cell.system := by
        simpa only [qs, List.mem_cons] using hq
      rcases hmem with hq | hq
      · subst q
        exact (sideConstraint_true_satisfies_iff l p).mpr hpos
      · exact hp q hq
    obtain ⟨sample, hsample⟩ := solve_complete ⟨p, hpqs⟩
    let child : SignCell := ⟨qs, sample⟩
    have hcell : cellOfSystem? qs = some child :=
      cellOfSystem_eq_some_of_solve hsample
    refine ⟨child, ?_, hpqs⟩
    rw [refineCell, List.mem_filterMap]
    refine ⟨some child, ?_, rfl⟩
    simp only [List.mem_cons]
    exact Or.inr (Or.inl hcell.symm)
  · have hneg : l.eval p < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hoff
    let qs := sideConstraint false l :: cell.system
    have hpqs : SatisfiesAll qs p := by
      intro q hq
      have hmem : q = sideConstraint false l ∨ q ∈ cell.system := by
        simpa only [qs, List.mem_cons] using hq
      rcases hmem with hq | hq
      · subst q
        exact (sideConstraint_false_satisfies_iff l p).mpr hneg
      · exact hp q hq
    obtain ⟨sample, hsample⟩ := solve_complete ⟨p, hpqs⟩
    let child : SignCell := ⟨qs, sample⟩
    have hcell : cellOfSystem? qs = some child :=
      cellOfSystem_eq_some_of_solve hsample
    refine ⟨child, ?_, hpqs⟩
    rw [refineCell, List.mem_filterMap]
    refine ⟨some child, ?_, rfl⟩
    simp only [List.mem_cons]
    exact Or.inl hcell.symm

/-- Refine every currently feasible cell along one affine line. -/
def refineCells (l : ZLine) (cells : List SignCell) : List SignCell :=
  cells.flatMap (refineCell l)

/-- A boundary-avoiding point represented before a line split is represented after it. -/
theorem refineCells_complete {l : ZLine} {cells : List SignCell} {p : ℚ × ℚ}
    (hp : ∃ cell ∈ cells, SatisfiesAll cell.system p) (hoff : l.eval p ≠ 0) :
    ∃ child ∈ refineCells l cells, SatisfiesAll child.system p := by
  obtain ⟨cell, hcell, hsat⟩ := hp
  obtain ⟨child, hchild, hchildSat⟩ := refineCell_complete hsat hoff
  refine ⟨child, ?_, hchildSat⟩
  simp only [refineCells, List.mem_flatMap]
  exact ⟨cell, hcell, hchild⟩

/-- Incrementally refine a list of cells along a list of arrangement lines. -/
def refineLines (cells : List SignCell) (ls : List ZLine) : List SignCell :=
  ls.foldl (fun cs l ↦ refineCells l cs) cells

/-- Refinement along a finite list preserves every point avoiding every processed line. -/
theorem refineLines_complete {cells : List SignCell} {ls : List ZLine} {p : ℚ × ℚ}
    (hp : ∃ cell ∈ cells, SatisfiesAll cell.system p)
    (hoff : ∀ l ∈ ls, l.eval p ≠ 0) :
    ∃ child ∈ refineLines cells ls, SatisfiesAll child.system p := by
  induction ls generalizing cells with
  | nil =>
      simpa only [refineLines, List.foldl_nil] using hp
  | cons l ls ih =>
      rw [refineLines, List.foldl_cons]
      apply ih
      · exact refineCells_complete hp (hoff l (by simp))
      · intro l' hl'
        exact hoff l' (by simp only [List.mem_cons]; exact Or.inr hl')

/-- Enumerate all feasible strict sign cells of the arrangement inside the open unit square. -/
def feasibleSignCells (ls : List ZLine) : List SignCell :=
  match cellOfSystem? openUnitSquare with
  | none => []
  | some base => refineLines [base] ls

/-- Every unit-square point avoiding the arrangement occurs in one enumerated sign cell. -/
theorem feasibleSignCells_complete {ls : List ZLine} {p : ℚ × ℚ}
    (hunit : SatisfiesAll openUnitSquare p) (hoff : ∀ l ∈ ls, l.eval p ≠ 0) :
    ∃ cell ∈ feasibleSignCells ls, SatisfiesAll cell.system p := by
  obtain ⟨sample, hsample⟩ := solve_complete ⟨p, hunit⟩
  let base : SignCell := ⟨openUnitSquare, sample⟩
  have hbase : cellOfSystem? openUnitSquare = some base :=
    cellOfSystem_eq_some_of_solve hsample
  rw [feasibleSignCells, hbase]
  apply refineLines_complete
  · exact ⟨base, by simp, hunit⟩
  · exact hoff

/-- Every cell returned by one refinement contains a solver-valid sample. -/
theorem mem_refineCell_valid {l : ZLine} {cell child : SignCell}
    (hchild : child ∈ refineCell l cell) : SatisfiesAll child.system child.sample := by
  rw [refineCell, List.mem_filterMap] at hchild
  obtain ⟨o, ho, hid⟩ := hchild
  have ho' : o = cellOfSystem? (sideConstraint false l :: cell.system) ∨
      o = cellOfSystem? (sideConstraint true l :: cell.system) := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using ho
  change o = some child at hid
  rcases ho' with ho' | ho'
  · rw [ho'] at hid
    have hs := cellOfSystem_sound hid
    rw [hs.1]
    exact hs.2
  · rw [ho'] at hid
    have hs := cellOfSystem_sound hid
    rw [hs.1]
    exact hs.2

/-- Every cell returned by a bulk refinement contains a solver-valid sample. -/
theorem mem_refineCells_valid {l : ZLine} {cells : List SignCell} {child : SignCell}
    (hchild : child ∈ refineCells l cells) : SatisfiesAll child.system child.sample := by
  simp only [refineCells, List.mem_flatMap] at hchild
  obtain ⟨cell, _, hc⟩ := hchild
  exact mem_refineCell_valid hc

/-- Refinement preserves sample validity when it starts from valid cells. -/
theorem mem_refineLines_valid {cells : List SignCell} {ls : List ZLine} {child : SignCell}
    (hvalid : ∀ cell ∈ cells, SatisfiesAll cell.system cell.sample)
    (hchild : child ∈ refineLines cells ls) : SatisfiesAll child.system child.sample := by
  induction ls generalizing cells with
  | nil =>
      simp only [refineLines, List.foldl_nil] at hchild
      exact hvalid child hchild
  | cons l ls ih =>
      rw [refineLines, List.foldl_cons] at hchild
      exact ih (fun cell hcell ↦ mem_refineCells_valid hcell) hchild

/-- Every enumerated sign cell contains a sample satisfying its accumulated system. -/
theorem feasibleSignCells_sound {ls : List ZLine} {cell : SignCell}
    (hcell : cell ∈ feasibleSignCells ls) : SatisfiesAll cell.system cell.sample := by
  unfold feasibleSignCells at hcell
  cases hbase : cellOfSystem? openUnitSquare with
  | none => simp [hbase] at hcell
  | some base =>
      rw [hbase] at hcell
      apply mem_refineLines_valid (child := cell) _ hcell
      intro c hc
      have hc' : c = base := by simpa using hc
      subst c
      have hs := cellOfSystem_sound hbase
      rw [hs.1]
      exact hs.2

/-- A strict system covers a list of lines when it contains a side constraint for every line. -/
def Covers (ls : List ZLine) (qs : List StrictInequality) : Prop :=
  ∀ l ∈ ls, sideConstraint false l ∈ qs ∨ sideConstraint true l ∈ qs

/-- A child produced by one refinement has the corresponding side constraint at the head of its
system. -/
theorem mem_refineCell_system {l : ZLine} {cell child : SignCell}
    (hchild : child ∈ refineCell l cell) :
    child.system = sideConstraint false l :: cell.system ∨
      child.system = sideConstraint true l :: cell.system := by
  rw [refineCell, List.mem_filterMap] at hchild
  obtain ⟨o, ho, hid⟩ := hchild
  have ho' : o = cellOfSystem? (sideConstraint false l :: cell.system) ∨
      o = cellOfSystem? (sideConstraint true l :: cell.system) := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using ho
  change o = some child at hid
  rcases ho' with ho' | ho'
  · rw [ho'] at hid
    exact Or.inl (cellOfSystem_sound hid).1
  · rw [ho'] at hid
    exact Or.inr (cellOfSystem_sound hid).1

/-- One refinement extends line coverage by the newly processed line. -/
theorem mem_refineCell_covers {covered : List ZLine} {l : ZLine}
    {cell child : SignCell} (hcovered : Covers covered cell.system)
    (hchild : child ∈ refineCell l cell) : Covers (l :: covered) child.system := by
  rcases mem_refineCell_system hchild with hsys | hsys
  · rw [hsys]
    intro k hk
    have hk' : k = l ∨ k ∈ covered := by simpa only [List.mem_cons] using hk
    rcases hk' with rfl | hk
    · exact Or.inl (by simp)
    · rcases hcovered k hk with h | h
      · exact Or.inl (by simp only [List.mem_cons]; exact Or.inr h)
      · exact Or.inr (by simp only [List.mem_cons]; exact Or.inr h)
  · rw [hsys]
    intro k hk
    have hk' : k = l ∨ k ∈ covered := by simpa only [List.mem_cons] using hk
    rcases hk' with rfl | hk
    · exact Or.inr (by simp)
    · rcases hcovered k hk with h | h
      · exact Or.inl (by simp only [List.mem_cons]; exact Or.inr h)
      · exact Or.inr (by simp only [List.mem_cons]; exact Or.inr h)

/-- Bulk refinement extends line coverage by the newly processed line. -/
theorem mem_refineCells_covers {covered : List ZLine} {l : ZLine}
    {cells : List SignCell} {child : SignCell}
    (hcovered : ∀ cell ∈ cells, Covers covered cell.system)
    (hchild : child ∈ refineCells l cells) : Covers (l :: covered) child.system := by
  simp only [refineCells, List.mem_flatMap] at hchild
  obtain ⟨cell, hcell, hc⟩ := hchild
  exact mem_refineCell_covers (hcovered cell hcell) hc

/-- A final cell covers every line processed by `refineLines`, in reverse processing order. -/
theorem mem_refineLines_covers {covered : List ZLine} {cells : List SignCell}
    {ls : List ZLine} {child : SignCell}
    (hcovered : ∀ cell ∈ cells, Covers covered cell.system)
    (hchild : child ∈ refineLines cells ls) :
    Covers (ls.reverse ++ covered) child.system := by
  induction ls generalizing covered cells with
  | nil =>
      simp only [refineLines, List.foldl_nil] at hchild
      simpa using hcovered child hchild
  | cons l ls ih =>
      rw [refineLines, List.foldl_cons] at hchild
      have h := ih (covered := l :: covered)
        (fun cell hcell ↦ mem_refineCells_covers hcovered hcell) hchild
      simpa [List.reverse_cons, List.append_assoc] using h

/-- Every final feasible sign cell contains a positive- or negative-side constraint for each
processed arrangement line. -/
theorem feasibleSignCells_covers {ls : List ZLine} {cell : SignCell}
    (hcell : cell ∈ feasibleSignCells ls) : Covers ls cell.system := by
  unfold feasibleSignCells at hcell
  cases hbase : cellOfSystem? openUnitSquare with
  | none => simp [hbase] at hcell
  | some base =>
      rw [hbase] at hcell
      have h := mem_refineLines_covers (covered := [])
        (fun _ _ ↦ by intro l hl; simp at hl) hcell
      intro l hl
      apply h l
      simpa using hl

/-- Add an integral lattice offset to a rational point. -/
def addOffset (p : ℚ × ℚ) (z : ZPoint) : ℚ × ℚ :=
  (p.1 + z.x, p.2 + z.y)

/-- Twice the signed rational area of the triangle with vertices `a`, `b`, and `p`. -/
def twiceAreaQ (a b p : ℚ × ℚ) : ℚ :=
  (b.1 - a.1) * (p.2 - a.2) - (b.2 - a.2) * (p.1 - a.1)

/-- Regard an integral point as a rational coordinate pair. -/
def zpointQ (p : ZPoint) : ℚ × ℚ :=
  (p.x, p.y)

/-- Exact closed-triangle membership by the three rational orientation signs. -/
def pointInTriangle (p : ℚ × ℚ) (t : ZTriangle) : Bool :=
  let s₀ := twiceAreaQ (zpointQ t.a) (zpointQ t.b) p
  let s₁ := twiceAreaQ (zpointQ t.b) (zpointQ t.c) p
  let s₂ := twiceAreaQ (zpointQ t.c) (zpointQ t.a) p
  decide ((0 ≤ s₀ ∧ 0 ≤ s₁ ∧ 0 ≤ s₂) ∨
    (s₀ ≤ 0 ∧ s₁ ≤ 0 ∧ s₂ ≤ 0))

/-- Exact membership in the finite union of normalized integer triangles. -/
def pointInRegion (ts : List ZTriangle) (p : ℚ × ℚ) : Bool :=
  ts.any fun t ↦ pointInTriangle p t

/-- The finite lattice signature of one rational arrangement sample. -/
def sampleSignature (ts : List ZTriangle) (zs : List ZPoint) (p : ℚ × ℚ) :
    Finset IntegerPlane :=
  ((zs.filter fun z ↦ pointInRegion ts (addOffset p z)).map ZPoint.toIntegerPlane).toFinset

/-- The deduplicated signatures represented by all feasible strict arrangement cells. -/
def signatureFamily (ts : List ZTriangle) : List (Finset IntegerPlane) :=
  let zs := offsetWindow ts
  ((feasibleSignCells (arrangementLines ts)).map fun cell ↦
    sampleSignature ts zs cell.sample).eraseDups

/-- Find the first nonempty finite lattice signature in a list. -/
def firstNonempty : List (Finset IntegerPlane) → Option (Finset IntegerPlane)
  | [] => none
  | F :: Fs => if F = ∅ then firstNonempty Fs else some F

/-- A signature returned by `firstNonempty` is nonempty. -/
theorem firstNonempty_nonempty {family : List (Finset IntegerPlane)}
    {F : Finset IntegerPlane} (h : firstNonempty family = some F) : F.Nonempty := by
  induction family with
  | nil => simp [firstNonempty] at h
  | cons G family ih =>
      simp only [firstNonempty] at h
      split at h
      · exact ih h
      · rename_i hG
        simp only [Option.some.injEq] at h
        subst F
        exact Finset.nonempty_iff_ne_empty.mpr hG

/-- Move the first nonempty signature to the front, when one exists. -/
def nonemptyFirst (family : List (Finset IntegerPlane)) : List (Finset IntegerPlane) :=
  match firstNonempty family with
  | none => family
  | some F => F :: family.erase F

/-- Package a signature family for the executable marker when it contains a nonempty member. -/
def nonemptyRasterFamily? (family : List (Finset IntegerPlane)) :
    Option NonemptyPlanarRasterFamily :=
  match h : firstNonempty family with
  | none => none
  | some F =>
      some {
        tiles := (F :: family.erase F).toArray
        size_pos := by simp
        first_nonempty := by simpa using firstNonempty_nonempty h
      }

/-- Compile normalized integer triangles to a marker raster whenever a nonempty signature exists. -/
def rasterTileFromTriangles? (ts : List ZTriangle) : Option (Finset IntegerPlane) :=
  (nonemptyRasterFamily? (signatureFamily ts)).map planarRasterTileExec

/-- Compile a valid raw rational triangulation to a marker raster when the executable family is
nonempty.  Totality and semantic correctness are intentionally deferred to the geometric bridge. -/
def compileRaster? (P : Code.Input) : Option (Finset IntegerPlane) :=
  rasterTileFromTriangles? (normalizedTriangles P)

/-! ## Exact triangle-membership bridge -/

/-- Regard a rational coordinate pair as a point of the real plane. -/
def sampleToPlane (p : ℚ × ℚ) : Plane :=
  (p.1 : ℝ) + (p.2 : ℝ) * Complex.I

/-- The real part of an embedded rational sample is its first coordinate. -/
@[simp]
theorem sampleToPlane_re (p : ℚ × ℚ) : (sampleToPlane p).re = p.1 := by
  simp [sampleToPlane]

/-- The imaginary part of an embedded rational sample is its second coordinate. -/
@[simp]
theorem sampleToPlane_im (p : ℚ × ℚ) : (sampleToPlane p).im = p.2 := by
  simp [sampleToPlane]

/-- Embedding commutes with addition of an integral lattice offset. -/
theorem sampleToPlane_addOffset (p : ℚ × ℚ) (z : ZPoint) :
    sampleToPlane (addOffset p z) = sampleToPlane p + integerPoint z.toIntegerPlane := by
  apply Complex.ext <;> simp [sampleToPlane, addOffset, ZPoint.toIntegerPlane]

private theorem twiceSignedArea_cyclic (a b c : Plane) :
    twiceSignedArea b c a = twiceSignedArea a b c := by
  simp only [twiceSignedArea]
  ring

private theorem twiceSignedArea_cyclic' (a b c : Plane) :
    twiceSignedArea c a b = twiceSignedArea a b c := by
  rw [twiceSignedArea_cyclic, twiceSignedArea_cyclic]

private theorem convex_twiceSignedArea_nonneg (a b : Plane) :
    Convex ℝ {p : Plane | 0 ≤ twiceSignedArea a b p} := by
  intro x hx y hy u v hu hv huv
  change 0 ≤ twiceSignedArea a b x at hx
  change 0 ≤ twiceSignedArea a b y at hy
  change 0 ≤ twiceSignedArea a b (u • x + v • y)
  have hformula :
      twiceSignedArea a b (u • x + v • y) =
        u * twiceSignedArea a b x + v * twiceSignedArea a b y := by
    simp only [twiceSignedArea, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, smul_eq_mul]
    have hv_eq : v = 1 - u := by linarith
    rw [hv_eq]
    ring
  rw [hformula]
  exact add_nonneg (mul_nonneg hu hx) (mul_nonneg hv hy)

private theorem convex_twiceSignedArea_nonpos (a b : Plane) :
    Convex ℝ {p : Plane | twiceSignedArea a b p ≤ 0} := by
  intro x hx y hy u v hu hv huv
  change twiceSignedArea a b x ≤ 0 at hx
  change twiceSignedArea a b y ≤ 0 at hy
  change twiceSignedArea a b (u • x + v • y) ≤ 0
  have hformula :
      twiceSignedArea a b (u • x + v • y) =
        u * twiceSignedArea a b x + v * twiceSignedArea a b y := by
    simp only [twiceSignedArea, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, smul_eq_mul]
    have hv_eq : v = 1 - u := by linarith
    rw [hv_eq]
    ring
  rw [hformula]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hu hx)
    (mul_nonpos_of_nonneg_of_nonpos hv hy)

private theorem twiceSignedArea_nonneg_on_convexHull (a b c : Plane)
    (harea : 0 ≤ twiceSignedArea a b c) :
    ∀ p ∈ convexHull ℝ ({a, b, c} : Set Plane), 0 ≤ twiceSignedArea a b p := by
  apply convexHull_min
  · intro p hp
    change 0 ≤ twiceSignedArea a b p
    rcases hp with rfl | rfl | rfl
    · simp [twiceSignedArea]
    · simp only [twiceSignedArea]
      ring_nf
      exact le_rfl
    · exact harea
  · exact convex_twiceSignedArea_nonneg a b

private theorem twiceSignedArea_nonpos_on_convexHull (a b c : Plane)
    (harea : twiceSignedArea a b c ≤ 0) :
    ∀ p ∈ convexHull ℝ ({a, b, c} : Set Plane), twiceSignedArea a b p ≤ 0 := by
  apply convexHull_min
  · intro p hp
    change twiceSignedArea a b p ≤ 0
    rcases hp with rfl | rfl | rfl
    · simp [twiceSignedArea]
    · simp only [twiceSignedArea]
      ring_nf
      exact le_rfl
    · exact harea
  · exact convex_twiceSignedArea_nonpos a b

private theorem mem_convexHull_three_signs_of_mem {a b c p : Plane}
    (hp : p ∈ convexHull ℝ ({a, b, c} : Set Plane)) :
    (0 ≤ twiceSignedArea a b p ∧ 0 ≤ twiceSignedArea b c p ∧
        0 ≤ twiceSignedArea c a p) ∨
      (twiceSignedArea a b p ≤ 0 ∧ twiceSignedArea b c p ≤ 0 ∧
        twiceSignedArea c a p ≤ 0) := by
  by_cases harea : 0 ≤ twiceSignedArea a b c
  · left
    have hcyclic₁ : ({b, c, a} : Set Plane) = {a, b, c} := by
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    have hcyclic₂ : ({c, a, b} : Set Plane) = {a, b, c} := by
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    exact ⟨twiceSignedArea_nonneg_on_convexHull a b c harea p hp,
      twiceSignedArea_nonneg_on_convexHull b c a
        (by rwa [twiceSignedArea_cyclic]) p (by rwa [hcyclic₁]),
      twiceSignedArea_nonneg_on_convexHull c a b
        (by rwa [twiceSignedArea_cyclic']) p (by rwa [hcyclic₂])⟩
  · right
    have harea' : twiceSignedArea a b c ≤ 0 := le_of_lt (lt_of_not_ge harea)
    have hcyclic₁ : ({b, c, a} : Set Plane) = {a, b, c} := by
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    have hcyclic₂ : ({c, a, b} : Set Plane) = {a, b, c} := by
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    exact ⟨twiceSignedArea_nonpos_on_convexHull a b c harea' p hp,
      twiceSignedArea_nonpos_on_convexHull b c a
        (by rwa [twiceSignedArea_cyclic]) p (by rwa [hcyclic₁]),
      twiceSignedArea_nonpos_on_convexHull c a b
        (by rwa [twiceSignedArea_cyclic']) p (by rwa [hcyclic₂])⟩

private theorem mem_convexHull_three_of_signs {a b c p : Plane}
    (harea : twiceSignedArea a b c ≠ 0)
    (hsigns :
      (0 ≤ twiceSignedArea a b p ∧ 0 ≤ twiceSignedArea b c p ∧
          0 ≤ twiceSignedArea c a p) ∨
        (twiceSignedArea a b p ≤ 0 ∧ twiceSignedArea b c p ≤ 0 ∧
          twiceSignedArea c a p ≤ 0)) :
    p ∈ convexHull ℝ ({a, b, c} : Set Plane) := by
  have hsum :
      twiceSignedArea a b p + twiceSignedArea b c p + twiceSignedArea c a p =
        twiceSignedArea a b c := by
    simp only [twiceSignedArea]
    ring
  rcases hsigns with hnonneg | hnonpos
  · have harea_pos : 0 < twiceSignedArea a b c := by
      have harea_nonneg : 0 ≤ twiceSignedArea a b c := by linarith
      exact lt_of_le_of_ne harea_nonneg harea.symm
    let w : Fin 3 → ℝ := ![
      twiceSignedArea b c p / twiceSignedArea a b c,
      twiceSignedArea c a p / twiceSignedArea a b c,
      twiceSignedArea a b p / twiceSignedArea a b c]
    let z : Fin 3 → Plane := ![a, b, c]
    refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ ?_
    · intro i
      fin_cases i
      · exact div_nonneg hnonneg.2.1 harea_pos.le
      · exact div_nonneg hnonneg.2.2 harea_pos.le
      · exact div_nonneg hnonneg.1 harea_pos.le
    · rw [Fin.sum_univ_three]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, w]
      rw [← add_div, ← add_div]
      have hsum' :
          twiceSignedArea b c p + twiceSignedArea c a p + twiceSignedArea a b p =
            twiceSignedArea a b c := by linarith [hsum]
      rw [hsum', div_self harea]
    · intro i
      fin_cases i <;> simp [z]
    · apply Complex.ext
      · rw [Fin.sum_univ_three]
        simp [w, z, Complex.add_re]
        field_simp [harea]
        simp only [twiceSignedArea]
        ring
      · rw [Fin.sum_univ_three]
        simp [w, z, Complex.add_im]
        field_simp [harea]
        simp only [twiceSignedArea]
        ring
  · have harea_neg : twiceSignedArea a b c < 0 := by
      have harea_nonpos : twiceSignedArea a b c ≤ 0 := by linarith
      exact lt_of_le_of_ne harea_nonpos harea
    let w : Fin 3 → ℝ := ![
      twiceSignedArea b c p / twiceSignedArea a b c,
      twiceSignedArea c a p / twiceSignedArea a b c,
      twiceSignedArea a b p / twiceSignedArea a b c]
    let z : Fin 3 → Plane := ![a, b, c]
    refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ ?_
    · intro i
      fin_cases i
      · exact div_nonneg_of_nonpos hnonpos.2.1 harea_neg.le
      · exact div_nonneg_of_nonpos hnonpos.2.2 harea_neg.le
      · exact div_nonneg_of_nonpos hnonpos.1 harea_neg.le
    · rw [Fin.sum_univ_three]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, w]
      rw [← add_div, ← add_div]
      have hsum' :
          twiceSignedArea b c p + twiceSignedArea c a p + twiceSignedArea a b p =
            twiceSignedArea a b c := by linarith [hsum]
      rw [hsum', div_self harea]
    · intro i
      fin_cases i <;> simp [z]
    · apply Complex.ext
      · rw [Fin.sum_univ_three]
        simp [w, z, Complex.add_re]
        field_simp [harea]
        simp only [twiceSignedArea]
        ring
      · rw [Fin.sum_univ_three]
        simp [w, z, Complex.add_im]
        field_simp [harea]
        simp only [twiceSignedArea]
        ring

/-- A point belongs to a nondegenerate closed triangle exactly when its three oriented edge areas
are all weakly nonnegative or all weakly nonpositive. -/
theorem mem_convexHull_three_iff_signs {a b c p : Plane}
    (harea : twiceSignedArea a b c ≠ 0) :
    p ∈ convexHull ℝ ({a, b, c} : Set Plane) ↔
      (0 ≤ twiceSignedArea a b p ∧ 0 ≤ twiceSignedArea b c p ∧
          0 ≤ twiceSignedArea c a p) ∨
        (twiceSignedArea a b p ≤ 0 ∧ twiceSignedArea b c p ≤ 0 ∧
          twiceSignedArea c a p ≤ 0) := by
  constructor
  · exact mem_convexHull_three_signs_of_mem
  · exact mem_convexHull_three_of_signs harea

/-- Embedding an integral point through rational coordinates agrees with its direct embedding. -/
@[simp]
theorem sampleToPlane_zpointQ (p : ZPoint) :
    sampleToPlane (zpointQ p) = p.toPlane := by
  apply Complex.ext <;> simp [sampleToPlane, zpointQ, ZPoint.toPlane]

/-- Rational twice-area casts exactly to the real-plane signed-area expression. -/
theorem twiceAreaQ_cast (a b p : ℚ × ℚ) :
    (twiceAreaQ a b p : ℝ) =
      twiceSignedArea (sampleToPlane a) (sampleToPlane b) (sampleToPlane p) := by
  simp only [twiceAreaQ, twiceSignedArea, sampleToPlane_re, sampleToPlane_im]
  push_cast
  rfl

/-- The rational orientation of integral endpoints casts to their real-plane orientation. -/
theorem twiceAreaQ_zpointQ_cast (a b : ZPoint) (p : ℚ × ℚ) :
    (twiceAreaQ (zpointQ a) (zpointQ b) p : ℝ) =
      twiceSignedArea a.toPlane b.toPlane (sampleToPlane p) := by
  rw [twiceAreaQ_cast, sampleToPlane_zpointQ, sampleToPlane_zpointQ]

/-- The executable orientation test agrees with convex-hull membership for a nondegenerate
integer triangle. -/
theorem pointInTriangle_eq_true_iff_mem_carrier {p : ℚ × ℚ} {t : ZTriangle}
    (harea : twiceAreaQ (zpointQ t.a) (zpointQ t.b) (zpointQ t.c) ≠ 0) :
    pointInTriangle p t = true ↔ sampleToPlane p ∈ t.carrier := by
  rw [ZTriangle.carrier, mem_convexHull_three_iff_signs]
  · simp only [pointInTriangle]
    simp only [decide_eq_true_eq]
    rw [← twiceAreaQ_zpointQ_cast, ← twiceAreaQ_zpointQ_cast,
      ← twiceAreaQ_zpointQ_cast]
    norm_cast
  · rw [← sampleToPlane_zpointQ t.c, ← twiceAreaQ_zpointQ_cast]
    exact_mod_cast harea

/-- Away from zero, the weak common-sign test is equivalent to the strict common-sign test. -/
theorem weak_signs_iff_strict_signs_of_ne {α : Type*} [LinearOrder α] [Zero α]
    {s₀ s₁ s₂ : α} (h₀ : s₀ ≠ 0) (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) :
    ((0 ≤ s₀ ∧ 0 ≤ s₁ ∧ 0 ≤ s₂) ∨ (s₀ ≤ 0 ∧ s₁ ≤ 0 ∧ s₂ ≤ 0)) ↔
      ((0 < s₀ ∧ 0 < s₁ ∧ 0 < s₂) ∨ (s₀ < 0 ∧ s₁ < 0 ∧ s₂ < 0)) := by
  constructor
  · rintro (hpos | hneg)
    · left
      exact ⟨lt_of_le_of_ne hpos.1 h₀.symm,
        lt_of_le_of_ne hpos.2.1 h₁.symm, lt_of_le_of_ne hpos.2.2 h₂.symm⟩
    · right
      exact ⟨lt_of_le_of_ne hneg.1 h₀,
        lt_of_le_of_ne hneg.2.1 h₁, lt_of_le_of_ne hneg.2.2 h₂⟩
  · rintro (hpos | hneg)
    · exact Or.inl ⟨hpos.1.le, hpos.2.1.le, hpos.2.2.le⟩
    · exact Or.inr ⟨hneg.1.le, hneg.2.1.le, hneg.2.2.le⟩

/-- Away from triangle edges, the executable triangle test is the strict common-sign test. -/
theorem pointInTriangle_eq_true_iff_strict_signs {p : ℚ × ℚ} {t : ZTriangle}
    (h₀ : twiceAreaQ (zpointQ t.a) (zpointQ t.b) p ≠ 0)
    (h₁ : twiceAreaQ (zpointQ t.b) (zpointQ t.c) p ≠ 0)
    (h₂ : twiceAreaQ (zpointQ t.c) (zpointQ t.a) p ≠ 0) :
    pointInTriangle p t = true ↔
      ((0 < twiceAreaQ (zpointQ t.a) (zpointQ t.b) p ∧
          0 < twiceAreaQ (zpointQ t.b) (zpointQ t.c) p ∧
          0 < twiceAreaQ (zpointQ t.c) (zpointQ t.a) p) ∨
        (twiceAreaQ (zpointQ t.a) (zpointQ t.b) p < 0 ∧
          twiceAreaQ (zpointQ t.b) (zpointQ t.c) p < 0 ∧
          twiceAreaQ (zpointQ t.c) (zpointQ t.a) p < 0)) := by
  simp only [pointInTriangle, decide_eq_true_eq]
  exact weak_signs_iff_strict_signs_of_ne h₀ h₁ h₂

/-- A translated integral edge-line evaluation is the negative rational orientation area. -/
theorem edgeLine_eval_eq_neg_twiceAreaQ (z a b : ZPoint) (p : ℚ × ℚ) :
    (edgeLine z a b).eval p =
      -twiceAreaQ (zpointQ a) (zpointQ b) (addOffset p z) := by
  simp only [edgeLine, ZLine.eval, twiceAreaQ, zpointQ, addOffset]
  push_cast
  ring

/-- Evaluate the same integral affine line on an arbitrary real-plane point. -/
def ZLine.evalPlane (l : ZLine) (p : Plane) : ℝ :=
  l.A * p.re + l.B * p.im + l.C

/-- Real evaluation at an embedded rational sample is the cast of rational evaluation. -/
theorem ZLine.evalPlane_sampleToPlane (l : ZLine) (p : ℚ × ℚ) :
    l.evalPlane (sampleToPlane p) = (l.eval p : ℝ) := by
  simp only [ZLine.evalPlane, ZLine.eval, sampleToPlane_re, sampleToPlane_im]
  push_cast
  rfl

/-- A translated edge-line evaluation is the negative real-plane signed area. -/
theorem edgeLine_evalPlane_eq_neg_twiceSignedArea (z a b : ZPoint) (p : Plane) :
    (edgeLine z a b).evalPlane p =
      -twiceSignedArea a.toPlane b.toPlane (p + integerPoint z.toIntegerPlane) := by
  rw [z.integerPoint_toIntegerPlane]
  simp [ZLine.evalPlane, edgeLine, twiceSignedArea, ZPoint.toPlane]
  ring

/-- Two nonzero real numbers lie on the same strict side of zero. -/
def SameStrictSign (x y : ℝ) : Prop :=
  (0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)

namespace SameStrictSign

/-- The left member of a same-strict-sign pair is nonzero. -/
theorem left_ne {x y : ℝ} (h : SameStrictSign x y) : x ≠ 0 := by
  rcases h with h | h
  · exact ne_of_gt h.1
  · exact ne_of_lt h.1

/-- The right member of a same-strict-sign pair is nonzero. -/
theorem right_ne {x y : ℝ} (h : SameStrictSign x y) : y ≠ 0 := by
  rcases h with h | h
  · exact ne_of_gt h.2
  · exact ne_of_lt h.2

/-- Same-strict-sign numbers are positive simultaneously. -/
theorem pos_iff {x y : ℝ} (h : SameStrictSign x y) : 0 < x ↔ 0 < y := by
  rcases h with h | h
  · exact iff_of_true h.1 h.2
  · constructor <;> intro hpos <;> linarith

/-- Same-strict-sign numbers are negative simultaneously. -/
theorem neg_iff {x y : ℝ} (h : SameStrictSign x y) : x < 0 ↔ y < 0 := by
  rcases h with h | h
  · constructor <;> intro hneg <;> linarith
  · exact iff_of_true h.1 h.2

/-- Simultaneous negation preserves the same-strict-sign relation. -/
theorem neg_iff_neg {x y : ℝ} :
    SameStrictSign (-x) (-y) ↔ SameStrictSign x y := by
  simp only [SameStrictSign, neg_pos, neg_lt_zero]
  tauto

end SameStrictSign

/-- Any two rational points satisfying a covered strict system lie on the same strict side of
every covered line. -/
theorem sameStrictSign_eval_of_satisfies {ls : List ZLine}
    {qs : List StrictInequality} {p q : ℚ × ℚ} (hcover : Covers ls qs)
    (hp : SatisfiesAll qs p) (hq : SatisfiesAll qs q) {l : ZLine} (hl : l ∈ ls) :
    SameStrictSign (l.eval p : ℝ) (l.eval q : ℝ) := by
  rcases hcover l hl with hneg | hpos
  · right
    have hpneg := (sideConstraint_false_satisfies_iff l p).mp (hp _ hneg)
    have hqneg := (sideConstraint_false_satisfies_iff l q).mp (hq _ hneg)
    exact ⟨by exact_mod_cast hpneg, by exact_mod_cast hqneg⟩
  · left
    have hppos := (sideConstraint_true_satisfies_iff l p).mp (hp _ hpos)
    have hqpos := (sideConstraint_true_satisfies_iff l q).mp (hq _ hpos)
    exact ⟨by exact_mod_cast hppos, by exact_mod_cast hqpos⟩

/-- Any two rational points satisfying one final feasible cell have matching strict signs on
every processed line. -/
theorem sameStrictSign_eval_of_cell_system {ls : List ZLine} {cell : SignCell}
    {p q : ℚ × ℚ} (hcell : cell ∈ feasibleSignCells ls)
    (hp : SatisfiesAll cell.system p) (hq : SatisfiesAll cell.system q)
    {l : ZLine} (hl : l ∈ ls) :
    SameStrictSign (l.eval p : ℝ) (l.eval q : ℝ) :=
  sameStrictSign_eval_of_satisfies (feasibleSignCells_covers hcell) hp hq hl

/-- The solver sample and every represented point have matching strict signs on every processed
line. -/
theorem sameStrictSign_sample_of_cell {ls : List ZLine} {cell : SignCell}
    {p : ℚ × ℚ} (hcell : cell ∈ feasibleSignCells ls)
    (hp : SatisfiesAll cell.system p) {l : ZLine} (hl : l ∈ ls) :
    SameStrictSign (l.eval cell.sample : ℝ) (l.eval p : ℝ) :=
  sameStrictSign_eval_of_cell_system hcell (feasibleSignCells_sound hcell) hp hl

/-- Two points with matching strict signs on all three edges have equivalent membership in a
nondegenerate triangle. -/
theorem mem_convexHull_three_iff_of_sameStrictSign {a b c u v : Plane}
    (harea : twiceSignedArea a b c ≠ 0)
    (h₀ : SameStrictSign (twiceSignedArea a b u) (twiceSignedArea a b v))
    (h₁ : SameStrictSign (twiceSignedArea b c u) (twiceSignedArea b c v))
    (h₂ : SameStrictSign (twiceSignedArea c a u) (twiceSignedArea c a v)) :
    u ∈ convexHull ℝ ({a, b, c} : Set Plane) ↔
      v ∈ convexHull ℝ ({a, b, c} : Set Plane) := by
  rw [mem_convexHull_three_iff_signs harea, mem_convexHull_three_iff_signs harea,
    weak_signs_iff_strict_signs_of_ne h₀.left_ne h₁.left_ne h₂.left_ne,
    weak_signs_iff_strict_signs_of_ne h₀.right_ne h₁.right_ne h₂.right_ne,
    h₀.pos_iff, h₁.pos_iff, h₂.pos_iff, h₀.neg_iff, h₁.neg_iff, h₂.neg_iff]

/-- Matching strict translated-edge signs transfer exact triangle membership from a real point
to the executable rational orientation test. -/
theorem mem_carrier_iff_pointInTriangle_of_same_strict_edge_signs
    {u : Plane} {p : ℚ × ℚ} {z : ZPoint} {t : ZTriangle}
    (harea : twiceAreaQ (zpointQ t.a) (zpointQ t.b) (zpointQ t.c) ≠ 0)
    (h₀ : SameStrictSign ((edgeLine z t.a t.b).evalPlane u)
      ((edgeLine z t.a t.b).eval p : ℝ))
    (h₁ : SameStrictSign ((edgeLine z t.b t.c).evalPlane u)
      ((edgeLine z t.b t.c).eval p : ℝ))
    (h₂ : SameStrictSign ((edgeLine z t.c t.a).evalPlane u)
      ((edgeLine z t.c t.a).eval p : ℝ)) :
    u + integerPoint z.toIntegerPlane ∈ t.carrier ↔
      pointInTriangle (addOffset p z) t = true := by
  have harea_real : twiceSignedArea t.a.toPlane t.b.toPlane t.c.toPlane ≠ 0 := by
    rw [← sampleToPlane_zpointQ t.c, ← twiceAreaQ_zpointQ_cast]
    exact_mod_cast harea
  have hedge₀u := edgeLine_evalPlane_eq_neg_twiceSignedArea z t.a t.b u
  have hedge₁u := edgeLine_evalPlane_eq_neg_twiceSignedArea z t.b t.c u
  have hedge₂u := edgeLine_evalPlane_eq_neg_twiceSignedArea z t.c t.a u
  have hedge₀p := edgeLine_evalPlane_eq_neg_twiceSignedArea z t.a t.b (sampleToPlane p)
  have hedge₁p := edgeLine_evalPlane_eq_neg_twiceSignedArea z t.b t.c (sampleToPlane p)
  have hedge₂p := edgeLine_evalPlane_eq_neg_twiceSignedArea z t.c t.a (sampleToPlane p)
  rw [← sampleToPlane_addOffset] at hedge₀p hedge₁p hedge₂p
  have h₀' : SameStrictSign
      (twiceSignedArea t.a.toPlane t.b.toPlane (u + integerPoint z.toIntegerPlane))
      (twiceSignedArea t.a.toPlane t.b.toPlane (sampleToPlane (addOffset p z))) := by
    rw [← SameStrictSign.neg_iff_neg]
    rw [← hedge₀u, ← hedge₀p, ZLine.evalPlane_sampleToPlane]
    exact h₀
  have h₁' : SameStrictSign
      (twiceSignedArea t.b.toPlane t.c.toPlane (u + integerPoint z.toIntegerPlane))
      (twiceSignedArea t.b.toPlane t.c.toPlane (sampleToPlane (addOffset p z))) := by
    rw [← SameStrictSign.neg_iff_neg]
    rw [← hedge₁u, ← hedge₁p, ZLine.evalPlane_sampleToPlane]
    exact h₁
  have h₂' : SameStrictSign
      (twiceSignedArea t.c.toPlane t.a.toPlane (u + integerPoint z.toIntegerPlane))
      (twiceSignedArea t.c.toPlane t.a.toPlane (sampleToPlane (addOffset p z))) := by
    rw [← SameStrictSign.neg_iff_neg]
    rw [← hedge₂u, ← hedge₂p, ZLine.evalPlane_sampleToPlane]
    exact h₂
  calc
    u + integerPoint z.toIntegerPlane ∈ t.carrier ↔
        sampleToPlane (addOffset p z) ∈ t.carrier := by
      exact mem_convexHull_three_iff_of_sameStrictSign harea_real h₀' h₁' h₂'
    _ ↔ pointInTriangle (addOffset p z) t = true :=
      (pointInTriangle_eq_true_iff_mem_carrier harea).symm

end Tiling.RationalPolygonal.Raw.Compiler
