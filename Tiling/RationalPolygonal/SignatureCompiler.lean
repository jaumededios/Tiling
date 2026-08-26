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

open LinearFeasibility

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

end Tiling.RationalPolygonal.Raw.Compiler
