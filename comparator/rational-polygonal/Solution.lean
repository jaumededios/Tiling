import Mathlib
import Tiling.RationalPolygonal.Main

/-!
# Solution for the rational-polygon comparator

The complete definition block below is repeated from the trusted `Challenge.lean`. Repetition is
intentional: the challenge remains one Mathlib-only file which a mathematician can read from top
to bottom, while `leanprover/comparator` independently verifies that these declarations elaborate
to exactly the same constants in the solution environment.

After that repeated block, the `ProductionBridge` namespace performs explicit conversion to the
project's geometry and invokes the formalized de Dios Pont--Grebík--Greenfeld--Madrid theorem.
-/

open Function MeasureTheory Set
open scoped Pointwise

namespace DeDiosGreenfeldComparator

/-! ## 1. Translational tilings of the plane -/

/-- The real plane, represented by `ℂ` with its usual real two-dimensional geometry. -/
abbrev Plane := ℂ

/-- The translates `t + Ω`, for `t ∈ T`, form a packing: two distinct copies of the tile `Ω`
overlap only on a set of Lebesgue measure zero. -/
def Packing (Ω T : Set Plane) : Prop :=
  ∀ ⦃s⦄, s ∈ T → ∀ ⦃t⦄, t ∈ T → s ≠ t →
    volume ((s +ᵥ Ω) ∩ (t +ᵥ Ω)) = 0

/-- The translates of `Ω` by `T` cover almost every point of the plane. -/
def Covering (Ω T : Set Plane) : Prop :=
  ∀ᵐ x ∂volume, ∃ t ∈ T, x ∈ t +ᵥ Ω

/-- The set `T` is a translational tiling of the plane by the single tile `Ω`: `T` is countable,
its translates of `Ω` form a packing, and those translates cover almost every point. -/
def Tiling (Ω T : Set Plane) : Prop :=
  T.Countable ∧ Packing Ω T ∧ Covering Ω T

/-! ## 1.1. Periodic translation sets -/

/-- Membership in `A` is unchanged after translation by `h`. -/
def PeriodicBy (A : Set Plane) (h : Plane) : Prop :=
  ∀ x, x + h ∈ A ↔ x ∈ A

/-- A planar translation set is doubly periodic when it has two nonparallel periods.

The displayed determinant is nonzero exactly when the two vectors are linearly independent. -/
def Periodic (A : Set Plane) : Prop :=
  ∃ h₁ h₂ : Plane,
    h₁.re * h₂.im - h₁.im * h₂.re ≠ 0 ∧ PeriodicBy A h₁ ∧ PeriodicBy A h₂

/-! ## 2. Polygonal tiles -/

/-- Twice the oriented area of the triangle with vertices `a`, `b`, and `c`. -/
def twiceSignedArea (a b c : Plane) : ℝ :=
  (b.re - a.re) * (c.im - a.im) - (b.im - a.im) * (c.re - a.re)

/-- A nondegenerate closed triangle. -/
def IsTriangle (s : Set Plane) : Prop :=
  ∃ a b c : Plane, twiceSignedArea a b c ≠ 0 ∧ s = convexHull ℝ {a, b, c}

/-- A finite decomposition of `Ω` into triangles whose distinct interiors overlap only on a
null set. Exact union is used for the closed representatives. -/
structure Triangulation (Ω : Set Plane) where
  /-- The finitely many triangular pieces. -/
  pieces : Finset (Set Plane)
  /-- Every piece is a nondegenerate triangle. -/
  isTriangle : ∀ t ∈ pieces, IsTriangle t
  /-- Distinct triangles intersect only on a null set. -/
  nullOverlap : ∀ ⦃s⦄, s ∈ pieces → ∀ ⦃t⦄, t ∈ pieces → s ≠ t →
    volume (s ∩ t) = 0
  /-- The pieces have union exactly `Ω`. -/
  sUnion_eq : ⋃₀ (pieces : Set (Set Plane)) = Ω

/-- A planar set is polygonal when it can be written as a finite union of nondegenerate
triangles, with overlaps allowed only along null boundaries. -/
def Polygonal (Ω : Set Plane) : Prop :=
  Nonempty (Triangulation Ω)

/-- The intrinsic vertices of a polygonal set.

A point is intrinsic when every triangulation sees it as an extreme point of one of its triangle
pieces. Quantifying over every triangulation makes this independent of arbitrary added diagonals
or subdivisions. -/
def intrinsicVertices (Ω : Set Plane) : Set Plane :=
  {x | ∀ triangulation : Triangulation Ω,
    ∃ t ∈ triangulation.pieces, x ∈ t.extremePoints ℝ}

/-! ## 3. Rational polygonal tiles -/

/-- A planar point with integer real and imaginary coordinates. -/
def IsIntegerPoint (z : Plane) : Prop :=
  ∃ m n : ℤ, z = (m : ℝ) + (n : ℝ) * Complex.I

/-- A translation-invariant common-denominator presentation of a rational polygon.

The chosen `anchor` is an intrinsic vertex. After moving it to the origin, multiplication by one
positive natural number sends every intrinsic vertex into `ℤ²`. This is equivalent to saying
that every difference of two polygon vertices has rational coordinates, but records the common
denominator needed by the normalization argument. -/
def RationalPolygon (Ω : Set Plane) : Prop :=
  Polygonal Ω ∧ Ω.Nonempty ∧
    ∃ anchor : Plane, anchor ∈ intrinsicVertices Ω ∧
      ∃ denominator : ℕ, 0 < denominator ∧
        ∀ w ∈ intrinsicVertices Ω,
          IsIntegerPoint ((denominator : ℝ) • (w - anchor))

end DeDiosGreenfeldComparator

namespace DeDiosGreenfeldComparator

namespace ProductionBridge

/-! ## Polygonal geometry -/

/-- Turn a comparator triangulation into the production library's triangulation structure. -/
def toProductionTriangulation {Ω : Set Plane} (τ : Triangulation Ω) :
    Tiling.Triangulation Ω where
  pieces := τ.pieces
  isTriangle := by
    intro t ht
    simpa [IsTriangle, twiceSignedArea, Tiling.IsTriangle, Tiling.twiceSignedArea] using
      τ.isTriangle t ht
  pairwiseAEDisjoint := by
    intro s hs t ht hst
    exact τ.nullOverlap hs ht hst
  sUnion_eq := τ.sUnion_eq

/-- Read a production triangulation using the comparator's independent structure. -/
def ofProductionTriangulation {Ω : Set Plane} (τ : Tiling.Triangulation Ω) :
    Triangulation Ω where
  pieces := τ.pieces
  isTriangle := by
    intro t ht
    simpa [IsTriangle, twiceSignedArea, Tiling.IsTriangle, Tiling.twiceSignedArea] using
      τ.isTriangle t ht
  nullOverlap := by
    intro s hs t ht hst
    exact τ.pairwiseAEDisjoint hs ht hst
  sUnion_eq := τ.sUnion_eq

/-- The independently defined intrinsic vertices are exactly the production vertex set.

The proof simply converts a triangulation in either direction.  This is the key check that the
challenge did not smuggle in a preferred triangulation or a different notion of polygon vertex. -/
theorem intrinsicVertices_eq_vertexSet (Ω : Set Plane) :
    intrinsicVertices Ω = Tiling.vertexSet Ω := by
  ext x
  constructor
  · intro hx τ
    obtain ⟨t, ht, hxt⟩ := hx (ofProductionTriangulation τ)
    exact ⟨t, ht, hxt⟩
  · intro hx τ
    obtain ⟨t, ht, hxt⟩ := hx (toProductionTriangulation τ)
    exact ⟨t, ht, hxt⟩

/-! ## Integer points -/

/-- The elementary coordinate definition of an integer point implies membership in the
production integer lattice. -/
theorem production_isIntegerPoint_of_isIntegerPoint {z : Plane}
    (hz : IsIntegerPoint z) :
    Tiling.RationalPolygonal.IsIntegerPoint z := by
  obtain ⟨m, n, rfl⟩ := hz
  apply Tiling.RationalPolygonal.mem_integerLattice_iff.mpr
  refine ⟨![m, n], ?_⟩
  simp [Tiling.RationalPolygonal.integerPoint]

/-! ## Monotile tilings -/

/-- Convert the comparator's direct monotile tiling relation to the unit-labelled production
relation. -/
theorem toProductionTiling (K : Tiling.RationalPolygonal.PolygonalRegion)
    {T : Set Plane} (hT : Tiling K.support T) :
    K.Tiles T := by
  refine
    { countable := K.placements_countable hT.1
      isPacking := ?_
      isCover := ?_ }
  · intro p hp q hq hpq
    apply hT.2.1 hp hq
    intro hpqfst
    apply hpq
    apply Prod.ext
    · exact hpqfst
    · exact Subsingleton.elim _ _
  · filter_upwards [hT.2.2] with x hx
    obtain ⟨t, ht, hxt⟩ := hx
    apply Set.mem_iUnion.mpr
    refine ⟨⟨(t, ()), ht⟩, ?_⟩
    exact hxt

/-- Convert a production monotile tiling back to the direct comparator relation. -/
theorem ofProductionTiling (K : Tiling.RationalPolygonal.PolygonalRegion)
    {T : Set Plane} (hT : K.Tiles T) :
    Tiling K.support T := by
  refine ⟨hT.countable, ?_, ?_⟩
  · intro s hs t ht hst
    have hplacements :
        AEDisjoint volume
          (Tiling.placedTile K.prototileFamily (s, ()))
          (Tiling.placedTile K.prototileFamily (t, ())) := by
      apply hT.isPacking hs ht
      intro hpair
      exact hst (congrArg Prod.fst hpair)
    exact hplacements
  · filter_upwards [hT.isCover] with x hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    exact ⟨p.1.1, p.property, hxp⟩

/-- Translate the production library's linear-independence formulation of double periodicity into
the nonzero-determinant formulation displayed in the challenge. -/
theorem periodic_of_production {A : Set Plane}
    (hA : Tiling.RationalPolygonal.DoublyPeriodic A) : Periodic A := by
  obtain ⟨h₁, h₂, hlinear, hperiod₁, hperiod₂⟩ := hA
  refine ⟨h₁, h₂, ?_, hperiod₁, hperiod₂⟩
  rw [linearIndependent_fin2] at hlinear
  obtain ⟨h₂ne, hnotMultiple⟩ := hlinear
  intro hdet
  by_cases hre : h₂.re = 0
  · have him : h₂.im ≠ 0 := by
      intro him
      apply h₂ne
      apply Complex.ext <;> simp [hre, him]
    have h₁re : h₁.re = 0 := by
      have hdet' := hdet
      rw [hre, mul_zero, sub_zero] at hdet'
      exact (mul_eq_zero.mp hdet').resolve_right him
    apply hnotMultiple (h₁.im / h₂.im)
    apply Complex.ext
    · simp [hre, h₁re]
    · simp [div_mul_cancel₀ _ him]
  · apply hnotMultiple (h₁.re / h₂.re)
    apply Complex.ext
    · simp [div_mul_cancel₀ _ hre]
    · simp only [Complex.smul_im, smul_eq_mul]
      rw [div_mul_eq_mul_div, div_eq_iff hre]
      change h₁.re * h₂.im = h₁.im * h₂.re
      exact sub_eq_zero.mp hdet

/-! ## The theorem bridge -/

/-- The Mathlib-only rationality predicate supplies a production region with the same support.

This is existential rather than a data-valued definition because `RationalPolygon Ω` is a
proposition: the theorem must not pretend that its geometric witnesses are executable input. -/
theorem exists_productionRegion {Ω : Set Plane} (hΩ : RationalPolygon Ω) :
    ∃ K : Tiling.RationalPolygonal.RationalPolygonalRegion, K.support = Ω := by
  rcases hΩ with ⟨⟨τ⟩, hnonempty, anchor, hanchor, denominator, hdenominator, hvertices⟩
  refine ⟨
    { support := Ω
      isPolygonal := ⟨toProductionTriangulation τ⟩
      nonempty := hnonempty
      anchor := anchor
      anchor_mem_vertex := by
        rw [← intrinsicVertices_eq_vertexSet]
        exact hanchor
      denominator := denominator
      denominator_pos := hdenominator
      vertex_integral := by
        intro w hw
        apply production_isIntegerPoint_of_isIntegerPoint
        apply hvertices w
        rwa [intrinsicVertices_eq_vertexSet] }, rfl⟩

end ProductionBridge

open ProductionBridge

/-- Every translationally tileable rational polygon admits a doubly periodic tiling.

This repeats the exact challenge theorem name and type.  The proof constructs the production
region, applies paper Theorem 1.1, and converts the returned tiling back to the independent
Mathlib-only vocabulary. -/
theorem periodic_tiling_of_rational_polygon
    (Ω : Set Plane) (hΩ : RationalPolygon Ω) :
    (∃ T : Set Plane, Tiling Ω T) →
      ∃ T : Set Plane, Periodic T ∧ Tiling Ω T := by
  intro htileable
  obtain ⟨K, hK⟩ := exists_productionRegion hΩ
  obtain ⟨T, hT⟩ := htileable
  have hT' : Tiling K.support T := by
    simpa only [hK] using hT
  have hproductionTileable :
      ∃ T : Set Plane, K.toPolygonalRegion.Tiles T :=
    ⟨T, toProductionTiling K.toPolygonalRegion hT'⟩
  obtain ⟨S, hStiles, hSperiodic⟩ :=
    (Tiling.RationalPolygonal.RationalPolygonalRegion.theorem_1_1 K).mp
      hproductionTileable
  refine ⟨S, periodic_of_production hSperiodic, ?_⟩
  simpa only [hK] using ofProductionTiling K.toPolygonalRegion hStiles

end DeDiosGreenfeldComparator
