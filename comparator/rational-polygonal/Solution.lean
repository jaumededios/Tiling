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
  ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ →
    volume ((t₁ +ᵥ Ω) ∩ (t₂ +ᵥ Ω)) = 0

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

/-- A planar translation set is doubly periodic when it has two linearly independent real
translation periods. -/
def Periodic (A : Set Plane) : Prop :=
  ∃ h₁ h₂ : Plane,
    LinearIndependent ℝ ![h₁, h₂] ∧ PeriodicBy A h₁ ∧ PeriodicBy A h₂

/-! ## 2. Polygonal tiles -/

/-- Twice the oriented area of the triangle with vertices `a`, `b`, and `c`. -/
def twiceSignedArea (a b c : Plane) : ℝ :=
  (b.re - a.re) * (c.im - a.im) - (b.im - a.im) * (c.re - a.re)

/-- A nondegenerate closed triangle. -/
def IsTriangle (s : Set Plane) : Prop :=
  ∃ a b c : Plane, twiceSignedArea a b c ≠ 0 ∧ s = convexHull ℝ {a, b, c}

/-- A triangle, bundled together with the fact that its three vertices are noncollinear. -/
def Triangle := {s : Set Plane // IsTriangle s}

/-- Regard a bundled triangle as its underlying subset of the plane. -/
instance : Coe Triangle (Set Plane) := ⟨Subtype.val⟩

/-- A finite decomposition of `Ω` into triangles whose distinct interiors overlap only on a
null set. Exact union is used for the closed representatives. -/
structure Triangulation (Ω : Set Plane) where
  /-- The finitely many triangular pieces. -/
  pieces : Finset Triangle
  /-- Distinct triangles intersect only on a null set. -/
  nullOverlap : ∀ t₁ ∈ pieces, ∀ t₂ ∈ pieces, t₁ ≠ t₂ →
    volume ((t₁ : Set Plane) ∩ (t₂ : Set Plane)) = 0
  /-- The pieces have union exactly `Ω`. -/
  sUnion_eq : (⋃ t ∈ pieces, (t : Set Plane)) = Ω

/-- A planar set is polygonal when it can be written as a finite union of nondegenerate
triangles, with overlaps allowed only along null boundaries. -/
def Polygonal (Ω : Set Plane) : Prop :=
  Nonempty (Triangulation Ω)

/-! ## 3. Rational polygonal tiles -/

/-- A point of the plane whose two coordinates are rational numbers. -/
def IsRationalPoint (z : Plane) : Prop :=
  ∃ x y : ℚ, z.re = x ∧ z.im = y

/-- A triangle is rational when it admits three noncollinear rational vertices. -/
def IsRationalTriangle (t : Triangle) : Prop :=
  ∃ a b c : Plane,
    IsRationalPoint a ∧ IsRationalPoint b ∧ IsRationalPoint c ∧
      twiceSignedArea a b c ≠ 0 ∧ (t : Set Plane) = convexHull ℝ {a, b, c}

/-- A triangle bundled together with a rational choice of its vertices. -/
def RationalTriangle := {t : Triangle // IsRationalTriangle t}

/-- A triangulation all of whose triangular pieces are rational. -/
structure RationalTriangulation (Ω : Set Plane) extends Triangulation Ω where
  /-- Every triangle in the decomposition has rational vertices. -/
  rational : ∀ t ∈ pieces, IsRationalTriangle t

/-- A nonempty planar set is a rational polygon when it has a finite triangulation into rational
triangles. -/
def RationalPolygon (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ Nonempty (RationalTriangulation Ω)

end DeDiosGreenfeldComparator

namespace DeDiosGreenfeldComparator

namespace ProductionBridge

/-! ## Polygonal geometry -/

/-- Forget the proof bundled with a comparator triangle. -/
private def triangleEmbedding : Triangle ↪ Set Plane where
  toFun := Subtype.val
  inj' := Subtype.val_injective

@[simp]
private theorem triangleEmbedding_apply (t : Triangle) :
    triangleEmbedding t = (t : Set Plane) :=
  rfl

/-- Turn a comparator triangulation into the production library's triangulation structure. -/
def toProductionTriangulation {Ω : Set Plane} (τ : Triangulation Ω) :
    Tiling.Triangulation Ω where
  pieces := τ.pieces.map triangleEmbedding
  isTriangle := by
    intro t ht
    rw [Finset.mem_map] at ht
    obtain ⟨triangle, -, rfl⟩ := ht
    change Tiling.IsTriangle (triangle : Set Plane)
    simpa [IsTriangle, twiceSignedArea, Tiling.IsTriangle, Tiling.twiceSignedArea] using
      triangle.property
  pairwiseAEDisjoint := by
    intro s hs t ht hst
    change s ∈ τ.pieces.map triangleEmbedding at hs
    change t ∈ τ.pieces.map triangleEmbedding at ht
    rw [Finset.mem_map] at hs ht
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨t', ht', rfl⟩ := ht
    apply τ.nullOverlap s' hs' t' ht'
    intro hst'
    exact hst (congrArg Subtype.val hst')
  sUnion_eq :=
    calc
      ⋃₀ ((τ.pieces.map triangleEmbedding : Finset (Set Plane)) : Set (Set Plane)) =
          ⋃ t ∈ τ.pieces, (t : Set Plane) := by
            apply Set.Subset.antisymm
            · intro x hx
              obtain ⟨s, hs, hxs⟩ := Set.mem_sUnion.mp hx
              change s ∈ τ.pieces.map triangleEmbedding at hs
              obtain ⟨triangle, htriangle, rfl⟩ := Finset.mem_map.mp hs
              exact Set.mem_iUnion.mpr ⟨triangle,
                Set.mem_iUnion.mpr ⟨htriangle, hxs⟩⟩
            · intro x hx
              obtain ⟨triangle, hx⟩ := Set.mem_iUnion.mp hx
              obtain ⟨htriangle, hx⟩ := Set.mem_iUnion.mp hx
              apply Set.mem_sUnion.mpr
              refine ⟨(triangle : Set Plane), ?_, hx⟩
              change (triangle : Set Plane) ∈ τ.pieces.map triangleEmbedding
              exact Finset.mem_map.mpr ⟨triangle, htriangle, rfl⟩
      _ = Ω := τ.sUnion_eq

/-- Bundle a production triangle with its proof of nondegeneracy. -/
private def productionTriangle {Ω : Set Plane} (τ : Tiling.Triangulation Ω)
    (t : {s // s ∈ τ.pieces}) : Triangle :=
  ⟨t.1, by
    simpa [IsTriangle, twiceSignedArea, Tiling.IsTriangle, Tiling.twiceSignedArea] using
      τ.isTriangle t.1 t.2⟩

@[simp]
private theorem productionTriangle_carrier {Ω : Set Plane} (τ : Tiling.Triangulation Ω)
    (t : {s // s ∈ τ.pieces}) :
    (productionTriangle τ t : Set Plane) = t.1 :=
  rfl

/-- The preceding bundling operation is injective because it does not change the carrier. -/
private def productionTriangleEmbedding {Ω : Set Plane} (τ : Tiling.Triangulation Ω) :
    {s // s ∈ τ.pieces} ↪ Triangle where
  toFun := productionTriangle τ
  inj' := by
    intro s t hst
    apply Subtype.ext
    exact congrArg (fun triangle : Triangle ↦ (triangle : Set Plane)) hst

/-- Read a production triangulation using the comparator's independent structure. -/
def ofProductionTriangulation {Ω : Set Plane} (τ : Tiling.Triangulation Ω) :
    Triangulation Ω where
  pieces := τ.pieces.attach.map (productionTriangleEmbedding τ)
  nullOverlap := by
    intro s hs t ht hst
    rw [Finset.mem_map] at hs ht
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨t', ht', rfl⟩ := ht
    apply τ.pairwiseAEDisjoint s'.property t'.property
    intro hst'
    apply hst
    apply Subtype.ext
    exact hst'
  sUnion_eq :=
    calc
      (⋃ t ∈ τ.pieces.attach.map (productionTriangleEmbedding τ), (t : Set Plane)) =
          ⋃₀ (τ.pieces : Set (Set Plane)) := by
            apply Set.Subset.antisymm
            · intro x hx
              obtain ⟨triangle, hx⟩ := Set.mem_iUnion.mp hx
              obtain ⟨htriangle, hx⟩ := Set.mem_iUnion.mp hx
              obtain ⟨s, -, hst⟩ := Finset.mem_map.mp htriangle
              subst triangle
              exact Set.mem_sUnion.mpr ⟨s.1, s.2, hx⟩
            · intro x hx
              obtain ⟨s, hs, hxs⟩ := Set.mem_sUnion.mp hx
              change s ∈ τ.pieces at hs
              let triangle : {s // s ∈ τ.pieces} := ⟨s, hs⟩
              apply Set.mem_iUnion.mpr
              refine ⟨productionTriangle τ triangle, Set.mem_iUnion.mpr ⟨?_, hxs⟩⟩
              exact Finset.mem_map.mpr ⟨triangle, by simp, rfl⟩
      _ = Ω := τ.sUnion_eq

/-! ## Rational vertices -/

/-- A displayed rational-vertex presentation of one bundled triangle. -/
private structure RationalVertices (t : Triangle) where
  a : Plane
  b : Plane
  c : Plane
  rational_a : IsRationalPoint a
  rational_b : IsRationalPoint b
  rational_c : IsRationalPoint c
  nondegenerate : twiceSignedArea a b c ≠ 0
  carrier_eq : (t : Set Plane) = convexHull ℝ {a, b, c}

/-- Choose the three rational vertices certified by a rational triangulation. -/
private noncomputable def chosenRationalVertices {Ω : Set Plane}
    (τ : RationalTriangulation Ω) (t : {t // t ∈ τ.pieces}) : RationalVertices t.1 :=
  Classical.choice (by
    obtain ⟨a, b, c, ha, hb, hc, hnondegenerate, hcarrier⟩ := τ.rational t.1 t.2
    exact ⟨⟨a, b, c, ha, hb, hc, hnondegenerate, hcarrier⟩⟩)

/-- The finite set of all displayed vertices in a rational triangulation. -/
private noncomputable def vertexCandidates {Ω : Set Plane} (τ : RationalTriangulation Ω) :
    Finset Plane := by
  classical
  exact τ.pieces.attach.biUnion fun t ↦
    {(chosenRationalVertices τ t).a, (chosenRationalVertices τ t).b,
      (chosenRationalVertices τ t).c}

/-- Every displayed vertex of a rational triangulation has rational coordinates. -/
private theorem rationalPoint_of_mem_vertexCandidates {Ω : Set Plane}
    (τ : RationalTriangulation Ω) {x : Plane} (hx : x ∈ vertexCandidates τ) :
    IsRationalPoint x := by
  classical
  rw [vertexCandidates, Finset.mem_biUnion] at hx
  obtain ⟨t, -, hx⟩ := hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact (chosenRationalVertices τ t).rational_a
  · exact (chosenRationalVertices τ t).rational_b
  · exact (chosenRationalVertices τ t).rational_c

/-- Every triangulation-independent production vertex is one of the displayed rational vertices
of any rational triangulation. -/
private theorem vertexSet_subset_vertexCandidates {Ω : Set Plane}
    (τ : RationalTriangulation Ω) :
    Tiling.vertexSet Ω ⊆ vertexCandidates τ := by
  classical
  intro x hx
  obtain ⟨s, hs, hxs⟩ := hx (toProductionTriangulation τ.toTriangulation)
  change s ∈ τ.pieces.map triangleEmbedding at hs
  obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
  let t' : {t // t ∈ τ.pieces} := ⟨t, ht⟩
  have hxvertices :
      x ∈ ({(chosenRationalVertices τ t').a, (chosenRationalVertices τ t').b,
        (chosenRationalVertices τ t').c} : Set Plane) := by
    apply extremePoints_convexHull_subset (𝕜 := ℝ)
    rw [← (chosenRationalVertices τ t').carrier_eq]
    exact hxs
  change x ∈ vertexCandidates τ
  rw [vertexCandidates, Finset.mem_biUnion]
  refine ⟨t', by simp [t'], ?_⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] using hxvertices

/-- A finite collection of rational points admits one positive denominator which clears every
coordinate simultaneously. -/
private theorem exists_commonDenominator (V : Finset Plane)
    (hV : ∀ v ∈ V, IsRationalPoint v) :
    ∃ denominator : ℕ, 0 < denominator ∧
      ∀ v ∈ V, Tiling.RationalPolygonal.IsIntegerPoint ((denominator : ℝ) • v) := by
  classical
  have hrat : ∀ v : {v // v ∈ V}, ∃ x y : ℚ, v.1.re = x ∧ v.1.im = y :=
    fun v ↦ hV v.1 v.2
  choose x y hxy using hrat
  let denominator := V.attach.lcm fun v ↦ Nat.lcm (x v).den (y v).den
  refine ⟨denominator, ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    apply Finset.lcm_ne_zero_iff.mpr
    intro v _hv
    exact Nat.lcm_ne_zero (Rat.den_nz (x v)) (Rat.den_nz (y v))
  · intro v hv
    let v' : {v // v ∈ V} := ⟨v, hv⟩
    have hxdiv : (x v').den ∣ denominator :=
      dvd_trans (Nat.dvd_lcm_left _ _)
        (Finset.dvd_lcm (f := fun w ↦ Nat.lcm (x w).den (y w).den) (by simp [v']))
    have hydiv : (y v').den ∣ denominator :=
      dvd_trans (Nat.dvd_lcm_right _ _)
        (Finset.dvd_lcm (f := fun w ↦ Nat.lcm (x w).den (y w).den) (by simp [v']))
    apply Tiling.RationalPolygonal.mem_integerLattice_iff.mpr
    refine ⟨![Tiling.RationalPolygonal.Raw.scaledCoordinate denominator (x v'),
      Tiling.RationalPolygonal.Raw.scaledCoordinate denominator (y v')], ?_⟩
    apply Complex.ext
    · simp only [Tiling.RationalPolygonal.integerPoint_re, Complex.smul_re]
      change (Tiling.RationalPolygonal.Raw.scaledCoordinate denominator (x v') : ℝ) =
        (denominator : ℝ) * v.re
      rw [Tiling.RationalPolygonal.Raw.scaledCoordinate_cast hxdiv, ← (hxy v').1]
    · simp only [Tiling.RationalPolygonal.integerPoint_im, Complex.smul_im]
      change (Tiling.RationalPolygonal.Raw.scaledCoordinate denominator (y v') : ℝ) =
        (denominator : ℝ) * v.im
      rw [Tiling.RationalPolygonal.Raw.scaledCoordinate_cast hydiv, ← (hxy v').2]

/-- Every bundled triangle is compact. -/
private theorem isCompact_triangle (t : Triangle) : IsCompact (t : Set Plane) := by
  obtain ⟨a, b, c, -, hcarrier⟩ := t.property
  rw [hcarrier]
  exact (by simp : ({a, b, c} : Set Plane).Finite).isCompact_convexHull ℝ

/-- Every nonempty finitely triangulated planar set has a vertex which appears in every
triangulation. A global extreme point supplies such a vertex. -/
private theorem vertexSet_nonempty_of_triangulation {Ω : Set Plane}
    (τ : Triangulation Ω) (hΩ : Ω.Nonempty) :
    (Tiling.vertexSet Ω).Nonempty := by
  have hcompact : IsCompact Ω := by
    rw [← τ.sUnion_eq]
    exact τ.pieces.isCompact_biUnion fun t _ht ↦ isCompact_triangle t
  obtain ⟨anchor, hanchorExtreme⟩ := hcompact.extremePoints_nonempty hΩ
  refine ⟨anchor, ?_⟩
  intro σ
  have hanchorUnion : anchor ∈ ⋃₀ (σ.pieces : Set (Set Plane)) := by
    rw [σ.sUnion_eq]
    exact extremePoints_subset hanchorExtreme
  obtain ⟨s, hs, hanchorS⟩ := Set.mem_sUnion.mp hanchorUnion
  refine ⟨s, hs, ?_⟩
  apply isExtreme_singleton.mp
  apply (isExtreme_singleton.mpr hanchorExtreme).mono
  · intro x hx
    rw [← σ.sUnion_eq]
    exact Set.mem_sUnion_of_mem hx hs
  · simpa only [Set.singleton_subset_iff] using hanchorS

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
    apply hT.2.1 p.1 hp q.1 hq
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

/-- The production library and the challenge use the same direct mathematical formulation of
double periodicity. -/
theorem periodic_of_production {A : Set Plane}
    (hA : Tiling.RationalPolygonal.DoublyPeriodic A) : Periodic A := by
  simpa only [Periodic, PeriodicBy, Tiling.RationalPolygonal.DoublyPeriodic,
    Tiling.RationalPolygonal.SetPeriodicBy] using hA

/-! ## The theorem bridge -/

/-- A rational triangulation supplies the production library's internal common-denominator
presentation. The common denominator and intrinsic anchor are derived here rather than exposed in
the challenge statement. -/
theorem exists_productionRegion {Ω : Set Plane} (hΩ : RationalPolygon Ω) :
    ∃ K : Tiling.RationalPolygonal.RationalPolygonalRegion, K.support = Ω := by
  classical
  obtain ⟨hnonempty, ⟨τ⟩⟩ := hΩ
  have hvertexSubset := vertexSet_subset_vertexCandidates τ
  have hcandidateRational : ∀ v ∈ vertexCandidates τ, IsRationalPoint v :=
    fun _v hv ↦ rationalPoint_of_mem_vertexCandidates τ hv
  obtain ⟨denominator, hdenominator, hclears⟩ :=
    exists_commonDenominator (vertexCandidates τ) hcandidateRational
  obtain ⟨anchor, hanchor⟩ :=
    vertexSet_nonempty_of_triangulation τ.toTriangulation hnonempty
  refine ⟨
    { support := Ω
      isPolygonal := ⟨toProductionTriangulation τ.toTriangulation⟩
      nonempty := hnonempty
      anchor := anchor
      anchor_mem_vertex := hanchor
      denominator := denominator
      denominator_pos := hdenominator
      vertex_integral := by
        intro w hw
        change (denominator : ℝ) • (w - anchor) ∈
          Tiling.RationalPolygonal.integerLattice
        rw [smul_sub]
        exact Tiling.RationalPolygonal.integerLattice.sub_mem
          (hclears w (hvertexSubset hw))
          (hclears anchor (hvertexSubset hanchor)) }, rfl⟩

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
