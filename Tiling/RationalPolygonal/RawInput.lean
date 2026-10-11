import Tiling.RationalPolygonal.Basic

set_option linter.style.header false

/-!
# Raw rational polygonal input

This module turns a finite list of rational triangle coordinates into the semantic
`RationalPolygonalRegion` used by the continuous tiling development. The runtime data contains
only rational coordinates. Geometric well-formedness remains in proof-only validity fields.

The executable normalization chooses an anchor from the input list, takes the least common
multiple of all coordinate denominators, and produces a finite code of integer triangles. The
main semantic theorem identifies the normalized support exactly with the union of the convex
hulls of those normalized integer triangles.
-/

open Function MeasureTheory Set
open scoped Pointwise

namespace Tiling.RationalPolygonal.Raw

/-- A point whose two coordinates are executable rational numbers. -/
structure QPoint where
  /-- Rational horizontal coordinate. -/
  x : ℚ
  /-- Rational vertical coordinate. -/
  y : ℚ
deriving DecidableEq, Repr

namespace QPoint

/-- The real-plane point denoted by a rational coordinate pair. -/
def toPlane (p : QPoint) : Plane :=
  (p.x : ℝ) + (p.y : ℝ) * Complex.I

@[simp]
theorem toPlane_re (p : QPoint) : p.toPlane.re = p.x := by
  simp [toPlane]

@[simp]
theorem toPlane_im (p : QPoint) : p.toPlane.im = p.y := by
  simp [toPlane]

/-- The two rational coordinates of a rational point. -/
def coordinates (p : QPoint) : Finset ℚ :=
  {p.x, p.y}

@[simp]
theorem mem_coordinates_iff {p : QPoint} {q : ℚ} :
    q ∈ p.coordinates ↔ q = p.x ∨ q = p.y := by
  simp [coordinates]

end QPoint

/-- A triangle encoded only by its three rational vertices. -/
structure QTriangle where
  /-- First rational vertex. -/
  a : QPoint
  /-- Second rational vertex. -/
  b : QPoint
  /-- Third rational vertex. -/
  c : QPoint
deriving DecidableEq, Repr

namespace QTriangle

/-- The finite set of encoded vertices of a rational triangle. -/
def vertices (t : QTriangle) : Finset QPoint :=
  {t.a, t.b, t.c}

/-- The closed convex triangle denoted by a rational triangle code. -/
def carrier (t : QTriangle) : Set Plane :=
  convexHull ℝ {t.a.toPlane, t.b.toPlane, t.c.toPlane}

/-- Nondegeneracy of a rational triangle code. -/
def Nondegenerate (t : QTriangle) : Prop :=
  twiceSignedArea t.a.toPlane t.b.toPlane t.c.toPlane ≠ 0

/-- A nondegenerate rational triangle code denotes a geometric triangle. -/
theorem isTriangle {t : QTriangle} (ht : t.Nondegenerate) : IsTriangle t.carrier := by
  exact ⟨t.a.toPlane, t.b.toPlane, t.c.toPlane, ht, rfl⟩

end QTriangle

/-- Executable input consisting only of a finite collection of rational triangle coordinates. -/
structure Code where
  /-- Finite list of rational triangle coordinates. -/
  triangles : List QTriangle
deriving DecidableEq, Repr

namespace Code

/-- The finset of triangles occurring in the executable list code. -/
def triangleFinset (C : Code) : Finset QTriangle :=
  C.triangles.toFinset

/-- The closed polygonal support denoted by a raw finite triangle code. -/
def support (C : Code) : Set Plane :=
  ⋃ t ∈ C.triangleFinset, t.carrier

/-- The finite set of all rational coordinates occurring in a raw code. -/
def coordinates (C : Code) : Finset ℚ :=
  C.triangleFinset.biUnion fun t ↦ t.vertices.biUnion QPoint.coordinates

/-- The executable least-common-multiple denominator of every coordinate in the code. -/
def commonDenominator (C : Code) : ℕ :=
  C.coordinates.lcm Rat.den

/-- Choose the first encoded vertex of the finset-selected triangle. -/
def anchor (C : Code) (hne : C.triangles ≠ []) : QPoint :=
  (C.triangles.head hne).a

/-- Semantic validity of a finite rational triangulation.  All fields are geometric proof
certificates; no raster or tiling-decision certificate occurs here. -/
structure Valid (C : Code) : Prop where
  nonempty : C.triangles ≠ []
  nondegenerate : ∀ t ∈ C.triangleFinset, t.Nondegenerate
  pairwiseAEDisjoint :
    (C.triangleFinset : Set QTriangle).Pairwise (AEDisjoint volume on QTriangle.carrier)
  anchor_mem_vertex : (C.anchor nonempty).toPlane ∈ vertexSet C.support

/-- A raw rational polygonal input: finite rational coordinates together with validity proofs. -/
structure Input where
  /-- Runtime rational-coordinate code. -/
  code : Code
  /-- Proof-only geometric validity certificate for the runtime code. -/
  valid : code.Valid

namespace Input

/-- The executable anchor selected from the input triangulation. -/
def anchor (P : Input) : QPoint :=
  P.code.anchor P.valid.nonempty

/-- The executable common denominator of every input coordinate. -/
def denominator (P : Input) : ℕ :=
  P.code.commonDenominator

/-- The selected anchor triangle belongs to the input code. -/
theorem choose_mem (P : Input) :
    P.code.triangles.head P.valid.nonempty ∈ P.code.triangleFinset := by
  simp only [Code.triangleFinset, List.mem_toFinset]
  exact List.head_mem P.valid.nonempty

/-- Every coordinate of every encoded vertex occurs in the global coordinate finset. -/
theorem coordinate_mem {P : Input} {t : QTriangle} (ht : t ∈ P.code.triangleFinset)
    {p : QPoint} (hp : p ∈ t.vertices) {q : ℚ} (hq : q ∈ p.coordinates) :
    q ∈ P.code.coordinates := by
  exact Finset.mem_biUnion.mpr ⟨t, ht,
    Finset.mem_biUnion.mpr ⟨p, hp, hq⟩⟩

/-- Every encoded coordinate denominator divides the executable common denominator. -/
theorem coordinate_den_dvd {P : Input} {t : QTriangle} (ht : t ∈ P.code.triangleFinset)
    {p : QPoint} (hp : p ∈ t.vertices) {q : ℚ} (hq : q ∈ p.coordinates) :
    q.den ∣ P.denominator := by
  exact Finset.dvd_lcm (P.coordinate_mem ht hp hq)

/-- Both denominators of every encoded vertex divide the executable common denominator. -/
theorem point_den_dvd {P : Input} {t : QTriangle} (ht : t ∈ P.code.triangleFinset)
    {p : QPoint} (hp : p ∈ t.vertices) :
    p.x.den ∣ P.denominator ∧ p.y.den ∣ P.denominator := by
  constructor
  · exact P.coordinate_den_dvd ht hp (by simp [QPoint.coordinates])
  · exact P.coordinate_den_dvd ht hp (by simp [QPoint.coordinates])

/-- Both anchor-coordinate denominators divide the common denominator. -/
theorem anchor_den_dvd (P : Input) :
    P.anchor.x.den ∣ P.denominator ∧ P.anchor.y.den ∣ P.denominator := by
  apply P.point_den_dvd P.choose_mem
  simp [anchor, Code.anchor, QTriangle.vertices]

/-- The executable common denominator is positive for every valid nonempty code. -/
theorem denominator_pos (P : Input) : 0 < P.denominator := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro q hq
  exact q.den_nz

/-- The explicit triangulation of the semantic support supplied by the raw code. -/
noncomputable def triangulation (P : Input) : Triangulation P.code.support where
  pieces := P.code.triangleFinset.image QTriangle.carrier
  isTriangle := by
    intro s hs
    simp only [Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact QTriangle.isTriangle (P.valid.nondegenerate t ht)
  pairwiseAEDisjoint := by
    intro s hs u hu hsu
    simp only [Finset.mem_coe, Finset.mem_image] at hs hu
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨v, hv, rfl⟩ := hu
    apply P.valid.pairwiseAEDisjoint ht hv
    intro htv
    apply hsu
    rw [htv]
  sUnion_eq := by
    ext x
    simp [Code.support]

/-- The semantic polygonal region denoted by a valid raw rational triangulation. -/
noncomputable def polygonalRegion (P : Input) : PolygonalRegion where
  support := P.code.support
  isPolygonal := ⟨P.triangulation⟩
  nonempty := by
    let t := P.code.triangles.head P.valid.nonempty
    have ht : t ∈ P.code.triangleFinset := P.choose_mem
    refine ⟨t.a.toPlane, ?_⟩
    simp only [Code.support, mem_iUnion]
    refine ⟨t, ⟨ht, ?_⟩⟩
    change t.a.toPlane ∈ convexHull ℝ {t.a.toPlane, t.b.toPlane, t.c.toPlane}
    exact subset_convexHull ℝ
      ({t.a.toPlane, t.b.toPlane, t.c.toPlane} : Set Plane) (by simp)

end Input

end Code

/-- An integer coordinate pair produced by normalization. -/
structure ZPoint where
  /-- Integral horizontal coordinate. -/
  x : ℤ
  /-- Integral vertical coordinate. -/
  y : ℤ
deriving DecidableEq, Repr

namespace ZPoint

/-- Embed an integer coordinate pair into the real plane. -/
def toPlane (p : ZPoint) : Plane :=
  (p.x : ℝ) + (p.y : ℝ) * Complex.I

/-- Regard an integer coordinate pair as the project's discrete integer plane. -/
def toIntegerPlane (p : ZPoint) : IntegerPlane :=
  ![p.x, p.y]

@[simp]
theorem integerPoint_toIntegerPlane (p : ZPoint) :
    integerPoint p.toIntegerPlane = p.toPlane := by
  apply Complex.ext <;> simp [toIntegerPlane, toPlane]

end ZPoint

/-- A triangle with integral vertices, produced by executable normalization. -/
structure ZTriangle where
  /-- First integral vertex. -/
  a : ZPoint
  /-- Second integral vertex. -/
  b : ZPoint
  /-- Third integral vertex. -/
  c : ZPoint
deriving DecidableEq, Repr

namespace ZTriangle

/-- The closed convex triangle denoted by an integral triangle. -/
def carrier (t : ZTriangle) : Set Plane :=
  convexHull ℝ {t.a.toPlane, t.b.toPlane, t.c.toPlane}

end ZTriangle

/-- Clear one rational denominator using a supplied common multiple. -/
def scaledCoordinate (D : ℕ) (q : ℚ) : ℤ :=
  q.num * (D / q.den : ℕ)

/-- Clearing a denominator computes the expected real scalar multiple. -/
theorem scaledCoordinate_cast {D : ℕ} {q : ℚ} (hdiv : q.den ∣ D) :
    (scaledCoordinate D q : ℝ) = (D : ℝ) * (q : ℝ) := by
  obtain ⟨k, rfl⟩ := hdiv
  rw [scaledCoordinate, Nat.mul_div_cancel_left k q.den_pos, Rat.cast_def]
  push_cast
  field_simp

namespace Code.Input

/-- Normalize one rational vertex to an integer vertex. -/
def normalizedPoint (P : Input) (p : QPoint) : ZPoint where
  x := scaledCoordinate P.denominator p.x - scaledCoordinate P.denominator P.anchor.x
  y := scaledCoordinate P.denominator p.y - scaledCoordinate P.denominator P.anchor.y

/-- Normalize one rational triangle to an integral triangle. -/
def normalizedTriangle (P : Input) (t : QTriangle) : ZTriangle where
  a := P.normalizedPoint t.a
  b := P.normalizedPoint t.b
  c := P.normalizedPoint t.c

/-- The executable finite integral triangle code obtained by normalization. -/
def normalizedCode (P : Input) : Finset ZTriangle :=
  P.code.triangleFinset.image P.normalizedTriangle

/-- The normalized support represented by the executable integral triangle code. -/
def normalizedCodeSupport (P : Input) : Set Plane :=
  ⋃ t ∈ P.normalizedCode, t.carrier

/-- Normalizing an encoded vertex agrees exactly with affine normalization in the real plane. -/
theorem normalizedPoint_toPlane {P : Input} {t : QTriangle} (ht : t ∈ P.code.triangleFinset)
    {p : QPoint} (hp : p ∈ t.vertices) :
    (P.normalizedPoint p).toPlane =
      (P.denominator : ℝ) • (p.toPlane - P.anchor.toPlane) := by
  have hpdiv := P.point_den_dvd ht hp
  have hadiv := P.anchor_den_dvd
  apply Complex.ext
  · simp only [ZPoint.toPlane, normalizedPoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_im, mul_one, Complex.smul_re,
      Complex.I_re, Complex.sub_re, QPoint.toPlane_re, Int.cast_sub]
    rw [scaledCoordinate_cast hpdiv.1, scaledCoordinate_cast hadiv.1]
    ring
  · simp only [ZPoint.toPlane, normalizedPoint, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.smul_im,
      Complex.sub_im, QPoint.toPlane_im, Int.cast_sub]
    rw [scaledCoordinate_cast hpdiv.2, scaledCoordinate_cast hadiv.2]
    ring

/-- Normalization sends each rational triangle carrier to its integral triangle carrier. -/
theorem normalizedTriangle_carrier {P : Input} {t : QTriangle}
    (ht : t ∈ P.code.triangleFinset) :
    (P.denominator : ℝ) • (-P.anchor.toPlane +ᵥ t.carrier) =
      (P.normalizedTriangle t).carrier := by
  rw [QTriangle.carrier, ← convexHull_vadd, ← convexHull_smul]
  apply congrArg (convexHull ℝ)
  ext x
  simp only [mem_smul_set, mem_vadd_set, Set.mem_insert_iff, Set.mem_singleton_iff,
    normalizedTriangle]
  constructor
  · rintro ⟨y, ⟨z, (rfl | rfl | rfl), rfl⟩, rfl⟩
    · left
      rw [normalizedPoint_toPlane ht (by simp [QTriangle.vertices])]
      simp only [vadd_eq_add]
      congr 1
      abel
    · right; left
      rw [normalizedPoint_toPlane ht (by simp [QTriangle.vertices])]
      simp only [vadd_eq_add]
      congr 1
      abel
    · right; right
      rw [normalizedPoint_toPlane ht (by simp [QTriangle.vertices])]
      simp only [vadd_eq_add]
      congr 1
      abel
  · rintro (rfl | rfl | rfl)
    · refine ⟨-P.anchor.toPlane +ᵥ t.a.toPlane, ⟨t.a.toPlane, by simp, rfl⟩, ?_⟩
      rw [normalizedPoint_toPlane ht (by simp [QTriangle.vertices])]
      simp only [vadd_eq_add]
      congr 1
      abel
    · refine ⟨-P.anchor.toPlane +ᵥ t.b.toPlane, ⟨t.b.toPlane, by simp, rfl⟩, ?_⟩
      rw [normalizedPoint_toPlane ht (by simp [QTriangle.vertices])]
      simp only [vadd_eq_add]
      congr 1
      abel
    · refine ⟨-P.anchor.toPlane +ᵥ t.c.toPlane, ⟨t.c.toPlane, by simp, rfl⟩, ?_⟩
      rw [normalizedPoint_toPlane ht (by simp [QTriangle.vertices])]
      simp only [vadd_eq_add]
      congr 1
      abel

/-- Every normalized encoded vertex is an embedded integer point. -/
theorem normalizedPoint_isInteger {P : Input} {t : QTriangle}
    (ht : t ∈ P.code.triangleFinset) {p : QPoint} (hp : p ∈ t.vertices) :
    IsIntegerPoint ((P.denominator : ℝ) • (p.toPlane - P.anchor.toPlane)) := by
  rw [← P.normalizedPoint_toPlane ht hp]
  rw [IsIntegerPoint, mem_integerLattice_iff]
  exact ⟨(P.normalizedPoint p).toIntegerPlane,
    (P.normalizedPoint p).integerPoint_toIntegerPlane⟩

/-- An intrinsic vertex of the semantic support is one of the explicitly encoded vertices. -/
theorem vertexSet_subset_encodedVertices (P : Input) :
    vertexSet P.code.support ⊆
      {x | ∃ t ∈ P.code.triangleFinset, ∃ p ∈ t.vertices, p.toPlane = x} := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := hx P.triangulation
  change s ∈ P.code.triangleFinset.image QTriangle.carrier at hs
  simp only [Finset.mem_image] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hxvertices : x ∈ ({t.a.toPlane, t.b.toPlane, t.c.toPlane} : Set Plane) :=
    extremePoints_convexHull_subset hxs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxvertices
  rcases hxvertices with hxa | hxb | hxc
  · exact ⟨t, ht, t.a, by simp [QTriangle.vertices], hxa.symm⟩
  · exact ⟨t, ht, t.b, by simp [QTriangle.vertices], hxb.symm⟩
  · exact ⟨t, ht, t.c, by simp [QTriangle.vertices], hxc.symm⟩

/-- The raw finite rational triangulation produces the existing semantic rational-region model. -/
noncomputable def rationalPolygonalRegion (P : Input) : RationalPolygonalRegion where
  toPolygonalRegion := P.polygonalRegion
  anchor := P.anchor.toPlane
  anchor_mem_vertex := P.valid.anchor_mem_vertex
  denominator := P.denominator
  denominator_pos := P.denominator_pos
  vertex_integral := by
    intro w hw
    obtain ⟨t, ht, p, hp, rfl⟩ := P.vertexSet_subset_encodedVertices hw
    exact P.normalizedPoint_isInteger ht hp

@[simp]
theorem rationalPolygonalRegion_support (P : Input) :
    P.rationalPolygonalRegion.support = P.code.support :=
  rfl

/-- The semantic normalized support is exactly the finite union of the normalized integral
triangle convex hulls, indexed by the original code. -/
theorem normalizedSupport_eq_iUnion (P : Input) :
    P.rationalPolygonalRegion.normalizedSupport =
      ⋃ t ∈ P.code.triangleFinset, (P.normalizedTriangle t).carrier := by
  change (P.denominator : ℝ) • (-P.anchor.toPlane +ᵥ P.code.support) = _
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    have hy' : P.anchor.toPlane + y ∈ P.code.support := by
      simpa only [vadd_eq_add, neg_neg, add_assoc, neg_add_cancel_left] using hy
    simp only [Code.support, mem_iUnion] at hy'
    obtain ⟨t, ht, hyt⟩ := hy'
    refine Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, ?_⟩⟩
    rw [← P.normalizedTriangle_carrier ht]
    refine ⟨y, ?_, rfl⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [vadd_eq_add, neg_neg, add_assoc, neg_add_cancel_left] using hyt
  · simp only [mem_iUnion]
    rintro ⟨t, ht, hxt⟩
    rw [← P.normalizedTriangle_carrier ht] at hxt
    obtain ⟨y, hyt, rfl⟩ := hxt
    refine ⟨y, ?_, rfl⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hyt ⊢
    simp only [Code.support, mem_iUnion]
    refine ⟨t, ht, ?_⟩
    simpa only [vadd_eq_add, neg_neg, add_assoc, neg_add_cancel_left] using hyt

/-- The same normalized-support theorem, expressed through the executable finite `ZTriangle`
code rather than through the original rational indexing finset. -/
theorem normalizedSupport_eq_normalizedCodeSupport (P : Input) :
    P.rationalPolygonalRegion.normalizedSupport = P.normalizedCodeSupport := by
  rw [P.normalizedSupport_eq_iUnion]
  ext x
  simp [normalizedCodeSupport, normalizedCode]

end Code.Input

end Tiling.RationalPolygonal.Raw

