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

namespace DeDiosPontGrebikGreenfeldMadridComparator

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

/-- A closed triangle, allowing the three vertices to be collinear. -/
def IsTriangle (s : Set Plane) : Prop :=
  ∃ a b c : Plane, s = convexHull ℝ {a, b, c}

/-- A closed triangle bundled as a subset of the plane. -/
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

/-- A planar polygon is a positive-area set which can be written as a finite union of triangles,
with overlaps allowed only along null boundaries. -/
def Polygon (Ω : Set Plane) : Prop :=
  volume Ω ≠ 0 ∧ Nonempty (Triangulation Ω)

/-! ## 3. Rational polygonal tiles -/

/-- A point of the plane whose two coordinates are rational numbers. -/
def IsRationalPoint (z : Plane) : Prop :=
  ∃ x y : ℚ, z.re = x ∧ z.im = y

/-- A triangle is rational when it admits three rational vertices. -/
def IsRationalTriangle (t : Triangle) : Prop :=
  ∃ a b c : Plane,
    IsRationalPoint a ∧ IsRationalPoint b ∧ IsRationalPoint c ∧
      (t : Set Plane) = convexHull ℝ {a, b, c}

/-- A triangle bundled together with a rational choice of its vertices. -/
def RationalTriangle := {t : Triangle // IsRationalTriangle t}

/-- A triangulation all of whose triangular pieces are rational. -/
structure RationalTriangulation (Ω : Set Plane) extends Triangulation Ω where
  /-- Every triangle in the decomposition has rational vertices. -/
  rational : ∀ t ∈ pieces, IsRationalTriangle t

/-- A rational polygon is a polygon whose triangulation can be chosen with rational vertices.
The positive-area requirement belongs to `Polygon`; this definition adds only rationality. -/
def RationalPolygon (Ω : Set Plane) : Prop :=
  Polygon Ω ∧ Nonempty (RationalTriangulation Ω)

end DeDiosPontGrebikGreenfeldMadridComparator

namespace DeDiosPontGrebikGreenfeldMadridComparator

namespace ProductionBridge

/-! ## Polygonal geometry and rational vertices -/

/-- A displayed rational-vertex presentation of one bundled triangle. -/
private structure RationalVertices (t : Triangle) where
  a : Plane
  b : Plane
  c : Plane
  rational_a : IsRationalPoint a
  rational_b : IsRationalPoint b
  rational_c : IsRationalPoint c
  carrier_eq : (t : Set Plane) = convexHull ℝ {a, b, c}

/-- Choose the three rational vertices certified by a rational triangulation. -/
private noncomputable def chosenRationalVertices {Ω : Set Plane}
    (τ : RationalTriangulation Ω) (t : {t // t ∈ τ.pieces}) : RationalVertices t.1 :=
  Classical.choice (by
    obtain ⟨a, b, c, ha, hb, hc, hcarrier⟩ := τ.rational t.1 t.2
    exact ⟨⟨a, b, c, ha, hb, hc, hcarrier⟩⟩)

/-- Two planar vectors are linearly independent exactly when their coordinate determinant is
nonzero. This coordinate lemma belongs to the production bridge, not the challenge statement. -/
private theorem linearIndependent_pair_iff_det_ne_zero (u v : Plane) :
    LinearIndependent ℝ ![u, v] ↔ u.re * v.im - u.im * v.re ≠ 0 := by
  constructor
  · intro hlinear
    rw [linearIndependent_fin2] at hlinear
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hlinear
    obtain ⟨hv, hnotMultiple⟩ := hlinear
    intro hdet
    by_cases hre : v.re = 0
    · have him : v.im ≠ 0 := by
        intro him
        apply hv
        apply Complex.ext <;> simp [hre, him]
      have hure : u.re = 0 := by
        have hdet' := hdet
        rw [hre, mul_zero, sub_zero] at hdet'
        exact (mul_eq_zero.mp hdet').resolve_right him
      apply hnotMultiple (u.im / v.im)
      apply Complex.ext
      · simp [hre, hure]
      · simp [div_mul_cancel₀ _ him]
    · apply hnotMultiple (u.re / v.re)
      apply Complex.ext
      · simp [div_mul_cancel₀ _ hre]
      · simp only [Complex.smul_im, smul_eq_mul]
        rw [div_mul_eq_mul_div, div_eq_iff hre]
        exact sub_eq_zero.mp hdet
  · intro hdet
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · intro hv
      subst v
      exact hdet (by simp)
    · intro r hur
      apply hdet
      rw [← hur]
      simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
      ring

/-- The invariant and coordinate formulations of nondegeneracy agree. -/
private theorem linearIndependent_pair_iff_production_area_ne_zero (a b c : Plane) :
    LinearIndependent ℝ ![b - a, c - a] ↔
      Tiling.twiceSignedArea a b c ≠ 0 := by
  simpa only [Tiling.twiceSignedArea, Complex.sub_re, Complex.sub_im] using
    linearIndependent_pair_iff_det_ne_zero (b - a) (c - a)

/-- The genuinely two-dimensional pieces of a rational triangulation. -/
private noncomputable def nondegeneratePieces {Ω : Set Plane} (τ : RationalTriangulation Ω) :
    Finset {t // t ∈ τ.pieces} := by
  classical
  exact τ.pieces.attach.filter fun t ↦
    LinearIndependent ℝ
      ![(chosenRationalVertices τ t).b - (chosenRationalVertices τ t).a,
        (chosenRationalVertices τ t).c - (chosenRationalVertices τ t).a]

/-- The union of the two-dimensional pieces; degenerate pieces have been discarded. -/
private noncomputable def essentialSupport {Ω : Set Plane} (τ : RationalTriangulation Ω) :
    Set Plane :=
  ⋃ t ∈ nondegeneratePieces τ, (t.1 : Set Plane)

/-- Forget both proof layers and retain the carrier of a triangulation piece. -/
private def attachedTriangleCarrierEmbedding {Ω : Set Plane} (τ : RationalTriangulation Ω) :
    {t // t ∈ τ.pieces} ↪ Set Plane where
  toFun t := (t.1 : Set Plane)
  inj' := by
    intro s t hst
    apply Subtype.ext
    apply Subtype.ext
    exact hst

/-- The nondegenerate pieces form a production-library triangulation of the essential support. -/
private noncomputable def essentialProductionTriangulation {Ω : Set Plane}
    (τ : RationalTriangulation Ω) : Tiling.Triangulation (essentialSupport τ) := by
  classical
  refine
    { pieces := (nondegeneratePieces τ).map (attachedTriangleCarrierEmbedding τ)
      isTriangle := ?_
      pairwiseAEDisjoint := ?_
      sUnion_eq := ?_ }
  · intro s hs
    rw [Finset.mem_map] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have hlinear : LinearIndependent ℝ
        ![(chosenRationalVertices τ t).b - (chosenRationalVertices τ t).a,
          (chosenRationalVertices τ t).c - (chosenRationalVertices τ t).a] :=
      (Finset.mem_filter.mp ht).2
    refine ⟨(chosenRationalVertices τ t).a, (chosenRationalVertices τ t).b,
      (chosenRationalVertices τ t).c,
      (linearIndependent_pair_iff_production_area_ne_zero _ _ _).mp hlinear, ?_⟩
    exact (chosenRationalVertices τ t).carrier_eq
  · intro s hs t ht hst
    change s ∈ (nondegeneratePieces τ).map (attachedTriangleCarrierEmbedding τ) at hs
    change t ∈ (nondegeneratePieces τ).map (attachedTriangleCarrierEmbedding τ) at ht
    rw [Finset.mem_map] at hs ht
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨t', ht', rfl⟩ := ht
    apply τ.nullOverlap s'.1 s'.2 t'.1 t'.2
    intro hst'
    apply hst
    exact congrArg (fun triangle : Triangle ↦ (triangle : Set Plane)) hst'
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := Set.mem_sUnion.mp hx
      change s ∈ (nondegeneratePieces τ).map (attachedTriangleCarrierEmbedding τ) at hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, hxs⟩⟩
    · intro x hx
      obtain ⟨t, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨ht, hx⟩ := Set.mem_iUnion.mp hx
      apply Set.mem_sUnion.mpr
      refine ⟨(t.1 : Set Plane), ?_, hx⟩
      change (t.1 : Set Plane) ∈
        (nondegeneratePieces τ).map (attachedTriangleCarrierEmbedding τ)
      exact Finset.mem_map.mpr ⟨t, ht, rfl⟩

/-- Three points are affinely independent exactly when the two differences based at the first
point are linearly independent. -/
private theorem affineIndependent_three_iff_linearIndependent_pair (a b c : Plane) :
    AffineIndependent ℝ ![a, b, c] ↔ LinearIndependent ℝ ![b - a, c - a] := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ ![a, b, c] 0]
  exact (linearIndependent_equiv' (R := ℝ)
    (finSuccAboveEquiv (0 : Fin 3)) (by
      funext i
      fin_cases i <;> rfl)).symm

/-- A degenerate displayed triangle is null.  This is why the expository `Triangle` type may
allow collinear vertices: such pieces do not affect any almost-everywhere tiling statement. -/
private theorem volume_triangle_eq_zero_of_degenerate {Ω : Set Plane}
    (τ : RationalTriangulation Ω) (t : {t // t ∈ τ.pieces})
    (hdegenerate : ¬ LinearIndependent ℝ
      ![(chosenRationalVertices τ t).b - (chosenRationalVertices τ t).a,
        (chosenRationalVertices τ t).c - (chosenRationalVertices τ t).a]) :
    volume (t.1 : Set Plane) = 0 := by
  rw [(chosenRationalVertices τ t).carrier_eq]
  have haffine : ¬ AffineIndependent ℝ
      ![(chosenRationalVertices τ t).a, (chosenRationalVertices τ t).b,
        (chosenRationalVertices τ t).c] := fun hindependent ↦
    hdegenerate ((affineIndependent_three_iff_linearIndependent_pair _ _ _).mp hindependent)
  have hcollinear : Collinear ℝ
      ({(chosenRationalVertices τ t).a, (chosenRationalVertices τ t).b,
        (chosenRationalVertices τ t).c} : Set Plane) :=
    collinear_iff_not_affineIndependent_set.mpr haffine
  apply measure_mono_null (convexHull_subset_affineSpan _)
  apply Measure.addHaar_affineSubspace
  intro hspan
  have hdim := hcollinear.finrank_le_one
  rw [← direction_affineSpan, hspan, AffineSubspace.direction_top, finrank_top,
    Complex.finrank_real_complex] at hdim
  omega

/-- Discarding degenerate pieces changes a rational polygon only on a null set. -/
private theorem support_ae_eq_essentialSupport {Ω : Set Plane}
    (τ : RationalTriangulation Ω) :
    Ω =ᵐ[volume] essentialSupport τ := by
  classical
  have hdegenerateAbsent : ∀ᵐ x ∂volume, ∀ t : {t // t ∈ τ.pieces},
      ¬ LinearIndependent ℝ
          ![(chosenRationalVertices τ t).b - (chosenRationalVertices τ t).a,
            (chosenRationalVertices τ t).c - (chosenRationalVertices τ t).a] →
        x ∉ (t.1 : Set Plane) := by
    apply ae_all_iff.mpr
    intro t
    by_cases hlinear : LinearIndependent ℝ
        ![(chosenRationalVertices τ t).b - (chosenRationalVertices τ t).a,
          (chosenRationalVertices τ t).c - (chosenRationalVertices τ t).a]
    · exact Filter.Eventually.of_forall fun _x hnotLinear ↦ (hnotLinear hlinear).elim
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp
        (volume_triangle_eq_zero_of_degenerate τ t hlinear)] with x hx
      exact fun _hnotLinear ↦ hx
  filter_upwards [hdegenerateAbsent] with x hx
  apply propext
  constructor
  · intro hxΩ
    rw [← τ.sUnion_eq] at hxΩ
    obtain ⟨t, hxΩ⟩ := Set.mem_iUnion.mp hxΩ
    obtain ⟨ht, hxt⟩ := Set.mem_iUnion.mp hxΩ
    let t' : {t // t ∈ τ.pieces} := ⟨t, ht⟩
    by_cases hlinear : LinearIndependent ℝ
        ![(chosenRationalVertices τ t').b - (chosenRationalVertices τ t').a,
          (chosenRationalVertices τ t').c - (chosenRationalVertices τ t').a]
    · apply Set.mem_iUnion.mpr
      refine ⟨t', Set.mem_iUnion.mpr ⟨?_, hxt⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hlinear⟩
    · exact (hx t' hlinear hxt).elim
  · intro hxEssential
    rw [← τ.sUnion_eq]
    obtain ⟨t, hxEssential⟩ := Set.mem_iUnion.mp hxEssential
    obtain ⟨_ht, hxt⟩ := Set.mem_iUnion.mp hxEssential
    exact Set.mem_iUnion.mpr ⟨t.1, Set.mem_iUnion.mpr ⟨t.2, hxt⟩⟩

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
    Tiling.vertexSet (essentialSupport τ) ⊆ vertexCandidates τ := by
  classical
  intro x hx
  obtain ⟨s, hs, hxs⟩ := hx (essentialProductionTriangulation τ)
  change s ∈ (nondegeneratePieces τ).map (attachedTriangleCarrierEmbedding τ) at hs
  obtain ⟨t, _ht, rfl⟩ := Finset.mem_map.mp hs
  have hxvertices :
      x ∈ ({(chosenRationalVertices τ t).a, (chosenRationalVertices τ t).b,
        (chosenRationalVertices τ t).c} : Set Plane) := by
    apply extremePoints_convexHull_subset (𝕜 := ℝ)
    rw [← (chosenRationalVertices τ t).carrier_eq]
    exact hxs
  change x ∈ vertexCandidates τ
  rw [vertexCandidates, Finset.mem_biUnion]
  refine ⟨t, by simp, ?_⟩
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
  obtain ⟨a, b, c, hcarrier⟩ := t.property
  rw [hcarrier]
  exact (by simp : ({a, b, c} : Set Plane).Finite).isCompact_convexHull ℝ

/-- Every nonempty compact planar set has a vertex which appears in every production-library
triangulation. A global extreme point supplies such a vertex. -/
private theorem vertexSet_nonempty_of_compact {Ω : Set Plane}
    (hcompact : IsCompact Ω) (hΩ : Ω.Nonempty) :
    (Tiling.vertexSet Ω).Nonempty := by
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

/-- Translating two almost-everywhere equal tiles by the same vector preserves their
almost-everywhere equality. -/
private theorem translate_ae_eq_translate {Ω Ω' : Set Plane}
    (hΩ : Ω =ᵐ[volume] Ω') (t : Plane) :
    t +ᵥ Ω =ᵐ[volume] t +ᵥ Ω' :=
  (quasiMeasurePreserving_add_left volume (-t)).vadd_ae_eq_of_ae_eq t hΩ

/-- Replacing a tile by an almost-everywhere equal set preserves a direct monotile tiling. -/
private theorem tiling_of_ae_eq {Ω Ω' T : Set Plane}
    (hΩ : Ω =ᵐ[volume] Ω') : Tiling Ω T → Tiling Ω' T := by
  intro hT
  refine ⟨hT.1, ?_, ?_⟩
  · intro t₁ ht₁ t₂ ht₂ hne
    have hinter :=
      ae_eq_set_inter (translate_ae_eq_translate hΩ t₁)
        (translate_ae_eq_translate hΩ t₂)
    exact (measure_congr hinter).symm.trans (hT.2.1 t₁ ht₁ t₂ ht₂ hne)
  · have htranslations : ∀ᵐ x ∂volume, ∀ t ∈ T,
        x ∈ t +ᵥ Ω ↔ x ∈ t +ᵥ Ω' := by
      apply (ae_ball_iff hT.1).mpr
      intro t _ht
      filter_upwards [translate_ae_eq_translate hΩ t] with x hx
      exact iff_of_eq hx
    filter_upwards [hT.2.2, htranslations] with x hxCover hxTranslations
    obtain ⟨t, ht, hxt⟩ := hxCover
    exact ⟨t, ht, (hxTranslations t ht).mp hxt⟩

/-- The direct monotile tiling relation depends only on the tile up to a null set. -/
private theorem tiling_congr_of_ae_eq {Ω Ω' T : Set Plane}
    (hΩ : Ω =ᵐ[volume] Ω') : Tiling Ω T ↔ Tiling Ω' T :=
  ⟨tiling_of_ae_eq hΩ, tiling_of_ae_eq hΩ.symm⟩

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
    ∃ K : Tiling.RationalPolygonal.RationalPolygonalRegion,
      Ω =ᵐ[volume] K.support := by
  classical
  obtain ⟨⟨hvolume, _htriangulated⟩, ⟨τ⟩⟩ := hΩ
  have hsupportAE : Ω =ᵐ[volume] essentialSupport τ :=
    support_ae_eq_essentialSupport τ
  have hessentialVolume : volume (essentialSupport τ) ≠ 0 := by
    intro hzero
    apply hvolume
    exact (measure_congr hsupportAE).trans hzero
  have hessentialNonempty : (essentialSupport τ).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    apply hessentialVolume
    rw [hempty, measure_empty]
  have hessentialCompact : IsCompact (essentialSupport τ) := by
    rw [essentialSupport]
    exact (nondegeneratePieces τ).isCompact_biUnion fun t _ht ↦ isCompact_triangle t.1
  have hvertexSubset := vertexSet_subset_vertexCandidates τ
  have hcandidateRational : ∀ v ∈ vertexCandidates τ, IsRationalPoint v :=
    fun _v hv ↦ rationalPoint_of_mem_vertexCandidates τ hv
  obtain ⟨denominator, hdenominator, hclears⟩ :=
    exists_commonDenominator (vertexCandidates τ) hcandidateRational
  obtain ⟨anchor, hanchor⟩ :=
    vertexSet_nonempty_of_compact hessentialCompact hessentialNonempty
  refine ⟨
    { support := essentialSupport τ
      isPolygonal := ⟨essentialProductionTriangulation τ⟩
      nonempty := hessentialNonempty
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
          (hclears anchor (hvertexSubset hanchor)) }, hsupportAE⟩

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
  have hT' : Tiling K.support T := (tiling_congr_of_ae_eq hK).mp hT
  have hproductionTileable :
      ∃ T : Set Plane, K.toPolygonalRegion.Tiles T :=
    ⟨T, toProductionTiling K.toPolygonalRegion hT'⟩
  obtain ⟨S, hStiles, hSperiodic⟩ :=
    (Tiling.RationalPolygonal.RationalPolygonalRegion.theorem_1_1 K).mp
      hproductionTileable
  refine ⟨S, periodic_of_production hSperiodic, ?_⟩
  exact (tiling_congr_of_ae_eq hK).mpr
    (ofProductionTiling K.toPolygonalRegion hStiles)

end DeDiosPontGrebikGreenfeldMadridComparator
