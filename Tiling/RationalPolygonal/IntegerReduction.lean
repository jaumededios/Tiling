import Tiling.RationalPolygonal.Basic

set_option linter.style.header false

/-!
# Integer reduction for rational polygonal tilings

This file specializes the finite-family connected-sliding development to one polygonal region.  It
formalizes the vertex-sharing relation from Section 2 of de Dios Pont--Grebík--Greenfeld--Madrid,
proves that a connected tiling by an integer-vertex region has integral translation differences,
and obtains an integer tiling from an arbitrary tiling.
-/

open Filter MeasureTheory Set
open scoped Pointwise

namespace Tiling.RationalPolygonal

namespace PolygonalRegion

/-- Package a monotile translation set as the polygonal prototiling consumed by the sliding API. -/
def polygonalProtoTiling (K : PolygonalRegion) (T : Set Plane) :
    PolygonalProtoTiling Unit where
  prototiles := K.prototileFamily
  placements := K.placements T
  isPolygonal := fun _ ↦ K.isPolygonal

@[simp]
theorem polygonalProtoTiling_prototiles (K : PolygonalRegion) (T : Set Plane) :
    (K.polygonalProtoTiling T).prototiles = K.prototileFamily :=
  rfl

@[simp]
theorem polygonalProtoTiling_placements (K : PolygonalRegion) (T : Set Plane) :
    (K.polygonalProtoTiling T).placements = K.placements T :=
  rfl

/-- Every intrinsic vertex of the region lies in the integer lattice. -/
def HasIntegerVertices (K : PolygonalRegion) : Prop :=
  ∀ v ∈ vertexSet K.support, IsIntegerPoint v

end PolygonalRegion

namespace RationalPolygonalRegion

/-- Clearing the denominator in a rational presentation produces an integer-vertex region. -/
theorem normalizedRegion_hasIntegerVertices (K : RationalPolygonalRegion) :
    PolygonalRegion.HasIntegerVertices K.normalizedRegion :=
  K.normalized_vertex_integral

/-- A normalized placed tile is the common-denominator dilation of the original placed tile. -/
theorem normalized_placedTile (K : RationalPolygonalRegion) (t : Plane) :
    placedTile K.normalizedRegion.prototileFamily
        (K.normalizedTranslation t, ()) =
      (K.denominator : ℝ) •
        placedTile K.toPolygonalRegion.prototileFamily (t, ()) := by
  ext x
  constructor
  · intro hx
    change x ∈ K.normalizedTranslation t +ᵥ K.normalizedSupport at hx
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
    change -K.normalizedTranslation t +ᵥ x ∈
      (K.denominator : ℝ) • (-K.anchor +ᵥ K.support) at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    refine ⟨t + K.anchor + y, ?_, ?_⟩
    · change t + K.anchor + y ∈ t +ᵥ K.support
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      convert hy using 1
      simp only [vadd_eq_add]
      abel
    · have hx_eq : x = K.normalizedTranslation t +
          (K.denominator : ℝ) • y := by
        change (K.denominator : ℝ) • y =
          -K.normalizedTranslation t + x at hyx
        rw [hyx]
        abel
      rw [hx_eq]
      simp only [RationalPolygonalRegion.normalizedTranslation, smul_add]
      module
  · rintro ⟨y, hy, rfl⟩
    change (K.denominator : ℝ) • y ∈
      K.normalizedTranslation t +ᵥ K.normalizedSupport
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change y ∈ t +ᵥ K.support at hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    refine ⟨-K.anchor + y - t, ?_, ?_⟩
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      convert hy using 1
      simp only [vadd_eq_add]
      abel
    · simp only [RationalPolygonalRegion.normalizedTranslation, vadd_eq_add,
        smul_add, smul_sub]
      module

/-- Rational affine normalization transports an almost-everywhere tiling to the normalized
integer-vertex region. -/
theorem normalizedRegion_tiles (K : RationalPolygonalRegion) {T : Set Plane}
    (hT : K.toPolygonalRegion.Tiles T) :
    K.normalizedRegion.Tiles (K.normalizedTranslations T) := by
  have hnormalized_countable : (K.normalizedTranslations T).Countable :=
    hT.countable.image K.normalizedTranslation
  refine ⟨PolygonalRegion.placements_countable K.normalizedRegion
    hnormalized_countable, ?_, ?_⟩
  · rintro p hp q hq hpq
    change p.1 ∈ K.normalizedTranslations T at hp
    change q.1 ∈ K.normalizedTranslations T at hq
    obtain ⟨t, ht, htp⟩ := hp
    obtain ⟨s, hs, hsq⟩ := hq
    let p₀ : Placement Plane Unit := (t, ())
    let q₀ : Placement Plane Unit := (s, ())
    have hp₀ : p₀ ∈ K.toPolygonalRegion.placements T := ht
    have hq₀ : q₀ ∈ K.toPolygonalRegion.placements T := hs
    have hts : t ≠ s := by
      intro hts
      apply hpq
      apply Prod.ext
      · rw [← htp, ← hsq, hts]
      · exact Subsingleton.elim _ _
    have hpq₀ : p₀ ≠ q₀ := by
      intro hpq₀
      apply hts
      exact congrArg Prod.fst hpq₀
    have had := hT.isPacking hp₀ hq₀ hpq₀
    change AEDisjoint volume
      (placedTile K.normalizedRegion.prototileFamily p)
      (placedTile K.normalizedRegion.prototileFamily q)
    have hpTile : placedTile K.normalizedRegion.prototileFamily p =
        (K.denominator : ℝ) •
          placedTile K.toPolygonalRegion.prototileFamily p₀ := by
      change p.1 +ᵥ K.normalizedSupport =
        (K.denominator : ℝ) • (t +ᵥ K.support)
      rw [← htp]
      exact K.normalized_placedTile t
    have hqTile : placedTile K.normalizedRegion.prototileFamily q =
        (K.denominator : ℝ) •
          placedTile K.toPolygonalRegion.prototileFamily q₀ := by
      change q.1 +ᵥ K.normalizedSupport =
        (K.denominator : ℝ) • (s +ᵥ K.support)
      rw [← hsq]
      exact K.normalized_placedTile s
    rw [hpTile, hqTile]
    exact aedisjoint_smul K.denominator K.denominator_cast_ne_zero had
  · have hcover :=
      (volume.quasiMeasurePreserving_smul
        (inv_ne_zero K.denominator_cast_ne_zero)).ae hT.isCover
    filter_upwards [hcover] with x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    let j : Placement Plane Unit := (K.normalizedTranslation i.1.1, ())
    have hj : j ∈ K.normalizedRegion.placements (K.normalizedTranslations T) := by
      exact ⟨i.1.1, i.2, rfl⟩
    refine Set.mem_iUnion.mpr ⟨⟨j, hj⟩, ?_⟩
    change x ∈ placedTile K.normalizedRegion.prototileFamily j
    rw [show placedTile K.normalizedRegion.prototileFamily j =
        (K.denominator : ℝ) •
          placedTile K.toPolygonalRegion.prototileFamily i.1 by
      simpa only [j] using K.normalized_placedTile i.1.1]
    refine ⟨(K.denominator : ℝ)⁻¹ • x, hxi, ?_⟩
    change (K.denominator : ℝ) • ((K.denominator : ℝ)⁻¹ • x) = x
    rw [← mul_smul, mul_inv_cancel₀ K.denominator_cast_ne_zero, one_smul]

/-- A placed original tile is the inverse dilation of its normalized counterpart. -/
theorem denormalized_placedTile (K : RationalPolygonalRegion) (t : Plane) :
    placedTile K.toPolygonalRegion.prototileFamily
        (K.denormalizedTranslation t, ()) =
      (K.denominator : ℝ)⁻¹ •
        placedTile K.normalizedRegion.prototileFamily (t, ()) := by
  have h := K.normalized_placedTile (K.denormalizedTranslation t)
  rw [K.normalizedTranslation_denormalizedTranslation] at h
  have hscaled := congrArg
    (fun A : Set Plane ↦ (K.denominator : ℝ)⁻¹ • A) h
  simpa [smul_smul, K.denominator_cast_ne_zero] using hscaled.symm

/-- Inverse rational normalization transports a normalized tiling back to the original region. -/
theorem tiles_of_normalizedRegion_tiles
    (K : RationalPolygonalRegion) {T : Set Plane}
    (hT : K.normalizedRegion.Tiles T) :
    K.toPolygonalRegion.Tiles (K.denormalizedTranslations T) := by
  have hdenormalized_countable : (K.denormalizedTranslations T).Countable :=
    hT.countable.image K.denormalizedTranslation
  refine ⟨PolygonalRegion.placements_countable K.toPolygonalRegion
    hdenormalized_countable, ?_, ?_⟩
  · rintro p hp q hq hpq
    change p.1 ∈ K.denormalizedTranslations T at hp
    change q.1 ∈ K.denormalizedTranslations T at hq
    obtain ⟨t, ht, htp⟩ := hp
    obtain ⟨s, hs, hsq⟩ := hq
    let p₀ : Placement Plane Unit := (t, ())
    let q₀ : Placement Plane Unit := (s, ())
    have hp₀ : p₀ ∈ K.normalizedRegion.placements T := ht
    have hq₀ : q₀ ∈ K.normalizedRegion.placements T := hs
    have hts : t ≠ s := by
      intro hts
      apply hpq
      apply Prod.ext
      · rw [← htp, ← hsq, hts]
      · exact Subsingleton.elim _ _
    have hpq₀ : p₀ ≠ q₀ := by
      intro hpq₀
      apply hts
      exact congrArg Prod.fst hpq₀
    have had := hT.isPacking hp₀ hq₀ hpq₀
    change AEDisjoint volume
      (placedTile K.toPolygonalRegion.prototileFamily p)
      (placedTile K.toPolygonalRegion.prototileFamily q)
    have hpTile : placedTile K.toPolygonalRegion.prototileFamily p =
        (K.denominator : ℝ)⁻¹ •
          placedTile K.normalizedRegion.prototileFamily p₀ := by
      change p.1 +ᵥ K.support =
        (K.denominator : ℝ)⁻¹ • (t +ᵥ K.normalizedSupport)
      rw [← htp]
      exact K.denormalized_placedTile t
    have hqTile : placedTile K.toPolygonalRegion.prototileFamily q =
        (K.denominator : ℝ)⁻¹ •
          placedTile K.normalizedRegion.prototileFamily q₀ := by
      change q.1 +ᵥ K.support =
        (K.denominator : ℝ)⁻¹ • (s +ᵥ K.normalizedSupport)
      rw [← hsq]
      exact K.denormalized_placedTile s
    rw [hpTile, hqTile]
    exact aedisjoint_smul (K.denominator : ℝ)⁻¹
      (inv_ne_zero K.denominator_cast_ne_zero) had
  · have hcover :=
      (volume.quasiMeasurePreserving_smul K.denominator_cast_ne_zero).ae hT.isCover
    filter_upwards [hcover] with x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    let j : Placement Plane Unit := (K.denormalizedTranslation i.1.1, ())
    have hj : j ∈ K.toPolygonalRegion.placements
        (K.denormalizedTranslations T) := by
      exact ⟨i.1.1, i.2, rfl⟩
    refine Set.mem_iUnion.mpr ⟨⟨j, hj⟩, ?_⟩
    change x ∈ placedTile K.toPolygonalRegion.prototileFamily j
    rw [show placedTile K.toPolygonalRegion.prototileFamily j =
        (K.denominator : ℝ)⁻¹ •
          placedTile K.normalizedRegion.prototileFamily i.1 by
      simpa only [j] using K.denormalized_placedTile i.1.1]
    refine ⟨(K.denominator : ℝ) • x, hxi, ?_⟩
    change (K.denominator : ℝ)⁻¹ • ((K.denominator : ℝ) • x) = x
    rw [← mul_smul, inv_mul_cancel₀ K.denominator_cast_ne_zero, one_smul]

end RationalPolygonalRegion

namespace PolygonalRegion

/-- The paper's integer-tiling condition: every placed intrinsic vertex is integral. -/
def IsIntegerTiling (K : PolygonalRegion) (T : Set Plane) : Prop :=
  K.Tiles T ∧
    ∀ t ∈ T, ∀ v ∈ vertexSet K.support, IsIntegerPoint (t + v)

/-- Translating all translation vectors preserves a monotile tiling of the whole plane. -/
theorem Tiles.vadd {K : PolygonalRegion} {T : Set Plane}
    (hT : K.Tiles T) (a : Plane) :
    K.Tiles (a +ᵥ T) := by
  have hTcountable : T.Countable := hT.countable
  have htranslated_countable : (a +ᵥ T).Countable := by
    have heq : a +ᵥ T = (fun t ↦ a + t) '' T := by
      ext x
      constructor
      · intro hx
        refine ⟨-a + x, ?_, by abel_nf⟩
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hx
      · rintro ⟨t, ht, rfl⟩
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          neg_add_cancel_left] using ht
    rw [heq]
    exact hTcountable.image _
  refine ⟨placements_countable K htranslated_countable, ?_, ?_⟩
  · intro p hp q hq hpq
    change p.1 ∈ a +ᵥ T at hp
    change q.1 ∈ a +ᵥ T at hq
    have hpT : -a + p.1 ∈ T := by
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hp
    have hqT : -a + q.1 ∈ T := by
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hq
    let p₀ : Placement Plane Unit := (-a + p.1, ())
    let q₀ : Placement Plane Unit := (-a + q.1, ())
    have hp₀T : p₀ ∈ K.placements T := hpT
    have hq₀T : q₀ ∈ K.placements T := hqT
    have hpq₀ : p₀ ≠ q₀ := by
      intro hpq₀
      apply hpq
      apply Prod.ext
      · have := congrArg Prod.fst hpq₀
        dsimp only [p₀, q₀] at this
        exact add_left_cancel this
      · exact Subsingleton.elim _ _
    have had := hT.isPacking hp₀T hq₀T hpq₀
    have hpTile : placedTile K.prototileFamily p =
        a +ᵥ placedTile K.prototileFamily p₀ := by
      ext x
      simp only [placedTile_eq, Set.mem_vadd_set_iff_neg_vadd_mem, p₀, vadd_eq_add]
      constructor <;> intro hx
      · convert hx using 1
        abel
      · convert hx using 1
        abel
    have hqTile : placedTile K.prototileFamily q =
        a +ᵥ placedTile K.prototileFamily q₀ := by
      ext x
      simp only [placedTile_eq, Set.mem_vadd_set_iff_neg_vadd_mem, q₀, vadd_eq_add]
      constructor <;> intro hx
      · convert hx using 1
        abel
      · convert hx using 1
        abel
    change AEDisjoint volume (placedTile K.prototileFamily p)
      (placedTile K.prototileFamily q)
    rw [hpTile, hqTile]
    exact aedisjoint_vadd a had
  · have hcover := (quasiMeasurePreserving_add_left volume (-a)).ae hT.isCover
    filter_upwards [hcover] with x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    let j : Placement Plane Unit := (a + i.1.1, ())
    have hj : j ∈ K.placements (a +ᵥ T) := by
      simpa only [placements, Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
        j, vadd_eq_add, neg_add_cancel_left] using i.2
    refine Set.mem_iUnion.mpr ⟨⟨j, hj⟩, ?_⟩
    change x ∈ (a + i.1.1) +ᵥ K.support
    change -a + x ∈ i.1.1 +ᵥ K.support at hxi
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxi ⊢
    convert hxi using 1
    simp only [vadd_eq_add]
    abel

private theorem vertexGraph_adj_translation_sub_mem_integerLattice
    {K : PolygonalRegion} {T : Set Plane} (hK : K.HasIntegerVertices)
    {i j : (K.polygonalProtoTiling T).placements}
    (hij : (K.polygonalProtoTiling T).vertexGraph.Adj i j) :
    j.1.1 - i.1.1 ∈ integerLattice := by
  let A := K.polygonalProtoTiling T
  have hconnected : A.VertexConnected i j := (A.vertexGraph_adj i j).mp hij |>.2
  obtain ⟨x, hxi, hxj⟩ := hconnected
  change x ∈ i.1.1 +ᵥ vertexSet K.support at hxi
  change x ∈ j.1.1 +ᵥ vertexSet K.support at hxj
  rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxi hxj
  have hi := hK (-i.1.1 +ᵥ x) hxi
  have hj := hK (-j.1.1 +ᵥ x) hxj
  change -i.1.1 +ᵥ x ∈ integerLattice at hi
  change -j.1.1 +ᵥ x ∈ integerLattice at hj
  have hdifference := AddSubgroup.sub_mem integerLattice hi hj
  convert hdifference using 1
  simp only [vadd_eq_add]
  abel

private theorem walk_translation_sub_mem_integerLattice
    {K : PolygonalRegion} {T : Set Plane} (hK : K.HasIntegerVertices)
    {i j : (K.polygonalProtoTiling T).placements}
    (p : (K.polygonalProtoTiling T).vertexGraph.Walk i j) :
    j.1.1 - i.1.1 ∈ integerLattice := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
      have huv' := vertexGraph_adj_translation_sub_mem_integerLattice hK huv
      change v.1.1 - u.1.1 ∈ integerLattice at huv'
      have hsum := AddSubgroup.add_mem integerLattice huv' ih
      convert hsum using 1
      abel

/-- Vertex-graph reachability in an integer-vertex tiling forces an integral translation
difference.  This is the arithmetic content of paper Lemma 2.4. -/
theorem samePlate_translation_sub_mem_integerLattice
    {K : PolygonalRegion} {T : Set Plane} (hK : K.HasIntegerVertices)
    {i j : (K.polygonalProtoTiling T).placements}
    (hij : (K.polygonalProtoTiling T).SamePlate i j) :
    j.1.1 - i.1.1 ∈ integerLattice := by
  obtain ⟨p⟩ := hij
  exact walk_translation_sub_mem_integerLattice hK p

/-- A connected monotile tiling containing the origin has only integer translation vectors. -/
theorem translations_integer_of_connected
    {K : PolygonalRegion} {T : Set Plane} (hK : K.HasIntegerVertices)
    (hzero : 0 ∈ T) (hconnected : (K.polygonalProtoTiling T).vertexGraph.Connected) :
    ∀ t ∈ T, IsIntegerPoint t := by
  intro t ht
  let i : (K.polygonalProtoTiling T).placements := ⟨(0, ()), hzero⟩
  let j : (K.polygonalProtoTiling T).placements := ⟨(t, ()), ht⟩
  have hreach : (K.polygonalProtoTiling T).SamePlate i j := hconnected i j
  change t ∈ integerLattice
  simpa only [i, j, sub_zero] using samePlate_translation_sub_mem_integerLattice hK hreach

/-- Every monotile tiling can be replaced by one whose vertex-sharing graph is connected.  This is
the monotile form of paper Lemma 2.7. -/
theorem exists_connected_tiling {K : PolygonalRegion} {T : Set Plane}
    (hT : K.Tiles T) :
    ∃ T' : Set Plane,
      K.Tiles T' ∧ (K.polygonalProtoTiling T').vertexGraph.Connected := by
  let A := K.polygonalProtoTiling T
  obtain ⟨S, hS, hconnected⟩ := A.exists_connected_tiling hT
  let T' : Set Plane := Prod.fst '' S
  have hplacements : K.placements T' = S := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hqS, hqp⟩ := hp
      have hqp' : q = p := by
        apply Prod.ext hqp
        exact Subsingleton.elim _ _
      simpa only [hqp'] using hqS
    · intro hp
      exact ⟨p, hp, rfl⟩
  rw [← hplacements] at hS hconnected
  refine ⟨T', hS, ?_⟩
  simpa only [polygonalProtoTiling, PolygonalProtoTiling.withPlacements, A] using hconnected

/-- **Existence of an integer tiling (paper Lemma 2.2).**  Any tiling by a polygonal region with
integer vertices can be replaced by a tiling containing the origin whose translations are all
integer lattice points. -/
theorem exists_integer_tiling {K : PolygonalRegion} (hK : K.HasIntegerVertices)
    {T : Set Plane} (hT : K.Tiles T) :
    ∃ T' : Set Plane,
      K.Tiles T' ∧ 0 ∈ T' ∧ ∀ t ∈ T', IsIntegerPoint t := by
  obtain ⟨T₀, hT₀, hconnected⟩ := exists_connected_tiling hT
  obtain ⟨i⟩ := hconnected.nonempty
  let base : Plane := i.1.1
  let T' : Set Plane := -base +ᵥ T₀
  have hibase : base ∈ T₀ := by
    change i.1.1 ∈ T₀
    exact i.2
  have hzero : 0 ∈ T' := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [neg_neg, vadd_eq_add, add_zero] using hibase
  have hinteger : ∀ t ∈ T', IsIntegerPoint t := by
    intro t ht
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at ht
    let ibase : (K.polygonalProtoTiling T₀).placements := ⟨(base, ()), i.2⟩
    let it : (K.polygonalProtoTiling T₀).placements := ⟨(-(-base) +ᵥ t, ()), ht⟩
    have hreach : (K.polygonalProtoTiling T₀).SamePlate ibase it :=
      hconnected ibase it
    have hdifference := samePlate_translation_sub_mem_integerLattice hK hreach
    change t ∈ integerLattice
    convert hdifference using 1
    simp only [ibase, it, vadd_eq_add]
    abel
  exact ⟨T', hT₀.vadd (-base), hzero, hinteger⟩

end PolygonalRegion

end Tiling.RationalPolygonal
