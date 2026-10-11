import Mathlib
import Tiling.RationalSlopes.Main

/-!
# Tilings by rational-slope tiles

The plane is identified with the complex numbers. A tile is a nonempty bounded
open set whose frontier is a finite union of rational-direction segments.
Packing and coverage are understood up to sets of area zero; periods, partitions,
and all statements about the original centres are exact.

RS1 and RS4 retain the original centres; RS2 and RS5 construct replacement tilings.
RS5 permits different period lattices on different pieces.
-/

set_option autoImplicit false

open MeasureTheory Set Submodule
open scoped Pointwise Topology

namespace RationalSlopesAdapter

/-- The Euclidean plane with its usual area measure. -/
abbrev Plane := ℂ

/-! ## Tiles and tilings -/

/-- A set equal to the interior of its closure; in particular, it is open. -/
def IsRegularOpen (E : Set Plane) : Prop := interior (closure E) = E

/-- The real span of `v` contains a nonzero integer vector. -/
def IsRationalDirection (v : Plane) : Prop :=
  ∃ r i : ℤ, (r, i) ≠ 0 ∧ ⟨r, i⟩ ∈ span ℝ ({v} : Set ℂ)

/-- A nonempty bounded open tile whose frontier is a finite union of
nondegenerate segments in rational directions. Boundary vertices may have
arbitrary real coordinates; holes and disconnected components are allowed. -/
def IsRationalSlopeTile (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ IsOpen Ω ∧ Bornology.IsBounded Ω ∧
    ∃ edges : Finset (Plane × Plane),
      (∀ e ∈ edges, e.1 ≠ e.2 ∧ IsRationalDirection (e.2 - e.1)) ∧
        frontier Ω = ⋃ e ∈ edges, segment ℝ e.1 e.2

/-- Distinct translates of the tile overlap only on a set of area zero. -/
def Packing (Ω T : Set Plane) : Prop :=
  ∀ s ∈ T, ∀ t ∈ T, s ≠ t → volume ((s +ᵥ Ω) ∩ (t +ᵥ Ω)) = 0

/-- Almost-everywhere coverage, with neither gaps in `E` nor overspill outside it. -/
def CoversExactly (Ω T E : Set Plane) : Prop :=
  ∀ᵐ x ∂volume, x ∈ E ↔ ∃ t ∈ T, x ∈ t +ᵥ Ω

/-- A countable packing of translates covering exactly the carrier `E`. -/
def TilingOn (Ω T E : Set Plane) : Prop :=
  T.Countable ∧ Packing Ω T ∧ CoversExactly Ω T E

/-- A translational tiling of the whole plane. -/
def Tiling (Ω T : Set Plane) : Prop := TilingOn Ω T univ

/-- The regular-open carrier of a family of translates. -/
def coveredRegion (Ω T : Set Plane) : Set Plane :=
  interior (closure (⋃ t ∈ T, t +ᵥ Ω))

/-! ## Periods and finite partitions -/

/-- A literal translational period; zero is allowed. -/
def IsPeriod (A : Set Plane) (p : Plane) : Prop := p +ᵥ A = A

/-- Two real-linearly independent periods, hence a rank-two period lattice. -/
def IsPeriodic (A : Set Plane) : Prop :=
  ∃ p q : Plane, LinearIndependent ℝ ![p, q] ∧ IsPeriod A p ∧ IsPeriod A q

/-- An exact partition into nonempty, pairwise disjoint sets. -/
def IsPartition (A : Set Plane) (pieces : Set (Set Plane)) : Prop :=
  (∀ S ∈ pieces, S.Nonempty) ∧ pieces.Pairwise Disjoint ∧ ⋃₀ pieces = A

/-- A finite partition into sets with nonzero periods, possibly different ones. -/
def WeaklyPeriodic (A : Set Plane) : Prop :=
  ∃ pieces : Finset (Set Plane), IsPartition A pieces ∧
    ∀ S ∈ pieces, ∃ p : Plane, p ≠ 0 ∧ IsPeriod S p

/-- A finite partition into doubly periodic sets; no common lattice is required. -/
def QuasiPeriodic (A : Set Plane) : Prop :=
  ∃ pieces : Finset (Set Plane), IsPartition A pieces ∧
    ∀ S ∈ pieces, IsPeriodic S

/-- Finitely many displacement vectors in every bounded set.
This also implies that the centre set itself is locally finite. -/
def HasFiniteLocalComplexity (T : Set Plane) : Prop :=
  ∀ B : Set Plane, Bornology.IsBounded B → ((T - T) ∩ B).Finite

/-! ## Columns -/

/-- Invariance under every translation in the direction `v`. -/
def IsInvariantAlong (E : Set Plane) (v : Plane) : Prop :=
  ∀ r : ℝ, IsPeriod E (r • v)

/-- Centres on the affine line through `t` in direction `v`. -/
def lineFibre (v : Plane) (T : Set Plane) (t : Plane) : Set Plane :=
  {s | s ∈ T ∧ ∃ r : ℝ, s = t + r • v}

/-- A packing in which every full directional fibre has a line-invariant carrier.
Each fibre is automatically nonempty, line-supported, and itself a packing. -/
def IsUnionOfColumns (Ω : Set Plane) (v : Plane) (T : Set Plane) : Prop :=
  Packing Ω T ∧
    ∀ t ∈ T, IsInvariantAlong (coveredRegion Ω (lineFibre v T t)) v

/-! ## Fell hulls and minimality -/

/-- Closed sets meeting `U`. -/
def hit (U : Set Plane) : Set (TopologicalSpace.Closeds Plane) :=
  {F | ((F : Set Plane) ∩ U).Nonempty}

/-- Closed sets avoiding `K`. -/
def miss (K : Set Plane) : Set (TopologicalSpace.Closeds Plane) :=
  {F | Disjoint (F : Set Plane) K}

/-- The hit-open/miss-compact Fell topology; points may escape to infinity. -/
abbrev fellTopology : TopologicalSpace (TopologicalSpace.Closeds Plane) :=
  TopologicalSpace.generateFrom
    ((hit '' {U : Set Plane | IsOpen U}) ∪ (miss '' {K : Set Plane | IsCompact K}))

/-- The Fell closure of translates of `T` by literal periods of its carrier `E`.
The closure is taken in the space of all closed subsets of the plane. -/
def orbitHull (E T : Set Plane) : Set (TopologicalSpace.Closeds Plane) :=
  closure[fellTopology]
    {S | ∃ p : Plane, IsPeriod E p ∧ (S : Set Plane) = p +ᵥ T}

/-- A closed centre set is minimal when every point of its hull generates that
same hull. This dynamical property does not depend on a choice of tile. -/
def IsMinimal (E T : Set Plane) : Prop :=
  IsClosed T ∧ ∀ S ∈ orbitHull E T, orbitHull E (S : Set Plane) = orbitHull E T

/-! ## Structural decomposition -/

/-- An exact partition of the original centres into a column aggregate and
finitely many nonempty minimal FLC pieces, all on periodic, direction-invariant
carriers. The column aggregate is not required to have finite local complexity. -/
structure MinimalTilingStructure (Ω T : Set Plane) where
  direction : Plane
  direction_rational : IsRationalDirection direction
  columns : Set Plane
  columns_subset : columns ⊆ T
  columns_are_union_of_columns : IsUnionOfColumns Ω direction columns
  pieces : Finset (Set Plane)
  pieces_partition : IsPartition (T \ columns) pieces
  pieces_have_finite_local_complexity : ∀ S ∈ pieces, HasFiniteLocalComplexity S
  pieces_tile_covered_region : ∀ S ∈ pieces, TilingOn Ω S (coveredRegion Ω S)
  pieces_minimal : ∀ S ∈ pieces, IsMinimal (coveredRegion Ω S) S
  columns_carrier_invariant : IsInvariantAlong (coveredRegion Ω columns) direction
  pieces_carrier_invariant : ∀ S ∈ pieces, IsInvariantAlong (coveredRegion Ω S) direction
  columns_carrier_periodic : IsPeriodic (coveredRegion Ω columns)
  pieces_carrier_periodic : ∀ S ∈ pieces, IsPeriodic (coveredRegion Ω S)

/-! ## Private adapters to the production API -/

noncomputable section

open Tiling.RationalPolygonal (PolygonalRegion IntegerPlane integerPoint)
open Tiling.Approximation
open Tiling.RationalSlopes.Approximation

private theorem regularOpen_isOpen {X : Type*} [TopologicalSpace X] {Ω : Set X}
    (hregular : interior (closure Ω) = Ω) : IsOpen Ω := by
  rw [← hregular]
  exact isOpen_interior

private theorem open_closure_regularClosed {X : Type*} [TopologicalSpace X] {Ω : Set X}
    (hopen : IsOpen Ω) : closure (interior (closure Ω)) = closure Ω := by
  apply subset_antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · exact closure_mono hopen.subset_interior_closure

private theorem isRationalVectorDirection_of_integer_span {v : Plane}
    (h : IsRationalDirection v) :
    Tiling.RationalSlopes.IsRationalVectorDirection v := by
  obtain ⟨r, i, hri, hmem⟩ := h
  let z : IntegerPlane := ![r, i]
  have hz : z ≠ 0 := by
    intro hzero
    apply hri
    apply Prod.ext
    · simpa [z] using congrFun hzero 0
    · simpa [z] using congrFun hzero 1
  have hpoint : integerPoint z = (⟨r, i⟩ : Plane) := by
    apply Complex.ext <;> simp [z, integerPoint]
  have hzmem : integerPoint z ∈ Submodule.span ℝ ({v} : Set Plane) := by
    rw [hpoint]
    exact hmem
  have hv : v ≠ 0 := by
    intro hzero
    rw [hzero] at hzmem
    have hzpoint : integerPoint z = 0 := by simpa using hzmem
    exact hz (Tiling.RationalPolygonal.integerPoint_injective (by simpa using hzpoint))
  exact ⟨hv, z, hz, hzmem⟩

private theorem lineEval_combo (l : RationalLine) (x y : Plane) (a b : ℝ)
    (hab : a + b = 1) : l.eval (a • x + b • y) = a * l.eval x + b * l.eval y := by
  simp only [RationalLine.eval, normalEval, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]
  linear_combination l.offset * hab

private theorem rationalSegment_hasLine {a b : Plane}
    (hdir : Tiling.RationalSlopes.IsRationalVectorDirection (b - a)) :
    ∃ l : RationalLine, ∀ z ∈ segment ℝ a b, l.eval z = 0 := by
  obtain ⟨n, hn⟩ := rationalDirection_hasNormal
    (Submodule.span ℝ ({b - a} : Set Plane)) (finrank_span_singleton hdir.1) hdir.2
  let l : RationalLine := ⟨n, normalEval n a⟩
  have hba : b - a ∈ normalDirection n := by
    rw [hn]
    exact Submodule.mem_span_singleton_self _
  have hba' : normalEval n (b - a) = 0 := by
    exact hba
  have hevalb : l.eval b = 0 := by
    dsimp [l, RationalLine.eval, normalEval] at hba' ⊢
    linarith
  have hevala : l.eval a = 0 := by simp [l, RationalLine.eval]
  refine ⟨l, ?_⟩
  rintro z ⟨s, t, _, _, hst, rfl⟩
  rw [lineEval_combo l a b s t hst, hevala, hevalb]
  simp

private theorem rationalSegment_direction_of_lineCover {a b : Plane} (hab : a ≠ b)
    (L : List RationalLine)
    (hcover : ∀ z ∈ segment ℝ a b, ∃ l ∈ L, l.eval z = 0) :
    Tiling.RationalSlopes.IsRationalVectorDirection (b - a) := by
  classical
  have hparam : ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ l ∈ L, l.eval ((1 - t) • a + t • b) = 0 := by
    intro t ht
    exact hcover _ ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, sub_add_cancel _ _, rfl⟩
  obtain ⟨l₀, _, _⟩ := hcover a (left_mem_segment ℝ a b)
  let label : ℝ → RationalLine := fun t =>
    if ht : t ∈ Icc (0 : ℝ) 1 then Classical.choose (hparam t ht) else l₀
  have hlabel (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      label t ∈ L ∧ (label t).eval ((1 - t) • a + t • b) = 0 := by
    simpa only [label, dif_pos ht] using Classical.choose_spec (hparam t ht)
  obtain ⟨s, hs, t, ht, hst, hlabels⟩ :=
    (Icc_infinite (by norm_num : (0 : ℝ) < 1)).exists_ne_map_eq_of_mapsTo
      (f := label) (t := (L.toFinset : Set RationalLine))
      (fun t ht => List.mem_toFinset.mpr (hlabel t ht).1) L.toFinset.finite_toSet
  let l := label s
  have hse : l.eval ((1 - s) • a + s • b) = 0 := (hlabel s hs).2
  have hte : l.eval ((1 - t) • a + t • b) = 0 := by
    simpa only [l, hlabels] using (hlabel t ht).2
  rw [lineEval_combo l a b (1 - s) s (by ring)] at hse
  rw [lineEval_combo l a b (1 - t) t (by ring)] at hte
  have hmul : (s - t) * (l.eval b - l.eval a) = 0 := by
    nlinarith [hse, hte]
  have hequal : l.eval b = l.eval a :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hst))
  have hmem : b - a ∈ normalDirection l.normal := by
    change normalEval l.normal (b - a) = 0
    dsimp [RationalLine.eval, normalEval] at hequal ⊢
    linarith
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
    (normalDirection_rational l.normal).1 hmem hne
  exact ⟨hne, hspan ▸ (normalDirection_rational l.normal).2⟩

/-- The finite line cover is a subset statement: extra boundary slits may vanish
on closing the tile. Intrinsic segments of the resulting region still have rational directions. -/
private theorem hasRationalSlopes_of_frontierLineFamily (K : PolygonalRegion)
    (L : List RationalLine)
    (hfront : ∀ z ∈ frontier K.support, ∃ l ∈ L, l.eval z = 0) :
    Tiling.RationalSlopes.HasRationalSlopes K := by
  obtain ⟨F, hF, hcover⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  refine ⟨F, ?_, hcover⟩
  intro e he
  obtain ⟨hne, _, _, hseg⟩ := hF e he
  exact rationalSegment_direction_of_lineCover hne L (fun z hz => hfront z (hseg hz))

private theorem rationalSegments_frontierLineFamily {Ω : Set Plane}
    (edges : Finset (Plane × Plane))
    (hdir : ∀ e ∈ edges, Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1))
    (hfront : frontier Ω = ⋃ e ∈ edges, segment ℝ e.1 e.2) :
    ∃ L : List RationalLine, ∀ z ∈ frontier Ω, ∃ l ∈ L, l.eval z = 0 := by
  classical
  choose line hline using fun e : {e // e ∈ edges} => rationalSegment_hasLine (hdir e.1 e.2)
  let L : List RationalLine := edges.attach.toList.map line
  refine ⟨L, ?_⟩
  intro z hz
  rw [hfront] at hz
  obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp hz
  refine ⟨line ⟨e, he⟩, ?_, hline ⟨e, he⟩ z hz⟩
  exact List.mem_map.mpr ⟨⟨e, he⟩, by simp, rfl⟩

private def tileEdges (Ω : Set Plane) (htile_shape : IsRationalSlopeTile Ω) :
    Finset (Plane × Plane) := Classical.choose htile_shape.2.2.2

private theorem tileEdges_rational {Ω : Set Plane} (htile_shape : IsRationalSlopeTile Ω) :
    ∀ e ∈ tileEdges Ω htile_shape,
      Tiling.RationalSlopes.IsRationalVectorDirection (e.2 - e.1) := by
  intro e he
  exact isRationalVectorDirection_of_integer_span
    ((Classical.choose_spec htile_shape.2.2.2).1 e he).2

private theorem tileEdges_frontier {Ω : Set Plane} (htile_shape : IsRationalSlopeTile Ω) :
    frontier Ω = ⋃ e ∈ tileEdges Ω htile_shape, segment ℝ e.1 e.2 :=
  (Classical.choose_spec htile_shape.2.2.2).2

private theorem tile_frontier_lines {Ω : Set Plane} (htile_shape : IsRationalSlopeTile Ω) :
    ∃ L : List RationalLine, ∀ z ∈ frontier Ω, ∃ l ∈ L, l.eval z = 0 :=
  rationalSegments_frontierLineFamily (tileEdges Ω htile_shape)
    (tileEdges_rational htile_shape) (tileEdges_frontier htile_shape)

private theorem tile_closure_isPolygonal {Ω : Set Plane}
    (htile_shape : IsRationalSlopeTile Ω) : Tiling.IsPolygonal (closure Ω) := by
  obtain ⟨L, hL⟩ := tile_frontier_lines htile_shape
  exact isPolygonal_of_finite_rational_frontier_lines (closure Ω)
    htile_shape.2.2.1.isCompact_closure (open_closure_regularClosed htile_shape.2.1) L
    (fun z hz => hL z (frontier_closure_subset hz))

/-- The canonical closed support is the closure of the original open tile. -/
private def toRegion (Ω : Set Plane) (htile_shape : IsRationalSlopeTile Ω) :
    PolygonalRegion where
  support := closure Ω
  isPolygonal := tile_closure_isPolygonal htile_shape
  nonempty := htile_shape.1.mono subset_closure

private theorem toRegion_hasRationalSlopes {Ω : Set Plane}
    (htile_shape : IsRationalSlopeTile Ω) :
    Tiling.RationalSlopes.HasRationalSlopes (toRegion Ω htile_shape) := by
  obtain ⟨L, hL⟩ := tile_frontier_lines htile_shape
  exact hasRationalSlopes_of_frontierLineFamily _ L
    (fun z hz => hL z (frontier_closure_subset hz))

private theorem volume_segment_zero (a b : Plane) : volume (segment ℝ a b) = 0 := by
  rw [← convexHull_pair]
  apply measure_mono_null (convexHull_subset_affineSpan {a, b})
  apply Measure.addHaar_affineSubspace
  by_cases hab : a = b
  · subst b
    intro htop
    have htop' : affineSpan ℝ ({a} : Set Plane) = ⊤ := by simpa using htop
    have hmem : a + 1 ∈ affineSpan ℝ ({a} : Set Plane) := by rw [htop']; simp
    have ha := (AffineSubspace.mem_affineSpan_singleton ℝ Plane).mp hmem
    have : (1 : Plane) = 0 := by linear_combination ha
    exact one_ne_zero this
  · intro htop
    have hdim := congrArg (fun s : AffineSubspace ℝ Plane => Module.finrank ℝ s.direction) htop
    rw [direction_affineSpan, vectorSpan_pair_rev, vsub_eq_sub,
      finrank_span_singleton (sub_ne_zero.mpr (Ne.symm hab)), AffineSubspace.direction_top,
      finrank_top, Complex.finrank_real_complex] at hdim
    omega

private theorem finiteSegments_frontier_null {Ω : Set Plane} (edges : Finset (Plane × Plane))
    (hfront : frontier Ω = ⋃ e ∈ edges, segment ℝ e.1 e.2) :
    volume (frontier Ω) = 0 := by
  rw [hfront]
  exact (measure_biUnion_null_iff edges.countable_toSet).mpr
    (fun e _ => volume_segment_zero e.1 e.2)

private theorem toRegion_openCarrier_ae_eq {Ω : Set Plane}
    (htile_shape : IsRationalSlopeTile Ω) :
    (toRegion Ω htile_shape).openCarrier =ᵐ[volume] Ω :=
  (toRegion Ω htile_shape).openCarrier_ae_eq.trans
    (closure_ae_eq_of_null_frontier
      (finiteSegments_frontier_null (tileEdges Ω htile_shape) (tileEdges_frontier htile_shape)))

/-- A null tile frontier and the identified closed support supply the AE adapter hypothesis. -/
private theorem tile_ae_eq_openCarrier_of_null_frontier {Ω : Set Plane} {K : PolygonalRegion}
    (hfrontier : volume (frontier Ω) = 0) (hclosure : closure Ω = K.support) :
    Ω =ᵐ[volume] K.openCarrier := by
  have hsupport : Ω =ᵐ[volume] K.support := by
    simpa only [hclosure] using (closure_ae_eq_of_null_frontier hfrontier).symm
  exact hsupport.trans K.openCarrier_ae_eq.symm

/-- Area-equivalent tiles remain area-equivalent under every translation. -/
private theorem translated_tile_ae_eq_openCarrier {Ω : Set Plane} {K : PolygonalRegion}
    (hΩ : Ω =ᵐ[volume] K.openCarrier) (t : Plane) :
    (t +ᵥ Ω : Set Plane) =ᵐ[volume] t +ᵥ K.openCarrier :=
  ((measurePreserving_add_left volume (-t)).quasiMeasurePreserving).vadd_ae_eq_of_ae_eq
    t hΩ

/-- Passing from the open tile to its production support changes no translated area. -/
private theorem translated_openCarrier_ae_eq_support (K : PolygonalRegion) (t : Plane) :
    (t +ᵥ K.openCarrier : Set Plane) =ᵐ[volume] t +ᵥ K.support := by
  have h := (K.isPolygonal.vadd t).interior_ae_eq
  simpa only [PolygonalRegion.openCarrier, interior_vadd] using h

/-- The challenge's open-tile packing is the production support packing. -/
private theorem packing_bridge {Ω T : Set Plane} {K : PolygonalRegion}
    (hΩ : Ω =ᵐ[volume] K.openCarrier) :
    Packing Ω T ↔ Tiling.IsPacking K.prototileFamily (K.placements T) := by
  have htranslate (t : Plane) :
      (t +ᵥ Ω : Set Plane) =ᵐ[volume] t +ᵥ K.support := by
    exact (translated_tile_ae_eq_openCarrier hΩ t).trans
      (translated_openCarrier_ae_eq_support K t)
  constructor
  · intro h u hu v hv hne
    rcases u with ⟨s, ⟨⟩⟩
    rcases v with ⟨t, ⟨⟩⟩
    have hp : AEDisjoint volume (s +ᵥ Ω) (t +ᵥ Ω) :=
      h s hu t hv (fun hst => hne (by simp [hst]))
    exact hp.congr (htranslate s).symm (htranslate t).symm
  · intro h s hs t ht hne
    have hp : AEDisjoint volume (s +ᵥ K.support) (t +ᵥ K.support) :=
      h (show (s, ()) ∈ K.placements T from hs)
        (show (t, ()) ∈ K.placements T from ht) (by simpa using hne)
    exact hp.congr (htranslate s) (htranslate t)

/-- Countability allows area-equivalent tiles to replace each other in their full union. -/
private theorem translated_union_coverage_bridge {Ω T : Set Plane} {K : PolygonalRegion}
    (hΩ : Ω =ᵐ[volume] K.openCarrier) (hT : T.Countable) :
    ∀ᵐ x ∂volume, (∃ t ∈ T, x ∈ t +ᵥ Ω) ↔
      ∃ s : T, x ∈ (s : Plane) +ᵥ K.openCarrier := by
  let : Countable T := hT.to_subtype
  have h := Filter.EventuallyEq.countable_iUnion
    (fun t : T => translated_tile_ae_eq_openCarrier hΩ (t : Plane))
  filter_upwards [h] with x hx
  have hx' := eq_iff_iff.mp hx
  change (x ∈ ⋃ t : T, (t : Plane) +ᵥ Ω) ↔
    (x ∈ ⋃ t : T, (t : Plane) +ᵥ K.openCarrier) at hx'
  simpa only [Set.mem_iUnion, Subtype.exists, exists_prop] using hx'

/-- Coverage may use either open representative once the centres are countable. -/
private theorem coversExactly_bridge {Ω T E : Set Plane} {K : PolygonalRegion}
    (hΩ : Ω =ᵐ[volume] K.openCarrier) (hT : T.Countable) :
    CoversExactly Ω T E ↔
      ∀ᵐ x ∂volume, x ∈ E ↔ ∃ s : T, x ∈ (s : Plane) +ᵥ K.openCarrier := by
  have hcoverage := translated_union_coverage_bridge hΩ hT
  constructor
  · intro h
    filter_upwards [h, hcoverage] with x hx hcov
    exact hx.trans hcov
  · intro h
    filter_upwards [h, hcoverage] with x hx hcov
    exact hx.trans hcov.symm

/-- The complete countable tiling-on-carrier predicates agree. -/
private theorem tilesOn_bridge {Ω T E : Set Plane} {K : PolygonalRegion}
    (hΩ : Ω =ᵐ[volume] K.openCarrier) :
    TilingOn Ω T E ↔ Tiling.Polygonal.TilesOn K T E := by
  constructor
  · rintro ⟨hc, hp, hcov⟩
    exact ⟨hc, (packing_bridge hΩ).mp hp, (coversExactly_bridge hΩ hc).mp hcov⟩
  · rintro ⟨hc, hp, hcov⟩
    exact ⟨hc, (packing_bridge hΩ).mpr hp, (coversExactly_bridge hΩ hc).mpr hcov⟩

/-- In particular, the challenge plane tiling is production `TilesOn ... univ`. -/
private theorem tiling_bridge {Ω T : Set Plane} {K : PolygonalRegion}
    (hΩ : Ω =ᵐ[volume] K.openCarrier) :
    Tiling Ω T ↔ Tiling.Polygonal.TilesOn K T univ :=
  tilesOn_bridge hΩ

/-- The ordinary-set whole-plane tiling also agrees with production monotile `Tiles`. -/
private theorem tiling_iff_tiles {Ω T : Set Plane} {K : PolygonalRegion}
    (hΩ : Ω =ᵐ[volume] K.openCarrier) : Tiling Ω T ↔ K.Tiles T :=
  (tiling_bridge hΩ).trans (Tiling.Polygonal.tilesOn_univ_iff_tiles K T)

private theorem closure_iUnion_eq_of_closures_eq {I : Type*} {A B : I → Set Plane}
    (h : ∀ i, closure (A i) = closure (B i)) :
    closure (⋃ i, A i) = closure (⋃ i, B i) := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    apply Set.iUnion_subset
    intro i
    exact subset_closure.trans ((h i).le.trans (closure_mono (Set.subset_iUnion B i)))
  · apply closure_minimal _ isClosed_closure
    apply Set.iUnion_subset
    intro i
    exact subset_closure.trans ((h i).ge.trans (closure_mono (Set.subset_iUnion A i)))

/-- Equal closed tile supports give literally equal regularized carriers, for any centre set. -/
private theorem coveredRegion_bridge {Ω T : Set Plane} {K : PolygonalRegion}
    (hclosure : closure Ω = K.support) :
    coveredRegion Ω T = Tiling.Polygonal.regularSupport K T := by
  have htranslated (t : T) :
      closure ((t : Plane) +ᵥ Ω) = closure ((t : Plane) +ᵥ K.openCarrier) := by
    rw [closure_vadd, closure_vadd, hclosure, PolygonalRegion.openCarrier,
      K.isPolygonal.closure_interior]
  have hindex : (⋃ t ∈ T, t +ᵥ Ω) = ⋃ t : T, (t : Plane) +ᵥ Ω := by
    ext x
    simp only [Set.mem_iUnion, Subtype.exists, exists_prop]
  unfold coveredRegion Tiling.Polygonal.regularSupport Tiling.Polygonal.openUnion
  rw [hindex, closure_iUnion_eq_of_closures_eq htranslated]

/-- Difference FLC already forces the centre set to be locally finite, including when empty. -/
private theorem HasFiniteLocalComplexity.locallyFinite {T : Set Plane}
    (hT : HasFiniteLocalComplexity T) (B : Set Plane) (hB : Bornology.IsBounded B) :
    (T ∩ B).Finite := by
  classical
  by_cases hnonempty : T.Nonempty
  · obtain ⟨t, ht⟩ := hnonempty
    have hfinite := hT ((-t) +ᵥ B) (hB.vadd (-t))
    apply (hfinite.image fun d : Plane => d + t).subset
    rintro x ⟨hxT, hxB⟩
    refine ⟨x - t, ⟨⟨x, hxT, t, ht, rfl⟩, ?_⟩, sub_add_cancel x t⟩
    refine ⟨x, hxB, ?_⟩
    change -t + x = x - t
    abel
  · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty, Set.empty_inter]
    exact Set.finite_empty

/-- Arbitrary bounded difference windows and the production radius formulation agree. -/
private theorem finiteLocalComplexity_bridge {T : Set Plane} :
    HasFiniteLocalComplexity T ↔ Tiling.Polygonal.HasFLC T := by
  constructor
  · intro hT
    exact ⟨hT.locallyFinite, fun R _hR => hT _ Metric.isBounded_closedBall⟩
  · intro hT B hB
    obtain ⟨R, hR⟩ := hB.subset_closedBall (0 : Plane)
    let R' := max R 0 + 1
    have hR' : 0 < R' := by
      dsimp [R']
      linarith [le_max_right R 0]
    apply (hT.2 R' hR').subset
    exact inter_subset_inter_right _
      (hR.trans (Metric.closedBall_subset_closedBall (by
        dsimp [R']
        linarith [le_max_left R 0])))

private theorem tile_tiling_bridge {Ω T E : Set Plane}
    (htile_shape : IsRationalSlopeTile Ω) :
    TilingOn Ω T E ↔ Tiling.Polygonal.TilesOn (toRegion Ω htile_shape) T E :=
  tilesOn_bridge (toRegion_openCarrier_ae_eq htile_shape).symm

private theorem isPeriod_iff_mem_periodGroup (A : Set Plane) (p : Plane) :
    RationalSlopesAdapter.IsPeriod A p ↔ p ∈ Tiling.Polygonal.periodGroup A := by
  exact AddAction.mem_stabilizer_iff.symm

private theorem isPeriod_iff_setPeriodicBy (A : Set Plane) (p : Plane) :
    RationalSlopesAdapter.IsPeriod A p ↔ Tiling.RationalPolygonal.SetPeriodicBy A p := by
  constructor
  · intro hp x
    have hmem := congrArg (fun S : Set Plane => p + x ∈ S) hp
    simpa [RationalSlopesAdapter.IsPeriod, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, add_comm] using hmem.symm
  · intro hp
    apply Set.ext
    intro x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add] using (hp (-p + x)).symm

private theorem isPeriodic_iff_isLatticePeriodic (A : Set Plane) :
    RationalSlopesAdapter.IsPeriodic A ↔ Tiling.Polygonal.IsLatticePeriodic A := by
  constructor
  · rintro ⟨p, q, hind, hp, hq⟩
    let L : Tiling.Polygonal.PlanarLattice := ⟨![p, q], hind⟩
    refine ⟨L, ?_⟩
    apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact (isPeriod_iff_mem_periodGroup A p).mp hp
    · exact (isPeriod_iff_mem_periodGroup A q).mp hq
  · rintro ⟨L, hL⟩
    have hbasis : ![L.basis 0, L.basis 1] = L.basis := by
      ext i
      fin_cases i <;> rfl
    refine ⟨L.basis 0, L.basis 1, hbasis.symm ▸ L.independent, ?_, ?_⟩
    · exact (isPeriod_iff_mem_periodGroup A _).mpr
        (hL (AddSubgroup.subset_closure (Set.mem_range_self 0)))
    · exact (isPeriod_iff_mem_periodGroup A _).mpr
        (hL (AddSubgroup.subset_closure (Set.mem_range_self 1)))

/-- The selected enumeration of a `Finset` contains every piece exactly once. -/
private def enumerate (pieces : Finset (Set Plane)) : Fin pieces.card → Set Plane :=
  fun i => (pieces.equivFin.symm i : Set Plane)

private theorem enumerate_mem (pieces : Finset (Set Plane)) (i : Fin pieces.card) :
    enumerate pieces i ∈ pieces :=
  (pieces.equivFin.symm i).property

private theorem enumerate_injective (pieces : Finset (Set Plane)) :
    Function.Injective (enumerate pieces) := by
  intro i j h
  exact pieces.equivFin.symm.injective (Subtype.ext h)

private theorem iUnion_enumerate (pieces : Finset (Set Plane)) :
    (⋃ i, enumerate pieces i) = ⋃₀ pieces := by
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    exact Set.mem_sUnion.mpr ⟨enumerate pieces i, enumerate_mem pieces i, hx⟩
  · rintro ⟨S, hS, hx⟩
    apply Set.mem_iUnion.mpr
    refine ⟨pieces.equivFin ⟨S, hS⟩, ?_⟩
    simpa [enumerate] using hx

/-- Exact conversion of a specific finite partition to its `Fin` enumeration. -/
private theorem isPartition_iff_enumeration (A : Set Plane) (pieces : Finset (Set Plane)) :
    IsPartition A pieces ↔
      (∀ i, (enumerate pieces i).Nonempty) ∧
        Set.PairwiseDisjoint Set.univ (enumerate pieces) ∧
        (⋃ i, enumerate pieces i) = A := by
  rw [IsPartition, iUnion_enumerate]
  constructor
  · rintro ⟨hne, hdis, hcover⟩
    refine ⟨fun i => hne _ (enumerate_mem pieces i), ?_, hcover⟩
    intro i _ j _ hij
    exact hdis (enumerate_mem pieces i) (enumerate_mem pieces j)
      (fun h => hij (enumerate_injective pieces h))
  · rintro ⟨hne, hdis, hcover⟩
    refine ⟨?_, ?_, hcover⟩
    · intro S hS
      simpa [enumerate] using hne (pieces.equivFin ⟨S, hS⟩)
    · intro S hS U hU hSU
      have hij : pieces.equivFin ⟨S, hS⟩ ≠ pieces.equivFin ⟨U, hU⟩ := by
        intro h
        exact hSU (congrArg Subtype.val (pieces.equivFin.injective h))
      simpa [Function.onFun, enumerate] using
        hdis (Set.mem_univ _) (Set.mem_univ _) hij

/-- A finite indexed family, with empty sets removed and repeated sets deduplicated. -/
private def nonemptyPieces {n : ℕ} (part : Fin n → Set Plane) : Finset (Set Plane) := by
  classical
  exact (Finset.univ.image part).filter Set.Nonempty

private theorem mem_nonemptyPieces {n : ℕ} (part : Fin n → Set Plane) (S : Set Plane) :
    S ∈ nonemptyPieces part ↔ (∃ i, part i = S) ∧ S.Nonempty := by
  classical
  simp [nonemptyPieces]

private theorem sUnion_nonemptyPieces {n : ℕ} (part : Fin n → Set Plane) :
    ⋃₀ (nonemptyPieces part) = ⋃ i, part i := by
  classical
  ext x
  constructor
  · rintro ⟨S, hS, hx⟩
    obtain ⟨⟨i, rfl⟩, _⟩ := (mem_nonemptyPieces part S).mp hS
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_sUnion.mpr ⟨part i,
      (mem_nonemptyPieces part (part i)).mpr ⟨⟨i, rfl⟩, ⟨x, hxi⟩⟩, hxi⟩

/-- Removing empty sets preserves literal disjointness and the exact union. -/
private theorem isPartition_nonemptyPieces {A : Set Plane} {n : ℕ}
    (part : Fin n → Set Plane)
    (hdis : Set.PairwiseDisjoint Set.univ part) (hcover : (⋃ i, part i) = A) :
    IsPartition A (nonemptyPieces part) := by
  classical
  refine ⟨?_, ?_, (sUnion_nonemptyPieces part).trans hcover⟩
  · intro S hS
    exact ((mem_nonemptyPieces part S).mp hS).2
  · intro S hS U hU hSU
    obtain ⟨⟨i, rfl⟩, _⟩ := (mem_nonemptyPieces part S).mp hS
    obtain ⟨⟨j, rfl⟩, _⟩ := (mem_nonemptyPieces part U).mp hU
    exact hdis (Set.mem_univ _) (Set.mem_univ _) (fun hij => hSU (congrArg part hij))

/-- Generic bridge for finite partitions with any property on their pieces.
The indexed side intentionally permits empty pieces, which are discarded. -/
private theorem finsetPartition_property_iff_indexed (A : Set Plane) (P : Set Plane → Prop) :
    (∃ pieces : Finset (Set Plane), IsPartition A pieces ∧
      ∀ S ∈ pieces, P S) ↔
    ∃ (n : ℕ) (part : Fin n → Set Plane), (∀ i, P (part i)) ∧
      Set.PairwiseDisjoint Set.univ part ∧ (⋃ i, part i) = A := by
  constructor
  · rintro ⟨pieces, hpartition, hP⟩
    obtain ⟨_, hdis, hcover⟩ := (isPartition_iff_enumeration A pieces).mp hpartition
    exact ⟨pieces.card, enumerate pieces,
      fun i => hP _ (enumerate_mem pieces i), hdis, hcover⟩
  · rintro ⟨n, part, hP, hdis, hcover⟩
    refine ⟨nonemptyPieces part, isPartition_nonemptyPieces part hdis hcover, ?_⟩
    intro S hS
    obtain ⟨⟨i, rfl⟩, _⟩ := (mem_nonemptyPieces part S).mp hS
    exact hP i

private theorem weaklyPeriodic_iff_production (A : Set Plane) :
    RationalSlopesAdapter.WeaklyPeriodic A ↔ Tiling.RationalPolygonal.WeaklyPeriodic A := by
  rw [RationalSlopesAdapter.WeaklyPeriodic,
    finsetPartition_property_iff_indexed A
      (fun S => ∃ p : Plane, p ≠ 0 ∧ RationalSlopesAdapter.IsPeriod S p)]
  constructor
  · rintro ⟨n, part, hperiod, hdis, hcover⟩
    choose period hne hp using hperiod
    exact ⟨⟨n, part, period, hne,
      fun i => (isPeriod_iff_setPeriodicBy (part i) (period i)).mp (hp i), hdis, hcover⟩⟩
  · rintro ⟨d⟩
    exact ⟨d.numberOfParts, d.part,
      fun i => ⟨d.period i, d.period_ne_zero i,
        (isPeriod_iff_setPeriodicBy (d.part i) (d.period i)).mpr (d.periodic_part i)⟩,
      d.pairwiseDisjoint, d.iUnion_parts⟩

private theorem quasiPeriodic_iff_production (A : Set Plane) :
    RationalSlopesAdapter.QuasiPeriodic A ↔ Tiling.Polygonal.IsQuasiPeriodic A := by
  rw [RationalSlopesAdapter.QuasiPeriodic]
  constructor
  · rintro ⟨pieces, hpartition, hperiod⟩
    obtain ⟨hne, hdis, hcover⟩ := (isPartition_iff_enumeration A pieces).mp hpartition
    exact ⟨pieces.card, enumerate pieces,
      fun i => ⟨hne i,
        (isPeriodic_iff_isLatticePeriodic _).mp (hperiod _ (enumerate_mem pieces i))⟩,
      hdis, hcover⟩
  · rintro ⟨n, part, hperiod, hdis, hcover⟩
    refine ⟨nonemptyPieces part, isPartition_nonemptyPieces part hdis hcover, ?_⟩
    intro S hS
    obtain ⟨⟨i, rfl⟩, _⟩ := (mem_nonemptyPieces part S).mp hS
    exact (isPeriodic_iff_isLatticePeriodic _).mpr (hperiod i).2

private def compactifiedCentres (F : TopologicalSpace.Closeds Plane) :
    Set (OnePoint Plane) :=
  (((↑) : Plane → OnePoint Plane) '' (F : Set Plane)) ∪ {OnePoint.infty}

/-- Identification of hit-open/miss-compact Fell with one-point Vietoris.
This proof is adapted from the old Solution's valid `native_fell_topology`.
-/
private theorem native_fell_topology :
    fellTopology = TopologicalSpace.induced compactifiedCentres
      (TopologicalSpace.vietoris (OnePoint Plane)) := by
  let : TopologicalSpace (Set (OnePoint Plane)) :=
    TopologicalSpace.vietoris (OnePoint Plane)
  let : TopologicalSpace (TopologicalSpace.Closeds Plane) := fellTopology
  apply le_antisymm
  · rw [TopologicalSpace.vietoris, induced_generateFrom_eq]
    apply TopologicalSpace.le_generateFrom_iff_subset_isOpen.mpr
    rintro _ ⟨U, hU, rfl⟩
    rcases hU with ⟨V, hV, rfl⟩ | ⟨V, hV, rfl⟩
    · by_cases hinfty : OnePoint.infty ∈ V
      · have hQ : IsCompact (((↑) : Plane → OnePoint Plane) ⁻¹' V)ᶜ :=
          ((OnePoint.isOpen_iff_of_mem hinfty).mp hV).2
        have heq : compactifiedCentres ⁻¹' V.powerset =
            {F : TopologicalSpace.Closeds Plane |
              Disjoint (F : Set Plane) (((↑) : Plane → OnePoint Plane) ⁻¹' V)ᶜ} := by
          ext F
          simp only [Set.mem_preimage, Set.mem_powerset_iff, Set.mem_ofPred_eq,
            compactifiedCentres, Set.union_subset_iff,
            Set.image_subset_iff, Set.singleton_subset_iff, hinfty, and_true,
            Set.disjoint_compl_right_iff_subset]
        rw [heq]
        exact TopologicalSpace.isOpen_generateFrom_of_mem (Or.inr ⟨_, hQ, rfl⟩)
      · have heq : compactifiedCentres ⁻¹' V.powerset = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro F hF
          exact hinfty (hF (Set.mem_union_right _ (Set.mem_singleton _)))
        rw [heq]
        exact @isOpen_empty _ fellTopology
    · by_cases hinfty : OnePoint.infty ∈ V
      · have heq : compactifiedCentres ⁻¹'
              {s : Set (OnePoint Plane) | (s ∩ V).Nonempty} = Set.univ := by
          ext F
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          exact ⟨OnePoint.infty,
            Set.mem_union_right _ (Set.mem_singleton _), hinfty⟩
        rw [heq]
        exact @isOpen_univ _ fellTopology
      · have hopen : IsOpen (((↑) : Plane → OnePoint Plane) ⁻¹' V) :=
          hV.preimage OnePoint.continuous_coe
        have heq : compactifiedCentres ⁻¹'
              {s : Set (OnePoint Plane) | (s ∩ V).Nonempty} =
            {F : TopologicalSpace.Closeds Plane |
              ((F : Set Plane) ∩ (((↑) : Plane → OnePoint Plane) ⁻¹' V)).Nonempty} := by
          ext F
          constructor
          · rintro ⟨z, hz, hzV⟩
            rcases hz with ⟨x, hx, rfl⟩ | hz
            · exact ⟨x, hx, hzV⟩
            · exact (hinfty (by simpa only [Set.mem_singleton_iff.mp hz] using hzV)).elim
          · rintro ⟨x, hx, hxV⟩
            exact ⟨(x : OnePoint Plane), Or.inl ⟨x, hx, rfl⟩, hxV⟩
        rw [heq]
        exact TopologicalSpace.isOpen_generateFrom_of_mem (Or.inl ⟨_, hopen, rfl⟩)
  · apply TopologicalSpace.le_generateFrom_iff_subset_isOpen.mpr
    rintro U (⟨V, hV, rfl⟩ | ⟨Q, hQ, rfl⟩)
    · apply isOpen_induced_iff.mpr
      refine ⟨{s : Set (OnePoint Plane) |
        (s ∩ (((↑) : Plane → OnePoint Plane) '' V)).Nonempty},
        TopologicalSpace.vietoris.isOpen_inter_nonempty_of_isOpen
          (OnePoint.isOpen_image_coe.mpr hV), ?_⟩
      ext F
      constructor
      · rintro ⟨z, hzF, x, hx, rfl⟩
        refine ⟨x, ?_, hx⟩
        simpa [compactifiedCentres] using hzF
      · rintro ⟨x, hx, hxV⟩
        exact ⟨(x : OnePoint Plane), Or.inl ⟨x, hx, rfl⟩, ⟨x, hxV, rfl⟩⟩
    · apply isOpen_induced_iff.mpr
      refine ⟨((((↑) : Plane → OnePoint Plane) '' Q)ᶜ).powerset,
        IsOpen.powerset_vietoris
          (OnePoint.isOpen_compl_image_coe.mpr ⟨hQ.isClosed, hQ⟩), ?_⟩
      ext F
      change ((((↑) : Plane → OnePoint Plane) '' (F : Set Plane)) ∪
        {OnePoint.infty} ⊆ (((↑) : Plane → OnePoint Plane) '' Q)ᶜ) ↔
        Disjoint (F : Set Plane) Q
      simp [Set.subset_def, Set.disjoint_left]
      aesop

local instance : TopologicalSpace (TopologicalSpace.Closeds Plane) := fellTopology

private def compactifyClosed (F : TopologicalSpace.Closeds Plane) :
    TopologicalSpace.NonemptyCompacts (OnePoint Plane) :=
  Tiling.Topology.fellCompactification (F : Set Plane) F.isClosed

private theorem compactifyClosed_inducing : Topology.IsInducing compactifyClosed := by
  constructor
  change fellTopology = TopologicalSpace.induced compactifyClosed
    (TopologicalSpace.induced
      ((↑) : TopologicalSpace.NonemptyCompacts (OnePoint Plane) → Set (OnePoint Plane))
      (TopologicalSpace.vietoris (OnePoint Plane)))
  simp only [induced_compose]
  exact native_fell_topology

private theorem compactifyClosed_embedding : Topology.IsEmbedding compactifyClosed where
  __ := compactifyClosed_inducing
  injective := by
    intro F G h
    apply TopologicalSpace.Closeds.ext
    ext x
    have hx := congrArg
      (fun C : TopologicalSpace.NonemptyCompacts (OnePoint Plane) =>
        (x : OnePoint Plane) ∈ (C : Set (OnePoint Plane))) h
    simpa [compactifyClosed, Tiling.Topology.fellCompactification] using hx

local instance : T2Space (TopologicalSpace.Closeds Plane) :=
  compactifyClosed_embedding.t2Space

/-- The production centre map is an embedding into the ambient Fell space. -/
private theorem centres_embedding (K : Tiling.RationalPolygonal.PolygonalRegion) (E : Set Plane) :
    Topology.IsEmbedding
      (Tiling.Polygonal.Topology.TilingSpace.centres (K := K) (E := E)) where
  eq_induced := by
    let : MetricSpace (OnePoint Plane) := by
      let e : OnePoint Plane ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
        onePointEquivSphereOfFinrankEq (ι := Fin 3) (V := Plane) (by
          norm_num [Plane, Complex.finrank_real_complex])
      exact e.isEmbedding.comapMetricSpace
    change TopologicalSpace.induced
      (fun T : Tiling.Polygonal.Topology.TilingSpace K E =>
        Tiling.Topology.fellCompactification
          (T.centres : Set Plane) T.centres.isClosed)
      (TopologicalSpace.induced
        ((↑) : TopologicalSpace.NonemptyCompacts (OnePoint Plane) → Set (OnePoint Plane))
        (TopologicalSpace.vietoris (OnePoint Plane))) =
      TopologicalSpace.induced Tiling.Polygonal.Topology.TilingSpace.centres fellTopology
    rw [native_fell_topology]
    simp only [induced_compose]
    rfl
  injective := by
    intro U V h
    cases U
    cases V
    cases h
    rfl

/-- In fact, the full fixed-carrier tiling space is a closed subspace of the
ambient Fell space: this follows from production's proved compactness. -/
private theorem centres_closedEmbedding (K : Tiling.RationalPolygonal.PolygonalRegion)
    (E : Set Plane) :
    Topology.IsClosedEmbedding
      (Tiling.Polygonal.Topology.TilingSpace.centres (K := K) (E := E)) where
  __ := centres_embedding K E
  isClosed_range := by
    have hcompact := (Tiling.Polygonal.Topology.tilingSpace_compact K E).image
      (centres_embedding K E).continuous
    simpa only [Set.image_univ] using hcompact.isClosed

/-- Literal periods agree with the production almost-everywhere periods on
regular-open carriers. -/
private theorem period_bridge {E : Set Plane}
    (hopen : IsOpen E) (hregular : interior (closure E) = E) (p : Plane) :
    p ∈ Tiling.Polygonal.aePeriodGroup E ↔ IsPeriod E p := by
  rw [Tiling.Polygonal.aePeriodGroup_eq_periodGroup_of_regularOpen hopen hregular]
  rfl

private theorem centres_translation {K : Tiling.RationalPolygonal.PolygonalRegion} {E : Set Plane}
    (p : Tiling.Polygonal.aePeriodGroup E)
    (U : Tiling.Polygonal.Topology.TilingSpace K E) :
    ((Tiling.Polygonal.Topology.TilingSpace.translate p U).centres : Set Plane) =
      (p : Plane) +ᵥ (U.centres : Set Plane) := by
  change (fun x => x + (p : Plane)) '' (U.centres : Set Plane) = _
  ext x
  simp only [mem_image, mem_vadd_set, vadd_eq_add]
  constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, add_comm _ _⟩

private theorem ambient_orbit_eq_image {K : Tiling.RationalPolygonal.PolygonalRegion}
    {E : Set Plane}
    (hopen : IsOpen E) (hregular : interior (closure E) = E)
    (U : Tiling.Polygonal.Topology.TilingSpace K E) :
    {S : TopologicalSpace.Closeds Plane |
      ∃ p : Plane, IsPeriod E p ∧ (S : Set Plane) = p +ᵥ (U.centres : Set Plane)} =
    Tiling.Polygonal.Topology.TilingSpace.centres ''
      AddAction.orbit (Tiling.Polygonal.aePeriodGroup E) U := by
  ext S
  constructor
  · rintro ⟨p, hp, hS⟩
    let g : Tiling.Polygonal.aePeriodGroup E := ⟨p, (period_bridge hopen hregular p).mpr hp⟩
    refine ⟨Tiling.Polygonal.Topology.TilingSpace.translate g U,
      AddAction.mem_orbit_iff.mpr ⟨g, rfl⟩, ?_⟩
    apply TopologicalSpace.Closeds.ext
    exact (centres_translation g U).trans hS.symm
  · rintro ⟨V, hV, rfl⟩
    obtain ⟨g, rfl⟩ := AddAction.mem_orbit_iff.mp hV
    exact ⟨g, (period_bridge hopen hregular g).mp g.property, centres_translation g U⟩

/-- Closure in the fixed-carrier space is the pullback of ambient Fell closure.
This does not assume that arbitrary ambient closure points are tilings. -/
private theorem production_hull_eq_preimage {K : Tiling.RationalPolygonal.PolygonalRegion}
    {E : Set Plane} (hopen : IsOpen E) (hregular : interior (closure E) = E)
    (U : Tiling.Polygonal.Topology.TilingSpace K E) :
    Tiling.Polygonal.Topology.orbitHull U =
      Tiling.Polygonal.Topology.TilingSpace.centres ⁻¹' orbitHull E (U.centres : Set Plane) := by
  rw [Tiling.Polygonal.Topology.orbitHull,
    (centres_embedding K E).isInducing.closure_eq_preimage_closure_image,
    orbitHull, ambient_orbit_eq_image hopen hregular]

/-- The image of the production hull is the full ambient Fell hull.
The reverse inclusion follows from compactness, rather than an assumed
closed-subspace statement. In particular, this proves that ambient hull points
of a production tiling still tile the fixed carrier. -/
private theorem ambient_hull_eq_image {K : Tiling.RationalPolygonal.PolygonalRegion}
    {E : Set Plane} (hopen : IsOpen E) (hregular : interior (closure E) = E)
    (U : Tiling.Polygonal.Topology.TilingSpace K E) :
    orbitHull E (U.centres : Set Plane) =
      Tiling.Polygonal.Topology.TilingSpace.centres '' Tiling.Polygonal.Topology.orbitHull U := by
  have hc := (centres_embedding K E).continuous
  have hclosed : IsClosed
      (Tiling.Polygonal.Topology.TilingSpace.centres '' Tiling.Polygonal.Topology.orbitHull U) :=
    ((Tiling.Polygonal.Topology.orbitHull_compact U).1.image hc).isClosed
  apply Set.Subset.antisymm
  · rw [orbitHull, ambient_orbit_eq_image hopen hregular]
    apply closure_minimal _ hclosed
    exact Set.image_mono subset_closure
  · change Tiling.Polygonal.Topology.TilingSpace.centres '' _ ⊆ _
    rw [production_hull_eq_preimage hopen hregular]
    exact Set.image_preimage_subset _ _

/-- Ambient Fell closure does not introduce a non-tiling centre set. -/
private theorem ambient_hull_points_tile {K : Tiling.RationalPolygonal.PolygonalRegion}
    {E : Set Plane} (hopen : IsOpen E) (hregular : interior (closure E) = E)
    (U : Tiling.Polygonal.Topology.TilingSpace K E)
    {S : TopologicalSpace.Closeds Plane} (hS : S ∈ orbitHull E (U.centres : Set Plane)) :
    Tiling.Polygonal.TilesOn K (S : Set Plane) E := by
  rw [ambient_hull_eq_image hopen hregular U] at hS
  obtain ⟨V, _, rfl⟩ := hS
  exact V.tilesOn

/-- The hard standalone bridge: the Challenge's tile-independent ambient
minimality and production tiling-space minimality coincide once the centres
tile the same regular-open carrier. -/
private theorem minimal_bridge {K : Tiling.RationalPolygonal.PolygonalRegion} {T E : Set Plane}
    (htiling : Tiling.Polygonal.TilesOn K T E)
    (hopen : IsOpen E) (hregular : interior (closure E) = E) :
    IsMinimal E T ↔ Tiling.Polygonal.Topology.IsMinimalTiling K T E := by
  constructor
  · rintro ⟨hclosed, hminimal⟩
    let U : Tiling.Polygonal.Topology.TilingSpace K E := ⟨⟨T, hclosed⟩, htiling⟩
    obtain ⟨_, hnonempty, hinvariant⟩ := Tiling.Polygonal.Topology.orbitHull_compact U
    refine ⟨U, rfl, hnonempty, isClosed_closure, hinvariant, ?_⟩
    intro V hV
    have hambient : V.centres ∈ orbitHull E T := by
      have hpull := production_hull_eq_preimage hopen hregular U
      rw [hpull] at hV
      exact hV
    rw [production_hull_eq_preimage hopen hregular V, hminimal V.centres hambient]
    exact (production_hull_eq_preimage hopen hregular U).symm
  · rintro ⟨U, hUT, hminimal⟩
    refine ⟨hUT ▸ U.centres.isClosed, ?_⟩
    intro S hS
    rw [← hUT, ambient_hull_eq_image hopen hregular U] at hS
    obtain ⟨V, hV, rfl⟩ := hS
    rw [ambient_hull_eq_image hopen hregular V, hminimal.2.2.2 V hV,
      ← ambient_hull_eq_image hopen hregular U, hUT]

/-- Choose an integer representative of the production rational line. -/
private theorem exists_rational_generator {δ : Submodule ℝ Plane}
    (hone : Module.finrank ℝ δ = 1)
    (hrat : Tiling.RationalSlopes.HasRationalDirection δ) :
    ∃ v : Plane, v ≠ 0 ∧ IsRationalDirection v ∧
      δ = Submodule.span ℝ ({v} : Set Plane) := by
  obtain ⟨z, hz, hspan⟩ :=
    (Tiling.RationalSlopes.hasRationalDirection_iff_integerSpan δ hone).mp hrat
  have hvec : integerPoint z ≠ 0 := by
    intro hzero
    exact hz (Tiling.RationalPolygonal.integerPoint_injective (by simpa using hzero))
  have hcoords : (z 0, z 1) ≠ (0 : ℤ × ℤ) := by
    intro h
    apply hz
    funext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  refine ⟨integerPoint z, hvec, ?_, hspan⟩
  refine ⟨z 0, z 1, hcoords, ?_⟩
  have hpoint : (⟨z 0, z 1⟩ : Plane) = integerPoint z := by
    apply Complex.ext <;> simp [integerPoint]
  rw [hpoint]
  exact Submodule.mem_span_singleton_self _

/-- The submodule and scalar descriptions give exactly the same full fibre. -/
private theorem lineFibre_eq {δ : Submodule ℝ Plane} {v : Plane}
    (hspan : δ = Submodule.span ℝ ({v} : Set Plane)) (T : Set Plane) (t : Plane) :
    Tiling.Polygonal.lineFibre δ T t = lineFibre v T t := by
  ext s
  change (s ∈ T ∧ s - t ∈ δ) ↔ (s ∈ T ∧ ∃ r : ℝ, s = t + r • v)
  rw [hspan]
  constructor
  · rintro ⟨hs, hline⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hline
    refine ⟨hs, r, ?_⟩
    calc
      s = (s - t) + t := by abel
      _ = r • v + t := by rw [hr]
      _ = t + r • v := add_comm _ _
  · rintro ⟨hs, r, rfl⟩
    exact ⟨hs, Submodule.mem_span_singleton.mpr ⟨r, by abel⟩⟩

/-- Restrict original aggregate packing; no geometric bridge is needed here. -/
private theorem packing_mono {Ω T A : Set Plane} (hpacking : Packing Ω T)
    (hsub : A ⊆ T) : Packing Ω A := by
  intro s hs t ht hst
  exact hpacking s (hsub hs) t (hsub ht) hst

private theorem invariantAlong_bridge {δ : Submodule ℝ Plane} {v : Plane} {E : Set Plane}
    (hspan : δ = Submodule.span ℝ ({v} : Set Plane))
    (hInv : Tiling.Polygonal.IsInvariantAlong E δ) : IsInvariantAlong E v := by
  intro r
  apply hInv (r • v)
  rw [hspan]
  exact Submodule.mem_span_singleton.mpr ⟨r, rfl⟩

/-- Production minimality already carries a tiling witness for its fixed carrier. -/
private theorem tilesOn_of_isMinimalTiling {K : PolygonalRegion} {S E : Set Plane}
    (hmin : Tiling.Polygonal.Topology.IsMinimalTiling K S E) :
    Tiling.Polygonal.TilesOn K S E := by
  obtain ⟨U, hU, _⟩ := hmin
  simpa only [hU] using U.tilesOn

namespace ProductionStructure

variable {K : PolygonalRegion} {T : Set Plane}
variable (d : Tiling.RationalSlopes.MinimalWholePlaneStructure K T)

private theorem columns_subset : d.columnAggregate ⊆ T := by
  intro x hx
  rw [← d.centres_partition]
  exact Or.inl hx

/-- The finite-image construction tolerates zero pieces; it adds no empty set. -/
private def pieceFinset : Finset (Set Plane) := Finset.univ.image d.piece

private theorem mem_pieceFinset {S : Set Plane} :
    S ∈ pieceFinset d ↔ ∃ j, d.piece j = S := by
  classical
  simp [pieceFinset]

/-- The image loses no indices: disjoint nonempty production pieces are distinct. -/
private theorem piece_injective : Function.Injective d.piece := by
  intro i j hij
  by_contra hne
  obtain ⟨x, hx⟩ := d.piece_nonempty i
  exact Set.disjoint_left.mp
    (d.pieces_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hne)
    hx (hij ▸ hx)

private theorem card_pieceFinset : (pieceFinset d).card = d.numberOfPieces := by
  classical
  rw [pieceFinset, Finset.card_image_of_injective _ (piece_injective d)]
  simp

/-- Passing from `Fin n` to a Finset preserves exactness and nonemptiness. -/
private theorem pieceFinset_partition :
    IsPartition (T \ d.columnAggregate) (pieceFinset d) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨j, rfl⟩ := (mem_pieceFinset d).mp hS
    exact d.piece_nonempty j
  · intro S hS R hR hSR
    obtain ⟨i, rfl⟩ := (mem_pieceFinset d).mp hS
    obtain ⟨j, rfl⟩ := (mem_pieceFinset d).mp hR
    apply d.pieces_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j)
    intro hij
    exact hSR (congrArg d.piece hij)
  · ext x
    constructor
    · intro hx
      obtain ⟨S, hS, hxS⟩ := Set.mem_sUnion.mp hx
      obtain ⟨j, rfl⟩ := (mem_pieceFinset d).mp hS
      refine ⟨?_, ?_⟩
      · rw [← d.centres_partition]
        exact Or.inr (Set.mem_iUnion.mpr ⟨j, hxS⟩)
      · intro hxcol
        exact Set.disjoint_left.mp (d.column_disjoint_piece j) hxcol hxS
    · rintro ⟨hxT, hxnotcol⟩
      rw [← d.centres_partition] at hxT
      rcases hxT with hxcol | hxpiece
      · exact False.elim (hxnotcol hxcol)
      · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxpiece
        exact Set.mem_sUnion.mpr
          ⟨d.piece j, (mem_pieceFinset d).mpr ⟨j, rfl⟩, hxj⟩

end ProductionStructure

/-- The structural adapter with all nonstructural transports stated explicitly.

`hpacking` is obtained from the original Challenge tiling. In particular we do
not try to infer aggregate packing from production per-fibre column packing.
The support transport must apply to all centre sets, including directional
fibres; transports valid only for the aggregate and named pieces are insufficient.
-/
private def structure_adapter {K : PolygonalRegion} {Ω T : Set Plane}
    (d : Tiling.RationalSlopes.MinimalWholePlaneStructure K T)
    (hpacking : Packing Ω T)
    (support_bridge : ∀ S : Set Plane,
      coveredRegion Ω S = Tiling.Polygonal.regularSupport K S)
    (tiling_bridge : ∀ S E : Set Plane,
      Tiling.Polygonal.TilesOn K S E → TilingOn Ω S E)
    (minimality_bridge : ∀ S : Set Plane,
      Tiling.Polygonal.Topology.IsMinimalTiling K S (Tiling.Polygonal.regularSupport K S) →
        IsMinimal (Tiling.Polygonal.regularSupport K S) S)
    (flc_bridge : ∀ S : Set Plane,
      Tiling.Polygonal.HasFLC S → HasFiniteLocalComplexity S)
    (periodicity_bridge : ∀ E : Set Plane,
      Tiling.Polygonal.IsLatticePeriodic E → IsPeriodic E) :
    MinimalTilingStructure Ω T := by
  classical
  let hgen := exists_rational_generator d.direction_oneDim d.direction_rational
  let v : Plane := Classical.choose hgen
  have hrat : IsRationalDirection v := (Classical.choose_spec hgen).2.1
  have hspan : d.direction = Submodule.span ℝ ({v} : Set Plane) :=
    (Classical.choose_spec hgen).2.2
  refine
    { direction := v
      direction_rational := hrat
      columns := d.columnAggregate
      columns_subset := ProductionStructure.columns_subset d
      columns_are_union_of_columns := ?_
      pieces := ProductionStructure.pieceFinset d
      pieces_partition := ProductionStructure.pieceFinset_partition d
      pieces_have_finite_local_complexity := ?_
      pieces_tile_covered_region := ?_
      pieces_minimal := ?_
      columns_carrier_invariant := ?_
      pieces_carrier_invariant := ?_
      columns_carrier_periodic := ?_
      pieces_carrier_periodic := ?_ }
  · refine ⟨packing_mono hpacking (ProductionStructure.columns_subset d), ?_⟩
    intro t ht
    rw [← lineFibre_eq hspan, support_bridge]
    exact invariantAlong_bridge hspan (d.aggregate_isUnionColumns t ht).2.2.2
  · intro S hS
    obtain ⟨j, rfl⟩ := (ProductionStructure.mem_pieceFinset d).mp hS
    exact flc_bridge _ (d.piece_hasFLC j)
  · intro S hS
    obtain ⟨j, rfl⟩ := (ProductionStructure.mem_pieceFinset d).mp hS
    rw [support_bridge]
    exact tiling_bridge _ _ (tilesOn_of_isMinimalTiling (d.piece_minimal j))
  · intro S hS
    obtain ⟨j, rfl⟩ := (ProductionStructure.mem_pieceFinset d).mp hS
    rw [support_bridge]
    exact minimality_bridge _ (d.piece_minimal j)
  · rw [support_bridge]
    exact invariantAlong_bridge hspan d.aggregate_invariant
  · intro S hS
    obtain ⟨j, rfl⟩ := (ProductionStructure.mem_pieceFinset d).mp hS
    rw [support_bridge]
    exact invariantAlong_bridge hspan (d.piece_invariant j)
  · rw [support_bridge]
    exact periodicity_bridge _ d.aggregate_carrier_periodic
  · intro S hS
    obtain ⟨j, rfl⟩ := (ProductionStructure.mem_pieceFinset d).mp hS
    rw [support_bridge]
    exact periodicity_bridge _ (d.piece_carrier_periodic j)

private def fromStructure {Ω T : Set Plane} (htile_shape : IsRationalSlopeTile Ω)
    (hpacking : Packing Ω T)
    (d : Tiling.RationalSlopes.MinimalWholePlaneStructure (toRegion Ω htile_shape) T) :
    MinimalTilingStructure Ω T :=
  structure_adapter d hpacking
    (fun _ => coveredRegion_bridge rfl)
    (fun _ _ h => (tile_tiling_bridge htile_shape).mpr h)
    (fun _ h => by
      obtain ⟨hopen, hregular⟩ :=
        Tiling.Polygonal.regularSupport_isRegularOpen (toRegion Ω htile_shape) _
      exact (minimal_bridge (tilesOn_of_isMinimalTiling h) hopen hregular).mpr h)
    (fun _ h => finiteLocalComplexity_bridge.mpr h)
    (fun _ h => (isPeriodic_iff_isLatticePeriodic _).mpr h)

/-! ## The five main theorems -/

/-- A minimal FLC tiling of a regular-open periodic carrier has weakly periodic
original centres. -/
theorem minimal_finite_local_complexity_tiling_is_weakly_periodic
    {Ω T E : Set Plane}
    (htile_shape : IsRationalSlopeTile Ω)
    (htiling : TilingOn Ω T E) (hfinite_local_complexity : HasFiniteLocalComplexity T)
    (hregular_open : IsRegularOpen E) (hperiodic : IsPeriodic E)
    (hminimal : IsMinimal E T) : WeaklyPeriodic T := by
  have htiles := (tile_tiling_bridge htile_shape).mp htiling
  exact (weaklyPeriodic_iff_production T).mpr (Tiling.RationalSlopes.minimal_flc_weaklyPeriodic
    (toRegion_hasRationalSlopes htile_shape)
    (finiteLocalComplexity_bridge.mp hfinite_local_complexity)
    htiles (regularOpen_isOpen hregular_open) hregular_open
    ((isPeriodic_iff_isLatticePeriodic E).mp hperiodic)
    ((minimal_bridge htiles (regularOpen_isOpen hregular_open) hregular_open).mp hminimal))

/-- An FLC tiling of a regular-open periodic carrier has a doubly periodic
replacement whose every period is a period of the carrier. -/
theorem finite_local_complexity_tiling_has_periodic_replacement
    {Ω T E : Set Plane}
    (htile_shape : IsRationalSlopeTile Ω)
    (htiling : TilingOn Ω T E) (hfinite_local_complexity : HasFiniteLocalComplexity T)
    (hregular_open : IsRegularOpen E) (hperiodic : IsPeriodic E) :
    ∃ S : Set Plane, TilingOn Ω S E ∧ IsPeriodic S ∧
      ∀ p : Plane, IsPeriod S p → IsPeriod E p := by
  obtain ⟨S, htiles, hper, hperiods⟩ := Tiling.RationalSlopes.flc_exists_periodic_replacement
    (toRegion_hasRationalSlopes htile_shape)
    (finiteLocalComplexity_bridge.mp hfinite_local_complexity)
    ((tile_tiling_bridge htile_shape).mp htiling) (regularOpen_isOpen hregular_open)
    hregular_open ((isPeriodic_iff_isLatticePeriodic E).mp hperiodic)
  refine ⟨S, (tile_tiling_bridge htile_shape).mpr htiles,
    (isPeriodic_iff_isLatticePeriodic S).mpr hper, ?_⟩
  intro p hp
  exact (isPeriod_iff_mem_periodGroup E p).mpr
    (hperiods ((isPeriod_iff_mem_periodGroup S p).mp hp))

/-- A minimal plane tiling has an exact column/FLC partition of its original centres. -/
theorem minimal_plane_tiling_has_structure
    {Ω T : Set Plane}
    (htile_shape : IsRationalSlopeTile Ω)
    (htiling : Tiling Ω T) (hminimal : IsMinimal univ T) :
    Nonempty (MinimalTilingStructure Ω T) := by
  have htiles := (tile_tiling_bridge htile_shape).mp htiling
  obtain ⟨d⟩ := Tiling.RationalSlopes.minimal_wholePlane_structure (toRegion Ω htile_shape) T
    (toRegion_hasRationalSlopes htile_shape) htiles
    ((minimal_bridge htiles isOpen_univ (by simp)).mp hminimal)
  exact ⟨fromStructure htile_shape htiling.2.1 d⟩

/-- The original centres of every minimal plane tiling are weakly periodic. -/
theorem minimal_plane_tiling_is_weakly_periodic
    {Ω T : Set Plane}
    (htile_shape : IsRationalSlopeTile Ω)
    (htiling : Tiling Ω T) (hminimal : IsMinimal univ T) : WeaklyPeriodic T := by
  have htiles := (tile_tiling_bridge htile_shape).mp htiling
  exact (weaklyPeriodic_iff_production T).mpr
    (Tiling.RationalSlopes.minimal_wholePlane_weaklyPeriodic
    (toRegion Ω htile_shape) T (toRegion_hasRationalSlopes htile_shape) htiles
    ((minimal_bridge htiles isOpen_univ (by simp)).mp hminimal))

/-- Every tileable rational-slope tile has a quasi-periodic replacement
plane tiling. Different pieces may have different lattices. -/
theorem tileable_rational_slopes_has_quasi_periodic_tiling
    {Ω T : Set Plane}
    (htile_shape : IsRationalSlopeTile Ω)
    (htiling : Tiling Ω T) :
    ∃ S : Set Plane, Tiling Ω S ∧ QuasiPeriodic S := by
  obtain ⟨S, htiles, hquasi⟩ := Tiling.RationalSlopes.exists_weaklyDoublyPeriodic_tiling
    (toRegion Ω htile_shape) T (toRegion_hasRationalSlopes htile_shape)
    ((tile_tiling_bridge htile_shape).mp htiling)
  exact ⟨S, (tile_tiling_bridge htile_shape).mpr htiles,
    (quasiPeriodic_iff_production S).mpr hquasi⟩


end
end RationalSlopesAdapter

set_option autoImplicit false

open Bornology MeasureTheory Set Submodule TopologicalSpace
open scoped Pointwise Topology

namespace RationalSlopesComparator


abbrev Plane := ℂ




def Packing (Ω T : Set Plane) : Prop :=
  T.Pairwise fun s t ↦ volume ((s +ᵥ Ω) ∩ (t +ᵥ Ω)) = 0


def CoversExactly (E Ω T : Set Plane) : Prop := E =ᵐ[volume] T +ᵥ Ω


def TilingOn (E Ω T : Set Plane) : Prop :=
  T.Countable ∧ Packing Ω T ∧ CoversExactly E Ω T


def Tiling (Ω T : Set Plane) : Prop := TilingOn univ Ω T


def coveredRegion (Ω T : Set Plane) : Set Plane :=
  interior (closure (T +ᵥ Ω))


def IsRegularOpen (E : Set Plane) : Prop := interior (closure E) = E




def IsPeriod (A : Set Plane) (p : Plane) : Prop := p +ᵥ A = A


def IsDoublyPeriodic (A : Set Plane) : Prop :=
  ∃ p q, LinearIndependent ℝ ![p, q] ∧ IsPeriod A p ∧ IsPeriod A q




def WeaklyPeriodic (A : Set Plane) : Prop :=
  ∃ P : Finpartition A, ∀ S ∈ P.parts, ∃ p, p ≠ 0 ∧ IsPeriod S p


def QuasiPeriodic (A : Set Plane) : Prop :=
  ∃ P : Finpartition A, ∀ S ∈ P.parts, IsDoublyPeriodic S




def IsRationalDirection (v : Plane) : Prop :=
  ∃ m n : ℤ, (m, n) ≠ 0 ∧ ⟨m, n⟩ ∈ span ℝ {v}


def IsRationalSlopeTile (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ IsOpen Ω ∧ IsBounded Ω ∧
    ∃ edges : Set (Plane × Plane), edges.Finite ∧
      (∀ e ∈ edges, e.1 ≠ e.2 ∧ IsRationalDirection (e.2 - e.1)) ∧
        frontier Ω = ⋃ e ∈ edges, segment ℝ e.1 e.2




def HasFiniteLocalComplexity (T : Set Plane) : Prop :=
  ∀ B, IsBounded B → ((T - T) ∩ B).Finite




def hit (U : Set Plane) : Set (Closeds Plane) :=
  {F | ((F : Set Plane) ∩ U).Nonempty}


def miss (K : Set Plane) : Set (Closeds Plane) :=
  {F | Disjoint (F : Set Plane) K}


abbrev fellTopology : TopologicalSpace (Closeds Plane) :=
  TopologicalSpace.generateFrom
    ((hit '' {U : Set Plane | IsOpen U}) ∪ (miss '' {K : Set Plane | IsCompact K}))


def orbitHull (E T : Set Plane) : Set (Closeds Plane) :=
  closure[fellTopology]
    {S | ∃ p, IsPeriod E p ∧ (S : Set Plane) = p +ᵥ T}


def IsMinimal (E T : Set Plane) : Prop :=
  IsClosed T ∧ ∀ S ∈ orbitHull E T, orbitHull E (S : Set Plane) = orbitHull E T












def IsInvariantAlong (E : Set Plane) (v : Plane) : Prop :=
  ∀ r : ℝ, IsPeriod E (r • v)


def lineFibre (v : Plane) (T : Set Plane) (t : Plane) : Set Plane :=
  T ∩ (t +ᵥ (span ℝ {v} : Set Plane))


def IsUnionOfColumns (Ω : Set Plane) (v : Plane) (T : Set Plane) : Prop :=
  Packing Ω T ∧
    ∀ t ∈ T, IsInvariantAlong (coveredRegion Ω (lineFibre v T t)) v













noncomputable section

private theorem tile_bridge {Ω : Set Plane} (h : IsRationalSlopeTile Ω) :
    RationalSlopesAdapter.IsRationalSlopeTile Ω := by
  rcases h with ⟨hn, ho, hb, edges, hf, he, hu⟩
  exact ⟨hn, ho, hb, hf.toFinset, by simpa [IsRationalDirection, RationalSlopesAdapter.IsRationalDirection] using he, by simpa using hu⟩

private theorem tiling_bridge {Ω T E : Set Plane} :
    TilingOn E Ω T ↔ RationalSlopesAdapter.TilingOn Ω T E := by
  simp only [TilingOn, RationalSlopesAdapter.TilingOn, Packing,
    RationalSlopesAdapter.Packing, Set.Pairwise, CoversExactly,
    RationalSlopesAdapter.CoversExactly]
  simp only [Filter.EventuallyEq, Set.mem_vadd_set]
  aesop

private theorem weak_bridge {T : Set Plane}
    (h : RationalSlopesAdapter.WeaklyPeriodic T) : WeaklyPeriodic T := by
  obtain ⟨parts, ⟨hn, hd, hu⟩, hp⟩ := h
  exact ⟨⟨parts, Finset.supIndep_iff_pairwiseDisjoint.mpr hd, by simpa [Set.sUnion_eq_biUnion] using hu, by simpa using (fun h => (hn ∅ h).ne_empty rfl)⟩, hp⟩

private theorem quasi_bridge {T : Set Plane}
    (h : RationalSlopesAdapter.QuasiPeriodic T) : QuasiPeriodic T := by
  obtain ⟨parts, ⟨hn, hd, hu⟩, hp⟩ := h
  exact ⟨⟨parts, Finset.supIndep_iff_pairwiseDisjoint.mpr hd, by simpa [Set.sUnion_eq_biUnion] using hu, by simpa using (fun h => (hn ∅ h).ne_empty rfl)⟩, hp⟩

private theorem covered_bridge (Ω T : Set Plane) :
    coveredRegion Ω T = RationalSlopesAdapter.coveredRegion Ω T := by
  unfold coveredRegion RationalSlopesAdapter.coveredRegion
  congr 2
  ext x
  simp

private theorem fibre_bridge (v : Plane) (T : Set Plane) (t : Plane) :
    lineFibre v T t = RationalSlopesAdapter.lineFibre v T t := by
  ext x
  simp [lineFibre, RationalSlopesAdapter.lineFibre, mem_vadd_set,
    Submodule.mem_span_singleton, eq_comm]

private theorem columns_bridge {Ω T : Set Plane} {v : Plane}
    (h : RationalSlopesAdapter.IsUnionOfColumns Ω v T) : IsUnionOfColumns Ω v T := by
  exact ⟨h.1, by simpa only [covered_bridge, fibre_bridge, IsInvariantAlong, RationalSlopesAdapter.IsInvariantAlong, IsPeriod, RationalSlopesAdapter.IsPeriod] using h.2⟩

theorem minimal_finite_local_complexity_tiling_is_weakly_periodic
    {Ω T E : Set Plane}
    (htile : IsRationalSlopeTile Ω)
    (htiling : TilingOn E Ω T) (hflc : HasFiniteLocalComplexity T)
    (hregular : IsRegularOpen E) (hperiodic : IsDoublyPeriodic E)
    (hminimal : IsMinimal E T) : WeaklyPeriodic T := by
  exact weak_bridge (RationalSlopesAdapter.minimal_finite_local_complexity_tiling_is_weakly_periodic
    (tile_bridge htile) (tiling_bridge.mp htiling) hflc hregular hperiodic hminimal)

theorem finite_local_complexity_tiling_has_periodic_replacement
    {Ω T E : Set Plane}
    (htile : IsRationalSlopeTile Ω)
    (htiling : TilingOn E Ω T) (hflc : HasFiniteLocalComplexity T)
    (hregular : IsRegularOpen E) (hperiodic : IsDoublyPeriodic E) :
    ∃ S, TilingOn E Ω S ∧ IsDoublyPeriodic S ∧
      ∀ p, IsPeriod S p → IsPeriod E p := by
  obtain ⟨S, ht, hp, hg⟩ := RationalSlopesAdapter.finite_local_complexity_tiling_has_periodic_replacement
    (tile_bridge htile) (tiling_bridge.mp htiling) hflc hregular hperiodic
  exact ⟨S, tiling_bridge.mpr ht, hp, hg⟩

theorem minimal_plane_tiling_has_structure
    {Ω T : Set Plane}
    (htile : IsRationalSlopeTile Ω)
    (htiling : Tiling Ω T) (hminimal : IsMinimal univ T) :
    ∃ v C, ∃ P : Finpartition (T \ C),
      IsRationalDirection v ∧ C ⊆ T ∧
      IsUnionOfColumns Ω v C ∧
      IsInvariantAlong (coveredRegion Ω C) v ∧
      IsDoublyPeriodic (coveredRegion Ω C) ∧
      ∀ S ∈ P.parts,
        let E := coveredRegion Ω S
        HasFiniteLocalComplexity S ∧
        TilingOn E Ω S ∧ IsMinimal E S ∧
        IsInvariantAlong E v ∧ IsDoublyPeriodic E := by
  obtain ⟨d⟩ := RationalSlopesAdapter.minimal_plane_tiling_has_structure
    (tile_bridge htile) (tiling_bridge.mp htiling) hminimal
  rcases d.pieces_partition with ⟨hn, hd, hu⟩
  let P : Finpartition (T \ d.columns) :=
    ⟨d.pieces, Finset.supIndep_iff_pairwiseDisjoint.mpr hd, by simpa [Set.sUnion_eq_biUnion] using hu, by simpa using (fun h => (hn ∅ h).ne_empty rfl)⟩
  refine ⟨d.direction, d.columns, P, d.direction_rational, d.columns_subset,
    columns_bridge d.columns_are_union_of_columns, ?_, ?_, ?_⟩
  · simpa only [covered_bridge, IsInvariantAlong, RationalSlopesAdapter.IsInvariantAlong, IsPeriod, RationalSlopesAdapter.IsPeriod, IsDoublyPeriodic, RationalSlopesAdapter.IsPeriodic, IsMinimal, RationalSlopesAdapter.IsMinimal, orbitHull, RationalSlopesAdapter.orbitHull, fellTopology, RationalSlopesAdapter.fellTopology, hit, RationalSlopesAdapter.hit, miss, RationalSlopesAdapter.miss] using d.columns_carrier_invariant
  · simpa only [covered_bridge, IsInvariantAlong, RationalSlopesAdapter.IsInvariantAlong, IsPeriod, RationalSlopesAdapter.IsPeriod, IsDoublyPeriodic, RationalSlopesAdapter.IsPeriodic, IsMinimal, RationalSlopesAdapter.IsMinimal, orbitHull, RationalSlopesAdapter.orbitHull, fellTopology, RationalSlopesAdapter.fellTopology, hit, RationalSlopesAdapter.hit, miss, RationalSlopesAdapter.miss] using d.columns_carrier_periodic
  · intro S hS
    exact ⟨d.pieces_have_finite_local_complexity S hS,
      tiling_bridge.mpr (by simpa only [covered_bridge, IsInvariantAlong, RationalSlopesAdapter.IsInvariantAlong, IsPeriod, RationalSlopesAdapter.IsPeriod, IsDoublyPeriodic, RationalSlopesAdapter.IsPeriodic, IsMinimal, RationalSlopesAdapter.IsMinimal, orbitHull, RationalSlopesAdapter.orbitHull, fellTopology, RationalSlopesAdapter.fellTopology, hit, RationalSlopesAdapter.hit, miss, RationalSlopesAdapter.miss] using d.pieces_tile_covered_region S hS),
      by change RationalSlopesAdapter.IsMinimal _ _; simpa only [covered_bridge] using d.pieces_minimal S hS,
      by simpa only [covered_bridge, IsInvariantAlong, RationalSlopesAdapter.IsInvariantAlong, IsPeriod, RationalSlopesAdapter.IsPeriod, IsDoublyPeriodic, RationalSlopesAdapter.IsPeriodic, IsMinimal, RationalSlopesAdapter.IsMinimal, orbitHull, RationalSlopesAdapter.orbitHull, fellTopology, RationalSlopesAdapter.fellTopology, hit, RationalSlopesAdapter.hit, miss, RationalSlopesAdapter.miss] using d.pieces_carrier_invariant S hS,
      by simpa only [covered_bridge, IsInvariantAlong, RationalSlopesAdapter.IsInvariantAlong, IsPeriod, RationalSlopesAdapter.IsPeriod, IsDoublyPeriodic, RationalSlopesAdapter.IsPeriodic, IsMinimal, RationalSlopesAdapter.IsMinimal, orbitHull, RationalSlopesAdapter.orbitHull, fellTopology, RationalSlopesAdapter.fellTopology, hit, RationalSlopesAdapter.hit, miss, RationalSlopesAdapter.miss] using d.pieces_carrier_periodic S hS⟩

theorem minimal_plane_tiling_is_weakly_periodic
    {Ω T : Set Plane}
    (htile : IsRationalSlopeTile Ω)
    (htiling : Tiling Ω T) (hminimal : IsMinimal univ T) : WeaklyPeriodic T := by
  exact weak_bridge (RationalSlopesAdapter.minimal_plane_tiling_is_weakly_periodic
    (tile_bridge htile) (tiling_bridge.mp htiling) hminimal)

theorem tileable_rational_slopes_has_quasi_periodic_tiling
    {Ω T : Set Plane}
    (htile : IsRationalSlopeTile Ω)
    (htiling : Tiling Ω T) :
    ∃ S, Tiling Ω S ∧ QuasiPeriodic S := by
  obtain ⟨S, ht, hp⟩ := RationalSlopesAdapter.tileable_rational_slopes_has_quasi_periodic_tiling
    (tile_bridge htile) (tiling_bridge.mp htiling)
  exact ⟨S, tiling_bridge.mpr ht, quasi_bridge hp⟩

end
end RationalSlopesComparator
