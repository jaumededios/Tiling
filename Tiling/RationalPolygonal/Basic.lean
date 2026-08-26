import Tiling.Geometry.Connected
import TranslationalTilings.Basic

set_option linter.style.header false

/-!
# Rational polygonal regions and their lattice model

This file supplies the common language for the continuous and discrete parts of the formalization
of de Dios Pont--Grebík--Greenfeld--Madrid.  A polygonal region is represented by its nonempty
regular-closed support.  Its paper-style open representative is the interior; the two agree almost
everywhere.

The file also defines the integer-lattice embedding, monotile placement sets, relative rationality,
and the three periodicity notions used in the paper.
-/

open Function MeasureTheory Set
open scoped Pointwise

namespace Tiling.RationalPolygonal

/-- The discrete integer plane used by the Greenfeld--Tao development. -/
abbrev IntegerPlane := TranslationalTilings.Plane

/-- Embed an integer coordinate pair in the real plane. -/
def integerPoint (z : IntegerPlane) : Plane :=
  (z 0 : ℝ) + (z 1 : ℝ) * Complex.I

/-- The integer-plane embedding as an additive homomorphism. -/
def integerPointHom : IntegerPlane →+ Plane where
  toFun := integerPoint
  map_zero' := by
    apply Complex.ext <;> simp [integerPoint]
  map_add' x y := by
    apply Complex.ext <;> simp [integerPoint]

@[simp]
theorem integerPointHom_apply (z : IntegerPlane) : integerPointHom z = integerPoint z :=
  rfl

@[simp]
theorem integerPoint_re (z : IntegerPlane) : (integerPoint z).re = z 0 := by
  simp [integerPoint]

@[simp]
theorem integerPoint_im (z : IntegerPlane) : (integerPoint z).im = z 1 := by
  simp [integerPoint]

/-- Integer coordinates determine the embedded point uniquely. -/
theorem integerPoint_injective : Injective integerPoint := by
  intro x y hxy
  funext i
  fin_cases i
  · have h0 : (x 0 : ℝ) = (y 0 : ℝ) := by
      simpa only [integerPoint_re] using congrArg Complex.re hxy
    exact_mod_cast h0
  · have h1 : (x 1 : ℝ) = (y 1 : ℝ) := by
      simpa only [integerPoint_im] using congrArg Complex.im hxy
    exact_mod_cast h1

/-- The additive subgroup of points having two integer coordinates. -/
def integerLattice : AddSubgroup Plane :=
  AddSubgroup.map integerPointHom ⊤

/-- A point of the real plane lies in the integer lattice exactly when it has an integer-coordinate
preimage. -/
theorem mem_integerLattice_iff {x : Plane} :
    x ∈ integerLattice ↔ ∃ z : IntegerPlane, integerPoint z = x := by
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, by simp, rfl⟩

/-- Predicate form of membership in the embedded integer lattice. -/
def IsIntegerPoint (x : Plane) : Prop :=
  x ∈ integerLattice

/-- A nonempty polygonal region, represented by its regular-closed support. -/
structure PolygonalRegion where
  /-- The closed support used for measure-theoretic tilings. -/
  support : Set Plane
  /-- The support has a finite triangulation. -/
  isPolygonal : Tiling.IsPolygonal support
  /-- Polygonal regions in the paper are nonempty. -/
  nonempty : support.Nonempty

namespace PolygonalRegion

/-- The bounded open polygonal set corresponding to the regular-closed support. -/
def openCarrier (K : PolygonalRegion) : Set Plane :=
  interior K.support

/-- The open and regular-closed representatives agree almost everywhere. -/
theorem openCarrier_ae_eq (K : PolygonalRegion) :
    K.openCarrier =ᵐ[volume] K.support :=
  K.isPolygonal.interior_ae_eq

/-- A polygonal region as a single prototile. -/
def prototile (K : PolygonalRegion) : Prototile Plane where
  support := K.support
  measurableSet_support := K.isPolygonal.isClosed.measurableSet
  nonempty_support := K.nonempty

/-- The unit-labelled prototile family associated to a polygonal region. -/
def prototileFamily (K : PolygonalRegion) : PrototileFamily Plane Unit :=
  fun _ ↦ K.prototile

/-- Regard a set of translation vectors as a unit-labelled placement set. -/
def placements (_K : PolygonalRegion) (T : Set Plane) : ProtoTiling Plane Unit :=
  {p | p.1 ∈ T}

@[simp]
theorem mem_placements_iff {K : PolygonalRegion} {T : Set Plane}
    {p : Placement Plane Unit} :
    p ∈ K.placements T ↔ p.1 ∈ T :=
  Iff.rfl

@[simp]
theorem placedTile_eq (K : PolygonalRegion) (p : Placement Plane Unit) :
    placedTile K.prototileFamily p = p.1 +ᵥ K.support :=
  rfl

/-- Unit-labelled placements are countable exactly when their translation set is countable. -/
theorem placements_countable (K : PolygonalRegion) {T : Set Plane} (hT : T.Countable) :
    (K.placements T).Countable := by
  let _ : Countable T := hT.to_subtype
  have heq : K.placements T =
      Set.range (fun t : T ↦ ((t : Plane), ())) := by
    ext p
    constructor
    · intro hp
      refine ⟨⟨p.1, hp⟩, ?_⟩
      apply Prod.ext
      · rfl
      · exact Subsingleton.elim _ _
    · rintro ⟨t, rfl⟩
      exact t.2
  rw [heq]
  exact Set.countable_range _

/-- A countable almost-everywhere translational tiling by one polygonal region. -/
def Tiles (K : PolygonalRegion) (T : Set Plane) : Prop :=
  Tiling.IsTiling K.prototileFamily (K.placements T)

/-- The translation set of a monotile tiling is countable. -/
theorem Tiles.countable {K : PolygonalRegion} {T : Set Plane} (hT : K.Tiles T) :
    T.Countable := by
  have hplacements : (K.placements T).Countable :=
    Tiling.IsTiling.countable hT
  have h := hplacements.image Prod.fst
  have heq : Prod.fst '' K.placements T = T := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hx
      exact ⟨(x, ()), hx, rfl⟩
  rwa [heq] at h

end PolygonalRegion

/-- Membership invariance under one specified real translation vector. -/
def SetPeriodicBy (A : Set Plane) (h : Plane) : Prop :=
  ∀ x, x + h ∈ A ↔ x ∈ A

/-- A set admitting one nonzero real period. -/
def SinglyPeriodic (A : Set Plane) : Prop :=
  ∃ h : Plane, h ≠ 0 ∧ SetPeriodicBy A h

/-- A finite disjoint decomposition into subsets carrying nonzero real periods. -/
structure WeakPeriodicDecomposition (A : Set Plane) where
  /-- Number of periodic pieces. -/
  numberOfParts : ℕ
  /-- The pieces of the decomposition. -/
  part : Fin numberOfParts → Set Plane
  /-- A period for each piece. -/
  period : Fin numberOfParts → Plane
  /-- Every selected period is nonzero. -/
  period_ne_zero : ∀ i, period i ≠ 0
  /-- Each piece is invariant under its selected period. -/
  periodic_part : ∀ i, SetPeriodicBy (part i) (period i)
  /-- Distinct pieces are disjoint. -/
  pairwiseDisjoint : Set.PairwiseDisjoint Set.univ part
  /-- The pieces have union exactly `A`. -/
  iUnion_parts : (⋃ i, part i) = A

/-- A set which is a finite disjoint union of singly periodic subsets. -/
def WeaklyPeriodic (A : Set Plane) : Prop :=
  Nonempty (WeakPeriodicDecomposition A)

/-- A set invariant under two linearly independent real translations. -/
def DoublyPeriodic (A : Set Plane) : Prop :=
  ∃ h₁ h₂ : Plane,
    LinearIndependent ℝ ![h₁, h₂] ∧ SetPeriodicBy A h₁ ∧ SetPeriodicBy A h₂

/-- Translating a periodically invariant set preserves the same period. -/
theorem setPeriodicBy_vadd {A : Set Plane} {h : Plane}
    (ha : Plane) (hA : SetPeriodicBy A h) :
    SetPeriodicBy (ha +ᵥ A) h := by
  intro x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem]
  simpa only [vadd_eq_add, neg_smul, one_smul, add_assoc] using hA (-ha + x)

/-- A translate of a singly periodic set is singly periodic. -/
theorem SinglyPeriodic.vadd {A : Set Plane} (hA : SinglyPeriodic A) (a : Plane) :
    SinglyPeriodic (a +ᵥ A) := by
  obtain ⟨h, hh, hperiod⟩ := hA
  exact ⟨h, hh, setPeriodicBy_vadd a hperiod⟩

/-- Relative rationality in the sense of the paper: all vertex differences from one vertex have
rational real and imaginary coordinates. -/
def IsRelativelyRational (K : PolygonalRegion) : Prop :=
  ∃ v ∈ vertexSet K.support,
    ∀ w ∈ vertexSet K.support, IsRationalPoint (w - v)

/-- A rational presentation with one common positive denominator for all relative vertices. -/
structure RationalPolygonalRegion extends PolygonalRegion where
  /-- The vertex chosen as the affine origin. -/
  anchor : Plane
  /-- The anchor is an intrinsic vertex. -/
  anchor_mem_vertex : anchor ∈ vertexSet support
  /-- A common denominator for every relative vertex. -/
  denominator : ℕ
  /-- The common denominator is positive. -/
  denominator_pos : 0 < denominator
  /-- After translation to the anchor and dilation, all intrinsic vertices are integral. -/
  vertex_integral : ∀ w ∈ vertexSet support,
    IsIntegerPoint ((denominator : ℝ) • (w - anchor))

namespace RationalPolygonalRegion

/-- The common denominator, viewed as a nonzero real scalar. -/
theorem denominator_cast_ne_zero (K : RationalPolygonalRegion) :
    (K.denominator : ℝ) ≠ 0 := by
  exact_mod_cast K.denominator_pos.ne'

/-- Translate the chosen anchor to the origin and clear the common vertex denominator. -/
def normalizedSupport (K : RationalPolygonalRegion) : Set Plane :=
  (K.denominator : ℝ) • (-K.anchor +ᵥ K.support)

/-- The polygonal region obtained by the paper's rational affine normalization. -/
def normalizedRegion (K : RationalPolygonalRegion) : PolygonalRegion where
  support := K.normalizedSupport
  isPolygonal := by
    apply IsPolygonal.smul (K.isPolygonal.vadd (-K.anchor))
    exact K.denominator_cast_ne_zero
  nonempty := by
    obtain ⟨x, hx⟩ := K.nonempty
    have hxtranslated : -K.anchor +ᵥ x ∈ -K.anchor +ᵥ K.support := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      have hpoint : -(-K.anchor) +ᵥ (-K.anchor +ᵥ x) = x := by
        simp only [vadd_eq_add]
        abel
      rwa [hpoint]
    exact ⟨(K.denominator : ℝ) • (-K.anchor +ᵥ x),
      ⟨-K.anchor +ᵥ x, hxtranslated, rfl⟩⟩

@[simp]
theorem normalizedRegion_support (K : RationalPolygonalRegion) :
    K.normalizedRegion.support = K.normalizedSupport :=
  rfl

/-- Translation vectors corresponding to normalized copies of the tile. -/
noncomputable def normalizedTranslation (K : RationalPolygonalRegion) (t : Plane) : Plane :=
  (K.denominator : ℝ) • (K.anchor + t)

/-- Normalize every translation vector in a candidate tiling. -/
noncomputable def normalizedTranslations (K : RationalPolygonalRegion)
    (T : Set Plane) : Set Plane :=
  K.normalizedTranslation '' T

@[simp]
theorem mem_normalizedTranslations_iff {K : RationalPolygonalRegion}
    {T : Set Plane} {x : Plane} :
    x ∈ K.normalizedTranslations T ↔
      ∃ t ∈ T, K.normalizedTranslation t = x :=
  Iff.rfl

/-- Rational normalization is injective on translation vectors. -/
theorem normalizedTranslation_injective (K : RationalPolygonalRegion) :
    Function.Injective K.normalizedTranslation := by
  intro x y hxy
  apply add_left_cancel (a := K.anchor)
  exact (smul_right_injective Plane K.denominator_cast_ne_zero) hxy

/-- Inverse affine change of coordinates on translation vectors. -/
noncomputable def denormalizedTranslation (K : RationalPolygonalRegion)
    (t : Plane) : Plane :=
  (K.denominator : ℝ)⁻¹ • t - K.anchor

/-- Apply the inverse normalization to every translation vector. -/
noncomputable def denormalizedTranslations (K : RationalPolygonalRegion)
    (T : Set Plane) : Set Plane :=
  K.denormalizedTranslation '' T

@[simp]
theorem mem_denormalizedTranslations_iff {K : RationalPolygonalRegion}
    {T : Set Plane} {x : Plane} :
    x ∈ K.denormalizedTranslations T ↔
      ∃ t ∈ T, K.denormalizedTranslation t = x :=
  Iff.rfl

@[simp]
theorem denormalizedTranslation_normalizedTranslation
    (K : RationalPolygonalRegion) (t : Plane) :
    K.denormalizedTranslation (K.normalizedTranslation t) = t := by
  simp only [denormalizedTranslation, normalizedTranslation, ← mul_smul,
    inv_mul_cancel₀ K.denominator_cast_ne_zero, one_smul]
  abel

@[simp]
theorem normalizedTranslation_denormalizedTranslation
    (K : RationalPolygonalRegion) (t : Plane) :
    K.normalizedTranslation (K.denormalizedTranslation t) = t := by
  simp only [normalizedTranslation, denormalizedTranslation]
  rw [show K.anchor + ((K.denominator : ℝ)⁻¹ • t - K.anchor) =
      (K.denominator : ℝ)⁻¹ • t by abel]
  rw [← mul_smul, mul_inv_cancel₀ K.denominator_cast_ne_zero, one_smul]

/-- Inverse normalization is injective on translation vectors. -/
theorem denormalizedTranslation_injective (K : RationalPolygonalRegion) :
    Function.Injective K.denormalizedTranslation := by
  intro x y hxy
  have := congrArg K.normalizedTranslation hxy
  simpa only [K.normalizedTranslation_denormalizedTranslation] using this

/-- Every intrinsic vertex of the normalized region is an integer point. -/
theorem normalized_vertex_integral (K : RationalPolygonalRegion) :
    ∀ w ∈ vertexSet K.normalizedSupport, IsIntegerPoint w := by
  intro w hw
  rw [normalizedSupport, vertexSet_smul _ K.denominator_cast_ne_zero,
    vertexSet_vadd] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hu
  have hu' := K.vertex_integral (-(-K.anchor) +ᵥ u) hu
  convert hu' using 1
  simp only [vadd_eq_add]
  congr 1
  abel

/-- A common-denominator rational presentation implies the paper's relative-rationality
predicate. -/
theorem isRelativelyRational (K : RationalPolygonalRegion) :
    IsRelativelyRational K.toPolygonalRegion := by
  refine ⟨K.anchor, K.anchor_mem_vertex, ?_⟩
  intro w hw
  obtain ⟨z, hz⟩ := mem_integerLattice_iff.mp (K.vertex_integral w hw)
  have hn : (K.denominator : ℝ) ≠ 0 := by
    exact_mod_cast K.denominator_pos.ne'
  have hre : (z 0 : ℝ) = (K.denominator : ℝ) * (w - K.anchor).re := by
    simpa only [integerPoint_re, Complex.smul_re, smul_eq_mul] using
      congrArg Complex.re hz
  have him : (z 1 : ℝ) = (K.denominator : ℝ) * (w - K.anchor).im := by
    simpa only [integerPoint_im, Complex.smul_im, smul_eq_mul] using
      congrArg Complex.im hz
  refine ⟨(z 0 : ℚ) / K.denominator, (z 1 : ℚ) / K.denominator, ?_, ?_⟩
  · rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
      eq_div_iff hn]
    simpa only [mul_comm] using hre.symm
  · rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
      eq_div_iff hn]
    simpa only [mul_comm] using him.symm

end RationalPolygonalRegion

end Tiling.RationalPolygonal
