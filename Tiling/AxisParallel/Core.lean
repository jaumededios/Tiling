import Mathlib.MeasureTheory.Group.AEStabilizer
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Tiling.RationalPolygonal.Basic
import Tiling.Geometry.PackingTopology
import Tiling.Geometry.Periodicity
import Tiling.Geometry.PolygonalCarrier

set_option linter.style.header false

open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel

/-- The two coordinate axes used throughout the axis-parallel development. -/
inductive Axis
  | horizontal
  | vertical
  deriving DecidableEq

namespace Axis

/-- Exchange the two coordinate axes. -/
def swap : Axis → Axis
  | horizontal => vertical
  | vertical => horizontal

/-- Coordinate in the direction of the labelled axis. -/
def coord : Axis → Tiling.Plane → ℝ
  | horizontal => Complex.re
  | vertical => Complex.im

/-- Coordinate transverse to the labelled axis. -/
def transverseCoord : Axis → Tiling.Plane → ℝ
  | horizontal => Complex.im
  | vertical => Complex.re

end Axis

/-- The real-linear coordinate interchange `(x,y) ↦ (y,x)`. -/
def coordinateSwap : Tiling.Plane ≃L[ℝ] Tiling.Plane :=
  Complex.equivRealProdCLM.trans
    ((ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).trans Complex.equivRealProdCLM.symm)

@[simp] theorem coordinateSwap_re (z : Tiling.Plane) :
    (coordinateSwap z).re = z.im := rfl

@[simp] theorem coordinateSwap_im (z : Tiling.Plane) :
    (coordinateSwap z).im = z.re := rfl

@[simp] theorem coordinateSwap_apply_apply (z : Tiling.Plane) :
    coordinateSwap (coordinateSwap z) = z := by
  apply Complex.ext <;> simp

private def coordinateSwapLIE : Tiling.Plane ≃ₗᵢ[ℝ] Tiling.Plane where
  toLinearEquiv := coordinateSwap.toLinearEquiv
  norm_map' z := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring

private theorem coordinateSwap_image_rectangle (a b : Tiling.Plane) :
    coordinateSwap '' Complex.Rectangle a b =
      Complex.Rectangle (coordinateSwap a) (coordinateSwap b) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change (coordinateSwap w).re ∈ Set.uIcc a.im b.im ∧
      (coordinateSwap w).im ∈ Set.uIcc a.re b.re
    simpa using hw.symm
  · intro hz
    refine ⟨coordinateSwap z, ?_, coordinateSwap_apply_apply z⟩
    change (coordinateSwap z).re ∈ Set.uIcc a.re b.re ∧
      (coordinateSwap z).im ∈ Set.uIcc a.im b.im
    change z.re ∈ Set.uIcc a.im b.im ∧ z.im ∈ Set.uIcc a.re b.re at hz
    simpa using hz.symm

private theorem coordinateSwap_image_eq_preimage (s : Set Tiling.Plane) :
    coordinateSwap '' s = coordinateSwap ⁻¹' s := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨coordinateSwap z, hz, coordinateSwap_apply_apply z⟩

private noncomputable def coordinateSwapRectangulation {s : Set Tiling.Plane}
    (R : Tiling.Rectangulation s) :
    Tiling.Rectangulation (coordinateSwap '' s) where
  pieces := R.pieces.image (coordinateSwap '' ·)
  isRectangle := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨a, b, hre, him, rfl⟩ := R.isRectangle q hq
    refine ⟨coordinateSwap a, coordinateSwap b, ?_, ?_,
      coordinateSwap_image_rectangle a b⟩
    · simpa using him
    · simpa using hre
  pairwiseAEDisjoint := by
    rw [Finset.coe_image]
    rintro _ ⟨r, hr, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    have hrq : r ≠ q := by
      intro heq
      exact hne (by simp [heq])
    have hd := R.pairwiseAEDisjoint hr hq hrq
    change MeasureTheory.AEDisjoint MeasureTheory.volume
      (coordinateSwap '' r) (coordinateSwap '' q)
    rw [coordinateSwap_image_eq_preimage, coordinateSwap_image_eq_preimage]
    exact hd.preimage coordinateSwapLIE.measurePreserving.quasiMeasurePreserving
  sUnion_eq := by
    calc
      ⋃₀ (R.pieces.image (coordinateSwap '' ·) : Set (Set Tiling.Plane)) =
          coordinateSwap '' ⋃₀ (R.pieces : Set (Set Tiling.Plane)) := by
        ext z
        constructor
        · rintro ⟨u, hu, hzu⟩
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨w, hw, rfl⟩ := hzu
          exact ⟨w, ⟨q, hq, hw⟩, rfl⟩
        · rintro ⟨w, ⟨q, hq, hw⟩, rfl⟩
          exact ⟨coordinateSwap '' q, Finset.mem_image.mpr ⟨q, hq, rfl⟩,
            ⟨w, hw, rfl⟩⟩
      _ = coordinateSwap '' s := congrArg (coordinateSwap '' ·) R.sUnion_eq

private theorem isAxisParallel_coordinateSwap {s : Set Tiling.Plane}
    (hs : Tiling.IsAxisParallel s) :
    Tiling.IsAxisParallel (coordinateSwap '' s) :=
  hs.map coordinateSwapRectangulation

private theorem coordinateSwap_image_triangle {s : Set Tiling.Plane}
    (hs : Tiling.IsTriangle s) :
    Tiling.IsTriangle (coordinateSwap '' s) := by
  obtain ⟨a, b, c, hnondeg, rfl⟩ := hs
  refine ⟨coordinateSwap a, coordinateSwap b, coordinateSwap c, ?_, ?_⟩
  · have harea : Tiling.twiceSignedArea (coordinateSwap a) (coordinateSwap b)
        (coordinateSwap c) = -Tiling.twiceSignedArea a b c := by
      simp [Tiling.twiceSignedArea]
    rw [harea]
    exact neg_ne_zero.mpr hnondeg
  · change coordinateSwap.toLinearMap '' convexHull ℝ {a, b, c} =
      convexHull ℝ {coordinateSwap a, coordinateSwap b, coordinateSwap c}
    rw [coordinateSwap.toLinearMap.image_convexHull]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop

private noncomputable def coordinateSwapTriangulation {s : Set Tiling.Plane}
    (T : Tiling.Triangulation s) :
    Tiling.Triangulation (coordinateSwap '' s) where
  pieces := T.pieces.image (coordinateSwap '' ·)
  isTriangle := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    exact coordinateSwap_image_triangle (T.isTriangle q hq)
  pairwiseAEDisjoint := by
    rw [Finset.coe_image]
    rintro _ ⟨r, hr, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    have hrq : r ≠ q := by
      intro heq
      exact hne (by simp [heq])
    have hd := T.pairwiseAEDisjoint hr hq hrq
    change MeasureTheory.AEDisjoint MeasureTheory.volume
      (coordinateSwap '' r) (coordinateSwap '' q)
    rw [coordinateSwap_image_eq_preimage, coordinateSwap_image_eq_preimage]
    exact hd.preimage coordinateSwapLIE.measurePreserving.quasiMeasurePreserving
  sUnion_eq := by
    calc
      ⋃₀ (T.pieces.image (coordinateSwap '' ·) : Set (Set Tiling.Plane)) =
          coordinateSwap '' ⋃₀ (T.pieces : Set (Set Tiling.Plane)) := by
        ext z
        constructor
        · rintro ⟨u, hu, hzu⟩
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨w, hw, rfl⟩ := hzu
          exact ⟨w, ⟨q, hq, hw⟩, rfl⟩
        · rintro ⟨w, ⟨q, hq, hw⟩, rfl⟩
          exact ⟨coordinateSwap '' q, Finset.mem_image.mpr ⟨q, hq, rfl⟩,
            ⟨w, hw, rfl⟩⟩
      _ = coordinateSwap '' s := congrArg (coordinateSwap '' ·) T.sUnion_eq

private theorem isPolygonal_coordinateSwap {s : Set Tiling.Plane}
    (hs : Tiling.IsPolygonal s) :
    Tiling.IsPolygonal (coordinateSwap '' s) :=
  hs.map coordinateSwapTriangulation

/-- A polygonal region whose support is axis-parallel. -/
structure Region extends Tiling.RationalPolygonal.PolygonalRegion where
  isAxisParallel : Tiling.IsAxisParallel support

namespace Region

/-- The canonical open representative of an axis-parallel region. -/
def openCarrier (K : Region) : Set Tiling.Plane :=
  K.toPolygonalRegion.openCarrier

/-- The intrinsic polygonal vertex set. -/
def vertices (K : Region) : Set Tiling.Plane :=
  Tiling.vertexSet K.support

/-- The finite wrapper around the intrinsic polygonal vertex set. -/
noncomputable def vertexFinset (K : Region) : Finset Tiling.Plane :=
  K.isPolygonal.vertexSet_finite.toFinset

/-- Regard a centre set as the unit-labelled polygonal prototiling by `K`. -/
def polygonalProtoTiling (K : Region) (T : Set Tiling.Plane) :
    Tiling.PolygonalProtoTiling Unit where
  prototiles := K.toPolygonalRegion.prototileFamily
  placements := K.toPolygonalRegion.placements T
  isPolygonal _ := K.isPolygonal

/-- Apply coordinate interchange to the support of a region. -/
noncomputable def coordinateSwap (K : Region) : Region where
  support := Tiling.AxisParallel.coordinateSwap '' K.support
  isPolygonal := isPolygonal_coordinateSwap K.isPolygonal
  nonempty := K.nonempty.image Tiling.AxisParallel.coordinateSwap
  isAxisParallel := isAxisParallel_coordinateSwap K.isAxisParallel

theorem vertices_eq_vertexSet (K : Region) :
    K.vertices = Tiling.vertexSet K.support := rfl

theorem coe_vertexFinset (K : Region) :
    (K.vertexFinset : Set Tiling.Plane) = K.vertices := by
  classical
  simp [vertexFinset, vertices]

end Region

/-- The raw open union of translates selected by a centre set. -/
abbrev openUnion (K : Region) (S : Set Tiling.Plane) : Set Tiling.Plane :=
  Tiling.Polygonal.openUnion K.toPolygonalRegion S

/-- The regular-open support of a placement subfamily. -/
abbrev regularSupport (K : Region) (S : Set Tiling.Plane) : Set Tiling.Plane :=
  Tiling.Polygonal.regularSupport K.toPolygonalRegion S

/-- A countable packing whose raw open union equals the target almost everywhere. -/
abbrev TilesOn (K : Region) (S D : Set Tiling.Plane) : Prop :=
  Tiling.Polygonal.TilesOn K.toPolygonalRegion S D

/-- A regular-open set whose boundary has a locally finite axis-parallel segment presentation. -/
def IsLocallyAxisParallelPolygonal (D : Set Tiling.Plane) : Prop :=
  IsOpen D ∧ interior (closure D) = D ∧
    ∃ G : Set (Set Tiling.Plane),
      (∀ g ∈ G, ∃ a b : Tiling.Plane,
        a ≠ b ∧ (a.re = b.re ∨ a.im = b.im) ∧ g = segment ℝ a b) ∧
      frontier D = ⋃₀ G ∧
      ∀ Q : Set Tiling.Plane, Bornology.IsBounded Q →
        {g : Set Tiling.Plane | g ∈ G ∧ (g ∩ Q).Nonempty}.Finite

/-- A boundary point at which the boundary is not locally a straight line. -/
abbrev IsProperVertex (D : Set Tiling.Plane) (x : Tiling.Plane) : Prop :=
  Tiling.Polygonal.IsProperVertex D x

/-- The intrinsic proper-vertex set of a planar carrier. -/
abbrev properVertices (D : Set Tiling.Plane) : Set Tiling.Plane :=
  Tiling.Polygonal.properVertices D

/-- Finite local complexity in its native bounded-difference form. -/
abbrev HasFLC {E : Type*} [NormedAddCommGroup E] (S : Set E) : Prop :=
  Tiling.Polygonal.HasFLC S

/-- A full-rank integer lattice specified by two real-linearly independent vectors. -/
abbrev PlanarLattice := Tiling.Polygonal.PlanarLattice

namespace PlanarLattice

/-- The additive subgroup generated by the two lattice basis vectors. -/
abbrev toAddSubgroup (L : PlanarLattice) : AddSubgroup Tiling.Plane :=
  Tiling.Polygonal.PlanarLattice.toAddSubgroup L

/-- The real basis canonically determined by the two generators of a planar lattice. -/
noncomputable def realBasis (L : PlanarLattice) : Module.Basis (Fin 2) ℝ Tiling.Plane :=
  basisOfLinearIndependentOfCardEqFinrank L.independent
    Complex.finrank_real_complex.symm

@[simp] theorem coe_realBasis (L : PlanarLattice) :
    (L.realBasis : Fin 2 → Tiling.Plane) = L.basis :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

@[simp] theorem realBasis_apply (L : PlanarLattice) (i : Fin 2) :
    L.realBasis i = L.basis i := congrFun L.coe_realBasis i

/-- The integer span of the canonical real basis is the lattice's additive subgroup. -/
theorem span_realBasis_toAddSubgroup (L : PlanarLattice) :
    (Submodule.span ℤ (Set.range L.realBasis)).toAddSubgroup = L.toAddSubgroup := by
  rw [Submodule.span_int_eq_addSubgroupClosure, toAddSubgroup, L.coe_realBasis]
  rfl

end PlanarLattice

/-- The literal translation stabilizer of a set. -/
abbrev periodGroup {E : Type*} [AddCommGroup E] (S : Set E) : AddSubgroup E :=
  Tiling.Polygonal.periodGroup S

theorem periodGroup_isAddSubgroup {E : Type*} [AddCommGroup E]
    (S : Set E) (u : E) : u ∈ periodGroup S ↔ u +ᵥ S = S :=
  Iff.rfl

/-- The almost-everywhere translation stabilizer under planar Lebesgue measure. -/
abbrev aePeriodGroup (S : Set Tiling.Plane) : AddSubgroup Tiling.Plane :=
  Tiling.Polygonal.aePeriodGroup S

/-- Literal periodicity under a full-rank planar lattice. -/
abbrev IsLatticePeriodic (S : Set Tiling.Plane) : Prop :=
  Tiling.Polygonal.IsLatticePeriodic S

/-- A finite disjoint union of nonempty lattice-periodic pieces. -/
abbrev IsQuasiPeriodic (S : Set Tiling.Plane) : Prop :=
  Tiling.Polygonal.IsQuasiPeriodic S

/-- A complete axis-parallel column of centres for `K`. -/
def IsCenterColumn (axis : Axis) (K : Region) (C : Set Tiling.Plane) : Prop :=
  Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements C) ∧
    C.Nonempty ∧
    (∃ c : ℝ, ∀ z ∈ C, axis.transverseCoord z = c) ∧
    ∀ a : ℝ,
      (match axis with
        | .horizontal => (a : ℂ)
        | .vertical => (a : ℂ) * Complex.I) +ᵥ regularSupport K C =
        regularSupport K C

theorem hasFLC_iff_boundedDifferences
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E] (S : Set E) :
    HasFLC S ↔
      (∀ Q : Set E, Bornology.IsBounded Q → (S ∩ Q).Finite) ∧
      ∀ R : ℝ, 0 < R → ((S - S) ∩ Metric.closedBall 0 R).Finite :=
  Iff.rfl

end Tiling.AxisParallel
