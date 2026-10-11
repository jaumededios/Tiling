import Tiling.AxisParallel.Core
import Tiling.AxisParallel.Foundations.RationalMeshCore
import Tiling.AxisParallel.Terminal.DirectionalCore

/-!
# Rational directional slices

Definition-only data for the rational finer-structure theorem. Rational affine lines are represented
by quotients of the real plane by the real span of a nonzero rational direction.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Terminal

/-- A nonzero direction with two rational coordinates. -/
abbrev RationalDirection := {u : Fin 2 → ℚ // u ≠ 0}

namespace RationalDirection

/-- The rational coordinate function of a rational direction. -/
def coordinates (u : RationalDirection) : Fin 2 → ℚ :=
  u.1

/-- Embed a rational direction into the real plane. -/
def toPlane (u : RationalDirection) : Tiling.Plane :=
  (u.coordinates 0 : ℝ) + (u.coordinates 1 : ℝ) * Complex.I

/-- The rational coordinates of an integer linear combination of two directions. -/
def linearCombination
    (lambda gamma : RationalDirection) (k l : ℤ) : Fin 2 → ℚ :=
  fun i ↦ (k : ℚ) * lambda.coordinates i +
    (l : ℚ) * gamma.coordinates i

end RationalDirection

/-- The additive subgroup consisting of the real line parallel to `u`. -/
def realDirectionSubgroup (u : RationalDirection) : AddSubgroup Tiling.Plane where
  carrier := {x | ∃ r : ℝ, x = r • u.toPlane}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨r, rfl⟩ ⟨s, rfl⟩
    refine ⟨r + s, ?_⟩
    module
  neg_mem' := by
    rintro x ⟨r, rfl⟩
    refine ⟨-r, ?_⟩
    module

/-- Scale an integer lattice point onto the mesh of denominator `d`. -/
noncomputable abbrev rationalScale :=
  Tiling.AxisParallel.RationalMesh.rationalScale

/-- The planar lattice mesh of denominator `d`. -/
abbrev rationalMesh := Tiling.AxisParallel.RationalMesh.rationalMesh

/-- Every point of `S` lies on the mesh of denominator `d`. -/
abbrev OnRationalMesh := Tiling.AxisParallel.RationalMesh.OnRationalMesh

/-- Affine lines parallel to a rational direction, represented by their quotient classes. -/
abbrev RationalSlice (u : RationalDirection) :=
  Tiling.Plane ⧸ realDirectionSubgroup u

namespace RationalSlice

/-- The affine-line carrier represented by a rational slice. -/
def carrier {u : RationalDirection} (Q : RationalSlice u) : Set Tiling.Plane :=
  TranslationalTilings.quotientCoset (realDirectionSubgroup u) Q

/-- Translate a rational affine line by a planar vector. -/
def vadd {u : RationalDirection} (Q : RationalSlice u)
    (a : Tiling.Plane) : RationalSlice u :=
  Q + QuotientAddGroup.mk' (realDirectionSubgroup u) a

/-- The centres of `T` lying on the represented affine line. -/
def centres {u : RationalDirection} (Q : RationalSlice u)
    (T : Set Tiling.Plane) : Set Tiling.Plane :=
  T ∩ Q.carrier

end RationalSlice

/-- A complete transverse orbit of nonempty periodic rational slices. -/
structure RationalSliceOrbit
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane)
    (within transverse : RationalDirection) where
  phases : Set (RationalSlice within)
  phase_iff_nonempty : ∀ Q,
    Q ∈ phases ↔ (Q.centres T).Nonempty
  phases_nonempty : phases.Nonempty
  slice_periodic : ∀ Q, Q ∈ phases →
    Tiling.RationalPolygonal.SetPeriodicBy
      (Q.centres T) within.toPlane
  phase_translate_mem : ∀ Q, Q ∈ phases → ∀ n : ℤ,
    Q.vadd (n • transverse.toPlane) ∈ phases
  regularSupport_transport : ∀ Q, Q ∈ phases → ∀ n : ℤ,
    n • transverse.toPlane +ᵥ
        Tiling.AxisParallel.regularSupport K (Q.centres T) =
      Tiling.AxisParallel.regularSupport K
        ((Q.vadd (n • transverse.toPlane)).centres T)

/-- The rational directional decomposition produced from an exact discrete rasterization. -/
structure RationalDirectionalDecomposition
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane) where
  lambda : RationalDirection
  gamma : RationalDirection
  basisIndependent :
    LinearIndependent ℝ ![lambda.toPlane, gamma.toPlane]
  numberOfParts : ℕ
  number_zero_iff : numberOfParts = 0 ↔ T = ∅
  part : Fin numberOfParts → Set Tiling.Plane
  part_nonempty : ∀ i, (part i).Nonempty
  parts_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ part
  parts_union : (⋃ i, part i) = T
  lambdaCoefficient : Fin numberOfParts → ℤ
  gammaCoefficient : Fin numberOfParts → ℤ
  lambdaCoefficient_ne_zero : ∀ i, lambdaCoefficient i ≠ 0
  direction : Fin numberOfParts → RationalDirection
  direction_coordinates : ∀ i,
    (direction i).coordinates =
      RationalDirection.linearCombination lambda gamma
        (lambdaCoefficient i) (gammaCoefficient i)
  orbit : ∀ i,
    RationalSliceOrbit K (part i) (direction i) gamma

/-- The strict-distance graph on `S` has at least two connected classes. -/
def IsGappedSlice (radius : ℝ) (S : Set Tiling.Plane) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S,
    ¬ Relation.EqvGen
      (fun a b : Tiling.Plane ↦ a ∈ S ∧ b ∈ S ∧ dist a b < radius) x y

namespace RationalSliceOrbit

/-- Existing phases whose corresponding original slice is gapped. -/
def gappedPhases
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {within transverse : RationalDirection}
    (O : RationalSliceOrbit K T within transverse)
    (originalSlice : RationalSlice within → Set Tiling.Plane)
    (radius : ℝ) : Set (RationalSlice within) :=
  {Q | Q ∈ O.phases ∧ IsGappedSlice radius (originalSlice Q)}

/-- Existing phases whose corresponding original slice is not gapped. -/
def noGapPhases
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {within transverse : RationalDirection}
    (O : RationalSliceOrbit K T within transverse)
    (originalSlice : RationalSlice within → Set Tiling.Plane)
    (radius : ℝ) : Set (RationalSlice within) :=
  O.phases \ O.gappedPhases originalSlice radius

/-- Centres in every transverse translate of every gapped seed phase. -/
def gappedCentres
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {within transverse : RationalDirection}
    (O : RationalSliceOrbit K T within transverse)
    (originalSlice : RationalSlice within → Set Tiling.Plane)
    (radius : ℝ) : Set Tiling.Plane :=
  ⋃ Q : O.gappedPhases originalSlice radius,
    ⋃ n : ℤ, (Q.1.vadd (n • transverse.toPlane)).centres T

/-- Centres in every transverse translate of every non-gapped seed phase. -/
def noGapCentres
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {within transverse : RationalDirection}
    (O : RationalSliceOrbit K T within transverse)
    (originalSlice : RationalSlice within → Set Tiling.Plane)
    (radius : ℝ) : Set Tiling.Plane :=
  ⋃ Q : O.noGapPhases originalSlice radius,
    ⋃ n : ℤ, (Q.1.vadd (n • transverse.toPlane)).centres T

end RationalSliceOrbit

end Tiling.AxisParallel.Terminal
