import Tiling.AxisParallel.Discrete.Core
import Tiling.RationalPolygonal.DiscreteCarrier
import TranslationalTilings.Slicing

/-!
# Directional slice data

This file contains the definition-only interface for the discrete finer-structure theorem.
Its slices are the existing quotient-indexed lattice slices from `TranslationalTilings.Slicing`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Set

namespace Tiling.AxisParallel.Terminal

/-- A primitive lattice direction together with its coordinates in a chosen lattice basis. -/
structure DiscreteDirection
    (h g : TranslationalTilings.Plane) where
  primitiveVector : TranslationalTilings.Plane
  primitive : TranslationalTilings.IsPrimitive primitiveVector
  hCoefficient : ℤ
  gCoefficient : ℤ
  hCoefficient_ne_zero : hCoefficient ≠ 0
  multiple : ℤ
  multiple_ne_zero : multiple ≠ 0
  period_eq :
    hCoefficient • h + gCoefficient • g = multiple • primitiveVector

namespace DiscreteDirection

/-- The period represented by the integer coordinates of a discrete direction. -/
def period {h g : TranslationalTilings.Plane}
    (d : DiscreteDirection h g) : TranslationalTilings.Plane :=
  d.hCoefficient • h + d.gCoefficient • g

end DiscreteDirection

/-- The existing lattice slice, exposed under the terminal theorem's vocabulary. -/
abbrev DiscreteSlice
    (u : TranslationalTilings.Plane)
    (Q : TranslationalTilings.Plane ⧸
      TranslationalTilings.directionSubgroup u)
    (A : Set TranslationalTilings.Plane) : Set TranslationalTilings.Plane :=
  TranslationalTilings.slicePattern u Q A

/-- A complete transverse orbit of nonempty periodic slices and their exact tile carriers. -/
structure DiscreteSliceOrbit
    (F : Finset TranslationalTilings.Plane)
    (A : Set TranslationalTilings.Plane)
    (u within transverse : TranslationalTilings.Plane) where
  phases : Set (TranslationalTilings.Plane ⧸
    TranslationalTilings.directionSubgroup u)
  phase_iff_nonempty : ∀ Q,
    Q ∈ phases ↔ (DiscreteSlice u Q A).Nonempty
  phases_nonempty : phases.Nonempty
  within_ne_zero : within ≠ 0
  within_parallel : TranslationalTilings.Commensurable within u
  slice_periodic : ∀ Q, Q ∈ phases →
    Tiling.RationalPolygonal.DiscretePeriodicBy
      (DiscreteSlice u Q A) within
  phase_translate_mem : ∀ Q, Q ∈ phases → ∀ n : ℤ,
    Q + QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup u)
      (n • transverse) ∈ phases
  carrier_transport : ∀ Q, Q ∈ phases → ∀ n : ℤ,
    TranslationalTilings.translateSet (n • transverse)
      (Tiling.RationalPolygonal.discreteCarrier F
        (DiscreteSlice u Q A)) =
      Tiling.RationalPolygonal.discreteCarrier F
        (DiscreteSlice u
          (Q + QuotientAddGroup.mk'
            (TranslationalTilings.directionSubgroup u) (n • transverse)) A)

/-- The complete output datum of the discrete finer-structure theorem. -/
structure DiscreteFinerStructureData
    (F : Finset TranslationalTilings.Plane)
    (A E : Set TranslationalTilings.Plane) (ell : ℕ) where
  tile_nonempty : F.Nonempty
  ell_pos : 0 < ell
  target_periodic : TranslationalTilings.SetScalarPeriodic ell E
  tiles : TranslationalTilings.Tiles F A E
  h : TranslationalTilings.Plane
  g : TranslationalTilings.Plane
  independent : TranslationalTilings.wedge h g ≠ 0
  numberOfParts : ℕ
  number_zero_iff : numberOfParts = 0 ↔ A = ∅
  part : Fin numberOfParts → Set TranslationalTilings.Plane
  part_nonempty : ∀ i, (part i).Nonempty
  pairwiseDisjoint : Set.PairwiseDisjoint Set.univ part
  iUnion_parts : (⋃ i, part i) = A
  direction : Fin numberOfParts → DiscreteDirection h g
  sliceOrbit : ∀ i,
    DiscreteSliceOrbit F (part i) (direction i).primitiveVector
      (direction i).period g

end Tiling.AxisParallel.Terminal
