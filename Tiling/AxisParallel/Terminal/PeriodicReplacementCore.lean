import Tiling.AxisParallel.Core

/-!
# Periodic replacement data

This definition-only module records a tiling of a fixed target whose centre set has a genuine
rank-two lattice of literal periods.
-/

namespace Tiling.AxisParallel.Terminal

/-- A replacement tiling of `E` together with a full-rank lattice of centre periods. -/
structure PeriodicReplacement
    (K : Tiling.AxisParallel.Region) (E : Set Tiling.Plane) where
  centres : Set Tiling.Plane
  tiles : Tiling.AxisParallel.TilesOn K centres E
  lattice : Tiling.AxisParallel.PlanarLattice
  lattice_periods : lattice.toAddSubgroup ≤
    Tiling.AxisParallel.periodGroup centres

end Tiling.AxisParallel.Terminal
