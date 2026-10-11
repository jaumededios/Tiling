import Tiling.Topology.FellCore

set_option linter.style.header false

open Filter Set

namespace Tiling.AxisParallel.Topology

/-- Literal pairwise separation by at least `delta`. -/
abbrev IsUniformlySeparated {E : Type*} [PseudoMetricSpace E]
    (delta : ℝ) (S : Set E) : Prop :=
  Tiling.Topology.IsUniformlySeparated delta S

/-- Adjoin the point at infinity to a closed set, using the preserved proved generic body. -/
abbrev fellCompactification
    {E : Type*} [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E]
    (S : Set E) (hS : IsClosed S) :
    TopologicalSpace.NonemptyCompacts (OnePoint E) :=
  Tiling.Topology.fellCompactification S hS

/-- Vietoris convergence after adjoining infinity, with closedness included in the predicate. -/
abbrev LocallyFellConverges
    {E : Type*} [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E]
    (S : ℕ → Set E) (L : Set E) : Prop :=
  Tiling.Topology.LocallyFellConverges S L

end Tiling.AxisParallel.Topology
