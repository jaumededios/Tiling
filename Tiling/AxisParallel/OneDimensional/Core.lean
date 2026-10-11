import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Sets.VietorisTopology

set_option linter.style.header false

open Function MeasureTheory Set
open scoped Pointwise

namespace Tiling.AxisParallel.OneDimensional

/-- A countable measure tiling by translates of `B` on the measurable target `X`. -/
def LineTilesOn (B L X : Set ℝ) : Prop :=
  MeasurableSet B ∧ MeasurableSet X ∧ L.Countable ∧
    Set.Pairwise L
      (MeasureTheory.AEDisjoint MeasureTheory.volume on
        ((· +ᵥ B) : ℝ → Set ℝ)) ∧
    ∀ᵐ x ∂MeasureTheory.volume,
      (x ∈ X ↔ ∃ l : L, x ∈ ((l : ℝ) +ᵥ B))

/-- A measure tiling of the whole real line by translates of `B`. -/
def LineTiles (B L : Set ℝ) : Prop :=
  LineTilesOn B L Set.univ

/-- A literal finite union of bounded nondegenerate open intervals. -/
def IsFiniteIntervalRegion (B : Set ℝ) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → ℝ),
    (∀ i, a i < b i) ∧ B = ⋃ i, Set.Ioo (a i) (b i)

/-- Translate a chosen centre of a line tiling to the origin. -/
def normalizeLineTiling (L : Set ℝ) (l0 : ℝ) : Set ℝ :=
  (-l0) +ᵥ L

/-- A line tiling with a distinguished centre normalized to zero. -/
structure NormalizedLineTiling (B : Set ℝ) where
  centres : Set ℝ
  tiles : LineTiles B centres
  zero_mem : 0 ∈ centres

end Tiling.AxisParallel.OneDimensional
