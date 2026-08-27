import ChallengeDeps

/-!
# Comparator challenge

This file is the trusted challenge side.  Its sole theorem is deliberately left as `sorry`:
`leanprover/comparator` compares its statement with the theorem in `Solution.lean`, then checks the
solution's transitive axiom closure independently.
-/

namespace DeDiosGreenfeldComparator

open MeasureTheory

/-- **Periodic tiling theorem for rational polygonal sets.**

If the rational polygonal set `Ω` tiles the real plane by translations at all, then it also tiles
using a translation set invariant under two linearly independent periods.  The ambient measure is
Mathlib's Lebesgue measure `volume` on `ℂ ≃ ℝ²`. -/
theorem periodic_tiling_of_rational_polygon
    (Ω : Set Plane) (hΩ : RationalPolygon Ω) :
    (∃ T : Set Plane, TranslationTiling volume Ω T) →
      ∃ T : Set Plane, Periodic T ∧ TranslationTiling volume Ω T := by
  sorry

end DeDiosGreenfeldComparator
