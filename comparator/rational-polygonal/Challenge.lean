import ChallengeDeps

/-!
# Comparator challenge

This file is the trusted challenge side.  Its sole theorem is deliberately left as `sorry`:
`leanprover/comparator` compares its statement with the theorem in `Solution.lean`, then checks the
solution's transitive axiom closure independently.
-/

namespace DeDiosGreenfeldComparator

/-- Every translationally tileable rational polygon admits a doubly periodic tiling. -/
theorem periodic_tiling_of_rational_polygon : PeriodicTilingTheorem := by
  sorry

end DeDiosGreenfeldComparator
