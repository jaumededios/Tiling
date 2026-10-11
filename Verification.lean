/-
Copyright (c) 2026 Tiling contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tiling contributors
-/
import Solution
import AxisParallelComparator.Solution
import AxisParallelComputabilityComparator.Solution
import RationalSlopesComparator.Solution
import Tiling.RationalSlopes.Main
import Tiling.RationalPolygonal.Main
import TranslationalTilings.Main

/-!
# Public theorem axiom audit

Check the complete proof dependencies of the comparator solutions and the
paper-facing library results. Challenge modules are intentionally not imported.
-/

run_cmd
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``DeDiosPontGrebikGreenfeldMadridComparator.periodic_tiling_of_rational_polygon,
    ``AxisParallelComparator.flc_tiling_weakly_periodic,
    ``AxisParallelComparator.periodic_tiling_of_flc,
    ``AxisParallelComparator.exists_minimal_tiling_in_hull,
    ``AxisParallelComparator.earthquake_decomposition,
    ``AxisParallelComparator.minimal_tiling_structure,
    ``AxisParallelComparator.minimal_tiling_weakly_periodic,
    ``AxisParallelComparator.quasi_periodic_tiling_with_common_period,
    ``AxisParallelComparator.finitely_many_tectonic_plates,
    ``AxisParallelComparator.earthquake_slabs_periodic,
    ``AxisParallelComparator.proper_cylinder_finite_horizontal_complexity,
    ``AxisParallelComparator.non_flc_earthquake_limit,
    ``AxisParallelComparator.non_flc_earthquake_limit_in_lattice,
    ``AxisParallelComparator.non_flc_finite_horizontal_complexity_limit,
    ``AxisParallelComputabilityComparator.rational_tiling_computable,
    ``AxisParallelComputabilityComparator.tiling_computable_relative,
    ``RationalSlopesComparator.minimal_finite_local_complexity_tiling_is_weakly_periodic,
    ``RationalSlopesComparator.finite_local_complexity_tiling_has_periodic_replacement,
    ``RationalSlopesComparator.minimal_plane_tiling_has_structure,
    ``RationalSlopesComparator.minimal_plane_tiling_is_weakly_periodic,
    ``RationalSlopesComparator.tileable_rational_slopes_has_quasi_periodic_tiling,
    ``Tiling.RationalPolygonal.RationalPolygonalRegion.theorem_1_1,
    ``Tiling.RationalPolygonal.RationalPolygonalRegion.theorem_1_2,
    ``Tiling.RationalPolygonal.RationalPolygonalRegion.corollary_1_1,
    ``Tiling.RationalPolygonal.RationalPolygonalRegion.corollary_1_1_spec,
    ``TranslationalTilings.theorem_1_3_i,
    ``TranslationalTilings.theorem_1_3_ii,
    ``TranslationalTilings.theorem_1_4_uniform,
    ``TranslationalTilings.theorem_1_4_l1,
    ``TranslationalTilings.theorem_1_4,
    ``TranslationalTilings.theorem_1_5_l1,
    ``TranslationalTilings.theorem_1_5,
    ``TranslationalTilings.corollary_1_6,
    ``TranslationalTilings.lemma_2_1,
    ``TranslationalTilings.theorem_1_7,
    ``TranslationalTilings.lemma_3_1_i,
    ``TranslationalTilings.lemma_3_1_ii,
    ``TranslationalTilings.lemma_3_1_iii,
    ``TranslationalTilings.theorem_3_4,
    ``TranslationalTilings.corollary_3_5,
    ``TranslationalTilings.proposition_4_1_i,
    ``TranslationalTilings.proposition_4_1_ii,
    ``TranslationalTilings.proposition_4_1_iii,
    ``TranslationalTilings.lemma_4_2,
    ``TranslationalTilings.lemma_4_2_bigO,
    ``TranslationalTilings.lemma_4_3,
    ``TranslationalTilings.lemma_4_3_halfCircle,
    ``TranslationalTilings.proposition_4_4,
    ``TranslationalTilings.lemma_5_1,
    ``TranslationalTilings.corollary_5_3,
    ``TranslationalTilings.theorem_5_4,
    ``TranslationalTilings.theorem_5_4_exact,
    ``TranslationalTilings.theorem_5_4_structural,
    ``TranslationalTilings.theorem_6_2,
    ``TranslationalTilings.theorem_6_2_lattice_input,
    ``Tiling.RationalSlopes.minimal_flc_weaklyPeriodic,
    ``Tiling.RationalSlopes.flc_exists_periodic_replacement,
    ``Tiling.RationalSlopes.minimal_wholePlane_structure,
    ``Tiling.RationalSlopes.minimal_wholePlane_weaklyPeriodic,
    ``Tiling.RationalSlopes.exists_weaklyDoublyPeriodic_tiling]
  for name in targets do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "{name} depends on disallowed axiom {axiomName}"
  Lean.logInfo
    m!"Verified {targets.size} public theorems against the standard axiom allow-list."
