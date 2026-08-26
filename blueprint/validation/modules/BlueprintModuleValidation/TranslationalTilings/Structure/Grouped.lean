import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.Dilation.Periodic
import TranslationalTilings.LatticeGeometry

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 92c0160157ec728377e183ab0532869fce5ecf4553e103ac64917236f1ec6b68  blueprint/03-dilation-structure.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

open scoped symmDiff

/- blueprint/03-dilation-structure.md:167; TranslationalTilings.StructureDecomposition -/
namespace TranslationalTilings
structure StructureDecomposition {d : ℕ}
    (F : Finset (Lattice d)) (A : Set (Lattice d)) (ell : ℕ) where
  phi : ↥(F.erase 0) → Lattice d → ℝ
  phi_nonneg : ∀ f x, 0 ≤ phi f x
  phi_le_one : ∀ f x, phi f x ≤ 1
  phi_periodic : ∀ f, Function.Periodic (phi f)
    ((indicatorDilationModulus ell F.card : ℤ) • (f.1 : Lattice d))
  decomposition : ∀ x, ((setIndicator A x : ℤ) : ℝ) =
    ((tileConv F (setIndicator A) x : ℤ) : ℝ) - ∑ f, phi f x
end TranslationalTilings

/- blueprint/03-dilation-structure.md:177; TranslationalTilings.GroupedStructureDecomposition -/
namespace TranslationalTilings
structure GroupedStructureDecomposition {d : ℕ}
    (F : Finset (Lattice d)) (A E : Set (Lattice d))
    (ell k : ℕ) where
  numberOfDirections : ℕ
  number_pos : 0 < numberOfDirections
  number_le : numberOfDirections ≤ F.card - 1
  direction : Fin numberOfDirections → Lattice d
  direction_ne_zero : ∀ j, direction j ≠ 0
  pairwise_incommensurable : PairwiseIncommensurable direction
  phi : Fin numberOfDirections → Lattice d → ℝ
  phi_nonneg : ∀ j x, 0 ≤ phi j x
  phi_le_level : ∀ j x, phi j x ≤ k
  phi_periodic : ∀ j, Function.Periodic (phi j)
    ((indicatorDilationModulus ell F.card : ℤ) • direction j)
  decomposition : ∀ x, ((setIndicator A x : ℤ) : ℝ) =
    (k : ℝ) * ((setIndicator E x : ℤ) : ℝ) - ∑ j, phi j x
  sum_phi_le : ∀ x, ∑ j, phi j x ≤ k
  direction_from_tile : ∀ j, ∃ f ∈ F, f ≠ 0 ∧
    ∃ z : ℤ, direction j = z • f
  product_direction_l1_bound :
    ∏ j, l1Norm (direction j) ≤ l1Diameter F ^ (F.card - 1)
  product_direction_euclidean_bound :
    ∏ j, euclideanNorm (direction j) ≤
      euclideanDiameter F ^ (F.card - 1)
end TranslationalTilings

/- blueprint/03-dilation-structure.md:202; TranslationalTilings.universalPeriod1D -/
namespace TranslationalTilings
def universalPeriod1D (ell : ℕ) (F : Finset ℤ) : ℕ :=
  indicatorDilationModulus ell F.card *
    (F.erase 0).lcm Int.natAbs
end TranslationalTilings

/- blueprint/03-dilation-structure.md:220; TranslationalTilings.exists_structureDecomposition -/
namespace TranslationalTilings
axiom exists_structureDecomposition {d ell : ℕ}
    {F : Finset (Lattice d)} {A : Set (Lattice d)}
    (hd : 0 < d) (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : ScalarPeriodic ell (tileConv F (setIndicator A))) :
    Nonempty (StructureDecomposition F A ell)
end TranslationalTilings

/- blueprint/03-dilation-structure.md:227; TranslationalTilings.exists_groupedStructureDecomposition -/
namespace TranslationalTilings
axiom exists_groupedStructureDecomposition {d ell k : ℕ}
    {F : Finset (Lattice d)} {A E : Set (Lattice d)}
    (hd : 0 < d) (hell : 0 < ell) (hk : 0 < k)
    (hcard : 1 < F.card) (hzero : 0 ∈ F)
    (hE : SetScalarPeriodic ell E) (htile : TilesAtLevel F A E k) :
    Nonempty (GroupedStructureDecomposition F A E ell k)
end TranslationalTilings

/- blueprint/03-dilation-structure.md:234; TranslationalTilings.grouped_q_bound -/
namespace TranslationalTilings
axiom grouped_q_bound {ell : ℕ} {F : Finset (Lattice d)} :
    indicatorDilationModulus ell F.card ≤ ell * 4 ^ (2 * F.card)
end TranslationalTilings

/- blueprint/03-dilation-structure.md:237; TranslationalTilings.structure_decomposition_mod_one -/
namespace TranslationalTilings
axiom structure_decomposition_mod_one
    {F : Finset (Lattice d)} {A E : Set (Lattice d)} {ell k : ℕ}
    (D : GroupedStructureDecomposition F A E ell k) (x : Lattice d) :
    (∑ j, ((D.phi j x) : AddCircle (1 : ℝ))) = 0
end TranslationalTilings

/- blueprint/03-dilation-structure.md:243; TranslationalTilings.universal_period_one_dimensional -/
namespace TranslationalTilings
axiom universal_period_one_dimensional
    {F : Finset ℤ} {A : Set ℤ} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : Function.Periodic
      (tileConv F (setIndicator A)) (ell : ℤ)) :
    Function.Periodic (setIndicator A) (universalPeriod1D ell F : ℤ)
end TranslationalTilings
