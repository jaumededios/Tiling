import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Index
import TranslationalTilings.Analysis.PolynomialRigidity
import TranslationalTilings.Structure.Grouped

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 4ad0ec2879696545635873cb4b6fab5ff9fe85bb902487927bd189221c4ac23a  blueprint/06-weak-periodicity.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/06-weak-periodicity.md:27; TranslationalTilings.canonicalDirection -/
namespace TranslationalTilings
def canonicalDirection (h : Plane) : Plane :=
  let v := primitivePart h
  if v 0 < 0 ∨ (v 0 = 0 ∧ v 1 < 0) then -v else v
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:31; TranslationalTilings.planeToPair -/
namespace TranslationalTilings
def planeToPair (h : Plane) : ℤ ×ₗ ℤ := (h 0, h 1)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:33; TranslationalTilings.pairToPlane -/
namespace TranslationalTilings
def pairToPlane (p : ℤ ×ₗ ℤ) : Plane := ![p.1, p.2]
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:35; TranslationalTilings.groupedDirectionPairs -/
namespace TranslationalTilings
def groupedDirectionPairs (F : Finset Plane) : Finset (ℤ ×ₗ ℤ) :=
  (F.erase 0).image fun f ↦ planeToPair (canonicalDirection f)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:38; TranslationalTilings.groupedDirectionCount -/
namespace TranslationalTilings
def groupedDirectionCount (F : Finset Plane) : ℕ :=
  (groupedDirectionPairs F).card
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:41; TranslationalTilings.groupedDirectionScale -/
namespace TranslationalTilings
def groupedDirectionScale (F : Finset Plane) (v : Plane) : ℕ :=
  ((F.erase 0).filter fun f ↦ canonicalDirection f = v).lcm vectorContent
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:44; TranslationalTilings.groupedTileDirections -/
namespace TranslationalTilings
def groupedTileDirections (F : Finset Plane) :
    Fin (groupedDirectionCount F) → Plane :=
  fun i ↦
    let v := pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl i)
    (groupedDirectionScale F v : ℤ) • v
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:58; TranslationalTilings.canonicalDirection_ne_zero -/
namespace TranslationalTilings
axiom canonicalDirection_ne_zero {h : Plane} (hh : h ≠ 0) :
  canonicalDirection h ≠ 0
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:61; TranslationalTilings.tile_integer_multiple_of_canonicalDirection -/
namespace TranslationalTilings
axiom tile_integer_multiple_of_canonicalDirection
    {h : Plane} (hh : h ≠ 0) :
  ∃ z : ℤ, z ≠ 0 ∧ h = z • canonicalDirection h
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:65; TranslationalTilings.canonicalDirection_eq_iff_commensurable -/
namespace TranslationalTilings
axiom canonicalDirection_eq_iff_commensurable
    {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) :
  canonicalDirection u = canonicalDirection v ↔ Commensurable u v
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:69; TranslationalTilings.groupedDirectionCount_pos -/
namespace TranslationalTilings
axiom groupedDirectionCount_pos
    {F : Finset Plane} (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  0 < groupedDirectionCount F
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:73; TranslationalTilings.groupedDirectionCount_le_erase -/
namespace TranslationalTilings
axiom groupedDirectionCount_le_erase (F : Finset Plane) :
  groupedDirectionCount F ≤ (F.erase 0).card
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:76; TranslationalTilings.groupedDirectionCount_le -/
namespace TranslationalTilings
axiom groupedDirectionCount_le
    {F : Finset Plane} (hzero : 0 ∈ F) :
  groupedDirectionCount F ≤ F.card - 1
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:80; TranslationalTilings.groupedDirectionCount_singleton_ne_zero -/
namespace TranslationalTilings
axiom groupedDirectionCount_singleton_ne_zero
    {f : Plane} (hf : f ≠ 0) :
  groupedDirectionCount {f} = 1
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:84; TranslationalTilings.groupedTileDirections_ne_zero -/
namespace TranslationalTilings
axiom groupedTileDirections_ne_zero
    {F : Finset Plane} (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  ∀ j, groupedTileDirections F j ≠ 0
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:88; TranslationalTilings.groupedTileDirections_pairwise -/
namespace TranslationalTilings
axiom groupedTileDirections_pairwise
    {F : Finset Plane} (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  PairwiseIncommensurable (groupedTileDirections F)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:92; TranslationalTilings.groupedTileDirections_from_tile -/
namespace TranslationalTilings
axiom groupedTileDirections_from_tile
    {F : Finset Plane} (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  ∀ j, ∃ f ∈ F, f ≠ 0 ∧ ∃ z : ℤ,
    groupedTileDirections F j = z • f
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:128; TranslationalTilings.directionAvoidanceLCM -/
namespace TranslationalTilings
def directionAvoidanceLCM {m : ℕ} (h : Fin m → Plane) : ℕ :=
  (Finset.univ : Finset (Fin m)).lcm fun j ↦
    Int.natAbs (wedge (avoidanceVector h) (h j))
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:132; TranslationalTilings.weakRigidityPeriod -/
namespace TranslationalTilings
def weakRigidityPeriod (directionCount : ℕ) : ℕ :=
  (Finset.range (directionCount + 1)).lcm universalRigidityPeriod
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:135; TranslationalTilings.weakPeriodVectorBound -/
namespace TranslationalTilings
def weakPeriodVectorBound (tileCard diameter : ℕ) : ℕ :=
  diameter ^ (tileCard - 1)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:138; TranslationalTilings.weakPeriodIndexConstant -/
namespace TranslationalTilings
def weakPeriodIndexConstant (tileCard : ℕ) : ℕ :=
  4 ^ (4 * tileCard) * (tileCard + 1) ^ (tileCard + 1)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:141; TranslationalTilings.weakPeriodIndexBound -/
namespace TranslationalTilings
def weakPeriodIndexBound (tileCard diameter : ℕ) : ℕ :=
  weakPeriodIndexConstant tileCard *
    max 1 (diameter ^ (2 * (tileCard - 1) ^ 2))
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:145; TranslationalTilings.weakPeriodMultiplierConstant -/
namespace TranslationalTilings
def weakPeriodMultiplierConstant (tileCard : ℕ) : ℕ :=
  weakRigidityPeriod tileCard *
    (tileCard + 1) ^ (2 * tileCard) * 4 ^ (2 * tileCard)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:149; TranslationalTilings.weakPeriodMultiplierBound -/
namespace TranslationalTilings
def weakPeriodMultiplierBound (tileCard diameter : ℕ) : ℕ :=
  weakPeriodMultiplierConstant tileCard *
    max 1 (diameter ^ (tileCard * (tileCard - 1)))
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:153; TranslationalTilings.weakPeriodIndexEuclideanConstant -/
namespace TranslationalTilings
noncomputable def weakPeriodIndexEuclideanConstant (tileCard : ℕ) : ℝ :=
  weakPeriodIndexConstant tileCard *
    Real.sqrt 2 ^ (2 * (tileCard - 1) ^ 2)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:157; TranslationalTilings.weakPeriodMultiplierEuclideanConstant -/
namespace TranslationalTilings
noncomputable def weakPeriodMultiplierEuclideanConstant
    (tileCard : ℕ) : ℝ :=
  weakPeriodMultiplierConstant tileCard *
    Real.sqrt 2 ^ (tileCard * (tileCard - 1))
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:162; TranslationalTilings.weakQ -/
namespace TranslationalTilings
def weakQ (F : Finset Plane) (ell : ℕ) : ℕ :=
  indicatorDilationModulus ell F.card
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:165; TranslationalTilings.weakN -/
namespace TranslationalTilings
def weakN {m : ℕ} (h : Fin m → Plane) : ℕ := pairWedgeLCM h
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:167; TranslationalTilings.weakAvoidance -/
namespace TranslationalTilings
def weakAvoidance {m : ℕ} (h : Fin m → Plane) : Plane := avoidanceVector h
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:169; TranslationalTilings.weakM -/
namespace TranslationalTilings
def weakM {m : ℕ} (h : Fin m → Plane) : ℕ := directionAvoidanceLCM h
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:171; TranslationalTilings.weakSliceVector -/
namespace TranslationalTilings
def weakSliceVector (F : Finset Plane) (ell : ℕ)
    {m : ℕ} (h : Fin m → Plane) : Plane :=
  ((weakQ F ell * weakN h : ℕ) : ℤ) • weakAvoidance h
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:175; TranslationalTilings.weakLattice -/
namespace TranslationalTilings
def weakLattice (F : Finset Plane) (ell : ℕ)
    {m : ℕ} (h : Fin m → Plane) (hm : 0 < m) : AddSubgroup Plane :=
  generatedPair (weakSliceVector F ell h)
    (((weakQ F ell * weakN h * weakM h : ℕ) : ℤ) • h ⟨0, hm⟩)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:180; TranslationalTilings.weakMultiplier -/
namespace TranslationalTilings
def weakMultiplier (F : Finset Plane) (ell : ℕ)
    {m : ℕ} (h : Fin m → Plane) : ℕ :=
  weakRigidityPeriod m * weakM h ^ 2 * weakN h *
    (weakQ F ell / ell)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:193; TranslationalTilings.directionAvoidanceLCM_pos -/
namespace TranslationalTilings
axiom directionAvoidanceLCM_pos
    {h : Fin m → Plane} (hne : ∀ j, h j ≠ 0) :
  0 < directionAvoidanceLCM h
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:197; TranslationalTilings.directionAvoidanceLCM_bound -/
namespace TranslationalTilings
axiom directionAvoidanceLCM_bound
    {h : Fin m → Plane} (hne : ∀ j, h j ≠ 0) :
  directionAvoidanceLCM h ≤
    (m + 1) ^ m * ∏ j, l1Norm (h j)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:202; TranslationalTilings.weakRigidityPeriod_pos -/
namespace TranslationalTilings
axiom weakRigidityPeriod_pos (directionCount : ℕ) :
  0 < weakRigidityPeriod directionCount
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:205; TranslationalTilings.universalRigidityPeriod_dvd_weak -/
namespace TranslationalTilings
axiom universalRigidityPeriod_dvd_weak
    {d directionCount : ℕ} (hd : d ≤ directionCount) :
  universalRigidityPeriod d ∣ weakRigidityPeriod directionCount
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:209; TranslationalTilings.weakRigidityPeriod_dvd_of_le -/
namespace TranslationalTilings
axiom weakRigidityPeriod_dvd_of_le
    {m c : ℕ} (hmc : m ≤ c) :
  weakRigidityPeriod m ∣ weakRigidityPeriod c
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:213; TranslationalTilings.weakQ_divisibility -/
namespace TranslationalTilings
axiom weakQ_divisibility {F : Finset Plane} {ell : ℕ} (hell : 0 < ell) :
  ell ∣ weakQ F ell
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:216; TranslationalTilings.weakQ_quotient_bound -/
namespace TranslationalTilings
axiom weakQ_quotient_bound
    {F : Finset Plane} {ell : ℕ} (hell : 0 < ell) :
  weakQ F ell / ell ≤ 4 ^ (2 * F.card)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:220; TranslationalTilings.weakN_bound -/
namespace TranslationalTilings
axiom weakN_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) :
  weakN D.direction ≤ l1Diameter F ^ ((F.card - 1) * (F.card - 2))
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:225; TranslationalTilings.weakM_bound -/
namespace TranslationalTilings
axiom weakM_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) :
  weakM D.direction ≤ (F.card + 1) ^ F.card *
    l1Diameter F ^ (F.card - 1)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:231; TranslationalTilings.weakLattice_le_scalar -/
namespace TranslationalTilings
axiom weakLattice_le_scalar
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
  weakLattice F ell D.direction D.number_pos ≤ scalarLattice ell
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:236; TranslationalTilings.weakLattice_relativeIndex_bound -/
namespace TranslationalTilings
axiom weakLattice_relativeIndex_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
  (weakLattice F ell D.direction D.number_pos).relIndex (scalarLattice ell) ≤
    weakPeriodIndexBound F.card (l1Diameter F)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:242; TranslationalTilings.weakMultiplier_pos -/
namespace TranslationalTilings
axiom weakMultiplier_pos
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
  0 < weakMultiplier F ell D.direction
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:247; TranslationalTilings.weakMultiplier_bound -/
namespace TranslationalTilings
axiom weakMultiplier_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
  weakMultiplier F ell D.direction ≤
    weakPeriodMultiplierBound F.card (l1Diameter F)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:253; TranslationalTilings.weak_period_mem_lattice -/
namespace TranslationalTilings
axiom weak_period_mem_lattice
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
  ∀ j, ((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) • D.direction j ∈
    weakLattice F ell D.direction D.number_pos
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:265; TranslationalTilings.WeakArithmeticData -/
namespace TranslationalTilings
structure WeakArithmeticData (F : Finset Plane) (ell : ℕ)
    {m : ℕ} (h : Fin m → Plane) (hm : 0 < m) where
  lattice : AddSubgroup Plane
  multiplier : ℕ
  lattice_eq : lattice = weakLattice F ell h hm
  multiplier_eq : multiplier = weakMultiplier F ell h
  q_pos : 0 < weakQ F ell
  pairLCM_pos : 0 < weakN h
  avoidanceLCM_pos : 0 < weakM h
  rigidityPeriod_pos : 0 < weakRigidityPeriod m
  multiplier_pos : 0 < multiplier
  exact_scalar_factor :
    ell * multiplier =
      weakRigidityPeriod m * weakM h ^ 2 * weakN h * weakQ F ell
  supremumOnePeriod_mem : ∀ j,
    ((weakM h ^ 2 * weakN h * weakQ F ell : ℕ) : ℤ) • h j ∈ lattice
  rigidityBranchPeriod_mem :
    ((weakRigidityPeriod m * weakM h * weakN h * weakQ F ell : ℕ) : ℤ) •
      h ⟨0, hm⟩ ∈ lattice
  advertisedPeriod_mem : ∀ j,
    ((weakRigidityPeriod m * weakM h ^ 2 * weakN h *
      weakQ F ell : ℕ) : ℤ) • h j ∈ lattice
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:288; TranslationalTilings.exists_weakArithmeticData -/
namespace TranslationalTilings
axiom exists_weakArithmeticData
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
  Nonempty (WeakArithmeticData F ell D.direction D.number_pos)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:319; TranslationalTilings.QuantitativeWeakPeriodData -/
namespace TranslationalTilings
structure QuantitativeWeakPeriodData
    (F : Finset Plane) (ell : ℕ) where
  numberOfDirections : ℕ
  number_pos : 0 < numberOfDirections
  number_le : numberOfDirections ≤ F.card - 1
  direction : Fin numberOfDirections → Plane
  direction_ne_zero : ∀ j, direction j ≠ 0
  pairwise_incommensurable : PairwiseIncommensurable direction
  direction_from_tile : ∀ j,
    ∃ f ∈ F, f ≠ 0 ∧ ∃ z : ℤ, direction j = z • f
  direction_l1_bound : ∀ j,
    l1Norm (direction j) ≤ weakPeriodVectorBound F.card (l1Diameter F)
  direction_euclidean_bound : ∀ j,
    euclideanNorm (direction j) ≤
      (euclideanDiameter F) ^ (F.card - 1)
  product_direction_l1_bound :
    ∏ j : Fin numberOfDirections, l1Norm (direction j) ≤
      l1Diameter F ^ (F.card - 1)
  product_direction_euclidean_bound :
    ∏ j : Fin numberOfDirections, euclideanNorm (direction j) ≤
      euclideanDiameter F ^ (F.card - 1)
  arithmetic : WeakArithmeticData F ell direction number_pos
  lattice_le : arithmetic.lattice ≤ scalarLattice ell
  relativeIndex_bound :
    arithmetic.lattice.relIndex (scalarLattice ell) ≤
      weakPeriodIndexBound F.card (l1Diameter F)
  multiplier_bound :
    arithmetic.multiplier ≤ weakPeriodMultiplierBound F.card (l1Diameter F)
  period_mem_lattice : ∀ j,
    ((ell * arithmetic.multiplier : ℕ) : ℤ) • direction j ∈
      arithmetic.lattice
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:351; TranslationalTilings.QuantitativeWeakPeriodData.lattice -/
namespace TranslationalTilings
abbrev QuantitativeWeakPeriodData.lattice
    {F : Finset Plane} {ell : ℕ}
    (D : QuantitativeWeakPeriodData F ell) : AddSubgroup Plane :=
  D.arithmetic.lattice
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:356; TranslationalTilings.QuantitativeWeakPeriodData.multiplier -/
namespace TranslationalTilings
abbrev QuantitativeWeakPeriodData.multiplier
    {F : Finset Plane} {ell : ℕ}
    (D : QuantitativeWeakPeriodData F ell) : ℕ :=
  D.arithmetic.multiplier
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:361; TranslationalTilings.QuantitativeWeakPeriodData.ValidFor -/
namespace TranslationalTilings
def QuantitativeWeakPeriodData.ValidFor
    {F : Finset Plane} {ell : ℕ}
    (D : QuantitativeWeakPeriodData F ell) (A : Set Plane) : Prop :=
  CosetwisePeriodic A D.lattice
    (fun j ↦ ((ell * D.multiplier : ℕ) : ℤ) • D.direction j)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:367; TranslationalTilings.linePhi -/
namespace TranslationalTilings
def linePhi {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (e x : Plane) (j : Fin D.numberOfDirections) (n : ℤ) : ℝ :=
  D.phi j (x + n • e)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:381; TranslationalTilings.linePhi_sum_mod_one -/
namespace TranslationalTilings
axiom linePhi_sum_mod_one
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (e x : Plane) (n : ℤ) :
  ∑ j, ((linePhi D e x j n : ℝ) : Torus) = 0
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:387; TranslationalTilings.linePhi_circlePolynomial -/
namespace TranslationalTilings
axiom linePhi_circlePolynomial
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) (j : Fin D.numberOfDirections) :
  ∃ P : CirclePolynomial (D.numberOfDirections - 2), ∀ n : ℤ,
    P n = (linePhi D (weakSliceVector F ell D.direction) x j n : Torus)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:394; TranslationalTilings.linePhi_pair_sup_le_one -/
namespace TranslationalTilings
axiom linePhi_pair_sup_le_one
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) {i j : Fin D.numberOfDirections} (hij : i ≠ j) :
  sSup (Set.range (linePhi D (weakSliceVector F ell D.direction) x i)) +
    sSup (Set.range (linePhi D (weakSliceVector F ell D.direction) x j)) ≤ 1
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:430; TranslationalTilings.coset_one_dimensional_periodicity -/
namespace TranslationalTilings
axiom coset_one_dimensional_periodicity
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E) :
  CosetwisePeriodic A (weakLattice F ell D.direction D.number_pos)
    (fun j ↦ ((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) •
      D.direction j)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:478; TranslationalTilings.exists_groupedStructureDecomposition_canonical -/
namespace TranslationalTilings
axiom exists_groupedStructureDecomposition_canonical
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic ell E) (htile : Tiles F A E) :
  ∃ D : GroupedStructureDecomposition F A E ell 1,
    ∃ hnum : D.numberOfDirections = groupedDirectionCount F,
      ∀ j : Fin (groupedDirectionCount F),
        D.direction (Fin.cast hnum.symm j) = groupedTileDirections F j
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:487; TranslationalTilings.exists_quantitativeWeakPeriodData -/
namespace TranslationalTilings
axiom exists_quantitativeWeakPeriodData
    {F : Finset Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  ∃ D : QuantitativeWeakPeriodData F ell,
    ∀ (E A : Set Plane), SetScalarPeriodic ell E → Tiles F A E →
      D.ValidFor A
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:495; TranslationalTilings.quantitative_weak_periodicity_l1 -/
namespace TranslationalTilings
axiom quantitative_weak_periodicity_l1
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic ell E) (htile : Tiles F A E) :
  ∃ D : QuantitativeWeakPeriodData F ell, D.ValidFor A
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:502; TranslationalTilings.quantitative_weak_periodicity_euclidean -/
namespace TranslationalTilings
axiom quantitative_weak_periodicity_euclidean
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic ell E) (htile : Tiles F A E) :
  ∃ (m : ℕ) (h : Fin m → Plane) (Λ : AddSubgroup Plane) (L : ℕ),
    0 < m ∧ m ≤ F.card - 1 ∧
    (∀ j, h j ≠ 0) ∧ PairwiseIncommensurable h ∧
    (∀ j, ∃ f ∈ F, f ≠ 0 ∧ ∃ z : ℤ, h j = z • f) ∧
    (∀ j, euclideanNorm (h j) ≤
      euclideanDiameter F ^ (F.card - 1)) ∧
    (∏ j : Fin m, euclideanNorm (h j)) ≤
      euclideanDiameter F ^ (F.card - 1) ∧
    Λ ≤ scalarLattice ell ∧
    (Λ.relIndex (scalarLattice ell) : ℝ) ≤
      weakPeriodIndexEuclideanConstant F.card *
        euclideanDiameter F ^ (2 * (F.card - 1) ^ 2) ∧
    0 < L ∧ (L : ℝ) ≤ weakPeriodMultiplierEuclideanConstant F.card *
      euclideanDiameter F ^ (F.card * (F.card - 1)) ∧
    CosetwisePeriodic A Λ
      (fun j ↦ ((ell * L : ℕ) : ℤ) • h j)
end TranslationalTilings

/- blueprint/06-weak-periodicity.md:524; TranslationalTilings.level_one_plane_weaklyPeriodic -/
namespace TranslationalTilings
axiom level_one_plane_weaklyPeriodic
    {F : Finset Plane} {A E : Set Plane}
    (hF : F.Nonempty) (hperiodicE : IsPeriodic E)
    (htile : Tiles F A E) : WeaklyPeriodic A
end TranslationalTilings
