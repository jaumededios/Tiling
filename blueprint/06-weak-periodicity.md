# Quantitative weak periodicity in the plane

Paper coverage: Proposition 4.1, Proposition 4.4, Theorem 1.4, and Theorem
1.3(i).  Target modules:

```lean
import TranslationalTilings.Analysis.PolynomialRigidity
import TranslationalTilings.Structure.Grouped
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Index
```

All constants below are closed expressions.  There is no cardinality-indexed
`O` object in the Lean API.

## 1. Canonical direction data

The grouped directions can be chosen canonically from the tile, hence before
the tiling set `A` is quantified.  First replace a nonzero vector by its
primitive part and orient it so that its first nonzero coordinate is positive.
Represent the result as an ordered pair so Mathlib's lexicographic product
order can enumerate the finite set.

```lean
namespace TranslationalTilings

def canonicalDirection (h : Plane) : Plane :=
  let v := primitivePart h
  if v 0 < 0 ∨ (v 0 = 0 ∧ v 1 < 0) then -v else v

def planeToPair (h : Plane) : ℤ ×ₗ ℤ := (h 0, h 1)

def pairToPlane (p : ℤ ×ₗ ℤ) : Plane := ![p.1, p.2]

def groupedDirectionPairs (F : Finset Plane) : Finset (ℤ ×ₗ ℤ) :=
  (F.erase 0).image fun f ↦ planeToPair (canonicalDirection f)

def groupedDirectionCount (F : Finset Plane) : ℕ :=
  (groupedDirectionPairs F).card

def groupedDirectionScale (F : Finset Plane) (v : Plane) : ℕ :=
  ((F.erase 0).filter fun f ↦ canonicalDirection f = v).lcm vectorContent

def groupedTileDirections (F : Finset Plane) :
    Fin (groupedDirectionCount F) → Plane :=
  fun i ↦
    let v := pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl i)
    (groupedDirectionScale F v : ℤ) • v
```

This is executable: `Finset.orderEmbOfFin` sorts the finite set.  It does not
choose a representative from an abstract quotient.  Within a class, the lcm
of the tile-vector contents turns the oriented primitive key into a common
integer multiple of every tile vector in that class; this is the actual
period direction stored in `groupedTileDirections`.

```lean
theorem canonicalDirection_ne_zero {h : Plane} (hh : h ≠ 0) :
  canonicalDirection h ≠ 0

theorem tile_integer_multiple_of_canonicalDirection
    {h : Plane} (hh : h ≠ 0) :
  ∃ z : ℤ, z ≠ 0 ∧ h = z • canonicalDirection h

theorem canonicalDirection_eq_iff_commensurable
    {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) :
  canonicalDirection u = canonicalDirection v ↔ Commensurable u v

theorem groupedDirectionCount_pos
    {F : Finset Plane} (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  0 < groupedDirectionCount F

theorem groupedDirectionCount_le_erase (F : Finset Plane) :
  groupedDirectionCount F ≤ (F.erase 0).card

theorem groupedDirectionCount_le
    {F : Finset Plane} (hzero : 0 ∈ F) :
  groupedDirectionCount F ≤ F.card - 1

theorem groupedDirectionCount_singleton_ne_zero
    {f : Plane} (hf : f ≠ 0) :
  groupedDirectionCount {f} = 1

theorem groupedTileDirections_ne_zero
    {F : Finset Plane} (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  ∀ j, groupedTileDirections F j ≠ 0

theorem groupedTileDirections_pairwise
    {F : Finset Plane} (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  PairwiseIncommensurable (groupedTileDirections F)

theorem groupedTileDirections_from_tile
    {F : Finset Plane} (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  ∀ j, ∃ f ∈ F, f ≠ 0 ∧ ∃ z : ℤ,
    groupedTileDirections F j = z • f
```

The integer-multiple clause is oriented exactly as in Theorem 1.4.  Equality
of canonical directions is the equivalence relation used when the ungrouped
functions from Chapter 3 are summed into grouped functions.
The singleton regression is deliberately unconditional apart from `f≠0`:
for `F={![1,0]}` it gives direction count one, while `F.card-1=0`.  This
exhibits why the sharper cardinality subtraction theorem must assume the
standing normalization `0∈F`; only the erase-cardinality bound is unconditional.

## 2. Closed quantitative constants

Let `c=|F|` and `D=l1Diameter F`.  The paper's data are

- `q = indicatorDilationModulus ell c`;
- `h` the canonical directions and `m` their number;
- `eTilde = avoidanceVector h`;
- `N = pairWedgeLCM h`;
- `e = q*N*eTilde`;
- `M = lcm_j |eTilde wedge h_j|`;
- `Lambda = <e,q*N*M*h_0>`;
- `Q_m = weakRigidityPeriod m`, a common multiple of all rigidity periods of
  degrees at most the actual direction count `m`;
- `L = Q*M^2*N*(q/ell)`.

The quotient is exact because `ell | q`.
The exact proposition uses `Q_m`.  The cardinality-only advertised constant
uses the cap `Q_c`; under the standing normalization `0∈F`,
`groupedDirectionCount_le hzero` gives `m≤c-1≤c`, and
`weakRigidityPeriod_dvd_of_le` transports every exact period into that cap.

```lean
def directionAvoidanceLCM {m : ℕ} (h : Fin m → Plane) : ℕ :=
  (Finset.univ : Finset (Fin m)).lcm fun j ↦
    Int.natAbs (wedge (avoidanceVector h) (h j))

def weakRigidityPeriod (directionCount : ℕ) : ℕ :=
  (Finset.range (directionCount + 1)).lcm universalRigidityPeriod

def weakPeriodVectorBound (tileCard diameter : ℕ) : ℕ :=
  diameter ^ (tileCard - 1)

def weakPeriodIndexConstant (tileCard : ℕ) : ℕ :=
  4 ^ (4 * tileCard) * (tileCard + 1) ^ (tileCard + 1)

def weakPeriodIndexBound (tileCard diameter : ℕ) : ℕ :=
  weakPeriodIndexConstant tileCard *
    max 1 (diameter ^ (2 * (tileCard - 1) ^ 2))

def weakPeriodMultiplierConstant (tileCard : ℕ) : ℕ :=
  weakRigidityPeriod tileCard *
    (tileCard + 1) ^ (2 * tileCard) * 4 ^ (2 * tileCard)

def weakPeriodMultiplierBound (tileCard diameter : ℕ) : ℕ :=
  weakPeriodMultiplierConstant tileCard *
    max 1 (diameter ^ (tileCard * (tileCard - 1)))

noncomputable def weakPeriodIndexEuclideanConstant (tileCard : ℕ) : ℝ :=
  weakPeriodIndexConstant tileCard *
    Real.sqrt 2 ^ (2 * (tileCard - 1) ^ 2)

noncomputable def weakPeriodMultiplierEuclideanConstant
    (tileCard : ℕ) : ℝ :=
  weakPeriodMultiplierConstant tileCard *
    Real.sqrt 2 ^ (tileCard * (tileCard - 1))

def weakQ (F : Finset Plane) (ell : ℕ) : ℕ :=
  indicatorDilationModulus ell F.card

def weakN {m : ℕ} (h : Fin m → Plane) : ℕ := pairWedgeLCM h

def weakAvoidance {m : ℕ} (h : Fin m → Plane) : Plane := avoidanceVector h

def weakM {m : ℕ} (h : Fin m → Plane) : ℕ := directionAvoidanceLCM h

def weakSliceVector (F : Finset Plane) (ell : ℕ)
    {m : ℕ} (h : Fin m → Plane) : Plane :=
  ((weakQ F ell * weakN h : ℕ) : ℤ) • weakAvoidance h

def weakLattice (F : Finset Plane) (ell : ℕ)
    {m : ℕ} (h : Fin m → Plane) (hm : 0 < m) : AddSubgroup Plane :=
  generatedPair (weakSliceVector F ell h)
    (((weakQ F ell * weakN h * weakM h : ℕ) : ℤ) • h ⟨0, hm⟩)

def weakMultiplier (F : Finset Plane) (ell : ℕ)
    {m : ℕ} (h : Fin m → Plane) : ℕ :=
  weakRigidityPeriod m * weakM h ^ 2 * weakN h *
    (weakQ F ell / ell)
```

No diagonal wedge enters either lcm.  `pairWedgeLCM` uses unordered distinct
pairs; `directionAvoidanceLCM` uses the avoidance vector, whose wedge with
every direction is nonzero.

The quantitative arithmetic API is:

```lean
theorem directionAvoidanceLCM_pos
    {h : Fin m → Plane} (hne : ∀ j, h j ≠ 0) :
  0 < directionAvoidanceLCM h

theorem directionAvoidanceLCM_bound
    {h : Fin m → Plane} (hne : ∀ j, h j ≠ 0) :
  directionAvoidanceLCM h ≤
    (m + 1) ^ m * ∏ j, l1Norm (h j)

theorem weakRigidityPeriod_pos (directionCount : ℕ) :
  0 < weakRigidityPeriod directionCount

theorem universalRigidityPeriod_dvd_weak
    {d directionCount : ℕ} (hd : d ≤ directionCount) :
  universalRigidityPeriod d ∣ weakRigidityPeriod directionCount

theorem weakRigidityPeriod_dvd_of_le
    {m c : ℕ} (hmc : m ≤ c) :
  weakRigidityPeriod m ∣ weakRigidityPeriod c

theorem weakQ_divisibility {F : Finset Plane} {ell : ℕ} (hell : 0 < ell) :
  ell ∣ weakQ F ell

theorem weakQ_quotient_bound
    {F : Finset Plane} {ell : ℕ} (hell : 0 < ell) :
  weakQ F ell / ell ≤ 4 ^ (2 * F.card)

theorem weakN_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) :
  weakN D.direction ≤ l1Diameter F ^ ((F.card - 1) * (F.card - 2))

theorem weakM_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) :
  weakM D.direction ≤ (F.card + 1) ^ F.card *
    l1Diameter F ^ (F.card - 1)

theorem weakLattice_le_scalar
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
  weakLattice F ell D.direction D.number_pos ≤ scalarLattice ell

theorem weakLattice_relativeIndex_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
  (weakLattice F ell D.direction D.number_pos).relIndex (scalarLattice ell) ≤
    weakPeriodIndexBound F.card (l1Diameter F)

theorem weakMultiplier_pos
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
  0 < weakMultiplier F ell D.direction

theorem weakMultiplier_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
  weakMultiplier F ell D.direction ≤
    weakPeriodMultiplierBound F.card (l1Diameter F)

theorem weak_period_mem_lattice
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
  ∀ j, ((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) • D.direction j ∈
    weakLattice F ell D.direction D.number_pos
```

The branch-specific divisibility facts are bundled before the simplified
quantitative certificate.  Thus the exact `q,N,M,Q,Lambda,L` data cannot drift
away from the bounds used by Sections 5--6.

```lean
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

theorem exists_weakArithmeticData
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
  Nonempty (WeakArithmeticData F ell D.direction D.number_pos)
```

The exponent computations are retained, rather than hidden in automation:

```text
N <= D^((c-1)(c-2))
M <= (c+1)^c D^(c-1)
|eTilde wedge h_0| <= (c+1) D^(c-1)
[ell Z^2 : Lambda]
  <= 4^(4c) (c+1)^(c+1) D^(2(c-1)^2)
L <= Q_c (c+1)^(2c) 4^(2c) D^(c(c-1)).
```

For the index, expand the determinant of the two lattice generators and
divide by `ell^2`.  Substitute `q/ell≤4^(2c)`, the displayed bounds on `N`
and `M`, and
`2(c-1)(c-2)+2(c-1)=2(c-1)^2`.  For `L`, use
`weakRigidityPeriod m ∣ weakRigidityPeriod c` together with positivity, then
substitute the bounds on `M`, `N`, and `q/ell`, using
`2(c-1)+(c-1)(c-2)=c(c-1)`.  Thus the exact identity uses `Q_m`, while only
the final cardinality-only inequality enlarges it to `Q_c`.  The `max 1`
terms make the functions total;
under `0∈F` and `1<F.card`, the diameter is positive and they simplify away.

## 3. Public result data

```lean
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

abbrev QuantitativeWeakPeriodData.lattice
    {F : Finset Plane} {ell : ℕ}
    (D : QuantitativeWeakPeriodData F ell) : AddSubgroup Plane :=
  D.arithmetic.lattice

abbrev QuantitativeWeakPeriodData.multiplier
    {F : Finset Plane} {ell : ℕ}
    (D : QuantitativeWeakPeriodData F ell) : ℕ :=
  D.arithmetic.multiplier

def QuantitativeWeakPeriodData.ValidFor
    {F : Finset Plane} {ell : ℕ}
    (D : QuantitativeWeakPeriodData F ell) (A : Set Plane) : Prop :=
  CosetwisePeriodic A D.lattice
    (fun j ↦ ((ell * D.multiplier : ℕ) : ℤ) • D.direction j)

def linePhi {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (e x : Plane) (j : Fin D.numberOfDirections) (n : ℤ) : ℝ :=
  D.phi j (x + n • e)
```

The Euclidean product field is not derived by inserting a generic
`sqrt 2` norm-equivalence factor.  It is copied from the coefficient-one
determinant/product estimate in `GroupedStructureDecomposition`, so the
paper's Euclidean statement is preserved exactly.

## 4. Proposition 4.1: line polynomials

```lean
theorem linePhi_sum_mod_one
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (e x : Plane) (n : ℤ) :
  ∑ j, ((linePhi D e x j n : ℝ) : Torus) = 0

theorem linePhi_circlePolynomial
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) (j : Fin D.numberOfDirections) :
  ∃ P : CirclePolynomial (D.numberOfDirections - 2), ∀ n : ℤ,
    P n = (linePhi D (weakSliceVector F ell D.direction) x j n : Torus)

theorem linePhi_pair_sup_le_one
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) {i j : Fin D.numberOfDirections} (hij : i ≠ j) :
  sSup (Set.range (linePhi D (weakSliceVector F ell D.direction) x i)) +
    sSup (Set.range (linePhi D (weakSliceVector F ell D.direction) x j)) ≤ 1
```

The first statement is `structure_decomposition_mod_one` evaluated on the
line.  For the polynomial statement, fix `j`.  For every `i≠j`, Cramer and
the definition of `N` express the slice vector as an integer combination of
`q*h_i` and `q*h_j`.  Apply the backward differences
`Delta_(e-b_ij*q*h_j)` for all `i≠j` to the mod-one sum.  Each kills `phi_i`,
acts as `Delta_e` on `phi_j`, and commutes with the remaining differences.
For at least two directions this gives
`Delta_e^(m-1) phi_j=0`, hence the line has `(m-1)`st difference zero and
`exists_circlePolynomial_of_difference` gives degree at most `m-2`.  If
`m=1`, the original mod-one sum already says the only line function is zero
modulo one, represented by the zero degree-zero polynomial.  Thus natural
subtraction causes no omitted edge case.

For the supremum inequality, Cramer gives integers `a_ij,b_ij` with
`e=a_ij*q*h_i+b_ij*q*h_j`.  Evaluate `D.sum_phi_le` at

`x+n1*e+a_ij*(n2-n1)*q*h_i = x+n2*e-b_ij*(n2-n1)*q*h_j`.

Periodicity identifies the two selected terms with `P_i(n1)` and `P_j(n2)`;
all other terms are nonnegative.  Each range is nonempty and bounded in
`[0,1]`, so two applications of `csSup_le` give the result.

## 5. Proposition 4.4: rigidity on every lattice coset

The exact paper typo is corrected here: the line argument in the sum is
`s+b_j*t`, with the index varying with the summand.

```lean
theorem coset_one_dimensional_periodicity
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E) :
  CosetwisePeriodic A (weakLattice F ell D.direction D.number_pos)
    (fun j ↦ ((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) •
      D.direction j)
```

Write a coset point as `x+s*e+t*q*N*M*h_0`.  Cramer gives, for each `j`,

`q*N*M*h_0 = a_j*q*h_j+b_j*e`,

and therefore

`1_A = 1_E(x)-sum_j P_j(s+b_j*t)`.

The explicit hypothesis `hE` is essential: it transports the target indicator
across the weak lattice, which lies inside `scalarLattice ell`.  The grouped
decomposition does not retain this target-periodicity certificate as a field.

There are two exhaustive branches.

1. If `sSup(range P_j)=1`, Proposition 4.1(iii) makes every other supremum
   zero, and nonnegativity makes those other functions identically zero.
   The mod-one sum says `P_j` is integer-valued; its `[0,1]` bounds make it
   `{0,1}`-valued.  The formula is invariant under the vector
   `M^2*N*q*h_j`, and hence under its positive multiple using
   `weakRigidityPeriod m`.
2. Otherwise every supremum is strictly below one.  Proposition 4.1(iii)
   implies that all but at most one line polynomial have real lifts in
   `[0,1/2]`.  `periodic_of_halfCircle` gives each of those a bounded positive
   period.  Their degree is at most `m-2≤F.card`; therefore their universal
   periods divide `weakRigidityPeriod m`.  The mod-one sum supplies the
   same period for the possible exception.  Since every real value lies in
   `[0,1)`, equality modulo one lifts to equality in `ℝ`.  The displayed
   indicator formula is then invariant under `Q*M*N*q*h_0`, and multiplying
   by `M` puts it in the advertised list `Q*M^2*N*q*h_j`.

The source phrase is thus recorded correctly: a line polynomial whose real
range is contained in one half of the circle avoids a ball in the other half.

## 6. The quantitative and qualitative theorems

The uniform constructor quantifies the data before `E` and `A`.  This makes
the paper's “does not otherwise depend on `A`” clause machine-checkable.

```lean
theorem exists_groupedStructureDecomposition_canonical
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic ell E) (htile : Tiles F A E) :
  ∃ D : GroupedStructureDecomposition F A E ell 1,
    ∃ hnum : D.numberOfDirections = groupedDirectionCount F,
      ∀ j : Fin (groupedDirectionCount F),
        D.direction (Fin.cast hnum.symm j) = groupedTileDirections F j

theorem exists_quantitativeWeakPeriodData
    {F : Finset Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  ∃ D : QuantitativeWeakPeriodData F ell,
    ∀ (E A : Set Plane), SetScalarPeriodic ell E → Tiles F A E →
      D.ValidFor A

/-- Greenfeld--Tao, Theorem 1.4, l1 form with closed constants. -/
theorem quantitative_weak_periodicity_l1
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic ell E) (htile : Tiles F A E) :
  ∃ D : QuantitativeWeakPeriodData F ell, D.ValidFor A

/-- Greenfeld--Tao, Theorem 1.4, paper-facing Euclidean form. -/
theorem quantitative_weak_periodicity_euclidean
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

/-- Greenfeld--Tao, Theorem 1.3(i). -/
theorem level_one_plane_weaklyPeriodic
    {F : Finset Plane} {A E : Set Plane}
    (hF : F.Nonempty) (hperiodicE : IsPeriodic E)
    (htile : Tiles F A E) : WeaklyPeriodic A

end TranslationalTilings
```

For Theorem 1.4, group the Chapter 3 decomposition by the canonical direction
function, use the direct l1 and Euclidean product bounds already stored there,
then take `weakLattice` and `weakMultiplier`.  Proposition 4.4 supplies
`ValidFor`; the arithmetic theorems supply every quantitative field.

For Theorem 1.3(i), choose a positive scalar period from the finite-index
period lattice of `E`.  Translate a point of the nonempty tile to zero using
`tiles_translate_tile`.  If the translated tile is a singleton, its tiling set
is a translate of `E` and is periodic.  Otherwise apply Theorem 1.4.
`weaklyPeriodic_of_cosetwise` turns the finite quotient by `Λ` into a disjoint
weak-periodic decomposition.  Translating the decomposition back preserves
all nonzero periods.  Empty tiles are excluded explicitly by `hF`; no
disjointness or cancellation step silently assumes nonemptiness.
