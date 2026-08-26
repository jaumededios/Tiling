# Dilation lemma and structural decompositions

Target modules are `TranslationalTilings.Dilation.Periodic` and
`TranslationalTilings.Structure.Grouped`.  This chapter participates in the strict
dependency-ordered check at `blueprint/validation/BlueprintIntegrated.lean`.
`tmp/BlueprintDilation.lean` is retained only as a local diagnostic and is not
an acceptance validator.

```lean
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.FiniteDifference
import TranslationalTilings.LatticeGeometry
```

This chapter covers all three parts of Lemma 3.1, Theorem 1.7, Theorem 3.4,
and Corollary 3.5.

## Dilation definitions

```lean
namespace TranslationalTilings

def dilate {d : ℕ} (r : ℕ)
    (F : Finset (Lattice d)) : Finset (Lattice d) :=
  F.image fun f ↦ (r : ℤ) • f

def BoundedBetween {α : Type*} (lo hi : ℤ) (g : α → ℤ) : Prop :=
  ∀ x, lo ≤ g x ∧ g x ≤ hi

def IntegerBounded {α : Type*} (g : α → ℤ) : Prop :=
  ∃ lo hi : ℤ, BoundedBetween lo hi g

def oscillationBound (lo hi : ℤ) : ℕ := Int.natAbs (hi - lo)

noncomputable def centeredMultipleInterval (ell R : ℕ) : Finset ℤ :=
  (Finset.Icc (-(R : ℤ)) R).image fun z ↦ (ell : ℤ) * z

noncomputable def folnerBox {d : ℕ}
    (ell R : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset fun _ : Fin d ↦ centeredMultipleInterval ell R

noncomputable def rayAverage {d : ℕ} (q N : ℕ) (f : Lattice d)
    (A : Set (Lattice d)) : Lattice d → ℚ :=
  fun x ↦ (N : ℚ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
    (setIndicator A (x - ((1 + n * q : ℕ) : ℤ) • f) : ℚ)

end TranslationalTilings
```

The Følner objects and ray averages are noncomputable proof constructions;
they never enter the executable decision procedures.  The noncomputability of
the centered integer interval comes from Mathlib's conditionally complete
order instance, not from an unstated choice.

## Public dilation theorems

```lean
theorem dilate_zero {d : ℕ} {F : Finset (Lattice d)}
    (hF : F.Nonempty) : dilate 0 F = {0}

theorem dilate_zero_eq_empty_iff {d : ℕ} (F : Finset (Lattice d)) :
    dilate 0 F = ∅ ↔ F = ∅

theorem dilate_one {d : ℕ} (F : Finset (Lattice d)) : dilate 1 F = F

theorem dilate_mul {d r s : ℕ} (F : Finset (Lattice d)) :
    dilate r (dilate s F) = dilate (r * s) F

theorem card_dilate {d r : ℕ} {F : Finset (Lattice d)} (hr : 0 < r) :
    (dilate r F).card = F.card

theorem tileMonoidAlgebra_frobenius_mod_prime
    {d p : ℕ} (F : Finset (Lattice d)) (hp : p.Prime) :
    tileMonoidAlgebra (ZMod p) (Lattice d) F ^ p =
      tileMonoidAlgebra (ZMod p) (Lattice d) (dilate p F)

theorem dilation_prime {d p : ℕ} {F : Finset (Lattice d)}
    {g : Lattice d → ℤ} {lo hi k : ℤ}
    (hbound : BoundedBetween lo hi g)
    (hconv : tileConv F g = fun _ ↦ k) (hp : p.Prime)
    (hlarge : oscillationBound lo hi * F.card < p) :
    tileConv (dilate p F) g = fun _ ↦ k

theorem dilation_coprime {d r : ℕ} {F : Finset (Lattice d)}
    {g : Lattice d → ℤ} {lo hi k : ℤ}
    (hbound : BoundedBetween lo hi g)
    (hconv : tileConv F g = fun _ ↦ k) (hr : 0 < r)
    (hcop : Nat.Coprime r
      (primorial (oscillationBound lo hi * F.card))) :
    tileConv (dilate r F) g = fun _ ↦ k

theorem folnerBox_card {d ell R : ℕ} (hell : 0 < ell) :
    (folnerBox (d := d) ell R).card = (2 * R + 1) ^ d

theorem folnerBox_translate_symmDiff_ratio_bound
    {d ell : ℕ} {v : Lattice d} (hv : v ∈ scalarLattice ell) :
    ∃ C : ℕ, ∀ R,
      (folnerBox (d := d) ell R ∆
        (folnerBox (d := d) ell R).image (fun x ↦ x + v)).card *
          (2 * R + 1) ≤ C * (folnerBox (d := d) ell R).card

theorem dilation_periodic {d ell r : ℕ}
    {F : Finset (Lattice d)} {g : Lattice d → ℤ} {lo hi : ℤ}
    (hbound : BoundedBetween lo hi g) (hell : 0 < ell)
    (hperiod : ScalarPeriodic ell (tileConv F g)) (hr : 0 < r)
    (hmod : Nat.ModEq
      (dilationModulus ell (oscillationBound lo hi) F.card) r 1) :
    tileConv (dilate r F) g = tileConv F g

theorem dilation_indicator_periodic {d ell r : ℕ}
    {F : Finset (Lattice d)} {A : Set (Lattice d)}
    (hell : 0 < ell)
    (hperiod : ScalarPeriodic ell (tileConv F (setIndicator A)))
    (hr : 0 < r)
    (hmod : Nat.ModEq (indicatorDilationModulus ell F.card) r 1) :
    tileConv (dilate r F) (setIndicator A) =
      tileConv F (setIndicator A)
```

`Nat.ModEq` is required.  Remainder equality would make congruence modulo one
impossible, while every integer is congruent to one modulo one.  Positivity of
`r` is also explicit: at modulus one, allowing `r=0` would make the constant
function case of part (iii) false for a multi-element tile.

## Proof of Lemma 3.1

For part (i), first split the zero-oscillation case.  Then multiplication by
the prime is injective on the lattice and preserves `F.card`.  In the additive
group algebra over `ZMod p`, Frobenius sends the tile sum to the sum supported
on `pF`.  Convolving the original constant equation with another `p-1` tile
factors and applying Fermat shows that the original and dilated convolutions
are congruent modulo `p`.  Subtract the lower bound from `g`; the integer
difference has magnitude at most
`oscillationBound lo hi * F.card < p`, so divisibility by `p` forces zero.

For part (ii), every prime divisor of `r` is larger than the cutoff by
`Nat.Prime.dvd_primorial_iff` and coprimality.  Strong induction on `r`, using
a prime factor and `dilate_mul`, iterates part (i).  This corrects the source
proof's typographical phrase “`r=1 mod q`”: the theorem and the factorization
require only that `r` be coprime to the small-prime product.

For part (iii), every lattice-period difference `backwardDiff lambda g` has
oscillation at most twice that of `g`.  Part (ii) makes the dilated convolution
periodic on `ell Z^d`.  Hence the difference between the dilated and original
convolutions is itself scalar-periodic.  Average it over the explicit box

`ell * {n : Z | -R <= n and n <= R}^d`.

Associativity moves the average next to the finite tile difference.  Because
`r` is congruent to one modulo `ell`, the two translates associated to each
tile point differ only on a box boundary.  The displayed symmetric-difference
bound makes its normalized size tend to zero.  Choose a finite `R` for which
the absolute value is below one.  The convolution difference is integer-valued,
so it is zero.  This is a finitary extraction from the paper's Følner-limit
argument.

## Structure definitions

```lean
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

def universalPeriod1D (ell : ℕ) (F : Finset ℤ) : ℕ :=
  indicatorDilationModulus ell F.card *
    (F.erase 0).lcm Int.natAbs

end TranslationalTilings
```

The public structures contain only data and laws used downstream.  The
ultrafilter witnessing their construction is proof-irrelevant and private.
The direction certificate records the paper's oriented claim—each direction
is an integer multiple of a nonzero tile vector—not merely commensurability.
Both norm bounds are stored because the Euclidean coefficient-one statement
cannot be recovered from generic norm equivalence.

## Public structure theorems

```lean
/-- Paper Theorem 1.7. -/
theorem exists_structureDecomposition {d ell : ℕ}
    {F : Finset (Lattice d)} {A : Set (Lattice d)}
    (hd : 0 < d) (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : ScalarPeriodic ell (tileConv F (setIndicator A))) :
    Nonempty (StructureDecomposition F A ell)

/-- Paper Theorem 3.4. -/
theorem exists_groupedStructureDecomposition {d ell k : ℕ}
    {F : Finset (Lattice d)} {A E : Set (Lattice d)}
    (hd : 0 < d) (hell : 0 < ell) (hk : 0 < k)
    (hcard : 1 < F.card) (hzero : 0 ∈ F)
    (hE : SetScalarPeriodic ell E) (htile : TilesAtLevel F A E k) :
    Nonempty (GroupedStructureDecomposition F A E ell k)

theorem grouped_q_bound {ell : ℕ} {F : Finset (Lattice d)} :
    indicatorDilationModulus ell F.card ≤ ell * 4 ^ (2 * F.card)

theorem structure_decomposition_mod_one
    {F : Finset (Lattice d)} {A E : Set (Lattice d)} {ell k : ℕ}
    (D : GroupedStructureDecomposition F A E ell k) (x : Lattice d) :
    (∑ j, ((D.phi j x) : AddCircle (1 : ℝ))) = 0

/-- Paper Corollary 3.5. -/
theorem universal_period_one_dimensional
    {F : Finset ℤ} {A : Set ℤ} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : Function.Periodic
      (tileConv F (setIndicator A)) (ell : ℤ)) :
    Function.Periodic (setIndicator A) (universalPeriod1D ell F : ℤ)
```

## Structure proof content

For each positive `N`, Lemma 3.1(iii) rewrites the indicator of `A` as the
periodic convolution minus the average of translates in each nonzero tile
direction.  All averages lie in `[0,1]`.  Regard their simultaneous values as
a point of the compact product

`product over (f in F erase 0, x in Z^d) of [0,1]`.

Extend `atTop` to an ultrafilter, map it into this compact product, and take
`Ultrafilter.lim`.  Coordinate projections tend to the corresponding limit.
All identities use finite sums, so coordinatewise convergence passes through
them.  The telescoping difference between ray averages at `x+qf` and `x` is at
most `2/N`; its limit is zero, proving the advertised period.  This uses
Mathlib's compact product and ultrafilter limit API, not Arzelà--Ascoli.

For Theorem 3.4, partition `F erase 0` into commensurability classes.  Apply
`exists_commonMultiple_of_pairwise_commensurable` from Chapter 2 to each
nonempty class.  Concretely, choose `f₀` in the class and let
`v=primitivePart f₀`.  The dimension-generic Bezout lemma behind
`integer_multiple_of_primitive_of_commensurable` writes every class member as
`z_f•v`, with `z_f≠0`.  Let `L` be the lcm of the positive contents
`|z_f|` and take `h_j=L•v`.  The sign of `z_f` is retained when writing
`h_j=(L/z_f)•f`; no orientation assumption on the class is needed.  Thus
`h_j` is a common integer multiple and the sum over the class has period
`q*h_j`.  Since a nonzero primitive integer vector has both l1 and Euclidean
norm at least one, `lcm≤product` gives directly

`euclideanNorm h_j <= product over f in class of euclideanNorm f`.

The coefficient-one l1 inequality is parallel.  Multiplying the per-class
inequalities is legitimate because the classes form a genuine finite
partition, and proves both product fields of `GroupedStructureDecomposition`.
Different classes give pairwise incommensurable directions.
Nonnegativity and

`indicator A = k * indicator E - sum phi_j`

give `sum phi_j <= k` and hence each `phi_j <= k`.

For Corollary 3.5, every nonzero one-dimensional tile vector divides
`n=(F.erase 0).lcm Int.natAbs`; consequently every structural term is periodic
with period `q*n`.  The convolution term is also `q*n`-periodic because
`ell` divides `q`.  Their linear combination is the indicator of `A`.
The rejected formula `lcm q n` is not used.  A regression test fixes
`F={0,2}` and the residues `{0,1}` modulo four: the convolution is constant,
period six fails for `A`, and the formal period `q*n=12` succeeds.
