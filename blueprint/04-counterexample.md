# The explicit higher-level counterexample

Target module: `TranslationalTilings.Counterexample`.  This is Section 2,
Lemma 2.1, and Theorem 1.3(ii).  It is independent of the positive structure
theory.  Acceptance uses the strict integrated artifact
`blueprint/validation/BlueprintIntegrated.lean` and its declaration-coverage
ledger.  `tmp/BlueprintCounterexample.lean` is a diagnostic aid only.

```lean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.NumberTheory.Real.Irrational
import TranslationalTilings.Basic
import TranslationalTilings.FiniteDifference
import TranslationalTilings.LatticeGeometry
```

## Construction and definitions

For `alpha=sqrt 2`, let

`chi(m1,m2)=(-1)^(natAbs(floor(m2/2)+m1))`.

It is sign-valued and four-scalar-periodic.  Translation by `(0,2)`, `(1,0)`,
or `(2,-2)` reverses its sign, so convolution by each corresponding two-point
tile vanishes.

The carry is

`floor(alpha*(m1+m2))-floor(alpha*m1)-floor(alpha*m2)`.

The fractional-part addition formula makes it zero or one.  On a positive
sign take the carry; on a negative sign take its complement.

```lean
namespace TranslationalTilings.Counterexample

noncomputable def alpha : ℝ := Real.sqrt 2

def chi (x : Plane) : ℤ :=
  (-1) ^ Int.natAbs (x 1 / 2 + x 0)

noncomputable def carry (x : Plane) : ℤ :=
  Int.floor (alpha * ((x 0 + x 1 : ℤ) : ℝ)) -
    Int.floor (alpha * (x 0 : ℝ)) -
    Int.floor (alpha * (x 1 : ℝ))

noncomputable def counterexampleSet : Set Plane :=
  {x | if chi x = 1 then carry x = 1 else carry x = 0}

def v₁ : Plane := ![0, 2]
def v₂ : Plane := ![1, 0]
def v₃ : Plane := ![2, -2]

def counterexampleTile : Finset Plane :=
  (Finset.univ : Finset (Fin 3 → Bool)).image fun t ↦
    (if t 0 then v₁ else 0) +
    (if t 1 then v₂ else 0) +
    (if t 2 then v₃ else 0)

end TranslationalTilings.Counterexample
```

All objects involving `sqrt 2`, real floors, or arbitrary set membership are
explicitly noncomputable.  The finite tile and sign function remain
executable.

## Public theorems

```lean
namespace TranslationalTilings.Counterexample

theorem irrational_alpha : Irrational alpha

theorem chi_eq_formula (m₁ m₂ : ℤ) :
    chi ![m₁, m₂] = (-1) ^ Int.natAbs (m₂ / 2 + m₁)

theorem chi_mem (x : Plane) : chi x = -1 ∨ chi x = 1

theorem chi_scalarPeriodic_four : ScalarPeriodic 4 chi

theorem chi_cancel_vertical : tileConv {0, v₁} chi = 0

theorem chi_cancel_horizontal : tileConv {0, v₂} chi = 0

theorem chi_cancel_diagonal : tileConv {0, v₃} chi = 0

/-- Paper Lemma 2.1, using the concrete witness `chi`. -/
theorem chi_lemma :
    ScalarPeriodic 4 chi ∧
      (∀ x, chi x = -1 ∨ chi x = 1) ∧
      tileConv {0, v₁} chi = 0 ∧ tileConv {0, v₂} chi = 0

theorem carry_zero_or_one (x : Plane) : carry x = 0 ∨ carry x = 1

theorem carry_eq_fract (x : Plane) :
    (carry x : ℝ) =
      Int.fract (alpha * (x 0 : ℝ)) +
      Int.fract (alpha * (x 1 : ℝ)) -
      Int.fract (alpha * ((x 0 + x 1 : ℤ) : ℝ))

theorem indicator_counterexampleSet (x : Plane) :
    ((setIndicator counterexampleSet x : ℤ) : ℝ) =
      (chi x : ℝ) *
        (Int.fract (alpha * (x 0 : ℝ)) +
          Int.fract (alpha * (x 1 : ℝ)) -
          Int.fract (alpha * ((x 0 + x 1 : ℤ) : ℝ)) -
          (1 / 2 : ℝ)) + (1 / 2 : ℝ)

theorem counterexampleTile_card : counterexampleTile.card = 8

theorem counterexampleTile_indicator_factorization :
    tileMonoidAlgebra ℤ Plane counterexampleTile =
      tileMonoidAlgebra ℤ Plane {0, v₁} *
        tileMonoidAlgebra ℤ Plane {0, v₂} *
        tileMonoidAlgebra ℤ Plane {0, v₃}

theorem counterexample_tiles_level_four :
    TilesAtLevel counterexampleTile counterexampleSet Set.univ 4

theorem irrational_fract_range_infinite {β : ℝ} (hβ : Irrational β) :
    Set.Infinite (Set.range fun n : ℤ ↦ Int.fract (β * n))

theorem counterexample_not_weaklyPeriodic :
    ¬ WeaklyPeriodic counterexampleSet

/-- Paper Theorem 1.3(ii). -/
theorem exists_eight_element_level_four_not_weaklyPeriodic :
    ∃ (F : Finset Plane) (A : Set Plane),
      F.card = 8 ∧ TilesAtLevel F A Set.univ 4 ∧ ¬ WeaklyPeriodic A

end TranslationalTilings.Counterexample
```

The indicator identity is an equality in `R`; every integer-to-real cast is
visible.  The rejected rational/real mixed equality is gone.

## Tiling calculation

The Boolean-cube map defining the tile is injective.  If two triples have the
same sum, the first coordinate modulo two recovers the second bit `t₁`.
Half of the second coordinate is `t₀-t₂∈{-1,0,1}`.  The values `-1` and
`1` recover `t₀,t₂` immediately.  In the remaining case `t₀=t₂`,
subtract the already known `t₁` from the first coordinate; the result is
`2*t₂`, distinguishing `t₀=t₂=0` from `t₀=t₂=1`.  Thus all three
bits are recovered, the image has eight elements, and the additive
group-algebra indicator factors into the three two-point indicators.

The vertical factor annihilates `chi` and `chi*fract(alpha*m1)`, because the
fractional term is unchanged by a vertical translation.  The horizontal
factor annihilates `chi*fract(alpha*m2)`.  The diagonal factor annihilates
`chi*fract(alpha*(m1+m2))`.  Associativity and the factorization therefore
kill every nonconstant term of `indicator_counterexampleSet`; the constant
one-half term contributes `8/2=4`.

## Non-weak-periodicity proof

Assume a finite disjoint periodic decomposition of `counterexampleSet`.
Merge commensurable period directions, replacing each finite class by a
nonzero common multiple.  The resulting periods are pairwise
incommensurable.  At most one is horizontal; relabel it first, inserting an
empty horizontal part when necessary.

Rearrange the indicator formula exactly as in the paper:

`chi(m)*fract(alpha*m2)-indicator(A1)(m)`

equals the sum of the remaining part indicators, the two other signed
fractional terms, the signed one-half term, and the constant negative
one-half term.  The left side has the nonzero horizontal period `4*h1`.
Every right-side term has a period incommensurable with it.

Choose a vector incommensurable with this finite family and multiply it by the
LCM of the nonzero wedge magnitudes.  Cramer's identity places the multiple in
the subgroup generated by `4*h1` and each right-side period.  The exact
`eliminate_periodic_summands` theorem from Chapter 01 applies: a finite
iteration of the same backward difference kills the right side and vanishes
on the left.

On every line in that difference direction, the left side is bounded and has
a positive-order vanishing finite difference, so it is constant.  It is now
periodic in two incommensurable directions.  Cramer's inclusion gives a
finite-index scalar period lattice, hence the function has finite range.
The sign and the first part indicator also have finite range, so the formula
forces `fract(alpha*n)` to have finite range.  Equal fractional parts at two
different integers would put a nonzero integer multiple of `alpha` in the
integers, contradicting `irrational_alpha`.

The helpers for merging one assumed decomposition, constructing its common
difference vector, and proving finite range from a scalar period lattice stay
private to this module.  They are proof propositions and have no downstream
consumer; the reusable Cramer and finite-difference results remain public in
the lower modules.
