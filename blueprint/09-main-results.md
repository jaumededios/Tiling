# Paper-facing API and theorem numbering

Target module:

```lean
import TranslationalTilings.Counterexample
import TranslationalTilings.Algorithms
```

This umbrella module contains no new mathematical argument.  It gives stable
paper-numbered names to the fully quantified lower-level declarations.  Exact
closed bounds remain visible; the file does not replace them by existential
`O`-constants.

```lean
namespace TranslationalTilings
```

## Main results from the introduction

The source uses “tile” in its standard nonempty sense.  The formal statement
records this explicitly: without it, `F=∅, E=∅` would make every set `A` a
vacuous tiling and Theorem 1.3(i) would be false.

```lean
/-- Paper Theorem 1.3(i): level-one plane tilings are weakly periodic. -/
theorem theorem_1_3_i
    {F : Finset Plane} {A E : Set Plane}
    (hF : F.Nonempty) (hperiodicE : IsPeriodic E)
    (htile : Tiles F A E) : WeaklyPeriodic A :=
  level_one_plane_weaklyPeriodic hF hperiodicE htile

/-- Paper Theorem 1.3(ii): an eight-element level-four counterexample. -/
theorem theorem_1_3_ii :
    ∃ (F : Finset Plane) (A : Set Plane),
      F.card = 8 ∧ TilesAtLevel F A Set.univ 4 ∧ ¬ WeaklyPeriodic A :=
  Counterexample.exists_eight_element_level_four_not_weaklyPeriodic
```

Theorem 1.4 is exported in three forms.  The first makes uniformity in the
tiling set syntactic by choosing the data before `E,A`; the next two are the
closed `l1` and paper-facing Euclidean forms.

```lean
/-- Paper Theorem 1.4, uniform-data form. -/
theorem theorem_1_4_uniform
    {F : Finset Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  ∃ D : QuantitativeWeakPeriodData F ell,
    ∀ (E A : Set Plane), SetScalarPeriodic ell E → Tiles F A E →
      D.ValidFor A :=
  exists_quantitativeWeakPeriodData hell hzero hcard

/-- Paper Theorem 1.4, exact natural-valued `l1` form. -/
theorem theorem_1_4_l1
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic ell E) (htile : Tiles F A E) :
  ∃ D : QuantitativeWeakPeriodData F ell, D.ValidFor A :=
  quantitative_weak_periodicity_l1 hell hzero hcard hE htile

/-- Paper Theorem 1.4, Euclidean-norm statement. -/
theorem theorem_1_4
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
      (fun j ↦ ((ell * L : ℕ) : ℤ) • h j) :=
  quantitative_weak_periodicity_euclidean hell hzero hcard hE htile
```

For Theorem 1.5 the exact certificate exposes the tiling set and scalar
multiplier.  Its proof first converts Theorem 1.4's cosetwise certificate into
a disjoint `DirectionalTilingDecomposition`, uses the dedicated one-part or
structural multi-part completion theorem, and rebases the resulting certificate
from `ell*L₀` to `ell`.  The Euclidean result is the paper-facing alias.

```lean
/-- Paper Theorem 1.5, exact `l1` certificate. -/
theorem theorem_1_5_l1
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (hexists : ∃ A, Tiles F A E) :
  ∃ C : PeriodicTilingCertificate F E ell,
    C.scalarMultiplier ≤ periodicTilingPeriodBound F.card (l1Diameter F) :=
  quantitative_periodic_tiling_l1 hell hE hexists

/-- Paper Theorem 1.5, Euclidean-diameter form. -/
theorem theorem_1_5
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (hexists : ∃ A, Tiles F A E) :
  ∃ (A' : Set Plane) (M : ℕ),
    0 < M ∧ Tiles F A' E ∧ SetScalarPeriodic (ell * M) A' ∧
    (M : ℝ) ≤ periodicTilingEuclideanConstant F.card *
      max 1 (euclideanDiameter F ^ periodicTilingExponent F.card) :=
  quantitative_periodic_tiling_euclidean hell hE hexists
```

The computational corollary packages correctness, the trace bound, and the
closed exponential estimate.  `planarTileSearchExponent` is itself bounded by
a tile-cardinality constant times a diameter power whose exponent is at most
`12*(|F|+1)^4`.

```lean
/-- Paper Corollary 1.6. -/
theorem corollary_1_6 (F : Finset Plane) :
    (planarTileDecision F = true ↔ ∃ A : Set Plane, TilesUniverse F A) ∧
    (planarTileDecisionCounted F).2 ≤ planarTileSearchCost F ∧
    planarTileSearchCost F ≤ 2 ^ planarTileSearchExponent F ∧
    planarTileSearchExponent F ≤ planarTileSearchConstant F.card *
      max 1 (l1Diameter F ^ planarTileDiameterExponent F.card) ∧
    planarTileDiameterExponent F.card ≤ 12 * (F.card + 1) ^ 4 :=
  ⟨planarTileDecision_eq_true_iff F,
    planarTileDecisionCounted_cost F,
    planarTileSearchCost_closed_bound F,
    planarTileSearchExponent_diameter_bound F,
    planarTileDiameterExponent_le_quartic F.card⟩
```

## Numbered results from Sections 2--6

Aliases below deliberately preserve the complete lower-module types; the
comparator prints those expanded types next to the source statement.

```lean
/-- Paper Lemma 2.1. -/
theorem lemma_2_1 :
    ScalarPeriodic 4 Counterexample.chi ∧
      (∀ x, Counterexample.chi x = -1 ∨ Counterexample.chi x = 1) ∧
      tileConv {0, Counterexample.v₁} Counterexample.chi = 0 ∧
      tileConv {0, Counterexample.v₂} Counterexample.chi = 0 :=
  Counterexample.chi_lemma

/-- Paper Theorem 1.7. -/
theorem theorem_1_7 {d ell : ℕ}
    {F : Finset (Lattice d)} {A : Set (Lattice d)}
    (hd : 0 < d) (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : ScalarPeriodic ell (tileConv F (setIndicator A))) :
    Nonempty (StructureDecomposition F A ell) :=
  exists_structureDecomposition hd hell hzero hperiod

/-- Paper Lemma 3.1(i). -/
theorem lemma_3_1_i {d p : ℕ} {F : Finset (Lattice d)}
    {g : Lattice d → ℤ} {lo hi k : ℤ}
    (hbound : BoundedBetween lo hi g)
    (hconv : tileConv F g = fun _ ↦ k) (hp : p.Prime)
    (hlarge : oscillationBound lo hi * F.card < p) :
    tileConv (dilate p F) g = fun _ ↦ k :=
  dilation_prime hbound hconv hp hlarge

/-- Paper Lemma 3.1(ii). -/
theorem lemma_3_1_ii {d r : ℕ} {F : Finset (Lattice d)}
    {g : Lattice d → ℤ} {lo hi k : ℤ}
    (hbound : BoundedBetween lo hi g)
    (hconv : tileConv F g = fun _ ↦ k) (hr : 0 < r)
    (hcop : Nat.Coprime r
      (primorial (oscillationBound lo hi * F.card))) :
    tileConv (dilate r F) g = fun _ ↦ k :=
  dilation_coprime hbound hconv hr hcop

/-- Paper Lemma 3.1(iii). -/
theorem lemma_3_1_iii {d ell r : ℕ}
    {F : Finset (Lattice d)} {g : Lattice d → ℤ} {lo hi : ℤ}
    (hbound : BoundedBetween lo hi g) (hell : 0 < ell)
    (hperiod : ScalarPeriodic ell (tileConv F g)) (hr : 0 < r)
    (hmod : Nat.ModEq
      (dilationModulus ell (oscillationBound lo hi) F.card) r 1) :
    tileConv (dilate r F) g = tileConv F g :=
  dilation_periodic hbound hell hperiod hr hmod

/-- Paper Theorem 3.4. -/
theorem theorem_3_4 {d ell k : ℕ}
    {F : Finset (Lattice d)} {A E : Set (Lattice d)}
    (hd : 0 < d) (hell : 0 < ell) (hk : 0 < k)
    (hcard : 1 < F.card) (hzero : 0 ∈ F)
    (hE : SetScalarPeriodic ell E) (htile : TilesAtLevel F A E k) :
    Nonempty (GroupedStructureDecomposition F A E ell k) :=
  exists_groupedStructureDecomposition hd hell hk hcard hzero hE htile

/-- Paper Corollary 3.5. -/
theorem corollary_3_5
    {F : Finset ℤ} {A : Set ℤ} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : Function.Periodic
      (tileConv F (setIndicator A)) (ell : ℤ)) :
    Function.Periodic (setIndicator A) (universalPeriod1D ell F : ℤ) :=
  universal_period_one_dimensional hell hzero hperiod

/-- Paper Proposition 4.1(i). -/
theorem proposition_4_1_i
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (e x : Plane) (n : ℤ) :
    ∑ j, ((linePhi D e x j n : ℝ) : Torus) = 0 :=
  linePhi_sum_mod_one D e x n

/-- Paper Proposition 4.1(ii). -/
theorem proposition_4_1_ii
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) (j : Fin D.numberOfDirections) :
  ∃ P : CirclePolynomial (D.numberOfDirections - 2), ∀ n : ℤ,
    P n = (linePhi D (weakSliceVector F ell D.direction) x j n : Torus) :=
  linePhi_circlePolynomial D x j

/-- Paper Proposition 4.1(iii). -/
theorem proposition_4_1_iii
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) {i j : Fin D.numberOfDirections} (hij : i ≠ j) :
  sSup (Set.range (linePhi D (weakSliceVector F ell D.direction) x i)) +
    sSup (Set.range (linePhi D (weakSliceVector F ell D.direction) x j)) ≤ 1 :=
  linePhi_pair_sup_le_one D x hij

/-- Paper Lemma 4.2, with the exact exponent `1-1/d`. -/
theorem lemma_4_2
    (d : ℕ) (hd : 0 < d) (P : CirclePolynomial d)
    (hrat : P.HasTorsionNonconstantCoeffs)
    (hnonconstant : ¬ P.FunctionConstant) :
  ‖completeSum P P.commonDenominator‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ)) :=
  complete_exponential_sum_paper_functionNonconstant d hd P hrat hnonconstant

/-- Paper Lemma 4.2 in literal uniform-constant form. -/
theorem lemma_4_2_bigO (d : ℕ) (hd : 0 < d) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ P : CirclePolynomial d,
    P.HasTorsionNonconstantCoeffs → ¬ P.FunctionConstant →
    ‖completeSum P P.commonDenominator‖ ≤
      C * Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ)) :=
  complete_exponential_sum_paper_bigO d hd

/-- Paper Lemma 4.3, with a positive-radius metric interval in `R/Z`. -/
theorem lemma_4_3
    (P : CirclePolynomial d) (c : Torus) (eps : ℚ)
    (heps : 0 < eps) (hsmall : eps < 1 / 2)
    (havoid : P.AvoidsBall c eps) :
  ∃ Q, 0 < Q ∧ Q ≤ rigidityPeriodBound d eps ∧ P.PeriodicWith Q :=
  periodic_of_avoidsBall P c eps heps hsmall havoid

/-- The half-circle specialization used in Proposition 4.4. -/
theorem lemma_4_3_halfCircle
    (P : CirclePolynomial d) (hhalf : P.HasHalfCircleLifts) :
  ∃ Q, 0 < Q ∧ Q ≤ halfCirclePeriodBound d ∧ P.PeriodicWith Q :=
  periodic_of_halfCircle P hhalf

/-- Paper Proposition 4.4. -/
theorem proposition_4_4
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E) :
  CosetwisePeriodic A (weakLattice F ell D.direction D.number_pos)
    (fun j ↦ ((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) •
      D.direction j) :=
  coset_one_dimensional_periodicity D hell hE

/-- Paper Lemma 5.1. -/
theorem lemma_5_1
    {F : Finset Plane} {A : Set Plane} {ell k : ℕ} {h x : Plane}
    (hell : 0 < ell) (hk : 0 < k) (hh : IsPrimitive h)
    (hAperiod : Function.Periodic (setIndicator A)
      (((ell * k : ℕ) : ℤ) • h))
    (hconvperiod : ScalarPeriodic ell (tileConv F (setIndicator A))) :
  ScalarPeriodic
    (indicatorDilationModulus ell F.card * k * slicingLCM F h)
    (tileConv (tileSlice F h x) (setIndicator A)) :=
  slicing_lemma hell hk hh hAperiod hconvperiod

/-- Paper Corollary 5.3. -/
theorem corollary_5_3
    {F : Finset Plane} {A : Set Plane} {ell k : ℕ} {h : Plane}
    (hell : 0 < ell) (hk : 0 < k) (hh : IsPrimitive h)
    (hAperiod : Function.Periodic (setIndicator A)
      (((ell * k : ℕ) : ℤ) • h))
    (hconvperiod : ScalarPeriodic ell (tileConv F (setIndicator A))) :
  ∃ A' : Set Plane,
    SetScalarPeriodic
      (indicatorDilationModulus ell F.card * k * slicingLCM F h) A' ∧
    convolutionEquivalent F A A' ∧
    ∀ line : Plane ⧸ directionSubgroup h,
      convolutionEquivalent F (slicePattern h line A)
        (slicePattern h line A') :=
  improve_onePeriodic hell hk hh hAperiod hconvperiod

/-- Paper Theorem 5.4 on its full nonempty-tile domain.  The result contains
the final periodic tiling and the separate component-convolution clause. -/
theorem theorem_5_4
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts) :
    Nonempty (PaperCompletionResult D) :=
  improve_weaklyPeriodic hF D hell hm

/-- Strong exact-construction form of Theorem 5.4.  The `1<F.card` hypothesis
is necessary for the `r>0` estimate in the `N * product L_j` certificate. -/
theorem theorem_5_4_exact
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (hcard : 1 < F.card)
    (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts) :
    Nonempty (CompletionCertificate D) :=
  improve_weaklyPeriodic_exact hF hcard D hell hm

/-- Exact-construction Theorem 5.4 in the structural regime `m≤|F|-1` used
by the main theorems, with the hidden constant depending only on `|F|`. -/
theorem theorem_5_4_structural
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts)
    (hmcard : D.numberOfParts ≤ F.card - 1) :
  ∃ C : CompletionCertificate D,
    C.completed.scalarMultiplier ≤
      structuralCompletionPeriodBound F.card (l1Diameter F)
        D.numberOfParts
        (∏ i : Fin D.numberOfParts, l1Norm (D.direction i)) :=
  improve_weaklyPeriodic_structural hF D hell hm hmcard

/-- Paper Theorem 6.2. -/
theorem theorem_6_2
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hexists : ∃ A, Tiles F A E.toSet) :
  nonOnePeriodicTilingDecision F E = true ↔
    ∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A :=
  nonOnePeriodicTilingDecision_eq_true_iff hF hexists

/-- Paper Theorem 6.2 for the canonical finite-index HNF period-lattice input
format. -/
theorem theorem_6_2_lattice_input
    {F : Finset Plane} {E : LatticePeriodicSetCode}
    (hF : F.Nonempty) (hexists : ∃ A, Tiles F A E.toSet) :
  nonOnePeriodicTilingDecisionLatticeInput F E = true ↔
    ∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A :=
  nonOnePeriodicTilingDecisionLatticeInput_eq_true_iff hF hexists

end TranslationalTilings
```

## Faithfulness ledger

- `theorem_1_3_i` adds only the paper's implicit meaning of “tile”:
  `F.Nonempty`.  Empty targets remain supported; for nonempty `F`, their only
  level-one tiling set is empty.
- `theorem_1_4_uniform` is slightly stronger in quantifier order than required:
  its data are independent of `E` as well as `A`.  The proof construction in
  Sections 3--4 has this uniformity.
- The vectors in the quantitative certificate are actual integer multiples of
  nonzero tile vectors, not merely commensurable with them.  Both individual
  and product Euclidean bounds have coefficient one as printed.
- `theorem_1_5_l1` uses the closed exponent
  `(c-1)*(c^2+c-1)`; `periodicTilingExponent_le_quartic` proves the paper's
  coarser `O(c^4)` form.
- Lemma 4.2 retains the printed exponent `1-1/d` and a constant chosen before
  the polynomial.  Lemma 4.3 represents a positive-length interval by a
  positive-radius metric ball in `AddCircle 1`.
- Canonical `theorem_5_4` is singleton-safe and returns
  `PaperCompletionResult`, which contains both the periodic completion with
  the honest explicit `m`-dependent bound and the paper's separate
  component-convolution clause.  `theorem_5_4_exact` exposes the full
  `N,N_j,C_j,s_j,L_j,M` arithmetic through `CompletionCertificate` under the
  necessary `1<F.card` hypothesis.  `theorem_5_4_structural` derives this
  hypothesis from `2≤m≤F.card-1` and exports the cardinality-only constant
  used in Theorems 1.4--1.5.  The `k=4096` regression explains why the exact
  certificate cannot be promised for singleton tiles.
- `FiniteDifference.lean` is the unique owner of `backwardDiff` and
  `backwardDiffIter`; all polynomial and structure results share that API.
- `theorem_6_2_lattice_input` starts from the checked triangular/HNF wire
  format of Chapter 8.  The proof-side HNF coverage theorem shows that every
  finite-index planar periodic target admits such a code.  The formal API does
  not claim a raw-generator conversion routine or charge a conversion cost.
- Corollary 1.6 and Theorem 6.2 refer to actual Boolean programs over finite
  payloads.  The cost theorem is explicitly a unit-cost arithmetic trace, not
  a bit-complexity assertion.
