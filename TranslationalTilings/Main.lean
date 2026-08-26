/-
Copyright (c) 2026 TranslationalTilings contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TranslationalTilings contributors
-/
import TranslationalTilings.Algorithms
import TranslationalTilings.Counterexample

/-!
# Main results for translational tilings

This module exports the paper-facing API.  The bodies are intentionally thin:
the mathematical work is owned by the preceding production modules, while this
file records the exact correspondence with the numbered results in arXiv v3.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- Paper Theorem 1.3(i): every level-one planar tiling of a periodic target is weakly periodic. -/
theorem theorem_1_3_i
    {F : Finset Plane} {A E : Set Plane}
    (hF : F.Nonempty) (hperiodicE : IsPeriodic E)
    (htile : Tiles F A E) : WeaklyPeriodic A :=
  level_one_plane_weaklyPeriodic hF hperiodicE htile

/-- Paper Theorem 1.3(ii): an eight-element tile admits a level-four tiling
that is not weakly periodic. -/
theorem theorem_1_3_ii :
    ∃ (F : Finset Plane) (A : Set Plane),
      F.card = 8 ∧ TilesAtLevel F A Set.univ 4 ∧ ¬ WeaklyPeriodic A :=
  Counterexample.exists_eight_element_level_four_not_weaklyPeriodic

/-- Uniform quantitative data for Paper Theorem 1.4, chosen independently of
the target and tiling. -/
theorem theorem_1_4_uniform
    {F : Finset Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  ∃ D : QuantitativeWeakPeriodData F ell,
    ∀ (E A : Set Plane), SetScalarPeriodic ell E → Tiles F A E →
      D.ValidFor A :=
  exists_quantitativeWeakPeriodData hell hzero hcard

/-- The `ℓ¹`-quantitative form of Paper Theorem 1.4. -/
theorem theorem_1_4_l1
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic ell E) (htile : Tiles F A E) :
  ∃ D : QuantitativeWeakPeriodData F ell, D.ValidFor A :=
  quantitative_weak_periodicity_l1 hell hzero hcard hE htile

/-- Paper Theorem 1.4 with Euclidean diameter bounds. -/
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

/-- The `ℓ¹`-quantitative periodic-completion form of Paper Theorem 1.5. -/
theorem theorem_1_5_l1
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (hexists : ∃ A, Tiles F A E) :
  ∃ C : PeriodicTilingCertificate F E ell,
    C.scalarMultiplier ≤ periodicTilingPeriodBound F.card (l1Diameter F) :=
  quantitative_periodic_tiling_l1 hell hE hexists

/-- Paper Theorem 1.5 with the advertised Euclidean period bound. -/
theorem theorem_1_5
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (hexists : ∃ A, Tiles F A E) :
  ∃ (A' : Set Plane) (M : ℕ),
    0 < M ∧ Tiles F A' E ∧ SetScalarPeriodic (ell * M) A' ∧
    (M : ℝ) ≤ periodicTilingEuclideanConstant F.card *
      max 1 (euclideanDiameter F ^ periodicTilingExponent F.card) :=
  quantitative_periodic_tiling_euclidean hell hE hexists

/-- Paper Corollary 1.6: a correct counted decision procedure with explicit elementary bounds. -/
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

/-- Paper Lemma 2.1, collecting the parity function's exact cancellation laws. -/
theorem lemma_2_1 :
    ScalarPeriodic 4 Counterexample.chi ∧
      (∀ x, Counterexample.chi x = -1 ∨ Counterexample.chi x = 1) ∧
      tileConv {0, Counterexample.v₁} Counterexample.chi = 0 ∧
      tileConv {0, Counterexample.v₂} Counterexample.chi = 0 :=
  Counterexample.chi_lemma

/-- Paper Theorem 1.7: the qualitative structure decomposition in every positive dimension. -/
theorem theorem_1_7 {d ell : ℕ}
    {F : Finset (Lattice d)} {A : Set (Lattice d)}
    (hd : 0 < d) (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : ScalarPeriodic ell (tileConv F (setIndicator A))) :
    Nonempty (StructureDecomposition F A ell) :=
  exists_structureDecomposition hd hell hzero hperiod

/-- Paper Lemma 3.1(i): large-prime dilation preserves a bounded convolution identity. -/
theorem lemma_3_1_i {d p : ℕ} {F : Finset (Lattice d)}
    {g : Lattice d → ℤ} {lo hi k : ℤ}
    (hbound : BoundedBetween lo hi g)
    (hconv : tileConv F g = fun _ ↦ k) (hp : p.Prime)
    (hlarge : oscillationBound lo hi * F.card < p) :
    tileConv (dilate p F) g = fun _ ↦ k :=
  dilation_prime hbound hconv hp hlarge

/-- Paper Lemma 3.1(ii): dilation by an integer coprime to the controlling
primorial preserves convolution. -/
theorem lemma_3_1_ii {d r : ℕ} {F : Finset (Lattice d)}
    {g : Lattice d → ℤ} {lo hi k : ℤ}
    (hbound : BoundedBetween lo hi g)
    (hconv : tileConv F g = fun _ ↦ k) (hr : 0 < r)
    (hcop : Nat.Coprime r
      (primorial (oscillationBound lo hi * F.card))) :
    tileConv (dilate r F) g = fun _ ↦ k :=
  dilation_coprime hbound hconv hr hcop

/-- Paper Lemma 3.1(iii): the full periodic dilation congruence. -/
theorem lemma_3_1_iii {d ell r : ℕ}
    {F : Finset (Lattice d)} {g : Lattice d → ℤ} {lo hi : ℤ}
    (hbound : BoundedBetween lo hi g) (hell : 0 < ell)
    (hperiod : ScalarPeriodic ell (tileConv F g)) (hr : 0 < r)
    (hmod : Nat.ModEq
      (dilationModulus ell (oscillationBound lo hi) F.card) r 1) :
    tileConv (dilate r F) g = tileConv F g :=
  dilation_periodic hbound hell hperiod hr hmod

/-- Paper Theorem 3.4: the grouped structure decomposition with quantitative direction control. -/
theorem theorem_3_4 {d ell k : ℕ}
    {F : Finset (Lattice d)} {A E : Set (Lattice d)}
    (hd : 0 < d) (hell : 0 < ell) (hk : 0 < k)
    (hcard : 1 < F.card) (hzero : 0 ∈ F)
    (hE : SetScalarPeriodic ell E) (htile : TilesAtLevel F A E k) :
    Nonempty (GroupedStructureDecomposition F A E ell k) :=
  exists_groupedStructureDecomposition hd hell hk hcard hzero hE htile

/-- Paper Corollary 3.5: the exact universal period in one dimension. -/
theorem corollary_3_5
    {F : Finset ℤ} {A : Set ℤ} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : Function.Periodic
      (tileConv F (setIndicator A)) (ell : ℤ)) :
    Function.Periodic (setIndicator A) (universalPeriod1D ell F : ℤ) :=
  universal_period_one_dimensional hell hzero hperiod

/-- Paper Proposition 4.1(i): the line functions sum to zero in the circle. -/
theorem proposition_4_1_i
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (e x : Plane) (n : ℤ) :
    ∑ j, ((linePhi D e x j n : ℝ) : Torus) = 0 :=
  linePhi_sum_mod_one D e x n

/-- Paper Proposition 4.1(ii): every line function is represented by a
bounded-degree circle polynomial. -/
theorem proposition_4_1_ii
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) (j : Fin D.numberOfDirections) :
  ∃ P : CirclePolynomial (D.numberOfDirections - 2), ∀ n : ℤ,
    P n = (linePhi D (weakSliceVector F ell D.direction) x j n : Torus) :=
  linePhi_circlePolynomial D x j

/-- Paper Proposition 4.1(iii): two distinct line functions have total supremum at most one. -/
theorem proposition_4_1_iii
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) {i j : Fin D.numberOfDirections} (hij : i ≠ j) :
  sSup (Set.range (linePhi D (weakSliceVector F ell D.direction) x i)) +
    sSup (Set.range (linePhi D (weakSliceVector F ell D.direction) x j)) ≤ 1 :=
  linePhi_pair_sup_le_one D x hij

/-- Paper Lemma 4.2 with the effective Stechkin constant. -/
theorem lemma_4_2
    (d : ℕ) (hd : 0 < d) (P : CirclePolynomial d)
    (hrat : P.HasTorsionNonconstantCoeffs)
    (hnonconstant : ¬ P.FunctionConstant) :
  ‖completeSum P P.commonDenominator‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ)) :=
  complete_exponential_sum_paper_functionNonconstant d hd P hrat hnonconstant

/-- Big-O formulation of Paper Lemma 4.2 with the constant uniform in the polynomial. -/
theorem lemma_4_2_bigO (d : ℕ) (hd : 0 < d) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ P : CirclePolynomial d,
    P.HasTorsionNonconstantCoeffs → ¬ P.FunctionConstant →
    ‖completeSum P P.commonDenominator‖ ≤
      C * Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ)) :=
  complete_exponential_sum_paper_bigO d hd

/-- Paper Lemma 4.3: avoiding a positive rational ball forces a bounded period. -/
theorem lemma_4_3
    (P : CirclePolynomial d) (c : Torus) (eps : ℚ)
    (heps : 0 < eps) (hsmall : eps < 1 / 2)
    (havoid : P.AvoidsBall c eps) :
  ∃ Q, 0 < Q ∧ Q ≤ rigidityPeriodBound d eps ∧ P.PeriodicWith Q :=
  periodic_of_avoidsBall P c eps heps hsmall havoid

/-- The half-circle specialization of Paper Lemma 4.3 used by Proposition 4.4. -/
theorem lemma_4_3_halfCircle
    (P : CirclePolynomial d) (hhalf : P.HasHalfCircleLifts) :
  ∃ Q, 0 < Q ∧ Q ≤ halfCirclePeriodBound d ∧ P.PeriodicWith Q :=
  periodic_of_halfCircle P hhalf

/-- Paper Proposition 4.4, with the periodic-target hypothesis used in equation (29) explicit. -/
theorem proposition_4_4
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E) :
  CosetwisePeriodic A (weakLattice F ell D.direction D.number_pos)
    (fun j ↦ ((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) •
      D.direction j) :=
  coset_one_dimensional_periodicity D hell hE

/-- Paper Lemma 5.1: a tile-slice convolution inherits an explicit scalar period. -/
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

/-- Paper Corollary 5.3: replace a one-periodic tiling by an equivalent fully periodic one. -/
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

/-- Paper Theorem 5.4 in its singleton-safe completion form. -/
theorem theorem_5_4
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts) :
    Nonempty (PaperCompletionResult D) :=
  improve_weaklyPeriodic hF D hell hm

/-- Exact-certificate strengthening of Paper Theorem 5.4 for tiles with at least two points. -/
theorem theorem_5_4_exact
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (hcard : 1 < F.card)
    (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts) :
    Nonempty (CompletionCertificate D) :=
  improve_weaklyPeriodic_exact hF hcard D hell hm

/-- Structural quantitative strengthening of Paper Theorem 5.4. -/
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

/-- Paper Theorem 6.2 for scalar-periodic target codes. -/
theorem theorem_6_2
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hexists : ∃ A, Tiles F A E.toSet) :
  nonOnePeriodicTilingDecision F E = true ↔
    ∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A :=
  nonOnePeriodicTilingDecision_eq_true_iff hF hexists

/-- Paper Theorem 6.2 for the checked lattice-periodic wire format. -/
theorem theorem_6_2_lattice_input
    {F : Finset Plane} {E : LatticePeriodicSetCode}
    (hF : F.Nonempty) (hexists : ∃ A, Tiles F A E.toSet) :
  nonOnePeriodicTilingDecisionLatticeInput F E = true ↔
    ∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A :=
  nonOnePeriodicTilingDecisionLatticeInput_eq_true_iff hF hexists

end TranslationalTilings
