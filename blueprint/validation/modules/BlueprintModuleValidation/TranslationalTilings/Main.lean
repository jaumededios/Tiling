import TranslationalTilings.Algorithms
import TranslationalTilings.Counterexample

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 0468a1bc01ad7a76a4e135867ca23b531d7494121472e5f7153ff45d6f937846  blueprint/09-main-results.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/09-main-results.md:27; TranslationalTilings.theorem_1_3_i -/
namespace TranslationalTilings
theorem theorem_1_3_i
    {F : Finset Plane} {A E : Set Plane}
    (hF : F.Nonempty) (hperiodicE : IsPeriodic E)
    (htile : Tiles F A E) : WeaklyPeriodic A :=
  level_one_plane_weaklyPeriodic hF hperiodicE htile
end TranslationalTilings

/- blueprint/09-main-results.md:34; TranslationalTilings.theorem_1_3_ii -/
namespace TranslationalTilings
theorem theorem_1_3_ii :
    ∃ (F : Finset Plane) (A : Set Plane),
      F.card = 8 ∧ TilesAtLevel F A Set.univ 4 ∧ ¬ WeaklyPeriodic A :=
  Counterexample.exists_eight_element_level_four_not_weaklyPeriodic
end TranslationalTilings

/- blueprint/09-main-results.md:46; TranslationalTilings.theorem_1_4_uniform -/
namespace TranslationalTilings
theorem theorem_1_4_uniform
    {F : Finset Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  ∃ D : QuantitativeWeakPeriodData F ell,
    ∀ (E A : Set Plane), SetScalarPeriodic ell E → Tiles F A E →
      D.ValidFor A :=
  exists_quantitativeWeakPeriodData hell hzero hcard
end TranslationalTilings

/- blueprint/09-main-results.md:55; TranslationalTilings.theorem_1_4_l1 -/
namespace TranslationalTilings
theorem theorem_1_4_l1
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic ell E) (htile : Tiles F A E) :
  ∃ D : QuantitativeWeakPeriodData F ell, D.ValidFor A :=
  quantitative_weak_periodicity_l1 hell hzero hcard hE htile
end TranslationalTilings

/- blueprint/09-main-results.md:63; TranslationalTilings.theorem_1_4 -/
namespace TranslationalTilings
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
end TranslationalTilings

/- blueprint/09-main-results.md:94; TranslationalTilings.theorem_1_5_l1 -/
namespace TranslationalTilings
theorem theorem_1_5_l1
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (hexists : ∃ A, Tiles F A E) :
  ∃ C : PeriodicTilingCertificate F E ell,
    C.scalarMultiplier ≤ periodicTilingPeriodBound F.card (l1Diameter F) :=
  quantitative_periodic_tiling_l1 hell hE hexists
end TranslationalTilings

/- blueprint/09-main-results.md:103; TranslationalTilings.theorem_1_5 -/
namespace TranslationalTilings
theorem theorem_1_5
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (hexists : ∃ A, Tiles F A E) :
  ∃ (A' : Set Plane) (M : ℕ),
    0 < M ∧ Tiles F A' E ∧ SetScalarPeriodic (ell * M) A' ∧
    (M : ℝ) ≤ periodicTilingEuclideanConstant F.card *
      max 1 (euclideanDiameter F ^ periodicTilingExponent F.card) :=
  quantitative_periodic_tiling_euclidean hell hE hexists
end TranslationalTilings

/- blueprint/09-main-results.md:121; TranslationalTilings.corollary_1_6 -/
namespace TranslationalTilings
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
end TranslationalTilings

/- blueprint/09-main-results.md:142; TranslationalTilings.lemma_2_1 -/
namespace TranslationalTilings
theorem lemma_2_1 :
    ScalarPeriodic 4 Counterexample.chi ∧
      (∀ x, Counterexample.chi x = -1 ∨ Counterexample.chi x = 1) ∧
      tileConv {0, Counterexample.v₁} Counterexample.chi = 0 ∧
      tileConv {0, Counterexample.v₂} Counterexample.chi = 0 :=
  Counterexample.chi_lemma
end TranslationalTilings

/- blueprint/09-main-results.md:150; TranslationalTilings.theorem_1_7 -/
namespace TranslationalTilings
theorem theorem_1_7 {d ell : ℕ}
    {F : Finset (Lattice d)} {A : Set (Lattice d)}
    (hd : 0 < d) (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : ScalarPeriodic ell (tileConv F (setIndicator A))) :
    Nonempty (StructureDecomposition F A ell) :=
  exists_structureDecomposition hd hell hzero hperiod
end TranslationalTilings

/- blueprint/09-main-results.md:158; TranslationalTilings.lemma_3_1_i -/
namespace TranslationalTilings
theorem lemma_3_1_i {d p : ℕ} {F : Finset (Lattice d)}
    {g : Lattice d → ℤ} {lo hi k : ℤ}
    (hbound : BoundedBetween lo hi g)
    (hconv : tileConv F g = fun _ ↦ k) (hp : p.Prime)
    (hlarge : oscillationBound lo hi * F.card < p) :
    tileConv (dilate p F) g = fun _ ↦ k :=
  dilation_prime hbound hconv hp hlarge
end TranslationalTilings

/- blueprint/09-main-results.md:167; TranslationalTilings.lemma_3_1_ii -/
namespace TranslationalTilings
theorem lemma_3_1_ii {d r : ℕ} {F : Finset (Lattice d)}
    {g : Lattice d → ℤ} {lo hi k : ℤ}
    (hbound : BoundedBetween lo hi g)
    (hconv : tileConv F g = fun _ ↦ k) (hr : 0 < r)
    (hcop : Nat.Coprime r
      (primorial (oscillationBound lo hi * F.card))) :
    tileConv (dilate r F) g = fun _ ↦ k :=
  dilation_coprime hbound hconv hr hcop
end TranslationalTilings

/- blueprint/09-main-results.md:177; TranslationalTilings.lemma_3_1_iii -/
namespace TranslationalTilings
theorem lemma_3_1_iii {d ell r : ℕ}
    {F : Finset (Lattice d)} {g : Lattice d → ℤ} {lo hi : ℤ}
    (hbound : BoundedBetween lo hi g) (hell : 0 < ell)
    (hperiod : ScalarPeriodic ell (tileConv F g)) (hr : 0 < r)
    (hmod : Nat.ModEq
      (dilationModulus ell (oscillationBound lo hi) F.card) r 1) :
    tileConv (dilate r F) g = tileConv F g :=
  dilation_periodic hbound hell hperiod hr hmod
end TranslationalTilings

/- blueprint/09-main-results.md:187; TranslationalTilings.theorem_3_4 -/
namespace TranslationalTilings
theorem theorem_3_4 {d ell k : ℕ}
    {F : Finset (Lattice d)} {A E : Set (Lattice d)}
    (hd : 0 < d) (hell : 0 < ell) (hk : 0 < k)
    (hcard : 1 < F.card) (hzero : 0 ∈ F)
    (hE : SetScalarPeriodic ell E) (htile : TilesAtLevel F A E k) :
    Nonempty (GroupedStructureDecomposition F A E ell k) :=
  exists_groupedStructureDecomposition hd hell hk hcard hzero hE htile
end TranslationalTilings

/- blueprint/09-main-results.md:196; TranslationalTilings.corollary_3_5 -/
namespace TranslationalTilings
theorem corollary_3_5
    {F : Finset ℤ} {A : Set ℤ} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : Function.Periodic
      (tileConv F (setIndicator A)) (ell : ℤ)) :
    Function.Periodic (setIndicator A) (universalPeriod1D ell F : ℤ) :=
  universal_period_one_dimensional hell hzero hperiod
end TranslationalTilings

/- blueprint/09-main-results.md:205; TranslationalTilings.proposition_4_1_i -/
namespace TranslationalTilings
theorem proposition_4_1_i
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (e x : Plane) (n : ℤ) :
    ∑ j, ((linePhi D e x j n : ℝ) : Torus) = 0 :=
  linePhi_sum_mod_one D e x n
end TranslationalTilings

/- blueprint/09-main-results.md:213; TranslationalTilings.proposition_4_1_ii -/
namespace TranslationalTilings
theorem proposition_4_1_ii
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) (j : Fin D.numberOfDirections) :
  ∃ P : CirclePolynomial (D.numberOfDirections - 2), ∀ n : ℤ,
    P n = (linePhi D (weakSliceVector F ell D.direction) x j n : Torus) :=
  linePhi_circlePolynomial D x j
end TranslationalTilings

/- blueprint/09-main-results.md:222; TranslationalTilings.proposition_4_1_iii -/
namespace TranslationalTilings
theorem proposition_4_1_iii
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) {i j : Fin D.numberOfDirections} (hij : i ≠ j) :
  sSup (Set.range (linePhi D (weakSliceVector F ell D.direction) x i)) +
    sSup (Set.range (linePhi D (weakSliceVector F ell D.direction) x j)) ≤ 1 :=
  linePhi_pair_sup_le_one D x hij
end TranslationalTilings

/- blueprint/09-main-results.md:231; TranslationalTilings.lemma_4_2 -/
namespace TranslationalTilings
theorem lemma_4_2
    (d : ℕ) (hd : 0 < d) (P : CirclePolynomial d)
    (hrat : P.HasTorsionNonconstantCoeffs)
    (hnonconstant : ¬ P.FunctionConstant) :
  ‖completeSum P P.commonDenominator‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ)) :=
  complete_exponential_sum_paper_functionNonconstant d hd P hrat hnonconstant
end TranslationalTilings

/- blueprint/09-main-results.md:242; TranslationalTilings.lemma_4_2_bigO -/
namespace TranslationalTilings
theorem lemma_4_2_bigO (d : ℕ) (hd : 0 < d) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ P : CirclePolynomial d,
    P.HasTorsionNonconstantCoeffs → ¬ P.FunctionConstant →
    ‖completeSum P P.commonDenominator‖ ≤
      C * Real.rpow (P.commonDenominator : ℝ)
        (1 - (1 : ℝ) / (d : ℝ)) :=
  complete_exponential_sum_paper_bigO d hd
end TranslationalTilings

/- blueprint/09-main-results.md:251; TranslationalTilings.lemma_4_3 -/
namespace TranslationalTilings
theorem lemma_4_3
    (P : CirclePolynomial d) (c : Torus) (eps : ℚ)
    (heps : 0 < eps) (hsmall : eps < 1 / 2)
    (havoid : P.AvoidsBall c eps) :
  ∃ Q, 0 < Q ∧ Q ≤ rigidityPeriodBound d eps ∧ P.PeriodicWith Q :=
  periodic_of_avoidsBall P c eps heps hsmall havoid
end TranslationalTilings

/- blueprint/09-main-results.md:259; TranslationalTilings.lemma_4_3_halfCircle -/
namespace TranslationalTilings
theorem lemma_4_3_halfCircle
    (P : CirclePolynomial d) (hhalf : P.HasHalfCircleLifts) :
  ∃ Q, 0 < Q ∧ Q ≤ halfCirclePeriodBound d ∧ P.PeriodicWith Q :=
  periodic_of_halfCircle P hhalf
end TranslationalTilings

/- blueprint/09-main-results.md:265; TranslationalTilings.proposition_4_4 -/
namespace TranslationalTilings
theorem proposition_4_4
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E) :
  CosetwisePeriodic A (weakLattice F ell D.direction D.number_pos)
    (fun j ↦ ((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) •
      D.direction j) :=
  coset_one_dimensional_periodicity D hell hE
end TranslationalTilings

/- blueprint/09-main-results.md:275; TranslationalTilings.lemma_5_1 -/
namespace TranslationalTilings
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
end TranslationalTilings

/- blueprint/09-main-results.md:287; TranslationalTilings.corollary_5_3 -/
namespace TranslationalTilings
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
end TranslationalTilings

/- blueprint/09-main-results.md:304; TranslationalTilings.theorem_5_4 -/
namespace TranslationalTilings
theorem theorem_5_4
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts) :
    Nonempty (PaperCompletionResult D) :=
  improve_weaklyPeriodic hF D hell hm
end TranslationalTilings

/- blueprint/09-main-results.md:313; TranslationalTilings.theorem_5_4_exact -/
namespace TranslationalTilings
theorem theorem_5_4_exact
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (hcard : 1 < F.card)
    (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts) :
    Nonempty (CompletionCertificate D) :=
  improve_weaklyPeriodic_exact hF hcard D hell hm
end TranslationalTilings

/- blueprint/09-main-results.md:323; TranslationalTilings.theorem_5_4_structural -/
namespace TranslationalTilings
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
end TranslationalTilings

/- blueprint/09-main-results.md:336; TranslationalTilings.theorem_6_2 -/
namespace TranslationalTilings
theorem theorem_6_2
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hexists : ∃ A, Tiles F A E.toSet) :
  nonOnePeriodicTilingDecision F E = true ↔
    ∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A :=
  nonOnePeriodicTilingDecision_eq_true_iff hF hexists
end TranslationalTilings

/- blueprint/09-main-results.md:345; TranslationalTilings.theorem_6_2_lattice_input -/
namespace TranslationalTilings
theorem theorem_6_2_lattice_input
    {F : Finset Plane} {E : LatticePeriodicSetCode}
    (hF : F.Nonempty) (hexists : ∃ A, Tiles F A E.toSet) :
  nonOnePeriodicTilingDecisionLatticeInput F E = true ↔
    ∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A :=
  nonOnePeriodicTilingDecisionLatticeInput_eq_true_iff hF hexists
end TranslationalTilings
