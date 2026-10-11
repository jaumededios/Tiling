import TranslationalTilings.Slicing
import TranslationalTilings.WeakPeriodicity

/-!
# Quantitative completion of weakly periodic tilings

This file implements the slicing-based completion step and its quantitative
bounds.  The exact construction certificate is deliberately restricted to
non-singleton tiles; `PaperCompletionResult` provides the domain-total paper
statement and handles singleton tiles through a direct construction.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

private theorem indicator_eq_iff_membership {G : Type*}
    (A : Set G) (u v : G) :
    setIndicator A u = setIndicator A v ↔ (u ∈ A ↔ v ∈ A) := by
  by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;>
    simp [setIndicator, hu, hv]

private theorem indicator_scalarPeriodic {d q : ℕ}
    {E : Set (Lattice d)} (hE : SetScalarPeriodic q E) :
    ScalarPeriodic q (setIndicator E) := by
  intro x z
  apply (indicator_eq_iff_membership E _ _).2
  exact hE x z

/-- A tiling set partitioned into finitely many one-directional periodic parts. -/
structure DirectionalTilingDecomposition
    (F : Finset Plane) (A E : Set Plane) (ell : ℕ) where
  /-- Number of directional parts. -/
  numberOfParts : ℕ
  number_pos : 0 < numberOfParts
  /-- The directional parts whose disjoint union is `A`. -/
  part : Fin numberOfParts → Set Plane
  /-- The nonzero period direction assigned to each part. -/
  direction : Fin numberOfParts → Plane
  direction_ne_zero : ∀ j, direction j ≠ 0
  pairwise_incommensurable : PairwiseIncommensurable direction
  periodic_part : ∀ j,
    Function.Periodic (setIndicator (part j))
      (((ell : ℕ) : ℤ) • direction j)
  pairwiseDisjoint : Set.PairwiseDisjoint Set.univ part
  union_parts : (⋃ j, part j) = A
  target_periodic : SetScalarPeriodic ell E
  tiles : Tiles F A E

/-- Convert quantitative cosetwise periodicity into a directional partition. -/
theorem exists_directionalTilingDecomposition_of_quantitativeData
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (_hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (htile : Tiles F A E) (W : QuantitativeWeakPeriodData F ell)
    (hW : W.ValidFor A) :
    ∃ D : DirectionalTilingDecomposition F A E (ell * W.multiplier),
      ∃ hnum : D.numberOfParts = W.numberOfDirections,
        ∀ j : Fin W.numberOfDirections,
          D.direction (Fin.cast hnum.symm j) = W.direction j := by
  classical
  let Λ := W.lattice
  let periods : Fin W.numberOfDirections → Plane := fun j ↦
    (((ell * W.multiplier : ℕ) : ℤ) • W.direction j)
  have hfiber (c : Plane ⧸ Λ) :
      ∃ j : Fin W.numberOfDirections, ∀ y,
        y + periods j ∈ A ∩ quotientCoset Λ c ↔
          y ∈ A ∩ quotientCoset Λ c := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective Λ c
    have hcoset : quotientCoset Λ (QuotientAddGroup.mk' Λ x) =
        addCoset Λ x := by
      ext y
      exact QuotientAddGroup.eq_iff_sub_mem
    simpa only [QuantitativeWeakPeriodData.ValidFor, periods, Λ,
      hcoset] using hW x
  let chosen : Plane ⧸ Λ → Fin W.numberOfDirections := fun c ↦
    Classical.choose (hfiber c)
  have hchosen (c : Plane ⧸ Λ) (y : Plane) :
      y + periods (chosen c) ∈ A ∩ quotientCoset Λ c ↔
        y ∈ A ∩ quotientCoset Λ c :=
    Classical.choose_spec (hfiber c) y
  let part : Fin W.numberOfDirections → Set Plane := fun j ↦
    {y | y ∈ A ∧ chosen (QuotientAddGroup.mk' Λ y) = j}
  have hpartPeriodic (j : Fin W.numberOfDirections) :
      Function.Periodic (setIndicator (part j)) (periods j) := by
    intro y
    apply (indicator_eq_iff_membership (part j) _ _).2
    let c : Plane ⧸ Λ := QuotientAddGroup.mk' Λ y
    have hpMem : periods j ∈ Λ := by
      exact W.period_mem_lattice j
    have hquot : QuotientAddGroup.mk' Λ (y + periods j) = c := by
      dsimp [c]
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      simpa only [add_sub_cancel_left] using hpMem
    change (y + periods j ∈ A ∧
        chosen (QuotientAddGroup.mk' Λ (y + periods j)) = j) ↔
      (y ∈ A ∧ chosen (QuotientAddGroup.mk' Λ y) = j)
    rw [hquot]
    by_cases hc : chosen c = j
    · simp only [c, hc, and_true]
      have hs := hchosen c y
      rw [hc] at hs
      constructor
      · intro hy
        exact (hs.mp ⟨hy, hquot⟩).1
      · intro hy
        exact (hs.mpr ⟨hy, rfl⟩).1
    · have hcy : chosen (QuotientAddGroup.mk' Λ y) ≠ j := by
        simpa only [c] using hc
      simp only [hc, hcy, and_false]
  have htarget : SetScalarPeriodic (ell * W.multiplier) E := by
    intro x z
    have hp := hE x ((W.multiplier : ℤ) • z)
    have hshift : (((ell * W.multiplier : ℕ) : ℤ) • z) =
        (ell : ℤ) • ((W.multiplier : ℤ) • z) := by
      push_cast
      module
    rw [hshift]
    exact hp
  refine ⟨{
    numberOfParts := W.numberOfDirections
    number_pos := W.number_pos
    part := part
    direction := W.direction
    direction_ne_zero := W.direction_ne_zero
    pairwise_incommensurable := W.pairwise_incommensurable
    periodic_part := ?_
    pairwiseDisjoint := ?_
    union_parts := ?_
    target_periodic := htarget
    tiles := htile
  }, rfl, ?_⟩
  · exact hpartPeriodic
  · rw [Set.pairwiseDisjoint_iff]
    intro i _ j _ hnonempty
    obtain ⟨y, hyi, hyj⟩ := hnonempty
    exact hyi.2.symm.trans hyj.2
  · ext y
    constructor
    · intro hy
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
      exact hyj.1
    · intro hy
      apply Set.mem_iUnion.mpr
      exact ⟨chosen (QuotientAddGroup.mk' Λ y), hy, rfl⟩
  · intro j
    rfl

/-- Number of unordered tile-point pairs used in the slicing exponent. -/
def completionSliceExponent (tileCard : ℕ) : ℕ :=
  tileCard * (tileCard - 1) / 2

/-- The slicing exponent is positive for a non-singleton tile. -/
theorem completionSliceExponent_pos {tileCard : ℕ}
    (hcard : 1 < tileCard) :
    0 < completionSliceExponent tileCard := by
  unfold completionSliceExponent
  have heven := Nat.even_mul_pred_self tileCard
  have hdouble := Nat.two_mul_div_two_of_even heven
  apply Nat.pos_of_ne_zero
  intro hz
  have hzero : 2 * (tileCard * (tileCard - 1) / 2) = 0 := by rw [hz]
  rw [hdouble] at hzero
  exact (Nat.mul_ne_zero (by omega) (by omega)) hzero

/-- Closed bound for a component's convolution-period multiplier. -/
def completionConvolutionBound
    (numberOfParts directionProduct directionNorm : ℕ) : ℕ :=
  max 1 (directionProduct ^ (numberOfParts - 1) *
    (numberOfParts + 1) * directionNorm)

/-- Local completion constant for a fixed number of directional parts. -/
def completionLocalConstant (tileCard numberOfParts : ℕ) : ℕ :=
  (numberOfParts + 1) * 4 ^ (2 * tileCard)

/-- Closed bound for the multiplier used to improve one directional part. -/
def completionPartMultiplierBound
    (tileCard diameter numberOfParts directionNorm : ℕ) : ℕ :=
  completionLocalConstant tileCard numberOfParts *
    max 1 (directionNorm ^ (completionSliceExponent tileCard + 1)) *
    max 1 (diameter ^ completionSliceExponent tileCard)

/-- Closed bound for the exact weak-periodic completion multiplier. -/
def weakCompletionPeriodBound
    (tileCard diameter numberOfParts directionProduct : ℕ) : ℕ :=
  completionLocalConstant tileCard numberOfParts ^ numberOfParts *
    max 1 (directionProduct ^
      (numberOfParts + completionSliceExponent tileCard)) *
    max 1 (diameter ^
      (numberOfParts * completionSliceExponent tileCard))

/-- Cardinality-relaxed structural completion bound. -/
def structuralCompletionPeriodBound
    (tileCard diameter numberOfParts directionProduct : ℕ) : ℕ :=
  (tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
    max 1 (directionProduct ^
      (numberOfParts + completionSliceExponent tileCard)) *
    max 1 (diameter ^
      (numberOfParts * completionSliceExponent tileCard))

/-- Sharper completion bound for a decomposition with one part. -/
def onePartCompletionMultiplierBound
    (tileCard diameter directionNorm : ℕ) : ℕ :=
  4 ^ (2 * tileCard) *
    max 1 (directionNorm ^ (completionSliceExponent tileCard + 1)) *
    max 1 (diameter ^ completionSliceExponent tileCard)

/-- Diameter exponent in the final periodic-tiling estimate. -/
def periodicTilingExponent (tileCard : ℕ) : ℕ :=
  (tileCard - 1) * (tileCard ^ 2 + tileCard - 1)

/-- Cardinality-dependent constant in the final `ℓ¹` period bound. -/
def periodicTilingConstant (tileCard : ℕ) : ℕ :=
  weakPeriodMultiplierConstant tileCard *
    (tileCard * 4 ^ (2 * tileCard)) ^ tileCard

/-- Final closed `ℓ¹` period-multiplier bound. -/
def periodicTilingPeriodBound (tileCard diameter : ℕ) : ℕ :=
  max 1 (periodicTilingConstant tileCard *
    max 1 (diameter ^ periodicTilingExponent tileCard))

/-- The weak completion period bound is at least one. -/
theorem one_le_weakCompletionPeriodBound
    (tileCard diameter numberOfParts directionProduct : ℕ) :
    1 ≤ weakCompletionPeriodBound tileCard diameter numberOfParts
      directionProduct := by
  unfold weakCompletionPeriodBound completionLocalConstant
  have hlocal : 0 < ((numberOfParts + 1) * 4 ^ (2 * tileCard)) := by
    positivity
  have hpow : 1 ≤ ((numberOfParts + 1) * 4 ^ (2 * tileCard)) ^
      numberOfParts := Nat.one_le_pow _ _ hlocal
  have hrest : 0 < max 1 (directionProduct ^
      (numberOfParts + completionSliceExponent tileCard)) *
      max 1 (diameter ^ (numberOfParts * completionSliceExponent tileCard)) := by
    positivity
  exact le_trans hpow (by
    simpa only [Nat.mul_assoc] using
      (Nat.le_mul_of_pos_right
        (((numberOfParts + 1) * 4 ^ (2 * tileCard)) ^ numberOfParts) hrest))

/-- Checked singleton regression for the completion formulas at direction norm `4096`. -/
theorem completion_singleton_bound_regression :
    completionSliceExponent 1 = 0 ∧
    completionPartMultiplierBound 1 0 2 4096 < 4096 ^ 2 ∧
    weakCompletionPeriodBound 1 0 2 4096 < 4096 ^ 3 := by
  norm_num [completionPartMultiplierBound, weakCompletionPeriodBound,
    completionLocalConstant, completionSliceExponent]

/-- Pairwise wedge least common multiple of the decomposition directions. -/
def completionPairLCM
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) : ℕ :=
  pairWedgeLCM D.direction

/-- A bounded direction avoiding every decomposition direction. -/
def completionAvoidance
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) : Plane :=
  avoidanceVector D.direction

/-- Absolute wedge of the avoidance vector with one component direction. -/
def completionWedgeFactor
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  Int.natAbs (wedge (completionAvoidance D) (D.direction j))

/-- Multiplier that makes one component convolution scalar-periodic. -/
def completionConvolutionMultiplier
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  completionPairLCM D * completionWedgeFactor D j

/-- Primitive part of a component direction. -/
def completionPrimitiveDirection
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : Plane :=
  primitivePart (D.direction j)

/-- Integer content of a component direction. -/
def completionDirectionContent
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  vectorContent (D.direction j)

/-- Exact quotient between the dilation modulus and its base period. -/
def completionDilationRatio
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  indicatorDilationModulus
      (ell * completionConvolutionMultiplier D j) F.card /
    (ell * completionConvolutionMultiplier D j)

/-- Slicing least common multiple for a component's primitive direction. -/
def completionSliceLCM
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  slicingLCM F (completionPrimitiveDirection D j)

/-- Exact multiplier used to improve one directional component. -/
def completionPartMultiplier
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  completionWedgeFactor D j * completionDilationRatio D j *
    completionDirectionContent D j * completionSliceLCM D j

/-- Exact scalar multiplier of a completed directional decomposition. -/
def completionMultiplier
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) : ℕ :=
  completionPairLCM D *
    ∏ j : Fin D.numberOfParts, completionPartMultiplier D j

/-- Dilation quotient specialized to the one-part construction. -/
def onePartDilationRatio
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (_D : DirectionalTilingDecomposition F A E ell) : ℕ :=
  indicatorDilationModulus ell F.card / ell

/-- Exact scalar multiplier for the one-part completion. -/
def onePartCompletionMultiplier
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) : ℕ :=
  let j : Fin D.numberOfParts := ⟨0, D.number_pos⟩
  onePartDilationRatio D * completionDirectionContent D j *
    completionSliceLCM D j

/-- The one-part dilation modulus factors through `onePartDilationRatio`. -/
theorem onePartDilationRatio_spec
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) :
    indicatorDilationModulus ell F.card = ell * onePartDilationRatio D := by
  exact (Nat.mul_div_cancel' (ell_dvd_dilationModulus ell 1 F.card)).symm

/-- The one-part dilation ratio is positive when the base period is positive. -/
theorem onePartDilationRatio_pos
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) (hell : 0 < ell) :
    0 < onePartDilationRatio D := by
  have hqpos : 0 < indicatorDilationModulus ell F.card := by
    simpa [indicatorDilationModulus] using
      (dilationModulus_pos (oscillation := 1) (tileCard := F.card) hell)
  apply Nat.div_pos
  · exact Nat.le_of_dvd hqpos (ell_dvd_dilationModulus ell 1 F.card)
  · exact hell

/-- A periodic tiling together with its exact scalar-period multiplier. -/
structure PeriodicTilingCertificate
    (F : Finset Plane) (E : Set Plane) (ell : ℕ) where
  /-- The completed tiling set. -/
  tilingSet : Set Plane
  /-- Multiplier of the base scalar period `ell`. -/
  scalarMultiplier : ℕ
  multiplier_pos : 0 < scalarMultiplier
  periodic : SetScalarPeriodic (ell * scalarMultiplier) tilingSet
  tiles : Tiles F tilingSet E

/-- Rebase a certificate at period `ell * k` to one at period `ell`. -/
def PeriodicTilingCertificate.rebase
    {F : Finset Plane} {E : Set Plane} {ell k : ℕ} (hk : 0 < k)
    (C : PeriodicTilingCertificate F E (ell * k)) :
    PeriodicTilingCertificate F E ell where
  tilingSet := C.tilingSet
  scalarMultiplier := k * C.scalarMultiplier
  multiplier_pos := Nat.mul_pos hk C.multiplier_pos
  periodic := by simpa [Nat.mul_assoc] using C.periodic
  tiles := C.tiles

/-- Exact completion data for a non-singleton directional decomposition. -/
structure CompletionCertificate
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) where
  /-- The resulting periodic tiling certificate. -/
  completed : PeriodicTilingCertificate F E ell
  convolutionMultiplier_pos : ∀ j,
    0 < completionConvolutionMultiplier D j
  convolutionMultiplier_bound : ∀ j,
    completionConvolutionMultiplier D j ≤
      completionConvolutionBound D.numberOfParts
      (∏ i : Fin D.numberOfParts, l1Norm (D.direction i))
      (l1Norm (D.direction j))
  convolution_periodic : ∀ j,
    ScalarPeriodic (ell * completionConvolutionMultiplier D j)
      (tileConv F (setIndicator (D.part j)))
  primitive_direction : ∀ j, IsPrimitive (completionPrimitiveDirection D j)
  direction_decomposition : ∀ j,
    D.direction j =
      (completionDirectionContent D j : ℤ) • completionPrimitiveDirection D j
  dilation_ratio_spec : ∀ j,
    indicatorDilationModulus
        (ell * completionConvolutionMultiplier D j) F.card =
      (ell * completionConvolutionMultiplier D j) *
        completionDilationRatio D j
  partMultiplier_pos : ∀ j, 0 < completionPartMultiplier D j
  partMultiplier_bound : ∀ j,
    completionPartMultiplier D j ≤ completionPartMultiplierBound F.card
      (l1Diameter F) D.numberOfParts (l1Norm (D.direction j))
  /-- Improved component sets, one for each original directional part. -/
  improvedPart : Fin D.numberOfParts → Set Plane
  improved_convolution : ∀ j,
    convolutionEquivalent F (D.part j) (improvedPart j)
  improved_periodic : ∀ j,
    SetScalarPeriodic
      (ell * completionPairLCM D * completionPartMultiplier D j)
      (improvedPart j)
  improved_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ improvedPart
  improved_union : (⋃ j, improvedPart j) = completed.tilingSet
  completed_multiplier_exact :
    completed.scalarMultiplier = completionMultiplier D
  completedMultiplier_bound :
    completed.scalarMultiplier ≤ weakCompletionPeriodBound F.card
      (l1Diameter F) D.numberOfParts
      (∏ i : Fin D.numberOfParts, l1Norm (D.direction i))

/-- Paper-facing completion result, totalized to include singleton tiles. -/
structure PaperCompletionResult
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) where
  /-- The resulting periodic tiling certificate. -/
  completed : PeriodicTilingCertificate F E ell
  completedMultiplier_bound :
    completed.scalarMultiplier ≤ weakCompletionPeriodBound F.card
      (l1Diameter F) D.numberOfParts
      (∏ i : Fin D.numberOfParts, l1Norm (D.direction i))
  component_convolution : ∀ j,
    0 < completionConvolutionMultiplier D j ∧
      completionConvolutionMultiplier D j ≤
        completionConvolutionBound D.numberOfParts
          (∏ i : Fin D.numberOfParts, l1Norm (D.direction i))
          (l1Norm (D.direction j)) ∧
      ScalarPeriodic (ell * completionConvolutionMultiplier D j)
        (tileConv F (setIndicator (D.part j)))

/-- Forget the internal exact data of a completion certificate. -/
def CompletionCertificate.toPaperCompletionResult
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    {D : DirectionalTilingDecomposition F A E ell}
    (C : CompletionCertificate D) : PaperCompletionResult D where
  completed := C.completed
  completedMultiplier_bound := C.completedMultiplier_bound
  component_convolution := fun j ↦ ⟨C.convolutionMultiplier_pos j,
    C.convolutionMultiplier_bound j, C.convolution_periodic j⟩

/-- The exact weak bound is dominated by the cardinality-relaxed structural bound. -/
theorem weakCompletionPeriodBound_le_structuralCompletionPeriodBound
    {tileCard diameter numberOfParts directionProduct : ℕ}
    (hmpos : 0 < numberOfParts)
    (hmcard : numberOfParts ≤ tileCard - 1) :
    weakCompletionPeriodBound tileCard diameter numberOfParts directionProduct ≤
      structuralCompletionPeriodBound tileCard diameter numberOfParts
        directionProduct := by
  have hmc : numberOfParts < tileCard := lt_of_le_of_lt hmcard (by
    omega : tileCard - 1 < tileCard)
  have hbase : completionLocalConstant tileCard numberOfParts ≤
      tileCard * 4 ^ (2 * tileCard) := by
    unfold completionLocalConstant
    gcongr
    omega
  have htilepos : 0 < tileCard := lt_trans hmpos hmc
  have hpow : completionLocalConstant tileCard numberOfParts ^ numberOfParts ≤
      (tileCard * 4 ^ (2 * tileCard)) ^ tileCard := by
    calc
      completionLocalConstant tileCard numberOfParts ^ numberOfParts ≤
          (tileCard * 4 ^ (2 * tileCard)) ^ numberOfParts :=
        Nat.pow_le_pow_left hbase _
      _ ≤ (tileCard * 4 ^ (2 * tileCard)) ^ tileCard :=
        Nat.pow_le_pow_right (by positivity) (le_of_lt hmc)
  unfold weakCompletionPeriodBound structuralCompletionPeriodBound
  gcongr

/-- Bound a completed multiplier by the structural completion formula. -/
theorem CompletionCertificate.completedMultiplier_structural_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    {D : DirectionalTilingDecomposition F A E ell}
    (C : CompletionCertificate D)
    (hmcard : D.numberOfParts ≤ F.card - 1) :
    C.completed.scalarMultiplier ≤
      structuralCompletionPeriodBound F.card (l1Diameter F) D.numberOfParts
        (∏ i : Fin D.numberOfParts, l1Norm (D.direction i)) :=
  C.completedMultiplier_bound.trans
    (weakCompletionPeriodBound_le_structuralCompletionPeriodBound
      D.number_pos hmcard)

/-- At least two structural parts force the tile to be non-singleton. -/
theorem one_lt_tileCard_of_structural_parts
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    {D : DirectionalTilingDecomposition F A E ell}
    (hm : 2 ≤ D.numberOfParts)
    (hmcard : D.numberOfParts ≤ F.card - 1) :
    1 < F.card := by
  omega

/-- Complete a directional tiling consisting of exactly one part. -/
theorem improve_onePart
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hone : D.numberOfParts = 1) :
    ∃ C : PeriodicTilingCertificate F E ell,
      C.scalarMultiplier = onePartCompletionMultiplier D ∧
      C.scalarMultiplier ≤ onePartCompletionMultiplierBound F.card
        (l1Diameter F) (l1Norm (D.direction ⟨0, D.number_pos⟩)) := by
  classical
  let j : Fin D.numberOfParts := ⟨0, D.number_pos⟩
  have hfin (i : Fin D.numberOfParts) : i = j := by
    apply Fin.ext
    have hi := i.isLt
    dsimp [j]
    omega
  have hpartA : D.part j = A := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [← D.union_parts]
      exact Set.mem_iUnion.mpr ⟨j, hx⟩
    · intro x hx
      rw [← D.union_parts] at hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      simpa only [hfin i] using hxi
  have hdecomp := primitive_decomposition (D.direction_ne_zero j)
  have hprimitive : IsPrimitive (completionPrimitiveDirection D j) := by
    exact hdecomp.2
  have hcontentPos : 0 < completionDirectionContent D j :=
    vectorContent_pos (D.direction_ne_zero j)
  have hperiodPart : Function.Periodic (setIndicator (D.part j))
      (((ell * completionDirectionContent D j : ℕ) : ℤ) •
        completionPrimitiveDirection D j) := by
    have hp := D.periodic_part j
    have hshift : (((ell * completionDirectionContent D j : ℕ) : ℤ) •
        completionPrimitiveDirection D j) =
        ((ell : ℕ) : ℤ) • D.direction j := by
      calc
        (((ell * completionDirectionContent D j : ℕ) : ℤ) •
            completionPrimitiveDirection D j) =
            (ell : ℤ) • ((completionDirectionContent D j : ℤ) •
              completionPrimitiveDirection D j) := by
          push_cast
          module
        _ = (ell : ℤ) • D.direction j := congrArg ((ell : ℤ) • ·) hdecomp.1
    rw [hshift]
    exact hp
  have hconvPeriod : ScalarPeriodic ell
      (tileConv F (setIndicator (D.part j))) := by
    intro x z
    rw [hpartA, D.tiles x, D.tiles (x + (ell : ℤ) • z)]
    rw [indicator_scalarPeriodic D.target_periodic x z]
  obtain ⟨A', hA'period, hconv, -⟩ := improve_onePeriodic
    hell hcontentPos hprimitive hperiodPart hconvPeriod
  have hratioSpec := onePartDilationRatio_spec D
  have hperiodExact : SetScalarPeriodic
      (ell * onePartCompletionMultiplier D) A' := by
    have hcoeff : ell * onePartCompletionMultiplier D =
        indicatorDilationModulus ell F.card * completionDirectionContent D j *
          completionSliceLCM D j := by
      simp only [onePartCompletionMultiplier]
      rw [hratioSpec]
      simp only [j]
      ring
    rw [hcoeff]
    exact hA'period
  have htiles : Tiles F A' E := by
    intro x
    have hc := congrFun hconv x
    rw [hpartA] at hc
    rw [← hc]
    exact D.tiles x
  have hmultPos : 0 < onePartCompletionMultiplier D := by
    simp only [onePartCompletionMultiplier]
    exact Nat.mul_pos
      (Nat.mul_pos (onePartDilationRatio_pos D hell) hcontentPos)
      (slicingLCM_pos F (completionPrimitiveDirection D j))
  have hratioBound : onePartDilationRatio D ≤ 4 ^ (2 * F.card) := by
    apply Nat.div_le_of_le_mul
    simpa [onePartDilationRatio, Nat.mul_comm] using
      (grouped_q_bound (ell := ell) (F := F))
  let r := completionSliceExponent F.card
  let p := l1Norm (completionPrimitiveDirection D j)
  let H := l1Norm (D.direction j)
  let Δ := l1Diameter F
  have hpPos : 0 < p := by
    rw [Nat.pos_iff_ne_zero]
    exact (l1Norm_eq_zero.not.mpr hprimitive.1)
  have hnormEq : completionDirectionContent D j * p = H := by
    calc
      completionDirectionContent D j * p =
          l1Norm ((completionDirectionContent D j : ℤ) •
            completionPrimitiveDirection D j) := by
        rw [l1Norm_zsmul]
        simp [p]
      _ = H := congrArg l1Norm hdecomp.1
  have hcontent_le : completionDirectionContent D j ≤ H := by
    rw [← hnormEq]
    exact Nat.le_mul_of_pos_right _ hpPos
  have hp_le : p ≤ H := by
    rw [← hnormEq]
    exact Nat.le_mul_of_pos_left _ hcontentPos
  have hsliceBound : completionSliceLCM D j ≤ (p * Δ) ^ r := by
    exact slicingLCM_bound F hprimitive
  have hcontentSlice :
      completionDirectionContent D j * completionSliceLCM D j ≤
        H ^ (r + 1) * Δ ^ r := by
    calc
      completionDirectionContent D j * completionSliceLCM D j ≤
          completionDirectionContent D j * (p * Δ) ^ r :=
        Nat.mul_le_mul_left _ hsliceBound
      _ = completionDirectionContent D j * p ^ r * Δ ^ r := by
        rw [Nat.mul_pow]
        ring
      _ ≤ H * H ^ r * Δ ^ r := by
        gcongr
      _ = H ^ (r + 1) * Δ ^ r := by
        rw [pow_succ]
        ring
  let C : PeriodicTilingCertificate F E ell := {
    tilingSet := A'
    scalarMultiplier := onePartCompletionMultiplier D
    multiplier_pos := hmultPos
    periodic := hperiodExact
    tiles := htiles
  }
  refine ⟨C, rfl, ?_⟩
  change onePartCompletionMultiplier D ≤ _
  unfold onePartCompletionMultiplier onePartCompletionMultiplierBound
  dsimp only
  calc
    onePartDilationRatio D * completionDirectionContent D j *
        completionSliceLCM D j ≤
        4 ^ (2 * F.card) * (H ^ (r + 1) * Δ ^ r) := by
      calc
        onePartDilationRatio D * completionDirectionContent D j *
            completionSliceLCM D j =
            onePartDilationRatio D *
              (completionDirectionContent D j * completionSliceLCM D j) := by ring
        _ ≤ 4 ^ (2 * F.card) * (H ^ (r + 1) * Δ ^ r) :=
          Nat.mul_le_mul hratioBound hcontentSlice
    _ ≤ 4 ^ (2 * F.card) * max 1 (H ^ (r + 1)) *
        max 1 (Δ ^ r) := by
      exact (Nat.mul_le_mul_left (4 ^ (2 * F.card))
        (Nat.mul_le_mul (le_max_right _ _) (le_max_right _ _))).trans_eq (by ring)
    _ = 4 ^ (2 * F.card) *
        max 1 (l1Norm (D.direction ⟨0, D.number_pos⟩) ^
          (completionSliceExponent F.card + 1)) *
        max 1 (l1Diameter F ^ completionSliceExponent F.card) := by
      simp only [H, r, Δ, j]

private theorem mem_generatedPair_iff (u v x : Plane) :
    x ∈ generatedPair u v ↔ ∃ a b : ℤ, x = a • u + b • v := by
  let H : AddSubgroup Plane := {
    carrier := {x | ∃ a b : ℤ, x = a • u + b • v}
    zero_mem' := ⟨0, 0, by simp⟩
    add_mem' := by
      rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
      refine ⟨a + c, b + d, ?_⟩
      module
    neg_mem' := by
      rintro x ⟨a, b, rfl⟩
      refine ⟨-a, -b, ?_⟩
      module
  }
  constructor
  · intro hx
    have hle : generatedPair u v ≤ H := by
      rw [generatedPair, AddSubgroup.closure_le]
      rintro y (rfl | rfl)
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    exact hle hx
  · rintro ⟨a, b, rfl⟩
    exact (generatedPair u v).add_mem
      ((generatedPair u v).zsmul_mem (AddSubgroup.subset_closure (by simp)) a)
      ((generatedPair u v).zsmul_mem (AddSubgroup.subset_closure (by simp)) b)

private theorem backwardDiff_applyDifferences_local
    {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (h : G) (directions : List G) (f : G → R) :
    backwardDiff h (applyDifferences directions f) =
      applyDifferences directions (backwardDiff h f) := by
  induction directions with
  | nil => rfl
  | cons k directions ih =>
      change backwardDiff h (backwardDiff k (applyDifferences directions f)) =
        backwardDiff k (applyDifferences directions (backwardDiff h f))
      rw [backwardDiff_comm, ih]

private theorem applyDifferences_zero_local
    {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (directions : List G) :
    applyDifferences directions (0 : G → R) = 0 := by
  induction directions with
  | nil => rfl
  | cons h directions ih =>
      change backwardDiff h (applyDifferences directions (0 : G → R)) = 0
      rw [ih]
      funext x
      simp [backwardDiff]

private theorem applyDifferences_eq_zero_of_periodic_mem_local
    {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (directions : List G) (h : G) (f : G → R)
    (hmem : h ∈ directions) (hperiod : Function.Periodic f h) :
    applyDifferences directions f = 0 := by
  induction directions with
  | nil => simp at hmem
  | cons k directions ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem
      · change backwardDiff h (applyDifferences directions f) = 0
        rw [backwardDiff_applyDifferences_local,
          backwardDiff_eq_zero_of_periodic h f hperiod,
          applyDifferences_zero_local]
      · change backwardDiff k (applyDifferences directions f) = 0
        rw [ih hmem]
        funext x
        simp only [backwardDiff, Pi.zero_apply, sub_self]

private theorem lineRestriction_backwardDiffIter_local
    {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (f : G → R) (x h : G) (n : ℕ) :
    lineRestriction (backwardDiffIter h n f) x h =
      backwardDiffIter 1 n (lineRestriction f x h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [backwardDiffIter, Function.iterate_succ_apply',
        backwardDiffIter, Function.iterate_succ_apply']
      rw [lineRestriction_backwardDiff]
      exact congrArg (backwardDiff 1) ih

private theorem setIndicator_iUnion_eq_sum {m : ℕ}
    (part : Fin m → Set Plane)
    (hdisjoint : Set.PairwiseDisjoint Set.univ part) :
    setIndicator (⋃ j, part j) = ∑ j, setIndicator (part j) := by
  have hd : ((↑(Finset.univ : Finset (Fin m))) : Set (Fin m)).PairwiseDisjoint
      part := by
    simpa only [Finset.coe_univ] using hdisjoint
  funext x
  simp only [setIndicator]
  rw [Finset.sum_apply]
  change ((⋃ j, part j).indicator (fun _ ↦ (1 : ℤ))) x =
    ∑ j, (part j).indicator (fun _ ↦ (1 : ℤ)) x
  simpa only [Finset.mem_univ, Set.iUnion_true] using congrFun
    (Finset.indicator_biUnion (Finset.univ : Finset (Fin m)) part hd
      (f := fun _ ↦ (1 : ℤ))) x

/-- Each component convolution has the advertised positive scalar period and bound. -/
theorem convolution_part_scalarPeriodic
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (hm : 2 ≤ D.numberOfParts) (j : Fin D.numberOfParts) :
    0 < completionConvolutionMultiplier D j ∧
      completionConvolutionMultiplier D j ≤
        completionConvolutionBound D.numberOfParts
        (∏ i : Fin D.numberOfParts, l1Norm (D.direction i))
        (l1Norm (D.direction j)) ∧
      ScalarPeriodic (ell * completionConvolutionMultiplier D j)
        (tileConv F (setIndicator (D.part j))) := by
  classical
  let N := completionPairLCM D
  let eTilde := completionAvoidance D
  let e : Plane := (((ell * N : ℕ) : ℤ) • eTilde)
  let component : Fin D.numberOfParts → Plane → ℤ := fun i ↦
    tileConv F (setIndicator (D.part i))
  let period : Fin D.numberOfParts → Plane := fun i ↦
    ((ell : ℕ) : ℤ) • D.direction i
  have hNpos : 0 < N := pairWedgeLCM_pos
    D.direction_ne_zero D.pairwise_incommensurable
  have havoid := avoidanceVector_spec D.direction_ne_zero
  have hwedgeNe : wedge eTilde (D.direction j) ≠ 0 := by
    intro hw
    exact havoid.2.1 j
      ((commensurable_iff_wedge_eq_zero havoid.1 (D.direction_ne_zero j)).2 hw)
  have hwedgePos : 0 < completionWedgeFactor D j := by
    exact Int.natAbs_pos.mpr hwedgeNe
  have hmultPos : 0 < completionConvolutionMultiplier D j := by
    exact Nat.mul_pos hNpos hwedgePos
  have hNbound : N ≤
      (∏ i : Fin D.numberOfParts, l1Norm (D.direction i)) ^
        (D.numberOfParts - 1) := by
    simpa only [N, completionPairLCM, Finset.prod_pow] using
      (pairWedgeLCM_bound D.direction_ne_zero D.pairwise_incommensurable)
  have hwedgeBound : completionWedgeFactor D j ≤
      (D.numberOfParts + 1) * l1Norm (D.direction j) := by
    calc
      completionWedgeFactor D j ≤
          l1Norm eTilde * l1Norm (D.direction j) :=
        natAbs_wedge_le_l1Norm_mul_l1Norm _ _
      _ ≤ (D.numberOfParts + 1) * l1Norm (D.direction j) :=
        Nat.mul_le_mul_right _ havoid.2.2
  have hmultBound : completionConvolutionMultiplier D j ≤
      completionConvolutionBound D.numberOfParts
        (∏ i : Fin D.numberOfParts, l1Norm (D.direction i))
        (l1Norm (D.direction j)) := by
    apply le_max_of_le_right
    unfold completionConvolutionMultiplier
    exact (Nat.mul_le_mul hNbound hwedgeBound).trans_eq (by ring)
  have hindicator : setIndicator A = ∑ i, setIndicator (D.part i) := by
    calc
      setIndicator A = setIndicator (⋃ i, D.part i) :=
        congrArg setIndicator D.union_parts.symm
      _ = ∑ i, setIndicator (D.part i) :=
        setIndicator_iUnion_eq_sum D.part D.pairwiseDisjoint
  have hcomponentSum : setIndicator E = ∑ i, component i := by
    funext x
    have ht := D.tiles x
    have ht' : tileConv F (setIndicator A) x = setIndicator E x := by
      norm_num at ht ⊢
      exact ht
    rw [hindicator] at ht'
    rw [← ht']
    simp only [component, Finset.sum_apply, tileConv]
    rw [Finset.sum_comm]
  have hcomponentPeriod (i : Fin D.numberOfParts) :
      Function.Periodic (component i) (period i) := by
    intro x
    unfold component tileConv
    apply Finset.sum_congr rfl
    intro f _
    change setIndicator (D.part i) (x + period i - f) =
      setIndicator (D.part i) (x - f)
    rw [show x + period i - f = (x - f) + period i by abel]
    exact D.periodic_part i (x - f)
  have hrepresent (i : Fin D.numberOfParts) (hij : i ≠ j) :
      ∃ a b : ℤ, e = a • period i + b • period j := by
    have hmem : ((N : ℕ) : ℤ) • eTilde ∈
        generatedPair (D.direction i) (D.direction j) := by
      apply pairWedgeLCM_scalarLattice_le D.direction_ne_zero
        D.pairwise_incommensurable hij
      exact ⟨eTilde, rfl⟩
    obtain ⟨a, b, hab⟩ := (mem_generatedPair_iff _ _ _).1 hmem
    refine ⟨a, b, ?_⟩
    calc
      e = (ell : ℤ) • (((N : ℕ) : ℤ) • eTilde) := by
        dsimp [e]
        module
      _ = (ell : ℤ) • (a • D.direction i + b • D.direction j) :=
        congrArg ((ell : ℤ) • ·) hab
      _ = a • period i + b • period j := by
        dsimp [period]
        module
  let coefficient : Fin D.numberOfParts → ℤ := fun i ↦
    if hij : i = j then 0 else
      Classical.choose (Classical.choose_spec (hrepresent i hij))
  have hrepresent' (i : Fin D.numberOfParts) (hij : i ≠ j) :
      ∃ a : ℤ, e = a • period i + coefficient i • period j := by
    simp only [coefficient, dif_neg hij]
    exact ⟨Classical.choose (hrepresent i hij),
      Classical.choose_spec (Classical.choose_spec (hrepresent i hij))⟩
  have heliminate := eliminate_periodic_summands j (setIndicator E) component
    e period coefficient hcomponentSum hcomponentPeriod hrepresent'
  have : Nontrivial (Fin D.numberOfParts) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simp only [Fintype.card_fin]
      omega)
  obtain ⟨i, hij⟩ := exists_ne j
  let d := e - coefficient i • period j
  have hdMem : d ∈ eliminationDirections j e period coefficient := by
    apply List.mem_map_of_mem
    simp [hij]
  have hdScalar : d ∈ scalarLattice ell := by
    refine (scalarLattice ell).sub_mem ?_ ((scalarLattice ell).zsmul_mem ?_ _)
    · refine ⟨((N : ℤ) • eTilde), ?_⟩
      change (ell : ℤ) • ((N : ℤ) • eTilde) = e
      dsimp [e]
      module
    · exact ⟨D.direction j, rfl⟩
  obtain ⟨zd, hzd⟩ := hdScalar
  have hEperiod : Function.Periodic (setIndicator E) d := by
    rw [← hzd]
    exact fun x ↦ indicator_scalarPeriodic D.target_periodic x zd
  have hleftZero : applyDifferences
      (eliminationDirections j e period coefficient) (setIndicator E) = 0 :=
    applyDifferences_eq_zero_of_periodic_mem_local _ d _ hdMem hEperiod
  rw [hleftZero] at heliminate
  have hiterZero : backwardDiffIter e (D.numberOfParts - 1) (component j) = 0 :=
    by simpa only [Fintype.card_fin] using heliminate.symm
  have hePeriod : Function.Periodic (component j) e := by
    intro x
    have hbounded : ∃ C : ℕ, ∀ z,
        Int.natAbs (lineRestriction (component j) x e z) ≤ C := by
      refine ⟨F.card, ?_⟩
      intro z
      simp only [lineRestriction, component, tileConv_indicator_eq_card]
      simp only [Int.natAbs_natCast]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have hlineDiff : backwardDiffIter 1 (D.numberOfParts - 1)
        (lineRestriction (component j) x e) = 0 := by
      rw [← lineRestriction_backwardDiffIter_local]
      rw [hiterZero]
      rfl
    have hlinePeriod := bounded_of_backwardDiffIter_eq_zero_is_constant
      (D.numberOfParts - 1) (by omega) _ hbounded hlineDiff
    simpa [lineRestriction] using hlinePeriod 0
  have hscalarPeriod : ScalarPeriodic
      (ell * completionConvolutionMultiplier D j) (component j) := by
    intro x z
    let u : Plane := (N : ℤ) • eTilde
    let w := completionWedgeFactor D j
    have hwedge : Int.natAbs (wedge u (D.direction j)) = N * w := by
      dsimp [u, w, completionWedgeFactor, eTilde, N]
      rw [wedge_zsmul_left, Int.natAbs_mul]
      simp
    have hmem : (((N * w : ℕ) : ℤ) • z) ∈
        generatedPair u (D.direction j) := by
      rw [← hwedge]
      exact scalarLattice_natAbs_wedge_le_generatedPair u (D.direction j)
        ⟨z, rfl⟩
    obtain ⟨a, b, hab⟩ := (mem_generatedPair_iff _ _ _).1 hmem
    have hpj := hcomponentPeriod j
    have hcomb := (hePeriod.zsmul a).add_period (hpj.zsmul b)
    have hshift : (((ell * completionConvolutionMultiplier D j : ℕ) : ℤ) • z) =
        a • e + b • period j := by
      have hs := congrArg (fun v : Plane ↦ (ell : ℤ) • v) hab
      dsimp [N, w, u, e, eTilde, period] at hs ⊢
      simpa only [completionConvolutionMultiplier, Nat.cast_mul, smul_add,
        smul_smul, mul_comm,
        mul_left_comm, mul_assoc] using hs
    rw [hshift]
    exact hcomb x
  exact ⟨hmultPos, hmultBound, hscalarPeriod⟩

private theorem completion_part_arithmetic
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hcard : 1 < F.card)
    (j : Fin D.numberOfParts)
    (hconvPos : 0 < completionConvolutionMultiplier D j) :
    IsPrimitive (completionPrimitiveDirection D j) ∧
      D.direction j =
        (completionDirectionContent D j : ℤ) •
          completionPrimitiveDirection D j ∧
      indicatorDilationModulus
          (ell * completionConvolutionMultiplier D j) F.card =
        (ell * completionConvolutionMultiplier D j) *
          completionDilationRatio D j ∧
      0 < completionPartMultiplier D j ∧
      completionPartMultiplier D j ≤ completionPartMultiplierBound F.card
        (l1Diameter F) D.numberOfParts (l1Norm (D.direction j)) := by
  have hdecomp := primitive_decomposition (D.direction_ne_zero j)
  have hprimitive : IsPrimitive (completionPrimitiveDirection D j) := hdecomp.2
  have hdirection : D.direction j =
      (completionDirectionContent D j : ℤ) •
        completionPrimitiveDirection D j := by
    exact hdecomp.1.symm
  have hcontentPos : 0 < completionDirectionContent D j :=
    vectorContent_pos (D.direction_ne_zero j)
  have hdenomPos : 0 < ell * completionConvolutionMultiplier D j :=
    Nat.mul_pos hell hconvPos
  have hratioSpec : indicatorDilationModulus
        (ell * completionConvolutionMultiplier D j) F.card =
      (ell * completionConvolutionMultiplier D j) *
        completionDilationRatio D j := by
    exact (Nat.mul_div_cancel' (ell_dvd_dilationModulus
      (ell * completionConvolutionMultiplier D j) 1 F.card)).symm
  have hqPos : 0 < indicatorDilationModulus
      (ell * completionConvolutionMultiplier D j) F.card := by
    simpa [indicatorDilationModulus] using
      (dilationModulus_pos (oscillation := 1) (tileCard := F.card) hdenomPos)
  have hratioPos : 0 < completionDilationRatio D j := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hqPos (ell_dvd_dilationModulus
        (ell * completionConvolutionMultiplier D j) 1 F.card)
    · exact hdenomPos
  have hwedgePos : 0 < completionWedgeFactor D j := by
    exact Nat.pos_of_mul_pos_left hconvPos
  have hpartPos : 0 < completionPartMultiplier D j := by
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos hwedgePos hratioPos) hcontentPos)
      (slicingLCM_pos F (completionPrimitiveDirection D j))
  have hratioBound : completionDilationRatio D j ≤ 4 ^ (2 * F.card) := by
    apply Nat.div_le_of_le_mul
    simpa [completionDilationRatio, Nat.mul_comm] using
      (grouped_q_bound
        (ell := ell * completionConvolutionMultiplier D j) (F := F))
  have havoid := avoidanceVector_spec D.direction_ne_zero
  have hwedgeBound : completionWedgeFactor D j ≤
      (D.numberOfParts + 1) * l1Norm (D.direction j) := by
    calc
      completionWedgeFactor D j ≤
          l1Norm (completionAvoidance D) * l1Norm (D.direction j) :=
        natAbs_wedge_le_l1Norm_mul_l1Norm _ _
      _ ≤ (D.numberOfParts + 1) * l1Norm (D.direction j) := by
        exact Nat.mul_le_mul_right _ havoid.2.2
  let r := completionSliceExponent F.card
  let p := l1Norm (completionPrimitiveDirection D j)
  let H := l1Norm (D.direction j)
  let Δ := l1Diameter F
  have hrPos : 0 < r := completionSliceExponent_pos hcard
  have hpPos : 0 < p := by
    rw [Nat.pos_iff_ne_zero]
    exact (l1Norm_eq_zero.not.mpr hprimitive.1)
  have hnormEq : completionDirectionContent D j * p = H := by
    calc
      completionDirectionContent D j * p =
          l1Norm ((completionDirectionContent D j : ℤ) •
            completionPrimitiveDirection D j) := by
        rw [l1Norm_zsmul]
        simp [p]
      _ = H := congrArg l1Norm hdecomp.1
  have hp_le : p ≤ H := by
    rw [← hnormEq]
    exact Nat.le_mul_of_pos_left _ hcontentPos
  have hsliceBound : completionSliceLCM D j ≤ (p * Δ) ^ r :=
    slicingLCM_bound F hprimitive
  let r' := r - 1
  have hr : r = r' + 1 := by
    dsimp [r']
    omega
  have hcontentPow : completionDirectionContent D j * p ^ r ≤ H ^ r := by
    calc
      completionDirectionContent D j * p ^ r =
          (completionDirectionContent D j * p) * p ^ r' := by
        rw [hr, pow_succ]
        ring
      _ = H * p ^ r' := by rw [hnormEq]
      _ ≤ H * H ^ r' := by
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp_le _)
      _ = H ^ r := by
        rw [hr, pow_succ]
        ring
  have hcontentSlice :
      completionDirectionContent D j * completionSliceLCM D j ≤
        H ^ r * Δ ^ r := by
    calc
      completionDirectionContent D j * completionSliceLCM D j ≤
          completionDirectionContent D j * (p * Δ) ^ r :=
        Nat.mul_le_mul_left _ hsliceBound
      _ = (completionDirectionContent D j * p ^ r) * Δ ^ r := by
        rw [Nat.mul_pow]
        ring
      _ ≤ H ^ r * Δ ^ r :=
        Nat.mul_le_mul_right _ hcontentPow
  have hpartBound : completionPartMultiplier D j ≤
      completionPartMultiplierBound F.card (l1Diameter F)
        D.numberOfParts (l1Norm (D.direction j)) := by
    unfold completionPartMultiplier completionPartMultiplierBound
      completionLocalConstant
    calc
      completionWedgeFactor D j * completionDilationRatio D j *
          completionDirectionContent D j * completionSliceLCM D j ≤
          ((D.numberOfParts + 1) * H) * 4 ^ (2 * F.card) *
            (H ^ r * Δ ^ r) := by
        calc
          completionWedgeFactor D j * completionDilationRatio D j *
              completionDirectionContent D j * completionSliceLCM D j =
              (completionWedgeFactor D j * completionDilationRatio D j) *
                (completionDirectionContent D j * completionSliceLCM D j) := by ring
          _ ≤ (((D.numberOfParts + 1) * H) * 4 ^ (2 * F.card)) *
                (H ^ r * Δ ^ r) :=
            Nat.mul_le_mul (Nat.mul_le_mul hwedgeBound hratioBound) hcontentSlice
      _ = ((D.numberOfParts + 1) * 4 ^ (2 * F.card)) *
          H ^ (r + 1) * Δ ^ r := by
        rw [pow_succ]
        ring
      _ ≤ ((D.numberOfParts + 1) * 4 ^ (2 * F.card)) *
          max 1 (H ^ (r + 1)) * max 1 (Δ ^ r) := by
        gcongr <;> exact le_max_right _ _
      _ = ((D.numberOfParts + 1) * 4 ^ (2 * F.card)) *
          max 1 (l1Norm (D.direction j) ^
            (completionSliceExponent F.card + 1)) *
          max 1 (l1Diameter F ^ completionSliceExponent F.card) := by
        rfl
  exact ⟨hprimitive, hdirection, hratioSpec, hpartPos, hpartBound⟩

private theorem max_one_pow_mul (d m r : ℕ) (hm : 0 < m) (hr : 0 < r) :
    max 1 (d ^ r) ^ m = max 1 (d ^ (m * r)) := by
  by_cases hd : d = 0
  · subst d
    simp [Nat.ne_of_gt hm, Nat.ne_of_gt hr]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    rw [max_eq_right (Nat.one_le_pow _ _ hdpos),
      max_eq_right (Nat.one_le_pow _ _ hdpos)]
    rw [← pow_mul]
    congr 1
    exact Nat.mul_comm r m

/-- Construct the exact completion certificate for at least two parts. -/
theorem improve_weaklyPeriodic_exact
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (hcard : 1 < F.card)
    (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts) :
    Nonempty (CompletionCertificate D) := by
  classical
  have hconv (j : Fin D.numberOfParts) :=
    convolution_part_scalarPeriodic D hm j
  have harith (j : Fin D.numberOfParts) :=
    completion_part_arithmetic D hell hcard j (hconv j).1
  have hexists (j : Fin D.numberOfParts) :
      ∃ A' : Set Plane,
        SetScalarPeriodic
          (indicatorDilationModulus
              (ell * completionConvolutionMultiplier D j) F.card *
            completionDirectionContent D j * completionSliceLCM D j) A' ∧
        convolutionEquivalent F (D.part j) A' := by
    have hp := (D.periodic_part j).zsmul
      (completionConvolutionMultiplier D j : ℤ)
    have hpartPeriod : Function.Periodic (setIndicator (D.part j))
        (((ell * completionConvolutionMultiplier D j *
          completionDirectionContent D j : ℕ) : ℤ) •
            completionPrimitiveDirection D j) := by
      have hshift :
          (((ell * completionConvolutionMultiplier D j *
            completionDirectionContent D j : ℕ) : ℤ) •
              completionPrimitiveDirection D j) =
            (completionConvolutionMultiplier D j : ℤ) •
              ((ell : ℤ) • D.direction j) := by
        rw [(harith j).2.1]
        push_cast
        module
      rw [hshift]
      exact hp
    have hcontentPos : 0 < completionDirectionContent D j :=
      vectorContent_pos (D.direction_ne_zero j)
    obtain ⟨A', hperiod, hconvolution, -⟩ := improve_onePeriodic
      (Nat.mul_pos hell (hconv j).1) hcontentPos
      (harith j).1 hpartPeriod (hconv j).2.2
    exact ⟨A', hperiod, hconvolution⟩
  let improvedPart : Fin D.numberOfParts → Set Plane := fun j ↦
    Classical.choose (hexists j)
  have himprovedSpec (j : Fin D.numberOfParts) :=
    Classical.choose_spec (hexists j)
  have himprovedConvolution (j : Fin D.numberOfParts) :
      convolutionEquivalent F (D.part j) (improvedPart j) :=
    (himprovedSpec j).2
  have himprovedPeriodic (j : Fin D.numberOfParts) :
      SetScalarPeriodic
        (ell * completionPairLCM D * completionPartMultiplier D j)
        (improvedPart j) := by
    have hp := (himprovedSpec j).1
    convert hp using 1
    rw [(harith j).2.2.1]
    unfold completionConvolutionMultiplier completionPartMultiplier
    ring
  have hindicator : setIndicator A = ∑ i, setIndicator (D.part i) := by
    calc
      setIndicator A = setIndicator (⋃ i, D.part i) :=
        congrArg setIndicator D.union_parts.symm
      _ = ∑ i, setIndicator (D.part i) :=
        setIndicator_iUnion_eq_sum D.part D.pairwiseDisjoint
  have hsumOriginal : setIndicator E =
      ∑ i, tileConv F (setIndicator (D.part i)) := by
    funext x
    have ht := D.tiles x
    have ht' : tileConv F (setIndicator A) x = setIndicator E x := by
      norm_num at ht ⊢
      exact ht
    rw [hindicator] at ht'
    rw [← ht']
    simp only [Finset.sum_apply, tileConv]
    rw [Finset.sum_comm]
  have hsumImproved : setIndicator E =
      ∑ i, tileConv F (setIndicator (improvedPart i)) := by
    rw [hsumOriginal]
    apply Finset.sum_congr rfl
    intro i _
    exact himprovedConvolution i
  have himprovedDisjoint : Set.PairwiseDisjoint Set.univ improvedPart := by
    rw [Set.pairwiseDisjoint_iff]
    intro i _ j _ hnonempty
    by_contra hij
    obtain ⟨y, hyi, hyj⟩ := hnonempty
    obtain ⟨f₀, hf₀⟩ := hF
    let x := y + f₀
    let count : Fin D.numberOfParts → ℕ := fun a ↦
      (F.filter fun f ↦ x - f ∈ improvedPart a).card
    have hcount (a : Fin D.numberOfParts) :
        tileConv F (setIndicator (improvedPart a)) x = (count a : ℤ) := by
      exact tileConv_indicator_eq_card F (improvedPart a) x
    have hicount : 1 ≤ count i := by
      apply Finset.card_pos.mpr
      refine ⟨f₀, Finset.mem_filter.mpr ⟨hf₀, ?_⟩⟩
      simpa [x] using hyi
    have hjcount : 1 ≤ count j := by
      apply Finset.card_pos.mpr
      refine ⟨f₀, Finset.mem_filter.mpr ⟨hf₀, ?_⟩⟩
      simpa [x] using hyj
    have hpairs : count i + count j ≤ ∑ a, count a := by
      rw [← Finset.sum_pair hij]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro a _ _
        exact Nat.zero_le _
    have htotal : ((∑ a, count a : ℕ) : ℤ) = setIndicator E x := by
      calc
        ((∑ a, count a : ℕ) : ℤ) = ∑ a, (count a : ℤ) := by
          push_cast
          rfl
        _ = ∑ a, tileConv F (setIndicator (improvedPart a)) x := by
          apply Finset.sum_congr rfl
          intro a _
          exact (hcount a).symm
        _ = setIndicator E x := by
          rw [← Finset.sum_apply]
          exact (congrFun hsumImproved x).symm
    have hEupper : setIndicator E x ≤ 1 := by
      by_cases hx : x ∈ E <;> simp [setIndicator, hx]
    have : (2 : ℕ) ≤ ∑ a, count a := by omega
    omega
  let completedSet : Set Plane := ⋃ j, improvedPart j
  have hcompletedIndicator : setIndicator completedSet =
      ∑ j, setIndicator (improvedPart j) := by
    exact setIndicator_iUnion_eq_sum improvedPart himprovedDisjoint
  have hcompletedTiles : Tiles F completedSet E := by
    intro x
    rw [hcompletedIndicator]
    simp only [tileConv, Finset.sum_apply]
    rw [Finset.sum_comm]
    have hs : (∑ y, ∑ f ∈ F, setIndicator (improvedPart y) (x - f)) =
        setIndicator E x := by
      simpa only [Finset.sum_apply, tileConv] using
        (congrFun hsumImproved x).symm
    norm_num at hs ⊢
    exact hs
  have hpairPos : 0 < completionPairLCM D :=
    pairWedgeLCM_pos D.direction_ne_zero D.pairwise_incommensurable
  have hpartPos (j : Fin D.numberOfParts) :
      0 < completionPartMultiplier D j := (harith j).2.2.2.1
  have hmultPos : 0 < completionMultiplier D := by
    exact Nat.mul_pos hpairPos (Finset.prod_pos fun j _ ↦ hpartPos j)
  have hcompletedPeriodic : SetScalarPeriodic
      (ell * completionMultiplier D) completedSet := by
    intro x z
    constructor
    · intro hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      have hdvd : completionPartMultiplier D j ∣
          ∏ i : Fin D.numberOfParts, completionPartMultiplier D i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      obtain ⟨t, ht⟩ := hdvd
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      have hp := himprovedPeriodic j x ((t : ℤ) • z)
      have hshift :
          x + (((ell * completionMultiplier D : ℕ) : ℤ) • z) =
            x + (((ell * completionPairLCM D *
              completionPartMultiplier D j : ℕ) : ℤ) •
                ((t : ℤ) • z)) := by
        unfold completionMultiplier
        rw [ht]
        push_cast
        module
      apply hp.mp
      rw [← hshift]
      exact hxj
    · intro hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      have hdvd : completionPartMultiplier D j ∣
          ∏ i : Fin D.numberOfParts, completionPartMultiplier D i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      obtain ⟨t, ht⟩ := hdvd
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      have hp := himprovedPeriodic j x ((t : ℤ) • z)
      have hshift :
          x + (((ell * completionMultiplier D : ℕ) : ℤ) • z) =
            x + (((ell * completionPairLCM D *
              completionPartMultiplier D j : ℕ) : ℤ) •
                ((t : ℤ) • z)) := by
        unfold completionMultiplier
        rw [ht]
        push_cast
        module
      have hxsmall := hp.mpr hxj
      rw [← hshift] at hxsmall
      exact hxsmall
  let H := ∏ i : Fin D.numberOfParts, l1Norm (D.direction i)
  let r := completionSliceExponent F.card
  let K := completionLocalConstant F.card D.numberOfParts
  let Δ := l1Diameter F
  have hHpos : 0 < H := by
    apply Finset.prod_pos
    intro i _
    rw [Nat.pos_iff_ne_zero]
    exact (l1Norm_eq_zero.not.mpr (D.direction_ne_zero i))
  have hNbound : completionPairLCM D ≤ H ^ (D.numberOfParts - 1) := by
    simpa only [completionPairLCM, H, Finset.prod_pow] using
      (pairWedgeLCM_bound D.direction_ne_zero D.pairwise_incommensurable)
  have hLbound (i : Fin D.numberOfParts) : completionPartMultiplier D i ≤
      K * l1Norm (D.direction i) ^ (r + 1) * max 1 (Δ ^ r) := by
    have hiNorm : 1 ≤ l1Norm (D.direction i) := by
      exact Nat.one_le_iff_ne_zero.mpr
        ((l1Norm_eq_zero).not.mpr (D.direction_ne_zero i))
    simpa [completionPartMultiplierBound, K, r, Δ,
      max_eq_right (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero
        (Nat.one_le_iff_ne_zero.mp hiNorm)))] using (harith i).2.2.2.2
  have hprodL : (∏ i : Fin D.numberOfParts, completionPartMultiplier D i) ≤
      K ^ D.numberOfParts * H ^ (r + 1) *
        max 1 (Δ ^ (D.numberOfParts * r)) := by
    calc
      (∏ i : Fin D.numberOfParts, completionPartMultiplier D i) ≤
          ∏ i : Fin D.numberOfParts,
            (K * l1Norm (D.direction i) ^ (r + 1) * max 1 (Δ ^ r)) := by
        exact Finset.prod_le_prod' fun i _ ↦ hLbound i
      _ = K ^ D.numberOfParts * H ^ (r + 1) *
          max 1 (Δ ^ r) ^ D.numberOfParts := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, Finset.prod_pow, H]
      _ = K ^ D.numberOfParts * H ^ (r + 1) *
          max 1 (Δ ^ (D.numberOfParts * r)) := by
        rw [max_one_pow_mul Δ D.numberOfParts r D.number_pos
          (completionSliceExponent_pos hcard)]
  have hmultBound : completionMultiplier D ≤
      weakCompletionPeriodBound F.card (l1Diameter F) D.numberOfParts H := by
    unfold completionMultiplier weakCompletionPeriodBound
    calc
      completionPairLCM D *
          (∏ i : Fin D.numberOfParts, completionPartMultiplier D i) ≤
          H ^ (D.numberOfParts - 1) *
            (K ^ D.numberOfParts * H ^ (r + 1) *
              max 1 (Δ ^ (D.numberOfParts * r))) :=
        Nat.mul_le_mul hNbound hprodL
      _ = K ^ D.numberOfParts * H ^ (D.numberOfParts + r) *
          max 1 (Δ ^ (D.numberOfParts * r)) := by
        have hexponent : (D.numberOfParts - 1) + (r + 1) =
            D.numberOfParts + r := by omega
        calc
          H ^ (D.numberOfParts - 1) *
              (K ^ D.numberOfParts * H ^ (r + 1) *
                max 1 (Δ ^ (D.numberOfParts * r))) =
              K ^ D.numberOfParts *
                (H ^ (D.numberOfParts - 1) * H ^ (r + 1)) *
                  max 1 (Δ ^ (D.numberOfParts * r)) := by ring
          _ = K ^ D.numberOfParts * H ^ (D.numberOfParts + r) *
                max 1 (Δ ^ (D.numberOfParts * r)) := by
            rw [← pow_add, hexponent]
      _ ≤ K ^ D.numberOfParts * max 1 (H ^ (D.numberOfParts + r)) *
          max 1 (Δ ^ (D.numberOfParts * r)) := by
        gcongr
        exact le_max_right _ _
      _ = completionLocalConstant F.card D.numberOfParts ^ D.numberOfParts *
          max 1 (H ^ (D.numberOfParts + completionSliceExponent F.card)) *
          max 1 (l1Diameter F ^
            (D.numberOfParts * completionSliceExponent F.card)) := by
        rfl
  let completed : PeriodicTilingCertificate F E ell := {
    tilingSet := completedSet
    scalarMultiplier := completionMultiplier D
    multiplier_pos := hmultPos
    periodic := hcompletedPeriodic
    tiles := hcompletedTiles
  }
  exact ⟨{
    completed := completed
    convolutionMultiplier_pos := fun j ↦ (hconv j).1
    convolutionMultiplier_bound := fun j ↦ (hconv j).2.1
    convolution_periodic := fun j ↦ (hconv j).2.2
    primitive_direction := fun j ↦ (harith j).1
    direction_decomposition := fun j ↦ (harith j).2.1
    dilation_ratio_spec := fun j ↦ (harith j).2.2.1
    partMultiplier_pos := hpartPos
    partMultiplier_bound := fun j ↦ (harith j).2.2.2.2
    improvedPart := improvedPart
    improved_convolution := himprovedConvolution
    improved_periodic := himprovedPeriodic
    improved_pairwiseDisjoint := himprovedDisjoint
    improved_union := rfl
    completed_multiplier_exact := rfl
    completedMultiplier_bound := hmultBound
  }⟩

/-- Construct a completion certificate with the structural multiplier bound. -/
theorem improve_weaklyPeriodic_structural
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts)
    (hmcard : D.numberOfParts ≤ F.card - 1) :
    ∃ C : CompletionCertificate D,
      C.completed.scalarMultiplier ≤
        structuralCompletionPeriodBound F.card (l1Diameter F)
          D.numberOfParts
          (∏ i : Fin D.numberOfParts, l1Norm (D.direction i)) := by
  obtain ⟨C⟩ := improve_weaklyPeriodic_exact hF
    (one_lt_tileCard_of_structural_parts hm hmcard) D hell hm
  exact ⟨C, C.completedMultiplier_structural_bound hmcard⟩

/-- A singleton tile admits a period-one completion. -/
theorem singleton_tile_periodic_completion
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (hcard : F.card = 1) :
    ∃ C : PeriodicTilingCertificate F E ell,
      C.scalarMultiplier = 1 := by
  classical
  obtain ⟨f, hF⟩ := Finset.card_eq_one.mp hcard
  let A' : Set Plane := {x | x + f ∈ E}
  have hperiod : SetScalarPeriodic (ell * 1) A' := by
    intro x z
    change x + ((ell * 1 : ℕ) : ℤ) • z + f ∈ E ↔ x + f ∈ E
    have hp := D.target_periodic (x + f) z
    have hshift : x + ((ell * 1 : ℕ) : ℤ) • z + f =
        x + f + (ell : ℤ) • z := by
      simp only [Nat.mul_one]
      abel
    rw [hshift]
    exact hp
  have htiles : Tiles F A' E := by
    rw [hF]
    intro x
    simp only [tileConv, Finset.sum_singleton]
    change setIndicator E (x - f + f) = (1 : ℤ) * setIndicator E x
    rw [sub_add_cancel, one_mul]
  refine ⟨{
    tilingSet := A'
    scalarMultiplier := 1
    multiplier_pos := Nat.zero_lt_one
    periodic := hperiod
    tiles := htiles
  }, rfl⟩

/-- Complete a weakly periodic tiling, including the singleton-tile case. -/
theorem improve_weaklyPeriodic
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts) :
    Nonempty (PaperCompletionResult D) := by
  by_cases hcard : F.card = 1
  · obtain ⟨C, hC⟩ := singleton_tile_periodic_completion D hcard
    exact ⟨{
      completed := C
      completedMultiplier_bound := by
        rw [hC]
        exact one_le_weakCompletionPeriodBound
          F.card (l1Diameter F) D.numberOfParts
            (∏ i : Fin D.numberOfParts, l1Norm (D.direction i))
      component_convolution := fun j ↦ convolution_part_scalarPeriodic D hm j
    }⟩
  · have hcardPos : 0 < F.card := Finset.card_pos.mpr hF
    have hcard' : 1 < F.card := by omega
    obtain ⟨C⟩ := improve_weaklyPeriodic_exact hF hcard' D hell hm
    exact ⟨C.toPaperCompletionResult⟩

private theorem onePartCompletionMultiplierBound_le_structural
    {tileCard diameter directionNorm : ℕ} (hcard : 1 < tileCard) :
    onePartCompletionMultiplierBound tileCard diameter directionNorm ≤
      structuralCompletionPeriodBound tileCard diameter 1 directionNorm := by
  have hbase : 4 ^ (2 * tileCard) ≤
      (tileCard * 4 ^ (2 * tileCard)) ^ tileCard := by
    calc
      4 ^ (2 * tileCard) ≤ tileCard * 4 ^ (2 * tileCard) :=
        Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ (tileCard * 4 ^ (2 * tileCard)) ^ tileCard :=
        Nat.le_pow (by omega)
  unfold onePartCompletionMultiplierBound structuralCompletionPeriodBound
  simpa only [one_mul, Nat.one_mul, Nat.add_comm 1] using
    Nat.mul_le_mul_right (max 1 (diameter ^ completionSliceExponent tileCard))
      (Nat.mul_le_mul_right
        (max 1 (directionNorm ^ (completionSliceExponent tileCard + 1))) hbase)

private theorem weak_mul_structural_le_periodic
    {tileCard diameter numberOfParts directionProduct : ℕ}
    (hcard : 1 < tileCard) (hmpos : 0 < numberOfParts)
    (hmcard : numberOfParts ≤ tileCard - 1)
    (hHpos : 0 < directionProduct)
    (hHbound : directionProduct ≤ diameter ^ (tileCard - 1)) :
    weakPeriodMultiplierBound tileCard diameter *
        structuralCompletionPeriodBound tileCard diameter numberOfParts
          directionProduct ≤
      periodicTilingPeriodBound tileCard diameter := by
  let r := completionSliceExponent tileCard
  let weakExponent := tileCard * (tileCard - 1)
  let completionExponent :=
    (tileCard - 1) * (numberOfParts + r) + numberOfParts * r
  let totalExponent := weakExponent + completionExponent
  have hrPos : 0 < r := completionSliceExponent_pos hcard
  have hdiamPos : 0 < diameter := by
    by_contra hd
    have hd0 : diameter = 0 := Nat.eq_zero_of_not_pos hd
    rw [hd0] at hHbound
    simp [show 0 < tileCard - 1 by omega] at hHbound
    omega
  have htwoR : 2 * r = tileCard * (tileCard - 1) := by
    unfold r completionSliceExponent
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self tileCard)
  have hcompletionExponent : completionExponent ≤
      (tileCard + 1) * (tileCard - 1) ^ 2 := by
    dsimp [completionExponent]
    nlinarith
  have htotalExponent : totalExponent ≤ periodicTilingExponent tileCard := by
    unfold totalExponent weakExponent periodicTilingExponent
    calc
      tileCard * (tileCard - 1) + completionExponent ≤
          tileCard * (tileCard - 1) +
            (tileCard + 1) * (tileCard - 1) ^ 2 :=
        Nat.add_le_add_left hcompletionExponent _
      _ = (tileCard - 1) * (tileCard ^ 2 + tileCard - 1) := by
        let n := tileCard - 1
        have hc : tileCard = n + 1 := by
          dsimp [n]
          omega
        rw [hc]
        simp
        ring
  have hHpow : directionProduct ^ (numberOfParts + r) ≤
      diameter ^ ((tileCard - 1) * (numberOfParts + r)) := by
    calc
      directionProduct ^ (numberOfParts + r) ≤
          (diameter ^ (tileCard - 1)) ^ (numberOfParts + r) :=
        Nat.pow_le_pow_left hHbound _
      _ = diameter ^ ((tileCard - 1) * (numberOfParts + r)) := by
        rw [pow_mul]
  have hweakMax : max 1 (diameter ^ weakExponent) =
      diameter ^ weakExponent :=
    max_eq_right (Nat.one_le_pow _ _ hdiamPos)
  have hHMax : max 1 (directionProduct ^ (numberOfParts + r)) =
      directionProduct ^ (numberOfParts + r) :=
    max_eq_right (Nat.one_le_pow _ _ hHpos)
  have hdiamCompletionMax : max 1 (diameter ^ (numberOfParts * r)) =
      diameter ^ (numberOfParts * r) :=
    max_eq_right (Nat.one_le_pow _ _ hdiamPos)
  have hperiodMax : max 1 (diameter ^ periodicTilingExponent tileCard) =
      diameter ^ periodicTilingExponent tileCard :=
    max_eq_right (Nat.one_le_pow _ _ hdiamPos)
  have hconstantPos : 0 < periodicTilingConstant tileCard := by
    have hfactor : 0 < (tileCard * 4 ^ (2 * tileCard)) ^ tileCard := by
      cases tileCard with
      | zero => simp
      | succ n => positivity
    unfold periodicTilingConstant weakPeriodMultiplierConstant
    exact Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos (weakRigidityPeriod_pos tileCard) (by positivity))
        (by positivity))
      hfactor
  unfold periodicTilingPeriodBound
  have hperiodProduct : 1 ≤ periodicTilingConstant tileCard *
      max 1 (diameter ^ periodicTilingExponent tileCard) := by
    have hc : 1 ≤ periodicTilingConstant tileCard :=
      Nat.one_le_iff_ne_zero.mpr hconstantPos.ne'
    simpa using Nat.mul_le_mul hc
      (le_max_left 1 (diameter ^ periodicTilingExponent tileCard))
  rw [max_eq_right hperiodProduct, hperiodMax]
  unfold weakPeriodMultiplierBound structuralCompletionPeriodBound
    periodicTilingConstant
  rw [hweakMax, hHMax, hdiamCompletionMax]
  calc
    weakPeriodMultiplierConstant tileCard * diameter ^ weakExponent *
        ((tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
          directionProduct ^ (numberOfParts + r) *
          diameter ^ (numberOfParts * r)) ≤
      weakPeriodMultiplierConstant tileCard * diameter ^ weakExponent *
        ((tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
          diameter ^ ((tileCard - 1) * (numberOfParts + r)) *
          diameter ^ (numberOfParts * r)) := by
      gcongr
    _ = weakPeriodMultiplierConstant tileCard *
        (tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
          diameter ^ totalExponent := by
      dsimp [totalExponent, completionExponent]
      calc
        weakPeriodMultiplierConstant tileCard * diameter ^ weakExponent *
            ((tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
              diameter ^ ((tileCard - 1) * (numberOfParts + r)) *
              diameter ^ (numberOfParts * r)) =
            weakPeriodMultiplierConstant tileCard *
              (tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
                (diameter ^ weakExponent *
                  (diameter ^ ((tileCard - 1) * (numberOfParts + r)) *
                    diameter ^ (numberOfParts * r))) := by ring
        _ = weakPeriodMultiplierConstant tileCard *
              (tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
                diameter ^
                  (weakExponent + ((tileCard - 1) * (numberOfParts + r) +
                    numberOfParts * r)) := by
          rw [pow_add, pow_add]
    _ ≤ weakPeriodMultiplierConstant tileCard *
        (tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
          diameter ^ periodicTilingExponent tileCard := by
      gcongr

private theorem l1Diameter_image_sub (F : Finset Plane) (t : Plane) :
    l1Diameter (F.image fun f ↦ f - t) = l1Diameter F := by
  apply Nat.le_antisymm
  · unfold l1Diameter
    apply Finset.sup_le
    intro xy hxy
    have hmem := Finset.mem_product.mp hxy
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hmem.1
    obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hmem.2
    rw [← hxeq, ← hyeq]
    simpa only [show x - t - (y - t) = x - y by abel] using
      (Finset.le_sup (f := fun uv : Plane × Plane ↦ l1Norm (uv.1 - uv.2))
        (show (x, y) ∈ F ×ˢ F by simp [hx, hy]))
  · unfold l1Diameter
    apply Finset.sup_le
    intro xy hxy
    have hmem := Finset.mem_product.mp hxy
    have hx : xy.1 - t ∈ F.image fun f ↦ f - t :=
      Finset.mem_image.mpr ⟨xy.1, hmem.1, rfl⟩
    have hy : xy.2 - t ∈ F.image fun f ↦ f - t :=
      Finset.mem_image.mpr ⟨xy.2, hmem.2, rfl⟩
    simpa only [show xy.1 - t - (xy.2 - t) = xy.1 - xy.2 by abel] using
      (Finset.le_sup (f := fun uv : Plane × Plane ↦ l1Norm (uv.1 - uv.2))
        (show (xy.1 - t, xy.2 - t) ∈
          (F.image fun f ↦ f - t) ×ˢ (F.image fun f ↦ f - t) by
            simp [hx, hy]))

private theorem singleton_periodic_certificate
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hcard : F.card = 1) (hE : SetScalarPeriodic ell E) :
    ∃ C : PeriodicTilingCertificate F E ell, C.scalarMultiplier = 1 := by
  classical
  obtain ⟨f, hF⟩ := Finset.card_eq_one.mp hcard
  let A' : Set Plane := {x | x + f ∈ E}
  have hperiod : SetScalarPeriodic (ell * 1) A' := by
    intro x z
    change x + ((ell * 1 : ℕ) : ℤ) • z + f ∈ E ↔ x + f ∈ E
    have hp := hE (x + f) z
    have hshift : x + ((ell * 1 : ℕ) : ℤ) • z + f =
        x + f + (ell : ℤ) • z := by
      simp only [Nat.mul_one]
      abel
    rw [hshift]
    exact hp
  have htiles : Tiles F A' E := by
    rw [hF]
    intro x
    simp only [tileConv, Finset.sum_singleton]
    change setIndicator E (x - f + f) = (1 : ℤ) * setIndicator E x
    rw [sub_add_cancel, one_mul]
  exact ⟨{
    tilingSet := A'
    scalarMultiplier := 1
    multiplier_pos := Nat.zero_lt_one
    periodic := hperiod
    tiles := htiles
  }, rfl⟩

private def PeriodicTilingCertificate.recenter
    {F : Finset Plane} {E : Set Plane} {ell : ℕ} (t : Plane)
    (C : PeriodicTilingCertificate (F.image fun f ↦ f - t) E ell) :
    PeriodicTilingCertificate F E ell where
  tilingSet := translateSet (-t) C.tilingSet
  scalarMultiplier := C.scalarMultiplier
  multiplier_pos := C.multiplier_pos
  periodic := by
    intro x z
    change x + ((ell * C.scalarMultiplier : ℕ) : ℤ) • z - (-t) ∈
        C.tilingSet ↔ x - (-t) ∈ C.tilingSet
    have hp := C.periodic (x - (-t)) z
    have hshift : x + ((ell * C.scalarMultiplier : ℕ) : ℤ) • z - (-t) =
        x - (-t) + ((ell * C.scalarMultiplier : ℕ) : ℤ) • z := by abel
    rw [hshift]
    exact hp
  tiles := by
    apply (tiles_translate_tile F (translateSet (-t) C.tilingSet) E 1 t).mpr
    have himage :
        @Finset.image Plane Plane (Classical.decEq Plane) (fun f ↦ f - t) F =
          F.image fun f ↦ f - t := by
      ext x
      simp only [Finset.mem_image]
    rw [himage]
    have htranslate : translateSet t (translateSet (-t) C.tilingSet) =
        C.tilingSet := by
      ext x
      change x - t - (-t) ∈ C.tilingSet ↔ x ∈ C.tilingSet
      rw [show x - t - (-t) = x by abel]
    simpa only [htranslate, Tiles] using C.tiles

/-- The final period exponent is bounded by a simple quartic expression. -/
theorem periodicTilingExponent_le_quartic (tileCard : ℕ) :
    periodicTilingExponent tileCard ≤ 3 * (tileCard + 1) ^ 4 := by
  unfold periodicTilingExponent
  cases tileCard with
  | zero => norm_num
  | succ n =>
      simp only [Nat.succ_sub_one]
      have hinner : (n + 1) ^ 2 + (n + 1) - 1 = (n + 1) ^ 2 + n := by
        omega
      rw [hinner]
      nlinarith [sq_nonneg (n : ℤ), sq_nonneg ((n : ℤ) ^ 2)]

/-- Quantitative periodic completion with an `ℓ¹`-diameter bound. -/
theorem quantitative_periodic_tiling_l1
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (hexists : ∃ A, Tiles F A E) :
    ∃ C : PeriodicTilingCertificate F E ell,
      C.scalarMultiplier ≤ periodicTilingPeriodBound F.card (l1Diameter F) := by
  classical
  obtain ⟨A, htile⟩ := hexists
  by_cases hEempty : E = ∅
  · subst E
    let C : PeriodicTilingCertificate F (∅ : Set Plane) ell := {
      tilingSet := ∅
      scalarMultiplier := 1
      multiplier_pos := Nat.zero_lt_one
      periodic := by simp [SetScalarPeriodic]
      tiles := by simp [Tiles, TilesAtLevel, tileConv, setIndicator]
    }
    exact ⟨C, le_max_left _ _⟩
  have hF : F.Nonempty := by
    by_contra hn
    have hFempty := Finset.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hEempty
    have ht := htile x
    rw [hFempty] at ht
    simp [tileConv, setIndicator, hx] at ht
  by_cases hcardOne : F.card = 1
  · obtain ⟨C, hC⟩ := singleton_periodic_certificate hcardOne hE
    refine ⟨C, ?_⟩
    rw [hC]
    exact le_max_left _ _
  have hcard : 1 < F.card := by
    have := Finset.card_pos.mpr hF
    omega
  obtain ⟨t, htF⟩ := hF
  let F₀ : Finset Plane := F.image fun f ↦ f - t
  let A₀ : Set Plane := translateSet t A
  have hzero : 0 ∈ F₀ := by
    exact Finset.mem_image.mpr ⟨t, htF, sub_self t⟩
  have hcardEq : F₀.card = F.card := by
    exact Finset.card_image_iff.mpr
      (Set.injOn_of_injective (sub_left_injective :
        Function.Injective fun f : Plane ↦ f - t))
  have hdiamEq : l1Diameter F₀ = l1Diameter F :=
    l1Diameter_image_sub F t
  have htile₀ : Tiles F₀ A₀ E := by
    have ht₀ := (tiles_translate_tile F A E 1 t).mp htile
    have himage :
        @Finset.image Plane Plane (Classical.decEq Plane) (fun f ↦ f - t) F = F₀ := by
      ext x
      simp only [F₀, Finset.mem_image]
    rw [himage] at ht₀
    exact ht₀
  obtain ⟨W, hW⟩ := exists_quantitativeWeakPeriodData
    hell hzero (by rw [hcardEq]; exact hcard)
  have hvalid := hW E A₀ hE htile₀
  obtain ⟨D, hnum, hdirection⟩ :=
    exists_directionalTilingDecomposition_of_quantitativeData
      hell hE htile₀ W hvalid
  have hWmultPos : 0 < W.multiplier := W.arithmetic.multiplier_pos
  have hbasePos : 0 < ell * W.multiplier := Nat.mul_pos hell hWmultPos
  let H := ∏ i : Fin D.numberOfParts, l1Norm (D.direction i)
  have hprodEq : H =
      ∏ j : Fin W.numberOfDirections, l1Norm (W.direction j) := by
    symm
    exact Fintype.prod_equiv (Fin.castOrderIso hnum.symm).toEquiv
      (fun j ↦ l1Norm (W.direction j))
      (fun i ↦ l1Norm (D.direction i))
      (fun j ↦ congrArg l1Norm (hdirection j).symm)
  have hHbound : H ≤ l1Diameter F₀ ^ (F₀.card - 1) := by
    rw [hprodEq]
    exact W.product_direction_l1_bound
  have hHpos : 0 < H := by
    apply Finset.prod_pos
    intro i _
    exact Nat.pos_iff_ne_zero.mpr
      ((l1Norm_eq_zero).not.mpr (D.direction_ne_zero i))
  have hmcard : D.numberOfParts ≤ F₀.card - 1 := by
    rw [hnum]
    exact W.number_le
  obtain ⟨Cbase, hCbaseBound⟩ :
      ∃ Cbase : PeriodicTilingCertificate F₀ E (ell * W.multiplier),
        Cbase.scalarMultiplier ≤
          structuralCompletionPeriodBound F₀.card (l1Diameter F₀)
            D.numberOfParts H := by
    by_cases hone : D.numberOfParts = 1
    · obtain ⟨Cbase, -, hbound⟩ := improve_onePart D hbasePos hone
      let j : Fin D.numberOfParts := ⟨0, D.number_pos⟩
      have hfin (i : Fin D.numberOfParts) : i = j := by
        apply Fin.ext
        have hi := i.isLt
        dsimp [j]
        omega
      have hprodOne : H = l1Norm (D.direction j) := by
        dsimp [H]
        rw [Finset.prod_eq_single j]
        · intro i _ hij
          exact (hij (hfin i)).elim
        · simp
      refine ⟨Cbase, hbound.trans ?_⟩
      change onePartCompletionMultiplierBound F₀.card (l1Diameter F₀)
          (l1Norm (D.direction j)) ≤
        structuralCompletionPeriodBound F₀.card (l1Diameter F₀)
          D.numberOfParts H
      calc
        onePartCompletionMultiplierBound F₀.card (l1Diameter F₀)
            (l1Norm (D.direction j)) ≤
            structuralCompletionPeriodBound F₀.card (l1Diameter F₀) 1
              (l1Norm (D.direction j)) :=
          onePartCompletionMultiplierBound_le_structural
            (by rw [hcardEq]; exact hcard)
        _ = structuralCompletionPeriodBound F₀.card (l1Diameter F₀)
              D.numberOfParts H := by rw [hone, hprodOne]
    · have hm : 2 ≤ D.numberOfParts :=
        (Nat.two_le_iff D.numberOfParts).mpr ⟨Nat.ne_of_gt D.number_pos, hone⟩
      obtain ⟨Cbase, hbound⟩ := improve_weaklyPeriodic_structural
        ⟨0, hzero⟩ D hbasePos hm hmcard
      exact ⟨Cbase.completed, hbound⟩
  let C₀ := PeriodicTilingCertificate.rebase hWmultPos Cbase
  let C := PeriodicTilingCertificate.recenter t C₀
  refine ⟨C, ?_⟩
  change W.multiplier * Cbase.scalarMultiplier ≤ _
  rw [← hcardEq, ← hdiamEq]
  calc
    W.multiplier * Cbase.scalarMultiplier ≤
        weakPeriodMultiplierBound F₀.card (l1Diameter F₀) *
          structuralCompletionPeriodBound F₀.card (l1Diameter F₀)
            D.numberOfParts H :=
      Nat.mul_le_mul W.multiplier_bound hCbaseBound
    _ ≤ periodicTilingPeriodBound F₀.card (l1Diameter F₀) :=
      weak_mul_structural_le_periodic
        (by rw [hcardEq]; exact hcard) D.number_pos hmcard hHpos hHbound

/-- Euclidean-diameter constant obtained from the `ℓ¹` completion bound. -/
noncomputable def periodicTilingEuclideanConstant (tileCard : ℕ) : ℝ :=
  periodicTilingConstant tileCard *
    Real.sqrt 2 ^ periodicTilingExponent tileCard

/-- Quantitative periodic completion in the paper-facing Euclidean form. -/
theorem quantitative_periodic_tiling_euclidean
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (hexists : ∃ A, Tiles F A E) :
    ∃ (A' : Set Plane) (M : ℕ),
      0 < M ∧ Tiles F A' E ∧ SetScalarPeriodic (ell * M) A' ∧
      (M : ℝ) ≤ periodicTilingEuclideanConstant F.card *
        max 1 (euclideanDiameter F ^ periodicTilingExponent F.card) := by
  obtain ⟨C, hC⟩ := quantitative_periodic_tiling_l1 hell hE hexists
  refine ⟨C.tilingSet, C.scalarMultiplier, C.multiplier_pos, C.tiles,
    C.periodic, ?_⟩
  let p := periodicTilingExponent F.card
  have hconstantPos : 0 < periodicTilingConstant F.card := by
    have hfactor : 0 < (F.card * 4 ^ (2 * F.card)) ^ F.card := by
      cases h : F.card with
      | zero => simp
      | succ n => positivity
    unfold periodicTilingConstant weakPeriodMultiplierConstant
    exact Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos (weakRigidityPeriod_pos F.card) (by positivity))
        (by positivity))
      hfactor
  have hboundNat : C.scalarMultiplier ≤
      periodicTilingConstant F.card * max 1 (l1Diameter F ^ p) := by
    apply hC.trans_eq
    unfold periodicTilingPeriodBound
    rw [max_eq_right]
    have hc : 1 ≤ periodicTilingConstant F.card :=
      Nat.one_le_iff_ne_zero.mpr hconstantPos.ne'
    simpa using Nat.mul_le_mul hc (le_max_left 1 (l1Diameter F ^ p))
  have hboundReal : (C.scalarMultiplier : ℝ) ≤
      periodicTilingConstant F.card *
        max 1 ((l1Diameter F : ℝ) ^ p) := by
    exact_mod_cast hboundNat
  have hdiam := l1Diameter_le_sqrt_dim_mul_euclideanDiameter F
  norm_num at hdiam
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by
    exact Real.one_le_sqrt.mpr (by norm_num)
  have hsqrtNonneg : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hdiamPow : (l1Diameter F : ℝ) ^ p ≤
      (Real.sqrt 2 * euclideanDiameter F) ^ p :=
    pow_le_pow_left₀ (by positivity) hdiam p
  have hsqrtPowOne : (1 : ℝ) ≤ Real.sqrt 2 ^ p :=
    one_le_pow₀ hsqrtOne
  have hsqrtPowNonneg : (0 : ℝ) ≤ Real.sqrt 2 ^ p :=
    pow_nonneg hsqrtNonneg _
  have hmax : max 1 ((l1Diameter F : ℝ) ^ p) ≤
      Real.sqrt 2 ^ p * max 1 (euclideanDiameter F ^ p) := by
    calc
      max 1 ((l1Diameter F : ℝ) ^ p) ≤
          max 1 ((Real.sqrt 2 * euclideanDiameter F) ^ p) :=
        max_le_max le_rfl hdiamPow
      _ = max 1 (Real.sqrt 2 ^ p * euclideanDiameter F ^ p) := by
        rw [mul_pow]
      _ ≤ Real.sqrt 2 ^ p * max 1 (euclideanDiameter F ^ p) := by
        apply max_le
        · exact hsqrtPowOne.trans (by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ)
                (euclideanDiameter F ^ p)) hsqrtPowNonneg))
        · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hsqrtPowNonneg
  calc
    (C.scalarMultiplier : ℝ) ≤
        periodicTilingConstant F.card *
          max 1 ((l1Diameter F : ℝ) ^ p) := hboundReal
    _ ≤ periodicTilingConstant F.card *
        (Real.sqrt 2 ^ p * max 1 (euclideanDiameter F ^ p)) := by
      gcongr
    _ = periodicTilingEuclideanConstant F.card *
        max 1 (euclideanDiameter F ^ periodicTilingExponent F.card) := by
      unfold periodicTilingEuclideanConstant
      dsimp [p]
      ring

end TranslationalTilings
