import TranslationalTilings.Slicing
import TranslationalTilings.WeakPeriodicity

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 8d1f5c269f26b6ded57492026a5c6dd65f659fdd42669d1797e69607a4f74afa  blueprint/07-periodic-completion.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/07-periodic-completion.md:147; TranslationalTilings.DirectionalTilingDecomposition -/
namespace TranslationalTilings
structure DirectionalTilingDecomposition
    (F : Finset Plane) (A E : Set Plane) (ell : ℕ) where
  numberOfParts : ℕ
  number_pos : 0 < numberOfParts
  part : Fin numberOfParts → Set Plane
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
end TranslationalTilings

/- blueprint/07-periodic-completion.md:174; TranslationalTilings.exists_directionalTilingDecomposition_of_quantitativeData -/
namespace TranslationalTilings
axiom exists_directionalTilingDecomposition_of_quantitativeData
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (htile : Tiles F A E) (W : QuantitativeWeakPeriodData F ell)
    (hW : W.ValidFor A) :
  ∃ D : DirectionalTilingDecomposition F A E (ell * W.multiplier),
    ∃ hnum : D.numberOfParts = W.numberOfDirections,
      ∀ j : Fin W.numberOfDirections,
        D.direction (Fin.cast hnum.symm j) = W.direction j
end TranslationalTilings

/- blueprint/07-periodic-completion.md:203; TranslationalTilings.completionSliceExponent -/
namespace TranslationalTilings
def completionSliceExponent (tileCard : ℕ) : ℕ :=
  tileCard * (tileCard - 1) / 2
end TranslationalTilings

/- blueprint/07-periodic-completion.md:206; TranslationalTilings.completionSliceExponent_pos -/
namespace TranslationalTilings
axiom completionSliceExponent_pos {tileCard : ℕ}
    (hcard : 1 < tileCard) :
  0 < completionSliceExponent tileCard
end TranslationalTilings

/- blueprint/07-periodic-completion.md:210; TranslationalTilings.completionConvolutionBound -/
namespace TranslationalTilings
def completionConvolutionBound
    (numberOfParts directionProduct directionNorm : ℕ) : ℕ :=
  max 1 (directionProduct ^ (numberOfParts - 1) *
    (numberOfParts + 1) * directionNorm)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:215; TranslationalTilings.completionLocalConstant -/
namespace TranslationalTilings
def completionLocalConstant (tileCard numberOfParts : ℕ) : ℕ :=
  (numberOfParts + 1) * 4 ^ (2 * tileCard)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:218; TranslationalTilings.completionPartMultiplierBound -/
namespace TranslationalTilings
def completionPartMultiplierBound
    (tileCard diameter numberOfParts directionNorm : ℕ) : ℕ :=
  completionLocalConstant tileCard numberOfParts *
    max 1 (directionNorm ^ (completionSliceExponent tileCard + 1)) *
    max 1 (diameter ^ completionSliceExponent tileCard)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:224; TranslationalTilings.weakCompletionPeriodBound -/
namespace TranslationalTilings
def weakCompletionPeriodBound
    (tileCard diameter numberOfParts directionProduct : ℕ) : ℕ :=
  completionLocalConstant tileCard numberOfParts ^ numberOfParts *
    max 1 (directionProduct ^
      (numberOfParts + completionSliceExponent tileCard)) *
    max 1 (diameter ^
      (numberOfParts * completionSliceExponent tileCard))
end TranslationalTilings

/- blueprint/07-periodic-completion.md:234; TranslationalTilings.structuralCompletionPeriodBound -/
namespace TranslationalTilings
def structuralCompletionPeriodBound
    (tileCard diameter numberOfParts directionProduct : ℕ) : ℕ :=
  (tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
    max 1 (directionProduct ^
      (numberOfParts + completionSliceExponent tileCard)) *
    max 1 (diameter ^
      (numberOfParts * completionSliceExponent tileCard))
end TranslationalTilings

/- blueprint/07-periodic-completion.md:243; TranslationalTilings.onePartCompletionMultiplierBound -/
namespace TranslationalTilings
def onePartCompletionMultiplierBound
    (tileCard diameter directionNorm : ℕ) : ℕ :=
  4 ^ (2 * tileCard) *
    max 1 (directionNorm ^ (completionSliceExponent tileCard + 1)) *
    max 1 (diameter ^ completionSliceExponent tileCard)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:249; TranslationalTilings.periodicTilingExponent -/
namespace TranslationalTilings
def periodicTilingExponent (tileCard : ℕ) : ℕ :=
  (tileCard - 1) * (tileCard ^ 2 + tileCard - 1)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:252; TranslationalTilings.periodicTilingConstant -/
namespace TranslationalTilings
def periodicTilingConstant (tileCard : ℕ) : ℕ :=
  weakPeriodMultiplierConstant tileCard *
    (tileCard * 4 ^ (2 * tileCard)) ^ tileCard
end TranslationalTilings

/- blueprint/07-periodic-completion.md:256; TranslationalTilings.periodicTilingPeriodBound -/
namespace TranslationalTilings
def periodicTilingPeriodBound (tileCard diameter : ℕ) : ℕ :=
  max 1 (periodicTilingConstant tileCard *
    max 1 (diameter ^ periodicTilingExponent tileCard))
end TranslationalTilings

/- blueprint/07-periodic-completion.md:260; TranslationalTilings.one_le_weakCompletionPeriodBound -/
namespace TranslationalTilings
axiom one_le_weakCompletionPeriodBound
    (tileCard diameter numberOfParts directionProduct : ℕ) :
  1 ≤ weakCompletionPeriodBound tileCard diameter numberOfParts
    directionProduct
end TranslationalTilings

/- blueprint/07-periodic-completion.md:267; TranslationalTilings.completion_singleton_bound_regression -/
namespace TranslationalTilings
theorem completion_singleton_bound_regression :
    completionSliceExponent 1 = 0 ∧
    completionPartMultiplierBound 1 0 2 4096 < 4096 ^ 2 ∧
    weakCompletionPeriodBound 1 0 2 4096 < 4096 ^ 3 := by
  norm_num [completionPartMultiplierBound, weakCompletionPeriodBound,
    completionLocalConstant, completionSliceExponent]
end TranslationalTilings

/- blueprint/07-periodic-completion.md:288; TranslationalTilings.completionPairLCM -/
namespace TranslationalTilings
def completionPairLCM
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) : ℕ :=
  pairWedgeLCM D.direction
end TranslationalTilings

/- blueprint/07-periodic-completion.md:293; TranslationalTilings.completionAvoidance -/
namespace TranslationalTilings
def completionAvoidance
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) : Plane :=
  avoidanceVector D.direction
end TranslationalTilings

/- blueprint/07-periodic-completion.md:298; TranslationalTilings.completionWedgeFactor -/
namespace TranslationalTilings
def completionWedgeFactor
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  Int.natAbs (wedge (completionAvoidance D) (D.direction j))
end TranslationalTilings

/- blueprint/07-periodic-completion.md:305; TranslationalTilings.completionConvolutionMultiplier -/
namespace TranslationalTilings
def completionConvolutionMultiplier
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  completionPairLCM D * completionWedgeFactor D j
end TranslationalTilings

/- blueprint/07-periodic-completion.md:311; TranslationalTilings.completionPrimitiveDirection -/
namespace TranslationalTilings
def completionPrimitiveDirection
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : Plane :=
  primitivePart (D.direction j)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:317; TranslationalTilings.completionDirectionContent -/
namespace TranslationalTilings
def completionDirectionContent
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  vectorContent (D.direction j)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:323; TranslationalTilings.completionDilationRatio -/
namespace TranslationalTilings
def completionDilationRatio
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  indicatorDilationModulus
      (ell * completionConvolutionMultiplier D j) F.card /
    (ell * completionConvolutionMultiplier D j)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:331; TranslationalTilings.completionSliceLCM -/
namespace TranslationalTilings
def completionSliceLCM
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  slicingLCM F (completionPrimitiveDirection D j)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:338; TranslationalTilings.completionPartMultiplier -/
namespace TranslationalTilings
def completionPartMultiplier
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  completionWedgeFactor D j * completionDilationRatio D j *
    completionDirectionContent D j * completionSliceLCM D j
end TranslationalTilings

/- blueprint/07-periodic-completion.md:346; TranslationalTilings.completionMultiplier -/
namespace TranslationalTilings
def completionMultiplier
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) : ℕ :=
  completionPairLCM D *
    ∏ j : Fin D.numberOfParts, completionPartMultiplier D j
end TranslationalTilings

/- blueprint/07-periodic-completion.md:354; TranslationalTilings.onePartDilationRatio -/
namespace TranslationalTilings
def onePartDilationRatio
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (_D : DirectionalTilingDecomposition F A E ell) : ℕ :=
  indicatorDilationModulus ell F.card / ell
end TranslationalTilings

/- blueprint/07-periodic-completion.md:360; TranslationalTilings.onePartCompletionMultiplier -/
namespace TranslationalTilings
def onePartCompletionMultiplier
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) : ℕ :=
  let j : Fin D.numberOfParts := ⟨0, D.number_pos⟩
  onePartDilationRatio D * completionDirectionContent D j *
    completionSliceLCM D j
end TranslationalTilings

/- blueprint/07-periodic-completion.md:367; TranslationalTilings.onePartDilationRatio_spec -/
namespace TranslationalTilings
axiom onePartDilationRatio_spec
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) :
  indicatorDilationModulus ell F.card = ell * onePartDilationRatio D
end TranslationalTilings

/- blueprint/07-periodic-completion.md:372; TranslationalTilings.onePartDilationRatio_pos -/
namespace TranslationalTilings
axiom onePartDilationRatio_pos
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) (hell : 0 < ell) :
  0 < onePartDilationRatio D
end TranslationalTilings

/- blueprint/07-periodic-completion.md:389; TranslationalTilings.PeriodicTilingCertificate -/
namespace TranslationalTilings
structure PeriodicTilingCertificate
    (F : Finset Plane) (E : Set Plane) (ell : ℕ) where
  tilingSet : Set Plane
  scalarMultiplier : ℕ
  multiplier_pos : 0 < scalarMultiplier
  periodic : SetScalarPeriodic (ell * scalarMultiplier) tilingSet
  tiles : Tiles F tilingSet E
end TranslationalTilings

/- blueprint/07-periodic-completion.md:399; TranslationalTilings.PeriodicTilingCertificate.rebase -/
namespace TranslationalTilings
def PeriodicTilingCertificate.rebase
    {F : Finset Plane} {E : Set Plane} {ell k : ℕ} (hk : 0 < k)
    (C : PeriodicTilingCertificate F E (ell * k)) :
    PeriodicTilingCertificate F E ell where
  tilingSet := C.tilingSet
  scalarMultiplier := k * C.scalarMultiplier
  multiplier_pos := Nat.mul_pos hk C.multiplier_pos
  periodic := by simpa [Nat.mul_assoc] using C.periodic
  tiles := C.tiles
end TranslationalTilings

/- blueprint/07-periodic-completion.md:409; TranslationalTilings.CompletionCertificate -/
namespace TranslationalTilings
structure CompletionCertificate
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) where
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
end TranslationalTilings

/- blueprint/07-periodic-completion.md:455; TranslationalTilings.PaperCompletionResult -/
namespace TranslationalTilings
structure PaperCompletionResult
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) where
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
end TranslationalTilings

/- blueprint/07-periodic-completion.md:472; TranslationalTilings.CompletionCertificate.toPaperCompletionResult -/
namespace TranslationalTilings
def CompletionCertificate.toPaperCompletionResult
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    {D : DirectionalTilingDecomposition F A E ell}
    (C : CompletionCertificate D) : PaperCompletionResult D where
  completed := C.completed
  completedMultiplier_bound := C.completedMultiplier_bound
  component_convolution := fun j ↦ ⟨C.convolutionMultiplier_pos j,
    C.convolutionMultiplier_bound j, C.convolution_periodic j⟩
end TranslationalTilings

/- blueprint/07-periodic-completion.md:541; TranslationalTilings.weakCompletionPeriodBound_le_structuralCompletionPeriodBound -/
namespace TranslationalTilings
axiom weakCompletionPeriodBound_le_structuralCompletionPeriodBound
    {tileCard diameter numberOfParts directionProduct : ℕ}
    (hmpos : 0 < numberOfParts)
    (hmcard : numberOfParts ≤ tileCard - 1) :
  weakCompletionPeriodBound tileCard diameter numberOfParts directionProduct ≤
    structuralCompletionPeriodBound tileCard diameter numberOfParts
      directionProduct
end TranslationalTilings

/- blueprint/07-periodic-completion.md:549; TranslationalTilings.CompletionCertificate.completedMultiplier_structural_bound -/
namespace TranslationalTilings
axiom CompletionCertificate.completedMultiplier_structural_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    {D : DirectionalTilingDecomposition F A E ell}
    (C : CompletionCertificate D)
    (hmcard : D.numberOfParts ≤ F.card - 1) :
  C.completed.scalarMultiplier ≤
    structuralCompletionPeriodBound F.card (l1Diameter F) D.numberOfParts
      (∏ i : Fin D.numberOfParts, l1Norm (D.direction i))
end TranslationalTilings

/- blueprint/07-periodic-completion.md:558; TranslationalTilings.one_lt_tileCard_of_structural_parts -/
namespace TranslationalTilings
axiom one_lt_tileCard_of_structural_parts
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    {D : DirectionalTilingDecomposition F A E ell}
    (hm : 2 ≤ D.numberOfParts)
    (hmcard : D.numberOfParts ≤ F.card - 1) :
  1 < F.card
end TranslationalTilings

/- blueprint/07-periodic-completion.md:581; TranslationalTilings.improve_onePart -/
namespace TranslationalTilings
axiom improve_onePart
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hone : D.numberOfParts = 1) :
  ∃ C : PeriodicTilingCertificate F E ell,
    C.scalarMultiplier = onePartCompletionMultiplier D ∧
    C.scalarMultiplier ≤ onePartCompletionMultiplierBound F.card
      (l1Diameter F) (l1Norm (D.direction ⟨0, D.number_pos⟩))
end TranslationalTilings

/- blueprint/07-periodic-completion.md:608; TranslationalTilings.convolution_part_scalarPeriodic -/
namespace TranslationalTilings
axiom convolution_part_scalarPeriodic
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (hm : 2 ≤ D.numberOfParts) (j : Fin D.numberOfParts) :
  0 < completionConvolutionMultiplier D j ∧
    completionConvolutionMultiplier D j ≤
      completionConvolutionBound D.numberOfParts
      (∏ i : Fin D.numberOfParts, l1Norm (D.direction i))
      (l1Norm (D.direction j)) ∧
    ScalarPeriodic (ell * completionConvolutionMultiplier D j)
      (tileConv F (setIndicator (D.part j)))
end TranslationalTilings

/- blueprint/07-periodic-completion.md:621; TranslationalTilings.improve_weaklyPeriodic_exact -/
namespace TranslationalTilings
axiom improve_weaklyPeriodic_exact
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (hcard : 1 < F.card)
    (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts) :
  Nonempty (CompletionCertificate D)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:630; TranslationalTilings.improve_weaklyPeriodic_structural -/
namespace TranslationalTilings
axiom improve_weaklyPeriodic_structural
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts)
    (hmcard : D.numberOfParts ≤ F.card - 1) :
  ∃ C : CompletionCertificate D,
    C.completed.scalarMultiplier ≤
      structuralCompletionPeriodBound F.card (l1Diameter F)
        D.numberOfParts
        (∏ i : Fin D.numberOfParts, l1Norm (D.direction i))
end TranslationalTilings

/- blueprint/07-periodic-completion.md:644; TranslationalTilings.singleton_tile_periodic_completion -/
namespace TranslationalTilings
axiom singleton_tile_periodic_completion
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (hcard : F.card = 1) :
  ∃ C : PeriodicTilingCertificate F E ell,
    C.scalarMultiplier = 1
end TranslationalTilings

/- blueprint/07-periodic-completion.md:653; TranslationalTilings.improve_weaklyPeriodic -/
namespace TranslationalTilings
axiom improve_weaklyPeriodic
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts) :
  Nonempty (PaperCompletionResult D)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:754; TranslationalTilings.periodicTilingExponent_le_quartic -/
namespace TranslationalTilings
axiom periodicTilingExponent_le_quartic (tileCard : ℕ) :
  periodicTilingExponent tileCard ≤ 3 * (tileCard + 1) ^ 4
end TranslationalTilings

/- blueprint/07-periodic-completion.md:758; TranslationalTilings.quantitative_periodic_tiling_l1 -/
namespace TranslationalTilings
axiom quantitative_periodic_tiling_l1
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (hexists : ∃ A, Tiles F A E) :
  ∃ C : PeriodicTilingCertificate F E ell,
    C.scalarMultiplier ≤ periodicTilingPeriodBound F.card (l1Diameter F)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:765; TranslationalTilings.periodicTilingEuclideanConstant -/
namespace TranslationalTilings
noncomputable def periodicTilingEuclideanConstant (tileCard : ℕ) : ℝ :=
  periodicTilingConstant tileCard *
    Real.sqrt 2 ^ periodicTilingExponent tileCard
end TranslationalTilings

/- blueprint/07-periodic-completion.md:770; TranslationalTilings.quantitative_periodic_tiling_euclidean -/
namespace TranslationalTilings
axiom quantitative_periodic_tiling_euclidean
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (hexists : ∃ A, Tiles F A E) :
  ∃ (A' : Set Plane) (M : ℕ),
    0 < M ∧ Tiles F A' E ∧ SetScalarPeriodic (ell * M) A' ∧
    (M : ℝ) ≤ periodicTilingEuclideanConstant F.card *
      max 1 (euclideanDiameter F ^ periodicTilingExponent F.card)
end TranslationalTilings
