# Slicing and conversion to a periodic tiling

Paper coverage: Lemma 5.1, Corollary 5.3, Theorem 5.4, and Theorem 1.5.
Target modules:

```lean
import TranslationalTilings.Dilation.Periodic
import TranslationalTilings.WeakPeriodicity
```

## 1. Slices and the nonzero-wedge lcm

```lean
namespace TranslationalTilings

def directionSubgroup (h : Plane) : AddSubgroup Plane :=
  AddSubgroup.zmultiples h

noncomputable def tileSlice (F : Finset Plane) (h x : Plane) : Finset Plane := by
  classical
  exact F.filter fun f ↦ f ∈ addCoset (directionSubgroup h) x

def slicingPairs (F : Finset Plane) (h : Plane) :
    Finset (Plane × Plane) :=
  (F ×ˢ F).filter fun ff ↦ wedge h (ff.1 - ff.2) ≠ 0

def slicingLCM (F : Finset Plane) (h : Plane) : ℕ :=
  (slicingPairs F h).lcm fun ff ↦
    Int.natAbs (wedge h (ff.1 - ff.2))

def slicePattern (h : Plane)
    (line : Plane ⧸ directionSubgroup h) (A : Set Plane) : Set Plane :=
  A ∩ quotientCoset (directionSubgroup h) line

def convolutionEquivalent {G : Type*} [AddCommGroup G]
    (F : Finset G) (A B : Set G) : Prop :=
  tileConv F (setIndicator A) = tileConv F (setIndicator B)
```

The filter is by `wedge ≠ 0`, not by a diagonal-sensitive surrogate.  Equal
pairs and all differences parallel to `h` are excluded before the lcm is
taken.  The lcm of an empty family is one, so it is always positive.  The
quotient-fiber definition of `slicePattern` contains no chosen representative.

```lean
theorem tileSlice_eq_empty_iff (F : Finset Plane) (h x : Plane) :
  tileSlice F h x = ∅ ↔ ∀ f ∈ F, f ∉ addCoset (directionSubgroup h) x

theorem tileSlice_translate (F : Finset Plane) (h x a : Plane) :
  tileSlice (F.image (fun f ↦ f + a)) h (x + a) =
    (tileSlice F h x).image (fun f ↦ f + a)

theorem slicingLCM_pos (F : Finset Plane) (h : Plane) :
  0 < slicingLCM F h

theorem wedge_difference_dvd_slicingLCM
    {f f' : Plane} (hf : f ∈ F) (hf' : f' ∈ F)
    (hwedge : wedge h (f - f') ≠ 0) :
  Int.natAbs (wedge h (f - f')) ∣ slicingLCM F h

theorem slicingLCM_bound
    (F : Finset Plane) {h : Plane} (hprimitive : IsPrimitive h) :
  slicingLCM F h ≤
    (l1Norm h * l1Diameter F) ^ (F.card * (F.card - 1) / 2)

theorem mem_slicePattern
    {h : Plane} {line : Plane ⧸ directionSubgroup h} {A : Set Plane}
    (y : Plane) :
  y ∈ slicePattern h line A ↔
    y ∈ A ∧ QuotientAddGroup.mk' (directionSubgroup h) y = line
```

For the bound, replace the ordered-pair product by one representative for each
unordered pair; the two orientations have equal absolute wedge.  Every
surviving factor is positive and at most
`l1Norm h*l1Diameter F`, and there are at most `c(c-1)/2` of them.

## 2. Lemma 5.1 and Corollary 5.3

```lean
/-- Greenfeld--Tao, Lemma 5.1. -/
theorem slicing_lemma
    {F : Finset Plane} {A : Set Plane} {ell k : ℕ} {h x : Plane}
    (hell : 0 < ell) (hk : 0 < k) (hh : IsPrimitive h)
    (hAperiod : Function.Periodic (setIndicator A)
      (((ell * k : ℕ) : ℤ) • h))
    (hconvperiod : ScalarPeriodic ell (tileConv F (setIndicator A))) :
  ScalarPeriodic
    (indicatorDilationModulus ell F.card * k * slicingLCM F h)
    (tileConv (tileSlice F h x) (setIndicator A))

/-- Greenfeld--Tao, Corollary 5.3. -/
theorem improve_onePeriodic
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
        (slicePattern h line A')
```

For the slicing lemma, translate a nonempty selected slice so that it contains
zero; the empty slice is immediate.  Dilation invariance holds for
`r ≡ 1 mod q`, where `q=indicatorDilationModulus ell F.card`.  Restrict to
`r ≡ 1 mod q*k`.  If `f` lies on the selected line, `r*f-f` is a multiple of
`ell*k*h`, so its contribution is unchanged.  Average the other translates
over the ray as in Chapter 3.  Each limit function has periods `ell*k*h` and
`q*k*f`.  Its nonzero wedge divides `slicingLCM F h`; Cramer's inclusion
therefore gives the full scalar period `q*k*s`.  The original convolution is
also scalar-periodic by that integer because `ell | q`.

For the corollary, an `SL(2,Z)` equivalence sends `h` to `(1,0)`.  An
`ell*k*h`-periodic set restricts on every parallel line to a bit vector of
length `ell*k`.  There are finitely many such vectors.  Order them
lexicographically, and replace each line pattern by the least pattern having
the same convolutions with every tile slice.  Lemma 5.1 says the equivalence
class repeats transversely with period `q*k*s`; least representatives are
therefore equal after that shift.  They also keep their longitudinal period.
The assembled set is scalar-periodic and preserves the convolution on each
line.  The `SL(2,Z)` transport preserves finite convolution, membership,
scalar periodicity, and all slice equalities.

The finite pattern used in this proof is a closed data type:

```lean
abbrev LinePattern (period : ℕ) := Fin period → Bool

def linePatternSetOfPos (period : ℕ) (hperiod : 0 < period)
    (P : LinePattern period) : Set ℤ :=
  {n | P ⟨n.natMod period, Int.natMod_lt hperiod.ne'⟩}
```

The positivity proof is deliberately part of the definition's API.  It rules
out the invalid `Fin 0` pattern type and supplies the proof required by
`Int.natMod_lt`; there is no second, partially specified notation-only
definition.

## 3. Directional decompositions already include the tiling hypotheses

```lean
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
```

The last two fields prevent the false unconstrained component-convolution
claim found by the first review.  The structure is proof-relevant public data
used by the classifier in Chapter 8.

Theorem 1.4 returns cosetwise periodicity, rather than a global partition with
one part for every direction.  The following bridge performs that conversion
below the periodic-completion dependency boundary, so both Theorem 1.5 and the
classifier can reuse it.

```lean
theorem exists_directionalTilingDecomposition_of_quantitativeData
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (htile : Tiles F A E) (W : QuantitativeWeakPeriodData F ell)
    (hW : W.ValidFor A) :
  ∃ D : DirectionalTilingDecomposition F A E (ell * W.multiplier),
    ∃ hnum : D.numberOfParts = W.numberOfDirections,
      ∀ j : Fin W.numberOfDirections,
        D.direction (Fin.cast hnum.symm j) = W.direction j
```

For each quotient fiber of `W.lattice`, choose the least direction index that
witnesses `hW`; the direction type is nonempty by `W.number_pos`.  Define the
`j`th part to be the union of the fibers assigned to `j`, intersected with
`A`.  Quotient fibers are pairwise disjoint and cover the plane, so these parts
are pairwise disjoint and have union `A`.  The advertised period belongs to
`W.lattice`, hence preserves its fiber, and the chosen witness makes the
intersection periodic.  A union of fibers assigned the same index therefore
has period `(ell*W.multiplier)•W.direction j`.  The original tiling identity is
unchanged, and `ell ∣ ell*W.multiplier` lifts `hE` to the required target
periodicity.  The least-index choice is proof-only and stays private; the
displayed existence theorem is the reusable public boundary.

## 4. Exact completion data and bounds

Let `c=|F|`, `D=l1Diameter F`, `m` be the number of parts,
`H=prod_j ||h_j||_1`, and `r=c(c-1)/2`.  Use the following closed functions:

```lean
def completionSliceExponent (tileCard : ℕ) : ℕ :=
  tileCard * (tileCard - 1) / 2

theorem completionSliceExponent_pos {tileCard : ℕ}
    (hcard : 1 < tileCard) :
  0 < completionSliceExponent tileCard

def completionConvolutionBound
    (numberOfParts directionProduct directionNorm : ℕ) : ℕ :=
  max 1 (directionProduct ^ (numberOfParts - 1) *
    (numberOfParts + 1) * directionNorm)

def completionLocalConstant (tileCard numberOfParts : ℕ) : ℕ :=
  (numberOfParts + 1) * 4 ^ (2 * tileCard)

def completionPartMultiplierBound
    (tileCard diameter numberOfParts directionNorm : ℕ) : ℕ :=
  completionLocalConstant tileCard numberOfParts *
    max 1 (directionNorm ^ (completionSliceExponent tileCard + 1)) *
    max 1 (diameter ^ completionSliceExponent tileCard)

def weakCompletionPeriodBound
    (tileCard diameter numberOfParts directionProduct : ℕ) : ℕ :=
  completionLocalConstant tileCard numberOfParts ^ numberOfParts *
    max 1 (directionProduct ^
      (numberOfParts + completionSliceExponent tileCard)) *
    max 1 (diameter ^
      (numberOfParts * completionSliceExponent tileCard))

/-- The completion bound with a hidden constant depending only on `tileCard`.
It is used in the structural regime `numberOfParts ≤ tileCard-1`. -/
def structuralCompletionPeriodBound
    (tileCard diameter numberOfParts directionProduct : ℕ) : ℕ :=
  (tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
    max 1 (directionProduct ^
      (numberOfParts + completionSliceExponent tileCard)) *
    max 1 (diameter ^
      (numberOfParts * completionSliceExponent tileCard))

/-- The exact multiplier bound for completing a single directional part. -/
def onePartCompletionMultiplierBound
    (tileCard diameter directionNorm : ℕ) : ℕ :=
  4 ^ (2 * tileCard) *
    max 1 (directionNorm ^ (completionSliceExponent tileCard + 1)) *
    max 1 (diameter ^ completionSliceExponent tileCard)

def periodicTilingExponent (tileCard : ℕ) : ℕ :=
  (tileCard - 1) * (tileCard ^ 2 + tileCard - 1)

def periodicTilingConstant (tileCard : ℕ) : ℕ :=
  weakPeriodMultiplierConstant tileCard *
    (tileCard * 4 ^ (2 * tileCard)) ^ tileCard

def periodicTilingPeriodBound (tileCard diameter : ℕ) : ℕ :=
  max 1 (periodicTilingConstant tileCard *
    max 1 (diameter ^ periodicTilingExponent tileCard))

theorem one_le_weakCompletionPeriodBound
    (tileCard diameter numberOfParts directionProduct : ℕ) :
  1 ≤ weakCompletionPeriodBound tileCard diameter numberOfParts
    directionProduct

/-- Numerical core of the singleton-domain counterexample to the old exact
completion-certificate theorem. -/
theorem completion_singleton_bound_regression :
    completionSliceExponent 1 = 0 ∧
    completionPartMultiplierBound 1 0 2 4096 < 4096 ^ 2 ∧
    weakCompletionPeriodBound 1 0 2 4096 < 4096 ^ 3 := by
  norm_num [completionPartMultiplierBound, weakCompletionPeriodBound,
    completionLocalConstant, completionSliceExponent]
```

For `completionSliceExponent_pos`, `1<tileCard` gives `2≤tileCard` and
`1≤tileCard-1`; hence `2≤tileCard*(tileCard-1)`, so division by two is
positive.  This named lemma, rather than an informal `r>0`, is consumed by the
exact constructor before rewriting the exponent `r-1`.  Every factor in
`weakCompletionPeriodBound` is at least one: the local constant is positive
and the other two factors are protected by `max 1`; this proves
`one_le_weakCompletionPeriodBound`.  The final theorem has a checked
`norm_num` body so the singleton arithmetic cannot drift silently.

The exact arithmetic used in the proof is represented by closed definitions,
not by locally chosen unnamed naturals:

```lean
def completionPairLCM
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) : ℕ :=
  pairWedgeLCM D.direction

def completionAvoidance
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) : Plane :=
  avoidanceVector D.direction

def completionWedgeFactor
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  Int.natAbs (wedge (completionAvoidance D) (D.direction j))

/-- The `N_j` in the first clause of Theorem 5.4. -/
def completionConvolutionMultiplier
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  completionPairLCM D * completionWedgeFactor D j

def completionPrimitiveDirection
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : Plane :=
  primitivePart (D.direction j)

def completionDirectionContent
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  vectorContent (D.direction j)

def completionDilationRatio
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  indicatorDilationModulus
      (ell * completionConvolutionMultiplier D j) F.card /
    (ell * completionConvolutionMultiplier D j)

def completionSliceLCM
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  slicingLCM F (completionPrimitiveDirection D j)

/-- The `L_j` in the proof of Theorem 5.4. -/
def completionPartMultiplier
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (j : Fin D.numberOfParts) : ℕ :=
  completionWedgeFactor D j * completionDilationRatio D j *
    completionDirectionContent D j * completionSliceLCM D j

/-- The final `M = N * product_j L_j` in Theorem 5.4. -/
def completionMultiplier
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) : ℕ :=
  completionPairLCM D *
    ∏ j : Fin D.numberOfParts, completionPartMultiplier D j

/-- Dilation ratio used when the decomposition has exactly one part.  In that
case its convolution is the target itself, so no auxiliary `N_j` is needed. -/
def onePartDilationRatio
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (_D : DirectionalTilingDecomposition F A E ell) : ℕ :=
  indicatorDilationModulus ell F.card / ell

/-- Exact multiplier obtained by applying Corollary 5.3 to the sole part. -/
def onePartCompletionMultiplier
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) : ℕ :=
  let j : Fin D.numberOfParts := ⟨0, D.number_pos⟩
  onePartDilationRatio D * completionDirectionContent D j *
    completionSliceLCM D j

theorem onePartDilationRatio_spec
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) :
  indicatorDilationModulus ell F.card = ell * onePartDilationRatio D

theorem onePartDilationRatio_pos
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell) (hell : 0 < ell) :
  0 < onePartDilationRatio D
```

Here `completionDilationRatio D j` is the paper's `C_j`.  Its denominator is
positive under the hypotheses of Theorem 5.4; the total natural-number
definition remains meaningful outside that theorem.  The first one-part
identity is `Nat.mul_div_cancel' (ell_dvd_dilationModulus ell 1 F.card)`, and
the positivity theorem uses `dilationModulus_pos hell` and `Nat.div_pos`.
Thus the later claim that the Corollary 5.3 period is *exactly* `ell` times
the stored multiplier is a public checked equality, not an informal division
step.  The exact intermediate data and the two quantitative conclusions are
exposed by certificates:

```lean
structure PeriodicTilingCertificate
    (F : Finset Plane) (E : Set Plane) (ell : ℕ) where
  tilingSet : Set Plane
  scalarMultiplier : ℕ
  multiplier_pos : 0 < scalarMultiplier
  periodic : SetScalarPeriodic (ell * scalarMultiplier) tilingSet
  tiles : Tiles F tilingSet E

/-- Reinterpret a certificate whose base period is `ell*k` as one whose base
period is `ell`, multiplying the stored scalar multiplier by `k`. -/
def PeriodicTilingCertificate.rebase
    {F : Finset Plane} {E : Set Plane} {ell k : ℕ} (hk : 0 < k)
    (C : PeriodicTilingCertificate F E (ell * k)) :
    PeriodicTilingCertificate F E ell where
  tilingSet := C.tilingSet
  scalarMultiplier := k * C.scalarMultiplier
  multiplier_pos := Nat.mul_pos hk C.multiplier_pos
  periodic := by simpa [Nat.mul_assoc] using C.periodic
  tiles := C.tiles

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

/-- The paper-facing payload of Theorem 5.4.  It retains the periodic
completion and the theorem's separate component-convolution clause, but does
not promise the exact `N * product L_j` construction in the singleton branch. -/
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

def CompletionCertificate.toPaperCompletionResult
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    {D : DirectionalTilingDecomposition F A E ell}
    (C : CompletionCertificate D) : PaperCompletionResult D where
  completed := C.completed
  completedMultiplier_bound := C.completedMultiplier_bound
  component_convolution := fun j ↦ ⟨C.convolutionMultiplier_pos j,
    C.convolutionMultiplier_bound j, C.convolution_periodic j⟩
```

This records the exact `N`, `N_j`, `C_j`, `s_j`, `L_j`, and `M`, both
quantitative conclusions of Theorem 5.4, the separately improved parts, and
the convolution/disjoint-union facts from which the final tiling is assembled.
It is therefore a construction certificate, not the literal domain-total
paper conclusion.  `PaperCompletionResult` is the weaker public result
payload: it remembers the final periodic tiling, its honest general bound, and
the separately stated `N_j` component conclusion.  The conversion above
forgets only exact construction data and is used in the non-singleton branch.

The hypothesis `1<F.card` is essential for constructing a
`CompletionCertificate`.  Here is the negative regression which fixes its
domain.  Put `k=4096`, `ell=1`, `F={0}`, and `A=E=Set.univ`.  There is a valid
two-part `DirectionalTilingDecomposition` with

```text
part 0 = empty,       direction 0 = (k,0),
part 1 = Set.univ,    direction 1 = (0,1).
```

The directions are nonzero and have wedge `k`, the two constant indicators
have their advertised periods, and empty parts are permitted.  The avoidance
search checks `(1,0),(1,1),(1,2)` and selects `(1,1)`.  At the first part the
frozen exact definitions therefore give

```text
completionPairLCM                  = k,
completionWedgeFactor              = k,
completionConvolutionMultiplier    = k^2,
completionDirectionContent         = k,
completionPrimitiveDirection       = (1,0),
completionSliceLCM                  = 1,
completionDilationRatio             = 1,
completionPartMultiplier            = k^2.
```

The slice lcm is one because a singleton tile has no nonzero-wedge pair, and
`indicatorDilationModulus (k^2) 1=lcm(k^2,primorial 2)=k^2` because `k` is
even.  Hence the exact total multiplier is `k^3`.  But
`completionSliceExponent 1=0`, so the advertised local bound is only
`48*k=196608<k^2=16777216`, and the total bound is only
`48^2*k^2=38654705664<k^3=68719476736`.  The checked theorem
`completion_singleton_bound_regression` records precisely these two strict
inequalities.  This is not malformed input: the old constructor's hypotheses
all hold.  Its proof failed exactly at

```text
k_j * ||h'_j||_1^r = ||h_j||_1 * ||h'_j||_1^(r-1),
```

which requires `r=F.card*(F.card-1)/2>0`.  The new non-singleton hypothesis
gives that positivity.  In the singleton branch the paper conclusion is
instead proved directly with multiplier one, without claiming any of the
exact `N * product L_j` fields.

The general certificate deliberately retains an explicit `m`-dependent local
constant.  The paper's `\ll_{|F|}` form is recovered only in the structural
regime `m≤|F|-1`, which is the regime supplied by Theorem 1.4:

```lean
theorem weakCompletionPeriodBound_le_structuralCompletionPeriodBound
    {tileCard diameter numberOfParts directionProduct : ℕ}
    (hmpos : 0 < numberOfParts)
    (hmcard : numberOfParts ≤ tileCard - 1) :
  weakCompletionPeriodBound tileCard diameter numberOfParts directionProduct ≤
    structuralCompletionPeriodBound tileCard diameter numberOfParts
      directionProduct

theorem CompletionCertificate.completedMultiplier_structural_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    {D : DirectionalTilingDecomposition F A E ell}
    (C : CompletionCertificate D)
    (hmcard : D.numberOfParts ≤ F.card - 1) :
  C.completed.scalarMultiplier ≤
    structuralCompletionPeriodBound F.card (l1Diameter F) D.numberOfParts
      (∏ i : Fin D.numberOfParts, l1Norm (D.direction i))

theorem one_lt_tileCard_of_structural_parts
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    {D : DirectionalTilingDecomposition F A E ell}
    (hm : 2 ≤ D.numberOfParts)
    (hmcard : D.numberOfParts ≤ F.card - 1) :
  1 < F.card
```

Indeed `m+1≤c`, `m≤c`, and positivity supplied by `hmpos` give

`((m+1)4^(2c))^m ≤ (c4^(2c))^c`.

All other factors are definitionally identical.  Thus the hidden constant in
the second theorem is a function of `c` alone; no `m`-dependent factor is
silently called an `O_c(1)` constant.  For the final helper, natural-number
arithmetic gives `2≤F.card-1` from `hm.trans hmcard`, hence `3≤F.card` and
in particular `1<F.card`.  This is the exact bridge used by the structural
constructor; it does not acquire a new public cardinality assumption.

The one-part case has its own exact certificate theorem rather than pretending
that the `m≥2` difference argument applies:

```lean
theorem improve_onePart
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hone : D.numberOfParts = 1) :
  ∃ C : PeriodicTilingCertificate F E ell,
    C.scalarMultiplier = onePartCompletionMultiplier D ∧
    C.scalarMultiplier ≤ onePartCompletionMultiplierBound F.card
      (l1Diameter F) (l1Norm (D.direction ⟨0, D.number_pos⟩))
```

Let `h=D.direction 0`, `k=vectorContent h`, and `h'=primitivePart h`.
The sole part is `A`, its period is `ell*h=ell*k*h'`, and its convolution is
the `ell Z²`-periodic target.  Corollary 5.3 returns a set with scalar period

`indicatorDilationModulus ell c * k * slicingLCM F h'`.

By `onePartDilationRatio_spec`, this is exactly `ell` times
`onePartCompletionMultiplier D`.  Positivity follows from
`onePartDilationRatio_pos hell`, nonzero `h`, primitive decomposition, and
`slicingLCM_pos`.  The slice bound and
`k*||h'||₁=||h||₁` give the displayed multiplier bound.  Convolution
equivalence and `D.tiles` give the new tiling; no nonempty-tile cancellation is
needed in the one-part case.

## 5. Theorem 5.4

```lean
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
      (tileConv F (setIndicator (D.part j)))

/-- Exact `N,N_j,C_j,s_j,L_j,M` construction underlying Theorem 5.4. -/
theorem improve_weaklyPeriodic_exact
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (hcard : 1 < F.card)
    (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts) :
  Nonempty (CompletionCertificate D)

/-- Theorem 5.4 in the structural regime used by Theorems 1.4 and 1.5, with
the printed hidden constant depending only on the tile cardinality. -/
theorem improve_weaklyPeriodic_structural
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts)
    (hmcard : D.numberOfParts ≤ F.card - 1) :
  ∃ C : CompletionCertificate D,
    C.completed.scalarMultiplier ≤
      structuralCompletionPeriodBound F.card (l1Diameter F)
        D.numberOfParts
        (∏ i : Fin D.numberOfParts, l1Norm (D.direction i))

/-- Direct periodic completion for a singleton tile.  It deliberately returns
only the paper conclusion, not the false singleton instance of the exact
construction certificate. -/
theorem singleton_tile_periodic_completion
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (hcard : F.card = 1) :
  ∃ C : PeriodicTilingCertificate F E ell,
    C.scalarMultiplier = 1

/-- Greenfeld--Tao, Theorem 5.4, with its completion and separate
component-convolution clauses, valid also for singleton tiles. -/
theorem improve_weaklyPeriodic
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hF : F.Nonempty) (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts) :
  Nonempty (PaperCompletionResult D)
```

For the convolution theorem, choose `eTilde=avoidanceVector D.direction`,
`N=pairWedgeLCM D.direction`, and `e=ell*N*eTilde`.  Differentiate the tiling
identity once for every `i≠j`.  The derivative kills the target because its
shift belongs to `ell Z^2`, kills the `i`th component by its directional
period, and acts as `Delta_e` on the `j`th.  The remaining convolution is a
bounded integer function; its restriction to every `e`-line has vanishing
`(m-1)`st difference and is constant.  It has periods `e` and `ell*h_j`, so
Cramer gives scalar multiplier

`N_j = N * |eTilde wedge h_j|`.

The product bound on `N` and `||eTilde||_1≤m+1` give exactly
`completionConvolutionBound`.

For each part, write `h_j=k_j*h'_j` with `h'_j` primitive.  Apply Corollary
5.3 with

```text
ell_j = ell * N_j
k       = k_j
C_j     = indicatorDilationModulus ell_j c / ell_j
s_j     = slicingLCM F h'_j
L_j     = |eTilde wedge h_j| * C_j * k_j * s_j.
```

Here `C_j≤4^(2c)`, and

`k_j * ||h'_j||_1^r = ||h_j||_1 * ||h'_j||_1^(r-1)`

for `r>0`.  The exact constructor applies
`completionSliceExponent_pos hcard` before this rewrite: since `1<c`, there
are at least two tile elements and hence at least one unordered pair.  Thus
the natural subtraction `r-1` does not truncate.  Consequently

`L_j≤(m+1)4^(2c)||h_j||_1^(r+1)D^r`,

which is `completionPartMultiplierBound`.  The improved part is
`ell*N*L_j Z^2`-periodic.  Taking

`M = N * product_j L_j`

makes every improved part `ell*M Z^2`-periodic and gives

`M≤((m+1)4^(2c))^m H^(m+r) D^(m*r)`.

This is the honest general `m`-dependent estimate.  When `m≤c-1`, the
structural comparison theorem replaces its first factor by
`(c*4^(2c))^c`, yielding exactly a hidden constant depending only on `c` as in
the paper's intended application.  In
`improve_weaklyPeriodic_structural`, `one_lt_tileCard_of_structural_parts hm
hmcard` first derives the hypothesis of `improve_weaklyPeriodic_exact`; the
resulting exact certificate is then paired with
`CompletionCertificate.completedMultiplier_structural_bound`.  No
non-singleton hypothesis is smuggled into the structural theorem's public
domain.

Summing their convolution identities yields the target indicator.  To prove
the improved parts disjoint, choose `f₀∈F` using `hF`; at `x+f₀` the
nonnegative convolution sum contains the value of the sum of part indicators
at `x`, while the target indicator is at most one.  Thus the pointwise sum is
at most one.  This is the nonempty-tile hypothesis that was absent from the
rejected blueprint.

It remains to prove the domain-total paper wrapper.  From `hF`, choose the
unique `f∈F` when `F.card=1`, so `F={f}`.  Define

```text
A' = { x | x+f ∈ E }.
```

Then at every `x`, the singleton convolution is
`1_A'(x-f)=1_E(x)`, so `Tiles F A' E`.  Moreover

```text
(x+ell*z)+f = (x+f)+ell*z,
```

and `D.target_periodic` proves that `A'` is `ell Z²`-periodic.  Taking
scalar multiplier one gives `singleton_tile_periodic_completion`.  Its bound
inside `PaperCompletionResult` follows from
`one_le_weakCompletionPeriodBound`; its component field is supplied, for
every `j`, by `convolution_part_scalarPeriodic D hm j`.

Finally, `Finset.card_pos.mpr hF` and natural trichotomy split the paper
wrapper into `F.card=1` or `1<F.card`.  The first branch is the direct
construction above.  The second invokes `improve_weaklyPeriodic_exact` and
then `CompletionCertificate.toPaperCompletionResult`.  Thus
`improve_weaklyPeriodic` is valid on the paper's full nonempty-tile domain,
while the stronger exact arithmetic is promised only where its `r>0`
estimate is true.

## 6. Theorem 1.5 with a fixed exponent polynomial

```lean
theorem periodicTilingExponent_le_quartic (tileCard : ℕ) :
  periodicTilingExponent tileCard ≤ 3 * (tileCard + 1) ^ 4

/-- Greenfeld--Tao, Theorem 1.5, l1 form. -/
theorem quantitative_periodic_tiling_l1
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (hexists : ∃ A, Tiles F A E) :
  ∃ C : PeriodicTilingCertificate F E ell,
    C.scalarMultiplier ≤ periodicTilingPeriodBound F.card (l1Diameter F)

noncomputable def periodicTilingEuclideanConstant (tileCard : ℕ) : ℝ :=
  periodicTilingConstant tileCard *
    Real.sqrt 2 ^ periodicTilingExponent tileCard

/-- Greenfeld--Tao, Theorem 1.5, paper-facing Euclidean form. -/
theorem quantitative_periodic_tiling_euclidean
    {F : Finset Plane} {E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (hexists : ∃ A, Tiles F A E) :
  ∃ (A' : Set Plane) (M : ℕ),
    0 < M ∧ Tiles F A' E ∧ SetScalarPeriodic (ell * M) A' ∧
    (M : ℝ) ≤ periodicTilingEuclideanConstant F.card *
      max 1 (euclideanDiameter F ^ periodicTilingExponent F.card)

end TranslationalTilings
```

If `E=∅`, choose the empty periodic tiling.  If `E` is nonempty, any tile in
`hexists` is nonempty.  A singleton tile is handled by translating `E`.
Otherwise Theorem 1.4 supplies quantitative cosetwise data with multiplier
`L₀`.  Apply
`exists_directionalTilingDecomposition_of_quantitativeData` to obtain the
actual disjoint directional partition with common base period `ell*L₀`.  If it
has one part, apply `improve_onePart`; if it has two or more parts, use
`improve_weaklyPeriodic_structural` (the direction-count field gives
`m≤c-1`, and that theorem derives `1<c` from these two inequalities before
calling the exact constructor).  In either case, apply
`PeriodicTilingCertificate.rebase` with `L₀`
to turn the certificate over base `ell*L₀` into one over base `ell`, whose
multiplier is exactly `L₀` times the completion multiplier.

With `m≤c-1`, `H≤D^(c-1)`, and `r=c(c-1)/2`, the completion exponent is

`(c-1)*(m+r)+m*r ≤ (c+1)*(c-1)^2`.

Adding the weak multiplier exponent `c(c-1)` gives

`periodicTilingExponent c=(c-1)(c^2+c-1)`.

This is actually cubic, hence satisfies the paper's coarser `O(c^4)` claim by
`periodicTilingExponent_le_quartic`.  The bound no longer contains a function
named “constant” whose value depends on the diameter or an existential
exponent that makes the asymptotic statement vacuous.
