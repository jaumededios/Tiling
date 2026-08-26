import TranslationalTilings.Dilation.Periodic
import TranslationalTilings.LatticeGeometry

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 8d1f5c269f26b6ded57492026a5c6dd65f659fdd42669d1797e69607a4f74afa  blueprint/07-periodic-completion.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/07-periodic-completion.md:16; TranslationalTilings.directionSubgroup -/
namespace TranslationalTilings
def directionSubgroup (h : Plane) : AddSubgroup Plane :=
  AddSubgroup.zmultiples h
end TranslationalTilings

/- blueprint/07-periodic-completion.md:19; TranslationalTilings.tileSlice -/
namespace TranslationalTilings
noncomputable def tileSlice (F : Finset Plane) (h x : Plane) : Finset Plane := by
  classical
  exact F.filter fun f ↦ f ∈ addCoset (directionSubgroup h) x
end TranslationalTilings

/- blueprint/07-periodic-completion.md:23; TranslationalTilings.slicingPairs -/
namespace TranslationalTilings
def slicingPairs (F : Finset Plane) (h : Plane) :
    Finset (Plane × Plane) :=
  (F ×ˢ F).filter fun ff ↦ wedge h (ff.1 - ff.2) ≠ 0
end TranslationalTilings

/- blueprint/07-periodic-completion.md:27; TranslationalTilings.slicingLCM -/
namespace TranslationalTilings
def slicingLCM (F : Finset Plane) (h : Plane) : ℕ :=
  (slicingPairs F h).lcm fun ff ↦
    Int.natAbs (wedge h (ff.1 - ff.2))
end TranslationalTilings

/- blueprint/07-periodic-completion.md:31; TranslationalTilings.slicePattern -/
namespace TranslationalTilings
def slicePattern (h : Plane)
    (line : Plane ⧸ directionSubgroup h) (A : Set Plane) : Set Plane :=
  A ∩ quotientCoset (directionSubgroup h) line
end TranslationalTilings

/- blueprint/07-periodic-completion.md:35; TranslationalTilings.convolutionEquivalent -/
namespace TranslationalTilings
def convolutionEquivalent {G : Type*} [AddCommGroup G]
    (F : Finset G) (A B : Set G) : Prop :=
  tileConv F (setIndicator A) = tileConv F (setIndicator B)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:46; TranslationalTilings.tileSlice_eq_empty_iff -/
namespace TranslationalTilings
axiom tileSlice_eq_empty_iff (F : Finset Plane) (h x : Plane) :
  tileSlice F h x = ∅ ↔ ∀ f ∈ F, f ∉ addCoset (directionSubgroup h) x
end TranslationalTilings

/- blueprint/07-periodic-completion.md:49; TranslationalTilings.tileSlice_translate -/
namespace TranslationalTilings
axiom tileSlice_translate (F : Finset Plane) (h x a : Plane) :
  tileSlice (F.image (fun f ↦ f + a)) h (x + a) =
    (tileSlice F h x).image (fun f ↦ f + a)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:53; TranslationalTilings.slicingLCM_pos -/
namespace TranslationalTilings
axiom slicingLCM_pos (F : Finset Plane) (h : Plane) :
  0 < slicingLCM F h
end TranslationalTilings

/- blueprint/07-periodic-completion.md:56; TranslationalTilings.wedge_difference_dvd_slicingLCM -/
namespace TranslationalTilings
axiom wedge_difference_dvd_slicingLCM
    {f f' : Plane} (hf : f ∈ F) (hf' : f' ∈ F)
    (hwedge : wedge h (f - f') ≠ 0) :
  Int.natAbs (wedge h (f - f')) ∣ slicingLCM F h
end TranslationalTilings

/- blueprint/07-periodic-completion.md:61; TranslationalTilings.slicingLCM_bound -/
namespace TranslationalTilings
axiom slicingLCM_bound
    (F : Finset Plane) {h : Plane} (hprimitive : IsPrimitive h) :
  slicingLCM F h ≤
    (l1Norm h * l1Diameter F) ^ (F.card * (F.card - 1) / 2)
end TranslationalTilings

/- blueprint/07-periodic-completion.md:66; TranslationalTilings.mem_slicePattern -/
namespace TranslationalTilings
axiom mem_slicePattern
    {h : Plane} {line : Plane ⧸ directionSubgroup h} {A : Set Plane}
    (y : Plane) :
  y ∈ slicePattern h line A ↔
    y ∈ A ∧ QuotientAddGroup.mk' (directionSubgroup h) y = line
end TranslationalTilings

/- blueprint/07-periodic-completion.md:82; TranslationalTilings.slicing_lemma -/
namespace TranslationalTilings
axiom slicing_lemma
    {F : Finset Plane} {A : Set Plane} {ell k : ℕ} {h x : Plane}
    (hell : 0 < ell) (hk : 0 < k) (hh : IsPrimitive h)
    (hAperiod : Function.Periodic (setIndicator A)
      (((ell * k : ℕ) : ℤ) • h))
    (hconvperiod : ScalarPeriodic ell (tileConv F (setIndicator A))) :
  ScalarPeriodic
    (indicatorDilationModulus ell F.card * k * slicingLCM F h)
    (tileConv (tileSlice F h x) (setIndicator A))
end TranslationalTilings

/- blueprint/07-periodic-completion.md:93; TranslationalTilings.improve_onePeriodic -/
namespace TranslationalTilings
axiom improve_onePeriodic
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
end TranslationalTilings

/- blueprint/07-periodic-completion.md:132; TranslationalTilings.LinePattern -/
namespace TranslationalTilings
abbrev LinePattern (period : ℕ) := Fin period → Bool
end TranslationalTilings

/- blueprint/07-periodic-completion.md:134; TranslationalTilings.linePatternSetOfPos -/
namespace TranslationalTilings
def linePatternSetOfPos (period : ℕ) (hperiod : 0 < period)
    (P : LinePattern period) : Set ℤ :=
  {n | P ⟨n.natMod period, Int.natMod_lt hperiod.ne'⟩}
end TranslationalTilings
