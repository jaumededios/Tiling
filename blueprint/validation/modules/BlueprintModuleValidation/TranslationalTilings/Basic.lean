import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.GroupTheory.Index

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 e7d56d0f7f8327fc2731cb5fb9d316f2bdf8262e86cfbb2e411268178c86777b  blueprint/01-foundations.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/01-foundations.md:68; TranslationalTilings.Lattice -/
namespace TranslationalTilings
abbrev Lattice (d : ℕ) := Fin d → ℤ
end TranslationalTilings

/- blueprint/01-foundations.md:69; TranslationalTilings.Plane -/
namespace TranslationalTilings
abbrev Plane := Lattice 2
end TranslationalTilings

/- blueprint/01-foundations.md:71; TranslationalTilings.setIndicator -/
namespace TranslationalTilings
noncomputable def setIndicator {G : Type*} (A : Set G) : G → ℤ :=
  A.indicator (fun _ ↦ 1)
end TranslationalTilings

/- blueprint/01-foundations.md:74; TranslationalTilings.tileMonoidAlgebra -/
namespace TranslationalTilings
noncomputable def tileMonoidAlgebra (R G : Type*) [Semiring R]
    [AddCommMonoid G] (F : Finset G) : AddMonoidAlgebra R G :=
  ∑ f ∈ F, AddMonoidAlgebra.single f (1 : R)
end TranslationalTilings

/- blueprint/01-foundations.md:78; TranslationalTilings.tileConv -/
namespace TranslationalTilings
def tileConv {G R : Type*} [AddCommGroup G] [AddCommMonoid R]
    (F : Finset G) (g : G → R) (x : G) : R :=
  ∑ f ∈ F, g (x - f)
end TranslationalTilings

/- blueprint/01-foundations.md:82; TranslationalTilings.TilesAtLevel -/
namespace TranslationalTilings
def TilesAtLevel {G : Type*} [AddCommGroup G]
    (F : Finset G) (A E : Set G) (k : ℕ) : Prop :=
  ∀ x, tileConv F (setIndicator A) x = (k : ℤ) * setIndicator E x
end TranslationalTilings

/- blueprint/01-foundations.md:86; TranslationalTilings.Tiles -/
namespace TranslationalTilings
def Tiles {G : Type*} [AddCommGroup G]
    (F : Finset G) (A E : Set G) : Prop :=
  TilesAtLevel F A E 1
end TranslationalTilings

/- blueprint/01-foundations.md:90; TranslationalTilings.TilesUniverse -/
namespace TranslationalTilings
def TilesUniverse {G : Type*} [AddCommGroup G]
    (F : Finset G) (A : Set G) : Prop := Tiles F A Set.univ
end TranslationalTilings

/- blueprint/01-foundations.md:93; TranslationalTilings.PeriodicOn -/
namespace TranslationalTilings
def PeriodicOn {G R : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (f : G → R) : Prop :=
  ∀ h ∈ H, Function.Periodic f h
end TranslationalTilings

/- blueprint/01-foundations.md:97; TranslationalTilings.ScalarPeriodic -/
namespace TranslationalTilings
def ScalarPeriodic {d : ℕ} {R : Type*}
    (q : ℕ) (f : Lattice d → R) : Prop :=
  ∀ x z, f (x + (q : ℤ) • z) = f x
end TranslationalTilings

/- blueprint/01-foundations.md:101; TranslationalTilings.SetPeriodicOn -/
namespace TranslationalTilings
def SetPeriodicOn {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (A : Set G) : Prop :=
  ∀ h ∈ H, ∀ x, x + h ∈ A ↔ x ∈ A
end TranslationalTilings

/- blueprint/01-foundations.md:105; TranslationalTilings.SetScalarPeriodic -/
namespace TranslationalTilings
def SetScalarPeriodic {d : ℕ} (q : ℕ) (A : Set (Lattice d)) : Prop :=
  ∀ x z, x + (q : ℤ) • z ∈ A ↔ x ∈ A
end TranslationalTilings

/- blueprint/01-foundations.md:108; TranslationalTilings.IsPeriodic -/
namespace TranslationalTilings
def IsPeriodic {d : ℕ} (A : Set (Lattice d)) : Prop :=
  ∃ H : AddSubgroup (Lattice d),
    Finite ((Lattice d) ⧸ H) ∧ SetPeriodicOn H A
end TranslationalTilings

/- blueprint/01-foundations.md:112; TranslationalTilings.addCoset -/
namespace TranslationalTilings
def addCoset {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (x : G) : Set G := {y | y - x ∈ H}
end TranslationalTilings

/- blueprint/01-foundations.md:115; TranslationalTilings.quotientCoset -/
namespace TranslationalTilings
def quotientCoset {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (c : G ⧸ H) : Set G :=
  {x | QuotientAddGroup.mk' H x = c}
end TranslationalTilings

/- blueprint/01-foundations.md:119; TranslationalTilings.translateSet -/
namespace TranslationalTilings
def translateSet {G : Type*} [AddCommGroup G]
    (t : G) (A : Set G) : Set G := {x | x - t ∈ A}
end TranslationalTilings

/- blueprint/01-foundations.md:122; TranslationalTilings.WeakPeriodicDecomposition -/
namespace TranslationalTilings
structure WeakPeriodicDecomposition (A : Set Plane) where
  numberOfParts : ℕ
  part : Fin numberOfParts → Set Plane
  period : Fin numberOfParts → Plane
  period_ne_zero : ∀ i, period i ≠ 0
  periodic_part : ∀ i, ∀ x, x + period i ∈ part i ↔ x ∈ part i
  pairwiseDisjoint : Set.PairwiseDisjoint Set.univ part
  iUnion_parts : (⋃ i, part i) = A
end TranslationalTilings

/- blueprint/01-foundations.md:131; TranslationalTilings.WeaklyPeriodic -/
namespace TranslationalTilings
def WeaklyPeriodic (A : Set Plane) : Prop :=
  Nonempty (WeakPeriodicDecomposition A)
end TranslationalTilings

/- blueprint/01-foundations.md:134; TranslationalTilings.OnePeriodic -/
namespace TranslationalTilings
def OnePeriodic (A : Set Plane) : Prop :=
  ∃ h : Plane, h ≠ 0 ∧ ∀ x, x + h ∈ A ↔ x ∈ A
end TranslationalTilings

/- blueprint/01-foundations.md:137; TranslationalTilings.CosetwisePeriodic -/
namespace TranslationalTilings
def CosetwisePeriodic (A : Set Plane) (Λ : AddSubgroup Plane)
    {m : ℕ} (periods : Fin m → Plane) : Prop :=
  ∀ x, ∃ j, ∀ y,
    y + periods j ∈ A ∩ addCoset Λ x ↔ y ∈ A ∩ addCoset Λ x
end TranslationalTilings

/- blueprint/01-foundations.md:153; TranslationalTilings.tileConv_apply -/
namespace TranslationalTilings
axiom tileConv_apply {G R : Type*} [AddCommGroup G] [AddCommMonoid R]
    (F : Finset G) (g : G → R) (x : G) :
    tileConv F g x = ∑ f ∈ F, g (x - f)
end TranslationalTilings

/- blueprint/01-foundations.md:157; TranslationalTilings.tileConv_zero -/
namespace TranslationalTilings
axiom tileConv_zero {G R : Type*} [AddCommGroup G] [AddCommMonoid R]
    (F : Finset G) : tileConv F (0 : G → R) = 0
end TranslationalTilings

/- blueprint/01-foundations.md:160; TranslationalTilings.tileConv_add -/
namespace TranslationalTilings
axiom tileConv_add {G R : Type*} [AddCommGroup G] [AddCommMonoid R]
    (F : Finset G) (g h : G → R) :
    tileConv F (g + h) = tileConv F g + tileConv F h
end TranslationalTilings

/- blueprint/01-foundations.md:164; TranslationalTilings.tileConv_sub -/
namespace TranslationalTilings
axiom tileConv_sub {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (F : Finset G) (g h : G → R) :
    tileConv F (g - h) = tileConv F g - tileConv F h
end TranslationalTilings

/- blueprint/01-foundations.md:168; TranslationalTilings.tileConv_smul -/
namespace TranslationalTilings
axiom tileConv_smul {G R S : Type*} [AddCommGroup G]
    [Semiring S] [AddCommMonoid R] [Module S R]
    (F : Finset G) (c : S) (g : G → R) :
    tileConv F (c • g) = c • tileConv F g
end TranslationalTilings

/- blueprint/01-foundations.md:173; TranslationalTilings.tileConv_translate -/
namespace TranslationalTilings
axiom tileConv_translate {G R : Type*} [AddCommGroup G] [AddCommMonoid R]
    (F : Finset G) (g : G → R) (a : G) :
    tileConv F (fun y ↦ g (y - a)) = fun x ↦ tileConv F g (x - a)
end TranslationalTilings

/- blueprint/01-foundations.md:177; TranslationalTilings.tileConv_indicator_eq_card -/
namespace TranslationalTilings
axiom tileConv_indicator_eq_card {G : Type*} [AddCommGroup G]
    (F : Finset G) (A : Set G) (x : G) :
    tileConv F (setIndicator A) x =
      ((@Finset.filter G (fun f ↦ x - f ∈ A)
        (fun _ ↦ Classical.propDecidable _) F).card : ℤ)
end TranslationalTilings

/- blueprint/01-foundations.md:183; TranslationalTilings.tilesAtLevel_iff_representation_count -/
namespace TranslationalTilings
axiom tilesAtLevel_iff_representation_count
    {G : Type*} [AddCommGroup G]
    (F : Finset G) (A E : Set G) (k : ℕ) :
  TilesAtLevel F A E k ↔ ∀ x,
      (@Finset.filter G (fun f ↦ x - f ∈ A)
        (fun _ ↦ Classical.propDecidable _) F).card =
          @ite ℕ (x ∈ E) (Classical.propDecidable _) k 0
end TranslationalTilings

/- blueprint/01-foundations.md:191; TranslationalTilings.periodicOn_mono -/
namespace TranslationalTilings
axiom periodicOn_mono {G R : Type*} [AddCommGroup G]
    {H K : AddSubgroup G} {f : G → R}
    (hHK : H ≤ K) (hf : PeriodicOn K f) : PeriodicOn H f
end TranslationalTilings

/- blueprint/01-foundations.md:195; TranslationalTilings.setPeriodicOn_iff_indicator -/
namespace TranslationalTilings
axiom setPeriodicOn_iff_indicator {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (A : Set G) :
    SetPeriodicOn H A ↔ PeriodicOn H (setIndicator A)
end TranslationalTilings

/- blueprint/01-foundations.md:199; TranslationalTilings.setScalarPeriodic_iff_membership -/
namespace TranslationalTilings
axiom setScalarPeriodic_iff_membership {d : ℕ}
    (q : ℕ) (A : Set (Lattice d)) :
    SetScalarPeriodic q A ↔ ∀ x z,
      x + (q : ℤ) • z ∈ A ↔ x ∈ A
end TranslationalTilings

/- blueprint/01-foundations.md:204; TranslationalTilings.finiteIndex_periodic_scalarPeriodic -/
namespace TranslationalTilings
axiom finiteIndex_periodic_scalarPeriodic {d : ℕ} {R : Type*}
    (H : AddSubgroup (Lattice d)) (f : Lattice d → R)
    [Finite ((Lattice d) ⧸ H)] (hf : PeriodicOn H f) :
    ScalarPeriodic H.index f
end TranslationalTilings

/- blueprint/01-foundations.md:209; TranslationalTilings.quotientCoset_pairwiseDisjoint -/
namespace TranslationalTilings
axiom quotientCoset_pairwiseDisjoint {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) :
    Set.PairwiseDisjoint Set.univ (quotientCoset H)
end TranslationalTilings

/- blueprint/01-foundations.md:213; TranslationalTilings.iUnion_quotientCoset -/
namespace TranslationalTilings
axiom iUnion_quotientCoset {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) : (⋃ c, quotientCoset H c) = Set.univ
end TranslationalTilings

/- blueprint/01-foundations.md:216; TranslationalTilings.weaklyPeriodic_of_cosetwise -/
namespace TranslationalTilings
axiom weaklyPeriodic_of_cosetwise (A : Set Plane)
    (Λ : AddSubgroup Plane) {m : ℕ} (periods : Fin m → Plane)
    [Finite (Plane ⧸ Λ)] (hm : 0 < m)
    (hne : ∀ j, periods j ≠ 0) (hmem : ∀ j, periods j ∈ Λ)
    (hA : CosetwisePeriodic A Λ periods) : WeaklyPeriodic A
end TranslationalTilings

/- blueprint/01-foundations.md:222; TranslationalTilings.tiles_translate_tile -/
namespace TranslationalTilings
axiom tiles_translate_tile {G : Type*} [AddCommGroup G]
    (F : Finset G) (A E : Set G) (k : ℕ) (t : G) :
  TilesAtLevel F A E k ↔
      TilesAtLevel
        (@Finset.image G G (Classical.decEq G) (fun f ↦ f - t) F)
        (translateSet t A) E k
end TranslationalTilings
