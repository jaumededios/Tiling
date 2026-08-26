import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.FiniteDifference
import TranslationalTilings.LatticeGeometry

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 92c0160157ec728377e183ab0532869fce5ecf4553e103ac64917236f1ec6b68  blueprint/03-dilation-structure.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

open scoped symmDiff

/- blueprint/03-dilation-structure.md:28; TranslationalTilings.dilate -/
namespace TranslationalTilings
def dilate {d : ℕ} (r : ℕ)
    (F : Finset (Lattice d)) : Finset (Lattice d) :=
  F.image fun f ↦ (r : ℤ) • f
end TranslationalTilings

/- blueprint/03-dilation-structure.md:32; TranslationalTilings.BoundedBetween -/
namespace TranslationalTilings
def BoundedBetween {α : Type*} (lo hi : ℤ) (g : α → ℤ) : Prop :=
  ∀ x, lo ≤ g x ∧ g x ≤ hi
end TranslationalTilings

/- blueprint/03-dilation-structure.md:35; TranslationalTilings.IntegerBounded -/
namespace TranslationalTilings
def IntegerBounded {α : Type*} (g : α → ℤ) : Prop :=
  ∃ lo hi : ℤ, BoundedBetween lo hi g
end TranslationalTilings

/- blueprint/03-dilation-structure.md:38; TranslationalTilings.oscillationBound -/
namespace TranslationalTilings
def oscillationBound (lo hi : ℤ) : ℕ := Int.natAbs (hi - lo)
end TranslationalTilings

/- blueprint/03-dilation-structure.md:40; TranslationalTilings.centeredMultipleInterval -/
namespace TranslationalTilings
noncomputable def centeredMultipleInterval (ell R : ℕ) : Finset ℤ :=
  (Finset.Icc (-(R : ℤ)) R).image fun z ↦ (ell : ℤ) * z
end TranslationalTilings

/- blueprint/03-dilation-structure.md:43; TranslationalTilings.folnerBox -/
namespace TranslationalTilings
noncomputable def folnerBox {d : ℕ}
    (ell R : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset fun _ : Fin d ↦ centeredMultipleInterval ell R
end TranslationalTilings

/- blueprint/03-dilation-structure.md:47; TranslationalTilings.rayAverage -/
namespace TranslationalTilings
noncomputable def rayAverage {d : ℕ} (q N : ℕ) (f : Lattice d)
    (A : Set (Lattice d)) : Lattice d → ℚ :=
  fun x ↦ (N : ℚ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
    (setIndicator A (x - ((1 + n * q : ℕ) : ℤ) • f) : ℚ)
end TranslationalTilings

/- blueprint/03-dilation-structure.md:63; TranslationalTilings.dilate_zero -/
namespace TranslationalTilings
axiom dilate_zero {d : ℕ} {F : Finset (Lattice d)}
    (hF : F.Nonempty) : dilate 0 F = {0}
end TranslationalTilings

/- blueprint/03-dilation-structure.md:66; TranslationalTilings.dilate_zero_eq_empty_iff -/
namespace TranslationalTilings
axiom dilate_zero_eq_empty_iff {d : ℕ} (F : Finset (Lattice d)) :
    dilate 0 F = ∅ ↔ F = ∅
end TranslationalTilings

/- blueprint/03-dilation-structure.md:69; TranslationalTilings.dilate_one -/
namespace TranslationalTilings
axiom dilate_one {d : ℕ} (F : Finset (Lattice d)) : dilate 1 F = F
end TranslationalTilings

/- blueprint/03-dilation-structure.md:71; TranslationalTilings.dilate_mul -/
namespace TranslationalTilings
axiom dilate_mul {d r s : ℕ} (F : Finset (Lattice d)) :
    dilate r (dilate s F) = dilate (r * s) F
end TranslationalTilings

/- blueprint/03-dilation-structure.md:74; TranslationalTilings.card_dilate -/
namespace TranslationalTilings
axiom card_dilate {d r : ℕ} {F : Finset (Lattice d)} (hr : 0 < r) :
    (dilate r F).card = F.card
end TranslationalTilings

/- blueprint/03-dilation-structure.md:77; TranslationalTilings.tileMonoidAlgebra_frobenius_mod_prime -/
namespace TranslationalTilings
axiom tileMonoidAlgebra_frobenius_mod_prime
    {d p : ℕ} (F : Finset (Lattice d)) (hp : p.Prime) :
    tileMonoidAlgebra (ZMod p) (Lattice d) F ^ p =
      tileMonoidAlgebra (ZMod p) (Lattice d) (dilate p F)
end TranslationalTilings

/- blueprint/03-dilation-structure.md:82; TranslationalTilings.dilation_prime -/
namespace TranslationalTilings
axiom dilation_prime {d p : ℕ} {F : Finset (Lattice d)}
    {g : Lattice d → ℤ} {lo hi k : ℤ}
    (hbound : BoundedBetween lo hi g)
    (hconv : tileConv F g = fun _ ↦ k) (hp : p.Prime)
    (hlarge : oscillationBound lo hi * F.card < p) :
    tileConv (dilate p F) g = fun _ ↦ k
end TranslationalTilings

/- blueprint/03-dilation-structure.md:89; TranslationalTilings.dilation_coprime -/
namespace TranslationalTilings
axiom dilation_coprime {d r : ℕ} {F : Finset (Lattice d)}
    {g : Lattice d → ℤ} {lo hi k : ℤ}
    (hbound : BoundedBetween lo hi g)
    (hconv : tileConv F g = fun _ ↦ k) (hr : 0 < r)
    (hcop : Nat.Coprime r
      (primorial (oscillationBound lo hi * F.card))) :
    tileConv (dilate r F) g = fun _ ↦ k
end TranslationalTilings

/- blueprint/03-dilation-structure.md:97; TranslationalTilings.folnerBox_card -/
namespace TranslationalTilings
axiom folnerBox_card {d ell R : ℕ} (hell : 0 < ell) :
    (folnerBox (d := d) ell R).card = (2 * R + 1) ^ d
end TranslationalTilings

/- blueprint/03-dilation-structure.md:100; TranslationalTilings.folnerBox_translate_symmDiff_ratio_bound -/
namespace TranslationalTilings
axiom folnerBox_translate_symmDiff_ratio_bound
    {d ell : ℕ} {v : Lattice d} (hv : v ∈ scalarLattice ell) :
    ∃ C : ℕ, ∀ R,
      (folnerBox (d := d) ell R ∆
        (folnerBox (d := d) ell R).image (fun x ↦ x + v)).card *
          (2 * R + 1) ≤ C * (folnerBox (d := d) ell R).card
end TranslationalTilings

/- blueprint/03-dilation-structure.md:107; TranslationalTilings.dilation_periodic -/
namespace TranslationalTilings
axiom dilation_periodic {d ell r : ℕ}
    {F : Finset (Lattice d)} {g : Lattice d → ℤ} {lo hi : ℤ}
    (hbound : BoundedBetween lo hi g) (hell : 0 < ell)
    (hperiod : ScalarPeriodic ell (tileConv F g)) (hr : 0 < r)
    (hmod : Nat.ModEq
      (dilationModulus ell (oscillationBound lo hi) F.card) r 1) :
    tileConv (dilate r F) g = tileConv F g
end TranslationalTilings

/- blueprint/03-dilation-structure.md:115; TranslationalTilings.dilation_indicator_periodic -/
namespace TranslationalTilings
axiom dilation_indicator_periodic {d ell r : ℕ}
    {F : Finset (Lattice d)} {A : Set (Lattice d)}
    (hell : 0 < ell)
    (hperiod : ScalarPeriodic ell (tileConv F (setIndicator A)))
    (hr : 0 < r)
    (hmod : Nat.ModEq (indicatorDilationModulus ell F.card) r 1) :
    tileConv (dilate r F) (setIndicator A) =
      tileConv F (setIndicator A)
end TranslationalTilings
