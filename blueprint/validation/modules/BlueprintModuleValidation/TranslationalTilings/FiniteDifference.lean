import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.GroupTheory.Index
import TranslationalTilings.Basic

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 e7d56d0f7f8327fc2731cb5fb9d316f2bdf8262e86cfbb2e411268178c86777b  blueprint/01-foundations.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/01-foundations.md:247; TranslationalTilings.backwardDiff -/
namespace TranslationalTilings
def backwardDiff {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (h : G) (f : G → R) : G → R := fun x ↦ f x - f (x - h)
end TranslationalTilings

/- blueprint/01-foundations.md:250; TranslationalTilings.backwardDiffIter -/
namespace TranslationalTilings
def backwardDiffIter {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (h : G) (n : ℕ) (f : G → R) : G → R :=
  (backwardDiff h)^[n] f
end TranslationalTilings

/- blueprint/01-foundations.md:254; TranslationalTilings.lineRestriction -/
namespace TranslationalTilings
def lineRestriction {G R : Type*} [AddCommGroup G]
    (f : G → R) (x h : G) : ℤ → R := fun n ↦ f (x + n • h)
end TranslationalTilings

/- blueprint/01-foundations.md:257; TranslationalTilings.eliminationDirections -/
namespace TranslationalTilings
noncomputable def eliminationDirections
    {ι G : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup G]
    (target : ι) (e : G) (period : ι → G)
    (targetCoefficient : ι → ℤ) : List G :=
  (Finset.univ.erase target).toList.map fun i ↦
    e - targetCoefficient i • period target
end TranslationalTilings

/- blueprint/01-foundations.md:264; TranslationalTilings.applyDifferences -/
namespace TranslationalTilings
def applyDifferences {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (directions : List G) (f : G → R) : G → R :=
  directions.foldr backwardDiff f
end TranslationalTilings

/- blueprint/01-foundations.md:281; TranslationalTilings.backwardDiff_eq_fwdDiff -/
namespace TranslationalTilings
axiom backwardDiff_eq_fwdDiff {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (h : G) (f : G → R) :
    backwardDiff h f = fun x ↦ fwdDiff h f (x - h)
end TranslationalTilings

/- blueprint/01-foundations.md:285; TranslationalTilings.backwardDiff_add -/
namespace TranslationalTilings
axiom backwardDiff_add {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (h : G) (f g : G → R) :
    backwardDiff h (f + g) = backwardDiff h f + backwardDiff h g
end TranslationalTilings

/- blueprint/01-foundations.md:289; TranslationalTilings.backwardDiff_comm -/
namespace TranslationalTilings
axiom backwardDiff_comm {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (h k : G) (f : G → R) :
    backwardDiff h (backwardDiff k f) =
      backwardDiff k (backwardDiff h f)
end TranslationalTilings

/- blueprint/01-foundations.md:294; TranslationalTilings.backwardDiff_tileConv -/
namespace TranslationalTilings
axiom backwardDiff_tileConv {G R : Type*}
    [AddCommGroup G] [AddCommGroup R]
    (h : G) (F : Finset G) (f : G → R) :
    backwardDiff h (tileConv F f) = tileConv F (backwardDiff h f)
end TranslationalTilings

/- blueprint/01-foundations.md:299; TranslationalTilings.backwardDiff_eq_zero_of_periodic -/
namespace TranslationalTilings
axiom backwardDiff_eq_zero_of_periodic {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (h : G) (f : G → R)
    (hf : Function.Periodic f h) : backwardDiff h f = 0
end TranslationalTilings

/- blueprint/01-foundations.md:303; TranslationalTilings.backwardDiff_sub_period_eq -/
namespace TranslationalTilings
axiom backwardDiff_sub_period_eq {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (h k : G) (f : G → R)
    (hf : Function.Periodic f k) :
    backwardDiff (h + k) f = backwardDiff h f
end TranslationalTilings

/- blueprint/01-foundations.md:308; TranslationalTilings.lineRestriction_backwardDiff -/
namespace TranslationalTilings
axiom lineRestriction_backwardDiff {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (f : G → R) (x h : G) :
    lineRestriction (backwardDiff h f) x h =
      backwardDiff 1 (lineRestriction f x h)
end TranslationalTilings

/- blueprint/01-foundations.md:313; TranslationalTilings.bounded_of_backwardDiffIter_eq_zero_is_constant -/
namespace TranslationalTilings
axiom bounded_of_backwardDiffIter_eq_zero_is_constant
    (n : ℕ) (hn : 0 < n) (f : ℤ → ℤ)
    (hbounded : ∃ C : ℕ, ∀ z, Int.natAbs (f z) ≤ C)
    (hdiff : backwardDiffIter 1 n f = 0) : Function.Periodic f 1
end TranslationalTilings

/- blueprint/01-foundations.md:318; TranslationalTilings.bounded_real_of_backwardDiffIter_eq_zero_is_constant -/
namespace TranslationalTilings
axiom bounded_real_of_backwardDiffIter_eq_zero_is_constant
    (n : ℕ) (hn : 0 < n) (f : ℤ → ℝ)
    (hbounded : ∃ C : ℝ, ∀ z, |f z| ≤ C)
    (hdiff : backwardDiffIter 1 n f = 0) : Function.Periodic f 1
end TranslationalTilings

/- blueprint/01-foundations.md:323; TranslationalTilings.eliminate_periodic_summands -/
namespace TranslationalTilings
axiom eliminate_periodic_summands
    {ι G R : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] [AddCommGroup R]
    (target : ι) (lhs : G → R) (summand : ι → G → R)
    (e : G) (period : ι → G) (targetCoefficient : ι → ℤ)
    (decomp : lhs = ∑ i, summand i)
    (hperiod : ∀ i, Function.Periodic (summand i) (period i))
    (represent : ∀ i, i ≠ target → ∃ a : ℤ,
      e = a • period i + targetCoefficient i • period target) :
    applyDifferences
        (eliminationDirections target e period targetCoefficient) lhs =
      backwardDiffIter e (Fintype.card ι - 1) (summand target)
end TranslationalTilings
