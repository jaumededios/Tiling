import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.NumberTheory.Real.Irrational
import TranslationalTilings.Basic
import TranslationalTilings.FiniteDifference
import TranslationalTilings.LatticeGeometry

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 e32144c83de089ff1743447cbb776dd5c5eccc1fc0fbf79aaa2de32ede10e9ad  blueprint/04-counterexample.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/04-counterexample.md:39; TranslationalTilings.Counterexample.alpha -/
namespace TranslationalTilings.Counterexample
noncomputable def alpha : ℝ := Real.sqrt 2
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:41; TranslationalTilings.Counterexample.chi -/
namespace TranslationalTilings.Counterexample
def chi (x : Plane) : ℤ :=
  (-1) ^ Int.natAbs (x 1 / 2 + x 0)
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:44; TranslationalTilings.Counterexample.carry -/
namespace TranslationalTilings.Counterexample
noncomputable def carry (x : Plane) : ℤ :=
  Int.floor (alpha * ((x 0 + x 1 : ℤ) : ℝ)) -
    Int.floor (alpha * (x 0 : ℝ)) -
    Int.floor (alpha * (x 1 : ℝ))
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:49; TranslationalTilings.Counterexample.counterexampleSet -/
namespace TranslationalTilings.Counterexample
noncomputable def counterexampleSet : Set Plane :=
  {x | if chi x = 1 then carry x = 1 else carry x = 0}
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:52; TranslationalTilings.Counterexample.v₁ -/
namespace TranslationalTilings.Counterexample
def v₁ : Plane := ![0, 2]
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:53; TranslationalTilings.Counterexample.v₂ -/
namespace TranslationalTilings.Counterexample
def v₂ : Plane := ![1, 0]
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:54; TranslationalTilings.Counterexample.v₃ -/
namespace TranslationalTilings.Counterexample
def v₃ : Plane := ![2, -2]
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:56; TranslationalTilings.Counterexample.counterexampleTile -/
namespace TranslationalTilings.Counterexample
def counterexampleTile : Finset Plane :=
  (Finset.univ : Finset (Fin 3 → Bool)).image fun t ↦
    (if t 0 then v₁ else 0) +
    (if t 1 then v₂ else 0) +
    (if t 2 then v₃ else 0)
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:74; TranslationalTilings.Counterexample.irrational_alpha -/
namespace TranslationalTilings.Counterexample
axiom irrational_alpha : Irrational alpha
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:76; TranslationalTilings.Counterexample.chi_eq_formula -/
namespace TranslationalTilings.Counterexample
axiom chi_eq_formula (m₁ m₂ : ℤ) :
    chi ![m₁, m₂] = (-1) ^ Int.natAbs (m₂ / 2 + m₁)
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:79; TranslationalTilings.Counterexample.chi_mem -/
namespace TranslationalTilings.Counterexample
axiom chi_mem (x : Plane) : chi x = -1 ∨ chi x = 1
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:81; TranslationalTilings.Counterexample.chi_scalarPeriodic_four -/
namespace TranslationalTilings.Counterexample
axiom chi_scalarPeriodic_four : ScalarPeriodic 4 chi
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:83; TranslationalTilings.Counterexample.chi_cancel_vertical -/
namespace TranslationalTilings.Counterexample
axiom chi_cancel_vertical : tileConv {0, v₁} chi = 0
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:85; TranslationalTilings.Counterexample.chi_cancel_horizontal -/
namespace TranslationalTilings.Counterexample
axiom chi_cancel_horizontal : tileConv {0, v₂} chi = 0
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:87; TranslationalTilings.Counterexample.chi_cancel_diagonal -/
namespace TranslationalTilings.Counterexample
axiom chi_cancel_diagonal : tileConv {0, v₃} chi = 0
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:90; TranslationalTilings.Counterexample.chi_lemma -/
namespace TranslationalTilings.Counterexample
axiom chi_lemma :
    ScalarPeriodic 4 chi ∧
      (∀ x, chi x = -1 ∨ chi x = 1) ∧
      tileConv {0, v₁} chi = 0 ∧ tileConv {0, v₂} chi = 0
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:95; TranslationalTilings.Counterexample.carry_zero_or_one -/
namespace TranslationalTilings.Counterexample
axiom carry_zero_or_one (x : Plane) : carry x = 0 ∨ carry x = 1
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:97; TranslationalTilings.Counterexample.carry_eq_fract -/
namespace TranslationalTilings.Counterexample
axiom carry_eq_fract (x : Plane) :
    (carry x : ℝ) =
      Int.fract (alpha * (x 0 : ℝ)) +
      Int.fract (alpha * (x 1 : ℝ)) -
      Int.fract (alpha * ((x 0 + x 1 : ℤ) : ℝ))
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:103; TranslationalTilings.Counterexample.indicator_counterexampleSet -/
namespace TranslationalTilings.Counterexample
axiom indicator_counterexampleSet (x : Plane) :
    ((setIndicator counterexampleSet x : ℤ) : ℝ) =
      (chi x : ℝ) *
        (Int.fract (alpha * (x 0 : ℝ)) +
          Int.fract (alpha * (x 1 : ℝ)) -
          Int.fract (alpha * ((x 0 + x 1 : ℤ) : ℝ)) -
          (1 / 2 : ℝ)) + (1 / 2 : ℝ)
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:111; TranslationalTilings.Counterexample.counterexampleTile_card -/
namespace TranslationalTilings.Counterexample
axiom counterexampleTile_card : counterexampleTile.card = 8
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:113; TranslationalTilings.Counterexample.counterexampleTile_indicator_factorization -/
namespace TranslationalTilings.Counterexample
axiom counterexampleTile_indicator_factorization :
    tileMonoidAlgebra ℤ Plane counterexampleTile =
      tileMonoidAlgebra ℤ Plane {0, v₁} *
        tileMonoidAlgebra ℤ Plane {0, v₂} *
        tileMonoidAlgebra ℤ Plane {0, v₃}
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:119; TranslationalTilings.Counterexample.counterexample_tiles_level_four -/
namespace TranslationalTilings.Counterexample
axiom counterexample_tiles_level_four :
    TilesAtLevel counterexampleTile counterexampleSet Set.univ 4
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:122; TranslationalTilings.Counterexample.irrational_fract_range_infinite -/
namespace TranslationalTilings.Counterexample
axiom irrational_fract_range_infinite {β : ℝ} (hβ : Irrational β) :
    Set.Infinite (Set.range fun n : ℤ ↦ Int.fract (β * n))
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:125; TranslationalTilings.Counterexample.counterexample_not_weaklyPeriodic -/
namespace TranslationalTilings.Counterexample
axiom counterexample_not_weaklyPeriodic :
    ¬ WeaklyPeriodic counterexampleSet
end TranslationalTilings.Counterexample

/- blueprint/04-counterexample.md:129; TranslationalTilings.Counterexample.exists_eight_element_level_four_not_weaklyPeriodic -/
namespace TranslationalTilings.Counterexample
axiom exists_eight_element_level_four_not_weaklyPeriodic :
    ∃ (F : Finset Plane) (A : Set Plane),
      F.card = 8 ∧ TilesAtLevel F A Set.univ 4 ∧ ¬ WeaklyPeriodic A
end TranslationalTilings.Counterexample
