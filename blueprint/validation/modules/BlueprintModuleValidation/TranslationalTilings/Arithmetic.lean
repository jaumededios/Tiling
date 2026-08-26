import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.NumberTheory.Primorial
import TranslationalTilings.Basic

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 d91153387a5765cc81db190413d07f5d2d1b59160689ee338cd9190f7f85256d  blueprint/02-lattice-geometry.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/02-lattice-geometry.md:39; TranslationalTilings.dilationModulus -/
namespace TranslationalTilings
def dilationModulus (ell oscillation tileCard : ℕ) : ℕ :=
  Nat.lcm ell (primorial (2 * oscillation * tileCard))
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:42; TranslationalTilings.indicatorDilationModulus -/
namespace TranslationalTilings
def indicatorDilationModulus (ell tileCard : ℕ) : ℕ :=
  dilationModulus ell 1 tileCard
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:45; TranslationalTilings.l1Norm -/
namespace TranslationalTilings
def l1Norm {d : ℕ} (x : Lattice d) : ℕ :=
  ∑ i, Int.natAbs (x i)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:48; TranslationalTilings.l1Diameter -/
namespace TranslationalTilings
def l1Diameter {d : ℕ} (F : Finset (Lattice d)) : ℕ :=
  (F ×ˢ F).sup fun xy ↦ l1Norm (xy.1 - xy.2)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:51; TranslationalTilings.euclideanNorm -/
namespace TranslationalTilings
noncomputable def euclideanNorm {d : ℕ} (x : Lattice d) : ℝ :=
  ‖(WithLp.toLp 2 (fun i : Fin d ↦ (x i : ℝ)) :
      EuclideanSpace ℝ (Fin d))‖
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:55; TranslationalTilings.euclideanDiameter -/
namespace TranslationalTilings
noncomputable def euclideanDiameter {d : ℕ}
    (F : Finset (Lattice d)) : ℝ :=
  if h : (F ×ˢ F).Nonempty then
    (F ×ˢ F).sup' h fun xy ↦ euclideanNorm (xy.1 - xy.2)
  else 0
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:71; TranslationalTilings.dilationModulus_pos -/
namespace TranslationalTilings
axiom dilationModulus_pos {ell oscillation tileCard : ℕ}
    (hell : 0 < ell) : 0 < dilationModulus ell oscillation tileCard
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:74; TranslationalTilings.ell_dvd_dilationModulus -/
namespace TranslationalTilings
axiom ell_dvd_dilationModulus (ell oscillation tileCard : ℕ) :
    ell ∣ dilationModulus ell oscillation tileCard
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:77; TranslationalTilings.prime_dvd_dilationModulus -/
namespace TranslationalTilings
axiom prime_dvd_dilationModulus {ell oscillation tileCard p : ℕ}
    (hp : p.Prime) (hpB : p ≤ 2 * oscillation * tileCard) :
    p ∣ dilationModulus ell oscillation tileCard
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:81; TranslationalTilings.prime_factor_gt_of_coprime_primorial -/
namespace TranslationalTilings
axiom prime_factor_gt_of_coprime_primorial {B r p : ℕ}
    (hr : Nat.Coprime r (primorial B))
    (hp : p.Prime) (hpr : p ∣ r) : B < p
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:85; TranslationalTilings.dilationModulus_le_explicit -/
namespace TranslationalTilings
axiom dilationModulus_le_explicit (ell oscillation tileCard : ℕ) :
    dilationModulus ell oscillation tileCard ≤
      ell * 4 ^ (2 * oscillation * tileCard)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:89; TranslationalTilings.l1Norm_eq_zero -/
namespace TranslationalTilings
axiom l1Norm_eq_zero {d : ℕ} {x : Lattice d} :
    l1Norm x = 0 ↔ x = 0
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:92; TranslationalTilings.l1Norm_neg -/
namespace TranslationalTilings
axiom l1Norm_neg {d : ℕ} (x : Lattice d) : l1Norm (-x) = l1Norm x
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:94; TranslationalTilings.l1Norm_add_le -/
namespace TranslationalTilings
axiom l1Norm_add_le {d : ℕ} (x y : Lattice d) :
    l1Norm (x + y) ≤ l1Norm x + l1Norm y
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:97; TranslationalTilings.l1Norm_sub_le -/
namespace TranslationalTilings
axiom l1Norm_sub_le {d : ℕ} (x y : Lattice d) :
    l1Norm (x - y) ≤ l1Norm x + l1Norm y
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:100; TranslationalTilings.l1Norm_zsmul -/
namespace TranslationalTilings
axiom l1Norm_zsmul {d : ℕ} (n : ℤ) (x : Lattice d) :
    l1Norm (n • x) = Int.natAbs n * l1Norm x
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:103; TranslationalTilings.mem_tile_norm_le_diameter -/
namespace TranslationalTilings
axiom mem_tile_norm_le_diameter {d : ℕ}
    {F : Finset (Lattice d)} (h0 : 0 ∈ F) {x : Lattice d} (hx : x ∈ F) :
    l1Norm x ≤ l1Diameter F
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:107; TranslationalTilings.euclideanNorm_le_l1Norm -/
namespace TranslationalTilings
axiom euclideanNorm_le_l1Norm {d : ℕ} (x : Lattice d) :
    euclideanNorm x ≤ (l1Norm x : ℝ)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:110; TranslationalTilings.euclideanNorm_zsmul -/
namespace TranslationalTilings
axiom euclideanNorm_zsmul {d : ℕ} (n : ℤ) (x : Lattice d) :
    euclideanNorm (n • x) = (Int.natAbs n : ℝ) * euclideanNorm x
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:113; TranslationalTilings.one_le_euclideanNorm -/
namespace TranslationalTilings
axiom one_le_euclideanNorm {d : ℕ} {x : Lattice d} (hx : x ≠ 0) :
    (1 : ℝ) ≤ euclideanNorm x
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:116; TranslationalTilings.l1Norm_le_sqrt_dim_mul_euclideanNorm -/
namespace TranslationalTilings
axiom l1Norm_le_sqrt_dim_mul_euclideanNorm {d : ℕ} (x : Lattice d) :
    (l1Norm x : ℝ) ≤ Real.sqrt d * euclideanNorm x
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:119; TranslationalTilings.euclideanDiameter_le_l1Diameter -/
namespace TranslationalTilings
axiom euclideanDiameter_le_l1Diameter {d : ℕ}
    (F : Finset (Lattice d)) :
    euclideanDiameter F ≤ l1Diameter F
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:123; TranslationalTilings.l1Diameter_le_sqrt_dim_mul_euclideanDiameter -/
namespace TranslationalTilings
axiom l1Diameter_le_sqrt_dim_mul_euclideanDiameter {d : ℕ}
    (F : Finset (Lattice d)) :
    (l1Diameter F : ℝ) ≤ Real.sqrt d * euclideanDiameter F
end TranslationalTilings
