import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.NumberTheory.Primorial
import TranslationalTilings.Arithmetic

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 d91153387a5765cc81db190413d07f5d2d1b59160689ee338cd9190f7f85256d  blueprint/02-lattice-geometry.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/02-lattice-geometry.md:138; TranslationalTilings.wedge -/
namespace TranslationalTilings
def wedge (u v : Plane) : ℤ := u 0 * v 1 - u 1 * v 0
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:140; TranslationalTilings.Commensurable -/
namespace TranslationalTilings
def Commensurable {d : ℕ} (u v : Lattice d) : Prop :=
  ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • u = b • v
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:143; TranslationalTilings.PairwiseIncommensurable -/
namespace TranslationalTilings
def PairwiseIncommensurable {d m : ℕ}
    (h : Fin m → Lattice d) : Prop :=
  ∀ i j, i ≠ j → ¬ Commensurable (h i) (h j)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:147; TranslationalTilings.generatedPair -/
namespace TranslationalTilings
def generatedPair (u v : Plane) : AddSubgroup Plane :=
  AddSubgroup.closure ({u, v} : Set Plane)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:150; TranslationalTilings.scalarLattice -/
namespace TranslationalTilings
def scalarLattice {d : ℕ} (q : ℕ) : AddSubgroup (Lattice d) :=
  (nsmulAddMonoidHom q).range
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:153; TranslationalTilings.vectorContent -/
namespace TranslationalTilings
def vectorContent {d : ℕ} (h : Lattice d) : ℕ :=
  (Finset.univ : Finset (Fin d)).gcd fun i ↦ Int.natAbs (h i)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:156; TranslationalTilings.primitivePart -/
namespace TranslationalTilings
def primitivePart {d : ℕ} (h : Lattice d) : Lattice d :=
  if h = 0 then 0 else fun i ↦ h i / (vectorContent h : ℤ)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:159; TranslationalTilings.IsPrimitive -/
namespace TranslationalTilings
def IsPrimitive {d : ℕ} (h : Lattice d) : Prop :=
  h ≠ 0 ∧ vectorContent h = 1
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:162; TranslationalTilings.slopeVector -/
namespace TranslationalTilings
def slopeVector (t : ℕ) : Plane := ![(1 : ℤ), (t : ℤ)]
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:164; TranslationalTilings.avoidsDirections -/
namespace TranslationalTilings
def avoidsDirections (h : Fin m → Plane) (t : ℕ) : Bool :=
  decide (∀ i, wedge (slopeVector t) (h i) ≠ 0)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:167; TranslationalTilings.avoidanceSlope -/
namespace TranslationalTilings
def avoidanceSlope (h : Fin m → Plane) : ℕ :=
  ((List.range (m + 1)).find? (avoidsDirections h)).getD 0
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:170; TranslationalTilings.avoidanceVector -/
namespace TranslationalTilings
def avoidanceVector (h : Fin m → Plane) : Plane :=
  slopeVector (avoidanceSlope h)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:173; TranslationalTilings.unorderedPairs -/
namespace TranslationalTilings
def unorderedPairs (m : ℕ) : Finset (Fin m × Fin m) :=
  Finset.univ.offDiag.filter fun ij ↦ ij.1 < ij.2
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:176; TranslationalTilings.pairWedgeLCM -/
namespace TranslationalTilings
def pairWedgeLCM {m : ℕ} (h : Fin m → Plane) : ℕ :=
  (unorderedPairs m).lcm fun ij ↦
    Int.natAbs (wedge (h ij.1) (h ij.2))
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:200; TranslationalTilings.wedge_zero_left -/
namespace TranslationalTilings
axiom wedge_zero_left (v : Plane) : wedge 0 v = 0
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:201; TranslationalTilings.wedge_zero_right -/
namespace TranslationalTilings
axiom wedge_zero_right (u : Plane) : wedge u 0 = 0
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:202; TranslationalTilings.wedge_add_left -/
namespace TranslationalTilings
axiom wedge_add_left (u v w : Plane) :
    wedge (u + v) w = wedge u w + wedge v w
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:204; TranslationalTilings.wedge_add_right -/
namespace TranslationalTilings
axiom wedge_add_right (u v w : Plane) :
    wedge u (v + w) = wedge u v + wedge u w
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:206; TranslationalTilings.wedge_swap -/
namespace TranslationalTilings
axiom wedge_swap (u v : Plane) : wedge u v = -wedge v u
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:207; TranslationalTilings.wedge_zsmul_left -/
namespace TranslationalTilings
axiom wedge_zsmul_left (n : ℤ) (u v : Plane) :
    wedge (n • u) v = n * wedge u v
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:209; TranslationalTilings.wedge_zsmul_right -/
namespace TranslationalTilings
axiom wedge_zsmul_right (n : ℤ) (u v : Plane) :
    wedge u (n • v) = n * wedge u v
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:212; TranslationalTilings.commensurable_iff_wedge_eq_zero -/
namespace TranslationalTilings
axiom commensurable_iff_wedge_eq_zero {u v : Plane}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    Commensurable u v ↔ wedge u v = 0
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:216; TranslationalTilings.cramer_identity -/
namespace TranslationalTilings
axiom cramer_identity (u v x : Plane) :
    (wedge u v) • x = wedge x v • u + wedge u x • v
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:219; TranslationalTilings.scalarLattice_natAbs_wedge_le_generatedPair -/
namespace TranslationalTilings
axiom scalarLattice_natAbs_wedge_le_generatedPair (u v : Plane) :
    scalarLattice (Int.natAbs (wedge u v)) ≤ generatedPair u v
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:222; TranslationalTilings.index_generatedPair -/
namespace TranslationalTilings
axiom index_generatedPair {u v : Plane} (hdet : wedge u v ≠ 0) :
    (generatedPair u v).index = Int.natAbs (wedge u v)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:225; TranslationalTilings.natAbs_wedge_le_l1Norm_mul_l1Norm -/
namespace TranslationalTilings
axiom natAbs_wedge_le_l1Norm_mul_l1Norm (u v : Plane) :
    Int.natAbs (wedge u v) ≤ l1Norm u * l1Norm v
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:228; TranslationalTilings.abs_wedge_le_euclideanNorm_mul_euclideanNorm -/
namespace TranslationalTilings
axiom abs_wedge_le_euclideanNorm_mul_euclideanNorm (u v : Plane) :
    |(wedge u v : ℝ)| ≤ euclideanNorm u * euclideanNorm v
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:231; TranslationalTilings.scalarLattice_mono_dvd -/
namespace TranslationalTilings
axiom scalarLattice_mono_dvd {d m n : ℕ} (h : m ∣ n) :
    scalarLattice (d := d) n ≤ scalarLattice m
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:234; TranslationalTilings.scalarLattice_index -/
namespace TranslationalTilings
axiom scalarLattice_index (d q : ℕ) :
    (scalarLattice (d := d) q).index = q ^ d
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:237; TranslationalTilings.vectorContent_pos -/
namespace TranslationalTilings
axiom vectorContent_pos {d : ℕ} {h : Lattice d} (hh : h ≠ 0) :
  0 < vectorContent h
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:240; TranslationalTilings.vectorContent_dvd_coord -/
namespace TranslationalTilings
axiom vectorContent_dvd_coord {d : ℕ} (h : Lattice d) (i : Fin d) :
    (vectorContent h : ℤ) ∣ h i
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:243; TranslationalTilings.primitive_decomposition -/
namespace TranslationalTilings
axiom primitive_decomposition {d : ℕ} {h : Lattice d} (hh : h ≠ 0) :
    (vectorContent h : ℤ) • primitivePart h = h ∧
      IsPrimitive (primitivePart h)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:247; TranslationalTilings.primitive_decomposition_unique -/
namespace TranslationalTilings
axiom primitive_decomposition_unique {d : ℕ}
    {h v : Lattice d} {k : ℕ}
    (hh : h ≠ 0) (hk : 0 < k) (hv : IsPrimitive v)
    (hdecomp : h = (k : ℤ) • v) :
    k = vectorContent h ∧ v = primitivePart h
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:253; TranslationalTilings.primitive_bezout -/
namespace TranslationalTilings
axiom primitive_bezout {d : ℕ} {v : Lattice d}
    (hv : IsPrimitive v) :
  ∃ a : Lattice d, ∑ i, a i * v i = 1
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:257; TranslationalTilings.integer_multiple_of_primitive_of_commensurable -/
namespace TranslationalTilings
axiom integer_multiple_of_primitive_of_commensurable
    {d : ℕ} {u v : Lattice d} (hu : u ≠ 0)
    (hv : IsPrimitive v) (huv : Commensurable u v) :
  ∃ z : ℤ, z ≠ 0 ∧ u = z • v
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:262; TranslationalTilings.exists_commonMultiple_of_pairwise_commensurable -/
namespace TranslationalTilings
axiom exists_commonMultiple_of_pairwise_commensurable
    {d : ℕ} {C : Finset (Lattice d)} (hC : C.Nonempty)
    (hne : ∀ f ∈ C, f ≠ 0)
    (hcomm : ∀ u ∈ C, ∀ v ∈ C, Commensurable u v) :
  ∃ h : Lattice d,
    h ≠ 0 ∧
    (∀ f ∈ C, ∃ z : ℤ, z ≠ 0 ∧ h = z • f) ∧
    l1Norm h ≤ ∏ f ∈ C, l1Norm f ∧
    euclideanNorm h ≤ ∏ f ∈ C, euclideanNorm f
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:272; TranslationalTilings.exists_SL2Z_send_primitive_to_e0 -/
namespace TranslationalTilings
axiom exists_SL2Z_send_primitive_to_e0 {h : Plane}
    (hh : IsPrimitive h) :
    ∃ e : Plane ≃ₗ[ℤ] Plane,
      LinearMap.det e.toLinearMap = 1 ∧ e h = ![1, 0]
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:277; TranslationalTilings.avoidanceVector_spec -/
namespace TranslationalTilings
axiom avoidanceVector_spec {m : ℕ} {h : Fin m → Plane}
    (hne : ∀ i, h i ≠ 0) :
    avoidanceVector h ≠ 0 ∧
      (∀ i, ¬ Commensurable (avoidanceVector h) (h i)) ∧
      l1Norm (avoidanceVector h) ≤ m + 1
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:283; TranslationalTilings.pairWedgeLCM_pos -/
namespace TranslationalTilings
axiom pairWedgeLCM_pos {m : ℕ} {h : Fin m → Plane}
    (hne : ∀ i, h i ≠ 0) (hpair : PairwiseIncommensurable h) :
    0 < pairWedgeLCM h
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:287; TranslationalTilings.pairWedgeLCM_scalarLattice_le -/
namespace TranslationalTilings
axiom pairWedgeLCM_scalarLattice_le {m : ℕ}
    {h : Fin m → Plane} (hne : ∀ i, h i ≠ 0)
    (hpair : PairwiseIncommensurable h) {i j : Fin m} (hij : i ≠ j) :
    scalarLattice (pairWedgeLCM h) ≤ generatedPair (h i) (h j)
end TranslationalTilings

/- blueprint/02-lattice-geometry.md:292; TranslationalTilings.pairWedgeLCM_bound -/
namespace TranslationalTilings
axiom pairWedgeLCM_bound {m : ℕ} {h : Fin m → Plane}
    (hne : ∀ i, h i ≠ 0) (hpair : PairwiseIncommensurable h) :
    pairWedgeLCM h ≤ ∏ i, l1Norm (h i) ^ (m - 1)
end TranslationalTilings
