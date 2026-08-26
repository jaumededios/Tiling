# Arithmetic, norms, and lattice geometry

Target modules are `TranslationalTilings.Arithmetic` and
`TranslationalTilings.LatticeGeometry`.  Acceptance is checked only through
the strict dependency-ordered artifact
`blueprint/validation/BlueprintIntegrated.lean` and its generated declaration
coverage ledger.  `tmp/BlueprintGeometry.lean` is a chapter-local diagnostic;
it cannot establish cross-chapter integration or acceptance.

```lean
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.NumberTheory.Primorial
import TranslationalTilings.Basic
```

## Reused Mathlib arithmetic

The project does not define its own finite LCM or prime product.  It uses:

- `Finset.lcm`, `Finset.dvd_lcm`, `Finset.lcm_dvd`,
  `Finset.lcm_eq_zero_iff`, and `Finset.lcm_dvd_prod`;
- the root declaration `primorial`, together with `primorial_pos`,
  `Nat.Prime.dvd_primorial_iff`, and `primorial_lt_four_pow`;
- `AddSubgroup.index_range_nsmul` for scalar-lattice indices;
- `Matrix.mulVec_cramer` as the generic Cramer identity behind the concrete
  two-dimensional wedge formula.

This removes two duplicated APIs from the rejected snapshot.

## Arithmetic and metric definitions

```lean
namespace TranslationalTilings

def dilationModulus (ell oscillation tileCard : ℕ) : ℕ :=
  Nat.lcm ell (primorial (2 * oscillation * tileCard))

def indicatorDilationModulus (ell tileCard : ℕ) : ℕ :=
  dilationModulus ell 1 tileCard

def l1Norm {d : ℕ} (x : Lattice d) : ℕ :=
  ∑ i, Int.natAbs (x i)

def l1Diameter {d : ℕ} (F : Finset (Lattice d)) : ℕ :=
  (F ×ˢ F).sup fun xy ↦ l1Norm (xy.1 - xy.2)

noncomputable def euclideanNorm {d : ℕ} (x : Lattice d) : ℝ :=
  ‖(WithLp.toLp 2 (fun i : Fin d ↦ (x i : ℝ)) :
      EuclideanSpace ℝ (Fin d))‖

noncomputable def euclideanDiameter {d : ℕ}
    (F : Finset (Lattice d)) : ℝ :=
  if h : (F ×ˢ F).Nonempty then
    (F ×ˢ F).sup' h fun xy ↦ euclideanNorm (xy.1 - xy.2)
  else 0

end TranslationalTilings
```

The explicit `PiLp 2` coercion is essential: the ordinary norm on
`Fin d -> R` is the supremum norm, not the Euclidean norm.  Both diameters are
zero on the empty tile.

## Public arithmetic and norm theorems

```lean
theorem dilationModulus_pos {ell oscillation tileCard : ℕ}
    (hell : 0 < ell) : 0 < dilationModulus ell oscillation tileCard

theorem ell_dvd_dilationModulus (ell oscillation tileCard : ℕ) :
    ell ∣ dilationModulus ell oscillation tileCard

theorem prime_dvd_dilationModulus {ell oscillation tileCard p : ℕ}
    (hp : p.Prime) (hpB : p ≤ 2 * oscillation * tileCard) :
    p ∣ dilationModulus ell oscillation tileCard

theorem prime_factor_gt_of_coprime_primorial {B r p : ℕ}
    (hr : Nat.Coprime r (primorial B))
    (hp : p.Prime) (hpr : p ∣ r) : B < p

theorem dilationModulus_le_explicit (ell oscillation tileCard : ℕ) :
    dilationModulus ell oscillation tileCard ≤
      ell * 4 ^ (2 * oscillation * tileCard)

theorem l1Norm_eq_zero {d : ℕ} {x : Lattice d} :
    l1Norm x = 0 ↔ x = 0

theorem l1Norm_neg {d : ℕ} (x : Lattice d) : l1Norm (-x) = l1Norm x

theorem l1Norm_add_le {d : ℕ} (x y : Lattice d) :
    l1Norm (x + y) ≤ l1Norm x + l1Norm y

theorem l1Norm_sub_le {d : ℕ} (x y : Lattice d) :
    l1Norm (x - y) ≤ l1Norm x + l1Norm y

theorem l1Norm_zsmul {d : ℕ} (n : ℤ) (x : Lattice d) :
    l1Norm (n • x) = Int.natAbs n * l1Norm x

theorem mem_tile_norm_le_diameter {d : ℕ}
    {F : Finset (Lattice d)} (h0 : 0 ∈ F) {x : Lattice d} (hx : x ∈ F) :
    l1Norm x ≤ l1Diameter F

theorem euclideanNorm_le_l1Norm {d : ℕ} (x : Lattice d) :
    euclideanNorm x ≤ (l1Norm x : ℝ)

theorem euclideanNorm_zsmul {d : ℕ} (n : ℤ) (x : Lattice d) :
    euclideanNorm (n • x) = (Int.natAbs n : ℝ) * euclideanNorm x

theorem one_le_euclideanNorm {d : ℕ} {x : Lattice d} (hx : x ≠ 0) :
    (1 : ℝ) ≤ euclideanNorm x

theorem l1Norm_le_sqrt_dim_mul_euclideanNorm {d : ℕ} (x : Lattice d) :
    (l1Norm x : ℝ) ≤ Real.sqrt d * euclideanNorm x

theorem euclideanDiameter_le_l1Diameter {d : ℕ}
    (F : Finset (Lattice d)) :
    euclideanDiameter F ≤ l1Diameter F

theorem l1Diameter_le_sqrt_dim_mul_euclideanDiameter {d : ℕ}
    (F : Finset (Lattice d)) :
    (l1Diameter F : ℝ) ≤ Real.sqrt d * euclideanDiameter F
```

The final comparison is used only where the paper permits a constant depending
on the tile cardinality or in fixed dimension two.  It is not used to obtain
the coefficient-one Euclidean direction bound in Theorem 1.4; that bound gets
a direct determinant/product proof in Chapter 03.

## Lattice geometry definitions

```lean
namespace TranslationalTilings

def wedge (u v : Plane) : ℤ := u 0 * v 1 - u 1 * v 0

def Commensurable {d : ℕ} (u v : Lattice d) : Prop :=
  ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • u = b • v

def PairwiseIncommensurable {d m : ℕ}
    (h : Fin m → Lattice d) : Prop :=
  ∀ i j, i ≠ j → ¬ Commensurable (h i) (h j)

def generatedPair (u v : Plane) : AddSubgroup Plane :=
  AddSubgroup.closure ({u, v} : Set Plane)

def scalarLattice {d : ℕ} (q : ℕ) : AddSubgroup (Lattice d) :=
  (nsmulAddMonoidHom q).range

def vectorContent {d : ℕ} (h : Lattice d) : ℕ :=
  (Finset.univ : Finset (Fin d)).gcd fun i ↦ Int.natAbs (h i)

def primitivePart {d : ℕ} (h : Lattice d) : Lattice d :=
  if h = 0 then 0 else fun i ↦ h i / (vectorContent h : ℤ)

def IsPrimitive {d : ℕ} (h : Lattice d) : Prop :=
  h ≠ 0 ∧ vectorContent h = 1

def slopeVector (t : ℕ) : Plane := ![(1 : ℤ), (t : ℤ)]

def avoidsDirections (h : Fin m → Plane) (t : ℕ) : Bool :=
  decide (∀ i, wedge (slopeVector t) (h i) ≠ 0)

def avoidanceSlope (h : Fin m → Plane) : ℕ :=
  ((List.range (m + 1)).find? (avoidsDirections h)).getD 0

def avoidanceVector (h : Fin m → Plane) : Plane :=
  slopeVector (avoidanceSlope h)

def unorderedPairs (m : ℕ) : Finset (Fin m × Fin m) :=
  Finset.univ.offDiag.filter fun ij ↦ ij.1 < ij.2

def pairWedgeLCM {m : ℕ} (h : Fin m → Plane) : ℕ :=
  (unorderedPairs m).lcm fun ij ↦
    Int.natAbs (wedge (h ij.1) (h ij.2))

end TranslationalTilings
```

`Commensurable` deliberately describes a common nonzero rational direction,
so zero is not commensurable with a nonzero vector.  Any place that needs
linear dependence including zero tests `wedge u v = 0` directly.  In
particular the slicing LCM in Chapter 07 filters nonzero wedges and cannot
receive a diagonal zero.  Content and primitive part are dimension-generic:
Theorem 3.4 is a theorem in `Z^d`, and its grouping proof must not depend on
the two-coordinate determinant API.  The older planar calls elaborate by
specializing `d=2`.

The avoidance vector is genuinely executable: it searches the canonical list
of slopes from zero through `m` and has a harmless fallback.  The theorem
below proves that the fallback is never taken under its advertised nonzero
direction hypothesis.

## Public lattice geometry theorems

```lean
theorem wedge_zero_left (v : Plane) : wedge 0 v = 0
theorem wedge_zero_right (u : Plane) : wedge u 0 = 0
theorem wedge_add_left (u v w : Plane) :
    wedge (u + v) w = wedge u w + wedge v w
theorem wedge_add_right (u v w : Plane) :
    wedge u (v + w) = wedge u v + wedge u w
theorem wedge_swap (u v : Plane) : wedge u v = -wedge v u
theorem wedge_zsmul_left (n : ℤ) (u v : Plane) :
    wedge (n • u) v = n * wedge u v
theorem wedge_zsmul_right (n : ℤ) (u v : Plane) :
    wedge u (n • v) = n * wedge u v

theorem commensurable_iff_wedge_eq_zero {u v : Plane}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    Commensurable u v ↔ wedge u v = 0

theorem cramer_identity (u v x : Plane) :
    (wedge u v) • x = wedge x v • u + wedge u x • v

theorem scalarLattice_natAbs_wedge_le_generatedPair (u v : Plane) :
    scalarLattice (Int.natAbs (wedge u v)) ≤ generatedPair u v

theorem index_generatedPair {u v : Plane} (hdet : wedge u v ≠ 0) :
    (generatedPair u v).index = Int.natAbs (wedge u v)

theorem natAbs_wedge_le_l1Norm_mul_l1Norm (u v : Plane) :
    Int.natAbs (wedge u v) ≤ l1Norm u * l1Norm v

theorem abs_wedge_le_euclideanNorm_mul_euclideanNorm (u v : Plane) :
    |(wedge u v : ℝ)| ≤ euclideanNorm u * euclideanNorm v

theorem scalarLattice_mono_dvd {d m n : ℕ} (h : m ∣ n) :
    scalarLattice (d := d) n ≤ scalarLattice m

theorem scalarLattice_index (d q : ℕ) :
    (scalarLattice (d := d) q).index = q ^ d

theorem vectorContent_pos {d : ℕ} {h : Lattice d} (hh : h ≠ 0) :
  0 < vectorContent h

theorem vectorContent_dvd_coord {d : ℕ} (h : Lattice d) (i : Fin d) :
    (vectorContent h : ℤ) ∣ h i

theorem primitive_decomposition {d : ℕ} {h : Lattice d} (hh : h ≠ 0) :
    (vectorContent h : ℤ) • primitivePart h = h ∧
      IsPrimitive (primitivePart h)

theorem primitive_decomposition_unique {d : ℕ}
    {h v : Lattice d} {k : ℕ}
    (hh : h ≠ 0) (hk : 0 < k) (hv : IsPrimitive v)
    (hdecomp : h = (k : ℤ) • v) :
    k = vectorContent h ∧ v = primitivePart h

theorem primitive_bezout {d : ℕ} {v : Lattice d}
    (hv : IsPrimitive v) :
  ∃ a : Lattice d, ∑ i, a i * v i = 1

theorem integer_multiple_of_primitive_of_commensurable
    {d : ℕ} {u v : Lattice d} (hu : u ≠ 0)
    (hv : IsPrimitive v) (huv : Commensurable u v) :
  ∃ z : ℤ, z ≠ 0 ∧ u = z • v

theorem exists_commonMultiple_of_pairwise_commensurable
    {d : ℕ} {C : Finset (Lattice d)} (hC : C.Nonempty)
    (hne : ∀ f ∈ C, f ≠ 0)
    (hcomm : ∀ u ∈ C, ∀ v ∈ C, Commensurable u v) :
  ∃ h : Lattice d,
    h ≠ 0 ∧
    (∀ f ∈ C, ∃ z : ℤ, z ≠ 0 ∧ h = z • f) ∧
    l1Norm h ≤ ∏ f ∈ C, l1Norm f ∧
    euclideanNorm h ≤ ∏ f ∈ C, euclideanNorm f

theorem exists_SL2Z_send_primitive_to_e0 {h : Plane}
    (hh : IsPrimitive h) :
    ∃ e : Plane ≃ₗ[ℤ] Plane,
      LinearMap.det e.toLinearMap = 1 ∧ e h = ![1, 0]

theorem avoidanceVector_spec {m : ℕ} {h : Fin m → Plane}
    (hne : ∀ i, h i ≠ 0) :
    avoidanceVector h ≠ 0 ∧
      (∀ i, ¬ Commensurable (avoidanceVector h) (h i)) ∧
      l1Norm (avoidanceVector h) ≤ m + 1

theorem pairWedgeLCM_pos {m : ℕ} {h : Fin m → Plane}
    (hne : ∀ i, h i ≠ 0) (hpair : PairwiseIncommensurable h) :
    0 < pairWedgeLCM h

theorem pairWedgeLCM_scalarLattice_le {m : ℕ}
    {h : Fin m → Plane} (hne : ∀ i, h i ≠ 0)
    (hpair : PairwiseIncommensurable h) {i j : Fin m} (hij : i ≠ j) :
    scalarLattice (pairWedgeLCM h) ≤ generatedPair (h i) (h j)

theorem pairWedgeLCM_bound {m : ℕ} {h : Fin m → Plane}
    (hne : ∀ i, h i ≠ 0) (hpair : PairwiseIncommensurable h) :
    pairWedgeLCM h ≤ ∏ i, l1Norm (h i) ^ (m - 1)
```

## Proof content

The primorial theorems give every required small prime divisor and the
explicit bound `primorial B < 4^B` when `B` is positive; the zero case is a
calculation.  `Nat.lcm_le_mul` then gives the displayed modulus majorant.

The `l1` laws are coordinatewise `Int.natAbs` inequalities.  The Euclidean
comparisons are Cauchy--Schwarz for the all-ones vector and the elementary
inequality `sqrt(sum x_i^2) <= sum |x_i|`.  Finite suprema transfer these
pointwise inequalities to diameters, with the empty branch reduced to zero.

The wedge identities are coordinate calculations.  If both vectors are
nonzero, zero wedge is equivalent to a common nonzero integer multiple by
clearing the two coordinate denominators.  Cramer's displayed identity shows
that `|u wedge v|` times every lattice vector belongs to the subgroup generated
by `u,v`; `AddSubgroup.index_eq_natAbs_det` supplies the corresponding index.
The scalar-lattice index itself is exactly Mathlib's
`AddSubgroup.index_range_nsmul` plus `finrank (Fin d -> Z) = d`.

For arbitrary `d`, `Finset.gcd` over `Fin d` divides every coordinate.
If the vector is nonzero then one coordinate has positive absolute value, so
the gcd is positive.  Division by this positive content is coordinatewise
exact; the standard finite-gcd Bézout identity proves that the quotient has
content one.  The same identity is exported as `primitive_bezout`.

For `integer_multiple_of_primitive_of_commensurable`, expand
`a•u=b•v`.  Multiplying the Bézout identity for `v` by `b` shows `a∣b`:
every term `b*v_i` equals `a*u_i`.  Cancelling the nonzero integer `a`
therefore gives `u=(b/a)•v`, with a nonzero coefficient because `u≠0`.

For a nonempty pairwise commensurable class `C`, choose `f₀∈C` and its
primitive part `v`.  The preceding theorem writes every `f` uniquely as
`z_f•v`, `z_f≠0`.  Let `L=lcm_f |z_f|` and `h=L•v`; divisibility, with the
sign of `z_f` restored, makes `h` an integer multiple of every `f`.  Mathlib's
`Finset.lcm_dvd_prod` gives `L≤∏_f |z_f|`.  The identities
`l1Norm (z•v)=|z|*l1Norm v` and `euclideanNorm (z•v)=|z|*euclideanNorm v`,
together with `1≤l1Norm v`, `one_le_euclideanNorm`, and `C.card≥1`, give

```text
norm h = L*norm v
       ≤ (product_f |z_f|)*norm v
       ≤ product_f (|z_f|*norm v)
       = product_f norm f.
```

This proves both coefficient-one class bounds without a dimension-dependent
norm-equivalence loss.  In dimension two, the determinant-one change of
coordinates is the Bézout matrix; its inverse has integer entries because its
determinant is one.

For bounded avoidance, each nonzero direction forbids at most one candidate
`(1,t)`.  There are `m+1` candidates and only `m` directions.  Hence the
Boolean search succeeds, returns a nonzero incommensurable vector, and has
`l1` norm at most `m+1`.

Finally, `pairWedgeLCM` uses each unordered pair once.  Nonzero,
incommensurable directions make every listed wedge positive after `natAbs`.
`Finset.dvd_lcm` plus Cramer gives all subgroup inclusions;
`Finset.lcm_dvd_prod` and
`|u wedge v| <= norm(u)*norm(v)` put each vector in exactly `m-1` product
factors, proving the final bound.
