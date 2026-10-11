import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement

/-!
# Discrete translational tilings

This file provides the exact, pointwise finite-convolution model used throughout the
formalization.  It also collects the basic periodicity and coset-partition interfaces.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- The rank-`d` integer lattice, represented by coordinate functions. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ

/-- The integer lattice plane `ℤ²`. -/
abbrev Plane := Lattice 2

/-- The integer-valued indicator function of a set. -/
noncomputable def setIndicator {G : Type*} (A : Set G) : G → ℤ :=
  A.indicator (fun _ ↦ 1)

/-- A finite tile encoded in the additive monoid algebra. -/
noncomputable def tileMonoidAlgebra (R G : Type*) [Semiring R]
    [AddCommMonoid G] (F : Finset G) : AddMonoidAlgebra R G :=
  ∑ f ∈ F, AddMonoidAlgebra.single f (1 : R)

/-- Convolution of a finite tile with a function on an additive group. -/
def tileConv {G R : Type*} [AddCommGroup G] [AddCommMonoid R]
    (F : Finset G) (g : G → R) (x : G) : R :=
  ∑ f ∈ F, g (x - f)

/-- The assertion that translating `A` by `F` tiles `E` at constant level `k`. -/
def TilesAtLevel {G : Type*} [AddCommGroup G]
    (F : Finset G) (A E : Set G) (k : ℕ) : Prop :=
  ∀ x, tileConv F (setIndicator A) x = (k : ℤ) * setIndicator E x

/-- The assertion that `F + A` tiles `E` at level one. -/
def Tiles {G : Type*} [AddCommGroup G]
    (F : Finset G) (A E : Set G) : Prop :=
  TilesAtLevel F A E 1

/-- The assertion that `F + A` tiles the whole ambient group. -/
def TilesUniverse {G : Type*} [AddCommGroup G]
    (F : Finset G) (A : Set G) : Prop :=
  Tiles F A Set.univ

/-- Periodicity of a function under every translation from a subgroup. -/
def PeriodicOn {G R : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (f : G → R) : Prop :=
  ∀ h ∈ H, Function.Periodic f h

/-- Coordinate-scalar periodicity with lattice period `q ℤᵈ`. -/
def ScalarPeriodic {d : ℕ} {R : Type*}
    (q : ℕ) (f : Lattice d → R) : Prop :=
  ∀ x z, f (x + (q : ℤ) • z) = f x

/-- Set membership is invariant under every translation from a subgroup. -/
def SetPeriodicOn {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (A : Set G) : Prop :=
  ∀ h ∈ H, ∀ x, x + h ∈ A ↔ x ∈ A

/-- Set membership is invariant under the scalar lattice `q ℤᵈ`. -/
def SetScalarPeriodic {d : ℕ} (q : ℕ) (A : Set (Lattice d)) : Prop :=
  ∀ x z, x + (q : ℤ) • z ∈ A ↔ x ∈ A

/-- A set invariant under a finite-index sublattice. -/
def IsPeriodic {d : ℕ} (A : Set (Lattice d)) : Prop :=
  ∃ H : AddSubgroup (Lattice d),
    Finite ((Lattice d) ⧸ H) ∧ SetPeriodicOn H A

/-- The additive coset `x + H`, represented by `y - x ∈ H`. -/
def addCoset {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (x : G) : Set G :=
  {y | y - x ∈ H}

/-- The fiber represented by an element of the quotient `G ⧸ H`. -/
def quotientCoset {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (c : G ⧸ H) : Set G :=
  {x | QuotientAddGroup.mk' H x = c}

/-- Translation of a set by `t`. -/
def translateSet {G : Type*} [AddCommGroup G]
    (t : G) (A : Set G) : Set G :=
  {x | x - t ∈ A}

/-- A finite disjoint decomposition into subsets with nonzero periods. -/
structure WeakPeriodicDecomposition (A : Set Plane) where
  /-- Number of periodic pieces. -/
  numberOfParts : ℕ
  /-- The subsets forming the decomposition. -/
  part : Fin numberOfParts → Set Plane
  /-- A period assigned to each subset. -/
  period : Fin numberOfParts → Plane
  period_ne_zero : ∀ i, period i ≠ 0
  periodic_part : ∀ i, ∀ x, x + period i ∈ part i ↔ x ∈ part i
  pairwiseDisjoint : Set.PairwiseDisjoint Set.univ part
  iUnion_parts : (⋃ i, part i) = A

/-- A planar set admitting a finite weak-periodic decomposition. -/
def WeaklyPeriodic (A : Set Plane) : Prop :=
  Nonempty (WeakPeriodicDecomposition A)

/-- A planar set possessing one global nonzero period. -/
def OnePeriodic (A : Set Plane) : Prop :=
  ∃ h : Plane, h ≠ 0 ∧ ∀ x, x + h ∈ A ↔ x ∈ A

/-- On each coset of `Λ`, the set has one period selected from `periods`. -/
def CosetwisePeriodic (A : Set Plane) (Λ : AddSubgroup Plane)
    {m : ℕ} (periods : Fin m → Plane) : Prop :=
  ∀ x, ∃ j, ∀ y,
    y + periods j ∈ A ∩ addCoset Λ x ↔ y ∈ A ∩ addCoset Λ x

/-- Expand finite-tile convolution at a point. -/
theorem tileConv_apply {G R : Type*} [AddCommGroup G] [AddCommMonoid R]
    (F : Finset G) (g : G → R) (x : G) :
    tileConv F g x = ∑ f ∈ F, g (x - f) :=
  rfl

/-- Convolution with the zero function is zero. -/
theorem tileConv_zero {G R : Type*} [AddCommGroup G] [AddCommMonoid R]
    (F : Finset G) : tileConv F (0 : G → R) = 0 := by
  funext x
  simp [tileConv]

/-- Finite-tile convolution distributes over addition. -/
theorem tileConv_add {G R : Type*} [AddCommGroup G] [AddCommMonoid R]
    (F : Finset G) (g h : G → R) :
    tileConv F (g + h) = tileConv F g + tileConv F h := by
  funext x
  simp [tileConv, Finset.sum_add_distrib]

/-- Finite-tile convolution distributes over subtraction. -/
theorem tileConv_sub {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (F : Finset G) (g h : G → R) :
    tileConv F (g - h) = tileConv F g - tileConv F h := by
  funext x
  simp [tileConv, Finset.sum_sub_distrib]

/-- Scalars commute with finite-tile convolution. -/
theorem tileConv_smul {G R S : Type*} [AddCommGroup G]
    [Semiring S] [AddCommMonoid R] [Module S R]
    (F : Finset G) (c : S) (g : G → R) :
    tileConv F (c • g) = c • tileConv F g := by
  funext x
  simp [tileConv, Finset.smul_sum]

/-- Translating the input function translates its finite-tile convolution. -/
theorem tileConv_translate {G R : Type*} [AddCommGroup G] [AddCommMonoid R]
    (F : Finset G) (g : G → R) (a : G) :
    tileConv F (fun y ↦ g (y - a)) = fun x ↦ tileConv F g (x - a) := by
  funext x
  apply Finset.sum_congr rfl
  intro f _
  abel_nf

/-- Indicator convolution counts tile points whose translates lie in a set. -/
theorem tileConv_indicator_eq_card {G : Type*} [AddCommGroup G]
    (F : Finset G) (A : Set G) (x : G) :
    tileConv F (setIndicator A) x =
      ((@Finset.filter G (fun f ↦ x - f ∈ A)
        (fun _ ↦ Classical.propDecidable _) F).card : ℤ) := by
  classical
  simp [tileConv, setIndicator, Set.indicator, Finset.sum_boole]

/-- Characterize a level tiling by its pointwise representation count. -/
theorem tilesAtLevel_iff_representation_count
    {G : Type*} [AddCommGroup G]
    (F : Finset G) (A E : Set G) (k : ℕ) :
  TilesAtLevel F A E k ↔ ∀ x,
      (@Finset.filter G (fun f ↦ x - f ∈ A)
        (fun _ ↦ Classical.propDecidable _) F).card =
          @ite ℕ (x ∈ E) (Classical.propDecidable _) k 0 := by
  classical
  constructor
  · intro h x
    specialize h x
    rw [tileConv_indicator_eq_card] at h
    by_cases hx : x ∈ E
    · rw [if_pos hx]
      simp only [setIndicator, Set.indicator_of_mem hx, mul_one] at h
      exact_mod_cast h
    · rw [if_neg hx]
      simp only [setIndicator, Set.indicator_of_notMem hx, mul_zero] at h
      exact_mod_cast h
  · intro h x
    specialize h x
    rw [tileConv_indicator_eq_card]
    by_cases hx : x ∈ E
    · rw [if_pos hx] at h
      simp only [setIndicator, Set.indicator_of_mem hx, mul_one]
      exact_mod_cast h
    · rw [if_neg hx] at h
      simp only [setIndicator, Set.indicator_of_notMem hx, mul_zero]
      exact_mod_cast h

/-- Periodicity restricts along inclusion of period subgroups. -/
theorem periodicOn_mono {G R : Type*} [AddCommGroup G]
    {H K : AddSubgroup G} {f : G → R}
    (hHK : H ≤ K) (hf : PeriodicOn K f) : PeriodicOn H f :=
  fun h hh ↦ hf h (hHK hh)

/-- Set periodicity is equivalent to periodicity of its integer indicator. -/
theorem setPeriodicOn_iff_indicator {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) (A : Set G) :
    SetPeriodicOn H A ↔ PeriodicOn H (setIndicator A) := by
  classical
  have indicator_eq_indicator_iff (x y : G) :
      setIndicator A x = setIndicator A y ↔ (x ∈ A ↔ y ∈ A) := by
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;>
      simp [setIndicator, hx, hy]
  constructor
  · intro h p hp x
    exact (indicator_eq_indicator_iff (x + p) x).2 (h p hp x)
  · intro h p hp x
    exact (indicator_eq_indicator_iff (x + p) x).1 (h p hp x)

/-- Restate scalar set periodicity directly as membership invariance. -/
theorem setScalarPeriodic_iff_membership {d : ℕ}
    (q : ℕ) (A : Set (Lattice d)) :
    SetScalarPeriodic q A ↔ ∀ x z,
      x + (q : ℤ) • z ∈ A ↔ x ∈ A :=
  Iff.rfl

/-- A function periodic on a finite-index subgroup is scalar-periodic by its index. -/
theorem finiteIndex_periodic_scalarPeriodic {d : ℕ} {R : Type*}
    (H : AddSubgroup (Lattice d)) (f : Lattice d → R)
    [Finite ((Lattice d) ⧸ H)] (hf : PeriodicOn H f) :
    ScalarPeriodic H.index f := by
  intro x z
  apply hf
  simpa using H.nsmul_index_mem z

/-- Distinct quotient fibers of an additive subgroup are disjoint. -/
theorem quotientCoset_pairwiseDisjoint {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) :
    Set.PairwiseDisjoint Set.univ (quotientCoset H) := by
  intro c _ d _ hcd
  change Disjoint (quotientCoset H c) (quotientCoset H d)
  rw [Set.disjoint_left]
  intro x hxc hxd
  exact hcd (hxc.symm.trans hxd)

/-- The quotient fibers of an additive subgroup cover the ambient group. -/
theorem iUnion_quotientCoset {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) : (⋃ c, quotientCoset H c) = Set.univ := by
  ext x
  simp [quotientCoset]

/-- Cosetwise nonzero periods in a finite-index lattice yield weak periodicity. -/
theorem weaklyPeriodic_of_cosetwise (A : Set Plane)
    (Λ : AddSubgroup Plane) {m : ℕ} (periods : Fin m → Plane)
    [Finite (Plane ⧸ Λ)] (_hm : 0 < m)
    (hne : ∀ j, periods j ≠ 0) (hmem : ∀ j, periods j ∈ Λ)
    (hA : CosetwisePeriodic A Λ periods) : WeaklyPeriodic A := by
  classical
  have hcoset : ∀ c : Plane ⧸ Λ, ∃ j, ∀ y,
      y + periods j ∈ A ∩ quotientCoset Λ c ↔
        y ∈ A ∩ quotientCoset Λ c := by
    intro c
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective Λ c
    simpa [addCoset, quotientCoset, QuotientAddGroup.eq_iff_sub_mem] using hA x
  let chosen : Plane ⧸ Λ → Fin m := fun c ↦ Classical.choose (hcoset c)
  let e : Fin (Nat.card (Plane ⧸ Λ)) ≃ (Plane ⧸ Λ) :=
    (Finite.equivFin (Plane ⧸ Λ)).symm
  refine ⟨{
    numberOfParts := Nat.card (Plane ⧸ Λ)
    part := fun i ↦ A ∩ quotientCoset Λ (e i)
    period := fun i ↦ periods (chosen (e i))
    period_ne_zero := fun i ↦ hne (chosen (e i))
    periodic_part := ?_
    pairwiseDisjoint := ?_
    iUnion_parts := ?_
  }⟩
  · intro i x
    let j := chosen (e i)
    have hq : x + periods j ∈ quotientCoset Λ (e i) ↔
        x ∈ quotientCoset Λ (e i) := by
      change QuotientAddGroup.mk' Λ (x + periods j) = e i ↔
        QuotientAddGroup.mk' Λ x = e i
      have hp0 : QuotientAddGroup.mk' Λ (periods j) = 0 :=
        (QuotientAddGroup.eq_zero_iff (periods j)).2 (hmem j)
      rw [map_add, hp0, add_zero]
    have hwhole := Classical.choose_spec (hcoset (e i)) x
    constructor
    · intro hx
      exact ⟨(hwhole.mp hx).1, hq.mp hx.2⟩
    · intro hx
      exact ⟨(hwhole.mpr hx).1, hq.mpr hx.2⟩
  · intro i _ j _ hij
    change Disjoint (A ∩ quotientCoset Λ (e i)) (A ∩ quotientCoset Λ (e j))
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    apply e.injective
    exact hxi.2.symm.trans hxj.2
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact hxi.1
    · intro x hx
      let c : Plane ⧸ Λ := QuotientAddGroup.mk' Λ x
      let i : Fin (Nat.card (Plane ⧸ Λ)) := e.symm c
      apply Set.mem_iUnion.mpr
      refine ⟨i, hx, ?_⟩
      change QuotientAddGroup.mk' Λ x = e i
      exact (e.apply_symm_apply c).symm

/-- Translating a tile and its tiling set preserves the tiling relation. -/
theorem tiles_translate_tile {G : Type*} [AddCommGroup G]
    (F : Finset G) (A E : Set G) (k : ℕ) (t : G) :
  TilesAtLevel F A E k ↔
      TilesAtLevel
        (@Finset.image G G (Classical.decEq G) (fun f ↦ f - t) F)
        (translateSet t A) E k := by
  classical
  have hconv :
      tileConv (F.image fun f ↦ f - t) (setIndicator (translateSet t A)) =
        tileConv F (setIndicator A) := by
    funext x
    simp only [tileConv]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro f _
      have harg : x - (f - t) - t = x - f := by abel
      simp only [setIndicator, Set.indicator_apply, translateSet, Set.mem_ofPred_eq, harg]
    · intro a _ b _ hab
      exact sub_left_injective hab
  unfold TilesAtLevel
  rw [hconv]

end TranslationalTilings
