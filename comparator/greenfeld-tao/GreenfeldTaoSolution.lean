import Mathlib
import TranslationalTilings.Main

/-!
# The main Greenfeld--Tao theorems on translational tilings

This solution repeats the self-contained challenge vocabulary verbatim, then bridges it to the
production formalization of Greenfeld and Tao, *The Structure of Translational Tilings in `Z^d`*.

The reusable formalization contains quantitative bounds, convolution algebras, lattice indices,
periodic target codes, and executable search certificates. None of that implementation machinery
is needed here. We work directly with finite tiles, representation counts, and periodic sets.
-/

open Function Set
open scoped BigOperators

namespace GreenfeldTaoComparator

/-! ## 1. Tiles and translational tilings -/

/-- The integer lattice `ℤ^d`. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ

/-- The integer lattice plane `ℤ²`. -/
abbrev Plane := Lattice 2

/-- The value `1` on `A` and `0` outside `A`. -/
noncomputable def indicator {G : Type*} (A : Set G) (x : G) : ℕ :=
  by classical exact if x ∈ A then 1 else 0

/-- The number of representations `x = f + a` with `f ∈ F` and `a ∈ A`.

For fixed `x` and `f`, the translating point has to be `a = x - f`, so it is enough to count the
tile points `f` for which `x - f` belongs to `A`. -/
noncomputable def representationCount {G : Type*} [AddCommGroup G]
    (F : Finset G) (A : Set G) (x : G) : ℕ := by
  classical
  exact (F.filter fun f ↦ x - f ∈ A).card

/-- The translates `f + A`, for `f ∈ F`, cover `E` exactly `k` times and do not cover points
outside `E`. -/
def TilesAtLevel {G : Type*} [AddCommGroup G]
    (F : Finset G) (A E : Set G) (k : ℕ) : Prop :=
  ∀ x, representationCount F A x = k * indicator E x

/-- A level-one translational tiling of `E`. -/
def Tiles {G : Type*} [AddCommGroup G]
    (F : Finset G) (A E : Set G) : Prop :=
  TilesAtLevel F A E 1

/-- A translational tiling of the whole ambient lattice. -/
def TilesLattice {G : Type*} [AddCommGroup G]
    (F : Finset G) (A : Set G) : Prop :=
  Tiles F A Set.univ

/-! ## 2. Periodicity -/

/-- A lattice set is periodic if membership is unchanged by every vector in `q ℤ^d` for some
positive integer `q`. -/
def Periodic {d : ℕ} (A : Set (Lattice d)) : Prop :=
  ∃ q : ℕ, 0 < q ∧ ∀ x z, x + (q : ℤ) • z ∈ A ↔ x ∈ A

/-- A planar set has one nonzero translation period. -/
def OnePeriodic (A : Set Plane) : Prop :=
  ∃ h : Plane, h ≠ 0 ∧ ∀ x, x + h ∈ A ↔ x ∈ A

/-- A planar set is weakly periodic if it is a finite disjoint union of one-periodic sets. -/
def WeaklyPeriodic (A : Set Plane) : Prop :=
  ∃ (n : ℕ) (part : Fin n → Set Plane),
    (∀ i, OnePeriodic (part i)) ∧
    Set.PairwiseDisjoint Set.univ part ∧
    (⋃ i, part i) = A

/-- The coset `x + Λ` of a sublattice `Λ`. -/
def latticeCoset (Λ : AddSubgroup Plane) (x : Plane) : Set Plane :=
  {y | y - x ∈ Λ}

/-- On every coset of `Λ`, membership in `A` is preserved by at least one vector from the finite
family `period`. The chosen vector may depend on the coset. -/
def PeriodicOnEachCoset (A : Set Plane) (Λ : AddSubgroup Plane)
    {m : ℕ} (period : Fin m → Plane) : Prop :=
  ∀ x, ∃ j, ∀ y,
    y + period j ∈ A ∩ latticeCoset Λ x ↔ y ∈ A ∩ latticeCoset Λ x


namespace ProductionBridge

private theorem tilesAtLevel_iff_production {G : Type*} [AddCommGroup G]
    (F : Finset G) (A E : Set G) (k : ℕ) :
    TilesAtLevel F A E k ↔
      TranslationalTilings.TilesAtLevel F A E k := by
  classical
  rw [TranslationalTilings.tilesAtLevel_iff_representation_count]
  constructor
  · intro h x
    have hxCount := h x
    by_cases hx : x ∈ E
    · simpa [representationCount, indicator, hx] using hxCount
    · simpa [representationCount, indicator, hx] using hxCount
  · intro h x
    have hxCount := h x
    by_cases hx : x ∈ E
    · simpa [representationCount, indicator, hx] using hxCount
    · simpa [representationCount, indicator, hx] using hxCount

private theorem tiles_iff_production {G : Type*} [AddCommGroup G]
    (F : Finset G) (A E : Set G) :
    Tiles F A E ↔ TranslationalTilings.Tiles F A E := by
  simpa only [Tiles, TranslationalTilings.Tiles] using
    tilesAtLevel_iff_production F A E 1

private theorem periodic_to_production_isPeriodic {d : ℕ}
    {A : Set (Lattice d)} (hA : Periodic A) :
    TranslationalTilings.IsPeriodic A := by
  obtain ⟨q, hq, hperiodic⟩ := hA
  let H : AddSubgroup (Lattice d) :=
    TranslationalTilings.scalarLattice q
  have hindex : H.index ≠ 0 := by
    change (TranslationalTilings.scalarLattice q).index ≠ 0
    rw [TranslationalTilings.scalarLattice_index]
    positivity
  let _ : Finite ((Lattice d) ⧸ H) :=
    AddSubgroup.index_ne_zero_iff_finite.mp hindex
  refine ⟨H, inferInstance, ?_⟩
  intro h hh x
  obtain ⟨z, rfl⟩ := hh
  exact hperiodic x z

private theorem weaklyPeriodic_iff_production {A : Set Plane} :
    WeaklyPeriodic A ↔ TranslationalTilings.WeaklyPeriodic A := by
  constructor
  · rintro ⟨n, part, hpart, hdisjoint, hunion⟩
    choose period period_ne_zero periodic_part using hpart
    exact ⟨
      { numberOfParts := n
        part := part
        period := period
        period_ne_zero := period_ne_zero
        periodic_part := periodic_part
        pairwiseDisjoint := hdisjoint
        iUnion_parts := hunion }⟩
  · rintro ⟨D⟩
    refine ⟨D.numberOfParts, D.part, ?_, D.pairwiseDisjoint, D.iUnion_parts⟩
    intro i
    exact ⟨D.period i, D.period_ne_zero i, D.periodic_part i⟩

end ProductionBridge

open ProductionBridge

/-! ## 3. The planar structure theorems -/

/-- **Greenfeld--Tao Theorem 1.3(i), qualitative form.**

Every level-one tiling of a periodic subset of ℤ² by a nonempty finite tile is weakly periodic.
-/
theorem level_one_tilings_are_weakly_periodic
    {F : Finset Plane} {A E : Set Plane}
    (hF : F.Nonempty) (hE : Periodic E) (hTiles : Tiles F A E) :
    WeaklyPeriodic A := by
  have hproduction :=
    TranslationalTilings.theorem_1_3_i hF
      (periodic_to_production_isPeriodic hE)
      ((tiles_iff_production F A E).mp hTiles)
  exact weaklyPeriodic_iff_production.mpr hproduction

/-- **Greenfeld--Tao Theorem 1.4, qualitative form.**

After translating the tile so that it contains the origin, every level-one tiling of a periodic
target is periodic along at most `|F| - 1` directions, coset by coset. The production theorem also
gives explicit bounds for the sublattice and periods; they are deliberately omitted here. -/
theorem tilings_have_finitely_many_period_directions
    {F : Finset Plane} {A E : Set Plane}
    (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : Periodic E) (hTiles : Tiles F A E) :
    ∃ (m : ℕ) (period : Fin m → Plane) (Λ : AddSubgroup Plane),
      0 < m ∧ m ≤ F.card - 1 ∧
      (∀ j, period j ≠ 0) ∧ PeriodicOnEachCoset A Λ period := by
  obtain ⟨ell, hell, hEperiodic⟩ := hE
  obtain ⟨m, h, Λ, L, hm, hmle, hh, _hpairwise, _hfromTile,
      _hindividualBound, _hproductBound, _hlattice, _hindexBound,
      hL, _hLBound, hcoset⟩ :=
    TranslationalTilings.theorem_1_4 hell hzero hcard hEperiodic
      ((tiles_iff_production F A E).mp hTiles)
  refine ⟨m, (fun j ↦ (((ell * L : ℕ) : ℤ) • h j)), Λ, hm, hmle, ?_, ?_⟩
  · intro j
    apply smul_ne_zero
    · exact_mod_cast (Nat.mul_pos hell hL).ne'
    · exact hh j
  · simpa only [PeriodicOnEachCoset, latticeCoset,
      TranslationalTilings.CosetwisePeriodic, TranslationalTilings.addCoset,
      Set.mem_inter_iff] using hcoset

/-- **Greenfeld--Tao Theorem 1.3(ii).**

Weak periodicity is special to level one: an eight-point tile admits a level-four tiling of the
plane whose translating set is not weakly periodic. -/
theorem higher_level_tilings_need_not_be_weakly_periodic :
    ∃ (F : Finset Plane) (A : Set Plane),
      F.card = 8 ∧ TilesAtLevel F A Set.univ 4 ∧ ¬ WeaklyPeriodic A := by
  obtain ⟨F, A, hcard, htiles, hnotWeak⟩ :=
    TranslationalTilings.theorem_1_3_ii
  refine ⟨F, A, hcard, (tilesAtLevel_iff_production F A Set.univ 4).mpr htiles, ?_⟩
  intro hweak
  exact hnotWeak (weaklyPeriodic_iff_production.mp hweak)

/-- **Greenfeld--Tao Theorem 1.5, qualitative form.**

Whenever a finite planar tile tiles a periodic target at all, it admits a periodic tiling of that
same target. Taking the target to be all of ℤ² gives the periodic tiling theorem. -/
theorem tileable_periodic_sets_have_periodic_tilings
    {F : Finset Plane} {E : Set Plane} (hE : Periodic E) :
    (∃ A : Set Plane, Tiles F A E) →
      ∃ A : Set Plane, Periodic A ∧ Tiles F A E := by
  rintro ⟨A, hTiles⟩
  obtain ⟨ell, hell, hEperiodic⟩ := hE
  have hproductionE : TranslationalTilings.SetScalarPeriodic ell E :=
    hEperiodic
  have hproductionExists :
      ∃ A : Set Plane, TranslationalTilings.Tiles F A E :=
    ⟨A, (tiles_iff_production F A E).mp hTiles⟩
  obtain ⟨A', M, hM, hTiles', hPeriodic', _hbound⟩ :=
    TranslationalTilings.theorem_1_5 hell hproductionE hproductionExists
  refine ⟨A', ⟨ell * M, Nat.mul_pos hell hM, ?_⟩, ?_⟩
  · exact hPeriodic'
  · exact (tiles_iff_production F A' E).mpr hTiles'

/-- **Greenfeld--Tao Corollary 1.6, qualitative form.**

There is a Boolean algorithm deciding whether a finite subset of ℤ² tiles the plane. The
solution supplies the formalization's executable finite search; the present statement deliberately
omits its much longer explicit running-time bound. -/
theorem planar_tileability_is_decidable :
    ∃ decide : Finset Plane → Bool, ∀ F,
      decide F = true ↔ ∃ A : Set Plane, TilesLattice F A := by
  refine ⟨TranslationalTilings.planarTileDecision, ?_⟩
  intro F
  rw [TranslationalTilings.planarTileDecision_eq_true_iff]
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A, (tiles_iff_production F A Set.univ).mpr hA⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, (tiles_iff_production F A Set.univ).mp hA⟩

/-! ## 4. The general structure theorem -/

/-- **Greenfeld--Tao Theorem 1.7.**

Suppose the representation-count function of F + A is periodic on ℤ^d, and translate F so
that it contains the origin. Then the indicator of A is the representation count minus one
bounded periodic error function for each nonzero point of F. All error functions share a common
positive scale q, and the function indexed by f is periodic in the direction q f. -/
theorem structure_of_periodic_representation_count
    {d ell : ℕ} {F : Finset (Lattice d)} {A : Set (Lattice d)}
    (hd : 0 < d) (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiodic : ∀ x z,
      representationCount F A (x + (ell : ℤ) • z) = representationCount F A x) :
    ∃ q : ℕ, 0 < q ∧
      ∃ φ : ↥(F.erase 0) → Lattice d → ℝ,
        (∀ f x, 0 ≤ φ f x ∧ φ f x ≤ 1) ∧
        (∀ f x, φ f (x + (q : ℤ) • (f : Lattice d)) = φ f x) ∧
        ∀ x, (indicator A x : ℝ) =
          (representationCount F A x : ℝ) - ∑ f, φ f x := by
  classical
  have hproductionPeriodic :
      TranslationalTilings.ScalarPeriodic ell
        (TranslationalTilings.tileConv F
          (TranslationalTilings.setIndicator A)) := by
    intro x z
    rw [TranslationalTilings.tileConv_indicator_eq_card,
      TranslationalTilings.tileConv_indicator_eq_card]
    exact_mod_cast hperiodic x z
  obtain ⟨D⟩ :=
    TranslationalTilings.theorem_1_7 hd hell hzero hproductionPeriodic
  let q := TranslationalTilings.indicatorDilationModulus ell F.card
  have hq : 0 < q := by
    simpa [q, TranslationalTilings.indicatorDilationModulus] using
      (TranslationalTilings.dilationModulus_pos
        (oscillation := 1) (tileCard := F.card) hell)
  refine ⟨q, hq, D.phi, ?_, ?_, ?_⟩
  · intro f x
    exact ⟨D.phi_nonneg f x, D.phi_le_one f x⟩
  · intro f x
    exact D.phi_periodic f x
  · intro x
    have hdecomposition := D.decomposition x
    rw [TranslationalTilings.tileConv_indicator_eq_card] at hdecomposition
    by_cases hx : x ∈ A
    · simpa [indicator, representationCount,
        TranslationalTilings.setIndicator, Set.indicator, hx] using hdecomposition
    · simpa [indicator, representationCount,
        TranslationalTilings.setIndicator, Set.indicator, hx] using hdecomposition

end GreenfeldTaoComparator
