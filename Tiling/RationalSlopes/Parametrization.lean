import Tiling.RationalSlopes.SlicesAndColumns
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology

noncomputable section

namespace Tiling.RationalSlopes

open Tiling.RationalPolygonal (PolygonalRegion WeaklyPeriodic)
open Tiling.Polygonal

structure GoodParametrization (K : PolygonalRegion) (T : Set Plane) where
  lattice : PlanarLattice
  numberOfParts : ℕ
  Index : Fin numberOfParts → Type
  atom : ∀ i, Index i → ℤ → Set Plane
  atom_nonempty : ∀ i a m, (atom i a m).Nonempty
  atoms_disjoint : Set.PairwiseDisjoint Set.univ
    (fun s : Σ i : Fin numberOfParts, Index i × ℤ => atom s.1 s.2.1 s.2.2)
  union_eq : (⋃ i, ⋃ a : Index i, ⋃ m : ℤ, atom i a m) = T
  lambdaCoefficient : Fin numberOfParts → ℤ
  gammaCoefficient : Fin numberOfParts → ℤ
  lambdaCoefficient_ne_zero : ∀ i, lambdaCoefficient i ≠ 0
  atom_periodic : ∀ i a m,
    lambdaCoefficient i • lattice.basis 0 + gammaCoefficient i • lattice.basis 1 ∈
      periodGroup (atom i a m)
  carrier_transport : ∀ i a m,
    regularSupport K (atom i a m) =
      m • lattice.basis 1 +ᵥ regularSupport K (atom i a 0)

namespace GoodParametrization

private theorem period_iUnion {ι : Type} (S : ι → Set Plane) (u : Plane)
    (h : ∀ i, u ∈ periodGroup (S i)) : u ∈ periodGroup (⋃ i, S i) := by
  change u +ᵥ (⋃ i, S i) = ⋃ i, S i
  rw [Set.vadd_set_iUnion]
  exact Set.iUnion_congr h

private theorem setPeriodicBy_of_period {S : Set Plane} {u : Plane}
    (h : u ∈ periodGroup S) : Tiling.RationalPolygonal.SetPeriodicBy S u := by
  have hneg : (-u) +ᵥ S = S := (periodGroup S).neg_mem h
  intro x
  have hx := congrArg (fun A : Set Plane => x ∈ A) hneg
  simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm] using hx

private theorem regularization_period {S : Set Plane} {u : Plane}
    (h : u ∈ periodGroup S) : u ∈ periodGroup (interior (closure S)) := by
  change u +ᵥ interior (closure S) = interior (closure S)
  rw [← interior_vadd, ← closure_vadd]
  exact congrArg (fun A : Set Plane => interior (closure A)) h

private theorem support_period (K : PolygonalRegion) {S : Set Plane} {u : Plane}
    (h : u ∈ periodGroup S) : u ∈ periodGroup (regularSupport K S) := by
  change u +ᵥ regularSupport K S = regularSupport K S
  rw [← regularSupport_vadd, h]

private theorem regularSupport_iUnion2 (K : PolygonalRegion) {ι κ : Type}
    (S : ι → κ → Set Plane) :
    regularSupport K (⋃ a, ⋃ m, S a m) =
      interior (closure (⋃ a, ⋃ m, regularSupport K (S a m))) := by
  have hUnion (f : ι → κ → Set Plane) :
      (⋃ p : ι × κ, f p.1 p.2) = ⋃ a, ⋃ m, f a m := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨a, m⟩, hx⟩
      exact ⟨a, m, hx⟩
    · rintro ⟨a, m, hx⟩
      exact ⟨⟨a, m⟩, hx⟩
  rw [← hUnion S, regularSupport_iUnion]
  exact congrArg (fun A : Set Plane => interior (closure A))
    (hUnion (fun a m => regularSupport K (S a m)))

private theorem orbit_period (A : Set Plane) (γ : Plane) :
    γ ∈ periodGroup (⋃ m : ℤ, m • γ +ᵥ A) := by
  change γ +ᵥ (⋃ m : ℤ, m • γ +ᵥ A) = ⋃ m : ℤ, m • γ +ᵥ A
  rw [Set.vadd_set_iUnion]
  exact Set.iUnion_congr_of_surjective (fun m : ℤ => m + 1)
    (by intro n; exact ⟨n - 1, by dsimp; omega⟩)
    (fun m => by rw [add_zsmul, one_zsmul, add_comm (m • γ) γ, add_vadd])

def part {K : PolygonalRegion} {T : Set Plane} (G : GoodParametrization K T)
    (i : Fin G.numberOfParts) : Set Plane :=
  ⋃ a : G.Index i, ⋃ m : ℤ, G.atom i a m

def commonMultiple {K : PolygonalRegion} {T : Set Plane}
    (G : GoodParametrization K T) : ℕ :=
  ∏ i : Fin G.numberOfParts, (G.lambdaCoefficient i).natAbs

def replacementCentres {K : PolygonalRegion} {T : Set Plane}
    (G : GoodParametrization K T) : Set Plane :=
  ⋃ i, ⋃ a : G.Index i, ⋃ m : ℤ, m • G.lattice.basis 1 +ᵥ G.atom i a 0

private theorem iUnion_sigma_prod {ι : Type} {κ : ι → Type}
    (f : ∀ i, κ i → ℤ → Set Plane) :
    (⋃ s : Σ i, κ i × ℤ, f s.1 s.2.1 s.2.2) = ⋃ i, ⋃ a, ⋃ m, f i a m := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, a, m⟩, hx⟩
    exact ⟨i, a, m, hx⟩
  · rintro ⟨i, a, m, hx⟩
    exact ⟨⟨i, a, m⟩, hx⟩

private theorem atom_subset {K : PolygonalRegion} {T : Set Plane}
    (G : GoodParametrization K T) (i : Fin G.numberOfParts) (a : G.Index i) (m : ℤ) :
    G.atom i a m ⊆ T := by
  intro x hx
  have h : x ∈ ⋃ i, ⋃ a : G.Index i, ⋃ m : ℤ, G.atom i a m :=
    Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨m, hx⟩⟩⟩
  exact G.union_eq ▸ h

private theorem period_vadd {S : Set Plane} {u : Plane} (h : u ∈ periodGroup S)
    (v : Plane) : u ∈ periodGroup (v +ᵥ S) := by
  change u +ᵥ (v +ᵥ S) = v +ᵥ S
  calc
    u +ᵥ (v +ᵥ S) = v +ᵥ (u +ᵥ S) := by rw [← add_vadd, add_comm, add_vadd]
    _ = v +ᵥ S := congrArg (fun A : Set Plane => v +ᵥ A) h

private theorem tile_subset_support (K : PolygonalRegion) {S : Set Plane}
    {s : Plane} (hs : s ∈ S) : s +ᵥ K.openCarrier ⊆ regularSupport K S := by
  have hOpen : IsOpen (openUnion K S) := isOpen_iUnion fun t => isOpen_interior.vadd (t : Plane)
  exact (Set.subset_iUnion (fun t : S => (t : Plane) +ᵥ K.openCarrier) ⟨s, hs⟩).trans
    hOpen.subset_interior_closure

theorem commonMultiple_pos {K : PolygonalRegion} {T : Set Plane}
    (G : GoodParametrization K T) : 0 < G.commonMultiple := by
  classical
  exact Finset.prod_pos fun i _ => Int.natAbs_pos.mpr (G.lambdaCoefficient_ne_zero i)

theorem commonMultiple_divisible {K : PolygonalRegion} {T : Set Plane}
    (G : GoodParametrization K T) (i : Fin G.numberOfParts) :
    G.lambdaCoefficient i ∣ (G.commonMultiple : ℤ) := by
  classical
  apply Int.dvd_natCast.mpr
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem weaklyPeriodic {K : PolygonalRegion} {T : Set Plane}
    (G : GoodParametrization K T) : WeaklyPeriodic T := by
  classical
  refine ⟨{
    numberOfParts := G.numberOfParts
    part := G.part
    period := fun i => G.lambdaCoefficient i • G.lattice.basis 0 +
      G.gammaCoefficient i • G.lattice.basis 1
    period_ne_zero := ?_
    periodic_part := ?_
    pairwiseDisjoint := ?_
    iUnion_parts := G.union_eq }⟩
  · intro i hzero
    have hcoeff := (Fintype.linearIndependent_iff.mp G.lattice.independent)
      ![(G.lambdaCoefficient i : ℝ), (G.gammaCoefficient i : ℝ)]
      (by simpa [Fin.sum_univ_two, Int.cast_smul_eq_zsmul] using hzero) 0
    exact G.lambdaCoefficient_ne_zero i (Int.cast_eq_zero.mp hcoeff)
  · intro i
    apply setPeriodicBy_of_period
    exact period_iUnion _ _ fun a => period_iUnion _ _ fun m => G.atom_periodic i a m
  · intro i _ j _ hij
    apply Set.disjoint_iUnion_left.mpr
    intro a
    apply Set.disjoint_iUnion_left.mpr
    intro m
    apply Set.disjoint_iUnion_right.mpr
    intro b
    apply Set.disjoint_iUnion_right.mpr
    intro n
    exact G.atoms_disjoint (x := ⟨i, a, m⟩) (y := ⟨j, b, n⟩) (by trivial) (by trivial)
      (fun heq => hij (congrArg Sigma.fst heq))

theorem carriers_periodic {K : PolygonalRegion} {T : Set Plane}
    (G : GoodParametrization K T)
    (hp : IsPacking K.prototileFamily (K.placements T)) :
    G.lattice.basis 1 ∈ periodGroup (regularSupport K T) ∧
      (G.commonMultiple : ℤ) • G.lattice.basis 0 ∈
        periodGroup (regularSupport K T) := by
  have hγ : ∀ i, G.lattice.basis 1 ∈ periodGroup (regularSupport K (G.part i)) := by
    intro i
    rw [part, regularSupport_iUnion2]
    apply regularization_period
    rw [Set.iUnion_congr fun a => Set.iUnion_congr (G.carrier_transport i a)]
    exact period_iUnion _ _ fun a => orbit_period _ _
  have hk : ∀ i, G.lambdaCoefficient i • G.lattice.basis 0 ∈
      periodGroup (regularSupport K (G.part i)) := by
    intro i
    have hw : G.lambdaCoefficient i • G.lattice.basis 0 +
        G.gammaCoefficient i • G.lattice.basis 1 ∈
        periodGroup (regularSupport K (G.part i)) :=
      support_period K (period_iUnion _ _ fun a =>
        period_iUnion _ _ fun m => G.atom_periodic i a m)
    have hsub := (periodGroup (regularSupport K (G.part i))).sub_mem hw
      ((periodGroup (regularSupport K (G.part i))).zsmul_mem (hγ i) (G.gammaCoefficient i))
    exact (show (G.lambdaCoefficient i • G.lattice.basis 0 +
        G.gammaCoefficient i • G.lattice.basis 1) -
        G.gammaCoefficient i • G.lattice.basis 1 =
        G.lambdaCoefficient i • G.lattice.basis 0 from add_sub_cancel_right _ _) ▸ hsub
  have hN : ∀ i, (G.commonMultiple : ℤ) • G.lattice.basis 0 ∈
      periodGroup (regularSupport K (G.part i)) := by
    intro i
    obtain ⟨n, hn⟩ := G.commonMultiple_divisible i
    rw [hn, mul_comm, mul_smul]
    exact (periodGroup (regularSupport K (G.part i))).zsmul_mem (hk i) n
  have hu : (⋃ i, G.part i) = T := G.union_eq
  have heq : regularSupport K T =
      interior (closure (⋃ i, regularSupport K (G.part i))) := by
    calc
      regularSupport K T = regularSupport K (⋃ i, G.part i) := congrArg _ hu.symm
      _ = _ := regularSupport_iUnion K _
  rw [heq]
  exact ⟨regularization_period (period_iUnion _ _ hγ),
    regularization_period (period_iUnion _ _ hN)⟩

theorem periodic_replacement {K : PolygonalRegion} {T E : Set Plane}
    (G : GoodParametrization K T) (hTiles : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E) :
    TilesOn K G.replacementCentres E ∧
      IsLatticePeriodic G.replacementCentres ∧
        periodGroup G.replacementCentres ≤ periodGroup E := by
  classical
  let A := fun s : Σ i : Fin G.numberOfParts, G.Index i × ℤ =>
    G.atom s.1 s.2.1 s.2.2
  let R := fun s : Σ i : Fin G.numberOfParts, G.Index i × ℤ =>
    s.2.2 • G.lattice.basis 1 +ᵥ G.atom s.1 s.2.1 0
  have haU : (⋃ s, A s) = T := (iUnion_sigma_prod G.atom).trans G.union_eq
  have hrU : (⋃ s, R s) = G.replacementCentres :=
    iUnion_sigma_prod (fun i a m => m • G.lattice.basis 1 +ᵥ G.atom i a 0)
  have hrSupport : ∀ s, regularSupport K (R s) = regularSupport K (A s) := by
    intro s
    exact (regularSupport_vadd K _ _).trans (G.carrier_transport _ _ _).symm
  have hRS : regularSupport K G.replacementCentres = regularSupport K T := by
    calc
      regularSupport K G.replacementCentres = regularSupport K (⋃ s, R s) := congrArg _ hrU.symm
      _ = interior (closure (⋃ s, regularSupport K (R s))) := regularSupport_iUnion K R
      _ = interior (closure (⋃ s, regularSupport K (A s))) :=
        congrArg (fun B : Set Plane => interior (closure B)) (Set.iUnion_congr hrSupport)
      _ = regularSupport K (⋃ s, A s) := (regularSupport_iUnion K A).symm
      _ = regularSupport K T := congrArg _ haU
  have hAtomPack : ∀ i a m, IsPacking K.prototileFamily (K.placements (G.atom i a m)) := by
    intro i a m
    apply (isPacking_iff_openCarrier_disjoint K _).mpr
    exact ((isPacking_iff_openCarrier_disjoint K T).mp hTiles.2.1).mono (atom_subset G i a m)
  have hRPack : ∀ s, IsPacking K.prototileFamily (K.placements (R s)) := by
    intro s
    exact (tilesOn_translate (tilesOn_regularSupport_of_packing (hAtomPack _ _ 0))
      (s.2.2 • G.lattice.basis 1)).2.1
  have hpR : IsPacking K.prototileFamily (K.placements G.replacementCentres) := by
    apply (isPacking_iff_openCarrier_disjoint K _).mpr
    intro x hx y hy hxy
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (hrU.symm ▸ hx)
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hrU.symm ▸ hy)
    by_cases hst : s = t
    · subst t
      exact ((isPacking_iff_openCarrier_disjoint K _).mp (hRPack s)) hs ht hxy
    · have hdisj := regularSupport_disjoint_of_disjoint_subfamilies hTiles.2.1
        (atom_subset G s.1 s.2.1 s.2.2) (atom_subset G t.1 t.2.1 t.2.2)
        (G.atoms_disjoint (by trivial) (by trivial) hst)
      rw [← hrSupport s, ← hrSupport t] at hdisj
      exact hdisj.mono (tile_subset_support K hs) (tile_subset_support K ht)
  have hTilesR : TilesOn K G.replacementCentres E := by
    have heq := hRS.trans (regularSupport_eq_of_tilesOn hEopen hEregular hTiles)
    exact heq ▸ tilesOn_regularSupport_of_packing hpR
  have hγ : G.lattice.basis 1 ∈ periodGroup G.replacementCentres :=
    period_iUnion _ _ fun i => period_iUnion _ _ fun a => orbit_period _ _
  have hN : (G.commonMultiple : ℤ) • G.lattice.basis 0 ∈
      periodGroup G.replacementCentres := by
    apply period_iUnion
    intro i
    have hγi : G.lattice.basis 1 ∈
        periodGroup (⋃ a : G.Index i, ⋃ m : ℤ, m • G.lattice.basis 1 +ᵥ G.atom i a 0) :=
      period_iUnion _ _ fun a => orbit_period _ _
    have hwi : G.lambdaCoefficient i • G.lattice.basis 0 +
        G.gammaCoefficient i • G.lattice.basis 1 ∈
        periodGroup (⋃ a : G.Index i, ⋃ m : ℤ, m • G.lattice.basis 1 +ᵥ G.atom i a 0) :=
      period_iUnion _ _ fun a => period_iUnion _ _ fun m =>
        period_vadd (G.atom_periodic i a 0) _
    have hki := (periodGroup (⋃ a : G.Index i,
      ⋃ m : ℤ, m • G.lattice.basis 1 +ᵥ G.atom i a 0)).sub_mem hwi
      ((periodGroup _).zsmul_mem hγi (G.gammaCoefficient i))
    simp only [add_sub_cancel_right] at hki
    obtain ⟨n, hn⟩ := G.commonMultiple_divisible i
    rw [hn, mul_comm, mul_smul]
    exact (periodGroup _).zsmul_mem hki n
  have hIndependent : LinearIndependent ℝ
      ![(G.commonMultiple : ℤ) • G.lattice.basis 0, G.lattice.basis 1] := by
    have hbase : LinearIndependent ℝ ![G.lattice.basis 0, G.lattice.basis 1] := by
      convert G.lattice.independent using 1
      ext j; fin_cases j <;> rfl
    have hn : (G.commonMultiple : ℝ) ≠ 0 := by exact_mod_cast G.commonMultiple_pos.ne'
    have hh := (LinearIndependent.pair_smul_smul_iff (isUnit_iff_ne_zero.mpr hn)
      (isUnit_iff_ne_zero.mpr (one_ne_zero : (1 : ℝ) ≠ 0))).mpr hbase
    rw [← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast]
    simpa only [one_smul] using hh
  have hLattice : IsLatticePeriodic G.replacementCentres := by
    refine ⟨⟨_, hIndependent⟩, ?_⟩
    change AddSubgroup.closure (Set.range
      ![(G.commonMultiple : ℤ) • G.lattice.basis 0, G.lattice.basis 1]) ≤ _
    apply (AddSubgroup.closure_le _).mpr
    rintro u ⟨j, rfl⟩
    fin_cases j
    · exact hN
    · exact hγ
  refine ⟨hTilesR, hLattice, ?_⟩
  have heq := regularSupport_eq_of_tilesOn hEopen hEregular hTilesR
  intro u hu
  change u +ᵥ E = E
  rw [← heq, ← regularSupport_vadd]
  exact congrArg (regularSupport K) hu

private theorem rescalePhase_injective (r : ℕ) (hr : 0 < r) :
    Function.Injective (fun p : ℤ × Fin r => (r : ℤ) * p.1 + (p.2.val : ℤ)) := by
  intro p q hpq
  have hrz : (r : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hdiv := congrArg (fun z : ℤ => z / (r : ℤ)) hpq
  have hpdiv : ((r : ℤ) * p.1 + (p.2.val : ℤ)) / (r : ℤ) = p.1 := by
    have hsmall : (p.2.val : ℤ) / (r : ℤ) = 0 :=
      Int.ediv_eq_zero_of_lt_abs (by exact_mod_cast Nat.zero_le p.2.val)
        (by exact_mod_cast p.2.isLt)
    calc
      ((r : ℤ) * p.1 + (p.2.val : ℤ)) / (r : ℤ) =
          ((p.2.val : ℤ) + (r : ℤ) * p.1) / (r : ℤ) := by congr 1; ring
      _ = (p.2.val : ℤ) / (r : ℤ) + p.1 := Int.add_mul_ediv_left _ _ hrz
      _ = p.1 := by rw [hsmall]; simp
  have hqdiv : ((r : ℤ) * q.1 + (q.2.val : ℤ)) / (r : ℤ) = q.1 := by
    have hsmall : (q.2.val : ℤ) / (r : ℤ) = 0 :=
      Int.ediv_eq_zero_of_lt_abs (by exact_mod_cast Nat.zero_le q.2.val)
        (by exact_mod_cast q.2.isLt)
    calc
      ((r : ℤ) * q.1 + (q.2.val : ℤ)) / (r : ℤ) =
          ((q.2.val : ℤ) + (r : ℤ) * q.1) / (r : ℤ) := by congr 1; ring
      _ = (q.2.val : ℤ) / (r : ℤ) + q.1 := Int.add_mul_ediv_left _ _ hrz
      _ = q.1 := by rw [hsmall]; simp
  have hquot : p.1 = q.1 := by rw [← hpdiv, ← hqdiv, hdiv]
  have hmod := congrArg (fun z : ℤ => z % (r : ℤ)) hpq
  change ((r : ℤ) * p.1 + (p.2.val : ℤ)) % (r : ℤ) =
    ((r : ℤ) * q.1 + (q.2.val : ℤ)) % (r : ℤ) at hmod
  have hpmod : ((r : ℤ) * p.1 + (p.2.val : ℤ)) % (r : ℤ) = p.2.val := by
    calc
      ((r : ℤ) * p.1 + (p.2.val : ℤ)) % (r : ℤ) =
          ((p.2.val : ℤ) + (r : ℤ) * p.1) % (r : ℤ) := by congr 1; ring
      _ = p.2.val % (r : ℤ) := Int.add_mul_emod_self_left _ _ _
      _ = p.2.val := Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le p.2.val)
          (by exact_mod_cast p.2.isLt)
  have hqmod : ((r : ℤ) * q.1 + (q.2.val : ℤ)) % (r : ℤ) = q.2.val := by
    calc
      ((r : ℤ) * q.1 + (q.2.val : ℤ)) % (r : ℤ) =
          ((q.2.val : ℤ) + (r : ℤ) * q.1) % (r : ℤ) := by congr 1; ring
      _ = q.2.val % (r : ℤ) := Int.add_mul_emod_self_left _ _ _
      _ = q.2.val := Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le q.2.val)
          (by exact_mod_cast q.2.isLt)
  have hresZ : (p.2.val : ℤ) = (q.2.val : ℤ) := by
    calc
      (p.2.val : ℤ) =
          ((r : ℤ) * p.1 + (p.2.val : ℤ)) % (r : ℤ) := hpmod.symm
      _ = ((r : ℤ) * q.1 + (q.2.val : ℤ)) % (r : ℤ) := hmod
      _ = (q.2.val : ℤ) := hqmod
  have hres : p.2.val = q.2.val := by exact_mod_cast hresZ
  apply Prod.ext hquot
  exact Fin.ext hres

private theorem rescalePhase_surjective (r : ℕ) (hr : 0 < r) (n : ℤ) :
    ∃ p : ℤ × Fin r, (r : ℤ) * p.1 + (p.2.val : ℤ) = n := by
  have hrz : (r : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hrpos : (0 : ℤ) < r := by exact_mod_cast hr
  let q : ℤ := n / (r : ℤ)
  let rem : ℤ := n % (r : ℤ)
  have hrem0 : 0 ≤ rem := by dsimp [rem]; exact Int.emod_nonneg _ hrz
  have hremLt : rem < (r : ℤ) := by dsimp [rem]; exact Int.emod_lt_of_pos _ hrpos
  let s : Fin r := ⟨rem.toNat, by
    exact (Int.toNat_lt_of_ne_zero (Nat.ne_of_gt hr)).2 (by exact_mod_cast hremLt)⟩
  refine ⟨(q, s), ?_⟩
  dsimp [q, s, rem]
  rw [Int.natCast_toNat_eq_self.mpr (Int.emod_nonneg _ hrz)]
  calc
    (r : ℤ) * (n / (r : ℤ)) + n % (r : ℤ) =
        n % (r : ℤ) + (r : ℤ) * (n / (r : ℤ)) := by ring
    _ = n := Int.emod_add_mul_ediv n (r : ℤ)

/-- Refining each integer orbit into residue classes permits one common scaled basis. -/
theorem rescale_basis {K : PolygonalRegion} {T : Set Plane}
    (G : GoodParametrization K T) (r : ℕ) (hr : 0 < r) :
    ∃ G' : GoodParametrization K T, ∀ j : Fin 2,
      G'.lattice.basis j = (r : ℤ) • G.lattice.basis j := by
  classical
  let b' : Fin 2 → Plane := fun j => (r : ℤ) • G.lattice.basis j
  have hrreal : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hb' : LinearIndependent ℝ b' := by
    have h := G.lattice.independent.units_smul (fun _ : Fin 2 => Units.mk0 (r : ℝ) hrreal)
    have hreal : LinearIndependent ℝ (fun j => (r : ℝ) • G.lattice.basis j) := by
      convert h using 1
      ext j
      simp
    convert hreal using 1
    funext j
    change (r : ℤ) • G.lattice.basis j = (r : ℝ) • G.lattice.basis j
    exact (Int.cast_smul_eq_zsmul ℝ _ _).symm
  let L' : PlanarLattice := ⟨b', hb'⟩
  let phase : ∀ i, G.Index i × Fin r → ℤ → ℤ :=
    fun _ p m => (r : ℤ) * m + (p.2.val : ℤ)
  let f : (Σ i : Fin G.numberOfParts, (G.Index i × Fin r) × ℤ) →
      (Σ i : Fin G.numberOfParts, G.Index i × ℤ) :=
    fun s => ⟨s.1, (s.2.1.1, phase s.1 s.2.1 s.2.2)⟩
  have hf : Function.Injective f := by
    intro s t hst
    cases s with
    | mk i sp =>
      cases t with
      | mk j tp =>
        have hi : i = j := congrArg Sigma.fst hst
        subst j
        rcases sp with ⟨⟨a, s0⟩, m⟩
        rcases tp with ⟨⟨b, t0⟩, n⟩
        have hOld : (a, phase i (a, s0) m) = (b, phase i (b, t0) n) := by
          have hh : HEq (a, phase i (a, s0) m) (b, phase i (b, t0) n) :=
            (Sigma.mk.inj_iff.mp hst).2
          exact eq_of_heq hh
        have hab : a = b := congrArg Prod.fst hOld
        have hphase : phase i (a, s0) m = phase i (b, t0) n := congrArg Prod.snd hOld
        subst b
        have hpq : (m, s0) = (n, t0) :=
          @rescalePhase_injective r hr (m, s0) (n, t0) hphase
        have hm := congrArg Prod.fst hpq
        have hs := congrArg Prod.snd hpq
        change m = n at hm
        change s0 = t0 at hs
        subst n
        subst t0
        rfl
  let atom' : ∀ i, G.Index i × Fin r → ℤ → Set Plane :=
    fun i p m => G.atom i p.1 (phase i p m)
  let G' : GoodParametrization K T := {
    lattice := L'
    numberOfParts := G.numberOfParts
    Index := fun i => G.Index i × Fin r
    atom := atom'
    atom_nonempty := by
      intro i p m
      exact G.atom_nonempty i p.1 (phase i p m)
    atoms_disjoint := by
      intro s hs t ht hst
      have hfst : f s ≠ f t := by
        intro hEq
        apply hst
        exact hf hEq
      simpa [f, atom', phase] using
        (G.atoms_disjoint (Set.mem_univ _) (Set.mem_univ _) hfst)
    union_eq := by
      apply Eq.trans ?_ G.union_eq
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨p, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨m, hx⟩
        simp only [Set.mem_iUnion]
        exact ⟨i, ⟨p.1, ⟨phase i p m, by simpa [atom'] using hx⟩⟩⟩
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨a, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨n, hx⟩
        obtain ⟨p, hp⟩ := rescalePhase_surjective r hr n
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        refine Set.mem_iUnion.mpr ⟨(a, p.2), ?_⟩
        refine Set.mem_iUnion.mpr ⟨p.1, ?_⟩
        simpa [atom', phase, hp] using hx
    lambdaCoefficient := G.lambdaCoefficient
    gammaCoefficient := G.gammaCoefficient
    lambdaCoefficient_ne_zero := G.lambdaCoefficient_ne_zero
    atom_periodic := by
      intro i p m
      have h := G.atom_periodic i p.1 (phase i p m)
      have hmul := (periodGroup (G.atom i p.1 (phase i p m))).zsmul_mem h (r : ℤ)
      simpa [atom', phase, b', L', Int.cast_smul_eq_zsmul,
        zsmul_add, mul_smul, mul_comm, mul_left_comm, mul_assoc] using hmul
    carrier_transport := by
      intro i p m
      change regularSupport K (G.atom i p.1 (phase i p m)) =
        m • L'.basis 1 +ᵥ regularSupport K (G.atom i p.1 (phase i p 0))
      rw [G.carrier_transport i p.1 (phase i p m),
        G.carrier_transport i p.1 (phase i p 0)]
      simp only [phase]
      rw [← add_vadd]
      apply congrArg (fun u : Plane => u +ᵥ regularSupport K (G.atom i p.1 0))
      module
  }
  refine ⟨G', ?_⟩
  intro j
  simp [G', L', b']

end GoodParametrization

/-- Empty families have no atoms and admit the standard lattice parametrization. -/
theorem empty_goodParametrization (K : PolygonalRegion) :
    Nonempty (GoodParametrization K ∅) := by
  classical
  let L : PlanarLattice := ⟨Complex.basisOneI, Complex.basisOneI.linearIndependent⟩
  refine ⟨{
    lattice := L
    numberOfParts := 0
    Index := fun i => Fin.elim0 i
    atom := fun i => Fin.elim0 i
    atom_nonempty := ?_
    atoms_disjoint := ?_
    union_eq := ?_
    lambdaCoefficient := Fin.elim0
    gammaCoefficient := Fin.elim0
    lambdaCoefficient_ne_zero := ?_
    atom_periodic := ?_
    carrier_transport := ?_ }⟩
  · intro i; exact Fin.elim0 i
  · intro s hs t ht hst; exact Fin.elim0 s.1
  · simp
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

/-- A literal centre period preserves the a.e. tiling and hence a regular-open carrier. -/
theorem centrePeriods_le_carrierPeriods
    {K : PolygonalRegion} {T E : Set Plane} (hTiles : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E) :
    periodGroup T ≤ periodGroup E := by
  have heq := regularSupport_eq_of_tilesOn hEopen hEregular hTiles
  intro u hu
  change u +ᵥ E = E
  rw [← heq, ← regularSupport_vadd]
  exact congrArg (regularSupport K) hu

end Tiling.RationalSlopes

namespace Tiling.Polygonal

open Tiling.RationalPolygonal (PolygonalRegion)

/-- The raw column fibre transport is packaged only above SlicesAndColumns, so there
is no geometry-to-parametrization import cycle. -/
theorem unionColumns_goodParametrization
    {K : PolygonalRegion} {T E : Set Plane} {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (hEper : IsLatticePeriodic E) (hcol : IsUnionOfColumns K δ T) :
    Nonempty (Tiling.RationalSlopes.GoodParametrization K T) := by
  classical
  obtain ⟨q, γ, hqδ, hq0, hγδ, hqT, htransport⟩ :=
    unionColumns_has_transverseFibreTransport hδ htile hEopen hEregular hEper hcol
  let orbitSetoid : Setoid T := {
    r := fun s t => ∃ m : ℤ, (s : Plane) - t - m • γ ∈ δ
    iseqv := ⟨?_, ?_, ?_⟩ }
  case refine_1 =>
    intro s
    exact ⟨0, by simp⟩
  case refine_2 =>
    rintro s t ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    convert δ.neg_mem hm using 1
    simp only [neg_smul]
    abel
  case refine_3 =>
    rintro s t u ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    convert δ.add_mem hm hn using 1
    simp only [add_zsmul]
    abel
  let Q := Quotient orbitSetoid
  let f : Q → ℤ → T := fun a m =>
    ⟨(htransport (a.out : Plane) a.out.property m).choose,
      (htransport (a.out : Plane) a.out.property m).choose_spec.1⟩
  have hf (a : Q) (m : ℤ) : (f a m : Plane) - a.out - m • γ ∈ δ ∧
      regularSupport K (lineFibre δ T (f a m)) =
        m • γ +ᵥ regularSupport K (lineFibre δ T a.out) :=
    (htransport (a.out : Plane) a.out.property m).choose_spec.2
  have hγmul (m : ℤ) (hm : m • γ ∈ δ) : m = 0 := by
    by_contra hm0
    have hc : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm0
    apply hγδ
    have hh := δ.smul_mem ((m : ℝ)⁻¹) hm
    simpa only [← Int.cast_smul_eq_zsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul] using hh
  have hIndices (a b : Q) (m n : ℤ) {x : Plane}
      (hx : x ∈ lineFibre δ T (f a m)) (hy : x ∈ lineFibre δ T (f b n)) :
      a = b ∧ m = n := by
    have hft : (f a m : Plane) - f b n ∈ δ := by
      convert δ.sub_mem hy.2 hx.2 using 1
      abel
    have hrel : (a.out : Plane) - b.out - (n - m) • γ ∈ δ := by
      convert δ.add_mem (δ.sub_mem hft (hf a m).1) (hf b n).1 using 1
      simp only [sub_zsmul]
      abel
    have hab : a = b := Quotient.out_equiv_out.mp ⟨n - m, hrel⟩
    subst b
    have hmn : (m - n) • γ ∈ δ := by
      convert δ.sub_mem (δ.sub_mem hft (hf a m).1) (δ.neg_mem (hf a n).1) using 1
      simp only [sub_zsmul]
      abel
    exact ⟨rfl, sub_eq_zero.mp (hγmul _ hmn)⟩
  have hqFibre (t : T) : q ∈ periodGroup (lineFibre δ T t) := by
    change q +ᵥ lineFibre δ T t = lineFibre δ T t
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · exact hqT ▸ (show q +ᵥ y ∈ q +ᵥ T from ⟨y, hy.1, rfl⟩)
      · convert δ.add_mem hqδ hy.2 using 1
        simp only [vadd_eq_add]
        abel
    · intro hx
      refine ⟨(-q) +ᵥ x, ⟨?_, ?_⟩, by simp⟩
      · exact (periodGroup T).neg_mem hqT ▸
          (show (-q) +ᵥ x ∈ (-q) +ᵥ T from ⟨x, hx.1, rfl⟩)
      · convert δ.add_mem (δ.neg_mem hqδ) hx.2 using 1
        simp only [vadd_eq_add]
        abel
  have hIndependent : LinearIndependent ℝ ![q, γ] := by
    apply linearIndependent_fin2.mpr
    change γ ≠ 0 ∧ ∀ a : ℝ, a • γ ≠ q
    constructor
    · intro hγ0; exact hγδ (hγ0 ▸ δ.zero_mem)
    · intro a ha
      by_cases ha0 : a = 0
      · exact hq0 (by simpa [ha0] using ha.symm)
      · apply hγδ
        have hh := δ.smul_mem a⁻¹ hqδ
        rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul] at hh
        exact hh
  refine ⟨{
    lattice := ⟨![q, γ], hIndependent⟩
    numberOfParts := 1
    Index := fun _ => Q
    atom := fun _ a m => lineFibre δ T (f a m)
    atom_nonempty := ?_
    atoms_disjoint := ?_
    union_eq := ?_
    lambdaCoefficient := fun _ => 1
    gammaCoefficient := fun _ => 0
    lambdaCoefficient_ne_zero := ?_
    atom_periodic := ?_
    carrier_transport := ?_ }⟩
  · intro i a m
    exact ⟨f a m, (f a m).property, by simp⟩
  · intro s _ t _ hst
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hab, hmn⟩ := hIndices s.2.1 t.2.1 s.2.2 t.2.2 hx hy
    apply hst
    have hi : s.1 = t.1 := Subsingleton.elim _ _
    cases s with | mk i am =>
      cases t with | mk j bn =>
        dsimp at hi hab hmn
        subst j
        exact congrArg (Sigma.mk i) (Prod.ext hab hmn)
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, a, m, hx⟩
      exact hx.1
    · intro hx
      let a : Q := Quotient.mk orbitSetoid ⟨x, hx⟩
      obtain ⟨m, hm⟩ := orbitSetoid.symm (Quotient.mk_out ⟨x, hx⟩)
      refine ⟨0, a, m, hx, ?_⟩
      convert δ.sub_mem hm (hf a m).1 using 1
      abel
  · intro i; exact one_ne_zero
  · intro i a m
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, zero_smul, add_zero]
      using hqFibre (f a m)
  · intro i a m
    have h0 := (hf a 0).2
    simp only [zero_smul, zero_vadd] at h0
    exact (hf a m).2.trans (congrArg (fun B : Set Plane => m • γ +ᵥ B) h0.symm)

end Tiling.Polygonal

/- Local audit: all project predecessor closures remain provisional until root promotion. -/
