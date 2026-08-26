import Mathlib.Data.Fintype.Pi
import TranslationalTilings.PeriodicCompletion

/-!
# Executable tiling classifiers

This module provides executable encodings of scalar- and lattice-periodic subsets of
`Z²`, instrumented finite searches with exact cost recurrences, tile normalization and
bounded representative tuples, and the chameleon-slice classifier together with its
soundness and completeness theorems.
-/


set_option relaxedAutoImplicit false

open scoped BigOperators Real

/- blueprint/08-algorithms.md:25; TranslationalTilings.BoxResidue -/
namespace TranslationalTilings
/-- Abbreviates the box residue type used by periodic-set codes. -/
abbrev BoxResidue (d q : ℕ) := Fin d → Fin q
end TranslationalTilings

/- blueprint/08-algorithms.md:27; TranslationalTilings.boxPoint -/
namespace TranslationalTilings
/-- Embed a coordinatewise residue vector into the integer lattice using standard
representatives. -/
def boxPoint (x : BoxResidue d q) : Lattice d :=
  fun i ↦ (x i : ℕ)
end TranslationalTilings

/- blueprint/08-algorithms.md:30; TranslationalTilings.PeriodicSetCode -/
namespace TranslationalTilings
/-- A Boolean table on a positive scalar-period fundamental box. -/
structure PeriodicSetCode (d : ℕ) where
  /-- Common period in every coordinate. -/
  period : ℕ
  /-- Positivity of the scalar period. -/
  period_pos : 0 < period
  /-- Membership table on the fundamental residue box. -/
  bits : BoxResidue d period → Bool
deriving DecidableEq
end TranslationalTilings

/- blueprint/08-algorithms.md:36; TranslationalTilings.PeriodicSetCode.memBool -/
namespace TranslationalTilings
/-- Test membership by reducing every lattice coordinate modulo the code period. -/
def PeriodicSetCode.memBool
    (C : PeriodicSetCode d) (x : Lattice d) : Bool :=
  C.bits fun i ↦ ⟨(x i).natMod C.period,
    Int.natMod_lt C.period_pos.ne'⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:41; TranslationalTilings.PeriodicSetCode.toSet -/
namespace TranslationalTilings
/-- The scalar-periodic lattice set represented by a periodic Boolean table. -/
def PeriodicSetCode.toSet (C : PeriodicSetCode d) : Set (Lattice d) :=
  {x | C.memBool x}
end TranslationalTilings

/- blueprint/08-algorithms.md:44; TranslationalTilings.PeriodicSetCode.ofBits -/
namespace TranslationalTilings
/-- Package a Boolean residue table with a specified positive scalar period. -/
def PeriodicSetCode.ofBits (q : ℕ) (hq : 0 < q)
    (bits : BoxResidue d q → Bool) : PeriodicSetCode d :=
  ⟨q, hq, bits⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:48; TranslationalTilings.PeriodicSetCode.univ -/
namespace TranslationalTilings
/-- The code whose represented set is the whole lattice. -/
def PeriodicSetCode.univ (d q : ℕ) (hq : 0 < q) : PeriodicSetCode d :=
  PeriodicSetCode.ofBits q hq fun _ ↦ true
end TranslationalTilings

/- blueprint/08-algorithms.md:51; TranslationalTilings.encodePeriodicSet -/
namespace TranslationalTilings
/-- Record a set on the standard residue representatives for a prescribed period. -/
noncomputable def encodePeriodicSet (q : ℕ) (hq : 0 < q)
    (A : Set (Lattice d)) : PeriodicSetCode d := by
  classical
  exact PeriodicSetCode.ofBits q hq fun r ↦ decide (boxPoint r ∈ A)
end TranslationalTilings

/- blueprint/08-algorithms.md:56; TranslationalTilings.PeriodicSetCode.pullbackTranslate -/
namespace TranslationalTilings
/-- Recode the pullback of a represented set under translation by `a`. -/
def PeriodicSetCode.pullbackTranslate
    (C : PeriodicSetCode d) (a : Lattice d) : PeriodicSetCode d :=
  PeriodicSetCode.ofBits C.period C.period_pos fun r ↦
    C.memBool (boxPoint r + a)
end TranslationalTilings

namespace TranslationalTilings

private theorem boxPoint_natMod_add_ediv (q : ℕ) (hq : 0 < q)
    (x : Lattice d) :
    boxPoint (fun i ↦ ⟨(x i).natMod q, Int.natMod_lt hq.ne'⟩) +
        (q : ℤ) • (fun i ↦ x i / (q : ℤ)) = x := by
  funext i
  simp only [boxPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Int.natMod, Int.toNat_of_nonneg]
  · exact Int.emod_add_mul_ediv (x i) q
  · exact Int.emod_nonneg _ (by exact_mod_cast hq.ne')

/-- The Boolean membership test agrees with membership in the represented set. -/
theorem PeriodicSetCode.memBool_eq_true_iff
    (C : PeriodicSetCode d) (x) :
    C.memBool x = true ↔ x ∈ C.toSet :=
  Iff.rfl

/-- The set represented by a code is periodic by its period times every lattice vector. -/
theorem PeriodicSetCode.toSet_scalarPeriodic (C : PeriodicSetCode d) :
    SetScalarPeriodic C.period C.toSet := by
  intro x z
  change C.memBool (x + (C.period : ℤ) • z) = true ↔ C.memBool x = true
  have hresidue :
      (fun i : Fin d ↦
        (⟨((x + (C.period : ℤ) • z) i).natMod C.period,
          Int.natMod_lt C.period_pos.ne'⟩ : Fin C.period)) =
      (fun i : Fin d ↦
        (⟨(x i).natMod C.period,
          Int.natMod_lt C.period_pos.ne'⟩ : Fin C.period)) := by
    funext i
    apply Fin.ext
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.natMod]
    rw [Int.add_emod]
    simp
  change C.bits _ = true ↔ C.bits _ = true
  rw [hresidue]

/-- Encoding a set already scalar-periodic by `q` recovers that set exactly. -/
theorem encodePeriodicSet_toSet
    (q : ℕ) (hq : 0 < q) (A : Set (Lattice d))
    (hA : SetScalarPeriodic q A) :
    (encodePeriodicSet q hq A).toSet = A := by
  classical
  ext x
  let r : BoxResidue d q :=
    fun i ↦ ⟨(x i).natMod q, Int.natMod_lt hq.ne'⟩
  let z : Lattice d := fun i ↦ x i / (q : ℤ)
  have hx : boxPoint r + (q : ℤ) • z = x :=
    boxPoint_natMod_add_ediv q hq x
  change decide (boxPoint r ∈ A) = true ↔ x ∈ A
  rw [decide_eq_true_eq, ← hx]
  exact (hA (boxPoint r) z).symm

/-- Pullback translation represents exactly the points whose translate lies in the original set. -/
theorem PeriodicSetCode.pullbackTranslate_toSet
    (C : PeriodicSetCode d) (a : Lattice d) :
    (C.pullbackTranslate a).toSet = {x | x + a ∈ C.toSet} := by
  ext x
  let r : BoxResidue d C.period :=
    fun i ↦ ⟨(x i).natMod C.period,
      Int.natMod_lt C.period_pos.ne'⟩
  let z : Lattice d := fun i ↦ x i / (C.period : ℤ)
  have hx : boxPoint r + (C.period : ℤ) • z = x :=
    boxPoint_natMod_add_ediv C.period C.period_pos x
  change boxPoint r + a ∈ C.toSet ↔ x + a ∈ C.toSet
  have hp := C.toSet_scalarPeriodic (boxPoint r + a) z
  convert hp.symm using 1
  rw [← hx]
  abel_nf

end TranslationalTilings

/- blueprint/08-algorithms.md:102; TranslationalTilings.LatticePeriodicSetCode -/
namespace TranslationalTilings
/-- A Boolean table for a planar lattice generated by a horizontal period and a sheared
vertical period. -/
structure LatticePeriodicSetCode where
  /-- Positive horizontal period. -/
  horizontalPeriod : ℕ
  /-- Positivity of the horizontal period. -/
  horizontal_pos : 0 < horizontalPeriod
  /-- Horizontal shear of the vertical generator. -/
  shear : ℤ
  /-- The chosen shear representative is nonnegative. -/
  shear_nonneg : 0 ≤ shear
  /-- The shear is reduced modulo the horizontal period. -/
  shear_lt_horizontal : shear < horizontalPeriod
  /-- Positive vertical period. -/
  verticalPeriod : ℕ
  /-- Positivity of the vertical period. -/
  vertical_pos : 0 < verticalPeriod
  /-- Membership table on the resulting finite planar quotient. -/
  bits : Fin horizontalPeriod → Fin verticalPeriod → Bool
deriving DecidableEq
end TranslationalTilings

/- blueprint/08-algorithms.md:113;
TranslationalTilings.LatticePeriodicSetCode.horizontalGenerator -/
namespace TranslationalTilings
/-- The horizontal generator `(horizontalPeriod, 0)` of the period lattice. -/
def LatticePeriodicSetCode.horizontalGenerator
    (C : LatticePeriodicSetCode) : Plane :=
  ![(C.horizontalPeriod : ℤ), 0]
end TranslationalTilings

/- blueprint/08-algorithms.md:117; TranslationalTilings.LatticePeriodicSetCode.verticalGenerator -/
namespace TranslationalTilings
/-- The sheared vertical generator `(shear, verticalPeriod)` of the period lattice. -/
def LatticePeriodicSetCode.verticalGenerator
    (C : LatticePeriodicSetCode) : Plane :=
  ![C.shear, (C.verticalPeriod : ℤ)]
end TranslationalTilings

/- blueprint/08-algorithms.md:121; TranslationalTilings.LatticePeriodicSetCode.periodLattice -/
namespace TranslationalTilings
/-- The additive lattice generated by the horizontal and sheared vertical periods. -/
def LatticePeriodicSetCode.periodLattice
    (C : LatticePeriodicSetCode) : AddSubgroup Plane :=
  AddSubgroup.closure
    ({C.horizontalGenerator, C.verticalGenerator} : Set Plane)
end TranslationalTilings

/- blueprint/08-algorithms.md:126; TranslationalTilings.LatticePeriodicSetCode.memBool -/
namespace TranslationalTilings
/-- Reduce a planar point to the sheared fundamental parallelogram and consult its bit. -/
def LatticePeriodicSetCode.memBool
    (C : LatticePeriodicSetCode) (x : Plane) : Bool :=
  let verticalQuotient : ℤ := x 1 / (C.verticalPeriod : ℤ)
  C.bits
    ⟨(x 0 - verticalQuotient * C.shear).natMod C.horizontalPeriod,
      Int.natMod_lt C.horizontal_pos.ne'⟩
    ⟨(x 1).natMod C.verticalPeriod,
      Int.natMod_lt C.vertical_pos.ne'⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:135; TranslationalTilings.LatticePeriodicSetCode.toSet -/
namespace TranslationalTilings
/-- The planar set represented by a lattice-periodic Boolean table. -/
def LatticePeriodicSetCode.toSet (C : LatticePeriodicSetCode) : Set Plane :=
  {x | C.memBool x}
end TranslationalTilings

/- blueprint/08-algorithms.md:138; TranslationalTilings.LatticePeriodicSetCode.scalarPeriod -/
namespace TranslationalTilings
/-- A scalar period contained in the coded period lattice. -/
def LatticePeriodicSetCode.scalarPeriod
    (C : LatticePeriodicSetCode) : ℕ :=
  C.horizontalPeriod * C.verticalPeriod
end TranslationalTilings

/- blueprint/08-algorithms.md:142; TranslationalTilings.LatticePeriodicSetCode.toScalarCode -/
namespace TranslationalTilings
/-- Convert a lattice-periodic code to a scalar-periodic table of product period. -/
def LatticePeriodicSetCode.toScalarCode
    (C : LatticePeriodicSetCode) : PeriodicSetCode 2 :=
  PeriodicSetCode.ofBits C.scalarPeriod
    (Nat.mul_pos C.horizontal_pos C.vertical_pos) fun r ↦
      C.memBool (boxPoint r)
end TranslationalTilings

namespace TranslationalTilings

private theorem LatticePeriodicSetCode.memBool_add_horizontal
    (C : LatticePeriodicSetCode) (x : Plane) :
    C.memBool (x + C.horizontalGenerator) = C.memBool x := by
  simp only [LatticePeriodicSetCode.memBool,
    LatticePeriodicSetCode.horizontalGenerator, Pi.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
  congr 2
  · simp only [Int.natMod]
    congr 1
    rw [show x 0 + (C.horizontalPeriod : ℤ) -
        x 1 / (C.verticalPeriod : ℤ) * C.shear =
      (x 0 - x 1 / (C.verticalPeriod : ℤ) * C.shear) +
        C.horizontalPeriod by ring]
    rw [Int.add_emod]
    simp

private theorem LatticePeriodicSetCode.memBool_add_vertical
    (C : LatticePeriodicSetCode) (x : Plane) :
    C.memBool (x + C.verticalGenerator) = C.memBool x := by
  have hc : (C.verticalPeriod : ℤ) ≠ 0 := by
    exact_mod_cast C.vertical_pos.ne'
  have hdiv :
      (x 1 + (C.verticalPeriod : ℤ)) / (C.verticalPeriod : ℤ) =
        x 1 / (C.verticalPeriod : ℤ) + 1 := by
    simpa only [one_mul] using
      Int.add_mul_ediv_right (x 1) 1 hc
  simp only [LatticePeriodicSetCode.memBool,
    LatticePeriodicSetCode.verticalGenerator, Pi.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, hdiv]
  congr 2
  · simp only [Int.natMod]
    congr 1
    ring_nf
  · simp only [Int.natMod]
    congr 1
    rw [Int.add_emod]
    simp

/-- Membership in the represented set is invariant under the full coded period lattice. -/
theorem LatticePeriodicSetCode.toSet_periodic
    (C : LatticePeriodicSetCode) :
    SetPeriodicOn C.periodLattice C.toSet := by
  intro h hh
  change ∀ x, C.memBool (x + h) = true ↔ C.memBool x = true
  suffices hp : ∀ x, C.memBool (x + h) = C.memBool x by
    intro x
    rw [hp]
  induction hh using AddSubgroup.closure_induction with
  | mem h hh =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with rfl | rfl
      · exact C.memBool_add_horizontal
      · exact C.memBool_add_vertical
  | zero => simp
  | add u v _hu _hv ihu ihv =>
      intro x
      rw [show x + (u + v) = (x + u) + v by abel, ihv, ihu]
  | neg u _hu ihu =>
      intro x
      have hp := (ihu (x - u)).symm
      convert hp using 1 <;> abel_nf

/-- The scalar lattice of product period is contained in the coded planar period lattice. -/
theorem LatticePeriodicSetCode.scalarLattice_le
    (C : LatticePeriodicSetCode) :
    scalarLattice C.scalarPeriod ≤ C.periodLattice := by
  rintro x ⟨z, rfl⟩
  have hh : C.horizontalGenerator ∈ C.periodLattice :=
    AddSubgroup.subset_closure (by simp)
  have hv : C.verticalGenerator ∈ C.periodLattice :=
    AddSubgroup.subset_closure (by simp)
  have hm := C.periodLattice.add_mem
    (C.periodLattice.zsmul_mem
      hh ((C.verticalPeriod : ℤ) * z 0 - C.shear * z 1))
    (C.periodLattice.zsmul_mem hv ((C.horizontalPeriod : ℤ) * z 1))
  convert hm using 1
  funext i
  fin_cases i <;>
    simp [LatticePeriodicSetCode.scalarPeriod,
      LatticePeriodicSetCode.horizontalGenerator,
      LatticePeriodicSetCode.verticalGenerator, Pi.smul_apply,
      ] <;> ring

/-- Scalar recoding preserves the represented planar set exactly. -/
theorem LatticePeriodicSetCode.toScalarCode_toSet
    (C : LatticePeriodicSetCode) :
    C.toScalarCode.toSet = C.toSet := by
  have hscalar : SetScalarPeriodic C.scalarPeriod C.toSet := by
    intro x z
    exact C.toSet_periodic _ (C.scalarLattice_le ⟨z, rfl⟩) x
  ext x
  let r : BoxResidue 2 C.scalarPeriod := fun i ↦
    ⟨(x i).natMod C.scalarPeriod,
      Int.natMod_lt (Nat.mul_pos C.horizontal_pos C.vertical_pos).ne'⟩
  let z : Plane := fun i ↦ x i / (C.scalarPeriod : ℤ)
  have hx : boxPoint r + (C.scalarPeriod : ℤ) • z = x :=
    boxPoint_natMod_add_ediv C.scalarPeriod
      (Nat.mul_pos C.horizontal_pos C.vertical_pos) x
  change C.memBool (boxPoint r) = true ↔ C.memBool x = true
  rw [← hx]
  exact (hscalar (boxPoint r) z).symm

/-- Every set periodic under a finite-index planar lattice admits a finite lattice-periodic code. -/
theorem exists_latticePeriodicSetCode_of_finite_quotient
    (Λ : AddSubgroup Plane) [Finite (Plane ⧸ Λ)]
    (E : Set Plane) (hE : SetPeriodicOn Λ E) :
    ∃ C : LatticePeriodicSetCode,
      C.periodLattice = Λ ∧ C.toSet = E := by
  classical
  have hindex : 0 < Λ.index := Nat.card_pos
  have hexA : ∃ n : ℕ, 0 < n ∧ (![(n : ℤ), 0] : Plane) ∈ Λ := by
    refine ⟨Λ.index, hindex, ?_⟩
    simpa using
      Λ.nsmul_index_mem (![(1 : ℤ), 0] : Plane)
  let a := Nat.find hexA
  have ha : 0 < a := (Nat.find_spec hexA).1
  have hha : (![(a : ℤ), 0] : Plane) ∈ Λ := (Nat.find_spec hexA).2
  have hexC : ∃ n : ℕ, 0 < n ∧
      ∃ b : ℤ, (![b, (n : ℤ)] : Plane) ∈ Λ := by
    refine ⟨Λ.index, hindex, 0, ?_⟩
    simpa using
      Λ.nsmul_index_mem (![(0 : ℤ), 1] : Plane)
  let c := Nat.find hexC
  have hc : 0 < c := (Nat.find_spec hexC).1
  obtain ⟨b₀, hb₀⟩ := (Nat.find_spec hexC).2
  let b : ℤ := b₀ % (a : ℤ)
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have hbnonneg : 0 ≤ b := Int.emod_nonneg _ haZ.ne'
  have hblt : b < a := Int.emod_lt_of_pos _ haZ
  have hbrem : b + (a : ℤ) * (b₀ / (a : ℤ)) = b₀ := by
    exact Int.emod_add_mul_ediv b₀ (a : ℤ)
  have hhb : (![b, (c : ℤ)] : Plane) ∈ Λ := by
    have hsub := Λ.sub_mem hb₀
      (Λ.zsmul_mem hha (b₀ / (a : ℤ)))
    convert hsub using 1
    funext i
    fin_cases i
    · change b = b₀ - (b₀ / (a : ℤ)) * a
      nlinarith [hbrem]
    · dsimp only [c]
      simp
  let C : LatticePeriodicSetCode := {
    horizontalPeriod := a
    horizontal_pos := ha
    shear := b
    shear_nonneg := hbnonneg
    shear_lt_horizontal := hblt
    verticalPeriod := c
    vertical_pos := hc
    bits := fun i j ↦ decide ((![(i : ℕ), (j : ℕ)] : Plane) ∈ E)
  }
  have hperiod : C.periodLattice = Λ := by
    apply le_antisymm
    · rw [LatticePeriodicSetCode.periodLattice, AddSubgroup.closure_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · simpa [C, LatticePeriodicSetCode.horizontalGenerator] using hha
      · simpa [C, LatticePeriodicSetCode.verticalGenerator] using hhb
    · intro x hx
      let qv : ℤ := x 1 / (c : ℤ)
      let rvZ : ℤ := x 1 % (c : ℤ)
      have hrvnonneg : 0 ≤ rvZ := Int.emod_nonneg _ (by exact_mod_cast hc.ne')
      have hrvltZ : rvZ < c := Int.emod_lt_of_pos _ (by exact_mod_cast hc)
      let rv : ℕ := rvZ.toNat
      have hrvcast : (rv : ℤ) = rvZ := by
        exact Int.toNat_of_nonneg hrvnonneg
      let y : Plane := x - qv • (![b, (c : ℤ)] : Plane)
      have hy : y ∈ Λ := Λ.sub_mem hx (Λ.zsmul_mem hhb qv)
      have hy1 : y 1 = rvZ := by
        change x 1 - qv * (c : ℤ) = rvZ
        dsimp only [qv, rvZ]
        have hmod := Int.emod_add_mul_ediv (x 1) (c : ℤ)
        ring_nf at hmod ⊢
        omega
      have hrvzero : rvZ = 0 := by
        by_contra hne
        have hrvpos : 0 < rv := by
          rw [Nat.pos_iff_ne_zero]
          intro hz
          apply hne
          rw [← hrvcast, hz]
          rfl
        have hcandidate : 0 < rv ∧
            ∃ d : ℤ, (![d, (rv : ℤ)] : Plane) ∈ Λ := by
          refine ⟨hrvpos, y 0, ?_⟩
          convert hy using 1
          funext i
          fin_cases i
          · rfl
          · change (rv : ℤ) = y 1
            rw [hrvcast, hy1]
        have hmin := Nat.find_min' hexC hcandidate
        have hrvlt : rv < c := by
          rw [← hrvcast] at hrvltZ
          exact_mod_cast hrvltZ
        exact (Nat.not_lt_of_ge hmin) hrvlt
      have hy1zero : y 1 = 0 := hy1.trans hrvzero
      let qh : ℤ := y 0 / (a : ℤ)
      let rhZ : ℤ := y 0 % (a : ℤ)
      have hrhnonneg : 0 ≤ rhZ := Int.emod_nonneg _ haZ.ne'
      have hrhltZ : rhZ < a := Int.emod_lt_of_pos _ haZ
      let rh : ℕ := rhZ.toNat
      have hrhcast : (rh : ℤ) = rhZ := Int.toNat_of_nonneg hrhnonneg
      let w : Plane := y - qh • (![(a : ℤ), 0] : Plane)
      have hw : w ∈ Λ := Λ.sub_mem hy (Λ.zsmul_mem hha qh)
      have hw0 : w 0 = rhZ := by
        change y 0 - qh * (a : ℤ) = rhZ
        dsimp only [qh, rhZ]
        have hmod := Int.emod_add_mul_ediv (y 0) (a : ℤ)
        ring_nf at hmod ⊢
        omega
      have hw1 : w 1 = 0 := by
        change y 1 - qh * 0 = 0
        simp only [mul_zero, sub_zero, hy1zero]
      have hrhzero : rhZ = 0 := by
        by_contra hne
        have hrhpos : 0 < rh := by
          rw [Nat.pos_iff_ne_zero]
          intro hz
          apply hne
          rw [← hrhcast, hz]
          rfl
        have hcandidate : 0 < rh ∧ (![(rh : ℤ), 0] : Plane) ∈ Λ := by
          refine ⟨hrhpos, ?_⟩
          convert hw using 1
          funext i
          fin_cases i
          · change (rh : ℤ) = w 0
            rw [hrhcast, hw0]
          · change (0 : ℤ) = w 1
            rw [hw1]
        have hmin := Nat.find_min' hexA hcandidate
        have hrhlt : rh < a := by
          rw [← hrhcast] at hrhltZ
          exact_mod_cast hrhltZ
        exact (Nat.not_lt_of_ge hmin) hrhlt
      have hwzero : w = 0 := by
        funext i
        fin_cases i
        · change w 0 = (0 : Plane) 0
          simp only [Pi.zero_apply, hw0, hrhzero]
        · change w 1 = (0 : Plane) 1
          simp only [Pi.zero_apply, hw1]
      have hydecomp : y = qh • (![(a : ℤ), 0] : Plane) := by
        exact sub_eq_zero.mp (by simpa only [w] using hwzero)
      have hxsplit : x = y + qv • (![b, (c : ℤ)] : Plane) := by
        dsimp only [y]
        abel
      have hdecomp :
          x = qh • (![(a : ℤ), 0] : Plane) +
            qv • (![b, (c : ℤ)] : Plane) := by
        rw [hxsplit, hydecomp]
      rw [hdecomp]
      exact C.periodLattice.add_mem
        (C.periodLattice.zsmul_mem
          (AddSubgroup.subset_closure (by simp [C,
            LatticePeriodicSetCode.horizontalGenerator])) qh)
        (C.periodLattice.zsmul_mem
          (AddSubgroup.subset_closure (by simp [C,
            LatticePeriodicSetCode.verticalGenerator])) qv)
  refine ⟨C, hperiod, ?_⟩
  ext x
  let qv : ℤ := x 1 / (c : ℤ)
  let r1 : Fin c := ⟨(x 1).natMod c, Int.natMod_lt hc.ne'⟩
  let u : ℤ := x 0 - qv * b
  let qh : ℤ := u / (a : ℤ)
  let r0 : Fin a := ⟨u.natMod a, Int.natMod_lt ha.ne'⟩
  let y : Plane := ![(r0 : ℕ), (r1 : ℕ)]
  let shift : Plane := qh • (![(a : ℤ), 0] : Plane) +
    qv • (![b, (c : ℤ)] : Plane)
  have hxy : y + shift = x := by
    funext i
    fin_cases i
    · change ((u.natMod a : ℕ) : ℤ) +
          (qh * (a : ℤ) + qv * b) = x 0
      rw [Int.natMod]
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ haZ.ne')]
      have hmod := Int.emod_add_mul_ediv u (a : ℤ)
      dsimp only [u, qh, qv] at hmod ⊢
      ring_nf at hmod ⊢
      omega
    · change ((x 1).natMod c : ℕ) + (qh * 0 + qv * (c : ℤ)) = x 1
      rw [Int.natMod]
      rw [Int.toNat_of_nonneg
        (Int.emod_nonneg _ (by exact_mod_cast hc.ne'))]
      have hmod := Int.emod_add_mul_ediv (x 1) (c : ℤ)
      dsimp only [qv]
      ring_nf at hmod ⊢
      omega
  have hshift : shift ∈ Λ := by
    rw [← hperiod]
    exact C.periodLattice.add_mem
      (C.periodLattice.zsmul_mem
        (AddSubgroup.subset_closure (by simp [C,
          LatticePeriodicSetCode.horizontalGenerator])) qh)
      (C.periodLattice.zsmul_mem
        (AddSubgroup.subset_closure (by simp [C,
          LatticePeriodicSetCode.verticalGenerator])) qv)
  change decide (y ∈ E) = true ↔ x ∈ E
  rw [decide_eq_true_eq, ← hxy]
  exact (hE shift hshift y).symm

end TranslationalTilings

/- blueprint/08-algorithms.md:195; TranslationalTilings.countedOr -/
namespace TranslationalTilings
/-- Combine two counted Boolean computations by OR, charging one operation for the connective. -/
def countedOr (a b : Bool × ℕ) : Bool × ℕ :=
  (a.1 || b.1, a.2 + b.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:198; <instance@blueprint/08-algorithms.md:198> -/
namespace TranslationalTilings
instance : Std.Commutative countedOr :=
  ⟨by intro a b; simp only [countedOr]; ext <;>
    simp [Bool.or_comm, Nat.add_comm]⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:202; <instance@blueprint/08-algorithms.md:202> -/
namespace TranslationalTilings
instance : Std.Associative countedOr :=
  ⟨by
    intro a b c
    apply Prod.ext
    · simp [countedOr, Bool.or_assoc]
    · simp [countedOr]
      omega⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:210; TranslationalTilings.countedAnd -/
namespace TranslationalTilings
/-- Combine two counted Boolean computations by AND, charging one operation for the connective. -/
def countedAnd (a b : Bool × ℕ) : Bool × ℕ :=
  (a.1 && b.1, a.2 + b.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:213; <instance@blueprint/08-algorithms.md:213> -/
namespace TranslationalTilings
instance : Std.Commutative countedAnd :=
  ⟨by intro a b; simp only [countedAnd]; ext <;>
    simp [Bool.and_comm, Nat.add_comm]⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:217; <instance@blueprint/08-algorithms.md:217> -/
namespace TranslationalTilings
instance : Std.Associative countedAnd :=
  ⟨by
    intro a b c
    apply Prod.ext
    · simp [countedAnd, Bool.and_assoc]
    · simp [countedAnd]
      omega⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:225; TranslationalTilings.countedAdd -/
namespace TranslationalTilings
/-- Add the values and costs of two counted natural-number computations, with one addition
charge. -/
def countedAdd (a b : ℕ × ℕ) : ℕ × ℕ :=
  (a.1 + b.1, a.2 + b.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:228; <instance@blueprint/08-algorithms.md:228> -/
namespace TranslationalTilings
instance : Std.Commutative countedAdd :=
  ⟨by intro a b; simp only [countedAdd]; ext <;> omega⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:231; <instance@blueprint/08-algorithms.md:231> -/
namespace TranslationalTilings
instance : Std.Associative countedAdd :=
  ⟨by intro a b c; simp only [countedAdd]; ext <;> omega⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:234; TranslationalTilings.countedAny -/
namespace TranslationalTilings
/-- Return the OR of a finite family together with its explicit fold cost. -/
def countedAny (s : Finset α) (p : α → Bool × ℕ) : Bool × ℕ :=
  s.fold countedOr (false, 1) p
end TranslationalTilings

/- blueprint/08-algorithms.md:237; TranslationalTilings.countedAll -/
namespace TranslationalTilings
/-- Return the AND of a finite family together with its explicit fold cost. -/
def countedAll (s : Finset α) (p : α → Bool × ℕ) : Bool × ℕ :=
  s.fold countedAnd (true, 1) p
end TranslationalTilings

/- blueprint/08-algorithms.md:240; TranslationalTilings.countedCount -/
namespace TranslationalTilings
/-- Count the successful predicates in a finite family and record the exact evaluation cost. -/
def countedCount (s : Finset α) (p : α → Bool × ℕ) : ℕ × ℕ :=
  s.fold countedAdd (0, 1) fun x ↦
    let r := p x
    (if r.1 then 1 else 0, r.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:245; TranslationalTilings.finsetAnyBool -/
namespace TranslationalTilings
/-- Decide whether a Boolean predicate succeeds at some element of a finite set. -/
def finsetAnyBool (s : Finset α) (p : α → Bool) : Bool :=
  (countedAny s fun x ↦ (p x, 0)).1
end TranslationalTilings

/- blueprint/08-algorithms.md:248; TranslationalTilings.finsetAllBool -/
namespace TranslationalTilings
/-- Decide whether a Boolean predicate succeeds at every element of a finite set. -/
def finsetAllBool (s : Finset α) (p : α → Bool) : Bool :=
  (countedAll s fun x ↦ (p x, 0)).1
end TranslationalTilings

/- blueprint/08-algorithms.md:251; TranslationalTilings.PeriodicSetCode.isEmptyBool -/
namespace TranslationalTilings
/-- Decide whether every bit in a periodic-set fundamental box is false. -/
def PeriodicSetCode.isEmptyBool (C : PeriodicSetCode d) : Bool :=
  finsetAllBool (Finset.univ : Finset (BoxResidue d C.period)) fun r ↦
    !C.bits r
end TranslationalTilings

namespace TranslationalTilings

private theorem countedAny_fst_eq_true_iff
    (s : Finset α) (p : α → Bool × ℕ) :
    (countedAny s p).1 = true ↔ ∃ x ∈ s, (p x).1 = true := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [countedAny]
  | @insert a s ha ih =>
      rw [countedAny, Finset.fold_insert ha]
      simp only [countedOr, Bool.or_eq_true]
      change (p a).1 = true ∨ (countedAny s p).1 = true ↔ _
      rw [ih]
      simp only [Finset.mem_insert]
      aesop

private theorem countedAll_fst_eq_true_iff
    (s : Finset α) (p : α → Bool × ℕ) :
    (countedAll s p).1 = true ↔ ∀ x ∈ s, (p x).1 = true := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [countedAll]
  | @insert a s ha ih =>
      rw [countedAll, Finset.fold_insert ha]
      simp only [countedAnd, Bool.and_eq_true]
      change (p a).1 = true ∧ (countedAll s p).1 = true ↔ _
      rw [ih]
      simp only [Finset.mem_insert]
      aesop

private theorem countedAll_cost
    (s : Finset α) (p : α → Bool × ℕ) :
    (countedAll s p).2 = 1 + ∑ x ∈ s, ((p x).2 + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [countedAll]
  | @insert a s ha ih =>
      rw [countedAll, Finset.fold_insert ha]
      change (p a).2 + (countedAll s p).2 + 1 = _
      rw [Finset.sum_insert ha, ih]
      omega

private theorem countedCount_fst
    (s : Finset α) (p : α → Bool × ℕ) :
    (countedCount s p).1 = (s.filter fun x ↦ (p x).1 = true).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [countedCount]
  | @insert a s ha ih =>
      rw [countedCount, Finset.fold_insert ha]
      change (if (p a).1 then 1 else 0) + (countedCount s p).1 = _
      rw [ih]
      by_cases hpa : (p a).1 = true
      · simp [Finset.filter_insert, hpa, ha]
        omega
      · simp [Finset.filter_insert, hpa]

private theorem countedCount_cost
    (s : Finset α) (p : α → Bool × ℕ) :
    (countedCount s p).2 = 1 + ∑ x ∈ s, ((p x).2 + 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [countedCount]
  | @insert a s ha ih =>
      rw [countedCount, Finset.fold_insert ha]
      change ((p a).2 + 1) + (countedCount s p).2 + 1 = _
      rw [Finset.sum_insert ha, ih]
      omega

private theorem finsetAnyBool_eq_true_iff
    (s : Finset α) (p : α → Bool) :
    finsetAnyBool s p = true ↔ ∃ x ∈ s, p x = true := by
  classical
  simpa only [finsetAnyBool] using
    countedAny_fst_eq_true_iff s (fun x ↦ (p x, 0))

private theorem finsetAllBool_eq_true_iff
    (s : Finset α) (p : α → Bool) :
    finsetAllBool s p = true ↔ ∀ x ∈ s, p x = true := by
  classical
  simpa only [finsetAllBool] using
    countedAll_fst_eq_true_iff s (fun x ↦ (p x, 0))

end TranslationalTilings

/- blueprint/08-algorithms.md:255; TranslationalTilings.PeriodicSetCode.memCounted -/
namespace TranslationalTilings
/-- Return coded membership and charge the coordinate-reduction cost `d + 1`. -/
def PeriodicSetCode.memCounted
    (C : PeriodicSetCode d) (x : Lattice d) : Bool × ℕ :=
  (C.memBool x, d + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:259; TranslationalTilings.periodicTileCountCounted -/
namespace TranslationalTilings
/-- Count tile translates covering one point in a coded complement, with an explicit cost. -/
def periodicTileCountCounted (F : Finset (Lattice d))
    (C : PeriodicSetCode d) (x : Lattice d) : ℕ × ℕ :=
  countedCount F
    (fun f ↦
      let r := C.memCounted (x - f)
      (r.1, r.2 + d))
end TranslationalTilings

/- blueprint/08-algorithms.md:266; TranslationalTilings.periodicTilingPointCounted -/
namespace TranslationalTilings
/-- Check the tiling equation at one lattice point and return its operation count. -/
def periodicTilingPointCounted (F : Finset (Lattice d))
    (A E : PeriodicSetCode d) (x : Lattice d) : Bool × ℕ :=
  let lhs := periodicTileCountCounted F A x
  let rhs := E.memCounted x
  (decide (lhs.1 = if rhs.1 then 1 else 0), lhs.2 + rhs.2 + 2)
end TranslationalTilings

/- blueprint/08-algorithms.md:272; TranslationalTilings.commonCodePeriod -/
namespace TranslationalTilings
/-- The least common scalar period of two periodic-set codes. -/
def commonCodePeriod (A E : PeriodicSetCode d) : ℕ :=
  Nat.lcm A.period E.period
end TranslationalTilings

namespace TranslationalTilings
/-- The least common period of two positive code periods is positive. -/
theorem commonCodePeriod_pos (A E : PeriodicSetCode d) :
    0 < commonCodePeriod A E :=
  Nat.lcm_pos A.period_pos E.period_pos
end TranslationalTilings

/- blueprint/08-algorithms.md:279; TranslationalTilings.tilesPeriodicTargetCounted -/
namespace TranslationalTilings
/-- Check the tiling equation on a full common-period fundamental box, recording total cost. -/
def tilesPeriodicTargetCounted (F : Finset (Lattice d))
    (A E : PeriodicSetCode d) : Bool × ℕ :=
  let q := commonCodePeriod A E
  let points : Finset (BoxResidue d q) := Finset.univ
  countedAll points
    (fun x ↦ periodicTilingPointCounted F A E (boxPoint x))
end TranslationalTilings

/- blueprint/08-algorithms.md:286; TranslationalTilings.tilesPeriodicTargetBool -/
namespace TranslationalTilings
/-- Boolean projection of the finite fundamental-box tiling check. -/
def tilesPeriodicTargetBool (F : Finset (Lattice d))
    (A E : PeriodicSetCode d) : Bool :=
  (tilesPeriodicTargetCounted F A E).1
end TranslationalTilings

/- blueprint/08-algorithms.md:290; TranslationalTilings.periodicCandidateCheckCost -/
namespace TranslationalTilings
/-- Closed operation count for checking a period-`q` candidate in dimension `d`. -/
def periodicCandidateCheckCost (d tileCard q : ℕ) : ℕ :=
  q ^ d * (tileCard * (2 * d + 3) + d + 5) + 1
end TranslationalTilings

namespace TranslationalTilings

private theorem PeriodicSetCode.memBool_boxPoint
    (C : PeriodicSetCode d) (r : BoxResidue d C.period) :
    C.memBool (boxPoint r) = C.bits r := by
  unfold PeriodicSetCode.memBool
  congr 1
  funext i
  apply Fin.ext
  simp only [boxPoint, Int.natMod]
  rw [Int.emod_eq_of_lt]
  · simp
  · exact Int.natCast_nonneg _
  · exact_mod_cast (r i).isLt

private theorem setScalarPeriodic_of_dvd {p q : ℕ} {A : Set (Lattice d)}
    (hpq : p ∣ q) (hA : SetScalarPeriodic p A) :
    SetScalarPeriodic q A := by
  obtain ⟨m, rfl⟩ := hpq
  intro x z
  have h := hA x ((m : ℤ) • z)
  simpa only [Nat.cast_mul, mul_smul] using h

private theorem periodicTileCountCounted_fst
    (F : Finset (Lattice d)) (C : PeriodicSetCode d) (x : Lattice d) :
    (periodicTileCountCounted F C x).1 =
      (@Finset.filter _ (fun f ↦ x - f ∈ C.toSet)
        (fun _ ↦ Classical.propDecidable _) F).card := by
  classical
  unfold periodicTileCountCounted
  simp only [PeriodicSetCode.memCounted]
  rw [countedCount_fst]
  rw [Finset.filter_congr_decidable]
  apply congrArg Finset.card
  ext f
  simp only [Finset.mem_filter]
  rw [PeriodicSetCode.memBool_eq_true_iff]

private theorem periodicTileCountCounted_cost_exact
    (F : Finset (Lattice d)) (C : PeriodicSetCode d) (x : Lattice d) :
    (periodicTileCountCounted F C x).2 =
      1 + F.card * (2 * d + 3) := by
  classical
  unfold periodicTileCountCounted
  rw [countedCount_cost]
  simp only [PeriodicSetCode.memCounted, Finset.sum_const,
    nsmul_eq_mul]
  congr 1
  congr 1
  omega

private theorem periodicTilingPointCounted_fst_eq_true_iff
    (F : Finset (Lattice d)) (A E : PeriodicSetCode d) (x : Lattice d) :
    (periodicTilingPointCounted F A E x).1 = true ↔
      (@Finset.filter _ (fun f ↦ x - f ∈ A.toSet)
        (fun _ ↦ Classical.propDecidable _) F).card =
        @ite ℕ (x ∈ E.toSet) (Classical.propDecidable _) 1 0 := by
  classical
  unfold periodicTilingPointCounted
  simp only [decide_eq_true_eq]
  rw [periodicTileCountCounted_fst]
  change _ = (if E.memBool x = true then 1 else 0) ↔ _
  by_cases hx : x ∈ E.toSet
  · have hb : E.memBool x = true := (E.memBool_eq_true_iff x).2 hx
    simp only [hb, hx, if_true]
  · have hb : E.memBool x ≠ true := fun h ↦
      hx ((E.memBool_eq_true_iff x).1 h)
    cases hbit : E.memBool x with
    | false => simp [hx]
    | true => exact (hb hbit).elim

private theorem periodicTilingPointCounted_cost_exact
    (F : Finset (Lattice d)) (A E : PeriodicSetCode d) (x : Lattice d) :
    (periodicTilingPointCounted F A E x).2 =
      F.card * (2 * d + 3) + d + 4 := by
  unfold periodicTilingPointCounted
  simp only [PeriodicSetCode.memCounted]
  rw [periodicTileCountCounted_cost_exact]
  omega

private theorem representationCount_periodic
    (F : Finset (Lattice d)) {q : ℕ} {A : Set (Lattice d)}
    (hA : SetScalarPeriodic q A) (x z : Lattice d) :
    (@Finset.filter _ (fun f ↦ x + (q : ℤ) • z - f ∈ A)
      (fun _ ↦ Classical.propDecidable _) F).card =
    (@Finset.filter _ (fun f ↦ x - f ∈ A)
      (fun _ ↦ Classical.propDecidable _) F).card := by
  apply congrArg Finset.card
  ext f
  simp only [Finset.mem_filter]
  have hp := hA (x - f) z
  have hp' : x + (q : ℤ) • z - f ∈ A ↔ x - f ∈ A := by
    convert hp using 1
    abel_nf
  exact and_congr Iff.rfl hp'

/-- The finite fundamental-box test is sound and complete for the global tiling equation. -/
theorem tilesPeriodicTargetBool_eq_true_iff
    (F : Finset (Lattice d)) (A E : PeriodicSetCode d) :
    tilesPeriodicTargetBool F A E = true ↔ Tiles F A.toSet E.toSet := by
  classical
  let q := commonCodePeriod A E
  have hAq : SetScalarPeriodic q A.toSet :=
    setScalarPeriodic_of_dvd (Nat.dvd_lcm_left A.period E.period)
      A.toSet_scalarPeriodic
  have hEq : SetScalarPeriodic q E.toSet :=
    setScalarPeriodic_of_dvd (Nat.dvd_lcm_right A.period E.period)
      E.toSet_scalarPeriodic
  rw [Tiles, tilesAtLevel_iff_representation_count]
  unfold tilesPeriodicTargetBool tilesPeriodicTargetCounted
  rw [countedAll_fst_eq_true_iff]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h x
    let r : BoxResidue d q :=
      fun i ↦ ⟨(x i).natMod q, Int.natMod_lt (commonCodePeriod_pos A E).ne'⟩
    let z : Lattice d := fun i ↦ x i / (q : ℤ)
    have hx : boxPoint r + (q : ℤ) • z = x :=
      boxPoint_natMod_add_ediv q (commonCodePeriod_pos A E) x
    have hr := (periodicTilingPointCounted_fst_eq_true_iff F A E
      (boxPoint r)).mp (h r)
    rw [← hx, representationCount_periodic F hAq]
    simpa only [hEq (boxPoint r) z] using hr
  · intro h r
    exact (periodicTilingPointCounted_fst_eq_true_iff F A E
      (boxPoint r)).mpr (h (boxPoint r))

/-- Exact operation count of the counted periodic-candidate tiling check. -/
theorem tilesPeriodicTargetCounted_cost_exact
    (F : Finset (Lattice d)) (A E : PeriodicSetCode d) :
    (tilesPeriodicTargetCounted F A E).2 =
      periodicCandidateCheckCost d F.card (commonCodePeriod A E) := by
  classical
  unfold tilesPeriodicTargetCounted
  rw [countedAll_cost]
  simp only [periodicTilingPointCounted_cost_exact, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    periodicCandidateCheckCost]
  rw [Nat.add_comm 1]
  congr 1

/-- The periodic-candidate check has the advertised closed operation count. -/
theorem tilesPeriodicTargetCounted_cost
    (F : Finset (Lattice d)) (A E : PeriodicSetCode d) :
    (tilesPeriodicTargetCounted F A E).2 ≤
      periodicCandidateCheckCost d F.card (commonCodePeriod A E) :=
  (tilesPeriodicTargetCounted_cost_exact F A E).le

/-- The emptiness bit is true exactly when the represented periodic set is empty. -/
theorem PeriodicSetCode.isEmptyBool_eq_true_iff (C : PeriodicSetCode d) :
    C.isEmptyBool = true ↔ C.toSet = ∅ := by
  unfold PeriodicSetCode.isEmptyBool
  rw [finsetAllBool_eq_true_iff]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hr := h (fun i ↦ ⟨(x i).natMod C.period,
      Int.natMod_lt C.period_pos.ne'⟩)
    have hfalse : C.memBool x = false := by
      change C.bits _ = false
      simpa using hr
    change C.memBool x = true at hx
    rw [hfalse] at hx
    contradiction
  · intro h r
    have hr : boxPoint r ∉ C.toSet := by rw [h]; simp
    change C.memBool (boxPoint r) ≠ true at hr
    rw [C.memBool_boxPoint r] at hr
    cases hbit : C.bits r with
    | false => rfl
    | true => exact (hr hbit).elim

end TranslationalTilings

/- blueprint/08-algorithms.md:338; TranslationalTilings.countedAllRange -/
namespace TranslationalTilings
/-- Universally fold counted Boolean computations over indices `0, …, n - 1`. -/
def countedAllRange : (n : ℕ) → (ℕ → Bool × ℕ) → Bool × ℕ
  | 0, _ => (true, 1)
  | n + 1, p =>
      let previous := countedAllRange n p
      let current := p n
      (previous.1 && current.1, previous.2 + current.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:345; TranslationalTilings.searchBoolTablesCounted -/
namespace TranslationalTilings
/-- Exhaustively search all Boolean tables on `Fin n`, returning success and exact cost. -/
def searchBoolTablesCounted :
    (n : ℕ) → ((Fin n → Bool) → Bool × ℕ) → Bool × ℕ
  | 0, check =>
      let result := check (fun i ↦ Fin.elim0 i)
      (result.1, result.2 + 1)
  | n + 1, check =>
      let falseBranch := searchBoolTablesCounted n fun tail ↦
        check (Fin.cases false tail)
      let trueBranch := searchBoolTablesCounted n fun tail ↦
        check (Fin.cases true tail)
      (falseBranch.1 || trueBranch.1,
        falseBranch.2 + trueBranch.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:358; TranslationalTilings.boolTableSearchCost -/
namespace TranslationalTilings
/-- Recurrence for the cost of exhaustively searching `2^n` Boolean tables. -/
def boolTableSearchCost : ℕ → ℕ → ℕ
  | 0, leafCost => leafCost + 1
  | n + 1, leafCost => 2 * boolTableSearchCost n leafCost + 1
end TranslationalTilings

/- blueprint/08-algorithms.md:362; TranslationalTilings.searchPositivePeriodsCounted -/
namespace TranslationalTilings
/-- Search every positive candidate period at most `B`, with an accumulated cost. -/
def searchPositivePeriodsCounted :
    (B : ℕ) → ((M : ℕ) → 0 < M → Bool × ℕ) → Bool × ℕ
  | 0, _ => (false, 1)
  | B + 1, check =>
      let previous := searchPositivePeriodsCounted B check
      let current := check (B + 1) (Nat.succ_pos B)
      (previous.1 || current.1, previous.2 + current.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:370; TranslationalTilings.positivePeriodSearchCost -/
namespace TranslationalTilings
/-- Recurrence for summing leaf costs over the positive periods up to `B`. -/
def positivePeriodSearchCost : (B : ℕ) → (ℕ → ℕ) → ℕ
  | 0, _ => 1
  | B + 1, leafCost =>
      positivePeriodSearchCost B leafCost + leafCost (B + 1) + 1
end TranslationalTilings

namespace TranslationalTilings

private theorem countedAllRange_fst_eq_true_iff
    (n : ℕ) (p : ℕ → Bool × ℕ) :
    (countedAllRange n p).1 = true ↔
      ∀ i < n, (p i).1 = true := by
  induction n with
  | zero => simp [countedAllRange]
  | succ n ih =>
      simp only [countedAllRange, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hprev, hlast⟩ i hi
        by_cases hin : i = n
        · simpa [hin] using hlast
        · exact hprev i (by omega)
      · intro h
        exact ⟨fun i hi ↦ h i (by omega), h n (by omega)⟩

/-- Exact fold-cost formula for universal search over a finite initial segment. -/
theorem countedAllRange_cost (n : ℕ) (p : ℕ → Bool × ℕ) :
    (countedAllRange n p).2 =
      1 + ∑ i ∈ Finset.range n, ((p i).2 + 1) := by
  induction n with
  | zero => simp [countedAllRange]
  | succ n ih =>
      simp only [countedAllRange, ih, Finset.sum_range_succ]
      omega

/-- Exhaustive table search succeeds exactly when some Boolean table passes the leaf check. -/
theorem searchBoolTablesCounted_eq_true_iff (n : ℕ)
    (check : (Fin n → Bool) → Bool × ℕ) :
    (searchBoolTablesCounted n check).1 = true ↔
      ∃ bits : Fin n → Bool, (check bits).1 = true := by
  induction n with
  | zero =>
      simp only [searchBoolTablesCounted]
      constructor
      · intro h
        exact ⟨fun i ↦ Fin.elim0 i, h⟩
      · rintro ⟨bits, h⟩
        simpa only [Subsingleton.elim bits (fun i ↦ Fin.elim0 i)] using h
  | succ n ih =>
      simp only [searchBoolTablesCounted, Bool.or_eq_true]
      rw [ih, ih]
      constructor
      · rintro (⟨tail, htail⟩ | ⟨tail, htail⟩)
        · exact ⟨Fin.cases false tail, htail⟩
        · exact ⟨Fin.cases true tail, htail⟩
      · rintro ⟨bits, hbits⟩
        let tail : Fin n → Bool := fun i ↦ bits i.succ
        have hcases (b : Bool) (hb : bits 0 = b) :
            Fin.cases b tail = bits := by
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simpa using hb.symm
          · rfl
        cases hb : bits 0 with
        | false =>
            left
            exact ⟨tail, by simpa only [hcases false hb] using hbits⟩
        | true =>
            right
            exact ⟨tail, by simpa only [hcases true hb] using hbits⟩

/-- Exact table-search cost when every leaf has the same prescribed cost. -/
theorem searchBoolTablesCounted_cost (n leafCost : ℕ)
    (check : (Fin n → Bool) → Bool × ℕ)
    (hcost : ∀ bits, (check bits).2 = leafCost) :
    (searchBoolTablesCounted n check).2 =
      boolTableSearchCost n leafCost := by
  induction n with
  | zero =>
      simp only [searchBoolTablesCounted, boolTableSearchCost]
      rw [hcost]
  | succ n ih =>
      simp only [searchBoolTablesCounted, boolTableSearchCost]
      rw [ih (fun tail ↦ check (Fin.cases false tail)),
        ih (fun tail ↦ check (Fin.cases true tail))]
      · omega
      · exact fun tail ↦ hcost (Fin.cases true tail)
      · exact fun tail ↦ hcost (Fin.cases false tail)

/-- Closed form for the Boolean-table search recurrence. -/
theorem boolTableSearchCost_closed (n leafCost : ℕ) :
    boolTableSearchCost n leafCost + 1 = 2 ^ n * (leafCost + 2) := by
  induction n with
  | zero => simp [boolTableSearchCost]
  | succ n ih =>
      simp only [boolTableSearchCost, pow_succ]
      calc
        2 * boolTableSearchCost n leafCost + 1 + 1 =
            2 * (boolTableSearchCost n leafCost + 1) := by omega
        _ = 2 * (2 ^ n * (leafCost + 2)) := by rw [ih]
        _ = 2 ^ n * 2 * (leafCost + 2) := by ring

/-- Positive-period search succeeds exactly when some `1 ≤ M ≤ B` passes its check. -/
theorem searchPositivePeriodsCounted_eq_true_iff (B : ℕ)
    (check : (M : ℕ) → 0 < M → Bool × ℕ) :
    (searchPositivePeriodsCounted B check).1 = true ↔
      ∃ (M : ℕ) (hM : 0 < M), M ≤ B ∧ (check M hM).1 = true := by
  induction B with
  | zero => simp [searchPositivePeriodsCounted]
  | succ B ih =>
      simp only [searchPositivePeriodsCounted, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨M, hM, hMB, hcheck⟩ | hlast)
        · exact ⟨M, hM, by omega, hcheck⟩
        · exact ⟨B + 1, Nat.succ_pos B, by omega, hlast⟩
      · rintro ⟨M, hM, hMB, hcheck⟩
        by_cases hlt : M ≤ B
        · left
          exact ⟨M, hM, hlt, hcheck⟩
        · right
          have hMsucc : M = B + 1 := by omega
          subst M
          simpa only [proof_irrel_heq] using hcheck

/-- Exact accumulated cost of searching all positive periods through `B`. -/
theorem searchPositivePeriodsCounted_cost (B : ℕ)
    (check : (M : ℕ) → 0 < M → Bool × ℕ)
    (leafCost : ℕ → ℕ)
    (hcost : ∀ M (hM : 0 < M), M ≤ B →
      (check M hM).2 = leafCost M) :
    (searchPositivePeriodsCounted B check).2 =
      positivePeriodSearchCost B leafCost := by
  induction B with
  | zero => simp [searchPositivePeriodsCounted, positivePeriodSearchCost]
  | succ B ih =>
      simp only [searchPositivePeriodsCounted, positivePeriodSearchCost]
      rw [ih (fun M hM hMB ↦ hcost M hM (by omega)),
        hcost (B + 1) (Nat.succ_pos B) (by omega)]

end TranslationalTilings

/- blueprint/08-algorithms.md:375; TranslationalTilings.planarBoxIndex -/
namespace TranslationalTilings
/-- Row-major index of a residue pair in a square `q × q` fundamental box. -/
def planarBoxIndex (q : ℕ) (x : BoxResidue 2 q) : Fin (q ^ 2) :=
  ⟨(x 0 : ℕ) * q + (x 1 : ℕ), by
    have hx0 := (x 0).isLt
    have hx1 := (x 1).isLt
    nlinarith⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:381; TranslationalTilings.planarBitsCode -/
namespace TranslationalTilings
/-- Decode a row-major Boolean table on `Fin (q²)` as a planar periodic-set code. -/
def planarBitsCode (q : ℕ) (hq : 0 < q)
    (bits : Fin (q ^ 2) → Bool) : PeriodicSetCode 2 :=
  PeriodicSetCode.ofBits q hq fun x ↦ bits (planarBoxIndex q x)
end TranslationalTilings

/- blueprint/08-algorithms.md:385; TranslationalTilings.planarBoxPointAt -/
namespace TranslationalTilings
/-- Decode a row-major box index to its standard planar lattice representative. -/
def planarBoxPointAt (q i : ℕ) : Plane :=
  ![(i / q : ℕ), (i % q : ℕ)]
end TranslationalTilings

/- blueprint/08-algorithms.md:388; TranslationalTilings.planarShiftedMemCounted -/
namespace TranslationalTilings
/-- Test whether `x - f` belongs to a row-major periodic candidate, with exact cost. -/
def planarShiftedMemCounted (q : ℕ) (hq : 0 < q)
    (bits : Fin (q ^ 2) → Bool) (x f : Plane) : Bool × ℕ :=
  let x0 := (x 0 - f 0).natMod q
  let x1 := (x 1 - f 1).natMod q
  let index : Fin (q ^ 2) := ⟨x0 * q + x1, by
    have hx0 : x0 < q := Int.natMod_lt hq.ne'
    have hx1 : x1 < q := Int.natMod_lt hq.ne'
    simp only [pow_two]
    nlinarith⟩
  (bits index, 7)
end TranslationalTilings

/- blueprint/08-algorithms.md:399; TranslationalTilings.planarTileCountCandidateCounted -/
namespace TranslationalTilings
/-- Count the translates of a planar tile covering one point of a candidate complement. -/
def planarTileCountCandidateCounted (F : Finset Plane)
    (q : ℕ) (hq : 0 < q) (bits : Fin (q ^ 2) → Bool)
    (x : Plane) : ℕ × ℕ :=
  F.fold countedAdd (0, 1) fun f ↦
    let r := planarShiftedMemCounted q hq bits x f
    (if r.1 then 1 else 0, r.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:406; TranslationalTilings.planarTilingPointCandidateCounted -/
namespace TranslationalTilings
/-- Check unique coverage by a planar candidate at one point, recording its cost. -/
def planarTilingPointCandidateCounted (F : Finset Plane)
    (q : ℕ) (hq : 0 < q) (bits : Fin (q ^ 2) → Bool)
    (x : Plane) : Bool × ℕ :=
  let lhs := planarTileCountCandidateCounted F q hq bits x
  (decide (lhs.1 = 1), lhs.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:412; TranslationalTilings.planarCandidateCheckCounted -/
namespace TranslationalTilings
/-- Check a row-major period-`q` candidate on every point of its fundamental square. -/
def planarCandidateCheckCounted (F : Finset Plane)
    (q : ℕ) (hq : 0 < q) (bits : Fin (q ^ 2) → Bool) : Bool × ℕ :=
  countedAllRange (q ^ 2) fun i ↦
    let r := planarTilingPointCandidateCounted F q hq bits
      (planarBoxPointAt q i)
    (r.1, r.2 + 2)
end TranslationalTilings

/- blueprint/08-algorithms.md:419; TranslationalTilings.planarCandidateCheckCost -/
namespace TranslationalTilings
/-- Closed cost assigned to checking one period-`q` planar candidate. -/
def planarCandidateCheckCost (tileCard q : ℕ) : ℕ :=
  q ^ 2 * (9 * tileCard + 5) + 1
end TranslationalTilings

namespace TranslationalTilings

private theorem planarShiftedMemCounted_fst
    (q : ℕ) (hq : 0 < q) (bits : Fin (q ^ 2) → Bool)
    (x f : Plane) :
    (planarShiftedMemCounted q hq bits x f).1 =
      (planarBitsCode q hq bits).memBool (x - f) := by
  rfl

private theorem planarShiftedMemCounted_snd
    (q : ℕ) (hq : 0 < q) (bits : Fin (q ^ 2) → Bool)
    (x f : Plane) :
    (planarShiftedMemCounted q hq bits x f).2 = 7 := by
  rfl

private theorem planarTileCountCandidateCounted_fst
    (F : Finset Plane) (q : ℕ) (hq : 0 < q)
    (bits : Fin (q ^ 2) → Bool) (x : Plane) :
    (planarTileCountCandidateCounted F q hq bits x).1 =
      (@Finset.filter _
        (fun f ↦ x - f ∈ (planarBitsCode q hq bits).toSet)
        (fun _ ↦ Classical.propDecidable _) F).card := by
  classical
  change (countedCount F (planarShiftedMemCounted q hq bits x)).1 = _
  rw [countedCount_fst, Finset.filter_congr_decidable]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro f _hf
  rw [planarShiftedMemCounted_fst,
    PeriodicSetCode.memBool_eq_true_iff]

private theorem planarTileCountCandidateCounted_cost_exact
    (F : Finset Plane) (q : ℕ) (hq : 0 < q)
    (bits : Fin (q ^ 2) → Bool) (x : Plane) :
    (planarTileCountCandidateCounted F q hq bits x).2 =
      1 + 9 * F.card := by
  classical
  change (countedCount F (planarShiftedMemCounted q hq bits x)).2 = _
  rw [countedCount_cost]
  simp only [planarShiftedMemCounted_snd, Finset.sum_const, nsmul_eq_mul]
  simp [Nat.mul_comm]

private theorem planarTilingPointCandidateCounted_fst_eq_true_iff
    (F : Finset Plane) (q : ℕ) (hq : 0 < q)
    (bits : Fin (q ^ 2) → Bool) (x : Plane) :
    (planarTilingPointCandidateCounted F q hq bits x).1 = true ↔
      (@Finset.filter _
        (fun f ↦ x - f ∈ (planarBitsCode q hq bits).toSet)
        (fun _ ↦ Classical.propDecidable _) F).card = 1 := by
  unfold planarTilingPointCandidateCounted
  simp only [decide_eq_true_eq]
  rw [planarTileCountCandidateCounted_fst]

private theorem planarTilingPointCandidateCounted_cost_exact
    (F : Finset Plane) (q : ℕ) (hq : 0 < q)
    (bits : Fin (q ^ 2) → Bool) (x : Plane) :
    (planarTilingPointCandidateCounted F q hq bits x).2 =
      9 * F.card + 2 := by
  unfold planarTilingPointCandidateCounted
  simp only
  rw [planarTileCountCandidateCounted_cost_exact]
  omega

private theorem planarBoxPointAt_planarBoxIndex
    (q : ℕ) (hq : 0 < q) (r : BoxResidue 2 q) :
    planarBoxPointAt q (planarBoxIndex q r) = boxPoint r := by
  funext i
  fin_cases i
  · have hnat : (((r 0 : ℕ) * q + (r 1 : ℕ)) / q : ℕ) = (r 0 : ℕ) := by
      rw [Nat.mul_comm (r 0 : ℕ) q, Nat.add_comm]
      rw [Nat.add_mul_div_left, Nat.div_eq_of_lt (r 1).isLt]
      all_goals omega
    simpa [planarBoxPointAt, planarBoxIndex, boxPoint, hq] using
      congrArg Int.ofNat hnat
  · have hnat : (((r 0 : ℕ) * q + (r 1 : ℕ)) % q : ℕ) = (r 1 : ℕ) := by
      rw [Nat.mul_comm (r 0 : ℕ) q, Nat.add_comm]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (r 1).isLt]
    simpa [planarBoxPointAt, planarBoxIndex, boxPoint, hq] using
      congrArg Int.ofNat hnat

/-- A candidate check succeeds exactly when its decoded periodic set tiles the plane by `F`. -/
theorem planarCandidateCheckCounted_eq_true_iff
    (F : Finset Plane) (q : ℕ) (hq : 0 < q)
    (bits : Fin (q ^ 2) → Bool) :
    (planarCandidateCheckCounted F q hq bits).1 = true ↔
      TilesUniverse F (planarBitsCode q hq bits).toSet := by
  classical
  let C := planarBitsCode q hq bits
  rw [TilesUniverse, Tiles, tilesAtLevel_iff_representation_count]
  simp only [Set.mem_univ, if_true]
  unfold planarCandidateCheckCounted
  rw [countedAllRange_fst_eq_true_iff]
  constructor
  · intro h x
    let r : BoxResidue 2 q :=
      fun i ↦ ⟨(x i).natMod q, Int.natMod_lt hq.ne'⟩
    let z : Plane := fun i ↦ x i / (q : ℤ)
    have hx : boxPoint r + (q : ℤ) • z = x :=
      boxPoint_natMod_add_ediv q hq x
    let i := planarBoxIndex q r
    have hi := i.isLt
    have hpoint := (planarTilingPointCandidateCounted_fst_eq_true_iff
      F q hq bits (planarBoxPointAt q i)).mp (h i hi)
    rw [planarBoxPointAt_planarBoxIndex q hq r] at hpoint
    rw [← hx]
    have hp :
        (@Finset.filter _
          (fun f ↦ boxPoint r + (q : ℤ) • z - f ∈ C.toSet)
          (fun _ ↦ Classical.propDecidable _) F).card =
        (@Finset.filter _ (fun f ↦ boxPoint r - f ∈ C.toSet)
          (fun _ ↦ Classical.propDecidable _) F).card := by
      simpa [C, planarBitsCode, PeriodicSetCode.ofBits] using
        representationCount_periodic F C.toSet_scalarPeriodic
          (boxPoint r) z
    exact hp.trans hpoint
  · intro h i hi
    exact (planarTilingPointCandidateCounted_fst_eq_true_iff
      F q hq bits (planarBoxPointAt q i)).mpr
        (h (planarBoxPointAt q i))

/-- The counted planar candidate check realizes its advertised exact cost. -/
theorem planarCandidateCheckCounted_cost
    (F : Finset Plane) (q : ℕ) (hq : 0 < q)
    (bits : Fin (q ^ 2) → Bool) :
    (planarCandidateCheckCounted F q hq bits).2 =
      planarCandidateCheckCost F.card q := by
  unfold planarCandidateCheckCounted
  rw [countedAllRange_cost]
  simp only [planarTilingPointCandidateCounted_cost_exact,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    planarCandidateCheckCost]
  rw [Nat.add_comm 1]
  congr 1

end TranslationalTilings

/- blueprint/08-algorithms.md:422; TranslationalTilings.planarTilePeriodCheckCounted -/
namespace TranslationalTilings
/-- Exhaustively search all Boolean complements having a fixed positive period `M`. -/
def planarTilePeriodCheckCounted (F : Finset Plane)
    (M : ℕ) (hM : 0 < M) : Bool × ℕ :=
  searchBoolTablesCounted (M ^ 2)
    (planarCandidateCheckCounted F M hM)
end TranslationalTilings

/- blueprint/08-algorithms.md:427; TranslationalTilings.planarTilePeriodSearchCost -/
namespace TranslationalTilings
/-- Cost of enumerating and checking every Boolean table of a fixed planar period. -/
def planarTilePeriodSearchCost (F : Finset Plane) (M : ℕ) : ℕ :=
  boolTableSearchCost (M ^ 2) (planarCandidateCheckCost F.card M)
end TranslationalTilings

namespace TranslationalTilings
/-- Exact cost of the exhaustive fixed-period tiling search. -/
theorem planarTilePeriodCheckCounted_cost
    (F : Finset Plane) (M : ℕ) (hM : 0 < M) :
    (planarTilePeriodCheckCounted F M hM).2 =
      planarTilePeriodSearchCost F M := by
  unfold planarTilePeriodCheckCounted planarTilePeriodSearchCost
  apply searchBoolTablesCounted_cost
  exact planarCandidateCheckCounted_cost F M hM
end TranslationalTilings

/- blueprint/08-algorithms.md:430; TranslationalTilings.planarTileDecisionCounted -/
namespace TranslationalTilings
/-- Search all positive complement periods through the quantitative tiling bound. -/
def planarTileDecisionCounted (F : Finset Plane) : Bool × ℕ :=
  searchPositivePeriodsCounted
    (periodicTilingPeriodBound F.card (l1Diameter F))
    (planarTilePeriodCheckCounted F)
end TranslationalTilings

/- blueprint/08-algorithms.md:435; TranslationalTilings.planarTileDecision -/
namespace TranslationalTilings
/-- Boolean projection of the bounded exhaustive planar tiling search. -/
def planarTileDecision (F : Finset Plane) : Bool :=
  (planarTileDecisionCounted F).1
end TranslationalTilings

/- blueprint/08-algorithms.md:438; TranslationalTilings.planarTileSearchCost -/
namespace TranslationalTilings
/-- Exact recurrence for the full bounded planar tiling search. -/
def planarTileSearchCost (F : Finset Plane) : ℕ :=
  positivePeriodSearchCost
    (periodicTilingPeriodBound F.card (l1Diameter F))
    (planarTilePeriodSearchCost F)
end TranslationalTilings

/- blueprint/08-algorithms.md:443; TranslationalTilings.planarTileSearchExponent -/
namespace TranslationalTilings
/-- Exponent used in the closed exponential upper bound for planar search. -/
def planarTileSearchExponent (F : Finset Plane) : ℕ :=
  (F.card + 2) *
    (periodicTilingPeriodBound F.card (l1Diameter F) + 2) ^ 4
end TranslationalTilings

/- blueprint/08-algorithms.md:447; TranslationalTilings.planarTileDiameterExponent -/
namespace TranslationalTilings
/-- Diameter exponent appearing after substituting the quantitative period bound. -/
def planarTileDiameterExponent (tileCard : ℕ) : ℕ :=
  4 * periodicTilingExponent tileCard
end TranslationalTilings

/- blueprint/08-algorithms.md:450; TranslationalTilings.planarTileSearchConstant -/
namespace TranslationalTilings
/-- Tile-cardinality-dependent constant in the closed planar search bound. -/
def planarTileSearchConstant (tileCard : ℕ) : ℕ :=
  16 * (tileCard + 2) * (periodicTilingConstant tileCard + 3) ^ 4
end TranslationalTilings

namespace TranslationalTilings

/-- The bounded planar search returns true exactly when `F` tiles `Z²`. -/
theorem planarTileDecision_eq_true_iff (F : Finset Plane) :
    planarTileDecision F = true ↔ ∃ A : Set Plane, TilesUniverse F A := by
  classical
  unfold planarTileDecision planarTileDecisionCounted
  rw [searchPositivePeriodsCounted_eq_true_iff]
  constructor
  · rintro ⟨M, hM, _hbound, hcheck⟩
    rw [planarTilePeriodCheckCounted,
      searchBoolTablesCounted_eq_true_iff] at hcheck
    obtain ⟨bits, hbits⟩ := hcheck
    exact ⟨(planarBitsCode M hM bits).toSet,
      (planarCandidateCheckCounted_eq_true_iff F M hM bits).mp hbits⟩
  · rintro ⟨A, htile⟩
    have hUniv : SetScalarPeriodic 1 (Set.univ : Set Plane) := by
      intro x z
      simp
    obtain ⟨C, hCbound⟩ := quantitative_periodic_tiling_l1
      (F := F) (E := Set.univ) Nat.zero_lt_one hUniv ⟨A, htile⟩
    let M := C.scalarMultiplier
    have hM : 0 < M := C.multiplier_pos
    have hperiodic : SetScalarPeriodic M C.tilingSet := by
      simpa only [one_mul] using C.periodic
    let bits : Fin (M ^ 2) → Bool := fun i ↦
      decide (planarBoxPointAt M i ∈ C.tilingSet)
    have hdecode : (planarBitsCode M hM bits).toSet = C.tilingSet := by
      ext x
      let r : BoxResidue 2 M := fun i ↦
        ⟨(x i).natMod M, Int.natMod_lt hM.ne'⟩
      let z : Plane := fun i ↦ x i / (M : ℤ)
      have hx : boxPoint r + (M : ℤ) • z = x :=
        boxPoint_natMod_add_ediv M hM x
      change bits (planarBoxIndex M r) = true ↔ x ∈ C.tilingSet
      rw [show bits (planarBoxIndex M r) =
          decide (boxPoint r ∈ C.tilingSet) by
        simp only [bits, planarBoxPointAt_planarBoxIndex M hM r]]
      rw [decide_eq_true_eq, ← hx]
      exact (hperiodic (boxPoint r) z).symm
    refine ⟨M, hM, hCbound, ?_⟩
    rw [planarTilePeriodCheckCounted,
      searchBoolTablesCounted_eq_true_iff]
    refine ⟨bits, (planarCandidateCheckCounted_eq_true_iff F M hM bits).2 ?_⟩
    simpa only [hdecode, TilesUniverse] using C.tiles

/-- The counted decision procedure has exactly the recursive search cost. -/
theorem planarTileDecisionCounted_cost_exact (F : Finset Plane) :
    (planarTileDecisionCounted F).2 = planarTileSearchCost F := by
  unfold planarTileDecisionCounted planarTileSearchCost
  apply searchPositivePeriodsCounted_cost
  intro M hM _hMB
  exact planarTilePeriodCheckCounted_cost F M hM

/-- The counted decision cost is bounded by the advertised search-cost expression. -/
theorem planarTileDecisionCounted_cost (F : Finset Plane) :
    (planarTileDecisionCounted F).2 ≤ planarTileSearchCost F :=
  (planarTileDecisionCounted_cost_exact F).le

private theorem positivePeriodSearchCost_eq_sum (B : ℕ)
    (leafCost : ℕ → ℕ) :
    positivePeriodSearchCost B leafCost =
      1 + ∑ k ∈ Finset.range B, (leafCost (k + 1) + 1) := by
  induction B with
  | zero => simp [positivePeriodSearchCost]
  | succ B ih =>
      simp only [positivePeriodSearchCost, ih, Finset.sum_range_succ]
      omega

/-- Expand the planar search recurrence as a sum over all candidate periods. -/
theorem planarTileSearchCost_eq_sum (F : Finset Plane) :
    let B := periodicTilingPeriodBound F.card (l1Diameter F)
    planarTileSearchCost F =
      1 + ∑ k ∈ Finset.range B,
        2 ^ ((k + 1) ^ 2) *
          ((k + 1) ^ 2 * (9 * F.card + 5) + 3) := by
  let B := periodicTilingPeriodBound F.card (l1Diameter F)
  unfold planarTileSearchCost
  rw [positivePeriodSearchCost_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  unfold planarTilePeriodSearchCost
  have hclosed := boolTableSearchCost_closed ((k + 1) ^ 2)
    (planarCandidateCheckCost F.card (k + 1))
  calc
    boolTableSearchCost ((k + 1) ^ 2)
          (planarCandidateCheckCost F.card (k + 1)) + 1 =
        2 ^ ((k + 1) ^ 2) *
          (planarCandidateCheckCost F.card (k + 1) + 2) := hclosed
    _ = 2 ^ ((k + 1) ^ 2) *
          ((k + 1) ^ 2 * (9 * F.card + 5) + 3) := by
      unfold planarCandidateCheckCost
      congr 1

/-- Bound the period sum by its largest exponential summand times the search range. -/
theorem planarTileSearchCost_preclosed_bound (F : Finset Plane) :
    let B := periodicTilingPeriodBound F.card (l1Diameter F)
    planarTileSearchCost F ≤
      1 + B * (2 ^ (B ^ 2) * (B ^ 2 * (9 * F.card + 5) + 3)) := by
  let B := periodicTilingPeriodBound F.card (l1Diameter F)
  rw [planarTileSearchCost_eq_sum]
  apply Nat.add_le_add_left
  calc
    ∑ k ∈ Finset.range B,
        2 ^ ((k + 1) ^ 2) * ((k + 1) ^ 2 * (9 * F.card + 5) + 3) ≤
        ∑ _k ∈ Finset.range B,
          2 ^ (B ^ 2) * (B ^ 2 * (9 * F.card + 5) + 3) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkB : k + 1 ≤ B :=
        Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
      have hsq : (k + 1) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hkB 2
      have hpow : 2 ^ ((k + 1) ^ 2) ≤ 2 ^ (B ^ 2) :=
        Nat.pow_le_pow_right (by omega) hsq
      have hlinear : (k + 1) ^ 2 * (9 * F.card + 5) + 3 ≤
          B ^ 2 * (9 * F.card + 5) + 3 :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_right (9 * F.card + 5) hsq) 3
      exact Nat.mul_le_mul hpow hlinear
    _ = B * (2 ^ (B ^ 2) * (B ^ 2 * (9 * F.card + 5) + 3)) := by
      simp

/-- Closed exponential upper bound for the total planar tiling decision cost. -/
theorem planarTileSearchCost_closed_bound (F : Finset Plane) :
    planarTileSearchCost F ≤ 2 ^ planarTileSearchExponent F := by
  let c := F.card
  let B := periodicTilingPeriodBound F.card (l1Diameter F)
  let P := B ^ 2 * (9 * c + 5) + 3
  let s := B ^ 2 + B + P
  have hB : 1 ≤ B := by
    exact le_max_left 1
      (periodicTilingConstant F.card *
        max 1 (l1Diameter F ^ periodicTilingExponent F.card))
  have hpre := planarTileSearchCost_preclosed_bound F
  change planarTileSearchCost F ≤ 1 + B * (2 ^ (B ^ 2) * P) at hpre
  have hBpow : B ≤ 2 ^ B := Nat.le_of_lt B.lt_two_pow_self
  have hPpow : P ≤ 2 ^ P := Nat.le_of_lt P.lt_two_pow_self
  have hstep :
      1 + B * (2 ^ (B ^ 2) * P) ≤ 2 ^ (s + 1) := by
    calc
      1 + B * (2 ^ (B ^ 2) * P) ≤
          1 + 2 ^ B * (2 ^ (B ^ 2) * 2 ^ P) := by gcongr
      _ = 1 + 2 ^ s := by
        simp only [← pow_add]
        congr 2
        simp only [s]
        omega
      _ ≤ 2 ^ (s + 1) := by
        rw [pow_succ]
        have hp : 0 < 2 ^ s := pow_pos (by omega) _
        omega
  have hsbound : s + 1 ≤ (c + 2) * (B + 2) ^ 4 := by
    have hBB : B ≤ B ^ 2 := by nlinarith
    have hsSmall : s + 1 ≤ (9 * c + 11) * B ^ 2 := by
      dsimp only [s, P]
      nlinarith
    have hfour : 9 * B ^ 2 ≤ (B + 2) ^ 4 := by
      nlinarith [sq_nonneg (B ^ 2 - 3 * B : ℤ)]
    calc
      s + 1 ≤ (9 * c + 11) * B ^ 2 := hsSmall
      _ ≤ (c + 2) * (9 * B ^ 2) := by nlinarith
      _ ≤ (c + 2) * (B + 2) ^ 4 := Nat.mul_le_mul_left _ hfour
  exact hpre.trans (hstep.trans
    (Nat.pow_le_pow_right (by omega) (by
      simpa only [planarTileSearchExponent, c, B] using hsbound)))

/-- Control the search exponent by the tile cardinality and `l1` diameter. -/
theorem planarTileSearchExponent_diameter_bound (F : Finset Plane) :
    planarTileSearchExponent F ≤ planarTileSearchConstant F.card *
      max 1 (l1Diameter F ^ planarTileDiameterExponent F.card) := by
  let c := F.card
  let D := l1Diameter F
  let C := periodicTilingConstant c
  let e := periodicTilingExponent c
  let X := max 1 (D ^ e)
  have hX : 1 ≤ X := le_max_left _ _
  have hB : periodicTilingPeriodBound c D + 2 ≤ 2 * (C + 3) * X := by
    unfold periodicTilingPeriodBound
    dsimp only [C, X]
    have hmax : max 1 (C * max 1 (D ^ e)) ≤ (C + 1) * X := by
      apply max_le
      · exact hX.trans (Nat.le_mul_of_pos_left X (Nat.succ_pos C))
      · exact Nat.mul_le_mul_right (max 1 (D ^ e)) (by omega)
    have htwo : 2 ≤ 2 * X := Nat.mul_le_mul_left 2 hX
    calc
      max 1 (C * max 1 (D ^ e)) + 2 ≤ (C + 1) * X + 2 :=
        Nat.add_le_add_right hmax 2
      _ ≤ (C + 1) * X + 2 * X := Nat.add_le_add_left htwo _
      _ = (C + 3) * X := by ring
      _ ≤ 2 * ((C + 3) * X) := Nat.le_mul_of_pos_left _ (by omega)
      _ = 2 * (C + 3) * X := by ring
  have hpow := Nat.pow_le_pow_left hB 4
  have hXpow : X ^ 4 = max 1 (D ^ (4 * e)) := by
    dsimp only [X]
    by_cases h : 1 ≤ D ^ e
    · rw [max_eq_right h, Nat.mul_comm 4 e, pow_mul]
      rw [max_eq_right]
      exact Nat.one_le_pow 4 _ (by omega)
    · have h' : D ^ e ≤ 1 := Nat.le_of_not_ge h
      rw [max_eq_left h', one_pow, max_eq_left]
      rw [Nat.mul_comm 4 e, pow_mul]
      have hc : D ^ e = 0 ∨ D ^ e = 1 := by omega
      rcases hc with hz | ho
      · simp [hz]
      · simp [ho]
  unfold planarTileSearchExponent planarTileSearchConstant
  dsimp only [c, D, C, e] at hB hpow hXpow ⊢
  calc
    (F.card + 2) *
        (periodicTilingPeriodBound F.card (l1Diameter F) + 2) ^ 4 ≤
        (F.card + 2) *
          (2 * (periodicTilingConstant F.card + 3) *
            max 1 (l1Diameter F ^ periodicTilingExponent F.card)) ^ 4 := by
      gcongr
    _ = 16 * (F.card + 2) *
          (periodicTilingConstant F.card + 3) ^ 4 *
          max 1 (l1Diameter F ^ (4 * periodicTilingExponent F.card)) := by
      rw [mul_pow, mul_pow, hXpow]
      norm_num
      ring

/-- The diameter exponent used by the search is at most the stated quartic polynomial. -/
theorem planarTileDiameterExponent_le_quartic (tileCard : ℕ) :
    planarTileDiameterExponent tileCard ≤ 12 * (tileCard + 1) ^ 4 := by
  unfold planarTileDiameterExponent
  have h := periodicTilingExponent_le_quartic tileCard
  omega

end TranslationalTilings

/- blueprint/08-algorithms.md:556; <example@blueprint/08-algorithms.md:556> -/
namespace TranslationalTilings
example : periodicTilingPeriodBound 0 0 = 1 := by decide
end TranslationalTilings

/- blueprint/08-algorithms.md:558; <example@blueprint/08-algorithms.md:558> -/
namespace TranslationalTilings
example :
    planarTileDecisionCounted (∅ : Finset Plane) = (false, 17) := by
  decide
end TranslationalTilings

/- blueprint/08-algorithms.md:562; <example@blueprint/08-algorithms.md:562> -/
namespace TranslationalTilings
example : planarTileSearchCost (∅ : Finset Plane) = 17 := by
  decide
end TranslationalTilings

/- blueprint/08-algorithms.md:589; TranslationalTilings.tileAnchor -/
namespace TranslationalTilings
/-- The lexicographically least tile point, or zero when the tile is empty. -/
def tileAnchor (F : Finset Plane) : Plane :=
  if hF : F.Nonempty then
    pairToPlane ((F.image planeToPair).min' (hF.image planeToPair))
  else 0
end TranslationalTilings

/- blueprint/08-algorithms.md:594; TranslationalTilings.normalizedTile -/
namespace TranslationalTilings
/-- Translate a tile by the negative of its anchor so that a nonempty tile contains zero. -/
def normalizedTile (F : Finset Plane) : Finset Plane :=
  F.image fun f ↦ f - tileAnchor F
end TranslationalTilings

/- blueprint/08-algorithms.md:597; TranslationalTilings.normalizedTargetCode -/
namespace TranslationalTilings
/-- Pull the target back by the tile-anchor translation used to normalize the tile. -/
def normalizedTargetCode
    (F : Finset Plane) (E : PeriodicSetCode 2) : PeriodicSetCode 2 :=
  E.pullbackTranslate (tileAnchor F)
end TranslationalTilings

namespace TranslationalTilings

private theorem pairToPlane_planeToPair (x : Plane) :
    pairToPlane (planeToPair x) = x := by
  funext i
  fin_cases i <;> rfl

/-- The anchor of a nonempty finite tile is one of its points. -/
theorem tileAnchor_mem {F : Finset Plane} (hF : F.Nonempty) :
    tileAnchor F ∈ F := by
  classical
  rw [tileAnchor, dif_pos hF]
  have hmin := Finset.min'_mem (F.image planeToPair) (hF.image planeToPair)
  obtain ⟨f, hf, hfeq⟩ := Finset.mem_image.mp hmin
  simpa only [← hfeq, pairToPlane_planeToPair] using hf

/-- Normalizing a nonempty tile places the origin in it. -/
theorem zero_mem_normalizedTile {F : Finset Plane} (hF : F.Nonempty) :
    0 ∈ normalizedTile F := by
  unfold normalizedTile
  apply Finset.mem_image.mpr
  exact ⟨tileAnchor F, tileAnchor_mem hF, sub_self _⟩

/-- Translation normalization preserves tile cardinality. -/
theorem card_normalizedTile (F : Finset Plane) :
    (normalizedTile F).card = F.card := by
  unfold normalizedTile
  rw [Finset.card_image_iff]
  intro x _ y _ hxy
  exact sub_left_injective hxy

/-- Translation normalization preserves the `l1` diameter. -/
theorem diameter_normalizedTile (F : Finset Plane) :
    l1Diameter (normalizedTile F) = l1Diameter F := by
  unfold normalizedTile
  apply Nat.le_antisymm
  · unfold l1Diameter
    apply Finset.sup_le
    intro xy hxy
    have hmem := Finset.mem_product.mp hxy
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hmem.1
    obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hmem.2
    rw [← hxeq, ← hyeq]
    simpa only [show x - tileAnchor F - (y - tileAnchor F) = x - y by abel] using
      (Finset.le_sup (f := fun uv : Plane × Plane ↦ l1Norm (uv.1 - uv.2))
        (show (x, y) ∈ F ×ˢ F by simp [hx, hy]))
  · unfold l1Diameter
    apply Finset.sup_le
    intro xy hxy
    have hmem := Finset.mem_product.mp hxy
    have hx : xy.1 - tileAnchor F ∈
        F.image fun f ↦ f - tileAnchor F :=
      Finset.mem_image.mpr ⟨xy.1, hmem.1, rfl⟩
    have hy : xy.2 - tileAnchor F ∈
        F.image fun f ↦ f - tileAnchor F :=
      Finset.mem_image.mpr ⟨xy.2, hmem.2, rfl⟩
    simpa only [show xy.1 - tileAnchor F - (xy.2 - tileAnchor F) =
        xy.1 - xy.2 by abel] using
      (Finset.le_sup (f := fun uv : Plane × Plane ↦ l1Norm (uv.1 - uv.2))
        (show (xy.1 - tileAnchor F, xy.2 - tileAnchor F) ∈
          (F.image fun f ↦ f - tileAnchor F) ×ˢ
            (F.image fun f ↦ f - tileAnchor F) by simp [hx, hy]))

/-- Simultaneously normalizing the tile and target preserves the tiling equation. -/
theorem tiles_normalized_iff (F : Finset Plane) (E : PeriodicSetCode 2)
    (A : Set Plane) :
    Tiles (normalizedTile F) A (normalizedTargetCode F E).toSet ↔
      Tiles F A E.toSet := by
  classical
  rw [normalizedTargetCode, PeriodicSetCode.pullbackTranslate_toSet]
  unfold Tiles TilesAtLevel
  let a := tileAnchor F
  have hconv (x : Plane) :
      tileConv (normalizedTile F) (setIndicator A) x =
        tileConv F (setIndicator A) (x + a) := by
    unfold normalizedTile tileConv
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro f _hf
      congr 1
      abel
    · intro x _hx y _hy hxy
      exact sub_left_injective hxy
  constructor
  · intro h x
    have hx := h (x - a)
    rw [hconv] at hx
    have hpull : x - a ∈ {y | y + a ∈ E.toSet} ↔ x ∈ E.toSet := by
      simp only [Set.mem_ofPred_eq, sub_add_cancel]
    have hindicator :
        setIndicator {y | y + a ∈ E.toSet} (x - a) =
          setIndicator E.toSet x := by
      change ({y | y + a ∈ E.toSet} : Set Plane).indicator (fun _ ↦ (1 : ℤ))
          (x - a) = E.toSet.indicator (fun _ ↦ (1 : ℤ)) x
      by_cases hmem : x ∈ E.toSet
      · rw [Set.indicator_of_mem (hpull.mpr hmem), Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem (fun hy ↦ hmem (hpull.mp hy)),
          Set.indicator_of_notMem hmem]
    rw [sub_add_cancel, hindicator] at hx
    exact hx
  · intro h x
    rw [hconv]
    exact h (x + a)

end TranslationalTilings

/- blueprint/08-algorithms.md:639; TranslationalTilings.classifierDirectionCount -/
namespace TranslationalTilings
/-- Number of commensurability classes among the nonzero tile-difference directions. -/
def classifierDirectionCount (F : Finset Plane) : ℕ :=
  groupedDirectionCount F
end TranslationalTilings

/- blueprint/08-algorithms.md:642; TranslationalTilings.classifierDirection -/
namespace TranslationalTilings
/-- Canonical scaled direction chosen for each tile-difference commensurability class. -/
def classifierDirection (F : Finset Plane) :
    Fin (classifierDirectionCount F) → Plane :=
  groupedTileDirections F
end TranslationalTilings

/- blueprint/08-algorithms.md:646; TranslationalTilings.classifierPrimitiveDirection -/
namespace TranslationalTilings
/-- Primitive integer vector underlying a canonical classifier direction. -/
def classifierPrimitiveDirection (F : Finset Plane)
    (j : Fin (classifierDirectionCount F)) : Plane :=
  primitivePart (classifierDirection F j)
end TranslationalTilings

/- blueprint/08-algorithms.md:650; TranslationalTilings.classifierWeakBound -/
namespace TranslationalTilings
/-- Quantitative upper bound on the weak-period multiplier enumerated by the classifier. -/
def classifierWeakBound (F : Finset Plane) : ℕ :=
  weakPeriodMultiplierBound F.card (l1Diameter F)
end TranslationalTilings

/- blueprint/08-algorithms.md:653; TranslationalTilings.classifierRepresentativeBound -/
namespace TranslationalTilings
/-- Uniform upper bound on scalar periods of completed representative components. -/
def classifierRepresentativeBound (F : Finset Plane) : ℕ :=
  periodicTilingPeriodBound F.card (l1Diameter F)
end TranslationalTilings

/- blueprint/08-algorithms.md:656; TranslationalTilings.classifierPeriod -/
namespace TranslationalTilings
/-- Common period obtained by multiplying the target period by the factorial period bound. -/
def classifierPeriod (F : Finset Plane) (E : PeriodicSetCode 2) : ℕ :=
  E.period * (classifierRepresentativeBound F).factorial
end TranslationalTilings

namespace TranslationalTilings
/-- The common classifier period is positive. -/
theorem classifierPeriod_pos (F : Finset Plane) (E : PeriodicSetCode 2) :
  0 < classifierPeriod F E :=
  Nat.mul_pos E.period_pos (Nat.factorial_pos _)
end TranslationalTilings

/- blueprint/08-algorithms.md:663; TranslationalTilings.RepresentativeTupleCode -/
namespace TranslationalTilings
/-- A bounded weak multiplier and one periodic component table for each classifier direction. -/
structure RepresentativeTupleCode
    (F : Finset Plane) (E : PeriodicSetCode 2) where
  /-- Candidate weak-period multiplier, bounded by `classifierWeakBound F`. -/
  weakMultiplier : Fin (classifierWeakBound F + 1)
  /-- Boolean table of the representative component in each canonical direction. -/
  representative : Fin (classifierDirectionCount F) →
    BoxResidue 2 (classifierPeriod F E) → Bool
deriving DecidableEq, Fintype
end TranslationalTilings

/- blueprint/08-algorithms.md:670; TranslationalTilings.RepresentativeTupleCode.weakMultiplierNat -/
namespace TranslationalTilings
/-- View the tuple's bounded weak multiplier as a natural number. -/
def RepresentativeTupleCode.weakMultiplierNat
    (T : RepresentativeTupleCode F E) : ℕ :=
  T.weakMultiplier
end TranslationalTilings

/- blueprint/08-algorithms.md:674;
TranslationalTilings.RepresentativeTupleCode.representativeCode -/
namespace TranslationalTilings
/-- Package one component table as a periodic-set code at the common classifier period. -/
def RepresentativeTupleCode.representativeCode
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) : PeriodicSetCode 2 :=
  PeriodicSetCode.ofBits (classifierPeriod F E)
    (classifierPeriod_pos F E) (T.representative j)
end TranslationalTilings

/- blueprint/08-algorithms.md:680; TranslationalTilings.validRepresentativeTupleBool -/
namespace TranslationalTilings
/-- Check positivity of the weak multiplier and that all component convolutions sum to the
target. -/
def validRepresentativeTupleBool
    (F : Finset Plane) (E : PeriodicSetCode 2)
    (T : RepresentativeTupleCode F E) : Bool :=
  decide (0 < T.weakMultiplierNat) &&
    finsetAllBool
      (Finset.univ : Finset (BoxResidue 2 (classifierPeriod F E)))
      fun x ↦ decide
        ((∑ j : Fin (classifierDirectionCount F),
          (periodicTileCountCounted F (T.representativeCode j)
            (boxPoint x)).1) =
          if E.memBool (boxPoint x) then 1 else 0)
end TranslationalTilings

/- blueprint/08-algorithms.md:692; TranslationalTilings.representativeTuples -/
namespace TranslationalTilings
/-- Finite enumeration of all representative tuples passing the validity check. -/
def representativeTuples
    (F : Finset Plane) (E : PeriodicSetCode 2) :
    Finset (RepresentativeTupleCode F E) :=
  Finset.univ.filter fun T ↦ validRepresentativeTupleBool F E T = true
end TranslationalTilings

namespace TranslationalTilings

/-- Semantic characterization of tuple validity by a global convolution identity. -/
theorem validRepresentativeTupleBool_eq_true_iff
    {E : PeriodicSetCode 2} (T) :
    validRepresentativeTupleBool F E T = true ↔
      0 < T.weakMultiplierNat ∧
      ∀ x,
        ∑ j : Fin (classifierDirectionCount F),
          tileConv F (setIndicator (T.representativeCode j).toSet) x =
            setIndicator E.toSet x := by
  classical
  let q := classifierPeriod F E
  have hq : 0 < q := classifierPeriod_pos F E
  have hEq : SetScalarPeriodic q E.toSet :=
    setScalarPeriodic_of_dvd ⟨(classifierRepresentativeBound F).factorial,
      rfl⟩ E.toSet_scalarPeriodic
  unfold validRepresentativeTupleBool
  rw [Bool.and_eq_true, decide_eq_true_eq, finsetAllBool_eq_true_iff]
  simp only [Finset.mem_univ, true_implies, decide_eq_true_eq]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h x
    let r : BoxResidue 2 q := fun i ↦
      ⟨(x i).natMod q, Int.natMod_lt hq.ne'⟩
    let z : Plane := fun i ↦ x i / (q : ℤ)
    have hx : boxPoint r + (q : ℤ) • z = x :=
      boxPoint_natMod_add_ediv q hq x
    have hlocal := h r
    simp_rw [periodicTileCountCounted_fst] at hlocal
    have hcount :
        (∑ j : Fin (classifierDirectionCount F),
          (@Finset.filter _
            (fun f ↦ x - f ∈ (T.representativeCode j).toSet)
            (fun _ ↦ Classical.propDecidable _) F).card) =
          @ite ℕ (x ∈ E.toSet) (Classical.propDecidable _) 1 0 := by
      rw [← hx]
      have hrep (j : Fin (classifierDirectionCount F)) :
          (@Finset.filter _
            (fun f ↦ boxPoint r + (q : ℤ) • z - f ∈
              (T.representativeCode j).toSet)
            (fun _ ↦ Classical.propDecidable _) F).card =
          (@Finset.filter _
            (fun f ↦ boxPoint r - f ∈ (T.representativeCode j).toSet)
            (fun _ ↦ Classical.propDecidable _) F).card := by
        have hrep' := representationCount_periodic F
          (T.representativeCode j).toSet_scalarPeriodic (boxPoint r) z
        change
          (@Finset.filter _
            (fun f ↦ boxPoint r + (q : ℤ) • z - f ∈
              (T.representativeCode j).toSet)
            (fun _ ↦ Classical.propDecidable _) F).card =
          (@Finset.filter _
            (fun f ↦ boxPoint r - f ∈ (T.representativeCode j).toSet)
            (fun _ ↦ Classical.propDecidable _) F).card at hrep'
        exact hrep'
      have hlocal' :
          (∑ j : Fin (classifierDirectionCount F),
            (@Finset.filter _
              (fun f ↦ boxPoint r - f ∈ (T.representativeCode j).toSet)
              (fun _ ↦ Classical.propDecidable _) F).card) =
            @ite ℕ (boxPoint r ∈ E.toSet) (Classical.propDecidable _) 1 0 := by
        simpa only [PeriodicSetCode.memBool_eq_true_iff] using hlocal
      simp_rw [hrep]
      simpa only [hEq (boxPoint r) z] using hlocal'
    simp_rw [tileConv_indicator_eq_card]
    by_cases hmem : x ∈ E.toSet
    · rw [if_pos hmem] at hcount
      simp only [setIndicator, Set.indicator_of_mem hmem]
      exact_mod_cast hcount
    · rw [if_neg hmem] at hcount
      simp only [setIndicator, Set.indicator_of_notMem hmem]
      exact_mod_cast hcount
  · intro h r
    have hx := h (boxPoint r)
    simp_rw [tileConv_indicator_eq_card] at hx
    simp_rw [periodicTileCountCounted_fst]
    by_cases hmem : boxPoint r ∈ E.toSet
    · have hmemBool : E.memBool (boxPoint r) = true := hmem
      simp only [setIndicator, Set.indicator_of_mem hmem] at hx
      rw [if_pos hmemBool]
      exact_mod_cast hx
    · have hmemBool : E.memBool (boxPoint r) ≠ true := hmem
      simp only [setIndicator, Set.indicator_of_notMem hmem] at hx
      rw [if_neg hmemBool]
      exact_mod_cast hx

/-- Membership in the enumerated tuple set is equivalent to positivity and the convolution
identity. -/
theorem mem_representativeTuples_iff
    {E : PeriodicSetCode 2} (T) :
    T ∈ representativeTuples F E ↔
      0 < T.weakMultiplierNat ∧
      ∀ x,
        ∑ j : Fin (classifierDirectionCount F),
          tileConv F (setIndicator (T.representativeCode j).toSet) x =
            setIndicator E.toSet x := by
  classical
  simp only [representativeTuples, Finset.mem_filter, Finset.mem_univ, true_and,
    validRepresentativeTupleBool_eq_true_iff]

end TranslationalTilings

/- blueprint/08-algorithms.md:729; TranslationalTilings.multipleCoordinate? -/
namespace TranslationalTilings
/-- Return the integer `n` with `z = n • v`, if such a multiple coordinate exists. -/
def multipleCoordinate? (v z : Plane) : Option ℤ :=
  if _hv0 : v 0 ≠ 0 then
    let n := z 0 / v 0
    if z = n • v then some n else none
  else if _hv1 : v 1 ≠ 0 then
    let n := z 1 / v 1
    if z = n • v then some n else none
  else none
end TranslationalTilings

/- blueprint/08-algorithms.md:738; TranslationalTilings.classifierLinePeriod -/
namespace TranslationalTilings
/-- Longitudinal period assigned to one classifier direction and weak multiplier. -/
def classifierLinePeriod (F : Finset Plane) (E : PeriodicSetCode 2)
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) : ℕ :=
  E.period * T.weakMultiplierNat * vectorContent (classifierDirection F j)
end TranslationalTilings

/- blueprint/08-algorithms.md:743; TranslationalTilings.linePatternMemBool -/
namespace TranslationalTilings
/-- Decode a cyclic Boolean pattern on the affine line `y + Z v`. -/
def linePatternMemBool (v y : Plane) (period : ℕ) (hperiod : 0 < period)
    (P : LinePattern period) (x : Plane) : Bool :=
  match multipleCoordinate? v (x - y) with
  | none => false
  | some n => P ⟨n.natMod period, Int.natMod_lt hperiod.ne'⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:749; TranslationalTilings.referenceSliceMemBool -/
namespace TranslationalTilings
/-- Test membership in the reference component restricted to the affine line through `y`. -/
def referenceSliceMemBool
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) (y x : Plane) : Bool :=
  (T.representativeCode j).memBool x &&
    (multipleCoordinate? (classifierPrimitiveDirection F j) (x - y)).isSome
end TranslationalTilings

/- blueprint/08-algorithms.md:755; TranslationalTilings.linePatternTileCount -/
namespace TranslationalTilings
/-- Count tile translates meeting the decoded affine-line pattern at `x`. -/
def linePatternTileCount (F : Finset Plane) (v y : Plane)
    (period : ℕ) (hperiod : 0 < period) (P : LinePattern period)
    (x : Plane) : ℕ :=
  (F.filter fun f ↦ linePatternMemBool v y period hperiod P (x - f)).card
end TranslationalTilings

/- blueprint/08-algorithms.md:760; TranslationalTilings.referenceSliceTileCount -/
namespace TranslationalTilings
/-- Count tile translates meeting the tuple's reference slice at `x`. -/
def referenceSliceTileCount (F : Finset Plane)
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) (y x : Plane) : ℕ :=
  (F.filter fun f ↦ referenceSliceMemBool T j y (x - f)).card
end TranslationalTilings

/- blueprint/08-algorithms.md:765; TranslationalTilings.lineCheckPeriod -/
namespace TranslationalTilings
/-- Common longitudinal window on which a candidate line pattern and reference slice are
compared. -/
def lineCheckPeriod (F : Finset Plane) (E : PeriodicSetCode 2)
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) : ℕ :=
  Nat.lcm (classifierLinePeriod F E T j) (classifierPeriod F E)
end TranslationalTilings

/- blueprint/08-algorithms.md:770; TranslationalTilings.differentLinePatternBool -/
namespace TranslationalTilings
/-- Detect a point in the common line window where a candidate differs from the reference slice. -/
def differentLinePatternBool (F : Finset Plane) (E : PeriodicSetCode 2)
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) (y : Plane)
    (hk : 0 < classifierLinePeriod F E T j)
    (P : LinePattern (classifierLinePeriod F E T j)) : Bool :=
  let Q := lineCheckPeriod F E T j
  finsetAnyBool (Finset.univ : Finset (Fin Q)) fun n ↦
    linePatternMemBool (classifierPrimitiveDirection F j) y
        (classifierLinePeriod F E T j) hk P
        (y + (n : ℕ) • classifierPrimitiveDirection F j) !=
      referenceSliceMemBool T j y
        (y + (n : ℕ) • classifierPrimitiveDirection F j)
end TranslationalTilings

/- blueprint/08-algorithms.md:783; TranslationalTilings.equivalentLinePatternBool -/
namespace TranslationalTilings
/-- Check equality of candidate and reference slice convolutions on a complete finite window. -/
def equivalentLinePatternBool (F : Finset Plane) (E : PeriodicSetCode 2)
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) (y : Plane)
    (hk : 0 < classifierLinePeriod F E T j)
    (P : LinePattern (classifierLinePeriod F E T j)) : Bool :=
  let Q := lineCheckPeriod F E T j
  finsetAllBool F fun f₀ ↦
    finsetAllBool (Finset.univ : Finset (Fin Q)) fun n ↦
      let x := f₀ + y + (n : ℕ) • classifierPrimitiveDirection F j
      linePatternTileCount F (classifierPrimitiveDirection F j) y
          (classifierLinePeriod F E T j) hk P x ==
        referenceSliceTileCount F T j y x
end TranslationalTilings

/- blueprint/08-algorithms.md:796; TranslationalTilings.hasChameleonSlice -/
namespace TranslationalTilings
/-- Search for a nontrivial line-pattern replacement with the same tile convolution. -/
def hasChameleonSlice (F : Finset Plane) (E : PeriodicSetCode 2)
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) : Bool :=
  if hk : 0 < classifierLinePeriod F E T j then
    finsetAnyBool
      (Finset.univ : Finset (BoxResidue 2 (classifierPeriod F E))) fun y ↦
      finsetAnyBool (Finset.univ : Finset
        (LinePattern (classifierLinePeriod F E T j))) fun P ↦
          differentLinePatternBool F E T j (boxPoint y) hk P &&
            equivalentLinePatternBool F E T j (boxPoint y) hk P
  else false
end TranslationalTilings

/- blueprint/08-algorithms.md:817; TranslationalTilings.decodedLinePattern -/
namespace TranslationalTilings
/-- The affine-line subset represented by a cyclic Boolean line pattern. -/
def decodedLinePattern (v y : Plane) (period : ℕ) (hperiod : 0 < period)
    (P : LinePattern period) : Set Plane :=
  {x | linePatternMemBool v y period hperiod P x}
end TranslationalTilings

namespace TranslationalTilings

/-- For nonzero `v`, the multiple-coordinate routine returns `n` exactly when `z = n • v`. -/
theorem multipleCoordinate?_eq_some_iff {v : Plane} (hv : v ≠ 0) :
    multipleCoordinate? v z = some n ↔ z = n • v := by
  have hscalar {a b : ℤ} {i : Fin 2} (hi : v i ≠ 0)
      (hab : a • v = b • v) : a = b := by
    have hc := congrFun hab i
    simp only [Pi.smul_apply, smul_eq_mul] at hc
    exact mul_right_cancel₀ hi hc
  unfold multipleCoordinate?
  by_cases hv0 : v 0 ≠ 0
  · rw [dif_pos hv0]
    let q := z 0 / v 0
    by_cases hz : z = q • v
    · rw [if_pos hz, Option.some.injEq]
      constructor
      · intro hqn
        rw [← hqn]
        exact hz
      · intro hzn
        exact hscalar hv0 (hz.symm.trans hzn)
    · rw [if_neg hz]
      simp only [reduceCtorEq, false_iff]
      intro hzn
      apply hz
      have hq : q = n := by
        dsimp only [q]
        rw [hzn, Pi.smul_apply, smul_eq_mul, mul_comm,
          Int.mul_ediv_cancel_left _ hv0]
      rw [hzn, hq]
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hv
      funext i
      fin_cases i
      · exact not_ne_iff.mp hv0
      · exact hv1
    rw [dif_neg hv0, dif_pos hv1]
    let q := z 1 / v 1
    by_cases hz : z = q • v
    · rw [if_pos hz, Option.some.injEq]
      constructor
      · intro hqn
        rw [← hqn]
        exact hz
      · intro hzn
        exact hscalar hv1 (hz.symm.trans hzn)
    · rw [if_neg hz]
      simp only [reduceCtorEq, false_iff]
      intro hzn
      apply hz
      have hq : q = n := by
        dsimp only [q]
        rw [hzn, Pi.smul_apply, smul_eq_mul, mul_comm,
          Int.mul_ediv_cancel_left _ hv1]
      rw [hzn, hq]

private theorem linePatternMemBool_eq_true_iff
    {v y x : Plane} {period : ℕ} (hperiod : 0 < period)
    (P : LinePattern period) (hv : v ≠ 0) :
    linePatternMemBool v y period hperiod P x = true ↔
      ∃ n : ℤ, x = y + n • v ∧
        P ⟨n.natMod period, Int.natMod_lt hperiod.ne'⟩ = true := by
  constructor
  · intro h
    cases hn : multipleCoordinate? v (x - y) with
    | none => simp [linePatternMemBool, hn] at h
    | some n =>
        refine ⟨n, ?_, ?_⟩
        · have hxy := (multipleCoordinate?_eq_some_iff hv).mp hn
          calc
            x = (x - y) + y := by abel
            _ = n • v + y := by rw [hxy]
            _ = y + n • v := by abel
        · simpa [linePatternMemBool, hn] using h
  · rintro ⟨n, rfl, hn⟩
    have hcoord : multipleCoordinate? v (y + n • v - y) = some n :=
      (multipleCoordinate?_eq_some_iff hv).mpr (by abel)
    rw [linePatternMemBool, hcoord]
    exact hn

private theorem referenceSliceMemBool_eq_true_iff
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) {y x : Plane}
    (hdir : classifierPrimitiveDirection F j ≠ 0) :
    referenceSliceMemBool T j y x = true ↔
      x ∈ (T.representativeCode j).toSet ∩
        addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y := by
  rw [referenceSliceMemBool, Bool.and_eq_true]
  constructor
  · rintro ⟨hxR, hxline⟩
    refine ⟨hxR, ?_⟩
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hxline
    have hmul := (multipleCoordinate?_eq_some_iff hdir).mp hn
    change x - y ∈ directionSubgroup (classifierPrimitiveDirection F j)
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, hmul.symm⟩
  · rintro ⟨hxR, hxline⟩
    refine ⟨hxR, ?_⟩
    change x - y ∈ directionSubgroup (classifierPrimitiveDirection F j) at hxline
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hxline
    exact Option.isSome_iff_exists.mpr
      ⟨n, (multipleCoordinate?_eq_some_iff hdir).mpr hn.symm⟩

private theorem int_natMod_add_period (n : ℤ) (period : ℕ) :
    (n + period).natMod period = n.natMod period := by
  unfold Int.natMod
  rw [Int.add_emod]
  simp

private theorem int_natMod_sub_period (n : ℤ) (period : ℕ) :
    (n - period).natMod period = n.natMod period := by
  unfold Int.natMod
  rw [Int.sub_emod]
  simp

private theorem decodedLinePattern_periodic
    {v y : Plane} {period : ℕ} (hperiod : 0 < period)
    (P : LinePattern period) (hv : v ≠ 0) :
    Function.Periodic (setIndicator (decodedLinePattern v y period hperiod P))
      ((period : ℤ) • v) := by
  intro x
  have hmem :
      x + (period : ℤ) • v ∈ decodedLinePattern v y period hperiod P ↔
        x ∈ decodedLinePattern v y period hperiod P := by
    change linePatternMemBool v y period hperiod P
        (x + (period : ℤ) • v) = true ↔
      linePatternMemBool v y period hperiod P x = true
    rw [linePatternMemBool_eq_true_iff hperiod P hv,
      linePatternMemBool_eq_true_iff hperiod P hv]
    constructor
    · rintro ⟨n, hn, hP⟩
      refine ⟨n - period, ?_, ?_⟩
      · calc
          x = x + (period : ℤ) • v - (period : ℤ) • v := by abel
          _ = y + n • v - (period : ℤ) • v := by rw [hn]
          _ = y + (n - period) • v := by module
      · simpa only [int_natMod_sub_period n period] using hP
    · rintro ⟨n, hn, hP⟩
      refine ⟨n + period, ?_, ?_⟩
      · rw [hn]
        module
      · simpa only [int_natMod_add_period n period] using hP
  let B := decodedLinePattern v y period hperiod P
  change setIndicator B (x + (period : ℤ) • v) = setIndicator B x
  by_cases hx : x + (period : ℤ) • v ∈ B
  · rw [setIndicator, Set.indicator_of_mem hx,
      Set.indicator_of_mem (hmem.mp hx)]
  · rw [setIndicator, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun hx' ↦ hx (hmem.mpr hx'))]

private theorem referenceSlice_periodic
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) (y : Plane) :
    Function.Periodic
      (setIndicator ((T.representativeCode j).toSet ∩
        addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y))
      ((classifierPeriod F E : ℤ) • classifierPrimitiveDirection F j) := by
  let v := classifierPrimitiveDirection F j
  let R := T.representativeCode j
  intro x
  have hmem :
      x + (classifierPeriod F E : ℤ) • v ∈
          R.toSet ∩ addCoset (directionSubgroup v) y ↔
        x ∈ R.toSet ∩ addCoset (directionSubgroup v) y := by
    constructor
    · rintro ⟨hxR, hxline⟩
      refine ⟨(R.toSet_scalarPeriodic x v).mp hxR, ?_⟩
      change x + (classifierPeriod F E : ℤ) • v - y ∈
        directionSubgroup v at hxline
      change x - y ∈ directionSubgroup v
      have hp : (classifierPeriod F E : ℤ) • v ∈ directionSubgroup v :=
        AddSubgroup.mem_zmultiples_iff.mpr ⟨classifierPeriod F E, rfl⟩
      have heq : x + (classifierPeriod F E : ℤ) • v - y -
          (classifierPeriod F E : ℤ) • v = x - y := by abel
      rw [← heq]
      exact (directionSubgroup v).sub_mem hxline hp
    · rintro ⟨hxR, hxline⟩
      refine ⟨(R.toSet_scalarPeriodic x v).mpr hxR, ?_⟩
      change x - y ∈ directionSubgroup v at hxline
      change x + (classifierPeriod F E : ℤ) • v - y ∈ directionSubgroup v
      have hp : (classifierPeriod F E : ℤ) • v ∈ directionSubgroup v :=
        AddSubgroup.mem_zmultiples_iff.mpr ⟨classifierPeriod F E, rfl⟩
      have heq : x + (classifierPeriod F E : ℤ) • v - y =
          (x - y) + (classifierPeriod F E : ℤ) • v := by abel
      rw [heq]
      exact (directionSubgroup v).add_mem hxline hp
  let B := R.toSet ∩ addCoset (directionSubgroup v) y
  change setIndicator B (x + (classifierPeriod F E : ℤ) • v) = setIndicator B x
  by_cases hx : x + (classifierPeriod F E : ℤ) • v ∈ B
  · rw [setIndicator, Set.indicator_of_mem hx,
      Set.indicator_of_mem (hmem.mp hx)]
  · rw [setIndicator, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun hx' ↦ hx (hmem.mpr hx'))]

private theorem tileConv_periodic_of_periodic
    {G R : Type*} [AddCommGroup G] [AddCommMonoid R]
    (F : Finset G) {g : G → R} {t : G} (hg : Function.Periodic g t) :
    Function.Periodic (tileConv F g) t := by
  intro x
  unfold tileConv
  apply Finset.sum_congr rfl
  intro f _
  rw [show x + t - f = (x - f) + t by abel]
  exact hg (x - f)

private theorem linePatternTileCount_eq_tileConv
    (F : Finset Plane) (v y : Plane) (period : ℕ) (hperiod : 0 < period)
    (P : LinePattern period) (x : Plane) :
    (linePatternTileCount F v y period hperiod P x : ℤ) =
      tileConv F (setIndicator (decodedLinePattern v y period hperiod P)) x := by
  rw [tileConv_indicator_eq_card]
  norm_cast
  unfold linePatternTileCount decodedLinePattern
  apply congrArg Finset.card
  ext f
  simp only [Finset.mem_filter, Set.mem_ofPred_eq]

private theorem referenceSliceTileCount_eq_tileConv
    (F : Finset Plane) (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) (y x : Plane)
    (hdir : classifierPrimitiveDirection F j ≠ 0) :
    (referenceSliceTileCount F T j y x : ℤ) =
      tileConv F (setIndicator ((T.representativeCode j).toSet ∩
        addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y)) x := by
  rw [tileConv_indicator_eq_card]
  norm_cast
  unfold referenceSliceTileCount
  apply congrArg Finset.card
  ext f
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ ↦ referenceSliceMemBool_eq_true_iff T j hdir)

private theorem convolution_eq_of_finite_line_check
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) (y : Plane)
    (P : LinePattern (classifierLinePeriod F E T j))
    (hdir : classifierPrimitiveDirection F j ≠ 0)
    (hk : 0 < classifierLinePeriod F E T j)
    (hcheck : ∀ f ∈ F, ∀ n : Fin (lineCheckPeriod F E T j),
      linePatternTileCount F (classifierPrimitiveDirection F j) y
          (classifierLinePeriod F E T j) hk P
          (f + y + (n : ℕ) • classifierPrimitiveDirection F j) =
        referenceSliceTileCount F T j y
          (f + y + (n : ℕ) • classifierPrimitiveDirection F j)) :
    convolutionEquivalent F
      (decodedLinePattern (classifierPrimitiveDirection F j) y
        (classifierLinePeriod F E T j) hk P)
      ((T.representativeCode j).toSet ∩
        addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y) := by
  classical
  let v := classifierPrimitiveDirection F j
  let k := classifierLinePeriod F E T j
  let Q := lineCheckPeriod F E T j
  have hQ : 0 < Q := Nat.lcm_pos hk (classifierPeriod_pos F E)
  have hdecodedQ :
      Function.Periodic
        (setIndicator (decodedLinePattern v y k hk P)) ((Q : ℤ) • v) := by
    obtain ⟨c, hc⟩ := Nat.dvd_lcm_left k (classifierPeriod F E)
    have hp := (decodedLinePattern_periodic (y := y) hk P hdir).nsmul c
    rw [show (Q : ℤ) • v = c • ((k : ℤ) • v) by
      dsimp only [Q]
      rw [lineCheckPeriod, hc]
      push_cast
      module]
    exact hp
  have hrefQ :
      Function.Periodic
        (setIndicator ((T.representativeCode j).toSet ∩
          addCoset (directionSubgroup v) y)) ((Q : ℤ) • v) := by
    obtain ⟨c, hc⟩ := Nat.dvd_lcm_right k (classifierPeriod F E)
    have hp := (referenceSlice_periodic T j y).nsmul c
    rw [show (Q : ℤ) • v =
        c • ((classifierPeriod F E : ℤ) • v) by
      dsimp only [Q]
      rw [lineCheckPeriod, hc]
      push_cast
      module]
    exact hp
  have hleftQ := tileConv_periodic_of_periodic F hdecodedQ
  have hrightQ := tileConv_periodic_of_periodic F hrefQ
  funext x
  by_cases hsupp :
      (∃ f ∈ F, x - f ∈ decodedLinePattern v y k hk P) ∨
        (∃ f ∈ F, x - f ∈ (T.representativeCode j).toSet ∩
          addCoset (directionSubgroup v) y)
  · obtain ⟨f, hf, m, hm⟩ : ∃ f ∈ F, ∃ m : ℤ, x = f + y + m • v := by
      rcases hsupp with hleft | hright
      · obtain ⟨f, hf, hx⟩ := hleft
        have hx' := (linePatternMemBool_eq_true_iff hk P hdir).mp hx
        obtain ⟨m, hm, -⟩ := hx'
        exact ⟨f, hf, m, by
          calc
            x = (x - f) + f := by abel
            _ = (y + m • v) + f := by rw [hm]
            _ = f + y + m • v := by abel⟩
      · obtain ⟨f, hf, hx⟩ := hright
        have hx' := (referenceSliceMemBool_eq_true_iff T j hdir).mpr hx
        rw [referenceSliceMemBool, Bool.and_eq_true] at hx'
        obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hx'.2
        have hm' := (multipleCoordinate?_eq_some_iff hdir).mp hm
        exact ⟨f, hf, m, by
          calc
            x = (x - f - y) + f + y := by abel
            _ = m • v + f + y := by rw [hm']
            _ = f + y + m • v := by abel⟩
    let r : ℕ := m.natMod Q
    let q : ℤ := m / Q
    have hr : r < Q := Int.natMod_lt hQ.ne'
    let n : Fin Q := ⟨r, hr⟩
    let x₀ : Plane := f + y + (r : ℕ) • v
    have hmq : (r : ℤ) + (Q : ℤ) * q = m := by
      dsimp only [r, q]
      rw [Int.natMod, Int.toNat_of_nonneg]
      · exact Int.emod_add_mul_ediv m Q
      · exact Int.emod_nonneg _ (by exact_mod_cast hQ.ne')
    have hxshift : x = x₀ + q • ((Q : ℤ) • v) := by
      rw [hm]
      dsimp only [x₀]
      rw [← hmq]
      module
    have hlocalNat := hcheck f hf n
    have hlocal :
        tileConv F (setIndicator (decodedLinePattern v y k hk P)) x₀ =
          tileConv F (setIndicator ((T.representativeCode j).toSet ∩
            addCoset (directionSubgroup v) y)) x₀ := by
      rw [← linePatternTileCount_eq_tileConv,
        ← referenceSliceTileCount_eq_tileConv F T j y x₀ hdir]
      exact_mod_cast hlocalNat
    rw [hxshift, hleftQ.zsmul q x₀, hrightQ.zsmul q x₀]
    exact hlocal
  · push Not at hsupp
    unfold tileConv
    apply Finset.sum_congr rfl
    intro f hf
    have hleft : x - f ∉ decodedLinePattern v y k hk P := hsupp.1 f hf
    have hright : x - f ∉ (T.representativeCode j).toSet ∩
        addCoset (directionSubgroup v) y := hsupp.2 f hf
    simp only [setIndicator]
    rw [Set.indicator_of_notMem hleft, Set.indicator_of_notMem hright]

/-- The finite longitudinal check is equivalent to convolution equality on the whole slice. -/
theorem equivalentLinePatternBool_eq_true_iff
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) (y : Plane)
    (P : LinePattern (classifierLinePeriod F E T j))
    (hdir : classifierPrimitiveDirection F j ≠ 0)
    (hk : 0 < classifierLinePeriod F E T j) :
    equivalentLinePatternBool F E T j y hk P = true ↔
      convolutionEquivalent F
        (decodedLinePattern (classifierPrimitiveDirection F j) y
          (classifierLinePeriod F E T j) hk P)
        ((T.representativeCode j).toSet ∩
          addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y) := by
  classical
  unfold equivalentLinePatternBool
  rw [finsetAllBool_eq_true_iff]
  constructor
  · intro hcheck
    apply convolution_eq_of_finite_line_check T j y P hdir hk
    intro f hf n
    have hn := (finsetAllBool_eq_true_iff
      (Finset.univ : Finset (Fin (lineCheckPeriod F E T j)))
      (fun n ↦
        let x := f + y + (n : ℕ) • classifierPrimitiveDirection F j
        linePatternTileCount F (classifierPrimitiveDirection F j) y
            (classifierLinePeriod F E T j) hk P x ==
          referenceSliceTileCount F T j y x)).mp (hcheck f hf) n
      (Finset.mem_univ n)
    simpa only [beq_iff_eq] using hn
  · intro hconv f hf
    rw [finsetAllBool_eq_true_iff]
    intro n _hn
    simp only [beq_iff_eq]
    let x := f + y + (n : ℕ) • classifierPrimitiveDirection F j
    have hx := congrFun hconv x
    rw [← linePatternTileCount_eq_tileConv,
      ← referenceSliceTileCount_eq_tileConv F T j y x hdir] at hx
    exact_mod_cast hx

private theorem membership_iff_of_setIndicator_eq
    {G : Type*} {B : Set G} {x y : G}
    (h : setIndicator B x = setIndicator B y) :
    x ∈ B ↔ y ∈ B := by
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;>
    simp [setIndicator, hx, hy] at h ⊢

private theorem differentLinePatternBool_eq_true_iff
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) (y : Plane)
    (P : LinePattern (classifierLinePeriod F E T j))
    (hdir : classifierPrimitiveDirection F j ≠ 0)
    (hk : 0 < classifierLinePeriod F E T j) :
    differentLinePatternBool F E T j y hk P = true ↔
      decodedLinePattern (classifierPrimitiveDirection F j) y
          (classifierLinePeriod F E T j) hk P ≠
        (T.representativeCode j).toSet ∩
          addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y := by
  classical
  let v := classifierPrimitiveDirection F j
  let k := classifierLinePeriod F E T j
  let Q := lineCheckPeriod F E T j
  let B := decodedLinePattern v y k hk P
  let C := (T.representativeCode j).toSet ∩ addCoset (directionSubgroup v) y
  have hQ : 0 < Q := Nat.lcm_pos hk (classifierPeriod_pos F E)
  have hBQ : Function.Periodic (setIndicator B) ((Q : ℤ) • v) := by
    obtain ⟨c, hc⟩ := Nat.dvd_lcm_left k (classifierPeriod F E)
    have hp := (decodedLinePattern_periodic (y := y) hk P hdir).nsmul c
    rw [show (Q : ℤ) • v = c • ((k : ℤ) • v) by
      dsimp only [Q]
      rw [lineCheckPeriod, hc]
      push_cast
      module]
    exact hp
  have hCQ : Function.Periodic (setIndicator C) ((Q : ℤ) • v) := by
    obtain ⟨c, hc⟩ := Nat.dvd_lcm_right k (classifierPeriod F E)
    have hp := (referenceSlice_periodic T j y).nsmul c
    rw [show (Q : ℤ) • v =
        c • ((classifierPeriod F E : ℤ) • v) by
      dsimp only [Q]
      rw [lineCheckPeriod, hc]
      push_cast
      module]
    exact hp
  unfold differentLinePatternBool
  rw [finsetAnyBool_eq_true_iff]
  constructor
  · rintro ⟨n, _hn, hne⟩ heq
    change B = C at heq
    have htruth :
        linePatternMemBool v y k hk P (y + (n : ℕ) • v) = true ↔
          referenceSliceMemBool T j y (y + (n : ℕ) • v) = true := by
      change y + (n : ℕ) • v ∈ B ↔
        referenceSliceMemBool T j y (y + (n : ℕ) • v) = true
      rw [heq]
      exact (referenceSliceMemBool_eq_true_iff T j hdir).symm
    have heqBool := (Bool.eq_iff_iff).mpr htruth
    exact (bne_iff_ne.mp hne) heqBool
  · intro hne
    have hexists : ∃ x : Plane, ¬(x ∈ B ↔ x ∈ C) := by
      by_contra hnone
      push Not at hnone
      exact hne (Set.ext hnone)
    obtain ⟨x, hx⟩ := hexists
    obtain ⟨m, hm⟩ : ∃ m : ℤ, x = y + m • v := by
      by_cases hxB : x ∈ B
      · have hx' := (linePatternMemBool_eq_true_iff hk P hdir).mp hxB
        obtain ⟨m, hm, -⟩ := hx'
        exact ⟨m, hm⟩
      · have hxC : x ∈ C := by
          by_contra hxC
          exact hx ⟨fun h ↦ (hxB h).elim, fun h ↦ (hxC h).elim⟩
        have hxline : x ∈ addCoset (directionSubgroup v) y := hxC.2
        change x - y ∈ directionSubgroup v at hxline
        obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hxline
        exact ⟨m, by
          calc
            x = (x - y) + y := by abel
            _ = m • v + y := by rw [← hm]
            _ = y + m • v := by abel⟩
    let r : ℕ := m.natMod Q
    let q : ℤ := m / Q
    have hr : r < Q := Int.natMod_lt hQ.ne'
    let n : Fin Q := ⟨r, hr⟩
    let x₀ : Plane := y + (r : ℕ) • v
    have hmq : (r : ℤ) + (Q : ℤ) * q = m := by
      dsimp only [r, q]
      rw [Int.natMod, Int.toNat_of_nonneg]
      · exact Int.emod_add_mul_ediv m Q
      · exact Int.emod_nonneg _ (by exact_mod_cast hQ.ne')
    have hxshift : x = x₀ + q • ((Q : ℤ) • v) := by
      rw [hm]
      dsimp only [x₀]
      rw [← hmq]
      module
    have hxBiff : x ∈ B ↔ x₀ ∈ B := by
      rw [hxshift]
      exact membership_iff_of_setIndicator_eq (hBQ.zsmul q x₀)
    have hxCiff : x ∈ C ↔ x₀ ∈ C := by
      rw [hxshift]
      exact membership_iff_of_setIndicator_eq (hCQ.zsmul q x₀)
    refine ⟨n, Finset.mem_univ n, ?_⟩
    have hlineTruth :
        linePatternMemBool v y k hk P x₀ = true ↔ x₀ ∈ B := Iff.rfl
    have hrefTruth :
        referenceSliceMemBool T j y x₀ = true ↔ x₀ ∈ C :=
      referenceSliceMemBool_eq_true_iff T j hdir
    have hboolNe :
        linePatternMemBool v y k hk P x₀ ≠ referenceSliceMemBool T j y x₀ := by
      intro heqBool
      apply hx
      rw [hxBiff, hxCiff]
      rw [← hlineTruth, ← hrefTruth, heqBool]
    simpa only [x₀, bne_iff_ne] using hboolNe

private theorem decodedLinePattern_translate_base
    (v y t : Plane) (period : ℕ) (hperiod : 0 < period)
    (P : LinePattern period) (x : Plane) :
    x ∈ decodedLinePattern v y period hperiod P ↔
      x + t ∈ decodedLinePattern v (y + t) period hperiod P := by
  change linePatternMemBool v y period hperiod P x = true ↔
    linePatternMemBool v (y + t) period hperiod P (x + t) = true
  unfold linePatternMemBool
  rw [show x + t - (y + t) = x - y by abel]

private theorem referenceSlice_translate_base
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) (y z x : Plane) :
    x ∈ (T.representativeCode j).toSet ∩
        addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y ↔
      x + (classifierPeriod F E : ℤ) • z ∈
        (T.representativeCode j).toSet ∩
          addCoset (directionSubgroup (classifierPrimitiveDirection F j))
            (y + (classifierPeriod F E : ℤ) • z) := by
  let R := T.representativeCode j
  let v := classifierPrimitiveDirection F j
  constructor
  · rintro ⟨hxR, hxline⟩
    refine ⟨(R.toSet_scalarPeriodic x z).mpr hxR, ?_⟩
    change x - y ∈ directionSubgroup v at hxline
    change x + (classifierPeriod F E : ℤ) • z -
      (y + (classifierPeriod F E : ℤ) • z) ∈ directionSubgroup v
    simpa only [show x + (classifierPeriod F E : ℤ) • z -
        (y + (classifierPeriod F E : ℤ) • z) = x - y by abel]
  · rintro ⟨hxR, hxline⟩
    refine ⟨(R.toSet_scalarPeriodic x z).mp hxR, ?_⟩
    change x + (classifierPeriod F E : ℤ) • z -
      (y + (classifierPeriod F E : ℤ) • z) ∈ directionSubgroup v at hxline
    change x - y ∈ directionSubgroup v
    simpa only [show x + (classifierPeriod F E : ℤ) • z -
        (y + (classifierPeriod F E : ℤ) • z) = x - y by abel] using hxline

private theorem convolutionEquivalent_of_translate_membership
    {G : Type*} [AddCommGroup G] (F : Finset G)
    {A₀ A B₀ B : Set G} (t : G)
    (hA : ∀ x, x ∈ A₀ ↔ x + t ∈ A)
    (hB : ∀ x, x ∈ B₀ ↔ x + t ∈ B)
    (hconv : convolutionEquivalent F A B) :
    convolutionEquivalent F A₀ B₀ := by
  classical
  have hindA (x : G) : setIndicator A₀ x = setIndicator A (x + t) := by
    by_cases hx : x ∈ A₀
    · simp [setIndicator, hx, (hA x).mp hx]
    · have hxt : x + t ∉ A := fun hmem ↦ hx ((hA x).mpr hmem)
      simp [setIndicator, hx, hxt]
  have hindB (x : G) : setIndicator B₀ x = setIndicator B (x + t) := by
    by_cases hx : x ∈ B₀
    · simp [setIndicator, hx, (hB x).mp hx]
    · have hxt : x + t ∉ B := fun hmem ↦ hx ((hB x).mpr hmem)
      simp [setIndicator, hx, hxt]
  funext x
  unfold tileConv
  calc
    ∑ f ∈ F, setIndicator A₀ (x - f) =
        ∑ f ∈ F, setIndicator A (x + t - f) := by
      apply Finset.sum_congr rfl
      intro f _
      rw [hindA, show x - f + t = x + t - f by abel]
    _ = ∑ f ∈ F, setIndicator B (x + t - f) := congrFun hconv (x + t)
    _ = ∑ f ∈ F, setIndicator B₀ (x - f) := by
      apply Finset.sum_congr rfl
      intro f _
      rw [hindB, show x - f + t = x + t - f by abel]

private theorem ne_of_ne_of_translate_membership
    {G : Type*} [AddCommGroup G] {A₀ A B₀ B : Set G} (t : G)
    (hA : ∀ x, x ∈ A₀ ↔ x + t ∈ A)
    (hB : ∀ x, x ∈ B₀ ↔ x + t ∈ B)
    (hne : A ≠ B) : A₀ ≠ B₀ := by
  intro heq
  apply hne
  ext x
  let x₀ := x - t
  have hx : x₀ + t = x := by dsimp only [x₀]; abel
  rw [← hx, ← hA x₀, ← hB x₀, heq]

private theorem algorithms_planeToPair_pairToPlane (p : ℤ ×ₗ ℤ) :
    planeToPair (pairToPlane p) = p := by
  apply Prod.ext <;> rfl

private theorem algorithms_planeToPair_injective : Function.Injective planeToPair := by
  intro u v huv
  funext i
  fin_cases i
  · exact congrArg Prod.fst huv
  · exact congrArg Prod.snd huv

private theorem classifierDirection_ne_zero
    (F : Finset Plane) (j : Fin (classifierDirectionCount F)) :
    classifierDirection F j ≠ 0 := by
  let p := (groupedDirectionPairs F).orderEmbOfFin rfl j
  let v := pairToPlane p
  have hpMem : planeToPair v ∈ groupedDirectionPairs F := by
    rw [algorithms_planeToPair_pairToPlane]
    exact Finset.orderEmbOfFin_mem (groupedDirectionPairs F) rfl j
  have hv : v ≠ 0 := by
    obtain ⟨f, hf, hfv⟩ := Finset.mem_image.mp hpMem
    have hfne : f ≠ 0 := Finset.ne_of_mem_erase hf
    have hcanon : canonicalDirection f = v := algorithms_planeToPair_injective hfv
    rw [← hcanon]
    exact canonicalDirection_ne_zero hfne
  have hscale : 0 < groupedDirectionScale F v := by
    rw [Nat.pos_iff_ne_zero]
    intro hzero
    rw [groupedDirectionScale, Finset.lcm_eq_zero_iff] at hzero
    obtain ⟨g, hg, hgzero⟩ := hzero
    have hgne : g ≠ 0 :=
      Finset.ne_of_mem_erase (Finset.mem_filter.mp hg).1
    exact (Nat.ne_of_gt (vectorContent_pos hgne)) hgzero
  change (groupedDirectionScale F v : ℤ) • v ≠ 0
  exact smul_ne_zero (by exact_mod_cast hscale.ne') hv

private theorem classifierPrimitiveDirection_ne_zero
    (F : Finset Plane) (j : Fin (classifierDirectionCount F)) :
    classifierPrimitiveDirection F j ≠ 0 :=
  (primitive_decomposition (classifierDirection_ne_zero F j)).2.1

private noncomputable def linePatternOfSet
    (v y : Plane) (period : ℕ) (B : Set Plane) : LinePattern period :=
  by
    classical
    exact fun n ↦ decide (y + (n : ℕ) • v ∈ B)

private theorem decodedLinePattern_linePatternOfSet_eq
    {v y : Plane} {period : ℕ} (hperiod : 0 < period)
    (hv : v ≠ 0) (B : Set Plane)
    (hsupport : B ⊆ addCoset (directionSubgroup v) y)
    (hBperiod : Function.Periodic (setIndicator B) ((period : ℤ) • v)) :
    decodedLinePattern v y period hperiod (linePatternOfSet v y period B) = B := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨m, hm, hmem⟩ :=
      (linePatternMemBool_eq_true_iff hperiod
        (linePatternOfSet v y period B) hv).mp hx
    let r : ℕ := m.natMod period
    let q : ℤ := m / period
    have hmq : (r : ℤ) + (period : ℤ) * q = m := by
      dsimp only [r, q]
      rw [Int.natMod, Int.toNat_of_nonneg]
      · exact Int.emod_add_mul_ediv m period
      · exact Int.emod_nonneg _ (by exact_mod_cast hperiod.ne')
    have hrB : y + (r : ℕ) • v ∈ B := by
      simpa only [linePatternOfSet, decide_eq_true_eq, r] using hmem
    have hshift : x = y + (r : ℕ) • v + q • ((period : ℤ) • v) := by
      rw [hm]
      rw [← hmq]
      module
    rw [hshift]
    exact (membership_iff_of_setIndicator_eq
      (hBperiod.zsmul q (y + (r : ℕ) • v))).mpr hrB
  · intro hx
    have hxline := hsupport hx
    change x - y ∈ directionSubgroup v at hxline
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hxline
    have hxy : x = y + m • v := by
      calc
        x = (x - y) + y := by abel
        _ = m • v + y := by rw [← hm]
        _ = y + m • v := by abel
    let r : ℕ := m.natMod period
    let q : ℤ := m / period
    have hmq : (r : ℤ) + (period : ℤ) * q = m := by
      dsimp only [r, q]
      rw [Int.natMod, Int.toNat_of_nonneg]
      · exact Int.emod_add_mul_ediv m period
      · exact Int.emod_nonneg _ (by exact_mod_cast hperiod.ne')
    have hshift : x = y + (r : ℕ) • v + q • ((period : ℤ) • v) := by
      rw [hxy, ← hmq]
      module
    have hrB : y + (r : ℕ) • v ∈ B := by
      rw [hshift] at hx
      exact (membership_iff_of_setIndicator_eq
        (hBperiod.zsmul q (y + (r : ℕ) • v))).mp hx
    apply (linePatternMemBool_eq_true_iff hperiod
      (linePatternOfSet v y period B) hv).mpr
    refine ⟨m, hxy, ?_⟩
    simpa only [linePatternOfSet, decide_eq_true_eq, r] using hrB

private theorem hasChameleonSlice_eq_true_iff_core
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F))
    (hdir : classifierPrimitiveDirection F j ≠ 0) :
    hasChameleonSlice F E T j = true ↔
      ∃ (y : Plane) (k : LinePattern (classifierLinePeriod F E T j))
        (hk : 0 < classifierLinePeriod F E T j),
        decodedLinePattern (classifierPrimitiveDirection F j) y
            (classifierLinePeriod F E T j) hk k ≠
          (T.representativeCode j).toSet ∩
            addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y ∧
        convolutionEquivalent F
          (decodedLinePattern (classifierPrimitiveDirection F j) y
            (classifierLinePeriod F E T j) hk k)
          ((T.representativeCode j).toSet ∩
            addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y) := by
  classical
  constructor
  · intro h
    unfold hasChameleonSlice at h
    split at h
    next hk =>
      rw [finsetAnyBool_eq_true_iff] at h
      obtain ⟨r, _hr, h⟩ := h
      rw [finsetAnyBool_eq_true_iff] at h
      obtain ⟨k, _hk, hboth⟩ := h
      rw [Bool.and_eq_true] at hboth
      refine ⟨boxPoint r, k, hk,
        (differentLinePatternBool_eq_true_iff T j (boxPoint r) k hdir hk).mp hboth.1,
        (equivalentLinePatternBool_eq_true_iff T j (boxPoint r) k hdir hk).mp hboth.2⟩
    next hk => simp at h
  · rintro ⟨y, k, hk, hne, hconv⟩
    let r : BoxResidue 2 (classifierPeriod F E) := fun i ↦
      ⟨(y i).natMod (classifierPeriod F E),
        Int.natMod_lt (classifierPeriod_pos F E).ne'⟩
    let z : Plane := fun i ↦ y i / (classifierPeriod F E : ℤ)
    let t : Plane := (classifierPeriod F E : ℤ) • z
    have hy : boxPoint r + t = y := by
      exact boxPoint_natMod_add_ediv
        (classifierPeriod F E) (classifierPeriod_pos F E) y
    let B₀ := decodedLinePattern (classifierPrimitiveDirection F j) (boxPoint r)
      (classifierLinePeriod F E T j) hk k
    let B := decodedLinePattern (classifierPrimitiveDirection F j) y
      (classifierLinePeriod F E T j) hk k
    let C₀ := (T.representativeCode j).toSet ∩
      addCoset (directionSubgroup (classifierPrimitiveDirection F j)) (boxPoint r)
    let C := (T.representativeCode j).toSet ∩
      addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y
    have hB (x : Plane) : x ∈ B₀ ↔ x + t ∈ B := by
      dsimp only [B₀, B, t]
      rw [← hy]
      exact decodedLinePattern_translate_base _ _ _ _ _ _ x
    have hC (x : Plane) : x ∈ C₀ ↔ x + t ∈ C := by
      dsimp only [C₀, C, t]
      rw [← hy]
      exact referenceSlice_translate_base T j (boxPoint r) z x
    have hne₀ : B₀ ≠ C₀ :=
      ne_of_ne_of_translate_membership t hB hC hne
    have hconv₀ : convolutionEquivalent F B₀ C₀ :=
      convolutionEquivalent_of_translate_membership F t hB hC hconv
    unfold hasChameleonSlice
    rw [dif_pos hk, finsetAnyBool_eq_true_iff]
    refine ⟨r, Finset.mem_univ r, ?_⟩
    rw [finsetAnyBool_eq_true_iff]
    refine ⟨k, Finset.mem_univ k, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · exact (differentLinePatternBool_eq_true_iff T j (boxPoint r) k hdir hk).mpr hne₀
    · exact (equivalentLinePatternBool_eq_true_iff T j (boxPoint r) k hdir hk).mpr hconv₀

/-- The executable slice search detects exactly the replaceable nontrivial slices. -/
theorem hasChameleonSlice_eq_true_iff
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F))
    (_hF : F.Nonempty) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (_hvalid : validRepresentativeTupleBool F E T = true) :
    hasChameleonSlice F E T j = true ↔
      ∃ (y : Plane) (k : LinePattern (classifierLinePeriod F E T j))
        (hk : 0 < classifierLinePeriod F E T j),
        decodedLinePattern (classifierPrimitiveDirection F j) y
            (classifierLinePeriod F E T j) hk k ≠
          (T.representativeCode j).toSet ∩
            addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y ∧
        convolutionEquivalent F
          (decodedLinePattern (classifierPrimitiveDirection F j) y
            (classifierLinePeriod F E T j) hk k)
          ((T.representativeCode j).toSet ∩
            addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y) :=
  hasChameleonSlice_eq_true_iff_core T j
    (primitive_decomposition
      (groupedTileDirections_ne_zero hzero hcard j)).2.1

end TranslationalTilings

/- blueprint/08-algorithms.md:866; TranslationalTilings.LineSelection -/
namespace TranslationalTilings
/-- A supported periodic replacement on every classifier direction and affine coset. -/
structure LineSelection (F : Finset Plane) (E : PeriodicSetCode 2)
    (T : RepresentativeTupleCode F E) where
  /-- Replacement subset chosen for each direction and quotient-indexed affine line. -/
  chosen : ∀ j : Fin (classifierDirectionCount F),
    (Plane ⧸ directionSubgroup (classifierPrimitiveDirection F j)) → Set Plane
  /-- Every replacement is supported on its designated affine line. -/
  supported : ∀ j line,
    chosen j line ⊆ quotientCoset
      (directionSubgroup (classifierPrimitiveDirection F j)) line
  /-- Each replacement has the classifier's prescribed longitudinal line period. -/
  periodic : ∀ j line,
    Function.Periodic (setIndicator (chosen j line))
      ((classifierLinePeriod F E T j : ℤ) •
        classifierPrimitiveDirection F j)
  /-- Each replacement has the same tile convolution as the corresponding reference slice. -/
  convolution_equivalent : ∀ j line,
    convolutionEquivalent F (chosen j line)
      ((T.representativeCode j).toSet ∩
        quotientCoset
          (directionSubgroup (classifierPrimitiveDirection F j)) line)
end TranslationalTilings

/- blueprint/08-algorithms.md:883; TranslationalTilings.assembleLineSelection -/
namespace TranslationalTilings
/-- Union all selected replacements over classifier directions and affine lines. -/
def assembleLineSelection
    (S : LineSelection F E T) : Set Plane :=
  ⋃ j, ⋃ line, S.chosen j line
end TranslationalTilings

/- blueprint/08-algorithms.md:887; TranslationalTilings.ProducedByTuple -/
namespace TranslationalTilings
/-- A set is produced by a tuple when it is the union assembled from some valid line selection. -/
def ProducedByTuple
    (T : RepresentativeTupleCode F E) (A : Set Plane) : Prop :=
  ∃ S : LineSelection F E T, A = assembleLineSelection S
end TranslationalTilings

namespace TranslationalTilings

private theorem setIndicator_iUnion_eq_sum_finite
    {G : Type*} {m : ℕ} (part : Fin m → Set G)
    (hdisjoint : Set.PairwiseDisjoint Set.univ part) :
    setIndicator (⋃ j, part j) = ∑ j, setIndicator (part j) := by
  have hd : ((↑(Finset.univ : Finset (Fin m))) : Set (Fin m)).PairwiseDisjoint
      part := by
    simpa only [Finset.coe_univ] using hdisjoint
  funext x
  simp only [setIndicator]
  rw [Finset.sum_apply]
  change ((⋃ j, part j).indicator (fun _ ↦ (1 : ℤ))) x =
    ∑ j, (part j).indicator (fun _ ↦ (1 : ℤ)) x
  simpa only [Finset.mem_univ, Set.iUnion_true] using congrFun
    (Finset.indicator_biUnion (Finset.univ : Finset (Fin m)) part hd
      (f := fun _ ↦ (1 : ℤ))) x

private theorem pairwiseDisjoint_of_sum_convolution
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    (F : Finset G) (part : ι → Set G) (E : Set G)
    (hF : F.Nonempty)
    (hsum : setIndicator E = ∑ i, tileConv F (setIndicator (part i))) :
    Set.PairwiseDisjoint Set.univ part := by
  classical
  rw [Set.pairwiseDisjoint_iff]
  intro i _ j _ hnonempty
  by_contra hij
  obtain ⟨y, hyi, hyj⟩ := hnonempty
  obtain ⟨f₀, hf₀⟩ := hF
  let x := y + f₀
  let count : ι → ℕ := fun a ↦
    (F.filter fun f ↦ x - f ∈ part a).card
  have hcount (a : ι) :
      tileConv F (setIndicator (part a)) x = (count a : ℤ) :=
    tileConv_indicator_eq_card F (part a) x
  have hicount : 1 ≤ count i := by
    apply Finset.card_pos.mpr
    refine ⟨f₀, Finset.mem_filter.mpr ⟨hf₀, ?_⟩⟩
    simpa only [x, add_sub_cancel_right] using hyi
  have hjcount : 1 ≤ count j := by
    apply Finset.card_pos.mpr
    refine ⟨f₀, Finset.mem_filter.mpr ⟨hf₀, ?_⟩⟩
    simpa only [x, add_sub_cancel_right] using hyj
  have hpairs : count i + count j ≤ ∑ a, count a := by
    rw [← Finset.sum_pair hij]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ _
    · intro a _ _
      exact Nat.zero_le _
  have htotal : ((∑ a, count a : ℕ) : ℤ) = setIndicator E x := by
    calc
      ((∑ a, count a : ℕ) : ℤ) = ∑ a, (count a : ℤ) := by
        push_cast
        rfl
      _ = ∑ a, tileConv F (setIndicator (part a)) x := by
        apply Finset.sum_congr rfl
        intro a _
        exact (hcount a).symm
      _ = setIndicator E x := by
        rw [← Finset.sum_apply]
        exact (congrFun hsum x).symm
  have hEupper : setIndicator E x ≤ 1 := by
    by_cases hx : x ∈ E <;> simp [setIndicator, hx]
  have htwo : (2 : ℕ) ≤ ∑ a, count a := by omega
  omega

private theorem tiles_iUnion_of_sum_convolution
    {G : Type*} [AddCommGroup G] {m : ℕ}
    (F : Finset G) (part : Fin m → Set G) (E : Set G)
    (hdisjoint : Set.PairwiseDisjoint Set.univ part)
    (hsum : setIndicator E = ∑ i, tileConv F (setIndicator (part i))) :
    Tiles F (⋃ i, part i) E := by
  have hindicator := setIndicator_iUnion_eq_sum_finite part hdisjoint
  intro x
  rw [hindicator]
  simp only [tileConv, Finset.sum_apply]
  rw [Finset.sum_comm]
  have hs : (∑ i, ∑ f ∈ F, setIndicator (part i) (x - f)) =
      setIndicator E x := by
    simpa only [Finset.sum_apply, tileConv] using (congrFun hsum x).symm
  norm_num at hs ⊢
  exact hs

private def representativeBackground
    (T : RepresentativeTupleCode F E) : Set Plane :=
  ⋃ j, (T.representativeCode j).toSet

private theorem representativeBackground_tiles
    (T : RepresentativeTupleCode F E) (hF : F.Nonempty)
    (hvalid : validRepresentativeTupleBool F E T = true) :
    Tiles F (representativeBackground T) E.toSet := by
  have hsum := (validRepresentativeTupleBool_eq_true_iff T).mp hvalid |>.2
  have hsum' : setIndicator E.toSet =
      ∑ j : Fin (classifierDirectionCount F),
        tileConv F (setIndicator (T.representativeCode j).toSet) := by
    funext x
    simpa only [Finset.sum_apply] using (hsum x).symm
  have hdisjoint := pairwiseDisjoint_of_sum_convolution F
    (fun j : Fin (classifierDirectionCount F) ↦ (T.representativeCode j).toSet)
    E.toSet hF hsum'
  exact tiles_iUnion_of_sum_convolution F
    (fun j : Fin (classifierDirectionCount F) ↦ (T.representativeCode j).toSet)
    E.toSet hdisjoint hsum'

private theorem lineSelection_direction_convolution
    (S : LineSelection F E T) (j : Fin (classifierDirectionCount F)) :
    convolutionEquivalent F (⋃ line, S.chosen j line)
      (T.representativeCode j).toSet := by
  classical
  let v := classifierPrimitiveDirection F j
  let H := directionSubgroup v
  let B := ⋃ line, S.chosen j line
  let R := (T.representativeCode j).toSet
  funext x
  let lines : Finset (Plane ⧸ H) :=
    F.image fun f ↦ QuotientAddGroup.mk' H (x - f)
  have hsumChosen : tileConv F (setIndicator B) x =
      ∑ line ∈ lines, tileConv F (setIndicator (S.chosen j line)) x := by
    unfold tileConv
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f hf
    let line₀ : Plane ⧸ H := QuotientAddGroup.mk' H (x - f)
    rw [Finset.sum_eq_single line₀]
    · have hmemIff : x - f ∈ S.chosen j line₀ ↔ x - f ∈ B := by
        constructor
        · intro hmem
          exact Set.mem_iUnion.mpr ⟨line₀, hmem⟩
        · intro hmem
          obtain ⟨line, hline⟩ := Set.mem_iUnion.mp hmem
          have hsupport := S.supported j line hline
          have heq : line = line₀ := by
            change QuotientAddGroup.mk' H (x - f) = line at hsupport
            exact hsupport.symm
          simpa only [heq] using hline
      by_cases hmem : x - f ∈ S.chosen j line₀
      · simp [setIndicator, hmem, hmemIff.mp hmem]
      · have hnotB : x - f ∉ B := fun hB ↦ hmem (hmemIff.mpr hB)
        simp [setIndicator, hmem, hnotB]
    · intro line hline hne
      have hnot : x - f ∉ S.chosen j line := by
        intro hmem
        have hsupport := S.supported j line hmem
        change QuotientAddGroup.mk' H (x - f) = line at hsupport
        exact hne hsupport.symm
      simp only [setIndicator, Set.indicator_of_notMem hnot]
    · intro hnot
      exact (hnot (Finset.mem_image.mpr ⟨f, hf, rfl⟩)).elim
  have hsumSlices (C : Set Plane) : tileConv F (setIndicator C) x =
      ∑ line ∈ lines, tileConv F (setIndicator (slicePattern v line C)) x := by
    unfold tileConv
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f hf
    let line₀ : Plane ⧸ H := QuotientAddGroup.mk' H (x - f)
    rw [Finset.sum_eq_single line₀]
    · have hindicator :
          setIndicator (slicePattern v line₀ C) (x - f) =
            setIndicator C (x - f) := by
        by_cases hmem : x - f ∈ C
        · have hslice : x - f ∈ slicePattern v line₀ C :=
            (mem_slicePattern (x - f)).2 ⟨hmem, rfl⟩
          simp [setIndicator, hmem, hslice]
        · have hslice : x - f ∉ slicePattern v line₀ C := fun hy ↦
            hmem ((mem_slicePattern (x - f)).1 hy).1
          simp [setIndicator, hmem, hslice]
      exact hindicator.symm
    · intro line hline hne
      have hnot : x - f ∉ slicePattern v line C := fun hy ↦
        hne ((mem_slicePattern (x - f)).1 hy).2.symm
      simp only [setIndicator, Set.indicator_of_notMem hnot]
    · intro hnot
      exact (hnot (Finset.mem_image.mpr ⟨f, hf, rfl⟩)).elim
  rw [hsumChosen, hsumSlices R]
  apply Finset.sum_congr rfl
  intro line _
  change tileConv F (setIndicator (S.chosen j line)) x =
    tileConv F (setIndicator (R ∩ quotientCoset H line)) x
  exact congrFun (S.convolution_equivalent j line) x

private theorem tiles_of_lineSelection
    (S : LineSelection F E T) (hF : F.Nonempty)
    (hvalid : validRepresentativeTupleBool F E T = true) :
    Tiles F (assembleLineSelection S) E.toSet := by
  let B : Fin (classifierDirectionCount F) → Set Plane := fun j ↦
    ⋃ line, S.chosen j line
  have hvalid' := (validRepresentativeTupleBool_eq_true_iff T).mp hvalid |>.2
  have hsum : setIndicator E.toSet = ∑ j, tileConv F (setIndicator (B j)) := by
    funext x
    simp only [Finset.sum_apply]
    calc
      setIndicator E.toSet x =
          ∑ j, tileConv F (setIndicator (T.representativeCode j).toSet) x :=
        (hvalid' x).symm
      _ = ∑ j, tileConv F (setIndicator (B j)) x := by
        apply Finset.sum_congr rfl
        intro j _
        exact (congrFun (lineSelection_direction_convolution S j) x).symm
  have hdisjoint := pairwiseDisjoint_of_sum_convolution F B E.toSet hF hsum
  have htiles := tiles_iUnion_of_sum_convolution F B E.toSet hdisjoint hsum
  simpa only [assembleLineSelection, B] using htiles

private theorem algorithm_onePartBound_le_structural
    {tileCard diameter directionNorm : ℕ} (hcard : 1 < tileCard) :
    onePartCompletionMultiplierBound tileCard diameter directionNorm ≤
      structuralCompletionPeriodBound tileCard diameter 1 directionNorm := by
  have hbase : 4 ^ (2 * tileCard) ≤
      (tileCard * 4 ^ (2 * tileCard)) ^ tileCard := by
    calc
      4 ^ (2 * tileCard) ≤ tileCard * 4 ^ (2 * tileCard) :=
        Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ (tileCard * 4 ^ (2 * tileCard)) ^ tileCard := Nat.le_pow (by omega)
  unfold onePartCompletionMultiplierBound structuralCompletionPeriodBound
  simpa only [one_mul, Nat.one_mul, Nat.add_comm 1] using
    Nat.mul_le_mul_right (max 1 (diameter ^ completionSliceExponent tileCard))
      (Nat.mul_le_mul_right
        (max 1 (directionNorm ^ (completionSliceExponent tileCard + 1))) hbase)

private theorem algorithm_weak_mul_structural_le_periodic
    {tileCard diameter numberOfParts directionProduct : ℕ}
    (hcard : 1 < tileCard) (hmpos : 0 < numberOfParts)
    (hmcard : numberOfParts ≤ tileCard - 1)
    (hHpos : 0 < directionProduct)
    (hHbound : directionProduct ≤ diameter ^ (tileCard - 1)) :
    weakPeriodMultiplierBound tileCard diameter *
        structuralCompletionPeriodBound tileCard diameter numberOfParts
          directionProduct ≤
      periodicTilingPeriodBound tileCard diameter := by
  let r := completionSliceExponent tileCard
  let weakExponent := tileCard * (tileCard - 1)
  let completionExponent :=
    (tileCard - 1) * (numberOfParts + r) + numberOfParts * r
  let totalExponent := weakExponent + completionExponent
  have hrPos : 0 < r := completionSliceExponent_pos hcard
  have hdiamPos : 0 < diameter := by
    by_contra hd
    have hd0 : diameter = 0 := Nat.eq_zero_of_not_pos hd
    rw [hd0] at hHbound
    simp [show 0 < tileCard - 1 by omega] at hHbound
    omega
  have htwoR : 2 * r = tileCard * (tileCard - 1) := by
    unfold r completionSliceExponent
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self tileCard)
  have hcompletionExponent : completionExponent ≤
      (tileCard + 1) * (tileCard - 1) ^ 2 := by
    dsimp [completionExponent]
    nlinarith
  have htotalExponent : totalExponent ≤ periodicTilingExponent tileCard := by
    unfold totalExponent weakExponent periodicTilingExponent
    calc
      tileCard * (tileCard - 1) + completionExponent ≤
          tileCard * (tileCard - 1) +
            (tileCard + 1) * (tileCard - 1) ^ 2 :=
        Nat.add_le_add_left hcompletionExponent _
      _ = (tileCard - 1) * (tileCard ^ 2 + tileCard - 1) := by
        let n := tileCard - 1
        have hc : tileCard = n + 1 := by
          dsimp [n]
          omega
        rw [hc]
        simp
        ring
  have hHpow : directionProduct ^ (numberOfParts + r) ≤
      diameter ^ ((tileCard - 1) * (numberOfParts + r)) := by
    calc
      directionProduct ^ (numberOfParts + r) ≤
          (diameter ^ (tileCard - 1)) ^ (numberOfParts + r) :=
        Nat.pow_le_pow_left hHbound _
      _ = diameter ^ ((tileCard - 1) * (numberOfParts + r)) := by rw [pow_mul]
  have hweakMax : max 1 (diameter ^ weakExponent) = diameter ^ weakExponent :=
    max_eq_right (Nat.one_le_pow _ _ hdiamPos)
  have hHMax : max 1 (directionProduct ^ (numberOfParts + r)) =
      directionProduct ^ (numberOfParts + r) :=
    max_eq_right (Nat.one_le_pow _ _ hHpos)
  have hdiamCompletionMax : max 1 (diameter ^ (numberOfParts * r)) =
      diameter ^ (numberOfParts * r) :=
    max_eq_right (Nat.one_le_pow _ _ hdiamPos)
  have hperiodMax : max 1 (diameter ^ periodicTilingExponent tileCard) =
      diameter ^ periodicTilingExponent tileCard :=
    max_eq_right (Nat.one_le_pow _ _ hdiamPos)
  have hconstantPos : 0 < periodicTilingConstant tileCard := by
    have hfactor : 0 < (tileCard * 4 ^ (2 * tileCard)) ^ tileCard := by
      cases tileCard with
      | zero => simp
      | succ n => positivity
    unfold periodicTilingConstant weakPeriodMultiplierConstant
    exact Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos (weakRigidityPeriod_pos tileCard) (by positivity))
        (by positivity))
      hfactor
  unfold periodicTilingPeriodBound
  have hperiodProduct : 1 ≤ periodicTilingConstant tileCard *
      max 1 (diameter ^ periodicTilingExponent tileCard) := by
    have hc : 1 ≤ periodicTilingConstant tileCard :=
      Nat.one_le_iff_ne_zero.mpr hconstantPos.ne'
    simpa using Nat.mul_le_mul hc
      (le_max_left 1 (diameter ^ periodicTilingExponent tileCard))
  rw [max_eq_right hperiodProduct, hperiodMax]
  unfold weakPeriodMultiplierBound structuralCompletionPeriodBound
    periodicTilingConstant
  rw [hweakMax, hHMax, hdiamCompletionMax]
  calc
    weakPeriodMultiplierConstant tileCard * diameter ^ weakExponent *
        ((tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
          directionProduct ^ (numberOfParts + r) *
          diameter ^ (numberOfParts * r)) ≤
      weakPeriodMultiplierConstant tileCard * diameter ^ weakExponent *
        ((tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
          diameter ^ ((tileCard - 1) * (numberOfParts + r)) *
          diameter ^ (numberOfParts * r)) := by
      gcongr
    _ = weakPeriodMultiplierConstant tileCard *
        (tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
          diameter ^ totalExponent := by
      dsimp [totalExponent, completionExponent]
      calc
        weakPeriodMultiplierConstant tileCard * diameter ^ weakExponent *
            ((tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
              diameter ^ ((tileCard - 1) * (numberOfParts + r)) *
              diameter ^ (numberOfParts * r)) =
            weakPeriodMultiplierConstant tileCard *
              (tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
                (diameter ^ weakExponent *
                  (diameter ^ ((tileCard - 1) * (numberOfParts + r)) *
                    diameter ^ (numberOfParts * r))) := by ring
        _ = weakPeriodMultiplierConstant tileCard *
              (tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
                diameter ^
                  (weakExponent + ((tileCard - 1) * (numberOfParts + r) +
                    numberOfParts * r)) := by rw [pow_add, pow_add]
    _ ≤ weakPeriodMultiplierConstant tileCard *
        (tileCard * 4 ^ (2 * tileCard)) ^ tileCard *
          diameter ^ periodicTilingExponent tileCard := by
      gcongr

/-- Produce a bounded weak multiplier and a directional tiling decomposition aligned exactly with
the canonical classifier directions. -/
theorem directionalDecomposition_uniform_classifier
    {E : PeriodicSetCode 2}
    (_hF : F.Nonempty) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic E.period E.toSet) (htile : Tiles F A E.toSet) :
    ∃ (L : ℕ), 0 < L ∧ L ≤ classifierWeakBound F ∧
      ∃ D : DirectionalTilingDecomposition F A E.toSet (E.period * L),
        ∃ hnum : D.numberOfParts = classifierDirectionCount F,
          ∀ j : Fin (classifierDirectionCount F),
            D.direction (Fin.cast hnum.symm j) = classifierDirection F j := by
  classical
  obtain ⟨G, hnum, hcanonical⟩ :=
    exists_groupedStructureDecomposition_canonical
      E.period_pos hzero hcard hE htile
  let W := Classical.choice (exists_weakArithmeticData G E.period_pos)
  have hprodL1 (j : Fin G.numberOfDirections) :
      l1Norm (G.direction j) ≤
        ∏ i : Fin G.numberOfDirections, l1Norm (G.direction i) := by
    exact Finset.single_le_prod'
      (s := (Finset.univ : Finset (Fin G.numberOfDirections)))
      (f := fun i ↦ l1Norm (G.direction i)) (a := j)
      (fun i _ ↦ by
        rw [Nat.one_le_iff_ne_zero]
        exact fun hz ↦ G.direction_ne_zero i (l1Norm_eq_zero.mp hz))
      (Finset.mem_univ j)
  have hprodEuclidean (j : Fin G.numberOfDirections) :
      euclideanNorm (G.direction j) ≤
        ∏ i : Fin G.numberOfDirections, euclideanNorm (G.direction i) := by
    calc
      euclideanNorm (G.direction j) =
          ∏ i ∈ ({j} : Finset (Fin G.numberOfDirections)),
            euclideanNorm (G.direction i) := by simp
      _ ≤ ∏ i ∈ (Finset.univ : Finset (Fin G.numberOfDirections)),
            euclideanNorm (G.direction i) := by
        apply Finset.prod_le_prod_of_subset_of_one_le
        · exact Finset.singleton_subset_iff.mpr (Finset.mem_univ j)
        · intro i _
          exact norm_nonneg _
        · intro i _ _
          exact one_le_euclideanNorm (G.direction_ne_zero i)
      _ = _ := by simp
  let Q : QuantitativeWeakPeriodData F E.period := {
    numberOfDirections := G.numberOfDirections
    number_pos := G.number_pos
    number_le := G.number_le
    direction := G.direction
    direction_ne_zero := G.direction_ne_zero
    pairwise_incommensurable := G.pairwise_incommensurable
    direction_from_tile := G.direction_from_tile
    direction_l1_bound := fun j ↦ by
      simpa only [weakPeriodVectorBound] using
        (hprodL1 j).trans G.product_direction_l1_bound
    direction_euclidean_bound := fun j ↦
      (hprodEuclidean j).trans G.product_direction_euclidean_bound
    product_direction_l1_bound := G.product_direction_l1_bound
    product_direction_euclidean_bound := G.product_direction_euclidean_bound
    arithmetic := W
    lattice_le := by
      rw [W.lattice_eq]
      exact weakLattice_le_scalar G E.period_pos
    relativeIndex_bound := by
      rw [W.lattice_eq]
      exact weakLattice_relativeIndex_bound G E.period_pos
    multiplier_bound := by
      rw [W.multiplier_eq]
      exact weakMultiplier_bound G E.period_pos
    period_mem_lattice := by
      intro j
      rw [W.exact_scalar_factor]
      exact W.advertisedPeriod_mem j
  }
  have hvalid : Q.ValidFor A := by
    have hbase := coset_one_dimensional_periodicity G E.period_pos hE
    change CosetwisePeriodic A Q.lattice
      (fun j ↦ ((E.period * Q.multiplier : ℕ) : ℤ) • Q.direction j)
    dsimp [Q, QuantitativeWeakPeriodData.lattice,
      QuantitativeWeakPeriodData.multiplier] at ⊢
    simpa only [W.lattice_eq, W.multiplier_eq, Nat.cast_mul] using hbase
  obtain ⟨D, hDnum, hDdir⟩ :=
    exists_directionalTilingDecomposition_of_quantitativeData
      E.period_pos hE htile Q hvalid
  refine ⟨W.multiplier, W.multiplier_pos, ?_, D, ?_⟩
  · simpa only [classifierWeakBound, W.multiplier_eq] using
      weakMultiplier_bound G E.period_pos
  · have hout : D.numberOfParts = classifierDirectionCount F :=
      hDnum.trans hnum
    refine ⟨hout, fun j ↦ ?_⟩
    let jG : Fin G.numberOfDirections := Fin.cast hnum.symm j
    calc
      D.direction (Fin.cast hout.symm j) =
          D.direction (Fin.cast hDnum.symm jG) := by
            congr
      _ = G.direction jG := hDdir jG
      _ = classifierDirection F j := by
        simpa only [jG, classifierDirection] using hcanonical j

end TranslationalTilings

/- blueprint/08-algorithms.md:921; TranslationalTilings.nonOnePeriodicTilingDecisionNormalized -/
namespace TranslationalTilings
/-- Test whether some valid normalized tuple has at least two chameleon directions. -/
def nonOnePeriodicTilingDecisionNormalized
    (F : Finset Plane) (E : PeriodicSetCode 2) : Bool :=
  finsetAnyBool (representativeTuples F E) fun T ↦
    decide (2 ≤ (Finset.univ.filter fun j ↦
      hasChameleonSlice F E T j = true).card)
end TranslationalTilings

/- blueprint/08-algorithms.md:927; TranslationalTilings.nonOnePeriodicTilingDecision -/
namespace TranslationalTilings
/-- Handle degenerate inputs, normalize the tiling problem, and run the chameleon classifier. -/
def nonOnePeriodicTilingDecision
    (F : Finset Plane) (E : PeriodicSetCode 2) : Bool :=
  if F = ∅ then false
  else if F.card = 1 then false
  else if E.isEmptyBool then false
  else
    nonOnePeriodicTilingDecisionNormalized
      (normalizedTile F) (normalizedTargetCode F E)
end TranslationalTilings

/- blueprint/08-algorithms.md:936; TranslationalTilings.nonOnePeriodicTilingDecisionLatticeInput -/
namespace TranslationalTilings
/-- Run the non-one-periodic classifier after converting an HNF lattice target to scalar form. -/
def nonOnePeriodicTilingDecisionLatticeInput
    (F : Finset Plane) (E : LatticePeriodicSetCode) : Bool :=
  nonOnePeriodicTilingDecision F E.toScalarCode
end TranslationalTilings

namespace TranslationalTilings

/-- A singleton tile forces its complement to be the corresponding translate of the target. -/
theorem singleton_tile_complement_eq_target
    {E : PeriodicSetCode 2}
    (hcard : F.card = 1) (htile : Tiles F A E.toSet) :
    ∃ a ∈ F, A = {x | x + a ∈ E.toSet} := by
  classical
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  refine ⟨a, Finset.mem_singleton_self a, ?_⟩
  ext x
  have hx := htile (x + a)
  simp only [tileConv, Finset.sum_singleton, add_sub_cancel_right] at hx
  by_cases hA : x ∈ A <;> by_cases hE : x + a ∈ E.toSet <;>
    simp [setIndicator, hA, hE] at hx ⊢

/-- If a nonempty tile tiles the empty target, its complement must be empty. -/
theorem empty_target_complement_empty
    {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hE : E.toSet = ∅)
    (htile : Tiles F A E.toSet) :
    A = ∅ := by
  classical
  rw [Tiles, tilesAtLevel_iff_representation_count] at htile
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨f, hf⟩ := hF
  have hcount := htile (x + f)
  rw [hE] at hcount
  simp only [Set.mem_empty_iff_false, if_false] at hcount
  have hmem : f ∈ (@Finset.filter _
      (fun g ↦ x + f - g ∈ A) (fun _ ↦ Classical.propDecidable _) F) := by
    simp only [Finset.mem_filter, hf, true_and]
    simpa only [add_sub_cancel_right] using hx
  have hpos := Finset.card_pos.mpr ⟨f, hmem⟩
  omega

/-- The empty tile admits no complement tiling a nonempty target. -/
theorem empty_tile_no_nonempty_target_tiling
    {E : PeriodicSetCode 2}
    (hE : E.toSet.Nonempty) :
    ¬ ∃ A, Tiles (∅ : Finset Plane) A E.toSet := by
  classical
  rintro ⟨A, htile⟩
  rw [Tiles, tilesAtLevel_iff_representation_count] at htile
  obtain ⟨x, hx⟩ := hE
  have hcount := htile x
  simp only [Finset.filter_empty, Finset.card_empty, if_pos hx] at hcount
  omega

end TranslationalTilings

namespace TranslationalTilings

private theorem setIndicator_periodic_of_membership
    {G : Type*} [AddCommGroup G] {B : Set G} {t : G}
    (hB : ∀ x, x + t ∈ B ↔ x ∈ B) :
    Function.Periodic (setIndicator B) t := by
  intro x
  by_cases hx : x ∈ B
  · have hxt : x + t ∈ B := (hB x).mpr hx
    simp [setIndicator, hx, hxt]
  · have hxt : x + t ∉ B := fun h ↦ hx ((hB x).mp h)
    simp [setIndicator, hx, hxt]

private theorem setIndicator_union_eq_add_of_disjoint
    {G : Type*} {B C : Set G} (hBC : Disjoint B C) :
    setIndicator (B ∪ C) = setIndicator B + setIndicator C := by
  classical
  funext x
  rw [Set.disjoint_left] at hBC
  by_cases hxB : x ∈ B
  · by_cases hxC : x ∈ C
    · exact (hBC hxB hxC).elim
    · simp [setIndicator, hxB, hxC]
  · by_cases hxC : x ∈ C <;> simp [setIndicator, hxB, hxC]

private theorem convolutionEquivalent_replace
    {G : Type*} [AddCommGroup G] (F : Finset G)
    {R B C : Set G} (hC : C ⊆ R) (hdisjoint : Disjoint B (R \ C))
    (hconv : convolutionEquivalent F B C) :
    convolutionEquivalent F (B ∪ (R \ C)) R := by
  classical
  have hR : R = C ∪ (R \ C) := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hxR
      by_cases hxC : x ∈ C
      · exact Or.inl hxC
      · exact Or.inr ⟨hxR, hxC⟩
    · rintro (hxC | ⟨hxR, -⟩)
      · exact hC hxC
      · exact hxR
  have hCR : Disjoint C (R \ C) := by
    rw [Set.disjoint_left]
    exact fun _ hxC hxRC ↦ hxRC.2 hxC
  have hleft : setIndicator (B ∪ (R \ C)) =
      setIndicator B + setIndicator (R \ C) :=
    setIndicator_union_eq_add_of_disjoint (B := B) (C := R \ C) hdisjoint
  have hright : setIndicator (C ∪ (R \ C)) =
      setIndicator C + setIndicator (R \ C) :=
    setIndicator_union_eq_add_of_disjoint (B := C) (C := R \ C) hCR
  have hrightR : setIndicator R = setIndicator C + setIndicator (R \ C) := by
    calc
      setIndicator R = setIndicator (C ∪ (R \ C)) := congrArg setIndicator hR
      _ = setIndicator C + setIndicator (R \ C) := hright
  change tileConv F (setIndicator (B ∪ (R \ C))) =
    tileConv F (setIndicator R)
  rw [hleft, hrightR]
  funext x
  unfold tileConv
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  exact congrArg (fun z ↦ z + ∑ f ∈ F, setIndicator (R \ C) (x - f))
    (congrFun hconv x)

private theorem classifierDirection_canonical_key
    (F : Finset Plane) (j : Fin (classifierDirectionCount F)) :
    canonicalDirection (classifierDirection F j) =
      pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl j) := by
  let p := (groupedDirectionPairs F).orderEmbOfFin rfl j
  let v := pairToPlane p
  have hpMem : planeToPair v ∈ groupedDirectionPairs F := by
    rw [algorithms_planeToPair_pairToPlane]
    exact Finset.orderEmbOfFin_mem (groupedDirectionPairs F) rfl j
  obtain ⟨f, hf, hfv⟩ := Finset.mem_image.mp hpMem
  have hfne : f ≠ 0 := Finset.ne_of_mem_erase hf
  have hcanon : canonicalDirection f = v := algorithms_planeToPair_injective hfv
  have hscale : 0 < groupedDirectionScale F v := by
    rw [Nat.pos_iff_ne_zero]
    intro hzero
    rw [groupedDirectionScale, Finset.lcm_eq_zero_iff] at hzero
    obtain ⟨g, hg, hgzero⟩ := hzero
    have hgne : g ≠ 0 :=
      Finset.ne_of_mem_erase (Finset.mem_filter.mp hg).1
    exact (Nat.ne_of_gt (vectorContent_pos hgne)) hgzero
  obtain ⟨z, hz, hfz⟩ := tile_integer_multiple_of_canonicalDirection hfne
  have hc : canonicalDirection (classifierDirection F j) = canonicalDirection f := by
    apply (canonicalDirection_eq_iff_commensurable
      (classifierDirection_ne_zero F j) hfne).2
    refine ⟨z, (groupedDirectionScale F v : ℤ), hz,
      by exact_mod_cast hscale.ne', ?_⟩
    calc
      z • classifierDirection F j =
          z • ((groupedDirectionScale F v : ℤ) • v) := by rfl
      _ = (groupedDirectionScale F v : ℤ) •
          (z • canonicalDirection f) := by rw [hcanon]; module
      _ = (groupedDirectionScale F v : ℤ) • f :=
        congrArg ((groupedDirectionScale F v : ℤ) • ·) hfz.symm
  exact hc.trans hcanon

private theorem classifierDirection_pairwise (F : Finset Plane) :
    PairwiseIncommensurable (classifierDirection F) := by
  intro i j hij hcomm
  have hcanon := (canonicalDirection_eq_iff_commensurable
    (classifierDirection_ne_zero F i) (classifierDirection_ne_zero F j)).2 hcomm
  rw [classifierDirection_canonical_key F i,
    classifierDirection_canonical_key F j] at hcanon
  apply hij
  apply ((groupedDirectionPairs F).orderEmbOfFin rfl).injective
  have hp := congrArg planeToPair hcanon
  simpa only [algorithms_planeToPair_pairToPlane] using hp

private theorem classifierPrimitiveDirection_pairwise (F : Finset Plane) :
    PairwiseIncommensurable (classifierPrimitiveDirection F) := by
  intro i j hij hcomm
  apply classifierDirection_pairwise F i j hij
  have hdi := (primitive_decomposition (classifierDirection_ne_zero F i)).1
  have hdj := (primitive_decomposition (classifierDirection_ne_zero F j)).1
  have hpi := classifierPrimitiveDirection_ne_zero F i
  have hpj := classifierPrimitiveDirection_ne_zero F j
  have hw := (commensurable_iff_wedge_eq_zero hpi hpj).1 hcomm
  change wedge (primitivePart (classifierDirection F i))
    (primitivePart (classifierDirection F j)) = 0 at hw
  apply (commensurable_iff_wedge_eq_zero
    (classifierDirection_ne_zero F i) (classifierDirection_ne_zero F j)).2
  rw [← hdi, ← hdj, wedge_zsmul_left, wedge_zsmul_right, hw]
  ring

private theorem wedge_eq_zero_of_mem_directionSubgroup
    {v d : Plane} (hd : d ∈ directionSubgroup v) :
    wedge v d = 0 := by
  obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hd
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

private theorem mem_line_of_mem_add_direction
    {v x y t : Plane}
    (hx : x ∈ addCoset (directionSubgroup v) y)
    (ht : t ∈ directionSubgroup v) :
    x + t ∈ addCoset (directionSubgroup v) y := by
  change x - y ∈ directionSubgroup v at hx
  change x + t - y ∈ directionSubgroup v
  convert (directionSubgroup v).add_mem hx ht using 1
  abel

private theorem commensurable_of_commensurable_right
    {u v t : Plane} (hu : Commensurable u t) (hv : Commensurable v t) :
    Commensurable u v := by
  obtain ⟨a, b, ha, hb, hut⟩ := hu
  obtain ⟨c, d, hc, hd, hvt⟩ := hv
  refine ⟨d * a, b * c, mul_ne_zero hd ha, mul_ne_zero hb hc, ?_⟩
  calc
    (d * a) • u = d • (a • u) := by module
    _ = d • (b • t) := congrArg (d • ·) hut
    _ = b • (d • t) := by module
    _ = b • (c • v) := congrArg (b • ·) hvt.symm
    _ = (b * c) • v := by module

private theorem direction_wedge_period_eq_zero_of_supported_on_two_lines
    {g : Plane → ℤ} {v₁ v₂ y₁ y₂ t x : Plane}
    (hperiod : Function.Periodic g t)
    (hsupport : ∀ z, g z ≠ 0 →
      z ∈ addCoset (directionSubgroup v₁) y₁ ∨
      z ∈ addCoset (directionSubgroup v₂) y₂)
    (hxg : g x ≠ 0)
    (hx₁ : x ∈ addCoset (directionSubgroup v₁) y₁)
    (hx₂ : x ∉ addCoset (directionSubgroup v₂) y₂) :
    wedge v₁ t = 0 := by
  have hxtg : g (x + t) ≠ 0 := by
    rw [hperiod x]
    exact hxg
  have hx2tg : g (x + (2 : ℤ) • t) ≠ 0 := by
    have hp2 := hperiod.zsmul (2 : ℤ) x
    intro hzero
    apply hxg
    rw [← hp2]
    exact hzero
  rcases hsupport (x + t) hxtg with hxt₁ | hxt₂
  · apply wedge_eq_zero_of_mem_directionSubgroup
    have hxt₁' : x + t - y₁ ∈ directionSubgroup v₁ := hxt₁
    have hx₁' : x - y₁ ∈ directionSubgroup v₁ := hx₁
    have hmem := (directionSubgroup v₁).sub_mem hxt₁' hx₁'
    convert hmem using 1
    abel
  · rcases hsupport (x + (2 : ℤ) • t) hx2tg with hx2t₁ | hx2t₂
    · have htwo : wedge v₁ ((2 : ℤ) • t) = 0 := by
        apply wedge_eq_zero_of_mem_directionSubgroup
        have hx2t₁' : x + (2 : ℤ) • t - y₁ ∈ directionSubgroup v₁ := hx2t₁
        have hx₁' : x - y₁ ∈ directionSubgroup v₁ := hx₁
        have hmem := (directionSubgroup v₁).sub_mem hx2t₁' hx₁'
        convert hmem using 1
        abel
      rw [wedge_zsmul_right] at htwo
      exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    · apply (hx₂ ?_).elim
      have ht₂ : t ∈ directionSubgroup v₂ := by
        have hx2t₂' : x + (2 : ℤ) • t - y₂ ∈ directionSubgroup v₂ := hx2t₂
        have hxt₂' : x + t - y₂ ∈ directionSubgroup v₂ := hxt₂
        have hmem := (directionSubgroup v₂).sub_mem hx2t₂' hxt₂'
        convert hmem using 1
        module
      have hback := mem_line_of_mem_add_direction hxt₂
        ((directionSubgroup v₂).neg_mem ht₂)
      convert hback using 1
      module

private theorem exists_nonzero_off_transverse_line
    {g : Plane → ℤ} {v₁ v₂ y₁ y₂ x : Plane} {k : ℤ}
    (hk : k ≠ 0) (htransverse : wedge v₂ v₁ ≠ 0)
    (hperiod : Function.Periodic g (k • v₁))
    (hsupport : ∀ z, g z ≠ 0 →
      z ∈ addCoset (directionSubgroup v₁) y₁)
    (hxg : g x ≠ 0) :
    ∃ z, g z ≠ 0 ∧
      z ∈ addCoset (directionSubgroup v₁) y₁ ∧
      z ∉ addCoset (directionSubgroup v₂) y₂ := by
  by_cases hx₂ : x ∈ addCoset (directionSubgroup v₂) y₂
  · let z := x + k • v₁
    have hzg : g z ≠ 0 := by
      intro hz
      apply hxg
      rw [← hperiod x]
      exact hz
    refine ⟨z, hzg, hsupport z hzg, ?_⟩
    intro hz₂
    have hmem : k • v₁ ∈ directionSubgroup v₂ := by
      have hz₂' : z - y₂ ∈ directionSubgroup v₂ := hz₂
      have hx₂' : x - y₂ ∈ directionSubgroup v₂ := hx₂
      have hd := (directionSubgroup v₂).sub_mem hz₂' hx₂'
      dsimp only [z] at hd
      convert hd using 1
      module
    have hwedge := wedge_eq_zero_of_mem_directionSubgroup hmem
    rw [wedge_zsmul_right] at hwedge
    exact htransverse ((mul_eq_zero.mp hwedge).resolve_left hk)
  · exact ⟨x, hxg, hsupport x hxg, hx₂⟩

private theorem eq_zero_of_two_incommensurable_wedges
    {v₁ v₂ t : Plane}
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hincommensurable : ¬ Commensurable v₁ v₂)
    (hw₁ : wedge v₁ t = 0) (hw₂ : wedge v₂ t = 0) :
    t = 0 := by
  by_contra ht
  apply hincommensurable
  exact commensurable_of_commensurable_right
    ((commensurable_iff_wedge_eq_zero hv₁ ht).mpr hw₁)
    ((commensurable_iff_wedge_eq_zero hv₂ ht).mpr hw₂)

private theorem algorithm_indicator_eq_iff_membership {G : Type*}
    (A : Set G) (u v : G) :
    setIndicator A u = setIndicator A v ↔ (u ∈ A ↔ v ∈ A) := by
  by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;>
    simp [setIndicator, hu, hv]

private theorem algorithm_indicator_scalarPeriodic {d q : ℕ}
    {E : Set (Lattice d)} (hE : SetScalarPeriodic q E) :
    ScalarPeriodic q (setIndicator E) := by
  intro x z
  apply (algorithm_indicator_eq_iff_membership E _ _).2
  exact hE x z

private theorem completion_component_period_dvd_classifier
    {F : Finset Plane} {E : PeriodicSetCode 2} {A : Set Plane} {L : ℕ}
    (D : DirectionalTilingDecomposition F A E.toSet (E.period * L))
    (hLpos : 0 < L) (hKpos : 0 < completionMultiplier D)
    (hLKbound : L * completionMultiplier D ≤ classifierRepresentativeBound F)
    (j : Fin D.numberOfParts) :
    E.period * L * completionPairLCM D * completionPartMultiplier D j ∣
      classifierPeriod F E := by
  have hpart : completionPartMultiplier D j ∣
      ∏ i : Fin D.numberOfParts, completionPartMultiplier D i :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hlocal :
      E.period * L * completionPairLCM D * completionPartMultiplier D j ∣
        E.period * (L * completionMultiplier D) := by
    unfold completionMultiplier
    simpa only [Nat.mul_assoc] using
      Nat.mul_dvd_mul_left (E.period * L * completionPairLCM D) hpart
  have hfactorial : L * completionMultiplier D ∣
      (classifierRepresentativeBound F).factorial :=
    Nat.dvd_factorial (Nat.mul_pos hLpos hKpos) hLKbound
  apply hlocal.trans
  unfold classifierPeriod
  simpa only [Nat.mul_assoc] using Nat.mul_dvd_mul_left E.period hfactorial

private theorem one_component_period_dvd_classifier
    {F : Finset Plane} {E : PeriodicSetCode 2} {A : Set Plane} {L : ℕ}
    (D : DirectionalTilingDecomposition F A E.toSet (E.period * L))
    (hLpos : 0 < L) (hKpos : 0 < onePartCompletionMultiplier D)
    (hLKbound : L * onePartCompletionMultiplier D ≤
      classifierRepresentativeBound F) :
    (E.period * L) * onePartCompletionMultiplier D ∣ classifierPeriod F E := by
  have hfactorial : L * onePartCompletionMultiplier D ∣
      (classifierRepresentativeBound F).factorial :=
    Nat.dvd_factorial (Nat.mul_pos hLpos hKpos) hLKbound
  unfold classifierPeriod
  simpa only [Nat.mul_assoc] using Nat.mul_dvd_mul_left E.period hfactorial

private theorem directional_product_bound
    {F : Finset Plane} {E : PeriodicSetCode 2} {A : Set Plane} {L : ℕ}
    (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (htiles : Tiles F A E.toSet)
    (D : DirectionalTilingDecomposition F A E.toSet (E.period * L))
    (hnum : D.numberOfParts = classifierDirectionCount F)
    (hdir : ∀ j : Fin (classifierDirectionCount F),
      D.direction (Fin.cast hnum.symm j) = classifierDirection F j) :
    ∏ i : Fin D.numberOfParts, l1Norm (D.direction i) ≤
      l1Diameter F ^ (F.card - 1) := by
  obtain ⟨G, hGnum, hGdir⟩ :=
    exists_groupedStructureDecomposition_canonical E.period_pos hzero hcard
      E.toSet_scalarPeriodic htiles
  have hDprod :
      (∏ i : Fin D.numberOfParts, l1Norm (D.direction i)) =
        ∏ j : Fin (classifierDirectionCount F), l1Norm (classifierDirection F j) := by
    symm
    exact Fintype.prod_equiv (Fin.castOrderIso hnum.symm).toEquiv
      (fun j ↦ l1Norm (classifierDirection F j))
      (fun i ↦ l1Norm (D.direction i))
      (fun j ↦ congrArg l1Norm (hdir j).symm)
  have hGprod :
      (∏ j : Fin (classifierDirectionCount F), l1Norm (classifierDirection F j)) =
        ∏ i : Fin G.numberOfDirections, l1Norm (G.direction i) := by
    exact Fintype.prod_equiv (Fin.castOrderIso hGnum.symm).toEquiv
      (fun j ↦ l1Norm (classifierDirection F j))
      (fun i ↦ l1Norm (G.direction i))
      (fun j ↦ congrArg l1Norm (hGdir j).symm)
  rw [hDprod, hGprod]
  exact G.product_direction_l1_bound

private theorem component_improvement_with_slices
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hm : 2 ≤ D.numberOfParts)
    (j : Fin D.numberOfParts) :
    ∃ A' : Set Plane,
      SetScalarPeriodic
        (ell * completionPairLCM D * completionPartMultiplier D j) A' ∧
      convolutionEquivalent F (D.part j) A' ∧
      ∀ line : Plane ⧸ directionSubgroup (completionPrimitiveDirection D j),
        convolutionEquivalent F
          (slicePattern (completionPrimitiveDirection D j) line (D.part j))
          (slicePattern (completionPrimitiveDirection D j) line A') := by
  have hconv := convolution_part_scalarPeriodic D hm j
  have hdecomp := primitive_decomposition (D.direction_ne_zero j)
  have hcontentPos : 0 < completionDirectionContent D j :=
    vectorContent_pos (D.direction_ne_zero j)
  have hpartPeriod : Function.Periodic (setIndicator (D.part j))
      ((((ell * completionConvolutionMultiplier D j) *
        completionDirectionContent D j : ℕ) : ℤ) •
          completionPrimitiveDirection D j) := by
    have hp := (D.periodic_part j).zsmul
      (completionConvolutionMultiplier D j : ℤ)
    have hshift :
        ((((ell * completionConvolutionMultiplier D j) *
          completionDirectionContent D j : ℕ) : ℤ) •
            completionPrimitiveDirection D j) =
          (completionConvolutionMultiplier D j : ℤ) •
            ((ell : ℤ) • D.direction j) := by
      have hdirection : D.direction j =
          (completionDirectionContent D j : ℤ) •
            completionPrimitiveDirection D j := hdecomp.1.symm
      rw [hdirection]
      push_cast
      module
    rw [hshift]
    exact hp
  obtain ⟨A', hperiod, hconvolution, hslices⟩ := improve_onePeriodic
    (Nat.mul_pos hell hconv.1) hcontentPos hdecomp.2 hpartPeriod hconv.2.2
  refine ⟨A', ?_, hconvolution, hslices⟩
  convert hperiod using 1
  have hfactor :
      indicatorDilationModulus
          (ell * completionConvolutionMultiplier D j) F.card =
        (ell * completionConvolutionMultiplier D j) *
          completionDilationRatio D j := by
    exact (Nat.mul_div_cancel' (ell_dvd_dilationModulus
      (ell * completionConvolutionMultiplier D j) 1 F.card)).symm
  rw [hfactor]
  unfold completionConvolutionMultiplier completionPartMultiplier
    completionSliceLCM completionPrimitiveDirection
  ring

private theorem classifier_component_improvement
    {F : Finset Plane} {E : PeriodicSetCode 2} {A : Set Plane} {L : ℕ}
    (D : DirectionalTilingDecomposition F A E.toSet (E.period * L))
    (hLpos : 0 < L) (hm : 2 ≤ D.numberOfParts)
    (hnum : D.numberOfParts = classifierDirectionCount F)
    (hdir : ∀ j : Fin (classifierDirectionCount F),
      D.direction (Fin.cast hnum.symm j) = classifierDirection F j)
    (j : Fin (classifierDirectionCount F)) :
    ∃ B : Set Plane,
      SetScalarPeriodic
        ((E.period * L) * completionPairLCM D *
          completionPartMultiplier D (Fin.cast hnum.symm j)) B ∧
      convolutionEquivalent F (D.part (Fin.cast hnum.symm j)) B ∧
      ∀ line : Plane ⧸ directionSubgroup (classifierPrimitiveDirection F j),
        convolutionEquivalent F
          (slicePattern (classifierPrimitiveDirection F j) line
            (D.part (Fin.cast hnum.symm j)))
          (slicePattern (classifierPrimitiveDirection F j) line B) := by
  let i : Fin D.numberOfParts := Fin.cast hnum.symm j
  have hconv := convolution_part_scalarPeriodic D hm i
  have hdirNe : classifierDirection F j ≠ 0 := by
    rw [← hdir j]
    exact D.direction_ne_zero i
  have hdecomp := primitive_decomposition hdirNe
  have hcontentPos : 0 < vectorContent (classifierDirection F j) :=
    vectorContent_pos hdirNe
  have hpartPeriod : Function.Periodic (setIndicator (D.part i))
      (((((E.period * L) * completionConvolutionMultiplier D i) *
        vectorContent (classifierDirection F j) : ℕ) : ℤ) •
          classifierPrimitiveDirection F j) := by
    have hp := (D.periodic_part i).zsmul
      (completionConvolutionMultiplier D i : ℤ)
    have hshift :
        (((((E.period * L) * completionConvolutionMultiplier D i) *
          vectorContent (classifierDirection F j) : ℕ) : ℤ) •
            classifierPrimitiveDirection F j) =
          (completionConvolutionMultiplier D i : ℤ) •
            (((E.period * L : ℕ) : ℤ) • D.direction i) := by
      calc
        (((((E.period * L) * completionConvolutionMultiplier D i) *
            vectorContent (classifierDirection F j) : ℕ) : ℤ) •
              classifierPrimitiveDirection F j) =
            (completionConvolutionMultiplier D i : ℤ) •
              (((E.period * L : ℕ) : ℤ) •
                ((vectorContent (classifierDirection F j) : ℤ) •
                  classifierPrimitiveDirection F j)) := by
          push_cast
          module
        _ = (completionConvolutionMultiplier D i : ℤ) •
              (((E.period * L : ℕ) : ℤ) • classifierDirection F j) := by
          exact congrArg (fun v ↦ (completionConvolutionMultiplier D i : ℤ) •
            (((E.period * L : ℕ) : ℤ) • v)) hdecomp.1
        _ = (completionConvolutionMultiplier D i : ℤ) •
              (((E.period * L : ℕ) : ℤ) • D.direction i) := by
          exact congrArg (fun v ↦ (completionConvolutionMultiplier D i : ℤ) •
            (((E.period * L : ℕ) : ℤ) • v)) (hdir j).symm
    rw [hshift]
    exact hp
  obtain ⟨B, hperiod, hconvolution, hslices⟩ := improve_onePeriodic
    (Nat.mul_pos (Nat.mul_pos E.period_pos hLpos) hconv.1)
    hcontentPos hdecomp.2 hpartPeriod hconv.2.2
  refine ⟨B, ?_, hconvolution, hslices⟩
  convert hperiod using 1
  have hfactor : indicatorDilationModulus
        ((E.period * L) * completionConvolutionMultiplier D i) F.card =
      ((E.period * L) * completionConvolutionMultiplier D i) *
        completionDilationRatio D i := by
    exact (Nat.mul_div_cancel' (ell_dvd_dilationModulus
      ((E.period * L) * completionConvolutionMultiplier D i) 1 F.card)).symm
  have hcontent : completionDirectionContent D i =
      vectorContent (classifierDirection F j) := by
    unfold completionDirectionContent
    rw [hdir j]
  have hslice : completionSliceLCM D i =
      slicingLCM F (classifierPrimitiveDirection F j) := by
    unfold completionSliceLCM completionPrimitiveDirection
      classifierPrimitiveDirection
    rw [hdir j]
  dsimp only [i] at hfactor hcontent hslice ⊢
  rw [hfactor]
  unfold completionConvolutionMultiplier completionPartMultiplier
  rw [hcontent, hslice]
  simp only [classifierPrimitiveDirection]
  ring

private theorem one_component_improvement_with_slices
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : DirectionalTilingDecomposition F A E ell)
    (hell : 0 < ell) (hone : D.numberOfParts = 1) :
    let j : Fin D.numberOfParts := ⟨0, D.number_pos⟩
    ∃ A' : Set Plane,
      SetScalarPeriodic (ell * onePartCompletionMultiplier D) A' ∧
      convolutionEquivalent F (D.part j) A' ∧
      ∀ line : Plane ⧸ directionSubgroup (completionPrimitiveDirection D j),
        convolutionEquivalent F
          (slicePattern (completionPrimitiveDirection D j) line (D.part j))
          (slicePattern (completionPrimitiveDirection D j) line A') := by
  let j : Fin D.numberOfParts := ⟨0, D.number_pos⟩
  have hfin (i : Fin D.numberOfParts) : i = j := by
    apply Fin.ext
    have hi := i.isLt
    dsimp [j]
    omega
  have hpartA : D.part j = A := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [← D.union_parts]
      exact Set.mem_iUnion.mpr ⟨j, hx⟩
    · intro x hx
      rw [← D.union_parts] at hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      simpa only [hfin i] using hxi
  have hdecomp := primitive_decomposition (D.direction_ne_zero j)
  have hcontentPos : 0 < completionDirectionContent D j :=
    vectorContent_pos (D.direction_ne_zero j)
  have hperiodPart : Function.Periodic (setIndicator (D.part j))
      (((ell * completionDirectionContent D j : ℕ) : ℤ) •
        completionPrimitiveDirection D j) := by
    have hp := D.periodic_part j
    have hshift : (((ell * completionDirectionContent D j : ℕ) : ℤ) •
        completionPrimitiveDirection D j) =
        ((ell : ℕ) : ℤ) • D.direction j := by
      calc
        (((ell * completionDirectionContent D j : ℕ) : ℤ) •
            completionPrimitiveDirection D j) =
            (ell : ℤ) • ((completionDirectionContent D j : ℤ) •
              completionPrimitiveDirection D j) := by
          push_cast
          module
        _ = (ell : ℤ) • D.direction j := congrArg ((ell : ℤ) • ·) hdecomp.1
    rw [hshift]
    exact hp
  have hconvPeriod : ScalarPeriodic ell
      (tileConv F (setIndicator (D.part j))) := by
    intro x z
    rw [hpartA, D.tiles x, D.tiles (x + (ell : ℤ) • z)]
    rw [algorithm_indicator_scalarPeriodic D.target_periodic x z]
  obtain ⟨A', hperiod, hconvolution, hslices⟩ := improve_onePeriodic
    hell hcontentPos hdecomp.2 hperiodPart hconvPeriod
  refine ⟨A', ?_, hconvolution, hslices⟩
  have hcoeff : ell * onePartCompletionMultiplier D =
      indicatorDilationModulus ell F.card * completionDirectionContent D j *
        completionSliceLCM D j := by
    rw [onePartDilationRatio_spec D]
    simp only [onePartCompletionMultiplier, j]
    ring
  rw [hcoeff]
  exact hperiod

private theorem forward_classifier_assembly
    {F : Finset Plane} {E : PeriodicSetCode 2} {A : Set Plane} {L : ℕ}
    (hLpos : 0 < L) (hLbound : L ≤ classifierWeakBound F)
    (D : DirectionalTilingDecomposition F A E.toSet (E.period * L))
    (hnum : D.numberOfParts = classifierDirectionCount F)
    (hdir : ∀ j : Fin (classifierDirectionCount F),
      D.direction (Fin.cast hnum.symm j) = classifierDirection F j)
    (B : Fin (classifierDirectionCount F) → Set Plane)
    (hBperiod : ∀ j, SetScalarPeriodic (classifierPeriod F E) (B j))
    (hBconv : ∀ j, convolutionEquivalent F
      (D.part (Fin.cast hnum.symm j)) (B j))
    (hBslice : ∀ j
      (line : Plane ⧸ directionSubgroup (classifierPrimitiveDirection F j)),
      convolutionEquivalent F
        (slicePattern (classifierPrimitiveDirection F j) line
          (D.part (Fin.cast hnum.symm j)))
        (slicePattern (classifierPrimitiveDirection F j) line (B j))) :
    ∃ T ∈ representativeTuples F E, ProducedByTuple T A := by
  classical
  let code (j : Fin (classifierDirectionCount F)) : PeriodicSetCode 2 :=
    encodePeriodicSet (classifierPeriod F E) (classifierPeriod_pos F E) (B j)
  let T : RepresentativeTupleCode F E := {
    weakMultiplier := ⟨L, Nat.lt_succ_of_le hLbound⟩
    representative := fun j ↦ (code j).bits
  }
  have hcode (j : Fin (classifierDirectionCount F)) :
      (T.representativeCode j).toSet = B j := by
    change (PeriodicSetCode.ofBits (classifierPeriod F E)
      (classifierPeriod_pos F E) (code j).bits).toSet = B j
    exact encodePeriodicSet_toSet _ _ _ (hBperiod j)
  have hindicator : setIndicator A = ∑ i, setIndicator (D.part i) := by
    calc
      setIndicator A = setIndicator (⋃ i, D.part i) :=
        congrArg setIndicator D.union_parts.symm
      _ = ∑ i, setIndicator (D.part i) :=
        setIndicator_iUnion_eq_sum_finite D.part D.pairwiseDisjoint
  have hsumOriginal : setIndicator E.toSet =
      ∑ i, tileConv F (setIndicator (D.part i)) := by
    funext x
    have ht := D.tiles x
    have ht' : tileConv F (setIndicator A) x = setIndicator E.toSet x := by
      norm_num at ht ⊢
      exact ht
    rw [hindicator] at ht'
    rw [← ht']
    simp only [Finset.sum_apply, tileConv]
    rw [Finset.sum_comm]
  have hsumB : setIndicator E.toSet =
      ∑ j, tileConv F (setIndicator (B j)) := by
    funext x
    have horiginal := congrFun hsumOriginal x
    simp only [Finset.sum_apply] at horiginal ⊢
    rw [horiginal]
    let e := Fin.castOrderIso hnum.symm
    calc
      (∑ i, tileConv F (setIndicator (D.part i)) x) =
          ∑ j, tileConv F
            (setIndicator (D.part (Fin.cast hnum.symm j))) x := by
        symm
        apply Fintype.sum_equiv e.toEquiv
        intro j
        congr 2
      _ = ∑ j, tileConv F (setIndicator (B j)) x := by
        apply Finset.sum_congr rfl
        intro j _
        exact congrFun (hBconv j) x
  have hTmem : T ∈ representativeTuples F E := by
    apply (mem_representativeTuples_iff T).mpr
    refine ⟨?_, fun x ↦ ?_⟩
    · simpa only [RepresentativeTupleCode.weakMultiplierNat, T] using hLpos
    · calc
        ∑ j, tileConv F (setIndicator (T.representativeCode j).toSet) x =
            ∑ j, tileConv F (setIndicator (B j)) x := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hcode]
        _ = setIndicator E.toSet x := by
          simpa only [Finset.sum_apply] using (congrFun hsumB x).symm
  let S : LineSelection F E T := {
    chosen := fun j line ↦ slicePattern (classifierPrimitiveDirection F j) line
      (D.part (Fin.cast hnum.symm j))
    supported := by
      intro j line x hx
      exact (mem_slicePattern x).mp hx |>.2
    periodic := by
      intro j line
      let i : Fin D.numberOfParts := Fin.cast hnum.symm j
      let v := classifierPrimitiveDirection F j
      let p : Plane := ((classifierLinePeriod F E T j : ℕ) : ℤ) • v
      change Function.Periodic
        (setIndicator (slicePattern v line (D.part i))) p
      have hdirectionNe : classifierDirection F j ≠ 0 := by
        rw [← hdir j]
        exact D.direction_ne_zero i
      have hdecomp := primitive_decomposition hdirectionNe
      have hlinePeriod : classifierLinePeriod F E T j =
          E.period * L * vectorContent (classifierDirection F j) := by
        rfl
      have hpEq : p = ((E.period * L : ℕ) : ℤ) • D.direction i := by
        dsimp only [p, v, i]
        rw [hlinePeriod]
        calc
          (((E.period * L * vectorContent (classifierDirection F j) : ℕ) : ℤ) •
              classifierPrimitiveDirection F j) =
              ((E.period * L : ℕ) : ℤ) •
                ((vectorContent (classifierDirection F j) : ℤ) •
                  classifierPrimitiveDirection F j) := by
            push_cast
            module
          _ = ((E.period * L : ℕ) : ℤ) • classifierDirection F j := by
            exact congrArg (((E.period * L : ℕ) : ℤ) • ·) hdecomp.1
          _ = ((E.period * L : ℕ) : ℤ) • D.direction
              (Fin.cast hnum.symm j) := by rw [hdir j]
      have hpart : Function.Periodic (setIndicator (D.part i)) p := by
        rw [hpEq]
        exact D.periodic_part i
      have hpH : p ∈ directionSubgroup v := by
        exact AddSubgroup.mem_zmultiples_iff.mpr
          ⟨classifierLinePeriod F E T j, rfl⟩
      intro x
      apply (algorithm_indicator_eq_iff_membership _ _ _).mpr
      rw [mem_slicePattern, mem_slicePattern]
      have hpartMem : x + p ∈ D.part i ↔ x ∈ D.part i :=
        (algorithm_indicator_eq_iff_membership _ _ _).mp (hpart x)
      have hquot : QuotientAddGroup.mk' (directionSubgroup v) (x + p) =
          QuotientAddGroup.mk' (directionSubgroup v) x := by
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        simpa only [add_sub_cancel_left] using hpH
      rw [hpartMem, hquot]
    convolution_equivalent := by
      intro j line
      rw [hcode]
      exact hBslice j line
  }
  refine ⟨T, hTmem, S, ?_⟩
  symm
  ext x
  constructor
  · intro hx
    change x ∈ ⋃ j, ⋃ line,
      slicePattern (classifierPrimitiveDirection F j) line
        (D.part (Fin.cast hnum.symm j)) at hx
    obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨line, hxline⟩ := Set.mem_iUnion.mp hx
    have hxpart := (mem_slicePattern x).mp hxline |>.1
    rw [← D.union_parts]
    exact Set.mem_iUnion.mpr ⟨Fin.cast hnum.symm j, hxpart⟩
  · intro hx
    rw [← D.union_parts] at hx
    obtain ⟨i, hxpart⟩ := Set.mem_iUnion.mp hx
    let j : Fin (classifierDirectionCount F) := Fin.cast hnum i
    let line := QuotientAddGroup.mk'
      (directionSubgroup (classifierPrimitiveDirection F j)) x
    change x ∈ ⋃ j, ⋃ line,
      slicePattern (classifierPrimitiveDirection F j) line
        (D.part (Fin.cast hnum.symm j))
    apply Set.mem_iUnion.mpr
    refine ⟨j, Set.mem_iUnion.mpr ⟨line, ?_⟩⟩
    apply (mem_slicePattern x).mpr
    refine ⟨?_, rfl⟩
    have hcast : Fin.cast hnum.symm j = i := by
      apply Fin.ext
      rfl
    rw [hcast]
    exact hxpart

/-- A complement tiles a scalar-periodic target exactly when it is assembled from
one of the finitely enumerated directional representative tuples. -/
theorem tiling_iff_from_periodic_representatives
    {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hzero : 0 ∈ F) (hcard : 1 < F.card) :
    Tiles F A E.toSet ↔
      ∃ T ∈ representativeTuples F E, ProducedByTuple T A := by
  classical
  constructor
  · intro htiles
    obtain ⟨L, hLpos, hLbound, D, hnum, hdir⟩ :=
      directionalDecomposition_uniform_classifier hF hzero hcard
        E.toSet_scalarPeriodic htiles
    have hmcard : D.numberOfParts ≤ F.card - 1 := by
      rw [hnum]
      exact groupedDirectionCount_le hzero
    have hproduct : ∏ i : Fin D.numberOfParts, l1Norm (D.direction i) ≤
        l1Diameter F ^ (F.card - 1) :=
      directional_product_bound hzero hcard htiles D hnum hdir
    have hproductPos : 0 < ∏ i : Fin D.numberOfParts,
        l1Norm (D.direction i) := by
      apply Finset.prod_pos
      intro i _
      rw [Nat.pos_iff_ne_zero]
      exact fun hz ↦ D.direction_ne_zero i (l1Norm_eq_zero.mp hz)
    have hstructural : classifierWeakBound F *
        structuralCompletionPeriodBound F.card (l1Diameter F)
          D.numberOfParts
          (∏ i : Fin D.numberOfParts, l1Norm (D.direction i)) ≤
        classifierRepresentativeBound F := by
      simpa only [classifierWeakBound, classifierRepresentativeBound] using
        algorithm_weak_mul_structural_le_periodic hcard D.number_pos hmcard
          hproductPos hproduct
    by_cases hone : D.numberOfParts = 1
    · let i₀ : Fin D.numberOfParts := ⟨0, D.number_pos⟩
      obtain ⟨B₀, hB₀period, hB₀conv, hB₀slice⟩ :=
        one_component_improvement_with_slices D
          (Nat.mul_pos E.period_pos hLpos) hone
      have hfin (i : Fin D.numberOfParts) : i = i₀ := by
        apply Fin.ext
        have hi := i.isLt
        dsimp only [i₀]
        omega
      have hprodEq : (∏ i : Fin D.numberOfParts, l1Norm (D.direction i)) =
          l1Norm (D.direction i₀) := by
        apply Finset.prod_eq_single i₀
        · intro i _ hi
          exact (hi (hfin i)).elim
        · simp
      have honeBound : onePartCompletionMultiplierBound F.card (l1Diameter F)
          (l1Norm (D.direction i₀)) ≤
          structuralCompletionPeriodBound F.card (l1Diameter F)
            D.numberOfParts
            (∏ i : Fin D.numberOfParts, l1Norm (D.direction i)) := by
        simpa only [hone, hprodEq] using
          (algorithm_onePartBound_le_structural
            (directionNorm := l1Norm (D.direction i₀)) hcard)
      obtain ⟨C, hExact, hBound⟩ := improve_onePart D
        (Nat.mul_pos E.period_pos hLpos) hone
      have hKpos : 0 < onePartCompletionMultiplier D := by
        rw [← hExact]
        exact C.multiplier_pos
      have hKbound : onePartCompletionMultiplier D ≤
          onePartCompletionMultiplierBound F.card (l1Diameter F)
            (l1Norm (D.direction i₀)) := by
        rw [← hExact]
        exact hBound
      have hLKbound : L * onePartCompletionMultiplier D ≤
          classifierRepresentativeBound F := by
        calc
          L * onePartCompletionMultiplier D ≤ classifierWeakBound F *
              onePartCompletionMultiplierBound F.card (l1Diameter F)
                (l1Norm (D.direction i₀)) := Nat.mul_le_mul hLbound hKbound
          _ ≤ classifierWeakBound F *
              structuralCompletionPeriodBound F.card (l1Diameter F)
                D.numberOfParts
                (∏ i : Fin D.numberOfParts, l1Norm (D.direction i)) :=
            Nat.mul_le_mul_left _ honeBound
          _ ≤ classifierRepresentativeBound F := hstructural
      have hdvd := one_component_period_dvd_classifier D hLpos hKpos hLKbound
      let B : Fin (classifierDirectionCount F) → Set Plane := fun _ ↦ B₀
      apply forward_classifier_assembly hLpos hLbound D hnum hdir B
      · intro j
        apply setScalarPeriodic_of_dvd hdvd
        exact hB₀period
      · intro j
        have hj : Fin.cast hnum.symm j = i₀ := hfin _
        simpa only [B, hj] using hB₀conv
      · intro j line
        have hj : Fin.cast hnum.symm j = i₀ := hfin _
        have hv : completionPrimitiveDirection D i₀ =
            classifierPrimitiveDirection F j := by
          unfold completionPrimitiveDirection classifierPrimitiveDirection
          rw [← hj, hdir j]
        have hs := hB₀slice
        rw [hv] at hs
        simpa only [B, hj] using hs line
    · have hm : 2 ≤ D.numberOfParts :=
        (Nat.two_le_iff D.numberOfParts).2 ⟨D.number_pos.ne', hone⟩
      obtain ⟨C⟩ := improve_weaklyPeriodic_exact hF hcard D
        (Nat.mul_pos E.period_pos hLpos) hm
      have hKpos : 0 < completionMultiplier D := by
        rw [← C.completed_multiplier_exact]
        exact C.completed.multiplier_pos
      have hKbound : completionMultiplier D ≤
          structuralCompletionPeriodBound F.card (l1Diameter F)
            D.numberOfParts
            (∏ i : Fin D.numberOfParts, l1Norm (D.direction i)) := by
        rw [← C.completed_multiplier_exact]
        exact C.completedMultiplier_structural_bound hmcard
      have hLKbound : L * completionMultiplier D ≤
          classifierRepresentativeBound F := by
        calc
          L * completionMultiplier D ≤ classifierWeakBound F *
              structuralCompletionPeriodBound F.card (l1Diameter F)
                D.numberOfParts
                (∏ i : Fin D.numberOfParts, l1Norm (D.direction i)) :=
            Nat.mul_le_mul hLbound hKbound
          _ ≤ classifierRepresentativeBound F := hstructural
      have himprove (j : Fin (classifierDirectionCount F)) :=
        classifier_component_improvement D hLpos hm hnum hdir j
      let B (j : Fin (classifierDirectionCount F)) : Set Plane :=
        Classical.choose (himprove j)
      let spec (j : Fin (classifierDirectionCount F)) :=
        Classical.choose_spec (himprove j)
      apply forward_classifier_assembly hLpos hLbound D hnum hdir B
      · intro j
        apply setScalarPeriodic_of_dvd
          (completion_component_period_dvd_classifier D hLpos hKpos hLKbound
            (Fin.cast hnum.symm j))
        exact (spec j).1
      · intro j
        exact (spec j).2.1
      · intro j line
        exact (spec j).2.2 line
  · rintro ⟨T, hT, S, rfl⟩
    apply tiles_of_lineSelection S hF
    exact (Finset.mem_filter.mp hT).2

/- The two independently replaceable slices can be changed simultaneously;
their transverse support destroys every nonzero global period. -/
/-- Two distinct chameleon directions produce a tiling complement with no nonzero period. -/
theorem two_chameleons_construct_not_onePeriodic
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (T : RepresentativeTupleCode F E)
    (j₁ j₂ : Fin (classifierDirectionCount F))
    (hF : F.Nonempty) (hvalid : T ∈ representativeTuples F E)
    (hne : j₁ ≠ j₂)
    (h₁ : hasChameleonSlice F E T j₁ = true)
    (h₂ : hasChameleonSlice F E T j₂ = true) :
    ∃ A, Tiles F A E.toSet ∧ ¬ OnePeriodic A := by
  classical
  let v₁ := classifierPrimitiveDirection F j₁
  let v₂ := classifierPrimitiveDirection F j₂
  have hv₁ : v₁ ≠ 0 := classifierPrimitiveDirection_ne_zero F j₁
  have hv₂ : v₂ ≠ 0 := classifierPrimitiveDirection_ne_zero F j₂
  obtain ⟨y₁, K₁, hk₁, hne₁, hconv₁⟩ :=
    (hasChameleonSlice_eq_true_iff_core T j₁ hv₁).mp h₁
  obtain ⟨y₂, K₂, hk₂, hne₂, hconv₂⟩ :=
    (hasChameleonSlice_eq_true_iff_core T j₂ hv₂).mp h₂
  let R : Fin (classifierDirectionCount F) → Set Plane :=
    fun j ↦ (T.representativeCode j).toSet
  let B₁ := decodedLinePattern v₁ y₁ (classifierLinePeriod F E T j₁) hk₁ K₁
  let B₂ := decodedLinePattern v₂ y₂ (classifierLinePeriod F E T j₂) hk₂ K₂
  let C₁ := R j₁ ∩ addCoset (directionSubgroup v₁) y₁
  let C₂ := R j₂ ∩ addCoset (directionSubgroup v₂) y₂
  change B₁ ≠ C₁ at hne₁
  change B₂ ≠ C₂ at hne₂
  change convolutionEquivalent F B₁ C₁ at hconv₁
  change convolutionEquivalent F B₂ C₂ at hconv₂
  have hB₁support : B₁ ⊆ addCoset (directionSubgroup v₁) y₁ := by
    intro x hx
    obtain ⟨m, hm, -⟩ := (linePatternMemBool_eq_true_iff hk₁ K₁ hv₁).mp hx
    change x - y₁ ∈ directionSubgroup v₁
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨m, ?_⟩
    rw [hm]
    abel
  have hB₂support : B₂ ⊆ addCoset (directionSubgroup v₂) y₂ := by
    intro x hx
    obtain ⟨m, hm, -⟩ := (linePatternMemBool_eq_true_iff hk₂ K₂ hv₂).mp hx
    change x - y₂ ∈ directionSubgroup v₂
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨m, ?_⟩
    rw [hm]
    abel
  have hC₁ : C₁ ⊆ R j₁ := fun _ hx ↦ hx.1
  have hC₂ : C₂ ⊆ R j₂ := fun _ hx ↦ hx.1
  have hdisj₁ : Disjoint B₁ (R j₁ \ C₁) := by
    rw [Set.disjoint_left]
    intro x hxB hxR
    exact hxR.2 ⟨hxR.1, hB₁support hxB⟩
  have hdisj₂ : Disjoint B₂ (R j₂ \ C₂) := by
    rw [Set.disjoint_left]
    intro x hxB hxR
    exact hxR.2 ⟨hxR.1, hB₂support hxB⟩
  let A₁ := B₁ ∪ (R j₁ \ C₁)
  let A₂ := B₂ ∪ (R j₂ \ C₂)
  have hconvA₁ : convolutionEquivalent F A₁ (R j₁) :=
    convolutionEquivalent_replace F hC₁ hdisj₁ hconv₁
  have hconvA₂ : convolutionEquivalent F A₂ (R j₂) :=
    convolutionEquivalent_replace F hC₂ hdisj₂ hconv₂
  let part : Fin (classifierDirectionCount F) → Set Plane := fun j ↦
    if j = j₁ then A₁ else if j = j₂ then A₂ else R j
  have hpartConv (j : Fin (classifierDirectionCount F)) :
      convolutionEquivalent F (part j) (R j) := by
    by_cases hj₁ : j = j₁
    · subst j
      simpa only [part, if_pos rfl] using hconvA₁
    · by_cases hj₂ : j = j₂
      · subst j
        simpa [part, hne.symm] using hconvA₂
      · simp only [part, if_neg hj₁, if_neg hj₂]
        rfl
  have hvalid' := (mem_representativeTuples_iff T).mp hvalid |>.2
  have hsumR : setIndicator E.toSet =
      ∑ j, tileConv F (setIndicator (R j)) := by
    funext x
    simp only [Finset.sum_apply]
    exact (hvalid' x).symm
  have hsumPart : setIndicator E.toSet =
      ∑ j, tileConv F (setIndicator (part j)) := by
    rw [hsumR]
    apply Finset.sum_congr rfl
    intro j _
    exact (hpartConv j).symm
  have hpartDisjoint := pairwiseDisjoint_of_sum_convolution F part E.toSet hF hsumPart
  let A := ⋃ j, part j
  have htilesA : Tiles F A E.toSet := by
    exact tiles_iUnion_of_sum_convolution F part E.toSet hpartDisjoint hsumPart
  refine ⟨A, htilesA, ?_⟩
  have hRDisjoint := pairwiseDisjoint_of_sum_convolution F R E.toSet hF hsumR
  have hindA : setIndicator A = ∑ j, setIndicator (part j) :=
    setIndicator_iUnion_eq_sum_finite part hpartDisjoint
  let Rall := ⋃ j, R j
  have hindR : setIndicator Rall = ∑ j, setIndicator (R j) :=
    setIndicator_iUnion_eq_sum_finite R hRDisjoint
  let g₁ : Plane → ℤ := fun x ↦ setIndicator B₁ x - setIndicator C₁ x
  let g₂ : Plane → ℤ := fun x ↦ setIndicator B₂ x - setIndicator C₂ x
  let g : Plane → ℤ := fun x ↦ setIndicator A x - setIndicator Rall x
  have hR₁ : R j₁ = C₁ ∪ (R j₁ \ C₁) := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hx
      by_cases hxC : x ∈ C₁
      · exact Or.inl hxC
      · exact Or.inr ⟨hx, hxC⟩
    · rintro (hx | ⟨hx, -⟩)
      · exact hC₁ hx
      · exact hx
  have hR₂ : R j₂ = C₂ ∪ (R j₂ \ C₂) := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hx
      by_cases hxC : x ∈ C₂
      · exact Or.inl hxC
      · exact Or.inr ⟨hx, hxC⟩
    · rintro (hx | ⟨hx, -⟩)
      · exact hC₂ hx
      · exact hx
  have hCdisj₁ : Disjoint C₁ (R j₁ \ C₁) := by
    rw [Set.disjoint_left]
    exact fun _ hxC hxR ↦ hxR.2 hxC
  have hCdisj₂ : Disjoint C₂ (R j₂ \ C₂) := by
    rw [Set.disjoint_left]
    exact fun _ hxC hxR ↦ hxR.2 hxC
  have hindA₁ := setIndicator_union_eq_add_of_disjoint hdisj₁
  have hindA₂ := setIndicator_union_eq_add_of_disjoint hdisj₂
  have hindR₁ : setIndicator (R j₁) =
      setIndicator C₁ + setIndicator (R j₁ \ C₁) := by
    calc
      setIndicator (R j₁) = setIndicator (C₁ ∪ (R j₁ \ C₁)) :=
        congrArg setIndicator hR₁
      _ = _ := setIndicator_union_eq_add_of_disjoint hCdisj₁
  have hindR₂ : setIndicator (R j₂) =
      setIndicator C₂ + setIndicator (R j₂ \ C₂) := by
    calc
      setIndicator (R j₂) = setIndicator (C₂ ∪ (R j₂ \ C₂)) :=
        congrArg setIndicator hR₂
      _ = _ := setIndicator_union_eq_add_of_disjoint hCdisj₂
  have hdiff₁ (x : Plane) : setIndicator A₁ x - setIndicator (R j₁) x = g₁ x := by
    dsimp only [A₁, g₁]
    rw [congrFun hindA₁ x, congrFun hindR₁ x]
    simp only [Pi.add_apply]
    ring
  have hdiff₂ (x : Plane) : setIndicator A₂ x - setIndicator (R j₂) x = g₂ x := by
    dsimp only [A₂, g₂]
    rw [congrFun hindA₂ x, congrFun hindR₂ x]
    simp only [Pi.add_apply]
    ring
  have hpartDiff (j : Fin (classifierDirectionCount F)) (x : Plane) :
      setIndicator (part j) x - setIndicator (R j) x =
        if j = j₁ then g₁ x else if j = j₂ then g₂ x else 0 := by
    by_cases hj₁ : j = j₁
    · subst j
      simpa [part] using hdiff₁ x
    · by_cases hj₂ : j = j₂
      · subst j
        simpa [part, hne.symm] using hdiff₂ x
      · simp only [part, if_neg hj₁, if_neg hj₂, sub_self]
  have hgeq (x : Plane) : g x = g₁ x + g₂ x := by
    dsimp only [g]
    rw [congrFun hindA x, congrFun hindR x]
    simp only [Finset.sum_apply]
    rw [← Finset.sum_sub_distrib]
    calc
      ∑ j, (setIndicator (part j) x - setIndicator (R j) x) =
          ∑ j, (if j = j₁ then g₁ x else if j = j₂ then g₂ x else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hpartDiff j x
      _ = g₁ x + g₂ x := by
        calc
          ∑ j, (if j = j₁ then g₁ x else if j = j₂ then g₂ x else 0) =
              ∑ j, ((if j = j₁ then g₁ x else 0) +
                (if j = j₂ then g₂ x else 0)) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj₁ : j = j₁ <;> by_cases hj₂ : j = j₂ <;>
              simp [hj₁, hj₂, hne, hne.symm]
          _ = (∑ j, if j = j₁ then g₁ x else 0) +
                ∑ j, if j = j₂ then g₂ x else 0 :=
            Finset.sum_add_distrib
          _ = g₁ x + g₂ x := by
            simp only [Finset.sum_ite_eq', Finset.mem_univ, if_pos]
  have hg₁support : ∀ z, g₁ z ≠ 0 →
      z ∈ addCoset (directionSubgroup v₁) y₁ := by
    intro z hz
    by_contra hzline
    have hzB : z ∉ B₁ := fun h ↦ hzline (hB₁support h)
    have hzC : z ∉ C₁ := fun h ↦ hzline h.2
    exact hz (by simp [g₁, setIndicator, hzB, hzC])
  have hg₂support : ∀ z, g₂ z ≠ 0 →
      z ∈ addCoset (directionSubgroup v₂) y₂ := by
    intro z hz
    by_contra hzline
    have hzB : z ∉ B₂ := fun h ↦ hzline (hB₂support h)
    have hzC : z ∉ C₂ := fun h ↦ hzline h.2
    exact hz (by simp [g₂, setIndicator, hzB, hzC])
  have hg₁nonzero : ∃ x, g₁ x ≠ 0 := by
    have hex : ∃ x, ¬ (x ∈ B₁ ↔ x ∈ C₁) := by
      by_contra hnone
      push Not at hnone
      exact hne₁ (Set.ext hnone)
    obtain ⟨x, hx⟩ := hex
    refine ⟨x, ?_⟩
    by_cases hxB : x ∈ B₁ <;> by_cases hxC : x ∈ C₁ <;>
      simp [g₁, setIndicator, hxB, hxC] at hx ⊢
  have hg₂nonzero : ∃ x, g₂ x ≠ 0 := by
    have hex : ∃ x, ¬ (x ∈ B₂ ↔ x ∈ C₂) := by
      by_contra hnone
      push Not at hnone
      exact hne₂ (Set.ext hnone)
    obtain ⟨x, hx⟩ := hex
    refine ⟨x, ?_⟩
    by_cases hxB : x ∈ B₂ <;> by_cases hxC : x ∈ C₂ <;>
      simp [g₂, setIndicator, hxB, hxC] at hx ⊢
  let Q₁ := Nat.lcm (classifierLinePeriod F E T j₁) (classifierPeriod F E)
  let Q₂ := Nat.lcm (classifierLinePeriod F E T j₂) (classifierPeriod F E)
  have hQ₁ : 0 < Q₁ := Nat.lcm_pos hk₁ (classifierPeriod_pos F E)
  have hQ₂ : 0 < Q₂ := Nat.lcm_pos hk₂ (classifierPeriod_pos F E)
  have hB₁Q : Function.Periodic (setIndicator B₁) ((Q₁ : ℤ) • v₁) := by
    obtain ⟨c, hc⟩ := Nat.dvd_lcm_left
      (classifierLinePeriod F E T j₁) (classifierPeriod F E)
    have hp := (decodedLinePattern_periodic (y := y₁) hk₁ K₁ hv₁).nsmul c
    rw [show (Q₁ : ℤ) • v₁ =
        c • ((classifierLinePeriod F E T j₁ : ℤ) • v₁) by
      dsimp only [Q₁]
      rw [hc]
      push_cast
      module]
    exact hp
  have hC₁Q : Function.Periodic (setIndicator C₁) ((Q₁ : ℤ) • v₁) := by
    obtain ⟨c, hc⟩ := Nat.dvd_lcm_right
      (classifierLinePeriod F E T j₁) (classifierPeriod F E)
    have hp := (referenceSlice_periodic T j₁ y₁).nsmul c
    rw [show (Q₁ : ℤ) • v₁ =
        c • ((classifierPeriod F E : ℤ) • v₁) by
      dsimp only [Q₁]
      rw [hc]
      push_cast
      module]
    exact hp
  have hB₂Q : Function.Periodic (setIndicator B₂) ((Q₂ : ℤ) • v₂) := by
    obtain ⟨c, hc⟩ := Nat.dvd_lcm_left
      (classifierLinePeriod F E T j₂) (classifierPeriod F E)
    have hp := (decodedLinePattern_periodic (y := y₂) hk₂ K₂ hv₂).nsmul c
    rw [show (Q₂ : ℤ) • v₂ =
        c • ((classifierLinePeriod F E T j₂ : ℤ) • v₂) by
      dsimp only [Q₂]
      rw [hc]
      push_cast
      module]
    exact hp
  have hC₂Q : Function.Periodic (setIndicator C₂) ((Q₂ : ℤ) • v₂) := by
    obtain ⟨c, hc⟩ := Nat.dvd_lcm_right
      (classifierLinePeriod F E T j₂) (classifierPeriod F E)
    have hp := (referenceSlice_periodic T j₂ y₂).nsmul c
    rw [show (Q₂ : ℤ) • v₂ =
        c • ((classifierPeriod F E : ℤ) • v₂) by
      dsimp only [Q₂]
      rw [hc]
      push_cast
      module]
    exact hp
  have hg₁Q : Function.Periodic g₁ ((Q₁ : ℤ) • v₁) := by
    intro x
    dsimp only [g₁]
    rw [hB₁Q x, hC₁Q x]
  have hg₂Q : Function.Periodic g₂ ((Q₂ : ℤ) • v₂) := by
    intro x
    dsimp only [g₂]
    rw [hB₂Q x, hC₂Q x]
  have hincomm := classifierPrimitiveDirection_pairwise F j₁ j₂ hne
  have hw₁₂ : wedge v₁ v₂ ≠ 0 := fun hw ↦
    hincomm ((commensurable_iff_wedge_eq_zero hv₁ hv₂).2 hw)
  have hw₂₁ : wedge v₂ v₁ ≠ 0 := by
    intro hw
    apply hw₁₂
    rw [wedge_swap]
    rw [hw]
    simp
  obtain ⟨x₁, hx₁g, hx₁line, hx₁off⟩ := exists_nonzero_off_transverse_line
    (by exact_mod_cast hQ₁.ne') hw₂₁ hg₁Q hg₁support hg₁nonzero.choose_spec
  obtain ⟨x₂, hx₂g, hx₂line, hx₂off⟩ := exists_nonzero_off_transverse_line
    (by exact_mod_cast hQ₂.ne') hw₁₂ hg₂Q hg₂support hg₂nonzero.choose_spec
  rintro ⟨u, hu, hAperiod⟩
  let q := classifierPeriod F E
  let t : Plane := (q : ℤ) • u
  have ht : t ≠ 0 := smul_ne_zero (by exact_mod_cast (classifierPeriod_pos F E).ne') hu
  have hAindicator : Function.Periodic (setIndicator A) t :=
    by
      have hp := (setIndicator_periodic_of_membership hAperiod).nsmul q
      have htq : t = q • u := by
        ext i
        simp [t]
      rw [htq]
      exact hp
  have hRmembership : ∀ x, x + t ∈ Rall ↔ x ∈ Rall := by
    intro x
    constructor
    · intro hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      exact ((T.representativeCode j).toSet_scalarPeriodic x u).mp hxj
    · intro hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      exact ((T.representativeCode j).toSet_scalarPeriodic x u).mpr hxj
  have hRindicator : Function.Periodic (setIndicator Rall) t :=
    setIndicator_periodic_of_membership hRmembership
  have hgperiod : Function.Periodic g t := by
    intro x
    dsimp only [g]
    rw [hAindicator x, hRindicator x]
  have hgsupport : ∀ z, g z ≠ 0 →
      z ∈ addCoset (directionSubgroup v₁) y₁ ∨
      z ∈ addCoset (directionSubgroup v₂) y₂ := by
    intro z hgz
    rw [hgeq z] at hgz
    by_cases hz₁ : g₁ z = 0
    · right
      apply hg₂support
      intro hz₂
      exact hgz (by rw [hz₁, hz₂]; simp)
    · exact Or.inl (hg₁support z hz₁)
  have hx₁g₂ : g₂ x₁ = 0 := by
    by_contra hx
    exact hx₁off (hg₂support x₁ hx)
  have hx₁g' : g x₁ ≠ 0 := by
    rw [hgeq x₁, hx₁g₂, add_zero]
    exact hx₁g
  have hx₂g₁ : g₁ x₂ = 0 := by
    by_contra hx
    exact hx₂off (hg₁support x₂ hx)
  have hx₂g' : g x₂ ≠ 0 := by
    rw [hgeq x₂, hx₂g₁, zero_add]
    exact hx₂g
  have hwt₁ := direction_wedge_period_eq_zero_of_supported_on_two_lines
    (v₁ := v₁) (v₂ := v₂) (y₁ := y₁) (y₂ := y₂)
    hgperiod hgsupport hx₁g' hx₁line hx₁off
  have hwt₂ := direction_wedge_period_eq_zero_of_supported_on_two_lines
    (v₁ := v₂) (v₂ := v₁) (y₁ := y₂) (y₂ := y₁)
    hgperiod (fun z hz ↦ (hgsupport z hz).elim Or.inr Or.inl)
    hx₂g' hx₂line hx₂off
  exact ht (eq_zero_of_two_incommensurable_wedges hv₁ hv₂ hincomm hwt₁ hwt₂)

private theorem lineSelection_detects_chameleon
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (T : RepresentativeTupleCode F E) (S : LineSelection F E T)
    (hvalid : T ∈ representativeTuples F E)
    (j : Fin (classifierDirectionCount F))
    (line : Plane ⧸ directionSubgroup (classifierPrimitiveDirection F j))
    (hne : S.chosen j line ≠
      slicePattern (classifierPrimitiveDirection F j) line
        (T.representativeCode j).toSet) :
    hasChameleonSlice F E T j = true := by
  classical
  let v := classifierPrimitiveDirection F j
  let H := directionSubgroup v
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective H line
  have hcoset : quotientCoset H (QuotientAddGroup.mk' H y) = addCoset H y := by
    ext x
    exact QuotientAddGroup.eq_iff_sub_mem
  have hweakPos : 0 < T.weakMultiplierNat :=
    (mem_representativeTuples_iff T).mp hvalid |>.1
  have hk : 0 < classifierLinePeriod F E T j := by
    unfold classifierLinePeriod
    exact Nat.mul_pos (Nat.mul_pos E.period_pos hweakPos)
      (vectorContent_pos (classifierDirection_ne_zero F j))
  let P := linePatternOfSet v y (classifierLinePeriod F E T j)
    (S.chosen j (QuotientAddGroup.mk' H y))
  have hsupport : S.chosen j (QuotientAddGroup.mk' H y) ⊆ addCoset H y := by
    simpa only [H, v, hcoset] using S.supported j (QuotientAddGroup.mk' H y)
  have hdecoded : decodedLinePattern v y (classifierLinePeriod F E T j) hk P =
      S.chosen j (QuotientAddGroup.mk' H y) := by
    exact decodedLinePattern_linePatternOfSet_eq hk
      (classifierPrimitiveDirection_ne_zero F j) _ hsupport
      (S.periodic j (QuotientAddGroup.mk' H y))
  apply (hasChameleonSlice_eq_true_iff_core T j
    (classifierPrimitiveDirection_ne_zero F j)).mpr
  refine ⟨y, P, hk, ?_, ?_⟩
  · intro heq
    apply hne
    have hchosen := hdecoded.symm.trans heq
    simpa only [v, H, slicePattern, hcoset] using hchosen
  · rw [hdecoded]
    simpa only [v, H, hcoset] using
      S.convolution_equivalent j (QuotientAddGroup.mk' H y)

private theorem empty_onePeriodic_algorithm : OnePeriodic (∅ : Set Plane) := by
  exact ⟨1, one_ne_zero, by simp⟩

private theorem atMostOne_from_slice_detection
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (T : RepresentativeTupleCode F E)
    (hvalid : T ∈ representativeTuples F E)
    (hatMostOne : ∀ j₁ j₂ : Fin (classifierDirectionCount F),
      hasChameleonSlice F E T j₁ = true →
      hasChameleonSlice F E T j₂ = true → j₁ = j₂)
    (hdetect : ∀ (S : LineSelection F E T)
      (j : Fin (classifierDirectionCount F))
      (line : Plane ⧸ directionSubgroup (classifierPrimitiveDirection F j)),
      S.chosen j line ≠
          slicePattern (classifierPrimitiveDirection F j) line
            (T.representativeCode j).toSet →
        hasChameleonSlice F E T j = true) :
    ∀ A, ProducedByTuple T A → OnePeriodic A := by
  classical
  intro A hproduced
  obtain ⟨S, rfl⟩ := hproduced
  by_cases hn : classifierDirectionCount F = 0
  · have hempty : assembleLineSelection S = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      rw [assembleLineSelection] at hx
      obtain ⟨j, _hxj⟩ := Set.mem_iUnion.mp hx
      exact Fin.elim0 (Fin.cast hn j)
    rw [hempty]
    exact empty_onePeriodic_algorithm
  · have hnpos : 0 < classifierDirectionCount F := Nat.pos_of_ne_zero hn
    have hcenter : ∃ j₀ : Fin (classifierDirectionCount F),
        ∀ j, hasChameleonSlice F E T j = true → j = j₀ := by
      by_cases hex : ∃ j : Fin (classifierDirectionCount F),
          hasChameleonSlice F E T j = true
      · obtain ⟨j₀, hj₀⟩ := hex
        exact ⟨j₀, fun j hj ↦ hatMostOne j j₀ hj hj₀⟩
      · let j₀ : Fin (classifierDirectionCount F) := ⟨0, hnpos⟩
        exact ⟨j₀, fun j hj ↦ (hex ⟨j, hj⟩).elim⟩
    obtain ⟨j₀, hcenter⟩ := hcenter
    let component (j : Fin (classifierDirectionCount F)) : Set Plane :=
      ⋃ line, S.chosen j line
    have hinactive (j : Fin (classifierDirectionCount F)) (hne : j ≠ j₀) :
        component j = (T.representativeCode j).toSet := by
      have hslice (line : Plane ⧸
          directionSubgroup (classifierPrimitiveDirection F j)) :
          S.chosen j line =
            slicePattern (classifierPrimitiveDirection F j) line
              (T.representativeCode j).toSet := by
        by_contra hneq
        exact hne (hcenter j (hdetect S j line hneq))
      ext x
      constructor
      · intro hx
        obtain ⟨line, hxline⟩ := Set.mem_iUnion.mp hx
        rw [hslice line] at hxline
        exact (mem_slicePattern x).mp hxline |>.1
      · intro hx
        let line := QuotientAddGroup.mk'
          (directionSubgroup (classifierPrimitiveDirection F j)) x
        apply Set.mem_iUnion.mpr
        refine ⟨line, ?_⟩
        rw [hslice line]
        exact (mem_slicePattern x).mpr ⟨hx, rfl⟩
    have hweakPos : 0 < T.weakMultiplierNat :=
      (mem_representativeTuples_iff T).mp hvalid |>.1
    have hk : 0 < classifierLinePeriod F E T j₀ := by
      unfold classifierLinePeriod
      exact Nat.mul_pos (Nat.mul_pos E.period_pos hweakPos)
        (vectorContent_pos (classifierDirection_ne_zero F j₀))
    let v := classifierPrimitiveDirection F j₀
    let k := classifierLinePeriod F E T j₀
    let q := classifierPeriod F E
    let p : Plane := (k : ℤ) • v
    let t : Plane := ((q * k : ℕ) : ℤ) • v
    have htEq : t = (q : ℤ) • p := by
      dsimp only [t, p]
      push_cast
      module
    have htne : t ≠ 0 := by
      apply smul_ne_zero
      · exact_mod_cast (Nat.mul_pos (classifierPeriod_pos F E) hk).ne'
      · exact classifierPrimitiveDirection_ne_zero F j₀
    have hactiveP : Function.Periodic (setIndicator (component j₀)) p := by
      intro x
      apply (algorithm_indicator_eq_iff_membership _ _ _).mpr
      constructor
      · intro hx
        obtain ⟨line, hxline⟩ := Set.mem_iUnion.mp hx
        apply Set.mem_iUnion.mpr
        refine ⟨line, ?_⟩
        exact (algorithm_indicator_eq_iff_membership _ _ _).mp
          (S.periodic j₀ line x) |>.mp hxline
      · intro hx
        obtain ⟨line, hxline⟩ := Set.mem_iUnion.mp hx
        apply Set.mem_iUnion.mpr
        refine ⟨line, ?_⟩
        exact (algorithm_indicator_eq_iff_membership _ _ _).mp
          (S.periodic j₀ line x) |>.mpr hxline
    have hcomponentT (j : Fin (classifierDirectionCount F)) :
        Function.Periodic (setIndicator (component j)) t := by
      by_cases hjeq : j = j₀
      · subst j
        rw [htEq]
        exact hactiveP.zsmul q
      · rw [hinactive j hjeq]
        intro x
        have hscalar := (T.representativeCode j).toSet_scalarPeriodic
        change SetScalarPeriodic q (T.representativeCode j).toSet at hscalar
        have hp := hscalar x ((k : ℤ) • v)
        have hshift : ((q : ℤ) : ℤ) • ((k : ℤ) • v) = t := by
          dsimp only [q]
          rw [← htEq]
        rw [hshift] at hp
        apply (algorithm_indicator_eq_iff_membership _ _ _).mpr
        exact hp
    refine ⟨t, htne, fun x ↦ ?_⟩
    have hassemble : assembleLineSelection S = ⋃ j, component j := by
      rfl
    rw [hassemble]
    constructor
    · intro hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨j,
        ((algorithm_indicator_eq_iff_membership _ _ _).mp (hcomponentT j x)).mp hxj⟩
    · intro hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨j,
        ((algorithm_indicator_eq_iff_membership _ _ _).mp (hcomponentT j x)).mpr hxj⟩

/-- If at most one directional slice is replaceable, every complement assembled
from the tuple has a common nonzero period. -/
theorem at_most_one_chameleon_all_onePeriodic
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (T : RepresentativeTupleCode F E)
    (_hF : F.Nonempty) (hvalid : T ∈ representativeTuples F E)
    (hatMostOne : ∀ j₁ j₂ : Fin (classifierDirectionCount F),
      hasChameleonSlice F E T j₁ = true →
      hasChameleonSlice F E T j₂ = true → j₁ = j₂) :
    ∀ A, ProducedByTuple T A → OnePeriodic A := by
  apply atMostOne_from_slice_detection T hvalid hatMostOne
  intro S j line hne
  exact lineSelection_detects_chameleon T S hvalid j line hne

private theorem normalized_nonOnePeriodicDecision_iff
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hzero : 0 ∈ F) (hcard : 1 < F.card) :
    nonOnePeriodicTilingDecisionNormalized F E = true ↔
      ∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A := by
  classical
  unfold nonOnePeriodicTilingDecisionNormalized
  rw [finsetAnyBool_eq_true_iff]
  constructor
  · rintro ⟨T, hT, hcount⟩
    rw [decide_eq_true_eq] at hcount
    obtain ⟨j₁, hj₁, j₂, hj₂, hne⟩ :=
      Finset.one_lt_card.mp (by omega : 1 <
        (Finset.univ.filter fun j ↦ hasChameleonSlice F E T j = true).card)
    exact two_chameleons_construct_not_onePeriodic T j₁ j₂ hF hT hne
      (Finset.mem_filter.mp hj₁).2 (Finset.mem_filter.mp hj₂).2
  · rintro ⟨A, htile, hnot⟩
    obtain ⟨T, hT, hproduced⟩ :=
      (tiling_iff_from_periodic_representatives hF hzero hcard).mp htile
    refine ⟨T, hT, ?_⟩
    rw [decide_eq_true_eq]
    by_contra htwo
    have hle :
        (Finset.univ.filter fun j ↦
          hasChameleonSlice F E T j = true).card ≤ 1 := by
      omega
    have hatMostOne : ∀ j₁ j₂ : Fin (classifierDirectionCount F),
        hasChameleonSlice F E T j₁ = true →
        hasChameleonSlice F E T j₂ = true → j₁ = j₂ := by
      intro j₁ j₂ h₁ h₂
      apply (Finset.card_le_one.mp hle) j₁
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ j₁, h₁⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ j₂, h₂⟩
    exact hnot
      (at_most_one_chameleon_all_onePeriodic T hF hT hatMostOne A hproduced)

private theorem translatedTarget_onePeriodic
    (E : PeriodicSetCode 2) (a : Plane) :
    OnePeriodic {x | x + a ∈ E.toSet} := by
  let z : Plane := fun _ ↦ 1
  let h : Plane := (E.period : ℤ) • z
  refine ⟨h, ?_, ?_⟩
  · intro hzero
    have hcomponent := congrFun hzero (0 : Fin 2)
    have hperiodZero : (E.period : ℤ) = 0 := by
      simpa only [h, z, Pi.smul_apply, smul_eq_mul, mul_one,
        Pi.zero_apply] using hcomponent
    exact E.period_pos.ne' (Int.ofNat_eq_zero.mp hperiodZero)
  · intro x
    have hp := E.toSet_scalarPeriodic (x + a) z
    change x + h + a ∈ E.toSet ↔ x + a ∈ E.toSet
    rw [show x + h + a = (x + a) + (E.period : ℤ) • z by
      dsimp only [h]
      abel]
    exact hp

/-- The executable scalar-periodic classifier returns `true` exactly when the
given tile admits a tiling complement with no nonzero global period. -/
theorem nonOnePeriodicTilingDecision_eq_true_iff
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hexists : ∃ A, Tiles F A E.toSet) :
    nonOnePeriodicTilingDecision F E = true ↔
      ∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A := by
  have _hexists := hexists
  rw [nonOnePeriodicTilingDecision]
  have hFne : F ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hF
  rw [if_neg hFne]
  by_cases hcard : F.card = 1
  · rw [if_pos hcard]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨A, htile, hnot⟩
    obtain ⟨a, _ha, hA⟩ := singleton_tile_complement_eq_target hcard htile
    exact hnot (hA ▸ translatedTarget_onePeriodic E a)
  · rw [if_neg hcard]
    by_cases hE : E.isEmptyBool = true
    · rw [if_pos hE]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨A, htile, hnot⟩
      have hA : A = ∅ := empty_target_complement_empty hF
        ((PeriodicSetCode.isEmptyBool_eq_true_iff E).mp hE) htile
      exact hnot (hA ▸ empty_onePeriodic_algorithm)
    · rw [if_neg hE]
      have hcardgt : 1 < F.card := by
        have hpos : 0 < F.card := Finset.card_pos.mpr hF
        omega
      have hFn : (normalizedTile F).Nonempty :=
        ⟨0, zero_mem_normalizedTile hF⟩
      have hFncard : 1 < (normalizedTile F).card := by
        simpa only [card_normalizedTile] using hcardgt
      have hnormalized := normalized_nonOnePeriodicDecision_iff
        (E := normalizedTargetCode F E) hFn
          (zero_mem_normalizedTile hF) hFncard
      constructor
      · intro h
        obtain ⟨A, htile, hnot⟩ := hnormalized.mp h
        exact ⟨A, (tiles_normalized_iff F E A).mp htile, hnot⟩
      · rintro ⟨A, htile, hnot⟩
        exact hnormalized.mpr
          ⟨A, (tiles_normalized_iff F E A).mpr htile, hnot⟩

/-- The Boolean classifier supplies a decidable instance for existence of a
non-one-periodic complement whenever the tiling problem is inhabited. -/
def non_one_periodic_tiling_decidable
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hexists : ∃ A, Tiles F A E.toSet) :
    Decidable (∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A) :=
  decidable_of_iff
    (nonOnePeriodicTilingDecision F E = true)
    (nonOnePeriodicTilingDecision_eq_true_iff hF hexists)

/-- The lattice-input wrapper has the same correctness specification as the
scalar-periodic classifier after converting its target code. -/
theorem nonOnePeriodicTilingDecisionLatticeInput_eq_true_iff
    {F : Finset Plane} {E : LatticePeriodicSetCode}
    (hF : F.Nonempty) (hexists : ∃ A, Tiles F A E.toSet) :
    nonOnePeriodicTilingDecisionLatticeInput F E = true ↔
      ∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A := by
  unfold nonOnePeriodicTilingDecisionLatticeInput
  have hexists' : ∃ A, Tiles F A E.toScalarCode.toSet := by
    simpa only [E.toScalarCode_toSet] using hexists
  simpa only [E.toScalarCode_toSet] using
    (nonOnePeriodicTilingDecision_eq_true_iff hF hexists')

end TranslationalTilings
