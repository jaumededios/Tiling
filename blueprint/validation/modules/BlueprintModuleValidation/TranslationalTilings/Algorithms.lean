import Mathlib.Data.Fintype.Pi
import TranslationalTilings.PeriodicCompletion

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 fb2e088b3a24017c4e393e4c2314e4df6648ea775ad41e238421b0ff2f0e43ea  blueprint/08-algorithms.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/08-algorithms.md:25; TranslationalTilings.BoxResidue -/
namespace TranslationalTilings
abbrev BoxResidue (d q : ℕ) := Fin d → Fin q
end TranslationalTilings

/- blueprint/08-algorithms.md:27; TranslationalTilings.boxPoint -/
namespace TranslationalTilings
def boxPoint (x : BoxResidue d q) : Lattice d :=
  fun i ↦ (x i : ℕ)
end TranslationalTilings

/- blueprint/08-algorithms.md:30; TranslationalTilings.PeriodicSetCode -/
namespace TranslationalTilings
structure PeriodicSetCode (d : ℕ) where
  period : ℕ
  period_pos : 0 < period
  bits : BoxResidue d period → Bool
deriving DecidableEq
end TranslationalTilings

/- blueprint/08-algorithms.md:36; TranslationalTilings.PeriodicSetCode.memBool -/
namespace TranslationalTilings
def PeriodicSetCode.memBool
    (C : PeriodicSetCode d) (x : Lattice d) : Bool :=
  C.bits fun i ↦ ⟨(x i).natMod C.period,
    Int.natMod_lt C.period_pos.ne'⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:41; TranslationalTilings.PeriodicSetCode.toSet -/
namespace TranslationalTilings
def PeriodicSetCode.toSet (C : PeriodicSetCode d) : Set (Lattice d) :=
  {x | C.memBool x}
end TranslationalTilings

/- blueprint/08-algorithms.md:44; TranslationalTilings.PeriodicSetCode.ofBits -/
namespace TranslationalTilings
def PeriodicSetCode.ofBits (q : ℕ) (hq : 0 < q)
    (bits : BoxResidue d q → Bool) : PeriodicSetCode d :=
  ⟨q, hq, bits⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:48; TranslationalTilings.PeriodicSetCode.univ -/
namespace TranslationalTilings
def PeriodicSetCode.univ (d q : ℕ) (hq : 0 < q) : PeriodicSetCode d :=
  PeriodicSetCode.ofBits q hq fun _ ↦ true
end TranslationalTilings

/- blueprint/08-algorithms.md:51; TranslationalTilings.encodePeriodicSet -/
namespace TranslationalTilings
noncomputable def encodePeriodicSet (q : ℕ) (hq : 0 < q)
    (A : Set (Lattice d)) : PeriodicSetCode d := by
  classical
  exact PeriodicSetCode.ofBits q hq fun r ↦ decide (boxPoint r ∈ A)
end TranslationalTilings

/- blueprint/08-algorithms.md:56; TranslationalTilings.PeriodicSetCode.pullbackTranslate -/
namespace TranslationalTilings
def PeriodicSetCode.pullbackTranslate
    (C : PeriodicSetCode d) (a : Lattice d) : PeriodicSetCode d :=
  PeriodicSetCode.ofBits C.period C.period_pos fun r ↦
    C.memBool (boxPoint r + a)
end TranslationalTilings

/- blueprint/08-algorithms.md:69; TranslationalTilings.PeriodicSetCode.memBool_eq_true_iff -/
namespace TranslationalTilings
axiom PeriodicSetCode.memBool_eq_true_iff (C : PeriodicSetCode d) (x) :
  C.memBool x = true ↔ x ∈ C.toSet
end TranslationalTilings

/- blueprint/08-algorithms.md:72; TranslationalTilings.PeriodicSetCode.toSet_scalarPeriodic -/
namespace TranslationalTilings
axiom PeriodicSetCode.toSet_scalarPeriodic (C : PeriodicSetCode d) :
  SetScalarPeriodic C.period C.toSet
end TranslationalTilings

/- blueprint/08-algorithms.md:75; TranslationalTilings.encodePeriodicSet_toSet -/
namespace TranslationalTilings
axiom encodePeriodicSet_toSet
    (q : ℕ) (hq : 0 < q) (A : Set (Lattice d))
    (hA : SetScalarPeriodic q A) :
  (encodePeriodicSet q hq A).toSet = A
end TranslationalTilings

/- blueprint/08-algorithms.md:80; TranslationalTilings.PeriodicSetCode.pullbackTranslate_toSet -/
namespace TranslationalTilings
axiom PeriodicSetCode.pullbackTranslate_toSet (C : PeriodicSetCode d)
    (a : Lattice d) :
  (C.pullbackTranslate a).toSet = {x | x + a ∈ C.toSet}
end TranslationalTilings

/- blueprint/08-algorithms.md:102; TranslationalTilings.LatticePeriodicSetCode -/
namespace TranslationalTilings
structure LatticePeriodicSetCode where
  horizontalPeriod : ℕ
  horizontal_pos : 0 < horizontalPeriod
  shear : ℤ
  shear_nonneg : 0 ≤ shear
  shear_lt_horizontal : shear < horizontalPeriod
  verticalPeriod : ℕ
  vertical_pos : 0 < verticalPeriod
  bits : Fin horizontalPeriod → Fin verticalPeriod → Bool
deriving DecidableEq
end TranslationalTilings

/- blueprint/08-algorithms.md:113; TranslationalTilings.LatticePeriodicSetCode.horizontalGenerator -/
namespace TranslationalTilings
def LatticePeriodicSetCode.horizontalGenerator
    (C : LatticePeriodicSetCode) : Plane :=
  ![(C.horizontalPeriod : ℤ), 0]
end TranslationalTilings

/- blueprint/08-algorithms.md:117; TranslationalTilings.LatticePeriodicSetCode.verticalGenerator -/
namespace TranslationalTilings
def LatticePeriodicSetCode.verticalGenerator
    (C : LatticePeriodicSetCode) : Plane :=
  ![C.shear, (C.verticalPeriod : ℤ)]
end TranslationalTilings

/- blueprint/08-algorithms.md:121; TranslationalTilings.LatticePeriodicSetCode.periodLattice -/
namespace TranslationalTilings
def LatticePeriodicSetCode.periodLattice
    (C : LatticePeriodicSetCode) : AddSubgroup Plane :=
  AddSubgroup.closure
    ({C.horizontalGenerator, C.verticalGenerator} : Set Plane)
end TranslationalTilings

/- blueprint/08-algorithms.md:126; TranslationalTilings.LatticePeriodicSetCode.memBool -/
namespace TranslationalTilings
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
def LatticePeriodicSetCode.toSet (C : LatticePeriodicSetCode) : Set Plane :=
  {x | C.memBool x}
end TranslationalTilings

/- blueprint/08-algorithms.md:138; TranslationalTilings.LatticePeriodicSetCode.scalarPeriod -/
namespace TranslationalTilings
def LatticePeriodicSetCode.scalarPeriod
    (C : LatticePeriodicSetCode) : ℕ :=
  C.horizontalPeriod * C.verticalPeriod
end TranslationalTilings

/- blueprint/08-algorithms.md:142; TranslationalTilings.LatticePeriodicSetCode.toScalarCode -/
namespace TranslationalTilings
def LatticePeriodicSetCode.toScalarCode
    (C : LatticePeriodicSetCode) : PeriodicSetCode 2 :=
  PeriodicSetCode.ofBits C.scalarPeriod
    (Nat.mul_pos C.horizontal_pos C.vertical_pos) fun r ↦
      C.memBool (boxPoint r)
end TranslationalTilings

/- blueprint/08-algorithms.md:151; TranslationalTilings.LatticePeriodicSetCode.toSet_periodic -/
namespace TranslationalTilings
axiom LatticePeriodicSetCode.toSet_periodic
    (C : LatticePeriodicSetCode) :
  SetPeriodicOn C.periodLattice C.toSet
end TranslationalTilings

/- blueprint/08-algorithms.md:155; TranslationalTilings.LatticePeriodicSetCode.scalarLattice_le -/
namespace TranslationalTilings
axiom LatticePeriodicSetCode.scalarLattice_le
    (C : LatticePeriodicSetCode) :
  scalarLattice C.scalarPeriod ≤ C.periodLattice
end TranslationalTilings

/- blueprint/08-algorithms.md:159; TranslationalTilings.LatticePeriodicSetCode.toScalarCode_toSet -/
namespace TranslationalTilings
axiom LatticePeriodicSetCode.toScalarCode_toSet
    (C : LatticePeriodicSetCode) :
  C.toScalarCode.toSet = C.toSet
end TranslationalTilings

/- blueprint/08-algorithms.md:163; TranslationalTilings.exists_latticePeriodicSetCode_of_finite_quotient -/
namespace TranslationalTilings
axiom exists_latticePeriodicSetCode_of_finite_quotient
    (Λ : AddSubgroup Plane) [Finite (Plane ⧸ Λ)]
    (E : Set Plane) (hE : SetPeriodicOn Λ E) :
  ∃ C : LatticePeriodicSetCode,
    C.periodLattice = Λ ∧ C.toSet = E
end TranslationalTilings

/- blueprint/08-algorithms.md:195; TranslationalTilings.countedOr -/
namespace TranslationalTilings
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
def countedAny (s : Finset α) (p : α → Bool × ℕ) : Bool × ℕ :=
  s.fold countedOr (false, 1) p
end TranslationalTilings

/- blueprint/08-algorithms.md:237; TranslationalTilings.countedAll -/
namespace TranslationalTilings
def countedAll (s : Finset α) (p : α → Bool × ℕ) : Bool × ℕ :=
  s.fold countedAnd (true, 1) p
end TranslationalTilings

/- blueprint/08-algorithms.md:240; TranslationalTilings.countedCount -/
namespace TranslationalTilings
def countedCount (s : Finset α) (p : α → Bool × ℕ) : ℕ × ℕ :=
  s.fold countedAdd (0, 1) fun x ↦
    let r := p x
    (if r.1 then 1 else 0, r.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:245; TranslationalTilings.finsetAnyBool -/
namespace TranslationalTilings
def finsetAnyBool (s : Finset α) (p : α → Bool) : Bool :=
  (countedAny s fun x ↦ (p x, 0)).1
end TranslationalTilings

/- blueprint/08-algorithms.md:248; TranslationalTilings.finsetAllBool -/
namespace TranslationalTilings
def finsetAllBool (s : Finset α) (p : α → Bool) : Bool :=
  (countedAll s fun x ↦ (p x, 0)).1
end TranslationalTilings

/- blueprint/08-algorithms.md:251; TranslationalTilings.PeriodicSetCode.isEmptyBool -/
namespace TranslationalTilings
def PeriodicSetCode.isEmptyBool (C : PeriodicSetCode d) : Bool :=
  finsetAllBool (Finset.univ : Finset (BoxResidue d C.period)) fun r ↦
    !C.bits r
end TranslationalTilings

/- blueprint/08-algorithms.md:255; TranslationalTilings.PeriodicSetCode.memCounted -/
namespace TranslationalTilings
def PeriodicSetCode.memCounted
    (C : PeriodicSetCode d) (x : Lattice d) : Bool × ℕ :=
  (C.memBool x, d + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:259; TranslationalTilings.periodicTileCountCounted -/
namespace TranslationalTilings
def periodicTileCountCounted (F : Finset (Lattice d))
    (C : PeriodicSetCode d) (x : Lattice d) : ℕ × ℕ :=
  countedCount F
    (fun f ↦
      let r := C.memCounted (x - f)
      (r.1, r.2 + d))
end TranslationalTilings

/- blueprint/08-algorithms.md:266; TranslationalTilings.periodicTilingPointCounted -/
namespace TranslationalTilings
def periodicTilingPointCounted (F : Finset (Lattice d))
    (A E : PeriodicSetCode d) (x : Lattice d) : Bool × ℕ :=
  let lhs := periodicTileCountCounted F A x
  let rhs := E.memCounted x
  (decide (lhs.1 = if rhs.1 then 1 else 0), lhs.2 + rhs.2 + 2)
end TranslationalTilings

/- blueprint/08-algorithms.md:272; TranslationalTilings.commonCodePeriod -/
namespace TranslationalTilings
def commonCodePeriod (A E : PeriodicSetCode d) : ℕ :=
  Nat.lcm A.period E.period
end TranslationalTilings

/- blueprint/08-algorithms.md:275; TranslationalTilings.commonCodePeriod_pos -/
namespace TranslationalTilings
theorem commonCodePeriod_pos (A E : PeriodicSetCode d) :
  0 < commonCodePeriod A E :=
  Nat.lcm_pos A.period_pos E.period_pos
end TranslationalTilings

/- blueprint/08-algorithms.md:279; TranslationalTilings.tilesPeriodicTargetCounted -/
namespace TranslationalTilings
def tilesPeriodicTargetCounted (F : Finset (Lattice d))
    (A E : PeriodicSetCode d) : Bool × ℕ :=
  let q := commonCodePeriod A E
  let points : Finset (BoxResidue d q) := Finset.univ
  countedAll points
    (fun x ↦ periodicTilingPointCounted F A E (boxPoint x))
end TranslationalTilings

/- blueprint/08-algorithms.md:286; TranslationalTilings.tilesPeriodicTargetBool -/
namespace TranslationalTilings
def tilesPeriodicTargetBool (F : Finset (Lattice d))
    (A E : PeriodicSetCode d) : Bool :=
  (tilesPeriodicTargetCounted F A E).1
end TranslationalTilings

/- blueprint/08-algorithms.md:290; TranslationalTilings.periodicCandidateCheckCost -/
namespace TranslationalTilings
def periodicCandidateCheckCost (d tileCard q : ℕ) : ℕ :=
  q ^ d * (tileCard * (2 * d + 3) + d + 5) + 1
end TranslationalTilings

/- blueprint/08-algorithms.md:304; TranslationalTilings.tilesPeriodicTargetBool_eq_true_iff -/
namespace TranslationalTilings
axiom tilesPeriodicTargetBool_eq_true_iff
    (F : Finset (Lattice d)) (A E : PeriodicSetCode d) :
  tilesPeriodicTargetBool F A E = true ↔ Tiles F A.toSet E.toSet
end TranslationalTilings

/- blueprint/08-algorithms.md:308; TranslationalTilings.tilesPeriodicTargetCounted_cost_exact -/
namespace TranslationalTilings
axiom tilesPeriodicTargetCounted_cost_exact
    (F : Finset (Lattice d)) (A E : PeriodicSetCode d) :
  (tilesPeriodicTargetCounted F A E).2 =
    periodicCandidateCheckCost d F.card (commonCodePeriod A E)
end TranslationalTilings

/- blueprint/08-algorithms.md:313; TranslationalTilings.tilesPeriodicTargetCounted_cost -/
namespace TranslationalTilings
theorem tilesPeriodicTargetCounted_cost
    (F : Finset (Lattice d)) (A E : PeriodicSetCode d) :
  (tilesPeriodicTargetCounted F A E).2 ≤
    periodicCandidateCheckCost d F.card (commonCodePeriod A E) :=
  (tilesPeriodicTargetCounted_cost_exact F A E).le
end TranslationalTilings

/- blueprint/08-algorithms.md:319; TranslationalTilings.PeriodicSetCode.isEmptyBool_eq_true_iff -/
namespace TranslationalTilings
axiom PeriodicSetCode.isEmptyBool_eq_true_iff (C : PeriodicSetCode d) :
  C.isEmptyBool = true ↔ C.toSet = ∅
end TranslationalTilings

/- blueprint/08-algorithms.md:338; TranslationalTilings.countedAllRange -/
namespace TranslationalTilings
def countedAllRange : (n : ℕ) → (ℕ → Bool × ℕ) → Bool × ℕ
  | 0, _ => (true, 1)
  | n + 1, p =>
      let previous := countedAllRange n p
      let current := p n
      (previous.1 && current.1, previous.2 + current.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:345; TranslationalTilings.searchBoolTablesCounted -/
namespace TranslationalTilings
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
def boolTableSearchCost : ℕ → ℕ → ℕ
  | 0, leafCost => leafCost + 1
  | n + 1, leafCost => 2 * boolTableSearchCost n leafCost + 1
end TranslationalTilings

/- blueprint/08-algorithms.md:362; TranslationalTilings.searchPositivePeriodsCounted -/
namespace TranslationalTilings
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
def positivePeriodSearchCost : (B : ℕ) → (ℕ → ℕ) → ℕ
  | 0, _ => 1
  | B + 1, leafCost =>
      positivePeriodSearchCost B leafCost + leafCost (B + 1) + 1
end TranslationalTilings

/- blueprint/08-algorithms.md:375; TranslationalTilings.planarBoxIndex -/
namespace TranslationalTilings
def planarBoxIndex (q : ℕ) (x : BoxResidue 2 q) : Fin (q ^ 2) :=
  ⟨(x 0 : ℕ) * q + (x 1 : ℕ), by
    have hx0 := (x 0).isLt
    have hx1 := (x 1).isLt
    nlinarith⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:381; TranslationalTilings.planarBitsCode -/
namespace TranslationalTilings
def planarBitsCode (q : ℕ) (hq : 0 < q)
    (bits : Fin (q ^ 2) → Bool) : PeriodicSetCode 2 :=
  PeriodicSetCode.ofBits q hq fun x ↦ bits (planarBoxIndex q x)
end TranslationalTilings

/- blueprint/08-algorithms.md:385; TranslationalTilings.planarBoxPointAt -/
namespace TranslationalTilings
def planarBoxPointAt (q i : ℕ) : Plane :=
  ![(i / q : ℕ), (i % q : ℕ)]
end TranslationalTilings

/- blueprint/08-algorithms.md:388; TranslationalTilings.planarShiftedMemCounted -/
namespace TranslationalTilings
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
def planarTileCountCandidateCounted (F : Finset Plane)
    (q : ℕ) (hq : 0 < q) (bits : Fin (q ^ 2) → Bool)
    (x : Plane) : ℕ × ℕ :=
  F.fold countedAdd (0, 1) fun f ↦
    let r := planarShiftedMemCounted q hq bits x f
    (if r.1 then 1 else 0, r.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:406; TranslationalTilings.planarTilingPointCandidateCounted -/
namespace TranslationalTilings
def planarTilingPointCandidateCounted (F : Finset Plane)
    (q : ℕ) (hq : 0 < q) (bits : Fin (q ^ 2) → Bool)
    (x : Plane) : Bool × ℕ :=
  let lhs := planarTileCountCandidateCounted F q hq bits x
  (decide (lhs.1 = 1), lhs.2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:412; TranslationalTilings.planarCandidateCheckCounted -/
namespace TranslationalTilings
def planarCandidateCheckCounted (F : Finset Plane)
    (q : ℕ) (hq : 0 < q) (bits : Fin (q ^ 2) → Bool) : Bool × ℕ :=
  countedAllRange (q ^ 2) fun i ↦
    let r := planarTilingPointCandidateCounted F q hq bits
      (planarBoxPointAt q i)
    (r.1, r.2 + 2)
end TranslationalTilings

/- blueprint/08-algorithms.md:419; TranslationalTilings.planarCandidateCheckCost -/
namespace TranslationalTilings
def planarCandidateCheckCost (tileCard q : ℕ) : ℕ :=
  q ^ 2 * (9 * tileCard + 5) + 1
end TranslationalTilings

/- blueprint/08-algorithms.md:422; TranslationalTilings.planarTilePeriodCheckCounted -/
namespace TranslationalTilings
def planarTilePeriodCheckCounted (F : Finset Plane)
    (M : ℕ) (hM : 0 < M) : Bool × ℕ :=
  searchBoolTablesCounted (M ^ 2)
    (planarCandidateCheckCounted F M hM)
end TranslationalTilings

/- blueprint/08-algorithms.md:427; TranslationalTilings.planarTilePeriodSearchCost -/
namespace TranslationalTilings
def planarTilePeriodSearchCost (F : Finset Plane) (M : ℕ) : ℕ :=
  boolTableSearchCost (M ^ 2) (planarCandidateCheckCost F.card M)
end TranslationalTilings

/- blueprint/08-algorithms.md:430; TranslationalTilings.planarTileDecisionCounted -/
namespace TranslationalTilings
def planarTileDecisionCounted (F : Finset Plane) : Bool × ℕ :=
  searchPositivePeriodsCounted
    (periodicTilingPeriodBound F.card (l1Diameter F))
    (planarTilePeriodCheckCounted F)
end TranslationalTilings

/- blueprint/08-algorithms.md:435; TranslationalTilings.planarTileDecision -/
namespace TranslationalTilings
def planarTileDecision (F : Finset Plane) : Bool :=
  (planarTileDecisionCounted F).1
end TranslationalTilings

/- blueprint/08-algorithms.md:438; TranslationalTilings.planarTileSearchCost -/
namespace TranslationalTilings
def planarTileSearchCost (F : Finset Plane) : ℕ :=
  positivePeriodSearchCost
    (periodicTilingPeriodBound F.card (l1Diameter F))
    (planarTilePeriodSearchCost F)
end TranslationalTilings

/- blueprint/08-algorithms.md:443; TranslationalTilings.planarTileSearchExponent -/
namespace TranslationalTilings
def planarTileSearchExponent (F : Finset Plane) : ℕ :=
  (F.card + 2) *
    (periodicTilingPeriodBound F.card (l1Diameter F) + 2) ^ 4
end TranslationalTilings

/- blueprint/08-algorithms.md:447; TranslationalTilings.planarTileDiameterExponent -/
namespace TranslationalTilings
def planarTileDiameterExponent (tileCard : ℕ) : ℕ :=
  4 * periodicTilingExponent tileCard
end TranslationalTilings

/- blueprint/08-algorithms.md:450; TranslationalTilings.planarTileSearchConstant -/
namespace TranslationalTilings
def planarTileSearchConstant (tileCard : ℕ) : ℕ :=
  16 * (tileCard + 2) * (periodicTilingConstant tileCard + 3) ^ 4
end TranslationalTilings

/- blueprint/08-algorithms.md:477; TranslationalTilings.countedAllRange_cost -/
namespace TranslationalTilings
axiom countedAllRange_cost (n : ℕ) (p : ℕ → Bool × ℕ) :
  (countedAllRange n p).2 =
    1 + ∑ i ∈ Finset.range n, ((p i).2 + 1)
end TranslationalTilings

/- blueprint/08-algorithms.md:481; TranslationalTilings.searchBoolTablesCounted_eq_true_iff -/
namespace TranslationalTilings
axiom searchBoolTablesCounted_eq_true_iff (n : ℕ)
    (check : (Fin n → Bool) → Bool × ℕ) :
  (searchBoolTablesCounted n check).1 = true ↔
    ∃ bits : Fin n → Bool, (check bits).1 = true
end TranslationalTilings

/- blueprint/08-algorithms.md:486; TranslationalTilings.searchBoolTablesCounted_cost -/
namespace TranslationalTilings
axiom searchBoolTablesCounted_cost (n leafCost : ℕ)
    (check : (Fin n → Bool) → Bool × ℕ)
    (hcost : ∀ bits, (check bits).2 = leafCost) :
  (searchBoolTablesCounted n check).2 =
    boolTableSearchCost n leafCost
end TranslationalTilings

/- blueprint/08-algorithms.md:492; TranslationalTilings.boolTableSearchCost_closed -/
namespace TranslationalTilings
axiom boolTableSearchCost_closed (n leafCost : ℕ) :
  boolTableSearchCost n leafCost + 1 = 2 ^ n * (leafCost + 2)
end TranslationalTilings

/- blueprint/08-algorithms.md:495; TranslationalTilings.searchPositivePeriodsCounted_eq_true_iff -/
namespace TranslationalTilings
axiom searchPositivePeriodsCounted_eq_true_iff (B : ℕ)
    (check : (M : ℕ) → 0 < M → Bool × ℕ) :
  (searchPositivePeriodsCounted B check).1 = true ↔
    ∃ (M : ℕ) (hM : 0 < M), M ≤ B ∧ (check M hM).1 = true
end TranslationalTilings

/- blueprint/08-algorithms.md:500; TranslationalTilings.searchPositivePeriodsCounted_cost -/
namespace TranslationalTilings
axiom searchPositivePeriodsCounted_cost (B : ℕ)
    (check : (M : ℕ) → 0 < M → Bool × ℕ) (leafCost : ℕ → ℕ)
    (hcost : ∀ M (hM : 0 < M), M ≤ B →
      (check M hM).2 = leafCost M) :
  (searchPositivePeriodsCounted B check).2 =
    positivePeriodSearchCost B leafCost
end TranslationalTilings

/- blueprint/08-algorithms.md:507; TranslationalTilings.planarCandidateCheckCounted_eq_true_iff -/
namespace TranslationalTilings
axiom planarCandidateCheckCounted_eq_true_iff
    (F : Finset Plane) (q : ℕ) (hq : 0 < q)
    (bits : Fin (q ^ 2) → Bool) :
  (planarCandidateCheckCounted F q hq bits).1 = true ↔
    TilesUniverse F (planarBitsCode q hq bits).toSet
end TranslationalTilings

/- blueprint/08-algorithms.md:513; TranslationalTilings.planarCandidateCheckCounted_cost -/
namespace TranslationalTilings
axiom planarCandidateCheckCounted_cost
    (F : Finset Plane) (q : ℕ) (hq : 0 < q)
    (bits : Fin (q ^ 2) → Bool) :
  (planarCandidateCheckCounted F q hq bits).2 =
    planarCandidateCheckCost F.card q
end TranslationalTilings

/- blueprint/08-algorithms.md:519; TranslationalTilings.planarTilePeriodCheckCounted_cost -/
namespace TranslationalTilings
axiom planarTilePeriodCheckCounted_cost
    (F : Finset Plane) (M : ℕ) (hM : 0 < M) :
  (planarTilePeriodCheckCounted F M hM).2 =
    planarTilePeriodSearchCost F M
end TranslationalTilings

/- blueprint/08-algorithms.md:524; TranslationalTilings.planarTileDecision_eq_true_iff -/
namespace TranslationalTilings
axiom planarTileDecision_eq_true_iff (F : Finset Plane) :
  planarTileDecision F = true ↔ ∃ A : Set Plane, TilesUniverse F A
end TranslationalTilings

/- blueprint/08-algorithms.md:527; TranslationalTilings.planarTileDecisionCounted_cost_exact -/
namespace TranslationalTilings
axiom planarTileDecisionCounted_cost_exact (F : Finset Plane) :
  (planarTileDecisionCounted F).2 = planarTileSearchCost F
end TranslationalTilings

/- blueprint/08-algorithms.md:530; TranslationalTilings.planarTileDecisionCounted_cost -/
namespace TranslationalTilings
theorem planarTileDecisionCounted_cost (F : Finset Plane) :
  (planarTileDecisionCounted F).2 ≤ planarTileSearchCost F :=
  (planarTileDecisionCounted_cost_exact F).le
end TranslationalTilings

/- blueprint/08-algorithms.md:534; TranslationalTilings.planarTileSearchCost_eq_sum -/
namespace TranslationalTilings
axiom planarTileSearchCost_eq_sum (F : Finset Plane) :
  let B := periodicTilingPeriodBound F.card (l1Diameter F)
  planarTileSearchCost F =
    1 + ∑ k ∈ Finset.range B,
      2 ^ ((k + 1) ^ 2) *
        ((k + 1) ^ 2 * (9 * F.card + 5) + 3)
end TranslationalTilings

/- blueprint/08-algorithms.md:541; TranslationalTilings.planarTileSearchCost_preclosed_bound -/
namespace TranslationalTilings
axiom planarTileSearchCost_preclosed_bound (F : Finset Plane) :
  let B := periodicTilingPeriodBound F.card (l1Diameter F)
  planarTileSearchCost F ≤
    1 + B * (2 ^ (B ^ 2) * (B ^ 2 * (9 * F.card + 5) + 3))
end TranslationalTilings

/- blueprint/08-algorithms.md:546; TranslationalTilings.planarTileSearchCost_closed_bound -/
namespace TranslationalTilings
axiom planarTileSearchCost_closed_bound (F : Finset Plane) :
  planarTileSearchCost F ≤ 2 ^ planarTileSearchExponent F
end TranslationalTilings

/- blueprint/08-algorithms.md:549; TranslationalTilings.planarTileSearchExponent_diameter_bound -/
namespace TranslationalTilings
axiom planarTileSearchExponent_diameter_bound (F : Finset Plane) :
  planarTileSearchExponent F ≤ planarTileSearchConstant F.card *
    max 1 (l1Diameter F ^ planarTileDiameterExponent F.card)
end TranslationalTilings

/- blueprint/08-algorithms.md:553; TranslationalTilings.planarTileDiameterExponent_le_quartic -/
namespace TranslationalTilings
axiom planarTileDiameterExponent_le_quartic (tileCard : ℕ) :
  planarTileDiameterExponent tileCard ≤ 12 * (tileCard + 1) ^ 4
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
def tileAnchor (F : Finset Plane) : Plane :=
  if hF : F.Nonempty then
    pairToPlane ((F.image planeToPair).min' (hF.image planeToPair))
  else 0
end TranslationalTilings

/- blueprint/08-algorithms.md:594; TranslationalTilings.normalizedTile -/
namespace TranslationalTilings
def normalizedTile (F : Finset Plane) : Finset Plane :=
  F.image fun f ↦ f - tileAnchor F
end TranslationalTilings

/- blueprint/08-algorithms.md:597; TranslationalTilings.normalizedTargetCode -/
namespace TranslationalTilings
def normalizedTargetCode
    (F : Finset Plane) (E : PeriodicSetCode 2) : PeriodicSetCode 2 :=
  E.pullbackTranslate (tileAnchor F)
end TranslationalTilings

/- blueprint/08-algorithms.md:603; TranslationalTilings.tileAnchor_mem -/
namespace TranslationalTilings
axiom tileAnchor_mem {F : Finset Plane} (hF : F.Nonempty) :
  tileAnchor F ∈ F
end TranslationalTilings

/- blueprint/08-algorithms.md:606; TranslationalTilings.zero_mem_normalizedTile -/
namespace TranslationalTilings
axiom zero_mem_normalizedTile {F : Finset Plane} (hF : F.Nonempty) :
  0 ∈ normalizedTile F
end TranslationalTilings

/- blueprint/08-algorithms.md:609; TranslationalTilings.card_normalizedTile -/
namespace TranslationalTilings
axiom card_normalizedTile (F : Finset Plane) :
  (normalizedTile F).card = F.card
end TranslationalTilings

/- blueprint/08-algorithms.md:612; TranslationalTilings.diameter_normalizedTile -/
namespace TranslationalTilings
axiom diameter_normalizedTile (F : Finset Plane) :
  l1Diameter (normalizedTile F) = l1Diameter F
end TranslationalTilings

/- blueprint/08-algorithms.md:615; TranslationalTilings.tiles_normalized_iff -/
namespace TranslationalTilings
axiom tiles_normalized_iff (F : Finset Plane) (E : PeriodicSetCode 2)
    (A : Set Plane) :
  Tiles (normalizedTile F) A (normalizedTargetCode F E).toSet ↔
    Tiles F A E.toSet
end TranslationalTilings

/- blueprint/08-algorithms.md:639; TranslationalTilings.classifierDirectionCount -/
namespace TranslationalTilings
def classifierDirectionCount (F : Finset Plane) : ℕ :=
  groupedDirectionCount F
end TranslationalTilings

/- blueprint/08-algorithms.md:642; TranslationalTilings.classifierDirection -/
namespace TranslationalTilings
def classifierDirection (F : Finset Plane) :
    Fin (classifierDirectionCount F) → Plane :=
  groupedTileDirections F
end TranslationalTilings

/- blueprint/08-algorithms.md:646; TranslationalTilings.classifierPrimitiveDirection -/
namespace TranslationalTilings
def classifierPrimitiveDirection (F : Finset Plane)
    (j : Fin (classifierDirectionCount F)) : Plane :=
  primitivePart (classifierDirection F j)
end TranslationalTilings

/- blueprint/08-algorithms.md:650; TranslationalTilings.classifierWeakBound -/
namespace TranslationalTilings
def classifierWeakBound (F : Finset Plane) : ℕ :=
  weakPeriodMultiplierBound F.card (l1Diameter F)
end TranslationalTilings

/- blueprint/08-algorithms.md:653; TranslationalTilings.classifierRepresentativeBound -/
namespace TranslationalTilings
def classifierRepresentativeBound (F : Finset Plane) : ℕ :=
  periodicTilingPeriodBound F.card (l1Diameter F)
end TranslationalTilings

/- blueprint/08-algorithms.md:656; TranslationalTilings.classifierPeriod -/
namespace TranslationalTilings
def classifierPeriod (F : Finset Plane) (E : PeriodicSetCode 2) : ℕ :=
  E.period * (classifierRepresentativeBound F).factorial
end TranslationalTilings

/- blueprint/08-algorithms.md:659; TranslationalTilings.classifierPeriod_pos -/
namespace TranslationalTilings
theorem classifierPeriod_pos (F : Finset Plane) (E : PeriodicSetCode 2) :
  0 < classifierPeriod F E :=
  Nat.mul_pos E.period_pos (Nat.factorial_pos _)
end TranslationalTilings

/- blueprint/08-algorithms.md:663; TranslationalTilings.RepresentativeTupleCode -/
namespace TranslationalTilings
structure RepresentativeTupleCode
    (F : Finset Plane) (E : PeriodicSetCode 2) where
  weakMultiplier : Fin (classifierWeakBound F + 1)
  representative : Fin (classifierDirectionCount F) →
    BoxResidue 2 (classifierPeriod F E) → Bool
deriving DecidableEq, Fintype
end TranslationalTilings

/- blueprint/08-algorithms.md:670; TranslationalTilings.RepresentativeTupleCode.weakMultiplierNat -/
namespace TranslationalTilings
def RepresentativeTupleCode.weakMultiplierNat
    (T : RepresentativeTupleCode F E) : ℕ :=
  T.weakMultiplier
end TranslationalTilings

/- blueprint/08-algorithms.md:674; TranslationalTilings.RepresentativeTupleCode.representativeCode -/
namespace TranslationalTilings
def RepresentativeTupleCode.representativeCode
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) : PeriodicSetCode 2 :=
  PeriodicSetCode.ofBits (classifierPeriod F E)
    (classifierPeriod_pos F E) (T.representative j)
end TranslationalTilings

/- blueprint/08-algorithms.md:680; TranslationalTilings.validRepresentativeTupleBool -/
namespace TranslationalTilings
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
def representativeTuples
    (F : Finset Plane) (E : PeriodicSetCode 2) :
    Finset (RepresentativeTupleCode F E) :=
  Finset.univ.filter fun T ↦ validRepresentativeTupleBool F E T = true
end TranslationalTilings

/- blueprint/08-algorithms.md:703; TranslationalTilings.validRepresentativeTupleBool_eq_true_iff -/
namespace TranslationalTilings
axiom validRepresentativeTupleBool_eq_true_iff
    {E : PeriodicSetCode 2} (T) :
  validRepresentativeTupleBool F E T = true ↔
    0 < T.weakMultiplierNat ∧
    ∀ x,
      ∑ j : Fin (classifierDirectionCount F),
        tileConv F (setIndicator (T.representativeCode j).toSet) x =
          setIndicator E.toSet x
end TranslationalTilings

/- blueprint/08-algorithms.md:712; TranslationalTilings.mem_representativeTuples_iff -/
namespace TranslationalTilings
axiom mem_representativeTuples_iff
    {E : PeriodicSetCode 2} (T) :
  T ∈ representativeTuples F E ↔
    0 < T.weakMultiplierNat ∧
    ∀ x,
      ∑ j : Fin (classifierDirectionCount F),
        tileConv F (setIndicator (T.representativeCode j).toSet) x =
          setIndicator E.toSet x
end TranslationalTilings

/- blueprint/08-algorithms.md:729; TranslationalTilings.multipleCoordinate? -/
namespace TranslationalTilings
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
def classifierLinePeriod (F : Finset Plane) (E : PeriodicSetCode 2)
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) : ℕ :=
  E.period * T.weakMultiplierNat * vectorContent (classifierDirection F j)
end TranslationalTilings

/- blueprint/08-algorithms.md:743; TranslationalTilings.linePatternMemBool -/
namespace TranslationalTilings
def linePatternMemBool (v y : Plane) (period : ℕ) (hperiod : 0 < period)
    (P : LinePattern period) (x : Plane) : Bool :=
  match multipleCoordinate? v (x - y) with
  | none => false
  | some n => P ⟨n.natMod period, Int.natMod_lt hperiod.ne'⟩
end TranslationalTilings

/- blueprint/08-algorithms.md:749; TranslationalTilings.referenceSliceMemBool -/
namespace TranslationalTilings
def referenceSliceMemBool
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) (y x : Plane) : Bool :=
  (T.representativeCode j).memBool x &&
    (multipleCoordinate? (classifierPrimitiveDirection F j) (x - y)).isSome
end TranslationalTilings

/- blueprint/08-algorithms.md:755; TranslationalTilings.linePatternTileCount -/
namespace TranslationalTilings
def linePatternTileCount (F : Finset Plane) (v y : Plane)
    (period : ℕ) (hperiod : 0 < period) (P : LinePattern period)
    (x : Plane) : ℕ :=
  (F.filter fun f ↦ linePatternMemBool v y period hperiod P (x - f)).card
end TranslationalTilings

/- blueprint/08-algorithms.md:760; TranslationalTilings.referenceSliceTileCount -/
namespace TranslationalTilings
def referenceSliceTileCount (F : Finset Plane)
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) (y x : Plane) : ℕ :=
  (F.filter fun f ↦ referenceSliceMemBool T j y (x - f)).card
end TranslationalTilings

/- blueprint/08-algorithms.md:765; TranslationalTilings.lineCheckPeriod -/
namespace TranslationalTilings
def lineCheckPeriod (F : Finset Plane) (E : PeriodicSetCode 2)
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F)) : ℕ :=
  Nat.lcm (classifierLinePeriod F E T j) (classifierPeriod F E)
end TranslationalTilings

/- blueprint/08-algorithms.md:770; TranslationalTilings.differentLinePatternBool -/
namespace TranslationalTilings
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
def decodedLinePattern (v y : Plane) (period : ℕ) (hperiod : 0 < period)
    (P : LinePattern period) : Set Plane :=
  {x | linePatternMemBool v y period hperiod P x}
end TranslationalTilings

/- blueprint/08-algorithms.md:821; TranslationalTilings.multipleCoordinate?_eq_some_iff -/
namespace TranslationalTilings
axiom multipleCoordinate?_eq_some_iff {v : Plane} (hv : v ≠ 0) :
  multipleCoordinate? v z = some n ↔ z = n • v
end TranslationalTilings

/- blueprint/08-algorithms.md:824; TranslationalTilings.equivalentLinePatternBool_eq_true_iff -/
namespace TranslationalTilings
axiom equivalentLinePatternBool_eq_true_iff
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
        addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y)
end TranslationalTilings

/- blueprint/08-algorithms.md:838; TranslationalTilings.hasChameleonSlice_eq_true_iff -/
namespace TranslationalTilings
axiom hasChameleonSlice_eq_true_iff
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (T : RepresentativeTupleCode F E)
    (j : Fin (classifierDirectionCount F))
    (hF : F.Nonempty) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hvalid : validRepresentativeTupleBool F E T = true) :
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
          addCoset (directionSubgroup (classifierPrimitiveDirection F j)) y)
end TranslationalTilings

/- blueprint/08-algorithms.md:866; TranslationalTilings.LineSelection -/
namespace TranslationalTilings
structure LineSelection (F : Finset Plane) (E : PeriodicSetCode 2)
    (T : RepresentativeTupleCode F E) where
  chosen : ∀ j : Fin (classifierDirectionCount F),
    (Plane ⧸ directionSubgroup (classifierPrimitiveDirection F j)) → Set Plane
  supported : ∀ j line,
    chosen j line ⊆ quotientCoset
      (directionSubgroup (classifierPrimitiveDirection F j)) line
  periodic : ∀ j line,
    Function.Periodic (setIndicator (chosen j line))
      ((classifierLinePeriod F E T j : ℤ) •
        classifierPrimitiveDirection F j)
  convolution_equivalent : ∀ j line,
    convolutionEquivalent F (chosen j line)
      ((T.representativeCode j).toSet ∩
        quotientCoset
          (directionSubgroup (classifierPrimitiveDirection F j)) line)
end TranslationalTilings

/- blueprint/08-algorithms.md:883; TranslationalTilings.assembleLineSelection -/
namespace TranslationalTilings
def assembleLineSelection
    (S : LineSelection F E T) : Set Plane :=
  ⋃ j, ⋃ line, S.chosen j line
end TranslationalTilings

/- blueprint/08-algorithms.md:887; TranslationalTilings.ProducedByTuple -/
namespace TranslationalTilings
def ProducedByTuple
    (T : RepresentativeTupleCode F E) (A : Set Plane) : Prop :=
  ∃ S : LineSelection F E T, A = assembleLineSelection S
end TranslationalTilings

/- blueprint/08-algorithms.md:893; TranslationalTilings.directionalDecomposition_uniform_classifier -/
namespace TranslationalTilings
axiom directionalDecomposition_uniform_classifier
    {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic E.period E.toSet) (htile : Tiles F A E.toSet) :
  ∃ (L : ℕ), 0 < L ∧ L ≤ classifierWeakBound F ∧
    ∃ D : DirectionalTilingDecomposition F A E.toSet (E.period * L),
      ∃ hnum : D.numberOfParts = classifierDirectionCount F,
        ∀ j : Fin (classifierDirectionCount F),
          D.direction (Fin.cast hnum.symm j) = classifierDirection F j
end TranslationalTilings

/- blueprint/08-algorithms.md:903; TranslationalTilings.tiling_iff_from_periodic_representatives -/
namespace TranslationalTilings
axiom tiling_iff_from_periodic_representatives
    {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hzero : 0 ∈ F) (hcard : 1 < F.card) :
  Tiles F A E.toSet ↔
    ∃ T ∈ representativeTuples F E, ProducedByTuple T A
end TranslationalTilings

/- blueprint/08-algorithms.md:921; TranslationalTilings.nonOnePeriodicTilingDecisionNormalized -/
namespace TranslationalTilings
def nonOnePeriodicTilingDecisionNormalized
    (F : Finset Plane) (E : PeriodicSetCode 2) : Bool :=
  finsetAnyBool (representativeTuples F E) fun T ↦
    decide (2 ≤ (Finset.univ.filter fun j ↦
      hasChameleonSlice F E T j = true).card)
end TranslationalTilings

/- blueprint/08-algorithms.md:927; TranslationalTilings.nonOnePeriodicTilingDecision -/
namespace TranslationalTilings
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
def nonOnePeriodicTilingDecisionLatticeInput
    (F : Finset Plane) (E : LatticePeriodicSetCode) : Bool :=
  nonOnePeriodicTilingDecision F E.toScalarCode
end TranslationalTilings

/- blueprint/08-algorithms.md:942; TranslationalTilings.two_chameleons_construct_not_onePeriodic -/
namespace TranslationalTilings
axiom two_chameleons_construct_not_onePeriodic
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (T : RepresentativeTupleCode F E)
    (j₁ j₂ : Fin (classifierDirectionCount F))
    (hF : F.Nonempty) (hvalid : T ∈ representativeTuples F E)
    (hne : j₁ ≠ j₂)
    (h₁ : hasChameleonSlice F E T j₁ = true)
    (h₂ : hasChameleonSlice F E T j₂ = true) :
  ∃ A, Tiles F A E.toSet ∧ ¬ OnePeriodic A
end TranslationalTilings

/- blueprint/08-algorithms.md:952; TranslationalTilings.at_most_one_chameleon_all_onePeriodic -/
namespace TranslationalTilings
axiom at_most_one_chameleon_all_onePeriodic
    {F : Finset Plane} {E : PeriodicSetCode 2}
    (T : RepresentativeTupleCode F E)
    (hF : F.Nonempty) (hvalid : T ∈ representativeTuples F E)
    (hatMostOne : ∀ j₁ j₂ : Fin (classifierDirectionCount F),
      hasChameleonSlice F E T j₁ = true →
      hasChameleonSlice F E T j₂ = true → j₁ = j₂) :
  ∀ A, ProducedByTuple T A → OnePeriodic A
end TranslationalTilings

/- blueprint/08-algorithms.md:961; TranslationalTilings.singleton_tile_complement_eq_target -/
namespace TranslationalTilings
axiom singleton_tile_complement_eq_target
    {E : PeriodicSetCode 2}
    (hcard : F.card = 1) (htile : Tiles F A E.toSet) :
  ∃ a ∈ F, A = {x | x + a ∈ E.toSet}
end TranslationalTilings

/- blueprint/08-algorithms.md:966; TranslationalTilings.empty_target_complement_empty -/
namespace TranslationalTilings
axiom empty_target_complement_empty
    {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hE : E.toSet = ∅)
    (htile : Tiles F A E.toSet) :
  A = ∅
end TranslationalTilings

/- blueprint/08-algorithms.md:972; TranslationalTilings.empty_tile_no_nonempty_target_tiling -/
namespace TranslationalTilings
axiom empty_tile_no_nonempty_target_tiling
    {E : PeriodicSetCode 2}
    (hE : E.toSet.Nonempty) :
  ¬ ∃ A, Tiles (∅ : Finset Plane) A E.toSet
end TranslationalTilings

/- blueprint/08-algorithms.md:978; TranslationalTilings.nonOnePeriodicTilingDecision_eq_true_iff -/
namespace TranslationalTilings
axiom nonOnePeriodicTilingDecision_eq_true_iff
    {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hexists : ∃ A, Tiles F A E.toSet) :
  nonOnePeriodicTilingDecision F E = true ↔
    ∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A
end TranslationalTilings

/- blueprint/08-algorithms.md:984; TranslationalTilings.non_one_periodic_tiling_decidable -/
namespace TranslationalTilings
def non_one_periodic_tiling_decidable
    {E : PeriodicSetCode 2}
    (hF : F.Nonempty) (hexists : ∃ A, Tiles F A E.toSet) :
  Decidable (∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A) :=
  decidable_of_iff
    (nonOnePeriodicTilingDecision F E = true)
    (nonOnePeriodicTilingDecision_eq_true_iff hF hexists)
end TranslationalTilings

/- blueprint/08-algorithms.md:992; TranslationalTilings.nonOnePeriodicTilingDecisionLatticeInput_eq_true_iff -/
namespace TranslationalTilings
axiom nonOnePeriodicTilingDecisionLatticeInput_eq_true_iff
    {E : LatticePeriodicSetCode}
    (hF : F.Nonempty) (hexists : ∃ A, Tiles F A E.toSet) :
  nonOnePeriodicTilingDecisionLatticeInput F E = true ↔
    ∃ A : Set Plane, Tiles F A E.toSet ∧ ¬ OnePeriodic A
end TranslationalTilings
