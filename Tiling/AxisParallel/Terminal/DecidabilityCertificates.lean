import Tiling.AxisParallel.Terminal.CertificateCoding
import Tiling.AxisParallel.Terminal.AffineCompilerCorrectness
import Tiling.AxisParallel.Terminal.PositiveCertificateVerification
import Tiling.AxisParallel.Terminal.PositiveCertificateCompleteness
import Tiling.AxisParallel.Terminal.LocalCoverSearch
import Tiling.AxisParallel.Terminal.LocalPackingCompactness
import Tiling.AxisParallel.Terminal.OracleProgramCore
import Tiling.AxisParallel.Terminal.CertificateCore
import Tiling.AxisParallel.Terminal.ExecutableRegionNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped Pointwise

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel
open Tiling.AxisParallel.Terminal.Executable
open Tiling.AxisParallel.Terminal.Executable.PositiveVerification
open Tiling.AxisParallel.Terminal.Executable.LocalCoverSearch
open Tiling.AxisParallel.Terminal.Executable.Semantics
open Tiling.AxisParallel.Terminal.Executable.AffineCompiler

def positiveStage (C : RegionCode) (O : Oracle C) (n : Nat) : Bool :=
  verifyPositiveStage C O n

def negativeStage (C : RegionCode) (O : Oracle C) (n : Nat) : Bool :=
  match buildLocalBound C O, wellFormedNegativeStage n with
  | some B, some code => negativeVerifier AffineCompiler.decideFormula O B code
  | _, _ => false

/-- Prefer an accepting positive certificate at a stage; otherwise accept a negative
certificate; otherwise keep searching. -/
private def dovetailStep (positive negative : Nat → Bool) (n : Nat) : Option Bool :=
  if positive n then some true else if negative n then some false else none

/-- Structurally recursive bounded dovetail.  Every stage up to and including `fuel` is run. -/
private def runThrough (positive negative : Nat → Bool) : Nat → Option Bool
  | 0 => dovetailStep positive negative 0
  | n + 1 =>
      match runThrough positive negative n with
      | some answer => some answer
      | none => dovetailStep positive negative (n + 1)

def decisionThrough (C : RegionCode) (O : Oracle C) (fuel : Nat) : Option Bool :=
  runThrough (positiveStage C O) (negativeStage C O) fuel

/-- A total computed Boolean at supplied fuel.  Its default is deliberately not claimed correct
until `decisionThrough` is proved to have resolved by that fuel. -/
def computedDecisionAtFuel (C : RegionCode) (O : Oracle C) (fuel : Nat) : Bool :=
  (decisionThrough C O fuel).getD false

private def ResolvesBy (C : RegionCode) (O : Oracle C) (fuel : Nat) : Prop :=
  (decisionThrough C O fuel).isSome


def positiveStageProgram (C : RegionCode) (stage : Nat) : OracleProgram (Query C) Bool :=
  match wellFormedPositiveStage stage with
  | none => .pure false
  | some code => verifyPositiveProgram C code

def negativeStageProgram (C : RegionCode) (stage : Nat) : OracleProgram (Query C) Bool :=
  OracleProgram.bind (buildLocalBoundProgram C) fun bound =>
    match bound, wellFormedNegativeStage stage with
    | some B, some code => negativeVerifierProgram B code
    | _, _ => .pure false

private def dovetailStepProgram (C : RegionCode) (n : Nat) :
    OracleProgram (Query C) (Option Bool) :=
  OracleProgram.bind (positiveStageProgram C n) fun positive =>
    if positive then .pure (some true)
    else OracleProgram.bind (negativeStageProgram C n) fun negative =>
      .pure (if negative then some false else none)

/-- The structurally recursive finite-input decision program. Its only runtime inputs are
the combinatorial region code and fuel; realizations and correct-oracle proofs occur only
in its correctness theorem. -/
def decisionThroughProgram (C : RegionCode) : Nat → OracleProgram (Query C) (Option Bool)
  | 0 => dovetailStepProgram C 0
  | n + 1 => OracleProgram.bind (decisionThroughProgram C n) fun earlier =>
      match earlier with
      | some answer => .pure (some answer)
      | none => dovetailStepProgram C (n + 1)

theorem positiveStageProgram_evaluate : ∀ (C : RegionCode) (O : Oracle C) n,
    OracleProgram.evaluate O.answer (positiveStageProgram C n) = positiveStage C O n := by
  intro C O n
  cases h : wellFormedPositiveStage n with
  | none =>
      simp only [positiveStageProgram, h, OracleProgram.evaluate]
      rw [positiveStage, verifyPositiveStage, h]
  | some code =>
      rw [positiveStageProgram, h]
      simpa [positiveStage, verifyPositiveStage, h] using
        (PositiveVerification.verifyPositiveProgram_evaluate C O code)

theorem negativeStageProgram_evaluate : ∀ (C : RegionCode) (O : Oracle C) n,
    OracleProgram.evaluate O.answer (negativeStageProgram C n) = negativeStage C O n := by
  intro C O n
  rw [negativeStageProgram, OracleProgram.evaluate_bind,
    LocalCoverSearch.buildLocalBoundProgram_evaluate]
  cases hbound : buildLocalBound C O with
  | none =>
      simp only [OracleProgram.evaluate]
      simp [negativeStage, hbound]
  | some B =>
      cases hcode : wellFormedNegativeStage n with
      | none =>
          simp only [OracleProgram.evaluate]
          simp [negativeStage, hbound, hcode]
      | some code =>
          rw [LocalCoverSearch.negativeVerifierProgram_evaluate]
          simp [negativeStage, hbound, hcode]

private theorem dovetailStepProgram_evaluate (C : RegionCode) (O : Oracle C) (n : Nat) :
    OracleProgram.evaluate O.answer (dovetailStepProgram C n) =
      dovetailStep (positiveStage C O) (negativeStage C O) n := by
  rw [dovetailStepProgram, OracleProgram.evaluate_bind,
    positiveStageProgram_evaluate]
  by_cases hp : positiveStage C O n
  · simp [dovetailStep, hp, OracleProgram.evaluate]
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    rw [OracleProgram.evaluate_bind, negativeStageProgram_evaluate]
    simp [dovetailStep, hp, OracleProgram.evaluate]

theorem decisionThroughProgram_evaluate : ∀ (C : RegionCode) (O : Oracle C) fuel,
    OracleProgram.evaluate O.answer (decisionThroughProgram C fuel) =
      decisionThrough C O fuel := by
  intro C O fuel
  induction fuel with
  | zero =>
      exact dovetailStepProgram_evaluate C O 0
  | succ fuel ih =>
      rw [decisionThroughProgram, OracleProgram.evaluate_bind, ih]
      cases h : decisionThrough C O fuel with
      | some answer =>
          have hrun : runThrough (positiveStage C O) (negativeStage C O) fuel =
              some answer := by simpa [decisionThrough] using h
          rw [decisionThrough]
          simp [runThrough, hrun, OracleProgram.evaluate]
      | none =>
          rw [dovetailStepProgram_evaluate]
          have hrun : runThrough (positiveStage C O) (negativeStage C O) fuel = none := by
            simpa [decisionThrough] using h
          rw [decisionThrough]
          simp [runThrough, hrun]

private theorem runThrough_none_iff (positive negative : Nat → Bool) : ∀ fuel,
    runThrough positive negative fuel = none ↔
      ∀ n ≤ fuel, dovetailStep positive negative n = none := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro h n hn
        have hn0 : n = 0 := by omega
        subst n
        simpa [runThrough] using h
      · intro h
        simpa [runThrough] using h 0 (by omega)
  | succ fuel ih =>
      constructor
      · intro h n hn
        cases hrun : runThrough positive negative fuel with
        | some answer => simp [runThrough, hrun] at h
        | none =>
            by_cases hlast : n = fuel + 1
            · subst n
              simpa [runThrough, hrun] using h
            · have hnold : n ≤ fuel := by omega
              exact (ih.mp hrun) n hnold
      · intro h
        have hold : runThrough positive negative fuel = none :=
          ih.mpr (fun n hn => h n (by omega))
        have hlast : dovetailStep positive negative (fuel + 1) = none :=
          h (fuel + 1) (by omega)
        simp [runThrough, hold, hlast]

private theorem runThrough_some_iff :
    ∀ (positive negative : Nat → Bool) fuel answer,
    runThrough positive negative fuel = some answer ↔
      ∃ n ≤ fuel, dovetailStep positive negative n = some answer ∧
        ∀ k < n, dovetailStep positive negative k = none := by
  intro positive negative fuel
  induction fuel with
  | zero =>
      intro answer
      constructor
      · intro h
        refine ⟨0, by omega, h, ?_⟩
        intro k hk
        omega
      · rintro ⟨n, hn, hstep, hnone⟩
        have hn0 : n = 0 := by omega
        subst n
        simpa [runThrough] using hstep
  | succ fuel ih =>
      intro answer
      constructor
      · intro h
        cases hrun : runThrough positive negative fuel with
        | some earlier =>
            have hearlier : earlier = answer := by
              simpa [runThrough, hrun] using h
            subst earlier
            obtain ⟨n, hn, hstep, hnone⟩ := (ih answer).mp hrun
            exact ⟨n, by omega, hstep, hnone⟩
        | none =>
            have hstep : dovetailStep positive negative (fuel + 1) = some answer := by
              simpa [runThrough, hrun] using h
            refine ⟨fuel + 1, by omega, hstep, ?_⟩
            intro k hk
            exact (runThrough_none_iff positive negative fuel).mp hrun k (by omega)
      · rintro ⟨n, hn, hstep, hnone⟩
        by_cases hnold : n ≤ fuel
        · have hrun : runThrough positive negative fuel = some answer :=
            (ih answer).mpr ⟨n, hnold, hstep, hnone⟩
          simp [runThrough, hrun]
        · have hnlast : n = fuel + 1 := by omega
          subst n
          have hrun : runThrough positive negative fuel = none :=
            (runThrough_none_iff positive negative fuel).mpr (fun k hk => hnone k (by omega))
          simp [runThrough, hrun, hstep]

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel
open Tiling.AxisParallel.Terminal.Executable
open Tiling.AxisParallel.Terminal.Executable.PositiveVerification
open Tiling.AxisParallel.Terminal.Executable.LocalCoverSearch
open Tiling.AxisParallel.Terminal.LocalPackingCompactness
open Tiling.AxisParallel.Terminal.Executable.AffineCompiler

private theorem tilesOn_multiplicity_one :
    ∀ {K : Region} {S : Set Tiling.Plane}, TilesOn K S Set.univ →
      ∀ᵐ z ∂volume, multiplicity K S z = 1 := by
  intro K S htiles
  rcases htiles with ⟨hcount, hpack, hcover⟩
  have hdisj := (isPacking_iff_openCarrier_disjoint K S).mp hpack
  filter_upwards [hcover] with z hz
  have hex : ∃ s : S, z ∈ (s.1 +ᵥ K.openCarrier) := hz.mp (Set.mem_univ z)
  have hcard : {s : Tiling.Plane | s ∈ S ∧ z ∈ s +ᵥ K.openCarrier}.ncard = 1 := by
    apply Set.ncard_eq_one.mpr
    obtain ⟨s, hs⟩ := hex
    refine ⟨s.1, ?_⟩
    ext t
    constructor
    · intro ht
      by_cases hst : t = s.1
      · simp [hst]
      · exact (Set.disjoint_left.mp (hdisj ht.1 s.2 hst) ht.2 hs).elim
    · intro ht
      subst t
      exact ⟨s.2, hs⟩
  simpa [LocalPackingCompactness.multiplicity] using hcard

theorem negativeStage_sound :
    ∀ {C : RegionCode} (R : Realization C) (O : CorrectOracle C R) n,
      negativeStage C O.toOracle n = true → ¬realizationPlaneTileable R := by
  intro C R O n hstage htile
  obtain ⟨S, hS⟩ := htile
  have hmult : ∀ᵐ z ∂volume, multiplicity R.region S z = 1 :=
    tilesOn_multiplicity_one hS
  unfold negativeStage at hstage
  cases hB : buildLocalBound C O.toOracle with
  | none => simp [hB] at hstage
  | some B =>
      cases hc : wellFormedNegativeStage n with
      | none => simp [hB, hc] at hstage
      | some c =>
          simp only [hB, hc] at hstage
          simp only [negativeVerifier, Bool.and_eq_true] at hstage
          have hcheck := hstage.1
          change
            (decide (0 < c.boxIndex && 0 < c.horizontalSubdivisions &&
                0 < c.verticalSubdivisions) &&
                AffineCompiler.decideFormula O.toOracle _) = true at hcheck
          have hparts := hcheck
          simp only [Bool.and_eq_true] at hparts
          have hsubdiv := hparts.1
          have hsub :=
            (AffineCompiler.decideFormula_correct R O _).mp hparts.2
          have hfail := hstage.2
          change
            (List.range (c.horizontalSubdivisions * c.verticalSubdivisions + 1)).all
              (fun m => !(AffineCompiler.decideFormula O.toOracle
                (localCoverFormula C B c.boxIndex m))) = true at hfail
          obtain ⟨m, x, y, hpack, hrel, hcover⟩ :=
            semanticLocalPacking_formulaWitness R O B hB c.boxIndex S hS.2.1 (by
              filter_upwards [hmult] with z hz hzbox
              simpa [LocalPackingCompactness.multiplicity] using hz)
          have hmle := relevantPacking_cardinality R O B hB c (by
            change decide (0 < c.boxIndex && 0 < c.horizontalSubdivisions &&
              0 < c.verticalSubdivisions) = true
            simpa only [Bool.and_eq_true] using hsubdiv) hsub x y hpack hrel
          have hmle' : m ≤ c.horizontalSubdivisions * c.verticalSubdivisions := hmle
          have hlocal : (localCoverFormula C B c.boxIndex m).Holds R Fin.elim0 Fin.elim0 :=
            (localCover_adequate R B c.boxIndex m).2 ⟨x, y, hpack, hrel, hcover⟩
          have hlocalTrue : AffineCompiler.decideFormula O.toOracle
              (localCoverFormula C B c.boxIndex m) = true :=
            (AffineCompiler.decideFormula_correct R O _).mpr hlocal
          have hmemb : m ∈ List.range (c.horizontalSubdivisions * c.verticalSubdivisions + 1) := by
            simp only [List.mem_range]
            omega
          have hnot := (List.all_eq_true.mp hfail) m hmemb
          simp [hlocalTrue] at hnot

private theorem buildLocalBound_exists {C : RegionCode}
    (R : Realization C) (O : CorrectOracle C R) :
    ∃ B : LocalBoundCode C, buildLocalBound C O.toOracle = some B := by
  have hcell : 0 < C.cellCount := by
    simpa [RegionCode.wellFormed] using R.wellFormed
  simp [buildLocalBound, hcell]

private theorem localBound_diameters_pos {C : RegionCode}
    (R : Realization C) (O : CorrectOracle C R) (B : LocalBoundCode C)
    (hB : buildLocalBound C O.toOracle = some B) :
    0 < evalCoeff R .horizontal B.horizontalDiameter ∧
      0 < evalCoeff R .vertical B.verticalDiameter := by
  have hA := buildLocalBound_adequate R O B hB
  have hw : 0 < evalCoeff R .horizontal B.horizontalWidth := by
    rw [hA.2.2.1]
    exact sub_pos.mpr (R.left_lt_right B.widthCell)
  have hv : 0 < evalCoeff R .vertical B.verticalWidth := by
    rw [hA.2.2.2]
    exact sub_pos.mpr (R.bottom_lt_top B.widthCell)
  have hx := hA.1 (C.rightVertex B.widthCell) (C.leftVertex B.widthCell)
  have hy := hA.2.1 (C.topVertex B.widthCell) (C.bottomVertex B.widthCell)
  rw [abs_of_pos (sub_pos.mpr (R.left_lt_right B.widthCell))] at hx
  rw [abs_of_pos (sub_pos.mpr (R.bottom_lt_top B.widthCell))] at hy
  exact ⟨by linarith, by linarith⟩

private theorem closedBall_subset_semanticLocalBox {C : RegionCode}
    (R : Realization C) (O : CorrectOracle C R) (B : LocalBoundCode C)
    (hB : buildLocalBound C O.toOracle = some B) :
    ∀ ballRadius : Nat, ∃ boxIndex : Nat, 0 < boxIndex ∧
      Metric.closedBall (0 : Tiling.Plane) ballRadius ⊆
        semanticLocalBox R B boxIndex := by
  intro ballRadius
  have hpos := localBound_diameters_pos R O B hB
  let dh := evalCoeff R .horizontal B.horizontalDiameter
  let dv := evalCoeff R .vertical B.verticalDiameter
  obtain ⟨boxIndex, hbox⟩ := exists_nat_gt ((ballRadius : ℝ) / min dh dv)
  have hmin : 0 < min dh dv := lt_min hpos.1 hpos.2
  have hball : (ballRadius : ℝ) < boxIndex * min dh dv := by
    rw [div_lt_iff₀ hmin] at hbox
    simpa [Nat.cast_mul] using hbox
  refine ⟨boxIndex + 1, Nat.succ_pos _, ?_⟩
  intro z hz
  have hzdist : ‖z‖ ≤ (ballRadius : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hre : |z.re| ≤ (ballRadius : ℝ) :=
    (Complex.abs_re_le_norm z).trans hzdist
  have him : |z.im| ≤ (ballRadius : ℝ) :=
    (Complex.abs_im_le_norm z).trans hzdist
  dsimp [semanticLocalBox, dh, dv]
  have hmulh : (ballRadius : ℝ) < (boxIndex + 1) * dh := by
    have hm : min dh dv ≤ dh := min_le_left _ _
    have hb' : (ballRadius : ℝ) < (boxIndex : ℝ) * min dh dv := hball
    have hn : (boxIndex : ℝ) ≤ (boxIndex + 1 : Nat) := by norm_num
    nlinarith
  have hmulv : (ballRadius : ℝ) < (boxIndex + 1) * dv := by
    have hm : min dh dv ≤ dv := min_le_right _ _
    have hb' : (ballRadius : ℝ) < (boxIndex : ℝ) * min dh dv := hball
    have hn : (boxIndex : ℝ) ≤ (boxIndex + 1 : Nat) := by norm_num
    nlinarith
  have hre_lo : -((boxIndex + 1 : ℝ) * dh) < z.re :=
    lt_of_lt_of_le (neg_lt_neg hmulh) (neg_le_of_abs_le hre)
  have hre_hi : z.re < (boxIndex + 1) * dh :=
    lt_of_le_of_lt (le_abs_self z.re |>.trans hre) hmulh
  have him_lo : -((boxIndex + 1 : ℝ) * dv) < z.im :=
    lt_of_lt_of_le (neg_lt_neg hmulv) (neg_le_of_abs_le him)
  have him_hi : z.im < (boxIndex + 1) * dv :=
    lt_of_le_of_lt (le_abs_self z.im |>.trans him) hmulv
  simpa [dh, dv, Nat.cast_add] using (show
    -((boxIndex + 1 : ℝ) * dh) < z.re ∧
      z.re < (boxIndex + 1 : ℝ) * dh ∧
      -((boxIndex + 1 : ℝ) * dv) < z.im ∧
      z.im < (boxIndex + 1 : ℝ) * dv from
    ⟨hre_lo, hre_hi, him_lo, him_hi⟩)

private theorem localCoverFormula_to_semanticPacking {C : RegionCode}
    (R : Realization C) (B : LocalBoundCode C) N m
    (hformula : (localCoverFormula C B N m).Holds R Fin.elim0 Fin.elim0) :
    ∃ S : Set Tiling.Plane,
      Tiling.IsPacking R.region.toPolygonalRegion.prototileFamily
        (R.region.toPolygonalRegion.placements S) ∧
      ∀ᵐ z ∂volume, z ∈ semanticLocalBox R B N →
        multiplicity R.region S z = 1 := by
  obtain ⟨S, _hfinite, hpacking, hcover⟩ :=
    localCoverFormula_sound R B N m hformula
  have hdisj := (isPacking_iff_openCarrier_disjoint R.region S).mp hpacking
  refine ⟨S, hpacking, ?_⟩
  filter_upwards [hcover] with z hz
  intro hzbox
  obtain ⟨s, hsS, hzs⟩ := hz hzbox
  have hcard : {t : Tiling.Plane | t ∈ S ∧ z ∈ t +ᵥ R.region.openCarrier}.ncard = 1 := by
    apply Set.ncard_eq_one.mpr
    refine ⟨s, ?_⟩
    ext t
    constructor
    · intro ht
      by_cases hst : t = s
      · simp [hst]
      · exact (Set.disjoint_left.mp (hdisj ht.1 hsS hst) ht.2 hzs).elim
    · intro ht
      subst t
      exact ⟨hsS, hzs⟩
  simpa [LocalPackingCompactness.multiplicity] using hcard

private theorem semanticBoxCover_restrict_closedBall :
    ∀ {K : Region} {S : Set Tiling.Plane} {box : Set Tiling.Plane} {N : Nat},
    Metric.closedBall (0 : Tiling.Plane) N ⊆ box →
    (∀ᵐ z ∂volume, z ∈ box → multiplicity K S z = 1) →
      ∀ᵐ z ∂volume, z ∈ Metric.closedBall (0 : Tiling.Plane) N →
        multiplicity K S z = 1 := by
  intro K S box N hsubset hmult
  filter_upwards [hmult] with z hzbox hzball
  exact hzbox (hsubset hzball)

theorem negativeStage_complete :
    ∀ {C : RegionCode} (R : Realization C) (O : CorrectOracle C R),
      ¬realizationPlaneTileable R → ∃ n, negativeStage C O.toOracle n = true := by
  intro C R O hnotile
  have hex : ∃ N : Nat, 0 < N ∧
      ¬ ∃ S : Set Tiling.Plane,
        Tiling.IsPacking R.region.toPolygonalRegion.prototileFamily
          (R.region.toPolygonalRegion.placements S) ∧
        ∀ᵐ z ∂volume, z ∈ Metric.closedBall (0 : Tiling.Plane) N →
          multiplicity R.region S z = 1 := by
    by_contra h
    push Not at h
    apply hnotile
    obtain ⟨L, hL⟩ := localCoverings_compactness R.region (fun N hN => h N hN)
    exact ⟨L, hL⟩
  obtain ⟨ballRadius, hballRadius, hnocover⟩ := hex
  obtain ⟨B, hB⟩ := buildLocalBound_exists R O
  obtain ⟨boxIndex, hboxIndex, hballsubset⟩ :=
    closedBall_subset_semanticLocalBox R O B hB ballRadius
  obtain ⟨q₁, q₂, hq₁, hq₂, hsubh, hsubv⟩ :=
    subdivision_exists R O B hB boxIndex hboxIndex
  let c : RawNegativeCode :=
    { boxIndex := boxIndex
      horizontalSubdivisions := q₁
      verticalSubdivisions := q₂ }
  have hc : c.wellFormed = true := by
    simp [c, RawNegativeCode.wellFormed, hboxIndex, hq₁, hq₂]
  obtain ⟨n, hn⟩ := wellFormedNegativeStage_complete c hc
  refine ⟨n, ?_⟩
  unfold negativeStage
  rw [hB, hn]
  simp only [negativeVerifier, Bool.and_eq_true]
  constructor
  · change
      (decide (0 < c.boxIndex && 0 < c.horizontalSubdivisions &&
        0 < c.verticalSubdivisions) &&
        AffineCompiler.decideFormula O.toOracle _) = true
    simp only [Bool.and_eq_true]
    constructor
    · simpa [c, RawNegativeCode.wellFormed] using hc
    · apply (AffineCompiler.decideFormula_correct R O _).mpr
      exact (positiveSubdivision_adequate R B c).mpr ⟨hsubh, hsubv⟩
  · change
      (List.range (c.horizontalSubdivisions * c.verticalSubdivisions + 1)).all
        (fun m => !(AffineCompiler.decideFormula O.toOracle
          (localCoverFormula C B c.boxIndex m))) = true
    apply List.all_eq_true.mpr
    intro m hm
    by_cases hlocal : AffineCompiler.decideFormula O.toOracle
        (localCoverFormula C B c.boxIndex m) = true
    · have hformula := (AffineCompiler.decideFormula_correct R O _).mp hlocal
      obtain ⟨S, hpacking, hmult⟩ :=
        localCoverFormula_to_semanticPacking R B c.boxIndex m hformula
      have hballmult : ∀ᵐ z ∂volume, z ∈ Metric.closedBall (0 : Tiling.Plane) ballRadius →
          multiplicity R.region S z = 1 := by
        exact semanticBoxCover_restrict_closedBall hballsubset hmult
      exact (hnocover ⟨S, hpacking, hballmult⟩).elim
    · simp [hlocal]
end Tiling.AxisParallel.Terminal


namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel
open Tiling.AxisParallel.Terminal.Executable
open Tiling.AxisParallel.Terminal.Executable.PositiveVerification
open Tiling.AxisParallel.Terminal.Executable.LocalCoverSearch
open Tiling.AxisParallel.Terminal.Executable.Semantics
open Tiling.AxisParallel.Terminal.Executable.AffineCompiler

def originalRegionPositiveProgram {K : Region} (N : RegionNormalization K) (stage : Nat) :
    OracleProgram (Query N.code) Bool :=
  OracleProgram.mapQuery (RuntimeRebase.rebaseQuery N.code.originVertex)
    (positiveStageProgram N.code stage)

def originalRegionNegativeProgram {K : Region} (N : RegionNormalization K) (stage : Nat) :
    OracleProgram (Query N.code) Bool :=
  OracleProgram.mapQuery (RuntimeRebase.rebaseQuery N.code.originVertex)
    (negativeStageProgram N.code stage)

def originalRegionDecisionProgram {K : Region} (N : RegionNormalization K) (fuel : Nat) :
    OracleProgram (Query N.code) (Option Bool) :=
  OracleProgram.mapQuery (RuntimeRebase.rebaseQuery N.code.originVertex)
    (decisionThroughProgram N.code fuel)

noncomputable def originalProgram {E : EncodedAxisParallelRegion}
    (N : RegionNormalization E.region) (A : LegacyNormalizationAdapter E N) (fuel : Nat) :
    OracleProgram (CoordQuery E) (Option Bool) :=
  OracleProgram.mapQuery
    (fun q => toLegacyQuery A (RuntimeRebase.rebaseQuery N.code.originVertex q))
    (decisionThroughProgram N.code fuel)

noncomputable def originalPositiveProgram {E : EncodedAxisParallelRegion}
    (N : RegionNormalization E.region) (A : LegacyNormalizationAdapter E N) (stage : Nat) :
    OracleProgram (CoordQuery E) Bool :=
  OracleProgram.mapQuery
    (fun q => toLegacyQuery A (RuntimeRebase.rebaseQuery N.code.originVertex q))
    (positiveStageProgram N.code stage)

noncomputable def originalNegativeProgram {E : EncodedAxisParallelRegion}
    (N : RegionNormalization E.region) (A : LegacyNormalizationAdapter E N) (stage : Nat) :
    OracleProgram (CoordQuery E) Bool :=
  OracleProgram.mapQuery
    (fun q => toLegacyQuery A (RuntimeRebase.rebaseQuery N.code.originVertex q))
    (negativeStageProgram N.code stage)

theorem originalRegionPrograms_evaluate :
    ∀ {K : Region} (N : RegionNormalization K) (O : Oracle N.code),
      (∀ stage,
        OracleProgram.evaluate O.answer (originalRegionPositiveProgram N stage) =
          positiveStage N.code
            (RuntimeRebase.rebaseOracle N.code.originVertex O) stage) ∧
      (∀ stage,
        OracleProgram.evaluate O.answer (originalRegionNegativeProgram N stage) =
          negativeStage N.code
            (RuntimeRebase.rebaseOracle N.code.originVertex O) stage) ∧
      (∀ fuel,
        OracleProgram.evaluate O.answer (originalRegionDecisionProgram N fuel) =
          decisionThrough N.code
            (RuntimeRebase.rebaseOracle N.code.originVertex O) fuel) := by
  intro K N O
  refine ⟨?_, ?_, ?_⟩
  · intro stage
    rw [originalRegionPositiveProgram, OracleProgram.evaluate_mapQuery]
    simpa [RuntimeRebase.rebaseOracle] using
      (positiveStageProgram_evaluate N.code
        (RuntimeRebase.rebaseOracle N.code.originVertex O) stage)
  · intro stage
    rw [originalRegionNegativeProgram, OracleProgram.evaluate_mapQuery]
    simpa [RuntimeRebase.rebaseOracle] using
      (negativeStageProgram_evaluate N.code
        (RuntimeRebase.rebaseOracle N.code.originVertex O) stage)
  · intro fuel
    rw [originalRegionDecisionProgram, OracleProgram.evaluate_mapQuery]
    simpa [RuntimeRebase.rebaseOracle] using
      (decisionThroughProgram_evaluate N.code
        (RuntimeRebase.rebaseOracle N.code.originVertex O) fuel)

theorem originalProgram_evaluate :
    ∀ (E : EncodedAxisParallelRegion) (O : SelectedCoordinateOracles E)
      (N : RegionNormalization E.region) (A : LegacyNormalizationAdapter E N)
      (originalOracle : Oracle N.code),
    (∀ q, originalOracle.answer q = O.answer (toLegacyQuery A q)) →
    ∀ fuel,
      OracleProgram.evaluate O.answer (originalProgram N A fuel) =
        decisionThrough N.code
          (RuntimeRebase.rebaseOracle N.code.originVertex originalOracle) fuel := by
  intro E O N A originalOracle hO fuel
  rw [originalProgram, OracleProgram.evaluate_mapQuery]
  have hanswer :
      (fun q : Query N.code => O.answer (toLegacyQuery A
        (RuntimeRebase.rebaseQuery N.code.originVertex q))) =
        (RuntimeRebase.rebaseOracle N.code.originVertex originalOracle).answer := by
    funext q
    exact (hO (RuntimeRebase.rebaseQuery N.code.originVertex q)).symm
  rw [hanswer]
  exact decisionThroughProgram_evaluate N.code
    (RuntimeRebase.rebaseOracle N.code.originVertex originalOracle) fuel

theorem originalStagePrograms_evaluate :
    ∀ (E : EncodedAxisParallelRegion) (O : SelectedCoordinateOracles E)
      (N : RegionNormalization E.region) (A : LegacyNormalizationAdapter E N)
      (originalOracle : Oracle N.code),
    (∀ q, originalOracle.answer q = O.answer (toLegacyQuery A q)) →
    (∀ stage,
      OracleProgram.evaluate O.answer (originalPositiveProgram N A stage) =
        positiveStage N.code
          (RuntimeRebase.rebaseOracle N.code.originVertex originalOracle) stage) ∧
    (∀ stage,
      OracleProgram.evaluate O.answer (originalNegativeProgram N A stage) =
        negativeStage N.code
          (RuntimeRebase.rebaseOracle N.code.originVertex originalOracle) stage) := by
  intro E O N A originalOracle hO
  have hanswer :
      (fun q : Query N.code => O.answer (toLegacyQuery A
        (RuntimeRebase.rebaseQuery N.code.originVertex q))) =
        (RuntimeRebase.rebaseOracle N.code.originVertex originalOracle).answer := by
    funext q
    exact (hO (RuntimeRebase.rebaseQuery N.code.originVertex q)).symm
  constructor
  · intro stage
    rw [originalPositiveProgram, OracleProgram.evaluate_mapQuery, hanswer]
    exact positiveStageProgram_evaluate N.code
      (RuntimeRebase.rebaseOracle N.code.originVertex originalOracle) stage
  · intro stage
    rw [originalNegativeProgram, OracleProgram.evaluate_mapQuery, hanswer]
    exact negativeStageProgram_evaluate N.code
      (RuntimeRebase.rebaseOracle N.code.originVertex originalOracle) stage

theorem originalTileable_iff_normalized :
    ∀ (E : EncodedAxisParallelRegion) (N : RegionNormalization E.region),
      isPlaneTileable E ↔ realizationPlaneTileable N.normalized := by
  intro E N
  change (∃ S : Set Tiling.Plane, Tiling.AxisParallel.TilesOn E.region S Set.univ) ↔
    ∃ S : Set Tiling.Plane,
      Tiling.AxisParallel.TilesOn N.normalized.region S Set.univ
  exact (tileableNormalizedIff N).symm

theorem decisionThrough_sound :
    ∀ {C : RegionCode} (R : Realization C) (O : CorrectOracle C R) fuel answer,
      decisionThrough C O.toOracle fuel = some answer →
        (answer = true ↔ realizationPlaneTileable R) := by
  intro C R O fuel answer hdecision
  have hrun : runThrough (positiveStage C O.toOracle) (negativeStage C O.toOracle) fuel =
      some answer := by
    simpa [decisionThrough] using hdecision
  obtain ⟨n, hn, hstep, hnone⟩ :=
    (runThrough_some_iff (positiveStage C O.toOracle) (negativeStage C O.toOracle)
      fuel answer).mp hrun
  by_cases hp : positiveStage C O.toOracle n
  · have hanswer : answer = true := by
      simpa [dovetailStep, hp] using hstep
    subst answer
    constructor
    · intro _
      exact PositiveVerification.verifyPositiveStage_sound R O n (by
        simpa [positiveStage] using hp)
    · intro _
      trivial
  · have hnneg : negativeStage C O.toOracle n := by
      have hstep' := hstep
      simp [dovetailStep, hp] at hstep'
      by_cases hnneg' : negativeStage C O.toOracle n
      · exact hnneg'
      · simp [hnneg'] at hstep'
    have hanswer : answer = false := by
      simpa [dovetailStep, hp, hnneg] using hstep
    subst answer
    constructor
    · intro hfalse
      simp at hfalse
    · intro htile
      exact False.elim (negativeStage_sound R O n hnneg htile)


end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel
open Tiling.AxisParallel.Terminal.Executable
open Tiling.AxisParallel.Terminal.Executable.PositiveVerification
open Tiling.AxisParallel.Terminal.Executable.Semantics

structure NormalizedProgramPackage {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) where
  decision : RelativeDecision (Query C) O.toOracle.answer (realizationPlaneTileable R)
  positive_program : decision.positive.program = positiveStageProgram C
  negative_program : decision.negative.program = negativeStageProgram C
  decision_program : decision.decisionProgram = decisionThroughProgram C

structure OriginalRegionProgramPackage (K : Region) (N : RegionNormalization K)
    (O : Oracle N.code) where
  decision : RelativeDecision (Query N.code) O.answer
    (∃ S : Set Tiling.Plane, TilesOn K S Set.univ)
  positive_program : decision.positive.program = originalRegionPositiveProgram N
  negative_program : decision.negative.program = originalRegionNegativeProgram N
  decision_program : decision.decisionProgram = originalRegionDecisionProgram N

structure OriginalProgramPackage (E : EncodedAxisParallelRegion)
    (O : SelectedCoordinateOracles E) (N : RegionNormalization E.region)
    (A : LegacyNormalizationAdapter E N) where
  decision : RelativeDecision (CoordQuery E) O.answer (isPlaneTileable E)
  positive_program : decision.positive.program = originalPositiveProgram N A
  negative_program : decision.negative.program = originalNegativeProgram N A
  decision_program : decision.decisionProgram = originalProgram N A

theorem decisionThrough_halts :
    ∀ {C : RegionCode} (R : Realization C) (O : CorrectOracle C R),
      ∃ fuel answer, decisionThrough C O.toOracle fuel = some answer := by
  intro C R O
  have hstage : ∃ n, dovetailStep (positiveStage C O.toOracle)
      (negativeStage C O.toOracle) n ≠ none := by
    by_cases htile : realizationPlaneTileable R
    · obtain ⟨n, hn⟩ := PositiveCertificateCompleteness.positiveStage_complete R O htile
      refine ⟨n, ?_⟩
      simp [dovetailStep, positiveStage, hn]
    · obtain ⟨n, hn⟩ := negativeStage_complete R O htile
      refine ⟨n, ?_⟩
      by_cases hp : positiveStage C O.toOracle n
      · simp [dovetailStep, hp]
      · simp [dovetailStep, hp, hn]
  obtain ⟨fuel, hstage⟩ := hstage
  cases hrun : runThrough (positiveStage C O.toOracle) (negativeStage C O.toOracle) fuel with
  | none =>
      exact (hstage ((runThrough_none_iff (positiveStage C O.toOracle)
        (negativeStage C O.toOracle) fuel).mp hrun fuel (Nat.le_refl fuel))).elim
  | some answer =>
      exact ⟨fuel, answer, hrun⟩

/-- This exact code/fuel-indexed program eventually answers for every realization and
correct oracle, and every successful answer at every fuel decides that realization's
whole-plane tileability. -/
theorem decisionThroughProgram_correct :
    ∀ {C : RegionCode} (R : Realization C) (O : CorrectOracle C R),
      (∃ fuel answer, OracleProgram.evaluate O.toOracle.answer
        (decisionThroughProgram C fuel) = some answer) ∧
      ∀ fuel answer, OracleProgram.evaluate O.toOracle.answer
        (decisionThroughProgram C fuel) = some answer →
          (answer = true ↔ realizationPlaneTileable R) := by
  intro C R O
  simp_rw [decisionThroughProgram_evaluate]
  exact ⟨decisionThrough_halts R O, decisionThrough_sound R O⟩

theorem computedDecision_iff :
    ∀ {C : RegionCode} (R : Realization C) (O : CorrectOracle C R),
      (∃ fuel, ResolvesBy C O.toOracle fuel) ∧
      ∀ fuel, ResolvesBy C O.toOracle fuel →
        (computedDecisionAtFuel C O.toOracle fuel = true ↔ realizationPlaneTileable R) := by
  intro C R O
  obtain ⟨fuel, answer, hdecision⟩ := decisionThrough_halts R O
  refine ⟨⟨fuel, ?_⟩, ?_⟩
  · simp [ResolvesBy, hdecision]
  · intro fuel hresolved
    cases hdecision : decisionThrough C O.toOracle fuel with
    | none =>
        simp [ResolvesBy, hdecision] at hresolved
    | some answer =>
        simpa [computedDecisionAtFuel, hdecision] using
          decisionThrough_sound R O fuel answer hdecision

theorem normalizedProgramPackage :
    ∀ {C : RegionCode} (R : Realization C) (O : CorrectOracle C R),
      Nonempty (NormalizedProgramPackage R O) := by
  intro C R O
  let positive : RelativeSemidecision (Query C) O.toOracle.answer
      (realizationPlaneTileable R) :=
    { program := positiveStageProgram C
      sound := fun stage h => PositiveVerification.verifyPositiveStage_sound R O stage (by
        rw [positiveStageProgram_evaluate] at h
        exact h)
      complete := fun h => by
        obtain ⟨stage, hstage⟩ := PositiveCertificateCompleteness.positiveStage_complete R O h
        refine ⟨stage, ?_⟩
        rw [positiveStageProgram_evaluate]
        exact hstage }
  let negative : RelativeSemidecision (Query C) O.toOracle.answer
      (¬realizationPlaneTileable R) :=
    { program := negativeStageProgram C
      sound := fun stage h => negativeStage_sound R O stage (by
        rw [negativeStageProgram_evaluate] at h
        exact h)
      complete := fun h => by
        obtain ⟨stage, hstage⟩ := negativeStage_complete R O h
        refine ⟨stage, ?_⟩
        rw [negativeStageProgram_evaluate]
        exact hstage }
  let decision : RelativeDecision (Query C) O.toOracle.answer
      (realizationPlaneTileable R) :=
    { positive := positive
      negative := negative
      decisionProgram := decisionThroughProgram C
      true_sound := fun fuel h => by
        rw [decisionThroughProgram_evaluate] at h
        exact (decisionThrough_sound R O fuel true h).mp rfl
      false_sound := fun fuel h htile => by
        rw [decisionThroughProgram_evaluate] at h
        exact Bool.false_ne_true ((decisionThrough_sound R O fuel false h).mpr htile)
      halts := by
        obtain ⟨fuel, answer, hanswer⟩ := decisionThrough_halts R O
        refine ⟨fuel, answer, ?_⟩
        rw [decisionThroughProgram_evaluate]
        exact hanswer }
  exact ⟨{ decision := decision
           positive_program := rfl
           negative_program := rfl
           decision_program := rfl }⟩

theorem normalizedPositiveSemidecision :
    ∀ {C : RegionCode} (R : Realization C) (O : CorrectOracle C R),
      Nonempty (RelativeSemidecision (Query C) O.toOracle.answer
        (realizationPlaneTileable R)) := by
  intro C R O
  obtain ⟨package⟩ := normalizedProgramPackage R O
  exact ⟨package.decision.positive⟩

theorem normalizedNegativeSemidecision :
    ∀ {C : RegionCode} (R : Realization C) (O : CorrectOracle C R),
      Nonempty (RelativeSemidecision (Query C) O.toOracle.answer
        (¬ realizationPlaneTileable R)) := by
  intro C R O
  obtain ⟨package⟩ := normalizedProgramPackage R O
  exact ⟨package.decision.negative⟩

theorem normalizedRelativeDecision :
    ∀ {C : RegionCode} (R : Realization C) (O : CorrectOracle C R),
      Nonempty (RelativeDecision (Query C) O.toOracle.answer
        (realizationPlaneTileable R)) := by
  intro C R O
  obtain ⟨package⟩ := normalizedProgramPackage R O
  exact ⟨package.decision⟩

theorem arbitraryRegionRelativeDecision :
    ∀ (K : Region) (N : RegionNormalization K) (O : Oracle N.code),
      CorrectOriginalOracle N.originalVertex O →
        Nonempty (OriginalRegionProgramPackage K N O) := by
  intro K N O hO
  obtain ⟨CO, hCO⟩ := rebaseOracleCorrect N O hO
  obtain ⟨P⟩ := normalizedProgramPackage N.normalized CO
  have htileiff : realizationPlaneTileable N.normalized ↔
      ∃ S : Set Tiling.Plane, TilesOn K S Set.univ :=
    tileableNormalizedIff N
  have heval := originalRegionPrograms_evaluate N O
  have hpositive (stage : Nat) :
      OracleProgram.evaluate O.answer (originalRegionPositiveProgram N stage) =
        OracleProgram.evaluate CO.toOracle.answer (P.decision.positive.program stage) := by
    rw [P.positive_program, positiveStageProgram_evaluate, hCO]
    exact heval.1 stage
  have hnegative (stage : Nat) :
      OracleProgram.evaluate O.answer (originalRegionNegativeProgram N stage) =
        OracleProgram.evaluate CO.toOracle.answer (P.decision.negative.program stage) := by
    rw [P.negative_program, negativeStageProgram_evaluate, hCO]
    exact heval.2.1 stage
  have hdecision (fuel : Nat) :
      OracleProgram.evaluate O.answer (originalRegionDecisionProgram N fuel) =
        OracleProgram.evaluate CO.toOracle.answer (P.decision.decisionProgram fuel) := by
    rw [P.decision_program, decisionThroughProgram_evaluate, hCO]
    exact heval.2.2 fuel
  let positive : RelativeSemidecision (Query N.code) O.answer
      (∃ S : Set Tiling.Plane, TilesOn K S Set.univ) :=
    { program := originalRegionPositiveProgram N
      sound := fun stage hrun =>
        htileiff.mp (P.decision.positive.sound stage (by
          rw [← hpositive stage]
          exact hrun))
      complete := fun htile => by
        obtain ⟨stage, hstage⟩ := P.decision.positive.complete (htileiff.mpr htile)
        exact ⟨stage, by rw [hpositive stage]; exact hstage⟩ }
  let negative : RelativeSemidecision (Query N.code) O.answer
      (¬ ∃ S : Set Tiling.Plane, TilesOn K S Set.univ) :=
    { program := originalRegionNegativeProgram N
      sound := fun stage hrun htile =>
        P.decision.negative.sound stage (by
          rw [← hnegative stage]
          exact hrun) (htileiff.mpr htile)
      complete := fun hnotile => by
        obtain ⟨stage, hstage⟩ := P.decision.negative.complete
          (fun htile => hnotile (htileiff.mp htile))
        exact ⟨stage, by rw [hnegative stage]; exact hstage⟩ }
  let decision : RelativeDecision (Query N.code) O.answer
      (∃ S : Set Tiling.Plane, TilesOn K S Set.univ) :=
    { positive := positive
      negative := negative
      decisionProgram := originalRegionDecisionProgram N
      true_sound := fun fuel hrun =>
        htileiff.mp (P.decision.true_sound fuel (by
          rw [← hdecision fuel]
          exact hrun))
      false_sound := fun fuel hrun htile =>
        P.decision.false_sound fuel (by
          rw [← hdecision fuel]
          exact hrun) (htileiff.mpr htile)
      halts := by
        obtain ⟨fuel, answer, hrun⟩ := P.decision.halts
        exact ⟨fuel, answer, by rw [hdecision fuel]; exact hrun⟩ }
  exact ⟨{
    decision := decision
    positive_program := rfl
    negative_program := rfl
    decision_program := rfl }⟩

theorem existsNormalization_relativeDecision :
    ∀ K : Region, ∃ N : RegionNormalization K,
      ∀ (O : Oracle N.code), CorrectOriginalOracle N.originalVertex O →
        Nonempty (OriginalRegionProgramPackage K N O) := by
  intro K
  obtain ⟨N⟩ := existsRegionNormalization K
  exact ⟨N, arbitraryRegionRelativeDecision K N⟩

theorem originalProgramPackage :
    ∀ (E : EncodedAxisParallelRegion) (O : SelectedCoordinateOracles E),
      ∃ (N : RegionNormalization E.region) (A : LegacyNormalizationAdapter E N),
        Nonempty (OriginalProgramPackage E O N A) := by
  intro E O
  obtain ⟨N⟩ := existsRegionNormalization E.region
  obtain ⟨A⟩ := legacyAdapter_exists E N
  obtain ⟨originalOracle, hOriginal, hanswer⟩ := legacyQuery_answer E O N A
  obtain ⟨P⟩ := arbitraryRegionRelativeDecision E.region N originalOracle hOriginal
  have positiveEval : ∀ stage,
      OracleProgram.evaluate O.answer (originalPositiveProgram N A stage) =
        OracleProgram.evaluate originalOracle.answer
          (originalRegionPositiveProgram N stage) := by
    intro stage
    exact ((originalStagePrograms_evaluate E O N A originalOracle hanswer).1 stage).trans
      ((originalRegionPrograms_evaluate N originalOracle).1 stage).symm
  have negativeEval : ∀ stage,
      OracleProgram.evaluate O.answer (originalNegativeProgram N A stage) =
        OracleProgram.evaluate originalOracle.answer
          (originalRegionNegativeProgram N stage) := by
    intro stage
    exact ((originalStagePrograms_evaluate E O N A originalOracle hanswer).2 stage).trans
      ((originalRegionPrograms_evaluate N originalOracle).2.1 stage).symm
  have decisionEval : ∀ fuel,
      OracleProgram.evaluate O.answer (originalProgram N A fuel) =
        OracleProgram.evaluate originalOracle.answer
          (originalRegionDecisionProgram N fuel) := by
    intro fuel
    exact (originalProgram_evaluate E O N A originalOracle hanswer fuel).trans
      ((originalRegionPrograms_evaluate N originalOracle).2.2 fuel).symm
  let positive : RelativeSemidecision (CoordQuery E) O.answer (isPlaneTileable E) :=
    { program := originalPositiveProgram N A
      sound := by
        intro stage hrun
        apply P.decision.positive.sound stage
        rw [P.positive_program, ← positiveEval stage]
        exact hrun
      complete := by
        intro htile
        obtain ⟨stage, hstage⟩ := P.decision.positive.complete htile
        refine ⟨stage, ?_⟩
        rw [positiveEval stage, ← P.positive_program]
        exact hstage }
  let negative : RelativeSemidecision (CoordQuery E) O.answer (¬isPlaneTileable E) :=
    { program := originalNegativeProgram N A
      sound := by
        intro stage hrun
        apply P.decision.negative.sound stage
        rw [P.negative_program, ← negativeEval stage]
        exact hrun
      complete := by
        intro hnotile
        obtain ⟨stage, hstage⟩ := P.decision.negative.complete hnotile
        refine ⟨stage, ?_⟩
        rw [negativeEval stage, ← P.negative_program]
        exact hstage }
  let decision : RelativeDecision (CoordQuery E) O.answer (isPlaneTileable E) :=
    { positive := positive
      negative := negative
      decisionProgram := originalProgram N A
      true_sound := by
        intro fuel hrun
        apply P.decision.true_sound fuel
        rw [P.decision_program, ← decisionEval fuel]
        exact hrun
      false_sound := by
        intro fuel hrun
        apply P.decision.false_sound fuel
        rw [P.decision_program, ← decisionEval fuel]
        exact hrun
      halts := by
        obtain ⟨fuel, answer, hrun⟩ := P.decision.halts
        refine ⟨fuel, answer, ?_⟩
        rw [decisionEval fuel, ← P.decision_program]
        exact hrun }
  exact ⟨N, A, ⟨{ decision := decision
                  positive_program := rfl
                  negative_program := rfl
                  decision_program := rfl }⟩⟩

theorem exists_positiveSemidecision :
    ∀ (E : EncodedAxisParallelRegion) (O : SelectedCoordinateOracles E),
      Nonempty (RelativeSemidecision (CoordQuery E) O.answer (isPlaneTileable E)) := by
  intro E O
  obtain ⟨N, A, ⟨P⟩⟩ := originalProgramPackage E O
  exact ⟨P.decision.positive⟩

theorem exists_negativeSemidecision :
    ∀ (E : EncodedAxisParallelRegion) (O : SelectedCoordinateOracles E),
      Nonempty (RelativeSemidecision (CoordQuery E) O.answer (¬isPlaneTileable E)) := by
  intro E O
  obtain ⟨N, A, ⟨P⟩⟩ := originalProgramPackage E O
  exact ⟨P.decision.negative⟩

theorem axisParallelTileability_oracleDecidable :
    ∀ (E : EncodedAxisParallelRegion) (O : SelectedCoordinateOracles E),
      Nonempty (RelativeDecision (CoordQuery E) O.answer (isPlaneTileable E)) := by
  intro E O
  obtain ⟨N, A, ⟨P⟩⟩ := originalProgramPackage E O
  exact ⟨P.decision⟩

end Tiling.AxisParallel.Terminal
