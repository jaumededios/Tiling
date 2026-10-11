import AxisParallelComputabilityComparator.Definitions
import Tiling.AxisParallel.Decidability.AllInput
import Tiling.AxisParallel.Decidability.Oracle.NumericalPrefix
import Tiling.AxisParallel.Decidability.Oracle.Coefficients
import Tiling.AxisParallel.Decidability.Oracle.CornerSum
import Tiling.AxisParallel.Decidability.Rational

set_option autoImplicit false
set_option warningAsError true

namespace AxisParallelComputabilityComparator

open Tiling.AxisParallel.Decidability

private def rectangles {n : ℕ} (data : TileData n) : List (Plane × Plane) :=
  List.ofFn fun i => (data.1 i, data.2 i)

private theorem rectangles_length {n : ℕ} (data : TileData n) :
    (rectangles data).length = n := by simp [rectangles]

private theorem region_eq {n : ℕ} (data : TileData n) :
    (data : Set Plane) = interior (⋃ r ∈ rectangles data,
      Tiling.AxisParallel.SetFormulation.rectangle r.1 r.2) := by
  change interior (⋃ i, rectangle (data.1 i) (data.2 i)) = _
  congr 1
  ext z
  simp only [rectangles, List.mem_ofFn, Set.mem_iUnion, Prod.exists]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨data.1 i, data.2 i, ⟨i, rfl⟩, hi⟩
  · rintro ⟨a, b, ⟨i, he⟩, hz⟩
    cases he
    exact ⟨i, hz⟩

private theorem tiling_eq (Ω T : Set Plane) :
    Tiling Ω T ↔ Tiling.AxisParallel.SetFormulation.Tiles Ω T := Iff.rfl

/-- The uniform numerical-prefix implementation. -/
def oracleAlgorithm : OracleAlgorithm where
  decide := NumericalPrefix.decide AllInput.program OracleCoefficients.encodeQuery
  computable_decide := NumericalPrefix.decide_computable
    AllInput.program_computable OracleCoefficients.encodeQuery_computable₂

private theorem oracle_correct {n : ℕ} (data : TileData n)
    (comparison : OrderComparisons n) (hc : data.HasOrderComparisons comparison) :
    CorrectOracle (cornerList (rectangles data))
      (fun q => comparison.oracle (OracleCoefficients.encodeQuery n q)) := by
  intro axis left right
  have hlen : (cornerList (rectangles data)).length = 2*n := by
    rw [RectangleInput.cornerList_length, rectangles_length]
  have hs := OracleCoefficients.coefficients_sum_eq (cornerList (rectangles data)) n
    (axis, left, right) hlen
  have hs' := OracleCoefficients.corner_sum_eq n data
    (OracleCoefficients.coefficients n (axis, left, right)) axis
  simp only [rectangles] at hs
  rw [hs] at hs'
  fin_cases axis
  · simp only [OrderComparisons.oracle, OracleCoefficients.encodeQuery, Fin.zero_eta,
      Fin.isValue, ne_eq, not_true_eq_false, decide_false, Encodable.encodek,
      Bool.false_eq_true, ↓reduceIte]
    rw [hc.1]
    have he := hs'.symm
    simpa [cornerIndex, coordinate, rectangles, sub_nonneg] using
      (iff_of_eq (congrArg (fun x : ℝ => 0 ≤ x) he))
  · simp only [OrderComparisons.oracle, OracleCoefficients.encodeQuery, Fin.mk_one,
      Fin.isValue, ne_eq, one_ne_zero, not_false_eq_true, decide_true,
      Encodable.encodek, ↓reduceIte]
    rw [hc.2]
    have he := hs'.symm
    simpa [cornerIndex, coordinate, rectangles, sub_nonneg] using
      (iff_of_eq (congrArg (fun x : ℝ => 0 ≤ x) he))

theorem tiling_computable_relative :
    ∃ algorithm : OracleAlgorithm,
      ∀ n (data : TileData n) (comparison : OrderComparisons n),
        data.HasOrderComparisons comparison → ∀ answer,
          algorithm.Returns comparison answer ↔
            (answer = true ↔ ∃ T, Tiling (data : Set Plane) T) := by
  refine ⟨oracleAlgorithm, ?_⟩
  intro n data comparison hc answer
  have ha := oracle_correct data comparison hc
  obtain ⟨⟨fuel, verdict, hv⟩, hs⟩ := AllInput.program_correct ha
  rw [rectangles_length] at hv hs
  change answer ∈ Nat.rfindOpt (fun k => NumericalPrefix.decide AllInput.program
    OracleCoefficients.encodeQuery (n, (List.range k).map comparison.oracle)) ↔ _
  rw [NumericalPrefix.returns_iff]
  constructor
  · rintro ⟨fuel, hf⟩
    have ht := hs fuel answer hf
    simpa only [← region_eq data, ← tiling_eq] using ht
  · intro ht
    have ht' : answer = true ↔ ∃ T, Tiling.AxisParallel.SetFormulation.Tiles
        (interior (⋃ r ∈ rectangles data,
          Tiling.AxisParallel.SetFormulation.rectangle r.1 r.2)) T := by
      simpa only [← region_eq data, ← tiling_eq] using ht
    have hv' := hs fuel verdict hv
    have he : answer = verdict := by
      cases answer <;> cases verdict <;> simp_all
    exact ⟨fuel, he.symm ▸ hv⟩

theorem rational_tiling_computable :
    ComputablePred (fun R : List ((ℚ × ℚ) × (ℚ × ℚ)) =>
      ∃ T, Tiling (interior (⋃ r ∈ R,
        rectangle ⟨r.1.1, r.1.2⟩ ⟨r.2.1, r.2.2⟩)) T) :=
  RationalDecision.rational_tiling_computable

end AxisParallelComputabilityComparator
