import Mathlib

/- Exact specification definitions, shared in name and body with the independent Challenge. -/

set_option autoImplicit false

open Bornology MeasureTheory Set Submodule TopologicalSpace
open scoped Pointwise Topology

namespace AxisParallelComputabilityComparator

abbrev Plane := ℂ

def Packing (Ω T : Set Plane) : Prop :=
  T.Pairwise fun s t ↦ volume ((s +ᵥ Ω) ∩ (t +ᵥ Ω)) = 0

def CoversExactly (E Ω T : Set Plane) : Prop := E =ᵐ[volume] T +ᵥ Ω

def TilingOn (E Ω T : Set Plane) : Prop :=
  T.Countable ∧ Packing Ω T ∧ CoversExactly E Ω T

def Tiling (Ω T : Set Plane) : Prop := TilingOn univ Ω T

abbrev p₁ (z : Plane) : ℝ := z.re
abbrev p₂ (z : Plane) : ℝ := z.im

def rectangle (a b : Plane) : Set Plane :=
  p₁ ⁻¹' Icc (p₁ a) (p₁ b) ∩ p₂ ⁻¹' Icc (p₂ a) (p₂ b)

abbrev TileData (n : ℕ) := (Fin n → Plane) × (Fin n → Plane)

def TileData.region {n : ℕ} (data : TileData n) : Set Plane :=
  interior (⋃ i, rectangle (data.1 i) (data.2 i))

instance {n : ℕ} : CoeTC (TileData n) (Set Plane) := ⟨TileData.region⟩

abbrev CornerWeights (n : ℕ) := Fin n × Fin 2 → ℤ

abbrev OrderComparison (n : ℕ) := CornerWeights n → Bool

structure OrderComparisons (n : ℕ) where
  horizontal : OrderComparison n
  vertical : OrderComparison n

def TileData.HasOrderComparisons {n : ℕ} (data : TileData n)
    (comparison : OrderComparisons n) : Prop :=
  (∀ a, comparison.horizontal a = true ↔
    0 ≤ ∑ i, (a (i, 0) • p₁ (data.1 i) + a (i, 1) • p₁ (data.2 i))) ∧
  (∀ a, comparison.vertical a = true ↔
    0 ≤ ∑ i, (a (i, 0) • p₂ (data.1 i) + a (i, 1) • p₂ (data.2 i)))

structure OracleAlgorithm where
  decide : ℕ × List Bool → Option Bool
  computable_decide : Computable decide

def cornerIndex {n : ℕ} (v : Fin n × Fin 2) : ℕ := 2 * v.1.val + v.2.val

def OrderComparisons.oracle {n : ℕ} (comparison : OrderComparisons n) : ℕ → Bool :=
  fun code => match Encodable.decode (α := Bool × List ℤ) code with
    | none => false
    | some (vertical, coefficients) =>
      (if vertical then comparison.vertical else comparison.horizontal)
        (fun v => coefficients.getD (cornerIndex v) 0)

def OracleAlgorithm.Returns {n : ℕ} (algorithm : OracleAlgorithm)
    (comparison : OrderComparisons n) (answer : Bool) : Prop :=
  answer ∈ Nat.rfindOpt (fun k =>
    algorithm.decide (n, (List.range k).map comparison.oracle))

end AxisParallelComputabilityComparator
