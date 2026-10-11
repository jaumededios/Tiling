import Mathlib

/-!
# Intrinsic vocabulary for the independent geometric challenge

The definitions below agree with the frozen Mathlib-only challenge.
-/

set_option autoImplicit false

open Bornology MeasureTheory Set Submodule TopologicalSpace
open scoped Pointwise Topology

namespace AxisParallelComparator

abbrev Plane := ℂ

def Packing (Ω T : Set Plane) : Prop :=
  T.Pairwise fun s t ↦ volume ((s +ᵥ Ω) ∩ (t +ᵥ Ω)) = 0

def CoversExactly (E Ω T : Set Plane) : Prop := E =ᵐ[volume] T +ᵥ Ω

def TilingOn (E Ω T : Set Plane) : Prop :=
  T.Countable ∧ Packing Ω T ∧ CoversExactly E Ω T

def Tiling (Ω T : Set Plane) : Prop := TilingOn univ Ω T

def coveredRegion (Ω T : Set Plane) : Set Plane :=
  interior (closure (T +ᵥ Ω))

def IsPeriod (A : Set Plane) (p : Plane) : Prop := p +ᵥ A = A

def IsDoublyPeriodic (A : Set Plane) : Prop :=
  ∃ p q, LinearIndependent ℝ ![p, q] ∧ IsPeriod A p ∧ IsPeriod A q

def WeaklyPeriodic (A : Set Plane) : Prop :=
  ∃ P : Finpartition A, ∀ S ∈ P.parts, ∃ p, p ≠ 0 ∧ IsPeriod S p

def QuasiPeriodic (A : Set Plane) : Prop :=
  ∃ P : Finpartition A, ∀ S ∈ P.parts, IsDoublyPeriodic S

abbrev e₁ : Plane := ⟨1, 0⟩

abbrev e₂ : Plane := ⟨0, 1⟩

abbrev p₁ (z : Plane) : ℝ := z.re

abbrev p₂ (z : Plane) : ℝ := z.im

def IsRegularOpen {X : Type*} [TopologicalSpace X] (U : Set X) : Prop :=
  interior (closure U) = U

def IsAxisParallelTile (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ IsBounded Ω ∧ IsRegularOpen Ω ∧
    ∃ edges : Finset (Plane × Plane),
      (∀ e ∈ edges, p₁ e.1 = p₁ e.2 ∨ p₂ e.1 = p₂ e.2) ∧
      frontier Ω = ⋃ e ∈ edges, segment ℝ e.1 e.2

def HasFiniteLocalComplexity {V : Type*} [NormedAddCommGroup V] (T : Set V) : Prop :=
  ∀ B, IsBounded B → ((T - T) ∩ B).Finite

def hit (U : Set Plane) : Set (Closeds Plane) :=
  {F | ((F : Set Plane) ∩ U).Nonempty}

def miss (K : Set Plane) : Set (Closeds Plane) :=
  {F | Disjoint (F : Set Plane) K}

abbrev fellTopology : TopologicalSpace (Closeds Plane) :=
  TopologicalSpace.generateFrom
    ((hit '' {U : Set Plane | IsOpen U}) ∪ (miss '' {K : Set Plane | IsCompact K}))

def orbitHullUnder (G T : Set Plane) : Set (Closeds Plane) :=
  closure[fellTopology] {S | ∃ p ∈ G, (S : Set Plane) = p +ᵥ T}

def orbitHull (E T : Set Plane) : Set (Closeds Plane) :=
  orbitHullUnder {p | IsPeriod E p} T

def IsMinimal (E T : Set Plane) : Prop :=
  IsClosed T ∧ ∀ S ∈ orbitHull E T, orbitHull E S = orbitHull E T

def IsInvariantAlong (E : Set Plane) (v : Plane) : Prop :=
  ∀ r : ℝ, IsPeriod E (r • v)

def lineFibre (v : Plane) (T : Set Plane) (t : Plane) : Set Plane :=
  T ∩ (t +ᵥ (span ℝ {v} : Set Plane))

def columnPart (Ω : Set Plane) (v : Plane) (T : Set Plane) : Set Plane :=
  {t ∈ T | IsInvariantAlong (coveredRegion Ω (lineFibre v T t)) v}

def IsEarthquakeComponent (Ω : Set Plane) (v : Plane) (T S : Set Plane) : Prop :=
  S.Nonempty ∧ S ⊆ T ∧ IsInvariantAlong (coveredRegion Ω S) v ∧
    ∀ R, R.Nonempty → R ⊆ S → IsInvariantAlong (coveredRegion Ω R) v → R = S

def tectonicPlates (Ω : Set Plane) (v : Plane) (T : Set Plane) : Set (Set Plane) :=
  {S | IsEarthquakeComponent Ω v T S ∧ S ⊆ T \ columnPart Ω v T}

def IsEarthquakeSplit (Ω S S₀ S₁ : Set Plane) (v : Plane) : Prop :=
  S₀.Nonempty ∧ S₁.Nonempty ∧ Disjoint S₀ S₁ ∧ S₀ ∪ S₁ = S ∧
    IsInvariantAlong (coveredRegion Ω S₀) v ∧ IsInvariantAlong (coveredRegion Ω S₁) v

def vertices (Ω : Set Plane) : Set Plane :=
  {v ∈ frontier Ω | ∀ ε > 0,
    (∃ a ∈ frontier Ω ∩ Metric.ball v ε, p₁ a ≠ p₁ v) ∧
    (∃ b ∈ frontier Ω ∩ Metric.ball v ε, p₂ b ≠ p₂ v)}

end AxisParallelComparator
