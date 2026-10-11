import Mathlib

/-!
# Tilings, periods, and rectangle tiles as ordinary sets

This set-based vocabulary connects the native `Region` development to statements
about subsets of the plane. `IsRectangleTile` records the finite rectangle
presentation; it is distinct from a choice of finite boundary input.
-/

set_option autoImplicit false

open Bornology MeasureTheory Set Submodule TopologicalSpace
open scoped Pointwise Topology

namespace Tiling.AxisParallel.SetFormulation

abbrev Plane := ℂ

def Packing (Ω T : Set Plane) : Prop :=
  T.Pairwise fun s t ↦ volume ((s +ᵥ Ω) ∩ (t +ᵥ Ω)) = 0

def CoversExactly (E Ω T : Set Plane) : Prop := E =ᵐ[volume] T +ᵥ Ω

def TilingOn (E Ω T : Set Plane) : Prop :=
  T.Countable ∧ Packing Ω T ∧ CoversExactly E Ω T

def Tiles (Ω T : Set Plane) : Prop := TilingOn univ Ω T

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

def rectangle (a b : Plane) : Set Plane :=
  p₁ ⁻¹' Icc (p₁ a) (p₁ b) ∩ p₂ ⁻¹' Icc (p₂ a) (p₂ b)

def IsRegularOpen {X : Type*} [TopologicalSpace X] (U : Set X) : Prop :=
  interior (closure U) = U

def IsRectangleTile (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ ∃ rectangles : Finset (Plane × Plane),
    Ω = interior (⋃ r ∈ rectangles, rectangle r.1 r.2)

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

def RectanglePresentation (R : List (Plane × Plane)) (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ Ω = interior (⋃ r ∈ R, rectangle r.1 r.2)

end Tiling.AxisParallel.SetFormulation
