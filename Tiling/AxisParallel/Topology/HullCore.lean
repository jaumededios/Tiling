import Tiling.AxisParallel.Core
import Tiling.AxisParallel.Topology.FellCore
import Mathlib.Topology.Metrizable.Basic

set_option linter.style.header false

/-!
# Fixed-carrier tiling-hull definitions

This module contains the fixed-carrier tiling space, its essential-stabilizer action, and the
native Fell/hull vocabulary.  Its metric is pulled back from the Hausdorff metric on compactified
closed centre sets.
-/

open Function MeasureTheory Metric Set
open scoped BigOperators Pointwise Topology

namespace Tiling.AxisParallel.Topology

/-- A closed set of centres which tiles the fixed carrier `E` by `K`. -/
structure TilingSpace
    (K : Tiling.AxisParallel.Region) (E : Set Tiling.Plane) where
  centres : TopologicalSpace.Closeds Tiling.Plane
  tilesOn : Tiling.AxisParallel.TilesOn K (centres : Set Tiling.Plane) E

/-- Translate a fixed-carrier tiling by an essential period of the carrier. -/
def TilingSpace.translate
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (g : Tiling.AxisParallel.aePeriodGroup E)
    (T : TilingSpace K E) : TilingSpace K E where
  centres :=
    ⟨(fun x => x + (g : Tiling.Plane)) '' (T.centres : Set Tiling.Plane),
      (Homeomorph.addRight (g : Tiling.Plane)).isClosed_image.mpr T.centres.isClosed⟩
  tilesOn := by
    let u : Tiling.Plane := g
    let S : Set Tiling.Plane := T.centres
    let S' : Set Tiling.Plane := (fun x => x + u) '' S
    change Tiling.AxisParallel.TilesOn K S' E
    refine ⟨T.tilesOn.1.image (fun x => x + u), ?_, ?_⟩
    · intro p hp q hq hpq
      rcases p with ⟨p, _⟩
      rcases q with ⟨q, _⟩
      change p ∈ S' at hp
      change q ∈ S' at hq
      rcases hp with ⟨s, hs, rfl⟩
      rcases hq with ⟨t, ht, rfl⟩
      have hst : s ≠ t := by
        intro hst
        apply hpq
        simp [hst]
      have had := T.tilesOn.2.1
        (show (s, ()) ∈ K.toPolygonalRegion.placements S from hs)
        (show (t, ()) ∈ K.toPolygonalRegion.placements S from ht)
        (show (s, ()) ≠ (t, ()) by simpa using hst)
      change AEDisjoint volume (s +ᵥ K.support) (t +ᵥ K.support) at had
      change AEDisjoint volume ((s + u) +ᵥ K.support) ((t + u) +ᵥ K.support)
      rw [MeasureTheory.AEDisjoint] at had ⊢
      rw [show (((s + u) +ᵥ K.support) ∩ ((t + u) +ᵥ K.support)) =
          u +ᵥ ((s +ᵥ K.support) ∩ (t +ᵥ K.support)) by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_vadd_set]
        constructor
        · rintro ⟨⟨a, ha, hax⟩, b, hb, hbx⟩
          refine ⟨-u + x, ⟨?_, ?_⟩, ?_⟩
          · refine ⟨a, ha, ?_⟩
            simp only [vadd_eq_add] at hax ⊢
            rw [← hax]
            abel
          · refine ⟨b, hb, ?_⟩
            simp only [vadd_eq_add] at hbx ⊢
            rw [← hbx]
            abel
          · simp only [vadd_eq_add]
            abel
        · rintro ⟨y, ⟨⟨a, ha, hay⟩, b, hb, hby⟩, hyx⟩
          constructor
          · refine ⟨a, ha, ?_⟩
            simp only [vadd_eq_add] at hay hyx ⊢
            calc
              s + u + a = u + (s + a) := by abel
              _ = u + y := by rw [hay]
              _ = x := hyx
          · refine ⟨b, hb, ?_⟩
            simp only [vadd_eq_add] at hby hyx ⊢
            calc
              t + u + b = u + (t + b) := by abel
              _ = u + y := by rw [hby]
              _ = x := hyx]
      simpa only [MeasureTheory.measure_vadd] using had
    · have hcover :=
        (MeasureTheory.quasiMeasurePreserving_add_right volume (-u)).ae T.tilesOn.2.2
      have hcarrier : (u +ᵥ E : Set Tiling.Plane) =ᵐ[volume] E := g.property
      filter_upwards [hcover, hcarrier] with x hxcover hxcarrier
      have hcarrier' : x ∈ E ↔ x - u ∈ E := by
        constructor
        · intro hx
          have hx' : x ∈ u +ᵥ E := hxcarrier.mpr hx
          rcases hx' with ⟨y, hy, hyx⟩
          have hxy : x - u = y := by
            simp only [vadd_eq_add] at hyx
            rw [← hyx]
            abel
          rwa [hxy]
        · intro hx
          apply hxcarrier.mp
          refine ⟨x - u, hx, ?_⟩
          simp only [vadd_eq_add]
          abel
      have hxcover' : x - u ∈ E ↔
          ∃ s : S, x - u ∈ (s : Tiling.Plane) +ᵥ K.openCarrier := by
        simpa only [sub_eq_add_neg, Tiling.AxisParallel.Region.openCarrier] using hxcover
      rw [hcarrier', hxcover']
      constructor
      · rintro ⟨s, hs⟩
        rcases hs with ⟨y, hy, hyx⟩
        refine ⟨⟨s + u, ⟨s, s.2, rfl⟩⟩, ?_⟩
        refine ⟨y, hy, ?_⟩
        simp only [vadd_eq_add] at hyx ⊢
        calc
          (s : Tiling.Plane) + u + y = ((s : Tiling.Plane) + y) + u := by abel
          _ = (x - u) + u := by rw [hyx]
          _ = x := sub_add_cancel x u
      · rintro ⟨s, hs⟩
        rcases s.2 with ⟨t, ht, hts⟩
        change t + u = (s : Tiling.Plane) at hts
        rcases hs with ⟨y, hy, hyx⟩
        refine ⟨⟨t, ht⟩, y, hy, ?_⟩
        simp only [vadd_eq_add] at hyx ⊢
        calc
          t + y = (t + u + y) - u := by abel
          _ = ((s : Tiling.Plane) + y) - u := by rw [hts]
          _ = x - u := by rw [hyx]

/-- The essential carrier stabilizer acts on the fixed-carrier tiling space by translation. -/
noncomputable instance TilingSpace.instAddAction
    (K : Tiling.AxisParallel.Region) (E : Set Tiling.Plane) :
    AddAction (Tiling.AxisParallel.aePeriodGroup E) (TilingSpace K E) where
  vadd := TilingSpace.translate
  zero_vadd T := by
    cases T with
    | mk centres tilesOn =>
        change TilingSpace.translate (0 : Tiling.AxisParallel.aePeriodGroup E)
          ⟨centres, tilesOn⟩ = ⟨centres, tilesOn⟩
        rw [TilingSpace.mk.injEq]
        apply TopologicalSpace.Closeds.ext
        ext x
        change x ∈ (fun y : Tiling.Plane => y + 0) '' (centres : Set Tiling.Plane) ↔
          x ∈ (centres : Set Tiling.Plane)
        simp
  add_vadd g h T := by
    cases T with
    | mk centres tilesOn =>
        change TilingSpace.translate (g + h) ⟨centres, tilesOn⟩ =
          TilingSpace.translate g (TilingSpace.translate h ⟨centres, tilesOn⟩)
        rw [TilingSpace.mk.injEq]
        apply TopologicalSpace.Closeds.ext
        ext x
        change x ∈ (fun y : Tiling.Plane => y + ((g + h :
            Tiling.AxisParallel.aePeriodGroup E) : Tiling.Plane)) ''
              (centres : Set Tiling.Plane) ↔
          x ∈ (fun y : Tiling.Plane => y + (g : Tiling.Plane)) ''
            ((fun y : Tiling.Plane => y + (h : Tiling.Plane)) ''
              (centres : Set Tiling.Plane))
        constructor
        · rintro ⟨y, hy, rfl⟩
          refine ⟨y + (h : Tiling.Plane), ⟨y, hy, rfl⟩, ?_⟩
          rw [AddSubgroup.coe_add]
          abel_nf
        · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
          refine ⟨y, hy, ?_⟩
          rw [AddSubgroup.coe_add]
          simp only [add_left_comm, add_comm]

/-- The jointly packaged stabilizer action. -/
def TilingSpace.translationAction
    (K : Tiling.AxisParallel.Region) (E : Set Tiling.Plane) :
    Tiling.AxisParallel.aePeriodGroup E × TilingSpace K E → TilingSpace K E :=
  fun p => TilingSpace.translate p.1 p.2

/-- Forget the proof fields of a sequence of fixed-carrier tilings. -/
def TilingSpace.centresSequence
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (T : ℕ → TilingSpace K E) : ℕ → Set Tiling.Plane :=
  fun n => T n |>.centres

/-- Translate one tiling by a sequence of essential carrier periods. -/
def TilingSpace.translateSequence
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (g : ℕ → Tiling.AxisParallel.aePeriodGroup E)
    (T : TilingSpace K E) : ℕ → TilingSpace K E :=
  fun n => T.translate (g n)

/-- Coerce a sequence of essential carrier periods to planar translation vectors. -/
def carrierTranslationSequence
    {E : Set Tiling.Plane}
    (g : ℕ → Tiling.AxisParallel.aePeriodGroup E) : ℕ → Tiling.Plane :=
  fun n => g n

/-- Sum a function over a set, using the subtype as the index type. -/
noncomputable def pointSum
    (F : Tiling.Plane → ℝ) (S : Set Tiling.Plane) : ℝ :=
  ∑' s : S, F s

/-- The Fell metric on fixed-carrier tilings, pulled back through compactification of their closed
centre sets. -/
noncomputable instance TilingSpace.instMetricSpace
    (K : Tiling.AxisParallel.Region) (E : Set Tiling.Plane) :
    MetricSpace (TilingSpace K E) := by
  letI : MetricSpace (OnePoint Tiling.Plane) := by
    let e : OnePoint Tiling.Plane ≃ₜ
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      onePointEquivSphereOfFinrankEq (ι := Fin 3) (V := Tiling.Plane)
        (by norm_num [Tiling.Plane, Complex.finrank_real_complex])
    exact e.isEmbedding.comapMetricSpace
  let embedding : TilingSpace K E →
      TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) := fun T =>
    fellCompactification (T.centres : Set Tiling.Plane) T.centres.isClosed
  exact MetricSpace.induced embedding (by
    intro T U h
    have hc : T.centres = U.centres := by
      apply TopologicalSpace.Closeds.ext
      ext x
      have hx := congrArg
        (fun C : TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) =>
          (x : OnePoint Tiling.Plane) ∈ (C : Set (OnePoint Tiling.Plane))) h
      simpa [embedding, fellCompactification, Tiling.Topology.fellCompactification] using hx
    cases T
    cases U
    simp_all) inferInstance

/-- The closure of the essential-stabilizer orbit of a fixed-carrier tiling. -/
def orbitHull
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (T : TilingSpace K E) : Set (TilingSpace K E) :=
  closure (AddAction.orbit (Tiling.AxisParallel.aePeriodGroup E) T)

/-- A nonempty closed invariant family in which every member has dense stabilizer orbit. -/
def IsTopologicallyMinimal
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (Y : Set (TilingSpace K E)) : Prop :=
  Y.Nonempty ∧ IsClosed Y ∧
    (∀ g : Tiling.AxisParallel.aePeriodGroup E,
      TilingSpace.translate g '' Y = Y) ∧
    ∀ T ∈ Y,
      closure (AddAction.orbit (Tiling.AxisParallel.aePeriodGroup E) T) = Y

end Tiling.AxisParallel.Topology
