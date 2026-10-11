import Tiling.AxisParallel.Foundations.NoProperVertexStabilizer
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.WeakTilingTopology

/-!
# Persistent and transient slabs in a weak limit

The limit centre set is divided according to eventual exact membership along a common
subsequence.  Local cancellation rules out transient corners; regular-open support classification
then supplies a common slab direction and saturation by continuous plates.
-/

open Set
open MeasureTheory
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Continuous

/-- A limit tiling split into centres which eventually persist exactly and centres which are
eventually absent, together with their common slab orientation. -/
structure PersistentTransientSplit
    (K : Tiling.AxisParallel.Region) (X : Set ℝ)
    (T : ℕ → Tiling.AxisParallel.Topology.TilingSpace K
      {z : Tiling.Plane | z.re ∈ X})
    (S : Tiling.AxisParallel.Topology.TilingSpace K
      {z : Tiling.Plane | z.re ∈ X}) where
  persistent : Set Tiling.Plane
  transient : Set Tiling.Plane
  persistent_subset : persistent ⊆ (S.centres : Set Tiling.Plane)
  transient_subset : transient ⊆ (S.centres : Set Tiling.Plane)
  disjoint : Disjoint persistent transient
  union_eq : persistent ∪ transient = (S.centres : Set Tiling.Plane)
  persistent_eventuallyMem : ∀ a ∈ persistent, ∀ᶠ n : ℕ in Filter.atTop,
    a ∈ ((T n).centres : Set Tiling.Plane)
  transient_eventuallyNotMem : ∀ b ∈ transient, ∀ᶠ n : ℕ in Filter.atTop,
    b ∉ ((T n).centres : Set Tiling.Plane)
  orientation : Tiling.AxisParallel.Axis
  persistentBase : Set ℝ
  transientBase : Set ℝ
  persistentBase_open : IsOpen persistentBase
  transientBase_open : IsOpen transientBase
  persistentBase_regular : interior (closure persistentBase) = persistentBase
  transientBase_regular : interior (closure transientBase) = transientBase
  persistentSupport_vertical : orientation = Tiling.AxisParallel.Axis.vertical →
    Tiling.AxisParallel.regularSupport K persistent =
      {z : Tiling.Plane | z.re ∈ persistentBase}
  transientSupport_vertical : orientation = Tiling.AxisParallel.Axis.vertical →
    Tiling.AxisParallel.regularSupport K transient =
      {z : Tiling.Plane | z.re ∈ transientBase}
  persistentSupport_horizontal : orientation = Tiling.AxisParallel.Axis.horizontal →
    Tiling.AxisParallel.regularSupport K persistent =
      {z : Tiling.Plane | z.im ∈ persistentBase}
  transientSupport_horizontal : orientation = Tiling.AxisParallel.Axis.horizontal →
    Tiling.AxisParallel.regularSupport K transient =
      {z : Tiling.Plane | z.im ∈ transientBase}
  horizontal_requires_plane : orientation = Tiling.AxisParallel.Axis.horizontal → X = Set.univ
  verticalPersistent_plateSaturated : orientation = Tiling.AxisParallel.Axis.vertical →
    ∀ P : Tiling.AxisParallel.Continuous.VerticalPlate K
        (S.centres : Set Tiling.Plane),
      (P.centres ∩ persistent).Nonempty → P.centres ⊆ persistent
  verticalTransient_plateSaturated : orientation = Tiling.AxisParallel.Axis.vertical →
    ∀ P : Tiling.AxisParallel.Continuous.VerticalPlate K
        (S.centres : Set Tiling.Plane),
      (P.centres ∩ transient).Nonempty → P.centres ⊆ transient
  horizontalPersistent_plateSaturated : orientation = Tiling.AxisParallel.Axis.horizontal →
    ∀ P : Tiling.AxisParallel.Continuous.VerticalPlate K.coordinateSwap
      (Tiling.AxisParallel.coordinateSwap '' (S.centres : Set Tiling.Plane)),
      (P.centres ∩ (Tiling.AxisParallel.coordinateSwap '' persistent)).Nonempty →
        P.centres ⊆ Tiling.AxisParallel.coordinateSwap '' persistent
  horizontalTransient_plateSaturated : orientation = Tiling.AxisParallel.Axis.horizontal →
    ∀ P : Tiling.AxisParallel.Continuous.VerticalPlate K.coordinateSwap
      (Tiling.AxisParallel.coordinateSwap '' (S.centres : Set Tiling.Plane)),
      (P.centres ∩ (Tiling.AxisParallel.coordinateSwap '' transient)).Nonempty →
        P.centres ⊆ Tiling.AxisParallel.coordinateSwap '' transient

/-- A countable limit centre set admits one subsequence deciding exact membership eventually for
every limit centre. -/
theorem exists_exactMembershipSubsequence
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (_hXnonempty : X.Nonempty) (_hXopen : IsOpen X)
    (_hXregular : interior (closure X) = X)
    (T : ℕ → Tiling.AxisParallel.Topology.TilingSpace K
      {z : Tiling.Plane | z.re ∈ X})
    (S : Tiling.AxisParallel.Topology.TilingSpace K
      {z : Tiling.Plane | z.re ∈ X})
    (_hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence T)
      (S.centres : Set Tiling.Plane)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ s ∈ (S.centres : Set Tiling.Plane),
        (∀ᶠ n : ℕ in Filter.atTop,
          s ∈ ((T (phi n)).centres : Set Tiling.Plane)) ∨
        (∀ᶠ n : ℕ in Filter.atTop,
          s ∉ ((T (phi n)).centres : Set Tiling.Plane)) := by
  classical
  let _ : Countable ↥S.centres := S.tilesOn.1.to_subtype
  let code : ℕ → (↥S.centres → Bool) := fun n s ↦
    decide (s.1 ∈ ((T n).centres : Set Tiling.Plane))
  obtain ⟨limit, phi, hphi, hcode⟩ := CompactSpace.tendsto_subseq code
  refine ⟨phi, hphi, ?_⟩
  intro s hs
  let s' : ↥S.centres := ⟨s, hs⟩
  have hcoordinate : Filter.Tendsto
      (fun n ↦ code (phi n) s') Filter.atTop (nhds (limit s')) :=
    (tendsto_pi_nhds.mp hcode) s'
  have heventually : ∀ᶠ n : ℕ in Filter.atTop,
      code (phi n) s' = limit s' := by
    simpa [nhds_discrete, Filter.tendsto_pure] using hcoordinate
  cases hlimit : limit s' with
  | false =>
      right
      filter_upwards [heventually] with n hn
      simp only [hlimit, code, decide_eq_false_iff_not] at hn
      exact hn
  | true =>
      left
      filter_upwards [heventually] with n hn
      simp only [hlimit, code, decide_eq_true_eq] at hn
      exact hn

/-- The exact-membership subsequence determines a literal partition of the limit centres into
eventually present and eventually absent points.  This is the set-theoretic part of a
`PersistentTransientSplit`, before the common slab geometry is imposed. -/
theorem exists_eventualMembershipPartition
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    (T : ℕ → Tiling.AxisParallel.Topology.TilingSpace K
      {z : Tiling.Plane | z.re ∈ X})
    (S : Tiling.AxisParallel.Topology.TilingSpace K
      {z : Tiling.Plane | z.re ∈ X})
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence T)
      (S.centres : Set Tiling.Plane)) :
    ∃ (phi : ℕ → ℕ) (A B : Set Tiling.Plane),
      StrictMono phi ∧
      A ⊆ (S.centres : Set Tiling.Plane) ∧
      B ⊆ (S.centres : Set Tiling.Plane) ∧
      Disjoint A B ∧
      A ∪ B = (S.centres : Set Tiling.Plane) ∧
      (∀ a ∈ A, ∀ᶠ n : ℕ in Filter.atTop,
        a ∈ ((T (phi n)).centres : Set Tiling.Plane)) ∧
      (∀ b ∈ B, ∀ᶠ n : ℕ in Filter.atTop,
        b ∉ ((T (phi n)).centres : Set Tiling.Plane)) := by
  obtain ⟨phi, hphi, hdecision⟩ := exists_exactMembershipSubsequence
    hXnonempty hXopen hXregular T S hconv
  let A : Set Tiling.Plane :=
    {s | s ∈ (S.centres : Set Tiling.Plane) ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        s ∈ ((T (phi n)).centres : Set Tiling.Plane)}
  let B : Set Tiling.Plane := (S.centres : Set Tiling.Plane) \ A
  refine ⟨phi, A, B, hphi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact ha.1
  · intro b hb
    exact hb.1
  · exact disjoint_sdiff_right
  · ext s
    simp only [A, B, mem_union, mem_ofPred_eq, mem_sdiff]
    tauto
  · intro a ha
    exact ha.2
  · intro b hb
    rcases hdecision b hb.1 with hbPresent | hbAbsent
    · exact (hb.2 ⟨hb.1, hbPresent⟩).elim
    · exact hbAbsent

private theorem open_subset_closure_of_ae_subset
    {U V : Set Tiling.Plane} (hU : IsOpen U)
    (hUV : ∀ᵐ x ∂MeasureTheory.volume, x ∈ U → x ∈ V) : U ⊆ closure V := by
  intro x hx
  by_contra hxV
  let W := U ∩ (closure V)ᶜ
  have hWopen : IsOpen W := hU.inter isClosed_closure.isOpen_compl
  have hxW : x ∈ W := ⟨hx, hxV⟩
  have hWzero : MeasureTheory.volume W = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr (hUV.mono fun y hy hyW ↦
      hyW.2 (subset_closure (hy hyW.1)))
  exact hWopen.measure_ne_zero MeasureTheory.volume ⟨x, hxW⟩ hWzero

private theorem eventually_mem_of_finite_relevant
    {A Q : Set Tiling.Plane} {C : ℕ → Set Tiling.Plane}
    (hfinite : (A ∩ Q).Finite)
    (hA : ∀ a ∈ A, ∀ᶠ n : ℕ in Filter.atTop, a ∈ C n) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ a ∈ A ∩ Q, a ∈ C n := by
  classical
  rw [← hfinite.coe_toFinset]
  simp only [Finset.mem_coe]
  exact (Filter.eventually_all_finset _).mpr fun a ha ↦
    hA a (hfinite.mem_toFinset.mp ha).1

private theorem local_regularOpen_eq
    {U V : Set Tiling.Plane} {x : Tiling.Plane} {r R : ℝ}
    (_hr : 0 < r) (hrR : r < R)
    (hU : IsOpen U) (hUreg : interior (closure U) = U)
    (hV : IsOpen V) (hVreg : interior (closure V) = V)
    (hae : ∀ᵐ z ∂MeasureTheory.volume,
      (z ∈ U ∩ Metric.ball x R) ↔ (z ∈ V ∩ Metric.ball x R)) :
    U ∩ Metric.ball x r = V ∩ Metric.ball x r := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzU, hzr⟩
    have hzR : z ∈ Metric.ball x R :=
      Metric.mem_ball.mpr ((Metric.mem_ball.mp hzr).trans hrR)
    let P := U ∩ Metric.ball x R
    let Q := V ∩ Metric.ball x R
    have hae' : P =ᵐ[MeasureTheory.volume] Q := by
      filter_upwards [hae] with z hz
      exact propext hz
    have hPQ : P ⊆ closure Q := open_subset_closure_of_ae_subset
      (hU.inter Metric.isOpen_ball) (hae'.le)
    have hPclV : P ⊆ closure V := hPQ.trans (closure_mono inter_subset_left)
    have hzInt : z ∈ interior (closure V) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset
        ((hU.inter Metric.isOpen_ball).mem_nhds ⟨hzU, hzR⟩) hPclV
    exact ⟨hVreg ▸ hzInt, hzr⟩
  · rintro z ⟨hzV, hzr⟩
    have hzR : z ∈ Metric.ball x R :=
      Metric.mem_ball.mpr ((Metric.mem_ball.mp hzr).trans hrR)
    let P := V ∩ Metric.ball x R
    let Q := U ∩ Metric.ball x R
    have hae' : P =ᵐ[MeasureTheory.volume] Q := by
      filter_upwards [hae] with z hz
      exact propext hz.symm
    have hPQ : P ⊆ closure Q := open_subset_closure_of_ae_subset
      (hV.inter Metric.isOpen_ball) (hae'.le)
    have hPclU : P ⊆ closure U := hPQ.trans (closure_mono inter_subset_left)
    have hzInt : z ∈ interior (closure U) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset
        ((hV.inter Metric.isOpen_ball).mem_nhds ⟨hzV, hzR⟩) hPclU
    exact ⟨hUreg ▸ hzInt, hzr⟩

/-- On a smaller ball, deleting the eventually fixed centres from each approximating tiling
leaves exactly the regularized support of the transient limit centres. -/
theorem fixedBackground_cancel
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (_hXnonempty : X.Nonempty) (_hXopen : IsOpen X)
    (_hXregular : interior (closure X) = X)
    {T : ℕ → Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    {S : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    {A B : Set Tiling.Plane}
    (_hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence T)
      (S.centres : Set Tiling.Plane))
    (hdisjoint : Disjoint A B)
    (hunion : A ∪ B = (S.centres : Set Tiling.Plane))
    (hA : ∀ a ∈ A, ∀ᶠ n : ℕ in Filter.atTop,
      a ∈ ((T n).centres : Set Tiling.Plane))
    (_hB : ∀ b ∈ B, ∀ᶠ n : ℕ in Filter.atTop,
      b ∉ ((T n).centres : Set Tiling.Plane))
    {x : Tiling.Plane}
    (_hx : x ∈ frontier (Tiling.AxisParallel.regularSupport K B)) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ᶠ n : ℕ in Filter.atTop,
      Tiling.AxisParallel.regularSupport K
          (((T n).centres : Set Tiling.Plane) \ A) ∩ Metric.ball x rho =
        Tiling.AxisParallel.regularSupport K B ∩ Metric.ball x rho := by
  classical
  let E : Set Tiling.Plane := {z : Tiling.Plane | z.re ∈ X}
  have hAS : A ⊆ (S.centres : Set Tiling.Plane) := by
    intro a ha
    rw [← hunion]
    exact Or.inl ha
  have hBS : B ⊆ (S.centres : Set Tiling.Plane) := by
    intro b hb
    rw [← hunion]
    exact Or.inr hb
  obtain ⟨R, hR⟩ := K.isPolygonal.isBounded.subset_closedBall (0 : Tiling.Plane)
  let Q : Set Tiling.Plane := Metric.closedBall x (R + 2)
  have hAfin : (A ∩ Q).Finite :=
    ((Tiling.AxisParallel.IsPacking.locallyFinite_centres S.tilesOn.2.1).1 Q
      Metric.isBounded_closedBall).subset (inter_subset_inter_left Q hAS)
  have hEventually := eventually_mem_of_finite_relevant hAfin hA
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [hEventually] with n hn
  let Cn : Set Tiling.Plane := ((T n).centres : Set Tiling.Plane)
  have relevant {a z : Tiling.Plane} (ha : a ∈ A)
      (hz : z ∈ Metric.ball x 1) (haz : z ∈ a +ᵥ K.openCarrier) : a ∈ Cn := by
    apply hn a
    refine ⟨ha, ?_⟩
    change dist a x ≤ R + 2
    have hak : -a + z ∈ K.support := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at haz
      exact interior_subset haz
    have hbound := hR hak
    rw [Metric.mem_closedBall, dist_zero_right] at hbound
    have hd : dist a z = dist (-a + z) 0 := by
      rw [dist_comm]
      simp only [dist_eq_norm, sub_zero]
      congr 1
      abel
    have hbound' : dist (-a + z) 0 ≤ R := by
      simpa only [dist_eq_norm, sub_zero] using hbound
    exact (calc
      dist a x ≤ dist a z + dist z x := dist_triangle _ _ _
      _ = dist (-a + z) 0 + dist z x := by rw [hd]
      _ < R + 1 := add_lt_add_of_le_of_lt hbound' (Metric.mem_ball.mp hz)
      _ < R + 2 := by linarith).le
  have residualT (z : Tiling.Plane) (hz : z ∈ Metric.ball x 1) :
      z ∈ Tiling.AxisParallel.openUnion K (Cn \ A) ↔
        z ∈ Tiling.AxisParallel.openUnion K Cn ∧
          z ∉ Tiling.AxisParallel.openUnion K A := by
    constructor
    · intro hzres
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzres
      obtain ⟨t, ht⟩ := hzres
      refine ⟨?_, ?_⟩
      · rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
        exact ⟨⟨t.1, t.2.1⟩, ht⟩
      · intro hzA
        rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzA
        obtain ⟨a, ha⟩ := hzA
        have haCn : a.1 ∈ Cn := relevant a.2 hz ha
        have hat : a.1 ≠ t.1 := fun e ↦ t.2.2 (e ▸ a.2)
        have hd := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K Cn).mp
          (T n).tilesOn.2.1 haCn t.2.1 hat
        exact Set.disjoint_left.1 hd ha ht
    · rintro ⟨hzT, hznotA⟩
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzT ⊢
      obtain ⟨t, ht⟩ := hzT
      refine ⟨⟨t.1, t.2, ?_⟩, ht⟩
      intro htA
      apply hznotA
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      exact ⟨⟨t.1, htA⟩, ht⟩
  have residualS (z : Tiling.Plane) :
      z ∈ Tiling.AxisParallel.openUnion K B ↔
        z ∈ Tiling.AxisParallel.openUnion K (S.centres : Set Tiling.Plane) ∧
          z ∉ Tiling.AxisParallel.openUnion K A := by
    constructor
    · intro hzB
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzB
      obtain ⟨b, hb⟩ := hzB
      refine ⟨?_, ?_⟩
      · rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
        exact ⟨⟨b.1, hBS b.2⟩, hb⟩
      · intro hzA
        rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzA
        obtain ⟨a, ha⟩ := hzA
        have hab : a.1 ≠ b.1 := by
          intro e
          exact Set.disjoint_left.1 hdisjoint a.2 (e ▸ b.2)
        have hd := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K
          (S.centres : Set Tiling.Plane)).mp S.tilesOn.2.1 (hAS a.2) (hBS b.2) hab
        exact Set.disjoint_left.1 hd ha hb
    · rintro ⟨hzS, hznotA⟩
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzS ⊢
      obtain ⟨s, hs⟩ := hzS
      have hsAB : s.1 ∈ A ∪ B := hunion.symm ▸ s.2
      rcases hsAB with hsA | hsB
      · exfalso
        apply hznotA
        rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
        exact ⟨⟨s.1, hsA⟩, hs⟩
      · exact ⟨⟨s.1, hsB⟩, hs⟩
  have haeTotals : ∀ᵐ z ∂MeasureTheory.volume,
      (z ∈ Tiling.AxisParallel.openUnion K Cn) ↔
        z ∈ Tiling.AxisParallel.openUnion K (S.centres : Set Tiling.Plane) := by
    filter_upwards [(T n).tilesOn.2.2, S.tilesOn.2.2] with z hT hS
    have hT' : z ∈ E ↔ z ∈ Tiling.AxisParallel.openUnion K Cn := by
      simpa only [E, Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier.eq_def, Set.mem_iUnion,
        Set.mem_ofPred_eq] using hT
    have hS' : z ∈ E ↔
        z ∈ Tiling.AxisParallel.openUnion K (S.centres : Set Tiling.Plane) := by
      simpa only [E, Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier.eq_def, Set.mem_iUnion,
        Set.mem_ofPred_eq] using hS
    exact hT'.symm.trans hS'
  have haeRaw : ∀ᵐ z ∂MeasureTheory.volume,
      (z ∈ Tiling.AxisParallel.openUnion K (Cn \ A) ∩ Metric.ball x 1) ↔
        z ∈ Tiling.AxisParallel.openUnion K B ∩ Metric.ball x 1 := by
    filter_upwards [haeTotals] with z hzTotal
    constructor
    · rintro ⟨hzres, hzball⟩
      rw [residualT z hzball] at hzres
      exact ⟨(residualS z).2 ⟨hzTotal.mp hzres.1, hzres.2⟩, hzball⟩
    · rintro ⟨hzB, hzball⟩
      rw [residualS z] at hzB
      exact ⟨(residualT z hzball).2 ⟨hzTotal.mpr hzB.1, hzB.2⟩, hzball⟩
  have packCn : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (Cn \ A)) := by
    intro p hp q hq hpq
    exact (T n).tilesOn.2.1 hp.1 hq.1 hpq
  have packB : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements B) := by
    intro p hp q hq hpq
    exact S.tilesOn.2.1 (hBS hp) (hBS hq) hpq
  have haeSupports : ∀ᵐ z ∂MeasureTheory.volume,
      (z ∈ Tiling.AxisParallel.regularSupport K (Cn \ A) ∩ Metric.ball x 1) ↔
        z ∈ Tiling.AxisParallel.regularSupport K B ∩ Metric.ball x 1 := by
    filter_upwards [Tiling.AxisParallel.openUnion_aeEq_regularSupport packCn,
      Tiling.AxisParallel.openUnion_aeEq_regularSupport packB, haeRaw] with z hCn hB hz
    constructor
    · rintro ⟨hzRC, hzball⟩
      have hzOC : z ∈ Tiling.AxisParallel.openUnion K (Cn \ A) :=
        Eq.mpr hCn hzRC
      have hzOB : z ∈ Tiling.AxisParallel.openUnion K B := (hz.mp ⟨hzOC, hzball⟩).1
      exact ⟨Eq.mp hB hzOB, hzball⟩
    · rintro ⟨hzRB, hzball⟩
      have hzOB : z ∈ Tiling.AxisParallel.openUnion K B := Eq.mpr hB hzRB
      have hzOC : z ∈ Tiling.AxisParallel.openUnion K (Cn \ A) :=
        (hz.mpr ⟨hzOB, hzball⟩).1
      exact ⟨Eq.mp hCn hzOC, hzball⟩
  exact local_regularOpen_eq (by norm_num) (by norm_num)
    (Tiling.AxisParallel.regularSupport_isRegularOpen K (Cn \ A)).1
    (Tiling.AxisParallel.regularSupport_isRegularOpen K (Cn \ A)).2
    (Tiling.AxisParallel.regularSupport_isRegularOpen K B).1
    (Tiling.AxisParallel.regularSupport_isRegularOpen K B).2 haeSupports

private theorem movingCorner_core
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    {T : ℕ → Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    {S : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    {A B : Set Tiling.Plane}
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence T)
      (S.centres : Set Tiling.Plane))
    (hunion : A ∪ B = (S.centres : Set Tiling.Plane))
    (hB : ∀ b ∈ B, ∀ᶠ n : ℕ in Filter.atTop,
      b ∉ ((T n).centres : Set Tiling.Plane))
    {x : Tiling.Plane} (hx : Tiling.AxisParallel.IsProperVertex
      (Tiling.AxisParallel.regularSupport K B) x)
    (hlocal : ∀ᶠ n : ℕ in Filter.atTop,
      Tiling.AxisParallel.regularSupport K
          (((T n).centres : Set Tiling.Plane) \ A) =ᶠ[𝓝 x]
        Tiling.AxisParallel.regularSupport K B) : False := by
  classical
  let C : Set Tiling.Plane := {c | ∃ v ∈ K.vertices, c = x - v}
  have hCfinite : C.Finite := by
    refine K.isPolygonal.vertexSet_finite.image (fun v ↦ x - v) |>.subset ?_
    rintro c ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  have houtside : Disjoint (S.centres : Set Tiling.Plane) (C \ (A ∪ B)) := by
    rw [← hunion]
    exact disjoint_sdiff_right
  have hmiss := locallyFellConverges_eventually_disjoint_compact hconv
    hCfinite.sdiff.isCompact houtside
  have hnoCandidate : ∀ᶠ n : ℕ in Filter.atTop,
      Disjoint (((T n).centres : Set Tiling.Plane) \ A) C := by
    have hall : ∀ᶠ n : ℕ in Filter.atTop, ∀ c ∈ C, c ∈ A ∪ B →
        c ∉ ((T n).centres : Set Tiling.Plane) \ A := by
      rw [hCfinite.eventually_all]
      intro c hc
      by_cases hcA : c ∈ A
      · exact Filter.Eventually.of_forall fun _ _ hcQ ↦ hcQ.2 hcA
      · by_cases hcB : c ∈ B
        · filter_upwards [hB c hcB] with n hn _ hcQ
          exact hn hcQ.1
        · exact Filter.Eventually.of_forall fun _ hcAB _ ↦
            hcB (hcAB.resolve_left hcA)
    filter_upwards [hmiss, hall] with n hnmiss hnC
    rw [Set.disjoint_left]
    intro c hcQ hcC
    by_cases hcAB : c ∈ A ∪ B
    · exact hnC c hcC hcAB hcQ
    · exact Set.disjoint_left.mp hnmiss hcQ.1 ⟨hcC, hcAB⟩
  have hevFalse : ∀ᶠ _ : ℕ in Filter.atTop, False := by
    filter_upwards [hlocal, hnoCandidate] with n hnlocal hnvertices
    let Q : Set Tiling.Plane := ((T n).centres : Set Tiling.Plane) \ A
    let P := K.polygonalProtoTiling Q
    have hpacking : Tiling.IsPacking P.prototiles P.placements := by
      intro i hi j hj hij
      exact (T n).tilesOn.2.1 hi.1 hj.1 hij
    have hxproper : Tiling.AxisParallel.IsProperVertex
        (Tiling.AxisParallel.regularSupport K Q) x :=
      (Tiling.AxisParallel.isProperVertex_iff_of_eventuallyEq hnlocal.symm).mp hx
    have hcarrier : P.placementCarrier Set.univ =
        closure (Tiling.AxisParallel.openUnion K Q) := by
      rw [Tiling.AxisParallel.closure_openUnion_eq_iUnion_support hpacking]
      ext y
      constructor
      · rw [Tiling.PolygonalProtoTiling.mem_placementCarrier_iff]
        rintro ⟨i, -, hi⟩
        rw [Set.mem_iUnion]
        refine ⟨⟨i.1.1, i.2⟩, ?_⟩
        change y ∈ i.1.1 +ᵥ K.support at hi
        exact hi
      · rw [Set.mem_iUnion]
        rintro ⟨q, hqy⟩
        rw [Tiling.PolygonalProtoTiling.mem_placementCarrier_iff]
        refine ⟨⟨(q.1, ()), q.2⟩, Set.mem_univ _, ?_⟩
        change y ∈ q.1 +ᵥ K.support
        exact hqy
    have hsupport : Tiling.AxisParallel.regularSupport K Q =
        interior (P.placementCarrier univ) := by
      rw [Tiling.AxisParallel.regularSupport, Tiling.Polygonal.regularSupport,
        ← Tiling.AxisParallel.openUnion, hcarrier]
    have hfrontier : frontier (Tiling.AxisParallel.regularSupport K Q) =
        frontier (P.placementCarrier univ) := by
      rw [hsupport, isOpen_interior.frontier_eq,
        (P.placementCarrier_isClosed hpacking univ).frontier_eq,
        P.placementCarrier_closure_interior hpacking univ]
    have hxcarrier : x ∈ frontier (P.placementCarrier univ) := hfrontier ▸ hxproper.1
    have hxnotstraight : ¬Tiling.BoundaryLocallyStraightAt (P.placementCarrier univ) x := by
      intro hs
      apply hxproper.2
      obtain ⟨L, hxL, hdim, hline⟩ := hs
      exact ⟨L, hxL, hdim, by simpa only [hfrontier] using hline⟩
    obtain ⟨i, -, hxi⟩ :=
      P.exists_vertex_of_not_boundaryLocallyStraightAt hpacking univ hxcarrier hxnotstraight
    rw [K.polygonalProtoTiling_placedVertices] at hxi
    obtain ⟨v, hv, hvx⟩ := hxi
    have hiC : i.1.1 ∈ C := by
      refine ⟨v, hv, ?_⟩
      rw [← hvx]
      simp
    exact Set.disjoint_left.mp hnvertices i.2 hiC
  exact (Filter.Eventually.exists hevFalse).choose_spec

/-- The locally stabilized support of the centres moving away from their limit positions cannot
have a proper boundary vertex. -/
theorem movingTileLimit_hasNoCorner
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    {T : ℕ → Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    {S : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    {A B : Set Tiling.Plane}
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence T)
      (S.centres : Set Tiling.Plane))
    (hdisjoint : Disjoint A B)
    (hunion : A ∪ B = (S.centres : Set Tiling.Plane))
    (hA : ∀ a ∈ A, ∀ᶠ n : ℕ in Filter.atTop,
      a ∈ ((T n).centres : Set Tiling.Plane))
    (hB : ∀ b ∈ B, ∀ᶠ n : ℕ in Filter.atTop,
      b ∉ ((T n).centres : Set Tiling.Plane))
    {x : Tiling.Plane} (hx : x ∈ frontier (Tiling.AxisParallel.regularSupport K B)) :
    ¬ Tiling.AxisParallel.IsProperVertex (Tiling.AxisParallel.regularSupport K B) x := by
  intro hxproper
  obtain ⟨rho, hrho, heq⟩ := fixedBackground_cancel
    hXnonempty hXopen hXregular hconv hdisjoint hunion hA hB hx
  apply movingCorner_core hconv hunion hB hxproper
  filter_upwards [heq] with n hn
  filter_upwards [Metric.ball_mem_nhds x hrho] with y hy
  have hiff := Set.ext_iff.mp hn y
  apply propext
  exact ⟨fun h ↦ (hiff.mp ⟨h, hy⟩).1, fun h ↦ (hiff.mpr ⟨h, hy⟩).1⟩

/-- The regular support of all transient limit centres has no proper boundary vertices. -/
theorem transientSupport_hasNoProperVertex
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    {T : ℕ → Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    {S : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    {A B : Set Tiling.Plane}
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence T)
      (S.centres : Set Tiling.Plane))
    (hdisjoint : Disjoint A B)
    (hunion : A ∪ B = (S.centres : Set Tiling.Plane))
    (hA : ∀ a ∈ A, ∀ᶠ n : ℕ in Filter.atTop,
      a ∈ ((T n).centres : Set Tiling.Plane))
    (hB : ∀ b ∈ B, ∀ᶠ n : ℕ in Filter.atTop,
      b ∉ ((T n).centres : Set Tiling.Plane)) :
    Tiling.AxisParallel.properVertices (Tiling.AxisParallel.regularSupport K B) = ∅ := by
  ext x
  change Tiling.AxisParallel.IsProperVertex
      (Tiling.AxisParallel.regularSupport K B) x ↔ x ∈ (∅ : Set Tiling.Plane)
  constructor
  · intro hx
    exact (movingTileLimit_hasNoCorner hXnonempty hXopen hXregular hconv hdisjoint
      hunion hA hB hx.1 hx).elim
  · intro hx
    exact hx.elim


/-- A regular-open planar set without proper vertices is invariant under every translation along
some nonzero direction.  Axis-parallel polygonality is needed only in the subsequent step that
identifies this direction as horizontal or vertical. -/
theorem noProperVertexSupport_hasStabilizerDirection
    {D : Set Tiling.Plane} (hDopen : IsOpen D)
    (hDregular : interior (closure D) = D)
    (hDvertices : Tiling.AxisParallel.properVertices D = ∅) :
    ∃ v : Tiling.Plane, v ≠ 0 ∧ ∀ r : ℝ,
      r • v ∈ AddAction.stabilizer Tiling.Plane D := by
  exact Tiling.AxisParallel.exists_stabilizerDirection_of_noProperVertices
    hDopen hDregular hDvertices

private theorem cylinder_regular_re
    {D : Set Tiling.Plane} (hDopen : IsOpen D)
    (hDregular : interior (closure D) = D) {Y : Set ℝ}
    (hDY : D = {z : Tiling.Plane | z.re ∈ Y}) :
    IsOpen Y ∧ interior (closure Y) = Y := by
  have hpre : D = Complex.re ⁻¹' Y := hDY
  have hYopen : IsOpen Y := by
    have hsection : Y = Complex.ofReal ⁻¹' D := by
      ext y
      simp [hpre]
    rw [hsection]
    exact hDopen.preimage Complex.continuous_ofReal
  refine ⟨hYopen, ?_⟩
  have heq : Complex.re ⁻¹' interior (closure Y) = Complex.re ⁻¹' Y := by
    rw [← Complex.interior_preimage_re, ← Complex.closure_preimage_re, ← hpre,
      hDregular, hpre]
  ext y
  have := Set.ext_iff.mp heq (y : ℂ)
  simpa using this

private theorem cylinder_regular_im
    {D : Set Tiling.Plane} (hDopen : IsOpen D)
    (hDregular : interior (closure D) = D) {Y : Set ℝ}
    (hDY : D = {z : Tiling.Plane | z.im ∈ Y}) :
    IsOpen Y ∧ interior (closure Y) = Y := by
  have hpre : D = Complex.im ⁻¹' Y := hDY
  have hYopen : IsOpen Y := by
    have hsection : Y = (fun y : ℝ ↦ (y : ℂ) * Complex.I) ⁻¹' D := by
      ext y
      simp [hpre]
    rw [hsection]
    exact hDopen.preimage (Complex.continuous_ofReal.mul continuous_const)
  refine ⟨hYopen, ?_⟩
  have heq : Complex.im ⁻¹' interior (closure Y) = Complex.im ⁻¹' Y := by
    rw [← Complex.interior_preimage_im, ← Complex.closure_preimage_im, ← hpre,
      hDregular, hpre]
  ext y
  have := Set.ext_iff.mp heq ((y : ℂ) * Complex.I)
  simpa using this

/-- A regular-open set with no proper vertices is an axis slab, provided its boundary is locally
contained in a coordinate cross. -/
theorem noProperVertexSupport_isAxisSlab_of_localBoundaryCross
    {D : Set Tiling.Plane} (hDopen : IsOpen D)
    (hDregular : interior (closure D) = D)
    (hcross : ∀ x, ∃ r > 0, ∀ z ∈ Metric.ball x r, z ∈ frontier D →
      z.re = x.re ∨ z.im = x.im)
    (hDvertices : Tiling.AxisParallel.properVertices D = ∅) :
    (∃ Y : Set ℝ, IsOpen Y ∧ interior (closure Y) = Y ∧
      D = {z : Tiling.Plane | z.re ∈ Y}) ∨
    (∃ Y : Set ℝ, IsOpen Y ∧ interior (closure Y) = Y ∧
      D = {z : Tiling.Plane | z.im ∈ Y}) := by
  by_cases hfront : frontier D = ∅
  · rcases frontier_eq_empty_iff.mp hfront with rfl | rfl
    · left
      refine ⟨∅, isOpen_empty, by simp, by simp⟩
    · left
      refine ⟨Set.univ, isOpen_univ, by simp, by simp⟩
  obtain ⟨v, hv, hinvariant⟩ :=
    noProperVertexSupport_hasStabilizerDirection hDopen hDregular hDvertices
  obtain ⟨x, hx⟩ : (frontier D).Nonempty := Set.nonempty_iff_ne_empty.mpr hfront
  obtain ⟨r, hr, hlocal⟩ := hcross x
  let t : ℝ := r / (2 * ‖v‖)
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ht : 0 < t := div_pos hr (mul_pos zero_lt_two hvnorm)
  have hfrontier_translate (a : ℝ) :
      a • v +ᵥ frontier D = frontier D := by
    have hi := (Homeomorph.vaddConst (a • v)).image_frontier D
    have hi' : a • v +ᵥ frontier D = frontier (a • v +ᵥ D) := by
      change (fun z ↦ a • v + z) '' frontier D =
        frontier ((fun z ↦ a • v + z) '' D)
      simpa [add_comm] using hi
    exact hi'.trans (congrArg frontier
      (AddAction.mem_stabilizer_iff.mp (hinvariant a)))
  have hzball : t • v + x ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp
    linarith
  have hzfront : t • v + x ∈ frontier D := by
    rw [← hfrontier_translate t]
    exact ⟨x, hx, rfl⟩
  rcases hlocal (t • v + x) hzball hzfront with hre | him
  · have hvre : v.re = 0 := by
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at hre
      exact (mul_eq_zero.mp (by linarith : t * v.re = 0)).resolve_left ht.ne'
    left
    have hvim : v.im ≠ 0 := by
      intro hvim
      apply hv
      apply Complex.ext <;> simp [hvre, hvim]
    have hvertical : ∀ a : ℝ, ((a : ℂ) * Complex.I) +ᵥ D = D := by
      intro a
      rw [show (a : ℂ) * Complex.I = (a / v.im) • v by
        apply Complex.ext <;> simp [hvre, hvim]]
      exact AddAction.mem_stabilizer_iff.mp (hinvariant (a / v.im))
    obtain ⟨Y, hDY⟩ := (Tiling.AxisParallel.verticalInvariant_iff_product D).mp hvertical
    exact ⟨Y, (cylinder_regular_re hDopen hDregular hDY).1,
      (cylinder_regular_re hDopen hDregular hDY).2, hDY⟩
  · have hvim : v.im = 0 := by
      simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at him
      exact (mul_eq_zero.mp (by linarith : t * v.im = 0)).resolve_left ht.ne'
    right
    have hvre : v.re ≠ 0 := by
      intro hvre
      apply hv
      apply Complex.ext <;> simp [hvre, hvim]
    have hhorizontal : ∀ a : ℝ, (a : ℂ) +ᵥ D = D := by
      intro a
      rw [show (a : ℂ) = (a / v.re) • v by
        apply Complex.ext <;> simp [hvim, hvre]]
      exact AddAction.mem_stabilizer_iff.mp (hinvariant (a / v.re))
    obtain ⟨Y, hDY⟩ := (Tiling.AxisParallel.horizontalInvariant_iff_product D).mp hhorizontal
    exact ⟨Y, (cylinder_regular_im hDopen hDregular hDY).1,
      (cylinder_regular_im hDopen hDregular hDY).2, hDY⟩

/-- A regular-open locally axis-parallel polygonal set without proper vertices is an axis slab. -/
theorem noProperVertexSupport_isAxisSlab
    {D : Set Tiling.Plane} (hDopen : IsOpen D)
    (hDregular : interior (closure D) = D)
    (hDpolygonal : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal D)
    (hDvertices : Tiling.AxisParallel.properVertices D = ∅) :
    (∃ Y : Set ℝ, IsOpen Y ∧ interior (closure Y) = Y ∧
      D = {z : Tiling.Plane | z.re ∈ Y}) ∨
    (∃ Y : Set ℝ, IsOpen Y ∧ interior (closure Y) = Y ∧
      D = {z : Tiling.Plane | z.im ∈ Y}) := by
  exact noProperVertexSupport_isAxisSlab_of_localBoundaryCross hDopen hDregular
    (Tiling.AxisParallel.exists_ball_frontier_subset_axisCross hDpolygonal) hDvertices

/-- An a.e. complementary regular-open set has the same slab direction as an already classified
nonempty slab; in the horizontal case the vertical carrier must be the whole plane. -/
theorem axisSlab_complement_inCarrier_of_classification
    {X : Set ℝ} (hXregular : interior (closure X) = X)
    {D0 D1 : Set Tiling.Plane}
    (hD0open : IsOpen D0) (hD1open : IsOpen D1)
    (hD0regular : interior (closure D0) = D0)
    (hcover : (D0 ∪ D1 : Set Tiling.Plane) =ᵐ[MeasureTheory.volume]
      ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane))
    (hdisjoint : MeasureTheory.AEDisjoint MeasureTheory.volume D0 D1)
    (hD1nonempty : D1.Nonempty)
    (hclass : (∃ Y : Set ℝ, IsOpen Y ∧ interior (closure Y) = Y ∧
      D1 = {z : Tiling.Plane | z.re ∈ Y}) ∨
      (∃ Y : Set ℝ, IsOpen Y ∧ interior (closure Y) = Y ∧
      D1 = {z : Tiling.Plane | z.im ∈ Y})) :
    (∃ Y0 Y1 : Set ℝ, IsOpen Y0 ∧ IsOpen Y1 ∧
      interior (closure Y0) = Y0 ∧ interior (closure Y1) = Y1 ∧
      D0 = {z : Tiling.Plane | z.re ∈ Y0} ∧
      D1 = {z : Tiling.Plane | z.re ∈ Y1}) ∨
    (X = Set.univ ∧ ∃ Y0 Y1 : Set ℝ, IsOpen Y0 ∧ IsOpen Y1 ∧
      interior (closure Y0) = Y0 ∧ interior (closure Y1) = Y1 ∧
      D0 = {z : Tiling.Plane | z.im ∈ Y0} ∧
      D1 = {z : Tiling.Plane | z.im ∈ Y1}) := by
  have hnotBoth : ∀ᵐ z ∂MeasureTheory.volume, ¬ (z ∈ D0 ∧ z ∈ D1) := by
    rw [MeasureTheory.AEDisjoint, measure_eq_zero_iff_ae_notMem] at hdisjoint
    simpa only [mem_inter_iff] using hdisjoint
  have hD0comp : D0 =ᵐ[MeasureTheory.volume]
      ({z : Tiling.Plane | z.re ∈ X} \ D1) := by
    filter_upwards [hcover, hnotBoth] with z hz hnb
    have hz' : ((z ∈ D0 ∨ z ∈ D1) ↔ z.re ∈ X) := iff_of_eq hz
    apply propext
    change (z ∈ D0) ↔ (z.re ∈ X ∧ z ∉ D1)
    exact by tauto
  rcases hclass with ⟨Y1, hY1open, hY1reg, rfl⟩ | ⟨Y1, hY1open, hY1reg, rfl⟩
  · have hcompInv : ∀ a : ℝ, ((a : ℂ) * Complex.I) +ᵥ
        (({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) \
          {z : Tiling.Plane | z.re ∈ Y1}) =
        (({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) \
          {z : Tiling.Plane | z.re ∈ Y1}) := by
      intro a
      ext z
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, mem_sdiff, mem_ofPred_eq, vadd_eq_add]
      simp
    have hD0inv : ∀ a : ℝ, ((a : ℂ) * Complex.I) +ᵥ D0 = D0 := by
      intro a
      apply Tiling.AxisParallel.regularOpen_eq_of_aeEq (hD0open.vadd _) (by
        rw [closure_vadd, interior_vadd, hD0regular]) hD0open hD0regular
      have hs := ((MeasureTheory.quasiMeasurePreserving_add_left MeasureTheory.volume
        (-((a : ℂ) * Complex.I))).vadd_ae_eq_of_ae_eq
          ((a : ℂ) * Complex.I) hD0comp)
      have hi : ((a : ℂ) * Complex.I) +ᵥ
          (({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) \
            {z : Tiling.Plane | z.re ∈ Y1}) =ᵐ[MeasureTheory.volume]
          (({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) \
            {z : Tiling.Plane | z.re ∈ Y1}) :=
        Filter.Eventually.of_forall fun z ↦ congrFun (hcompInv a) z
      exact (hs.trans hi).trans hD0comp.symm
    obtain ⟨Y0, hY0⟩ :=
      (Tiling.AxisParallel.verticalInvariant_iff_product D0).mp hD0inv
    have hY0reg := cylinder_regular_re hD0open hD0regular hY0
    exact Or.inl ⟨Y0, Y1, hY0reg.1, hY1open, hY0reg.2, hY1reg, hY0, rfl⟩
  · have hD1sub : ({z : Tiling.Plane | z.im ∈ Y1} : Set Tiling.Plane) ⊆
        closure ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) := by
      apply open_subset_closure_of_ae_subset hD1open
      filter_upwards [hcover] with z hz hz1
      exact hz.mp (Or.inr hz1)
    have hclosureX : closure X = Set.univ := by
      apply eq_univ_of_forall
      intro x
      obtain ⟨z, hz⟩ := hD1nonempty
      have hp := hD1sub (show (x : ℂ) + (z.im : ℂ) * Complex.I ∈
        {w : Tiling.Plane | w.im ∈ Y1} by simpa using hz)
      change (x : ℂ) + (z.im : ℂ) * Complex.I ∈ closure (Complex.re ⁻¹' X) at hp
      rw [Complex.closure_preimage_re] at hp
      simpa using hp
    have hXuniv : X = Set.univ := by rw [← hXregular, hclosureX, interior_univ]
    have hD0ae : D0 =ᵐ[MeasureTheory.volume]
        ({z : Tiling.Plane | z.im ∉ Y1} : Set Tiling.Plane) := by
      filter_upwards [hD0comp] with z hz
      have hz' : (z ∈ D0) ↔ (z.re ∈ X ∧ z.im ∉ Y1) := iff_of_eq hz
      rw [hXuniv] at hz'
      change (z ∈ D0) = (z.im ∉ Y1)
      exact propext (by simpa only [mem_univ, true_and] using hz')
    have hcompInv : ∀ a : ℝ, (a : ℂ) +ᵥ
        ({z : Tiling.Plane | z.im ∉ Y1} : Set Tiling.Plane) =
        {z : Tiling.Plane | z.im ∉ Y1} := by
      intro a
      ext z
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, mem_ofPred_eq, vadd_eq_add]
      simp
    have hD0inv : ∀ a : ℝ, (a : ℂ) +ᵥ D0 = D0 := by
      intro a
      apply Tiling.AxisParallel.regularOpen_eq_of_aeEq (hD0open.vadd _) (by
        rw [closure_vadd, interior_vadd, hD0regular]) hD0open hD0regular
      have hs := (MeasureTheory.quasiMeasurePreserving_add_left MeasureTheory.volume
        (-(a : ℂ))).vadd_ae_eq_of_ae_eq (a : ℂ) hD0ae
      have hi : (a : ℂ) +ᵥ ({z : Tiling.Plane | z.im ∉ Y1} : Set Tiling.Plane)
          =ᵐ[MeasureTheory.volume] {z : Tiling.Plane | z.im ∉ Y1} :=
        Filter.Eventually.of_forall fun z ↦ congrFun (hcompInv a) z
      exact (hs.trans hi).trans hD0ae.symm
    obtain ⟨Y0, hY0⟩ :=
      (Tiling.AxisParallel.horizontalInvariant_iff_product D0).mp hD0inv
    have hY0reg := cylinder_regular_im hD0open hD0regular hY0
    exact Or.inr ⟨hXuniv, Y0, Y1, hY0reg.1, hY1open, hY0reg.2, hY1reg, hY0, rfl⟩

/-- The regular-open complement of a nonempty axis slab in a vertical carrier is a slab in the
same direction; a nonempty horizontal slab forces the carrier to be the whole plane. -/
theorem axisSlab_complement_inCarrier
    {X : Set ℝ} (_hXopen : IsOpen X) (hXregular : interior (closure X) = X)
    {D0 D1 : Set Tiling.Plane}
    (hD0open : IsOpen D0) (hD1open : IsOpen D1)
    (hD0regular : interior (closure D0) = D0)
    (hD1regular : interior (closure D1) = D1)
    (hcover : (D0 ∪ D1 : Set Tiling.Plane) =ᵐ[MeasureTheory.volume]
      ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane))
    (hdisjoint : MeasureTheory.AEDisjoint MeasureTheory.volume D0 D1)
    (_hD0nonempty : D0.Nonempty) (hD1nonempty : D1.Nonempty)
    (hD1polygonal : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal D1)
    (hD1vertices : Tiling.AxisParallel.properVertices D1 = ∅) :
    (∃ Y0 Y1 : Set ℝ, IsOpen Y0 ∧ IsOpen Y1 ∧
      interior (closure Y0) = Y0 ∧ interior (closure Y1) = Y1 ∧
      D0 = {z : Tiling.Plane | z.re ∈ Y0} ∧
      D1 = {z : Tiling.Plane | z.re ∈ Y1}) ∨
    (X = Set.univ ∧ ∃ Y0 Y1 : Set ℝ, IsOpen Y0 ∧ IsOpen Y1 ∧
      interior (closure Y0) = Y0 ∧ interior (closure Y1) = Y1 ∧
      D0 = {z : Tiling.Plane | z.im ∈ Y0} ∧
      D1 = {z : Tiling.Plane | z.im ∈ Y1}) := by
  apply axisSlab_complement_inCarrier_of_classification hXregular hD0open hD1open hD0regular
    hcover hdisjoint hD1nonempty
  exact noProperVertexSupport_isAxisSlab hD1open hD1regular hD1polygonal hD1vertices

private theorem regularSupport_nonempty_of_centres
    (K : Tiling.AxisParallel.Region) {Q : Set Tiling.Plane} (hQ : Q.Nonempty) :
    (Tiling.AxisParallel.regularSupport K Q).Nonempty := by
  have hOpenCarrier : K.openCarrier.Nonempty :=
    K.isPolygonal.interior_nonempty K.nonempty
  obtain ⟨q, hq⟩ := hQ
  obtain ⟨k, hk⟩ := hOpenCarrier
  refine ⟨q + k, ?_⟩
  change q + k ∈ interior (closure (Tiling.AxisParallel.openUnion K Q))
  have hopen : IsOpen (Tiling.AxisParallel.openUnion K Q) := by
    exact isOpen_iUnion fun s ↦
      (Tiling.AxisParallel.Region.openCarrier_regularOpen K).1.vadd (s : Tiling.Plane)
  apply interior_maximal subset_closure hopen
  rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
  exact ⟨⟨q, hq⟩, k, hk, rfl⟩

/-- After passage to a subsequence, the limit centres split literally into eventually present and
eventually absent sets whose regular supports have one common slab direction and are saturated by
the corresponding continuous plates. -/
theorem exists_persistentTransientSplit
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    (_hfrontier : ∀ C : Set ℝ, IsCompact C → (C ∩ frontier X).Finite)
    (T : ℕ → Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    (S : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence T)
      (S.centres : Set Tiling.Plane)) :
    ∃ (phi : ℕ → ℕ)
      (_D : Tiling.AxisParallel.Continuous.PersistentTransientSplit K X (T ∘ phi) S),
      StrictMono phi := by
  obtain ⟨phi, A, B, hphi, hAS, hBS, hAB, hUnion, hAevent, hBevent⟩ :=
    exists_eventualMembershipPartition hXnonempty hXopen hXregular T S hconv
  have hconvphi : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence (T ∘ phi))
      (S.centres : Set Tiling.Plane) := by
    apply ((Tiling.AxisParallel.Continuous.locallyFell_metrizable K
      {z : Tiling.Plane | z.re ∈ X}).2 (T ∘ phi) S).mp
    exact (((Tiling.AxisParallel.Continuous.locallyFell_metrizable K
      {z : Tiling.Plane | z.re ∈ X}).2 T S).mpr hconv).comp hphi.tendsto_atTop
  by_cases hBempty : B = ∅
  · subst B
    have hAeq : A = (S.centres : Set Tiling.Plane) := by simpa using hUnion
    subst A
    have hCarrierOpen : IsOpen ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) :=
      hXopen.preimage Complex.continuous_re
    have hCarrierRegular : interior
        (closure ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane)) =
        {z : Tiling.Plane | z.re ∈ X} := by
      change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
      rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hXregular]
    have hSupportS : Tiling.AxisParallel.regularSupport K (S.centres : Set Tiling.Plane) =
        {z : Tiling.Plane | z.re ∈ X} :=
      Tiling.AxisParallel.regularSupport_eq_of_tilesOn hCarrierOpen hCarrierRegular S.tilesOn
    refine ⟨phi, {
      persistent := (S.centres : Set Tiling.Plane)
      transient := ∅
      persistent_subset := Subset.rfl
      transient_subset := empty_subset _
      disjoint := disjoint_empty _
      union_eq := union_empty _
      persistent_eventuallyMem := hAevent
      transient_eventuallyNotMem := by simp
      orientation := Tiling.AxisParallel.Axis.vertical
      persistentBase := X
      transientBase := ∅
      persistentBase_open := hXopen
      transientBase_open := isOpen_empty
      persistentBase_regular := hXregular
      transientBase_regular := by simp
      persistentSupport_vertical := fun _ ↦ hSupportS
      transientSupport_vertical := fun _ ↦ by
        simp [Tiling.AxisParallel.regularSupport, Tiling.Polygonal.regularSupport,
          Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion]
      persistentSupport_horizontal := by intro h; cases h
      transientSupport_horizontal := by intro h; cases h
      horizontal_requires_plane := by intro h; cases h
      verticalPersistent_plateSaturated := by
        intro _ P _ p hp
        rcases hp with ⟨q, _hq, rfl⟩
        exact q.2
      verticalTransient_plateSaturated := by simp
      horizontalPersistent_plateSaturated := by intro h; cases h
      horizontalTransient_plateSaturated := by intro h; cases h
    }, hphi⟩
  · let parts : Bool → Set Tiling.Plane := fun b ↦ if b then B else A
    have hparts : Set.PairwiseDisjoint Set.univ parts := by
      intro i _ j _ hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · change Disjoint A B
        exact hAB
      · change Disjoint B A
        exact hAB.symm
      · exact (hij rfl).elim
    have hpartsUnion : (⋃ i, parts i) = (S.centres : Set Tiling.Plane) := by
      rw [show (⋃ i, parts i) = A ∪ B by
        ext z
        simp [parts]]
      exact hUnion
    obtain ⟨hSupportPairwise, hSupportCover⟩ :=
      Tiling.AxisParallel.regularSupport_pairwiseDisjoint parts hparts hpartsUnion S.tilesOn
    have hSupportDisjoint : Disjoint (Tiling.AxisParallel.regularSupport K A)
        (Tiling.AxisParallel.regularSupport K B) := by
      have hd := hSupportPairwise (Set.mem_univ false) (Set.mem_univ true) (by decide)
      change Disjoint (Tiling.AxisParallel.regularSupport K A)
        (Tiling.AxisParallel.regularSupport K B) at hd
      exact hd
    have hSupportCover :
        (Tiling.AxisParallel.regularSupport K A ∪
          Tiling.AxisParallel.regularSupport K B : Set Tiling.Plane)
          =ᵐ[MeasureTheory.volume] ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) := by
      have heq : (⋃ i, Tiling.AxisParallel.regularSupport K (parts i)) =
          Tiling.AxisParallel.regularSupport K A ∪
            Tiling.AxisParallel.regularSupport K B := by
        ext z
        constructor
        · rw [Set.mem_iUnion]
          rintro ⟨i, hi⟩
          cases i
          · exact Or.inl hi
          · exact Or.inr hi
        · rintro (hz | hz)
          · rw [Set.mem_iUnion]
            exact ⟨false, hz⟩
          · rw [Set.mem_iUnion]
            exact ⟨true, hz⟩
      rw [heq] at hSupportCover
      exact hSupportCover
    have hBsupportNonempty : (Tiling.AxisParallel.regularSupport K B).Nonempty :=
      regularSupport_nonempty_of_centres K (Set.nonempty_iff_ne_empty.mpr hBempty)
    have hpackingB : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements B) := by
      intro p hp q hq hpq
      exact S.tilesOn.2.1 (hBS hp) (hBS hq) hpq
    have hBvertices : Tiling.AxisParallel.properVertices
        (Tiling.AxisParallel.regularSupport K B) = ∅ :=
      transientSupport_hasNoProperVertex hXnonempty hXopen hXregular hconvphi hAB hUnion
        hAevent hBevent
    have hBclass := noProperVertexSupport_isAxisSlab_of_localBoundaryCross
      (Tiling.AxisParallel.regularSupport_isRegularOpen K B).1
      (Tiling.AxisParallel.regularSupport_isRegularOpen K B).2
      (Tiling.AxisParallel.regularSupport_localBoundaryCross hpackingB) hBvertices
    have hslabs := axisSlab_complement_inCarrier_of_classification hXregular
      (Tiling.AxisParallel.regularSupport_isRegularOpen K A).1
      (Tiling.AxisParallel.regularSupport_isRegularOpen K B).1
      (Tiling.AxisParallel.regularSupport_isRegularOpen K A).2 hSupportCover
      hSupportDisjoint.aedisjoint hBsupportNonempty hBclass
    rcases hslabs with ⟨Y0, Y1, hY0open, hY1open, hY0reg, hY1reg,
        hSupportA, hSupportB⟩ | ⟨hXuniv, Y0, Y1, hY0open, hY1open, hY0reg,
        hY1reg, hSupportA, hSupportB⟩
    · have hsat := verticalPlates_saturated_of_slabPartition K hUnion hSupportDisjoint
        hY0reg hY1reg hSupportA hSupportB
      refine ⟨phi, {
        persistent := A
        transient := B
        persistent_subset := hAS
        transient_subset := hBS
        disjoint := hAB
        union_eq := hUnion
        persistent_eventuallyMem := hAevent
        transient_eventuallyNotMem := hBevent
        orientation := Tiling.AxisParallel.Axis.vertical
        persistentBase := Y0
        transientBase := Y1
        persistentBase_open := hY0open
        transientBase_open := hY1open
        persistentBase_regular := hY0reg
        transientBase_regular := hY1reg
        persistentSupport_vertical := fun _ ↦ hSupportA
        transientSupport_vertical := fun _ ↦ hSupportB
        persistentSupport_horizontal := by intro h; cases h
        transientSupport_horizontal := by intro h; cases h
        horizontal_requires_plane := by intro h; cases h
        verticalPersistent_plateSaturated := fun _ ↦ hsat.1
        verticalTransient_plateSaturated := fun _ ↦ hsat.2
        horizontalPersistent_plateSaturated := by intro h; cases h
        horizontalTransient_plateSaturated := by intro h; cases h
      }, hphi⟩
    · have hSwapSupportA : Tiling.AxisParallel.regularSupport K.coordinateSwap
          (Tiling.AxisParallel.coordinateSwap '' A) =
          {z : Tiling.Plane | z.re ∈ Y0} := by
        rw [Tiling.AxisParallel.regularSupport_coordinateSwap, hSupportA]
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          simpa using hw
        · intro hz
          refine ⟨Tiling.AxisParallel.coordinateSwap z, ?_,
            Tiling.AxisParallel.coordinateSwap_apply_apply z⟩
          simpa using hz
      have hSwapSupportB : Tiling.AxisParallel.regularSupport K.coordinateSwap
          (Tiling.AxisParallel.coordinateSwap '' B) =
          {z : Tiling.Plane | z.re ∈ Y1} := by
        rw [Tiling.AxisParallel.regularSupport_coordinateSwap, hSupportB]
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          simpa using hw
        · intro hz
          refine ⟨Tiling.AxisParallel.coordinateSwap z, ?_,
            Tiling.AxisParallel.coordinateSwap_apply_apply z⟩
          simpa using hz
      have hSwapUnion : Tiling.AxisParallel.coordinateSwap '' A ∪
          Tiling.AxisParallel.coordinateSwap '' B =
          Tiling.AxisParallel.coordinateSwap '' (S.centres : Set Tiling.Plane) := by
        rw [← Set.image_union, hUnion]
      have hSwapDisjoint : Disjoint
          (Tiling.AxisParallel.regularSupport K.coordinateSwap
            (Tiling.AxisParallel.coordinateSwap '' A))
          (Tiling.AxisParallel.regularSupport K.coordinateSwap
            (Tiling.AxisParallel.coordinateSwap '' B)) := by
        rw [Tiling.AxisParallel.regularSupport_coordinateSwap,
          Tiling.AxisParallel.regularSupport_coordinateSwap]
        exact hSupportDisjoint.image
          Tiling.AxisParallel.coordinateSwap.injective.injOn
          (subset_univ _) (subset_univ _)
      have hsat := verticalPlates_saturated_of_slabPartition K.coordinateSwap hSwapUnion
        hSwapDisjoint hY0reg hY1reg hSwapSupportA hSwapSupportB
      refine ⟨phi, {
        persistent := A
        transient := B
        persistent_subset := hAS
        transient_subset := hBS
        disjoint := hAB
        union_eq := hUnion
        persistent_eventuallyMem := hAevent
        transient_eventuallyNotMem := hBevent
        orientation := Tiling.AxisParallel.Axis.horizontal
        persistentBase := Y0
        transientBase := Y1
        persistentBase_open := hY0open
        transientBase_open := hY1open
        persistentBase_regular := hY0reg
        transientBase_regular := hY1reg
        persistentSupport_vertical := by intro h; cases h
        transientSupport_vertical := by intro h; cases h
        persistentSupport_horizontal := fun _ ↦ hSupportA
        transientSupport_horizontal := fun _ ↦ hSupportB
        horizontal_requires_plane := fun _ ↦ hXuniv
        verticalPersistent_plateSaturated := by intro h; cases h
        verticalTransient_plateSaturated := by intro h; cases h
        horizontalPersistent_plateSaturated := fun _ ↦ hsat.1
        horizontalTransient_plateSaturated := fun _ ↦ hsat.2
      }, hphi⟩



/-- Restrict a persistent/transient split along a strictly monotone subsequence. -/
noncomputable def PersistentTransientSplit.subsequence
    {K : Region} {X : Set ℝ}
    {U : ℕ → Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    {S : Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    (D : PersistentTransientSplit K X U S) (phi : ℕ → ℕ)
    (hphi : StrictMono phi) : PersistentTransientSplit K X (U ∘ phi) S where
  persistent := D.persistent
  transient := D.transient
  persistent_subset := D.persistent_subset
  transient_subset := D.transient_subset
  disjoint := D.disjoint
  union_eq := D.union_eq
  persistent_eventuallyMem a ha :=
    (D.persistent_eventuallyMem a ha).filter_mono hphi.tendsto_atTop
  transient_eventuallyNotMem b hb :=
    (D.transient_eventuallyNotMem b hb).filter_mono hphi.tendsto_atTop
  orientation := D.orientation
  persistentBase := D.persistentBase
  transientBase := D.transientBase
  persistentBase_open := D.persistentBase_open
  transientBase_open := D.transientBase_open
  persistentBase_regular := D.persistentBase_regular
  transientBase_regular := D.transientBase_regular
  persistentSupport_vertical := D.persistentSupport_vertical
  transientSupport_vertical := D.transientSupport_vertical
  persistentSupport_horizontal := D.persistentSupport_horizontal
  transientSupport_horizontal := D.transientSupport_horizontal
  horizontal_requires_plane := D.horizontal_requires_plane
  verticalPersistent_plateSaturated := D.verticalPersistent_plateSaturated
  verticalTransient_plateSaturated := D.verticalTransient_plateSaturated
  horizontalPersistent_plateSaturated := D.horizontalPersistent_plateSaturated
  horizontalTransient_plateSaturated := D.horizontalTransient_plateSaturated

private theorem vadd_cylinder_re (g : Tiling.Plane) (Y : Set ℝ) :
    g +ᵥ ({z : Tiling.Plane | z.re ∈ Y} : Set Tiling.Plane) =
      {z : Tiling.Plane | z.re ∈ g.re +ᵥ Y} := by
  ext z
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, mem_ofPred_eq, Complex.add_re,
    Complex.neg_re, vadd_eq_add]

private theorem vadd_cylinder_im (g : Tiling.Plane) (Y : Set ℝ) :
    g +ᵥ ({z : Tiling.Plane | z.im ∈ Y} : Set Tiling.Plane) =
      {z : Tiling.Plane | z.im ∈ g.im +ᵥ Y} := by
  ext z
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, mem_ofPred_eq, Complex.add_im,
    Complex.neg_im, vadd_eq_add]

private theorem regularSupport_disjoint_of_partition
    {K : Region} {X : Set ℝ} {T A B : Set Tiling.Plane}
    (hUnion : A ∪ B = T) (hAB : Disjoint A B)
    (hTile : TilesOn K T {z : Tiling.Plane | z.re ∈ X}) :
    Disjoint (regularSupport K A) (regularSupport K B) := by
  let parts : Bool → Set Tiling.Plane := fun b ↦ if b then B else A
  have hp : Set.PairwiseDisjoint Set.univ parts := by
    intro i _ j _ hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hAB
    · exact (by
        change Disjoint B A
        exact hAB.symm)
    · exact (hij rfl).elim
  have hu : (⋃ i, parts i) = T := by
    rw [show (⋃ i, parts i) = A ∪ B by ext z; simp [parts], hUnion]
  have hd := (regularSupport_pairwiseDisjoint parts hp hu hTile).1
    (Set.mem_univ false) (Set.mem_univ true) (by decide)
  exact hd

/-- Translate a persistent/transient split by an essential period of its carrier. -/
noncomputable def PersistentTransientSplit.translate
    {K : Region} {X : Set ℝ}
    {U : ℕ → Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    {S : Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    (D : PersistentTransientSplit K X U S)
    (gamma : aePeriodGroup ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane)) :
    PersistentTransientSplit K X
      (fun n ↦ Topology.TilingSpace.translate gamma (U n))
      (Topology.TilingSpace.translate gamma S) := by
  let g : Tiling.Plane := gamma
  let A := g +ᵥ D.persistent
  let B := g +ᵥ D.transient
  have hcentres :
      ((Topology.TilingSpace.translate gamma S).centres : Set Tiling.Plane) =
        g +ᵥ (S.centres : Set Tiling.Plane) := by
    ext z
    change z ∈ (fun x : Tiling.Plane ↦ x + g) '' (S.centres : Set Tiling.Plane) ↔
      z ∈ g +ᵥ (S.centres : Set Tiling.Plane)
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simpa only [vadd_eq_add] using (add_comm g x)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simpa only [vadd_eq_add] using (add_comm x g)⟩
  have hAevent : ∀ a ∈ A, ∀ᶠ n in Filter.atTop,
      a ∈ (((Topology.TilingSpace.translate gamma (U n)).centres) : Set Tiling.Plane) := by
    rintro a ⟨a₀, ha₀, rfl⟩
    filter_upwards [D.persistent_eventuallyMem a₀ ha₀] with n hn
    exact ⟨a₀, hn, by simp [g, add_comm]⟩
  have hBevent : ∀ b ∈ B, ∀ᶠ n in Filter.atTop,
      b ∉ (((Topology.TilingSpace.translate gamma (U n)).centres) : Set Tiling.Plane) := by
    rintro b ⟨b₀, hb₀, rfl⟩
    filter_upwards [D.transient_eventuallyNotMem b₀ hb₀] with n hn
    rintro ⟨c, hc, heq⟩
    apply hn
    have : c = b₀ := by
      apply add_right_cancel (b := g)
      simpa [g, add_comm, add_left_comm] using heq
    simpa [this] using hc
  have hUnion : A ∪ B =
      ((Topology.TilingSpace.translate gamma S).centres : Set Tiling.Plane) := by
    rw [hcentres, ← D.union_eq]
    ext z
    simp [A, B, Set.mem_vadd_set_iff_neg_vadd_mem]
  have hDisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro z hzA hzB
    dsimp [A] at hzA
    dsimp [B] at hzB
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzA hzB
    exact Set.disjoint_left.1 D.disjoint hzA hzB
  have hSupportDisjoint : Disjoint (regularSupport K A) (regularSupport K B) :=
    regularSupport_disjoint_of_partition hUnion hDisjoint
      (Topology.TilingSpace.translate gamma S).tilesOn
  refine {
    persistent := A
    transient := B
    persistent_subset := by rw [hcentres]; exact vadd_set_mono D.persistent_subset
    transient_subset := by rw [hcentres]; exact vadd_set_mono D.transient_subset
    disjoint := hDisjoint
    union_eq := hUnion
    persistent_eventuallyMem := hAevent
    transient_eventuallyNotMem := hBevent
    orientation := D.orientation
    persistentBase := D.orientation.transverseCoord g +ᵥ D.persistentBase
    transientBase := D.orientation.transverseCoord g +ᵥ D.transientBase
    persistentBase_open := D.persistentBase_open.vadd _
    transientBase_open := D.transientBase_open.vadd _
    persistentBase_regular := by rw [closure_vadd, interior_vadd, D.persistentBase_regular]
    transientBase_regular := by rw [closure_vadd, interior_vadd, D.transientBase_regular]
    persistentSupport_vertical := ?_
    transientSupport_vertical := ?_
    persistentSupport_horizontal := ?_
    transientSupport_horizontal := ?_
    horizontal_requires_plane := D.horizontal_requires_plane
    verticalPersistent_plateSaturated := ?_
    verticalTransient_plateSaturated := ?_
    horizontalPersistent_plateSaturated := ?_
    horizontalTransient_plateSaturated := ?_ }
  · intro ho
    dsimp [A]
    rw [regularSupport_vadd, D.persistentSupport_vertical ho, vadd_cylinder_re]
    simp [ho, Axis.transverseCoord]
  · intro ho
    dsimp [B]
    rw [regularSupport_vadd, D.transientSupport_vertical ho, vadd_cylinder_re]
    simp [ho, Axis.transverseCoord]
  · intro ho
    dsimp [A]
    rw [regularSupport_vadd, D.persistentSupport_horizontal ho, vadd_cylinder_im]
    simp [ho, Axis.transverseCoord]
  · intro ho
    dsimp [B]
    rw [regularSupport_vadd, D.transientSupport_horizontal ho, vadd_cylinder_im]
    simp [ho, Axis.transverseCoord]
  · intro ho
    have hsA : regularSupport K A = {z : Tiling.Plane |
        z.re ∈ D.orientation.transverseCoord g +ᵥ D.persistentBase} := by
      dsimp [A]
      rw [regularSupport_vadd, D.persistentSupport_vertical ho, vadd_cylinder_re]
      simp [ho, Axis.transverseCoord]
    have hsB : regularSupport K B = {z : Tiling.Plane |
        z.re ∈ D.orientation.transverseCoord g +ᵥ D.transientBase} := by
      dsimp [B]
      rw [regularSupport_vadd, D.transientSupport_vertical ho, vadd_cylinder_re]
      simp [ho, Axis.transverseCoord]
    exact (verticalPlates_saturated_of_slabPartition K hUnion hSupportDisjoint
      (by rw [closure_vadd, interior_vadd, D.persistentBase_regular])
      (by rw [closure_vadd, interior_vadd, D.transientBase_regular]) hsA hsB).1
  · intro ho
    have hsA : regularSupport K A = {z : Tiling.Plane |
        z.re ∈ D.orientation.transverseCoord g +ᵥ D.persistentBase} := by
      dsimp [A]
      rw [regularSupport_vadd, D.persistentSupport_vertical ho, vadd_cylinder_re]
      simp [ho, Axis.transverseCoord]
    have hsB : regularSupport K B = {z : Tiling.Plane |
        z.re ∈ D.orientation.transverseCoord g +ᵥ D.transientBase} := by
      dsimp [B]
      rw [regularSupport_vadd, D.transientSupport_vertical ho, vadd_cylinder_re]
      simp [ho, Axis.transverseCoord]
    exact (verticalPlates_saturated_of_slabPartition K hUnion hSupportDisjoint
      (by rw [closure_vadd, interior_vadd, D.persistentBase_regular])
      (by rw [closure_vadd, interior_vadd, D.transientBase_regular]) hsA hsB).2
  · intro ho
    have hsA : regularSupport K A = {z : Tiling.Plane |
        z.im ∈ D.orientation.transverseCoord g +ᵥ D.persistentBase} := by
      dsimp [A]
      rw [regularSupport_vadd, D.persistentSupport_horizontal ho, vadd_cylinder_im]
      simp [ho, Axis.transverseCoord]
    have hsB : regularSupport K B = {z : Tiling.Plane |
        z.im ∈ D.orientation.transverseCoord g +ᵥ D.transientBase} := by
      dsimp [B]
      rw [regularSupport_vadd, D.transientSupport_horizontal ho, vadd_cylinder_im]
      simp [ho, Axis.transverseCoord]
    have hSwapA : regularSupport K.coordinateSwap (coordinateSwap '' A) =
        {z : Tiling.Plane | z.re ∈ D.orientation.transverseCoord g +ᵥ D.persistentBase} := by
      rw [regularSupport_coordinateSwap, hsA]
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩; simpa using hw
      · intro hz; exact ⟨coordinateSwap z, by simpa using hz, coordinateSwap_apply_apply z⟩
    have hSwapB : regularSupport K.coordinateSwap (coordinateSwap '' B) =
        {z : Tiling.Plane | z.re ∈ D.orientation.transverseCoord g +ᵥ D.transientBase} := by
      rw [regularSupport_coordinateSwap, hsB]
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩; simpa using hw
      · intro hz; exact ⟨coordinateSwap z, by simpa using hz, coordinateSwap_apply_apply z⟩
    have hSwapUnion : coordinateSwap '' A ∪ coordinateSwap '' B = coordinateSwap ''
        ((Topology.TilingSpace.translate gamma S).centres : Set Tiling.Plane) := by
      rw [← Set.image_union, hUnion]
    have hSwapDisjoint : Disjoint
        (regularSupport K.coordinateSwap (coordinateSwap '' A))
        (regularSupport K.coordinateSwap (coordinateSwap '' B)) := by
      rw [regularSupport_coordinateSwap, regularSupport_coordinateSwap]
      exact hSupportDisjoint.image coordinateSwap.injective.injOn
        (subset_univ _) (subset_univ _)
    exact (verticalPlates_saturated_of_slabPartition K.coordinateSwap hSwapUnion
      hSwapDisjoint (by rw [closure_vadd, interior_vadd, D.persistentBase_regular])
      (by rw [closure_vadd, interior_vadd, D.transientBase_regular]) hSwapA hSwapB).1
  · intro ho
    have hsA : regularSupport K A = {z : Tiling.Plane |
        z.im ∈ D.orientation.transverseCoord g +ᵥ D.persistentBase} := by
      dsimp [A]
      rw [regularSupport_vadd, D.persistentSupport_horizontal ho, vadd_cylinder_im]
      simp [ho, Axis.transverseCoord]
    have hsB : regularSupport K B = {z : Tiling.Plane |
        z.im ∈ D.orientation.transverseCoord g +ᵥ D.transientBase} := by
      dsimp [B]
      rw [regularSupport_vadd, D.transientSupport_horizontal ho, vadd_cylinder_im]
      simp [ho, Axis.transverseCoord]
    have hSwapA : regularSupport K.coordinateSwap (coordinateSwap '' A) =
        {z : Tiling.Plane | z.re ∈ D.orientation.transverseCoord g +ᵥ D.persistentBase} := by
      rw [regularSupport_coordinateSwap, hsA]
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩; simpa using hw
      · intro hz; exact ⟨coordinateSwap z, by simpa using hz, coordinateSwap_apply_apply z⟩
    have hSwapB : regularSupport K.coordinateSwap (coordinateSwap '' B) =
        {z : Tiling.Plane | z.re ∈ D.orientation.transverseCoord g +ᵥ D.transientBase} := by
      rw [regularSupport_coordinateSwap, hsB]
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩; simpa using hw
      · intro hz; exact ⟨coordinateSwap z, by simpa using hz, coordinateSwap_apply_apply z⟩
    have hSwapUnion : coordinateSwap '' A ∪ coordinateSwap '' B = coordinateSwap ''
        ((Topology.TilingSpace.translate gamma S).centres : Set Tiling.Plane) := by
      rw [← Set.image_union, hUnion]
    have hSwapDisjoint : Disjoint
        (regularSupport K.coordinateSwap (coordinateSwap '' A))
        (regularSupport K.coordinateSwap (coordinateSwap '' B)) := by
      rw [regularSupport_coordinateSwap, regularSupport_coordinateSwap]
      exact hSupportDisjoint.image coordinateSwap.injective.injOn
        (subset_univ _) (subset_univ _)
    exact (verticalPlates_saturated_of_slabPartition K.coordinateSwap hSwapUnion
      hSwapDisjoint (by rw [closure_vadd, interior_vadd, D.persistentBase_regular])
      (by rw [closure_vadd, interior_vadd, D.transientBase_regular]) hSwapA hSwapB).2

end Tiling.AxisParallel.Continuous
