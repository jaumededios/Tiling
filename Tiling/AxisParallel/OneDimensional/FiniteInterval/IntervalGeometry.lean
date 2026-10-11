import Tiling.AxisParallel.Foundations.OneDimensionalTilings
import Mathlib.Topology.Order.Compact

/-!
# Geometry of finite unions of intervals

Finite interval presentations retain all original endpoints, including redundant ones.
Their translated endpoints are locally finite and cannot lie inside a distinct packed tile.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.OneDimensional.FiniteInterval

open Tiling.AxisParallel.Foundations

structure IntervalPresentation (B : Set ℝ) where
  n : ℕ
  left : Fin n → ℝ
  right : Fin n → ℝ
  lt : ∀ i, left i < right i
  union_eq : B = ⋃ i, Set.Ioo (left i) (right i)

noncomputable def IntervalPresentation.ofIsFiniteIntervalRegion
    {B : Set ℝ} (hB : IsFiniteIntervalRegion B) : IntervalPresentation B :=
  Classical.choice (show Nonempty (IntervalPresentation B) from by
    rcases hB with ⟨n, left, right, hlt, hEq⟩
    exact ⟨⟨n, left, right, hlt, hEq⟩⟩)

def IntervalPresentation.endpoints {B : Set ℝ} (P : IntervalPresentation B) : Finset ℝ := by
  classical
  exact (Finset.univ.image P.left) ∪ (Finset.univ.image P.right)

def IntervalPresentation.gapLengths {B : Set ℝ} (P : IntervalPresentation B) : Set ℝ :=
  {d | ∃ e₁ ∈ P.endpoints, ∃ e₂ ∈ P.endpoints, e₁ < e₂ ∧ d = e₂ - e₁}

def translatedEndpointSet {B : Set ℝ} (P : IntervalPresentation B) (L : Set ℝ) : Set ℝ :=
  L + (P.endpoints : Set ℝ)

theorem IntervalPresentation.isOpen {B : Set ℝ} (P : IntervalPresentation B) : IsOpen B := by
  rw [P.union_eq]
  exact isOpen_iUnion fun i ↦ isOpen_Ioo

theorem IntervalPresentation.isFiniteIntervalRegion {B : Set ℝ} (P : IntervalPresentation B) :
    IsFiniteIntervalRegion B := by
  exact ⟨P.n, P.left, P.right, P.lt, P.union_eq⟩

theorem IntervalPresentation.isBounded {B : Set ℝ} (P : IntervalPresentation B) :
    Bornology.IsBounded B := by
  rw [P.union_eq]
  exact (Bornology.isBounded_iUnion).2 fun i ↦ Metric.isBounded_Ioo (P.left i) (P.right i)

theorem IntervalPresentation.measurableSet {B : Set ℝ} (P : IntervalPresentation B) :
    MeasurableSet B :=
  (IntervalPresentation.isOpen P).measurableSet

theorem IntervalPresentation.volume_ne_top {B : Set ℝ} (P : IntervalPresentation B) :
    volume B ≠ ⊤ :=
  (IntervalPresentation.isBounded P).measure_lt_top.ne

theorem IntervalPresentation.closure_eq_iUnion_Icc {B : Set ℝ} (P : IntervalPresentation B) :
    closure B = ⋃ i, Set.Icc (P.left i) (P.right i) := by
  calc
    closure B = closure (⋃ i, Set.Ioo (P.left i) (P.right i)) :=
      congrArg closure P.union_eq
    _ = ⋃ i, closure (Set.Ioo (P.left i) (P.right i)) := by
      exact closure_iUnion_of_finite (fun i : Fin P.n ↦
        Set.Ioo (P.left i) (P.right i))
    _ = ⋃ i, Set.Icc (P.left i) (P.right i) := by
      congr 1
      funext i
      exact closure_Ioo (ne_of_lt (P.lt i))

theorem IntervalPresentation.endpoint_subset_closure {B : Set ℝ} (P : IntervalPresentation B) :
    (P.endpoints : Set ℝ) ⊆ closure B := by
  intro x hx
  simp only [IntervalPresentation.endpoints, Finset.coe_union, Finset.coe_image,
    Set.mem_union, Set.mem_image] at hx
  rw [IntervalPresentation.closure_eq_iUnion_Icc P, Set.mem_iUnion]
  rcases hx with hx | hx
  · obtain ⟨i, -, rfl⟩ := hx
    exact ⟨i, ⟨le_rfl, (P.lt i).le⟩⟩
  · obtain ⟨i, -, rfl⟩ := hx
    exact ⟨i, ⟨(P.lt i).le, le_rfl⟩⟩

theorem IntervalPresentation.closure_diff_subset_endpoints {B : Set ℝ}
    (P : IntervalPresentation B) : closure B \ B ⊆ (P.endpoints : Set ℝ) := by
  rintro x ⟨hxcl, hxB⟩
  rw [IntervalPresentation.closure_eq_iUnion_Icc P, Set.mem_iUnion] at hxcl
  obtain ⟨i, hxi⟩ := hxcl
  have hnotIoo : x ∉ Set.Ioo (P.left i) (P.right i) := by
    intro hx
    apply hxB
    rw [P.union_eq, Set.mem_iUnion]
    exact ⟨i, hx⟩
  have hxEq : x = P.left i ∨ x = P.right i := by
    rcases hxi with ⟨hl, hr⟩
    simp only [Set.mem_Ioo, not_and_or] at hnotIoo
    rcases hnotIoo with hnl | hnr
    · exact Or.inl (le_antisymm (le_of_not_gt hnl) hl)
    · exact Or.inr (le_antisymm hr (le_of_not_gt hnr))
  simp only [IntervalPresentation.endpoints, Finset.coe_union, Finset.coe_image,
    Set.mem_union, Set.mem_image]
  rcases hxEq with rfl | rfl
  · exact Or.inl ⟨i, Finset.mem_univ _, rfl⟩
  · exact Or.inr ⟨i, Finset.mem_univ _, rfl⟩

theorem IntervalPresentation.frontier_subset_endpoints {B : Set ℝ} (P : IntervalPresentation B) :
    frontier B ⊆ (P.endpoints : Set ℝ) := by
  rw [frontier, (IntervalPresentation.isOpen P).interior_eq]
  exact IntervalPresentation.closure_diff_subset_endpoints P

theorem IntervalPresentation.gapLengths_finite {B : Set ℝ} (P : IntervalPresentation B) :
    P.gapLengths.Finite := by
  let E : Set ℝ := P.endpoints
  have hE : E.Finite := P.endpoints.finite_toSet
  let D : Set ℝ := (fun q : ℝ × ℝ ↦ q.2 - q.1) '' (E ×ˢ E)
  have hD : D.Finite := (hE.prod hE).image _
  apply hD.subset
  rintro d ⟨e₁, he₁, e₂, he₂, -, rfl⟩
  exact ⟨(e₁, e₂), ⟨he₁, he₂⟩, rfl⟩

theorem IntervalPresentation.gapLengths_pos {B : Set ℝ} (P : IntervalPresentation B)
    {d : ℝ} (hd : d ∈ P.gapLengths) : 0 < d := by
  rcases hd with ⟨e₁, -, e₂, -, hlt, rfl⟩
  linarith

theorem IntervalPresentation.gapLengths_nonempty {B : Set ℝ} (P : IntervalPresentation B)
    (hB : B.Nonempty) : P.gapLengths.Nonempty := by
  obtain ⟨x, hx⟩ := hB
  rw [P.union_eq, Set.mem_iUnion] at hx
  obtain ⟨i, hxi⟩ := hx
  refine ⟨P.right i - P.left i, P.left i, ?_, P.right i, ?_, P.lt i, rfl⟩
  · rw [IntervalPresentation.endpoints, Finset.mem_union]
    exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  · rw [IntervalPresentation.endpoints, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

theorem IntervalPresentation.endpoints_nonempty {B : Set ℝ} (P : IntervalPresentation B)
    (hB : B.Nonempty) : P.endpoints.Nonempty := by
  obtain ⟨x, hx⟩ := hB
  rw [P.union_eq, Set.mem_iUnion] at hx
  obtain ⟨i, -⟩ := hx
  exact ⟨P.left i, by
    rw [IntervalPresentation.endpoints, Finset.mem_union]
    exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩

theorem mem_translatedEndpointSet_iff {B L : Set ℝ} (P : IntervalPresentation B) {x : ℝ} :
    x ∈ translatedEndpointSet P L ↔ ∃ l ∈ L, ∃ e ∈ P.endpoints, x = l + e := by
  rw [translatedEndpointSet]
  constructor
  · rintro ⟨l, hl, e, he, rfl⟩
    exact ⟨l, hl, e, he, rfl⟩
  · rintro ⟨l, hl, e, he, rfl⟩
    exact ⟨l, hl, e, he, rfl⟩

theorem translatedEndpointSet_boundedWindowFinite {B L : Set ℝ} (P : IntervalPresentation B)
    (hLlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (L ∩ Q).Finite) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q → (translatedEndpointSet P L ∩ Q).Finite := by
  intro Q hQ
  let E : Set ℝ := P.endpoints
  have hE : E.Finite := P.endpoints.finite_toSet
  have hprod : (L ∩ (Q - E)) ×ˢ E |>.Finite := by
    exact (hLlocal _ (isBounded_sub hQ hE.isBounded)).prod hE
  let add : ℝ × ℝ → ℝ := fun q ↦ q.1 + q.2
  apply (hprod.image add).subset
  rintro x ⟨hxtrans, hxQ⟩
  rw [mem_translatedEndpointSet_iff P] at hxtrans
  obtain ⟨l, hl, e, he, rfl⟩ := hxtrans
  refine ⟨(l, e), ⟨⟨hl, ?_⟩, he⟩, rfl⟩
  exact ⟨l + e, hxQ, e, he, by simp⟩

theorem endpoint_not_mem_other_openTile {B L : Set ℝ} (P : IntervalPresentation B)
    (hpack : Set.Pairwise L (AEDisjoint volume on ((· +ᵥ B) : ℝ → Set ℝ)))
    {l m e : ℝ} (hl : l ∈ L) (hm : m ∈ L) (hlm : l ≠ m) (he : e ∈ P.endpoints) :
    l + e ∉ m +ᵥ B := by
  intro hmem
  have hecl : e ∈ closure B := IntervalPresentation.endpoint_subset_closure P he
  have hcl : l + e ∈ closure (l +ᵥ B) := by
    rw [closure_vadd]
    exact ⟨e, hecl, by simp⟩
  have hopenB : IsOpen B := IntervalPresentation.isOpen P
  have hne : ((m +ᵥ B) ∩ (l +ᵥ B)).Nonempty :=
    (mem_closure_iff.mp hcl) (m +ᵥ B) (hopenB.vadd m) hmem
  have hpos : 0 < volume ((m +ᵥ B) ∩ (l +ᵥ B)) :=
    ((hopenB.vadd m).inter (hopenB.vadd l)).measure_pos volume hne
  have hzero := hpack hm hl hlm.symm
  exact hpos.ne' hzero

theorem IsFiniteIntervalRegion.isOpen {B : Set ℝ} (hB : IsFiniteIntervalRegion B) : IsOpen B :=
  IntervalPresentation.isOpen (IntervalPresentation.ofIsFiniteIntervalRegion hB)

theorem IsFiniteIntervalRegion.measure_ne_top {B : Set ℝ} (hB : IsFiniteIntervalRegion B) :
    volume B ≠ ⊤ :=
  IntervalPresentation.volume_ne_top (IntervalPresentation.ofIsFiniteIntervalRegion hB)

theorem IsFiniteIntervalRegion.extremeCollars {B : Set ℝ} (hB : IsFiniteIntervalRegion B)
    (hBpositive : 0 < (volume B).toReal) :
    ∃ a b etaLeft etaRight : ℝ, a < b ∧ 0 < etaLeft ∧ 0 < etaRight ∧
      B ⊆ Set.Icc a b ∧ Set.Ioo a (a + etaLeft) ⊆ B ∧
      Set.Ioo (b - etaRight) b ⊆ B := by
  let P := IntervalPresentation.ofIsFiniteIntervalRegion hB
  have hBne : B.Nonempty := by
    by_contra hn
    have hEmpty : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    rw [hEmpty] at hBpositive
    simp at hBpositive
  have hE : P.endpoints.Nonempty := IntervalPresentation.endpoints_nonempty P hBne
  let a : ℝ := P.endpoints.min' hE
  let b : ℝ := P.endpoints.max' hE
  have hleft_mem (i : Fin P.n) : P.left i ∈ P.endpoints := by
    rw [IntervalPresentation.endpoints, Finset.mem_union]
    exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hright_mem (i : Fin P.n) : P.right i ∈ P.endpoints := by
    rw [IntervalPresentation.endpoints, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have ha_left : ∃ i, a = P.left i := by
    have ha_mem : a ∈ P.endpoints := Finset.min'_mem _ hE
    rw [IntervalPresentation.endpoints, Finset.mem_union] at ha_mem
    rcases ha_mem with ha | ha
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ha
      exact ⟨i, hi.symm⟩
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ha
      exfalso
      have hmin := Finset.min'_le P.endpoints (P.left i) (hleft_mem i)
      dsimp only [a] at hi hmin
      rw [← hi] at hmin
      exact (not_lt_of_ge hmin) (P.lt i)
  have hb_right : ∃ i, b = P.right i := by
    have hb_mem : b ∈ P.endpoints := Finset.max'_mem _ hE
    rw [IntervalPresentation.endpoints, Finset.mem_union] at hb_mem
    rcases hb_mem with hb | hb
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hb
      exfalso
      have hmax := Finset.le_max' P.endpoints (P.right i) (hright_mem i)
      dsimp only [b] at hi hmax
      rw [← hi] at hmax
      exact (not_lt_of_ge hmax) (P.lt i)
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hb
      exact ⟨i, hi.symm⟩
  obtain ⟨iLeft, ha⟩ := ha_left
  obtain ⟨iRight, hb⟩ := hb_right
  have hab : a < b := by
    have hbmax := Finset.le_max' P.endpoints (P.right iLeft) (hright_mem iLeft)
    calc
      a = P.left iLeft := ha
      _ < P.right iLeft := P.lt iLeft
      _ ≤ b := hbmax
  let etaLeft := P.right iLeft - a
  let etaRight := b - P.left iRight
  have hetaLeft : 0 < etaLeft := by
    dsimp only [etaLeft]
    rw [ha]
    exact sub_pos.mpr (P.lt iLeft)
  have hetaRight : 0 < etaRight := by
    dsimp only [etaRight]
    rw [hb]
    exact sub_pos.mpr (P.lt iRight)
  refine ⟨a, b, etaLeft, etaRight, hab, hetaLeft, hetaRight, ?_, ?_, ?_⟩
  · intro x hx
    rw [P.union_eq, Set.mem_iUnion] at hx
    obtain ⟨i, hxi⟩ := hx
    have hamin := Finset.min'_le P.endpoints (P.left i) (hleft_mem i)
    have hbmax := Finset.le_max' P.endpoints (P.right i) (hright_mem i)
    exact ⟨le_trans hamin hxi.1.le, le_trans hxi.2.le hbmax⟩
  · have hsum : a + etaLeft = P.right iLeft := by
      dsimp only [etaLeft]
      ring
    rw [hsum]
    intro x hx
    rw [P.union_eq, Set.mem_iUnion]
    exact ⟨iLeft, by simpa [ha] using hx⟩
  · have hsub : b - etaRight = P.left iRight := by
      dsimp only [etaRight]
      ring
    rw [hsub]
    intro x hx
    rw [P.union_eq, Set.mem_iUnion]
    exact ⟨iRight, by simpa [hb] using hx⟩

theorem finiteInterval_lineTilesOn_centres_locallyFinite {B H X : Set ℝ}
    (hB : IsFiniteIntervalRegion B)
    (hBpositive : 0 < (volume B).toReal) (hTile : LineTilesOn B H X) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q → (H ∩ Q).Finite := by
  obtain ⟨_, _, _, _, hlocal, _⟩ :=
    linePacking_uniformlySeparated hTile
      (IsFiniteIntervalRegion.measure_ne_top hB) hBpositive
  exact hlocal

end Tiling.AxisParallel.OneDimensional.FiniteInterval

open Filter Set Topology

namespace Tiling.AxisParallel.Foundations.GenericSlices

open Tiling.AxisParallel
open Tiling.AxisParallel.OneDimensional

def ValidIntervalIndex {n : ℕ} (a b : Fin n → ℝ) :=
  {i : Fin n // a i ≤ b i}

def closedIntervalOf {n : ℕ} (a b : Fin n → ℝ)
    (i : ValidIntervalIndex a b) : Set ℝ := Icc (a i.1) (b i.1)

def IntervalsTouch {n : ℕ} (a b : Fin n → ℝ)
    (i j : ValidIntervalIndex a b) : Prop :=
  (closedIntervalOf a b i ∩ closedIntervalOf a b j).Nonempty

/-- Equivalence generated by overlap or touching of valid closed intervals. -/
def SameIntervalRun {n : ℕ} (a b : Fin n → ℝ)
    (i j : ValidIntervalIndex a b) : Prop :=
  Relation.EqvGen (IntervalsTouch a b) i j

/-- A merged presentation: its intervals are nonempty and distinct intervals
are separated by a genuine open gap.  Thus touching or overlapping closed
input intervals never survive as an artificial internal seam. -/
structure MaximalIntervalPresentation (B : Set ℝ) where
  n : ℕ
  left : Fin n → ℝ
  right : Fin n → ℝ
  lt : ∀ i, left i < right i
  pairwise_gap : ∀ i j, i ≠ j → right i < left j ∨ right j < left i
  union_eq : B = ⋃ i, Ioo (left i) (right i)
  closure_eq : closure B = ⋃ i, Icc (left i) (right i)

private theorem eqvGen_to_reflTransGen_of_symm
    {α : Type*} {r : α → α → Prop} (hsymm : Std.Symm r)
    {a b : α} (h : Relation.EqvGen r a b) : Relation.ReflTransGen r a b := by
  induction h with
  | rel x y hxy => exact .tail .refl hxy
  | refl x => exact .refl
  | symm x y _ ih =>
      let _ : Std.Symm r := hsymm
      exact symm_of (Relation.ReflTransGen r) ih
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

private theorem reflTransGen_to_eqvGen
    {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.EqvGen r a b := by
  induction h with
  | refl => exact .refl _
  | tail hxy hyz ih => exact .trans _ _ _ ih (.rel _ _ hyz)

private theorem restrict_touching_path
    {n : ℕ} (a b : Fin n → ℝ) (i : ValidIntervalIndex a b)
    {j k : ValidIntervalIndex a b}
    (hj : SameIntervalRun a b i j)
    (hjk : Relation.ReflTransGen (IntervalsTouch a b) j k) :
    Relation.ReflTransGen
      (fun p q => IntervalsTouch a b p q ∧ SameIntervalRun a b i p) j k := by
  induction hjk with
  | refl => exact .refl
  | tail hpq hqr ih =>
      apply Relation.ReflTransGen.tail ih
      refine ⟨hqr, ?_⟩
      exact Relation.EqvGen.trans _ j _ hj (reflTransGen_to_eqvGen hpq)

private theorem finiteIntervalRun_union_eq_hull_proof :
    (∀ {n : ℕ} (a b : Fin n → ℝ) (i : ValidIntervalIndex a b),
    ∃ l r : ℝ, l ≤ r ∧
      (⋃ j : {j : ValidIntervalIndex a b // SameIntervalRun a b i j},
          closedIntervalOf a b j.1) = Icc l r ∧
      (∀ j : ValidIntervalIndex a b, SameIntervalRun a b i j →
        l ≤ a j.1 ∧ b j.1 ≤ r) ∧
      (∃ j : ValidIntervalIndex a b,
          SameIntervalRun a b i j ∧ a j.1 = l) ∧
      ∃ j : ValidIntervalIndex a b,
          SameIntervalRun a b i j ∧ b j.1 = r) := by
  intro n a b i
  let t : Set (ValidIntervalIndex a b) := {j | SameIntervalRun a b i j}
  let U : Set ℝ := ⋃ j ∈ t, closedIntervalOf a b j
  let _ : Finite (ValidIntervalIndex a b) :=
    Finite.of_injective (fun j => j.1) Subtype.val_injective
  let _ : Finite ↑t := Finite.of_injective (fun j => j.1) Subtype.val_injective
  have htfinite : t.Finite := t.toFinite
  have hcompact : IsCompact U := by
    exact htfinite.isCompact_biUnion (fun _ _ => isCompact_Icc)
  have hnonempty : U.Nonempty := by
    refine ⟨a i.1, mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨Relation.EqvGen.refl i, ?_⟩⟩⟩
    exact ⟨le_rfl, i.2⟩
  have hpre : IsPreconnected U := by
    apply IsPreconnected.biUnion_of_reflTransGen
    · intro j _
      exact isPreconnected_Icc
    · intro j hj k hk
      apply restrict_touching_path a b i hj
      apply eqvGen_to_reflTransGen_of_symm
      · exact ⟨by
          intro p q hpq
          simpa only [IntervalsTouch, inter_comm] using hpq⟩
      exact Relation.EqvGen.trans _ i _ (Relation.EqvGen.symm _ _ hj) hk
  have hconnected : IsConnected U := ⟨hnonempty, hpre⟩
  let l := sInf U
  let r := sSup U
  have hUeq : U = Icc l r := eq_Icc_of_connected_compact hconnected hcompact
  have hlU : l ∈ U := hcompact.sInf_mem hnonempty
  have hrU : r ∈ U := hcompact.sSup_mem hnonempty
  have hlleast : IsLeast U l := hcompact.isLeast_sInf hnonempty
  have hrgreatest : IsGreatest U r := hcompact.isGreatest_sSup hnonempty
  have hlr : l ≤ r := hlleast.2 hrU
  refine ⟨l, r, hlr, ?_, ?_, ?_, ?_⟩
  · rw [← hUeq]
    ext x
    constructor
    · rintro hx
      rcases mem_iUnion.1 hx with ⟨j, hxj⟩
      exact mem_iUnion.2 ⟨j.1, mem_iUnion.2 ⟨j.2, hxj⟩⟩
    · rintro hx
      rcases mem_iUnion.1 hx with ⟨j, hxj⟩
      rcases mem_iUnion.1 hxj with ⟨hji, hxj⟩
      exact mem_iUnion.2 ⟨⟨j, hji⟩, hxj⟩
  · intro j hj
    have hjsub : closedIntervalOf a b j ⊆ U := by
      intro x hx
      exact mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hj, hx⟩⟩
    exact ⟨hlleast.2 (hjsub ⟨le_rfl, j.2⟩),
      hrgreatest.2 (hjsub ⟨j.2, le_rfl⟩)⟩
  · rcases mem_iUnion.1 hlU with ⟨j, hj⟩
    rcases mem_iUnion.1 hj with ⟨hji, hjl⟩
    refine ⟨j, hji, le_antisymm hjl.1 ?_⟩
    exact hlleast.2 (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hji, ⟨le_rfl, j.2⟩⟩⟩)
  · rcases mem_iUnion.1 hrU with ⟨j, hj⟩
    rcases mem_iUnion.1 hj with ⟨hji, hjr⟩
    refine ⟨j, hji, le_antisymm ?_ hjr.2⟩
    exact hrgreatest.2 (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hji, ⟨j.2, le_rfl⟩⟩⟩)

private theorem distinctIntervalRuns_strictGap_proof :
    (∀ {n : ℕ} (a b : Fin n → ℝ)
      (i j : ValidIntervalIndex a b),
    ¬ SameIntervalRun a b i j →
    ∀ {li ri lj rj : ℝ},
      (⋃ k : {k : ValidIntervalIndex a b // SameIntervalRun a b i k},
          closedIntervalOf a b k.1) = Icc li ri →
      (⋃ k : {k : ValidIntervalIndex a b // SameIntervalRun a b j k},
          closedIntervalOf a b k.1) = Icc lj rj →
      ri < lj ∨ rj < li) := by
  intro n a b i j hij li ri lj rj hi hj
  have hdisj : Disjoint (Icc li ri) (Icc lj rj) := by
    rw [← hi, ← hj]
    apply Set.disjoint_left.2
    intro x hxi hxj
    rcases mem_iUnion.1 hxi with ⟨k, hxk⟩
    rcases mem_iUnion.1 hxj with ⟨l, hxl⟩
    have htouch : IntervalsTouch a b k.1 l.1 := ⟨x, hxk, hxl⟩
    apply hij
    exact Relation.EqvGen.trans _ k.1 _ k.2
      (Relation.EqvGen.trans _ l.1 _ (.rel _ _ htouch)
        (Relation.EqvGen.symm _ _ l.2))
  have hiri : li ≤ ri := by
    have hx : a i.1 ∈ ⋃ k : {k : ValidIntervalIndex a b //
        SameIntervalRun a b i k}, closedIntervalOf a b k.1 := by
      exact mem_iUnion.2 ⟨⟨i, .refl i⟩, ⟨le_rfl, i.2⟩⟩
    rw [hi] at hx
    exact hx.1.trans hx.2
  have hjrj : lj ≤ rj := by
    have hx : a j.1 ∈ ⋃ k : {k : ValidIntervalIndex a b //
        SameIntervalRun a b j k}, closedIntervalOf a b k.1 := by
      exact mem_iUnion.2 ⟨⟨j, .refl j⟩, ⟨le_rfl, j.2⟩⟩
    rw [hj] at hx
    exact hx.1.trans hx.2
  by_contra hgap
  push Not at hgap
  have hx1 : max li lj ∈ Icc li ri := by
    constructor
    · exact le_max_left _ _
    · exact max_le hiri hgap.1
  have hx2 : max li lj ∈ Icc lj rj := by
    constructor
    · exact le_max_right _ _
    · exact max_le hgap.2 hjrj
  exact Set.disjoint_left.1 hdisj hx1 hx2

private theorem separatedIntervals_interior_closure
    (s : Finset (ℝ × ℝ))
    (hlt : ∀ p ∈ s, p.1 < p.2)
    (hgap : ∀ p ∈ s, ∀ q ∈ s, p ≠ q →
      p.2 < q.1 ∨ q.2 < p.1) :
    interior (⋃ p ∈ s, Icc p.1 p.2) = ⋃ p ∈ s, Ioo p.1 p.2 ∧
      closure (⋃ p ∈ s, Ioo p.1 p.2) = ⋃ p ∈ s, Icc p.1 p.2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hltp : p.1 < p.2 := hlt p (Finset.mem_insert_self ..)
      have hlts : ∀ q ∈ s, q.1 < q.2 := by
        intro q hq
        exact hlt q (Finset.mem_insert_of_mem hq)
      have hgaps : ∀ q ∈ s, ∀ r ∈ s, q ≠ r →
          q.2 < r.1 ∨ r.2 < q.1 := by
        intro q hq r hr hqr
        exact hgap q (Finset.mem_insert_of_mem hq) r
          (Finset.mem_insert_of_mem hr) hqr
      obtain ⟨hinterior, hclosure⟩ := ih hlts hgaps
      have hclosedSubtype : IsClosed (⋃ q : ↑s, Icc q.1.1 q.1.2) :=
        isClosed_iUnion_of_finite fun _ => isClosed_Icc
      have hclosedRest : IsClosed (⋃ q ∈ s, Icc q.1 q.2) := by
        convert hclosedSubtype using 1
        ext x
        simp
      have hpdisj : Disjoint (Icc p.1 p.2) (⋃ q ∈ s, Icc q.1 q.2) := by
        rw [Set.disjoint_iUnion_right]
        intro q
        rw [Set.disjoint_iUnion_right]
        intro hq
        apply Set.disjoint_left.2
        intro x hxp hxq
        have hpq := hgap p (Finset.mem_insert_self ..) q
          (Finset.mem_insert_of_mem hq) (fun hpq => hp (hpq ▸ hq))
        rcases hpq with hpq | hqp
        · exact (not_lt_of_ge hxq.1) (hxp.2.trans_lt hpq)
        · exact (not_lt_of_ge hxp.1) (hxq.2.trans_lt hqp)
      constructor
      · rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert]
        rw [interior_union_of_disjoint_closure]
        · rw [interior_Icc, hinterior]
        · simpa only [isClosed_Icc.closure_eq, hclosedRest.closure_eq] using hpdisj
      · rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert]
        rw [closure_union, closure_Ioo (ne_of_lt hltp), hclosure]

private theorem separatedIntervals_interior
    (s : Finset (ℝ × ℝ))
    (hle : ∀ p ∈ s, p.1 ≤ p.2)
    (hgap : ∀ p ∈ s, ∀ q ∈ s, p ≠ q →
      p.2 < q.1 ∨ q.2 < p.1) :
    interior (⋃ p ∈ s, Icc p.1 p.2) = ⋃ p ∈ s, Ioo p.1 p.2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hlep := hle p (Finset.mem_insert_self ..)
      have hles : ∀ q ∈ s, q.1 ≤ q.2 := fun q hq =>
        hle q (Finset.mem_insert_of_mem hq)
      have hgaps : ∀ q ∈ s, ∀ r ∈ s, q ≠ r →
          q.2 < r.1 ∨ r.2 < q.1 := fun q hq r hr hqr =>
        hgap q (Finset.mem_insert_of_mem hq) r
          (Finset.mem_insert_of_mem hr) hqr
      have hclosedSubtype : IsClosed (⋃ q : ↑s, Icc q.1.1 q.1.2) :=
        isClosed_iUnion_of_finite fun _ => isClosed_Icc
      have hclosedRest : IsClosed (⋃ q ∈ s, Icc q.1 q.2) := by
        convert hclosedSubtype using 1
        ext x
        simp
      have hpdisj : Disjoint (Icc p.1 p.2) (⋃ q ∈ s, Icc q.1 q.2) := by
        rw [Set.disjoint_iUnion_right]
        intro q
        rw [Set.disjoint_iUnion_right]
        intro hq
        apply Set.disjoint_left.2
        intro x hxp hxq
        rcases hgap p (Finset.mem_insert_self ..) q
          (Finset.mem_insert_of_mem hq) (fun hpq => hp (hpq ▸ hq)) with hpq | hqp
        · exact (not_lt_of_ge hxq.1) (hxp.2.trans_lt hpq)
        · exact (not_lt_of_ge hxp.1) (hxq.2.trans_lt hqp)
      rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert,
        interior_union_of_disjoint_closure]
      · rw [interior_Icc, ih hles hgaps]
      · simpa only [isClosed_Icc.closure_eq, hclosedRest.closure_eq] using hpdisj

private theorem finiteClosedIntervals_merge_proof :
    (∀ {n : ℕ} (a b : Fin n → ℝ),
    Nonempty (MaximalIntervalPresentation
      (interior (⋃ i, Icc (a i) (b i))))) := by
  classical
  intro n a b
  let V := ValidIntervalIndex a b
  let _ : Finite V := Finite.of_injective (fun j : V => j.1) Subtype.val_injective
  let _ : Fintype V := Fintype.ofFinite V
  choose l r hlr hrun hbounds hleft hright using
    fun i : V => finiteIntervalRun_union_eq_hull_proof a b i
  let hull : V → ℝ × ℝ := fun i => (l i, r i)
  let allPairs : Finset (ℝ × ℝ) := Finset.univ.image hull
  let goodPairs : Finset (ℝ × ℝ) := allPairs.filter fun p => p.1 < p.2
  have hull_eq_of_run {i j : V} (hij : SameIntervalRun a b i j) : hull i = hull j := by
    have hclasses :
        (⋃ k : {k : V // SameIntervalRun a b i k}, closedIntervalOf a b k.1) =
          ⋃ k : {k : V // SameIntervalRun a b j k}, closedIntervalOf a b k.1 := by
      ext x
      constructor
      · rintro hx
        rcases mem_iUnion.1 hx with ⟨k, hxk⟩
        exact mem_iUnion.2 ⟨⟨k.1,
          Relation.EqvGen.trans _ i _ (Relation.EqvGen.symm _ _ hij) k.2⟩, hxk⟩
      · rintro hx
        rcases mem_iUnion.1 hx with ⟨k, hxk⟩
        exact mem_iUnion.2 ⟨⟨k.1, Relation.EqvGen.trans _ j _ hij k.2⟩, hxk⟩
    have hIcc : Icc (l i) (r i) = Icc (l j) (r j) := by
      rw [← hrun i, ← hrun j]
      exact hclasses
    have hli_mem : l i ∈ Icc (l j) (r j) := by
      rw [← hIcc]
      exact ⟨le_rfl, hlr i⟩
    have hlj_mem : l j ∈ Icc (l i) (r i) := by
      rw [hIcc]
      exact ⟨le_rfl, hlr j⟩
    have hri_mem : r i ∈ Icc (l j) (r j) := by
      rw [← hIcc]
      exact ⟨hlr i, le_rfl⟩
    have hrj_mem : r j ∈ Icc (l i) (r i) := by
      rw [hIcc]
      exact ⟨hlr j, le_rfl⟩
    apply Prod.ext
    · change l i = l j
      exact le_antisymm hlj_mem.1 hli_mem.1
    · change r i = r j
      exact le_antisymm hri_mem.2 hrj_mem.2
  have hall_le : ∀ p ∈ allPairs, p.1 ≤ p.2 := by
    intro p hp
    rcases Finset.mem_image.1 hp with ⟨i, _, rfl⟩
    exact hlr i
  have hall_gap : ∀ p ∈ allPairs, ∀ q ∈ allPairs, p ≠ q →
      p.2 < q.1 ∨ q.2 < p.1 := by
    intro p hp q hq hpq
    rcases Finset.mem_image.1 hp with ⟨i, _, rfl⟩
    rcases Finset.mem_image.1 hq with ⟨j, _, rfl⟩
    apply distinctIntervalRuns_strictGap_proof a b i j
    · intro hij
      exact hpq (hull_eq_of_run hij)
    · exact hrun i
    · exact hrun j
  have hunion : (⋃ i, Icc (a i) (b i)) = ⋃ p ∈ allPairs, Icc p.1 p.2 := by
    ext x
    constructor
    · rintro hx
      rcases mem_iUnion.1 hx with ⟨i, hxi⟩
      let vi : V := ⟨i, hxi.1.trans hxi.2⟩
      apply mem_iUnion.2
      refine ⟨hull vi, mem_iUnion.2 ⟨Finset.mem_image.2 ⟨vi, Finset.mem_univ _, rfl⟩, ?_⟩⟩
      rw [← hrun vi]
      exact mem_iUnion.2 ⟨⟨vi, .refl vi⟩, hxi⟩
    · rintro hx
      rcases mem_iUnion.1 hx with ⟨p, hxp⟩
      rcases mem_iUnion.1 hxp with ⟨hp, hxp⟩
      rcases Finset.mem_image.1 hp with ⟨i, _, rfl⟩
      rw [← hrun i] at hxp
      rcases mem_iUnion.1 hxp with ⟨j, hxj⟩
      exact mem_iUnion.2 ⟨j.1.1, hxj⟩
  have hinteriorAll := separatedIntervals_interior allPairs hall_le hall_gap
  have hgood_lt : ∀ p ∈ goodPairs, p.1 < p.2 := by
    intro p hp
    exact (Finset.mem_filter.1 hp).2
  have hgood_gap : ∀ p ∈ goodPairs, ∀ q ∈ goodPairs, p ≠ q →
      p.2 < q.1 ∨ q.2 < p.1 := by
    intro p hp q hq hpq
    exact hall_gap p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 hpq
  obtain ⟨hinteriorGood, hclosureGood⟩ :=
    separatedIntervals_interior_closure goodPairs hgood_lt hgood_gap
  have hopenUnion :
      (⋃ p ∈ allPairs, Ioo p.1 p.2) = ⋃ p ∈ goodPairs, Ioo p.1 p.2 := by
    ext x
    constructor
    · rintro hx
      rcases mem_iUnion.1 hx with ⟨p, hxp⟩
      rcases mem_iUnion.1 hxp with ⟨hp, hxp⟩
      exact mem_iUnion.2 ⟨p, mem_iUnion.2
        ⟨Finset.mem_filter.2 ⟨hp, hxp.1.trans hxp.2⟩, hxp⟩⟩
    · rintro hx
      rcases mem_iUnion.1 hx with ⟨p, hxp⟩
      rcases mem_iUnion.1 hxp with ⟨hp, hxp⟩
      exact mem_iUnion.2 ⟨p, mem_iUnion.2 ⟨(Finset.mem_filter.1 hp).1, hxp⟩⟩
  let G := ↑goodPairs
  let e : G ≃ Fin (Fintype.card G) := Fintype.equivFin G
  let pick : Fin (Fintype.card G) → G := e.symm
  refine ⟨{
    n := Fintype.card G
    left := fun i => (pick i).1.1
    right := fun i => (pick i).1.2
    lt := fun i => hgood_lt (pick i) (pick i).2
    pairwise_gap := ?_
    union_eq := ?_
    closure_eq := ?_ }⟩
  · intro i j hij
    apply hgood_gap (pick i) (pick i).2 (pick j) (pick j).2
    intro hpick
    exact hij (e.symm.injective (Subtype.ext hpick))
  · calc
      interior (⋃ i, Icc (a i) (b i)) =
          interior (⋃ p ∈ allPairs, Icc p.1 p.2) := congrArg interior hunion
      _ = ⋃ p ∈ allPairs, Ioo p.1 p.2 := hinteriorAll
      _ = ⋃ p ∈ goodPairs, Ioo p.1 p.2 := hopenUnion
      _ = ⋃ i, Ioo (pick i).1.1 (pick i).1.2 := by
        ext x
        constructor
        · rintro hx
          rcases mem_iUnion.1 hx with ⟨p, hxp⟩
          rcases mem_iUnion.1 hxp with ⟨hp, hxp⟩
          let gp : G := ⟨p, hp⟩
          exact mem_iUnion.2 ⟨e gp, by simpa [pick, gp] using hxp⟩
        · rintro hx
          rcases mem_iUnion.1 hx with ⟨i, hxi⟩
          exact mem_iUnion.2 ⟨pick i, mem_iUnion.2 ⟨(pick i).2, hxi⟩⟩
  · have hbase : interior (⋃ i, Icc (a i) (b i)) =
        ⋃ p ∈ goodPairs, Ioo p.1 p.2 := by
      calc
        _ = interior (⋃ p ∈ allPairs, Icc p.1 p.2) := congrArg interior hunion
        _ = ⋃ p ∈ allPairs, Ioo p.1 p.2 := hinteriorAll
        _ = _ := hopenUnion
    rw [hbase, hclosureGood]
    ext x
    constructor
    · rintro hx
      rcases mem_iUnion.1 hx with ⟨p, hxp⟩
      rcases mem_iUnion.1 hxp with ⟨hp, hxp⟩
      let gp : G := ⟨p, hp⟩
      exact mem_iUnion.2 ⟨e gp, by simpa [pick, gp] using hxp⟩
    · rintro hx
      rcases mem_iUnion.1 hx with ⟨i, hxi⟩
      exact mem_iUnion.2 ⟨pick i, mem_iUnion.2 ⟨(pick i).2, hxi⟩⟩

theorem finiteClosedIntervals_merge :
    (∀ {n : ℕ} (a b : Fin n → ℝ),
    Nonempty (MaximalIntervalPresentation
      (interior (⋃ i, Icc (a i) (b i))))) :=
  finiteClosedIntervals_merge_proof

theorem finiteIntervalRun_union_eq_hull :
    (∀ {n : ℕ} (a b : Fin n → ℝ) (i : ValidIntervalIndex a b),
    ∃ l r : ℝ, l ≤ r ∧
      (⋃ j : {j : ValidIntervalIndex a b // SameIntervalRun a b i j},
          closedIntervalOf a b j.1) = Icc l r ∧
      (∀ j : ValidIntervalIndex a b, SameIntervalRun a b i j →
        l ≤ a j.1 ∧ b j.1 ≤ r) ∧
      (∃ j : ValidIntervalIndex a b,
          SameIntervalRun a b i j ∧ a j.1 = l) ∧
      ∃ j : ValidIntervalIndex a b,
          SameIntervalRun a b i j ∧ b j.1 = r) :=
  finiteIntervalRun_union_eq_hull_proof

theorem distinctIntervalRuns_strictGap :
    (∀ {n : ℕ} (a b : Fin n → ℝ)
      (i j : ValidIntervalIndex a b),
    ¬ SameIntervalRun a b i j →
    ∀ {li ri lj rj : ℝ},
      (⋃ k : {k : ValidIntervalIndex a b // SameIntervalRun a b i k},
          closedIntervalOf a b k.1) = Icc li ri →
      (⋃ k : {k : ValidIntervalIndex a b // SameIntervalRun a b j k},
          closedIntervalOf a b k.1) = Icc lj rj →
      ri < lj ∨ rj < li) :=
  distinctIntervalRuns_strictGap_proof

end Tiling.AxisParallel.Foundations.GenericSlices
