import Tiling.AxisParallel.OneDimensional.FiniteInterval.EndpointCoding
import Tiling.AxisParallel.OneDimensional.FiniteInterval.LocalRigidity

/-!
# Whole-line rigidity and periodicity

Finite endpoint alphabets and local rigidity give finitely many normalized
tilings. Recentring an infinite set of centres then yields a positive period.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel.OneDimensional.FiniteInterval

open Tiling.AxisParallel.Foundations

/-- A covered midpoint makes a consecutive translated-endpoint cell a raw tile-endpoint gap. -/
theorem consecutive_translatedEndpoint_gap_of_covered_midpoint
    {B L : Set ℝ} (P : IntervalPresentation B)
    (hpack : Set.Pairwise L
      (AEDisjoint volume on ((· +ᵥ B) : ℝ → Set ℝ)))
    {x y : ℝ}
    (hxy : ConsecutiveIn (translatedEndpointSet P L) x y)
    (hmid : ∃ l ∈ L, (x + y) / 2 ∈ l +ᵥ closure B) :
    y - x ∈ P.gapLengths := by
  let z : ℝ := (x + y) / 2
  obtain ⟨l, hl, hzcl⟩ := hmid
  have hxz : x < z := by dsimp [z]; linarith [hxy.2.2.1]
  have hzy : z < y := by dsimp [z]; linarith [hxy.2.2.1]
  have hzcl' : z - l ∈ closure B := by
    dsimp [z]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzcl
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using hzcl
  have hzB : z - l ∈ B := by
    by_contra hzB
    have he : z - l ∈ (P.endpoints : Set ℝ) :=
      P.closure_diff_subset_endpoints ⟨hzcl', hzB⟩
    have hzE : z ∈ translatedEndpointSet P L :=
      (mem_translatedEndpointSet_iff P).2
        ⟨l, hl, z - l, he, by ring⟩
    exact Set.disjoint_left.1 hxy.2.2.2 hzE ⟨hxz, hzy⟩
  rw [P.union_eq, Set.mem_iUnion] at hzB
  obtain ⟨i, hi⟩ := hzB
  have hleftEnd : P.left i ∈ P.endpoints := by
    rw [IntervalPresentation.endpoints, Finset.mem_union]
    exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hrightEnd : P.right i ∈ P.endpoints := by
    rw [IntervalPresentation.endpoints, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hleftE : l + P.left i ∈ translatedEndpointSet P L :=
    (mem_translatedEndpointSet_iff P).2
      ⟨l, hl, P.left i, hleftEnd, rfl⟩
  have hrightE : l + P.right i ∈ translatedEndpointSet P L :=
    (mem_translatedEndpointSet_iff P).2
      ⟨l, hl, P.right i, hrightEnd, rfl⟩
  have hleft_lt_z : l + P.left i < z := by linarith [hi.1]
  have hz_lt_right : z < l + P.right i := by linarith [hi.2]
  have hleft_le_x : l + P.left i ≤ x := by
    by_contra h
    have hxleft : x < l + P.left i := lt_of_not_ge h
    exact Set.disjoint_left.1 hxy.2.2.2 hleftE
      ⟨hxleft, lt_trans hleft_lt_z hzy⟩
  have hy_le_right : y ≤ l + P.right i := by
    by_contra h
    have hrighty : l + P.right i < y := lt_of_not_ge h
    exact Set.disjoint_left.1 hxy.2.2.2 hrightE
      ⟨lt_trans hxz hz_lt_right, hrighty⟩
  obtain ⟨m, hm, ex, hex, hxeq⟩ :=
    (mem_translatedEndpointSet_iff P).1 hxy.1
  obtain ⟨n, hn, ey, hey, hyeq⟩ :=
    (mem_translatedEndpointSet_iff P).1 hxy.2.1
  have hxOwned : ∃ ex ∈ P.endpoints, x = l + ex := by
    by_cases hxleft : x = l + P.left i
    · exact ⟨P.left i, hleftEnd, hxleft⟩
    · have hleft_lt_x : l + P.left i < x :=
        lt_of_le_of_ne hleft_le_x (Ne.symm hxleft)
      have hxOpen : x ∈ l +ᵥ B := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem, P.union_eq, Set.mem_iUnion]
        refine ⟨i, ?_⟩
        simp only [vadd_eq_add]
        constructor <;> linarith
      have hm_eq_l : m = l := by
        by_contra hml
        have hxNot := endpoint_not_mem_other_openTile P hpack hm hl hml hex
        exact hxNot (hxeq ▸ hxOpen)
      exact ⟨ex, hex, by simpa [hm_eq_l] using hxeq⟩
  have hyOwned : ∃ ey ∈ P.endpoints, y = l + ey := by
    by_cases hyright : y = l + P.right i
    · exact ⟨P.right i, hrightEnd, hyright⟩
    · have hy_lt_right : y < l + P.right i :=
        lt_of_le_of_ne hy_le_right hyright
      have hyOpen : y ∈ l +ᵥ B := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem, P.union_eq, Set.mem_iUnion]
        refine ⟨i, ?_⟩
        simp only [vadd_eq_add]
        constructor <;> linarith
      have hn_eq_l : n = l := by
        by_contra hnl
        have hyNot := endpoint_not_mem_other_openTile P hpack hn hl hnl hey
        exact hyNot (hyeq ▸ hyOpen)
      exact ⟨ey, hey, by simpa [hn_eq_l] using hyeq⟩
  obtain ⟨ex', hex', hxeq'⟩ := hxOwned
  obtain ⟨ey', hey', hyeq'⟩ := hyOwned
  refine ⟨ex', hex', ey', hey', ?_, ?_⟩
  · linarith [hxy.2.2.1]
  · linarith

/-- Whole-line coverage supplies the midpoint hypothesis for every consecutive endpoint cell. -/
theorem consecutive_translatedEndpoint_gap
    {B L : Set ℝ} (P : IntervalPresentation B)
    (hBpositive : 0 < (volume B).toReal) (hTile : LineTiles B L)
    {x y : ℝ} (hxy : ConsecutiveIn (translatedEndpointSet P L) x y) :
    y - x ∈ P.gapLengths := by
  have hsource :=
    (finiteOpenIntervals_source_iff_ae P.isFiniteIntervalRegion hBpositive).1 hTile
  have hmid : ∃ l ∈ L, (x + y) / 2 ∈ l +ᵥ closure B := by
    have hm : (x + y) / 2 ∈ ⋃ l : L, l.1 +ᵥ closure B := by
      rw [hsource.2.2]
      exact Set.mem_univ _
    rw [Set.mem_iUnion] at hm
    obtain ⟨l, hl⟩ := hm
    exact ⟨l.1, l.2, hl⟩
  exact consecutive_translatedEndpoint_gap_of_covered_midpoint
    P hTile.2.2.2.1 hxy hmid

/-- Uniform finite centre candidates for every normalized whole-line tiling. -/
theorem finite_centerCandidates
    {B : Set ℝ} (P : IntervalPresentation B)
    (hBpositive : 0 < (volume B).toReal)
    (radius : ℝ) (hradius : 0 ≤ radius) :
    ∃ F : Finset ℝ, ∀ (L : Set ℝ),
      LineTiles B L → 0 ∈ L →
      L ∩ Set.Icc (-radius) radius ⊆ (F : Set ℝ) := by
  have hBne : B.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hBempty
    rw [hBempty, measure_empty, ENNReal.toReal_zero] at hBpositive
    exact lt_irrefl 0 hBpositive
  obtain ⟨e₀, he₀⟩ := P.endpoints_nonempty hBne
  obtain ⟨E, hE⟩ := finite_candidates_of_gapAlphabet
    P.gapLengths_finite (fun a ha ↦ P.gapLengths_pos ha)
    e₀ radius hradius
  let F : Finset ℝ := E.image (fun e ↦ e - e₀)
  refine ⟨F, ?_⟩
  intro L hTile hzero l hl
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (translatedEndpointSet P L ∩ Q).Finite := by
    apply translatedEndpointSet_boundedWindowFinite P
    obtain ⟨_, _, _, _, hcentres, _⟩ := linePacking_uniformlySeparated
      hTile P.volume_ne_top hBpositive
    exact hcentres
  have heAnchor : e₀ ∈ translatedEndpointSet P L :=
    (mem_translatedEndpointSet_iff P).2 ⟨0, hzero, e₀, he₀, by simp⟩
  have hgap : ∀ x y, ConsecutiveIn (translatedEndpointSet P L) x y →
      y - x ∈ P.gapLengths := fun x y hxy ↦
    consecutive_translatedEndpoint_gap P hBpositive hTile hxy
  have hle : l ∈ Set.Icc (-radius) radius := hl.2
  have hendpoint : l + e₀ ∈ translatedEndpointSet P L :=
    (mem_translatedEndpointSet_iff P).2 ⟨l, hl.1, e₀, he₀, rfl⟩
  have hwindow : l + e₀ ∈ Set.Icc (e₀ - radius) (e₀ + radius) := by
    constructor <;> linarith [hle.1, hle.2]
  have hmemE : l + e₀ ∈ E := hE _ hlocal heAnchor hgap ⟨hendpoint, hwindow⟩
  rw [Finset.mem_coe, Finset.mem_image]
  exact ⟨l + e₀, hmemE, by ring⟩

theorem finite_normalized_localPatterns
    {B : Set ℝ} (P : IntervalPresentation B)
    (hBpositive : 0 < (volume B).toReal)
    (radius : ℝ) (hradius : 0 ≤ radius) :
    {S : Set ℝ | ∃ L : Set ℝ,
      LineTiles B L ∧ 0 ∈ L ∧ S = L ∩ Set.Icc (-radius) radius}.Finite := by
  obtain ⟨F, hF⟩ := finite_centerCandidates P hBpositive radius hradius
  let G : Set (Set ℝ) := ((fun s : Finset ℝ ↦ (s : Set ℝ)) ''
    (F.powerset : Set (Finset ℝ)))
  have hG : G.Finite := F.powerset.finite_toSet.image _
  apply hG.subset
  rintro S ⟨L, hTile, hzero, rfl⟩
  have hsub := hF L hTile hzero
  have hfin : (L ∩ Set.Icc (-radius) radius).Finite :=
    F.finite_toSet.subset hsub
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · simp only [Finset.mem_coe, Finset.mem_powerset]
    intro x hx
    apply hsub
    simpa using hx
  · exact Set.Finite.coe_toFinset hfin

private theorem finite_normalizedCentreSets_aux
    {B : Set ℝ} (hB : IsFiniteIntervalRegion B)
    (hBpositive : 0 < (volume B).toReal) :
    {L : Set ℝ | LineTiles B L ∧ 0 ∈ L}.Finite := by
  let P := IntervalPresentation.ofIsFiniteIntervalRegion hB
  obtain ⟨R, hRpos, hrigid⟩ :=
    finiteInterval_lineTilingsOn_localRigidity hB hBpositive
  let D : Set (Set ℝ) := {L : Set ℝ | LineTiles B L ∧ 0 ∈ L}
  let restrict : Set ℝ → Set ℝ := fun L ↦ L ∩ Set.Icc (-R) R
  have himage : (restrict '' D).Finite := by
    apply (finite_normalized_localPatterns P hBpositive R hRpos.le).subset
    rintro S ⟨L, hLD, rfl⟩
    exact ⟨L, hLD.1, hLD.2, rfl⟩
  apply Set.Finite.of_finite_image himage
  intro H hH H' hH' heq
  apply hrigid H H' Set.univ 0 hH.1 hH'.1
  simpa only [zero_sub, zero_add] using heq

/-- Finite-interval whole-line tilings normalized at a centre form a finite type. -/
theorem finite_normalizedLineTilings
    {B : Set ℝ} (hB : IsFiniteIntervalRegion B)
    (hBpositive : 0 < (volume B).toReal) :
    Finite (NormalizedLineTiling B) := by
  have hcentres := finite_normalizedCentreSets_aux hB hBpositive
  let C := {L : Set ℝ | LineTiles B L ∧ 0 ∈ L}
  let _ : Finite C := Set.finite_coe_iff.mpr hcentres
  let f : NormalizedLineTiling B → C := fun N ↦
    ⟨N.centres, N.tiles, N.zero_mem⟩
  apply Finite.of_injective f
  intro N N' heq
  cases N with
  | mk centres tiles zero_mem =>
    cases N' with
    | mk centres' tiles' zero_mem' =>
      have hcentresEq : centres = centres' := congrArg Subtype.val heq
      subst centres'
      rfl

/-- Equivalent set-level form, useful before packaging structures. -/
theorem finite_normalizedCentreSets
    {B : Set ℝ} (hB : IsFiniteIntervalRegion B)
    (hBpositive : 0 < (volume B).toReal) :
    {L : Set ℝ | LineTiles B L ∧ 0 ∈ L}.Finite :=
  finite_normalizedCentreSets_aux hB hBpositive

private theorem not_ae_univ_of_isBounded {A : Set ℝ}
    (hA : Bornology.IsBounded A) : ¬ A =ᵐ[volume] Set.univ := by
  intro hae
  have hmeasure : volume A = volume Set.univ := measure_congr hae
  exact hA.measure_lt_top.ne (by simpa using hmeasure)

theorem lineTiles_centres_infinite {B L : Set ℝ}
    (hBbounded : Bornology.IsBounded B) (hTile : LineTiles B L) : L.Infinite := by
  intro hL
  have hLbounded : Bornology.IsBounded L := hL.isBounded
  have hsumBounded : Bornology.IsBounded (L + B) :=
    isBounded_add hLbounded hBbounded
  apply not_ae_univ_of_isBounded hsumBounded
  filter_upwards [hTile.2.2.2.2] with x hx
  apply propext
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    obtain ⟨l, hl⟩ := hx.mp (Set.mem_univ x)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hl
    exact ⟨l.1, l.2, -l.1 + x, hl, by ring⟩

private theorem period_of_equal_normalizations {B L : Set ℝ}
    {l₁ l₂ : L} {N₁ N₂ : NormalizedLineTiling B}
    (hN₁ : N₁.centres = normalizeLineTiling L l₁.1)
    (hN₂ : N₂.centres = normalizeLineTiling L l₂.1)
    (heq : N₁ = N₂) : (l₂.1 - l₁.1) +ᵥ L = L := by
  have hcentres : normalizeLineTiling L l₁.1 = normalizeLineTiling L l₂.1 := by
    rw [← hN₁, ← hN₂, heq]
  have h := congrArg (fun S : Set ℝ ↦ l₂.1 +ᵥ S) hcentres
  rw [normalizeLineTiling, normalizeLineTiling] at h
  calc
    (l₂.1 - l₁.1) +ᵥ L = l₂.1 +ᵥ ((-l₁.1) +ᵥ L) := by
      ext x
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
      ring_nf
    _ = l₂.1 +ᵥ ((-l₂.1) +ᵥ L) := h
    _ = L := by
      ext x
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
      ring_nf

/-- Finiteness of normalized recenterings forces a positive literal centre period. -/
theorem exists_positiveLinePeriod_of_finite_normalized
    {B L : Set ℝ} (hBbounded : Bornology.IsBounded B)
    (hTile : LineTiles B L) (hfinite : Finite (NormalizedLineTiling B)) :
    ∃ p : ℝ, 0 < p ∧ p +ᵥ L = L := by
  let _ : Finite (NormalizedLineTiling B) := hfinite
  have hLinfinite : L.Infinite := lineTiles_centres_infinite hBbounded hTile
  let _ : Infinite L := hLinfinite.to_subtype
  let N : L → NormalizedLineTiling B := fun l ↦
    Classical.choose (normalizeLineTiling_spec hTile l.2)
  have hN (l : L) : (N l).centres = normalizeLineTiling L l.1 :=
    (Classical.choose_spec (normalizeLineTiling_spec hTile l.2)).1
  have hninj : ¬ Function.Injective N := not_injective_infinite_finite N
  rw [Function.Injective] at hninj
  push Not at hninj
  obtain ⟨l₁, l₂, heq, hne⟩ := hninj
  have hperiod : (l₂.1 - l₁.1) +ᵥ L = L :=
    period_of_equal_normalizations (hN l₁) (hN l₂) heq
  have hvalsne : l₂.1 ≠ l₁.1 := by
    intro hvals
    apply hne
    apply Subtype.ext
    exact hvals.symm
  have hdiffne : l₂.1 - l₁.1 ≠ 0 := sub_ne_zero.mpr hvalsne
  rcases lt_or_gt_of_ne hdiffne with hneg | hpos
  · refine ⟨-(l₂.1 - l₁.1), neg_pos.mpr hneg, ?_⟩
    exact (Tiling.AxisParallel.periodGroup L).neg_mem hperiod
  · exact ⟨l₂.1 - l₁.1, hpos, hperiod⟩

/-- Every whole-line tiling by a positive finite-interval tile has a positive centre period. -/
theorem exists_positiveLinePeriod {B L : Set ℝ}
    (hB : IsFiniteIntervalRegion B) (hBpositive : 0 < (volume B).toReal)
    (hTile : LineTiles B L) : ∃ p : ℝ, 0 < p ∧ p +ᵥ L = L := by
  let P := IntervalPresentation.ofIsFiniteIntervalRegion hB
  exact exists_positiveLinePeriod_of_finite_normalized P.isBounded hTile
    (finite_normalizedLineTilings hB hBpositive)

end Tiling.AxisParallel.OneDimensional.FiniteInterval
