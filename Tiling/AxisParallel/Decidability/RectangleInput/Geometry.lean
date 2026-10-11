import Tiling.AxisParallel.Decidability.RectangleInput.Rectangles
import Tiling.AxisParallel.SetFormulation.RegionBridge

set_option autoImplicit false

noncomputable section

open Set
open MeasureTheory
open scoped Topology

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput

def TableCorrect (V : List Plane) (history : List Bool) : Prop :=
  ∀ vertical i j, i < V.length → j < V.length →
    (compare V.length history vertical i j = true ↔
      coordinate (axis vertical) (V.getD i 0) ≤
        coordinate (axis vertical) (V.getD j 0))

theorem comparisonHistory_correct {V : List Plane} {answer : Query → Bool}
    (hanswer : CorrectOracle V answer) :
    TableCorrect V (comparisonHistory V.length answer) := by
  intro vertical i j hi hj
  exact compare_history_correct hanswer hi hj vertical

theorem cornerList_length (R : List (Plane × Plane)) :
    (cornerList R).length = 2 * R.length := by
  induction R with
  | nil => rfl
  | cons r R ih => simp [cornerList, Nat.mul_comm]; omega

theorem cornerList_getD_left (R : List (Plane × Plane)) {k : ℕ} (hk : k < R.length) :
    (cornerList R).getD (2 * k) 0 = (R.getD k (0, 0)).1 := by
  induction R generalizing k with
  | nil => simp at hk
  | cons r R ih =>
    cases k with
    | zero => simp [cornerList]
    | succ k =>
      simpa [cornerList, Nat.mul_succ] using ih (by simpa using hk)

theorem cornerList_getD_right (R : List (Plane × Plane)) {k : ℕ} (hk : k < R.length) :
    (cornerList R).getD (2 * k + 1) 0 = (R.getD k (0, 0)).2 := by
  induction R generalizing k with
  | nil => simp at hk
  | cons r R ih =>
    cases k with
    | zero => simp [cornerList]
    | succ k =>
      simpa [cornerList, Nat.mul_succ, Nat.add_assoc] using ih (by simpa using hk)

theorem RectanglePresentation.isAxisParallelTile {R : List (Plane × Plane)}
    {Ω : Set Plane} (hR : RectanglePresentation R Ω) : IsRectangleTile Ω := by
  classical
  refine ⟨hR.1, R.toFinset, ?_⟩
  simpa only [List.mem_toFinset] using hR.2

theorem strictLevel_correct {V : List Plane} {history : List Bool}
    (h : TableCorrect V history) {i j : ℕ} (hi : i < V.length) (hj : j < V.length)
    (vertical : Bool) :
    strictLevel V.length history vertical i j = true ↔
      coordinate (axis vertical) (V.getD i 0) <
        coordinate (axis vertical) (V.getD j 0) := by
  simp only [strictLevel, Bool.not_eq_true_eq_eq_false]
  simp only [Bool.eq_false_iff, ne_eq, h vertical j i hj hi, not_le]

theorem equalLevel_correct {V : List Plane} {history : List Bool}
    (h : TableCorrect V history) {i j : ℕ} (hi : i < V.length) (hj : j < V.length)
    (vertical : Bool) :
    equalLevel V.length history vertical i j = true ↔
      coordinate (axis vertical) (V.getD i 0) =
        coordinate (axis vertical) (V.getD j 0) := by
  simp only [equalLevel, Bool.and_eq_true]
  rw [h vertical i j hi hj, h vertical j i hj hi, le_antisymm_iff]

theorem canonicalLevel_correct {V : List Plane} {history : List Bool}
    (h : TableCorrect V history) {i : ℕ} (hi : i < V.length) (vertical : Bool) :
    canonicalLevel V.length history vertical i = true ↔
      ∀ j < i, coordinate (axis vertical) (V.getD i 0) ≠
        coordinate (axis vertical) (V.getD j 0) := by
  simp only [canonicalLevel, allBelow_eq_true, Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff]
  constructor
  · intro hc j hj heq
    exact hc j hj ((equalLevel_correct h hi (hj.trans hi) vertical).2 heq)
  · intro hc j hj heq
    exact hc j hj ((equalLevel_correct h hi (hj.trans hi) vertical).1 heq)

def levels (V : List Plane) (vertical : Bool) : Finset ℝ :=
  V.toFinset.image (coordinate (axis vertical))

def cellSet (V : List Plane) (c : Cell) : Set Plane :=
  Tiling.AxisParallel.FiniteRectangles.cell
    ((V.getD c.1.1 0).re, (V.getD c.1.2 0).re)
    ((V.getD c.2.1 0).im, (V.getD c.2.2 0).im)

theorem mem_levels {V : List Plane} {vertical : Bool} {x : ℝ} :
    x ∈ levels V vertical ↔ ∃ i < V.length,
      coordinate (axis vertical) (V.getD i 0) = x := by
  classical
  simp only [levels, Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hv
    exact ⟨i, hi, by rw [List.getD_eq_getElem V 0 hi, hget]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨V.getD i 0, by rw [List.getD_eq_getElem V 0 hi]; exact List.getElem_mem hi, rfl⟩

theorem canonical_representative {V : List Plane} {history : List Bool}
    (h : TableCorrect V history) {vertical : Bool} {x : ℝ}
    (hx : x ∈ levels V vertical) :
    ∃ i < V.length, coordinate (axis vertical) (V.getD i 0) = x ∧
      canonicalLevel V.length history vertical i = true := by
  classical
  have he := mem_levels.mp hx
  let i := Nat.find he
  have hi : i < V.length ∧ coordinate (axis vertical) (V.getD i 0) = x := Nat.find_spec he
  refine ⟨i, hi.1, hi.2, (canonicalLevel_correct h hi.1 vertical).2 ?_⟩
  intro j hj heq
  have hjx : coordinate (axis vertical) (V.getD j 0) = x := heq.symm.trans hi.2
  exact (not_le_of_gt hj) (Nat.find_min' he ⟨hj.trans hi.1, hjx⟩)

theorem canonical_injective {V : List Plane} {history : List Bool}
    (h : TableCorrect V history) {vertical : Bool} {i j : ℕ}
    (hi : i < V.length) (hj : j < V.length)
    (hci : canonicalLevel V.length history vertical i = true)
    (hcj : canonicalLevel V.length history vertical j = true)
    (heq : coordinate (axis vertical) (V.getD i 0) =
      coordinate (axis vertical) (V.getD j 0)) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact ((canonicalLevel_correct h hj vertical).1 hcj i hij heq.symm).elim
  · exact hij
  · exact ((canonicalLevel_correct h hi vertical).1 hci j hij heq).elim

theorem adjacentLevels_correct {V : List Plane} {history : List Bool}
    (h : TableCorrect V history) {vertical : Bool} {i j : ℕ}
    (hi : i < V.length) (hj : j < V.length) :
    adjacentLevels V.length history vertical i j = true ↔
      canonicalLevel V.length history vertical i = true ∧
      canonicalLevel V.length history vertical j = true ∧
      (coordinate (axis vertical) (V.getD i 0),
        coordinate (axis vertical) (V.getD j 0)) ∈
          Tiling.AxisParallel.IntrinsicVertices.consecutiveLevelPairs (levels V vertical) := by
  classical
  simp only [adjacentLevels, Bool.and_eq_true]
  rw [strictLevel_correct h hi hj vertical]
  simp only [Tiling.AxisParallel.IntrinsicVertices.consecutiveLevelPairs,
    Finset.mem_filter, Finset.mem_product]
  have hm₁ : coordinate (axis vertical) (V.getD i 0) ∈ levels V vertical :=
    mem_levels.mpr ⟨i, hi, rfl⟩
  have hm₂ : coordinate (axis vertical) (V.getD j 0) ∈ levels V vertical :=
    mem_levels.mpr ⟨j, hj, rfl⟩
  simp only [hm₁, hm₂, true_and]
  constructor
  · rintro ⟨⟨⟨hci, hcj⟩, hij⟩, hall⟩
    refine ⟨hci, hcj, hij, ?_⟩
    intro x hx hbetween
    obtain ⟨k, hk, rfl⟩ := mem_levels.mp hx
    have hallk := (allBelow_eq_true.mp hall) k hk
    simp only [Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff, ne_eq,
      Bool.and_eq_true] at hallk
    exact hallk ⟨(strictLevel_correct h hi hk vertical).2 hbetween.1,
      (strictLevel_correct h hk hj vertical).2 hbetween.2⟩
  · rintro ⟨hci, hcj, hij, hnone⟩
    refine ⟨⟨⟨hci, hcj⟩, hij⟩, allBelow_eq_true.mpr ?_⟩
    intro k hk
    simp only [Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff, ne_eq,
      Bool.and_eq_true]
    rintro ⟨hik, hkj⟩
    exact hnone _ (mem_levels.mpr ⟨k, hk, rfl⟩)
      ⟨(strictLevel_correct h hi hk vertical).1 hik,
        (strictLevel_correct h hk hj vertical).1 hkj⟩

theorem adjacent_representatives {V : List Plane} {history : List Bool}
    (h : TableCorrect V history) {vertical : Bool} {p : ℝ × ℝ}
    (hp : p ∈ Tiling.AxisParallel.IntrinsicVertices.consecutiveLevelPairs
      (levels V vertical)) :
    ∃ i j, i < V.length ∧ j < V.length ∧
      coordinate (axis vertical) (V.getD i 0) = p.1 ∧
      coordinate (axis vertical) (V.getD j 0) = p.2 ∧
      adjacentLevels V.length history vertical i j = true := by
  have hpdata := Tiling.AxisParallel.FiniteRectangles.pair_data hp
  obtain ⟨i, hi, hix, hci⟩ := canonical_representative h hpdata.1
  obtain ⟨j, hj, hjx, hcj⟩ := canonical_representative h hpdata.2.1
  refine ⟨i, j, hi, hj, hix, hjx, (adjacentLevels_correct h hi hj).2 ?_⟩
  exact ⟨hci, hcj, by rw [hix, hjx]; simpa only [Prod.eta] using hp⟩

theorem rectangleCovers_correct {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history) {c : Cell} {k : ℕ}
    (hk : k < R.length)
    (hc : c.1.1 < 2 * R.length ∧ c.1.2 < 2 * R.length ∧
      c.2.1 < 2 * R.length ∧ c.2.2 < 2 * R.length) :
    rectangleCovers R.length history c k = true ↔
      (R.getD k (0, 0)).1.re ≤ ((cornerList R).getD c.1.1 0).re ∧
      ((cornerList R).getD c.1.2 0).re ≤ (R.getD k (0, 0)).2.re ∧
      (R.getD k (0, 0)).1.im ≤ ((cornerList R).getD c.2.1 0).im ∧
      ((cornerList R).getD c.2.2 0).im ≤ (R.getD k (0, 0)).2.im := by
  have hleft : 2 * k < (cornerList R).length := by rw [cornerList_length]; omega
  have hright : 2 * k + 1 < (cornerList R).length := by rw [cornerList_length]; omega
  have h₁ : c.1.1 < (cornerList R).length := by simpa [cornerList_length] using hc.1
  have h₂ : c.1.2 < (cornerList R).length := by simpa [cornerList_length] using hc.2.1
  have h₃ : c.2.1 < (cornerList R).length := by simpa [cornerList_length] using hc.2.2.1
  have h₄ : c.2.2 < (cornerList R).length := by simpa [cornerList_length] using hc.2.2.2
  simp only [rectangleCovers, ← cornerList_length, Bool.and_eq_true]
  rw [h false _ _ hleft h₁, h false _ _ h₂ hright,
    h true _ _ hleft h₃, h true _ _ h₄ hright,
    cornerList_getD_left R hk, cornerList_getD_right R hk]
  simp [coordinate, axis, and_assoc]

theorem cell_subset_of_rectangleCovers {R : List (Plane × Plane)}
    {history : List Bool} (h : TableCorrect (cornerList R) history)
    {c : Cell} {k : ℕ} (hk : k < R.length)
    (hc : c.1.1 < 2 * R.length ∧ c.1.2 < 2 * R.length ∧
      c.2.1 < 2 * R.length ∧ c.2.2 < 2 * R.length)
    (hcover : rectangleCovers R.length history c k = true) :
    cellSet (cornerList R) c ⊆ interior (rectangle (R.getD k (0, 0)).1
      (R.getD k (0, 0)).2) := by
  have hs := (rectangleCovers_correct h hk hc).1 hcover
  intro z hz
  rw [rectangle_eq_orderedBox, Tiling.AxisParallel.FiniteRectangles.orderedBox,
    Tiling.AxisParallel.FiniteRectangles.interior_box]
  change z.re ∈ Ioo _ _ ∧ z.im ∈ Ioo _ _ at hz ⊢
  exact ⟨⟨hs.1.trans_lt hz.1.1, hz.1.2.trans_le hs.2.1⟩,
    ⟨hs.2.2.1.trans_lt hz.2.1, hz.2.2.trans_le hs.2.2.2⟩⟩

theorem computed_cell_subset {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) {c : Cell}
    (hc : c ∈ cells (R.length, history)) : cellSet (cornerList R) c ⊆ Ω := by
  obtain ⟨hb, hcell⟩ := mem_cells.mp hc
  have hoc : occupied R.length history c = true := (Bool.and_eq_true_iff.mp hcell).2
  obtain ⟨k, hk, hcover⟩ := anyBelow_eq_true.mp hoc
  apply (cell_subset_of_rectangleCovers h hk hb hcover).trans
  rw [hR.2]
  apply interior_mono
  exact subset_iUnion_of_subset (R.getD k (0, 0))
    (subset_iUnion_of_subset
      (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk) subset_rfl)

theorem consecutive_enclosed {s : Finset ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Tiling.AxisParallel.IntrinsicVertices.consecutiveLevelPairs s)
    {x a b : ℝ} (hx : x ∈ Ioo p.1 p.2) (ha : a ∈ s) (hb : b ∈ s)
    (hax : a ≤ x) (hxb : x ≤ b) : a ≤ p.1 ∧ p.2 ≤ b := by
  classical
  have hnone := (Finset.mem_filter.mp hp).2.2
  constructor
  · by_contra h
    exact hnone a ha ⟨lt_of_not_ge h, hax.trans_lt hx.2⟩
  · by_contra h
    exact hnone b hb ⟨hx.1.trans_le hxb, lt_of_not_ge h⟩

def openCells (R : List (Plane × Plane)) (history : List Bool) : Set Plane :=
  ⋃ c ∈ cells (R.length, history), cellSet (cornerList R) c

theorem openCells_subset {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) : openCells R history ⊆ Ω := by
  intro z hz
  obtain ⟨c, hz⟩ := mem_iUnion.mp hz
  obtain ⟨hc, hz⟩ := mem_iUnion.mp hz
  exact computed_cell_subset hR h hc hz

theorem mem_openCells_of_offGrid {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) {z : Plane} (hz : z ∈ Ω)
    (hxoff : z.re ∉ levels (cornerList R) false)
    (hyoff : z.im ∉ levels (cornerList R) true) : z ∈ openCells R history := by
  have hzUnion : z ∈ ⋃ r ∈ R, rectangle r.1 r.2 := by
    exact interior_subset (hR.2 ▸ hz)
  obtain ⟨r, hzUnion⟩ := mem_iUnion.mp hzUnion
  obtain ⟨hr, hzr⟩ := mem_iUnion.mp hzUnion
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hr
  have hgetD : R.getD k (0, 0) = r := (List.getD_eq_getElem R (0, 0) hk).trans hget
  have hkleft : 2 * k < (cornerList R).length := by rw [cornerList_length]; omega
  have hkright : 2 * k + 1 < (cornerList R).length := by rw [cornerList_length]; omega
  have hleft : (cornerList R).getD (2 * k) 0 = r.1 := by
    rw [cornerList_getD_left R hk, hgetD]
  have hright : (cornerList R).getD (2 * k + 1) 0 = r.2 := by
    rw [cornerList_getD_right R hk, hgetD]
  have hal : r.1.re ∈ levels (cornerList R) false :=
    mem_levels.mpr ⟨2 * k, hkleft, by rw [hleft]; rfl⟩
  have har : r.2.re ∈ levels (cornerList R) false :=
    mem_levels.mpr ⟨2 * k + 1, hkright, by rw [hright]; rfl⟩
  have hbl : r.1.im ∈ levels (cornerList R) true :=
    mem_levels.mpr ⟨2 * k, hkleft, by rw [hleft]; rfl⟩
  have hbr : r.2.im ∈ levels (cornerList R) true :=
    mem_levels.mpr ⟨2 * k + 1, hkright, by rw [hright]; rfl⟩
  change (r.1.re ≤ z.re ∧ z.re ≤ r.2.re) ∧
    (r.1.im ≤ z.im ∧ z.im ≤ r.2.im) at hzr
  have hax : r.1.re < z.re := lt_of_le_of_ne hzr.1.1
    (fun heq => hxoff (heq ▸ hal))
  have hxb : z.re < r.2.re := lt_of_le_of_ne hzr.1.2
    (fun heq => hxoff (heq.symm ▸ har))
  have hay : r.1.im < z.im := lt_of_le_of_ne hzr.2.1
    (fun heq => hyoff (heq ▸ hbl))
  have hyb : z.im < r.2.im := lt_of_le_of_ne hzr.2.2
    (fun heq => hyoff (heq.symm ▸ hbr))
  obtain ⟨xl, xr, hxp, hx⟩ := Tiling.AxisParallel.FiniteRectangles.pair_around hxoff
    ⟨r.1.re, hal, hax⟩ ⟨r.2.re, har, hxb⟩
  obtain ⟨yb, yt, hyp, hy⟩ := Tiling.AxisParallel.FiniteRectangles.pair_around hyoff
    ⟨r.1.im, hbl, hay⟩ ⟨r.2.im, hbr, hyb⟩
  obtain ⟨i, j, hi, hj, hix, hjx, hadjx⟩ := adjacent_representatives h hxp
  obtain ⟨b, t, hb, ht, hby, hty, hadjy⟩ := adjacent_representatives h hyp
  change ((cornerList R).getD i 0).re = xl at hix
  change ((cornerList R).getD j 0).re = xr at hjx
  change ((cornerList R).getD b 0).im = yb at hby
  change ((cornerList R).getD t 0).im = yt at hty
  let c : Cell := ((i, j), (b, t))
  have hcBounds : c.1.1 < 2 * R.length ∧ c.1.2 < 2 * R.length ∧
      c.2.1 < 2 * R.length ∧ c.2.2 < 2 * R.length := by
    simpa only [cornerList_length] using And.intro hi (And.intro hj (And.intro hb ht))
  have hxbound := consecutive_enclosed hxp hx hal har hzr.1.1 hzr.1.2
  have hybound := consecutive_enclosed hyp hy hbl hbr hzr.2.1 hzr.2.2
  have hcover : rectangleCovers R.length history c k = true := by
    apply (rectangleCovers_correct h hk hcBounds).2
    rw [hgetD]
    rw [hix, hjx, hby, hty]
    exact ⟨hxbound.1, hxbound.2, hybound.1, hybound.2⟩
  have haccept : accepted (R.length, history) c = true := by
    simp only [accepted, Bool.and_eq_true, occupied, anyBelow_eq_true]
    exact ⟨⟨by simpa only [cornerList_length] using hadjx,
      by simpa only [cornerList_length] using hadjy⟩, k, hk, hcover⟩
  refine mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨mem_cells.mpr ⟨hcBounds, haccept⟩, ?_⟩⟩
  change z.re ∈ Ioo _ _ ∧ z.im ∈ Ioo _ _
  rw [hix, hjx, hby, hty]
  exact ⟨hx, hy⟩

theorem volume_coordinate_level (vertical : Bool) (a : ℝ) :
    volume {z : Plane | coordinate (axis vertical) z = a} = 0 := by
  cases vertical with
  | false =>
    have heq : {z : Plane | coordinate (axis false) z = a} =
        Complex.measurableEquivRealProd ⁻¹' ({a} ×ˢ (univ : Set ℝ)) := by
      ext z
      simp [coordinate, axis, Complex.measurableEquivRealProd]
    rw [heq, Complex.volume_preserving_equiv_real_prod.measure_preimage
      ((measurableSet_singleton a).prod MeasurableSet.univ).nullMeasurableSet]
    change (volume.prod volume) ({a} ×ˢ (univ : Set ℝ)) = 0
    simp [Measure.prod_prod]
  | true =>
    have heq : {z : Plane | coordinate (axis true) z = a} =
        Complex.measurableEquivRealProd ⁻¹' ((univ : Set ℝ) ×ˢ {a}) := by
      ext z
      simp [coordinate, axis, Complex.measurableEquivRealProd]
    rw [heq, Complex.volume_preserving_equiv_real_prod.measure_preimage
      (MeasurableSet.univ.prod (measurableSet_singleton a)).nullMeasurableSet]
    change (volume.prod volume) ((univ : Set ℝ) ×ˢ {a}) = 0
    simp [Measure.prod_prod]

theorem coordinate_ae_off_levels (V : List Plane) (vertical : Bool) :
    ∀ᵐ z : Plane ∂volume, coordinate (axis vertical) z ∉ levels V vertical := by
  classical
  rw [ae_iff]
  have heq : {z : Plane | ¬coordinate (axis vertical) z ∉ levels V vertical} =
      ⋃ a ∈ levels V vertical, {z : Plane | coordinate (axis vertical) z = a} := by
    ext z
    simp
  rw [heq]
  exact (measure_biUnion_null_iff (levels V vertical).countable_toSet).2
    (fun a _ => volume_coordinate_level vertical a)

/-- Every computed open cell is correct, and all omitted points lie on finitely
many coordinate lines. This is the presentation field required by runtime input. -/
theorem openCells_ae_eq {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) : openCells R history =ᵐ[volume] Ω := by
  filter_upwards [coordinate_ae_off_levels (cornerList R) false,
    coordinate_ae_off_levels (cornerList R) true] with z hx hy
  apply propext
  constructor
  · exact fun hz => openCells_subset hR h hz
  · intro hz
    exact mem_openCells_of_offGrid hR h hz hx hy

theorem computed_cells_disjoint {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history) {c d : Cell}
    (hc : c ∈ cells (R.length, history)) (hd : d ∈ cells (R.length, history))
    (hne : c ≠ d) : Disjoint (cellSet (cornerList R) c) (cellSet (cornerList R) d) := by
  have hcm := mem_cells.mp hc
  have hdm := mem_cells.mp hd
  rw [← cornerList_length] at hcm hdm
  have hac := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcm.2).1)
  have had := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hdm.2).1)
  rw [← cornerList_length] at hac had
  have hcx := (adjacentLevels_correct h hcm.1.1 hcm.1.2.1).1 hac.1
  have hcy := (adjacentLevels_correct h hcm.1.2.2.1 hcm.1.2.2.2).1 hac.2
  have hdx := (adjacentLevels_correct h hdm.1.1 hdm.1.2.1).1 had.1
  have hdy := (adjacentLevels_correct h hdm.1.2.2.1 hdm.1.2.2.2).1 had.2
  by_cases hxeq :
      (coordinate (axis false) ((cornerList R).getD c.1.1 0),
        coordinate (axis false) ((cornerList R).getD c.1.2 0)) =
      (coordinate (axis false) ((cornerList R).getD d.1.1 0),
        coordinate (axis false) ((cornerList R).getD d.1.2 0))
  · have hlabels : c.1 = d.1 := Prod.ext
      (canonical_injective h hcm.1.1 hdm.1.1 hcx.1 hdx.1 (congrArg Prod.fst hxeq))
      (canonical_injective h hcm.1.2.1 hdm.1.2.1 hcx.2.1 hdx.2.1
        (congrArg Prod.snd hxeq))
    have hyne :
        (coordinate (axis true) ((cornerList R).getD c.2.1 0),
          coordinate (axis true) ((cornerList R).getD c.2.2 0)) ≠
        (coordinate (axis true) ((cornerList R).getD d.2.1 0),
          coordinate (axis true) ((cornerList R).getD d.2.2 0)) := by
      intro heq
      apply hne
      exact Prod.ext hlabels (Prod.ext
        (canonical_injective h hcm.1.2.2.1 hdm.1.2.2.1 hcy.1 hdy.1
          (congrArg Prod.fst heq))
        (canonical_injective h hcm.1.2.2.2 hdm.1.2.2.2 hcy.2.1 hdy.2.1
          (congrArg Prod.snd heq)))
    have hdisj := Tiling.AxisParallel.FiniteRectangles.pair_intervals_disjoint hcy.2.2 hdy.2.2 hyne
    rw [Set.disjoint_left]
    intro z hzc hzd
    exact Set.disjoint_left.mp hdisj hzc.2 hzd.2
  · have hdisj := Tiling.AxisParallel.FiniteRectangles.pair_intervals_disjoint hcx.2.2 hdx.2.2 hxeq
    rw [Set.disjoint_left]
    intro z hzc hzd
    exact Set.disjoint_left.mp hdisj hzc.1 hzd.1

end Tiling.AxisParallel.Decidability.RectangleInput
