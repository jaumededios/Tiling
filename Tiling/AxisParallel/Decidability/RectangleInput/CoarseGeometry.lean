import Tiling.AxisParallel.Decidability.RectangleInput.Coarse
import Tiling.AxisParallel.Decidability.RectangleInput.VertexGeometry

set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

noncomputable section

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput

def coarseLevels (V : List Plane) (input : TableInput) (vertical : Bool) : Finset ℝ :=
  (vertexLabels input).toFinset.image (coordinate (axis vertical) ∘ pointValue V)

theorem mem_coarseLevels {V : List Plane} {input : TableInput} {vertical : Bool} {x : ℝ} :
    x ∈ coarseLevels V input vertical ↔ ∃ p ∈ vertexLabels input,
      coordinate (axis vertical) (pointValue V p) = x := by
  classical
  simp [coarseLevels, Function.comp_apply]

theorem usedLevel_data {R : List (Plane × Plane)} {history : List Bool}
    {vertical : Bool} {i : ℕ} (hi : usedLevel (R.length, history) vertical i = true) :
    i < 2 * R.length ∧ canonicalLevel (2 * R.length) history vertical i = true ∧
      coordinate (axis vertical) ((cornerList R).getD i 0) ∈
        coarseLevels (cornerList R) (R.length, history) vertical := by
  obtain ⟨p, hp, hpi⟩ := usedLevel_eq_true.mp hi
  have hpm := mem_vertexLabels.mp hp
  have hpc := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hpm.2.2).1)
  refine ⟨?_, ?_, mem_coarseLevels.mpr ⟨p, hp, ?_⟩⟩
  · cases vertical with
    | false => exact hpi ▸ hpm.1
    | true => exact hpi ▸ hpm.2.1
  · cases vertical with
    | false => exact hpi ▸ hpc.1
    | true => exact hpi ▸ hpc.2
  · rw [coordinate_pointValue, hpi]

theorem coarseLevel_representative {R : List (Plane × Plane)} {history : List Bool}
    {vertical : Bool} {x : ℝ}
    (hx : x ∈ coarseLevels (cornerList R) (R.length, history) vertical) :
    ∃ i, i < 2 * R.length ∧ usedLevel (R.length, history) vertical i = true ∧
      coordinate (axis vertical) ((cornerList R).getD i 0) = x := by
  obtain ⟨p, hp, hpx⟩ := mem_coarseLevels.mp hx
  let i := bif vertical then p.2 else p.1
  have hiused : usedLevel (R.length, history) vertical i = true :=
    usedLevel_eq_true.mpr ⟨p, hp, rfl⟩
  exact ⟨i, (usedLevel_data hiused).1, hiused,
    by simpa only [coordinate_pointValue] using hpx⟩

theorem coarseAdjacent_correct {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history) {vertical : Bool} {i j : ℕ}
    (hi : i < 2 * R.length) (hj : j < 2 * R.length) :
    coarseAdjacent (R.length, history) vertical i j = true ↔
      usedLevel (R.length, history) vertical i = true ∧
      usedLevel (R.length, history) vertical j = true ∧
      (coordinate (axis vertical) ((cornerList R).getD i 0),
        coordinate (axis vertical) ((cornerList R).getD j 0)) ∈
        Tiling.AxisParallel.IntrinsicVertices.consecutiveLevelPairs
          (coarseLevels (cornerList R) (R.length, history) vertical) := by
  classical
  have hi' : i < (cornerList R).length := by simpa only [cornerList_length] using hi
  have hj' : j < (cornerList R).length := by simpa only [cornerList_length] using hj
  simp only [coarseAdjacent, Bool.and_eq_true]
  rw [← cornerList_length, strictLevel_correct h hi' hj' vertical]
  constructor
  · rintro ⟨⟨⟨hui, huj⟩, hij⟩, hall⟩
    refine ⟨hui, huj, ?_⟩
    rw [Tiling.AxisParallel.IntrinsicVertices.consecutiveLevelPairs,
      Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨(usedLevel_data hui).2.2, (usedLevel_data huj).2.2⟩, hij, ?_⟩
    intro x hx hbetween
    obtain ⟨k, hk, huk, hkx⟩ := coarseLevel_representative hx
    have hallk := allBelow_eq_true.mp hall k (by simpa only [cornerList_length] using hk)
    simp only [Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff, ne_eq,
      Bool.and_eq_true] at hallk
    have hk' : k < (cornerList R).length := by simpa only [cornerList_length] using hk
    apply hallk
    exact ⟨⟨huk, (strictLevel_correct h hi' hk' vertical).2 (hkx ▸ hbetween.1)⟩,
      (strictLevel_correct h hk' hj' vertical).2 (hkx ▸ hbetween.2)⟩
  · rintro ⟨hui, huj, hp⟩
    have hpdata := Tiling.AxisParallel.FiniteRectangles.pair_data hp
    have hnone := (Finset.mem_filter.mp hp).2.2
    refine ⟨⟨⟨hui, huj⟩, hpdata.2.2⟩, allBelow_eq_true.mpr ?_⟩
    intro k hk
    simp only [Bool.not_eq_true_eq_eq_false, Bool.eq_false_iff, ne_eq,
      Bool.and_eq_true]
    rintro ⟨⟨huk, hik⟩, hkj⟩
    exact hnone _ (usedLevel_data huk).2.2
      ⟨(strictLevel_correct h hi' hk vertical).1 hik,
        (strictLevel_correct h hk hj' vertical).1 hkj⟩

theorem coarseAdjacent_representatives {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history) {vertical : Bool} {p : ℝ × ℝ}
    (hp : p ∈ Tiling.AxisParallel.IntrinsicVertices.consecutiveLevelPairs
      (coarseLevels (cornerList R) (R.length, history) vertical)) :
    ∃ i j, i < 2 * R.length ∧ j < 2 * R.length ∧
      coordinate (axis vertical) ((cornerList R).getD i 0) = p.1 ∧
      coordinate (axis vertical) ((cornerList R).getD j 0) = p.2 ∧
      coarseAdjacent (R.length, history) vertical i j = true := by
  have hpdata := Tiling.AxisParallel.FiniteRectangles.pair_data hp
  obtain ⟨i, hi, hui, hix⟩ := coarseLevel_representative hpdata.1
  obtain ⟨j, hj, huj, hjx⟩ := coarseLevel_representative hpdata.2.1
  refine ⟨i, j, hi, hj, hix, hjx, (coarseAdjacent_correct h hi hj).2 ?_⟩
  exact ⟨hui, huj, by rw [hix, hjx]; simpa only [Prod.eta] using hp⟩

theorem coarseLevels_subset_fineLevels {R : List (Plane × Plane)} {history : List Bool}
    (vertical : Bool) : coarseLevels (cornerList R) (R.length, history) vertical ⊆
      levels (cornerList R) vertical := by
  intro x hx
  obtain ⟨i, hi, _, hix⟩ := coarseLevel_representative hx
  exact mem_levels.mpr ⟨i, by simpa only [cornerList_length] using hi, hix⟩

theorem cellContained_correct {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history) {c d : Cell}
    (hc : c.1.1 < 2 * R.length ∧ c.1.2 < 2 * R.length ∧
      c.2.1 < 2 * R.length ∧ c.2.2 < 2 * R.length)
    (hd : d.1.1 < 2 * R.length ∧ d.1.2 < 2 * R.length ∧
      d.2.1 < 2 * R.length ∧ d.2.2 < 2 * R.length) :
    cellContained (R.length, history) c d = true ↔
      ((cornerList R).getD c.1.1 0).re ≤ ((cornerList R).getD d.1.1 0).re ∧
      ((cornerList R).getD d.1.2 0).re ≤ ((cornerList R).getD c.1.2 0).re ∧
      ((cornerList R).getD c.2.1 0).im ≤ ((cornerList R).getD d.2.1 0).im ∧
      ((cornerList R).getD d.2.2 0).im ≤ ((cornerList R).getD c.2.2 0).im := by
  rw [← cornerList_length] at hc hd
  simp only [cellContained, ← cornerList_length, Bool.and_eq_true]
  rw [h false _ _ hc.1 hd.1, h false _ _ hd.2.1 hc.2.1,
    h true _ _ hc.2.2.1 hd.2.2.1, h true _ _ hd.2.2.2 hc.2.2.2]
  simp [coordinate, axis, and_assoc]

def nativeAxis (vertical : Bool) : Tiling.AxisParallel.Axis :=
  if vertical then .vertical else .horizontal

@[simp] theorem nativeAxis_coord (vertical : Bool) (z : Plane) :
    (nativeAxis vertical).coord z = coordinate (axis vertical) z := by
  cases vertical <;> rfl

theorem intrinsicLevels_eq_coarseLevels {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) (vertical : Bool) :
    Tiling.AxisParallel.IntrinsicVertices.intrinsicCoordinateLevels
      (regionOfTile Ω (RectanglePresentation.isAxisParallelTile hR)) (nativeAxis vertical) =
      coarseLevels (cornerList R) (R.length, history) vertical := by
  classical
  let K := regionOfTile Ω (RectanglePresentation.isAxisParallelTile hR)
  have hvertices : vertices Ω = K.vertices :=
    vertices_eq_native Ω (RectanglePresentation.isAxisParallelTile hR)
  ext x
  simp only [Tiling.AxisParallel.IntrinsicVertices.intrinsicCoordinateLevels,
    Finset.mem_image]
  constructor
  · rintro ⟨v, hv, hvx⟩
    have hvnative : v ∈ K.vertices := by
      change v ∈ (↑K.vertexFinset : Set Plane) at hv
      rwa [K.coe_vertexFinset] at hv
    have hvpublic : v ∈ vertices Ω := hvertices.symm ▸ hvnative
    obtain ⟨p, hp, hvalue⟩ := (vertexLabels_exact hR h v).2 hvpublic
    exact mem_coarseLevels.mpr ⟨p, hp, by rw [hvalue, ← nativeAxis_coord]; exact hvx⟩
  · intro hx
    obtain ⟨p, hp, rfl⟩ := mem_coarseLevels.mp hx
    have hv : pointValue (cornerList R) p ∈ K.vertices :=
      hvertices ▸ vertexLabels_sound hR h hp
    refine ⟨pointValue (cornerList R) p, ?_, nativeAxis_coord _ _⟩
    change pointValue (cornerList R) p ∈ (↑K.vertexFinset : Set Plane)
    rwa [K.coe_vertexFinset]

theorem frontier_coarse_axes {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) :
    ∀ z ∈ frontier Ω,
      z.re ∈ coarseLevels (cornerList R) (R.length, history) false ∨
      z.im ∈ coarseLevels (cornerList R) (R.length, history) true := by
  let K := regionOfTile Ω (RectanglePresentation.isAxisParallelTile hR)
  have hvertices : vertices Ω = K.vertices :=
    vertices_eq_native Ω (RectanglePresentation.isAxisParallelTile hR)
  intro z hz
  have hfront : frontier Ω = frontier K.support := by
    rw [← regionOfTile_openCarrier Ω (RectanglePresentation.isAxisParallelTile hR)]
    exact K.frontier_openCarrier_eq_frontier_support
  rcases Tiling.AxisParallel.IntrinsicVertices.frontier_subset_vertexCoordinateGrid K
      (hfront ▸ hz) with ⟨v, hv, hvx⟩ | ⟨v, hv, hvy⟩
  · obtain ⟨p, hp, hvalue⟩ := (vertexLabels_exact hR h v).2 (hvertices.symm ▸ hv)
    exact Or.inl (mem_coarseLevels.mpr ⟨p, hp, by rw [hvalue]; exact hvx.symm⟩)
  · obtain ⟨p, hp, hvalue⟩ := (vertexLabels_exact hR h v).2 (hvertices.symm ▸ hv)
    exact Or.inr (mem_coarseLevels.mpr ⟨p, hp, by rw [hvalue]; exact hvy.symm⟩)

private theorem cellSet_nonempty {V : List Plane} {c : Cell}
    (hx : (V.getD c.1.1 0).re < (V.getD c.1.2 0).re)
    (hy : (V.getD c.2.1 0).im < (V.getD c.2.2 0).im) : (cellSet V c).Nonempty := by
  let z : Plane := ⟨((V.getD c.1.1 0).re + (V.getD c.1.2 0).re) / 2,
    ((V.getD c.2.1 0).im + (V.getD c.2.2 0).im) / 2⟩
  refine ⟨z, ?_⟩
  change (_ < _ ∧ _ < _) ∧ (_ < _ ∧ _ < _)
  dsimp [z]
  constructor <;> constructor <;> linarith

theorem computed_cell_nonempty {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history) {c : Cell}
    (hc : c ∈ cells (R.length, history)) : (cellSet (cornerList R) c).Nonempty := by
  have hcm := mem_cells.mp hc
  have hadj := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcm.2).1
  rw [← cornerList_length] at hcm hadj
  have hxp := (adjacentLevels_correct h hcm.1.1 hcm.1.2.1).1 hadj.1
  have hyp := (adjacentLevels_correct h hcm.1.2.2.1 hcm.1.2.2.2).1 hadj.2
  exact cellSet_nonempty (Tiling.AxisParallel.FiniteRectangles.pair_data hxp.2.2).2.2
    (Tiling.AxisParallel.FiniteRectangles.pair_data hyp.2.2).2.2

theorem coarse_cell_subset {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) {c : Cell}
    (hc : c ∈ coarseCells (R.length, history)) : cellSet (cornerList R) c ⊆ Ω := by
  have hcm := mem_coarseCells.mp hc
  have hca := Bool.and_eq_true_iff.mp hcm.2
  have hcadj := Bool.and_eq_true_iff.mp hca.1
  have hxp := (coarseAdjacent_correct h hcm.1.1 hcm.1.2.1).1 hcadj.1
  have hyp := (coarseAdjacent_correct h hcm.1.2.2.1 hcm.1.2.2.2).1 hcadj.2
  have hinside : (cellSet (cornerList R) c ∩ Ω).Nonempty := by
    obtain ⟨d, hd, hcontained⟩ := List.any_eq_true.mp hca.2
    have hbounds := (cellContained_correct h hcm.1 (mem_cells.mp hd).1).1 hcontained
    obtain ⟨z, hz⟩ := computed_cell_nonempty h hd
    refine ⟨z, ?_, computed_cell_subset hR h hd hz⟩
    exact ⟨⟨hbounds.1.trans_lt hz.1.1, hz.1.2.trans_le hbounds.2.1⟩,
      ⟨hbounds.2.2.1.trans_lt hz.2.1, hz.2.2.trans_le hbounds.2.2.2⟩⟩
  exact Tiling.AxisParallel.FiniteRectangles.cell_inside_of_meets
    (RectanglePresentation.isAxisParallelTile hR).isOpen _ _ (frontier_coarse_axes hR h)
    hxp.2.2 hyp.2.2 hinside

theorem coarseAccepted_of_subset {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) {c : Cell}
    (hc : c.1.1 < 2 * R.length ∧ c.1.2 < 2 * R.length ∧
      c.2.1 < 2 * R.length ∧ c.2.2 < 2 * R.length)
    (hcx : coarseAdjacent (R.length, history) false c.1.1 c.1.2 = true)
    (hcy : coarseAdjacent (R.length, history) true c.2.1 c.2.2 = true)
    (hinside : cellSet (cornerList R) c ⊆ Ω) : coarseAccepted (R.length, history) c = true := by
  have hxp := (coarseAdjacent_correct h hc.1 hc.2.1).1 hcx
  have hyp := (coarseAdjacent_correct h hc.2.2.1 hc.2.2.2).1 hcy
  have hxdata := Tiling.AxisParallel.FiniteRectangles.pair_data hxp.2.2
  have hydata := Tiling.AxisParallel.FiniteRectangles.pair_data hyp.2.2
  have hopen : IsOpen (cellSet (cornerList R) c) :=
    (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  obtain ⟨z, hzoff, hzc⟩ := (Tiling.AxisParallel.FiniteRectangles.offGrid_dense
    (levels (cornerList R) false) (levels (cornerList R) true)).exists_mem_open
      hopen (cellSet_nonempty hxdata.2.2 hydata.2.2)
  have hzfine := mem_openCells_of_offGrid hR h (hinside hzc) hzoff.1 hzoff.2
  obtain ⟨d, hzfine⟩ := mem_iUnion.mp hzfine
  obtain ⟨hd, hzd⟩ := mem_iUnion.mp hzfine
  have hdm := mem_cells.mp hd
  have hdadj := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hdm.2).1
  rw [← cornerList_length] at hdm hdadj
  have hdpx := (adjacentLevels_correct h hdm.1.1 hdm.1.2.1).1 hdadj.1
  have hdpy := (adjacentLevels_correct h hdm.1.2.2.1 hdm.1.2.2.2).1 hdadj.2
  have hbx := consecutive_enclosed hdpx.2.2 hzd.1
    (coarseLevels_subset_fineLevels false hxdata.1)
    (coarseLevels_subset_fineLevels false hxdata.2.1) hzc.1.1.le hzc.1.2.le
  have hby := consecutive_enclosed hdpy.2.2 hzd.2
    (coarseLevels_subset_fineLevels true hydata.1)
    (coarseLevels_subset_fineLevels true hydata.2.1) hzc.2.1.le hzc.2.2.le
  simp only [coarseAccepted, Bool.and_eq_true, List.any_eq_true]
  refine ⟨⟨hcx, hcy⟩, d, hd, (cellContained_correct h hc (mem_cells.mp hd).1).2 ?_⟩
  exact ⟨hbx.1, hbx.2, hby.1, hby.2⟩

def coarseOpenCells (R : List (Plane × Plane)) (history : List Bool) : Set Plane :=
  ⋃ c ∈ coarseCells (R.length, history), cellSet (cornerList R) c

theorem coarseOpenCells_subset {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) : coarseOpenCells R history ⊆ Ω := by
  intro z hz
  obtain ⟨c, hz⟩ := mem_iUnion.mp hz
  obtain ⟨hc, hz⟩ := mem_iUnion.mp hz
  exact coarse_cell_subset hR h hc hz

theorem mem_coarseOpenCells_of_offGrid {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) {z : Plane} (hz : z ∈ Ω)
    (hxoff : z.re ∉ coarseLevels (cornerList R) (R.length, history) false)
    (hyoff : z.im ∉ coarseLevels (cornerList R) (R.length, history) true) :
    z ∈ coarseOpenCells R history := by
  let K := regionOfTile Ω (RectanglePresentation.isAxisParallelTile hR)
  have hzK : z ∈ K.openCarrier := by simpa only [K, regionOfTile_openCarrier] using hz
  have hvertices : vertices Ω = K.vertices :=
    vertices_eq_native Ω (RectanglePresentation.isAxisParallelTile hR)
  have hoffK : Tiling.AxisParallel.IntrinsicVertices.OffVertexCoordinateGrid K z := by
    intro v hv
    obtain ⟨p, hp, hvalue⟩ := (vertexLabels_exact hR h v).2 (hvertices.symm ▸ hv)
    constructor
    · intro heq
      exact hxoff (mem_coarseLevels.mpr ⟨p, hp, by rw [hvalue]; exact heq.symm⟩)
    · intro heq
      exact hyoff (mem_coarseLevels.mpr ⟨p, hp, by rw [hvalue]; exact heq.symm⟩)
  obtain ⟨xp, yp, hxp, hyp, hzbox⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicCell_around_offGrid K hzK hoffK
  have hlevelsx : Tiling.AxisParallel.IntrinsicVertices.intrinsicCoordinateLevels K
      .horizontal = coarseLevels (cornerList R) (R.length, history) false :=
    intrinsicLevels_eq_coarseLevels hR h false
  have hlevelsy : Tiling.AxisParallel.IntrinsicVertices.intrinsicCoordinateLevels K
      .vertical = coarseLevels (cornerList R) (R.length, history) true :=
    intrinsicLevels_eq_coarseLevels hR h true
  rw [hlevelsx] at hxp
  rw [hlevelsy] at hyp
  obtain ⟨i, j, hi, hj, hix, hjx, hcx⟩ := coarseAdjacent_representatives h hxp
  obtain ⟨b, t, hb, ht, hby, hty, hcy⟩ := coarseAdjacent_representatives h hyp
  change ((cornerList R).getD i 0).re = xp.1 at hix
  change ((cornerList R).getD j 0).re = xp.2 at hjx
  change ((cornerList R).getD b 0).im = yp.1 at hby
  change ((cornerList R).getD t 0).im = yp.2 at hty
  let c : Cell := ((i, j), (b, t))
  have hcBounds : c.1.1 < 2 * R.length ∧ c.1.2 < 2 * R.length ∧
      c.2.1 < 2 * R.length ∧ c.2.2 < 2 * R.length := ⟨hi, hj, hb, ht⟩
  have hzcell : z ∈ cellSet (cornerList R) c := by
    change z.re ∈ Ioo _ _ ∧ z.im ∈ Ioo _ _
    rw [hix, hjx, hby, hty]
    exact hzbox
  have hinside : cellSet (cornerList R) c ⊆ Ω :=
    Tiling.AxisParallel.FiniteRectangles.cell_inside_of_meets
      (RectanglePresentation.isAxisParallelTile hR).isOpen
      _ _ (frontier_coarse_axes hR h)
      ((coarseAdjacent_correct h hi hj).1 hcx).2.2
      ((coarseAdjacent_correct h hb ht).1 hcy).2.2 ⟨z, hzcell, hz⟩
  refine mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨mem_coarseCells.mpr
    ⟨hcBounds, coarseAccepted_of_subset hR h hcBounds hcx hcy hinside⟩, hzcell⟩⟩

theorem coarseOpenCells_ae_eq {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) : coarseOpenCells R history =ᵐ[volume] Ω := by
  filter_upwards [coordinate_ae_off_levels (cornerList R) false,
    coordinate_ae_off_levels (cornerList R) true] with z hx hy
  apply propext
  constructor
  · exact fun hz => coarseOpenCells_subset hR h hz
  · intro hz
    apply mem_coarseOpenCells_of_offGrid hR h hz
    · exact fun hx' => hx (coarseLevels_subset_fineLevels false hx')
    · exact fun hy' => hy (coarseLevels_subset_fineLevels true hy')

theorem coarseCells_nonempty {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) : 0 < (coarseCells (R.length, history)).length := by
  obtain ⟨z, hzoff, hz⟩ := (Tiling.AxisParallel.FiniteRectangles.offGrid_dense
    (levels (cornerList R) false) (levels (cornerList R) true)).exists_mem_open
      (RectanglePresentation.isAxisParallelTile hR).isOpen hR.1
  have hzcoarse := mem_coarseOpenCells_of_offGrid hR h hz
    (fun hx => hzoff.1 (coarseLevels_subset_fineLevels false hx))
    (fun hy => hzoff.2 (coarseLevels_subset_fineLevels true hy))
  obtain ⟨c, hzcoarse⟩ := mem_iUnion.mp hzcoarse
  obtain ⟨hc, _⟩ := mem_iUnion.mp hzcoarse
  exact List.length_pos_of_mem hc

theorem coarse_cells_disjoint {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history) {c d : Cell}
    (hc : c ∈ coarseCells (R.length, history)) (hd : d ∈ coarseCells (R.length, history))
    (hne : c ≠ d) : Disjoint (cellSet (cornerList R) c) (cellSet (cornerList R) d) := by
  have hcm := mem_coarseCells.mp hc
  have hdm := mem_coarseCells.mp hd
  have hac := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcm.2).1
  have had := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hdm.2).1
  have hcx := (coarseAdjacent_correct h hcm.1.1 hcm.1.2.1).1 hac.1
  have hcy := (coarseAdjacent_correct h hcm.1.2.2.1 hcm.1.2.2.2).1 hac.2
  have hdx := (coarseAdjacent_correct h hdm.1.1 hdm.1.2.1).1 had.1
  have hdy := (coarseAdjacent_correct h hdm.1.2.2.1 hdm.1.2.2.2).1 had.2
  have hci := (usedLevel_data hcx.1).2.1
  have hcj := (usedLevel_data hcx.2.1).2.1
  have hcb := (usedLevel_data hcy.1).2.1
  have hct := (usedLevel_data hcy.2.1).2.1
  have hdi := (usedLevel_data hdx.1).2.1
  have hdj := (usedLevel_data hdx.2.1).2.1
  have hdb := (usedLevel_data hdy.1).2.1
  have hdt := (usedLevel_data hdy.2.1).2.1
  rw [← cornerList_length] at hcm hdm hci hcj hcb hct hdi hdj hdb hdt
  by_cases hxeq :
      (coordinate (axis false) ((cornerList R).getD c.1.1 0),
        coordinate (axis false) ((cornerList R).getD c.1.2 0)) =
      (coordinate (axis false) ((cornerList R).getD d.1.1 0),
        coordinate (axis false) ((cornerList R).getD d.1.2 0))
  · have hlabels : c.1 = d.1 := Prod.ext
      (canonical_injective h hcm.1.1 hdm.1.1 hci hdi (congrArg Prod.fst hxeq))
      (canonical_injective h hcm.1.2.1 hdm.1.2.1 hcj hdj (congrArg Prod.snd hxeq))
    have hyne :
        (coordinate (axis true) ((cornerList R).getD c.2.1 0),
          coordinate (axis true) ((cornerList R).getD c.2.2 0)) ≠
        (coordinate (axis true) ((cornerList R).getD d.2.1 0),
          coordinate (axis true) ((cornerList R).getD d.2.2 0)) := by
      intro heq
      apply hne
      exact Prod.ext hlabels (Prod.ext
        (canonical_injective h hcm.1.2.2.1 hdm.1.2.2.1 hcb hdb (congrArg Prod.fst heq))
        (canonical_injective h hcm.1.2.2.2 hdm.1.2.2.2 hct hdt (congrArg Prod.snd heq)))
    have hdisj := Tiling.AxisParallel.FiniteRectangles.pair_intervals_disjoint hcy.2.2 hdy.2.2 hyne
    exact Set.disjoint_left.mpr (fun z hzc hzd => Set.disjoint_left.mp hdisj hzc.2 hzd.2)
  · have hdisj := Tiling.AxisParallel.FiniteRectangles.pair_intervals_disjoint hcx.2.2 hdx.2.2 hxeq
    exact Set.disjoint_left.mpr (fun z hzc hzd => Set.disjoint_left.mp hdisj hzc.1 hzd.1)

end Tiling.AxisParallel.Decidability.RectangleInput
