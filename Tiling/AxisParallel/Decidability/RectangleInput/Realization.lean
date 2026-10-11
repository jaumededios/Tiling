import Tiling.AxisParallel.Decidability.RectangleInput.Packed
import Tiling.AxisParallel.Decidability.RectangleInput.CoarseGeometry
import Tiling.AxisParallel.Decidability.RectangleInput.Translation
import Tiling.AxisParallel.Terminal.ExecutableInputSemantics
import Tiling.AxisParallel.Foundations.PositiveSimilarityTransport

set_option autoImplicit false

open Set MeasureTheory
open scoped Pointwise

noncomputable section

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput

abbrev inputCode (input : TableInput) (hinput : 0 < (vertexLabels input).length) :=
  regionCode (packedRegion input) hinput

def originalVertex (V : List Plane) (input : TableInput)
    (i : Fin (vertexLabels input).length) : Plane :=
  pointValue V ((vertexLabels input).getD i (0, 0))

def anchor (V : List Plane) (input : TableInput) (hinput : 0 < (vertexLabels input).length) :
    Plane := originalVertex V input ⟨0, hinput⟩

def normalizedVertex (V : List Plane) (input : TableInput)
    (hinput : 0 < (vertexLabels input).length) (i : Fin (vertexLabels input).length) : Plane :=
  originalVertex V input i - anchor V input hinput

def indexedCell (input : TableInput) (hinput : 0 < (vertexLabels input).length)
    (e : Fin (inputCode input hinput).cellCount) : Cell :=
  (coarseCells input).get ⟨e, by
    have he : e.val < (packedRegion input).2.length := e.isLt
    simpa only [packedRegion, List.length_map] using he⟩

theorem indexedCell_mem (input : TableInput) (hinput : 0 < (vertexLabels input).length)
    (e : Fin (inputCode input hinput).cellCount) : indexedCell input hinput e ∈ coarseCells input :=
  List.get_mem _ _

theorem originalVertex_range {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history) :
    Set.range (originalVertex (cornerList R) (R.length, history)) = vertices Ω := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    apply vertexLabels_sound hR h
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact List.getElem_mem i.isLt
  · intro hv
    obtain ⟨p, hp, hvalue⟩ := (vertexLabels_exact hR h v).2 hv
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hp
    refine ⟨⟨i, hi⟩, ?_⟩
    change pointValue (cornerList R) ((vertexLabels _).getD i (0, 0)) = v
    rw [List.getD_eq_getElem _ _ hi, hget, hvalue]

theorem originalVertex_injective {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history) :
    Function.Injective (originalVertex (cornerList R) (R.length, history)) := by
  intro i j heq
  have hlabel :
      (vertexLabels (R.length, history)).getD i (0, 0) =
        (vertexLabels (R.length, history)).getD j (0, 0) := by
    apply pointValue_injective_on_vertexLabels h
    · rw [List.getD_eq_getElem _ _ i.isLt]; exact List.getElem_mem i.isLt
    · rw [List.getD_eq_getElem _ _ j.isLt]; exact List.getElem_mem j.isLt
    · exact heq
  apply (vertexLabels_nodup (R.length, history)).get_inj_iff.mp
  simpa only [List.getD_eq_get] using hlabel

theorem firstVertex_coordinate {R : List (Plane × Plane)} {history : List Bool}
    {vertical : Bool} {i : ℕ} (hi : usedLevel (R.length, history) vertical i = true) :
    coordinate (axis vertical)
      (originalVertex (cornerList R) (R.length, history)
        ⟨firstVertex (R.length, history) vertical i, (firstVertex_spec hi).1⟩) =
      coordinate (axis vertical) ((cornerList R).getD i 0) := by
  change coordinate (axis vertical) (pointValue (cornerList R) _) = _
  rw [coordinate_pointValue, (firstVertex_spec hi).2]

private theorem packedCell_getD (input : TableInput)
    (hinput : 0 < (vertexLabels input).length)
    (e : Fin (inputCode input hinput).cellCount) :
    (packedRegion input).2.getD e (0, 0) = encodedCell input (indexedCell input hinput e) := by
  rw [List.getD_eq_getElem _ _ e.isLt]
  simp only [packedRegion, List.getElem_map]
  rfl

theorem indexedCell_injective (input : TableInput)
    (hinput : 0 < (vertexLabels input).length) :
    Function.Injective (indexedCell input hinput) := by
  intro e f heq
  have hidx := (coarseCells_nodup input).get_inj_iff.mp heq
  have hv := congrArg Fin.val hidx
  exact Fin.ext hv

theorem inputCode_left_coordinate {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length)
    (e : Fin (inputCode (R.length, history) hinput).cellCount) :
    (originalVertex (cornerList R) (R.length, history)
      ((inputCode (R.length, history) hinput).leftVertex e)).re =
      ((cornerList R).getD (indexedCell (R.length, history) hinput e).1.1 0).re := by
  have hcm := mem_coarseCells.mp (indexedCell_mem (R.length, history) hinput e)
  have hca := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcm.2).1).1
  have hui := ((coarseAdjacent_correct h hcm.1.1 hcm.1.2.1).1 hca).1
  have hidx : ((inputCode (R.length, history) hinput).leftVertex e).val =
      firstVertex (R.length, history) false (indexedCell (R.length, history) hinput e).1.1 := by
    change ((packedRegion _).2.getD e (0, 0)).1.1 % _ = _
    rw [packedCell_getD]
    exact Nat.mod_eq_of_lt (firstVertex_spec hui).1
  have hv := firstVertex_coordinate hui
  change (pointValue (cornerList R) ((vertexLabels _).getD _ (0, 0))).re = _
  rw [hidx]
  exact hv

theorem inputCode_right_coordinate {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length)
    (e : Fin (inputCode (R.length, history) hinput).cellCount) :
    (originalVertex (cornerList R) (R.length, history)
      ((inputCode (R.length, history) hinput).rightVertex e)).re =
      ((cornerList R).getD (indexedCell (R.length, history) hinput e).1.2 0).re := by
  have hcm := mem_coarseCells.mp (indexedCell_mem (R.length, history) hinput e)
  have hca := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcm.2).1).1
  have hui := ((coarseAdjacent_correct h hcm.1.1 hcm.1.2.1).1 hca).2.1
  have hidx : ((inputCode (R.length, history) hinput).rightVertex e).val =
      firstVertex (R.length, history) false (indexedCell (R.length, history) hinput e).1.2 := by
    change ((packedRegion _).2.getD e (0, 0)).1.2 % _ = _
    rw [packedCell_getD]
    exact Nat.mod_eq_of_lt (firstVertex_spec hui).1
  have hv := firstVertex_coordinate hui
  change (pointValue (cornerList R) ((vertexLabels _).getD _ (0, 0))).re = _
  rw [hidx]
  exact hv

theorem inputCode_bottom_coordinate {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length)
    (e : Fin (inputCode (R.length, history) hinput).cellCount) :
    (originalVertex (cornerList R) (R.length, history)
      ((inputCode (R.length, history) hinput).bottomVertex e)).im =
      ((cornerList R).getD (indexedCell (R.length, history) hinput e).2.1 0).im := by
  have hcm := mem_coarseCells.mp (indexedCell_mem (R.length, history) hinput e)
  have hca := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcm.2).1).2
  have hui := ((coarseAdjacent_correct h hcm.1.2.2.1 hcm.1.2.2.2).1 hca).1
  have hidx : ((inputCode (R.length, history) hinput).bottomVertex e).val =
      firstVertex (R.length, history) true (indexedCell (R.length, history) hinput e).2.1 := by
    change ((packedRegion _).2.getD e (0, 0)).2.1 % _ = _
    rw [packedCell_getD]
    exact Nat.mod_eq_of_lt (firstVertex_spec hui).1
  have hv := firstVertex_coordinate hui
  change (pointValue (cornerList R) ((vertexLabels _).getD _ (0, 0))).im = _
  rw [hidx]
  exact hv

theorem inputCode_top_coordinate {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length)
    (e : Fin (inputCode (R.length, history) hinput).cellCount) :
    (originalVertex (cornerList R) (R.length, history)
      ((inputCode (R.length, history) hinput).topVertex e)).im =
      ((cornerList R).getD (indexedCell (R.length, history) hinput e).2.2 0).im := by
  have hcm := mem_coarseCells.mp (indexedCell_mem (R.length, history) hinput e)
  have hca := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcm.2).1).2
  have hui := ((coarseAdjacent_correct h hcm.1.2.2.1 hcm.1.2.2.2).1 hca).2.1
  have hidx : ((inputCode (R.length, history) hinput).topVertex e).val =
      firstVertex (R.length, history) true (indexedCell (R.length, history) hinput e).2.2 := by
    change ((packedRegion _).2.getD e (0, 0)).2.2 % _ = _
    rw [packedCell_getD]
    exact Nat.mod_eq_of_lt (firstVertex_spec hui).1
  have hv := firstVertex_coordinate hui
  change (pointValue (cornerList R) ((vertexLabels _).getD _ (0, 0))).im = _
  rw [hidx]
  exact hv

def runtimeCell (V : List Plane) (input : TableInput)
    (hinput : 0 < (vertexLabels input).length)
    (e : Fin (inputCode input hinput).cellCount) : Set Plane :=
  {z | (normalizedVertex V input hinput ((inputCode input hinput).leftVertex e)).re < z.re ∧
    z.re < (normalizedVertex V input hinput ((inputCode input hinput).rightVertex e)).re ∧
    (normalizedVertex V input hinput ((inputCode input hinput).bottomVertex e)).im < z.im ∧
    z.im < (normalizedVertex V input hinput ((inputCode input hinput).topVertex e)).im}

theorem runtimeCell_eq_vadd {R : List (Plane × Plane)} {history : List Bool}
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length)
    (e : Fin (inputCode (R.length, history) hinput).cellCount) :
    runtimeCell (cornerList R) (R.length, history) hinput e =
      (-anchor (cornerList R) (R.length, history) hinput) +ᵥ
        cellSet (cornerList R) (indexedCell (R.length, history) hinput e) := by
  ext z
  simp only [runtimeCell, normalizedVertex, Complex.sub_re, Complex.sub_im,
    inputCode_left_coordinate h hinput e, inputCode_right_coordinate h hinput e,
    inputCode_bottom_coordinate h hinput e, inputCode_top_coordinate h hinput e,
    Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add,
    cellSet, Tiling.AxisParallel.FiniteRectangles.cell, Complex.mem_reProdIm, Set.mem_Ioo,
    Complex.add_re, Complex.add_im]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    constructor <;> constructor <;> linarith
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem indexedCell_union (V : List Plane) (input : TableInput)
    (hinput : 0 < (vertexLabels input).length) :
    (⋃ e : Fin (inputCode input hinput).cellCount, cellSet V (indexedCell input hinput e)) =
      ⋃ c ∈ coarseCells input, cellSet V c := by
  ext z
  constructor
  · intro hz
    obtain ⟨e, hz⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨indexedCell input hinput e,
      mem_iUnion.mpr ⟨indexedCell_mem input hinput e, hz⟩⟩
  · intro hz
    obtain ⟨c, hz⟩ := mem_iUnion.mp hz
    obtain ⟨hc, hz⟩ := mem_iUnion.mp hz
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hc
    have he : i < (inputCode input hinput).cellCount := by
      simpa only [inputCode, regionCode, packedRegion, List.length_map] using hi
    let e : Fin (inputCode input hinput).cellCount := ⟨i, he⟩
    have hce : indexedCell input hinput e = c := hget
    exact mem_iUnion.mpr ⟨e, hce.symm ▸ hz⟩

theorem runtimeCells_ae_eq {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length) :
    (⋃ e, runtimeCell (cornerList R) (R.length, history) hinput e) =ᵐ[volume]
      (translatedRegion hR (-anchor (cornerList R) (R.length, history) hinput)).openCarrier := by
  have hunion : (⋃ e, runtimeCell (cornerList R) (R.length, history) hinput e) =
      (-anchor (cornerList R) (R.length, history) hinput) +ᵥ coarseOpenCells R history := by
    simp only [runtimeCell_eq_vadd h hinput, ← Set.vadd_set_iUnion]
    rw [indexedCell_union]
    rfl
  rw [hunion, translatedRegion_openCarrier]
  have hae := (quasiMeasurePreserving_add_left volume
    (anchor (cornerList R) (R.length, history) hinput)).ae (coarseOpenCells_ae_eq hR h)
  filter_upwards [hae] with z hz
  apply propext
  change (z ∈ (-anchor (cornerList R) (R.length, history) hinput) +ᵥ
    coarseOpenCells R history) ↔ (z ∈ (-anchor (cornerList R) (R.length, history) hinput) +ᵥ Ω)
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add]
  exact Iff.of_eq hz

theorem normalizedVertex_range {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length) :
    Set.range (normalizedVertex (cornerList R) (R.length, history) hinput) =
      (translatedRegion hR (-anchor (cornerList R) (R.length, history) hinput)).vertices := by
  rw [translatedRegion_vertices, ← originalVertex_range hR h]
  have heq : normalizedVertex (cornerList R) (R.length, history) hinput =
      fun i => (-anchor (cornerList R) (R.length, history) hinput) +ᵥ
        originalVertex (cornerList R) (R.length, history) i := by
    funext i
    simp only [normalizedVertex, vadd_eq_add, sub_eq_add_neg, add_comm]
  rw [heq, Set.range_vadd]

/-- Semantic interpretation of the primitive-recursive rectangle frontend. Its
origin is the first retained intrinsic vertex, and its cells are disjoint. -/
def realization {R : List (Plane × Plane)} {Ω : Set Plane} {history : List Bool}
    (hR : RectanglePresentation R Ω) (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length) :
    Tiling.AxisParallel.Terminal.Executable.Realization (inputCode (R.length, history) hinput) where
  region := translatedRegion hR (-anchor (cornerList R) (R.length, history) hinput)
  vertex := normalizedVertex (cornerList R) (R.length, history) hinput
  vertex_injective := by
    intro i j heq
    exact originalVertex_injective h (sub_left_inj.mp heq)
  vertex_range := normalizedVertex_range hR h hinput
  wellFormed := by
    simp only [Tiling.AxisParallel.Terminal.Executable.RegionCode.wellFormed,
      decide_eq_true_eq, inputCode, regionCode, packedRegion, List.length_map]
    exact coarseCells_nonempty hR h
  origin_eq_zero := sub_self _
  left_lt_right := by
    intro e
    have hcm := mem_coarseCells.mp (indexedCell_mem (R.length, history) hinput e)
    have hca := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcm.2).1).1
    have hxp := (coarseAdjacent_correct h hcm.1.1 hcm.1.2.1).1 hca
    simp only [normalizedVertex, Complex.sub_re, inputCode_left_coordinate h hinput e,
      inputCode_right_coordinate h hinput e, sub_lt_sub_iff_right]
    exact (Tiling.AxisParallel.FiniteRectangles.pair_data hxp.2.2).2.2
  bottom_lt_top := by
    intro e
    have hcm := mem_coarseCells.mp (indexedCell_mem (R.length, history) hinput e)
    have hca := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hcm.2).1).2
    have hyp := (coarseAdjacent_correct h hcm.1.2.2.1 hcm.1.2.2.2).1 hca
    simp only [normalizedVertex, Complex.sub_im, inputCode_bottom_coordinate h hinput e,
      inputCode_top_coordinate h hinput e, sub_lt_sub_iff_right]
    exact (Tiling.AxisParallel.FiniteRectangles.pair_data hyp.2.2).2.2
  cells_pairwiseDisjoint := by
    intro e _ f _ hne
    change Disjoint (runtimeCell (cornerList R) (R.length, history) hinput e)
      (runtimeCell (cornerList R) (R.length, history) hinput f)
    rw [runtimeCell_eq_vadd h hinput e, runtimeCell_eq_vadd h hinput f,
      Set.disjoint_vadd_set]
    exact coarse_cells_disjoint h (indexedCell_mem _ _ e) (indexedCell_mem _ _ f)
      (fun heq => hne (indexedCell_injective _ _ heq))
  presentation_correct := runtimeCells_ae_eq hR h hinput

@[simp] theorem realization_vertex {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length) (i : Fin (vertexLabels _).length) :
    (realization hR h hinput).vertex i =
      originalVertex (cornerList R) (R.length, history) i -
        anchor (cornerList R) (R.length, history) hinput := rfl

@[simp] theorem realization_openCarrier {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length) :
    (realization hR h hinput).region.openCarrier =
      (-anchor (cornerList R) (R.length, history) hinput) +ᵥ Ω :=
  translatedRegion_openCarrier hR _

theorem realization_tilesOn_iff {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length) (T : Set Plane) :
    Tiling.AxisParallel.TilesOn (realization hR h hinput).region T univ ↔ Tiles Ω T := by
  let K := regionOfTile Ω (RectanglePresentation.isAxisParallelTile hR)
  let a := anchor (cornerList R) (R.length, history) hinput
  have hcarrier : (realization hR h hinput).region.openCarrier =
      Tiling.AxisParallel.positiveSimilarity 1 (-a) '' K.openCarrier := by
    rw [realization_openCarrier, Tiling.AxisParallel.positiveSimilarity_image_eq_vadd_smul,
      regionOfTile_openCarrier, one_smul]
  have hnative := Tiling.AxisParallel.tilesOn_positiveSimilarity_iff
    (K := K) (R := (realization hR h hinput).region) (S := T) (D := univ)
    (s := 1) (r := -a) (c := 0) (by norm_num) hcarrier
  have htiles : Tiling.AxisParallel.TilesOn (realization hR h hinput).region T univ ↔
      Tiling.AxisParallel.TilesOn K T univ := by
    simpa only [Tiling.AxisParallel.positiveSimilarity_image_eq_vadd_smul,
      one_smul, zero_vadd, add_zero, Set.vadd_set_univ] using hnative
  exact htiles.trans (tilingOn_iff_native Ω (RectanglePresentation.isAxisParallelTile hR)
    univ T).symm

theorem realization_tileable_iff {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length) :
    (∃ T, Tiling.AxisParallel.TilesOn (realization hR h hinput).region T univ) ↔
      ∃ T, Tiles Ω T :=
  exists_congr (fun T => realization_tilesOn_iff hR h hinput T)

theorem comparisonHistory_rectangles_correct {R : List (Plane × Plane)} {answer : Query → Bool}
    (hanswer : CorrectOracle (cornerList R) answer) :
    TableCorrect (cornerList R) (comparisonHistory (2 * R.length) answer) := by
  simpa only [cornerList_length] using comparisonHistory_correct hanswer

/-- The proof-layer realization of the actual finite-query frontend. The code
contains only data computed from the rectangle count and the finite answer list. -/
def realizationOfOracle {R : List (Plane × Plane)} {Ω : Set Plane}
    {answer : Query → Bool} (hR : RectanglePresentation R Ω)
    (hanswer : CorrectOracle (cornerList R) answer) :
    Tiling.AxisParallel.Terminal.Executable.Realization
      (inputCode (R.length, comparisonHistory (2 * R.length) answer)
        (vertexLabels_nonempty hR (comparisonHistory_rectangles_correct hanswer))) :=
  realization hR (comparisonHistory_rectangles_correct hanswer)
    (vertexLabels_nonempty hR (comparisonHistory_rectangles_correct hanswer))

theorem realizationOfOracle_tileable_iff {R : List (Plane × Plane)} {Ω : Set Plane}
    {answer : Query → Bool} (hR : RectanglePresentation R Ω)
    (hanswer : CorrectOracle (cornerList R) answer) :
    (∃ T, Tiling.AxisParallel.TilesOn (realizationOfOracle hR hanswer).region T univ) ↔
      ∃ T, Tiles Ω T :=
  realization_tileable_iff hR (comparisonHistory_rectangles_correct hanswer) _

end Tiling.AxisParallel.Decidability.RectangleInput
