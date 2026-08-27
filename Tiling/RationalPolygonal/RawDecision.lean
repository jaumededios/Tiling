import Tiling.RationalPolygonal.Decision
import Tiling.RationalPolygonal.SignatureCorrectness

set_option linter.style.header false

/-!
# Executable tileability decision for raw rational polygons

This module closes the executable pipeline from a valid finite rational triangulation to the
bounded planar lattice decision procedure.  The compiler computes the positive-measure signature
family, moves one nonempty signature to color zero, applies the executable rigid planar marker,
and runs `planarTileDecision` on the resulting finite lattice tile.

Only unordered equality of the executable and semantic signature families is needed.  The proof
uses marker rigidity to identify tileability of any chosen family enumeration, so it does not
require the executable marker raster to be literally equal to the separately ordered canonical
semantic raster.
-/

open Set TranslationalTilings

namespace Tiling.RationalPolygonal.Raw.Decision

open Compiler

/-- The total Boolean decision on raw rational-coordinate input.  The fallback branch is
executable; semantic signature correctness proves that valid input never reaches it. -/
def rawTileDecision (P : Code.Input) : Bool :=
  match nonemptyRasterFamily? (signatureFamily (normalizedTriangles P)) with
  | none => false
  | some input => planarTileDecision (planarRasterTileExec input)

/-- A signature selected by `firstNonempty` occurred in the original list. -/
theorem firstNonempty_mem {family : List (Finset IntegerPlane)}
    {F : Finset IntegerPlane} (h : firstNonempty family = some F) : F ∈ family := by
  induction family with
  | nil => simp [firstNonempty] at h
  | cons G family ih =>
      simp only [firstNonempty] at h
      split at h
      · exact List.mem_cons_of_mem G (ih h)
      · simp only [Option.some.injEq] at h
        subst F
        exact List.mem_cons_self

/-- If a list contains a nonempty signature, `firstNonempty` returns some signature. -/
theorem firstNonempty_exists_of_exists_nonempty {family : List (Finset IntegerPlane)}
    (h : ∃ F ∈ family, F.Nonempty) : ∃ F, firstNonempty family = some F := by
  induction family with
  | nil => simp at h
  | cons G family ih =>
      by_cases hG : G = ∅
      · have htail : ∃ F ∈ family, F.Nonempty := by
          obtain ⟨F, hF, hFne⟩ := h
          have hFG : F ≠ G := by
            intro hEq
            subst F
            exact hFne.ne_empty hG
          exact ⟨F, (List.mem_cons.mp hF).resolve_left hFG, hFne⟩
        obtain ⟨F, hfirst⟩ := ih htail
        exact ⟨F, by simp [firstNonempty, hG, hfirst]⟩
      · exact ⟨G, by simp [firstNonempty, hG]⟩

/-- Universal quantification over array indices is equivalent to universal quantification over
array members. -/
theorem forall_fin_get_iff_forall_mem {α : Type*} (a : Array α) (Q : α → Prop) :
    (∀ i : Fin a.size, Q a[i]) ↔ ∀ x ∈ a, Q x := by
  constructor
  · intro h x hx
    obtain ⟨i, hi, hix⟩ := Array.mem_iff_getElem.mp hx
    subst x
    exact h ⟨i, hi⟩
  · intro h i
    exact h a[i] (Array.getElem_mem i.isLt)

/-- Reordering one known member to the head does not change list membership. -/
theorem mem_cons_erase_iff {α : Type*} [BEq α] [LawfulBEq α]
    {a x : α} {xs : List α} (ha : a ∈ xs) :
    x ∈ a :: xs.erase a ↔ x ∈ xs := by
  by_cases hxa : x = a
  · subst x
    constructor
    · intro _
      exact ha
    · intro _
      exact List.mem_cons_self
  · simp only [List.mem_cons, hxa, false_or, List.mem_erase_of_ne hxa]

/-- The array packaged by `nonemptyRasterFamily?` enumerates exactly the input list family. -/
theorem nonemptyRasterFamily_members {family : List (Finset IntegerPlane)}
    {input : NonemptyPlanarRasterFamily}
    (hinput : nonemptyRasterFamily? family = some input) :
    ∀ F, F ∈ input.tiles ↔ F ∈ family := by
  unfold nonemptyRasterFamily? at hinput
  split at hinput
  · contradiction
  · rename_i first hfirst
    have hfirstMem : first ∈ family := firstNonempty_mem hfirst
    simp only [Option.some.injEq] at hinput
    subst input
    intro F
    simpa only [List.mem_toArray] using
      (mem_cons_erase_iff (a := first) (x := F) hfirstMem)

/-- The packaged array admits one common tiling exactly when every member of the original list
admits that same tiling. -/
theorem nonemptyRasterFamily_tiles_iff {family : List (Finset IntegerPlane)}
    {input : NonemptyPlanarRasterFamily}
    (hinput : nonemptyRasterFamily? family = some input) :
    (∃ T : Set IntegerPlane,
      ∀ i : Fin input.tiles.size, TilesUniverse input.tiles[i] T) ↔
      ∃ T : Set IntegerPlane, ∀ F ∈ family, TilesUniverse F T := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro F hF
    apply (forall_fin_get_iff_forall_mem input.tiles
      (fun G ↦ TilesUniverse G T)).mp hT F
    exact (nonemptyRasterFamily_members hinput F).mpr hF
  · rintro ⟨T, hT⟩
    refine ⟨T, (forall_fin_get_iff_forall_mem input.tiles
      (fun G ↦ TilesUniverse G T)).mpr ?_⟩
    intro F hF
    exact hT F ((nonemptyRasterFamily_members hinput F).mp hF)

/-- The generic rigid planar marker is tileable exactly when its entire finite color family has
one common translation-set tiling. -/
theorem exists_planarRasterTile_tiling_iff_family {M : ℕ} (hM : 0 < M)
    (tile : Fin M → Finset IntegerPlane) (hzero : (tile ⟨0, hM⟩).Nonempty) :
    (∃ U : Set IntegerPlane, TilesUniverse (planarRasterTile tile) U) ↔
      ∃ T : Set IntegerPlane, ∀ i, TilesUniverse (tile i) T := by
  constructor
  · rintro ⟨U, hU⟩
    exact exists_family_tiling_of_planarRasterTile hM tile hzero U hU
  · rintro ⟨T, hT⟩
    exact ⟨markerTranslationSet M T,
      planarRasterTile_tilesUniverse_of_family hM tile T hT⟩

/-- Simultaneous tiling of every relevant signature of the normalized region is equivalent to
real-plane tileability of the original rational region. -/
theorem relevantSignatures_tileable_iff (P : Code.Input) :
    (∃ S : Set IntegerPlane,
      ∀ F ∈ P.rationalPolygonalRegion.normalizedRegion.relevantSignatures,
        TilesUniverse F S) ↔
      ∃ T : Set Plane, P.rationalPolygonalRegion.toPolygonalRegion.Tiles T := by
  constructor
  · rintro ⟨S, hS⟩
    have hnormalized : P.rationalPolygonalRegion.normalizedRegion.Tiles
        (integerPoint '' S) :=
      (PolygonalRegion.tiles_integerPoint_image_iff_relevantSignatures
        P.rationalPolygonalRegion.normalizedRegion S).mpr hS
    exact ⟨P.rationalPolygonalRegion.denormalizedTranslations (integerPoint '' S),
      P.rationalPolygonalRegion.tiles_of_normalizedRegion_tiles hnormalized⟩
  · rintro ⟨T, hT⟩
    have hnormalized := P.rationalPolygonalRegion.normalizedRegion_tiles hT
    obtain ⟨S, hStiles, -⟩ :=
      P.rationalPolygonalRegion.normalizedRegion.exists_integer_signature_tiling
        P.rationalPolygonalRegion.normalizedRegion_hasIntegerVertices hnormalized
    exact ⟨S, (PolygonalRegion.tiles_integerPoint_image_iff_relevantSignatures
      P.rationalPolygonalRegion.normalizedRegion S).mp hStiles⟩

/-- Unordered equality of the executable and semantic signature families. -/
def SignatureFamilyCorrect (P : Code.Input) : Prop :=
  (signatureFamily (normalizedTriangles P)).toFinset =
    P.rationalPolygonalRegion.normalizedRegion.relevantSignatures

/-- Semantic family correctness guarantees that executable nonempty-family packaging succeeds. -/
theorem nonemptyRasterFamily_exists (P : Code.Input) (hcorrect : SignatureFamilyCorrect P) :
    ∃ input, nonemptyRasterFamily?
      (signatureFamily (normalizedTriangles P)) = some input := by
  let K := P.rationalPolygonalRegion.normalizedRegion
  obtain ⟨F, hF, hFne⟩ := K.exists_nonempty_relevantSignature
  have hFexec : F ∈ signatureFamily (normalizedTriangles P) := by
    have : F ∈ (signatureFamily (normalizedTriangles P)).toFinset := by
      rw [hcorrect]
      exact hF
    simpa using this
  obtain ⟨first, hfirst⟩ :=
    firstNonempty_exists_of_exists_nonempty ⟨F, hFexec, hFne⟩
  unfold nonemptyRasterFamily?
  split
  · rename_i hnone
    rw [hnone] at hfirst
    contradiction
  · exact ⟨_, rfl⟩

/-- Under the unordered signature-family bridge, the total raw Boolean decides real-plane
tileability of the source rational polygon. -/
theorem rawTileDecision_eq_true_iff (P : Code.Input)
    (hcorrect : SignatureFamilyCorrect P) :
    rawTileDecision P = true ↔
      ∃ T : Set Plane, P.rationalPolygonalRegion.toPolygonalRegion.Tiles T := by
  obtain ⟨input, hinput⟩ := nonemptyRasterFamily_exists P hcorrect
  rw [rawTileDecision, hinput]
  rw [planarTileDecision_eq_true_iff, planarRasterTileExec_eq_planarRasterTile]
  rw [exists_planarRasterTile_tiling_iff_family input.size_pos
    (fun i : Fin input.tiles.size ↦ input.tiles[i]) input.first_nonempty]
  rw [nonemptyRasterFamily_tiles_iff hinput]
  have hfamilies :
      (∃ T : Set IntegerPlane,
          ∀ F ∈ signatureFamily (normalizedTriangles P), TilesUniverse F T) ↔
        ∃ T : Set IntegerPlane,
          ∀ F ∈ P.rationalPolygonalRegion.normalizedRegion.relevantSignatures,
            TilesUniverse F T := by
    constructor
    · rintro ⟨T, hT⟩
      refine ⟨T, ?_⟩
      intro F hF
      apply hT F
      have : F ∈ (signatureFamily (normalizedTriangles P)).toFinset := by
        rw [hcorrect]
        exact hF
      simpa using this
    · rintro ⟨T, hT⟩
      refine ⟨T, ?_⟩
      intro F hF
      apply hT F
      rw [← hcorrect]
      simpa using hF
  rw [hfamilies]
  exact relevantSignatures_tileable_iff P

/-- Correctness contract for one Boolean algorithm on every valid raw rational triangulation. -/
def DecidesRawTileability (algorithm : Code.Input → Bool) : Prop :=
  ∀ P, algorithm P = true ↔
    ∃ T : Set Plane, P.rationalPolygonalRegion.toPolygonalRegion.Tiles T

/-- The total executable raw decision satisfies the paper-facing tileability contract. -/
theorem rawTileDecision_decidesRawTileability :
    DecidesRawTileability rawTileDecision := by
  intro P
  exact rawTileDecision_eq_true_iff P
    (signatureFamily_toFinset_eq_relevantSignatures P)

/-- There is one executable Boolean algorithm deciding tileability of every valid raw rational
triangulation. -/
theorem exists_rawTileabilityAlgorithm :
    ∃ algorithm : Code.Input → Bool, DecidesRawTileability algorithm :=
  ⟨rawTileDecision, rawTileDecision_decidesRawTileability⟩

end Tiling.RationalPolygonal.Raw.Decision
