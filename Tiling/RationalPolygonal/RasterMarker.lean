import Tiling.RationalPolygonal.Raster

set_option linter.style.header false

/-!
# Rigid raster markers

This file implements the finite marker geometry from Section 3 of
de Dios Pont--Grebík--Greenfeld--Madrid.  Nonzero colors are represented by disjoint eight-point
rings on a grid of spacing three.  Color zero fills the rest of the square and carries the two
asymmetric protrusions and holes which force tiling translations into one coarse-lattice coset.
-/

open Set
open TranslationalTilings
open scoped Pointwise

namespace Tiling.RationalPolygonal

/-- Integer-plane point with the displayed coordinates. -/
def latticePoint (x y : ℤ) : IntegerPlane := ![x, y]

@[simp]
theorem latticePoint_apply_zero (x y : ℤ) : latticePoint x y 0 = x :=
  rfl

@[simp]
theorem latticePoint_apply_one (x y : ℤ) : latticePoint x y 1 = y :=
  rfl

/-- A closed integer-coordinate rectangle. -/
noncomputable def gridBox (x₀ x₁ y₀ y₁ : ℤ) : Finset IntegerPlane :=
  (Finset.Icc x₀ x₁ ×ˢ Finset.Icc y₀ y₁).image
    (fun p ↦ latticePoint p.1 p.2)

@[simp]
theorem mem_gridBox_iff {x₀ x₁ y₀ y₁ : ℤ} {z : IntegerPlane} :
    z ∈ gridBox x₀ x₁ y₀ y₁ ↔
      x₀ ≤ z 0 ∧ z 0 ≤ x₁ ∧ y₀ ≤ z 1 ∧ z 1 ≤ y₁ := by
  classical
  constructor
  · intro hz
    rw [gridBox, Finset.mem_image] at hz
    obtain ⟨p, hp, hpz⟩ := hz
    have hp' : p.1 ∈ Finset.Icc x₀ x₁ ∧ p.2 ∈ Finset.Icc y₀ y₁ := by
      exact Finset.mem_product.mp hp
    rw [Finset.mem_Icc, Finset.mem_Icc] at hp'
    obtain ⟨hp₀, hp₁⟩ := hp'
    subst z
    simpa only [latticePoint_apply_zero, latticePoint_apply_one] using
      ⟨hp₀.1, hp₀.2, hp₁.1, hp₁.2⟩
  · rintro ⟨hx₀, hx₁, hy₀, hy₁⟩
    rw [gridBox, Finset.mem_image]
    refine ⟨(z 0, z 1), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hx₀, hx₁⟩,
        Finset.mem_Icc.mpr ⟨hy₀, hy₁⟩⟩, ?_⟩
    funext i
    fin_cases i <;> rfl

/-- Marker square side length.  Taking `k = M` is the paper's construction with a valid (though
not size-minimal) choice satisfying `M ≤ k²`. -/
def markerSide (M : ℕ) : ℕ := 3 * M + 4

/-- Center of the eight-point marker assigned to a nonzero color. -/
def markerCenter {M : ℕ} (i : Fin M) : IntegerPlane :=
  latticePoint (3 * (i : ℤ)) 3

/-- The eight-point ring around a nonzero color center. -/
noncomputable def markerRing {M : ℕ} (i : Fin M) : Finset IntegerPlane :=
  (gridBox (3 * (i : ℤ) - 1) (3 * (i : ℤ) + 1) 2 4).erase
    (markerCenter i)

/-- The unmodified `N × N` marker square. -/
noncomputable def markerSquare (M : ℕ) : Finset IntegerPlane :=
  gridBox 0 (markerSide M - 1) 0 (markerSide M - 1)

/-- The union of all nonzero-color marker rings. -/
noncomputable def nonzeroMarkerRings (M : ℕ) : Finset IntegerPlane :=
  Finset.univ.biUnion fun i : Fin M ↦
    if i.val = 0 then ∅ else markerRing i

/-- Horizontal protrusion in the distinguished color-zero marker. -/
def markerEast (M : ℕ) : IntegerPlane :=
  latticePoint (markerSide M) 1

/-- Vertical protrusion in the distinguished color-zero marker. -/
def markerNorth (M : ℕ) : IntegerPlane :=
  latticePoint 1 (markerSide M)

/-- First color-zero marker hole. -/
def markerWestHole : IntegerPlane := latticePoint 0 1

/-- Second color-zero marker hole. -/
def markerSouthHole : IntegerPlane := latticePoint 1 0

/-- Distinguished marker: square complement of all rings, with two protrusions and two holes. -/
noncomputable def markerZero (M : ℕ) : Finset IntegerPlane :=
  ((insert (markerNorth M)
    (insert (markerEast M) (markerSquare M \ nonzeroMarkerRings M))).erase
      markerWestHole).erase markerSouthHole

/-- The square after making the two asymmetric boundary holes and protrusions. -/
noncomputable def modifiedMarkerSquare (M : ℕ) : Finset IntegerPlane :=
  ((insert (markerNorth M) (insert (markerEast M) (markerSquare M))).erase
    markerWestHole).erase markerSouthHole

/-- Marker block assigned to a color. -/
noncomputable def markerBlock {M : ℕ} (i : Fin M) : Finset IntegerPlane :=
  if i.val = 0 then markerZero M else markerRing i

/-- Union of all color blocks in the marker family. -/
noncomputable def markerUnion (M : ℕ) : Finset IntegerPlane :=
  Finset.univ.biUnion fun i : Fin M ↦ markerBlock i

@[simp]
theorem markerBlock_zero {M : ℕ} (hM : 0 < M) :
    markerBlock ⟨0, hM⟩ = markerZero M := by
  simp [markerBlock]

theorem markerBlock_of_ne_zero {M : ℕ} {i : Fin M} (hi : i.val ≠ 0) :
    markerBlock i = markerRing i := by
  simp [markerBlock, hi]

/-- A nonzero-color center lies strictly inside the marker square. -/
theorem markerCenter_mem_markerSquare {M : ℕ} {i : Fin M} (hi : i.val ≠ 0) :
    markerCenter i ∈ markerSquare M := by
  rw [markerSquare, mem_gridBox_iff]
  simp only [markerCenter, latticePoint_apply_zero, latticePoint_apply_one,
    markerSide, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hiLower : (1 : ℤ) ≤ i := by
    omega
  have hiUpper : (i : ℤ) < M := by
    exact_mod_cast i.isLt
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

/-- Each nonzero marker is exactly an eight-point ring. -/
theorem markerRing_card {M : ℕ} (i : Fin M) :
    (markerRing i).card = 8 := by
  rw [markerRing, Finset.card_erase_of_mem]
  · rw [gridBox]
    rw [Finset.card_image_of_injective]
    · have hproduct := Finset.card_product
        (Finset.Icc (3 * (i : ℤ) - 1) (3 * (i : ℤ) + 1))
        (Finset.Icc (2 : ℤ) 4)
      rw [hproduct, Int.card_Icc, Int.card_Icc]
      have hx : 3 * (i : ℤ) + 1 + 1 - (3 * (i : ℤ) - 1) = 3 := by
        ring
      rw [hx]
      decide
    · intro p q hpq
      apply Prod.ext
      · exact congrFun hpq 0
      · exact congrFun hpq 1
  · rw [mem_gridBox_iff]
    simp [markerCenter]

/-- Coordinate bounds for a point in a nonzero marker ring. -/
theorem markerRing_bounds {M : ℕ} {i : Fin M} {z : IntegerPlane}
    (hz : z ∈ markerRing i) :
    3 * (i : ℤ) - 1 ≤ z 0 ∧ z 0 ≤ 3 * (i : ℤ) + 1 ∧
      2 ≤ z 1 ∧ z 1 ≤ 4 := by
  exact mem_gridBox_iff.mp (Finset.mem_of_mem_erase hz)

/-- Rings belonging to distinct colors are disjoint. -/
theorem markerRing_disjoint {M : ℕ} {i j : Fin M} (hij : i ≠ j) :
    Disjoint (markerRing i) (markerRing j) := by
  rw [Finset.disjoint_left]
  intro z hzi hzj
  have hi := markerRing_bounds hzi
  have hj := markerRing_bounds hzj
  have hval : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  omega

/-- A nonzero-color ring is contained in the unmodified marker square. -/
theorem markerRing_subset_markerSquare {M : ℕ} {i : Fin M}
    (hi : i.val ≠ 0) :
    markerRing i ⊆ markerSquare M := by
  intro z hz
  rw [markerSquare, mem_gridBox_iff]
  have hb := markerRing_bounds hz
  have hiLower : (1 : ℤ) ≤ i := by omega
  have hiUpper : (i : ℤ) < M := by exact_mod_cast i.isLt
  simp only [markerSide, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- A nonzero-color ring occurs in the union removed from the color-zero block. -/
theorem markerRing_subset_nonzeroMarkerRings {M : ℕ} {i : Fin M}
    (hi : i.val ≠ 0) :
    markerRing i ⊆ nonzeroMarkerRings M := by
  intro z hz
  rw [nonzeroMarkerRings, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, by simp [hi, hz]⟩

/-- The two protrusions lie outside every nonzero marker ring. -/
theorem protrusions_not_mem_markerRing {M : ℕ} {i : Fin M}
    (hi : i.val ≠ 0) :
    markerEast M ∉ markerRing i ∧ markerNorth M ∉ markerRing i := by
  constructor
  · intro h
    have hb := markerRing_bounds h
    simp only [markerEast, latticePoint_apply_one] at hb
    omega
  · intro h
    have hb := markerRing_bounds h
    have hiLower : (1 : ℤ) ≤ i := by omega
    simp only [markerNorth, latticePoint_apply_zero] at hb
    omega

/-- The distinguished color-zero block is disjoint from every nonzero ring. -/
theorem markerZero_disjoint_markerRing {M : ℕ} {i : Fin M}
    (hi : i.val ≠ 0) :
    Disjoint (markerZero M) (markerRing i) := by
  rw [Finset.disjoint_left]
  intro z hz0 hzi
  have hz0' := (Finset.mem_erase.mp hz0).2
  have hz0'' := (Finset.mem_erase.mp hz0').2
  simp only [Finset.mem_insert] at hz0''
  rcases hz0'' with hNorth | hEast | hbase
  · subst z
    exact (protrusions_not_mem_markerRing hi).2 hzi
  · subst z
    exact (protrusions_not_mem_markerRing hi).1 hzi
  · have hznot : z ∉ nonzeroMarkerRings M := (Finset.mem_sdiff.mp hbase).2
    exact hznot (markerRing_subset_nonzeroMarkerRings hi hzi)

/-- Distinct color markers are pairwise disjoint. -/
theorem markerBlock_disjoint {M : ℕ} {i j : Fin M} (hij : i ≠ j) :
    Disjoint (markerBlock i) (markerBlock j) := by
  by_cases hi : i.val = 0
  · have hj : j.val ≠ 0 := by
      intro hj0
      apply hij
      apply Fin.ext
      omega
    rw [markerBlock, if_pos hi, markerBlock_of_ne_zero hj]
    exact markerZero_disjoint_markerRing hj
  · by_cases hj : j.val = 0
    · rw [markerBlock_of_ne_zero hi, markerBlock, if_pos hj]
      exact (markerZero_disjoint_markerRing hi).symm
    · rw [markerBlock_of_ne_zero hi, markerBlock_of_ne_zero hj]
      exact markerRing_disjoint hij

private theorem markerZero_subset_modifiedMarkerSquare (M : ℕ) :
    markerZero M ⊆ modifiedMarkerSquare M := by
  classical
  intro z hz
  rw [markerZero, Finset.mem_erase, Finset.mem_erase] at hz
  obtain ⟨hsouth, hwest, hbase⟩ := hz
  rw [modifiedMarkerSquare, Finset.mem_erase, Finset.mem_erase]
  refine ⟨hsouth, hwest, ?_⟩
  rcases Finset.mem_insert.mp hbase with hNorth | hrest
  · exact Finset.mem_insert.mpr (Or.inl hNorth)
  · rcases Finset.mem_insert.mp hrest with hEast | hbase'
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inl hEast)))
    · have hsquare : z ∈ markerSquare M := (Finset.mem_sdiff.mp hbase').1
      have hinner : z ∈ insert (markerEast M) (markerSquare M) :=
        Finset.mem_insert.mpr (Or.inr hsquare)
      exact Finset.mem_insert.mpr (Or.inr hinner)

private theorem markerRing_subset_modifiedMarkerSquare {M : ℕ} {i : Fin M}
    (hi : i.val ≠ 0) : markerRing i ⊆ modifiedMarkerSquare M := by
  classical
  intro z hz
  have hsquare := markerRing_subset_markerSquare hi hz
  have hsouth : z ≠ markerSouthHole := by
    intro hzSouth
    subst z
    have hb := markerRing_bounds hz
    simp only [markerSouthHole, latticePoint_apply_one] at hb
    omega
  have hwest : z ≠ markerWestHole := by
    intro hzWest
    subst z
    have hb := markerRing_bounds hz
    simp only [markerWestHole, latticePoint_apply_one] at hb
    omega
  rw [modifiedMarkerSquare, Finset.mem_erase, Finset.mem_erase]
  exact ⟨hsouth, hwest, Finset.mem_insert.mpr <|
    Or.inr <| Finset.mem_insert.mpr <| Or.inr hsquare⟩

private theorem markerUnion_subset_modifiedMarkerSquare {M : ℕ} :
    markerUnion M ⊆ modifiedMarkerSquare M := by
  classical
  intro z hz
  rw [markerUnion, Finset.mem_biUnion] at hz
  obtain ⟨i, -, hzi⟩ := hz
  by_cases hi : i.val = 0
  · rw [markerBlock, if_pos hi] at hzi
    exact markerZero_subset_modifiedMarkerSquare M hzi
  · rw [markerBlock_of_ne_zero hi] at hzi
    exact markerRing_subset_modifiedMarkerSquare hi hzi

private theorem modifiedMarkerSquare_subset_markerUnion {M : ℕ} (hM : 0 < M) :
    modifiedMarkerSquare M ⊆ markerUnion M := by
  classical
  intro z hz
  rw [modifiedMarkerSquare, Finset.mem_erase, Finset.mem_erase] at hz
  obtain ⟨hsouth, hwest, hmodified⟩ := hz
  rw [markerUnion, Finset.mem_biUnion]
  by_cases hrings : z ∈ nonzeroMarkerRings M
  · rw [nonzeroMarkerRings, Finset.mem_biUnion] at hrings
    obtain ⟨i, -, hi⟩ := hrings
    split at hi
    · simp at hi
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [markerBlock_of_ne_zero (by assumption)]
      exact hi
  · let zero : Fin M := ⟨0, hM⟩
    refine ⟨zero, Finset.mem_univ zero, ?_⟩
    rw [markerBlock_zero hM, markerZero, Finset.mem_erase, Finset.mem_erase]
    refine ⟨hsouth, hwest, ?_⟩
    rcases Finset.mem_insert.mp hmodified with hNorth | hrest
    · exact Finset.mem_insert.mpr (Or.inl hNorth)
    · rcases Finset.mem_insert.mp hrest with hEast | hsquare
      · exact Finset.mem_insert.mpr (Or.inr <| Finset.mem_insert.mpr <| Or.inl hEast)
      · exact Finset.mem_insert.mpr (Or.inr <| Finset.mem_insert.mpr <|
          Or.inr (Finset.mem_sdiff.mpr ⟨hsquare, hrings⟩))

/-- The marker blocks partition exactly the modified square used in the raster construction. -/
theorem markerUnion_eq_modifiedMarkerSquare {M : ℕ} (hM : 0 < M) :
    markerUnion M = modifiedMarkerSquare M := by
  apply Finset.Subset.antisymm
  · exact markerUnion_subset_modifiedMarkerSquare
  · exact modifiedMarkerSquare_subset_markerUnion hM

section ColoredRaster

/-- Package a finite family of lattice tiles as one tile in `ℤ² × ZMod M`, with the second
coordinate recording the color. -/
noncomputable def coloredRasterTile {M : ℕ}
    (tile : Fin M → Finset IntegerPlane) :
    Finset (IntegerPlane × ZMod M) :=
  Finset.univ.biUnion fun i ↦
    (tile i).image fun z ↦ (z, (i : ZMod M))

@[simp]
theorem mem_coloredRasterTile_iff {M : ℕ}
    {tile : Fin M → Finset IntegerPlane} {p : IntegerPlane × ZMod M} :
    p ∈ coloredRasterTile tile ↔
      ∃ i : Fin M, p.1 ∈ tile i ∧ (i : ZMod M) = p.2 := by
  classical
  simp only [coloredRasterTile, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨i, z, hz, hzp⟩
    exact ⟨i, hzp ▸ hz, congrArg Prod.snd hzp⟩
  · rintro ⟨i, hi, hcolor⟩
    exact ⟨i, p.1, hi, Prod.ext rfl hcolor⟩

/-- Embed one common translation set in the zero-color layer. -/
def coloredTranslations {M : ℕ} (T : Set IntegerPlane) :
    Set (IntegerPlane × ZMod M) :=
  (fun t ↦ (t, 0)) '' T

@[simp]
theorem mem_coloredTranslations_iff {M : ℕ} {T : Set IntegerPlane}
    {p : IntegerPlane × ZMod M} :
    p ∈ coloredTranslations (M := M) T ↔
      ∃ t ∈ T, (t, 0) = p :=
  Iff.rfl

/-- Distinct standard representatives give distinct elements of `ZMod M`. -/
theorem fin_cast_zmod_injective {M : ℕ} [NeZero M] :
    Function.Injective (fun i : Fin M ↦ (i : ZMod M)) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg ZMod.val hij
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt] using hval

/-- A simultaneous tiling by a finite tile family is exactly a one-tile tiling in the product
group whose finite coordinate records the family member. -/
theorem coloredRasterTile_tilesUniverse_iff {M : ℕ} [NeZero M]
    (tile : Fin M → Finset IntegerPlane) (T : Set IntegerPlane) :
    TilesUniverse (coloredRasterTile tile) (coloredTranslations (M := M) T) ↔
      ∀ i, TilesUniverse (tile i) T := by
  constructor
  · intro hcolored i
    apply tilesUniverse_of_existsUnique
    intro x
    obtain ⟨f, hf, hfunique⟩ :=
      existsUnique_tile_representation hcolored (x, (i : ZMod M))
    obtain ⟨j, hjtile, hjcolor⟩ := mem_coloredRasterTile_iff.mp hf.1
    obtain ⟨t, htT, htEq⟩ := hf.2
    have hsecond : (i : ZMod M) - f.2 = 0 := by
      have h := congrArg Prod.snd htEq.symm
      change (i : ZMod M) - f.2 = 0 at h
      exact h
    have hfcolor : f.2 = (i : ZMod M) := (sub_eq_zero.mp hsecond).symm
    have hji : j = i := fin_cast_zmod_injective (hjcolor.trans hfcolor)
    subst j
    refine ⟨f.1, ?_, ?_⟩
    · refine ⟨hjtile, ?_⟩
      have hfirst : x - f.1 = t := by
        have h := congrArg Prod.fst htEq.symm
        change x - f.1 = t at h
        exact h
      rwa [hfirst]
    · intro g hg
      let candidate : IntegerPlane × ZMod M := (g, (i : ZMod M))
      have hcTile : candidate ∈ coloredRasterTile tile := by
        exact mem_coloredRasterTile_iff.mpr ⟨i, hg.1, rfl⟩
      have hcTranslation : (x, (i : ZMod M)) - candidate ∈
          coloredTranslations (M := M) T := by
        refine ⟨x - g, hg.2, ?_⟩
        ext
        · rfl
        · simp [candidate]
      have hcf : candidate = f := hfunique candidate ⟨hcTile, hcTranslation⟩
      exact congrArg Prod.fst hcf
  · intro hfamily
    apply tilesUniverse_of_existsUnique
    rintro ⟨x, c⟩
    let i : Fin M := ⟨c.val, ZMod.val_lt c⟩
    have hic : (i : ZMod M) = c := by
      simpa only [i] using ZMod.natCast_zmod_val c
    obtain ⟨z, hz, hzunique⟩ :=
      existsUnique_tile_representation (hfamily i) x
    let f : IntegerPlane × ZMod M := (z, c)
    refine ⟨f, ?_, ?_⟩
    · constructor
      · exact mem_coloredRasterTile_iff.mpr ⟨i, hz.1, hic⟩
      · refine ⟨x - z, hz.2, ?_⟩
        ext
        · rfl
        · simp [f]
    · intro g hg
      obtain ⟨j, hgtile, hjcolor⟩ := mem_coloredRasterTile_iff.mp hg.1
      obtain ⟨t, htT, htEq⟩ := hg.2
      have hgcolor : g.2 = c := by
        have : c - g.2 = 0 := by
          have h := congrArg Prod.snd htEq.symm
          change c - g.2 = 0 at h
          exact h
        exact (sub_eq_zero.mp this).symm
      have hji : j = i := by
        apply fin_cast_zmod_injective
        exact hjcolor.trans (hgcolor.trans hic.symm)
      subst j
      have hfirst : x - g.1 = t := by
        have h := congrArg Prod.fst htEq.symm
        change x - g.1 = t at h
        exact h
      have hgz : g.1 = z := by
        apply hzunique g.1
        exact ⟨hgtile, hfirst ▸ htT⟩
      apply Prod.ext
      · exact hgz
      · exact hgcolor

end ColoredRaster

end Tiling.RationalPolygonal
