import Tiling.RationalPolygonal.RasterMarker

set_option linter.style.header false

/-!
# Executable planar raster markers

This module gives computable copies of the finite marker construction used in Section 3 of
de Dios Pont--Grebík--Greenfeld--Madrid.  In particular, it avoids the classical locally finite
order instance used by the semantic integer interval: `integerIntervalExec` enumerates integer
offsets from the lower endpoint instead.

The bridge theorems identify every executable constructor with its semantic counterpart in
`RasterMarker`.  Thus downstream compilers can produce an actual `Finset IntegerPlane`, while
all tiling theorems proved for `planarRasterTile` remain available without duplication.
-/

open scoped Pointwise

namespace Tiling.RationalPolygonal

/-- The computable closed integer interval used by the executable grid constructor. -/
def integerIntervalExec (lo hi : ℤ) : Finset ℤ :=
  (Finset.range (hi - lo + 1).toNat).image fun k : ℕ ↦ lo + (k : ℤ)

/-- A computable closed integer-coordinate rectangle. -/
def gridBoxExec (x₀ x₁ y₀ y₁ : ℤ) : Finset IntegerPlane :=
  (integerIntervalExec x₀ x₁ ×ˢ integerIntervalExec y₀ y₁).image
    (fun p ↦ latticePoint p.1 p.2)

/-- The executable eight-point ring around a nonzero color center. -/
def markerRingExec {M : ℕ} (i : Fin M) : Finset IntegerPlane :=
  (gridBoxExec (3 * (i : ℤ) - 1) (3 * (i : ℤ) + 1) 2 4).erase
    (markerCenter i)

/-- The executable unmodified marker square. -/
def markerSquareExec (M : ℕ) : Finset IntegerPlane :=
  gridBoxExec 0 (markerSide M - 1) 0 (markerSide M - 1)

/-- The executable union of all nonzero-color rings. -/
def nonzeroMarkerRingsExec (M : ℕ) : Finset IntegerPlane :=
  Finset.univ.biUnion fun i : Fin M ↦
    if i.val = 0 then ∅ else markerRingExec i

/-- The executable distinguished color-zero marker. -/
def markerZeroExec (M : ℕ) : Finset IntegerPlane :=
  ((insert (markerNorth M)
    (insert (markerEast M) (markerSquareExec M \ nonzeroMarkerRingsExec M))).erase
      markerWestHole).erase markerSouthHole

/-- The executable marker block assigned to one color. -/
def markerBlockExec {M : ℕ} (i : Fin M) : Finset IntegerPlane :=
  if i.val = 0 then markerZeroExec M else markerRingExec i

/-- The executable marker scale. -/
def markerScaleExec (M : ℕ) (x : IntegerPlane) : IntegerPlane :=
  (markerSide M : ℤ) • x

/-- Replace every point of every array-indexed color tile by its executable marker block. -/
def planarRasterTileArrayExec
    (tiles : Array (Finset IntegerPlane)) : Finset IntegerPlane :=
  Finset.univ.biUnion fun i : Fin tiles.size ↦
    (tiles[i]).biUnion fun f ↦
      (markerBlockExec i).image fun s ↦ markerScaleExec tiles.size f + s

/-- An array-indexed family with at least one color and a nonempty distinguished first tile. -/
structure NonemptyPlanarRasterFamily where
  /-- The finite array of color tiles. -/
  tiles : Array (Finset IntegerPlane)
  /-- The array contains a distinguished color zero. -/
  size_pos : 0 < tiles.size
  /-- The color-zero tile is nonempty. -/
  first_nonempty : (tiles[0]'size_pos).Nonempty

/-- The production executable API for a finite family with a nonempty first tile. -/
def planarRasterTileExec
    (input : NonemptyPlanarRasterFamily) : Finset IntegerPlane :=
  planarRasterTileArrayExec input.tiles

/-- Membership in the executable interval is the usual pair of closed endpoint inequalities. -/
@[simp]
theorem mem_integerIntervalExec_iff {lo hi z : ℤ} :
    z ∈ integerIntervalExec lo hi ↔ lo ≤ z ∧ z ≤ hi := by
  rw [integerIntervalExec, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk
    have hk' : (k : ℤ) < ((hi - lo + 1).toNat : ℤ) := by
      exact_mod_cast hk
    rw [Int.ofNat_toNat] at hk'
    constructor
    · exact Int.le_add_of_nonneg_right (Int.natCast_nonneg k)
    · omega
  · rintro ⟨hlo, hhi⟩
    have hdiff : 0 ≤ z - lo := by omega
    have hspan : 0 < hi - lo + 1 := by omega
    refine ⟨(z - lo).toNat, Finset.mem_range.mpr ?_, ?_⟩
    · exact (Int.toNat_lt_toNat hspan).mpr (by omega)
    · rw [Int.toNat_of_nonneg hdiff]
      omega

/-- The executable integer interval is extensionally equal to the semantic interval. -/
theorem integerIntervalExec_eq (lo hi : ℤ) :
    integerIntervalExec lo hi = Finset.Icc lo hi := by
  ext z
  simp only [mem_integerIntervalExec_iff, Finset.mem_Icc]

/-- The executable grid box is extensionally equal to the semantic grid box. -/
theorem gridBoxExec_eq (x₀ x₁ y₀ y₁ : ℤ) :
    gridBoxExec x₀ x₁ y₀ y₁ = gridBox x₀ x₁ y₀ y₁ := by
  rw [gridBoxExec, integerIntervalExec_eq, integerIntervalExec_eq, gridBox]

/-- The executable marker ring is extensionally equal to the semantic marker ring. -/
theorem markerRingExec_eq {M : ℕ} (i : Fin M) :
    markerRingExec i = markerRing i := by
  simp only [markerRingExec, markerRing, gridBoxExec_eq]

/-- The executable marker square is extensionally equal to the semantic marker square. -/
theorem markerSquareExec_eq (M : ℕ) :
    markerSquareExec M = markerSquare M := by
  simp only [markerSquareExec, markerSquare, gridBoxExec_eq]

/-- The executable union of nonzero rings equals its semantic counterpart. -/
theorem nonzeroMarkerRingsExec_eq (M : ℕ) :
    nonzeroMarkerRingsExec M = nonzeroMarkerRings M := by
  simp only [nonzeroMarkerRingsExec, nonzeroMarkerRings, markerRingExec_eq]

/-- The executable color-zero marker is extensionally equal to the semantic marker. -/
theorem markerZeroExec_eq (M : ℕ) :
    markerZeroExec M = markerZero M := by
  simp only [markerZeroExec, markerZero, markerSquareExec_eq, nonzeroMarkerRingsExec_eq]

/-- Every executable marker block is extensionally equal to its semantic counterpart. -/
theorem markerBlockExec_eq {M : ℕ} (i : Fin M) :
    markerBlockExec i = markerBlock i := by
  simp only [markerBlockExec, markerBlock, markerZeroExec_eq, markerRingExec_eq]

/-- Executable marker scaling is definitionally equal to semantic marker scaling. -/
theorem markerScaleExec_eq (M : ℕ) (x : IntegerPlane) :
    markerScaleExec M x = markerScale M x :=
  rfl

/-- Exact extensional bridge from the executable array API to the semantic marker tile. -/
theorem planarRasterTileArrayExec_eq_planarRasterTile
    (tiles : Array (Finset IntegerPlane)) :
    planarRasterTileArrayExec tiles = planarRasterTile (fun i : Fin tiles.size ↦ tiles[i]) := by
  simp only [planarRasterTileArrayExec, planarRasterTile, markerBlockExec_eq,
    markerScaleExec_eq]

/-- Exact bridge for the production input wrapper. -/
theorem planarRasterTileExec_eq_planarRasterTile
    (input : NonemptyPlanarRasterFamily) :
    planarRasterTileExec input =
      planarRasterTile (fun i : Fin input.tiles.size ↦ input.tiles[i]) := by
  simp only [planarRasterTileExec, planarRasterTileArrayExec_eq_planarRasterTile]

/-- A valid executable input produces a nonempty marker tile. -/
theorem planarRasterTileExec_nonempty (input : NonemptyPlanarRasterFamily) :
    (planarRasterTileExec input).Nonempty := by
  rw [planarRasterTileExec_eq_planarRasterTile]
  let zero : Fin input.tiles.size := ⟨0, input.size_pos⟩
  obtain ⟨f, hf⟩ := input.first_nonempty
  obtain ⟨s, hs⟩ := markerBlock_nonempty input.size_pos zero
  refine ⟨markerScale input.tiles.size f + s, ?_⟩
  exact mem_planarRasterTile_iff.mpr ⟨zero, f, hf, s, hs, rfl⟩

end Tiling.RationalPolygonal
