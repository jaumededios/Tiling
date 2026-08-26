import Tiling.RationalPolygonal.RasterMarker

/-!
# Rigidity of planar raster markers

This file proves the local finite geometry behind the raster construction of
de Dios Pont--Grebík--Greenfeld--Madrid.  A marker block which fills either asymmetric hole of a
zero marker without overlapping it must itself be the zero block, positioned at the matching
protrusion.  Iterating those forced predecessors and aligning two southwest quadrants proves that
every translation of an exact raster tiling lies in one coarse-lattice coset, after which the
source color family decodes exactly.  The proof treats the nonzero eight-point rings and the large
complementary zero block separately and does not assume the false stronger claim that every local
owner transfer is already a coarse-lattice move.
-/

open Set
open TranslationalTilings
open scoped Pointwise

namespace Tiling.RationalPolygonal

private theorem markerZero_mem_of_square_not_rings {M : ℕ} {z : IntegerPlane}
    (hsquare : z ∈ markerSquare M) (hrings : z ∉ nonzeroMarkerRings M)
    (hwest : z ≠ markerWestHole) (hsouth : z ≠ markerSouthHole) :
    z ∈ markerZero M := by
  rw [markerZero, Finset.mem_erase, Finset.mem_erase]
  exact ⟨hsouth, hwest, Finset.mem_insert.mpr <|
    Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_sdiff.mpr ⟨hsquare, hrings⟩⟩

private theorem markerZero_mem_of_square_y_ge_five {M : ℕ} {z : IntegerPlane}
    (hsquare : z ∈ markerSquare M) (hy : 5 ≤ z 1) :
    z ∈ markerZero M := by
  apply markerZero_mem_of_square_not_rings hsquare
  · intro hz
    rw [nonzeroMarkerRings, Finset.mem_biUnion] at hz
    obtain ⟨i, -, hi⟩ := hz
    split at hi
    · simp at hi
    · have hb := markerRing_bounds hi
      omega
  · intro h
    have h1 := congrFun h 1
    simp only [markerWestHole, latticePoint_apply_one] at h1
    omega
  · intro h
    have h1 := congrFun h 1
    simp only [markerSouthHole, latticePoint_apply_one] at h1
    omega

private theorem markerZero_mem_of_square_y_le_one {M : ℕ} {z : IntegerPlane}
    (hsquare : z ∈ markerSquare M) (hy : z 1 ≤ 1)
    (hwest : z ≠ markerWestHole) (hsouth : z ≠ markerSouthHole) :
    z ∈ markerZero M := by
  apply markerZero_mem_of_square_not_rings hsquare
  · intro hz
    rw [nonzeroMarkerRings, Finset.mem_biUnion] at hz
    obtain ⟨i, -, hi⟩ := hz
    split at hi
    · simp at hi
    · have hb := markerRing_bounds hi
      omega
  · exact hwest
  · exact hsouth

private theorem markerZero_mem_of_small_target {M : ℕ} (hM : 0 < M)
    {x y : ℤ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy3 : y ≤ 3)
    (hwest : ¬ (x = 0 ∧ y = 1)) (hsouth : ¬ (x = 1 ∧ y = 0)) :
    latticePoint x y ∈ markerZero M := by
  apply markerZero_mem_of_square_not_rings
  · rw [markerSquare, mem_gridBox_iff]
    simp only [latticePoint_apply_zero, latticePoint_apply_one, markerSide]
    omega
  · intro hz
    rw [nonzeroMarkerRings, Finset.mem_biUnion] at hz
    obtain ⟨i, -, hi⟩ := hz
    split at hi
    · simp at hi
    · have hb := markerRing_bounds hi
      have hiLower : (1 : ℤ) ≤ i := by omega
      simp only [latticePoint_apply_zero] at hb
      omega
  · intro h
    apply hwest
    exact ⟨congrFun h 0, congrFun h 1⟩
  · intro h
    apply hsouth
    exact ⟨congrFun h 0, congrFun h 1⟩

private theorem markerRing_relative_mem {M : ℕ} (i : Fin M) {dx dy : ℤ}
    (hxlo : -1 ≤ dx) (hxhi : dx ≤ 1) (hylo : -1 ≤ dy) (hyhi : dy ≤ 1)
    (hne : dx ≠ 0 ∨ dy ≠ 0) :
    latticePoint (3 * (i : ℤ) + dx) (3 + dy) ∈ markerRing i := by
  rw [markerRing, Finset.mem_erase]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [markerCenter, latticePoint_apply_zero, latticePoint_apply_one] at h0 h1
    rcases hne with hne | hne
    · exact hne (by omega)
    · exact hne (by omega)
  · rw [mem_gridBox_iff]
    simp only [latticePoint_apply_zero, latticePoint_apply_one]
    omega

private theorem markerRing_west_collision {M : ℕ} (hM : 0 < M)
    {i : Fin M} (_hi : i.val ≠ 0) {s : IntegerPlane}
    (hs : s ∈ markerRing i) :
    ∃ q ∈ markerRing i, q + (markerWestHole - s) ∈ markerZero M := by
  let dx : ℤ := s 0 - 3 * (i : ℤ)
  let dy : ℤ := s 1 - 3
  have hb := markerRing_bounds hs
  have hdxlo : -1 ≤ dx := by dsimp only [dx]; omega
  have hdxhi : dx ≤ 1 := by dsimp only [dx]; omega
  have hdylo : -1 ≤ dy := by dsimp only [dy]; omega
  have hdyhi : dy ≤ 1 := by dsimp only [dy]; omega
  have hcenter : dx ≠ 0 ∨ dy ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    have h0 : s 0 = 3 * (i : ℤ) := by
      dsimp only [dx] at h
      omega
    have h1 : s 1 = 3 := by
      dsimp only [dy] at h
      omega
    have hsCenter : s = markerCenter i := by
      funext k
      fin_cases k
      · change s 0 = 3 * (i : ℤ)
        exact h0
      · change s 1 = 3
        exact h1
    have hne := (Finset.mem_erase.mp hs).1
    exact hne hsCenter
  have hsEq : s = latticePoint (3 * (i : ℤ) + dx) (3 + dy) := by
    funext k
    fin_cases k
    · change s 0 = 3 * (i : ℤ) + dx
      dsimp only [dx]
      ring
    · change s 1 = 3 + dy
      dsimp only [dy]
      ring
  have hex : ∃ qx qy : ℤ,
      -1 ≤ qx ∧ qx ≤ 1 ∧ -1 ≤ qy ∧ qy ≤ 1 ∧
      (qx ≠ 0 ∨ qy ≠ 0) ∧
      0 ≤ qx - dx ∧ qx - dx ≤ 1 ∧
      0 ≤ 1 + qy - dy ∧ 1 + qy - dy ≤ 3 ∧
      ¬ (qx - dx = 0 ∧ 1 + qy - dy = 1) ∧
      ¬ (qx - dx = 1 ∧ 1 + qy - dy = 0) := by
    by_cases hdx : dx = 0
    · have hdy : dy ≠ 0 := by
        rcases hcenter with h | h
        · exact (h hdx).elim
        · exact h
      have hdyCases : dy = -1 ∨ dy = 1 := by omega
      rcases hdyCases with hdyNeg | hdyPos
      · exact ⟨0, 1, by omega⟩
      · exact ⟨1, 1, by omega⟩
    · have hdyCases : dy = -1 ∨ dy = 0 ∨ dy = 1 := by omega
      rcases hdyCases with hdyNeg | hdyZero | hdyPos
      · exact ⟨dx, 0, by omega⟩
      · exact ⟨dx, -1, by omega⟩
      · exact ⟨dx, 0, by omega⟩
  obtain ⟨qx, qy, hqxlo, hqxhi, hqylo, hqyhi, hqne,
    htxlo, htxhi, htylo, htyhi, htwest, htsouth⟩ := hex
  let q := latticePoint (3 * (i : ℤ) + qx) (3 + qy)
  refine ⟨q, markerRing_relative_mem i hqxlo hqxhi hqylo hqyhi hqne, ?_⟩
  have hshift : q + (markerWestHole - s) =
      latticePoint (qx - dx) (1 + qy - dy) := by
    rw [hsEq]
    funext k
    fin_cases k
    · change 3 * (i : ℤ) + qx + (0 - (3 * (i : ℤ) + dx)) = qx - dx
      ring
    · change 3 + qy + (1 - (3 + dy)) = 1 + qy - dy
      ring
  rw [hshift]
  exact markerZero_mem_of_small_target hM htxlo htxhi htylo htyhi htwest htsouth

private theorem nonzeroMarkerRings_one_empty : nonzeroMarkerRings 1 = ∅ := by
  ext z
  constructor
  · rw [nonzeroMarkerRings, Finset.mem_biUnion]
    rintro ⟨i, -, hi⟩
    have hizero : i.val = 0 := by omega
    simp at hi
  · simp

private theorem markerZero_one_mem_of_box {x y : ℤ}
    (hx0 : 0 ≤ x) (hx6 : x ≤ 6) (hy0 : 0 ≤ y) (hy6 : y ≤ 6)
    (hwest : ¬ (x = 0 ∧ y = 1)) (hsouth : ¬ (x = 1 ∧ y = 0)) :
    latticePoint x y ∈ markerZero 1 := by
  apply markerZero_mem_of_square_not_rings
  · rw [markerSquare, mem_gridBox_iff]
    norm_num [markerSide, latticePoint]
    omega
  · rw [nonzeroMarkerRings_one_empty]
    simp
  · intro h
    apply hwest
    exact ⟨congrFun h 0, congrFun h 1⟩
  · intro h
    apply hsouth
    exact ⟨congrFun h 0, congrFun h 1⟩

private theorem markerZero_west_filler {M : ℕ} (hM : 0 < M) {s : IntegerPlane}
    (hs : s ∈ markerZero M)
    (havoid : ∀ q ∈ markerZero M,
      q + (markerWestHole - s) ∉ markerZero M) :
    s = markerEast M := by
  rw [markerZero, Finset.mem_erase, Finset.mem_erase] at hs
  simp only [Finset.mem_insert] at hs
  obtain ⟨hsSouth, hsWest, hsNorth | hsEast | hsBase⟩ := hs
  · subst s
    exfalso
    let q := latticePoint 1 (markerSide M - 1)
    have hqSquare : q ∈ markerSquare M := by
      rw [markerSquare, mem_gridBox_iff]
      simp only [q, latticePoint_apply_zero, latticePoint_apply_one, markerSide]
      omega
    have hq : q ∈ markerZero M := by
      apply markerZero_mem_of_square_y_ge_five hqSquare
      simp only [q, latticePoint_apply_one, markerSide]
      omega
    apply (havoid q hq)
    have hshift : q + (markerWestHole - markerNorth M) = latticePoint 0 0 := by
      funext k
      fin_cases k
      · simp [q, markerWestHole, markerNorth, latticePoint]
      · simp [q, markerWestHole, markerNorth, latticePoint, markerSide]
    rw [hshift]
    exact markerZero_mem_of_small_target hM (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  · exact hsEast
  · obtain ⟨hsSquare, -⟩ := Finset.mem_sdiff.mp hsBase
    let x : ℤ := s 0
    let y : ℤ := s 1
    have hsBounds := (mem_gridBox_iff.mp (show s ∈ markerSquare M from hsSquare))
    have hx0 : 0 ≤ x := by simpa only [x] using hsBounds.1
    have hxN : x ≤ (markerSide M : ℤ) - 1 := by
      simp only [markerSquare, mem_gridBox_iff] at hsSquare
      dsimp only [x]
      have := hsSquare.2.1
      simp only [markerSide] at this ⊢
      omega
    have hy0 : 0 ≤ y := by simpa only [y] using hsBounds.2.2.1
    have hyN : y ≤ (markerSide M : ℤ) - 1 := by
      simp only [markerSquare, mem_gridBox_iff] at hsSquare
      dsimp only [y]
      have := hsSquare.2.2.2
      simp only [markerSide] at this ⊢
      omega
    simp only [markerSide, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hxN hyN
    have hsEq : s = latticePoint x y := by
      funext k
      fin_cases k <;> rfl
    have hwest : ¬ (x = 0 ∧ y = 1) := by
      intro h
      apply hsWest
      rw [hsEq]
      funext k
      fin_cases k <;> simp [markerWestHole, latticePoint, h]
    have hsouth : ¬ (x = 1 ∧ y = 0) := by
      intro h
      apply hsSouth
      rw [hsEq]
      funext k
      fin_cases k <;> simp [markerSouthHole, latticePoint, h]
    rw [hsEq] at havoid
    by_cases hMone : M = 1
    · subst M
      have hx6 : x ≤ 6 := by norm_num [markerSide] at hxN ⊢; omega
      have hy6 : y ≤ 6 := by norm_num [markerSide] at hyN ⊢; omega
      by_cases hyZero : y = 0
      · let q := latticePoint x 5
        have hq : q ∈ markerZero 1 :=
          markerZero_one_mem_of_box hx0 hx6 (by omega) (by omega)
            (by omega) (by omega)
        exfalso
        apply (havoid q hq)
        have hshift : q + (markerWestHole - latticePoint x y) = latticePoint 0 6 := by
          funext k
          fin_cases k <;> simp [q, markerWestHole, latticePoint, hyZero]
        rw [hshift]
        exact markerZero_one_mem_of_box (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)
      · by_cases hspecialWest : x = 0 ∧ y = 2
        · let q := latticePoint 0 3
          have hq : q ∈ markerZero 1 :=
            markerZero_one_mem_of_box (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega)
          exfalso
          apply (havoid q hq)
          have hshift : q + (markerWestHole - latticePoint x y) = latticePoint 0 2 := by
            funext k
            fin_cases k <;>
              simp [q, markerWestHole, latticePoint, hspecialWest.1, hspecialWest.2]
          rw [hshift]
          exact markerZero_one_mem_of_box (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega)
        · by_cases hspecialSouth : x = 1 ∧ y = 1
          · let q := latticePoint 1 2
            have hq : q ∈ markerZero 1 :=
              markerZero_one_mem_of_box (by omega) (by omega) (by omega) (by omega)
                (by omega) (by omega)
            exfalso
            apply (havoid q hq)
            have hshift : q + (markerWestHole - latticePoint x y) = latticePoint 0 2 := by
              funext k
              fin_cases k <;>
                simp [q, markerWestHole, latticePoint, hspecialSouth.1, hspecialSouth.2]
            rw [hshift]
            exact markerZero_one_mem_of_box (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega)
          · let q := latticePoint x (y - 1)
            have hq : q ∈ markerZero 1 :=
              markerZero_one_mem_of_box hx0 hx6 (by omega) (by omega)
                (by omega) (by omega)
            exfalso
            apply (havoid q hq)
            have hshift : q + (markerWestHole - latticePoint x y) = latticePoint 0 0 := by
              funext k
              fin_cases k <;> simp [q, markerWestHole, latticePoint]
            rw [hshift]
            exact markerZero_one_mem_of_box (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega)
    · have hMtwo : 2 ≤ M := by omega
      by_cases hyZero : y = 0
      · let q := latticePoint x 5
        have hqSquare : q ∈ markerSquare M := by
          rw [markerSquare, mem_gridBox_iff]
          simp only [q, latticePoint_apply_zero, latticePoint_apply_one, markerSide]
          omega
        have hq := markerZero_mem_of_square_y_ge_five hqSquare (by
          simp only [q, latticePoint_apply_one]; omega)
        exfalso
        apply (havoid q hq)
        have hshift : q + (markerWestHole - latticePoint x y) = latticePoint 0 6 := by
          funext k
          fin_cases k <;> simp [q, markerWestHole, latticePoint, hyZero]
        rw [hshift]
        apply markerZero_mem_of_square_y_ge_five
        · rw [markerSquare, mem_gridBox_iff]
          simp only [latticePoint_apply_zero, latticePoint_apply_one, markerSide]
          omega
        · norm_num [latticePoint]
      · by_cases hyLow : y ≤ (markerSide M : ℤ) - 5
        · let q := latticePoint x ((markerSide M : ℤ) - 1)
          have hqSquare : q ∈ markerSquare M := by
            rw [markerSquare, mem_gridBox_iff]
            simp only [q, latticePoint_apply_zero, latticePoint_apply_one, markerSide]
            omega
          have hq := markerZero_mem_of_square_y_ge_five hqSquare (by
            simp only [q, latticePoint_apply_one, markerSide]; omega)
          exfalso
          apply (havoid q hq)
          have hshift : q + (markerWestHole - latticePoint x y) =
            latticePoint 0 ((markerSide M : ℤ) - y) := by
            funext k
            fin_cases k <;> simp [q, markerWestHole, latticePoint]
          rw [hshift]
          apply markerZero_mem_of_square_y_ge_five
          · rw [markerSquare, mem_gridBox_iff]
            simp only [latticePoint_apply_zero, latticePoint_apply_one, markerSide]
            omega
          · simp only [latticePoint_apply_one]
            omega
        · let q := latticePoint x (y - 1)
          simp only [markerSide, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hyLow
          have hqSquare : q ∈ markerSquare M := by
            rw [markerSquare, mem_gridBox_iff]
            simp only [q, latticePoint_apply_zero, latticePoint_apply_one, markerSide]
            omega
          have hq := markerZero_mem_of_square_y_ge_five hqSquare (by
            simp only [q, latticePoint_apply_one]
            omega)
          exfalso
          apply (havoid q hq)
          have hshift : q + (markerWestHole - latticePoint x y) = latticePoint 0 0 := by
            funext k
            fin_cases k <;> simp [q, markerWestHole, latticePoint]
          rw [hshift]
          exact markerZero_mem_of_small_target hM (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)

/-- A marker block disjointly filling the west hole of a zero block is the zero block's east
protrusion. -/
theorem markerBlock_west_filler {M : ℕ} (hM : 0 < M)
    {i : Fin M} {s : IntegerPlane} (hs : s ∈ markerBlock i)
    (havoid : ∀ q ∈ markerBlock i,
      q + (markerWestHole - s) ∉ markerZero M) :
    i.val = 0 ∧ s = markerEast M := by
  by_cases hi : i.val = 0
  · refine ⟨hi, ?_⟩
    apply markerZero_west_filler hM
    · rwa [markerBlock, if_pos hi] at hs
    · intro q hq
      exact havoid q (by rwa [markerBlock, if_pos hi])
  · exfalso
    have hsRing : s ∈ markerRing i := by rwa [markerBlock_of_ne_zero hi] at hs
    obtain ⟨q, hq, htarget⟩ := markerRing_west_collision hM hi hsRing
    exact (havoid q (by rwa [markerBlock_of_ne_zero hi])) htarget

private theorem markerRing_south_collision {M : ℕ} (hM : 0 < M)
    {i : Fin M} (_hi : i.val ≠ 0) {s : IntegerPlane}
    (hs : s ∈ markerRing i) :
    ∃ q ∈ markerRing i, q + (markerSouthHole - s) ∈ markerZero M := by
  let dx : ℤ := s 0 - 3 * (i : ℤ)
  let dy : ℤ := s 1 - 3
  have hb := markerRing_bounds hs
  have hdxlo : -1 ≤ dx := by dsimp only [dx]; omega
  have hdxhi : dx ≤ 1 := by dsimp only [dx]; omega
  have hdylo : -1 ≤ dy := by dsimp only [dy]; omega
  have hdyhi : dy ≤ 1 := by dsimp only [dy]; omega
  have hcenter : dx ≠ 0 ∨ dy ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    have h0 : s 0 = 3 * (i : ℤ) := by dsimp only [dx] at h; omega
    have h1 : s 1 = 3 := by dsimp only [dy] at h; omega
    apply (Finset.mem_erase.mp hs).1
    funext k
    fin_cases k
    · change s 0 = 3 * (i : ℤ)
      exact h0
    · change s 1 = 3
      exact h1
  have hsEq : s = latticePoint (3 * (i : ℤ) + dx) (3 + dy) := by
    funext k
    fin_cases k
    · change s 0 = 3 * (i : ℤ) + dx
      dsimp only [dx]
      ring
    · change s 1 = 3 + dy
      dsimp only [dy]
      ring
  have hex : ∃ qx qy : ℤ,
      -1 ≤ qx ∧ qx ≤ 1 ∧ -1 ≤ qy ∧ qy ≤ 1 ∧
      (qx ≠ 0 ∨ qy ≠ 0) ∧
      0 ≤ 1 + qx - dx ∧ 1 + qx - dx ≤ 3 ∧
      0 ≤ qy - dy ∧ qy - dy ≤ 1 ∧
      ¬ (1 + qx - dx = 0 ∧ qy - dy = 1) ∧
      ¬ (1 + qx - dx = 1 ∧ qy - dy = 0) := by
    by_cases hdx : dx = 0
    · have hdy : dy ≠ 0 := by
        rcases hcenter with h | h
        · exact (h hdx).elim
        · exact h
      have hdyCases : dy = -1 ∨ dy = 1 := by omega
      rcases hdyCases with hdyNeg | hdyPos
      · exact ⟨-1, -1, by omega⟩
      · exact ⟨-1, 1, by omega⟩
    · have hdxCases : dx = -1 ∨ dx = 1 := by omega
      have hdyCases : dy = -1 ∨ dy = 0 ∨ dy = 1 := by omega
      rcases hdxCases with hdxNeg | hdxPos
      · rcases hdyCases with hdyNeg | hdyZero | hdyPos
        · exact ⟨-1, 0, by omega⟩
        · exact ⟨-1, 1, by omega⟩
        · exact ⟨0, 1, by omega⟩
      · rcases hdyCases with hdyNeg | hdyZero | hdyPos
        · exact ⟨0, -1, by omega⟩
        · exact ⟨1, 1, by omega⟩
        · exact ⟨0, 1, by omega⟩
  obtain ⟨qx, qy, hqxlo, hqxhi, hqylo, hqyhi, hqne,
    htxlo, htxhi, htylo, htyhi, htwest, htsouth⟩ := hex
  let q := latticePoint (3 * (i : ℤ) + qx) (3 + qy)
  refine ⟨q, markerRing_relative_mem i hqxlo hqxhi hqylo hqyhi hqne, ?_⟩
  have hshift : q + (markerSouthHole - s) =
      latticePoint (1 + qx - dx) (qy - dy) := by
    rw [hsEq]
    funext k
    fin_cases k
    · change 3 * (i : ℤ) + qx + (1 - (3 * (i : ℤ) + dx)) = 1 + qx - dx
      ring
    · change 3 + qy + (0 - (3 + dy)) = qy - dy
      ring
  rw [hshift]
  apply markerZero_mem_of_square_y_le_one
  · rw [markerSquare, mem_gridBox_iff]
    simp only [latticePoint_apply_zero, latticePoint_apply_one, markerSide]
    omega
  · simpa only [latticePoint_apply_one] using htyhi
  · intro h
    apply htwest
    exact ⟨congrFun h 0, congrFun h 1⟩
  · intro h
    apply htsouth
    exact ⟨congrFun h 0, congrFun h 1⟩

private theorem markerZero_south_filler {M : ℕ} (hM : 0 < M) {s : IntegerPlane}
    (hs : s ∈ markerZero M)
    (havoid : ∀ q ∈ markerZero M,
      q + (markerSouthHole - s) ∉ markerZero M) :
    s = markerNorth M := by
  rw [markerZero, Finset.mem_erase, Finset.mem_erase] at hs
  simp only [Finset.mem_insert] at hs
  obtain ⟨hsSouth, hsWest, hsNorth | hsEast | hsBase⟩ := hs
  · exact hsNorth
  · subst s
    exfalso
    let q := latticePoint ((markerSide M : ℤ) - 1) 6
    have hqSquare : q ∈ markerSquare M := by
      rw [markerSquare, mem_gridBox_iff]
      simp only [q, latticePoint_apply_zero, latticePoint_apply_one, markerSide]
      omega
    have hq := markerZero_mem_of_square_y_ge_five hqSquare (by
      simp only [q, latticePoint_apply_one]; omega)
    apply (havoid q hq)
    have hshift : q + (markerSouthHole - markerEast M) = latticePoint 0 5 := by
      funext k
      fin_cases k
      · simp [q, markerSouthHole, markerEast, latticePoint]
      · rfl
    rw [hshift]
    apply markerZero_mem_of_square_y_ge_five
    · rw [markerSquare, mem_gridBox_iff]
      simp only [latticePoint_apply_zero, latticePoint_apply_one, markerSide]
      omega
    · rfl
  · obtain ⟨hsSquare, -⟩ := Finset.mem_sdiff.mp hsBase
    let x : ℤ := s 0
    let y : ℤ := s 1
    have hsBounds := mem_gridBox_iff.mp (show s ∈ markerSquare M from hsSquare)
    have hx0 : 0 ≤ x := by simpa only [x] using hsBounds.1
    have hxN : x ≤ (markerSide M : ℤ) - 1 := by
      simp only [markerSquare, mem_gridBox_iff] at hsSquare
      dsimp only [x]
      have := hsSquare.2.1
      simp only [markerSide] at this ⊢
      omega
    have hy0 : 0 ≤ y := by simpa only [y] using hsBounds.2.2.1
    have hyN : y ≤ (markerSide M : ℤ) - 1 := by
      simp only [markerSquare, mem_gridBox_iff] at hsSquare
      dsimp only [y]
      have := hsSquare.2.2.2
      simp only [markerSide] at this ⊢
      omega
    simp only [markerSide, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hxN hyN
    have hsEq : s = latticePoint x y := by
      funext k
      fin_cases k <;> rfl
    have hwest : ¬ (x = 0 ∧ y = 1) := by
      intro h
      apply hsWest
      rw [hsEq]
      funext k
      fin_cases k <;> simp [markerWestHole, latticePoint, h]
    have hsouth : ¬ (x = 1 ∧ y = 0) := by
      intro h
      apply hsSouth
      rw [hsEq]
      funext k
      fin_cases k <;> simp [markerSouthHole, latticePoint, h]
    rw [hsEq] at havoid
    by_cases hyLow : y ≤ 1
    · let q := latticePoint x ((markerSide M : ℤ) - 1)
      have hqSquare : q ∈ markerSquare M := by
        rw [markerSquare, mem_gridBox_iff]
        simp only [q, latticePoint_apply_zero, latticePoint_apply_one, markerSide]
        omega
      have hq := markerZero_mem_of_square_y_ge_five hqSquare (by
        simp only [q, latticePoint_apply_one, markerSide]; omega)
      exfalso
      apply (havoid q hq)
      have hshift : q + (markerSouthHole - latticePoint x y) =
          latticePoint 1 ((markerSide M : ℤ) - 1 - y) := by
        funext k
        fin_cases k
        · simp [q, markerSouthHole, latticePoint]
        · simp [q, markerSouthHole, latticePoint]
          ring
      rw [hshift]
      apply markerZero_mem_of_square_y_ge_five
      · rw [markerSquare, mem_gridBox_iff]
        simp only [latticePoint_apply_zero, latticePoint_apply_one, markerSide]
        omega
      · simp only [latticePoint_apply_one, markerSide]
        omega
    · by_cases hyMid : y ≤ 4
      · by_cases hxZero : x = 0
        · let q := latticePoint x 5
          have hqSquare : q ∈ markerSquare M := by
            rw [markerSquare, mem_gridBox_iff]
            simp only [q, latticePoint_apply_zero, latticePoint_apply_one, markerSide]
            omega
          have hq := markerZero_mem_of_square_y_ge_five hqSquare (by
            simp only [q, latticePoint_apply_one]; omega)
          exfalso
          apply (havoid q hq)
          have hshift : q + (markerSouthHole - latticePoint x y) =
              latticePoint 1 (5 - y) := by
            funext k
            fin_cases k
            · simp [q, markerSouthHole, latticePoint, hxZero]
            · simp [q, markerSouthHole, latticePoint]
              ring
          rw [hshift]
          exact markerZero_mem_of_small_target hM (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)
        · by_cases hyFour : y = 4
          · let q := latticePoint x 5
            have hqSquare : q ∈ markerSquare M := by
              rw [markerSquare, mem_gridBox_iff]
              simp only [q, latticePoint_apply_zero, latticePoint_apply_one, markerSide]
              omega
            have hq := markerZero_mem_of_square_y_ge_five hqSquare (by
              simp only [q, latticePoint_apply_one]; omega)
            exfalso
            apply (havoid q hq)
            have hshift : q + (markerSouthHole - latticePoint x y) =
                latticePoint 1 1 := by
              funext k
              fin_cases k <;> simp [q, markerSouthHole, latticePoint, hyFour]
            rw [hshift]
            exact markerZero_mem_of_small_target hM (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega)
          · let q := latticePoint (x - 1) 5
            have hqSquare : q ∈ markerSquare M := by
              rw [markerSquare, mem_gridBox_iff]
              simp only [q, latticePoint_apply_zero, latticePoint_apply_one, markerSide]
              omega
            have hq := markerZero_mem_of_square_y_ge_five hqSquare (by
              simp only [q, latticePoint_apply_one]; omega)
            exfalso
            apply (havoid q hq)
            have hshift : q + (markerSouthHole - latticePoint x y) =
                latticePoint 0 (5 - y) := by
              funext k
              fin_cases k
              · simp [q, markerSouthHole, latticePoint]
              · simp [q, markerSouthHole, latticePoint]
                ring
            rw [hshift]
            exact markerZero_mem_of_small_target hM (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega)
      · by_cases hxZero : x = 0
        · let q := latticePoint 1 y
          have hqSquare : q ∈ markerSquare M := by
            rw [markerSquare, mem_gridBox_iff]
            simp only [q, latticePoint_apply_zero, latticePoint_apply_one, markerSide]
            omega
          have hq := markerZero_mem_of_square_y_ge_five hqSquare (by
            simp only [q, latticePoint_apply_one]; omega)
          exfalso
          apply (havoid q hq)
          have hshift : q + (markerSouthHole - latticePoint x y) = latticePoint 2 0 := by
            funext k
            fin_cases k <;> simp [q, markerSouthHole, latticePoint, hxZero]
          rw [hshift]
          apply markerZero_mem_of_square_y_le_one
          · rw [markerSquare, mem_gridBox_iff]
            simp only [latticePoint_apply_zero, latticePoint_apply_one, markerSide]
            omega
          · norm_num [latticePoint]
          · intro h
            have h0 := congrFun h 0
            norm_num [markerWestHole, latticePoint] at h0
          · intro h
            have h0 := congrFun h 0
            norm_num [markerSouthHole, latticePoint] at h0
        · let q := latticePoint (x - 1) y
          have hqSquare : q ∈ markerSquare M := by
            rw [markerSquare, mem_gridBox_iff]
            simp only [q, latticePoint_apply_zero, latticePoint_apply_one, markerSide]
            omega
          have hq := markerZero_mem_of_square_y_ge_five hqSquare (by
            simp only [q, latticePoint_apply_one]; omega)
          exfalso
          apply (havoid q hq)
          have hshift : q + (markerSouthHole - latticePoint x y) = latticePoint 0 0 := by
            funext k
            fin_cases k <;> simp [q, markerSouthHole, latticePoint]
          rw [hshift]
          exact markerZero_mem_of_small_target hM (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)

/-- A marker block disjointly filling the south hole of a zero block is the zero block's north
protrusion. -/
theorem markerBlock_south_filler {M : ℕ} (hM : 0 < M)
    {i : Fin M} {s : IntegerPlane} (hs : s ∈ markerBlock i)
    (havoid : ∀ q ∈ markerBlock i,
      q + (markerSouthHole - s) ∉ markerZero M) :
    i.val = 0 ∧ s = markerNorth M := by
  by_cases hi : i.val = 0
  · refine ⟨hi, ?_⟩
    apply markerZero_south_filler hM
    · rwa [markerBlock, if_pos hi] at hs
    · intro q hq
      exact havoid q (by rwa [markerBlock, if_pos hi])
  · exfalso
    have hsRing : s ∈ markerRing i := by rwa [markerBlock_of_ne_zero hi] at hs
    obtain ⟨q, hq, htarget⟩ := markerRing_south_collision hM hi hsRing
    exact (havoid q (by rwa [markerBlock_of_ne_zero hi])) htarget

private theorem markerBlock_subset_modifiedMarkerSquare {M : ℕ} (hM : 0 < M)
    (i : Fin M) : markerBlock i ⊆ modifiedMarkerSquare M := by
  intro s hs
  rw [← markerUnion_eq_modifiedMarkerSquare hM, markerUnion,
    Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, hs⟩

private theorem markerEast_mem_markerZero (M : ℕ) :
    markerEast M ∈ markerZero M := by
  rw [markerZero, Finset.mem_erase, Finset.mem_erase]
  refine ⟨?_, ?_, Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert_self ..⟩
  · intro h
    have h0 := congrFun h 0
    simp only [markerEast, markerSouthHole, markerSide,
      latticePoint_apply_zero] at h0
    omega
  · intro h
    have h0 := congrFun h 0
    simp only [markerEast, markerWestHole, markerSide,
      latticePoint_apply_zero] at h0
    omega

private theorem markerNorth_mem_markerZero (M : ℕ) :
    markerNorth M ∈ markerZero M := by
  rw [markerZero, Finset.mem_erase, Finset.mem_erase]
  refine ⟨?_, ?_, Finset.mem_insert_self ..⟩
  · intro h
    have h1 := congrFun h 1
    simp only [markerNorth, markerSouthHole, markerSide,
      latticePoint_apply_one] at h1
    omega
  · intro h
    have h1 := congrFun h 1
    simp only [markerNorth, markerWestHole, markerSide,
      latticePoint_apply_one] at h1
    omega

private theorem markerScale_mem_markerLattice (M : ℕ) (g : IntegerPlane) :
    markerScale M g ∈ markerLattice M := by
  rw [mem_markerLattice_iff]
  exact ⟨g, rfl⟩

private theorem markerWest_decomposition (M : ℕ) (g : IntegerPlane) :
    markerScale M (g - horizontalUnit) + markerEast M =
      markerScale M g + markerWestHole := by
  rw [markerScale_sub]
  funext k
  fin_cases k
  · change markerScale M g 0 - markerScale M horizontalUnit 0 +
      markerEast M 0 = markerScale M g 0 + markerWestHole 0
    simp only [markerScale, markerSide, horizontalUnit, markerEast,
      markerWestHole, Pi.smul_apply, smul_eq_mul, latticePoint_apply_zero]
    ring
  · change markerScale M g 1 - markerScale M horizontalUnit 1 +
      markerEast M 1 = markerScale M g 1 + markerWestHole 1
    simp only [markerScale, horizontalUnit, markerEast, markerWestHole,
      Pi.smul_apply, smul_eq_mul, latticePoint_apply_one]
    ring

private theorem markerSouth_decomposition (M : ℕ) (g : IntegerPlane) :
    markerScale M (g - verticalUnit) + markerNorth M =
      markerScale M g + markerSouthHole := by
  rw [markerScale_sub]
  funext k
  fin_cases k
  · change markerScale M g 0 - markerScale M verticalUnit 0 +
      markerNorth M 0 = markerScale M g 0 + markerSouthHole 0
    simp only [markerScale, verticalUnit, markerNorth, markerSouthHole,
      Pi.smul_apply, smul_eq_mul, latticePoint_apply_zero]
    ring
  · change markerScale M g 1 - markerScale M verticalUnit 1 +
      markerNorth M 1 = markerScale M g 1 + markerSouthHole 1
    simp only [markerScale, markerSide, verticalUnit, markerNorth,
      markerSouthHole, Pi.smul_apply, smul_eq_mul, latticePoint_apply_one]
    ring

private def zeroMarkerPlacements {M : ℕ} (hM : 0 < M)
    (tile : Fin M → Finset IntegerPlane) (U : Set IntegerPlane) :
    Set IntegerPlane :=
  {v | ∃ g ∈ tile ⟨0, hM⟩, ∃ t ∈ U, markerScale M g + t = v}

private theorem mem_zeroMarkerPlacements_iff {M : ℕ} {hM : 0 < M}
    {tile : Fin M → Finset IntegerPlane} {U : Set IntegerPlane} {v : IntegerPlane} :
    v ∈ zeroMarkerPlacements hM tile U ↔
      ∃ g ∈ tile ⟨0, hM⟩, ∃ t ∈ U, markerScale M g + t = v :=
  Iff.rfl

private theorem zeroMarkerPlacements_west_predecessor {M : ℕ} (hM : 0 < M)
    (tile : Fin M → Finset IntegerPlane) {U : Set IntegerPlane}
    (hU : TilesUniverse (planarRasterTile tile) U)
    {v : IntegerPlane} (hv : v ∈ zeroMarkerPlacements hM tile U) :
    v - markerScale M horizontalUnit ∈ zeroMarkerPlacements hM tile U := by
  obtain ⟨g, hg, t, ht, hgt⟩ := mem_zeroMarkerPlacements_iff.mp hv
  have hzero : (⟨0, hM⟩ : Fin M).val = 0 := rfl
  let x := markerWestHole + v
  obtain ⟨r, hr, -⟩ := existsUnique_tile_representation hU x
  obtain ⟨i, f, hf, s, hs, hrEq⟩ := mem_planarRasterTile_iff.mp hr.1
  let u := x - r
  have hu : u ∈ U := by
    change x - r ∈ U
    exact hr.2
  have hxu : r + u = x := by
    dsimp only [u]
    abel
  have hworld : markerScale M f + s + u =
      markerScale M g + markerWestHole + t := by
    rw [hrEq]
    calc
      r + u = x := hxu
      _ = markerWestHole + v := rfl
      _ = markerWestHole + (markerScale M g + t) := by rw [← hgt]
      _ = markerScale M g + markerWestHole + t := by abel
  have hiS : i.val = 0 ∧ s = markerEast M := by
    by_cases hut : u = t
    · have hsModified := markerBlock_subset_modifiedMarkerSquare hM i hs
      have hEastBlock : markerEast M ∈ markerBlock (⟨0, hM⟩ : Fin M) := by
        rw [markerBlock, if_pos hzero]
        exact markerEast_mem_markerZero M
      have hEastModified := markerBlock_subset_modifiedMarkerSquare hM ⟨0, hM⟩
        hEastBlock
      have heq : s + markerScale M f =
          markerEast M + markerScale M (g - horizontalUnit) := by
        rw [hut] at hworld
        have hbase : markerScale M f + s = markerScale M g + markerWestHole := by
          apply add_right_cancel (b := t)
          simpa only [add_assoc] using hworld
        calc
          s + markerScale M f = markerScale M f + s := add_comm _ _
          _ = markerScale M g + markerWestHole := hbase
          _ = markerScale M (g - horizontalUnit) + markerEast M :=
            (markerWest_decomposition M g).symm
          _ = markerEast M + markerScale M (g - horizontalUnit) := add_comm _ _
      have hscale : markerScale M f = markerScale M (g - horizontalUnit) :=
        translation_eq_of_eq_representations
          (modifiedMarkerSquare_tiles_markerLattice M)
          hsModified (markerScale_mem_markerLattice M f)
          hEastModified (markerScale_mem_markerLattice M (g - horizontalUnit)) heq
      have hsEast : s = markerEast M := by
        rw [hscale] at heq
        exact add_right_cancel heq
      refine ⟨?_, hsEast⟩
      by_contra hi
      have hine : i ≠ (⟨0, hM⟩ : Fin M) := by
        intro hieq
        apply hi
        have hval := congrArg Fin.val hieq
        exact hval
      have hdisjoint := Finset.disjoint_left.mp (markerBlock_disjoint hine)
      exact hdisjoint hs (hsEast ▸ hEastBlock)
    · apply markerBlock_west_filler hM hs
      intro q hq htarget
      apply hut
      let a := markerScale M f + q
      let b := markerScale M g + (q + (markerWestHole - s))
      have ha : a ∈ planarRasterTile tile := by
        exact mem_planarRasterTile_iff.mpr ⟨i, f, hf, q, hq, rfl⟩
      have hb : b ∈ planarRasterTile tile := by
        exact mem_planarRasterTile_iff.mpr
          ⟨⟨0, hM⟩, g, hg, q + (markerWestHole - s),
            by rwa [markerBlock, if_pos hzero], rfl⟩
      apply translation_eq_of_eq_representations hU ha hu hb ht
      dsimp only [a, b]
      calc
        markerScale M f + q + u =
            (markerScale M f + s + u) + (q - s) := by abel
        _ = (markerScale M g + markerWestHole + t) + (q - s) := by rw [hworld]
        _ = markerScale M g + (q + (markerWestHole - s)) + t := by abel
  obtain ⟨hi, hsEast⟩ := hiS
  have hieq : i = ⟨0, hM⟩ := Fin.ext hi
  subst i
  refine mem_zeroMarkerPlacements_iff.mpr ⟨f, hf, u, hu, ?_⟩
  calc
    markerScale M f + u = x - s := by
      dsimp only [u]
      rw [← hrEq]
      abel
    _ = markerWestHole + v - markerEast M := by rw [hsEast]
    _ = v - markerScale M horizontalUnit := by
      funext k
      fin_cases k
      · change 0 + v 0 - (markerSide M : ℤ) =
          v 0 - (markerSide M : ℤ) * 1
        ring
      · change 1 + v 1 - 1 = v 1 - (markerSide M : ℤ) * 0
        ring

private theorem zeroMarkerPlacements_south_predecessor {M : ℕ} (hM : 0 < M)
    (tile : Fin M → Finset IntegerPlane) {U : Set IntegerPlane}
    (hU : TilesUniverse (planarRasterTile tile) U)
    {v : IntegerPlane} (hv : v ∈ zeroMarkerPlacements hM tile U) :
    v - markerScale M verticalUnit ∈ zeroMarkerPlacements hM tile U := by
  obtain ⟨g, hg, t, ht, hgt⟩ := mem_zeroMarkerPlacements_iff.mp hv
  have hzero : (⟨0, hM⟩ : Fin M).val = 0 := rfl
  let x := markerSouthHole + v
  obtain ⟨r, hr, -⟩ := existsUnique_tile_representation hU x
  obtain ⟨i, f, hf, s, hs, hrEq⟩ := mem_planarRasterTile_iff.mp hr.1
  let u := x - r
  have hu : u ∈ U := by
    change x - r ∈ U
    exact hr.2
  have hxu : r + u = x := by
    dsimp only [u]
    abel
  have hworld : markerScale M f + s + u =
      markerScale M g + markerSouthHole + t := by
    rw [hrEq]
    calc
      r + u = x := hxu
      _ = markerSouthHole + v := rfl
      _ = markerSouthHole + (markerScale M g + t) := by rw [← hgt]
      _ = markerScale M g + markerSouthHole + t := by abel
  have hiS : i.val = 0 ∧ s = markerNorth M := by
    by_cases hut : u = t
    · have hsModified := markerBlock_subset_modifiedMarkerSquare hM i hs
      have hNorthBlock : markerNorth M ∈ markerBlock (⟨0, hM⟩ : Fin M) := by
        rw [markerBlock, if_pos hzero]
        exact markerNorth_mem_markerZero M
      have hNorthModified := markerBlock_subset_modifiedMarkerSquare hM ⟨0, hM⟩
        hNorthBlock
      have heq : s + markerScale M f =
          markerNorth M + markerScale M (g - verticalUnit) := by
        rw [hut] at hworld
        have hbase : markerScale M f + s = markerScale M g + markerSouthHole := by
          apply add_right_cancel (b := t)
          simpa only [add_assoc] using hworld
        calc
          s + markerScale M f = markerScale M f + s := add_comm _ _
          _ = markerScale M g + markerSouthHole := hbase
          _ = markerScale M (g - verticalUnit) + markerNorth M :=
            (markerSouth_decomposition M g).symm
          _ = markerNorth M + markerScale M (g - verticalUnit) := add_comm _ _
      have hscale : markerScale M f = markerScale M (g - verticalUnit) :=
        translation_eq_of_eq_representations
          (modifiedMarkerSquare_tiles_markerLattice M)
          hsModified (markerScale_mem_markerLattice M f)
          hNorthModified (markerScale_mem_markerLattice M (g - verticalUnit)) heq
      have hsNorth : s = markerNorth M := by
        rw [hscale] at heq
        exact add_right_cancel heq
      refine ⟨?_, hsNorth⟩
      by_contra hi
      have hine : i ≠ (⟨0, hM⟩ : Fin M) := by
        intro hieq
        apply hi
        have hval := congrArg Fin.val hieq
        exact hval
      have hdisjoint := Finset.disjoint_left.mp (markerBlock_disjoint hine)
      exact hdisjoint hs (hsNorth ▸ hNorthBlock)
    · apply markerBlock_south_filler hM hs
      intro q hq htarget
      apply hut
      let a := markerScale M f + q
      let b := markerScale M g + (q + (markerSouthHole - s))
      have ha : a ∈ planarRasterTile tile := by
        exact mem_planarRasterTile_iff.mpr ⟨i, f, hf, q, hq, rfl⟩
      have hb : b ∈ planarRasterTile tile := by
        exact mem_planarRasterTile_iff.mpr
          ⟨⟨0, hM⟩, g, hg, q + (markerSouthHole - s),
            by rwa [markerBlock, if_pos hzero], rfl⟩
      apply translation_eq_of_eq_representations hU ha hu hb ht
      dsimp only [a, b]
      calc
        markerScale M f + q + u =
            (markerScale M f + s + u) + (q - s) := by abel
        _ = (markerScale M g + markerSouthHole + t) + (q - s) := by rw [hworld]
        _ = markerScale M g + (q + (markerSouthHole - s)) + t := by abel
  obtain ⟨hi, hsNorth⟩ := hiS
  have hieq : i = ⟨0, hM⟩ := Fin.ext hi
  subst i
  refine mem_zeroMarkerPlacements_iff.mpr ⟨f, hf, u, hu, ?_⟩
  calc
    markerScale M f + u = x - s := by
      dsimp only [u]
      rw [← hrEq]
      abel
    _ = markerSouthHole + v - markerNorth M := by rw [hsNorth]
    _ = v - markerScale M verticalUnit := by
      funext k
      fin_cases k
      · change 1 + v 0 - 1 = v 0 - (markerSide M : ℤ) * 0
        ring
      · change 0 + v 1 - (markerSide M : ℤ) =
          v 1 - (markerSide M : ℤ) * 1
        ring

private theorem zeroMarkerPlacements_sub_nat_horizontal {M : ℕ} (hM : 0 < M)
    (tile : Fin M → Finset IntegerPlane) {U : Set IntegerPlane}
    (hU : TilesUniverse (planarRasterTile tile) U)
    {v : IntegerPlane} (hv : v ∈ zeroMarkerPlacements hM tile U) (a : ℕ) :
    v - (a : ℤ) • markerScale M horizontalUnit ∈
      zeroMarkerPlacements hM tile U := by
  induction a with
  | zero => simpa
  | succ a ih =>
      have hp := zeroMarkerPlacements_west_predecessor hM tile hU ih
      convert hp using 1
      push_cast
      simp only [add_smul, one_smul]
      abel

private theorem zeroMarkerPlacements_sub_nat_pair {M : ℕ} (hM : 0 < M)
    (tile : Fin M → Finset IntegerPlane) {U : Set IntegerPlane}
    (hU : TilesUniverse (planarRasterTile tile) U)
    {v : IntegerPlane} (hv : v ∈ zeroMarkerPlacements hM tile U) (a b : ℕ) :
    v - (a : ℤ) • markerScale M horizontalUnit -
        (b : ℤ) • markerScale M verticalUnit ∈
      zeroMarkerPlacements hM tile U := by
  have hh := zeroMarkerPlacements_sub_nat_horizontal hM tile hU hv a
  induction b with
  | zero => simpa using hh
  | succ b ih =>
      have hp := zeroMarkerPlacements_south_predecessor hM tile hU ih
      convert hp using 1
      push_cast
      simp only [add_smul, one_smul]
      abel

private theorem exists_nat_shifts_controlled (N a b : ℤ) (hN : 7 ≤ N) :
    ∃ ka kb : ℕ,
      -2 ≤ (a - N * (ka : ℤ)) - (b - N * (kb : ℤ)) ∧
        (a - N * (ka : ℤ)) - (b - N * (kb : ℤ)) ≤ N - 3 := by
  let delta := a - b
  let q := delta / N
  let r := delta % N
  let c := if r ≤ N - 3 then q else q + 1
  let ka := c.toNat
  let kb := (-c).toNat
  have hNpos : 0 < N := by omega
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    exact Int.emod_nonneg _ (by omega)
  have hrN : r < N := by
    dsimp only [r]
    exact Int.emod_lt_of_pos _ hNpos
  have hdelta : r + N * q = delta := by
    dsimp only [r, q]
    exact Int.emod_add_mul_ediv delta N
  have hdiff : (ka : ℤ) - (kb : ℤ) = c := by
    exact Int.toNat_sub_toNat_neg c
  have hvalue : (a - N * (ka : ℤ)) - (b - N * (kb : ℤ)) = delta - N * c := by
    rw [← hdiff]
    dsimp only [delta]
    ring
  refine ⟨ka, kb, ?_⟩
  dsimp only [delta] at hdelta
  by_cases hr : r ≤ N - 3
  · have hc : c = q := by simp [c, hr]
    rw [hvalue, hc]
    constructor <;> omega
  · have hc : c = q + 1 := by simp [c, hr]
    rw [hvalue, hc]
    have hmul : N * (q + 1) = N * q + N := by ring
    rw [hmul]
    constructor <;> omega

private theorem markerZero_mem_of_safe_row {M : ℕ} {z : IntegerPlane}
    (hsquare : z ∈ markerSquare M) (hy : z 1 ≤ 1 ∨ 5 ≤ z 1)
    (hwest : z ≠ markerWestHole) (hsouth : z ≠ markerSouthHole) :
    z ∈ markerZero M := by
  rw [markerZero, Finset.mem_erase, Finset.mem_erase]
  refine ⟨hsouth, hwest, Finset.mem_insert.mpr <| Or.inr <|
    Finset.mem_insert.mpr <| Or.inr <| Finset.mem_sdiff.mpr ⟨hsquare, ?_⟩⟩
  intro hz
  rw [nonzeroMarkerRings, Finset.mem_biUnion] at hz
  obtain ⟨i, -, hi⟩ := hz
  split at hi
  · simp at hi
  · have hb := markerRing_bounds hi
    omega

private theorem markerZero_one_mem_of_box_global {x y : ℤ}
    (hx0 : 0 ≤ x) (hx6 : x ≤ 6) (hy0 : 0 ≤ y) (hy6 : y ≤ 6)
    (hwest : ¬ (x = 0 ∧ y = 1)) (hsouth : ¬ (x = 1 ∧ y = 0)) :
    latticePoint x y ∈ markerZero 1 := by
  rw [markerZero, Finset.mem_erase, Finset.mem_erase]
  refine ⟨?_, ?_, Finset.mem_insert.mpr <| Or.inr <|
    Finset.mem_insert.mpr <| Or.inr <| Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
  · intro h
    apply hsouth
    exact ⟨congrFun h 0, congrFun h 1⟩
  · intro h
    apply hwest
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rw [markerSquare, mem_gridBox_iff]
    norm_num [markerSide, latticePoint]
    omega
  · rw [nonzeroMarkerRings]
    intro hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨i, -, hi⟩ := hz
    have hizero : i.val = 0 := by omega
    simp at hi

private theorem markerZero_overlap_of_controlled {M : ℕ} (hM : 0 < M)
    {d : IntegerPlane}
    (hdxlo : -2 ≤ d 0) (hdxhi : d 0 ≤ (markerSide M : ℤ) - 3)
    (hdylo : -2 ≤ d 1) (hdyhi : d 1 ≤ (markerSide M : ℤ) - 3) :
    ∃ q ∈ markerZero M, q + d ∈ markerZero M := by
  have hside : (markerSide M : ℤ) = 3 * (M : ℤ) + 4 := by
    simp only [markerSide, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hx : ∃ qx : ℤ,
      2 ≤ qx ∧ qx ≤ (markerSide M : ℤ) - 1 ∧
      2 ≤ qx + d 0 ∧ qx + d 0 ≤ (markerSide M : ℤ) - 1 := by
    by_cases hdx : 0 ≤ d 0
    · exact ⟨2, by omega⟩
    · exact ⟨2 - d 0, by omega⟩
  obtain ⟨qx, hqx0, hqxN, hqdx0, hqdxN⟩ := hx
  by_cases hMone : M = 1
  · subst M
    have hy : ∃ qy : ℤ,
        2 ≤ qy ∧ qy ≤ 6 ∧ 2 ≤ qy + d 1 ∧ qy + d 1 ≤ 6 := by
      by_cases hdy : 0 ≤ d 1
      · exact ⟨2, by norm_num [markerSide] at hdyhi; omega⟩
      · exact ⟨2 - d 1, by omega⟩
    obtain ⟨qy, hqy0, hqy6, hqdy0, hqdy6⟩ := hy
    refine ⟨latticePoint qx qy, ?_, ?_⟩
    · exact markerZero_one_mem_of_box_global (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · have hdEq : d = latticePoint (d 0) (d 1) := by
        funext k
        fin_cases k <;> rfl
      rw [hdEq]
      have hadd : latticePoint qx qy + latticePoint (d 0) (d 1) =
          latticePoint (qx + d 0) (qy + d 1) := by
        funext k
        fin_cases k <;> rfl
      rw [hadd]
      exact markerZero_one_mem_of_box_global (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  · have hMtwo : 2 ≤ M := by omega
    have hy : ∃ qy : ℤ,
        0 ≤ qy ∧ qy ≤ (markerSide M : ℤ) - 1 ∧
        0 ≤ qy + d 1 ∧ qy + d 1 ≤ (markerSide M : ℤ) - 1 ∧
        (qy ≤ 1 ∨ 5 ≤ qy) ∧ (qy + d 1 ≤ 1 ∨ 5 ≤ qy + d 1) := by
      by_cases hdyNeg : d 1 < 0
      · by_cases hdyOne : d 1 = -1
        · exact ⟨1, by omega⟩
        · exact ⟨7, by omega⟩
      · by_cases hdyLow : d 1 ≤ 1
        · exact ⟨0, by omega⟩
        · by_cases hdyMid : d 1 ≤ 4
          · exact ⟨5, by omega⟩
          · exact ⟨0, by omega⟩
    obtain ⟨qy, hqy0, hqyN, hqdy0, hqdyN, hqySafe, hqdySafe⟩ := hy
    have hqSquare : latticePoint qx qy ∈ markerSquare M := by
      rw [markerSquare, mem_gridBox_iff]
      simp only [latticePoint_apply_zero, latticePoint_apply_one]
      omega
    have hq : latticePoint qx qy ∈ markerZero M := by
      apply markerZero_mem_of_safe_row hqSquare hqySafe
      · intro h
        have h0 := congrFun h 0
        simp only [markerWestHole, latticePoint_apply_zero] at h0
        omega
      · intro h
        have h0 := congrFun h 0
        simp only [markerSouthHole, latticePoint_apply_zero] at h0
        omega
    refine ⟨latticePoint qx qy, hq, ?_⟩
    have hdEq : d = latticePoint (d 0) (d 1) := by
      funext k
      fin_cases k <;> rfl
    rw [hdEq]
    have hadd : latticePoint qx qy + latticePoint (d 0) (d 1) =
        latticePoint (qx + d 0) (qy + d 1) := by
      funext k
      fin_cases k <;> rfl
    rw [hadd]
    apply markerZero_mem_of_safe_row
    · rw [markerSquare, mem_gridBox_iff]
      simp only [latticePoint_apply_zero, latticePoint_apply_one]
      omega
    · simpa only [latticePoint_apply_one] using hqdySafe
    · intro h
      have h0 := congrFun h 0
      simp only [markerWestHole, latticePoint_apply_zero] at h0
      omega
    · intro h
      have h0 := congrFun h 0
      simp only [markerSouthHole, latticePoint_apply_zero] at h0
      omega

/-- If the zero-color source tile is nonempty, every pair of translations in an exact raster
tiling differ by a coarse marker-lattice vector. -/
theorem planarRasterTile_translation_differences_mem_markerLattice
    {M : ℕ} (hM : 0 < M) (tile : Fin M → Finset IntegerPlane)
    (hzeroTile : (tile ⟨0, hM⟩).Nonempty)
    {U : Set IntegerPlane} (hU : TilesUniverse (planarRasterTile tile) U)
    {t u : IntegerPlane} (ht : t ∈ U) (hu : u ∈ U) :
    t - u ∈ markerLattice M := by
  obtain ⟨g, hg⟩ := hzeroTile
  let v₀ := markerScale M g + t
  let w₀ := markerScale M g + u
  have hv₀ : v₀ ∈ zeroMarkerPlacements hM tile U :=
    mem_zeroMarkerPlacements_iff.mpr ⟨g, hg, t, ht, rfl⟩
  have hw₀ : w₀ ∈ zeroMarkerPlacements hM tile U :=
    mem_zeroMarkerPlacements_iff.mpr ⟨g, hg, u, hu, rfl⟩
  have hside : 7 ≤ (markerSide M : ℤ) := by
    simp only [markerSide, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    omega
  obtain ⟨vx, wx, hxlo, hxhi⟩ :=
    exists_nat_shifts_controlled (markerSide M : ℤ) (v₀ 0) (w₀ 0) hside
  obtain ⟨vy, wy, hylo, hyhi⟩ :=
    exists_nat_shifts_controlled (markerSide M : ℤ) (v₀ 1) (w₀ 1) hside
  let v' := v₀ - (vx : ℤ) • markerScale M horizontalUnit -
    (vy : ℤ) • markerScale M verticalUnit
  let w' := w₀ - (wx : ℤ) • markerScale M horizontalUnit -
    (wy : ℤ) • markerScale M verticalUnit
  have hv' : v' ∈ zeroMarkerPlacements hM tile U :=
    zeroMarkerPlacements_sub_nat_pair hM tile hU hv₀ vx vy
  have hw' : w' ∈ zeroMarkerPlacements hM tile U :=
    zeroMarkerPlacements_sub_nat_pair hM tile hU hw₀ wx wy
  let d := v' - w'
  have hdxlo : -2 ≤ d 0 := by
    dsimp only [d, v', w']
    simp only [Pi.sub_apply, Pi.smul_apply, markerScale, smul_eq_mul,
      horizontalUnit, verticalUnit, latticePoint_apply_zero, mul_zero, mul_one, sub_zero]
    simpa only [mul_comm] using hxlo
  have hdxhi : d 0 ≤ (markerSide M : ℤ) - 3 := by
    dsimp only [d, v', w']
    simp only [Pi.sub_apply, Pi.smul_apply, markerScale, smul_eq_mul,
      horizontalUnit, verticalUnit, latticePoint_apply_zero, mul_zero, mul_one, sub_zero]
    simpa only [mul_comm] using hxhi
  have hdylo : -2 ≤ d 1 := by
    dsimp only [d, v', w']
    simp only [Pi.sub_apply, Pi.smul_apply, markerScale, smul_eq_mul,
      horizontalUnit, verticalUnit, latticePoint_apply_one, mul_zero, mul_one, sub_zero]
    simpa only [mul_comm] using hylo
  have hdyhi : d 1 ≤ (markerSide M : ℤ) - 3 := by
    dsimp only [d, v', w']
    simp only [Pi.sub_apply, Pi.smul_apply, markerScale, smul_eq_mul,
      horizontalUnit, verticalUnit, latticePoint_apply_one, mul_zero, mul_one, sub_zero]
    simpa only [mul_comm] using hyhi
  obtain ⟨q, hq, hqd⟩ :=
    markerZero_overlap_of_controlled hM hdxlo hdxhi hdylo hdyhi
  obtain ⟨gv, hgv, tv, htv, hgvEq⟩ := mem_zeroMarkerPlacements_iff.mp hv'
  obtain ⟨gw, hgw, tw, htw, hgwEq⟩ := mem_zeroMarkerPlacements_iff.mp hw'
  have hzero : (⟨0, hM⟩ : Fin M).val = 0 := rfl
  let a := markerScale M gv + q
  let b := markerScale M gw + (q + d)
  have ha : a ∈ planarRasterTile tile := by
    exact mem_planarRasterTile_iff.mpr
      ⟨⟨0, hM⟩, gv, hgv, q, by rwa [markerBlock, if_pos hzero], rfl⟩
  have hb : b ∈ planarRasterTile tile := by
    exact mem_planarRasterTile_iff.mpr
      ⟨⟨0, hM⟩, gw, hgw, q + d, by rwa [markerBlock, if_pos hzero], rfl⟩
  have hab : a + tv = b + tw := by
    dsimp only [a, b]
    calc
      markerScale M gv + q + tv = q + (markerScale M gv + tv) := by abel
      _ = q + v' := by rw [hgvEq]
      _ = (q + d) + w' := by dsimp only [d]; abel
      _ = markerScale M gw + (q + d) + tw := by rw [← hgwEq]; abel
  have htveq : tv = tw :=
    translation_eq_of_eq_representations hU ha htv hb htw hab
  have hdLattice : d ∈ markerLattice M := by
    rw [mem_markerLattice_iff]
    refine ⟨gv - gw, ?_⟩
    change markerScale M (gv - gw) = d
    rw [markerScale_sub]
    dsimp only [d]
    rw [← hgvEq, ← hgwEq, htveq]
    abel
  have hhorizontal : markerScale M horizontalUnit ∈ markerLattice M :=
    markerScale_mem_markerLattice M horizontalUnit
  have hvertical : markerScale M verticalUnit ∈ markerLattice M :=
    markerScale_mem_markerLattice M verticalUnit
  have hshift :
      (((vx : ℤ) - wx) • markerScale M horizontalUnit +
        ((vy : ℤ) - wy) • markerScale M verticalUnit) ∈ markerLattice M :=
    (markerLattice M).add_mem
      ((markerLattice M).zsmul_mem hhorizontal ((vx : ℤ) - wx))
      ((markerLattice M).zsmul_mem hvertical ((vy : ℤ) - wy))
  have hsum := (markerLattice M).add_mem hdLattice hshift
  convert hsum using 1
  dsimp only [d, v', w', v₀, w₀]
  simp only [sub_smul]
  abel

/-- Every exact tiling by a planar raster tile with a nonempty zero layer decodes to one common
translation set which tiles every source color. -/
theorem exists_family_tiling_of_planarRasterTile {M : ℕ} (hM : 0 < M)
    (tile : Fin M → Finset IntegerPlane) (hzeroTile : (tile ⟨0, hM⟩).Nonempty)
    (U : Set IntegerPlane) (hraster : TilesUniverse (planarRasterTile tile) U) :
    ∃ T : Set IntegerPlane, ∀ i, TilesUniverse (tile i) T := by
  obtain ⟨r, hr, -⟩ := existsUnique_tile_representation hraster 0
  let base := -r
  have hbase : base ∈ U := by
    simpa only [base, zero_sub] using hr.2
  apply exists_family_tiling_of_planarRasterTile_coset hM tile U hraster base
  intro u hu
  exact planarRasterTile_translation_differences_mem_markerLattice
    hM tile hzeroTile hraster hu hbase


end Tiling.RationalPolygonal
