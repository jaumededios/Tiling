import Tiling.RationalPolygonal.RasterMarker

/-!
# Rigidity of planar raster markers

This file proves the local finite geometry behind the raster construction of
de Dios Pont--Grebík--Greenfeld--Madrid.  A marker block which fills either asymmetric hole of a
zero marker without overlapping it must itself be the zero block, positioned at the matching
protrusion.  The proof treats the nonzero eight-point rings and the large complementary zero
block separately and does not assume the false stronger claim that every local owner transfer is
already a coarse-lattice move.
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

end Tiling.RationalPolygonal
