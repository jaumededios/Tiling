import Tiling.RationalPolygonal.RasterMarker

/-!
# A rigid interlocking lattice frame

This module isolates a constant four-by-four frame whose two boundary holes and matching
protrusions force every exact translation tiling into one coset of `4ℤ²`.  It is the geometric
rigidity gadget used by the strip encoding of a finite family of planar lattice tiles.
-/

open Set
open TranslationalTilings
open scoped Pointwise

namespace Tiling.RationalPolygonal

/-- The four-by-four square with west/south holes moved to east/north protrusions. -/
noncomputable def rigidFrame : Finset IntegerPlane := modifiedMarkerSquare 0

private theorem mem_rigidFrame_iff {z : IntegerPlane} :
    z ∈ rigidFrame ↔
      z = latticePoint 1 4 ∨ z = latticePoint 4 1 ∨
        (0 ≤ z 0 ∧ z 0 ≤ 3 ∧ 0 ≤ z 1 ∧ z 1 ≤ 3 ∧
          z ≠ latticePoint 0 1 ∧ z ≠ latticePoint 1 0) := by
  rw [rigidFrame, modifiedMarkerSquare, Finset.mem_erase, Finset.mem_erase]
  simp only [markerNorth, markerEast, markerSide,
    Finset.mem_insert, markerSquare, mem_gridBox_iff]
  norm_num
  constructor
  · rintro ⟨hSouth, hWest, hNorth | hEast | hbox⟩
    · exact Or.inl hNorth
    · exact Or.inr (Or.inl hEast)
    · exact Or.inr (Or.inr ⟨hbox.1, hbox.2.1, hbox.2.2.1,
        hbox.2.2.2, hWest, hSouth⟩)
  · rintro (hNorth | hEast | hbox)
    · subst z
      constructor
      · intro h
        have h1 := congrFun h 1
        simp [markerSouthHole, latticePoint] at h1
      · constructor
        · intro h
          have h1 := congrFun h 1
          simp [markerWestHole, latticePoint] at h1
        · exact Or.inl rfl
    · subst z
      constructor
      · intro h
        have h0 := congrFun h 0
        simp [markerSouthHole, latticePoint] at h0
      · constructor
        · intro h
          have h0 := congrFun h 0
          simp [markerWestHole, latticePoint] at h0
        · exact Or.inr (Or.inl rfl)
    · exact ⟨hbox.2.2.2.2.2, hbox.2.2.2.2.1,
        Or.inr (Or.inr ⟨hbox.1, hbox.2.1,
          hbox.2.2.1, hbox.2.2.2.1⟩)⟩

private theorem rigidFrame_west_filler {s : IntegerPlane}
    (hs : s ∈ rigidFrame)
    (havoid : ∀ q ∈ rigidFrame, q + (markerWestHole - s) ∉ rigidFrame) :
    s = latticePoint 4 1 := by
  rw [mem_rigidFrame_iff] at hs
  rcases hs with hNorth | hEast | hs
  · subst s
    exfalso
    have hq : latticePoint 1 3 ∈ rigidFrame := by
      rw [mem_rigidFrame_iff]
      right; right
      simp [latticePoint]
    have hshift : latticePoint 1 3 +
        (markerWestHole - latticePoint 1 4) = latticePoint 0 0 := by
      ext i
      fin_cases i <;> rfl
    have htarget : latticePoint 0 0 ∈ rigidFrame := by
      rw [mem_rigidFrame_iff]
      right; right
      simp [latticePoint]
    exact (havoid _ hq) (hshift ▸ htarget)
  · exact hEast
  · obtain ⟨hs0lo, hs0hi, hs1lo, hs1hi, hsWest, hsSouth⟩ := hs
    let x : ℤ := s 0
    let y : ℤ := s 1
    have hsEq : s = latticePoint x y := by
      funext i
      fin_cases i <;> rfl
    rw [hsEq] at havoid hsWest hsSouth ⊢
    have hxlo : 0 ≤ x := by simpa [x] using hs0lo
    have hxhi : x ≤ 3 := by simpa [x] using hs0hi
    have hylo : 0 ≤ y := by simpa [y] using hs1lo
    have hyhi : y ≤ 3 := by simpa [y] using hs1hi
    interval_cases x <;> interval_cases y
    all_goals try { exfalso; apply hsWest; funext i; fin_cases i <;> simp_all [latticePoint] }
    all_goals subst s
    all_goals
      exfalso
      first
      | exact (havoid (latticePoint 0 2) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 0 2 + (markerWestHole - latticePoint 0 0) =
              latticePoint 0 3 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 0 3) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 0 3 + (markerWestHole - latticePoint 0 2) =
              latticePoint 0 2 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 0 2) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 0 2 + (markerWestHole - latticePoint 0 3) =
              latticePoint 0 0 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 1 2) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 1 2 + (markerWestHole - latticePoint 1 1) =
              latticePoint 0 2 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 1 1) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 1 1 + (markerWestHole - latticePoint 1 2) =
              latticePoint 0 0 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 1 2) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 1 2 + (markerWestHole - latticePoint 1 3) =
              latticePoint 0 0 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 2 1) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 2 1 + (markerWestHole - latticePoint 2 0) =
              latticePoint 0 2 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 2 0) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 2 0 + (markerWestHole - latticePoint 2 1) =
              latticePoint 0 0 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 2 1) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 2 1 + (markerWestHole - latticePoint 2 2) =
              latticePoint 0 0 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 2 2) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 2 2 + (markerWestHole - latticePoint 2 3) =
              latticePoint 0 0 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 3 1) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 3 1 + (markerWestHole - latticePoint 3 0) =
              latticePoint 0 2 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 3 0) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 3 0 + (markerWestHole - latticePoint 3 1) =
              latticePoint 0 0 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 3 1) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 3 1 + (markerWestHole - latticePoint 3 2) =
              latticePoint 0 0 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])
      | exact (havoid (latticePoint 3 2) (by
          rw [mem_rigidFrame_iff]; norm_num [latticePoint])) (by
            rw [show latticePoint 3 2 + (markerWestHole - latticePoint 3 3) =
              latticePoint 0 0 by ext i; fin_cases i <;> rfl]
            rw [mem_rigidFrame_iff]; norm_num [latticePoint])

/-- Exchange the two integer coordinates. -/
private def swapCoordinates (z : IntegerPlane) : IntegerPlane :=
  latticePoint (z 1) (z 0)

@[simp]
private theorem swapCoordinates_apply_zero (z : IntegerPlane) : swapCoordinates z 0 = z 1 := rfl

@[simp]
private theorem swapCoordinates_apply_one (z : IntegerPlane) : swapCoordinates z 1 = z 0 := rfl

@[simp]
private theorem swapCoordinates_swap (z : IntegerPlane) :
    swapCoordinates (swapCoordinates z) = z := by
  funext i
  fin_cases i <;> rfl

@[simp]
private theorem swapCoordinates_latticePoint (x y : ℤ) :
    swapCoordinates (latticePoint x y) = latticePoint y x := by
  rfl

@[simp]
private theorem swapCoordinates_add (x y : IntegerPlane) :
    swapCoordinates (x + y) = swapCoordinates x + swapCoordinates y := by
  funext i
  fin_cases i <;> rfl

@[simp]
private theorem swapCoordinates_sub (x y : IntegerPlane) :
    swapCoordinates (x - y) = swapCoordinates x - swapCoordinates y := by
  funext i
  fin_cases i <;> rfl

@[simp]
private theorem swapCoordinates_west : swapCoordinates markerWestHole = markerSouthHole := by
  rfl

@[simp]
private theorem swapCoordinates_south : swapCoordinates markerSouthHole = markerWestHole := by
  rfl

@[simp]
private theorem swapCoordinates_east :
    swapCoordinates (latticePoint 4 1) = latticePoint 1 4 := by
  rfl

@[simp]
private theorem swapCoordinates_mem_rigidFrame {z : IntegerPlane} :
    swapCoordinates z ∈ rigidFrame ↔ z ∈ rigidFrame := by
  have hforward : ∀ w : IntegerPlane,
      swapCoordinates w ∈ rigidFrame → w ∈ rigidFrame := by
    intro w hw
    rw [mem_rigidFrame_iff] at hw ⊢
    rcases hw with hNorth | hEast | hbox
    · right; left
      simpa only [swapCoordinates_latticePoint, swapCoordinates_swap] using
        congrArg swapCoordinates hNorth
    · left
      simpa only [swapCoordinates_latticePoint, swapCoordinates_swap] using
        congrArg swapCoordinates hEast
    · right; right
      refine ⟨hbox.2.2.1, hbox.2.2.2.1, hbox.1, hbox.2.1, ?_, ?_⟩
      · intro h
        subst w
        exact hbox.2.2.2.2.2 rfl
      · intro h
        subst w
        exact hbox.2.2.2.2.1 rfl
  constructor
  · exact hforward z
  · intro hz
    have := hforward (swapCoordinates z) (by simpa only [swapCoordinates_swap] using hz)
    simpa only [swapCoordinates_swap] using this

private theorem rigidFrame_south_filler {s : IntegerPlane}
    (hs : s ∈ rigidFrame)
    (havoid : ∀ q ∈ rigidFrame, q + (markerSouthHole - s) ∉ rigidFrame) :
    s = latticePoint 1 4 := by
  have hswap : swapCoordinates s = latticePoint 4 1 := by
    apply rigidFrame_west_filler (swapCoordinates_mem_rigidFrame.mpr hs)
    intro q hq htarget
    have hqswap : swapCoordinates q ∈ rigidFrame := swapCoordinates_mem_rigidFrame.mpr hq
    apply havoid (swapCoordinates q) hqswap
    apply swapCoordinates_mem_rigidFrame.mp
    simpa only [swapCoordinates_add, swapCoordinates_sub, swapCoordinates_west,
      swapCoordinates_south, swapCoordinates_swap] using htarget
  have := congrArg swapCoordinates hswap
  simpa only [swapCoordinates_swap, swapCoordinates_east] using this

private theorem rigidFrame_west_predecessor {T : Set IntegerPlane}
    (hT : TilesUniverse rigidFrame T) {t : IntegerPlane} (ht : t ∈ T) :
    t - latticePoint 4 0 ∈ T := by
  have hhole : markerWestHole ∉ rigidFrame := by
    rw [mem_rigidFrame_iff]
    norm_num [markerWestHole, latticePoint]
  let x := markerWestHole + t
  obtain ⟨s, hs, -⟩ := existsUnique_tile_representation hT x
  let t' := x - s
  have ht' : t' ∈ T := hs.2
  have ht'ne : t' ≠ t := by
    intro heq
    apply hhole
    have : markerWestHole = s := by
      funext i
      have hi := congrFun heq i
      simp only [t', x, Pi.sub_apply, Pi.add_apply] at hi
      omega
    rw [this]
    exact hs.1
  have havoid : ∀ q ∈ rigidFrame,
      q + (markerWestHole - s) ∉ rigidFrame := by
    intro q hq hshift
    apply ht'ne
    symm
    apply translation_eq_of_eq_representations hT hshift ht hq ht'
    dsimp only [t', x]
    abel
  have hsEast := rigidFrame_west_filler hs.1 havoid
  have ht'eq : t' = t - latticePoint 4 0 := by
    dsimp only [t', x]
    rw [hsEast]
    funext i
    fin_cases i
    · change 0 + t 0 - 4 = t 0 - 4
      ring
    · change 1 + t 1 - 1 = t 1 - 0
      ring
  rwa [← ht'eq]

private theorem rigidFrame_south_predecessor {T : Set IntegerPlane}
    (hT : TilesUniverse rigidFrame T) {t : IntegerPlane} (ht : t ∈ T) :
    t - latticePoint 0 4 ∈ T := by
  have hhole : markerSouthHole ∉ rigidFrame := by
    rw [mem_rigidFrame_iff]
    norm_num [markerSouthHole, latticePoint]
  let x := markerSouthHole + t
  obtain ⟨s, hs, -⟩ := existsUnique_tile_representation hT x
  let t' := x - s
  have ht' : t' ∈ T := hs.2
  have ht'ne : t' ≠ t := by
    intro heq
    apply hhole
    have : markerSouthHole = s := by
      funext i
      have hi := congrFun heq i
      simp only [t', x, Pi.sub_apply, Pi.add_apply] at hi
      omega
    rw [this]
    exact hs.1
  have havoid : ∀ q ∈ rigidFrame,
      q + (markerSouthHole - s) ∉ rigidFrame := by
    intro q hq hshift
    apply ht'ne
    symm
    apply translation_eq_of_eq_representations hT hshift ht hq ht'
    dsimp only [t', x]
    abel
  have hsNorth := rigidFrame_south_filler hs.1 havoid
  have ht'eq : t' = t - latticePoint 0 4 := by
    dsimp only [t', x]
    rw [hsNorth]
    funext i
    fin_cases i
    · change 1 + t 0 - 1 = t 0 - 0
      ring
    · change 0 + t 1 - 4 = t 1 - 4
      ring
  rwa [← ht'eq]

@[simp]
private theorem latticePoint_add (a b c d : ℤ) :
    latticePoint a b + latticePoint c d = latticePoint (a + c) (b + d) := by
  funext i
  fin_cases i <;> rfl

private theorem rigidFrame_sub_nat_horizontal {T : Set IntegerPlane}
    (hT : TilesUniverse rigidFrame T) {t : IntegerPlane} (ht : t ∈ T) (k : ℕ) :
    t - latticePoint (4 * k) 0 ∈ T := by
  induction k with
  | zero =>
      convert ht using 1
      funext i
      fin_cases i
      · change t 0 - 0 = t 0
        ring
      · change t 1 - 0 = t 1
        ring
  | succ k ih =>
      have hp := rigidFrame_west_predecessor hT ih
      convert hp using 1
      funext i
      fin_cases i
      · change t 0 - (4 * (k + 1) : ℕ) = t 0 - (4 * k : ℕ) - 4
        push_cast
        ring
      · change t 1 - 0 = t 1 - 0 - 0
        ring

private theorem rigidFrame_sub_nat_vertical {T : Set IntegerPlane}
    (hT : TilesUniverse rigidFrame T) {t : IntegerPlane} (ht : t ∈ T) (k : ℕ) :
    t - latticePoint 0 (4 * k) ∈ T := by
  induction k with
  | zero =>
      convert ht using 1
      funext i
      fin_cases i
      · change t 0 - 0 = t 0
        ring
      · change t 1 - 0 = t 1
        ring
  | succ k ih =>
      have hp := rigidFrame_south_predecessor hT ih
      convert hp using 1
      funext i
      fin_cases i
      · change t 0 - 0 = t 0 - 0 - 0
        ring
      · change t 1 - (4 * (k + 1) : ℕ) = t 1 - (4 * k : ℕ) - 4
        push_cast
        ring

private theorem rigidFrame_sub_nat_pair {T : Set IntegerPlane}
    (hT : TilesUniverse rigidFrame T) {t : IntegerPlane} (ht : t ∈ T) (a b : ℕ) :
    t - latticePoint (4 * a) (4 * b) ∈ T := by
  have hh := rigidFrame_sub_nat_horizontal hT ht a
  have hv := rigidFrame_sub_nat_vertical hT hh b
  convert hv using 1
  funext i
  fin_cases i
  · change t 0 - (4 * a : ℕ) = t 0 - (4 * a : ℕ) - 0
    ring
  · change t 1 - (4 * b : ℕ) = t 1 - 0 - (4 * b : ℕ)
    ring

private theorem rigidFrame_overlap_of_coordinate_bounds {d : IntegerPlane}
    (hxlo : -3 ≤ d 0) (hxhi : d 0 ≤ 3)
    (hylo : -3 ≤ d 1) (hyhi : d 1 ≤ 3) :
    ∃ q ∈ rigidFrame, q + d ∈ rigidFrame := by
  have hex : ∃ a b : ℤ,
      0 ≤ a ∧ a ≤ 3 ∧ 0 ≤ b ∧ b ≤ 3 ∧
      ¬(a = 0 ∧ b = 1) ∧ ¬(a = 1 ∧ b = 0) ∧
      0 ≤ a + d 0 ∧ a + d 0 ≤ 3 ∧
      0 ≤ b + d 1 ∧ b + d 1 ≤ 3 ∧
      ¬(a + d 0 = 0 ∧ b + d 1 = 1) ∧
      ¬(a + d 0 = 1 ∧ b + d 1 = 0) := by
    let x : ℤ := d 0
    let y : ℤ := d 1
    change ∃ a b : ℤ,
      0 ≤ a ∧ a ≤ 3 ∧ 0 ≤ b ∧ b ≤ 3 ∧
      ¬(a = 0 ∧ b = 1) ∧ ¬(a = 1 ∧ b = 0) ∧
      0 ≤ a + x ∧ a + x ≤ 3 ∧
      0 ≤ b + y ∧ b + y ≤ 3 ∧
      ¬(a + x = 0 ∧ b + y = 1) ∧
      ¬(a + x = 1 ∧ b + y = 0)
    have hxlo' : -3 ≤ x := by simpa [x] using hxlo
    have hxhi' : x ≤ 3 := by simpa [x] using hxhi
    have hylo' : -3 ≤ y := by simpa [y] using hylo
    have hyhi' : y ≤ 3 := by simpa [y] using hyhi
    interval_cases x <;> interval_cases y
    all_goals
      first
      | exact ⟨0, 0, by omega⟩
      | exact ⟨0, 2, by omega⟩
      | exact ⟨0, 3, by omega⟩
      | exact ⟨1, 1, by omega⟩
      | exact ⟨1, 2, by omega⟩
      | exact ⟨1, 3, by omega⟩
      | exact ⟨2, 0, by omega⟩
      | exact ⟨2, 1, by omega⟩
      | exact ⟨2, 2, by omega⟩
      | exact ⟨2, 3, by omega⟩
      | exact ⟨3, 0, by omega⟩
      | exact ⟨3, 1, by omega⟩
      | exact ⟨3, 2, by omega⟩
      | exact ⟨3, 3, by omega⟩
  obtain ⟨a, b, ha0, ha3, hb0, hb3, hwest, hsouth,
    had0, had3, hbd0, hbd3, hwest', hsouth'⟩ := hex
  refine ⟨latticePoint a b, ?_, ?_⟩
  · rw [mem_rigidFrame_iff]
    right; right
    exact ⟨ha0, ha3, hb0, hb3,
      by intro h; apply hwest; exact ⟨congrFun h 0, congrFun h 1⟩,
      by intro h; apply hsouth; exact ⟨congrFun h 0, congrFun h 1⟩⟩
  · have hd : d = latticePoint (d 0) (d 1) := by
      funext i
      fin_cases i <;> rfl
    rw [hd, latticePoint_add, mem_rigidFrame_iff]
    right; right
    exact ⟨had0, had3, hbd0, hbd3,
      by intro h; apply hwest'; exact ⟨congrFun h 0, congrFun h 1⟩,
      by intro h; apply hsouth'; exact ⟨congrFun h 0, congrFun h 1⟩⟩

private theorem exists_nat_shifts_close (a b : ℤ) :
    ∃ ka kb : ℕ,
      -3 ≤ (a - 4 * (ka : ℤ)) - (b - 4 * (kb : ℤ)) ∧
        (a - 4 * (ka : ℤ)) - (b - 4 * (kb : ℤ)) ≤ 3 := by
  let m : ℤ := min (a / 4) (b / 4)
  let ka : ℕ := (a / 4 - m).toNat
  let kb : ℕ := (b / 4 - m).toNat
  have hma : m ≤ a / 4 := min_le_left _ _
  have hmb : m ≤ b / 4 := min_le_right _ _
  have hka : (ka : ℤ) = a / 4 - m := by
    exact Int.toNat_of_nonneg (by omega)
  have hkb : (kb : ℤ) = b / 4 - m := by
    exact Int.toNat_of_nonneg (by omega)
  have harem0 : 0 ≤ a % 4 := Int.emod_nonneg _ (by norm_num)
  have harem4 : a % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hbrem0 : 0 ≤ b % 4 := Int.emod_nonneg _ (by norm_num)
  have hbrem4 : b % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have haeq := Int.emod_add_mul_ediv a 4
  have hbeq := Int.emod_add_mul_ediv b 4
  refine ⟨ka, kb, ?_⟩
  rw [hka, hkb]
  omega

/-- Every exact tiling by the interlocking four-by-four frame uses translations from one coset of
the coarse lattice `4ℤ²`. -/
theorem rigidFrame_translation_differences_mem_lattice
    {T : Set IntegerPlane} (hT : TilesUniverse rigidFrame T)
    {t u : IntegerPlane} (ht : t ∈ T) (hu : u ∈ T) :
    t - u ∈ markerLattice 0 := by
  obtain ⟨tx, ux, hxlo, hxhi⟩ := exists_nat_shifts_close (t 0) (u 0)
  obtain ⟨ty, uy, hylo, hyhi⟩ := exists_nat_shifts_close (t 1) (u 1)
  let t' := t - latticePoint (4 * tx) (4 * ty)
  let u' := u - latticePoint (4 * ux) (4 * uy)
  have ht' : t' ∈ T := rigidFrame_sub_nat_pair hT ht tx ty
  have hu' : u' ∈ T := rigidFrame_sub_nat_pair hT hu ux uy
  let d := t' - u'
  have hdxlo : -3 ≤ d 0 := by
    change -3 ≤ (t 0 - 4 * (tx : ℤ)) - (u 0 - 4 * (ux : ℤ))
    exact hxlo
  have hdxhi : d 0 ≤ 3 := by
    change (t 0 - 4 * (tx : ℤ)) - (u 0 - 4 * (ux : ℤ)) ≤ 3
    exact hxhi
  have hdylo : -3 ≤ d 1 := by
    change -3 ≤ (t 1 - 4 * (ty : ℤ)) - (u 1 - 4 * (uy : ℤ))
    exact hylo
  have hdyhi : d 1 ≤ 3 := by
    change (t 1 - 4 * (ty : ℤ)) - (u 1 - 4 * (uy : ℤ)) ≤ 3
    exact hyhi
  obtain ⟨q, hq, hqd⟩ :=
    rigidFrame_overlap_of_coordinate_bounds hdxlo hdxhi hdylo hdyhi
  have hut : u' = t' := by
    apply translation_eq_of_eq_representations hT hqd hu' hq ht'
    dsimp only [d]
    abel
  rw [mem_markerLattice_iff]
  refine ⟨latticePoint ((tx : ℤ) - ux) ((ty : ℤ) - uy), ?_⟩
  funext i
  fin_cases i
  · have hi := congrFun hut.symm 0
    dsimp only [t', u'] at hi
    change t 0 - 4 * (tx : ℤ) = u 0 - 4 * (ux : ℤ) at hi
    change (markerSide 0 : ℤ) * ((tx : ℤ) - ux) = t 0 - u 0
    norm_num [markerSide]
    omega
  · have hi := congrFun hut.symm 1
    dsimp only [t', u'] at hi
    change t 1 - 4 * (ty : ℤ) = u 1 - 4 * (uy : ℤ) at hi
    change (markerSide 0 : ℤ) * ((ty : ℤ) - uy) = t 1 - u 1
    norm_num [markerSide]
    omega

end Tiling.RationalPolygonal
