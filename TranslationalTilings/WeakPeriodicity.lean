import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Index
import TranslationalTilings.Analysis.PolynomialRigidity
import TranslationalTilings.Structure.Grouped

/-!
# Quantitative weak periodicity in the plane

Canonical grouped directions, the exact arithmetic lattice certificate, and
the quantitative and qualitative weak-periodicity theorems.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- The primitive direction of a plane vector, oriented by a fixed lexicographic sign rule. -/
def canonicalDirection (h : Plane) : Plane :=
  let v := primitivePart h
  if v 0 < 0 ∨ (v 0 = 0 ∧ v 1 < 0) then -v else v

/-- Identifies a plane vector with an ordered pair of integers. -/
def planeToPair (h : Plane) : ℤ ×ₗ ℤ := (h 0, h 1)

/-- Identifies an ordered pair of integers with a plane vector. -/
def pairToPlane (p : ℤ ×ₗ ℤ) : Plane := ![p.1, p.2]

/-- The finite set of canonical nonzero direction keys occurring in a tile. -/
def groupedDirectionPairs (F : Finset Plane) : Finset (ℤ ×ₗ ℤ) :=
  (F.erase 0).image fun f ↦ planeToPair (canonicalDirection f)

/-- The number of commensurability classes of nonzero tile elements. -/
def groupedDirectionCount (F : Finset Plane) : ℕ :=
  (groupedDirectionPairs F).card

/-- The least common multiple of contents in the canonical direction class `v`. -/
def groupedDirectionScale (F : Finset Plane) (v : Plane) : ℕ :=
  ((F.erase 0).filter fun f ↦ canonicalDirection f = v).lcm vectorContent

/-- The sorted list of canonical common multiples of all nonzero tile directions. -/
def groupedTileDirections (F : Finset Plane) :
    Fin (groupedDirectionCount F) → Plane :=
  fun i ↦
    let v := pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl i)
    (groupedDirectionScale F v : ℤ) • v

private theorem pairToPlane_planeToPair (v : Plane) :
    pairToPlane (planeToPair v) = v := by
  funext i
  fin_cases i <;> rfl

private theorem planeToPair_injective : Function.Injective planeToPair := by
  intro u v huv
  rw [← pairToPlane_planeToPair u, ← pairToPlane_planeToPair v, huv]

private theorem planeToPair_pairToPlane (p : ℤ ×ₗ ℤ) :
    planeToPair (pairToPlane p) = p := by
  apply Prod.ext <;> rfl

private theorem orientedPrimitive_neg {v : Plane} (hv : v ≠ 0) :
    (if (-v) 0 < 0 ∨ ((-v) 0 = 0 ∧ (-v) 1 < 0) then -(-v) else -v) =
      (if v 0 < 0 ∨ (v 0 = 0 ∧ v 1 < 0) then -v else v) := by
  have hvcoords : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    fin_cases i <;> simp [h.1, h.2]
  have hbadneg :
      ((-v) 0 < 0 ∨ ((-v) 0 = 0 ∧ (-v) 1 < 0)) ↔
        ¬ (v 0 < 0 ∨ (v 0 = 0 ∧ v 1 < 0)) := by
    simp only [Pi.neg_apply]
    rcases hvcoords with h0 | h1 <;> omega
  by_cases hbad : v 0 < 0 ∨ (v 0 = 0 ∧ v 1 < 0)
  · have hnbad : ¬ ((-v) 0 < 0 ∨ ((-v) 0 = 0 ∧ (-v) 1 < 0)) := by
      exact fun hn ↦ (hbadneg.mp hn) hbad
    rw [if_neg hnbad, if_pos hbad]
  · have hnbad : (-v) 0 < 0 ∨ ((-v) 0 = 0 ∧ (-v) 1 < 0) :=
      hbadneg.mpr hbad
    rw [if_pos hnbad, if_neg hbad]
    simp

private theorem vectorContent_zsmul (z : ℤ) (v : Plane) :
    vectorContent (z • v) = Int.natAbs z * vectorContent v := by
  simp [vectorContent, Int.natAbs_mul, Finset.gcd_mul_left]

/-- Canonical orientation preserves nonzeroness. -/
theorem canonicalDirection_ne_zero {h : Plane} (hh : h ≠ 0) :
    canonicalDirection h ≠ 0 := by
  have hp : primitivePart h ≠ 0 := (primitive_decomposition hh).2.1
  simp only [canonicalDirection]
  split_ifs <;> simp_all

/-- Every nonzero plane vector is a nonzero integer multiple of its canonical direction. -/
theorem tile_integer_multiple_of_canonicalDirection
    {h : Plane} (hh : h ≠ 0) :
    ∃ z : ℤ, z ≠ 0 ∧ h = z • canonicalDirection h := by
  have hc : (vectorContent h : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (vectorContent_pos hh))
  have hdecomp := (primitive_decomposition hh).1
  by_cases horient :
      (primitivePart h) 0 < 0 ∨
        ((primitivePart h) 0 = 0 ∧ (primitivePart h) 1 < 0)
  · refine ⟨-(vectorContent h : ℤ), neg_ne_zero.mpr hc, ?_⟩
    rw [canonicalDirection, if_pos horient, neg_smul, smul_neg, neg_neg]
    exact hdecomp.symm
  · refine ⟨(vectorContent h : ℤ), hc, ?_⟩
    rw [canonicalDirection, if_neg horient]
    exact hdecomp.symm

/-- Two nonzero vectors have the same canonical direction exactly when they are commensurable. -/
theorem canonicalDirection_eq_iff_commensurable
    {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) :
    canonicalDirection u = canonicalDirection v ↔ Commensurable u v := by
  constructor
  · intro heq
    obtain ⟨a, ha, hua⟩ := tile_integer_multiple_of_canonicalDirection hu
    obtain ⟨b, hb, hvb⟩ := tile_integer_multiple_of_canonicalDirection hv
    exact ⟨b, a, hb, ha, by rw [hua, hvb, heq]; module⟩
  · intro hcomm
    let pu := primitivePart u
    let pv := primitivePart v
    have hpu : IsPrimitive pu := (primitive_decomposition hu).2
    have hpv : IsPrimitive pv := (primitive_decomposition hv).2
    have huv : Commensurable pu pv := by
      obtain ⟨a, b, ha, hb, hab⟩ := hcomm
      have hcu : (vectorContent u : ℤ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (vectorContent_pos hu))
      have hcv : (vectorContent v : ℤ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (vectorContent_pos hv))
      refine ⟨a * (vectorContent u : ℤ), b * (vectorContent v : ℤ),
        mul_ne_zero ha hcu, mul_ne_zero hb hcv, ?_⟩
      dsimp [pu, pv]
      rw [mul_smul, (primitive_decomposition hu).1,
        mul_smul, (primitive_decomposition hv).1]
      exact hab
    obtain ⟨z, hz, hpuz⟩ :=
      integer_multiple_of_primitive_of_commensurable hpu.1 hpv huv
    have hzabs : Int.natAbs z = 1 := by
      have hc := congrArg vectorContent hpuz
      rw [vectorContent_zsmul, hpu.2, hpv.2, mul_one] at hc
      exact hc.symm
    have hz_cases : z = 1 ∨ z = -1 := by
      cases z with
      | ofNat n =>
          left
          change n = 1 at hzabs
          subst n
          rfl
      | negSucc n =>
          right
          change n + 1 = 1 at hzabs
          have hn : n = 0 := by omega
          subst n
          rfl
    rcases hz_cases with rfl | rfl
    · rw [canonicalDirection, canonicalDirection]
      change (if pu 0 < 0 ∨ (pu 0 = 0 ∧ pu 1 < 0) then -pu else pu) =
        if pv 0 < 0 ∨ (pv 0 = 0 ∧ pv 1 < 0) then -pv else pv
      simpa using congrArg
        (fun w : Plane ↦
          if w 0 < 0 ∨ (w 0 = 0 ∧ w 1 < 0) then -w else w) hpuz
    · have hpueq : pu = -pv := by simpa using hpuz
      rw [canonicalDirection, canonicalDirection]
      change (if pu 0 < 0 ∨ (pu 0 = 0 ∧ pu 1 < 0) then -pu else pu) =
        if pv 0 < 0 ∨ (pv 0 = 0 ∧ pv 1 < 0) then -pv else pv
      rw [hpueq]
      exact orientedPrimitive_neg hpv.1

/-- A tile containing zero and at least one other point has a canonical direction. -/
theorem groupedDirectionCount_pos
    {F : Finset Plane} (hzero : 0 ∈ F) (hcard : 1 < F.card) :
    0 < groupedDirectionCount F := by
  rw [groupedDirectionCount, Finset.card_pos]
  have herase : (F.erase 0).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hzero]
    omega
  obtain ⟨f, hf⟩ := herase
  exact ⟨planeToPair (canonicalDirection f),
    Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩

/-- The number of direction classes is at most the size of the nonzero tile. -/
theorem groupedDirectionCount_le_erase (F : Finset Plane) :
    groupedDirectionCount F ≤ (F.erase 0).card := by
  exact Finset.card_image_le

/-- For a tile containing zero, the direction count is at most `F.card - 1`. -/
theorem groupedDirectionCount_le
    {F : Finset Plane} (hzero : 0 ∈ F) :
    groupedDirectionCount F ≤ F.card - 1 := by
  rw [← Finset.card_erase_of_mem hzero]
  exact groupedDirectionCount_le_erase F

/-- A singleton nonzero tile has exactly one grouped direction. -/
theorem groupedDirectionCount_singleton_ne_zero
    {f : Plane} (hf : f ≠ 0) :
    groupedDirectionCount {f} = 1 := by
  have hz : (0 : Plane) ≠ f := Ne.symm hf
  simp [groupedDirectionCount, groupedDirectionPairs, hz]

private theorem groupedDirectionScale_pos_of_mem
    {F : Finset Plane} {v : Plane}
    (hv : planeToPair v ∈ groupedDirectionPairs F) :
    0 < groupedDirectionScale F v := by
  obtain ⟨f, hf, hp⟩ := Finset.mem_image.mp hv
  have hfne : f ≠ 0 := Finset.ne_of_mem_erase hf
  have hfv : canonicalDirection f = v := by
    apply planeToPair_injective
    exact hp
  rw [Nat.pos_iff_ne_zero]
  intro hzero
  rw [groupedDirectionScale, Finset.lcm_eq_zero_iff] at hzero
  obtain ⟨g, hg, hgzero⟩ := hzero
  have hgne : g ≠ 0 :=
    Finset.ne_of_mem_erase (Finset.mem_filter.mp hg).1
  exact (Nat.ne_of_gt (vectorContent_pos hgne)) hgzero

private theorem groupedTileDirection_key_mem {F : Finset Plane}
    (j : Fin (groupedDirectionCount F)) :
    planeToPair (pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl j)) ∈
      groupedDirectionPairs F := by
  rw [planeToPair_pairToPlane]
  exact Finset.orderEmbOfFin_mem (groupedDirectionPairs F) rfl j

/-- Every canonical grouped tile direction is nonzero. -/
theorem groupedTileDirections_ne_zero
    {F : Finset Plane} (_hzero : 0 ∈ F) (_hcard : 1 < F.card) :
    ∀ j, groupedTileDirections F j ≠ 0 := by
  intro j
  let v := pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl j)
  have hscale : 0 < groupedDirectionScale F v :=
    groupedDirectionScale_pos_of_mem (groupedTileDirection_key_mem j)
  have hv : v ≠ 0 := by
    obtain ⟨f, hf, hp⟩ := Finset.mem_image.mp (groupedTileDirection_key_mem j)
    have hfne : f ≠ 0 := Finset.ne_of_mem_erase hf
    have hfv : canonicalDirection f = v := planeToPair_injective hp
    rw [← hfv]
    exact canonicalDirection_ne_zero hfne
  dsimp [groupedTileDirections]
  exact smul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hscale)) hv

private theorem canonicalDirection_groupedTileDirections
    {F : Finset Plane} (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (j : Fin (groupedDirectionCount F)) :
    canonicalDirection (groupedTileDirections F j) =
      pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl j) := by
  let v := pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl j)
  obtain ⟨f, hf, hp⟩ := Finset.mem_image.mp (groupedTileDirection_key_mem j)
  have hfne : f ≠ 0 := Finset.ne_of_mem_erase hf
  have hfv : canonicalDirection f = v := planeToPair_injective hp
  have hspos : 0 < groupedDirectionScale F v :=
    groupedDirectionScale_pos_of_mem (groupedTileDirection_key_mem j)
  have hgroup : groupedTileDirections F j =
      (groupedDirectionScale F v : ℤ) • v := by rfl
  obtain ⟨z, hz, hfz⟩ := tile_integer_multiple_of_canonicalDirection hfne
  change canonicalDirection (groupedTileDirections F j) = v
  rw [← hfv]
  apply (canonicalDirection_eq_iff_commensurable
    (groupedTileDirections_ne_zero hzero hcard j) hfne).2
  refine ⟨z, (groupedDirectionScale F v : ℤ), hz,
    by exact_mod_cast (Nat.ne_of_gt hspos), ?_⟩
  calc
    z • groupedTileDirections F j =
        z • ((groupedDirectionScale F v : ℤ) • v) := by rw [hgroup]
    _ = (groupedDirectionScale F v : ℤ) •
        (z • canonicalDirection f) := by rw [hfv]; module
    _ = (groupedDirectionScale F v : ℤ) • f :=
      congrArg ((groupedDirectionScale F v : ℤ) • ·) hfz.symm

/-- Distinct canonical grouped tile directions are pairwise incommensurable. -/
theorem groupedTileDirections_pairwise
    {F : Finset Plane} (hzero : 0 ∈ F) (hcard : 1 < F.card) :
    PairwiseIncommensurable (groupedTileDirections F) := by
  intro i j hij hcomm
  have hine := groupedTileDirections_ne_zero hzero hcard i
  have hjne := groupedTileDirections_ne_zero hzero hcard j
  have hcanon := (canonicalDirection_eq_iff_commensurable hine hjne).2 hcomm
  have hcani := canonicalDirection_groupedTileDirections hzero hcard i
  have hcanj := canonicalDirection_groupedTileDirections hzero hcard j
  rw [hcani, hcanj] at hcanon
  apply hij
  apply (groupedDirectionPairs F).orderEmbOfFin rfl |>.injective
  rw [← planeToPair_pairToPlane
    ((groupedDirectionPairs F).orderEmbOfFin rfl i),
    ← planeToPair_pairToPlane
      ((groupedDirectionPairs F).orderEmbOfFin rfl j), hcanon]

/-- Every grouped direction is an integer multiple of a nonzero tile element. -/
theorem groupedTileDirections_from_tile
    {F : Finset Plane} (_hzero : 0 ∈ F) (_hcard : 1 < F.card) :
    ∀ j, ∃ f ∈ F, f ≠ 0 ∧ ∃ z : ℤ,
      groupedTileDirections F j = z • f := by
  intro j
  let v := pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl j)
  obtain ⟨f, hf, hp⟩ := Finset.mem_image.mp (groupedTileDirection_key_mem j)
  have hfne : f ≠ 0 := Finset.ne_of_mem_erase hf
  have hfv : canonicalDirection f = v := planeToPair_injective hp
  have hdiv : vectorContent f ∣ groupedDirectionScale F v := by
    apply Finset.dvd_lcm
    exact Finset.mem_filter.mpr ⟨hf, hfv⟩
  obtain ⟨c, hc⟩ := hdiv
  have hdecomp : (vectorContent f : ℤ) • primitivePart f = f :=
    (primitive_decomposition hfne).1
  have hgroup : groupedTileDirections F j =
      (groupedDirectionScale F v : ℤ) • v := by rfl
  by_cases horient :
      (primitivePart f) 0 < 0 ∨
        ((primitivePart f) 0 = 0 ∧ (primitivePart f) 1 < 0)
  · refine ⟨f, (Finset.mem_erase.mp hf).2, hfne, -(c : ℤ), ?_⟩
    calc
      groupedTileDirections F j =
          ((vectorContent f * c : ℕ) : ℤ) • (-primitivePart f) := by
        rw [hgroup, hc, ← hfv, canonicalDirection, if_pos horient]
      _ = -(c : ℤ) • ((vectorContent f : ℤ) • primitivePart f) := by
        norm_cast
        module
      _ = -(c : ℤ) • f := by rw [hdecomp]
  · refine ⟨f, (Finset.mem_erase.mp hf).2, hfne, (c : ℤ), ?_⟩
    calc
      groupedTileDirections F j =
          ((vectorContent f * c : ℕ) : ℤ) • primitivePart f := by
        rw [hgroup, hc, ← hfv, canonicalDirection, if_neg horient]
      _ = (c : ℤ) • ((vectorContent f : ℤ) • primitivePart f) := by
        norm_cast
        module
      _ = (c : ℤ) • f := by rw [hdecomp]

/-- The least common multiple of the wedges with the avoidance vector. -/
def directionAvoidanceLCM {m : ℕ} (h : Fin m → Plane) : ℕ :=
  (Finset.univ : Finset (Fin m)).lcm fun j ↦
    Int.natAbs (wedge (avoidanceVector h) (h j))

/-- A common rigidity period for all circle-polynomial degrees up to the direction count. -/
def weakRigidityPeriod (directionCount : ℕ) : ℕ :=
  (Finset.range (directionCount + 1)).lcm universalRigidityPeriod

/-- Closed `ℓ¹` bound for each advertised period direction. -/
def weakPeriodVectorBound (tileCard diameter : ℕ) : ℕ :=
  diameter ^ (tileCard - 1)

/-- Tile-cardinality factor in the weak-lattice relative-index bound. -/
def weakPeriodIndexConstant (tileCard : ℕ) : ℕ :=
  4 ^ (4 * tileCard) * (tileCard + 1) ^ (tileCard + 1)

/-- Closed relative-index bound for the quantitative weak lattice. -/
def weakPeriodIndexBound (tileCard diameter : ℕ) : ℕ :=
  weakPeriodIndexConstant tileCard *
    max 1 (diameter ^ (2 * (tileCard - 1) ^ 2))

/-- Tile-cardinality factor in the weak-period multiplier bound. -/
def weakPeriodMultiplierConstant (tileCard : ℕ) : ℕ :=
  weakRigidityPeriod tileCard *
    (tileCard + 1) ^ (2 * tileCard) * 4 ^ (2 * tileCard)

/-- Closed bound for the quantitative weak-period multiplier. -/
def weakPeriodMultiplierBound (tileCard diameter : ℕ) : ℕ :=
  weakPeriodMultiplierConstant tileCard *
    max 1 (diameter ^ (tileCard * (tileCard - 1)))

/-- Euclidean normalization of the weak-lattice index constant. -/
noncomputable def weakPeriodIndexEuclideanConstant (tileCard : ℕ) : ℝ :=
  weakPeriodIndexConstant tileCard *
    Real.sqrt 2 ^ (2 * (tileCard - 1) ^ 2)

/-- Euclidean normalization of the weak-period multiplier constant. -/
noncomputable def weakPeriodMultiplierEuclideanConstant
    (tileCard : ℕ) : ℝ :=
  weakPeriodMultiplierConstant tileCard *
    Real.sqrt 2 ^ (tileCard * (tileCard - 1))

/-- The structural dilation modulus used in the weak-periodicity argument. -/
def weakQ (F : Finset Plane) (ell : ℕ) : ℕ :=
  indicatorDilationModulus ell F.card

/-- The pairwise-wedge least common multiple of a direction family. -/
def weakN {m : ℕ} (h : Fin m → Plane) : ℕ := pairWedgeLCM h

/-- The bounded vector avoiding every direction in a family. -/
def weakAvoidance {m : ℕ} (h : Fin m → Plane) : Plane := avoidanceVector h

/-- The avoidance-wedge least common multiple of a direction family. -/
def weakM {m : ℕ} (h : Fin m → Plane) : ℕ := directionAvoidanceLCM h

/-- The transverse slice vector used to restrict the grouped error functions. -/
def weakSliceVector (F : Finset Plane) (ell : ℕ)
    {m : ℕ} (h : Fin m → Plane) : Plane :=
  ((weakQ F ell * weakN h : ℕ) : ℤ) • weakAvoidance h

/-- The rank-two lattice generated by the slice vector and a scaled first direction. -/
def weakLattice (F : Finset Plane) (ell : ℕ)
    {m : ℕ} (h : Fin m → Plane) (hm : 0 < m) : AddSubgroup Plane :=
  generatedPair (weakSliceVector F ell h)
    (((weakQ F ell * weakN h * weakM h : ℕ) : ℤ) • h ⟨0, hm⟩)

/-- The common scalar multiplier of all advertised one-dimensional periods. -/
def weakMultiplier (F : Finset Plane) (ell : ℕ)
    {m : ℕ} (h : Fin m → Plane) : ℕ :=
  weakRigidityPeriod m * weakM h ^ 2 * weakN h *
    (weakQ F ell / ell)

/-- The avoidance-wedge least common multiple is positive for nonzero directions. -/
theorem directionAvoidanceLCM_pos
    {h : Fin m → Plane} (hne : ∀ j, h j ≠ 0) :
    0 < directionAvoidanceLCM h := by
  rw [Nat.pos_iff_ne_zero]
  intro hzero
  rw [directionAvoidanceLCM, Finset.lcm_eq_zero_iff] at hzero
  obtain ⟨j, _hj, hw⟩ := hzero
  have hav := avoidanceVector_spec hne
  have hwne : wedge (avoidanceVector h) (h j) ≠ 0 := by
    intro hwzero
    exact hav.2.1 j
      ((commensurable_iff_wedge_eq_zero hav.1 (hne j)).2 hwzero)
  exact Int.natAbs_ne_zero.mpr hwne hw

/-- Bounds the avoidance-wedge least common multiple by the product of direction norms. -/
theorem directionAvoidanceLCM_bound
    {h : Fin m → Plane} (hne : ∀ j, h j ≠ 0) :
    directionAvoidanceLCM h ≤
      (m + 1) ^ m * ∏ j, l1Norm (h j) := by
  have hav := avoidanceVector_spec hne
  have hprodpos :
      0 < ∏ j : Fin m, Int.natAbs (wedge (avoidanceVector h) (h j)) := by
    apply Finset.prod_pos
    intro j _
    apply Int.natAbs_pos.mpr
    intro hw
    exact hav.2.1 j
      ((commensurable_iff_wedge_eq_zero hav.1 (hne j)).2 hw)
  calc
    directionAvoidanceLCM h ≤
        ∏ j : Fin m, Int.natAbs (wedge (avoidanceVector h) (h j)) := by
      apply Nat.le_of_dvd hprodpos
      exact Finset.lcm_dvd_prod Finset.univ _
    _ ≤ ∏ j : Fin m, ((m + 1) * l1Norm (h j)) := by
      apply Finset.prod_le_prod'
      intro j _
      calc
        Int.natAbs (wedge (avoidanceVector h) (h j)) ≤
            l1Norm (avoidanceVector h) * l1Norm (h j) :=
          natAbs_wedge_le_l1Norm_mul_l1Norm _ _
        _ ≤ (m + 1) * l1Norm (h j) :=
          Nat.mul_le_mul_right _ hav.2.2
    _ = (m + 1) ^ m * ∏ j, l1Norm (h j) := by
      show (Finset.univ.prod fun j : Fin m ↦
        (m + 1) * l1Norm (h j)) = _
      rw [Finset.prod_mul_distrib]
      simp

private theorem universalRigidityPeriod_pos' (d : ℕ) :
    0 < universalRigidityPeriod d := by
  rw [universalRigidityPeriod, Nat.pos_iff_ne_zero]
  intro hzero
  rw [Finset.lcm_eq_zero_iff] at hzero
  obtain ⟨q, hq, hqzero⟩ := hzero
  simp only [id_eq] at hqzero
  have hqone := (Finset.mem_Icc.mp hq).1
  omega

/-- The universal weak rigidity period is positive. -/
theorem weakRigidityPeriod_pos (directionCount : ℕ) :
    0 < weakRigidityPeriod directionCount := by
  rw [weakRigidityPeriod, Nat.pos_iff_ne_zero]
  intro hzero
  rw [Finset.lcm_eq_zero_iff] at hzero
  obtain ⟨d, _hd, hdzero⟩ := hzero
  exact (Nat.ne_of_gt (universalRigidityPeriod_pos' d)) hdzero

/-- Every bounded-degree universal rigidity period divides the weak rigidity period. -/
theorem universalRigidityPeriod_dvd_weak
    {d directionCount : ℕ} (hd : d ≤ directionCount) :
    universalRigidityPeriod d ∣ weakRigidityPeriod directionCount := by
  apply Finset.dvd_lcm
  simp
  omega

/-- Weak rigidity periods are monotone under divisibility in the direction count. -/
theorem weakRigidityPeriod_dvd_of_le
    {m c : ℕ} (hmc : m ≤ c) :
    weakRigidityPeriod m ∣ weakRigidityPeriod c := by
  apply Finset.lcm_dvd
  intro d hd
  apply Finset.dvd_lcm
  simp only [Finset.mem_range] at hd ⊢
  omega

/-- The target scalar period divides the structural dilation modulus. -/
theorem weakQ_divisibility {F : Finset Plane} {ell : ℕ} (_hell : 0 < ell) :
    ell ∣ weakQ F ell := by
  exact ell_dvd_dilationModulus ell 1 F.card

/-- Bounds the quotient of the structural modulus by the target period. -/
theorem weakQ_quotient_bound
    {F : Finset Plane} {ell : ℕ} (hell : 0 < ell) :
    weakQ F ell / ell ≤ 4 ^ (2 * F.card) := by
  obtain ⟨r, hr⟩ := weakQ_divisibility (F := F) hell
  have hq := grouped_q_bound (ell := ell) (F := F)
  change indicatorDilationModulus ell F.card = ell * r at hr
  change indicatorDilationModulus ell F.card / ell ≤ _
  rw [hr] at hq ⊢
  simpa [Nat.mul_div_cancel_left r hell] using
    (Nat.le_of_mul_le_mul_left hq hell)

private theorem l1Diameter_pos_of_one_lt_card {F : Finset Plane}
    (hcard : 1 < F.card) : 0 < l1Diameter F := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
  have hnorm : 0 < l1Norm (x - y) := by
    rw [Nat.pos_iff_ne_zero]
    intro hzero
    exact hxy (sub_eq_zero.mp (l1Norm_eq_zero.mp hzero))
  exact hnorm.trans_le
    (Finset.le_sup (f := fun zw : Plane × Plane ↦ l1Norm (zw.1 - zw.2))
      (show (x, y) ∈ F ×ˢ F by simp [hx, hy]))

/-- Bounds the pairwise-wedge least common multiple for a grouped decomposition. -/
theorem weakN_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) :
    weakN D.direction ≤ l1Diameter F ^ ((F.card - 1) * (F.card - 2)) := by
  have hmle := D.number_le
  have hmpos := D.number_pos
  have hm1 : D.numberOfDirections - 1 ≤ F.card - 2 := by omega
  calc
    weakN D.direction ≤
        ∏ i, l1Norm (D.direction i) ^ (D.numberOfDirections - 1) :=
      pairWedgeLCM_bound D.direction_ne_zero D.pairwise_incommensurable
    _ = (∏ i, l1Norm (D.direction i)) ^ (D.numberOfDirections - 1) := by
      rw [Finset.prod_pow]
    _ ≤ (l1Diameter F ^ (F.card - 1)) ^
        (D.numberOfDirections - 1) :=
      Nat.pow_le_pow_left D.product_direction_l1_bound _
    _ = l1Diameter F ^ ((F.card - 1) * (D.numberOfDirections - 1)) := by
      rw [pow_mul]
    _ ≤ l1Diameter F ^ ((F.card - 1) * (F.card - 2)) := by
      apply Nat.pow_le_pow_right
      · apply l1Diameter_pos_of_one_lt_card
        omega
      · exact Nat.mul_le_mul_left _ hm1

/-- Bounds the avoidance-wedge least common multiple for a grouped decomposition. -/
theorem weakM_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) :
    weakM D.direction ≤ (F.card + 1) ^ F.card *
      l1Diameter F ^ (F.card - 1) := by
  have hmle := D.number_le
  have hmpos := D.number_pos
  have hmc : D.numberOfDirections ≤ F.card := by omega
  have hpow :
      (D.numberOfDirections + 1) ^ D.numberOfDirections ≤
        (F.card + 1) ^ F.card := by
    exact (Nat.pow_le_pow_left (by omega) _).trans
      (Nat.pow_le_pow_right (by positivity) hmc)
  calc
    weakM D.direction ≤
        (D.numberOfDirections + 1) ^ D.numberOfDirections *
          ∏ j, l1Norm (D.direction j) :=
      directionAvoidanceLCM_bound D.direction_ne_zero
    _ ≤ (F.card + 1) ^ F.card * ∏ j, l1Norm (D.direction j) := by
      gcongr
    _ ≤ (F.card + 1) ^ F.card *
        l1Diameter F ^ (F.card - 1) := by
      gcongr
      exact D.product_direction_l1_bound

/-- The weak rank-two lattice lies inside the target scalar lattice. -/
theorem weakLattice_le_scalar
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
    weakLattice F ell D.direction D.number_pos ≤ scalarLattice ell := by
  obtain ⟨r, hr⟩ := weakQ_divisibility (F := F) hell
  rw [weakLattice, generatedPair]
  apply (AddSubgroup.closure_le _).2
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · refine ⟨(r * weakN D.direction) • weakAvoidance D.direction, ?_⟩
    change ell • ((r * weakN D.direction) • weakAvoidance D.direction) =
      weakSliceVector F ell D.direction
    rw [weakSliceVector, hr]
    norm_cast
    module
  · refine ⟨(r * weakN D.direction * weakM D.direction) •
      D.direction ⟨0, D.number_pos⟩, ?_⟩
    change ell • ((r * weakN D.direction * weakM D.direction) •
        D.direction ⟨0, D.number_pos⟩) =
      ((weakQ F ell * weakN D.direction * weakM D.direction : ℕ) : ℤ) •
        D.direction ⟨0, D.number_pos⟩
    rw [hr]
    norm_cast
    module

private theorem weak_supremumOnePeriod_mem
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) : ∀ j,
    ((weakM D.direction ^ 2 * weakN D.direction * weakQ F ell : ℕ) : ℤ) •
      D.direction j ∈ weakLattice F ell D.direction D.number_pos := by
  intro j
  let a := weakAvoidance D.direction
  let h0 := D.direction ⟨0, D.number_pos⟩
  let q := weakQ F ell
  let N := weakN D.direction
  let M := weakM D.direction
  have hMdivNat : Int.natAbs (wedge a h0) ∣ M := by
    change Int.natAbs (wedge a h0) ∣ directionAvoidanceLCM D.direction
    unfold directionAvoidanceLCM
    apply Finset.dvd_lcm
    exact Finset.mem_univ _
  have hMdivInt : wedge a h0 ∣ (M : ℤ) := by
    rw [← Int.natAbs_dvd]
    exact_mod_cast hMdivNat
  obtain ⟨r, hr⟩ := hMdivInt
  have ha_mem : ((q * N : ℕ) : ℤ) • a ∈
      weakLattice F ell D.direction D.number_pos := by
    apply AddSubgroup.subset_closure
    left
    rfl
  have hh0_mem : ((q * N * M : ℕ) : ℤ) • h0 ∈
      weakLattice F ell D.direction D.number_pos := by
    apply AddSubgroup.subset_closure
    right
    rfl
  have hid := cramer_identity a h0 (D.direction j)
  have heq :
      ((M ^ 2 * N * q : ℕ) : ℤ) • D.direction j =
        (r * (M : ℤ) * wedge (D.direction j) h0) •
            (((q * N : ℕ) : ℤ) • a) +
          (r * wedge a (D.direction j)) •
            (((q * N * M : ℕ) : ℤ) • h0) := by
    have hr' : (M : ℤ) = wedge a h0 * r := hr
    calc
      ((M ^ 2 * N * q : ℕ) : ℤ) • D.direction j =
          ((M : ℤ) * r * (N : ℤ) * (q : ℤ)) •
            (wedge a h0 • D.direction j) := by
        simp only [Nat.cast_mul, Nat.cast_pow]
        rw [hr']
        module
      _ = ((M : ℤ) * r * (N : ℤ) * (q : ℤ)) •
          (wedge (D.direction j) h0 • a +
            wedge a (D.direction j) • h0) := by rw [hid]
      _ = (r * (M : ℤ) * wedge (D.direction j) h0) •
            (((q * N : ℕ) : ℤ) • a) +
          (r * wedge a (D.direction j)) •
            (((q * N * M : ℕ) : ℤ) • h0) := by
        norm_cast
        module
  rw [heq]
  exact (weakLattice F ell D.direction D.number_pos).add_mem
    ((weakLattice F ell D.direction D.number_pos).zsmul_mem ha_mem _)
    ((weakLattice F ell D.direction D.number_pos).zsmul_mem hh0_mem _)

private theorem weak_rigidityBranchPeriod_mem
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) :
    ((weakRigidityPeriod D.numberOfDirections * weakM D.direction *
      weakN D.direction * weakQ F ell : ℕ) : ℤ) •
        D.direction ⟨0, D.number_pos⟩ ∈
      weakLattice F ell D.direction D.number_pos := by
  have hgen :
      ((weakQ F ell * weakN D.direction * weakM D.direction : ℕ) : ℤ) •
          D.direction ⟨0, D.number_pos⟩ ∈
        weakLattice F ell D.direction D.number_pos := by
    apply AddSubgroup.subset_closure
    right
    rfl
  have hz := (weakLattice F ell D.direction D.number_pos).zsmul_mem hgen
    (weakRigidityPeriod D.numberOfDirections : ℤ)
  convert hz using 1
  norm_cast
  module

private theorem weak_advertisedPeriod_mem
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) : ∀ j,
    ((weakRigidityPeriod D.numberOfDirections * weakM D.direction ^ 2 *
      weakN D.direction * weakQ F ell : ℕ) : ℤ) • D.direction j ∈
      weakLattice F ell D.direction D.number_pos := by
  intro j
  have hz := (weakLattice F ell D.direction D.number_pos).zsmul_mem
    (weak_supremumOnePeriod_mem D j)
    (weakRigidityPeriod D.numberOfDirections : ℤ)
  convert hz using 1
  norm_cast
  module

/-- The advertised weak-period multiplier is positive. -/
theorem weakMultiplier_pos
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
    0 < weakMultiplier F ell D.direction := by
  have hqpos : 0 < weakQ F ell := by
    simpa [weakQ, indicatorDilationModulus] using
      dilationModulus_pos (oscillation := 1) (tileCard := F.card) hell
  have hqdiv := weakQ_divisibility (F := F) hell
  have hquot : 0 < weakQ F ell / ell := by
    exact Nat.div_pos (Nat.le_of_dvd hqpos hqdiv) hell
  exact Nat.mul_pos
    (Nat.mul_pos
      (Nat.mul_pos (weakRigidityPeriod_pos D.numberOfDirections)
        (pow_pos (directionAvoidanceLCM_pos D.direction_ne_zero) _))
      (pairWedgeLCM_pos D.direction_ne_zero D.pairwise_incommensurable))
    hquot

/-- The advertised multiplier satisfies the closed `ℓ¹` bound. -/
theorem weakMultiplier_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
    weakMultiplier F ell D.direction ≤
      weakPeriodMultiplierBound F.card (l1Diameter F) := by
  let c := F.card
  let diam := l1Diameter F
  have hmle := D.number_le
  have hmpos := D.number_pos
  have hc2 : 2 ≤ c := by omega
  have hdiam : 0 < diam := l1Diameter_pos_of_one_lt_card (by omega)
  have hQdvd : weakRigidityPeriod D.numberOfDirections ∣ weakRigidityPeriod c :=
    weakRigidityPeriod_dvd_of_le (by omega)
  have hQ : weakRigidityPeriod D.numberOfDirections ≤ weakRigidityPeriod c :=
    Nat.le_of_dvd (weakRigidityPeriod_pos c) hQdvd
  have hM := weakM_bound D
  have hN := weakN_bound D
  have hq := weakQ_quotient_bound (F := F) hell
  have hmain : weakMultiplier F ell D.direction ≤
      weakRigidityPeriod c *
        ((c + 1) ^ c * diam ^ (c - 1)) ^ 2 *
        diam ^ ((c - 1) * (c - 2)) * 4 ^ (2 * c) := by
    unfold weakMultiplier
    dsimp [c, diam] at hM hN hq ⊢
    calc
      weakRigidityPeriod D.numberOfDirections * weakM D.direction ^ 2 *
          weakN D.direction * (weakQ F ell / ell) ≤
        weakRigidityPeriod c * weakM D.direction ^ 2 *
          weakN D.direction * (weakQ F ell / ell) := by gcongr
      _ ≤ weakRigidityPeriod c *
          ((F.card + 1) ^ F.card * l1Diameter F ^ (F.card - 1)) ^ 2 *
          weakN D.direction * (weakQ F ell / ell) := by gcongr
      _ ≤ weakRigidityPeriod c *
          ((F.card + 1) ^ F.card * l1Diameter F ^ (F.card - 1)) ^ 2 *
          l1Diameter F ^ ((F.card - 1) * (F.card - 2)) *
          (weakQ F ell / ell) := by gcongr
      _ ≤ weakRigidityPeriod c *
          ((F.card + 1) ^ F.card * l1Diameter F ^ (F.card - 1)) ^ 2 *
          l1Diameter F ^ ((F.card - 1) * (F.card - 2)) *
          4 ^ (2 * F.card) := by gcongr
  calc
    weakMultiplier F ell D.direction ≤
        weakRigidityPeriod c *
          ((c + 1) ^ c * diam ^ (c - 1)) ^ 2 *
          diam ^ ((c - 1) * (c - 2)) * 4 ^ (2 * c) := hmain
    _ = weakRigidityPeriod c * (c + 1) ^ (2 * c) * 4 ^ (2 * c) *
        diam ^ (c * (c - 1)) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      have hcExp : c * 2 = 2 * c := by omega
      have hdiamPow :
          diam ^ ((c - 1) * 2) * diam ^ ((c - 1) * (c - 2)) =
            diam ^ (c * (c - 1)) := by
        rw [← pow_add]
        congr 1
        calc
          (c - 1) * 2 + (c - 1) * (c - 2) =
              (c - 1) * (2 + (c - 2)) := by ring
          _ = (c - 1) * c := by
            congr 1
            omega
          _ = c * (c - 1) := Nat.mul_comm _ _
      rw [hcExp]
      calc
        weakRigidityPeriod c *
              ((c + 1) ^ (2 * c) * diam ^ ((c - 1) * 2)) *
              diam ^ ((c - 1) * (c - 2)) * 4 ^ (2 * c) =
            weakRigidityPeriod c * (c + 1) ^ (2 * c) * 4 ^ (2 * c) *
              (diam ^ ((c - 1) * 2) *
                diam ^ ((c - 1) * (c - 2))) := by ring
        _ = _ := by rw [hdiamPow]
    _ = weakPeriodMultiplierConstant c * diam ^ (c * (c - 1)) := by rfl
    _ ≤ weakPeriodMultiplierConstant c *
        max 1 (diam ^ (c * (c - 1))) := by
      gcongr
      exact le_max_right _ _
    _ = weakPeriodMultiplierBound F.card (l1Diameter F) := by rfl

/-- The weak lattice has bounded relative index in the target scalar lattice. -/
theorem weakLattice_relativeIndex_bound
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
    (weakLattice F ell D.direction D.number_pos).relIndex (scalarLattice ell) ≤
      weakPeriodIndexBound F.card (l1Diameter F) := by
  let c := F.card
  let diam := l1Diameter F
  let q := weakQ F ell
  let N := weakN D.direction
  let M := weakM D.direction
  let a := weakAvoidance D.direction
  let h0 := D.direction ⟨0, D.number_pos⟩
  have hmle := D.number_le
  have hmpos := D.number_pos
  have hc2 : 2 ≤ c := by omega
  have hdiam : 0 < diam := l1Diameter_pos_of_one_lt_card (by omega)
  have hqpos : 0 < q := by
    simpa [q, weakQ, indicatorDilationModulus] using
      dilationModulus_pos (oscillation := 1) (tileCard := F.card) hell
  have hNpos : 0 < N :=
    pairWedgeLCM_pos D.direction_ne_zero D.pairwise_incommensurable
  have hMpos : 0 < M := directionAvoidanceLCM_pos D.direction_ne_zero
  have haSpec := avoidanceVector_spec D.direction_ne_zero
  have hw0 : wedge a h0 ≠ 0 := by
    intro hw
    exact haSpec.2.1 ⟨0, D.number_pos⟩
      ((commensurable_iff_wedge_eq_zero haSpec.1
        (D.direction_ne_zero ⟨0, D.number_pos⟩)).2 hw)
  have hdet :
      wedge (weakSliceVector F ell D.direction)
        (((q * N * M : ℕ) : ℤ) • h0) ≠ 0 := by
    rw [weakSliceVector, wedge_zsmul_left, wedge_zsmul_right]
    exact mul_ne_zero
      (by exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos hqpos hNpos)))
      (mul_ne_zero
        (by exact_mod_cast
          (Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos hqpos hNpos) hMpos)))
        hw0)
  have hindex :
      (weakLattice F ell D.direction D.number_pos).index =
        q ^ 2 * N ^ 2 * M * Int.natAbs (wedge a h0) := by
    rw [weakLattice, index_generatedPair hdet]
    simp only [weakSliceVector, wedge_zsmul_left, wedge_zsmul_right,
      Int.natAbs_mul, Int.natAbs_natCast]
    dsimp [q, N, M, a, h0]
    ring
  have hlattice := weakLattice_le_scalar D hell
  have hrelIndex := AddSubgroup.relIndex_mul_index hlattice
  rw [scalarLattice_index, hindex] at hrelIndex
  obtain ⟨r, hr⟩ := weakQ_divisibility (F := F) hell
  change q = ell * r at hr
  have hrelEq :
      (weakLattice F ell D.direction D.number_pos).relIndex
          (scalarLattice ell) =
        r ^ 2 * N ^ 2 * M * Int.natAbs (wedge a h0) := by
    apply Nat.mul_right_cancel (pow_pos hell 2)
    calc
      (weakLattice F ell D.direction D.number_pos).relIndex
            (scalarLattice ell) * ell ^ 2 =
          q ^ 2 * N ^ 2 * M * Int.natAbs (wedge a h0) := hrelIndex
      _ = (r ^ 2 * N ^ 2 * M * Int.natAbs (wedge a h0)) * ell ^ 2 := by
        rw [hr, mul_pow]
        ring
  have hrBound : r ≤ 4 ^ (2 * c) := by
    have hqBound := weakQ_quotient_bound (F := F) hell
    change q / ell ≤ 4 ^ (2 * c) at hqBound
    rw [hr, Nat.mul_div_cancel_left r hell] at hqBound
    exact hqBound
  have hNBound : N ≤ diam ^ ((c - 1) * (c - 2)) := weakN_bound D
  have hMBound : M ≤ (c + 1) ^ c * diam ^ (c - 1) := weakM_bound D
  have hnorm0 : l1Norm h0 ≤ ∏ j, l1Norm (D.direction j) := by
    dsimp [h0]
    have hs := Finset.single_le_prod'
      (s := (Finset.univ : Finset (Fin D.numberOfDirections)))
      (f := fun j ↦ l1Norm (D.direction j))
      (a := ⟨0, D.number_pos⟩) (fun j _ ↦ by
        rw [Nat.one_le_iff_ne_zero]
        intro hzero
        exact D.direction_ne_zero j (l1Norm_eq_zero.mp hzero))
      (Finset.mem_univ _)
    simpa using hs
  have hwBound : Int.natAbs (wedge a h0) ≤
      (c + 1) * diam ^ (c - 1) := by
    calc
      Int.natAbs (wedge a h0) ≤ l1Norm a * l1Norm h0 :=
        natAbs_wedge_le_l1Norm_mul_l1Norm _ _
      _ ≤ (D.numberOfDirections + 1) * l1Norm h0 := by
        gcongr
        exact haSpec.2.2
      _ ≤ (c + 1) * (∏ j, l1Norm (D.direction j)) := by
        gcongr
        omega
      _ ≤ (c + 1) * diam ^ (c - 1) := by
        gcongr
        exact D.product_direction_l1_bound
  have hraw :
      (weakLattice F ell D.direction D.number_pos).relIndex
          (scalarLattice ell) ≤
        (4 ^ (2 * c)) ^ 2 *
          (diam ^ ((c - 1) * (c - 2))) ^ 2 *
          ((c + 1) ^ c * diam ^ (c - 1)) *
          ((c + 1) * diam ^ (c - 1)) := by
    rw [hrelEq]
    gcongr
  have hconst : (4 ^ (2 * c)) ^ 2 = 4 ^ (4 * c) := by
    rw [← pow_mul]
    congr 1
    omega
  have hcconst : (c + 1) ^ c * (c + 1) = (c + 1) ^ (c + 1) := by
    rw [pow_succ]
  have hdexp :
      ((c - 1) * (c - 2)) * 2 + (c - 1) + (c - 1) =
        2 * (c - 1) ^ 2 := by
    calc
      ((c - 1) * (c - 2)) * 2 + (c - 1) + (c - 1) =
          2 * (c - 1) * ((c - 2) + 1) := by ring
      _ = 2 * (c - 1) * (c - 1) := by
        congr 2
        omega
      _ = 2 * (c - 1) ^ 2 := by ring
  have hclosed :
      (4 ^ (2 * c)) ^ 2 *
          (diam ^ ((c - 1) * (c - 2))) ^ 2 *
          ((c + 1) ^ c * diam ^ (c - 1)) *
          ((c + 1) * diam ^ (c - 1)) =
        weakPeriodIndexConstant c * diam ^ (2 * (c - 1) ^ 2) := by
    rw [hconst, ← pow_mul]
    calc
      4 ^ (4 * c) * diam ^ (((c - 1) * (c - 2)) * 2) *
            ((c + 1) ^ c * diam ^ (c - 1)) *
            ((c + 1) * diam ^ (c - 1)) =
          4 ^ (4 * c) * ((c + 1) ^ c * (c + 1)) *
            (diam ^ (((c - 1) * (c - 2)) * 2) *
              diam ^ (c - 1) * diam ^ (c - 1)) := by ring
      _ = 4 ^ (4 * c) * (c + 1) ^ (c + 1) *
          diam ^ (2 * (c - 1) ^ 2) := by
        rw [hcconst, ← pow_add, ← pow_add, hdexp]
      _ = weakPeriodIndexConstant c * diam ^ (2 * (c - 1) ^ 2) := rfl
  calc
    (weakLattice F ell D.direction D.number_pos).relIndex
        (scalarLattice ell) ≤ _ := hraw
    _ = weakPeriodIndexConstant c * diam ^ (2 * (c - 1) ^ 2) := hclosed
    _ ≤ weakPeriodIndexConstant c *
        max 1 (diam ^ (2 * (c - 1) ^ 2)) := by
      gcongr
      exact le_max_right _ _
    _ = weakPeriodIndexBound F.card (l1Diameter F) := by rfl

/-- Every advertised direction period belongs to the weak lattice. -/
theorem weak_period_mem_lattice
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
    ∀ j, ((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) • D.direction j ∈
      weakLattice F ell D.direction D.number_pos := by
  intro j
  have hqdiv := weakQ_divisibility (F := F) hell
  have hfactor :
      ell * weakMultiplier F ell D.direction =
        weakRigidityPeriod D.numberOfDirections * weakM D.direction ^ 2 *
          weakN D.direction * weakQ F ell := by
    rw [weakMultiplier]
    obtain ⟨r, hr⟩ := hqdiv
    change weakQ F ell = ell * r at hr
    rw [hr, Nat.mul_div_cancel_left r hell]
    ring
  rw [hfactor]
  exact weak_advertisedPeriod_mem D j

/-- Exact positivity, factorization, and lattice-membership certificates for the weak arithmetic. -/
structure WeakArithmeticData (F : Finset Plane) (ell : ℕ)
    {m : ℕ} (h : Fin m → Plane) (hm : 0 < m) where
  /-- The certified weak lattice. -/
  lattice : AddSubgroup Plane
  /-- The certified common period multiplier. -/
  multiplier : ℕ
  lattice_eq : lattice = weakLattice F ell h hm
  multiplier_eq : multiplier = weakMultiplier F ell h
  q_pos : 0 < weakQ F ell
  pairLCM_pos : 0 < weakN h
  avoidanceLCM_pos : 0 < weakM h
  rigidityPeriod_pos : 0 < weakRigidityPeriod m
  multiplier_pos : 0 < multiplier
  exact_scalar_factor :
    ell * multiplier =
      weakRigidityPeriod m * weakM h ^ 2 * weakN h * weakQ F ell
  supremumOnePeriod_mem : ∀ j,
    ((weakM h ^ 2 * weakN h * weakQ F ell : ℕ) : ℤ) • h j ∈ lattice
  rigidityBranchPeriod_mem :
    ((weakRigidityPeriod m * weakM h * weakN h * weakQ F ell : ℕ) : ℤ) •
      h ⟨0, hm⟩ ∈ lattice
  advertisedPeriod_mem : ∀ j,
    ((weakRigidityPeriod m * weakM h ^ 2 * weakN h *
      weakQ F ell : ℕ) : ℤ) • h j ∈ lattice

/-- Packages all exact arithmetic facts attached to a grouped decomposition. -/
theorem exists_weakArithmeticData
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1) (hell : 0 < ell) :
    Nonempty (WeakArithmeticData F ell D.direction D.number_pos) := by
  have hqpos : 0 < weakQ F ell := by
    simpa [weakQ, indicatorDilationModulus] using
      dilationModulus_pos (oscillation := 1) (tileCard := F.card) hell
  have hfactor :
      ell * weakMultiplier F ell D.direction =
        weakRigidityPeriod D.numberOfDirections * weakM D.direction ^ 2 *
          weakN D.direction * weakQ F ell := by
    rw [weakMultiplier]
    obtain ⟨r, hr⟩ := weakQ_divisibility (F := F) hell
    change weakQ F ell = ell * r at hr
    rw [hr, Nat.mul_div_cancel_left r hell]
    ring
  exact ⟨{
    lattice := weakLattice F ell D.direction D.number_pos
    multiplier := weakMultiplier F ell D.direction
    lattice_eq := rfl
    multiplier_eq := rfl
    q_pos := hqpos
    pairLCM_pos := pairWedgeLCM_pos D.direction_ne_zero
      D.pairwise_incommensurable
    avoidanceLCM_pos := directionAvoidanceLCM_pos D.direction_ne_zero
    rigidityPeriod_pos := weakRigidityPeriod_pos D.numberOfDirections
    multiplier_pos := weakMultiplier_pos D hell
    exact_scalar_factor := hfactor
    supremumOnePeriod_mem := weak_supremumOnePeriod_mem D
    rigidityBranchPeriod_mem := weak_rigidityBranchPeriod_mem D
    advertisedPeriod_mem := weak_advertisedPeriod_mem D }⟩

/-- Uniform directions, lattice, multiplier, and closed bounds for weak periodicity. -/
structure QuantitativeWeakPeriodData
    (F : Finset Plane) (ell : ℕ) where
  /-- The number of pairwise-incommensurable directions. -/
  numberOfDirections : ℕ
  number_pos : 0 < numberOfDirections
  number_le : numberOfDirections ≤ F.card - 1
  /-- The advertised direction family. -/
  direction : Fin numberOfDirections → Plane
  direction_ne_zero : ∀ j, direction j ≠ 0
  pairwise_incommensurable : PairwiseIncommensurable direction
  direction_from_tile : ∀ j,
    ∃ f ∈ F, f ≠ 0 ∧ ∃ z : ℤ, direction j = z • f
  direction_l1_bound : ∀ j,
    l1Norm (direction j) ≤ weakPeriodVectorBound F.card (l1Diameter F)
  direction_euclidean_bound : ∀ j,
    euclideanNorm (direction j) ≤
      (euclideanDiameter F) ^ (F.card - 1)
  product_direction_l1_bound :
    ∏ j : Fin numberOfDirections, l1Norm (direction j) ≤
      l1Diameter F ^ (F.card - 1)
  product_direction_euclidean_bound :
    ∏ j : Fin numberOfDirections, euclideanNorm (direction j) ≤
      euclideanDiameter F ^ (F.card - 1)
  /-- The exact arithmetic certificate for the direction family. -/
  arithmetic : WeakArithmeticData F ell direction number_pos
  lattice_le : arithmetic.lattice ≤ scalarLattice ell
  relativeIndex_bound :
    arithmetic.lattice.relIndex (scalarLattice ell) ≤
      weakPeriodIndexBound F.card (l1Diameter F)
  multiplier_bound :
    arithmetic.multiplier ≤ weakPeriodMultiplierBound F.card (l1Diameter F)
  period_mem_lattice : ∀ j,
    ((ell * arithmetic.multiplier : ℕ) : ℤ) • direction j ∈
      arithmetic.lattice

/-- The weak lattice carried by quantitative weak-period data. -/
abbrev QuantitativeWeakPeriodData.lattice
    {F : Finset Plane} {ell : ℕ}
    (D : QuantitativeWeakPeriodData F ell) : AddSubgroup Plane :=
  D.arithmetic.lattice

/-- The common multiplier carried by quantitative weak-period data. -/
abbrev QuantitativeWeakPeriodData.multiplier
    {F : Finset Plane} {ell : ℕ}
    (D : QuantitativeWeakPeriodData F ell) : ℕ :=
  D.arithmetic.multiplier

/-- The assertion that the data supplies a cosetwise period for a set. -/
def QuantitativeWeakPeriodData.ValidFor
    {F : Finset Plane} {ell : ℕ}
    (D : QuantitativeWeakPeriodData F ell) (A : Set Plane) : Prop :=
  CosetwisePeriodic A D.lattice
    (fun j ↦ ((ell * D.multiplier : ℕ) : ℤ) • D.direction j)

/-- Restricts a grouped error function to an integral affine line. -/
def linePhi {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (e x : Plane) (j : Fin D.numberOfDirections) (n : ℤ) : ℝ :=
  D.phi j (x + n • e)

/-- The circle-valued sum of all restricted error functions vanishes. -/
theorem linePhi_sum_mod_one
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (e x : Plane) (n : ℤ) :
    ∑ j, ((linePhi D e x j n : ℝ) : Torus) = 0 := by
  simpa [linePhi] using structure_decomposition_mod_one D (x + n • e)

private theorem applyDifferences_zero_local {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (directions : List G) :
    applyDifferences directions (0 : G → R) = 0 := by
  induction directions with
  | nil => rfl
  | cons h directions ih =>
      change backwardDiff h (applyDifferences directions (0 : G → R)) = 0
      rw [ih]
      funext x
      simp [backwardDiff]

private theorem lineRestriction_backwardDiffIter_local
    {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (f : G → R) (x h : G) (n : ℕ) :
    lineRestriction (backwardDiffIter h n f) x h =
      backwardDiffIter 1 n (lineRestriction f x h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [backwardDiffIter, Function.iterate_succ_apply',
        backwardDiffIter, Function.iterate_succ_apply']
      change lineRestriction (backwardDiff h (backwardDiffIter h n f)) x h =
        backwardDiff 1 (backwardDiffIter 1 n (lineRestriction f x h))
      rw [lineRestriction_backwardDiff, ih]

private theorem backwardDiffIter_zero_local {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (h : G) (n : ℕ) :
    backwardDiffIter h n (0 : G → R) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [backwardDiffIter, Function.iterate_succ_apply']
      change backwardDiff h (backwardDiffIter h n (0 : G → R)) = 0
      rw [ih]
      funext x
      simp [backwardDiff]

private theorem weakSliceVector_pair_representation
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    {i j : Fin D.numberOfDirections} (hij : i ≠ j) :
    ∃ a b : ℤ, weakSliceVector F ell D.direction =
      a • ((weakQ F ell : ℤ) • D.direction i) +
        b • ((weakQ F ell : ℤ) • D.direction j) := by
  have hNdvdNat :
      Int.natAbs (wedge (D.direction i) (D.direction j)) ∣ weakN D.direction := by
    change Int.natAbs (wedge (D.direction i) (D.direction j)) ∣
      pairWedgeLCM D.direction
    unfold pairWedgeLCM
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact Finset.dvd_lcm (show (i, j) ∈ unorderedPairs D.numberOfDirections by
        simp [unorderedPairs, hij, hijlt])
    · have hdvd : Int.natAbs (wedge (D.direction j) (D.direction i)) ∣
          (unorderedPairs D.numberOfDirections).lcm fun ij ↦
            Int.natAbs (wedge (D.direction ij.1) (D.direction ij.2)) :=
        Finset.dvd_lcm (show (j, i) ∈ unorderedPairs D.numberOfDirections by
          simp [unorderedPairs, hij.symm, hjilt])
      calc
        Int.natAbs (wedge (D.direction i) (D.direction j)) =
            Int.natAbs (wedge (D.direction j) (D.direction i)) := by
          rw [wedge_swap, Int.natAbs_neg]
        _ ∣ _ := hdvd
  have hNdvdInt : wedge (D.direction i) (D.direction j) ∣
      (weakN D.direction : ℤ) := by
    rw [← Int.natAbs_dvd]
    exact_mod_cast hNdvdNat
  obtain ⟨r, hr⟩ := hNdvdInt
  refine ⟨r * wedge (weakAvoidance D.direction) (D.direction j),
    r * wedge (D.direction i) (weakAvoidance D.direction), ?_⟩
  have hid := cramer_identity (D.direction i) (D.direction j)
    (weakAvoidance D.direction)
  have hr' : (weakN D.direction : ℤ) =
      wedge (D.direction i) (D.direction j) * r := hr
  calc
    weakSliceVector F ell D.direction =
        ((weakQ F ell : ℤ) * r) •
          (wedge (D.direction i) (D.direction j) •
            weakAvoidance D.direction) := by
      rw [weakSliceVector]
      simp only [Nat.cast_mul]
      rw [hr']
      module
    _ = ((weakQ F ell : ℤ) * r) •
        (wedge (weakAvoidance D.direction) (D.direction j) • D.direction i +
          wedge (D.direction i) (weakAvoidance D.direction) •
            D.direction j) := by rw [hid]
    _ = (r * wedge (weakAvoidance D.direction) (D.direction j)) •
          ((weakQ F ell : ℤ) • D.direction i) +
        (r * wedge (D.direction i) (weakAvoidance D.direction)) •
          ((weakQ F ell : ℤ) • D.direction j) := by module

/-- Every restricted error function is represented modulo one by a bounded-degree polynomial. -/
theorem linePhi_circlePolynomial
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) (j : Fin D.numberOfDirections) :
    ∃ P : CirclePolynomial (D.numberOfDirections - 2), ∀ n : ℤ,
      P n = (linePhi D (weakSliceVector F ell D.direction) x j n : Torus) := by
  classical
  let q : ℕ := weakQ F ell
  let e : Plane := weakSliceVector F ell D.direction
  let period : Fin D.numberOfDirections → Plane :=
    fun i ↦ (q : ℤ) • D.direction i
  let summand : Fin D.numberOfDirections → Plane → Torus :=
    fun i y ↦ (D.phi i y : Torus)
  have hrepr (i : Fin D.numberOfDirections) (hij : i ≠ j) :
      ∃ a b : ℤ, e = a • period i + b • period j := by
    simpa [e, period, q] using weakSliceVector_pair_representation D hij
  let reprA (i : Fin D.numberOfDirections) (hij : i ≠ j) : ℤ :=
    Classical.choose (hrepr i hij)
  let reprB (i : Fin D.numberOfDirections) (hij : i ≠ j) : ℤ :=
    Classical.choose (Classical.choose_spec (hrepr i hij))
  let targetCoefficient : Fin D.numberOfDirections → ℤ := fun i ↦
    if hij : i = j then 0 else reprB i hij
  have hreprTarget (i : Fin D.numberOfDirections) (hij : i ≠ j) :
      ∃ a : ℤ, e = a • period i + targetCoefficient i • period j := by
    refine ⟨reprA i hij, ?_⟩
    have hspec := Classical.choose_spec (Classical.choose_spec (hrepr i hij))
    simpa [targetCoefficient, reprA, reprB, hij] using hspec
  have hperiod (i : Fin D.numberOfDirections) :
      Function.Periodic (summand i) (period i) := by
    intro y
    change (D.phi i (y + (q : ℤ) • D.direction i) : Torus) =
      (D.phi i y : Torus)
    have hp := D.phi_periodic i y
    simpa [q, weakQ] using congrArg (fun t : ℝ ↦ (t : Torus)) hp
  have hdecomp :
      (0 : Plane → Torus) = ∑ i, summand i := by
    funext y
    simp only [Pi.zero_apply, Finset.sum_apply]
    change (0 : Torus) = ∑ i, (D.phi i y : Torus)
    exact (structure_decomposition_mod_one D y).symm
  have helim := eliminate_periodic_summands j (0 : Plane → Torus)
    summand e period targetCoefficient hdecomp hperiod hreprTarget
  rw [applyDifferences_zero_local] at helim
  have hplane : backwardDiffIter e (D.numberOfDirections - 1) (summand j) = 0 :=
    by simpa using helim.symm
  let f : ℤ → Torus := lineRestriction (summand j) x e
  by_cases hm : D.numberOfDirections = 1
  · have hfzero : f = 0 := by
      funext n
      have hsum := linePhi_sum_mod_one D e x n
      have hsumSingle :
          (∑ i, ((linePhi D e x i n : ℝ) : Torus)) =
            (linePhi D e x j n : Torus) := by
        apply Finset.sum_eq_single j
        · intro i _ hij
          exact (hij (Fin.ext (by omega))).elim
        · simp
      rw [hsumSingle] at hsum
      change f n = 0
      simpa [f, summand, lineRestriction, linePhi] using hsum
    have hdiff : backwardDiffIter 1 ((D.numberOfDirections - 2) + 1) f = 0 := by
      rw [hfzero]
      exact backwardDiffIter_zero_local 1 _
    obtain ⟨P, hP⟩ := exists_circlePolynomial_of_difference
      (d := D.numberOfDirections - 2) f hdiff
    exact ⟨P, fun n ↦ by
      simpa [f, summand, e, lineRestriction, linePhi] using hP n⟩
  · have hmpos := D.number_pos
    have hm2 : 2 ≤ D.numberOfDirections := by omega
    have hline := congrArg (fun g : Plane → Torus ↦ lineRestriction g x e) hplane
    rw [lineRestriction_backwardDiffIter_local] at hline
    have hdiff : backwardDiffIter 1 ((D.numberOfDirections - 2) + 1) f = 0 := by
      change backwardDiffIter 1 ((D.numberOfDirections - 2) + 1)
        (lineRestriction (summand j) x e) = 0
      have hcount : (D.numberOfDirections - 2) + 1 =
          D.numberOfDirections - 1 := by omega
      rw [hcount]
      exact hline
    obtain ⟨P, hP⟩ := exists_circlePolynomial_of_difference
      (d := D.numberOfDirections - 2) f hdiff
    exact ⟨P, fun n ↦ by
      simpa [f, summand, e, lineRestriction, linePhi] using hP n⟩

/-- Suprema of two distinct restricted error functions sum to at most one. -/
theorem linePhi_pair_sup_le_one
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) {i j : Fin D.numberOfDirections} (hij : i ≠ j) :
    sSup (Set.range (linePhi D (weakSliceVector F ell D.direction) x i)) +
      sSup (Set.range (linePhi D (weakSliceVector F ell D.direction) x j)) ≤ 1 := by
  obtain ⟨a, b, he⟩ := weakSliceVector_pair_representation D hij
  let e := weakSliceVector F ell D.direction
  let pi := (weakQ F ell : ℤ) • D.direction i
  let pj := (weakQ F ell : ℤ) • D.direction j
  have hpair (n₁ n₂ : ℤ) :
      linePhi D e x i n₁ + linePhi D e x j n₂ ≤ 1 := by
    let y := x + n₁ • e + (a * (n₂ - n₁)) • pi
    have hyi : D.phi i y = linePhi D e x i n₁ := by
      have hp := (D.phi_periodic i).zsmul (a * (n₂ - n₁))
      change D.phi i ((x + n₁ • e) + (a * (n₂ - n₁)) • pi) =
        D.phi i (x + n₁ • e)
      simpa [pi, weakQ] using hp (x + n₁ • e)
    have hyeq : y = x + n₂ • e + (-b * (n₂ - n₁)) • pj := by
      dsimp [y]
      dsimp [e, pi, pj] at he ⊢
      rw [he]
      module
    have hyj : D.phi j y = linePhi D e x j n₂ := by
      have hp := (D.phi_periodic j).zsmul (-b * (n₂ - n₁))
      rw [hyeq]
      change D.phi j ((x + n₂ • e) + (-b * (n₂ - n₁)) • pj) =
        D.phi j (x + n₂ • e)
      simpa [pj, weakQ] using hp (x + n₂ • e)
    calc
      linePhi D e x i n₁ + linePhi D e x j n₂ =
          D.phi i y + D.phi j y := by rw [hyi, hyj]
      _ = ∑ k ∈ ({i, j} : Finset (Fin D.numberOfDirections)), D.phi k y := by
        simp [hij]
      _ ≤ ∑ k, D.phi k y :=
        Finset.sum_le_univ_sum_of_nonneg fun k ↦ D.phi_nonneg k y
      _ ≤ 1 := by simpa using D.sum_phi_le y
  have hrangei : (Set.range (linePhi D e x i)).Nonempty := Set.range_nonempty _
  have hrangej : (Set.range (linePhi D e x j)).Nonempty := Set.range_nonempty _
  have hsupj (n : ℤ) :
      sSup (Set.range (linePhi D e x j)) ≤ 1 - linePhi D e x i n := by
    apply csSup_le hrangej
    intro y hy
    obtain ⟨m, rfl⟩ := hy
    linarith [hpair n m]
  have hsupi :
      sSup (Set.range (linePhi D e x i)) ≤
        1 - sSup (Set.range (linePhi D e x j)) := by
    apply csSup_le hrangei
    intro y hy
    obtain ⟨n, rfl⟩ := hy
    linarith [hsupj n]
  dsimp [e] at hsupi ⊢
  linarith

private theorem mem_generatedPair_iff_exists_zsmul_add_zsmul
    (u v p : Plane) (hp : p ∈ generatedPair u v) :
    ∃ s t : ℤ, p = s • u + t • v := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
  | zero => exact ⟨0, 0, by simp⟩
  | add p r _hp _hr ihp ihr =>
      obtain ⟨sp, tp, hp⟩ := ihp
      obtain ⟨sr, tr, hr⟩ := ihr
      refine ⟨sp + sr, tp + tr, ?_⟩
      rw [hp, hr]
      module
  | neg p _hp ihp =>
      obtain ⟨s, t, hp⟩ := ihp
      refine ⟨-s, -t, ?_⟩
      rw [hp]
      module

private theorem weakSecondGenerator_pair_representation
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (j : Fin D.numberOfDirections) :
    ∃ a b : ℤ,
      (((weakQ F ell * weakN D.direction * weakM D.direction : ℕ) : ℤ) •
          D.direction ⟨0, D.number_pos⟩) =
        a • ((weakQ F ell : ℤ) • D.direction j) +
          b • weakSliceVector F ell D.direction := by
  have hMdivNat :
      Int.natAbs (wedge (weakAvoidance D.direction) (D.direction j)) ∣
        weakM D.direction := by
    change Int.natAbs (wedge (avoidanceVector D.direction) (D.direction j)) ∣
      directionAvoidanceLCM D.direction
    unfold directionAvoidanceLCM
    apply Finset.dvd_lcm
    exact Finset.mem_univ j
  have hMdivInt : wedge (weakAvoidance D.direction) (D.direction j) ∣
      (weakM D.direction : ℤ) := by
    rw [← Int.natAbs_dvd]
    exact_mod_cast hMdivNat
  obtain ⟨r, hr⟩ := hMdivInt
  refine ⟨(weakN D.direction : ℤ) * r *
      wedge (weakAvoidance D.direction) (D.direction ⟨0, D.number_pos⟩),
    r * wedge (D.direction ⟨0, D.number_pos⟩) (D.direction j), ?_⟩
  have hid := cramer_identity (weakAvoidance D.direction) (D.direction j)
    (D.direction ⟨0, D.number_pos⟩)
  have hr' : (weakM D.direction : ℤ) =
      wedge (weakAvoidance D.direction) (D.direction j) * r := hr
  calc
    (((weakQ F ell * weakN D.direction * weakM D.direction : ℕ) : ℤ) •
        D.direction ⟨0, D.number_pos⟩) =
        ((weakQ F ell : ℤ) * (weakN D.direction : ℤ) * r) •
          (wedge (weakAvoidance D.direction) (D.direction j) •
            D.direction ⟨0, D.number_pos⟩) := by
      simp only [Nat.cast_mul]
      rw [hr']
      module
    _ = ((weakQ F ell : ℤ) * (weakN D.direction : ℤ) * r) •
        (wedge (D.direction ⟨0, D.number_pos⟩) (D.direction j) •
            weakAvoidance D.direction +
          wedge (weakAvoidance D.direction) (D.direction ⟨0, D.number_pos⟩) •
            D.direction j) := by rw [hid]
    _ = ((weakN D.direction : ℤ) * r *
          wedge (weakAvoidance D.direction) (D.direction ⟨0, D.number_pos⟩)) •
            ((weakQ F ell : ℤ) • D.direction j) +
        (r * wedge (D.direction ⟨0, D.number_pos⟩) (D.direction j)) •
            weakSliceVector F ell D.direction := by
      rw [weakSliceVector]
      simp only [Nat.cast_mul]
      module

private theorem phi_on_weakCoset
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x y : Plane)
    (hy : y ∈ addCoset (weakLattice F ell D.direction D.number_pos) x)
    (j : Fin D.numberOfDirections) :
    ∃ s t b : ℤ,
      y = x + s • weakSliceVector F ell D.direction +
        t • (((weakQ F ell * weakN D.direction * weakM D.direction : ℕ) : ℤ) •
          D.direction ⟨0, D.number_pos⟩) ∧
      D.phi j y =
        linePhi D (weakSliceVector F ell D.direction) x j (s + b * t) := by
  obtain ⟨s, t, hrep⟩ := mem_generatedPair_iff_exists_zsmul_add_zsmul
    _ _ _ hy
  obtain ⟨a, b, hg⟩ := weakSecondGenerator_pair_representation D j
  have hyrep : y = x + s • weakSliceVector F ell D.direction +
      t • (((weakQ F ell * weakN D.direction * weakM D.direction : ℕ) : ℤ) •
        D.direction ⟨0, D.number_pos⟩) := by
    change y - x = _ at hrep
    calc
      y = x + (y - x) := by abel
      _ = _ := by rw [hrep]; abel
  refine ⟨s, t, b, hyrep, ?_⟩
  have hp := (D.phi_periodic j).zsmul (t * a)
  rw [hyrep, hg]
  change D.phi j
      (x + s • weakSliceVector F ell D.direction +
        t • (a • ((weakQ F ell : ℤ) • D.direction j) +
          b • weakSliceVector F ell D.direction)) = _
  have hpoint :
      x + s • weakSliceVector F ell D.direction +
          t • (a • ((weakQ F ell : ℤ) • D.direction j) +
            b • weakSliceVector F ell D.direction) =
        (x + (s + b * t) • weakSliceVector F ell D.direction) +
          (t * a) • ((weakQ F ell : ℤ) • D.direction j) := by
    module
  rw [hpoint]
  simpa [weakQ, linePhi] using hp
    (x + (s + b * t) • weakSliceVector F ell D.direction)

private theorem phi_at_weakCoordinates
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) (s : ℤ) (j : Fin D.numberOfDirections) :
    ∃ b : ℤ, ∀ t : ℤ,
      D.phi j
          (x + s • weakSliceVector F ell D.direction +
            t • (((weakQ F ell * weakN D.direction * weakM D.direction : ℕ) : ℤ) •
              D.direction ⟨0, D.number_pos⟩)) =
        linePhi D (weakSliceVector F ell D.direction) x j (s + b * t) := by
  obtain ⟨a, b, hg⟩ := weakSecondGenerator_pair_representation D j
  refine ⟨b, fun t ↦ ?_⟩
  have hp := (D.phi_periodic j).zsmul (t * a)
  rw [hg]
  have hpoint :
      x + s • weakSliceVector F ell D.direction +
          t • (a • ((weakQ F ell : ℤ) • D.direction j) +
            b • weakSliceVector F ell D.direction) =
        (x + (s + b * t) • weakSliceVector F ell D.direction) +
          (t * a) • ((weakQ F ell : ℤ) • D.direction j) := by
    module
  rw [hpoint]
  simpa [weakQ, linePhi] using hp
    (x + (s + b * t) • weakSliceVector F ell D.direction)

private theorem setPeriodicOn_weakLattice_of_scalarPeriodic
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E) :
    SetPeriodicOn (weakLattice F ell D.direction D.number_pos) E := by
  intro p hp x
  have hpScalar := weakLattice_le_scalar D hell hp
  obtain ⟨z, hz⟩ := hpScalar
  rw [← hz]
  change x + (ell : ℤ) • z ∈ E ↔ x ∈ E
  exact hE x z

private theorem addCoset_add_iff
    (H : AddSubgroup Plane) {p x y : Plane} (hp : p ∈ H) :
    y + p ∈ addCoset H x ↔ y ∈ addCoset H x := by
  change y + p - x ∈ H ↔ y - x ∈ H
  constructor
  · intro h
    have := H.sub_mem h hp
    convert this using 1
    abel
  · intro h
    have := H.add_mem h hp
    convert this using 1
    abel

private theorem setIndicator_eq_iff_membership_local
    (S : Set Plane) (u v : Plane) :
    setIndicator S u = setIndicator S v ↔ (u ∈ S ↔ v ∈ S) := by
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
    simp [setIndicator, hu, hv]

private theorem linePhi_bddAbove
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (e x : Plane) (j : Fin D.numberOfDirections) :
    BddAbove (Set.range (linePhi D e x j)) := by
  refine ⟨1, ?_⟩
  rintro y ⟨n, rfl⟩
  change D.phi j (x + n • e) ≤ 1
  simpa using D.phi_le_level j (x + n • e)

private theorem linePhi_periodic_of_sup_le_half
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) (j : Fin D.numberOfDirections)
    (hsup : sSup (Set.range
      (linePhi D (weakSliceVector F ell D.direction) x j)) ≤ 1 / 2) :
    Function.Periodic
      (linePhi D (weakSliceVector F ell D.direction) x j)
      (weakRigidityPeriod D.numberOfDirections : ℤ) := by
  obtain ⟨P, hP⟩ := linePhi_circlePolynomial D x j
  have hhalf : P.HasHalfCircleLifts := by
    intro n
    refine ⟨linePhi D (weakSliceVector F ell D.direction) x j n, ?_, hP n⟩
    constructor
    · exact D.phi_nonneg j _
    · exact (le_csSup (linePhi_bddAbove D _ _ j) ⟨n, rfl⟩).trans hsup
  obtain ⟨q, hq, hqbound, hqperiod⟩ := periodic_of_halfCircle P hhalf
  have hU := periodic_universalRigidityPeriod P q hqperiod hq hqbound
  obtain ⟨r, hr⟩ := universalRigidityPeriod_dvd_weak
    (show D.numberOfDirections - 2 ≤ D.numberOfDirections by omega)
  have hPperiod : P.PeriodicWith (weakRigidityPeriod D.numberOfDirections) := by
    rw [hr]
    simpa [CirclePolynomial.PeriodicWith, Nat.cast_mul, nsmul_eq_mul, mul_comm]
      using hU.nsmul r
  intro n
  have hcoe :
      ((linePhi D (weakSliceVector F ell D.direction) x j
          (n + (weakRigidityPeriod D.numberOfDirections : ℤ)) : ℝ) : Torus) =
        (linePhi D (weakSliceVector F ell D.direction) x j n : Torus) := by
    calc
      _ = P (n + (weakRigidityPeriod D.numberOfDirections : ℤ)) :=
        (hP _).symm
      _ = P n := hPperiod n
      _ = _ := hP n
  refine (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (a := (0 : ℝ)) (p := (1 : ℝ)) ?_ ?_).1 hcoe
  · constructor
    · exact D.phi_nonneg j _
    · have hle : linePhi D (weakSliceVector F ell D.direction) x j
          (n + (weakRigidityPeriod D.numberOfDirections : ℤ)) ≤
            sSup (Set.range
              (linePhi D (weakSliceVector F ell D.direction) x j)) :=
          le_csSup (linePhi_bddAbove D _ _ j)
            ⟨n + (weakRigidityPeriod D.numberOfDirections : ℤ), rfl⟩
      linarith
  · constructor
    · exact D.phi_nonneg j _
    · have hle : linePhi D (weakSliceVector F ell D.direction) x j n ≤
          sSup (Set.range
            (linePhi D (weakSliceVector F ell D.direction) x j)) :=
          le_csSup (linePhi_bddAbove D _ _ j) ⟨n, rfl⟩
      linarith

private theorem linePhi_real_periodic_of_circle_periodic_of_sup_lt_one
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane) (j : Fin D.numberOfDirections) (Q : ℕ)
    (hcircle : Function.Periodic
      (fun n ↦ (linePhi D (weakSliceVector F ell D.direction) x j n : Torus))
      (Q : ℤ))
    (hsup : sSup (Set.range
      (linePhi D (weakSliceVector F ell D.direction) x j)) < 1) :
    Function.Periodic
      (linePhi D (weakSliceVector F ell D.direction) x j) (Q : ℤ) := by
  intro n
  refine (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (a := (0 : ℝ)) (p := (1 : ℝ)) ?_ ?_).1 (hcircle n)
  · constructor
    · exact D.phi_nonneg j _
    · have hle : linePhi D (weakSliceVector F ell D.direction) x j
          (n + (Q : ℤ)) ≤ sSup (Set.range
            (linePhi D (weakSliceVector F ell D.direction) x j)) :=
          le_csSup (linePhi_bddAbove D
            (weakSliceVector F ell D.direction) x j) ⟨n + (Q : ℤ), rfl⟩
      linarith
  · constructor
    · exact D.phi_nonneg j _
    · have hle : linePhi D (weakSliceVector F ell D.direction) x j n ≤
          sSup (Set.range
            (linePhi D (weakSliceVector F ell D.direction) x j)) :=
          le_csSup (linePhi_bddAbove D
            (weakSliceVector F ell D.direction) x j) ⟨n, rfl⟩
      linarith

private theorem all_linePhi_periodic_of_sup_lt_one
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (x : Plane)
    (hall : ∀ j, sSup (Set.range
      (linePhi D (weakSliceVector F ell D.direction) x j)) < 1) :
    ∀ j, Function.Periodic
      (linePhi D (weakSliceVector F ell D.direction) x j)
      (weakRigidityPeriod D.numberOfDirections : ℤ) := by
  classical
  let high : Prop := ∃ j : Fin D.numberOfDirections,
    1 / 2 < sSup (Set.range
      (linePhi D (weakSliceVector F ell D.direction) x j))
  let j₀ : Fin D.numberOfDirections :=
    if h : high then Classical.choose h else ⟨0, D.number_pos⟩
  have hhalf (k : Fin D.numberOfDirections) (hk : k ≠ j₀) :
      sSup (Set.range
        (linePhi D (weakSliceVector F ell D.direction) x k)) ≤ 1 / 2 := by
    by_cases hh : high
    · have hj₀ : 1 / 2 < sSup (Set.range
          (linePhi D (weakSliceVector F ell D.direction) x j₀)) := by
        simpa [j₀, hh] using Classical.choose_spec hh
      have hpairs := linePhi_pair_sup_le_one D x hk
      linarith
    · exact le_of_not_gt fun hkhigh ↦ hh ⟨k, hkhigh⟩
  have hother (k : Fin D.numberOfDirections) (hk : k ≠ j₀) :
      Function.Periodic
        (linePhi D (weakSliceVector F ell D.direction) x k)
        (weakRigidityPeriod D.numberOfDirections : ℤ) :=
    linePhi_periodic_of_sup_le_half D x k (hhalf k hk)
  have hj₀Circle : Function.Periodic
      (fun n ↦ (linePhi D (weakSliceVector F ell D.direction) x j₀ n : Torus))
      (weakRigidityPeriod D.numberOfDirections : ℤ) := by
    intro n
    have hsumShift := linePhi_sum_mod_one D
      (weakSliceVector F ell D.direction) x
      (n + (weakRigidityPeriod D.numberOfDirections : ℤ))
    have hsumBase := linePhi_sum_mod_one D
      (weakSliceVector F ell D.direction) x n
    have hrest :
        (∑ k ∈ (Finset.univ.erase j₀),
            ((linePhi D (weakSliceVector F ell D.direction) x k
              (n + (weakRigidityPeriod D.numberOfDirections : ℤ)) : ℝ) : Torus)) =
          ∑ k ∈ (Finset.univ.erase j₀),
            (linePhi D (weakSliceVector F ell D.direction) x k n : Torus) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkj₀ : k ≠ j₀ := Finset.ne_of_mem_erase hk
      exact congrArg (fun t : ℝ ↦ (t : Torus)) (hother k hkj₀ n)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀)] at hsumShift
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀)] at hsumBase
    rw [hrest] at hsumShift
    exact add_left_cancel (hsumShift.trans hsumBase.symm)
  have hj₀Real := linePhi_real_periodic_of_circle_periodic_of_sup_lt_one
    D x j₀ (weakRigidityPeriod D.numberOfDirections) hj₀Circle (hall j₀)
  intro k
  by_cases hk : k = j₀
  · simpa [hk] using hj₀Real
  · exact hother k hk

private theorem setIndicator_eq_of_target_and_phi_eq
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    {u v : Plane} (hE : u ∈ E ↔ v ∈ E)
    (hphi : ∀ j, D.phi j u = D.phi j v) :
    setIndicator A u = setIndicator A v := by
  have hindicatorE : setIndicator E u = setIndicator E v :=
    (setIndicator_eq_iff_membership_local E u v).2 hE
  have hsum : (∑ j, D.phi j u) = ∑ j, D.phi j v := by
    apply Finset.sum_congr rfl
    intro j _
    exact hphi j
  have hcast : (((setIndicator A u : ℤ) : ℝ)) =
      ((setIndicator A v : ℤ) : ℝ) := by
    rw [D.decomposition u, D.decomposition v, hindicatorE, hsum]
  exact_mod_cast hcast

private theorem coset_supremumOne_periodic
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (x : Plane) (j : Fin D.numberOfDirections)
    (hsup : sSup (Set.range
      (linePhi D (weakSliceVector F ell D.direction) x j)) = 1) :
    ∀ y,
      y + (((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) •
          D.direction j) ∈
          A ∩ addCoset (weakLattice F ell D.direction D.number_pos) x ↔
        y ∈ A ∩ addCoset
          (weakLattice F ell D.direction D.number_pos) x := by
  let Λ := weakLattice F ell D.direction D.number_pos
  let period := (((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) •
    D.direction j)
  have hperiodMem : period ∈ Λ := weak_period_mem_lattice D hell j
  have hcoset (y : Plane) :
      y + period ∈ addCoset Λ x ↔ y ∈ addCoset Λ x :=
    addCoset_add_iff Λ hperiodMem
  have htarget : SetPeriodicOn Λ E :=
    setPeriodicOn_weakLattice_of_scalarPeriodic D hell hE
  obtain ⟨W⟩ := exists_weakArithmeticData D hell
  have hfactor : ell * weakMultiplier F ell D.direction =
      weakRigidityPeriod D.numberOfDirections * weakM D.direction ^ 2 *
        weakN D.direction * weakQ F ell := by
    rw [← W.multiplier_eq]
    exact W.exact_scalar_factor
  have hperiodEq : period =
      (((weakRigidityPeriod D.numberOfDirections * weakM D.direction ^ 2 *
          weakN D.direction : ℕ) : ℤ) •
        ((weakQ F ell : ℤ) • D.direction j)) := by
    calc
      period = ((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) •
          D.direction j := rfl
      _ = ((weakRigidityPeriod D.numberOfDirections * weakM D.direction ^ 2 *
          weakN D.direction * weakQ F ell : ℕ) : ℤ) • D.direction j := by
        rw [hfactor]
      _ = (((weakRigidityPeriod D.numberOfDirections * weakM D.direction ^ 2 *
          weakN D.direction : ℕ) : ℤ) •
        ((weakQ F ell : ℤ) • D.direction j)) := by
        simp only [Nat.cast_mul]
        module
  have hphiPeriod : Function.Periodic (D.phi j) period := by
    have hbase : Function.Periodic (D.phi j)
        ((weakQ F ell : ℤ) • D.direction j) := by
      simpa [weakQ] using D.phi_periodic j
    rw [hperiodEq]
    exact hbase.zsmul _
  have hother (k : Fin D.numberOfDirections) (hkj : k ≠ j)
      (z : Plane) (hz : z ∈ addCoset Λ x) : D.phi k z = 0 := by
    have hjk : j ≠ k := Ne.symm hkj
    have hpairs := linePhi_pair_sup_le_one D x hjk
    have hsupk : sSup (Set.range
        (linePhi D (weakSliceVector F ell D.direction) x k)) ≤ 0 := by
      rw [hsup] at hpairs
      linarith
    obtain ⟨s, t, b, _hzrep, hline⟩ := phi_on_weakCoset D x z hz k
    have hle : linePhi D (weakSliceVector F ell D.direction) x k
        (s + b * t) ≤ sSup (Set.range
          (linePhi D (weakSliceVector F ell D.direction) x k)) := by
      apply le_csSup (linePhi_bddAbove D _ _ k)
      exact ⟨s + b * t, rfl⟩
    have hnonneg := D.phi_nonneg k z
    rw [hline] at hnonneg
    rw [hline]
    linarith
  intro y
  constructor
  · rintro ⟨hyA, hycos⟩
    have hycos' : y ∈ addCoset Λ x := (hcoset y).mp hycos
    refine ⟨?_, hycos'⟩
    have hindicator : setIndicator A (y + period) = setIndicator A y := by
      apply setIndicator_eq_of_target_and_phi_eq D
      · exact htarget period hperiodMem y
      · intro k
        by_cases hkj : k = j
        · subst k
          exact hphiPeriod y
        · rw [hother k hkj (y + period) hycos,
            hother k hkj y hycos']
    exact ((setIndicator_eq_iff_membership_local A (y + period) y).1
      hindicator).mp hyA
  · rintro ⟨hyA, hycos⟩
    refine ⟨?_, (hcoset y).mpr hycos⟩
    have hindicator : setIndicator A (y + period) = setIndicator A y := by
      apply setIndicator_eq_of_target_and_phi_eq D
      · exact htarget period hperiodMem y
      · intro k
        by_cases hkj : k = j
        · subst k
          exact hphiPeriod y
        · rw [hother k hkj (y + period) ((hcoset y).mpr hycos),
            hother k hkj y hycos]
    exact ((setIndicator_eq_iff_membership_local A (y + period) y).1
      hindicator).mpr hyA

private theorem coset_allSuprema_lt_one_periodic
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E)
    (x : Plane)
    (hall : ∀ j, sSup (Set.range
      (linePhi D (weakSliceVector F ell D.direction) x j)) < 1) :
    ∀ y,
      y + (((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) •
          D.direction ⟨0, D.number_pos⟩) ∈
          A ∩ addCoset (weakLattice F ell D.direction D.number_pos) x ↔
        y ∈ A ∩ addCoset
          (weakLattice F ell D.direction D.number_pos) x := by
  let Λ := weakLattice F ell D.direction D.number_pos
  let e := weakSliceVector F ell D.direction
  let g := (((weakQ F ell * weakN D.direction * weakM D.direction : ℕ) : ℤ) •
    D.direction ⟨0, D.number_pos⟩)
  let period := (((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) •
    D.direction ⟨0, D.number_pos⟩)
  let z : ℤ := ((weakM D.direction * weakRigidityPeriod D.numberOfDirections : ℕ) : ℤ)
  have hperiodMem : period ∈ Λ :=
    weak_period_mem_lattice D hell ⟨0, D.number_pos⟩
  have hcoset (y : Plane) :
      y + period ∈ addCoset Λ x ↔ y ∈ addCoset Λ x :=
    addCoset_add_iff Λ hperiodMem
  have htarget : SetPeriodicOn Λ E :=
    setPeriodicOn_weakLattice_of_scalarPeriodic D hell hE
  obtain ⟨W⟩ := exists_weakArithmeticData D hell
  have hfactor : ell * weakMultiplier F ell D.direction =
      weakRigidityPeriod D.numberOfDirections * weakM D.direction ^ 2 *
        weakN D.direction * weakQ F ell := by
    rw [← W.multiplier_eq]
    exact W.exact_scalar_factor
  have hperiodEq : period = z • g := by
    calc
      period = ((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) •
          D.direction ⟨0, D.number_pos⟩ := rfl
      _ = ((weakRigidityPeriod D.numberOfDirections * weakM D.direction ^ 2 *
          weakN D.direction * weakQ F ell : ℕ) : ℤ) •
            D.direction ⟨0, D.number_pos⟩ := by rw [hfactor]
      _ = z • g := by
        dsimp [z, g]
        rw [smul_smul]
        congr 1
        norm_cast
        ring_nf
  have hlinePeriod := all_linePhi_periodic_of_sup_lt_one D x hall
  have hphi (y : Plane) (hy : y ∈ addCoset Λ x)
      (k : Fin D.numberOfDirections) : D.phi k (y + period) = D.phi k y := by
    obtain ⟨s, t, hrep⟩ := mem_generatedPair_iff_exists_zsmul_add_zsmul
      _ _ _ hy
    have hyrep : y = x + s • e + t • g := by
      change y - x = _ at hrep
      calc
        y = x + (y - x) := by abel
        _ = _ := by rw [hrep]; abel
    obtain ⟨b, hcoord⟩ := phi_at_weakCoordinates D x s k
    have hcoordBase : D.phi k y =
        linePhi D e x k (s + b * t) := by
      rw [hyrep]
      simpa [e, g] using hcoord t
    have hyshift : y + period = x + s • e + (t + z) • g := by
      rw [hyrep, hperiodEq]
      module
    have hcoordShift : D.phi k (y + period) =
        linePhi D e x k (s + b * (t + z)) := by
      rw [hyshift]
      simpa [e, g] using hcoord (t + z)
    have hp := (hlinePeriod k).zsmul (b * (weakM D.direction : ℤ))
    have hline : linePhi D e x k (s + b * (t + z)) =
        linePhi D e x k (s + b * t) := by
      have hp' := hp (s + b * t)
      dsimp [e, z] at hp' ⊢
      convert hp' using 1
      ring_nf
    exact hcoordShift.trans (hline.trans hcoordBase.symm)
  intro y
  constructor
  · rintro ⟨hyA, hycos⟩
    have hycos' : y ∈ addCoset Λ x := (hcoset y).mp hycos
    refine ⟨?_, hycos'⟩
    have hindicator : setIndicator A (y + period) = setIndicator A y := by
      apply setIndicator_eq_of_target_and_phi_eq D
      · exact htarget period hperiodMem y
      · exact fun k ↦ hphi y hycos' k
    exact ((setIndicator_eq_iff_membership_local A (y + period) y).1
      hindicator).mp hyA
  · rintro ⟨hyA, hycos⟩
    refine ⟨?_, (hcoset y).mpr hycos⟩
    have hindicator : setIndicator A (y + period) = setIndicator A y := by
      apply setIndicator_eq_of_target_and_phi_eq D
      · exact htarget period hperiodMem y
      · exact fun k ↦ hphi y hycos k
    exact ((setIndicator_eq_iff_membership_local A (y + period) y).1
      hindicator).mpr hyA

/-- On every weak-lattice coset, one advertised direction is a period of the tiling set. -/
theorem coset_one_dimensional_periodicity
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (D : GroupedStructureDecomposition F A E ell 1)
    (hell : 0 < ell) (hE : SetScalarPeriodic ell E) :
    CosetwisePeriodic A (weakLattice F ell D.direction D.number_pos)
      (fun j ↦ ((ell * weakMultiplier F ell D.direction : ℕ) : ℤ) •
        D.direction j) := by
  intro x
  by_cases hsup : ∃ j : Fin D.numberOfDirections,
      sSup (Set.range
        (linePhi D (weakSliceVector F ell D.direction) x j)) = 1
  · obtain ⟨j, hj⟩ := hsup
    exact ⟨j, coset_supremumOne_periodic D hell hE x j hj⟩
  · have hall : ∀ j : Fin D.numberOfDirections,
        sSup (Set.range
          (linePhi D (weakSliceVector F ell D.direction) x j)) < 1 := by
      intro j
      have hle : sSup (Set.range
          (linePhi D (weakSliceVector F ell D.direction) x j)) ≤ 1 := by
        apply csSup_le (Set.range_nonempty _)
        rintro y ⟨n, rfl⟩
        change D.phi j (x + n • weakSliceVector F ell D.direction) ≤ 1
        simpa using D.phi_le_level j _
      exact lt_of_le_of_ne hle (fun heq ↦ hsup ⟨j, heq⟩)
    exact ⟨⟨0, D.number_pos⟩, coset_allSuprema_lt_one_periodic
      D hell hE x hall⟩

private theorem canonicalDirection_isPrimitive
    {f : Plane} (hf : f ≠ 0) : IsPrimitive (canonicalDirection f) := by
  have hp := (primitive_decomposition hf).2
  constructor
  · exact canonicalDirection_ne_zero hf
  · rw [canonicalDirection]
    split_ifs
    · have hcontent := vectorContent_zsmul (-1 : ℤ) (primitivePart f)
      simpa [hp.2] using hcontent
    · exact hp.2

private theorem groupedTileDirections_fiber_spec
    {F : Finset Plane} (_hzero : 0 ∈ F) (_hcard : 1 < F.card)
    (j : Fin (groupedDirectionCount F)) :
    let v := pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl j)
    (∀ f ∈ F.erase 0, canonicalDirection f = v →
      ∃ z : ℤ, z ≠ 0 ∧ groupedTileDirections F j = z • f) ∧
    l1Norm (groupedTileDirections F j) ≤
      ∏ f ∈ (F.erase 0).filter (fun f ↦ canonicalDirection f = v), l1Norm f ∧
    euclideanNorm (groupedTileDirections F j) ≤
      ∏ f ∈ (F.erase 0).filter (fun f ↦ canonicalDirection f = v),
        euclideanNorm f := by
  classical
  let v := pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl j)
  let C := (F.erase 0).filter fun f ↦ canonicalDirection f = v
  have hkey := groupedTileDirection_key_mem (F := F) j
  obtain ⟨f₀, hf₀erase, hf₀key⟩ := Finset.mem_image.mp hkey
  have hf₀ne : f₀ ≠ 0 := Finset.ne_of_mem_erase hf₀erase
  have hf₀v : canonicalDirection f₀ = v := by
    apply planeToPair_injective
    exact hf₀key
  have hCnonempty : C.Nonempty := ⟨f₀, Finset.mem_filter.mpr ⟨hf₀erase, hf₀v⟩⟩
  have hCne (f : Plane) (hf : f ∈ C) : f ≠ 0 :=
    Finset.ne_of_mem_erase (Finset.mem_filter.mp hf).1
  have hCcomm (u : Plane) (hu : u ∈ C) (w : Plane) (hw : w ∈ C) :
      Commensurable u w := by
    apply (canonicalDirection_eq_iff_commensurable (hCne u hu) (hCne w hw)).1
    exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hw).2.symm
  obtain ⟨common, hcommonNe, hcommonMultiple, hcommonL1, hcommonEu⟩ :=
    exists_commonMultiple_of_pairwise_commensurable hCnonempty hCne hCcomm
  have hcommonComm : Commensurable common f₀ := by
    obtain ⟨z, hz, hcommon⟩ := hcommonMultiple f₀
      (Finset.mem_filter.mpr ⟨hf₀erase, hf₀v⟩)
    exact ⟨1, z, one_ne_zero, hz, by simp [hcommon]⟩
  have hcommonCanon : canonicalDirection common = v := by
    calc
      canonicalDirection common = canonicalDirection f₀ :=
        (canonicalDirection_eq_iff_commensurable hcommonNe hf₀ne).2 hcommonComm
      _ = v := hf₀v
  have hvPrimitive : IsPrimitive v := by
    rw [← hf₀v]
    exact canonicalDirection_isPrimitive hf₀ne
  obtain ⟨a, ha, hcommonDecomp⟩ :=
    tile_integer_multiple_of_canonicalDirection hcommonNe
  rw [hcommonCanon] at hcommonDecomp
  have hcontentCommon : vectorContent common = Int.natAbs a := by
    have hc := congrArg vectorContent hcommonDecomp
    rw [vectorContent_zsmul, hvPrimitive.2, mul_one] at hc
    exact hc
  have hscaleDvd : groupedDirectionScale F v ∣ vectorContent common := by
    unfold groupedDirectionScale
    apply Finset.lcm_dvd
    intro f hf
    obtain ⟨z, _hz, hcommon⟩ := hcommonMultiple f hf
    rw [hcommon, vectorContent_zsmul]
    exact dvd_mul_left _ _
  have hscaleLe : groupedDirectionScale F v ≤ vectorContent common := by
    apply Nat.le_of_dvd (vectorContent_pos hcommonNe)
    exact hscaleDvd
  have hmultiple (f : Plane) (hf : f ∈ F.erase 0)
      (hfv : canonicalDirection f = v) :
      ∃ z : ℤ, z ≠ 0 ∧ groupedTileDirections F j = z • f := by
    have hfne : f ≠ 0 := Finset.ne_of_mem_erase hf
    have hdiv : vectorContent f ∣ groupedDirectionScale F v := by
      apply Finset.dvd_lcm
      exact Finset.mem_filter.mpr ⟨hf, hfv⟩
    obtain ⟨c, hc⟩ := hdiv
    have hcne : c ≠ 0 := by
      intro hc0
      have hspos := groupedDirectionScale_pos_of_mem (F := F)
        (groupedTileDirection_key_mem j)
      rw [hc, hc0, Nat.mul_zero] at hspos
      omega
    have hdecomp : (vectorContent f : ℤ) • primitivePart f = f :=
      (primitive_decomposition hfne).1
    have hgroup : groupedTileDirections F j =
        (groupedDirectionScale F v : ℤ) • v := by rfl
    by_cases horient : (primitivePart f) 0 < 0 ∨
        ((primitivePart f) 0 = 0 ∧ (primitivePart f) 1 < 0)
    · refine ⟨-(c : ℤ), neg_ne_zero.mpr (by exact_mod_cast hcne), ?_⟩
      calc
          groupedTileDirections F j =
              ((vectorContent f * c : ℕ) : ℤ) • (-primitivePart f) := by
            rw [hgroup, hc, ← hfv, canonicalDirection, if_pos horient]
          _ = -(c : ℤ) • ((vectorContent f : ℤ) • primitivePart f) := by
            norm_cast
            module
          _ = -(c : ℤ) • f := by rw [hdecomp]
    · refine ⟨(c : ℤ), (by exact_mod_cast hcne), ?_⟩
      calc
        groupedTileDirections F j =
            ((vectorContent f * c : ℕ) : ℤ) • primitivePart f := by
          rw [hgroup, hc, ← hfv, canonicalDirection, if_neg horient]
        _ = (c : ℤ) • ((vectorContent f : ℤ) • primitivePart f) := by
          norm_cast
          module
        _ = (c : ℤ) • f := by rw [hdecomp]
  refine ⟨hmultiple, ?_, ?_⟩
  · calc
      l1Norm (groupedTileDirections F j) =
          groupedDirectionScale F v * l1Norm v := by
        rw [show groupedTileDirections F j =
          (groupedDirectionScale F v : ℤ) • v by rfl, l1Norm_zsmul]
        simp
      _ ≤ vectorContent common * l1Norm v := Nat.mul_le_mul_right _ hscaleLe
      _ = Int.natAbs a * l1Norm v := by rw [hcontentCommon]
      _ = l1Norm common := by rw [hcommonDecomp, l1Norm_zsmul]
      _ ≤ ∏ f ∈ C, l1Norm f := hcommonL1
  · calc
      euclideanNorm (groupedTileDirections F j) =
          groupedDirectionScale F v * euclideanNorm v := by
        rw [show groupedTileDirections F j =
          (groupedDirectionScale F v : ℤ) • v by rfl, euclideanNorm_zsmul]
        simp
      _ ≤ vectorContent common * euclideanNorm v := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hscaleLe) (norm_nonneg _)
      _ = (Int.natAbs a : ℝ) * euclideanNorm v := by rw [hcontentCommon]
      _ = euclideanNorm common := by rw [hcommonDecomp, euclideanNorm_zsmul]
      _ ≤ ∏ f ∈ C, euclideanNorm f := hcommonEu

private def canonicalClass (F : Finset Plane) (f : ↑(F.erase 0)) :
    ↑(groupedDirectionPairs F) :=
  ⟨planeToPair (canonicalDirection f),
    Finset.mem_image.mpr ⟨f, f.property, rfl⟩⟩

private def canonicalIndex (F : Finset Plane) (f : ↑(F.erase 0)) :
    Fin (groupedDirectionCount F) :=
  ((groupedDirectionPairs F).orderIsoOfFin rfl).symm (canonicalClass F f)

private noncomputable def canonicalGroupedPhi
    {F : Finset Plane} {A : Set Plane} {ell : ℕ}
    (S : StructureDecomposition F A ell) :
    Fin (groupedDirectionCount F) → Plane → ℝ :=
  fun j x ↦ ∑ f ∈ Finset.univ.filter
    (fun f : ↑(F.erase 0) ↦ canonicalIndex F f = j), S.phi f x

private theorem canonicalGroupedPhi_sum
    {F : Finset Plane} {A : Set Plane} {ell : ℕ}
    (S : StructureDecomposition F A ell) (x : Plane) :
    (∑ j, canonicalGroupedPhi S j x) = ∑ f, S.phi f x := by
  simpa only [canonicalGroupedPhi] using Finset.sum_fiberwise
    (Finset.univ : Finset ↑(F.erase 0)) (canonicalIndex F) (fun f ↦ S.phi f x)

private theorem canonicalIndex_key
    {F : Finset Plane} (f : ↑(F.erase 0)) :
    (groupedDirectionPairs F).orderEmbOfFin rfl (canonicalIndex F f) =
      planeToPair (canonicalDirection f) := by
  change ((groupedDirectionPairs F).orderIsoOfFin rfl
    (canonicalIndex F f) : ℤ ×ₗ ℤ) = _
  exact congrArg Subtype.val
    ((groupedDirectionPairs F).orderIsoOfFin rfl |>.apply_symm_apply
      (canonicalClass F f))

private theorem canonicalIndex_eq_iff
    {F : Finset Plane} (f : ↑(F.erase 0))
    (j : Fin (groupedDirectionCount F)) :
    canonicalIndex F f = j ↔ canonicalDirection f =
      pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl j) := by
  constructor
  · intro h
    have hkey := canonicalIndex_key f
    rw [h] at hkey
    apply planeToPair_injective
    simpa only [planeToPair_pairToPlane] using hkey.symm
  · intro h
    apply (groupedDirectionPairs F).orderEmbOfFin rfl |>.injective
    rw [canonicalIndex_key, ← planeToPair_pairToPlane
      ((groupedDirectionPairs F).orderEmbOfFin rfl j), h]

private theorem canonical_prod_partition
    {R : Type*} [CommMonoid R]
    {F : Finset Plane} (w : ↑(F.erase 0) → R) :
    (∏ j : Fin (groupedDirectionCount F),
      ∏ f ∈ Finset.univ.filter
        (fun f : ↑(F.erase 0) ↦ canonicalIndex F f = j), w f) = ∏ f, w f := by
  simpa only using Finset.prod_fiberwise
    (Finset.univ : Finset ↑(F.erase 0)) (canonicalIndex F) w

private theorem canonical_fiber_prod_eq
    {R : Type*} [CommMonoid R]
    {F : Finset Plane} (j : Fin (groupedDirectionCount F))
    (w : Plane → R) :
    (∏ f ∈ (F.erase 0).filter (fun f ↦ canonicalDirection f =
      pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl j)), w f) =
      ∏ f ∈ Finset.univ.filter
        (fun f : ↑(F.erase 0) ↦ canonicalIndex F f = j), w f := by
  classical
  let s := Finset.univ.filter
    (fun f : ↑(F.erase 0) ↦ canonicalIndex F f = j)
  have hset : (F.erase 0).filter (fun f ↦ canonicalDirection f =
      pairToPlane ((groupedDirectionPairs F).orderEmbOfFin rfl j)) =
      s.image Subtype.val := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_image,
      Finset.mem_univ, true_and, s]
    constructor
    · rintro ⟨hf, hcanon⟩
      exact ⟨⟨f, hf⟩, (canonicalIndex_eq_iff ⟨f, hf⟩ j).2 hcanon, rfl⟩
    · rintro ⟨f', hf', rfl⟩
      exact ⟨f'.property, (canonicalIndex_eq_iff f' j).1 hf'⟩
  rw [hset, Finset.prod_image]
  intro a _ b _ hab
  exact Subtype.ext hab

private theorem mem_tile_euclideanNorm_le_diameter_local
    {F : Finset Plane} (hzero : 0 ∈ F) {f : Plane} (hf : f ∈ F) :
    euclideanNorm f ≤ euclideanDiameter F := by
  classical
  have hprod : (F ×ˢ F).Nonempty := ⟨(f, 0), by simp [hf, hzero]⟩
  rw [euclideanDiameter, dif_pos hprod]
  have hle := Finset.le_sup'
    (f := fun xy : Plane × Plane ↦ euclideanNorm (xy.1 - xy.2))
    (show (f, 0) ∈ F ×ˢ F by simp [hf, hzero])
  simpa only [sub_zero] using hle

/-- Constructs the grouped decomposition using the canonical sorted direction list. -/
theorem exists_groupedStructureDecomposition_canonical
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic ell E) (htile : Tiles F A E) :
    ∃ D : GroupedStructureDecomposition F A E ell 1,
      ∃ hnum : D.numberOfDirections = groupedDirectionCount F,
        ∀ j : Fin (groupedDirectionCount F),
          D.direction (Fin.cast hnum.symm j) = groupedTileDirections F j := by
  classical
  have hEindicator : ScalarPeriodic ell (setIndicator E) := by
    intro x z
    have hm := hE x z
    by_cases hx : x ∈ E
    · have hy : x + (ell : ℤ) • z ∈ E := hm.mpr hx
      rw [setIndicator, Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · have hy : x + (ell : ℤ) • z ∉ E := fun h ↦ hx (hm.mp h)
      rw [setIndicator, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  have hconvperiod : ScalarPeriodic ell (tileConv F (setIndicator A)) := by
    intro x z
    rw [htile, htile, hEindicator x z]
  obtain ⟨S⟩ := exists_structureDecomposition (d := 2) (by omega)
    hell hzero hconvperiod
  have hsum (x : Plane) :
      ∑ j, canonicalGroupedPhi S j x ≤ ((1 : ℕ) : ℝ) := by
    rw [canonicalGroupedPhi_sum]
    have hdecomp := S.decomposition x
    rw [htile x] at hdecomp
    simp only [Int.cast_mul, Int.cast_natCast] at hdecomp
    norm_num only [Int.cast_one, one_mul] at hdecomp
    have hA0 : (0 : ℝ) ≤ ((setIndicator A x : ℤ) : ℝ) := by
      by_cases hx : x ∈ A <;> simp [setIndicator, hx]
    have hE1 : ((setIndicator E x : ℤ) : ℝ) ≤ 1 := by
      by_cases hx : x ∈ E <;> simp [setIndicator, hx]
    norm_num only [Nat.cast_one] at ⊢
    linarith
  let D : GroupedStructureDecomposition F A E ell 1 := {
    numberOfDirections := groupedDirectionCount F
    number_pos := groupedDirectionCount_pos hzero hcard
    number_le := groupedDirectionCount_le hzero
    direction := groupedTileDirections F
    direction_ne_zero := groupedTileDirections_ne_zero hzero hcard
    pairwise_incommensurable := groupedTileDirections_pairwise hzero hcard
    phi := canonicalGroupedPhi S
    phi_nonneg := by
      intro j x
      exact Finset.sum_nonneg fun f _ ↦ S.phi_nonneg f x
    phi_le_level := by
      intro j x
      have hnonneg (i : Fin (groupedDirectionCount F)) :
          0 ≤ canonicalGroupedPhi S i x :=
        Finset.sum_nonneg fun f _ ↦ S.phi_nonneg f x
      calc
        canonicalGroupedPhi S j x ≤ ∑ i, canonicalGroupedPhi S i x :=
          Finset.single_le_sum (fun i _ ↦ hnonneg i) (Finset.mem_univ j)
        _ ≤ (1 : ℕ) := by simpa using hsum x
    phi_periodic := by
      intro j x
      apply Finset.sum_congr rfl
      intro f hf
      have hfindex := (Finset.mem_filter.mp hf).2
      have hfcanon := (canonicalIndex_eq_iff f j).1 hfindex
      obtain ⟨z, _hz, hdir⟩ :=
        (groupedTileDirections_fiber_spec hzero hcard j).1 f
          f.property hfcanon
      have hp := (S.phi_periodic f).zsmul z
      change S.phi f
        (x + (indicatorDilationModulus ell F.card : ℤ) • groupedTileDirections F j) =
          S.phi f x
      have hper : z • ((indicatorDilationModulus ell F.card : ℤ) • (f : Plane)) =
          (indicatorDilationModulus ell F.card : ℤ) • groupedTileDirections F j := by
        rw [hdir]
        module
      rw [← hper]
      exact hp x
    decomposition := by
      intro x
      rw [canonicalGroupedPhi_sum]
      have hS := S.decomposition x
      rw [htile x] at hS
      simpa using hS
    sum_phi_le := hsum
    direction_from_tile := groupedTileDirections_from_tile hzero hcard
    product_direction_l1_bound := by
      calc
        (∏ j : Fin (groupedDirectionCount F), l1Norm (groupedTileDirections F j)) ≤
            ∏ j : Fin (groupedDirectionCount F),
              ∏ f ∈ Finset.univ.filter
                (fun f : ↑(F.erase 0) ↦ canonicalIndex F f = j),
                  l1Norm (f : Plane) := by
          apply Finset.prod_le_prod'
          intro j _
          rw [← canonical_fiber_prod_eq (R := ℕ) j (fun f ↦ l1Norm f)]
          exact (groupedTileDirections_fiber_spec hzero hcard j).2.1
        _ = ∏ f : ↑(F.erase 0), l1Norm (f : Plane) := by
          exact canonical_prod_partition (R := ℕ)
            (fun f ↦ l1Norm (f : Plane))
        _ ≤ ∏ _f : ↑(F.erase 0), l1Diameter F := by
          apply Finset.prod_le_prod'
          intro f _
          exact mem_tile_norm_le_diameter hzero
            (x := (f : Plane)) (Finset.mem_erase.mp f.property).2
        _ = l1Diameter F ^ (F.card - 1) := by
          simp [Finset.card_erase_of_mem hzero]
    product_direction_euclidean_bound := by
      calc
        (∏ j : Fin (groupedDirectionCount F), euclideanNorm (groupedTileDirections F j)) ≤
            ∏ j : Fin (groupedDirectionCount F),
              ∏ f ∈ Finset.univ.filter
                (fun f : ↑(F.erase 0) ↦ canonicalIndex F f = j),
                  euclideanNorm (f : Plane) := by
          apply Finset.prod_le_prod
          · intro j _
            exact norm_nonneg _
          · intro j _
            rw [← canonical_fiber_prod_eq (R := ℝ) j (fun f ↦ euclideanNorm f)]
            exact (groupedTileDirections_fiber_spec hzero hcard j).2.2
        _ = ∏ f : ↑(F.erase 0), euclideanNorm (f : Plane) := by
          exact canonical_prod_partition (R := ℝ)
            (fun f ↦ euclideanNorm (f : Plane))
        _ ≤ ∏ _f : ↑(F.erase 0), euclideanDiameter F := by
          apply Finset.prod_le_prod
          · intro f _
            exact norm_nonneg _
          · intro f _
            exact mem_tile_euclideanNorm_le_diameter_local hzero
              (f := (f : Plane)) (Finset.mem_erase.mp f.property).2
        _ = euclideanDiameter F ^ (F.card - 1) := by
          simp [Finset.card_erase_of_mem hzero]
  }
  exact ⟨D, rfl, fun j ↦ rfl⟩

private theorem cosetwisePeriodic_transport_direction
    {F : Finset Plane} {ell m n : ℕ} {A : Set Plane}
    (h : Fin m → Plane) (k : Fin n → Plane)
    (hm : 0 < m) (hn : 0 < n) (e : m = n)
    (heq : ∀ j, h j = k (Fin.cast e j))
    (H : CosetwisePeriodic A (weakLattice F ell h hm)
      (fun j ↦ ((ell * weakMultiplier F ell h : ℕ) : ℤ) • h j)) :
    CosetwisePeriodic A (weakLattice F ell k hn)
      (fun j ↦ ((ell * weakMultiplier F ell k : ℕ) : ℤ) • k j) := by
  subst n
  simp only [Fin.cast_refl] at heq
  have hfun : h = k := funext heq
  subst k
  simpa only using H

/-- Produces quantitative weak-periodicity data depending only on the tile and target period. -/
theorem exists_quantitativeWeakPeriodData
    {F : Finset Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card) :
    ∃ D : QuantitativeWeakPeriodData F ell,
      ∀ (E A : Set Plane), SetScalarPeriodic ell E → Tiles F A E →
        D.ValidFor A := by
  classical
  have hemptyPeriodic : SetScalarPeriodic ell (∅ : Set Plane) := by
    intro x z
    simp
  have hemptyTiles : Tiles F (∅ : Set Plane) (∅ : Set Plane) := by
    intro x
    simp [tileConv, setIndicator]
  obtain ⟨D₀, hnum₀, hdir₀⟩ := exists_groupedStructureDecomposition_canonical
    hell hzero hcard hemptyPeriodic hemptyTiles
  obtain ⟨W₀⟩ := exists_weakArithmeticData D₀ hell
  have hdirectionL1 (j : Fin D₀.numberOfDirections) :
      l1Norm (D₀.direction j) ≤
        weakPeriodVectorBound F.card (l1Diameter F) := by
    have hs := Finset.single_le_prod'
      (s := (Finset.univ : Finset (Fin D₀.numberOfDirections)))
      (f := fun i ↦ l1Norm (D₀.direction i)) (a := j)
      (fun i _ ↦ by
        rw [Nat.one_le_iff_ne_zero]
        intro hnorm
        exact D₀.direction_ne_zero i (l1Norm_eq_zero.mp hnorm))
      (Finset.mem_univ j)
    exact hs.trans D₀.product_direction_l1_bound
  have hdirectionEu (j : Fin D₀.numberOfDirections) :
      euclideanNorm (D₀.direction j) ≤
        euclideanDiameter F ^ (F.card - 1) := by
    have hs : euclideanNorm (D₀.direction j) ≤
        ∏ i : Fin D₀.numberOfDirections, euclideanNorm (D₀.direction i) := by
      calc
        euclideanNorm (D₀.direction j) =
            ∏ i ∈ ({j} : Finset (Fin D₀.numberOfDirections)),
              euclideanNorm (D₀.direction i) := by simp
        _ ≤ ∏ i ∈ (Finset.univ : Finset (Fin D₀.numberOfDirections)),
              euclideanNorm (D₀.direction i) := by
          apply Finset.prod_le_prod_of_subset_of_one_le
          · exact Finset.singleton_subset_iff.mpr (Finset.mem_univ j)
          · intro i _
            exact norm_nonneg _
          · intro i _ _
            exact one_le_euclideanNorm (D₀.direction_ne_zero i)
        _ = _ := by simp
    exact hs.trans D₀.product_direction_euclidean_bound
  let QD : QuantitativeWeakPeriodData F ell := {
    numberOfDirections := D₀.numberOfDirections
    number_pos := D₀.number_pos
    number_le := D₀.number_le
    direction := D₀.direction
    direction_ne_zero := D₀.direction_ne_zero
    pairwise_incommensurable := D₀.pairwise_incommensurable
    direction_from_tile := D₀.direction_from_tile
    direction_l1_bound := hdirectionL1
    direction_euclidean_bound := hdirectionEu
    product_direction_l1_bound := D₀.product_direction_l1_bound
    product_direction_euclidean_bound := D₀.product_direction_euclidean_bound
    arithmetic := W₀
    lattice_le := by
      rw [W₀.lattice_eq]
      exact weakLattice_le_scalar D₀ hell
    relativeIndex_bound := by
      rw [W₀.lattice_eq]
      exact weakLattice_relativeIndex_bound D₀ hell
    multiplier_bound := by
      rw [W₀.multiplier_eq]
      exact weakMultiplier_bound D₀ hell
    period_mem_lattice := by
      intro j
      rw [W₀.lattice_eq, W₀.multiplier_eq]
      exact weak_period_mem_lattice D₀ hell j
  }
  refine ⟨QD, ?_⟩
  intro E A hE htile
  obtain ⟨D₁, hnum₁, hdir₁⟩ := exists_groupedStructureDecomposition_canonical
    hell hzero hcard hE htile
  have hnum : D₁.numberOfDirections = D₀.numberOfDirections :=
    hnum₁.trans hnum₀.symm
  have hdirection : ∀ j : Fin D₁.numberOfDirections,
      D₁.direction j = D₀.direction (Fin.cast hnum j) := by
    intro j
    let jc : Fin (groupedDirectionCount F) := Fin.cast hnum₁ j
    have h₁ := hdir₁ jc
    have h₀ := hdir₀ jc
    have hcast₁ : Fin.cast hnum₁.symm jc = j := by
      apply Fin.ext
      rfl
    have hcast₀ : Fin.cast hnum₀.symm jc = Fin.cast hnum j := by
      apply Fin.ext
      rfl
    rw [hcast₁] at h₁
    rw [hcast₀] at h₀
    exact h₁.trans h₀.symm
  have hvalid := coset_one_dimensional_periodicity D₁ hell hE
  have htransport := cosetwisePeriodic_transport_direction
    D₁.direction D₀.direction D₁.number_pos D₀.number_pos
      hnum hdirection hvalid
  change CosetwisePeriodic A QD.lattice
    (fun j ↦ ((ell * QD.multiplier : ℕ) : ℤ) • QD.direction j)
  dsimp [QD, QuantitativeWeakPeriodData.lattice,
    QuantitativeWeakPeriodData.multiplier] at ⊢
  simpa only [W₀.lattice_eq, W₀.multiplier_eq, Nat.cast_mul] using htransport

/-- Greenfeld--Tao Theorem 1.4 with closed `ℓ¹` constants. -/
theorem quantitative_weak_periodicity_l1
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic ell E) (htile : Tiles F A E) :
    ∃ D : QuantitativeWeakPeriodData F ell, D.ValidFor A := by
  obtain ⟨D, hD⟩ :=
    exists_quantitativeWeakPeriodData (F := F) (ell := ell) hell hzero hcard
  exact ⟨D, hD E A hE htile⟩

/-- Greenfeld--Tao Theorem 1.4 in the paper-facing Euclidean normalization. -/
theorem quantitative_weak_periodicity_euclidean
    {F : Finset Plane} {A E : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F) (hcard : 1 < F.card)
    (hE : SetScalarPeriodic ell E) (htile : Tiles F A E) :
    ∃ (m : ℕ) (h : Fin m → Plane) (Λ : AddSubgroup Plane) (L : ℕ),
      0 < m ∧ m ≤ F.card - 1 ∧
      (∀ j, h j ≠ 0) ∧ PairwiseIncommensurable h ∧
      (∀ j, ∃ f ∈ F, f ≠ 0 ∧ ∃ z : ℤ, h j = z • f) ∧
      (∀ j, euclideanNorm (h j) ≤
        euclideanDiameter F ^ (F.card - 1)) ∧
      (∏ j : Fin m, euclideanNorm (h j)) ≤
        euclideanDiameter F ^ (F.card - 1) ∧
      Λ ≤ scalarLattice ell ∧
      (Λ.relIndex (scalarLattice ell) : ℝ) ≤
        weakPeriodIndexEuclideanConstant F.card *
          euclideanDiameter F ^ (2 * (F.card - 1) ^ 2) ∧
      0 < L ∧ (L : ℝ) ≤ weakPeriodMultiplierEuclideanConstant F.card *
        euclideanDiameter F ^ (F.card * (F.card - 1)) ∧
      CosetwisePeriodic A Λ
        (fun j ↦ ((ell * L : ℕ) : ℤ) • h j) := by
  obtain ⟨D, hvalid⟩ := quantitative_weak_periodicity_l1
    hell hzero hcard hE htile
  let p := 2 * (F.card - 1) ^ 2
  let q := F.card * (F.card - 1)
  have hdiamNat : 0 < l1Diameter F := l1Diameter_pos_of_one_lt_card hcard
  have hdiam := l1Diameter_le_sqrt_dim_mul_euclideanDiameter F
  norm_num at hdiam
  have hindexNat := D.relativeIndex_bound
  have hindexMax : max 1 (l1Diameter F ^ p) = l1Diameter F ^ p := by
    apply max_eq_right
    exact Nat.one_le_pow p _ hdiamNat
  have hindexReal : (D.lattice.relIndex (scalarLattice ell) : ℝ) ≤
      weakPeriodIndexConstant F.card * (l1Diameter F : ℝ) ^ p := by
    rw [weakPeriodIndexBound, hindexMax] at hindexNat
    exact_mod_cast hindexNat
  have hmultNat := D.multiplier_bound
  have hmultMax : max 1 (l1Diameter F ^ q) = l1Diameter F ^ q := by
    apply max_eq_right
    exact Nat.one_le_pow q _ hdiamNat
  have hmultReal : (D.multiplier : ℝ) ≤
      weakPeriodMultiplierConstant F.card * (l1Diameter F : ℝ) ^ q := by
    rw [weakPeriodMultiplierBound, hmultMax] at hmultNat
    exact_mod_cast hmultNat
  refine ⟨D.numberOfDirections, D.direction, D.lattice, D.multiplier,
    D.number_pos, D.number_le, D.direction_ne_zero,
    D.pairwise_incommensurable, D.direction_from_tile,
    D.direction_euclidean_bound, D.product_direction_euclidean_bound,
    D.lattice_le, ?_, D.arithmetic.multiplier_pos, ?_, hvalid⟩
  · calc
      (D.lattice.relIndex (scalarLattice ell) : ℝ) ≤
          weakPeriodIndexConstant F.card * (l1Diameter F : ℝ) ^ p := hindexReal
      _ ≤ weakPeriodIndexConstant F.card *
          (Real.sqrt 2 * euclideanDiameter F) ^ p := by
        gcongr
      _ = weakPeriodIndexEuclideanConstant F.card *
          euclideanDiameter F ^ (2 * (F.card - 1) ^ 2) := by
        simp only [weakPeriodIndexEuclideanConstant, p, mul_pow]
        ring_nf
  · calc
      (D.multiplier : ℝ) ≤
          weakPeriodMultiplierConstant F.card * (l1Diameter F : ℝ) ^ q := hmultReal
      _ ≤ weakPeriodMultiplierConstant F.card *
          (Real.sqrt 2 * euclideanDiameter F) ^ q := by
        gcongr
      _ = weakPeriodMultiplierEuclideanConstant F.card *
          euclideanDiameter F ^ (F.card * (F.card - 1)) := by
        simp only [weakPeriodMultiplierEuclideanConstant, q, mul_pow]
        ring_nf

private theorem weaklyPeriodic_of_onePeriodic_local {A : Set Plane}
    (hA : OnePeriodic A) : WeaklyPeriodic A := by
  obtain ⟨p, hpne, hp⟩ := hA
  refine ⟨{
    numberOfParts := 1
    part := fun _ ↦ A
    period := fun _ ↦ p
    period_ne_zero := fun _ ↦ hpne
    periodic_part := fun _ ↦ hp
    pairwiseDisjoint := ?_
    iUnion_parts := ?_ }⟩
  · intro i _hi j _hj hij
    exact (hij (Subsingleton.elim i j)).elim
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hi
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩

private theorem weaklyPeriodic_translateSet_local (t : Plane) {A : Set Plane}
    (hA : WeaklyPeriodic A) : WeaklyPeriodic (translateSet t A) := by
  obtain ⟨D⟩ := hA
  refine ⟨{
    numberOfParts := D.numberOfParts
    part := fun i ↦ translateSet t (D.part i)
    period := D.period
    period_ne_zero := D.period_ne_zero
    periodic_part := ?_
    pairwiseDisjoint := ?_
    iUnion_parts := ?_ }⟩
  · intro i x
    change x + D.period i - t ∈ D.part i ↔ x - t ∈ D.part i
    simpa only [sub_add_eq_add_sub] using D.periodic_part i (x - t)
  · intro i _hi j _hj hij
    change Disjoint (translateSet t (D.part i)) (translateSet t (D.part j))
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hdisj := D.pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij
    exact Set.disjoint_left.mp hdisj hxi hxj
  · ext x
    simp only [Set.mem_iUnion, translateSet]
    constructor
    · rintro ⟨i, hi⟩
      have hx : x - t ∈ ⋃ i, D.part i := Set.mem_iUnion.mpr ⟨i, hi⟩
      rw [D.iUnion_parts] at hx
      exact hx
    · intro hx
      have hx' : x - t ∈ ⋃ i, D.part i := by
        rw [D.iUnion_parts]
        exact hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
      exact ⟨i, hi⟩

private theorem setScalarPeriodic_of_periodic_local
    {E : Set Plane} (hE : IsPeriodic E) :
    ∃ ell, 0 < ell ∧ SetScalarPeriodic ell E := by
  obtain ⟨H, hfinite, hperiod⟩ := hE
  let _ : Finite (Plane ⧸ H) := hfinite
  refine ⟨H.index, ?_, ?_⟩
  · rw [AddSubgroup.index_eq_card]
    exact Nat.card_pos
  · intro x z
    apply hperiod
    simpa using H.nsmul_index_mem z

private theorem singleton_tile_weaklyPeriodic
    {A E : Set Plane} (t : Plane) (hperiodicE : IsPeriodic E)
    (htile : Tiles ({t} : Finset Plane) A E) : WeaklyPeriodic A := by
  obtain ⟨ell, hell, hE⟩ := setScalarPeriodic_of_periodic_local hperiodicE
  let e : Plane := ![(1 : ℤ), (0 : ℤ)]
  let p : Plane := (ell : ℤ) • e
  have he : e ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [e] at h0
  have hpne : p ≠ 0 := smul_ne_zero
    (by exact_mod_cast (Nat.ne_of_gt hell)) he
  have htileEq (x : Plane) : setIndicator A (x - t) = setIndicator E x := by
    simpa [Tiles, TilesAtLevel, tileConv] using htile x
  apply weaklyPeriodic_of_onePeriodic_local
  refine ⟨p, hpne, ?_⟩
  intro x
  apply (setIndicator_eq_iff_membership_local A (x + p) x).1
  calc
    setIndicator A (x + p) = setIndicator E ((x + p) + t) := by
      simpa only [add_sub_cancel_right] using htileEq ((x + p) + t)
    _ = setIndicator E (x + t) := by
      apply (setIndicator_eq_iff_membership_local E _ _).2
      have hper := hE (x + t) e
      simpa only [p, add_assoc, add_left_comm, add_comm] using hper
    _ = setIndicator A x := by
      symm
      simpa only [add_sub_cancel_right] using htileEq (x + t)

private theorem quantitative_lattice_index_ne_zero
    {F : Finset Plane} {ell : ℕ} (D : QuantitativeWeakPeriodData F ell) :
    D.lattice.index ≠ 0 := by
  let q := weakQ F ell
  let N := weakN D.direction
  let M := weakM D.direction
  let a := weakAvoidance D.direction
  let h₀ := D.direction ⟨0, D.number_pos⟩
  have haSpec := avoidanceVector_spec D.direction_ne_zero
  have hw₀ : wedge a h₀ ≠ 0 := by
    intro hw
    exact haSpec.2.1 ⟨0, D.number_pos⟩
      ((commensurable_iff_wedge_eq_zero haSpec.1
        (D.direction_ne_zero ⟨0, D.number_pos⟩)).2 hw)
  have hdet : wedge (weakSliceVector F ell D.direction)
      (((q * N * M : ℕ) : ℤ) • h₀) ≠ 0 := by
    rw [weakSliceVector, wedge_zsmul_left, wedge_zsmul_right]
    exact mul_ne_zero
      (by exact_mod_cast (Nat.ne_of_gt
        (Nat.mul_pos D.arithmetic.q_pos D.arithmetic.pairLCM_pos)))
      (mul_ne_zero
        (by exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos
          (Nat.mul_pos D.arithmetic.q_pos D.arithmetic.pairLCM_pos)
          D.arithmetic.avoidanceLCM_pos))) hw₀)
  change D.arithmetic.lattice.index ≠ 0
  rw [D.arithmetic.lattice_eq, weakLattice, index_generatedPair hdet]
  exact Int.natAbs_ne_zero.mpr hdet

private theorem quantitative_valid_weaklyPeriodic
    {F : Finset Plane} {A : Set Plane} {ell : ℕ}
    (hell : 0 < ell) (D : QuantitativeWeakPeriodData F ell)
    (hvalid : D.ValidFor A) : WeaklyPeriodic A := by
  let _ : Finite (Plane ⧸ D.lattice) :=
    AddSubgroup.index_ne_zero_iff_finite.mp (quantitative_lattice_index_ne_zero D)
  apply weaklyPeriodic_of_cosetwise A D.lattice
    (fun j ↦ (((ell * D.multiplier : ℕ) : ℤ) • D.direction j))
    D.number_pos
  · intro j
    apply smul_ne_zero
    · exact Int.ofNat_ne_zero.mpr
        (Nat.ne_of_gt (Nat.mul_pos hell D.arithmetic.multiplier_pos))
    · exact D.direction_ne_zero j
  · exact D.period_mem_lattice
  · exact hvalid

/-- Greenfeld--Tao Theorem 1.3(i): every level-one planar tiling is weakly periodic. -/
theorem level_one_plane_weaklyPeriodic
    {F : Finset Plane} {A E : Set Plane}
    (hF : F.Nonempty) (hperiodicE : IsPeriodic E)
    (htile : Tiles F A E) : WeaklyPeriodic A := by
  have hFpos : 0 < F.card := Finset.card_pos.mpr hF
  obtain ⟨t, htF⟩ := hF
  by_cases hcard : F.card = 1
  · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
    have htu : t = u := by
      rw [hu] at htF
      simpa using htF
    subst t
    rw [hu] at htile
    exact singleton_tile_weaklyPeriodic u hperiodicE htile
  · obtain ⟨ell, hell, hE⟩ := setScalarPeriodic_of_periodic_local hperiodicE
    let F₀ : Finset Plane := F.image fun f ↦ f - t
    let A₀ : Set Plane := translateSet t A
    have hzero : 0 ∈ F₀ :=
      Finset.mem_image.mpr ⟨t, htF, sub_self t⟩
    have hcardEq : F₀.card = F.card :=
      Finset.card_image_iff.mpr (Set.injOn_of_injective
        (sub_left_injective : Function.Injective fun f : Plane ↦ f - t))
    have hcard₀ : 1 < F₀.card := by
      rw [hcardEq]
      omega
    have htile₀ : Tiles F₀ A₀ E := by
      have ht₀ := (tiles_translate_tile F A E 1 t).mp htile
      have himage :
          @Finset.image Plane Plane (Classical.decEq Plane)
            (fun f ↦ f - t) F = F₀ := by
        ext x
        simp only [F₀, Finset.mem_image]
      rw [himage] at ht₀
      exact ht₀
    obtain ⟨D, hvalid⟩ := quantitative_weak_periodicity_l1
      hell hzero hcard₀ hE htile₀
    have hweak₀ : WeaklyPeriodic A₀ :=
      quantitative_valid_weaklyPeriodic hell D hvalid
    have hback := weaklyPeriodic_translateSet_local (-t) hweak₀
    simpa [A₀, translateSet] using hback

end TranslationalTilings
