import Tiling.RationalPolygonal.DiscreteCarrier
import Tiling.RationalPolygonal.IntegerReduction

set_option linter.style.header false

/-!
# Fundamental-cell raster signatures

For a polygonal region `K` and a point `u` in one lattice cell, the raster signature consists of
the integer vectors `z` for which `u + z` lies in `K`.  Compactness of `K` and closed discreteness
of the embedded integer plane make every signature finite.  The elementary representation lemma
below is the exact local bridge between a continuous integer-translation tiling and a discrete
tiling of `ℤ²` by one signature.
-/

open Filter MeasureTheory Set
open TranslationalTilings
open scoped Pointwise

namespace Tiling.RationalPolygonal

/-- A compact closed representative of one fundamental cell of the integer lattice. -/
def closedUnitCell : Set Plane :=
  Complex.equivRealProdCLM ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)

/-- The closed fundamental cell is compact. -/
theorem isCompact_closedUnitCell : IsCompact closedUnitCell := by
  exact Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.2
    (isCompact_Icc.prod isCompact_Icc)

/-- The fundamental cell has positive planar volume. -/
theorem volume_closedUnitCell_ne_zero : volume closedUnitCell ≠ 0 := by
  let c : Plane := (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * Complex.I
  let ball : Set Plane := Metric.ball c (4 : ℝ)⁻¹
  have hballNonempty : ball.Nonempty := by
    exact ⟨c, Metric.mem_ball_self (by norm_num)⟩
  have hballMeasure : volume ball ≠ 0 :=
    Metric.isOpen_ball.measure_ne_zero volume hballNonempty
  have hballSubset : ball ⊆ closedUnitCell := by
    intro z hz
    have hnorm : ‖z - c‖ < (4 : ℝ)⁻¹ := by
      simpa only [ball, Metric.mem_ball, Complex.dist_eq] using hz
    have hre : |z.re - (2 : ℝ)⁻¹| < (4 : ℝ)⁻¹ := by
      apply lt_of_le_of_lt _ hnorm
      simpa only [c, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, mul_zero, Complex.ofReal_im, zero_mul,
        sub_zero, add_zero, Complex.sub_re] using Complex.abs_re_le_norm (z - c)
    have him : |z.im - (2 : ℝ)⁻¹| < (4 : ℝ)⁻¹ := by
      apply lt_of_le_of_lt _ hnorm
      simpa only [c, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_one, Complex.ofReal_re, zero_mul,
        zero_add, add_zero, Complex.sub_im] using Complex.abs_im_le_norm (z - c)
    rw [closedUnitCell]
    change (z.re, z.im) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
    rw [abs_lt] at hre him
    constructor <;> constructor <;> norm_num at hre him ⊢ <;> linarith
  intro hcellZero
  exact hballMeasure (MeasureTheory.measure_mono_null hballSubset hcellZero)

/-- Integer translate of the closed fundamental cell. -/
def translatedClosedUnitCell (q : IntegerPlane) : Set Plane :=
  integerPoint q +ᵥ closedUnitCell

/-- Integer translates of the closed unit cell cover the real plane. -/
theorem iUnion_translatedClosedUnitCell :
    (⋃ q : IntegerPlane, translatedClosedUnitCell q) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  let q : IntegerPlane := ![⌊x.re⌋, ⌊x.im⌋]
  refine ⟨q, ?_⟩
  rw [translatedClosedUnitCell, Set.mem_vadd_set_iff_neg_vadd_mem, closedUnitCell]
  change ((-integerPoint q + x).re, (-integerPoint q + x).im) ∈
    Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
  simp only [Complex.add_re, Complex.neg_re, integerPoint_re,
    Complex.add_im, Complex.neg_im, integerPoint_im]
  have hreLower := Int.floor_le x.re
  have hreUpper := Int.lt_floor_add_one x.re
  have himLower := Int.floor_le x.im
  have himUpper := Int.lt_floor_add_one x.im
  change (⌊x.re⌋ : ℝ) ≤ x.re at hreLower
  change x.re < (⌊x.re⌋ : ℝ) + 1 at hreUpper
  change (⌊x.im⌋ : ℝ) ≤ x.im at himLower
  change x.im < (⌊x.im⌋ : ℝ) + 1 at himUpper
  dsimp only [q, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> constructor <;> linarith

/-- Translating every vector in a translation set does not change whether a finite tile tiles the
whole ambient group. -/
theorem tilesUniverse_vadd_translationSet_iff {G : Type*} [AddCommGroup G]
    (a : G) (F : Finset G) (T : Set G) :
    TilesUniverse F (a +ᵥ T) ↔ TilesUniverse F T := by
  constructor
  · intro hshift
    apply tilesUniverse_of_existsUnique
    intro x
    obtain ⟨f, hf, hfunique⟩ :=
      existsUnique_tile_representation hshift (a + x)
    refine ⟨f, ?_, ?_⟩
    · refine ⟨hf.1, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hf
      convert hf.2 using 1
      simp only [vadd_eq_add]
      abel
    · intro g hg
      apply hfunique g
      refine ⟨hg.1, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      convert hg.2 using 1
      simp only [vadd_eq_add]
      abel
  · intro hT
    apply tilesUniverse_of_existsUnique
    intro x
    obtain ⟨f, hf, hfunique⟩ :=
      existsUnique_tile_representation hT (-a + x)
    refine ⟨f, ?_, ?_⟩
    · refine ⟨hf.1, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      convert hf.2 using 1
      simp only [vadd_eq_add]
      abel
    · intro g hg
      apply hfunique g
      refine ⟨hg.1, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hg
      convert hg.2 using 1
      simp only [vadd_eq_add]
      abel

namespace PolygonalRegion

/-- Almost every point of a monotile tiling belongs to exactly one translated copy. -/
theorem Tiles.ae_existsUnique_translation {K : PolygonalRegion} {T : Set Plane}
    (hT : K.Tiles T) :
    ∀ᵐ x, ∃! t : Plane,
      t ∈ T ∧ x ∈ placedTile K.prototileFamily (t, ()) := by
  let A := K.placements T
  let _ : Countable A := (Tiling.IsTiling.countable hT).to_subtype
  have hunique : ∀ᵐ x, ∀ i j : A,
      x ∈ placedTile K.prototileFamily i.1 →
      x ∈ placedTile K.prototileFamily j.1 → i = j := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · rw [ae_iff]
      have hijval : i.1 ≠ j.1 := by
        intro hval
        apply hij
        exact Subtype.ext hval
      have had := hT.isPacking i.2 j.2 hijval
      change volume
        (placedTile K.prototileFamily i.1 ∩
          placedTile K.prototileFamily j.1) = 0 at had
      rw [show {x | ¬(x ∈ placedTile K.prototileFamily i.1 →
          x ∈ placedTile K.prototileFamily j.1 → i = j)} =
          placedTile K.prototileFamily i.1 ∩
            placedTile K.prototileFamily j.1 by
        ext x
        simp [hij]]
      exact had
  filter_upwards [hT.isCover, hunique] with x hxcover hxunique
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxcover
  refine ⟨i.1.1, ⟨i.2, hxi⟩, ?_⟩
  intro t ht
  let j : A := ⟨(t, ()), ht.1⟩
  have hij := hxunique i j hxi ht.2
  exact congrArg (fun p : A ↦ p.1.1) hij |>.symm

/-- Integer offsets at which the lattice orbit of `u` meets the polygonal support. -/
def latticeSlice (K : PolygonalRegion) (u : Plane) : Set IntegerPlane :=
  {z | u + integerPoint z ∈ K.support}

@[simp]
theorem mem_latticeSlice_iff {K : PolygonalRegion} {u : Plane}
    {z : IntegerPlane} :
    z ∈ K.latticeSlice u ↔ u + integerPoint z ∈ K.support :=
  Iff.rfl

/-- Every lattice slice of a bounded polygonal region is finite. -/
theorem latticeSlice_finite (K : PolygonalRegion) (u : Plane) :
    (K.latticeSlice u).Finite := by
  have hcompact : IsCompact (-u +ᵥ K.support) :=
    (K.isPolygonal.vadd (-u)).isCompact
  have hfinite := finite_integerPoint_preimage_of_isCompact hcompact
  apply hfinite.subset
  intro z hz
  change u + integerPoint z ∈ K.support at hz
  change integerPoint z ∈ -u +ᵥ K.support
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  convert hz using 1
  simp only [vadd_eq_add]
  abel

/-- All integer offsets that can occur in a signature based in the closed fundamental cell. -/
def signatureWindow (K : PolygonalRegion) : Set IntegerPlane :=
  {z | ∃ u ∈ closedUnitCell, u + integerPoint z ∈ K.support}

/-- The common signature window is finite. -/
theorem signatureWindow_finite (K : PolygonalRegion) :
    K.signatureWindow.Finite := by
  let differences : Set Plane :=
    (fun p : Plane × Plane ↦ p.1 - p.2) ''
      (K.support ×ˢ closedUnitCell)
  have hcompact : IsCompact differences :=
    (K.isPolygonal.isCompact.prod isCompact_closedUnitCell).image continuous_sub
  have hfinite := finite_integerPoint_preimage_of_isCompact hcompact
  apply hfinite.subset
  intro z hz
  obtain ⟨u, huCell, huz⟩ := hz
  change integerPoint z ∈ differences
  refine ⟨(u + integerPoint z, u), ⟨huz, huCell⟩, ?_⟩
  simp only
  abel

/-- The finite raster tile seen from a fundamental-cell point. -/
noncomputable def signature (K : PolygonalRegion) (u : Plane) : Finset IntegerPlane :=
  K.latticeSlice_finite u |>.toFinset

@[simp]
theorem mem_signature_iff {K : PolygonalRegion} {u : Plane}
    {z : IntegerPlane} :
    z ∈ K.signature u ↔ u + integerPoint z ∈ K.support := by
  simp only [signature, Set.Finite.mem_toFinset, mem_latticeSlice_iff]

/-- Carrier covered by integer translates of a polygonal region. -/
def integerTranslationCarrier (K : PolygonalRegion)
    (T : Set IntegerPlane) : Set Plane :=
  {x | ∃ y ∈ K.support, ∃ t ∈ T, x = y + integerPoint t}

@[simp]
theorem mem_integerTranslationCarrier_iff {K : PolygonalRegion}
    {T : Set IntegerPlane} {x : Plane} :
    x ∈ K.integerTranslationCarrier T ↔
      ∃ y ∈ K.support, ∃ t ∈ T, x = y + integerPoint t :=
  Iff.rfl

/-- Integer translates of a compact polygonal support form a locally finite family, even when
the selected translation set is not assumed to tile or pack the plane. -/
theorem locallyFinite_integerTranslates
    (K : PolygonalRegion) (T : Set IntegerPlane) :
    LocallyFinite fun t : T ↦ integerPoint (t : IntegerPlane) +ᵥ K.support := by
  obtain ⟨R, hR⟩ := K.isPolygonal.isBounded.subset_closedBall (0 : Plane)
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  let H : Set T :=
    {t | ((integerPoint (t : IntegerPlane) +ᵥ K.support) ∩ Metric.ball x 1).Nonempty}
  have himage_subset : ((fun t : T ↦ (t : IntegerPlane)) '' H) ⊆
      {z : IntegerPlane | integerPoint z ∈ Metric.closedBall x (R + 1)} := by
    rintro z ⟨t, ht, rfl⟩
    obtain ⟨y, hytranslate, hyball⟩ := ht
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hytranslate
    have hsupport := hR hytranslate
    change integerPoint (t : IntegerPlane) ∈ Metric.closedBall x (R + 1)
    rw [Metric.mem_closedBall] at hsupport ⊢
    rw [Metric.mem_ball] at hyball
    have hdistance :
        dist (integerPoint (t : IntegerPlane)) y =
          dist (-integerPoint (t : IntegerPlane) + y) 0 := by
      rw [dist_comm]
      simp only [dist_eq_norm, sub_zero]
      congr 1
      abel
    calc
      dist (integerPoint (t : IntegerPlane)) x ≤
          dist (integerPoint (t : IntegerPlane)) y + dist y x :=
        dist_triangle _ _ _
      _ = dist (-integerPoint (t : IntegerPlane) + y) 0 + dist y x := by
        rw [hdistance]
      _ ≤ R + 1 := add_le_add hsupport hyball.le
  have hfinite :
      {z : IntegerPlane | integerPoint z ∈ Metric.closedBall x (R + 1)}.Finite :=
    finite_integerPoint_preimage_of_isCompact (isCompact_closedBall x (R + 1))
  have himage_finite : ((fun t : T ↦ (t : IntegerPlane)) '' H).Finite :=
    hfinite.subset himage_subset
  change H.Finite
  exact himage_finite.of_finite_image (Set.injOn_of_injective Subtype.val_injective)

/-- Every carrier formed from integer translates of a polygonal region is regular closed. -/
theorem integerTranslationCarrier_closure_interior
    (K : PolygonalRegion) (T : Set IntegerPlane) :
    closure (interior (K.integerTranslationCarrier T)) =
      K.integerTranslationCarrier T := by
  have hunion :
      (⋃ t : T, integerPoint (t : IntegerPlane) +ᵥ K.support) =
        K.integerTranslationCarrier T := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxt
      exact ⟨-integerPoint (t : IntegerPlane) + x, hxt,
        (t : IntegerPlane), t.2, by abel⟩
    · rintro ⟨y, hy, t, ht, rfl⟩
      apply Set.mem_iUnion.mpr
      refine ⟨⟨t, ht⟩, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      convert hy using 1
      simp only [vadd_eq_add]
      abel
  rw [← hunion]
  exact (K.locallyFinite_integerTranslates T).closure_interior_iUnion_eq fun t ↦
    (K.isPolygonal.vadd (integerPoint (t : IntegerPlane))).closure_interior

private theorem regularClosed_eq_of_ae_eq
    {A B : Set Plane}
    (hA : closure (interior A) = A)
    (hB : closure (interior B) = B)
    (hAB : A =ᵐ[volume] B) : A = B := by
  have hAclosed : IsClosed A := by
    rw [← hA]
    exact isClosed_closure
  have hBclosed : IsClosed B := by
    rw [← hB]
    exact isClosed_closure
  have hzeroAB : volume (A \ B) = 0 := (ae_eq_set.mp hAB).1
  have hzeroBA : volume (B \ A) = 0 := (ae_eq_set.mp hAB).2
  apply Set.Subset.antisymm
  · rw [← hA]
    apply closure_minimal _ hBclosed
    intro x hxA
    by_contra hxB
    let U := interior A ∩ Bᶜ
    have hUopen : IsOpen U := isOpen_interior.inter hBclosed.isOpen_compl
    have hxU : x ∈ U := ⟨hxA, hxB⟩
    have hUzero : volume U = 0 := by
      apply measure_mono_null _ hzeroAB
      intro y hy
      exact ⟨interior_subset hy.1, hy.2⟩
    exact hUopen.measure_ne_zero volume ⟨x, hxU⟩ hUzero
  · rw [← hB]
    apply closure_minimal _ hAclosed
    intro x hxB
    by_contra hxA
    let U := interior B ∩ Aᶜ
    have hUopen : IsOpen U := isOpen_interior.inter hAclosed.isOpen_compl
    have hxU : x ∈ U := ⟨hxB, hxA⟩
    have hUzero : volume U = 0 := by
      apply measure_mono_null _ hzeroBA
      intro y hy
      exact ⟨interior_subset hy.1, hy.2⟩
    exact hUopen.measure_ne_zero volume ⟨x, hxU⟩ hUzero

/-- Almost-everywhere equality of two integer-translation carriers upgrades to literal equality. -/
theorem integerTranslationCarrier_eq_of_ae_eq
    (K : PolygonalRegion) {T₀ T₁ : Set IntegerPlane}
    (h : K.integerTranslationCarrier T₀ =ᵐ[volume]
      K.integerTranslationCarrier T₁) :
    K.integerTranslationCarrier T₀ = K.integerTranslationCarrier T₁ := by
  exact regularClosed_eq_of_ae_eq
    (K.integerTranslationCarrier_closure_interior T₀)
    (K.integerTranslationCarrier_closure_interior T₁) h

/-- Pointwise carrier membership is exactly discrete signature-carrier membership in lattice
coordinates. -/
theorem mem_integerTranslationCarrier_iff_mem_discreteCarrier_signature
    (K : PolygonalRegion) (T : Set IntegerPlane)
    {u x : Plane} {q : IntegerPlane} (hx : x = u + integerPoint q) :
    x ∈ K.integerTranslationCarrier T ↔
      q ∈ discreteCarrier (K.signature u) T := by
  constructor
  · rintro ⟨y, hy, t, ht, hxy⟩
    let f : IntegerPlane := q - t
    have hf : f ∈ K.signature u := by
      rw [mem_signature_iff]
      rw [integerPoint_sub]
      rw [hxy] at hx
      convert hy using 1
      calc
        u + (integerPoint q - integerPoint t) =
            (u + integerPoint q) - integerPoint t := by abel
        _ = (y + integerPoint t) - integerPoint t := by rw [hx]
        _ = y := by abel
    exact mem_discreteCarrier_iff.mpr ⟨f, hf, t, ht, by dsimp only [f]; abel⟩
  · rintro ⟨f, hf, t, ht, hq⟩
    refine ⟨u + integerPoint f, mem_signature_iff.mp hf, t, ht, ?_⟩
    rw [hx, hq, integerPoint_add]
    abel

/-- Moving the base point by an integer vector shifts the finite signature by the opposite
integer vector. -/
theorem signature_add_integerPoint (K : PolygonalRegion)
    (u : Plane) (q : IntegerPlane) :
    K.signature (u + integerPoint q) = shiftFinset q (K.signature u) := by
  ext z
  rw [mem_signature_iff, mem_shiftFinset_iff, mem_signature_iff, integerPoint_add]
  constructor <;> intro h
  · convert h using 1
    abel
  · convert h using 1
    abel

/-- Every signature based in the fundamental cell lies in the common finite window. -/
theorem signature_subset_signatureWindow (K : PolygonalRegion) {u : Plane}
    (hu : u ∈ closedUnitCell) :
    ↑(K.signature u) ⊆ K.signatureWindow := by
  intro z hz
  exact ⟨u, hu, (mem_signature_iff.mp hz)⟩

/-- The finite list of all candidate signatures inside the common window. -/
noncomputable def candidateSignatures (K : PolygonalRegion) :
    Finset (Finset IntegerPlane) :=
  K.signatureWindow_finite.toFinset.powerset

/-- Every actual fundamental-cell signature occurs in the finite candidate list. -/
theorem signature_mem_candidateSignatures (K : PolygonalRegion) {u : Plane}
    (hu : u ∈ closedUnitCell) :
    K.signature u ∈ K.candidateSignatures := by
  rw [candidateSignatures, Finset.mem_powerset]
  intro z hz
  simpa only [Set.Finite.mem_toFinset] using
    K.signature_subset_signatureWindow hu hz

/-- Points of the fundamental cell which have one specified finite signature. -/
def signatureFiber (K : PolygonalRegion) (F : Finset IntegerPlane) : Set Plane :=
  closedUnitCell ∩ {u | K.signature u = F}

@[simp]
theorem mem_signatureFiber_iff {K : PolygonalRegion} {F : Finset IntegerPlane}
    {u : Plane} :
    u ∈ K.signatureFiber F ↔ u ∈ closedUnitCell ∧ K.signature u = F :=
  Iff.rfl

private theorem measurableSet_signature_membership
    (K : PolygonalRegion) (z : IntegerPlane) :
    MeasurableSet {u : Plane | z ∈ K.signature u} := by
  have hcontinuous : Continuous (fun u : Plane ↦ u + integerPoint z) :=
    continuous_id.add continuous_const
  have heq : {u : Plane | z ∈ K.signature u} =
      (fun u : Plane ↦ u + integerPoint z) ⁻¹' K.support := by
    ext u
    exact mem_signature_iff
  rw [heq]
  exact K.isPolygonal.isClosed.measurableSet.preimage hcontinuous.measurable

/-- Every signature fiber is measurable. -/
theorem measurableSet_signatureFiber (K : PolygonalRegion)
    (F : Finset IntegerPlane) :
    MeasurableSet (K.signatureFiber F) := by
  let condition : IntegerPlane → Set Plane := fun z ↦
    if z ∈ F then {u | z ∈ K.signature u} else {u | z ∉ K.signature u}
  have hcondition : ∀ z, MeasurableSet (condition z) := by
    intro z
    by_cases hz : z ∈ F
    · simpa only [condition, if_pos hz] using measurableSet_signature_membership K z
    · dsimp only [condition]
      rw [if_neg hz]
      change MeasurableSet ({u : Plane | z ∈ K.signature u}ᶜ)
      exact (measurableSet_signature_membership K z).compl
  have heq : {u : Plane | K.signature u = F} = ⋂ z, condition z := by
    ext u
    simp only [Set.mem_iInter]
    constructor
    · intro h z
      by_cases hz : z ∈ F
      · have hzsig : z ∈ K.signature u := by
          rw [h]
          exact hz
        dsimp only [condition]
        rw [if_pos hz]
        exact hzsig
      · have hzsig : z ∉ K.signature u := by
          rw [h]
          exact hz
        dsimp only [condition]
        rw [if_neg hz]
        exact hzsig
    · intro h
      apply Finset.ext
      intro z
      specialize h z
      by_cases hz : z ∈ F
      · have hzsig : z ∈ K.signature u := by
          dsimp only [condition] at h
          rw [if_pos hz] at h
          exact h
        exact iff_of_true hzsig hz
      · have hzsig : z ∉ K.signature u := by
          dsimp only [condition] at h
          rw [if_neg hz] at h
          exact h
        exact iff_of_false hzsig hz
  rw [signatureFiber, heq]
  exact isCompact_closedUnitCell.isClosed.measurableSet.inter
    (MeasurableSet.iInter hcondition)

/-- The signatures occurring on a positive-measure subset of the fundamental cell. -/
noncomputable def relevantSignatures (K : PolygonalRegion) :
    Finset (Finset IntegerPlane) :=
  K.candidateSignatures.filter fun F ↦ volume (K.signatureFiber F) ≠ 0

@[simp]
theorem mem_relevantSignatures_iff {K : PolygonalRegion}
    {F : Finset IntegerPlane} :
    F ∈ K.relevantSignatures ↔
      F ∈ K.candidateSignatures ∧ volume (K.signatureFiber F) ≠ 0 := by
  classical
  simp only [relevantSignatures, Finset.mem_filter]

/-- A conull simultaneous signature tiling tiles each positive-measure signature exactly. -/
theorem tilesUniverse_relevantSignatures_of_ae
    (K : PolygonalRegion) {T : Set IntegerPlane}
    (hT : ∀ᵐ u, TilesUniverse (K.signature u) T) :
    ∀ F ∈ K.relevantSignatures, TilesUniverse F T := by
  intro F hF
  have hmeasure : volume (K.signatureFiber F) ≠ 0 :=
    (mem_relevantSignatures_iff.mp hF).2
  obtain ⟨u, huFiber, huTiles⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hmeasure (ae_restrict_of_ae hT)
  rw [mem_signatureFiber_iff] at huFiber
  rwa [huFiber.2] at huTiles

/-- Almost every point of the fundamental cell has a positive-measure signature. -/
theorem ae_signature_mem_relevantSignatures (K : PolygonalRegion) :
    ∀ᵐ u ∂volume.restrict closedUnitCell,
      K.signature u ∈ K.relevantSignatures := by
  classical
  have havoid : ∀ᵐ u ∂volume,
      ∀ F ∈ K.candidateSignatures,
        volume (K.signatureFiber F) = 0 → u ∉ K.signatureFiber F := by
    rw [eventually_all_finset]
    intro F hF
    by_cases hzero : volume (K.signatureFiber F) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with u hu
      exact fun _ ↦ hu
    · exact Filter.Eventually.of_forall fun _ h ↦ (hzero h).elim
  have hcell : MeasurableSet closedUnitCell :=
    isCompact_closedUnitCell.isClosed.measurableSet
  filter_upwards [ae_restrict_of_ae havoid, ae_restrict_mem hcell]
    with u huAvoid huCell
  rw [mem_relevantSignatures_iff]
  have hcandidate := K.signature_mem_candidateSignatures huCell
  refine ⟨hcandidate, ?_⟩
  intro hzero
  exact huAvoid (K.signature u) hcandidate hzero ⟨huCell, rfl⟩

/-- Every polygonal region has at least one positive-measure fundamental-cell signature. -/
theorem relevantSignatures_nonempty (K : PolygonalRegion) :
    K.relevantSignatures.Nonempty := by
  let _ : (ae (volume.restrict closedUnitCell)).NeBot :=
    ae_restrict_neBot.mpr volume_closedUnitCell_ne_zero
  obtain ⟨u, hu⟩ := K.ae_signature_mem_relevantSignatures.exists
  exact ⟨K.signature u, hu⟩

/-- A nonempty polygonal region has a positive-measure signature containing at least one lattice
point.  This supplies the distinguished nonempty color needed by the rigid marker construction. -/
theorem exists_nonempty_relevantSignature (K : PolygonalRegion) :
    ∃ F ∈ K.relevantSignatures, F.Nonempty := by
  have hsupport : volume K.support ≠ 0 :=
    ne_of_gt (K.isPolygonal.volume_pos K.nonempty)
  have hunion :
      (⋃ q : IntegerPlane, K.support ∩ translatedClosedUnitCell q) = K.support := by
    rw [← Set.inter_iUnion]
    rw [iUnion_translatedClosedUnitCell]
    simp
  have hexists : ∃ q : IntegerPlane,
      volume (K.support ∩ translatedClosedUnitCell q) ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hzero : volume (⋃ q : IntegerPlane,
        K.support ∩ translatedClosedUnitCell q) = 0 :=
      measure_iUnion_null hnone
    rw [hunion] at hzero
    exact hsupport hzero
  obtain ⟨q, hq⟩ := hexists
  let basePart : Set Plane :=
    -integerPoint q +ᵥ (K.support ∩ translatedClosedUnitCell q)
  have hbaseMeasure : volume basePart ≠ 0 := by
    change volume (-integerPoint q +ᵥ
      (K.support ∩ translatedClosedUnitCell q)) ≠ 0
    rw [measure_vadd]
    exact hq
  have hbaseCell : basePart ⊆ closedUnitCell := by
    intro u hu
    change u ∈ -integerPoint q +ᵥ
      (K.support ∩ translatedClosedUnitCell q) at hu
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hu
    have huTranslated := hu.2
    rw [translatedClosedUnitCell, Set.mem_vadd_set_iff_neg_vadd_mem] at huTranslated
    simpa only [neg_neg, vadd_eq_add, neg_add_cancel_left] using huTranslated
  have hbaseSignature : ∀ u ∈ basePart, q ∈ K.signature u := by
    intro u hu
    change u ∈ -integerPoint q +ᵥ
      (K.support ∩ translatedClosedUnitCell q) at hu
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hu
    rw [mem_signature_iff]
    simpa only [neg_neg, vadd_eq_add, add_comm] using hu.1
  have hcellMeasurable : MeasurableSet closedUnitCell :=
    isCompact_closedUnitCell.isClosed.measurableSet
  have hae : ∀ᵐ u ∂volume,
      u ∈ closedUnitCell → K.signature u ∈ K.relevantSignatures :=
    (ae_restrict_iff' hcellMeasurable).mp K.ae_signature_mem_relevantSignatures
  obtain ⟨u, huBase, huRelevant⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hbaseMeasure (ae_restrict_of_ae hae)
  have hrel : K.signature u ∈ K.relevantSignatures :=
    huRelevant (hbaseCell huBase)
  exact ⟨K.signature u, hrel, ⟨q, hbaseSignature u huBase⟩⟩

/-- Exact tiling of every positive-measure signature implies an almost-everywhere tiling of all
signatures in the plane. -/
theorem ae_signature_tilesUniverse_of_relevantSignatures
    (K : PolygonalRegion) {T : Set IntegerPlane}
    (hT : ∀ F ∈ K.relevantSignatures, TilesUniverse F T) :
    ∀ᵐ u, TilesUniverse (K.signature u) T := by
  have hcell : ∀ᵐ u ∂volume.restrict closedUnitCell,
      TilesUniverse (K.signature u) T :=
    K.ae_signature_mem_relevantSignatures.mono fun _ hu ↦ hT _ hu
  have htranslated : ∀ q : IntegerPlane,
      ∀ᵐ x ∂volume.restrict (translatedClosedUnitCell q),
        TilesUniverse (K.signature x) T := by
    intro q
    let a : Plane := integerPoint q
    have hmaps : Set.MapsTo (fun x : Plane ↦ -a + x)
        (translatedClosedUnitCell q) closedUnitCell := by
      intro x hx
      rw [translatedClosedUnitCell, Set.mem_vadd_set_iff_neg_vadd_mem] at hx
      simpa only [a, vadd_eq_add] using hx
    have hpull :=
      ((quasiMeasurePreserving_add_left volume (-a)).restrict hmaps).ae hcell
    filter_upwards [hpull] with x hx
    have hpoint : (-a + x) + integerPoint q = x := by
      dsimp only [a]
      abel
    have hsignature := K.signature_add_integerPoint (-a + x) q
    rw [hpoint] at hsignature
    rw [hsignature, tilesUniverse_shiftFinset_iff]
    exact hx
  have hall : ∀ᵐ x ∂volume.restrict
      (⋃ q : IntegerPlane, translatedClosedUnitCell q),
      TilesUniverse (K.signature x) T :=
    (ae_restrict_iUnion_iff translatedClosedUnitCell
      (fun x ↦ TilesUniverse (K.signature x) T)).mpr htranslated
  simpa only [iUnion_translatedClosedUnitCell, Measure.restrict_univ] using hall

/-- Equality of every positive-measure signature carrier implies almost-everywhere equality of the
corresponding continuous integer-translation carriers. -/
theorem integerTranslationCarrier_ae_eq_of_relevantSignatures
    (K : PolygonalRegion) {T₀ T₁ : Set IntegerPlane}
    (hT : ∀ F ∈ K.relevantSignatures,
      discreteCarrier F T₀ = discreteCarrier F T₁) :
    K.integerTranslationCarrier T₀ =ᵐ[volume]
      K.integerTranslationCarrier T₁ := by
  have hcell : ∀ᵐ u ∂volume.restrict closedUnitCell,
      K.signature u ∈ K.relevantSignatures :=
    K.ae_signature_mem_relevantSignatures
  have htranslated : ∀ q : IntegerPlane,
      ∀ᵐ x ∂volume.restrict (translatedClosedUnitCell q),
        x ∈ K.integerTranslationCarrier T₀ ↔
          x ∈ K.integerTranslationCarrier T₁ := by
    intro q
    let a : Plane := integerPoint q
    have hmaps : Set.MapsTo (fun x : Plane ↦ -a + x)
        (translatedClosedUnitCell q) closedUnitCell := by
      intro x hx
      rw [translatedClosedUnitCell, Set.mem_vadd_set_iff_neg_vadd_mem] at hx
      simpa only [a, vadd_eq_add] using hx
    have hpull :=
      ((quasiMeasurePreserving_add_left volume (-a)).restrict hmaps).ae hcell
    filter_upwards [hpull] with x hxRelevant
    let u : Plane := -a + x
    have hcoordinate : x = u + integerPoint q := by
      dsimp only [u, a]
      abel
    rw [K.mem_integerTranslationCarrier_iff_mem_discreteCarrier_signature
      T₀ hcoordinate,
      K.mem_integerTranslationCarrier_iff_mem_discreteCarrier_signature
        T₁ hcoordinate]
    exact Set.ext_iff.mp (hT (K.signature u) hxRelevant) q
  have hall : ∀ᵐ x ∂volume.restrict
      (⋃ q : IntegerPlane, translatedClosedUnitCell q),
      x ∈ K.integerTranslationCarrier T₀ ↔
        x ∈ K.integerTranslationCarrier T₁ :=
    (ae_restrict_iUnion_iff translatedClosedUnitCell
      (fun x ↦ x ∈ K.integerTranslationCarrier T₀ ↔
        x ∈ K.integerTranslationCarrier T₁)).mpr htranslated
  have hall' : ∀ᵐ x ∂volume,
      x ∈ K.integerTranslationCarrier T₀ ↔
        x ∈ K.integerTranslationCarrier T₁ := by
    simpa only [iUnion_translatedClosedUnitCell, Measure.restrict_univ] using hall
  filter_upwards [hall'] with x hx
  exact propext hx

/-- Membership in a continuously placed tile is the corresponding raster-signature membership. -/
theorem mem_placedTile_integerPoint_iff_signature
    (K : PolygonalRegion) (u : Plane) (x t : IntegerPlane) :
    u + integerPoint x ∈
        placedTile K.prototileFamily (integerPoint t, ()) ↔
      x - t ∈ K.signature u := by
  rw [mem_signature_iff]
  change u + integerPoint x ∈ integerPoint t +ᵥ K.support ↔ _
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  have heq : -integerPoint t +ᵥ (u + integerPoint x) =
      u + integerPoint (x - t) := by
    rw [show integerPoint (x - t) = integerPoint x - integerPoint t by
      exact map_sub integerPointHom x t]
    simp only [vadd_eq_add]
    abel
  rw [heq]

/-- Exact discrete tiling by one signature is equivalent to unique continuous placement
representation on the full lattice orbit through `u`. -/
theorem signature_tilesUniverse_iff_unique_translation
    (K : PolygonalRegion) (u : Plane) (T : Set IntegerPlane) :
    TilesUniverse (K.signature u) T ↔
      ∀ x : IntegerPlane, ∃! t : IntegerPlane,
        t ∈ T ∧
          u + integerPoint x ∈
            placedTile K.prototileFamily (integerPoint t, ()) := by
  constructor
  · intro htiles x
    obtain ⟨f, hf, hfunique⟩ :=
      existsUnique_tile_representation htiles x
    let t : IntegerPlane := x - f
    refine ⟨t, ?_, ?_⟩
    · refine ⟨hf.2, ?_⟩
      rw [K.mem_placedTile_integerPoint_iff_signature]
      simpa only [t, sub_sub_cancel] using hf.1
    · intro s hs
      have hxs : x - s ∈ K.signature u :=
        (K.mem_placedTile_integerPoint_iff_signature u x s).mp hs.2
      have hchosen : f = x - s := (hfunique (x - s) ⟨hxs, by
        simpa only [sub_sub_cancel] using hs.1⟩).symm
      dsimp only [t]
      rw [hchosen]
      abel
  · intro hunique
    apply tilesUniverse_of_existsUnique
    intro x
    obtain ⟨t, ht, htunique⟩ := hunique x
    let f : IntegerPlane := x - t
    refine ⟨f, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact (K.mem_placedTile_integerPoint_iff_signature u x t).mp ht.2
      · simpa only [f, sub_sub_cancel] using ht.1
    · intro g hg
      let s : IntegerPlane := x - g
      have hs : s ∈ T ∧
          u + integerPoint x ∈
            placedTile K.prototileFamily (integerPoint s, ()) := by
        refine ⟨hg.2, ?_⟩
        rw [K.mem_placedTile_integerPoint_iff_signature]
        simpa only [s, sub_sub_cancel] using hg.1
      have hst : s = t := htunique s hs
      dsimp only [f, s] at hst ⊢
      rw [← hst]
      abel

/-- If all translation vectors are integral, record their unique integer coordinates. -/
def integerTranslationSet (T : Set Plane) : Set IntegerPlane :=
  {z | integerPoint z ∈ T}

@[simp]
theorem mem_integerTranslationSet_iff {T : Set Plane} {z : IntegerPlane} :
    z ∈ integerTranslationSet T ↔ integerPoint z ∈ T :=
  Iff.rfl

/-- An integral real translation set is exactly the image of its integer-coordinate set. -/
theorem integerPoint_image_integerTranslationSet {T : Set Plane}
    (hT : ∀ t ∈ T, IsIntegerPoint t) :
    integerPoint '' integerTranslationSet T = T := by
  ext t
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro ht
    obtain ⟨z, hz⟩ := mem_integerLattice_iff.mp (hT t ht)
    refine ⟨z, ?_, hz⟩
    change integerPoint z ∈ T
    rw [hz]
    exact ht

/-- A continuous tiling by integer translations induces, for almost every fundamental-cell point,
an exact discrete tiling by its finite signature. -/
theorem Tiles.ae_signature_tilesUniverse {K : PolygonalRegion}
    {T : Set IntegerPlane}
    (hT : K.Tiles (integerPoint '' T)) :
    ∀ᵐ u, TilesUniverse (K.signature u) T := by
  have hglobal := hT.ae_existsUnique_translation
  have horbits : ∀ᵐ u, ∀ x : IntegerPlane, ∃! r : Plane,
      r ∈ integerPoint '' T ∧
        u + integerPoint x ∈ placedTile K.prototileFamily (r, ()) := by
    rw [ae_all_iff]
    intro x
    have horbit :=
      (quasiMeasurePreserving_add_left volume (integerPoint x)).ae hglobal
    simpa only [add_comm] using horbit
  filter_upwards [horbits] with u hu
  apply (K.signature_tilesUniverse_iff_unique_translation u T).mpr
  intro y
  obtain ⟨r, hr, hrunique⟩ := hu y
  obtain ⟨t, htT, htr⟩ := hr.1
  refine ⟨t, ?_, ?_⟩
  · refine ⟨htT, ?_⟩
    simpa only [htr] using hr.2
  · intro s hs
    have hrs : integerPoint s = r := by
      apply hrunique (integerPoint s)
      exact ⟨⟨s, hs.1, rfl⟩, hs.2⟩
    exact integerPoint_injective (hrs.trans htr.symm)

/-- Conversely, almost-everywhere discrete tiling of the signatures reconstructs the continuous
integer-translation tiling. -/
theorem tiles_integerPoint_image_of_ae_signature_tilesUniverse
    (K : PolygonalRegion) {T : Set IntegerPlane}
    (hT : ∀ᵐ u, TilesUniverse (K.signature u) T) :
    K.Tiles (integerPoint '' T) := by
  have htranslations : (integerPoint '' T).Countable :=
    Set.to_countable T |>.image integerPoint
  refine ⟨placements_countable K htranslations, ?_, ?_⟩
  · intro p hp q hq hpq
    change p.1 ∈ integerPoint '' T at hp
    change q.1 ∈ integerPoint '' T at hq
    obtain ⟨t, ht, htp⟩ := hp
    obtain ⟨s, hs, hsq⟩ := hq
    change AEDisjoint volume
      (placedTile K.prototileFamily p)
      (placedTile K.prototileFamily q)
    change volume
      (placedTile K.prototileFamily p ∩
        placedTile K.prototileFamily q) = 0
    have hae : ∀ᵐ u,
        u ∉ placedTile K.prototileFamily p ∩
          placedTile K.prototileFamily q := by
      filter_upwards [hT] with u hu
      intro huinter
      obtain ⟨chosen, hchosen, hunique⟩ :=
        (K.signature_tilesUniverse_iff_unique_translation u T).mp hu 0
      have htPlaced : u + integerPoint 0 ∈
          placedTile K.prototileFamily (integerPoint t, ()) := by
        have hup := huinter.1
        change u ∈ p.1 +ᵥ K.support at hup
        change u + integerPoint 0 ∈ integerPoint t +ᵥ K.support
        simpa only [integerPoint_zero, add_zero, htp] using hup
      have hsPlaced : u + integerPoint 0 ∈
          placedTile K.prototileFamily (integerPoint s, ()) := by
        have huq := huinter.2
        change u ∈ q.1 +ᵥ K.support at huq
        change u + integerPoint 0 ∈ integerPoint s +ᵥ K.support
        simpa only [integerPoint_zero, add_zero, hsq] using huq
      have htchosen := hunique t ⟨ht, htPlaced⟩
      have hschosen := hunique s ⟨hs, hsPlaced⟩
      apply hpq
      apply Prod.ext
      · rw [← htp, ← hsq, htchosen, hschosen]
      · exact Subsingleton.elim _ _
    simpa only [not_not, Set.ofPred_mem_eq] using (ae_iff.mp hae)
  · filter_upwards [hT] with u hu
    obtain ⟨t, ht, -⟩ :=
      (K.signature_tilesUniverse_iff_unique_translation u T).mp hu 0
    let p : Placement Plane Unit := (integerPoint t, ())
    have hp : p ∈ K.placements (integerPoint '' T) :=
      ⟨t, ht.1, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨⟨p, hp⟩, ?_⟩
    simpa only [p, integerPoint_zero, add_zero] using ht.2

/-- The exact measure-theoretic raster bridge: continuous integer tilings are equivalent to
almost-everywhere simultaneous discrete tilings by their finite signatures. -/
theorem tiles_integerPoint_image_iff_ae_signature_tilesUniverse
    (K : PolygonalRegion) (T : Set IntegerPlane) :
    K.Tiles (integerPoint '' T) ↔
      ∀ᵐ u, TilesUniverse (K.signature u) T :=
  ⟨Tiles.ae_signature_tilesUniverse,
    K.tiles_integerPoint_image_of_ae_signature_tilesUniverse⟩

/-- Finite raster form of the continuous tiling equation: the integer translates tile the region
exactly when they tile every positive-measure fundamental-cell signature. -/
theorem tiles_integerPoint_image_iff_relevantSignatures
    (K : PolygonalRegion) (T : Set IntegerPlane) :
    K.Tiles (integerPoint '' T) ↔
      ∀ F ∈ K.relevantSignatures, TilesUniverse F T := by
  constructor
  · intro htiles
    exact K.tilesUniverse_relevantSignatures_of_ae
      htiles.ae_signature_tilesUniverse
  · intro hsignatures
    exact K.tiles_integerPoint_image_of_ae_signature_tilesUniverse
      (K.ae_signature_tilesUniverse_of_relevantSignatures hsignatures)

/-- An integer-vertex polygonal region that tiles continuously has an integer translation set,
and the same set tiles almost every raster signature. -/
theorem exists_integer_signature_tiling {K : PolygonalRegion}
    (hK : K.HasIntegerVertices) {T : Set Plane} (hT : K.Tiles T) :
    ∃ S : Set IntegerPlane,
      K.Tiles (integerPoint '' S) ∧
        ∀ᵐ u, TilesUniverse (K.signature u) S := by
  obtain ⟨T', hT'tiles, -, hT'integer⟩ := K.exists_integer_tiling hK hT
  let S := integerTranslationSet T'
  have himage : integerPoint '' S = T' :=
    integerPoint_image_integerTranslationSet hT'integer
  have htilesImage : K.Tiles (integerPoint '' S) := by
    rwa [himage]
  exact ⟨S, htilesImage, htilesImage.ae_signature_tilesUniverse⟩

end PolygonalRegion

end Tiling.RationalPolygonal
