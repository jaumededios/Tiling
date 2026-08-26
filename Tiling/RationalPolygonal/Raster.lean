import Tiling.RationalPolygonal.Earthquake
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

/-- Embed a discrete weak-periodic decomposition into the real plane. -/
noncomputable def integerPointWeakPeriodicDecomposition {A : Set IntegerPlane}
    (D : TranslationalTilings.WeakPeriodicDecomposition A) :
    WeakPeriodicDecomposition (integerPoint '' A) where
  numberOfParts := D.numberOfParts
  part i := integerPoint '' D.part i
  period i := integerPoint (D.period i)
  period_ne_zero i hzero :=
    D.period_ne_zero i (integerPoint_injective (hzero.trans integerPoint_zero.symm))
  periodic_part i := by
    intro x
    constructor
    · rintro ⟨a, ha, hax⟩
      have ha' : a - D.period i ∈ D.part i := by
        apply (D.periodic_part i (a - D.period i)).mp
        simpa only [sub_add_cancel] using ha
      refine ⟨a - D.period i, ha', ?_⟩
      rw [integerPoint_sub, hax]
      abel
    · rintro ⟨a, ha, rfl⟩
      have ha' : a + D.period i ∈ D.part i :=
        (D.periodic_part i a).mpr ha
      exact ⟨a + D.period i, ha', integerPoint_add a (D.period i)⟩
  pairwiseDisjoint := by
    intro i _ j _ hij
    change Disjoint (integerPoint '' D.part i) (integerPoint '' D.part j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨a, ha, hax⟩ := hxi
    obtain ⟨b, hb, hbx⟩ := hxj
    have hab : a = b := integerPoint_injective (hax.trans hbx.symm)
    subst b
    exact (Set.disjoint_left.mp
      (D.pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij)) ha hb
  iUnion_parts := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, hai, rfl⟩ := hxi
      refine ⟨a, ?_, rfl⟩
      rw [← D.iUnion_parts]
      exact Set.mem_iUnion.mpr ⟨i, hai⟩
    · rintro ⟨a, ha, rfl⟩
      rw [← D.iUnion_parts] at ha
      obtain ⟨i, hai⟩ := Set.mem_iUnion.mp ha
      exact Set.mem_iUnion.mpr ⟨i, ⟨a, hai, rfl⟩⟩

/-- Discrete weak periodicity becomes weak periodicity by real translation vectors. -/
theorem weaklyPeriodic_integerPoint_image {A : Set IntegerPlane}
    (hA : TranslationalTilings.WeaklyPeriodic A) :
    WeaklyPeriodic (integerPoint '' A) := by
  obtain ⟨D⟩ := hA
  exact ⟨integerPointWeakPeriodicDecomposition D⟩

namespace PolygonalRegion

/-- Every continuous tiling by integer translations is weakly periodic.  This is the immediate
consequence of the raster lemma and Greenfeld--Tao noted before the earthquake argument. -/
theorem Tiles.weaklyPeriodic_of_integerPoint_image
    {K : PolygonalRegion} {T : Set IntegerPlane}
    (hT : K.Tiles (integerPoint '' T)) :
    WeaklyPeriodic (integerPoint '' T) := by
  have hsignatures := hT.ae_signature_tilesUniverse
  obtain ⟨u, hu⟩ := hsignatures.exists
  obtain ⟨f, hf, -⟩ := existsUnique_tile_representation hu 0
  exact weaklyPeriodic_integerPoint_image
    (tilesUniverse_weaklyPeriodic ⟨f, hf.1⟩ hu)

end PolygonalRegion

namespace RationalPolygonalRegion

/-- Every rational polygonal region which tiles admits a weakly periodic tiling.  This endpoint
uses rational normalization, connected integer reduction, the raster bridge, and Greenfeld--Tao,
then transports the resulting decomposition back to the original scale. -/
theorem exists_weaklyPeriodic_tiling (K : RationalPolygonalRegion)
    {T : Set Plane} (hT : K.toPolygonalRegion.Tiles T) :
    ∃ S : Set Plane, K.toPolygonalRegion.Tiles S ∧ WeaklyPeriodic S := by
  have hnormalized := K.normalizedRegion_tiles hT
  obtain ⟨T', hT'tiles, -, hT'integer⟩ :=
    K.normalizedRegion.exists_integer_tiling
      K.normalizedRegion_hasIntegerVertices hnormalized
  let Z := PolygonalRegion.integerTranslationSet T'
  have himage : integerPoint '' Z = T' :=
    PolygonalRegion.integerPoint_image_integerTranslationSet hT'integer
  have hT'image : K.normalizedRegion.Tiles (integerPoint '' Z) := by
    rwa [himage]
  have hweakImage := hT'image.weaklyPeriodic_of_integerPoint_image
  have hweakT' : WeaklyPeriodic T' := by
    rwa [himage] at hweakImage
  refine ⟨K.denormalizedTranslations T',
    K.tiles_of_normalizedRegion_tiles hT'tiles, ?_⟩
  exact K.weaklyPeriodic_denormalizedTranslations hweakT'

end RationalPolygonalRegion

end Tiling.RationalPolygonal
