import Tiling.RationalSlopes.Parametrization
import Tiling.AxisParallel.Terminal.DiscreteFinerStructure
import Tiling.RationalPolygonal.RasterMarker

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.RationalSlopes

open Tiling.RationalPolygonal (PolygonalRegion IntegerPlane integerPoint)
open Tiling.Polygonal

def LiesInRationalMeshCoset (T : Set Plane) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∃ a : Plane,
    T ⊆ a +ᵥ {z : Plane | ∃ p : IntegerPlane, z = (d : ℝ)⁻¹ • integerPoint p}

/-- The meaningful rational output before lifting: original parts, entire line fibres,
integer coefficient periods, and exact regular-support transport across transverse phases. -/
structure RationalSliceParametrization (K : PolygonalRegion) (T : Set Plane) where
  lattice : PlanarLattice
  basis_rational : ∀ j, ∃ q : Fin 2 → ℚ,
    lattice.basis j = Complex.mk (q 0) (q 1)
  numberOfParts : ℕ
  part : Fin numberOfParts → Set Plane
  part_nonempty : ∀ i, (part i).Nonempty
  parts_disjoint : Set.PairwiseDisjoint Set.univ part
  union_parts : (⋃ i, part i) = T
  direction : Fin numberOfParts → Submodule ℝ Plane
  direction_dim : ∀ i, Module.finrank ℝ (direction i) = 1
  lambdaCoefficient : Fin numberOfParts → ℤ
  gammaCoefficient : Fin numberOfParts → ℤ
  lambdaCoefficient_ne_zero : ∀ i, lambdaCoefficient i ≠ 0
  within_mem : ∀ i,
    lambdaCoefficient i • lattice.basis 0 + gammaCoefficient i • lattice.basis 1 ∈
      direction i
  fibre_period : ∀ i t, t ∈ part i →
    lambdaCoefficient i • lattice.basis 0 + gammaCoefficient i • lattice.basis 1 ∈
      periodGroup (lineFibre (direction i) (part i) t)
  fibre_transport : ∀ i t, t ∈ part i → ∀ m : ℤ,
    ∃ s ∈ part i, s - t - m • lattice.basis 1 ∈ direction i ∧
      regularSupport K (lineFibre (direction i) (part i) s) =
        m • lattice.basis 1 +ᵥ regularSupport K (lineFibre (direction i) (part i) t)

private theorem convolution_le_one_iff_no_duplicate_rsHelper
    {G : Type*} [AddCommGroup G] (F : Finset G) (A : Set G) :
    (∀ x : G, TranslationalTilings.tileConv F
      (TranslationalTilings.setIndicator A) x ≤ 1) ↔
    ∀ x f g : G, f ∈ F → x - f ∈ A → g ∈ F → x - g ∈ A → f = g := by
  classical
  constructor
  · intro h x f g hf hfa hg hga
    have hcardZ : ((F.filter fun q ↦ x - q ∈ A).card : ℤ) ≤ 1 := by
      rw [← TranslationalTilings.tileConv_indicator_eq_card]
      exact h x
    have hcard : (F.filter fun q ↦ x - q ∈ A).card ≤ 1 := by
      exact_mod_cast hcardZ
    have hunique := Finset.card_le_one.mp hcard
    exact hunique f (Finset.mem_filter.mpr ⟨hf, hfa⟩)
      g (Finset.mem_filter.mpr ⟨hg, hga⟩)
  · intro h x
    have hcard : (F.filter fun q ↦ x - q ∈ A).card ≤ 1 :=
      Finset.card_le_one.mpr (by
        intro f hf g hg
        exact h x f g (Finset.mem_filter.mp hf).1 (Finset.mem_filter.mp hf).2
          (Finset.mem_filter.mp hg).1 (Finset.mem_filter.mp hg).2)
    rw [TranslationalTilings.tileConv_indicator_eq_card]
    exact_mod_cast hcard

private theorem tiles_ownDiscreteCarrier_iff_convolution_le_one_rsHelper
    {G : Type*} [AddCommGroup G] (F : Finset G) (A : Set G) :
    TranslationalTilings.Tiles F A
      (Tiling.RationalPolygonal.discreteCarrier F A) ↔
      ∀ x : G, TranslationalTilings.tileConv F
        (TranslationalTilings.setIndicator A) x ≤ 1 := by
  classical
  constructor
  · intro hTile x
    rw [TranslationalTilings.tileConv_indicator_eq_card]
    have h := hTile x
    rw [TranslationalTilings.tileConv_indicator_eq_card] at h
    by_cases hx : x ∈ Tiling.RationalPolygonal.discreteCarrier F A
    · simp only [TranslationalTilings.setIndicator, Set.indicator_of_mem hx,
        mul_one] at h
      exact h.le
    · simp only [TranslationalTilings.setIndicator, Set.indicator_of_notMem hx,
        mul_zero] at h
      omega
  · intro h
    apply (TranslationalTilings.tilesAtLevel_iff_representation_count
      F A (Tiling.RationalPolygonal.discreteCarrier F A) 1).mpr
    intro x
    have hle :
        ((F.filter fun f ↦ x - f ∈ A).card : ℤ) ≤ 1 := by
      rw [← TranslationalTilings.tileConv_indicator_eq_card]
      exact h x
    by_cases hx : x ∈ Tiling.RationalPolygonal.discreteCarrier F A
    · have hpos : 0 < (F.filter fun f ↦ x - f ∈ A).card := by
        apply Finset.card_pos.mpr
        obtain ⟨f, hfF, a, haA, hxa⟩ :=
          Tiling.RationalPolygonal.mem_discreteCarrier_iff.mp hx
        refine ⟨f, Finset.mem_filter.mpr ⟨hfF, ?_⟩⟩
        rw [hxa]
        simp only [add_sub_cancel_left]
        exact haA
      have hleNat : (F.filter fun f ↦ x - f ∈ A).card ≤ 1 := by
        exact_mod_cast hle
      have hcard : (F.filter fun f ↦ x - f ∈ A).card = 1 := by
        omega
      simp [hx, hcard]
    · have hempty : F.filter (fun f ↦ x - f ∈ A) = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨f, hf⟩
        have hf' := Finset.mem_filter.mp hf
        apply hx
        refine ⟨f, hf'.1, x - f, hf'.2, ?_⟩
        abel
      simp [hempty, hx]

private theorem planarRaster_convolution_le_one_iff_family_rsHelper
    {M : ℕ} (hM : 0 < M) (tile : Fin M → Finset IntegerPlane)
    (A : Set IntegerPlane) :
    (∀ X : IntegerPlane, TranslationalTilings.tileConv
      (Tiling.RationalPolygonal.planarRasterTile tile)
      (TranslationalTilings.setIndicator
        (Tiling.RationalPolygonal.markerTranslationSet M A)) X ≤ 1) ↔
    ∀ i : Fin M, ∀ q : IntegerPlane, TranslationalTilings.tileConv
      (tile i) (TranslationalTilings.setIndicator A) q ≤ 1 := by
  classical
  constructor
  · intro h i q
    apply (convolution_le_one_iff_no_duplicate_rsHelper (tile i) A).2
    intro q' f g hf hfa hg hga
    obtain ⟨s, hs⟩ := Tiling.RationalPolygonal.markerBlock_nonempty hM i
    let X := Tiling.RationalPolygonal.markerScale M q' + s
    let r₁ := Tiling.RationalPolygonal.markerScale M f + s
    let r₂ := Tiling.RationalPolygonal.markerScale M g + s
    have hr₁ : r₁ ∈ Tiling.RationalPolygonal.planarRasterTile tile :=
      Tiling.RationalPolygonal.mem_planarRasterTile_iff.mpr
        ⟨i, f, hf, s, hs, rfl⟩
    have hr₂ : r₂ ∈ Tiling.RationalPolygonal.planarRasterTile tile :=
      Tiling.RationalPolygonal.mem_planarRasterTile_iff.mpr
        ⟨i, g, hg, s, hs, rfl⟩
    have hX₁ : X = r₁ + Tiling.RationalPolygonal.markerScale M (q' - f) := by
      dsimp [X, r₁]
      rw [Tiling.RationalPolygonal.markerScale_sub]
      abel
    have hX₂ : X = r₂ + Tiling.RationalPolygonal.markerScale M (q' - g) := by
      dsimp [X, r₂]
      rw [Tiling.RationalPolygonal.markerScale_sub]
      abel
    have hu₁ : X - r₁ ∈
        Tiling.RationalPolygonal.markerTranslationSet M A := by
      rw [show X - r₁ = Tiling.RationalPolygonal.markerScale M (q' - f) by
        rw [hX₁]
        abel]
      exact ⟨q' - f, hfa, rfl⟩
    have hu₂ : X - r₂ ∈
        Tiling.RationalPolygonal.markerTranslationSet M A := by
      rw [show X - r₂ = Tiling.RationalPolygonal.markerScale M (q' - g) by
        rw [hX₂]
        abel]
      exact ⟨q' - g, hga, rfl⟩
    have huniq :=
      (convolution_le_one_iff_no_duplicate_rsHelper
        (Tiling.RationalPolygonal.planarRasterTile tile)
        (Tiling.RationalPolygonal.markerTranslationSet M A)).mp h
    have hrEq := huniq X r₁ r₂ hr₁ hu₁ hr₂ hu₂
    have hscale : Tiling.RationalPolygonal.markerScale M f =
        Tiling.RationalPolygonal.markerScale M g := by
      dsimp [r₁, r₂] at hrEq
      exact add_right_cancel hrEq
    exact Tiling.RationalPolygonal.markerScale_injective M hscale
  · intro h
    apply (convolution_le_one_iff_no_duplicate_rsHelper
      (Tiling.RationalPolygonal.planarRasterTile tile)
      (Tiling.RationalPolygonal.markerTranslationSet M A)).2
    intro X r r' hr hrT hr' hr'T
    obtain ⟨i, f, hf, s, hs, rfl⟩ :=
      Tiling.RationalPolygonal.mem_planarRasterTile_iff.mp hr
    obtain ⟨t, ht, htEq⟩ :=
      Tiling.RationalPolygonal.mem_markerTranslationSet_iff.mp hrT
    obtain ⟨j, g, hg, s', hs', rfl⟩ :=
      Tiling.RationalPolygonal.mem_planarRasterTile_iff.mp hr'
    obtain ⟨u, hu, huEq⟩ :=
      Tiling.RationalPolygonal.mem_markerTranslationSet_iff.mp hr'T
    have hX₁ : X = Tiling.RationalPolygonal.markerScale M (f + t) + s := by
      calc
        X = (Tiling.RationalPolygonal.markerScale M f + s) +
            (X - (Tiling.RationalPolygonal.markerScale M f + s)) := by abel
        _ = (Tiling.RationalPolygonal.markerScale M f + s) +
            Tiling.RationalPolygonal.markerScale M t := by rw [htEq]
        _ = Tiling.RationalPolygonal.markerScale M (f + t) + s := by
          rw [Tiling.RationalPolygonal.markerScale_add]
          abel
    have hX₂ : X = Tiling.RationalPolygonal.markerScale M (g + u) + s' := by
      calc
        X = (Tiling.RationalPolygonal.markerScale M g + s') +
            (X - (Tiling.RationalPolygonal.markerScale M g + s')) := by abel
        _ = (Tiling.RationalPolygonal.markerScale M g + s') +
            Tiling.RationalPolygonal.markerScale M u := by rw [huEq]
        _ = Tiling.RationalPolygonal.markerScale M (g + u) + s' := by
          rw [Tiling.RationalPolygonal.markerScale_add]
          abel
    have hsModified : s ∈ Tiling.RationalPolygonal.modifiedMarkerSquare M := by
      rw [← Tiling.RationalPolygonal.markerUnion_eq_modifiedMarkerSquare hM,
        Tiling.RationalPolygonal.markerUnion, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ i, hs⟩
    have hs'Modified : s' ∈ Tiling.RationalPolygonal.modifiedMarkerSquare M := by
      rw [← Tiling.RationalPolygonal.markerUnion_eq_modifiedMarkerSquare hM,
        Tiling.RationalPolygonal.markerUnion, Finset.mem_biUnion]
      exact ⟨j, Finset.mem_univ j, hs'⟩
    have hXSubS : X - s ∈ Tiling.RationalPolygonal.markerLattice M := by
      rw [Tiling.RationalPolygonal.mem_markerLattice_iff]
      refine ⟨f + t, ?_⟩
      rw [hX₁]
      abel
    have hXSubS' : X - s' ∈ Tiling.RationalPolygonal.markerLattice M := by
      rw [Tiling.RationalPolygonal.mem_markerLattice_iff]
      refine ⟨g + u, ?_⟩
      rw [hX₂]
      abel
    obtain ⟨chosen, hchosen, hchosenUnique⟩ :=
      Tiling.RationalPolygonal.existsUnique_tile_representation
        (Tiling.RationalPolygonal.modifiedMarkerSquare_tiles_markerLattice M) X
    have hss' : s = s' :=
      (hchosenUnique s ⟨hsModified, hXSubS⟩).trans
        (hchosenUnique s' ⟨hs'Modified, hXSubS'⟩).symm
    have hij : i = j := by
      by_contra hij
      have hnot : s ∉ Tiling.RationalPolygonal.markerBlock j :=
        Finset.disjoint_left.mp
          (Tiling.RationalPolygonal.markerBlock_disjoint hij) hs
      exact hnot (hss' ▸ hs')
    subst j
    have hscale : Tiling.RationalPolygonal.markerScale M (f + t) =
        Tiling.RationalPolygonal.markerScale M (g + u) := by
      have hX₂' : X = Tiling.RationalPolygonal.markerScale M (g + u) + s := by
        calc
          X = Tiling.RationalPolygonal.markerScale M (g + u) + s' := hX₂
          _ = Tiling.RationalPolygonal.markerScale M (g + u) + s := by
            rw [hss'.symm]
      exact add_right_cancel (hX₁.symm.trans hX₂')
    have hsum : f + t = g + u :=
      Tiling.RationalPolygonal.markerScale_injective M hscale
    have hfg :=
      ((convolution_le_one_iff_no_duplicate_rsHelper (tile i) A).mp (h i))
        (f + t) f g hf (by simpa using ht) hg (by
          have hqg : (f + t) - g = u := by
            calc
              (f + t) - g = (g + u) - g := by rw [hsum]
              _ = u := add_sub_cancel_left g u
          rw [hqg]
          exact hu)
    have htu : t = u := by
      rw [hfg] at hsum
      exact add_left_cancel hsum
    simp [hfg, hss']

private theorem relevantPlanarSignature_counts_iff_relevant_rsHelper
    (K : PolygonalRegion) (A : Set IntegerPlane) :
    (∀ i : Fin K.relevantSignatureCount, ∀ z : IntegerPlane,
      TranslationalTilings.tileConv (K.relevantPlanarSignatureAt i)
        (TranslationalTilings.setIndicator A) z ≤ 1) ↔
    ∀ F ∈ K.relevantSignatures, ∀ z : IntegerPlane,
      TranslationalTilings.tileConv F (TranslationalTilings.setIndicator A) z ≤ 1 := by
  constructor
  · intro h F hF z
    obtain ⟨j, hj⟩ := K.exists_relevantSignatureAt_eq hF
    let i := K.relevantPlanarSignaturePermutation.symm j
    have hperm : K.relevantPlanarSignaturePermutation i = j :=
      K.relevantPlanarSignaturePermutation.apply_symm_apply j
    rw [← hj]
    have hisig : K.relevantPlanarSignatureAt i = K.relevantSignatureAt j := by
      rw [Tiling.RationalPolygonal.PolygonalRegion.relevantPlanarSignatureAt, hperm]
    rw [← hisig]
    exact h i z
  · intro h i z
    exact h (K.relevantPlanarSignatureAt i)
      (K.relevantSignatureAt_mem (K.relevantPlanarSignaturePermutation i)) z

private theorem relevantRaster_tiles_ownCarrier_iff_signatureCounts_rsHelper
    (K : PolygonalRegion) (A : Set IntegerPlane) :
    TranslationalTilings.Tiles K.relevantPlanarRasterTile
      (Tiling.RationalPolygonal.markerTranslationSet K.relevantSignatureCount A)
      (Tiling.RationalPolygonal.discreteCarrier K.relevantPlanarRasterTile
        (Tiling.RationalPolygonal.markerTranslationSet K.relevantSignatureCount A)) ↔
    ∀ F ∈ K.relevantSignatures, ∀ z : IntegerPlane,
      TranslationalTilings.tileConv F (TranslationalTilings.setIndicator A) z ≤ 1 := by
  change TranslationalTilings.Tiles
    (Tiling.RationalPolygonal.planarRasterTile K.relevantPlanarSignatureAt)
    (Tiling.RationalPolygonal.markerTranslationSet K.relevantSignatureCount A)
    (Tiling.RationalPolygonal.discreteCarrier
      (Tiling.RationalPolygonal.planarRasterTile K.relevantPlanarSignatureAt)
      (Tiling.RationalPolygonal.markerTranslationSet K.relevantSignatureCount A)) ↔ _
  rw [tiles_ownDiscreteCarrier_iff_convolution_le_one_rsHelper,
    planarRaster_convolution_le_one_iff_family_rsHelper K.relevantSignatureCount_pos,
    relevantPlanarSignature_counts_iff_relevant_rsHelper]

private theorem integerPacking_iff_signatureCounts_measure_rsHelper
    (K : PolygonalRegion) (A : Set IntegerPlane) :
    IsPacking K.prototileFamily (K.placements (integerPoint '' A)) ↔
      ∀ F ∈ K.relevantSignatures, ∀ z : IntegerPlane,
        TranslationalTilings.tileConv F (TranslationalTilings.setIndicator A) z ≤ 1 := by
  classical
  constructor
  · intro hpacking F hF z
    apply (convolution_le_one_iff_no_duplicate_rsHelper F A).2
    intro z' f g hf hfA hg hgA
    by_contra hfg
    let t : IntegerPlane := z' - f
    let s : IntegerPlane := z' - g
    have htA : t ∈ A := by simpa [t] using hfA
    have hsA : s ∈ A := by simpa [s] using hgA
    have hts : t ≠ s := by
      intro hts
      apply hfg
      have hzt : z' - t = f := by dsimp [t]; abel
      have hzs : z' - s = g := by dsimp [s]; abel
      calc
        f = z' - t := hzt.symm
        _ = z' - s := by rw [hts]
        _ = g := hzs
    have hpt : (integerPoint t, ()) ∈ K.placements (integerPoint '' A) :=
      ⟨t, htA, rfl⟩
    have hps : (integerPoint s, ()) ∈ K.placements (integerPoint '' A) :=
      ⟨s, hsA, rfl⟩
    have hplacementsNe : (integerPoint t, ()) ≠ (integerPoint s, ()) := by
      intro hpEq
      apply hts
      exact Tiling.RationalPolygonal.integerPoint_injective
        (congrArg Prod.fst hpEq)
    have hdisjoint := hpacking hpt hps hplacementsNe
    change volume
      (placedTile K.prototileFamily (integerPoint t, ()) ∩
        placedTile K.prototileFamily (integerPoint s, ())) = 0 at hdisjoint
    have hfiberSubset : integerPoint z' +ᵥ K.signatureFiber F ⊆
        placedTile K.prototileFamily (integerPoint t, ()) ∩
          placedTile K.prototileFamily (integerPoint s, ()) := by
      intro x hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
      let u : Plane := -integerPoint z' + x
      have hxu : x = integerPoint z' + u := by dsimp [u]; abel
      have huFiber : u ∈ K.signatureFiber F := by
        change -integerPoint z' + x ∈ K.signatureFiber F
        exact hx
      have huSig : K.signature u = F :=
        (K.mem_signatureFiber_iff.mp huFiber).2
      have hfSig : f ∈ K.signature u := by rw [huSig]; exact hf
      have hgSig : g ∈ K.signature u := by rw [huSig]; exact hg
      have hfSupport : u + integerPoint f ∈ K.support :=
        K.mem_signature_iff.mp hfSig
      have hgSupport : u + integerPoint g ∈ K.support :=
        K.mem_signature_iff.mp hgSig
      have hzt : z' = t + f := by dsimp [t]; abel
      have hzs : z' = s + g := by dsimp [s]; abel
      constructor
      · change x ∈ integerPoint t +ᵥ K.support
        rw [hxu, hzt, Tiling.RationalPolygonal.integerPoint_add]
        have hrewrite : -integerPoint t +
            (integerPoint t + integerPoint f + u) = u + integerPoint f := by abel
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simp only [vadd_eq_add]
        simpa only [hxu, hzt, Tiling.RationalPolygonal.integerPoint_add] using
          (show -integerPoint t +
              (integerPoint t + integerPoint f + u) ∈ K.support by
            rw [hrewrite]
            exact hfSupport)
      · change x ∈ integerPoint s +ᵥ K.support
        rw [hxu, hzs, Tiling.RationalPolygonal.integerPoint_add]
        have hrewrite : -integerPoint s +
            (integerPoint s + integerPoint g + u) = u + integerPoint g := by abel
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simp only [vadd_eq_add]
        simpa only [hxu, hzs, Tiling.RationalPolygonal.integerPoint_add] using
          (show -integerPoint s +
              (integerPoint s + integerPoint g + u) ∈ K.support by
            rw [hrewrite]
            exact hgSupport)
    have htranslatedZero : volume (integerPoint z' +ᵥ K.signatureFiber F) = 0 :=
      measure_mono_null hfiberSubset hdisjoint
    have hfiberZero : volume (K.signatureFiber F) = 0 := by
      simpa only [measure_vadd] using htranslatedZero
    exact ((K.mem_relevantSignatures_iff.mp hF).2) hfiberZero
  · intro hcounts p hp q hq hpq
    change p.1 ∈ integerPoint '' A at hp
    change q.1 ∈ integerPoint '' A at hq
    obtain ⟨t, ht, htp⟩ := hp
    obtain ⟨s, hs, hsq⟩ := hq
    change AEDisjoint volume
      (placedTile K.prototileFamily p)
      (placedTile K.prototileFamily q)
    change volume
      (placedTile K.prototileFamily p ∩
        placedTile K.prototileFamily q) = 0
    have hae : ∀ᵐ x,
        x ∉ placedTile K.prototileFamily p ∩
          placedTile K.prototileFamily q := by
      have htranslated : ∀ z : IntegerPlane,
          ∀ᵐ x ∂volume.restrict
            (Tiling.RationalPolygonal.translatedClosedUnitCell z),
            x ∉ placedTile K.prototileFamily p ∩
              placedTile K.prototileFamily q := by
        intro z
        let a : Plane := integerPoint z
        have hmaps : Set.MapsTo (fun x : Plane ↦ -a + x)
            (Tiling.RationalPolygonal.translatedClosedUnitCell z)
            Tiling.RationalPolygonal.closedUnitCell := by
          intro x hx
          rw [Tiling.RationalPolygonal.translatedClosedUnitCell,
            Set.mem_vadd_set_iff_neg_vadd_mem] at hx
          simpa only [a, vadd_eq_add] using hx
        have hpull :=
          ((quasiMeasurePreserving_add_left volume (-a)).restrict hmaps).ae
            K.ae_signature_mem_relevantSignatures
        filter_upwards [hpull] with x hrel
        intro hxIntersect
        let u : Plane := -a + x
        have hpoint : x = u + integerPoint z := by
          dsimp [u, a]
          abel
        have hplacedT : u + integerPoint z ∈
            placedTile K.prototileFamily (integerPoint t, ()) := by
          have hmem := hxIntersect.1
          change x ∈ p.1 +ᵥ K.support at hmem
          change u + integerPoint z ∈ integerPoint t +ᵥ K.support
          rw [hpoint, ← htp] at hmem
          exact hmem
        have hplacedS : u + integerPoint z ∈
            placedTile K.prototileFamily (integerPoint s, ()) := by
          have hmem := hxIntersect.2
          change x ∈ q.1 +ᵥ K.support at hmem
          change u + integerPoint z ∈ integerPoint s +ᵥ K.support
          rw [hpoint, ← hsq] at hmem
          exact hmem
        have htSig : z - t ∈ K.signature u :=
          (K.mem_placedTile_integerPoint_iff_signature u z t).mp hplacedT
        have hsSig : z - s ∈ K.signature u :=
          (K.mem_placedTile_integerPoint_iff_signature u z s).mp hplacedS
        have huniq :=
          (convolution_le_one_iff_no_duplicate_rsHelper (K.signature u) A).mp
            (hcounts (K.signature u) hrel) z (z - t) (z - s) htSig
              (by simpa using ht) hsSig (by simpa using hs)
        have hts : t = s := by
          have hsub : z - t = z - s := huniq
          calc
            t = z - (z - t) := by abel
            _ = z - (z - s) := by rw [hsub]
            _ = s := by abel
        apply hpq
        apply Prod.ext
        · rw [← htp, ← hsq, hts]
        · exact Subsingleton.elim _ _
      have hall : ∀ᵐ x ∂volume.restrict
          (⋃ z : IntegerPlane,
            Tiling.RationalPolygonal.translatedClosedUnitCell z),
          x ∉ placedTile K.prototileFamily p ∩
            placedTile K.prototileFamily q :=
        (ae_restrict_iUnion_iff Tiling.RationalPolygonal.translatedClosedUnitCell
          (fun x ↦ x ∉ placedTile K.prototileFamily p ∩
            placedTile K.prototileFamily q)).mpr htranslated
      have hall' : ∀ᵐ x ∂volume,
          x ∉ placedTile K.prototileFamily p ∩
            placedTile K.prototileFamily q := by
        simpa only [Tiling.RationalPolygonal.iUnion_translatedClosedUnitCell,
          Measure.restrict_univ] using hall
      exact hall'
    simpa only [not_not, Set.ofPred_mem_eq] using (ae_iff.mp hae)


private theorem rationalPoint_has_integer_multiple_rsHelper {x : Plane}
    (hx : Tiling.IsRationalPoint x) :
    ∃ n : ℕ, 0 < n ∧ ∃ z : IntegerPlane,
      (n : ℝ) • x = integerPoint z := by
  rcases hx with ⟨r, s, hr, hs⟩
  let n : ℕ := r.den * s.den
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.mul_pos (Rat.den_pos _) (Rat.den_pos _)
  refine ⟨n, hn, ![r.num * s.den, s.num * r.den], ?_⟩
  apply Complex.ext
  · rw [Tiling.RationalPolygonal.integerPoint_re]
    simp only [Complex.smul_re, smul_eq_mul]
    change (n : ℝ) * x.re = ((r.num * s.den : ℤ) : ℝ)
    rw [hr]
    have hRrat : (n : ℚ) * r = (r.num * s.den : ℤ) := by
      dsimp [n]
      calc
        ((r.den * s.den : ℕ) : ℚ) * r =
            (r.den : ℚ) * r * (s.den : ℚ) := by push_cast; ring
        _ = (r.num : ℚ) * (s.den : ℚ) := by rw [Rat.den_mul_eq_num]
        _ = ((r.num * s.den : ℤ) : ℚ) := by norm_cast
    exact_mod_cast hRrat
  · rw [Tiling.RationalPolygonal.integerPoint_im]
    simp only [Complex.smul_im, smul_eq_mul]
    change (n : ℝ) * x.im = ((s.num * r.den : ℤ) : ℝ)
    rw [hs]
    have hIrat : (n : ℚ) * s = (s.num * r.den : ℤ) := by
      dsimp [n]
      calc
        ((r.den * s.den : ℕ) : ℚ) * s =
            (s.den : ℚ) * s * (r.den : ℚ) := by push_cast; ring
        _ = (s.num : ℚ) * (r.den : ℚ) := by rw [Rat.den_mul_eq_num]
        _ = ((s.num * r.den : ℤ) : ℚ) := by norm_cast
    exact_mod_cast hIrat

private def integerDeterminant_rsHelper (p q : IntegerPlane) : ℤ :=
  p 0 * q 1 - p 1 * q 0

private theorem integerPeriod_contains_scalar_rsHelper
    (H : AddSubgroup Plane) (p q : IntegerPlane)
    (hp : integerPoint p ∈ H) (hq : integerPoint q ∈ H)
    (hdet : integerDeterminant_rsHelper p q ≠ 0) :
    ∃ ell : ℕ, 0 < ell ∧ ∀ z : IntegerPlane,
      integerPoint ((ell : ℤ) • z) ∈ H := by
  let D := integerDeterminant_rsHelper p q
  let a (z : IntegerPlane) : ℤ := q 1 * z 0 - q 0 * z 1
  let b (z : IntegerPlane) : ℤ := -p 1 * z 0 + p 0 * z 1
  have hD : D ≠ 0 := hdet
  have hcomb (z : IntegerPlane) : D • z = a z • p + b z • q := by
    ext i
    fin_cases i <;> simp [D, a, b, integerDeterminant_rsHelper] <;> ring
  have hmembership (z : IntegerPlane) : integerPoint (D • z) ∈ H := by
    rw [hcomb]
    have h₁ : (a z : ℤ) • integerPoint p ∈ H := H.zsmul_mem hp (a z)
    have h₂ : (b z : ℤ) • integerPoint q ∈ H := H.zsmul_mem hq (b z)
    have hsum := H.add_mem h₁ h₂
    have hmap : integerPoint (a z • p + b z • q) =
        (a z : ℤ) • integerPoint p + (b z : ℤ) • integerPoint q := by
      change Tiling.RationalPolygonal.integerPointHom (a z • p + b z • q) = _
      rw [map_add, map_zsmul, map_zsmul,
        Tiling.RationalPolygonal.integerPointHom_apply,
        Tiling.RationalPolygonal.integerPointHom_apply]
    rw [hmap]
    exact hsum
  let ell : ℕ := D.natAbs
  have hell : 0 < ell := by
    dsimp [ell]
    exact Int.natAbs_pos.mpr hD
  refine ⟨ell, hell, ?_⟩
  intro z
  by_cases hpositive : 0 < D
  · have hcast : (ell : ℤ) = D := by
      dsimp [ell]
      exact Int.natAbs_of_nonneg (le_of_lt hpositive)
    rw [hcast]
    exact hmembership z
  · have hnegative : D < 0 := lt_of_le_of_ne (le_of_not_gt hpositive) hD
    have hcast : (ell : ℤ) = -D := by
      have hcast' : ((-D).natAbs : ℤ) = -D :=
        Int.natAbs_of_nonneg (show 0 ≤ -D by omega)
      simpa [ell] using hcast'
    rw [hcast, neg_zsmul]
    have hneg : integerPoint (-(D • z)) ∈ H := by
      have hmap : integerPoint (-(D • z)) = -integerPoint (D • z) := by
        change Tiling.RationalPolygonal.integerPointHom (-(D • z)) = _
        rw [map_neg, Tiling.RationalPolygonal.integerPointHom_apply]
      rw [hmap]
      exact H.neg_mem (hmembership z)
    exact hneg

-- RP1 rational geometry helpers; imported predecessor closures remain provisional.
private theorem rp1_rational_isRelativelyRational (K : PolygonalRegion)
    (hK : IsRational K.support) : Tiling.RationalPolygonal.IsRelativelyRational K := by
  have hproper : K.support ≠ Set.univ := by
    obtain ⟨B, hB, hb⟩ := K.isPolygonal.isCompact.isBounded.exists_pos_norm_le
    intro heq
    have h := hb ((B + 1 : ℝ) : Plane) (heq.symm ▸ Set.mem_univ _)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < B + 1)] at h
    linarith
  obtain ⟨x, hx⟩ := nonempty_frontier_iff.mpr ⟨K.nonempty, hproper⟩
  obtain ⟨F, hF, hfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  rw [hfront] at hx
  obtain ⟨e, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨he, _⟩ := Set.mem_iUnion.mp hx
  refine ⟨e.1, (hF e he).2.1, ?_⟩
  intro w hw
  obtain ⟨r, s, hr, hs⟩ := hK.2 w hw
  obtain ⟨u, v, hu, hv⟩ := hK.2 e.1 (hF e he).2.1
  exact ⟨r - u, s - v, by simp [hr, hu], by simp [hs, hv]⟩

private theorem rp1_invariantAlong_frontier (D : Set Plane) (δ : Submodule ℝ Plane)
    (hD : IsInvariantAlong D δ) : IsInvariantAlong (frontier D) δ := by
  intro u hu
  have h := (Homeomorph.addLeft u).image_frontier D
  change u +ᵥ frontier D = frontier (u +ᵥ D) at h
  rwa [hD u hu] at h

private theorem rp1_vertical_mem (x : Plane) :
    x ∈ Submodule.span ℝ ({Complex.I} : Set Plane) ↔ x.re = 0 := by
  constructor
  · rintro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp
  · intro hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x.im, ?_⟩
    apply Complex.ext <;> simp [hx]

private theorem rp1_cornerFree_rationalPeriods
    (K : PolygonalRegion) (hK : IsRational K.support) (Z : Set IntegerPlane)
    (hp : IsPacking K.prototileFamily (K.placements (integerPoint '' Z)))
    (hper : IsLatticePeriodic (regularSupport K (integerPoint '' Z)))
    (hne : (regularSupport K (integerPoint '' Z)).Nonempty)
    (hproper : regularSupport K (integerPoint '' Z) ≠ Set.univ)
    (hW : properVertices (regularSupport K (integerPoint '' Z)) = ∅) :
    ∃ lambda γ : Plane, IsRationalPoint lambda ∧ IsRationalPoint γ ∧
      LinearIndependent ℝ ![lambda, γ] ∧
      lambda ∈ periodGroup (regularSupport K (integerPoint '' Z)) ∧
      γ ∈ periodGroup (regularSupport K (integerPoint '' Z)) := by
  classical
  let S := integerPoint '' Z
  let E := regularSupport K S
  have hS : S.Nonempty := by
    by_contra h
    have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hE : E = ∅ := by simp [E, regularSupport, openUnion, he]
    exact hne.ne_empty hE
  obtain ⟨δ, hδ, hboundary, hinv⟩ := cornerFree_carrier_invariant hS hp hproper hW
  have hratδ := hasRationalDirection_of_hasBoundaryDirection
    (hasRationalSlopes_of_isRelativelyRational K (rp1_rational_isRelativelyRational K hK)) hboundary
  obtain ⟨z, hz, hzm⟩ := hratδ
  let e := integerPoint z
  have he : e ≠ 0 := by
    intro h
    apply hz
    apply Tiling.RationalPolygonal.integerPoint_injective
    simpa [e] using h
  obtain ⟨A, hArat, hmap⟩ := exists_rationalLinear_straighten δ hδ ⟨z, hz, hzm⟩
  let π : Plane →ₗ[ℝ] ℝ := Complex.reLm.comp A.toLinearMap
  have hδiff (x : Plane) : x ∈ δ ↔ π x = 0 := by
    have h : A x ∈ δ.map A.toLinearMap ↔ x ∈ δ := by
      constructor
      · rintro ⟨y, hy, hxy⟩
        exact A.injective hxy ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hmap, rp1_vertical_mem] at h
    exact h.symm
  have hπe : π e = 0 := (hδiff e).mp hzm
  have hfrontinv := rp1_invariantAlong_frontier E δ hinv
  have hline (x : Plane) (hx : x ∈ frontier E) : {y | π y = π x} ⊆ frontier E := by
    intro y hy
    change π y = π x at hy
    have hd : y - x ∈ δ := (hδiff _).mpr (by simp only [map_sub, hy, sub_self])
    rw [← hfrontinv (y - x) hd]
    exact ⟨x, hx, by simp [vadd_eq_add]⟩
  have hlevelrat (x : Plane) (hx : x ∈ frontier E) : ∃ q : ℚ, π x = q := by
    obtain ⟨_, _, hvertex⟩ := frontierLevel_has_bounded_intrinsicVertex K S hp π e he hπe
    obtain ⟨v, s, hv, hs, hvs, _⟩ := hvertex x (hline x hx)
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨r, u, hr, hu⟩ := hK.2 v hv
    have hsum : IsRationalPoint (v + integerPoint t) := by
      exact ⟨r + (t 0 : ℚ), u + (t 1 : ℚ), by simp [hr], by simp [hu]⟩
    obtain ⟨q, _, hq, _⟩ := hArat _ hsum
    exact ⟨q, hvs.symm.trans hq⟩
  obtain ⟨L, hL⟩ := hper
  have hex : ∃ j : Fin 2, L.basis j ∉ δ := by
    by_contra! h
    let v : Fin 2 → δ := fun j => ⟨L.basis j, h j⟩
    have hv : LinearIndependent ℝ v := LinearIndependent.of_comp δ.subtype L.independent
    have hd := hv.fintype_card_le_finrank
    rw [hδ] at hd
    simp only [Fintype.card_fin] at hd
    omega
  obtain ⟨j, hj⟩ := hex
  let α := L.basis j
  have hα : α ∈ periodGroup E := hL (AddSubgroup.subset_closure (Set.mem_range_self j))
  have hπα : π α ≠ 0 := fun h => hj ((hδiff α).mpr h)
  obtain ⟨x, hx⟩ := nonempty_frontier_iff.mpr ⟨hne, hproper⟩
  have hxa : α + x ∈ frontier E := by
    have h := (Homeomorph.addLeft α).image_frontier E
    change α +ᵥ frontier E = frontier (α +ᵥ E) at h
    rw [AddAction.mem_stabilizer_iff.mp hα] at h
    rw [← h]
    exact ⟨x, hx, rfl⟩
  obtain ⟨q, hq⟩ := hlevelrat x hx
  obtain ⟨r, hr⟩ := hlevelrat (α + x) hxa
  have hπarat : π α = ((r - q : ℚ) : ℝ) := by
    rw [map_add, hq] at hr
    push_cast
    linarith
  let γ := A.symm ((π α : ℝ) : Plane)
  have hγrat : IsRationalPoint γ := by
    apply hArat.symm
    exact ⟨r - q, 0, by simpa using hπarat, by simp⟩
  have hπγ : π γ = π α := by simp [π, γ]
  have hγ : γ ∈ periodGroup E := by
    have hd : γ - α ∈ δ := (hδiff _).mpr (by simp only [map_sub, hπγ, sub_self])
    have hpδ : γ - α ∈ periodGroup E := AddAction.mem_stabilizer_iff.mpr (hinv _ hd)
    convert (periodGroup E).add_mem hpδ hα using 1
    abel
  refine ⟨e, γ, ⟨(z 0 : ℚ), (z 1 : ℚ), by simp [e], by simp [e]⟩, hγrat, ?_,
    AddAction.mem_stabilizer_iff.mpr (hinv _ hzm), hγ⟩
  rw [linearIndependent_fin2]
  change γ ≠ 0 ∧ ∀ c : ℝ, c • γ ≠ e
  refine ⟨?_, ?_⟩
  · intro hγ0
    exact hπα (by rw [← hπγ, hγ0, map_zero])
  · intro c hc
    have hc0 : c = 0 := by
      have h := congrArg π hc
      simp only [map_smul, smul_eq_mul, hπγ, hπe] at h
      exact (mul_eq_zero.mp h).resolve_right hπα
    rw [hc0, zero_smul] at hc
    exact he hc.symm

private theorem rp1_properVertex_rationalPeriods
    (K : PolygonalRegion) (hK : IsRational K.support) (Z : Set IntegerPlane)
    (hp : IsPacking K.prototileFamily (K.placements (integerPoint '' Z)))
    (hper : IsLatticePeriodic (regularSupport K (integerPoint '' Z)))
    (hW : (properVertices (regularSupport K (integerPoint '' Z))).Nonempty) :
    ∃ lambda γ : Plane, IsRationalPoint lambda ∧ IsRationalPoint γ ∧
      LinearIndependent ℝ ![lambda, γ] ∧
      lambda ∈ periodGroup (regularSupport K (integerPoint '' Z)) ∧
      γ ∈ periodGroup (regularSupport K (integerPoint '' Z)) := by
  let E := regularSupport K (integerPoint '' Z)
  have hvertexrat (x : Plane) (hx : x ∈ properVertices E) : IsRationalPoint x := by
    obtain ⟨v, hv, s, ⟨z, hz, rfl⟩, rfl⟩ := properVertexProvenance hp x hx
    obtain ⟨r, u, hr, hu⟩ := hK.2 v hv
    exact ⟨r + (z 0 : ℚ), u + (z 1 : ℚ), by simp [hr], by simp [hu]⟩
  have hperiodrat (p : Plane) (hp : p ∈ periodGroup E) : IsRationalPoint p := by
    obtain ⟨x, hx⟩ := hW
    have hx' : p + x ∈ properVertices E := by
      have heq : p +ᵥ properVertices E = properVertices E := by
        rw [← properVertices_vadd E p, AddAction.mem_stabilizer_iff.mp hp]
      rw [← heq]
      exact ⟨x, hx, rfl⟩
    obtain ⟨r, u, hr, hu⟩ := hvertexrat (p + x) hx'
    obtain ⟨q, v, hq, hv⟩ := hvertexrat x hx
    refine ⟨r - q, u - v, ?_, ?_⟩
    · simp only [Complex.add_re] at hr
      push_cast
      linarith
    · simp only [Complex.add_im] at hu
      push_cast
      linarith
  obtain ⟨L, hL⟩ := hper
  have hb (j : Fin 2) : L.basis j ∈ periodGroup E :=
    hL (AddSubgroup.subset_closure (Set.mem_range_self j))
  refine ⟨L.basis 0, L.basis 1, hperiodrat _ (hb 0), hperiodrat _ (hb 1), ?_, hb 0, hb 1⟩
  convert L.independent using 1
  funext j
  fin_cases j <;> rfl

private theorem rp1_rationalPeriods_contains_scalar
    (H : AddSubgroup Plane) {u v : Plane} (hu : IsRationalPoint u) (hv : IsRationalPoint v)
    (hli : LinearIndependent ℝ ![u, v]) (huH : u ∈ H) (hvH : v ∈ H) :
    ∃ ell : ℕ, 0 < ell ∧ ∀ z : IntegerPlane, integerPoint ((ell : ℤ) • z) ∈ H := by
  obtain ⟨n, hn, p, hnp⟩ := rationalPoint_has_integer_multiple_rsHelper hu
  obtain ⟨m, hm, q, hmq⟩ := rationalPoint_has_integer_multiple_rsHelper hv
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hu0 : u ≠ 0 := by simpa using hli.ne_zero (0 : Fin 2)
  have hv0 : v ≠ 0 := by simpa using hli.ne_zero (1 : Fin 2)
  have hp0 : p ≠ 0 := by
    intro h
    have hs : (n : ℝ) • u = 0 := by simpa [h] using hnp
    exact hu0 ((smul_eq_zero.mp hs).resolve_left hnr)
  have hq0 : q ≠ 0 := by
    intro h
    have hs : (m : ℝ) • v = 0 := by simpa [h] using hmq
    exact hv0 ((smul_eq_zero.mp hs).resolve_left hmr)
  have hpH : integerPoint p ∈ H := by
    rw [← hnp]
    simpa only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast] using H.zsmul_mem huH (n : ℤ)
  have hqH : integerPoint q ∈ H := by
    rw [← hmq]
    simpa only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast] using H.zsmul_mem hvH (m : ℤ)
  apply integerPeriod_contains_scalar_rsHelper H p q hpH hqH
  intro hdet
  have hw : TranslationalTilings.wedge p q = 0 := hdet
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (TranslationalTilings.commensurable_iff_wedge_eq_zero hp0 hq0).mpr hw
  have h := congrArg Tiling.RationalPolygonal.integerPointHom hab
  simp only [map_zsmul, Tiling.RationalPolygonal.integerPointHom_apply] at h
  rw [← hnp, ← hmq] at h
  simp only [← Int.cast_smul_eq_zsmul ℝ, smul_smul] at h
  have hc : ![(a : ℝ) * (n : ℝ), -((b : ℝ) * (m : ℝ))] = (0 : Fin 2 → ℝ) :=
    hli.fintypeLinearCombination_injective (by
      simpa [Fintype.linearCombination_apply, Fin.sum_univ_two, neg_smul, sub_eq_add_neg]
        using sub_eq_zero.mpr h)
  have hc0 := congrFun hc 0
  simp only [Matrix.cons_val_zero, Pi.zero_apply] at hc0
  exact mul_ne_zero (by exact_mod_cast ha) hnr hc0

theorem integerCarrier_scalarPeriodic
    (K : PolygonalRegion) (hKrat : IsRational K.support) (A : Set IntegerPlane)
    (hpacking : IsPacking K.prototileFamily (K.placements (integerPoint '' A)))
    (hperiodic : IsLatticePeriodic (regularSupport K (integerPoint '' A))) :
    ∃ ell : ℕ, 0 < ell ∧ ∀ z : IntegerPlane,
      integerPoint ((ell : ℤ) • z) ∈
        periodGroup (regularSupport K (integerPoint '' A)) := by
  let E := regularSupport K (integerPoint '' A)
  by_cases hEmpty : E = ∅
  · refine ⟨1, by decide, ?_⟩
    intro z
    norm_num
    change integerPoint z ∈ AddAction.stabilizer Plane E
    change integerPoint z +ᵥ E = E
    rw [hEmpty]
    simp
  by_cases hFull : E = Set.univ
  · refine ⟨1, by decide, ?_⟩
    intro z
    norm_num
    change integerPoint z ∈ AddAction.stabilizer Plane E
    change integerPoint z +ᵥ E = E
    rw [hFull]
    simp
  by_cases hVertices : (properVertices E).Nonempty
  · obtain ⟨u, v, hu, hv, hli, huH, hvH⟩ :=
      rp1_properVertex_rationalPeriods K hKrat A hpacking hperiodic hVertices
    exact rp1_rationalPeriods_contains_scalar (periodGroup E) hu hv hli huH hvH
  · obtain ⟨u, v, hu, hv, hli, huH, hvH⟩ :=
      rp1_cornerFree_rationalPeriods K hKrat A hpacking hperiodic
        (Set.nonempty_iff_ne_empty.mpr hEmpty) hFull
        (Set.not_nonempty_iff_eq_empty.mp hVertices)
    exact rp1_rationalPeriods_contains_scalar (periodGroup E) hu hv hli huH hvH

/-- A packing is equivalent to every positive-volume relevant signature having count at most one. -/
theorem integerPacking_iff_signatureCounts
    (K : PolygonalRegion) (A : Set IntegerPlane) :
    IsPacking K.prototileFamily (K.placements (integerPoint '' A)) ↔
      ∀ F ∈ K.relevantSignatures, ∀ z : IntegerPlane,
        TranslationalTilings.tileConv F (TranslationalTilings.setIndicator A) z ≤ 1 :=
  integerPacking_iff_signatureCounts_measure_rsHelper K A

/-- Generic periodic-target raster packing bridge, not a whole-plane-only tiling equivalence. -/
theorem relevantRaster_tiles_ownCarrier_iff_packing
    (K : PolygonalRegion) (A : Set IntegerPlane) :
    TranslationalTilings.Tiles K.relevantPlanarRasterTile
      (Tiling.RationalPolygonal.markerTranslationSet K.relevantSignatureCount A)
      (Tiling.RationalPolygonal.discreteCarrier K.relevantPlanarRasterTile
        (Tiling.RationalPolygonal.markerTranslationSet K.relevantSignatureCount A)) ↔
      IsPacking K.prototileFamily (K.placements (integerPoint '' A)) := by
  rw [relevantRaster_tiles_ownCarrier_iff_signatureCounts_rsHelper]
  exact (integerPacking_iff_signatureCounts K A).symm

private theorem closure_openUnion_integerPoint_image
    (K : PolygonalRegion) (A : Set IntegerPlane) :
    closure (openUnion K (integerPoint '' A)) = K.integerTranslationCarrier A := by
  have hopen : openUnion K (integerPoint '' A) =
      ⋃ a : A, integerPoint (a : IntegerPlane) +ᵥ K.openCarrier := by
    ext x
    simp only [openUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨_, a, ha, rfl⟩, hx⟩
      exact ⟨⟨a, ha⟩, hx⟩
    · rintro ⟨a, hx⟩
      exact ⟨⟨integerPoint a, a, a.2, rfl⟩, hx⟩
  have hlocal : LocallyFinite fun a : A ↦ integerPoint (a : IntegerPlane) +ᵥ K.openCarrier :=
    (K.locallyFinite_integerTranslates A).subset fun a ↦
      Set.vadd_set_mono interior_subset
  rw [hopen, hlocal.closure_iUnion]
  simp only [closure_vadd, PolygonalRegion.openCarrier, K.isPolygonal.closure_interior]
  ext x
  simp only [Set.mem_iUnion, Set.mem_vadd_set, vadd_eq_add,
    PolygonalRegion.mem_integerTranslationCarrier_iff]
  constructor
  · rintro ⟨a, y, hy, rfl⟩
    exact ⟨y, hy, a, a.2, add_comm _ _⟩
  · rintro ⟨y, hy, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, y, hy, add_comm _ _⟩

private theorem closure_regularSupport_integerPoint_image
    (K : PolygonalRegion) (A : Set IntegerPlane) :
    closure (regularSupport K (integerPoint '' A)) = K.integerTranslationCarrier A := by
  rw [regularSupport, closure_openUnion_integerPoint_image]
  exact K.integerTranslationCarrier_closure_interior A

private theorem integerTranslationCarrier_vadd
    (K : PolygonalRegion) (A : Set IntegerPlane) (u : IntegerPlane) :
    K.integerTranslationCarrier (u +ᵥ A) = integerPoint u +ᵥ K.integerTranslationCarrier A := by
  ext x
  simp only [PolygonalRegion.mem_integerTranslationCarrier_iff,
    Set.mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨y, hy, _, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨y + integerPoint a, ⟨y, hy, a, ha, rfl⟩, by
      rw [Tiling.RationalPolygonal.integerPoint_add]; abel⟩
  · rintro ⟨_, ⟨y, hy, a, ha, rfl⟩, rfl⟩
    exact ⟨y, hy, u + a, ⟨a, ha, rfl⟩, by
      rw [Tiling.RationalPolygonal.integerPoint_add]; abel⟩

private theorem markerTranslationSet_vadd
    (M : ℕ) (A : Set IntegerPlane) (u : IntegerPlane) :
    Tiling.RationalPolygonal.markerTranslationSet M (u +ᵥ A) =
      Tiling.RationalPolygonal.markerScale M u +ᵥ
        Tiling.RationalPolygonal.markerTranslationSet M A := by
  ext x
  simp only [Tiling.RationalPolygonal.markerTranslationSet, Set.mem_image,
    Set.mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, (Tiling.RationalPolygonal.markerScale_add _ _ _).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨u + a, ⟨a, ha, rfl⟩, Tiling.RationalPolygonal.markerScale_add _ _ _⟩

private theorem discreteCarrier_vadd
    (F : Finset IntegerPlane) (A : Set IntegerPlane) (u : IntegerPlane) :
    Tiling.RationalPolygonal.discreteCarrier F (u +ᵥ A) =
      u +ᵥ Tiling.RationalPolygonal.discreteCarrier F A := by
  ext x
  simp only [Tiling.RationalPolygonal.mem_discreteCarrier_iff,
    Set.mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨f, hf, _, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f + a, ⟨f, hf, a, ha, rfl⟩, by abel⟩
  · rintro ⟨_, ⟨f, hf, a, ha, rfl⟩, rfl⟩
    exact ⟨f, hf, u + a, ⟨a, ha, rfl⟩, by abel⟩

theorem relevantRaster_scalarPeriodic
    (K : PolygonalRegion) (A : Set IntegerPlane) {ell : ℕ} (hell : 0 < ell)
    (hperiod : ∀ z : IntegerPlane,
      integerPoint ((ell : ℤ) • z) ∈
        periodGroup (regularSupport K (integerPoint '' A))) :
    TranslationalTilings.SetScalarPeriodic
      (Tiling.RationalPolygonal.markerSide K.relevantSignatureCount * ell)
      (Tiling.RationalPolygonal.discreteCarrier K.relevantPlanarRasterTile
        (Tiling.RationalPolygonal.markerTranslationSet K.relevantSignatureCount A)) := by
  intro x z
  have hp : integerPoint ((ell : ℤ) • z) +ᵥ
      regularSupport K (integerPoint '' A) = regularSupport K (integerPoint '' A) :=
    hperiod z
  have hc : K.integerTranslationCarrier ((ell : ℤ) • z +ᵥ A) =
      K.integerTranslationCarrier A := by
    rw [integerTranslationCarrier_vadd]
    simpa only [closure_vadd, closure_regularSupport_integerPoint_image] using
      congrArg closure hp
  have hd := (K.relevantPlanarRasterTile_carrier_eq_iff
      ((ell : ℤ) • z +ᵥ A) A).mpr hc
  rw [markerTranslationSet_vadd, discreteCarrier_vadd] at hd
  have hs : Tiling.RationalPolygonal.markerScale K.relevantSignatureCount ((ell : ℤ) • z) =
      ((Tiling.RationalPolygonal.markerSide K.relevantSignatureCount * ell : ℕ) : ℤ) • z := by
    simp [Tiling.RationalPolygonal.markerScale, mul_smul]
  rw [hs] at hd
  have hm := Set.ext_iff.mp hd
    (x + ((Tiling.RationalPolygonal.markerSide K.relevantSignatureCount * ell : ℕ) : ℤ) • z)
  simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
    add_left_comm, neg_add_cancel, add_zero] using hm.symm

private theorem lineFibre_eq_of_sub_mem
    (δ : Submodule ℝ Plane) (S : Set Plane) {s t : Plane} (hst : s - t ∈ δ) :
    lineFibre δ S s = lineFibre δ S t := by
  ext x
  constructor
  · rintro ⟨hxS, hxs⟩
    refine ⟨hxS, ?_⟩
    convert δ.add_mem hxs hst using 1
    abel
  · rintro ⟨hxS, hxt⟩
    refine ⟨hxS, ?_⟩
    convert δ.sub_mem hxt hst using 1
    abel

private theorem integerPoint_zsmul (n : ℤ) (x : IntegerPlane) :
    integerPoint (n • x) = n • integerPoint x :=
  map_zsmul Tiling.RationalPolygonal.integerPointHom n x

private theorem integerPoint_markerScale (M : ℕ) (x : IntegerPlane) :
    integerPoint (Tiling.RationalPolygonal.markerScale M x) =
      (Tiling.RationalPolygonal.markerSide M : ℤ) • integerPoint x :=
  integerPoint_zsmul _ _

private theorem integerPoint_basis_independent {h g : IntegerPlane}
    (hw : TranslationalTilings.wedge h g ≠ 0) :
    LinearIndependent ℝ ![integerPoint h, integerPoint g] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hg
    have hz : g = 0 := Tiling.RationalPolygonal.integerPoint_injective
      (hg.trans (Tiling.RationalPolygonal.integerPoint_zero.symm))
    exact hw (by simp [hz, TranslationalTilings.wedge])
  · intro c hc
    have hr := congrArg Complex.re hc
    have hi := congrArg Complex.im hc
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero,
      Complex.smul_re, Complex.smul_im, Tiling.RationalPolygonal.integerPoint_re,
      Tiling.RationalPolygonal.integerPoint_im, smul_eq_mul] at hr hi
    have he : (TranslationalTilings.wedge h g : ℝ) = 0 := by
      simp only [TranslationalTilings.wedge, Int.cast_sub, Int.cast_mul]
      rw [← hr, ← hi]
      ring
    exact hw (by exact_mod_cast he)

private theorem markerPreimage_vadd (M : ℕ) (B : Set IntegerPlane) (w : IntegerPlane) :
    Tiling.RationalPolygonal.markerPreimage M
        (Tiling.RationalPolygonal.markerScale M w +ᵥ B) =
      w +ᵥ Tiling.RationalPolygonal.markerPreimage M B := by
  ext a
  simp only [Tiling.RationalPolygonal.mem_markerPreimage_iff,
    Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  rw [show -w + a = a - w by abel,
    Tiling.RationalPolygonal.markerScale_sub]
  abel

private theorem integerPoint_image_vadd (A : Set IntegerPlane) (w : IntegerPlane) :
    integerPoint '' (w +ᵥ A) = integerPoint w +ᵥ (integerPoint '' A) := by
  ext x
  simp only [Set.mem_image, Set.mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, (Tiling.RationalPolygonal.integerPoint_add _ _).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨w + a, ⟨a, ha, rfl⟩, Tiling.RationalPolygonal.integerPoint_add _ _⟩

private theorem decoded_period (M : ℕ) (B : Set IntegerPlane) (w : IntegerPlane)
    (hp : Tiling.RationalPolygonal.DiscretePeriodicBy B
      (Tiling.RationalPolygonal.markerScale M w)) :
    integerPoint w ∈ periodGroup
      (integerPoint '' Tiling.RationalPolygonal.markerPreimage M B) := by
  have hb : Tiling.RationalPolygonal.markerScale M w +ᵥ B = B := by
    ext x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have hm := hp (x - Tiling.RationalPolygonal.markerScale M w)
    simpa only [sub_add_cancel, vadd_eq_add, neg_add_eq_sub] using hm.symm
  have hm := congrArg (Tiling.RationalPolygonal.markerPreimage M) hb
  rw [markerPreimage_vadd] at hm
  have hi := congrArg (Set.image integerPoint) hm
  rw [integerPoint_image_vadd] at hi
  exact hi

private theorem decoded_carrier_transport
    (K : PolygonalRegion) (B₀ B₁ : Set IntegerPlane)
    (hB₀ : B₀ ⊆ Tiling.RationalPolygonal.markerLattice K.relevantSignatureCount)
    (hB₁ : B₁ ⊆ Tiling.RationalPolygonal.markerLattice K.relevantSignatureCount)
    (w : IntegerPlane)
    (hc : Tiling.RationalPolygonal.markerScale K.relevantSignatureCount w +ᵥ
        Tiling.RationalPolygonal.discreteCarrier K.relevantPlanarRasterTile B₀ =
      Tiling.RationalPolygonal.discreteCarrier K.relevantPlanarRasterTile B₁) :
    regularSupport K (integerPoint '' Tiling.RationalPolygonal.markerPreimage
        K.relevantSignatureCount B₁) = integerPoint w +ᵥ
      regularSupport K (integerPoint '' Tiling.RationalPolygonal.markerPreimage
        K.relevantSignatureCount B₀) := by
  let A₀ := Tiling.RationalPolygonal.markerPreimage K.relevantSignatureCount B₀
  let A₁ := Tiling.RationalPolygonal.markerPreimage K.relevantSignatureCount B₁
  have h₀ : Tiling.RationalPolygonal.markerTranslationSet K.relevantSignatureCount A₀ = B₀ :=
    Tiling.RationalPolygonal.markerTranslationSet_markerPreimage_eq_of_subset hB₀
  have h₁ : Tiling.RationalPolygonal.markerTranslationSet K.relevantSignatureCount A₁ = B₁ :=
    Tiling.RationalPolygonal.markerTranslationSet_markerPreimage_eq_of_subset hB₁
  rw [← h₀, ← h₁, ← discreteCarrier_vadd, ← markerTranslationSet_vadd] at hc
  have hcont := (K.relevantPlanarRasterTile_carrier_eq_iff (w +ᵥ A₀) A₁).mp hc
  rw [integerTranslationCarrier_vadd] at hcont
  have hi := congrArg interior hcont.symm
  simpa only [regularSupport, closure_openUnion_integerPoint_image, interior_vadd] using hi

private theorem integerPoint_mem_realSpan_iff_directionSubgroup
    {u v : IntegerPlane} (hu : TranslationalTilings.IsPrimitive u) :
    integerPoint v ∈ Submodule.span ℝ {integerPoint u} ↔
      v ∈ TranslationalTilings.directionSubgroup u := by
  constructor
  · intro hvSpan
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvSpan
    have hre : (v 0 : ℝ) = c * (u 0 : ℝ) := by
      have h := congrArg Complex.re hc
      simpa [integerPoint, Complex.smul_re, mul_comm] using h.symm
    have him : (v 1 : ℝ) = c * (u 1 : ℝ) := by
      have h := congrArg Complex.im hc
      simpa [integerPoint, Complex.smul_im, mul_comm] using h.symm
    have hwReal : ((TranslationalTilings.wedge u v : ℤ) : ℝ) = 0 := by
      simp only [TranslationalTilings.wedge, Int.cast_sub, Int.cast_mul]
      rw [hre, him]
      ring
    have hw : TranslationalTilings.wedge u v = 0 := by exact_mod_cast hwReal
    by_cases hv0 : v = 0
    · rw [hv0]
      exact (TranslationalTilings.directionSubgroup u).zero_mem
    · have hcomm : TranslationalTilings.Commensurable v u :=
        (TranslationalTilings.commensurable_iff_wedge_eq_zero hv0 hu.1).2
          (by rw [TranslationalTilings.wedge_swap, hw]; simp)
      obtain ⟨z, _hz0, hvz⟩ :=
        TranslationalTilings.integer_multiple_of_primitive_of_commensurable hv0 hu hcomm
      rw [TranslationalTilings.directionSubgroup, AddSubgroup.mem_zmultiples_iff]
      exact ⟨z, hvz.symm⟩
  · intro hvDir
    rw [TranslationalTilings.directionSubgroup, AddSubgroup.mem_zmultiples_iff] at hvDir
    obtain ⟨z, hz⟩ := hvDir
    rw [← hz, integerPoint_zsmul]
    exact (Submodule.span ℝ {integerPoint u}).toAddSubgroup.zsmul_mem
      (Submodule.subset_span (by simp)) z

private theorem coarse_direction_iff
    (M : ℕ) {u a b : IntegerPlane} (hu : TranslationalTilings.IsPrimitive u) :
    Tiling.RationalPolygonal.markerScale M a - Tiling.RationalPolygonal.markerScale M b ∈
        TranslationalTilings.directionSubgroup u ↔
      integerPoint a - integerPoint b ∈ Submodule.span ℝ {integerPoint u} := by
  have hN : (Tiling.RationalPolygonal.markerSide M : ℝ) ≠ 0 := by
    exact_mod_cast (show Tiling.RationalPolygonal.markerSide M ≠ 0 by
      unfold Tiling.RationalPolygonal.markerSide; omega)
  rw [← Tiling.RationalPolygonal.markerScale_sub,
    ← integerPoint_mem_realSpan_iff_directionSubgroup hu, integerPoint_markerScale]
  rw [← Int.cast_smul_eq_zsmul ℝ]
  simp only [Int.cast_natCast]
  rw [(Submodule.span ℝ {integerPoint u}).smul_mem_iff hN,
    Tiling.RationalPolygonal.integerPoint_sub]

private theorem decode_discreteSlice
    (M : ℕ) (B : Set IntegerPlane) {u : IntegerPlane}
    (hu : TranslationalTilings.IsPrimitive u) (t : IntegerPlane) :
    integerPoint '' Tiling.RationalPolygonal.markerPreimage M
        (Tiling.AxisParallel.Terminal.DiscreteSlice u
          (QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup u)
            (Tiling.RationalPolygonal.markerScale M t)) B) =
      lineFibre (Submodule.span ℝ {integerPoint u})
        (integerPoint '' Tiling.RationalPolygonal.markerPreimage M B) (integerPoint t) := by
  ext x
  constructor
  · rintro ⟨a, ⟨haB, haQ⟩, rfl⟩
    refine ⟨⟨a, haB, rfl⟩, ?_⟩
    exact (coarse_direction_iff M hu).mp (QuotientAddGroup.eq_iff_sub_mem.mp haQ)
  · rintro ⟨⟨a, haB, rfl⟩, haδ⟩
    exact ⟨a, ⟨haB, QuotientAddGroup.eq_iff_sub_mem.mpr
      ((coarse_direction_iff M hu).mpr haδ)⟩, rfl⟩

/-- Coarse marker rescaling of both discrete basis vectors is part of the conversion,
not an unproved claim that arbitrary fine-lattice carrier periods decode. -/
theorem rationalSliceParametrization_of_discreteRasterData
    (K : PolygonalRegion) (A : Set IntegerPlane) (ell : ℕ)
    (D : Tiling.AxisParallel.Terminal.DiscreteFinerStructureData
      K.relevantPlanarRasterTile
      (Tiling.RationalPolygonal.markerTranslationSet K.relevantSignatureCount A)
      (Tiling.RationalPolygonal.discreteCarrier K.relevantPlanarRasterTile
        (Tiling.RationalPolygonal.markerTranslationSet K.relevantSignatureCount A)) ell) :
    Nonempty (RationalSliceParametrization K (integerPoint '' A)) := by
  classical
  let M := K.relevantSignatureCount
  let N := Tiling.RationalPolygonal.markerSide M
  let C := fun i ↦ Tiling.RationalPolygonal.markerPreimage M (D.part i)
  let part := fun i ↦ integerPoint '' C i
  let δ := fun i ↦ Submodule.span ℝ {integerPoint (D.direction i).primitiveVector}
  have hcoarse (i) : D.part i ⊆ (Tiling.RationalPolygonal.markerLattice M : Set IntegerPlane) := by
    intro x hx
    have hxA : x ∈ Tiling.RationalPolygonal.markerTranslationSet M A := by
      rw [← D.iUnion_parts]
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    obtain ⟨a, _ha, rfl⟩ := hxA
    exact ⟨a, rfl⟩
  have hpartnonempty (i) : (part i).Nonempty := by
    obtain ⟨x, hx⟩ := D.part_nonempty i
    obtain ⟨a, ha⟩ := hcoarse i hx
    refine ⟨integerPoint a, a, ?_, rfl⟩
    change (Tiling.RationalPolygonal.markerSide M : ℤ) • a ∈ D.part i
    rw [ha]
    exact hx
  have hperiod (i) : integerPoint (D.direction i).period =
      (D.direction i).hCoefficient • integerPoint D.h +
        (D.direction i).gCoefficient • integerPoint D.g := by
    simp only [Tiling.AxisParallel.Terminal.DiscreteDirection.period,
      Tiling.RationalPolygonal.integerPoint_add, integerPoint_zsmul]
  have hslicephase (i) (a : IntegerPlane) (ha : a ∈ C i) :
      QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup
        (D.direction i).primitiveVector) (Tiling.RationalPolygonal.markerScale M a) ∈
      (D.sliceOrbit i).phases := by
    apply ((D.sliceOrbit i).phase_iff_nonempty _).mpr
    exact ⟨Tiling.RationalPolygonal.markerScale M a, ha, rfl⟩
  refine ⟨{
    lattice := {
      basis := ![integerPoint D.h, integerPoint D.g]
      independent := integerPoint_basis_independent D.independent
    }
    basis_rational := ?_
    numberOfParts := D.numberOfParts
    part := part
    part_nonempty := hpartnonempty
    parts_disjoint := ?_
    union_parts := ?_
    direction := δ
    direction_dim := ?_
    lambdaCoefficient := fun i ↦ (D.direction i).hCoefficient
    gammaCoefficient := fun i ↦ (D.direction i).gCoefficient
    lambdaCoefficient_ne_zero := fun i ↦ (D.direction i).hCoefficient_ne_zero
    within_mem := ?_
    fibre_period := ?_
    fibre_transport := ?_
  }⟩
  · intro j
    refine ⟨fun k ↦ ((![D.h, D.g] j) k : ℚ), ?_⟩
    fin_cases j <;> apply Complex.ext <;> simp
  · intro i _ j _ hij
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab : a = b := Tiling.RationalPolygonal.integerPoint_injective (hax.trans hbx.symm)
    subst b
    exact Set.disjoint_left.mp (D.pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij) ha hb
  · ext x
    constructor
    · rintro hx
      obtain ⟨i, a, ha, rfl⟩ := Set.mem_iUnion.mp hx
      have hma : Tiling.RationalPolygonal.markerScale M a ∈
          Tiling.RationalPolygonal.markerTranslationSet M A := by
        rw [← D.iUnion_parts]
        exact Set.mem_iUnion.mpr ⟨i, ha⟩
      obtain ⟨b, hb, hba⟩ := hma
      have hab := (Tiling.RationalPolygonal.markerScale_injective M) hba
      exact ⟨a, hab ▸ hb, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      have hma : Tiling.RationalPolygonal.markerScale M a ∈
          Tiling.RationalPolygonal.markerTranslationSet M A := ⟨a, ha, rfl⟩
      rw [← D.iUnion_parts] at hma
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hma
      exact Set.mem_iUnion.mpr ⟨i, a, hi, rfl⟩
  · intro i
    apply finrank_span_singleton
    exact fun hz ↦ (D.direction i).primitive.1
      (Tiling.RationalPolygonal.integerPoint_injective
        (hz.trans (Tiling.RationalPolygonal.integerPoint_zero.symm)))
  · intro i
    change (D.direction i).hCoefficient • integerPoint D.h +
      (D.direction i).gCoefficient • integerPoint D.g ∈ δ i
    rw [← hperiod i, show (D.direction i).period =
      (D.direction i).multiple • (D.direction i).primitiveVector from (D.direction i).period_eq,
      integerPoint_zsmul]
    exact (δ i).toAddSubgroup.zsmul_mem (Submodule.subset_span (by simp)) _
  · rintro i t ⟨a, ha, rfl⟩
    let Q := QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup
      (D.direction i).primitiveVector) (Tiling.RationalPolygonal.markerScale M a)
    have hp := ((D.sliceOrbit i).slice_periodic Q (hslicephase i a ha)).zsmul (N : ℤ)
    have hdecode := decoded_period M
      (Tiling.AxisParallel.Terminal.DiscreteSlice (D.direction i).primitiveVector Q (D.part i))
      (D.direction i).period hp
    rw [decode_discreteSlice M _ (D.direction i).primitive a, hperiod] at hdecode
    exact hdecode
  · rintro i t ⟨a, ha, rfl⟩ m
    let u := (D.direction i).primitiveVector
    let Q := QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup u)
      (Tiling.RationalPolygonal.markerScale M a)
    let Q' := Q + QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup u)
      (((N : ℤ) * m) • D.g)
    have hQ := hslicephase i a ha
    have hQ' : Q' ∈ (D.sliceOrbit i).phases :=
      (D.sliceOrbit i).phase_translate_mem Q hQ ((N : ℤ) * m)
    have hshift : ((N : ℤ) * m) • D.g =
        Tiling.RationalPolygonal.markerScale M (m • D.g) := by
      dsimp [Tiling.RationalPolygonal.markerScale, N]
      rw [mul_smul]
    have hQ'eq : Q' = QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup u)
        (Tiling.RationalPolygonal.markerScale M (a + m • D.g)) := by
      change QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup u)
        (Tiling.RationalPolygonal.markerScale M a) +
        QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup u)
          (((N : ℤ) * m) • D.g) = _
      rw [hshift, ← map_add, ← Tiling.RationalPolygonal.markerScale_add]
    obtain ⟨b, hb, hbQ⟩ := ((D.sliceOrbit i).phase_iff_nonempty Q').mp hQ'
    obtain ⟨c, hc⟩ := hcoarse i hb
    have hcB : c ∈ C i := by
      change (Tiling.RationalPolygonal.markerSide M : ℤ) • c ∈ D.part i
      rw [hc]
      exact hb
    have hcδ : integerPoint c - integerPoint (a + m • D.g) ∈ δ i := by
      apply (coarse_direction_iff M (D.direction i).primitive).mp
      apply QuotientAddGroup.eq_iff_sub_mem.mp
      change QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup u) b = Q' at hbQ
      rw [hQ'eq] at hbQ
      change QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup u)
        ((Tiling.RationalPolygonal.markerSide M : ℤ) • c) = _
      rw [hc]
      exact hbQ
    refine ⟨integerPoint c, ⟨c, hcB, rfl⟩, ?_, ?_⟩
    · simpa only [Tiling.RationalPolygonal.integerPoint_add, integerPoint_zsmul,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_add_eq_sub_sub] using hcδ
    · let B₀ := Tiling.AxisParallel.Terminal.DiscreteSlice u Q (D.part i)
      let B₁ := Tiling.AxisParallel.Terminal.DiscreteSlice u Q' (D.part i)
      have ht := (D.sliceOrbit i).carrier_transport Q hQ ((N : ℤ) * m)
      have ht' : Tiling.RationalPolygonal.markerScale M (m • D.g) +ᵥ
          Tiling.RationalPolygonal.discreteCarrier K.relevantPlanarRasterTile B₀ =
        Tiling.RationalPolygonal.discreteCarrier K.relevantPlanarRasterTile B₁ := by
        change TranslationalTilings.translateSet (((N : ℤ) * m) • D.g)
          (Tiling.RationalPolygonal.discreteCarrier K.relevantPlanarRasterTile B₀) =
          Tiling.RationalPolygonal.discreteCarrier K.relevantPlanarRasterTile B₁ at ht
        rw [hshift] at ht
        rw [← ht]
        ext x
        simp only [TranslationalTilings.translateSet, Set.mem_ofPred_eq,
          Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
      have htransport := decoded_carrier_transport K B₀ B₁
        (fun _ hx ↦ hcoarse i hx.1) (fun _ hx ↦ hcoarse i hx.1) (m • D.g) ht'
      have hdec₀ := decode_discreteSlice M (D.part i) (D.direction i).primitive a
      have hdec₁ := decode_discreteSlice M (D.part i) (D.direction i).primitive (a + m • D.g)
      rw [← hQ'eq] at hdec₁
      rw [hdec₀, hdec₁] at htransport
      rw [lineFibre_eq_of_sub_mem (δ i) (part i) hcδ]
      simpa only [integerPoint_zsmul, Matrix.cons_val_one, Matrix.cons_val_fin_one] using htransport

private theorem affineMap_injective (A : Plane ≃L[ℝ] Plane) (a : Plane) :
    Function.Injective (affineMap A a) := by
  intro x y h
  exact A.injective (add_left_cancel h)

private theorem affineMap_image_vadd
    (A : Plane ≃L[ℝ] Plane) (a w : Plane) (S : Set Plane) :
    affineMap A a '' (w +ᵥ S) = A w +ᵥ (affineMap A a '' S) := by
  ext x
  simp only [Set.mem_image, Set.mem_vadd_set, vadd_eq_add, affineMap]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨a + A s, ⟨s, hs, rfl⟩, by rw [map_add]; abel⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨w + s, ⟨s, hs, rfl⟩, by rw [map_add]; abel⟩

private theorem affineMap_lineFibre
    (A : Plane ≃L[ℝ] Plane) (a : Plane) (δ : Submodule ℝ Plane)
    (S : Set Plane) (t : Plane) :
    lineFibre (δ.map A.toLinearMap) (affineMap A a '' S) (affineMap A a t) =
      affineMap A a '' lineFibre δ S t := by
  ext x
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hst⟩
    obtain ⟨v, hv, hvst⟩ := hst
    have hv' : v = s - t := A.injective (by
      change A v = affineMap A a s - affineMap A a t at hvst
      simpa [affineMap, map_sub] using hvst)
    exact ⟨s, ⟨hs, hv' ▸ hv⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hst⟩, rfl⟩
    refine ⟨⟨s, hs, rfl⟩, s - t, hst, ?_⟩
    simp only [affineMap, map_sub]
    abel

private theorem affineMap_regularSupport
    (K : PolygonalRegion) (A : Plane ≃L[ℝ] Plane) (a : Plane) (S : Set Plane) :
    regularSupport (affineImage K A 0) (affineMap A a '' S) =
      affineMap A a '' regularSupport K S := by
  have hopen : openUnion (affineImage K A 0) (affineMap A a '' S) =
      affineMap A a '' openUnion K S := by
    ext x
    simp only [openUnion, affineImage_openCarrier, Set.mem_iUnion,
      Set.mem_image, Set.mem_vadd_set, vadd_eq_add, affineMap, zero_add]
    constructor
    · rintro ⟨⟨_, t, ht, rfl⟩, _, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨t + u, ⟨⟨t, ht⟩, u, hu, rfl⟩, by
        simp [affineMap, map_add, add_comm, add_left_comm]⟩
    · rintro ⟨_, ⟨⟨t, ht⟩, u, hu, rfl⟩, rfl⟩
      exact ⟨⟨a + A t, t, ht, rfl⟩, A u, ⟨u, hu, rfl⟩, by
        simp only [map_add, add_assoc]⟩
  let H := A.toHomeomorph.trans (Homeomorph.addLeft a)
  change interior (closure _) = H '' interior (closure (openUnion K S))
  rw [hopen]
  exact (congrArg interior (H.image_closure (openUnion K S))).symm.trans
    (H.image_interior (closure (openUnion K S))).symm

private theorem rationalSliceParametrization_affine
    {K : PolygonalRegion} {T : Set Plane} (G : RationalSliceParametrization K T)
    (A : Plane ≃L[ℝ] Plane) (hA : IsRationalLinear A) (a : Plane) :
    Nonempty (RationalSliceParametrization (affineImage K A 0) (affineMap A a '' T)) := by
  classical
  let part := fun i ↦ affineMap A a '' G.part i
  let δ := fun i ↦ (G.direction i).map A.toLinearMap
  refine ⟨{
    lattice := {
      basis := fun j ↦ A (G.lattice.basis j)
      independent := G.lattice.independent.map' A.toLinearMap
        (LinearMap.ker_eq_bot.mpr A.injective)
    }
    basis_rational := ?_
    numberOfParts := G.numberOfParts
    part := part
    part_nonempty := fun i ↦ (G.part_nonempty i).image _
    parts_disjoint := ?_
    union_parts := ?_
    direction := δ
    direction_dim := fun i ↦ (A.toLinearEquiv.finrank_map_eq (G.direction i)).trans (G.direction_dim i)
    lambdaCoefficient := G.lambdaCoefficient
    gammaCoefficient := G.gammaCoefficient
    lambdaCoefficient_ne_zero := G.lambdaCoefficient_ne_zero
    within_mem := ?_
    fibre_period := ?_
    fibre_transport := ?_
  }⟩
  · intro j
    obtain ⟨q, hq⟩ := G.basis_rational j
    have hrat : IsRationalPoint (G.lattice.basis j) := by
      refine ⟨q 0, q 1, ?_, ?_⟩ <;> rw [hq]
    obtain ⟨r, s, hr, hs⟩ := hA _ hrat
    refine ⟨![r, s], ?_⟩
    apply Complex.ext <;> assumption
  · intro i _ j _ hij
    apply Set.disjoint_left.mpr
    rintro x ⟨s, hs, hsx⟩ ⟨t, ht, htx⟩
    have hst := affineMap_injective A a (hsx.trans htx.symm)
    exact Set.disjoint_left.mp
      (G.parts_disjoint (Set.mem_univ i) (Set.mem_univ j) hij) hs (hst ▸ ht)
  · change (⋃ i, affineMap A a '' G.part i) = _
    rw [← Set.image_iUnion, G.union_parts]
  · intro i
    refine ⟨_, G.within_mem i, ?_⟩
    simp only [map_add, map_zsmul]
    rfl
  · rintro i _ ⟨t, ht, rfl⟩
    rw [affineMap_lineFibre, periodGroup_affineImage]
    refine ⟨_, G.fibre_period i t ht, ?_⟩
    simp only [map_add, map_zsmul]
    rfl
  · rintro i _ ⟨t, ht, rfl⟩ m
    obtain ⟨s, hs, hδ, hc⟩ := G.fibre_transport i t ht m
    refine ⟨affineMap A a s, ⟨s, hs, rfl⟩, ?_, ?_⟩
    · refine ⟨s - t - m • G.lattice.basis 1, hδ, ?_⟩
      simp only [affineMap, map_sub, map_zsmul]
      abel
    · rw [affineMap_lineFibre, affineMap_lineFibre,
        affineMap_regularSupport, affineMap_regularSupport, hc, affineMap_image_vadd]
      simp only [map_zsmul]

private theorem integer_rationalSliceParametrization
    (K : PolygonalRegion) (hKrat : IsRational K.support) (A : Set IntegerPlane)
    (hp : IsPacking K.prototileFamily (K.placements (integerPoint '' A)))
    (hper : IsLatticePeriodic (regularSupport K (integerPoint '' A))) :
    Nonempty (RationalSliceParametrization K (integerPoint '' A)) := by
  obtain ⟨ell, hell, hperiod⟩ := integerCarrier_scalarPeriodic K hKrat A hp hper
  have hF : K.relevantPlanarRasterTile.Nonempty := by
    obtain ⟨f, hf⟩ := K.relevantPlanarSignatureAt_zero_nonempty
    obtain ⟨s, hs⟩ := Tiling.RationalPolygonal.markerBlock_nonempty
      K.relevantSignatureCount_pos K.relevantSignatureZero
    exact ⟨Tiling.RationalPolygonal.markerScale K.relevantSignatureCount f + s,
      Tiling.RationalPolygonal.mem_planarRasterTile_iff.mpr
        ⟨K.relevantSignatureZero, f, hf, s, hs, rfl⟩⟩
  have hmarkerpos : 0 < Tiling.RationalPolygonal.markerSide K.relevantSignatureCount * ell :=
    Nat.mul_pos (by unfold Tiling.RationalPolygonal.markerSide; omega) hell
  obtain ⟨D⟩ := Tiling.AxisParallel.Terminal.exists_discreteFinerStructure hF hmarkerpos
    (relevantRaster_scalarPeriodic K A hell hperiod)
    ((relevantRaster_tiles_ownCarrier_iff_packing K A).mpr hp)
  exact rationalSliceParametrization_of_discreteRasterData K A _ D

private theorem polygonalRegion_eq_of_support_eq {K L : PolygonalRegion}
    (h : K.support = L.support) : K = L := by
  cases K
  cases L
  cases h
  rfl

theorem exists_rationalSliceParametrization
    {K : PolygonalRegion} {T E : Set Plane} (hKrat : IsRational K.support)
    (hmesh : LiesInRationalMeshCoset T) (htile : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (hEper : IsLatticePeriodic E) :
    Nonempty (RationalSliceParametrization K T) := by
  classical
  obtain ⟨d, hd, a, hTmesh⟩ := hmesh
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  let A : Plane ≃L[ℝ] Plane := ContinuousLinearEquiv.smulLeft (Units.mk0 (d : ℝ) hd0)
  have hArat : IsRationalLinear A := by
    rintro v ⟨r, s, hr, hs⟩
    change IsRationalPoint ((d : ℝ) • v)
    exact ⟨(d : ℚ) * r, (d : ℚ) * s, by simp [hr], by simp [hs]⟩
  have hAratinv : IsRationalLinear A.symm := by
    rintro v ⟨r, s, hr, hs⟩
    change IsRationalPoint ((d : ℝ)⁻¹ • v)
    exact ⟨r / (d : ℚ), s / (d : ℚ), by simp [hr, div_eq_mul_inv, mul_comm, hd0],
      by simp [hs, div_eq_mul_inv, mul_comm, hd0]⟩
  let K₀ := affineImage K A 0
  let T₀ := affineMap A (-A a) '' T
  let E₀ := affineMap A (-A a) '' E
  have hnormalize (S : Set Plane) : A '' (-a +ᵥ S) = affineMap A (-A a) '' S := by
    ext x
    simp only [Set.mem_image, Set.mem_vadd_set, vadd_eq_add, affineMap]
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s, hs, by simp only [map_add, map_neg]⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨-a + s, ⟨s, hs, rfl⟩, by simp only [map_add, map_neg]⟩
  have hK₀rat : IsRational K₀.support := by
    refine ⟨K₀.isPolygonal, ?_⟩
    intro v hv
    rw [vertexSet_affineImage] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simpa only [affineMap, zero_add] using hArat w (hKrat.2 w hw)
  have hT₀integer : ∀ t ∈ T₀, Tiling.RationalPolygonal.IsIntegerPoint t := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨z, ⟨p, rfl⟩, rfl⟩ := Set.mem_vadd_set.mp (hTmesh ht)
    apply Tiling.RationalPolygonal.mem_integerLattice_iff.mpr
    refine ⟨p, ?_⟩
    simp only [affineMap, vadd_eq_add]
    change integerPoint p = -((d : ℝ) • a) +
      (d : ℝ) • (a + (d : ℝ)⁻¹ • integerPoint p)
    rw [smul_add, smul_smul, mul_inv_cancel₀ hd0, one_smul]
    abel
  let Z := PolygonalRegion.integerTranslationSet T₀
  have hZ : integerPoint '' Z = T₀ :=
    PolygonalRegion.integerPoint_image_integerTranslationSet hT₀integer
  have htile₀ : TilesOn K₀ T₀ E₀ := by
    have hn := (tilesOn_affineImage_iff K A 0 (-a +ᵥ T) (-a +ᵥ E)).mpr
      (tilesOn_translate htile (-a))
    have hA0 : affineMap A 0 = A := by
      funext x
      simp only [affineMap, zero_add]
    rw [hA0, hnormalize, hnormalize] at hn
    exact hn
  let H := A.toHomeomorph.trans (Homeomorph.addLeft (-A a))
  have hE₀open : IsOpen E₀ := H.isOpenMap E hEopen
  have hE₀regular : interior (closure E₀) = E₀ := by
    change interior (closure (H '' E)) = H '' E
    rw [← H.image_closure, ← H.image_interior, hEregular]
  have hE₀per : IsLatticePeriodic E₀ :=
    (isLatticePeriodic_affineImage_iff A (-A a) E).mpr hEper
  have hsupport : regularSupport K₀ T₀ = E₀ :=
    regularSupport_eq_of_tilesOn hE₀open hE₀regular htile₀
  have hp₀ : IsPacking K₀.prototileFamily (K₀.placements (integerPoint '' Z)) := by
    rw [hZ]
    exact htile₀.2.1
  have hper₀ : IsLatticePeriodic (regularSupport K₀ (integerPoint '' Z)) := by
    rw [hZ, hsupport]
    exact hE₀per
  obtain ⟨G₀⟩ := integer_rationalSliceParametrization K₀ hK₀rat Z hp₀ hper₀
  rw [hZ] at G₀
  have hKback : affineImage K₀ A.symm 0 = K := by
    apply polygonalRegion_eq_of_support_eq
    change affineMap A.symm 0 '' (affineMap A 0 '' K.support) = K.support
    rw [Set.image_image]
    simpa only [Function.comp_def, affineMap, zero_add, A.symm_apply_apply, id_eq] using
      Set.image_id K.support
  have hTback : affineMap A.symm a '' T₀ = T := by
    change affineMap A.symm a '' (affineMap A (-A a) '' T) = T
    rw [Set.image_image]
    simpa only [Function.comp_def, affineMap, map_add, map_neg,
      A.symm_apply_apply, add_neg_cancel_left, id_eq] using Set.image_id T
  have hresult := rationalSliceParametrization_affine G₀ A.symm hAratinv a
  rw [hKback, hTback] at hresult
  exact hresult

/-- Selecting transverse orbit representatives makes the rational slice datum a good
parametrization. Integer phase actions are free because gamma is transverse to each direction. -/
private theorem RationalSliceParametrization.gamma_not_mem
    {K : PolygonalRegion} {T : Set Plane} (G : RationalSliceParametrization K T)
    (i : Fin G.numberOfParts) : G.lattice.basis 1 ∉ G.direction i := by
  intro hg
  have hk : (G.lambdaCoefficient i : ℝ) ≠ 0 := by
    exact_mod_cast G.lambdaCoefficient_ne_zero i
  have hl : G.lattice.basis 0 ∈ G.direction i := by
    apply (G.direction i).smul_mem_iff hk |>.mp
    have hm := (G.direction i).sub_mem (G.within_mem i)
      ((G.direction i).toAddSubgroup.zsmul_mem hg (G.gammaCoefficient i))
    simpa only [add_sub_cancel_right, Int.cast_smul_eq_zsmul] using hm
  let v : Fin 2 → G.direction i := fun j ↦ ⟨G.lattice.basis j, by
    fin_cases j
    · exact hl
    · exact hg⟩
  have hv : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (G.direction i).subtype G.lattice.independent
  have hd := hv.fintype_card_le_finrank
  rw [G.direction_dim] at hd
  simp only [Fintype.card_fin] at hd
  omega

theorem RationalSliceParametrization.toGood
    {K : PolygonalRegion} {T : Set Plane} (G : RationalSliceParametrization K T) :
    Nonempty (GoodParametrization K T) := by
  classical
  let γ := G.lattice.basis 1
  let orbit : ∀ i : Fin G.numberOfParts, Setoid (G.part i) := fun i ↦ {
    r := fun x y ↦ ∃ m : ℤ, (x : Plane) - y - m • γ ∈ G.direction i
    iseqv := {
      refl := fun x ↦ ⟨0, by simp⟩
      symm := by
        rintro x y ⟨m, hm⟩
        refine ⟨-m, ?_⟩
        convert (G.direction i).neg_mem hm using 1
        module
      trans := by
        rintro x y z ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        convert (G.direction i).add_mem hm hn using 1
        module
    }
  }
  let Index := fun i ↦ Quotient (orbit i)
  let rep : ∀ i, Index i → Plane := fun i a ↦ (Quotient.out a : G.part i)
  let atom : ∀ i, Index i → ℤ → Set Plane := fun i a m ↦
    lineFibre (G.direction i) (G.part i) (rep i a + m • γ)
  have hrep (i) (a : Index i) : rep i a ∈ G.part i := (Quotient.out a).2
  have hphase (i) (a : Index i) (m : ℤ) :
      ∃ s ∈ G.part i, atom i a m = lineFibre (G.direction i) (G.part i) s ∧
        regularSupport K (atom i a m) =
          m • γ +ᵥ regularSupport K (atom i a 0) := by
    obtain ⟨s, hs, hline, hc⟩ := G.fibre_transport i (rep i a) (hrep i a) m
    have heq : atom i a m = lineFibre (G.direction i) (G.part i) s := by
      symm
      apply lineFibre_eq_of_sub_mem
      convert hline using 1
      abel
    refine ⟨s, hs, heq, ?_⟩
    rw [heq]
    simpa only [atom, zero_smul, add_zero] using hc
  refine ⟨{
    lattice := G.lattice
    numberOfParts := G.numberOfParts
    Index := Index
    atom := atom
    atom_nonempty := ?_
    atoms_disjoint := ?_
    union_eq := ?_
    lambdaCoefficient := G.lambdaCoefficient
    gammaCoefficient := G.gammaCoefficient
    lambdaCoefficient_ne_zero := G.lambdaCoefficient_ne_zero
    atom_periodic := ?_
    carrier_transport := ?_
  }⟩
  · intro i a m
    obtain ⟨s, hs, heq, _⟩ := hphase i a m
    rw [heq]
    exact ⟨s, hs, by simp⟩
  · rintro ⟨i, a, m⟩ _ ⟨j, b, n⟩ _ hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    by_cases hij : i = j
    · subst j
      have hab : a = b := by
        apply Quotient.out_equiv_out.mp
        refine ⟨n - m, ?_⟩
        convert (G.direction i).sub_mem hy.2 hx.2 using 1
        module
      subst b
      have hmn : m = n := by
        have hmul : (m - n) • γ ∈ G.direction i := by
          convert (G.direction i).sub_mem hy.2 hx.2 using 1
          module
        by_contra hmn
        have hcast : ((m - n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn
        have hg : γ ∈ G.direction i := (G.direction i).smul_mem_iff hcast |>.mp (by
          simpa only [Int.cast_smul_eq_zsmul] using hmul)
        exact G.gamma_not_mem i hg
      subst n
      exact hne rfl
    · exact Set.disjoint_left.mp
        (G.parts_disjoint (Set.mem_univ i) (Set.mem_univ j) hij) hx.1 hy.1
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hxi
      obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp hxa
      rw [← G.union_parts]
      exact Set.mem_iUnion.mpr ⟨i, hxm.1⟩
    · intro x hx
      rw [← G.union_parts] at hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      let a : Index i := Quotient.mk'' (⟨x, hxi⟩ : G.part i)
      obtain ⟨m, hm⟩ := Quotient.mk_out (s := orbit i) (⟨x, hxi⟩ : G.part i)
      refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨a,
        Set.mem_iUnion.mpr ⟨-m, hxi, ?_⟩⟩⟩
      convert (G.direction i).neg_mem hm using 1
      module
  · intro i a m
    obtain ⟨s, hs, heq, _⟩ := hphase i a m
    rw [heq]
    exact G.fibre_period i s hs
  · intro i a m
    exact (hphase i a m).choose_spec.2.2


end Tiling.RationalSlopes
