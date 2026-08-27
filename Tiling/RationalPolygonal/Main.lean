import Tiling.RationalPolygonal.RasterRigidity
import Tiling.RationalPolygonal.WeakPeriodicity
import Tiling.RationalPolygonal.RawDecision
import TranslationalTilings.Main

/-!
# Main results for rational polygonal tilings

This module combines rational affine normalization, connected integer reduction, the rigid raster
encoding, Greenfeld--Tao periodic completion, and the verified executable compiler from finite
rational triangulations.  It exposes Theorem 1.1, Corollary 1.1, and Theorem 1.2 of de Dios
Pont--Grebík--Greenfeld--Madrid through their paper-facing semantic and raw-input APIs.
-/

open Set
open TranslationalTilings
open scoped Pointwise

namespace Tiling.RationalPolygonal

/-- A positive scalar period in both lattice coordinates becomes two linearly independent real
periods after embedding the integer plane. -/
theorem doublyPeriodic_integerPoint_image_of_setScalarPeriodic
    {A : Set IntegerPlane} {P : ℕ} (hP : 0 < P)
    (hA : SetScalarPeriodic P A) :
    DoublyPeriodic (integerPoint '' A) := by
  let v₁ : IntegerPlane := (P : ℤ) • horizontalUnit
  let v₂ : IntegerPlane := (P : ℤ) • verticalUnit
  let h₁ := integerPoint v₁
  let h₂ := integerPoint v₂
  have hperiod₁ : SetPeriodicBy (integerPoint '' A) h₁ := by
    apply setPeriodicBy_integerPoint_image
    intro x
    exact hA x horizontalUnit
  have hperiod₂ : SetPeriodicBy (integerPoint '' A) h₂ := by
    apply setPeriodicBy_integerPoint_image
    intro x
    exact hA x verticalUnit
  refine ⟨h₁, h₂, ?_, hperiod₁, hperiod₂⟩
  rw [linearIndependent_fin2]
  change h₂ ≠ 0 ∧ ∀ a : ℝ, a • h₂ ≠ h₁
  constructor
  · intro hzero
    have hvzero : v₂ = 0 := by
      apply integerPoint_injective
      simpa only [h₂, integerPoint_zero] using hzero
    have him := congrFun hvzero 1
    change (P : ℤ) * 1 = 0 at him
    omega
  · intro a ha
    have hre := congrArg Complex.re ha
    simp [h₁, h₂, v₁, v₂, integerPoint, horizontalUnit,
      verticalUnit, latticePoint] at hre
    have hPReal : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
    exact hPReal hre.symm

namespace PolygonalRegion

/-- A tileable planar raster admits a scalar-periodic completion, which decodes to a doubly
periodic integer-translation tiling of the polygonal region. -/
theorem exists_doublyPeriodic_integer_tiling_of_tileable_raster
    (K : PolygonalRegion)
    (hraster : ∃ U : Set IntegerPlane,
      TilesUniverse K.relevantPlanarRasterTile U) :
    ∃ T : Set IntegerPlane,
      K.Tiles (integerPoint '' T) ∧ DoublyPeriodic (integerPoint '' T) := by
  have htarget : SetScalarPeriodic 1 (Set.univ : Set IntegerPlane) := by
    intro x z
    simp
  obtain ⟨U, hU⟩ := hraster
  obtain ⟨U', P, hP, hU', hperiod, -⟩ :=
    TranslationalTilings.theorem_1_5 (F := K.relevantPlanarRasterTile)
      (E := Set.univ) (ell := 1) (by omega) htarget ⟨U, hU⟩
  have hperiod' : SetScalarPeriodic P U' := by simpa using hperiod
  obtain ⟨T, hfamily, hTperiod⟩ :=
    exists_scalarPeriodic_family_tiling_of_planarRasterTile
      K.relevantSignatureCount_pos K.relevantPlanarSignatureAt
      K.relevantPlanarSignatureAt_zero_nonempty hU' hperiod'
  refine ⟨T, ?_, doublyPeriodic_integerPoint_image_of_setScalarPeriodic hP hTperiod⟩
  apply (K.tiles_integerPoint_image_iff_relevantSignatures T).mpr
  exact (K.relevantPlanarSignatureAt_tilesUniverse_iff T).mp hfamily

end PolygonalRegion

namespace RationalPolygonalRegion

/-- Inverse rational normalization preserves two-dimensional periodicity. -/
theorem doublyPeriodic_denormalizedTranslations
    (K : RationalPolygonalRegion) {A : Set Plane}
    (hA : DoublyPeriodic A) :
    DoublyPeriodic (K.denormalizedTranslations A) := by
  obtain ⟨h₁, h₂, hlinear, hperiod₁, hperiod₂⟩ := hA
  let c : ℝ := (K.denominator : ℝ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero K.denominator_cast_ne_zero
  refine ⟨c • h₁, c • h₂, ?_,
    K.setPeriodicBy_denormalizedTranslations hperiod₁,
    K.setPeriodicBy_denormalizedTranslations hperiod₂⟩
  exact (LinearIndependent.pair_smul_iff hc).mpr hlinear

/-- Every tiling by a rational polygonal region can be replaced by a doubly periodic tiling. -/
theorem exists_doublyPeriodic_tiling (K : RationalPolygonalRegion)
    {T : Set Plane} (hT : K.toPolygonalRegion.Tiles T) :
    ∃ S : Set Plane,
      K.toPolygonalRegion.Tiles S ∧ DoublyPeriodic S := by
  have hnormalized := K.normalizedRegion_tiles hT
  obtain ⟨Z, hZtiles, -⟩ := K.normalizedRegion.exists_integer_signature_tiling
    K.normalizedRegion_hasIntegerVertices hnormalized
  have hraster : ∃ U : Set IntegerPlane,
      TilesUniverse K.normalizedRegion.relevantPlanarRasterTile U :=
    (K.normalizedRegion.exists_integer_tiling_iff_relevantPlanarRasterTile).mp
      ⟨Z, hZtiles⟩
  obtain ⟨Z', hZ'tiles, hZ'periodic⟩ :=
    K.normalizedRegion.exists_doublyPeriodic_integer_tiling_of_tileable_raster hraster
  refine ⟨K.denormalizedTranslations (integerPoint '' Z'),
    K.tiles_of_normalizedRegion_tiles hZ'tiles, ?_⟩
  exact K.doublyPeriodic_denormalizedTranslations hZ'periodic

/-- Paper Theorem 1.1: a rational polygonal region tiles the plane if and only if it admits a
doubly periodic translational tiling. -/
theorem tileable_iff_exists_doublyPeriodic_tiling (K : RationalPolygonalRegion) :
    (∃ T : Set Plane, K.toPolygonalRegion.Tiles T) ↔
      ∃ T : Set Plane,
        K.toPolygonalRegion.Tiles T ∧ DoublyPeriodic T := by
  constructor
  · rintro ⟨T, hT⟩
    exact K.exists_doublyPeriodic_tiling hT
  · rintro ⟨T, hT, -⟩
    exact ⟨T, hT⟩

/-- **Paper Theorem 1.1.** A rational polygonal region tiles the plane exactly when it admits a
doubly periodic translational tiling. -/
theorem theorem_1_1 (K : RationalPolygonalRegion) :
    (∃ T : Set Plane, K.toPolygonalRegion.Tiles T) ↔
      ∃ T : Set Plane,
        K.toPolygonalRegion.Tiles T ∧ DoublyPeriodic T :=
  K.tileable_iff_exists_doublyPeriodic_tiling

/-- Pointwise specification of the executable algorithm in paper Corollary 1.1. -/
theorem corollary_1_1_spec
    (P : Raw.Code.Input) :
    Raw.Decision.rawTileDecision P = true ↔
      ∃ T : Set Plane,
        P.rationalPolygonalRegion.toPolygonalRegion.Tiles T :=
  Raw.Decision.rawTileDecision_decidesRawTileability P

/-- **Paper Corollary 1.1.** There is one executable Boolean algorithm which decides whether the
rational polygonal region given by any valid finite rational triangulation tiles the plane. -/
theorem corollary_1_1 :
    ∃ algorithm : Raw.Code.Input → Bool,
      Raw.Decision.DecidesRawTileability algorithm :=
  Raw.Decision.exists_rawTileabilityAlgorithm

/-- **Paper Theorem 1.2.** Every translation set tiling by a rational polygonal region is weakly
periodic. -/
theorem theorem_1_2
    {K : RationalPolygonalRegion} {T : Set Plane}
    (hT : K.toPolygonalRegion.Tiles T) : WeaklyPeriodic T :=
  RationalPolygonalRegion.Tiles.weaklyPeriodic hT

end RationalPolygonalRegion

end Tiling.RationalPolygonal
