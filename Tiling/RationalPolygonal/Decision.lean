import Tiling.RationalPolygonal.RasterRigidity
import TranslationalTilings.Algorithms

set_option linter.style.header false

/-!
# Executable tileability decision for compiled rational polygons

Lean's semantic `RationalPolygonalRegion` stores a real set and proof witnesses, so it is not an
executable input type.  The effective input to the paper's Corollary 1.1 is the finite lattice tile
computed by its rasterization stage.  This file makes that compilation boundary explicit: a
`RasterPresentation` is runtime data, `Represents` certifies which rational region it encodes, and
`tileDecision` is the actual bounded Boolean search from the planar Greenfeld--Tao development.
-/

open TranslationalTilings

namespace Tiling.RationalPolygonal

/-- Finite runtime representation produced by rasterizing a rational polygonal region. -/
structure RasterPresentation where
  /-- The finite planar lattice tile supplied to the exhaustive decision procedure. -/
  rasterTile : Finset IntegerPlane
deriving DecidableEq

namespace RasterPresentation

/-- A compiled raster presentation represents `K` when it is exactly the canonical marker raster
of the integral affine normalization of `K`. -/
def Represents (P : RasterPresentation) (K : RationalPolygonalRegion) : Prop :=
  P.rasterTile = K.normalizedRegion.relevantPlanarRasterTile

/-- The executable Boolean decision on a compiled rational-polygonal input. -/
def tileDecision (P : RasterPresentation) : Bool :=
  planarTileDecision P.rasterTile

/-- The exact counted running cost of the executable decision. -/
def tileDecisionCost (P : RasterPresentation) : ℕ :=
  planarTileSearchCost P.rasterTile

/-- The counted implementation returns the same Boolean and the advertised exact cost. -/
theorem planarTileDecisionCounted_eq
    (P : RasterPresentation) :
    planarTileDecisionCounted P.rasterTile =
      (P.tileDecision, P.tileDecisionCost) := by
  apply Prod.ext
  · rfl
  · exact planarTileDecisionCounted_cost_exact P.rasterTile

/-- Tileability of a rational region is exactly tileability of its canonical normalized raster. -/
theorem tileable_iff_canonicalRaster (K : RationalPolygonalRegion) :
    (∃ T : Set Plane, K.toPolygonalRegion.Tiles T) ↔
      ∃ A : Set IntegerPlane,
        TilesUniverse K.normalizedRegion.relevantPlanarRasterTile A := by
  constructor
  · rintro ⟨T, hT⟩
    have hnormalized := K.normalizedRegion_tiles hT
    obtain ⟨Z, hZtiles, -, hZinteger⟩ :=
      K.normalizedRegion.exists_integer_tiling
        K.normalizedRegion_hasIntegerVertices hnormalized
    let A := PolygonalRegion.integerTranslationSet Z
    have himage : integerPoint '' A = Z :=
      PolygonalRegion.integerPoint_image_integerTranslationSet hZinteger
    have hAtiles : K.normalizedRegion.Tiles (integerPoint '' A) := by
      rwa [himage]
    exact (K.normalizedRegion.exists_integer_tiling_iff_relevantPlanarRasterTile).mp
      ⟨A, hAtiles⟩
  · rintro hraster
    obtain ⟨A, hAtiles⟩ :=
      (K.normalizedRegion.exists_integer_tiling_iff_relevantPlanarRasterTile).mpr hraster
    exact ⟨K.denormalizedTranslations (integerPoint '' A),
      K.tiles_of_normalizedRegion_tiles hAtiles⟩

/-- **Paper Corollary 1.1, executable specification.**  On a finite raster presentation of `K`,
the bounded Boolean search returns true exactly when `K` tiles the real plane by translations. -/
theorem tileDecision_eq_true_iff
    (P : RasterPresentation) (K : RationalPolygonalRegion)
    (hP : P.Represents K) :
    P.tileDecision = true ↔
      ∃ T : Set Plane, K.toPolygonalRegion.Tiles T := by
  rw [tileDecision, planarTileDecision_eq_true_iff, hP]
  exact (tileable_iff_canonicalRaster K).symm

/-- A compiled presentation yields a constructive decidable instance for semantic tileability. -/
def tileableDecidable
    (P : RasterPresentation) (K : RationalPolygonalRegion)
    (hP : P.Represents K) :
    Decidable (∃ T : Set Plane, K.toPolygonalRegion.Tiles T) :=
  decidable_of_iff (P.tileDecision = true) (P.tileDecision_eq_true_iff K hP)

/-- The canonical raster is a finite presentation of every semantic rational polygonal region.
This definition is noncomputable only because the semantic region is not an effective input; the
decision on the resulting finite `RasterPresentation` is the executable function above. -/
noncomputable def canonical (K : RationalPolygonalRegion) : RasterPresentation where
  rasterTile := K.normalizedRegion.relevantPlanarRasterTile

/-- The canonical compiled presentation represents its source region. -/
theorem canonical_represents (K : RationalPolygonalRegion) :
    (canonical K).Represents K :=
  rfl

end RasterPresentation

end Tiling.RationalPolygonal
