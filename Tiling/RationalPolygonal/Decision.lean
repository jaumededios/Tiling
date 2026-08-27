import Tiling.RationalPolygonal.RasterRigidity
import TranslationalTilings.Algorithms

set_option linter.style.header false

/-!
# Compiled raster decision backend

Lean's semantic `RationalPolygonalRegion` stores a real set and proof witnesses, so it is not an
executable input type.  This file isolates the reusable backend after raster compilation: a
`RasterPresentation` is finite runtime data, `Represents` certifies which semantic rational region
it encodes, and `tileDecision` is the bounded Boolean search from the planar Greenfeld--Tao
development.  `RawDecision` supplies the paper-facing executable frontend from rational
coordinates and delegates its final search to this backend infrastructure.
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

/-- **Compiled-backend specification.** On a finite raster presentation of `K`, the bounded
Boolean search returns true exactly when `K` tiles the real plane by translations. -/
theorem tileDecision_eq_true_iff
    (P : RasterPresentation) (K : RationalPolygonalRegion)
    (hP : P.Represents K) :
    P.tileDecision = true ↔
      ∃ T : Set Plane, K.toPolygonalRegion.Tiles T := by
  rw [tileDecision, planarTileDecision_eq_true_iff, hP]
  exact (tileable_iff_canonicalRaster K).symm

/-- Correctness contract for a Boolean algorithm on finite rational-polygon raster
presentations.  The contract is extensional in the represented semantic region: every valid code
must return the real-plane tileability answer. -/
def DecidesTileability
    (algorithm : RasterPresentation → Bool) : Prop :=
  ∀ P K, P.Represents K →
    (algorithm P = true ↔
      ∃ T : Set Plane, K.toPolygonalRegion.Tiles T)

/-- The executable bounded raster search decides tileability on every valid presentation. -/
theorem tileDecision_decidesTileability :
    DecidesTileability tileDecision := by
  intro P K hP
  exact P.tileDecision_eq_true_iff K hP

/-- There is a single executable Boolean algorithm deciding every valid finite raster
presentation of a rational polygonal region. -/
theorem exists_tileabilityAlgorithm :
    ∃ algorithm : RasterPresentation → Bool,
      DecidesTileability algorithm :=
  ⟨tileDecision, tileDecision_decidesTileability⟩

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

/-- Every semantic rational polygonal region has at least one finite raster presentation. -/
theorem exists_representation (K : RationalPolygonalRegion) :
    ∃ P : RasterPresentation, P.Represents K :=
  ⟨canonical K, canonical_represents K⟩

end RasterPresentation

end Tiling.RationalPolygonal
