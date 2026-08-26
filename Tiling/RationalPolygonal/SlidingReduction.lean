import Tiling.RationalPolygonal.ContinuousEarthquake

set_option linter.style.header false

/-!
# Integer sliding reductions retaining continuous plates

This file packages the compatibility step between the continuous sliding argument and the
discrete earthquake argument in Theorem 1.2 of de Dios Pont--Grebík--Greenfeld--Madrid.  Starting
from an integer-vertex monotile tiling, the continuous plates are shifted until the vertex graph
is connected, the resulting tiling is based at one placement, and every translation is thereby
identified with a lattice point.  Unlike the earlier existential integer reduction, the package
retains the partition by old continuous plates and the common integer sliding direction on the
raster carrier of every plate.
-/

open MeasureTheory Set
open scoped Pointwise

namespace Tiling.RationalPolygonal

namespace PolygonalRegion

/-- An integer-lattice realization of a connected component shift, together with the partition
by the original continuous plates and their common raster-carrier period. -/
structure IntegerSlidingReduction (K : PolygonalRegion) (T : Set Plane) where
  /-- A nonzero lattice vector parallel to every old continuous plate. -/
  direction : IntegerPlane
  /-- The retained sliding vector is nonzero. -/
  direction_ne_zero : direction ≠ 0
  /-- The embedded lattice vector is a genuine continuous sliding direction. -/
  sliding : (K.polygonalProtoTiling T).IsSlidingDirection (integerPoint direction)
  /-- The component displacement used to connect the shifted vertex graph. -/
  shift : (K.polygonalProtoTiling T).Plate → ℝ
  /-- The placement translated to the origin before taking lattice coordinates. -/
  base : Plane
  /-- Integer coordinates of all based shifted translations. -/
  translations : Set IntegerPlane
  /-- Integer coordinates belonging to each old continuous plate. -/
  plateTranslations : (K.polygonalProtoTiling T).Plate → Set IntegerPlane
  /-- The shifted continuous tiling has connected vertex graph. -/
  shifted_connected :
    (K.polygonalProtoTiling
      (K.shiftedContinuousTranslations T (integerPoint direction) shift)).vertexGraph.Connected
  /-- The based shifted tiling is exactly the real image of `translations`. -/
  image_translations :
    integerPoint '' translations =
      -base +ᵥ K.shiftedContinuousTranslations T (integerPoint direction) shift
  /-- Each discrete plate is exactly the based image of its corresponding continuous plate. -/
  image_plateTranslations : ∀ C,
    integerPoint '' plateTranslations C =
      -base +ᵥ K.shiftedContinuousPlateTranslations T (integerPoint direction) shift C
  /-- The integer realization is still a tiling by `K`. -/
  tiles : K.Tiles (integerPoint '' translations)
  /-- Distinct old plates give disjoint lattice translation sets. -/
  plate_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ plateTranslations
  /-- The old plate translation sets partition all integer translations. -/
  iUnion_plateTranslations : (⋃ C, plateTranslations C) = translations
  /-- Every raster carrier of an old plate has the retained common sliding period. -/
  signatureCarrier_periodic : ∀ C u,
    DiscretePeriodicBy (discreteCarrier (K.signature u) (plateTranslations C)) direction

/-- Integer-vertex monotile tilings admit an integer sliding reduction retaining the complete old
continuous-plate partition. -/
theorem Tiles.exists_integerSlidingReduction
    {K : PolygonalRegion} (hK : K.HasIntegerVertices)
    {T : Set Plane} (hT : K.Tiles T) : Nonempty (IntegerSlidingReduction K T) := by
  classical
  obtain ⟨w, hw, hv, shift, hshiftedTiles, hshiftedConnected⟩ :=
    hT.exists_integer_connected_shiftedContinuousTranslations hK
  let S := K.shiftedContinuousTranslations T (integerPoint w) shift
  obtain ⟨ibase⟩ := hshiftedConnected.nonempty
  let base : Plane := ibase.1.1
  let U : Set Plane := -base +ᵥ S
  have hUinteger : ∀ t ∈ U, IsIntegerPoint t := by
    intro t ht
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at ht
    let i : (K.polygonalProtoTiling S).placements :=
      ⟨(base, ()), ibase.2⟩
    let j : (K.polygonalProtoTiling S).placements :=
      ⟨(-(-base) +ᵥ t, ()), ht⟩
    have hreach : (K.polygonalProtoTiling S).SamePlate i j :=
      hshiftedConnected i j
    have hdifference := samePlate_translation_sub_mem_integerLattice hK hreach
    change t ∈ integerLattice
    convert hdifference using 1
    simp only [i, j, base, vadd_eq_add]
    abel
  let Z : Set IntegerPlane := integerTranslationSet U
  have himageZ : integerPoint '' Z = U :=
    integerPoint_image_integerTranslationSet hUinteger
  have htilesZ : K.Tiles (integerPoint '' Z) := by
    rw [himageZ]
    exact hshiftedTiles.vadd (-base)
  let P : (K.polygonalProtoTiling T).Plate → Set IntegerPlane :=
    fun C ↦ integerTranslationSet
      (-base +ᵥ K.shiftedContinuousPlateTranslations T (integerPoint w) shift C)
  have hpieceSubset (C : (K.polygonalProtoTiling T).Plate) :
      K.shiftedContinuousPlateTranslations T (integerPoint w) shift C ⊆ S := by
    intro x hx
    exact K.mem_shiftedContinuousTranslations_iff.mpr ⟨C, hx⟩
  have hPinteger (C : (K.polygonalProtoTiling T).Plate) :
      ∀ t ∈ -base +ᵥ
          K.shiftedContinuousPlateTranslations T (integerPoint w) shift C,
        IsIntegerPoint t := by
    intro t ht
    apply hUinteger t
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at ht ⊢
    exact hpieceSubset C ht
  have himageP (C : (K.polygonalProtoTiling T).Plate) :
      integerPoint '' P C =
        -base +ᵥ K.shiftedContinuousPlateTranslations T (integerPoint w) shift C :=
    integerPoint_image_integerTranslationSet (hPinteger C)
  have hpairP : Set.PairwiseDisjoint Set.univ P := by
    intro C _ D _ hCD
    change Disjoint (P C) (P D)
    rw [Set.disjoint_left]
    intro z hzC hzD
    have hzC' : integerPoint z ∈
        -base +ᵥ K.shiftedContinuousPlateTranslations T (integerPoint w) shift C := hzC
    have hzD' : integerPoint z ∈
        -base +ᵥ K.shiftedContinuousPlateTranslations T (integerPoint w) shift D := hzD
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzC' hzD'
    exact (Set.disjoint_left.mp
      (PolygonalRegion.IsSlidingDirection.shiftedContinuousPlateTranslations_pairwiseDisjoint
        hv hT shift
          (Set.mem_univ C) (Set.mem_univ D) hCD)) hzC' hzD'
  have hunionP : (⋃ C, P C) = Z := by
    ext z
    simp only [Set.mem_iUnion, P, Z, mem_integerTranslationSet_iff]
    change (∃ C, integerPoint z ∈
        -base +ᵥ K.shiftedContinuousPlateTranslations T (integerPoint w) shift C) ↔
      integerPoint z ∈ U
    simp only [U, S, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg,
      K.mem_shiftedContinuousTranslations_iff]
  have hperiodP (C : (K.polygonalProtoTiling T).Plate) (u : Plane) :
      DiscretePeriodicBy (discreteCarrier (K.signature u) (P C)) w := by
    apply K.signatureCarrier_periodic_of_integerTranslationCarrier
    rw [K.integerTranslationCarrier_eq_translationCarrier_image, himageP C]
    exact PolygonalRegion.IsSlidingDirection.setPeriodicBy_translatedShiftedPlateCarrier
      hv shift C
  exact ⟨{
    direction := w
    direction_ne_zero := hw
    sliding := hv
    shift := shift
    base := base
    translations := Z
    plateTranslations := P
    shifted_connected := hshiftedConnected
    image_translations := himageZ
    image_plateTranslations := himageP
    tiles := htilesZ
    plate_pairwiseDisjoint := hpairP
    iUnion_plateTranslations := hunionP
    signatureCarrier_periodic := hperiodP
  }⟩

end PolygonalRegion

end Tiling.RationalPolygonal
