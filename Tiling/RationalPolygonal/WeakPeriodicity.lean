import Tiling.RationalPolygonal.SlidingReduction

set_option linter.style.header false

/-!
# Weak periodicity of every rational-polygonal tiling

This file completes the compatibility argument in Theorem 1.2 of de Dios
Pont--Grebík--Greenfeld--Madrid.  The connected integer sliding reduction retains the original
continuous plates.  Their raster carriers have one common integer sliding period, so canonical
quake plates refine the continuous-plate partition.  A uniform finite decomposition of all quake
plates can therefore be unshifted plate by plate.  Equal labels keep one common period, yielding a
finite weak-periodic decomposition of the original translation set rather than merely a different
tiling by the same region.
-/

open MeasureTheory Set
open scoped Pointwise
open TranslationalTilings

namespace Tiling.RationalPolygonal

/-- Embedding a discretely periodic lattice set into the real plane preserves its period. -/
theorem setPeriodicBy_integerPoint_image {A : Set IntegerPlane} {w : IntegerPlane}
    (hA : DiscretePeriodicBy A w) :
    SetPeriodicBy (integerPoint '' A) (integerPoint w) := by
  intro x
  constructor
  · rintro ⟨a, ha, hax⟩
    have ha' : a - w ∈ A := by
      apply (hA (a - w)).mp
      simpa only [sub_add_cancel] using ha
    refine ⟨a - w, ha', ?_⟩
    rw [integerPoint_sub, hax]
    abel
  · rintro ⟨a, ha, rfl⟩
    have ha' : a + w ∈ A := (hA a).mpr ha
    exact ⟨a + w, ha', integerPoint_add a w⟩

/-- A union of sets sharing one period has that period. -/
theorem setPeriodicBy_iUnion {ι : Sort*} {A : ι → Set Plane} {v : Plane}
    (hA : ∀ i, SetPeriodicBy (A i) v) :
    SetPeriodicBy (⋃ i, A i) v := by
  intro x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hxi⟩
    exact ⟨i, (hA i x).mp hxi⟩
  · rintro ⟨i, hxi⟩
    exact ⟨i, (hA i x).mpr hxi⟩

namespace PolygonalRegion

namespace IntegerSlidingReduction

variable {K : PolygonalRegion} {T : Set Plane}

/-- One uniform quake label, transported back from the based integer tiling through the component
shift belonging to the quake plate's old continuous owner. -/
noncomputable def unshiftedQuakePart
    (R : IntegerSlidingReduction K T) {u : Plane}
    (D : UniformQuakePeriodicDecomposition
      (K.signature u) R.translations R.direction)
    (C : QuakePlate (K.signature u) R.translations R.direction)
    (j : Fin D.numberOfParts) : Set Plane :=
  (R.base - R.shift (R.quakePlateOwner C) • integerPoint R.direction) +ᵥ
    (integerPoint '' D.part C j)

/-- The real part with label `j`, obtained by unshifting that label in every quake plate. -/
noncomputable def assembledQuakePart
    (R : IntegerSlidingReduction K T) {u : Plane}
    (D : UniformQuakePeriodicDecomposition
      (K.signature u) R.translations R.direction)
    (j : Fin D.numberOfParts) : Set Plane :=
  ⋃ C, R.unshiftedQuakePart D C j

/-- Every unshifted quake piece returns to the translation set of its old continuous owner. -/
theorem unshiftedQuakePart_subset_owner
    (R : IntegerSlidingReduction K T) {u : Plane}
    (hTiles : TilesUniverse (K.signature u) R.translations)
    (D : UniformQuakePeriodicDecomposition
      (K.signature u) R.translations R.direction)
    (C : QuakePlate (K.signature u) R.translations R.direction)
    (j : Fin D.numberOfParts) :
    R.unshiftedQuakePart D C j ⊆
      K.continuousPlateTranslations T (R.quakePlateOwner C) := by
  intro x hx
  rw [unshiftedQuakePart, Set.mem_vadd_set_iff_neg_vadd_mem] at hx
  obtain ⟨z, hzPart, hzEq⟩ := hx
  have hzQuake : z ∈ quakePlateTranslations C := by
    rw [← D.iUnion_parts C]
    exact Set.mem_iUnion.mpr ⟨j, hzPart⟩
  have hzOwner := R.quakePlateTranslations_subset_owner hTiles C hzQuake
  have hzImage : integerPoint z ∈
      -R.base +ᵥ K.shiftedContinuousPlateTranslations T
        (integerPoint R.direction) R.shift (R.quakePlateOwner C) := by
    rw [← R.image_plateTranslations]
    exact ⟨z, hzOwner, rfl⟩
  rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzImage
  change -(-R.base) + integerPoint z ∈
    R.shift (R.quakePlateOwner C) • integerPoint R.direction +ᵥ
      K.continuousPlateTranslations T (R.quakePlateOwner C) at hzImage
  rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzImage
  convert hzImage using 1
  simp only [vadd_eq_add] at hzEq ⊢
  rw [hzEq]
  module

/-- Every assembled label has the common real period obtained by embedding its lattice period. -/
theorem assembledQuakePart_periodic
    (R : IntegerSlidingReduction K T) {u : Plane}
    (D : UniformQuakePeriodicDecomposition
      (K.signature u) R.translations R.direction)
    (j : Fin D.numberOfParts) :
    SetPeriodicBy (R.assembledQuakePart D j) (integerPoint (D.period j)) := by
  apply setPeriodicBy_iUnion
  intro C
  exact setPeriodicBy_vadd
    (R.base - R.shift (R.quakePlateOwner C) • integerPoint R.direction)
    (setPeriodicBy_integerPoint_image (D.periodic_part C j))

/-- Distinct uniform labels remain disjoint after the owner-dependent inverse component shift. -/
theorem assembledQuakePart_pairwiseDisjoint
    (R : IntegerSlidingReduction K T) {u : Plane}
    (hTiles : TilesUniverse (K.signature u) R.translations)
    (D : UniformQuakePeriodicDecomposition
      (K.signature u) R.translations R.direction) :
    Set.PairwiseDisjoint Set.univ (R.assembledQuakePart D) := by
  intro i _ j _ hij
  change Disjoint (R.assembledQuakePart D i) (R.assembledQuakePart D j)
  rw [Set.disjoint_left]
  intro x hxi hxj
  obtain ⟨C, hxCi⟩ := Set.mem_iUnion.mp hxi
  obtain ⟨E, hxEj⟩ := Set.mem_iUnion.mp hxj
  have hxOwnerC := R.unshiftedQuakePart_subset_owner hTiles D C i hxCi
  have hxOwnerE := R.unshiftedQuakePart_subset_owner hTiles D E j hxEj
  have howner : R.quakePlateOwner C = R.quakePlateOwner E := by
    by_contra hne
    exact (Set.disjoint_left.mp
      (K.continuousPlateTranslations_pairwiseDisjoint T
        (Set.mem_univ _) (Set.mem_univ _) hne)) hxOwnerC hxOwnerE
  rw [unshiftedQuakePart, Set.mem_vadd_set_iff_neg_vadd_mem] at hxCi hxEj
  obtain ⟨z, hzi, hzEq⟩ := hxCi
  obtain ⟨r, hrj, hrEq⟩ := hxEj
  have hzrReal : integerPoint z = integerPoint r := by
    calc
      integerPoint z =
          -(R.base - R.shift (R.quakePlateOwner C) • integerPoint R.direction) + x := hzEq
      _ = -(R.base - R.shift (R.quakePlateOwner E) • integerPoint R.direction) + x := by
        rw [howner]
      _ = integerPoint r := hrEq.symm
  have hzr : z = r := integerPoint_injective hzrReal
  subst r
  have hzC : z ∈ quakePlateTranslations C := by
    rw [← D.iUnion_parts C]
    exact Set.mem_iUnion.mpr ⟨i, hzi⟩
  have hzE : z ∈ quakePlateTranslations E := by
    rw [← D.iUnion_parts E]
    exact Set.mem_iUnion.mpr ⟨j, hrj⟩
  have hCE : C = E := by
    by_contra hne
    exact (Set.disjoint_left.mp
      (quakePlateTranslations_pairwiseDisjoint
        (Set.mem_univ C) (Set.mem_univ E) hne)) hzC hzE
  subst E
  exact (Set.disjoint_left.mp
    (D.pairwiseDisjoint C (Set.mem_univ i) (Set.mem_univ j) hij)) hzi hrj

/-- The assembled uniform labels cover exactly the original continuous translation set. -/
theorem iUnion_assembledQuakePart
    (R : IntegerSlidingReduction K T) {u : Plane}
    (hTiles : TilesUniverse (K.signature u) R.translations)
    (D : UniformQuakePeriodicDecomposition
      (K.signature u) R.translations R.direction) :
    (⋃ j, R.assembledQuakePart D j) = T := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hxj
    exact (R.unshiftedQuakePart_subset_owner hTiles D C j hxC).1
  · intro x hxT
    rw [← K.iUnion_continuousPlateTranslations T] at hxT
    obtain ⟨A, hxA⟩ := Set.mem_iUnion.mp hxT
    let y : Plane := -R.base +
      (R.shift A • integerPoint R.direction + x)
    have hyBased : y ∈ -R.base +ᵥ
        K.shiftedContinuousPlateTranslations T (integerPoint R.direction) R.shift A := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change -(-R.base) + y ∈
        R.shift A • integerPoint R.direction +ᵥ
          K.continuousPlateTranslations T A
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      convert hxA using 1
      simp only [y, vadd_eq_add]
      module
    have hyImage : y ∈ integerPoint '' R.plateTranslations A := by
      rw [R.image_plateTranslations]
      exact hyBased
    obtain ⟨z, hzA, hzEq⟩ := hyImage
    have hzZ : z ∈ R.translations := R.plateTranslations_subset A hzA
    let C : QuakePlate (K.signature u) R.translations R.direction :=
      (quakeGraph (K.signature u) R.translations R.direction).connectedComponentMk
        ⟨z, hzZ⟩
    have hzC : z ∈ quakePlateTranslations C :=
      mem_quakePlateTranslations_mk ⟨z, hzZ⟩
    have hzOwner := R.quakePlateTranslations_subset_owner hTiles C hzC
    have howner : R.quakePlateOwner C = A := by
      by_contra hne
      exact (Set.disjoint_left.mp
        (R.plate_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) hne)) hzOwner hzA
    rw [← D.iUnion_parts C] at hzC
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzC
    apply Set.mem_iUnion.mpr
    refine ⟨j, Set.mem_iUnion.mpr ⟨C, ?_⟩⟩
    refine ⟨integerPoint z, ⟨z, hzj, rfl⟩, ?_⟩
    rw [howner, hzEq]
    simp only [y, vadd_eq_add]
    abel

/-- The uniform quake decomposition, transported plate by plate, is a finite weak-periodic
decomposition of the original continuous translation set. -/
noncomputable def weakPeriodicDecomposition
    (R : IntegerSlidingReduction K T) {u : Plane}
    (hTiles : TilesUniverse (K.signature u) R.translations)
    (D : UniformQuakePeriodicDecomposition
      (K.signature u) R.translations R.direction) :
    WeakPeriodicDecomposition T where
  numberOfParts := D.numberOfParts
  part := R.assembledQuakePart D
  period j := integerPoint (D.period j)
  period_ne_zero j hzero :=
    D.period_ne_zero j
      (integerPoint_injective (hzero.trans integerPoint_zero.symm))
  periodic_part := R.assembledQuakePart_periodic D
  pairwiseDisjoint := R.assembledQuakePart_pairwiseDisjoint hTiles D
  iUnion_parts := R.iUnion_assembledQuakePart hTiles D

end IntegerSlidingReduction

/-- **Paper Theorem 1.2, integer-vertex form.** Every given tiling by an integer-vertex polygonal
region is weakly periodic. -/
theorem Tiles.weaklyPeriodic_of_integerVertices
    {K : PolygonalRegion} (hK : K.HasIntegerVertices)
    {T : Set Plane} (hT : K.Tiles T) : WeaklyPeriodic T := by
  obtain ⟨R⟩ := hT.exists_integerSlidingReduction hK
  have hsignatures := R.tiles.ae_signature_tilesUniverse
  obtain ⟨u, hu⟩ := hsignatures.exists
  obtain ⟨f, hf, -⟩ := existsUnique_tile_representation hu 0
  obtain ⟨D⟩ := exists_uniformQuakePeriodicDecomposition
    (F := K.signature u) ⟨f, hf.1⟩ R.direction_ne_zero hu
  exact ⟨R.weakPeriodicDecomposition hu D⟩

end PolygonalRegion

namespace RationalPolygonalRegion

/-- Forward and inverse rational normalization cancel on translation sets. -/
theorem denormalizedTranslations_normalizedTranslations
    (K : RationalPolygonalRegion) (T : Set Plane) :
    K.denormalizedTranslations (K.normalizedTranslations T) = T := by
  ext x
  rw [K.mem_denormalizedTranslations_iff_normalizedTranslation_mem]
  constructor
  · rintro ⟨t, ht, htx⟩
    exact (K.normalizedTranslation_injective htx).symm ▸ ht
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **Paper Theorem 1.2.** Every given translational tiling by a relatively rational polygonal
region is a finite disjoint union of singly periodic translation sets. -/
theorem Tiles.weaklyPeriodic
    {K : RationalPolygonalRegion} {T : Set Plane}
    (hT : K.toPolygonalRegion.Tiles T) : WeaklyPeriodic T := by
  have hnormalized := K.normalizedRegion_tiles hT
  have hweakNormalized := hnormalized.weaklyPeriodic_of_integerVertices
    K.normalizedRegion_hasIntegerVertices
  have hweakDenormalized :=
    K.weaklyPeriodic_denormalizedTranslations hweakNormalized
  rwa [K.denormalizedTranslations_normalizedTranslations] at hweakDenormalized

end RationalPolygonalRegion

end Tiling.RationalPolygonal
