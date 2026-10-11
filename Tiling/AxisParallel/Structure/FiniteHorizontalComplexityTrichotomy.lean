import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.Approximation.GoodApproximationPreservesTilings
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.NontrivialEarthquakeLimit
import Tiling.AxisParallel.Continuous.WeakTilingTopology
import Tiling.AxisParallel.Continuous.CoordinateSwapTilings
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Foundations.PositiveSimilarityTransport
import Tiling.AxisParallel.Continuous.PositiveSimilarityPlates
import Tiling.AxisParallel.Structure.CrossAxisLimit
import Tiling.AxisParallel.Structure.ProductRigidity
import Tiling.AxisParallel.Structure.SimultaneousColumns

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Structure

/-- The oriented finite-horizontal-complexity output used by the terminal decomposition. -/
structure FiniteHorizontalComplexityTrichotomyData
    (K : Tiling.AxisParallel.Region)
    (T : Tiling.AxisParallel.Topology.TilingSpace K Set.univ) where
  orientation : Tiling.AxisParallel.Axis
  limit : Tiling.AxisParallel.Topology.TilingSpace K Set.univ
  limit_mem_hull : limit ∈ Tiling.AxisParallel.Topology.orbitHull T
  swapped_tilesOn : orientation = Tiling.AxisParallel.Axis.horizontal →
    Tiling.AxisParallel.TilesOn K.coordinateSwap
      (Tiling.AxisParallel.coordinateSwap '' (limit.centres : Set Tiling.Plane))
      Set.univ
  finiteHorizontal_original : orientation = Tiling.AxisParallel.Axis.vertical →
    Tiling.AxisParallel.Continuous.HasFiniteHorizontalComplexity
      (limit.centres : Set Tiling.Plane)
  finiteHorizontal_swapped : orientation = Tiling.AxisParallel.Axis.horizontal →
    Tiling.AxisParallel.Continuous.HasFiniteHorizontalComplexity
      (Tiling.AxisParallel.coordinateSwap '' (limit.centres : Set Tiling.Plane))
  nontrivialVertical_original : orientation = Tiling.AxisParallel.Axis.vertical →
    ¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K
        (limit.centres : Set Tiling.Plane),
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧
        P.centres = (limit.centres : Set Tiling.Plane)
  nontrivialVertical_swapped : orientation = Tiling.AxisParallel.Axis.horizontal →
    ¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K.coordinateSwap
        (Tiling.AxisParallel.coordinateSwap '' (limit.centres : Set Tiling.Plane)),
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧
        P.centres = Tiling.AxisParallel.coordinateSwap ''
          (limit.centres : Set Tiling.Plane)

universe u

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Topology

private abbrev NontrivialVerticalDecomposition
    (K : Region) (S : Set Tiling.Plane) :=
  ¬ ∃ P : Continuous.VerticalPlate K S,
    ¬ Continuous.IsVerticalColumn P ∧ P.centres = S

private def IsCoordinateSwapTiling {K : Region}
    (T : TilingSpace K Set.univ)
    (Tσ : TilingSpace K.coordinateSwap Set.univ) : Prop :=
  (Tσ.centres : Set Tiling.Plane) =
    coordinateSwap '' (T.centres : Set Tiling.Plane)

private def IsPersistentCrossAxisAlternative {K : Region}
    {T S : TilingSpace K Set.univ} :
    CrossAxisLimitAlternative K T S → Prop
  | .finiteVerticalComplexity _ => False
  | .persistentHorizontalColumn .. => True

private theorem coordinateSwapTiling_exists
    {K : Region} (T : TilingSpace K Set.univ) :
    ∃ Tσ : TilingSpace K.coordinateSwap Set.univ,
      IsCoordinateSwapTiling T Tσ := by
  obtain ⟨Tσ, hTσ⟩ :=
    Tiling.AxisParallel.Continuous.exists_coordinateSwapTiling T
  exact ⟨Tσ, hTσ⟩

private theorem coordinateSwapTiling_unique
    {K : Region} {T : TilingSpace K Set.univ}
    {Tσ Uσ : TilingSpace K.coordinateSwap Set.univ} :
    IsCoordinateSwapTiling T Tσ → IsCoordinateSwapTiling T Uσ → Tσ = Uσ := by
  intro hTσ hUσ
  cases Tσ with
  | mk cσ hσ =>
    cases Uσ with
    | mk cυ hυ =>
      congr 1
      apply TopologicalSpace.Closeds.ext
      exact hTσ.trans hUσ.symm

private theorem coordinateSwapTiling_involutive
    {K : Region} {T : TilingSpace K Set.univ}
    {Tσ : TilingSpace K.coordinateSwap Set.univ} :
    IsCoordinateSwapTiling T Tσ →
      ∃ U : TilingSpace K Set.univ,
        (U.centres : Set Tiling.Plane) = (T.centres : Set Tiling.Plane) ∧
        (coordinateSwap '' (Tσ.centres : Set Tiling.Plane)) =
          (U.centres : Set Tiling.Plane) := by
  intro hTσ
  refine ⟨T, rfl, ?_⟩
  rw [hTσ]
  ext z
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    simpa using hu
  · intro hz
    exact ⟨coordinateSwap z, ⟨z, hz, rfl⟩, coordinateSwap_apply_apply z⟩

private theorem coordinateSwap_orbitHull_iff
    {K : Region}
    {T S : TilingSpace K Set.univ}
    {Tσ Sσ : TilingSpace K.coordinateSwap Set.univ}
    (hTσ : IsCoordinateSwapTiling T Tσ)
    (hSσ : IsCoordinateSwapTiling S Sσ) :
    (S ∈ orbitHull T ↔ Sσ ∈ orbitHull Tσ) := by
  simpa only [IsCoordinateSwapTiling] using
    (Tiling.AxisParallel.Continuous.coordinateSwap_orbitHull_iff
      (T := T) (S := S) (Tσ := Tσ) (Sσ := Sσ) hTσ hSσ)

private theorem coordinateSwap_nontrivial_iff
    {K : Region} {T : TilingSpace K Set.univ}
    {Tσ : TilingSpace K.coordinateSwap Set.univ} :
    IsCoordinateSwapTiling T Tσ →
    (NontrivialVerticalDecomposition K (T.centres : Set Tiling.Plane) ↔
      NontrivialVerticalDecomposition K.coordinateSwap.coordinateSwap
        (coordinateSwap '' (Tσ.centres : Set Tiling.Plane))) := by
  intro hTσ
  have himage :
      coordinateSwap '' (coordinateSwap '' (T.centres : Set Tiling.Plane)) =
        (T.centres : Set Tiling.Plane) := by
    ext z
    constructor
    · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      simpa using hu
    · intro hz
      exact ⟨coordinateSwap z, ⟨z, hz, rfl⟩, coordinateSwap_apply_apply z⟩
  rw [hTσ, Region.coordinateSwap_involutive K, himage]

private theorem orbitHull_transitive
    {K : Region} {T S U : TilingSpace K Set.univ} :
    S ∈ orbitHull T → U ∈ orbitHull S → U ∈ orbitHull T := by
  intro hST hUS
  let H : Set (TilingSpace K Set.univ) := orbitHull T
  have hclosed : IsClosed H := isClosed_closure
  apply (closure_minimal ?_ hclosed) hUS
  intro V hV
  rcases hV with ⟨g, rfl⟩
  have himage : TilingSpace.translate g '' H = H :=
    (orbitHull_compact T).2.2 g
  exact (Set.ext_iff.mp himage _).mp ⟨S, hST, rfl⟩

private theorem planeNontrivialEarthquake_exists :
    ∀ {K : Region} (T : TilingSpace K Set.univ),
      (¬ HasFLC (T.centres : Set Tiling.Plane)) →
        Nonempty (NontrivialEarthquakeLimitData K Set.univ T) := by
  intro K T hT
  exact exists_nontrivialEarthquakeOrbitLimit Set.univ_nonempty isOpen_univ
    (by simp) (beta0 := (1 : ℝ)) (by norm_num) (by simp) T hT

private theorem verticalEarthquakeSplit_nontrivial :
    ∀ {K : Region} {T : TilingSpace K Set.univ}
      (E : NontrivialEarthquakeLimitData K Set.univ T),
      E.split.orientation = Axis.vertical →
        NontrivialVerticalDecomposition K (E.limit.centres : Set Tiling.Plane) := by
  intro K T E hor hbad
  obtain ⟨P, _hPcolumn, hPcentres⟩ := hbad
  obtain ⟨p, hp⟩ := E.persistent_nonempty
  obtain ⟨q, hq⟩ := E.transient_nonempty
  have hpLimit : p ∈ (E.limit.centres : Set Tiling.Plane) :=
    E.split.persistent_subset hp
  have hqLimit : q ∈ (E.limit.centres : Set Tiling.Plane) :=
    E.split.transient_subset hq
  have hpP : p ∈ P.centres := by
    rw [hPcentres]
    exact hpLimit
  have hqP : q ∈ P.centres := by
    rw [hPcentres]
    exact hqLimit
  have hmeet : (P.centres ∩ E.split.persistent).Nonempty := ⟨p, hpP, hp⟩
  have hsat := E.split.verticalPersistent_plateSaturated hor P hmeet
  exact (Set.disjoint_left.1 E.split.disjoint) (hsat hqP) hq

private theorem horizontalEarthquakeSplit_nontrivial :
    ∀ {K : Region} {T : TilingSpace K Set.univ}
      (E : NontrivialEarthquakeLimitData K Set.univ T)
      (Eσ : TilingSpace K.coordinateSwap Set.univ),
      IsCoordinateSwapTiling E.limit Eσ →
      E.split.orientation = Axis.horizontal →
        NontrivialVerticalDecomposition K.coordinateSwap
          (Eσ.centres : Set Tiling.Plane) := by
  intro K T E Eσ hswap hor
  change (Eσ.centres : Set Tiling.Plane) =
    coordinateSwap '' (E.limit.centres : Set Tiling.Plane) at hswap
  rw [hswap]
  intro hbad
  obtain ⟨P, _hPcolumn, hPcentres⟩ := hbad
  obtain ⟨p, hp⟩ := E.persistent_nonempty
  obtain ⟨q, hq⟩ := E.transient_nonempty
  have hpLimit : p ∈ (E.limit.centres : Set Tiling.Plane) :=
    E.split.persistent_subset hp
  have hqLimit : q ∈ (E.limit.centres : Set Tiling.Plane) :=
    E.split.transient_subset hq
  have hpP : coordinateSwap p ∈ P.centres := by
    rw [hPcentres]
    exact ⟨p, hpLimit, rfl⟩
  have hqP : coordinateSwap q ∈ P.centres := by
    rw [hPcentres]
    exact ⟨q, hqLimit, rfl⟩
  have hmeet : (P.centres ∩ (coordinateSwap '' E.split.persistent)).Nonempty :=
    ⟨coordinateSwap p, hpP, ⟨p, hp, rfl⟩⟩
  have hsat := E.split.horizontalPersistent_plateSaturated hor P hmeet
  obtain ⟨r, hr, hreq⟩ := hsat hqP
  have hrq : r = q := coordinateSwap.injective hreq
  exact (Set.disjoint_left.1 E.split.disjoint) (hrq ▸ hr) hq

private theorem trichotomyData_vertical_of :
    ∀ {K : Region} {T S : TilingSpace K Set.univ},
      S ∈ orbitHull T →
      HasFiniteHorizontalComplexity (S.centres : Set Tiling.Plane) →
      NontrivialVerticalDecomposition K (S.centres : Set Tiling.Plane) →
        Nonempty (FiniteHorizontalComplexityTrichotomyData K T) := by
  intro K T S hHull hFinite hNontrivial
  exact ⟨{
    orientation := Axis.vertical
    limit := S
    limit_mem_hull := hHull
    swapped_tilesOn := by intro h; cases h
    finiteHorizontal_original := by intro h; exact hFinite
    finiteHorizontal_swapped := by intro h; cases h
    nontrivialVertical_original := by intro h; exact hNontrivial
    nontrivialVertical_swapped := by intro h; cases h }⟩

private theorem trichotomyData_horizontal_of :
    ∀ {K : Region} {T S : TilingSpace K Set.univ}
      (Sσ : TilingSpace K.coordinateSwap Set.univ),
      IsCoordinateSwapTiling S Sσ → S ∈ orbitHull T →
      HasFiniteHorizontalComplexity (Sσ.centres : Set Tiling.Plane) →
      NontrivialVerticalDecomposition K.coordinateSwap
        (Sσ.centres : Set Tiling.Plane) →
      Nonempty (FiniteHorizontalComplexityTrichotomyData K T) := by
  intro K T S Sσ hswap hHull hFinite hNontrivial
  exact ⟨{
    orientation := Axis.horizontal
    limit := S
    limit_mem_hull := hHull
    swapped_tilesOn := by
      intro _
      rw [← hswap]
      exact Sσ.tilesOn
    finiteHorizontal_original := by intro h; cases h
    finiteHorizontal_swapped := by intro h; rw [← hswap]; exact hFinite
    nontrivialVertical_original := by intro h; cases h
    nontrivialVertical_swapped := by intro h; rw [← hswap]; exact hNontrivial }⟩

private theorem swappedCrossAxisFiniteBranch
    {K : Region} {T S₀ : TilingSpace K Set.univ}
    (S₀σ : TilingSpace K.coordinateSwap Set.univ)
    (hS₀σ : IsCoordinateSwapTiling S₀ S₀σ)
    (hS₀T : S₀ ∈ orbitHull T)
    (S₁ : TilingSpace K.coordinateSwap Set.univ)
    (hS₁ : S₁ ∈ orbitHull S₀σ)
    (hNontrivial : NontrivialVerticalDecomposition K.coordinateSwap.coordinateSwap
      (coordinateSwap '' (S₁.centres : Set Tiling.Plane)))
    (hFinite : HasFiniteHorizontalComplexity
      (coordinateSwap '' (S₁.centres : Set Tiling.Plane))) :
    ∃ U : TilingSpace K Set.univ,
      (U.centres : Set Tiling.Plane) =
          coordinateSwap '' (S₁.centres : Set Tiling.Plane) ∧
      U ∈ orbitHull T ∧
      NontrivialVerticalDecomposition K (U.centres : Set Tiling.Plane) ∧
      HasFiniteHorizontalComplexity (U.centres : Set Tiling.Plane) := by
  obtain ⟨U₀, hU₀⟩ := coordinateSwapTiling_exists S₁
  have hK : K.coordinateSwap.coordinateSwap = K :=
    Region.coordinateSwap_involutive K
  let U : TilingSpace K Set.univ :=
    { centres := U₀.centres
      tilesOn := Eq.mp
        (congrArg (fun R : Region =>
          TilesOn R (U₀.centres : Set Tiling.Plane) Set.univ) hK)
        U₀.tilesOn }
  have hUcent : (U.centres : Set Tiling.Plane) =
      coordinateSwap '' (S₁.centres : Set Tiling.Plane) := by
    simpa only [U, IsCoordinateSwapTiling] using hU₀
  have hUσ : IsCoordinateSwapTiling U S₁ := by
    change (S₁.centres : Set Tiling.Plane) =
      coordinateSwap '' (U.centres : Set Tiling.Plane)
    rw [hUcent]
    ext z
    constructor
    · intro hz
      exact ⟨coordinateSwap z, ⟨z, hz, rfl⟩, coordinateSwap_apply_apply z⟩
    · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      simpa using hu
  have hUS₀ : U ∈ orbitHull S₀ := by
    apply (coordinateSwap_orbitHull_iff hS₀σ hUσ).mpr
    exact hS₁
  have hUT : U ∈ orbitHull T :=
    orbitHull_transitive hS₀T hUS₀
  have hNontrivialU : NontrivialVerticalDecomposition K
      (U.centres : Set Tiling.Plane) :=
    (coordinateSwap_nontrivial_iff hUσ).mpr hNontrivial
  refine ⟨U, hUcent, hUT, hNontrivialU, ?_⟩
  rw [hUcent]
  exact hFinite

private structure NormalizedPersistentBranchData
    (K : Region) (source : TilingSpace K Set.univ) where
  vertexAnchor : Tiling.Plane
  vertexAnchor_mem : vertexAnchor ∈ K.vertices
  centreAnchor : Tiling.Plane
  centreAnchor_mem : centreAnchor ∈ (source.centres : Set Tiling.Plane)
  context : ApproximationContext.{u}
  normalizedSource : TilingSpace context.region Set.univ
  context_region : context.region.openCarrier =
    (-vertexAnchor) +ᵥ K.openCarrier
  context_centres : context.centres =
    (-centreAnchor) +ᵥ (source.centres : Set Tiling.Plane)
  context_target : context.target = Set.univ
  normalizedSource_centres :
    (normalizedSource.centres : Set Tiling.Plane) = context.centres
  fibre : PersistentHorizontalFibreData context normalizedSource

private theorem normalizedPersistentBranch_exists :
    ∀ {K : Region} {source limit : TilingSpace K Set.univ}
      (A : CrossAxisLimitAlternative K source limit),
      IsPersistentCrossAxisAlternative A →
        Nonempty (NormalizedPersistentBranchData.{u} K source) := by
  intro K source limit A hA
  cases A with
  | finiteVerticalComplexity finite => exact False.elim hA
  | persistentHorizontalColumn anchor anchor_mem movingCentre movingCentre_mem
      translations translations_eq converges fibre fibre_eq anchor_mem_fibre
      horizontalPlate horizontalPlate_isColumn horizontalPlate_centres persistent_pullback =>
    obtain ⟨vertexAnchor, vertexAnchor_mem, _vertexB, _vertexB_mem, _hdiam, _hdist⟩ :=
      Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair K
    obtain ⟨C : ApproximationContext.{u}, hCregion, hCcentres, hCtarget, hCtiles⟩ :=
      normalizeApproximationContext K (source.centres : Set Tiling.Plane) Set.univ
        vertexAnchor vertexAnchor_mem anchor anchor_mem
    have htarget : C.target = Set.univ := by
      simpa using hCtarget
    have hsourceTiles : TilesOn C.region C.centres Set.univ := by
      have h := hCtiles.mp source.tilesOn
      simpa [htarget] using h
    have hCclosed : IsClosed C.centres := by
      rw [hCcentres]
      have himage : (-anchor) +ᵥ (source.centres : Set Tiling.Plane) =
          Homeomorph.addRight (-anchor) '' (source.centres : Set Tiling.Plane) := by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, hy, by simp [vadd_eq_add, add_comm]⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, hy, by simp [vadd_eq_add, add_comm]⟩
      rw [himage]
      exact (Homeomorph.addRight (-anchor)).isClosed_image.mpr source.centres.isClosed
    let normalizedSource : TilingSpace C.region Set.univ :=
      ⟨⟨C.centres, hCclosed⟩, hsourceTiles⟩
    have hcarrier : C.region.openCarrier =
        positiveSimilarity 1 (-vertexAnchor) '' K.openCarrier := by
      rw [hCregion]
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, by
          simp [positiveSimilarity, vadd_eq_add]
          abel⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, by
          simp [positiveSimilarity, vadd_eq_add]
          abel⟩
    have hlimitTiles : TilesOn C.region
        (positiveSimilarity 1 (-anchor) '' (limit.centres : Set Tiling.Plane)) Set.univ := by
      have hscale : (0 : ℝ) < 1 := by norm_num
      have h := (tilesOn_positiveSimilarity_iff (s := 1) (r := -vertexAnchor)
        (c := -anchor) hscale hcarrier).mpr limit.tilesOn
      have himage : positiveSimilarity 1 (-vertexAnchor + -anchor) ''
          (Set.univ : Set Tiling.Plane) = Set.univ := by
        rw [Set.image_univ, Set.range_eq_univ.mpr (positiveSimilarity_surjective hscale)]
      rw [himage] at h
      exact h
    have hlimitClosed : IsClosed
        (positiveSimilarity 1 (-anchor) '' (limit.centres : Set Tiling.Plane)) := by
      have himage : positiveSimilarity 1 (-anchor) '' (limit.centres : Set Tiling.Plane) =
          Homeomorph.addRight (-anchor) '' (limit.centres : Set Tiling.Plane) := by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, hy, by simp [positiveSimilarity]⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨y, hy, by simp [positiveSimilarity]⟩
      rw [himage]
      exact (Homeomorph.addRight (-anchor)).isClosed_image.mpr limit.centres.isClosed
    let normalizedLimit : TilingSpace C.region Set.univ :=
      ⟨⟨positiveSimilarity 1 (-anchor) '' (limit.centres : Set Tiling.Plane),
        hlimitClosed⟩, hlimitTiles⟩
    let b : aePeriodGroup (Set.univ : Set Tiling.Plane) :=
      ⟨-anchor, by
        rw [aePeriodGroup, Tiling.Polygonal.aePeriodGroup, AddAction.aestabilizer_univ]
        exact AddSubgroup.mem_top (-anchor)⟩
    have hOldTendsto : Tendsto
        (TilingSpace.translateSequence translations source) atTop (nhds limit) :=
      ((locallyFell_metrizable K Set.univ).2 _ limit).mpr converges
    have hTranslateContinuous : Continuous (fun U : TilingSpace K Set.univ =>
        TilingSpace.translate b U) := by
      exact (translationAction_continuous K Set.univ).comp
        (Continuous.prodMk continuous_const continuous_id)
    have hTranslatedTendsto : Tendsto
        (fun n => TilingSpace.translate b
          (TilingSpace.translate (translations n) source)) atTop
        (nhds (TilingSpace.translate b limit)) :=
      (hTranslateContinuous.tendsto limit).comp hOldTendsto
    have hTranslatedConverges : LocallyFellConverges
        (fun n => ((TilingSpace.translate b
          (TilingSpace.translate (translations n) source)).centres : Set Tiling.Plane))
        ((TilingSpace.translate b limit).centres : Set Tiling.Plane) :=
      ((locallyFell_metrizable K Set.univ).2 _ (TilingSpace.translate b limit)).mp
        hTranslatedTendsto
    have hSeqCentres :
        TilingSpace.centresSequence
            (TilingSpace.translateSequence translations normalizedSource) =
          (fun n => ((TilingSpace.translate b
            (TilingSpace.translate (translations n) source)).centres : Set Tiling.Plane)) := by
      funext n
      ext z
      constructor
      · intro hz
        rcases hz with ⟨x, hx, hzx⟩
        change x ∈ C.centres at hx
        rw [hCcentres] at hx
        rcases hx with ⟨y, hy, hxy⟩
        have hy' : y + (translations n : Tiling.Plane) ∈
            ((TilingSpace.translate (translations n) source).centres : Set Tiling.Plane) :=
          ⟨y, hy, rfl⟩
        refine ⟨y + (translations n : Tiling.Plane), hy', ?_⟩
        rw [← hxy] at hzx
        simpa [b, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzx
      · intro hz
        rcases hz with ⟨y, hy, hzy⟩
        change y ∈ (fun x : Tiling.Plane => x + (translations n : Tiling.Plane)) ''
          (source.centres : Set Tiling.Plane) at hy
        rcases hy with ⟨y₀, hy₀, rfl⟩
        refine ⟨y₀ - anchor, ?_, ?_⟩
        · change y₀ - anchor ∈ C.centres
          rw [hCcentres]
          exact ⟨y₀, hy₀, by
            simp only [vadd_eq_add]
            abel⟩
        · change (y₀ - anchor) + (translations n : Tiling.Plane) = z
          rw [sub_eq_add_neg]
          simpa [b, add_assoc, add_comm, add_left_comm] using hzy
    have hLimitCentres :
        (normalizedLimit.centres : Set Tiling.Plane) =
          ((TilingSpace.translate b limit).centres : Set Tiling.Plane) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, by simp [b, positiveSimilarity]⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, by simp [b, positiveSimilarity]⟩
    have hNormalizedConverges : LocallyFellConverges
        (TilingSpace.centresSequence
          (TilingSpace.translateSequence translations normalizedSource))
        (normalizedLimit.centres : Set Tiling.Plane) := by
      rw [hSeqCentres, hLimitCentres]
      exact hTranslatedConverges
    have hNormalizedTendsto : Tendsto
        (TilingSpace.translateSequence translations normalizedSource) atTop
        (nhds normalizedLimit) :=
      ((locallyFell_metrizable C.region Set.univ).2 _ normalizedLimit).mpr
        hNormalizedConverges
    have hLimitHull : normalizedLimit ∈ orbitHull normalizedSource := by
      apply mem_closure_of_tendsto hNormalizedTendsto
      exact Filter.Eventually.of_forall fun n => AddAction.mem_orbit _ (translations n)
    have hsimVadd (u : Tiling.Plane) (S : Set Tiling.Plane) :
        positiveSimilarity 1 u '' S = u +ᵥ S := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, by
          simp [positiveSimilarity, vadd_eq_add]
          abel⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, by
          simp [positiveSimilarity, vadd_eq_add]
          abel⟩
    have hswapVadd (u : Tiling.Plane) (S : Set Tiling.Plane) :
        coordinateSwap '' (u +ᵥ S) = coordinateSwap u +ᵥ (coordinateSwap '' S) := by
      ext z
      constructor
      · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨coordinateSwap y, ⟨y, hy, rfl⟩, coordinateSwap.map_add u y⟩
      · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨u + y, ⟨y, hy, rfl⟩, coordinateSwap.map_add u y⟩
    have hswapOpen (R : Region) :
        R.coordinateSwap.openCarrier = coordinateSwap '' R.openCarrier := by
      change interior (coordinateSwap '' R.support) = coordinateSwap '' interior R.support
      exact (coordinateSwap.toHomeomorph.image_interior R.support).symm
    have hcarrierSwap : C.region.coordinateSwap.openCarrier =
        positiveSimilarity 1 (coordinateSwap (-vertexAnchor)) ''
          K.coordinateSwap.openCarrier := by
      rw [hswapOpen C.region, hCregion, hswapVadd, hswapOpen K]
      ext z
      constructor <;> rintro ⟨y, hy, rfl⟩ <;>
        exact ⟨y, hy, by
          simp [positiveSimilarity, vadd_eq_add]
          abel⟩
    let normalizedFibre : Set Tiling.Plane := (-anchor) +ᵥ fibre
    have hFibreEq : normalizedFibre =
        (normalizedLimit.centres : Set Tiling.Plane) ∩
          {z : Tiling.Plane | z.im = (0 : Tiling.Plane).im} := by
      dsimp [normalizedFibre]
      rw [fibre_eq]
      ext z
      constructor
      · rintro ⟨s, ⟨hsLimit, hsLine⟩, rfl⟩
        change s.im = anchor.im at hsLine
        refine ⟨?_, ?_⟩
        · exact ⟨s, hsLimit, by
            simp [positiveSimilarity, vadd_eq_add]
            abel⟩
        · change (-anchor + s).im = (0 : Tiling.Plane).im
          rw [Complex.add_im, Complex.neg_im, hsLine]
          simp
      · rintro ⟨hz, hzLine⟩
        rcases hz with ⟨s, hsLimit, hzs⟩
        have hsLine : s.im = anchor.im := by
          change z.im = (0 : Tiling.Plane).im at hzLine
          rw [← hzs] at hzLine
          simp [positiveSimilarity] at hzLine
          linarith
        refine ⟨s, ⟨hsLimit, hsLine⟩, ?_⟩
        simpa [positiveSimilarity, vadd_eq_add, add_comm] using hzs
    have hzeroContext : (0 : Tiling.Plane) ∈ C.centres := by
      rw [hCcentres]
      exact ⟨anchor, anchor_mem, by simp [vadd_eq_add]⟩
    have hmovingContext (n : ℕ) : movingCentre n - anchor ∈ C.centres := by
      rw [hCcentres]
      exact ⟨movingCentre n, movingCentre_mem n, by
        simp only [vadd_eq_add]
        abel⟩
    have hzeroFibre : (0 : Tiling.Plane) ∈ normalizedFibre := by
      exact ⟨anchor, anchor_mem_fibre, by simp [vadd_eq_add]⟩
    have hMovingFibre (s : Tiling.Plane) (hs : s ∈ normalizedFibre) :
        ∀ᶠ n : ℕ in atTop, s - (translations n : Tiling.Plane) ∈ C.centres := by
      rcases hs with ⟨t, ht, rfl⟩
      filter_upwards [persistent_pullback t ht] with n hn
      rw [hCcentres]
      exact ⟨t - (translations n : Tiling.Plane), hn, by
        simp only [vadd_eq_add]
        abel⟩
    have hswapLimit : coordinateSwap '' (normalizedLimit.centres : Set Tiling.Plane) =
        positiveSimilarity 1 (coordinateSwap (-anchor)) ''
          (coordinateSwap '' (limit.centres : Set Tiling.Plane)) := by
      rw [show (normalizedLimit.centres : Set Tiling.Plane) =
        positiveSimilarity 1 (-anchor) '' (limit.centres : Set Tiling.Plane) by rfl]
      rw [hsimVadd, hswapVadd, hsimVadd]
    let plateEquiv :
        VerticalPlate K.coordinateSwap
            (coordinateSwap '' (limit.centres : Set Tiling.Plane)) ≃
          VerticalPlate C.region.coordinateSwap
            (positiveSimilarity 1 (coordinateSwap (-anchor)) ''
              (coordinateSwap '' (limit.centres : Set Tiling.Plane))) :=
      verticalPlate_positiveSimilarityEquiv
        (by norm_num) hcarrierSwap (coordinateSwap (-anchor))
    let plateRaw := plateEquiv horizontalPlate
    have transportColumn {T U : Set Tiling.Plane} (h : T = U)
        (P : VerticalPlate C.region.coordinateSwap T) :
        IsVerticalColumn P → IsVerticalColumn (h ▸ P) := by
      intro hP
      cases h
      exact hP
    have transportCentres {T U : Set Tiling.Plane} (h : T = U)
        (P : VerticalPlate C.region.coordinateSwap T) (Q : Set Tiling.Plane)
        (hP : P.centres = Q) : (h ▸ P).centres = Q := by
      cases h
      exact hP
    let plate : VerticalPlate C.region.coordinateSwap
        (coordinateSwap '' (normalizedLimit.centres : Set Tiling.Plane)) :=
      hswapLimit.symm ▸ plateRaw
    have hplateColumn : IsVerticalColumn plate := by
      have hplateRawColumn : IsVerticalColumn plateRaw :=
        (verticalPlate_positiveSimilarityEquiv_isVerticalColumn
          (by norm_num) hcarrierSwap (coordinateSwap (-anchor)) horizontalPlate).mp
          horizontalPlate_isColumn
      exact transportColumn hswapLimit.symm plateRaw hplateRawColumn
    have hplateCentres : plate.centres = coordinateSwap '' normalizedFibre := by
      have hraw : plateRaw.centres =
          positiveSimilarity 1 (coordinateSwap (-anchor)) ''
            horizontalPlate.centres := by
        exact verticalPlate_positiveSimilarityEquiv_centres_image
          (by norm_num) hcarrierSwap (coordinateSwap (-anchor)) horizontalPlate
      have hraw' : plateRaw.centres =
          positiveSimilarity 1 (coordinateSwap (-anchor)) ''
            (coordinateSwap '' fibre) := by
        calc
          plateRaw.centres = positiveSimilarity 1 (coordinateSwap (-anchor)) ''
              horizontalPlate.centres := hraw
          _ = positiveSimilarity 1 (coordinateSwap (-anchor)) ''
              (coordinateSwap '' fibre) := by rw [horizontalPlate_centres]
      have himage : positiveSimilarity 1 (coordinateSwap (-anchor)) ''
          (coordinateSwap '' fibre) = coordinateSwap '' normalizedFibre := by
        calc
          positiveSimilarity 1 (coordinateSwap (-anchor)) ''
              (coordinateSwap '' fibre) =
              coordinateSwap (-anchor) +ᵥ (coordinateSwap '' fibre) :=
                hsimVadd _ _
          _ = coordinateSwap '' ((-anchor) +ᵥ fibre) :=
            (hswapVadd (-anchor) fibre).symm
          _ = coordinateSwap '' normalizedFibre := by rfl
      have hraw'' : plateRaw.centres = coordinateSwap '' normalizedFibre :=
        hraw'.trans himage
      exact transportCentres hswapLimit.symm plateRaw _ hraw''
    let normalizedFibreData : PersistentHorizontalFibreData C normalizedSource := {
      source_centres_eq := by rfl
      limit := normalizedLimit
      limit_mem_hull := hLimitHull
      translations := translations
      converges := hNormalizedConverges
      anchor := 0
      anchor_mem_context := hzeroContext
      movingCentre := fun n => movingCentre n - anchor
      movingCentre_mem_context := hmovingContext
      translations_eq := by
        intro n
        rw [translations_eq]
        simp only [zero_sub]
        abel
      fibre := normalizedFibre
      fibre_eq := hFibreEq
      anchor_mem_fibre := hzeroFibre
      horizontalPlate := plate
      horizontalPlate_isColumn := hplateColumn
      horizontalPlate_centres := hplateCentres
      persistent_pullback := hMovingFibre }
    refine ⟨{
      vertexAnchor := vertexAnchor
      vertexAnchor_mem := vertexAnchor_mem
      centreAnchor := anchor
      centreAnchor_mem := anchor_mem
      context := C
      normalizedSource := normalizedSource
      context_region := hCregion
      context_centres := hCcentres
      context_target := htarget
      normalizedSource_centres := by rfl
      fibre := normalizedFibreData }⟩

private theorem normalization_preserves_nontrivial :
    ∀ {K : Region} {source : TilingSpace K Set.univ}
      (N : NormalizedPersistentBranchData.{u} K source),
      NontrivialVerticalDecomposition K (source.centres : Set Tiling.Plane) →
      NontrivialVerticalDecomposition N.context.region N.context.centres := by
  intro K source N hSource hBad
  have hscale : (0 : ℝ) < 1 := by norm_num
  have hcarrier : N.context.region.openCarrier =
      positiveSimilarity 1 (-N.vertexAnchor) '' K.openCarrier := by
    rw [N.context_region]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by
        simp [positiveSimilarity, vadd_eq_add]
        abel⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by
        simp [positiveSimilarity, vadd_eq_add]
        abel⟩
  have himage : N.context.centres =
      positiveSimilarity 1 (-N.centreAnchor) ''
        (source.centres : Set Tiling.Plane) := by
    rw [N.context_centres]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by
        simp [positiveSimilarity, vadd_eq_add]
        abel⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by
        simp [positiveSimilarity, vadd_eq_add]
        abel⟩
  have hBad' : ∃ P : VerticalPlate N.context.region
      (positiveSimilarity 1 (-N.centreAnchor) ''
        (source.centres : Set Tiling.Plane)),
      ¬ IsVerticalColumn P ∧
        P.centres = positiveSimilarity 1 (-N.centreAnchor) ''
          (source.centres : Set Tiling.Plane) := by
    exact himage ▸ hBad
  rcases hBad' with ⟨P, hPnot, hPcentres⟩
  let P' : VerticalPlate N.context.region
      (positiveSimilarity 1 (-N.centreAnchor) ''
        (source.centres : Set Tiling.Plane)) := P
  let e : VerticalPlate K (source.centres : Set Tiling.Plane) ≃
      VerticalPlate N.context.region
        (positiveSimilarity 1 (-N.centreAnchor) ''
          (source.centres : Set Tiling.Plane)) :=
    verticalPlate_positiveSimilarityEquiv hscale hcarrier (-N.centreAnchor)
  let Q : VerticalPlate K (source.centres : Set Tiling.Plane) := e.symm P'
  have heq : e Q = P' := e.apply_symm_apply P'
  have hQcentres : Q.centres = (source.centres : Set Tiling.Plane) := by
    have heq : e Q = P' := e.apply_symm_apply P'
    have hP'image : P'.centres = positiveSimilarity 1 (-N.centreAnchor) '' Q.centres := by
      rw [← heq]
      exact verticalPlate_positiveSimilarityEquiv_centres_image
        hscale hcarrier (-N.centreAnchor) Q
    have hP'centres : P'.centres = N.context.centres := by
      exact hPcentres.trans himage.symm
    rw [hP'centres] at hP'image
    exact (Set.image_eq_image (positiveSimilarity_injective hscale)).mp
      (hP'image.symm.trans himage)
  have hQnot : ¬ IsVerticalColumn Q := by
    intro hQcol
    apply hPnot
    have hiff := verticalPlate_positiveSimilarityEquiv_isVerticalColumn
      hscale hcarrier (-N.centreAnchor) Q
    have : IsVerticalColumn (e Q) := hiff.mp hQcol
    have hP'col : IsVerticalColumn P' := by
      rw [← heq]
      exact this
    exact hP'col
  exact hSource ⟨Q, hQnot, hQcentres⟩

private theorem realProjection_vadd (u : Tiling.Plane) (S : Set Tiling.Plane) :
    Complex.re '' (u +ᵥ S) = u.re +ᵥ (Complex.re '' S) := by
  ext x
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y.re, ⟨y, hy, rfl⟩, ?_⟩
    simp [vadd_eq_add]
  · rintro ⟨x₀, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨u + y, ⟨y, hy, rfl⟩, ?_⟩
    simp [vadd_eq_add]

private theorem imaginaryProjection_vadd (u : Tiling.Plane) (S : Set Tiling.Plane) :
    Complex.im '' (u +ᵥ S) = u.im +ᵥ (Complex.im '' S) := by
  ext x
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y.im, ⟨y, hy, rfl⟩, ?_⟩
    simp [vadd_eq_add]
  · rintro ⟨x₀, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨u + y, ⟨y, hy, rfl⟩, ?_⟩
    simp [vadd_eq_add]

private theorem horizontalCentreProjection_vadd (u : Tiling.Plane)
    (S : Set Tiling.Plane) :
    horizontalCentreProjection (u +ᵥ S) =
      u.re +ᵥ horizontalCentreProjection S := by
  exact realProjection_vadd u S

private theorem normalization_preserves_infiniteHorizontal :
    ∀ {K : Region} {source : TilingSpace K Set.univ}
      (N : NormalizedPersistentBranchData.{u} K source),
      (¬ HasFiniteHorizontalComplexity (source.centres : Set Tiling.Plane)) →
      ¬ HasFiniteHorizontalComplexity N.context.centres := by
  intro K source N hSource hContext
  have hContextFLC : HasFLC (horizontalCentreProjection N.context.centres) :=
    hContext
  rw [N.context_centres, horizontalCentreProjection_vadd] at hContextFLC
  have hSourceFLC : HasFLC (horizontalCentreProjection
      (source.centres : Set Tiling.Plane)) := by
    have htranslated := hContextFLC.vadd N.centreAnchor.re
    simpa [vadd_vadd, vadd_eq_add, add_assoc, add_comm, add_left_comm] using htranslated
  exact hSource hSourceFLC

private theorem normalization_reflects_productRegion :
    ∀ {K : Region} {source : TilingSpace K Set.univ}
      (N : NormalizedPersistentBranchData.{u} K source),
      IsProductRegion N.context.region → IsProductRegion K := by
  intro K source N hContextProduct
  rw [isProductRegion_iff_regularizedProjections] at hContextProduct ⊢
  have hRealProjection :
      interior (closure (Complex.re '' N.context.region.openCarrier)) =
        (-N.vertexAnchor).re +ᵥ
          interior (closure (Complex.re '' K.openCarrier)) := by
    rw [N.context_region, realProjection_vadd, closure_vadd, interior_vadd]
  have hImaginaryProjection :
      interior (closure (Complex.im '' N.context.region.openCarrier)) =
        (-N.vertexAnchor).im +ᵥ
          interior (closure (Complex.im '' K.openCarrier)) := by
    rw [N.context_region, imaginaryProjection_vadd, closure_vadd, interior_vadd]
  ext z
  constructor
  · intro hz
    have hz' : (-N.vertexAnchor) + z ∈ N.context.region.openCarrier := by
      rw [N.context_region]
      exact ⟨z, hz, rfl⟩
    rw [hContextProduct] at hz'
    rw [hRealProjection, hImaginaryProjection] at hz'
    have hzre : ((-N.vertexAnchor) + z).re ∈
        (-N.vertexAnchor).re +ᵥ
          interior (closure (Complex.re '' K.openCarrier)) := hz'.1
    have hzim : ((-N.vertexAnchor) + z).im ∈
        (-N.vertexAnchor).im +ᵥ
          interior (closure (Complex.im '' K.openCarrier)) := hz'.2
    constructor
    · simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hzre
    · simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hzim
  · intro hz
    have hz' : (-N.vertexAnchor) + z ∈
        {w : Tiling.Plane |
          w.re ∈ interior (closure (Complex.re '' N.context.region.openCarrier)) ∧
          w.im ∈ interior (closure (Complex.im '' N.context.region.openCarrier))} := by
      rw [hRealProjection, hImaginaryProjection]
      constructor
      · refine ⟨z.re, hz.1, ?_⟩
        simp [vadd_eq_add]
      · refine ⟨z.im, hz.2, ?_⟩
        simp [vadd_eq_add]
    have hz'' : (-N.vertexAnchor) + z ∈ N.context.region.openCarrier :=
      hContextProduct.symm ▸ hz'
    rw [N.context_region] at hz''
    obtain ⟨w, hw, hweq⟩ := hz''
    have hweq' : -N.vertexAnchor + w = -N.vertexAnchor + z := by
      simpa [vadd_eq_add] using hweq
    have : w = z := add_left_cancel hweq'
    exact this ▸ hw

private structure ApproximationSequenceData (C : ApproximationContext.{u}) where
  epsilon : ℕ → ℝ
  epsilon_pos : ∀ n, 0 < epsilon n
  epsilon_zero : Tendsto epsilon atTop (nhds 0)
  map : (n : ℕ) → C.coordinateSpace →ₗ[ℚ] ℚ
  isApproximation : ∀ n, IsEpsilonApproximation C (epsilon n) (map n)
  deformation : (n : ℕ) → CoordinateDeformation C (map n)
  transport : (n : ℕ) →
    TwoStageDeformationSupportTransport C (map n) (deformation n)

private theorem approximationSequenceData_exists :
    ∀ (C : ApproximationContext.{u}),
      TilesOn C.region C.centres Set.univ →
        Nonempty (ApproximationSequenceData C) := by
  intro C hTiles
  obtain ⟨ε₀, hε₀, hgood⟩ := isGoodApproximation_of_sufficientlyFine C
  let ε : ℕ → ℝ := fun n ↦ ε₀ / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    exact div_pos hε₀ (by positivity)
  have hεzero : Tendsto ε atTop (nhds 0) := by
    have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact tendsto_const_nhds.div_atTop hden
  choose φ hφ using fun n ↦ exists_epsilonApproximation C (ε n) (hεpos n)
  have hle : ∀ n, ε n ≤ ε₀ := by
    intro n
    dsimp [ε]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hgoodφ : ∀ n, IsGoodApproximation C (φ n) := by
    intro n
    apply hgood (φ n)
    refine {
      epsilon_pos := lt_of_lt_of_le (hφ n |>.epsilon_pos) (hle n)
      fixesRational := (hφ n).fixesRational
      basis_close := fun j ↦ lt_of_lt_of_le ((hφ n).basis_close j) (hle n) }
  let D : (n : ℕ) → CoordinateDeformation C (φ n) := fun n ↦
    (exists_rationalPolygonDeformation C (φ n) (hgoodφ n)).some
  let P : (n : ℕ) → TwoStageDeformationSupportTransport C (φ n) (D n) :=
    fun n ↦ (exists_twoStageDeformationSupportTransport C (φ n) (D n) hTiles).some
  exact ⟨{
    epsilon := ε
    epsilon_pos := hεpos
    epsilon_zero := hεzero
    map := φ
    isApproximation := hφ
    deformation := D
    transport := P }⟩

/- The normalized persistent fibre survives each actual rational deformation as
   two transverse columns of one deformed tiling. -/
set_option linter.unusedVariables false in
private theorem simultaneousColumns_force_deformedProducts :
    ∀ {K : Region} {source : TilingSpace K Set.univ}
      (N : NormalizedPersistentBranchData.{u} K source)
      (hNontrivial : NontrivialVerticalDecomposition
        N.context.region N.context.centres)
      (hInfinite : ¬ HasFiniteHorizontalComplexity N.context.centres)
      (A : ApproximationSequenceData N.context),
      ∀ n, IsProductRegion (A.deformation n).deformedRegion := by
  intro K source N hNontrivial hInfinite A n
  obtain ⟨O, hData⟩ :=
    exists_orbitLimit_withSimultaneousColumns
      N.fibre hNontrivial hInfinite (A.deformation n) (A.transport n)
  obtain ⟨M⟩ := hData
  exact productRegion_of_transverseColumns
    M.horizontal.limit.tilesOn
    M.verticalColumn M.verticalColumn_isColumn
    M.horizontal.horizontalColumn M.horizontal.horizontalColumn_isColumn

/- Products for all errors tending to zero descend to the original tile;
   the two different normalization shifts are reflected separately. -/
set_option linter.unusedVariables false in
private theorem normalizedPersistentBranch_productRegion :
    ∀ {K : Region} {source : TilingSpace K Set.univ}
      (N : NormalizedPersistentBranchData.{u} K source),
      NontrivialVerticalDecomposition K (source.centres : Set Tiling.Plane) →
      (¬ HasFiniteHorizontalComplexity (source.centres : Set Tiling.Plane)) →
        IsProductRegion K := by
  intro K source N hNontrivial hInfinite
  have hNNontrivial := normalization_preserves_nontrivial N hNontrivial
  have hNInfinite := normalization_preserves_infiniteHorizontal N hInfinite
  have hTiles : TilesOn N.context.region N.context.centres Set.univ := by
    rw [← N.normalizedSource_centres]
    exact N.normalizedSource.tilesOn
  obtain ⟨A⟩ := approximationSequenceData_exists N.context hTiles
  have hProducts :=
    simultaneousColumns_force_deformedProducts N hNNontrivial hNInfinite A
  have hContextProduct :=
    productRegion_of_deformations N.context A.epsilon A.epsilon_pos
      A.epsilon_zero A.map A.isApproximation A.deformation hProducts
  exact normalization_reflects_productRegion N hContextProduct

/- S04 denies every nonzero horizontal period of this exact aggregate support;
   S07 supplies one positive period of it for a product tile. -/
private theorem infiniteNontrivial_productRegion_false :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      NontrivialVerticalDecomposition K T →
      (¬ HasFiniteHorizontalComplexity T) →
      IsProductRegion K → False := by
  intro K T hTiles hNontrivial hInfinite hProduct
  have hAperiodic :=
    (infiniteHorizontalComplexity_iff_columnBaseAperiodic
      hTiles hNontrivial).1.mp hInfinite
  have hColumns : (Continuous.verticalColumnCentres K T).Nonempty := by
    by_contra hEmpty
    have hEmpty' : Continuous.verticalColumnCentres K T = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hEmpty
    have hSupportEmpty :
        regularSupport K (Continuous.verticalColumnCentres K T) = ∅ := by
      simp [regularSupport, Tiling.Polygonal.regularSupport,
        Tiling.Polygonal.openUnion, hEmpty']
    exact Set.not_nonempty_empty (hSupportEmpty ▸ hAperiodic.1)
  obtain ⟨beta, hbeta, hperiod⟩ :=
    productRegion_columnUnion_horizontalPeriodic K hProduct
  exact hAperiodic.2 beta (ne_of_gt hbeta) (hperiod T hTiles hColumns)

set_option linter.unusedVariables false in
private theorem persistentCrossAxisAlternative_false :
    ∀ {K : Region} {source limit : TilingSpace K Set.univ}
      (hNontrivial : NontrivialVerticalDecomposition K
        (source.centres : Set Tiling.Plane))
      (hInfinite : ¬ HasFiniteHorizontalComplexity
        (source.centres : Set Tiling.Plane))
      (A : CrossAxisLimitAlternative K source limit),
      IsPersistentCrossAxisAlternative A → False := by
  intro K source limit hNontrivial hInfinite A hA
  obtain ⟨N⟩ := normalizedPersistentBranch_exists.{0} A hA
  have hProduct := normalizedPersistentBranch_productRegion N hNontrivial hInfinite
  exact infiniteNontrivial_productRegion_false
    source.tilesOn hNontrivial hInfinite hProduct

/-- A non-FLC whole-plane tiling has an oriented hull limit with finite
horizontal complexity and nontrivial vertical decomposition. -/
theorem exists_finiteHorizontalComplexityTrichotomy
    {K : Region} (T : TilingSpace K Set.univ)
    (hNotFLC : ¬ HasFLC (T.centres : Set Tiling.Plane)) :
    Nonempty (FiniteHorizontalComplexityTrichotomyData K T) := by
  obtain ⟨E⟩ := planeNontrivialEarthquake_exists T hNotFLC
  cases hOrientation : E.split.orientation with
  | vertical =>
      have hNontrivial := verticalEarthquakeSplit_nontrivial E hOrientation
      by_cases hFinite : HasFiniteHorizontalComplexity
          (E.limit.centres : Set Tiling.Plane)
      · exact trichotomyData_vertical_of E.limit_mem_hull hFinite hNontrivial
      · obtain ⟨S, hHull, hSwapNontrivial, hAlternative⟩ :=
          exists_crossAxisOrbitLimit E.limit hNontrivial hFinite
        obtain ⟨A⟩ := hAlternative
        by_cases hPersistent : IsPersistentCrossAxisAlternative A
        · exact False.elim
            (persistentCrossAxisAlternative_false hNontrivial hFinite A hPersistent)
        · cases A with
          | finiteVerticalComplexity hFiniteSwapped =>
              obtain ⟨Sσ, hSσ⟩ := coordinateSwapTiling_exists S
              have hSwapNontrivial' :
                  NontrivialVerticalDecomposition K.coordinateSwap
                    (Sσ.centres : Set Tiling.Plane) := by
                change ¬ ∃ P : Continuous.VerticalPlate K.coordinateSwap
                    (Sσ.centres : Set Tiling.Plane),
                    ¬ Continuous.IsVerticalColumn P ∧
                      P.centres = (Sσ.centres : Set Tiling.Plane)
                rw [hSσ]
                exact hSwapNontrivial
              have hFiniteSwapped' :
                  HasFiniteHorizontalComplexity
                    (Sσ.centres : Set Tiling.Plane) := by
                rw [hSσ]
                exact hFiniteSwapped
              exact trichotomyData_horizontal_of (K := K) (T := T) (S := S)
                Sσ hSσ (orbitHull_transitive E.limit_mem_hull hHull)
                hFiniteSwapped' hSwapNontrivial'
          | persistentHorizontalColumn anchor anchor_mem_source movingCentre
              movingCentre_mem translations translations_eq converges fibre
              fibre_eq anchor_mem_fibre horizontalPlate horizontalPlate_isColumn
              horizontalPlate_centres persistent_pullback =>
              exact False.elim (hPersistent trivial)
  | horizontal =>
      obtain ⟨Eσ, hEσ⟩ := coordinateSwapTiling_exists E.limit
      have hNontrivialσ := horizontalEarthquakeSplit_nontrivial
        E Eσ hEσ hOrientation
      by_cases hFinite : HasFiniteHorizontalComplexity
          (Eσ.centres : Set Tiling.Plane)
      · exact trichotomyData_horizontal_of (K := K) (T := T) (S := E.limit)
          Eσ hEσ E.limit_mem_hull hFinite hNontrivialσ
      · obtain ⟨S₁, hS₁, hS₁Nontrivial, hAlternative⟩ :=
          exists_crossAxisOrbitLimit Eσ hNontrivialσ hFinite
        obtain ⟨A⟩ := hAlternative
        by_cases hPersistent : IsPersistentCrossAxisAlternative A
        · exact False.elim
            (persistentCrossAxisAlternative_false hNontrivialσ hFinite A hPersistent)
        · cases A with
          | finiteVerticalComplexity hFiniteSwapped =>
              obtain ⟨U, hUcentres, hUHull, hUNontrivial, hUFinite⟩ :=
                swappedCrossAxisFiniteBranch Eσ hEσ E.limit_mem_hull
                  S₁ hS₁ hS₁Nontrivial hFiniteSwapped
              exact trichotomyData_vertical_of hUHull hUFinite hUNontrivial
          | persistentHorizontalColumn anchor anchor_mem_source movingCentre
              movingCentre_mem translations translations_eq converges fibre
              fibre_eq anchor_mem_fibre horizontalPlate horizontalPlate_isColumn
              horizontalPlate_centres persistent_pullback =>
              exact False.elim (hPersistent trivial)

end Tiling.AxisParallel.Structure
