import Mathlib.Order.Filter.Basic
import Tiling.AxisParallel.Structure.HorizontalComplexityCharacterization.BoundaryDensity
import Tiling.AxisParallel.Structure.HorizontalComplexityCharacterization.ColumnBaseCharacterization
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.HorizontalComplexityCore
import Tiling.AxisParallel.Continuous.PlateCore
import Tiling.AxisParallel.Continuous.PersistentTransientSlabs
import Tiling.AxisParallel.Continuous.PositiveSimilarityPlates
import Tiling.AxisParallel.Continuous.WeakTilingTopology
import Tiling.AxisParallel.Structure.HorizontalComplexityCharacterization.EdgeOffsets
import Tiling.AxisParallel.Topology.FellCore
import Tiling.AxisParallel.Topology.HullCore

/-!
# Cross-axis limits

Private dependency-closed S05 records and helper proofs accompany the public
historical alternative below.
-/

open Filter Set
open scoped Pointwise Topology

set_option warningAsError true

noncomputable section

namespace Tiling.AxisParallel.Structure

/-- The two outcomes of the cross-axis limiting argument. -/
inductive CrossAxisLimitAlternative
    (K : Tiling.AxisParallel.Region)
    (T S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ) where
  | finiteVerticalComplexity
      (finite :
        Tiling.AxisParallel.Continuous.HasFiniteHorizontalComplexity
          (Tiling.AxisParallel.coordinateSwap ''
            (S.centres : Set Tiling.Plane))) :
      CrossAxisLimitAlternative K T S
  | persistentHorizontalColumn
      (anchor : Tiling.Plane)
      (anchor_mem_source : anchor ∈ (T.centres : Set Tiling.Plane))
      (movingCentre : ℕ → Tiling.Plane)
      (movingCentre_mem : ∀ n : ℕ,
        movingCentre n ∈ (T.centres : Set Tiling.Plane))
      (translations : ℕ → Tiling.AxisParallel.aePeriodGroup Set.univ)
      (translations_eq : ∀ n : ℕ,
        (translations n : Tiling.Plane) = anchor - movingCentre n)
      (converges : Tiling.AxisParallel.Topology.LocallyFellConverges
        (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
          (Tiling.AxisParallel.Topology.TilingSpace.translateSequence translations T))
        (S.centres : Set Tiling.Plane))
      (fibre : Set Tiling.Plane)
      (fibre_eq : fibre =
        (S.centres : Set Tiling.Plane) ∩ {z : Tiling.Plane | z.im = anchor.im})
      (anchor_mem_fibre : anchor ∈ fibre)
      (horizontalPlate : Tiling.AxisParallel.Continuous.VerticalPlate
        K.coordinateSwap
          (Tiling.AxisParallel.coordinateSwap '' (S.centres : Set Tiling.Plane)))
      (horizontalPlate_isColumn :
        Tiling.AxisParallel.Continuous.IsVerticalColumn horizontalPlate)
      (horizontalPlate_centres : horizontalPlate.centres =
        Tiling.AxisParallel.coordinateSwap '' fibre)
      (persistent_pullback : ∀ s ∈ fibre, ∀ᶠ n : ℕ in Filter.atTop,
        s - (translations n : Tiling.Plane) ∈ (T.centres : Set Tiling.Plane)) :
      CrossAxisLimitAlternative K T S

open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Topology

private abbrev NontrivialDecomposition (K : Region) (T : Set Tiling.Plane) :=
  ¬ ∃ P : VerticalPlate K T, ¬ IsVerticalColumn P ∧ P.centres = T

/-! Auxiliary S05 consumer adapter; this is not an additional counted target. -/

private theorem atMostOneNoncolumn_of_not_finiteHorizontalComplexity
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (hNontrivial :
      ¬ ∃ P : VerticalPlate K T,
        ¬ IsVerticalColumn P ∧ P.centres = T)
    (hInfinite : ¬ HasFiniteHorizontalComplexity T) :
    ∀ P Q : VerticalPlate K T,
      ¬ IsVerticalColumn P →
      ¬ IsVerticalColumn Q → P = Q := by
  intro P Q hPnoncolumn hQnoncolumn
  by_contra hPQ
  obtain ⟨M, hM, hDense⟩ :=
    componentBoundarySet_relativelyDense_of_two_noncolumnPlates hTile
      ⟨P, Q, hPQ, hPnoncolumn, hQnoncolumn⟩
  exact hInfinite (finiteHorizontalComplexity_of_relativelyDenseBoundaries
    hTile hNontrivial ⟨M, hM, hDense⟩)

private structure EscapingHorizontalContactData (K : Region) (T : Set Tiling.Plane) where
  a : ↑K.vertices
  b : ↑K.vertices
  a' : ↑K.vertices
  b' : ↑K.vertices
  left : ℕ → ↑T
  right : ℕ → ↑T
  distinct : ∀ n : ℕ, left n ≠ right n
  contact : ∀ n : ℕ, HorizontalProperContact K (left n).1 (right n).1
  labelled : ∀ n : ℕ,
    ((right n).1 - (left n).1).re ∈
      Tiling.AxisParallel.Structure.horizontalContactDisplacements K T a b a' b'
  horizontal_injective : Function.Injective
    (fun n ↦ ((right n).1 - (left n).1).re)
  common_vertical_displacement : ∀ n : ℕ,
    ((right n).1 - (left n).1).im = a.1.im - a'.1.im

private theorem im_eq_of_mem_openSegment_horizontal_local
    {a b p : Tiling.Plane} (hab : a.im = b.im)
    (hp : p ∈ openSegment ℝ a b) : p.im = a.im := by
  rw [openSegment_eq_image] at hp
  obtain ⟨r, _hr, rfl⟩ := hp
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rw [hab]
  ring

private theorem horizontalContactDisplacement_witness
    {K : Region} {T : Set Tiling.Plane}
    {a b a' b' : ↥K.vertices} {d : ℝ}
    (hd : d ∈ horizontalContactDisplacements K T a b a' b')
    (hdne : d ≠ 0) :
    ∃ t s : ↥T,
      t ≠ s ∧ HorizontalProperContact K t.1 s.1 ∧
      d = ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).re ∧
      ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).im = a.1.im - a'.1.im := by
  have hdOrig := hd
  rw [horizontalContactDisplacements_iff] at hd
  obtain ⟨hab, habIm, habEdge, ha'b', ha'b'Im, ha'b'Edge,
    t, s, hdEq, u, v, huv, huvIm, huvOverlap⟩ := hd
  have htne : t ≠ s := by
    intro hts
    apply hdne
    rw [hdEq, hts]
    simp
  have hpBoth := huvOverlap (midpoint_mem_openSegment (𝕜 := ℝ) u v)
  have hpFirstIm := im_eq_of_mem_openSegment_horizontal_local
    (by simp only [Complex.add_im]; linarith [habIm]) hpBoth.1
  have hpSecondIm := im_eq_of_mem_openSegment_horizontal_local
    (by simp only [Complex.add_im]; linarith [ha'b'Im]) hpBoth.2
  have him : ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).im =
      a.1.im - a'.1.im := by
    rw [Complex.sub_im]
    simp only [Complex.add_im] at hpFirstIm hpSecondIm
    linarith
  have hadj : (Continuous.verticalPlateGraph K T).Adj t s := by
    apply (verticalPlateGraph_adj_iff_exists_horizontalContactDisplacement K T t s).2
    have hmem :
        ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).re ∈
          horizontalContactDisplacements K T a b a' b' := by
      rw [← hdEq]
      exact hdOrig
    exact ⟨htne, ⟨a, b, a', b', him, hmem⟩⟩
  have hcontact : HorizontalProperContact K t.1 s.1 :=
    (Continuous.verticalPlateGraph_adj_iff t s).mp hadj |>.2
  exact ⟨t, s, htne, hcontact, hdEq, him⟩

private theorem escapingHorizontalContactData_of_infinite_displacements
    {K : Region} {T : Set Tiling.Plane}
    {a b a' b' : ↥K.vertices}
    (hinfinite :
      (horizontalContactDisplacements K T a b a' b').Infinite) :
    Nonempty (EscapingHorizontalContactData K T) := by
  classical
  let D : Set ℝ := horizontalContactDisplacements K T a b a' b' \ {0}
  have hD : D.Infinite := hinfinite.sdiff (Set.finite_singleton 0)
  let e : ℕ ↪ D := hD.to_subtype.natEmbedding
  have hwitness (n : ℕ) :
      ∃ t s : ↥T,
        t ≠ s ∧ HorizontalProperContact K t.1 s.1 ∧
        (e n : ℝ) = ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).re ∧
        ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).im = a.1.im - a'.1.im := by
    have hmem := (e n).property
    change (e n : ℝ) ∈ horizontalContactDisplacements K T a b a' b' ∧
      (e n : ℝ) ≠ 0 at hmem
    apply horizontalContactDisplacement_witness hmem.1 hmem.2
  choose left right hdistinct hcontact hdelta him using hwitness
  refine ⟨⟨a, b, a', b', left, right, hdistinct, hcontact, ?_, ?_, ?_⟩⟩
  · intro n
    rw [← hdelta n]
    exact (show (e n : ℝ) ∈ D from (e n).property).1
  · intro m n hmn
    have hemn : (e m : ℝ) = (e n : ℝ) :=
      (hdelta m).trans (hmn.trans (hdelta n).symm)
    apply e.injective
    apply Subtype.ext
    exact hemn
  · exact him

private theorem escapingHorizontalContacts_exists
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (hNontrivial : NontrivialDecomposition K T)
    (hInfinite : ¬ HasFiniteHorizontalComplexity T) :
    Nonempty (EscapingHorizontalContactData K T) := by
  obtain ⟨a, b, a', b', hDisp⟩ :=
    ((infiniteHorizontalComplexity_iff_columnBaseAperiodic
      hTile hNontrivial).2.2).mp hInfinite
  exact escapingHorizontalContactData_of_infinite_displacements hDisp

private structure CoupledCrossAxisLimits
    (K : Region) (T : TilingSpace K Set.univ)
    (E : EscapingHorizontalContactData K (T.centres : Set Tiling.Plane)) where
  anchor : Tiling.Plane
  anchor' : Tiling.Plane
  anchor_eq : anchor = (E.left 0).1
  anchor'_eq : anchor' = (E.right 0).1
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  translations : ℕ → aePeriodGroup Set.univ
  translations' : ℕ → aePeriodGroup Set.univ
  translations_eq : ∀ n : ℕ,
    (translations n : Tiling.Plane) = anchor - (E.left (subsequence n)).1
  translations'_eq : ∀ n : ℕ,
    (translations' n : Tiling.Plane) = anchor' - (E.right (subsequence n)).1
  limit : TilingSpace K Set.univ
  limit' : TilingSpace K Set.univ
  converges : LocallyFellConverges
    (TilingSpace.centresSequence (TilingSpace.translateSequence translations T))
    (limit.centres : Set Tiling.Plane)
  converges' : LocallyFellConverges
    (TilingSpace.centresSequence (TilingSpace.translateSequence translations' T))
    (limit'.centres : Set Tiling.Plane)
  limit_mem_hull : limit ∈ orbitHull T
  limit'_mem_hull : limit' ∈ orbitHull T
  offsetLimit : Tiling.Plane
  offsets_converge : Tendsto
    (fun n ↦ (E.right (subsequence n)).1 - (E.left (subsequence n)).1)
    atTop (nhds offsetLimit)
  persistent : Set Tiling.Plane
  persistent' : Set Tiling.Plane
  split : PersistentTransientSplit K Set.univ
    (TilingSpace.translateSequence translations T) limit
  split' : PersistentTransientSplit K Set.univ
    (TilingSpace.translateSequence translations' T) limit'
  persistent_eq_split : persistent = split.persistent
  persistent'_eq_split : persistent' = split'.persistent
  persistent_eq : persistent = {s ∈ (limit.centres : Set Tiling.Plane) |
    ∀ᶠ n : ℕ in atTop, s - (translations n : Tiling.Plane) ∈
      (T.centres : Set Tiling.Plane)}
  persistent'_eq : persistent' = {s ∈ (limit'.centres : Set Tiling.Plane) |
    ∀ᶠ n : ℕ in atTop, s - (translations' n : Tiling.Plane) ∈
      (T.centres : Set Tiling.Plane)}
  anchor_persistent : anchor ∈ persistent
  anchor'_persistent : anchor' ∈ persistent'
  movingLimit : Tiling.Plane
  movingLimit' : Tiling.Plane
  movingLimit_eq : movingLimit = anchor + offsetLimit
  movingLimit'_eq : movingLimit' = anchor' - offsetLimit
  movingLimit_mem : movingLimit ∈ (limit.centres : Set Tiling.Plane)
  movingLimit'_mem : movingLimit' ∈ (limit'.centres : Set Tiling.Plane)
  movingLimit_transient : movingLimit ∉ persistent
  movingLimit'_transient : movingLimit' ∉ persistent'

private theorem persistentTransientSplit_subsequence
    {K : Region} {X : Set ℝ}
    {U : ℕ → TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    {S : TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    (D : PersistentTransientSplit K X U S) {phi : ℕ → ℕ}
    (hphi : StrictMono phi) :
    ∃ D' : PersistentTransientSplit K X (U ∘ phi) S,
      D'.persistent = D.persistent ∧ D'.transient = D.transient ∧
      D'.orientation = D.orientation ∧
      D'.persistentBase = D.persistentBase ∧
      D'.transientBase = D.transientBase := by
  refine ⟨D.subsequence phi hphi, rfl, rfl, rfl, rfl, rfl⟩

private theorem injective_subsequence_avoiding_limit
    {f : ℕ → Tiling.Plane} {z : Tiling.Plane}
    (hinj : Function.Injective f)
    (hlim : Tendsto f atTop (nhds z)) :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ Function.Injective (f ∘ psi) ∧
      Tendsto (f ∘ psi) atTop (nhds z) ∧ ∀ n, f (psi n) ≠ z := by
  by_cases h : ∃ k, f k = z
  · obtain ⟨k, hk⟩ := h
    let psi : ℕ → ℕ := fun n ↦ n + (k + 1)
    have hpsi : StrictMono psi := strictMono_id.add_const _
    refine ⟨psi, hpsi, hinj.comp hpsi.injective, hlim.comp hpsi.tendsto_atTop, ?_⟩
    intro n hn
    have hnk : psi n ≠ k := by
      dsimp only [psi]
      omega
    apply hnk
    apply hinj
    exact hn.trans hk.symm
  · exact ⟨id, strictMono_id, hinj, by simpa using hlim,
      fun n hn ↦ h ⟨n, hn⟩⟩

private theorem anchoredOrbitLimit
    {K : Region} {T : TilingSpace K Set.univ}
    (g : ℕ → aePeriodGroup Set.univ) (anchor : Tiling.Plane)
    (moving : ℕ → Tiling.Plane) {R : ℝ}
    (hmoving_bound : ∀ n, moving n ∈ Metric.closedBall anchor R)
    (hanchor_mem : ∀ n, anchor ∈
      ((TilingSpace.translate (g n) T).centres : Set Tiling.Plane))
    (hmoving_mem : ∀ n, moving n ∈
      ((TilingSpace.translate (g n) T).centres : Set Tiling.Plane))
    (hmoving_injective : Function.Injective moving) :
    ∃ (phi : ℕ → ℕ) (S : TilingSpace K Set.univ) (z : Tiling.Plane),
      StrictMono phi ∧ S ∈ orbitHull T ∧
      LocallyFellConverges
        (TilingSpace.centresSequence (TilingSpace.translateSequence (g ∘ phi) T))
        (S.centres : Set Tiling.Plane) ∧
      (∀ n, anchor ∈
        ((TilingSpace.translate (g (phi n)) T).centres : Set Tiling.Plane)) ∧
      anchor ∈ (S.centres : Set Tiling.Plane) ∧
      z ∈ (S.centres : Set Tiling.Plane) ∧ z ≠ anchor ∧
      Function.Injective (moving ∘ phi) ∧
      Tendsto (moving ∘ phi) atTop (nhds z) ∧
      (∀ n, moving (phi n) ≠ z) := by
  let _ : CompactSpace (TilingSpace K Set.univ) :=
    isCompact_univ_iff.mp (tilingSpace_compact K Set.univ)
  obtain ⟨S, phi₀, hphi₀, hUlim⟩ :=
    CompactSpace.tendsto_subseq (TilingSpace.translateSequence g T)
  obtain ⟨z, _hzball, phi₁, hphi₁, hzlim⟩ :=
    (isCompact_closedBall anchor R).tendsto_subseq
      (fun n ↦ hmoving_bound (phi₀ n))
  let phi := phi₀ ∘ phi₁
  have hphi : StrictMono phi := hphi₀.comp hphi₁
  have hUlim' : Tendsto
      (TilingSpace.translateSequence g T ∘ phi) atTop (nhds S) :=
    hUlim.comp hphi₁.tendsto_atTop
  have hconv : LocallyFellConverges
      (TilingSpace.centresSequence (TilingSpace.translateSequence (g ∘ phi) T))
      (S.centres : Set Tiling.Plane) := by
    apply (locallyFell_metrizable K Set.univ).2 _ S |>.mp
    change Tendsto (fun n ↦ TilingSpace.translate (g (phi n)) T)
      atTop (nhds S)
    simpa [phi, TilingSpace.translateSequence, Function.comp_def] using hUlim'
  have hanchor_limit : anchor ∈ (S.centres : Set Tiling.Plane) :=
    Tiling.AxisParallel.Continuous.mem_of_locallyFellConverges_of_tendsto_mem hconv
      (fun n ↦ hanchor_mem (phi n)) tendsto_const_nhds
  have hmoving_limit : z ∈ (S.centres : Set Tiling.Plane) :=
    Tiling.AxisParallel.Continuous.mem_of_locallyFellConverges_of_tendsto_mem hconv
      (fun n ↦ hmoving_mem (phi n))
      (by simpa [phi, Function.comp_def] using hzlim)
  obtain ⟨psi, hpsi, hmoving_injective', hmoving_limit', hneq⟩ :=
    injective_subsequence_avoiding_limit
      (hmoving_injective.comp hphi.injective)
      (by simpa [phi, Function.comp_def] using hzlim)
  let finalPhi := phi ∘ psi
  have hfinal : StrictMono finalPhi := hphi.comp hpsi
  have hconv' : LocallyFellConverges
      (TilingSpace.centresSequence
        (TilingSpace.translateSequence (g ∘ finalPhi) T))
      (S.centres : Set Tiling.Plane) := by
    rcases hconv with ⟨hclosed, hSclosed, hconv⟩
    refine ⟨fun n ↦ hclosed (psi n), hSclosed, ?_⟩
    simpa [finalPhi, TilingSpace.centresSequence,
      TilingSpace.translateSequence, Function.comp_def] using
      hconv.comp hpsi.tendsto_atTop
  have hmovlimFinal : Tendsto (moving ∘ finalPhi) atTop (nhds z) := by
    simpa [finalPhi, Function.comp_assoc] using hmoving_limit'
  have hseparation : ∃ δ : ℝ, 0 < δ ∧
      ∀ n, Tiling.AxisParallel.Topology.IsUniformlySeparated δ
        ((TilingSpace.translate (g (finalPhi n)) T).centres : Set Tiling.Plane) := by
    obtain ⟨δ, hδ, hsep⟩ := tilesOn_uniformlySeparated K
    exact ⟨δ, hδ, fun n ↦ hsep _ _
      (TilingSpace.translate (g (finalPhi n)) T).tilesOn⟩
  have hanchor_ne_moving : z ≠ anchor := by
    obtain ⟨δ, hδ, hsep⟩ := hseparation
    intro hza
    have hdist : ∀ n, δ ≤ dist anchor (moving (finalPhi n)) := by
      intro n
      have hne : moving (finalPhi n) ≠ anchor := by
        intro hma
        apply hneq n
        change moving (phi (psi n)) = anchor at hma
        rw [hza]
        exact hma
      simpa [dist_comm] using hsep n (hmoving_mem (finalPhi n))
        (hanchor_mem (finalPhi n)) hne
    have hdistlim : Tendsto (fun n ↦ dist anchor (moving (finalPhi n)))
        atTop (nhds (dist anchor z)) :=
      (continuous_const.dist continuous_id).tendsto z |>.comp hmovlimFinal
    have hδz : δ ≤ dist anchor z :=
      isClosed_Ici.mem_of_tendsto hdistlim (Filter.Eventually.of_forall hdist)
    rw [hza, dist_self] at hδz
    exact (not_le_of_gt hδ) hδz
  have hShull : S ∈ orbitHull T := by
    apply isClosed_closure.mem_of_tendsto hUlim'
    filter_upwards [] with n
    apply subset_closure
    have horbit : TilingSpace.translate (g (phi n)) T ∈
        AddAction.orbit (aePeriodGroup Set.univ) T :=
      ⟨g (phi n), rfl⟩
    simpa [TilingSpace.translateSequence, Function.comp_apply] using horbit
  refine ⟨finalPhi, S, z, hfinal, hShull, hconv', ?_, hanchor_limit,
    hmoving_limit, hanchor_ne_moving, hmoving_injective', hmovlimFinal, ?_⟩
  · intro n
    exact hanchor_mem (finalPhi n)
  · intro n
    exact hneq n

private theorem eventuallyAbsentOfSeparation
    {K : Region} {U : ℕ → TilingSpace K Set.univ}
    {zseq : ℕ → Tiling.Plane} {z : Tiling.Plane}
    (hzmem : ∀ n, zseq n ∈ ((U n).centres : Set Tiling.Plane))
    (hzlim : Tendsto zseq atTop (nhds z))
    (hzneq : ∀ n, zseq n ≠ z) :
    ∀ᶠ n : ℕ in atTop, z ∉ ((U n).centres : Set Tiling.Plane) := by
  obtain ⟨δ, hδ, hsep⟩ := tilesOn_uniformlySeparated K
  have hclose : ∀ᶠ n : ℕ in atTop, dist (zseq n) z < δ := by
    filter_upwards [hzlim.eventually (Metric.ball_mem_nhds z hδ)] with n hn
    simpa only [Metric.mem_ball, dist_comm] using hn
  filter_upwards [hclose] with n hn hz
  exact (not_lt_of_ge (hsep _ _ (U n).tilesOn (hzmem n) hz (hzneq n))) hn

private theorem persistent_of_exact
    {K : Region} {U : ℕ → TilingSpace K Set.univ}
    {S : TilingSpace K Set.univ}
    (D : PersistentTransientSplit K Set.univ U S)
    {a : Tiling.Plane} (haS : a ∈ (S.centres : Set Tiling.Plane))
    (haU : ∀ n, a ∈ ((U n).centres : Set Tiling.Plane)) :
    a ∈ D.persistent := by
  rw [← D.union_eq] at haS
  rcases haS with ha | ha
  · exact ha
  · have hfalse : ∀ᶠ n : ℕ in atTop, False :=
      (D.transient_eventuallyNotMem a ha).mono fun n hn ↦ hn (haU n)
    exact False.elim hfalse.exists.choose_spec

private theorem transient_of_absent
    {K : Region} {U : ℕ → TilingSpace K Set.univ}
    {S : TilingSpace K Set.univ}
    (D : PersistentTransientSplit K Set.univ U S)
    {z : Tiling.Plane} (hzS : z ∈ (S.centres : Set Tiling.Plane))
    (hzAbsent : ∀ᶠ n : ℕ in atTop,
      z ∉ ((U n).centres : Set Tiling.Plane)) :
    z ∈ D.transient := by
  rw [← D.union_eq] at hzS
  rcases hzS with hz | hz
  · have hfalse : ∀ᶠ n : ℕ in atTop, False :=
      (D.persistent_eventuallyMem z hz).and hzAbsent |>.mono
        fun n hn ↦ hn.2 (hn.1)
    exact False.elim hfalse.exists.choose_spec
  · exact hz

private theorem persistent_eq_eventual
    {K : Region} {U : ℕ → TilingSpace K Set.univ}
    {S : TilingSpace K Set.univ}
    (D : PersistentTransientSplit K Set.univ U S) :
    D.persistent = {s ∈ (S.centres : Set Tiling.Plane) |
      ∀ᶠ n : ℕ in atTop, s ∈ ((U n).centres : Set Tiling.Plane)} := by
  ext s
  constructor
  · intro hs
    exact ⟨D.persistent_subset hs, D.persistent_eventuallyMem s hs⟩
  · rintro ⟨hs, hev⟩
    rw [← D.union_eq] at hs
    rcases hs with hs | hs
    · exact hs
    · have hfalse : ∀ᶠ n : ℕ in atTop, False :=
        (D.transient_eventuallyNotMem s hs).and hev |>.mono
          fun n hn ↦ hn.1 (hn.2)
      exact False.elim hfalse.exists.choose_spec

private theorem coupledCrossAxisLimits_exists
    {K : Region} (T : TilingSpace K Set.univ)
    (E : EscapingHorizontalContactData K (T.centres : Set Tiling.Plane)) :
    Nonempty (CoupledCrossAxisLimits K T E) := by
  classical
  let left : ℕ → Tiling.Plane := fun n ↦ (E.left n).1
  let right : ℕ → Tiling.Plane := fun n ↦ (E.right n).1
  let anchor : Tiling.Plane := left 0
  let anchor' : Tiling.Plane := right 0
  have hdiff : Function.Injective (right - left) := by
    intro m n hmn
    apply E.horizontal_injective
    exact congrArg Complex.re hmn
  obtain ⟨R, hR⟩ :=
    Tiling.AxisParallel.Structure.horizontalContactDisplacements_bounded
      K (T.centres : Set Tiling.Plane) E.a E.b E.a' E.b'
  have hRpair (n : ℕ) : ∀ d ∈
      Tiling.AxisParallel.Structure.horizontalContactDisplacements K
        (T.centres : Set Tiling.Plane) E.a E.b E.a' E.b',
      |(right n - left n).re - d| ≤ R := by
    intro d hd
    exact hR (show (right n - left n).re ∈ _ from by
      simpa [left, right] using E.labelled n)
      (show d ∈ _ from by simpa only [compl_compl] using hd)
  let d₀ : ℝ := (right 0 - left 0).re
  let c₀ : ℝ := E.a.1.im - E.a'.1.im
  let R₀ : ℝ := |d₀| + R + |c₀|
  have hbound (n : ℕ) : right n - left n ∈ Metric.closedBall 0 R₀ := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hp := hRpair n d₀ (by simpa only [compl_compl] using E.labelled 0)
    have him : (right n - left n).im = c₀ := by
      simpa [c₀, left, right] using E.common_vertical_displacement n
    dsimp [d₀] at hp
    have hp' : |(right n - left n).re - d₀| ≤ R := by
      simpa [d₀] using hp
    have hreal : |(right n - left n).re| ≤ |d₀| + R := by
      calc
        |(right n - left n).re| =
            |((right n - left n).re - d₀) + d₀| := by
              congr 1
              ring
        _ ≤ |(right n - left n).re - d₀| + |d₀| := abs_add_le _ _
        _ = |d₀| + |(right n - left n).re - d₀| := by ring
        _ = |(right n - left n).re - d₀| + |d₀| := by ring
        _ ≤ R + |d₀| := add_le_add_left hp' |d₀|
        _ = |d₀| + R := by ring
    calc
      ‖right n - left n‖ ≤
          |(right n - left n).re| + |(right n - left n).im| :=
            Complex.norm_le_abs_re_add_abs_im _
      _ ≤ |(right n - left n).re| + |c₀| := by rw [him]
      _ ≤ (|d₀| + R) + |c₀| := add_le_add hreal (le_refl _)
      _ = R₀ := by rfl
  let translations₀ : ℕ → aePeriodGroup Set.univ := fun n ↦
    ⟨anchor - left n, by
      change anchor - left n ∈ AddAction.aestabilizer Tiling.Plane
        MeasureTheory.volume (Set.univ : Set Tiling.Plane)
      rw [AddAction.mem_aestabilizer]
      simp⟩
  let moving₀ : ℕ → Tiling.Plane := fun n ↦ right n + (translations₀ n : Tiling.Plane)
  have hanchor_mem₀ (n : ℕ) : anchor ∈
      ((TilingSpace.translate (translations₀ n) T).centres : Set Tiling.Plane) := by
    change anchor ∈ (fun x ↦ x + (translations₀ n : Tiling.Plane)) ''
      (T.centres : Set Tiling.Plane)
    refine ⟨left n, (E.left n).2, ?_⟩
    dsimp [translations₀, anchor]
    abel
  have hmoving_mem₀ (n : ℕ) : moving₀ n ∈
      ((TilingSpace.translate (translations₀ n) T).centres : Set Tiling.Plane) := by
    change moving₀ n ∈ (fun x ↦ x + (translations₀ n : Tiling.Plane)) ''
      (T.centres : Set Tiling.Plane)
    exact ⟨right n, (E.right n).2, rfl⟩
  have hmoving_injective₀ : Function.Injective moving₀ := by
    intro m n hmn
    apply hdiff
    have hmn' := congrArg (fun z : Tiling.Plane => z - anchor) hmn
    dsimp [moving₀, translations₀, anchor] at hmn'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmn'
  have hmoving_bound₀ (n : ℕ) : moving₀ n ∈ Metric.closedBall anchor R₀ := by
    simpa [Metric.mem_closedBall, dist_eq_norm, moving₀, translations₀, anchor,
      AddSubgroup.coe_mk, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using hbound n
  obtain ⟨phi₀, S₀, movingLimit₀, hphi₀, hHull₀, hconv₀,
      hanchor_mem₀', hanchor_limit₀, hmoving_limit₀, hne₀,
      hmovinj₀, hmovlim₀, hneq₀⟩ := anchoredOrbitLimit translations₀ anchor moving₀
      hmoving_bound₀ hanchor_mem₀ hmoving_mem₀ hmoving_injective₀
  let U₀ := TilingSpace.translateSequence (translations₀ ∘ phi₀) T
  have hconv₀' : LocallyFellConverges
      (TilingSpace.centresSequence U₀) (S₀.centres : Set Tiling.Plane) := by
    simpa [U₀, TilingSpace.centresSequence, Function.comp_def] using hconv₀
  obtain ⟨phi₁, D₁, hphi₁⟩ := exists_persistentTransientSplit
    (show (Set.univ : Set ℝ).Nonempty by simp)
    (show IsOpen (Set.univ : Set ℝ) by simp)
    (show interior (closure (Set.univ : Set ℝ)) = Set.univ by simp)
    (fun C _ ↦ by simp) U₀ S₀ hconv₀'
  let phiA := phi₀ ∘ phi₁
  have hphiA : StrictMono phiA := hphi₀.comp hphi₁
  let translationsA : ℕ → aePeriodGroup Set.univ := translations₀ ∘ phiA
  have hconvA : LocallyFellConverges
      (TilingSpace.centresSequence (TilingSpace.translateSequence translationsA T))
      (S₀.centres : Set Tiling.Plane) := by
    rcases hconv₀ with ⟨hclosed, hSclosed, hconv⟩
    refine ⟨fun n ↦ hclosed (phi₁ n), hSclosed, ?_⟩
    simpa [translationsA, phiA, TilingSpace.translateSequence,
      TilingSpace.centresSequence, Function.comp_def] using
      hconv.comp hphi₁.tendsto_atTop
  have hanchor_memA (n : ℕ) : anchor ∈
      ((TilingSpace.translate (translationsA n) T).centres : Set Tiling.Plane) := by
    exact hanchor_mem₀ (phiA n)
  have hmov_memA (n : ℕ) : moving₀ (phiA n) ∈
      ((TilingSpace.translate (translationsA n) T).centres : Set Tiling.Plane) := by
    exact hmoving_mem₀ (phiA n)
  have hmovlimA : Tendsto (moving₀ ∘ phiA) atTop (nhds movingLimit₀) :=
    hmovlim₀.comp hphi₁.tendsto_atTop
  have hAbsA : ∀ᶠ n : ℕ in atTop, movingLimit₀ ∉
      ((TilingSpace.translate (translationsA n) T).centres : Set Tiling.Plane) :=
    eventuallyAbsentOfSeparation hmov_memA hmovlimA
      (fun n ↦ hneq₀ (phi₁ n))
  have hanchor_persistentA : anchor ∈ D₁.persistent := persistent_of_exact D₁
    hanchor_limit₀ hanchor_memA
  have hmov_limitA : movingLimit₀ ∈ (S₀.centres : Set Tiling.Plane) :=
    Tiling.AxisParallel.Continuous.mem_of_locallyFellConverges_of_tendsto_mem
      hconvA hmov_memA hmovlimA
  have hmov_transientA : movingLimit₀ ∈ D₁.transient :=
    transient_of_absent D₁ hmov_limitA hAbsA
  let translationsB : ℕ → aePeriodGroup Set.univ := fun n ↦
    ⟨anchor' - right (phiA n), by
      change anchor' - right (phiA n) ∈ AddAction.aestabilizer Tiling.Plane
        MeasureTheory.volume (Set.univ : Set Tiling.Plane)
      rw [AddAction.mem_aestabilizer]
      simp⟩
  let movingB : ℕ → Tiling.Plane := fun n ↦ left (phiA n) + (translationsB n : Tiling.Plane)
  have hanchor_memB (n : ℕ) : anchor' ∈
      ((TilingSpace.translate (translationsB n) T).centres : Set Tiling.Plane) := by
    change anchor' ∈ (fun x ↦ x + (translationsB n : Tiling.Plane)) ''
      (T.centres : Set Tiling.Plane)
    refine ⟨right (phiA n), (E.right (phiA n)).2, ?_⟩
    dsimp [translationsB, anchor']
    abel
  have hmov_memB (n : ℕ) : movingB n ∈
      ((TilingSpace.translate (translationsB n) T).centres : Set Tiling.Plane) := by
    change movingB n ∈ (fun x ↦ x + (translationsB n : Tiling.Plane)) ''
      (T.centres : Set Tiling.Plane)
    exact ⟨left (phiA n), (E.left (phiA n)).2, rfl⟩
  have hmovinjB : Function.Injective movingB := by
    intro m n hmn
    apply hphiA.injective
    apply hdiff
    have hmn' := congrArg (fun z : Tiling.Plane => anchor' - z) hmn
    dsimp [movingB, translationsB, anchor'] at hmn'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmn'
  have hmovboundB (n : ℕ) : movingB n ∈ Metric.closedBall anchor' R₀ := by
    have hb := hbound (phiA n)
    rw [Metric.mem_closedBall, dist_eq_norm]
    change ‖movingB n - anchor'‖ ≤ R₀
    dsimp [movingB, translationsB, anchor']
    rw [show left (phiA n) + (right 0 - right (phiA n)) - right 0 =
      -(right (phiA n) - left (phiA n)) by ring, norm_neg]
    simpa using hb
  obtain ⟨phi₂, S₂, movingLimit₂, hphi₂, hHull₂, hconv₂,
      hanchor_mem₂, hanchor_limit₂, hmov_limit₂, hne₂, hmovinj₂,
      hmovlim₂, hneq₂⟩ := anchoredOrbitLimit translationsB anchor' movingB
      hmovboundB hanchor_memB hmov_memB hmovinjB
  let phiB := phiA ∘ phi₂
  have hphiB : StrictMono phiB := hphiA.comp hphi₂
  let translationsB' := translationsB ∘ phi₂
  have hconvB : LocallyFellConverges
      (TilingSpace.centresSequence
        (TilingSpace.translateSequence translationsB' T))
      (S₂.centres : Set Tiling.Plane) := by
    simpa [translationsB', TilingSpace.translateSequence,
      TilingSpace.centresSequence, Function.comp_def] using hconv₂
  obtain ⟨phi₃, D₂, hphi₃⟩ := exists_persistentTransientSplit
    (show (Set.univ : Set ℝ).Nonempty by simp)
    (show IsOpen (Set.univ : Set ℝ) by simp)
    (show interior (closure (Set.univ : Set ℝ)) = Set.univ by simp)
    (fun C _ ↦ by simp) (TilingSpace.translateSequence translationsB' T) S₂ hconvB
  let phiFinal := phiB ∘ phi₃
  have hphiFinal : StrictMono phiFinal := hphiB.comp hphi₃
  let split : PersistentTransientSplit K Set.univ
      (TilingSpace.translateSequence (translations₀ ∘ phiFinal) T) S₀ :=
    D₁.subsequence (phi₂ ∘ phi₃) (hphi₂.comp hphi₃)
  let split' := D₂
  have hsplit_eq : split.persistent = D₁.persistent := rfl
  have hsplit'_eq : split'.persistent = D₂.persistent := rfl
  have hanchor_persistentB : anchor' ∈ D₂.persistent := persistent_of_exact D₂
    hanchor_limit₂ (fun n ↦ by
      change anchor' ∈ ((TilingSpace.translate
        (translationsB' (phi₃ n)) T).centres : Set Tiling.Plane)
      exact hanchor_mem₂ (phi₃ n))
  have hmovlimBmem : movingLimit₂ ∈ (S₂.centres : Set Tiling.Plane) := hmov_limit₂
  have hmov_transientB : movingLimit₂ ∈ D₂.transient := by
    apply transient_of_absent D₂ hmovlimBmem
    apply eventuallyAbsentOfSeparation
    · intro n
      change movingB (phi₂ (phi₃ n)) ∈
        ((TilingSpace.translate (translationsB' (phi₃ n)) T).centres : Set Tiling.Plane)
      exact hmov_memB (phi₂ (phi₃ n))
    · exact hmovlim₂.comp hphi₃.tendsto_atTop
    · exact fun n ↦ hneq₂ (phi₃ n)
  let offsetLimit : Tiling.Plane := movingLimit₀ - anchor
  have hoffsets₀ : Tendsto (fun n ↦ right (phiFinal n) - left (phiFinal n))
      atTop (nhds offsetLimit) := by
    have hmov := hmovlimA.comp (hphi₂.comp hphi₃).tendsto_atTop
    have hrel : (fun n ↦ moving₀ (phiFinal n) - anchor) =
        (fun n ↦ right (phiFinal n) - left (phiFinal n)) := by
      funext n
      dsimp [moving₀, translations₀, anchor]
      abel
    rw [← hrel]
    exact (continuous_id.sub continuous_const).tendsto movingLimit₀ |>.comp hmov
  have hmovBlimit_eq : movingLimit₂ = anchor' - offsetLimit := by
    have hmovB : Tendsto (fun n ↦ movingB (phi₂ (phi₃ n))) atTop
        (nhds movingLimit₂) := hmovlim₂.comp hphi₃.tendsto_atTop
    have hoff := hoffsets₀
    have hrel : (fun n ↦ movingB (phi₂ (phi₃ n))) =
        (fun n ↦ anchor' - (right (phiFinal n) - left (phiFinal n))) := by
      funext n
      dsimp [movingB, translationsB, phiFinal, phiB]
      abel
    rw [hrel] at hmovB
    have htarget : Tendsto
        (fun _ : ℕ ↦ anchor' - offsetLimit) atTop
        (nhds (anchor' - offsetLimit)) := tendsto_const_nhds
    have hlim : Tendsto
        (fun n ↦ anchor' - (right (phiFinal n) - left (phiFinal n)))
        atTop (nhds (anchor' - offsetLimit)) := by
      simpa using (tendsto_const_nhds.sub hoff)
    exact tendsto_nhds_unique hmovB hlim
  have hconvFinal : LocallyFellConverges
      (TilingSpace.centresSequence
        (TilingSpace.translateSequence (translations₀ ∘ phiFinal) T))
      (S₀.centres : Set Tiling.Plane) := by
    rcases hconvA with ⟨hclosed, hSclosed, hconv⟩
    refine ⟨fun n ↦ hclosed (phi₂ (phi₃ n)), hSclosed, ?_⟩
    simpa [phiFinal, translationsA, TilingSpace.translateSequence,
      TilingSpace.centresSequence, Function.comp_def, phiB] using
      hconv.comp (hphi₂.comp hphi₃).tendsto_atTop
  have hconv₂Final : LocallyFellConverges
      (TilingSpace.centresSequence
        (TilingSpace.translateSequence (translationsB' ∘ phi₃) T))
      (S₂.centres : Set Tiling.Plane) := by
    rcases hconv₂ with ⟨hclosed, hSclosed, hconv⟩
    refine ⟨fun n ↦ hclosed (phi₃ n), hSclosed, ?_⟩
    simpa [translationsB', TilingSpace.translateSequence,
      TilingSpace.centresSequence, Function.comp_def] using
      hconv.comp hphi₃.tendsto_atTop
  have memTranslate (g : aePeriodGroup Set.univ) (s : Tiling.Plane) :
      s ∈ ((TilingSpace.translate g T).centres : Set Tiling.Plane) ↔
        s - (g : Tiling.Plane) ∈ (T.centres : Set Tiling.Plane) := by
    change s ∈ (fun x ↦ x + (g : Tiling.Plane)) ''
        (T.centres : Set Tiling.Plane) ↔ _
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hs
      refine ⟨s - (g : Tiling.Plane), hs, ?_⟩
      abel
  have eventual_mem_translate (gseq : ℕ → aePeriodGroup Set.univ)
      (s : Tiling.Plane) :
      (∀ᶠ n : ℕ in atTop,
        s ∈ ((TilingSpace.translate (gseq n) T).centres : Set Tiling.Plane)) ↔
      (∀ᶠ n : ℕ in atTop,
        s - (gseq n : Tiling.Plane) ∈ (T.centres : Set Tiling.Plane)) := by
    constructor
    · intro h
      filter_upwards [h] with n hn
      exact (memTranslate (gseq n) s).mp hn
    · intro h
      filter_upwards [h] with n hn
      exact (memTranslate (gseq n) s).mpr hn
  refine ⟨{
    anchor := anchor,
    anchor' := anchor',
    anchor_eq := rfl,
    anchor'_eq := rfl,
    subsequence := phiFinal,
    subsequence_strictMono := hphiFinal,
    translations := translations₀ ∘ phiFinal,
    translations' := translationsB ∘ phi₂ ∘ phi₃,
    translations_eq := by intro n; rfl,
    translations'_eq := by intro n; rfl,
    limit := S₀,
    limit' := S₂,
    converges := hconvFinal,
    converges' := hconv₂Final,
    limit_mem_hull := hHull₀,
    limit'_mem_hull := hHull₂,
    offsetLimit := offsetLimit,
    offsets_converge := hoffsets₀,
    persistent := split.persistent,
    persistent' := split'.persistent,
    split := split,
    split' := split',
    persistent_eq_split := rfl,
    persistent'_eq_split := rfl,
    persistent_eq := by
      rw [persistent_eq_eventual split]
      ext s
      constructor
      · rintro ⟨hs, hev⟩
        have hev' : ∀ᶠ n : ℕ in atTop,
            s ∈
              ((TilingSpace.translate (translations₀ (phiFinal n)) T).centres :
                Set Tiling.Plane) := by
          filter_upwards [hev] with n hn
          change s ∈
            ((TilingSpace.translate ((translations₀ ∘ phiFinal) n) T).centres :
              Set Tiling.Plane) at hn
          rw [show (translations₀ ∘ phiFinal) n = translations₀ (phiFinal n) by rfl] at hn
          exact hn
        exact ⟨hs, (eventual_mem_translate (translations₀ ∘ phiFinal) s).mp hev'⟩
      · rintro ⟨hs, hev⟩
        exact ⟨hs, (eventual_mem_translate (translations₀ ∘ phiFinal) s).mpr hev⟩
    persistent'_eq := by
      rw [persistent_eq_eventual split']
      ext s
      constructor
      · rintro ⟨hs, hev⟩
        have hev' : ∀ᶠ n : ℕ in atTop,
            s ∈
              ((TilingSpace.translate (translationsB' (phi₃ n)) T).centres :
                Set Tiling.Plane) := by
          filter_upwards [hev] with n hn
          exact hn
        exact ⟨hs, (eventual_mem_translate (translationsB' ∘ phi₃) s).mp hev'⟩
      · rintro ⟨hs, hev⟩
        exact ⟨hs, (eventual_mem_translate (translationsB' ∘ phi₃) s).mpr hev⟩
    anchor_persistent := by
      change anchor ∈ D₁.persistent
      exact hanchor_persistentA,
    anchor'_persistent := hanchor_persistentB,
    movingLimit := movingLimit₀,
    movingLimit' := movingLimit₂,
    movingLimit_eq := by dsimp [offsetLimit]; ring,
    movingLimit'_eq := hmovBlimit_eq,
    movingLimit_mem := by
      exact Tiling.AxisParallel.Continuous.mem_of_locallyFellConverges_of_tendsto_mem
        hconvFinal
        (fun n ↦ by
          change moving₀ (phiFinal n) ∈
            ((TilingSpace.translate (translations₀ (phiFinal n)) T).centres : Set Tiling.Plane)
          exact hmov_memA (phi₂ (phi₃ n)))
        (hmovlimA.comp (hphi₂.comp hphi₃).tendsto_atTop),
    movingLimit'_mem := hmovlimBmem,
    movingLimit_transient := by
      change movingLimit₀ ∉ D₁.persistent
      intro hp
      exact Set.disjoint_left.mp D₁.disjoint hp hmov_transientA,
    movingLimit'_transient := by
      change movingLimit₂ ∉ D₂.persistent
      intro hp
      exact Set.disjoint_left.mp D₂.disjoint hp hmov_transientB }⟩

private theorem persistentVerticalSlab_excludes_crossingContact
    {K : Region} {T A : Set Tiling.Plane} {t s : T}
    (hTile : TilesOn K T Set.univ) (hAT : A ⊆ T) (htA : t.1 ∈ A) (hsA : s.1 ∉ A)
    (hContact : HorizontalProperContact K t.1 s.1)
    (hInvariant : ∀ y : ℝ, ((y : ℂ) * Complex.I) +ᵥ regularSupport K A =
      regularSupport K A) : False := by
  obtain ⟨XA, hAsupport⟩ :=
    (Tiling.AxisParallel.verticalInvariant_iff_product
      (regularSupport K A)).mp hInvariant
  have hXAreg : interior (closure XA) = XA := by
    have hreg := (Tiling.AxisParallel.regularSupport_isRegularOpen K A).2
    rw [hAsupport] at hreg
    change interior (closure (Complex.re ⁻¹' XA)) = Complex.re ⁻¹' XA at hreg
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re] at hreg
    exact (Set.preimage_injective.mpr Complex.re_surjective) hreg
  let B : Set Tiling.Plane := T \ A
  have hUnion : A ∪ B = T := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact hAT hz
      · exact hz.1
    · intro hz
      by_cases hzA : z ∈ A
      · exact Or.inl hzA
      · exact Or.inr ⟨hz, hzA⟩
  have hTslab : ∃ X : Set ℝ, X = interior (closure X) ∧
      regularSupport K T = Complex.re ⁻¹' X := by
    refine ⟨Set.univ, by simp, ?_⟩
    rw [Tiling.AxisParallel.regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile]
    simp
  obtain ⟨XB, hXBreg, hBsupport⟩ :=
    verticalSlab_sdiff hTile (Subset.rfl) hAT hTslab
      ⟨XA, hXAreg.symm, hAsupport⟩
  let parts : Bool → Set Tiling.Plane
    | false => A
    | true => B
  have hparts : Set.PairwiseDisjoint Set.univ parts := by
    intro i _ j _ hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact Set.disjoint_left.2 fun _ hzA hzB ↦ hzB.2 hzA
    · exact Set.disjoint_left.2 fun _ hzB hzA ↦ hzB.2 hzA
    · exact (hij rfl).elim
  have hpartsUnion : (⋃ i, parts i) = T := by
    rw [show (⋃ i, parts i) = A ∪ B by
      ext z
      simp [parts]]
    exact hUnion
  have hSupportDisjoint : Disjoint (regularSupport K A)
      (regularSupport K B) := by
    have hpair := (Tiling.AxisParallel.regularSupport_pairwiseDisjoint
      parts hparts hpartsUnion hTile).1
    have h := hpair (Set.mem_univ false) (Set.mem_univ true) (by decide)
    change Disjoint (regularSupport K A) (regularSupport K B) at h
    exact h
  have hsat := verticalPlates_saturated_of_slabPartition K hUnion hSupportDisjoint
    hXAreg hXBreg.symm hAsupport hBsupport
  let P : VerticalPlate K T := VerticalPlate.ofCentre t
  have htP : t.1 ∈ P.centres := VerticalPlate.mem_centres_ofCentre t
  have hneq : t ≠ s := by
    intro h
    exact hsA (h ▸ htA)
  have hadj : (verticalPlateGraph K T).Adj t s :=
    (verticalPlateGraph_adj_iff t s).2 ⟨hneq, hContact⟩
  have hmk : (verticalPlateGraph K T).connectedComponentMk t =
      (verticalPlateGraph K T).connectedComponentMk s :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
  have hmkP : (verticalPlateGraph K T).connectedComponentMk t = P := by
    rfl
  have hsSupp : s ∈ P.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff P s).2 (hmk.symm.trans hmkP)
  have hsP : s.1 ∈ P.centres := ⟨s, hsSupp, rfl⟩
  exact hsA (hsat.1 P ⟨t.1, htP, htA⟩ hsP)

private theorem coupledLimits_translation_eq
    {K : Region} {T : TilingSpace K Set.univ}
    {E : EscapingHorizontalContactData K (T.centres : Set Tiling.Plane)}
    (L : CoupledCrossAxisLimits K T E) :
    (L.anchor' - L.movingLimit) +ᵥ (L.limit.centres : Set Tiling.Plane) =
      (L.limit'.centres : Set Tiling.Plane) := by
  let gammaPlane : Tiling.Plane := L.anchor' - L.movingLimit
  let gamma : aePeriodGroup Set.univ :=
    ⟨gammaPlane, by simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]⟩
  let residual : ℕ → aePeriodGroup Set.univ :=
    fun n ↦ L.translations' n - L.translations n
  have hresidual : Tendsto residual atTop (nhds gamma) := by
    rw [tendsto_subtype_rng]
    have hoff : Tendsto
        (fun n ↦ (L.translations' n : Tiling.Plane) -
          (L.translations n : Tiling.Plane)) atTop (nhds gammaPlane) := by
      have h := L.offsets_converge.const_sub (L.anchor' - L.anchor)
      convert h using 1 <;> simp [gammaPlane, L.movingLimit_eq,
        L.translations_eq, L.translations'_eq,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    exact hoff
  have hU : Tendsto
      (TilingSpace.translateSequence L.translations T) atTop (nhds L.limit) :=
    ((locallyFell_metrizable K Set.univ).2
      (TilingSpace.translateSequence L.translations T) L.limit).mpr L.converges
  have hpair : Tendsto
      (fun n ↦ (residual n,
        TilingSpace.translateSequence L.translations T n)) atTop
      (nhds (gamma, L.limit)) := by
    rw [nhds_prod_eq]
    exact hresidual.prodMk hU
  have haction := (translationAction_continuous K Set.univ).tendsto
    (gamma, L.limit)
  have hlim := haction.comp hpair
  have hlim' : Tendsto
      (fun n ↦ residual n +ᵥ TilingSpace.translateSequence L.translations T n)
      atTop (nhds (TilingSpace.translate gamma L.limit)) := by
    change Tendsto
      (fun n ↦ TilingSpace.translationAction K Set.univ
        (residual n, TilingSpace.translateSequence L.translations T n))
      atTop (nhds (TilingSpace.translate gamma L.limit)) at hlim
    exact hlim
  have hseq : (fun n ↦ residual n +ᵥ
      TilingSpace.translateSequence L.translations T n) =
      TilingSpace.translateSequence L.translations' T := by
    funext n
    change TilingSpace.translate (residual n)
      (TilingSpace.translate (L.translations n) T) =
      TilingSpace.translate (L.translations' n) T
    change residual n +ᵥ (L.translations n +ᵥ T) =
      L.translations' n +ᵥ T
    rw [← add_vadd]
    congr 1
    dsimp [residual]
    exact sub_add_cancel _ _
  rw [hseq] at hlim'
  have hU' : Tendsto (TilingSpace.translateSequence L.translations' T)
      atTop (nhds L.limit') :=
    ((locallyFell_metrizable K Set.univ).2
      (TilingSpace.translateSequence L.translations' T) L.limit').mpr L.converges'
  have heq : TilingSpace.translate gamma L.limit = L.limit' :=
    tendsto_nhds_unique hlim' hU'
  have hcentres := congrArg (fun U : TilingSpace K Set.univ =>
      (U.centres : Set Tiling.Plane)) heq
  change (fun x : Tiling.Plane ↦ x + gammaPlane) ''
      (L.limit.centres : Set Tiling.Plane) =
    (L.limit'.centres : Set Tiling.Plane) at hcentres
  ext z
  rw [mem_vadd_set]
  constructor
  · rintro ⟨y, hy, hyz⟩
    apply (Set.ext_iff.mp hcentres z).mp
    refine ⟨y, hy, ?_⟩
    simpa [gammaPlane, add_comm] using hyz
  · intro hz
    obtain ⟨y, hy, hyz⟩ := (Set.ext_iff.mp hcentres z).mpr hz
    refine ⟨y, hy, ?_⟩
    simpa [gammaPlane, add_comm] using hyz

private theorem coupledPersistentOverlap_forces_eventualOffsetEq
    {K : Region} {T : TilingSpace K Set.univ}
    {E : EscapingHorizontalContactData K (T.centres : Set Tiling.Plane)}
    (L : CoupledCrossAxisLimits K T E)
    {p q : Tiling.Plane} (hp : p ∈ L.persistent) (hq : q ∈ L.persistent')
    (hpq : q = (L.anchor' - L.movingLimit) + p) :
    ∀ᶠ n : ℕ in atTop,
      (E.right (L.subsequence n)).1 - (E.left (L.subsequence n)).1 =
        L.offsetLimit := by
  rw [L.persistent_eq] at hp
  rw [L.persistent'_eq] at hq
  have hp_event := hp.2
  have hq_event := hq.2
  obtain ⟨delta, hdelta, hseparate⟩ := tilesOn_uniformlySeparated K
  have hTseparate := hseparate Set.univ (T.centres : Set Tiling.Plane) T.tilesOn
  let source : ℕ → Tiling.Plane :=
    fun n ↦ p - (L.translations n : Tiling.Plane)
  let source' : ℕ → Tiling.Plane :=
    fun n ↦ q - (L.translations' n : Tiling.Plane)
  have hsource_close : Tendsto (fun n ↦ source n - source' n)
      atTop (nhds 0) := by
    have hoff : Tendsto
        (fun n ↦ (L.translations' n : Tiling.Plane) -
          (L.translations n : Tiling.Plane)) atTop
        (nhds (L.anchor' - L.movingLimit)) := by
      have h := L.offsets_converge.const_sub (L.anchor' - L.anchor)
      convert h using 1 <;> simp [L.movingLimit_eq,
        L.translations_eq, L.translations'_eq,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have hzero : Tendsto
        (fun _ : ℕ ↦ p - q +
          ((L.translations' _ : Tiling.Plane) - (L.translations _ : Tiling.Plane)))
        atTop (nhds (p - q + (L.anchor' - L.movingLimit))) :=
      (tendsto_const_nhds.add hoff)
    have hzero' : Tendsto
        (fun n ↦ source n - source' n) atTop (nhds 0) := by
      convert hzero using 1
      · funext n
        dsimp [source, source']
        rw [hpq]
        abel
      · rw [hpq]
        abel
    exact hzero'
  have hsmall : ∀ᶠ n : ℕ in atTop,
      dist (source n) (source' n) < delta := by
    filter_upwards [hsource_close.eventually (Metric.ball_mem_nhds 0 hdelta)] with n hn
    have hn' : dist (source n - source' n) 0 < delta := by
      simpa [Metric.mem_ball, dist_comm] using hn
    simpa [dist_eq_norm, sub_eq_add_neg] using hn'
  have hequal : ∀ᶠ n : ℕ in atTop, source n = source' n := by
    filter_upwards [hp_event, hq_event, hsmall] with n hpn hqn hdist
    by_contra hne
    have hsep := hTseparate (by simpa [source] using hpn)
      (by simpa [source'] using hqn) hne
    exact (not_lt_of_ge hsep) hdist
  filter_upwards [hequal] with n hn
  have htrans :
      (L.translations' n : Tiling.Plane) - (L.translations n : Tiling.Plane) =
        L.anchor' - L.movingLimit := by
    have hn' := hn
    dsimp [source, source'] at hn'
    rw [hpq] at hn'
    calc
      (L.translations' n : Tiling.Plane) - (L.translations n : Tiling.Plane) =
          (L.anchor' - L.movingLimit) -
            ((L.anchor' - L.movingLimit) + p -
              (L.translations' n : Tiling.Plane) -
              (p - (L.translations n : Tiling.Plane))) := by abel
      _ = L.anchor' - L.movingLimit := by rw [hn']; simp
  have hoffset := L.translations_eq n
  have hoffset' := L.translations'_eq n
  rw [hoffset, hoffset'] at htrans
  have htrans' :
      (E.right (L.subsequence n)).1 - (E.left (L.subsequence n)).1 =
        L.movingLimit - L.anchor := by
    calc
      (E.right (L.subsequence n)).1 - (E.left (L.subsequence n)).1 =
          L.anchor' - L.anchor -
            (L.anchor' - (E.right (L.subsequence n)).1 -
              (L.anchor - (E.left (L.subsequence n)).1)) := by abel
      _ = L.anchor' - L.anchor - (L.anchor' - L.movingLimit) := by
        rw [htrans]
      _ = L.movingLimit - L.anchor := by abel
  rw [L.movingLimit_eq] at htrans'
  convert htrans' using 1
  abel_nf

private theorem coupledLimits_translationAndPersistentDisjoint
    {K : Region} {T : TilingSpace K Set.univ}
    {E : EscapingHorizontalContactData K (T.centres : Set Tiling.Plane)}
    (L : CoupledCrossAxisLimits K T E) :
    let w := L.anchor' - L.movingLimit
    w +ᵥ (L.limit.centres : Set Tiling.Plane) =
        (L.limit'.centres : Set Tiling.Plane) ∧
      Disjoint (w +ᵥ L.persistent) L.persistent' := by
  dsimp
  refine ⟨coupledLimits_translation_eq L, ?_⟩
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_vadd_set] at hx
  obtain ⟨p, hp, hpx⟩ := hx
  have hoffset := coupledPersistentOverlap_forces_eventualOffsetEq L hp hx'
    hpx.symm
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hoffset)
  have hN0 := hN N le_rfl
  have hN1 := hN (N + 1) (Nat.le_succ N)
  have hRe :
      ((E.right (L.subsequence N)).1 - (E.left (L.subsequence N)).1).re =
        ((E.right (L.subsequence (N + 1))).1 -
          (E.left (L.subsequence (N + 1))).1).re := by
    exact congrArg Complex.re (hN0.trans hN1.symm)
  have hindex : L.subsequence N = L.subsequence (N + 1) :=
    E.horizontal_injective hRe
  exact (Nat.ne_of_lt (L.subsequence_strictMono (Nat.lt_succ_self N))) hindex

private theorem persistentHorizontalPlate_isCompleteFibre
    {K : Region} {T S : TilingSpace K Set.univ}
    {g : ℕ → aePeriodGroup Set.univ} {A : Set Tiling.Plane}
    {anchor : Tiling.Plane}
    (P : VerticalPlate K.coordinateSwap
      (coordinateSwap '' (S.centres : Set Tiling.Plane)))
    (_hconv : LocallyFellConverges
      (TilingSpace.centresSequence (TilingSpace.translateSequence g T))
      (S.centres : Set Tiling.Plane))
    (hA : A = {s ∈ (S.centres : Set Tiling.Plane) |
      ∀ᶠ n : ℕ in atTop, s - (g n : Tiling.Plane) ∈
        (T.centres : Set Tiling.Plane)})
    (_hanchorA : anchor ∈ A)
    (_hInvariant : ∀ x : ℝ, (x : ℂ) +ᵥ regularSupport K A =
      regularSupport K A)
    (hPcolumn : IsVerticalColumn P) (hPanchor : coordinateSwap anchor ∈ P.centres)
    (hPsub : P.centres ⊆ coordinateSwap '' A) :
    P.centres = coordinateSwap ''
        ((S.centres : Set Tiling.Plane) ∩ {z | z.im = anchor.im}) ∧
      (S.centres : Set Tiling.Plane) ∩ {z | z.im = anchor.im} ⊆ A := by
  have hSwapTile : TilesOn K.coordinateSwap
      (coordinateSwap '' (S.centres : Set Tiling.Plane)) Set.univ := by
    simpa using (Tiling.AxisParallel.tilesOn_coordinateSwap S.tilesOn)
  obtain ⟨axis, haxis⟩ := (isVerticalColumn_iff P).mp hPcolumn
  have haxisAnchor : axis = anchor.im := by
    have := haxis hPanchor
    simpa [coordinateSwap] using this.symm
  have hPaxis : P.centres ⊆ {z : Tiling.Plane | z.re = anchor.im} := by
    intro z hz
    have hz' := haxis hz
    simpa [haxisAnchor] using hz'
  have hPslab := VerticalPlate.support_isVerticalSlab hSwapTile P
  have hPbase := verticalColumn_regularSupport hSwapTile P hPcolumn hPaxis
  have hAinS : A ⊆ (S.centres : Set Tiling.Plane) := by
    rw [hA]
    exact inter_subset_left
  have hfirst : P.centres ⊆ coordinateSwap ''
      ((S.centres : Set Tiling.Plane) ∩ {z | z.im = anchor.im}) := by
    rintro z hz
    obtain ⟨a, ha, haz⟩ := hPsub hz
    have haS : a ∈ (S.centres : Set Tiling.Plane) := hAinS ha
    refine ⟨a, ⟨haS, ?_⟩, haz⟩
    have hzre := hPaxis hz
    have : (coordinateSwap a).re = anchor.im := haz ▸ hzre
    simpa [coordinateSwap] using this
  have hreverse : coordinateSwap ''
      ((S.centres : Set Tiling.Plane) ∩ {z | z.im = anchor.im}) ⊆ P.centres := by
    rintro q ⟨z, hzS, hzq⟩
    by_contra hqP
    have hqC : q ∈ coordinateSwap '' (S.centres : Set Tiling.Plane) :=
      ⟨z, hzS.1, hzq⟩
    have hqaxis : q.re = anchor.im := by
      have h := congrArg Complex.re hzq
      calc
        q.re = z.im := by simpa [coordinateSwap] using h.symm
        _ = anchor.im := hzS.2
    have hPsubC : P.centres ⊆ coordinateSwap ''
        (S.centres : Set Tiling.Plane) := by
      intro u hu
      obtain ⟨a, ha, hua⟩ := hPsub hu
      exact ⟨a, hAinS ha, hua⟩
    have hPpack : Tiling.IsPacking K.coordinateSwap.toPolygonalRegion.prototileFamily
        (K.coordinateSwap.toPolygonalRegion.placements P.centres) := by
      apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
        K.coordinateSwap P.centres).mpr
      intro u hu v hv huv
      exact (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
        K.coordinateSwap (coordinateSwap '' (S.centres : Set Tiling.Plane))).mp
        hSwapTile.2.1 (hPsubC hu) (hPsubC hv) huv
    have hraw : openUnion K.coordinateSwap P.centres =ᵐ[MeasureTheory.volume]
        P.support := Tiling.AxisParallel.openUnion_aeEq_regularSupport hPpack
    have hKopen : IsOpen K.coordinateSwap.openCarrier :=
      K.coordinateSwap.openCarrier_regularOpen.1
    have hprojopen : IsOpen (Complex.re '' K.coordinateSwap.openCarrier) :=
      Complex.isOpenMap_re _ hKopen
    have hsumEq :
        (Complex.re '' K.coordinateSwap.openCarrier) + {anchor.im} =
          anchor.im +ᵥ (Complex.re '' K.coordinateSwap.openCarrier) := by
      ext u
      constructor
      · rintro ⟨v, ⟨x, hx, rfl⟩, ha⟩
        rw [mem_vadd_set]
        refine ⟨x.re, ⟨x, hx, rfl⟩, ?_⟩
        simpa [vadd_eq_add, add_comm] using ha
      · rw [mem_vadd_set]
        rintro ⟨v, ⟨x, hx, rfl⟩, ha⟩
        refine ⟨x.re, ⟨x, hx, rfl⟩, anchor.im, Set.mem_singleton _, ?_⟩
        simpa [vadd_eq_add, add_comm] using ha
    have hsumopen : IsOpen
        ((Complex.re '' K.coordinateSwap.openCarrier) + {anchor.im}) := by
      rw [hsumEq]
      exact hprojopen.vadd _
    have hqSupport : q +ᵥ K.coordinateSwap.openCarrier ⊆ P.support := by
      rw [hPbase.2]
      intro y hy
      obtain ⟨k, hk, rfl⟩ := hy
      apply hPbase.1.symm ▸ hsumopen.subset_interior_closure
      refine ⟨k.re, ⟨k, hk, rfl⟩, anchor.im, Set.mem_singleton _, ?_⟩
      simp only [vadd_eq_add, Complex.add_re]
      rw [hqaxis]
      ring
    have hUopen : IsOpen (q +ᵥ K.coordinateSwap.openCarrier) :=
      hKopen.vadd q
    have hKnonempty : K.coordinateSwap.openCarrier.Nonempty :=
      K.coordinateSwap.isPolygonal.interior_nonempty K.coordinateSwap.nonempty
    have hUnonempty : (q +ᵥ K.coordinateSwap.openCarrier).Nonempty := by
      obtain ⟨k, hk⟩ := hKnonempty
      exact ⟨q +ᵥ k, ⟨k, hk, rfl⟩⟩
    have hUpos := hUopen.measure_pos MeasureTheory.volume hUnonempty
    let U : Set Tiling.Plane := q +ᵥ K.coordinateSwap.openCarrier
    let V : Set Tiling.Plane := openUnion K.coordinateSwap P.centres
    have hUae : U =ᵐ[MeasureTheory.volume] (U ∩ V : Set Tiling.Plane) := by
      filter_upwards [hraw] with y hy
      apply propext
      constructor
      · intro hyU
        exact ⟨hyU, (iff_of_eq hy).mpr (hqSupport hyU)⟩
      · exact fun hy' ↦ hy'.1
    have hUmeasure : MeasureTheory.volume (q +ᵥ K.coordinateSwap.openCarrier) =
        MeasureTheory.volume
          ((q +ᵥ K.coordinateSwap.openCarrier : Set Tiling.Plane) ∩
            openUnion K.coordinateSwap P.centres) :=
      MeasureTheory.measure_congr (by simpa [U, V] using hUae)
    have hIntpos : 0 < MeasureTheory.volume
        ((q +ᵥ K.coordinateSwap.openCarrier : Set Tiling.Plane) ∩
          openUnion K.coordinateSwap P.centres) := by
      rw [← hUmeasure]
      exact hUpos
    have hIntnonempty :
        ((q +ᵥ K.coordinateSwap.openCarrier : Set Tiling.Plane) ∩
          openUnion K.coordinateSwap P.centres).Nonempty := by
      apply Set.nonempty_iff_ne_empty.mpr
      intro hempty
      rw [hempty, MeasureTheory.measure_empty] at hIntpos
      exact (lt_irrefl _ hIntpos)
    obtain ⟨y, hyq, hyP⟩ := hIntnonempty
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hyP
    obtain ⟨r, hyr⟩ := hyP
    have hrP : (r : Tiling.Plane) ∈ P.centres := r.2
    have hrq : (r : Tiling.Plane) ≠ q := by
      intro heq
      exact hqP (heq ▸ hrP)
    have hopenQ : IsOpen (q +ᵥ K.coordinateSwap.openCarrier) := hKopen.vadd q
    have hopenR : IsOpen ((r : Tiling.Plane) +ᵥ K.coordinateSwap.openCarrier) :=
      hKopen.vadd (r : Tiling.Plane)
    have hpos := hopenQ.inter hopenR |>.measure_pos MeasureTheory.volume
      ⟨y, hyq, hyr⟩
    have hzero := hSwapTile.2.1
      (show ((r : Tiling.Plane), ()) ∈
        K.coordinateSwap.toPolygonalRegion.placements
          (coordinateSwap '' (S.centres : Set Tiling.Plane)) by
          change (r : Tiling.Plane) ∈ coordinateSwap '' (S.centres : Set Tiling.Plane)
          exact hPsubC r.2)
      (show (q, ()) ∈
        K.coordinateSwap.toPolygonalRegion.placements
          (coordinateSwap '' (S.centres : Set Tiling.Plane)) by
          change q ∈ coordinateSwap '' (S.centres : Set Tiling.Plane)
          exact hqC)
      (by simpa using hrq)
    have hmono :
        ((q +ᵥ K.coordinateSwap.openCarrier : Set Tiling.Plane) ∩
            ((r : Tiling.Plane) +ᵥ K.coordinateSwap.openCarrier : Set Tiling.Plane)) ⊆
          ((r : Tiling.Plane) +ᵥ K.coordinateSwap.support) ∩
            (q +ᵥ K.coordinateSwap.support) := by
      rintro w ⟨hwq, hwr⟩
      rw [Region.openCarrier,
        Tiling.RationalPolygonal.PolygonalRegion.openCarrier] at hwr hwq
      rw [← interior_vadd] at hwr hwq
      exact ⟨interior_subset hwr, interior_subset hwq⟩
    have hpos' : 0 < MeasureTheory.volume
        (((r : Tiling.Plane) +ᵥ K.coordinateSwap.support) ∩
          (q +ᵥ K.coordinateSwap.support)) :=
      hpos.trans_le (MeasureTheory.measure_mono hmono)
    exact (ne_of_gt hpos') hzero
  have hsecond :
      (S.centres : Set Tiling.Plane) ∩ {z | z.im = anchor.im} ⊆ A := by
    intro z hz
    have hzP : coordinateSwap z ∈ P.centres := hreverse ⟨z, hz, rfl⟩
    obtain ⟨a, ha, hza⟩ := hPsub hzP
    have : a = z := by
      apply coordinateSwap.injective
      exact hza
    simpa [this] using ha
  constructor
  · apply Set.Subset.antisymm hfirst
    exact hreverse
  · exact hsecond

private theorem eventually_mem_of_finite_relevant
    {A Q : Set Tiling.Plane} {C : ℕ → Set Tiling.Plane}
    (hfinite : (A ∩ Q).Finite)
    (hA : ∀ a ∈ A, ∀ᶠ n : ℕ in atTop, a ∈ C n) :
    ∀ᶠ n : ℕ in atTop, ∀ a ∈ A ∩ Q, a ∈ C n := by
  classical
  rw [← hfinite.coe_toFinset]
  simp only [Finset.mem_coe]
  exact (Filter.eventually_all_finset _).mpr fun a ha ↦
    hA a (hfinite.mem_toFinset.mp ha).1

private theorem fixedBackground_cancel_univ
    {K : Region} {U : ℕ → TilingSpace K Set.univ}
    {S : TilingSpace K Set.univ} {A B : Set Tiling.Plane}
    (hconv : LocallyFellConverges (TilingSpace.centresSequence U)
      (S.centres : Set Tiling.Plane))
    (hdisjoint : Disjoint A B) (hunion : A ∪ B = (S.centres : Set Tiling.Plane))
    (hA : ∀ a ∈ A, ∀ᶠ n : ℕ in atTop,
      a ∈ ((U n).centres : Set Tiling.Plane))
    (hB : ∀ b ∈ B, ∀ᶠ n : ℕ in atTop,
      b ∉ ((U n).centres : Set Tiling.Plane))
    {x : Tiling.Plane} (hx : x ∈ frontier (regularSupport K B)) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ᶠ n : ℕ in atTop,
      regularSupport K (((U n).centres : Set Tiling.Plane) \ A) ∩ Metric.ball x rho =
        regularSupport K B ∩ Metric.ball x rho := by
  simpa using (Tiling.AxisParallel.Continuous.fixedBackground_cancel
    (K := K) (X := (Set.univ : Set ℝ)) (T := U) (S := S)
    (A := A) (B := B) (by simp) isOpen_univ (by simp) hconv hdisjoint hunion hA hB hx)

private theorem persistentPatch_eventuallyPulledBack
    {K : Region} {U : ℕ → TilingSpace K Set.univ}
    {S : TilingSpace K Set.univ}
    (D : PersistentTransientSplit K Set.univ U S)
    {Q : Set Tiling.Plane} (hfinite : (D.persistent ∩ Q).Finite) :
    ∀ᶠ n : ℕ in atTop, ∀ a ∈ D.persistent ∩ Q,
      a ∈ ((U n).centres : Set Tiling.Plane) := by
  exact eventually_mem_of_finite_relevant hfinite D.persistent_eventuallyMem

private theorem shrinkingContact_hasLimitPoint
    {K : Region} {anchor movingLimit : Tiling.Plane}
    {moving : ℕ → Tiling.Plane}
    (hcontact : ∀ n, HorizontalProperContact K anchor (moving n))
    (hmoving : Tendsto moving atTop (nhds movingLimit)) :
    ∃ (x : Tiling.Plane) (phi : ℕ → ℕ) (a b : ℕ → Tiling.Plane),
      StrictMono phi ∧
      Tendsto (fun n ↦ AffineMap.lineMap (a (phi n)) (b (phi n)) (1 / 2 : ℝ))
        atTop (nhds x) ∧
      (∀ n, a (phi n) ≠ b (phi n)) ∧
      (∀ n, (a (phi n)).im = (b (phi n)).im) ∧
      (∀ n, openSegment ℝ (a (phi n)) (b (phi n)) ⊆
        (frontier (anchor +ᵥ K.support) ∩
          frontier ((moving (phi n)) +ᵥ K.support)) \
          ((anchor +ᵥ K.vertices) ∪
            ((moving (phi n)) +ᵥ K.vertices))) ∧
      (∀ n, AffineMap.lineMap (a (phi n)) (b (phi n)) (1 / 2 : ℝ) ∈
        frontier (anchor +ᵥ K.support) ∩
          frontier ((moving (phi n)) +ᵥ K.support)) ∧
      x ∈ closure (anchor +ᵥ K.support) ∧
      x ∈ closure (movingLimit +ᵥ K.support) := by
  classical
  choose a b hab him hseg using hcontact
  let xseq : ℕ → Tiling.Plane := fun n ↦
    AffineMap.lineMap (a n) (b n) (1 / 2 : ℝ)
  have hmid (n : ℕ) : xseq n ∈ openSegment ℝ (a n) (b n) := by
    dsimp [xseq]
    apply lineMap_mem_openSegment (𝕜 := ℝ) (a n) (b n)
    exact ⟨by norm_num, by norm_num⟩
  have hfront (n : ℕ) :
      xseq n ∈ frontier (anchor +ᵥ K.support) ∩
        frontier ((moving n) +ᵥ K.support) := (hseg n (hmid n)).1
  obtain ⟨R, hR⟩ := K.isPolygonal.isBounded.subset_closedBall (0 : Tiling.Plane)
  have hbounded : ∀ n, xseq n ∈ Metric.closedBall anchor R := by
    intro n
    have hclosure : xseq n ∈ closure (anchor +ᵥ K.support) :=
      frontier_subset_closure (hfront n).1
    apply closure_minimal ?_ Metric.isClosed_closedBall hclosure
    rintro z ⟨k, hk, rfl⟩
    rw [Metric.mem_closedBall, dist_comm]
    have hk' := hR hk
    rw [Metric.mem_closedBall, dist_zero_right] at hk'
    simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hk'
  obtain ⟨x, _hxball, phi, hphi, hxlim⟩ :=
    (isCompact_closedBall anchor R).tendsto_subseq hbounded
  have hanchorX : x ∈ closure (anchor +ᵥ K.support) := by
    apply isClosed_closure.mem_of_tendsto hxlim
    exact Filter.Eventually.of_forall fun n ↦
      frontier_subset_closure (hfront (phi n)).1
  have hmovingSub : Tendsto (moving ∘ phi) atTop (nhds movingLimit) :=
    hmoving.comp hphi.tendsto_atTop
  let yseq : ℕ → Tiling.Plane := fun n ↦ xseq (phi n) - moving (phi n)
  have hylimit : Tendsto yseq atTop (nhds (x - movingLimit)) := by
    dsimp [yseq]
    exact hxlim.sub hmovingSub
  have hysupport : ∀ n, yseq n ∈ closure K.support := by
    intro n
    have hcl := frontier_subset_closure (hfront (phi n)).2
    rw [closure_vadd] at hcl
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hcl
    simpa [yseq, sub_eq_add_neg, add_comm] using hcl
  have hyX : x - movingLimit ∈ closure K.support := by
    apply isClosed_closure.mem_of_tendsto hylimit
    exact Filter.Eventually.of_forall hysupport
  refine ⟨x, phi, a, b, hphi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [xseq, Function.comp_def] using hxlim
  · intro n
    exact hab (phi n)
  · intro n
    exact him (phi n)
  · intro n
    exact hseg (phi n)
  · intro n
    exact hfront (phi n)
  · exact hanchorX
  · rw [closure_vadd, mem_vadd_set]
    exact ⟨x - movingLimit, hyX, by
      change movingLimit + (x - movingLimit) = x
      abel⟩

private theorem placedSupport_subset_closure_regularSupport_local
    (K : Region) {A : Set Tiling.Plane} {s : Tiling.Plane} (hs : s ∈ A) :
    s +ᵥ K.support ⊆ closure (regularSupport K A) := by
  rw [K.isPolygonal.closure_interior.symm, ← closure_vadd s (interior K.support)]
  apply closure_mono
  intro z hz
  rw [regularSupport]
  have hopen : IsOpen (⋃ i : A, (i : Tiling.Plane) +ᵥ K.openCarrier) :=
    isOpen_iUnion (fun i : A ↦ isOpen_interior.vadd (i : Tiling.Plane))
  apply hopen.subset_interior_closure
  exact Set.mem_iUnion_of_mem ⟨s, hs⟩ hz

private theorem shrinkingContact_limit_frontier
    {K : Region} {U : ℕ → TilingSpace K Set.univ}
    {S : TilingSpace K Set.univ}
    (D : PersistentTransientSplit K Set.univ U S)
    {anchor movingLimit : Tiling.Plane} (moving : ℕ → Tiling.Plane)
    (hcontact : ∀ n, HorizontalProperContact K anchor (moving n))
    (hmoving : Tendsto moving atTop (nhds movingLimit))
    (hanchor : anchor ∈ D.persistent)
    (hmovingLimit : movingLimit ∈ D.transient)
    (_horient : D.orientation = Axis.vertical) :
    ∃ (x : Tiling.Plane) (phi : ℕ → ℕ) (a b : ℕ → Tiling.Plane),
      StrictMono phi ∧
      Tendsto (fun n ↦ AffineMap.lineMap (a (phi n)) (b (phi n)) (1 / 2 : ℝ))
        atTop (nhds x) ∧
      (∀ n, a (phi n) ≠ b (phi n)) ∧
      (∀ n, (a (phi n)).im = (b (phi n)).im) ∧
      (∀ n, openSegment ℝ (a (phi n)) (b (phi n)) ⊆
        (frontier (anchor +ᵥ K.support) ∩
          frontier ((moving (phi n)) +ᵥ K.support)) \
          ((anchor +ᵥ K.vertices) ∪
            ((moving (phi n)) +ᵥ K.vertices))) ∧
      (∀ n, AffineMap.lineMap (a (phi n)) (b (phi n)) (1 / 2 : ℝ) ∈
        frontier (anchor +ᵥ K.support) ∩
          frontier ((moving (phi n)) +ᵥ K.support)) ∧
      x ∈ frontier (regularSupport K D.transient) := by
  obtain ⟨x, phi, a, b, hphi, hxlim, hab, him, hseg, hfront,
      hxAnchorTile, hxMovingTile⟩ :=
    shrinkingContact_hasLimitPoint hcontact hmoving
  have hAnchorClosure :
      closure (anchor +ᵥ K.support) ⊆ closure (regularSupport K D.persistent) := by
    simpa using
      (closure_mono (placedSupport_subset_closure_regularSupport_local K hanchor))
  have hMovingClosure :
      closure (movingLimit +ᵥ K.support) ⊆ closure (regularSupport K D.transient) := by
    simpa using
      (closure_mono
        (placedSupport_subset_closure_regularSupport_local K hmovingLimit))
  have hxPersistent : x ∈ closure (regularSupport K D.persistent) :=
    hAnchorClosure hxAnchorTile
  have hxTransientClosure : x ∈ closure (regularSupport K D.transient) :=
    hMovingClosure hxMovingTile
  have hSupportDisjoint :
      Disjoint (regularSupport K D.persistent)
        (regularSupport K D.transient) := by
    let parts : Bool → Set Tiling.Plane := fun b ↦ if b then D.transient else D.persistent
    have hparts : Set.PairwiseDisjoint Set.univ parts := by
      intro i _ j _ hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · change Disjoint D.persistent D.transient
        exact D.disjoint
      · change Disjoint D.transient D.persistent
        exact D.disjoint.symm
      · exact (hij rfl).elim
    have hpartsUnion : (⋃ i, parts i) = (S.centres : Set Tiling.Plane) := by
      rw [show (⋃ i, parts i) = D.persistent ∪ D.transient by
        ext z
        simp [parts]]
      exact D.union_eq
    obtain ⟨hpair, _hcover⟩ :=
      regularSupport_pairwiseDisjoint parts hparts hpartsUnion S.tilesOn
    have h := hpair (Set.mem_univ false) (Set.mem_univ true) (by decide)
    change Disjoint (regularSupport K D.persistent)
      (regularSupport K D.transient) at h
    exact h
  have hxNotInterior : x ∉ interior (regularSupport K D.transient) := by
    intro hxInt
    have hfreq : ∃ᶠ y in 𝓝 x, y ∈ regularSupport K D.persistent :=
      (mem_closure_iff_frequently.mp hxPersistent)
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ regularSupport K D.transient :=
      mem_interior_iff_mem_nhds.mp hxInt
    obtain ⟨y, hyP, hyT⟩ := (hfreq.and_eventually hnear).exists
    exact Set.disjoint_left.mp hSupportDisjoint hyP hyT
  refine ⟨x, phi, a, b, hphi, hxlim, hab, him, hseg, hfront, ?_⟩
  exact ⟨hxTransientClosure, hxNotInterior⟩

private theorem horizontal_point_mem_openSegment_iff_local
    {a b : Tiling.Plane} (_hab : a ≠ b) (hh : a.im = b.im) (x : ℝ) :
    ((x : ℂ) + a.im * Complex.I) ∈ openSegment ℝ a b ↔
      x ∈ openSegment ℝ a.re b.re := by
  rw [openSegment_eq_image, openSegment_eq_image]
  constructor <;> rintro ⟨u, hu, h⟩
  · refine ⟨u, hu, ?_⟩
    simpa using congrArg Complex.re h
  · refine ⟨u, hu, ?_⟩
    apply Complex.ext
    · simpa using congrArg id h
    · simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
        Complex.smul_im, smul_eq_mul]
      rw [hh]
      ring

private theorem shrinkingHorizontalContacts_excludeVerticalSplit
    {K : Region} {U : ℕ → TilingSpace K Set.univ}
    {S : TilingSpace K Set.univ}
    (D : PersistentTransientSplit K Set.univ U S)
    {anchor movingLimit : Tiling.Plane} (moving : ℕ → Tiling.Plane) :
    LocallyFellConverges (TilingSpace.centresSequence U)
      (S.centres : Set Tiling.Plane) →
    anchor ∈ D.persistent → movingLimit ∈ D.transient →
    (∀ n, anchor ∈ ((U n).centres : Set Tiling.Plane)) →
    (∀ n, moving n ∈ ((U n).centres : Set Tiling.Plane)) →
    (∀ n, HorizontalProperContact K anchor (moving n)) →
    Tendsto moving atTop (nhds movingLimit) →
    D.orientation ≠ Axis.vertical := by
  intro hconv hanchor hmovingLimit hanchorU hmovingU hcontact hmoving horient
  have hPsupport : regularSupport K D.persistent =
      {z : Tiling.Plane | z.re ∈ D.persistentBase} :=
    D.persistentSupport_vertical horient
  obtain ⟨x, phi, a, b, hphi, hxlim, hab, him, hseg, hfront, hxfront⟩ :=
    shrinkingContact_limit_frontier D moving hcontact hmoving hanchor hmovingLimit horient
  obtain ⟨rho, hrho, hcancel⟩ := fixedBackground_cancel_univ hconv D.disjoint
    D.union_eq D.persistent_eventuallyMem D.transient_eventuallyNotMem hxfront
  have hBopen : IsOpen D.persistentBase := D.persistentBase_open
  have hBreg : interior (closure D.persistentBase) = D.persistentBase :=
    D.persistentBase_regular
  have hmidBase (n : ℕ) :
      (AffineMap.lineMap (a (phi n)) (b (phi n)) (1 / 2 : ℝ)).re ∈
        D.persistentBase := by
    let J : Set ℝ := openSegment ℝ (a (phi n)).re (b (phi n)).re
    have hJclosure : J ⊆ closure D.persistentBase := by
      intro u hu
      let z : Tiling.Plane := (u : ℂ) + (a (phi n)).im * Complex.I
      have hzseg : z ∈ openSegment ℝ (a (phi n)) (b (phi n)) := by
        exact (horizontal_point_mem_openSegment_iff_local (hab n)
          (him n) u).2 hu
      have hzfront := (hseg n hzseg).1.1
      have hzcl : z ∈ closure (regularSupport K D.persistent) :=
        (by
          simpa using
            (closure_mono (placedSupport_subset_closure_regularSupport_local K hanchor))
              (frontier_subset_closure hzfront))
      rw [hPsupport] at hzcl
      change z ∈ closure (Complex.re ⁻¹' D.persistentBase) at hzcl
      rw [Complex.closure_preimage_re] at hzcl
      change z.re ∈ closure D.persistentBase at hzcl
      simpa [z] using hzcl
    have hmidJ : (midpoint ℝ (a (phi n)).re (b (phi n)).re) ∈ J :=
      midpoint_mem_openSegment _ _
    have hJopen : IsOpen J := by
      dsimp [J]
      have hne : (a (phi n)).re ≠ (b (phi n)).re := by
        intro heq
        apply hab n
        apply Complex.ext heq (him n)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [openSegment_eq_Ioo hlt]
        exact isOpen_Ioo
      · rw [openSegment_symm, openSegment_eq_Ioo hgt]
        exact isOpen_Ioo
    have hmidB : midpoint ℝ (a (phi n)).re (b (phi n)).re ∈
        D.persistentBase := by
      rw [← hBreg]
      exact mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hJopen.mem_nhds hmidJ) hJclosure)
    have hre :
        (AffineMap.lineMap (a (phi n)) (b (phi n)) (1 / 2 : ℝ)).re =
          midpoint ℝ (a (phi n)).re (b (phi n)).re := by
      simp [AffineMap.lineMap_apply, midpoint]
    rw [hre]
    exact hmidB
  have hmidPersistent (n : ℕ) :
      AffineMap.lineMap (a (phi n)) (b (phi n)) (1 / 2 : ℝ) ∈
        regularSupport K D.persistent := by
    rw [hPsupport]
    exact hmidBase n
  obtain ⟨delta, hdelta, hsep⟩ := tilesOn_uniformlySeparated K
  have hSsep := hsep Set.univ (S.centres : Set Tiling.Plane) S.tilesOn
  have hmovingNotPersistent : ∀ᶠ n : ℕ in atTop, moving (phi n) ∉ D.persistent := by
    have hnear : ∀ᶠ n : ℕ in atTop,
        dist (moving (phi n)) movingLimit < delta := by
      have hball := (hmoving.comp hphi.tendsto_atTop).eventually
        (Metric.ball_mem_nhds movingLimit (by linarith))
      filter_upwards [hball] with n hn
      simpa [Metric.mem_ball, dist_comm] using hn
    filter_upwards [hnear] with n hn hbad
    have hmnS : moving (phi n) ∈ (S.centres : Set Tiling.Plane) := by
      exact D.persistent_subset hbad
    have hmlS : movingLimit ∈ (S.centres : Set Tiling.Plane) :=
      D.transient_subset hmovingLimit
    have hne : moving (phi n) ≠ movingLimit := by
      intro heq
      exact Set.disjoint_left.mp D.disjoint hbad (heq ▸ hmovingLimit)
    have hge := hSsep hmnS hmlS hne
    exact (not_lt_of_ge hge) hn
  have hsupportDisjoint :
      Disjoint (regularSupport K D.persistent)
        (regularSupport K D.transient) := by
    let parts : Bool → Set Tiling.Plane := fun q ↦
      if q then D.transient else D.persistent
    have hparts : Set.PairwiseDisjoint Set.univ parts := by
      intro i _ j _ hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · exact D.disjoint
      · exact D.disjoint.symm
      · exact (hij rfl).elim
    have hpartsUnion : (⋃ q, parts q) = (S.centres : Set Tiling.Plane) := by
      rw [show (⋃ q, parts q) = D.persistent ∪ D.transient by
        ext z
        simp [parts]]
      exact D.union_eq
    obtain ⟨hpair, _⟩ := regularSupport_pairwiseDisjoint parts hparts
      hpartsUnion S.tilesOn
    have h := hpair (Set.mem_univ false) (Set.mem_univ true) (by decide)
    change Disjoint (regularSupport K D.persistent)
      (regularSupport K D.transient) at h
    exact h
  have hmidBall : ∀ᶠ n : ℕ in atTop,
      AffineMap.lineMap (a (phi n)) (b (phi n)) (1 / 2 : ℝ) ∈
        Metric.ball x rho :=
    hxlim.eventually (Metric.ball_mem_nhds x hrho)
  have hcancelPhi : ∀ᶠ n : ℕ in atTop,
      regularSupport K (((U (phi n)).centres : Set Tiling.Plane) \ D.persistent) ∩
        Metric.ball x rho = regularSupport K D.transient ∩ Metric.ball x rho :=
    hcancel.filter_mono hphi.tendsto_atTop
  have hev := hcancelPhi.and (hmovingNotPersistent.and hmidBall)
  obtain ⟨n, hnCancel, hnNotPersistent, hnBall⟩ :=
    (Filter.Eventually.exists hev)
  let m : Tiling.Plane :=
    AffineMap.lineMap (a (phi n)) (b (phi n)) (1 / 2 : ℝ)
  have hmPersistent : m ∈ regularSupport K D.persistent := by
    simpa [m] using hmidPersistent n
  have hmMoveClosure : m ∈ closure ((moving (phi n)) +ᵥ K.openCarrier) := by
    have hmfront := (hfront n).2
    have hmsupp : m ∈ closure ((moving (phi n)) +ᵥ K.support) :=
      frontier_subset_closure hmfront
    rw [← K.isPolygonal.closure_interior, ← closure_vadd] at hmsupp
    rw [closure_closure] at hmsupp
    change m ∈ closure ((moving (phi n)) +ᵥ K.openCarrier) at hmsupp
    exact hmsupp
  have hPopen : IsOpen (regularSupport K D.persistent) :=
    (regularSupport_isRegularOpen K D.persistent).1
  have hmSmall : m ∈ regularSupport K D.persistent ∩ Metric.ball x rho :=
    ⟨hmPersistent, by simpa [m] using hnBall⟩
  obtain ⟨z, hzSmall, hzMove⟩ :=
    mem_closure_iff.1 hmMoveClosure _ (hPopen.inter Metric.isOpen_ball) hmSmall
  let Q : Set Tiling.Plane :=
    ((U (phi n)).centres : Set Tiling.Plane) \ D.persistent
  have hzResidual : z ∈ regularSupport K Q := by
    rw [regularSupport]
    have hopen : IsOpen (⋃ q : Q, (q : Tiling.Plane) +ᵥ K.openCarrier) :=
      isOpen_iUnion (fun q ↦ isOpen_interior.vadd (q : Tiling.Plane))
    apply hopen.subset_interior_closure
    let q : Q :=
      ⟨moving (phi n), hmovingU (phi n), hnNotPersistent⟩
    exact Set.mem_iUnion_of_mem q hzMove
  have hzTransient : z ∈ regularSupport K D.transient := by
    have hzEq : z ∈ regularSupport K Q ∩ Metric.ball x rho :=
      ⟨hzResidual, hzSmall.2⟩
    rw [hnCancel] at hzEq
    exact hzEq.1
  exact Set.disjoint_left.mp hsupportDisjoint hzSmall.1 hzTransient

/-- Unit-scale specialization of positive-similarity contact transport, shared by
the four translated contact sequences below. -/
private theorem horizontalProperContact_vadd_iff_local
    {K : Region} {u s t : Tiling.Plane} :
    HorizontalProperContact K s t ↔
      HorizontalProperContact K (u +ᵥ s) (u +ᵥ t) := by
  simpa only [positiveSimilarity, one_smul, vadd_eq_add, add_comm] using
    (Continuous.horizontalProperContact_positiveSimilarity_iff
      (K := K) (R := K) (s := 1) (r := 0) (c := u) (by norm_num)
      (by rw [positiveSimilarity_image_eq_vadd_smul]; simp) s t)

private theorem coupledPersistentSupports_horizontal
    {K : Region} {T : TilingSpace K Set.univ}
    {E : EscapingHorizontalContactData K (T.centres : Set Tiling.Plane)}
    (L : CoupledCrossAxisLimits K T E) :
    (∀ x : ℝ, (x : ℂ) +ᵥ regularSupport K L.persistent =
      regularSupport K L.persistent) ∧
    (∀ x : ℝ, (x : ℂ) +ᵥ regularSupport K L.persistent' =
      regularSupport K L.persistent') := by
  let U : ℕ → TilingSpace K Set.univ :=
    TilingSpace.translateSequence L.translations T
  let U' : ℕ → TilingSpace K Set.univ :=
    TilingSpace.translateSequence L.translations' T
  have hanchorU : ∀ n, L.anchor ∈ ((U n).centres : Set Tiling.Plane) := by
    intro n
    refine ⟨E.left (L.subsequence n), (E.left (L.subsequence n)).2, ?_⟩
    change (E.left (L.subsequence n)).1 + (L.translations n : Tiling.Plane) =
      L.anchor
    rw [L.translations_eq]
    abel
  have hmoveU : ∀ n,
      ((E.right (L.subsequence n)).1 + (L.translations n : Tiling.Plane)) ∈
        ((U n).centres : Set Tiling.Plane) := by
    intro n
    refine ⟨E.right (L.subsequence n), (E.right (L.subsequence n)).2, ?_⟩
    change (E.right (L.subsequence n)).1 + (L.translations n : Tiling.Plane) =
      (E.right (L.subsequence n)).1 + (L.translations n : Tiling.Plane)
    rfl
  have hmoveLimitU :
      L.movingLimit ∈ L.split.transient := by
    have hnotP : L.movingLimit ∉ L.split.persistent := by
      intro hp
      apply L.movingLimit_transient
      rw [L.persistent_eq_split]
      exact hp
    have hpart := L.split.union_eq ▸ L.movingLimit_mem
    rcases hpart with hp | ht
    · exact (hnotP hp).elim
    · exact ht
  have hmove : Tendsto
      (fun n ↦ (E.right (L.subsequence n)).1 +
        (L.translations n : Tiling.Plane)) atTop (nhds L.movingLimit) := by
    have hoff : Tendsto
        (fun n ↦ (E.right (L.subsequence n)).1 -
          (E.left (L.subsequence n)).1) atTop (nhds L.offsetLimit) :=
      L.offsets_converge
    have hadd : Tendsto
        (fun n ↦ L.anchor +
          ((E.right (L.subsequence n)).1 - (E.left (L.subsequence n)).1))
        atTop (nhds (L.anchor + L.offsetLimit)) :=
      tendsto_const_nhds.add hoff
    convert hadd using 1 <;>
      simp [L.translations_eq, L.movingLimit_eq, sub_eq_add_neg,
        add_assoc, add_comm]
  have hcontactU : ∀ n, HorizontalProperContact K L.anchor
      ((E.right (L.subsequence n)).1 + (L.translations n : Tiling.Plane)) := by
    intro n
    have hc := (horizontalProperContact_vadd_iff_local (K := K)
      (u := L.translations n) (s := (E.left (L.subsequence n)).1)
      (t := (E.right (L.subsequence n)).1)).mp
      (E.contact (L.subsequence n))
    have hleft : (L.translations n : Tiling.Plane) +
        (E.left (L.subsequence n)).1 = L.anchor := by
      rw [L.translations_eq]
      abel
    rw [← hleft]
    simpa [vadd_eq_add, add_comm] using hc
  have hnotVertical : L.split.orientation ≠ Axis.vertical := by
    exact shrinkingHorizontalContacts_excludeVerticalSplit L.split
      (fun n ↦ (E.right (L.subsequence n)).1 + (L.translations n : Tiling.Plane))
      L.converges (by rw [← L.persistent_eq_split]; exact L.anchor_persistent)
      hmoveLimitU hanchorU hmoveU hcontactU hmove
  have horient : L.split.orientation = Axis.horizontal := by
    cases h : L.split.orientation with
    | vertical => exact (hnotVertical h).elim
    | horizontal => rfl
  have hanchorU' : ∀ n, L.anchor' ∈ ((U' n).centres : Set Tiling.Plane) := by
    intro n
    refine ⟨E.right (L.subsequence n), (E.right (L.subsequence n)).2, ?_⟩
    change (E.right (L.subsequence n)).1 + (L.translations' n : Tiling.Plane) =
      L.anchor'
    rw [L.translations'_eq]
    abel
  have hmoveU' : ∀ n,
      ((E.left (L.subsequence n)).1 + (L.translations' n : Tiling.Plane)) ∈
        ((U' n).centres : Set Tiling.Plane) := by
    intro n
    refine ⟨E.left (L.subsequence n), (E.left (L.subsequence n)).2, ?_⟩
    rfl
  have hmoveLimitU' : L.movingLimit' ∈ L.split'.transient := by
    have hnotP : L.movingLimit' ∉ L.split'.persistent := by
      intro hp
      apply L.movingLimit'_transient
      rw [L.persistent'_eq_split]
      exact hp
    have hpart := L.split'.union_eq ▸ L.movingLimit'_mem
    rcases hpart with hp | ht
    · exact (hnotP hp).elim
    · exact ht
  have hmove' : Tendsto
      (fun n ↦ (E.left (L.subsequence n)).1 +
        (L.translations' n : Tiling.Plane)) atTop (nhds L.movingLimit') := by
    have hoff : Tendsto
        (fun n ↦ (E.right (L.subsequence n)).1 -
          (E.left (L.subsequence n)).1) atTop (nhds L.offsetLimit) :=
      L.offsets_converge
    have hneg : Tendsto
        (fun n ↦ -((E.right (L.subsequence n)).1 -
          (E.left (L.subsequence n)).1)) atTop (nhds (-L.offsetLimit)) :=
      by
        have hc := (continuous_neg.tendsto L.offsetLimit).comp hoff
        convert hc using 1
        funext n
        simp only [Function.comp_apply]
    have hadd : Tendsto
        (fun n ↦ L.anchor' -
          ((E.right (L.subsequence n)).1 - (E.left (L.subsequence n)).1))
        atTop (nhds (L.anchor' - L.offsetLimit)) := by
      have hc : Tendsto
          (fun n ↦ L.anchor' +
            (-((E.right (L.subsequence n)).1 -
              (E.left (L.subsequence n)).1)))
          atTop (nhds (L.anchor' + (-L.offsetLimit))) :=
        tendsto_const_nhds.add hneg
      simpa [sub_eq_add_neg] using hc
    convert hadd using 1 <;>
      simp [L.translations'_eq, L.movingLimit'_eq, sub_eq_add_neg,
        add_comm, add_left_comm]
  have hcontactU' : ∀ n, HorizontalProperContact K L.anchor'
      ((E.left (L.subsequence n)).1 + (L.translations' n : Tiling.Plane)) := by
    intro n
    have hc0 := (horizontalProperContact_vadd_iff_local (K := K)
      (u := L.translations' n) (s := (E.right (L.subsequence n)).1)
      (t := (E.left (L.subsequence n)).1)).mp
      ((horizontalProperContact_comm K
        (E.left (L.subsequence n)).1 (E.right (L.subsequence n)).1).mp
        (E.contact (L.subsequence n)))
    have hright : (L.translations' n : Tiling.Plane) +
        (E.right (L.subsequence n)).1 = L.anchor' := by
      rw [L.translations'_eq]
      abel
    rw [← hright]
    simpa [vadd_eq_add, add_comm] using hc0
  have hnotVertical' : L.split'.orientation ≠ Axis.vertical := by
    exact shrinkingHorizontalContacts_excludeVerticalSplit L.split'
      (fun n ↦ (E.left (L.subsequence n)).1 + (L.translations' n : Tiling.Plane))
      L.converges' (by rw [← L.persistent'_eq_split]; exact L.anchor'_persistent)
      hmoveLimitU' hanchorU' hmoveU' hcontactU' hmove'
  have horient' : L.split'.orientation = Axis.horizontal := by
    cases h : L.split'.orientation with
    | vertical => exact (hnotVertical' h).elim
    | horizontal => rfl
  constructor
  · intro x
    rw [L.persistent_eq_split, L.split.persistentSupport_horizontal horient]
    ext z
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  · intro x
    rw [L.persistent'_eq_split, L.split'.persistentSupport_horizontal horient']
    ext z
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]

private theorem one_isVerticalColumn_of_saturated_disjoint_local
    {K : Region} {T : Set Tiling.Plane}
    {A B : Set Tiling.Plane}
    (P Q : VerticalPlate K T)
    (hPsub : P.centres ⊆ A)
    (hQsub : Q.centres ⊆ B)
    (hAB : Disjoint A B)
    (hAtMostOne : ∀ R S : VerticalPlate K T,
      ¬ IsVerticalColumn R → ¬ IsVerticalColumn S → R = S) :
    IsVerticalColumn P ∨ IsVerticalColumn Q := by
  have hPQ : P ≠ Q := by
    intro h
    subst Q
    obtain ⟨p, hp⟩ := P.nonempty_supp
    exact Set.disjoint_left.mp hAB (hPsub ⟨p, hp, rfl⟩) (hQsub ⟨p, hp, rfl⟩)
  by_cases hP : IsVerticalColumn P
  · exact Or.inl hP
  by_cases hQ : IsVerticalColumn Q
  · exact Or.inr hQ
  exact False.elim (hPQ (hAtMostOne P Q hP hQ))

private theorem coupledHorizontalColumnSelection_core_local
    {K : Region} {T₀ T₁ A₀ A₁ : Set Tiling.Plane} (v : Tiling.Plane)
    (hT : v +ᵥ T₀ = T₁)
    (a₀ : T₀) (a₁ : T₁)
    (ha₀ : (a₀ : Tiling.Plane) ∈ A₀)
    (ha₁ : (a₁ : Tiling.Plane) ∈ A₁)
    (hSat₀ : ∀ P : VerticalPlate K T₀,
      (P.centres ∩ A₀).Nonempty → P.centres ⊆ A₀)
    (hSat₁ : ∀ P : VerticalPlate K T₁,
      (P.centres ∩ A₁).Nonempty → P.centres ⊆ A₁)
    (hDisj : Disjoint (v +ᵥ A₀) A₁)
    (hAtMostOne : ∀ P Q : VerticalPlate K T₁,
      ¬ IsVerticalColumn P → ¬ IsVerticalColumn Q → P = Q) :
    (∃ P : VerticalPlate K T₀,
      IsVerticalColumn P ∧ (a₀ : Tiling.Plane) ∈ P.centres ∧
        P.centres ⊆ A₀) ∨
    (∃ Q : VerticalPlate K T₁,
      IsVerticalColumn Q ∧ (a₁ : Tiling.Plane) ∈ Q.centres ∧
        Q.centres ⊆ A₁) := by
  have hcarrier : K.openCarrier = positiveSimilarity 1 0 '' K.openCarrier := by
    simpa only [one_smul, zero_vadd] using
      (positiveSimilarity_image_eq_vadd_smul
        (s := 1) (b := 0) (U := K.openCarrier)).symm
  have htarget : positiveSimilarity 1 v '' T₀ = T₁ := by
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul, hT]
  let P₀ : VerticalPlate K T₀ := VerticalPlate.ofCentre (K := K) a₀
  let Q₁ : VerticalPlate K T₁ := VerticalPlate.ofCentre (K := K) a₁
  have hP₀mem : (a₀ : Tiling.Plane) ∈ P₀.centres :=
    VerticalPlate.mem_centres_ofCentre a₀
  have hQ₁mem : (a₁ : Tiling.Plane) ∈ Q₁.centres :=
    VerticalPlate.mem_centres_ofCentre a₁
  have hP₀sub : P₀.centres ⊆ A₀ :=
    hSat₀ P₀ ⟨a₀, hP₀mem, ha₀⟩
  have hQ₁sub : Q₁.centres ⊆ A₁ :=
    hSat₁ Q₁ ⟨a₁, hQ₁mem, ha₁⟩
  let e : VerticalPlate K T₀ ≃
      VerticalPlate K (positiveSimilarity 1 v '' T₀) :=
    verticalPlate_positiveSimilarityEquiv (by norm_num) hcarrier v
  let P₁ : VerticalPlate K T₁ := htarget ▸ e P₀
  have hP₁centres : P₁.centres = v +ᵥ P₀.centres := by
    dsimp [P₁, e]
    cases htarget
    rw [verticalPlate_positiveSimilarityEquiv_centres_image]
    simpa only [one_smul] using
      (positiveSimilarity_image_eq_vadd_smul (s := 1) (b := v) (U := P₀.centres))
  have hP₁sub : P₁.centres ⊆ v +ᵥ A₀ := by
    rw [hP₁centres]
    intro z hz
    rcases Set.mem_vadd_set.mp hz with ⟨x, hx, hxz⟩
    rw [Set.mem_vadd_set]
    exact ⟨x, hP₀sub hx, hxz⟩
  have hP₁columniff : IsVerticalColumn P₁ ↔ IsVerticalColumn P₀ := by
    dsimp [P₁]
    cases htarget
    exact (verticalPlate_positiveSimilarityEquiv_isVerticalColumn
      (by norm_num) hcarrier v P₀).symm
  rcases one_isVerticalColumn_of_saturated_disjoint_local P₁ Q₁
      hP₁sub hQ₁sub hDisj hAtMostOne with hP₁column | hQ₁column
  · exact Or.inl ⟨P₀, hP₁columniff.mp hP₁column, hP₀mem, hP₀sub⟩
  · exact Or.inr ⟨Q₁, hQ₁column, hQ₁mem, hQ₁sub⟩

private theorem coupledPersistentOrientations
    {K : Region} {T : TilingSpace K Set.univ}
    {E : EscapingHorizontalContactData K (T.centres : Set Tiling.Plane)}
    (L : CoupledCrossAxisLimits K T E) :
    L.split.orientation = Axis.horizontal ∧
      L.split'.orientation = Axis.horizontal := by
  let U : ℕ → TilingSpace K Set.univ :=
    TilingSpace.translateSequence L.translations T
  let U' : ℕ → TilingSpace K Set.univ :=
    TilingSpace.translateSequence L.translations' T
  have hanchorU : ∀ n, L.anchor ∈ ((U n).centres : Set Tiling.Plane) := by
    intro n
    refine ⟨E.left (L.subsequence n), (E.left (L.subsequence n)).2, ?_⟩
    change (E.left (L.subsequence n)).1 + (L.translations n : Tiling.Plane) = L.anchor
    rw [L.translations_eq]
    abel
  have hmoveU : ∀ n,
      ((E.right (L.subsequence n)).1 + (L.translations n : Tiling.Plane)) ∈
        ((U n).centres : Set Tiling.Plane) := by
    intro n
    refine ⟨E.right (L.subsequence n), (E.right (L.subsequence n)).2, rfl⟩
  have hmoveLimitU : L.movingLimit ∈ L.split.transient := by
    have hnotP : L.movingLimit ∉ L.split.persistent := by
      intro hp
      apply L.movingLimit_transient
      rw [L.persistent_eq_split]
      exact hp
    have hpart := L.split.union_eq ▸ L.movingLimit_mem
    rcases hpart with hp | ht
    · exact (hnotP hp).elim
    · exact ht
  have hmove : Tendsto
      (fun n ↦ (E.right (L.subsequence n)).1 +
        (L.translations n : Tiling.Plane)) atTop (nhds L.movingLimit) := by
    have hoff := L.offsets_converge
    have hadd : Tendsto
        (fun n ↦ L.anchor +
          ((E.right (L.subsequence n)).1 - (E.left (L.subsequence n)).1))
        atTop (nhds (L.anchor + L.offsetLimit)) :=
      tendsto_const_nhds.add hoff
    convert hadd using 1 <;>
      simp [L.translations_eq, L.movingLimit_eq, sub_eq_add_neg,
        add_assoc, add_comm]
  have hcontactU : ∀ n, HorizontalProperContact K L.anchor
      ((E.right (L.subsequence n)).1 + (L.translations n : Tiling.Plane)) := by
    intro n
    have hc := (horizontalProperContact_vadd_iff_local (K := K)
      (u := L.translations n) (s := (E.left (L.subsequence n)).1)
      (t := (E.right (L.subsequence n)).1)).mp
      (E.contact (L.subsequence n))
    have hleft : (L.translations n : Tiling.Plane) +
        (E.left (L.subsequence n)).1 = L.anchor := by
      rw [L.translations_eq]
      abel
    rw [← hleft]
    simpa [vadd_eq_add, add_comm] using hc
  have hnotVertical : L.split.orientation ≠ Axis.vertical :=
    shrinkingHorizontalContacts_excludeVerticalSplit L.split
      (fun n ↦ (E.right (L.subsequence n)).1 + (L.translations n : Tiling.Plane))
      L.converges (by rw [← L.persistent_eq_split]; exact L.anchor_persistent)
      hmoveLimitU hanchorU hmoveU hcontactU hmove
  have horient : L.split.orientation = Axis.horizontal := by
    cases h : L.split.orientation with
    | vertical => exact (hnotVertical h).elim
    | horizontal => rfl
  have hanchorU' : ∀ n, L.anchor' ∈ ((U' n).centres : Set Tiling.Plane) := by
    intro n
    refine ⟨E.right (L.subsequence n), (E.right (L.subsequence n)).2, ?_⟩
    change (E.right (L.subsequence n)).1 + (L.translations' n : Tiling.Plane) = L.anchor'
    rw [L.translations'_eq]
    abel
  have hmoveU' : ∀ n,
      ((E.left (L.subsequence n)).1 + (L.translations' n : Tiling.Plane)) ∈
        ((U' n).centres : Set Tiling.Plane) := by
    intro n
    refine ⟨E.left (L.subsequence n), (E.left (L.subsequence n)).2, rfl⟩
  have hmoveLimitU' : L.movingLimit' ∈ L.split'.transient := by
    have hnotP : L.movingLimit' ∉ L.split'.persistent := by
      intro hp
      apply L.movingLimit'_transient
      rw [L.persistent'_eq_split]
      exact hp
    have hpart := L.split'.union_eq ▸ L.movingLimit'_mem
    rcases hpart with hp | ht
    · exact (hnotP hp).elim
    · exact ht
  have hmove' : Tendsto
      (fun n ↦ (E.left (L.subsequence n)).1 +
        (L.translations' n : Tiling.Plane)) atTop (nhds L.movingLimit') := by
    have hoff := L.offsets_converge
    have hneg : Tendsto
        (fun n ↦ -((E.right (L.subsequence n)).1 -
          (E.left (L.subsequence n)).1)) atTop (nhds (-L.offsetLimit)) :=
      (continuous_neg.tendsto L.offsetLimit).comp hoff
    have hadd : Tendsto
        (fun n ↦ L.anchor' -
          ((E.right (L.subsequence n)).1 - (E.left (L.subsequence n)).1))
        atTop (nhds (L.anchor' - L.offsetLimit)) := by
      have hc : Tendsto
          (fun n ↦ L.anchor' +
            (-((E.right (L.subsequence n)).1 -
              (E.left (L.subsequence n)).1))) atTop
          (nhds (L.anchor' + (-L.offsetLimit))) :=
        tendsto_const_nhds.add hneg
      simpa [sub_eq_add_neg] using hc
    convert hadd using 1 <;>
      simp [L.translations'_eq, L.movingLimit'_eq, sub_eq_add_neg,
        add_comm, add_left_comm]
  have hcontactU' : ∀ n, HorizontalProperContact K L.anchor'
      ((E.left (L.subsequence n)).1 + (L.translations' n : Tiling.Plane)) := by
    intro n
    have hc0 := (horizontalProperContact_vadd_iff_local (K := K)
      (u := L.translations' n) (s := (E.right (L.subsequence n)).1)
      (t := (E.left (L.subsequence n)).1)).mp
      ((horizontalProperContact_comm K
        (E.left (L.subsequence n)).1 (E.right (L.subsequence n)).1).mp
        (E.contact (L.subsequence n)))
    have hright : (L.translations' n : Tiling.Plane) +
        (E.right (L.subsequence n)).1 = L.anchor' := by
      rw [L.translations'_eq]
      abel
    rw [← hright]
    simpa [vadd_eq_add, add_comm] using hc0
  have hnotVertical' : L.split'.orientation ≠ Axis.vertical :=
    shrinkingHorizontalContacts_excludeVerticalSplit L.split'
      (fun n ↦ (E.left (L.subsequence n)).1 + (L.translations' n : Tiling.Plane))
      L.converges' (by rw [← L.persistent'_eq_split]; exact L.anchor'_persistent)
      hmoveLimitU' hanchorU' hmoveU' hcontactU' hmove'
  have horient' : L.split'.orientation = Axis.horizontal := by
    cases h : L.split'.orientation with
    | vertical => exact (hnotVertical' h).elim
    | horizontal => rfl
  exact ⟨horient, horient'⟩

private theorem coupledHorizontalColumnSelection
    {K : Region} {T : TilingSpace K Set.univ}
    {E : EscapingHorizontalContactData K (T.centres : Set Tiling.Plane)}
    (L : CoupledCrossAxisLimits K T E)
    (_hInfinite : ¬ HasFiniteHorizontalComplexity
      (coordinateSwap '' (L.limit.centres : Set Tiling.Plane)))
    (_hInfinite' : ¬ HasFiniteHorizontalComplexity
      (coordinateSwap '' (L.limit'.centres : Set Tiling.Plane))) :
    (∃ P : VerticalPlate K.coordinateSwap
        (coordinateSwap '' (L.limit.centres : Set Tiling.Plane)),
      IsVerticalColumn P ∧ coordinateSwap L.anchor ∈ P.centres ∧
        P.centres ⊆ coordinateSwap '' L.persistent) ∨
    (∃ P : VerticalPlate K.coordinateSwap
        (coordinateSwap '' (L.limit'.centres : Set Tiling.Plane)),
      IsVerticalColumn P ∧ coordinateSwap L.anchor' ∈ P.centres ∧
        P.centres ⊆ coordinateSwap '' L.persistent') := by
  obtain ⟨horient, horient'⟩ := coupledPersistentOrientations L
  let T₀ : Set Tiling.Plane := coordinateSwap '' (L.limit.centres : Set Tiling.Plane)
  let T₁ : Set Tiling.Plane := coordinateSwap '' (L.limit'.centres : Set Tiling.Plane)
  let A₀ : Set Tiling.Plane := coordinateSwap '' L.persistent
  let A₁ : Set Tiling.Plane := coordinateSwap '' L.persistent'
  let w := L.anchor' - L.movingLimit
  let v : Tiling.Plane := coordinateSwap w
  have hTranslate : w +ᵥ (L.limit.centres : Set Tiling.Plane) =
      (L.limit'.centres : Set Tiling.Plane) :=
    (coupledLimits_translationAndPersistentDisjoint L).1
  have hswapVadd (u : Tiling.Plane) (S : Set Tiling.Plane) :
      coordinateSwap '' (u +ᵥ S) = coordinateSwap u +ᵥ (coordinateSwap '' S) := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨coordinateSwap x, ⟨x, hx, rfl⟩,
        coordinateSwap.map_add u x⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨u +ᵥ x, ⟨x, hx, rfl⟩, coordinateSwap.map_add u x⟩
  have hswapTranslate : v +ᵥ T₀ = T₁ := by
    dsimp [v, T₀, T₁]
    calc
      coordinateSwap w +ᵥ (coordinateSwap '' (L.limit.centres : Set Tiling.Plane)) =
          coordinateSwap '' (w +ᵥ (L.limit.centres : Set Tiling.Plane)) :=
        (hswapVadd w (L.limit.centres : Set Tiling.Plane)).symm
      _ = coordinateSwap '' (L.limit'.centres : Set Tiling.Plane) := by rw [hTranslate]
  have hDisj : Disjoint (v +ᵥ A₀) A₁ := by
    have himage : v +ᵥ A₀ = coordinateSwap '' (w +ᵥ L.persistent) := by
      dsimp [v, A₀]
      exact (hswapVadd w L.persistent).symm
    rw [himage, show A₁ = coordinateSwap '' L.persistent' by rfl]
    rw [Set.disjoint_left]
    intro z hz0 hz1
    obtain ⟨x, hx, hxz⟩ := hz0
    obtain ⟨y, hy, hyz⟩ := hz1
    have hxy : x = y := coordinateSwap.injective (hxz.trans hyz.symm)
    exact Set.disjoint_left.mp
      (coupledLimits_translationAndPersistentDisjoint L).2 hx (hxy.symm ▸ hy)
  have ha₀ : (coordinateSwap L.anchor : Tiling.Plane) ∈ A₀ :=
    ⟨L.anchor, L.anchor_persistent, rfl⟩
  have ha₁ : (coordinateSwap L.anchor' : Tiling.Plane) ∈ A₁ :=
    ⟨L.anchor', L.anchor'_persistent, rfl⟩
  have hSat₀ : ∀ P : VerticalPlate K.coordinateSwap T₀,
      (P.centres ∩ A₀).Nonempty → P.centres ⊆ A₀ := by
    intro P hP
    have hP' : (P.centres ∩ coordinateSwap '' L.split.persistent).Nonempty := by
      simpa [A₀, L.persistent_eq_split] using hP
    have hres := L.split.horizontalPersistent_plateSaturated horient P hP'
    simpa only [A₀, ← L.persistent_eq_split] using hres
  have hSat₁ : ∀ P : VerticalPlate K.coordinateSwap T₁,
      (P.centres ∩ A₁).Nonempty → P.centres ⊆ A₁ := by
    intro P hP
    have hP' : (P.centres ∩ coordinateSwap '' L.split'.persistent).Nonempty := by
      simpa [A₁, L.persistent'_eq_split] using hP
    have hres := L.split'.horizontalPersistent_plateSaturated horient' P hP'
    simpa only [A₁, ← L.persistent'_eq_split] using hres
  have hanchorT₁ : coordinateSwap L.anchor' ∈ T₁ := by
    have hpSplit : L.anchor' ∈ L.split'.persistent := by
      rw [← L.persistent'_eq_split]
      exact L.anchor'_persistent
    have hp : L.anchor' ∈ (L.limit'.centres : Set Tiling.Plane) :=
      L.split'.persistent_subset hpSplit
    exact ⟨L.anchor', hp, rfl⟩
  have hmoveLimit'_transient : L.movingLimit' ∈ L.split'.transient := by
    have hnotP : L.movingLimit' ∉ L.split'.persistent := by
      intro hp
      apply L.movingLimit'_transient
      rw [L.persistent'_eq_split]
      exact hp
    have hpart := L.split'.union_eq ▸ L.movingLimit'_mem
    rcases hpart with hp | ht
    · exact (hnotP hp).elim
    · exact ht
  have hnontrivial₁ :
      ¬ ∃ R : VerticalPlate K.coordinateSwap T₁,
        ¬ IsVerticalColumn R ∧ R.centres = T₁ := by
    rintro ⟨R, hRnoncolumn, hRT⟩
    have hzT : coordinateSwap L.movingLimit' ∈ T₁ := by
      exact ⟨L.movingLimit', L.movingLimit'_mem, rfl⟩
    have hzR : coordinateSwap L.movingLimit' ∈ R.centres := hRT.symm ▸ hzT
    have hzA : coordinateSwap L.movingLimit' ∈ A₁ :=
      hSat₁ R ⟨coordinateSwap L.anchor', hRT.symm ▸ hanchorT₁,
        ⟨L.anchor', L.anchor'_persistent, rfl⟩⟩ hzR
    obtain ⟨z', hz'P, hzz'⟩ := hzA
    have hEq : z' = L.movingLimit' := by
      exact coordinateSwap.injective hzz'
    have hp : L.movingLimit' ∈ L.split'.persistent := by
      rw [← L.persistent'_eq_split]
      exact hEq ▸ hz'P
    exact Set.disjoint_left.mp L.split'.disjoint hp hmoveLimit'_transient
  have hTilesSwap : TilesOn K.coordinateSwap T₁ Set.univ := by
    simpa [T₁] using Tiling.AxisParallel.tilesOn_coordinateSwap L.limit'.tilesOn
  have hAtMostOne' := atMostOneNoncolumn_of_not_finiteHorizontalComplexity
    hTilesSwap hnontrivial₁ _hInfinite'
  have hanchorT₀ : coordinateSwap L.anchor ∈ T₀ := by
    have hpSplit : L.anchor ∈ L.split.persistent := by
      rw [← L.persistent_eq_split]
      exact L.anchor_persistent
    have hp : L.anchor ∈ (L.limit.centres : Set Tiling.Plane) :=
      L.split.persistent_subset hpSplit
    exact ⟨L.anchor, hp, rfl⟩
  exact coupledHorizontalColumnSelection_core_local v hswapTranslate
    ⟨coordinateSwap L.anchor, hanchorT₀⟩ ⟨coordinateSwap L.anchor', hanchorT₁⟩ ha₀ ha₁
    hSat₀ hSat₁ hDisj hAtMostOne'

private theorem swappedDecomposition_nontrivial_of_horizontalSplit
    {K : Region} {U : ℕ → TilingSpace K Set.univ}
    {S : TilingSpace K Set.univ}
    (D : PersistentTransientSplit K Set.univ U S)
    {anchor moving : Tiling.Plane}
    (horient : D.orientation = Axis.horizontal)
    (hanchor : anchor ∈ D.persistent)
    (hmoving : moving ∈ D.transient) :
    ¬ ∃ P : VerticalPlate K.coordinateSwap
        (coordinateSwap '' (S.centres : Set Tiling.Plane)),
      ¬ IsVerticalColumn P ∧
        P.centres = coordinateSwap '' (S.centres : Set Tiling.Plane) := by
  rintro ⟨P, _hPnoncolumn, hPwhole⟩
  have hanchorS : anchor ∈ (S.centres : Set Tiling.Plane) :=
    D.persistent_subset hanchor
  have hanchorP : coordinateSwap anchor ∈ P.centres := by
    rw [hPwhole]
    exact ⟨anchor, hanchorS, rfl⟩
  have hPpersistent : P.centres ⊆ coordinateSwap '' D.persistent := by
    apply D.horizontalPersistent_plateSaturated horient P
    exact ⟨coordinateSwap anchor, hanchorP, ⟨anchor, hanchor, rfl⟩⟩
  have hmovingS : moving ∈ (S.centres : Set Tiling.Plane) :=
    D.transient_subset hmoving
  have hmovingP : coordinateSwap moving ∈ P.centres := by
    rw [hPwhole]
    exact ⟨moving, hmovingS, rfl⟩
  obtain ⟨z, hzPersistent, hswap⟩ := hPpersistent hmovingP
  have hz : z = moving := coordinateSwap.injective hswap
  exact Set.disjoint_left.mp D.disjoint (hz ▸ hzPersistent) hmoving

theorem exists_crossAxisOrbitLimit
    {K : Region} (T : TilingSpace K Set.univ)
    (hNontrivial :
      ¬ ∃ P : VerticalPlate K (T.centres : Set Tiling.Plane),
        ¬ IsVerticalColumn P ∧ P.centres = (T.centres : Set Tiling.Plane))
    (hInfinite : ¬ HasFiniteHorizontalComplexity
      (T.centres : Set Tiling.Plane)) :
    ∃ S : TilingSpace K Set.univ, S ∈ orbitHull T ∧
      (¬ ∃ P : VerticalPlate K.coordinateSwap
          (coordinateSwap '' (S.centres : Set Tiling.Plane)),
        ¬ IsVerticalColumn P ∧
          P.centres = coordinateSwap '' (S.centres : Set Tiling.Plane)) ∧
      Nonempty (CrossAxisLimitAlternative K T S) := by
  obtain ⟨E⟩ := escapingHorizontalContacts_exists T.tilesOn hNontrivial hInfinite
  obtain ⟨L⟩ := coupledCrossAxisLimits_exists T E
  obtain ⟨horient, horient'⟩ := coupledPersistentOrientations L
  have hanchor : L.anchor ∈ L.split.persistent := by
    rw [← L.persistent_eq_split]
    exact L.anchor_persistent
  have hanchor' : L.anchor' ∈ L.split'.persistent := by
    rw [← L.persistent'_eq_split]
    exact L.anchor'_persistent
  have hmoving : L.movingLimit ∈ L.split.transient := by
    have hnot : L.movingLimit ∉ L.split.persistent := by
      intro h
      exact L.movingLimit_transient (L.persistent_eq_split ▸ h)
    rcases L.split.union_eq ▸ L.movingLimit_mem with hp | ht
    · exact (hnot hp).elim
    · exact ht
  have hmoving' : L.movingLimit' ∈ L.split'.transient := by
    have hnot : L.movingLimit' ∉ L.split'.persistent := by
      intro h
      exact L.movingLimit'_transient (L.persistent'_eq_split ▸ h)
    rcases L.split'.union_eq ▸ L.movingLimit'_mem with hp | ht
    · exact (hnot hp).elim
    · exact ht
  have hnontrivial := swappedDecomposition_nontrivial_of_horizontalSplit
    L.split horient hanchor hmoving
  have hnontrivial' := swappedDecomposition_nontrivial_of_horizontalSplit
    L.split' horient' hanchor' hmoving'
  by_cases hfinite : HasFiniteHorizontalComplexity
      (coordinateSwap '' (L.limit.centres : Set Tiling.Plane))
  · exact ⟨L.limit, L.limit_mem_hull, hnontrivial,
      ⟨CrossAxisLimitAlternative.finiteVerticalComplexity hfinite⟩⟩
  by_cases hfinite' : HasFiniteHorizontalComplexity
      (coordinateSwap '' (L.limit'.centres : Set Tiling.Plane))
  · exact ⟨L.limit', L.limit'_mem_hull, hnontrivial',
      ⟨CrossAxisLimitAlternative.finiteVerticalComplexity hfinite'⟩⟩
  obtain hcolumn | hcolumn := coupledHorizontalColumnSelection L hfinite hfinite'
  · obtain ⟨P, hPcolumn, hPanchor, hPsub⟩ := hcolumn
    let fibre : Set Tiling.Plane :=
      (L.limit.centres : Set Tiling.Plane) ∩ {z | z.im = L.anchor.im}
    have hcomplete := persistentHorizontalPlate_isCompleteFibre
      (T := T) (S := L.limit) (g := L.translations)
      (A := L.persistent) (anchor := L.anchor) P
      L.converges L.persistent_eq L.anchor_persistent
      (coupledPersistentSupports_horizontal L).1 hPcolumn hPanchor hPsub
    have hanchorT : L.anchor ∈ (T.centres : Set Tiling.Plane) := by
      rw [L.anchor_eq]
      exact (E.left 0).property
    have hanchorF : L.anchor ∈ fibre := by
      constructor
      · exact L.split.persistent_subset hanchor
      · rfl
    have hpull : ∀ s ∈ fibre, ∀ᶠ n : ℕ in atTop,
        s - (L.translations n : Tiling.Plane) ∈
          (T.centres : Set Tiling.Plane) := by
      intro s hs
      have hmem : s ∈ L.persistent := hcomplete.2 hs
      rw [L.persistent_eq] at hmem
      exact hmem.2
    exact ⟨L.limit, L.limit_mem_hull, hnontrivial,
      ⟨CrossAxisLimitAlternative.persistentHorizontalColumn
        L.anchor hanchorT
        (fun n ↦ (E.left (L.subsequence n)).1)
        (fun n ↦ (E.left (L.subsequence n)).property)
        L.translations L.translations_eq L.converges fibre rfl
        hanchorF P hPcolumn hcomplete.1 hpull⟩⟩
  · obtain ⟨P, hPcolumn, hPanchor, hPsub⟩ := hcolumn
    let fibre : Set Tiling.Plane :=
      (L.limit'.centres : Set Tiling.Plane) ∩ {z | z.im = L.anchor'.im}
    have hcomplete := persistentHorizontalPlate_isCompleteFibre
      (T := T) (S := L.limit') (g := L.translations')
      (A := L.persistent') (anchor := L.anchor') P
      L.converges' L.persistent'_eq L.anchor'_persistent
      (coupledPersistentSupports_horizontal L).2 hPcolumn hPanchor hPsub
    have hanchorT : L.anchor' ∈ (T.centres : Set Tiling.Plane) := by
      rw [L.anchor'_eq]
      exact (E.right 0).property
    have hanchorF : L.anchor' ∈ fibre := by
      constructor
      · exact L.split'.persistent_subset hanchor'
      · rfl
    have hpull : ∀ s ∈ fibre, ∀ᶠ n : ℕ in atTop,
        s - (L.translations' n : Tiling.Plane) ∈
          (T.centres : Set Tiling.Plane) := by
      intro s hs
      have hmem : s ∈ L.persistent' := hcomplete.2 hs
      rw [L.persistent'_eq] at hmem
      exact hmem.2
    exact ⟨L.limit', L.limit'_mem_hull, hnontrivial',
      ⟨CrossAxisLimitAlternative.persistentHorizontalColumn
        L.anchor' hanchorT
        (fun n ↦ (E.right (L.subsequence n)).1)
        (fun n ↦ (E.right (L.subsequence n)).property)
        L.translations' L.translations'_eq L.converges' fibre rfl
        hanchorF P hPcolumn hcomplete.1 hpull⟩⟩


end Tiling.AxisParallel.Structure
