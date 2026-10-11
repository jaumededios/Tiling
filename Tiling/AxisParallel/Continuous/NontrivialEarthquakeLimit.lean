import Tiling.AxisParallel.Continuous.WeakTilingTopology
import Tiling.AxisParallel.Continuous.LocalizingNonFLC
import Tiling.AxisParallel.Continuous.PersistentTransientSlabs

/-!
# Nontrivial earthquake limit assembly

This module constructs a localized orbit limit with a fixed centre and an eventually absent
limiting centre, packages it into a nonempty persistent/transient split, and rounds its displayed
translations to any prescribed full-rank lattice in the carrier period group.
-/

open Set
open scoped Pointwise Topology
noncomputable section
namespace Tiling.AxisParallel.Continuous

/-- A localized orbit limit equipped with a nonempty persistent/transient earthquake split and
the exact fixed and moving witnesses that certify both colours are nonempty. -/
structure NontrivialEarthquakeLimitData
    (K : Tiling.AxisParallel.Region) (X : Set ℝ)
    (T : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}) where
  translations : ℕ → Tiling.AxisParallel.aePeriodGroup {z : Tiling.Plane | z.re ∈ X}
  limit : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}
  limit_mem_hull : limit ∈ Tiling.AxisParallel.Topology.orbitHull T
  converges : Tiling.AxisParallel.Topology.LocallyFellConverges
    (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
      (Tiling.AxisParallel.Topology.TilingSpace.translateSequence translations T))
    (limit.centres : Set Tiling.Plane)
  split : PersistentTransientSplit K X
    (Tiling.AxisParallel.Topology.TilingSpace.translateSequence translations T) limit
  persistent_nonempty : split.persistent.Nonempty
  transient_nonempty : split.transient.Nonempty
  fixedPoint : Tiling.Plane
  movingLimitPoint : Tiling.Plane
  movingCentres : ℕ → Tiling.Plane
  fixedPoint_mem_persistent : fixedPoint ∈ split.persistent
  movingLimitPoint_mem_transient : movingLimitPoint ∈ split.transient
  fixedPoint_ne_movingLimitPoint : fixedPoint ≠ movingLimitPoint
  fixedPoint_exact : ∀ n : ℕ, fixedPoint ∈
    ((Tiling.AxisParallel.Topology.TilingSpace.translate
      (translations n) T).centres : Set Tiling.Plane)
  movingCentres_mem : ∀ n : ℕ, movingCentres n ∈
    ((Tiling.AxisParallel.Topology.TilingSpace.translate
      (translations n) T).centres : Set Tiling.Plane)
  movingCentres_injective : Function.Injective movingCentres
  movingCentres_tendsto : Filter.Tendsto movingCentres Filter.atTop (nhds movingLimitPoint)
  movingCentres_ne_limit : ∀ n : ℕ, movingCentres n ≠ movingLimitPoint
  movingLimitPoint_eventuallyAbsent : ∀ᶠ n : ℕ in Filter.atTop, movingLimitPoint ∉
    ((Tiling.AxisParallel.Topology.TilingSpace.translate
      (translations n) T).centres : Set Tiling.Plane)

/-- The frontier of a tiled vertical cylinder is the cylinder over its base frontier, and that
base frontier is locally finite. -/
theorem localizedLimit_carrierBoundary
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (_hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    (T : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}) :
    frontier {z : Tiling.Plane | z.re ∈ X} = {z : Tiling.Plane | z.re ∈ frontier X} ∧
    ∀ C : Set ℝ, IsCompact C → (C ∩ frontier X).Finite := by
  exact ⟨Tiling.AxisParallel.frontier_verticalCylinder,
    T.tilesOn.verticalCylinder_frontier_locallyFinite hXopen hXregular⟩

/-- Package raw localized fixed/moving-centre data into a nontrivial persistent/transient split
after passing to the exact-membership subsequence supplied by C08. -/
private theorem nontrivialEarthquakeLimitData_of_localizedSequence
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    (T : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    (g : ℕ → Tiling.AxisParallel.aePeriodGroup {z : Tiling.Plane | z.re ∈ X})
    (S : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    (a z : Tiling.Plane) (zseq : ℕ → Tiling.Plane)
    (hHull : S ∈ Tiling.AxisParallel.Topology.orbitHull T)
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
        (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T))
      (S.centres : Set Tiling.Plane))
    (haExact : ∀ n, a ∈
      ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
        Set Tiling.Plane))
    (haS : a ∈ (S.centres : Set Tiling.Plane))
    (hzS : z ∈ (S.centres : Set Tiling.Plane)) (haz : a ≠ z)
    (hzmem : ∀ n, zseq n ∈
      ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
        Set Tiling.Plane))
    (hzinj : Function.Injective zseq)
    (hzlim : Filter.Tendsto zseq Filter.atTop (nhds z))
    (hzneq : ∀ n, zseq n ≠ z)
    (hzabs : ∀ᶠ n : ℕ in Filter.atTop, z ∉
      ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
        Set Tiling.Plane)) :
    Nonempty (NontrivialEarthquakeLimitData K X T) := by
  let U := Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T
  have hfront := T.tilesOn.verticalCylinder_frontier_locallyFinite hXopen hXregular
  obtain ⟨phi, D, hphi⟩ := exists_persistentTransientSplit
    hXnonempty hXopen hXregular hfront U S hconv
  have haP : a ∈ D.persistent := by
    have haUnion : a ∈ D.persistent ∪ D.transient := D.union_eq.symm ▸ haS
    rcases haUnion with ha | ha
    · exact ha
    · have he := D.transient_eventuallyNotMem a ha
      have : ∀ᶠ n : ℕ in Filter.atTop, False := he.mono fun n hn => hn (haExact (phi n))
      obtain ⟨n, hn⟩ := this.exists
      exact hn.elim
  have hzT : z ∈ D.transient := by
    have hzUnion : z ∈ D.persistent ∪ D.transient := D.union_eq.symm ▸ hzS
    rcases hzUnion with hz | hz
    · have he := D.persistent_eventuallyMem z hz
      have ha := hzabs.filter_mono hphi.tendsto_atTop
      have : ∀ᶠ n : ℕ in Filter.atTop, False := he.and ha |>.mono fun n hn => hn.2 hn.1
      obtain ⟨n, hn⟩ := this.exists
      exact hn.elim
    · exact hz
  refine ⟨{
    translations := g ∘ phi
    limit := S
    limit_mem_hull := hHull
    converges := ?_
    split := D
    persistent_nonempty := ⟨a, haP⟩
    transient_nonempty := ⟨z, hzT⟩
    fixedPoint := a
    movingLimitPoint := z
    movingCentres := zseq ∘ phi
    fixedPoint_mem_persistent := haP
    movingLimitPoint_mem_transient := hzT
    fixedPoint_ne_movingLimitPoint := haz
    fixedPoint_exact := fun n => haExact (phi n)
    movingCentres_mem := fun n => hzmem (phi n)
    movingCentres_injective := hzinj.comp hphi.injective
    movingCentres_tendsto := hzlim.comp hphi.tendsto_atTop
    movingCentres_ne_limit := fun n => hzneq (phi n)
    movingLimitPoint_eventuallyAbsent := hzabs.filter_mono hphi.tendsto_atTop }⟩
  apply ((locallyFell_metrizable K {z : Tiling.Plane | z.re ∈ X}).2 _ S).mp
  change Filter.Tendsto (U ∘ phi) Filter.atTop (nhds S)
  exact (((locallyFell_metrizable K {z : Tiling.Plane | z.re ∈ X}).2 U S).mpr hconv).comp
    hphi.tendsto_atTop

/-- Plane-case localization: translate one endpoint of every varying displacement to a fixed
anchor, then take a compact Fell subsequence. -/
private theorem exists_planeLocalizedNonFLCOrbitLimit
    {K : Tiling.AxisParallel.Region}
    (T : Tiling.AxisParallel.Topology.TilingSpace K Set.univ)
    (hTnonFLC : ¬ Tiling.AxisParallel.HasFLC
      (T.centres : Set Tiling.Plane)) :
    ∃ (g : ℕ → Tiling.AxisParallel.aePeriodGroup (Set.univ : Set Tiling.Plane))
      (S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ)
      (a z : Tiling.Plane) (zseq : ℕ → Tiling.Plane),
      S ∈ Tiling.AxisParallel.Topology.orbitHull T ∧
      Tiling.AxisParallel.Topology.LocallyFellConverges
        (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
          (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T))
        (S.centres : Set Tiling.Plane) ∧
      (∀ n : ℕ, a ∈
        ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
          Set Tiling.Plane)) ∧
      a ∈ (S.centres : Set Tiling.Plane) ∧
      z ∈ (S.centres : Set Tiling.Plane) ∧ z ≠ a ∧
      (∀ n : ℕ, zseq n ∈
        ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
          Set Tiling.Plane)) ∧
      Function.Injective zseq ∧ Filter.Tendsto zseq Filter.atTop (nhds z) ∧
      (∀ n : ℕ, zseq n ≠ z) ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        z ∉ ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
          Set Tiling.Plane) := by
  classical
  obtain ⟨delta, hdelta, hsep⟩ := tilesOn_uniformlySeparated K
  have hloc : ∀ Q : Set Tiling.Plane, Bornology.IsBounded Q →
      ((T.centres : Set Tiling.Plane) ∩ Q).Finite :=
    (Tiling.AxisParallel.IsPacking.locallyFinite_centres T.tilesOn.2.1).1
  obtain ⟨R, t, s, r, hR, hmem, hdist, hinj, hlim, hrne, hneq⟩ :=
    exists_varyingDisplacement_of_not_hasFLC hdelta
      (hsep _ _ T.tilesOn) hloc hTnonFLC
  let a : Tiling.Plane := 0
  let g₀ : ℕ → Tiling.AxisParallel.aePeriodGroup (Set.univ : Set Tiling.Plane) :=
    fun n ↦ ⟨a - t n, by
      simp [Tiling.AxisParallel.aePeriodGroup, Tiling.Polygonal.aePeriodGroup]⟩
  let U : ℕ → Set Tiling.Plane := fun n ↦
    ((Tiling.AxisParallel.Topology.TilingSpace.translate (g₀ n) T).centres :
      Set Tiling.Plane)
  have hUTiles (n : ℕ) : Tiling.AxisParallel.TilesOn K (U n) Set.univ :=
    (Tiling.AxisParallel.Topology.TilingSpace.translate (g₀ n) T).tilesOn
  have haU (n : ℕ) : a ∈ U n := by
    refine ⟨t n, (hmem n).1, ?_⟩
    change t n + (a - t n) = a
    abel
  obtain ⟨phi, L, hphi, hLTiles, hLclosed, hconv, haLraw⟩ :=
    exists_tilesOn_locallyFellSubsequence U hUTiles
  let S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ :=
    ⟨⟨L, hLclosed⟩, hLTiles⟩
  let g : ℕ → Tiling.AxisParallel.aePeriodGroup (Set.univ : Set Tiling.Plane) := g₀ ∘ phi
  let zseq : ℕ → Tiling.Plane := fun n ↦ a + (s (phi n) - t (phi n))
  let z : Tiling.Plane := a + r
  have haTranslated (n : ℕ) : a ∈
      ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
        Set Tiling.Plane) := haU (phi n)
  have hzseqTranslated (n : ℕ) : zseq n ∈
      ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
        Set Tiling.Plane) := by
    refine ⟨s (phi n), (hmem (phi n)).2, ?_⟩
    change s (phi n) + (a - t (phi n)) = a + (s (phi n) - t (phi n))
    abel
  have hconv' : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
        (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T))
      (S.centres : Set Tiling.Plane) := by
    change Tiling.AxisParallel.Topology.LocallyFellConverges
      (fun n ↦ ((Tiling.AxisParallel.Topology.TilingSpace.translate (g₀ (phi n)) T).centres :
        Set Tiling.Plane)) L
    exact hconv
  have haS : a ∈ (S.centres : Set Tiling.Plane) := by
    exact haLraw a haTranslated
  have hzlim : Filter.Tendsto zseq Filter.atTop (nhds z) := by
    exact tendsto_const_nhds.add (hlim.comp hphi.tendsto_atTop)
  have hzS : z ∈ (S.centres : Set Tiling.Plane) := by
    exact mem_of_locallyFellConverges_of_tendsto_mem hconv' hzseqTranslated hzlim
  have hzinj : Function.Injective zseq := by
    intro m n hmn
    apply hphi.injective
    apply hinj
    change a + (s (phi m) - t (phi m)) = a + (s (phi n) - t (phi n)) at hmn
    exact add_left_cancel hmn
  have hzneqa : z ≠ a := by
    intro hza
    apply hrne
    change a + r = a at hza
    exact add_left_cancel (hza.trans (add_zero a).symm)
  have hzneq (n : ℕ) : zseq n ≠ z := by
    intro hn
    apply hneq (phi n)
    change a + (s (phi n) - t (phi n)) = a + r at hn
    exact add_left_cancel hn
  have habsent : ∀ᶠ n : ℕ in Filter.atTop,
      z ∉ ((Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).centres :
        Set Tiling.Plane) :=
    eventually_absent_of_uniformlySeparated hdelta
      (fun n ↦ hsep _ _ (Tiling.AxisParallel.Topology.TilingSpace.translate (g n) T).tilesOn)
      zseq z hzseqTranslated hzlim hzneq
  have htendstoS : Filter.Tendsto
      (Tiling.AxisParallel.Topology.TilingSpace.translateSequence g T)
      Filter.atTop (nhds S) :=
    ((locallyFell_metrizable K Set.univ).2 _ S).mpr hconv'
  have hShull : S ∈ Tiling.AxisParallel.Topology.orbitHull T := by
    apply mem_closure_of_tendsto htendstoS
    exact Filter.Eventually.of_forall fun n ↦ by
      exact AddAction.mem_orbit _ (g n)
  exact ⟨g, S, a, z, zseq, hShull, hconv', haTranslated, haS, hzS, hzneqa,
    hzseqTranslated, hzinj, hzlim, hzneq, habsent⟩

/-- Round the displayed translations to a lattice while retaining the exact constant-residual
transport of an existing nontrivial split. -/
private theorem latticeAssembly_of_nontrivialEarthquakeLimitData
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    {T : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    (D : NontrivialEarthquakeLimitData K X T)
    (hXopen : IsOpen X) (hXregular : interior (closure X) = X)
    (Lambda : Tiling.AxisParallel.PlanarLattice)
    (hLambda : Lambda.toAddSubgroup ≤
      Tiling.AxisParallel.aePeriodGroup {z : Tiling.Plane | z.re ∈ X}) :
    ∃ (lambda : ℕ → Tiling.AxisParallel.aePeriodGroup
        {z : Tiling.Plane | z.re ∈ X})
      (gamma : Tiling.AxisParallel.aePeriodGroup
        {z : Tiling.Plane | z.re ∈ X})
      (D' : PersistentTransientSplit K X
        (Tiling.AxisParallel.Topology.TilingSpace.translateSequence
          (D.translations + Function.const ℕ gamma) T)
        (Tiling.AxisParallel.Topology.TilingSpace.translate gamma D.limit)),
      (∀ n : ℕ, (lambda n : Tiling.Plane) ∈ Lambda.toAddSubgroup) ∧
      Tiling.AxisParallel.Topology.TilingSpace.translate gamma D.limit ∈
        Tiling.AxisParallel.Topology.orbitHull T ∧
      Tiling.AxisParallel.Topology.LocallyFellConverges
        (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
          (Tiling.AxisParallel.Topology.TilingSpace.translateSequence lambda T))
        ((Tiling.AxisParallel.Topology.TilingSpace.translate gamma D.limit).centres :
          Set Tiling.Plane) ∧
      D'.persistent.Nonempty ∧ D'.transient.Nonempty := by
  let E : Set Tiling.Plane := {z : Tiling.Plane | z.re ∈ X}
  have hEopen : IsOpen E := hXopen.preimage Complex.continuous_re
  have hEregular : interior (closure E) = E := by
    change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hXregular]
  obtain ⟨_phi, lambda, gamma, _hphi, hlambda, _hresidual, hconv⟩ :=
    roundTranslationsToLattice_regularOpen hEopen hEregular Lambda hLambda
      D.translations T D.limit D.converges
  have hseq : (fun n ↦ Tiling.AxisParallel.Topology.TilingSpace.translate gamma
      (Tiling.AxisParallel.Topology.TilingSpace.translate (D.translations n) T)) =
      Tiling.AxisParallel.Topology.TilingSpace.translateSequence
        (D.translations + Function.const ℕ gamma) T := by
    funext n
    change gamma +ᵥ (D.translations n +ᵥ T) = (D.translations n + gamma) +ᵥ T
    rw [← add_vadd]
    congr 1
    exact add_comm _ _
  let D0 := D.split.translate gamma
  let D' : PersistentTransientSplit K X
      (Tiling.AxisParallel.Topology.TilingSpace.translateSequence
        (D.translations + Function.const ℕ gamma) T)
      (Tiling.AxisParallel.Topology.TilingSpace.translate gamma D.limit) := {
    persistent := D0.persistent
    transient := D0.transient
    persistent_subset := D0.persistent_subset
    transient_subset := D0.transient_subset
    disjoint := D0.disjoint
    union_eq := D0.union_eq
    persistent_eventuallyMem := by
      intro a ha
      filter_upwards [D0.persistent_eventuallyMem a ha] with n hn
      rw [← congrFun hseq n]
      exact hn
    transient_eventuallyNotMem := by
      intro b hb
      filter_upwards [D0.transient_eventuallyNotMem b hb] with n hn
      rw [← congrFun hseq n]
      exact hn
    orientation := D0.orientation
    persistentBase := D0.persistentBase
    transientBase := D0.transientBase
    persistentBase_open := D0.persistentBase_open
    transientBase_open := D0.transientBase_open
    persistentBase_regular := D0.persistentBase_regular
    transientBase_regular := D0.transientBase_regular
    persistentSupport_vertical := D0.persistentSupport_vertical
    transientSupport_vertical := D0.transientSupport_vertical
    persistentSupport_horizontal := D0.persistentSupport_horizontal
    transientSupport_horizontal := D0.transientSupport_horizontal
    horizontal_requires_plane := D0.horizontal_requires_plane
    verticalPersistent_plateSaturated := D0.verticalPersistent_plateSaturated
    verticalTransient_plateSaturated := D0.verticalTransient_plateSaturated
    horizontalPersistent_plateSaturated := D0.horizontalPersistent_plateSaturated
    horizontalTransient_plateSaturated := D0.horizontalTransient_plateSaturated }
  refine ⟨lambda, gamma, D', hlambda, ?_, hconv, ?_, ?_⟩
  · rw [← (orbitHull_compact T).2.2 gamma]
    exact ⟨D.limit, D.limit_mem_hull, rfl⟩
  · rcases D.persistent_nonempty with ⟨p, hp⟩
    have hp' : ((D.split.translate gamma).persistent).Nonempty :=
      ⟨(gamma : Tiling.Plane) + p, ⟨p, hp, rfl⟩⟩
    exact hp'
  · rcases D.transient_nonempty with ⟨p, hp⟩
    have hp' : ((D.split.translate gamma).transient).Nonempty :=
      ⟨(gamma : Tiling.Plane) + p, ⟨p, hp, rfl⟩⟩
    exact hp'

/-- Every non-FLC tiling of a nonempty regular periodic vertical carrier has an orbit limit with a
nontrivial persistent/transient earthquake split. -/
theorem exists_nontrivialEarthquakeOrbitLimit
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    {beta0 : ℝ} (hbeta0 : 0 < beta0)
    (hXperiod : ∀ x : ℝ, x + beta0 ∈ X ↔ x ∈ X)
    (T : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    (hTnonFLC : ¬ Tiling.AxisParallel.HasFLC
      (T.centres : Set Tiling.Plane)) :
    Nonempty (NontrivialEarthquakeLimitData K X T) := by
  by_cases hXplane : X = Set.univ
  · subst X
    obtain ⟨g, S, a, z, zseq, hHull, hconv, haExact, haS, hzS, hza,
        hzmem, hzinj, hzlim, hzneq, hzabs⟩ :=
      exists_planeLocalizedNonFLCOrbitLimit T hTnonFLC
    exact nontrivialEarthquakeLimitData_of_localizedSequence
      Set.univ_nonempty hXopen hXregular T g S a z zseq hHull hconv haExact
      haS hzS hza.symm hzmem hzinj hzlim hzneq hzabs
  · obtain ⟨g, S, a, z, zseq, hHull, hconv, haExact, haS, hzS, hza,
        hzmem, hzinj, hzlim, hzneq, hzabs⟩ :=
      exists_localizedNonFLCOrbitLimit hXnonempty hXopen hXregular hXplane
        hbeta0 hXperiod T hTnonFLC
    exact nontrivialEarthquakeLimitData_of_localizedSequence
      hXnonempty hXopen hXregular T g S a z zseq hHull hconv haExact
      haS hzS hza.symm hzmem hzinj hzlim hzneq hzabs

/-- The nontrivial earthquake limit can be displayed using translations in any prescribed
full-rank lattice contained in the carrier period group. -/
theorem exists_nontrivialEarthquakeOrbitLimit_latticeTranslations
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    {beta0 : ℝ} (hbeta0 : 0 < beta0)
    (hXperiod : ∀ x : ℝ, x + beta0 ∈ X ↔ x ∈ X)
    (T : Tiling.AxisParallel.Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X})
    (hTnonFLC : ¬ Tiling.AxisParallel.HasFLC
      (T.centres : Set Tiling.Plane))
    (Lambda : Tiling.AxisParallel.PlanarLattice)
    (hLambda : Lambda.toAddSubgroup ≤
      Tiling.AxisParallel.aePeriodGroup {z : Tiling.Plane | z.re ∈ X}) :
    ∃ (D : NontrivialEarthquakeLimitData K X T)
      (lambda : ℕ → Tiling.AxisParallel.aePeriodGroup
        {z : Tiling.Plane | z.re ∈ X})
      (gamma : Tiling.AxisParallel.aePeriodGroup
        {z : Tiling.Plane | z.re ∈ X})
      (D' : PersistentTransientSplit K X
        (Tiling.AxisParallel.Topology.TilingSpace.translateSequence
          (D.translations + Function.const ℕ gamma) T)
        (Tiling.AxisParallel.Topology.TilingSpace.translate gamma D.limit)),
      (∀ n : ℕ, (lambda n : Tiling.Plane) ∈ Lambda.toAddSubgroup) ∧
      Tiling.AxisParallel.Topology.TilingSpace.translate gamma D.limit ∈
        Tiling.AxisParallel.Topology.orbitHull T ∧
      Tiling.AxisParallel.Topology.LocallyFellConverges
        (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
          (Tiling.AxisParallel.Topology.TilingSpace.translateSequence lambda T))
        ((Tiling.AxisParallel.Topology.TilingSpace.translate gamma D.limit).centres :
          Set Tiling.Plane) ∧
      D'.persistent.Nonempty ∧ D'.transient.Nonempty := by
  obtain ⟨D⟩ := exists_nontrivialEarthquakeOrbitLimit
    hXnonempty hXopen hXregular hbeta0 hXperiod T hTnonFLC
  obtain ⟨lambda, gamma, D', hlambda, hHull, hconv, hp, ht⟩ :=
    latticeAssembly_of_nontrivialEarthquakeLimitData
      D hXopen hXregular Lambda hLambda
  exact ⟨D, lambda, gamma, D', hlambda, hHull, hconv, hp, ht⟩


end Tiling.AxisParallel.Continuous
