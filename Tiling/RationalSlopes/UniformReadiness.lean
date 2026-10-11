import Tiling.RationalSlopes.NonFLC
import Tiling.RationalSlopes.NonReadyRigidity
import Tiling.RationalSlopes.DirectionalRaster
import Tiling.RationalSlopes.EarthquakePeriodicity
import Tiling.RationalSlopes.Approximation.LinkTransport
import Tiling.RationalSlopes.Approximation.FLCTransport
import Tiling.Topology.TilingHull

set_option autoImplicit false
set_option linter.style.header false
open Function Filter MeasureTheory Set
open scoped Pointwise Topology
noncomputable section
open Tiling
open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Polygonal
open Tiling.Polygonal.Topology
open Tiling.RationalSlopes

namespace Tiling.RationalSlopes

/- Hole-free scratch bodies; PROVISIONAL imported predecessor closures.
   The four public signatures below are frozen. See the owner receipt. -/

private theorem eventually_ne_of_injective (f : ℕ → Plane)
    (hf : Injective f) (d : Plane) : ∀ᶠ n in atTop, f n ≠ d := by
  classical
  by_cases h : ∃ n, f n = d
  · obtain ⟨m, hm⟩ := h
    filter_upwards [eventually_gt_atTop m] with n hn
    intro heq
    exact (ne_of_gt hn) (hf (heq.trans hm.symm))
  · exact Filter.Eventually.of_forall (fun n hn => h ⟨n, hn⟩)

private theorem properContactDisplacements_subset_supportDifferences
    (K : PolygonalRegion) (η : Submodule ℝ Plane) (T : Set Plane) :
    properContactDisplacements K η T ⊆ K.support - K.support := by
  rintro d ⟨s, _, t, _, _, rfl, a, b, _, _, hsegment⟩
  have hmid := hsegment (midpoint_mem_openSegment (𝕜 := ℝ) a b)
  have hsclosed : IsClosed (s +ᵥ K.support) := by
    exact (Homeomorph.addLeft s).isClosed_image.mpr K.isPolygonal.isCompact.isClosed
  have htclosed : IsClosed (t +ᵥ K.support) := by
    exact (Homeomorph.addLeft t).isClosed_image.mpr K.isPolygonal.isCompact.isClosed
  obtain ⟨x, hx, hsx⟩ := Set.mem_vadd_set.mp (hsclosed.frontier_subset hmid.1)
  obtain ⟨y, hy, hty⟩ := Set.mem_vadd_set.mp (htclosed.frontier_subset hmid.2)
  refine Set.mem_sub.mpr ⟨y, hy, x, hx, ?_⟩
  change s + x = midpoint ℝ a b at hsx
  change t + y = midpoint ℝ a b at hty
  have heq : s + x = t + y := hsx.trans hty.symm
  calc
    y - x = (t + y) - (t + x) := by abel
    _ = s - t := by rw [← heq]; abel

/-- The non-ready contact alphabet supplies distinct bounded displacements
and hence a convergent paired-contact sequence before either limit is chosen. -/
private theorem infiniteContacts_pairedConvergentSequence
    (K : PolygonalRegion) (η : Submodule ℝ Plane) (T : Set Plane)
    (hinfinite : ¬(properContactDisplacements K η T).Finite) :
    ∃ (tn sn : ℕ → Plane) (d : Plane),
      (∀ n, tn n ∈ T ∧ sn n ∈ T ∧ tn n ≠ sn n ∧
        ProperEdgeContactAlong K η (sn n) (tn n)) ∧
      Injective (fun n => sn n - tn n) ∧
      Tendsto (fun n => sn n - tn n) atTop (𝓝 d) := by
  classical
  let e : ℕ ↪ properContactDisplacements K η T :=
    Set.Infinite.natEmbedding _ hinfinite
  choose sn hs tn ht hne heq hcontact using fun n => (e n).property
  have hmem : ∀ n, sn n - tn n ∈ K.support - K.support := by
    intro n
    apply properContactDisplacements_subset_supportDifferences K η T
    rw [← heq n]
    exact (e n).property
  have hinj : Injective (fun n => sn n - tn n) := by
    intro n m hnm
    apply e.injective
    apply Subtype.ext
    simpa only [heq] using hnm
  have hcompact : IsCompact ((fun p : Plane × Plane => p.1 - p.2) ''
      (K.support ×ˢ K.support)) :=
    (K.isPolygonal.isCompact.prod K.isPolygonal.isCompact).image
      (continuous_fst.sub continuous_snd)
  have hmem' : ∀ n, sn n - tn n ∈
      (fun p : Plane × Plane => p.1 - p.2) '' (K.support ×ˢ K.support) := by
    intro n
    obtain ⟨x, hx, y, hy, heq⟩ := Set.mem_sub.mp (hmem n)
    exact ⟨(x, y), ⟨hx, hy⟩, heq⟩
  obtain ⟨d, _, ι, hι, hlim⟩ := hcompact.tendsto_subseq hmem'
  exact ⟨tn ∘ ι, sn ∘ ι, d,
    fun n => ⟨ht _, hs _, (hne _).symm, hcontact _⟩, hinj.comp hι.injective, hlim⟩

/-- Packing separation rules out a centre persistent in both aligned limits.
The displacement limit itself is never assumed to be an attained displacement. -/
private theorem paired_persistentParts_disjoint
    (T A B : Set Plane) (t s d : Plane) (tn sn : ℕ → Plane)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hsep : T.Pairwise (fun x y => ρ ≤ dist x y))
    (hinj : Injective (fun n => sn n - tn n))
    (hlim : Tendsto (fun n => sn n - tn n) atTop (𝓝 d))
    (hA : ∀ x ∈ A, ∀ᶠ n in atTop, x - (t - tn n) ∈ T)
    (hB : ∀ y ∈ B, ∀ᶠ n in atTop, y - (s - sn n) ∈ T) :
    Disjoint A (-(s - t - d) +ᵥ B) := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  obtain ⟨y, hyB, hxy⟩ := Set.mem_vadd_set.mp hxB
  have hy : y = x + (s - t - d) := by
    change -(s - t - d) + y = x at hxy
    rw [← hxy]
    abel
  have hsmall : ∀ᶠ n in atTop, ‖sn n - tn n - d‖ < ρ := by
    have hc : Tendsto (fun n => ‖sn n - tn n - d‖) atTop (𝓝 (0 : ℝ)) := by
      simpa using (hlim.sub_const d).norm
    exact hc.eventually (gt_mem_nhds hρ)
  have hne := eventually_ne_of_injective (fun n => sn n - tn n) hinj d
  obtain ⟨n, hnA, hnB, hnsmall, hnne⟩ :=
    ((hA x hxA).and ((hB y hyB).and (hsmall.and hne))).exists
  have hdifference : (y - (s - sn n)) - (x - (t - tn n)) = sn n - tn n - d := by
    rw [hy]
    abel
  have hdistinct : y - (s - sn n) ≠ x - (t - tn n) := by
    intro heq
    have hz : sn n - tn n - d = 0 := by
      rw [← hdifference, heq, sub_self]
    exact hnne (sub_eq_zero.mp hz)
  have hdist : dist (y - (s - sn n)) (x - (t - tn n)) = ‖sn n - tn n - d‖ := by
    rw [dist_eq_norm, hdifference]
  have hlarge := hsep hnB hnA hdistinct
  change ρ ≤ dist (y - (s - sn n)) (x - (t - tn n)) at hlarge
  rw [hdist] at hlarge
  exact (not_lt_of_ge hlarge) hnsmall

private theorem locallyFell_limit_unique {A : ℕ → Set Plane} {S U : Set Plane}
    (hS : Tiling.Topology.LocallyFellConverges A S)
    (hU : Tiling.Topology.LocallyFellConverges A U) : S = U := by
  obtain ⟨hAn, hclosedS, hlimS⟩ := hS
  obtain ⟨_, hclosedU, hlimU⟩ := hU
  have hlimU' : Tendsto (fun n => Tiling.Topology.fellCompactification (A n) (hAn n))
      atTop (𝓝 (Tiling.Topology.fellCompactification U hclosedU)) := hlimU
  have heq := tendsto_nhds_unique hlimS hlimU'
  ext x
  have hmem := congrArg
    (fun C : TopologicalSpace.NonemptyCompacts (OnePoint Plane) =>
      (x : OnePoint Plane) ∈ (C : Set (OnePoint Plane))) heq
  simpa [Tiling.Topology.fellCompactification] using iff_of_eq hmem

private theorem locallyFell_subsequence {A : ℕ → Set Plane} {S : Set Plane}
    (hconv : Tiling.Topology.LocallyFellConverges A S)
    (ι : ℕ → ℕ) (hι : StrictMono ι) :
    Tiling.Topology.LocallyFellConverges (A ∘ ι) S := by
  obtain ⟨hA, hS, hlim⟩ := hconv
  exact ⟨fun n => hA (ι n), hS, hlim.comp hι.tendsto_atTop⟩

private theorem translatedTiling_subsequenceExists
    (K : PolygonalRegion) (T : Set Plane) (g : ℕ → Plane)
    (hT : TilesOn K T Set.univ) :
    ∃ (ι : ℕ → ℕ) (S : Set Plane), StrictMono ι ∧
      Tiling.Topology.LocallyFellConverges (fun n => g (ι n) +ᵥ T) S := by
  have htiles : ∀ n, TilesOn K (g n +ᵥ T) Set.univ := by
    intro n
    simpa using tilesOn_translate hT (g n)
  obtain ⟨ρ, hρ, hsep⟩ := exists_packingSeparation K
  obtain ⟨ι, S, hι, _, _, hconv⟩ :=
    Tiling.Topology.exists_locallyFellConvergent_subsequence ρ hρ (fun n => g n +ᵥ T)
      (fun n => (packing_centres_locallyFinite (htiles n).2.1).2.2)
      (fun n => hsep _ (htiles n).2.1)
  exact ⟨ι, S, hι, hconv⟩

/-- Both full limits and both Boolean stabilizations are extracted on one
common subsequence. A later stabilization never replaces one of the limits. -/
private theorem pairedLimits_commonStabilizedSubsequence
    (K : PolygonalRegion) (T : Set Plane) (g h : ℕ → Plane)
    (hT : TilesOn K T Set.univ) :
    ∃ (ι : ℕ → ℕ) (S U : Set Plane), StrictMono ι ∧
      Tiling.Topology.LocallyFellConverges (fun n => g (ι n) +ᵥ T) S ∧
      Tiling.Topology.LocallyFellConverges (fun n => h (ι n) +ᵥ T) U ∧
      (∀ u ∈ S, (∀ᶠ n in atTop, u ∈ g (ι n) +ᵥ T) ∨
        (∀ᶠ n in atTop, u ∉ g (ι n) +ᵥ T)) ∧
      (∀ u ∈ U, (∀ᶠ n in atTop, u ∈ h (ι n) +ᵥ T) ∨
        (∀ᶠ n in atTop, u ∉ h (ι n) +ᵥ T)) := by
  obtain ⟨ι₀, S, hι₀, hS₀⟩ := translatedTiling_subsequenceExists K T g hT
  obtain ⟨ι₁, U, hι₁, hU₁⟩ := translatedTiling_subsequenceExists K T (h ∘ ι₀) hT
  have hS₁ := locallyFell_subsequence hS₀ ι₁ hι₁
  have hS : TilesOn K S Set.univ := by
    apply tilesOn_isClosed (fun n => ?_) hS₁
    simpa using tilesOn_translate hT (g (ι₀ (ι₁ n)))
  have hU : TilesOn K U Set.univ := by
    apply tilesOn_isClosed (fun n => ?_) hU₁
    simpa using tilesOn_translate hT (h (ι₀ (ι₁ n)))
  obtain ⟨ι₂, hι₂, hstabS⟩ := diagonal_stabilizesCentres
    (fun n => g (ι₀ (ι₁ n)) +ᵥ T) S hS.1
  obtain ⟨ι₃, hι₃, hstabU⟩ := diagonal_stabilizesCentres
    (fun n => h (ι₀ (ι₁ (ι₂ n))) +ᵥ T) U hU.1
  refine ⟨ι₀ ∘ ι₁ ∘ ι₂ ∘ ι₃, S, U,
    hι₀.comp (hι₁.comp (hι₂.comp hι₃)),
    locallyFell_subsequence (locallyFell_subsequence hS₁ ι₂ hι₂) ι₃ hι₃,
    locallyFell_subsequence (locallyFell_subsequence hU₁ ι₂ hι₂) ι₃ hι₃, ?_, hstabU⟩
  intro u hu
  obtain hmem | hnot := hstabS u hu
  · exact Or.inl (hι₃.tendsto_atTop.eventually hmem)
  · exact Or.inr (hι₃.tendsto_atTop.eventually hnot)

/-- The two full limits are related by equality, not just subfamily inclusion. -/
private theorem paired_limits_translate_eq {T S U : Set Plane}
    (g h : ℕ → Plane) (k : Plane)
    (hfirst : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S)
    (hsecond : Tiling.Topology.LocallyFellConverges (fun n => h n +ᵥ T) U)
    (hdiff : Tendsto (fun n => h n - g n) atTop (𝓝 k)) : U = k +ᵥ S := by
  have htranslated := Tiling.Topology.locallyFell_translate hfirst hdiff
  have hseq : (fun n => (h n - g n) +ᵥ (g n +ᵥ T)) = (fun n => h n +ᵥ T) := by
    funext n
    rw [vadd_vadd, sub_add_cancel]
  rw [hseq] at htranslated
  exact locallyFell_limit_unique hsecond htranslated

/-- In the plane, two distinct invariant directions force any two nonempty
invariant sets to meet. Thus disjoint stabilized carriers have equal directions. -/
private theorem disjoint_invariantCarriers_sameDirection
    (A B : Set Plane) (δ η : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) (hη : Module.finrank ℝ η = 1)
    (hA : A.Nonempty) (hB : B.Nonempty) (hd : Disjoint A B)
    (hAinv : IsInvariantAlong A δ) (hBinv : IsInvariantAlong B η) : δ = η := by
  by_contra hne
  have hinf : δ ⊓ η = ⊥ := by
    have hstrict : δ ⊓ η ≠ δ := by
      intro heq
      have hle : δ ≤ η := by rw [← heq]; exact inf_le_right
      exact hne (Submodule.eq_of_le_of_finrank_eq hle (hδ.trans hη.symm))
    exact ((Submodule.isAtom_iff_finrank_eq_one.mpr hδ).ne_iff_eq_bot inf_le_left).mp hstrict
  have hsup : δ ⊔ η = ⊤ := by
    apply Submodule.eq_top_of_disjoint
    · simp [Plane, Complex.finrank_real_complex, hδ, hη]
    · exact disjoint_iff.mpr hinf
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hdiff : b - a ∈ δ ⊔ η := by rw [hsup]; trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hdiff
  have hpoint : u + a = -v + b := by
    have : u + v = b - a := huv
    calc
      u + a = (u + v) + a - v := by abel
      _ = -v + b := by rw [this]; abel
  have ha' : u + a ∈ A := by
    rw [← hAinv u hu]
    exact Set.mem_vadd_set.mpr ⟨a, ha, rfl⟩
  have hb' : -v + b ∈ B := by
    rw [← hBinv (-v) (η.neg_mem hv)]
    exact Set.mem_vadd_set.mpr ⟨b, hb, rfl⟩
  exact Set.disjoint_left.mp hd ha' (hpoint.symm ▸ hb')

private theorem locallyFell_limit_mono {A B : ℕ → Set Plane} {S U : Set Plane}
    (hA : Tiling.Topology.LocallyFellConverges A S)
    (hB : Tiling.Topology.LocallyFellConverges B U)
    (hsub : ∀ n, A n ⊆ B n) : S ⊆ U := by
  intro x hx
  by_contra hxnot
  have hUclosed : IsClosed U := hB.choose_spec.choose
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUclosed.isOpen_compl x hxnot
  have hhalf : 0 < ε / 2 := half_pos hε
  have hdisj : Disjoint U (Metric.closedBall x (ε / 2)) := by
    rw [Set.disjoint_left]
    intro y hyU hyball
    have hyopen : y ∈ Metric.ball x ε := by
      exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hyball) (by linarith))
    exact hball hyopen hyU
  have hmiss := Tiling.Topology.locallyFellConverges_eventually_disjoint_compact
    hB (isCompact_closedBall x (ε / 2)) hdisj
  have hhit := Tiling.Topology.locallyFellConverges_eventually_exists_mem_ball hA hx hhalf
  obtain ⟨n, hnmiss, y, hyA, hyclose⟩ := (hmiss.and hhit).exists
  exact Set.disjoint_left.mp hnmiss (hsub n hyA)
    (Metric.mem_closedBall.mpr (le_of_lt hyclose))

/-- A bounded lattice correction changes the full limit to `a +ᵥ T`.
The retained piece therefore has to be translated BACK by `-a`. -/
private theorem corrected_piece_subset_original
    {S P T Q : Set Plane} (ℓ : ℕ → Plane) (a : Plane)
    (hPS : P ⊆ S)
    (hpiece : Tiling.Topology.LocallyFellConverges (fun n => ℓ n +ᵥ P) Q)
    (hfull : Tiling.Topology.LocallyFellConverges (fun n => ℓ n +ᵥ S) (a +ᵥ T)) :
    (-a) +ᵥ Q ⊆ T := by
  have hQ := locallyFell_limit_mono hpiece hfull (fun _ => Set.vadd_set_mono hPS)
  rintro x ⟨q, hq, hx⟩
  obtain ⟨t, ht, hqt⟩ := Set.mem_vadd_set.mp (hQ hq)
  have heq : x = t := by
    change -a + q = x at hx
    change a + t = q at hqt
    rw [← hx, ← hqt]
    abel
  exact heq.symm ▸ ht

private theorem invariantCarrier_lattice_of_transversePeriod
    (E : Set Plane) (δ : Submodule ℝ Plane) (v : Plane)
    (hδ : Module.finrank ℝ δ = 1) (hvδ : v ∉ δ)
    (hInv : IsInvariantAlong E δ) (hv : v ∈ periodGroup E) : IsLatticePeriodic E := by
  obtain ⟨L, hL⟩ := periodStepGroup_containsLattice δ v hδ hvδ
  have hstep : periodStepGroup δ v ≤ periodGroup E := by
    apply sup_le
    · intro u hu
      exact hInv u hu
    · apply (AddSubgroup.closure_le _).mpr
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      exact hu ▸ hv
  exact ⟨L, fun _ hu => hstep (hL hu)⟩

private theorem component_centres_subset {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (P : EarthquakeComponent K δ T) : P.centres ⊆ T := by
  rintro x ⟨t, _, rfl⟩
  exact t.property

private theorem component_centres_nonempty {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (P : EarthquakeComponent K δ T) : P.centres.Nonempty := by
  exact P.nonempty_supp.image Subtype.val

private theorem columnPart_subset (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) : columnPart K δ T ⊆ T := by
  intro t ht
  obtain ⟨P, hPt⟩ := Set.mem_iUnion.mp ht
  exact component_centres_subset P.1 hPt

private theorem columnPart_carrier_invariant (K : PolygonalRegion)
    (δ : Submodule ℝ Plane) (T : Set Plane) :
    IsInvariantAlong (regularSupport K (columnPart K δ T)) δ := by
  intro u hu
  let X : Set Plane := ⋃ P : {P : EarthquakeComponent K δ T //
    IsCenterColumn K δ P.centres}, regularSupport K P.1.centres
  have hX : (Homeomorph.addLeft u) '' X = X := by
    dsimp [X]
    rw [Set.image_iUnion]
    congr 1
    funext P
    exact P.property.2.2.2 u hu
  rw [columnPart, regularSupport_iUnion]
  change (Homeomorph.addLeft u) '' interior (closure X) = interior (closure X)
  rw [(Homeomorph.addLeft u).image_interior,
    (Homeomorph.addLeft u).image_closure, hX]

private theorem nonempty_columnPart_of_columnSubset
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T C : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (hpack : IsPacking K.prototileFamily (K.placements T))
    (hCT : C ⊆ T) (hC : IsCenterColumn K δ C) :
    (columnPart K δ T).Nonempty := by
  obtain ⟨P, hP⟩ := column_isComponent K δ T C hδ hpack hCT hC
  have hPcol : IsCenterColumn K δ P.centres := hP.symm ▸ hC
  obtain ⟨c, hc⟩ := hC.2.1
  exact ⟨c, Set.mem_iUnion.mpr ⟨⟨P, hPcol⟩, hP.symm ▸ hc⟩⟩

private theorem exists_noncolumnComponent_of_notAll
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hnotAll : T ≠ columnPart K δ T) :
    ∃ P : EarthquakeComponent K δ T, P ∈ noncolumnComponents K δ T := by
  classical
  have hnotSubset : ¬ T ⊆ columnPart K δ T := by
    intro h
    exact hnotAll (Set.Subset.antisymm h (columnPart_subset K δ T))
  obtain ⟨t, htT, htnot⟩ := Set.sdiff_nonempty.mpr hnotSubset
  let P : EarthquakeComponent K δ T :=
    (earthquakeGraph K δ T).connectedComponentMk ⟨t, htT⟩
  have htP : t ∈ P.centres := ⟨⟨t, htT⟩, by simp [P], rfl⟩
  refine ⟨P, ?_⟩
  intro hcol
  exact htnot (Set.mem_iUnion.mpr ⟨⟨P, hcol⟩, htP⟩)

private theorem unionColumns_eq_columnPart
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hδ : Module.finrank ℝ δ = 1)
    (hp : IsPacking K.prototileFamily (K.placements T))
    (hcols : IsUnionOfColumns K δ T) : T = columnPart K δ T := by
  apply Set.Subset.antisymm _ (columnPart_subset K δ T)
  intro t ht
  obtain ⟨P, hP⟩ := column_isComponent K δ T (lineFibre δ T t) hδ hp
    (fun _ hu => hu.1) (hcols t ht)
  have hPcol : IsCenterColumn K δ P.centres := by
    rw [hP]
    exact hcols t ht
  apply Set.mem_iUnion.mpr
  refine ⟨⟨P, hPcol⟩, ?_⟩
  rw [hP]
  exact ⟨ht, by simp⟩

private theorem lineFibre_vadd (δ : Submodule ℝ Plane) (T : Set Plane)
    (u t : Plane) : lineFibre δ (u +ᵥ T) (u + t) = u +ᵥ lineFibre δ T t := by
  ext x
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hδ⟩
    refine ⟨s, ⟨hs, ?_⟩, rfl⟩
    convert hδ using 1
    change s - t = (u + s) - (u + t)
    abel
  · rintro ⟨s, ⟨hs, hδ⟩, rfl⟩
    refine ⟨⟨s, hs, rfl⟩, ?_⟩
    convert hδ using 1
    change (u + s) - (u + t) = s - t
    abel

private theorem centerColumn_vadd {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {C : Set Plane} (hC : IsCenterColumn K δ C) (u : Plane) :
    IsCenterColumn K δ (u +ᵥ C) := by
  obtain ⟨hpack, hne, ⟨a, ha⟩, hinv⟩ := hC
  refine ⟨(tilesOn_translate (tilesOn_regularSupport_of_packing hpack) u).2.1,
    hne.image (fun y => u +ᵥ y), ⟨u + a, ?_⟩, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    convert ha y hy using 1
    change (u + y) - (u + a) = y - a
    abel
  · rw [regularSupport_vadd]
    intro v hv
    rw [vadd_vadd, add_comm v u, ← vadd_vadd, hinv v hv]

private theorem unionColumns_vadd {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (hcol : IsUnionOfColumns K δ T) (u : Plane) :
    IsUnionOfColumns K δ (u +ᵥ T) := by
  rintro x ⟨t, ht, rfl⟩
  change IsCenterColumn K δ (lineFibre δ (u +ᵥ T) (u + t))
  rw [lineFibre_vadd]
  exact centerColumn_vadd (hcol t ht) u

private theorem regularSupport_nonempty_of_nonempty (K : PolygonalRegion)
    {C : Set Plane} (hC : C.Nonempty) : (regularSupport K C).Nonempty := by
  obtain ⟨c, hc⟩ := hC
  obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hopen : IsOpen (openUnion K C) := by
    apply isOpen_iUnion
    intro t
    exact isOpen_interior.vadd (t : Plane)
  exact ⟨c + x, hopen.subset_interior_closure
    (Set.mem_iUnion.mpr ⟨⟨c, hc⟩, Set.mem_vadd_set.mpr ⟨x, hx, rfl⟩⟩)⟩

private theorem nontrivial_noncolumnComponent_periodicProper
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hK : HasRationalSlopes K) (hδ : Module.finrank ℝ δ = 1)
    (hbδ : HasBoundaryDirection K δ) (hT : TilesOn K T Set.univ)
    (hready : IsUniformlyReady K δ T)
    (hquake : HasNontrivialEarthquakeDecomposition K δ T)
    (hnotAll : T ≠ columnPart K δ T)
    (P : EarthquakeComponent K δ T) (hP : P ∈ noncolumnComponents K δ T) :
    P.centres.Nonempty ∧ P.centres ⊆ T ∧ P.carrier ≠ Set.univ ∧
      IsInvariantAlong P.carrier δ ∧ IsLatticePeriodic P.carrier := by
  have hTinv : IsInvariantAlong (regularSupport K T) δ := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) hT]
    intro u hu
    simp
  have hPinv := component_isInvariant K δ T hδ hT.2.1 hTinv P
  obtain ⟨v, hvδ, _, hvP⟩ :=
    uniformlyReady_commonCarrierPeriod K δ T hK hδ hbδ hT hready hquake
  have hPperiod := invariantCarrier_lattice_of_transversePeriod
    P.carrier δ v hδ hvδ hPinv (hvP P hP)
  have hPproper : P.carrier ≠ Set.univ := by
    obtain hall | ⟨P₀, Q₀, hne⟩ := hquake
    · exact False.elim (hnotAll hall)
    · have hexQ : ∃ Q : EarthquakeComponent K δ T, P ≠ Q := by
        by_cases hPP₀ : P = P₀
        · exact ⟨Q₀, hPP₀ ▸ hne⟩
        · exact ⟨P₀, hPP₀⟩
      obtain ⟨Q, hPQ⟩ := hexQ
      have hd := components_carriers_disjoint K δ T hδ hT.2.1
        (Set.mem_univ P) (Set.mem_univ Q) hPQ
      change Disjoint P.carrier Q.carrier at hd
      obtain ⟨x, hx⟩ := regularSupport_nonempty_of_nonempty K (component_centres_nonempty Q)
      intro hfull
      rw [hfull] at hd
      exact Set.disjoint_left.mp hd (Set.mem_univ x) hx
  exact ⟨component_centres_nonempty P, component_centres_subset P, hPproper, hPinv, hPperiod⟩

/-- Eventual exact membership is retained in an orbit limit; this does not
assert that the image exhausts a fibre of that limit. -/
private theorem mem_limit_of_eventually_mem {A : ℕ → Set Plane} {U : Set Plane}
    (hconv : Tiling.Topology.LocallyFellConverges A U) {x : Plane}
    (hx : ∀ᶠ n in atTop, x ∈ A n) : x ∈ U := by
  by_contra hnot
  have hdisj : Disjoint U ({x} : Set Plane) := by
    simpa only [Set.disjoint_singleton_right] using hnot
  have hmiss := Tiling.Topology.locallyFellConverges_eventually_disjoint_compact
    hconv isCompact_singleton hdisj
  obtain ⟨n, hn, hdn⟩ := (hx.and hmiss).exists
  exact Set.disjoint_left.mp hdn hn (Set.mem_singleton x)

/-- The exact persistent image is placed in the SAME specified full limit.
Only additivity is used: no continuity or multiplicativity of the scalar map. -/
private theorem persistent_deformedImage_subset_limit
    {K : PolygonalRegion} {T : Set Plane} {η : Submodule ℝ Plane}
    (p : PersistentColumnData K T η) (φ : ℝ →ₗ[ℚ] ℚ) (tφ : Plane)
    (U : Set Plane)
    (hconv : Tiling.Topology.LocallyFellConverges
      (fun n => (tφ - Tiling.Approximation.deformPoint φ (p.movingCentre n)) +ᵥ
        (Tiling.Approximation.deformPoint φ '' T)) U) :
    (fun u => tφ + Tiling.Approximation.deformPoint φ (u - p.anchor)) '' p.column ⊆ U := by
  rintro x ⟨u, hu, rfl⟩
  apply mem_limit_of_eventually_mem hconv
  filter_upwards [p.persistent u hu] with n hn
  apply Set.mem_vadd_set.mpr
  refine ⟨Tiling.Approximation.deformPoint φ (u - (p.anchor - p.movingCentre n)),
    ⟨u - (p.anchor - p.movingCentre n), hn, rfl⟩, ?_⟩
  change (tφ - Tiling.Approximation.deformPoint φ (p.movingCentre n)) +
    Tiling.Approximation.deformPoint φ (u - (p.anchor - p.movingCentre n)) = _
  change (tφ - Tiling.Approximation.deformPointLinear φ (p.movingCentre n)) +
    Tiling.Approximation.deformPointLinear φ (u - (p.anchor - p.movingCentre n)) =
      tφ + Tiling.Approximation.deformPointLinear φ (u - p.anchor)
  simp only [map_sub]
  abel

private theorem column_integer_remainder {q : Plane} (hq : q ≠ 0)
    (r : ℝ) : ∃ m : ℤ, ‖(r - (m : ℝ)) • q‖ < ‖q‖ := by
  refine ⟨Int.floor r, ?_⟩
  have hr0 : 0 ≤ r - (Int.floor r : ℝ) := sub_nonneg.mpr (Int.floor_le r)
  have hr1 : r - (Int.floor r : ℝ) < 1 := by
    rw [sub_lt_iff_lt_add]
    linarith [Int.lt_floor_add_one r]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq
  nlinarith

private theorem column_real_smul_sub_int_zsmul (r : ℝ) (m : ℤ) (q : Plane) :
    r • q - m • q = (r - (m : ℝ)) • q := by
  rw [← Int.cast_smul_eq_zsmul ℝ, ← sub_smul]

private theorem centerColumn_period {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {C : Set Plane} (hδ : Module.finrank ℝ δ = 1)
    (hC : IsCenterColumn K δ C) :
    ∃ q : Plane, q ∈ δ ∧ q ≠ 0 ∧ q ∈ periodGroup C := by
  obtain ⟨q, hqδ, hq0, hqperiod⟩ := column_universal_period K δ hδ
  exact ⟨q, hqδ, hq0, hqperiod C hC⟩

/-- A real universal longitudinal period and local packing finiteness reduce
all bounded differences to one bounded fundamental interval. -/
private theorem centerColumn_hasFLC {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {C : Set Plane} (hδ : Module.finrank ℝ δ = 1)
    (hC : IsCenterColumn K δ C) : HasFLC C := by
  classical
  obtain ⟨q, hqδ, hq0, hqperiod⟩ := centerColumn_period hδ hC
  obtain ⟨a, ha⟩ := hC.2.2.1
  obtain ⟨c₀, hc₀⟩ := hC.2.1
  have hspan : δ = Submodule.span ℝ ({q} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ hqδ hq0
  have hlocal := (packing_centres_locallyFinite hC.1).1
  refine ⟨hlocal, ?_⟩
  intro R hR
  let B : Set Plane := C ∩ Metric.closedBall c₀ (R + ‖q‖)
  have hBfinite : B.Finite := hlocal _ Metric.isBounded_closedBall
  apply (hBfinite.sub hBfinite).subset
  intro z hz
  obtain ⟨c, hcC, c', hc'C, rfl⟩ := Set.mem_sub.mp hz.1
  have hzBound : ‖c - c'‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz.2
  have hcδ : c - c₀ ∈ δ := by
    convert δ.sub_mem (ha c hcC) (ha c₀ hc₀) using 1
    abel
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hcδ)
  obtain ⟨m, hm⟩ := column_integer_remainder hq0 r
  have hres : c - c₀ - m • q = (r - (m : ℝ)) • q := by
    rw [← hr, column_real_smul_sub_int_zsmul]
  have hresNorm : ‖c - c₀ - m • q‖ < ‖q‖ := by rwa [hres]
  have hnegtranslate : -(m • q) +ᵥ C = C :=
    (periodGroup C).neg_mem ((periodGroup C).zsmul_mem hqperiod m)
  let c₁ := c - m • q
  let c₁' := c' - m • q
  have hc₁ : c₁ ∈ C := by
    dsimp [c₁]
    rw [← hnegtranslate]
    exact Set.mem_vadd_set.mpr ⟨c, hcC, by simp [sub_eq_add_neg, add_comm]⟩
  have hc₁' : c₁' ∈ C := by
    dsimp [c₁']
    rw [← hnegtranslate]
    exact Set.mem_vadd_set.mpr ⟨c', hc'C, by simp [sub_eq_add_neg, add_comm]⟩
  have hsub : c₁ - c₀ = c - c₀ - m • q := by dsimp [c₁]; abel
  have hc₁ball : c₁ ∈ Metric.closedBall c₀ (R + ‖q‖) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hsub]
    exact le_trans hresNorm.le (by linarith)
  have hshiftDist : dist c₁' c₁ = dist c' c := by
    dsimp [c₁, c₁']
    simp only [sub_eq_add_neg, dist_add_right]
  have hc₁'ball : c₁' ∈ Metric.closedBall c₀ (R + ‖q‖) := by
    rw [Metric.mem_closedBall]
    calc
      dist c₁' c₀ ≤ dist c₁' c₁ + dist c₁ c₀ := dist_triangle _ _ _
      _ = dist c' c + dist c₁ c₀ := by rw [hshiftDist]
      _ ≤ R + ‖q‖ := by
        have hcc' : dist c' c ≤ R := by
          simpa [dist_comm, dist_eq_norm] using hzBound
        have hc₁c₀ : dist c₁ c₀ ≤ ‖q‖ := by
          rw [dist_eq_norm, hsub]
          exact hresNorm.le
        linarith
  refine ⟨c₁, ⟨hc₁, hc₁ball⟩, c₁', ⟨hc₁', hc₁'ball⟩, ?_⟩
  dsimp [c₁, c₁']
  abel

private theorem centerColumn_lineRelativeDense
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {C : Set Plane}
    (hδ : Module.finrank ℝ δ = 1) (hC : IsCenterColumn K δ C) :
    ∀ t ∈ C, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z, z - t ∈ δ → ∃ c ∈ C, dist z c < ρ := by
  obtain ⟨q, hqδ, hq0, hqperiod⟩ := centerColumn_period hδ hC
  have hspan : δ = Submodule.span ℝ ({q} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ hqδ hq0
  intro t ht
  refine ⟨‖q‖, norm_pos_iff.mpr hq0, ?_⟩
  intro z hzt
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hzt)
  obtain ⟨m, hm⟩ := column_integer_remainder hq0 r
  have htranslate : (m • q) +ᵥ C = C := (periodGroup C).zsmul_mem hqperiod m
  have hcmem : t + m • q ∈ C := by
    rw [← htranslate]
    exact Set.mem_vadd_set.mpr ⟨t, ht, by simp [add_comm]⟩
  refine ⟨t + m • q, hcmem, ?_⟩
  rw [dist_eq_norm]
  have hsub : z - (t + m • q) = r • q - m • q := by
    calc
      z - (t + m • q) = (z - t) - m • q := by abel
      _ = r • q - m • q := by rw [hr]
  rw [hsub, column_real_smul_sub_int_zsmul]
  exact hm

/-- Anchor normalization turns the persistent affine image into the literal
linear image; this is algebra, not an assertion that it exhausts a limit fibre. -/
private theorem persistent_linearImage_subset_limit
    {K : PolygonalRegion} {T : Set Plane} {η : Submodule ℝ Plane}
    (p : PersistentColumnData K T η) (φ : ℝ →ₗ[ℚ] ℚ) (U : Set Plane)
    (hconv : Tiling.Topology.LocallyFellConverges
      (fun n => (Tiling.Approximation.deformPoint φ p.anchor -
        Tiling.Approximation.deformPoint φ (p.movingCentre n)) +ᵥ
          (Tiling.Approximation.deformPoint φ '' T)) U) :
    Tiling.Approximation.deformPoint φ '' p.column ⊆ U := by
  have heq : (fun u => Tiling.Approximation.deformPoint φ p.anchor +
      Tiling.Approximation.deformPoint φ (u - p.anchor)) =
        Tiling.Approximation.deformPoint φ := by
    funext u
    change Tiling.Approximation.deformPointLinear φ p.anchor +
      Tiling.Approximation.deformPointLinear φ (u - p.anchor) =
        Tiling.Approximation.deformPointLinear φ u
    rw [map_sub, add_sub_cancel]
  simpa only [heq] using
    persistent_deformedImage_subset_limit p φ
      (Tiling.Approximation.deformPoint φ p.anchor) U hconv

/-- FT's exact proper-vertex transport and rational coset preservation prove
that the literal image is a complete column before any maximal-fibre argument. -/
private theorem deformedColumn_of_properVerticesTransport
    {K L : PolygonalRegion} {C : Set Plane} {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) (hrat : HasRationalDirection δ)
    (hC : IsCenterColumn K δ C) (φ : ℝ →ₗ[ℚ] ℚ)
    (hpack : IsPacking L.prototileFamily
      (L.placements (Tiling.Approximation.deformPoint φ '' C)))
    (hvertices : properVertices
      (regularSupport L (Tiling.Approximation.deformPoint φ '' C)) =
        Tiling.Approximation.deformPoint φ '' properVertices (regularSupport K C)) :
    IsCenterColumn L δ (Tiling.Approximation.deformPoint φ '' C) := by
  obtain ⟨a, ha⟩ := hC.2.2.1
  obtain ⟨n, hn⟩ := Approximation.rationalDirection_hasNormal δ hδ hrat
  have hline : IsLineSupported (Tiling.Approximation.deformPoint φ '' C) δ := by
    refine ⟨Tiling.Approximation.deformPoint φ a, ?_⟩
    rintro x ⟨c, hc, rfl⟩
    rw [← hn]
    apply Tiling.Approximation.rationalDirection_preservesCoset
    simpa only [hn] using ha c hc
  have hsource : properVertices (regularSupport K C) = ∅ :=
    (lineCarrier_noProperVertices_iff_column hδ hC.2.1 hC.1 hC.2.2.1).mpr hC
  apply (lineCarrier_noProperVertices_iff_column hδ
    (hC.2.1.image (Tiling.Approximation.deformPoint φ)) hpack hline).mp
  rw [hvertices, hsource, Set.image_empty]

private theorem finiteFLC_columnDeformation
    (K : PolygonalRegion) (C : Set Plane) (δ : Submodule ℝ Plane)
    (hK : HasRationalSlopes K) (hδ : Module.finrank ℝ δ = 1)
    (hrat : HasRationalDirection δ) (hC : IsCenterColumn K δ C) :
    ∃ P : Approximation.PolyhedralCode, Approximation.polyhedralSupport P = K.support ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, Tiling.Approximation.IsFiniteApproximation F ε φ →
          ∃ L : PolygonalRegion,
            L.support = Approximation.deformedPolyhedralSupport P φ ∧
            Tiling.IsRational L.support ∧ HasRationalSlopes L ∧
            IsCenterColumn L δ (Tiling.Approximation.deformPoint φ '' C) := by
  obtain ⟨a, haC⟩ := hC.2.1
  obtain ⟨b, hb⟩ := hC.2.2.1
  have hline : ∀ c ∈ C, c - a ∈ δ := by
    intro c hc
    convert δ.sub_mem (hb c hc) (hb a haC) using 1
    abel
  obtain ⟨P, hP, W, hW, hzero, F, ε, hε, hdeform⟩ :=
    Approximation.finiteFLCFibre_germEquivalence K C δ a hK hδ hrat
      (centerColumn_hasFLC hδ hC) hline
      (centerColumn_lineRelativeDense hδ hC a haC)
      (tilesOn_regularSupport_of_packing hC.1)
  refine ⟨P, hP, F, ε, hε, ?_⟩
  intro φ hφ
  obtain ⟨L, hLP, hLrat, hLslopes, _, _, htiles, _, hvertices⟩ := hdeform φ hφ
  exact ⟨L, hLP, hLrat, hLslopes,
    deformedColumn_of_properVerticesTransport hδ hrat hC φ htiles.2.1
      (hvertices C (Set.Subset.refl C))⟩

/-- Absolute rationality implies the required relative rationality. The
intrinsic anchor is obtained from the actual finite positive vertex-gap data. -/
private theorem relativelyRational_of_rationalSupport
    (L : PolygonalRegion) (hL : Tiling.IsRational L.support) :
    Tiling.RationalPolygonal.IsRelativelyRational L := by
  have hre : (Complex.reCLM : Plane →L[ℝ] ℝ) ≠ 0 := by
    intro heq
    have h := congrArg (fun f : Plane →L[ℝ] ℝ => f 1) heq
    norm_num at h
  obtain ⟨_, ⟨r, hr⟩, _⟩ := positiveVertexGaps_finitePositive L Complex.reCLM hre
  obtain ⟨_, v, hv, w, hw, _⟩ := hr
  refine ⟨v, hv, ?_⟩
  intro z hz
  obtain ⟨x, y, hx, hy⟩ := hL.2 z hz
  obtain ⟨xv, yv, hxv, hyv⟩ := hL.2 v hv
  refine ⟨x - xv, y - yv, ?_, ?_⟩
  · simp only [Complex.sub_re, hx, hxv, Rat.cast_sub]
  · simp only [Complex.sub_im, hy, hyv, Rat.cast_sub]

namespace Approximation

private theorem uniformReadiness_sign_nonpos (x : ℝ) :
    Real.sign x ≤ 0 ↔ x ≤ 0 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [Real.sign_of_neg hx, hx.le]
  · simp [hx]
  · simp [Real.sign_of_pos hx, not_le.mpr hx]

private theorem uniformReadiness_support_transport_mem
    (P : PolyhedralCode) (φ : ℝ →ₗ[ℚ] ℚ) (H : Plane ≃ₜ Plane)
    (hH : ∀ cell ∈ P, ∀ l ∈ cell, ∀ z : Plane,
      Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z))
    (z : Plane) :
    H z ∈ deformedPolyhedralSupport P φ ↔ z ∈ polyhedralSupport P := by
  have hle (cell : List RationalLine) (hc : cell ∈ P) (l : RationalLine)
      (hl : l ∈ cell) : (deformLine φ l).eval (H z) ≤ 0 ↔ l.eval z ≤ 0 := by
    rw [← uniformReadiness_sign_nonpos, hH cell hc l hl z,
      uniformReadiness_sign_nonpos]
  constructor
  · rintro ⟨cell', hcell', hcell⟩
    obtain ⟨cell, hc, rfl⟩ := List.mem_map.mp hcell'
    refine ⟨cell, hc, ?_⟩
    intro l hl
    exact (hle cell hc l hl).mp
      (hcell (deformLine φ l) (List.mem_map.mpr ⟨l, hl, rfl⟩))
  · rintro ⟨cell, hc, hcell⟩
    refine ⟨cell.map (deformLine φ), List.mem_map.mpr ⟨cell, hc, rfl⟩, ?_⟩
    intro l' hl'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
    exact (hle cell hc l hl).mpr (hcell l hl)

private theorem uniformReadiness_exterior_line_witness
    (P : PolyhedralCode) (y : Plane) (hy : y ∉ polyhedralSupport P) :
    ∀ cell ∈ P, ∃ l ∈ cell, 0 < l.eval y := by
  intro cell hc
  by_contra h
  push Not at h
  apply hy
  exact ⟨cell, hc, h⟩

private theorem uniformReadiness_lineEval_continuous (l : RationalLine) :
    Continuous l.eval := by
  change Continuous (fun z : Plane =>
    (l.normal.x : ℝ) * z.re + (l.normal.y : ℝ) * z.im - l.offset)
  fun_prop

/-- The finite arrangement transport gives the inner half of support closeness.
The compact net is tested by coordinate evaluations, while all code signs are
preserved by the transport homeomorphism. -/
private theorem uniformReadiness_deformedSupport_innerClose
    (K : Tiling.RationalPolygonal.PolygonalRegion) (P : PolyhedralCode)
    (hP : polyhedralSupport P = K.support) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ℝ, ∃ τ : ℝ, 0 < τ ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, Tiling.Approximation.IsFiniteApproximation F τ φ →
        ∀ x ∈ K.support, ∃ y ∈ deformedPolyhedralSupport P φ, dist x y < ε := by
  classical
  obtain ⟨Z, hZsub, hZfinite, hZcover⟩ :=
    IsCompact.finite_cover_balls K.isPolygonal.isCompact (e := ε / 3) (by positivity)
  let Zf : Finset Plane := hZfinite.toFinset
  let L : Finset RationalLine := P.flatten.toFinset
  obtain ⟨F₀, τ₀, hτ₀, htransport⟩ :=
    finiteRationalArrangement_transport L Zf
  let F : Finset ℝ := F₀ ∪ Zf.image Complex.re ∪ Zf.image Complex.im
  let τ : ℝ := min τ₀ (ε / 3)
  refine ⟨F, τ, lt_min hτ₀ (by positivity), ?_⟩
  intro φ hφ x hx
  have hφ₀ : Tiling.Approximation.IsFiniteApproximation F₀ τ₀ φ := by
    refine ⟨hφ.1, ?_⟩
    intro r hr
    have hr' : r ∈ F := by simp [F, hr]
    have hbound := hφ.2 r hr'
    exact lt_of_lt_of_le hbound (min_le_left _ _)
  obtain ⟨H, hHZ, hsign⟩ := htransport φ hφ₀
  obtain ⟨z, hzZ, hxz⟩ := by
    have hxcover : x ∈ ⋃ z ∈ Z, Metric.ball z (ε / 3) := hZcover hx
    simpa only [mem_iUnion, Metric.mem_ball] using hxcover
  have hzmem : z ∈ Zf := by
    simpa [Zf] using hzZ
  have hzK : z ∈ K.support := hZsub hzZ
  have hlines : ∀ cell ∈ P, ∀ l ∈ cell, l ∈ L := by
    intro cell hc l hl
    simp only [L, List.mem_toFinset, List.mem_flatten]
    exact ⟨cell, hc, hl⟩
  have htarget : H z ∈ deformedPolyhedralSupport P φ :=
    (uniformReadiness_support_transport_mem P φ H
      (fun cell hc l hl => hsign l (hlines cell hc l hl)) z).2
      (by rw [hP]; exact hzK)
  have hmove : dist z (Tiling.Approximation.deformPoint φ z) < 2 * (ε / 3) := by
    have hre : |((φ z.re : ℚ) : ℝ) - z.re| < τ := by
      apply hφ.2
      simp only [F, Finset.mem_union]
      left
      right
      exact Finset.mem_image.mpr ⟨z, hzmem, rfl⟩
    have him : |((φ z.im : ℚ) : ℝ) - z.im| < τ := by
      apply hφ.2
      simp only [F, Finset.mem_union]
      right
      exact Finset.mem_image.mpr ⟨z, hzmem, rfl⟩
    have hnorm : ‖z - Tiling.Approximation.deformPoint φ z‖ ≤
        |z.re - (φ z.re : ℝ)| + |z.im - (φ z.im : ℝ)| := by
      simp only [Tiling.Approximation.deformPoint, Complex.norm_def]
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · rw [Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im]
        nlinarith [sq_abs (z.re - (φ z.re : ℝ)),
          sq_abs (z.im - (φ z.im : ℝ)),
          mul_nonneg (abs_nonneg (z.re - (φ z.re : ℝ)))
            (abs_nonneg (z.im - (φ z.im : ℝ)))]
    calc
      dist z (Tiling.Approximation.deformPoint φ z) =
          ‖z - Tiling.Approximation.deformPoint φ z‖ := by simp [dist_eq_norm]
      _ ≤ |z.re - (φ z.re : ℝ)| + |z.im - (φ z.im : ℝ)| := hnorm
      _ < τ + τ := add_lt_add (by simpa [abs_sub_comm] using hre) (by simpa [abs_sub_comm] using him)
      _ ≤ 2 * (ε / 3) := by dsimp [τ]; nlinarith [min_le_right τ₀ (ε / 3)]
  have htarget' : Tiling.Approximation.deformPoint φ z ∈
      deformedPolyhedralSupport P φ := by
    rw [← hHZ z hzmem]
    exact htarget
  refine ⟨Tiling.Approximation.deformPoint φ z, htarget', ?_⟩
  calc
    dist x (Tiling.Approximation.deformPoint φ z) ≤
        dist x z + dist z (Tiling.Approximation.deformPoint φ z) := dist_triangle x z _
    _ < ε / 3 + 2 * (ε / 3) := add_lt_add hxz hmove
    _ = ε := by ring

/-- A finite subcover of the bounded exterior gives uniform offset tests for
the outer half of support closeness. -/
private theorem uniformReadiness_deformedSupport_outerClose
    (K : Tiling.RationalPolygonal.PolygonalRegion) (P : PolyhedralCode)
    (hP : polyhedralSupport P = K.support) {B ε : ℝ}
    (_hB : 0 < B) (hε : 0 < ε) :
    ∃ F : Finset ℝ, ∃ τ : ℝ, 0 < τ ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, Tiling.Approximation.IsFiniteApproximation F τ φ →
        ∀ y ∈ deformedPolyhedralSupport P φ,
          y ∈ Metric.closedBall 0 B →
            ∃ x ∈ K.support, dist y x < ε := by
  classical
  by_cases hnil : P = []
  · refine ⟨∅, 1, by norm_num, ?_⟩
    intro φ hφ y hy
    simp [hnil, deformedPolyhedralSupport, polyhedralSupport] at hy
  let bad : Set Plane := Metric.closedBall 0 B ∩
    ⋂ x : {x : Plane // x ∈ K.support}, {y : Plane | ε ≤ dist y x}
  have hbadClosed : IsClosed bad := by
    apply Metric.isClosed_closedBall.inter
    exact isClosed_iInter fun x => isClosed_le continuous_const
      (continuous_id.dist continuous_const)
  have hbadCompact : IsCompact bad :=
    (isCompact_closedBall (0 : Plane) B).of_isClosed_subset hbadClosed inter_subset_left
  set_option linter.style.haveILetI false in
  haveI : Finite {c : List RationalLine // c ∈ P.toFinset} := inferInstance
  let Cell := {c : List RationalLine // c ∈ P.toFinset}
  let idx := {y : Plane // y ∈ bad}
  have hyNotSupport (i : idx) : i.1 ∉ polyhedralSupport P := by
    intro hy
    have hdist : ε ≤ dist i.1 i.1 :=
      (mem_iInter.mp i.2.2) ⟨i.1, by simpa [hP] using hy⟩
    simp at hdist
    linarith
  let lineAt (i : idx) (c : Cell) : RationalLine :=
    Classical.choose (uniformReadiness_exterior_line_witness P i.1
      (hyNotSupport i) c.1 (List.mem_toFinset.mp c.2))
  have hlineAt (i : idx) (c : Cell) :
      lineAt i c ∈ c.1 ∧ 0 < (lineAt i c).eval i.1 := by
    exact Classical.choose_spec (uniformReadiness_exterior_line_witness P i.1
      (hyNotSupport i) c.1 (List.mem_toFinset.mp c.2))
  let margin (i : idx) (c : Cell) : ℝ := (lineAt i c).eval i.1 / 2
  let U (i : idx) : Set Plane := ⋂ c : Cell,
    {w : Plane | margin i c < (lineAt i c).eval w}
  have hUopen (i : idx) : IsOpen (U i) := by
    apply isOpen_iInter_of_finite
    intro c
    exact isOpen_lt continuous_const (uniformReadiness_lineEval_continuous (lineAt i c))
  have hcenterU (i : idx) : i.1 ∈ U i := by
    rw [mem_iInter]
    intro c
    dsimp [margin]
    linarith [(hlineAt i c).2]
  obtain ⟨t, hcover⟩ := hbadCompact.elim_finite_subcover U hUopen (by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hcenterU ⟨y, hy⟩⟩)
  let M : Finset ℝ := insert 1 (t.biUnion fun i => Finset.univ.image (margin i))
  have hMne : M.Nonempty := ⟨1, by simp [M]⟩
  have hMpos : ∀ r ∈ M, 0 < r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with hr1 | hrM
    · norm_num [hr1]
    · simp only [Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_univ, true_and] at hrM
      obtain ⟨i, hi, c, rfl⟩ := hrM
      exact half_pos (hlineAt i c).2
  let τ : ℝ := M.min' hMne / 2
  have hτ : 0 < τ := half_pos (hMpos _ (Finset.min'_mem M hMne))
  refine ⟨P.flatten.toFinset.image RationalLine.offset, τ, hτ, ?_⟩
  intro φ hφ y hy hball
  by_contra hclose
  push Not at hclose
  have hybad : y ∈ bad := by
    refine ⟨hball, ?_⟩
    rw [mem_iInter]
    intro x
    exact hclose x.1 x.2
  obtain ⟨i, hi, hyU⟩ : ∃ i, i ∈ t ∧ y ∈ U i := by
    rcases Set.mem_iUnion.mp (hcover hybad) with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨hit, hyU⟩
    exact ⟨i, hit, hyU⟩
  obtain ⟨cell', hcell', hineq⟩ := hy
  obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hcell'
  let c : Cell := ⟨cell, List.mem_toFinset.mpr hcell⟩
  let l := lineAt i c
  have hlcell : l ∈ cell := hlineAt i c |>.1
  have hmargin : τ < margin i c := by
    have hmarginMem : margin i c ∈ M := by
      apply Finset.mem_insert.mpr
      right
      exact Finset.mem_biUnion.mpr ⟨i, hi,
        Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩
    have hminle : M.min' hMne ≤ margin i c := Finset.min'_le M _ hmarginMem
    dsimp [τ]
    linarith [hMpos _ (Finset.min'_mem M hMne)]
  have hyUline : margin i c < l.eval y := by
    exact mem_iInter.mp hyU c
  have hlflat : l ∈ P.flatten := List.mem_flatten.mpr ⟨cell, hcell, hlcell⟩
  have hoff : l.offset ∈ P.flatten.toFinset.image RationalLine.offset :=
    Finset.mem_image.mpr ⟨l, List.mem_toFinset.mpr hlflat, rfl⟩
  have hoffclose : |(φ l.offset : ℝ) - l.offset| < τ := hφ.2 _ hoff
  have hpositive : 0 < (deformLine φ l).eval y := by
    change 0 < Tiling.Approximation.normalEval l.normal y - (φ l.offset : ℝ)
    rw [RationalLine.eval] at hyUline
    have hphiupper : (φ l.offset : ℝ) - l.offset < τ := (abs_lt.mp hoffclose).2
    linarith
  have hnonpos := hineq (deformLine φ l) (List.mem_map.mpr ⟨l, hlcell, rfl⟩)
  linarith

/-- A single finite test set controls both directions of support closeness for
all bounded polygonal regions with the prescribed deformed support. -/
private theorem uniformReadiness_supportClose_control
    (K : Tiling.RationalPolygonal.PolygonalRegion) (P : PolyhedralCode)
    (hP : polyhedralSupport P = K.support) {B ε : ℝ}
    (hB : 0 < B) (hε : 0 < ε) :
    ∃ F : Finset ℝ, ∃ τ : ℝ, 0 < τ ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, Tiling.Approximation.IsFiniteApproximation F τ φ →
        ∀ L : Tiling.RationalPolygonal.PolygonalRegion,
          L.support = deformedPolyhedralSupport P φ →
          L.support ⊆ Metric.closedBall 0 B →
            (∀ x ∈ K.support, ∃ y ∈ L.support, dist x y < ε) ∧
            (∀ y ∈ L.support, ∃ x ∈ K.support, dist y x < ε) := by
  classical
  obtain ⟨Fi, τi, hτi, hi⟩ := uniformReadiness_deformedSupport_innerClose K P hP hε
  obtain ⟨Fo, τo, hτo, ho⟩ := uniformReadiness_deformedSupport_outerClose K P hP hB hε
  let F := Fi ∪ Fo
  let τ := min τi τo
  refine ⟨F, τ, lt_min hτi hτo, ?_⟩
  intro φ hφ L hL hLball
  have hφi : Tiling.Approximation.IsFiniteApproximation Fi τi φ := by
    refine ⟨hφ.1, ?_⟩
    intro r hr
    exact lt_of_lt_of_le (hφ.2 r (by simp [F, hr])) (min_le_left _ _)
  have hφo : Tiling.Approximation.IsFiniteApproximation Fo τo φ := by
    refine ⟨hφ.1, ?_⟩
    intro r hr
    exact lt_of_lt_of_le (hφ.2 r (by simp [F, hr])) (min_le_right _ _)
  constructor
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hi φ hφi x hx
    exact ⟨y, by rw [hL]; exact hy, hxy⟩
  · intro y hy
    have hy' : y ∈ deformedPolyhedralSupport P φ := by rw [← hL]; exact hy
    obtain ⟨x, hx, hyx⟩ := ho φ hφo y hy' (hLball hy)
    exact ⟨x, hx, by simpa [dist_comm] using hyx⟩

end Approximation

private theorem polygonalRegion_eq_of_support_eq {K L : PolygonalRegion}
    (h : K.support = L.support) : K = L := by
  cases K
  cases L
  cases h
  rfl

/-- The same prototype is used by LT and the exact FT image-column
construction. Only finite unions and minima combine their tests. -/
private theorem joint_columnDeformation
    (K : PolygonalRegion) (T : Set Plane) (δ η : Submodule ℝ Plane)
    (hK : HasRationalSlopes K) (hδ : Module.finrank ℝ δ = 1)
    (hη : Module.finrank ℝ η = 1) (hbδ : HasBoundaryDirection K δ)
    (hbη : HasBoundaryDirection K η) (hT : TilesOn K T Set.univ)
    (hquake : HasNontrivialEarthquakeDecomposition K δ T)
    (hcolumnPart : (columnPart K δ T).Nonempty) (p : PersistentColumnData K T η) :
    ∃ P : Approximation.PolyhedralCode, Approximation.polyhedralSupport P = K.support ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, Tiling.Approximation.IsFiniteApproximation F ε φ →
          ∃ L : PolygonalRegion,
            L.support = Approximation.deformedPolyhedralSupport P φ ∧
            Tiling.IsRational L.support ∧
            TilesOn L (Tiling.Approximation.deformPoint φ '' T) Set.univ ∧
            (columnPart L δ (Tiling.Approximation.deformPoint φ '' T)).Nonempty ∧
            IsCenterColumn L η (Tiling.Approximation.deformPoint φ '' p.column) := by
  classical
  have hratδ := hasRationalDirection_of_hasBoundaryDirection hK hbδ
  have hratη := hasRationalDirection_of_hasBoundaryDirection hK hbη
  obtain ⟨P, hP, F₁, ε₁, hε₁, hLT⟩ := Approximation.oneLinkRationalDeformation
    K T δ hδ hratδ hK hT (nontrivial_decomposition_hasLink K δ T hδ hT hquake)
  obtain ⟨Q, hQ, F₂, ε₂, hε₂, hFT⟩ :=
    finiteFLC_columnDeformation K p.column η hK hη hratη p.column_isColumn
  obtain ⟨F₃, ε₃, hε₃, hcodes⟩ :=
    Approximation.polyhedralDeformation_independentOfCode K P Q hP hQ
  let F := F₁ ∪ F₂ ∪ F₃
  let ε := min ε₁ (min ε₂ ε₃)
  refine ⟨P, hP, F, ε, lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro φ hφ
  have hφ₁ := Tiling.Approximation.finiteApproximation_strengthen F₁ F ε₁ ε φ
    (by dsimp [F]; exact Finset.subset_union_left.trans Finset.subset_union_left)
    (min_le_left _ _) hφ
  have hφ₂ := Tiling.Approximation.finiteApproximation_strengthen F₂ F ε₂ ε φ
    (by dsimp [F]; exact Finset.subset_union_right.trans Finset.subset_union_left)
    ((min_le_right _ _).trans (min_le_left _ _)) hφ
  have hφ₃ := Tiling.Approximation.finiteApproximation_strengthen F₃ F ε₃ ε φ
    (by dsimp [F]; exact Finset.subset_union_right)
    ((min_le_right _ _).trans (min_le_right _ _)) hφ
  obtain ⟨L, hLP, hLrat, _, hLtiles, _, hLcols⟩ := hLT φ hφ₁
  obtain ⟨L', hLQ, _, _, hL'col⟩ := hFT φ hφ₂
  have heq : L' = L := polygonalRegion_eq_of_support_eq
    (hLQ.trans ((hcodes φ hφ₃).symm.trans hLP.symm))
  have himageColumn : IsCenterColumn L η
      (Tiling.Approximation.deformPoint φ '' p.column) := heq ▸ hL'col
  obtain ⟨t, ht⟩ := hcolumnPart
  obtain ⟨C, htC⟩ := Set.mem_iUnion.mp ht
  have hCsubset : C.1.centres ⊆ T := component_centres_subset C.1
  have hCimage := hLcols C.1.centres hCsubset C.property
  have hCimagesub : Tiling.Approximation.deformPoint φ '' C.1.centres ⊆
      Tiling.Approximation.deformPoint φ '' T := Set.image_mono hCsubset
  exact ⟨L, hLP, hLrat, hLtiles,
    nonempty_columnPart_of_columnSubset hδ hLtiles.2.1 hCimagesub hCimage,
    himageColumn⟩

private theorem bounded_joint_columnDeformation
    (K : PolygonalRegion) (T : Set Plane) (δ η : Submodule ℝ Plane)
    (hK : HasRationalSlopes K) (hδ : Module.finrank ℝ δ = 1)
    (hη : Module.finrank ℝ η = 1) (hbδ : HasBoundaryDirection K δ)
    (hbη : HasBoundaryDirection K η) (hT : TilesOn K T Set.univ)
    (hquake : HasNontrivialEarthquakeDecomposition K δ T)
    (hcolumnPart : (columnPart K δ T).Nonempty) (p : PersistentColumnData K T η) :
    ∃ P : Approximation.PolyhedralCode, Approximation.polyhedralSupport P = K.support ∧
      ∃ B : ℝ, 0 < B ∧ ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, Tiling.Approximation.IsFiniteApproximation F ε φ →
          ∃ L : PolygonalRegion,
            L.support = Approximation.deformedPolyhedralSupport P φ ∧
            L.support ⊆ Metric.closedBall 0 B ∧ Tiling.IsRational L.support ∧
            TilesOn L (Tiling.Approximation.deformPoint φ '' T) Set.univ ∧
            (columnPart L δ (Tiling.Approximation.deformPoint φ '' T)).Nonempty ∧
            IsCenterColumn L η (Tiling.Approximation.deformPoint φ '' p.column) := by
  classical
  obtain ⟨P, hP, F₁, ε₁, hε₁, hLTFT⟩ :=
    joint_columnDeformation K T δ η hK hδ hη hbδ hbη hT hquake hcolumnPart p
  obtain ⟨Q, hQ, W, hW, hzero, B, R, hB, hR, F₂, ε₂, hε₂, hbound⟩ :=
    Approximation.rationalPolygon_uniformBoundaryControl K hK
  obtain ⟨F₃, ε₃, hε₃, hcodes⟩ :=
    Approximation.polyhedralDeformation_independentOfCode K P Q hP hQ
  let F := F₁ ∪ F₂ ∪ F₃
  let ε := min ε₁ (min ε₂ ε₃)
  refine ⟨P, hP, B, hB, F, ε, lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro φ hφ
  have hφ₁ := Tiling.Approximation.finiteApproximation_strengthen F₁ F ε₁ ε φ
    (by dsimp [F]; exact Finset.subset_union_left.trans Finset.subset_union_left)
    (min_le_left _ _) hφ
  have hφ₂ := Tiling.Approximation.finiteApproximation_strengthen F₂ F ε₂ ε φ
    (by dsimp [F]; exact Finset.subset_union_right.trans Finset.subset_union_left)
    ((min_le_right _ _).trans (min_le_left _ _)) hφ
  have hφ₃ := Tiling.Approximation.finiteApproximation_strengthen F₃ F ε₃ ε φ
    (by dsimp [F]; exact Finset.subset_union_right)
    ((min_le_right _ _).trans (min_le_right _ _)) hφ
  obtain ⟨L, hLP, hLrat, hLtiles, hLcols, hLimage⟩ := hLTFT φ hφ₁
  obtain ⟨L', hLQ, hLbound, _, _⟩ := hbound φ hφ₂
  have heq : L' = L := polygonalRegion_eq_of_support_eq
    (hLQ.trans ((hcodes φ hφ₃).symm.trans hLP.symm))
  exact ⟨L, hLP, heq ▸ hLbound, hLrat, hLtiles, hLcols, hLimage⟩

private theorem rational_columnPart_periodic
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hK : Tiling.RationalPolygonal.IsRelativelyRational K)
    (hδ : Module.finrank ℝ δ = 1) (hrat : HasRationalDirection δ)
    (hT : TilesOn K T Set.univ) :
    IsLatticePeriodic (regularSupport K (columnPart K δ T)) := by
  obtain ⟨v, hv⟩ := rational_wholePlane_commonCarrierPeriod K δ T hK hδ hrat hT
  exact invariantCarrier_lattice_of_transversePeriod _ δ v hδ hv.1
    (columnPart_carrier_invariant K δ T) hv.2.1

private theorem invariant_split_nontrivial
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T A : Set Plane)
    (hδ : Module.finrank ℝ δ = 1) (hT : TilesOn K T Set.univ)
    (hAT : A ⊆ T) (hA : A.Nonempty) (hnotA : (T \ A).Nonempty)
    (hInv : IsInvariantAlong (regularSupport K A) δ) :
    HasNontrivialEarthquakeDecomposition K δ T := by
  classical
  have hTInv : IsInvariantAlong (regularSupport K T) δ := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) hT]
    intro u hu
    ext x
    simp
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hnotA
  let P : EarthquakeComponent K δ T :=
    (earthquakeGraph K δ T).connectedComponentMk ⟨a, hAT ha⟩
  let Q : EarthquakeComponent K δ T :=
    (earthquakeGraph K δ T).connectedComponentMk ⟨b, hb.1⟩
  have haP : a ∈ P.centres := ⟨⟨a, hAT ha⟩, by simp [P], rfl⟩
  have hPA : P.centres ⊆ A := by
    obtain hd | hsub := invariantSubfamily_isUnionComponents
      K δ T A hδ hT.2.1 hTInv hAT hInv P
    · exact False.elim (Set.disjoint_left.mp hd haP ha)
    · exact hsub
  have hbQ : b ∈ Q.centres := ⟨⟨b, hb.1⟩, by simp [Q], rfl⟩
  exact Or.inr ⟨P, Q, fun h => hb.2 (hPA (h ▸ hbQ))⟩

private theorem shifted_properPiece_nontrivial
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T Q : Set Plane) (a : Plane)
    (hδ : Module.finrank ℝ δ = 1) (hT : TilesOn K T Set.univ)
    (hQsub : Q ⊆ a +ᵥ T) (hQne : Q.Nonempty)
    (hQproper : regularSupport K Q ≠ Set.univ)
    (hQinv : IsInvariantAlong (regularSupport K Q) δ) :
    HasNontrivialEarthquakeDecomposition K δ T := by
  have hQT : (-a) +ᵥ Q ⊆ T := by
    rintro x ⟨q, hq, rfl⟩
    obtain ⟨t, ht, hqt⟩ := Set.mem_vadd_set.mp (hQsub hq)
    have heq : (-a) +ᵥ q = t := by rw [← hqt]; simp
    change (-a) +ᵥ q ∈ T
    rw [heq]
    exact ht
  have hAne : ((-a) +ᵥ Q).Nonempty := hQne.image (fun q => (-a) +ᵥ q)
  have hAproper : (-a) +ᵥ Q ≠ T := by
    intro heq
    have hcarrier : (-a) +ᵥ regularSupport K Q = (Set.univ : Set Plane) := by
      rw [← regularSupport_vadd, heq]
      exact regularSupport_eq_of_tilesOn isOpen_univ (by simp) hT
    have hshift := congrArg (fun E : Set Plane => a +ᵥ E) hcarrier
    exact hQproper (by
      simpa only [vadd_vadd, add_neg_cancel, zero_vadd, Set.vadd_set_univ] using hshift)
  have hcomplement : (T \ ((-a) +ᵥ Q)).Nonempty := by
    apply Set.sdiff_nonempty.mpr
    intro hTA
    exact hAproper (Set.Subset.antisymm hQT hTA)
  have hAinv : IsInvariantAlong (regularSupport K ((-a) +ᵥ Q)) δ := by
    rw [regularSupport_vadd]
    intro u hu
    rw [vadd_vadd, add_comm u (-a), ← vadd_vadd, hQinv u hu]
  exact invariant_split_nontrivial K δ T ((-a) +ᵥ Q) hδ hT hQT hAne hcomplement hAinv

/-- Once a nonempty proper fixed-carrier piece has been retained, the bounded
correction does not lose nontriviality in the original full tiling. -/
private theorem corrected_limit_piece_nontrivial
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (S P T Q : Set Plane)
    (ℓ : ℕ → Plane) (a : Plane) (hδ : Module.finrank ℝ δ = 1)
    (hT : TilesOn K T Set.univ) (hPS : P ⊆ S)
    (hpiece : Tiling.Topology.LocallyFellConverges (fun n => ℓ n +ᵥ P) Q)
    (hfull : Tiling.Topology.LocallyFellConverges (fun n => ℓ n +ᵥ S) (a +ᵥ T))
    (hQne : Q.Nonempty) (hQproper : regularSupport K Q ≠ Set.univ)
    (hQinv : IsInvariantAlong (regularSupport K Q) δ) :
    HasNontrivialEarthquakeDecomposition K δ T := by
  have hQT := corrected_piece_subset_original ℓ a hPS hpiece hfull
  have hAne : ((-a) +ᵥ Q).Nonempty := by
    obtain ⟨q, hq⟩ := hQne
    exact ⟨-a + q, Set.mem_vadd_set.mpr ⟨q, hq, rfl⟩⟩
  have hAproper : (-a) +ᵥ Q ≠ T := by
    intro heq
    have hcarrier : (-a) +ᵥ regularSupport K Q = (Set.univ : Set Plane) := by
      rw [← regularSupport_vadd, heq]
      exact regularSupport_eq_of_tilesOn isOpen_univ (by simp) hT
    have hshift := congrArg (fun E : Set Plane => a +ᵥ E) hcarrier
    have hQfull : regularSupport K Q = Set.univ := by
      simpa only [vadd_vadd, add_neg_cancel, zero_vadd, Set.vadd_set_univ] using hshift
    exact hQproper hQfull
  have hcomplement : (T \ ((-a) +ᵥ Q)).Nonempty := by
    apply Set.sdiff_nonempty.mpr
    intro hTA
    exact hAproper (Set.Subset.antisymm hQT hTA)
  have hAinv : IsInvariantAlong (regularSupport K ((-a) +ᵥ Q)) δ := by
    rw [regularSupport_vadd]
    intro u hu
    rw [vadd_vadd, add_comm u (-a), ← vadd_vadd, hQinv u hu]
  exact invariant_split_nontrivial K δ T ((-a) +ᵥ Q) hδ hT hQT hAne hcomplement hAinv

/-- Lattice-normalized subfamily compactness keeps the bounded correction
in the FULL limit and returns actual shared normalized shifts, not a certificate. -/
private theorem fixedCarrier_limit
    {K : PolygonalRegion} {T C U : Set Plane} {g : ℕ → Plane}
    (hT : TilesOn K T Set.univ) (hCT : C ⊆ T)
    (hEperiodic : IsLatticePeriodic (regularSupport K C))
    (hconv : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) U) :
    ∃ (a : Plane) (V : Set Plane) (ell : ℕ → Plane),
      Tiling.Topology.LocallyFellConverges (fun n => ell n +ᵥ C) V ∧
      Tiling.Topology.LocallyFellConverges (fun n => ell n +ᵥ T) (a +ᵥ U) ∧
      TilesOn K V (regularSupport K C) ∧ V ⊆ a +ᵥ U := by
  classical
  let E : Set Plane := regularSupport K C
  have hCpack : IsPacking K.prototileFamily (K.placements C) := hT.2.1.mono (fun _ h => hCT h)
  have hCtiles : TilesOn K C E := tilesOn_regularSupport_of_packing hCpack
  obtain ⟨L, hL⟩ := hEperiodic
  obtain ⟨R, _, hrepresentative⟩ := planarLattice_boundedCosetRepresentative L
  choose ell hell using fun n => hrepresentative (g n)
  let d : ℕ → Plane := fun n => ell n - g n
  have hdBound : ∀ n, d n ∈ Metric.closedBall (0 : Plane) R := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa [d, norm_sub_rev] using (hell n).2
  obtain ⟨a, _, φ, hφ, hdlim⟩ :=
    (isCompact_closedBall (0 : Plane) R).tendsto_subseq hdBound
  have hcorrected := Tiling.Topology.locallyFell_translate
    (locallyFell_subsequence hconv φ hφ) hdlim
  have hcorrectedEq :
      (fun n => (d ∘ φ) n +ᵥ ((fun n => g n +ᵥ T) ∘ φ) n) =
        (fun n => ell (φ n) +ᵥ T) := by
    funext n
    simp only [d, Function.comp_apply, vadd_vadd, sub_add_cancel]
  rw [hcorrectedEq] at hcorrected
  have hperiod : ∀ n, ell (φ n) +ᵥ E = E := by
    intro n
    exact hL (hell (φ n)).1
  have htilesCseq : ∀ n, TilesOn K (ell (φ n) +ᵥ C) E := by
    intro n
    simpa only [hperiod n] using tilesOn_translate hCtiles (ell (φ n))
  obtain ⟨ε, hε, hseparation⟩ := exists_packingSeparation K
  obtain ⟨ψ, V, hψ, _, _, hCconv⟩ :=
    Tiling.Topology.exists_locallyFellConvergent_subsequence ε hε
      (fun n => ell (φ n) +ᵥ C)
      (fun n => (packing_centres_locallyFinite (htilesCseq n).2.1).2.2)
      (fun n => hseparation _ (htilesCseq n).2.1)
  have hfull := locallyFell_subsequence hcorrected ψ hψ
  have hVsub : V ⊆ a +ᵥ U := locallyFell_limit_mono hCconv hfull
    (fun _ => Set.vadd_set_mono hCT)
  exact ⟨a, V, fun n => ell (φ (ψ n)), hCconv, hfull,
    tilesOn_isClosed (fun n => htilesCseq (ψ n)) hCconv, hVsub⟩

/-- The original U is fixed throughout: a surviving aggregate column is
translated back from the normalized full limit `a +ᵥ U`. -/
private theorem periodicColumnAggregate_survives_sameLimit
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T C U : Set Plane} {g : ℕ → Plane}
    (hδ : Module.finrank ℝ δ = 1) (hT : TilesOn K T Set.univ)
    (hCT : C ⊆ T) (hCne : C.Nonempty) (hCcol : IsUnionOfColumns K δ C)
    (hEperiodic : IsLatticePeriodic (regularSupport K C))
    (hconv : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) U) :
    ∃ D ⊆ U, IsCenterColumn K δ D := by
  obtain ⟨a, V, ell, hpiece, _, hVtiles, hVsub⟩ := fixedCarrier_limit hT hCT hEperiodic hconv
  have hCpack : IsPacking K.prototileFamily (K.placements C) := hT.2.1.mono (fun _ h => hCT h)
  have hVcol : IsUnionOfColumns K δ V := unionColumns_closedUnderLimits hδ
    (fun n => (tilesOn_translate (tilesOn_regularSupport_of_packing hCpack) (ell n)).2.1)
    (fun n => unionColumns_vadd hCcol (ell n)) hpiece
  have hVE : regularSupport K V = regularSupport K C := regularSupport_eq_of_tilesOn
    (regularSupport_isRegularOpen K C).1 (regularSupport_isRegularOpen K C).2 hVtiles
  have hVne : V.Nonempty := by
    by_contra h
    have hempty : V = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hEempty : regularSupport K C = ∅ := by
      rw [← hVE, hempty]
      simp [regularSupport, openUnion]
    exact (regularSupport_nonempty_of_nonempty K hCne).ne_empty hEempty
  obtain ⟨t, ht⟩ := hVne
  let D := lineFibre δ V t
  have hDcol : IsCenterColumn K δ D := hVcol t ht
  have hDsub : (-a) +ᵥ D ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hzU, hz⟩ := Set.mem_vadd_set.mp (hVsub hy.1)
    have heq : (-a) +ᵥ y = z := by rw [← hz]; simp
    change (-a) +ᵥ y ∈ U
    rw [heq]
    exact hzU
  exact ⟨(-a) +ᵥ D, hDsub, centerColumn_vadd hDcol (-a)⟩

/-- After a genuine finite deformation has produced the exact image column,
both directions are retained in one full orbit limit. -/
private theorem persistent_deformation_simultaneousColumns
    {K L : PolygonalRegion} {T : Set Plane} {δ η : Submodule ℝ Plane}
    (p : PersistentColumnData K T η) (φ : ℝ →ₗ[ℚ] ℚ)
    (hδ : Module.finrank ℝ δ = 1) (hratδ : HasRationalDirection δ)
    (hLrat : Tiling.RationalPolygonal.IsRelativelyRational L)
    (hLT : TilesOn L (Tiling.Approximation.deformPoint φ '' T) Set.univ)
    (hδne : (columnPart L δ (Tiling.Approximation.deformPoint φ '' T)).Nonempty)
    (himageColumn : IsCenterColumn L η
      (Tiling.Approximation.deformPoint φ '' p.column)) :
    ∃ U C D : Set Plane, TilesOn L U Set.univ ∧ C ⊆ U ∧ D ⊆ U ∧
      IsCenterColumn L δ C ∧ IsCenterColumn L η D := by
  let g : ℕ → Plane := fun n => Tiling.Approximation.deformPoint φ p.anchor -
    Tiling.Approximation.deformPoint φ (p.movingCentre n)
  obtain ⟨ι, U, hι, hconv⟩ := translatedTiling_subsequenceExists L
    (Tiling.Approximation.deformPoint φ '' T) g hLT
  let p' : PersistentColumnData K T η :=
    { p with
      movingCentre := p.movingCentre ∘ ι
      movingCentre_mem_source := fun n => p.movingCentre_mem_source (ι n)
      converges := locallyFell_subsequence p.converges ι hι
      persistent := fun u hu => hι.tendsto_atTop.eventually (p.persistent u hu) }
  have hDsub : Tiling.Approximation.deformPoint φ '' p.column ⊆ U :=
    persistent_linearImage_subset_limit p' φ U hconv
  have hU : TilesOn L U Set.univ := by
    apply tilesOn_isClosed (fun n => ?_) hconv
    simpa using tilesOn_translate hLT (g (ι n))
  obtain ⟨C, hCU, hCcol⟩ := periodicColumnAggregate_survives_sameLimit hδ hLT
    (columnPart_subset L δ _) hδne
    (columnPart_isUnionColumns L δ _ hδ hLT.2.1)
    (rational_columnPart_periodic L δ _ hLrat hδ hratδ hLT) hconv
  exact ⟨U, C, Tiling.Approximation.deformPoint φ '' p.column,
    hU, hCU, hDsub, hCcol, himageColumn⟩

/-- The actual eventual-persistent part contains the fixed anchor and omits
the moving-centre limit, so NF gives a genuinely nontrivial decomposition. -/
private theorem nonFLC_nontrivialWholePlaneHullWitness
    (K : PolygonalRegion) (T : Set Plane)
    (hT : TilesOn K T Set.univ) (hnotFLC : ¬HasFLC T) :
    ∃ (S : Set Plane) (g : ℕ → Plane) (δ : Submodule ℝ Plane),
      Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S ∧
      TilesOn K S Set.univ ∧ Module.finrank ℝ δ = 1 ∧
      HasBoundaryDirection K δ ∧ HasNontrivialEarthquakeDecomposition K δ S := by
  obtain ⟨S, t, s, moving, g, _, hsource, hanchor, hconv, hs, hne, hlim, hstab⟩ :=
    nonFLC_anchoredWholePlaneLimit K T hT hnotFLC
  have htilesn : ∀ n, TilesOn K (g n +ᵥ T) Set.univ := by
    intro n
    simpa using tilesOn_translate hT (g n)
  have hS := tilesOn_isClosed htilesn hconv
  have htS : t ∈ S := Tiling.Topology.mem_of_locallyFellConverges_of_tendsto_mem
    hconv hanchor tendsto_const_nhds
  have hmoving : ∀ n, moving n + g n ∈ g n +ᵥ T := by
    intro n
    exact Set.mem_vadd_set.mpr ⟨moving n, hsource n, by simp [add_comm]⟩
  obtain ⟨ρ, hρ, hsep⟩ := exists_packingSeparation K
  have hsmall : ∀ᶠ n in atTop, dist (moving n + g n) s < ρ := by
    have hc : Tendsto (fun n => dist (moving n + g n) s) atTop (𝓝 (0 : ℝ)) := by
      simpa using hlim.dist (tendsto_const_nhds (x := s))
    exact hc.eventually (gt_mem_nhds hρ)
  have htransient : ∀ᶠ n in atTop, s ∉ g n +ᵥ T := by
    filter_upwards [hsmall] with n hn hs'
    exact (not_lt_of_ge (hsep _ (htilesn n).2.1 (hmoving n) hs' (hne n))) hn
  let A : Set Plane := {u | u ∈ S ∧ ∀ᶠ n in atTop, u ∈ g n +ᵥ T}
  have hA : A.Nonempty := ⟨t, htS, Filter.Eventually.of_forall hanchor⟩
  have hsnotA : s ∉ A := by
    intro hsA
    obtain ⟨n, hnmem, hnnot⟩ := (hsA.2.and htransient).exists
    exact hnnot hnmem
  have hnotA : (S \ A).Nonempty := ⟨s, hs, hsnotA⟩
  obtain ⟨δ, hδ, hbδ, hInv, _⟩ :=
    stabilizedWholePlaneLimit_earthquake K T S A g hT hconv rfl hstab hA hnotA
  exact ⟨S, g, δ, hconv, hS, hδ, hbδ,
    invariant_split_nontrivial K δ S A hδ hS (fun _ hu => hu.1) hA hnotA hInv⟩

private theorem plane_mem_aePeriodGroup_univ (u : Plane) :
    u ∈ aePeriodGroup (Set.univ : Set Plane) := by
  simp [aePeriodGroup]

private theorem tilingSpace_translate_centres {K : PolygonalRegion}
    {E : Set Plane} (g : aePeriodGroup E) (T : TilingSpace K E) :
    ((TilingSpace.translate g T).centres : Set Plane) =
      (g : Plane) +ᵥ (T.centres : Set Plane) := by
  change (fun x : Plane => x + (g : Plane)) '' (T.centres : Set Plane) =
    (g : Plane) +ᵥ (T.centres : Set Plane)
  ext x
  simp only [mem_image, mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, add_comm _ _⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, add_comm _ _⟩

private theorem translated_limits_transitive
    {K : PolygonalRegion} {T S U : Set Plane} {g h : ℕ → Plane}
    (hT : TilesOn K T Set.univ)
    (hTS : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S)
    (hSU : Tiling.Topology.LocallyFellConverges (fun n => h n +ᵥ S) U) :
    ∃ f : ℕ → Plane, Tiling.Topology.LocallyFellConverges (fun n => f n +ᵥ T) U := by
  classical
  have hTseq : ∀ n, TilesOn K (g n +ᵥ T) Set.univ := by
    intro n
    simpa using tilesOn_translate hT (g n)
  have hS : TilesOn K S Set.univ := tilesOn_isClosed hTseq hTS
  have hSseq : ∀ n, TilesOn K (h n +ᵥ S) Set.univ := by
    intro n
    simpa using tilesOn_translate hS (h n)
  have hU : TilesOn K U Set.univ := tilesOn_isClosed hSseq hSU
  let T₀ : TilingSpace K Set.univ :=
    ⟨⟨T, (packing_centres_locallyFinite hT.2.1).2.2⟩, hT⟩
  let S₀ : TilingSpace K Set.univ :=
    ⟨⟨S, (packing_centres_locallyFinite hS.2.1).2.2⟩, hS⟩
  let U₀ : TilingSpace K Set.univ :=
    ⟨⟨U, (packing_centres_locallyFinite hU.2.1).2.2⟩, hU⟩
  let pg : ℕ → aePeriodGroup (Set.univ : Set Plane) :=
    fun n => ⟨g n, plane_mem_aePeriodGroup_univ (g n)⟩
  have hTspaceConv : Tendsto (fun n => TilingSpace.translate (pg n) T₀) atTop (𝓝 S₀) := by
    apply (locallyFell_metrizable K Set.univ (fun n => TilingSpace.translate (pg n) T₀) S₀).2
    simpa only [tilingSpace_translate_centres, pg, T₀, S₀,
      TopologicalSpace.Closeds.coe_mk] using hTS
  have hS₀orbit : S₀ ∈ orbitHull T₀ :=
    isClosed_closure.mem_of_tendsto hTspaceConv
      (Eventually.of_forall fun n => subset_closure ⟨pg n, rfl⟩)
  let ph : ℕ → aePeriodGroup (Set.univ : Set Plane) :=
    fun n => ⟨h n, plane_mem_aePeriodGroup_univ (h n)⟩
  have hSspaceConv : Tendsto (fun n => TilingSpace.translate (ph n) S₀) atTop (𝓝 U₀) := by
    apply (locallyFell_metrizable K Set.univ (fun n => TilingSpace.translate (ph n) S₀) U₀).2
    simpa only [tilingSpace_translate_centres, ph, S₀, U₀,
      TopologicalSpace.Closeds.coe_mk] using hSU
  have hU₀orbitS : U₀ ∈ orbitHull S₀ :=
    isClosed_closure.mem_of_tendsto hSspaceConv
      (Eventually.of_forall fun n => subset_closure ⟨ph n, rfl⟩)
  have horbitSubset : orbitHull S₀ ⊆ orbitHull T₀ := by
    apply closure_minimal
    · rintro V ⟨a, rfl⟩
      have hm : TilingSpace.translate a S₀ ∈ TilingSpace.translate a '' orbitHull T₀ :=
        ⟨S₀, hS₀orbit, rfl⟩
      rwa [(orbitHull_compact T₀).2.2 a] at hm
    · exact isClosed_closure
  have hU₀orbitT : U₀ ∈ orbitHull T₀ := horbitSubset hU₀orbitS
  obtain ⟨V, hV, hlim⟩ := mem_closure_iff_seq_limit.mp hU₀orbitT
  choose q hq using hV
  let f : ℕ → Plane := fun n => (q n : Plane)
  have hVeq : (fun n => TilingSpace.translate (q n) T₀) = V := by
    funext n
    exact hq n
  have hconv := (locallyFell_metrizable K Set.univ
    (fun n => TilingSpace.translate (q n) T₀) U₀).mp (hVeq.symm ▸ hlim)
  refine ⟨f, ?_⟩
  simpa only [tilingSpace_translate_centres, f, T₀, U₀,
    TopologicalSpace.Closeds.coe_mk] using hconv

/-- A positive transverse segment in the closure of an invariant open set
meets that open set. No segment length is bounded away from zero. -/
private theorem transverse_segment_meets_invariant_open
    (D : Set Plane) (α η : Submodule ℝ Plane) (a b : Plane)
    (_hDopen : IsOpen D) (hDinv : IsInvariantAlong D α)
    (hα : Module.finrank ℝ α = 1) (hη : Module.finrank ℝ η = 1)
    (hratα : HasRationalDirection α) (hne : α ≠ η)
    (hab : a ≠ b) (habη : b - a ∈ η)
    (hseg : openSegment ℝ a b ⊆ closure D) :
    (openSegment ℝ a b ∩ D).Nonempty := by
  obtain ⟨n, hn⟩ := Approximation.rationalDirection_hasNormal α hα hratα
  let ψ : Plane →L[ℝ] ℝ := (n.x : ℝ) • Complex.reCLM + (n.y : ℝ) • Complex.imCLM
  have hker : LinearMap.ker ψ.toLinearMap = α := by
    simpa only [Tiling.Approximation.normalDirection, ψ] using hn
  have hba0 : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hbaNot : b - a ∉ α := by
    intro hmem
    exact hne ((eq_span_singleton_of_mem_of_finrank_eq_one hα hmem hba0).trans
      (eq_span_singleton_of_mem_of_finrank_eq_one hη habη hba0).symm)
  have hψne : ψ a ≠ ψ b := by
    intro heq
    apply hbaNot
    rw [← hker, LinearMap.mem_ker]
    change ψ (b - a) = 0
    rw [map_sub, heq, sub_self]
  let E : Set Plane := ψ ⁻¹' openSegment ℝ (ψ a) (ψ b)
  have hEopen : IsOpen E := by
    dsimp [E]
    rw [openSegment_eq_Ioo' hψne]
    exact isOpen_Ioo.preimage ψ.continuous
  have hmid : midpoint ℝ a b ∈ E := by
    change ψ.toLinearMap.toAffineMap (midpoint ℝ a b) ∈
      openSegment ℝ (ψ.toLinearMap.toAffineMap a) (ψ.toLinearMap.toAffineMap b)
    rw [← image_openSegment ℝ ψ.toLinearMap.toAffineMap a b]
    exact Set.mem_image_of_mem _ (midpoint_mem_openSegment (𝕜 := ℝ) a b)
  obtain ⟨y, hyE, hyD⟩ := mem_closure_iff.mp
    (hseg (midpoint_mem_openSegment (𝕜 := ℝ) a b)) E hEopen hmid
  have hyimage : ψ y ∈ ψ.toLinearMap.toAffineMap '' openSegment ℝ a b := by
    rw [image_openSegment]
    exact hyE
  obtain ⟨p, hpseg, hψp⟩ := hyimage
  have hpyα : p - y ∈ α := by
    rw [← hker, LinearMap.mem_ker]
    change ψ (p - y) = 0
    rw [map_sub]
    change ψ p = ψ y at hψp
    rw [hψp, sub_self]
  have hpD : p ∈ D := by
    rw [← hDinv (p - y) hpyα]
    exact Set.mem_vadd_set.mpr ⟨y, hyD, by change (p - y) + y = p; abel⟩
  exact ⟨p, hpseg, hpD⟩

/-- A finite positive transverse contact meets an actual tile interior of
the invariant subfamily, by regular-closedness and two density steps. -/
private theorem transverse_contact_meets_persistent_tile
    (K : PolygonalRegion) (A : Set Plane) (α η : Submodule ℝ Plane) (s t : Plane)
    (htA : t ∈ A) (hα : Module.finrank ℝ α = 1) (hη : Module.finrank ℝ η = 1)
    (hratα : HasRationalDirection α) (hne : α ≠ η)
    (hInv : IsInvariantAlong (regularSupport K A) α)
    (hcontact : ProperEdgeContactAlong K η s t) :
    ∃ c ∈ A, ((c +ᵥ K.openCarrier) ∩ (s +ᵥ K.openCarrier)).Nonempty := by
  have hUopen : IsOpen (openUnion K A) := by
    apply isOpen_iUnion
    intro c
    exact (Homeomorph.addLeft (c : Plane)).isOpenMap _ isOpen_interior
  have hUsub : openUnion K A ⊆ regularSupport K A :=
    interior_maximal subset_closure hUopen
  have htileOpen : t +ᵥ K.openCarrier ⊆ regularSupport K A := by
    intro x hx
    exact hUsub (Set.mem_iUnion.mpr ⟨⟨t, htA⟩, hx⟩)
  have htileClosed : t +ᵥ K.support ⊆ closure (regularSupport K A) := by
    have htregular : closure (t +ᵥ K.openCarrier) = t +ᵥ K.support := by
      rw [closure_vadd]
      exact congrArg (fun X : Set Plane => t +ᵥ X) K.isPolygonal.closure_interior
    rw [← htregular]
    exact closure_mono htileOpen
  obtain ⟨a, b, hab, habη, hseg⟩ := hcontact
  have hclosedt : IsClosed (t +ᵥ K.support) :=
    (Homeomorph.addLeft t).isClosed_image.mpr K.isPolygonal.isCompact.isClosed
  have hcloseds : IsClosed (s +ᵥ K.support) :=
    (Homeomorph.addLeft s).isClosed_image.mpr K.isPolygonal.isCompact.isClosed
  obtain ⟨p, hpseg, hpD⟩ := transverse_segment_meets_invariant_open
    (regularSupport K A) α η a b (regularSupport_isRegularOpen K A).1 hInv
      hα hη hratα hne hab habη
      (fun x hx => htileClosed (hclosedt.frontier_subset (hseg hx).2))
  have hpclosed : p ∈ closure (s +ᵥ K.openCarrier) := by
    rw [closure_vadd]
    change p ∈ s +ᵥ closure (interior K.support)
    rw [K.isPolygonal.closure_interior]
    exact hcloseds.frontier_subset (hseg hpseg).1
  obtain ⟨q, hqD, hqTile⟩ := mem_closure_iff.mp hpclosed (regularSupport K A)
    (regularSupport_isRegularOpen K A).1 hpD
  have hqClosure : q ∈ closure (openUnion K A) := interior_subset hqD
  have hOopen : IsOpen ((regularSupport K A) ∩ (s +ᵥ K.openCarrier)) :=
    (regularSupport_isRegularOpen K A).1.inter
      ((Homeomorph.addLeft s).isOpenMap _ isOpen_interior)
  obtain ⟨x, hxO, hxUnion⟩ := mem_closure_iff.mp hqClosure
    ((regularSupport K A) ∩ (s +ᵥ K.openCarrier)) hOopen ⟨hqD, hqTile⟩
  obtain ⟨c, hxc⟩ := Set.mem_iUnion.mp hxUnion
  exact ⟨c, c.property, x, hxc, hxO.2⟩

private theorem properContact_vadd (K : PolygonalRegion) (η : Submodule ℝ Plane)
    (s t g : Plane) (hcontact : ProperEdgeContactAlong K η s t) :
    ProperEdgeContactAlong K η (g + s) (g + t) := by
  obtain ⟨a, b, hab, habη, hseg⟩ := hcontact
  refine ⟨g + a, g + b, fun h => hab (add_left_cancel h), ?_, ?_⟩
  · convert habη using 1
    abel
  · intro x hx
    rw [← openSegment_translate_image ℝ g a b] at hx
    obtain ⟨y, hy, heq⟩ := hx
    obtain ⟨hys, hyt⟩ := hseg hy
    rw [← heq]
    constructor
    · rw [← vadd_vadd]
      change g + y ∈ frontier ((Homeomorph.addLeft g) '' (s +ᵥ K.support))
      rw [← (Homeomorph.addLeft g).image_frontier]
      exact ⟨y, hys, rfl⟩
    · rw [← vadd_vadd]
      change g + y ∈ frontier ((Homeomorph.addLeft g) '' (t +ᵥ K.support))
      rw [← (Homeomorph.addLeft g).image_frontier]
      exact ⟨y, hyt, rfl⟩

/-- A fixed bounded patch of persistent centres suffices for every late
finite contact, even when the positive contact lengths tend to zero. -/
private theorem persistent_contacts_force_direction
    (K : PolygonalRegion) (A : Set Plane) (Tn : ℕ → Set Plane)
    (α η : Submodule ℝ Plane) (t r : Plane) (sn : ℕ → Plane)
    (htA : t ∈ A) (hpackA : IsPacking K.prototileFamily (K.placements A))
    (hpackn : ∀ n, IsPacking K.prototileFamily (K.placements (Tn n)))
    (hpersistent : ∀ a ∈ A, ∀ᶠ n in atTop, a ∈ Tn n)
    (hsn : ∀ n, sn n ∈ Tn n) (hlim : Tendsto sn atTop (𝓝 r)) (hrNot : r ∉ A)
    (hα : Module.finrank ℝ α = 1) (hη : Module.finrank ℝ η = 1)
    (hratα : HasRationalDirection α)
    (hInv : IsInvariantAlong (regularSupport K A) α)
    (hcontact : ∀ n, ProperEdgeContactAlong K η (sn n) t) : α = η := by
  classical
  by_contra hne
  obtain ⟨R, hR, hKR⟩ := K.isPolygonal.isCompact.isBounded.subset_closedBall_lt 0 0
  let Q : Set Plane := A ∩ Metric.closedBall r (1 + 2 * R)
  have hQfinite : Q.Finite := (packing_centres_locallyFinite hpackA).1 _
    Metric.isBounded_closedBall
  have hpatch : ∀ᶠ n in atTop, ∀ a ∈ Q, a ∈ Tn n :=
    hQfinite.eventually_all.mpr (fun a ha => hpersistent a ha.1)
  have hnear : ∀ᶠ n in atTop, dist (sn n) r < 1 :=
    hlim.eventually (Metric.ball_mem_nhds r zero_lt_one)
  have hnotA : ∀ᶠ n in atTop, sn n ∉ A :=
    hlim.eventually ((packing_centres_locallyFinite hpackA).2.2.isOpen_compl.mem_nhds hrNot)
  obtain ⟨n, hnpatch, hnnear, hnnot⟩ := (hpatch.and (hnear.and hnotA)).exists
  obtain ⟨c, hcA, x, hxc, hxs⟩ := transverse_contact_meets_persistent_tile
    K A α η (sn n) t htA hα hη hratα hne hInv (hcontact n)
  obtain ⟨u, hu, hcu⟩ := Set.mem_vadd_set.mp hxc
  obtain ⟨v, hv, hsv⟩ := Set.mem_vadd_set.mp hxs
  have hdiff : c - sn n = v - u := by
    change c + u = x at hcu
    change sn n + v = x at hsv
    rw [← hcu] at hsv
    calc
      c - sn n = (c + u) - (sn n + u) := by abel
      _ = (sn n + v) - (sn n + u) := by rw [hsv]
      _ = v - u := by abel
  have huc : ‖u‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hKR (interior_subset hu)
  have hvc : ‖v‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hKR (interior_subset hv)
  have hcs : dist c (sn n) ≤ 2 * R := by
    rw [dist_eq_norm, hdiff]
    exact (norm_sub_le v u).trans (by linarith)
  have hcQ : c ∈ Q := by
    refine ⟨hcA, ?_⟩
    rw [Metric.mem_closedBall]
    exact (dist_triangle c (sn n) r).trans (by linarith)
  have hcsne : c ≠ sn n := fun heq => hnnot (heq ▸ hcA)
  have hdisjoint := (isPacking_iff_openCarrier_disjoint K (Tn n)).mp (hpackn n)
    (hnpatch c hcQ) (hsn n) hcsne
  exact Set.disjoint_left.mp hdisjoint hxc hxs

theorem nonReady_pairLimit_readyOrPersistentColumn :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    HasRationalSlopes K → Module.finrank ℝ δ = 1 → HasBoundaryDirection K δ →
    TilesOn K T Set.univ → HasNontrivialEarthquakeDecomposition K δ T →
    ¬IsUniformlyReady K δ T →
      ∃ η : Submodule ℝ Plane, Module.finrank ℝ η = 1 ∧
        HasBoundaryDirection K η ∧ δ ≠ η ∧
        ((∃ (S : Set Plane) (g : ℕ → Plane),
          Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S ∧
          IsUniformlyReady K η S ∧ HasNontrivialEarthquakeDecomposition K η S) ∨
            Nonempty (PersistentColumnData K T η))
  := by
  intro K δ T hK hδ hbδ hT hquake hnotReady
  obtain ⟨_, _, _, η, hη, hbη, hηne, hinfinite⟩ :=
    nonReady_characterization K δ T hK hδ hbδ hT hquake hnotReady
  obtain ⟨tn, sn, d, hcontacts, hinj, hdisp⟩ :=
    infiniteContacts_pairedConvergentSequence K η T hinfinite
  let g : ℕ → Plane := fun n => tn 0 - tn n
  let h : ℕ → Plane := fun n => sn 0 - sn n
  obtain ⟨ι, S, U, hι, hS, hU, hstabS, hstabU⟩ :=
    pairedLimits_commonStabilizedSubsequence K T g h hT
  have hdiff : Tendsto (fun n => h (ι n) - g (ι n)) atTop
      (𝓝 (sn 0 - tn 0 - d)) := by
    convert (tendsto_const_nhds (x := sn 0 - tn 0)).sub
      (hdisp.comp hι.tendsto_atTop) using 1
    funext n
    dsimp [g, h]
    abel
  have hfullEquality : U = (sn 0 - tn 0 - d) +ᵥ S :=
    paired_limits_translate_eq (g ∘ ι) (h ∘ ι) (sn 0 - tn 0 - d) hS hU hdiff
  let k := sn 0 - tn 0 - d
  let A : Set Plane := {u | u ∈ S ∧ ∀ᶠ n in atTop, u ∈ g (ι n) +ᵥ T}
  let B : Set Plane := {u | u ∈ U ∧ ∀ᶠ n in atTop, u ∈ h (ι n) +ᵥ T}
  have hAS : A ⊆ S := fun _ hu => hu.1
  have hBU : B ⊆ U := fun _ hu => hu.1
  have htmem : ∀ n, tn 0 ∈ g (ι n) +ᵥ T := by
    intro n
    exact Set.mem_vadd_set.mpr ⟨tn (ι n), (hcontacts _).1, by dsimp [g]; abel⟩
  have hsmem : ∀ n, sn 0 ∈ h (ι n) +ᵥ T := by
    intro n
    exact Set.mem_vadd_set.mpr ⟨sn (ι n), (hcontacts _).2.1, by dsimp [h]; abel⟩
  have htA : tn 0 ∈ A :=
    ⟨Tiling.Topology.mem_of_locallyFellConverges_of_tendsto_mem hS htmem
      tendsto_const_nhds, Eventually.of_forall htmem⟩
  have hsB : sn 0 ∈ B :=
    ⟨Tiling.Topology.mem_of_locallyFellConverges_of_tendsto_mem hU hsmem
      tendsto_const_nhds, Eventually.of_forall hsmem⟩
  obtain ⟨ρ, hρ, hsep⟩ := exists_packingSeparation K
  have hpartsDisjoint : Disjoint A ((-k) +ᵥ B) := by
    apply paired_persistentParts_disjoint T A B (tn 0) (sn 0) d
      (tn ∘ ι) (sn ∘ ι) ρ hρ (hsep T hT.2.1)
      (hinj.comp hι.injective) (hdisp.comp hι.tendsto_atTop)
    · intro u hu
      filter_upwards [hu.2] with n hn
      obtain ⟨t, ht, heq⟩ := Set.mem_vadd_set.mp hn
      have heq' : u - (tn 0 - tn (ι n)) = t := by
        change (tn 0 - tn (ι n)) + t = u at heq
        rw [← heq]
        abel
      exact heq'.symm ▸ ht
    · intro u hu
      filter_upwards [hu.2] with n hn
      obtain ⟨t, ht, heq⟩ := Set.mem_vadd_set.mp hn
      have heq' : u - (sn 0 - sn (ι n)) = t := by
        change (sn 0 - sn (ι n)) + t = u at heq
        rw [← heq]
        abel
      exact heq'.symm ▸ ht
  have hBS : (-k) +ᵥ B ⊆ S := by
    rintro x ⟨b, hb, rfl⟩
    have hbU := hb.1
    rw [hfullEquality] at hbU
    obtain ⟨s, hs, heq⟩ := Set.mem_vadd_set.mp hbU
    have heq' : (-k) +ᵥ b = s := by
      rw [← heq]
      change -k + ((sn 0 - tn 0 - d) + s) = s
      dsimp [k]
      abel
    change (-k) +ᵥ b ∈ S
    rw [heq']
    exact hs
  have hsBshift : (-k) +ᵥ sn 0 ∈ (-k) +ᵥ B :=
    Set.mem_vadd_set.mpr ⟨sn 0, hsB, rfl⟩
  have hSminusA : (S \ A).Nonempty :=
    ⟨(-k) +ᵥ sn 0, hBS hsBshift, fun ha =>
      Set.disjoint_left.mp hpartsDisjoint ha hsBshift⟩
  have htU : k +ᵥ tn 0 ∈ U := by
    rw [hfullEquality]
    exact Set.mem_vadd_set.mpr ⟨tn 0, htA.1, rfl⟩
  have htNotB : k +ᵥ tn 0 ∉ B := by
    intro hmem
    have hm : tn 0 ∈ (-k) +ᵥ B := by
      exact Set.mem_vadd_set.mpr ⟨k +ᵥ tn 0, hmem, by simp⟩
    exact Set.disjoint_left.mp hpartsDisjoint htA hm
  have hUminusB : (U \ B).Nonempty := ⟨k +ᵥ tn 0, htU, htNotB⟩
  obtain ⟨α, hα, hbα, hAinv, hAcompl⟩ := stabilizedWholePlaneLimit_earthquake
    K T S A (g ∘ ι) hT hS rfl hstabS ⟨tn 0, htA⟩ hSminusA
  obtain ⟨β, hβ, hbβ, hBinv, hBcompl⟩ := stabilizedWholePlaneLimit_earthquake
    K T U B (h ∘ ι) hT hU rfl hstabU ⟨sn 0, hsB⟩ hUminusB
  have hStiles : TilesOn K S Set.univ := by
    apply tilesOn_isClosed (fun n => ?_) hS
    simpa using tilesOn_translate hT (g (ι n))
  have hcarriersDisjoint : Disjoint (regularSupport K A)
      (regularSupport K ((-k) +ᵥ B)) :=
    regularSupport_disjoint_of_disjoint_subfamilies hStiles.2.1 hAS hBS hpartsDisjoint
  have hBshiftInv : IsInvariantAlong (regularSupport K ((-k) +ᵥ B)) β := by
    rw [regularSupport_vadd]
    intro u hu
    rw [vadd_vadd, add_comm u (-k), ← vadd_vadd, hBinv u hu]
  have hαβ : α = β := disjoint_invariantCarriers_sameDirection
    (regularSupport K A) (regularSupport K ((-k) +ᵥ B)) α β hα hβ
    (regularSupport_nonempty_of_nonempty K ⟨tn 0, htA⟩)
    (regularSupport_nonempty_of_nonempty K ⟨(-k) +ᵥ sn 0, hsBshift⟩)
    hcarriersDisjoint hAinv hBshiftInv
  have hSquake : HasNontrivialEarthquakeDecomposition K α S :=
    invariant_split_nontrivial K α S A hα hStiles hAS ⟨tn 0, htA⟩ hSminusA hAinv
  have hαη : α = η := by
    have hseqEq : (fun n => g (ι n) + sn (ι n)) =
        (fun n => tn 0 + (sn (ι n) - tn (ι n))) := by
      funext n
      dsimp [g]
      abel
    have hanchorEq : tn 0 + d = (-k) +ᵥ sn 0 := by
      dsimp [k]
      abel
    have hmovlim : Tendsto (fun n => g (ι n) + sn (ι n)) atTop
        (𝓝 ((-k) +ᵥ sn 0)) := by
      rw [hseqEq, ← hanchorEq]
      exact (tendsto_const_nhds (x := tn 0)).add (hdisp.comp hι.tendsto_atTop)
    apply persistent_contacts_force_direction K A (fun n => g (ι n) +ᵥ T)
      α η (tn 0) ((-k) +ᵥ sn 0) (fun n => g (ι n) + sn (ι n)) htA
      (hStiles.2.1.mono (fun _ hu => hAS hu))
    · intro n
      exact (tilesOn_translate hT (g (ι n))).2.1
    · exact fun u hu => hu.2
    · intro n
      exact Set.mem_vadd_set.mpr ⟨sn (ι n), (hcontacts _).2.1, rfl⟩
    · exact hmovlim
    · exact fun ha => Set.disjoint_left.mp hpartsDisjoint ha hsBshift
    · exact hα
    · exact hη
    · exact hasRationalDirection_of_hasBoundaryDirection hK hbα
    · exact hAinv
    · intro n
      have hn := properContact_vadd K η (sn (ι n)) (tn (ι n)) (g (ι n))
        (hcontacts _).2.2.2
      have heq : g (ι n) + tn (ι n) = tn 0 := by dsimp [g]; abel
      simpa only [heq] using hn
  refine ⟨η, hη, hbη, hηne.symm, ?_⟩
  have hSquakeη : HasNontrivialEarthquakeDecomposition K η S := hαη ▸ hSquake
  by_cases hreadyS : IsUniformlyReady K η S
  · exact Or.inl ⟨S, g ∘ ι, hS, hreadyS, hSquakeη⟩
  · obtain ⟨⟨P, hPunique⟩, _, _, _⟩ :=
      nonReady_characterization K η S hK hη hbη hStiles hSquakeη hreadyS
    have hSinv : IsInvariantAlong (regularSupport K S) η := by
      rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) hStiles]
      intro u hu
      ext x
      simp
    let Qa : EarthquakeComponent K η S :=
      (earthquakeGraph K η S).connectedComponentMk ⟨tn 0, htA.1⟩
    let Qb : EarthquakeComponent K η S :=
      (earthquakeGraph K η S).connectedComponentMk ⟨(-k) +ᵥ sn 0, hBS hsBshift⟩
    have htQa : tn 0 ∈ Qa.centres := ⟨⟨tn 0, htA.1⟩, by simp [Qa], rfl⟩
    have hsQb : (-k) +ᵥ sn 0 ∈ Qb.centres :=
      ⟨⟨(-k) +ᵥ sn 0, hBS hsBshift⟩, by simp [Qb], rfl⟩
    have hQaA : Qa.centres ⊆ A := by
      obtain hd | hsub := invariantSubfamily_isUnionComponents K η S A hη
        hStiles.2.1 hSinv hAS (hαη ▸ hAinv) Qa
      · exact False.elim (Set.disjoint_left.mp hd htQa htA)
      · exact hsub
    have hQbB : Qb.centres ⊆ (-k) +ᵥ B := by
      obtain hd | hsub := invariantSubfamily_isUnionComponents K η S ((-k) +ᵥ B) hη
        hStiles.2.1 hSinv hBS ((hαβ.symm.trans hαη) ▸ hBshiftInv) Qb
      · exact False.elim (Set.disjoint_left.mp hd hsQb hsBshift)
      · exact hsub
    have hQne : Qa ≠ Qb := by
      intro heq
      exact Set.disjoint_left.mp hpartsDisjoint (hQaA htQa) (hQbB (heq ▸ htQa))
    by_cases hQaCol : IsCenterColumn K η Qa.centres
    · apply Or.inr
      refine ⟨{
        anchor := tn 0
        anchor_mem_source := (hcontacts 0).1
        movingCentre := tn ∘ ι
        movingCentre_mem_source := fun n => (hcontacts (ι n)).1
        limitCentres := S
        converges := hS
        column := Qa.centres
        column_subset := component_centres_subset Qa
        column_isColumn := hQaCol
        anchor_mem_column := htQa
        persistent := ?_ }⟩
      intro u hu
      filter_upwards [(hQaA hu).2] with n hn
      obtain ⟨t, ht, heq⟩ := Set.mem_vadd_set.mp hn
      have heq' : u - (tn 0 - tn (ι n)) = t := by
        change (tn 0 - tn (ι n)) + t = u at heq
        rw [← heq]
        abel
      exact heq'.symm ▸ ht
    · have hQbCol : IsCenterColumn K η Qb.centres := by
        by_contra hQbNot
        have hQaP : Qa = P := by
          have hm : Qa ∈ noncolumnComponents K η S := hQaCol
          rw [hPunique] at hm
          exact Set.mem_singleton_iff.mp hm
        have hQbP : Qb = P := by
          have hm : Qb ∈ noncolumnComponents K η S := hQbNot
          rw [hPunique] at hm
          exact Set.mem_singleton_iff.mp hm
        exact hQne (hQaP.trans hQbP.symm)
      have htranslatedSubset : k +ᵥ Qb.centres ⊆ B := by
        rintro u ⟨q, hq, rfl⟩
        obtain ⟨b, hb, heq⟩ := Set.mem_vadd_set.mp (hQbB hq)
        have heq' : k +ᵥ q = b := by rw [← heq]; simp
        change k +ᵥ q ∈ B
        rw [heq']
        exact hb
      apply Or.inr
      refine ⟨{
        anchor := sn 0
        anchor_mem_source := (hcontacts 0).2.1
        movingCentre := sn ∘ ι
        movingCentre_mem_source := fun n => (hcontacts (ι n)).2.1
        limitCentres := U
        converges := hU
        column := k +ᵥ Qb.centres
        column_subset := htranslatedSubset.trans hBU
        column_isColumn := centerColumn_vadd hQbCol k
        anchor_mem_column := Set.mem_vadd_set.mpr ⟨(-k) +ᵥ sn 0, hsQb, by simp⟩
        persistent := ?_ }⟩
      intro u hu
      filter_upwards [(htranslatedSubset hu).2] with n hn
      obtain ⟨t, ht, heq⟩ := Set.mem_vadd_set.mp hn
      have heq' : u - (sn 0 - sn (ι n)) = t := by
        change (sn 0 - sn (ι n)) + t = u at heq
        rw [← heq]
        abel
      exact heq'.symm ▸ ht

theorem persistentColumn_rationalSimultaneousColumns :
∀ (K : PolygonalRegion) (δ η : Submodule ℝ Plane) (T : Set Plane),
    HasRationalSlopes K → Module.finrank ℝ δ = 1 → Module.finrank ℝ η = 1 →
    HasBoundaryDirection K δ → HasBoundaryDirection K η → δ ≠ η →
    TilesOn K T Set.univ → HasNontrivialEarthquakeDecomposition K δ T →
    (columnPart K δ T).Nonempty → PersistentColumnData K T η →
      ∀ ε : ℝ, 0 < ε → ∃ L : PolygonalRegion,
        Tiling.RationalPolygonal.IsRelativelyRational L ∧ SupportClose ε K L ∧
          ∃ U C D : Set Plane, TilesOn L U Set.univ ∧ C ⊆ U ∧ D ⊆ U ∧
            IsCenterColumn L δ C ∧ IsCenterColumn L η D
  := by
  intro K δ η T hK hδ hη hbδ hbη hne hT hquake hcol p ε hε
  classical
  obtain ⟨P, hP, B, hB, F₁, τ₁, hτ₁, hdeform⟩ :=
    bounded_joint_columnDeformation K T δ η hK hδ hη hbδ hbη hT hquake hcol p
  have hcloseControls : ∃ F₂ : Finset ℝ, ∃ τ₂ : ℝ, 0 < τ₂ ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, Tiling.Approximation.IsFiniteApproximation F₂ τ₂ φ →
        ∀ L : PolygonalRegion, L.support = Approximation.deformedPolyhedralSupport P φ →
          L.support ⊆ Metric.closedBall 0 B → SupportClose ε K L := by
    simpa only [SupportClose, dist_comm] using
      Approximation.uniformReadiness_supportClose_control K P hP hB hε
  obtain ⟨F₂, τ₂, hτ₂, hclose⟩ := hcloseControls
  let F := F₁ ∪ F₂
  let τ := min τ₁ τ₂
  obtain ⟨φ, hφ⟩ := Tiling.Approximation.exists_finiteApproximation F τ (lt_min hτ₁ hτ₂)
  have hφ₁ := Tiling.Approximation.finiteApproximation_strengthen F₁ F τ₁ τ φ
    Finset.subset_union_left (min_le_left _ _) hφ
  have hφ₂ := Tiling.Approximation.finiteApproximation_strengthen F₂ F τ₂ τ φ
    Finset.subset_union_right (min_le_right _ _) hφ
  obtain ⟨L, hLP, hLbound, hLrat, hLtiles, hLcol, hLimage⟩ := hdeform φ hφ₁
  have hLrel := relativelyRational_of_rationalSupport L hLrat
  obtain ⟨U, C, D, hU, hCU, hDU, hC, hD⟩ :=
    persistent_deformation_simultaneousColumns p φ hδ
      (hasRationalDirection_of_hasBoundaryDirection hK hbδ) hLrel hLtiles hLcol hLimage
  exact ⟨L, hLrel, hclose φ hφ₂ L hLP hLbound, U, C, D, hU, hCU, hDU, hC, hD⟩

/-- The persistent-column alternative contradicts the exact period group
provided by non-readiness. Both approximating columns are in a single U. -/
private theorem persistentColumn_impossible_of_nonReady
    (K : PolygonalRegion) (δ η : Submodule ℝ Plane) (T : Set Plane)
    (hK : HasRationalSlopes K) (hδ : Module.finrank ℝ δ = 1)
    (hη : Module.finrank ℝ η = 1)
    (hbδ : HasBoundaryDirection K δ) (hbη : HasBoundaryDirection K η)
    (hne : δ ≠ η) (htile : TilesOn K T Set.univ)
    (hquake : HasNontrivialEarthquakeDecomposition K δ T)
    (hnot : ¬IsUniformlyReady K δ T) (p : PersistentColumnData K T η) : False := by
  obtain ⟨_, hcol, hperiod, _⟩ :=
    nonReady_characterization K δ T hK hδ hbδ htile hquake hnot
  have hproduct : IsProductAlong K δ η := by
    apply product_closedUnderSupportApproximation K δ η hδ hη hne
    intro ε hε
    obtain ⟨L, _, hclose, U, C, D, hU, hCU, hDU, hC, hD⟩ :=
      persistentColumn_rationalSimultaneousColumns K δ η T hK hδ hη hbδ hbη hne
        htile hquake hcol p ε hε
    exact ⟨L, hclose,
      simultaneousColumns_product L U C D δ η hδ hη hne hU.2.1 hCU hDU hC hD⟩
  obtain ⟨v, hv, hforall⟩ :=
    product_columnPart_universalTransversePeriod K δ η hδ hη hne hproduct
  have hvperiod := hforall T htile hcol
  rw [hperiod] at hvperiod
  exact hv hvperiod

theorem exists_uniformlyReadyWholePlaneHullPoint :
∀ (K : PolygonalRegion) (T : Set Plane), HasRationalSlopes K →
    TilesOn K T Set.univ → ¬HasFLC T →
      ∃ (S : Set Plane) (g : ℕ → Plane) (δ : Submodule ℝ Plane),
        Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S ∧
        Module.finrank ℝ δ = 1 ∧ HasBoundaryDirection K δ ∧
        HasRationalDirection δ ∧ IsUniformlyReady K δ S ∧
        HasNontrivialEarthquakeDecomposition K δ S
  := by
  intro K T hK hT hnotFLC
  obtain ⟨S, g, δ, hconv, hS, hδ, hbδ, hquake⟩ :=
    nonFLC_nontrivialWholePlaneHullWitness K T hT hnotFLC
  by_cases hready : IsUniformlyReady K δ S
  · exact ⟨S, g, δ, hconv, hδ, hbδ,
      hasRationalDirection_of_hasBoundaryDirection hK hbδ, hready, hquake⟩
  · obtain ⟨η, hη, hbη, hne, hreadyOrColumn⟩ :=
      nonReady_pairLimit_readyOrPersistentColumn K δ S hK hδ hbδ hS hquake hready
    rcases hreadyOrColumn with hfound | hp
    · obtain ⟨U, h, hSU, hUready, hUquake⟩ := hfound
      obtain ⟨f, hTU⟩ := translated_limits_transitive hT hconv hSU
      exact ⟨U, f, η, hTU, hη, hbη,
        hasRationalDirection_of_hasBoundaryDirection hK hbη, hUready, hUquake⟩
    · obtain ⟨p⟩ := hp
      exact False.elim (persistentColumn_impossible_of_nonReady
        K δ η S hK hδ hη hbδ hbη hne hS hquake hready p)

theorem minimal_nonFLC_uniformlyReady :
∀ (K : PolygonalRegion) (T : Set Plane), HasRationalSlopes K →
    TilesOn K T Set.univ → IsMinimalTiling K T Set.univ → ¬HasFLC T →
      ∃ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 ∧ HasBoundaryDirection K δ ∧
        HasRationalDirection δ ∧ IsUniformlyReady K δ T ∧
        HasNontrivialEarthquakeDecomposition K δ T
  := by
  intro K T hK hT hminimal hnotFLC
  obtain ⟨S, g, δ, hconv, hδ, hbδ, hratδ, hreadyS, hquakeS⟩ :=
    exists_uniformlyReadyWholePlaneHullPoint K T hK hT hnotFLC
  let pg : ℕ → aePeriodGroup (Set.univ : Set Plane) :=
    fun n => ⟨g n, plane_mem_aePeriodGroup_univ (g n)⟩
  obtain ⟨h, hreturn⟩ := (isMinimalTiling_iff_returnSequences K T Set.univ hT).mp
    hminimal S ⟨pg, hconv⟩
  have hS : TilesOn K S Set.univ := by
    apply tilesOn_isClosed (fun n => ?_) hconv
    simpa using tilesOn_translate hT (g n)
  have hreadyT : IsUniformlyReady K δ T :=
    uniformlyReady_closedUnderTranslatedLimits K δ S T hδ hS hreadyS
      (fun n => (h n : Plane)) hreturn
  refine ⟨δ, hδ, hbδ, hratδ, hreadyT, ?_⟩
  by_cases hall : S = columnPart K δ S
  · have hScol : IsUnionOfColumns K δ S := by
      rw [hall]
      exact columnPart_isUnionColumns K δ S hδ hS.2.1
    have hTcol : IsUnionOfColumns K δ T :=
      unionColumns_closedUnderLimits hδ
        (fun n => (tilesOn_translate hS (h n : Plane)).2.1)
        (fun n => unionColumns_vadd hScol (h n : Plane)) hreturn
    exact Or.inl (unionColumns_eq_columnPart K δ T hδ hT.2.1 hTcol)
  · obtain ⟨P, hP⟩ := exists_noncolumnComponent_of_notAll K δ S hall
    obtain ⟨hPne, hPS, hPproper, hPinv, hPperiod⟩ :=
      nontrivial_noncolumnComponent_periodicProper K δ S hK hδ hbδ hS hreadyS hquakeS hall P hP
    obtain ⟨a, V, ell, hpiece, hfull, hVtiles, _⟩ :=
      fixedCarrier_limit hS hPS hPperiod hreturn
    have hVE : regularSupport K V = P.carrier := regularSupport_eq_of_tilesOn
      (regularSupport_isRegularOpen K P.centres).1
      (regularSupport_isRegularOpen K P.centres).2 hVtiles
    have hVne : V.Nonempty := by
      by_contra h
      have hempty : V = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have hEempty : P.carrier = ∅ := by
        rw [← hVE, hempty]
        simp [regularSupport, openUnion]
      exact (regularSupport_nonempty_of_nonempty K hPne).ne_empty hEempty
    apply corrected_limit_piece_nontrivial K δ S P.centres T V ell a hδ hT hPS
      hpiece hfull hVne
    · rwa [hVE]
    · rwa [hVE]



end Tiling.RationalSlopes
