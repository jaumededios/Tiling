import Tiling.RationalSlopes.UniformReadiness
import Tiling.RationalSlopes.EarthquakePeriodicity
import Tiling.RationalSlopes.NonFLC
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


private noncomputable def standardLattice : PlanarLattice where
  basis := ![(1 : Plane), Complex.I]
  independent := by
    rw [LinearIndependent.pair_iffₛ]
    intro a b c d h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    norm_num at hre him
    exact ⟨hre, him⟩

private theorem regularSupport_empty (K : PolygonalRegion) :
    regularSupport K ∅ = ∅ := by
  simp [regularSupport, openUnion]

private theorem empty_latticePeriodic : IsLatticePeriodic (∅ : Set Plane) := by
  refine ⟨standardLattice, ?_⟩
  intro v hv
  change v +ᵥ (∅ : Set Plane) = ∅
  simp

private theorem univ_latticePeriodic : IsLatticePeriodic (Set.univ : Set Plane) := by
  refine ⟨standardLattice, ?_⟩
  intro v hv
  change v +ᵥ (Set.univ : Set Plane) = Set.univ
  simp

structure MinimalWholePlaneStructure (K : PolygonalRegion) (T : Set Plane) where
  direction : Submodule ℝ Plane
  direction_oneDim : Module.finrank ℝ direction = 1
  direction_rational : HasRationalDirection direction
  columnAggregate : Set Plane
  aggregate_isUnionColumns : IsUnionOfColumns K direction columnAggregate
  numberOfPieces : ℕ
  piece : Fin numberOfPieces → Set Plane
  piece_nonempty : ∀ j, (piece j).Nonempty
  pieces_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ piece
  column_disjoint_piece : ∀ j, Disjoint columnAggregate (piece j)
  centres_partition : columnAggregate ∪ (⋃ j, piece j) = T
  piece_hasFLC : ∀ j, HasFLC (piece j)
  piece_minimal : ∀ j, Tiling.Polygonal.Topology.IsMinimalTiling K (piece j)
    (regularSupport K (piece j))
  aggregate_invariant : IsInvariantAlong (regularSupport K columnAggregate) direction
  piece_invariant : ∀ j, IsInvariantAlong (regularSupport K (piece j)) direction
  aggregate_carrier_periodic : IsLatticePeriodic (regularSupport K columnAggregate)
  piece_carrier_periodic : ∀ j, IsLatticePeriodic (regularSupport K (piece j))

private theorem component_centres_subset {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (P : EarthquakeComponent K δ T) : P.centres ⊆ T := by
  rintro x ⟨s, _, rfl⟩
  exact s.property

private theorem component_centres_nonempty {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (P : EarthquakeComponent K δ T) : P.centres.Nonempty :=
  P.nonempty_supp.image Subtype.val

private theorem component_centres_disjoint {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T : Set Plane}
    {P Q : EarthquakeComponent K δ T} (hPQ : P ≠ Q) : Disjoint P.centres Q.centres := by
  apply Set.disjoint_left.mpr
  rintro x ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
  have hst : t = s := Subtype.ext heq
  subst t
  exact hPQ (SimpleGraph.ConnectedComponent.eq_of_common_vertex hs ht)

/-- The packing bound counts only the components with a proved bounded witness. -/
private theorem components_finite_of_bounded_witness
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements T)) {B : Set Plane}
    (hB : Bornology.IsBounded B)
    (hw : ∀ P ∈ noncolumnComponents K δ T, (P.centres ∩ B).Nonempty) :
    (noncolumnComponents K δ T).Finite := by
  classical
  let J := {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}
  let w (P : J) : Plane := (hw P.1 P.2).choose
  have hwP (P : J) : w P ∈ P.1.centres ∩ B := (hw P.1 P.2).choose_spec
  let f : J → ↥(T ∩ B) := fun P =>
    ⟨w P, component_centres_subset P.1 (hwP P).1, (hwP P).2⟩
  have hf : Function.Injective f := by
    intro P Q hPQ
    apply Subtype.ext
    by_contra hne
    have heq : w P = w Q := congrArg Subtype.val hPQ
    exact Set.disjoint_left.mp (component_centres_disjoint hne)
      (hwP P).1 (heq.symm ▸ (hwP Q).1)
  have : Finite ↥(T ∩ B) := ((packing_centres_locallyFinite hp).1 B hB).to_subtype
  have : Finite J := Finite.of_injective f hf
  exact Set.toFinite _

private theorem invariant_univ (δ : Submodule ℝ Plane) :
    IsInvariantAlong (Set.univ : Set Plane) δ := by
  intro u hu
  simp

private theorem stepGroup_le_carrierPeriods {δ : Submodule ℝ Plane}
    {v : Plane} {D : Set Plane} (hInv : IsInvariantAlong D δ)
    (hv : v ∈ periodGroup D) : periodStepGroup δ v ≤ periodGroup D := by
  apply sup_le
  · intro u hu
    exact AddAction.mem_stabilizer_iff.mpr (hInv u hu)
  · exact (AddSubgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hv)

private theorem carrier_latticePeriodic_of_commonPeriod {δ : Submodule ℝ Plane}
    {v : Plane} {D : Set Plane} (hδ : Module.finrank ℝ δ = 1)
    (hvδ : v ∉ δ) (hInv : IsInvariantAlong D δ) (hv : v ∈ periodGroup D) :
    IsLatticePeriodic D := by
  obtain ⟨L, hL⟩ := periodStepGroup_containsLattice δ v hδ hvδ
  exact ⟨L, fun u hu => stepGroup_le_carrierPeriods hInv hv (hL hu)⟩

private theorem columnPart_invariant {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (hδ : Module.finrank ℝ δ = 1)
    (hp : IsPacking K.prototileFamily (K.placements T))
    (hInv : IsInvariantAlong (regularSupport K T) δ) :
    IsInvariantAlong (regularSupport K (columnPart K δ T)) δ := by
  intro u hu
  rw [columnPart, regularSupport_iUnion]
  rw [← interior_vadd, ← closure_vadd, ← Set.image_vadd, Set.image_iUnion]
  simp_rw [Set.image_vadd]
  apply congrArg (fun S : Set Plane => interior (closure S))
  exact Set.iUnion_congr fun P => component_isInvariant K δ T hδ hp hInv P.1 u hu

private theorem columnPart_disjoint_noncolumn {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T : Set Plane} (P : EarthquakeComponent K δ T)
    (hP : P ∈ noncolumnComponents K δ T) : Disjoint (columnPart K δ T) P.centres := by
  rw [columnPart]
  apply Set.disjoint_iUnion_left.mpr
  intro Q
  apply component_centres_disjoint
  intro hQP
  exact hP (hQP ▸ Q.2)

private theorem subfamily_packing {K : PolygonalRegion} {T A : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements T)) (hAT : A ⊆ T) :
    IsPacking K.prototileFamily (K.placements A) :=
  hp.mono (fun _ h => hAT h)

/-- Under the original step group, the actual limit tiles the original fixed carrier. -/
private theorem component_limit_tilesOn_original_carrier {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T U : Set Plane} {v : Plane} {g : ℕ → Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (hv : IsCommonCarrierPeriod K δ T v)
    (hg : ∀ n, g n ∈ periodStepGroup δ v)
    (P : EarthquakeComponent K δ T) (hP : P ∈ noncolumnComponents K δ T)
    (hconv : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ P.centres) U) :
    TilesOn K U P.carrier := by
  have hsupport : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hInv : IsInvariantAlong P.carrier δ := component_isInvariant K δ T hδ htile.2.1
    (hsupport.symm ▸ invariant_univ δ) P
  have hperiods := stepGroup_le_carrierPeriods hInv (hv.2.2 P hP)
  have hPtile : TilesOn K P.centres P.carrier :=
    tilesOn_regularSupport_of_packing (subfamily_packing htile.2.1 (component_centres_subset P))
  apply tilesOn_isClosed (fun n => ?_) hconv
  have hgn : g n +ᵥ P.carrier = P.carrier :=
    AddAction.mem_stabilizer_iff.mp (hperiods (hg n))
  simpa only [hgn] using tilesOn_translate hPtile (g n)

private theorem component_limit_support_eq_original_carrier {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T U : Set Plane} {v : Plane} {g : ℕ → Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (hv : IsCommonCarrierPeriod K δ T v)
    (hg : ∀ n, g n ∈ periodStepGroup δ v)
    (P : EarthquakeComponent K δ T) (hP : P ∈ noncolumnComponents K δ T)
    (hconv : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ P.centres) U) :
    regularSupport K U = P.carrier := by
  obtain ⟨hopen, hregular⟩ := regularSupport_isRegularOpen K P.centres
  exact regularSupport_eq_of_tilesOn hopen hregular
    (component_limit_tilesOn_original_carrier hδ htile hv hg P hP hconv)

private theorem columnPart_limit_support_eq_original_carrier {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T U : Set Plane} {v : Plane} {g : ℕ → Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (hv : IsCommonCarrierPeriod K δ T v)
    (hg : ∀ n, g n ∈ periodStepGroup δ v)
    (hconv : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ columnPart K δ T) U) :
    regularSupport K U = regularSupport K (columnPart K δ T) := by
  have hsupport : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hInv := columnPart_invariant hδ htile.2.1 (hsupport.symm ▸ invariant_univ δ)
  have hperiods := stepGroup_le_carrierPeriods hInv hv.2.1
  have hcolT : columnPart K δ T ⊆ T := by
    intro x hx
    obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
    exact component_centres_subset P.1 hxP
  have hCtile : TilesOn K (columnPart K δ T) (regularSupport K (columnPart K δ T)) :=
    tilesOn_regularSupport_of_packing (subfamily_packing htile.2.1 hcolT)
  have hUtile : TilesOn K U (regularSupport K (columnPart K δ T)) := by
    apply tilesOn_isClosed (fun n => ?_) hconv
    have hgn : g n +ᵥ regularSupport K (columnPart K δ T) =
        regularSupport K (columnPart K δ T) :=
      AddAction.mem_stabilizer_iff.mp (hperiods (hg n))
    simpa only [hgn] using tilesOn_translate hCtile (g n)
  obtain ⟨hopen, hregular⟩ := regularSupport_isRegularOpen K (columnPart K δ T)
  exact regularSupport_eq_of_tilesOn hopen hregular hUtile

/-- The bounded return correction is retained; torus regularity closes the two inclusions. -/
private theorem corrected_carrier_inclusions_eq {D E : Set Plane} {a : Plane}
    (hDopen : IsOpen D) (hDreg : interior (closure D) = D)
    (hDper : IsLatticePeriodic D) (hDE : D ⊆ E) (hEaD : E ⊆ a +ᵥ D) :
    E = D ∧ a +ᵥ D = D := by
  have hback : (-a) +ᵥ D ⊆ D := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hyz⟩ := hEaD (hDE hy)
    simpa [← hyz] using hz
  have hneg := periodicRegularOpen_translatedContainment D hDopen hDreg hDper (-a) hback
  have ha : a +ᵥ D = D := by
    have := congrArg (fun S : Set Plane => a +ᵥ S) hneg
    simpa using this.symm
  exact ⟨Set.Subset.antisymm (ha ▸ hEaD) hDE, ha⟩

/-- Packing excludes an extra centre after carrier equality, not before. -/
private theorem centres_eq_of_subset_support_eq {K : PolygonalRegion}
    {T A B : Set Plane} (hp : IsPacking K.prototileFamily (K.placements T))
    (hBT : B ⊆ T) (hAB : A ⊆ B)
    (hsupport : regularSupport K A = regularSupport K B) : A = B := by
  apply Set.Subset.antisymm hAB
  intro t htB
  by_contra htA
  have hsingleT : ({t} : Set Plane) ⊆ T := Set.singleton_subset_iff.mpr (hBT htB)
  have hdisj : Disjoint A ({t} : Set Plane) := by
    simp [Set.disjoint_singleton_right, htA]
  have hcarriers := regularSupport_disjoint_of_disjoint_subfamilies hp
    (hAB.trans hBT) hsingleT hdisj
  obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hxopen : t + x ∈ openUnion K ({t} : Set Plane) :=
    Set.mem_iUnion.mpr ⟨⟨t, Set.mem_singleton t⟩, Set.mem_vadd_set.mpr ⟨x, hx, rfl⟩⟩
  have hsingleOpen : IsOpen (openUnion K ({t} : Set Plane)) :=
    isOpen_iUnion fun s => isOpen_interior.vadd (s : Plane)
  have hxsingle : t + x ∈ regularSupport K ({t} : Set Plane) :=
    (hsingleOpen.subset_interior_iff.mpr subset_closure) hxopen
  have hxB : t + x ∈ openUnion K B :=
    Set.mem_iUnion.mpr ⟨⟨t, htB⟩, Set.mem_vadd_set.mpr ⟨x, hx, rfl⟩⟩
  have hBopen : IsOpen (openUnion K B) :=
    isOpen_iUnion fun s => isOpen_interior.vadd (s : Plane)
  have hxBsupport : t + x ∈ regularSupport K B :=
    (hBopen.subset_interior_iff.mpr subset_closure) hxB
  rw [← hsupport] at hxBsupport
  exact Set.disjoint_left.mp hcarriers hxBsupport hxsingle

/-- The two finite surjections forbid refinement of the actual inherited families. -/
private theorem finite_refinement_single_piece {I J : Type}
    [Fintype I] [Fintype J] (parent : J → I) (back : I → J)
    (hp : Function.Surjective parent) (hb : Function.Surjective back)
    (inherited : I → Set Plane) (canonical : J → Set Plane)
    (hcover : ∀ i, inherited i = ⋃ j : {j // parent j = i}, canonical j.1) :
    ∀ i, ∃ j, parent j = i ∧ canonical j = inherited i := by
  have hcard : Fintype.card J = Fintype.card I :=
    le_antisymm (Fintype.card_le_of_surjective back hb)
      (Fintype.card_le_of_surjective parent hp)
  have hinj := ((Fintype.bijective_iff_surjective_and_card parent).mpr ⟨hp, hcard⟩).1
  intro i
  obtain ⟨j, hj⟩ := hp i
  refine ⟨j, hj, ?_⟩
  rw [hcover i]
  ext x
  constructor
  · intro hx
    exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩
  · intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    have hkj : k.1 = j := hinj (k.2.trans hj.symm)
    simpa [hkj] using hk

private theorem locallyFell_limits_subset {A B : ℕ → Set Plane} {U S : Set Plane}
    (hAB : ∀ n, A n ⊆ B n)
    (hA : Tiling.Topology.LocallyFellConverges A U)
    (hB : Tiling.Topology.LocallyFellConverges B S) : U ⊆ S := by
  intro x hx
  by_contra hxS
  have hclosed : IsClosed S := hB.2.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl x hxS
  have hcompact : IsCompact (Metric.closedBall x (ε / 2)) := isCompact_closedBall x (ε / 2)
  have hdisj : Disjoint S (Metric.closedBall x (ε / 2)) := by
    apply Set.disjoint_right.mpr
    intro y hy
    exact hball (Metric.closedBall_subset_ball (by linarith) hy)
  have hhit := Tiling.Topology.locallyFellConverges_eventually_exists_mem_ball hA hx
    (show 0 < ε / 2 by linarith)
  have hmiss := Tiling.Topology.locallyFellConverges_eventually_disjoint_compact hB hcompact hdisj
  obtain ⟨n, hn, hm⟩ := (hhit.and hmiss).exists
  obtain ⟨y, hy, hyx⟩ := hn
  exact Set.disjoint_left.mp hm (hAB n hy) (Metric.mem_closedBall.mpr hyx.le)

private theorem unionColumns_subset_columnPart {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {S U : Set Plane} (hδ : Module.finrank ℝ δ = 1)
    (hp : IsPacking K.prototileFamily (K.placements S)) (hUS : U ⊆ S)
    (hcols : IsUnionOfColumns K δ U) : U ⊆ columnPart K δ S := by
  intro x hx
  have hxfibre : x ∈ lineFibre δ U x := ⟨hx, by simp⟩
  have hfibreS : lineFibre δ U x ⊆ S := fun y hy => hUS hy.1
  obtain ⟨P, hP⟩ := column_isComponent K δ S (lineFibre δ U x)
    hδ hp hfibreS (hcols x hx)
  have hPcol : IsCenterColumn K δ P.centres := hP.symm ▸ hcols x hx
  exact Set.mem_iUnion.mpr ⟨⟨P, hPcol⟩, hP.symm ▸ hxfibre⟩

private theorem centerColumn_vadd {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {C : Set Plane} (hC : IsCenterColumn K δ C) (g : Plane) :
    IsCenterColumn K δ (g +ᵥ C) := by
  refine ⟨(tilesOn_translate (tilesOn_regularSupport_of_packing hC.1) g).2.1,
    hC.2.1.image (fun x => g +ᵥ x), ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hC.2.2.1
    refine ⟨g + a, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    simpa only [vadd_eq_add, add_sub_add_left_eq_sub] using ha y hy
  · rw [regularSupport_vadd]
    intro u hu
    calc
      u +ᵥ (g +ᵥ regularSupport K C) = g +ᵥ (u +ᵥ regularSupport K C) := by
        rw [← vadd_assoc, vadd_eq_add, add_comm u g]
        exact vadd_assoc g u (regularSupport K C)
      _ = g +ᵥ regularSupport K C := by rw [hC.2.2.2 u hu]

private theorem lineFibre_vadd (δ : Submodule ℝ Plane) (U : Set Plane) (g t : Plane) :
    lineFibre δ (g +ᵥ U) (g + t) = g +ᵥ lineFibre δ U t := by
  ext x
  simp only [lineFibre, Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  have hdiff : x - (g + t) = -g + x - t := by abel
  rw [hdiff]

private theorem unionColumns_vadd {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {U : Set Plane} (hcols : IsUnionOfColumns K δ U) (g : Plane) :
    IsUnionOfColumns K δ (g +ᵥ U) := by
  rintro x ⟨t, ht, rfl⟩
  change IsCenterColumn K δ (lineFibre δ (g +ᵥ U) (g + t))
  rw [lineFibre_vadd]
  exact centerColumn_vadd (hcols t ht) g

private theorem columnPart_limit_subset_new_columnPart {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T S U : Set Plane} {g : ℕ → Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (hfull : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S)
    (hcol : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ columnPart K δ T) U) :
    U ⊆ columnPart K δ S := by
  have hCsubset : columnPart K δ T ⊆ T := by
    intro x hx
    obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
    exact component_centres_subset P.1 hxP
  have hpC := subfamily_packing htile.2.1 hCsubset
  have hpCn (n : ℕ) : IsPacking K.prototileFamily
      (K.placements (g n +ᵥ columnPart K δ T)) :=
    (tilesOn_translate (tilesOn_regularSupport_of_packing hpC) (g n)).2.1
  have hUcols : IsUnionOfColumns K δ U := unionColumns_closedUnderLimits hδ hpCn
    (fun n => unionColumns_vadd (columnPart_isUnionColumns K δ T hδ htile.2.1) (g n)) hcol
  have hUS : U ⊆ S := locallyFell_limits_subset
    (fun n => Set.vadd_set_mono hCsubset) hcol hfull
  have hS : TilesOn K S Set.univ := tilesOn_isClosed
    (fun n => by simpa using tilesOn_translate htile (g n)) hfull
  exact unionColumns_subset_columnPart hδ hS.2.1 hUS hUcols

/-- A transverse invariant nonempty subfamily cannot fit in a proper cylinder. -/
private theorem invariant_subset_direction_eq {δ η : Submodule ℝ Plane} {A D : Set Plane}
    (hδ : Module.finrank ℝ δ = 1) (hη : Module.finrank ℝ η = 1)
    (hA : A.Nonempty) (hAD : A ⊆ D)
    (hDinv : IsInvariantAlong D δ) (hAinv : IsInvariantAlong A η)
    (hproper : D ≠ Set.univ) : η = δ := by
  classical
  by_contra hne
  have hnotle : ¬η ≤ δ := fun h =>
    hne (Submodule.eq_of_le_of_finrank_eq h (hη.trans hδ.symm))
  have hex : ∃ e : Plane, e ∈ η ∧ e ∉ δ := by
    by_contra hn
    apply hnotle
    intro e he
    by_contra heδ
    exact hn ⟨e, he, heδ⟩
  obtain ⟨e, heη, heδ⟩ := hex
  have htop : δ ⊔ Submodule.span ℝ ({e} : Set Plane) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by
      rw [Submodule.finrank_sup_span_singleton heδ, hδ]
      norm_num [Plane, Complex.finrank_real_complex])
  have hsumtop : δ ⊔ η = ⊤ := by
    apply top_unique
    rw [← htop]
    exact sup_le_sup_left (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr heη)) δ
  apply hproper
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨a, ha⟩ := hA
  have hx : x - a ∈ δ ⊔ η := hsumtop.symm ▸ Submodule.mem_top
  obtain ⟨d, hd, u, hu, hdu⟩ := Submodule.mem_sup.mp hx
  have hua : u + a ∈ A := by
    change u +ᵥ a ∈ A
    rw [← hAinv u hu]
    exact Set.vadd_mem_vadd_set ha
  have hdua : d + (u + a) ∈ D := by
    change d +ᵥ (u + a) ∈ D
    rw [← hDinv d hd]
    exact Set.vadd_mem_vadd_set (hAD hua)
  have heq : d + (u + a) = x := by rw [← add_assoc, hdu]; abel
  exact heq ▸ hdua

private theorem regularSupport_mono {K : PolygonalRegion} {A B : Set Plane}
    (hAB : A ⊆ B) : regularSupport K A ⊆ regularSupport K B := by
  apply interior_mono
  apply closure_mono
  intro x hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨⟨a, hAB a.2⟩, ha⟩

private theorem regularSupport_nonempty {K : PolygonalRegion} {A : Set Plane}
    (hA : A.Nonempty) : (regularSupport K A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hmem : a + x ∈ openUnion K A := Set.mem_iUnion.mpr
    ⟨⟨a, ha⟩, Set.mem_vadd_set.mpr ⟨x, hx, rfl⟩⟩
  have hopen : IsOpen (openUnion K A) := isOpen_iUnion fun s => isOpen_interior.vadd (s : Plane)
  exact ⟨a + x, (hopen.subset_interior_iff.mpr subset_closure) hmem⟩

private theorem noncolumn_carrier_proper {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (htile : TilesOn K T Set.univ)
    (hdecomp : HasNontrivialEarthquakeDecomposition K δ T)
    (P : EarthquakeComponent K δ T) (hP : P ∈ noncolumnComponents K δ T) :
    P.carrier ≠ Set.univ := by
  intro hcarrier
  have hsupport : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hPwhole : P.centres = T := centres_eq_of_subset_support_eq htile.2.1
    subset_rfl (component_centres_subset P) (hcarrier.trans hsupport.symm)
  rcases hdecomp with hcolumns | ⟨Q, R, hQR⟩
  · have hd := columnPart_disjoint_noncolumn P hP
    obtain ⟨x, hx⟩ := component_centres_nonempty P
    have hxT : x ∈ T := component_centres_subset P hx
    exact Set.disjoint_left.mp hd (hcolumns ▸ hxT) hx
  · have heq (Q : EarthquakeComponent K δ T) : Q = P := by
      by_contra hQP
      obtain ⟨x, hxQ⟩ := component_centres_nonempty Q
      have hxP : x ∈ P.centres := hPwhole.symm ▸ component_centres_subset Q hxQ
      exact Set.disjoint_left.mp (component_centres_disjoint hQP) hxQ hxP
    exact hQR ((heq Q).trans (heq R).symm)

private theorem locallyFell_subsequence {A : ℕ → Set Plane} {U : Set Plane}
    (hconv : Tiling.Topology.LocallyFellConverges A U)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tiling.Topology.LocallyFellConverges (A ∘ φ) U :=
  ⟨fun n => hconv.1 (φ n), hconv.2.1, hconv.2.2.comp hφ.tendsto_atTop⟩


private theorem transverseCoordinate {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) :
    ∃ π : Plane →L[ℝ] ℝ, ∃ c : Plane, π c = 1 ∧ ∀ z, z ∈ δ ↔ π z = 0 := by
  have hδne : δ ≠ ⊥ := by
    intro heq
    rw [heq] at hδ
    simp at hδ
  obtain ⟨d, hdδ, hdne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδne
  have hspan : Submodule.span ℝ {d} = δ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hdδ)
    · rw [finrank_span_singleton hdne, hδ]
  let π : Plane →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.mul ℝ Plane d⁻¹)
  have hπ (z : Plane) : π z = (d⁻¹ * z).im := rfl
  refine ⟨π, d * Complex.I, ?_, ?_⟩
  · rw [hπ, ← mul_assoc, inv_mul_cancel₀ hdne, one_mul, Complex.I_im]
  · intro z
    rw [← hspan, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨r, rfl⟩
      rw [hπ, mul_smul_comm, inv_mul_cancel₀ hdne]
      simp
    · intro hz
      refine ⟨(d⁻¹ * z).re, ?_⟩
      have heq : ((d⁻¹ * z).re : Plane) = d⁻¹ * z := by
        apply Complex.ext
        · simp
        · simpa [hπ] using hz.symm
      change ((d⁻¹ * z).re : Plane) * d = z
      rw [heq]
      calc
        d⁻¹ * z * d = (d⁻¹ * d) * z := by ring
        _ = z := by rw [inv_mul_cancel₀ hdne, one_mul]

private theorem carrier_supportOwner {K : PolygonalRegion} {A : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements A))
    {x : Plane} (hx : x ∈ regularSupport K A) :
    ∃ s ∈ A, ∃ k ∈ K.support, s + k = x := by
  have hx' := interior_subset hx
  rw [closure_openUnion_eq_iUnion_support hp] at hx'
  obtain ⟨s, k, hk, heq⟩ := Set.mem_iUnion.mp hx'
  exact ⟨s, s.property, k, hk, heq⟩

private theorem carrier_openPoint {K : PolygonalRegion} {A : Set Plane}
    {s z : Plane} (hs : s ∈ A) (hz : z ∈ K.openCarrier) :
    s + z ∈ regularSupport K A := by
  have hopen : IsOpen (openUnion K A) :=
    isOpen_iUnion fun t => isOpen_interior.vadd (t : Plane)
  exact hopen.subset_interior_closure (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, z, hz, rfl⟩)

private theorem directionalOverlap_coordinateBound
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {π : Plane →L[ℝ] ℝ}
    (hker : ∀ z, z ∈ δ ↔ π z = 0) {M : ℝ}
    (hK : ∀ z ∈ K.support, |π z| ≤ M) {s t : Plane}
    (h : DirectionalOverlap K δ s t) : |π s - π t| ≤ 2 * M := by
  obtain ⟨x, ⟨a, ha, rfl⟩, y, ⟨b, hb, rfl⟩, hdiff⟩ := h
  have heq : π s - π t = π b - π a := by
    have hh := (hker _).mp hdiff
    simp only [vadd_eq_add, map_sub, map_add] at hh
    linarith
  rw [heq]
  exact (abs_sub _ _).trans (by linarith [hK a (interior_subset ha), hK b (interior_subset hb)])

private theorem walk_crosses_band
    {V : Type*} (G : SimpleGraph V) {s t : V} (p : G.Walk s t)
    (q : V → ℝ) {R : ℝ} (hR : 0 < R)
    (hlip : ∀ ⦃u v⦄, G.Adj u v → |q u - q v| ≤ 2 * R)
    (hs : q s ≤ 0) (ht : 0 ≤ q t) :
    ∃ v, G.Reachable s v ∧ |q v| ≤ R := by
  induction p with
  | @nil u =>
      have hq : q u = 0 := le_antisymm hs ht
      exact ⟨u, SimpleGraph.Reachable.rfl, by simp [hq, le_of_lt hR]⟩
  | @cons u v t hadj p ih =>
      by_cases hband : |q u| ≤ R
      · exact ⟨u, .rfl, hband⟩
      · have hqu : q u < -R := by
          have habs : R < |q u| := lt_of_not_ge hband
          rw [abs_of_nonpos hs] at habs
          linarith
        by_cases hv : q v ≤ 0
        · obtain ⟨w, hw, hbw⟩ := ih hv ht
          exact ⟨w, hadj.reachable.trans hw, hbw⟩
        · have hvpos : 0 < q v := lt_of_not_ge hv
          have hdiff := hlip hadj
          have hupper : q v ≤ R := by
            have hdiff' : |q v - q u| ≤ 2 * R := by
              simpa [abs_sub_comm] using hdiff
            have hle : q v - q u ≤ 2 * R := (abs_le.mp hdiff').2
            linarith
          exact ⟨v, hadj.reachable, abs_le.mpr ⟨by linarith, hupper⟩⟩
private theorem connectedComponent_crosses_band
    {V : Type*} (G : SimpleGraph V) (C : G.ConnectedComponent)
    (q : V → ℝ) {R : ℝ} (hR : 0 < R)
    (hlip : ∀ ⦃u v⦄, G.Adj u v → |q u - q v| ≤ 2 * R)
    {s t : V} (hsC : s ∈ C.supp) (htC : t ∈ C.supp)
    (hs : q s ≤ 0) (ht : 0 ≤ q t) :
    ∃ v ∈ C.supp, |q v| ≤ R := by
  have hcomp : G.connectedComponentMk s = G.connectedComponentMk t :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C s).mp hsC |>.trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff C t).mp htC).symm
  have hreach : G.Reachable s t := SimpleGraph.ConnectedComponent.eq.mp hcomp
  obtain ⟨p⟩ := hreach
  obtain ⟨v, hv, hband⟩ := walk_crosses_band G p q hR hlip hs ht
  refine ⟨v, ?_, hband⟩
  exact SimpleGraph.ConnectedComponent.mem_supp_iff C v |>.2 <|
    (SimpleGraph.ConnectedComponent.sound hv).symm.trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff C s).mp hsC)

private theorem normalize_bandCentre {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {A : Set Plane} {π : Plane →L[ℝ] ℝ} {c : Plane}
    (hker : ∀ z, z ∈ δ ↔ π z = 0) (hc : π c = 1)
    (hp : IsPacking K.prototileFamily (K.placements A))
    (hInv : IsInvariantAlong (regularSupport K A) δ)
    {M R : ℝ} (hKπ : ∀ z ∈ K.support, |π z| ≤ M)
    (hKR : ∀ z ∈ K.support, ‖z‖ ≤ R) {t : Plane}
    (ht : t ∈ A) (htπ : |π t| ≤ M) :
    ∃ s ∈ A, ‖s‖ ≤ (2 * M) * ‖c‖ + R := by
  obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hy : t + z ∈ regularSupport K A := carrier_openPoint ht hz
  let x : Plane := π (t + z) • c
  have huδ : x - (t + z) ∈ δ := (hker _).mpr (by
    simp only [x, map_sub, map_smul, hc, smul_eq_mul, mul_one, sub_self])
  have hx : x ∈ regularSupport K A := by
    rw [← hInv (x - (t + z)) huδ]
    exact ⟨t + z, hy, by simp [vadd_eq_add]⟩
  obtain ⟨s, hs, k, hk, heq⟩ := carrier_supportOwner hp hx
  refine ⟨s, hs, ?_⟩
  have hsx : s = x - k := by rw [← heq]; abel
  have hxbound : ‖x‖ ≤ (2 * M) * ‖c‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hsum : |π (t + z)| ≤ 2 * M := by
      rw [map_add]
      exact (abs_add_le _ _).trans (by linarith [hKπ z (interior_subset hz)])
    exact mul_le_mul_of_nonneg_right hsum (norm_nonneg c)
  rw [hsx]
  exact (norm_sub_le _ _).trans (add_le_add hxbound (hKR k hk))

private theorem component_bandCentre {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} {π : Plane →L[ℝ] ℝ}
    (hker : ∀ z, z ∈ δ ↔ π z = 0) {M : ℝ} (hM : 0 < M)
    (hKπ : ∀ z ∈ K.support, |π z| ≤ M)
    (P : EarthquakeComponent K δ T)
    (hp : IsPacking K.prototileFamily (K.placements P.centres))
    (hpos : ∃ x ∈ P.carrier, M < π x)
    (hneg : ∃ x ∈ P.carrier, π x < -M) :
    ∃ t ∈ P.centres, |π t| ≤ M := by
  obtain ⟨xp, hxp, hxpπ⟩ := hpos
  obtain ⟨sp, hsp, kp, hkp, hpEq⟩ := carrier_supportOwner hp hxp
  obtain ⟨xn, hxn, hxnπ⟩ := hneg
  obtain ⟨sn, hsn, kn, hkn, hnEq⟩ := carrier_supportOwner hp hxn
  have hspπ : 0 ≤ π sp := by
    have hh := (abs_le.mp (hKπ kp hkp)).2
    rw [← hpEq, map_add] at hxpπ
    linarith
  have hsnπ : π sn ≤ 0 := by
    have hh := (abs_le.mp (hKπ kn hkn)).1
    rw [← hnEq, map_add] at hxnπ
    linarith
  obtain ⟨vp, hvp, rfl⟩ := hsp
  obtain ⟨vn, hvn, rfl⟩ := hsn
  have hlip : ∀ ⦃u v⦄, (earthquakeGraph K δ T).Adj u v →
      |π (u : Plane) - π (v : Plane)| ≤ 2 * M := by
    intro u v huv
    obtain ⟨_, hov | hov⟩ := huv
    · exact directionalOverlap_coordinateBound hker hKπ hov
    · simpa only [abs_sub_comm] using directionalOverlap_coordinateBound hker hKπ hov
  obtain ⟨t, ht, htπ⟩ := connectedComponent_crosses_band (earthquakeGraph K δ T)
    P (fun t => π (t : Plane)) hM hlip hvn hvp hsnπ hspπ
  exact ⟨t, ⟨t, ht, rfl⟩, htπ⟩

private theorem exists_scalar_above
    (π : Plane →L[ℝ] ℝ) (E : Set Plane) (w : Plane)
    (hw : w ∈ periodGroup E) (hp : 0 < π w)
    {y : Plane} (hy : y ∈ E) (b : ℝ) :
    ∃ x ∈ E, b < π x := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - π y) / π w)
  have hn' : b - π y < (n : ℝ) * π w := by
    apply (div_lt_iff₀ hp).mp
    exact hn
  let k : ℤ := n
  have hk : k • w ∈ periodGroup E := (periodGroup E).zsmul_mem hw k
  have htrans : k • w +ᵥ E = E := hk
  let x : Plane := k • w +ᵥ y
  refine ⟨x, ?_, ?_⟩
  · have hmem : k • w +ᵥ y ∈ k • w +ᵥ E :=
      vadd_mem_vadd_set_iff.mpr hy
    rw [← htrans]
    simpa [x] using hmem
  · have hπ : π x = (n : ℝ) * π w + π y := by
      dsimp [x, k]
      rw [map_add, map_zsmul]
      simp [zsmul_eq_mul]
    rw [hπ]
    linarith

private theorem exists_scalar_below
    (π : Plane →L[ℝ] ℝ) (E : Set Plane) (w : Plane)
    (hw : w ∈ periodGroup E) (hp : 0 < π w)
    {y : Plane} (hy : y ∈ E) (b : ℝ) :
    ∃ x ∈ E, π x < b := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((π y - b) / π w)
  have hn' : π y - b < (n : ℝ) * π w := by
    apply (div_lt_iff₀ hp).mp
    exact hn
  let k : ℤ := -(n : ℤ)
  have hk : k • w ∈ periodGroup E := (periodGroup E).zsmul_mem hw k
  have htrans : k • w +ᵥ E = E := hk
  let x : Plane := k • w +ᵥ y
  refine ⟨x, ?_, ?_⟩
  · have hmem : k • w +ᵥ y ∈ k • w +ᵥ E :=
      vadd_mem_vadd_set_iff.mpr hy
    rw [← htrans]
    simpa [x] using hmem
  · have hπ : π x = -(n : ℝ) * π w + π y := by
      dsimp [x, k]
      rw [map_add, map_zsmul]
      simp [zsmul_eq_mul]
    rw [hπ]
    linarith

private theorem period_scalar_unbounded
    (π : Plane →L[ℝ] ℝ) (E : Set Plane) (w : Plane)
    (hw : w ∈ periodGroup E) (hp : 0 < π w)
    {y : Plane} (hy : y ∈ E) (M : ℝ) :
    (∃ x ∈ E, π x > M) ∧ (∃ x ∈ E, π x < -M) := by
  exact ⟨exists_scalar_above π E w hw hp hy M,
    exists_scalar_below π E w hw hp hy (-M)⟩

theorem commonCarrierPeriod_noncolumnComponents_finite :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane) (periodVec : Plane),
    Module.finrank ℝ δ = 1 → TilesOn K T Set.univ →
    IsCommonCarrierPeriod K δ T periodVec → (noncolumnComponents K δ T).Finite
  := by
  intro K δ T periodVec hδ htile hperiod
  obtain ⟨π, c, hc, hker⟩ := transverseCoordinate hδ
  obtain ⟨R, hR⟩ := K.isPolygonal.isBounded.exists_norm_le
  have hRnonneg : 0 ≤ R := by
    obtain ⟨z, hz⟩ := K.nonempty
    exact (norm_nonneg z).trans (hR z hz)
  let M : ℝ := ‖π‖ * R + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hKπ : ∀ z ∈ K.support, |π z| ≤ M := by
    intro z hz
    have hh := π.le_opNorm_of_le (hR z hz)
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (by dsimp [M]; linarith)
  have hπv : π periodVec ≠ 0 := fun hz => hperiod.1 ((hker _).mpr hz)
  have hw : ∃ w : Plane, 0 < π w ∧
      ∀ P ∈ noncolumnComponents K δ T, w ∈ periodGroup P.carrier := by
    rcases lt_or_gt_of_ne hπv with hn | hp
    · refine ⟨-periodVec, ?_, ?_⟩
      · rw [map_neg]; linarith
      · intro P hP
        exact (periodGroup P.carrier).neg_mem (hperiod.2.2 P hP)
    · exact ⟨periodVec, hp, hperiod.2.2⟩
  obtain ⟨w, hwπ, hwperiod⟩ := hw
  have hInvT : IsInvariantAlong (regularSupport K T) δ := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile]
    exact invariant_univ δ
  apply components_finite_of_bounded_witness htile.2.1
    (B := Metric.closedBall (0 : Plane) ((2 * M) * ‖c‖ + R)) Metric.isBounded_closedBall
  intro P hP
  have hpP := subfamily_packing htile.2.1 (component_centres_subset P)
  obtain ⟨y, hy⟩ := regularSupport_nonempty (component_centres_nonempty P)
  obtain ⟨hpos, hneg⟩ := period_scalar_unbounded π P.carrier w (hwperiod P hP) hwπ hy M
  obtain ⟨t, ht, htπ⟩ := component_bandCentre hker hM hKπ P hpP hpos hneg
  obtain ⟨s, hs, hsbound⟩ := normalize_bandCentre hker hc hpP
    (component_isInvariant K δ T hδ htile.2.1 hInvT P) hKπ hR ht htπ
  exact ⟨s, hs, by simpa only [Metric.mem_closedBall, dist_zero_right] using hsbound⟩

private theorem proper_invariant_subfamily_gives_decomposition
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (S A : Set Plane)
    (hδ : Module.finrank ℝ δ = 1) (hTiles : TilesOn K S univ)
    (hAne : A.Nonempty) (hAS : A ⊆ S) (hAproper : A ≠ S)
    (hAinv : IsInvariantAlong (regularSupport K A) δ) :
    HasNontrivialEarthquakeDecomposition K δ S := by
  have hpack : IsPacking K.prototileFamily (K.placements S) := hTiles.2.1
  have hregular : regularSupport K S = univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTiles
  have hSinv : IsInvariantAlong (regularSupport K S) δ := by
    rw [hregular]
    intro u hu
    simp
  obtain ⟨a, haA⟩ := hAne
  have hnotSub : ¬ S ⊆ A := by
    intro hSA
    exact hAproper (Set.Subset.antisymm hAS hSA)
  obtain ⟨b, hbS, hbA⟩ := Set.not_subset.mp hnotSub
  let G := earthquakeGraph K δ S
  let P : EarthquakeComponent K δ S := G.connectedComponentMk ⟨a, hAS haA⟩
  let Q : EarthquakeComponent K δ S := G.connectedComponentMk ⟨b, hbS⟩
  have haP : a ∈ P.centres := by
    refine ⟨⟨a, hAS haA⟩, ?_, rfl⟩
    rfl
  have hbQ : b ∈ Q.centres := by
    refine ⟨⟨b, hbS⟩, ?_, rfl⟩
    rfl
  have hsplitP := invariantSubfamily_isUnionComponents K δ S A
    hδ hpack hSinv hAS hAinv P
  have hPsub : P.centres ⊆ A := by
    rcases hsplitP with hd | hsub
    · exact (Set.disjoint_left.mp hd haP haA).elim
    · exact hsub
  have hsplitQ := invariantSubfamily_isUnionComponents K δ S A
    hδ hpack hSinv hAS hAinv Q
  have hQdisj : Disjoint Q.centres A := by
    rcases hsplitQ with hd | hsub
    · exact hd
    · exact False.elim (hbA (hsub hbQ))
  have hPQ : P ≠ Q := by
    intro hEq
    have hbP : b ∈ P.centres := by
      rw [hEq]
      exact hbQ
    exact hbA (hPsub hbP)
  exact Or.inr ⟨P, Q, hPQ⟩

private theorem finite_simultaneous_locallyFell_extraction :
    ∀ N : ℕ, ∀ (ε : ℝ) (A : Fin N → ℕ → Set Plane),
      0 < ε → (∀ i n, IsClosed (A i n)) →
      (∀ i n, Tiling.Topology.IsUniformlySeparated ε (A i n)) →
      ∃ (φ : ℕ → ℕ) (V : Fin N → Set Plane), StrictMono φ ∧
        ∀ i, Tiling.Topology.LocallyFellConverges ((A i) ∘ φ) (V i) := by
  intro N
  induction N with
  | zero =>
      intro ε A hε hclosed hsep
      refine ⟨id, (fun i => Fin.elim0 i), strictMono_id, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ N ih =>
      intro ε A hε hclosed hsep
      obtain ⟨φ₁, L, hφ₁, hLclosed, hLsep, hLconv⟩ :=
        Tiling.Topology.exists_locallyFellConvergent_subsequence ε hε (A 0)
          (fun n => hclosed 0 n) (fun n => hsep 0 n)
      let B : Fin N → ℕ → Set Plane := fun i n => A i.succ (φ₁ n)
      have hBclosed : ∀ i n, IsClosed (B i n) := by
        intro i n
        exact hclosed i.succ (φ₁ n)
      have hBsep : ∀ i n, Tiling.Topology.IsUniformlySeparated ε (B i n) := by
        intro i n
        exact hsep i.succ (φ₁ n)
      obtain ⟨φ₂, W, hφ₂, hWconv⟩ := ih ε B hε hBclosed hBsep
      let φ : ℕ → ℕ := φ₁ ∘ φ₂
      let V : Fin (N + 1) → Set Plane := Fin.cases L W
      refine ⟨φ, V, hφ₁.comp hφ₂, ?_⟩
      intro i
      refine Fin.cases ?_ ?_ i
      · have hsub := locallyFell_subsequence hLconv hφ₂
        change Tiling.Topology.LocallyFellConverges (fun n => A 0 (φ₁ (φ₂ n))) L
        exact hsub
      · intro i
        change Tiling.Topology.LocallyFellConverges
          (fun n => A i.succ (φ₁ (φ₂ n))) (W i)
        exact hWconv i

private theorem finite_union_limit_eq
    (N : ℕ) (A : Fin N → ℕ → Set Plane) (V : Fin N → Set Plane)
    (S : Set Plane)
    (hA : ∀ i, Tiling.Topology.LocallyFellConverges (A i) (V i))
    (hS : Tiling.Topology.LocallyFellConverges (fun n => ⋃ i, A i n) S) :
    (⋃ i, V i) = S := by
  have hViClosed : ∀ i, IsClosed (V i) := fun i => (hA i).2.1
  have hUnionClosed : IsClosed (⋃ i, V i) := isClosed_iUnion_of_finite hViClosed
  have hAiSub : ∀ i n, A i n ⊆ ⋃ j, A j n := by
    intro i n x hx
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  have hsubset : ∀ i, V i ⊆ S := by
    intro i
    exact locallyFell_limits_subset (fun n => hAiSub i n) (hA i) hS
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun i => hsubset i
  · intro x hxS
    by_contra hxV
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.mp hUnionClosed.isOpen_compl x hxV
    have hcompact : IsCompact (Metric.closedBall x (ε / 2)) :=
      isCompact_closedBall x (ε / 2)
    have hdisj : Disjoint (⋃ i, V i) (Metric.closedBall x (ε / 2)) := by
      apply Set.disjoint_right.mpr
      intro y hyball hyV
      have hyNot : y ∈ (⋃ i, V i)ᶜ :=
        hball (Metric.closedBall_subset_ball (by linarith) hyball)
      exact hyNot hyV
    have hmissEach : ∀ i, ∀ᶠ n in atTop,
        Disjoint (A i n) (Metric.closedBall x (ε / 2)) := by
      intro i
      have hdisjI : Disjoint (V i) (Metric.closedBall x (ε / 2)) := by
        apply Set.disjoint_left.mpr
        intro y hyI hyball
        exact Set.disjoint_left.mp hdisj
          (Set.mem_iUnion.mpr ⟨i, hyI⟩) hyball
      exact Tiling.Topology.locallyFellConverges_eventually_disjoint_compact
        (hA i) hcompact hdisjI
    have hmiss : ∀ᶠ n in atTop, ∀ i, Disjoint (A i n)
        (Metric.closedBall x (ε / 2)) :=
      Filter.eventually_all.mpr hmissEach
    have hhit := Tiling.Topology.locallyFellConverges_eventually_exists_mem_ball
      hS hxS (by linarith : 0 < ε / 2)
    obtain ⟨n, hnMiss, hnHit⟩ := (hmiss.and hhit).exists
    obtain ⟨y, hyUnion, hyx⟩ := hnHit
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyUnion
    exact Set.disjoint_left.mp (hnMiss i) hyi
      (Metric.mem_closedBall.mpr hyx.le)

private theorem finite_simultaneous_indexed_extraction {I : Type*} [Finite I]
    (ε : ℝ) (A : I → ℕ → Set Plane) (hε : 0 < ε)
    (hclosed : ∀ i n, IsClosed (A i n))
    (hsep : ∀ i n, Tiling.Topology.IsUniformlySeparated ε (A i n)) :
    ∃ (φ : ℕ → ℕ) (V : I → Set Plane), StrictMono φ ∧
      ∀ i, Tiling.Topology.LocallyFellConverges ((A i) ∘ φ) (V i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  obtain ⟨φ, V, hφ, hV⟩ := finite_simultaneous_locallyFell_extraction (Fintype.card I) ε
    (fun i => A (e.symm i)) hε (fun i n => hclosed (e.symm i) n)
    (fun i n => hsep (e.symm i) n)
  refine ⟨φ, fun i => V (e i), hφ, ?_⟩
  intro i
  simpa only [e.symm_apply_apply] using hV (e i)

private theorem finite_union_indexed_limit_eq {I : Type*} [Finite I]
    (A : I → ℕ → Set Plane) (V : I → Set Plane) (S : Set Plane)
    (hA : ∀ i, Tiling.Topology.LocallyFellConverges (A i) (V i))
    (hS : Tiling.Topology.LocallyFellConverges (fun n => ⋃ i, A i n) S) :
    (⋃ i, V i) = S := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hS' : Tiling.Topology.LocallyFellConverges (fun n => ⋃ i, A (e i) n) S := by
    have hfn : (fun n => ⋃ i, A (e i) n) = (fun n => ⋃ i, A i n) :=
      funext fun n => e.surjective.iUnion_comp (fun i => A i n)
    exact hfn.symm ▸ hS
  have hh := finite_union_limit_eq (Fintype.card I) (fun i => A (e i))
    (fun i => V (e i)) S (fun i => hA (e i)) hS'
  simpa only [e.surjective.iUnion_comp] using hh

private theorem actualSubfamily_limit {K : PolygonalRegion} {T A S : Set Plane}
    {g : ℕ → Plane} (htile : TilesOn K T Set.univ) (hAT : A ⊆ T)
    (hfull : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S) :
    ∃ (φ : ℕ → ℕ) (U : Set Plane), StrictMono φ ∧
      Tiling.Topology.LocallyFellConverges (fun n => g (φ n) +ᵥ A) U ∧ U ⊆ S := by
  have hpseq (n : ℕ) : IsPacking K.prototileFamily (K.placements (g n +ᵥ A)) :=
    subfamily_packing (tilesOn_translate htile (g n)).2.1 (Set.vadd_set_mono hAT)
  obtain ⟨ε, hε, hsep⟩ := exists_packingSeparation K
  obtain ⟨φ, U, hφ, _, _, hconv⟩ :=
    Tiling.Topology.exists_locallyFellConvergent_subsequence ε hε (fun n => g n +ᵥ A)
      (fun n => (packing_centres_locallyFinite (hpseq n)).2.2)
      (fun n => hsep _ (hpseq n))
  exact ⟨φ, U, hφ, hconv, locallyFell_limits_subset
    (fun _ => Set.vadd_set_mono hAT) hconv (locallyFell_subsequence hfull hφ)⟩

private theorem columnPart_subset {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} : columnPart K δ T ⊆ T := by
  intro x hx
  obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
  exact component_centres_subset P.1 hxP

private theorem exists_noncolumnComponent_of_notAll {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T : Set Plane} (hne : T ≠ columnPart K δ T) :
    ∃ P ∈ noncolumnComponents K δ T, True := by
  have hnot : ¬ T ⊆ columnPart K δ T := fun h => hne (Subset.antisymm h columnPart_subset)
  obtain ⟨x, hxT, hxC⟩ := Set.not_subset.mp hnot
  rw [← components_partition K δ T] at hxT
  rcases hxT with hcol | hnoncol
  · exact (hxC hcol).elim
  · obtain ⟨P, _⟩ := Set.mem_iUnion.mp hnoncol
    exact ⟨P.1, P.2, trivial⟩

private theorem nonallColumns_limit_decomposition {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T S : Set Plane} {v : Plane} {g : ℕ → Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (hdecomp : HasNontrivialEarthquakeDecomposition K δ T)
    (hperiod : IsCommonCarrierPeriod K δ T v)
    (hg : ∀ n, g n ∈ periodStepGroup δ v)
    (hfull : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S)
    (hne : T ≠ columnPart K δ T) : HasNontrivialEarthquakeDecomposition K δ S := by
  obtain ⟨P, hP, _⟩ := exists_noncolumnComponent_of_notAll hne
  obtain ⟨φ, U, hφ, hUconv, hUS⟩ := actualSubfamily_limit htile (component_centres_subset P) hfull
  have hUsupport : regularSupport K U = P.carrier :=
    component_limit_support_eq_original_carrier hδ htile hperiod (fun n => hg (φ n)) P hP hUconv
  have hUne : U.Nonempty := by
    by_contra he
    have hzero := Set.not_nonempty_iff_eq_empty.mp he
    have hneP := regularSupport_nonempty (K := K) (component_centres_nonempty P)
    rw [hzero, regularSupport_empty] at hUsupport
    exact hneP.ne_empty hUsupport.symm
  have hS : TilesOn K S Set.univ := tilesOn_isClosed
    (fun n => by simpa using tilesOn_translate htile (g n)) hfull
  have hSsupport : regularSupport K S = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) hS
  have hTsupport : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hUproper : U ≠ S := by
    intro heq
    exact noncolumn_carrier_proper htile hdecomp P hP
      (hUsupport.symm.trans (heq ▸ hSsupport))
  have hUInv : IsInvariantAlong (regularSupport K U) δ := by
    rw [hUsupport]
    exact component_isInvariant K δ T hδ htile.2.1 (hTsupport.symm ▸ invariant_univ δ) P
  exact proper_invariant_subfamily_gives_decomposition K δ S U hδ hS hUne hUS hUproper hUInv

private theorem invariant_coordinate_membership {δ : Submodule ℝ Plane}
    {π : Plane →L[ℝ] ℝ} {c : Plane} {E : Set Plane}
    (hker : ∀ z, z ∈ δ ↔ π z = 0) (hc : π c = 1)
    (hInv : IsInvariantAlong E δ) (x : Plane) :
    x ∈ E ↔ π x • c ∈ E := by
  let u : Plane := π x • c - x
  have hu : u ∈ δ := (hker _).mpr (by
    simp only [u, map_sub, map_smul, hc, smul_eq_mul, mul_one, sub_self])
  constructor
  · intro hx
    rw [← hInv u hu]
    exact ⟨x, hx, by simp [u, vadd_eq_add]⟩
  · intro hx
    rw [← hInv (-u) (δ.neg_mem hu)]
    exact ⟨π x • c, hx, by simp [u, vadd_eq_add]⟩

private theorem invariant_section_period {δ : Submodule ℝ Plane}
    {π : Plane →L[ℝ] ℝ} {c : Plane} {E : Set Plane}
    (hker : ∀ z, z ∈ δ ↔ π z = 0) (hc : π c = 1)
    (hInv : IsInvariantAlong E δ) {v : Plane} (hv : v ∈ periodGroup E) :
    π v ∈ periodGroup {r : ℝ | r • c ∈ E} := by
  change π v +ᵥ {r : ℝ | r • c ∈ E} = {r : ℝ | r • c ∈ E}
  ext r
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hx : v + s • c ∈ E := by
      rw [← show v +ᵥ E = E from hv]
      exact ⟨s • c, hs, rfl⟩
    have hh := (invariant_coordinate_membership hker hc hInv _).mp hx
    simpa only [Set.mem_ofPred_eq, map_add, map_smul, hc, smul_eq_mul, mul_one, vadd_eq_add] using hh
  · intro hr
    have hx : -v + r • c ∈ E := by
      rw [← show (-v) +ᵥ E = E from (periodGroup E).neg_mem hv]
      exact ⟨r • c, hr, rfl⟩
    have hh := (invariant_coordinate_membership hker hc hInv _).mp hx
    refine ⟨-π v + r, ?_, by simp [vadd_eq_add]⟩
    simpa only [Set.mem_ofPred_eq, map_add, map_neg, map_smul, hc, smul_eq_mul, mul_one] using hh

private theorem positive_transversePeriods_commensurable {δ : Submodule ℝ Plane}
    {π : Plane →L[ℝ] ℝ} {c : Plane} {D E : Set Plane} {v w : Plane}
    (hker : ∀ z, z ∈ δ ↔ π z = 0) (hc : π c = 1)
    (hDInv : IsInvariantAlong D δ) (hEInv : IsInvariantAlong E δ)
    (hDOpen : IsOpen D) (hEOpen : IsOpen E) (hEne : E.Nonempty)
    (hDproper : D ≠ Set.univ) (hED : E ⊆ D)
    (hv : v ∈ periodGroup D) (hw : w ∈ periodGroup E)
    (hvpos : 0 < π v) (hwpos : 0 < π w) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * π v = (n : ℝ) * π w := by
  let A : Set ℝ := {r | r • c ∈ E}
  let B : Set ℝ := {r | r • c ∈ D}
  have hAopen : IsOpen A := hEOpen.preimage (continuous_id.smul continuous_const)
  have hBopen : IsOpen B := hDOpen.preimage (continuous_id.smul continuous_const)
  have hAne : A.Nonempty := by
    obtain ⟨x, hx⟩ := hEne
    exact ⟨π x, (invariant_coordinate_membership hker hc hEInv x).mp hx⟩
  have hBproper : B ≠ Set.univ := by
    intro hB
    apply hDproper
    apply Set.eq_univ_of_forall
    intro x
    apply (invariant_coordinate_membership hker hc hDInv x).mpr
    have hx : π x ∈ B := by rw [hB]; trivial
    exact hx
  exact periodicOpen_inclusion_commensurable A B (π v) (π w) hAopen hAne
    hBopen hBproper (fun _ h => hED h) hvpos hwpos
    (invariant_section_period hker hc hDInv hv)
    (invariant_section_period hker hc hEInv hw)

private theorem positive_transversePeriod {δ : Submodule ℝ Plane}
    {π : Plane →L[ℝ] ℝ} {D : Set Plane} {v : Plane}
    (hker : ∀ z, z ∈ δ ↔ π z = 0) (hvδ : v ∉ δ)
    (hv : v ∈ periodGroup D) :
    ∃ w : Plane, w ∉ δ ∧ w ∈ periodGroup D ∧ 0 < π w ∧
      periodStepGroup δ w ≤ periodStepGroup δ v := by
  have hπv : π v ≠ 0 := fun hz => hvδ ((hker _).mpr hz)
  have hvmem : v ∈ periodStepGroup δ v :=
    (show AddSubgroup.closure ({v} : Set Plane) ≤ periodStepGroup δ v from le_sup_right)
      (AddSubgroup.subset_closure (Set.mem_singleton v))
  have htransfer {w : Plane} (hw : w ∈ periodStepGroup δ v) :
      periodStepGroup δ w ≤ periodStepGroup δ v :=
    sup_le le_sup_left ((AddSubgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hw))
  rcases lt_or_gt_of_ne hπv with hn | hp
  · refine ⟨-v, ?_, (periodGroup D).neg_mem hv, ?_,
      htransfer ((periodStepGroup δ v).neg_mem hvmem)⟩
    · intro hneg
      exact hvδ (by simpa only [neg_neg] using δ.neg_mem hneg)
    · rw [map_neg]; linarith
  · exact ⟨v, hvδ, hv, hp, le_rfl⟩

private theorem carrierInclusion_commonLattice {δ : Submodule ℝ Plane}
    {D E : Set Plane} {v w : Plane} (hδ : Module.finrank ℝ δ = 1)
    (hDInv : IsInvariantAlong D δ) (hEInv : IsInvariantAlong E δ)
    (hDOpen : IsOpen D) (hEOpen : IsOpen E) (hEne : E.Nonempty)
    (hDproper : D ≠ Set.univ) (hED : E ⊆ D)
    (hvδ : v ∉ δ) (hwδ : w ∉ δ)
    (hv : v ∈ periodGroup D) (hw : w ∈ periodGroup E) :
    ∃ L : PlanarLattice, L.toAddSubgroup ≤ periodStepGroup δ v ∧
      L.toAddSubgroup ≤ periodStepGroup δ w := by
  obtain ⟨π, c, hc, hker⟩ := transverseCoordinate hδ
  obtain ⟨v', hv'δ, hv', hv'pos, hstepv⟩ := positive_transversePeriod hker hvδ hv
  obtain ⟨w', hw'δ, hw', hw'pos, hstepw⟩ := positive_transversePeriod hker hwδ hw
  obtain ⟨m, n, hm, hn, hmn⟩ := positive_transversePeriods_commensurable hker hc
    hDInv hEInv hDOpen hEOpen hEne hDproper hED hv' hw' hv'pos hw'pos
  have hrel : (m : ℤ) • v' - (n : ℤ) • w' ∈ δ := (hker _).mpr (by
    rw [map_sub, map_zsmul, map_zsmul]
    simp only [zsmul_eq_mul, Int.cast_natCast]
    exact sub_eq_zero.mpr hmn)
  obtain ⟨L, hLv, hLw⟩ := commensurableStepGroups_commonLattice δ v' w' hδ hv'δ hw'δ
    ⟨m, n, by exact_mod_cast (ne_of_gt hm), by exact_mod_cast (ne_of_gt hn), hrel⟩
  exact ⟨L, le_trans hLv hstepv, le_trans hLw hstepw⟩

private theorem fixedCarrier_limit_inLattice
    {K : PolygonalRegion} {T C U : Set Plane} {g : ℕ → Plane}
    (hT : TilesOn K T Set.univ) (hCT : C ⊆ T)
    (L : PlanarLattice) (hL : L.toAddSubgroup ≤ periodGroup (regularSupport K C))
    (hconv : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) U) :
    ∃ (a : Plane) (V : Set Plane) (ell : ℕ → Plane),
      (∀ n, ell n ∈ L.toAddSubgroup) ∧
      Tiling.Topology.LocallyFellConverges (fun n => ell n +ᵥ C) V ∧
      Tiling.Topology.LocallyFellConverges (fun n => ell n +ᵥ T) (a +ᵥ U) ∧
      TilesOn K V (regularSupport K C) ∧ V ⊆ a +ᵥ U := by
  classical
  let E : Set Plane := regularSupport K C
  have hCpack : IsPacking K.prototileFamily (K.placements C) := hT.2.1.mono (fun _ h => hCT h)
  have hCtiles : TilesOn K C E := tilesOn_regularSupport_of_packing hCpack
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
    (locallyFell_subsequence hconv hφ) hdlim
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
  have hfull := locallyFell_subsequence hcorrected hψ
  have hVsub : V ⊆ a +ᵥ U := locallyFell_limits_subset (fun _ => Set.vadd_set_mono hCT) hCconv hfull
  exact ⟨a, V, fun n => ell (φ (ψ n)), fun n => (hell (φ (ψ n))).1, hCconv, hfull,
    tilesOn_isClosed (fun n => htilesCseq (ψ n)) hCconv, hVsub⟩

private theorem columnPart_vadd {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (hδ : Module.finrank ℝ δ = 1)
    (htile : TilesOn K T Set.univ) (a : Plane) :
    columnPart K δ (a +ᵥ T) = a +ᵥ columnPart K δ T := by
  have hatile : TilesOn K (a +ᵥ T) Set.univ := by simpa using tilesOn_translate htile a
  have hforward : a +ᵥ columnPart K δ T ⊆ columnPart K δ (a +ᵥ T) :=
    unionColumns_subset_columnPart hδ hatile.2.1 (Set.vadd_set_mono columnPart_subset)
      (unionColumns_vadd (columnPart_isUnionColumns K δ T hδ htile.2.1) a)
  have hsub : (-a) +ᵥ columnPart K δ (a +ᵥ T) ⊆ T := by
    have hh := Set.vadd_set_mono (a := -a) (columnPart_subset (T := a +ᵥ T) (δ := δ) (K := K))
    simpa only [neg_vadd_vadd] using hh
  have hback : (-a) +ᵥ columnPart K δ (a +ᵥ T) ⊆ columnPart K δ T :=
    unionColumns_subset_columnPart hδ htile.2.1 hsub
      (unionColumns_vadd (columnPart_isUnionColumns K δ (a +ᵥ T) hδ hatile.2.1) (-a))
  apply Set.Subset.antisymm ?_ hforward
  intro x hx
  have hmem : -a + x ∈ columnPart K δ T := hback ⟨x, hx, rfl⟩
  exact ⟨-a + x, hmem, by simp [vadd_eq_add]⟩

private theorem backward_columnCarrier_inclusion_inLattice {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {S T : Set Plane} {g : ℕ → Plane}
    (hδ : Module.finrank ℝ δ = 1) (hS : TilesOn K S Set.univ)
    (hT : TilesOn K T Set.univ) (L : PlanarLattice)
    (hL : L.toAddSubgroup ≤ periodGroup (regularSupport K (columnPart K δ S)))
    (hreturn : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ S) T) :
    ∃ a : Plane, regularSupport K (columnPart K δ S) ⊆
      a +ᵥ regularSupport K (columnPart K δ T) := by
  obtain ⟨a, V, ell, _, hpart, _, hVtile, hVsub⟩ :=
    fixedCarrier_limit_inLattice hS columnPart_subset L hL hreturn
  have hcols : IsUnionOfColumns K δ V := unionColumns_closedUnderLimits hδ
    (fun n => (tilesOn_translate (tilesOn_regularSupport_of_packing
      (subfamily_packing hS.2.1 (columnPart_subset (δ := δ)))) (ell n)).2.1)
    (fun n => unionColumns_vadd (columnPart_isUnionColumns K δ S hδ hS.2.1) (ell n)) hpart
  have haT : TilesOn K (a +ᵥ T) Set.univ := by simpa using tilesOn_translate hT a
  have hVC : V ⊆ a +ᵥ columnPart K δ T := by
    rw [← columnPart_vadd hδ hT a]
    exact unionColumns_subset_columnPart hδ haT.2.1 hVsub hcols
  have hsupport : regularSupport K V = regularSupport K (columnPart K δ S) :=
    regularSupport_eq_of_tilesOn (regularSupport_isRegularOpen K _).1
      (regularSupport_isRegularOpen K _).2 hVtile
  refine ⟨a, ?_⟩
  rw [← hsupport, ← regularSupport_vadd]
  exact regularSupport_mono hVC

theorem minimal_columnPartLimit_eq :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T S U : Set Plane)
    (periodVec : Plane) (g : ℕ → Plane), HasRationalSlopes K →
    Module.finrank ℝ δ = 1 → HasBoundaryDirection K δ →
    TilesOn K T Set.univ → IsMinimalTiling K T Set.univ →
    IsUniformlyReady K δ T → HasNontrivialEarthquakeDecomposition K δ T →
    IsCommonCarrierPeriod K δ T periodVec → (∀ n, g n ∈ periodStepGroup δ periodVec) →
    Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S →
    Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ columnPart K δ T) U →
      U = columnPart K δ S
  := by
  intro K δ T S U periodVec g hK hδ hbδ htile hminimal hready hdecomp hperiod hg hfull hpart
  have hS : TilesOn K S Set.univ := tilesOn_isClosed
    (fun n => by simpa using tilesOn_translate htile (g n)) hfull
  have hUS : U ⊆ columnPart K δ S := columnPart_limit_subset_new_columnPart hδ htile hfull hpart
  by_cases hall : T = columnPart K δ T
  · have hTcols : IsUnionOfColumns K δ T := by
      rw [hall]
      exact columnPart_isUnionColumns K δ T hδ htile.2.1
    have hScols : IsUnionOfColumns K δ S := unionColumns_closedUnderLimits hδ
      (fun n => (tilesOn_translate htile (g n)).2.1)
      (fun n => unionColumns_vadd hTcols (g n)) hfull
    have hSall : S = columnPart K δ S := Set.Subset.antisymm
      (unionColumns_subset_columnPart hδ hS.2.1 subset_rfl hScols) columnPart_subset
    rw [← hall] at hpart
    have hSU : S ⊆ U := locallyFell_limits_subset (fun _ => subset_rfl) hfull hpart
    exact Set.Subset.antisymm hUS (hSall ▸ hSU)
  · have hreadyS := uniformlyReady_closedUnderTranslatedLimits K δ T S hδ htile hready g hfull
    have hdecompS := nonallColumns_limit_decomposition hδ htile hdecomp hperiod hg hfull hall
    obtain ⟨vS, hvS⟩ := uniformlyReady_commonCarrierPeriod K δ S hK hδ hbδ hS hreadyS hdecompS
    let pg : ℕ → aePeriodGroup (Set.univ : Set Plane) := fun n =>
      ⟨g n, by simp [aePeriodGroup]⟩
    obtain ⟨h, hreturn⟩ := (isMinimalTiling_iff_returnSequences K T Set.univ htile).mp
      hminimal S ⟨pg, hfull⟩
    obtain ⟨L, hL⟩ := periodStepGroup_containsLattice δ vS hδ hvS.1
    have hSsupport : regularSupport K S = Set.univ :=
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) hS
    have hTsupport : regularSupport K T = Set.univ :=
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
    have hSinv := hSsupport.symm ▸ invariant_univ δ
    have hTinv := hTsupport.symm ▸ invariant_univ δ
    have hCinvS := columnPart_invariant hδ hS.2.1 hSinv
    have hCinvT := columnPart_invariant hδ htile.2.1 hTinv
    have hLcarrier : L.toAddSubgroup ≤ periodGroup (regularSupport K (columnPart K δ S)) :=
      le_trans hL (stepGroup_le_carrierPeriods hCinvS hvS.2.1)
    obtain ⟨a, hback⟩ := backward_columnCarrier_inclusion_inLattice hδ hS htile L hLcarrier hreturn
    have hUsupport := columnPart_limit_support_eq_original_carrier hδ htile hperiod hg hpart
    have hforward : regularSupport K (columnPart K δ T) ⊆ regularSupport K (columnPart K δ S) := by
      rw [← hUsupport]
      exact regularSupport_mono hUS
    have hCperiod := carrier_latticePeriodic_of_commonPeriod hδ hperiod.1 hCinvT hperiod.2.1
    have hcarriereq := (corrected_carrier_inclusions_eq
      (regularSupport_isRegularOpen K _).1 (regularSupport_isRegularOpen K _).2
      hCperiod hforward hback).1
    exact centres_eq_of_subset_support_eq hS.2.1 columnPart_subset hUS
      (hUsupport.trans hcarriereq.symm)

private theorem centres_disjoint_of_carriers_disjoint {K : PolygonalRegion}
    {A B : Set Plane} (hd : Disjoint (regularSupport K A) (regularSupport K B)) :
    Disjoint A B := by
  apply Set.disjoint_left.mpr
  intro t htA htB
  obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
  exact Set.disjoint_left.mp hd (carrier_openPoint htA hz) (carrier_openPoint htB hz)

private theorem plane_mem_aePeriodGroup_univ (u : Plane) :
    u ∈ aePeriodGroup (Set.univ : Set Plane) := by
  simp [aePeriodGroup]

private theorem tilingSpace_translate_centres
    {K : PolygonalRegion} {E : Set Plane}
    (g : aePeriodGroup E) (X : TilingSpace K E) :
    ((TilingSpace.translate g X).centres : Set Plane) =
      (g : Plane) +ᵥ (X.centres : Set Plane) := by
  change (fun x : Plane => x + (g : Plane)) '' (X.centres : Set Plane) =
    (g : Plane) +ᵥ (X.centres : Set Plane)
  ext x
  simp only [mem_image, mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, add_comm _ _⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, add_comm _ _⟩

private theorem minimal_limit_univ
    {K : PolygonalRegion} {T S : Set Plane}
    (hT : TilesOn K T Set.univ)
    (hminimal : IsMinimalTiling K T Set.univ)
    (g : ℕ → Plane)
    (hconv : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S) :
    IsMinimalTiling K S Set.univ := by
  rcases hminimal with ⟨X, hXT, hOrbitMinimal⟩
  have hTseq : ∀ n, TilesOn K (g n +ᵥ T) Set.univ := by
    intro n
    simpa using tilesOn_translate hT (g n)
  have hS : TilesOn K S Set.univ :=
    Tiling.Polygonal.Topology.tilesOn_isClosed hTseq hconv
  let X₀ : TilingSpace K Set.univ := X
  let Y : TilingSpace K Set.univ :=
    ⟨⟨S, (packing_centres_locallyFinite hS.2.1).2.2⟩, hS⟩
  let pg : ℕ → aePeriodGroup (Set.univ : Set Plane) :=
    fun n => ⟨g n, plane_mem_aePeriodGroup_univ (g n)⟩
  have hspaceConv : Tendsto
      (fun n => TilingSpace.translate (pg n) X₀) atTop (𝓝 Y) := by
    apply (Tiling.Polygonal.Topology.locallyFell_metrizable K Set.univ
      (fun n => TilingSpace.translate (pg n) X₀) Y).2
    simpa only [tilingSpace_translate_centres, pg, X₀, Y,
      TopologicalSpace.Closeds.coe_mk, hXT] using hconv
  have hYorbit : Y ∈ orbitHull X₀ :=
    isClosed_closure.mem_of_tendsto hspaceConv
      (Eventually.of_forall fun n => subset_closure ⟨pg n, rfl⟩)
  have hYhull : orbitHull Y = orbitHull X₀ :=
    hOrbitMinimal.2.2.2 Y hYorbit
  refine ⟨Y, ?_, ?_⟩
  · rfl
  · rw [hYhull]
    exact hOrbitMinimal

private theorem minimal_limit_inCarrier {K : PolygonalRegion} {E T S : Set Plane}
    (hminimal : IsMinimalTiling K T E) (g : ℕ → aePeriodGroup E)
    (hconv : Tiling.Topology.LocallyFellConverges (fun n => (g n : Plane) +ᵥ T) S) :
    IsMinimalTiling K S E := by
  obtain ⟨X, hXT, hOrbitMinimal⟩ := hminimal
  have hseq : ∀ n, TilesOn K ((g n : Plane) +ᵥ T) E := by
    intro n
    simpa only [tilingSpace_translate_centres, hXT] using (TilingSpace.translate (g n) X).tilesOn
  have hS : TilesOn K S E := tilesOn_isClosed hseq hconv
  let Y : TilingSpace K E := ⟨⟨S, (packing_centres_locallyFinite hS.2.1).2.2⟩, hS⟩
  have hspace : Tendsto (fun n => TilingSpace.translate (g n) X) atTop (𝓝 Y) := by
    apply (locallyFell_metrizable K E (fun n => TilingSpace.translate (g n) X) Y).2
    simpa only [tilingSpace_translate_centres, Y, TopologicalSpace.Closeds.coe_mk, hXT] using hconv
  have hYorbit : Y ∈ orbitHull X := isClosed_closure.mem_of_tendsto hspace
    (Eventually.of_forall fun n => subset_closure ⟨g n, rfl⟩)
  have hYhull : orbitHull Y = orbitHull X := hOrbitMinimal.2.2.2 Y hYorbit
  refine ⟨Y, rfl, ?_⟩
  rw [hYhull]
  exact hOrbitMinimal

private theorem actual_noncolumn_partition_limit {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T S : Set Plane} {v : Plane} {g : ℕ → Plane}
    (hK : HasRationalSlopes K) (hδ : Module.finrank ℝ δ = 1) (hbδ : HasBoundaryDirection K δ)
    (htile : TilesOn K T Set.univ) (hminimal : IsMinimalTiling K T Set.univ)
    (hready : IsUniformlyReady K δ T) (hdecomp : HasNontrivialEarthquakeDecomposition K δ T)
    (hperiod : IsCommonCarrierPeriod K δ T v) (hg : ∀ n, g n ∈ periodStepGroup δ v)
    (hfull : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S) :
    ∃ (φ : ℕ → ℕ)
      (U : {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T} → Set Plane),
      StrictMono φ ∧
      (∀ P, Tiling.Topology.LocallyFellConverges (fun n => g (φ n) +ᵥ P.1.centres) (U P)) ∧
      (∀ P, regularSupport K (U P) = P.1.carrier) ∧
      regularSupport K (columnPart K δ S) = regularSupport K (columnPart K δ T) ∧
      columnPart K δ S ∪ (⋃ P, U P) = S := by
  classical
  let J := {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}
  have : Finite J := (commonCarrierPeriod_noncolumnComponents_finite K δ T v hδ htile hperiod).to_subtype
  let A : Option J → Set Plane := fun i => match i with
    | none => columnPart K δ T
    | some P => P.1.centres
  have hAT : ∀ i, A i ⊆ T := by
    intro i
    cases i with
    | none => exact columnPart_subset
    | some P => exact component_centres_subset P.1
  have hpack (i : Option J) (n : ℕ) :
      IsPacking K.prototileFamily (K.placements (g n +ᵥ A i)) :=
    subfamily_packing (tilesOn_translate htile (g n)).2.1 (Set.vadd_set_mono (hAT i))
  obtain ⟨ε, hε, hsep⟩ := exists_packingSeparation K
  obtain ⟨φ, V, hφ, hV⟩ := finite_simultaneous_indexed_extraction ε
    (fun i n => g n +ᵥ A i) hε
    (fun i n => (packing_centres_locallyFinite (hpack i n)).2.2)
    (fun i n => hsep _ (hpack i n))
  have hApartition : (⋃ i, A i) = T := by
    rw [Set.iUnion_option]
    exact components_partition K δ T
  have hUnionFn : (fun n => ⋃ i, g (φ n) +ᵥ A i) = (fun n => g (φ n) +ᵥ T) := by
    funext n
    simp only [← Set.image_vadd, ← Set.image_iUnion, hApartition]
  have hfullφ := locallyFell_subsequence hfull hφ
  have hVpartition := finite_union_indexed_limit_eq (fun i n => g (φ n) +ᵥ A i) V S hV
    (hUnionFn.symm ▸ hfullφ)
  have hVcol : V none = columnPart K δ S := minimal_columnPartLimit_eq
    K δ T S (V none) v (fun n => g (φ n)) hK hδ hbδ htile hminimal hready hdecomp hperiod
    (fun n => hg (φ n)) hfullφ (hV none)
  refine ⟨φ, fun P => V (some P), hφ, fun P => hV (some P), ?_, ?_, ?_⟩
  · intro P
    exact component_limit_support_eq_original_carrier hδ htile hperiod (fun n => hg (φ n))
      P.1 P.2 (hV (some P))
  · rw [← hVcol]
    exact columnPart_limit_support_eq_original_carrier hδ htile hperiod (fun n => hg (φ n)) (hV none)
  · rw [Set.iUnion_option, hVcol] at hVpartition
    exact hVpartition

private theorem invariant_partition_parent {I : Type*} {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {S : Set Plane} (A : I → Set Plane)
    (hδ : Module.finrank ℝ δ = 1) (hS : TilesOn K S Set.univ)
    (hne : ∀ i, (A i).Nonempty) (hAS : ∀ i, A i ⊆ S)
    (hInv : ∀ i, IsInvariantAlong (regularSupport K (A i)) δ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hCdisj : ∀ i, Disjoint (columnPart K δ S) (A i))
    (hpartition : columnPart K δ S ∪ (⋃ i, A i) = S) :
    ∃ parent : {Q : EarthquakeComponent K δ S // Q ∈ noncolumnComponents K δ S} → I,
      Function.Surjective parent ∧ (∀ Q, Q.1.centres ⊆ A (parent Q)) ∧
      ∀ i, A i = ⋃ Q : {Q : {Q : EarthquakeComponent K δ S //
        Q ∈ noncolumnComponents K δ S} // parent Q = i}, Q.1.1.centres := by
  classical
  let J := {Q : EarthquakeComponent K δ S // Q ∈ noncolumnComponents K δ S}
  have hSinv : IsInvariantAlong (regularSupport K S) δ := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) hS]
    exact invariant_univ δ
  have hex (Q : J) : ∃ i, Q.1.centres ⊆ A i := by
    obtain ⟨t, htQ⟩ := component_centres_nonempty Q.1
    have htS := component_centres_subset Q.1 htQ
    rw [← hpartition] at htS
    rcases htS with htC | htA
    · exact (Set.disjoint_left.mp (columnPart_disjoint_noncolumn Q.1 Q.2) htC htQ).elim
    · obtain ⟨i, hti⟩ := Set.mem_iUnion.mp htA
      refine ⟨i, ?_⟩
      rcases invariantSubfamily_isUnionComponents K δ S (A i) hδ hS.2.1 hSinv
        (hAS i) (hInv i) Q.1 with hd | hsub
      · exact (Set.disjoint_left.mp hd htQ hti).elim
      · exact hsub
  choose parent hparent using hex
  have hindex {Q : J} {i : I} {t : Plane} (htQ : t ∈ Q.1.centres) (hti : t ∈ A i) :
      parent Q = i := by
    by_contra hneq
    exact Set.disjoint_left.mp (hdisj (parent Q) i hneq) (hparent Q htQ) hti
  have hclass {i : I} {t : Plane} (hti : t ∈ A i) :
      ∃ Q : J, t ∈ Q.1.centres ∧ parent Q = i := by
    let Q : EarthquakeComponent K δ S :=
      (earthquakeGraph K δ S).connectedComponentMk ⟨t, hAS i hti⟩
    have htQ : t ∈ Q.centres := ⟨⟨t, hAS i hti⟩, rfl, rfl⟩
    have hQ : Q ∈ noncolumnComponents K δ S := by
      intro hcol
      have htC : t ∈ columnPart K δ S := Set.mem_iUnion.mpr ⟨⟨Q, hcol⟩, htQ⟩
      exact Set.disjoint_left.mp (hCdisj i) htC hti
    exact ⟨⟨Q, hQ⟩, htQ, hindex (Q := ⟨Q, hQ⟩) htQ hti⟩
  refine ⟨parent, ?_, hparent, ?_⟩
  · intro i
    obtain ⟨t, hti⟩ := hne i
    obtain ⟨Q, _, hQi⟩ := hclass hti
    exact ⟨Q, hQi⟩
  · intro i
    apply Set.Subset.antisymm
    · intro t hti
      obtain ⟨Q, htQ, hQi⟩ := hclass hti
      exact Set.mem_iUnion.mpr ⟨⟨Q, hQi⟩, htQ⟩
    · intro t ht
      obtain ⟨Q, htQ⟩ := Set.mem_iUnion.mp ht
      exact Q.2 ▸ hparent Q.1 htQ

private theorem parent_of_original_carrier_partition {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T S : Set Plane}
    (A : {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T} → Set Plane)
    (hδ : Module.finrank ℝ δ = 1) (hT : TilesOn K T Set.univ) (hS : TilesOn K S Set.univ)
    (hA : ∀ P, regularSupport K (A P) = P.1.carrier)
    (hC : regularSupport K (columnPart K δ S) = regularSupport K (columnPart K δ T))
    (hpartition : columnPart K δ S ∪ (⋃ P, A P) = S) :
    ∃ parent : {Q : EarthquakeComponent K δ S // Q ∈ noncolumnComponents K δ S} →
      {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T},
      Function.Surjective parent ∧ (∀ Q, Q.1.centres ⊆ A (parent Q)) ∧
      ∀ i, A i = ⋃ Q : {Q : {Q : EarthquakeComponent K δ S //
        Q ∈ noncolumnComponents K δ S} // parent Q = i}, Q.1.1.centres := by
  have hTinv : IsInvariantAlong (regularSupport K T) δ := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) hT]
    exact invariant_univ δ
  apply invariant_partition_parent A hδ hS
  · intro P
    by_contra he
    have hnP := regularSupport_nonempty (K := K) (component_centres_nonempty P.1)
    have hzero := Set.not_nonempty_iff_eq_empty.mp he
    have hh := hA P
    rw [hzero, regularSupport_empty] at hh
    exact hnP.ne_empty hh.symm
  · intro P t ht
    rw [← hpartition]
    exact Or.inr (Set.mem_iUnion.mpr ⟨P, ht⟩)
  · intro P
    rw [hA P]
    exact component_isInvariant K δ T hδ hT.2.1 hTinv P.1
  · intro P Q hPQ
    apply centres_disjoint_of_carriers_disjoint
    rw [hA P, hA Q]
    exact regularSupport_disjoint_of_disjoint_subfamilies hT.2.1
      (component_centres_subset P.1) (component_centres_subset Q.1)
      (component_centres_disjoint (fun heq => hPQ (Subtype.ext heq)))
  · intro P
    apply centres_disjoint_of_carriers_disjoint
    rw [hC, hA P]
    exact regularSupport_disjoint_of_disjoint_subfamilies hT.2.1 columnPart_subset
      (component_centres_subset P.1) (columnPart_disjoint_noncolumn P.1 P.2)
  · exact hpartition

private theorem noncolumn_count_monotone {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T S : Set Plane} {v : Plane} {g : ℕ → Plane}
    [Finite {Q : EarthquakeComponent K δ S // Q ∈ noncolumnComponents K δ S}]
    (hK : HasRationalSlopes K) (hδ : Module.finrank ℝ δ = 1) (hbδ : HasBoundaryDirection K δ)
    (hT : TilesOn K T Set.univ) (hminimal : IsMinimalTiling K T Set.univ)
    (hready : IsUniformlyReady K δ T) (hdecomp : HasNontrivialEarthquakeDecomposition K δ T)
    (hperiod : IsCommonCarrierPeriod K δ T v) (hg : ∀ n, g n ∈ periodStepGroup δ v)
    (hfull : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S) :
    Nat.card {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T} ≤
      Nat.card {Q : EarthquakeComponent K δ S // Q ∈ noncolumnComponents K δ S} := by
  obtain ⟨φ, A, _, _, hA, hC, hpartition⟩ :=
    actual_noncolumn_partition_limit hK hδ hbδ hT hminimal hready hdecomp hperiod hg hfull
  have hS : TilesOn K S Set.univ := tilesOn_isClosed
    (fun n => by simpa using tilesOn_translate hT (g n)) hfull
  obtain ⟨parent, hp, _, _⟩ := parent_of_original_carrier_partition A hδ hT hS hA hC hpartition
  exact Nat.card_le_card_of_surjective parent hp

private theorem finite_refinement_single_piece_of_card_le {I J : Type*} [Finite J]
    (parent : J → I) (hp : Function.Surjective parent) (hcard : Nat.card J ≤ Nat.card I)
    (inherited : I → Set Plane) (canonical : J → Set Plane)
    (hcover : ∀ i, inherited i = ⋃ j : {j // parent j = i}, canonical j.1) :
    ∀ i, ∃ j, parent j = i ∧ canonical j = inherited i := by
  have hinj := (hp.bijective_of_nat_card_le hcard).1
  intro i
  obtain ⟨j, hj⟩ := hp i
  refine ⟨j, hj, ?_⟩
  rw [hcover i]
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩
  · intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    have hkj : k.1 = j := hinj (k.2.trans hj.symm)
    exact hkj ▸ hk

private theorem directionalSaturation_vadd
    (δ : Submodule ℝ Plane) (E : Set Plane) (a : Plane) :
    directionalSaturation δ (a +ᵥ E) = a +ᵥ directionalSaturation δ E := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    let z : Plane := (-a) +ᵥ y
    have hz : z ∈ E := by
      have hy' : y = a +ᵥ z := by simp [z]
      rw [hy'] at hy
      exact vadd_mem_vadd_set_iff.mp hy
    have hdiff : ((-a) +ᵥ x) - z = x - y := by
      simp [z, vadd_eq_add]
    have hsat : (-a) +ᵥ x ∈ directionalSaturation δ E :=
      ⟨z, hz, hdiff.symm ▸ hxy⟩
    change ∃ w, w ∈ directionalSaturation δ E ∧ a + w = x
    exact ⟨(-a) +ᵥ x, hsat, by simp [vadd_eq_add]⟩
  · intro hx
    change ∃ w, w ∈ directionalSaturation δ E ∧ a + w = x at hx
    rcases hx with ⟨w, ⟨y, hy, hwy⟩, rfl⟩
    change ∃ y ∈ a +ᵥ E, (a + w) - y ∈ δ
    refine ⟨a + y, ?_, ?_⟩
    · exact vadd_mem_vadd_set_iff.mpr hy
    · simpa [vadd_eq_add] using hwy

private theorem directionalOverlap_vadd
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (a s t : Plane) :
    DirectionalOverlap K δ (a +ᵥ s) (a +ᵥ t) ↔
      DirectionalOverlap K δ s t := by
  have hs : (a +ᵥ s) +ᵥ K.openCarrier =
      a +ᵥ (s +ᵥ K.openCarrier) := by
    ext x
    simp [vadd_vadd]
  rw [DirectionalOverlap, hs, directionalSaturation_vadd]
  have houter (E : Set Plane) :
      (a +ᵥ t) +ᵥ E = a +ᵥ (t +ᵥ E) := by
    ext x
    simp [vadd_vadd]
  constructor
  · rintro ⟨x, hxA, hxB⟩
    have hbackA : (-a) +ᵥ x ∈ s +ᵥ K.openCarrier := by
      have hxA' : x = a +ᵥ ((-a) +ᵥ x) := by simp
      rw [hxA'] at hxA
      exact vadd_mem_vadd_set_iff.mp hxA
    have hbackB : (-a) +ᵥ x ∈ directionalSaturation δ (t +ᵥ K.openCarrier) := by
      have hxB' : x = a +ᵥ ((-a) +ᵥ x) := by simp
      rw [hxB', houter] at hxB
      have htemp : (-a) +ᵥ x ∈ t +ᵥ directionalSaturation δ K.openCarrier :=
        vadd_mem_vadd_set_iff.mp hxB
      exact (directionalSaturation_vadd δ K.openCarrier t).symm ▸ htemp
    exact ⟨(-a) +ᵥ x, hbackA, hbackB⟩
  · rintro ⟨x, hxA, hxB⟩
    refine ⟨a +ᵥ x, ?_, ?_⟩
    · exact vadd_mem_vadd_set_iff.mpr hxA
    · have hsat : a +ᵥ x ∈ a +ᵥ directionalSaturation δ (t +ᵥ K.openCarrier) :=
        vadd_mem_vadd_set_iff.mpr hxB
      rw [directionalSaturation_vadd] at hsat
      have houter : (a +ᵥ t) +ᵥ directionalSaturation δ K.openCarrier =
          a +ᵥ (t +ᵥ directionalSaturation δ K.openCarrier) := by
        ext y
        simp [vadd_vadd]
      rw [houter]
      exact hsat

private theorem centerColumn_vadd_iff {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {C : Set Plane} (a : Plane) :
    IsCenterColumn K δ (a +ᵥ C) ↔ IsCenterColumn K δ C := by
  constructor
  · intro h
    have h' := centerColumn_vadd h (-a)
    simpa [vadd_vadd] using h'
  · exact fun h => centerColumn_vadd h a

private noncomputable def earthquakeGraph_vadd_iso
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane) (a : Plane) :
    earthquakeGraph K δ T ≃g earthquakeGraph K δ (a +ᵥ T) := by
  let f : T ≃ (a +ᵥ T) := Equiv.Set.imageOfInjOn (fun t : Plane => a +ᵥ t)
    T (by
      intro x hx y hy hxy
      exact add_left_cancel hxy)
  refine ⟨f, ?_⟩
  intro s t
  change (f s ≠ f t ∧
      (DirectionalOverlap K δ (f s).1 (f t).1 ∨
        DirectionalOverlap K δ (f t).1 (f s).1)) ↔
    (s ≠ t ∧ (DirectionalOverlap K δ s.1 t.1 ∨
      DirectionalOverlap K δ t.1 s.1))
  rw [f.injective.ne_iff]
  exact and_congr Iff.rfl
    (or_congr (directionalOverlap_vadd K δ a s.1 t.1)
      (directionalOverlap_vadd K δ a t.1 s.1))

private noncomputable def earthquakeComponent_vadd_equiv
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane) (a : Plane) :
    EarthquakeComponent K δ T ≃ EarthquakeComponent K δ (a +ᵥ T) := by
  exact (earthquakeGraph_vadd_iso K δ T a).connectedComponentEquiv

private theorem earthquakeComponent_vadd_centres
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane) (a : Plane)
    (P : EarthquakeComponent K δ T) :
    (earthquakeComponent_vadd_equiv K δ T a P).centres = a +ᵥ P.centres := by
  let hgraph := earthquakeGraph_vadd_iso K δ T a
  let e := earthquakeComponent_vadd_equiv K δ T a
  change (Subtype.val '' (e P).supp) = a +ᵥ (Subtype.val '' P.supp)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    let y' : (e P).supp := ⟨y, hy⟩
    let x' : P.supp := (SimpleGraph.ConnectedComponent.isoEquivSupp hgraph P).symm y'
    have happly := (SimpleGraph.ConnectedComponent.isoEquivSupp hgraph P).apply_symm_apply y'
    have hmap : hgraph.toEquiv x'.1 = y'.1 := by
      change hgraph.toEquiv ((SimpleGraph.ConnectedComponent.isoEquivSupp hgraph P).symm y').1 = y'.1
      exact congrArg Subtype.val happly
    have hval := congrArg Subtype.val hmap
    refine ⟨x'.1.1, ⟨x'.1, x'.2, rfl⟩, ?_⟩
    change a +ᵥ x'.1.1 = y
    exact hval
  · rintro ⟨z, ⟨z', hz, rfl⟩, rfl⟩
    let z'' : P.supp := ⟨z', hz⟩
    let w' : (e P).supp := SimpleGraph.ConnectedComponent.isoEquivSupp hgraph P z''
    refine ⟨w'.1, w'.2, ?_⟩
    rfl

private noncomputable def noncolumnComponents_vadd_equiv
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane) (a : Plane) :
    {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T} ≃
      {P : EarthquakeComponent K δ (a +ᵥ T) //
        P ∈ noncolumnComponents K δ (a +ᵥ T)} := by
  classical
  let e := earthquakeComponent_vadd_equiv K δ T a
  have hcol (P : EarthquakeComponent K δ T) :
      IsCenterColumn K δ P.centres ↔ IsCenterColumn K δ (e P).centres := by
    rw [earthquakeComponent_vadd_centres]
    exact (centerColumn_vadd_iff a).symm
  refine
    { toFun := fun P => ⟨e P.1, ?_⟩
      invFun := fun Q => ⟨e.symm Q.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change ¬ IsCenterColumn K δ (e P.1).centres
    intro hc
    exact P.2 ((hcol P.1).mpr hc)
  · have h := hcol (e.symm Q.1)
    change ¬ IsCenterColumn K δ (e.symm Q.1).centres
    intro hc
    apply Q.2
    simpa only [e.apply_symm_apply] using h.mp hc
  · intro P
    apply Subtype.ext
    exact e.left_inv P.1
  · intro Q
    apply Subtype.ext
    exact e.right_inv Q.1

theorem minimal_componentLimit_isComponent :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T S U : Set Plane)
    (periodVec : Plane) (g : ℕ → Plane), HasRationalSlopes K →
    Module.finrank ℝ δ = 1 → HasBoundaryDirection K δ →
    TilesOn K T Set.univ → IsMinimalTiling K T Set.univ →
    IsUniformlyReady K δ T → HasNontrivialEarthquakeDecomposition K δ T →
    IsCommonCarrierPeriod K δ T periodVec → (∀ n, g n ∈ periodStepGroup δ periodVec) →
    Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S →
      ∀ P ∈ noncolumnComponents K δ T,
        Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ P.centres) U →
          ∃ Q ∈ noncolumnComponents K δ S, Q.centres = U
  := by
  intro K δ T S U periodVec g hK hδ hbδ htile hminimal hready hdecomp hperiod hg hfull P hP hpart
  have hS : TilesOn K S Set.univ := tilesOn_isClosed
    (fun n => by simpa using tilesOn_translate htile (g n)) hfull
  have hTall : T ≠ columnPart K δ T := by
    intro hall
    obtain ⟨t, htP⟩ := component_centres_nonempty P
    have htC : t ∈ columnPart K δ T := hall ▸ component_centres_subset P htP
    exact Set.disjoint_left.mp (columnPart_disjoint_noncolumn P hP) htC htP
  have hdecompS := nonallColumns_limit_decomposition hδ htile hdecomp hperiod hg hfull hTall
  have hreadyS := uniformlyReady_closedUnderTranslatedLimits K δ T S hδ htile hready g hfull
  have hminimalS := minimal_limit_univ htile hminimal g hfull
  obtain ⟨vS, hvS⟩ := uniformlyReady_commonCarrierPeriod K δ S hK hδ hbδ hS hreadyS hdecompS
  let JT := {R : EarthquakeComponent K δ T // R ∈ noncolumnComponents K δ T}
  let JS := {Q : EarthquakeComponent K δ S // Q ∈ noncolumnComponents K δ S}
  have : Finite JT := (commonCarrierPeriod_noncolumnComponents_finite K δ T periodVec hδ htile hperiod).to_subtype
  have : Finite JS := (commonCarrierPeriod_noncolumnComponents_finite K δ S vS hδ hS hvS).to_subtype
  obtain ⟨φ, A, hφ, hAconv, hAcarrier, hCcarrier, hpartition⟩ :=
    actual_noncolumn_partition_limit hK hδ hbδ htile hminimal hready hdecomp hperiod hg hfull
  obtain ⟨parent, hp, hparent, hcover⟩ :=
    parent_of_original_carrier_partition A hδ htile hS hAcarrier hCcarrier hpartition
  let p : JT := ⟨P, hP⟩
  obtain ⟨Q, hQ⟩ := hp p
  have hQAP : Q.1.centres ⊆ A p := hQ ▸ hparent Q
  have hQP : Q.1.carrier ⊆ P.carrier := by
    rw [← hAcarrier p]
    exact regularSupport_mono hQAP
  have hTinv : IsInvariantAlong (regularSupport K T) δ := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile]
    exact invariant_univ δ
  have hSinv : IsInvariantAlong (regularSupport K S) δ := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) hS]
    exact invariant_univ δ
  obtain ⟨L, hLT, hLS⟩ := carrierInclusion_commonLattice hδ
    (component_isInvariant K δ T hδ htile.2.1 hTinv P)
    (component_isInvariant K δ S hδ hS.2.1 hSinv Q.1)
    (regularSupport_isRegularOpen K P.centres).1
    (regularSupport_isRegularOpen K Q.1.centres).1
    (regularSupport_nonempty (K := K) (component_centres_nonempty Q.1))
    (noncolumn_carrier_proper htile hdecomp P hP) hQP
    hperiod.1 hvS.1 (hperiod.2.2 P hP) (hvS.2.2 Q.1 Q.2)
  let pg : ℕ → aePeriodGroup (Set.univ : Set Plane) :=
    fun n => ⟨g n, plane_mem_aePeriodGroup_univ (g n)⟩
  obtain ⟨h, hreturn⟩ := (isMinimalTiling_iff_returnSequences K T Set.univ htile).mp
    hminimal S ⟨pg, hfull⟩
  have hLcolumn : L.toAddSubgroup ≤ periodGroup (regularSupport K (columnPart K δ S)) :=
    le_trans hLS (stepGroup_le_carrierPeriods (columnPart_invariant hδ hS.2.1 hSinv) hvS.2.1)
  obtain ⟨a, V, ell, hell, _, hcorrected, _, _⟩ :=
    fixedCarrier_limit_inLattice hS columnPart_subset L hLcolumn hreturn
  have hellBoth : ∀ n, ell n ∈ periodStepGroup δ periodVec ∧ ell n ∈ periodStepGroup δ vS :=
    fun n => ⟨hLT (hell n), hLS (hell n)⟩
  let e := noncolumnComponents_vadd_equiv K δ T a
  have : Finite {R : EarthquakeComponent K δ (a +ᵥ T) // R ∈ noncolumnComponents K δ (a +ᵥ T)} :=
    Finite.of_injective e.symm e.symm.injective
  have hreverse := noncolumn_count_monotone hK hδ hbδ hS hminimalS hreadyS hdecompS hvS
    (fun n => (hellBoth n).2) hcorrected
  rw [← Nat.card_congr e] at hreverse
  obtain ⟨Q', _, hQ'A⟩ := finite_refinement_single_piece_of_card_le parent hp hreverse A
    (fun Q => Q.1.centres) hcover p
  have hpartφ := locallyFell_subsequence hpart hφ
  have hAU : A p = U := Set.Subset.antisymm
    (locallyFell_limits_subset (fun _ => subset_rfl) (hAconv p) hpartφ)
    (locallyFell_limits_subset (fun _ => subset_rfl) hpartφ (hAconv p))
  exact ⟨Q'.1, Q'.2, hQ'A.trans hAU⟩

theorem minimal_noncolumnComponent_hasFLC :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane) (periodVec : Plane),
    HasRationalSlopes K → Module.finrank ℝ δ = 1 → HasBoundaryDirection K δ →
    TilesOn K T Set.univ → IsMinimalTiling K T Set.univ →
    IsUniformlyReady K δ T → HasNontrivialEarthquakeDecomposition K δ T →
    IsCommonCarrierPeriod K δ T periodVec →
      ∀ P ∈ noncolumnComponents K δ T, HasFLC P.centres
  := by
  intro K δ T v hK hδ hboundary htile hminimal hready hdecomp hv P hP
  by_contra hnflc
  have hsupport : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hInvT : IsInvariantAlong (regularSupport K T) δ := hsupport.symm ▸ invariant_univ δ
  have hInvP := component_isInvariant K δ T hδ htile.2.1 hInvT P
  have hPtile : TilesOn K P.centres P.carrier :=
    tilesOn_regularSupport_of_packing (subfamily_packing htile.2.1 (component_centres_subset P))
  obtain ⟨hPopen, hPreg⟩ := regularSupport_isRegularOpen K P.centres
  obtain ⟨L, hL⟩ := periodStepGroup_containsLattice δ v hδ hv.1
  have hLper : L.toAddSubgroup ≤ aePeriodGroup P.carrier := by
    change L.toAddSubgroup ≤ aePeriodGroup (regularSupport K P.centres)
    rw [aePeriodGroup_eq_periodGroup_of_regularOpen hPopen hPreg]
    exact hL.trans (stepGroup_le_carrierPeriods hInvP (hv.2.2 P hP))
  obtain ⟨U, g, η, hUconv, hUtile, hη, hηboundary, hquake⟩ :=
    nonFLC_earthquakeLimit_inPrescribedLattice K P.centres P.carrier hPtile
      (regularSupport_nonempty (component_centres_nonempty P)) hPopen hPreg hnflc L hLper
  have hfulltile (n : ℕ) : TilesOn K ((g n : Plane) +ᵥ T) Set.univ := by
    simpa using tilesOn_translate htile (g n : Plane)
  obtain ⟨ε, hε, hsep⟩ := exists_packingSeparation K
  obtain ⟨φ, S, hφ, hSclosed, hSsep, hfullconv⟩ :=
    Tiling.Topology.exists_locallyFellConvergent_subsequence ε hε
      (fun n => (g n : Plane) +ᵥ T)
      (fun n => (packing_centres_locallyFinite (hfulltile n).2.1).2.2)
      (fun n => hsep _ (hfulltile n).2.1)
  let u : ℕ → Plane := fun n => (g (φ n) : Plane)
  have hu : ∀ n, u n ∈ periodStepGroup δ v := fun n => hL (g (φ n)).2
  have hfull : Tiling.Topology.LocallyFellConverges (fun n => u n +ᵥ T) S := hfullconv
  have hpart : Tiling.Topology.LocallyFellConverges (fun n => u n +ᵥ P.centres) U :=
    locallyFell_subsequence hUconv hφ
  obtain ⟨Q, hQ, hQcentres⟩ := minimal_componentLimit_isComponent K δ T S U v u
    hK hδ hboundary htile hminimal hready hdecomp hv hu hfull P hP hpart
  have hStile : TilesOn K S Set.univ := tilesOn_isClosed (fun n => hfulltile (φ n)) hfull
  have hSsupport : regularSupport K S = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) hStile
  have hUirreducible : IsIrreducibleDirectionalSubfamily K δ S U :=
    (irreducible_iff_component K δ S U hδ hStile.2.1
      (hSsupport.symm ▸ invariant_univ δ)).mpr ⟨Q, hQcentres⟩
  have hUcarrier : regularSupport K U = P.carrier :=
    regularSupport_eq_of_tilesOn hPopen hPreg hUtile
  obtain ⟨A, hA, hAU, hAne, hAinv⟩ := hquake
  have hηδ : η = δ := invariant_subset_direction_eq hδ hη
    (regularSupport_nonempty hA)
    ((regularSupport_mono hAU).trans_eq hUcarrier) hInvP hAinv
    (noncolumn_carrier_proper htile hdecomp P hP)
  exact hAne (hUirreducible.2.2.2 A hA hAU (hηδ ▸ hAinv))

private theorem commonCarrierPeriod_of_actual_component_equiv {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T S : Set Plane} {v : Plane}
    (e : {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T} ≃
      {Q : EarthquakeComponent K δ S // Q ∈ noncolumnComponents K δ S})
    (hcarrier : ∀ P, (e P).1.carrier = P.1.carrier)
    (hcolumn : regularSupport K (columnPart K δ S) = regularSupport K (columnPart K δ T))
    (hperiod : IsCommonCarrierPeriod K δ T v) : IsCommonCarrierPeriod K δ S v := by
  refine ⟨hperiod.1, ?_, ?_⟩
  · rw [hcolumn]
    exact hperiod.2.1
  · intro Q hQ
    have h : ∀ R : {Q : EarthquakeComponent K δ S // Q ∈ noncolumnComponents K δ S},
        v ∈ periodGroup R.1.carrier := by
      intro R
      obtain ⟨P, rfl⟩ := e.surjective R
      rw [hcarrier P]
      exact hperiod.2.2 P.1 P.2
    exact h ⟨Q, hQ⟩

private theorem step_limit_actual_component_equiv {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T S : Set Plane} {v : Plane} {g : ℕ → Plane}
    (hK : HasRationalSlopes K) (hδ : Module.finrank ℝ δ = 1) (hbδ : HasBoundaryDirection K δ)
    (htile : TilesOn K T Set.univ) (hminimal : IsMinimalTiling K T Set.univ)
    (hready : IsUniformlyReady K δ T) (hdecomp : HasNontrivialEarthquakeDecomposition K δ T)
    (hperiod : IsCommonCarrierPeriod K δ T v) (hg : ∀ n, g n ∈ periodStepGroup δ v)
    (hfull : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S) :
    ∃ (φ : ℕ → ℕ)
      (e : {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T} ≃
        {Q : EarthquakeComponent K δ S // Q ∈ noncolumnComponents K δ S}),
      StrictMono φ ∧
      (∀ P, Tiling.Topology.LocallyFellConverges
        (fun n => g (φ n) +ᵥ P.1.centres) (e P).1.centres) ∧
      (∀ P, (e P).1.carrier = P.1.carrier) ∧ IsCommonCarrierPeriod K δ S v := by
  classical
  obtain ⟨φ, A, hφ, hAconv, hAcarrier, hCcarrier, hpartition⟩ :=
    actual_noncolumn_partition_limit hK hδ hbδ htile hminimal hready hdecomp hperiod hg hfull
  let JT := {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}
  let JS := {Q : EarthquakeComponent K δ S // Q ∈ noncolumnComponents K δ S}
  have hQ : ∀ P : JT, ∃ Q : JS, Q.1.centres = A P := by
    intro P
    obtain ⟨Q, hQ, heq⟩ := minimal_componentLimit_isComponent K δ T S (A P) v
      (fun n => g (φ n)) hK hδ hbδ htile hminimal hready hdecomp hperiod
      (fun n => hg (φ n)) (locallyFell_subsequence hfull hφ) P.1 P.2 (hAconv P)
    exact ⟨⟨Q, hQ⟩, heq⟩
  choose f hf using hQ
  have hfcarrier (P : JT) : (f P).1.carrier = P.1.carrier := by
    change regularSupport K (f P).1.centres = P.1.carrier
    rw [hf P, hAcarrier P]
  have hinj : Function.Injective f := by
    intro P R hPR
    by_contra hne
    have hd := regularSupport_disjoint_of_disjoint_subfamilies htile.2.1
      (component_centres_subset P.1) (component_centres_subset R.1)
      (component_centres_disjoint (fun heq => hne (Subtype.ext heq)))
    have heq : P.1.carrier = R.1.carrier :=
      (hfcarrier P).symm.trans ((congrArg (fun Q : JS => Q.1.carrier) hPR).trans (hfcarrier R))
    obtain ⟨x, hx⟩ := regularSupport_nonempty (K := K) (component_centres_nonempty P.1)
    have hxR : x ∈ R.1.carrier := heq ▸ hx
    exact Set.disjoint_left.mp hd hx hxR
  have hsurj : Function.Surjective f := by
    intro Q
    obtain ⟨t, ht⟩ := component_centres_nonempty Q.1
    have htS := component_centres_subset Q.1 ht
    rw [← hpartition] at htS
    have htA : t ∈ ⋃ P, A P := htS.resolve_left
      (fun hc => Set.disjoint_left.mp (columnPart_disjoint_noncolumn Q.1 Q.2) hc ht)
    obtain ⟨P, htP⟩ := Set.mem_iUnion.mp htA
    have htF : t ∈ (f P).1.centres := (hf P).symm ▸ htP
    refine ⟨P, Subtype.ext ?_⟩
    by_contra hne
    exact Set.disjoint_left.mp (component_centres_disjoint hne) htF ht
  let e : JT ≃ JS := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨φ, e, hφ, ?_, hfcarrier,
    commonCarrierPeriod_of_actual_component_equiv e hfcarrier hCcarrier hperiod⟩
  · intro P
    change Tiling.Topology.LocallyFellConverges _ (f P).1.centres
    rw [hf P]
    exact hAconv P

private theorem minimal_component_limit_preserves_originalCarrier {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T U : Set Plane} {v : Plane} {g : ℕ → Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (hperiod : IsCommonCarrierPeriod K δ T v) (hg : ∀ n, g n ∈ periodStepGroup δ v)
    (P : EarthquakeComponent K δ T) (hP : P ∈ noncolumnComponents K δ T)
    (hminimal : IsMinimalTiling K P.centres P.carrier)
    (hpart : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ P.centres) U) :
    IsMinimalTiling K U P.carrier := by
  have hTinv : IsInvariantAlong (regularSupport K T) δ := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile]
    exact invariant_univ δ
  have hperiods := stepGroup_le_carrierPeriods
    (component_isInvariant K δ T hδ htile.2.1 hTinv P) (hperiod.2.2 P hP)
  let pg : ℕ → aePeriodGroup P.carrier := fun n =>
    ⟨g n, (AddAction.stabilizer_le_aestabilizer (G := Plane) (μ := volume) P.carrier)
      (hperiods (hg n))⟩
  exact minimal_limit_inCarrier hminimal pg hpart

private theorem exists_minimal_carrier_lattice_limit {K : PolygonalRegion}
    {T E : Set Plane} (htile : TilesOn K T E) (hEopen : IsOpen E)
    (hEreg : interior (closure E) = E) (L : PlanarLattice)
    (hL : L.toAddSubgroup ≤ aePeriodGroup E) :
    ∃ (U : Set Plane) (a : aePeriodGroup E) (ell : ℕ → L.toAddSubgroup),
      IsMinimalTiling K U E ∧
      Tiling.Topology.LocallyFellConverges (fun n => (ell n : Plane) +ᵥ T) ((a : Plane) +ᵥ U) := by
  classical
  let X : TilingSpace K E := ⟨⟨T, (packing_centres_locallyFinite htile.2.1).2.2⟩, htile⟩
  obtain ⟨Y, hYhull, hYminimal⟩ := exists_minimalTiling_in_hull X
  obtain ⟨V, hV, hVlim⟩ := mem_closure_iff_seq_limit.mp hYhull
  choose g hg using hV
  have hVeq : (fun n => TilingSpace.translate (g n) X) = V := funext hg
  have hspace := hVeq.symm ▸ hVlim
  have hconv := (locallyFell_metrizable K E (fun n => TilingSpace.translate (g n) X) Y).mp hspace
  have hconv' : Tiling.Topology.LocallyFellConverges
      (fun n => (g n : Plane) +ᵥ (X.centres : Set Plane)) (Y.centres : Set Plane) := by
    simpa only [tilingSpace_translate_centres] using hconv
  obtain ⟨φ, ell, a, _, _, hlimit⟩ := latticeRestricted_hull_limit hEopen hEreg g hconv' L hL
  exact ⟨Y.centres, a, ell, ⟨Y, rfl, hYminimal⟩, hlimit⟩

private theorem aePeriodGroup_vadd_eq (E : Set Plane) (a : Plane) :
    aePeriodGroup (a +ᵥ E) = aePeriodGroup E := by
  ext u
  change (u +ᵥ (a +ᵥ E)) =ᵐ[volume] (a +ᵥ E) ↔
    (u +ᵥ E) =ᵐ[volume] E
  constructor
  · intro hu
    have hq : Measure.QuasiMeasurePreserving (fun x : Plane => -(-a) + x)
        volume volume := by
      simpa using (quasiMeasurePreserving_add_left volume a)
    have h := hq.vadd_ae_eq_of_ae_eq (-a) hu
    simpa [vadd_vadd, add_comm, add_left_comm, add_assoc] using h
  · intro hu
    have hq : Measure.QuasiMeasurePreserving (fun x : Plane => -a + x)
        volume volume := by
      simpa using (quasiMeasurePreserving_add_left volume (-a))
    have h := hq.vadd_ae_eq_of_ae_eq a hu
    simpa [vadd_vadd, add_comm, add_left_comm, add_assoc] using h

private theorem centre_translate_minimal
    {K : PolygonalRegion} {T E : Set Plane} (a : Plane)
    (hT : TilesOn K T E) (hminimal : IsMinimalTiling K T E) :
    IsMinimalTiling K (a +ᵥ T) (a +ᵥ E) := by
  apply (isMinimalTiling_iff_returnSequences K (a +ᵥ T) (a +ᵥ E)
    (tilesOn_translate hT a)).2
  intro L hL
  rcases hL with ⟨g, hg⟩
  have hgroup : aePeriodGroup (a +ᵥ E) = aePeriodGroup E :=
    aePeriodGroup_vadd_eq E a
  let g' : ℕ → aePeriodGroup E := fun n =>
    ⟨g n, by rw [← hgroup]; exact (g n).property⟩
  have hback : Tiling.Topology.LocallyFellConverges (fun n => (g' n : Plane) +ᵥ T)
      ((-a) +ᵥ L) := by
    have h := Tiling.Topology.locallyFell_translate hg (g := fun _ : ℕ => -a)
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => -a) atTop (𝓝 (-a)))
    simpa [g', vadd_vadd, add_comm, add_left_comm, add_assoc] using h
  obtain ⟨h, hh⟩ :=
    (isMinimalTiling_iff_returnSequences K T E hT).1 hminimal _ ⟨g', hback⟩
  let h' : ℕ → aePeriodGroup (a +ᵥ E) := fun n =>
    ⟨h n, by rw [hgroup]; exact (h n).property⟩
  refine ⟨h', ?_⟩
  have hfwd := Tiling.Topology.locallyFell_translate hh (g := fun _ : ℕ => a)
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
  simpa [h', vadd_vadd, add_comm, add_left_comm, add_assoc] using hfwd

private theorem minimal_translate_by_aePeriod {K : PolygonalRegion} {T E : Set Plane}
    (hminimal : IsMinimalTiling K T E) (a : aePeriodGroup E) :
    IsMinimalTiling K ((a : Plane) +ᵥ T) E := by
  obtain ⟨X, hXT, hOrbitMinimal⟩ := hminimal
  have ht : TilesOn K ((a : Plane) +ᵥ T) E := by
    simpa only [tilingSpace_translate_centres, hXT] using (TilingSpace.translate a X).tilesOn
  have hc := (packing_centres_locallyFinite ht.2.1).2.2
  have hminimalT : IsMinimalTiling K T E := ⟨X, hXT, hOrbitMinimal⟩
  exact minimal_limit_inCarrier hminimalT (fun _ => a) ⟨fun _ => hc, hc, tendsto_const_nhds⟩

private theorem minimalize_one_actual_component {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T : Set Plane} {v : Plane}
    (hK : HasRationalSlopes K) (hδ : Module.finrank ℝ δ = 1) (hbδ : HasBoundaryDirection K δ)
    (htile : TilesOn K T Set.univ) (hminimal : IsMinimalTiling K T Set.univ)
    (hready : IsUniformlyReady K δ T) (hdecomp : HasNontrivialEarthquakeDecomposition K δ T)
    (hperiod : IsCommonCarrierPeriod K δ T v)
    (P : {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
    ∃ (S : Set Plane) (g : ℕ → Plane)
      (e : {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T} ≃
        {Q : EarthquakeComponent K δ S // Q ∈ noncolumnComponents K δ S}),
      (∀ n, g n ∈ periodStepGroup δ v) ∧
      Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S ∧
      (∀ R, (e R).1.carrier = R.1.carrier) ∧ IsCommonCarrierPeriod K δ S v ∧
      IsMinimalTiling K (e P).1.centres (e P).1.carrier ∧
      (∀ R, IsMinimalTiling K R.1.centres R.1.carrier →
        IsMinimalTiling K (e R).1.centres (e R).1.carrier) := by
  classical
  have hTinv : IsInvariantAlong (regularSupport K T) δ := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile]
    exact invariant_univ δ
  have hPinv := component_isInvariant K δ T hδ htile.2.1 hTinv P.1
  have hPtile : TilesOn K P.1.centres P.1.carrier :=
    tilesOn_regularSupport_of_packing (subfamily_packing htile.2.1 (component_centres_subset P.1))
  obtain ⟨hPopen, hPreg⟩ := regularSupport_isRegularOpen K P.1.centres
  obtain ⟨L, hL⟩ := periodStepGroup_containsLattice δ v hδ hperiod.1
  have hLper : L.toAddSubgroup ≤ aePeriodGroup P.1.carrier := by
    change L.toAddSubgroup ≤ aePeriodGroup (regularSupport K P.1.centres)
    rw [aePeriodGroup_eq_periodGroup_of_regularOpen hPopen hPreg]
    exact hL.trans (stepGroup_le_carrierPeriods hPinv (hperiod.2.2 P.1 P.2))
  obtain ⟨U, a, ell, hUminimal, hpart⟩ :=
    exists_minimal_carrier_lattice_limit hPtile hPopen hPreg L hLper
  have hpartMinimal := minimal_translate_by_aePeriod hUminimal a
  have hfulltile (n : ℕ) : TilesOn K ((ell n : Plane) +ᵥ T) Set.univ := by
    simpa using tilesOn_translate htile (ell n : Plane)
  obtain ⟨ε, hε, hsep⟩ := exists_packingSeparation K
  obtain ⟨ψ, S, hψ, _, _, hfull⟩ :=
    Tiling.Topology.exists_locallyFellConvergent_subsequence ε hε
      (fun n => (ell n : Plane) +ᵥ T)
      (fun n => (packing_centres_locallyFinite (hfulltile n).2.1).2.2)
      (fun n => hsep _ (hfulltile n).2.1)
  let u : ℕ → Plane := fun n => (ell (ψ n) : Plane)
  have hu : ∀ n, u n ∈ periodStepGroup δ v := fun n => hL (ell (ψ n)).2
  obtain ⟨φ, e, hφ, hconv, hcarrier, hSperiod⟩ :=
    step_limit_actual_component_equiv hK hδ hbδ htile hminimal hready hdecomp hperiod hu hfull
  let g : ℕ → Plane := fun n => u (φ n)
  have hg : ∀ n, g n ∈ periodStepGroup δ v := fun n => hu (φ n)
  have hselected : (e P).1.centres = (a : Plane) +ᵥ U := by
    have hpart' := locallyFell_subsequence (locallyFell_subsequence hpart hψ) hφ
    exact Set.Subset.antisymm
      (locallyFell_limits_subset (fun _ => subset_rfl) (hconv P) hpart')
      (locallyFell_limits_subset (fun _ => subset_rfl) hpart' (hconv P))
  refine ⟨S, g, e, hg, locallyFell_subsequence hfull hφ, hcarrier, hSperiod, ?_, ?_⟩
  · rw [hselected, hcarrier P]
    exact hpartMinimal
  · intro R hRminimal
    rw [hcarrier R]
    exact minimal_component_limit_preserves_originalCarrier hδ htile hperiod hg
      R.1 R.2 hRminimal (hconv R)

private theorem restricted_translated_limits_transitive
    {K : PolygonalRegion} {T S U : Set Plane}
    (hT : TilesOn K T Set.univ) (G : AddSubgroup Plane)
    (g h : ℕ → Plane) (hg : ∀ n, g n ∈ G) (hh : ∀ n, h n ∈ G)
    (hfull : Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S)
    (hlimit : Tiling.Topology.LocallyFellConverges (fun n => h n +ᵥ S) U) :
    ∃ f : ℕ → Plane, (∀ n, f n ∈ G) ∧
      Tiling.Topology.LocallyFellConverges (fun n => f n +ᵥ T) U := by
  let GOrbit : Set (TilingSpace K Set.univ) :=
    Set.range fun v : G =>
      TilingSpace.translate
        (⟨(v : Plane), plane_mem_aePeriodGroup_univ v⟩ :
          aePeriodGroup (Set.univ : Set Plane))
        (⟨⟨T, (packing_centres_locallyFinite hT.2.1).2.2⟩, hT⟩ :
          TilingSpace K Set.univ)
  let X : TilingSpace K Set.univ :=
    ⟨⟨T, (packing_centres_locallyFinite hT.2.1).2.2⟩, hT⟩
  have hTseq : ∀ n, TilesOn K (g n +ᵥ T) Set.univ := by
    intro n
    simpa using tilesOn_translate hT (g n)
  have hS : TilesOn K S Set.univ :=
    Tiling.Polygonal.Topology.tilesOn_isClosed hTseq hfull
  have hSseq : ∀ n, TilesOn K (h n +ᵥ S) Set.univ := by
    intro n
    simpa using tilesOn_translate hS (h n)
  let Yn : ℕ → TilingSpace K Set.univ := fun n =>
    ⟨⟨h n +ᵥ S, (packing_centres_locallyFinite (hSseq n).2.1).2.2⟩,
      hSseq n⟩
  have hYn_mem : ∀ n, Yn n ∈ closure GOrbit := by
    intro n
    let kn : ℕ → aePeriodGroup (Set.univ : Set Plane) := fun m =>
      ⟨h n + g m, plane_mem_aePeriodGroup_univ (h n + g m)⟩
    have htranslated := Tiling.Topology.locallyFell_translate hfull
      (g := fun _ : ℕ => h n)
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => h n) atTop (𝓝 (h n)))
    have hspace : Tendsto (fun m => TilingSpace.translate (kn m) X)
        atTop (𝓝 (Yn n)) := by
      apply (Tiling.Polygonal.Topology.locallyFell_metrizable K Set.univ
        (fun m => TilingSpace.translate (kn m) X) (Yn n)).2
      simpa only [tilingSpace_translate_centres, kn, X, Yn,
        TopologicalSpace.Closeds.coe_mk, vadd_vadd] using htranslated
    apply isClosed_closure.mem_of_tendsto hspace
    filter_upwards with m
    exact subset_closure ⟨⟨h n + g m, G.add_mem (hh n) (hg m)⟩, rfl⟩
  have hU : TilesOn K U Set.univ :=
    Tiling.Polygonal.Topology.tilesOn_isClosed hSseq hlimit
  let Y : TilingSpace K Set.univ :=
    ⟨⟨U, (packing_centres_locallyFinite hU.2.1).2.2⟩, hU⟩
  have hspaceLimit : Tendsto Yn atTop (𝓝 Y) := by
    apply (Tiling.Polygonal.Topology.locallyFell_metrizable K Set.univ Yn Y).2
    simpa only [Yn, Y, TopologicalSpace.Closeds.coe_mk] using hlimit
  have hYmem : Y ∈ closure GOrbit :=
    isClosed_closure.mem_of_tendsto hspaceLimit
      (Eventually.of_forall hYn_mem)
  obtain ⟨V, hV, hVlim⟩ := mem_closure_iff_seq_limit.mp hYmem
  choose f hf using hV
  have hcentres : ∀ n, (V n).centres = (f n : Plane) +ᵥ T := by
    intro n
    rw [← hf n]
    exact tilingSpace_translate_centres
      ⟨(f n : Plane), plane_mem_aePeriodGroup_univ (f n : Plane)⟩ X
  have hconv := (Tiling.Polygonal.Topology.locallyFell_metrizable
    K Set.univ V Y).1 hVlim
  refine ⟨fun n => (f n : Plane), (fun n => (f n).property), ?_⟩
  simpa only [hcentres, Y, TopologicalSpace.Closeds.coe_mk] using hconv

private theorem finite_actual_component_minimalization {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T : Set Plane} {v : Plane}
    (hK : HasRationalSlopes K) (hδ : Module.finrank ℝ δ = 1) (hbδ : HasBoundaryDirection K δ)
    (htile : TilesOn K T Set.univ) (hminimal : IsMinimalTiling K T Set.univ)
    (hready : IsUniformlyReady K δ T) (hdecomp : HasNontrivialEarthquakeDecomposition K δ T)
    (hperiod : IsCommonCarrierPeriod K δ T v)
    (F : Finset {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}) :
    ∃ (S : Set Plane) (g : ℕ → Plane)
      (e : {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T} ≃
        {Q : EarthquakeComponent K δ S // Q ∈ noncolumnComponents K δ S}),
      (∀ n, g n ∈ periodStepGroup δ v) ∧
      Tiling.Topology.LocallyFellConverges (fun n => g n +ᵥ T) S ∧
      (∀ R, (e R).1.carrier = R.1.carrier) ∧ IsCommonCarrierPeriod K δ S v ∧
      ∀ R ∈ F, IsMinimalTiling K (e R).1.centres (e R).1.carrier := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      have hc := (packing_centres_locallyFinite htile.2.1).2.2
      refine ⟨T, fun _ => 0, Equiv.refl _, fun _ => zero_mem _, ?_,
        fun _ => rfl, hperiod, ?_⟩
      · simpa only [zero_vadd] using
          (show Tiling.Topology.LocallyFellConverges (fun _ : ℕ => T) T from
            ⟨fun _ => hc, hc, tendsto_const_nhds⟩)
      · simp
  | @insert P F hPF ih =>
      obtain ⟨S, g, e, hg, hfull, hcarrier, hSperiod, hprev⟩ := ih
      have hS : TilesOn K S Set.univ := tilesOn_isClosed
        (fun n => by simpa using tilesOn_translate htile (g n)) hfull
      have hSminimal := minimal_limit_univ htile hminimal g hfull
      have hSready := uniformlyReady_closedUnderTranslatedLimits K δ T S hδ htile hready g hfull
      have hTall : T ≠ columnPart K δ T := by
        intro hall
        obtain ⟨t, ht⟩ := component_centres_nonempty P.1
        have htC : t ∈ columnPart K δ T := hall ▸ component_centres_subset P.1 ht
        exact Set.disjoint_left.mp (columnPart_disjoint_noncolumn P.1 P.2) htC ht
      have hSdecomp := nonallColumns_limit_decomposition hδ htile hdecomp hperiod hg hfull hTall
      obtain ⟨U, h, f, hh, hlimit, hfcarrier, hUperiod, hselected, hpreserve⟩ :=
        minimalize_one_actual_component hK hδ hbδ hS hSminimal hSready hSdecomp hSperiod (e P)
      obtain ⟨k, hk, hfinal⟩ := restricted_translated_limits_transitive
        htile (periodStepGroup δ v) g h hg hh hfull hlimit
      refine ⟨U, k, e.trans f, hk, hfinal, ?_, hUperiod, ?_⟩
      · intro R
        exact (hfcarrier (e R)).trans (hcarrier R)
      · intro R hR
        rcases Finset.mem_insert.mp hR with hRP | hRF
        · subst R
          exact hselected
        · exact hpreserve (e R) (hprev R hRF)

theorem minimal_noncolumnComponent_isMinimal :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane) (periodVec : Plane),
    HasRationalSlopes K → Module.finrank ℝ δ = 1 → HasBoundaryDirection K δ →
    TilesOn K T Set.univ → IsMinimalTiling K T Set.univ →
    IsUniformlyReady K δ T → HasNontrivialEarthquakeDecomposition K δ T →
    IsCommonCarrierPeriod K δ T periodVec →
      ∀ P ∈ noncolumnComponents K δ T, IsMinimalTiling K P.centres P.carrier
  := by
  intro K δ T v hK hδ hbδ htile hminimal hready hdecomp hperiod P hP
  classical
  let JT := {R : EarthquakeComponent K δ T // R ∈ noncolumnComponents K δ T}
  have : Finite JT :=
    (commonCarrierPeriod_noncolumnComponents_finite K δ T v hδ htile hperiod).to_subtype
  let : Fintype JT := Fintype.ofFinite JT
  obtain ⟨S, g, e, hg, hfull, hcarrier, hSperiod, hpieces⟩ :=
    finite_actual_component_minimalization hK hδ hbδ htile hminimal hready hdecomp hperiod
      (Finset.univ : Finset JT)
  have hS : TilesOn K S Set.univ := tilesOn_isClosed
    (fun n => by simpa using tilesOn_translate htile (g n)) hfull
  have hSminimal := minimal_limit_univ htile hminimal g hfull
  have hSready := uniformlyReady_closedUnderTranslatedLimits K δ T S hδ htile hready g hfull
  have hTall : T ≠ columnPart K δ T := by
    intro hall
    obtain ⟨t, ht⟩ := component_centres_nonempty P
    have htC : t ∈ columnPart K δ T := hall ▸ component_centres_subset P ht
    exact Set.disjoint_left.mp (columnPart_disjoint_noncolumn P hP) htC ht
  have hSdecomp := nonallColumns_limit_decomposition hδ htile hdecomp hperiod hg hfull hTall
  have hAllS (R : {R : EarthquakeComponent K δ S // R ∈ noncolumnComponents K δ S}) :
      IsMinimalTiling K R.1.centres R.1.carrier := by
    obtain ⟨A, rfl⟩ := e.surjective R
    exact hpieces A (Finset.mem_univ A)
  let pg : ℕ → aePeriodGroup (Set.univ : Set Plane) :=
    fun n => ⟨g n, plane_mem_aePeriodGroup_univ (g n)⟩
  obtain ⟨h, hreturn⟩ := (isMinimalTiling_iff_returnSequences K T Set.univ htile).mp
    hminimal S ⟨pg, hfull⟩
  obtain ⟨L, hL⟩ := periodStepGroup_containsLattice δ v hδ hperiod.1
  have hSinv : IsInvariantAlong (regularSupport K S) δ := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) hS]
    exact invariant_univ δ
  have hLcolumn : L.toAddSubgroup ≤ periodGroup (regularSupport K (columnPart K δ S)) :=
    hL.trans (stepGroup_le_carrierPeriods (columnPart_invariant hδ hS.2.1 hSinv) hSperiod.2.1)
  obtain ⟨a, _, ell, hell, _, hcorrected, _, _⟩ :=
    fixedCarrier_limit_inLattice hS columnPart_subset L hLcolumn hreturn
  have hellStep : ∀ n, ell n ∈ periodStepGroup δ v := fun n => hL (hell n)
  obtain ⟨φ, f, hφ, hpart, hfcarrier, _⟩ :=
    step_limit_actual_component_equiv hK hδ hbδ hS hSminimal hSready hSdecomp
      hSperiod hellStep hcorrected
  let z := noncolumnComponents_vadd_equiv K δ T a
  let p : JT := ⟨P, hP⟩
  let R := f.symm (z p)
  have hRminimal := hAllS R
  have hQminimal : IsMinimalTiling K (z p).1.centres (z p).1.carrier := by
    have hm : IsMinimalTiling K (f R).1.centres (f R).1.carrier := by
      rw [hfcarrier R]
      exact minimal_component_limit_preserves_originalCarrier hδ hS hSperiod
        (fun n => hellStep (φ n)) R.1 R.2 hRminimal (hpart R)
    simpa only [R, Equiv.apply_symm_apply] using hm
  have haT : TilesOn K (a +ᵥ T) Set.univ := by
    simpa using tilesOn_translate htile a
  have hQtile : TilesOn K (z p).1.centres (z p).1.carrier :=
    tilesOn_regularSupport_of_packing
      (subfamily_packing haT.2.1 (component_centres_subset (z p).1))
  have hback := centre_translate_minimal (-a) hQtile hQminimal
  have hzcentres : (z p).1.centres = a +ᵥ P.centres :=
    earthquakeComponent_vadd_centres K δ T a P
  have hzcarrier : (z p).1.carrier = a +ᵥ P.carrier := by
    change regularSupport K (z p).1.centres = a +ᵥ regularSupport K P.centres
    rw [hzcentres, regularSupport_vadd]
  simpa only [hzcentres, hzcarrier, vadd_vadd, neg_add_cancel, zero_vadd] using hback

private theorem wholePlane_structure_of_hasFLC {K : PolygonalRegion} {T : Set Plane}
    (htile : TilesOn K T Set.univ) (hminimal : IsMinimalTiling K T Set.univ)
    (hflc : HasFLC T) : Nonempty (MinimalWholePlaneStructure K T) := by
  classical
  let δ : Submodule ℝ Plane := Submodule.span ℝ ({(1 : Plane)} : Set Plane)
  have hδ : Module.finrank ℝ δ = 1 := finrank_span_singleton (by norm_num)
  have hrat : HasRationalDirection δ := by
    refine ⟨![1, 0], ?_, ?_⟩
    · intro hz
      have h0 := congrArg (fun z : Tiling.RationalPolygonal.IntegerPlane => z 0) hz
      norm_num at h0
    · have hpoint : Tiling.RationalPolygonal.integerPoint ![1, 0] = (1 : Plane) := by
        norm_num [Tiling.RationalPolygonal.integerPoint]
      rw [hpoint]
      exact Submodule.subset_span (Set.mem_singleton 1)
  have hsupport : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hTne : T.Nonempty := by
    by_contra h
    have hT : T = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [hT, regularSupport_empty] at hsupport
    exact Set.empty_ne_univ hsupport
  refine ⟨{
    direction := δ
    direction_oneDim := hδ
    direction_rational := hrat
    columnAggregate := ∅
    aggregate_isUnionColumns := by intro t ht; simp at ht
    numberOfPieces := 1
    piece := fun _ => T
    piece_nonempty := fun _ => hTne
    pieces_pairwiseDisjoint := ?_
    column_disjoint_piece := by intro j; simp
    centres_partition := by
      change (∅ : Set Plane) ∪ (⋃ _ : Fin 1, T) = T
      rw [Set.empty_union]
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
        exact hj
      · intro x hx
        exact Set.mem_iUnion.mpr ⟨(0 : Fin 1), hx⟩
    piece_hasFLC := fun _ => hflc
    piece_minimal := fun _ => hsupport.symm ▸ hminimal
    aggregate_invariant := by rw [regularSupport_empty]; intro u hu; simp
    piece_invariant := fun _ => hsupport.symm ▸ invariant_univ δ
    aggregate_carrier_periodic := by rw [regularSupport_empty]; exact empty_latticePeriodic
    piece_carrier_periodic := fun _ => hsupport.symm ▸ univ_latticePeriodic
  }⟩
  intro i hi j hj hij
  exact (hij (Subsingleton.elim i j)).elim

private theorem wholePlane_structure_of_allColumns {K : PolygonalRegion} {T : Set Plane}
    {δ : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1)
    (hrat : HasRationalDirection δ) (htile : TilesOn K T Set.univ)
    (hcols : IsUnionOfColumns K δ T) : Nonempty (MinimalWholePlaneStructure K T) := by
  have hsupport : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  exact ⟨{
    direction := δ
    direction_oneDim := hδ
    direction_rational := hrat
    columnAggregate := T
    aggregate_isUnionColumns := hcols
    numberOfPieces := 0
    piece := Fin.elim0
    piece_nonempty := fun j => Fin.elim0 j
    pieces_pairwiseDisjoint := by intro i; exact Fin.elim0 i
    column_disjoint_piece := fun j => Fin.elim0 j
    centres_partition := by simp
    piece_hasFLC := fun j => Fin.elim0 j
    piece_minimal := fun j => Fin.elim0 j
    aggregate_invariant := hsupport.symm ▸ invariant_univ δ
    piece_invariant := fun j => Fin.elim0 j
    aggregate_carrier_periodic := hsupport.symm ▸ univ_latticePeriodic
    piece_carrier_periodic := fun j => Fin.elim0 j
  }⟩


theorem minimal_wholePlane_structure :
∀ (K : PolygonalRegion) (T : Set Plane), HasRationalSlopes K →
    TilesOn K T Set.univ → IsMinimalTiling K T Set.univ →
      Nonempty (MinimalWholePlaneStructure K T)
  := by
  intro K T hK htile hminimal
  classical
  by_cases hflc : HasFLC T
  · exact wholePlane_structure_of_hasFLC htile hminimal hflc
  · obtain ⟨δ, hδ, hboundary, hrat, hready, hdecomp⟩ :=
      minimal_nonFLC_uniformlyReady K T hK htile hminimal hflc
    by_cases hcolumns : T = columnPart K δ T
    · apply wholePlane_structure_of_allColumns hδ hrat htile
      simpa only [← hcolumns] using columnPart_isUnionColumns K δ T hδ htile.2.1
    -- This branch has a noncolumn piece; no such witness is selected in the column branch.
    · obtain ⟨v, hv⟩ := uniformlyReady_commonCarrierPeriod K δ T
        hK hδ hboundary htile hready hdecomp
      have hfinite := commonCarrierPeriod_noncolumnComponents_finite K δ T v hδ htile hv
      let J := {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T}
      let : Fintype J := hfinite.fintype
      let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
      have hsupport : regularSupport K T = Set.univ :=
        regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
      have hInv : IsInvariantAlong (regularSupport K T) δ :=
        hsupport ▸ invariant_univ δ
      have hcinv : IsInvariantAlong (regularSupport K (columnPart K δ T)) δ :=
        columnPart_invariant hδ htile.2.1 hInv
      have hpiece_union :
          (⋃ j : Fin (Fintype.card J), (e j).1.centres) = ⋃ P : J, P.1.centres := by
        ext x
        constructor
        · intro hx
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨e j, hj⟩
        · intro hx
          obtain ⟨P, hP⟩ := Set.mem_iUnion.mp hx
          obtain ⟨j, rfl⟩ := e.surjective P
          exact Set.mem_iUnion.mpr ⟨j, hP⟩
      refine ⟨{
        direction := δ
        direction_oneDim := hδ
        direction_rational := hrat
        columnAggregate := columnPart K δ T
        aggregate_isUnionColumns := columnPart_isUnionColumns K δ T hδ htile.2.1
        numberOfPieces := Fintype.card J
        piece := fun j => (e j).1.centres
        piece_nonempty := fun j => component_centres_nonempty (e j).1
        pieces_pairwiseDisjoint := ?_
        column_disjoint_piece := fun j => columnPart_disjoint_noncolumn (e j).1 (e j).2
        centres_partition := ?_
        piece_hasFLC := fun j => minimal_noncolumnComponent_hasFLC
          K δ T v hK hδ hboundary htile hminimal hready hdecomp hv (e j).1 (e j).2
        piece_minimal := fun j => minimal_noncolumnComponent_isMinimal
          K δ T v hK hδ hboundary htile hminimal hready hdecomp hv (e j).1 (e j).2
        aggregate_invariant := hcinv
        piece_invariant := fun j => component_isInvariant K δ T hδ htile.2.1 hInv (e j).1
        aggregate_carrier_periodic := carrier_latticePeriodic_of_commonPeriod hδ hv.1 hcinv hv.2.1
        piece_carrier_periodic := fun j => carrier_latticePeriodic_of_commonPeriod hδ hv.1
          (component_isInvariant K δ T hδ htile.2.1 hInv (e j).1) (hv.2.2 (e j).1 (e j).2)
      }⟩
      · intro i hi j hj hij
        apply component_centres_disjoint
        intro heq
        exact hij (e.injective (Subtype.ext heq))
      · rw [hpiece_union]
        exact components_partition K δ T


-- Actual predecessor-closure audit; all skeleton-backed consumers are provisional.

end Tiling.RationalSlopes
