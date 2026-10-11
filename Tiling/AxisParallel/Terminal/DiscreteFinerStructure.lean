import Tiling.AxisParallel.Foundations.ExternalInputs
import Tiling.AxisParallel.Terminal.DirectionalCore
import Tiling.RationalPolygonal.DiscreteCarrier
import TranslationalTilings.PeriodicCompletion

/-!
# Finer structure for a discrete planar tiling

This module packages the Greenfeld--Tao directional decomposition, completion, and slicing
interfaces into the finite family of complete slice orbits used by the terminal argument.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Set
open scoped BigOperators

namespace Tiling.AxisParallel.Terminal

private theorem indicator_eq_iff_membership {G : Type*}
    (S : Set G) (x y : G) :
    TranslationalTilings.setIndicator S x =
        TranslationalTilings.setIndicator S y ↔ (x ∈ S ↔ y ∈ S) := by
  classical
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
    simp [TranslationalTilings.setIndicator, hx, hy]

private def quarterTurn
    (v : TranslationalTilings.Plane) : TranslationalTilings.Plane :=
  ![-v 1, v 0]

private theorem wedge_quarterTurn_self_ne_zero
    {v : TranslationalTilings.Plane} (hv : v ≠ 0) :
    TranslationalTilings.wedge (quarterTurn v) v ≠ 0 := by
  intro hw
  have hw' : -(v 1 * v 1) - v 0 * v 0 = 0 := by
    simpa [TranslationalTilings.wedge, quarterTurn] using hw
  have hv0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have hv1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  apply hv
  funext i
  fin_cases i <;> assumption

private theorem wedge_coordinate_identity
    (h g u : TranslationalTilings.Plane) :
    TranslationalTilings.wedge u g • h +
        TranslationalTilings.wedge h u • g =
      TranslationalTilings.wedge h g • u := by
  funext i
  fin_cases i <;> simp [TranslationalTilings.wedge] <;> ring

private theorem exists_discreteFinerStructure_of_directional
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {ell base : ℕ}
    (hF : F.Nonempty) (hell : 0 < ell)
    (hE : TranslationalTilings.SetScalarPeriodic ell E)
    (hTile : TranslationalTilings.Tiles F A E)
    (D : TranslationalTilings.DirectionalTilingDecomposition F A E base)
    (hbase : 0 < base) (hA : A.Nonempty) :
    Nonempty (DiscreteFinerStructureData F A E ell) := by
  classical
  let Active := {j : Fin D.numberOfParts // (D.part j).Nonempty}
  let m := Fintype.card Active
  let activeEquiv : Active ≃ Fin m := Fintype.equivFin Active
  let index : Fin m → Fin D.numberOfParts := fun i ↦ (activeEquiv.symm i).1
  let part : Fin m → Set TranslationalTilings.Plane := fun i ↦ D.part (index i)
  have hpartNonempty (i : Fin m) : (part i).Nonempty :=
    (activeEquiv.symm i).2
  have hpartSubset (i : Fin m) : part i ⊆ A := by
    intro x hx
    rw [← D.union_parts]
    exact Set.mem_iUnion.mpr ⟨index i, hx⟩
  have hindexInjective : Function.Injective index := by
    intro i j hij
    apply activeEquiv.symm.injective
    apply Subtype.ext
    exact hij
  have hpartsDisjoint : Set.PairwiseDisjoint Set.univ part := by
    intro i _hi j _hj hij
    exact D.pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _)
      (hindexInjective.ne hij)
  have hpartsUnion : (⋃ i, part i) = A := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact hpartSubset i hxi
    · intro x hx
      rw [← D.union_parts] at hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      have hjNonempty : (D.part j).Nonempty := ⟨x, hxj⟩
      let a : Active := ⟨j, hjNonempty⟩
      let i : Fin m := activeEquiv a
      have hindex : index i = j := by
        change (activeEquiv.symm (activeEquiv a)).1 = j
        simp [a]
      exact Set.mem_iUnion.mpr ⟨i, by simpa [part, hindex] using hxj⟩
  have hmpos : 0 < m := by
    obtain ⟨x, hx⟩ := hA
    rw [← hpartsUnion] at hx
    obtain ⟨i, _hxi⟩ := Set.mem_iUnion.mp hx
    exact Nat.pos_of_ne_zero fun hm ↦ Fin.elim0 (hm ▸ i)
  let u : Fin m → TranslationalTilings.Plane := fun i ↦
    TranslationalTilings.primitivePart (D.direction (index i))
  let content : Fin m → ℕ := fun i ↦
    TranslationalTilings.vectorContent (D.direction (index i))
  have huPrimitive (i : Fin m) : TranslationalTilings.IsPrimitive (u i) :=
    (TranslationalTilings.primitive_decomposition
      (D.direction_ne_zero (index i))).2
  have huNe (i : Fin m) : u i ≠ 0 := (huPrimitive i).1
  have hcontentPos (i : Fin m) : 0 < content i :=
    TranslationalTilings.vectorContent_pos (D.direction_ne_zero (index i))
  have hdirection (i : Fin m) :
      (content i : ℤ) • u i = D.direction (index i) :=
    (TranslationalTilings.primitive_decomposition
      (D.direction_ne_zero (index i))).1
  obtain ⟨N, hNpos, hcarrierPeriodic⟩ :=
    Tiling.AxisParallel.Foundations.gtCommonDirectionalCarrierPeriod D hbase
  let k : Fin m → ℕ := fun i ↦ base * content i
  have hkPos (i : Fin m) : 0 < k i :=
    Nat.mul_pos hbase (hcontentPos i)
  have hpartPeriodic (i : Fin m) :
      Function.Periodic (TranslationalTilings.setIndicator (part i))
        (((N * k i : ℕ) : ℤ) • u i) := by
    have hp := (D.periodic_part (index i)).zsmul (N : ℤ)
    have hshift : (((N * k i : ℕ) : ℤ) • u i) =
        (N : ℤ) • ((base : ℤ) • D.direction (index i)) := by
      rw [← hdirection i]
      dsimp [k]
      module
    simpa only [part, hshift] using hp
  have hconvPeriodic (i : Fin m) :
      TranslationalTilings.ScalarPeriodic N
        (TranslationalTilings.tileConv F
          (TranslationalTilings.setIndicator (part i))) := by
    rw [Tiling.RationalPolygonal.tileConv_indicator_eq_indicator_discreteCarrier
      hTile (hpartSubset i)]
    intro x z
    apply (indicator_eq_iff_membership
      (Tiling.RationalPolygonal.discreteCarrier F (part i)) _ _).2
    exact hcarrierPeriodic (index i) x z
  let modulus : Fin m → ℕ := fun i ↦
    TranslationalTilings.indicatorDilationModulus N F.card * k i *
      TranslationalTilings.slicingLCM F (u i)
  have hmodulusPos (i : Fin m) : 0 < modulus i := by
    exact Nat.mul_pos
      (Nat.mul_pos
        (by simpa [TranslationalTilings.indicatorDilationModulus] using
          (TranslationalTilings.dilationModulus_pos
            (oscillation := 1) (tileCard := F.card) hNpos))
        (hkPos i))
      (TranslationalTilings.slicingLCM_pos F (u i))
  let scale : ℕ := ∏ i : Fin m, modulus i
  have hscalePos : 0 < scale := by
    dsimp [scale]
    exact Finset.prod_pos fun i _ ↦ hmodulusPos i
  have hmodulusDvdScale (i : Fin m) : modulus i ∣ scale := by
    simpa [scale] using
      (Finset.dvd_prod_of_mem modulus (Finset.mem_univ i))
  let v : TranslationalTilings.Plane := TranslationalTilings.avoidanceVector u
  have hvSpec := TranslationalTilings.avoidanceVector_spec huNe
  have hvNe : v ≠ 0 := hvSpec.1
  let h : TranslationalTilings.Plane := quarterTurn v
  let g : TranslationalTilings.Plane := (scale : ℤ) • v
  have hgNe : g ≠ 0 := by
    exact smul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hscalePos)) hvNe
  have hhg : TranslationalTilings.wedge h g ≠ 0 := by
    rw [show g = (scale : ℤ) • v by rfl,
      TranslationalTilings.wedge_zsmul_right]
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hscalePos))
      (wedge_quarterTurn_self_ne_zero hvNe)
  have huWedgeG (i : Fin m) :
      TranslationalTilings.wedge (u i) g ≠ 0 := by
    rw [show g = (scale : ℤ) • v by rfl,
      TranslationalTilings.wedge_zsmul_right]
    refine mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hscalePos)) ?_
    rw [TranslationalTilings.wedge_swap]
    exact neg_ne_zero.mpr fun hw ↦ hvSpec.2.1 i
      ((TranslationalTilings.commensurable_iff_wedge_eq_zero hvNe (huNe i)).2 hw)
  let direction : Fin m → DiscreteDirection h g := fun i ↦ {
    primitiveVector := u i
    primitive := huPrimitive i
    hCoefficient := TranslationalTilings.wedge (u i) g
    gCoefficient := TranslationalTilings.wedge h (u i)
    hCoefficient_ne_zero := huWedgeG i
    multiple := TranslationalTilings.wedge h g
    multiple_ne_zero := hhg
    period_eq := wedge_coordinate_identity h g (u i)
  }
  have hNkDvdScale (i : Fin m) : N * k i ∣ scale := by
    apply dvd_trans ?_ (hmodulusDvdScale i)
    apply dvd_mul_of_dvd_left _ (TranslationalTilings.slicingLCM F (u i))
    apply Nat.mul_dvd_mul_right
      (show N ∣ TranslationalTilings.indicatorDilationModulus N F.card by
        exact TranslationalTilings.ell_dvd_dilationModulus N 1 F.card)
  have hwithinPeriodic (i : Fin m) (Q : TranslationalTilings.Plane ⧸
      TranslationalTilings.directionSubgroup (u i)) :
      Tiling.RationalPolygonal.DiscretePeriodicBy
        (DiscreteSlice (u i) Q (part i)) (direction i).period := by
    obtain ⟨q, hq⟩ := hNkDvdScale i
    have hdet : TranslationalTilings.wedge h g =
        ((q : ℤ) * TranslationalTilings.wedge h v) *
          ((N * k i : ℕ) : ℤ) := by
      rw [show g = (scale : ℤ) • v by rfl,
        TranslationalTilings.wedge_zsmul_right]
      have hscale : scale = N * k i * q := hq
      rw [hscale]
      push_cast
      ring
    have hp : Function.Periodic
        (TranslationalTilings.setIndicator (part i)) (direction i).period := by
      have hp' := (hpartPeriodic i).zsmul
        ((q : ℤ) * TranslationalTilings.wedge h v)
      have hshift : (direction i).period =
          ((q : ℤ) * TranslationalTilings.wedge h v) •
            (((N * k i : ℕ) : ℤ) • u i) := by
        rw [show (direction i).period =
          TranslationalTilings.wedge h g • u i from (direction i).period_eq, hdet]
        module
      rw [hshift]
      exact hp'
    have hpMem : (direction i).period ∈
        TranslationalTilings.directionSubgroup (u i) := by
      rw [show (direction i).period =
        TranslationalTilings.wedge h g • u i from (direction i).period_eq]
      change _ ∈ AddSubgroup.zmultiples (u i)
      exact ⟨_, rfl⟩
    have hquot (x : TranslationalTilings.Plane) :
        QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup (u i))
            (x + (direction i).period) =
          QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup (u i)) x := by
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      simpa only [add_sub_cancel_left] using hpMem
    intro x
    change x + (direction i).period ∈ part i ∩
        TranslationalTilings.quotientCoset
          (TranslationalTilings.directionSubgroup (u i)) Q ↔
      x ∈ part i ∩ TranslationalTilings.quotientCoset
        (TranslationalTilings.directionSubgroup (u i)) Q
    constructor
    · rintro ⟨hxpart, hxQ⟩
      refine ⟨?_, ?_⟩
      · exact ((indicator_eq_iff_membership (part i) _ _).1
          (hp x)).mp hxpart
      · change QuotientAddGroup.mk'
          (TranslationalTilings.directionSubgroup (u i)) x = Q
        change QuotientAddGroup.mk'
          (TranslationalTilings.directionSubgroup (u i))
            (x + (direction i).period) = Q at hxQ
        rw [hquot x] at hxQ
        exact hxQ
    · rintro ⟨hxpart, hxQ⟩
      refine ⟨?_, ?_⟩
      · exact ((indicator_eq_iff_membership (part i) _ _).1
          (hp x)).mpr hxpart
      · change QuotientAddGroup.mk'
          (TranslationalTilings.directionSubgroup (u i))
            (x + (direction i).period) = Q
        rw [hquot x]
        exact hxQ
  have horbit (i : Fin m) :
      DiscreteSliceOrbit F (part i) (u i) (direction i).period g := by
    let phases : Set (TranslationalTilings.Plane ⧸
        TranslationalTilings.directionSubgroup (u i)) :=
      {Q | (DiscreteSlice (u i) Q (part i)).Nonempty}
    have hphasesNonempty : phases.Nonempty := by
      obtain ⟨x, hx⟩ := hpartNonempty i
      let Q := QuotientAddGroup.mk'
        (TranslationalTilings.directionSubgroup (u i)) x
      refine ⟨Q, x, hx, ?_⟩
      change QuotientAddGroup.mk'
        (TranslationalTilings.directionSubgroup (u i)) x = Q
      rfl
    have htransport (Q : TranslationalTilings.Plane ⧸
        TranslationalTilings.directionSubgroup (u i)) (n : ℤ) :
        TranslationalTilings.translateSet (n • g)
            (Tiling.RationalPolygonal.discreteCarrier F
              (DiscreteSlice (u i) Q (part i))) =
          Tiling.RationalPolygonal.discreteCarrier F
            (DiscreteSlice (u i)
              (Q + QuotientAddGroup.mk'
                (TranslationalTilings.directionSubgroup (u i)) (n • g))
              (part i)) := by
      obtain ⟨q, hq⟩ := hmodulusDvdScale i
      have ht := Tiling.AxisParallel.Foundations.gtSliceTransport
        (F := F) (A := part i) (ell := N) (k := k i)
        hNpos (hkPos i) (huPrimitive i) (hpartPeriodic i)
        (hconvPeriodic i) Q ((n * (q : ℤ)) • v)
      have hshift : n • g =
          ((modulus i : ℕ) : ℤ) • ((n * (q : ℤ)) • v) := by
        dsimp [g]
        rw [show scale = modulus i * q from hq]
        push_cast
        module
      simpa only [DiscreteSlice, modulus, hshift] using ht
    refine {
      phases := phases
      phase_iff_nonempty := fun Q ↦ Iff.rfl
      phases_nonempty := hphasesNonempty
      within_ne_zero := by
        rw [show (direction i).period =
          TranslationalTilings.wedge h g • u i from (direction i).period_eq]
        exact smul_ne_zero hhg (huNe i)
      within_parallel := by
        rw [show (direction i).period =
          TranslationalTilings.wedge h g • u i from (direction i).period_eq]
        exact ⟨1, TranslationalTilings.wedge h g, one_ne_zero, hhg, by module⟩
      slice_periodic := fun Q _hQ ↦ hwithinPeriodic i Q
      phase_translate_mem := ?_
      carrier_transport := fun Q _hQ n ↦ htransport Q n
    }
    intro Q hQ n
    change (DiscreteSlice (u i)
      (Q + QuotientAddGroup.mk'
        (TranslationalTilings.directionSubgroup (u i)) (n • g))
      (part i)).Nonempty
    obtain ⟨x, hxSlice⟩ := hQ
    obtain ⟨f, hf⟩ := hF
    have hxCarrier : f + x ∈
        Tiling.RationalPolygonal.discreteCarrier F
          (DiscreteSlice (u i) Q (part i)) :=
      ⟨f, hf, x, hxSlice, rfl⟩
    have hxTranslated : n • g + (f + x) ∈
        TranslationalTilings.translateSet (n • g)
          (Tiling.RationalPolygonal.discreteCarrier F
            (DiscreteSlice (u i) Q (part i))) := by
      simpa [TranslationalTilings.translateSet] using hxCarrier
    rw [htransport Q n] at hxTranslated
    obtain ⟨_f, _hf, y, hy, _hxy⟩ := hxTranslated
    exact ⟨y, hy⟩
  refine ⟨{
    tile_nonempty := hF
    ell_pos := hell
    target_periodic := hE
    tiles := hTile
    h := h
    g := g
    independent := hhg
    numberOfParts := m
    number_zero_iff := ?_
    part := part
    part_nonempty := hpartNonempty
    pairwiseDisjoint := hpartsDisjoint
    iUnion_parts := hpartsUnion
    direction := direction
    sliceOrbit := horbit
  }⟩
  constructor
  · intro hm
    exact (Nat.ne_of_gt hmpos hm).elim
  · intro hAempty
    exact (Set.nonempty_iff_ne_empty.mp hA hAempty).elim

/-- Every exact tiling of a scalar-periodic target has the complete discrete finer structure. -/
theorem exists_discreteFinerStructure
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {ell : ℕ}
    (hF : F.Nonempty) (hell : 0 < ell)
    (hE : TranslationalTilings.SetScalarPeriodic ell E)
    (hTile : TranslationalTilings.Tiles F A E) :
    Nonempty (DiscreteFinerStructureData F A E ell) := by
  classical
  by_cases hAempty : A = ∅
  · let h : TranslationalTilings.Plane := ![(1 : ℤ), 0]
    let g : TranslationalTilings.Plane := ![(0 : ℤ), 1]
    refine ⟨{
      tile_nonempty := hF
      ell_pos := hell
      target_periodic := hE
      tiles := hTile
      h := h
      g := g
      independent := by simp [h, g, TranslationalTilings.wedge]
      numberOfParts := 0
      number_zero_iff := by simp [hAempty]
      part := Fin.elim0
      part_nonempty := fun i ↦ Fin.elim0 i
      pairwiseDisjoint := by intro i; exact Fin.elim0 i
      iUnion_parts := by simp [hAempty]
      direction := Fin.elim0
      sliceOrbit := fun i ↦ Fin.elim0 i
    }⟩
  have hA : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hAempty
  by_cases hcardOne : F.card = 1
  · obtain ⟨f, hFsingleton⟩ := Finset.card_eq_one.mp hcardOne
    let e0 : TranslationalTilings.Plane := ![(1 : ℤ), 0]
    have he0 : e0 ≠ 0 := by
      intro hz
      have := congrFun hz 0
      norm_num [e0] at this
    have htileEq (x : TranslationalTilings.Plane) :
        TranslationalTilings.setIndicator A (x - f) =
          TranslationalTilings.setIndicator E x := by
      simpa [TranslationalTilings.Tiles, TranslationalTilings.TilesAtLevel,
        TranslationalTilings.tileConv, hFsingleton] using hTile x
    have hperiodA : Function.Periodic
        (TranslationalTilings.setIndicator A) ((ell : ℤ) • e0) := by
      intro x
      calc
        TranslationalTilings.setIndicator A (x + (ell : ℤ) • e0) =
            TranslationalTilings.setIndicator E
              ((x + (ell : ℤ) • e0) + f) := by
          simpa only [add_sub_cancel_right] using
            htileEq ((x + (ell : ℤ) • e0) + f)
        _ = TranslationalTilings.setIndicator E (x + f) := by
          apply (indicator_eq_iff_membership E _ _).2
          have hp := hE (x + f) e0
          simpa only [add_assoc, add_left_comm, add_comm] using hp
        _ = TranslationalTilings.setIndicator A x := by
          symm
          simpa only [add_sub_cancel_right] using htileEq (x + f)
    let D : TranslationalTilings.DirectionalTilingDecomposition F A E ell := {
      numberOfParts := 1
      number_pos := Nat.zero_lt_one
      part := fun _ ↦ A
      direction := fun _ ↦ e0
      direction_ne_zero := fun _ ↦ he0
      pairwise_incommensurable := by
        intro i j hij
        exact (hij (Subsingleton.elim i j)).elim
      periodic_part := fun _ ↦ hperiodA
      pairwiseDisjoint := by
        intro i _hi j _hj hij
        exact (hij (Subsingleton.elim i j)).elim
      union_parts := by
        apply Set.Subset.antisymm
        · intro x hx
          obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
          exact hxi
        · intro x hx
          exact Set.mem_iUnion.mpr ⟨0, hx⟩
      target_periodic := hE
      tiles := hTile
    }
    exact exists_discreteFinerStructure_of_directional
      hF hell hE hTile D hell hA
  · have hcard : 1 < F.card := by
      have hcardPos : 0 < F.card := Finset.card_pos.mpr hF
      omega
    obtain ⟨t, htF⟩ := hF
    let F₀ : Finset TranslationalTilings.Plane := F.image fun f ↦ f - t
    let A₀ : Set TranslationalTilings.Plane :=
      TranslationalTilings.translateSet t A
    have hzero : 0 ∈ F₀ :=
      Finset.mem_image.mpr ⟨t, htF, sub_self t⟩
    have hcardEq : F₀.card = F.card :=
      Finset.card_image_iff.mpr
        (Set.injOn_of_injective (sub_left_injective :
          Function.Injective fun f : TranslationalTilings.Plane ↦ f - t))
    have htile₀ : TranslationalTilings.Tiles F₀ A₀ E := by
      have ht := (TranslationalTilings.tiles_translate_tile F A E 1 t).mp hTile
      have himage :
          @Finset.image TranslationalTilings.Plane TranslationalTilings.Plane
            (Classical.decEq TranslationalTilings.Plane)
            (fun f ↦ f - t) F = F₀ := by
        ext x
        simp only [F₀, Finset.mem_image]
      rw [himage] at ht
      exact ht
    obtain ⟨W, hW⟩ :=
      Tiling.AxisParallel.Foundations.gtUniformCosetwiseDirections
        (F := F₀) (E := E) hell hzero (by simpa [hcardEq] using hcard) hE
    have hvalid := hW A₀ htile₀
    obtain ⟨D₀, _hnum, _hdirections⟩ :=
      TranslationalTilings.exists_directionalTilingDecomposition_of_quantitativeData
        hell hE htile₀ W hvalid
    have hbase : 0 < ell * W.multiplier :=
      Nat.mul_pos hell W.arithmetic.multiplier_pos
    let part : Fin D₀.numberOfParts → Set TranslationalTilings.Plane :=
      fun i ↦ TranslationalTilings.translateSet (-t) (D₀.part i)
    have hpartsUnion : (⋃ i, part i) = A := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
        change x - -t ∈ D₀.part i at hxi
        have hxA₀ : x - -t ∈ A₀ := by
          rw [← D₀.union_parts]
          exact Set.mem_iUnion.mpr ⟨i, hxi⟩
        change x - -t - t ∈ A at hxA₀
        simpa only [sub_neg_eq_add, add_sub_cancel_right] using hxA₀
      · intro hx
        have hxA₀ : x + t ∈ A₀ := by
          change x + t - t ∈ A
          simpa only [add_sub_cancel_right] using hx
        rw [← D₀.union_parts] at hxA₀
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxA₀
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        change x - -t ∈ D₀.part i
        simpa only [sub_neg_eq_add] using hxi
    let D : TranslationalTilings.DirectionalTilingDecomposition F A E
        (ell * W.multiplier) := {
      numberOfParts := D₀.numberOfParts
      number_pos := D₀.number_pos
      part := part
      direction := D₀.direction
      direction_ne_zero := D₀.direction_ne_zero
      pairwise_incommensurable := D₀.pairwise_incommensurable
      periodic_part := by
        intro i x
        change TranslationalTilings.setIndicator (D₀.part i)
            (x + ((ell * W.multiplier : ℕ) : ℤ) • D₀.direction i - -t) =
          TranslationalTilings.setIndicator (D₀.part i) (x - -t)
        simpa only [sub_neg_eq_add, add_assoc, add_left_comm, add_comm] using
          D₀.periodic_part i (x + t)
      pairwiseDisjoint := by
        intro i _hi j _hj hij
        change Disjoint (part i) (part j)
        rw [Set.disjoint_left]
        intro x hxi hxj
        exact Set.disjoint_left.mp
          (D₀.pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) hij)
          (by simpa [part, TranslationalTilings.translateSet] using hxi)
          (by simpa [part, TranslationalTilings.translateSet] using hxj)
      union_parts := hpartsUnion
      target_periodic := D₀.target_periodic
      tiles := hTile
    }
    exact exists_discreteFinerStructure_of_directional
      ⟨t, htF⟩ hell hE hTile D hbase hA

end Tiling.AxisParallel.Terminal
