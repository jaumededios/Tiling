import Tiling.AxisParallel.Core
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Lattice intersections forced by finite local complexity

This theorem-layer module proves the exact-intersection lattice witness through a finite-index
argument and contains the finite vertex-decoration adapter used by the final construction.
-/

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Terminal

private theorem flcDifferencesInterFinite
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {Y Q : Set E} (hY : Tiling.AxisParallel.HasFLC Y)
    (hQ : Bornology.IsBounded Q) : ((Y - Y) ∩ Q).Finite := by
  obtain ⟨R, hQR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).mp hQ
  let R' : ℝ := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  refine (hY.2 R' hR').subset ?_
  rintro x ⟨hxDiff, hxQ⟩
  exact ⟨hxDiff, Metric.closedBall_subset_closedBall (le_max_left R 1) (hQR hxQ)⟩

private theorem lattice_quotientImage_finite
    {Y : Set Tiling.Plane} (hY : Tiling.AxisParallel.HasFLC Y)
    (v : Tiling.Plane) (L : Tiling.AxisParallel.PlanarLattice)
    (hCoset : v +ᵥ (L.toAddSubgroup : Set Tiling.Plane) ⊆ Y) :
    (QuotientAddGroup.mk' L.toAddSubgroup '' Y).Finite := by
  let b := L.realBasis
  let H : AddSubgroup Tiling.Plane :=
    (Submodule.span ℤ (Set.range b)).toAddSubgroup
  have hHL : H = L.toAddSubgroup := L.span_realBasis_toAddSubgroup
  rw [← hHL] at hCoset ⊢
  have hD : ((Y - Y) ∩ ZSpan.fundamentalDomain b).Finite :=
    flcDifferencesInterFinite hY (ZSpan.fundamentalDomain_isBounded b)
  refine (hD.image (fun d => QuotientAddGroup.mk' H (v + d))).subset ?_
  rintro q ⟨y, hy, rfl⟩
  let d : Tiling.Plane := ZSpan.fract b (y - v)
  have hbase : v + (ZSpan.floor b (y - v) : Tiling.Plane) ∈ Y := by
    apply hCoset
    exact ⟨(ZSpan.floor b (y - v) : Tiling.Plane),
      (ZSpan.floor b (y - v)).property, rfl⟩
  have hdDiff : d ∈ Y - Y := by
    refine ⟨y, hy, v + (ZSpan.floor b (y - v) : Tiling.Plane), hbase, ?_⟩
    dsimp only [d]
    rw [ZSpan.fract_apply]
    abel_nf
  have hdFund : d ∈ ZSpan.fundamentalDomain b :=
    ZSpan.fract_mem_fundamentalDomain b (y - v)
  refine ⟨d, ⟨hdDiff, hdFund⟩, ?_⟩
  apply (QuotientAddGroup.mk'_eq_mk' H).2
  refine ⟨(ZSpan.floor b (y - v) : Tiling.Plane), ?_, ?_⟩
  · exact (ZSpan.floor b (y - v)).property
  · dsimp only [d]
    rw [ZSpan.fract_apply]
    abel_nf

private theorem finiteIndex_commonIntersection
    {n : ℕ} (hn : 0 < n)
    {Y : Set Tiling.Plane} (hY : Tiling.AxisParallel.HasFLC Y)
    (v : Fin n → Tiling.Plane)
    (L : Fin n → Tiling.AxisParallel.PlanarLattice)
    (hCoset : ∀ i : Fin n,
      v i +ᵥ ((L i).toAddSubgroup : Set Tiling.Plane) ⊆ Y) :
    let i₀ : Fin n := ⟨0, hn⟩
    let H₀ := (L i₀).toAddSubgroup
    ((⨅ i : Fin n, (L i).toAddSubgroup).addSubgroupOf H₀).FiniteIndex := by
  let i₀ : Fin n := ⟨0, hn⟩
  let H₀ := (L i₀).toAddSubgroup
  have hEach : ∀ i : Fin n, ((L i).toAddSubgroup.addSubgroupOf H₀).FiniteIndex := by
    intro i
    let f : H₀ →+ Tiling.Plane ⧸ (L i).toAddSubgroup :=
      (QuotientAddGroup.mk' (L i).toAddSubgroup).comp H₀.subtype
    have hImage :
        (QuotientAddGroup.mk' (L i).toAddSubgroup '' Y).Finite :=
      lattice_quotientImage_finite hY (v i) (L i) (hCoset i)
    have hRange : (f.range : Set (Tiling.Plane ⧸ (L i).toAddSubgroup)).Finite := by
      refine (hImage.image fun q =>
        q - QuotientAddGroup.mk' (L i).toAddSubgroup (v i₀)).subset ?_
      rintro q ⟨x, rfl⟩
      have hxY : v i₀ + (x : Tiling.Plane) ∈ Y := by
        apply hCoset i₀
        exact ⟨x, x.property, rfl⟩
      refine ⟨QuotientAddGroup.mk' (L i).toAddSubgroup
        (v i₀ + (x : Tiling.Plane)), ⟨_, hxY, rfl⟩, ?_⟩
      simp [f]
    let _ : Fintype f.range := hRange.fintype
    have hKer : f.ker.FiniteIndex := AddSubgroup.finiteIndex_ker f
    have hKerEq : f.ker = (L i).toAddSubgroup.addSubgroupOf H₀ := by
      ext x
      simp [f, AddSubgroup.mem_addSubgroupOf]
    rw [← hKerEq]
    exact hKer
  change ((⨅ i : Fin n, (L i).toAddSubgroup).addSubgroupOf H₀).FiniteIndex
  rw [show (⨅ i : Fin n, (L i).toAddSubgroup).addSubgroupOf H₀ =
      ⨅ i : Fin n, (L i).toAddSubgroup.addSubgroupOf H₀ by
    ext x
    change ((x : Tiling.Plane) ∈ ⨅ i : Fin n, (L i).toAddSubgroup) ↔
      x ∈ ⨅ i : Fin n, (L i).toAddSubgroup.addSubgroupOf H₀
    rw [AddSubgroup.mem_iInf, AddSubgroup.mem_iInf]
    rfl]
  exact AddSubgroup.finiteIndex_iInf hEach

private theorem span_toIntSubmodule_eq_top_of_finiteIndex_in_zspan
    (b : Module.Basis (Fin 2) ℝ Tiling.Plane)
    (H : AddSubgroup Tiling.Plane)
    [((H.addSubgroupOf
      (Submodule.span ℤ (Set.range b)).toAddSubgroup)).FiniteIndex] :
    Submodule.span ℝ (H.toIntSubmodule : Set Tiling.Plane) = ⊤ := by
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.2
  rintro _ ⟨i, rfl⟩
  let H₀ : AddSubgroup Tiling.Plane :=
    (Submodule.span ℤ (Set.range b)).toAddSubgroup
  let A : AddSubgroup H₀ := H.addSubgroupOf H₀
  let x₀ : H₀ := ⟨b i, by
    change b i ∈ Submodule.span ℤ (Set.range b)
    exact Submodule.subset_span (Set.mem_range_self i)⟩
  have hxA : A.index • x₀ ∈ A := A.nsmul_index_mem x₀
  have hxH : A.index • b i ∈ H := by
    exact hxA
  have hxSpan : (A.index : ℝ) • b i ∈
      Submodule.span ℝ (H.toIntSubmodule : Set Tiling.Plane) := by
    apply Submodule.subset_span
    simpa using hxH
  have hIndex : (A.index : ℝ) ≠ 0 := by
    exact_mod_cast (inferInstance : A.FiniteIndex).index_ne_zero
  rw [show b i = (A.index : ℝ)⁻¹ • ((A.index : ℝ) • b i) by
    rw [← mul_smul, inv_mul_cancel₀ hIndex, one_smul]]
  exact Submodule.smul_mem _ _ hxSpan

theorem finitePlanarLattices_commonSublattice_of_cosets_subset_flc
    {n : ℕ} (hn : 0 < n)
    {Y : Set Tiling.Plane} (hY : Tiling.AxisParallel.HasFLC Y)
    (v : Fin n → Tiling.Plane)
    (L : Fin n → Tiling.AxisParallel.PlanarLattice)
    (hCoset : ∀ i : Fin n,
      v i +ᵥ ((L i).toAddSubgroup : Set Tiling.Plane) ⊆ Y) :
    ∃ Lcommon : Tiling.AxisParallel.PlanarLattice,
      Lcommon.toAddSubgroup = ⨅ i : Fin n, (L i).toAddSubgroup := by
  let i₀ : Fin n := ⟨0, hn⟩
  let H : AddSubgroup Tiling.Plane := ⨅ i : Fin n, (L i).toAddSubgroup
  let b₀ : Module.Basis (Fin 2) ℝ Tiling.Plane := (L i₀).realBasis
  let Z₀ : Submodule ℤ Tiling.Plane := Submodule.span ℤ (Set.range b₀)
  have hZ₀ : Z₀.toAddSubgroup = (L i₀).toAddSubgroup := by
    simpa [Z₀, b₀] using (L i₀).span_realBasis_toAddSubgroup
  have hHZ₀ : H ≤ Z₀.toAddSubgroup := by
    intro x hx
    have hx₀ : x ∈ (L i₀).toAddSubgroup := by
      exact (AddSubgroup.mem_iInf.mp hx) i₀
    rw [hZ₀]
    exact hx₀
  have hFiniteIndex : (H.addSubgroupOf Z₀.toAddSubgroup).FiniteIndex := by
    have h := finiteIndex_commonIntersection hn hY v L hCoset
    change (H.addSubgroupOf (L i₀).toAddSubgroup).FiniteIndex at h
    rwa [hZ₀]
  let _ : (H.addSubgroupOf Z₀.toAddSubgroup).FiniteIndex := hFiniteIndex
  let inclusion : H.toIntSubmodule → Z₀ := fun x => ⟨x, hHZ₀ x.property⟩
  have inclusion_continuous : Continuous inclusion := by
    exact Continuous.subtype_mk continuous_subtype_val _
  have inclusion_injective : Function.Injective inclusion := by
    intro x y hxy
    apply Subtype.ext
    simpa [inclusion] using congrArg Subtype.val hxy
  let _ : DiscreteTopology H.toIntSubmodule :=
    DiscreteTopology.of_continuous_injective inclusion_continuous inclusion_injective
  have hSpan : Submodule.span ℝ (H.toIntSubmodule : Set Tiling.Plane) = ⊤ := by
    exact span_toIntSubmodule_eq_top_of_finiteIndex_in_zspan b₀ H
  let _ : IsZLattice ℝ H.toIntSubmodule := ⟨hSpan⟩
  let _ : Module.Finite ℤ H.toIntSubmodule :=
    ZLattice.module_finite ℝ H.toIntSubmodule
  let _ : Module.Free ℤ H.toIntSubmodule :=
    ZLattice.module_free ℝ H.toIntSubmodule
  have hCard : Fintype.card (Module.Free.ChooseBasisIndex ℤ H.toIntSubmodule) =
      Fintype.card (Fin 2) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ H.toIntSubmodule]
    exact Complex.finrank_real_complex
  let e : Module.Free.ChooseBasisIndex ℤ H.toIntSubmodule ≃ Fin 2 :=
    Fintype.equivOfCardEq hCard
  let bℤ : Module.Basis (Fin 2) ℤ H.toIntSubmodule :=
    (Module.Free.chooseBasis ℤ H.toIntSubmodule).reindex e
  let bℝ : Module.Basis (Fin 2) ℝ Tiling.Plane :=
    bℤ.ofZLatticeBasis ℝ H.toIntSubmodule
  let Lcommon : Tiling.AxisParallel.PlanarLattice :=
    { basis := bℝ
      independent := bℝ.linearIndependent }
  refine ⟨Lcommon, ?_⟩
  change AddSubgroup.closure (Set.range bℝ) = H
  rw [← Submodule.span_int_eq_addSubgroupClosure,
    bℤ.ofZLatticeBasis_span ℝ, AddSubgroup.toIntSubmodule_toAddSubgroup]

private theorem HasFLC.add_finite
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {T V : Set E} (hT : Tiling.AxisParallel.HasFLC T) (hV : V.Finite) :
    Tiling.AxisParallel.HasFLC (V + T) := by
  rcases hT with ⟨hTlocal, hTdiff⟩
  constructor
  · intro Q hQ
    have hQV : Bornology.IsBounded (Q - V) :=
      Bornology.IsBounded.sub hQ hV.isBounded
    have hTQ : (T ∩ (Q - V)).Finite := hTlocal (Q - V) hQV
    refine (hV.add hTQ).subset ?_
    rintro z ⟨hzVT, hzQ⟩
    rcases hzVT with ⟨v, hv, t, ht, rfl⟩
    refine ⟨v, hv, t, ⟨ht, ?_⟩, rfl⟩
    exact ⟨v + t, hzQ, v, hv, by abel_nf⟩
  · intro R hR
    have hVV : (V - V).Finite := hV.sub hV
    have hbounded : Bornology.IsBounded (Metric.closedBall (0 : E) R - (V - V)) :=
      Bornology.IsBounded.sub Metric.isBounded_closedBall hVV.isBounded
    obtain ⟨C, hC⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : E)).mp hbounded
    let C' : ℝ := max C 1
    have hC' : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
    have hCC' : Metric.closedBall (0 : E) C ⊆ Metric.closedBall 0 C' :=
      Metric.closedBall_subset_closedBall (le_max_left C 1)
    have hTfinite : ((T - T) ∩ Metric.closedBall (0 : E) C').Finite :=
      hTdiff C' hC'
    refine (hVV.add hTfinite).subset ?_
    rintro z ⟨hzDiff, hzBall⟩
    rcases hzDiff with ⟨x, hxVT, y, hyVT, rfl⟩
    rcases hxVT with ⟨v, hv, t, ht, rfl⟩
    rcases hyVT with ⟨w, hw, s, hs, rfl⟩
    have hvw : v - w ∈ V - V := ⟨v, hv, w, hw, rfl⟩
    have htsBounded : t - s ∈ Metric.closedBall (0 : E) C' := by
      apply hCC'
      apply hC
      refine ⟨(v + t) - (w + s), hzBall, v - w, hvw, ?_⟩
      abel_nf
    refine ⟨v - w, hvw, t - s, ⟨⟨t, ht, s, hs, rfl⟩, htsBounded⟩, ?_⟩
    simp only [sub_eq_add_neg, neg_add_rev]
    ac_rfl

theorem _root_.Tiling.AxisParallel.HasFLC.add_vertexOffsets
    {T : Set Tiling.Plane} (hT : Tiling.AxisParallel.HasFLC T)
    (K : Tiling.AxisParallel.Region) :
    Tiling.AxisParallel.HasFLC (K.vertices + T) := by
  apply Tiling.AxisParallel.Terminal.HasFLC.add_finite hT
  exact K.isPolygonal.vertexSet_finite

end Tiling.AxisParallel.Terminal
