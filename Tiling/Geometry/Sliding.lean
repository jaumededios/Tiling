import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Tiling.Geometry.PackingTopology

set_option linter.style.header false

/-!
# Sliding components of polygonal tilings

This file contains the reusable component-shift operation.  Its geometric input is a certificate
that every plate carrier is fixed by all translations along one nonzero direction.  From that
certificate, arbitrary independent shifts of the plates preserve the tiling.

The existence of the certificate is the finite-family extension of Lemma 2.5 in
*Periodicity and decidability of translational tilings by rational polygonal sets*
(arXiv:2408.02151).  The published lemma is stated for a single open polygonal tile; this project
uses finite families of closed polygonal supports and records the required carrier invariance
explicitly.
-/

open MeasureTheory Set
open scoped Pointwise

namespace Tiling

universe u

private theorem affine_line_subset_frontier_of_locally_straight
    {t : Set Plane} {x : Plane} {L : AffineSubspace ℝ Plane}
    (hxL : x ∈ L) (hLdim : Module.finrank ℝ L.direction = 1)
    (hxlocal : ∀ᶠ y in nhds x, (y ∈ frontier t ↔ y ∈ (L : Set Plane)))
    (hstraight : ∀ y, y ∈ frontier t → BoundaryLocallyStraightAt t y) :
    (L : Set Plane) ⊆ frontier t := by
  have hdirection : L.direction ≠ ⊥ := by
    intro hbot
    have : Module.finrank ℝ L.direction = 0 := by rw [hbot]; simp
    omega
  obtain ⟨v, hvL, hv⟩ := (Submodule.ne_bot_iff L.direction).mp hdirection
  let f : ℝ → Plane := fun r ↦ r • v +ᵥ x
  have hf_continuous : Continuous f := by fun_prop
  have hfL : ∀ r, f r ∈ L := by
    intro r
    exact L.vadd_mem_of_mem_direction (L.direction.smul_mem r hvL) hxL
  let a : Set ℝ := f ⁻¹' frontier t
  have ha_closed : IsClosed a :=
    (isClosed_frontier : IsClosed (frontier t)).preimage hf_continuous
  have hzero : (0 : ℝ) ∈ interior a := by
    rw [mem_interior_iff_mem_nhds]
    have htendsto : Filter.Tendsto f (nhds (0 : ℝ)) (nhds x) := by
      have htendsto' : Filter.Tendsto f (nhds (0 : ℝ)) (nhds (f 0)) :=
        hf_continuous.continuousAt
      simpa only [f, zero_smul, zero_vadd] using htendsto'
    have hpull : ∀ᶠ r in nhds (0 : ℝ), f r ∈ frontier t ↔ f r ∈ (L : Set Plane) :=
      htendsto.eventually hxlocal
    filter_upwards [hpull] with r hr
    exact hr.mpr (hfL r)
  have hinterior_closed : IsClosed (interior a) := by
    rw [← closure_subset_iff_isClosed]
    intro r hr
    have hra : r ∈ a := ha_closed.closure_subset (closure_mono interior_subset hr)
    obtain ⟨L', hfrL', hL'dim, hlocal⟩ := hstraight (f r) hra
    by_cases hrint : r ∈ interior a
    · exact hrint
    have hpull : ∀ᶠ q in nhds r, (f q ∈ frontier t ↔ f q ∈ (L' : Set Plane)) :=
      hf_continuous.continuousAt.tendsto.eventually hlocal
    obtain ⟨U, hUsub, hUopen, hrU⟩ := mem_nhds_iff.mp hpull
    obtain ⟨q, hqU, hqint⟩ := (mem_closure_iff.mp hr U hUopen hrU)
    have hqr : q ≠ r := fun h ↦ hrint (h ▸ hqint)
    have hqa : q ∈ a := interior_subset hqint
    have hfqfrontier : f q ∈ frontier t := hqa
    have hfqL' : f q ∈ L' := (hUsub hqU).mp hfqfrontier
    have hscaled : (q - r) • v ∈ L'.direction := by
      have := L'.vsub_mem_direction hfqL' hfrL'
      simpa only [f, vadd_eq_add, vsub_eq_sub, add_sub_add_right_eq_sub, sub_smul] using this
    have hvL' : v ∈ L'.direction := by
      have := L'.direction.smul_mem (q - r)⁻¹ hscaled
      simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hqr), one_smul] using this
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset hpull ?_
    intro q hq
    apply hq.mpr
    have hdelta : (q - r) • v ∈ L'.direction := L'.direction.smul_mem _ hvL'
    have := L'.vadd_mem_of_mem_direction hdelta hfrL'
    have heq : (q - r) • v +ᵥ f r = f q := by
      simp only [f, vadd_eq_add, sub_smul]
      abel
    rw [heq] at this
    exact this
  have hinterior_univ : interior a = univ :=
    IsClopen.eq_univ ⟨hinterior_closed, isOpen_interior⟩ ⟨0, hzero⟩
  intro y hyL
  have hvsub : y -ᵥ x ∈ L.direction := L.vsub_mem_direction hyL hxL
  obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one hLdim
    (show (⟨v, hvL⟩ : L.direction) ≠ 0 by exact Subtype.coe_ne_coe.mp hv)
    (⟨y -ᵥ x, hvsub⟩ : L.direction)
  have hr' : r • v = y -ᵥ x := congrArg Subtype.val hr
  have hyf : f r = y := by
    simp only [f, hr', vsub_vadd]
  have : r ∈ a := interior_subset (hinterior_univ.symm ▸ mem_univ r)
  simpa only [a, mem_preimage, hyf] using this

private theorem affine_line_direction_le_local_direction
    {t : Set Plane} {p : Plane} {L N : AffineSubspace ℝ Plane}
    (hpL : p ∈ L) (hpN : p ∈ N) (hLfrontier : (L : Set Plane) ⊆ frontier t)
    (hlocal : ∀ᶠ y in nhds p, (y ∈ frontier t ↔ y ∈ (N : Set Plane))) :
    L.direction ≤ N.direction := by
  intro v hvL
  by_cases hv : v = 0
  · simpa only [hv] using N.direction.zero_mem
  let f : ℝ → Plane := fun r ↦ r • v +ᵥ p
  have hf_continuous : Continuous f := by fun_prop
  have htendsto : Filter.Tendsto f (nhds (0 : ℝ)) (nhds p) := by
    have htendsto' : Filter.Tendsto f (nhds (0 : ℝ)) (nhds (f 0)) :=
      hf_continuous.continuousAt
    simpa only [f, zero_smul, zero_vadd] using htendsto'
  have hpull : ∀ᶠ r in nhds (0 : ℝ), f r ∈ frontier t ↔ f r ∈ (N : Set Plane) :=
    htendsto.eventually hlocal
  obtain ⟨a, b, hab, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp hpull
  let r : ℝ := b / 2
  have hrpos : 0 < r := by dsimp only [r]; linarith [hab.2]
  have hrIoo : r ∈ Ioo a b := by
    constructor
    · exact lt_trans hab.1 hrpos
    · dsimp only [r]
      linarith [hab.2]
  have hfrL : f r ∈ L := L.vadd_mem_of_mem_direction (L.direction.smul_mem r hvL) hpL
  have hfrN : f r ∈ N := (hIoo hrIoo).mp (hLfrontier hfrL)
  have hscaled : r • v ∈ N.direction := by
    have := N.vsub_mem_direction hfrN hpN
    simpa only [f, vadd_vsub] using this
  have := N.direction.smul_mem r⁻¹ hscaled
  simpa only [smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul] using this

private theorem affine_lines_in_locally_straight_frontier_parallel
    {t : Set Plane} {L M : AffineSubspace ℝ Plane}
    (hLne : (L : Set Plane).Nonempty) (hMne : (M : Set Plane).Nonempty)
    (hLdim : Module.finrank ℝ L.direction = 1)
    (hMdim : Module.finrank ℝ M.direction = 1)
    (hLfrontier : (L : Set Plane) ⊆ frontier t)
    (hMfrontier : (M : Set Plane) ⊆ frontier t)
    (hstraight : ∀ y, y ∈ frontier t → BoundaryLocallyStraightAt t y) :
    L.direction = M.direction := by
  by_contra hdirections
  have hinf : L.direction ⊓ M.direction = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    by_contra hz0
    have hspanL := eq_span_singleton_of_mem_of_finrank_eq_one hLdim hz.1 hz0
    have hspanM := eq_span_singleton_of_mem_of_finrank_eq_one hMdim hz.2 hz0
    exact hdirections (hspanL.trans hspanM.symm)
  have hsupdim : Module.finrank ℝ ↑(L.direction ⊔ M.direction) = 2 := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq L.direction M.direction
    rw [hinf] at hdim
    rw [finrank_bot] at hdim
    simp only [hLdim, hMdim] at hdim
    omega
  have hsup : L.direction ⊔ M.direction = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Complex.finrank_real_complex] using hsupdim
  obtain ⟨p, hpL, hpM⟩ :=
    AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top hLne hMne hsup
  obtain ⟨N, hpN, hNdim, hlocal⟩ := hstraight p (hLfrontier hpL)
  have hLN : L.direction ≤ N.direction :=
    affine_line_direction_le_local_direction hpL hpN hLfrontier hlocal
  have hMN : M.direction ≤ N.direction :=
    affine_line_direction_le_local_direction hpM hpN hMfrontier hlocal
  have hsupN : L.direction ⊔ M.direction ≤ N.direction := sup_le hLN hMN
  rw [hsup] at hsupN
  have hNtop : N.direction = ⊤ := top_unique hsupN
  have : Module.finrank ℝ N.direction = 2 := by
    rw [hNtop, finrank_top, Complex.finrank_real_complex]
  omega

private theorem affine_line_direction_mem_stabilizer
    {t : Set Plane} {L : AffineSubspace ℝ Plane}
    (htclosed : IsClosed t) (hLne : (L : Set Plane).Nonempty)
    (hLdim : Module.finrank ℝ L.direction = 1)
    (hLfrontier : (L : Set Plane) ⊆ frontier t)
    (hstraight : ∀ y, y ∈ frontier t → BoundaryLocallyStraightAt t y)
    {v : Plane} (hvL : v ∈ L.direction) :
    v ∈ AddAction.stabilizer Plane t := by
  rw [AddAction.mem_stabilizer_iff]
  by_cases hv : v = 0
  · simp only [hv, zero_vadd]
  ext y
  rw [mem_vadd_set_iff_neg_vadd_mem]
  let f : ℝ → Plane := fun r ↦ r • v +ᵥ y
  have hf_continuous : Continuous f := by fun_prop
  have hmembership : ∀ r, f r ∈ t ↔ f 0 ∈ t := by
    by_cases hhit : ∃ q, f q ∈ frontier t
    · obtain ⟨q, hq⟩ := hhit
      obtain ⟨M, hfqM, hMdim, hlocal⟩ := hstraight (f q) hq
      have hMfrontier : (M : Set Plane) ⊆ frontier t :=
        affine_line_subset_frontier_of_locally_straight hfqM hMdim hlocal hstraight
      have hdirections : L.direction = M.direction :=
        affine_lines_in_locally_straight_frontier_parallel hLne ⟨f q, hfqM⟩
          hLdim hMdim hLfrontier hMfrontier hstraight
      have hvM : v ∈ M.direction := hdirections ▸ hvL
      have horbit_frontier : ∀ r, f r ∈ frontier t := by
        intro r
        apply hMfrontier
        have hdelta : (r - q) • v ∈ M.direction := M.direction.smul_mem _ hvM
        have hmem := M.vadd_mem_of_mem_direction hdelta hfqM
        have heq : (r - q) • v +ᵥ f q = f r := by
          simp only [f, vadd_eq_add, sub_smul]
          abel
        rwa [heq] at hmem
      intro r
      constructor <;> intro
      · exact htclosed.closure_eq ▸ frontier_subset_closure (horbit_frontier 0)
      · exact htclosed.closure_eq ▸ frontier_subset_closure (horbit_frontier r)
    · have hpre_frontier : frontier (f ⁻¹' t) = ∅ := by
        ext r
        constructor
        · intro hr
          exact (hhit ⟨r, hf_continuous.frontier_preimage_subset t hr⟩).elim
        · intro hr
          exact hr.elim
      rcases frontier_eq_empty_iff.mp hpre_frontier with hempty | huniv
      · have hnone : ∀ r, f r ∉ t := by
          intro r hr
          have : r ∈ f ⁻¹' t := hr
          rw [hempty] at this
          exact this
        intro r
        exact ⟨fun hr ↦ (hnone r hr).elim, fun hzero ↦ (hnone 0 hzero).elim⟩
      · have hall : ∀ r, f r ∈ t := by
          intro r
          have : r ∈ f ⁻¹' t := by rw [huniv]; exact mem_univ r
          exact this
        intro r
        exact ⟨fun _ ↦ hall 0, fun _ ↦ hall r⟩
  simpa only [f, neg_one_smul, zero_smul, zero_vadd] using hmembership (-1)

private theorem interior_nonempty_of_regular_closed_nonempty {t : Set Plane}
    (hne : t.Nonempty) (hregular : closure (interior t) = t) :
    (interior t).Nonempty := by
  by_contra hinterior
  rw [Set.not_nonempty_iff_eq_empty.mp hinterior, closure_empty] at hregular
  exact hne.ne_empty hregular.symm

private theorem directions_eq_of_aedisjoint
    {s t : Set Plane} {L M : AffineSubspace ℝ Plane}
    (hsinterior : (interior s).Nonempty) (htinterior : (interior t).Nonempty)
    (had : AEDisjoint volume s t)
    (hLdim : Module.finrank ℝ L.direction = 1)
    (hMdim : Module.finrank ℝ M.direction = 1)
    (hLs : ∀ v ∈ L.direction, v ∈ AddAction.stabilizer Plane s)
    (hMt : ∀ v ∈ M.direction, v ∈ AddAction.stabilizer Plane t) :
    L.direction = M.direction := by
  by_contra hdirections
  have hinf : L.direction ⊓ M.direction = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    by_contra hz0
    have hspanL := eq_span_singleton_of_mem_of_finrank_eq_one hLdim hz.1 hz0
    have hspanM := eq_span_singleton_of_mem_of_finrank_eq_one hMdim hz.2 hz0
    exact hdirections (hspanL.trans hspanM.symm)
  have hsupdim : Module.finrank ℝ ↑(L.direction ⊔ M.direction) = 2 := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq L.direction M.direction
    rw [hinf, finrank_bot] at hdim
    simp only [hLdim, hMdim] at hdim
    omega
  have hsup : L.direction ⊔ M.direction = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Complex.finrank_real_complex] using hsupdim
  obtain ⟨xs, hxs⟩ := hsinterior
  obtain ⟨xt, hxt⟩ := htinterior
  have hdelta : xt -ᵥ xs ∈ L.direction ⊔ M.direction := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨v, hvL, w, hwM, hvw⟩ := Submodule.mem_sup.mp hdelta
  let p : Plane := v +ᵥ xs
  have hp_eq : p = -w +ᵥ xt := by
    dsimp only [p]
    rw [vadd_eq_add, vadd_eq_add, neg_add_eq_sub]
    rw [vsub_eq_sub] at hvw
    calc
      v + xs = (v + w) + xs - w := by abel
      _ = (xt - xs) + xs - w := by rw [hvw]
      _ = xt - w := by abel
  have hvstabilizer : v +ᵥ s = s := AddAction.mem_stabilizer_iff.mp (hLs v hvL)
  have hwstabilizer : -w +ᵥ t = t :=
    AddAction.mem_stabilizer_iff.mp (hMt (-w) (M.direction.neg_mem hwM))
  have hp_s : p ∈ interior s := by
    rw [← hvstabilizer, interior_vadd]
    exact ⟨xs, hxs, by simp only [p]⟩
  have hp_t : p ∈ interior t := by
    rw [hp_eq, ← hwstabilizer, interior_vadd]
    exact ⟨xt, hxt, rfl⟩
  have hpositive : 0 < volume (interior s ∩ interior t) :=
    (isOpen_interior.inter isOpen_interior).measure_pos volume ⟨p, hp_s, hp_t⟩
  have hzero : volume (interior s ∩ interior t) = 0 :=
    measure_mono_null (inter_subset_inter interior_subset interior_subset) had.eq
  exact (ne_of_gt hpositive) hzero

/-- Nonempty regular-closed planar regions with locally straight boundaries which are pairwise
almost-everywhere disjoint have one common nonzero translation-invariance direction.

This isolates the global planar classification and common-direction argument from all tiling and
local-finiteness bookkeeping. -/
theorem exists_common_stabilizer_direction {ι : Type*} (s : ι → Set Plane)
    (hne : ∀ i, (s i).Nonempty)
    (hregular : ∀ i, closure (interior (s i)) = s i)
    (had : ∀ ⦃i j⦄, i ≠ j → AEDisjoint volume (s i) (s j))
    (hstraight : ∀ i x, x ∈ frontier (s i) → BoundaryLocallyStraightAt (s i) x) :
    ∃ v : Plane, v ≠ 0 ∧ ∀ i (r : ℝ),
      r • v ∈ AddAction.stabilizer Plane (s i) := by
  classical
  by_cases hindex : ∃ i : ι, True
  · obtain ⟨i, -⟩ := hindex
    have hiinterior : (interior (s i)).Nonempty :=
      interior_nonempty_of_regular_closed_nonempty (hne i) (hregular i)
    have hiclosed : IsClosed (s i) := by
      rw [← hregular i]
      exact isClosed_closure
    by_cases hifrontier : frontier (s i) = ∅
    · have hiuniv : s i = univ := by
        rcases frontier_eq_empty_iff.mp hifrontier with hiempty | hiuniv
        · exact ((hne i).ne_empty hiempty).elim
        · exact hiuniv
      refine ⟨1, one_ne_zero, ?_⟩
      intro j r
      have hji : j = i := by
        by_contra hji
        have hjinterior : (interior (s j)).Nonempty :=
          interior_nonempty_of_regular_closed_nonempty (hne j) (hregular j)
        have hsjzero : volume (s j) = 0 := by
          have hz := (had (i := i) (j := j) (Ne.symm hji)).eq
          simpa only [hiuniv, univ_inter] using hz
        have hinteriorzero : volume (interior (s j)) = 0 :=
          measure_mono_null interior_subset hsjzero
        exact (ne_of_gt (isOpen_interior.measure_pos volume hjinterior)) hinteriorzero
      subst j
      rw [AddAction.mem_stabilizer_iff, hiuniv]
      simp
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hifrontier
      obtain ⟨L, hxL, hLdim, hxlocal⟩ := hstraight i x hx
      have hLfrontier : (L : Set Plane) ⊆ frontier (s i) :=
        affine_line_subset_frontier_of_locally_straight hxL hLdim hxlocal (hstraight i)
      have hLne : (L : Set Plane).Nonempty := ⟨x, hxL⟩
      have hdirection : L.direction ≠ ⊥ := by
        intro hbot
        have : Module.finrank ℝ L.direction = 0 := by rw [hbot]; simp
        omega
      obtain ⟨v, hvL, hv⟩ := (Submodule.ne_bot_iff L.direction).mp hdirection
      have histabilizer : ∀ z ∈ L.direction,
          z ∈ AddAction.stabilizer Plane (s i) := by
        intro z hz
        exact affine_line_direction_mem_stabilizer hiclosed hLne hLdim hLfrontier
          (hstraight i) hz
      refine ⟨v, hv, ?_⟩
      intro j r
      by_cases hji : j = i
      · subst j
        exact histabilizer (r • v) (L.direction.smul_mem r hvL)
      have hjinterior : (interior (s j)).Nonempty :=
        interior_nonempty_of_regular_closed_nonempty (hne j) (hregular j)
      have hjclosed : IsClosed (s j) := by
        rw [← hregular j]
        exact isClosed_closure
      have hjfrontier : frontier (s j) ≠ ∅ := by
        intro hjfrontier
        have hjuniv : s j = univ := by
          rcases frontier_eq_empty_iff.mp hjfrontier with hjempty | hjuniv
          · exact ((hne j).ne_empty hjempty).elim
          · exact hjuniv
        have hsizero : volume (s i) = 0 := by
          have hz := (had (i := i) (j := j) (Ne.symm hji)).eq
          simpa only [hjuniv, inter_univ] using hz
        have hinteriorzero : volume (interior (s i)) = 0 :=
          measure_mono_null interior_subset hsizero
        exact (ne_of_gt (isOpen_interior.measure_pos volume hiinterior)) hinteriorzero
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hjfrontier
      obtain ⟨M, hyM, hMdim, hylocal⟩ := hstraight j y hy
      have hMfrontier : (M : Set Plane) ⊆ frontier (s j) :=
        affine_line_subset_frontier_of_locally_straight hyM hMdim hylocal (hstraight j)
      have hMne : (M : Set Plane).Nonempty := ⟨y, hyM⟩
      have hjstabilizer : ∀ z ∈ M.direction,
          z ∈ AddAction.stabilizer Plane (s j) := by
        intro z hz
        exact affine_line_direction_mem_stabilizer hjclosed hMne hMdim hMfrontier
          (hstraight j) hz
      have hdirections : L.direction = M.direction :=
        directions_eq_of_aedisjoint hiinterior hjinterior (had (Ne.symm hji))
          hLdim hMdim histabilizer hjstabilizer
      apply hjstabilizer
      rw [← hdirections]
      exact L.direction.smul_mem r hvL
  · refine ⟨1, one_ne_zero, ?_⟩
    intro i
    exact (hindex ⟨i, trivial⟩).elim

namespace PolygonalProtoTiling

variable {P : Type u} (A : PolygonalProtoTiling P)

/-- Translate a placement by the amount assigned to its plate in the direction `v`. -/
noncomputable def shiftedPlacement (v : Plane) (shift : A.Plate → ℝ) (i : A.placements) :
    Placement Plane P :=
  (i.1.1 + shift (A.vertexGraph.connectedComponentMk i) • v, i.1.2)

@[simp]
theorem shiftedPlacement_translation (v : Plane) (shift : A.Plate → ℝ) (i : A.placements) :
    (A.shiftedPlacement v shift i).1 =
      i.1.1 + shift (A.vertexGraph.connectedComponentMk i) • v :=
  rfl

@[simp]
theorem shiftedPlacement_label (v : Plane) (shift : A.Plate → ℝ) (i : A.placements) :
    (A.shiftedPlacement v shift i).2 = i.1.2 :=
  rfl

/-- Shift every plate independently by a real multiple of the common direction `v`. -/
noncomputable def shiftComponents (v : Plane) (shift : A.Plate → ℝ) :
    PolygonalProtoTiling P :=
  A.withPlacements (Set.range (A.shiftedPlacement v shift))

@[simp]
theorem shiftComponents_prototiles (v : Plane) (shift : A.Plate → ℝ) :
    (A.shiftComponents v shift).prototiles = A.prototiles :=
  rfl

@[simp]
theorem mem_shiftComponents_placements_iff {v : Plane} {shift : A.Plate → ℝ}
    {i : Placement Plane P} :
    i ∈ (A.shiftComponents v shift).placements ↔
      ∃ j : A.placements, A.shiftedPlacement v shift j = i :=
  Iff.rfl

/-- The canonical map from old placement vertices to shifted placement vertices. -/
noncomputable def shiftedVertex (v : Plane) (shift : A.Plate → ℝ) (i : A.placements) :
    (A.shiftComponents v shift).placements :=
  ⟨A.shiftedPlacement v shift i, ⟨i, rfl⟩⟩

@[simp]
theorem shiftedVertex_val (v : Plane) (shift : A.Plate → ℝ) (i : A.placements) :
    (A.shiftedVertex v shift i).1 = A.shiftedPlacement v shift i :=
  rfl

/-- Every shifted placement vertex comes from an original placement. -/
theorem shiftedVertex_surjective (v : Plane) (shift : A.Plate → ℝ) :
    Function.Surjective (A.shiftedVertex v shift) := by
  rintro ⟨_, i, rfl⟩
  exact ⟨i, rfl⟩

/-- The support of a shifted placement is the corresponding translate of the old support. -/
theorem placedTile_shiftedPlacement (v : Plane) (shift : A.Plate → ℝ)
    (i : A.placements) :
    placedTile A.prototiles (A.shiftedPlacement v shift i) =
      shift (A.vertexGraph.connectedComponentMk i) • v +ᵥ
        placedTile A.prototiles i.1 := by
  simp only [placedTile, shiftedPlacement]
  rw [vadd_vadd, add_comm]

/-- Shifting a placement translates its placed vertex set by the same vector. -/
theorem placedVertexSet_shiftedVertex (v : Plane) (shift : A.Plate → ℝ)
    (i : A.placements) :
    (A.shiftComponents v shift).placedVertexSet (A.shiftedVertex v shift i) =
      shift (A.vertexGraph.connectedComponentMk i) • v +ᵥ A.placedVertexSet i := by
  simp only [placedVertexSet, shiftComponents_prototiles, shiftedVertex_val, shiftedPlacement]
  rw [vadd_vadd, add_comm]

/-- A component shift cannot identify two placements from the same old plate. -/
theorem shiftedVertex_injective_of_component_eq (v : Plane) (shift : A.Plate → ℝ)
    {i j : A.placements}
    (hcomponent : A.vertexGraph.connectedComponentMk i =
      A.vertexGraph.connectedComponentMk j)
    (hshifted : A.shiftedVertex v shift i = A.shiftedVertex v shift j) : i = j := by
  apply Subtype.ext
  have hval := congrArg (fun k : (A.shiftComponents v shift).placements ↦ k.1) hshifted
  apply Prod.ext
  · dsimp only [shiftedVertex, shiftedPlacement] at hval ⊢
    rw [hcomponent] at hval
    exact add_right_cancel (congrArg Prod.fst hval)
  · simpa only [shiftedVertex, shiftedPlacement] using congrArg Prod.snd hval

/-- Component shifting preserves every old vertex-graph edge.  It is a graph homomorphism, not a
graph embedding: a suitable shift is intended to create new edges between old plates. -/
noncomputable def shiftedVertexHom (v : Plane) (shift : A.Plate → ℝ) :
    A.vertexGraph →g (A.shiftComponents v shift).vertexGraph where
  toFun := A.shiftedVertex v shift
  map_rel' := by
    intro i j hij
    have hcomponent : A.vertexGraph.connectedComponentMk i =
        A.vertexGraph.connectedComponentMk j :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hij
    rw [(A.shiftComponents v shift).vertexGraph_adj]
    refine ⟨?_, ?_⟩
    · intro hshifted
      exact hij.ne (A.shiftedVertex_injective_of_component_eq v shift hcomponent hshifted)
    · obtain ⟨x, hxi, hxj⟩ := (A.vertexGraph_adj i j).mp hij |>.2
      rw [VertexConnected, A.placedVertexSet_shiftedVertex,
        A.placedVertexSet_shiftedVertex, hcomponent]
      refine ⟨shift (A.vertexGraph.connectedComponentMk j) • v +ᵥ x, ?_, ?_⟩
      · simpa only [mem_vadd_set_iff_neg_vadd_mem, neg_vadd_vadd] using hxi
      · simpa only [mem_vadd_set_iff_neg_vadd_mem, neg_vadd_vadd] using hxj

/-- Assigning zero displacement to every plate leaves the placement set unchanged. -/
@[simp]
theorem shiftComponents_zero_placements (v : Plane) :
    (A.shiftComponents v 0).placements = A.placements := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    simp [shiftedPlacement, j.2]
  · intro hi
    exact ⟨⟨i, hi⟩, by simp [shiftedPlacement]⟩

/-- A direction along which every plate carrier is fixed by all real translations. -/
structure IsSlidingDirection (v : Plane) : Prop where
  ne_zero : v ≠ 0
  invariant : ∀ (C : A.Plate) (r : ℝ),
    r • v ∈ AddAction.stabilizer Plane (A.plateCarrier C)

namespace IsSlidingDirection

variable {A} {v : Plane}

/-- The carrier-invariance field, exposed as a pointwise set equality. -/
theorem vadd_plateCarrier (hv : A.IsSlidingDirection v) (C : A.Plate) (r : ℝ) :
    r • v +ᵥ A.plateCarrier C = A.plateCarrier C :=
  AddAction.mem_stabilizer_iff.mp (hv.invariant C r)

end IsSlidingDirection

private theorem vadd_subset_vadd {s t : Set Plane} (a : Plane) (hst : s ⊆ t) :
    a +ᵥ s ⊆ a +ᵥ t := by
  intro x hx
  simpa only [mem_vadd_set_iff_neg_vadd_mem] using hst
    (by simpa only [mem_vadd_set_iff_neg_vadd_mem] using hx)

/-- Independently shifting invariant plate carriers preserves the tiling. -/
theorem IsSlidingDirection.isTiling_shiftComponents {v : Plane}
    (hv : A.IsSlidingDirection v) (hA : IsTiling A.prototiles A.placements)
    (shift : A.Plate → ℝ) :
    IsTiling (A.shiftComponents v shift).prototiles
      (A.shiftComponents v shift).placements := by
  let _ : Countable A.placements := hA.countable.to_subtype
  rw [shiftComponents_prototiles]
  refine ⟨Set.countable_range _, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    change AEDisjoint volume
      (placedTile A.prototiles (A.shiftedPlacement v shift i))
      (placedTile A.prototiles (A.shiftedPlacement v shift j))
    rw [A.placedTile_shiftedPlacement, A.placedTile_shiftedPlacement]
    by_cases hcomponent : A.vertexGraph.connectedComponentMk i =
        A.vertexGraph.connectedComponentMk j
    · rw [hcomponent]
      apply aedisjoint_vadd
      apply hA.isPacking i.2 j.2
      intro h
      exact hij (congrArg (A.shiftedPlacement v shift) (Subtype.ext h))
    · apply (A.plateCarrier_aedisjoint hA hcomponent).mono
      · rw [← hv.vadd_plateCarrier (A.vertexGraph.connectedComponentMk i)
          (shift (A.vertexGraph.connectedComponentMk i))]
        exact vadd_subset_vadd _ (A.placedTile_subset_plateCarrier i)
      · rw [← hv.vadd_plateCarrier (A.vertexGraph.connectedComponentMk j)
          (shift (A.vertexGraph.connectedComponentMk j))]
        exact vadd_subset_vadd _ (A.placedTile_subset_plateCarrier j)
  · filter_upwards [hA.isCover] with x hx
    rw [mem_iUnion] at hx ⊢
    obtain ⟨i, hxi⟩ := hx
    let C := A.vertexGraph.connectedComponentMk i
    have hxC : x ∈ A.plateCarrier C := A.placedTile_subset_plateCarrier i hxi
    have hxshiftedCarrier : x ∈ shift C • v +ᵥ A.plateCarrier C := by
      rw [hv.vadd_plateCarrier]
      exact hxC
    rw [mem_vadd_set_iff_neg_vadd_mem] at hxshiftedCarrier
    obtain ⟨j, hjC, hxj⟩ := A.mem_plateCarrier_iff.mp hxshiftedCarrier
    have hcomponent : A.vertexGraph.connectedComponentMk j = C := hjC
    refine ⟨A.shiftedVertex v shift j, ?_⟩
    change x ∈ placedTile A.prototiles (A.shiftedPlacement v shift j)
    rw [A.placedTile_shiftedPlacement]
    rw [hcomponent, mem_vadd_set_iff_neg_vadd_mem]
    exact hxj

/-- The zero component shift preserves any tiling, independently of the chosen direction. -/
theorem isTiling_shiftComponents_zero
    (hA : IsTiling A.prototiles A.placements) (v : Plane) :
    IsTiling (A.shiftComponents v 0).prototiles (A.shiftComponents v 0).placements := by
  rw [shiftComponents_prototiles, shiftComponents_zero_placements]
  exact hA

/-- **Tiling components have a common sliding direction.**  A tiling by a finite polygonal
family has a nonzero direction along which every plate carrier is invariant.

This is the structural finite-family extension of Lemma 2.5 in arXiv:2408.02151. -/
theorem exists_isSlidingDirection [Finite P]
    (hA : IsTiling A.prototiles A.placements) :
    ∃ v : Plane, A.IsSlidingDirection v := by
  obtain ⟨v, hv, hinvariant⟩ := exists_common_stabilizer_direction A.plateCarrier
    A.plateCarrier_nonempty
    (A.plateCarrier_closure_interior hA.isPacking)
    (fun _ _ hCD ↦ A.plateCarrier_aedisjoint hA hCD)
    (fun C x hx ↦ A.plateCarrier_boundaryLocallyStraightAt hA C hx)
  exact ⟨v, ⟨hv, hinvariant⟩⟩

/-- For a tiling by a finite polygonal family, there is a nonzero common direction such that every
map from plates to real shifts preserves the tiling. -/
theorem exists_sliding_direction [Finite P]
    (hA : IsTiling A.prototiles A.placements) :
    ∃ v : Plane, v ≠ 0 ∧ ∀ shift : A.Plate → ℝ,
      IsTiling (A.shiftComponents v shift).prototiles
        (A.shiftComponents v shift).placements := by
  obtain ⟨v, hv⟩ := A.exists_isSlidingDirection hA
  exact ⟨v, hv.ne_zero, fun shift ↦
    IsSlidingDirection.isTiling_shiftComponents A hv hA shift⟩

end PolygonalProtoTiling

end Tiling
