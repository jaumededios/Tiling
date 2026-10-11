/-
Copyright (c) 2026 The Tiling Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tiling Authors
-/

import Tiling.AxisParallel.Core
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Finite orbit representatives for planar lattices

This module provides finite representatives for the orbits of a locally finite
set under a full-rank planar lattice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function Set
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel

theorem exists_finiteOrbitRepresentatives_of_planarLattice
    {S : Set Plane} (L : PlanarLattice)
    (hlocal : ∀ Q, Bornology.IsBounded Q → (S ∩ Q).Finite)
    (hperiod : L.toAddSubgroup ≤ periodGroup S) :
    ∃ R : Finset Plane,
      (R : Set Plane) ⊆ S ∧
      QuotientAddGroup.mk' L.toAddSubgroup '' (R : Set Plane) =
        QuotientAddGroup.mk' L.toAddSubgroup '' S ∧
      Set.InjOn (QuotientAddGroup.mk' L.toAddSubgroup) (R : Set Plane) := by
  let b := L.realBasis
  let F : Set Plane := ZSpan.fundamentalDomain b
  have hfin : (S ∩ F).Finite := hlocal F (ZSpan.fundamentalDomain_isBounded b)
  let R : Finset Plane := hfin.toFinset
  have hRset : (R : Set Plane) = S ∩ F := by
    ext x
    simp [R]
  have hsub : (R : Set Plane) ⊆ S := by
    rw [hRset]
    exact inter_subset_left
  have hfractS (s : Plane) (hs : s ∈ S) : ZSpan.fract b s ∈ S := by
    rw [ZSpan.fract_apply]
    have hfloor : (ZSpan.floor b s : Plane) ∈ periodGroup S := by
      apply hperiod
      rw [← L.span_realBasis_toAddSubgroup]
      exact (ZSpan.floor b s).property
    have hneg : -(ZSpan.floor b s : Plane) +ᵥ S = S :=
      (periodGroup_isAddSubgroup S _).mp (neg_mem hfloor)
    have hmem : -(ZSpan.floor b s : Plane) + s ∈
        -(ZSpan.floor b s : Plane) +ᵥ S := ⟨s, hs, rfl⟩
    rw [hneg] at hmem
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hmem
  have hsurj :
      QuotientAddGroup.mk' L.toAddSubgroup '' (R : Set Plane) =
        QuotientAddGroup.mk' L.toAddSubgroup '' S := by
    apply Set.Subset.antisymm
    · exact image_mono hsub
    · rintro q ⟨s, hs, rfl⟩
      let r := ZSpan.fract b s
      have hrS : r ∈ S := hfractS s hs
      have hrF : r ∈ F := ZSpan.fract_mem_fundamentalDomain b s
      refine ⟨r, ?_, ?_⟩
      · rw [hRset]
        exact ⟨hrS, hrF⟩
      · apply (QuotientAddGroup.mk'_eq_mk' _).2
        refine ⟨(ZSpan.floor b s : Plane), ?_, ?_⟩
        · rw [← L.span_realBasis_toAddSubgroup]
          exact (ZSpan.floor b s).property
        · dsimp only [r]
          rw [ZSpan.fract_apply]
          abel
  refine ⟨R, hsub, hsurj, ?_⟩
  intro x hx y hy hq
  have hxF : x ∈ F := (hRset ▸ hx).2
  have hyF : y ∈ F := (hRset ▸ hy).2
  have hdiff : -x + y ∈ L.toAddSubgroup := by
    obtain ⟨z, hz, hxy⟩ := (QuotientAddGroup.mk'_eq_mk' _).mp hq
    rw [← hxy]
    simpa using hz
  have hfract : ZSpan.fract b x = ZSpan.fract b y := by
    rw [ZSpan.fract_eq_fract]
    have hz : -x + y ∈
        (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
      rw [L.span_realBasis_toAddSubgroup]
      exact hdiff
    exact hz
  rw [ZSpan.fract_eq_self.mpr hxF, ZSpan.fract_eq_self.mpr hyF] at hfract
  exact hfract

end Tiling.AxisParallel
