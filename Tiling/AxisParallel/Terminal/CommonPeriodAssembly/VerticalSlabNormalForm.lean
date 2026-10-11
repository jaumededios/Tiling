/-
Copyright (c) 2026 The Tiling Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tiling Authors
-/
import Tiling.AxisParallel.Terminal.CommonPeriodAssembly.LinePeriodGroup

/-!
# Triangular normal form for a periodic vertical slab

A proper measurable slab has a cyclic group of horizontal a.e. periods.
An integer Bézout change of basis then triangularizes its rank-two lattice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Terminal

private theorem prod_univ_ae_eq_iff {A B : Set ℝ} :
    (A ×ˢ (Set.univ : Set ℝ)) =ᵐ[volume.prod volume]
      (B ×ˢ (Set.univ : Set ℝ)) ↔ A =ᵐ[volume] B := by
  constructor
  · intro h
    have hh := MeasureTheory.Measure.ae_ae_of_ae_prod h
    filter_upwards [hh] with x hx
    obtain ⟨y, hy⟩ := Filter.Eventually.exists hx
    change (x ∈ A ∧ y ∈ (Set.univ : Set ℝ)) = (x ∈ B ∧ y ∈ (Set.univ : Set ℝ)) at hy
    change (x ∈ A) = (x ∈ B)
    exact propext (by simpa using hy)
  · intro h
    exact MeasureTheory.Measure.set_prod_ae_eq h Filter.EventuallyEq.rfl

theorem slab_aePeriod_iff_re_aePeriod :
    ∀ {X : Set ℝ} {v : Tiling.Plane},
    v ∈ aePeriodGroup {z : Tiling.Plane | z.re ∈ X} ↔
      (v.re +ᵥ X) =ᵐ[volume] X := by
  intro X v
  change (v +ᵥ {z : Tiling.Plane | z.re ∈ X}) =ᵐ[volume]
      {z : Tiling.Plane | z.re ∈ X} ↔ _
  have heq :
      (v +ᵥ {z : Tiling.Plane | z.re ∈ X}) =
        Complex.measurableEquivRealProd ⁻¹' ((v.re +ᵥ X) ×ˢ (Set.univ : Set ℝ)) := by
    ext z
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  rw [heq]
  have heq0 : {z : Tiling.Plane | z.re ∈ X} =
      Complex.measurableEquivRealProd ⁻¹' (X ×ˢ (Set.univ : Set ℝ)) := by ext z; simp
  rw [heq0]
  change (Complex.measurableEquivRealProd ⁻¹' ((v.re +ᵥ X) ×ˢ Set.univ))
      =ᵐ[volume] (Complex.measurableEquivRealProd ⁻¹' (X ×ˢ Set.univ)) ↔ _
  rw [← prod_univ_ae_eq_iff]
  constructor
  · intro h
    exact (Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving).preimage_ae_eq h
  · intro h
    exact Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.preimage_ae_eq h

theorem planarLattice_has_nonvertical_vector :
    ∀ (Lambda : PlanarLattice),
    ∃ v ∈ Lambda.toAddSubgroup, v.re ≠ 0 := by
  intro Lambda
  by_contra hn
  push Not at hn
  have h0 : (Lambda.basis 0).re = 0 :=
    hn _ (AddSubgroup.subset_closure (Set.mem_range_self 0))
  have h1 : (Lambda.basis 1).re = 0 :=
    hn _ (AddSubgroup.subset_closure (Set.mem_range_self 1))
  have hlin := linearIndependent_fin2.mp Lambda.independent
  have him1 : (Lambda.basis 1).im ≠ 0 := by
    intro hi
    apply hlin.1
    apply Complex.ext <;> simp [h1, hi]
  apply hlin.2 ((Lambda.basis 0).im / (Lambda.basis 1).im)
  apply Complex.ext
  · simp [h0, h1]
  · simp [him1]

theorem lattice_triangular_of_cyclic_projection :
    ∀ (Lambda : PlanarLattice) {c : ℝ},
    0 < c →
    (∀ v ∈ Lambda.toAddSubgroup, ∃ n : ℤ, v.re = n • c) →
    ∃ alpha beta shear : ℝ,
      0 < alpha ∧ 0 < beta ∧
      Lambda.toAddSubgroup = triangularPeriodSubgroup alpha beta shear := by
  intro Lambda c hc hproj
  obtain ⟨a, ha⟩ := hproj (Lambda.basis 0)
    (AddSubgroup.subset_closure (Set.mem_range_self 0))
  obtain ⟨b, hb⟩ := hproj (Lambda.basis 1)
    (AddSubgroup.subset_closure (Set.mem_range_self 1))
  let d : ℕ := a.gcd b
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hn
    push Not at hn
    have hr0 : (Lambda.basis 0).re = 0 := by simpa [hn.1] using ha
    have hr1 : (Lambda.basis 1).re = 0 := by simpa [hn.2] using hb
    have hnv := planarLattice_has_nonvertical_vector Lambda
    obtain ⟨x, hx, hxr⟩ := hnv
    rw [← Lambda.span_realBasis_toAddSubgroup] at hx
    obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    apply hxr
    rw [← hk]
    simp [Fin.sum_univ_two, Lambda.realBasis_apply, hr0, hr1]
  have hdpos : 0 < d := by
    rcases hab with ha0 | hb0
    · exact Int.gcd_pos_of_ne_zero_left b ha0
    · exact Int.gcd_pos_of_ne_zero_right a hb0
  let p : ℤ := a / (d : ℤ)
  let q : ℤ := b / (d : ℤ)
  let u : ℤ := a.gcdA b
  let w : ℤ := a.gcdB b
  have hda : (d : ℤ) ∣ a := Int.gcd_dvd_left _ _
  have hdb : (d : ℤ) ∣ b := Int.gcd_dvd_right _ _
  have hpa : p * (d : ℤ) = a := Int.ediv_mul_cancel hda
  have hqb : q * (d : ℤ) = b := Int.ediv_mul_cancel hdb
  have hbez : a * u + b * w = (d : ℤ) := by
    simpa [d, u, w] using (Int.gcd_eq_gcd_ab a b).symm
  have hdet : p * u + q * w = 1 := by
    apply mul_right_cancel₀ (show (d : ℤ) ≠ 0 by exact_mod_cast hdpos.ne')
    calc
      (p * u + q * w) * (d : ℤ) = (p * d) * u + (q * d) * w := by ring
      _ = a * u + b * w := by rw [hpa, hqb]
      _ = d := hbez
      _ = 1 * d := by simp
  have hdetR : (p : ℝ) * u + (q : ℝ) * w = 1 := by exact_mod_cast hdet
  let vert : Tiling.Plane := q • Lambda.basis 0 - p • Lambda.basis 1
  let skew : Tiling.Plane := u • Lambda.basis 0 + w • Lambda.basis 1
  have hvertre : vert.re = 0 := by
    have hpaR : (p : ℝ) * d = a := by exact_mod_cast hpa
    have hqbR : (q : ℝ) * d = b := by exact_mod_cast hqb
    simp only [Fin.isValue, zsmul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.intCast_re,
      ha, Complex.intCast_im, zero_mul, sub_zero, hb, vert]
    rw [← hpaR, ← hqbR]
    ring
  have hskewre : skew.re = (d : ℝ) * c := by
    have hbezR : (a : ℝ) * u + (b : ℝ) * w = d := by exact_mod_cast hbez
    simp [skew, ha, hb]
    nlinarith
  have hvertne : vert ≠ 0 := by
    intro hv
    have hlin := linearIndependent_fin2.mp Lambda.independent
    by_cases hq : q = 0
    · have hp : p ≠ 0 := by
        intro hp
        simp [hq, hp] at hdet
      have hv' : (p : ℝ) • Lambda.basis 1 = 0 := by
        simpa [vert, hq] using hv.symm
      exact hlin.1 ((smul_eq_zero.mp hv').resolve_left (by exact_mod_cast hp))
    · apply hlin.2 ((q : ℝ)⁻¹ * (p : ℝ))
      have hv' : (q : ℝ) • Lambda.basis 0 = (p : ℝ) • Lambda.basis 1 := by
        exact sub_eq_zero.mp (by simpa [vert] using hv)
      calc
        ((q : ℝ)⁻¹ * (p : ℝ)) • Lambda.basis 1 =
            (q : ℝ)⁻¹ • ((p : ℝ) • Lambda.basis 1) := by rw [smul_smul]
        _ = (q : ℝ)⁻¹ • ((q : ℝ) • Lambda.basis 0) := by rw [hv']
        _ = Lambda.basis 0 := by simp [hq]
  have hvertim : vert.im ≠ 0 := by
    intro hi
    apply hvertne
    apply Complex.ext <;> simp [hvertre, hi]
  refine ⟨|vert.im|, (d : ℝ) * c, skew.im, abs_pos.mpr hvertim,
    mul_pos (by exact_mod_cast hdpos) hc, ?_⟩
  ext x
  constructor
  · intro hx
    rw [← Lambda.span_realBasis_toAddSubgroup] at hx
    obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    let r : ℤ := w * k 0 - u * k 1
    let s : ℤ := p * k 0 + q * k 1
    change ∃ m n : ℤ, x = m • verticalPeriodVector |vert.im| +
      n • skewPeriodVector ((d : ℝ) * c) skew.im
    have hsum : (∑ i, k i • Lambda.realBasis i) =
        (k 0 : ℝ) • Lambda.basis 0 + (k 1 : ℝ) • Lambda.basis 1 := by
      simp [Fin.sum_univ_two, Lambda.realBasis_apply]
    have hcomb : (k 0 : ℝ) • Lambda.basis 0 + (k 1 : ℝ) • Lambda.basis 1 =
        (r : ℝ) • vert + (s : ℝ) • skew := by
      have hdetR' : (q : ℝ) * w + (p : ℝ) * u = 1 := by nlinarith [hdetR]
      have he : (r : ℝ) • vert + (s : ℝ) • skew =
          (((q : ℝ) * w + (p : ℝ) * u) * k 0) • Lambda.basis 0 +
            (((q : ℝ) * w + (p : ℝ) * u) * k 1) • Lambda.basis 1 := by
        simp [r, s, vert, skew]
        ring_nf
      rw [he, hdetR']
      simp
    by_cases hvpos : 0 < vert.im
    · refine ⟨r, s, ?_⟩
      have hvform : verticalPeriodVector |vert.im| = vert := by
        apply Complex.ext <;> simp [verticalPeriodVector, hvertre, abs_of_pos hvpos]
      have hsform : skewPeriodVector ((d : ℝ) * c) skew.im = skew := by
        apply Complex.ext <;> simp [skewPeriodVector, hskewre]
      rw [← hk, hsum, hcomb, hvform, hsform]
      norm_cast
    · refine ⟨-r, s, ?_⟩
      have hvneg : vert.im < 0 := lt_of_le_of_ne (le_of_not_gt hvpos) hvertim
      have hvform : verticalPeriodVector |vert.im| = -vert := by
        apply Complex.ext <;> simp [verticalPeriodVector, hvertre, abs_of_neg hvneg]
      have hsform : skewPeriodVector ((d : ℝ) * c) skew.im = skew := by
        apply Complex.ext <;> simp [skewPeriodVector, hskewre]
      rw [← hk, hsum, hcomb, hvform, hsform]
      simp
  · change (∃ m n : ℤ, x = m • verticalPeriodVector |vert.im| +
      n • skewPeriodVector ((d : ℝ) * c) skew.im) → _
    rintro ⟨r, s, rfl⟩
    rw [← Lambda.span_realBasis_toAddSubgroup]
    have hbmem (i : Fin 2) : Lambda.basis i ∈ Submodule.span ℤ (Set.range Lambda.realBasis) := by
      rw [← Lambda.realBasis_apply]
      exact Submodule.subset_span (Set.mem_range_self i)
    apply Submodule.add_mem
    · by_cases hvpos : 0 < vert.im
      · have heq : verticalPeriodVector |vert.im| = vert := by
          apply Complex.ext <;> simp [verticalPeriodVector, hvertre, abs_of_pos hvpos]
        rw [heq]
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _
          (Submodule.smul_mem _ _ (hbmem 0))
          (Submodule.smul_mem _ _ (hbmem 1)))
      · have hvneg : vert.im < 0 := lt_of_le_of_ne (le_of_not_gt hvpos) hvertim
        have heq : verticalPeriodVector |vert.im| = -vert := by
          apply Complex.ext <;> simp [verticalPeriodVector, hvertre, abs_of_neg hvneg]
        rw [heq]
        exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.sub_mem _
          (Submodule.smul_mem _ _ (hbmem 0))
          (Submodule.smul_mem _ _ (hbmem 1))))
    · have heq : skewPeriodVector ((d : ℝ) * c) skew.im = skew := by
        apply Complex.ext <;> simp [skewPeriodVector, hskewre]
      rw [heq]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ (hbmem 0))
        (Submodule.smul_mem _ _ (hbmem 1)))

theorem exists_verticalSlabNormalForm
    :
    ∀ {Lambda : PlanarLattice} {X : Set ℝ},
    MeasurableSet X →
    volume X ≠ 0 →
    volume Xᶜ ≠ 0 →
    Lambda.toAddSubgroup ≤
      aePeriodGroup {z : Tiling.Plane | z.re ∈ X} →
    Nonempty (VerticalSlabLatticeForm Lambda) := by
  intro Lambda X hX hXne hXcne hsub
  obtain ⟨v, hvL, hvre⟩ := planarLattice_has_nonvertical_vector Lambda
  have hvperiod : (v.re +ᵥ X) =ᵐ[volume] X :=
    slab_aePeriod_iff_re_aePeriod.mp (hsub hvL)
  obtain ⟨c, hcprop, _⟩ := properPeriodicLine_periodGroup_cyclic
    hX hXne hXcne ⟨v.re, hvre, hvperiod⟩
  obtain ⟨hc, hcperiod⟩ := hcprop
  obtain ⟨alpha, beta, shear, halpha, hbeta, hgroup⟩ :=
    lattice_triangular_of_cyclic_projection Lambda hc (by
      intro w hw
      have hwperiod : (w.re +ᵥ X) =ᵐ[volume] X :=
        slab_aePeriod_iff_re_aePeriod.mp (hsub hw)
      exact (hcperiod w.re).mp hwperiod)
  exact ⟨{
    verticalPeriod := alpha
    horizontalPeriod := beta
    shear := shear
    verticalPeriod_pos := halpha
    horizontalPeriod_pos := hbeta
    subgroup_eq := hgroup
  }⟩


end Tiling.AxisParallel.Terminal
