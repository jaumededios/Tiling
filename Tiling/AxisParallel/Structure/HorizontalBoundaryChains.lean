import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Filter.Basic
import Mathlib.Order.SuccPred.LinearLocallyFinite
import Tiling.AxisParallel.Core
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Foundations.GenericSlices
import Tiling.AxisParallel.Continuous.EarthquakePlates

set_option linter.style.header false

open Filter Set
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel

namespace Region

/-- The positive horizontal differences between intrinsic vertices of an axis-parallel region. -/
noncomputable def horizontalStepAlphabet (K : Region) : Finset ℝ :=
  ((K.vertexFinset.biUnion fun a ↦
    K.vertexFinset.image fun b ↦ b.re - a.re).filter fun d ↦ 0 < d)

theorem mem_horizontalStepAlphabet_iff (K : Region) (d : ℝ) :
    d ∈ K.horizontalStepAlphabet ↔
      ∃ a ∈ K.vertices, ∃ b ∈ K.vertices,
        d = b.re - a.re ∧ 0 < d := by
  classical
  simp only [horizontalStepAlphabet, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl⟩, hpos⟩
    refine ⟨a, ?_, b, ?_, rfl, hpos⟩
    · change a ∈ (K.vertexFinset : Set Tiling.Plane) at ha
      simpa [K.coe_vertexFinset] using ha
    · change b ∈ (K.vertexFinset : Set Tiling.Plane) at hb
      simpa [K.coe_vertexFinset] using hb
  · rintro ⟨a, ha, b, hb, rfl, hpos⟩
    refine ⟨⟨a, ?_, b, ?_, rfl⟩, hpos⟩
    · change a ∈ (K.vertexFinset : Set Tiling.Plane)
      simpa [K.coe_vertexFinset] using ha
    · change b ∈ (K.vertexFinset : Set Tiling.Plane)
      simpa [K.coe_vertexFinset] using hb

private theorem extremePoint_mem_vertexSet
    {S : Set Tiling.Plane} {x : Tiling.Plane}
    (hx : x ∈ S.extremePoints ℝ) : x ∈ Tiling.vertexSet S := by
  rw [mem_extremePoints_iff_left] at hx
  intro triangulation
  have hxUnion : x ∈ ⋃₀ (triangulation.pieces : Set (Set Tiling.Plane)) := by
    rw [triangulation.sUnion_eq]
    exact hx.1
  obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp hxUnion
  refine ⟨t, ht, ?_⟩
  rw [mem_extremePoints_iff_left]
  refine ⟨hxt, ?_⟩
  intro y hyt z hzt hxseg
  apply hx.2 y
  · rw [← triangulation.sUnion_eq]
    exact Set.mem_sUnion_of_mem hyt ht
  · rw [← triangulation.sUnion_eq]
    exact Set.mem_sUnion_of_mem hzt ht
  · exact hxseg

private theorem exists_extremePoint_isMax_re
    {S : Set Tiling.Plane} (hcompact : IsCompact S) (hne : S.Nonempty) :
    ∃ x ∈ S.extremePoints ℝ, ∀ y ∈ S, y.re ≤ x.re := by
  obtain ⟨x, hxS, hxMax⟩ :=
    hcompact.exists_isMaxOn hne Complex.continuous_re.continuousOn
  let F : Set Tiling.Plane := S ∩ {z | z.re = x.re}
  have hFcompact : IsCompact F :=
    hcompact.inter_right (isClosed_eq Complex.continuous_re continuous_const)
  have hFne : F.Nonempty := ⟨x, hxS, rfl⟩
  obtain ⟨p, hpF, hpMax⟩ :=
    hFcompact.exists_isMaxOn hFne Complex.continuous_im.continuousOn
  refine ⟨p, ?_, ?_⟩
  · rw [mem_extremePoints_iff_left]
    refine ⟨hpF.1, ?_⟩
    intro y hyS z hzS hpseg
    rcases hpseg with ⟨a, b, ha, hb, hab, hp⟩
    have hpre := congrArg Complex.re hp
    have hpim := congrArg Complex.im hp
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at hpre
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at hpim
    have hyre : y.re ≤ p.re := by rw [hpF.2]; exact hxMax hyS
    have hzre : z.re ≤ p.re := by rw [hpF.2]; exact hxMax hzS
    have hresum : a * (p.re - y.re) + b * (p.re - z.re) = 0 := by
      calc
        a * (p.re - y.re) + b * (p.re - z.re) =
            (a + b) * p.re - (a * y.re + b * z.re) := by ring
        _ = 0 := by rw [hab, hpre]; ring
    have hyterm : 0 ≤ a * (p.re - y.re) :=
      mul_nonneg ha.le (sub_nonneg.mpr hyre)
    have hzterm : 0 ≤ b * (p.re - z.re) :=
      mul_nonneg hb.le (sub_nonneg.mpr hzre)
    have hyzero : a * (p.re - y.re) = 0 := by linarith
    have hzzero : b * (p.re - z.re) = 0 := by linarith
    have hyreEq : y.re = p.re := by
      rcases mul_eq_zero.mp hyzero with ha0 | hy0
      · exact (ha.ne' ha0).elim
      · linarith
    have hzreEq : z.re = p.re := by
      rcases mul_eq_zero.mp hzzero with hb0 | hz0
      · exact (hb.ne' hb0).elim
      · linarith
    have hyF : y ∈ F := ⟨hyS, hyreEq.trans hpF.2⟩
    have hzF : z ∈ F := ⟨hzS, hzreEq.trans hpF.2⟩
    have hyim : y.im ≤ p.im := hpMax hyF
    have hzim : z.im ≤ p.im := hpMax hzF
    have himsum : a * (p.im - y.im) + b * (p.im - z.im) = 0 := by
      calc
        a * (p.im - y.im) + b * (p.im - z.im) =
            (a + b) * p.im - (a * y.im + b * z.im) := by ring
        _ = 0 := by rw [hab, hpim]; ring
    have hyimterm : 0 ≤ a * (p.im - y.im) :=
      mul_nonneg ha.le (sub_nonneg.mpr hyim)
    have hzimterm : 0 ≤ b * (p.im - z.im) :=
      mul_nonneg hb.le (sub_nonneg.mpr hzim)
    have hyimzero : a * (p.im - y.im) = 0 := by linarith
    have hyimEq : y.im = p.im := by
      rcases mul_eq_zero.mp hyimzero with ha0 | hy0
      · exact (ha.ne' ha0).elim
      · linarith
    exact Complex.ext hyreEq hyimEq
  · intro y hy
    rw [hpF.2]
    exact hxMax hy

private theorem exists_extremePoint_isMin_re
    {S : Set Tiling.Plane} (hcompact : IsCompact S) (hne : S.Nonempty) :
    ∃ x ∈ S.extremePoints ℝ, ∀ y ∈ S, x.re ≤ y.re := by
  obtain ⟨x, hxS, hxMin⟩ :=
    hcompact.exists_isMinOn hne Complex.continuous_re.continuousOn
  let F : Set Tiling.Plane := S ∩ {z | z.re = x.re}
  have hFcompact : IsCompact F :=
    hcompact.inter_right (isClosed_eq Complex.continuous_re continuous_const)
  have hFne : F.Nonempty := ⟨x, hxS, rfl⟩
  obtain ⟨p, hpF, hpMax⟩ :=
    hFcompact.exists_isMaxOn hFne Complex.continuous_im.continuousOn
  refine ⟨p, ?_, ?_⟩
  · rw [mem_extremePoints_iff_left]
    refine ⟨hpF.1, ?_⟩
    intro y hyS z hzS hpseg
    rcases hpseg with ⟨a, b, ha, hb, hab, hp⟩
    have hpre := congrArg Complex.re hp
    have hpim := congrArg Complex.im hp
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at hpre
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at hpim
    have hyre : p.re ≤ y.re := by rw [hpF.2]; exact hxMin hyS
    have hzre : p.re ≤ z.re := by rw [hpF.2]; exact hxMin hzS
    have hresum : a * (y.re - p.re) + b * (z.re - p.re) = 0 := by
      calc
        a * (y.re - p.re) + b * (z.re - p.re) =
            (a * y.re + b * z.re) - (a + b) * p.re := by ring
        _ = 0 := by rw [hab, hpre]; ring
    have hyterm : 0 ≤ a * (y.re - p.re) :=
      mul_nonneg ha.le (sub_nonneg.mpr hyre)
    have hzterm : 0 ≤ b * (z.re - p.re) :=
      mul_nonneg hb.le (sub_nonneg.mpr hzre)
    have hyzero : a * (y.re - p.re) = 0 := by linarith
    have hzzero : b * (z.re - p.re) = 0 := by linarith
    have hyreEq : y.re = p.re := by
      rcases mul_eq_zero.mp hyzero with ha0 | hy0
      · exact (ha.ne' ha0).elim
      · linarith
    have hzreEq : z.re = p.re := by
      rcases mul_eq_zero.mp hzzero with hb0 | hz0
      · exact (hb.ne' hb0).elim
      · linarith
    have hyF : y ∈ F := ⟨hyS, hyreEq.trans hpF.2⟩
    have hzF : z ∈ F := ⟨hzS, hzreEq.trans hpF.2⟩
    have hyim : y.im ≤ p.im := hpMax hyF
    have hzim : z.im ≤ p.im := hpMax hzF
    have himsum : a * (p.im - y.im) + b * (p.im - z.im) = 0 := by
      calc
        a * (p.im - y.im) + b * (p.im - z.im) =
            (a + b) * p.im - (a * y.im + b * z.im) := by ring
        _ = 0 := by rw [hab, hpim]; ring
    have hyimterm : 0 ≤ a * (p.im - y.im) :=
      mul_nonneg ha.le (sub_nonneg.mpr hyim)
    have hzimterm : 0 ≤ b * (p.im - z.im) :=
      mul_nonneg hb.le (sub_nonneg.mpr hzim)
    have hyimzero : a * (p.im - y.im) = 0 := by linarith
    have hyimEq : y.im = p.im := by
      rcases mul_eq_zero.mp hyimzero with ha0 | hy0
      · exact (ha.ne' ha0).elim
      · linarith
    exact Complex.ext hyreEq hyimEq
  · intro y hy
    rw [hpF.2]
    exact hxMin hy

private theorem exists_support_re_ne (K : Region) :
    ∃ u ∈ K.support, ∃ v ∈ K.support, u.re ≠ v.re := by
  obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) x hx
  let y : Tiling.Plane := x + (epsilon / 2 : ℝ)
  have hyball : y ∈ Metric.ball x epsilon := by
    rw [Metric.mem_ball, Complex.dist_eq]
    simp only [y]
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hepsilon)]
    linarith
  have hy : y ∈ K.support := interior_subset (hball hyball)
  refine ⟨x, interior_subset hx, y, hy, ?_⟩
  have hne : x.re ≠ (x + (epsilon / 2 : ℝ)).re := by
    simp
    linarith
  exact hne

theorem horizontalStepAlphabet_nonempty (K : Region) :
    K.horizontalStepAlphabet.Nonempty := by
  obtain ⟨xmin, hxminExtreme, hxmin⟩ :=
    exists_extremePoint_isMin_re K.isPolygonal.isCompact K.nonempty
  obtain ⟨xmax, hxmaxExtreme, hxmax⟩ :=
    exists_extremePoint_isMax_re K.isPolygonal.isCompact K.nonempty
  obtain ⟨u, hu, v, hv, huv⟩ := exists_support_re_ne K
  have hminmax : xmin.re ≤ xmax.re := hxmin xmax
    (mem_extremePoints_iff_left.mp hxmaxExtreme).1
  have hne : xmin.re ≠ xmax.re := by
    intro hEq
    have huEq : u.re = xmin.re := by
      apply le_antisymm
      · simpa only [hEq] using hxmax u hu
      · exact hxmin u hu
    have hvEq : v.re = xmin.re := by
      apply le_antisymm
      · simpa only [hEq] using hxmax v hv
      · exact hxmin v hv
    exact huv (huEq.trans hvEq.symm)
  have hlt : xmin.re < xmax.re := lt_of_le_of_ne hminmax hne
  refine ⟨xmax.re - xmin.re, (K.mem_horizontalStepAlphabet_iff _).2 ?_⟩
  refine ⟨xmin, ?_, xmax, ?_, rfl, sub_pos.mpr hlt⟩
  · exact extremePoint_mem_vertexSet hxminExtreme
  · exact extremePoint_mem_vertexSet hxmaxExtreme

theorem horizontalStepAlphabet_pos (K : Region) {d : ℝ}
    (hd : d ∈ K.horizontalStepAlphabet) : 0 < d := by
  obtain ⟨a, ha, b, hb, heq, hpos⟩ :=
    (K.mem_horizontalStepAlphabet_iff d).mp hd
  exact hpos

end Region

namespace Structure

private theorem next_eq_of_strictMono_sameRange
    {Z : Set ℝ} (f g : ℤ → ℝ)
    (hf : StrictMono f) (hg : StrictMono g)
    (hfrange : Set.range f = Z) (hgrange : Set.range g = Z)
    {i j : ℤ} (hij : f i = g j) :
    f (i + 1) = g (j + 1) := by
  rcases lt_trichotomy (f (i + 1)) (g (j + 1)) with hlt | heq | hgt
  · have hmem : f (i + 1) ∈ Set.range g := by
      rw [hgrange, ← hfrange]
      exact Set.mem_range_self (i + 1)
    obtain ⟨m, hm⟩ := hmem
    have hjm : j < m := (hg.lt_iff_lt).mp <| by
      rw [← hij, hm]
      exact hf (by omega)
    have hmj : m < j + 1 := (hg.lt_iff_lt).mp <| hm.symm ▸ hlt
    omega
  · exact heq
  · have hmem : g (j + 1) ∈ Set.range f := by
      rw [hfrange, ← hgrange]
      exact Set.mem_range_self (j + 1)
    obtain ⟨m, hm⟩ := hmem
    have him : i < m := (hf.lt_iff_lt).mp <| by
      rw [hij, hm]
      exact hg (by omega)
    have hmi : m < i + 1 := (hf.lt_iff_lt).mp <| hm.symm ▸ hgt
    omega

private theorem prev_eq_of_strictMono_sameRange
    {Z : Set ℝ} (f g : ℤ → ℝ)
    (hf : StrictMono f) (hg : StrictMono g)
    (hfrange : Set.range f = Z) (hgrange : Set.range g = Z)
    {i j : ℤ} (hij : f i = g j) :
    f (i - 1) = g (j - 1) := by
  have hmem : g (j - 1) ∈ Set.range f := by
    rw [hfrange, ← hgrange]
    exact Set.mem_range_self (j - 1)
  obtain ⟨k, hk⟩ := hmem
  have hnext := next_eq_of_strictMono_sameRange f g hf hg hfrange hgrange hk
  have hki : k + 1 = i := hf.injective <| by
    calc
      f (k + 1) = g ((j - 1) + 1) := hnext
      _ = g j := by
        congr 1
        omega
      _ = f i := hij.symm
  have hk_eq : k = i - 1 := by omega
  simpa [hk_eq] using hk

theorem increasingProjectedCentreEnumeration_uniqueUpToShift
    {Z : Set ℝ} (z w : ℤ → ℝ)
    (hz : StrictMono z) (hw : StrictMono w)
    (hzrange : Set.range z = Z) (hwrange : Set.range w = Z) :
    ∃ k : ℤ, ∀ i : ℤ, w i = z (i + k) := by
  have hwzero : w 0 ∈ Set.range z := by
    rw [hzrange, ← hwrange]
    exact Set.mem_range_self 0
  obtain ⟨k, hk⟩ := hwzero
  refine ⟨k, fun i ↦ Int.inductionOn' i 0 ?_ ?_ ?_⟩
  · simpa using hk.symm
  · intro i hi hind
    have hnext := next_eq_of_strictMono_sameRange w z hw hz hwrange hzrange hind
    simpa only [add_assoc, add_left_comm, add_comm] using hnext
  · intro i hi hind
    have hprev := prev_eq_of_strictMono_sameRange w z hw hz hwrange hzrange hind
    simpa only [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hprev

end Structure

namespace Structure

private structure BoundaryStepChain (K : Tiling.AxisParallel.Region)
    (T : Set Tiling.Plane) (x y : ℝ) where
  length : ℕ
  length_pos : 0 < length
  point : Fin (length + 1) → ℝ
  point_zero : point 0 = x
  point_last : point (Fin.last length) = y
  point_strictMono : StrictMono point
  leftVertex : Fin length → ↥K.vertices
  rightVertex : Fin length → ↥K.vertices
  centre : Fin length → ↥T
  endpoint_coordinates : ∀ i : Fin length,
    (leftVertex i).1.re + (centre i).1.re = point i.castSucc ∧
      (rightVertex i).1.re + (centre i).1.re = point i.succ
  step_mem : ∀ i : Fin length,
    point i.succ - point i.castSucc ∈ K.horizontalStepAlphabet

private theorem verticalPlate_centres_nonempty
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T) :
    P.centres.Nonempty := by
  obtain ⟨t, ht⟩ := P.nonempty_supp
  exact ⟨t.1, t, ht, rfl⟩

private theorem verticalPlate_centres_subset
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T) :
    P.centres ⊆ T := by
  rintro _ ⟨t, _, rfl⟩
  exact t.2

private theorem verticalPlate_base_eq_of_support_eq
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T)
    {X : Set ℝ} (hSupport : P.support = Complex.re ⁻¹' X) :
    P.base = X := by
  rw [Tiling.AxisParallel.Continuous.VerticalPlate.base_eq, hSupport]
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hx
    exact ⟨(x : ℂ), hx, rfl⟩

private theorem verticalPlate_base_regular
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (hTile : Tiling.AxisParallel.TilesOn K T Set.univ)
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T) :
    P.base = interior (closure P.base) :=
  (Tiling.AxisParallel.Continuous.VerticalPlate.support_isVerticalSlab hTile P).1

private theorem verticalPlate_base_nonempty
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T) :
    P.base.Nonempty := by
  obtain ⟨t, htP⟩ := verticalPlate_centres_nonempty P
  obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
  refine ⟨(t + u).re, ?_⟩
  rw [Tiling.AxisParallel.Continuous.VerticalPlate.base_eq]
  refine ⟨t + u, ?_, rfl⟩
  change t + u ∈ Tiling.AxisParallel.regularSupport K P.centres
  have hopen : IsOpen (Tiling.AxisParallel.openUnion K P.centres) := by
    apply isOpen_iUnion
    intro s
    exact isOpen_interior.vadd s.1
  apply interior_mono subset_closure
  rw [hopen.interior_eq]
  apply Set.mem_iUnion_of_mem ⟨t, htP⟩
  rw [mem_vadd_set]
  exact ⟨u, hu, rfl⟩

private theorem frontier_regularSupport_subset_tileFrontiers
    {K : Tiling.AxisParallel.Region} {T S : Set Tiling.Plane}
    (hTile : Tiling.AxisParallel.TilesOn K T Set.univ)
    (hST : S ⊆ T) :
    frontier (Tiling.AxisParallel.regularSupport K S) ⊆
      ⋃ s : ↥S, frontier ((s.1 : Tiling.Plane) +ᵥ K.support) := by
  have hpackingS : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K S).mpr
    intro s hs t ht hst
    exact (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
      (hST hs) (hST ht) hst
  intro p hp
  have hpclosure : p ∈ closure (Tiling.AxisParallel.openUnion K S) := by
    have hp' := frontier_interior_subset hp
    simpa only [closure_closure] using frontier_subset_closure hp'
  rw [Tiling.AxisParallel.closure_openUnion_eq_iUnion_support hpackingS] at hpclosure
  obtain ⟨s, hps⟩ := Set.mem_iUnion.mp hpclosure
  apply Set.mem_iUnion_of_mem s
  rw [frontier, (K.isPolygonal.vadd s.1).isClosed.closure_eq]
  refine ⟨hps, ?_⟩
  intro hpint
  have hpreg : p ∈ Tiling.AxisParallel.regularSupport K S := by
    apply interior_mono ?_ hpint
    rw [Tiling.AxisParallel.closure_openUnion_eq_iUnion_support hpackingS]
    exact subset_iUnion (fun q : ↥S ↦ (q.1 : Tiling.Plane) +ᵥ K.support) s
  rw [frontier] at hp
  apply hp.2
  change p ∈ interior (interior (closure (Tiling.AxisParallel.openUnion K S)))
  simpa only [Tiling.AxisParallel.regularSupport, Tiling.Polygonal.regularSupport,
    ← Tiling.AxisParallel.openUnion.eq_def, interior_interior] using hpreg

private theorem verticalPlate_frontier_subset_ambientTileFrontiers
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (hTile : Tiling.AxisParallel.TilesOn K T Set.univ)
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T) :
    frontier P.support ⊆
      ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
  rw [Tiling.AxisParallel.Continuous.VerticalPlate.support_eq_regularSupport]
  intro p hp
  obtain ⟨s, hps⟩ := Set.mem_iUnion.mp
    (frontier_regularSupport_subset_tileFrontiers hTile
      (verticalPlate_centres_subset P) hp)
  apply Set.mem_iUnion_of_mem ⟨s.1, verticalPlate_centres_subset P s.2⟩
  exact hps

private theorem completeVerticalPlateBoundary_of_proper
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (hTile : Tiling.AxisParallel.TilesOn K T Set.univ)
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T)
    (hproper : P.base ≠ Set.univ) :
    ∃ (X : Set ℝ) (c : ℝ),
      P.centres.Nonempty ∧ X.Nonempty ∧ X ≠ Set.univ ∧
      IsOpen X ∧ interior (closure X) = X ∧ c ∈ frontier X ∧
      P.support = Complex.re ⁻¹' X ∧
      {z : Tiling.Plane | z.re = c} ⊆
        ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
  have hslab :=
    Tiling.AxisParallel.Continuous.VerticalPlate.support_isVerticalSlab hTile P
  have hopen : IsOpen P.base := by
    rw [hslab.1]
    exact isOpen_interior
  have hne : P.base.Nonempty := verticalPlate_base_nonempty P
  have hfront : (frontier P.base).Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    rcases frontier_eq_empty_iff.mp hempty with he | he
    · exact Set.not_nonempty_empty (he ▸ hne)
    · exact hproper he
  obtain ⟨c, hc⟩ := hfront
  refine ⟨P.base, c, verticalPlate_centres_nonempty P, hne, hproper,
    hopen, hslab.1.symm, hc, hslab.2, ?_⟩
  intro z hz
  apply verticalPlate_frontier_subset_ambientTileFrontiers hTile P
  rw [hslab.2]
  change z ∈ frontier {w : Tiling.Plane | w.re ∈ P.base}
  rw [Tiling.AxisParallel.frontier_verticalCylinder]
  change z.re = c at hz
  change z.re ∈ frontier P.base
  exact hz ▸ hc

private theorem verticalColumn_base_bounded
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (hTile : Tiling.AxisParallel.TilesOn K T Set.univ)
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T)
    (hcolumn : Tiling.AxisParallel.Continuous.IsVerticalColumn P) :
    Bornology.IsBounded P.base := by
  obtain ⟨x, hx⟩ :=
    (Tiling.AxisParallel.Continuous.isVerticalColumn_iff P).mp hcolumn
  rw [(Tiling.AxisParallel.Continuous.verticalColumn_regularSupport
    hTile P hcolumn hx).1]
  have hK : Bornology.IsBounded K.openCarrier :=
    K.isPolygonal.isBounded.subset interior_subset
  have hre : Bornology.IsBounded (Complex.re '' K.openCarrier) := by
    have himage := hK.image Complex.reCLM
    change Bornology.IsBounded (Complex.reCLM '' K.openCarrier)
    exact himage
  exact (hre.add Bornology.isBounded_singleton).closure.subset interior_subset

private theorem completeVerticalPlateBoundary :
    (∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
    Tiling.AxisParallel.TilesOn K T Set.univ →
    (¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T) →
    ∃ (P : Tiling.AxisParallel.Continuous.VerticalPlate K T) (X : Set ℝ) (c : ℝ),
      P.centres.Nonempty ∧ X.Nonempty ∧ X ≠ Set.univ ∧
      IsOpen X ∧ interior (closure X) = X ∧ c ∈ frontier X ∧
      P.support = Complex.re ⁻¹' X ∧
      {z : Tiling.Plane | z.re = c} ⊆
        ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support)) := by
  intro K T hTile hNontrivial
  have hcover : ∀ᵐ q ∂MeasureTheory.volume,
      ∃ t : ↥T, q ∈ ((t.1 : Tiling.Plane) +ᵥ K.openCarrier) := by
    filter_upwards [hTile.2.2] with q hq
    exact hq.mp (Set.mem_univ q)
  obtain ⟨q, t, hqt⟩ := hcover.exists
  let P : Tiling.AxisParallel.Continuous.VerticalPlate K T :=
    Tiling.AxisParallel.Continuous.VerticalPlate.ofCentre t
  have hproper : P.base ≠ Set.univ := by
    intro hbase
    have hfull : P.support = Set.univ := by
      rw [(Tiling.AxisParallel.Continuous.VerticalPlate.support_isVerticalSlab
        hTile P).2, hbase]
      ext z
      simp
    have hcentres : P.centres = T :=
      Tiling.AxisParallel.Continuous.plate_centres_eq_of_support_eq_univ hTile P hfull
    have hcolumn : Tiling.AxisParallel.Continuous.IsVerticalColumn P := by
      by_contra hncol
      exact hNontrivial ⟨P, hncol, hcentres⟩
    have hbdd := verticalColumn_base_bounded hTile P hcolumn
    exact not_bddAbove_univ (hbase ▸ hbdd.bddAbove)
  obtain ⟨X, c, hPne, hXne, hXproper, hXopen, hXreg, hc, hsupport, hline⟩ :=
    completeVerticalPlateBoundary_of_proper hTile P hproper
  exact ⟨P, X, c, hPne, hXne, hXproper, hXopen, hXreg, hc, hsupport, hline⟩

/-- Final typed constructor used after the finite horizontal arrangement has
selected its ordered breakpoints and the unique tile covering each gap. -/
private theorem boundaryStepChain_of_labelledArrangement
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane} {x y : ℝ}
    {n : ℕ} (hn : 0 < n) (point : Fin (n + 1) → ℝ)
    (hzero : point 0 = x) (hlast : point (Fin.last n) = y)
    (hmono : StrictMono point)
    (leftVertex rightVertex : Fin n → ↥K.vertices)
    (centre : Fin n → ↥T)
    (hend : ∀ i : Fin n,
      (leftVertex i).1.re + (centre i).1.re = point i.castSucc ∧
      (rightVertex i).1.re + (centre i).1.re = point i.succ) :
    Nonempty (BoundaryStepChain K T x y) := by
  refine ⟨{
    length := n
    length_pos := hn
    point := point
    point_zero := hzero
    point_last := hlast
    point_strictMono := hmono
    leftVertex := leftVertex
    rightVertex := rightVertex
    centre := centre
    endpoint_coordinates := hend
    step_mem := ?_ }⟩
  intro i
  apply (K.mem_horizontalStepAlphabet_iff _).2
  refine ⟨leftVertex i, (leftVertex i).2, rightVertex i, (rightVertex i).2, ?_, ?_⟩
  · rcases hend i with ⟨hl, hr⟩
    linarith
  · exact sub_pos.mpr (hmono i.castSucc_lt_succ)

private theorem openSegment_eq_vertical
    (v w : Tiling.Plane) (h : v.re = w.re) :
    openSegment ℝ v w =
      (fun y : ℝ ↦ (v.re : ℂ) + (y : ℂ) * Complex.I) ''
        openSegment ℝ v.im w.im := by
  ext z
  constructor
  · rintro ⟨a, b, ha, hb, hab, hz⟩
    refine ⟨z.im, ⟨a, b, ha, hb, hab, ?_⟩, ?_⟩
    · rw [← hz]
      simp
    · rw [← hz]
      have hweighted (r : ℝ) : a * r + b * r = r := by
        rw [← add_mul, hab, one_mul]
      apply Complex.ext <;> simp [h, hweighted]
  · rintro ⟨y, ⟨a, b, ha, hb, hab, hy⟩, rfl⟩
    refine ⟨a, b, ha, hb, hab, ?_⟩
    have hweighted (r : ℝ) : a * r + b * r = r := by
      rw [← add_mul, hab, one_mul]
    apply Complex.ext
    · simp [h, hweighted]
    · simpa using hy

private theorem exists_mem_openSegment_not_mem_finset
    {a b : ℝ} (hab : a ≠ b) (F : Finset ℝ) :
    ∃ x ∈ openSegment ℝ a b, x ∉ F := by
  have hlt : min a b < max a b := (min_lt_max).2 hab
  have hNotCountable : ¬ (Set.Ioo (min a b) (max a b)).Countable := by
    rw [Cardinal.Real.Ioo_countable_iff]
    exact not_le.mpr hlt
  by_contra hNo
  push Not at hNo
  have hSubset : Set.Ioo (min a b) (max a b) ⊆ (F : Set ℝ) := by
    intro x hx
    exact hNo x (by rwa [openSegment_eq_Ioo' hab])
  exact hNotCountable (F.finite_toSet.countable.mono hSubset)

private theorem tileFrontier_disjoint_openUnion
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (hTile : Tiling.AxisParallel.TilesOn K T Set.univ)
    (s : ↑T) :
    Disjoint (frontier ((s.1 : Tiling.Plane) +ᵥ K.support))
      (Tiling.AxisParallel.openUnion K T) := by
  rw [Set.disjoint_left]
  intro q hqFront hqOpen
  rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hqOpen
  obtain ⟨t, hqt⟩ := hqOpen
  by_cases hst : s = t
  · subst t
    rw [frontier] at hqFront
    apply hqFront.2
    rw [interior_vadd]
    exact hqt
  · have hClosure : q ∈ closure (s.1 +ᵥ K.openCarrier) := by
      rw [closure_vadd]
      change q ∈ s.1 +ᵥ closure (interior K.support)
      rw [K.isPolygonal.closure_interior]
      simpa only [(K.isPolygonal.vadd s.1).isClosed.closure_eq] using
        (frontier_subset_closure hqFront)
    have hMeet :
        ((t.1 +ᵥ K.openCarrier) ∩ (s.1 +ᵥ K.openCarrier)).Nonempty :=
      (mem_closure_iff.mp hClosure) _ (isOpen_interior.vadd t.1) hqt
    obtain ⟨z, hzt, hzs⟩ := hMeet
    have hstPlane : (s.1 : Tiling.Plane) ≠ t.1 := by
      intro heq
      exact hst (Subtype.ext heq)
    exact Set.disjoint_left.mp
      ((Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp
        hTile.2.1 s.2 t.2 hstPlane) hzs hzt


private theorem horizontalPresentation_left_frontier
    {K : Tiling.AxisParallel.Region} {y : ℝ}
    (H : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation K y)
    (i : Fin H.n) :
    H.left i ∈ frontier
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K y) := by
  have hClosure : H.left i ∈ closure
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K y) := by
    rw [H.closure_eq, Set.mem_iUnion]
    exact ⟨i, ⟨le_rfl, (H.lt i).le⟩⟩
  have hNotMem : H.left i ∉
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K y := by
    intro hmem
    have hUnion : H.left i ∈ ⋃ j, Ioo (H.left j) (H.right j) := by
      exact H.union_eq ▸ hmem
    rw [Set.mem_iUnion] at hUnion
    obtain ⟨j, hj⟩ := hUnion
    by_cases hij : i = j
    · subst j
      exact (lt_irrefl _ hj.1)
    · rcases H.pairwise_gap i j hij with hRightLeft | hRightRight
      · exact (not_lt_of_ge (H.lt i).le) (hRightLeft.trans hj.1)
      · exact (not_lt_of_ge hRightRight.le) hj.2
  rw [frontier]
  exact ⟨hClosure, fun hInterior ↦ hNotMem (interior_subset hInterior)⟩

private theorem horizontalPresentation_right_frontier
    {K : Tiling.AxisParallel.Region} {y : ℝ}
    (H : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation K y)
    (i : Fin H.n) :
    H.right i ∈ frontier
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K y) := by
  have hClosure : H.right i ∈ closure
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K y) := by
    rw [H.closure_eq, Set.mem_iUnion]
    exact ⟨i, ⟨(H.lt i).le, le_rfl⟩⟩
  have hNotMem : H.right i ∉
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K y := by
    intro hmem
    have hUnion : H.right i ∈ ⋃ j, Ioo (H.left j) (H.right j) := by
      exact H.union_eq ▸ hmem
    rw [Set.mem_iUnion] at hUnion
    obtain ⟨j, hj⟩ := hUnion
    by_cases hij : i = j
    · subst j
      exact (lt_irrefl _ hj.2)
    · rcases H.pairwise_gap i j hij with hRightLeft | hRightRight
      · exact (not_lt_of_ge hRightLeft.le) hj.1
      · exact (not_lt_of_ge (H.lt i).le) (hj.2.trans hRightRight)
  rw [frontier]
  exact ⟨hClosure, fun hInterior ↦ hNotMem (interior_subset hInterior)⟩

private theorem relevantTilesFinite : (∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
    Tiling.AxisParallel.TilesOn K T Set.univ →
    ∀ Q : Set Tiling.Plane, Bornology.IsBounded Q →
      {t : Tiling.Plane | t ∈ T ∧ ((t +ᵥ K.support) ∩ Q).Nonempty}.Finite) := by
  intro K T hTile Q hQ
  let C : Set Tiling.Plane := Q - K.support
  have hC : Bornology.IsBounded C := hQ.sub K.isPolygonal.isBounded
  have hsub :
      {t : Tiling.Plane | t ∈ T ∧ ((t +ᵥ K.support) ∩ Q).Nonempty} ⊆ T ∩ C := by
    rintro t ⟨ht, z, hztranslate, hzQ⟩
    refine ⟨ht, ?_⟩
    rw [Set.mem_sub]
    rw [mem_vadd_set] at hztranslate
    obtain ⟨k, hk, rfl⟩ := hztranslate
    exact ⟨t + k, hzQ, k, hk, by simp⟩
  exact ((Tiling.AxisParallel.IsPacking.locallyFinite_centres hTile.2.1).1 C hC).subset hsub

private theorem boundaryChainExtraction_proof
    (hRelevant : (∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
    Tiling.AxisParallel.TilesOn K T Set.univ →
    ∀ Q : Set Tiling.Plane, Bornology.IsBounded Q →
      {t : Tiling.Plane | t ∈ T ∧ ((t +ᵥ K.support) ∩ Q).Nonempty}.Finite)) :
    (∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
    Tiling.AxisParallel.TilesOn K T Set.univ →
    ∀ {c : ℝ},
      ({z : Tiling.Plane | z.re = c} ⊆
        ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support)) →
    ∀ (v : ↥K.vertices) (t : ↥T),
      (v.1 + (t.1 : Tiling.Plane)).re ≠ c →
      Nonempty (BoundaryStepChain K T
        (min c (v.1 + (t.1 : Tiling.Plane)).re)
        (max c (v.1 + (t.1 : Tiling.Plane)).re))) := by
  intro K T hTile c hline v t hne
  obtain ⟨w, hwv, hwvRe, hEdge⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.intrinsicVertex_incident_axisEdge K Axis.vertical v
  have hvwRe : v.1.re = w.1.re := hwvRe.symm
  have hvwIm : v.1.im ≠ w.1.im := by
    intro him
    apply hwv
    exact Complex.ext hvwRe.symm him.symm
  let p : ℝ := (v.1 + (t.1 : Tiling.Plane)).re
  let lo : ℝ := min c p
  let hi : ℝ := max c p
  have hlohi : lo < hi := by
    exact (min_lt_max).2 (Ne.symm hne)
  let yv : ℝ := t.1.im + v.1.im
  let yw : ℝ := t.1.im + w.1.im
  let Q : Set Tiling.Plane :=
    Set.uIcc lo hi ×ℂ Set.uIcc yv yw
  have hQBounded : Bornology.IsBounded Q := by
    exact (Metric.isBounded_Icc (min lo hi) (max lo hi)).reProdIm
      (Metric.isBounded_Icc (min yv yw) (max yv yw))
  let R : Set Tiling.Plane :=
    {s : Tiling.Plane | s ∈ T ∧ ((s +ᵥ K.support) ∩ Q).Nonempty}
  have hRFinite : R.Finite := hRelevant hTile Q hQBounded
  let F : Finset Tiling.Plane := hRFinite.toFinset
  have htF : (t.1 : Tiling.Plane) ∈ F := by
    change t.1 ∈ hRFinite.toFinset
    rw [Set.Finite.mem_toFinset]
    refine ⟨t.2, ?_⟩
    let y0 : ℝ := (v.1.im + w.1.im) / 2
    let z0 : Tiling.Plane := Complex.mk v.1.re y0
    have hy0 : y0 ∈ openSegment ℝ v.1.im w.1.im := by
      convert midpoint_mem_openSegment (𝕜 := ℝ) v.1.im w.1.im using 1
      simp [y0, midpoint_eq_smul_add, div_eq_mul_inv, smul_eq_mul, mul_comm]
    have hz0Edge : z0 ∈ frontier K.support := by
      apply (hEdge ?_).1
      rw [openSegment_eq_vertical v.1 w.1 hvwRe]
      refine ⟨y0, hy0, ?_⟩
      apply Complex.ext <;> simp [z0]
    let q0 : Tiling.Plane := t.1 + z0
    refine ⟨q0, ?_, ?_⟩
    · refine ⟨z0, ?_, rfl⟩
      simpa only [K.isPolygonal.isClosed.closure_eq] using
        (frontier_subset_closure hz0Edge)
    · change q0.re ∈ Set.uIcc lo hi ∧ q0.im ∈ Set.uIcc yv yw
      constructor
      · have hpEq : q0.re = p := by simp [q0, z0, p, add_comm]
        rw [hpEq]
        rw [Set.uIcc_of_le hlohi.le]
        exact ⟨min_le_right _ _, le_max_right _ _⟩
      · have hy0Seg : y0 ∈ segment ℝ v.1.im w.1.im :=
          openSegment_subset_segment ℝ _ _ hy0
        rw [segment_eq_uIcc] at hy0Seg
        rw [Set.mem_uIcc] at hy0Seg ⊢
        rcases hy0Seg with hy0Seg | hy0Seg
        · left
          simp only [q0, z0, yv, yw, Complex.add_im]
          constructor <;> linarith
        · right
          simp only [q0, z0, yv, yw, Complex.add_im]
          constructor <;> linarith
  have hFNonempty : F.Nonempty := ⟨t.1, htF⟩
  let bad : Finset ℝ :=
    F.biUnion fun s ↦ K.vertexFinset.image fun u ↦ s.im + u.im
  have hyvyw : yv ≠ yw := by
    dsimp only [yv, yw]
    intro hEq
    exact hvwIm (add_left_cancel hEq)
  obtain ⟨y, hySegment, hyBad⟩ :=
    exists_mem_openSegment_not_mem_finset hyvyw bad
  have hyU : y ∈ Set.uIoo yv yw := by
    simpa only [segment_eq_uIcc, openSegment_eq_Ioo' hyvyw,
      Set.uIoo] using hySegment
  have hGeneric (s : ↑F) :
      y - s.1.im ∉ K.vertexFinset.image Complex.im := by
    intro hsVertex
    rw [Finset.mem_image] at hsVertex
    obtain ⟨u, hu, huEq⟩ := hsVertex
    apply hyBad
    have hmem : s.1.im + u.im ∈ bad := by
      rw [show bad = F.biUnion (fun r ↦
        K.vertexFinset.image fun q ↦ r.im + q.im) from rfl,
        Finset.mem_biUnion]
      exact ⟨s.1, s.2, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
    have hyEq : y = s.1.im + u.im := by linarith
    exact hyEq ▸ hmem
  let H (s : ↑F) :
      Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
        K (y - s.1.im) :=
    (Tiling.AxisParallel.Foundations.GenericSlices.horizontalGenericSlicePresentation_exists
      K (hGeneric s)).some
  let I := Σ s : ↑F, Fin (H s).n
  let left : I → ℝ := fun i ↦ i.1.1.re + (H i.1).left i.2
  let right : I → ℝ := fun i ↦ i.1.1.re + (H i.1).right i.2
  let endpoints : Finset ℝ :=
    (Finset.univ.image left) ∪ (Finset.univ.image right)
  let B : Finset ℝ :=
    insert hi (insert lo
      (endpoints.filter fun r ↦ lo ≤ r ∧ r ≤ hi))
  have hloB : lo ∈ B := by simp [B]
  have hhiB : hi ∈ B := by simp [B]
  have hBSubset : ∀ r ∈ B, r ∈ Set.Icc lo hi := by
    intro r hr
    simp only [B, Finset.mem_insert, Finset.mem_filter] at hr
    rcases hr with rfl | rfl | hr
    · exact ⟨hlohi.le, le_rfl⟩
    · exact ⟨le_rfl, hlohi.le⟩
    · exact hr.2
  have hBCard : 2 ≤ B.card := by
    have hPair : ({lo, hi} : Finset ℝ) ⊆ B := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hloB
      · exact hhiB
    have := Finset.card_le_card hPair
    have hPairCard : ({lo, hi} : Finset ℝ).card = 2 :=
      Finset.card_pair (ne_of_lt hlohi)
    rwa [hPairCard] at this
  let n : ℕ := B.card - 1
  have hn : 0 < n := by dsimp only [n]; omega
  have hCard : B.card = n + 1 := by dsimp only [n]; omega
  let e : Fin (n + 1) ≃o ↑B := B.orderIsoOfFin hCard
  let point : Fin (n + 1) → ℝ := fun i ↦ (e i).1
  have hPointMono : StrictMono point := by
    intro i j hij
    exact e.strictMono hij
  have hPointZero : point 0 = lo := by
    apply le_antisymm
    · obtain ⟨j, hj⟩ := e.surjective ⟨lo, hloB⟩
      have h0j : (0 : Fin (n + 1)) ≤ j := Fin.zero_le j
      calc
        point 0 ≤ point j := e.monotone h0j
        _ = lo := congrArg Subtype.val hj
    · exact (hBSubset _ (e 0).2).1
  have hPointLast : point (Fin.last n) = hi := by
    apply le_antisymm
    · exact (hBSubset _ (e (Fin.last n)).2).2
    · obtain ⟨j, hj⟩ := e.surjective ⟨hi, hhiB⟩
      have hjLast : j ≤ Fin.last n := Fin.le_last j
      calc
        hi = point j := (congrArg Subtype.val hj).symm
        _ ≤ point (Fin.last n) := e.monotone hjLast
  let eps (s : ↑F) : ℝ :=
    (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice_locallyConstant
      K (hGeneric s)).choose
  have hEpsPos (s : ↑F) : 0 < eps s :=
    (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice_locallyConstant
      K (hGeneric s)).choose_spec.1
  have hStable (s : ↑F) (r : ℝ)
      (hr : |r - (y - s.1.im)| < eps s) :
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K r =
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K
          (y - s.1.im) :=
    (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice_locallyConstant
      K (hGeneric s)).choose_spec.2 r hr
  have hFSubtypeNonempty : (Finset.univ : Finset ↑F).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact ⟨⟨t.1, htF⟩⟩
  let epsValues : Finset ℝ := (Finset.univ : Finset ↑F).image eps
  have hEpsValuesNonempty : epsValues.Nonempty :=
    hFSubtypeNonempty.image eps
  let eps0 : ℝ := epsValues.min' hEpsValuesNonempty
  have hEps0Pos : 0 < eps0 := by
    have hmem := epsValues.min'_mem hEpsValuesNonempty
    change eps0 ∈ (Finset.univ : Finset ↑F).image eps at hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨s, -, hs⟩ := hmem
    exact hs ▸ hEpsPos s
  have hEps0Le (s : ↑F) : eps0 ≤ eps s := by
    apply epsValues.min'_le
    change eps s ∈ (Finset.univ : Finset ↑F).image eps
    rw [Finset.mem_image]
    exact ⟨s, Finset.mem_univ s, rfl⟩
  let ylo : ℝ := min yv yw
  let yhi : ℝ := max yv yw
  have hyBounds : ylo < y ∧ y < yhi := by
    exact hyU
  let margin : ℝ := min (y - ylo) (yhi - y)
  have hMarginPos : 0 < margin := by
    exact lt_min (sub_pos.mpr hyBounds.1) (sub_pos.mpr hyBounds.2)
  let eta : ℝ := min eps0 margin / 2
  have hEtaPos : 0 < eta := div_pos (lt_min hEps0Pos hMarginPos) (by norm_num)
  have hEtaLeEps (s : ↑F) : eta < eps s := by
    have : eta < eps0 := by
      dsimp only [eta]
      nlinarith [min_le_left eps0 margin, hEps0Pos]
    exact this.trans_le (hEps0Le s)
  have hEtaLeMargin : eta < margin := by
    dsimp only [eta]
    nlinarith [min_le_right eps0 margin, hMarginPos]
  have hCNotOpen : Complex.mk c y ∉ Tiling.AxisParallel.openUnion K T := by
    have hcLine : (Complex.mk c y).re = c := rfl
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (hline hcLine)
    exact Set.disjoint_left.mp (tileFrontier_disjoint_openUnion hTile s) hs
  have hPNotOpen : Complex.mk p y ∉ Tiling.AxisParallel.openUnion K T := by
    have hySource : y - t.1.im ∈ openSegment ℝ v.1.im w.1.im := by
      rcases hySegment with ⟨a, b, ha, hb, hab, hyEq⟩
      refine ⟨a, b, ha, hb, hab, ?_⟩
      dsimp only [yv, yw] at hyEq
      simp only [smul_eq_mul] at hyEq ⊢
      calc
        a * v.1.im + b * w.1.im =
            (a * (t.1.im + v.1.im) + b * (t.1.im + w.1.im)) -
              (a + b) * t.1.im := by ring
        _ = y - t.1.im := by rw [hyEq, hab, one_mul]
    let z : Tiling.Plane := Complex.mk v.1.re (y - t.1.im)
    have hzEdge : z ∈ frontier K.support := by
      apply (hEdge ?_).1
      rw [openSegment_eq_vertical v.1 w.1 hvwRe]
      refine ⟨y - t.1.im, hySource, ?_⟩
      apply Complex.ext <;> simp [z]
    have hTranslated : Complex.mk p y ∈
        frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
      rw [Tiling.AxisParallel.frontier_vadd_eq]
      refine ⟨z, hzEdge, ?_⟩
      apply Complex.ext <;> simp [z, p, add_comm]
    exact Set.disjoint_left.mp (tileFrontier_disjoint_openUnion hTile t)
      hTranslated
  have hBreakpointNotOpen (r : ℝ) (hrB : r ∈ B) :
      Complex.mk r y ∉ Tiling.AxisParallel.openUnion K T := by
    simp only [B, Finset.mem_insert, Finset.mem_filter] at hrB
    rcases hrB with rfl | rfl | hrEndpoint
    · rcases max_choice c p with hpEq | hpEq
      · simpa only [hi, hpEq] using hCNotOpen
      · simpa only [hi, hpEq] using hPNotOpen
    · rcases min_choice c p with hpEq | hpEq
      · simpa only [lo, hpEq] using hCNotOpen
      · simpa only [lo, hpEq] using hPNotOpen
    · have hrE : r ∈ endpoints := hrEndpoint.1
      simp only [endpoints, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and] at hrE
      rcases hrE with ⟨j, hj⟩ | ⟨j, hj⟩
      · let sT : T := ⟨j.1.1, (Set.Finite.mem_toFinset hRFinite).mp j.1.2 |>.1⟩
        have hRelFrontier :=
          Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice_frontier_lifts K
            (hGeneric j.1) (horizontalPresentation_left_frontier (H j.1) j.2)
        have hTranslated : Complex.mk r y ∈
            frontier ((sT.1 : Tiling.Plane) +ᵥ K.support) := by
          rw [Tiling.AxisParallel.frontier_vadd_eq]
          refine ⟨Complex.mk ((H j.1).left j.2) (y - j.1.1.im),
            hRelFrontier, ?_⟩
          subst r
          apply Complex.ext <;> simp [left, sT]
        exact Set.disjoint_left.mp (tileFrontier_disjoint_openUnion hTile sT)
          hTranslated
      · let sT : T := ⟨j.1.1, (Set.Finite.mem_toFinset hRFinite).mp j.1.2 |>.1⟩
        have hRelFrontier :=
          Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice_frontier_lifts K
            (hGeneric j.1) (horizontalPresentation_right_frontier (H j.1) j.2)
        have hTranslated : Complex.mk r y ∈
            frontier ((sT.1 : Tiling.Plane) +ᵥ K.support) := by
          rw [frontier_vadd_eq]
          refine ⟨Complex.mk ((H j.1).right j.2) (y - j.1.1.im),
            hRelFrontier, ?_⟩
          subst r
          apply Complex.ext <;> simp [right, sT]
        exact Set.disjoint_left.mp (tileFrontier_disjoint_openUnion hTile sT)
          hTranslated
  have gap_has_interval (i : Fin n) :
      ∃ j : I, left j = point i.castSucc ∧ right j = point i.succ := by
    let U : Set Tiling.Plane :=
      Set.Ioo (point i.castSucc) (point i.succ) ×ℂ Set.Ioo (y - eta) (y + eta)
    have hGapLt : point i.castSucc < point i.succ :=
      hPointMono i.castSucc_lt_succ
    have hUOpen : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
    have hUNonempty : U.Nonempty := by
      rw [Complex.reProdIm_nonempty]
      exact ⟨Set.nonempty_Ioo.mpr hGapLt,
        Set.nonempty_Ioo.mpr (by linarith [hEtaPos])⟩
    have hCovered : ∃ q ∈ U, ∃ s : ↑T,
        q ∈ ((s.1 : Tiling.Plane) +ᵥ K.openCarrier) := by
      by_contra hNo
      push Not at hNo
      have hUNull : MeasureTheory.volume U = 0 := by
        apply MeasureTheory.measure_mono_null
          (t := {q | ¬ ∃ s : ↑T,
            q ∈ ((s.1 : Tiling.Plane) +ᵥ K.openCarrier)})
        · intro q hq
          exact fun ⟨s, hs⟩ ↦ hNo q hq s hs
        · exact MeasureTheory.ae_iff.mp (by
            filter_upwards [hTile.2.2] with q hq
            exact hq.mp (Set.mem_univ q))
      exact (hUOpen.measure_pos MeasureTheory.volume hUNonempty).ne' hUNull
    obtain ⟨q, hqU, s, hqs⟩ := hCovered
    have hqQ : q ∈ Q := by
      change q.re ∈ Set.uIcc lo hi ∧ q.im ∈ Set.uIcc yv yw
      have hleftBounds := hBSubset _ (e i.castSucc).2
      have hrightBounds := hBSubset _ (e i.succ).2
      have hqRe : q.re ∈ Set.Ioo (point i.castSucc) (point i.succ) := hqU.1
      have hqIm : q.im ∈ Set.Ioo (y - eta) (y + eta) := hqU.2
      constructor
      · rw [Set.uIcc_of_le hlohi.le]
        change lo ≤ point i.castSucc ∧ point i.castSucc ≤ hi at hleftBounds
        change lo ≤ point i.succ ∧ point i.succ ≤ hi at hrightBounds
        exact ⟨hleftBounds.1.trans hqRe.1.le,
          hqRe.2.le.trans hrightBounds.2⟩
      · change min yv yw ≤ q.im ∧ q.im ≤ max yv yw
        change ylo ≤ q.im ∧ q.im ≤ yhi
        obtain ⟨hqImLo, hqImHi⟩ := hqIm
        have hEtaYLo : eta < y - ylo :=
          hEtaLeMargin.trans_le (min_le_left _ _)
        have hEtaYHi : eta < yhi - y :=
          hEtaLeMargin.trans_le (min_le_right _ _)
        constructor
        · exact le_of_lt (by linarith)
        · exact le_of_lt (by linarith)
    have hsR : s.1 ∈ R := by
      refine ⟨s.2, q, ?_, hqQ⟩
      exact Set.vadd_set_mono interior_subset hqs
    let sF : ↑F := ⟨s.1, (Set.Finite.mem_toFinset hRFinite).mpr hsR⟩
    have hqSliceCurrent : q.re - s.1.re ∈
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K
          (q.im - s.1.im) := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hqs
      change Complex.mk (q.re - s.1.re) (q.im - s.1.im) ∈ K.openCarrier
      have heq : -s.1 + q =
          Complex.mk (q.re - s.1.re) (q.im - s.1.im) := by
        apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
      exact heq ▸ hqs
    have hNear : |(q.im - s.1.im) - (y - s.1.im)| < eps sF := by
      obtain ⟨hqImLo, hqImHi⟩ := hqU.2
      rw [sub_sub_sub_cancel_right]
      apply (abs_lt).2
      constructor <;> linarith [hEtaLeEps sF]
    have hqSlice : q.re - s.1.re ∈
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K
          (y - s.1.im) := by
      rw [← hStable sF _ hNear]
      exact hqSliceCurrent
    have hqUnion : q.re - s.1.re ∈
        ⋃ k, Set.Ioo ((H sF).left k) ((H sF).right k) := by
      exact (H sF).union_eq ▸ hqSlice
    rw [Set.mem_iUnion] at hqUnion
    obtain ⟨k, hqk⟩ := hqUnion
    let j : I := ⟨sF, k⟩
    have hLeftQ : left j < q.re := by
      dsimp only [left, j]
      linarith [hqk.1]
    have hQRight : q.re < right j := by
      dsimp only [right, j]
      linarith [hqk.2]
    have hLeftLe : left j ≤ point i.castSucc := by
      by_cases hllo : left j ≤ lo
      · exact hllo.trans (hBSubset _ (e i.castSucc).2).1
      · have hleftMem : left j ∈ B := by
          simp only [B, Finset.mem_insert, Finset.mem_filter]
          right; right
          refine ⟨?_, le_of_lt (lt_of_not_ge hllo), ?_⟩
          · simp only [endpoints, Finset.mem_union, Finset.mem_image,
              Finset.mem_univ, true_and]
            exact Or.inl ⟨j, rfl⟩
          · exact hLeftQ.le.trans
              ((show q.re < point i.succ from hqU.1.2).le.trans
                (hBSubset _ (e i.succ).2).2)
        let k' : Fin (n + 1) := e.symm ⟨left j, hleftMem⟩
        have hkLt : k' < i.succ := by
          apply e.lt_iff_lt.mp
          change (e k').1 < (e i.succ).1
          simpa only [k', e.apply_symm_apply, point] using
            hLeftQ.trans hqU.1.2
        have hkLe : k' ≤ i.castSucc := by
          rw [Fin.lt_def] at hkLt
          rw [Fin.le_iff_val_le_val]
          simp only [Fin.val_succ, Fin.val_castSucc] at hkLt ⊢
          omega
        have hmono := e.monotone hkLe
        change (e k').1 ≤ (e i.castSucc).1 at hmono
        simpa only [k', e.apply_symm_apply, point] using hmono
    have hRightLe : point i.succ ≤ right j := by
      by_cases hh : hi ≤ right j
      · exact (hBSubset _ (e i.succ).2).2.trans hh
      · have hrightMem : right j ∈ B := by
          simp only [B, Finset.mem_insert, Finset.mem_filter]
          right; right
          refine ⟨?_, ?_, le_of_lt (lt_of_not_ge hh)⟩
          · simp only [endpoints, Finset.mem_union, Finset.mem_image,
              Finset.mem_univ, true_and]
            exact Or.inr ⟨j, rfl⟩
          · exact (hBSubset _ (e i.castSucc).2).1.trans
              ((show point i.castSucc < q.re from hqU.1.1).le.trans hQRight.le)
        let k' : Fin (n + 1) := e.symm ⟨right j, hrightMem⟩
        have hik : i.castSucc < k' := by
          apply e.lt_iff_lt.mp
          change (e i.castSucc).1 < (e k').1
          simpa only [k', e.apply_symm_apply, point] using
            hqU.1.1.trans hQRight
        have hiSuccLe : i.succ ≤ k' := by
          rw [Fin.lt_def] at hik
          rw [Fin.le_iff_val_le_val]
          simp only [Fin.val_succ, Fin.val_castSucc] at hik ⊢
          omega
        have hmono := e.monotone hiSuccLe
        change (e i.succ).1 ≤ (e k').1 at hmono
        simpa only [k', e.apply_symm_apply, point] using hmono
    have hLeftEq : left j = point i.castSucc := by
      apply le_antisymm hLeftLe
      by_contra hStrict
      apply hBreakpointNotOpen _ (e i.castSucc).2
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      refine ⟨s, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      have hmem : point i.castSucc - s.1.re ∈
          Set.Ioo ((H sF).left k) ((H sF).right k) := by
        dsimp only [left, right, j] at hStrict hRightLe ⊢
        constructor <;> linarith
      have : point i.castSucc - s.1.re ∈
          Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K
            (y - s.1.im) := by
        exact (H sF).union_eq.symm ▸ Set.mem_iUnion_of_mem k hmem
      have heq : (-s.1 : Tiling.Plane) +ᵥ Complex.mk (point i.castSucc) y =
          Complex.mk (point i.castSucc - s.1.re) (y - s.1.im) := by
        apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
      change -s.1 +ᵥ Complex.mk (point i.castSucc) y ∈ K.openCarrier
      rw [heq]
      exact this
    have hRightEq : right j = point i.succ := by
      apply le_antisymm
      · by_contra hStrict
        apply hBreakpointNotOpen _ (e i.succ).2
        rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
        refine ⟨s, ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        have hmem : point i.succ - s.1.re ∈
            Set.Ioo ((H sF).left k) ((H sF).right k) := by
          dsimp only [left, right, j] at hLeftLe hStrict ⊢
          constructor <;> linarith
        have : point i.succ - s.1.re ∈
            Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K
              (y - s.1.im) := by
          exact (H sF).union_eq.symm ▸ Set.mem_iUnion_of_mem k hmem
        have heq : (-s.1 : Tiling.Plane) +ᵥ Complex.mk (point i.succ) y =
            Complex.mk (point i.succ - s.1.re) (y - s.1.im) := by
          apply Complex.ext <;> simp [sub_eq_add_neg, add_comm]
        change -s.1 +ᵥ Complex.mk (point i.succ) y ∈ K.openCarrier
        rw [heq]
        exact this
      · exact hRightLe
    exact ⟨j, hLeftEq, hRightEq⟩
  let label : Fin n → I := fun i ↦ (gap_has_interval i).choose
  have hLabel (i : Fin n) :
      left (label i) = point i.castSucc ∧
        right (label i) = point i.succ := (gap_has_interval i).choose_spec
  let leftVertex : Fin n → ↑K.vertices :=
    fun i ↦ (H (label i).1).leftVertex (label i).2
  let rightVertex : Fin n → ↑K.vertices :=
    fun i ↦ (H (label i).1).rightVertex (label i).2
  let centre : Fin n → ↑T := fun i ↦
    ⟨(label i).1.1,
      (Set.Finite.mem_toFinset hRFinite).mp (label i).1.2 |>.1⟩
  apply boundaryStepChain_of_labelledArrangement hn point hPointZero hPointLast
    hPointMono leftVertex rightVertex centre
  intro i
  constructor
  · have hcoord := (H (label i).1).leftVertex_coord (label i).2
    have hend := (hLabel i).1
    dsimp only [leftVertex, centre, left] at hcoord hend ⊢
    linarith
  · have hcoord := (H (label i).1).rightVertex_coord (label i).2
    have hend := (hLabel i).2
    dsimp only [rightVertex, centre, right] at hcoord hend ⊢
    linarith

private theorem boundaryChainExtraction :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ {c : ℝ},
      ({z : Tiling.Plane | z.re = c} ⊆
        ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support)) →
      ∀ (v : ↥K.vertices) (t : ↥T),
      (v.1 + (t.1 : Tiling.Plane)).re ≠ c →
      Nonempty (BoundaryStepChain K T
        (min c (v.1 + (t.1 : Tiling.Plane)).re)
        (max c (v.1 + (t.1 : Tiling.Plane)).re)) :=
  boundaryChainExtraction_proof relevantTilesFinite

private theorem projectedCentresRelativelyDense :
    (∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
    Tiling.AxisParallel.TilesOn K T Set.univ →
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ,
      ∃ t ∈ T, |t.re - x| < R) := by
  intro K T hTile
  obtain ⟨D, hD⟩ := K.isPolygonal.isBounded.subset_closedBall (0 : Tiling.Plane)
  let R : ℝ := max D 0 + 1
  refine ⟨R, by dsimp [R]; linarith [le_max_right D 0], fun x ↦ ?_⟩
  let z : Tiling.Plane := (x : ℂ)
  have hcover : ∀ᵐ q ∂MeasureTheory.volume,
      ∃ t : ↥T, q ∈ ((t.1 : Tiling.Plane) +ᵥ K.openCarrier) := by
    filter_upwards [hTile.2.2] with q hq
    exact (hq.mp (Set.mem_univ q))
  have hex : ∃ q ∈ Metric.ball z 1,
      ∃ t : ↥T, q ∈ ((t.1 : Tiling.Plane) +ᵥ K.openCarrier) := by
    by_contra hn
    push Not at hn
    have hballnull : MeasureTheory.volume (Metric.ball z 1) = 0 := by
      apply MeasureTheory.measure_mono_null (t := {q | ¬ ∃ t : ↥T,
        q ∈ ((t.1 : Tiling.Plane) +ᵥ K.openCarrier)})
      · intro q hq
        change ¬ ∃ t : ↥T, q ∈ ((t.1 : Tiling.Plane) +ᵥ K.openCarrier)
        rintro ⟨t, ht⟩
        exact hn q hq t ht
      · exact MeasureTheory.ae_iff.mp hcover
    exact (Metric.measure_ball_pos MeasureTheory.volume z zero_lt_one).ne' hballnull
  obtain ⟨q, hqball, t, hqt⟩ := hex
  refine ⟨t.1, t.2, ?_⟩
  rw [mem_vadd_set] at hqt
  obtain ⟨k, hk, hkq⟩ := hqt
  have hkclosed : k ∈ Metric.closedBall (0 : Tiling.Plane) D :=
    hD (interior_subset hk)
  have hkbound : ‖k‖ ≤ max D 0 := by
    have : ‖k‖ ≤ D := by simpa [Metric.mem_closedBall, dist_eq_norm] using hkclosed
    exact this.trans (le_max_left _ _)
  have hqbound : ‖q - z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hqball
  have hreal : |t.1.re - x| ≤ ‖(t.1 : Tiling.Plane) - z‖ := by
    simpa [z] using Complex.abs_re_le_norm ((t.1 : Tiling.Plane) - z)
  calc
    |t.1.re - x| ≤ ‖(t.1 : Tiling.Plane) - z‖ := hreal
    _ = ‖q - k - z‖ := by rw [← hkq]; simp
    _ ≤ ‖k‖ + ‖q - z‖ := by
      rw [show q - k - z = (q - z) - k by abel, norm_sub_rev]
      exact norm_sub_le _ _
    _ < max D 0 + 1 := add_lt_add_of_le_of_lt hkbound hqbound
    _ = R := rfl

private theorem projectedCentresUnboundedBothWays :
    (∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
    Tiling.AxisParallel.TilesOn K T Set.univ →
    (¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T) →
    (∀ a : ℝ, ∃ x ∈ Complex.re '' T, x < a) ∧
      (∀ a : ℝ, ∃ x ∈ Complex.re '' T, a < x)) := by
  intro K T hTile _hNontrivial
  obtain ⟨R, hR, hdense⟩ := projectedCentresRelativelyDense hTile
  constructor
  · intro a
    obtain ⟨t, ht, hdist⟩ := hdense (a - R - 1)
    refine ⟨t.re, ⟨t, ht, rfl⟩, ?_⟩
    rw [abs_lt] at hdist
    linarith
  · intro a
    obtain ⟨t, ht, hdist⟩ := hdense (a + R + 1)
    refine ⟨t.re, ⟨t, ht, rfl⟩, ?_⟩
    rw [abs_lt] at hdist
    linarith

private theorem boundaryStepChain_endpointDifference
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane} {x y : ℝ}
    (C : BoundaryStepChain K T x y) (i : Fin C.length) :
    C.point i.succ - C.point i.castSucc =
      (C.rightVertex i).1.re - (C.leftVertex i).1.re := by
  rcases C.endpoint_coordinates i with ⟨hl, hr⟩
  linarith

private theorem fin_sum_successive_sub
    (n : ℕ) (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  let g : ℕ → ℝ := fun i ↦ if hi : i < n + 1 then f ⟨i, hi⟩ else f (Fin.last n)
  calc
    ∑ i : Fin n, (f i.succ - f i.castSucc) =
        ∑ i : Fin n, (g (i + 1) - g i) := by
          apply Finset.sum_congr rfl
          intro i _
          have hsucc : g (i + 1) = f i.succ := by
            dsimp only [g]
            rw [dif_pos (by omega)]
            congr 1
          have hcast : g i = f i.castSucc := by
            simp only [g, dif_pos (Nat.lt_trans i.isLt (Nat.lt_succ_self n))]
            congr 1
          rw [hsucc, hcast]
    _ = ∑ i ∈ Finset.range n, (g (i + 1) - g i) :=
      Fin.sum_univ_eq_sum_range (fun i ↦ g (i + 1) - g i) n
    _ = g n - g 0 := Finset.sum_range_sub g n
    _ = f (Fin.last n) - f 0 := by
      have hn : g n = f (Fin.last n) := by
        simp only [g, dif_pos (Nat.lt_succ_self n)]
        congr 1
      have hzero : g 0 = f 0 := by simp [g]
      rw [hn, hzero]

private theorem boundaryStepChain_sum
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane} {x y : ℝ}
    (C : BoundaryStepChain K T x y) :
    ∑ i : Fin C.length, (C.point i.succ - C.point i.castSucc) = y - x := by
  rw [fin_sum_successive_sub, C.point_last, C.point_zero]

private theorem horizontalBoundaryDistance_eq_stepSum_proof
    (hExtract : (∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
    Tiling.AxisParallel.TilesOn K T Set.univ →
    ∀ {c : ℝ},
      ({z : Tiling.Plane | z.re = c} ⊆
        ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support)) →
    ∀ (v : ↥K.vertices) (t : ↥T),
      (v.1 + (t.1 : Tiling.Plane)).re ≠ c →
      Nonempty (BoundaryStepChain K T
        (min c (v.1 + (t.1 : Tiling.Plane)).re)
        (max c (v.1 + (t.1 : Tiling.Plane)).re)))) :
    ∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
      ∀ (_hTile : Tiling.AxisParallel.TilesOn K T Set.univ),
      ∀ {c : ℝ},
      ∀ (_hline : {z : Tiling.Plane | z.re = c} ⊆
        ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support)),
      ∀ (v : ↥K.vertices) (t : ↥T),
      (v.1 + (t.1 : Tiling.Plane)).re ≠ c →
      ∃ n : ℕ, 0 < n ∧ ∃ step : Fin n → ℝ,
        (∀ i : Fin n, step i ∈ K.horizontalStepAlphabet) ∧
        |(v.1 + (t.1 : Tiling.Plane)).re - c| = ∑ i, step i := by
  intro K T hTile c hline v t hne
  obtain ⟨C⟩ := hExtract hTile hline v t hne
  refine ⟨C.length, C.length_pos,
    fun i ↦ C.point i.succ - C.point i.castSucc, C.step_mem, ?_⟩
  rw [boundaryStepChain_sum]
  have hminmax :
      max c (v.1 + (t.1 : Tiling.Plane)).re -
          min c (v.1 + (t.1 : Tiling.Plane)).re =
        |(v.1 + (t.1 : Tiling.Plane)).re - c| := by
    exact max_sub_min_eq_abs _ _
  exact hminmax.symm

private theorem horizontalBoundaryStepCount_le_proof
    (hDistance : ∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
      ∀ (_hTile : Tiling.AxisParallel.TilesOn K T Set.univ),
      ∀ {c : ℝ},
      ∀ (_hline : {z : Tiling.Plane | z.re = c} ⊆
        ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support)),
      ∀ (v : ↥K.vertices) (t : ↥T),
      (v.1 + (t.1 : Tiling.Plane)).re ≠ c →
      ∃ n : ℕ, 0 < n ∧ ∃ step : Fin n → ℝ,
        (∀ i : Fin n, step i ∈ K.horizontalStepAlphabet) ∧
        |(v.1 + (t.1 : Tiling.Plane)).re - c| = ∑ i, step i) :
    ∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
      Tiling.AxisParallel.TilesOn K T Set.univ →
      ∀ {c R delta : ℝ},
      ({z : Tiling.Plane | z.re = c} ⊆
        ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support)) →
      0 < delta →
      (∀ d ∈ K.horizontalStepAlphabet, delta ≤ d) →
      ∀ (v : ↥K.vertices) (t : ↥T),
      (v.1 + (t.1 : Tiling.Plane)).re ≠ c →
      |(v.1 + (t.1 : Tiling.Plane)).re - c| ≤ R →
      ∃ n : ℕ, 0 < n ∧ ∃ step : Fin n → ℝ,
        (∀ i : Fin n, step i ∈ K.horizontalStepAlphabet) ∧
        |(v.1 + (t.1 : Tiling.Plane)).re - c| = ∑ i, step i ∧
        (n : ℝ) * delta ≤ R := by
  intro K T hTile c R delta hline hdelta hdelta_le v t hne hR
  obtain ⟨n, hn, step, hstep, hsum⟩ := hDistance hTile hline v t hne
  refine ⟨n, hn, step, hstep, hsum, ?_⟩
  calc
    (n : ℝ) * delta = ∑ _i : Fin n, delta := by simp
    _ ≤ ∑ i : Fin n, step i := Finset.sum_le_sum fun i _ ↦ hdelta_le _ (hstep i)
    _ = |(v.1 + (t.1 : Tiling.Plane)).re - c| := hsum.symm
    _ ≤ R := hR

private def ProjectedCentresLocallyFinite : Prop :=
  ∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
    Tiling.AxisParallel.TilesOn K T Set.univ →
    (¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T) →
    ∀ Q : Set ℝ, Bornology.IsBounded Q →
      ((Complex.re '' T) ∩ Q).Finite

private theorem projectedCentres_locallyFinite
    (hComplete : (∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
    Tiling.AxisParallel.TilesOn K T Set.univ →
    (¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T) →
    ∃ (P : Tiling.AxisParallel.Continuous.VerticalPlate K T) (X : Set ℝ) (c : ℝ),
      P.centres.Nonempty ∧ X.Nonempty ∧ X ≠ Set.univ ∧
      IsOpen X ∧ interior (closure X) = X ∧ c ∈ frontier X ∧
      P.support = Complex.re ⁻¹' X ∧
      {z : Tiling.Plane | z.re = c} ⊆
        ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support)))
    (hExtract : (∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
    Tiling.AxisParallel.TilesOn K T Set.univ →
    ∀ {c : ℝ},
      ({z : Tiling.Plane | z.re = c} ⊆
        ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support)) →
    ∀ (v : ↥K.vertices) (t : ↥T),
      (v.1 + (t.1 : Tiling.Plane)).re ≠ c →
      Nonempty (BoundaryStepChain K T
        (min c (v.1 + (t.1 : Tiling.Plane)).re)
        (max c (v.1 + (t.1 : Tiling.Plane)).re)))) : ProjectedCentresLocallyFinite := by
  intro K T hTile hNontrivial Q hQ
  obtain ⟨P, X, c, -, -, -, -, -, -, -, hline⟩ := hComplete hTile hNontrivial
  obtain ⟨d, hd⟩ := K.horizontalStepAlphabet_nonempty
  obtain ⟨v, hv, w, hw, hdvw, hdpos⟩ :=
    (K.mem_horizontalStepAlphabet_iff d).mp hd
  let vK : ↑K.vertices := ⟨v, hv⟩
  let A : Finset ℝ := K.horizontalStepAlphabet
  have hAne : A.Nonempty := by simpa only [A] using K.horizontalStepAlphabet_nonempty
  let delta : ℝ := A.min' hAne
  have hdelta : 0 < delta := by
    apply K.horizontalStepAlphabet_pos
    simpa only [A] using A.min'_mem hAne
  have hdeltaLe : ∀ a ∈ A, delta ≤ a := by
    intro a ha
    exact A.min'_le a ha
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hQ
  let R : ℝ := |v.re| + |r| + |c| + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (R / delta)
  let Codes := Fin 2 × (Σ m : Fin N, Fin m.1 → ↑A)
  let value : Codes → ℝ := fun code ↦
    if code.1 = 0 then c - v.re - ∑ i, (code.2.2 i).1
    else c - v.re + ∑ i, (code.2.2 i).1
  apply ((Set.finite_range value).insert (c - v.re)).subset
  rintro x ⟨⟨t, htT, rfl⟩, htreQ⟩
  let tT : ↑T := ⟨t, htT⟩
  let p : ℝ := v.re + t.re
  by_cases hp : p = c
  · left
    dsimp only [p] at hp
    linarith
  · right
    have hpPlaced : (vK.1 + (tT.1 : Tiling.Plane)).re ≠ c := by
      simpa only [Complex.add_re, vK, tT, p] using hp
    obtain ⟨C⟩ := hExtract hTile hline vK tT hpPlaced
    have htAbs : |t.re| ≤ r := by
      have := hr htreQ
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using this
    have hpBound : |p - c| ≤ R := by
      have htri : |v.re + t.re - c| ≤ |v.re| + |t.re| + |c| := by
        calc
          |v.re + t.re - c| ≤ |v.re + t.re| + |c| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              abs_sub_le (v.re + t.re) 0 c
          _ ≤ |v.re| + |t.re| + |c| := by
            gcongr
            exact abs_add_le _ _
      dsimp only [p, R]
      exact htri.trans (by nlinarith [htAbs, le_abs_self r])
    have hsum : ∑ i : Fin C.length,
        (C.point i.succ - C.point i.castSucc) = |p - c| := by
      rw [boundaryStepChain_sum]
      calc
        max c (vK.1 + (tT.1 : Tiling.Plane)).re -
            min c (vK.1 + (tT.1 : Tiling.Plane)).re =
            |(vK.1 + (tT.1 : Tiling.Plane)).re - c| :=
          max_sub_min_eq_abs _ _
        _ = |p - c| := by simp [vK, tT, p]
    have hmul : (C.length : ℝ) * delta ≤ R := by
      calc
        (C.length : ℝ) * delta = ∑ _i : Fin C.length, delta := by simp
        _ ≤ ∑ i : Fin C.length,
            (C.point i.succ - C.point i.castSucc) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hdeltaLe _ (by simpa only [A] using C.step_mem i)
        _ = |p - c| := hsum
        _ ≤ R := hpBound
    have hnN : C.length < N := by
      have hnreal : (C.length : ℝ) < N := by
        have hRN : R < (N : ℝ) * delta := (div_lt_iff₀ hdelta).mp hN
        nlinarith
      exact_mod_cast hnreal
    let codeWord : Σ m : Fin N, Fin m.1 → ↑A :=
      ⟨⟨C.length, hnN⟩, fun i ↦
        ⟨C.point i.succ - C.point i.castSucc,
          by simpa only [A] using C.step_mem i⟩⟩
    rcases lt_or_gt_of_ne hp with hpLt | hpGt
    · refine ⟨((0 : Fin 2), codeWord), ?_⟩
      simp only [value, codeWord, Fin.isValue, ↓reduceIte]
      have habs : |p - c| = c - p := by
        rw [abs_of_nonpos (sub_nonpos.mpr hpLt.le)]
        ring
      rw [hsum, habs]
      dsimp only [p]
      ring
    · refine ⟨((1 : Fin 2), codeWord), ?_⟩
      simp only [value, codeWord, Fin.isValue, one_ne_zero, ↓reduceIte]
      have habs : |p - c| = p - c := abs_of_pos (sub_pos.mpr hpGt)
      rw [hsum, habs]
      dsimp only [p]
      ring

private theorem projectedCentres_eventuallyConstant_proof
    (hLocal : ProjectedCentresLocallyFinite) :
    ∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
      Tiling.AxisParallel.TilesOn K T Set.univ →
      (¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
        ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T) →
      ∀ (x : ℕ → ℝ), (∀ n : ℕ, x n ∈ Complex.re '' T) →
      ∀ {a : ℝ}, Filter.Tendsto x Filter.atTop (nhds a) →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → x n = a := by
  intro K T hTile hNontrivial x hx a hxa
  let Z : Set ℝ := Complex.re '' T
  let S : Set ℝ := Z ∩ Metric.closedBall a 1
  have hSFinite : S.Finite := by
    exact hLocal hTile hNontrivial (Metric.closedBall a 1)
      (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall a 1))
  let D : Set ℝ := S \ {a}
  have hDClosed : IsClosed D := hSFinite.sdiff.isClosed
  have haD : a ∈ Dᶜ := by
    change a ∉ S \ {a}
    intro ha
    exact ha.2 rfl
  have hEventuallyNotD : ∀ᶠ n in Filter.atTop, x n ∈ Dᶜ :=
    hxa (hDClosed.isOpen_compl.mem_nhds haD)
  have hEventuallyBall : ∀ᶠ n in Filter.atTop, x n ∈ Metric.ball a 1 :=
    hxa (Metric.ball_mem_nhds a zero_lt_one)
  rw [Filter.eventually_atTop] at hEventuallyNotD hEventuallyBall
  obtain ⟨nD, hnD⟩ := hEventuallyNotD
  obtain ⟨nB, hnB⟩ := hEventuallyBall
  refine ⟨max nD nB, fun n hn ↦ ?_⟩
  have hnD' := hnD n ((le_max_left _ _).trans hn)
  have hnB' := hnB n ((le_max_right _ _).trans hn)
  by_contra hne
  apply hnD'
  refine ⟨⟨hx n, ?_⟩, hne⟩
  exact Metric.mem_closedBall'.2 (Metric.mem_ball'.1 hnB').le

private theorem projectedCentres_closedLocallyFinite_proof
    (hLocal : ProjectedCentresLocallyFinite) :
    ∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
      Tiling.AxisParallel.TilesOn K T Set.univ →
      (¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
        ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T) →
      IsClosed (Complex.re '' T) ∧
        ∀ Q : Set ℝ, Bornology.IsBounded Q →
          ((Complex.re '' T) ∩ Q).Finite := by
  intro K T hTile hNontrivial
  have hloc := hLocal hTile hNontrivial
  refine ⟨?_, hloc⟩
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hSFinite := hloc (Metric.closedBall x 1)
    (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall x 1))
  let S : Set ℝ := (Complex.re '' T) ∩ Metric.closedBall x 1
  have hSClosed : IsClosed S := by
    apply Set.Finite.isClosed
    simpa only [S] using hSFinite
  have hxSCompl : x ∈ Sᶜ := by
    intro hxS
    exact hx hxS.1
  apply Filter.mem_of_superset
    (inter_mem (hSClosed.isOpen_compl.mem_nhds hxSCompl)
      (Metric.ball_mem_nhds x zero_lt_one))
  rintro y ⟨hyS, hyBall⟩ hyZ
  apply hyS
  exact ⟨hyZ, Metric.mem_closedBall'.2 (Metric.mem_ball'.1 hyBall).le⟩

private theorem locallyFiniteOrderEnumeration : (∀ {Z : Set ℝ}, Z.Nonempty →
    (∀ Q : Set ℝ, Bornology.IsBounded Q → (Z ∩ Q).Finite) →
    (∀ a : ℝ, ∃ x ∈ Z, x < a) →
    (∀ a : ℝ, ∃ x ∈ Z, a < x) →
    ∃ z : ℤ → ℝ, StrictMono z ∧ Set.range z = Z) := by
  intro Z hZNonempty hLocal hBelow hAbove
  let _ : Nonempty Z := hZNonempty.to_subtype
  let _ : LocallyFiniteOrder Z := LocallyFiniteOrder.ofFiniteIcc fun a b ↦ by
    have hFinite := hLocal (Set.Icc a.1 b.1) (Metric.isBounded_Icc a.1 b.1)
    apply (Set.Finite.preimage Subtype.val_injective.injOn hFinite).subset
    intro x hx
    exact ⟨x.2, hx⟩
  let _ : SuccOrder Z := LinearLocallyFiniteOrder.succOrder Z
  let _ : PredOrder Z := LinearLocallyFiniteOrder.predOrder Z
  let _ : NoMaxOrder Z := ⟨fun z ↦ by
    obtain ⟨x, hxZ, hzx⟩ := hAbove z.1
    exact ⟨⟨x, hxZ⟩, hzx⟩⟩
  let _ : NoMinOrder Z := ⟨fun z ↦ by
    obtain ⟨x, hxZ, hxz⟩ := hBelow z.1
    exact ⟨⟨x, hxZ⟩, hxz⟩⟩
  let e : Z ≃o ℤ := orderIsoIntOfLinearSuccPredArch
  let z : ℤ → ℝ := fun n ↦ (e.symm n).1
  refine ⟨z, ?_, ?_⟩
  · intro m n hmn
    exact e.symm.strictMono hmn
  · ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact (e.symm n).2
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)

private theorem exists_increasingProjectedCentreEnumeration_proof
    (hLocal : ProjectedCentresLocallyFinite)
    (hRelativelyDense : (∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
    Tiling.AxisParallel.TilesOn K T Set.univ →
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ,
      ∃ t ∈ T, |t.re - x| < R))
    (hUnbounded : (∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
    Tiling.AxisParallel.TilesOn K T Set.univ →
    (¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T) →
    (∀ a : ℝ, ∃ x ∈ Complex.re '' T, x < a) ∧
      (∀ a : ℝ, ∃ x ∈ Complex.re '' T, a < x)))
    (hEnumeration : (∀ {Z : Set ℝ}, Z.Nonempty →
    (∀ Q : Set ℝ, Bornology.IsBounded Q → (Z ∩ Q).Finite) →
    (∀ a : ℝ, ∃ x ∈ Z, x < a) →
    (∀ a : ℝ, ∃ x ∈ Z, a < x) →
    ∃ z : ℤ → ℝ, StrictMono z ∧ Set.range z = Z)) :
    ∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane},
      Tiling.AxisParallel.TilesOn K T Set.univ →
      (¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
        ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T) →
      ∃ z : ℤ → ℝ, StrictMono z ∧ Set.range z = Complex.re '' T := by
  intro K T hTile hNontrivial
  obtain ⟨R, hR, hDense⟩ := hRelativelyDense hTile
  obtain ⟨t, htT, htR⟩ := hDense 0
  have hNonempty : (Complex.re '' T).Nonempty := ⟨t.re, t, htT, rfl⟩
  exact hEnumeration hNonempty (hLocal hTile hNontrivial)
    (hUnbounded hTile hNontrivial).1 (hUnbounded hTile hNontrivial).2

theorem horizontalBoundaryDistance_eq_stepSum :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ {c : ℝ},
      ({z : Tiling.Plane | z.re = c} ⊆
        ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support)) →
      ∀ (v : ↥K.vertices) (t : ↥T),
      (v.1 + (t.1 : Tiling.Plane)).re ≠ c →
      ∃ n : ℕ, 0 < n ∧ ∃ step : Fin n → ℝ,
        (∀ i : Fin n, step i ∈ K.horizontalStepAlphabet) ∧
        |(v.1 + (t.1 : Tiling.Plane)).re - c| = ∑ i, step i :=
  horizontalBoundaryDistance_eq_stepSum_proof
    boundaryChainExtraction

theorem horizontalBoundaryStepCount_le :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ {c R delta : ℝ},
      ({z : Tiling.Plane | z.re = c} ⊆
        ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support)) →
      0 < delta →
      (∀ d ∈ K.horizontalStepAlphabet, delta ≤ d) →
      ∀ (v : ↥K.vertices) (t : ↥T),
      (v.1 + (t.1 : Tiling.Plane)).re ≠ c →
      |(v.1 + (t.1 : Tiling.Plane)).re - c| ≤ R →
      ∃ n : ℕ, 0 < n ∧ ∃ step : Fin n → ℝ,
        (∀ i : Fin n, step i ∈ K.horizontalStepAlphabet) ∧
        |(v.1 + (t.1 : Tiling.Plane)).re - c| = ∑ i, step i ∧
        (n : ℝ) * delta ≤ R :=
  horizontalBoundaryStepCount_le_proof horizontalBoundaryDistance_eq_stepSum

theorem projectedCentres_closedLocallyFinite :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (¬ ∃ P : Continuous.VerticalPlate K T,
        ¬ Continuous.IsVerticalColumn P ∧ P.centres = T) →
      IsClosed (Complex.re '' T) ∧
        ∀ Q : Set ℝ, Bornology.IsBounded Q → ((Complex.re '' T) ∩ Q).Finite :=
  projectedCentres_closedLocallyFinite_proof
    (projectedCentres_locallyFinite completeVerticalPlateBoundary
      boundaryChainExtraction)

theorem projectedCentres_eventuallyConstant :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (¬ ∃ P : Continuous.VerticalPlate K T,
        ¬ Continuous.IsVerticalColumn P ∧ P.centres = T) →
      ∀ (x : ℕ → ℝ), (∀ n : ℕ, x n ∈ Complex.re '' T) →
      ∀ {a : ℝ}, Filter.Tendsto x Filter.atTop (nhds a) →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → x n = a :=
  projectedCentres_eventuallyConstant_proof
    (projectedCentres_locallyFinite completeVerticalPlateBoundary
      boundaryChainExtraction)

theorem exists_increasingProjectedCentreEnumeration :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (¬ ∃ P : Continuous.VerticalPlate K T,
        ¬ Continuous.IsVerticalColumn P ∧ P.centres = T) →
      ∃ z : ℤ → ℝ, StrictMono z ∧ Set.range z = Complex.re '' T :=
  exists_increasingProjectedCentreEnumeration_proof
    (projectedCentres_locallyFinite completeVerticalPlateBoundary
      boundaryChainExtraction)
    projectedCentresRelativelyDense
    projectedCentresUnboundedBothWays locallyFiniteOrderEnumeration

end Structure

end Tiling.AxisParallel
