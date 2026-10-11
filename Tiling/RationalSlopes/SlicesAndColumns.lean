import Tiling.RationalSlopes.BoundaryGeometry
import Tiling.Topology.TilingHull
import Tiling.AxisParallel.OneDimensional.FiniteInterval.PeriodConsequences
import Tiling.AxisParallel.OneDimensional.FiniteInterval.PeriodicTarget

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.Polygonal

open Tiling.RationalPolygonal (PolygonalRegion)

/-- A nonempty complete column, including the common packing requirement. -/
def IsCenterColumn (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (C : Set Plane) : Prop :=
  IsPacking K.prototileFamily (K.placements C) ∧ C.Nonempty ∧
    IsLineSupported C δ ∧ IsInvariantAlong (regularSupport K C) δ

/-- Empty centre sets are allowed; each existing whole fibre must be a column. -/
def IsUnionOfColumns (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) : Prop :=
  ∀ t ∈ T, IsCenterColumn K δ (lineFibre δ T t)

/-- Points whose complete affine directional fibre is contained in `D`. -/
def completeFibreCore (D : Set Plane) (δ : Submodule ℝ Plane) : Set Plane :=
  {x | x +ᵥ (δ : Set Plane) ⊆ D}

private theorem mem_completeFibreCore_iff {D : Set Plane} {δ : Submodule ℝ Plane}
    {x : Plane} : x ∈ completeFibreCore D δ ↔ ∀ v ∈ δ, x + v ∈ D := by
  constructor
  · intro hx v hv
    exact hx ⟨v, hv, rfl⟩
  · intro hx y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact hx v hv

/-- Compactness of the longitudinal circle is essential; openness alone is insufficient. -/
theorem completeFibreCore_isOpen_of_longitudinalPeriod
    {D : Set Plane} {δ : Submodule ℝ Plane} (hD : IsOpen D)
    (hδ : Module.finrank ℝ δ = 1) {p : Plane}
    (hpδ : p ∈ δ) (hp : p ≠ 0) (hperiod : p ∈ periodGroup D) :
    IsOpen (completeFibreCore D δ) := by
  classical
  have hspan : δ = Submodule.span ℝ ({p} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ hpδ hp
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let K : Set Plane := (fun r : ℝ => x + r • p) '' Set.Icc (0 : ℝ) 1
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc.image_of_continuousOn (by fun_prop)
  have hKsub : K ⊆ D := by
    rintro y ⟨r, hr, rfl⟩
    have : r • p ∈ (δ : Set Plane) := δ.smul_mem r hpδ
    change x +ᵥ (δ : Set Plane) ⊆ D at hx
    apply hx
    exact vadd_mem_vadd_set_iff.mpr this
  obtain ⟨ε, hε, hthick⟩ := hKcompact.exists_thickening_subset_open hD hKsub
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x hε) ?_
  intro y hy
  rw [Metric.mem_ball] at hy
  have hcore : y ∈ completeFibreCore D δ := by
    change y +ᵥ (δ : Set Plane) ⊆ D
    intro z hz
    change z ∈ y +ᵥ (δ : Set Plane) at hz
    rw [mem_vadd_set_iff_neg_vadd_mem] at hz
    rw [hspan] at hz
    change -y + z ∈ Submodule.span ℝ ({p} : Set Plane) at hz
    rcases Submodule.mem_span_singleton.mp hz with ⟨c, hc⟩
    have hz' : z = y + c • p := by
      calc
        z = y + (-y + z) := by abel
        _ = y + c • p := by rw [hc]
    rw [hz']
    let r : ℝ := Int.fract c
    let n : ℤ := ⌊c⌋
    have hr : r ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg c, le_of_lt (Int.fract_lt_one c)⟩
    have hclose : dist (y + r • p) (x + r • p) < ε := by
      simpa [dist_add_right] using hy
    have hnear : y + r • p ∈ Metric.thickening ε K := by
      rw [Metric.mem_thickening_iff]
      exact ⟨x + r • p, ⟨r, hr, rfl⟩, hclose⟩
    have hDnear : y + r • p ∈ D := hthick hnear
    have hpn : (n : ℤ) • p ∈ periodGroup D := by
      exact (periodGroup D).zsmul_mem hperiod n
    have hperiodn : (n : ℤ) • p +ᵥ D = D := hpn
    have hcoord : c • p = r • p + (n : ℤ) • p := by
      have hscalar : Int.fract c + (⌊c⌋ : ℝ) = c := by
        rw [Int.fract]
        ring
      calc
        c • p = (Int.fract c + (⌊c⌋ : ℝ)) • p := by rw [hscalar]
        _ = Int.fract c • p + (⌊c⌋ : ℝ) • p := by rw [add_smul]
        _ = r • p + (n : ℤ) • p := by simp [r, n]
    rw [hcoord]
    have htranslate : (n : ℤ) • p +ᵥ (y + r • p) ∈ ((n : ℤ) • p +ᵥ D) :=
      vadd_mem_vadd_set_iff.mpr hDnear
    rw [hperiodn] at htranslate
    have htranslate' : (n : ℤ) • p + (y + r • p) ∈ D := by
      simpa [vadd_eq_add] using htranslate
    simpa [vadd_eq_add, add_assoc, add_comm, add_left_comm] using htranslate'
  exact hcore

theorem completeFibreCore_invariant (D : Set Plane) (δ : Submodule ℝ Plane) :
    IsInvariantAlong (completeFibreCore D δ) δ := by
  intro u hu
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_completeFibreCore_iff] at hy ⊢
    intro v hv
    simpa only [vadd_eq_add, add_assoc, add_comm u] using hy (u + v) (δ.add_mem hu hv)
  · intro hx
    refine ⟨x - u, ?_, by simp⟩
    rw [mem_completeFibreCore_iff] at hx ⊢
    intro v hv
    convert hx (v - u) (δ.sub_mem hv hu) using 1
    simp only [sub_eq_add_neg]
    abel

theorem completeFibreCore_periods {D : Set Plane} (δ : Submodule ℝ Plane) :
    periodGroup D ≤ periodGroup (completeFibreCore D δ) := by
  intro u hu
  change u +ᵥ D = D at hu
  change u +ᵥ completeFibreCore D δ = completeFibreCore D δ
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_completeFibreCore_iff] at hy ⊢
    intro v hv
    have : u + (y + v) ∈ D := by
      rw [← hu]
      exact ⟨y + v, hy v hv, rfl⟩
    simpa only [vadd_eq_add, add_assoc] using this
  · intro hx
    refine ⟨x - u, ?_, by simp⟩
    rw [mem_completeFibreCore_iff] at hx ⊢
    intro v hv
    have : x + v ∈ u +ᵥ D := hu.symm ▸ hx v hv
    rcases this with ⟨y, hy, hxy⟩
    convert hy using 1
    change u + y = x + v at hxy
    linear_combination -hxy

/-- Relative regular complement, not the false literal equality `X_E \ B = X_A`. -/
private theorem regularOpen_union_complement
    {A B E : Set Plane} (hAopen : IsOpen A) (hAreg : interior (closure A) = A)
    (hBopen : IsOpen B) (hdisj : Disjoint A B)
    (hBreg : interior (closure B) = B) (hE : E = interior (closure (A ∪ B))) :
    A = E \ closure B ∧ B = E \ closure A := by
  have hEopen : IsOpen E := hE ▸ isOpen_interior
  have hA : E \ closure B ⊆ A := by
    have hopen : IsOpen (E \ closure B) := IsOpen.inter hEopen isClosed_closure.isOpen_compl
    have hsubset : E \ closure B ⊆ closure A := by
      intro x hx
      have hxint : x ∈ interior (closure (A ∪ B)) := hE ▸ hx.1
      have hxcl : x ∈ closure (A ∪ B) := interior_subset hxint
      rw [closure_union] at hxcl
      rcases hxcl with hxA | hxB
      · exact hxA
      · exact (hx.2 hxB).elim
    intro x hx
    have : x ∈ interior (closure A) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (hopen.mem_nhds hx) hsubset
    simpa [hAreg] using this
  have hB : E \ closure A ⊆ B := by
    have hopen : IsOpen (E \ closure A) := IsOpen.inter hEopen isClosed_closure.isOpen_compl
    have hsubset : E \ closure A ⊆ closure B := by
      intro x hx
      have hxint : x ∈ interior (closure (A ∪ B)) := hE ▸ hx.1
      have hxcl : x ∈ closure (A ∪ B) := interior_subset hxint
      rw [closure_union] at hxcl
      rcases hxcl with hxA | hxB
      · exact (hx.2 hxA).elim
      · exact hxB
    intro x hx
    have : x ∈ interior (closure B) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (hopen.mem_nhds hx) hsubset
    simpa [hBreg] using this
  constructor
  · apply Set.ext
    intro x
    constructor
    · intro hx
      have hxE : x ∈ E := by
        rw [hE, mem_interior_iff_mem_nhds]
        exact Filter.mem_of_superset (hAopen.mem_nhds hx) (fun _ hy => subset_closure (Or.inl hy))
      refine ⟨hxE, ?_⟩
      · intro hxcl
        have hdisj' : Disjoint A (closure B) := hdisj.closure_right hAopen
        exact hdisj'.le_bot ⟨hx, hxcl⟩
    · exact fun hx => hA hx
  · apply Set.ext
    intro x
    constructor
    · intro hx
      have hxE : x ∈ E := by
        rw [hE, mem_interior_iff_mem_nhds]
        exact Filter.mem_of_superset (hBopen.mem_nhds hx) (fun _ hy => subset_closure (Or.inr hy))
      refine ⟨hxE, ?_⟩
      · intro hxcl
        have hdisj' : Disjoint B (closure A) := hdisj.symm.closure_right hBopen
        exact hdisj'.le_bot ⟨hx, hxcl⟩
    · exact fun hx => hB hx

theorem columnComplement_completeFibreCore
    {A B E : Set Plane} {δ : Submodule ℝ Plane}
    (hAopen : IsOpen A) (hAreg : interior (closure A) = A)
    (hBopen : IsOpen B) (hBreg : interior (closure B) = B)
    (hdisj : Disjoint A B) (hE : E = interior (closure (A ∪ B)))
    (hBδ : IsInvariantAlong B δ)
    (hcoreOpen : IsOpen (completeFibreCore E δ)) :
    B = completeFibreCore E δ \ closure (completeFibreCore A δ) := by
  classical
  let XE := completeFibreCore E δ
  let XA := completeFibreCore A δ
  have hcomp := regularOpen_union_complement hAopen hAreg hBopen hdisj hBreg hE
  have hXA : XA ⊆ A := by
    intro x hx
    have : x ∈ x +ᵥ (δ : Set Plane) := by
      have hz : x +ᵥ (0 : Plane) ∈ x +ᵥ (δ : Set Plane) :=
        vadd_mem_vadd_set_iff.mpr δ.zero_mem
      simpa using hz
    exact hx this
  have hBXA : Disjoint B XA := (hdisj.mono_left hXA).symm
  have hBclXA : Disjoint B (closure XA) := hBXA.closure_right hBopen
  have hclosureInvariant : IsInvariantAlong (closure B) δ := by
    intro u hu
    calc
      u +ᵥ closure B = closure (u +ᵥ B) := (closure_vadd u B).symm
      _ = closure B := congrArg closure (hBδ u hu)
  have hXEsub : XE ⊆ XA ∪ closure B := by
    intro x hx
    by_cases hxB : x ∈ closure B
    · exact Or.inr hxB
    · apply Or.inl
      change x +ᵥ (δ : Set Plane) ⊆ A
      intro z hz
      have hzE : z ∈ E := hx hz
      have hznot : z ∉ closure B := by
        intro hzcl
        have hu : -x + z ∈ δ := by
          rw [mem_vadd_set_iff_neg_vadd_mem] at hz
          exact hz
        let u := -x + z
        have hzEq : z = x + u := by dsimp [u]; abel
        have hneg : -u ∈ δ := δ.neg_mem hu
        have hshift : -u +ᵥ closure B = closure B := hclosureInvariant (-u) hneg
        have hxcl : x ∈ closure B := by
          have hxshift : -u +ᵥ z ∈ -u +ᵥ closure B := by
            rw [vadd_mem_vadd_set_iff]
            exact hzcl
          rw [hshift] at hxshift
          rw [hzEq] at hxshift
          simpa [vadd_eq_add, u, add_assoc, add_comm, add_left_comm] using hxshift
        exact hxB hxcl
      exact hcomp.1.symm ▸ ⟨hzE, hznot⟩
  have hBsub : B ⊆ XE \ closure XA := by
    intro x hx
    refine ⟨?_, ?_⟩
    · change x +ᵥ (δ : Set Plane) ⊆ E
      intro z hz
      have hu : -x + z ∈ δ := by
        rw [mem_vadd_set_iff_neg_vadd_mem] at hz
        exact hz
      let u := -x + z
      have hzEq : z = x + u := by dsimp [u]; abel
      rw [hzEq]
      have hshift : u +ᵥ x ∈ B := by
        have hmem : u +ᵥ x ∈ u +ᵥ B := vadd_mem_vadd_set_iff.mpr hx
        simpa [hBδ u hu] using hmem
      have hshiftE : u +ᵥ x ∈ E := (hcomp.2 ▸ hshift).1
      simpa [vadd_eq_add, add_comm] using hshiftE
    · intro hxcl
      exact hBclXA.le_bot ⟨hx, hxcl⟩
  have hrevClosure : XE \ closure XA ⊆ closure B := by
    intro x hx
    by_contra hxB
    have hxA : x ∈ XA := (hXEsub hx.1).resolve_right hxB
    exact hx.2 (subset_closure hxA)
  have hrev : XE \ closure XA ⊆ B := by
    intro x hx
    have hopen : IsOpen (XE \ closure XA) := IsOpen.inter hcoreOpen isClosed_closure.isOpen_compl
    have hxB : x ∈ interior (closure B) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (hopen.mem_nhds hx) hrevClosure
    simpa [hBreg] using hxB
  exact Set.Subset.antisymm hBsub hrev

private theorem exists_lattice_period_not_mem_line {E : Set Plane}
    {δ : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1)
    (hEper : IsLatticePeriodic E) :
    ∃ β : Plane, β ∈ periodGroup E ∧ β ∉ δ := by
  classical
  obtain ⟨L, hL⟩ := hEper
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, L.basis i ∉ δ := by
    by_contra h
    push Not at h
    have hspan : Submodule.span ℝ (Set.range L.basis) ≤ δ := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨i, rfl⟩
      exact h i
    have hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range L.basis)) = 2 := by
      rw [finrank_span_eq_card L.independent]
      simp
    have := Submodule.finrank_mono hspan
    rw [hdim, hδ] at this
    norm_num at this
  refine ⟨L.basis i, hL ?_, hi⟩
  exact AddSubgroup.subset_closure ⟨i, rfl⟩

private theorem planarCrossCLM_ker_eq_span {p : Plane} (hp : p ≠ 0) :
    LinearMap.ker (Tiling.planarCrossCLM p).toLinearMap =
      Submodule.span ℝ ({p} : Set Plane) := by
  ext z
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  change Tiling.planarCross p z = 0 ↔ ∃ r : ℝ, r • p = z
  constructor
  · intro hz
    have hline : z ∈ Tiling.affineLine 0 p := by
      change Tiling.planarCross p z - Tiling.planarCross p 0 = 0
      simpa [Tiling.planarCross] using hz
    rcases (Tiling.mem_affineLine_iff_exists_smul hp).mp hline with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    simpa using hr.symm
  · rintro ⟨r, rfl⟩
    simp [Tiling.planarCross]
    ring

private theorem planarCrossCLM_surjective {u : Plane} (hu : u ≠ 0) :
    Surjective (Tiling.planarCrossCLM u) := by
  have hcross : Tiling.planarCrossCLM u (u * Complex.I) ≠ 0 := by
    have hcoord : u.re ≠ 0 ∨ u.im ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hu (Complex.ext (by simpa using hn.1) (by simpa using hn.2))
    change u.re * (u * Complex.I).im - u.im * (u * Complex.I).re ≠ 0
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub]
    rcases hcoord with hr | hi
    · nlinarith [sq_pos_of_ne_zero hr, sq_nonneg u.im]
    · nlinarith [sq_pos_of_ne_zero hi, sq_nonneg u.re]
  intro r
  refine ⟨(r / Tiling.planarCrossCLM u (u * Complex.I)) • (u * Complex.I), ?_⟩
  rw [map_smul]
  exact div_mul_cancel₀ r hcross

private theorem period_mem_image_period {f : Plane →L[ℝ] ℝ} {S : Set Plane}
    {v : Plane} (hv : v ∈ periodGroup S) :
    f v ∈ periodGroup (f '' S) := by
  change v +ᵥ S = S at hv
  change f v +ᵥ (f '' S) = f '' S
  calc
    f v +ᵥ (f '' S) = f '' (v +ᵥ S) := by
      ext r
      constructor
      · intro hr
        have hsimage : -f v + r ∈ f '' S := by
          rw [mem_vadd_set_iff_neg_vadd_mem] at hr
          exact hr
        rcases hsimage with ⟨s, hs, hfs⟩
        refine ⟨v +ᵥ s, vadd_mem_vadd_set_iff.mpr hs, ?_⟩
        change f (v + s) = r
        rw [map_add, hfs]
        abel
      · rintro ⟨x, hx, hfx⟩
        have hx' : -v +ᵥ x ∈ S := by
          rw [mem_vadd_set_iff_neg_vadd_mem] at hx
          exact hx
        rw [mem_vadd_set_iff_neg_vadd_mem]
        refine ⟨-v +ᵥ x, hx', ?_⟩
        change f (-v + x) = -f v + r
        rw [map_add, map_neg, hfx]
    _ = f '' S := congrArg (fun U : Set Plane => f '' U) hv

private theorem orient_image_period {f : Plane →L[ℝ] ℝ} {S : Set Plane} {v : Plane}
    (hv : f v ∈ periodGroup (f '' S)) (hfv : f v ≠ 0) :
    ∃ w : Plane, ∃ r : ℝ, (w = v ∨ w = -v) ∧ 0 < r ∧ f w = r ∧
      r ∈ periodGroup (f '' S) := by
  by_cases hpos : 0 < f v
  · refine ⟨v, f v, Or.inl rfl, hpos, rfl, hv⟩
  · have hneg : f v < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hfv
    have hvneg : -f v ∈ periodGroup (f '' S) := by
      simpa [map_neg] using (periodGroup (f '' S)).neg_mem hv
    refine ⟨-v, -f v, Or.inr rfl, neg_pos.mpr hneg, ?_, hvneg⟩
    simp

private theorem period_compl {S : Set ℝ} {u : ℝ}
    (hu : u ∈ periodGroup S) : u ∈ periodGroup (Sᶜ) := by
  change u +ᵥ Sᶜ = Sᶜ
  change u +ᵥ S = S at hu
  ext x
  rw [mem_vadd_set_iff_neg_vadd_mem]
  simp only [mem_compl_iff]
  constructor
  · intro hx hSx
    have htranslated : -u +ᵥ x ∈ -u +ᵥ S := vadd_mem_vadd_set_iff.mpr hSx
    have hneg : -u +ᵥ S = S := (periodGroup S).neg_mem hu
    rw [hneg] at htranslated
    exact hx htranslated
  · intro hx htranslated
    have hback : u +ᵥ (-u +ᵥ x) ∈ u +ᵥ S := vadd_mem_vadd_set_iff.mpr htranslated
    rw [hu] at hback
    have hback' : x ∈ S := by simpa [vadd_eq_add, add_assoc, add_comm] using hback
    exact hx hback'

private theorem period_interior {S : Set ℝ} {u : ℝ}
    (hu : u ∈ periodGroup S) : u ∈ periodGroup (interior S) := by
  change u +ᵥ interior S = interior S
  rw [← interior_vadd, hu]

private theorem period_sdiff {X Y : Set Plane} {u : Plane}
    (hX : u ∈ periodGroup X) (hY : u ∈ periodGroup Y) :
    u ∈ periodGroup (X \ Y) := by
  change u +ᵥ (X \ Y) = X \ Y
  change u +ᵥ X = X at hX
  change u +ᵥ Y = Y at hY
  ext x
  rw [mem_vadd_set_iff_neg_vadd_mem]
  simp only [Set.mem_sdiff]
  have hiff (Z : Set Plane) (hZ : u +ᵥ Z = Z) :
      (-u + x ∈ Z ↔ x ∈ Z) := by
    constructor
    · intro hx
      have hx' : u +ᵥ (-u + x) ∈ u +ᵥ Z := vadd_mem_vadd_set_iff.mpr hx
      rw [hZ] at hx'
      simpa [vadd_eq_add, add_assoc] using hx'
    · intro hx
      have hneg : -u +ᵥ Z = Z := by
        have := (periodGroup Z).neg_mem (show u ∈ periodGroup Z from hZ)
        exact this
      have hx' : -u +ᵥ x ∈ -u +ᵥ Z := vadd_mem_vadd_set_iff.mpr hx
      rw [hneg] at hx'
      exact hx'
  exact and_congr (hiff X hX) (not_congr (hiff Y hY))

private theorem period_closure {S : Set Plane} {u : Plane}
    (hu : u ∈ periodGroup S) : u ∈ periodGroup (closure S) := by
  change u +ᵥ closure S = closure S
  rw [← closure_vadd, hu]

private theorem period_compl_closure_plane {S : Set Plane} {u : Plane}
    (hu : u ∈ periodGroup S) : u ∈ periodGroup ((closure S)ᶜ) := by
  change u +ᵥ (closure S)ᶜ = (closure S)ᶜ
  have hcl : u +ᵥ closure S = closure S := by rw [← closure_vadd, hu]
  have hneg : -u +ᵥ closure S = closure S := (periodGroup (closure S)).neg_mem (by
    change u +ᵥ closure S = closure S
    exact hcl)
  ext x
  rw [mem_vadd_set_iff_neg_vadd_mem]
  simp only [mem_compl_iff]
  constructor
  · intro hx hcx
    have htranslated : -u +ᵥ x ∈ -u +ᵥ closure S := vadd_mem_vadd_set_iff.mpr hcx
    rw [hneg] at htranslated
    exact hx htranslated
  · intro hx htranslated
    have hback : u +ᵥ (-u +ᵥ x) ∈ u +ᵥ closure S := vadd_mem_vadd_set_iff.mpr htranslated
    rw [hcl] at hback
    have hback' : x ∈ closure S := by
      simpa [vadd_eq_add, add_assoc, add_comm] using hback
    exact hx hback'

private theorem period_from_scalar_relation {B : Set Plane} {δ : Submodule ℝ Plane}
    {f : Plane →L[ℝ] ℝ} {b c γ : Plane} {β η : ℝ}
    (hker : LinearMap.ker f.toLinearMap = δ)
    (hBδ : IsInvariantAlong B δ) (hb : b ∈ periodGroup B)
    (hbcoord : f b = β) (hccoord : f c = η)
    (hcsign : c = γ ∨ c = -γ)
    (hcomm : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * β = (n : ℝ) * η) :
    ∃ ell : ℕ, 0 < ell ∧ (ell : ℤ) • γ ∈ periodGroup B := by
  obtain ⟨m, n, hm, hn, hmn⟩ := hcomm
  have hrel : (m : ℤ) • b - (n : ℤ) • c ∈ δ := by
    apply hker ▸ LinearMap.mem_ker.mpr
    change f ((m : ℤ) • b - (n : ℤ) • c) = 0
    rw [map_sub, map_zsmul, map_zsmul, hbcoord, hccoord]
    have hmn' : (m : ℝ) * β = (n : ℝ) * η := hmn
    simpa [zsmul_eq_mul] using sub_eq_zero.mpr hmn'
  have hmb : (m : ℤ) • b ∈ periodGroup B := (periodGroup B).zsmul_mem hb m
  have hrelB : (m : ℤ) • b - (n : ℤ) • c ∈ periodGroup B := hBδ _ hrel
  have hnC : (n : ℤ) • c ∈ periodGroup B := by
    have hh := (periodGroup B).sub_mem hmb hrelB
    convert hh using 1; abel
  have hnGamma : (n : ℤ) • γ ∈ periodGroup B := by
    rcases hcsign with hc | hc
    · simpa [hc] using hnC
    · have hneg := (periodGroup B).neg_mem hnC
      simpa [hc] using hneg
  exact ⟨n, hn, hnGamma⟩

private theorem transverse_core_relation {B XE XA : Set Plane} {δ : Submodule ℝ Plane}
    {f : Plane →L[ℝ] ℝ} {b c γ : Plane} {β η : ℝ}
    (hker : LinearMap.ker f.toLinearMap = δ) (hBδ : IsInvariantAlong B δ)
    (hXAδ : IsInvariantAlong XA δ)
    (hcomp : B = XE \ closure XA) (hbXE : b ∈ periodGroup XE)
    (hcXA : c ∈ periodGroup XA) (hcsign : c = γ ∨ c = -γ)
    (hbcoord : f b = β) (hccoord : f c = η)
    (hcomm : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * β = (n : ℝ) * η) :
    ∃ ell : ℕ, 0 < ell ∧ (ell : ℤ) • γ ∈ periodGroup B := by
  obtain ⟨m, n, hm, hn, hmn⟩ := hcomm
  have hrel : (m : ℤ) • b - (n : ℤ) • c ∈ δ := by
    apply hker ▸ LinearMap.mem_ker.mpr
    change f ((m : ℤ) • b - (n : ℤ) • c) = 0
    rw [map_sub, map_zsmul, map_zsmul, hbcoord, hccoord]
    simpa [zsmul_eq_mul] using sub_eq_zero.mpr hmn
  have hnC : (n : ℤ) • c ∈ periodGroup XA := (periodGroup XA).zsmul_mem hcXA n
  have hzXA : (m : ℤ) • b - (n : ℤ) • c ∈ periodGroup XA := by
    exact hXAδ _ hrel
  have hmXA : (m : ℤ) • b ∈ periodGroup XA := by
    have := (periodGroup XA).add_mem hzXA hnC
    convert this using 1; abel
  have hmXE : (m : ℤ) • b ∈ periodGroup XE := (periodGroup XE).zsmul_mem hbXE m
  have hmB : (m : ℤ) • b ∈ periodGroup B := by
    rw [hcomp]
    exact period_sdiff hmXE (period_closure hmXA)
  have hzB : (m : ℤ) • b - (n : ℤ) • c ∈ periodGroup B := hBδ _ hrel
  have hnC_B : (n : ℤ) • c ∈ periodGroup B := by
    have := (periodGroup B).sub_mem hmB hzB
    convert this using 1; abel
  have hnGamma : (n : ℤ) • γ ∈ periodGroup B := by
    rcases hcsign with hc | hc
    · simpa [hc] using hnC_B
    · have hneg := (periodGroup B).neg_mem hnC_B
      simpa [hc] using hneg
  exact ⟨n, hn, hnGamma⟩

/-- Nonempty branch used after lifting the noncolumn lattice and a shared longitudinal period. -/
theorem columnComplement_transversePeriodic
    {A B E : Set Plane} {δ : Submodule ℝ Plane} {γ p : Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (hAopen : IsOpen A) (hAreg : interior (closure A) = A)
    (hBopen : IsOpen B) (hBreg : interior (closure B) = B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hdisj : Disjoint A B)
    (hE : E = interior (closure (A ∪ B))) (hEper : IsLatticePeriodic E)
    (hBδ : IsInvariantAlong B δ) (hγ : γ ∉ δ)
    (hAγ : γ ∈ periodGroup A)
    (hpδ : p ∈ δ) (hp : p ≠ 0) (hAp : p ∈ periodGroup A) :
    ∃ ell : ℕ, 0 < ell ∧ (ell : ℤ) • γ ∈ periodGroup B := by
  classical
  obtain ⟨β, hβE, hβδ⟩ := exists_lattice_period_not_mem_line hδ hEper
  let f : Plane →L[ℝ] ℝ := Tiling.planarCrossCLM p
  have hspan : δ = Submodule.span ℝ ({p} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ hpδ hp
  have hker : LinearMap.ker f.toLinearMap = δ := by
    rw [show f = Tiling.planarCrossCLM p by rfl, planarCrossCLM_ker_eq_span hp, hspan]
  have hβimage : f β ≠ 0 := by
    intro hβzero
    have hβker : β ∈ LinearMap.ker f.toLinearMap := LinearMap.mem_ker.mpr hβzero
    exact hβδ (hker ▸ hβker)
  have hγimage : f γ ≠ 0 := by
    intro hγzero
    have hγker : γ ∈ LinearMap.ker f.toLinearMap := LinearMap.mem_ker.mpr hγzero
    exact hγ (hker ▸ hγker)
  have hβimagePeriod : f β ∈ periodGroup (f '' (completeFibreCore E δ)) := by
    exact period_mem_image_period (completeFibreCore_periods δ hβE)
  have hγimagePeriod : f γ ∈ periodGroup (f '' (completeFibreCore A δ)) := by
    exact period_mem_image_period (completeFibreCore_periods δ hAγ)
  have hpA : p +ᵥ A = A := hAp
  have hpB : p +ᵥ B = B := hBδ p hpδ
  have hpUnion : p +ᵥ (A ∪ B) = A ∪ B := by
    calc
      p +ᵥ (A ∪ B) = (p +ᵥ A) ∪ (p +ᵥ B) := by
        rw [← image_vadd, image_union, image_vadd, image_vadd]
      _ = A ∪ B := by rw [hpA, hpB]
  have hpE : p ∈ periodGroup E := by
    change p +ᵥ E = E
    calc
      p +ᵥ E = p +ᵥ interior (closure (A ∪ B)) := by rw [hE]
      _ = interior (p +ᵥ closure (A ∪ B)) := by rw [← interior_vadd]
      _ = interior (closure (p +ᵥ (A ∪ B))) := by rw [← closure_vadd]
      _ = interior (closure (A ∪ B)) := by rw [hpUnion]
      _ = E := hE.symm
  have hEopen : IsOpen E := hE ▸ isOpen_interior
  have hXEopen : IsOpen (completeFibreCore E δ) :=
    completeFibreCore_isOpen_of_longitudinalPeriod hEopen hδ hpδ hp hpE
  have hXAopen : IsOpen (completeFibreCore A δ) :=
    completeFibreCore_isOpen_of_longitudinalPeriod hAopen hδ hpδ hp hAp
  have hfsurj : Function.Surjective f.toLinearMap := by
    intro r
    refine ⟨(r / f γ) • γ, ?_⟩
    change f ((r / f γ) • γ) = r
    rw [map_smul]
    exact div_mul_cancel₀ r hγimage
  have hfopen : IsOpenMap f.toLinearMap := LinearMap.isOpenMap_of_finiteDimensional _ hfsurj
  have hXEimageOpen : IsOpen (f '' completeFibreCore E δ) := hfopen _ hXEopen
  have hXAimageOpen : IsOpen (f '' completeFibreCore A δ) := hfopen _ hXAopen
  have hAtoE : A ⊆ E := by
    intro x hx
    have hx' : x ∈ E \ closure B :=
      (regularOpen_union_complement hAopen hAreg hBopen hdisj hBreg hE).1 ▸ hx
    exact hx'.1
  have hXAtoXE : completeFibreCore A δ ⊆ completeFibreCore E δ := by
    intro x hx
    change x +ᵥ (δ : Set Plane) ⊆ E
    exact Set.Subset.trans hx hAtoE
  have hXAimageSub : f '' completeFibreCore A δ ⊆ f '' completeFibreCore E δ :=
    Set.image_mono hXAtoXE
  have hXA : completeFibreCore A δ ⊆ A := by
    intro x hx
    have hz : x ∈ x +ᵥ (δ : Set Plane) := by
      have hzero : x +ᵥ (0 : Plane) ∈ x +ᵥ (δ : Set Plane) :=
        vadd_mem_vadd_set_iff.mpr δ.zero_mem
      simpa using hzero
    exact hx hz
  have hBXA : Disjoint B (completeFibreCore A δ) := (hdisj.mono_left hXA).symm
  have hcoreComp : B = completeFibreCore E δ \ closure (completeFibreCore A δ) :=
    columnComplement_completeFibreCore hAopen hAreg hBopen hBreg hdisj hE hBδ hXEopen
  have hBimageOpen : IsOpen (f '' B) := hfopen _ hBopen
  have hAimageOpen : IsOpen (f '' A) := hfopen _ hAopen
  have hBimageNe : (f '' B).Nonempty := hBne.image f
  have hAimageNe : (f '' A).Nonempty := hAne.image f
  have hgammaAImage : f γ ∈ periodGroup (f '' A) := period_mem_image_period hAγ
  have himageXA_B : Disjoint (f '' completeFibreCore A δ) (f '' B) := by
    rw [Set.disjoint_left]
    rintro r ⟨a, ha, har⟩ ⟨b, hb, hbr⟩
    have hfa : f a = f b := har.trans hbr.symm
    have hzero : f (a - b) = 0 := by rw [map_sub, hfa]; abel
    have hdiff : a - b ∈ δ := hker ▸ (LinearMap.mem_ker.mpr hzero)
    have hshift : (a - b) +ᵥ B = B := hBδ (a - b) hdiff
    have hab : a ∈ B := by
      have : (a - b) +ᵥ b ∈ (a - b) +ᵥ B := vadd_mem_vadd_set_iff.mpr hb
      rw [hshift] at this
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact hBXA.le_bot ⟨hab, ha⟩
  have himageA_B : Disjoint (f '' A) (f '' B) := by
    rw [Set.disjoint_left]
    rintro r ⟨a, ha, har⟩ ⟨b, hb, hbr⟩
    have hfa : f a = f b := har.trans hbr.symm
    have hzero : f (a - b) = 0 := by rw [map_sub, hfa]; abel
    have hdiff : a - b ∈ δ := hker ▸ (LinearMap.mem_ker.mpr hzero)
    have hshift : (a - b) +ᵥ B = B := hBδ (a - b) hdiff
    have hab : a ∈ B := by
      have : (a - b) +ᵥ b ∈ (a - b) +ᵥ B := vadd_mem_vadd_set_iff.mpr hb
      rw [hshift] at this
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact hdisj.le_bot ⟨ha, hab⟩
  obtain ⟨b, βpos, hbSign, hβpos, hbcoord, hβimagePos⟩ :=
    orient_image_period hβimagePeriod hβimage
  obtain ⟨c, ηcore, hcSign, hηcore, hccoord, hηcoreImage⟩ :=
    orient_image_period hγimagePeriod hγimage
  have hbXE : b ∈ periodGroup (completeFibreCore E δ) := by
    rcases hbSign with hb | hb
    · simpa [hb] using completeFibreCore_periods δ hβE
    · have hn := (periodGroup (completeFibreCore E δ)).neg_mem
        (completeFibreCore_periods δ hβE)
      simpa [hb] using hn
  by_cases hXAne : (completeFibreCore A δ).Nonempty
  · by_cases hXEuniv : f '' completeFibreCore E δ = Set.univ
    · have hXEall : completeFibreCore E δ = Set.univ := by
        apply Set.eq_univ_iff_forall.mpr
        intro x
        have hfx : f x ∈ f '' completeFibreCore E δ := by
          rw [hXEuniv]
          simp
        obtain ⟨y, hy, hfy⟩ := hfx
        have hdiff : x - y ∈ δ := by
          apply hker ▸ LinearMap.mem_ker.mpr
          change f (x - y) = 0
          rw [map_sub, hfy]
          abel
        have hinv := completeFibreCore_invariant E δ (x - y) hdiff
        have hx' : (x - y) +ᵥ y ∈ (x - y) +ᵥ completeFibreCore E δ :=
          vadd_mem_vadd_set_iff.mpr hy
        rw [hinv] at hx'
        simpa [vadd_eq_add, sub_eq_add_neg, add_assoc, add_comm] using hx'
      have hcXA : c ∈ periodGroup (completeFibreCore A δ) := by
        rcases hcSign with hc | hc
        · simpa [hc] using completeFibreCore_periods δ hAγ
        · have hn := (periodGroup (completeFibreCore A δ)).neg_mem
            (completeFibreCore_periods δ hAγ)
          simpa [hc] using hn
      have hcComp : c ∈ periodGroup ((closure (completeFibreCore A δ))ᶜ) :=
        period_compl_closure_plane hcXA
      have hcB : c ∈ periodGroup B := by
        have hcompB : B = (closure (completeFibreCore A δ))ᶜ := by
          calc
            B = completeFibreCore E δ \ closure (completeFibreCore A δ) := hcoreComp
            _ = (closure (completeFibreCore A δ))ᶜ := by
              rw [hXEall]
              ext x
              simp
        rw [hcompB]
        exact hcComp
      rcases hcSign with hc | hc
      · exact ⟨1, by norm_num, by simpa [hc] using hcB⟩
      · have hn := (periodGroup B).neg_mem hcB
        exact ⟨1, by norm_num, by simpa [hc] using hn⟩
    · have hproper : f '' completeFibreCore E δ ≠ Set.univ := hXEuniv
      have hXAimageNe : (f '' completeFibreCore A δ).Nonempty := hXAne.image f
      obtain ⟨m, n, hm, hn, hmn⟩ := periodicOpen_inclusion_commensurable
        (f '' completeFibreCore A δ) (f '' completeFibreCore E δ) βpos ηcore
        hXAimageOpen hXAimageNe hXEimageOpen hproper hXAimageSub
        hβpos hηcore hβimagePos hηcoreImage
      exact transverse_core_relation hker hBδ
        (completeFibreCore_invariant A δ) hcoreComp hbXE
        (by
          rcases hcSign with hc | hc
          · simpa [hc] using completeFibreCore_periods δ hAγ
          · have hn := (periodGroup (completeFibreCore A δ)).neg_mem
              (completeFibreCore_periods δ hAγ)
            simpa [hc] using hn)
        hcSign hbcoord hccoord ⟨m, n, hm, hn, hmn⟩
  · have hXAempty : completeFibreCore A δ = ∅ := Set.not_nonempty_iff_eq_empty.mp hXAne
    have hBE : B = completeFibreCore E δ := by
      rw [hcoreComp, hXAempty, closure_empty, sdiff_empty]
    have hBimagePeriod : βpos ∈ periodGroup (f '' B) := by
      rw [hBE]
      exact hβimagePos
    have hgammaAImage : f γ ∈ periodGroup (f '' A) := period_mem_image_period hAγ
    obtain ⟨d, ηraw, hdSign, hηraw, hdcoord, hηrawImage⟩ :=
      orient_image_period hgammaAImage hγimage
    let C : Set ℝ := interior ((f '' B)ᶜ)
    have hsep : Disjoint (f '' A) (closure (f '' B)) :=
      himageA_B.closure_right hAimageOpen
    have hAintoC : f '' A ⊆ C := by
      intro r hr
      change r ∈ interior ((f '' B)ᶜ)
      rw [mem_interior_iff_mem_nhds]
      apply Filter.mem_of_superset (hAimageOpen.mem_nhds hr)
      intro s hs
      have hsnot : s ∉ closure (f '' B) := by
        intro hscl
        exact hsep.le_bot ⟨hs, hscl⟩
      exact fun hsB => hsnot (subset_closure hsB)
    have hCopen : IsOpen C := isOpen_interior
    have hCproper : C ≠ Set.univ := by
      intro hfull
      obtain ⟨r, hr⟩ := hBimageNe
      have hrC : r ∈ C := by rw [hfull]; trivial
      have hrcomp : r ∈ (f '' B)ᶜ := interior_subset hrC
      have hrnot : r ∉ f '' B := by simpa [mem_compl_iff] using hrcomp
      exact hrnot hr
    have hβC : βpos ∈ periodGroup C := by
      dsimp [C]
      exact period_interior (period_compl hBimagePeriod)
    obtain ⟨m, n, hm, hn, hmn⟩ := periodicOpen_inclusion_commensurable
      (f '' A) C βpos ηraw hAimageOpen hAimageNe hCopen hCproper hAintoC
      hβpos hηraw hβC hηrawImage
    have hbB : b ∈ periodGroup B := by rw [hBE]; exact hbXE
    exact period_from_scalar_relation hker hBδ hbB hbcoord hdcoord hdSign
      ⟨m, n, hm, hn, hmn⟩

private theorem openUnion_subset_regularSupport (K : PolygonalRegion) (S : Set Plane) :
    openUnion K S ⊆ regularSupport K S := by
  have hopen : IsOpen (openUnion K S) := by
    apply isOpen_iUnion
    intro s
    exact (Homeomorph.addLeft (s : Plane)).isOpenMap _ isOpen_interior
  exact hopen.subset_interior_iff.mpr subset_closure

private theorem translated_tile_mem_regularSupport {K : PolygonalRegion} {S : Set Plane}
    {s u : Plane} (hs : s ∈ S) (hu : u ∈ K.openCarrier) :
    s + u ∈ regularSupport K S := by
  apply openUnion_subset_regularSupport K S
  exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨u, hu, rfl⟩⟩

private theorem invariant_eq_preimage_image {δ : Submodule ℝ Plane} {X : Set Plane}
    {π : Plane →L[ℝ] ℝ} (hker : LinearMap.ker π.toLinearMap = δ)
    (hX : IsInvariantAlong X δ) : X = π ⁻¹' (π '' X) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨x, hx, rfl⟩
  · rintro x ⟨y, hy, hxy⟩
    have hdiff : x - y ∈ δ := by
      rw [← hker, LinearMap.mem_ker]
      change π (x - y) = 0
      rw [map_sub, hxy]
      abel
    have hinv := hX (x - y) hdiff
    have h := hinv ▸ (show (x - y) +ᵥ y ∈ (x - y) +ᵥ X from ⟨y, hy, rfl⟩)
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

private theorem column_carrier_eq_preimage_projection
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {C : Set Plane}
    {π : Plane →L[ℝ] ℝ} {c : Plane}
    (hker : LinearMap.ker π.toLinearMap = δ) (hπopen : IsOpenMap π)
    (hcol : IsCenterColumn K δ C) (hc : c ∈ C) :
    regularSupport K C = π ⁻¹' (π c +ᵥ interior (π '' K.support)) := by
  have hclosure : closure (regularSupport K C) = closure (openUnion K C) := by
    apply Set.Subset.antisymm
    · exact (closure_mono interior_subset).trans_eq closure_closure
    · exact closure_mono (openUnion_subset_regularSupport K C)
  have hclosedInv : IsInvariantAlong (closure (openUnion K C)) δ := by
    intro v hv
    rw [← hclosure, ← closure_vadd, hcol.2.2.2 v hv]
  have hclosedSat := invariant_eq_preimage_image hker hclosedInv
  have himage : π '' closure (openUnion K C) = π c +ᵥ (π '' K.support) := by
    rw [closure_openUnion_eq_iUnion_support hcol.1]
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      obtain ⟨k, hk, rfl⟩ := hs
      obtain ⟨a, ha⟩ := hcol.2.2.1
      have hsc : (s : Plane) - c ∈ δ := by
        have h := δ.sub_mem (ha s s.property) (ha c hc)
        convert h using 1; abel
      have hπsc : π s = π c := by
        rw [← hker, LinearMap.mem_ker, map_sub, sub_eq_zero] at hsc
        exact hsc
      refine ⟨π k, ⟨k, hk, rfl⟩, ?_⟩
      change π c + π k = π ((s : Plane) + k)
      rw [map_add, hπsc]
    · rintro ⟨r, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨c + k, Set.mem_iUnion.mpr ⟨⟨c, hc⟩, ⟨k, hk, rfl⟩⟩, ?_⟩
      exact map_add π c k
  change interior (closure (openUnion K C)) = _
  rw [hclosedSat, himage, ← hπopen.preimage_interior_eq_interior_preimage π.continuous,
    interior_vadd]

private theorem lineFibre_projected_coord {δ : Submodule ℝ Plane} {T : Set Plane}
    {π : Plane →L[ℝ] ℝ} (hker : LinearMap.ker π.toLinearMap = δ)
    {t s : Plane} (hs : s ∈ lineFibre δ T t) : π s = π t := by
  have h := hs.2
  rw [← hker, LinearMap.mem_ker] at h
  change π (s - t) = 0 at h
  simpa only [map_sub, sub_eq_zero] using h

private theorem unionColumns_scalarOpenPacking
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    {π : Plane →L[ℝ] ℝ} (hker : LinearMap.ker π.toLinearMap = δ)
    (hπopen : IsOpenMap π) (hπsurj : Surjective π)
    (hpack : IsPacking K.prototileFamily (K.placements T))
    (hcol : IsUnionOfColumns K δ T) :
    Tiling.AxisParallel.OneDimensional.LineTilesOn
      (interior (π '' K.support)) (π '' T)
      (Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion
        (interior (π '' K.support)) (π '' T)) := by
  let J := interior (π '' K.support)
  let H := π '' T
  have hUopen : IsOpen
      (Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion J H) := by
    apply isOpen_iUnion
    intro h
    exact isOpen_interior.vadd (h : ℝ)
  refine ⟨isOpen_interior.measurableSet, hUopen.measurableSet,
    (packing_centres_locallyFinite hpack).2.1.image π, ?_, ?_⟩
  · intro l hl l' hl' hne
    obtain ⟨c, hc, hcl⟩ := hl
    obtain ⟨c', hc', hc'l'⟩ := hl'
    have hfibres : Disjoint (lineFibre δ T c) (lineFibre δ T c') := by
      rw [Set.disjoint_left]
      intro s hs hs'
      exact hne (hcl.symm.trans ((lineFibre_projected_coord hker hs).symm.trans
        ((lineFibre_projected_coord hker hs').trans hc'l')))
    have hdisj := regularSupport_disjoint_of_disjoint_subfamilies hpack
      (fun _ hs => hs.1) (fun _ hs => hs.1) hfibres
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro r hr hr'
    obtain ⟨x, hxr⟩ := hπsurj r
    apply Set.disjoint_left.mp hdisj
    · rw [column_carrier_eq_preimage_projection hker hπopen (hcol c hc)
        (show c ∈ lineFibre δ T c from ⟨hc, by simp⟩)]
      change π x ∈ π c +ᵥ J
      simpa only [hxr, hcl] using hr
    · rw [column_carrier_eq_preimage_projection hker hπopen (hcol c' hc')
        (show c' ∈ lineFibre δ T c' from ⟨hc', by simp⟩)]
      change π x ∈ π c' +ᵥ J
      simpa only [hxr, hc'l'] using hr'
  · exact Filter.Eventually.of_forall (fun _ => Set.mem_iUnion)

private theorem unionColumns_carrier_eq_preimage_regularizedTarget
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    {π : Plane →L[ℝ] ℝ} (hker : LinearMap.ker π.toLinearMap = δ)
    (hπopen : IsOpenMap π) (hcol : IsUnionOfColumns K δ T) :
    regularSupport K T = π ⁻¹'
      Tiling.AxisParallel.OneDimensional.FiniteInterval.regularizedTarget
        (interior (π '' K.support)) (π '' T) := by
  let J := interior (π '' K.support)
  let H := π '' T
  have hT : (⋃ t : T, lineFibre δ T t) = T := by
    ext s
    constructor
    · intro hs
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hs
      exact ht.1
    · intro hs
      exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨hs, by simp⟩⟩
  have hU : (⋃ t : T, regularSupport K (lineFibre δ T t)) = π ⁻¹'
      Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion J H := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
      rw [column_carrier_eq_preimage_projection hker hπopen (hcol t t.property)
        (show (t : Plane) ∈ lineFibre δ T t from ⟨t.property, by simp⟩)] at ht
      exact Set.mem_iUnion.mpr ⟨⟨π t, ⟨t, t.property, rfl⟩⟩, ht⟩
    · intro hx
      obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, ht, hth⟩ := h.property
      apply Set.mem_iUnion.mpr
      refine ⟨⟨t, ht⟩, ?_⟩
      rw [column_carrier_eq_preimage_projection hker hπopen (hcol t ht)
        (show t ∈ lineFibre δ T t from ⟨ht, by simp⟩)]
      change π x ∈ π t +ᵥ J
      simpa only [hth] using hh
  calc
    regularSupport K T = regularSupport K (⋃ t : T, lineFibre δ T t) := by rw [hT]
    _ = interior (closure (⋃ t : T, regularSupport K (lineFibre δ T t))) :=
      regularSupport_iUnion K _
    _ = interior (closure (π ⁻¹'
        Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion J H)) := by rw [hU]
    _ = π ⁻¹' Tiling.AxisParallel.OneDimensional.FiniteInterval.regularizedTarget J H := by
      rw [← hπopen.preimage_closure_eq_closure_preimage π.continuous,
        ← hπopen.preimage_interior_eq_interior_preimage π.continuous]
      rfl

private theorem unionColumns_transport_of_projected_period
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    {π : Plane →L[ℝ] ℝ} {γ : Plane}
    (hker : LinearMap.ker π.toLinearMap = δ) (hπopen : IsOpenMap π)
    (hcol : IsUnionOfColumns K δ T) (hγ : π γ ∈ periodGroup (π '' T)) :
    ∀ t ∈ T, ∀ m : ℤ, ∃ s ∈ T, s - t - m • γ ∈ δ ∧
      regularSupport K (lineFibre δ T s) =
        m • γ +ᵥ regularSupport K (lineFibre δ T t) := by
  intro t ht m
  have hm : m • π γ +ᵥ (π '' T) = π '' T := (periodGroup (π '' T)).zsmul_mem hγ m
  have hπt : π t ∈ π '' T := ⟨t, ht, rfl⟩
  have hπs : m • π γ + π t ∈ π '' T := hm ▸ ⟨π t, hπt, rfl⟩
  obtain ⟨s, hs, hscoord⟩ := hπs
  refine ⟨s, hs, ?_, ?_⟩
  · rw [← hker, LinearMap.mem_ker]
    change π (s - t - m • γ) = 0
    rw [map_sub, map_sub, map_zsmul, hscoord]
    abel
  · rw [column_carrier_eq_preimage_projection hker hπopen (hcol s hs)
        (show s ∈ lineFibre δ T s from ⟨hs, by simp⟩),
      column_carrier_eq_preimage_projection hker hπopen (hcol t ht)
        (show t ∈ lineFibre δ T t from ⟨ht, by simp⟩)]
    ext x
    rw [mem_vadd_set_iff_neg_vadd_mem]
    change π x ∈ π s +ᵥ interior (π '' K.support) ↔
      π (-(m • γ) + x) ∈ π t +ᵥ interior (π '' K.support)
    rw [mem_vadd_set_iff_neg_vadd_mem, mem_vadd_set_iff_neg_vadd_mem,
      map_add, map_neg, map_zsmul, hscoord]
    simp only [vadd_eq_add]
    rw [show -(m • π γ + π t) + π x = -π t + (-(m • π γ) + π x) by abel]

private theorem unionColumns_prescribed_transverse_multiple_aux
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane} {γ : Plane}
    (hTne : T.Nonempty) (hpack : IsPacking K.prototileFamily (K.placements T))
    (hcol : IsUnionOfColumns K δ T) (hproper : regularSupport K T ≠ Set.univ)
    (hγδ : γ ∉ δ) (hγperiod : γ ∈ periodGroup (regularSupport K T))
    {π : Plane →L[ℝ] ℝ} (hker : LinearMap.ker π.toLinearMap = δ)
    (hπopen : IsOpenMap π) (hπsurj : Surjective π)
    (hJfinite : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
      (interior (π '' K.support))) :
    ∃ n : ℕ, 0 < n ∧ ∀ t ∈ T, ∀ m : ℤ, ∃ s ∈ T,
      s - t - m • ((n : ℤ) • γ) ∈ δ ∧
        regularSupport K (lineFibre δ T s) =
          m • ((n : ℤ) • γ) +ᵥ regularSupport K (lineFibre δ T t) := by
  let J := interior (π '' K.support)
  let H := π '' T
  let R := Tiling.AxisParallel.OneDimensional.FiniteInterval.regularizedTarget J H
  have hOopen : IsOpen (π '' K.openCarrier) := hπopen _ isOpen_interior
  have hOsub : π '' K.openCarrier ⊆ J :=
    hOopen.subset_interior_iff.mpr (Set.image_mono interior_subset)
  have hJne : J.Nonempty :=
    ((K.isPolygonal.interior_nonempty K.nonempty).image π).mono hOsub
  have hmass : 0 < (volume J).toReal := ENNReal.toReal_pos
    (isOpen_interior.measure_pos volume hJne).ne'
    (Tiling.AxisParallel.OneDimensional.FiniteInterval.IsFiniteIntervalRegion.measure_ne_top hJfinite)
  let P := Tiling.AxisParallel.OneDimensional.FiniteInterval.IntervalPresentation.ofIsFiniteIntervalRegion
    hJfinite
  obtain ⟨hRopen, hRreg, _, _, htileR, hfront⟩ :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.LineTilesOn.regularizedTarget P
      (unionColumns_scalarOpenPacking hker hπopen hπsurj hpack hcol) hmass
  change Tiling.AxisParallel.OneDimensional.LineTilesOn J H R at htileR
  have hcarrier : regularSupport K T = π ⁻¹' R :=
    unionColumns_carrier_eq_preimage_regularizedTarget hker hπopen hcol
  have himage : π '' regularSupport K T = R := by
    rw [hcarrier]
    exact Set.image_preimage_eq R hπsurj
  have hRproper : R ≠ Set.univ := by
    intro hfull
    apply hproper
    rw [hcarrier, hfull, preimage_univ]
  have hRne : R.Nonempty := by
    obtain ⟨t, ht⟩ := hTne
    obtain ⟨j, hj⟩ := hJne
    exact ⟨π t + j,
      Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion_subset_regularizedTarget P
        (Set.mem_iUnion.mpr ⟨⟨π t, ⟨t, ht, rfl⟩⟩, ⟨j, hj, rfl⟩⟩)⟩
  have hγzero : π γ ≠ 0 := by
    intro hz
    exact hγδ (hker ▸ LinearMap.mem_ker.mpr hz)
  have hγR : π γ ∈ periodGroup R := by
    rw [← himage]
    exact period_mem_image_period hγperiod
  obtain ⟨n, hn, hperiodH⟩ : ∃ n : ℕ, 0 < n ∧ (n : ℤ) • π γ ∈ periodGroup H := by
    by_cases hp : 0 < π γ
    · obtain ⟨n, hn, hpH⟩ :=
        Tiling.AxisParallel.OneDimensional.FiniteInterval.exists_nsmul_targetPeriod_vadd_centres_eq
          P htileR hmass hRne hRopen hRreg hRproper hp hγR hfront
      refine ⟨n, hn, ?_⟩
      change (n : ℤ) • π γ +ᵥ H = H
      simpa [zsmul_eq_mul] using hpH
    · have hpneg : 0 < -π γ := neg_pos.mpr
        (lt_of_le_of_ne (le_of_not_gt hp) hγzero)
      obtain ⟨n, hn, hpH⟩ :=
        Tiling.AxisParallel.OneDimensional.FiniteInterval.exists_nsmul_targetPeriod_vadd_centres_eq
          P htileR hmass hRne hRopen hRreg hRproper hpneg
          ((periodGroup R).neg_mem hγR) hfront
      have hneg := (periodGroup H).neg_mem
        (show (n : ℝ) * -π γ ∈ periodGroup H from hpH)
      exact ⟨n, hn, by simpa [zsmul_eq_mul] using hneg⟩
  refine ⟨n, hn, unionColumns_transport_of_projected_period hker hπopen hcol ?_⟩
  simpa only [map_zsmul] using hperiodH

private theorem unionColumns_transverse_period
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T E : Set Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (hEper : IsLatticePeriodic E) (hcol : IsUnionOfColumns K δ T)
    {π : Plane →L[ℝ] ℝ} (hker : LinearMap.ker π.toLinearMap = δ)
    (hπopen : IsOpenMap π) (hπsurj : Surjective π)
    (hJfinite : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
      (interior (π '' K.support))) :
    ∃ γ : Plane, γ ∉ δ ∧ π γ ∈ periodGroup (π '' T) := by
  let J := interior (π '' K.support)
  let H := π '' T
  let R := Tiling.AxisParallel.OneDimensional.FiniteInterval.regularizedTarget J H
  have hOopen : IsOpen (π '' K.openCarrier) := hπopen _ isOpen_interior
  have hOsub : π '' K.openCarrier ⊆ J := by
    apply hOopen.subset_interior_iff.mpr
    exact Set.image_mono interior_subset
  have hJne : J.Nonempty :=
    ((K.isPolygonal.interior_nonempty K.nonempty).image π).mono hOsub
  have hJmass : 0 < (volume J).toReal := ENNReal.toReal_pos
    (isOpen_interior.measure_pos volume hJne).ne'
    (Tiling.AxisParallel.OneDimensional.FiniteInterval.IsFiniteIntervalRegion.measure_ne_top
      hJfinite)
  let P := Tiling.AxisParallel.OneDimensional.FiniteInterval.IntervalPresentation.ofIsFiniteIntervalRegion
    hJfinite
  have hTileU := unionColumns_scalarOpenPacking hker hπopen hπsurj htile.2.1 hcol
  obtain ⟨hRopen, hRregular, _, _, hTileR, hfront⟩ :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.LineTilesOn.regularizedTarget
      P hTileU hJmass
  change Tiling.AxisParallel.OneDimensional.LineTilesOn J H R at hTileR
  have hEpre : E = π ⁻¹' R := by
    rw [← regularSupport_eq_of_tilesOn hEopen hEregular htile]
    exact unionColumns_carrier_eq_preimage_regularizedTarget hker hπopen hcol
  have hEimage : π '' E = R := by
    rw [hEpre]
    exact Set.image_preimage_eq R hπsurj
  obtain ⟨p, hp, hpH⟩ : ∃ p : ℝ, 0 < p ∧ p ∈ periodGroup H := by
    by_cases hHne : H.Nonempty
    · by_cases hRfull : R = Set.univ
      · obtain ⟨p, hp, _, hpH⟩ :=
          Tiling.AxisParallel.OneDimensional.FiniteInterval.exists_commonLinePeriod hJfinite hJmass
        refine ⟨p, hp, hpH H ?_⟩
        change Tiling.AxisParallel.OneDimensional.LineTilesOn J H Set.univ
        simpa only [hRfull] using hTileR
      · have hRne : R.Nonempty := by
          obtain ⟨h, hh⟩ := hHne
          obtain ⟨j, hj⟩ := hJne
          refine ⟨h + j, ?_⟩
          exact Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion_subset_regularizedTarget
            P (Set.mem_iUnion.mpr ⟨⟨h, hh⟩, ⟨j, hj, rfl⟩⟩)
        obtain ⟨β, hβE, hβδ⟩ := exists_lattice_period_not_mem_line hδ hEper
        have hβzero : π β ≠ 0 := by
          intro hz
          exact hβδ (hker ▸ LinearMap.mem_ker.mpr hz)
        obtain ⟨b, p, _, hp, _, hpR⟩ :=
          orient_image_period (period_mem_image_period hβE) hβzero
        rw [hEimage] at hpR
        obtain ⟨n, hn, hnH⟩ :=
          Tiling.AxisParallel.OneDimensional.FiniteInterval.exists_nsmul_targetPeriod_vadd_centres_eq
            P hTileR hJmass hRne hRopen hRregular hRfull hp hpR hfront
        exact ⟨(n : ℝ) * p, mul_pos (Nat.cast_pos.mpr hn) hp, hnH⟩
    · refine ⟨1, zero_lt_one, ?_⟩
      have hHempty : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hHne
      change (1 : ℝ) +ᵥ H = H
      simp [hHempty]
  obtain ⟨γ, hγ⟩ := hπsurj p
  refine ⟨γ, ?_, ?_⟩
  · intro hγδ
    have hz : π γ = 0 := LinearMap.mem_ker.mp (hker.symm ▸ hγδ)
    exact hp.ne' (hγ.symm.trans hz)
  · simpa only [hγ] using hpH

private theorem polygonal_generic_line_finiteFrontier
    (K : PolygonalRegion) (u : Plane) (hu : u ≠ 0)
    (π : Plane →L[ℝ] ℝ) (hπopen : IsOpenMap π) (hπu : π u = 0) :
    ∃ k ∈ K.openCarrier,
      {r : ℝ | k + r • u ∈ frontier K.support}.Finite := by
  classical
  obtain ⟨k₀, hk₀⟩ := K.isPolygonal.interior_nonempty K.nonempty
  let U : Set ℝ := π '' K.openCarrier
  have hUopen : IsOpen U := hπopen _ isOpen_interior
  have hUmem : π k₀ ∈ U := ⟨k₀, hk₀, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hUmem)
  let P : Set ℝ := π '' vertexSet K.support
  have hPfinite : P.Finite := K.isPolygonal.vertexSet_finite.image π
  have hIooInf : (Set.Ioo (π k₀ - ε) (π k₀ + ε)).Infinite := by
    apply Set.Ioo_infinite
    linarith
  obtain ⟨r, hrIoo, hravoid⟩ := hIooInf.exists_notMem_finite hPfinite
  have hrball : r ∈ Metric.ball (π k₀) ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hrIoo.1, hrIoo.2]
  have hrU : r ∈ U := hball hrball
  obtain ⟨k, hk, hπk⟩ := hrU
  have hcritical : π k ∉ π '' vertexSet K.support := by
    rw [hπk]
    exact hravoid
  exact ⟨k, hk, K.isPolygonal.noncriticalSection_frontier_finite π k u hu hπu hcritical⟩

private theorem polygonal_lineSection_finiteClosedIntervals (K : PolygonalRegion)
    (k u : Plane) (hu : u ≠ 0) :
    ∃ (n : ℕ) (a b : Fin n → ℝ), (∀ i, a i ≤ b i) ∧
      {r : ℝ | k + r • u ∈ K.support} = ⋃ i, Set.Icc (a i) (b i) := by
  exact K.isPolygonal.lineSection_finiteClosedIntervals k u hu

private theorem polygonal_projection_finiteClosedIntervals (K : PolygonalRegion)
    (π : Plane →L[ℝ] ℝ) :
    ∃ (n : ℕ) (a b : Fin n → ℝ), (∀ i, a i ≤ b i) ∧
      closure (π '' K.openCarrier) = ⋃ i, Set.Icc (a i) (b i) := by
  classical
  obtain ⟨F⟩ := K.isPolygonal
  let J := {t : Set Plane // t ∈ F.pieces}
  have hpresentation (j : J) : ∃ a b : ℝ, a ≤ b ∧ π '' j.1 = Set.Icc a b := by
    have htriangle := F.isTriangle j.1 j.2
    have hcompact := htriangle.isCompact.image π.continuous
    have hconvex : Convex ℝ j.1 := by
      obtain ⟨a, b, c, _, heq⟩ := htriangle
      rw [heq]
      exact convex_convexHull ℝ _
    have hne : (π '' j.1).Nonempty :=
      (htriangle.interior_nonempty.mono interior_subset).image π
    have hconnected : IsConnected (π '' j.1) :=
      ⟨hne, (hconvex.linear_image π.toLinearMap).isPreconnected⟩
    refine ⟨sInf (π '' j.1), sSup (π '' j.1),
      (hcompact.isLeast_sInf hne).2 (hcompact.sSup_mem hne),
      eq_Icc_of_connected_compact hconnected hcompact⟩
  choose a b hab heq using hpresentation
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hclosedImage : closure (π '' K.openCarrier) = π '' K.support := by
    apply Set.Subset.antisymm
    · apply closure_minimal (Set.image_mono interior_subset)
      exact (K.isPolygonal.isCompact.image π.continuous).isClosed
    · rw [← K.isPolygonal.closure_interior]
      exact image_closure_subset_closure_image π.continuous
  refine ⟨Fintype.card J, a ∘ e, b ∘ e, fun i => hab (e i), ?_⟩
  rw [hclosedImage]
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← F.sUnion_eq] at hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp hx
    let j : J := ⟨t, ht⟩
    apply Set.mem_iUnion.mpr
    refine ⟨e.symm j, ?_⟩
    change π x ∈ Set.Icc (a (e (e.symm j))) (b (e (e.symm j)))
    rw [e.apply_symm_apply, ← heq j]
    exact ⟨x, hxt, rfl⟩
  · intro hr
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hr
    have hri : r ∈ π '' (e i).1 := by rw [heq (e i)]; exact hi
    obtain ⟨x, hx, rfl⟩ := hri
    refine ⟨x, ?_, rfl⟩
    rw [← F.sUnion_eq]
    exact Set.mem_sUnion.mpr ⟨(e i).1, (e i).2, hx⟩

private theorem column_scalarLineTiles
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {u k c : Plane}
    (hu : u ≠ 0) (huδ : u ∈ δ)
    (hspan : δ = Submodule.span ℝ ({u} : Set Plane))
    (hk : k ∈ K.openCarrier)
    (hfront : {r : ℝ | k + r • u ∈ frontier K.support}.Finite)
    {C : Set Plane} (hcol : IsCenterColumn K δ C) (hc : c ∈ C) :
    Tiling.AxisParallel.OneDimensional.LineTiles
      (interior {r : ℝ | k + r • u ∈ K.support})
      {r : ℝ | c + r • u ∈ C} := by
  classical
  let B : Set ℝ := interior {r : ℝ | k + r • u ∈ K.support}
  let L : Set ℝ := {r | c + r • u ∈ C}
  let Z : Set ℝ := {r | k + r • u ∈ frontier K.support}
  let N : Set ℝ := Set.image2 (· + ·) L Z
  have hL : L.Countable := (packing_centres_locallyFinite hcol.1).2.1.preimage
    (show Injective (fun r : ℝ => c + r • u) from
      fun r s hrs => smul_left_injective ℝ hu (add_left_cancel hrs))
  have hN : N.Countable := hL.image2 hfront.countable (· + ·)
  have hgood (r : ℝ) (hr : r ∈ B) (hz : r ∉ Z) : k + r • u ∈ K.openCarrier := by
    have hrF : r ∈ {r : ℝ | k + r • u ∈ K.support} := interior_subset hr
    by_contra hn
    apply hz
    change k + r • u ∈ frontier K.support
    rw [frontier, K.isPolygonal.isClosed.closure_eq]
    exact ⟨hrF, hn⟩
  have hOopen : IsOpen {r : ℝ | k + r • u ∈ K.openCarrier} :=
    isOpen_interior.preimage (by fun_prop)
  have hOsub : {r : ℝ | k + r • u ∈ K.openCarrier} ⊆ B := by
    intro r hr
    change r ∈ interior {r : ℝ | k + r • u ∈ K.support}
    rw [mem_interior_iff_mem_nhds]
    apply Filter.mem_of_superset (hOopen.mem_nhds hr)
    intro s hs
    change k + s • u ∈ K.support
    exact interior_subset hs
  have hnotZ (r l : ℝ) (hl : l ∈ L) (hr : r ∉ N) : r - l ∉ Z := by
    intro hz
    exact hr ⟨l, hl, r - l, hz, by ring⟩
  have htile (r l : ℝ) (hl : l ∈ L) (hr : r ∈ l +ᵥ B) (hN : r ∉ N) :
      c + k + r • u ∈ (c + l • u) +ᵥ K.openCarrier := by
    have hrl : r - l ∈ B := by
      simpa [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg,
        add_comm] using hr
    refine ⟨k + (r - l) • u, hgood (r - l) hrl (hnotZ r l hl hN), ?_⟩
    change c + l • u + (k + (r - l) • u) = c + k + r • u
    rw [sub_smul]
    abel
  have hcover (r : ℝ) : ∃ l ∈ L, k + (r - l) • u ∈ K.support := by
    have hbase : c + k ∈ regularSupport K C := translated_tile_mem_regularSupport hc hk
    have hinv := hcol.2.2.2 (r • u) (δ.smul_mem r huδ)
    have hx : c + k + r • u ∈ regularSupport K C := by
      have h := hinv ▸ (show r • u +ᵥ (c + k) ∈ r • u +ᵥ regularSupport K C from
        ⟨c + k, hbase, rfl⟩)
      simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using h
    have hxcl : c + k + r • u ∈ closure (openUnion K C) := interior_subset hx
    rw [closure_openUnion_eq_iUnion_support hcol.1] at hxcl
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hxcl
    obtain ⟨y, hy, hxy⟩ := hs
    obtain ⟨a, ha⟩ := hcol.2.2.1
    have hsc : (s : Plane) - c ∈ δ := by
      have h := δ.sub_mem (ha s s.property) (ha c hc)
      convert h using 1; abel
    rw [hspan] at hsc
    obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.mp hsc
    have hsl : (s : Plane) = c + l • u := by rw [hl]; abel
    refine ⟨l, ?_, ?_⟩
    · change c + l • u ∈ C
      rw [← hsl]
      exact s.property
    · have heq : y = k + (r - l) • u := by
        change (s : Plane) + y = c + k + r • u at hxy
        rw [hsl] at hxy
        rw [sub_smul]
        linear_combination hxy
      exact heq ▸ hy
  refine ⟨isOpen_interior.measurableSet, MeasurableSet.univ, hL, ?_, ?_⟩
  · intro l hl l' hl' hne
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hN.ae_notMem volume] with r hr
    rintro ⟨hrl, hrl'⟩
    have hcentres : c + l • u ≠ c + l' • u := by
      intro heq
      exact hne (smul_left_injective ℝ hu (add_left_cancel heq))
    exact Set.disjoint_left.mp ((isPacking_iff_openCarrier_disjoint K C).mp
      hcol.1 hl hl' hcentres) (htile r l hl hrl hr) (htile r l' hl' hrl' hr)
  · filter_upwards [hN.ae_notMem volume] with r hr
    constructor
    · intro _
      obtain ⟨l, hl, hrl⟩ := hcover r
      have hrlOpen : k + (r - l) • u ∈ K.openCarrier := by
        by_contra hn
        exact hnotZ r l hl hr (by
          change k + (r - l) • u ∈ frontier K.support
          rw [frontier, K.isPolygonal.isClosed.closure_eq]
          exact ⟨hrl, hn⟩)
      refine ⟨⟨l, hl⟩, ?_⟩
      change r ∈ l +ᵥ B
      rw [mem_vadd_set_iff_neg_vadd_mem]
      have hrlB : r - l ∈ B := hOsub hrlOpen
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hrlB
    · intro _
      trivial

private theorem lineSupported_exists_coord {δ : Submodule ℝ Plane} {C : Set Plane}
    {u c : Plane} (hspan : δ = Submodule.span ℝ ({u} : Set Plane))
    (hline : IsLineSupported C δ) (hc : c ∈ C) {s : Plane} (hs : s ∈ C) :
    ∃ r : ℝ, s = c + r • u := by
  obtain ⟨a, ha⟩ := hline
  have hsc : s - c ∈ δ := by
    have h := δ.sub_mem (ha s hs) (ha c hc)
    convert h using 1; abel
  rw [hspan] at hsc
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hsc
  exact ⟨r, by rw [hr]; abel⟩

private theorem column_scalar_period_lifts {δ : Submodule ℝ Plane} {C : Set Plane}
    {u c : Plane} {P : ℝ} (hspan : δ = Submodule.span ℝ ({u} : Set Plane))
    (hline : IsLineSupported C δ) (hc : c ∈ C)
    (hP : P ∈ periodGroup {r : ℝ | c + r • u ∈ C}) :
    P • u ∈ periodGroup C := by
  let L : Set ℝ := {r | c + r • u ∈ C}
  have hP' : P +ᵥ L = L := hP
  change P • u +ᵥ C = C
  ext s
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := lineSupported_exists_coord hspan hline hc hy
    have hr : r ∈ L := hy
    have hPr : P + r ∈ L := hP' ▸ ⟨r, hr, rfl⟩
    change c + (P + r) • u ∈ C at hPr
    simpa only [add_smul, vadd_eq_add, add_comm, add_left_comm, add_assoc] using hPr
  · intro hs
    obtain ⟨r, rfl⟩ := lineSupported_exists_coord hspan hline hc hs
    have hr : r ∈ L := hs
    have hneg : -P +ᵥ L = L := (periodGroup L).neg_mem hP
    have hnegR : -P + r ∈ L := hneg ▸ ⟨r, hr, rfl⟩
    refine ⟨c + (-P + r) • u, hnegR, ?_⟩
    simp only [add_smul, neg_smul, vadd_eq_add]
    abel

private theorem column_common_period_of_generic_section
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) {u k : Plane}
    (hu : u ≠ 0) (huδ : u ∈ δ)
    (hspan : δ = Submodule.span ℝ ({u} : Set Plane))
    (hk : k ∈ K.openCarrier)
    (hfront : {r : ℝ | k + r • u ∈ frontier K.support}.Finite)
    (hfinite : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
      (interior {r : ℝ | k + r • u ∈ K.support})) :
    ∃ q : Plane, q ∈ δ ∧ q ≠ 0 ∧ ∀ C : Set Plane,
      IsCenterColumn K δ C → q ∈ periodGroup C := by
  let B : Set ℝ := interior {r : ℝ | k + r • u ∈ K.support}
  have hOopen : IsOpen {r : ℝ | k + r • u ∈ K.openCarrier} :=
    isOpen_interior.preimage (by fun_prop)
  have hzero : (0 : ℝ) ∈ B := by
    change (0 : ℝ) ∈ interior {r : ℝ | k + r • u ∈ K.support}
    rw [mem_interior_iff_mem_nhds]
    apply Filter.mem_of_superset (hOopen.mem_nhds (show (0 : ℝ) ∈
      {r : ℝ | k + r • u ∈ K.openCarrier} from by simpa using hk))
    intro r hr
    change k + r • u ∈ K.support
    exact interior_subset hr
  have hmass : 0 < (volume B).toReal := ENNReal.toReal_pos
    (isOpen_interior.measure_pos volume ⟨0, hzero⟩).ne'
    (Tiling.AxisParallel.OneDimensional.FiniteInterval.IsFiniteIntervalRegion.measure_ne_top
      hfinite)
  obtain ⟨P, hP, _, hPL⟩ :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.exists_commonLinePeriod hfinite hmass
  refine ⟨P • u, δ.smul_mem P huδ, smul_ne_zero hP.ne' hu, ?_⟩
  intro C hcol
  obtain ⟨c, hc⟩ := hcol.2.1
  apply column_scalar_period_lifts hspan hcol.2.2.1 hc
  exact hPL _ (column_scalarLineTiles hu huδ hspan hk hfront hcol hc)

private theorem column_universal_period_of_scalarMerge
    (hmerge : ∀ {n : ℕ} (a b : Fin n → ℝ),
      Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
        (interior (⋃ i, Set.Icc (a i) (b i))))
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (hδ : Module.finrank ℝ δ = 1) :
    ∃ q : Plane, q ∈ δ ∧ q ≠ 0 ∧ ∀ C : Set Plane,
      IsCenterColumn K δ C → q ∈ periodGroup C := by
  obtain ⟨u, hu0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hδ]; norm_num)
  have hu : (u : Plane) ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hδ u.property hu
  let π : Plane →L[ℝ] ℝ := Tiling.planarCrossCLM u
  have hπsurj : Surjective π := planarCrossCLM_surjective hu
  have hπopen : IsOpenMap π := LinearMap.isOpenMap_of_finiteDimensional _ hπsurj
  have hπu : π u = 0 := by
    simp [π, Tiling.planarCross]
    ring
  obtain ⟨k, hk, hfront⟩ := polygonal_generic_line_finiteFrontier K u hu π hπopen hπu
  obtain ⟨n, a, b, _, hclosed⟩ := polygonal_lineSection_finiteClosedIntervals K k u hu
  apply column_common_period_of_generic_section K δ hu u.property hspan hk hfront
  rw [hclosed]
  exact hmerge a b

private theorem unionColumns_prescribed_multiple_of_scalarMerge
    (hmerge : ∀ {n : ℕ} (a b : Fin n → ℝ),
      Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
        (interior (⋃ i, Set.Icc (a i) (b i))))
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane} {γ : Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (hpack : IsPacking K.prototileFamily (K.placements T))
    (hcol : IsUnionOfColumns K δ T) (hproper : regularSupport K T ≠ Set.univ)
    (hγδ : γ ∉ δ) (hγperiod : γ ∈ periodGroup (regularSupport K T)) :
    ∃ n : ℕ, 0 < n ∧ ∀ t ∈ T, ∀ m : ℤ, ∃ s ∈ T,
      s - t - m • ((n : ℤ) • γ) ∈ δ ∧
        regularSupport K (lineFibre δ T s) =
          m • ((n : ℤ) • γ) +ᵥ regularSupport K (lineFibre δ T t) := by
  by_cases hTne : T.Nonempty
  · obtain ⟨u, hu0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hδ]; norm_num)
    have hu : (u : Plane) ≠ 0 := fun h => hu0 (Subtype.ext h)
    let π : Plane →L[ℝ] ℝ := Tiling.planarCrossCLM u
    have hπsurj : Surjective π := planarCrossCLM_surjective hu
    have hπopen : IsOpenMap π := LinearMap.isOpenMap_of_finiteDimensional _ hπsurj
    have hker : LinearMap.ker π.toLinearMap = δ := by
      rw [show π = Tiling.planarCrossCLM u by rfl, planarCrossCLM_ker_eq_span hu]
      exact (eq_span_singleton_of_mem_of_finrank_eq_one hδ u.property hu).symm
    have hclosedImage : closure (π '' K.openCarrier) = π '' K.support := by
      apply Set.Subset.antisymm
      · exact closure_minimal (Set.image_mono interior_subset)
          (K.isPolygonal.isCompact.image π.continuous).isClosed
      · rw [← K.isPolygonal.closure_interior]
        exact image_closure_subset_closure_image π.continuous
    obtain ⟨n, a, b, _, hclosed⟩ := polygonal_projection_finiteClosedIntervals K π
    apply unionColumns_prescribed_transverse_multiple_aux hTne hpack hcol hproper hγδ
      hγperiod hker hπopen hπsurj
    rw [← hclosedImage, hclosed]
    exact hmerge a b
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    exact (hTne ⟨t, ht⟩).elim

private theorem unionColumns_rawTransport_of_scalarMerge
    (hmerge : ∀ {n : ℕ} (a b : Fin n → ℝ),
      Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
        (interior (⋃ i, Set.Icc (a i) (b i))))
    {K : PolygonalRegion} {T E : Set Plane} {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (hEper : IsLatticePeriodic E) (hcol : IsUnionOfColumns K δ T) :
    ∃ q γ : Plane, q ∈ δ ∧ q ≠ 0 ∧ γ ∉ δ ∧ q ∈ periodGroup T ∧
      ∀ t ∈ T, ∀ m : ℤ, ∃ s ∈ T, s - t - m • γ ∈ δ ∧
        regularSupport K (lineFibre δ T s) =
          m • γ +ᵥ regularSupport K (lineFibre δ T t) := by
  obtain ⟨q, hqδ, hq0, hq⟩ := column_universal_period_of_scalarMerge hmerge K δ hδ
  have hqT : q ∈ periodGroup T := by
    change q +ᵥ T = T
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hqC := hq (lineFibre δ T t) (hcol t ht)
      have htC : t ∈ lineFibre δ T t := ⟨ht, by simp⟩
      have hqtC : q +ᵥ t ∈ lineFibre δ T t := hqC ▸ ⟨t, htC, rfl⟩
      exact hqtC.1
    · intro hx
      have hqC := (periodGroup (lineFibre δ T x)).neg_mem
        (hq (lineFibre δ T x) (hcol x hx))
      have hxC : x ∈ lineFibre δ T x := ⟨hx, by simp⟩
      have hnegC : (-q) +ᵥ x ∈ lineFibre δ T x := hqC ▸ ⟨x, hxC, rfl⟩
      exact ⟨(-q) +ᵥ x, hnegC.1, by simp⟩
  obtain ⟨u, hu0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hδ]; norm_num)
  have hu : (u : Plane) ≠ 0 := fun h => hu0 (Subtype.ext h)
  let π : Plane →L[ℝ] ℝ := Tiling.planarCrossCLM u
  have hπsurj : Surjective π := planarCrossCLM_surjective hu
  have hπopen : IsOpenMap π := LinearMap.isOpenMap_of_finiteDimensional _ hπsurj
  have hker : LinearMap.ker π.toLinearMap = δ := by
    rw [show π = Tiling.planarCrossCLM u by rfl, planarCrossCLM_ker_eq_span hu]
    exact (eq_span_singleton_of_mem_of_finrank_eq_one hδ u.property hu).symm
  have hclosedImage : closure (π '' K.openCarrier) = π '' K.support := by
    apply Set.Subset.antisymm
    · exact closure_minimal (Set.image_mono interior_subset)
        (K.isPolygonal.isCompact.image π.continuous).isClosed
    · rw [← K.isPolygonal.closure_interior]
      exact image_closure_subset_closure_image π.continuous
  obtain ⟨n, a, b, _, hclosed⟩ := polygonal_projection_finiteClosedIntervals K π
  have hJfinite : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion
      (interior (π '' K.support)) := by
    rw [← hclosedImage, hclosed]
    exact hmerge a b
  by_cases hproper : T.Nonempty ∧ regularSupport K T ≠ Set.univ
  · obtain ⟨β, hβE, hβδ⟩ := exists_lattice_period_not_mem_line hδ hEper
    have hβperiod : β ∈ periodGroup (regularSupport K T) := by
      rw [regularSupport_eq_of_tilesOn hEopen hEregular htile]
      exact hβE
    obtain ⟨n, hn, htransport⟩ := unionColumns_prescribed_multiple_of_scalarMerge
      hmerge hδ htile.2.1 hcol hproper.2 hβδ hβperiod
    refine ⟨q, (n : ℤ) • β, hqδ, hq0, ?_, hqT, htransport⟩
    intro hγδ
    apply hβδ
    have hnreal : ((n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have h := δ.smul_mem (((n : ℤ) : ℝ)⁻¹) hγδ
    simpa only [← Int.cast_smul_eq_zsmul ℝ, smul_smul, inv_mul_cancel₀ hnreal,
      one_smul] using h
  · obtain ⟨γ, hγδ, hγperiod⟩ := unionColumns_transverse_period hδ htile hEopen
      hEregular hEper hcol hker hπopen hπsurj hJfinite
    exact ⟨q, γ, hqδ, hq0, hγδ, hqT,
      unionColumns_transport_of_projected_period hker hπopen hcol hγperiod⟩

theorem unionColumns_prescribed_transverse_multiple
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane} {γ : Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (hpack : IsPacking K.prototileFamily (K.placements T))
    (hcol : IsUnionOfColumns K δ T)
    (hproper : regularSupport K T ≠ Set.univ)
    (hγδ : γ ∉ δ) (hγperiod : γ ∈ periodGroup (regularSupport K T)) :
    ∃ n : ℕ, 0 < n ∧ ∀ t ∈ T, ∀ m : ℤ, ∃ s ∈ T,
      s - t - m • ((n : ℤ) • γ) ∈ δ ∧
        regularSupport K (lineFibre δ T s) =
          m • ((n : ℤ) • γ) +ᵥ regularSupport K (lineFibre δ T t) := by
  apply unionColumns_prescribed_multiple_of_scalarMerge ?_ hδ hpack hcol hproper hγδ hγperiod
  intro n a b
  obtain ⟨P⟩ := Tiling.AxisParallel.Foundations.GenericSlices.finiteClosedIntervals_merge a b
  exact ⟨P.n, P.left, P.right, P.lt, P.union_eq⟩

/-- Raw column orbit facts; no good-parametrization record is imported backwards into
the geometry owner. Empty families satisfy this with arbitrary independent directions. -/
theorem unionColumns_has_transverseFibreTransport
    {K : PolygonalRegion} {T E : Set Plane} {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (hEper : IsLatticePeriodic E) (hcol : IsUnionOfColumns K δ T) :
    ∃ q γ : Plane, q ∈ δ ∧ q ≠ 0 ∧ γ ∉ δ ∧ q ∈ periodGroup T ∧
      ∀ t ∈ T, ∀ m : ℤ, ∃ s ∈ T, s - t - m • γ ∈ δ ∧
        regularSupport K (lineFibre δ T s) =
          m • γ +ᵥ regularSupport K (lineFibre δ T t) := by
  apply unionColumns_rawTransport_of_scalarMerge ?_ hδ htile hEopen hEregular hEper hcol
  intro n a b
  obtain ⟨P⟩ := Tiling.AxisParallel.Foundations.GenericSlices.finiteClosedIntervals_merge a b
  exact ⟨P.n, P.left, P.right, P.lt, P.union_eq⟩

private theorem lineFibre_period {δ : Submodule ℝ Plane} {T : Set Plane}
    {q : Plane} (hqδ : q ∈ δ) (hq : q ∈ periodGroup T) (t : Plane) :
    q ∈ periodGroup (lineFibre δ T t) := by
  change q +ᵥ T = T at hq
  change q +ᵥ lineFibre δ T t = lineFibre δ T t
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hyt⟩, rfl⟩
    refine ⟨hq ▸ ⟨y, hy, rfl⟩, ?_⟩
    convert δ.add_mem hqδ hyt using 1
    change q + y - t = q + (y - t)
    abel
  · rintro ⟨hx, hxt⟩
    refine ⟨x - q, ⟨?_, ?_⟩, by simp⟩
    · have hx' : x ∈ q +ᵥ T := hq.symm ▸ hx
      obtain ⟨y, hy, hxy⟩ := hx'
      convert hy using 1
      change q + y = x at hxy
      linear_combination -hxy
    · convert δ.sub_mem hxt hqδ using 1
      abel

private theorem zsmul_mem_direction_iff {δ : Submodule ℝ Plane} {γ : Plane}
    (hγ : γ ∉ δ) (m : ℤ) : m • γ ∈ δ ↔ m = 0 := by
  constructor
  · intro hm
    by_contra hm0
    apply hγ
    have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    have h := δ.smul_mem ((m : ℝ)⁻¹) hm
    simpa only [← Int.cast_smul_eq_zsmul ℝ, smul_smul, inv_mul_cancel₀ hmreal,
      one_smul] using h
  · rintro rfl
    simp

theorem unionColumns_periodicReplacement
    {K : PolygonalRegion} {T E : Set Plane} {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (hEper : IsLatticePeriodic E) (hcol : IsUnionOfColumns K δ T) :
    ∃ S : Set Plane, TilesOn K S E ∧ IsLatticePeriodic S := by
  classical
  obtain ⟨q, γ, hqδ, hq0, hγδ, hqT, htransport⟩ :=
    unionColumns_has_transverseFibreTransport hδ htile hEopen hEregular hEper hcol
  let orbit : Setoid T := {
    r := fun s t => ∃ m : ℤ, (s : Plane) - t - m • γ ∈ δ
    iseqv := ⟨fun t => ⟨0, by simp⟩,
      fun {s t} ⟨m, hm⟩ => ⟨-m, by
        convert δ.neg_mem hm using 1
        simp only [neg_zsmul]
        abel⟩,
      fun {s t v} ⟨m, hm⟩ ⟨n, hn⟩ => ⟨m + n, by
        convert δ.add_mem hm hn using 1
        simp only [add_zsmul]
        abel⟩⟩ }
  let Q := Quotient orbit
  let r : Q → T := Quotient.out
  have hr (a : Q) : Quotient.mk orbit (r a) = a := Quotient.out_eq a
  let I := Q × ℤ
  have hphase (i : I) := htransport (r i.1) (r i.1).property i.2
  choose base hbase hbaseδ hshape using hphase
  let P : I → Set Plane := fun i => i.2 • γ +ᵥ lineFibre δ T (r i.1)
  let C : I → Set Plane := fun i => lineFibre δ T (base i)
  let S : Set Plane := ⋃ i : I, P i
  have hbaseClass (i : I) : Quotient.mk orbit (⟨base i, hbase i⟩ : T) = i.1 :=
    (Quotient.sound (show orbit.r ⟨base i, hbase i⟩ (r i.1) from ⟨i.2, hbaseδ i⟩)).trans (hr i.1)
  have hdisj (i j : I) (hij : i ≠ j) : Disjoint (C i) (C j) := by
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hdiff : base i - base j ∈ δ := by
      convert δ.sub_mem hzj.2 hzi.2 using 1
      abel
    have hclasses : i.1 = j.1 := (hbaseClass i).symm.trans
      ((Quotient.sound (show orbit.r ⟨base i, hbase i⟩ ⟨base j, hbase j⟩ from
        ⟨0, by simpa using hdiff⟩)).trans (hbaseClass j))
    have hreps : (r i.1 : Plane) = r j.1 := congrArg (fun a => (r a : Plane)) hclasses
    have hmγ : (i.2 - j.2) • γ ∈ δ := by
      convert δ.sub_mem hdiff (δ.sub_mem (hbaseδ i) (hbaseδ j)) using 1
      simp only [sub_zsmul]
      rw [hreps]
      abel
    have hms : i.2 = j.2 := sub_eq_zero.mp ((zsmul_mem_direction_iff hγδ _).mp hmγ)
    exact hij (Prod.ext hclasses hms)
  have hcover : (⋃ i : I, C i) = T := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun _ _ ht => ht.1)
    · intro t ht
      let a : Q := Quotient.mk orbit ⟨t, ht⟩
      have horbit : orbit.r (⟨t, ht⟩ : T) (r a) := Quotient.exact (hr a).symm
      obtain ⟨m, hm⟩ := horbit
      apply Set.mem_iUnion.mpr
      refine ⟨(a, m), ht, ?_⟩
      convert δ.sub_mem hm (hbaseδ (a, m)) using 1
      abel
  have hPshape (i : I) : regularSupport K (P i) = regularSupport K (C i) :=
    (regularSupport_vadd K (lineFibre δ T (r i.1)) (i.2 • γ)).trans (hshape i).symm
  have hPpack (i : I) : IsPacking K.prototileFamily (K.placements (P i)) :=
    (tilesOn_translate (tilesOn_regularSupport_of_packing (hcol (r i.1) (r i.1).property).1)
      (i.2 • γ)).2.1
  have hSpack : IsPacking K.prototileFamily (K.placements S) := by
    rw [isPacking_iff_openCarrier_disjoint]
    intro x hx y hy hxy
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
    by_cases hij : i = j
    · subst j
      exact (isPacking_iff_openCarrier_disjoint K (P i)).mp (hPpack i) hxi hyj hxy
    · have hcarrierDisj : Disjoint (regularSupport K (P i)) (regularSupport K (P j)) := by
        rw [hPshape, hPshape]
        exact regularSupport_disjoint_of_disjoint_subfamilies htile.2.1
          (fun _ h => h.1) (fun _ h => h.1) (hdisj i j hij)
      rw [Set.disjoint_left]
      intro z hzx hzy
      obtain ⟨w, hw, rfl⟩ := hzx
      have hzw := translated_tile_mem_regularSupport hxi hw
      obtain ⟨v, hv, hyv⟩ := hzy
      have hzv := translated_tile_mem_regularSupport hyj hv
      change y + v = x + w at hyv
      rw [hyv] at hzv
      exact Set.disjoint_left.mp hcarrierDisj hzw hzv
  have hsupport : regularSupport K S = E := by
    calc
      regularSupport K S = interior (closure (⋃ i : I, regularSupport K (P i))) :=
        regularSupport_iUnion K P
      _ = interior (closure (⋃ i : I, regularSupport K (C i))) := by simp_rw [hPshape]
      _ = regularSupport K (⋃ i : I, C i) := (regularSupport_iUnion K C).symm
      _ = regularSupport K T := by rw [hcover]
      _ = E := regularSupport_eq_of_tilesOn hEopen hEregular htile
  have hqP (i : I) : q ∈ periodGroup (P i) := by
    have hqF := lineFibre_period hqδ hqT (r i.1)
    change q +ᵥ lineFibre δ T (r i.1) = lineFibre δ T (r i.1) at hqF
    change q +ᵥ (i.2 • γ +ᵥ lineFibre δ T (r i.1)) = i.2 • γ +ᵥ lineFibre δ T (r i.1)
    rw [← add_vadd, add_comm q, add_vadd, hqF]
  have hqS : q ∈ periodGroup S := by
    change q +ᵥ S = S
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨i, hiy⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨i, hqP i ▸ ⟨y, hiy, rfl⟩⟩
    · intro hx
      obtain ⟨i, hix⟩ := Set.mem_iUnion.mp hx
      have hneg := (periodGroup (P i)).neg_mem (hqP i)
      have hnegx : (-q) +ᵥ x ∈ P i := hneg ▸ ⟨x, hix, rfl⟩
      exact ⟨(-q) +ᵥ x, Set.mem_iUnion.mpr ⟨i, hnegx⟩, by simp⟩
  have hγS : γ ∈ periodGroup S := by
    change γ +ᵥ S = S
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨⟨a, m⟩, s, hs, rfl⟩ := Set.mem_iUnion.mp hy
      apply Set.mem_iUnion.mpr
      refine ⟨(a, m + 1), s, hs, ?_⟩
      change (m + 1) • γ + s = γ + (m • γ + s)
      simp only [add_zsmul, one_zsmul]
      abel
    · intro hx
      obtain ⟨⟨a, m⟩, s, hs, rfl⟩ := Set.mem_iUnion.mp hx
      refine ⟨(m - 1) • γ + s, Set.mem_iUnion.mpr ⟨(a, m - 1), s, hs, rfl⟩, ?_⟩
      change γ + ((m - 1) • γ + s) = m • γ + s
      simp only [sub_zsmul, one_zsmul]
      abel
  let L : PlanarLattice := {
    basis := ![γ, q]
    independent := by
      rw [linearIndependent_fin2]
      refine ⟨hq0, fun a heq => hγδ ?_⟩
      change a • q = γ at heq
      rw [← heq]
      exact δ.smul_mem a hqδ }
  refine ⟨S, hsupport ▸ tilesOn_regularSupport_of_packing hSpack, L, ?_⟩
  change L.toAddSubgroup ≤ periodGroup S
  rw [PlanarLattice.toAddSubgroup, AddSubgroup.closure_le]
  rintro v ⟨i, rfl⟩
  fin_cases i
  · exact hγS
  · exact hqS

/-! ## SlicesAndColumns owner -/


private theorem packing_locallyFell_limit {K : PolygonalRegion}
    {Sn : ℕ → Set Plane} {S : Set Plane}
    (hp : ∀ n, IsPacking K.prototileFamily (K.placements (Sn n)))
    (hlim : Tiling.Topology.LocallyFellConverges Sn S) :
    IsPacking K.prototileFamily (K.placements S) := by
  rw [isPacking_iff_openCarrier_disjoint]
  intro s hs t ht hst
  rw [Set.disjoint_left]
  intro x hxs hxt
  have hne : 0 < dist s t := dist_pos.mpr hst
  have hnear (c : Plane) (hxc : x ∈ c +ᵥ K.openCarrier) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ z, dist z c < ε → x ∈ z +ᵥ K.openCarrier := by
    have hpre : IsOpen ((fun z : Plane => x - z) ⁻¹' K.openCarrier) :=
      isOpen_interior.preimage (continuous_const.sub continuous_id)
    have hcpre : c ∈ (fun z : Plane => x - z) ⁻¹' K.openCarrier := by
      simpa only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, sub_eq_add_neg, add_comm] using hxc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hpre c hcpre
    refine ⟨ε, hε, fun z hz => ?_⟩
    have hzpre := hball hz
    refine ⟨x - z, hzpre, ?_⟩
    change z + (x - z) = x
    abel
  obtain ⟨εs, hεs, hsnear⟩ := hnear s hxs
  obtain ⟨εt, hεt, htnear⟩ := hnear t hxt
  let ε := min (min εs εt) (dist s t / 3)
  have hε : 0 < ε := lt_min (lt_min hεs hεt) (by positivity)
  have hhitS := Tiling.Topology.locallyFellConverges_eventually_exists_mem_ball hlim hs hε
  have hhitT := Tiling.Topology.locallyFellConverges_eventually_exists_mem_ball hlim ht hε
  obtain ⟨n, ⟨sn, hsn, hsnnear⟩, ⟨tn, htn, htnnear⟩⟩ := (hhitS.and hhitT).exists
  have hsx : x ∈ sn +ᵥ K.openCarrier :=
    hsnear sn (hsnnear.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have htx : x ∈ tn +ᵥ K.openCarrier :=
    htnear tn (htnnear.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hsntn : sn ≠ tn := by
    intro heq
    have hbound := dist_triangle s sn t
    have hsn' : dist sn s < dist s t / 3 := hsnnear.trans_le (min_le_right _ _)
    have htn' : dist tn t < dist s t / 3 := htnnear.trans_le (min_le_right _ _)
    rw [dist_comm s sn, heq] at hbound
    rw [heq] at hsn'
    linarith only [hbound, hsn', htn', hne]
  exact Set.disjoint_left.mp ((isPacking_iff_openCarrier_disjoint K (Sn n)).mp
    (hp n) hsn htn hsntn) hsx htx

private theorem support_limit_eventually_near {K : PolygonalRegion}
    {Sn : ℕ → Set Plane} {S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hlim : Tiling.Topology.LocallyFellConverges Sn S)
    {x : Plane} (hx : x ∈ closure (openUnion K S)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ y ∈ regularSupport K (Sn n), dist y x < ε := by
  rw [closure_openUnion_eq_iUnion_support hp] at hx
  obtain ⟨s, hsx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨k, hk, rfl⟩ := hsx
  have hkcl : k ∈ closure K.openCarrier := by
    simpa only [Tiling.RationalPolygonal.PolygonalRegion.openCarrier,
      K.isPolygonal.closure_interior] using hk
  obtain ⟨v, hv, hkv⟩ := Metric.mem_closure_iff.mp hkcl (ε / 2) (by positivity)
  filter_upwards [Tiling.Topology.locallyFellConverges_eventually_exists_mem_ball
    hlim s.property (show 0 < ε / 2 by positivity)] with n hn
  obtain ⟨t, ht, hts⟩ := hn
  refine ⟨t + v, translated_tile_mem_regularSupport ht hv, ?_⟩
  have hdist := dist_add_add_le t v (s : Plane) k
  rw [dist_comm k v] at hkv
  change dist (t + v) ((s : Plane) + k) < ε
  linarith only [hdist, hts, hkv]

private theorem support_limit_eventually_avoids {K : PolygonalRegion}
    {Sn : ℕ → Set Plane} {S : Set Plane}
    (hp : ∀ n, IsPacking K.prototileFamily (K.placements (Sn n)))
    (hlim : Tiling.Topology.LocallyFellConverges Sn S)
    {x : Plane} (hx : x ∉ closure (openUnion K S)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop,
      ∀ y, dist y x ≤ ε → y ∉ regularSupport K (Sn n) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    isClosed_closure.isOpen_compl x hx
  let ε := r / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  let F : Set Plane := (fun z : Plane × Plane => z.1 - z.2) ''
    (Metric.closedBall x ε ×ˢ K.support)
  have hFcompact : IsCompact F := by
    exact ((isCompact_closedBall x ε).prod K.isPolygonal.isCompact).image
      (continuous_fst.sub continuous_snd)
  have hSF : Disjoint S F := by
    rw [Set.disjoint_left]
    intro s hs hF
    obtain ⟨⟨y, k⟩, ⟨hy, hk⟩, hsk⟩ := hF
    have hynot := hball (show dist y x < r by
      have hy' : dist y x ≤ ε := hy
      dsimp [ε] at hy'
      linarith only [hr, hy'])
    apply hynot
    have hysupport : y ∈ s +ᵥ K.support := by
      refine ⟨k, hk, ?_⟩
      change s + k = y
      change y - k = s at hsk
      linear_combination -hsk
    have hysingle : y ∈ closure ((s : Plane) +ᵥ K.openCarrier) := by
      rw [closure_vadd, Tiling.RationalPolygonal.PolygonalRegion.openCarrier,
        K.isPolygonal.closure_interior]
      exact hysupport
    apply closure_mono (show s +ᵥ K.openCarrier ⊆ openUnion K S from
      Set.subset_iUnion_of_subset ⟨s, hs⟩ Set.Subset.rfl) hysingle
  refine ⟨ε, hε, ?_⟩
  filter_upwards [Tiling.Topology.locallyFellConverges_eventually_disjoint_compact
    hlim hFcompact hSF] with n hn y hy hysupport
  have hyclosure : y ∈ closure (openUnion K (Sn n)) := interior_subset hysupport
  rw [closure_openUnion_eq_iUnion_support (hp n)] at hyclosure
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hyclosure
  obtain ⟨k, hk, hsk⟩ := hs
  apply Set.disjoint_left.mp hn s.property
  refine ⟨(y, k), ⟨hy, hk⟩, ?_⟩
  change (s : Plane) + k = y at hsk
  linear_combination -hsk

private theorem locallyFell_comp {Sn : ℕ → Set Plane} {S : Set Plane}
    (hc : Tiling.Topology.LocallyFellConverges Sn S)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tiling.Topology.LocallyFellConverges (Sn ∘ φ) S := by
  obtain ⟨hSn, hS, hconv⟩ := hc
  exact ⟨fun n => hSn (φ n), hS, hconv.comp hφ.tendsto_atTop⟩

private theorem locallyFell_track {Sn : ℕ → Set Plane} {S : Set Plane}
    (hc : Tiling.Topology.LocallyFellConverges Sn S) {x : Plane} (hx : x ∈ S) :
    ∃ (φ : ℕ → ℕ) (xn : ℕ → Plane), StrictMono φ ∧
      (∀ n, xn n ∈ Sn (φ n)) ∧ Tendsto xn atTop (𝓝 x) := by
  classical
  have hN (k : ℕ) : ∃ N : ℕ, ∀ n ≥ N,
      ∃ y ∈ Sn n, dist y x < 1 / ((k : ℝ) + 1) := by
    exact Filter.eventually_atTop.mp
      (Tiling.Topology.locallyFellConverges_eventually_exists_mem_ball hc hx (by positivity))
  choose N hN using hN
  let φ : ℕ → ℕ := Nat.rec (N 0) (fun n a => max (a + 1) (N (n + 1)))
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact lt_of_lt_of_le (Nat.lt_succ_self (φ n)) (le_max_left _ _)
  have hφN (n : ℕ) : N n ≤ φ n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_right _ _
  choose xn hxn hxndist using fun n => hN n (φ n) (hφN n)
  refine ⟨φ, xn, hφ, hxn, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  apply (hxndist n).trans_le
  apply le_trans _ hk.le
  exact one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hn 1)

private theorem locallyFell_limit_mono {An Bn : ℕ → Set Plane} {A B : Set Plane}
    (hA : Tiling.Topology.LocallyFellConverges An A)
    (hB : Tiling.Topology.LocallyFellConverges Bn B)
    (hsub : ∀ n, An n ⊆ Bn n) : A ⊆ B := by
  intro x hx
  obtain ⟨φ, xn, hφ, hxn, hxlim⟩ := locallyFell_track hA hx
  exact Tiling.Topology.mem_of_locallyFellConverges_of_tendsto_mem
    (locallyFell_comp hB hφ) (fun n => hsub (φ n) (hxn n)) hxlim

private theorem packing_mono {K : PolygonalRegion} {S T : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements T)) (hST : S ⊆ T) :
    IsPacking K.prototileFamily (K.placements S) := by
  rw [isPacking_iff_openCarrier_disjoint] at hp ⊢
  exact hp.mono hST

theorem lineCarrier_noProperVertices_iff_column
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {S : Set Plane}
    (hδ : Module.finrank ℝ δ = 1) (hS : S.Nonempty)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (hline : IsLineSupported S δ) :
    properVertices (regularSupport K S) = ∅ ↔ IsCenterColumn K δ S := by
  constructor
  · intro hW
    refine ⟨hp, hS, hline, ?_⟩
    obtain ⟨A, _, hsat⟩ := noCornerLineCarrier_localSaturation K
    have hglobal (x y : Plane) (hxy : y - x ∈ δ) :
        x ∈ regularSupport K S ↔ y ∈ regularSupport K S := by
      let R := dist x 0 + dist y 0 + 1
      have hR : 0 < R := by dsimp [R]; positivity
      have hcorners : Disjoint (properVertices (regularSupport K S))
          (Metric.ball 0 (R + A)) := by rw [hW]; simp
      have hs := hsat δ hδ S hp hline 0 R hR hcorners
      apply hs x (by rw [Metric.mem_ball]; dsimp [R]; have := dist_nonneg (x := y) (y := 0); linarith)
        y (by rw [Metric.mem_ball]; dsimp [R]; have := dist_nonneg (x := x) (y := 0); linarith) hxy
    intro u hu
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hglobal x (u + x) (by simpa using hu)).mp hx
    · intro hy
      refine ⟨y - u, ?_, by simp⟩
      apply (hglobal (y - u) y (by simpa using hu)).mpr hy
  · intro hcol
    have hSct := (packing_centres_locallyFinite hp).2.1
    have hWct : (properVertices (regularSupport K S)).Countable := by
      apply ((K.isPolygonal.vertexSet_finite.countable).image2 hSct (· + ·)).mono
      intro x hx
      obtain ⟨v, hv, s, hs, hxs⟩ := properVertexProvenance hp x hx
      exact ⟨v, hv, s, hs, hxs.symm⟩
    obtain ⟨u, hu0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hδ]; norm_num)
    have hu : (u : Plane) ≠ 0 := fun h => hu0 (Subtype.ext h)
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    let f : ℝ → Plane := fun r => r • (u : Plane) + x
    have hf : Injective f := by
      intro r s hrs
      exact smul_left_injective ℝ hu (add_right_cancel hrs)
    have hpre : f ⁻¹' properVertices (regularSupport K S) = univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro r
      have hinv := hcol.2.2.2 (r • (u : Plane)) (δ.smul_mem r u.property)
      have hWinv : r • (u : Plane) +ᵥ properVertices (regularSupport K S) =
          properVertices (regularSupport K S) := by
        rw [← properVertices_vadd, hinv]
      exact hWinv ▸ ⟨x, hx, rfl⟩
    exact Set.not_countable_univ (hpre ▸ hWct.preimage hf)

theorem column_maximal_in_fibre
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T C : Set Plane}
    (hδ : Module.finrank ℝ δ = 1)
    (hp : IsPacking K.prototileFamily (K.placements T))
    (hcT : C ⊆ T) (hc : IsCenterColumn K δ C) :
    ∀ t ∈ C, lineFibre δ T t = C := by
  clear hδ
  intro t ht
  apply Set.Subset.antisymm
  · intro s hs
    by_contra hsC
    have hdisj : Disjoint C ({s} : Set Plane) := by
      rw [Set.disjoint_singleton_right]
      exact hsC
    have hcarriers := regularSupport_disjoint_of_disjoint_subfamilies
      hp hcT (Set.singleton_subset_iff.mpr hs.1) hdisj
    obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have htu := translated_tile_mem_regularSupport ht hu
    have hsu : s + u ∈ regularSupport K C := by
      have hinv := hc.2.2.2 (s - t) hs.2
      rw [← hinv]
      exact ⟨t + u, htu, by change s - t + (t + u) = s + u; abel⟩
    exact Set.disjoint_left.mp hcarriers hsu
      (translated_tile_mem_regularSupport (Set.mem_singleton s) hu)
  · obtain ⟨a, ha⟩ := hc.2.2.1
    intro s hs
    refine ⟨hcT hs, ?_⟩
    convert δ.sub_mem (ha s hs) (ha t ht) using 1
    abel

/-- Disjointness is essential; two columns sharing a tile need not be parallel. -/
theorem disjoint_columns_parallel
    {K : PolygonalRegion} {T C U : Set Plane} {δ ε : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) (hε : Module.finrank ℝ ε = 1)
    (hp : IsPacking K.prototileFamily (K.placements T))
    (hcT : C ⊆ T) (huT : U ⊆ T) (hdisj : Disjoint C U)
    (hc : IsCenterColumn K δ C) (hu : IsCenterColumn K ε U) : δ = ε := by
  by_contra hne
  have hnle : ¬ ε ≤ δ := by
    intro hle
    exact hne (Submodule.eq_of_le_of_finrank_eq hle (hε.trans hδ.symm)).symm
  obtain ⟨v, hvε, hvδ⟩ := SetLike.not_le_iff_exists.mp hnle
  have hsmallTop : δ ⊔ Submodule.span ℝ ({v} : Set Plane) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.finrank_sup_span_singleton hvδ, hδ]
    simp [Plane, Complex.finrank_real_complex]
  have htop : δ ⊔ ε = ⊤ := by
    apply top_unique
    rw [← hsmallTop]
    exact sup_le_sup_left (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvε)) δ
  obtain ⟨c, hcC⟩ := hc.2.1
  obtain ⟨d, hdU⟩ := hu.2.1
  obtain ⟨w, hw⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hdiff : d - c ∈ δ ⊔ ε := by rw [htop]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hdiff
  have hC : a + (c + w) ∈ regularSupport K C := by
    rw [← hc.2.2.2 a ha]
    exact ⟨c + w, translated_tile_mem_regularSupport hcC hw, rfl⟩
  have hU : a + (c + w) ∈ regularSupport K U := by
    rw [← hu.2.2.2 (-b) (ε.neg_mem hb)]
    refine ⟨d + w, translated_tile_mem_regularSupport hdU hw, ?_⟩
    change -b + (d + w) = a + (c + w)
    linear_combination -hab
  exact Set.disjoint_left.mp
    (regularSupport_disjoint_of_disjoint_subfamilies hp hcT huT hdisj) hC hU

theorem column_universal_period (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) :
    ∃ q : Plane, q ∈ δ ∧ q ≠ 0 ∧ ∀ C : Set Plane,
      IsCenterColumn K δ C → q ∈ periodGroup C := by
  apply column_universal_period_of_scalarMerge ?_ K δ hδ
  intro n a b
  obtain ⟨P⟩ := Tiling.AxisParallel.Foundations.GenericSlices.finiteClosedIntervals_merge a b
  exact ⟨P.n, P.left, P.right, P.lt, P.union_eq⟩

theorem unionColumns_singlyPeriodic
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    (hδ : Module.finrank ℝ δ = 1) (hcol : IsUnionOfColumns K δ T) :
    ∃ q : Plane, q ∈ δ ∧ q ≠ 0 ∧ q ∈ periodGroup T := by
  obtain ⟨q, hqδ, hq0, hq⟩ := column_universal_period K δ hδ
  refine ⟨q, hqδ, hq0, ?_⟩
  change q +ᵥ T = T
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hqC := hq (lineFibre δ T t) (hcol t ht)
    change q +ᵥ lineFibre δ T t = lineFibre δ T t at hqC
    have htC : t ∈ lineFibre δ T t := ⟨ht, by simp⟩
    have hqtC : q +ᵥ t ∈ lineFibre δ T t := hqC ▸ ⟨t, htC, rfl⟩
    exact hqtC.1
  · intro hx
    have hqC := (periodGroup (lineFibre δ T x)).neg_mem
      (hq (lineFibre δ T x) (hcol x hx))
    change (-q) +ᵥ lineFibre δ T x = lineFibre δ T x at hqC
    have hxC : x ∈ lineFibre δ T x := ⟨hx, by simp⟩
    have hnegC : (-q) +ᵥ x ∈ lineFibre δ T x := hqC ▸ ⟨x, hxC, rfl⟩
    exact ⟨(-q) +ᵥ x, hnegC.1, by simp⟩

theorem noCornerLineLimit_isColumn
    {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) {Cn : ℕ → Set Plane} {C : Set Plane}
    {tn : ℕ → Plane} {t : Plane}
    (hp : ∀ n, IsPacking K.prototileFamily (K.placements (Cn n)))
    (htn : ∀ n, tn n ∈ Cn n)
    (hline : ∀ n, ∀ s ∈ Cn n, s - tn n ∈ δ)
    (htlim : Tendsto tn atTop (𝓝 t))
    (hc : Tiling.Topology.LocallyFellConverges Cn C)
    (hcorners : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
      Disjoint (properVertices (regularSupport K (Cn n))) (Metric.ball 0 R)) :
    IsCenterColumn K δ C := by
  have hpack := packing_locallyFell_limit hp hc
  have htC := Tiling.Topology.mem_of_locallyFellConverges_of_tendsto_mem hc htn htlim
  have hlineC : IsLineSupported C δ := by
    refine ⟨t, fun s hs => ?_⟩
    change s - t ∈ (δ : Set Plane)
    rw [← δ.closed_of_finiteDimensional.closure_eq]
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have htnnear : ∀ᶠ n in atTop, dist (tn n) t < ε / 2 :=
      (Metric.tendsto_nhds.mp htlim) (ε / 2) (by positivity)
    have hhit := Tiling.Topology.locallyFellConverges_eventually_exists_mem_ball
      hc hs (show 0 < ε / 2 by positivity)
    obtain ⟨n, hn, sn, hsn, hdist⟩ := (htnnear.and hhit).exists
    refine ⟨sn - tn n, hline n sn hsn, ?_⟩
    have hbound := dist_add_add_le s (-t) sn (-(tn n))
    rw [dist_neg_neg, dist_comm t (tn n), dist_comm s sn] at hbound
    change dist (s + -t) (sn + -(tn n)) < ε
    linarith only [hbound, hn, hdist]
  obtain ⟨A, hA, hsat⟩ := noCornerLineCarrier_localSaturation K
  have hmove (u : Plane) (hu : u ∈ δ) (x : Plane)
      (hx : x ∈ closure (openUnion K C)) :
      u + x ∈ closure (openUnion K C) := by
    by_contra hnot
    obtain ⟨ε, hε, havoid⟩ := support_limit_eventually_avoids hp hc hnot
    let η := min ε 1
    have hη : 0 < η := lt_min hε zero_lt_one
    let R := dist x 0 + dist (u + x) 0 + 2
    have hR : 0 < R := by dsimp [R]; positivity
    have hcorn := hcorners (R + A) (add_pos hR hA)
    have hnear := support_limit_eventually_near hpack hc hx hη
    obtain ⟨n, ⟨hnAvoid, hnCorners⟩, y, hy, hyx⟩ :=
      ((havoid.and hcorn).and hnear).exists
    have hyball : y ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball]
      have htri := dist_triangle y x 0
      have hy1 : dist y x < 1 := hyx.trans_le (min_le_right _ _)
      dsimp [R]
      have := dist_nonneg (x := u + x) (y := 0)
      linarith only [htri, hy1, this]
    have huyball : u + y ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball]
      have htri := dist_triangle (u + y) (u + x) 0
      rw [dist_add_left] at htri
      have hy1 : dist y x < 1 := hyx.trans_le (min_le_right _ _)
      dsimp [R]
      have := dist_nonneg (x := x) (y := 0)
      linarith only [htri, hy1, this]
    have hsatn := hsat δ hδ (Cn n) (hp n) ⟨tn n, hline n⟩ 0 R hR hnCorners
    have huy : u + y ∈ regularSupport K (Cn n) :=
      (hsatn y hyball (u + y) huyball (by simpa using hu)).mp hy
    exact hnAvoid (u + y) (by
      rw [dist_add_left]
      exact hyx.le.trans (min_le_left _ _)) huy
  have hclosedInv : IsInvariantAlong (closure (openUnion K C)) δ := by
    intro u hu
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hmove u hu y hy
    · intro hx
      refine ⟨-u + x, hmove (-u) (δ.neg_mem hu) x hx, ?_⟩
      simp [vadd_eq_add]
  refine ⟨hpack, ⟨t, htC⟩, hlineC, ?_⟩
  intro u hu
  change u +ᵥ interior (closure (openUnion K C)) = interior (closure (openUnion K C))
  rw [← interior_vadd, hclosedInv u hu]

theorem unionColumns_closedUnderLimits
    {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) {Tn : ℕ → Set Plane} {S : Set Plane}
    (hp : ∀ n, IsPacking K.prototileFamily (K.placements (Tn n)))
    (hcol : ∀ n, IsUnionOfColumns K δ (Tn n))
    (hlim : Tiling.Topology.LocallyFellConverges Tn S) :
    IsUnionOfColumns K δ S := by
  intro s hs
  obtain ⟨φ, sn, hφ, hsn, hsnlim⟩ := locallyFell_track hlim hs
  let Fn : ℕ → Set Plane := fun n => lineFibre δ (Tn (φ n)) (sn n)
  have hFncol (n : ℕ) : IsCenterColumn K δ (Fn n) := hcol (φ n) (sn n) (hsn n)
  obtain ⟨d, hd, hsep⟩ := exists_packingSeparation K
  have hFnclosed (n : ℕ) : IsClosed (Fn n) :=
    (packing_centres_locallyFinite (hFncol n).1).2.2
  have hFnsep (n : ℕ) : Tiling.Topology.IsUniformlySeparated d (Fn n) :=
    hsep (Fn n) (hFncol n).1
  obtain ⟨ψ, C, hψ, _, _, hCconv⟩ :=
    Tiling.Topology.exists_locallyFellConvergent_subsequence d hd Fn hFnclosed hFnsep
  have hanchors (n : ℕ) : sn (ψ n) ∈ Fn (ψ n) := ⟨hsn (ψ n), by simp⟩
  have hanchorlim : Tendsto (sn ∘ ψ) atTop (𝓝 s) := hsnlim.comp hψ.tendsto_atTop
  have hC : IsCenterColumn K δ C := by
    apply noCornerLineLimit_isColumn hδ (fun n => (hFncol (ψ n)).1)
      hanchors (fun n t ht => ht.2) hanchorlim hCconv
    intro R hR
    apply Filter.Eventually.of_forall
    intro n
    have hW : properVertices (regularSupport K (Fn (ψ n))) = ∅ :=
      (lineCarrier_noProperVertices_iff_column hδ (hFncol (ψ n)).2.1
        (hFncol (ψ n)).1 (hFncol (ψ n)).2.2.1).mpr (hFncol (ψ n))
    rw [hW]
    simp
  have hCsub : C ⊆ S :=
    locallyFell_limit_mono hCconv (locallyFell_comp hlim (hφ.comp hψ))
      (fun n t ht => ht.1)
  have hsC : s ∈ C := Tiling.Topology.mem_of_locallyFellConverges_of_tendsto_mem
    hCconv hanchors hanchorlim
  have heq := column_maximal_in_fibre hδ (packing_locallyFell_limit hp hlim) hCsub hC s hsC
  rw [heq]
  exact hC

private theorem lineFibre_vadd (δ : Submodule ℝ Plane) (T : Set Plane) (u t : Plane) :
    lineFibre δ (u +ᵥ T) (u + t) = u +ᵥ lineFibre δ T t := by
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

private theorem unionColumns_vadd {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (hcol : IsUnionOfColumns K δ T) (u : Plane) :
    IsUnionOfColumns K δ (u +ᵥ T) := by
  rintro x ⟨t, ht, rfl⟩
  change IsCenterColumn K δ (lineFibre δ (u +ᵥ T) (u + t))
  rw [lineFibre_vadd]
  obtain ⟨hp, hne, ⟨a, ha⟩, hinv⟩ := hcol t ht
  refine ⟨(tilesOn_translate (tilesOn_regularSupport_of_packing hp) u).2.1,
    hne.image (fun y => u +ᵥ y), ⟨u + a, ?_⟩, ?_⟩
  · rintro x ⟨s, hs, rfl⟩
    convert ha s hs using 1
    change (u + s) - (u + a) = s - a
    abel
  · rw [regularSupport_vadd]
    intro v hv
    calc
      v +ᵥ (u +ᵥ regularSupport K (lineFibre δ T t)) =
          (v + u) +ᵥ regularSupport K (lineFibre δ T t) := (add_vadd _ _ _).symm
      _ = (u + v) +ᵥ regularSupport K (lineFibre δ T t) := by rw [add_comm v u]
      _ = u +ᵥ (v +ᵥ regularSupport K (lineFibre δ T t)) := add_vadd _ _ _
      _ = u +ᵥ regularSupport K (lineFibre δ T t) := by rw [hinv v hv]

private theorem fibreProperVertices_vadd (K : PolygonalRegion) (T : Set Plane)
    (δ : Submodule ℝ Plane) (u : Plane) :
    fibreProperVertices K (u +ᵥ T) δ = u +ᵥ fibreProperVertices K T δ := by
  have hmem {V : Set Plane} {x : Plane} : x ∈ fibreProperVertices K V δ ↔
      ∃ t ∈ V, x ∈ properVertices (regularSupport K (lineFibre δ V t)) := by
    simp only [fibreProperVertices, Set.mem_iUnion, Subtype.exists, exists_prop]
  ext x
  constructor
  · intro hx
    obtain ⟨t, ⟨s, hs, hst⟩, hx⟩ := hmem.mp hx
    change u + s = t at hst
    subst t
    rw [lineFibre_vadd, regularSupport_vadd, properVertices_vadd] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hmem.mpr ⟨s, hs, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, ht, hyt⟩ := hmem.mp hy
    apply hmem.mpr
    refine ⟨u + t, ⟨t, ht, rfl⟩, ?_⟩
    rw [lineFibre_vadd, regularSupport_vadd, properVertices_vadd]
    exact ⟨y, hyt, rfl⟩

private theorem unionColumns_of_fibreCorners_escape
    {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) {Tn : ℕ → Set Plane} {S : Set Plane}
    (hp : ∀ n, IsPacking K.prototileFamily (K.placements (Tn n)))
    (hlim : Tiling.Topology.LocallyFellConverges Tn S)
    (hcorn : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
      Disjoint (fibreProperVertices K (Tn n) δ) (Metric.ball 0 R)) :
    IsUnionOfColumns K δ S := by
  intro s hs
  obtain ⟨φ, sn, hφ, hsn, hsnlim⟩ := locallyFell_track hlim hs
  let Fn : ℕ → Set Plane := fun n => lineFibre δ (Tn (φ n)) (sn n)
  have hFnpack (n : ℕ) : IsPacking K.prototileFamily (K.placements (Fn n)) :=
    packing_mono (hp (φ n)) (fun _ h => h.1)
  obtain ⟨d, hd, hsep⟩ := exists_packingSeparation K
  obtain ⟨ψ, C, hψ, _, _, hCconv⟩ :=
    Tiling.Topology.exists_locallyFellConvergent_subsequence d hd Fn
      (fun n => (packing_centres_locallyFinite (hFnpack n)).2.2)
      (fun n => hsep (Fn n) (hFnpack n))
  have hanchors (n : ℕ) : sn (ψ n) ∈ Fn (ψ n) := ⟨hsn (ψ n), by simp⟩
  have hanchorlim : Tendsto (sn ∘ ψ) atTop (𝓝 s) := hsnlim.comp hψ.tendsto_atTop
  have hC : IsCenterColumn K δ C := by
    apply noCornerLineLimit_isColumn hδ (fun n => hFnpack (ψ n))
      hanchors (fun n t ht => ht.2) hanchorlim hCconv
    intro R hR
    filter_upwards [(hφ.comp hψ).tendsto_atTop.eventually (hcorn R hR)] with n hn
    apply hn.mono_left
    exact Set.subset_iUnion_of_subset ⟨sn (ψ n), hsn (ψ n)⟩ Set.Subset.rfl
  have hCsub : C ⊆ S := locallyFell_limit_mono hCconv
    (locallyFell_comp hlim (hφ.comp hψ)) (fun _ _ ht => ht.1)
  have hsC := Tiling.Topology.mem_of_locallyFellConverges_of_tendsto_mem
    hCconv hanchors hanchorlim
  rw [column_maximal_in_fibre hδ (packing_locallyFell_limit hp hlim) hCsub hC s hsC]
  exact hC

theorem minimal_noncolumn_fibreCorners_relativeDense
    {K : PolygonalRegion} {T E : Set Plane} {δ : Submodule ℝ Plane}
    (hδ : Module.finrank ℝ δ = 1) (hT : T.Nonempty)
    (htile : TilesOn K T E) (hEopen : IsOpen E)
    (hEregular : interior (closure E) = E) (hEper : IsLatticePeriodic E)
    (hminimal : Tiling.Polygonal.Topology.IsMinimalTiling K T E)
    (hnotcol : ¬ IsUnionOfColumns K δ T) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : Plane,
      ∃ v ∈ fibreProperVertices K T δ, dist x v < R := by
  classical
  clear hT
  by_contra hbad
  push Not at hbad
  obtain ⟨L, hL⟩ := hEper
  obtain ⟨D, hD, hrep⟩ := planarLattice_boundedCosetRepresentative L
  have hholes (n : ℕ) : ∃ x : Plane, ∀ v ∈ fibreProperVertices K T δ,
      ¬ dist x v < D + ((n : ℝ) + 1) := by
    simpa only [not_lt] using hbad (D + ((n : ℝ) + 1)) (by positivity)
  choose x hx using hholes
  choose ℓ hℓ hℓdist using fun n => hrep (x n)
  let g : ℕ → aePeriodGroup E := fun n => ⟨-ℓ n, by
    rw [aePeriodGroup_eq_periodGroup_of_regularOpen hEopen hEregular]
    exact (periodGroup E).neg_mem (hL (hℓ n))⟩
  let Tn : ℕ → Set Plane := fun n => (g n : Plane) +ᵥ T
  have hTnpack (n : ℕ) : IsPacking K.prototileFamily (K.placements (Tn n)) :=
    (tilesOn_translate htile (g n : Plane)).2.1
  have hcorn (R : ℝ) (hR : 0 < R) : ∀ᶠ n in atTop,
      Disjoint (fibreProperVertices K (Tn n) δ) (Metric.ball 0 R) := by
    obtain ⟨N, hN⟩ := exists_nat_gt R
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    rw [Set.disjoint_left]
    intro v hv hvball
    rw [fibreProperVertices_vadd] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    apply hx n w hw
    have hbound := dist_triangle (x n) (ℓ n) w
    have hclose : dist (x n) (ℓ n) ≤ D := by
      simpa only [dist_eq_norm_sub] using hℓdist n
    have hshift : dist (ℓ n) w = dist ((g n : Plane) + w) 0 := by
      change dist (ℓ n) w = dist (-ℓ n + w) 0
      rw [dist_comm (ℓ n) w]
      simp [dist_eq_norm_sub, sub_eq_add_neg, add_comm]
    rw [Metric.mem_ball] at hvball
    change dist ((g n : Plane) + w) 0 < R at hvball
    rw [hshift] at hbound
    have hnR : R < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
    linarith only [hbound, hclose, hvball, hnR]
  obtain ⟨d, hd, hsep⟩ := exists_packingSeparation K
  obtain ⟨φ, S, hφ, _, _, hlim⟩ :=
    Tiling.Topology.exists_locallyFellConvergent_subsequence d hd Tn
      (fun n => (packing_centres_locallyFinite (hTnpack n)).2.2)
      (fun n => hsep (Tn n) (hTnpack n))
  have hScol : IsUnionOfColumns K δ S :=
    unionColumns_of_fibreCorners_escape hδ (fun n => hTnpack (φ n)) hlim
      (fun R hR => hφ.tendsto_atTop.eventually (hcorn R hR))
  obtain ⟨h, hreturn⟩ := (Tiling.Polygonal.Topology.isMinimalTiling_iff_returnSequences
    K T E htile).mp hminimal S ⟨fun n => g (φ n), hlim⟩
  have hSpack := packing_locallyFell_limit (fun n => hTnpack (φ n)) hlim
  apply hnotcol
  exact unionColumns_closedUnderLimits hδ
    (fun n => (tilesOn_translate (tilesOn_regularSupport_of_packing hSpack) (h n : Plane)).2.1)
    (fun n => unionColumns_vadd hScol (h n : Plane)) hreturn


end Tiling.Polygonal
