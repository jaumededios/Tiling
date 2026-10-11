import Tiling.Geometry.PolygonalCarrier

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology

noncomputable section

namespace Tiling.RationalSlopes

open Tiling.RationalPolygonal (PolygonalRegion IntegerPlane integerPoint)

def HasRationalDirection (δ : Submodule ℝ Plane) : Prop :=
  ∃ z : IntegerPlane, z ≠ 0 ∧ integerPoint z ∈ δ

def IsRationalVectorDirection (v : Plane) : Prop :=
  v ≠ 0 ∧ HasRationalDirection (Submodule.span ℝ ({v} : Set Plane))

def HasRationalSlopes (K : PolygonalRegion) : Prop :=
  ∃ F : Finset (Plane × Plane),
    (∀ e ∈ F, IsRationalVectorDirection (e.2 - e.1)) ∧
      frontier K.support = ⋃ e ∈ F, segment ℝ e.1 e.2

def IsRationalLinear (A : Plane ≃L[ℝ] Plane) : Prop :=
  ∀ v : Plane, IsRationalPoint v → IsRationalPoint (A v)

private theorem integerPoint_ne_zero {z : IntegerPlane} (hz : z ≠ 0) :
    integerPoint z ≠ 0 := by
  intro h
  apply hz
  exact Tiling.RationalPolygonal.integerPoint_injective (by simpa using h)

theorem hasRationalDirection_iff_integerSpan
    (δ : Submodule ℝ Plane) (hδ : Module.finrank ℝ δ = 1) :
    HasRationalDirection δ ↔
      ∃ z : IntegerPlane, z ≠ 0 ∧
        δ = Submodule.span ℝ ({integerPoint z} : Set Plane) := by
  constructor
  · rintro ⟨z, hz, hmem⟩
    exact ⟨z, hz, eq_span_singleton_of_mem_of_finrank_eq_one hδ hmem
      (integerPoint_ne_zero hz)⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, Submodule.mem_span_singleton_self _⟩

theorem isRationalVectorDirection_iff (v : Plane) :
    IsRationalVectorDirection v ↔ ∃ z : IntegerPlane,
      z ≠ 0 ∧ ∃ r : ℝ, r ≠ 0 ∧ v = r • integerPoint z := by
  constructor
  · rintro ⟨hv, hrat⟩
    obtain ⟨z, hz, heq⟩ := (hasRationalDirection_iff_integerSpan _
      (finrank_span_singleton hv)).mp hrat
    have hmem : v ∈ Submodule.span ℝ ({integerPoint z} : Set Plane) := by
      rw [← heq]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨z, hz, r, fun hzero => hv (by simpa [hzero] using hr.symm), hr.symm⟩
  · rintro ⟨z, hz, r, hr, rfl⟩
    refine ⟨smul_ne_zero hr (integerPoint_ne_zero hz), z, hz, ?_⟩
    exact Submodule.mem_span_singleton.mpr ⟨r⁻¹, by simp [hr]⟩

theorem rationalPoint_isRationalVectorDirection {v : Plane}
    (hv : IsRationalPoint v) (hne : v ≠ 0) : IsRationalVectorDirection v := by
  obtain ⟨p, q, hp, hq⟩ := hv
  let z : IntegerPlane := ![p.num * (q.den : ℤ), q.num * (p.den : ℤ)]
  let d : ℝ := (p.den : ℝ) * (q.den : ℝ)
  have hpd : (p.den : ℝ) ≠ 0 := by exact_mod_cast p.den_nz
  have hqd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hd : d ≠ 0 := mul_ne_zero hpd hqd
  have heq : v = d⁻¹ • integerPoint z := by
    apply Complex.ext
    · simp [z, d, hp, Tiling.RationalPolygonal.integerPoint,
        Rat.cast_def]
      field_simp
    · simp [z, d, hq, Tiling.RationalPolygonal.integerPoint,
        Rat.cast_def]
      field_simp
  apply (isRationalVectorDirection_iff v).mpr
  refine ⟨z, ?_, d⁻¹, inv_ne_zero hd, heq⟩
  intro hz
  exact hne (by simpa [hz] using heq)

private theorem segment_direction_mem_of_local {D : Set Plane} {a b x : Plane}
    {δ : Submodule ℝ Plane} (hseg : segment ℝ a b ⊆ D)
    (hx : x ∈ segment ℝ a b)
    (hlocal : ∀ᶠ y in 𝓝 x, y ∈ D → y - x ∈ δ) : b - a ∈ δ := by
  have endpoint (p : Plane) (hp : p ∈ segment ℝ a b) : p - x ∈ δ := by
    let f : ℝ → Plane := fun t => t • (p - x) + x
    have ht : Tendsto f (𝓝 0) (𝓝 x) := by
      have hc : Continuous f := by fun_prop
      simpa only [f, zero_smul, zero_add] using hc.continuousAt.tendsto (x := (0 : ℝ))
    obtain ⟨l, u, hlu, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ht.eventually hlocal)
    let t : ℝ := min u 1 / 2
    have hupos : 0 < u := hlu.2
    have htpos : 0 < t := by dsimp [t]; positivity
    have htlt : t < u := by dsimp [t]; linarith [min_le_left u 1]
    have htle : t ≤ 1 := by dsimp [t]; linarith [min_le_right u 1]
    have hfseg : f t ∈ segment ℝ a b := by
      have hc := (convex_segment a b) hx hp (sub_nonneg.mpr htle)
        htpos.le (sub_add_cancel 1 t)
      convert hc using 1
      simp only [f, smul_sub, sub_smul, one_smul]
      abel
    have hscaled := hI ⟨lt_trans hlu.1 htpos, htlt⟩ (hseg hfseg)
    have := δ.smul_mem t⁻¹ hscaled
    simpa [f, smul_smul, htpos.ne'] using this
  have ha := endpoint a (left_mem_segment ℝ a b)
  have hb := endpoint b (right_mem_segment ℝ a b)
  convert δ.sub_mem hb ha using 1
  abel

private theorem segment_direction_axis {D : Set Plane} (hD : IsAxisParallel D)
    {a b : Plane} (hseg : segment ℝ a b ⊆ frontier D) :
    (b - a).re = 0 ∨ (b - a).im = 0 := by
  obtain ⟨ε, hε, hcross⟩ := hD.localBoundaryCross a
  let f : ℝ → Plane := fun t => t • (b - a) + a
  have ht : Tendsto f (𝓝 0) (𝓝 a) := by
    have hc : Continuous f := by fun_prop
    simpa only [f, zero_smul, zero_add] using hc.continuousAt.tendsto (x := (0 : ℝ))
  obtain ⟨l, u, hlu, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (ht.eventually (Metric.ball_mem_nhds a hε))
  let t : ℝ := min u 1 / 2
  have hupos : 0 < u := hlu.2
  have htpos : 0 < t := by dsimp [t]; positivity
  have htlt : t < u := by dsimp [t]; linarith [min_le_left u 1]
  have htle : t ≤ 1 := by dsimp [t]; linarith [min_le_right u 1]
  have hfseg : f t ∈ segment ℝ a b := by
    rw [segment_eq_image]
    refine ⟨t, ⟨htpos.le, htle⟩, ?_⟩
    change (1 - t) • a + t • b = t • (b - a) + a
    module
  have hc := hcross (f t) (hI ⟨lt_trans hlu.1 htpos, htlt⟩) (hseg hfseg)
  rcases hc with hr | hi
  · left
    have : t * (b - a).re = 0 := by simpa [f] using hr
    exact (mul_eq_zero.mp this).resolve_left htpos.ne'
  · right
    have : t * (b - a).im = 0 := by simpa [f] using hi
    exact (mul_eq_zero.mp this).resolve_left htpos.ne'

private theorem rational_direction_axis {v : Plane} (hv : v ≠ 0)
    (haxis : v.re = 0 ∨ v.im = 0) : IsRationalVectorDirection v := by
  apply (isRationalVectorDirection_iff v).mpr
  rcases haxis with hr | hi
  · refine ⟨![0, 1], by decide, v.im, ?_, ?_⟩
    · intro hz
      apply hv
      apply Complex.ext <;> simp [hr, hz]
    · apply Complex.ext <;> simp [Tiling.RationalPolygonal.integerPoint, hr]
  · refine ⟨![1, 0], by decide, v.re, ?_, ?_⟩
    · intro hz
      apply hv
      apply Complex.ext <;> simp [hi, hz]
    · apply Complex.ext <;> simp [Tiling.RationalPolygonal.integerPoint, hi]

theorem hasRationalSlopes_of_isAxisParallel (K : PolygonalRegion)
    (hK : IsAxisParallel K.support) : HasRationalSlopes K := by
  obtain ⟨F, hF, hcover⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  refine ⟨F, ?_, hcover⟩
  intro e he
  obtain ⟨hne, -, -, hseg⟩ := hF e he
  exact rational_direction_axis (sub_ne_zero.mpr hne.symm)
    (segment_direction_axis hK hseg)

theorem hasRationalSlopes_of_isRelativelyRational (K : PolygonalRegion)
    (hK : Tiling.RationalPolygonal.IsRelativelyRational K) :
    HasRationalSlopes K := by
  obtain ⟨v, hv, hrat⟩ := hK
  obtain ⟨F, hF, hcover⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  refine ⟨F, ?_, hcover⟩
  intro e he
  obtain ⟨hne, ha, hb, -⟩ := hF e he
  obtain ⟨p, q, hp, hq⟩ := hrat e.1 ha
  obtain ⟨r, s, hr, hs⟩ := hrat e.2 hb
  apply rationalPoint_isRationalVectorDirection _ (sub_ne_zero.mpr hne.symm)
  refine ⟨r - p, s - q, ?_, ?_⟩
  · simp only [Rat.cast_sub, Complex.sub_re] at *
    linarith
  · simp only [Rat.cast_sub, Complex.sub_im] at *
    linarith

theorem hasRationalSlopes_iff_localDirections (K : PolygonalRegion) :
    HasRationalSlopes K ↔
      ∀ x ∈ frontier K.support, x ∉ vertexSet K.support →
        ∃ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 ∧ HasRationalDirection δ ∧
          ∀ᶠ y in 𝓝 x, (y ∈ frontier K.support ↔ y - x ∈ δ) := by
  constructor
  · rintro ⟨F, hrat, hcover⟩ x hx hxv
    obtain ⟨L, hxL, hdim, hlocal⟩ :=
      K.isPolygonal.boundaryLocallyStraightAt_of_not_mem_vertexSet hx hxv
    have hlocal' : ∀ᶠ y in 𝓝 x,
        y ∈ frontier K.support ↔ y - x ∈ L.direction := by
      filter_upwards [hlocal] with y hy
      exact hy.trans (L.vsub_right_mem_direction_iff_mem hxL y).symm
    have hxcover := hx
    rw [hcover] at hxcover
    obtain ⟨e, hxe⟩ := mem_iUnion.mp hxcover
    obtain ⟨heF, hxe⟩ := mem_iUnion.mp hxe
    have hseg : segment ℝ e.1 e.2 ⊆ frontier K.support := by
      rw [hcover]
      exact subset_iUnion_of_subset e (subset_iUnion_of_subset heF subset_rfl)
    have hdir := segment_direction_mem_of_local hseg hxe (hlocal'.mono fun y hy => hy.mp)
    obtain ⟨hne, z, hz, hzspan⟩ := hrat e heF
    have hle : Submodule.span ℝ ({e.2 - e.1} : Set Plane) ≤ L.direction :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr hdir
    exact ⟨L.direction, hdim, ⟨z, hz, hle hzspan⟩, hlocal'⟩
  · intro hlocal
    obtain ⟨F, hF, hcover⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
    refine ⟨F, ?_, hcover⟩
    intro e he
    obtain ⟨hne, -, -, hseg⟩ := hF e he
    have hinf : (segment ℝ e.1 e.2).Infinite := by
      rw [segment_eq_image_lineMap]
      exact (Icc_infinite (by norm_num : (0 : ℝ) < 1)).image
        (AffineMap.lineMap_injective ℝ hne).injOn
    obtain ⟨x, hxseg, hxv⟩ := hinf.exists_notMem_finite K.isPolygonal.vertexSet_finite
    obtain ⟨δ, hdim, hrat, hloc⟩ := hlocal x (hseg hxseg) hxv
    have hdir := segment_direction_mem_of_local hseg hxseg (hloc.mono fun y hy => hy.mp)
    have hdne : e.2 - e.1 ≠ 0 := sub_ne_zero.mpr hne.symm
    have heq := eq_span_singleton_of_mem_of_finrank_eq_one hdim hdir hdne
    exact ⟨hdne, heq ▸ hrat⟩

theorem IsRationalLinear.symm {A : Plane ≃L[ℝ] Plane}
    (hA : IsRationalLinear A) : IsRationalLinear A.symm := by
  intro v hv
  -- The inverse-coordinate formula in the rational basis (1, I).
  have h1 := hA 1 ⟨1, 0, by norm_num, by norm_num⟩
  have hI := hA Complex.I ⟨0, 1, by norm_num, by norm_num⟩
  rcases h1 with ⟨a₁, a₂, ha₁, ha₂⟩
  rcases hI with ⟨b₁, b₂, hb₁, hb₂⟩
  rcases hv with ⟨x, y, hx, hy⟩
  let a : Plane := A 1
  let b : Plane := A Complex.I
  let d : ℚ := a₁ * b₂ - b₁ * a₂
  have ha : a.re = (a₁ : ℝ) ∧ a.im = (a₂ : ℝ) := ⟨ha₁, ha₂⟩
  have hb : b.re = (b₁ : ℝ) ∧ b.im = (b₂ : ℝ) := ⟨hb₁, hb₂⟩
  have hdet : d ≠ 0 := by
    intro hd
    by_cases hzero : a₂ = 0 ∧ b₂ = 0
    · have ha0 : a₁ ≠ 0 := by
        intro ha10
        have hAone : A (1 : Plane) = 0 := by
          apply Complex.ext <;> simp [a, ha.1, ha.2, ha10, hzero.1]
        exact one_ne_zero (A.injective (hAone.trans (map_zero A).symm))
      have hrel : b = ((b₁ / a₁ : ℚ) : ℝ) • a := by
        apply Complex.ext
        · simp only [Complex.smul_re, smul_eq_mul]
          rw [hb.1, ha.1]
          exact_mod_cast (div_mul_cancel₀ b₁ ha0).symm
        · simp only [Complex.smul_im, smul_eq_mul]
          rw [hb.2, ha.2]
          simp [hzero.1, hzero.2]
      have hrelA : A Complex.I = ((b₁ / a₁ : ℚ) : ℝ) • A 1 := by
        simpa [a, b] using hrel
      have hpre : (Complex.I : Plane) = ((b₁ / a₁ : ℚ) : ℝ) • (1 : Plane) :=
        A.injective (by simpa only [map_smul] using hrelA)
      have him := congrArg Complex.im hpre
      norm_num at him
    · have hlin : (b₂ : ℝ) • a - (a₂ : ℝ) • b = 0 := by
        apply Complex.ext
        · simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul, ha.1, hb.1,
            Complex.zero_re]
          have hdR : (a₁ : ℝ) * b₂ - b₁ * a₂ = 0 := by exact_mod_cast hd
          nlinarith [hdR]
        · simp only [Complex.sub_im, Complex.smul_im, smul_eq_mul, ha.2, hb.2,
            Complex.zero_im]
          ring
      have hmap : A ((b₂ : ℝ) • (1 : Plane) - (a₂ : ℝ) • Complex.I) =
          (b₂ : ℝ) • a - (a₂ : ℝ) • b := by
        rw [map_sub, map_smul, map_smul]
      have hpre : (b₂ : ℝ) • (1 : Plane) - (a₂ : ℝ) • Complex.I = 0 := by
        apply A.injective
        rw [hmap, hlin]
        simp
      have hre := congrArg Complex.re hpre
      have him := congrArg Complex.im hpre
      simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul, Complex.one_re,
        Complex.I_re, mul_one, mul_zero, sub_zero, Complex.zero_re] at hre
      simp only [Complex.sub_im, Complex.smul_im, smul_eq_mul, Complex.one_im,
        Complex.I_im, mul_zero, mul_one, zero_sub, Complex.zero_im, neg_eq_zero] at him
      have hb20 : b₂ = 0 := by exact_mod_cast hre
      have ha20 : a₂ = 0 := by exact_mod_cast him
      exact hzero ⟨ha20, hb20⟩
  let w := A.symm v
  have hw : A w = v := A.apply_symm_apply v
  have hcoords : w.re = ((x * b₂ - b₁ * y) / d : ℚ) ∧
      w.im = ((a₁ * y - x * a₂) / d : ℚ) := by
    have hrepr : A w = w.re • a + w.im • b := by
      have hdecomp : w = w.re • (1 : Plane) + w.im • Complex.I := by
        apply Complex.ext <;> simp
      rw [hdecomp, map_add, map_smul, map_smul]
      simp [a, b]
    have hr := congrArg Complex.re hw
    have hi := congrArg Complex.im hw
    rw [hrepr, Complex.add_re, Complex.smul_re, Complex.smul_re, ha.1, hb.1] at hr
    rw [hrepr, Complex.add_im, Complex.smul_im, Complex.smul_im, ha.2, hb.2] at hi
    rw [hx] at hr
    rw [hy] at hi
    constructor
    · have heq : (d : ℝ) * w.re = ((x * b₂ - b₁ * y : ℚ) : ℝ) := by
        dsimp [d]
        push_cast
        linear_combination (b₂ : ℝ) * hr - (b₁ : ℝ) * hi
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdet
      push_cast
      apply (eq_div_iff hdR).2
      simpa [mul_comm] using heq
    · have heq : (d : ℝ) * w.im = ((a₁ * y - x * a₂ : ℚ) : ℝ) := by
        dsimp [d]
        push_cast
        linear_combination (a₁ : ℝ) * hi - (a₂ : ℝ) * hr
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdet
      push_cast
      apply (eq_div_iff hdR).2
      simpa [mul_comm] using heq
  exact ⟨(x * b₂ - b₁ * y) / d, (a₁ * y - x * a₂) / d,
    hcoords.1, hcoords.2⟩

private theorem rational_direction_linear {A : Plane ≃L[ℝ] Plane}
    (hA : IsRationalLinear A) {v : Plane} (hv : IsRationalVectorDirection v) :
    IsRationalVectorDirection (A v) := by
  obtain ⟨z, hz, r, hr, hv⟩ := (isRationalVectorDirection_iff v).mp hv
  have hzr : IsRationalPoint (integerPoint z) := by
    refine ⟨(z 0 : ℚ), (z 1 : ℚ), ?_, ?_⟩ <;>
      simp [Tiling.RationalPolygonal.integerPoint]
  have hAz : A (integerPoint z) ≠ 0 := by
    exact fun h => integerPoint_ne_zero hz (A.injective (by simpa using h))
  obtain ⟨w, hw, s, hs, hAs⟩ := (isRationalVectorDirection_iff _).mp
    (rationalPoint_isRationalVectorDirection (hA _ hzr) hAz)
  refine (isRationalVectorDirection_iff _).mpr ⟨w, hw, r * s, mul_ne_zero hr hs, ?_⟩
  rw [hv, map_smul, hAs, smul_smul]

private theorem rational_boundary_affineImage (D : Set Plane)
    (A : Plane ≃L[ℝ] Plane) (hA : IsRationalLinear A) (a : Plane)
    (hD : ∃ F : Finset (Plane × Plane),
      (∀ e ∈ F, IsRationalVectorDirection (e.2 - e.1)) ∧
        frontier D = ⋃ e ∈ F, segment ℝ e.1 e.2) :
    ∃ F : Finset (Plane × Plane),
      (∀ e ∈ F, IsRationalVectorDirection (e.2 - e.1)) ∧
        frontier (Tiling.Polygonal.affineMap A a '' D) =
          ⋃ e ∈ F, segment ℝ e.1 e.2 := by
  classical
  obtain ⟨F, hrat, hcover⟩ := hD
  let f := Tiling.Polygonal.affineMap A a
  let h : Plane ≃ₜ Plane := A.toHomeomorph.trans (Homeomorph.addLeft a)
  have hh : (h : Plane → Plane) = f := rfl
  let φ : Plane →ᵃ[ℝ] Plane :=
    { toFun := f
      linear := A.toLinearMap
      map_vadd' := by intro p v; simp [f, Tiling.Polygonal.affineMap, add_comm, add_left_comm] }
  have hseg (p q : Plane) : f '' segment ℝ p q = segment ℝ (f p) (f q) :=
    image_segment ℝ φ p q
  refine ⟨F.image (fun e => (f e.1, f e.2)), ?_, ?_⟩
  · intro e he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    have heq : f b.2 - f b.1 = A (b.2 - b.1) := by
      simp [f, Tiling.Polygonal.affineMap, map_sub]
    rw [heq]
    exact rational_direction_linear hA (hrat b hb)
  · have hfront : frontier (Tiling.Polygonal.affineMap A a '' D) = f '' frontier D :=
      (h.image_frontier D).symm
    rw [hfront, hcover]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨e, he⟩ := mem_iUnion.mp hx
      obtain ⟨heF, hxe⟩ := mem_iUnion.mp he
      exact mem_iUnion.mpr ⟨(f e.1, f e.2), mem_iUnion.mpr
        ⟨Finset.mem_image.mpr ⟨e, heF, rfl⟩, hseg e.1 e.2 ▸ mem_image_of_mem f hxe⟩⟩
    · intro hy
      obtain ⟨e, he⟩ := mem_iUnion.mp hy
      obtain ⟨heF, hye⟩ := mem_iUnion.mp he
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp heF
      rw [← hseg] at hye
      obtain ⟨x, hx, rfl⟩ := hye
      exact mem_image_of_mem f (mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hb, hx⟩⟩)

theorem hasRationalSlopes_affineImage_iff (K : PolygonalRegion)
    (A : Plane ≃L[ℝ] Plane) (hA : IsRationalLinear A) (a : Plane) :
    HasRationalSlopes (Tiling.Polygonal.affineImage K A a) ↔
      HasRationalSlopes K := by
  constructor
  · intro h
    have hback := rational_boundary_affineImage
      (Tiling.Polygonal.affineImage K A a).support A.symm hA.symm (-A.symm a) h
    have hcancel : Tiling.Polygonal.affineMap A.symm (-A.symm a) ''
        (Tiling.Polygonal.affineImage K A a).support = K.support := by
      change Tiling.Polygonal.affineMap A.symm (-A.symm a) ''
        (Tiling.Polygonal.affineMap A a '' K.support) = K.support
      rw [← image_comp]
      have hf : Tiling.Polygonal.affineMap A.symm (-A.symm a) ∘
          Tiling.Polygonal.affineMap A a = id := by
        funext x
        simp [Tiling.Polygonal.affineMap]
      rw [hf, image_id]
    rw [hcancel] at hback
    exact hback
  · intro h
    exact rational_boundary_affineImage K.support A hA a h

theorem exists_rationalLinear_straighten (δ : Submodule ℝ Plane)
    (hδ : Module.finrank ℝ δ = 1) (hrat : HasRationalDirection δ) :
    ∃ A : Plane ≃L[ℝ] Plane, IsRationalLinear A ∧
      δ.map A.toLinearMap = Submodule.span ℝ ({Complex.I} : Set Plane) := by
  rcases hrat with ⟨z, hz, hzm⟩
  let p : ℤ := z 0
  let q : ℤ := z 1
  have hcoord : p ≠ 0 ∨ q ≠ 0 := by
    by_contra! h
    apply hz
    funext i
    fin_cases i <;> simp [p, q, h]
  let c : ℂ := (q : ℝ) + (p : ℝ) * Complex.I
  have hc : c ≠ 0 := by
    intro hc0
    have hre := congrArg Complex.re hc0
    have him := congrArg Complex.im hc0
    simp only [c, Complex.add_re, Complex.add_im, Complex.mul_I_re, Complex.mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, add_zero, zero_add,
      Complex.zero_re, Complex.zero_im] at hre him
    rcases hcoord with hp | hq
    · exact hp (by exact_mod_cast him)
    · exact hq (by exact_mod_cast hre)
  let u : ℂˣ := Units.mk0 c hc
  let A : Plane ≃L[ℝ] Plane :=
    (u.mulLeftLinearEquiv ℝ ℂ).toContinuousLinearEquivOfContinuous
      (by change Continuous (fun x : ℂ => c * x); fun_prop)
  have hA : IsRationalLinear A := by
    intro v hv
    rcases hv with ⟨x, y, hx, hy⟩
    refine ⟨(q : ℚ) * x - (p : ℚ) * y,
      (p : ℚ) * x + (q : ℚ) * y, ?_, ?_⟩
    · change (c * v).re = _
      simp [c, Complex.mul_re, hx, hy]
    · change (c * v).im = _
      simp [c, Complex.mul_im, hx, hy]
      ring
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hδ hzm (integerPoint_ne_zero hz)
  refine ⟨A, hA, ?_⟩
  rw [hspan, Submodule.map_span]
  have hAz : A (integerPoint z) = ((z 0 : ℝ) ^ 2 + (z 1 : ℝ) ^ 2) • Complex.I := by
    change c * integerPoint z = _
    apply Complex.ext
    · simp only [Complex.smul_re, Complex.I_re, smul_eq_mul, mul_zero]
      simp [c, integerPoint, p, q, Complex.mul_re]
      ring
    · simp only [Complex.smul_im, Complex.I_im, smul_eq_mul, mul_one]
      simp [c, integerPoint, p, q, Complex.mul_im]
      ring
  rw [Set.image_singleton]
  change ℝ ∙ A (integerPoint z) = ℝ ∙ Complex.I
  rw [hAz]
  have hscale : ((z 0 : ℝ) ^ 2 + (z 1 : ℝ) ^ 2) ≠ 0 := by
    rcases hcoord with hp | hq
    · have hpR : (z 0 : ℝ) ≠ 0 := by exact_mod_cast hp
      exact ne_of_gt (by nlinarith [sq_pos_of_ne_zero hpR, sq_nonneg (z 1 : ℝ)])
    · have hqR : (z 1 : ℝ) ≠ 0 := by exact_mod_cast hq
      exact ne_of_gt (by nlinarith [sq_pos_of_ne_zero hqR, sq_nonneg (z 0 : ℝ)])
  have hu : IsUnit ((z 0 : ℝ) ^ 2 + (z 1 : ℝ) ^ 2) := isUnit_iff_ne_zero.mpr hscale
  exact Submodule.span_singleton_smul_eq hu Complex.I


end Tiling.RationalSlopes
