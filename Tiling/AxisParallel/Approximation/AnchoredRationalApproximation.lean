import Tiling.AxisParallel.Approximation.Core
import Tiling.Geometry.Plane
import Tiling.RationalPolygonal.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Basis.Basic

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Approximation

noncomputable section

private theorem sub_mem_uIcc_iff (a x p q : ℝ) :
    -a + x ∈ Set.uIcc p q ↔ x ∈ Set.uIcc (a + p) (a + q) := by
  simp only [Set.mem_uIcc]
  constructor
  · rintro (h | h)
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · rintro (h | h)
    · left; constructor <;> linarith
    · right; constructor <;> linarith

private theorem vadd_rectangle (a p q : Tiling.Plane) :
    a +ᵥ Complex.Rectangle p q = Complex.Rectangle (a + p) (a + q) := by
  ext z
  simp only [Complex.Rectangle, Set.mem_vadd_set_iff_neg_vadd_mem,
    Complex.mem_reProdIm, vadd_eq_add, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, sub_mem_uIcc_iff]

private noncomputable def vaddRectangulation {s : Set Tiling.Plane}
    (R : Tiling.Rectangulation s) (a : Tiling.Plane) :
    Tiling.Rectangulation (a +ᵥ s) where
  pieces := R.pieces.image (a +ᵥ ·)
  isRectangle := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨p, q, hre, him, rfl⟩ := R.isRectangle q hq
    exact ⟨a + p, a + q, by simpa using hre, by simpa using him,
      vadd_rectangle a p q⟩
  pairwiseAEDisjoint := by
    rw [Finset.coe_image]
    rintro _ ⟨r, hr, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    apply Tiling.aedisjoint_vadd a
    apply R.pairwiseAEDisjoint hr hq
    intro hrq
    exact hne (by simp [hrq])
  sUnion_eq := by
    ext z
    constructor
    · rintro ⟨u, hu, hzu⟩
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzu ⊢
      rw [← R.sUnion_eq]
      exact Set.mem_sUnion_of_mem hzu hq
    · intro hz
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz
      obtain ⟨q, hq, hzq⟩ := Set.mem_sUnion.mp (R.sUnion_eq.symm ▸ hz)
      exact Set.mem_sUnion_of_mem
        (by simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using hzq)
        (Finset.mem_image.mpr ⟨q, hq, rfl⟩)

private noncomputable def vaddRegion (K : Tiling.AxisParallel.Region)
    (a : Tiling.Plane) : Tiling.AxisParallel.Region where
  support := a +ᵥ K.support
  isPolygonal := K.isPolygonal.vadd a
  nonempty := by
    obtain ⟨x, hx⟩ := K.nonempty
    exact ⟨a + x, by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hx⟩
  isAxisParallel := by
    obtain ⟨R⟩ := K.isAxisParallel
    exact ⟨vaddRectangulation R a⟩

private theorem Region.vadd_openCarrier (K : Tiling.AxisParallel.Region)
    (a : Tiling.Plane) :
    (vaddRegion K a).openCarrier = a +ᵥ K.openCarrier := by
  change interior (a +ᵥ K.support) = a +ᵥ interior K.support
  rw [interior_vadd]

private theorem Region.vadd_vertices (K : Tiling.AxisParallel.Region)
    (a : Tiling.Plane) :
    (vaddRegion K a).vertices = a +ᵥ K.vertices := by
  exact Tiling.vertexSet_vadd a K.support

private theorem Region.eq_of_support_eq {K L : Tiling.AxisParallel.Region}
    (h : K.support = L.support) : K = L := by
  cases K with
  | mk K hK =>
    cases L with
    | mk L hL =>
      simp only [Tiling.AxisParallel.Region.mk.injEq]
      cases K with
      | mk Ks Kp Kn =>
        cases L with
        | mk Ls Lp Ln =>
          simpa only [Tiling.RationalPolygonal.PolygonalRegion.mk.injEq] using h

private theorem vadd_neg_vadd_set (a : Tiling.Plane) (S : Set Tiling.Plane) :
    (-a) +ᵥ (a +ᵥ S) = S := by
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add]
  constructor <;> intro hx
  · convert hx using 1
    all_goals abel
  · convert hx using 1
    all_goals abel

private theorem add_vadd_set (a b : Tiling.Plane) (S : Set Tiling.Plane) :
    a +ᵥ (b +ᵥ S) = (a + b) +ᵥ S := by
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  constructor <;> intro hx
  · convert hx using 1
    all_goals abel
  · convert hx using 1
    all_goals abel

private theorem vaddRegion_neg_vadd (K : Tiling.AxisParallel.Region)
    (a : Tiling.Plane) : vaddRegion (vaddRegion K a) (-a) = K := by
  apply Region.eq_of_support_eq
  exact vadd_neg_vadd_set a K.support

private theorem tilesOn_vadd
    (K : Tiling.AxisParallel.Region) (S D : Set Tiling.Plane)
    (a b : Tiling.Plane) (h : Tiling.AxisParallel.TilesOn K S D) :
    Tiling.AxisParallel.TilesOn (vaddRegion K a) (b +ᵥ S) ((a + b) +ᵥ D) := by
  refine ⟨?_, ?_, ?_⟩
  · have hset : b +ᵥ S = (fun s : Tiling.Plane ↦ b + s) '' S := by
      ext x
      constructor
      · intro hx
        exact ⟨-b + x, by
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hx,
          by abel_nf⟩
      · rintro ⟨s, hs, rfl⟩
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          neg_add_cancel_left] using hs
    rw [hset]
    exact h.1.image _
  · intro i hi j hj hij
    let i₀ : Tiling.Placement Tiling.Plane Unit := (-b + i.1, ())
    let j₀ : Tiling.Placement Tiling.Plane Unit := (-b + j.1, ())
    have hi₀ : i₀ ∈ K.toPolygonalRegion.placements S := by
      change -b + i.1 ∈ S
      change i.1 ∈ b +ᵥ S at hi
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hi
    have hj₀ : j₀ ∈ K.toPolygonalRegion.placements S := by
      change -b + j.1 ∈ S
      change j.1 ∈ b +ᵥ S at hj
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hj
    have hij₀ : i₀ ≠ j₀ := by
      intro heq
      apply hij
      apply Prod.ext
      · have := congrArg Prod.fst heq
        dsimp only [i₀, j₀] at this
        linear_combination this
      · exact Subsingleton.elim _ _
    have hd := h.2.1 hi₀ hj₀ hij₀
    have hd' := Tiling.aedisjoint_vadd (a + b) hd
    have hiTile :
        (a + b) +ᵥ ((-b + i.1) +ᵥ K.support) =
          i.1 +ᵥ (a +ᵥ K.support) := by
      rw [add_vadd_set, add_vadd_set]
      congr 1
      abel
    have hjTile :
        (a + b) +ᵥ ((-b + j.1) +ᵥ K.support) =
          j.1 +ᵥ (a +ᵥ K.support) := by
      rw [add_vadd_set, add_vadd_set]
      congr 1
      abel
    change MeasureTheory.AEDisjoint MeasureTheory.volume
      (i.1 +ᵥ (a +ᵥ K.support)) (j.1 +ᵥ (a +ᵥ K.support))
    rw [← hiTile, ← hjTile]
    exact hd'
  · have hpull :=
      (MeasureTheory.quasiMeasurePreserving_add_left MeasureTheory.volume (-(a + b))).ae h.2.2
    filter_upwards [hpull] with x hx
    have htarget : x ∈ (a + b) +ᵥ D ↔ -(a + b) + x ∈ D := by
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    have hunion :
        (∃ s : b +ᵥ S,
            x ∈ ((s : Tiling.Plane) +ᵥ (vaddRegion K a).openCarrier)) ↔
          ∃ s : S, -(a + b) + x ∈ ((s : Tiling.Plane) +ᵥ K.openCarrier) := by
      rw [Region.vadd_openCarrier]
      constructor
      · rintro ⟨s, hsx⟩
        let s₀ : S := ⟨-b + s.1, by
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using s.2⟩
        refine ⟨s₀, ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsx ⊢
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsx
        convert hsx using 1
        all_goals
          simp only [s₀, vadd_eq_add]
          abel
      · rintro ⟨s, hsx⟩
        let s' : b +ᵥ S := ⟨b + s.1, by
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
            neg_add_cancel_left] using s.2⟩
        refine ⟨s', ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsx ⊢
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        convert hsx using 1
        all_goals
          simp only [s', vadd_eq_add]
          abel
    exact htarget.trans (hx.trans hunion.symm)

private theorem tilesOn_vadd_iff
    (K : Tiling.AxisParallel.Region) (S D : Set Tiling.Plane)
    (a b : Tiling.Plane) :
    Tiling.AxisParallel.TilesOn K S D ↔
      Tiling.AxisParallel.TilesOn (vaddRegion K a) (b +ᵥ S) ((a + b) +ᵥ D) := by
  constructor
  · exact tilesOn_vadd K S D a b
  · intro h
    have hback := tilesOn_vadd (vaddRegion K a) (b +ᵥ S) ((a + b) +ᵥ D)
      (-a) (-b) h
    rw [vaddRegion_neg_vadd, vadd_neg_vadd_set, add_vadd_set,
      show -a + -b + (a + b) = 0 by abel, zero_vadd] at hback
    exact hback

/-- Translate a tile, its centres, and its target so that a chosen vertex and centre are zero. -/
theorem normalizeApproximationContext.{u}
    (K : Tiling.AxisParallel.Region) (T E : Set Tiling.Plane)
    (v₀ : Tiling.Plane) (hv₀ : v₀ ∈ K.vertices)
    (t₀ : Tiling.Plane) (ht₀ : t₀ ∈ T) :
    ∃ C : ApproximationContext.{u},
      C.region.openCarrier = (-v₀) +ᵥ K.openCarrier ∧
      C.centres = (-t₀) +ᵥ T ∧
      C.target = (-(v₀ + t₀)) +ᵥ E ∧
      (Tiling.AxisParallel.TilesOn K T E ↔
        Tiling.AxisParallel.TilesOn C.region C.centres C.target) := by
  let K' := vaddRegion K (-v₀)
  let T' := (-t₀) +ᵥ T
  let E' := (-(v₀ + t₀)) +ᵥ E
  have hzeroVertices : (0 : Tiling.Plane) ∈ K'.vertices := by
    rw [show K'.vertices = (-v₀) +ᵥ K.vertices by
      exact Region.vadd_vertices K (-v₀)]
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, zero_vadd,
      vadd_eq_add, add_zero] using hv₀
  have hzeroCentres : (0 : Tiling.Plane) ∈ T' := by
    simpa only [T', Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, zero_vadd,
      vadd_eq_add, add_zero] using ht₀
  let V : Submodule ℚ ℝ := Submodule.span ℚ
    {r : ℝ | ∃ (axis : Tiling.AxisParallel.Axis) (a b : Tiling.Plane),
      (∃ v ∈ K'.vertices, ∃ t ∈ T', a = v + t) ∧
      (∃ v ∈ K'.vertices, ∃ t ∈ T', b = v + t) ∧
      r = Tiling.AxisParallel.Axis.coord axis (a - b)}
  have vertex_re_mem : ∀ v ∈ K'.vertices, v.re ∈ V := by
    intro v hv
    apply Submodule.subset_span
    refine ⟨Tiling.AxisParallel.Axis.horizontal, v, 0, ?_, ?_, ?_⟩
    · exact ⟨v, hv, 0, hzeroCentres, by simp⟩
    · exact ⟨0, hzeroVertices, 0, hzeroCentres, by simp⟩
    · simp [Tiling.AxisParallel.Axis.coord]
  have vertex_im_mem : ∀ v ∈ K'.vertices, v.im ∈ V := by
    intro v hv
    apply Submodule.subset_span
    refine ⟨Tiling.AxisParallel.Axis.vertical, v, 0, ?_, ?_, ?_⟩
    · exact ⟨v, hv, 0, hzeroCentres, by simp⟩
    · exact ⟨0, hzeroVertices, 0, hzeroCentres, by simp⟩
    · simp [Tiling.AxisParallel.Axis.coord]
  have centre_re_mem : ∀ t ∈ T', t.re ∈ V := by
    intro t ht
    apply Submodule.subset_span
    refine ⟨Tiling.AxisParallel.Axis.horizontal, t, 0, ?_, ?_, ?_⟩
    · exact ⟨0, hzeroVertices, t, ht, by simp⟩
    · exact ⟨0, hzeroVertices, 0, hzeroCentres, by simp⟩
    · simp [Tiling.AxisParallel.Axis.coord]
  have centre_im_mem : ∀ t ∈ T', t.im ∈ V := by
    intro t ht
    apply Submodule.subset_span
    refine ⟨Tiling.AxisParallel.Axis.vertical, t, 0, ?_, ?_, ?_⟩
    · exact ⟨0, hzeroVertices, t, ht, by simp⟩
    · exact ⟨0, hzeroVertices, 0, hzeroCentres, by simp⟩
    · simp [Tiling.AxisParallel.Axis.coord]
  let C : ApproximationContext.{u} := {
    region := K'
    centres := T'
    target := E'
    zero_mem_vertices := hzeroVertices
    zero_mem_centres := hzeroCentres
    coordinateSpace := V
    basisIndex := ULift.{u} (Module.Free.ChooseBasisIndex ℚ V)
    basis := (Module.Free.chooseBasis ℚ V).reindex Equiv.ulift.symm
    coordinateSpace_eq_span := rfl
    vertex_re_mem := vertex_re_mem
    vertex_im_mem := vertex_im_mem
    centre_re_mem := centre_re_mem
    centre_im_mem := centre_im_mem }
  refine ⟨C, ?_, rfl, rfl, ?_⟩
  · exact Region.vadd_openCarrier K (-v₀)
  · have h := tilesOn_vadd_iff K T E (-v₀) (-t₀)
    have hab : -v₀ + -t₀ = -(v₀ + t₀) := by abel
    simpa only [C, K', T', E', hab] using h

private def basisWeight (C : ApproximationContext) (z : C.coordinateSpace) : ℝ :=
  ∑ j ∈ (C.basis.repr z).support, |((C.basis.repr z j) : ℝ)|

private theorem basisWeight_nonneg (C : ApproximationContext) (z : C.coordinateSpace) :
    0 ≤ basisWeight C z := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

private theorem mapScalar_sub_eq_sum
    (C : ApproximationContext) (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (z : C.coordinateSpace) :
    mapScalar φ z - (z : ℝ) =
      ∑ j ∈ (C.basis.repr z).support,
        ((C.basis.repr z j) : ℝ) *
          (mapScalar φ (C.basis j) - ((C.basis j : C.coordinateSpace) : ℝ)) := by
  have hz :
      ∑ j ∈ (C.basis.repr z).support, (C.basis.repr z j) • C.basis j = z := by
    simpa only [C.basis.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum] using
      C.basis.repr.symm_apply_apply z
  have hφrat := congrArg φ hz
  have hcoe := congrArg (fun w : C.coordinateSpace ↦ (w : ℝ)) hz
  have hφ :
      ((φ z) : ℝ) = ∑ j ∈ (C.basis.repr z).support,
        ((C.basis.repr z j) : ℝ) * ((φ (C.basis j)) : ℝ) := by
    rw [← hφrat]
    simp only [map_sum, LinearMap.map_smul_of_tower, Rat.smul_def, Rat.cast_sum,
      Rat.cast_mul, Rat.cast_id]
  have hval :
      (z : ℝ) = ∑ j ∈ (C.basis.repr z).support,
        ((C.basis.repr z j) : ℝ) * ((C.basis j : C.coordinateSpace) : ℝ) := by
    rw [← hcoe]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Rat.smul_def]
  simp only [mapScalar]
  rw [hφ, hval]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

private theorem exists_epsilonApproximation_of_one_not_mem
    (C : ApproximationContext) (ε : ℝ) (hε : 0 < ε)
    (hone : (1 : ℝ) ∉ C.coordinateSpace) :
    ∃ φ : C.coordinateSpace →ₗ[ℚ] ℚ, IsEpsilonApproximation C ε φ := by
  choose f hf using fun j : C.basisIndex ↦
    exists_rat_near (((C.basis j : C.coordinateSpace) : ℝ)) hε
  let φ : C.coordinateSpace →ₗ[ℚ] ℚ := C.basis.constr ℚ f
  refine ⟨φ, ⟨hε, ?_, ?_⟩⟩
  · intro q hq
    by_cases hq0 : q = 0
    · subst q
      have hzero : (⟨(((0 : ℚ) : ℝ)), hq⟩ : C.coordinateSpace) = 0 := by
        apply Subtype.ext
        norm_num
      rw [hzero]
      exact map_zero φ
    · exfalso
      apply hone
      have hscaled := C.coordinateSpace.smul_mem q⁻¹ hq
      simpa [Rat.smul_def, hq0] using hscaled
  · intro j
    simpa only [φ, C.basis.constr_basis, abs_sub_comm] using hf j

theorem exists_epsilonApproximation (C : ApproximationContext) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : C.coordinateSpace →ₗ[ℚ] ℚ, IsEpsilonApproximation C ε φ := by
  classical
  by_cases hone : (1 : ℝ) ∈ C.coordinateSpace
  · let one : C.coordinateSpace := ⟨1, hone⟩
    let r := C.basis.repr one
    have hone0 : one ≠ 0 := by
      intro h
      have := congrArg Subtype.val h
      norm_num [one] at this
    have hr0 : r ≠ 0 := by
      intro h
      apply hone0
      apply C.basis.repr.injective
      simpa only [r, map_zero] using h
    have hrsupp : r.support.Nonempty := Finsupp.support_nonempty_iff.mpr hr0
    obtain ⟨j₀, hj₀⟩ := hrsupp
    have hc : r j₀ ≠ 0 := Finsupp.mem_support_iff.mp hj₀
    let S : ℝ := ∑ j ∈ r.support.erase j₀, |((r j) : ℝ)|
    have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    let R : ℝ := ε * |((r j₀) : ℝ)| / (S + 1)
    let δ : ℝ := min ε R / 2
    have hcR : ((r j₀ : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hc
    have hR : 0 < R := by
      exact div_pos (mul_pos hε (abs_pos.mpr hcR)) (by linarith)
    have hδ : 0 < δ := div_pos (lt_min hε hR) (by norm_num)
    choose g hg using fun j : C.basisIndex ↦
      exists_rat_near (((C.basis j : C.coordinateSpace) : ℝ)) hδ
    let A : ℚ := ∑ j ∈ r.support.erase j₀, r j * g j
    let f : C.basisIndex → ℚ := fun j ↦
      if j = j₀ then (r j₀)⁻¹ * (1 - A) else g j
    let φ : C.coordinateSpace →ₗ[ℚ] ℚ := C.basis.constr ℚ f
    have hφone : φ one = 1 := by
      simp only [φ, C.basis.constr_apply, Finsupp.sum]
      change ∑ x ∈ r.support, r x * f x = 1
      rw [← Finset.sum_erase_add _ _ hj₀]
      have herase : ∑ x ∈ r.support.erase j₀, r x * f x = A := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxne : x ≠ j₀ := (Finset.mem_erase.mp hx).1
        simp only [f, if_neg hxne, A]
      rw [herase]
      simp only [f, if_pos]
      have hinv : r j₀ * (r j₀)⁻¹ = 1 := by exact mul_inv_cancel₀ hc
      calc
        A + r j₀ * ((r j₀)⁻¹ * (1 - A)) =
            A + (r j₀ * (r j₀)⁻¹) * (1 - A) := by ring
        _ = 1 := by rw [hinv]; ring
    refine ⟨φ, ⟨hε, ?_, ?_⟩⟩
    · intro q hq
      have hqeq : (⟨(q : ℝ), hq⟩ : C.coordinateSpace) = q • one := by
        apply Subtype.ext
        simp [one, Rat.smul_def]
      rw [hqeq, map_smul, hφone]
      simp
    · intro j
      simp only [φ, C.basis.constr_basis]
      by_cases hj : j = j₀
      · subst j
        simp only [f, if_pos]
        have honeExpansion :
            (1 : ℝ) = ∑ j ∈ r.support,
              ((r j) : ℝ) * ((C.basis j : C.coordinateSpace) : ℝ) := by
          have hrrepr :
              ∑ j ∈ r.support, (r j) • C.basis j = one := by
            simpa only [r, C.basis.repr_symm_apply, Finsupp.linearCombination_apply,
              Finsupp.sum] using C.basis.repr.symm_apply_apply one
          have := congrArg (fun z : C.coordinateSpace ↦ (z : ℝ)) hrrepr
          simpa only [one, Submodule.coe_sum, Submodule.coe_smul_of_tower,
            Rat.smul_def] using this.symm
        have honeSplit :
            (1 : ℝ) = ((r j₀) : ℝ) * ((C.basis j₀ : C.coordinateSpace) : ℝ) +
              ∑ j ∈ r.support.erase j₀,
                ((r j) : ℝ) * ((C.basis j : C.coordinateSpace) : ℝ) := by
          rw [← Finset.sum_erase_add _ _ hj₀] at honeExpansion
          linarith
        let B : ℝ := ∑ j ∈ r.support.erase j₀,
          ((r j) : ℝ) * ((C.basis j : C.coordinateSpace) : ℝ)
        let G : ℝ := ∑ j ∈ r.support.erase j₀,
          ((r j) : ℝ) * ((g j) : ℝ)
        change (1 : ℝ) = ((r j₀) : ℝ) *
          ((C.basis j₀ : C.coordinateSpace) : ℝ) + B at honeSplit
        have hcastA : ((A : ℚ) : ℝ) = G := by
          simp only [A, G, Rat.cast_sum, Rat.cast_mul]
        have hpivot :
            (((r j₀)⁻¹ * (1 - A) : ℚ) : ℝ) -
                ((C.basis j₀ : C.coordinateSpace) : ℝ) =
              (((r j₀ : ℚ) : ℝ))⁻¹ * (B - G) := by
          rw [Rat.cast_mul, Rat.cast_inv, Rat.cast_sub, Rat.cast_one, hcastA]
          field_simp [hcR]
          nlinarith
        rw [hpivot, abs_mul]
        have hsum : |B - G| ≤ S * δ := by
          have hBG : B - G = ∑ j ∈ r.support.erase j₀,
              ((r j) : ℝ) *
                (((C.basis j : C.coordinateSpace) : ℝ) - ((g j) : ℝ)) := by
            simp only [B, G]
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib]
          rw [hBG]
          calc
            |∑ j ∈ r.support.erase j₀,
                ((r j) : ℝ) *
                  (((C.basis j : C.coordinateSpace) : ℝ) - ((g j) : ℝ))|
                ≤ ∑ j ∈ r.support.erase j₀,
                  |((r j) : ℝ) *
                    (((C.basis j : C.coordinateSpace) : ℝ) - ((g j) : ℝ))| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ j ∈ r.support.erase j₀, |((r j) : ℝ)| * δ := by
              apply Finset.sum_le_sum
              intro k hk
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (le_of_lt (hg k)) (abs_nonneg _)
            _ = S * δ := by simp only [S, Finset.sum_mul]
        have hInvAbs : |(((r j₀ : ℚ) : ℝ))⁻¹| = |((r j₀) : ℝ)|⁻¹ :=
          abs_inv _
        rw [hInvAbs]
        calc
          |((r j₀) : ℝ)|⁻¹ * |B - G| ≤ |((r j₀) : ℝ)|⁻¹ * (S * δ) :=
            mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (abs_nonneg _))
          _ < ε := by
            have hcabs : 0 < |((r j₀) : ℝ)| := abs_pos.mpr hcR
            have hδR : δ < R := by
              dsimp [δ]
              have hminle : min ε R ≤ R := min_le_right _ _
              linarith
            calc
              |((r j₀) : ℝ)|⁻¹ * (S * δ) ≤
                  |((r j₀) : ℝ)|⁻¹ * ((S + 1) * δ) := by
                    gcongr
                    nlinarith
              _ < |((r j₀) : ℝ)|⁻¹ * ((S + 1) * R) := by
                    gcongr
              _ = ε := by
                    dsimp [R]
                    field_simp [ne_of_gt hcabs, show S + 1 ≠ 0 by linarith]
      · simp only [f, if_neg hj]
        have hδε : δ < ε := by
          dsimp [δ]
          have hminle : min ε R ≤ ε := min_le_left _ _
          linarith
        exact lt_trans (by simpa only [abs_sub_comm] using hg j) hδε
  · exact exists_epsilonApproximation_of_one_not_mem C ε hε hone

private def finiteVertexDifferenceScalar (C : ApproximationContext)
    (axis : Tiling.AxisParallel.Axis)
    (v w : {x : Tiling.Plane // x ∈ C.region.vertexFinset}) : C.coordinateSpace := by
  have hv : (v : Tiling.Plane) ∈ C.region.vertices := by
    rw [← C.region.coe_vertexFinset]
    exact v.2
  have hw : (w : Tiling.Plane) ∈ C.region.vertices := by
    rw [← C.region.coe_vertexFinset]
    exact w.2
  cases axis with
  | horizontal =>
      exact ⟨v.1.re - w.1.re, C.coordinateSpace.sub_mem
        (C.vertex_re_mem v hv) (C.vertex_re_mem w hw)⟩
  | vertical =>
      exact ⟨v.1.im - w.1.im, C.coordinateSpace.sub_mem
        (C.vertex_im_mem v hv) (C.vertex_im_mem w hw)⟩

/-- Basiswise approximation controls every prescribed finite set uniformly. -/
theorem approximation_uniformOn_finset (C : ApproximationContext)
    (Z : Finset C.coordinateSpace) (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (φ : C.coordinateSpace →ₗ[ℚ] ℚ),
      IsEpsilonApproximation C ε₀ φ →
      ∀ z ∈ Z, |mapScalar φ z - (z : ℝ)| < η := by
  let B : ℝ := ∑ z ∈ Z, basisWeight C z
  let ε₀ : ℝ := η / (B + 1)
  have hB : 0 ≤ B := by
    exact Finset.sum_nonneg fun z _ ↦ basisWeight_nonneg C z
  have hden : 0 < B + 1 := by linarith
  have hε₀ : 0 < ε₀ := div_pos hη hden
  refine ⟨ε₀, hε₀, ?_⟩
  intro φ hφ z hz
  have hweight : basisWeight C z ≤ B := by
    exact Finset.single_le_sum (fun w _ ↦ basisWeight_nonneg C w) hz
  have hmul : basisWeight C z * ε₀ < η := by
    have hlt : basisWeight C z < B + 1 := lt_of_le_of_lt hweight (by linarith)
    have := mul_lt_mul_of_pos_right hlt hε₀
    have heq : (B + 1) * ε₀ = η := by
      dsimp [ε₀]
      field_simp
    linarith
  rw [mapScalar_sub_eq_sum]
  calc
    |∑ j ∈ (C.basis.repr z).support,
        ((C.basis.repr z j) : ℝ) *
          (mapScalar φ (C.basis j) - ((C.basis j : C.coordinateSpace) : ℝ))|
        ≤ ∑ j ∈ (C.basis.repr z).support,
            |((C.basis.repr z j) : ℝ) *
              (mapScalar φ (C.basis j) - ((C.basis j : C.coordinateSpace) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ (C.basis.repr z).support,
          |((C.basis.repr z j) : ℝ)| * ε₀ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (le_of_lt (hφ.basis_close j)) (abs_nonneg _)
    _ = basisWeight C z * ε₀ := by
      simp only [basisWeight, Finset.sum_mul]
    _ < η := hmul

/-- On a finite scalar alphabet, sufficiently fine approximations preserve signs. -/
theorem approximation_preservesSign_finset (C : ApproximationContext)
    (Z : Finset C.coordinateSpace) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (φ : C.coordinateSpace →ₗ[ℚ] ℚ),
      IsEpsilonApproximation C ε₀ φ →
      ∀ z ∈ Z, Real.sign (mapScalar φ z) = Real.sign (z : ℝ) := by
  classical
  let Z' := Z.filter fun z ↦ z ≠ 0
  by_cases hZ' : Z' = ∅
  · refine ⟨1, zero_lt_one, ?_⟩
    intro φ hφ z hz
    have hz0 : z = 0 := by
      by_contra hnz
      have : z ∈ Z' := Finset.mem_filter.mpr ⟨hz, hnz⟩
      rw [hZ'] at this
      simp at this
    subst z
    simp [mapScalar]
  · have hnonempty : (Z'.image fun z : C.coordinateSpace ↦ |(z : ℝ)|).Nonempty := by
      simpa only [Finset.image_nonempty] using (Finset.nonempty_iff_ne_empty.mpr hZ')
    let δ : ℝ := (Z'.image fun z : C.coordinateSpace ↦ |(z : ℝ)|).min' hnonempty
    have hδ : 0 < δ := by
      have hmem := Finset.min'_mem
        (Z'.image fun z : C.coordinateSpace ↦ |(z : ℝ)|) hnonempty
      obtain ⟨z, hz, hzval⟩ := Finset.mem_image.mp hmem
      dsimp [δ]
      rw [← hzval]
      exact abs_pos.mpr (by
        intro h
        exact (Finset.mem_filter.mp hz).2 (Subtype.ext h))
    obtain ⟨ε₀, hε₀, hcontrol⟩ :=
      approximation_uniformOn_finset C Z (δ / 2) (half_pos hδ)
    refine ⟨ε₀, hε₀, ?_⟩
    intro φ hφ z hz
    by_cases hz0 : z = 0
    · subst z
      simp [mapScalar]
    · have hz' : z ∈ Z' := Finset.mem_filter.mpr ⟨hz, hz0⟩
      have hδle : δ ≤ |(z : ℝ)| := by
        exact Finset.min'_le _ _
          (Finset.mem_image.mpr ⟨z, hz', rfl⟩)
      have herr := hcontrol φ hφ z hz
      have hz0' : (z : ℝ) ≠ 0 := fun h ↦ hz0 (Subtype.ext h)
      rcases lt_or_gt_of_ne hz0' with hzneg | hzpos
      · have habsz : |(z : ℝ)| = -(z : ℝ) := abs_of_neg hzneg
        have hub := (abs_lt.mp herr).2
        have hmneg : mapScalar φ z < 0 := by
          rw [habsz] at hδle
          linarith
        rw [Real.sign_of_neg hmneg, Real.sign_of_neg hzneg]
      · have habsz : |(z : ℝ)| = (z : ℝ) := abs_of_pos hzpos
        have hlb := (abs_lt.mp herr).1
        have hmpos : 0 < mapScalar φ z := by
          rw [habsz] at hδle
          linarith
        rw [Real.sign_of_pos hmpos, Real.sign_of_pos hzpos]

/-- Sign control on the finite vertex-difference alphabet is exactly goodness. -/
theorem isGoodApproximation_of_sufficientlyFine (C : ApproximationContext) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (φ : C.coordinateSpace →ₗ[ℚ] ℚ),
      IsEpsilonApproximation C ε₀ φ → IsGoodApproximation C φ := by
  classical
  let axes : Finset Tiling.AxisParallel.Axis :=
    {Tiling.AxisParallel.Axis.horizontal, Tiling.AxisParallel.Axis.vertical}
  let V := C.region.vertexFinset.attach
  let Z : Finset C.coordinateSpace := axes.biUnion fun axis ↦
    (V.product V).image fun vw ↦ finiteVertexDifferenceScalar C axis vw.1 vw.2
  obtain ⟨ε₀, hε₀, hsign⟩ := approximation_preservesSign_finset C Z
  refine ⟨ε₀, hε₀, ?_⟩
  intro φ hφ
  refine ⟨?_⟩
  intro axis v w hv hw
  let v' : {x : Tiling.Plane // x ∈ C.region.vertexFinset} := ⟨v, by
    have : v ∈ (C.region.vertexFinset : Set Tiling.Plane) := by
      rw [C.region.coe_vertexFinset]
      exact hv
    exact this⟩
  let w' : {x : Tiling.Plane // x ∈ C.region.vertexFinset} := ⟨w, by
    have : w ∈ (C.region.vertexFinset : Set Tiling.Plane) := by
      rw [C.region.coe_vertexFinset]
      exact hw
    exact this⟩
  have haxis : axis ∈ axes := by
    cases axis <;> simp [axes]
  have hv' : v' ∈ V := by simp [V, v']
  have hw' : w' ∈ V := by simp [V, w']
  have hz : finiteVertexDifferenceScalar C axis v' w' ∈ Z := by
    refine Finset.mem_biUnion.mpr ⟨axis, haxis, ?_⟩
    refine Finset.mem_image.mpr ⟨(v', w'), Finset.mem_product.mpr ⟨hv', hw'⟩, rfl⟩
  have hs := hsign φ hφ (finiteVertexDifferenceScalar C axis v' w') hz
  have hmap :
      mapScalar φ (finiteVertexDifferenceScalar C axis v' w') =
        Tiling.AxisParallel.Axis.coord axis
          (mapPoint φ (C.vertexPoint v hv) - mapPoint φ (C.vertexPoint w hw)) := by
    cases axis <;>
      simp only [finiteVertexDifferenceScalar, v', w', mapPoint,
        ApproximationContext.vertexPoint, Tiling.AxisParallel.Axis.coord, mapScalar,
        Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, add_zero, zero_add]
    all_goals
      norm_cast
      rw [← map_sub]
      rfl
  rw [hmap] at hs
  cases axis <;>
    simpa [finiteVertexDifferenceScalar, v', w', Tiling.AxisParallel.Axis.coord] using hs

end

end Tiling.AxisParallel.Approximation
