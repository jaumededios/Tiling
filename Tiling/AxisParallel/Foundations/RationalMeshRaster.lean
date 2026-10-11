import Tiling.AxisParallel.Foundations.RationalMeshCore
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.RationalPolygonal.DiscreteCarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.RationalMesh

open Tiling.AxisParallel
open Tiling.AxisParallel.RationalMesh

private theorem rationalScale_re_eq (d : ℕ) (z : ZPlane) :
    (rationalScale d z).re = (z 0 : ℝ) / (d : ℝ) := by
  simp [rationalScale]

private theorem rationalScale_im_eq (d : ℕ) (z : ZPlane) :
    (rationalScale d z).im = (z 1 : ℝ) / (d : ℝ) := by
  simp [rationalScale]

private theorem floor_re_eq_of_mem_meshCell {d : ℕ} (hd : 0 < d)
    {z : ZPlane} {x : Tiling.Plane} (hx : x ∈ meshCell d z) :
    ⌊(d : ℝ) * x.re⌋ = z 0 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rcases hx with ⟨hxlo, hxhi, _, _⟩
  rw [rationalScale_re_eq] at hxlo hxhi
  have hlo : (z 0 : ℝ) < (d : ℝ) * x.re := by
    have := (div_lt_iff₀ hdR).mp hxlo
    simpa [mul_comm] using this
  have hhi : (d : ℝ) * x.re < (z 0 : ℝ) + 1 := by
    have hxhi' : x.re < ((z 0 : ℝ) + 1) / (d : ℝ) := by
      rw [add_div]
      simpa using hxhi
    have := (lt_div_iff₀ hdR).mp hxhi'
    simpa [mul_comm] using this
  exact Int.floor_eq_iff.mpr ⟨hlo.le, hhi⟩

private theorem floor_im_eq_of_mem_meshCell {d : ℕ} (hd : 0 < d)
    {z : ZPlane} {x : Tiling.Plane} (hx : x ∈ meshCell d z) :
    ⌊(d : ℝ) * x.im⌋ = z 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rcases hx with ⟨_, _, hxlo, hxhi⟩
  rw [rationalScale_im_eq] at hxlo hxhi
  have hlo : (z 1 : ℝ) < (d : ℝ) * x.im := by
    have := (div_lt_iff₀ hdR).mp hxlo
    simpa [mul_comm] using this
  have hhi : (d : ℝ) * x.im < (z 1 : ℝ) + 1 := by
    have hxhi' : x.im < ((z 1 : ℝ) + 1) / (d : ℝ) := by
      rw [add_div]
      simpa using hxhi
    have := (lt_div_iff₀ hdR).mp hxhi'
    simpa [mul_comm] using this
  exact Int.floor_eq_iff.mpr ⟨hlo.le, hhi⟩

theorem rationalScale_injective :
  ∀ {d : ℕ}, 0 < d → Function.Injective (rationalScale d) := by
  intro d hd z w hzw
  funext i
  fin_cases i
  · have h := congrArg Complex.re hzw
    simp only [rationalScale] at h
    change (((z 0 : ℤ) : ℚ) / (d : ℚ) : ℝ) =
      (((w 0 : ℤ) : ℚ) / (d : ℚ) : ℝ) at h
    have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
    field_simp [hdr] at h
    exact_mod_cast h
  · have h := congrArg Complex.im hzw
    simp only [rationalScale] at h
    change (((z 1 : ℤ) : ℚ) / (d : ℚ) : ℝ) =
      (((w 1 : ℤ) : ℚ) / (d : ℚ) : ℝ) at h
    have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
    field_simp [hdr] at h
    exact_mod_cast h

theorem rationalScale_add :
  ∀ {d : ℕ}, 0 < d → ∀ z a : ZPlane,
    rationalScale d (z + a) = rationalScale d z + rationalScale d a := by
  intro d _hd z a
  apply Complex.ext
  · simp only [rationalScale, Pi.add_apply, Complex.add_re]
    push_cast
    ring
  · simp only [rationalScale, Pi.add_apply, Complex.add_im]
    push_cast
    ring

theorem meshCell_nonempty :
  ∀ {d : ℕ}, 0 < d → ∀ z : ZPlane, (meshCell d z).Nonempty := by
  intro d hd z
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hw : (0 : ℝ) < 1 / d := one_div_pos.mpr hdR
  refine ⟨Complex.mk ((rationalScale d z).re + (1 / d : ℝ) / 2)
    ((rationalScale d z).im + (1 / d : ℝ) / 2), ?_⟩
  change (rationalScale d z).re < (rationalScale d z).re + (1 / d : ℝ) / 2 ∧
    (rationalScale d z).re + (1 / d : ℝ) / 2 <
      (rationalScale d z).re + (1 / d : ℝ) ∧
    (rationalScale d z).im < (rationalScale d z).im + (1 / d : ℝ) / 2 ∧
    (rationalScale d z).im + (1 / d : ℝ) / 2 <
      (rationalScale d z).im + (1 / d : ℝ)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem meshCell_pairwiseDisjoint :
  ∀ {d : ℕ}, 0 < d → Set.PairwiseDisjoint Set.univ (meshCell d) := by
  intro d hd z _hz w _hw hzw
  change Disjoint (meshCell d z) (meshCell d w)
  rw [Set.disjoint_left]
  intro x hxz hxw
  apply hzw
  funext i
  fin_cases i
  · exact (floor_re_eq_of_mem_meshCell hd hxz).symm.trans
      (floor_re_eq_of_mem_meshCell hd hxw)
  · exact (floor_im_eq_of_mem_meshCell hd hxz).symm.trans
      (floor_im_eq_of_mem_meshCell hd hxw)

theorem meshCell_add :
  ∀ {d : ℕ}, 0 < d → ∀ z a : ZPlane,
    meshCell d (z + a) = rationalScale d a +ᵥ meshCell d z := by
  intro d hd z a
  ext x
  simp only [meshCell, Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
    vadd_eq_add, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im]
  rw [rationalScale_add hd]
  simp only [Complex.add_re, Complex.add_im]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith

private theorem offMesh_existsUnique_meshCell :
  ∀ {d : ℕ}, 0 < d → ∀ x : Tiling.Plane,
    x ∉ meshLines d → ∃! z : ZPlane, x ∈ meshCell d z := by
  intro d hd x hx
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hxre : ∀ n : ℤ, x.re ≠ (((n : ℚ) / (d : ℚ)) : ℝ) := by
    intro n hn
    apply hx
    exact Or.inl ⟨n, hn⟩
  have hxim : ∀ n : ℤ, x.im ≠ (((n : ℚ) / (d : ℚ)) : ℝ) := by
    intro n hn
    apply hx
    exact Or.inr ⟨n, hn⟩
  let z : ZPlane := fun i =>
    if i = 0 then ⌊(d : ℝ) * x.re⌋ else ⌊(d : ℝ) * x.im⌋
  have hz0 : z 0 = ⌊(d : ℝ) * x.re⌋ := by simp [z]
  have hz1 : z 1 = ⌊(d : ℝ) * x.im⌋ := by simp [z]
  have hrelo_le : (z 0 : ℝ) / (d : ℝ) ≤ x.re := by
    apply (div_le_iff₀ hdR).2
    rw [hz0]
    simpa [mul_comm] using (Int.floor_le ((d : ℝ) * x.re))
  have hrelo : (z 0 : ℝ) / (d : ℝ) < x.re := by
    apply lt_of_le_of_ne hrelo_le
    intro heq
    apply hxre (z 0)
    rw [← heq]
    norm_num
  have hrehi : x.re < (z 0 : ℝ) / (d : ℝ) + 1 / (d : ℝ) := by
    rw [← add_div]
    apply (lt_div_iff₀ hdR).2
    rw [hz0]
    simp [mul_comm]
  have himlo_le : (z 1 : ℝ) / (d : ℝ) ≤ x.im := by
    apply (div_le_iff₀ hdR).2
    rw [hz1]
    simpa [mul_comm] using (Int.floor_le ((d : ℝ) * x.im))
  have himlo : (z 1 : ℝ) / (d : ℝ) < x.im := by
    apply lt_of_le_of_ne himlo_le
    intro heq
    apply hxim (z 1)
    rw [← heq]
    norm_num
  have himhi : x.im < (z 1 : ℝ) / (d : ℝ) + 1 / (d : ℝ) := by
    rw [← add_div]
    apply (lt_div_iff₀ hdR).2
    rw [hz1]
    simp [mul_comm]
  refine ⟨z, ?_, ?_⟩
  · change (rationalScale d z).re < x.re ∧
      x.re < (rationalScale d z).re + (1 / d : ℝ) ∧
      (rationalScale d z).im < x.im ∧
      x.im < (rationalScale d z).im + (1 / d : ℝ)
    rw [rationalScale_re_eq, rationalScale_im_eq]
    exact ⟨hrelo, hrehi, himlo, himhi⟩
  · intro w hw
    funext i
    fin_cases i
    · simpa [hz0] using (floor_re_eq_of_mem_meshCell hd hw).symm
    · simpa [hz1] using (floor_im_eq_of_mem_meshCell hd hw).symm

private theorem volume_re_eq_zero (c : ℝ) :
    volume {x : Tiling.Plane | x.re = c} = 0 := by
  have hset : {x : Tiling.Plane | x.re = c} =
      Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (Set.univ : Set ℝ)) := by
    ext x
    simp
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage]
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  · exact ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet

private theorem volume_im_eq_zero (c : ℝ) :
    volume {x : Tiling.Plane | x.im = c} = 0 := by
  have hset : {x : Tiling.Plane | x.im = c} =
      Complex.measurableEquivRealProd ⁻¹' ((Set.univ : Set ℝ) ×ˢ {c}) := by
    ext x
    simp
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage]
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  · exact (MeasurableSet.univ.prod (measurableSet_singleton c)).nullMeasurableSet

private theorem meshLines_volume_zero :
  ∀ {d : ℕ}, 0 < d → volume (meshLines d) = 0 := by
  intro d _hd
  have hlines : meshLines d =
      (⋃ n : ℤ, {x : Tiling.Plane | x.re = (((n : ℚ) / (d : ℚ)) : ℝ)}) ∪
        (⋃ n : ℤ, {x : Tiling.Plane | x.im = (((n : ℚ) / (d : ℚ)) : ℝ)}) := by
    ext x
    simp [meshLines]
  rw [hlines]
  rw [measure_union_null]
  · exact measure_iUnion_null fun n ↦ volume_re_eq_zero _
  · exact measure_iUnion_null fun n ↦ volume_im_eq_zero _

theorem isOpen_meshCell (d : ℕ) (z : ZPlane) : IsOpen (meshCell d z) := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

private theorem isOpen_rawCellUnion (d : ℕ) (A : Set ZPlane) :
    IsOpen (⋃ z : A, meshCell d z.1) := by
  exact isOpen_iUnion fun z ↦ isOpen_meshCell d z.1

private theorem offMesh_mem_regularizedCellUnion_iff :
  ∀ {d : ℕ}, 0 < d → ∀ (A : Set ZPlane) (x : Tiling.Plane),
    x ∉ meshLines d →
      (x ∈ regularizedCellUnion d A ↔
        ∃ z ∈ A, x ∈ meshCell d z) := by
  intro d hd A x hx
  let U : Set Tiling.Plane := ⋃ z : A, meshCell d z.1
  have hUopen : IsOpen U := isOpen_rawCellUnion d A
  constructor
  · intro hxreg
    rcases offMesh_existsUnique_meshCell hd x hx with ⟨z, hxz, _hzuniq⟩
    refine ⟨z, ?_, hxz⟩
    by_contra hzA
    have hxcl : x ∈ closure U := interior_subset hxreg
    rcases (mem_closure_iff.mp hxcl) (meshCell d z) (isOpen_meshCell d z) hxz with
      ⟨y, hyz, hyU⟩
    rcases Set.mem_iUnion.mp hyU with ⟨w, hyw⟩
    have hzw : z = w.1 := by
      funext i
      fin_cases i
      · exact (floor_re_eq_of_mem_meshCell hd hyz).symm.trans
          (floor_re_eq_of_mem_meshCell hd hyw)
      · exact (floor_im_eq_of_mem_meshCell hd hyz).symm.trans
          (floor_im_eq_of_mem_meshCell hd hyw)
    exact hzA (hzw ▸ w.2)
  · rintro ⟨z, hzA, hxz⟩
    change x ∈ interior (closure U)
    apply (hUopen.subset_interior_iff.mpr subset_closure)
    exact Set.mem_iUnion_of_mem ⟨z, hzA⟩ hxz

private theorem meshCell_disjoint_meshLines {d : ℕ} (hd : 0 < d)
    {z : ZPlane} {x : Tiling.Plane} (hx : x ∈ meshCell d z) :
    x ∉ meshLines d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  intro hline
  rcases hline with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hn' : x.re = (n : ℝ) / (d : ℝ) := by
      norm_num at hn ⊢
      exact hn
    rcases hx with ⟨hxlo, hxhi, _, _⟩
    rw [rationalScale_re_eq, hn'] at hxlo hxhi
    have hxhi' : (n : ℝ) / (d : ℝ) < ((z 0 : ℝ) + 1) / (d : ℝ) := by
      rw [add_div]
      exact hxhi
    have hloR : (z 0 : ℝ) < n := (div_lt_div_iff_of_pos_right hdR).mp hxlo
    have hhiR : (n : ℝ) < (z 0 : ℝ) + 1 :=
      (div_lt_div_iff_of_pos_right hdR).mp hxhi'
    have hlo : z 0 < n := by exact_mod_cast hloR
    have hhi : n < z 0 + 1 := by exact_mod_cast hhiR
    omega
  · have hn' : x.im = (n : ℝ) / (d : ℝ) := by
      norm_num at hn ⊢
      exact hn
    rcases hx with ⟨_, _, hxlo, hxhi⟩
    rw [rationalScale_im_eq, hn'] at hxlo hxhi
    have hxhi' : (n : ℝ) / (d : ℝ) < ((z 1 : ℝ) + 1) / (d : ℝ) := by
      rw [add_div]
      exact hxhi
    have hloR : (z 1 : ℝ) < n := (div_lt_div_iff_of_pos_right hdR).mp hxlo
    have hhiR : (n : ℝ) < (z 1 : ℝ) + 1 :=
      (div_lt_div_iff_of_pos_right hdR).mp hxhi'
    have hlo : z 1 < n := by exact_mod_cast hloR
    have hhi : n < z 1 + 1 := by exact_mod_cast hhiR
    omega

theorem meshCell_subset_regularizedCellUnion_iff :
  ∀ {d : ℕ}, 0 < d → ∀ (A : Set ZPlane) (z : ZPlane),
    meshCell d z ⊆ regularizedCellUnion d A ↔ z ∈ A := by
  intro d hd A z
  constructor
  · intro hsubset
    rcases meshCell_nonempty hd z with ⟨x, hxz⟩
    have hxoff := meshCell_disjoint_meshLines hd hxz
    rcases (offMesh_mem_regularizedCellUnion_iff hd A x hxoff).mp
      (hsubset hxz) with ⟨w, hwA, hxw⟩
    have hzw : z = w := by
      funext i
      fin_cases i
      · exact (floor_re_eq_of_mem_meshCell hd hxz).symm.trans
          (floor_re_eq_of_mem_meshCell hd hxw)
      · exact (floor_im_eq_of_mem_meshCell hd hxz).symm.trans
          (floor_im_eq_of_mem_meshCell hd hxw)
    exact hzw ▸ hwA
  · intro hzA x hxz
    exact (offMesh_mem_regularizedCellUnion_iff hd A x
      (meshCell_disjoint_meshLines hd hxz)).mpr ⟨z, hzA, hxz⟩

private theorem rawCellUnion_aeEq_regularizedCellUnion :
  ∀ {d : ℕ}, 0 < d → ∀ A : Set ZPlane,
    (⋃ z : A, meshCell d z.1) =ᵐ[volume] regularizedCellUnion d A := by
  intro d hd A
  apply ae_iff.mpr
  apply measure_mono_null _ (meshLines_volume_zero hd)
  intro x hx
  by_contra hxline
  apply hx
  apply propext
  change (x ∈ ⋃ z : A, meshCell d z.1) ↔ x ∈ regularizedCellUnion d A
  rw [offMesh_mem_regularizedCellUnion_iff hd A x hxline]
  simp

private theorem region_frontier_subset_meshLines :
  ∀ {K : Region} {d : ℕ}, 0 < d →
    OnRationalMesh d K.vertices →
      frontier K.openCarrier ⊆ meshLines d := by
  intro K d _hd hmesh x hx
  rw [K.frontier_openCarrier_eq_frontier_support] at hx
  rcases Tiling.AxisParallel.IntrinsicVertices.frontier_subset_vertexCoordinateGrid K hx with
    ⟨v, hv, hxv⟩ | ⟨v, hv, hxv⟩
  · rcases hmesh hv with ⟨z, hz⟩
    left
    refine ⟨z 0, ?_⟩
    calc
      x.re = v.re := hxv
      _ = (rationalScale d z).re := congrArg Complex.re hz.symm
      _ = _ := rfl
  · rcases hmesh hv with ⟨z, hz⟩
    right
    refine ⟨z 1, ?_⟩
    calc
      x.im = v.im := hxv
      _ = (rationalScale d z).im := congrArg Complex.im hz.symm
      _ = _ := rfl


private theorem tiledTarget_frontier_subset_meshLines :
  ∀ {K : Region} {T E : Set Tiling.Plane} {d : ℕ},
    0 < d → OnRationalMesh d K.vertices → OnRationalMesh d T →
    IsOpen E → interior (closure E) = E → TilesOn K T E →
      frontier E ⊆ meshLines d := by
  intro K T E d hd hK hT hEopen hEregular htiles x hx
  have hsupport : regularSupport K T = E :=
    regularSupport_eq_of_tilesOn hEopen hEregular htiles
  rw [← hsupport] at hx
  have hxfrontClosure : x ∈ frontier (closure (openUnion K T)) :=
    frontier_interior_subset hx
  have hclosure := closure_openUnion_eq_iUnion_support htiles.2.1
  let C : Set Tiling.Plane := ⋃ t : T, (t : Tiling.Plane) +ᵥ K.support
  have hCclosed : IsClosed C := by
    change IsClosed (⋃ t : T, (t : Tiling.Plane) +ᵥ K.support)
    rw [← hclosure]
    exact isClosed_closure
  have hxfrontC : x ∈ frontier C := by
    simpa only [C, hclosure] using hxfrontClosure
  have hxC : x ∈ C := hCclosed.frontier_subset hxfrontC
  rcases Set.mem_iUnion.mp hxC with ⟨t, hxt⟩
  have hxnotInteriorC : x ∉ interior C :=
    (mem_frontier_iff_notMem_interior hxC).mp hxfrontC
  have hxfrontTile : x ∈ frontier ((t : Tiling.Plane) +ᵥ K.support) := by
    apply (mem_frontier_iff_notMem_interior hxt).mpr
    intro hxint
    apply hxnotInteriorC
    exact interior_mono (Set.subset_iUnion (fun t : T ↦
      (t : Tiling.Plane) +ᵥ K.support) t) hxint
  rw [Tiling.AxisParallel.frontier_vadd_eq] at hxfrontTile
  have hxsource : x - (t : Tiling.Plane) ∈ frontier K.openCarrier := by
    rw [K.frontier_openCarrier_eq_frontier_support]
    simpa only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hxfrontTile
  have hxsourceLine := region_frontier_subset_meshLines hd hK hxsource
  rcases hT t.2 with ⟨a, ha⟩
  rcases hxsourceLine with ⟨n, hn⟩ | ⟨n, hn⟩
  · left
    refine ⟨n + a 0, ?_⟩
    have htre : (t : Tiling.Plane).re = (a 0 : ℝ) / (d : ℝ) := by
      calc
        (t : Tiling.Plane).re = (rationalScale d a).re :=
          congrArg Complex.re ha.symm
        _ = _ := rationalScale_re_eq d a
    have hn' : (x - (t : Tiling.Plane)).re = (n : ℝ) / (d : ℝ) := by
      norm_num at hn ⊢
      exact hn
    norm_num at ⊢
    simp only [Complex.sub_re] at hn'
    have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
    field_simp [hdne] at htre hn' ⊢
    linarith
  · right
    refine ⟨n + a 1, ?_⟩
    have htim : (t : Tiling.Plane).im = (a 1 : ℝ) / (d : ℝ) := by
      calc
        (t : Tiling.Plane).im = (rationalScale d a).im :=
          congrArg Complex.im ha.symm
        _ = _ := rationalScale_im_eq d a
    have hn' : (x - (t : Tiling.Plane)).im = (n : ℝ) / (d : ℝ) := by
      norm_num at hn ⊢
      exact hn
    norm_num at ⊢
    simp only [Complex.sub_im] at hn'
    have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
    field_simp [hdne] at htim hn' ⊢
    linarith

theorem frontier_regularizedCellUnion_subset_meshLines :
  ∀ {d : ℕ}, 0 < d → ∀ A : Set ZPlane,
    frontier (regularizedCellUnion d A) ⊆ meshLines d := by
  intro d hd A x hxfront
  by_contra hxoff
  rcases offMesh_existsUnique_meshCell hd x hxoff with ⟨z, hxz, _⟩
  by_cases hzA : z ∈ A
  · have hxreg : x ∈ regularizedCellUnion d A :=
      (meshCell_subset_regularizedCellUnion_iff hd A z).mpr hzA hxz
    have hxint : x ∈ interior (regularizedCellUnion d A) :=
      (subset_interior_iff_isOpen.mpr isOpen_interior) hxreg
    exact hxfront.2 hxint
  · have hxcl : x ∈ closure (regularizedCellUnion d A) := hxfront.1
    rcases (mem_closure_iff.mp hxcl) (meshCell d z) (isOpen_meshCell d z) hxz with
      ⟨y, hyz, hyreg⟩
    have hyoff := meshCell_disjoint_meshLines hd hyz
    rcases (offMesh_mem_regularizedCellUnion_iff hd A y hyoff).mp hyreg with
      ⟨w, hwA, hyw⟩
    have hzw : z = w := by
      funext i
      fin_cases i
      · exact (floor_re_eq_of_mem_meshCell hd hyz).symm.trans
          (floor_re_eq_of_mem_meshCell hd hyw)
      · exact (floor_im_eq_of_mem_meshCell hd hyz).symm.trans
          (floor_im_eq_of_mem_meshCell hd hyw)
    exact hzA (hzw ▸ hwA)

private theorem convex_meshCell (d : ℕ) (z : ZPlane) :
    Convex ℝ (meshCell d z) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx₁, hx₂, hx₃, hx₄⟩
  rcases hy with ⟨hy₁, hy₂, hy₃, hy₄⟩
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    subst a
    subst b
    simpa using ⟨hy₁, hy₂, hy₃, hy₄⟩
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  change (rationalScale d z).re < (a • x + b • y).re ∧
    (a • x + b • y).re < (rationalScale d z).re + 1 / (d : ℝ) ∧
    (rationalScale d z).im < (a • x + b • y).im ∧
    (a • x + b • y).im < (rationalScale d z).im + 1 / (d : ℝ)
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    smul_eq_mul]
  constructor
  · have h := add_lt_add_of_lt_of_le
      (mul_lt_mul_of_pos_left hx₁ ha')
      (mul_le_mul_of_nonneg_left hy₁.le hb)
    simpa [← add_mul, hab] using h
  constructor
  · have h := add_lt_add_of_lt_of_le
      (mul_lt_mul_of_pos_left hx₂ ha')
      (mul_le_mul_of_nonneg_left hy₂.le hb)
    simpa [← add_mul, hab] using h
  constructor
  · have h := add_lt_add_of_lt_of_le
      (mul_lt_mul_of_pos_left hx₃ ha')
      (mul_le_mul_of_nonneg_left hy₃.le hb)
    simpa [← add_mul, hab] using h
  · have h := add_lt_add_of_lt_of_le
      (mul_lt_mul_of_pos_left hx₄ ha')
      (mul_le_mul_of_nonneg_left hy₄.le hb)
    simpa [← add_mul, hab] using h

theorem target_cells_constant :
  ∀ {K : Region} {T E : Set Tiling.Plane} {d : ℕ},
    0 < d → OnRationalMesh d K.vertices → OnRationalMesh d T →
    IsOpen E → interior (closure E) = E → TilesOn K T E →
    ∀ z : ZPlane, meshCell d z ⊆ E ∨ Disjoint (meshCell d z) E := by
  intro K T E d hd hK hT hEopen hEregular htiles z
  have hfront : frontier E ⊆ meshLines d :=
    tiledTarget_frontier_subset_meshLines hd hK hT
      hEopen hEregular htiles
  have hcover : meshCell d z ⊆ E ∪ (closure E)ᶜ := by
    intro x hxcell
    have hxnotFrontier : x ∉ frontier E := by
      intro hxfront
      exact meshCell_disjoint_meshLines hd hxcell (hfront hxfront)
    by_cases hxcl : x ∈ closure E
    · left
      have hxint : x ∈ interior E := by
        by_contra hxnotint
        exact hxnotFrontier ⟨hxcl, hxnotint⟩
      simpa only [hEopen.interior_eq] using hxint
    · exact Or.inr hxcl
  rcases (convex_meshCell d z).isPreconnected.subset_or_subset
      hEopen isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) hcover with
    hsub | hsub
  · exact Or.inl hsub
  · right
    rw [Set.disjoint_left]
    intro x hxcell hxE
    exact hsub hxcell (subset_closure hxE)

theorem target_eq_regularizedRaster :
  ∀ {K : Region} {T E : Set Tiling.Plane} {d : ℕ},
    0 < d → OnRationalMesh d K.vertices → OnRationalMesh d T →
    IsOpen E → interior (closure E) = E → TilesOn K T E →
    E = regularizedCellUnion d (rasterCells d E) := by
  intro K T E d hd hK hT hEopen hEregular htiles
  let A : Set ZPlane := rasterCells d E
  let U : Set Tiling.Plane := ⋃ z : A, meshCell d z.1
  have hconstant := target_cells_constant hd hK hT
    hEopen hEregular htiles
  have hUE : U =ᵐ[volume] E := by
    apply ae_iff.mpr
    apply measure_mono_null _ (meshLines_volume_zero hd)
    intro x hxneq
    by_contra hxline
    apply hxneq
    apply propext
    change (x ∈ U) ↔ x ∈ E
    constructor
    · intro hxU
      rcases Set.mem_iUnion.mp hxU with ⟨z, hxz⟩
      exact z.2 hxz
    · intro hxE
      rcases offMesh_existsUnique_meshCell hd x hxline with ⟨z, hxz, _⟩
      have hzsubset : meshCell d z ⊆ E := by
        rcases hconstant z with hsub | hdisj
        · exact hsub
        · exact False.elim (Set.disjoint_left.mp hdisj hxz hxE)
      exact Set.mem_iUnion_of_mem ⟨z, hzsubset⟩ hxz
  have hUreg : U =ᵐ[volume] regularizedCellUnion d A :=
    rawCellUnion_aeEq_regularizedCellUnion hd A
  apply regularOpen_eq_of_aeEq hEopen hEregular isOpen_interior
  · simp
  · exact hUE.symm.trans hUreg

private theorem rasterCells_finite {K : Region} {d : ℕ} (hd : 0 < d) :
    (rasterCells d K.openCarrier).Finite := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
  obtain ⟨C, hC⟩ := K.isPolygonal.isCompact.isBounded.exists_norm_le
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((d : ℝ) * C + 1)
  let B : Set (ℤ × ℤ) := Set.Icc (-(N : ℤ)) (N : ℤ) ×ˢ
    Set.Icc (-(N : ℤ)) (N : ℤ)
  have hBfinite : B.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  let e : ZPlane → ℤ × ℤ := fun z ↦ (z 0, z 1)
  have he : Function.Injective e := by
    intro z w hzw
    funext i
    fin_cases i
    · exact congrArg Prod.fst hzw
    · exact congrArg Prod.snd hzw
  apply (hBfinite.preimage he.injOn).subset
  intro z hz
  let x : Tiling.Plane := Complex.mk
    ((rationalScale d z).re + (1 / d : ℝ) / 2)
    ((rationalScale d z).im + (1 / d : ℝ) / 2)
  have hw : (0 : ℝ) < 1 / d := one_div_pos.mpr hdR
  have hxcell : x ∈ meshCell d z := by
    change (rationalScale d z).re < (rationalScale d z).re + (1 / d : ℝ) / 2 ∧
      (rationalScale d z).re + (1 / d : ℝ) / 2 <
        (rationalScale d z).re + (1 / d : ℝ) ∧
      (rationalScale d z).im < (rationalScale d z).im + (1 / d : ℝ) / 2 ∧
      (rationalScale d z).im + (1 / d : ℝ) / 2 <
        (rationalScale d z).im + (1 / d : ℝ)
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have hxsupport : x ∈ K.support := interior_subset (hz hxcell)
  have hxnorm : ‖x‖ ≤ C := hC x hxsupport
  have hre := abs_le.mp (Complex.abs_re_le_norm x |>.trans hxnorm)
  have him := abs_le.mp (Complex.abs_im_le_norm x |>.trans hxnorm)
  have hxre : x.re = (z 0 : ℝ) / (d : ℝ) + 1 / (d : ℝ) / 2 := by
    simp only [x, rationalScale_re_eq]
  have hxim : x.im = (z 1 : ℝ) / (d : ℝ) + 1 / (d : ℝ) / 2 := by
    simp only [x, rationalScale_im_eq]
  have hzre : (z 0 : ℝ) = (d : ℝ) * x.re - 1 / 2 := by
    rw [hxre]
    field_simp [hdne]
    ring
  have hzim : (z 1 : ℝ) = (d : ℝ) * x.im - 1 / 2 := by
    rw [hxim]
    field_simp [hdne]
    ring
  have hz0loR : (-(N : ℤ) : ℝ) ≤ (z 0 : ℝ) := by
    norm_num
    rw [hzre]
    nlinarith
  have hz0hiR : (z 0 : ℝ) ≤ (N : ℕ) := by
    rw [hzre]
    nlinarith
  have hz1loR : (-(N : ℤ) : ℝ) ≤ (z 1 : ℝ) := by
    norm_num
    rw [hzim]
    nlinarith
  have hz1hiR : (z 1 : ℝ) ≤ (N : ℕ) := by
    rw [hzim]
    nlinarith
  change e z ∈ B
  exact ⟨⟨by exact_mod_cast hz0loR, by exact_mod_cast hz0hiR⟩,
    ⟨by exact_mod_cast hz1loR, by exact_mod_cast hz1hiR⟩⟩

private theorem openSet_meshCell_constant {E : Set Tiling.Plane} {d : ℕ}
    (hd : 0 < d) (hEopen : IsOpen E) (hfront : frontier E ⊆ meshLines d)
    (z : ZPlane) : meshCell d z ⊆ E ∨ Disjoint (meshCell d z) E := by
  have hcover : meshCell d z ⊆ E ∪ (closure E)ᶜ := by
    intro x hxcell
    have hxnotFrontier : x ∉ frontier E := by
      intro hxfront
      exact meshCell_disjoint_meshLines hd hxcell (hfront hxfront)
    by_cases hxcl : x ∈ closure E
    · left
      have hxint : x ∈ interior E := by
        by_contra hxnotint
        exact hxnotFrontier ⟨hxcl, hxnotint⟩
      simpa only [hEopen.interior_eq] using hxint
    · exact Or.inr hxcl
  rcases (convex_meshCell d z).isPreconnected.subset_or_subset
      hEopen isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) hcover with
    hsub | hsub
  · exact Or.inl hsub
  · right
    rw [Set.disjoint_left]
    intro x hxcell hxE
    exact hsub hxcell (subset_closure hxE)

theorem exists_regionRaster :
  ∀ {K : Region} {d : ℕ}, 0 < d → OnRationalMesh d K.vertices →
    ∃ F : Finset ZPlane,
      F.Nonempty ∧
      (F : Set ZPlane) = rasterCells d K.openCarrier ∧
      K.openCarrier =ᵐ[volume] ⋃ f : F, meshCell d f.1 ∧
      K.openCarrier = regularizedCellUnion d F := by
  intro K d hd hmesh
  let A : Set ZPlane := rasterCells d K.openCarrier
  have hAfin : A.Finite := rasterCells_finite hd
  let F : Finset ZPlane := hAfin.toFinset
  have hFA : (F : Set ZPlane) = A := by
    simp [F]
  have hfront : frontier K.openCarrier ⊆ meshLines d :=
    region_frontier_subset_meshLines hd hmesh
  have hconstant : ∀ z : ZPlane,
      meshCell d z ⊆ K.openCarrier ∨ Disjoint (meshCell d z) K.openCarrier :=
    openSet_meshCell_constant hd K.openCarrier_regularOpen.1 hfront
  let U : Set Tiling.Plane := ⋃ z : A, meshCell d z.1
  have hUE : U =ᵐ[volume] K.openCarrier := by
    apply ae_iff.mpr
    apply measure_mono_null _ (meshLines_volume_zero hd)
    intro x hxneq
    by_contra hxline
    apply hxneq
    apply propext
    change (x ∈ U) ↔ x ∈ K.openCarrier
    constructor
    · intro hxU
      rcases Set.mem_iUnion.mp hxU with ⟨z, hxz⟩
      exact z.2 hxz
    · intro hxK
      rcases offMesh_existsUnique_meshCell hd x hxline with ⟨z, hxz, _⟩
      have hzsubset : meshCell d z ⊆ K.openCarrier := by
        rcases hconstant z with hsub | hdisj
        · exact hsub
        · exact False.elim (Set.disjoint_left.mp hdisj hxz hxK)
      exact Set.mem_iUnion_of_mem ⟨z, hzsubset⟩ hxz
  have hUreg : U =ᵐ[volume] regularizedCellUnion d A :=
    rawCellUnion_aeEq_regularizedCellUnion hd A
  have hregular : K.openCarrier = regularizedCellUnion d A := by
    apply regularOpen_eq_of_aeEq K.openCarrier_regularOpen.1
      K.openCarrier_regularOpen.2 isOpen_interior
    · simp
    · exact hUE.symm.trans hUreg
  have hAnonempty : A.Nonempty := by
    obtain ⟨x, hxK⟩ := K.isPolygonal.interior_nonempty K.nonempty
    change x ∈ K.openCarrier at hxK
    have hopenNe : volume K.openCarrier ≠ 0 :=
      K.openCarrier_regularOpen.1.measure_ne_zero volume ⟨x, hxK⟩
    have hex : ∃ y ∈ K.openCarrier, y ∉ meshLines d := by
      by_contra hnone
      push Not at hnone
      have hsub : K.openCarrier ⊆ meshLines d := fun y hy ↦ hnone y hy
      exact hopenNe (nonpos_iff_eq_zero.mp
        ((measure_mono hsub).trans_eq (meshLines_volume_zero hd)))
    rcases hex with ⟨y, hyK, hyoff⟩
    rcases offMesh_existsUnique_meshCell hd y hyoff with ⟨z, hyz, _⟩
    refine ⟨z, ?_⟩
    rcases hconstant z with hsub | hdisj
    · exact hsub
    · exact False.elim (Set.disjoint_left.mp hdisj hyz hyK)
  refine ⟨F, ?_, hFA, ?_, ?_⟩
  · simpa [F] using hAnonempty
  · have hUF : (⋃ f : F, meshCell d f.1) = U := by
      ext x
      simp [U, F]
    rw [hUF]
    exact hUE.symm
  · rw [hFA]
    exact hregular

private theorem translatedRaster_rawSandwich :
  ∀ {K : Region} {d : ℕ}, 0 < d → OnRationalMesh d K.vertices →
    ∀ (F : Finset ZPlane),
      (F : Set ZPlane) = rasterCells d K.openCarrier →
    ∀ A : Set ZPlane,
      (⋃ q : Tiling.RationalPolygonal.discreteCarrier F A, meshCell d q.1) ⊆
        openUnion K (rationalScale d '' A) ∧
      openUnion K (rationalScale d '' A) ⊆
        closure (⋃ q : Tiling.RationalPolygonal.discreteCarrier F A,
          meshCell d q.1) := by
  intro K d hd hmesh F hF A
  let U : Set Tiling.Plane :=
    ⋃ q : Tiling.RationalPolygonal.discreteCarrier F A, meshCell d q.1
  constructor
  · intro x hxU
    rcases Set.mem_iUnion.mp hxU with ⟨q, hxq⟩
    rcases Tiling.RationalPolygonal.mem_discreteCarrier_iff.mp q.2 with
      ⟨f, hfF, a, haA, hq⟩
    rw [hq, meshCell_add hd] at hxq
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    refine ⟨⟨rationalScale d a, ⟨a, haA, rfl⟩⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxq ⊢
    have hfRaster : f ∈ rasterCells d K.openCarrier := by
      rw [← hF]
      exact hfF
    exact hfRaster hxq
  · rcases exists_regionRaster hd hmesh with
      ⟨G, _hGne, hG, _hKae, hKreg⟩
    have hGF : G = F := Finset.coe_injective (hG.trans hF.symm)
    subst G
    let V : Set Tiling.Plane := ⋃ f : F, meshCell d f.1
    have hKcl : K.openCarrier ⊆ closure V := by
      intro y hy
      rw [hKreg] at hy
      exact interior_subset hy
    intro x hxOpen
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hxOpen
    rcases hxOpen with ⟨s, hxs⟩
    rcases s.2 with ⟨a, haA, hsa⟩
    have hxTranslatedClosure :
        x ∈ closure (rationalScale d a +ᵥ V) := by
      rw [closure_vadd]
      rw [← hsa] at hxs
      exact Set.vadd_set_mono hKcl hxs
    apply closure_mono _ hxTranslatedClosure
    intro y hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    rcases Set.mem_iUnion.mp hy with ⟨f, hyf⟩
    have hyCell : y ∈ meshCell d (f.1 + a) := by
      rw [meshCell_add hd]
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      exact hyf
    have hcarrier : f.1 + a ∈
        Tiling.RationalPolygonal.discreteCarrier F A :=
      Tiling.RationalPolygonal.mem_discreteCarrier_iff.mpr
        ⟨f.1, f.2, a, haA, rfl⟩
    exact Set.mem_iUnion_of_mem ⟨f.1 + a, hcarrier⟩ hyCell

theorem regularSupport_rationalScale_image :
  ∀ {K : Region} {d : ℕ}, 0 < d → OnRationalMesh d K.vertices →
    ∀ (F : Finset ZPlane),
      (F : Set ZPlane) = rasterCells d K.openCarrier →
    ∀ A : Set ZPlane,
      regularSupport K (rationalScale d '' A) =
        regularizedCellUnion d (Tiling.RationalPolygonal.discreteCarrier F A) := by
  intro K d hd hmesh F hF A
  let D : Set ZPlane := Tiling.RationalPolygonal.discreteCarrier F A
  let U : Set Tiling.Plane := ⋃ q : D, meshCell d q.1
  rcases translatedRaster_rawSandwich hd hmesh F hF A with
    ⟨hUopen, hopenU⟩
  have hclosure : closure (openUnion K (rationalScale d '' A)) = closure U := by
    apply Set.Subset.antisymm
    · exact closure_minimal hopenU isClosed_closure
    · exact closure_mono hUopen
  change interior (closure (openUnion K (rationalScale d '' A))) =
    interior (closure U)
  rw [hclosure]

private theorem offMesh_sub_rationalScale {d : ℕ} (hd : 0 < d)
    {y : Tiling.Plane} (hy : y ∉ meshLines d) (a : ZPlane) :
    y - rationalScale d a ∉ meshLines d := by
  intro hline
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  rcases hline with ⟨n, hn⟩ | ⟨n, hn⟩
  · apply hy
    left
    refine ⟨n + a 0, ?_⟩
    have hn' : y.re - (a 0 : ℝ) / (d : ℝ) =
        (n : ℝ) / (d : ℝ) := by
      norm_num at hn ⊢
      simpa only [Complex.sub_re, rationalScale_re_eq] using hn
    norm_num at ⊢
    field_simp [hdne] at hn' ⊢
    linarith
  · apply hy
    right
    refine ⟨n + a 1, ?_⟩
    have hn' : y.im - (a 1 : ℝ) / (d : ℝ) =
        (n : ℝ) / (d : ℝ) := by
      norm_num at hn ⊢
      simpa only [Complex.sub_im, rationalScale_im_eq] using hn
    norm_num at ⊢
    field_simp [hdne] at hn' ⊢
    linarith

private theorem discreteCarrier_eq_target_of_tiles {F : Finset ZPlane}
    {A R : Set ZPlane} (htiles : TranslationalTilings.Tiles F A R) :
    Tiling.RationalPolygonal.discreteCarrier F A = R := by
  classical
  have hcount := (TranslationalTilings.tilesAtLevel_iff_representation_count
    F A R 1).mp htiles
  ext q
  constructor
  · intro hq
    rcases Tiling.RationalPolygonal.mem_discreteCarrier_iff.mp hq with
      ⟨f, hfF, a, haA, hqeq⟩
    by_contra hqR
    have hc := hcount q
    rw [if_neg hqR] at hc
    have hfmem : f ∈ F.filter fun g ↦ q - g ∈ A := by
      simp only [Finset.mem_filter, hfF, true_and]
      rw [hqeq]
      simpa only [add_sub_cancel_left] using haA
    have hpos : 0 < (F.filter fun g ↦ q - g ∈ A).card :=
      Finset.card_pos.mpr ⟨f, hfmem⟩
    omega
  · intro hqR
    have hc := hcount q
    rw [if_pos hqR] at hc
    have hne : (F.filter fun f ↦ q - f ∈ A).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty] at hc
      simp at hc
    rcases hne with ⟨f, hf⟩
    rw [Finset.mem_filter] at hf
    exact Tiling.RationalPolygonal.mem_discreteCarrier_iff.mpr
      ⟨f, hf.1, q - f, hf.2, by abel⟩

private theorem tile_representation_unique {F : Finset ZPlane}
    {A R : Set ZPlane} (htiles : TranslationalTilings.Tiles F A R)
    {q f g : ZPlane} (hfF : f ∈ F) (hfA : q - f ∈ A)
    (hgF : g ∈ F) (hgA : q - g ∈ A) : f = g := by
  classical
  have hcount := (TranslationalTilings.tilesAtLevel_iff_representation_count
    F A R 1).mp htiles q
  have hqR : q ∈ R := by
    rw [← discreteCarrier_eq_target_of_tiles htiles]
    exact Tiling.RationalPolygonal.mem_discreteCarrier_iff.mpr
      ⟨f, hfF, q - f, hfA, by abel⟩
  rw [if_pos hqR] at hcount
  rcases Finset.card_eq_one.mp hcount with ⟨u, hu⟩
  have hfmem : f ∈ F.filter fun u ↦ q - u ∈ A := by
    simp only [Finset.mem_filter, hfF, hfA, and_self]
  have hgmem : g ∈ F.filter fun u ↦ q - u ∈ A := by
    simp only [Finset.mem_filter, hgF, hgA, and_self]
  rw [hu] at hfmem hgmem
  simp only [Finset.mem_singleton] at hfmem hgmem
  exact hfmem.trans hgmem.symm

private theorem packing_representation_unique {K : Region} {d : ℕ}
    (hd : 0 < d) (F : Finset ZPlane)
    (hF : (F : Set ZPlane) = rasterCells d K.openCarrier)
    (A : Set ZPlane)
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (rationalScale d '' A)))
    {q f g : ZPlane} (hfF : f ∈ F) (hfA : q - f ∈ A)
    (hgF : g ∈ F) (hgA : q - g ∈ A) : f = g := by
  by_contra hfg
  let a : ZPlane := q - f
  let b : ZPlane := q - g
  have hab : a ≠ b := by
    intro hab
    apply hfg
    dsimp only [a, b] at hab
    rw [sub_eq_add_neg] at hab
    exact neg_injective (add_left_cancel hab)
  have hcent : rationalScale d a ≠ rationalScale d b :=
    (rationalScale_injective hd).ne hab
  have hdisj := (isPacking_iff_openCarrier_disjoint K
    (rationalScale d '' A)).mp hpacking
    (show rationalScale d a ∈ rationalScale d '' A from ⟨a, hfA, rfl⟩)
    (show rationalScale d b ∈ rationalScale d '' A from ⟨b, hgA, rfl⟩)
    hcent
  rcases meshCell_nonempty hd q with ⟨x, hxq⟩
  have hfa : f + a = q := by simp [a]
  have hgb : g + b = q := by simp [b]
  have hxfa : x ∈ rationalScale d a +ᵥ meshCell d f := by
    rw [← meshCell_add hd, hfa]
    exact hxq
  have hxgb : x ∈ rationalScale d b +ᵥ meshCell d g := by
    rw [← meshCell_add hd, hgb]
    exact hxq
  have hfRaster : f ∈ rasterCells d K.openCarrier := by
    rw [← hF]
    exact hfF
  have hgRaster : g ∈ rasterCells d K.openCarrier := by
    rw [← hF]
    exact hgF
  have hxKfa : x ∈ rationalScale d a +ᵥ K.openCarrier :=
    Set.vadd_set_mono hfRaster hxfa
  have hxKgb : x ∈ rationalScale d b +ᵥ K.openCarrier :=
    Set.vadd_set_mono hgRaster hxgb
  exact Set.disjoint_left.mp hdisj hxKfa hxKgb

theorem tilesOn_rationalScale_image_iff_raster :
  ∀ {K : Region} {A : Set ZPlane} {E : Set Tiling.Plane} {d : ℕ},
    0 < d → OnRationalMesh d K.vertices →
    IsOpen E → interior (closure E) = E →
    E = regularizedCellUnion d (rasterCells d E) →
    ∃ F : Finset ZPlane,
      F.Nonempty ∧ (F : Set ZPlane) = rasterCells d K.openCarrier ∧
      (TilesOn K (rationalScale d '' A) E ↔
        TranslationalTilings.Tiles F A (rasterCells d E)) := by
  classical
  intro K A E d hd hmesh hEopen hEregular hEraster
  rcases exists_regionRaster hd hmesh with
    ⟨F, hFne, hF, _hKae, hKreg⟩
  refine ⟨F, hFne, hF, ?_⟩
  let R : Set ZPlane := rasterCells d E
  let D : Set ZPlane := Tiling.RationalPolygonal.discreteCarrier F A
  constructor
  · intro hcontinuous
    have hsupportE : regularSupport K (rationalScale d '' A) = E :=
      regularSupport_eq_of_tilesOn hEopen hEregular hcontinuous
    have hsupportD : regularSupport K (rationalScale d '' A) =
        regularizedCellUnion d D :=
      regularSupport_rationalScale_image hd hmesh F hF A
    have hregEq : regularizedCellUnion d D = regularizedCellUnion d R := by
      calc
        regularizedCellUnion d D = regularSupport K (rationalScale d '' A) :=
          hsupportD.symm
        _ = E := hsupportE
        _ = regularizedCellUnion d R := hEraster
    have hDR : D = R := by
      ext q
      constructor
      · intro hqD
        have hsub :=
          (meshCell_subset_regularizedCellUnion_iff hd D q).mpr hqD
        rw [hregEq] at hsub
        exact (meshCell_subset_regularizedCellUnion_iff hd R q).mp hsub
      · intro hqR
        have hsub :=
          (meshCell_subset_regularizedCellUnion_iff hd R q).mpr hqR
        rw [← hregEq] at hsub
        exact (meshCell_subset_regularizedCellUnion_iff hd D q).mp hsub
    apply (TranslationalTilings.tilesAtLevel_iff_representation_count
      F A R 1).mpr
    intro q
    by_cases hqR : q ∈ R
    · rw [if_pos hqR]
      have hqD : q ∈ D := by rwa [hDR]
      rcases Tiling.RationalPolygonal.mem_discreteCarrier_iff.mp hqD with
        ⟨f, hfF, a, haA, hq⟩
      have hfA : q - f ∈ A := by
        rw [hq]
        simpa only [add_sub_cancel_left] using haA
      have hfilter : (F.filter fun g ↦ q - g ∈ A) = {f} := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hg
          exact packing_representation_unique hd F hF A hcontinuous.2.1
            hg.1 hg.2 hfF hfA
        · rintro rfl
          exact ⟨hfF, hfA⟩
      rw [hfilter]
      simp
    · rw [if_neg hqR]
      have hfilter : (F.filter fun f ↦ q - f ∈ A) = ∅ := by
        ext f
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hfF hfA
        apply hqR
        rw [← hDR]
        exact Tiling.RationalPolygonal.mem_discreteCarrier_iff.mpr
          ⟨f, hfF, q - f, hfA, by abel⟩
      rw [hfilter]
      simp
  · intro hdiscrete
    have hDR : D = R := discreteCarrier_eq_target_of_tiles hdiscrete
    have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements (rationalScale d '' A)) := by
      rw [isPacking_iff_openCarrier_disjoint]
      intro s hs t ht hst
      rcases hs with ⟨a, haA, rfl⟩
      rcases ht with ⟨b, hbA, rfl⟩
      change Disjoint (rationalScale d a +ᵥ K.openCarrier)
        (rationalScale d b +ᵥ K.openCarrier)
      rw [Set.disjoint_left]
      intro x hxa hxb
      let O : Set Tiling.Plane :=
        (rationalScale d a +ᵥ K.openCarrier) ∩
          (rationalScale d b +ᵥ K.openCarrier)
      have hOopen : IsOpen O :=
        (K.openCarrier_regularOpen.1.vadd (rationalScale d a)).inter
          (K.openCarrier_regularOpen.1.vadd (rationalScale d b))
      have hOne : O.Nonempty := ⟨x, hxa, hxb⟩
      have hOmeasure : volume O ≠ 0 := hOopen.measure_ne_zero volume hOne
      have hyexists : ∃ y ∈ O, y ∉ meshLines d := by
        by_contra hnone
        push Not at hnone
        have hsub : O ⊆ meshLines d := fun y hy ↦ hnone y hy
        exact hOmeasure (nonpos_iff_eq_zero.mp
          ((measure_mono hsub).trans_eq (meshLines_volume_zero hd)))
      rcases hyexists with ⟨y, hya, hyoff⟩
      have hyaK : y - rationalScale d a ∈ K.openCarrier := by
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          neg_add_eq_sub] using hya.1
      have hybK : y - rationalScale d b ∈ K.openCarrier := by
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          neg_add_eq_sub] using hya.2
      have hyaoff := offMesh_sub_rationalScale hd hyoff a
      have hyboff := offMesh_sub_rationalScale hd hyoff b
      rcases offMesh_existsUnique_meshCell hd _ hyaoff with
        ⟨f, hyaf, _⟩
      rcases offMesh_existsUnique_meshCell hd _ hyboff with
        ⟨g, hybg, _⟩
      have hfRaster : f ∈ rasterCells d K.openCarrier := by
        rcases openSet_meshCell_constant hd K.openCarrier_regularOpen.1
            (region_frontier_subset_meshLines hd hmesh) f with
          hf | hf
        · exact hf
        · exact False.elim (Set.disjoint_left.mp hf hyaf hyaK)
      have hgRaster : g ∈ rasterCells d K.openCarrier := by
        rcases openSet_meshCell_constant hd K.openCarrier_regularOpen.1
            (region_frontier_subset_meshLines hd hmesh) g with
          hg | hg
        · exact hg
        · exact False.elim (Set.disjoint_left.mp hg hybg hybK)
      have hfF : f ∈ F := by
        change f ∈ (F : Set ZPlane)
        rw [hF]
        exact hfRaster
      have hgF : g ∈ F := by
        change g ∈ (F : Set ZPlane)
        rw [hF]
        exact hgRaster
      have hyfa : y ∈ meshCell d (f + a) := by
        rw [meshCell_add hd]
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          neg_add_eq_sub] using hyaf
      have hygb : y ∈ meshCell d (g + b) := by
        rw [meshCell_add hd]
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          neg_add_eq_sub] using hybg
      have hindex : f + a = g + b := by
        funext i
        fin_cases i
        · exact (floor_re_eq_of_mem_meshCell hd hyfa).symm.trans
            (floor_re_eq_of_mem_meshCell hd hygb)
        · exact (floor_im_eq_of_mem_meshCell hd hyfa).symm.trans
            (floor_im_eq_of_mem_meshCell hd hygb)
      have hfg : f = g := tile_representation_unique hdiscrete
        hfF (show f + a - f ∈ A by simpa using haA)
        hgF (show f + a - g ∈ A by rw [hindex]; simpa using hbA)
      have hab : a = b := by
        rw [hfg] at hindex
        exact add_left_cancel hindex
      exact hst (congrArg (rationalScale d) hab)
    have hcountable : (rationalScale d '' A).Countable :=
      (Set.countable_univ.mono (Set.subset_univ A)).image (rationalScale d)
    refine ⟨hcountable, hpacking, ?_⟩
    have hopenAE := openUnion_aeEq_regularSupport hpacking
    have hsupport : regularSupport K (rationalScale d '' A) = E := by
      calc
        regularSupport K (rationalScale d '' A) =
            regularizedCellUnion d D :=
          regularSupport_rationalScale_image hd hmesh F hF A
        _ = regularizedCellUnion d R := congrArg (regularizedCellUnion d) hDR
        _ = E := hEraster.symm
    filter_upwards [hopenAE] with x hx
    rw [← Set.mem_iUnion]
    change x ∈ E ↔ x ∈ openUnion K (rationalScale d '' A)
    rw [← hsupport]
    change regularSupport K (rationalScale d '' A) x ↔
      openUnion K (rationalScale d '' A) x
    exact iff_of_eq hx.symm


end Tiling.AxisParallel.RationalMesh
