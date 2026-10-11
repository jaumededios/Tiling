import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.Dilation.Periodic
import TranslationalTilings.LatticeGeometry

/-!
# Grouped structure decompositions

The compactness construction of the paper's structural decomposition, its
grouping by commensurability classes, and the one-dimensional period corollary.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real symmDiff

namespace TranslationalTilings

/-- A decomposition of a tiling convolution into bounded periodic directional
error functions. -/
structure StructureDecomposition {d : ℕ}
    (F : Finset (Lattice d)) (A : Set (Lattice d)) (ell : ℕ) where
  /-- The periodic error function attached to each nonzero tile vector. -/
  phi : ↥(F.erase 0) → Lattice d → ℝ
  phi_nonneg : ∀ f x, 0 ≤ phi f x
  phi_le_one : ∀ f x, phi f x ≤ 1
  phi_periodic : ∀ f, Function.Periodic (phi f)
    ((indicatorDilationModulus ell F.card : ℤ) • (f.1 : Lattice d))
  decomposition : ∀ x, ((setIndicator A x : ℤ) : ℝ) =
    ((tileConv F (setIndicator A) x : ℤ) : ℝ) - ∑ f, phi f x

/-- A structure decomposition grouped into primitive pairwise-incommensurable
directions. -/
structure GroupedStructureDecomposition {d : ℕ}
    (F : Finset (Lattice d)) (A E : Set (Lattice d))
    (ell k : ℕ) where
  /-- The number of grouped primitive directions. -/
  numberOfDirections : ℕ
  number_pos : 0 < numberOfDirections
  number_le : numberOfDirections ≤ F.card - 1
  /-- The primitive representative of each commensurability class. -/
  direction : Fin numberOfDirections → Lattice d
  direction_ne_zero : ∀ j, direction j ≠ 0
  pairwise_incommensurable : PairwiseIncommensurable direction
  /-- The accumulated periodic error along each grouped direction. -/
  phi : Fin numberOfDirections → Lattice d → ℝ
  phi_nonneg : ∀ j x, 0 ≤ phi j x
  phi_le_level : ∀ j x, phi j x ≤ k
  phi_periodic : ∀ j, Function.Periodic (phi j)
    ((indicatorDilationModulus ell F.card : ℤ) • direction j)
  decomposition : ∀ x, ((setIndicator A x : ℤ) : ℝ) =
    (k : ℝ) * ((setIndicator E x : ℤ) : ℝ) - ∑ j, phi j x
  sum_phi_le : ∀ x, ∑ j, phi j x ≤ k
  direction_from_tile : ∀ j, ∃ f ∈ F, f ≠ 0 ∧
    ∃ z : ℤ, direction j = z • f
  product_direction_l1_bound :
    ∏ j, l1Norm (direction j) ≤ l1Diameter F ^ (F.card - 1)
  product_direction_euclidean_bound :
    ∏ j, euclideanNorm (direction j) ≤
      euclideanDiameter F ^ (F.card - 1)

/-- The common one-dimensional period obtained from the dilation modulus and
the least common multiple of the tile displacements. -/
def universalPeriod1D (ell : ℕ) (F : Finset ℤ) : ℕ :=
  indicatorDilationModulus ell F.card *
    (F.erase 0).lcm Int.natAbs

private noncomputable def structureApprox {d : ℕ} (q N : ℕ)
    (f : Lattice d) (A : Set (Lattice d)) (x : Lattice d) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
    ((setIndicator A
      (x - ((1 + n * q : ℕ) : ℤ) • f) : ℤ) : ℝ)

private theorem structureApprox_mem_Icc {d q N : ℕ}
    (f : Lattice d) (A : Set (Lattice d)) (x : Lattice d) :
    structureApprox q N f A x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  have hindicator (y : Lattice d) :
      (0 : ℝ) ≤ ((setIndicator A y : ℤ) : ℝ) ∧
        ((setIndicator A y : ℤ) : ℝ) ≤ 1 := by
    by_cases hy : y ∈ A <;> simp [setIndicator, hy]
  have hsum_nonneg :
      0 ≤ ∑ n ∈ Finset.range (N + 1),
        ((setIndicator A
          (x - ((1 + n * q : ℕ) : ℤ) • f) : ℤ) : ℝ) :=
    Finset.sum_nonneg fun n _ ↦ (hindicator _).1
  have hsum_le :
      (∑ n ∈ Finset.range (N + 1),
        ((setIndicator A
          (x - ((1 + n * q : ℕ) : ℤ) • f) : ℤ) : ℝ)) ≤
          (N + 1 : ℕ) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range (N + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun n _ ↦ (hindicator _).2
      _ = (N + 1 : ℕ) := by simp
  have hpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hpos.le) hsum_nonneg
  · rw [structureApprox, inv_mul_le_iff₀ hpos]
    simpa using hsum_le

private theorem tileConv_dilate_apply_real {d r : ℕ}
    (F : Finset (Lattice d)) (A : Set (Lattice d)) (x : Lattice d)
    (hr : 0 < r) :
    ((tileConv (dilate r F) (setIndicator A) x : ℤ) : ℝ) =
      ∑ f ∈ F,
        ((setIndicator A (x - (r : ℤ) • f) : ℤ) : ℝ) := by
  rw [← Int.cast_sum]
  congr 1
  simp only [tileConv, dilate]
  rw [Finset.sum_image]
  intro a _ b _ hab
  apply_fun fun z i ↦ z i at hab
  funext i
  have hrz : (r : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hi := congrFun hab i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact mul_left_cancel₀ hrz hi

private theorem structureApprox_sum {d ell N : ℕ}
    {F : Finset (Lattice d)} {A : Set (Lattice d)}
    (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : ScalarPeriodic ell (tileConv F (setIndicator A)))
    (x : Lattice d) :
    ∑ f : ↥(F.erase 0),
        structureApprox (indicatorDilationModulus ell F.card) N f A x =
      ((tileConv F (setIndicator A) x : ℤ) : ℝ) -
        ((setIndicator A x : ℤ) : ℝ) := by
  classical
  let q := indicatorDilationModulus ell F.card
  have hterm (n : ℕ) :
      (∑ f : ↥(F.erase 0),
        ((setIndicator A
          (x - ((1 + n * q : ℕ) : ℤ) • (f : Lattice d)) : ℤ) : ℝ)) =
        ((tileConv F (setIndicator A) x : ℤ) : ℝ) -
          ((setIndicator A x : ℤ) : ℝ) := by
    let r := 1 + n * q
    have hr : 0 < r := by positivity
    have hmod : Nat.ModEq q r 1 := by
      simp [Nat.ModEq, r]
    have hdilate := dilation_indicator_periodic hell hperiod hr hmod
    have hx := congrFun hdilate x
    have hcast := congrArg (fun z : ℤ ↦ (z : ℝ)) hx
    rw [tileConv_dilate_apply_real F A x hr] at hcast
    have herase := Finset.sum_erase_add F
      (fun f ↦ ((setIndicator A (x - (r : ℤ) • f) : ℤ) : ℝ)) hzero
    have hsubtype :
        (∑ f ∈ F.erase 0,
          ((setIndicator A (x - (r : ℤ) • f) : ℤ) : ℝ)) =
        ∑ f : ↥(F.erase 0),
          ((setIndicator A (x - (r : ℤ) • (f : Lattice d)) : ℤ) : ℝ) :=
      Finset.sum_subtype (F.erase 0) (fun f ↦ Iff.rfl)
        (fun f ↦ ((setIndicator A (x - (r : ℤ) • f) : ℤ) : ℝ))
    simp only [smul_zero, sub_zero] at herase
    rw [hsubtype] at herase
    dsimp [r, q] at herase hcast ⊢
    linarith
  have hpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  simp only [structureApprox]
  rw [← Finset.mul_sum, Finset.sum_comm]
  dsimp [q] at hterm
  have hterm' (n : ℕ) :
      (∑ f : ↥(F.erase 0),
        ((setIndicator A
          (x - ((1 + n * indicatorDilationModulus ell F.card : ℕ) : ℤ) •
            (f : Lattice d)) : ℤ) : ℝ)) =
        ((tileConv F (setIndicator A) x : ℤ) : ℝ) -
          ((setIndicator A x : ℤ) : ℝ) := by
    convert hterm n using 1
    all_goals norm_num
  simp_rw [hterm']
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

private theorem structureApprox_periodic_tendsto {d q : ℕ}
    (f : Lattice d) (A : Set (Lattice d)) (x : Lattice d) :
    Filter.Tendsto
      (fun N ↦ structureApprox q N f A (x + (q : ℤ) • f) -
        structureApprox q N f A x)
      Filter.atTop (nhds 0) := by
  classical
  let a : ℕ → ℝ := fun n ↦
    ((setIndicator A
      (x - ((1 + n * q : ℕ) : ℤ) • f) : ℤ) : ℝ)
  let b : ℕ → ℝ := fun n ↦
    ((setIndicator A
      (x + (q : ℤ) • f - ((1 + n * q : ℕ) : ℤ) • f) : ℤ) : ℝ)
  have hb_succ (n : ℕ) : b (n + 1) = a n := by
    dsimp [a, b]
    congr 2
    norm_cast
    module
  have hsumShift (N : ℕ) :
      (∑ n ∈ Finset.range (N + 1), b n) =
        (∑ n ∈ Finset.range N, a n) + b 0 := by
    rw [Finset.sum_range_succ']
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    exact hb_succ n
  have hdiff (N : ℕ) :
      structureApprox q N f A (x + (q : ℤ) • f) -
          structureApprox q N f A x =
        ((N + 1 : ℕ) : ℝ)⁻¹ * (b 0 - a N) := by
    rw [structureApprox, structureApprox]
    change ((N + 1 : ℕ) : ℝ)⁻¹ * (∑ n ∈ Finset.range (N + 1), b n) -
        ((N + 1 : ℕ) : ℝ)⁻¹ * (∑ n ∈ Finset.range (N + 1), a n) = _
    rw [hsumShift, Finset.sum_range_succ]
    ring
  have habs (n : ℕ) : |a n| ≤ 1 ∧ |b n| ≤ 1 := by
    have hindicator (y : Lattice d) :
        |((setIndicator A y : ℤ) : ℝ)| ≤ 1 := by
      by_cases hy : y ∈ A <;> simp [setIndicator, hy]
    constructor
    · exact hindicator _
    · exact hindicator _
  have hbound (N : ℕ) :
      |structureApprox q N f A (x + (q : ℤ) • f) -
          structureApprox q N f A x| ≤
        2 * (1 / ((N : ℝ) + 1)) := by
    rw [hdiff, abs_mul, abs_inv]
    have hdenom : |((N + 1 : ℕ) : ℝ)| = (N : ℝ) + 1 := by
      rw [abs_of_nonneg (by positivity)]
      norm_num
    rw [hdenom]
    calc
      ((N : ℝ) + 1)⁻¹ * |b 0 - a N| ≤
          ((N : ℝ) + 1)⁻¹ * (|b 0| + |a N|) := by
        gcongr
        exact abs_sub _ _
      _ ≤ ((N : ℝ) + 1)⁻¹ * (1 + 1) := by
        gcongr
        · exact (habs 0).2
        · exact (habs N).1
      _ = 2 * (1 / ((N : ℝ) + 1)) := by ring
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun _ ↦ abs_nonneg _) hbound
    (by simpa using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2))

/-- A scalar-periodic tiling convolution admits bounded periodic directional
error functions (Paper Theorem 1.7). -/
theorem exists_structureDecomposition {d ell : ℕ}
    {F : Finset (Lattice d)} {A : Set (Lattice d)}
    (_hd : 0 < d) (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : ScalarPeriodic ell (tileConv F (setIndicator A))) :
    Nonempty (StructureDecomposition F A ell) := by
  classical
  let q := indicatorDilationModulus ell F.card
  let X := ∀ _f : ↥(F.erase 0), Lattice d → Set.Icc (0 : ℝ) 1
  have happroxMem (N : ℕ) (f : ↥(F.erase 0)) (x : Lattice d) :
      structureApprox q N (f : Lattice d) A x ∈ Set.Icc (0 : ℝ) 1 :=
    structureApprox_mem_Icc (q := q) (N := N) (f : Lattice d) A x
  let point : ℕ → X := fun N f x ↦
    ⟨structureApprox q N (f : Lattice d) A x, happroxMem N f x⟩
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  let limitPoint : X := (U.map point).lim
  let phi : ↥(F.erase 0) → Lattice d → ℝ :=
    fun f x ↦ (limitPoint f x).1
  have hpoint : Filter.Tendsto point (U : Filter ℕ) (nhds limitPoint) := by
    exact (U.map point).le_nhds_lim
  have hUle : (U : Filter ℕ) ≤ Filter.atTop := by
    dsimp [U]
    exact Ultrafilter.of_le Filter.atTop
  have hcoord (f : ↥(F.erase 0)) (x : Lattice d) :
      Filter.Tendsto (fun N ↦ structureApprox q N f A x)
        (U : Filter ℕ) (nhds (phi f x)) := by
    have hcontinuous : Continuous (fun p : X ↦ (p f x).1) :=
      continuous_subtype_val.comp
        ((continuous_apply x).comp (continuous_apply f))
    have htend := (hcontinuous.tendsto limitPoint).comp hpoint
    refine htend.congr' (Filter.Eventually.of_forall fun N ↦ ?_)
    rfl
  refine ⟨{
    phi := phi
    phi_nonneg := ?_
    phi_le_one := ?_
    phi_periodic := ?_
    decomposition := ?_ }⟩
  · intro f x
    exact (limitPoint f x).property.1
  · intro f x
    exact (limitPoint f x).property.2
  · intro f x
    have hlim := (hcoord f (x + (q : ℤ) • (f : Lattice d))).sub (hcoord f x)
    have hzero := (structureApprox_periodic_tendsto
      (q := q) (f : Lattice d) A x).mono_left hUle
    have heq := tendsto_nhds_unique hlim hzero
    exact sub_eq_zero.mp heq
  · intro x
    have hsumlim : Filter.Tendsto
        (fun N ↦ ∑ f : ↥(F.erase 0), structureApprox q N f A x)
        (U : Filter ℕ) (nhds (∑ f, phi f x)) := by
      exact tendsto_finsetSum Finset.univ fun f _ ↦ hcoord f x
    have hsumEq :
        (fun N ↦ ∑ f : ↥(F.erase 0), structureApprox q N f A x) =
          fun _ ↦ ((tileConv F (setIndicator A) x : ℤ) : ℝ) -
            ((setIndicator A x : ℤ) : ℝ) := by
      funext N
      dsimp [q]
      exact structureApprox_sum hell hzero hperiod x
    rw [hsumEq] at hsumlim
    have heq := tendsto_nhds_unique hsumlim tendsto_const_nhds
    linarith

private abbrev NonzeroLattice (d : ℕ) := {x : Lattice d // x ≠ 0}

private theorem commensurable_refl_nonzero {d : ℕ} (u : NonzeroLattice d) :
    Commensurable (u : Lattice d) u := by
  exact ⟨1, 1, one_ne_zero, one_ne_zero, by simp⟩

private theorem commensurable_symm {d : ℕ} {u v : Lattice d} :
    Commensurable u v → Commensurable v u := by
  rintro ⟨a, b, ha, hb, hab⟩
  exact ⟨b, a, hb, ha, hab.symm⟩

private theorem commensurable_trans_nonzero {d : ℕ}
    {u v w : Lattice d} (_hu : u ≠ 0) (_hv : v ≠ 0) (_hw : w ≠ 0)
    (huv : Commensurable u v) (hvw : Commensurable v w) :
    Commensurable u w := by
  obtain ⟨a, b, ha, hb, hab⟩ := huv
  obtain ⟨c, e, hc, he, hce⟩ := hvw
  refine ⟨c * a, b * e, mul_ne_zero hc ha, mul_ne_zero hb he, ?_⟩
  calc
    (c * a) • u = c • (a • u) := by rw [mul_smul]
    _ = c • (b • v) := by rw [hab]
    _ = (c * b) • v := by rw [mul_smul]
    _ = (b * c) • v := by rw [mul_comm]
    _ = b • (c • v) := by rw [mul_smul]
    _ = b • (e • w) := by rw [hce]
    _ = (b * e) • w := by rw [mul_smul]

private def nonzeroCommensurabilitySetoid (d : ℕ) :
    Setoid (NonzeroLattice d) where
  r u v := Commensurable (u : Lattice d) v
  iseqv := {
    refl := commensurable_refl_nonzero
    symm := @fun _u _v huv ↦ commensurable_symm huv
    trans := @fun u v w huv hvw ↦
      commensurable_trans_nonzero u.property v.property w.property huv hvw }

private abbrev DirectionClass (d : ℕ) :=
  Quotient (nonzeroCommensurabilitySetoid d)

private theorem commensurable_of_nonzero_multiple {d : ℕ}
    {u v : Lattice d} {z : ℤ} (hz : z ≠ 0)
    (hu : u = z • v) : Commensurable u v := by
  exact ⟨1, z, one_ne_zero, hz, by simp [hu]⟩

private theorem mem_tile_euclideanNorm_le_diameter {d : ℕ}
    {F : Finset (Lattice d)} (hzero : 0 ∈ F)
    {f : Lattice d} (hf : f ∈ F) :
    euclideanNorm f ≤ euclideanDiameter F := by
  classical
  have hprod : (F ×ˢ F).Nonempty :=
    ⟨(f, 0), by simp [hf, hzero]⟩
  rw [euclideanDiameter, dif_pos hprod]
  have hle := Finset.le_sup'
    (f := fun xy : Lattice d × Lattice d ↦
      euclideanNorm (xy.1 - xy.2))
    (show (f, 0) ∈ F ×ˢ F by simp [hf, hzero])
  simpa only [sub_zero] using hle

/-- Group the structural error functions into primitive pairwise-incommensurable
directions (Paper Theorem 3.4). -/
theorem exists_groupedStructureDecomposition {d ell k : ℕ}
    {F : Finset (Lattice d)} {A E : Set (Lattice d)}
    (hd : 0 < d) (hell : 0 < ell) (hk : 0 < k)
    (hcard : 1 < F.card) (hzero : 0 ∈ F)
    (hE : SetScalarPeriodic ell E) (htile : TilesAtLevel F A E k) :
    Nonempty (GroupedStructureDecomposition F A E ell k) := by
  classical
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hEindicator : ScalarPeriodic ell (setIndicator E) := by
    intro x z
    have hm := hE x z
    by_cases hx : x ∈ E
    · have hy : x + (ell : ℤ) • z ∈ E := hm.mpr hx
      rw [setIndicator, Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · have hy : x + (ell : ℤ) • z ∉ E := fun h ↦ hx (hm.mp h)
      rw [setIndicator, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  have hconvperiod : ScalarPeriodic ell (tileConv F (setIndicator A)) := by
    intro x z
    rw [htile, htile, hEindicator x z]
  obtain ⟨D⟩ := exists_structureDecomposition hd hell hzero hconvperiod
  have heraseCard : (F.erase 0).card = F.card - 1 :=
    Finset.card_erase_of_mem hzero
  have heraseNonempty : (F.erase 0).Nonempty := by
    apply Finset.card_pos.mp
    rw [heraseCard]
    omega
  let nz : ↥(F.erase 0) → NonzeroLattice d := fun f ↦
    ⟨(f : Lattice d), Finset.ne_of_mem_erase f.property⟩
  let classOf : ↥(F.erase 0) → DirectionClass d := fun f ↦
    Quotient.mk _ (nz f)
  let classes : Finset (DirectionClass d) := Finset.univ.image classOf
  have hclassesNonempty : classes.Nonempty := by
    obtain ⟨f, hf⟩ := heraseNonempty
    exact ⟨classOf ⟨f, hf⟩, by simp [classes]⟩
  let classIndex : ↥(F.erase 0) → ↥classes := fun f ↦
    ⟨classOf f, by simp [classes]⟩
  let memberSet (c : ↥classes) : Finset (Lattice d) :=
    (Finset.univ.filter fun f : ↥(F.erase 0) ↦ classIndex f = c).image
      Subtype.val
  have hmemberNonempty (c : ↥classes) : (memberSet c).Nonempty := by
    have hc := c.property
    dsimp [classes] at hc
    obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hc
    refine ⟨f.1, ?_⟩
    dsimp [memberSet]
    exact Finset.mem_image.mpr ⟨f, by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by
        apply Subtype.ext
        exact hf⟩, rfl⟩
  have hmemberNe (c : ↥classes) (f : Lattice d) (hf : f ∈ memberSet c) :
      f ≠ 0 := by
    obtain ⟨fsub, _, rfl⟩ := Finset.mem_image.mp hf
    exact Finset.ne_of_mem_erase fsub.property
  have hmemberComm (c : ↥classes) (u : Lattice d) (hu : u ∈ memberSet c)
      (v : Lattice d) (hv : v ∈ memberSet c) : Commensurable u v := by
    obtain ⟨usub, husub, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨vsub, hvsub, rfl⟩ := Finset.mem_image.mp hv
    have huc : classOf usub = c.1 :=
      congrArg Subtype.val (Finset.mem_filter.mp husub).2
    have hvc : classOf vsub = c.1 :=
      congrArg Subtype.val (Finset.mem_filter.mp hvsub).2
    have hquot : classOf usub = classOf vsub := huc.trans hvc.symm
    exact Quotient.eq_iff_equiv.mp hquot
  have hcommon (c : ↥classes) :=
    exists_commonMultiple_of_pairwise_commensurable
      (hmemberNonempty c) (hmemberNe c) (hmemberComm c)
  let common (c : ↥classes) : Lattice d := Classical.choose (hcommon c)
  have hcommonSpec (c : ↥classes) :
      common c ≠ 0 ∧
      (∀ f ∈ memberSet c, ∃ z : ℤ, z ≠ 0 ∧ common c = z • f) ∧
      l1Norm (common c) ≤ ∏ f ∈ memberSet c, l1Norm f ∧
      euclideanNorm (common c) ≤
        ∏ f ∈ memberSet c, euclideanNorm f :=
    Classical.choose_spec (hcommon c)
  let equivFin := Fintype.equivFin ↥classes
  let direction : Fin (Fintype.card ↥classes) → Lattice d :=
    fun j ↦ common (equivFin.symm j)
  let groupedPhi : Fin (Fintype.card ↥classes) → Lattice d → ℝ := fun j x ↦
    ∑ f ∈ Finset.univ.filter
      (fun f : ↥(F.erase 0) ↦ classIndex f = equivFin.symm j), D.phi f x
  have hgroupSum (x : Lattice d) :
      (∑ j : Fin (Fintype.card ↥classes), groupedPhi j x) =
        ∑ f : ↥(F.erase 0), D.phi f x := by
    rw [show (∑ j : Fin (Fintype.card ↥classes), groupedPhi j x) =
        ∑ c : ↥classes,
          ∑ f ∈ Finset.univ.filter
            (fun f : ↥(F.erase 0) ↦ classIndex f = c), D.phi f x by
      apply Fintype.sum_equiv equivFin.symm
      intro c
      rfl]
    simpa using Finset.sum_fiberwise
      (Finset.univ : Finset ↥(F.erase 0))
      classIndex
      (fun f ↦ D.phi f x)
  have hsumLe (x : Lattice d) : ∑ j, groupedPhi j x ≤ k := by
    rw [hgroupSum]
    have hdecomp := D.decomposition x
    rw [htile x] at hdecomp
    simp only [Int.cast_mul, Int.cast_natCast] at hdecomp
    have hA0 : (0 : ℝ) ≤ ((setIndicator A x : ℤ) : ℝ) := by
      by_cases hx : x ∈ A <;> simp [setIndicator, hx]
    have hE1 : ((setIndicator E x : ℤ) : ℝ) ≤ 1 := by
      by_cases hx : x ∈ E <;> simp [setIndicator, hx]
    nlinarith [hkReal]
  refine ⟨{
    numberOfDirections := Fintype.card ↥classes
    number_pos := Fintype.card_pos_iff.mpr ⟨⟨_, hclassesNonempty.choose_spec⟩⟩
    number_le := by
      rw [Fintype.card_coe]
      calc
        classes.card ≤ (Finset.univ : Finset ↥(F.erase 0)).card :=
          Finset.card_image_le
        _ = (F.erase 0).card := by simp
        _ = F.card - 1 := heraseCard
    direction := direction
    direction_ne_zero := fun j ↦ (hcommonSpec (equivFin.symm j)).1
    pairwise_incommensurable := ?_
    phi := groupedPhi
    phi_nonneg := ?_
    phi_le_level := ?_
    phi_periodic := ?_
    decomposition := ?_
    sum_phi_le := hsumLe
    direction_from_tile := ?_
    product_direction_l1_bound := ?_
    product_direction_euclidean_bound := ?_ }⟩
  · intro i j hij hcomm
    let ci := equivFin.symm i
    let cj := equivFin.symm j
    obtain ⟨fi, hfi⟩ := hmemberNonempty ci
    obtain ⟨fj, hfj⟩ := hmemberNonempty cj
    obtain ⟨zi, hzi, hi⟩ := (hcommonSpec ci).2.1 fi hfi
    obtain ⟨zj, hzj, hj⟩ := (hcommonSpec cj).2.1 fj hfj
    have hcfi : Commensurable (common ci) fi :=
      commensurable_of_nonzero_multiple hzi hi
    have hcfj : Commensurable (common cj) fj :=
      commensurable_of_nonzero_multiple hzj hj
    have hfiCommonj : Commensurable fi (common cj) :=
      commensurable_trans_nonzero (hmemberNe ci fi hfi)
        (hcommonSpec ci).1 (hcommonSpec cj).1
        (commensurable_symm hcfi) hcomm
    have hfifj : Commensurable fi fj :=
      commensurable_trans_nonzero (hmemberNe ci fi hfi)
        (hcommonSpec cj).1 (hmemberNe cj fj hfj) hfiCommonj hcfj
    obtain ⟨fisub, hfisub, rfl⟩ := Finset.mem_image.mp hfi
    obtain ⟨fjsub, hfjsub, rfl⟩ := Finset.mem_image.mp hfj
    have hclass : classOf fisub = classOf fjsub :=
      Quotient.sound hfifj
    have hci : classOf fisub = ci.1 :=
      congrArg Subtype.val (Finset.mem_filter.mp hfisub).2
    have hcj : classOf fjsub = cj.1 :=
      congrArg Subtype.val (Finset.mem_filter.mp hfjsub).2
    have hcicj : ci = cj := Subtype.ext (hci ▸ hcj ▸ hclass)
    exact hij (equivFin.symm.injective hcicj)
  · intro j x
    exact Finset.sum_nonneg fun f _ ↦ D.phi_nonneg f x
  · intro j x
    calc
      groupedPhi j x ≤ ∑ f : ↥(F.erase 0), D.phi f x := by
        dsimp [groupedPhi]
        exact Finset.sum_le_univ_sum_of_nonneg fun f ↦ D.phi_nonneg f x
      _ = ∑ j, groupedPhi j x := (hgroupSum x).symm
      _ ≤ k := hsumLe x
  · intro j x
    apply Finset.sum_congr rfl
    intro f hf
    let c := equivFin.symm j
    have hfclassIndex : classIndex f = c := (Finset.mem_filter.mp hf).2
    have hfclass : classOf f = c.1 := congrArg Subtype.val hfclassIndex
    have hfmem : (f : Lattice d) ∈ memberSet c := by
      exact Finset.mem_image.mpr ⟨f, by simp [hfclassIndex], rfl⟩
    obtain ⟨z, _, hz⟩ := (hcommonSpec c).2.1 f hfmem
    have hp := (D.phi_periodic f).zsmul z
    have hper : z • ((indicatorDilationModulus ell F.card : ℤ) •
        (f : Lattice d)) =
        (indicatorDilationModulus ell F.card : ℤ) • common c := by
      rw [hz]
      module
    change D.phi f
      (x + (indicatorDilationModulus ell F.card : ℤ) • common c) = D.phi f x
    rw [← hper]
    exact hp x
  · intro x
    rw [hgroupSum]
    have hD := D.decomposition x
    rw [htile x] at hD
    simpa only [Int.cast_mul, Int.cast_natCast] using hD
  · intro j
    let c := equivFin.symm j
    obtain ⟨f, hf⟩ := hmemberNonempty c
    obtain ⟨z, _, hz⟩ := (hcommonSpec c).2.1 f hf
    refine ⟨f, ?_, hmemberNe c f hf, z, ?_⟩
    · obtain ⟨fsub, hfsub, rfl⟩ := Finset.mem_image.mp hf
      exact (Finset.mem_erase.mp fsub.property).2
    · exact hz
  · have hmemberProd (c : ↥classes) :
        (∏ f ∈ memberSet c, l1Norm f) =
          ∏ f ∈ Finset.univ.filter
            (fun f : ↥(F.erase 0) ↦ classIndex f = c),
              l1Norm (f : Lattice d) := by
      dsimp [memberSet]
      rw [Finset.prod_image]
      intro a _ b _ hab
      exact Subtype.ext hab
    have hpartition :
        (∏ c : ↥classes, ∏ f ∈ memberSet c, l1Norm f) =
          ∏ f : ↥(F.erase 0), l1Norm (f : Lattice d) := by
      simp_rw [hmemberProd]
      simpa using Finset.prod_fiberwise
        (Finset.univ : Finset ↥(F.erase 0))
        classIndex
        (fun f ↦ l1Norm (f : Lattice d))
    rw [show (∏ j : Fin (Fintype.card ↥classes), l1Norm (direction j)) =
        ∏ c : ↥classes, l1Norm (common c) by
      exact Fintype.prod_equiv equivFin.symm _ _ fun _ ↦ rfl]
    calc
      (∏ c : ↥classes, l1Norm (common c)) ≤
          ∏ c : ↥classes, ∏ f ∈ memberSet c, l1Norm f :=
        Finset.prod_le_prod' fun c _ ↦ (hcommonSpec c).2.2.1
      _ = ∏ f : ↥(F.erase 0), l1Norm (f : Lattice d) := hpartition
      _ ≤ ∏ _f : ↥(F.erase 0), l1Diameter F :=
        Finset.prod_le_prod' fun f _ ↦
          mem_tile_norm_le_diameter hzero (Finset.mem_erase.mp f.property).2
      _ = l1Diameter F ^ (F.card - 1) := by
        simp [heraseCard]
  · have hmemberProd (c : ↥classes) :
        (∏ f ∈ memberSet c, euclideanNorm f) =
          ∏ f ∈ Finset.univ.filter
            (fun f : ↥(F.erase 0) ↦ classIndex f = c),
              euclideanNorm (f : Lattice d) := by
      dsimp [memberSet]
      rw [Finset.prod_image]
      intro a _ b _ hab
      exact Subtype.ext hab
    have hpartition :
        (∏ c : ↥classes, ∏ f ∈ memberSet c, euclideanNorm f) =
          ∏ f : ↥(F.erase 0), euclideanNorm (f : Lattice d) := by
      simp_rw [hmemberProd]
      simpa using Finset.prod_fiberwise
        (Finset.univ : Finset ↥(F.erase 0))
        classIndex
        (fun f ↦ euclideanNorm (f : Lattice d))
    rw [show (∏ j : Fin (Fintype.card ↥classes), euclideanNorm (direction j)) =
        ∏ c : ↥classes, euclideanNorm (common c) by
      exact Fintype.prod_equiv equivFin.symm _ _ fun _ ↦ rfl]
    calc
      (∏ c : ↥classes, euclideanNorm (common c)) ≤
          ∏ c : ↥classes, ∏ f ∈ memberSet c, euclideanNorm f :=
        Finset.prod_le_prod
          (fun c _ ↦ norm_nonneg _)
          (fun c _ ↦ (hcommonSpec c).2.2.2)
      _ = ∏ f : ↥(F.erase 0), euclideanNorm (f : Lattice d) := hpartition
      _ ≤ ∏ _f : ↥(F.erase 0), euclideanDiameter F :=
        Finset.prod_le_prod
          (fun f _ ↦ norm_nonneg _)
          (fun f _ ↦ mem_tile_euclideanNorm_le_diameter hzero
            (Finset.mem_erase.mp f.property).2)
      _ = euclideanDiameter F ^ (F.card - 1) := by
        simp [heraseCard]

/-- The grouped decomposition's dilation modulus satisfies the explicit bound. -/
theorem grouped_q_bound {ell : ℕ} {F : Finset (Lattice d)} :
    indicatorDilationModulus ell F.card ≤ ell * 4 ^ (2 * F.card) := by
  simpa [indicatorDilationModulus] using
    dilationModulus_le_explicit ell 1 F.card

/-- The grouped decomposition identity reduces modulo one to the original
indicator of the tiling set. -/
theorem structure_decomposition_mod_one
    {F : Finset (Lattice d)} {A E : Set (Lattice d)} {ell k : ℕ}
    (D : GroupedStructureDecomposition F A E ell k) (x : Lattice d) :
    (∑ j, ((D.phi j x) : AddCircle (1 : ℝ))) = 0 := by
  have hcoe (s : Finset (Fin D.numberOfDirections)) :
      (∑ j ∈ s, ((D.phi j x) : AddCircle (1 : ℝ))) =
        ((∑ j ∈ s, D.phi j x : ℝ) : AddCircle (1 : ℝ)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, ih, AddCircle.coe_add]
  change ∑ j ∈ Finset.univ, ((D.phi j x) : AddCircle (1 : ℝ)) = 0
  rw [hcoe]
  have hsum : ∑ j, D.phi j x =
      (k : ℝ) * ((setIndicator E x : ℤ) : ℝ) -
        ((setIndicator A x : ℤ) : ℝ) := by
    linarith [D.decomposition x]
  rw [hsum]
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨(k : ℤ) * setIndicator E x - setIndicator A x, ?_⟩
  norm_num

/-- In one dimension, a bounded integer tiling function has the universal
period determined by the tile (Paper Corollary 3.5). -/
theorem universal_period_one_dimensional
    {F : Finset ℤ} {A : Set ℤ} {ell : ℕ}
    (hell : 0 < ell) (hzero : 0 ∈ F)
    (hperiod : Function.Periodic
      (tileConv F (setIndicator A)) (ell : ℤ)) :
    Function.Periodic (setIndicator A) (universalPeriod1D ell F : ℤ) := by
  classical
  let e : Lattice 1 ≃+ ℤ := AddEquiv.piUnique fun _ : Fin 1 ↦ ℤ
  let F' : Finset (Lattice 1) := F.image e.symm
  let A' : Set (Lattice 1) := e ⁻¹' A
  have hindicator (x : Lattice 1) : setIndicator A' x = setIndicator A (e x) := by
    by_cases hx : e x ∈ A <;> simp [setIndicator, A', hx]
  have hconv (x : Lattice 1) :
      tileConv F' (setIndicator A') x = tileConv F (setIndicator A) (e x) := by
    simp only [tileConv, F']
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro f _
      rw [hindicator]
      congr 1
    · exact fun _ _ _ _ h ↦ e.symm.injective h
  have hzero' : 0 ∈ F' := by
    exact Finset.mem_image.mpr ⟨0, hzero, by simp⟩
  have hconvperiod : ScalarPeriodic ell (tileConv F' (setIndicator A')) := by
    intro x z
    rw [hconv, hconv]
    have hp := hperiod.zsmul (e z)
    rw [show e (x + (ell : ℤ) • z) =
        e x + (e z) • (ell : ℤ) by
      rw [map_add, map_zsmul]
      simp [mul_comm]]
    exact hp (e x)
  obtain ⟨D⟩ := exists_structureDecomposition (d := 1)
    Nat.zero_lt_one hell hzero' hconvperiod
  let q := indicatorDilationModulus ell F.card
  let n := (F.erase 0).lcm Int.natAbs
  let P := universalPeriod1D ell F
  have hcard : F'.card = F.card := by
    dsimp [F']
    exact Finset.card_image_iff.mpr e.symm.injective.injOn
  have hqF' : indicatorDilationModulus ell F'.card = q := by
    rw [hcard]
  have hdecomp (x : ℤ) :
      ((setIndicator A x : ℤ) : ℝ) =
        ((tileConv F (setIndicator A) x : ℤ) : ℝ) -
          ∑ f : ↥(F'.erase 0), D.phi f (e.symm x) := by
    have hD := D.decomposition (e.symm x)
    rw [hindicator, hconv] at hD
    simpa using hD
  have hP : P = q * n := by
    rfl
  have hellP : ell ∣ P := by
    rw [hP]
    exact (ell_dvd_dilationModulus ell 1 F.card).trans (dvd_mul_right q n)
  have hconvP : Function.Periodic (tileConv F (setIndicator A)) (P : ℤ) := by
    obtain ⟨t, ht⟩ := hellP
    have hp := hperiod.zsmul (t : ℤ)
    have hperiodEq : (P : ℤ) = (t : ℤ) • (ell : ℤ) := by
      rw [ht]
      simp [mul_comm]
    rw [hperiodEq]
    exact hp
  have hphiP (f' : ↥(F'.erase 0)) :
      Function.Periodic (fun x : ℤ ↦ D.phi f' (e.symm x)) (P : ℤ) := by
    have hf'F' : (f' : Lattice 1) ∈ F' := (Finset.mem_erase.mp f'.property).2
    obtain ⟨f, hfF, hff'⟩ := Finset.mem_image.mp hf'F'
    have hfne : f ≠ 0 := by
      intro hfzero
      subst f
      exact Finset.ne_of_mem_erase f'.property (by simpa using hff'.symm)
    have hfErase : f ∈ F.erase 0 := Finset.mem_erase.mpr ⟨hfne, hfF⟩
    have hfdvdNat : Int.natAbs f ∣ n := by
      exact Finset.dvd_lcm hfErase
    have hfdvdInt : f ∣ (n : ℤ) := by
      rw [← Int.natAbs_dvd]
      exact_mod_cast hfdvdNat
    obtain ⟨z, hz⟩ := hfdvdInt
    have hperiodF := (D.phi_periodic f').zsmul z
    have hvec : e.symm (P : ℤ) =
        z • ((indicatorDilationModulus ell F'.card : ℤ) •
          (f' : Lattice 1)) := by
      have hPz : (P : ℤ) = (q : ℤ) * (n : ℤ) := by exact_mod_cast hP
      have heff : e (f' : Lattice 1) = f := by
        rw [← hff']
        simp
      apply e.injective
      simp only [e.apply_symm_apply, map_zsmul]
      rw [hPz, hz, hqF', heff]
      ring
    intro x
    change D.phi f' (e.symm (x + (P : ℤ))) = D.phi f' (e.symm x)
    rw [e.symm.map_add, hvec]
    exact hperiodF (e.symm x)
  have hsumP : Function.Periodic
      (fun x : ℤ ↦ ∑ f : ↥(F'.erase 0), D.phi f (e.symm x)) (P : ℤ) := by
    intro x
    apply Finset.sum_congr rfl
    intro f _
    exact hphiP f x
  intro x
  have hleft := hdecomp (x + P)
  have hright := hdecomp x
  rw [hconvP x] at hleft
  have hsumx := hsumP x
  change (∑ f : ↥(F'.erase 0), D.phi f (e.symm (x + P))) =
    ∑ f : ↥(F'.erase 0), D.phi f (e.symm x) at hsumx
  rw [hsumx] at hleft
  change setIndicator A (x + (P : ℤ)) = setIndicator A x
  have hcastEq :
      ((setIndicator A (x + (P : ℤ)) : ℤ) : ℝ) =
        ((setIndicator A x : ℤ) : ℝ) := by linarith
  exact_mod_cast hcastEq

end TranslationalTilings
