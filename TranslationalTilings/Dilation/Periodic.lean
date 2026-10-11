import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.FiniteDifference
import TranslationalTilings.LatticeGeometry

/-!
# Periodic dilation

The three parts of the paper's dilation lemma: prime dilations, dilations
coprime to all small primes, and dilations congruent to one modulo a lattice
period together with the required finite Følner boxes.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real symmDiff

namespace TranslationalTilings

/-- Pointwise integral dilation of a finite lattice tile. -/
def dilate {d : ℕ} (r : ℕ)
    (F : Finset (Lattice d)) : Finset (Lattice d) :=
  F.image fun f ↦ (r : ℤ) • f

/-- A two-sided integer bound. -/
def BoundedBetween {α : Type*} (lo hi : ℤ) (g : α → ℤ) : Prop :=
  ∀ x, lo ≤ g x ∧ g x ≤ hi

/-- Existence of some two-sided integer bound. -/
def IntegerBounded {α : Type*} (g : α → ℤ) : Prop :=
  ∃ lo hi : ℤ, BoundedBetween lo hi g

/-- Width of an integer interval, represented as a natural number. -/
def oscillationBound (lo hi : ℤ) : ℕ := Int.natAbs (hi - lo)

/-- Multiples of `ell` whose coefficients lie between `-R` and `R`. -/
noncomputable def centeredMultipleInterval (ell R : ℕ) : Finset ℤ :=
  (Finset.Icc (-(R : ℤ)) R).image fun z ↦ (ell : ℤ) * z

/-- The centered box in the scalar lattice `ell · ℤ^d`. -/
noncomputable def folnerBox {d : ℕ}
    (ell R : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset fun _ : Fin d ↦ centeredMultipleInterval ell R

/-- A finite average along a ray, used in the structure theorem. -/
noncomputable def rayAverage {d : ℕ} (q N : ℕ) (f : Lattice d)
    (A : Set (Lattice d)) : Lattice d → ℚ :=
  fun x ↦ (N : ℚ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
    (setIndicator A (x - ((1 + n * q : ℕ) : ℤ) • f) : ℚ)

/-- Dilating a nonempty finite tile by zero gives the singleton origin. -/
theorem dilate_zero {d : ℕ} {F : Finset (Lattice d)}
    (hF : F.Nonempty) : dilate 0 F = {0} := by
  ext x
  constructor
  · rw [dilate, Finset.mem_image]
    rintro ⟨f, -, rfl⟩
    simp
  · intro hx
    simp only [Finset.mem_singleton] at hx
    subst x
    obtain ⟨f, hf⟩ := hF
    exact Finset.mem_image.mpr ⟨f, hf, by simp⟩

/-- Zero dilation is empty exactly when the original tile is empty. -/
theorem dilate_zero_eq_empty_iff {d : ℕ} (F : Finset (Lattice d)) :
    dilate 0 F = ∅ ↔ F = ∅ := by
  constructor
  · intro h
    by_contra hF
    have hne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF
    rw [dilate_zero hne] at h
    simp at h
  · rintro rfl
    simp [dilate]

/-- Dilation by one fixes a finite tile. -/
theorem dilate_one {d : ℕ} (F : Finset (Lattice d)) : dilate 1 F = F := by
  simp [dilate]

/-- Successive dilations multiply their scale factors. -/
theorem dilate_mul {d r s : ℕ} (F : Finset (Lattice d)) :
    dilate r (dilate s F) = dilate (r * s) F := by
  ext x
  simp only [dilate, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨f, hf, ?_⟩
    simp [mul_smul, Nat.cast_mul]
  · rintro ⟨f, hf, rfl⟩
    refine ⟨(s : ℤ) • f, ⟨f, hf, rfl⟩, ?_⟩
    simp [mul_smul, Nat.cast_mul]

/-- Positive dilation preserves the cardinality of a finite lattice tile. -/
theorem card_dilate {d r : ℕ} {F : Finset (Lattice d)} (hr : 0 < r) :
    (dilate r F).card = F.card := by
  apply Finset.card_image_iff.mpr
  intro x _ y _ hxy
  apply_fun fun z i ↦ z i at hxy
  funext i
  have hrz : (r : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hi := congrFun hxy i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact mul_left_cancel₀ hrz hi

/-- In prime characteristic, the Frobenius power of a tile is its prime dilation. -/
theorem tileMonoidAlgebra_frobenius_mod_prime
    {d p : ℕ} (F : Finset (Lattice d)) (hp : p.Prime) :
    tileMonoidAlgebra (ZMod p) (Lattice d) F ^ p =
      tileMonoidAlgebra (ZMod p) (Lattice d) (dilate p F) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CharP (AddMonoidAlgebra (ZMod p) (Lattice d)) p :=
    charP_of_injective_algebraMap' (ZMod p) p
  rw [tileMonoidAlgebra, sum_pow_char]
  simp only [AddMonoidAlgebra.single_pow, one_pow]
  rw [tileMonoidAlgebra]
  simp only [dilate]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro f _
    rw [nsmul_eq_mul]
    norm_cast
  · intro x _ y _ hxy
    apply_fun fun z i ↦ z i at hxy
    funext i
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hi := congrFun hxy i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    exact mul_left_cancel₀ hpz hi

/-- Translation by `a`, bundled as a linear endomorphism of the function space. -/
private def backwardShift {G R : Type*} [AddCommGroup G] [CommRing R]
    (a : G) : Module.End R (G → R) where
  toFun f x := f (x - a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The commuting translation representation of an additive group. -/
private def backwardShiftMonoidHom {G R : Type*}
    [AddCommGroup G] [CommRing R] :
    Multiplicative G →* Module.End R (G → R) where
  toFun a := backwardShift a.toAdd
  map_one' := by
    ext f x
    simp [backwardShift]
  map_mul' a b := by
    ext f x
    change f (x - (a.toAdd + b.toAdd)) = f ((x - a.toAdd) - b.toAdd)
    congr 1
    abel

/-- The regular translation representation of the additive monoid algebra. -/
private noncomputable def convolutionRepresentation (G R : Type*)
    [AddCommGroup G] [CommRing R] :
    AddMonoidAlgebra R G →ₐ[R] Module.End R (G → R) :=
  AddMonoidAlgebra.lift R (Module.End R (G → R)) G
    (backwardShiftMonoidHom (G := G) (R := R))

private theorem convolutionRepresentation_tile_apply
    {G R : Type*} [AddCommGroup G] [CommRing R]
    (F : Finset G) (g : G → R) :
    convolutionRepresentation G R (tileMonoidAlgebra R G F) g = tileConv F g := by
  funext x
  simp [convolutionRepresentation, tileMonoidAlgebra,
    backwardShiftMonoidHom, backwardShift, tileConv]

private theorem tileConv_const {G R : Type*}
    [AddCommGroup G] [CommRing R] (F : Finset G) (c : R) :
    tileConv F (fun _ ↦ c) = fun _ ↦ (F.card : R) * c := by
  funext x
  simp [tileConv, nsmul_eq_mul]

private theorem convolutionRepresentation_pow_const
    {G R : Type*} [AddCommGroup G] [CommRing R]
    (F : Finset G) (c : R) (n : ℕ) :
    (convolutionRepresentation G R (tileMonoidAlgebra R G F) ^ n)
        (fun _ ↦ c) = fun _ ↦ (F.card : R) ^ n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, convolutionRepresentation_tile_apply,
        ih, tileConv_const]
      funext x
      ring

private theorem tileConv_dilate_mod_prime
    {d p : ℕ} (F : Finset (Lattice d)) (g : Lattice d → ℤ)
    (k : ℤ) (hp : p.Prime)
    (hconv : tileConv F g = fun _ ↦ k)
    (hFpos : 0 < F.card) (hcard : F.card < p) :
    ∀ x, ((tileConv (dilate p F) g x : ℤ) : ZMod p) = (k : ZMod p) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let gz : Lattice d → ZMod p := fun x ↦ (g x : ZMod p)
  let T := convolutionRepresentation (Lattice d) (ZMod p)
  have hTg : T (tileMonoidAlgebra (ZMod p) (Lattice d) F) gz = fun _ ↦ (k : ZMod p) := by
    rw [convolutionRepresentation_tile_apply]
    funext x
    simpa [tileConv, gz] using
      congrArg (fun z : ℤ ↦ (z : ZMod p)) (congrFun hconv x)
  have hcard_ne : (F.card : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hFpos hcard
  have hfermat : (F.card : ZMod p) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hcard_ne
  intro x
  have hfrob := tileMonoidAlgebra_frobenius_mod_prime F hp
  have hop := congrArg T hfrob
  rw [map_pow] at hop
  have happ := DFunLike.congr_fun hop gz
  have hp_pos : 0 < p := hp.pos
  have hp_eq : p = (p - 1) + 1 := by omega
  have hexp :
      (T (tileMonoidAlgebra (ZMod p) (Lattice d) F) ^ p) gz =
        (T (tileMonoidAlgebra (ZMod p) (Lattice d) F) ^ ((p - 1) + 1)) gz :=
    congrArg (fun n ↦ (T (tileMonoidAlgebra (ZMod p) (Lattice d) F) ^ n) gz) hp_eq
  have hpow :
      (T (tileMonoidAlgebra (ZMod p) (Lattice d) F) ^ p) gz =
        fun _ ↦ (k : ZMod p) := by
    rw [hexp, pow_succ, Module.End.mul_apply, hTg,
      convolutionRepresentation_pow_const, hfermat]
    simp
  have hx := congrFun (happ.symm.trans hpow) x
  simpa [T, gz, convolutionRepresentation_tile_apply, tileConv] using hx

private theorem tileConv_boundedBetween {G : Type*} [AddCommGroup G]
    (F : Finset G) (g : G → ℤ) (lo hi : ℤ)
    (hbound : BoundedBetween lo hi g) (x : G) :
    (F.card : ℤ) * lo ≤ tileConv F g x ∧
      tileConv F g x ≤ (F.card : ℤ) * hi := by
  constructor
  · simpa [tileConv, nsmul_eq_mul, mul_comm] using
      Finset.sum_le_sum (s := F) (fun f _ ↦ (hbound (x - f)).1)
  · simpa [tileConv, nsmul_eq_mul, mul_comm] using
      Finset.sum_le_sum (s := F) (fun f _ ↦ (hbound (x - f)).2)

/-- Prime dilation preserves a bounded integral tiling convolution under the
required congruence condition. -/
theorem dilation_prime {d p : ℕ} {F : Finset (Lattice d)}
    {g : Lattice d → ℤ} {lo hi k : ℤ}
    (hbound : BoundedBetween lo hi g)
    (hconv : tileConv F g = fun _ ↦ k) (hp : p.Prime)
    (hlarge : oscillationBound lo hi * F.card < p) :
    tileConv (dilate p F) g = fun _ ↦ k := by
  by_cases hF : F.Nonempty
  · have hFpos : 0 < F.card := Finset.card_pos.mpr hF
    by_cases hosc : oscillationBound lo hi = 0
    · have hlohi : lo = hi := by
        have : hi - lo = 0 := Int.natAbs_eq_zero.mp hosc
        omega
      have hg : g = fun _ ↦ lo := by
        funext x
        exact le_antisymm ((hbound x).2.trans_eq hlohi.symm) (hbound x).1
      rw [hg] at hconv ⊢
      funext x
      have hcard := card_dilate (F := F) hp.pos
      simpa [tileConv, nsmul_eq_mul, hcard] using congrFun hconv x
    · have hoscpos : 0 < oscillationBound lo hi := Nat.pos_of_ne_zero hosc
      have hcardlt : F.card < p :=
        (Nat.le_mul_of_pos_left F.card hoscpos).trans_lt hlarge
      funext x
      have hmod := tileConv_dilate_mod_prime F g k hp hconv hFpos hcardlt x
      have hpdiv : (p : ℤ) ∣ k - tileConv (dilate p F) g x :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hmod
      have hlohi : lo ≤ hi := (hbound 0).1.trans (hbound 0).2
      have hkbound := tileConv_boundedBetween F g lo hi hbound 0
      rw [congrFun hconv 0] at hkbound
      have hdbound := tileConv_boundedBetween (dilate p F) g lo hi hbound x
      rw [card_dilate (F := F) hp.pos] at hdbound
      have habs : |k - tileConv (dilate p F) g x| ≤
          ((oscillationBound lo hi * F.card : ℕ) : ℤ) := by
        rw [abs_le]
        have hosc_cast : ((oscillationBound lo hi : ℕ) : ℤ) = hi - lo := by
          simp [oscillationBound, Int.natAbs_of_nonneg (sub_nonneg.mpr hlohi)]
        simp only [Nat.cast_mul, hosc_cast]
        constructor <;> nlinarith [hkbound.1, hkbound.2, hdbound.1, hdbound.2]
      have hnatAbs : Int.natAbs (k - tileConv (dilate p F) g x) < p := by
        have hle : Int.natAbs (k - tileConv (dilate p F) g x) ≤
            oscillationBound lo hi * F.card := by
          rw [← Int.natCast_natAbs] at habs
          exact_mod_cast habs
        exact hle.trans_lt hlarge
      have hzero : k - tileConv (dilate p F) g x = 0 := by
        apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hpdiv
        simpa using hnatAbs
      omega
  · have hempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    subst F
    simpa [dilate, tileConv] using hconv

/-- Dilation by a scale coprime to the controlling factorial preserves the
tiling convolution. -/
theorem dilation_coprime {d r : ℕ} {F : Finset (Lattice d)}
    {g : Lattice d → ℤ} {lo hi k : ℤ}
    (hbound : BoundedBetween lo hi g)
    (hconv : tileConv F g = fun _ ↦ k) (hr : 0 < r)
    (hcop : Nat.Coprime r
      (primorial (oscillationBound lo hi * F.card))) :
    tileConv (dilate r F) g = fun _ ↦ k := by
  induction r using Nat.strong_induction_on generalizing F with
  | h r ih =>
      by_cases hrone : r = 1
      · subst r
        simpa [dilate_one] using hconv
      · obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd hrone
        have hpbig : oscillationBound lo hi * F.card < p :=
          prime_factor_gt_of_coprime_primorial hcop hp hpr
        have hpconv : tileConv (dilate p F) g = fun _ ↦ k :=
          dilation_prime hbound hconv hp hpbig
        obtain ⟨s, hrs⟩ := hpr
        have hspos : 0 < s := by
          subst r
          exact Nat.pos_of_mul_pos_left hr
        have hplt : 1 < p := hp.one_lt
        have hslt : s < r := by
          rw [hrs]
          exact lt_mul_of_one_lt_left hspos hplt
        have hsdiv : s ∣ r := by
          exact ⟨p, by simpa [mul_comm] using hrs⟩
        have hcop_s : Nat.Coprime s
            (primorial (oscillationBound lo hi * (dilate p F).card)) := by
          rw [card_dilate (F := F) hp.pos]
          exact hcop.coprime_dvd_left hsdiv
        have hsconv := ih s hslt (F := dilate p F) hpconv hspos hcop_s
        rw [dilate_mul] at hsconv
        rw [hrs, mul_comm]
        exact hsconv

private theorem centeredMultipleInterval_card {ell R : ℕ} (hell : 0 < ell) :
    (centeredMultipleInterval ell R).card = 2 * R + 1 := by
  rw [centeredMultipleInterval, Finset.card_image_iff.mpr]
  · rw [Int.card_Icc]
    omega
  · intro x _ y _ hxy
    have hellz : (ell : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hell)
    exact mul_left_cancel₀ hellz hxy

/-- The centered Følner box has the expected product cardinality. -/
theorem folnerBox_card {d ell R : ℕ} (hell : 0 < ell) :
    (folnerBox (d := d) ell R).card = (2 * R + 1) ^ d := by
  rw [folnerBox, Fintype.card_piFinset]
  simp [centeredMultipleInterval_card hell]

private noncomputable def intCube {d : ℕ} (R : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(R : ℤ)) R

private theorem intCube_card {d R : ℕ} :
    (intCube (d := d) R).card = (2 * R + 1) ^ d := by
  rw [intCube, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ]
  rw [Fintype.card_fin]
  congr 1
  omega

private theorem mem_intCube_iff {d R : ℕ} {x : Lattice d} :
    x ∈ intCube (d := d) R ↔ ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R := by
  simp [intCube]

private theorem intCube_translate_boundary {d : ℕ} (z : Lattice d) :
    ∃ C : ℕ, ∀ R,
      (intCube (d := d) R ∆
        (intCube (d := d) R).image (fun x ↦ x + z)).card * (2 * R + 1) ≤
          C * (intCube (d := d) R).card := by
  let M : ℕ := l1Norm z
  let C : ℕ := 2 * (2 * M + 1) +
    4 * M * d * (2 * M + 1) ^ (d - 1)
  refine ⟨C, fun R ↦ ?_⟩
  have hzM (i : Fin d) : Int.natAbs (z i) ≤ M := by
    dsimp [M, l1Norm]
    exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (Int.natAbs (z j)))
      (Finset.mem_univ i)
  have hzBounds (i : Fin d) : -(M : ℤ) ≤ z i ∧ z i ≤ M := by
    have habs : |z i| ≤ (M : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hzM i
    exact abs_le.mp habs
  by_cases hd : d = 0
  · subst d
    have hz : z = 0 := Subsingleton.elim _ _
    subst z
    have hshift : (fun x : Lattice 0 ↦ x + 0) = id := by
      funext x
      exact Subsingleton.elim _ _
    rw [hshift]
    simp
  have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  rw [intCube_card]
  by_cases hRM : R < M
  · have hsymm :
        (intCube (d := d) R ∆
          (intCube (d := d) R).image (fun x ↦ x + z)).card ≤
            2 * (intCube (d := d) R).card := by
      calc
        _ ≤ (intCube (d := d) R ∪
            (intCube (d := d) R).image (fun x ↦ x + z)).card :=
          Finset.card_le_card Finset.symmDiff_subset_union
        _ ≤ (intCube (d := d) R).card +
            ((intCube (d := d) R).image (fun x ↦ x + z)).card :=
          Finset.card_union_le ..
        _ = 2 * (intCube (d := d) R).card := by
          rw [Finset.card_image_iff.mpr]
          · omega
          · exact fun _ _ _ _ h ↦ add_right_cancel h
    have hside : 2 * R + 1 ≤ 2 * M + 1 := by omega
    dsimp [C]
    calc
      _ ≤ (2 * (intCube (d := d) R).card) * (2 * R + 1) :=
        Nat.mul_le_mul_right _ hsymm
      _ ≤ (2 * (2 * M + 1)) * (intCube (d := d) R).card := by
        calc
          (2 * (intCube (d := d) R).card) * (2 * R + 1) =
              2 * ((2 * R + 1) * (intCube (d := d) R).card) := by ac_rfl
          _ ≤ 2 * ((2 * M + 1) * (intCube (d := d) R).card) :=
            Nat.mul_le_mul_left 2
              (Nat.mul_le_mul_right (intCube (d := d) R).card hside)
          _ = (2 * (2 * M + 1)) * (intCube (d := d) R).card := by ac_rfl
      _ ≤ (2 * (2 * M + 1) +
          4 * M * d * (2 * M + 1) ^ (d - 1)) *
          (intCube (d := d) R).card :=
        Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ = _ := by rw [intCube_card]
  · have hMR : M ≤ R := Nat.le_of_not_gt hRM
    let outer := intCube (d := d) (R + M)
    let inner := intCube (d := d) (R - M)
    let box := intCube (d := d) R
    have hinnerBox : inner ⊆ box := by
      intro x hx
      rw [mem_intCube_iff] at hx ⊢
      intro i
      have := hx i
      constructor <;> omega
    have hinnerTranslate : inner ⊆ box.image (fun x ↦ x + z) := by
      intro x hx
      rw [mem_intCube_iff] at hx
      refine Finset.mem_image.mpr ⟨x - z, ?_, by abel⟩
      rw [mem_intCube_iff]
      intro i
      have hxi := hx i
      have hzi := hzBounds i
      constructor
      · change -(R : ℤ) ≤ x i - z i
        omega
      · change x i - z i ≤ (R : ℤ)
        omega
    have hboxOuter : box ⊆ outer := by
      intro x hx
      rw [mem_intCube_iff] at hx ⊢
      intro i
      have := hx i
      constructor <;> omega
    have htranslateOuter : box.image (fun x ↦ x + z) ⊆ outer := by
      rintro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rw [mem_intCube_iff] at hy ⊢
      intro i
      have hyi := hy i
      have hzi := hzBounds i
      constructor <;> simp only [Pi.add_apply] <;> omega
    have hsubset : box ∆ box.image (fun x ↦ x + z) ⊆ outer \ inner := by
      intro x hx
      rw [Finset.mem_symmDiff] at hx
      rw [Finset.mem_sdiff]
      constructor
      · rcases hx with hx | hx
        · exact hboxOuter hx.1
        · exact htranslateOuter hx.1
      · intro hxi
        rcases hx with hx | hx
        · exact hx.2 (hinnerTranslate hxi)
        · exact hx.2 (hinnerBox hxi)
    have hcardSubset : (box ∆ box.image (fun x ↦ x + z)).card ≤
        outer.card - inner.card := by
      calc
        _ ≤ (outer \ inner).card := Finset.card_le_card hsubset
        _ = outer.card - inner.card := Finset.card_sdiff_of_subset
          (hinnerBox.trans hboxOuter)
    have hpowBound :
        ((2 * (R + M) + 1) ^ d - (2 * (R - M) + 1) ^ d) *
            (2 * R + 1) ≤
          (4 * M * d * (2 * M + 1) ^ (d - 1)) * (2 * R + 1) ^ d := by
      have hsides : 2 * (R - M) + 1 ≤ 2 * (R + M) + 1 := by omega
      have hdiff : (2 * (R + M) + 1) ^ d - (2 * (R - M) + 1) ^ d ≤
          4 * M * d * (2 * (R + M) + 1) ^ (d - 1) := by
        grind [abs_pow_sub_pow_le (α := ℤ)
          (2 * (R + M) + 1) (2 * (R - M) + 1) d]
      have houterSide : 2 * (R + M) + 1 ≤ (2 * M + 1) * (2 * R + 1) := by
        nlinarith
      have hpowers := Nat.pow_le_pow_left houterSide (d - 1)
      calc
        _ ≤ (4 * M * d * (2 * (R + M) + 1) ^ (d - 1)) *
            (2 * R + 1) := Nat.mul_le_mul_right _ hdiff
        _ ≤ (4 * M * d * ((2 * M + 1) * (2 * R + 1)) ^ (d - 1)) *
            (2 * R + 1) := by gcongr
        _ = _ := by
          rw [mul_pow]
          calc
            4 * M * d * ((2 * M + 1) ^ (d - 1) * (2 * R + 1) ^ (d - 1)) *
                (2 * R + 1) =
                4 * M * d * (2 * M + 1) ^ (d - 1) *
                  ((2 * R + 1) ^ (d - 1) * (2 * R + 1)) := by ac_rfl
            _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hdpos]
    dsimp [C]
    calc
      (box ∆ box.image (fun x ↦ x + z)).card * (2 * R + 1) ≤
          (outer.card - inner.card) * (2 * R + 1) :=
        Nat.mul_le_mul_right _ hcardSubset
      _ = ((2 * (R + M) + 1) ^ d - (2 * (R - M) + 1) ^ d) *
          (2 * R + 1) := by simp [outer, inner, intCube_card]
      _ ≤ (4 * M * d * (2 * M + 1) ^ (d - 1)) * (2 * R + 1) ^ d := hpowBound
      _ ≤ (2 * (2 * M + 1) + 4 * M * d * (2 * M + 1) ^ (d - 1)) *
          (2 * R + 1) ^ d := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- Translation changes a large Følner box by a quantitatively small symmetric difference. -/
theorem folnerBox_translate_symmDiff_ratio_bound
    {d ell : ℕ} {v : Lattice d} (hv : v ∈ scalarLattice ell) :
    ∃ C : ℕ, ∀ R,
      (folnerBox (d := d) ell R ∆
        (folnerBox (d := d) ell R).image (fun x ↦ x + v)).card *
          (2 * R + 1) ≤ C * (folnerBox (d := d) ell R).card := by
  rcases ell.eq_zero_or_pos with rfl | hell
  · have hvzero : v = 0 := by
      obtain ⟨z, hz⟩ := hv
      simpa using hz.symm
    subst v
    refine ⟨0, fun R ↦ ?_⟩
    simp
  · obtain ⟨z, hz⟩ := hv
    obtain ⟨C, hC⟩ := intCube_translate_boundary z
    refine ⟨C, fun R ↦ ?_⟩
    let scale : Lattice d → Lattice d := fun x ↦ (ell : ℤ) • x
    have hscale : Function.Injective scale := by
      intro x y hxy
      funext i
      have hi := congrFun hxy i
      have hellz : (ell : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hell)
      simp only [scale, Pi.smul_apply, smul_eq_mul] at hi
      exact mul_left_cancel₀ hellz hi
    have hbox : folnerBox (d := d) ell R = (intCube (d := d) R).image scale := by
      rw [folnerBox, centeredMultipleInterval, intCube,
        Fintype.piFinset_image (fun _ z ↦ (ell : ℤ) * z)]
      rfl
    have hvscale : v = scale z := by
      simpa [scale] using hz.symm
    have htranslate :
        (folnerBox (d := d) ell R).image (fun x ↦ x + v) =
          ((intCube (d := d) R).image (fun x ↦ x + z)).image scale := by
      rw [hbox, Finset.image_image, Finset.image_image]
      apply Finset.image_congr
      intro x _
      rw [hvscale]
      dsimp [scale]
      module
    rw [htranslate, hbox, ← Finset.image_symmDiff _ _ hscale,
      Finset.card_image_iff.mpr hscale.injOn,
      Finset.card_image_iff.mpr hscale.injOn]
    exact hC R

private theorem periodic_of_backwardDiff_eq_zero {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (h : G) (f : G → R)
    (hdiff : backwardDiff h f = 0) : Function.Periodic f h := by
  intro x
  have hx := congrFun hdiff (x + h)
  simp only [backwardDiff, Pi.zero_apply] at hx
  rw [show x + h - h = x by abel] at hx
  exact sub_eq_zero.mp hx

private theorem tileConv_dilate_apply {d r : ℕ}
    (F : Finset (Lattice d)) (g : Lattice d → ℤ) (x : Lattice d)
    (hr : 0 < r) :
    tileConv (dilate r F) g x = ∑ f ∈ F, g (x - (r : ℤ) • f) := by
  simp only [tileConv, dilate]
  rw [Finset.sum_image]
  intro a _ b _ hab
  apply_fun fun z i ↦ z i at hab
  funext i
  have hrz : (r : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hi := congrFun hab i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact mul_left_cancel₀ hrz hi

private theorem natAbs_sum_sub_sum_le_symmDiff_card
    {α : Type*} [DecidableEq α] (s t : Finset α) (φ : α → ℤ) (K : ℕ)
    (hφ : ∀ x, Int.natAbs (φ x) ≤ K) :
    Int.natAbs ((∑ x ∈ s, φ x) - ∑ x ∈ t, φ x) ≤
      2 * K * (s ∆ t).card := by
  have hdecomp :
      (∑ x ∈ s, φ x) - ∑ x ∈ t, φ x =
        (∑ x ∈ s \ t, φ x) - ∑ x ∈ t \ s, φ x := by
    have hs := Finset.sum_inter_add_sum_sdiff s t φ
    have ht := Finset.sum_inter_add_sum_sdiff t s φ
    rw [Finset.inter_comm] at ht
    omega
  rw [hdecomp]
  calc
    Int.natAbs ((∑ x ∈ s \ t, φ x) - ∑ x ∈ t \ s, φ x) ≤
        Int.natAbs (∑ x ∈ s \ t, φ x) +
          Int.natAbs (∑ x ∈ t \ s, φ x) := Int.natAbs_sub_le _ _
    _ ≤ (∑ x ∈ s \ t, Int.natAbs (φ x)) +
          ∑ x ∈ t \ s, Int.natAbs (φ x) :=
      Nat.add_le_add (Int.natAbs_sum_le _ _) (Int.natAbs_sum_le _ _)
    _ ≤ (s \ t).card * K + (t \ s).card * K := by
      gcongr
      · simpa [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul (s \ t) (fun x ↦ Int.natAbs (φ x)) K
            (fun x _ ↦ hφ x)
      · simpa [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul (t \ s) (fun x ↦ Int.natAbs (φ x)) K
            (fun x _ ↦ hφ x)
    _ ≤ (s ∆ t).card * K + (s ∆ t).card * K := by
      gcongr
      · exact Finset.symmDiff_subset_sdiff (s := s) (t := t)
      · exact Finset.symmDiff_subset_sdiff' (s := s) (t := t)
    _ = 2 * K * (s ∆ t).card := by ring

private theorem folnerBox_mem_scalarLattice {d ell R : ℕ}
    {x : Lattice d} (hx : x ∈ folnerBox (d := d) ell R) :
    x ∈ scalarLattice ell := by
  rw [folnerBox, Fintype.mem_piFinset] at hx
  have hx' (i : Fin d) : ∃ z : ℤ,
      z ∈ Finset.Icc (-(R : ℤ)) R ∧ (ell : ℤ) * z = x i := by
    simpa only [centeredMultipleInterval, Finset.mem_image] using hx i
  choose z _ hzx using hx'
  refine ⟨z, ?_⟩
  funext i
  simpa [nsmul_eq_mul] using hzx i

/-- Scalar periodicity and boundedness make the coprime dilation convolution periodic. -/
theorem dilation_periodic {d ell r : ℕ}
    {F : Finset (Lattice d)} {g : Lattice d → ℤ} {lo hi : ℤ}
    (hbound : BoundedBetween lo hi g) (hell : 0 < ell)
    (hperiod : ScalarPeriodic ell (tileConv F g)) (hr : 0 < r)
    (hmod : Nat.ModEq
      (dilationModulus ell (oscillationBound lo hi) F.card) r 1) :
    tileConv (dilate r F) g = tileConv F g := by
  classical
  have hlohi : lo ≤ hi := (hbound 0).1.trans (hbound 0).2
  have hoscDiff :
      oscillationBound (lo - hi) (hi - lo) = 2 * oscillationBound lo hi := by
    have heq : (hi - lo) - (lo - hi) = 2 * (hi - lo) := by ring
    simp only [oscillationBound, heq, Int.natAbs_mul]
    norm_num
  have hcop : Nat.Coprime r
      (primorial (2 * oscillationBound lo hi * F.card)) := by
    have hcopMod : Nat.Coprime r
        (dilationModulus ell (oscillationBound lo hi) F.card) := by
      exact hmod.gcd_eq.trans (by simp)
    exact Nat.Coprime.of_dvd_right
      (Nat.dvd_lcm_right ell
        (primorial (2 * oscillationBound lo hi * F.card))) hcopMod
  have hdilatePeriod : ScalarPeriodic ell (tileConv (dilate r F) g) := by
    intro x z
    let lambda : Lattice d := (ell : ℤ) • z
    have hboundDiff :
        BoundedBetween (lo - hi) (hi - lo) (backwardDiff lambda g) := by
      intro y
      have hy := hbound y
      have hylambda := hbound (y - lambda)
      simp only [backwardDiff]
      constructor <;> omega
    have hconvDiff : tileConv F (backwardDiff lambda g) = fun _ ↦ 0 := by
      rw [← backwardDiff_tileConv]
      apply backwardDiff_eq_zero_of_periodic
      intro y
      exact hperiod y z
    have hcopDiff : Nat.Coprime r
        (primorial (oscillationBound (lo - hi) (hi - lo) * F.card)) := by
      simpa [hoscDiff, mul_assoc] using hcop
    have hdilateDiff :
        tileConv (dilate r F) (backwardDiff lambda g) = fun _ ↦ 0 :=
      dilation_coprime hboundDiff hconvDiff hr hcopDiff
    have hbackward :
        backwardDiff lambda (tileConv (dilate r F) g) = 0 := by
      rw [backwardDiff_tileConv, hdilateDiff]
      rfl
    exact periodic_of_backwardDiff_eq_zero lambda _ hbackward x
  let H : Lattice d → ℤ :=
    fun x ↦ tileConv (dilate r F) g x - tileConv F g x
  have hHperiod : ScalarPeriodic ell H := by
    intro x z
    dsimp [H]
    rw [hdilatePeriod x z, hperiod x z]
  have hmodEll : Nat.ModEq ell r 1 :=
    hmod.of_dvd (ell_dvd_dilationModulus ell (oscillationBound lo hi) F.card)
  have honele : 1 ≤ r := hr
  have helldvd : ell ∣ r - 1 :=
    (Nat.modEq_iff_dvd' honele).mp hmodEll.symm
  obtain ⟨q, hq⟩ := helldvd
  let shift : Lattice d → Lattice d :=
    fun f ↦ -(((r - 1 : ℕ) : ℤ) • f)
  have hshiftLattice (f : Lattice d) : shift f ∈ scalarLattice ell := by
    refine ⟨-((q : ℤ) • f), ?_⟩
    change ell • (-((q : ℤ) • f)) = shift f
    dsimp [shift]
    rw [hq]
    module
  choose C hC using fun f : Lattice d ↦
    folnerBox_translate_symmDiff_ratio_bound (hshiftLattice f)
  let K : ℕ := Int.natAbs lo + Int.natAbs hi
  have hgAbs (y : Lattice d) : Int.natAbs (g y) ≤ K := by
    have habs : |g y| ≤ (K : ℤ) := by
      rw [abs_le]
      constructor
      · calc
          -(K : ℤ) ≤ -((Int.natAbs lo : ℕ) : ℤ) := by
            dsimp [K]
            apply neg_le_neg
            norm_cast
            exact Nat.le_add_right _ _
          _ = -|lo| := by rw [Int.natCast_natAbs]
          _ ≤ lo := neg_abs_le lo
          _ ≤ g y := (hbound y).1
      · calc
          g y ≤ hi := (hbound y).2
          _ ≤ |hi| := le_abs_self hi
          _ = ((Int.natAbs hi : ℕ) : ℤ) := by rw [Int.natCast_natAbs]
          _ ≤ (K : ℤ) := by
            dsimp [K]
            norm_cast
            exact Nat.le_add_left _ _
    rw [← Int.natCast_natAbs] at habs
    exact_mod_cast habs
  let total : ℕ := 2 * K * ∑ f ∈ F, C f
  funext x
  let R : ℕ := total
  let B : Finset (Lattice d) := folnerBox ell R
  have hBpos : 0 < B.card := by
    dsimp [B]
    rw [folnerBox_card hell]
    positivity
  have hHconst (b : Lattice d) (hb : b ∈ B) : H (x + b) = H x := by
    have hbLattice : b ∈ scalarLattice ell :=
      folnerBox_mem_scalarLattice (R := R) hb
    obtain ⟨z, hz⟩ := hbLattice
    have hp := hHperiod x z
    change (ell : ℤ) • z = b at hz
    rw [hz] at hp
    exact hp
  have haverageConst :
      (∑ b ∈ B, H (x + b)) = (B.card : ℤ) * H x := by
    calc
      (∑ b ∈ B, H (x + b)) = ∑ _b ∈ B, H x :=
        Finset.sum_congr rfl fun b hb ↦ hHconst b hb
      _ = (B.card : ℤ) * H x := by simp
  have hshiftSum (f : Lattice d) :
      (∑ b ∈ B, g (x + b - (r : ℤ) • f)) =
        ∑ b ∈ B.image (fun b ↦ b + shift f), g (x + b - f) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro b _
      dsimp [shift]
      congr 1
      rw [Nat.cast_sub honele]
      module
    · intro a _ b _ hab
      exact add_right_cancel hab
  have hinnerBound (f : Lattice d) :
      Int.natAbs
          ((∑ b ∈ B, g (x + b - (r : ℤ) • f)) -
            ∑ b ∈ B, g (x + b - f)) * (2 * R + 1) ≤
        (2 * K * C f) * B.card := by
    rw [hshiftSum f]
    have hsum := natAbs_sum_sub_sum_le_symmDiff_card
      (B.image (fun b ↦ b + shift f)) B (fun b ↦ g (x + b - f)) K
      (fun b ↦ hgAbs (x + b - f))
    have hboundary := hC f R
    calc
      Int.natAbs
          ((∑ b ∈ B.image (fun b ↦ b + shift f), g (x + b - f)) -
            ∑ b ∈ B, g (x + b - f)) * (2 * R + 1) ≤
          (2 * K *
            (B.image (fun b ↦ b + shift f) ∆ B).card) * (2 * R + 1) :=
        Nat.mul_le_mul_right _ hsum
      _ = 2 * K *
          ((B ∆ B.image (fun b ↦ b + shift f)).card * (2 * R + 1)) := by
        rw [symmDiff_comm]
        ring
      _ ≤ 2 * K * (C f * B.card) := by
        apply Nat.mul_le_mul_left
        simpa [B] using hboundary
      _ = (2 * K * C f) * B.card := by ring
  have haverageExpand :
      (∑ b ∈ B, H (x + b)) =
        ∑ f ∈ F,
          ((∑ b ∈ B, g (x + b - (r : ℤ) • f)) -
            ∑ b ∈ B, g (x + b - f)) := by
    dsimp [H]
    simp_rw [tileConv_dilate_apply F g _ hr, tileConv]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    congr 1 <;> exact Finset.sum_comm
  have hsumBound :
      Int.natAbs (∑ b ∈ B, H (x + b)) * (2 * R + 1) ≤
        total * B.card := by
    rw [haverageExpand]
    calc
      Int.natAbs
          (∑ f ∈ F,
            ((∑ b ∈ B, g (x + b - (r : ℤ) • f)) -
              ∑ b ∈ B, g (x + b - f))) * (2 * R + 1) ≤
          (∑ f ∈ F,
            Int.natAbs
              ((∑ b ∈ B, g (x + b - (r : ℤ) • f)) -
                ∑ b ∈ B, g (x + b - f))) * (2 * R + 1) :=
        Nat.mul_le_mul_right _ (Int.natAbs_sum_le _ _)
      _ = ∑ f ∈ F,
          Int.natAbs
              ((∑ b ∈ B, g (x + b - (r : ℤ) • f)) -
                ∑ b ∈ B, g (x + b - f)) * (2 * R + 1) := by
        rw [Finset.sum_mul]
      _ ≤ ∑ f ∈ F, (2 * K * C f) * B.card :=
        Finset.sum_le_sum fun f _ ↦ hinnerBound f
      _ = total * B.card := by
        dsimp [total]
        rw [Finset.mul_sum]
        exact (Finset.sum_mul F (fun f ↦ 2 * K * C f) B.card).symm
  rw [haverageConst] at hsumBound
  have hnatAbsCard :
      Int.natAbs ((B.card : ℤ) * H x) = B.card * Int.natAbs (H x) := by
    rw [Int.natAbs_mul]
    norm_num
  rw [hnatAbsCard] at hsumBound
  have hcancel : Int.natAbs (H x) * (2 * R + 1) ≤ total := by
    apply Nat.le_of_mul_le_mul_left ?_ hBpos
    calc
      B.card * (Int.natAbs (H x) * (2 * R + 1)) =
          (B.card * Int.natAbs (H x)) * (2 * R + 1) := by ac_rfl
      _ ≤ total * B.card := hsumBound
      _ = B.card * total := by ac_rfl
  have hHzero : H x = 0 := by
    by_contra hxne
    have hpos : 0 < Int.natAbs (H x) := Int.natAbs_pos.mpr hxne
    have hside := (Nat.le_mul_of_pos_left (2 * R + 1) hpos).trans hcancel
    dsimp [R] at hside
    omega
  exact sub_eq_zero.mp hHzero

/-- Indicator-valued scalar-periodic tilings are invariant under admissible dilations. -/
theorem dilation_indicator_periodic {d ell r : ℕ}
    {F : Finset (Lattice d)} {A : Set (Lattice d)}
    (hell : 0 < ell)
    (hperiod : ScalarPeriodic ell (tileConv F (setIndicator A)))
    (hr : 0 < r)
    (hmod : Nat.ModEq (indicatorDilationModulus ell F.card) r 1) :
    tileConv (dilate r F) (setIndicator A) =
      tileConv F (setIndicator A) := by
  classical
  have hbound : BoundedBetween 0 1 (setIndicator A) := by
    intro x
    by_cases hx : x ∈ A <;> simp [setIndicator, hx]
  apply dilation_periodic hbound hell hperiod hr
  simpa [indicatorDilationModulus, oscillationBound] using hmod

end TranslationalTilings
