import Tiling.AxisParallel.OneDimensional.FiniteInterval.IntervalGeometry

/-!
# Geometry of periodic targets

Regularizing the open translated union changes it only at locally finite endpoints.
A periodic regularized target has finitely many possible gap lengths.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.OneDimensional.FiniteInterval

open Tiling.AxisParallel.OneDimensional

def lineOpenUnion (B H : Set ℝ) : Set ℝ := ⋃ h : H, (h : ℝ) +ᵥ B

def lineClosedUnion (B H : Set ℝ) : Set ℝ := ⋃ h : H, (h : ℝ) +ᵥ closure B

def regularizedTarget (B H : Set ℝ) : Set ℝ := interior (closure (lineOpenUnion B H))

def targetGapLengths (R : Set ℝ) : Set ℝ :=
  {d | ∃ x y : ℝ, x ∈ frontier R ∧ y ∈ frontier R ∧ x < y ∧
    Set.Ioo x y ⊆ (closure R)ᶜ ∧ d = y - x}

theorem lineOpenUnion_isOpen {B H : Set ℝ}
    (P : IntervalPresentation B) : IsOpen (lineOpenUnion B H) := by
  rw [lineOpenUnion]
  exact isOpen_iUnion fun h : H => (P.isOpen).vadd (h : ℝ)

theorem locallyFinite_closedTranslates_of_boundedWindowFinite {B H : Set ℝ}
    (P : IntervalPresentation B)
    (hHlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (H ∩ Q).Finite) :
    LocallyFinite (fun h : H => (h : ℝ) +ᵥ closure B) := by
  intro x
  let t : Set ℝ := Metric.ball x 1
  let Q : Set ℝ := t - closure B
  have ht : t ∈ 𝓝 x := Metric.ball_mem_nhds x zero_lt_one
  have hQbounded : Bornology.IsBounded Q :=
    Metric.isBounded_ball.sub (P.isBounded).closure
  have hfinVal : (H ∩ Q).Finite := hHlocal Q hQbounded
  have hfin : {h : H | (h : ℝ) ∈ H ∩ Q}.Finite :=
    hfinVal.preimage Subtype.val_injective.injOn
  refine ⟨t, ht, hfin.subset ?_⟩
  intro h hh
  obtain ⟨y, hyTranslate, hyt⟩ := hh
  obtain ⟨b, hb, hy⟩ := hyTranslate
  constructor
  · exact h.2
  · change (h : ℝ) ∈ t - closure B
    refine ⟨y, hyt, b, hb, ?_⟩
    dsimp only at hy ⊢
    rw [vadd_eq_add] at hy
    linarith

theorem lineClosedUnion_isClosed {B H : Set ℝ}
    (_P : IntervalPresentation B)
    (hlocal : LocallyFinite (fun h : H => (h : ℝ) +ᵥ closure B)) :
    IsClosed (lineClosedUnion B H) := by
  rw [lineClosedUnion]
  exact hlocal.isClosed_iUnion fun h => isClosed_closure.vadd (h : ℝ)

theorem closure_lineOpenUnion {B H : Set ℝ}
    (_P : IntervalPresentation B)
    (hlocal : LocallyFinite (fun h : H => (h : ℝ) +ᵥ closure B)) :
    closure (lineOpenUnion B H) = lineClosedUnion B H := by
  rw [lineOpenUnion, lineClosedUnion]
  have hopenlocal : LocallyFinite (fun h : H => (h : ℝ) +ᵥ B) :=
    hlocal.subset fun h x hx => by
      obtain ⟨b, hb, rfl⟩ := hx
      exact ⟨b, subset_closure hb, rfl⟩
  rw [hopenlocal.closure_iUnion]
  simp only [closure_vadd]

theorem regularizedTarget_isRegularOpen (B H : Set ℝ) :
    IsOpen (FiniteInterval.regularizedTarget B H) ∧
      interior (closure (FiniteInterval.regularizedTarget B H)) =
        FiniteInterval.regularizedTarget B H := by
  refine ⟨isOpen_interior, ?_⟩
  simp only [regularizedTarget]
  exact interior_closure_idem

theorem lineOpenUnion_subset_regularizedTarget
    {B H : Set ℝ} (P : IntervalPresentation B) :
    lineOpenUnion B H ⊆ FiniteInterval.regularizedTarget B H := by
  exact (lineOpenUnion_isOpen P).subset_interior_closure

theorem closure_regularizedTarget_subset_lineClosedUnion {B H : Set ℝ}
    (P : IntervalPresentation B)
    (hlocal : LocallyFinite (fun h : H => (h : ℝ) +ᵥ closure B)) :
    closure (FiniteInterval.regularizedTarget B H) ⊆ lineClosedUnion B H := by
  rw [regularizedTarget, ← closure_lineOpenUnion P hlocal]
  exact isClosed_closure.closure_interior_subset

theorem closure_regularizedTarget_eq_lineClosedUnion {B H : Set ℝ} (P : IntervalPresentation B)
    (hlocal : LocallyFinite (fun h : H => (h : ℝ) +ᵥ closure B)) :
    closure (FiniteInterval.regularizedTarget B H) = lineClosedUnion B H := by
  apply Subset.antisymm (closure_regularizedTarget_subset_lineClosedUnion P hlocal)
  rw [← closure_lineOpenUnion P hlocal]
  exact closure_mono (lineOpenUnion_subset_regularizedTarget P)

theorem lineClosedUnion_diff_lineOpenUnion_subset_translatedEndpointSet {B H : Set ℝ}
    (P : IntervalPresentation B) :
    lineClosedUnion B H \ lineOpenUnion B H ⊆ translatedEndpointSet P H := by
  intro x hx
  have hxC := hx.1
  rw [lineClosedUnion, mem_iUnion] at hxC
  obtain ⟨h, hxh⟩ := hxC
  have hxnot : x ∉ (h : ℝ) +ᵥ B := by
    intro hxB
    apply hx.2
    rw [lineOpenUnion, mem_iUnion]
    exact ⟨h, hxB⟩
  have hcl : x - (h : ℝ) ∈ closure B := by
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg, add_comm] using hxh
  have hnB : x - (h : ℝ) ∉ B := by
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg, add_comm] using hxnot
  apply (mem_translatedEndpointSet_iff P).2
  exact ⟨h, h.2, x - (h : ℝ), P.closure_diff_subset_endpoints ⟨hcl, hnB⟩, by ring⟩

theorem frontier_regularizedTarget_subset_translatedEndpointSet {B H : Set ℝ}
    (P : IntervalPresentation B)
    (hlocal : LocallyFinite (fun h : H => (h : ℝ) +ᵥ closure B)) :
    frontier (FiniteInterval.regularizedTarget B H) ⊆ translatedEndpointSet P H := by
  intro x hx
  apply lineClosedUnion_diff_lineOpenUnion_subset_translatedEndpointSet P
  rw [frontier, (regularizedTarget_isRegularOpen B H).1.interior_eq] at hx
  exact ⟨closure_regularizedTarget_subset_lineClosedUnion P hlocal hx.1,
    fun hxU => hx.2 (lineOpenUnion_subset_regularizedTarget P hxU)⟩

theorem regularizedTarget_diff_lineOpenUnion_subset_translatedEndpointSet {B H : Set ℝ}
    (P : IntervalPresentation B)
    (hlocal : LocallyFinite (fun h : H => (h : ℝ) +ᵥ closure B)) :
    FiniteInterval.regularizedTarget B H \ lineOpenUnion B H ⊆ translatedEndpointSet P H := by
  intro x hx
  apply lineClosedUnion_diff_lineOpenUnion_subset_translatedEndpointSet P
  exact ⟨closure_regularizedTarget_subset_lineClosedUnion P hlocal (subset_closure hx.1), hx.2⟩

theorem translatedEndpointSet_countable
    {B H : Set ℝ} (P : IntervalPresentation B) (hHcountable : H.Countable) :
    (translatedEndpointSet P H).Countable := by
  rw [translatedEndpointSet]
  exact hHcountable.image2 P.endpoints.finite_toSet.countable (· + ·)

theorem volume_translatedEndpointSet_eq_zero
    {B H : Set ℝ} (P : IntervalPresentation B) (hHcountable : H.Countable) :
    volume (translatedEndpointSet P H) = 0 := by
  exact (translatedEndpointSet_countable P hHcountable).measure_zero volume

theorem lineOpenUnion_ae_regularizedTarget
    {B H : Set ℝ} (P : IntervalPresentation B) (hHcountable : H.Countable)
    (hlocal : LocallyFinite (fun h : H => (h : ℝ) +ᵥ closure B)) :
    lineOpenUnion B H =ᵐ[volume] FiniteInterval.regularizedTarget B H := by
  apply ae_eq_set.2
  constructor
  · rw [sdiff_eq_empty.mpr (lineOpenUnion_subset_regularizedTarget P), measure_empty]
  · apply measure_mono_null
      (regularizedTarget_diff_lineOpenUnion_subset_translatedEndpointSet P hlocal)
      (volume_translatedEndpointSet_eq_zero P hHcountable)

theorem LineTilesOn.lineOpenUnion_ae {B H X : Set ℝ} (hTile : LineTilesOn B H X) :
    lineOpenUnion B H =ᵐ[volume] X := by
  filter_upwards [hTile.2.2.2.2] with x hx
  apply propext
  change x ∈ (⋃ h : H, (h : ℝ) +ᵥ B) ↔ x ∈ X
  rw [mem_iUnion]
  exact hx.symm

theorem regularOpen_real_eq_of_aeEq {U V : Set ℝ}
    (hUopen : IsOpen U) (hUregular : interior (closure U) = U)
    (hVopen : IsOpen V) (hVregular : interior (closure V) = V)
    (hUV : U =ᵐ[volume] V) : U = V := by
  have closure_mono_of_ae {A B : Set ℝ} (hA : IsOpen A) (hB : IsOpen B)
      (hAB : A =ᵐ[volume] B) : A ⊆ closure B := by
    intro x hxA
    by_contra hxB
    let W := A ∩ (closure B)ᶜ
    have hWopen : IsOpen W := hA.inter isClosed_closure.isOpen_compl
    have hxW : x ∈ W := ⟨hxA, hxB⟩
    have hWzero : volume W = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr (hAB.mono fun y hy hyW => by
        have hyB : y ∈ B := Eq.mp hy hyW.1
        exact hyW.2 (subset_closure hyB))
    exact hWopen.measure_ne_zero volume ⟨x, hxW⟩ hWzero
  have hclosure : closure U = closure V := Subset.antisymm
    (closure_minimal (closure_mono_of_ae hUopen hVopen hUV) isClosed_closure)
    (closure_minimal (closure_mono_of_ae hVopen hUopen hUV.symm) isClosed_closure)
  calc
    U = interior (closure U) := hUregular.symm
    _ = interior (closure V) := congrArg interior hclosure
    _ = V := hVregular

theorem LineTilesOn.regularizedTarget
    {B H X : Set ℝ} (P : IntervalPresentation B) (hTile : LineTilesOn B H X)
    (hBpositive : 0 < (volume B).toReal) :
    let R := FiniteInterval.regularizedTarget B H
    IsOpen R ∧ interior (closure R) = R ∧ lineOpenUnion B H =ᵐ[volume] R ∧
      R =ᵐ[volume] X ∧ LineTilesOn B H R ∧
      (∀ C : Set ℝ, IsCompact C → (C ∩ frontier R).Finite) := by
  dsimp only
  have hHlocal := finiteInterval_lineTilesOn_centres_locallyFinite
    P.isFiniteIntervalRegion hBpositive hTile
  have hlocal := locallyFinite_closedTranslates_of_boundedWindowFinite P hHlocal
  have hUaeR := lineOpenUnion_ae_regularizedTarget P hTile.2.2.1 hlocal
  have hUaeX := LineTilesOn.lineOpenUnion_ae hTile
  have hRaeX := hUaeR.symm.trans hUaeX
  have hR := regularizedTarget_isRegularOpen B H
  refine ⟨hR.1, hR.2, hUaeR, hRaeX, ?_, ?_⟩
  · refine ⟨hTile.1, hR.1.measurableSet, hTile.2.2.1, hTile.2.2.2.1, ?_⟩
    filter_upwards [hUaeR] with x hx
    change x ∈ FiniteInterval.regularizedTarget B H ↔ ∃ h : H, x ∈ (h : ℝ) +ᵥ B
    have hx' : x ∈ lineOpenUnion B H ↔ x ∈ FiniteInterval.regularizedTarget B H :=
      Iff.of_eq hx
    rw [lineOpenUnion, mem_iUnion] at hx'
    exact hx'.symm
  · intro C hC
    have hE := translatedEndpointSet_boundedWindowFinite P hHlocal C hC.isBounded
    apply hE.subset
    intro x hx
    exact ⟨frontier_regularizedTarget_subset_translatedEndpointSet P hlocal hx.2, hx.1⟩

theorem LineTilesOn.regularizedTarget_eq
    {B H R : Set ℝ} (P : IntervalPresentation B) (hTile : LineTilesOn B H R)
    (hBpositive : 0 < (volume B).toReal) (hRopen : IsOpen R)
    (hRregular : interior (closure R) = R) : FiniteInterval.regularizedTarget B H = R := by
  obtain ⟨hO, hreg, _, hae, _, _⟩ := LineTilesOn.regularizedTarget P hTile hBpositive
  exact regularOpen_real_eq_of_aeEq hO hreg hRopen hRregular hae

theorem LineTilesOn.lineClosedUnion_eq_closure_target
    {B H R : Set ℝ} (P : IntervalPresentation B) (hTile : LineTilesOn B H R)
    (hBpositive : 0 < (volume B).toReal) (hRopen : IsOpen R)
    (hRregular : interior (closure R) = R) : lineClosedUnion B H = closure R := by
  have hHlocal := finiteInterval_lineTilesOn_centres_locallyFinite
    P.isFiniteIntervalRegion hBpositive hTile
  have hlocal := locallyFinite_closedTranslates_of_boundedWindowFinite P hHlocal
  rw [← closure_regularizedTarget_eq_lineClosedUnion P hlocal,
    LineTilesOn.regularizedTarget_eq P hTile hBpositive hRopen hRregular]

theorem LineTilesOn.frontier_target_subset_translatedEndpointSet
    {B H R : Set ℝ} (P : IntervalPresentation B) (hTile : LineTilesOn B H R)
    (hBpositive : 0 < (volume B).toReal) (hRopen : IsOpen R)
    (hRregular : interior (closure R) = R) :
    frontier R ⊆ translatedEndpointSet P H := by
  have hHlocal := finiteInterval_lineTilesOn_centres_locallyFinite
    P.isFiniteIntervalRegion hBpositive hTile
  have hlocal := locallyFinite_closedTranslates_of_boundedWindowFinite P hHlocal
  rw [← LineTilesOn.regularizedTarget_eq P hTile hBpositive hRopen hRregular]
  exact frontier_regularizedTarget_subset_translatedEndpointSet P hlocal

theorem LineTilesOn.translatedEndpointSet_subset_closure_target
    {B H R : Set ℝ} (P : IntervalPresentation B) (hTile : LineTilesOn B H R)
    (hBpositive : 0 < (volume B).toReal) (hRopen : IsOpen R)
    (hRregular : interior (closure R) = R) :
    translatedEndpointSet P H ⊆ closure R := by
  intro x hx
  obtain ⟨h, hh, e, he, rfl⟩ := (mem_translatedEndpointSet_iff P).1 hx
  rw [← LineTilesOn.lineClosedUnion_eq_closure_target P hTile hBpositive hRopen hRregular]
  rw [lineClosedUnion, mem_iUnion]
  refine ⟨⟨h, hh⟩, ?_⟩
  exact ⟨e, P.endpoint_subset_closure he, by simp [vadd_eq_add]⟩

theorem LineTilesOn.regularizedTarget_periodic_of_target_ae
    {B H X : Set ℝ} (P : IntervalPresentation B) (hTile : LineTilesOn B H X)
    (hBpositive : 0 < (volume B).toReal) {p : ℝ}
    (hXperiod : p +ᵥ X =ᵐ[volume] X) :
    p +ᵥ FiniteInterval.regularizedTarget B H =
      FiniteInterval.regularizedTarget B H := by
  obtain ⟨hRopen, hRregular, _, hRaeX, _, _⟩ :=
    LineTilesOn.regularizedTarget P hTile hBpositive
  have hae : p +ᵥ FiniteInterval.regularizedTarget B H =ᵐ[volume]
      FiniteInterval.regularizedTarget B H :=
    ((MeasureTheory.vadd_set_ae_eq p).2 hRaeX).trans (hXperiod.trans hRaeX.symm)
  apply regularOpen_real_eq_of_aeEq (hRopen.vadd p) _ hRopen hRregular hae
  rw [closure_vadd, interior_vadd, hRregular]

theorem LineTilesOn.regularizedTarget_periodic
    {B H X : Set ℝ} (P : IntervalPresentation B) (hTile : LineTilesOn B H X)
    (hBpositive : 0 < (volume B).toReal) {p : ℝ}
    (hXperiod : ∀ x, x + p ∈ X ↔ x ∈ X) :
    p +ᵥ FiniteInterval.regularizedTarget B H = FiniteInterval.regularizedTarget B H := by
  apply LineTilesOn.regularizedTarget_periodic_of_target_ae P hTile hBpositive
  filter_upwards [] with x
  apply propext
  change x ∈ p +ᵥ X ↔ x ∈ X
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  simpa [add_comm, sub_eq_add_neg] using (hXperiod (x - p)).symm

private theorem frontier_periodic_function_of_vadd_eq {R : Set ℝ} {a : ℝ}
    (h : a +ᵥ R = R) : Function.Periodic (fun x => x ∈ frontier R) a := by
  intro x
  have hi := (Homeomorph.vaddConst a).image_frontier R
  have himage (S : Set ℝ) : (Homeomorph.vaddConst a : ℝ → ℝ) '' S = a +ᵥ S := by
    ext y
    simp only [Set.mem_image, Set.mem_vadd_set_iff_neg_vadd_mem,
      Homeomorph.vaddConst_apply, vadd_eq_add]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [add_comm] using hz
    · intro hy
      exact ⟨y - a, by simpa [sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc] using hy, by simp⟩
  rw [himage, himage] at hi
  rw [h] at hi
  apply propext
  constructor
  · intro hx
    have hx' : a + x ∈ frontier R := by simpa [add_comm] using hx
    rw [← hi] at hx'
    obtain ⟨y, hy, hay⟩ := hx'
    have : y = x := by simpa using hay
    simpa [this] using hy
  · intro hx
    have hx' : a + x ∈ a +ᵥ frontier R := ⟨x, hx, rfl⟩
    rw [hi] at hx'
    simpa [add_comm] using hx'

theorem frontier_periodic {R : Set ℝ} {p : ℝ} (hperiod : p +ᵥ R = R) :
    p +ᵥ frontier R = frontier R := by
  ext x
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  have hfun := frontier_periodic_function_of_vadd_eq hperiod
  simpa [Function.Periodic, sub_eq_add_neg, add_comm] using (hfun (-p + x)).symm

theorem frontier_periodic_zsmul {R : Set ℝ} {p : ℝ} (hperiod : p +ᵥ R = R)
    (m : ℤ) : ((m : ℝ) * p) +ᵥ frontier R = frontier R := by
  ext x
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  have hfun := (frontier_periodic_function_of_vadd_eq hperiod).zsmul m
  simpa [Function.Periodic, zsmul_eq_mul, sub_eq_add_neg, add_comm] using
    (hfun (-((m : ℝ) * p) + x)).symm

theorem periods_commensurable_of_finite_frontier_residues
    {R : Set ℝ} {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpperiod : p +ᵥ R = R) (hqperiod : q +ᵥ R = R)
    (hfinite : (frontier R ∩ Set.Ico 0 p).Finite) (hne : (frontier R).Nonempty) :
    ∃ r : ℚ, p = (r : ℝ) * q := by
  obtain ⟨x, hx⟩ := hne
  have hpfront := frontier_periodic_function_of_vadd_eq hpperiod
  have hqfront := frontier_periodic_function_of_vadd_eq hqperiod
  let residue : ℕ → ℝ := fun n => p * Int.fract ((x + (n : ℝ) * q) / p)
  have hres_mem (n : ℕ) : residue n ∈ frontier R ∩ Set.Ico 0 p := by
    have hxn : x + (n : ℝ) * q ∈ frontier R := by
      have hn := hqfront.nat_mul n x
      simpa [nsmul_eq_mul] using hn.mpr hx
    let z : ℤ := -Int.floor ((x + (n : ℝ) * q) / p)
    have hzmem : (z : ℝ) * p + (x + (n : ℝ) * q) ∈ frontier R := by
      have hz := hpfront.zsmul z (x + (n : ℝ) * q)
      have := hz.mpr hxn
      simpa [zsmul_eq_mul, add_comm] using this
    have heq : residue n = (z : ℝ) * p + (x + (n : ℝ) * q) := by
      change p * (((x + (n : ℝ) * q) / p) -
        (Int.floor ((x + (n : ℝ) * q) / p) : ℝ)) =
        (z : ℝ) * p + (x + (n : ℝ) * q)
      have hzcast : (z : ℝ) =
          -(Int.floor ((x + (n : ℝ) * q) / p) : ℝ) := by simp [z]
      rw [hzcast]
      field_simp [hp.ne']; ring
    refine ⟨heq ▸ hzmem, ?_⟩
    constructor
    · exact mul_nonneg hp.le (Int.fract_nonneg _)
    · nlinarith [Int.fract_lt_one ((x + (n : ℝ) * q) / p)]
  let f : ℕ → {y : ℝ // y ∈ frontier R ∩ Set.Ico 0 p} :=
    fun n => ⟨residue n, hres_mem n⟩
  let _ : Fintype {y : ℝ // y ∈ frontier R ∩ Set.Ico 0 p} := hfinite.fintype
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hfract : Int.fract ((x + (i : ℝ) * q) / p) =
      Int.fract ((x + (j : ℝ) * q) / p) := by
    have heq' := congrArg Subtype.val heq
    dsimp [f, residue] at heq'
    exact mul_left_cancel₀ hp.ne' heq'
  have hlin : ((i : ℝ) - (j : ℝ)) * q =
      ((Int.floor ((x + (i : ℝ) * q) / p) : ℝ) -
        (Int.floor ((x + (j : ℝ) * q) / p) : ℝ)) * p := by
    rw [Int.fract, Int.fract] at hfract
    field_simp at hfract
    have hjarg : x + q * (j : ℝ) = x + (j : ℝ) * q := by ring
    rw [hjarg] at hfract
    linear_combination hfract
  let a : ℤ := Int.ofNat i - Int.ofNat j
  let b : ℤ := Int.floor ((x + (i : ℝ) * q) / p) -
    Int.floor ((x + (j : ℝ) * q) / p)
  have ha : a ≠ 0 := by
    intro ha0
    apply hij
    exact Int.ofNat_inj.mp (Int.sub_eq_zero.mp ha0)
  have hab : (a : ℝ) * q = (b : ℝ) * p := by simpa [a, b] using hlin
  have hb : b ≠ 0 := by
    intro hb0
    have haz : (a : ℝ) * q = 0 := by simpa [hb0] using hab
    have hacast : (a : ℝ) = 0 := (mul_eq_zero.mp haz).resolve_right hq.ne'
    exact ha (by exact_mod_cast hacast)
  refine ⟨(a / b : ℚ), ?_⟩
  rw [Rat.cast_div]
  push_cast
  field_simp [hb]
  nlinarith [hab]

theorem frontier_nonempty_of_nonempty_proper_regularOpen {R : Set ℝ}
    (hRnonempty : R.Nonempty) (_hRopen : IsOpen R)
    (_hRregular : interior (closure R) = R) (hRproper : R ≠ Set.univ) :
    (frontier R).Nonempty := by
  by_contra hne
  have hempty : frontier R = ∅ := not_nonempty_iff_eq_empty.mp hne
  rcases frontier_eq_empty_iff.mp hempty with hRempty | hRuniv
  · exact hRnonempty.ne_empty hRempty
  · exact hRproper hRuniv

private theorem periodic_mem_of_vadd_eq {S : Set ℝ} {a : ℝ} (h : a +ᵥ S = S) :
    Function.Periodic (fun x => x ∈ S) a := by
  intro x
  apply propext
  constructor
  · intro hx
    have hx' : a + x ∈ S := by simpa [add_comm] using hx
    rw [← h] at hx'
    obtain ⟨y, hy, hay⟩ := hx'
    have : y = x := by simpa using hay
    simpa [this] using hy
  · intro hx
    have hx' : a + x ∈ a +ᵥ S := ⟨x, hx, rfl⟩
    rw [h] at hx'
    simpa [add_comm] using hx'

theorem targetGapLength_le_period {R : Set ℝ} {p d : ℝ} (hp : 0 < p)
    (hperiod : p +ᵥ R = R) (hd : d ∈ targetGapLengths R) : d ≤ p := by
  obtain ⟨x, y, hx, hy, hxy, hgap, rfl⟩ := hd
  by_contra hnot
  have hxp : x + p ∈ Ioo x y := by constructor <;> linarith
  have hxpfront : x + p ∈ frontier R := by
    have hm : p + x ∈ p +ᵥ frontier R := ⟨x, hx, rfl⟩
    rw [frontier_periodic hperiod] at hm
    simpa [add_comm] using hm
  exact hgap hxp (frontier_subset_closure hxpfront)

theorem targetGapLength_witness_in_twoPeriodWindow {R : Set ℝ} {p d : ℝ}
    (hp : 0 < p) (hperiod : p +ᵥ R = R) (hd : d ∈ targetGapLengths R) :
    ∃ x y : ℝ, x ∈ frontier R ∩ Set.Ico 0 p ∧
      y ∈ frontier R ∩ Set.Ioc 0 (2 * p) ∧ x < y ∧
      Set.Ioo x y ⊆ (closure R)ᶜ ∧ d = y - x := by
  obtain ⟨a, b, ha, hb, hab, hgap, hdab⟩ := hd
  let m : ℤ := Int.floor (a / p)
  let x : ℝ := a - (m : ℝ) * p
  let y : ℝ := b - (m : ℝ) * p
  have hxfract : x = p * Int.fract (a / p) := by
    dsimp [x, m]
    rw [Int.fract]
    field_simp [hp.ne']
  have hx0 : 0 ≤ x := by rw [hxfract]; exact mul_nonneg hp.le (Int.fract_nonneg _)
  have hxp : x < p := by
    rw [hxfract]
    nlinarith [Int.fract_lt_one (a / p)]
  have hxy : x < y := by dsimp [x, y]; linarith
  have hdiff : y - x = b - a := by dsimp [x, y]; ring
  have hyle : y ≤ 2 * p := by
    have hdle := targetGapLength_le_period hp hperiod
      ⟨a, b, ha, hb, hab, hgap, hdab⟩
    rw [hdab, ← hdiff] at hdle
    linarith
  have hy0 : 0 < y := lt_of_le_of_lt hx0 hxy
  have hfrontfun := (frontier_periodic_function_of_vadd_eq hperiod).zsmul (-m)
  have hxfront : x ∈ frontier R := by
    have := (hfrontfun a).mpr ha
    simpa [x, zsmul_eq_mul, sub_eq_add_neg] using this
  have hyfront : y ∈ frontier R := by
    have := (hfrontfun b).mpr hb
    simpa [y, zsmul_eq_mul, sub_eq_add_neg] using this
  have hclosurePeriod : p +ᵥ closure R = closure R := by
    rw [← closure_vadd, hperiod]
  have hclosureFun := (periodic_mem_of_vadd_eq hclosurePeriod).zsmul m
  have hgap' : Ioo x y ⊆ (closure R)ᶜ := by
    intro z hz hzcl
    have hzshift : z + (m : ℝ) * p ∈ closure R := by
      have := (hclosureFun z).mpr hzcl
      simpa [zsmul_eq_mul] using this
    have hz1 := hz.1
    have hz2 := hz.2
    dsimp [x, y] at hz1 hz2
    apply hgap (show z + (m : ℝ) * p ∈ Ioo a b by
      constructor <;> linarith)
    exact hzshift
  refine ⟨x, y, ⟨hxfront, hx0, hxp⟩, ⟨hyfront, hy0, hyle⟩,
    hxy, hgap', ?_⟩
  rw [hdab, hdiff]

theorem targetGapLengths_finite {R : Set ℝ} {p : ℝ} (hp : 0 < p)
    (hperiod : p +ᵥ R = R)
    (hfrontierLocal : ∀ C : Set ℝ, IsCompact C → (C ∩ frontier R).Finite) :
    (targetGapLengths R).Finite := by
  let F : Set ℝ := Icc 0 (2 * p) ∩ frontier R
  have hF : F.Finite := hfrontierLocal (Icc 0 (2 * p)) isCompact_Icc
  apply ((hF.prod hF).image fun q : ℝ × ℝ => q.2 - q.1).subset
  intro d hd
  obtain ⟨x, y, hx, hy, hxy, hgap, hdiff⟩ :=
    targetGapLength_witness_in_twoPeriodWindow hp hperiod hd
  refine ⟨(x, y), ?_, hdiff.symm⟩
  constructor
  · exact ⟨⟨hx.2.1, (le_of_lt hx.2.2).trans (by linarith [hp])⟩, hx.1⟩
  · exact ⟨⟨hy.2.1.le, hy.2.2⟩, hy.1⟩

theorem targetGapLengths_pos {R : Set ℝ} {d : ℝ}
    (hd : d ∈ targetGapLengths R) : 0 < d := by
  obtain ⟨x, y, _, _, hxy, _, rfl⟩ := hd
  linarith

end Tiling.AxisParallel.OneDimensional.FiniteInterval
