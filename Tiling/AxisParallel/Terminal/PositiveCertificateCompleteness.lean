import Tiling.AxisParallel.Terminal.NormalFormCore
import Tiling.AxisParallel.Terminal.PositiveCertificateVerification
import Tiling.AxisParallel.Terminal.CertificateCoding
import Tiling.AxisParallel.Continuous.LocalizingNonFLC
import Tiling.AxisParallel.Terminal.MainCorollaries

/-!
# Positive certificate completeness

Finite presentation data and the elementary exact normal-form-to-positive-stage completeness
obligations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped Pointwise

namespace Tiling.AxisParallel.Terminal.PositiveCertificateCompleteness

open Tiling.AxisParallel
open Tiling.AxisParallel.Terminal
open Tiling.AxisParallel.Terminal.Executable
open Tiling.AxisParallel.Terminal.Executable.PositiveVerification

private def slabRawCode (orientation : Bool) {pieceCount : Nat}
    (intervalCount representativeCount : Fin pieceCount → Nat)
    (checkingRadius : Nat) : RawTriangularCode where
  orientation := orientation
  pieces := List.ofFn fun j =>
    { intervalCount := intervalCount j, representativeCount := representativeCount j }
  checkingRadius := checkingRadius

private def latticeRawCode (q : Rat) (representativeCount firstIndexBound secondIndexBound : Nat) :
    RawLatticeCode where
  rationalSeparator := q
  representativeCount := representativeCount
  firstIndexBound := firstIndexBound
  secondIndexBound := secondIndexBound

def IsFiniteOrbitPresentation (S : Set Tiling.Plane) (u v : Tiling.Plane)
    {r : Nat} (representative : Fin r → Tiling.Plane) : Prop :=
  S = {p | ∃ (a : Fin r) (n m : Int),
    p = representative a + n • u + m • v}

/-- Joint finite interval data for all slab colours.  This is proof-only extracted data, not an
input certificate and not a runtime value. -/
structure FiniteSlabBasePresentation {K : Region} (D : SlabCertificate K) where
  intervalCount : Fin D.numberOfPieces → Nat
  intervalCount_pos : ∀ j, 0 < intervalCount j
  left : ∀ j, Fin (intervalCount j) → Real
  right : ∀ j, Fin (intervalCount j) → Real
  normalized : ∀ j ell,
    0 ≤ left j ell ∧ left j ell < right j ell ∧
      right j ell ≤ D.commonHorizontalPeriod
  interiors_disjoint : ∀ j ell j' (ell' : Fin (intervalCount j')),
    Sigma.mk j ell ≠ Sigma.mk j' ell' →
    right j ell ≤ left j' ell' ∨ right j' ell' ≤ left j ell
  period_closed_cover : ∀ x, 0 < x → x < D.commonHorizontalPeriod →
    ∃ j ell, left j ell ≤ x ∧ x ≤ right j ell
  base_ae : ∀ j, D.base j =ᵐ[volume]
    ⋃ q : Int, ⋃ ell : Fin (intervalCount j),
      Set.Ioo (left j ell + q * D.commonHorizontalPeriod)
        (right j ell + q * D.commonHorizontalPeriod)

/-- A finite set of normalized representatives for every slab colour. -/
structure FiniteSlabOrbitPresentation {K : Region} (D : SlabCertificate K) where
  representativeCount : Fin D.numberOfPieces → Nat
  representativeCount_pos : ∀ j, 0 < representativeCount j
  representative : ∀ j, Fin (representativeCount j) → Tiling.Plane
  normalized : ∀ j a,
    0 ≤ (representative j a).re ∧
    (representative j a).re < D.commonHorizontalPeriod ∧
    0 ≤ (representative j a).im ∧
    (representative j a).im < D.commonVerticalPeriod
  presents : ∀ j, IsFiniteOrbitPresentation (D.selectedPiece j)
    (skewPeriodVector D.commonHorizontalPeriod (D.normalizedShear j))
    (verticalPeriodVector D.commonVerticalPeriod) (representative j)

structure FiniteLatticeOrbitPresentation {K : Region}
    (D : PeriodicReplacement K Set.univ) where
  firstPeriod : Tiling.Plane
  secondPeriod : Tiling.Plane
  rationalSeparator : Rat
  second_first_pos : 0 < secondPeriod.re
  second_second_pos : 0 < secondPeriod.im
  separated_first_pos :
    0 < firstPeriod.re - rationalSeparator * secondPeriod.re
  separated_second_pos :
    0 < rationalSeparator * secondPeriod.im - firstPeriod.im
  periods_mem : firstPeriod ∈ D.lattice.toAddSubgroup ∧
    secondPeriod ∈ D.lattice.toAddSubgroup
  independent : LinearIndependent Real ![firstPeriod, secondPeriod]
  representativeCount : Nat
  representativeCount_pos : 0 < representativeCount
  representative : Fin representativeCount → Tiling.Plane
  presents : IsFiniteOrbitPresentation D.centres firstPeriod secondPeriod representative


private theorem slabRawCode_wellFormed :
    ∀ (orientation : Bool) {pieceCount : Nat}
        (intervalCount representativeCount : Fin pieceCount → Nat) radius,
      0 < pieceCount → (∀ j, 0 < intervalCount j) →
      (∀ j, 0 < representativeCount j) → 0 < radius →
        (slabRawCode orientation intervalCount representativeCount radius).wellFormed = true := by
  intro orientation pieceCount intervalCount representativeCount radius
    hpieces hinterval hrepresentative hradius
  simp [slabRawCode, RawTriangularCode.wellFormed,
    RawTriangularPieceCode.wellFormed, hpieces.ne', hinterval,
    hrepresentative, hradius]

private theorem slab_checkingRadius_exists :
    ∀ {C : RegionCode} (R : Realization C) {K : Region}
        (D : SlabCertificate K), K = R.region →
      ∃ radius : Nat, 0 < radius ∧
        (∀ a b, |selectedCoordinate D.orientation .horizontal (R.vertex a) -
          selectedCoordinate D.orientation .horizontal (R.vertex b)| <
            radius * D.commonHorizontalPeriod) ∧
        (∀ a b, |selectedCoordinate D.orientation .vertical (R.vertex a) -
          selectedCoordinate D.orientation .vertical (R.vertex b)| <
            radius * D.commonVerticalPeriod) := by
  intro C R K D _hK
  let horizontalDiameter : Fin C.vertexCount × Fin C.vertexCount → ℝ := fun p ↦
    |selectedCoordinate D.orientation .horizontal (R.vertex p.1) -
      selectedCoordinate D.orientation .horizontal (R.vertex p.2)|
  let verticalDiameter : Fin C.vertexCount × Fin C.vertexCount → ℝ := fun p ↦
    |selectedCoordinate D.orientation .vertical (R.vertex p.1) -
      selectedCoordinate D.orientation .vertical (R.vertex p.2)|
  obtain ⟨H, hH⟩ := Finite.exists_le horizontalDiameter
  obtain ⟨V, hV⟩ := Finite.exists_le verticalDiameter
  obtain ⟨radius, hradius⟩ := exists_nat_gt
    (max (H / D.commonHorizontalPeriod) (V / D.commonVerticalPeriod))
  refine ⟨radius + 1, Nat.succ_pos radius, ?_, ?_⟩
  · intro a b
    have hab := hH (a, b)
    have hratio : H / D.commonHorizontalPeriod < radius + 1 := by
      have : (radius : ℝ) < radius + 1 := by norm_num
      exact lt_trans (lt_of_le_of_lt (le_max_left _ _) hradius) this
    have hmul := (div_lt_iff₀ D.commonHorizontalPeriod_pos).mp hratio
    exact lt_of_le_of_lt hab (by simpa using hmul)
  · intro a b
    have hab := hV (a, b)
    have hratio : V / D.commonVerticalPeriod < radius + 1 := by
      have : (radius : ℝ) < radius + 1 := by norm_num
      exact lt_trans (lt_of_le_of_lt (le_max_right _ _) hradius) this
    have hmul := (div_lt_iff₀ D.commonVerticalPeriod_pos).mp hratio
    exact lt_of_le_of_lt hab (by simpa using hmul)

private theorem latticeRawCode_wellFormed :
    ∀ q representativeCount firstIndexBound secondIndexBound,
      0 < representativeCount → 0 < firstIndexBound → 0 < secondIndexBound →
        (latticeRawCode q representativeCount firstIndexBound
          secondIndexBound).wellFormed = true := by
  intro q representativeCount firstIndexBound secondIndexBound
    hrepresentative hfirst hsecond
  simp [latticeRawCode, RawLatticeCode.wellFormed, hrepresentative, hfirst,
    hsecond]


private noncomputable def normalizeSlabRepresentative
    (beta alpha shear : ℝ) (z : Tiling.Plane) : Tiling.Plane :=
  let n : ℤ := ⌊z.re / beta⌋
  let z₁ := z - n • skewPeriodVector beta shear
  let m : ℤ := ⌊z₁.im / alpha⌋
  z₁ - m • verticalPeriodVector alpha

private theorem normalizeSlabRepresentative_mem_coset
    (beta alpha shear : ℝ) (z : Tiling.Plane) :
    z - normalizeSlabRepresentative beta alpha shear z ∈
      triangularPeriodSubgroup alpha beta shear := by
  let n : ℤ := ⌊z.re / beta⌋
  let z₁ := z - n • skewPeriodVector beta shear
  let m : ℤ := ⌊z₁.im / alpha⌋
  refine ⟨m, n, ?_⟩
  simp only [normalizeSlabRepresentative, n, z₁, m]
  abel

private theorem normalizeSlabRepresentative_bounds
    {beta alpha : ℝ} (hbeta : 0 < beta) (halpha : 0 < alpha)
    (shear : ℝ) (z : Tiling.Plane) :
    0 ≤ (normalizeSlabRepresentative beta alpha shear z).re ∧
    (normalizeSlabRepresentative beta alpha shear z).re < beta ∧
    0 ≤ (normalizeSlabRepresentative beta alpha shear z).im ∧
    (normalizeSlabRepresentative beta alpha shear z).im < alpha := by
  let n : ℤ := ⌊z.re / beta⌋
  let z₁ := z - n • skewPeriodVector beta shear
  let m : ℤ := ⌊z₁.im / alpha⌋
  have hnle : (n : ℝ) ≤ z.re / beta := Int.floor_le _
  have hnlt : z.re / beta < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hmle : (m : ℝ) ≤ z₁.im / alpha := Int.floor_le _
  have hmlt : z₁.im / alpha < (m : ℝ) + 1 := Int.lt_floor_add_one _
  have hre : (normalizeSlabRepresentative beta alpha shear z).re =
      z.re - (n : ℝ) * beta := by
    simp [normalizeSlabRepresentative, n, skewPeriodVector,
      verticalPeriodVector]
  have him : (normalizeSlabRepresentative beta alpha shear z).im =
      z₁.im - (m : ℝ) * alpha := by
    simp [normalizeSlabRepresentative, n, z₁, m, verticalPeriodVector]
  rw [hre, him]
  constructor
  · exact sub_nonneg.mpr ((le_div_iff₀ hbeta).mp hnle)
  constructor
  · have := (div_lt_iff₀ hbeta).mp hnlt
    linarith
  · constructor
    · exact sub_nonneg.mpr ((le_div_iff₀ halpha).mp hmle)
    · have := (div_lt_iff₀ halpha).mp hmlt
      linarith

private theorem slab_piece_finiteOrbit :
    ∀ {K : Region} (D : SlabCertificate K),
      Nonempty (FiniteSlabOrbitPresentation D) := by
  intro K D
  classical
  have hdata : ∀ j : Fin D.numberOfPieces,
      ∃ R : Finset Tiling.Plane,
        (R : Set Tiling.Plane) ⊆ D.selectedPiece j ∧
        QuotientAddGroup.mk'
              (triangularPeriodSubgroup D.commonVerticalPeriod
                D.commonHorizontalPeriod (D.normalizedShear j)) ''
            (R : Set Tiling.Plane) =
          QuotientAddGroup.mk'
              (triangularPeriodSubgroup D.commonVerticalPeriod
                D.commonHorizontalPeriod (D.normalizedShear j)) ''
            D.selectedPiece j ∧
        Set.InjOn
          (QuotientAddGroup.mk'
            (triangularPeriodSubgroup D.commonVerticalPeriod
              D.commonHorizontalPeriod (D.normalizedShear j)))
          (R : Set Tiling.Plane) := by
    intro j
    exact exists_finiteOrbitRepresentatives D.commonVerticalPeriod_pos
      D.commonHorizontalPeriod_pos (D.piece_tiles j)
      (D.common_verticalPeriod j) (D.common_skewPeriod j)
  choose R hRsub hRquot hRinj using hdata
  have hRcard (j : Fin D.numberOfPieces) : 0 < (R j).card := by
    rw [Finset.card_pos]
    by_contra hempty
    have hset : ((R j : Finset Tiling.Plane) : Set Tiling.Plane) = ∅ := by
      simpa using hempty
    obtain ⟨s, hs⟩ := D.selectedPiece_nonempty j
    have himage : QuotientAddGroup.mk'
          (triangularPeriodSubgroup D.commonVerticalPeriod
            D.commonHorizontalPeriod (D.normalizedShear j)) s ∈
        QuotientAddGroup.mk'
            (triangularPeriodSubgroup D.commonVerticalPeriod
              D.commonHorizontalPeriod (D.normalizedShear j)) ''
          D.selectedPiece j := ⟨s, hs, rfl⟩
    rw [← hRquot j, hset] at himage
    simp at himage
  let rawRepresentative (j : Fin D.numberOfPieces) :
      Fin (R j).card → Tiling.Plane := fun a => ((R j).equivFin.symm a).1
  let representative (j : Fin D.numberOfPieces) :
      Fin (R j).card → Tiling.Plane := fun a =>
    normalizeSlabRepresentative D.commonHorizontalPeriod D.commonVerticalPeriod
      (D.normalizedShear j) (rawRepresentative j a)
  refine ⟨⟨fun j => (R j).card, hRcard, representative, ?_, ?_⟩⟩
  · intro j a
    exact normalizeSlabRepresentative_bounds D.commonHorizontalPeriod_pos
      D.commonVerticalPeriod_pos (D.normalizedShear j) (rawRepresentative j a)
  · intro j
    unfold IsFiniteOrbitPresentation
    ext s
    constructor
    · intro hs
      have hsQ : QuotientAddGroup.mk'
            (triangularPeriodSubgroup D.commonVerticalPeriod
              D.commonHorizontalPeriod (D.normalizedShear j)) s ∈
          QuotientAddGroup.mk'
              (triangularPeriodSubgroup D.commonVerticalPeriod
                D.commonHorizontalPeriod (D.normalizedShear j)) ''
            (R j : Set Tiling.Plane) := by
        rw [hRquot j]
        exact ⟨s, hs, rfl⟩
      obtain ⟨r, hr, hrs⟩ := hsQ
      let a : Fin (R j).card := (R j).equivFin ⟨r, hr⟩
      have hra : rawRepresentative j a = r := by simp [rawRepresentative, a]
      let H := triangularPeriodSubgroup D.commonVerticalPeriod
        D.commonHorizontalPeriod (D.normalizedShear j)
      have hsr : s - r ∈ H := by
        obtain ⟨d, hd, heq⟩ := (QuotientAddGroup.mk'_eq_mk' H).mp hrs.symm
        rw [← heq]
        simpa [sub_eq_add_neg, add_comm] using hd
      have hrnorm : r - representative j a ∈ H := by
        rw [← hra]
        exact normalizeSlabRepresentative_mem_coset _ _ _ _
      have htotal : s - representative j a ∈ H := by
        convert add_mem hsr hrnorm using 1
        abel
      obtain ⟨m, n, hmn⟩ := htotal
      refine ⟨a, n, m, ?_⟩
      rw [show s = representative j a + (s - representative j a) by abel, hmn]
      abel
    · rintro ⟨a, n, m, rfl⟩
      have hraw : rawRepresentative j a ∈ D.selectedPiece j := by
        apply hRsub j
        exact ((R j).equivFin.symm a).2
      have hnorm : representative j a ∈ D.selectedPiece j := by
        have hp := normalizeSlabRepresentative_mem_coset
          D.commonHorizontalPeriod D.commonVerticalPeriod
          (D.normalizedShear j) (rawRepresentative j a)
        have hperiod : rawRepresentative j a - representative j a ∈
            periodGroup (D.selectedPiece j) := by
          apply (show triangularPeriodSubgroup D.commonVerticalPeriod
              D.commonHorizontalPeriod (D.normalizedShear j) ≤
              periodGroup (D.selectedPiece j) from ?_)
          · exact hp
          · rintro x ⟨m, n, rfl⟩
            exact add_mem
              ((periodGroup _).zsmul_mem (D.common_verticalPeriod j) m)
              ((periodGroup _).zsmul_mem (D.common_skewPeriod j) n)
        have hshift := (periodGroup_isAddSubgroup (D.selectedPiece j)
          (-(rawRepresentative j a - representative j a))).mp (neg_mem hperiod)
        have : representative j a ∈
            -(rawRepresentative j a - representative j a) +ᵥ D.selectedPiece j := by
          refine ⟨rawRepresentative j a, hraw, ?_⟩
          simp [vadd_eq_add]
        rwa [hshift] at this
      have hperiod : n • skewPeriodVector D.commonHorizontalPeriod
            (D.normalizedShear j) +
          m • verticalPeriodVector D.commonVerticalPeriod ∈
          periodGroup (D.selectedPiece j) :=
        add_mem ((periodGroup _).zsmul_mem (D.common_skewPeriod j) n)
          ((periodGroup _).zsmul_mem (D.common_verticalPeriod j) m)
      have hshift := (periodGroup_isAddSubgroup (D.selectedPiece j) _).mp hperiod
      have : n • skewPeriodVector D.commonHorizontalPeriod
            (D.normalizedShear j) +
          m • verticalPeriodVector D.commonVerticalPeriod + representative j a ∈
          (n • skewPeriodVector D.commonHorizontalPeriod (D.normalizedShear j) +
            m • verticalPeriodVector D.commonVerticalPeriod) +ᵥ D.selectedPiece j :=
        ⟨representative j a, hnorm, rfl⟩
      rw [hshift] at this
      simpa [add_assoc, add_comm, add_left_comm] using this

private theorem rationalSeparator_exists
    (u v : Tiling.Plane) (hvRe : 0 < v.re) (hvIm : 0 < v.im)
    (hslope : u.im / v.im < u.re / v.re) :
    ∃ q : Rat, 0 < u.re - q * v.re ∧ 0 < q * v.im - u.im := by
  obtain ⟨q, hqLower, hqUpper⟩ := exists_rat_btwn hslope
  refine ⟨q, ?_, ?_⟩
  · have := (lt_div_iff₀ hvRe).mp hqUpper
    simpa [sub_pos] using this
  · have := (div_lt_iff₀ hvIm).mp hqLower
    simpa [sub_pos, mul_comm] using this

/-- Both displayed basis vectors lie in the additive subgroup generated by a planar
lattice.  This is the production bridge needed after a geometric basis choice. -/
private theorem basis_mem_toAddSubgroup (L : PlanarLattice) (i : Fin 2) :
    L.basis i ∈ L.toAddSubgroup := by
  apply AddSubgroup.subset_closure
  exact ⟨i, rfl⟩

/-- Every full-rank planar lattice contains a vector in the open first quadrant. -/
private theorem exists_firstQuadrant_mem (L : PlanarLattice) :
    ∃ v ∈ L.toAddSubgroup, 0 < v.re ∧ 0 < v.im := by
  obtain ⟨R, hR, hcover⟩ :=
    Tiling.AxisParallel.Continuous.planarLattice_coveringRadius L
  let x : Tiling.Plane := Complex.mk (R + 1) (R + 1)
  obtain ⟨v, hvL, hvdist⟩ := hcover x
  refine ⟨v, hvL, ?_, ?_⟩
  · rw [dist_eq_norm] at hvdist
    have hre : |v.re - x.re| ≤ R := by
      exact (Complex.abs_re_le_norm (v - x)).trans hvdist
    have := (abs_le.mp hre).1
    dsimp [x] at this
    linarith
  · rw [dist_eq_norm] at hvdist
    have him : |v.im - x.im| ≤ R := by
      exact (Complex.abs_im_le_norm (v - x)).trans hvdist
    have := (abs_le.mp him).1
    dsimp [x] at this
    linarith

/-- A nonzero vector is independent from at least one member of a planar basis. -/
private theorem exists_basisVector_independent (L : PlanarLattice)
    (v : Tiling.Plane) (hv : v ≠ 0) :
    ∃ i : Fin 2, LinearIndependent ℝ ![L.basis i, v] := by
  let c := L.realBasis.repr v
  have hc : c ≠ 0 := by
    intro h
    apply hv
    apply L.realBasis.repr.injective
    dsimp [c] at h
    simpa only [map_zero] using h
  by_cases h1 : c 1 ≠ 0
  · refine ⟨0, ?_⟩
    rw [LinearIndependent.pair_iffₛ]
    intro s t s' t' h
    have h' : s • L.realBasis 0 + t • v = s' • L.realBasis 0 + t' • v := by
      simpa only [L.realBasis_apply] using h
    have hr := congrArg (fun z ↦ L.realBasis.repr z 1) h'
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply] at hr
    rw [L.realBasis.repr_self] at hr
    norm_num [Finsupp.single_apply] at hr
    dsimp [c] at h1
    have ht : t = t' := hr.resolve_right h1
    subst t'
    have hr0 := congrArg (fun z ↦ L.realBasis.repr z 0) h'
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply] at hr0
    rw [L.realBasis.repr_self] at hr0
    norm_num [Finsupp.single_apply] at hr0
    exact ⟨hr0, rfl⟩
  · have h0 : c 0 ≠ 0 := by
      intro hzero
      apply hc
      apply Finsupp.ext
      intro i
      fin_cases i
      · exact hzero
      · exact not_ne_iff.mp h1
    refine ⟨1, ?_⟩
    rw [LinearIndependent.pair_iffₛ]
    intro s t s' t' h
    have h' : s • L.realBasis 1 + t • v = s' • L.realBasis 1 + t' • v := by
      simpa only [L.realBasis_apply] using h
    have hr := congrArg (fun z ↦ L.realBasis.repr z 0) h'
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply] at hr
    rw [L.realBasis.repr_self] at hr
    norm_num [Finsupp.single_apply] at hr
    dsimp [c] at h0
    have ht : t = t' := hr.resolve_right h0
    subst t'
    have hr1 := congrArg (fun z ↦ L.realBasis.repr z 1) h'
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply] at hr1
    rw [L.realBasis.repr_self] at hr1
    norm_num [Finsupp.single_apply] at hr1
    exact ⟨hr1, rfl⟩

private theorem determinant_ne_zero_of_independent
    (u v : Tiling.Plane) (hvRe : 0 < v.re)
    (hIndependent : LinearIndependent ℝ ![u, v]) :
    u.re * v.im - u.im * v.re ≠ 0 := by
  intro hdet
  have hrel : v.re • u + (-u.re) • v = 0 := by
    apply Complex.ext
    · simp [mul_comm]
    · simp only [Complex.add_im, Complex.smul_im, Complex.zero_im]
      dsimp
      linarith
  have hcoeff := (LinearIndependent.pair_iffₛ.mp hIndependent)
    v.re (-u.re) 0 0 (by simpa using hrel)
  exact hvRe.ne' hcoeff.1

/-- Orienting the independent basis vector makes its determinant with `v` positive. -/
private theorem exists_orientedLatticePartner (L : PlanarLattice)
    (v : Tiling.Plane) (hvL : v ∈ L.toAddSubgroup) (hvRe : 0 < v.re) :
    ∃ u ∈ L.toAddSubgroup,
      LinearIndependent ℝ ![u, v] ∧ 0 < u.re * v.im - u.im * v.re := by
  have hv : v ≠ 0 := by
    intro h
    subst v
    simp at hvRe
  obtain ⟨i, hi⟩ := exists_basisVector_independent L v hv
  let u0 := L.basis i
  have hu0 : u0 ∈ L.toAddSubgroup := basis_mem_toAddSubgroup L i
  have hdet0 : u0.re * v.im - u0.im * v.re ≠ 0 :=
    determinant_ne_zero_of_independent u0 v hvRe hi
  rcases lt_or_gt_of_ne hdet0 with hneg | hpos
  · refine ⟨-u0, neg_mem hu0, ?_, ?_⟩
    · rw [LinearIndependent.pair_iffₛ]
      intro s t s' t' h
      have h' : (-s) • u0 + t • v = (-s') • u0 + t' • v := by
        simpa [neg_smul] using h
      obtain ⟨hs, ht⟩ := LinearIndependent.pair_iffₛ.mp hi _ _ _ _ h'
      exact ⟨neg_injective hs, ht⟩
    · change 0 < (-u0.re) * v.im - (-u0.im) * v.re
      linarith
  · exact ⟨u0, hu0, hi, hpos⟩

/-- The complete period-selection part of the frozen target. -/
private theorem rationallySeparatedPeriods_exists (L : PlanarLattice) :
    ∃ (u v : Tiling.Plane) (q : Rat),
      0 < v.re ∧ 0 < v.im ∧
      0 < u.re - q * v.re ∧ 0 < q * v.im - u.im ∧
      u ∈ L.toAddSubgroup ∧ v ∈ L.toAddSubgroup ∧
      LinearIndependent ℝ ![u, v] := by
  obtain ⟨v, hvL, hvRe, hvIm⟩ := exists_firstQuadrant_mem L
  obtain ⟨u, huL, hIndependent, hdet⟩ :=
    exists_orientedLatticePartner L v hvL hvRe
  have hslope : u.im / v.im < u.re / v.re := by
    rw [div_lt_div_iff₀ hvIm hvRe]
    linarith
  obtain ⟨q, hqRe, hqIm⟩ := rationalSeparator_exists u v hvRe hvIm hslope
  exact ⟨u, v, q, hvRe, hvIm, hqRe, hqIm, huL, hvL, hIndependent⟩

private noncomputable def pairLattice (u v : Tiling.Plane)
    (h : LinearIndependent ℝ ![u, v]) : PlanarLattice where
  basis := ![u, v]
  independent := h

private theorem pairLattice_floor_expansion (u v x : Tiling.Plane)
    (h : LinearIndependent ℝ ![u, v]) :
    ∃ n m : ℤ, (ZSpan.floor (pairLattice u v h).realBasis x : Tiling.Plane) =
      n • u + m • v := by
  let L := pairLattice u v h
  have hmem := (ZSpan.floor L.realBasis x).property
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc]
  simp [L, pairLattice, Fin.sum_univ_two]

private theorem finiteOrbitPresentation_of_independentPeriods
    {K : Region} {S : Set Tiling.Plane} (hTiles : TilesOn K S Set.univ)
    (u v : Tiling.Plane) (huPeriod : u ∈ periodGroup S)
    (hvPeriod : v ∈ periodGroup S)
    (hIndependent : LinearIndependent ℝ ![u, v]) :
    ∃ (r : Nat) (_hr : 0 < r) (representative : Fin r → Tiling.Plane),
      IsFiniteOrbitPresentation S u v representative := by
  let L := pairLattice u v hIndependent
  let b := L.realBasis
  let F : Set Tiling.Plane := ZSpan.fundamentalDomain b
  have hLF := (IsPacking.locallyFinite_centres hTiles.2.1).1
  have hfinite : (S ∩ F).Finite :=
    hLF F (ZSpan.fundamentalDomain_isBounded b)
  let R : Finset Tiling.Plane := hfinite.toFinset
  have hRset : (R : Set Tiling.Plane) = S ∩ F := by
    ext x
    simp [R]
  have hsubgroup : L.toAddSubgroup ≤ periodGroup S := by
    rw [PlanarLattice.toAddSubgroup, Tiling.Polygonal.PlanarLattice.toAddSubgroup,
      AddSubgroup.closure_le]
    rintro w ⟨i, rfl⟩
    fin_cases i
    · exact huPeriod
    · exact hvPeriod
  have hfractS (s : Tiling.Plane) (hs : s ∈ S) : ZSpan.fract b s ∈ S := by
    rw [ZSpan.fract_apply]
    have hfloor : (ZSpan.floor b s : Tiling.Plane) ∈ periodGroup S := by
      apply hsubgroup
      rw [← L.span_realBasis_toAddSubgroup]
      exact (ZSpan.floor b s).property
    have hneg : -(ZSpan.floor b s : Tiling.Plane) +ᵥ S = S :=
      (periodGroup_isAddSubgroup S _).mp (neg_mem hfloor)
    have hm : -(ZSpan.floor b s : Tiling.Plane) + s ∈
        -(ZSpan.floor b s : Tiling.Plane) +ᵥ S := ⟨s, hs, rfl⟩
    rw [hneg] at hm
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hm
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := hTiles.2.2.exists
    obtain ⟨s, hs⟩ := hx.mp (Set.mem_univ x)
    exact ⟨s.1, s.2⟩
  have hRne : R.Nonempty := by
    obtain ⟨s, hs⟩ := hSne
    let z := ZSpan.fract b s
    have hzS : z ∈ S := hfractS s hs
    have hzF : z ∈ F := ZSpan.fract_mem_fundamentalDomain b s
    refine ⟨z, ?_⟩
    change z ∈ (R : Set Tiling.Plane)
    rw [hRset]
    exact ⟨hzS, hzF⟩
  let representative : Fin R.card → Tiling.Plane :=
    fun a ↦ ((R.equivFin).symm a).1
  refine ⟨R.card, Finset.card_pos.mpr hRne, representative, ?_⟩
  ext p
  constructor
  · intro hp
    let z := ZSpan.fract b p
    have hzS : z ∈ S := hfractS p hp
    have hzF : z ∈ F := ZSpan.fract_mem_fundamentalDomain b p
    have hzR : z ∈ R := by
      change z ∈ (R : Set Tiling.Plane)
      rw [hRset]
      exact ⟨hzS, hzF⟩
    let a : Fin R.card := R.equivFin ⟨z, hzR⟩
    obtain ⟨n, m, hfloor⟩ := pairLattice_floor_expansion u v p hIndependent
    refine ⟨a, n, m, ?_⟩
    have ha : representative a = z := by
      simp [representative, a]
    rw [ha]
    dsimp [z, b, L]
    rw [ZSpan.fract_apply, hfloor]
    abel
  · rintro ⟨a, n, m, rfl⟩
    have hrepR : representative a ∈ R := by
      exact ((R.equivFin).symm a).2
    have hrepS : representative a ∈ S := by
      have := (show representative a ∈ (R : Set Tiling.Plane) from hrepR)
      rw [hRset] at this
      exact this.1
    have hperiod : n • u + m • v ∈ periodGroup S :=
      add_mem ((periodGroup S).zsmul_mem huPeriod n)
        ((periodGroup S).zsmul_mem hvPeriod m)
    have htranslate := (periodGroup_isAddSubgroup S _).mp hperiod
    have hm : (n • u + m • v) + representative a ∈
        (n • u + m • v) +ᵥ S := ⟨representative a, hrepS, rfl⟩
    rw [htranslate] at hm
    convert hm using 1
    abel

/-- The current production theorem completely supplies finite orbit representatives
for an already triangular pair of periods. -/
private theorem triangular_finiteOrbitRepresentatives
    {K : Region} {S : Set Tiling.Plane} {alpha beta shear : ℝ}
    (hAlpha : 0 < alpha) (hBeta : 0 < beta) (hTiles : TilesOn K S Set.univ)
    (hVertical : verticalPeriodVector alpha ∈ periodGroup S)
    (hSkew : skewPeriodVector beta shear ∈ periodGroup S) :
    ∃ R : Finset Tiling.Plane,
      (R : Set Tiling.Plane) ⊆ S ∧
      QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear) ''
          (R : Set Tiling.Plane) =
        QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear) '' S ∧
      Set.InjOn
        (QuotientAddGroup.mk' (triangularPeriodSubgroup alpha beta shear))
        (R : Set Tiling.Plane) := by
  exact exists_finiteOrbitRepresentatives hAlpha hBeta hTiles hVertical hSkew

/-- Every periodic replacement admits rationally separated independent lattice periods
and finitely many centre-orbit representatives. -/
private theorem lattice_rationallySeparatedPeriods :
    ∀ {K : Region} (D : PeriodicReplacement K Set.univ),
      Nonempty (FiniteLatticeOrbitPresentation D) := by
  intro K D
  obtain ⟨u, v, q, hvRe, hvIm, hqRe, hqIm, huL, hvL, hIndependent⟩ :=
    rationallySeparatedPeriods_exists D.lattice
  have huPeriod : u ∈ periodGroup D.centres := D.lattice_periods huL
  have hvPeriod : v ∈ periodGroup D.centres := D.lattice_periods hvL
  obtain ⟨r, hr, representative, hpresents⟩ :=
    finiteOrbitPresentation_of_independentPeriods D.tiles u v huPeriod hvPeriod hIndependent
  exact ⟨{
    firstPeriod := u
    secondPeriod := v
    rationalSeparator := q
    second_first_pos := hvRe
    second_second_pos := hvIm
    separated_first_pos := hqRe
    separated_second_pos := hqIm
    periods_mem := ⟨huL, hvL⟩
    independent := hIndependent
    representativeCount := r
    representativeCount_pos := hr
    representative := representative
    presents := hpresents
  }⟩
private def slabCenteredIntegerWIP {radius : Nat}
    (i : Fin (2 * radius + 1)) : Int :=
  Int.ofNat i.val - Int.ofNat radius

private def slabPieceCountWIP (c : RawTriangularCode) : Nat := c.pieces.length

private def slabPieceWIP (c : RawTriangularCode) (j : Fin (slabPieceCountWIP c)) :
    RawTriangularPieceCode := c.pieces.get j

private abbrev SlabFirstIndexWIP (c : RawTriangularCode) :=
  Fin (2 * (c.checkingRadius + 1) + 1)

private abbrev SlabSecondIndexWIP (c : RawTriangularCode) :=
  Fin (2 * (2 * c.checkingRadius + 3) + 1)

private abbrev SlabFiniteIndexWIP (c : RawTriangularCode)
    (j : Fin (slabPieceCountWIP c)) :=
  Fin (slabPieceWIP c j).representativeCount ×
    SlabFirstIndexWIP c × SlabSecondIndexWIP c

private def slabFiniteIndicesWIP (c : RawTriangularCode)
    (j : Fin (slabPieceCountWIP c)) : List (SlabFiniteIndexWIP c j) :=
  (List.ofFn fun r : Fin (slabPieceWIP c j).representativeCount => r).flatMap fun r =>
    (List.ofFn fun n : SlabFirstIndexWIP c => n).flatMap fun n =>
      List.ofFn fun k : SlabSecondIndexWIP c => (r, n, k)

private def slabSemanticCentreWIP (code : RawTriangularCode)
    (X : TriangularRawParameters code) (j : Fin (slabPieceCountWIP code))
    (r : Fin (slabPieceWIP code j).representativeCount) (n k : Int) :
    Tiling.Plane :=
  (X.representativeX ⟨j, r⟩ + n * X.beta) +
    (X.representativeY ⟨j, r⟩ + n * X.shear j + k * X.alpha) * Complex.I

private def slabSemanticOpenCellWIP {C : RegionCode} (R : Realization C)
    (epsilon : Bool) (e : Fin C.cellCount) (centre point : Tiling.Plane) : Prop :=
  centre.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) < point.re ∧
  point.re < centre.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) ∧
  centre.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)) < point.im ∧
  point.im < centre.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.rightVertex e else C.topVertex e))

private def slabSemanticClosedCellWIP {C : RegionCode} (R : Realization C)
    (epsilon : Bool) (e : Fin C.cellCount) (centre point : Tiling.Plane) : Prop :=
  centre.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) ≤ point.re ∧
  point.re ≤ centre.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) ∧
  centre.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)) ≤ point.im ∧
  point.im ≤ centre.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.rightVertex e else C.topVertex e))

private def slabSemanticCellsNonoverlapWIP {C : RegionCode} (R : Realization C)
    (epsilon : Bool) (e e' : Fin C.cellCount) (c c' : Tiling.Plane) : Prop :=
  c.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) ≤
    c'.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.bottomVertex e' else C.leftVertex e')) ∨
  c'.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.topVertex e' else C.rightVertex e')) ≤
    c.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) ∨
  c.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.rightVertex e else C.topVertex e)) ≤
    c'.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.leftVertex e' else C.bottomVertex e')) ∨
  c'.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.rightVertex e' else C.topVertex e')) ≤
    c.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e))

/-- Joint finite interval data for all slab colours. -/
private noncomputable def slabRawParametersWIP {K : Region} (D : SlabCertificate K)
    (base : FiniteSlabBasePresentation D) (orbit : FiniteSlabOrbitPresentation D)
    (radius : Nat) :
    TriangularRawParameters
      (slabRawCode D.orientation base.intervalCount orbit.representativeCount radius) := by
  let code := slabRawCode D.orientation base.intervalCount
    orbit.representativeCount radius
  have hcount : code.pieces.length = D.numberOfPieces := by
    simp [code, slabRawCode]
  refine {
    alpha := D.commonVerticalPeriod
    beta := D.commonHorizontalPeriod
    shear := fun i => D.normalizedShear
      ⟨i.val, by
        have hi := i.isLt
        change i.val < code.pieces.length at hi
        simpa [hcount] using hi⟩
    intervalLeft := fun i =>
      let jl : Fin code.pieces.length :=
        ⟨i.1.val, by
          have hi := i.1.isLt
          change i.1.val < code.pieces.length at hi
          exact hi⟩
      let j0 : Fin D.numberOfPieces := Fin.cast hcount jl
      base.left j0 (Fin.cast (by
        change (code.pieces.get jl).intervalCount = base.intervalCount j0
        rcases jl with ⟨v, hv⟩
        simp [code, slabRawCode, j0]) i.2)
    intervalRight := fun i =>
      let jl : Fin code.pieces.length :=
        ⟨i.1.val, by
          have hi := i.1.isLt
          change i.1.val < code.pieces.length at hi
          exact hi⟩
      let j0 : Fin D.numberOfPieces := Fin.cast hcount jl
      base.right j0 (Fin.cast (by
        change (code.pieces.get jl).intervalCount = base.intervalCount j0
        rcases jl with ⟨v, hv⟩
        simp [code, slabRawCode, j0]) i.2)
    representativeX := fun i =>
      let jl : Fin code.pieces.length :=
        ⟨i.1.val, by
          have hi := i.1.isLt
          change i.1.val < code.pieces.length at hi
          exact hi⟩
      let j0 : Fin D.numberOfPieces := Fin.cast hcount jl
      (orbit.representative j0 (Fin.cast (by
        change (code.pieces.get jl).representativeCount = orbit.representativeCount j0
        rcases jl with ⟨v, hv⟩
        simp [code, slabRawCode, j0]) i.2)).re
    representativeY := fun i =>
      let jl : Fin code.pieces.length :=
        ⟨i.1.val, by
          have hi := i.1.isLt
          change i.1.val < code.pieces.length at hi
          exact hi⟩
      let j0 : Fin D.numberOfPieces := Fin.cast hcount jl
      (orbit.representative j0 (Fin.cast (by
        change (code.pieces.get jl).representativeCount = orbit.representativeCount j0
        rcases jl with ⟨v, hv⟩
        simp [code, slabRawCode, j0]) i.2)).im }

private theorem slabRawParametersWIP_periods_pos {K : Region}
    (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (orbit : FiniteSlabOrbitPresentation D) (radius : Nat) :
    let X := slabRawParametersWIP D base orbit radius
    0 < X.alpha ∧ 0 < X.beta := by
  dsimp
  exact ⟨D.commonVerticalPeriod_pos, D.commonHorizontalPeriod_pos⟩

private theorem slabRawParametersWIP_shear_normalized {K : Region}
    (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (orbit : FiniteSlabOrbitPresentation D) (radius : Nat) :
    let code := slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius
    let X := slabRawParametersWIP D base orbit radius
    ∀ j : Fin code.pieces.length, 0 ≤ X.shear j ∧ X.shear j < X.alpha := by
  dsimp
  intro j
  let j0 : Fin D.numberOfPieces := ⟨j.val, by
    simpa [slabRawCode] using j.isLt⟩
  simpa [slabRawParametersWIP, j0] using
    And.intro (D.normalizedShear_nonnegative j0) (D.normalizedShear_lt j0)

private theorem slabRawParametersWIP_intervals_normalized {K : Region}
    (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (orbit : FiniteSlabOrbitPresentation D) (radius : Nat) :
    let code := slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius
    let X := slabRawParametersWIP D base orbit radius
    ∀ i : Sigma fun j : Fin code.pieces.length =>
        Fin (code.pieces.get j).intervalCount,
      0 ≤ X.intervalLeft i ∧ X.intervalLeft i < X.intervalRight i ∧
        X.intervalRight i ≤ X.beta := by
  dsimp
  rintro ⟨j, ell⟩
  let j0 : Fin D.numberOfPieces := ⟨j.val, by
    simpa [slabRawCode] using j.isLt⟩
  have hell : ell.val < base.intervalCount j0 := by
    have h := ell.isLt
    rcases j with ⟨v, hv⟩
    simpa [slabRawCode, j0] using h
  let ell0 : Fin (base.intervalCount j0) := ⟨ell.val, hell⟩
  let jx : Fin D.numberOfPieces := ⟨j.val, by
    simpa [slabRawCode] using j.isLt⟩
  change 0 ≤ base.left jx (Fin.cast _ ell) ∧
    base.left jx (Fin.cast _ ell) < base.right jx (Fin.cast _ ell) ∧
    base.right jx (Fin.cast _ ell) ≤ D.commonHorizontalPeriod
  have hj : jx = j0 := Fin.ext rfl
  cases hj
  have hinner :
      ((slabRawCode D.orientation base.intervalCount orbit.representativeCount
        radius).pieces.get j).intervalCount = base.intervalCount j0 := by
    rcases j with ⟨v, hv⟩
    simp [slabRawCode, j0]
  let ellx : Fin (base.intervalCount j0) := Fin.cast hinner ell
  change 0 ≤ base.left j0 ellx ∧
    base.left j0 ellx < base.right j0 ellx ∧
    base.right j0 ellx ≤ D.commonHorizontalPeriod
  have he : ellx = ell0 := Fin.ext rfl
  rw [he]
  exact base.normalized j0 ell0

private theorem slabRawParametersWIP_representatives_normalized {K : Region}
    (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (orbit : FiniteSlabOrbitPresentation D) (radius : Nat) :
    let code := slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius
    let X := slabRawParametersWIP D base orbit radius
    ∀ i : Sigma fun j : Fin code.pieces.length =>
        Fin (code.pieces.get j).representativeCount,
      (0 ≤ X.representativeX i ∧ X.representativeX i < X.beta) ∧
        0 ≤ X.representativeY i ∧ X.representativeY i < X.alpha := by
  dsimp
  rintro ⟨j, a⟩
  let j0 : Fin D.numberOfPieces := ⟨j.val, by
    simpa [slabRawCode] using j.isLt⟩
  have ha : a.val < orbit.representativeCount j0 := by
    have h := a.isLt
    rcases j with ⟨v, hv⟩
    simpa [slabRawCode, j0] using h
  let a0 : Fin (orbit.representativeCount j0) := ⟨a.val, ha⟩
  let jx : Fin D.numberOfPieces := ⟨j.val, by
    simpa [slabRawCode] using j.isLt⟩
  change (0 ≤ (orbit.representative jx (Fin.cast _ a)).re ∧
      (orbit.representative jx (Fin.cast _ a)).re < D.commonHorizontalPeriod) ∧
    0 ≤ (orbit.representative jx (Fin.cast _ a)).im ∧
      (orbit.representative jx (Fin.cast _ a)).im < D.commonVerticalPeriod
  have hj : jx = j0 := Fin.ext rfl
  cases hj
  have hinner :
      ((slabRawCode D.orientation base.intervalCount orbit.representativeCount
        radius).pieces.get j).representativeCount = orbit.representativeCount j0 := by
    rcases j with ⟨v, hv⟩
    simp [slabRawCode, j0]
  let ax : Fin (orbit.representativeCount j0) := Fin.cast hinner a
  change (0 ≤ (orbit.representative j0 ax).re ∧
      (orbit.representative j0 ax).re < D.commonHorizontalPeriod) ∧
    0 ≤ (orbit.representative j0 ax).im ∧
      (orbit.representative j0 ax).im < D.commonVerticalPeriod
  have he : ax = a0 := Fin.ext rfl
  rw [he]
  rcases orbit.normalized j0 a0 with ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨⟨h₁, h₂⟩, h₃, h₄⟩

private theorem slabRawParametersWIP_vertex_diameter_bounds
    {C : RegionCode} (R : Realization C) (D : SlabCertificate R.region)
    (base : FiniteSlabBasePresentation D) (orbit : FiniteSlabOrbitPresentation D)
    (radius : Nat)
    (hhorizontal : ∀ a b,
      |selectedCoordinate D.orientation .horizontal (R.vertex a) -
        selectedCoordinate D.orientation .horizontal (R.vertex b)| <
          radius * D.commonHorizontalPeriod)
    (hvertical : ∀ a b,
      |selectedCoordinate D.orientation .vertical (R.vertex a) -
        selectedCoordinate D.orientation .vertical (R.vertex b)| <
          radius * D.commonVerticalPeriod) :
    let code := slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius
    let X := slabRawParametersWIP D base orbit radius
    (∀ a b, |selectedCoordinate code.orientation .horizontal (R.vertex a) -
      selectedCoordinate code.orientation .horizontal (R.vertex b)| <
        code.checkingRadius * X.beta) ∧
    (∀ a b, |selectedCoordinate code.orientation .vertical (R.vertex a) -
      selectedCoordinate code.orientation .vertical (R.vertex b)| <
        code.checkingRadius * X.alpha) := by
  exact ⟨hhorizontal, hvertical⟩

private theorem slabRawParametersWIP_base_period_covered {K : Region}
    (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (orbit : FiniteSlabOrbitPresentation D) (radius : Nat) :
    let code := slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius
    let X := slabRawParametersWIP D base orbit radius
    ∀ x, 0 < x → x < X.beta →
      ∃ i : Sigma fun j : Fin code.pieces.length =>
        Fin (code.pieces.get j).intervalCount,
        X.intervalLeft i ≤ x ∧ x ≤ X.intervalRight i := by
  dsimp
  intro x hx0 hxp
  obtain ⟨j0, ell0, hx⟩ := base.period_closed_cover x hx0 hxp
  let code := slabRawCode D.orientation base.intervalCount
    orbit.representativeCount radius
  have hcount : code.pieces.length = D.numberOfPieces := by
    simp [code, slabRawCode]
  let j : Fin code.pieces.length := Fin.cast hcount.symm j0
  have hinner : (code.pieces.get j).intervalCount = base.intervalCount j0 := by
    rcases j0 with ⟨v, hv⟩
    simp [code, slabRawCode, j]
  let ell : Fin (code.pieces.get j).intervalCount := Fin.cast hinner.symm ell0
  refine ⟨⟨j, ell⟩, ?_⟩
  change base.left j0 (Fin.cast _ ell) ≤ x ∧
    x ≤ base.right j0 (Fin.cast _ ell)
  let ellx : Fin (base.intervalCount j0) := Fin.cast hinner ell
  change base.left j0 ellx ≤ x ∧ x ≤ base.right j0 ellx
  have he : ellx = ell0 := Fin.ext rfl
  rw [he]
  exact hx

private noncomputable def slabIntervalIndexToBaseWIP {K : Region}
    (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (orbit : FiniteSlabOrbitPresentation D) (radius : Nat)
    (i : Sigma fun j : Fin
        (slabRawCode D.orientation base.intervalCount orbit.representativeCount
          radius).pieces.length =>
      Fin ((slabRawCode D.orientation base.intervalCount orbit.representativeCount
        radius).pieces.get j).intervalCount) :
    Sigma fun j : Fin D.numberOfPieces => Fin (base.intervalCount j) := by
  rcases i with ⟨j, ell⟩
  let code := slabRawCode D.orientation base.intervalCount
    orbit.representativeCount radius
  have hcount : code.pieces.length = D.numberOfPieces := by
    simp [code, slabRawCode]
  let j0 : Fin D.numberOfPieces := Fin.cast hcount j
  have hinner : (code.pieces.get j).intervalCount = base.intervalCount j0 := by
    rcases j with ⟨v, hv⟩
    simp [code, slabRawCode, j0]
  exact ⟨j0, Fin.cast hinner ell⟩

private theorem slabIntervalIndexToBaseWIP_injective {K : Region}
    (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (orbit : FiniteSlabOrbitPresentation D) (radius : Nat) :
    Function.Injective (slabIntervalIndexToBaseWIP D base orbit radius) := by
  rintro ⟨j, ell⟩ ⟨j', ell'⟩ h
  have hj : j = j' := Fin.ext (congrArg (fun z => z.1.val) h)
  subst j'
  congr 1
  apply Fin.ext
  exact congrArg (fun z => z.2.val) h

private theorem slabRawParametersWIP_interval_interiors_disjoint {K : Region}
    (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (orbit : FiniteSlabOrbitPresentation D) (radius : Nat) :
    let code := slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius
    let X := slabRawParametersWIP D base orbit radius
    ∀ i i' : Sigma fun j : Fin code.pieces.length =>
        Fin (code.pieces.get j).intervalCount,
      i ≠ i' →
      X.intervalRight i ≤ X.intervalLeft i' ∨
        X.intervalRight i' ≤ X.intervalLeft i := by
  dsimp
  intro i i' hne
  rcases i with ⟨j, ell⟩
  rcases i' with ⟨j', ell'⟩
  let a := slabIntervalIndexToBaseWIP D base orbit radius ⟨j, ell⟩
  let b := slabIntervalIndexToBaseWIP D base orbit radius ⟨j', ell'⟩
  have hab : a ≠ b := fun h => hne
    (slabIntervalIndexToBaseWIP_injective D base orbit radius h)
  have hd := base.interiors_disjoint a.1 a.2 b.1 b.2 hab
  change base.right a.1 a.2 ≤ base.left b.1 b.2 ∨
    base.right b.1 b.2 ≤ base.left a.1 a.2
  exact hd

private theorem slabAe_inter_measure_ne_zero_of_open_subset
    {U A B K K' : Set Tiling.Plane}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hUA : U ⊆ A) (hUB : U ⊆ B)
    (hAK : A =ᵐ[volume] K) (hBK : B =ᵐ[volume] K') :
    volume (K ∩ K') ≠ 0 := by
  intro hzero
  have hinter : (A ∩ B : Set Tiling.Plane) =ᵐ[volume] (K ∩ K' : Set Tiling.Plane) := by
    filter_upwards [hAK, hBK] with z hzA hzB
    change (z ∈ A) = (z ∈ K) at hzA
    change (z ∈ B) = (z ∈ K') at hzB
    change (z ∈ A ∧ z ∈ B) = (z ∈ K ∧ z ∈ K')
    rw [hzA, hzB]
  have habZero : volume (A ∩ B) = 0 := by
    rw [measure_congr hinter]
    exact hzero
  have hUzero : volume U = 0 :=
    measure_mono_null (fun z hz => And.intro (hUA hz) (hUB hz)) habZero
  exact (hUopen.measure_pos volume hUne).ne' hUzero

private theorem slabSemanticCentreWIP_mem_selectedPiece
    {K : Region} (D : SlabCertificate K) (orbit : FiniteSlabOrbitPresentation D)
    (j : Fin D.numberOfPieces) (r : Fin (orbit.representativeCount j))
    (n k : Int) :
    (orbit.representative j r).re + n * D.commonHorizontalPeriod +
        ((orbit.representative j r).im + n * D.normalizedShear j +
          k * D.commonVerticalPeriod) * Complex.I ∈ D.selectedPiece j := by
  rw [orbit.presents]
  refine ⟨r, n, k, ?_⟩
  apply Complex.ext
  · simp [skewPeriodVector, verticalPeriodVector, mul_comm, mul_left_comm]
  · simp [skewPeriodVector, verticalPeriodVector, mul_comm, mul_left_comm]

private theorem regularOpen_real_eq_of_aeEq
    {U V : Set ℝ} (hU : IsOpen U) (hUregular : interior (closure U) = U)
    (hV : IsOpen V) (hVregular : interior (closure V) = V)
    (hUV : U =ᵐ[volume] V) : U = V := by
  have closure_mono_of_ae {A B : Set ℝ} (hA : IsOpen A) (hB : IsOpen B)
      (hAB : A =ᵐ[volume] B) : A ⊆ closure B := by
    intro x hxA
    by_contra hxB
    let W := A ∩ (closure B)ᶜ
    have hWopen : IsOpen W := hA.inter isClosed_closure.isOpen_compl
    have hxW : x ∈ W := ⟨hxA, hxB⟩
    have hWzero : volume W = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr (hAB.mono fun y hy hyW ↦ by
        have hyB : y ∈ B := Eq.mp hy hyW.1
        exact hyW.2 (subset_closure hyB))
    exact hWopen.measure_ne_zero volume ⟨x, hxW⟩ hWzero
  have hclosure : closure U = closure V := Set.Subset.antisymm
    (closure_minimal (closure_mono_of_ae hU hV hUV) isClosed_closure)
    (closure_minimal (closure_mono_of_ae hV hU hUV.symm) isClosed_closure)
  calc
    U = interior (closure U) := hUregular.symm
    _ = interior (closure V) := congrArg interior hclosure
    _ = V := hVregular

private theorem slabBase_commonHorizontalPeriod
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces) :
    D.commonHorizontalPeriod +ᵥ D.base j = D.base j := by
  have hae := support_aePeriod_of_centrePeriod
    (D.base_open j).measurableSet (D.piece_tiles j) (D.common_skewPeriod j)
  have hopen : IsOpen (D.commonHorizontalPeriod +ᵥ D.base j) :=
    (D.base_open j).vadd D.commonHorizontalPeriod
  have hregular : interior (closure (D.commonHorizontalPeriod +ᵥ D.base j)) =
      D.commonHorizontalPeriod +ᵥ D.base j := by
    rw [closure_vadd, interior_vadd, D.base_regular j]
  exact regularOpen_real_eq_of_aeEq hopen hregular (D.base_open j) (D.base_regular j)
    (by simpa [skewPeriodVector] using hae)

private theorem slabBases_pairwiseDisjoint
    {K : Region} (D : SlabCertificate K) :
    Set.Pairwise Set.univ fun i j ↦ Disjoint (D.base i) (D.base j) := by
  intro i _hi j _hj hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hne : volume (D.base i ∩ D.base j) ≠ 0 :=
    ((D.base_open i).inter (D.base_open j)).measure_ne_zero volume ⟨x, hxi, hxj⟩
  exact hne (D.bases_pairwise_aeDisjoint (Set.mem_univ i) (Set.mem_univ j) hij)

private theorem slabBases_union_dense
    {K : Region} (D : SlabCertificate K) :
    closure (⋃ j, D.base j) = Set.univ := by
  apply eq_univ_of_forall
  intro x
  rw [mem_closure_iff]
  intro U hUopen hxU
  by_contra hdisj
  have hUsub : U ⊆ (⋃ j, D.base j)ᶜ := by
    intro y hyU hybase
    exact hdisj ⟨y, hyU, hybase⟩
  have hUnull : volume U = 0 := by
    apply measure_mono_null hUsub
    simpa using D.bases_cover.compl.measure_eq
  exact (hUopen.measure_pos volume ⟨x, hxU⟩).ne' hUnull

private theorem slabBase_frontier_locallyFinite
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces) :
    ∀ C : Set ℝ, IsCompact C → (C ∩ frontier (D.base j)).Finite :=
  (D.piece_tiles j).verticalCylinder_frontier_locallyFinite
    (D.base_open j) (D.base_regular j)

private noncomputable def slabBaseCellFrontier
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces) : Finset ℝ :=
  (slabBase_frontier_locallyFinite D j (Set.Icc 0 D.commonHorizontalPeriod)
    isCompact_Icc).toFinset

private theorem mem_slabBaseCellFrontier_iff
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces) (x : ℝ) :
    x ∈ slabBaseCellFrontier D j ↔
      x ∈ Set.Icc 0 D.commonHorizontalPeriod ∩ frontier (D.base j) := by
  simp [slabBaseCellFrontier]

private noncomputable def slabAllCellCuts
    {K : Region} (D : SlabCertificate K) : Finset ℝ :=
  {0, D.commonHorizontalPeriod} ∪
    Finset.univ.biUnion fun j : Fin D.numberOfPieces ↦ slabBaseCellFrontier D j

private theorem slabAllCellCuts_zero_mem
    {K : Region} (D : SlabCertificate K) : 0 ∈ slabAllCellCuts D := by
  simp [slabAllCellCuts]

private theorem slabAllCellCuts_period_mem
    {K : Region} (D : SlabCertificate K) :
    D.commonHorizontalPeriod ∈ slabAllCellCuts D := by
  simp [slabAllCellCuts]

private theorem frontier_mem_slabAllCellCuts
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces)
    {x : ℝ} (hx : x ∈ Set.Icc 0 D.commonHorizontalPeriod)
    (hfrontier : x ∈ frontier (D.base j)) : x ∈ slabAllCellCuts D := by
  rw [slabAllCellCuts, Finset.mem_union]
  right
  rw [Finset.mem_biUnion]
  exact ⟨j, Finset.mem_univ _, (mem_slabBaseCellFrontier_iff D j x).2
    ⟨hx, hfrontier⟩⟩

private theorem slabAllCellCuts_card_two_le
    {K : Region} (D : SlabCertificate K) : 2 ≤ (slabAllCellCuts D).card := by
  have hsubset : ({0, D.commonHorizontalPeriod} : Finset ℝ) ⊆
      slabAllCellCuts D := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact slabAllCellCuts_zero_mem D
    · exact slabAllCellCuts_period_mem D
  have hcard := Finset.card_le_card hsubset
  have hne : (0 : ℝ) ≠ D.commonHorizontalPeriod :=
    D.commonHorizontalPeriod_pos.ne
  have hpair : ({0, D.commonHorizontalPeriod} : Finset ℝ).card = 2 := by
    simp [hne]
  omega

private noncomputable def slabElementaryIntervalCount
    {K : Region} (D : SlabCertificate K) : Nat :=
  (slabAllCellCuts D).card - 1

private theorem slabElementaryIntervalCount_pos
    {K : Region} (D : SlabCertificate K) : 0 < slabElementaryIntervalCount D := by
  unfold slabElementaryIntervalCount
  have hcard := slabAllCellCuts_card_two_le D
  omega

private theorem slabAllCellCuts_subset_Icc
    {K : Region} (D : SlabCertificate K) :
    ↑(slabAllCellCuts D) ⊆ Set.Icc 0 D.commonHorizontalPeriod := by
  intro x hx
  change x ∈ slabAllCellCuts D at hx
  rw [slabAllCellCuts, Finset.mem_union] at hx
  rcases hx with hx | hx
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨le_rfl, D.commonHorizontalPeriod_pos.le⟩
    · exact ⟨D.commonHorizontalPeriod_pos.le, le_rfl⟩
  · rw [Finset.mem_biUnion] at hx
    obtain ⟨j, _hj, hxj⟩ := hx
    exact (mem_slabBaseCellFrontier_iff D j x).1 hxj |>.1

private noncomputable def slabCutList
    {K : Region} (D : SlabCertificate K) : List ℝ :=
  (slabAllCellCuts D).sort

private theorem slabCutList_length
    {K : Region} (D : SlabCertificate K) :
    (slabCutList D).length = (slabAllCellCuts D).card := by
  simp [slabCutList]

private noncomputable def slabElementaryLeft
    {K : Region} (D : SlabCertificate K)
    (i : Fin (slabElementaryIntervalCount D)) : ℝ :=
  (slabCutList D).get ⟨i, by
    rw [slabCutList_length]
    have hi := i.isLt
    unfold slabElementaryIntervalCount at hi
    omega⟩

private noncomputable def slabElementaryRight
    {K : Region} (D : SlabCertificate K)
    (i : Fin (slabElementaryIntervalCount D)) : ℝ :=
  (slabCutList D).get ⟨i + 1, by
    rw [slabCutList_length]
    have hi := i.isLt
    unfold slabElementaryIntervalCount at hi
    have hcard := slabAllCellCuts_card_two_le D
    omega⟩

private theorem slabElementaryLeft_lt_right
    {K : Region} (D : SlabCertificate K)
    (i : Fin (slabElementaryIntervalCount D)) :
    slabElementaryLeft D i < slabElementaryRight D i := by
  unfold slabElementaryLeft slabElementaryRight slabCutList
  apply (slabAllCellCuts D).sortedLT_sort
  change (i : Nat) < i + 1
  omega

private theorem slabElementary_normalized
    {K : Region} (D : SlabCertificate K)
    (i : Fin (slabElementaryIntervalCount D)) :
    0 ≤ slabElementaryLeft D i ∧
      slabElementaryLeft D i < slabElementaryRight D i ∧
      slabElementaryRight D i ≤ D.commonHorizontalPeriod := by
  have hleftMem : slabElementaryLeft D i ∈ slabAllCellCuts D := by
    unfold slabElementaryLeft slabCutList
    exact (Finset.mem_sort (α := ℝ) (· ≤ ·)).1 (List.get_mem _ _)
  have hrightMem : slabElementaryRight D i ∈ slabAllCellCuts D := by
    unfold slabElementaryRight slabCutList
    exact (Finset.mem_sort (α := ℝ) (· ≤ ·)).1 (List.get_mem _ _)
  exact ⟨(slabAllCellCuts_subset_Icc D hleftMem).1,
    slabElementaryLeft_lt_right D i,
    (slabAllCellCuts_subset_Icc D hrightMem).2⟩

private theorem slabElementary_no_cut
    {K : Region} (D : SlabCertificate K)
    (i : Fin (slabElementaryIntervalCount D)) :
    Disjoint (Set.Ioo (slabElementaryLeft D i) (slabElementaryRight D i))
      (slabAllCellCuts D : Set ℝ) := by
  rw [Set.disjoint_left]
  intro x hxI hxCut
  have hxList : x ∈ slabCutList D := by
    rw [slabCutList, Finset.mem_sort]
    exact hxCut
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hxList
  let il : Fin (slabCutList D).length := ⟨i, by
    rw [slabCutList_length]
    have hi := i.isLt
    unfold slabElementaryIntervalCount at hi
    omega⟩
  let ir : Fin (slabCutList D).length := ⟨i + 1, by
    rw [slabCutList_length]
    have hi := i.isLt
    unfold slabElementaryIntervalCount at hi
    have hcard := slabAllCellCuts_card_two_le D
    omega⟩
  have hik : (i : Nat) < k := by
    change il < k
    apply ((slabAllCellCuts D).sortedLT_sort.lt_iff_lt).mp
    change (slabCutList D).get il < (slabCutList D).get k
    rw [show (slabCutList D).get il = slabElementaryLeft D i by rfl, hk]
    exact hxI.1
  have hki : k < (i : Nat) + 1 := by
    change k < ir
    apply ((slabAllCellCuts D).sortedLT_sort.lt_iff_lt).mp
    change (slabCutList D).get k < (slabCutList D).get ir
    rw [hk, show (slabCutList D).get ir = slabElementaryRight D i by rfl]
    exact hxI.2
  omega

private theorem slabElementary_disjoint_frontier
    {K : Region} (D : SlabCertificate K)
    (i : Fin (slabElementaryIntervalCount D))
    (j : Fin D.numberOfPieces) :
    Disjoint (Set.Ioo (slabElementaryLeft D i) (slabElementaryRight D i))
      (frontier (D.base j)) := by
  rw [Set.disjoint_left]
  intro x hxI hxF
  have hnorm := slabElementary_normalized D i
  have hxCell : x ∈ Set.Icc 0 D.commonHorizontalPeriod :=
    ⟨hnorm.1.trans hxI.1.le, hxI.2.le.trans hnorm.2.2⟩
  have hxCut := frontier_mem_slabAllCellCuts D j hxCell hxF
  exact Set.disjoint_left.1 (slabElementary_no_cut D i) hxI hxCut

private theorem slabElementary_has_uniqueBase
    {K : Region} (D : SlabCertificate K)
    (i : Fin (slabElementaryIntervalCount D)) :
    ∃! j : Fin D.numberOfPieces,
      Set.Ioo (slabElementaryLeft D i) (slabElementaryRight D i) ⊆ D.base j := by
  let m := (slabElementaryLeft D i + slabElementaryRight D i) / 2
  have hm : m ∈ Set.Ioo (slabElementaryLeft D i) (slabElementaryRight D i) := by
    dsimp [m]
    constructor <;> linarith [slabElementaryLeft_lt_right D i]
  have hmclosure : m ∈ closure (⋃ j, D.base j) := by
    rw [slabBases_union_dense D]
    exact Set.mem_univ m
  obtain ⟨y, hyI, hybase⟩ := mem_closure_iff.mp hmclosure
    (Set.Ioo (slabElementaryLeft D i) (slabElementaryRight D i)) isOpen_Ioo hm
  obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hybase
  have hsubInterior :
      Set.Ioo (slabElementaryLeft D i) (slabElementaryRight D i) ⊆
        interior (D.base j) :=
    Tiling.IsPreconnected.subset_interior_of_disjoint_frontier_of_mem
      isPreconnected_Ioo (slabElementary_disjoint_frontier D i j) hyI hyj
  refine ⟨j, hsubInterior.trans interior_subset, ?_⟩
  intro j' hj'
  by_contra hne
  have hdisj := slabBases_pairwiseDisjoint D (Set.mem_univ j)
    (Set.mem_univ j') (Ne.symm hne)
  exact Set.disjoint_left.1 hdisj
    (hsubInterior.trans interior_subset hyI) (hj' hyI)

private noncomputable def slabElementaryLabel
    {K : Region} (D : SlabCertificate K)
    (i : Fin (slabElementaryIntervalCount D)) : Fin D.numberOfPieces :=
  Classical.choose (slabElementary_has_uniqueBase D i)

private theorem slabElementary_subset_label
    {K : Region} (D : SlabCertificate K)
    (i : Fin (slabElementaryIntervalCount D)) :
    Set.Ioo (slabElementaryLeft D i) (slabElementaryRight D i) ⊆
      D.base (slabElementaryLabel D i) :=
  (Classical.choose_spec (slabElementary_has_uniqueBase D i)).1

private theorem open_periodic_exists_mem_Ioo
    {X : Set ℝ} {p : ℝ} (hp : 0 < p) (hXopen : IsOpen X)
    (hXne : X.Nonempty) (hperiod : p +ᵥ X = X) :
    ∃ x ∈ Set.Ioo (0 : ℝ) p, x ∈ X := by
  obtain ⟨x, hx⟩ := hXne
  let n : ℤ := ⌊x / p⌋
  let y : ℝ := x - n * p
  have hnle : (n : ℝ) ≤ x / p := Int.floor_le _
  have hnlt : x / p < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact sub_nonneg.mpr ((le_div_iff₀ hp).mp hnle)
  have hyp : y < p := by
    dsimp [y]
    have := (div_lt_iff₀ hp).mp hnlt
    linarith
  have hpGroup : p ∈ periodGroup X :=
    (periodGroup_isAddSubgroup X p).mpr hperiod
  have hshift : ((-n : ℤ) • p : ℝ) +ᵥ X = X :=
    (periodGroup_isAddSubgroup X _).mp ((periodGroup X).zsmul_mem hpGroup (-n))
  have hyX : y ∈ X := by
    have : ((-n : ℤ) • p : ℝ) + x ∈ ((-n : ℤ) • p : ℝ) +ᵥ X :=
      ⟨x, hx, rfl⟩
    rw [hshift] at this
    simpa [y, sub_eq_add_neg, add_comm] using this
  rcases hy0.eq_or_lt with hyzero | hypos
  · have hX0 : (0 : ℝ) ∈ X := by rwa [← hyzero] at hyX
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hXopen 0 hX0
    let δ := min (ε / 2) (p / 2)
    have hδ : 0 < δ := lt_min (half_pos hε) (half_pos hp)
    have hδp : δ < p := (min_le_right _ _).trans_lt (half_lt_self hp)
    have hδball : δ ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
      simpa [abs_of_pos hδ] using hδε
    exact ⟨δ, ⟨hδ, hδp⟩, hball hδball⟩
  · exact ⟨y, ⟨hypos, hyp⟩, hyX⟩

private theorem exists_elementaryGap_of_mem_Ioo_not_cut
    {K : Region} (D : SlabCertificate K) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) D.commonHorizontalPeriod)
    (hxcut : x ∉ slabAllCellCuts D) :
    ∃ i : Fin (slabElementaryIntervalCount D),
      x ∈ Set.Ioo (slabElementaryLeft D i) (slabElementaryRight D i) := by
  let lower := (slabAllCellCuts D).filter (· < x)
  have hzeroLower : 0 ∈ lower := by
    simp [lower, slabAllCellCuts_zero_mem D, hx.1]
  have hlower : lower.Nonempty := ⟨0, hzeroLower⟩
  let left := lower.max' hlower
  have hleftCut : left ∈ slabAllCellCuts D := by
    exact (Finset.mem_filter.mp (lower.max'_mem hlower)).1
  have hleftx : left < x := by
    exact (Finset.mem_filter.mp (lower.max'_mem hlower)).2
  have hleftList : left ∈ slabCutList D := by
    rw [slabCutList, Finset.mem_sort]
    exact hleftCut
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hleftList
  have hpList : D.commonHorizontalPeriod ∈ slabCutList D := by
    rw [slabCutList, Finset.mem_sort]
    exact slabAllCellCuts_period_mem D
  obtain ⟨kp, hkp⟩ := List.mem_iff_get.mp hpList
  have hkkp : k < kp := by
    apply ((slabAllCellCuts D).sortedLT_sort.lt_iff_lt).mp
    change (slabCutList D).get k < (slabCutList D).get kp
    rw [hk, hkp]
    exact hleftx.trans hx.2
  have hkSucc : (k : Nat) + 1 < (slabCutList D).length := by
    exact (Nat.add_one_le_iff.mpr hkkp).trans_lt kp.isLt
  have hkCount : (k : Nat) < slabElementaryIntervalCount D := by
    have hlen := slabCutList_length D
    unfold slabElementaryIntervalCount
    omega
  let i : Fin (slabElementaryIntervalCount D) := ⟨k, hkCount⟩
  refine ⟨i, ?_, ?_⟩
  · unfold slabElementaryLeft
    rw [show (⟨i, by
      rw [slabCutList_length]
      have hi := i.isLt
      unfold slabElementaryIntervalCount at hi
      omega⟩ : Fin (slabCutList D).length) = k by apply Fin.ext; rfl, hk]
    exact hleftx
  · let ks : Fin (slabCutList D).length := ⟨k + 1, hkSucc⟩
    have hrightCut : (slabCutList D).get ks ∈ slabAllCellCuts D := by
      rw [← Finset.mem_sort (s := slabAllCellCuts D) (r := (· ≤ ·))]
      exact List.get_mem _ _
    have hleftRight : left < (slabCutList D).get ks := by
      rw [← hk]
      apply (slabAllCellCuts D).sortedLT_sort
      change (k : Nat) < k + 1
      omega
    have hxright : x < (slabCutList D).get ks := by
      by_contra hnot
      have hle : (slabCutList D).get ks ≤ x := le_of_not_gt hnot
      have hne : (slabCutList D).get ks ≠ x := fun heq ↦
        hxcut (heq ▸ hrightCut)
      have hlt : (slabCutList D).get ks < x := lt_of_le_of_ne hle hne
      have hmemLower : (slabCutList D).get ks ∈ lower := by
        exact Finset.mem_filter.mpr ⟨hrightCut, hlt⟩
      exact (not_lt_of_ge (lower.le_max' _ hmemLower)) hleftRight
    simpa [slabElementaryRight, i, ks] using hxright

private theorem slabBase_occurs_as_elementaryLabel
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces) :
    ∃ i : Fin (slabElementaryIntervalCount D), slabElementaryLabel D i = j := by
  obtain ⟨x, hxCell, hxBase⟩ := open_periodic_exists_mem_Ioo
    D.commonHorizontalPeriod_pos (D.base_open j) (D.base_nonempty j)
    (slabBase_commonHorizontalPeriod D j)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (D.base_open j) x hxBase
  let δ := min (ε / 2) (min (x / 2) ((D.commonHorizontalPeriod - x) / 2))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos hε) (lt_min (half_pos hxCell.1)
      (half_pos (sub_pos.mpr hxCell.2)))
  have hinfinite : (Set.Ioo (x - δ) (x + δ)).Infinite :=
    Set.Ioo_infinite (by linarith)
  obtain ⟨y, hySmall, hyCut⟩ :=
    hinfinite.exists_notMem_finset (slabAllCellCuts D)
  have hyCell : y ∈ Set.Ioo (0 : ℝ) D.commonHorizontalPeriod := by
    have hδx : δ ≤ x / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hδp : δ ≤ (D.commonHorizontalPeriod - x) / 2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    constructor <;> linarith [hySmall.1, hySmall.2]
  have hyBase : y ∈ D.base j := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hyabs : |y - x| < δ := (abs_lt).2 ⟨by linarith [hySmall.1], by
      linarith [hySmall.2]⟩
    exact hyabs.trans_le ((min_le_left _ _).trans (half_le_self hε.le))
  obtain ⟨i, hyGap⟩ := exists_elementaryGap_of_mem_Ioo_not_cut D hyCell hyCut
  refine ⟨i, ?_⟩
  have hsubInterior :
      Set.Ioo (slabElementaryLeft D i) (slabElementaryRight D i) ⊆
        interior (D.base j) :=
    Tiling.IsPreconnected.subset_interior_of_disjoint_frontier_of_mem
      isPreconnected_Ioo (slabElementary_disjoint_frontier D i j) hyGap hyBase
  exact ((Classical.choose_spec (slabElementary_has_uniqueBase D i)).2 j
    (hsubInterior.trans interior_subset)).symm

private noncomputable def slabColorGaps
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces) :
    Finset (Fin (slabElementaryIntervalCount D)) :=
  Finset.univ.filter fun i ↦ slabElementaryLabel D i = j

private theorem slabColorGaps_nonempty
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces) :
    (slabColorGaps D j).Nonempty := by
  obtain ⟨i, hi⟩ := slabBase_occurs_as_elementaryLabel D j
  exact ⟨i, by simp [slabColorGaps, hi]⟩

private noncomputable def slabColourIntervalCount
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces) : Nat :=
  (slabColorGaps D j).card

private theorem slabColourIntervalCount_pos
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces) :
    0 < slabColourIntervalCount D j := by
  exact Finset.card_pos.mpr (slabColorGaps_nonempty D j)

private noncomputable def slabColourGapIndex
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces)
    (ell : Fin (slabColourIntervalCount D j)) :
    Fin (slabElementaryIntervalCount D) :=
  ((slabColorGaps D j).equivFin.symm ell).1

private noncomputable def slabColourLeft
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces)
    (ell : Fin (slabColourIntervalCount D j)) : ℝ :=
  slabElementaryLeft D (slabColourGapIndex D j ell)

private noncomputable def slabColourRight
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces)
    (ell : Fin (slabColourIntervalCount D j)) : ℝ :=
  slabElementaryRight D (slabColourGapIndex D j ell)

private theorem slabColourGapIndex_label
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces)
    (ell : Fin (slabColourIntervalCount D j)) :
    slabElementaryLabel D (slabColourGapIndex D j ell) = j := by
  exact (Finset.mem_filter.mp ((slabColorGaps D j).equivFin.symm ell).2).2

private theorem slabElementary_intervals_ordered
    {K : Region} (D : SlabCertificate K)
    {a b : Fin (slabElementaryIntervalCount D)} (hab : a ≠ b) :
    slabElementaryRight D a ≤ slabElementaryLeft D b ∨
      slabElementaryRight D b ≤ slabElementaryLeft D a := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · left
    unfold slabElementaryRight slabElementaryLeft slabCutList
    apply (slabAllCellCuts D).pairwise_sort (· ≤ ·) |>.rel_get_of_le
    change (a : Nat) + 1 ≤ b
    omega
  · right
    unfold slabElementaryRight slabElementaryLeft slabCutList
    apply (slabAllCellCuts D).pairwise_sort (· ≤ ·) |>.rel_get_of_le
    change (b : Nat) + 1 ≤ a
    omega

private theorem slabColour_normalized
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces)
    (ell : Fin (slabColourIntervalCount D j)) :
    0 ≤ slabColourLeft D j ell ∧
      slabColourLeft D j ell < slabColourRight D j ell ∧
      slabColourRight D j ell ≤ D.commonHorizontalPeriod :=
  slabElementary_normalized D (slabColourGapIndex D j ell)

private theorem slabColour_interiors_disjoint
    {K : Region} (D : SlabCertificate K)
    (j : Fin D.numberOfPieces) (ell : Fin (slabColourIntervalCount D j))
    (j' : Fin D.numberOfPieces) (ell' : Fin (slabColourIntervalCount D j'))
    (hne : (Sigma.mk j ell : Sigma fun j ↦ Fin (slabColourIntervalCount D j)) ≠
      Sigma.mk j' ell') :
    slabColourRight D j ell ≤ slabColourLeft D j' ell' ∨
      slabColourRight D j' ell' ≤ slabColourLeft D j ell := by
  apply slabElementary_intervals_ordered D
  intro hindex
  have hj : j = j' := by
    rw [← slabColourGapIndex_label D j ell,
      ← slabColourGapIndex_label D j' ell', hindex]
  subst j'
  have hell : ell = ell' := by
    apply (slabColorGaps D j).equivFin.symm.injective
    exact Subtype.ext hindex
  subst ell'
  exact hne rfl

private noncomputable def slabElementaryColourIndex
    {K : Region} (D : SlabCertificate K)
    (i : Fin (slabElementaryIntervalCount D)) :
    Fin (slabColourIntervalCount D (slabElementaryLabel D i)) :=
  (slabColorGaps D (slabElementaryLabel D i)).equivFin
    ⟨i, by simp [slabColorGaps]⟩

private theorem slabElementaryColourIndex_gapIndex
    {K : Region} (D : SlabCertificate K)
    (i : Fin (slabElementaryIntervalCount D)) :
    slabColourGapIndex D (slabElementaryLabel D i)
      (slabElementaryColourIndex D i) = i := by
  unfold slabColourGapIndex slabElementaryColourIndex
  simp

private theorem elementaryGap_closedCover_of_not_cut
    {K : Region} (D : SlabCertificate K) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) D.commonHorizontalPeriod)
    (hxcut : x ∉ slabAllCellCuts D) :
    ∃ i : Fin (slabElementaryIntervalCount D),
      slabElementaryLeft D i ≤ x ∧ x ≤ slabElementaryRight D i := by
  obtain ⟨i, hi⟩ := exists_elementaryGap_of_mem_Ioo_not_cut D hx hxcut
  exact ⟨i, hi.1.le, hi.2.le⟩

private theorem elementaryGap_closedCover_of_cut
    {K : Region} (D : SlabCertificate K) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) D.commonHorizontalPeriod)
    (hxcut : x ∈ slabAllCellCuts D) :
    ∃ i : Fin (slabElementaryIntervalCount D),
      slabElementaryLeft D i ≤ x ∧ x ≤ slabElementaryRight D i := by
  have hxList : x ∈ slabCutList D := by
    rw [slabCutList, Finset.mem_sort]
    exact hxcut
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hxList
  have hzeroList : (0 : ℝ) ∈ slabCutList D := by
    rw [slabCutList, Finset.mem_sort]
    exact slabAllCellCuts_zero_mem D
  obtain ⟨k0, hk0⟩ := List.mem_iff_get.mp hzeroList
  have hpList : D.commonHorizontalPeriod ∈ slabCutList D := by
    rw [slabCutList, Finset.mem_sort]
    exact slabAllCellCuts_period_mem D
  obtain ⟨kp, hkp⟩ := List.mem_iff_get.mp hpList
  have hk0k : k0 < k := by
    apply ((slabAllCellCuts D).sortedLT_sort.lt_iff_lt).mp
    change (slabCutList D).get k0 < (slabCutList D).get k
    rw [hk0, hk]
    exact hx.1
  have hkkp : k < kp := by
    apply ((slabAllCellCuts D).sortedLT_sort.lt_iff_lt).mp
    change (slabCutList D).get k < (slabCutList D).get kp
    rw [hk, hkp]
    exact hx.2
  have hkpos : 0 < (k : Nat) := lt_of_le_of_lt (Nat.zero_le _) hk0k
  have hklt : (k : Nat) < (slabCutList D).length := k.isLt
  have hiCount : (k : Nat) - 1 < slabElementaryIntervalCount D := by
    have hlen := slabCutList_length D
    unfold slabElementaryIntervalCount
    omega
  let i : Fin (slabElementaryIntervalCount D) := ⟨k - 1, hiCount⟩
  refine ⟨i, ?_, ?_⟩
  · have hleftRight := slabElementaryLeft_lt_right D i
    have hrightEq : slabElementaryRight D i = x := by
      unfold slabElementaryRight
      rw [show (⟨i + 1, by
        rw [slabCutList_length]
        have hi := i.isLt
        unfold slabElementaryIntervalCount at hi
        have hc := slabAllCellCuts_card_two_le D
        omega⟩ : Fin (slabCutList D).length) = k by apply Fin.ext; dsimp [i]; omega, hk]
    linarith
  · unfold slabElementaryRight
    rw [show (⟨i + 1, by
      rw [slabCutList_length]
      have hi := i.isLt
      unfold slabElementaryIntervalCount at hi
      have hc := slabAllCellCuts_card_two_le D
      omega⟩ : Fin (slabCutList D).length) = k by apply Fin.ext; dsimp [i]; omega, hk]

private theorem slabElementary_closedCover
    {K : Region} (D : SlabCertificate K) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) D.commonHorizontalPeriod) :
    ∃ i : Fin (slabElementaryIntervalCount D),
      slabElementaryLeft D i ≤ x ∧ x ≤ slabElementaryRight D i := by
  by_cases hxcut : x ∈ slabAllCellCuts D
  · exact elementaryGap_closedCover_of_cut D hx hxcut
  · exact elementaryGap_closedCover_of_not_cut D hx hxcut

private theorem slabColour_period_closed_cover
    {K : Region} (D : SlabCertificate K) (x : ℝ) (hx0 : 0 < x)
    (hxp : x < D.commonHorizontalPeriod) :
    ∃ j ell, slabColourLeft D j ell ≤ x ∧ x ≤ slabColourRight D j ell := by
  obtain ⟨i, hi⟩ := slabElementary_closedCover D ⟨hx0, hxp⟩
  refine ⟨slabElementaryLabel D i, slabElementaryColourIndex D i, ?_⟩
  simpa [slabColourLeft, slabColourRight,
    slabElementaryColourIndex_gapIndex] using hi

private theorem slabBase_int_mul_period
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces) (q : ℤ) :
    ((q : ℝ) * D.commonHorizontalPeriod) +ᵥ D.base j = D.base j := by
  have hpGroup : D.commonHorizontalPeriod ∈ periodGroup (D.base j) :=
    (periodGroup_isAddSubgroup (D.base j) _).mpr (slabBase_commonHorizontalPeriod D j)
  simpa [zsmul_eq_mul] using
    (periodGroup_isAddSubgroup (D.base j) _).mp
      ((periodGroup (D.base j)).zsmul_mem hpGroup q)

private theorem slabBase_mem_add_int_mul_period
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces)
    (q : ℤ) (x : ℝ) :
    x + (q : ℝ) * D.commonHorizontalPeriod ∈ D.base j ↔ x ∈ D.base j := by
  have hp := slabBase_int_mul_period D j q
  constructor
  · intro hx
    rw [← hp, Set.mem_vadd_set_iff_neg_vadd_mem] at hx
    convert hx using 1
    all_goals simp only [vadd_eq_add]
    all_goals ring_nf
  · intro hx
    rw [← hp]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    convert hx using 1
    all_goals simp only [vadd_eq_add]
    all_goals ring_nf

private noncomputable def slabExceptionalCuts
    {K : Region} (D : SlabCertificate K) : Set ℝ :=
  ⋃ q : ℤ, (fun c : ℝ ↦ c + (q : ℝ) * D.commonHorizontalPeriod) ''
    (slabAllCellCuts D : Set ℝ)

private theorem slabExceptionalCuts_countable
    {K : Region} (D : SlabCertificate K) :
    (slabExceptionalCuts D).Countable := by
  apply Set.countable_iUnion
  intro q
  exact (slabAllCellCuts D).countable_toSet.image _

private theorem slabBase_pointwise_decode_off_exceptional
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces)
    {x : ℝ} (hxE : x ∉ slabExceptionalCuts D) :
    (x ∈ D.base j ↔
      x ∈ ⋃ q : Int, ⋃ ell : Fin (slabColourIntervalCount D j),
        Set.Ioo (slabColourLeft D j ell + q * D.commonHorizontalPeriod)
          (slabColourRight D j ell + q * D.commonHorizontalPeriod)) := by
  let q : ℤ := ⌊x / D.commonHorizontalPeriod⌋
  let y : ℝ := x - (q : ℝ) * D.commonHorizontalPeriod
  have hp := D.commonHorizontalPeriod_pos
  have hqlo : (q : ℝ) ≤ x / D.commonHorizontalPeriod := Int.floor_le _
  have hqhi : x / D.commonHorizontalPeriod < (q : ℝ) + 1 := Int.lt_floor_add_one _
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact sub_nonneg.mpr ((le_div_iff₀ hp).mp hqlo)
  have hyp : y < D.commonHorizontalPeriod := by
    dsimp [y]
    have := (div_lt_iff₀ hp).mp hqhi
    linarith
  have hyCut : y ∉ slabAllCellCuts D := by
    intro hy
    apply hxE
    rw [slabExceptionalCuts, Set.mem_iUnion]
    refine ⟨q, ?_⟩
    exact ⟨y, hy, by dsimp [y]; ring_nf⟩
  have hy0' : 0 < y := lt_of_le_of_ne hy0 fun h ↦
    hyCut (h ▸ slabAllCellCuts_zero_mem D)
  obtain ⟨i, hi⟩ := exists_elementaryGap_of_mem_Ioo_not_cut D
    ⟨hy0', hyp⟩ hyCut
  have hperiod : x ∈ D.base j ↔ y ∈ D.base j := by
    have h := slabBase_mem_add_int_mul_period D j q y
    convert h using 1
    all_goals dsimp [y]
    all_goals ring_nf
  constructor
  · intro hx
    have hyj : y ∈ D.base j := hperiod.mp hx
    have hlabel : slabElementaryLabel D i = j := by
      symm
      apply (Classical.choose_spec (slabElementary_has_uniqueBase D i)).2 j
      have hsub := Tiling.IsPreconnected.subset_interior_of_disjoint_frontier_of_mem
        isPreconnected_Ioo (slabElementary_disjoint_frontier D i j) hi hyj
      exact hsub.trans interior_subset
    subst j
    rw [Set.mem_iUnion]
    refine ⟨q, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨slabElementaryColourIndex D i, ?_⟩
    simp only [slabColourLeft, slabColourRight,
      slabElementaryColourIndex_gapIndex]
    dsimp [y] at hi
    constructor
    · linarith [hi.1]
    · linarith [hi.2]
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨r, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨ell, hx⟩ := hx
    have hgap :
        x - (r : ℝ) * D.commonHorizontalPeriod ∈
          Set.Ioo (slabColourLeft D j ell) (slabColourRight D j ell) := by
      constructor
      · linarith [hx.1]
      · linarith [hx.2]
    have hbase : x - (r : ℝ) * D.commonHorizontalPeriod ∈ D.base j := by
      unfold slabColourLeft slabColourRight at hgap
      rw [← slabColourGapIndex_label D j ell]
      exact slabElementary_subset_label D (slabColourGapIndex D j ell) hgap
    have h := slabBase_mem_add_int_mul_period D j r
      (x - (r : ℝ) * D.commonHorizontalPeriod)
    apply h.mpr at hbase
    convert hbase using 1
    all_goals ring_nf

private theorem slabColour_base_ae
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces) :
    D.base j =ᵐ[volume]
      ⋃ q : Int, ⋃ ell : Fin (slabColourIntervalCount D j),
        Set.Ioo (slabColourLeft D j ell + q * D.commonHorizontalPeriod)
          (slabColourRight D j ell + q * D.commonHorizontalPeriod) := by
  filter_upwards [(slabExceptionalCuts_countable D).ae_notMem volume]
    with x hx
  exact propext (slabBase_pointwise_decode_off_exceptional D j hx)

private theorem slab_bases_finiteIntervals :
    ∀ {K : Region} (D : SlabCertificate K),
      Nonempty (FiniteSlabBasePresentation D) := by
  intro K D
  exact ⟨{
    intervalCount := slabColourIntervalCount D
    intervalCount_pos := slabColourIntervalCount_pos D
    left := slabColourLeft D
    right := slabColourRight D
    normalized := slabColour_normalized D
    interiors_disjoint := slabColour_interiors_disjoint D
    period_closed_cover := slabColour_period_closed_cover D
    base_ae := slabColour_base_ae D }⟩


open Tiling.AxisParallel.Terminal.Executable
open Tiling.AxisParallel.Terminal.Executable.PositiveVerification

private def semanticOpenCellNL {C : RegionCode} (R : Realization C) (epsilon : Bool)
    (e : Fin C.cellCount) (centre point : Tiling.Plane) : Prop :=
  centre.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) < point.re ∧
  point.re < centre.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) ∧
  centre.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)) < point.im ∧
  point.im < centre.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.rightVertex e else C.topVertex e))

private theorem semanticOpenCellNL_isOpen {C : RegionCode} (R : Realization C)
    (epsilon : Bool) (e : Fin C.cellCount) (centre : Tiling.Plane) :
    IsOpen {p | semanticOpenCellNL R epsilon e centre p} := by
  unfold semanticOpenCellNL
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

private noncomputable def selectedRegionNL {C : RegionCode} (R : Realization C)
    (epsilon : Bool) : Region := if epsilon then R.region.coordinateSwap else R.region

@[simp] private theorem selectedCoordinate_false_horizontal (p : Tiling.Plane) :
    selectedCoordinate false .horizontal p = p.re := rfl
@[simp] private theorem selectedCoordinate_false_vertical (p : Tiling.Plane) :
    selectedCoordinate false .vertical p = p.im := rfl
@[simp] private theorem selectedCoordinate_true_horizontal (p : Tiling.Plane) :
    selectedCoordinate true .horizontal p = p.im := rfl
@[simp] private theorem selectedCoordinate_true_vertical (p : Tiling.Plane) :
    selectedCoordinate true .vertical p = p.re := rfl

private theorem selected_presentation_ae_falseNL : ∀ {C} (R : Realization C),
    (⋃ e, {p | semanticOpenCellNL R false e 0 p}) =ᵐ[volume] R.region.openCarrier := by
  intro C R
  simpa [semanticOpenCellNL] using R.presentation_correct

private noncomputable def coordinateSwapIsometry_local : Tiling.Plane ≃ₗᵢ[ℝ] Tiling.Plane where
  toLinearEquiv := Tiling.AxisParallel.coordinateSwap.toLinearEquiv
  norm_map' z := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring

private theorem coordinateSwap_image_eq_preimage_local (s : Set Tiling.Plane) :
    Tiling.AxisParallel.coordinateSwap '' s =
      Tiling.AxisParallel.coordinateSwap ⁻¹' s := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨Tiling.AxisParallel.coordinateSwap z, hz,
      Tiling.AxisParallel.coordinateSwap_apply_apply z⟩


private theorem semanticOpenCellNL_true_image_false_local {C} (R : Realization C)
    (e : Fin C.cellCount) :
    {p | semanticOpenCellNL R true e 0 p} =
      Tiling.AxisParallel.coordinateSwap ''
        {p | semanticOpenCellNL R false e 0 p} := by
  ext p
  constructor
  · intro hp
    refine ⟨Tiling.AxisParallel.coordinateSwap p, ?_,
      Tiling.AxisParallel.coordinateSwap_apply_apply p⟩
    change (0 : Tiling.Plane).re + selectedCoordinate false .horizontal
          (R.vertex (C.leftVertex e)) < (Tiling.AxisParallel.coordinateSwap p).re ∧
        (Tiling.AxisParallel.coordinateSwap p).re <
          (0 : Tiling.Plane).re + selectedCoordinate false .horizontal
            (R.vertex (C.rightVertex e)) ∧
        (0 : Tiling.Plane).im + selectedCoordinate false .vertical
            (R.vertex (C.bottomVertex e)) <
          (Tiling.AxisParallel.coordinateSwap p).im ∧
        (Tiling.AxisParallel.coordinateSwap p).im <
          (0 : Tiling.Plane).im + selectedCoordinate false .vertical
            (R.vertex (C.topVertex e))
    simpa [semanticOpenCellNL,
      Tiling.AxisParallel.Axis.coord, Tiling.AxisParallel.Axis.swap,
      and_assoc, and_left_comm, and_comm] using hp
  · rintro ⟨q, hq, rfl⟩
    change (0 : Tiling.Plane).re + selectedCoordinate true .horizontal
          (R.vertex (C.bottomVertex e)) < (Tiling.AxisParallel.coordinateSwap q).re ∧
        (Tiling.AxisParallel.coordinateSwap q).re <
          (0 : Tiling.Plane).re + selectedCoordinate true .horizontal
            (R.vertex (C.topVertex e)) ∧
        (0 : Tiling.Plane).im + selectedCoordinate true .vertical
            (R.vertex (C.leftVertex e)) <
          (Tiling.AxisParallel.coordinateSwap q).im ∧
        (Tiling.AxisParallel.coordinateSwap q).im <
          (0 : Tiling.Plane).im + selectedCoordinate true .vertical
            (R.vertex (C.rightVertex e))
    simpa [semanticOpenCellNL,
      Tiling.AxisParallel.Axis.coord, Tiling.AxisParallel.Axis.swap,
      and_assoc, and_left_comm, and_comm] using hq

private theorem selected_presentation_ae_local : ∀ {C} (R : Realization C) epsilon,
    (⋃ e, {p | semanticOpenCellNL R epsilon e 0 p}) =ᵐ[MeasureTheory.volume]
      (selectedRegionNL R epsilon).openCarrier := by
  intro C R epsilon
  cases epsilon with
  | false => simpa [selectedRegionNL] using selected_presentation_ae_falseNL R
  | true =>
      have hcells :
          (⋃ e, {p | semanticOpenCellNL R true e 0 p}) =
            Tiling.AxisParallel.coordinateSwap ''
              (⋃ e, {p | semanticOpenCellNL R false e 0 p}) := by
        rw [Set.image_iUnion]
        apply Set.iUnion_congr
        intro e
        exact semanticOpenCellNL_true_image_false_local R e
      have hfalse := selected_presentation_ae_falseNL R
      have hswap :=
        coordinateSwapIsometry_local.measurePreserving.quasiMeasurePreserving.ae hfalse
      have himage :
          Tiling.AxisParallel.coordinateSwap ''
              (⋃ e, {p | semanticOpenCellNL R false e 0 p}) =ᵐ[MeasureTheory.volume]
            Tiling.AxisParallel.coordinateSwap '' R.region.openCarrier := by
        rw [coordinateSwap_image_eq_preimage_local,
          coordinateSwap_image_eq_preimage_local]
        filter_upwards [hswap] with x hx
        change (⋃ e, {p | semanticOpenCellNL R false e 0 p})
            (Tiling.AxisParallel.coordinateSwap x) =
          R.region.openCarrier (Tiling.AxisParallel.coordinateSwap x) at hx
        exact hx
      rw [hcells]
      change Tiling.AxisParallel.coordinateSwap ''
          (⋃ e, {p | semanticOpenCellNL R false e 0 p}) =ᵐ[MeasureTheory.volume]
        (R.region.coordinateSwap).openCarrier
      apply himage.trans
      filter_upwards [] with x
      rw [Tiling.AxisParallel.coordinateSwap_openCarrier]

private theorem semanticOpenCellNL_vadd_local {C} (R : Realization C) (epsilon : Bool)
    (e : Fin C.cellCount) (centre : Tiling.Plane) :
    {p | semanticOpenCellNL R epsilon e centre p} =
      centre +ᵥ {p | semanticOpenCellNL R epsilon e 0 p} := by
  ext p
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simp only [Set.mem_ofPred_eq]
  simp [semanticOpenCellNL, selectedCoordinate,
    Tiling.AxisParallel.Axis.coord, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im]

private theorem semanticOpenCellNL_ae_selectedTile
    {C : RegionCode} (R : Realization C) (D : SlabCertificate R.region)
    (e : Fin C.cellCount) (centre : Tiling.Plane) :
    ∀ᵐ z ∂volume, z ∈ {p | semanticOpenCellNL R D.orientation e centre p} →
      z ∈ centre +ᵥ D.selectedRegion.openCarrier := by
  have hbase : ∀ᵐ z ∂volume,
      z ∈ {p | semanticOpenCellNL R D.orientation e 0 p} →
        z ∈ (selectedRegionNL R D.orientation).openCarrier := by
    filter_upwards [selected_presentation_ae_local R D.orientation] with z hz
    intro hze
    apply Eq.mp hz
    exact Set.mem_iUnion.mpr ⟨e, hze⟩
  let A : Set Tiling.Plane := {p | semanticOpenCellNL R D.orientation e 0 p}
  have hinter : (fun z => z ∈ A) =ᵐ[volume]
      (fun z => z ∈ A ∩ (selectedRegionNL R D.orientation).openCarrier) := by
    filter_upwards [hbase] with z hz
    apply propext
    constructor
    · intro h; exact ⟨h, hz h⟩
    · exact And.left
  have hshift := (MeasureTheory.vadd_set_ae_eq centre).mpr hinter
  filter_upwards [hshift] with z hz
  intro hzc
  have hzc' : z ∈ {p | semanticOpenCellNL R D.orientation e centre p} := hzc
  rw [semanticOpenCellNL_vadd_local] at hzc'
  have hzint : z ∈ centre +ᵥ
      (A ∩
        (selectedRegionNL R D.orientation).openCarrier) := Eq.mp hz hzc'
  obtain ⟨w, hw, rfl⟩ := Set.mem_vadd_set.mp hzint
  have hwRegion : w ∈ D.selectedRegion.openCarrier := by
    rw [D.selectedRegion_eq]
    exact hw.2
  exact ⟨w, hwRegion, rfl⟩

private def periodicOpenBase {K : Region} (D : SlabCertificate K)
    (base : FiniteSlabBasePresentation D) (j : Fin D.numberOfPieces) : Set ℝ :=
  ⋃ q : Int, ⋃ ell : Fin (base.intervalCount j),
    Set.Ioo (base.left j ell + q * D.commonHorizontalPeriod)
      (base.right j ell + q * D.commonHorizontalPeriod)

/-- The exact geometric payload supplied by one generated semantic open cell. -/
private structure GeneratedSlabOpenCell {K : Region} (D : SlabCertificate K)
    (j : Fin D.numberOfPieces) where
  centre : Tiling.Plane
  carrier : Set Tiling.Plane
  centre_mem : centre ∈ D.selectedPiece j
  carrier_open : IsOpen carrier
  carrier_nonempty : carrier.Nonempty
  carrier_ae_tile : ∀ᵐ z ∂volume, z ∈ carrier →
    z ∈ centre +ᵥ D.selectedRegion.openCarrier

private theorem closure_eq_of_open_aeEq_real {A B : Set ℝ}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : A =ᵐ[volume] B) :
    closure A = closure B := by
  have hsub {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
      (hUV : U =ᵐ[volume] V) : U ⊆ closure V := by
    intro x hx
    by_contra hxV
    let W := U ∩ (closure V)ᶜ
    have hWopen : IsOpen W := hU.inter isClosed_closure.isOpen_compl
    have hxW : x ∈ W := ⟨hx, hxV⟩
    have hWzero : volume W = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr (hUV.mono fun y hy hyW => by
        have hyV : y ∈ V := Eq.mp hy hyW.1
        exact hyW.2 (subset_closure hyV))
    exact hWopen.measure_ne_zero volume ⟨x, hxW⟩ hWzero
  exact Set.Subset.antisymm
    (closure_minimal (hsub hA hB hAB) isClosed_closure)
    (closure_minimal (hsub hB hA hAB.symm) isClosed_closure)

private theorem generatedSlabOpenCell_no_leakage
    {K : Region} (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (j : Fin D.numberOfPieces) (G : GeneratedSlabOpenCell D j)
    (houtside : ∀ z ∈ G.carrier, z.re ∉ closure (periodicOpenBase D base j)) : False := by
  have hperiodicOpen : IsOpen (periodicOpenBase D base j) := by
    apply isOpen_iUnion
    intro q
    apply isOpen_iUnion
    intro ell
    exact isOpen_Ioo
  have hclosure : closure (D.base j) = closure (periodicOpenBase D base j) :=
    closure_eq_of_open_aeEq_real (D.base_open j) hperiodicOpen (base.base_ae j)
  have hcarrierTarget : ∀ᵐ z ∂volume, z ∈ G.carrier → z.re ∈ D.base j := by
    filter_upwards [G.carrier_ae_tile, (D.piece_tiles j).2.2] with z hzCell hzTile
    intro hz
    exact hzTile.mpr ⟨⟨G.centre, G.centre_mem⟩, hzCell hz⟩
  have hcarrierNull : volume G.carrier = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hcarrierTarget] with z hzTarget
    intro hz
    have hzBase : z.re ∈ D.base j := hzTarget hz
    exact houtside z hz (hclosure ▸ subset_closure hzBase)
  exact G.carrier_open.measure_ne_zero volume G.carrier_nonempty hcarrierNull

/-- Exact generated-field bridge: a semantic open cell which is almost everywhere the translate
of its selected tile cannot contain a point outside the closed periodic base. -/
private theorem generatedSemanticCell_mem_closedPeriodicBase
    {K : Region} (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (j : Fin D.numberOfPieces) (centre p : Tiling.Plane)
    (hcentre : centre ∈ D.selectedPiece j) (cell : Set Tiling.Plane)
    (hcellOpen : IsOpen cell) (hp : p ∈ cell)
    (hcellAE : ∀ᵐ z ∂volume, z ∈ cell →
      z ∈ centre +ᵥ D.selectedRegion.openCarrier) :
    p.re ∈ closure (periodicOpenBase D base j) := by
  by_contra hout
  let carrier : Set Tiling.Plane :=
    cell ∩ Complex.re ⁻¹' (closure (periodicOpenBase D base j))ᶜ
  have hcarrierOpen : IsOpen carrier := hcellOpen.inter
    (isClosed_closure.isOpen_compl.preimage Complex.continuous_re)
  have hpCarrier : p ∈ carrier := ⟨hp, hout⟩
  let G : GeneratedSlabOpenCell D j :=
    { centre := centre
      carrier := carrier
      centre_mem := hcentre
      carrier_open := hcarrierOpen
      carrier_nonempty := ⟨p, hpCarrier⟩
      carrier_ae_tile := hcellAE.mono fun z hz hzc => hz hzc.1 }
  exact generatedSlabOpenCell_no_leakage D base j G (fun z hz => hz.2)

private theorem mem_closure_periodicOpenBase
    {K : Region} (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (j : Fin D.numberOfPieces) {x : ℝ}
    (hx : x ∈ closure (periodicOpenBase D base j)) :
    ∃ q : Int, ∃ ell : Fin (base.intervalCount j),
      base.left j ell + q * D.commonHorizontalPeriod ≤ x ∧
      x ≤ base.right j ell + q * D.commonHorizontalPeriod := by
  let F : Int → Set ℝ := fun q => Set.Icc
    (q * D.commonHorizontalPeriod) ((q + 1) * D.commonHorizontalPeriod)
  have hlocal : LocallyFinite F := by
    apply locallyFinite_Icc_of_tendsto
    · exact (tendsto_intCast_atTop_atTop.atTop_mul_const D.commonHorizontalPeriod_pos)
    · have ht := Filter.tendsto_id.atBot_zsmul_const D.commonHorizontalPeriod_pos
      rw [Filter.tendsto_atBot] at ht ⊢
      intro b
      filter_upwards [ht (b - D.commonHorizontalPeriod)] with q hq
      have hq' : (q : ℝ) * D.commonHorizontalPeriod ≤
          b - D.commonHorizontalPeriod := by simpa [zsmul_eq_mul] using hq
      simpa [zsmul_eq_mul, add_mul] using (show
        (q : ℝ) * D.commonHorizontalPeriod + D.commonHorizontalPeriod ≤ b by
          linarith)
  let G : Int → Set ℝ := fun q => ⋃ ell : Fin (base.intervalCount j),
    Set.Ioo (base.left j ell + q * D.commonHorizontalPeriod)
      (base.right j ell + q * D.commonHorizontalPeriod)
  have hGF : ∀ q, G q ⊆ F q := by
    intro q y hy
    simp only [G, Set.mem_iUnion] at hy
    obtain ⟨ell, hyl, hyr⟩ := hy
    dsimp [F]
    rcases base.normalized j ell with ⟨hl, _, hr⟩
    constructor <;> nlinarith
  have hGlocal : LocallyFinite G := hlocal.subset hGF
  have hperiodic : periodicOpenBase D base j = ⋃ q, G q := by
    simp [periodicOpenBase, G]
  rw [hperiodic, hGlocal.closure_iUnion] at hx
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
  have hfinite : IsClosed (⋃ ell : Fin (base.intervalCount j),
      Set.Icc (base.left j ell + q * D.commonHorizontalPeriod)
        (base.right j ell + q * D.commonHorizontalPeriod)) :=
    isClosed_iUnion_of_finite fun ell => isClosed_Icc
  have hopenSub : G q ⊆
      ⋃ ell : Fin (base.intervalCount j),
        Set.Icc (base.left j ell + q * D.commonHorizontalPeriod)
          (base.right j ell + q * D.commonHorizontalPeriod) := by
    intro y hy
    obtain ⟨ell, hyl, hyr⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨ell, le_of_lt hyl, le_of_lt hyr⟩
  have := closure_minimal hopenSub hfinite hxq
  obtain ⟨ell, hell⟩ := Set.mem_iUnion.mp this
  exact ⟨q, ell, hell⟩

private theorem checkingBox_mem_closedPeriodicBase
    {K : Region} (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (j : Fin D.numberOfPieces) {x : ℝ} (hx0 : 0 < x)
    (hxβ : x < D.commonHorizontalPeriod)
    (hx : x ∈ closure (periodicOpenBase D base j)) :
    ∃ ell q, q ∈ ([-1, 0, 1] : List Int) ∧
      base.left j ell + q * D.commonHorizontalPeriod ≤ x ∧
      x ≤ base.right j ell + q * D.commonHorizontalPeriod := by
  obtain ⟨q, ell, hleft, hright⟩ := mem_closure_periodicOpenBase D base j hx
  rcases base.normalized j ell with ⟨hl, _, hr⟩
  have hqle : q ≤ 0 := by
    by_contra hn
    have hq : (1 : Int) ≤ q := by omega
    have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith [D.commonHorizontalPeriod_pos]
  have hqge : 0 ≤ q := by
    by_contra hn
    have hq : q ≤ (-1 : Int) := by omega
    have hq' : (q : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hq
    nlinarith [D.commonHorizontalPeriod_pos]
  have hq : q = 0 := by omega
  subst q
  exact ⟨ell, 0, by simp, by simpa using hleft, by simpa using hright⟩

private theorem semanticCell_noLeakage
    {C : RegionCode} (R : Realization C) (D : SlabCertificate R.region)
    (base : FiniteSlabBasePresentation D) (j : Fin D.numberOfPieces)
    (centre : Tiling.Plane) (hcentre : centre ∈ D.selectedPiece j)
    (e : Fin C.cellCount) (p : Tiling.Plane)
    (hp : semanticOpenCellNL R D.orientation e centre p)
    (hp0 : 0 < p.re) (hpβ : p.re < D.commonHorizontalPeriod) :
    ∃ ell q, q ∈ ([-1, 0, 1] : List Int) ∧
      base.left j ell + q * D.commonHorizontalPeriod ≤ p.re ∧
      p.re ≤ base.right j ell + q * D.commonHorizontalPeriod := by
  let cell : Set Tiling.Plane :=
    {z | semanticOpenCellNL R D.orientation e centre z}
  have hcellOpen : IsOpen cell := by
    unfold cell semanticOpenCellNL
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hpclosure := generatedSemanticCell_mem_closedPeriodicBase D base j centre p
    hcentre cell hcellOpen hp (semanticOpenCellNL_ae_selectedTile R D e centre)
  exact checkingBox_mem_closedPeriodicBase D base j hp0 hpβ hpclosure

private theorem selectedPiece_centres_eq_of_tileIntersection_measure_ne_zero
    {K : Region} (D : SlabCertificate K) (j : Fin D.numberOfPieces)
    {c c' : Tiling.Plane} (hc : c ∈ D.selectedPiece j)
    (hc' : c' ∈ D.selectedPiece j)
    (hvol : volume ((c +ᵥ D.selectedRegion.openCarrier) ∩
      (c' +ᵥ D.selectedRegion.openCarrier)) ≠ 0) : c = c' := by
  by_contra hne
  have hd := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
    D.selectedRegion (D.selectedPiece j)).mp (D.piece_tiles j).2.1 hc hc' hne
  obtain ⟨z, hz⟩ := MeasureTheory.nonempty_of_measure_ne_zero hvol
  exact Set.disjoint_left.1 hd hz.1 hz.2

private def semanticCellsNonoverlapNL {C : RegionCode} (R : Realization C)
    (epsilon : Bool) (e e' : Fin C.cellCount) (c c' : Tiling.Plane) : Prop :=
  c.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) ≤
    c'.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.bottomVertex e' else C.leftVertex e')) ∨
  c'.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.topVertex e' else C.rightVertex e')) ≤
    c.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) ∨
  c.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.rightVertex e else C.topVertex e)) ≤
    c'.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.leftVertex e' else C.bottomVertex e')) ∨
  c'.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.rightVertex e' else C.topVertex e')) ≤
    c.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e))

private theorem semanticCellsNonoverlapNL_of_packing
    {C : RegionCode} (R : Realization C) (D : SlabCertificate R.region)
    (j : Fin D.numberOfPieces) {c c' : Tiling.Plane}
    (hc : c ∈ D.selectedPiece j) (hc' : c' ∈ D.selectedPiece j) :
    c = c' ∨ ∀ e e', semanticCellsNonoverlapNL R D.orientation e e' c c' := by
  by_cases hcc : c = c'
  · exact Or.inl hcc
  right
  intro e e'
  by_contra hno
  simp only [semanticCellsNonoverlapNL, not_or, not_le] at hno
  let loX : Fin C.cellCount → ℝ := fun f => selectedCoordinate D.orientation .horizontal
    (R.vertex (if D.orientation then C.bottomVertex f else C.leftVertex f))
  let hiX : Fin C.cellCount → ℝ := fun f => selectedCoordinate D.orientation .horizontal
    (R.vertex (if D.orientation then C.topVertex f else C.rightVertex f))
  let loY : Fin C.cellCount → ℝ := fun f => selectedCoordinate D.orientation .vertical
    (R.vertex (if D.orientation then C.leftVertex f else C.bottomVertex f))
  let hiY : Fin C.cellCount → ℝ := fun f => selectedCoordinate D.orientation .vertical
    (R.vertex (if D.orientation then C.rightVertex f else C.topVertex f))
  have hxpos (f) : loX f < hiX f := by
    cases h : D.orientation
    · simpa [loX, hiX, h] using R.left_lt_right f
    · simpa [loX, hiX, h] using R.bottom_lt_top f
  have hypos (f) : loY f < hiY f := by
    cases h : D.orientation
    · simpa [loY, hiY, h] using R.bottom_lt_top f
    · simpa [loY, hiY, h] using R.left_lt_right f
  let z : Tiling.Plane := Complex.mk
    ((max (c.re + loX e) (c'.re + loX e') +
      min (c.re + hiX e) (c'.re + hiX e')) / 2)
    ((max (c.im + loY e) (c'.im + loY e') +
      min (c.im + hiY e) (c'.im + hiY e')) / 2)
  have hxgap : max (c.re + loX e) (c'.re + loX e') <
      min (c.re + hiX e) (c'.re + hiX e') := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith [hxpos e], hno.2.1⟩,
      ⟨hno.1, by linarith [hxpos e']⟩⟩
  have hygap : max (c.im + loY e) (c'.im + loY e') <
      min (c.im + hiY e) (c'.im + hiY e') := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith [hypos e], hno.2.2.2⟩,
      ⟨hno.2.2.1, by linarith [hypos e']⟩⟩
  have hxmidlo : max (c.re + loX e) (c'.re + loX e') < z.re := by
    dsimp [z]; linarith
  have hxmidhi : z.re < min (c.re + hiX e) (c'.re + hiX e') := by
    dsimp [z]; linarith
  have hymidlo : max (c.im + loY e) (c'.im + loY e') < z.im := by
    dsimp [z]; linarith
  have hymidhi : z.im < min (c.im + hiY e) (c'.im + hiY e') := by
    dsimp [z]; linarith
  let U : Set Tiling.Plane :=
    {p | semanticOpenCellNL R D.orientation e c p} ∩
      {p | semanticOpenCellNL R D.orientation e' c' p}
  have hUopen : IsOpen U := by
    exact (semanticOpenCellNL_isOpen R D.orientation e c).inter
      (semanticOpenCellNL_isOpen R D.orientation e' c')
  have hzU : z ∈ U := by
    change semanticOpenCellNL R D.orientation e c z ∧
      semanticOpenCellNL R D.orientation e' c' z
    change (c.re + loX e < z.re ∧ z.re < c.re + hiX e ∧
      c.im + loY e < z.im ∧ z.im < c.im + hiY e) ∧
      (c'.re + loX e' < z.re ∧ z.re < c'.re + hiX e' ∧
      c'.im + loY e' < z.im ∧ z.im < c'.im + hiY e')
    constructor
    · exact ⟨(le_max_left _ _).trans_lt hxmidlo,
        hxmidhi.trans_le (min_le_left _ _),
        (le_max_left _ _).trans_lt hymidlo,
        hymidhi.trans_le (min_le_left _ _)⟩
    · exact ⟨(le_max_right _ _).trans_lt hxmidlo,
        hxmidhi.trans_le (min_le_right _ _),
        (le_max_right _ _).trans_lt hymidlo,
        hymidhi.trans_le (min_le_right _ _)⟩
  have hUA : ∀ᵐ w ∂volume, w ∈ U → w ∈ c +ᵥ D.selectedRegion.openCarrier := by
    filter_upwards [semanticOpenCellNL_ae_selectedTile R D e c] with w hw
    exact fun h => hw h.1
  have hUB : ∀ᵐ w ∂volume, w ∈ U → w ∈ c' +ᵥ D.selectedRegion.openCarrier := by
    filter_upwards [semanticOpenCellNL_ae_selectedTile R D e' c'] with w hw
    exact fun h => hw h.2
  have hvol : volume ((c +ᵥ D.selectedRegion.openCarrier) ∩
      (c' +ᵥ D.selectedRegion.openCarrier)) ≠ 0 := by
    intro hzero
    have hUnull : volume U = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      have hnot := measure_eq_zero_iff_ae_notMem.mp hzero
      filter_upwards [hUA, hUB, hnot] with w hwA hwB hnotw
      intro hw
      exact hnotw ⟨hwA hw, hwB hw⟩
    exact hUopen.measure_ne_zero volume ⟨z, hzU⟩ hUnull
  exact hcc (selectedPiece_centres_eq_of_tileIntersection_measure_ne_zero
    D j hc hc' hvol)


open Tiling.AxisParallel.Terminal.Executable
open Tiling.AxisParallel.Terminal.Executable.PositiveVerification

private def triangularPieceCount (c : RawTriangularCode) : Nat := c.pieces.length

private def triangularPiece (c : RawTriangularCode)
    (j : Fin (triangularPieceCount c)) : RawTriangularPieceCode := c.pieces.get j

private def triangularCenteredInteger {radius : Nat}
    (i : Fin (2 * radius + 1)) : Int :=
  Int.ofNat i.val - Int.ofNat radius

private abbrev TriangularFirstIndexProbe (c : RawTriangularCode) :=
  Fin (2 * (c.checkingRadius + 1) + 1)

private abbrev TriangularSecondIndexProbe (c : RawTriangularCode) :=
  Fin (2 * (2 * c.checkingRadius + 3) + 1)

private abbrev TriangularFiniteIndexProbe
    (c : RawTriangularCode) (j : Fin (triangularPieceCount c)) :=
  Fin (triangularPiece c j).representativeCount ×
    TriangularFirstIndexProbe c × TriangularSecondIndexProbe c

private def triangularFiniteIndicesProbe
    (c : RawTriangularCode) (j : Fin (triangularPieceCount c)) :
    List (TriangularFiniteIndexProbe c j) :=
  (List.ofFn fun r : Fin (triangularPiece c j).representativeCount => r).flatMap fun r =>
    (List.ofFn fun n : TriangularFirstIndexProbe c => n).flatMap fun n =>
      List.ofFn fun k : TriangularSecondIndexProbe c => (r, n, k)

private theorem triangularCenteredInteger_complete (radius : Nat) (n : Int)
    (hn : n.natAbs ≤ radius) :
    ∃ i : Fin (2 * radius + 1), triangularCenteredInteger i = n := by
  by_cases hnonneg : 0 ≤ n
  · have hi : n.natAbs + radius < 2 * radius + 1 := by omega
    refine ⟨⟨n.natAbs + radius, hi⟩, ?_⟩
    change Int.ofNat (n.natAbs + radius) - Int.ofNat radius = n
    have hadd : Int.ofNat (n.natAbs + radius) =
        Int.ofNat n.natAbs + Int.ofNat radius := Int.natCast_add _ _
    rw [hadd]
    have hnat : Int.ofNat n.natAbs = n := Int.natAbs_of_nonneg hnonneg
    rw [hnat]
    omega
  · have hneg : n < 0 := Int.lt_of_not_ge hnonneg
    have hi : radius - n.natAbs < 2 * radius + 1 := by omega
    refine ⟨⟨radius - n.natAbs, hi⟩, ?_⟩
    change Int.ofNat (radius - n.natAbs) - Int.ofNat radius = n
    have hsub : Int.ofNat (radius - n.natAbs) =
        Int.ofNat radius - Int.ofNat n.natAbs := Int.ofNat_sub hn
    rw [hsub]
    have hnat : Int.ofNat n.natAbs = -n :=
      Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
    rw [hnat]
    omega

private theorem triangular_index_enumeration_complete
    (code : RawTriangularCode) (j : Fin (triangularPieceCount code))
    (r : Fin (triangularPiece code j).representativeCount) (n k : Int)
    (hn : n.natAbs ≤ code.checkingRadius + 1)
    (hk : k.natAbs ≤ 2 * code.checkingRadius + 3) :
    ∃ i ∈ triangularFiniteIndicesProbe code j,
      i.1 = r ∧ triangularCenteredInteger i.2.1 = n ∧
        triangularCenteredInteger i.2.2 = k := by
  obtain ⟨nidx, hnidx⟩ :=
    triangularCenteredInteger_complete (code.checkingRadius + 1) n hn
  obtain ⟨kidx, hkidx⟩ :=
    triangularCenteredInteger_complete (2 * code.checkingRadius + 3) k hk
  refine ⟨(r, nidx, kidx), ?_, rfl, hnidx, hkidx⟩
  simp only [triangularFiniteIndicesProbe]
  apply List.mem_flatMap.mpr
  refine ⟨r, List.mem_ofFn.mpr ⟨r, rfl⟩, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨nidx, List.mem_ofFn.mpr ⟨nidx, rfl⟩, ?_⟩
  exact List.mem_ofFn.mpr ⟨kidx, rfl⟩

private theorem triangular_firstIndex_bound
    (rad : Nat) (beta x cx : Real) (n : Int)
    (hbeta : 0 < beta) (hx0 : 0 ≤ x) (hx1 : x < beta)
    (hcx0 : -(rad : Real) * beta < cx)
    (hcx1 : cx < ((rad : Real) + 1) * beta)
    (hcentre : cx = x + (n : Real) * beta) :
    n.natAbs ≤ rad + 1 := by
  have hnupper : n < (rad + 1 : Nat) := by
    by_contra hnot
    have hge : (rad + 1 : Int) ≤ n := by omega
    have hgeR : ((rad + 1 : Int) : Real) ≤ (n : Real) := by exact_mod_cast hge
    norm_num at hgeR
    have hmul := mul_le_mul_of_nonneg_right hgeR hbeta.le
    rw [hcentre] at hcx1
    nlinarith
  have hnlower : (-(rad + 1 : Nat) : Int) < n := by
    by_contra hnot
    have hle : n ≤ (-(rad + 1 : Nat) : Int) := by omega
    have hleR : (n : Real) ≤ (-(rad + 1 : Nat) : Int) := by exact_mod_cast hle
    norm_num at hleR
    have hmul := mul_le_mul_of_nonneg_right hleR hbeta.le
    rw [hcentre] at hcx0
    nlinarith
  omega

private theorem triangular_shear_bounds
    (rad : Nat) (alpha shear : Real) (n : Int)
    (halpha : 0 < alpha) (hs0 : 0 ≤ shear) (hs1 : shear < alpha)
    (hn0 : (-(rad + 1 : Nat) : Int) ≤ n)
    (hn1 : n ≤ (rad + 1 : Int)) :
    -((rad : Real) + 1) * alpha ≤ (n : Real) * shear ∧
      (n : Real) * shear ≤ ((rad : Real) + 1) * alpha := by
  have hn0R : (-(rad + 1 : Nat) : Real) ≤ (n : Real) := by exact_mod_cast hn0
  have hn1R : (n : Real) ≤ (rad + 1 : Nat) := by exact_mod_cast hn1
  norm_num [Nat.cast_add] at hn0R hn1R ⊢
  constructor
  · by_cases hn : 0 ≤ n
    · have hnR : 0 ≤ (n : Real) := by exact_mod_cast hn
      nlinarith [mul_nonneg hnR hs0]
    · have hnR : (n : Real) ≤ 0 := by exact_mod_cast (Int.le_of_lt (Int.lt_of_not_ge hn))
      have hmul := mul_le_mul_of_nonneg_right hn0R hs0
      have hshear := mul_le_mul_of_nonneg_left hs1.le (by positivity : 0 ≤ (rad : Real) + 1)
      nlinarith
  · by_cases hn : 0 ≤ n
    · have hnR : 0 ≤ (n : Real) := by exact_mod_cast hn
      have hmul := mul_le_mul_of_nonneg_right hn1R halpha.le
      have hshear := mul_le_mul_of_nonneg_left hs1.le hnR
      nlinarith
    · have hnR : (n : Real) ≤ 0 := by exact_mod_cast (Int.le_of_lt (Int.lt_of_not_ge hn))
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hnR hs0]

private theorem triangular_secondIndex_bound
    (rad : Nat) (alpha y shearTerm cy : Real) (k : Int)
    (halpha : 0 < alpha) (hy0 : 0 ≤ y) (hy1 : y < alpha)
    (hs0 : -((rad : Real) + 1) * alpha ≤ shearTerm)
    (hs1 : shearTerm ≤ ((rad : Real) + 1) * alpha)
    (hcy0 : -(rad : Real) * alpha < cy)
    (hcy1 : cy < ((rad : Real) + 1) * alpha)
    (hcentre : cy = y + shearTerm + (k : Real) * alpha) :
    k.natAbs ≤ 2 * rad + 3 := by
  have hkupper : k < (2 * rad + 3 : Nat) := by
    by_contra hnot
    have hge : (2 * rad + 3 : Int) ≤ k := by omega
    have hgeR : ((2 * rad + 3 : Int) : Real) ≤ (k : Real) := by
      exact_mod_cast hge
    norm_num [Nat.cast_add, Nat.cast_mul] at hgeR hs0 hcy1 ⊢
    have hmul := mul_le_mul_of_nonneg_right hgeR halpha.le
    rw [hcentre] at hcy1
    nlinarith
  have hklower : (-(2 * rad + 3 : Nat) : Int) < k := by
    by_contra hnot
    have hle : k ≤ (-(2 * rad + 3 : Nat) : Int) := by omega
    have hleR : (k : Real) ≤ (-(2 * rad + 3 : Nat) : Int) := by
      exact_mod_cast hle
    norm_num [Nat.cast_add, Nat.cast_mul] at hleR hs1 hcy0 ⊢
    have hmul := mul_le_mul_of_nonneg_right hleR halpha.le
    rw [hcentre] at hcy0
    nlinarith
  omega

private theorem triangular_neighbour_bounds_from_expanded_geometry
    (rad : Nat) (alpha beta shear x y cx cy : Real) (n k : Int)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hshear : 0 ≤ shear ∧ shear < alpha)
    (hx : 0 ≤ x ∧ x < beta) (hy : 0 ≤ y ∧ y < alpha)
    (hcx0 : -(rad : Real) * beta < cx)
    (hcx1 : cx < ((rad : Real) + 1) * beta)
    (hcy0 : -(rad : Real) * alpha < cy)
    (hcy1 : cy < ((rad : Real) + 1) * alpha)
    (hcx : cx = x + (n : Real) * beta)
    (hcy : cy = y + (n : Real) * shear + (k : Real) * alpha) :
    n.natAbs ≤ rad + 1 ∧ k.natAbs ≤ 2 * rad + 3 := by
  have hn := triangular_firstIndex_bound rad beta x cx n hbeta hx.1 hx.2
    hcx0 hcx1 hcx
  have hn0 : (-(rad + 1 : Nat) : Int) ≤ n := by omega
  have hn1 : n ≤ (rad + 1 : Int) := by omega
  have hns := triangular_shear_bounds rad alpha shear n halpha
    hshear.1 hshear.2 hn0 hn1
  refine ⟨hn, ?_⟩
  exact triangular_secondIndex_bound rad alpha y ((n : Real) * shear) cy k
    halpha hy.1 hy.2 hns.1 hns.2 hcy0 hcy1 hcy

private theorem triangular_exists_mem_open_of_ae
    {U : Set Tiling.Plane} {P : Tiling.Plane → Prop}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hP : ∀ᵐ x ∂MeasureTheory.volume, P x) : ∃ x ∈ U, P x := by
  have hmu : MeasureTheory.volume.restrict U ≠ 0 := by
    intro hz
    have hzero : MeasureTheory.volume U = 0 := by
      rw [← MeasureTheory.Measure.restrict_apply_univ U, hz]
      simp
    exact (hUopen.measure_pos MeasureTheory.volume hUne).ne' hzero
  let hne : (MeasureTheory.ae (MeasureTheory.volume.restrict U)).NeBot :=
    MeasureTheory.ae_neBot.mpr hmu
  have hP' : ∀ᵐ x ∂MeasureTheory.volume.restrict U, P x :=
    hP.filter_mono MeasureTheory.ae_restrict_le
  rcases @Filter.Eventually.exists Tiling.Plane _
      (MeasureTheory.ae (MeasureTheory.volume.restrict U)) hne
      (hP'.and (MeasureTheory.ae_restrict_mem hUopen.measurableSet)) with
    ⟨x, hxP, hxU⟩
  exact ⟨x, hxU, hxP⟩

private theorem triangular_open_complement_select
    {checked box : Set Tiling.Plane} {p : Tiling.Plane}
    {P : Tiling.Plane → Prop}
    (hchecked : IsClosed checked) (hbox : IsOpen box)
    (hpbox : p ∈ box) (hpchecked : p ∉ checked)
    (hP : ∀ᵐ x ∂MeasureTheory.volume, P x) :
    ∃ q, q ∈ box ∧ q ∉ checked ∧ P q := by
  let U := box ∩ checkedᶜ
  have hUopen : IsOpen U := hbox.inter hchecked.isOpen_compl
  have hpU : p ∈ U := ⟨hpbox, hpchecked⟩
  obtain ⟨q, hq, hqP⟩ :=
    triangular_exists_mem_open_of_ae hUopen ⟨p, hpU⟩ hP
  exact ⟨q, hq.1, hq.2, hqP⟩

private def triangularSemanticCentreProbe (code : RawTriangularCode)
    (X : TriangularRawParameters code) (j : Fin (triangularPieceCount code))
    (r : Fin (triangularPiece code j).representativeCount) (n k : Int) :
    Tiling.Plane :=
  (X.representativeX ⟨j, r⟩ + n * X.beta) +
    (X.representativeY ⟨j, r⟩ + n * X.shear j + k * X.alpha) * Complex.I

private def triangularClosedCellProbe {C : RegionCode} (R : Realization C)
    (epsilon : Bool) (e : Fin C.cellCount) (centre : Tiling.Plane) :
    Set Tiling.Plane :=
  {p | centre.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) ≤ p.re ∧
    p.re ≤ centre.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) ∧
    centre.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)) ≤ p.im ∧
    p.im ≤ centre.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.rightVertex e else C.topVertex e))}

private theorem triangularClosedCellProbe_isClosed {C : RegionCode}
    (R : Realization C) (epsilon : Bool) (e : Fin C.cellCount)
    (centre : Tiling.Plane) :
    IsClosed (triangularClosedCellProbe R epsilon e centre) := by
  unfold triangularClosedCellProbe
  apply IsClosed.inter
  · change IsClosed (Complex.re ⁻¹' Set.Ici _)
    exact isClosed_Ici.preimage Complex.continuous_re
  · apply IsClosed.inter
    · change IsClosed (Complex.re ⁻¹' Set.Iic _)
      exact isClosed_Iic.preimage Complex.continuous_re
    · apply IsClosed.inter
      · change IsClosed (Complex.im ⁻¹' Set.Ici _)
        exact isClosed_Ici.preimage Complex.continuous_im
      · change IsClosed (Complex.im ⁻¹' Set.Iic _)
        exact isClosed_Iic.preimage Complex.continuous_im

private def triangularCheckedProbe {C : RegionCode} (R : Realization C)
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code)) : Set Tiling.Plane :=
  ⋃ i : {i // i ∈ triangularFiniteIndicesProbe code j},
    ⋃ e : Fin C.cellCount,
      triangularClosedCellProbe R code.orientation e
        (triangularSemanticCentreProbe code X j i.1.1
          (triangularCenteredInteger i.1.2.1)
          (triangularCenteredInteger i.1.2.2))

private theorem triangularCheckedProbe_isClosed {C : RegionCode}
    (R : Realization C) (code : RawTriangularCode)
    (X : TriangularRawParameters code) (j : Fin (triangularPieceCount code)) :
    IsClosed (triangularCheckedProbe R code X j) := by
  unfold triangularCheckedProbe
  apply isClosed_iUnion_of_finite
  intro i
  apply isClosed_iUnion_of_finite
  intro e
  exact triangularClosedCellProbe_isClosed R code.orientation e _

private theorem triangular_allCentres_presentation_ae
    (S cells carrier : Set Tiling.Plane) (hS : S.Countable)
    (hpresentation : cells =ᵐ[MeasureTheory.volume] carrier) :
    ∀ᵐ p ∂MeasureTheory.volume, ∀ s : S,
      (p ∈ (s.1 +ᵥ cells) ↔ p ∈ (s.1 +ᵥ carrier)) := by
  let _ : Countable S := hS.to_subtype
  rw [eventually_countable_forall]
  intro s
  exact ((MeasureTheory.vadd_set_ae_eq s.1).mpr hpresentation).mem_iff

private theorem triangular_cover_and_presentation_select
    {U S cells carrier : Set Tiling.Plane}
    (hU : IsOpen U) (hUne : U.Nonempty) (hS : S.Countable)
    (hcover : ∀ᵐ p ∂MeasureTheory.volume,
      p ∈ Set.univ ↔ ∃ s : S, p ∈ s.1 +ᵥ carrier)
    (hpresentation : cells =ᵐ[MeasureTheory.volume] carrier) :
    ∃ p ∈ U, (∃ s : S, p ∈ s.1 +ᵥ carrier) ∧
      ∀ s : S, (p ∈ s.1 +ᵥ cells ↔ p ∈ s.1 +ᵥ carrier) := by
  have hall := triangular_allCentres_presentation_ae S cells carrier hS hpresentation
  obtain ⟨p, hpU, hpcover, hpall⟩ :=
    triangular_exists_mem_open_of_ae hU hUne (hcover.and hall)
  exact ⟨p, hpU, (hpcover.mp (Set.mem_univ p)), hpall⟩

private theorem triangular_orbit_member_indices {K : Tiling.AxisParallel.Region}
    (D : SlabCertificate K) (orbit : FiniteSlabOrbitPresentation D)
    (j : Fin D.numberOfPieces) {s : Tiling.Plane} (hs : s ∈ D.selectedPiece j) :
    ∃ (r : Fin (orbit.representativeCount j)) (n k : Int),
      s = orbit.representative j r +
      n • skewPeriodVector D.commonHorizontalPeriod (D.normalizedShear j) +
      k • verticalPeriodVector D.commonVerticalPeriod := by
  exact (Set.ext_iff.mp (orbit.presents j) s).mp hs

private theorem triangularSemanticCentreProbe_eq_orbit
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    {K : Tiling.AxisParallel.Region} (D : SlabCertificate K)
    (orbit : FiniteSlabOrbitPresentation D)
    (j : Fin (triangularPieceCount code))
    (jD : Fin D.numberOfPieces)
    (r : Fin (triangularPiece code j).representativeCount)
    (rD : Fin (orbit.representativeCount jD)) (n k : Int)
    (hbeta : X.beta = D.commonHorizontalPeriod)
    (halpha : X.alpha = D.commonVerticalPeriod)
    (hshear : X.shear j = D.normalizedShear jD)
    (hrepX : X.representativeX ⟨j, r⟩ = (orbit.representative jD rD).re)
    (hrepY : X.representativeY ⟨j, r⟩ = (orbit.representative jD rD).im) :
    triangularSemanticCentreProbe code X j r n k =
      orbit.representative jD rD +
        n • skewPeriodVector D.commonHorizontalPeriod (D.normalizedShear jD) +
        k • verticalPeriodVector D.commonVerticalPeriod := by
  apply Complex.ext <;>
    simp [triangularSemanticCentreProbe, skewPeriodVector, verticalPeriodVector,
      hbeta, halpha, hshear, hrepX, hrepY]

private theorem triangularCheckedProbe_mem_of_openCell
    {C : RegionCode} (R : Realization C) (code : RawTriangularCode)
    (X : TriangularRawParameters code) (j : Fin (triangularPieceCount code))
    (i : TriangularFiniteIndexProbe code j)
    (hi : i ∈ triangularFiniteIndicesProbe code j) (e : Fin C.cellCount)
    (p : Tiling.Plane)
    (hopen :
      let c := triangularSemanticCentreProbe code X j i.1
        (triangularCenteredInteger i.2.1) (triangularCenteredInteger i.2.2)
      c.re + selectedCoordinate code.orientation .horizontal
          (R.vertex (if code.orientation then C.bottomVertex e else C.leftVertex e)) < p.re ∧
      p.re < c.re + selectedCoordinate code.orientation .horizontal
          (R.vertex (if code.orientation then C.topVertex e else C.rightVertex e)) ∧
      c.im + selectedCoordinate code.orientation .vertical
          (R.vertex (if code.orientation then C.leftVertex e else C.bottomVertex e)) < p.im ∧
      p.im < c.im + selectedCoordinate code.orientation .vertical
          (R.vertex (if code.orientation then C.rightVertex e else C.topVertex e))) :
    p ∈ triangularCheckedProbe R code X j := by
  apply Set.mem_iUnion.mpr
  refine ⟨⟨i, hi⟩, Set.mem_iUnion.mpr ⟨e, ?_⟩⟩
  change _ ≤ p.re ∧ p.re ≤ _ ∧ _ ≤ p.im ∧ p.im ≤ _
  exact ⟨hopen.1.le, hopen.2.1.le, hopen.2.2.1.le, hopen.2.2.2.le⟩

private theorem triangular_centre_bounds_of_openCell
    (rad : Nat) (alpha beta cx cy px py left right bottom top : Real)
    (hp : 0 < px ∧ px < beta ∧ 0 < py ∧ py < alpha)
    (hcell : cx + left < px ∧ px < cx + right ∧
      cy + bottom < py ∧ py < cy + top)
    (hleft : |left| < (rad : Real) * beta)
    (hright : |right| < (rad : Real) * beta)
    (hbottom : |bottom| < (rad : Real) * alpha)
    (htop : |top| < (rad : Real) * alpha) :
    -(rad : Real) * beta < cx ∧
      cx < ((rad : Real) + 1) * beta ∧
      -(rad : Real) * alpha < cy ∧
      cy < ((rad : Real) + 1) * alpha := by
  have hl := abs_lt.mp hleft
  have hr := abs_lt.mp hright
  have hb := abs_lt.mp hbottom
  have ht := abs_lt.mp htop
  constructor
  · nlinarith [hcell.2.1, hr.1, hp.1]
  constructor
  · nlinarith [hcell.1, hl.1, hp.2.1]
  constructor
  · nlinarith [hcell.2.2.2, ht.1, hp.2.2.1]
  · nlinarith [hcell.2.2.1, hb.1, hp.2.2.2]

private theorem triangular_selected_vertex_abs_bounds {C : RegionCode}
    (R : Realization C) (orientation : Bool) (radius : Nat)
    (alpha beta : Real)
    (hHorizontal : ∀ a b,
      |selectedCoordinate orientation .horizontal (R.vertex a) -
        selectedCoordinate orientation .horizontal (R.vertex b)| < radius * beta)
    (hVertical : ∀ a b,
      |selectedCoordinate orientation .vertical (R.vertex a) -
        selectedCoordinate orientation .vertical (R.vertex b)| < radius * alpha)
    (e : Fin C.cellCount) :
    |selectedCoordinate orientation .horizontal
        (R.vertex (if orientation then C.bottomVertex e else C.leftVertex e))| <
        radius * beta ∧
    |selectedCoordinate orientation .horizontal
        (R.vertex (if orientation then C.topVertex e else C.rightVertex e))| <
        radius * beta ∧
    |selectedCoordinate orientation .vertical
        (R.vertex (if orientation then C.leftVertex e else C.bottomVertex e))| <
        radius * alpha ∧
    |selectedCoordinate orientation .vertical
        (R.vertex (if orientation then C.rightVertex e else C.topVertex e))| <
        radius * alpha := by
  have hzero (s : CoordSort) :
      selectedCoordinate orientation s (0 : Tiling.Plane) = 0 := by
    cases orientation <;> cases s <;> rfl
  have hh (a : Fin C.vertexCount) := hHorizontal C.originVertex a
  have hv (a : Fin C.vertexCount) := hVertical C.originVertex a
  have hh' (a : Fin C.vertexCount) :
      |selectedCoordinate orientation .horizontal (R.vertex a)| < radius * beta := by
    simpa [R.origin_eq_zero, hzero, abs_neg] using hh a
  have hv' (a : Fin C.vertexCount) :
      |selectedCoordinate orientation .vertical (R.vertex a)| < radius * alpha := by
    simpa [R.origin_eq_zero, hzero, abs_neg] using hv a
  exact ⟨hh' _, hh' _, hv' _, hv' _⟩

private theorem slabPiece_openCell_select
    {C : RegionCode} (R : Realization C) (D : SlabCertificate R.region)
    (j : Fin D.numberOfPieces) {U : Set Tiling.Plane}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hUtarget : U ⊆ {p : Tiling.Plane | p.re ∈ D.base j}) :
    ∃ q ∈ U, ∃ s : D.selectedPiece j, ∃ e : Fin C.cellCount,
      semanticOpenCellNL R D.orientation e s.1 q := by
  let cells : Set Tiling.Plane :=
    ⋃ e, {p | semanticOpenCellNL R D.orientation e 0 p}
  have hpresentation : cells =ᵐ[volume] D.selectedRegion.openCarrier := by
    rw [D.selectedRegion_eq]
    exact selected_presentation_ae_local R D.orientation
  have hall := triangular_allCentres_presentation_ae
    (D.selectedPiece j) cells D.selectedRegion.openCarrier
    (D.piece_tiles j).1 hpresentation
  have hcover := (D.piece_tiles j).2.2
  have hgood : ∀ᵐ q ∂volume, q ∈ U →
      ∃ s : D.selectedPiece j, q ∈ s.1 +ᵥ cells := by
    filter_upwards [hcover, hall] with q hqcover hqall
    intro hqU
    obtain ⟨s, hs⟩ := hqcover.mp (hUtarget hqU)
    exact ⟨s, (hqall s).mpr hs⟩
  obtain ⟨q, hqU, hqgood⟩ := triangular_exists_mem_open_of_ae hUopen hUne hgood
  obtain ⟨s, hqs⟩ := hqgood hqU
  obtain ⟨w, hw, hqw⟩ := Set.mem_vadd_set.mp hqs
  obtain ⟨e, hwe⟩ := Set.mem_iUnion.mp hw
  refine ⟨q, hqU, s, e, ?_⟩
  change q ∈ {p | semanticOpenCellNL R D.orientation e s.1 p}
  rw [semanticOpenCellNL_vadd_local]
  exact ⟨w, hwe, hqw⟩

private theorem generatedRepresentativeCount
    {K : Region} (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (orbit : FiniteSlabOrbitPresentation D) (radius : Nat)
    (jCode : Fin (triangularPieceCount (slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius))) :
    (triangularPiece (slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius) jCode).representativeCount =
      orbit.representativeCount ⟨jCode.val, by
        simpa [triangularPieceCount, slabRawCode] using jCode.isLt⟩ := by
  rcases jCode with ⟨v, hv⟩
  simp [triangularPiece, triangularPieceCount, slabRawCode]

private theorem generatedIntervalCount
    {K : Region} (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (orbit : FiniteSlabOrbitPresentation D) (radius : Nat)
    (jCode : Fin (triangularPieceCount (slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius))) :
    (triangularPiece (slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius) jCode).intervalCount =
      base.intervalCount ⟨jCode.val, by
        simpa [triangularPieceCount, slabRawCode] using jCode.isLt⟩ := by
  rcases jCode with ⟨v, hv⟩
  simp [triangularPiece, triangularPieceCount, slabRawCode]

private theorem generatedOrbitIndices
    {K : Region} (D : SlabCertificate K) (base : FiniteSlabBasePresentation D)
    (orbit : FiniteSlabOrbitPresentation D) (radius : Nat)
    (j : Fin D.numberOfPieces) (r : Fin (orbit.representativeCount j)) :
    let code := slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius
    ∃ jCode : Fin (triangularPieceCount code),
      ∃ rCode : Fin (triangularPiece code jCode).representativeCount,
        jCode.val = j.val ∧ rCode.val = r.val := by
  dsimp
  let code := slabRawCode D.orientation base.intervalCount
    orbit.representativeCount radius
  have hcount : triangularPieceCount code = D.numberOfPieces := by
    simp [code, triangularPieceCount, slabRawCode]
  let jCode : Fin (triangularPieceCount code) := Fin.cast hcount.symm j
  have hjCode : (⟨jCode.val, by simpa [hcount] using jCode.isLt⟩ :
      Fin D.numberOfPieces) = j := Fin.ext rfl
  have hrep : (triangularPiece code jCode).representativeCount =
      orbit.representativeCount j := by
    let jBack : Fin D.numberOfPieces := ⟨jCode.val, by
      simpa [hcount] using jCode.isLt⟩
    have hjBack : jBack = j := Fin.ext rfl
    have hpiece : (triangularPiece code jCode).representativeCount =
        orbit.representativeCount jBack := by
      exact generatedRepresentativeCount D base orbit radius jCode
    exact hpiece.trans (congrArg orbit.representativeCount hjBack)
  let rCode : Fin (triangularPiece code jCode).representativeCount :=
    Fin.cast hrep.symm r
  exact ⟨jCode, rCode, rfl, rfl⟩

private theorem slabFiniteCoverageWIP
    {C : RegionCode} (R : Realization C) (D : SlabCertificate R.region)
    (base : FiniteSlabBasePresentation D) (orbit : FiniteSlabOrbitPresentation D)
    (radius : Nat)
    (hhorizontal : ∀ a b,
      |selectedCoordinate D.orientation .horizontal (R.vertex a) -
        selectedCoordinate D.orientation .horizontal (R.vertex b)| <
          radius * D.commonHorizontalPeriod)
    (hvertical : ∀ a b,
      |selectedCoordinate D.orientation .vertical (R.vertex a) -
        selectedCoordinate D.orientation .vertical (R.vertex b)| <
          radius * D.commonVerticalPeriod) :
    let code := slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius
    let X := slabRawParametersWIP D base orbit radius
    ∀ j (p : Tiling.Plane), 0 < p.re → p.re < X.beta → 0 < p.im → p.im < X.alpha →
      (∃ ell q, q ∈ ([-1, 0, 1] : List Int) ∧
        X.intervalLeft ⟨j, ell⟩ + q * X.beta < p.re ∧
        p.re < X.intervalRight ⟨j, ell⟩ + q * X.beta) →
      ∃ i ∈ triangularFiniteIndicesProbe code j, ∃ e,
        slabSemanticClosedCellWIP R code.orientation e
          (triangularSemanticCentreProbe code X j i.1
            (triangularCenteredInteger i.2.1) (triangularCenteredInteger i.2.2)) p := by
  dsimp
  intro j p hp0 hpBeta hpI0 hpAlpha hbase
  let code := slabRawCode D.orientation base.intervalCount
    orbit.representativeCount radius
  let X := slabRawParametersWIP D base orbit radius
  let checked : Set Tiling.Plane :=
    ⋃ i : {i // i ∈ triangularFiniteIndicesProbe code j}, ⋃ e : Fin C.cellCount,
      {z | slabSemanticClosedCellWIP R code.orientation e
        (triangularSemanticCentreProbe code X j i.1.1
          (triangularCenteredInteger i.1.2.1) (triangularCenteredInteger i.1.2.2)) z}
  have hcheckedClosed : IsClosed checked := by
    apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro e
    unfold slabSemanticClosedCellWIP
    apply IsClosed.inter
    · exact isClosed_Ici.preimage Complex.continuous_re
    · apply IsClosed.inter
      · exact isClosed_Iic.preimage Complex.continuous_re
      · apply IsClosed.inter
        · exact isClosed_Ici.preimage Complex.continuous_im
        · exact isClosed_Iic.preimage Complex.continuous_im
  by_contra hcoverage
  push Not at hcoverage
  have hpNot : p ∉ checked := by
    intro hp
    rcases Set.mem_iUnion.mp hp with ⟨i, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨e, hpe⟩
    exact hcoverage i.1 i.2 e hpe
  obtain ⟨ell, q0, _hq0, hleft, hright⟩ := hbase
  let target : Set Tiling.Plane := {z |
    X.intervalLeft ⟨j, ell⟩ + q0 * X.beta < z.re ∧
    z.re < X.intervalRight ⟨j, ell⟩ + q0 * X.beta}
  let box : Set Tiling.Plane := {z | 0 < z.re ∧ z.re < X.beta ∧
    0 < z.im ∧ z.im < X.alpha}
  let U := box ∩ checkedᶜ ∩ target
  have hUopen : IsOpen U := by
    exact ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))).inter
      hcheckedClosed.isOpen_compl |>.inter
        ((isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const))
  have hpU : p ∈ U := ⟨⟨⟨hp0, hpBeta, hpI0, hpAlpha⟩, hpNot⟩, hleft, hright⟩
  let jD : Fin D.numberOfPieces := ⟨j.val, by
    have hj := j.isLt
    change j.val < code.pieces.length at hj
    simpa [code, slabRawCode] using hj⟩
  have hUtarget : U ⊆ {z : Tiling.Plane | z.re ∈ D.base jD} := by
    intro z hz
    let idx := slabIntervalIndexToBaseWIP D base orbit radius ⟨j, ell⟩
    have hidxj : idx.1 = jD := Fin.ext rfl
    have hleft' : base.left idx.1 idx.2 + q0 * D.commonHorizontalPeriod < z.re := by
      exact hz.2.1
    have hright' : z.re < base.right idx.1 idx.2 + q0 * D.commonHorizontalPeriod := by
      exact hz.2.2
    have hzP : z.re ∈ periodicOpenBase D base jD := by
      rw [periodicOpenBase, Set.mem_iUnion]
      cases hidxj
      exact ⟨q0, Set.mem_iUnion.mpr ⟨idx.2, And.intro hleft' hright'⟩⟩
    have hPopen : IsOpen (periodicOpenBase D base jD) := by
      apply isOpen_iUnion
      intro q
      apply isOpen_iUnion
      intro ell'
      exact isOpen_Ioo
    have hclosure : closure (D.base jD) = closure (periodicOpenBase D base jD) :=
      closure_eq_of_open_aeEq_real (D.base_open jD) hPopen (base.base_ae jD)
    have hzInterior : z.re ∈ interior (closure (periodicOpenBase D base jD)) :=
      interior_maximal subset_closure hPopen hzP
    rw [← hclosure, D.base_regular jD] at hzInterior
    exact hzInterior
  obtain ⟨z, hzU, s, e, hcell⟩ := slabPiece_openCell_select R D jD hUopen
    ⟨p, hpU⟩ hUtarget
  obtain ⟨r, n, k, hs⟩ := triangular_orbit_member_indices D orbit jD s.2
  obtain ⟨jCode, rCode, hjCode, hrCode⟩ :=
    generatedOrbitIndices D base orbit radius jD r
  have hj : jCode = j := Fin.ext (hjCode.trans rfl)
  subst jCode
  have hdiam := slabRawParametersWIP_vertex_diameter_bounds R D base orbit radius
    hhorizontal hvertical
  have hv := triangular_selected_vertex_abs_bounds R D.orientation radius
    D.commonVerticalPeriod D.commonHorizontalPeriod hdiam.1 hdiam.2 e
  have hzbox : 0 < z.re ∧ z.re < D.commonHorizontalPeriod ∧
      0 < z.im ∧ z.im < D.commonVerticalPeriod := by
    have hzboxX : 0 < z.re ∧ z.re < X.beta ∧ 0 < z.im ∧ z.im < X.alpha := hzU.1.1
    simpa [X, slabRawParametersWIP] using hzboxX
  have hcb := triangular_centre_bounds_of_openCell radius
    D.commonVerticalPeriod D.commonHorizontalPeriod s.1.re s.1.im z.re z.im
    (selectedCoordinate D.orientation .horizontal
      (R.vertex (if D.orientation then C.bottomVertex e else C.leftVertex e)))
    (selectedCoordinate D.orientation .horizontal
      (R.vertex (if D.orientation then C.topVertex e else C.rightVertex e)))
    (selectedCoordinate D.orientation .vertical
      (R.vertex (if D.orientation then C.leftVertex e else C.bottomVertex e)))
    (selectedCoordinate D.orientation .vertical
      (R.vertex (if D.orientation then C.rightVertex e else C.topVertex e)))
    hzbox hcell hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  have hsRe : s.1.re = (orbit.representative jD r).re +
      (n : Real) * D.commonHorizontalPeriod := by
    rw [hs]
    simp [skewPeriodVector, verticalPeriodVector]
  have hsIm : s.1.im = (orbit.representative jD r).im +
      (n : Real) * D.normalizedShear jD +
      (k : Real) * D.commonVerticalPeriod := by
    rw [hs]
    simp [skewPeriodVector, verticalPeriodVector]
  have hbounds := triangular_neighbour_bounds_from_expanded_geometry radius
    D.commonVerticalPeriod D.commonHorizontalPeriod (D.normalizedShear jD)
    (orbit.representative jD r).re (orbit.representative jD r).im
    s.1.re s.1.im n k D.commonVerticalPeriod_pos D.commonHorizontalPeriod_pos
    ⟨D.normalizedShear_nonnegative jD, D.normalizedShear_lt jD⟩
    ⟨(orbit.normalized jD r).1, (orbit.normalized jD r).2.1⟩
    ⟨(orbit.normalized jD r).2.2.1, (orbit.normalized jD r).2.2.2⟩
    hcb.1 hcb.2.1 hcb.2.2.1 hcb.2.2.2 hsRe hsIm
  obtain ⟨i, hi, hir, hin, hik⟩ :=
    triangular_index_enumeration_complete code j rCode n k hbounds.1 hbounds.2
  let rBack : Fin (orbit.representativeCount jD) := ⟨rCode.val, by
    rw [← generatedRepresentativeCount D base orbit radius j]
    exact rCode.isLt⟩
  have hrBack : rBack = r := Fin.ext hrCode
  have hrOrbit : (orbit.representative jD rBack).re =
      (orbit.representative jD r).re := by
    rw [hrBack]
  let jBack : Fin D.numberOfPieces := ⟨j.val, by
    have hj := j.isLt
    change j.val < code.pieces.length at hj
    simpa [code, slabRawCode] using hj⟩
  have hjBack : jBack = jD := Fin.ext hjCode
  have hrepCount : (triangularPiece code j).representativeCount =
      orbit.representativeCount jBack := by
    exact generatedRepresentativeCount D base orbit radius j
  have hrepGenerated : orbit.representative jBack (Fin.cast hrepCount rCode) =
      orbit.representative jD r := by
    cases hjBack
    congr 1
  have hrepX : X.representativeX ⟨j, rCode⟩ =
      (orbit.representative jD r).re := by
    change (orbit.representative jBack (Fin.cast hrepCount rCode)).re = _
    exact congrArg Complex.re hrepGenerated
  have hrepY : X.representativeY ⟨j, rCode⟩ =
      (orbit.representative jD r).im := by
    change (orbit.representative jBack (Fin.cast hrepCount rCode)).im = _
    exact congrArg Complex.im hrepGenerated
  have hshear : X.shear j = D.normalizedShear jD := by
    change D.normalizedShear jBack = D.normalizedShear jD
    rw [hjBack]
  have hbeta : X.beta = D.commonHorizontalPeriod := rfl
  have halpha : X.alpha = D.commonVerticalPeriod := rfl
  have hc : triangularSemanticCentreProbe code X j i.1
      (triangularCenteredInteger i.2.1) (triangularCenteredInteger i.2.2) = s.1 := by
    rw [hir, hin, hik, hs]
    apply Complex.ext <;>
      simp only [triangularSemanticCentreProbe, hrepX, hrepY, hshear, hbeta, halpha,
        zsmul_eq_mul, skewPeriodVector, verticalPeriodVector, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
        Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im] <;> ring
  have hzChecked : z ∈ checked := by
    apply Set.mem_iUnion.mpr
    refine ⟨⟨i, hi⟩, Set.mem_iUnion.mpr ⟨e, ?_⟩⟩
    change slabSemanticClosedCellWIP R code.orientation e
      (triangularSemanticCentreProbe code X j i.1
        (triangularCenteredInteger i.2.1) (triangularCenteredInteger i.2.2)) z
    rw [hc]
    exact ⟨hcell.1.le, hcell.2.1.le, hcell.2.2.1.le, hcell.2.2.2.le⟩
  exact hzU.1.2 hzChecked

private theorem slabRawParametersWIP_checks
    {C : RegionCode} (R : Realization C) (D : SlabCertificate R.region)
    (base : FiniteSlabBasePresentation D) (orbit : FiniteSlabOrbitPresentation D)
    (radius : Nat)
    (hhorizontal : ∀ a b,
      |selectedCoordinate D.orientation .horizontal (R.vertex a) -
        selectedCoordinate D.orientation .horizontal (R.vertex b)| <
          radius * D.commonHorizontalPeriod)
    (hvertical : ∀ a b,
      |selectedCoordinate D.orientation .vertical (R.vertex a) -
        selectedCoordinate D.orientation .vertical (R.vertex b)| <
          radius * D.commonVerticalPeriod) :
    let code := slabRawCode D.orientation base.intervalCount
      orbit.representativeCount radius
    TriangularChecks R code (slabRawParametersWIP D base orbit radius) := by
  dsimp
  let code := slabRawCode D.orientation base.intervalCount
    orbit.representativeCount radius
  let X := slabRawParametersWIP D base orbit radius
  refine {
    periods_pos := slabRawParametersWIP_periods_pos D base orbit radius
    shear_normalized := slabRawParametersWIP_shear_normalized D base orbit radius
    intervals_normalized := slabRawParametersWIP_intervals_normalized D base orbit radius
    interval_interiors_disjoint :=
      slabRawParametersWIP_interval_interiors_disjoint D base orbit radius
    base_period_covered := slabRawParametersWIP_base_period_covered D base orbit radius
    representatives_normalized :=
      slabRawParametersWIP_representatives_normalized D base orbit radius
    vertex_diameter_bounds :=
      slabRawParametersWIP_vertex_diameter_bounds R D base orbit radius
        hhorizontal hvertical
    finite_packing := ?_
    no_leakage := ?_
    finite_coverage := ?_ }
  · intro j i i' hne
    change triangularSemanticCentreProbe code X j i.1
        (triangularCenteredInteger i.2.1) (triangularCenteredInteger i.2.2) =
          triangularSemanticCentreProbe code X j i'.1
            (triangularCenteredInteger i'.2.1) (triangularCenteredInteger i'.2.2) ∨
      ∀ e e', slabSemanticCellsNonoverlapWIP R code.orientation e e'
        (triangularSemanticCentreProbe code X j i.1
          (triangularCenteredInteger i.2.1) (triangularCenteredInteger i.2.2))
        (triangularSemanticCentreProbe code X j i'.1
          (triangularCenteredInteger i'.2.1) (triangularCenteredInteger i'.2.2))
    let jD : Fin D.numberOfPieces := ⟨j.val, by
      have hj := j.isLt
      change j.val < code.pieces.length at hj
      simpa [code, slabRawCode] using hj⟩
    let rD : Fin (orbit.representativeCount jD) := ⟨i.1.val, by
      have h := i.1.isLt
      change i.1.val < (triangularPiece code j).representativeCount at h
      rw [generatedRepresentativeCount D base orbit radius j] at h
      exact h⟩
    let rD' : Fin (orbit.representativeCount jD) := ⟨i'.1.val, by
      have h := i'.1.isLt
      change i'.1.val < (triangularPiece code j).representativeCount at h
      rw [generatedRepresentativeCount D base orbit radius j] at h
      exact h⟩
    let n := triangularCenteredInteger i.2.1
    let k := triangularCenteredInteger i.2.2
    let n' := triangularCenteredInteger i'.2.1
    let k' := triangularCenteredInteger i'.2.2
    have hc : triangularSemanticCentreProbe code X j i.1 n k ∈ D.selectedPiece jD := by
      change (orbit.representative jD rD).re + n * D.commonHorizontalPeriod +
          ((orbit.representative jD rD).im + n * D.normalizedShear jD +
            k * D.commonVerticalPeriod) * Complex.I ∈ D.selectedPiece jD
      exact slabSemanticCentreWIP_mem_selectedPiece D orbit jD rD n k
    have hc' : triangularSemanticCentreProbe code X j i'.1 n' k' ∈
        D.selectedPiece jD := by
      change (orbit.representative jD rD').re + n' * D.commonHorizontalPeriod +
          ((orbit.representative jD rD').im + n' * D.normalizedShear jD +
            k' * D.commonVerticalPeriod) * Complex.I ∈ D.selectedPiece jD
      exact slabSemanticCentreWIP_mem_selectedPiece D orbit jD rD' n' k'
    exact semanticCellsNonoverlapNL_of_packing R D jD hc hc'
  · intro j p hp0 hpBeta _hpI0 _hpAlpha hopen
    obtain ⟨i, _hi, e, hcell⟩ := hopen
    change slabSemanticOpenCellWIP R code.orientation e
      (triangularSemanticCentreProbe code X j i.1
        (triangularCenteredInteger i.2.1) (triangularCenteredInteger i.2.2)) p at hcell
    let jD : Fin D.numberOfPieces := ⟨j.val, by
      have hj := j.isLt
      change j.val < code.pieces.length at hj
      simpa [code, slabRawCode] using hj⟩
    let rD : Fin (orbit.representativeCount jD) := ⟨i.1.val, by
      have h := i.1.isLt
      change i.1.val < (triangularPiece code j).representativeCount at h
      rw [generatedRepresentativeCount D base orbit radius j] at h
      exact h⟩
    let n := triangularCenteredInteger i.2.1
    let k := triangularCenteredInteger i.2.2
    have hc : triangularSemanticCentreProbe code X j i.1 n k ∈ D.selectedPiece jD := by
      change (orbit.representative jD rD).re + n * D.commonHorizontalPeriod +
          ((orbit.representative jD rD).im + n * D.normalizedShear jD +
            k * D.commonVerticalPeriod) * Complex.I ∈ D.selectedPiece jD
      exact slabSemanticCentreWIP_mem_selectedPiece D orbit jD rD n k
    have hpBeta' : p.re < D.commonHorizontalPeriod := hpBeta
    obtain ⟨ellD, q, hq, hl, hr⟩ := semanticCell_noLeakage R D base jD
      (triangularSemanticCentreProbe code X j i.1 n k) hc e p hcell hp0 hpBeta'
    have hcount : (code.pieces.get j).intervalCount = base.intervalCount jD := by
      exact generatedIntervalCount D base orbit radius j
    let ell : Fin (code.pieces.get j).intervalCount := Fin.cast hcount.symm ellD
    refine ⟨ell, q, hq, ?_, ?_⟩
    · change base.left jD (Fin.cast hcount ell) + q * D.commonHorizontalPeriod ≤ p.re
      simpa [ell] using hl
    · change p.re ≤ base.right jD (Fin.cast hcount ell) + q * D.commonHorizontalPeriod
      simpa [ell] using hr
  · exact slabFiniteCoverageWIP R D base orbit radius hhorizontal hvertical

private theorem slabCertificate_rawChecks :
    ∀ {C : RegionCode} (R : Realization C) (D : SlabCertificate R.region),
      ∃ base : FiniteSlabBasePresentation D,
      ∃ orbit : FiniteSlabOrbitPresentation D,
      ∃ radius : Nat,
      ∃ X : TriangularRawParameters
        (slabRawCode D.orientation base.intervalCount orbit.representativeCount radius),
        let code := slabRawCode D.orientation base.intervalCount
          orbit.representativeCount radius
        code.wellFormed = true ∧ TriangularChecks R code X := by
  intro C R D
  obtain ⟨base⟩ := slab_bases_finiteIntervals D
  obtain ⟨orbit⟩ := slab_piece_finiteOrbit D
  obtain ⟨radius, hradius, hhorizontal, hvertical⟩ :=
    slab_checkingRadius_exists R D rfl
  let code := slabRawCode D.orientation base.intervalCount
    orbit.representativeCount radius
  let X := slabRawParametersWIP D base orbit radius
  refine ⟨base, orbit, radius, X, ?_, ?_⟩
  · apply slabRawCode_wellFormed D.orientation base.intervalCount
      orbit.representativeCount radius
    · exact lt_of_lt_of_le (by norm_num : 0 < 2) D.atLeastTwoPieces
    · exact base.intervalCount_pos
    · exact orbit.representativeCount_pos
    · exact hradius
  · exact slabRawParametersWIP_checks R D base orbit radius hhorizontal hvertical

private def probeCenteredInteger {radius : Nat} (i : Fin (2 * radius + 1)) : Int :=
  Int.ofNat i.val - Int.ofNat radius

private abbrev ProbeLatticeIndex (representativeCount firstBound secondBound : Nat) :=
  Fin representativeCount × Fin (2 * firstBound + 1) × Fin (2 * secondBound + 1)

private def probeLatticeIndices (representativeCount firstBound secondBound : Nat) :
    Finset (ProbeLatticeIndex representativeCount firstBound secondBound) :=
  Finset.univ.filter fun i ↦
    (probeCenteredInteger i.2.1).natAbs < firstBound ∧
      (probeCenteredInteger i.2.2).natAbs < secondBound

private def probeLatticeIndexList (representativeCount firstBound secondBound : Nat) :
    List (ProbeLatticeIndex representativeCount firstBound secondBound) :=
  ((List.ofFn fun r : Fin representativeCount => r).flatMap fun r =>
    (List.ofFn fun n : Fin (2 * firstBound + 1) => n).flatMap fun n =>
      List.ofFn fun m : Fin (2 * secondBound + 1) => (r, n, m)).filter fun i =>
        decide ((probeCenteredInteger i.2.1).natAbs < firstBound ∧
          (probeCenteredInteger i.2.2).natAbs < secondBound)

private theorem mem_probeLatticeIndices_iff
    {representativeCount firstBound secondBound : Nat}
    (i : ProbeLatticeIndex representativeCount firstBound secondBound) :
    i ∈ probeLatticeIndices representativeCount firstBound secondBound ↔
      (probeCenteredInteger i.2.1).natAbs < firstBound ∧
      (probeCenteredInteger i.2.2).natAbs < secondBound := by
  simp [probeLatticeIndices]

private theorem probeCenteredInteger_complete : ∀ radius (n : Int),
    n.natAbs ≤ radius → ∃ i : Fin (2 * radius + 1), probeCenteredInteger i = n := by
  intro radius n hn
  by_cases hnonneg : 0 ≤ n
  · have hi : n.natAbs + radius < 2 * radius + 1 := by omega
    refine ⟨⟨n.natAbs + radius, hi⟩, ?_⟩
    change Int.ofNat (n.natAbs + radius) - Int.ofNat radius = n
    have hadd : Int.ofNat (n.natAbs + radius) =
        Int.ofNat n.natAbs + Int.ofNat radius := Int.natCast_add _ _
    rw [hadd]
    have hnat : Int.ofNat n.natAbs = n := Int.natAbs_of_nonneg hnonneg
    rw [hnat]
    omega
  · have hneg : n < 0 := Int.lt_of_not_ge hnonneg
    have hi : radius - n.natAbs < 2 * radius + 1 := by omega
    refine ⟨⟨radius - n.natAbs, hi⟩, ?_⟩
    change Int.ofNat (radius - n.natAbs) - Int.ofNat radius = n
    have hsub : Int.ofNat (radius - n.natAbs) =
        Int.ofNat radius - Int.ofNat n.natAbs := Int.ofNat_sub hn
    rw [hsub]
    have hnat : Int.ofNat n.natAbs = -n :=
      Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
    rw [hnat]
    omega

private theorem probeLatticeIndex_complete
    {representativeCount firstBound secondBound : Nat}
    (r : Fin representativeCount) (n m : Int)
    (hn : n.natAbs < firstBound) (hm : m.natAbs < secondBound) :
    ∃ i ∈ probeLatticeIndices representativeCount firstBound secondBound,
      i.1 = r ∧ probeCenteredInteger i.2.1 = n ∧ probeCenteredInteger i.2.2 = m := by
  obtain ⟨ni, hni⟩ := probeCenteredInteger_complete firstBound n (by omega)
  obtain ⟨mi, hmi⟩ := probeCenteredInteger_complete secondBound m (by omega)
  refine ⟨(r, ni, mi), ?_, rfl, hni, hmi⟩
  rw [mem_probeLatticeIndices_iff]
  simpa [hni, hmi] using And.intro hn hm

private theorem positiveNatMul_gt {a B : Real} (ha : 0 < a) :
    ∃ n : Nat, 0 < n ∧ B < n * a := by
  obtain ⟨n, hn⟩ := exists_nat_gt (B / a)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have hratio : B / a < (n + 1 : Nat) := lt_trans hn (by norm_num)
  simpa [Nat.cast_add, Nat.cast_one] using (div_lt_iff₀ ha).mp hratio

/-- A single pair of positive checking bounds controls all signed period sums and all
chosen orbit representatives. -/
private theorem latticeSignedAndRepresentativeBounds_exists
    {K : Tiling.AxisParallel.Region}
    {D : Tiling.AxisParallel.Terminal.PeriodicReplacement K Set.univ}
    (orbit : FiniteLatticeOrbitPresentation D) :
    ∃ horizontalBound verticalBound : Real,
      0 < horizontalBound ∧ 0 < verticalBound ∧
      (∀ sx ∈ ([-1, 1] : List Int), ∀ sy ∈ ([-1, 1] : List Int),
        sx * orbit.firstPeriod.re + sy * orbit.secondPeriod.re ≤ horizontalBound ∧
        sx * orbit.firstPeriod.im + sy * orbit.secondPeriod.im ≤ verticalBound) ∧
      (∀ r, |(orbit.representative r).re| ≤ horizontalBound ∧
        |(orbit.representative r).im| ≤ verticalBound) := by
  obtain ⟨repX, hrepX⟩ := Finite.exists_le
    (fun r : Fin orbit.representativeCount ↦ |(orbit.representative r).re|)
  obtain ⟨repY, hrepY⟩ := Finite.exists_le
    (fun r : Fin orbit.representativeCount ↦ |(orbit.representative r).im|)
  have hrepXnonneg : 0 ≤ repX :=
    (abs_nonneg (orbit.representative ⟨0, orbit.representativeCount_pos⟩).re).trans
      (hrepX ⟨0, orbit.representativeCount_pos⟩)
  have hrepYnonneg : 0 ≤ repY :=
    (abs_nonneg (orbit.representative ⟨0, orbit.representativeCount_pos⟩).im).trans
      (hrepY ⟨0, orbit.representativeCount_pos⟩)
  let Hx := |orbit.firstPeriod.re| + |orbit.secondPeriod.re| + repX + 1
  let Hy := |orbit.firstPeriod.im| + |orbit.secondPeriod.im| + repY + 1
  refine ⟨Hx, Hy, by dsimp [Hx]; positivity, by dsimp [Hy]; positivity, ?_, ?_⟩
  · intro sx hsx sy hsy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsx hsy
    rcases hsx with rfl | rfl <;> rcases hsy with rfl | rfl <;>
      constructor <;> dsimp [Hx, Hy] <;> norm_num <;>
      linarith [le_abs_self orbit.firstPeriod.re, neg_le_abs orbit.firstPeriod.re,
        le_abs_self orbit.secondPeriod.re, neg_le_abs orbit.secondPeriod.re,
        le_abs_self orbit.firstPeriod.im, neg_le_abs orbit.firstPeriod.im,
        le_abs_self orbit.secondPeriod.im, neg_le_abs orbit.secondPeriod.im]
  · intro r
    constructor
    · dsimp [Hx]
      linarith [hrepX r, abs_nonneg orbit.firstPeriod.re,
        abs_nonneg orbit.secondPeriod.re]
    · dsimp [Hy]
      linarith [hrepY r, abs_nonneg orbit.firstPeriod.im,
        abs_nonneg orbit.secondPeriod.im]

/-- Positive finite index bounds satisfying the remaining numerical inequalities. -/
private theorem latticeIndexBounds_exists
    {C : Tiling.AxisParallel.Terminal.Executable.RegionCode}
    (R : Tiling.AxisParallel.Terminal.Executable.Realization C)
    {K : Tiling.AxisParallel.Region}
    {D : Tiling.AxisParallel.Terminal.PeriodicReplacement K Set.univ}
    (orbit : FiniteLatticeOrbitPresentation D)
    (horizontalBound verticalBound : Real) :
    ∃ (firstPeriodAbsoluteXBound : Real) (firstIndexBound secondIndexBound : Nat),
      0 < firstIndexBound ∧ 0 < secondIndexBound ∧
      (∀ a b, 2 * horizontalBound + |(R.vertex a).re - (R.vertex b).re| <
        firstIndexBound *
          (orbit.firstPeriod.re - orbit.rationalSeparator * orbit.secondPeriod.re)) ∧
      (∀ a b, 2 * verticalBound + |(R.vertex a).im - (R.vertex b).im| <
        firstIndexBound *
          (orbit.rationalSeparator * orbit.secondPeriod.im - orbit.firstPeriod.im)) ∧
      0 ≤ firstPeriodAbsoluteXBound ∧
      orbit.firstPeriod.re ≤ firstPeriodAbsoluteXBound ∧
      -orbit.firstPeriod.re ≤ firstPeriodAbsoluteXBound ∧
      (∀ a b, 2 * horizontalBound + |(R.vertex a).re - (R.vertex b).re| +
        firstIndexBound * firstPeriodAbsoluteXBound <
          secondIndexBound * orbit.secondPeriod.re) := by
  obtain ⟨vertexX, hvertexX⟩ := Finite.exists_le
    (fun p : Fin C.vertexCount × Fin C.vertexCount ↦
      |(R.vertex p.1).re - (R.vertex p.2).re|)
  obtain ⟨vertexY, hvertexY⟩ := Finite.exists_le
    (fun p : Fin C.vertexCount × Fin C.vertexCount ↦
      |(R.vertex p.1).im - (R.vertex p.2).im|)
  let Ux := |orbit.firstPeriod.re|
  let target := max
    ((2 * horizontalBound + vertexX) /
      (orbit.firstPeriod.re - orbit.rationalSeparator * orbit.secondPeriod.re))
    ((2 * verticalBound + vertexY) /
      (orbit.rationalSeparator * orbit.secondPeriod.im - orbit.firstPeriod.im))
  obtain ⟨L, hL⟩ := exists_nat_gt target
  let firstBound := L + 1
  obtain ⟨secondBound, hSecondPos, hSecond⟩ := positiveNatMul_gt
    (a := orbit.secondPeriod.re)
    (B := 2 * horizontalBound + vertexX + firstBound * Ux)
    orbit.second_first_pos
  refine ⟨Ux, firstBound, secondBound, Nat.succ_pos L, hSecondPos, ?_, ?_,
    abs_nonneg _, le_abs_self _, neg_le_abs _, ?_⟩
  · intro a b
    have hv := hvertexX (a, b)
    have ht : (2 * horizontalBound + vertexX) /
        (orbit.firstPeriod.re - orbit.rationalSeparator * orbit.secondPeriod.re) <
        (firstBound : Nat) := lt_of_le_of_lt (le_max_left _ _) (hL.trans (by
          dsimp [firstBound]
          norm_num))
    have hm := (div_lt_iff₀ orbit.separated_first_pos).mp ht
    have hle : 2 * horizontalBound + |(R.vertex a).re - (R.vertex b).re| ≤
        2 * horizontalBound + vertexX := by linarith
    exact hle.trans_lt hm
  · intro a b
    have hv := hvertexY (a, b)
    have ht : (2 * verticalBound + vertexY) /
        (orbit.rationalSeparator * orbit.secondPeriod.im - orbit.firstPeriod.im) <
        (firstBound : Nat) := lt_of_le_of_lt (le_max_right _ _) (hL.trans (by
          dsimp [firstBound]
          norm_num))
    have hm := (div_lt_iff₀ orbit.separated_second_pos).mp ht
    have hle : 2 * verticalBound + |(R.vertex a).im - (R.vertex b).im| ≤
        2 * verticalBound + vertexY := by linarith
    exact hle.trans_lt hm
  · intro a b
    have hv := hvertexX (a, b)
    have hle : 2 * horizontalBound + |(R.vertex a).re - (R.vertex b).re| +
        firstBound * Ux ≤ 2 * horizontalBound + vertexX + firstBound * Ux := by
      linarith
    exact hle.trans_lt hSecond

open Tiling.AxisParallel.Terminal.Executable.PositiveVerification

private theorem ae_inter_measure_ne_zero_of_open_subset
    {U A B K K' : Set Tiling.Plane}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hUA : U ⊆ A) (hUB : U ⊆ B)
    (hAK : A =ᵐ[MeasureTheory.volume] K)
    (hBK : B =ᵐ[MeasureTheory.volume] K') :
    MeasureTheory.volume (K ∩ K') ≠ 0 := by
  intro hzero
  have hinter : (A ∩ B : Set Tiling.Plane) =ᵐ[MeasureTheory.volume]
      (K ∩ K' : Set Tiling.Plane) := by
    filter_upwards [hAK, hBK] with z hzA hzB
    change (z ∈ A) = (z ∈ K) at hzA
    change (z ∈ B) = (z ∈ K') at hzB
    change (z ∈ A ∧ z ∈ B) = (z ∈ K ∧ z ∈ K')
    rw [hzA, hzB]
  have habZero : MeasureTheory.volume (A ∩ B) = 0 := by
    rw [MeasureTheory.measure_congr hinter]
    exact hzero
  have hUzero : MeasureTheory.volume U = 0 :=
    MeasureTheory.measure_mono_null (fun z hz ↦ And.intro (hUA hz) (hUB hz)) habZero
  exact (hUopen.measure_pos MeasureTheory.volume hUne).ne' hUzero

private theorem exists_mem_open_of_ae {U : Set Tiling.Plane} {P : Tiling.Plane → Prop}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hP : ∀ᵐ x ∂MeasureTheory.volume, P x) : ∃ x ∈ U, P x := by
  have hμ : MeasureTheory.volume.restrict U ≠ 0 := by
    intro hz
    have hzero : MeasureTheory.volume U = 0 := by
      rw [← MeasureTheory.Measure.restrict_apply_univ U, hz]
      simp
    exact (hUopen.measure_pos MeasureTheory.volume hUne).ne' hzero
  let hne : (MeasureTheory.ae (MeasureTheory.volume.restrict U)).NeBot :=
    MeasureTheory.ae_neBot.mpr hμ
  have hP' : ∀ᵐ x ∂MeasureTheory.volume.restrict U, P x :=
    hP.filter_mono MeasureTheory.ae_restrict_le
  rcases @Filter.Eventually.exists Tiling.Plane _
      (MeasureTheory.ae (MeasureTheory.volume.restrict U)) hne
      (hP'.and (MeasureTheory.ae_restrict_mem hUopen.measurableSet)) with ⟨x, hxP, hxU⟩
  exact ⟨x, hxU, hxP⟩

/-- Same-module assembly core.  Its final two constructor fields are deliberately left
as the live proof frontier below. -/
private theorem latticeBoundsAndChecks_ofOrbit
    {C : Tiling.AxisParallel.Terminal.Executable.RegionCode}
    (R : Tiling.AxisParallel.Terminal.Executable.Realization C)
    (D : Tiling.AxisParallel.Terminal.PeriodicReplacement R.region Set.univ)
    (orbit : FiniteLatticeOrbitPresentation D) :
    ∃ firstBound secondBound,
    ∃ X : LatticeRawParameters
      (latticeRawCode orbit.rationalSeparator orbit.representativeCount
        firstBound secondBound),
      let code := latticeRawCode orbit.rationalSeparator orbit.representativeCount
        firstBound secondBound
      latticeCentreSet code X = D.centres ∧ code.wellFormed = true ∧
        LatticeChecks R code X := by
  obtain ⟨Hx, Hy, hHx, hHy, hSigned, hRepresentative⟩ :=
    latticeSignedAndRepresentativeBounds_exists orbit
  obtain ⟨Ux, firstBound, secondBound, hFirstPos, hSecondPos,
      hFirstX, hFirstY, hUx0, hUx, hNegUx, hSecond⟩ :=
    latticeIndexBounds_exists R orbit Hx Hy
  let code := latticeRawCode orbit.rationalSeparator orbit.representativeCount
    firstBound secondBound
  let X : LatticeRawParameters code := {
    firstPeriod := orbit.firstPeriod
    secondPeriod := orbit.secondPeriod
    representative := orbit.representative
    horizontalBound := Hx
    verticalBound := Hy
    firstPeriodAbsoluteXBound := Ux
  }
  refine ⟨firstBound, secondBound, X, ?_, ?_, ?_⟩
  · change {p | ∃ r n m,
      p = orbit.representative r + n • orbit.firstPeriod + m • orbit.secondPeriod} =
        D.centres
    exact orbit.presents.symm
  · exact latticeRawCode_wellFormed _ _ _ _ orbit.representativeCount_pos
      hFirstPos hSecondPos
  · refine {
      separated_periods := ⟨orbit.second_first_pos, orbit.second_second_pos,
        orbit.separated_first_pos, orbit.separated_second_pos⟩
      checking_bounds_pos := ⟨hHx, hHy⟩
      period_signed_bounds := hSigned
      representatives_bounded := hRepresentative
      first_index_bounds := ⟨hFirstX, hFirstY⟩
      first_period_x_bound := ⟨hUx0, hUx, hNegUx⟩
      second_index_bound := hSecond
      finite_packing := by
        intro i i' _hi _hi' _hne
        let c := orbit.representative i.1 +
          probeCenteredInteger i.2.1 • orbit.firstPeriod +
          probeCenteredInteger i.2.2 • orbit.secondPeriod
        let c' := orbit.representative i'.1 +
          probeCenteredInteger i'.2.1 • orbit.firstPeriod +
          probeCenteredInteger i'.2.2 • orbit.secondPeriod
        change c = c' ∨ ∀ e e',
          c.re + (R.vertex (C.rightVertex e)).re ≤
              c'.re + (R.vertex (C.leftVertex e')).re ∨
          c'.re + (R.vertex (C.rightVertex e')).re ≤
              c.re + (R.vertex (C.leftVertex e)).re ∨
          c.im + (R.vertex (C.topVertex e)).im ≤
              c'.im + (R.vertex (C.bottomVertex e')).im ∨
          c'.im + (R.vertex (C.topVertex e')).im ≤
              c.im + (R.vertex (C.bottomVertex e)).im
        by_cases hcc : c = c'
        · exact Or.inl hcc
        · right
          intro e e'
          by_contra hno
          simp only [not_or, not_le] at hno
          let cell : Fin C.cellCount → Set Tiling.Plane := fun f ↦
            {z | (R.vertex (C.leftVertex f)).re < z.re ∧
              z.re < (R.vertex (C.rightVertex f)).re ∧
              (R.vertex (C.bottomVertex f)).im < z.im ∧
              z.im < (R.vertex (C.topVertex f)).im}
          let U := (c +ᵥ cell e) ∩ (c' +ᵥ cell e')
          have hUopen : IsOpen U := by
            apply IsOpen.inter
            · exact (isOpen_lt continuous_const Complex.continuous_re).inter
                ((isOpen_lt Complex.continuous_re continuous_const).inter
                  ((isOpen_lt continuous_const Complex.continuous_im).inter
                    (isOpen_lt Complex.continuous_im continuous_const))) |>.vadd c
            · exact (isOpen_lt continuous_const Complex.continuous_re).inter
                ((isOpen_lt Complex.continuous_re continuous_const).inter
                  ((isOpen_lt continuous_const Complex.continuous_im).inter
                    (isOpen_lt Complex.continuous_im continuous_const))) |>.vadd c'
          let z : Tiling.Plane := Complex.mk
            ((max (c.re + (R.vertex (C.leftVertex e)).re)
                (c'.re + (R.vertex (C.leftVertex e')).re) +
              min (c.re + (R.vertex (C.rightVertex e)).re)
                (c'.re + (R.vertex (C.rightVertex e')).re)) / 2)
            ((max (c.im + (R.vertex (C.bottomVertex e)).im)
                (c'.im + (R.vertex (C.bottomVertex e')).im) +
              min (c.im + (R.vertex (C.topVertex e)).im)
                (c'.im + (R.vertex (C.topVertex e')).im)) / 2)
          have hxgap : max (c.re + (R.vertex (C.leftVertex e)).re)
              (c'.re + (R.vertex (C.leftVertex e')).re) <
              min (c.re + (R.vertex (C.rightVertex e)).re)
                (c'.re + (R.vertex (C.rightVertex e')).re) := by
            rw [max_lt_iff, lt_min_iff, lt_min_iff]
            exact ⟨⟨by linarith [R.left_lt_right e], hno.2.1⟩,
              ⟨hno.1, by linarith [R.left_lt_right e']⟩⟩
          have hygap : max (c.im + (R.vertex (C.bottomVertex e)).im)
              (c'.im + (R.vertex (C.bottomVertex e')).im) <
              min (c.im + (R.vertex (C.topVertex e)).im)
                (c'.im + (R.vertex (C.topVertex e')).im) := by
            rw [max_lt_iff, lt_min_iff, lt_min_iff]
            exact ⟨⟨by linarith [R.bottom_lt_top e], hno.2.2.2⟩,
              ⟨hno.2.2.1, by linarith [R.bottom_lt_top e']⟩⟩
          have hz : z ∈ U := by
            dsimp [U]
            constructor
            · refine ⟨z - c, ?_, by simp [vadd_eq_add, sub_eq_add_neg]⟩
              dsimp [cell, z]
              refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)) <;>
                linarith [le_max_left
                  (c.re + (R.vertex (C.leftVertex e)).re)
                  (c'.re + (R.vertex (C.leftVertex e')).re),
                  min_le_left
                  (c.re + (R.vertex (C.rightVertex e)).re)
                  (c'.re + (R.vertex (C.rightVertex e')).re),
                  le_max_left
                  (c.im + (R.vertex (C.bottomVertex e)).im)
                  (c'.im + (R.vertex (C.bottomVertex e')).im),
                  min_le_left
                  (c.im + (R.vertex (C.topVertex e)).im)
                  (c'.im + (R.vertex (C.topVertex e')).im),
                  R.left_lt_right e, R.left_lt_right e',
                  R.bottom_lt_top e, R.bottom_lt_top e']
            · refine ⟨z - c', ?_, by simp [vadd_eq_add, sub_eq_add_neg]⟩
              dsimp [cell, z]
              refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)) <;>
              linarith [le_max_left
                (c.re + (R.vertex (C.leftVertex e)).re)
                (c'.re + (R.vertex (C.leftVertex e')).re),
                le_max_right
                (c.re + (R.vertex (C.leftVertex e)).re)
                (c'.re + (R.vertex (C.leftVertex e')).re),
                min_le_left
                (c.re + (R.vertex (C.rightVertex e)).re)
                (c'.re + (R.vertex (C.rightVertex e')).re),
                min_le_right
                (c.re + (R.vertex (C.rightVertex e)).re)
                (c'.re + (R.vertex (C.rightVertex e')).re),
                le_max_left
                (c.im + (R.vertex (C.bottomVertex e)).im)
                (c'.im + (R.vertex (C.bottomVertex e')).im),
                le_max_right
                (c.im + (R.vertex (C.bottomVertex e)).im)
                (c'.im + (R.vertex (C.bottomVertex e')).im),
                min_le_left
                (c.im + (R.vertex (C.topVertex e)).im)
                (c'.im + (R.vertex (C.topVertex e')).im),
                min_le_right
                (c.im + (R.vertex (C.topVertex e)).im)
                (c'.im + (R.vertex (C.topVertex e')).im),
                R.left_lt_right e, R.left_lt_right e',
                R.bottom_lt_top e, R.bottom_lt_top e']
          let A := c +ᵥ ⋃ f, cell f
          let B := c' +ᵥ ⋃ f, cell f
          have hUA : U ⊆ A := by
            intro w hw
            obtain ⟨q, hq, rfl⟩ := hw.1
            exact ⟨q, Set.mem_iUnion.mpr ⟨e, hq⟩, rfl⟩
          have hUB : U ⊆ B := by
            intro w hw
            obtain ⟨q, hq, rfl⟩ := hw.2
            exact ⟨q, Set.mem_iUnion.mpr ⟨e', hq⟩, rfl⟩
          have hAK : A =ᵐ[MeasureTheory.volume] c +ᵥ R.region.openCarrier := by
            exact (MeasureTheory.vadd_set_ae_eq c).mpr R.presentation_correct
          have hBK : B =ᵐ[MeasureTheory.volume] c' +ᵥ R.region.openCarrier := by
            exact (MeasureTheory.vadd_set_ae_eq c').mpr R.presentation_correct
          have hvol := ae_inter_measure_ne_zero_of_open_subset hUopen ⟨z, hz⟩
            hUA hUB hAK hBK
          have hc : c ∈ D.centres := by
            rw [orbit.presents]
            exact ⟨i.1, probeCenteredInteger i.2.1, probeCenteredInteger i.2.2, rfl⟩
          have hc' : c' ∈ D.centres := by
            rw [orbit.presents]
            exact ⟨i'.1, probeCenteredInteger i'.2.1, probeCenteredInteger i'.2.2, rfl⟩
          have hd := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
            R.region D.centres).mp D.tiles.2.1 hc hc' hcc
          obtain ⟨w, hw⟩ := MeasureTheory.nonempty_of_measure_ne_zero hvol
          exact Set.disjoint_left.1 hd hw.1 hw.2
      finite_coverage := by
        intro p hpBox
        let centre : ProbeLatticeIndex orbit.representativeCount firstBound secondBound →
            Tiling.Plane := fun i ↦ orbit.representative i.1 +
          probeCenteredInteger i.2.1 • orbit.firstPeriod +
          probeCenteredInteger i.2.2 • orbit.secondPeriod
        let closedCell (i : ProbeLatticeIndex orbit.representativeCount
            firstBound secondBound) (e : Fin C.cellCount) : Set Tiling.Plane :=
          {z | (centre i).re + (R.vertex (C.leftVertex e)).re ≤ z.re ∧
            z.re ≤ (centre i).re + (R.vertex (C.rightVertex e)).re ∧
            (centre i).im + (R.vertex (C.bottomVertex e)).im ≤ z.im ∧
            z.im ≤ (centre i).im + (R.vertex (C.topVertex e)).im}
        let checked : Set Tiling.Plane :=
          ⋃ i : {i // i ∈ probeLatticeIndexList orbit.representativeCount firstBound secondBound},
            ⋃ e : Fin C.cellCount, closedCell i.1 e
        have hcheckedClosed : IsClosed checked := by
          apply isClosed_iUnion_of_finite
          intro i
          apply isClosed_iUnion_of_finite
          intro e
          change IsClosed {z : Tiling.Plane |
            (centre i.1).re + (R.vertex (C.leftVertex e)).re ≤ z.re ∧
            z.re ≤ (centre i.1).re + (R.vertex (C.rightVertex e)).re ∧
            (centre i.1).im + (R.vertex (C.bottomVertex e)).im ≤ z.im ∧
            z.im ≤ (centre i.1).im + (R.vertex (C.topVertex e)).im}
          apply IsClosed.inter
          · change IsClosed (Complex.re ⁻¹' Set.Ici
              ((centre i.1).re + (R.vertex (C.leftVertex e)).re))
            exact isClosed_Ici.preimage Complex.continuous_re
          · apply IsClosed.inter
            · change IsClosed (Complex.re ⁻¹' Set.Iic
                ((centre i.1).re + (R.vertex (C.rightVertex e)).re))
              exact isClosed_Iic.preimage Complex.continuous_re
            · apply IsClosed.inter
              · change IsClosed (Complex.im ⁻¹' Set.Ici
                  ((centre i.1).im + (R.vertex (C.bottomVertex e)).im))
                exact isClosed_Ici.preimage Complex.continuous_im
              · change IsClosed (Complex.im ⁻¹' Set.Iic
                  ((centre i.1).im + (R.vertex (C.topVertex e)).im))
                exact isClosed_Iic.preimage Complex.continuous_im
        by_contra hcoverage
        push Not at hcoverage
        have hpNot : p ∉ checked := by
          intro hp
          rcases Set.mem_iUnion.mp hp with ⟨i, hp⟩
          rcases Set.mem_iUnion.mp hp with ⟨e, hpe⟩
          have hiPrivate : i.1 ∈
              probeLatticeIndexList orbit.representativeCount firstBound secondBound := i.2
          exact hcoverage i.1 (by
            change i.1 ∈
              ((List.ofFn fun r : Fin orbit.representativeCount => r).flatMap fun r =>
                (List.ofFn fun n : Fin (2 * firstBound + 1) => n).flatMap fun n =>
                  List.ofFn fun m : Fin (2 * secondBound + 1) => (r, n, m)).filter
                    (fun j => decide ((probeCenteredInteger j.2.1).natAbs < firstBound ∧
                      (probeCenteredInteger j.2.2).natAbs < secondBound))
            simpa [probeLatticeIndexList] using hiPrivate) e (by
              change closedCell i.1 e p
              exact hpe)
        let box : Set Tiling.Plane :=
          {z | -Hx < z.re ∧ z.re < Hx ∧ -Hy < z.im ∧ z.im < Hy}
        let U := box ∩ checkedᶜ
        have hUopen : IsOpen U := by
          exact ((isOpen_lt continuous_const Complex.continuous_re).inter
            ((isOpen_lt Complex.continuous_re continuous_const).inter
              ((isOpen_lt continuous_const Complex.continuous_im).inter
                (isOpen_lt Complex.continuous_im continuous_const)))).inter
            hcheckedClosed.isOpen_compl
        have hpU : p ∈ U := by
          refine ⟨?_, hpNot⟩
          change -Hx < p.re ∧ p.re < Hx ∧ -Hy < p.im ∧ p.im < Hy
          exact hpBox
        have hUne : U.Nonempty := ⟨p, hpU⟩
        have hAE : ∀ᵐ q ∂MeasureTheory.volume,
            (q ∈ Set.univ ↔ ∃ s : D.centres,
              q ∈ ((s : Tiling.Plane) +ᵥ R.region.openCarrier)) := D.tiles.2.2
        let cells : Set Tiling.Plane := ⋃ e : Fin C.cellCount,
          {z | (R.vertex (C.leftVertex e)).re < z.re ∧
            z.re < (R.vertex (C.rightVertex e)).re ∧
            (R.vertex (C.bottomVertex e)).im < z.im ∧
            z.im < (R.vertex (C.topVertex e)).im}
        let _ : Countable D.centres := D.tiles.1.to_subtype
        have hPresentationAE : ∀ᵐ q ∂MeasureTheory.volume, ∀ s : D.centres,
            (q ∈ ((s : Tiling.Plane) +ᵥ cells) ↔
              q ∈ ((s : Tiling.Plane) +ᵥ R.region.openCarrier)) := by
          rw [eventually_countable_forall]
          intro s
          have hbase : cells =ᵐ[MeasureTheory.volume] R.region.openCarrier := by
            simpa [cells] using R.presentation_correct
          exact ((MeasureTheory.vadd_set_ae_eq (s : Tiling.Plane)).mpr hbase).mem_iff
        obtain ⟨q, hqU, hqCover, hqPresentation⟩ :=
          exists_mem_open_of_ae hUopen hUne (hAE.and hPresentationAE)
        obtain ⟨s, hqs⟩ := hqCover.mp (Set.mem_univ q)
        have hqCells : q ∈ (s : Tiling.Plane) +ᵥ cells :=
          (hqPresentation s).mpr hqs
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hqCells
        rcases Set.mem_iUnion.mp hqCells with ⟨e, hqe⟩
        obtain ⟨r, n, m, hs⟩ := (Set.ext_iff.mp orbit.presents s.1).mp s.2
        have hcell :
            s.1.re + (R.vertex (C.leftVertex e)).re < q.re ∧
              q.re < s.1.re + (R.vertex (C.rightVertex e)).re ∧
              s.1.im + (R.vertex (C.bottomVertex e)).im < q.im ∧
              q.im < s.1.im + (R.vertex (C.topVertex e)).im := by
          change (R.vertex (C.leftVertex e)).re < (-s.1 + q).re ∧
            (-s.1 + q).re < (R.vertex (C.rightVertex e)).re ∧
            (R.vertex (C.bottomVertex e)).im < (-s.1 + q).im ∧
            (-s.1 + q).im < (R.vertex (C.topVertex e)).im at hqe
          simp only [Complex.add_re, Complex.neg_re, Complex.add_im, Complex.neg_im] at hqe
          exact ⟨by linarith [hqe.1], by linarith [hqe.2.1],
            by linarith [hqe.2.2.1], by linarith [hqe.2.2.2]⟩
        have hqbox : -Hx < q.re ∧ q.re < Hx ∧ -Hy < q.im ∧ q.im < Hy := by
          exact hqU.1
        let w : Tiling.Plane := n • orbit.firstPeriod + m • orbit.secondPeriod
        have hwre : w.re = (n : Real) * orbit.firstPeriod.re +
            (m : Real) * orbit.secondPeriod.re := by
          simp [w, Complex.add_re]
        have hwim : w.im = (n : Real) * orbit.firstPeriod.im +
            (m : Real) * orbit.secondPeriod.im := by
          simp [w, Complex.add_im]
        have hs' : s.1 = orbit.representative r + w := by
          rw [hs]
          simp only [w, add_assoc]
        rw [hs'] at hcell
        have hwxUpper : w.re < 2 * Hx +
            |(R.vertex (C.leftVertex e)).re - (R.vertex C.originVertex).re| := by
          have hrep := (hRepresentative r).1
          have hrepLower : -Hx ≤ (orbit.representative r).re := (abs_le.mp hrep).1
          have habs : -(R.vertex (C.leftVertex e)).re ≤
              |(R.vertex (C.leftVertex e)).re| := neg_le_abs _
          have horigin : (R.vertex C.originVertex).re = 0 := by
            simpa using congrArg Complex.re R.origin_eq_zero
          simp only [Complex.add_re] at hcell
          rw [horigin, sub_zero]
          linarith [hcell.1, hqbox.2.1]
        have hwxLower : -(2 * Hx +
            |(R.vertex (C.rightVertex e)).re - (R.vertex C.originVertex).re|) < w.re := by
          have hrep := (hRepresentative r).1
          have hrepUpper : (orbit.representative r).re ≤ Hx :=
            le_trans (le_abs_self _) hrep
          have habs : (R.vertex (C.rightVertex e)).re ≤
              |(R.vertex (C.rightVertex e)).re| := le_abs_self _
          have horigin : (R.vertex C.originVertex).re = 0 := by
            simpa using congrArg Complex.re R.origin_eq_zero
          simp only [Complex.add_re] at hcell
          rw [horigin, sub_zero]
          linarith [hcell.2.1, hqbox.1]
        have hwyUpper : w.im < 2 * Hy +
            |(R.vertex (C.bottomVertex e)).im - (R.vertex C.originVertex).im| := by
          have hrep := (hRepresentative r).2
          have hrepLower : -Hy ≤ (orbit.representative r).im := (abs_le.mp hrep).1
          have habs : -(R.vertex (C.bottomVertex e)).im ≤
              |(R.vertex (C.bottomVertex e)).im| := neg_le_abs _
          have horigin : (R.vertex C.originVertex).im = 0 := by
            simpa using congrArg Complex.im R.origin_eq_zero
          simp only [Complex.add_im] at hcell
          rw [horigin, sub_zero]
          linarith [hcell.2.2.1, hqbox.2.2.2]
        have hwyLower : -(2 * Hy +
            |(R.vertex (C.topVertex e)).im - (R.vertex C.originVertex).im|) < w.im := by
          have hrep := (hRepresentative r).2
          have hrepUpper : (orbit.representative r).im ≤ Hy :=
            le_trans (le_abs_self _) hrep
          have habs : (R.vertex (C.topVertex e)).im ≤
              |(R.vertex (C.topVertex e)).im| := le_abs_self _
          have horigin : (R.vertex C.originVertex).im = 0 := by
            simpa using congrArg Complex.im R.origin_eq_zero
          simp only [Complex.add_im] at hcell
          rw [horigin, sub_zero]
          linarith [hcell.2.2.2, hqbox.2.2.1]
        have hidentx : w.re =
            ((n : Real) * orbit.rationalSeparator + (m : Real)) *
                orbit.secondPeriod.re +
              (n : Real) * (orbit.firstPeriod.re -
                orbit.rationalSeparator * orbit.secondPeriod.re) := by
          rw [hwre]
          ring
        have hidenty : w.im =
            ((n : Real) * orbit.rationalSeparator + (m : Real)) *
                orbit.secondPeriod.im -
              (n : Real) * (orbit.rationalSeparator * orbit.secondPeriod.im -
                orbit.firstPeriod.im) := by
          rw [hwim]
          ring
        have hnUpper : (n : Real) < (firstBound : Real) := by
          by_contra hn
          have hnge : (firstBound : Real) ≤ (n : Real) := le_of_not_gt hn
          by_cases hh : 0 ≤ (n : Real) * orbit.rationalSeparator + (m : Real)
          · have hna : (firstBound : Real) *
                (orbit.firstPeriod.re - orbit.rationalSeparator * orbit.secondPeriod.re) ≤
              (n : Real) *
                (orbit.firstPeriod.re - orbit.rationalSeparator * orbit.secondPeriod.re) :=
              mul_le_mul_of_nonneg_right hnge
                (le_of_lt orbit.separated_first_pos)
            have hhv : 0 ≤ ((n : Real) * orbit.rationalSeparator + (m : Real)) *
                orbit.secondPeriod.re := mul_nonneg hh
              (le_of_lt orbit.second_first_pos)
            linarith [hFirstX (C.leftVertex e) C.originVertex, hwxUpper,
              hidentx, hna, hhv]
          · have hh' : (n : Real) * orbit.rationalSeparator + (m : Real) ≤ 0 :=
              (lt_of_not_ge hh).le
            have hnb : (firstBound : Real) *
                (orbit.rationalSeparator * orbit.secondPeriod.im - orbit.firstPeriod.im) ≤
              (n : Real) *
                (orbit.rationalSeparator * orbit.secondPeriod.im - orbit.firstPeriod.im) :=
              mul_le_mul_of_nonneg_right hnge
                (le_of_lt orbit.separated_second_pos)
            have hhv : ((n : Real) * orbit.rationalSeparator + (m : Real)) *
                orbit.secondPeriod.im ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hh'
              (le_of_lt orbit.second_second_pos)
            linarith [hFirstY (C.topVertex e) C.originVertex, hwyLower,
              hidenty, hnb, hhv]
        have hnLower : -(firstBound : Real) < (n : Real) := by
          by_contra hn
          have hnle : (n : Real) ≤ -(firstBound : Real) := le_of_not_gt hn
          by_cases hh : 0 ≤ (n : Real) * orbit.rationalSeparator + (m : Real)
          · have hnb : (firstBound : Real) *
                (orbit.rationalSeparator * orbit.secondPeriod.im - orbit.firstPeriod.im) ≤
              -(n : Real) *
                (orbit.rationalSeparator * orbit.secondPeriod.im - orbit.firstPeriod.im) := by
              apply mul_le_mul_of_nonneg_right _ orbit.separated_second_pos.le
              linarith
            have hhv : 0 ≤ ((n : Real) * orbit.rationalSeparator + (m : Real)) *
                orbit.secondPeriod.im := mul_nonneg hh orbit.second_second_pos.le
            linarith [hFirstY (C.bottomVertex e) C.originVertex, hwyUpper,
              hidenty, hnb, hhv]
          · have hh' : (n : Real) * orbit.rationalSeparator + (m : Real) ≤ 0 :=
              (lt_of_not_ge hh).le
            have hna : (firstBound : Real) *
                (orbit.firstPeriod.re - orbit.rationalSeparator * orbit.secondPeriod.re) ≤
              -(n : Real) *
                (orbit.firstPeriod.re - orbit.rationalSeparator * orbit.secondPeriod.re) := by
              apply mul_le_mul_of_nonneg_right _ orbit.separated_first_pos.le
              linarith
            have hhv : ((n : Real) * orbit.rationalSeparator + (m : Real)) *
                orbit.secondPeriod.re ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg hh' orbit.second_first_pos.le
            linarith [hFirstX (C.rightVertex e) C.originVertex, hwxLower,
              hidentx, hna, hhv]
        have hnUpperInt : n < (firstBound : Int) := by exact_mod_cast hnUpper
        have hnLowerInt : -(firstBound : Int) < n := by exact_mod_cast hnLower
        have hnNat : n.natAbs < firstBound := by omega
        have hnAbs : |(n : Real)| ≤ (firstBound : Real) :=
          abs_le.mpr ⟨hnLower.le, hnUpper.le⟩
        have huAbs : |orbit.firstPeriod.re| ≤ Ux := by
          apply abs_le.mpr
          exact ⟨by linarith [hNegUx], hUx⟩
        have hnuAbs : |(n : Real) * orbit.firstPeriod.re| ≤
            (firstBound : Real) * Ux := by
          rw [abs_mul]
          calc
            |(n : Real)| * |orbit.firstPeriod.re| ≤
                (firstBound : Real) * |orbit.firstPeriod.re| :=
              mul_le_mul_of_nonneg_right hnAbs (abs_nonneg _)
            _ ≤ (firstBound : Real) * Ux :=
              mul_le_mul_of_nonneg_left huAbs (Nat.cast_nonneg _)
        have hmvUpper : (m : Real) * orbit.secondPeriod.re <
            (secondBound : Real) * orbit.secondPeriod.re := by
          have hsecond := hSecond (C.leftVertex e) C.originVertex
          have hmvre : (m : Real) * orbit.secondPeriod.re =
              w.re - (n : Real) * orbit.firstPeriod.re := by
            rw [hwre]
            ring
          rw [hmvre]
          have hle : w.re - (n : Real) * orbit.firstPeriod.re ≤
              w.re + |(n : Real) * orbit.firstPeriod.re| := by
            linarith [neg_le_abs ((n : Real) * orbit.firstPeriod.re)]
          linarith [hsecond, hnuAbs, hwxUpper, hle]
        have hmvLower : -(secondBound : Real) * orbit.secondPeriod.re <
            (m : Real) * orbit.secondPeriod.re := by
          have hsecond := hSecond (C.rightVertex e) C.originVertex
          have hmvre : (m : Real) * orbit.secondPeriod.re =
              w.re - (n : Real) * orbit.firstPeriod.re := by
            rw [hwre]
            ring
          rw [hmvre]
          have hle : -|(n : Real) * orbit.firstPeriod.re| ≤
              -(n : Real) * orbit.firstPeriod.re := by
            linarith [le_abs_self ((n : Real) * orbit.firstPeriod.re)]
          linarith [hsecond, hnuAbs, hwxLower, hle]
        have hmUpper : (m : Real) < (secondBound : Real) :=
          lt_of_mul_lt_mul_right hmvUpper orbit.second_first_pos.le
        have hmLower : -(secondBound : Real) < (m : Real) :=
          lt_of_mul_lt_mul_right hmvLower orbit.second_first_pos.le
        have hmUpperInt : m < (secondBound : Int) := by exact_mod_cast hmUpper
        have hmLowerInt : -(secondBound : Int) < m := by exact_mod_cast hmLower
        have hmNat : m.natAbs < secondBound := by omega
        obtain ⟨i, hi, hir, hin, him⟩ :=
          probeLatticeIndex_complete r n m hnNat hmNat
        have hiList : i ∈ probeLatticeIndexList orbit.representativeCount
            firstBound secondBound := by
          rw [probeLatticeIndexList, List.mem_filter]
          refine ⟨?_, ?_⟩
          · rcases i with ⟨r', n', m'⟩
            rw [List.mem_flatMap]
            refine ⟨r', List.mem_ofFn.mpr ⟨r', rfl⟩, ?_⟩
            rw [List.mem_flatMap]
            refine ⟨n', List.mem_ofFn.mpr ⟨n', rfl⟩, ?_⟩
            exact List.mem_ofFn.mpr ⟨m', rfl⟩
          · simpa [mem_probeLatticeIndices_iff] using
              (mem_probeLatticeIndices_iff i).mp hi
        have hcentre : centre i = orbit.representative r + w := by
          dsimp [centre]
          rw [hir, hin, him]
          simp only [w, add_assoc]
        have hqClosed : q ∈ closedCell i e := by
          change (centre i).re + (R.vertex (C.leftVertex e)).re ≤ q.re ∧
            q.re ≤ (centre i).re + (R.vertex (C.rightVertex e)).re ∧
            (centre i).im + (R.vertex (C.bottomVertex e)).im ≤ q.im ∧
            q.im ≤ (centre i).im + (R.vertex (C.topVertex e)).im
          rw [hcentre]
          exact ⟨hcell.1.le, hcell.2.1.le, hcell.2.2.1.le, hcell.2.2.2.le⟩
        apply hqU.2
        apply Set.mem_iUnion.mpr
        refine ⟨⟨i, hiList⟩, ?_⟩
        exact Set.mem_iUnion.mpr ⟨e, hqClosed⟩
    }

private theorem lattice_boundsAndChecks :
    ∀ {C : RegionCode} (R : Realization C)
        (D : PeriodicReplacement R.region Set.univ),
      ∃ orbit : FiniteLatticeOrbitPresentation D, ∃ firstBound secondBound : Nat,
      ∃ X : LatticeRawParameters
        (latticeRawCode orbit.rationalSeparator orbit.representativeCount
          firstBound secondBound),
        let code := latticeRawCode orbit.rationalSeparator orbit.representativeCount
          firstBound secondBound
        latticeCentreSet code X = D.centres ∧ code.wellFormed = true ∧
          LatticeChecks R code X := by
  intro C R D
  obtain ⟨orbit⟩ := lattice_rationallySeparatedPeriods D
  obtain ⟨firstBound, secondBound, X, hX⟩ :=
    latticeBoundsAndChecks_ofOrbit R D orbit
  exact ⟨orbit, firstBound, secondBound, X, hX⟩

theorem normalForm_rawChecks :
    ∀ {C : RegionCode} (R : Realization C), PeriodicTilingNormalForm R.region →
      ∃ code : RawPositiveCode, code.wellFormed = true ∧
        match code with
        | .triangular c => ∃ X : TriangularRawParameters c, TriangularChecks R c X
        | .lattice c => ∃ X : LatticeRawParameters c, LatticeChecks R c X := by
  intro C R normalForm
  cases normalForm with
  | orientedSlabs D =>
      obtain ⟨base, orbit, radius, X, hwellFormed, hchecks⟩ :=
        slabCertificate_rawChecks R D
      exact ⟨.triangular (slabRawCode D.orientation base.intervalCount
        orbit.representativeCount radius), hwellFormed, X, hchecks⟩
  | wholePlaneLattice D =>
      obtain ⟨orbit, firstBound, secondBound, X, _hcentres, hwellFormed, hchecks⟩ :=
        lattice_boundsAndChecks R D
      exact ⟨.lattice (latticeRawCode orbit.rationalSeparator
        orbit.representativeCount firstBound secondBound), hwellFormed, X, hchecks⟩

theorem positiveStage_complete :
    ∀ {C : RegionCode} (R : Realization C) (O : CorrectOracle C R),
      realizationPlaneTileable R → ∃ n, verifyPositiveStage C O.toOracle n = true := by
  intro C R O htileable
  obtain ⟨normalForm⟩ := exists_periodicTilingNormalForm R.region htileable
  obtain ⟨code, hwellFormed, hchecks⟩ := normalForm_rawChecks R normalForm
  have hverify : verifyPositive C O.toOracle code = true :=
    (verifyPositive_correct R O code).mpr ⟨hwellFormed, hchecks⟩
  obtain ⟨n, hn⟩ := wellFormedPositiveStage_complete code hwellFormed
  exact ⟨n, by rw [verifyPositiveStage, hn]; exact hverify⟩

end Tiling.AxisParallel.Terminal.PositiveCertificateCompleteness
