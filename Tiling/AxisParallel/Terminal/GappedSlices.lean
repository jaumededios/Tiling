import Tiling.AxisParallel.Terminal.RationalFinerStructure
import Tiling.AxisParallel.OneDimensional.PeriodicPointEnumeration
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Gapped rational slices

Large gaps in rational slice orbits force two independent periods on the
union of all gapped slice centres.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped BigOperators Pointwise

noncomputable section

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel
open Tiling.AxisParallel.Terminal
open Tiling.AxisParallel.OneDimensional

private def finiteTranslateMultiplicity
    (Omega : Set Tiling.Plane) (A : Finset Tiling.Plane)
    (x : Tiling.Plane) : ℝ :=
  ∑ a ∈ A, Omega.indicator (fun _ ↦ (1 : ℝ)) (x - a)


private def ell (t : ℝ) (z : Tiling.Plane) : ℝ := z.re + t * z.im

private def upperCap (Omega : Set Tiling.Plane) (t : ℝ) (r : ℝ) : Set Tiling.Plane :=
  Omega ∩ {y | r < ell t y}

private theorem finiteTranslationalCancellation :
    ∀ {Omega : Set Tiling.Plane}, Bornology.IsBounded Omega →
      MeasurableSet Omega → 0 < volume Omega →
      ∀ (A B : Finset Tiling.Plane),
        finiteTranslateMultiplicity Omega A =ᵐ[volume]
          finiteTranslateMultiplicity Omega B →
        A = B := by
  classical
  intro Omega hbounded hmeas hpositive A B hEq
  let A0 := A \ B
  let B0 := B \ A
  let C := A0 ∪ B0
  let I := A ∩ B
  let f : Tiling.Plane → ℝ := fun x ↦ Omega.indicator (fun _ ↦ (1 : ℝ)) x
  have hcancel : finiteTranslateMultiplicity Omega A0 =ᵐ[volume]
      finiteTranslateMultiplicity Omega B0 := by
    filter_upwards [hEq] with x hx
    have hA := Finset.sum_sdiff (f := fun a ↦ f (x - a)) (s₁ := I) (s₂ := A)
      (by
        intro z hz
        simp only [I, Finset.mem_inter] at hz
        exact hz.1)
    have hB := Finset.sum_sdiff (f := fun a ↦ f (x - a)) (s₁ := I) (s₂ := B)
      (by
        intro z hz
        simp only [I, Finset.mem_inter] at hz
        exact hz.2)
    have hA' : (∑ a ∈ A0, f (x - a)) + ∑ a ∈ I, f (x - a) =
        ∑ a ∈ A, f (x - a) := by simpa [A0, I] using hA
    have hB' : (∑ a ∈ B0, f (x - a)) + ∑ a ∈ I, f (x - a) =
        ∑ a ∈ B, f (x - a) := by simpa [B0, I] using hB
    have hsum : (∑ a ∈ A0, f (x - a)) = ∑ a ∈ B0, f (x - a) := by
      change (∑ a ∈ A, f (x - a)) = ∑ a ∈ B, f (x - a) at hx
      linarith [hx, hA', hB']
    simpa [finiteTranslateMultiplicity, f] using hsum
  by_cases hC : C = ∅
  · have hA0 : A0 = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro hne
      obtain ⟨a, ha⟩ := hne
      have haC : a ∈ C := by simp [C, A0, ha]
      have hne : a ∉ (∅ : Finset Tiling.Plane) := by simp
      exact hne (hC ▸ haC)
    have hB0 : B0 = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro hne
      obtain ⟨b, hb⟩ := hne
      have hbC : b ∈ C := by simp [C, B0, hb]
      have hne : b ∉ (∅ : Finset Tiling.Plane) := by simp
      exact hne (hC ▸ hbC)
    apply Finset.ext
    intro x
    constructor
    · intro hx
      by_contra hxB
      have : x ∈ A0 := Finset.mem_sdiff.mpr ⟨hx, hxB⟩
      have hne : x ∉ (∅ : Finset Tiling.Plane) := by simp
      exact hne (hA0 ▸ this)
    · intro hx
      by_contra hxA
      have : x ∈ B0 := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
      have hne : x ∉ (∅ : Finset Tiling.Plane) := by simp
      exact hne (hB0 ▸ this)
  · have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hC
    let bad : Finset ℝ :=
      (C.product C).biUnion (fun p ↦
        if p.1.im = p.2.im then ∅
        else {(p.1.re - p.2.re) / (p.2.im - p.1.im)})
    let t : ℝ := if hb : bad.Nonempty then bad.max' hb + 1 else 0
    have htbad : ∀ q ∈ bad, q < t := by
      intro q hq
      by_cases hb : bad.Nonempty
      · dsimp [t]
        rw [dif_pos hb]
        exact lt_of_le_of_lt (bad.le_max' q hq) (lt_add_one _)
      · exact False.elim (hb ⟨q, hq⟩)
    have hell_inj : ∀ {c d : Tiling.Plane}, c ∈ C → d ∈ C → ell t c = ell t d → c = d := by
      intro c d hc hd heq
      by_contra hne
      have hpair : (c, d) ∈ C.product C := Finset.mem_product.mpr ⟨hc, hd⟩
      by_cases him : c.im = d.im
      · have hre : c.re = d.re := by
          dsimp [ell] at heq
          rw [him] at heq
          linarith
        exact hne (Complex.ext hre him)
      · have hbad : t = (c.re - d.re) / (d.im - c.im) := by
          dsimp [ell] at heq
          apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm him))).2
          linarith
        have : (c.re - d.re) / (d.im - c.im) ∈ bad := by
          rw [Finset.mem_biUnion]
          exact ⟨(c, d), hpair, by simp [him]⟩
        linarith [htbad _ this]
    obtain ⟨cStar, hcStar, hmax⟩ := C.exists_max_image (ell t) hCne
    have hstar_unique : ∀ {c : Tiling.Plane}, c ∈ C → ell t c = ell t cStar → c = cStar := by
      intro c hc heq
      exact hell_inj hc hcStar heq
    have hdisj : Disjoint A0 B0 := by
      rw [Finset.disjoint_left]
      intro c hcA hcB
      exact (Finset.mem_sdiff.mp hcA).2 (Finset.mem_sdiff.mp hcB).1
    have hstar_side : cStar ∈ A0 ∨ cStar ∈ B0 := by simpa [C] using hcStar
    let P : Finset Tiling.Plane := if cStar ∈ A0 then A0 else B0
    let Q : Finset Tiling.Plane := if cStar ∈ A0 then B0 else A0
    have hcStarP : cStar ∈ P := by
      simp only [P]
      split <;> simp_all
    have hPQ : finiteTranslateMultiplicity Omega P =ᵐ[volume]
        finiteTranslateMultiplicity Omega Q := by
      by_cases hp : cStar ∈ A0
      · simpa [P, Q, hp] using hcancel
      · simpa [P, Q, hp] using hcancel.symm
    have hPempty : P = ∅ := by
      by_contra hPne
      have hPne' : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hPne
      let D := C.erase cStar
      let gaps : Finset ℝ := D.image (fun c ↦ ell t cStar - ell t c)
      have hDgap : ∀ c ∈ D, 0 < ell t cStar - ell t c := by
        intro c hc
        have hcC : c ∈ C := Finset.mem_of_mem_erase hc
        have hcle : ell t c ≤ ell t cStar := hmax c hcC
        have hcne : c ≠ cStar := Finset.mem_erase.mp hc |>.1
        have hneq : ell t c ≠ ell t cStar := by
          intro heq
          exact hcne (hstar_unique hcC heq)
        exact sub_pos.mpr (lt_of_le_of_ne hcle hneq)
      let delta : ℝ := if hg : gaps.Nonempty then gaps.min' hg else 1
      have hdelta : 0 < delta := by
        by_cases hg : gaps.Nonempty
        · simp only [delta, dif_pos hg]
          have hq : gaps.min' hg ∈ gaps := Finset.min'_mem gaps hg
          rw [Finset.mem_image] at hq
          obtain ⟨c, hcD, heq⟩ := hq
          rw [← heq]
          exact hDgap c hcD
        · simp [delta, hg]
      have hgap : ∀ c ∈ D, delta ≤ ell t cStar - ell t c := by
        intro c hc
        by_cases hg : gaps.Nonempty
        · simp only [delta, dif_pos hg]
          exact Finset.min'_le gaps _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
        · exact False.elim (hg ⟨ell t cStar - ell t c, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩)
      let E : Set ℝ := {r | 0 < volume (upperCap Omega t r)}
      have hEllMeas : Measurable (ell t) := by
        change Measurable (fun z : Tiling.Plane ↦ z.re + t * z.im)
        exact Complex.measurable_re.add
          ((measurable_const : Measurable (fun _ : Tiling.Plane ↦ t)).mul
            Complex.measurable_im)
      have hEnon : E.Nonempty := by
        by_contra hne
        have hzero : volume (⋃ n : ℕ, upperCap Omega t (-(n : ℝ))) = 0 := by
          apply measure_iUnion_null
          intro n
          apply bot_unique
          have hn : ¬ 0 < volume (upperCap Omega t (-(n : ℝ))) := by
            intro h
            exact hne ⟨-(n : ℝ), h⟩
          exact le_of_eq (bot_unique (not_lt.mp hn))
        have hsub : Omega ⊆ ⋃ n : ℕ, upperCap Omega t (-(n : ℝ)) := by
          intro y hy
          obtain ⟨n, hn⟩ := exists_nat_gt (-ell t y)
          refine mem_iUnion.mpr ⟨n, hy, ?_⟩
          change -(n : ℝ) < ell t y
          linarith
        rw [measure_mono_null hsub hzero] at hpositive
        exact (lt_irrefl _ hpositive)
      have hEbd : BddAbove E := by
        obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : Tiling.Plane)
        refine ⟨(1 + |t|) * R, ?_⟩
        intro r hr
        by_contra hnot
        have hlt : (1 + |t|) * R < r := lt_of_not_ge hnot
        have hcapempty : upperCap Omega t r = ∅ := by
          ext y
          constructor
          · intro hy
            have hyball : y ∈ Metric.closedBall (0 : Tiling.Plane) R := hR hy.1
            have hynorm : ‖y‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hyball
            have hEll : ell t y ≤ (1 + |t|) * R := by
              dsimp [ell]
              calc
                y.re + t * y.im ≤ |y.re| + |t * y.im| := by
                  gcongr <;> exact le_abs_self _
                _ = |y.re| + |t| * |y.im| := by rw [abs_mul]
                _ ≤ ‖y‖ + |t| * ‖y‖ := by
                  exact add_le_add (Complex.abs_re_le_norm y)
                    (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm y) (abs_nonneg t))
                _ = (1 + |t|) * ‖y‖ := by ring
                _ ≤ (1 + |t|) * R := by gcongr
            have hygt : r < ell t y := hy.2
            linarith
          · intro hy
            simp at hy
        have hrpos : 0 < volume (upperCap Omega t r) := by simpa [E] using hr
        rw [hcapempty] at hrpos
        simp at hrpos
      let M : ℝ := sSup E
      have hMd : M - delta < M := sub_lt_self _ hdelta
      obtain ⟨r, hrE, hrM⟩ := (lt_csSup_iff hEbd hEnon).mp hMd
      have hMr : M ≥ r := le_csSup hEbd hrE
      have hMrδ : M < r + delta := by linarith
      have hrδnot : r + delta ∉ E := notMem_of_csSup_lt hMrδ hEbd
      have hnullcap : volume (upperCap Omega t (r + delta)) = 0 := by
        apply bot_unique
        exact not_lt.mp (by simpa [E] using hrδnot)
      let N : Set Tiling.Plane := {x |
        finiteTranslateMultiplicity Omega P x ≠ finiteTranslateMultiplicity Omega Q x}
      have hNnull : volume N = 0 := by
        simpa [N] using (ae_iff.mp hPQ)
      let Ncaps : Set Tiling.Plane :=
        ⋃ c : D, (fun y ↦ (c : Tiling.Plane) + y) ''
          upperCap Omega t (r + delta)
      have hNcapsnull : volume Ncaps = 0 := by
        apply measure_iUnion_null
        intro c
        rw [Set.image_add_left]
        exact (measurePreserving_add_left volume (-(c : Tiling.Plane))).quasiMeasurePreserving
          |>.preimage_null hnullcap
      let Nbad := N ∪ Ncaps
      have hNbadnull : volume Nbad = 0 :=
        measure_union_null hNnull hNcapsnull
      have hcapmeas : MeasurableSet (upperCap Omega t r) := by
        exact hmeas.inter (measurableSet_Ioi.preimage hEllMeas)
      have hSpos : 0 < volume ((fun y ↦ cStar + y) '' upperCap Omega t r) := by
        rw [Set.image_add_left, measure_preimage_add volume (-cStar)]
        simpa [E] using hrE
      have hSnot : ((fun y ↦ cStar + y) '' upperCap Omega t r \ Nbad).Nonempty := by
        by_contra hempty
        have hsub : (fun y ↦ cStar + y) '' upperCap Omega t r ⊆ Nbad := by
          intro x hx
          by_contra hxN
          exact hempty ⟨x, hx, hxN⟩
        rw [measure_mono_null hsub hNbadnull] at hSpos
        exact (lt_irrefl _ hSpos)
      obtain ⟨x, hxS, hxNbad⟩ := hSnot
      obtain ⟨y, hycap, hxy⟩ := hxS
      have hyOmega : y ∈ Omega := hycap.1
      have hxstar : x - cStar ∈ Omega := by
        rw [← hxy]
        simpa [sub_eq_add_neg, add_assoc] using hyOmega
      have hPC : ∀ c ∈ P, c ∈ C := by
        intro c hc
        by_cases hp : cStar ∈ A0
        · exact Finset.mem_union_left _ (by simpa [P, hp] using hc)
        · exact Finset.mem_union_right _ (by simpa [P, hp] using hc)
      have hQC : ∀ c ∈ Q, c ∈ C := by
        intro c hc
        by_cases hp : cStar ∈ A0
        · exact Finset.mem_union_right _ (by simpa [Q, hp] using hc)
        · exact Finset.mem_union_left _ (by simpa [Q, hp] using hc)
      have hPother : ∀ c ∈ P, c ≠ cStar → x - c ∉ Omega := by
        intro c hcP hcne hmem
        have hcD : c ∈ D := Finset.mem_erase.mpr ⟨hcne, hPC c hcP⟩
        have hgapc := hgap c hcD
        have hlin : r + delta < ell t (x - c) := by
          have hcalc : ell t (x - c) = ell t y + ell t cStar - ell t c := by
            rw [← hxy]
            dsimp [ell]
            ring
          rw [hcalc]
          have hygt : r < ell t y := hycap.2
          linarith
        have hxcap : x ∈ (fun z ↦ c + z) '' upperCap Omega t (r + delta) := by
          refine ⟨x - c, ⟨hmem, hlin⟩, ?_⟩
          simp [sub_eq_add_neg, add_left_comm]
        have : x ∈ Ncaps := by
          refine mem_iUnion.mpr ⟨⟨c, hcD⟩, hxcap⟩
        exact hxNbad (Or.inr this)
      have hQnotstar : ∀ c ∈ Q, c ≠ cStar := by
        intro c hc hceq
        have hPQdisj : Disjoint P Q := by
          by_cases hp : cStar ∈ A0
          · simpa [P, Q, hp] using hdisj
          · simpa [P, Q, hp] using hdisj.symm
        exact (Finset.disjoint_left.mp hPQdisj) hcStarP (hceq ▸ hc)
      have hQother : ∀ c ∈ Q, x - c ∉ Omega := by
        intro c hc hmem
        have hcD : c ∈ D := Finset.mem_erase.mpr ⟨hQnotstar c hc, hQC c hc⟩
        have hgapc := hgap c hcD
        have hlin : r + delta < ell t (x - c) := by
          have hcalc : ell t (x - c) = ell t y + ell t cStar - ell t c := by
            rw [← hxy]
            dsimp [ell]
            ring
          rw [hcalc]
          have hygt : r < ell t y := hycap.2
          linarith
        have hxcap : x ∈ (fun z ↦ c + z) '' upperCap Omega t (r + delta) := by
          refine ⟨x - c, ⟨hmem, hlin⟩, ?_⟩
          simp [sub_eq_add_neg, add_left_comm]
        have hxc : x ∈ Ncaps := mem_iUnion.mpr ⟨⟨c, hcD⟩, hxcap⟩
        exact hxNbad (Or.inr hxc)
      have hPsum : finiteTranslateMultiplicity Omega P x = 1 := by
        dsimp [finiteTranslateMultiplicity]
        rw [Finset.sum_eq_single cStar]
        · simp [hxstar]
        · intro c hc hceq
          simp [hPother c hc hceq]
        · simp [Set.indicator_apply, hcStarP]
      have hQsum : finiteTranslateMultiplicity Omega Q x = 0 := by
        dsimp [finiteTranslateMultiplicity]
        apply Finset.sum_eq_zero
        intro c hc
        simp [hQother c hc]
      have hxEq : finiteTranslateMultiplicity Omega P x =
          finiteTranslateMultiplicity Omega Q x := by
        have hxN : x ∉ N := by intro hx; exact hxNbad (Or.inl hx)
        exact not_ne_iff.mp (by simpa [N] using hxN)
      linarith [hPsum, hQsum, hxEq]
    have hfalse : False := by
      simp [hPempty] at hcStarP
    exact hfalse.elim


private lemma block_packing
    {K : Region} {A : Set Tiling.Plane}
    {U : Set Tiling.Plane}
    (hsub : U ⊆ A)
    (hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A)) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements U) := by
  intro p hp q hq hpq
  exact hpack (hsub hp) (hsub hq) hpq

private lemma block_raw_union
    {K : Region} {A : Set Tiling.Plane}
    (Ablock : ℤ → Finset Tiling.Plane)
    (hpart : (⋃ r : ℤ, (Ablock r : Set Tiling.Plane)) = A) :
    openUnion K A = ⋃ r : ℤ, openUnion K (Ablock r : Set Tiling.Plane) := by
  ext x
  constructor
  · intro hx
    rw [openUnion] at hx
    obtain ⟨a, hax⟩ := Set.mem_iUnion.mp hx
    have har : (a : Tiling.Plane) ∈ ⋃ r : ℤ, (Ablock r : Set Tiling.Plane) := by
      rw [hpart]
      exact a.property
    rw [mem_iUnion] at har
    obtain ⟨r, har⟩ := har
    refine mem_iUnion_of_mem r ?_
    rw [openUnion]
    exact mem_iUnion_of_mem ⟨(a : Tiling.Plane), har⟩ hax
  · intro hx
    rw [mem_iUnion] at hx
    obtain ⟨r, hx⟩ := hx
    rw [openUnion] at hx
    obtain ⟨a, hax⟩ := Set.mem_iUnion.mp hx
    rw [openUnion]
    refine mem_iUnion_of_mem ⟨(a : Tiling.Plane), ?_⟩ hax
    rw [← hpart]
    exact mem_iUnion_of_mem r a.property

private lemma raw_union_ae_macro_support
    {K : Region} {A : Set Tiling.Plane}
    (Ablock : ℤ → Finset Tiling.Plane)
    (hpart : (⋃ r : ℤ, (Ablock r : Set Tiling.Plane)) = A)
    (hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A)) :
    openUnion K A =ᵐ[volume]
      ⋃ r : ℤ, regularSupport K (Ablock r : Set Tiling.Plane) := by
  have hsub : ∀ r : ℤ, (Ablock r : Set Tiling.Plane) ⊆ A := by
    intro r
    rw [← hpart]
    exact subset_iUnion (fun r : ℤ ↦ (Ablock r : Set Tiling.Plane)) r
  have hpackr : ∀ r : ℤ,
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements (Ablock r : Set Tiling.Plane)) := by
    intro r
    exact block_packing (hsub r) hpack
  have hae : ∀ r : ℤ,
      openUnion K (Ablock r : Set Tiling.Plane) =ᵐ[volume]
        regularSupport K (Ablock r : Set Tiling.Plane) := by
    intro r
    exact openUnion_aeEq_regularSupport (hpackr r)
  exact (Filter.EventuallyEq.of_eq (block_raw_union Ablock hpart)).trans
    (Filter.EventuallyEq.countable_iUnion hae)

private lemma global_raw_union_ae
    {K : Region} {A B : Set Tiling.Plane}
    (hpackA : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A))
    (hpackB : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements B))
    (hsupp : regularSupport K A = regularSupport K B) :
    openUnion K A =ᵐ[volume] openUnion K B := by
  exact (openUnion_aeEq_regularSupport hpackA).trans
    ((Filter.EventuallyEq.of_eq hsupp).trans
      (openUnion_aeEq_regularSupport hpackB).symm)

private lemma raw_union_ae_macro
    {K : Region} {A B : Set Tiling.Plane}
    (Ablock : ℤ → Finset Tiling.Plane)
    (hpart : (⋃ r : ℤ, (Ablock r : Set Tiling.Plane)) = A)
    (hpackA : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A))
    (hpackB : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements B))
    (hsupp : regularSupport K A = regularSupport K B) :
    openUnion K B =ᵐ[volume]
      ⋃ r : ℤ, regularSupport K (Ablock r : Set Tiling.Plane) := by
  exact (global_raw_union_ae hpackA hpackB hsupp).symm.trans
    (raw_union_ae_macro_support Ablock hpart hpackA)

private lemma exists_macro_assignment
    {K : Region} {B : Set Tiling.Plane}
    (b : Tiling.Plane) (hb : b ∈ B)
    (_hopen : IsOpen K.openCarrier)
    (hvol : 0 < volume K.openCarrier)
    {U : Set Tiling.Plane} (hcover : openUnion K B =ᵐ[volume] U)
    {R : ℤ → Set Tiling.Plane}
    (hU : U = ⋃ r : ℤ, R r) :
    ∃ r : ℤ, 0 < volume ((b +ᵥ K.openCarrier) ∩ R r) := by
  let Tb : Set Tiling.Plane := b +ᵥ K.openCarrier
  change ∃ r : ℤ, 0 < volume (Tb ∩ R r)
  have hsub : Tb ⊆ openUnion K B := by
    intro x hx
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
    exact ⟨⟨b, hb⟩, hx⟩
  by_contra hn
  push Not at hn
  have hRnull : ∀ r : ℤ,
      volume (Tb ∩ R r) = 0 := by
    intro r
    exact le_antisymm (hn r) bot_le
  have hUcover : ∀ x ∈ Tb ∩ U,
      x ∈ ⋃ r : ℤ, Tb ∩ R r := by
    intro x hx
    rw [hU] at hx
    obtain ⟨hxT, hxU⟩ := hx
    rw [mem_iUnion] at hxU
    obtain ⟨r, hxr⟩ := hxU
    exact mem_iUnion_of_mem r ⟨hxT, hxr⟩
  have hIzero : volume (Tb ∩ U) = 0 := by
    apply measure_mono_null hUcover
    exact measure_iUnion_null hRnull
  have htae : ∀ᵐ x : Tiling.Plane, x ∈ Tb → x ∈ U := by
    filter_upwards [hcover] with x hx hxT
    exact hx.mp (hsub hxT)
  have hteq : (Tb =ᵐ[volume] (Tb ∩ U : Set Tiling.Plane)) := by
    filter_upwards [htae] with x hx
    apply propext
    constructor
    · intro hxb
      exact ⟨hxb, hx hxb⟩
    · exact And.left
  have hTzero : volume Tb = 0 := by
    rw [hteq.measure_eq]
    exact hIzero
  have hTpos : 0 < volume Tb := by
    dsimp [Tb]
    rw [measure_vadd]
    exact hvol
  exact (ne_of_gt hTpos) hTzero

private lemma unique_macro_assignment
    {K : Region}
    (b : Tiling.Plane) {R : ℤ → Set Tiling.Plane}
    (hK : Bornology.IsBounded K.openCarrier)
    (hsep : ∀ r s : ℤ, r ≠ s →
      ∀ x ∈ R r, ∀ y ∈ R s,
        Metric.diam K.openCarrier < dist x y)
    {r s : ℤ}
    (hr : 0 < volume ((b +ᵥ K.openCarrier) ∩ R r))
    (hs : 0 < volume ((b +ᵥ K.openCarrier) ∩ R s)) :
    r = s := by
  by_contra hrs
  obtain ⟨x, hx⟩ := MeasureTheory.nonempty_of_measure_ne_zero (ne_of_gt hr)
  obtain ⟨y, hy⟩ := MeasureTheory.nonempty_of_measure_ne_zero (ne_of_gt hs)
  have hxy : dist x y ≤ Metric.diam K.openCarrier := by
    have hxy0 := Metric.dist_le_diam_of_mem (hK.vadd b) hx.1 hy.1
    simpa using hxy0
  have hxy' := hsep r s hrs x hx.2 y hy.2
  linarith

private lemma regular_support_bounded_of_finset
    {K : Region} (F : Finset Tiling.Plane)
    (hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (F : Set Tiling.Plane))) :
    Bornology.IsBounded (regularSupport K (F : Set Tiling.Plane)) := by
  let U : Set Tiling.Plane := (F : Set Tiling.Plane)
  have hsub : regularSupport K U ⊆
      ⋃ s : U, (s : Tiling.Plane) +ᵥ K.support := by
    intro x hx
    rw [regularSupport, Tiling.Polygonal.regularSupport, ← openUnion] at hx
    rw [closure_openUnion_eq_iUnion_support hpack] at hx
    exact interior_subset hx
  have hbound : Bornology.IsBounded
      (⋃ s : U, (s : Tiling.Plane) +ᵥ K.support) := by
    rw [Set.iUnion_subtype]
    change Bornology.IsBounded
      (⋃ x ∈ (F : Set Tiling.Plane), x +ᵥ K.support)
    apply (Bornology.isBounded_biUnion
      (s := (F : Set Tiling.Plane)) F.finite_toSet).2
    intro s hs
    exact (K.isPolygonal.isBounded.vadd s)
  exact hbound.subset hsub

private lemma finite_assignment_block
    {K : Region} {B : Set Tiling.Plane}
    (hOpenBound : Bornology.IsBounded K.openCarrier)
    {R : Set Tiling.Plane}
    (hR : Bornology.IsBounded R)
    (hfin : ∀ C : Set Tiling.Plane, Bornology.IsBounded C → (B ∩ C).Finite) :
    ∃ S : Finset Tiling.Plane, ∀ b : Tiling.Plane, b ∈ S ↔ b ∈ B ∧
        0 < volume ((b +ᵥ K.openCarrier) ∩ R) := by
  let C : Set Tiling.Plane := R - K.openCarrier
  have hC : Bornology.IsBounded C := hR.sub hOpenBound
  have hAss : {b : Tiling.Plane | b ∈ B ∧
      0 < volume ((b +ᵥ K.openCarrier) ∩ R)} ⊆ B ∩ C := by
    intro b hb
    have hne := MeasureTheory.nonempty_of_measure_ne_zero (ne_of_gt hb.2)
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy, hby⟩ := Set.mem_vadd_set.mp hx.1
    refine ⟨hb.1, ?_⟩
    rw [mem_sub]
    refine ⟨x, hx.2, y, hy, ?_⟩
    have := congrArg (fun z : Tiling.Plane ↦ z - y) hby
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm
  have hfinite : {b : Tiling.Plane | b ∈ B ∧
      0 < volume ((b +ᵥ K.openCarrier) ∩ R)}.Finite :=
    (hfin C hC).subset hAss
  let S : Finset Tiling.Plane := hfinite.toFinset
  refine ⟨S, ?_⟩
  intro b
  rw [show (b ∈ S) ↔ b ∈ ({b : Tiling.Plane | b ∈ B ∧
      0 < volume ((b +ᵥ K.openCarrier) ∩ R)} : Set Tiling.Plane) by
      simp [S]]
  rfl

private lemma assigned_block_raw_ae
    {K : Region} {B : Set Tiling.Plane}
    (Bblock : ℤ → Finset Tiling.Plane)
    {R : ℤ → Set Tiling.Plane}
    (hmem : ∀ r b, b ∈ Bblock r ↔ b ∈ B ∧
      0 < volume ((b +ᵥ K.openCarrier) ∩ R r))
    (huniq : ∀ b ∈ B, ∀ r s : ℤ,
      0 < volume ((b +ᵥ K.openCarrier) ∩ R r) →
      0 < volume ((b +ᵥ K.openCarrier) ∩ R s) → r = s)
    (hcover : openUnion K B =ᵐ[volume] ⋃ r : ℤ, R r)
    (hcount : B.Countable) :
    ∀ r : ℤ, openUnion K (Bblock r : Set Tiling.Plane) =ᵐ[volume] R r := by
  let _ : Countable B := hcount.to_subtype
  intro r
  let Rr : Set Tiling.Plane := R r
  let V : Set Tiling.Plane := openUnion K (Bblock r : Set Tiling.Plane)
  let Tb : B → Set Tiling.Plane := fun b =>
    (b : Tiling.Plane) +ᵥ K.openCarrier
  let N₁ : B → Set Tiling.Plane := fun b =>
    if (b : Tiling.Plane) ∈ Bblock r then Tb b \ Rr else ∅
  have hN₁ : ∀ b : B, volume (N₁ b) = 0 := by
    intro b
    by_cases hb : (b : Tiling.Plane) ∈ Bblock r
    · have hpos : 0 < volume (Tb b ∩ Rr) := by
        exact (hmem r (b : Tiling.Plane)).mp hb |>.2
      have hTae : ∀ᵐ x : Tiling.Plane, x ∈ Tb b →
          x ∈ ⋃ s : ℤ, R s := by
        have hsub : Tb b ⊆ openUnion K B := by
          intro x hx
          rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
          exact ⟨b, hx⟩
        filter_upwards [hcover] with x hx hxT
        exact hx.mp (hsub hxT)
      let N : ℤ → Set Tiling.Plane := fun s =>
        if s = r then ∅ else Tb b ∩ R s
      have hNnull : ∀ s : ℤ, volume (N s) = 0 := by
        intro s
        by_cases hsr : s = r
        · simp [N, hsr]
        · have hnot : ¬ 0 < volume (Tb b ∩ R s) := by
            intro hs
            have hrs := huniq (b : Tiling.Plane) b.property r s hpos hs
            exact hsr hrs.symm
          simp [N, hsr, le_antisymm (le_of_not_gt hnot) bot_le]
      have hNzero : volume (⋃ s : ℤ, N s) = 0 := measure_iUnion_null hNnull
      have hsubae : (Tb b \ Rr) ≤ᵐ[volume] ⋃ s : ℤ, N s := by
        filter_upwards [hTae] with x hx
        intro hxTb
        obtain ⟨s, hxs⟩ := mem_iUnion.mp (hx hxTb.1)
        by_cases hsr : s = r
        · subst s
          exact (hxTb.2 hxs).elim
        · exact mem_iUnion_of_mem s (by
            simp only [N, if_neg hsr, mem_inter_iff]
            exact ⟨hxTb.1, hxs⟩)
      have hle := measure_mono_ae hsubae
      rw [hNzero] at hle
      have hzero : volume (Tb b \ Rr) = 0 := le_zero_iff.mp hle
      simpa [N₁, hb] using hzero
    · simp [N₁, hb]
  have hVzero : volume (V \ Rr) = 0 := by
    have hsub : V \ Rr ⊆ ⋃ b : B, N₁ b := by
      intro x hx
      change x ∈ openUnion K (Bblock r : Set Tiling.Plane) ∧ x ∉ Rr at hx
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier] at hx
      obtain ⟨b, hbx⟩ := mem_iUnion.mp hx.1
      have hb : (b : Tiling.Plane) ∈ Bblock r := by
        exact b.property
      have hbB : (b : Tiling.Plane) ∈ B := (hmem r (b : Tiling.Plane)).mp hb |>.1
      let b' : B := ⟨(b : Tiling.Plane), hbB⟩
      have hb' : (b' : Tiling.Plane) ∈ Bblock r := hb
      exact mem_iUnion_of_mem b' (by
        simp only [N₁, hb', if_pos, Set.mem_sdiff]
        exact ⟨hbx, hx.2⟩)
    exact measure_mono_null hsub (measure_iUnion_null hN₁)
  let N₂ : B → Set Tiling.Plane := fun b =>
    if (b : Tiling.Plane) ∈ Bblock r then ∅ else Tb b ∩ Rr
  have hN₂ : ∀ b : B, volume (N₂ b) = 0 := by
    intro b
    by_cases hb : (b : Tiling.Plane) ∈ Bblock r
    · simp [N₂, hb]
    · have hnot : ¬ 0 < volume (Tb b ∩ Rr) := by
        intro hs
        exact hb ((hmem r (b : Tiling.Plane)).mpr ⟨b.property, hs⟩)
      simp [N₂, hb, le_antisymm (le_of_not_gt hnot) bot_le]
  have hRzero : volume (Rr \ V) = 0 := by
    have hsub : (Rr \ V) ≤ᵐ[volume] ⋃ b : B, N₂ b := by
      filter_upwards [hcover] with x hx hxRV
      obtain ⟨hxR, hxV⟩ := hxRV
      have hxU : x ∈ ⋃ s : ℤ, R s := mem_iUnion_of_mem r hxR
      have hxB : x ∈ openUnion K B := hx.mpr hxU
      obtain ⟨b, hbx⟩ := by
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hxB
        exact hxB
      by_cases hb : (b : Tiling.Plane) ∈ Bblock r
      · exfalso
        have hxV' : x ∈ V := by
          dsimp [V]
          rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
          exact ⟨⟨b, hb⟩, hbx⟩
        exact hxV hxV'
      · exact mem_iUnion_of_mem b (by
          simp only [N₂, if_neg hb]
          exact ⟨hbx, hxR⟩)
    have hle := measure_mono_ae hsub
    rw [measure_iUnion_null hN₂] at hle
    exact le_zero_iff.mp hle
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hVzero,
    measure_eq_zero_iff_ae_notMem.mp hRzero] with x hxV hxR
  apply propext
  constructor
  · intro hx
    by_contra hnot
    exact hxV ⟨hx, hnot⟩
  · intro hx
    by_contra hnot
    exact hxR ⟨hx, hnot⟩

private lemma finite_multiplicity_eq_indicator
    {K : Region} {F : Finset Tiling.Plane}
    (hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (F : Set Tiling.Plane))) :
    ∀ x : Tiling.Plane,
      finiteTranslateMultiplicity K.openCarrier F x =
        (openUnion K (F : Set Tiling.Plane)).indicator (fun _ ↦ (1 : ℝ)) x := by
  classical
  intro x
  by_cases hx : x ∈ openUnion K (F : Set Tiling.Plane)
  · have hx0 := hx
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hx
    obtain ⟨a, hax⟩ := hx
    have haF : (a : Tiling.Plane) ∈ F := a.property
    have haarg : x - (a : Tiling.Plane) ∈ K.openCarrier := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hax
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hax
    have hsum : ∀ c ∈ F, c ≠ (a : Tiling.Plane) →
        K.openCarrier.indicator (fun _ ↦ (1 : ℝ)) (x - c) = 0 := by
      intro c hc hca
      have hnot : x - c ∉ K.openCarrier := by
        intro hcarg
        have hcx : x ∈ (c : Tiling.Plane) +ᵥ K.openCarrier := by
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hcarg
        exact Set.disjoint_left.1
          ((isPacking_iff_openCarrier_disjoint K (F : Set Tiling.Plane)).mp
            hpack hc haF hca) hcx hax
      simp [hnot]
    have hsum' : ∑ c ∈ F,
        K.openCarrier.indicator (fun _ ↦ (1 : ℝ)) (x - c) = 1 := by
      rw [Finset.sum_eq_single (a : Tiling.Plane)]
      · simp [Set.indicator_of_mem haarg]
      · exact hsum
      · intro haa
        exact (haa haF).elim
    rw [finiteTranslateMultiplicity, hsum']
    simp [Set.indicator_of_mem hx0]
  · have hsum : ∀ c ∈ F,
        K.openCarrier.indicator (fun _ ↦ (1 : ℝ)) (x - c) = 0 := by
      intro c hc
      have hnot : x - c ∉ K.openCarrier := by
        intro hcarg
        apply hx
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
        exact ⟨⟨c, hc⟩, by
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hcarg⟩
      simp [hnot]
    rw [finiteTranslateMultiplicity, Finset.sum_eq_zero hsum]
    simp [hx]

private theorem separatedMacroBlocks_localizeMultiplicity
    {K : Region} {A B : Set Tiling.Plane}
    (Ablock : ℤ → Finset Tiling.Plane)
    (hopen : IsOpen K.openCarrier) (hbounded : Bornology.IsBounded K.openCarrier)
    (_hmeas : MeasurableSet K.openCarrier) (hvol : 0 < volume K.openCarrier)
    (hpart : (⋃ r : ℤ, (Ablock r : Set Tiling.Plane)) = A)
    (hsep : ∀ r s : ℤ, r ≠ s →
      ∀ x ∈ regularSupport K (Ablock r : Set Tiling.Plane),
      ∀ y ∈ regularSupport K (Ablock s : Set Tiling.Plane),
        Metric.diam K.openCarrier < dist x y)
    (hpackA : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A))
    (hpackB : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements B))
    (hfinB : ∀ C : Set Tiling.Plane, Bornology.IsBounded C → (B ∩ C).Finite)
    (hsupp : regularSupport K A = regularSupport K B) :
      ∃ Bblock : ℤ → Finset Tiling.Plane,
        (⋃ r : ℤ, (Bblock r : Set Tiling.Plane)) = B ∧
        Set.PairwiseDisjoint (Set.univ : Set ℤ)
          (fun r ↦ (Bblock r : Set Tiling.Plane)) ∧
        (∀ (r : ℤ) (b : Tiling.Plane),
          b ∈ Bblock r ↔ b ∈ B ∧
            0 < volume ((b +ᵥ K.openCarrier) ∩
              regularSupport K (Ablock r : Set Tiling.Plane))) ∧
        ∀ r : ℤ,
          finiteTranslateMultiplicity K.openCarrier (Ablock r) =ᵐ[volume]
            finiteTranslateMultiplicity K.openCarrier (Bblock r) := by
  classical
  have hsub : ∀ r : ℤ, (Ablock r : Set Tiling.Plane) ⊆ A := by
    intro r
    rw [← hpart]
    exact subset_iUnion (fun r : ℤ ↦ (Ablock r : Set Tiling.Plane)) r
  have hpackr : ∀ r : ℤ,
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements (Ablock r : Set Tiling.Plane)) := by
    intro r
    exact block_packing (hsub r) hpackA
  have hrawA : openUnion K A =ᵐ[volume]
      ⋃ r : ℤ, regularSupport K (Ablock r : Set Tiling.Plane) :=
    raw_union_ae_macro_support Ablock hpart hpackA
  have hrawB : openUnion K B =ᵐ[volume]
      ⋃ r : ℤ, regularSupport K (Ablock r : Set Tiling.Plane) :=
    raw_union_ae_macro Ablock hpart hpackA hpackB hsupp
  have hcountB : B.Countable := (Tiling.AxisParallel.IsPacking.locallyFinite_centres hpackB).2
  let Bblock : ℤ → Finset Tiling.Plane := fun r ↦
    Classical.choose (finite_assignment_block hbounded (regular_support_bounded_of_finset
      (Ablock r) (hpackr r)) hfinB)
  have hBmem : ∀ r b, b ∈ Bblock r ↔ b ∈ B ∧
      0 < volume ((b +ᵥ K.openCarrier) ∩
        regularSupport K (Ablock r : Set Tiling.Plane)) := by
    intro r b
    exact Classical.choose_spec (finite_assignment_block hbounded
      (regular_support_bounded_of_finset (Ablock r) (hpackr r)) hfinB) b
  have hex : ∀ b ∈ B, ∃ r : ℤ, 0 < volume ((b +ᵥ K.openCarrier) ∩
      regularSupport K (Ablock r : Set Tiling.Plane)) := by
    intro b hb
    exact exists_macro_assignment b hb hopen hvol hrawB rfl
  have huniq : ∀ b ∈ B, ∀ r s : ℤ,
      0 < volume ((b +ᵥ K.openCarrier) ∩
        regularSupport K (Ablock r : Set Tiling.Plane)) →
      0 < volume ((b +ᵥ K.openCarrier) ∩
        regularSupport K (Ablock s : Set Tiling.Plane)) → r = s := by
    intro b hb r s hr hs
    exact unique_macro_assignment b hbounded hsep hr hs
  have hcoverB : ∀ r : ℤ,
      openUnion K (Bblock r : Set Tiling.Plane) =ᵐ[volume]
        regularSupport K (Ablock r : Set Tiling.Plane) := by
    intro r
    exact assigned_block_raw_ae Bblock hBmem huniq hrawB hcountB r
  have hUnion : (⋃ r : ℤ, (Bblock r : Set Tiling.Plane)) = B := by
    ext b
    constructor
    · intro hb
      rw [mem_iUnion] at hb
      obtain ⟨r, hb⟩ := hb
      exact (hBmem r b).mp hb |>.1
    · intro hb
      obtain ⟨r, hr⟩ := hex b hb
      exact mem_iUnion_of_mem r ((hBmem r b).mpr ⟨hb, hr⟩)
  have hDisj : Set.PairwiseDisjoint (Set.univ : Set ℤ)
      (fun r ↦ (Bblock r : Set Tiling.Plane)) := by
    intro r _ s _ hrs
    change Disjoint (Bblock r : Set Tiling.Plane) (Bblock s : Set Tiling.Plane)
    rw [Set.disjoint_left]
    intro b hbr hbs
    have hr := (hBmem r b).mp hbr |>.2
    have hs := (hBmem s b).mp hbs |>.2
    exact hrs (huniq b ((hBmem r b).mp hbr |>.1) r s hr hs)
  refine ⟨Bblock, hUnion, hDisj, hBmem, ?_⟩
  intro r
  have hpackBr : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (Bblock r : Set Tiling.Plane)) := by
    intro p hp q hq hpq
    exact hpackB ((hBmem r p.1).mp hp |>.1) ((hBmem r q.1).mp hq |>.1) hpq
  have hrawEq : openUnion K (Ablock r : Set Tiling.Plane) =ᵐ[volume]
      openUnion K (Bblock r : Set Tiling.Plane) :=
    (openUnion_aeEq_regularSupport (hpackr r)).trans
      (hcoverB r).symm
  filter_upwards [hrawEq] with x hx
  rw [finite_multiplicity_eq_indicator (hpackr r) x,
    finite_multiplicity_eq_indicator hpackBr x]
  exact congrArg (fun p : Prop ↦ if p then (1 : ℝ) else 0) hx

open Tiling.AxisParallel
open Tiling.AxisParallel.Terminal

private def StrictlyOrderedAlong
    (u : Tiling.Plane) (a : ℤ → Tiling.Plane) : Prop :=
  ∀ i j : ℤ, i < j → ∃ r : ℝ, 0 < r ∧ a j = a i + r • u

private lemma ordered_injective
    {u : Tiling.Plane} {a : ℤ → Tiling.Plane}
    (hu : u ≠ 0) (ha : StrictlyOrderedAlong u a) : Function.Injective a := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨r, hr, hrij⟩ := ha i j hlt
    rw [hij] at hrij
    have : r • u = 0 := add_right_cancel (by
      have h : r • u + a j = 0 + a j := by simpa [add_comm] using hrij.symm
      exact h)
    exact hu (smul_eq_zero.mp this |>.resolve_left (ne_of_gt hr))
  · obtain ⟨r, hr, hrij⟩ := ha j i hgt
    rw [hij] at hrij
    have : r • u = 0 := add_right_cancel (by
      have h : r • u + a j = 0 + a j := by simpa [add_comm] using hrij.symm
      exact h)
    exact hu (smul_eq_zero.mp this |>.resolve_left (ne_of_gt hr))

private def periodBlock (j₀ : ℤ) (p : ℕ) (a : ℤ → Tiling.Plane) (r : ℤ) :
    Finset Tiling.Plane :=
  (Finset.Icc (j₀ + r * (p : ℤ) + 1)
    (j₀ + (r + 1) * (p : ℤ))).image a

private lemma mem_periodBlock_iff
    {j₀ : ℤ} {p : ℕ} (_hp : 0 < p) {a : ℤ → Tiling.Plane}
    (ha : Function.Injective a) (r : ℤ) (j : ℤ) :
    a j ∈ periodBlock j₀ p a r ↔
      j₀ + r * (p : ℤ) + 1 ≤ j ∧ j ≤ j₀ + (r + 1) * (p : ℤ) := by
  simp only [periodBlock, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨k, hk, hkj⟩
    have : k = j := ha hkj
    simpa [this] using hk
  · intro hj
    exact ⟨j, hj, rfl⟩

private lemma periodBlock_disjoint
    {j₀ : ℤ} {p : ℕ} (hp : 0 < p) {a : ℤ → Tiling.Plane}
    (ha : Function.Injective a) :
    Set.PairwiseDisjoint (Set.univ : Set ℤ)
      (fun r ↦ (periodBlock j₀ p a r : Set Tiling.Plane)) := by
  intro r _ s _ hrs
  change Disjoint (periodBlock j₀ p a r : Set Tiling.Plane)
    (periodBlock j₀ p a s : Set Tiling.Plane)
  rw [Set.disjoint_left]
  intro x hxr hxs
  change x ∈ periodBlock j₀ p a r at hxr
  change x ∈ periodBlock j₀ p a s at hxs
  rw [periodBlock] at hxr hxs
  obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hxr
  obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hxs
  have hjk' : j = k := ha (hkx.trans hjx.symm).symm
  subst k
  rcases lt_or_gt_of_ne hrs with hrs' | hrs'
  · have h₁ := Finset.mem_Icc.mp hj
    have h₂ := Finset.mem_Icc.mp hk
    have hmul : (r + 1) * (p : ℤ) ≤ s * (p : ℤ) := by
      have hrs1 : r + 1 ≤ s := by omega
      simpa using mul_le_mul_of_nonneg_right hrs1 (show 0 ≤ (p : ℤ) by omega)
    simp only [add_mul, one_mul] at h₁ h₂ hmul
    omega
  · have h₁ := Finset.mem_Icc.mp hj
    have h₂ := Finset.mem_Icc.mp hk
    have hmul : (s + 1) * (p : ℤ) ≤ r * (p : ℤ) := by
      have hrs1 : s + 1 ≤ r := by omega
      simpa using mul_le_mul_of_nonneg_right hrs1 (show 0 ≤ (p : ℤ) by omega)
    simp only [add_mul, one_mul] at h₁ h₂ hmul
    omega

private lemma periodBlock_union
    {j₀ : ℤ} {p : ℕ} (hp : 0 < p) {a : ℤ → Tiling.Plane} :
    (⋃ r : ℤ, (periodBlock j₀ p a r : Set Tiling.Plane)) = Set.range a := by
  ext x
  constructor
  · intro hx
    rw [mem_iUnion] at hx
    obtain ⟨r, hr⟩ := hx
    change x ∈ Finset.image a (Finset.Icc _ _) at hr
    rw [Finset.mem_image] at hr
    obtain ⟨j, -, rfl⟩ := hr
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    let q : ℤ := (j - j₀ - 1) / (p : ℤ)
    have hdecomp : j₀ + q * (p : ℤ) + 1 ≤ j ∧
        j ≤ j₀ + (q + 1) * (p : ℤ) := by
      have hn : j - j₀ - 1 = q * (p : ℤ) + (j - j₀ - 1) % (p : ℤ) := by
        dsimp [q]
        simpa [add_comm] using (Int.ediv_mul_add_emod (j - j₀ - 1) (p : ℤ)).symm
      have hmod : 0 ≤ (j - j₀ - 1) % (p : ℤ) := Int.emod_nonneg _ (by omega)
      have hmod' : (j - j₀ - 1) % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos _ (by omega)
      have hq : q * (p : ℤ) + (p : ℤ) = (q + 1) * (p : ℤ) := by ring
      omega
    rw [mem_iUnion]
    refine ⟨q, ?_⟩
    change a j ∈ periodBlock j₀ p a q
    exact Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr hdecomp, rfl⟩

private lemma regularSupport_periodBlock_separated
    {K : Region} {A : Set Tiling.Plane}
    {j₀ : ℤ} {p : ℕ} {a : ℤ → Tiling.Plane}
    (_hp : 0 < p) (hpart : Set.range a = A)
    (hvol : 0 < volume K.openCarrier)
    (hpackA : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A))
    (hcentre : ∀ r s : ℤ, r ≠ s →
      ∀ c ∈ periodBlock j₀ p a r, ∀ d ∈ periodBlock j₀ p a s,
        3 * Metric.diam K.openCarrier < dist c d) :
    ∀ r s : ℤ, r ≠ s →
      ∀ x ∈ regularSupport K (periodBlock j₀ p a r : Set Tiling.Plane),
      ∀ y ∈ regularSupport K (periodBlock j₀ p a s : Set Tiling.Plane),
        Metric.diam K.openCarrier < dist x y := by
  intro r s hrs x hx y hy
  have hsub (t : ℤ) : (periodBlock j₀ p a t : Set Tiling.Plane) ⊆ A := by
    intro z hz
    rw [periodBlock] at hz
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
    rw [← hpart]
    exact ⟨k, rfl⟩
  have hpack (t : ℤ) : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (periodBlock j₀ p a t : Set Tiling.Plane)) := by
    intro q hq q' hq' hne
    exact hpackA (hsub t hq) (hsub t hq') hne
  have hxs : ∃ c : Tiling.Plane, c ∈ periodBlock j₀ p a r ∧
      x ∈ c +ᵥ K.support := by
    have hxc : x ∈ closure (openUnion K (periodBlock j₀ p a r : Set Tiling.Plane)) :=
      interior_subset hx
    rw [closure_openUnion_eq_iUnion_support (hpack r)] at hxc
    rw [mem_iUnion] at hxc
    obtain ⟨c, hcx⟩ := hxc
    exact ⟨c, c.property, hcx⟩
  have hys : ∃ d : Tiling.Plane, d ∈ periodBlock j₀ p a s ∧
      y ∈ d +ᵥ K.support := by
    have hyc : y ∈ closure (openUnion K (periodBlock j₀ p a s : Set Tiling.Plane)) :=
      interior_subset hy
    rw [closure_openUnion_eq_iUnion_support (hpack s)] at hyc
    rw [mem_iUnion] at hyc
    obtain ⟨d, hdy⟩ := hyc
    exact ⟨d, d.property, hdy⟩
  obtain ⟨c, hc, hxc⟩ := hxs
  obtain ⟨d, hd, hyd⟩ := hys
  obtain ⟨o, ho⟩ := MeasureTheory.nonempty_of_measure_ne_zero (ne_of_gt hvol)
  have hsupp : Bornology.IsBounded K.support := K.isPolygonal.isBounded
  have hclosure : closure K.openCarrier = K.support := by
    exact K.isPolygonal.closure_interior
  have hdiam : Metric.diam K.support = Metric.diam K.openCarrier := by
    rw [← hclosure, Metric.diam_closure]
  have hxc' : dist x (c +ᵥ o) ≤ Metric.diam K.openCarrier := by
    have ho' : o ∈ K.support := by rw [← hclosure]; exact subset_closure ho
    have h := Metric.dist_le_diam_of_mem (hsupp.vadd c) hxc
      (Set.mem_vadd_set.mpr ⟨o, ho', rfl⟩)
    simpa [hdiam] using h
  have hyd' : dist y (d +ᵥ o) ≤ Metric.diam K.openCarrier := by
    have ho' : o ∈ K.support := by rw [← hclosure]; exact subset_closure ho
    have h := Metric.dist_le_diam_of_mem (hsupp.vadd d) hyd
      (Set.mem_vadd_set.mpr ⟨o, ho', rfl⟩)
    simpa [hdiam] using h
  have hcd := hcentre r s hrs c hc d hd
  have htri := dist_triangle4 (c +ᵥ o) x y (d +ᵥ o)
  have hcd' : dist (c +ᵥ o) (d +ᵥ o) = dist c d := by
    simp [dist_eq_norm, sub_eq_add_neg, add_comm, add_assoc]
  rw [hcd'] at htri
  have hxc'' : dist (c +ᵥ o) x ≤ Metric.diam K.openCarrier := by
    simpa [dist_comm] using hxc'
  have hyd'' : dist y (d +ᵥ o) ≤ Metric.diam K.openCarrier := by
    simpa [dist_comm] using hyd'
  linarith

private lemma period_shift
    {u : Tiling.Plane} {p : ℕ} {a : ℤ → Tiling.Plane}
    (hper : ∀ j : ℤ, a (j + p) = a j + u)
    (j r : ℤ) : a (j + r * (p : ℤ)) = a j + r • u := by
  induction r using Int.induction_on with
  | zero => simp
  | @succ n ih =>
      rw [show j + (↑n + 1) * (p : ℤ) = (j + ↑n * (p : ℤ)) + p by ring]
      rw [hper, ih]
      rw [add_zsmul]
      simp [add_comm, add_left_comm]
  | @pred n ih =>
      have hp := hper (j + (-↑n - 1) * (p : ℤ))
      rw [show j + (-↑n - 1) * (p : ℤ) + p = j + (-↑n) * (p : ℤ) by ring] at hp
      have hpred : a (j + (-↑n) * (p : ℤ) - p) =
          a (j + (-↑n) * (p : ℤ)) - u := by
        apply eq_sub_of_add_eq
        convert hp.symm using 1
        · ring_nf
      rw [show j + (-↑n - 1) * (p : ℤ) =
        j + (-↑n) * (p : ℤ) - p by ring]
      rw [hpred, ih]
      rw [sub_zsmul]
      simp [sub_eq_add_neg, add_comm, add_left_comm]

private lemma ordered_segment
    {u : Tiling.Plane} {a : ℤ → Tiling.Plane}
    (ha : StrictlyOrderedAlong u a) {i j : ℤ} (hij : i ≤ j) :
    ∃ t : ℝ, 0 ≤ t ∧ a j = a i + t • u := by
  rcases hij.eq_or_lt with rfl | hij
  · exact ⟨0, le_rfl, by simp⟩
  · obtain ⟨t, ht, h⟩ := ha i j hij
    exact ⟨t, ht.le, h⟩

private lemma centre_gap_lower
    {u : Tiling.Plane} {a : ℤ → Tiling.Plane}
    (ha : StrictlyOrderedAlong u a)
    {i k j : ℤ} (hik : i ≤ k) (hkj : k < j) :
    dist (a k) (a (k + 1)) ≤ dist (a i) (a j) := by
  obtain ⟨x, hx, hxi⟩ := ordered_segment ha hik
  obtain ⟨g, hg, hgk⟩ := ha k (k + 1) (by omega)
  obtain ⟨y, hy, hyj⟩ := ordered_segment ha (by omega : k + 1 ≤ j)
  have hj : a j = a i + (x + g + y) • u := by
    rw [hyj, hgk, hxi]
    rw [add_smul, add_smul]
    abel
  have hnorm : 0 ≤ ‖u‖ := norm_nonneg _
  have hright : dist (a i) (a j) = ‖(x + g + y) • u‖ := by
    rw [hj, dist_eq_norm, sub_eq_add_neg]
    simp [add_comm]
  have hright' : dist (a i) (a j) = (x + g + y) * ‖u‖ := by
    rw [hright, norm_smul]
    simp [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x + g + y)]
  have hleft : dist (a k) (a (k + 1)) = ‖g • u‖ := by
    rw [hgk, dist_eq_norm, sub_eq_add_neg]
    simp [add_comm]
  have hleft' : dist (a k) (a (k + 1)) = g * ‖u‖ := by
    rw [hleft, norm_smul]
    simp [Real.norm_eq_abs, abs_of_nonneg hg.le]
  calc
    dist (a k) (a (k + 1)) = g * ‖u‖ := hleft'
    _ ≤ (x + g + y) * ‖u‖ := by nlinarith
    _ = dist (a i) (a j) := hright'.symm

private lemma periodBlock_centre_separation_lt
    {K : Region} {u : Tiling.Plane} {a : ℤ → Tiling.Plane}
    {j₀ : ℤ} {p : ℕ} (hp : 0 < p)
    (hu : u ≠ 0)
    (ha : StrictlyOrderedAlong u a)
    (hper : ∀ j : ℤ, a (j + p) = a j + u)
    (hgap : ∀ r : ℤ, 3 * Metric.diam K.openCarrier <
      dist (a (j₀ + r * (p : ℤ))) (a (j₀ + r * (p : ℤ) + 1))) :
    ∀ r s : ℤ, r < s →
      ∀ c ∈ periodBlock j₀ p a r, ∀ d ∈ periodBlock j₀ p a s,
        3 * Metric.diam K.openCarrier < dist c d := by
  intro r s hrs c hc d hd
  have hinj := ordered_injective hu ha
  obtain ⟨i, hi, hic⟩ := by
    rw [periodBlock] at hc
    exact Finset.mem_image.mp hc
  obtain ⟨j, hj, hjd⟩ := by
    rw [periodBlock] at hd
    exact Finset.mem_image.mp hd
  have hi' := Finset.mem_Icc.mp hi
  have hj' := Finset.mem_Icc.mp hj
  subst c
  subst d
  let k : ℤ := j₀ + (r + 1) * (p : ℤ)
  have hik : i ≤ k := by dsimp [k]; omega
  have hmul : (r + 1) * (p : ℤ) ≤ s * (p : ℤ) := by
    have hrs1 : r + 1 ≤ s := by omega
    simpa using mul_le_mul_of_nonneg_right hrs1 (show 0 ≤ (p : ℤ) by omega)
  have hkj : k < j := by dsimp [k]; omega
  have hlow := centre_gap_lower ha hik hkj
  have hshift0 := period_shift hper j₀ (r + 1)
  have hshift1 := period_shift hper (j₀ + 1) (r + 1)
  have hgap_eq : dist (a k) (a (k + 1)) =
        dist (a j₀) (a (j₀ + 1)) := by
    dsimp [k]
    rw [show j₀ + (r + 1) * (p : ℤ) + 1 =
        (j₀ + 1) + (r + 1) * (p : ℤ) by ring]
    rw [hshift0, hshift1]
    simp only [dist_eq_norm]
    congr 1
    abel
  have hseed := hgap 0
  rw [show j₀ + (0 : ℤ) * (p : ℤ) = j₀ by ring] at hseed
  rw [hgap_eq] at hlow
  linarith

private lemma periodBlock_centre_separation
    {K : Region} {u : Tiling.Plane} {a : ℤ → Tiling.Plane}
    {j₀ : ℤ} {p : ℕ} (hp : 0 < p) (hu : u ≠ 0)
    (ha : StrictlyOrderedAlong u a)
    (hper : ∀ j : ℤ, a (j + p) = a j + u)
    (hgap : ∀ r : ℤ, 3 * Metric.diam K.openCarrier <
      dist (a (j₀ + r * (p : ℤ))) (a (j₀ + r * (p : ℤ) + 1))) :
    ∀ r s : ℤ, r ≠ s →
      ∀ c ∈ periodBlock j₀ p a r, ∀ d ∈ periodBlock j₀ p a s,
        3 * Metric.diam K.openCarrier < dist c d := by
  intro r s hrs c hc d hd
  rcases lt_or_gt_of_ne hrs with hrs' | hrs'
  · exact periodBlock_centre_separation_lt hp hu ha hper hgap r s hrs' c hc d hd
  · rw [dist_comm]
    exact periodBlock_centre_separation_lt hp hu ha hper hgap s r hrs' d hd c hc

private lemma periodic_gap
    {u : Tiling.Plane} {a : ℤ → Tiling.Plane}
    {j₀ : ℤ} {p : ℕ}
    (hper : ∀ j : ℤ, a (j + p) = a j + u) (r : ℤ) :
    dist (a (j₀ + r * (p : ℤ)))
        (a (j₀ + r * (p : ℤ) + 1)) =
      dist (a j₀) (a (j₀ + 1)) := by
  have h0 := period_shift hper j₀ r
  have h1 := period_shift hper (j₀ + 1) r
  rw [show j₀ + r * (p : ℤ) + 1 =
    (j₀ + 1) + r * (p : ℤ) by ring, h0, h1]
  simp only [dist_eq_norm]
  congr 1
  abel

private theorem repeatedLargeGap_centres_unique_of_regularSupport_eq
    {K : Region} {A B : Set Tiling.Plane} {u : Tiling.Plane}
    {p : ℕ} {a : ℤ → Tiling.Plane} {j₀ : ℤ}
    (hopen : IsOpen K.openCarrier)
    (hbounded : Bornology.IsBounded K.openCarrier)
    (hmeas : MeasurableSet K.openCarrier)
    (hvol : 0 < volume K.openCarrier)
    (_hfrontier : volume (frontier K.openCarrier) = 0)
    (hu : u ≠ 0) (hp : 0 < p) (hpart : Set.range a = A)
    (ha : StrictlyOrderedAlong u a)
    (hper : ∀ j : ℤ, a (j + p) = a j + u)
    (hseed : 3 * Metric.diam K.openCarrier <
      dist (a j₀) (a (j₀ + 1)))
    (hpackA : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A))
    (hpackB : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements B))
    (hsupp : regularSupport K A = regularSupport K B) :
    B = A := by
  classical
  let Ablock : ℤ → Finset Tiling.Plane :=
    fun r ↦ periodBlock j₀ p a r
  have hAunion : (⋃ r : ℤ, (Ablock r : Set Tiling.Plane)) = A := by
    dsimp [Ablock]
    exact (periodBlock_union hp).trans hpart
  have hgap : ∀ r : ℤ, 3 * Metric.diam K.openCarrier <
      dist (a (j₀ + r * (p : ℤ)))
        (a (j₀ + r * (p : ℤ) + 1)) := by
    intro r
    rw [periodic_gap hper r]
    exact hseed
  have hcentre : ∀ r s : ℤ, r ≠ s →
      ∀ c ∈ Ablock r, ∀ d ∈ Ablock s,
        3 * Metric.diam K.openCarrier < dist c d := by
    intro r s hrs c hc d hd
    exact periodBlock_centre_separation hp hu ha hper hgap r s hrs c hc d hd
  have hsep : ∀ r s : ℤ, r ≠ s →
      ∀ x ∈ regularSupport K (Ablock r : Set Tiling.Plane),
      ∀ y ∈ regularSupport K (Ablock s : Set Tiling.Plane),
        Metric.diam K.openCarrier < dist x y := by
    dsimp [Ablock]
    exact regularSupport_periodBlock_separated hp hpart hvol hpackA hcentre
  have hfinB : ∀ C : Set Tiling.Plane, Bornology.IsBounded C →
      (B ∩ C).Finite :=
    (Tiling.AxisParallel.IsPacking.locallyFinite_centres hpackB).1
  obtain ⟨Bblock, hBunion, _hBdisj, _hBmem, hmult⟩ :=
    separatedMacroBlocks_localizeMultiplicity Ablock hopen hbounded hmeas hvol
      hAunion hsep hpackA hpackB hfinB hsupp
  have hblock : ∀ r : ℤ, Bblock r = Ablock r := by
    intro r
    exact (finiteTranslationalCancellation hbounded hmeas hvol (Ablock r) (Bblock r) (hmult r)).symm
  have hblocks : (⋃ r : ℤ, (Bblock r : Set Tiling.Plane)) =
      ⋃ r : ℤ, (Ablock r : Set Tiling.Plane) := by
    apply iUnion_congr
    intro r
    exact congrArg (fun F : Finset Tiling.Plane =>
      (F : Set Tiling.Plane)) (hblock r)
  exact hBunion.symm.trans (hblocks.trans hAunion)



private theorem rationalDirection_toPlane_ne_zero (u : RationalDirection) :
    u.toPlane ≠ 0 := by
  intro h
  apply u.property
  funext i
  fin_cases i
  · have hr := congrArg Complex.re h
    change u.coordinates 0 = 0
    simpa [RationalDirection.toPlane] using hr
  · have hi := congrArg Complex.im h
    change u.coordinates 1 = 0
    simpa [RationalDirection.toPlane] using hi

private theorem affineParameter_mem_carrier
    {u : RationalDirection} {Q : RationalSlice u}
    {q x : Tiling.Plane} (hq : q ∈ Q.carrier) (hx : x ∈ Q.carrier) :
    ∃ r : ℝ, x = q + r • u.toPlane := by
  have hquot : QuotientAddGroup.mk' (realDirectionSubgroup u) x =
      QuotientAddGroup.mk' (realDirectionSubgroup u) q := by
    exact hx.trans hq.symm
  have hsub : x - q ∈ realDirectionSubgroup u :=
    QuotientAddGroup.eq_iff_sub_mem.mp hquot
  obtain ⟨r, hr⟩ := hsub
  refine ⟨r, ?_⟩
  rw [sub_eq_iff_eq_add] at hr
  simpa [add_comm] using hr

private theorem exists_orderedPeriodic_lineEnumeration_of_shared_api
    {u : RationalDirection} (Q : RationalSlice u)
    {S : Set Tiling.Plane} :
    S ⊆ Q.carrier → S.Nonempty →
    (∀ C : Set Tiling.Plane, IsCompact C → (S ∩ C).Finite) →
    Tiling.RationalPolygonal.SetPeriodicBy S u.toPlane →
      ∃ p : ℕ, 0 < p ∧ ∃ a : ℤ → Tiling.Plane,
        Set.range a = S ∧ StrictlyOrderedAlong u.toPlane a ∧
        ∀ j : ℤ, a (j + p) = a j + u.toPlane := by
  intro hSsub hSne hlocal hSperiod
  have hu : u.toPlane ≠ 0 := rationalDirection_toPlane_ne_zero u
  obtain ⟨q, hqS⟩ := hSne
  have hqQ : q ∈ Q.carrier := hSsub hqS
  let f : ℝ → Tiling.Plane := fun r => q + r • u.toPlane
  have hf : Continuous f := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hf_inj : Function.Injective f := by
    intro r s hrs
    have hzero : (r - s) • u.toPlane = 0 := by
      dsimp [f] at hrs
      have hrs' : r • u.toPlane = s • u.toPlane := add_left_cancel hrs
      rw [sub_smul, hrs', sub_self]
    rcases smul_eq_zero.mp hzero with hrs | hzero
    · exact sub_eq_zero.mp hrs
    · exact False.elim (hu hzero)
  let E : Set ℝ := {r | f r ∈ S}
  have hEne : E.Nonempty := ⟨0, by simpa [E, f] using hqS⟩
  have hElocal : ∀ R : Set ℝ, Bornology.IsBounded R →
      (E ∩ R).Finite := by
    intro R hR
    obtain ⟨B, hRB⟩ := hR.subset_closedBall 0
    let C : Set Tiling.Plane := f '' Metric.closedBall 0 B
    have hC : IsCompact C := (isCompact_closedBall 0 B).image hf
    have hfin : (S ∩ C).Finite := hlocal C hC
    have hpre : (f ⁻¹' (S ∩ C)).Finite := hfin.preimage hf_inj.injOn
    apply hpre.subset
    intro r hr
    have hrB : r ∈ Metric.closedBall 0 B := hRB hr.2
    exact ⟨hr.1, ⟨r, hrB, rfl⟩⟩
  have hEperiod : (1 : ℝ) +ᵥ E = E := by
    ext r
    constructor
    · intro hr
      obtain ⟨s, hs, hrs⟩ := Set.mem_vadd_set.mp hr
      have hfs : f s ∈ S := hs
      have hper := (hSperiod (f s))
      have hmem : f s + u.toPlane ∈ S := hper.mpr hfs
      have hfr : f r ∈ S := by
        rw [← hrs]
        change f (1 + s) ∈ S
        convert hmem using 1
        dsimp [f]
        push_cast
        ring_nf
      simpa [E] using hfr
    · intro hr
      have heq : f (r - 1) = f r - u.toPlane := by
        change q + (r - 1) • u.toPlane =
          (q + r • u.toPlane) - u.toPlane
        rw [sub_smul]
        simp only [one_smul]
        abel
      have hmem' : f r - u.toPlane ∈ S := by
        apply (hSperiod (f r - u.toPlane)).mp
        simpa [sub_add_cancel] using (show f r ∈ S from by simpa [E] using hr)
      have hmem : f (r - 1) ∈ S := by
        rw [heq]
        exact hmem'
      refine ⟨r - 1, ?_, ?_⟩
      · simpa [E] using hmem
      · simp [vadd_eq_add]
  obtain ⟨e⟩ := periodicIntEnumeration_exists E 1 (by norm_num) hEne hElocal hEperiod
  refine ⟨e.count, e.count_pos, fun j => f (e.point j), ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨j, rfl⟩
      change f (e.point j) ∈ S
      have hpE : e.point j ∈ E := by
        have hpE' : e.point j ∈ Set.range e.point := ⟨j, rfl⟩
        rw [e.point_range] at hpE'
        exact hpE'
      simpa [E] using hpE
    · intro x hx
      obtain ⟨r, hr⟩ := affineParameter_mem_carrier hqQ (hSsub hx)
      have hrE : r ∈ E := by
        change f r ∈ S
        have hfr : f r = x := by simpa [f] using hr.symm
        rw [hfr]
        exact hx
      obtain ⟨j, hj⟩ := Set.mem_range.mp (e.point_range.symm ▸ hrE)
      exact ⟨j, (congrArg f hj).trans hr.symm⟩
  · intro i j hij
    refine ⟨e.point j - e.point i, sub_pos.mpr (e.point_strictMono hij), ?_⟩
    dsimp [f]
    push_cast
    ring
  · intro j
    dsimp [f]
    change q + ↑(e.point (j + Int.ofNat e.count)) * u.toPlane =
      q + ↑(e.point j) * u.toPlane + u.toPlane
    rw [e.point_period j]
    push_cast
    ring


private def OrderedPeriodicPremise
    {_K Kphi : Region} {_source T : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi T)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (D : ℝ) : Prop :=
  ∀ i Q,
    Q ∈ (Dcmp.orbit i).gappedPhases (originalSlice i) (60 * D) →
      ∃ p : ℕ, 0 < p ∧ ∃ a : ℤ → Tiling.Plane,
        Set.range a = Q.centres (Dcmp.part i) ∧
        StrictlyOrderedAlong (Dcmp.direction i).toPlane a ∧
        (∀ j : ℤ,
          a (j + p) = a j + (Dcmp.direction i).toPlane)

private theorem relation_chain_of_adjacent
    {α : Type*} {R : α → α → Prop} {a : ℤ → α}
    (hadj : ∀ j : ℤ, Relation.EqvGen R (a j) (a (j + 1)))
    (j : ℤ) : Relation.EqvGen R (a 0) (a j) := by
  induction j using Int.induction_on with
  | zero => exact Relation.EqvGen.refl _
  | @succ n ih =>
      exact Relation.EqvGen.trans _ _ _ ih (hadj n)
  | @pred n ih =>
      have hstep : Relation.EqvGen R (a (-n)) (a (-n - 1)) := by
        convert Relation.EqvGen.symm _ _ (hadj (-n - 1)) using 1
        all_goals ring_nf
      exact Relation.EqvGen.trans _ _ _ ih hstep

private theorem source_preimage_of_slice_mem
    {Kphi : Region} {source T : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi T)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (Phi : source ↪ Tiling.Plane) (hPhiRange : Set.range Phi = T)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : source | Phi t ∈ Q.centres (Dcmp.part i)})
    {i : Fin Dcmp.numberOfParts} {Q : RationalSlice (Dcmp.direction i)}
    (hQphase : Q ∈ (Dcmp.orbit i).phases)
    {x : Tiling.Plane} (hx : x ∈ Q.centres (Dcmp.part i)) :
    ∃ v : source, (v : Tiling.Plane) ∈ originalSlice i Q ∧ Phi v = x := by
  have hpart : x ∈ T := by
    exact (Dcmp.parts_union ▸ mem_iUnion.2 ⟨i, hx.1⟩)
  obtain ⟨v, hv⟩ := Set.mem_range.1 (hPhiRange ▸ hpart)
  have hvx : Phi v = x := hv
  have hvq : Phi v ∈ Q.centres (Dcmp.part i) := by simpa [hvx] using hx
  have himage : (v : Tiling.Plane) ∈
      Set.image Subtype.val {t : source | Phi t ∈ Q.centres (Dcmp.part i)} :=
    ⟨v, hvq, rfl⟩
  refine ⟨v, ?_, hvx⟩
  rw [hPreimage i Q hQphase]
  exact himage

/-- T05's large-gap/preimage bridge, with the ordered enumeration supplied as
an explicit premise.  The unused packing and local-finiteness inputs remain in
the frozen shape so the result can be inserted at the same seam later. -/
private theorem largeRepeatedGap_of_gappedPreimage_of_enumeration
    {K Kphi : Region} {source T : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi T)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (Phi : source ↪ Tiling.Plane) (hPhiRange : Set.range Phi = T)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : source | Phi t ∈ Q.centres (Dcmp.part i)})
    (D M : ℝ) (_hD : D = Metric.diam K.openCarrier)
    (hDpos : 0 < D) (hM : 60 * D < M) (hReciprocal : M⁻¹ < D)
    (hRationalGeometry : IsOpen Kphi.openCarrier ∧
      Bornology.IsBounded Kphi.openCarrier ∧
      0 < volume Kphi.openCarrier ∧
      volume (frontier Kphi.openCarrier) = 0 ∧
      Metric.diam Kphi.openCarrier ≤ 2 * D)
    (_hGlobalPacking : Tiling.IsPacking Kphi.toPolygonalRegion.prototileFamily
      (Kphi.toPolygonalRegion.placements T))
    (_hSourceLocal : ∀ Q : Set Tiling.Plane, Bornology.IsBounded Q →
      (source ∩ Q).Finite)
    (hCoarse : ∀ v w : source,
      dist (Phi v) (Phi w) < M / 2 → dist (v : Tiling.Plane) w < M)
    (hAccurate : ∀ v w : source,
      dist (v : Tiling.Plane) w < M →
        dist (Phi w - Phi v) ((w : Tiling.Plane) - v) < M⁻¹)
    (hEnum : OrderedPeriodicPremise (_K := Kphi) (_source := source) (T := T)
      Dcmp originalSlice D) :
    ∀ (i : Fin Dcmp.numberOfParts)
      (Q : RationalSlice (Dcmp.direction i)),
      Q ∈ (Dcmp.orbit i).gappedPhases (originalSlice i) (60 * D) →
        ∃ p : ℕ, 0 < p ∧ ∃ a : ℤ → Tiling.Plane,
          Set.range a = Q.centres (Dcmp.part i) ∧
          StrictlyOrderedAlong (Dcmp.direction i).toPlane a ∧
          (∀ j : ℤ,
            a (j + p) = a j + (Dcmp.direction i).toPlane) ∧
          ∃ j₀ : ℤ, 3 * Metric.diam Kphi.openCarrier <
            dist (a j₀) (a (j₀ + 1)) := by
  intro i Q hQgapped
  obtain ⟨p, hp, a, haRange, haOrder, haPeriod⟩ := hEnum i Q hQgapped
  refine ⟨p, hp, a, haRange, haOrder, haPeriod, ?_⟩
  by_contra hNoGap
  push Not at hNoGap
  have hQphase : Q ∈ (Dcmp.orbit i).phases := hQgapped.1
  let R : Tiling.Plane → Tiling.Plane → Prop := fun x y ↦
    x ∈ originalSlice i Q ∧ y ∈ originalSlice i Q ∧ dist x y < 60 * D
  have hpre (j : ℤ) : ∃ v : source,
      (v : Tiling.Plane) ∈ originalSlice i Q ∧ Phi v = a j := by
    apply source_preimage_of_slice_mem Dcmp originalSlice Phi hPhiRange hPreimage hQphase
    exact haRange ▸ ⟨j, rfl⟩
  choose v hvSlice hvPhi using hpre
  have hsmall (j : ℤ) : dist (v j : Tiling.Plane) (v (j + 1)) < 60 * D := by
    have hdiam : Metric.diam Kphi.openCarrier ≤ 2 * D := hRationalGeometry.2.2.2.2
    have hgap : dist (a j) (a (j + 1)) < 30 * D := by
      have hle : dist (a j) (a (j + 1)) ≤ 3 * (2 * D) :=
        le_trans (hNoGap j) (by nlinarith [hdiam])
      nlinarith
    have hgapM : dist (Phi (v j)) (Phi (v (j + 1))) < M / 2 := by
      rw [hvPhi j, hvPhi (j + 1)]
      have hhalf : 30 * D < M / 2 := by linarith
      exact lt_of_lt_of_le hgap (by linarith)
    have hsourceM : dist (v j : Tiling.Plane) (v (j + 1)) < M := hCoarse _ _ hgapM
    have herror := hAccurate _ _ hsourceM
    have hdist : dist (v j : Tiling.Plane) (v (j + 1)) ≤
        dist (Phi (v j)) (Phi (v (j + 1))) +
          dist (Phi (v (j + 1)) - Phi (v j))
            ((v (j + 1) : Tiling.Plane) - v j) := by
      rw [dist_comm, dist_eq_norm]
      calc
        ‖(v (j + 1) : Tiling.Plane) - v j‖ =
            ‖((v (j + 1) : Tiling.Plane) - v j) -
                (Phi (v (j + 1)) - Phi (v j)) +
              (Phi (v (j + 1)) - Phi (v j))‖ := by ring_nf
        _ ≤ ‖((v (j + 1) : Tiling.Plane) - v j) -
                (Phi (v (j + 1)) - Phi (v j))‖ +
              ‖Phi (v (j + 1)) - Phi (v j)‖ := norm_add_le _ _
        _ = dist (Phi (v j)) (Phi (v (j + 1))) +
            dist (Phi (v (j + 1)) - Phi (v j))
              ((v (j + 1) : Tiling.Plane) - v j) := by
          rw [dist_eq_norm, dist_eq_norm]
          rw [add_comm]
          congr 1
          · exact norm_sub_rev _ _
          · exact norm_sub_rev _ _
    have hrational : dist (Phi (v j)) (Phi (v (j + 1))) < 30 * D := by
      rw [hvPhi j, hvPhi (j + 1)]
      exact hgap
    have hbound : dist (v j : Tiling.Plane) (v (j + 1)) <
        30 * D + D := by
      calc
        dist (v j : Tiling.Plane) (v (j + 1)) ≤
            dist (Phi (v j)) (Phi (v (j + 1))) +
              dist (Phi (v (j + 1)) - Phi (v j))
                ((v (j + 1) : Tiling.Plane) - v j) := hdist
        _ < 30 * D + D := by linarith
    linarith
  have hadj : ∀ j : ℤ, Relation.EqvGen R (v j) (v (j + 1)) := by
    intro j
    exact Relation.EqvGen.rel _ _ ⟨hvSlice j, hvSlice (j + 1), hsmall j⟩
  obtain ⟨x, hx, y, hy, hnot⟩ := hQgapped.2
  have hximage : x ∈ Set.image Subtype.val
      {t : source | Phi t ∈ Q.centres (Dcmp.part i)} := by
    rw [← hPreimage i Q hQphase]
    exact hx
  have hyimage : y ∈ Set.image Subtype.val
      {t : source | Phi t ∈ Q.centres (Dcmp.part i)} := by
    rw [← hPreimage i Q hQphase]
    exact hy
  obtain ⟨sx, hsx, hsxx⟩ := (Set.mem_image Subtype.val _ _).1 hximage
  obtain ⟨sy, hsy, hsyy⟩ := (Set.mem_image Subtype.val _ _).1 hyimage
  let vx : source := sx
  let vy : source := sy
  have hvxSlice : (vx : Tiling.Plane) ∈ originalSlice i Q := by
    simpa [vx, hsxx] using hx
  have hvySlice : (vy : Tiling.Plane) ∈ originalSlice i Q := by
    simpa [vy, hsyy] using hy
  have hcentvx : Phi vx ∈ Q.centres (Dcmp.part i) := hsx
  have hcentvy : Phi vy ∈ Q.centres (Dcmp.part i) := hsy
  obtain ⟨jx, hjx⟩ := Set.mem_range.1 (haRange.symm ▸ hcentvx)
  obtain ⟨jy, hjy⟩ := Set.mem_range.1 (haRange.symm ▸ hcentvy)
  have hvx_eq : v jx = vx := by
    apply Phi.injective
    rw [hvPhi jx, hjx]
  have hvy_eq : v jy = vy := by
    apply Phi.injective
    rw [hvPhi jy, hjy]
  have hchain : Relation.EqvGen R (v jx) (v jy) :=
    Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (relation_chain_of_adjacent hadj jx))
      (relation_chain_of_adjacent hadj jy)
  have hxv : (v jx : Tiling.Plane) = x := by
    rw [hvx_eq]
    exact hsxx
  have hyv : (v jy : Tiling.Plane) = y := by
    rw [hvy_eq]
    exact hsyy
  apply hnot
  rw [← hxv, ← hyv]
  exact hchain

private theorem exists_orderedPeriodic_lineEnumeration
    {u : RationalDirection} (Q : RationalSlice u)
    {S : Set Tiling.Plane} :
    S ⊆ Q.carrier → S.Nonempty →
    (∀ C : Set Tiling.Plane, IsCompact C → (S ∩ C).Finite) →
    Tiling.RationalPolygonal.SetPeriodicBy S u.toPlane →
      ∃ p : ℕ, 0 < p ∧ ∃ a : ℤ → Tiling.Plane,
        Set.range a = S ∧ StrictlyOrderedAlong u.toPlane a ∧
        ∀ j : ℤ, a (j + p) = a j + u.toPlane := by
  simpa only [StrictlyOrderedAlong] using
    (exists_orderedPeriodic_lineEnumeration_of_shared_api
      (u := u) (Q := Q) (S := S))

private theorem largeRepeatedGap_of_gappedPreimage
    {K Kphi : Region} {source T : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi T)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (Phi : source ↪ Tiling.Plane) (hPhiRange : Set.range Phi = T)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : source | Phi t ∈ Q.centres (Dcmp.part i)})
    (D M : ℝ) (hD : D = Metric.diam K.openCarrier)
    (hDpos : 0 < D) (hM : 60 * D < M) (hReciprocal : M⁻¹ < D)
    (hRationalGeometry : IsOpen Kphi.openCarrier ∧
      Bornology.IsBounded Kphi.openCarrier ∧
      0 < volume Kphi.openCarrier ∧
      volume (frontier Kphi.openCarrier) = 0 ∧
      Metric.diam Kphi.openCarrier ≤ 2 * D)
    (hGlobalPacking : Tiling.IsPacking Kphi.toPolygonalRegion.prototileFamily
      (Kphi.toPolygonalRegion.placements T))
    (hSourceLocal : ∀ Q : Set Tiling.Plane, Bornology.IsBounded Q →
      (source ∩ Q).Finite)
    (hCoarse : ∀ v w : source,
      dist (Phi v) (Phi w) < M / 2 → dist (v : Tiling.Plane) w < M)
    (hAccurate : ∀ v w : source,
      dist (v : Tiling.Plane) w < M →
        dist (Phi w - Phi v) ((w : Tiling.Plane) - v) < M⁻¹) :
    ∀ (i : Fin Dcmp.numberOfParts)
      (Q : RationalSlice (Dcmp.direction i)),
      Q ∈ (Dcmp.orbit i).gappedPhases (originalSlice i) (60 * D) →
        ∃ p : ℕ, 0 < p ∧ ∃ a : ℤ → Tiling.Plane,
          Set.range a = Q.centres (Dcmp.part i) ∧
          StrictlyOrderedAlong (Dcmp.direction i).toPlane a ∧
          (∀ j : ℤ,
            a (j + p) = a j + (Dcmp.direction i).toPlane) ∧
          ∃ j₀ : ℤ, 3 * Metric.diam Kphi.openCarrier <
            dist (a j₀) (a (j₀ + 1)) := by
  intro i Q hQ
  simpa only [StrictlyOrderedAlong] using
    (largeRepeatedGap_of_gappedPreimage_of_enumeration
    Dcmp originalSlice Phi hPhiRange hPreimage D M hD hDpos hM hReciprocal
    hRationalGeometry hGlobalPacking hSourceLocal hCoarse hAccurate
    (by
      intro i' Q' hQ'
      exact exists_orderedPeriodic_lineEnumeration
        (S := Q'.centres (Dcmp.part i')) Q'
        (by
          have hphase := hQ'.1
          intro x hx
          exact hx.2)
        ((Dcmp.orbit i').phase_iff_nonempty Q' |>.mp hQ'.1)
        (by
          intro C hC
          apply (Tiling.AxisParallel.IsPacking.locallyFinite_centres hGlobalPacking).1
            C hC.isBounded |>.subset
          intro x hx
          exact ⟨Dcmp.parts_union ▸ mem_iUnion.2 ⟨i', hx.1.1⟩, hx.2⟩)
        ((Dcmp.orbit i').slice_periodic Q' hQ'.1))
    i Q hQ)


private theorem rationalDirection_toPlane_linearCombination
    {K : Region} {T : Set Tiling.Plane}
    (D : RationalDirectionalDecomposition K T)
    (i : Fin D.numberOfParts) :
    (D.direction i).toPlane =
      D.lambdaCoefficient i • D.lambda.toPlane +
      D.gammaCoefficient i • D.gamma.toPlane := by
  change ((D.direction i).coordinates 0 : ℝ) +
      (D.direction i).coordinates 1 * Complex.I = _
  rw [show (D.direction i).coordinates =
      RationalDirection.linearCombination D.lambda D.gamma
        (D.lambdaCoefficient i) (D.gammaCoefficient i) from
      D.direction_coordinates i]
  apply Complex.ext
  · simp [RationalDirection.toPlane, RationalDirection.linearCombination,
      Complex.add_re, Complex.mul_re]
  · simp [RationalDirection.toPlane, RationalDirection.linearCombination,
      Complex.add_im, Complex.mul_im]

private theorem setPeriodicBy_zsmul
    {A : Set Tiling.Plane} {v : Tiling.Plane}
    (hA : Tiling.RationalPolygonal.SetPeriodicBy A v) (n : ℤ) :
    Tiling.RationalPolygonal.SetPeriodicBy A (n • v) := by
  intro x
  have hp : Function.Periodic (fun y : Tiling.Plane ↦ y ∈ A) v :=
    fun y ↦ propext (hA y)
  exact eq_iff_iff.mp (hp.zsmul n x)

private theorem setPeriodicBy_iUnion
    {ι : Sort*} {A : ι → Set Tiling.Plane} {v : Tiling.Plane}
    (hA : ∀ i, Tiling.RationalPolygonal.SetPeriodicBy (A i) v) :
    Tiling.RationalPolygonal.SetPeriodicBy (⋃ i, A i) v := by
  intro x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (hA i x).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (hA i x).mpr hi⟩

private theorem setPeriodicBy_add
    {A : Set Tiling.Plane} {u v : Tiling.Plane}
    (hu : Tiling.RationalPolygonal.SetPeriodicBy A u)
    (hv : Tiling.RationalPolygonal.SetPeriodicBy A v) :
    Tiling.RationalPolygonal.SetPeriodicBy A (u + v) := by
  intro x
  simpa [add_assoc, add_comm, add_left_comm] using (hu (x + v)).trans (hv x)

private theorem setPeriodicBy_neg
    {A : Set Tiling.Plane} {u : Tiling.Plane}
    (hu : Tiling.RationalPolygonal.SetPeriodicBy A u) :
    Tiling.RationalPolygonal.SetPeriodicBy A (-u) := by
  intro x
  simpa [sub_eq_add_neg] using (hu (x - u)).symm

private theorem commonLambdaMultiplier_exists
    {K : Region} {T : Set Tiling.Plane}
    (D : RationalDirectionalDecomposition K T) :
    ∃ N : ℕ, 0 < N ∧
      ∀ i : Fin D.numberOfParts,
        D.lambdaCoefficient i ∣ (N : ℤ) := by
  let N : ℕ := ∏ i : Fin D.numberOfParts, (D.lambdaCoefficient i).natAbs
  refine ⟨N, ?_, ?_⟩
  · dsimp [N]
    exact Finset.prod_pos fun i hi =>
      (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr
        (D.lambdaCoefficient_ne_zero i)))
  · intro i
    apply Int.natAbs_dvd_natAbs.mp
    simpa using (Finset.dvd_prod_of_mem (fun j : Fin D.numberOfParts ↦
      (D.lambdaCoefficient j).natAbs) (Finset.mem_univ i))

private theorem gappedOrbit_gamma_periodic
    {K : Region} {T : Set Tiling.Plane}
    {within transverse : RationalDirection}
    (O : RationalSliceOrbit K T within transverse)
    (originalSlice : RationalSlice within → Set Tiling.Plane)
    {radius : ℝ}
    (htransport : ∀ Q, Q ∈ O.gappedPhases originalSlice radius → ∀ n : ℤ,
      (Q.vadd (n • transverse.toPlane)).centres T =
        n • transverse.toPlane +ᵥ Q.centres T) :
    Tiling.RationalPolygonal.SetPeriodicBy
      (O.gappedCentres originalSlice radius) transverse.toPlane := by
  intro x
  simp only [RationalSliceOrbit.gappedCentres, Set.mem_iUnion]
  constructor
  · rintro ⟨Q, n, hn⟩
    refine ⟨Q, n - 1, ?_⟩
    have hn' := hn
    rw [htransport Q.1 Q.2 n] at hn'
    rw [htransport Q.1 Q.2 (n - 1)]
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, sub_smul, sub_eq_add_neg, add_smul,
      add_assoc, add_left_comm, add_comm] using hn'
  · rintro ⟨Q, n, hn⟩
    refine ⟨Q, n + 1, ?_⟩
    have hn' := hn
    rw [htransport Q.1 Q.2 n] at hn'
    rw [htransport Q.1 Q.2 (n + 1)]
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, add_smul,
      add_assoc, add_left_comm, add_comm] using hn'

private theorem gappedOrbit_within_periodic
    {K : Region} {T : Set Tiling.Plane}
    {within transverse : RationalDirection}
    (O : RationalSliceOrbit K T within transverse)
    (originalSlice : RationalSlice within → Set Tiling.Plane)
    {radius : ℝ} :
    Tiling.RationalPolygonal.SetPeriodicBy
      (O.gappedCentres originalSlice radius) within.toPlane := by
  apply setPeriodicBy_iUnion
  intro Q
  apply setPeriodicBy_iUnion
  intro n
  apply O.slice_periodic
  have hphase : Q.1 ∈ O.phases := Q.2.1
  exact O.phase_translate_mem Q.1 hphase n

private theorem gappedPart_twoPeriods_of_transport
    {K : Region} {T : Set Tiling.Plane}
    (D : RationalDirectionalDecomposition K T)
    (originalSlice : ∀ i : Fin D.numberOfParts,
      RationalSlice (D.direction i) → Set Tiling.Plane)
    (radius : ℝ)
    (htransport : ∀ i Q,
      Q ∈ (D.orbit i).gappedPhases (originalSlice i) radius →
      ∀ n : ℤ,
        (Q.vadd (n • D.gamma.toPlane)).centres (D.part i) =
          n • D.gamma.toPlane +ᵥ Q.centres (D.part i)) :
    ∃ N : ℕ, 0 < N ∧
      (∀ i : Fin D.numberOfParts,
        D.lambdaCoefficient i ∣ (N : ℤ)) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
          (⋃ i, (D.orbit i).gappedCentres (originalSlice i) radius)
          ((N : ℤ) • D.lambda.toPlane) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
          (⋃ i, (D.orbit i).gappedCentres (originalSlice i) radius)
          ((N : ℤ) • D.gamma.toPlane) := by
  obtain ⟨N, hN, hdiv⟩ := commonLambdaMultiplier_exists D
  have hgamma : ∀ i : Fin D.numberOfParts,
      Tiling.RationalPolygonal.SetPeriodicBy
        ((D.orbit i).gappedCentres (originalSlice i) radius)
        D.gamma.toPlane := by
    intro i
    exact gappedOrbit_gamma_periodic (D.orbit i) (originalSlice i)
      (htransport i)
  have hwithin : ∀ i : Fin D.numberOfParts,
      Tiling.RationalPolygonal.SetPeriodicBy
        ((D.orbit i).gappedCentres (originalSlice i) radius)
        (D.direction i).toPlane := by
    intro i
    exact gappedOrbit_within_periodic (D.orbit i) (originalSlice i)
  have hdir : ∀ i : Fin D.numberOfParts,
      Tiling.RationalPolygonal.SetPeriodicBy
        ((D.orbit i).gappedCentres (originalSlice i) radius)
        ((D.lambdaCoefficient i : ℤ) • D.lambda.toPlane) := by
    intro i
    have hi := rationalDirection_toPlane_linearCombination D i
    have hcomb := setPeriodicBy_zsmul (hwithin i) 1
    have hneg := setPeriodicBy_neg
      (setPeriodicBy_zsmul (hgamma i) (D.gammaCoefficient i))
    have hscaled := setPeriodicBy_add hcomb hneg
    rw [hi] at hscaled
    simpa [add_smul, add_assoc, add_left_comm, add_comm] using hscaled
  have hone : ∀ i : Fin D.numberOfParts,
      Tiling.RationalPolygonal.SetPeriodicBy
        ((D.orbit i).gappedCentres (originalSlice i) radius)
        ((N : ℤ) • D.lambda.toPlane) := by
    intro i
    obtain ⟨q, hq⟩ := hdiv i
    have hqperiod := setPeriodicBy_zsmul (hdir i) q
    simpa [hq, mul_smul, mul_comm, mul_left_comm, mul_assoc] using hqperiod
  refine ⟨N, hN, hdiv, ?_, ?_⟩
  · apply setPeriodicBy_iUnion
    intro i
    exact hone i
  · apply setPeriodicBy_iUnion
    intro i
    exact setPeriodicBy_zsmul (hgamma i) (N : ℤ)


private theorem gappedPhase_centres_translate
    {K Kphi : Region} {source T : Set Tiling.Plane}
    (D : RationalDirectionalDecomposition Kphi T)
    (originalSlice : ∀ i : Fin D.numberOfParts,
      RationalSlice (D.direction i) → Set Tiling.Plane)
    (Phi : source ↪ Tiling.Plane) :
    Set.range Phi = T →
    (∀ (i : Fin D.numberOfParts)
      (Q : RationalSlice (D.direction i)),
      Q ∈ (D.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : source | Phi t ∈ Q.centres (D.part i)}) →
    ∀ (diameter M : ℝ), diameter = Metric.diam K.openCarrier →
    0 < diameter → 60 * diameter < M → M⁻¹ < diameter →
    (IsOpen Kphi.openCarrier ∧
      Bornology.IsBounded Kphi.openCarrier ∧
      0 < volume Kphi.openCarrier ∧
      volume (frontier Kphi.openCarrier) = 0 ∧
      Metric.diam Kphi.openCarrier ≤ 2 * diameter) →
    Tiling.IsPacking Kphi.toPolygonalRegion.prototileFamily
      (Kphi.toPolygonalRegion.placements T) →
    (∀ C : Set Tiling.Plane, Bornology.IsBounded C →
      (source ∩ C).Finite) →
    (∀ v w : source,
      dist (Phi v) (Phi w) < M / 2 →
        dist (v : Tiling.Plane) w < M) →
    (∀ v w : source,
      dist (v : Tiling.Plane) w < M →
        dist (Phi w - Phi v) ((w : Tiling.Plane) - v) < M⁻¹) →
    (∀ (i : Fin D.numberOfParts)
      (Q : RationalSlice (D.direction i)),
      Q ∈ (D.orbit i).gappedPhases (originalSlice i) (60 * diameter) →
      ∃ p : ℕ, 0 < p ∧ ∃ a : ℤ → Tiling.Plane,
        Set.range a = Q.centres (D.part i) ∧
        StrictlyOrderedAlong (D.direction i).toPlane a ∧
        (∀ j : ℤ,
          a (j + p) = a j + (D.direction i).toPlane) ∧
        ∃ j₀ : ℤ, 3 * Metric.diam Kphi.openCarrier <
          dist (a j₀) (a (j₀ + 1))) →
    (∀ {A B : Set Tiling.Plane} {u : Tiling.Plane}
      {p : ℕ} {a : ℤ → Tiling.Plane} {j₀ : ℤ},
      IsOpen Kphi.openCarrier → Bornology.IsBounded Kphi.openCarrier →
      MeasurableSet Kphi.openCarrier → 0 < volume Kphi.openCarrier →
      volume (frontier Kphi.openCarrier) = 0 →
      u ≠ 0 → 0 < p → Set.range a = A →
      StrictlyOrderedAlong u a →
      (∀ j : ℤ, a (j + p) = a j + u) →
      3 * Metric.diam Kphi.openCarrier <
        dist (a j₀) (a (j₀ + 1)) →
      Tiling.IsPacking Kphi.toPolygonalRegion.prototileFamily
        (Kphi.toPolygonalRegion.placements A) →
      Tiling.IsPacking Kphi.toPolygonalRegion.prototileFamily
        (Kphi.toPolygonalRegion.placements B) →
      regularSupport Kphi A = regularSupport Kphi B → B = A) →
    ∀ (i : Fin D.numberOfParts)
      (Q : RationalSlice (D.direction i)),
      Q ∈ (D.orbit i).gappedPhases (originalSlice i) (60 * diameter) →
      ∀ n : ℤ,
        (Q.vadd (n • D.gamma.toPlane)).centres (D.part i) =
          n • D.gamma.toPlane +ᵥ Q.centres (D.part i) := by
  intro hPhiRange hPreimage diameter M hdiam hpos hlarge hsmall hGeometry
    hPacking hSourceLocal hCoarse hAccurate hLarge hUnique i Q hQg n
  let A : Set Tiling.Plane := Q.centres (D.part i)
  let An : Set Tiling.Plane :=
    (Q.vadd (n • D.gamma.toPlane)).centres (D.part i)
  let B : Set Tiling.Plane := (-n • D.gamma.toPlane) +ᵥ An
  have hQphase : Q ∈ (D.orbit i).phases := hQg.1
  have hApack : Tiling.IsPacking Kphi.toPolygonalRegion.prototileFamily
      (Kphi.toPolygonalRegion.placements A) := by
    apply (isPacking_iff_openCarrier_disjoint Kphi A).mpr
    intro a ha b hb hab
    have haT : a ∈ T := by
      rw [← D.parts_union]
      exact Set.mem_iUnion.mpr ⟨i, ha.1⟩
    have hbT : b ∈ T := by
      rw [← D.parts_union]
      exact Set.mem_iUnion.mpr ⟨i, hb.1⟩
    exact (isPacking_iff_openCarrier_disjoint Kphi T).mp hPacking
      haT hbT hab
  have hBpack : Tiling.IsPacking Kphi.toPolygonalRegion.prototileFamily
      (Kphi.toPolygonalRegion.placements B) := by
    apply (isPacking_iff_openCarrier_disjoint Kphi B).mpr
    intro b hb c hc hbc
    change Disjoint (b +ᵥ Kphi.openCarrier) (c +ᵥ Kphi.openCarrier)
    rw [Set.disjoint_left]
    intro x hxb hxc
    have hb' : n • D.gamma.toPlane + b ∈ An := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hb
      simpa [vadd_eq_add, add_assoc, add_comm, add_left_comm] using hb
    have hc' : n • D.gamma.toPlane + c ∈ An := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hc
      simpa [vadd_eq_add, add_assoc, add_comm, add_left_comm] using hc
    have hbc' : n • D.gamma.toPlane + b ≠
        n • D.gamma.toPlane + c := by
      intro he
      apply hbc
      exact add_left_cancel he
    have hAnpack : Tiling.IsPacking Kphi.toPolygonalRegion.prototileFamily
        (Kphi.toPolygonalRegion.placements An) := by
      apply (isPacking_iff_openCarrier_disjoint Kphi An).mpr
      intro a ha b hb hab
      have haT : a ∈ T := by
        rw [← D.parts_union]
        exact Set.mem_iUnion.mpr ⟨i, ha.1⟩
      have hbT : b ∈ T := by
        rw [← D.parts_union]
        exact Set.mem_iUnion.mpr ⟨i, hb.1⟩
      exact (isPacking_iff_openCarrier_disjoint Kphi T).mp hPacking
        haT hbT hab
    have hd := (isPacking_iff_openCarrier_disjoint Kphi An).mp hAnpack
      hb' hc' hbc'
    apply (Set.disjoint_left.mp hd)
      (a := x + n • D.gamma.toPlane)
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxb ⊢
      simpa [vadd_eq_add, add_assoc, add_comm, add_left_comm] using hxb
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxc ⊢
      simpa [vadd_eq_add, add_assoc, add_comm, add_left_comm] using hxc
  have hreg : regularSupport Kphi A = regularSupport Kphi B := by
    rw [regularSupport_vadd]
    rw [← (D.orbit i).regularSupport_transport Q hQphase n]
    simp [A]
  obtain ⟨p, hp, a, ha, horder, hperiod, j₀, hgap⟩ := hLarge i Q hQg
  have hBA : B = A := hUnique
    (A := A) (B := B) (u := (D.direction i).toPlane)
    (p := p) (a := a) (j₀ := j₀)
    hGeometry.1 hGeometry.2.1 hGeometry.1.measurableSet
      hGeometry.2.2.1 hGeometry.2.2.2.1
      (rationalDirection_toPlane_ne_zero (D.direction i)) hp ha horder
      hperiod hgap hApack hBpack hreg
  have hrecover : An = n • D.gamma.toPlane +ᵥ B := by
    ext x
    simp [B]
  change An = n • D.gamma.toPlane +ᵥ A
  rw [hrecover, hBA]


/-- Exact frozen sole T05 public theorem. -/
theorem gappedSliceUnion_twoPeriods
    {K Kphi : Region} {source T : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi T)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (Phi : source ↪ Tiling.Plane) :
    Set.range Phi = T →
    (∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : source | Phi t ∈ Q.centres (Dcmp.part i)}) →
    ∀ (D M : ℝ), D = Metric.diam K.openCarrier →
    0 < D → 60 * D < M → M⁻¹ < D →
    (IsOpen Kphi.openCarrier ∧
      Bornology.IsBounded Kphi.openCarrier ∧
      0 < volume Kphi.openCarrier ∧
      volume (frontier Kphi.openCarrier) = 0 ∧
      Metric.diam Kphi.openCarrier ≤ 2 * D) →
    Tiling.IsPacking Kphi.toPolygonalRegion.prototileFamily
      (Kphi.toPolygonalRegion.placements T) →
    (∀ Q : Set Tiling.Plane, Bornology.IsBounded Q →
      (source ∩ Q).Finite) →
    (∀ v w : source,
      dist (Phi v) (Phi w) < M / 2 →
        dist (v : Tiling.Plane) w < M) →
    (∀ v w : source,
      dist (v : Tiling.Plane) w < M →
        dist (Phi w - Phi v) ((w : Tiling.Plane) - v) < M⁻¹) →
      ∃ N : ℕ, 0 < N ∧
        (∀ i : Fin Dcmp.numberOfParts,
          Dcmp.lambdaCoefficient i ∣ (N : ℤ)) ∧
        Tiling.RationalPolygonal.SetPeriodicBy
            (⋃ i, (Dcmp.orbit i).gappedCentres
              (originalSlice i) (60 * D))
            ((N : ℤ) • Dcmp.lambda.toPlane) ∧
        Tiling.RationalPolygonal.SetPeriodicBy
            (⋃ i, (Dcmp.orbit i).gappedCentres
              (originalSlice i) (60 * D))
            ((N : ℤ) • Dcmp.gamma.toPlane) := by
  intro hPhiRange hPreimage D M hD hDpos hM hReciprocal
    hRationalGeometry hGlobalPacking hSourceLocal hCoarse hAccurate
  have hTransport :=
    gappedPhase_centres_translate Dcmp originalSlice Phi hPhiRange hPreimage
      D M hD hDpos hM hReciprocal hRationalGeometry hGlobalPacking
      hSourceLocal hCoarse hAccurate
      (largeRepeatedGap_of_gappedPreimage Dcmp originalSlice Phi hPhiRange
        hPreimage D M hD hDpos hM hReciprocal hRationalGeometry
        hGlobalPacking hSourceLocal hCoarse hAccurate)
      repeatedLargeGap_centres_unique_of_regularSupport_eq
  exact gappedPart_twoPeriods_of_transport Dcmp originalSlice (60 * D)
    hTransport

end Tiling.AxisParallel.Terminal
