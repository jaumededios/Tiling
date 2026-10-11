import Tiling.RationalSlopes.Approximation.FLCTransport
import Tiling.RationalSlopes.BoundaryGeometry
import Mathlib.Order.SuccPred.LinearLocallyFinite

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology
open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Approximation
open Tiling.RationalSlopes.Approximation
open Tiling.Polygonal (HasFLC IsLatticePeriodic RelativeDense TilesOn)

noncomputable section

namespace Tiling.RationalSlopes

/- Root-approved standard locally finite order provider for the two-sided endpoint chain. -/
/-- In a relatively dense set with finite bounded windows, every point has an immediate
successor. The successor gap is bounded by twice the relative-density radius. -/
private theorem cp_exists_ordered_successor_with_gap
    (Y : Set ℝ) (hfinite : ∀ Q : Set ℝ, Bornology.IsBounded Q → (Y ∩ Q).Finite)
    (hdense : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℝ, ∃ y ∈ Y, |z - y| < ρ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ Y, ∃ y' ∈ Y,
      y < y' ∧ (∀ z ∈ Y, y < z → y' ≤ z) ∧ y' - y < 2 * ρ := by
  obtain ⟨ρ, hρ, hρdense⟩ := hdense
  refine ⟨ρ, hρ, ?_⟩
  intro y hy
  obtain ⟨z, hzY, hdist⟩ := hρdense (y + ρ)
  have hdistAbs : |(y + ρ) - z| < ρ := by simpa using hdist
  have hyz : y < z := by
    have hright := (abs_lt.mp hdistAbs).2
    linarith
  have hzy : z < y + 2 * ρ := by
    have hleft := (abs_lt.mp hdistAbs).1
    linarith
  let A : Set ℝ := Y ∩ Set.Ioc y z
  have hfiniteIcc : (Y ∩ Set.Icc y z).Finite :=
    hfinite (Set.Icc y z) (Metric.isBounded_Icc y z)
  have hfiniteA : A.Finite := by
    apply hfiniteIcc.subset
    intro x hx
    exact ⟨hx.1, ⟨le_of_lt hx.2.1, hx.2.2⟩⟩
  have hAne : A.Nonempty := ⟨z, hzY, ⟨hyz, le_rfl⟩⟩
  obtain ⟨y', hy'A, hy'min⟩ := Set.exists_min_image A id hfiniteA hAne
  have hy'Y : y' ∈ Y := hy'A.1
  have hyy' : y < y' := hy'A.2.1
  refine ⟨y', hy'Y, hyy', ?_, ?_⟩
  · intro w hwY hyw
    by_cases hwz : w ≤ z
    · exact hy'min w ⟨hwY, ⟨hyw, hwz⟩⟩
    · exact le_of_lt (lt_of_le_of_lt (hy'min z ⟨hzY, ⟨hyz, le_rfl⟩⟩) (lt_of_not_ge hwz))
  · have hylez : y' ≤ z := hy'A.2.2
    linarith

/-- Every point has an immediate predecessor, with the same uniform gap bound. -/
private theorem cp_exists_ordered_predecessor_with_gap
    (Y : Set ℝ) (hfinite : ∀ Q : Set ℝ, Bornology.IsBounded Q → (Y ∩ Q).Finite)
    (hdense : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℝ, ∃ y ∈ Y, |z - y| < ρ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ Y, ∃ y' ∈ Y,
      y' < y ∧ (∀ z ∈ Y, z < y → z ≤ y') ∧ y - y' < 2 * ρ := by
  obtain ⟨ρ, hρ, hρdense⟩ := hdense
  refine ⟨ρ, hρ, ?_⟩
  intro y hy
  obtain ⟨z, hzY, hdist⟩ := hρdense (y - ρ)
  have hdistAbs : |(y - ρ) - z| < ρ := by simpa using hdist
  have hzy : z < y := by
    have hleft := (abs_lt.mp hdistAbs).1
    linarith
  have hyz : y - 2 * ρ < z := by
    have hright := (abs_lt.mp hdistAbs).2
    linarith
  let A : Set ℝ := Y ∩ Set.Ico z y
  have hfiniteIcc : (Y ∩ Set.Icc z y).Finite :=
    hfinite (Set.Icc z y) (Metric.isBounded_Icc z y)
  have hfiniteA : A.Finite := by
    apply hfiniteIcc.subset
    intro x hx
    exact ⟨hx.1, ⟨hx.2.1, hx.2.2.le⟩⟩
  have hAne : A.Nonempty := ⟨z, hzY, ⟨le_rfl, hzy⟩⟩
  obtain ⟨y', hy'A, hy'max⟩ := Set.exists_max_image A id hfiniteA hAne
  have hy'Y : y' ∈ Y := hy'A.1
  have hy'y : y' < y := hy'A.2.2
  refine ⟨y', hy'Y, hy'y, ?_, ?_⟩
  · intro w hwY hwy
    by_cases hzw : z ≤ w
    · exact hy'max w ⟨hwY, ⟨hzw, hwy⟩⟩
    · have hwz : w ≤ z := le_of_lt (lt_of_not_ge hzw)
      have hzy' : z ≤ y' := hy'max z ⟨hzY, ⟨le_rfl, hzy⟩⟩
      exact hwz.trans hzy'
  · have hzy' : z ≤ y' := hy'A.2.1
    linarith

/-- Any positive separation bound is inherited by the immediate successor gap. -/
private theorem cp_ordered_successor_gap_lower_bound
    {Y : Set ℝ} {y y' δ : ℝ}
    (hy : y ∈ Y) (hy' : y' ∈ Y) (hyy' : y < y')
    (hsep : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → δ ≤ |a - b|) :
    δ ≤ y' - y := by
  have h := hsep y hy y' hy' (ne_of_lt hyy')
  rw [abs_of_nonpos (sub_nonpos.mpr hyy'.le)] at h
  linarith

/-- A locally finite subset of the reals with no endpoints is order-isomorphic to `ℤ`;
transporting the order gives a strictly increasing two-sided chain enumerating the whole set. -/
private theorem cp_exists_ordered_integer_chain
    (Y : Set ℝ) (hfinite : ∀ a b : ℝ, (Y ∩ Set.Icc a b).Finite)
    (habove : ∀ r : ℝ, ∃ a ∈ Y, r < a) (hbelow : ∀ r : ℝ, ∃ a ∈ Y, a < r) :
    ∃ y : ℤ → ℝ, Set.range y = Y ∧ StrictMono y := by
  classical
  obtain ⟨y0, hy0⟩ := habove 0
  let α := {x : ℝ // x ∈ Y}
  have hIccFinite : ∀ a b : α, (Set.Icc a b).Finite := by
    intro a b
    have hreal : (Y ∩ Set.Icc (a : ℝ) (b : ℝ)).Finite := hfinite _ _
    have hpre : ((fun x : α => (x : ℝ)) ⁻¹' (Y ∩ Set.Icc (a : ℝ) (b : ℝ))).Finite :=
      hreal.preimage (by
        intro x hx z hz hxz
        exact Subtype.ext hxz)
    apply hpre.subset
    intro x hx
    change a ≤ x ∧ x ≤ b at hx
    change (x : ℝ) ∈ Y ∩ Set.Icc (a : ℝ) (b : ℝ)
    exact ⟨x.2, hx⟩
  letI : LocallyFiniteOrder α := LocallyFiniteOrder.ofFiniteIcc hIccFinite
  letI : Nonempty α := ⟨⟨y0, hy0.1⟩⟩
  letI : NoMaxOrder α := ⟨fun a => by
    obtain ⟨z, hzY, haz⟩ := habove (a : ℝ)
    exact ⟨⟨z, hzY⟩, haz⟩⟩
  letI : NoMinOrder α := ⟨fun a => by
    obtain ⟨z, hzY, hza⟩ := hbelow (a : ℝ)
    exact ⟨⟨z, hzY⟩, hza⟩⟩
  letI : SuccOrder α := LinearLocallyFiniteOrder.succOrder α
  letI : PredOrder α := LinearLocallyFiniteOrder.predOrder α
  let e : α ≃o ℤ := orderIsoIntOfLinearSuccPredArch
  refine ⟨fun n => (e.symm n : ℝ), ?_, ?_⟩
  · apply Set.eq_of_subset_of_subset
    · rintro x ⟨n, rfl⟩
      exact (e.symm n).2
    · intro x hx
      let a : α := ⟨x, hx⟩
      exact ⟨e a, by simp [a, e]⟩
  · intro a b hab
    exact_mod_cast e.symm.strictMono hab

/-- Under the original bounded-window/density hypotheses, the integer chain has uniformly
bounded gaps. -/
private theorem cp_exists_ordered_integer_chain_with_gap_bound
    (Y : Set ℝ) (hfinite : ∀ Q : Set ℝ, Bornology.IsBounded Q → (Y ∩ Q).Finite)
    (hdense : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℝ, ∃ y ∈ Y, |z - y| < ρ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ y : ℤ → ℝ,
      Set.range y = Y ∧ StrictMono y ∧ ∀ n : ℤ, y n < y (n + 1) ∧ y (n + 1) - y n < 2 * ρ := by
  obtain ⟨ρ, hρ, hρdense⟩ := hdense
  have hfiniteIcc : ∀ a b : ℝ, (Y ∩ Set.Icc a b).Finite := by
    intro a b
    exact hfinite _ (Metric.isBounded_Icc a b)
  have habove : ∀ r : ℝ, ∃ a ∈ Y, r < a := by
    intro r
    obtain ⟨a, ha, hdist⟩ := hρdense (r + 2 * ρ)
    have hlt := (abs_lt.mp hdist).2
    exact ⟨a, ha, by linarith⟩
  have hbelow : ∀ r : ℝ, ∃ a ∈ Y, a < r := by
    intro r
    obtain ⟨a, ha, hdist⟩ := hρdense (r - 2 * ρ)
    have hgt := (abs_lt.mp hdist).1
    exact ⟨a, ha, by linarith⟩
  obtain ⟨y, hrange, hstrict⟩ := cp_exists_ordered_integer_chain Y hfiniteIcc habove hbelow
  refine ⟨ρ, hρ, y, hrange, hstrict, ?_⟩
  intro n
  have hnY : y n ∈ Y := by
    rw [← hrange]
    exact ⟨n, rfl⟩
  obtain ⟨z, hzY, hdist⟩ := hρdense (y n + ρ)
  have hzn : y n < z := by
    have h := (abs_lt.mp hdist).2
    linarith
  have hzb : z < y n + 2 * ρ := by
    have h := (abs_lt.mp hdist).1
    linarith
  have hzRange : z ∈ Set.range y := hrange ▸ hzY
  obtain ⟨m, rfl⟩ := Set.mem_range.mp hzRange
  have hnm : n < m := hstrict.lt_iff_lt.mp hzn
  have hnnext : n + 1 ≤ m := by omega
  have hnextZ : y (n + 1) ≤ y m := hstrict.monotone hnnext
  constructor
  · exact hstrict (by omega)
  · linarith

/-- A pairwise separation bound supplies the lower bound for every gap of the chain. -/
private theorem cp_integer_chain_gap_lower_bound
    {Y : Set ℝ} {y : ℤ → ℝ} (hrange : Set.range y = Y) (hstrict : StrictMono y)
    {δ : ℝ} (hsep : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → δ ≤ |a - b|) :
    ∀ n : ℤ, δ ≤ y (n + 1) - y n := by
  intro n
  have hleft : y n ∈ Y := by rw [← hrange]; exact ⟨n, rfl⟩
  have hright : y (n + 1) ∈ Y := by rw [← hrange]; exact ⟨n + 1, rfl⟩
  exact cp_ordered_successor_gap_lower_bound hleft hright (hstrict (by omega)) hsep


/-- A two-sided integer sequence with a positive uniform gap is increasing, escapes to both
ends of the real line, and brackets every real number between consecutive terms. -/
private theorem cp_integer_gap_chain_covers_reals
    (y : ℤ → ℝ) (d : ℝ) (hd : 0 < d)
    (hgap : ∀ n : ℤ, d ≤ y (n + 1) - y n) :
    StrictMono y ∧
      (∀ z : ℝ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → z < y n) ∧
      (∀ z : ℝ, ∃ N : ℤ, ∀ n : ℤ, n ≤ N → y n < z) ∧
      (∀ z : ℝ, ∃ n : ℤ, y n ≤ z ∧ z ≤ y (n + 1)) := by
  have hsucc : ∀ n : ℤ, y n < y (n + 1) := by
    intro n
    have := hgap n
    linarith
  have hmono : StrictMono y := strictMono_int_of_lt_succ hsucc
  have hiterate : ∀ (i : ℤ) (k : ℕ), y i + (k : ℝ) * d ≤ y (i + (k : ℤ)) := by
    intro i k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep := hgap (i + (k : ℤ))
        have hindex : i + ((k + 1 : ℕ) : ℤ) = i + (k : ℤ) + 1 := by push_cast; ring
        have hmul : ((k + 1 : ℕ) : ℝ) * d = (k : ℝ) * d + d := by push_cast; ring
        rw [hindex, hmul]
        linarith
  have hforward : ∀ z : ℝ, ∃ N : ℤ, z < y N := by
    intro z
    obtain ⟨N, hN⟩ := exists_nat_gt ((z - y 0) / d)
    have hN' : z - y 0 < (N : ℝ) * d := (div_lt_iff₀ hd).mp hN
    have hIter := hiterate 0 N
    refine ⟨N, ?_⟩
    have hIter' : y 0 + (N : ℝ) * d ≤ y (N : ℤ) := by simpa using hIter
    linarith
  have hbackward : ∀ z : ℝ, ∃ N : ℤ, y N < z := by
    intro z
    obtain ⟨N, hN⟩ := exists_nat_gt ((y 0 - z) / d)
    have hN' : y 0 - z < (N : ℝ) * d := (div_lt_iff₀ hd).mp hN
    have hIter := hiterate (-(N : ℤ)) N
    refine ⟨-(N : ℤ), ?_⟩
    have hIter' : y (-(N : ℤ)) + (N : ℝ) * d ≤ y 0 := by
      simpa using hIter
    linarith
  refine ⟨hmono, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨N, hNz⟩ := hforward z
    refine ⟨N, ?_⟩
    intro n hNn
    exact lt_of_lt_of_le hNz (hmono.monotone hNn)
  · intro z
    obtain ⟨N, hNz⟩ := hbackward z
    refine ⟨N, ?_⟩
    intro n hnN
    exact lt_of_le_of_lt (hmono.monotone hnN) hNz
  · intro z
    obtain ⟨N, hNhigh⟩ := hforward z
    obtain ⟨M, hMlow⟩ := hbackward z
    let S : Set ℤ := {n | y n ≤ z}
    have hSne : S.Nonempty := ⟨M, le_of_lt hMlow⟩
    have hSbdd : BddAbove S := by
      refine ⟨N, ?_⟩
      intro n hn
      by_contra hnot
      have hNn : N ≤ n := le_of_not_ge hnot
      have hle := hmono.monotone hNn
      change y n ≤ z at hn
      linarith
    obtain ⟨n, hnmax⟩ := hSbdd.exists_isGreatest_of_nonempty hSne
    refine ⟨n, hnmax.1, ?_⟩
    by_contra hn
    have hnext : n + 1 ∈ S := by
      change y (n + 1) ≤ z
      exact le_of_not_ge hn
    have hle := hnmax.2 hnext
    omega

/-- A finite set of strictly positive possible step lengths has a positive common lower bound. -/
private theorem cp_finite_positive_step_alphabet_has_minimum
    (D : Set ℝ) (hfinite : D.Finite) (hne : D.Nonempty)
    (hpos : ∀ d ∈ D, 0 < d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ D, δ ≤ d := by
  obtain ⟨δ, hδD, hδmin⟩ := Set.exists_min_image D id hfinite hne
  exact ⟨δ, hpos δ hδD, hδmin⟩

/-- If every consecutive step belongs to a finite positive alphabet, it is bounded away from
zero, and the resulting integer chain covers the line. -/
private theorem cp_finite_positive_step_chain_covers_reals
    (y : ℤ → ℝ) (D : Set ℝ) (hfinite : D.Finite)
    (hpos : ∀ d ∈ D, 0 < d)
    (hsteps : ∀ n : ℤ, y (n + 1) - y n ∈ D) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ n : ℤ, δ ≤ y (n + 1) - y n) ∧
      (∀ z : ℝ, ∃ n : ℤ, y n ≤ z ∧ z ≤ y (n + 1)) := by
  have hne : D.Nonempty := ⟨y 1 - y 0, hsteps 0⟩
  obtain ⟨δ, hδ, hδD⟩ := cp_finite_positive_step_alphabet_has_minimum D hfinite hne hpos
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro n
    exact hδD _ (hsteps n)
  · exact (cp_integer_gap_chain_covers_reals y δ hδ (fun n => hδD _ (hsteps n))).2.2.2


private theorem cp_ordered_affine_line (Y : Set Plane) (hY : HasFLC Y)
    (a e : Plane) (he : ‖e‖ = 1) (ρ : ℝ) (hρ : 0 < ρ)
    (hdense : ∀ z : ℝ, ∃ t : ℝ, a + t • e ∈ Y ∧
      dist (a + z • e) (a + t • e) < ρ) :
    ∃ r : ℤ → ℝ, Set.range r = {t : ℝ | a + t • e ∈ Y} ∧ StrictMono r ∧
      ∀ n : ℤ, dist (a + r n • e) (a + r (n + 1) • e) < 2 * ρ := by
  classical
  let Z : Set ℝ := {t | a + t • e ∈ Y}
  have hene : e ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at he
    exact zero_ne_one he
  have hinj : Function.Injective (fun t : ℝ => a + t • e) := by
    intro s t hst
    exact smul_left_injective ℝ hene (add_left_cancel hst)
  have hdist (s t : ℝ) : dist (a + s • e) (a + t • e) = |s - t| := by
    rw [dist_eq_norm]
    have hs : (a + s • e) - (a + t • e) = (s - t) • e := by module
    rw [hs, norm_smul, Real.norm_eq_abs, he, mul_one]
  have hfinite : ∀ u v : ℝ, (Z ∩ Set.Icc u v).Finite := by
    intro u v
    let R : ℝ := max |u| |v|
    have hB := hY.1 (Metric.closedBall a R) Metric.isBounded_closedBall
    have hpre : ((fun t : ℝ => a + t • e) ⁻¹' (Y ∩ Metric.closedBall a R)).Finite :=
      hB.preimage hinj.injOn
    apply hpre.subset
    rintro t ⟨htZ, ht⟩
    refine ⟨htZ, ?_⟩
    rw [Metric.mem_closedBall]
    have hd : dist (a + t • e) a = |t| := by simpa using hdist t 0
    rw [hd]
    dsimp [R]
    exact abs_le.mpr ⟨by linarith [ht.1, neg_abs_le u, le_max_left |u| |v|],
      by linarith [ht.2, le_abs_self v, le_max_right |u| |v|]⟩
  have hzdense : ∀ z : ℝ, ∃ t ∈ Z, |z - t| < ρ := by
    intro z
    obtain ⟨t, ht, hdt⟩ := hdense z
    exact ⟨t, ht, by rwa [hdist] at hdt⟩
  have habove : ∀ z : ℝ, ∃ t ∈ Z, z < t := by
    intro z
    obtain ⟨t, ht, hdt⟩ := hzdense (z + ρ)
    exact ⟨t, ht, by linarith [(abs_lt.mp hdt).2]⟩
  have hbelow : ∀ z : ℝ, ∃ t ∈ Z, t < z := by
    intro z
    obtain ⟨t, ht, hdt⟩ := hzdense (z - ρ)
    exact ⟨t, ht, by linarith [(abs_lt.mp hdt).1]⟩
  obtain ⟨r, hrange, hstrict⟩ := cp_exists_ordered_integer_chain Z hfinite habove hbelow
  refine ⟨r, hrange, hstrict, ?_⟩
  intro n
  obtain ⟨t, ht, hdt⟩ := hzdense (r n + ρ)
  have hnt : r n < t := by linarith [(abs_lt.mp hdt).2]
  have htb : t < r n + 2 * ρ := by linarith [(abs_lt.mp hdt).1]
  have htRange : t ∈ Set.range r := hrange ▸ ht
  obtain ⟨m, rfl⟩ := htRange
  have hnm : n < m := hstrict.lt_iff_lt.mp hnt
  have hnext : r (n + 1) ≤ r m := hstrict.monotone (by omega)
  rw [hdist, abs_of_nonpos (sub_nonpos.mpr (hstrict (by omega)).le)]
  linarith


/-- The real linear functional encoded by a rational normal. -/
private def cp_rationalNormalFunctional (n : RationalNormal) : Plane →ₗ[ℝ] ℝ :=
  (n.x : ℝ) • Complex.reCLM.toLinearMap + (n.y : ℝ) • Complex.imCLM.toLinearMap

private theorem cp_rationalNormalFunctional_eq_eval (n : RationalNormal) (z : Plane) :
    cp_rationalNormalFunctional n z = normalEval n z := by
  simp [cp_rationalNormalFunctional, normalEval]

private theorem cp_rationalNormalFunctional_ker (n : RationalNormal) :
    LinearMap.ker (cp_rationalNormalFunctional n) = normalDirection n := rfl

/-- Every rational normal defines a surjective functional. -/
private theorem cp_rationalNormalFunctional_surjective (n : RationalNormal) :
    Function.Surjective (cp_rationalNormalFunctional n) := by
  intro r
  rcases n.nonzero with hx | hy
  · have hxR : (n.x : ℝ) ≠ 0 := by exact_mod_cast hx
    refine ⟨⟨r / (n.x : ℝ), 0⟩, ?_⟩
    rw [cp_rationalNormalFunctional_eq_eval, normalEval]
    simp only [mul_zero, add_zero]
    field_simp [hxR]
  · have hyR : (n.y : ℝ) ≠ 0 := by exact_mod_cast hy
    refine ⟨⟨0, r / (n.y : ℝ)⟩, ?_⟩
    rw [cp_rationalNormalFunctional_eq_eval, normalEval]
    field_simp [hyR] <;> ring

/-- Any one-dimensional kernel has a unit direction and its associated scalar coordinate. -/
private theorem cp_exists_unit_kernel_coordinate (ψ : Plane →ₗ[ℝ] ℝ)
    (hker : Module.finrank ℝ (LinearMap.ker ψ) = 1) :
    ∃ e : Plane, ∃ τ : Plane →ₗ[ℝ] ℝ,
      ‖e‖ = 1 ∧ ψ e = 0 ∧ τ e = 1 ∧
        ∀ v : Plane, ψ v = 0 → v = (τ v) • e := by
  classical
  have hker_nebot : LinearMap.ker ψ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hker
    norm_num at hker
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (LinearMap.ker ψ)).mp hker_nebot
  let e : Plane := (‖v‖⁻¹ : ℝ) • v
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have henorm : ‖e‖ = 1 := by
    calc
      ‖e‖ = ‖(‖v‖⁻¹ : ℝ)‖ * ‖v‖ := by simp [e]
      _ = 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvnorm)]
        exact inv_mul_cancel₀ (ne_of_gt hvnorm)
  have heker : e ∈ LinearMap.ker ψ := by
    rw [LinearMap.mem_ker]
    have hvψ : ψ v = 0 := LinearMap.mem_ker.mp hv
    change ψ ((‖v‖⁻¹ : ℝ) • v) = 0
    rw [map_smul, hvψ, smul_zero]
  have he0 : e ≠ 0 := by
    intro h
    have : ‖e‖ = 0 := by simp [h]
    linarith [henorm]
  let τ : Plane →ₗ[ℝ] ℝ :=
    (e.re : ℝ) • Complex.reCLM.toLinearMap + (e.im : ℝ) • Complex.imCLM.toLinearMap
  have hτe : τ e = 1 := by
    have hnormsq : Complex.normSq e = 1 := by
      rw [Complex.normSq_eq_norm_sq, henorm]
      norm_num
    have hdot : e.re ^ 2 + e.im ^ 2 = 1 := by
      have := Complex.normSq_apply e
      rw [hnormsq] at this
      nlinarith [this]
    change e.re * e.re + e.im * e.im = 1
    nlinarith [hdot]
  have heSpan := eq_span_singleton_of_mem_of_finrank_eq_one hker heker he0
  refine ⟨e, τ, henorm, ?_, hτe, ?_⟩
  · exact LinearMap.mem_ker.mp heker
  · intro w hw
    have hwmem : w ∈ LinearMap.ker ψ := LinearMap.mem_ker.mpr hw
    rw [heSpan] at hwmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwmem
    have hτw : τ w = c := by
      calc
        τ w = τ (c • e) := by rw [hc]
        _ = c * τ e := by simpa [smul_eq_mul] using (map_smul τ c e)
        _ = c := by rw [hτe, mul_one]
    calc
      w = c • e := hc.symm
      _ = (τ w) • e := by rw [hτw]

/-- A point of a level line is its basepoint plus its kernel coordinate. -/
private theorem cp_affine_level_eq_kernel_coordinate
    {ψ : Plane →ₗ[ℝ] ℝ} {a x e : Plane} {τ : Plane →ₗ[ℝ] ℝ}
    (hlevel : ψ x = ψ a)
    (hdecomp : ∀ v : Plane, ψ v = 0 → v = (τ v) • e) :
    x = a + (τ (x - a)) • e := by
  have hker : ψ (x - a) = 0 := by rw [map_sub, hlevel, sub_self]
  calc
    x = a + (x - a) := by abel
    _ = a + (τ (x - a)) • e := by congr 1; exact hdecomp (x - a) hker



private theorem cp_finite_chain_gap_alphabet (Y : Set Plane) (hY : HasFLC Y)
    (x : ℤ → Plane) (hx : ∀ n, x n ∈ Y) (R : ℝ)
    (hR : ∀ n, dist (x (n + 1)) (x n) < R) :
    ∃ D : Set Plane, D.Finite ∧ D ⊆ Y - Y ∧
      (∀ d ∈ D, ‖d‖ ≤ R) ∧ ∀ n, x (n + 1) - x n ∈ D := by
  let D := (Y - Y) ∩ Metric.closedBall (0 : Plane) R
  have hRpos : 0 < R := lt_of_le_of_lt dist_nonneg (hR 0)
  refine ⟨D, hY.2 R hRpos, inter_subset_left, ?_, ?_⟩
  · intro d hd
    simpa [Metric.mem_closedBall, dist_zero_right] using hd.2
  · intro n
    refine ⟨Set.sub_mem_sub (hx (n + 1)) (hx n), ?_⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using (hR n).le

/- The ambient map in this construction is only additive. In particular, no continuity
   of `deformPoint` is used: all escape/coverage comes from the finite positive alphabet. -/
private theorem cp_image_chain_dense_of_finite_alphabet
    (f : Plane →+ Plane) (a e : Plane) (he : ‖e‖ = 1)
    (τ : Plane →ₗ[ℝ] ℝ) (hτ : τ e = 1) (r : ℤ → ℝ)
    (hline : ∀ n : ℤ, ∃ u : ℝ, f (a + r n • e) = f a + u • e)
    (D : Set Plane) (hD : D.Finite)
    (hsteps : ∀ n : ℤ, (a + r (n + 1) • e) - (a + r n • e) ∈ D)
    (hpositive : ∀ d ∈ D, 0 < τ (f d))
    (M : ℝ) (hbound : ∀ d ∈ D, ‖f d‖ < M) :
    ∀ z : ℝ, ∃ n : ℤ, dist (f a + z • e) (f (a + r n • e)) < M := by
  classical
  choose u hu using hline
  have hgap (n : ℤ) : u (n + 1) - u n =
      τ (f ((a + r (n + 1) • e) - (a + r n • e))) := by
    rw [map_sub, hu (n + 1), hu n]
    have hsub : (f a + u (n + 1) • e) - (f a + u n • e) =
        (u (n + 1) - u n) • e := by module
    rw [hsub, map_smul, hτ, smul_eq_mul, mul_one]
  let E : Set ℝ := (fun d : Plane => τ (f d)) '' D
  have hE : E.Finite := hD.image _
  have hEpos : ∀ t ∈ E, 0 < t := by
    rintro t ⟨d, hd, rfl⟩
    exact hpositive d hd
  have hEstep : ∀ n : ℤ, u (n + 1) - u n ∈ E := by
    intro n
    exact ⟨_, hsteps n, (hgap n).symm⟩
  obtain ⟨δ, hδ, hδgap, hcover⟩ :=
    cp_finite_positive_step_chain_covers_reals u E hE hEpos hEstep
  intro z
  obtain ⟨n, hn, hn'⟩ := hcover z
  refine ⟨n, ?_⟩
  rw [hu n, dist_eq_norm]
  have hsub : (f a + z • e) - (f a + u n • e) = (z - u n) • e := by module
  rw [hsub, norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_nonneg (sub_nonneg.mpr hn)]
  have hnorm : ‖f ((a + r (n + 1) • e) - (a + r n • e))‖ =
      u (n + 1) - u n := by
    rw [map_sub, hu (n + 1), hu n]
    have hsub' : (f a + u (n + 1) • e) - (f a + u n • e) =
        (u (n + 1) - u n) • e := by module
    rw [hsub', norm_smul, Real.norm_eq_abs, he, mul_one,
      abs_of_pos (lt_of_lt_of_le hδ (hδgap n))]
  have hM := hbound _ (hsteps n)
  rw [hnorm] at hM
  linarith


private theorem cp_finite_vector_control (D : Set Plane) (hD : D.Finite)
    (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ d ∈ D, ‖deformPoint φ d - d‖ < η := by
  classical
  let F : Finset ℝ := hD.toFinset.image Complex.re ∪ hD.toFinset.image Complex.im
  refine ⟨F, η / 3, by positivity, ?_⟩
  intro φ hφ d hd
  have hre := hφ.2 d.re (Finset.mem_union_left _ (Finset.mem_image.mpr
    ⟨d, hD.mem_toFinset.mpr hd, rfl⟩))
  have him := hφ.2 d.im (Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨d, hD.mem_toFinset.mpr hd, rfl⟩))
  have hnorm := Complex.norm_le_abs_re_add_abs_im (deformPoint φ d - d)
  change ‖deformPoint φ d - d‖ ≤
    |(φ d.re : ℝ) - d.re| + |(φ d.im : ℝ) - d.im| at hnorm
  linarith

private theorem cp_finite_positive_gap_control (D : Set Plane) (hD : D.Finite)
    (hzero : 0 ∉ D) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ d ∈ D, ‖deformPoint φ d - d‖ < ‖d‖ ∧
          ‖deformPoint φ d‖ < ‖d‖ + 1 := by
  classical
  by_cases hne : D.Nonempty
  · obtain ⟨d₀, hd₀, hmin⟩ := Set.exists_min_image D norm hD hne
    have hd₀pos : 0 < ‖d₀‖ := norm_pos_iff.mpr (by intro h; exact hzero (h ▸ hd₀))
    let η : ℝ := min ‖d₀‖ 1
    have hη : 0 < η := lt_min hd₀pos zero_lt_one
    obtain ⟨F, ε, hε, hctrl⟩ := cp_finite_vector_control D hD η hη
    refine ⟨F, ε, hε, ?_⟩
    intro φ hφ d hd
    have herr := hctrl φ hφ d hd
    refine ⟨lt_of_lt_of_le herr ((min_le_left _ _).trans (hmin d hd)), ?_⟩
    have htri : ‖deformPoint φ d‖ ≤ ‖deformPoint φ d - d‖ + ‖d‖ := by
      simpa only [sub_add_cancel] using norm_add_le (deformPoint φ d - d) d
    have hηone : η ≤ 1 := min_le_right _ _
    linarith
  · refine ⟨∅, 1, zero_lt_one, ?_⟩
    intro φ hφ d hd
    exact (hne ⟨d, hd⟩).elim

private theorem cp_finite_boundary_normals (K : PolygonalRegion)
    (hK : Tiling.RationalSlopes.HasRationalSlopes K) :
    ∃ N : Finset RationalNormal, ∀ δ : Submodule ℝ Plane,
      Tiling.Polygonal.HasBoundaryDirection K δ →
        ∃ n ∈ N, normalDirection n = δ := by
  classical
  let B := {δ : Submodule ℝ Plane // Tiling.Polygonal.HasBoundaryDirection K δ}
  have hB := Tiling.Polygonal.boundaryDirections_finite K
  haveI : Finite B := hB.to_subtype
  have hnormal : ∀ δ : B, ∃ n : RationalNormal, normalDirection n = δ.1 := by
    intro δ
    have hdim : Module.finrank ℝ δ.1 = 1 := by
      obtain ⟨a, b, hab, hseg, hspan⟩ := δ.2
      rw [hspan]
      exact finrank_span_singleton (sub_ne_zero.mpr hab.symm)
    exact rationalDirection_hasNormal δ.1 hdim
      (Tiling.Polygonal.hasRationalDirection_of_hasBoundaryDirection hK δ.2)
  choose ν hν using hnormal
  have hfinite : (Set.range ν).Finite := Set.finite_range ν
  refine ⟨hfinite.toFinset, ?_⟩
  intro δ hδ
  refine ⟨ν ⟨δ, hδ⟩, hfinite.mem_toFinset.mpr ⟨⟨δ, hδ⟩, rfl⟩, hν ⟨δ, hδ⟩⟩


private theorem cp_deformation_bounded_gap_tests (Y : Set Plane) (hY : HasFLC Y)
    (R : ℝ) (hR : 0 < R) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ u ∈ Y, ∀ v ∈ Y, dist u v < R → u ≠ v →
          ‖deformPoint φ (u - v) - (u - v)‖ < ‖u - v‖ ∧
            ‖deformPoint φ (u - v)‖ < ‖u - v‖ + 1 := by
  let D : Set Plane := ((Y - Y) ∩ Metric.closedBall 0 R) \ {0}
  have hD : D.Finite := (hY.2 R hR).diff
  have hzero : 0 ∉ D := by simp [D]
  obtain ⟨F, ε, hε, hctrl⟩ := cp_finite_positive_gap_control D hD hzero
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ u hu v hv hdist hne
  have hnorm : ‖u - v‖ < R := by simpa only [dist_eq_norm] using hdist
  have hd : u - v ∈ D := by
    refine ⟨⟨Set.sub_mem_sub hu hv, ?_⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm.le
    · simpa only [Set.mem_singleton_iff] using sub_ne_zero.mpr hne
  obtain ⟨hrel, hb⟩ := hctrl φ hφ (u - v) hd
  exact ⟨hrel, hb⟩


private theorem cp_positive_image_scalar (e : Plane) (he : ‖e‖ = 1)
    (s t : ℝ) (hs : 0 < s) (herr : ‖t • e - s • e‖ < ‖s • e‖) :
    0 < t := by
  have hsub : t • e - s • e = (t - s) • e := by module
  rw [hsub, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, he,
    mul_one, mul_one, abs_of_pos hs] at herr
  linarith [(abs_lt.mp herr).1]


theorem deformPoint_lineCloud_dense_of_gapControl
    (Y : Set Plane) (hY : HasFLC Y) (n : RationalNormal)
    (hker : Module.finrank ℝ (normalDirection n) = 1)
    (a : Plane) (ρ : ℝ) (hρ : 0 < ρ)
    (hdense : ∀ z : Plane, normalEval n z = normalEval n a →
      ∃ w ∈ Y, normalEval n w = normalEval n a ∧ dist z w < ρ)
    (φ : ℝ →ₗ[ℚ] ℚ)
    (hctrl : ∀ u ∈ Y, ∀ v ∈ Y, dist u v < 2 * ρ → u ≠ v →
      ‖deformPoint φ (u - v) - (u - v)‖ < ‖u - v‖ ∧
        ‖deformPoint φ (u - v)‖ < 2 * ρ + 1) :
    ∀ z : Plane, normalEval n z = normalEval n (deformPoint φ a) →
      ∃ w ∈ Y, normalEval n w = normalEval n a ∧
        normalEval n (deformPoint φ w) = normalEval n (deformPoint φ a) ∧
        dist z (deformPoint φ w) < 2 * ρ + 1 := by
  classical
  let π := cp_rationalNormalFunctional n
  let f : Plane →+ Plane := (deformPointLinear φ).toAddMonoidHom
  obtain ⟨e, τ, he, hπe, hτe, hdecomp⟩ := cp_exists_unit_kernel_coordinate π hker
  have hnormal (z : Plane) : π z = normalEval n z := cp_rationalNormalFunctional_eq_eval n z
  have hpoint (s : ℝ) : π (a + s • e) = π a := by
    rw [map_add, map_smul, hπe, smul_zero, add_zero]
  have hsource_dense : ∀ s : ℝ, ∃ t : ℝ, a + t • e ∈ Y ∧
      dist (a + s • e) (a + t • e) < ρ := by
    intro s
    obtain ⟨w, hw, hwline, hdist⟩ := hdense (a + s • e)
      (by simpa only [← hnormal] using hpoint s)
    have hwcoord : w = a + τ (w - a) • e :=
      cp_affine_level_eq_kernel_coordinate (by simpa only [hnormal] using hwline) hdecomp
    exact ⟨τ (w - a), hwcoord ▸ hw, hwcoord ▸ hdist⟩
  obtain ⟨r, hrange, hstrict, hgap⟩ := cp_ordered_affine_line Y hY a e he ρ hρ hsource_dense
  let p : ℤ → Plane := fun k => a + r k • e
  have hpY : ∀ k, p k ∈ Y := by
    intro k
    have hh : r k ∈ Set.range r := ⟨k, rfl⟩
    rwa [hrange] at hh
  have hpnormal (k : ℤ) : π (p k) = π a := hpoint _
  have hfpoint (k : ℤ) : π (f (p k)) = π (f a) := by
    change normalEval n (deformPoint φ (p k)) = normalEval n (deformPoint φ a)
    rw [rationalNormal_commutes, rationalNormal_commutes]
    rw [← hnormal, ← hnormal, hpnormal]
  have hline : ∀ k : ℤ, ∃ u : ℝ, f (p k) = f a + u • e := by
    intro k
    exact ⟨τ (f (p k) - f a),
      cp_affine_level_eq_kernel_coordinate (hfpoint k) hdecomp⟩
  obtain ⟨D₀, hD₀, hD₀sub, hD₀bound, hD₀steps⟩ :=
    cp_finite_chain_gap_alphabet Y hY p hpY (2 * ρ) (fun k => by
      simpa only [dist_comm] using hgap k)
  let D : Set Plane := Set.range (fun k : ℤ => p (k + 1) - p k)
  have hD : D.Finite := hD₀.subset (by rintro d ⟨k, rfl⟩; exact hD₀steps k)
  have hctrlstep (k : ℤ) :
      ‖f (p (k + 1) - p k) - (p (k + 1) - p k)‖ < ‖p (k + 1) - p k‖ ∧
      ‖f (p (k + 1) - p k)‖ < 2 * ρ + 1 := by
    apply hctrl _ (hpY (k + 1)) _ (hpY k) (by simpa only [dist_comm] using hgap k)
    intro heq
    have he0 : e ≠ 0 := by intro h; simpa [h] using he
    have hrr : r (k + 1) = r k := smul_left_injective ℝ he0 (add_left_cancel heq)
    exact (ne_of_gt (hstrict (by omega))) hrr
  have hpositive : ∀ d ∈ D, 0 < τ (f d) := by
    rintro d ⟨k, rfl⟩
    have hzero : π (f (p (k + 1) - p k)) = 0 := by
      rw [map_sub, map_sub, hfpoint, hfpoint, sub_self]
    have himage := hdecomp _ hzero
    have hsource : p (k + 1) - p k = (r (k + 1) - r k) • e := by
      change (a + r (k + 1) • e) - (a + r k • e) = (r (k + 1) - r k) • e
      module
    have herr := (hctrlstep k).1
    rw [himage] at herr
    have hsource_norm : ‖p (k + 1) - p k‖ = ‖(r (k + 1) - r k) • e‖ := congrArg norm hsource
    rw [hsource_norm] at herr
    have herr' : ‖τ (f (p (k + 1) - p k)) • e - (r (k + 1) - r k) • e‖ <
        ‖(r (k + 1) - r k) • e‖ := by
      exact hsource ▸ herr
    have hpos := cp_positive_image_scalar e he (r (k + 1) - r k)
      (τ (f (p (k + 1) - p k))) (sub_pos.mpr (hstrict (by omega))) herr'
    exact hpos
  have hbound : ∀ d ∈ D, ‖f d‖ < 2 * ρ + 1 := by
    rintro d ⟨k, rfl⟩
    exact (hctrlstep k).2
  have hcover := cp_image_chain_dense_of_finite_alphabet f a e he τ hτe r hline D hD
    (fun k => ⟨k, rfl⟩) hpositive (2 * ρ + 1) hbound
  intro z hz
  have hzπ : π z = π (f a) := by
    change π z = π (deformPoint φ a)
    simpa only [hnormal] using hz
  have hzcoord : z = f a + τ (z - f a) • e :=
    cp_affine_level_eq_kernel_coordinate hzπ hdecomp
  obtain ⟨k, hk⟩ := hcover (τ (z - f a))
  refine ⟨p k, hpY k, ?_, ?_, ?_⟩
  · simpa only [hnormal] using hpnormal k
  · change normalEval n (f (p k)) = normalEval n (f a)
    simpa only [hnormal] using hfpoint k
  · change dist z (f (a + r k • e)) < 2 * ρ + 1
    simpa only [← hzcoord] using hk


private theorem cp_lifted_chain_preserves_fibre_density
    (Y : Set Plane) (hY : HasFLC Y)
    (f : Plane →+ Plane) (π : Plane →ₗ[ℝ] ℝ) (e : Plane) (τ : Plane →ₗ[ℝ] ℝ)
    (v : ℤ → Plane) (u : ℤ → ℝ) (b : Plane) (M : ℝ)
    (he : ‖e‖ = 1) (hπe : π e = 0) (hτe : τ e = 1)
    (hrep : ∀ w : Plane, π w = 0 → w = (τ w) • e)
    (hvY : ∀ n : ℤ, v n ∈ Y)
    (himage : ∀ n : ℤ, f (v n) = b + (u n) • e)
    (hstrict : StrictMono u)
    (himageGap : ∀ n : ℤ, dist (f (v (n + 1))) (f (v n)) < M / 2)
    (hcoarse : ∀ x ∈ Y, ∀ y ∈ Y,
      dist (f x) (f y) < M / 2 → dist x y < M)
    (hreflect : ∀ x ∈ Y, ∀ y ∈ Y,
      dist (f x) (f y) < M / 2 →
        (π (f x - f y) = 0 ↔ π (x - y) = 0))
    (hvector : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → dist x y < M →
      ‖f (x - y) - (x - y)‖ < ‖x - y‖) :
    (∀ n : ℤ, π (v n - v 0) = 0) ∧
      ∀ z : Plane, π (z - v 0) = 0 → ∃ n : ℤ, dist z (v n) < M := by
  have hM : 0 < M := by
    have h := himageGap 0
    have : 0 ≤ dist (f (v (0 + 1))) (f (v 0)) := dist_nonneg
    have hpos : 0 < M / 2 := lt_of_le_of_lt this h
    linarith
  have himageStep : ∀ n : ℤ,
      f (v (n + 1)) - f (v n) = (u (n + 1) - u n) • e := by
    intro n
    rw [himage, himage]
    module
  have hsourceNormalStep : ∀ n : ℤ, π (v (n + 1) - v n) = 0 := by
    intro n
    have hπimage : π (f (v (n + 1)) - f (v n)) = 0 := by
      rw [himageStep, map_smul, hπe, smul_zero]
    exact (hreflect (v (n + 1)) (hvY _) (v n) (hvY _) (himageGap n)).mp hπimage
  have hlevel : ∀ n : ℤ, π (v n) = π (v 0) := by
    intro n
    induction n using Int.induction_on with
    | zero => rfl
    | succ n ih =>
        have hs := hsourceNormalStep n
        rw [map_sub] at hs
        have hs' : π (v (n + 1)) = π (v n) := sub_eq_zero.mp hs
        simpa using hs'.trans ih
    | pred n ih =>
        let k : ℤ := -(n : ℤ) - 1
        have hs := hsourceNormalStep k
        have hidx : k + 1 = -(n : ℤ) := by dsimp [k]; omega
        rw [hidx, map_sub] at hs
        have hs' : π (v (-(n : ℤ))) = π (v k) := sub_eq_zero.mp hs
        exact hs'.symm.trans ih
  have hvlevel : ∀ n : ℤ, π (v n - v 0) = 0 := by
    intro n
    rw [map_sub, hlevel n, sub_self]
  let r : ℤ → ℝ := fun n => τ (v n - v 0)
  have hsourceRep : ∀ n : ℤ, v n = v 0 + (r n) • e := by
    intro n
    have hker : π (v n - v 0) = 0 := hvlevel n
    have hrepr := hrep (v n - v 0) hker
    have hrepr' : v n = v 0 + (τ (v n - v 0)) • e := by
      calc
        v n = v 0 + (v n - v 0) := by abel
        _ = v 0 + (τ (v n - v 0)) • e := congrArg (fun w : Plane => v 0 + w) hrepr
    simpa [r] using hrepr'
  have hτstep : ∀ n : ℤ, τ (v (n + 1) - v n) = r (n + 1) - r n := by
    intro n
    have hvec : v (n + 1) - v n = (v (n + 1) - v 0) - (v n - v 0) := by abel
    rw [hvec, map_sub]
  have hgap_pos : ∀ n : ℤ, 0 < r (n + 1) - r n := by
    intro n
    have himgpos : 0 < u (n + 1) - u n := sub_pos.mpr (hstrict (by omega))
    have hdist : dist (f (v (n + 1))) (f (v n)) < M / 2 := himageGap n
    have hsourceM : dist (v (n + 1)) (v n) < M :=
      hcoarse (v (n + 1)) (hvY _) (v n) (hvY _) hdist
    have hne : v (n + 1) ≠ v n := by
      intro heq
      have : f (v (n + 1)) = f (v n) := congrArg f heq
      have hzero : f (v (n + 1)) - f (v n) = 0 := sub_eq_zero.mpr this
      rw [himageStep] at hzero
      have hzero' := congrArg τ hzero
      rw [map_smul, hτe, smul_eq_mul, mul_one, map_zero] at hzero'
      linarith
    have hvec := hvector (v (n + 1)) (hvY _) (v n) (hvY _) hne hsourceM
    have hstep : v (n + 1) - v n = (r (n + 1) - r n) • e := by
      have hkerstep := hsourceNormalStep n
      have hrepr := hrep (v (n + 1) - v n) hkerstep
      rw [hτstep n] at hrepr
      exact hrepr
    have hdiff : f (v (n + 1) - v n) - (v (n + 1) - v n) =
        ((u (n + 1) - u n) - (r (n + 1) - r n)) • e := by
      have hfstep : f (v (n + 1) - v n) = f (v (n + 1)) - f (v n) :=
        map_sub f _ _
      rw [hfstep, himageStep, hstep]
      module
    have hnorm : ‖((u (n + 1) - u n) - (r (n + 1) - r n)) • e‖ <
        ‖(r (n + 1) - r n) • e‖ := by
      rw [← hdiff]
      rw [← hstep]
      exact hvec
    simp only [norm_smul, he, mul_one, Real.norm_eq_abs] at hnorm
    by_contra hnot
    have hle : r (n + 1) - r n ≤ 0 := le_of_not_gt hnot
    have hbound := (abs_lt.mp hnorm).2
    rw [abs_of_nonpos hle] at hbound
    linarith
  have hgap_bound : ∀ n : ℤ, r (n + 1) - r n < M := by
    intro n
    have hsourceM := hcoarse (v (n + 1)) (hvY _) (v n) (hvY _) (himageGap n)
    have hstep : v (n + 1) - v n = (r (n + 1) - r n) • e := by
      have hkerstep := hsourceNormalStep n
      have hrepr := hrep (v (n + 1) - v n) hkerstep
      rw [hτstep n] at hrepr
      exact hrepr
    have hdistEq : dist (v (n + 1)) (v n) = r (n + 1) - r n := by
      rw [dist_eq_norm, hstep, norm_smul, he, Real.norm_eq_abs, abs_of_pos (hgap_pos n), mul_one]
    rw [hdistEq] at hsourceM
    exact hsourceM
  let S : Set Plane := (Y - Y) ∩ Metric.closedBall (0 : Plane) M
  have hSfinite : S.Finite := hY.2 M hM
  have hdiffS : ∀ n : ℤ, v (n + 1) - v n ∈ S := by
    intro n
    constructor
    · exact ⟨v (n + 1), hvY _, v n, hvY _, rfl⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have hsourceM := hcoarse (v (n + 1)) (hvY _) (v n) (hvY _) (himageGap n)
      simpa [dist_eq_norm] using hsourceM.le
  let D : Set ℝ := Set.range (fun n : ℤ => r (n + 1) - r n)
  have hDfinite : D.Finite := by
    apply (hSfinite.image τ).subset
    rintro d ⟨n, rfl⟩
    exact ⟨v (n + 1) - v n, hdiffS n, hτstep n⟩
  have hsteps : ∀ n : ℤ, r (n + 1) - r n ∈ D := fun n => ⟨n, rfl⟩
  have hposD : ∀ d ∈ D, 0 < d := by
    rintro d ⟨n, rfl⟩
    exact hgap_pos n
  obtain ⟨δ, hδ, hδgap, hbracket⟩ :=
    cp_finite_positive_step_chain_covers_reals r D hDfinite hposD hsteps
  refine ⟨hvlevel, ?_⟩
  intro z hz
  let rz : ℝ := τ (z - v 0)
  have hzrep : z = v 0 + rz • e := by
    have h := hrep (z - v 0) hz
    calc
      z = v 0 + (z - v 0) := by abel
      _ = v 0 + rz • e := by
        simpa [rz] using congrArg (fun w : Plane => v 0 + w) h
  obtain ⟨n, hnlow, hnhigh⟩ := hbracket rz
  have hdistEq : dist z (v n) = |rz - r n| := by
    rw [dist_eq_norm]
    have hkerzn : π (z - v n) = 0 := by
      have hvec : z - v n = (z - v 0) - (v n - v 0) := by abel
      rw [hvec, map_sub, hz, hvlevel n, sub_self]
    have hcoord : τ (z - v n) = rz - r n := by
      have hvec : z - v n = (z - v 0) - (v n - v 0) := by abel
      rw [hvec, map_sub]
    have hrepr := hrep (z - v n) hkerzn
    rw [hcoord] at hrepr
    rw [hrepr, norm_smul, he, Real.norm_eq_abs, mul_one]
  have hgap := hgap_bound n
  have habs : |rz - r n| ≤ r (n + 1) - r n := by
    rw [abs_of_nonneg (sub_nonneg.mpr hnlow)]
    linarith
  refine ⟨n, ?_⟩
  rw [hdistEq]
  exact lt_of_le_of_lt habs hgap




private theorem cp_inverse_cloud_gives_source_fibre_density
    (Y : Set Plane) (hY : HasFLC Y)
    (φ : ℝ →ₗ[ℚ] ℚ) (n : RationalNormal)
    (hker : Module.finrank ℝ (normalDirection n) = 1) (b : ℝ) (ρ M : ℝ)
    (hImageFLC : HasFLC (deformPoint φ '' Y))
    (hρ : 0 < ρ) (hM : 4 * ρ < M)
    (hcloud : ∀ z : Plane, normalEval n z = b →
      ∃ y ∈ deformPoint φ '' Y, normalEval n y = b ∧ dist z y < ρ)
    (hcoarse : ∀ x ∈ Y, ∀ y ∈ Y,
      dist (deformPoint φ x) (deformPoint φ y) < M / 2 → dist x y < M)
    (hreflect : ∀ x ∈ Y, ∀ y ∈ Y,
      dist (deformPoint φ x) (deformPoint φ y) < M / 2 →
        (normalEval n (deformPoint φ x - deformPoint φ y) = 0 ↔
          normalEval n (x - y) = 0))
    (hvector : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → dist x y < M →
      ‖deformPoint φ (x - y) - (x - y)‖ < ‖x - y‖) :
    ∃ a ∈ Y, normalEval n (deformPoint φ a) = b ∧
      ∀ z : Plane, normalEval n z = normalEval n a →
        ∃ w ∈ Y, normalEval n w = normalEval n a ∧ dist z w < M := by
  classical
  let ψ := cp_rationalNormalFunctional n
  have hψeval (x : Plane) : ψ x = normalEval n x := cp_rationalNormalFunctional_eq_eval n x
  have hkerψ : Module.finrank ℝ (LinearMap.ker ψ) = 1 := by
    change Module.finrank ℝ (normalDirection n) = 1
    exact hker
  obtain ⟨e, τ, he, hψe, hτe, hrep⟩ :=
    cp_exists_unit_kernel_coordinate ψ hkerψ
  obtain ⟨x₀, hx₀⟩ := cp_rationalNormalFunctional_surjective n b
  have hx₀level : ψ x₀ = b := by simpa [ψ] using hx₀
  let B : Set Plane := {y | y ∈ deformPoint φ '' Y ∧ ψ y = b}
  let U : Set ℝ := (fun y : Plane => τ (y - x₀)) '' B
  have hUfinite : ∀ a c : ℝ, (U ∩ Set.Icc a c).Finite := by
    intro a c
    let R : ℝ := max |a| |c|
    let Q : Set Plane := Metric.closedBall x₀ (R + 1)
    have hQbounded : Bornology.IsBounded Q := Metric.isBounded_closedBall
    have hImgFinite : ((deformPoint φ '' Y) ∩ Q).Finite := hImageFLC.1 Q hQbounded
    have hcoord_image :
        (U ∩ Set.Icc a c) ⊆ (fun y : Plane => τ (y - x₀)) ''
          (B ∩ Q) := by
      rintro t ⟨⟨y, hyB, rfl⟩, hta, htc⟩
      have hycoord : y = x₀ + (τ (y - x₀)) • e := by
        apply cp_affine_level_eq_kernel_coordinate (ψ := ψ)
        exact hyB.2.trans hx₀level.symm
        exact hrep
      have haR : -R ≤ a := (abs_le.mp (le_max_left |a| |c|)).1
      have hcR : c ≤ R := (abs_le.mp (le_max_right |a| |c|)).2
      have htnorm : |τ (y - x₀)| ≤ R := by
        dsimp [R]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have hyQ : y ∈ Q := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        rw [hycoord]
        have hcancel : x₀ + (τ (y - x₀)) • e - x₀ = (τ (y - x₀)) • e := by abel
        rw [hcancel]
        have : ‖(τ (y - x₀)) • e‖ = |τ (y - x₀)| := by
          rw [norm_smul, he, Real.norm_eq_abs, mul_one]
        rw [this]
        linarith [norm_nonneg x₀]
      exact ⟨y, ⟨hyB, hyQ⟩, rfl⟩
    have hBfinite : (B ∩ Q).Finite := by
      apply hImgFinite.subset
      rintro y ⟨hyB, hyQ⟩
      exact ⟨hyB.1, hyQ⟩
    exact (hBfinite.image (fun y : Plane => τ (y - x₀))).subset hcoord_image
  have hUdense : ∀ t : ℝ, ∃ s ∈ U, |t - s| < ρ := by
    intro t
    let z := x₀ + t • e
    have hzlevel : normalEval n z = b := by
      rw [← hψeval, map_add, map_smul, hψe, smul_zero, hx₀level, add_zero]
    obtain ⟨y, hyImg, hyLevel, hdist⟩ := hcloud z hzlevel
    have hyψ : ψ y = b := by simpa [hψeval] using hyLevel
    have hycoord : y = x₀ + (τ (y - x₀)) • e := by
      apply cp_affine_level_eq_kernel_coordinate (ψ := ψ)
      exact hyψ.trans hx₀level.symm
      exact hrep
    let s := τ (y - x₀)
    refine ⟨s, ?_, ?_⟩
    · exact ⟨y, ⟨hyImg, hyψ⟩, rfl⟩
    · have hdist' : dist (x₀ + t • e) (x₀ + s • e) < ρ := by
        change dist (x₀ + t • e) y < ρ at hdist
        rw [hycoord] at hdist
        exact hdist
      have hdistEq : dist (x₀ + t • e) (x₀ + s • e) = |t - s| := by
        rw [dist_eq_norm]
        have hdiff : (x₀ + t • e) - (x₀ + s • e) = (t - s) • e := by module
        rw [hdiff, norm_smul, he, Real.norm_eq_abs, mul_one]
      rw [hdistEq] at hdist'
      exact hdist'
  have hfiniteBounded : ∀ Q : Set ℝ, Bornology.IsBounded Q → (U ∩ Q).Finite := by
    intro Q hQ
    obtain ⟨r, hr⟩ := hQ.subset_closedBall 0
    have hsub : U ∩ Q ⊆ U ∩ Set.Icc (-r) r := by
      rintro t ⟨htU, htQ⟩
      have hnorm : ‖t - 0‖ ≤ r := hr htQ
      rw [Real.norm_eq_abs, sub_zero] at hnorm
      exact ⟨htU, abs_le.mp hnorm⟩
    exact (hUfinite (-r) r).subset hsub
  have habove : ∀ r : ℝ, ∃ a ∈ U, r < a := by
    intro r
    obtain ⟨a, ha, hdist⟩ := hUdense (r + 2 * ρ)
    have := (abs_lt.mp hdist).2
    exact ⟨a, ha, by linarith⟩
  have hbelow : ∀ r : ℝ, ∃ a ∈ U, a < r := by
    intro r
    obtain ⟨a, ha, hdist⟩ := hUdense (r - 2 * ρ)
    have := (abs_lt.mp hdist).1
    exact ⟨a, ha, by linarith⟩
  have hfiniteIcc : ∀ a c : ℝ, (U ∩ Set.Icc a c).Finite := fun a c => hUfinite a c
  obtain ⟨u, huRange, huStrict⟩ := cp_exists_ordered_integer_chain U hfiniteIcc habove hbelow
  have huGap : ∀ k : ℤ, u k < u (k + 1) ∧ u (k + 1) - u k < 2 * ρ := by
    intro k
    have hukU : u k ∈ U := by rw [← huRange]; exact ⟨k, rfl⟩
    obtain ⟨s, hsU, hdist⟩ := hUdense (u k + ρ)
    have hks : u k < s := by have := (abs_lt.mp hdist).2; linarith
    have hsb : s < u k + 2 * ρ := by have := (abs_lt.mp hdist).1; linarith
    obtain ⟨m, rfl⟩ := Set.mem_range.mp (huRange ▸ hsU)
    have hkm : k < m := huStrict.lt_iff_lt.mp hks
    have hkn : k + 1 ≤ m := by omega
    have hnext : u (k + 1) ≤ u m := huStrict.monotone hkn
    exact ⟨huStrict (by omega), by linarith⟩
  have hvWitness : ∀ k : ℤ, ∃ a : Plane, a ∈ Y ∧
      deformPoint φ a = x₀ + (u k) • e := by
    intro k
    have hukU : u k ∈ U := by rw [← huRange]; exact ⟨k, rfl⟩
    obtain ⟨y, hyB, hcoord⟩ := hukU
    obtain ⟨a, haY, hya⟩ := hyB.1
    refine ⟨a, haY, ?_⟩
    have hyrepr : y = x₀ + (τ (y - x₀)) • e := by
      apply cp_affine_level_eq_kernel_coordinate (ψ := ψ)
      exact hyB.2.trans hx₀level.symm
      exact hrep
    calc
      deformPoint φ a = y := hya
      _ = x₀ + (τ (y - x₀)) • e := hyrepr
      _ = x₀ + (u k) • e := by
        change τ (y - x₀) = u k at hcoord
        exact congrArg (fun t : ℝ => x₀ + t • e) hcoord
  let v : ℤ → Plane := fun k => Classical.choose (hvWitness k)
  have hvY : ∀ k : ℤ, v k ∈ Y := fun k => (Classical.choose_spec (hvWitness k)).1
  have hvImage : ∀ k : ℤ, deformPoint φ (v k) = x₀ + (u k) • e := by
    intro k
    exact (Classical.choose_spec (hvWitness k)).2
  let f : Plane →+ Plane := (deformPointLinear φ).toAddMonoidHom
  have hf (x : Plane) : f x = deformPoint φ x := rfl
  have himageGap : ∀ k : ℤ, dist (f (v (k + 1))) (f (v k)) < M / 2 := by
    intro k
    rw [hf, hf, hvImage, hvImage]
    have hgap := huGap k
    have hdist : dist (x₀ + u (k + 1) • e) (x₀ + u k • e) = u (k + 1) - u k := by
      rw [dist_eq_norm]
      have hdiff : (x₀ + u (k + 1) • e) - (x₀ + u k • e) =
          (u (k + 1) - u k) • e := by module
      rw [hdiff, norm_smul, he, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hgap.1), mul_one]
    rw [hdist]
    linarith
  have hcoarse' : ∀ x ∈ Y, ∀ y ∈ Y,
      dist (f x) (f y) < M / 2 → dist x y < M := by
    intro x hx y hy hxy
    simpa [hf] using hcoarse x hx y hy hxy
  have hreflect' : ∀ x ∈ Y, ∀ y ∈ Y,
      dist (f x) (f y) < M / 2 →
        (ψ (f x - f y) = 0 ↔ ψ (x - y) = 0) := by
    intro x hx y hy hxy
    have h := hreflect x hx y hy (by simpa [hf] using hxy)
    simpa only [hψeval, hf] using h
  have hvector' : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → dist x y < M →
      ‖f (x - y) - (x - y)‖ < ‖x - y‖ := by
    intro x hx y hy hne hxy
    simpa [hf] using hvector x hx y hy hne hxy
  have hvImage' : ∀ k : ℤ, f (v k) = x₀ + (u k) • e := by
    intro k
    rw [hf, hvImage]
  have hLift := cp_lifted_chain_preserves_fibre_density Y hY f ψ e τ v u x₀ M
    he hψe hτe hrep hvY hvImage' huStrict himageGap hcoarse' hreflect' hvector'
  refine ⟨v 0, hvY 0, ?_, ?_⟩
  · rw [← hψeval, hvImage 0, map_add, map_smul, hψe, smul_zero, hx₀level, add_zero]
  · intro z hz
    have hzψ : ψ (z - v 0) = 0 := by
      rw [map_sub, hψeval, hψeval, hz, sub_self]
    obtain ⟨k, hdist⟩ := hLift.2 z hzψ
    refine ⟨v k, hvY k, ?_, hdist⟩
    have hsame := hLift.1 k
    rw [map_sub] at hsame
    rw [← hψeval, ← hψeval]
    exact sub_eq_zero.mp hsame




private theorem cp_image_line_excludes_proper_vertices
    (C D Y : Set Plane) (f : Plane →+ Plane) (π : Plane →ₗ[ℝ] ℝ)
    (a b : Plane) (M : ℝ)
    (hvertices : Tiling.Polygonal.properVertices D =
      f '' Tiling.Polygonal.properVertices C)
    (hprovenance : Tiling.Polygonal.properVertices C ⊆ Y)
    (hdisj : Disjoint {x : Plane | π x = π a} (Tiling.Polygonal.properVertices C))
    (hdense : ∀ z : Plane, π z = π b →
      ∃ w ∈ Y, π w = π a ∧ π (f w) = π b ∧ dist z (f w) < M / 2)
    (hreflect : ∀ v ∈ Y, ∀ w ∈ Y, dist (f v) (f w) < M / 2 →
      (π (f v - f w) = 0 ↔ π (v - w) = 0)) :
    Disjoint {x : Plane | π x = π b} (Tiling.Polygonal.properVertices D) := by
  rw [Set.disjoint_left]
  intro z hzline hzvertex
  rw [hvertices] at hzvertex
  obtain ⟨v, hv, rfl⟩ := hzvertex
  obtain ⟨w, hwY, hwline, hwimage, hdist⟩ := hdense (f v) hzline
  have hzero : π (f v - f w) = 0 := by
    rw [map_sub, hzline, hwimage, sub_self]
  have hsourcezero := (hreflect v (hprovenance hv) w hwY hdist).mp hzero
  have hvline : π v = π a := by
    rw [map_sub, hwline] at hsourcezero
    exact sub_eq_zero.mp hsourcezero
  exact Set.disjoint_left.mp hdisj hvline hv


/-- A locally straight frontier germ on a line with no proper vertex anywhere on that line
propagates to the entire line. -/
/- Private construction work, not an additional public interface. The frozen
   declarations below remain provisional while owned or predecessor holes remain. -/

private theorem cp_det_ne_zero_of_independent (u v : Plane)
    (h : LinearIndependent ℝ ![u, v]) :
    u.re * v.im - u.im * v.re ≠ 0 := by
  intro hd
  have h₁ : v.im • u = u.im • v := by
    apply Complex.ext <;> simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
    · nlinarith
    · ring
  have him := h.eq_zero_of_pair' h₁
  have h₂ : v.re • u = u.re • v := by
    apply Complex.ext <;> simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
    · ring
    · nlinarith
  have hre := h.eq_zero_of_pair' h₂
  have hu : u = 0 := Complex.ext (by simpa using hre.2) (by simpa using him.2)
  exact h.ne_zero 0 hu

private theorem cp_independent_of_det_ne_zero (u v : Plane)
    (hd : u.re * v.im - u.im * v.re ≠ 0) :
    LinearIndependent ℝ ![u, v] := by
  rw [LinearIndependent.pair_iffₛ]
  intro s t s' t' he
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    smul_eq_mul] at hr hi
  have hs : (s - s') * (u.re * v.im - u.im * v.re) = 0 := by
    nlinarith [congrArg (fun x => x * v.im) hr, congrArg (fun x => x * v.re) hi]
  have ht : (t - t') * (u.re * v.im - u.im * v.re) = 0 := by
    nlinarith [congrArg (fun x => x * u.im) hr, congrArg (fun x => x * u.re) hi]
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hd),
    sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hd)⟩

private theorem cp_finite_independence_control (u v : Plane)
    (h : LinearIndependent ℝ ![u, v]) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        LinearIndependent ℝ ![deformPoint φ u, deformPoint φ v] := by
  classical
  let p : (ℝ × ℝ) × (ℝ × ℝ) := ((u.re, u.im), (v.re, v.im))
  let d : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun q => q.1.1 * q.2.2 - q.1.2 * q.2.1
  have hd : d p ≠ 0 := cp_det_ne_zero_of_independent u v h
  have hc : ContinuousAt d p := by dsimp [d]; fun_prop
  have ho : {q | d q ≠ 0} ∈ 𝓝 p := hc.preimage_mem_nhds (isOpen_ne.mem_nhds hd)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp ho
  refine ⟨{u.re, u.im, v.re, v.im}, ε, hε, ?_⟩
  intro φ hφ
  have ha : |(φ u.re : ℝ) - u.re| < ε := hφ.2 _ (by simp)
  have hb' : |(φ u.im : ℝ) - u.im| < ε := hφ.2 _ (by simp)
  have hc' : |(φ v.re : ℝ) - v.re| < ε := hφ.2 _ (by simp)
  have hd' : |(φ v.im : ℝ) - v.im| < ε := hφ.2 _ (by simp)
  apply cp_independent_of_det_ne_zero
  change d (((φ u.re : ℝ), (φ u.im : ℝ)), ((φ v.re : ℝ), (φ v.im : ℝ))) ≠ 0
  apply hb
  simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, p]
  exact ⟨⟨ha, hb'⟩, ⟨hc', hd'⟩⟩

private theorem cp_lattice_of_pair_periods (D : Set Plane) (u v : Plane)
    (h : LinearIndependent ℝ ![u, v])
    (hu : u ∈ Tiling.Polygonal.periodGroup D)
    (hv : v ∈ Tiling.Polygonal.periodGroup D) : IsLatticePeriodic D := by
  refine ⟨⟨![u, v], h⟩, ?_⟩
  change AddSubgroup.closure (Set.range ![u, v]) ≤ Tiling.Polygonal.periodGroup D
  rw [AddSubgroup.closure_le]
  rintro x ⟨i, rfl⟩
  fin_cases i <;> assumption

private theorem cp_sameGerm_trans {D E G : Set Plane} {x y z : Plane}
    (hDE : Tiling.Polygonal.SameGermAt D x E y)
    (hEG : Tiling.Polygonal.SameGermAt E y G z) :
    Tiling.Polygonal.SameGermAt D x G z := by
  have ht : Tendsto (fun q : Plane => q + (y - x)) (𝓝 x) (𝓝 y) := by
    have hxy : x + (y - x) = y := by abel
    have hc : Continuous (fun q : Plane => q + (y - x)) := by fun_prop
    have hh := hc.tendsto x
    change Tendsto (fun q : Plane => q + (y - x)) (𝓝 x) (𝓝 (x + (y - x))) at hh
    rwa [hxy] at hh
  have he := ht.eventually hEG.mem_iff
  apply Filter.Eventually.set_eq
  filter_upwards [hDE.mem_iff, he] with q hq heq
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hq heq ⊢
  have hxy : -(x - y) + q = q + (y - x) := by abel
  have hyz : -(y - z) + (q + (y - x)) = -(x - z) + q := by abel
  rw [hxy] at hq
  rw [hyz] at heq
  exact hq.trans heq

private theorem cp_sameGerm_symm {D E : Set Plane} {x y : Plane}
    (hDE : Tiling.Polygonal.SameGermAt D x E y) :
    Tiling.Polygonal.SameGermAt E y D x := by
  have ht : Tendsto (fun q : Plane => q + (x - y)) (𝓝 y) (𝓝 x) := by
    have hyx : y + (x - y) = x := by abel
    have hc : Continuous (fun q : Plane => q + (x - y)) := by fun_prop
    have hh := hc.tendsto y
    change Tendsto (fun q : Plane => q + (x - y)) (𝓝 y) (𝓝 (y + (x - y))) at hh
    rwa [hyx] at hh
  have he := ht.eventually hDE.mem_iff
  apply Filter.Eventually.set_eq
  filter_upwards [he] with q hq
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hq ⊢
  have hxy : -(x - y) + (q + (x - y)) = q := by abel
  have hyx : -(y - x) + q = q + (x - y) := by abel
  rw [hxy] at hq
  rw [hyx]
  exact hq.symm

private theorem cp_sameGerm_of_period {D : Set Plane} {u : Plane}
    (hu : u ∈ Tiling.Polygonal.periodGroup D) (x : Plane) :
    Tiling.Polygonal.SameGermAt D x D (x + u) := by
  have hn := AddAction.mem_stabilizer_iff.mp
    ((Tiling.Polygonal.periodGroup D).neg_mem hu)
  have hxy : x - (x + u) = -u := by abel
  unfold Tiling.Polygonal.SameGermAt
  rw [hxy, hn]
  rfl

private theorem cp_deform_vadd (φ : ℝ →ₗ[ℚ] ℚ) (u : Plane) (S : Set Plane) :
    deformPoint φ '' (u +ᵥ S) = deformPoint φ u +ᵥ (deformPoint φ '' S) := by
  ext x
  constructor
  · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨deformPoint φ s, ⟨s, hs, rfl⟩, ((deformPointLinear φ).map_add u s).symm⟩
  · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨u + s, ⟨s, hs, rfl⟩, (deformPointLinear φ).map_add u s⟩

private theorem cp_transported_period_germ (φ : ℝ →ₗ[ℚ] ℚ)
    {D G : Set Plane} {u v : Plane} (hu : u ∈ Tiling.Polygonal.periodGroup D)
    (hv : Tiling.Polygonal.SameGermAt D v G (deformPoint φ v))
    (hvu : Tiling.Polygonal.SameGermAt D (v + u) G (deformPoint φ (v + u))) :
    Tiling.Polygonal.SameGermAt G (deformPoint φ v) G
      (deformPoint φ v + deformPoint φ u) := by
  have hh := cp_sameGerm_trans (cp_sameGerm_symm hv)
    (cp_sameGerm_trans (cp_sameGerm_of_period hu v) hvu)
  have ha := (deformPointLinear φ).map_add v u
  change deformPoint φ (v + u) = deformPoint φ v + deformPoint φ u at ha
  rwa [ha] at hh

private theorem cp_image_properVertices_period (φ : ℝ →ₗ[ℚ] ℚ)
    {D : Set Plane} {u : Plane} (hu : u ∈ Tiling.Polygonal.periodGroup D) :
    deformPoint φ u +ᵥ (deformPoint φ '' Tiling.Polygonal.properVertices D) =
      deformPoint φ '' Tiling.Polygonal.properVertices D := by
  have hs : u +ᵥ Tiling.Polygonal.properVertices D = Tiling.Polygonal.properVertices D := by
    rw [← Tiling.Polygonal.properVertices_vadd D u, AddAction.mem_stabilizer_iff.mp hu]
  rw [← cp_deform_vadd, hs]

private theorem cp_eq_univ_of_all_periods {D : Set Plane} (hne : D.Nonempty)
    (hperiod : ∀ u : Plane, u ∈ Tiling.Polygonal.periodGroup D) : D = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨x, hx⟩ := hne
  have hp := AddAction.mem_stabilizer_iff.mp (hperiod (y - x))
  rw [← hp]
  exact ⟨x, hx, by simp⟩

private theorem cp_regularSupport_nonempty (K : PolygonalRegion) {S : Set Plane}
    (hS : S.Nonempty) : (Tiling.Polygonal.regularSupport K S).Nonempty := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hop : IsOpen (Tiling.Polygonal.openUnion K S) := by
    apply isOpen_iUnion
    intro t
    exact (Homeomorph.addLeft (t : Plane)).isOpenMap _ isOpen_interior
  have hu : s + k ∈ Tiling.Polygonal.openUnion K S := by
    apply Set.mem_iUnion.mpr
    exact ⟨⟨s, hs⟩, ⟨k, hk, rfl⟩⟩
  exact ⟨s + k, interior_maximal subset_closure hop hu⟩

/- The canonical quantitative frontier-level provider gives an actual intrinsic endpoint;
   the same support bound recovers the fixed decorated radius used before φ is chosen. -/
private theorem cp_frontier_level_decoratedDense_of_bound (K : PolygonalRegion) (S : Set Plane)
    (W : Finset Plane) (hdec : Decorates K W)
    (hp : Tiling.IsPacking K.prototileFamily (K.placements S)) (hflc : HasFLC S)
    (B : ℝ) (hbound : ∀ z ∈ K.support, ‖z‖ ≤ B)
    (π : Plane →ₗ[ℝ] ℝ) (a e : Plane) (he : e ≠ 0) (hπe : π e = 0)
    (hline : {y | π y = π a} ⊆ frontier (Tiling.Polygonal.regularSupport K S)) :
    ∀ x : Plane, π x = π a →
      ∃ w ∈ decoratedCloud W S, π w = π a ∧ dist x w < 2 * B + ‖e‖ + 2 := by
  classical
  intro x hx
  obtain ⟨v, q, hv, hq, hlevel, hqx⟩ :=
    Tiling.Polygonal.frontierLevel_has_intrinsicVertex_of_supportBound
      K S hp π e he hπe B hbound x (by
        intro y hy
        exact hline (hy.trans hx))
  have hvSupport : v ∈ K.support := by
    obtain ⟨T⟩ := K.isPolygonal
    obtain ⟨t, ht, hvt⟩ := hv T
    rw [← T.sUnion_eq]
    exact Set.mem_sUnion.mpr ⟨t, ht, extremePoints_subset hvt⟩
  have hW := decorates_intrinsicVertices K W hdec
  refine ⟨v + q, ⟨v, hW hv, q, hq, rfl⟩, hlevel.trans hx, ?_⟩
  have hdv : dist q (v + q) ≤ B := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_right]
    exact hbound v hvSupport
  have hdist := dist_triangle x q (v + q)
  rw [dist_comm x q] at hdist
  linarith

private theorem cp_frontier_level_decoratedDense (K : PolygonalRegion) (S : Set Plane)
    (W : Finset Plane) (hdec : Decorates K W)
    (hp : Tiling.IsPacking K.prototileFamily (K.placements S)) (hflc : HasFLC S)
    (π : Plane →ₗ[ℝ] ℝ) (a e : Plane) (he : e ≠ 0) (hπe : π e = 0)
    (hline : {y | π y = π a} ⊆ frontier (Tiling.Polygonal.regularSupport K S)) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : Plane, π x = π a →
      ∃ w ∈ decoratedCloud W S, π w = π a ∧ dist x w < A := by
  obtain ⟨B, hB, hbound⟩ := K.isPolygonal.isCompact.isBounded.exists_pos_norm_le
  exact ⟨2 * B + ‖e‖ + 2, by positivity,
    cp_frontier_level_decoratedDense_of_bound K S W hdec hp hflc B hbound π a e he hπe hline⟩


private theorem cp_open_local_level_halfPlane (ψ : Plane →L[ℝ] ℝ)
    {D : Set Plane} {x : Plane} {r : ℝ} (hDopen : IsOpen D)
    (hDreg : interior (closure D) = D) (hr : 0 < r)
    (hboundary : ∀ y ∈ Metric.ball x r, (y ∈ frontier D ↔ ψ y = ψ x)) :
    D =ᶠ[𝓝 x] {y | ψ x < ψ y} ∨ D =ᶠ[𝓝 x] {y | ψ y < ψ x} := by
  have hclreg : closure (interior (closure D)) = closure D := by rw [hDreg]
  have hf : frontier (closure D) = frontier D := by
    simp only [frontier, closure_closure, hDreg, hDopen.interior_eq]
  have hx : x ∈ frontier (closure D) := by
    rw [hf]
    exact (hboundary x (Metric.mem_ball_self hr)).mpr rfl
  have hb : ∀ y ∈ Metric.ball x r, (y ∈ frontier (closure D) ↔ ψ y = ψ x) := by
    simpa only [hf] using hboundary
  have hs := Tiling.local_levelSet_dichotomy ψ hr hclreg hx hb
  have hball : ∀ᶠ y in 𝓝 x, y ∈ Metric.ball x r := Metric.ball_mem_nhds x hr
  have hnotFront {y : Plane} (hy : y ∈ D) : y ∉ frontier D := by
    have hi : y ∈ interior D := by rwa [hDopen.interior_eq]
    exact fun h => Set.disjoint_left.mp disjoint_interior_frontier hi h
  rcases hs with hs | hs
  · left
    apply Filter.Eventually.set_eq
    filter_upwards [hball] with y hyball
    constructor
    · intro hyD
      rcases lt_trichotomy (ψ y) (ψ x) with hlt | heq | hgt
      · exact False.elim (interior_subset (hs.2 ⟨hyball, hlt⟩) (subset_closure hyD))
      · exact False.elim (hnotFront hyD ((hboundary y hyball).mpr heq))
      · exact hgt
    · intro hy
      simpa only [hDreg] using hs.1 ⟨hyball, hy⟩
  · right
    apply Filter.Eventually.set_eq
    filter_upwards [hball] with y hyball
    constructor
    · intro hyD
      rcases lt_trichotomy (ψ y) (ψ x) with hlt | heq | hgt
      · exact hlt
      · exact False.elim (hnotFront hyD ((hboundary y hyball).mpr heq))
      · exact False.elim (interior_subset (hs.1 ⟨hyball, hgt⟩) (subset_closure hyD))
    · intro hy
      simpa only [hDreg] using hs.2 ⟨hyball, hy⟩

private theorem cp_positive_negative_germs_ne (ψ : Plane →L[ℝ] ℝ)
    (hψ : Function.Surjective ψ) (x : Plane) :
    ¬ ({y : Plane | ψ x < ψ y} =ᶠ[𝓝 x] {y : Plane | ψ y < ψ x}) := by
  intro h
  obtain ⟨v, hv⟩ := hψ 1
  have hc : Continuous (fun t : ℝ => x + t • v) := by fun_prop
  have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  have hh := ht.eventually h.mem_iff
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hh
  have hε2 : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  have hbad := he hε2
  change (ψ x < ψ (x + (ε / 2) • v) ↔ ψ (x + (ε / 2) • v) < ψ x) at hbad
  simp only [map_add, map_smul, hv, smul_eq_mul, mul_one] at hbad
  exact (not_lt_of_ge (by linarith : ψ x ≤ ψ x + ε / 2))
    (hbad.mp (by linarith : ψ x < ψ x + ε / 2))

private theorem cp_level_side_constant (ψ : Plane →L[ℝ] ℝ)
    (hψ : Function.Surjective ψ) (a : Plane) (D : Set Plane)
    (hside : ∀ x : Plane, ψ x = ψ a →
      D =ᶠ[𝓝 x] {y | ψ a < ψ y} ∨ D =ᶠ[𝓝 x] {y | ψ y < ψ a}) :
    (∀ x : Plane, ψ x = ψ a → D =ᶠ[𝓝 x] {y | ψ a < ψ y}) ∨
      (∀ x : Plane, ψ x = ψ a → D =ᶠ[𝓝 x] {y | ψ y < ψ a}) := by
  let U : Set Plane := {x | D =ᶠ[𝓝 x] {y | ψ a < ψ y}}
  let V : Set Plane := {x | D =ᶠ[𝓝 x] {y | ψ y < ψ a}}
  have hu : IsOpen U := by
    simp only [U, Filter.eventuallyEq_set]
    exact isOpen_setOfPred_eventually_nhds
  have hv : IsOpen V := by
    simp only [V, Filter.eventuallyEq_set]
    exact isOpen_setOfPred_eventually_nhds
  have hconn : IsPreconnected {x : Plane | ψ x = ψ a} :=
    (convex_hyperplane ψ.toLinearMap.isLinear (ψ a)).isPreconnected
  have hcover : {x : Plane | ψ x = ψ a} ⊆ U ∪ V := fun x hx => hside x hx
  have hdisj : Disjoint ({x : Plane | ψ x = ψ a} ∩ U) V := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    have hh := hx.2.symm.trans hxV
    have hn := cp_positive_negative_germs_ne ψ hψ x
    have hxa : ψ x = ψ a := hx.1
    rw [hxa] at hn
    exact hn hh
  rcases hside a rfl with ha | ha
  · left
    intro x hx
    rcases hside x hx with hh | hh
    · exact hh
    · obtain ⟨y, hyline, hyU, hyV⟩ := hconn U V hu hv hcover ⟨a, rfl, ha⟩ ⟨x, hx, hh⟩
      exact False.elim (Set.disjoint_left.mp hdisj ⟨hyline, hyU⟩ hyV)
  · right
    intro x hx
    rcases hside x hx with hh | hh
    · obtain ⟨y, hyline, hyU, hyV⟩ := hconn U V hu hv hcover ⟨x, hx, hh⟩ ⟨a, rfl, ha⟩
      exact False.elim (Set.disjoint_left.mp hdisj ⟨hyline, hyU⟩ hyV)
    · exact hh

private theorem cp_mem_kernel_line (π : Plane →ₗ[ℝ] ℝ) (a x : Plane) :
    x ∈ a +ᵥ (LinearMap.ker π : Set Plane) ↔ π x = π a := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    change π (a + v) = π a
    have hv' : π v = 0 := hv
    rw [map_add, hv', add_zero]
  · intro hx
    refine ⟨x - a, ?_, ?_⟩
    · change π (x - a) = 0
      rw [map_sub, hx, sub_self]
    · simp [vadd_eq_add]

private theorem cp_positive_halfPlane_sameGerm (ψ : Plane →L[ℝ] ℝ) (x y : Plane) :
    Tiling.Polygonal.SameGermAt {q | ψ x < ψ q} x {q | ψ y < ψ q} y := by
  apply Filter.EventuallyEq.of_eq
  ext q
  change (q ∈ {q | ψ x < ψ q} ↔ q ∈ (x - y) +ᵥ {q | ψ y < ψ q})
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  change ψ x < ψ q ↔ ψ y < ψ (-(x - y) + q)
  rw [map_add, map_neg, map_sub]
  constructor <;> intro h <;> linarith

private theorem cp_negative_halfPlane_sameGerm (ψ : Plane →L[ℝ] ℝ) (x y : Plane) :
    Tiling.Polygonal.SameGermAt {q | ψ q < ψ x} x {q | ψ q < ψ y} y := by
  apply Filter.EventuallyEq.of_eq
  ext q
  change (q ∈ {q | ψ q < ψ x} ↔ q ∈ (x - y) +ᵥ {q | ψ q < ψ y})
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  change ψ q < ψ x ↔ ψ (-(x - y) + q) < ψ y
  rw [map_add, map_neg, map_sub]
  constructor <;> intro h <;> linarith

private theorem cp_uniform_germs_on_levels (ψ : Plane →L[ℝ] ℝ)
    (hψ : Function.Surjective ψ) (D E : Set Plane) (a b : Plane)
    (hD : ∀ x : Plane, ψ x = ψ a →
      D =ᶠ[𝓝 x] {q | ψ a < ψ q} ∨ D =ᶠ[𝓝 x] {q | ψ q < ψ a})
    (hE : ∀ y : Plane, ψ y = ψ b →
      E =ᶠ[𝓝 y] {q | ψ b < ψ q} ∨ E =ᶠ[𝓝 y] {q | ψ q < ψ b})
    (hab : Tiling.Polygonal.SameGermAt D a E b) :
    ∀ x y : Plane, ψ x = ψ a → ψ y = ψ b → Tiling.Polygonal.SameGermAt D x E y := by
  have hDs := cp_level_side_constant ψ hψ a D hD
  have hEs := cp_level_side_constant ψ hψ b E hE
  have hs {G H : Set Plane} {z : Plane} (h : G =ᶠ[𝓝 z] H) :
      Tiling.Polygonal.SameGermAt G z H z := by
    simpa only [Tiling.Polygonal.SameGermAt, sub_self, zero_vadd] using h
  rcases hDs with hDp | hDn <;> rcases hEs with hEp | hEn
  · intro x y hx hy
    have hDx := hs (hDp x hx)
    have hEy := hs (hEp y hy)
    rw [← hx] at hDx
    rw [← hy] at hEy
    exact cp_sameGerm_trans hDx
      (cp_sameGerm_trans (cp_positive_halfPlane_sameGerm ψ x y) (cp_sameGerm_symm hEy))
  · have hh := cp_sameGerm_trans (cp_sameGerm_symm (hs (hDp a rfl)))
      (cp_sameGerm_trans hab
        (cp_sameGerm_trans (hs (hEn b rfl)) (cp_negative_halfPlane_sameGerm ψ b a)))
    have he : {q | ψ a < ψ q} =ᶠ[𝓝 a] {q | ψ q < ψ a} := by
      simpa only [Tiling.Polygonal.SameGermAt, sub_self, zero_vadd] using hh
    exact False.elim (cp_positive_negative_germs_ne ψ hψ a he)
  · have hh := cp_sameGerm_trans (cp_sameGerm_symm (hs (hDn a rfl)))
      (cp_sameGerm_trans hab
        (cp_sameGerm_trans (hs (hEp b rfl)) (cp_positive_halfPlane_sameGerm ψ b a)))
    have he : {q | ψ q < ψ a} =ᶠ[𝓝 a] {q | ψ a < ψ q} := by
      simpa only [Tiling.Polygonal.SameGermAt, sub_self, zero_vadd] using hh
    exact False.elim (cp_positive_negative_germs_ne ψ hψ a he.symm)
  · intro x y hx hy
    have hDx := hs (hDn x hx)
    have hEy := hs (hEn y hy)
    rw [← hx] at hDx
    rw [← hy] at hEy
    exact cp_sameGerm_trans hDx
      (cp_sameGerm_trans (cp_negative_halfPlane_sameGerm ψ x y) (cp_sameGerm_symm hEy))

private theorem cp_straightLine_local_level (ψ : Plane →L[ℝ] ℝ)
    (hδ : Module.finrank ℝ (LinearMap.ker ψ.toLinearMap) = 1)
    {D : Set Plane} {a x : Plane}
    (hl : Tiling.Polygonal.IsStraightFrontierLine D (LinearMap.ker ψ.toLinearMap) a)
    (hx : ψ x = ψ a) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball x r, (y ∈ frontier D ↔ ψ y = ψ a) := by
  have hxline := (cp_mem_kernel_line ψ.toLinearMap a x).mpr hx
  have hxfront := hl.1 hxline
  have hxs : BoundaryLocallyStraightAt D x := by
    by_contra hn
    exact Set.disjoint_left.mp hl.2 hxline ⟨hxfront, hn⟩
  obtain ⟨L, hxL, hLdim, hlocal⟩ := hxs
  have hle : LinearMap.ker ψ.toLinearMap ≤ L.direction := by
    intro v hv
    have hv0 : ψ v = 0 := hv
    have hray : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      have hc : Continuous (fun t : ℝ => x + t • v) := by fun_prop
      simpa only [zero_smul, add_zero] using hc.tendsto 0
    have hall : ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ L := by
      filter_upwards [hray.eventually hlocal] with t ht
      apply ht.mp
      apply hl.1
      apply (cp_mem_kernel_line ψ.toLinearMap a (x + t • v)).mpr
      change ψ (x + t • v) = ψ a
      simp only [map_add, map_smul, hv0, smul_zero, add_zero, hx]
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hall
    have hεball : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
      linarith
    have hmem := L.vsub_mem_direction (hb hεball) hxL
    change (x + (ε / 2) • v) - x ∈ L.direction at hmem
    rw [add_sub_cancel_left] at hmem
    exact (L.direction.smul_mem_iff (ne_of_gt (half_pos hε))).mp hmem
  have hdir : LinearMap.ker ψ.toLinearMap = L.direction :=
    Submodule.eq_of_le_of_finrank_eq hle (hδ.trans hLdim.symm)
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨r, hr, ?_⟩
  intro y hy
  have hby : y ∈ frontier D ↔ y ∈ L := hb hy
  rw [hby]
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hxL y, ← hdir]
  change ψ (y - x) = 0 ↔ ψ y = ψ a
  rw [map_sub, hx, sub_eq_zero]

private theorem cp_germ_transports_local_level (ψ : Plane →ₗ[ℝ] ℝ)
    {D E : Set Plane} {x y : Plane}
    (hg : Tiling.Polygonal.SameGermAt D x E y)
    (hlevel : ∀ᶠ z in 𝓝 x, (z ∈ frontier D ↔ ψ z = ψ x)) :
    ∀ᶠ z in 𝓝 y, (z ∈ frontier E ↔ ψ z = ψ y) := by
  have hfront := Tiling.Polygonal.frontier_eventuallyEq_of_eventuallyEq hg
  have htranslated : ∀ᶠ z in 𝓝 x,
      (z ∈ frontier ((x - y) +ᵥ E) ↔ ψ z = ψ x) := by
    filter_upwards [hfront, hlevel] with z hz hl
    change (z ∈ frontier D) = (z ∈ frontier ((x - y) +ᵥ E)) at hz
    rw [← hz]
    exact hl
  have hfr : frontier ((x - y) +ᵥ E) = (x - y) +ᵥ frontier E := by
    exact ((Homeomorph.addLeft (x - y)).image_frontier E).symm
  have hc : Continuous (fun z : Plane => x - y + z) := continuous_const.add continuous_id
  have hpull : ∀ᶠ z in 𝓝 y,
      (x - y + z ∈ frontier ((x - y) +ᵥ E) ↔ ψ (x - y + z) = ψ x) := by
    have ht : Tendsto (fun z : Plane => x - y + z) (𝓝 y) (𝓝 x) := by
      simpa only [sub_add_cancel] using hc.tendsto y
    exact ht.eventually htranslated
  filter_upwards [hpull] with z hz
  rw [hfr, Set.mem_vadd_set_iff_neg_vadd_mem] at hz
  have hcancel : -(x - y) + (x - y + z) = z := by abel
  change (-(x - y) + (x - y + z) ∈ frontier E ↔ ψ (x - y + z) = ψ x) at hz
  rw [hcancel, map_add, map_sub] at hz
  convert hz using 1 <;> constructor <;> intro h <;> linarith


private theorem cp_straightLine_uniform_germs (ψ : Plane →L[ℝ] ℝ)
    (hψ : Function.Surjective ψ)
    (hδ : Module.finrank ℝ (LinearMap.ker ψ.toLinearMap) = 1)
    {D E : Set Plane} {a b : Plane}
    (hDo : IsOpen D) (hDr : interior (closure D) = D)
    (hEo : IsOpen E) (hEr : interior (closure E) = E)
    (hDl : Tiling.Polygonal.IsStraightFrontierLine D (LinearMap.ker ψ.toLinearMap) a)
    (hEl : Tiling.Polygonal.IsStraightFrontierLine E (LinearMap.ker ψ.toLinearMap) b)
    (hab : Tiling.Polygonal.SameGermAt D a E b) :
    ∀ x y : Plane, ψ x = ψ a → ψ y = ψ b → Tiling.Polygonal.SameGermAt D x E y := by
  apply cp_uniform_germs_on_levels ψ hψ D E a b ?_ ?_ hab
  · intro x hx
    obtain ⟨r, hr, hb⟩ := cp_straightLine_local_level ψ hδ hDl hx
    have hbx : ∀ y ∈ Metric.ball x r, (y ∈ frontier D ↔ ψ y = ψ x) := by
      simpa only [hx] using hb
    have hh := cp_open_local_level_halfPlane ψ hDo hDr hr hbx
    rwa [hx] at hh
  · intro y hy
    obtain ⟨r, hr, hb⟩ := cp_straightLine_local_level ψ hδ hEl hy
    have hby : ∀ x ∈ Metric.ball y r, (x ∈ frontier E ↔ ψ x = ψ y) := by
      simpa only [hy] using hb
    have hh := cp_open_local_level_halfPlane ψ hEo hEr hr hby
    rwa [hy] at hh

private theorem cp_complete_line_from_transport_data (ψ : Plane →L[ℝ] ℝ)
    (hψ : Function.Surjective ψ)
    (hδ : Module.finrank ℝ (LinearMap.ker ψ.toLinearMap) = 1)
    {D E : Set Plane} {a b : Plane}
    (hDo : IsOpen D) (hDr : interior (closure D) = D)
    (hEo : IsOpen E) (hEr : interior (closure E) = E)
    (hDl : Tiling.Polygonal.IsStraightFrontierLine D (LinearMap.ker ψ.toLinearMap) a)
    (hdisj : Disjoint {x : Plane | ψ x = ψ b} (Tiling.Polygonal.properVertices E))
    (hseed : ∃ x y : Plane, ψ x = ψ a ∧ ψ y = ψ b ∧
      Tiling.Polygonal.SameGermAt D x E y) :
    Tiling.Polygonal.IsStraightFrontierLine E (LinearMap.ker ψ.toLinearMap) b ∧
      ∀ x y : Plane, ψ x = ψ a → ψ y = ψ b → Tiling.Polygonal.SameGermAt D x E y := by
  obtain ⟨x₀, y₀, hx₀, hy₀, hg₀⟩ := hseed
  obtain ⟨r, hr, hball⟩ := cp_straightLine_local_level ψ hδ hDl hx₀
  have hlocal : ∀ᶠ z in 𝓝 x₀, (z ∈ frontier D ↔ ψ.toLinearMap z = ψ.toLinearMap x₀) := by
    filter_upwards [Metric.ball_mem_nhds x₀ hr] with z hz
    have hh := hball z hz
    change (z ∈ frontier D ↔ ψ z = ψ x₀)
    rwa [hx₀]
  have htarget := cp_germ_transports_local_level ψ.toLinearMap hg₀ hlocal
  have hfront : {x : Plane | ψ x = ψ b} ⊆ frontier E := by
    apply Tiling.Polygonal.straight_frontier_germ_propagates_on_line ψ.toLinearMap hδ E b hdisj
    refine ⟨y₀, hy₀, ?_⟩
    change ∀ᶠ z in 𝓝 y₀, (z ∈ frontier E ↔ ψ z = ψ b)
    change ∀ᶠ z in 𝓝 y₀, (z ∈ frontier E ↔ ψ z = ψ y₀) at htarget
    rwa [hy₀] at htarget
  have hline : b +ᵥ (LinearMap.ker ψ.toLinearMap : Set Plane) = {x : Plane | ψ x = ψ b} := by
    ext x
    exact cp_mem_kernel_line ψ.toLinearMap b x
  have hEl : Tiling.Polygonal.IsStraightFrontierLine E (LinearMap.ker ψ.toLinearMap) b := by
    exact ⟨by rwa [hline], by rwa [hline]⟩
  refine ⟨hEl, ?_⟩
  have hsideD : ∀ x : Plane, ψ x = ψ x₀ →
      D =ᶠ[𝓝 x] {z | ψ x₀ < ψ z} ∨ D =ᶠ[𝓝 x] {z | ψ z < ψ x₀} := by
    intro x hx
    obtain ⟨r, hr, hb⟩ := cp_straightLine_local_level ψ hδ hDl (hx.trans hx₀)
    have hb' : ∀ z ∈ Metric.ball x r, (z ∈ frontier D ↔ ψ z = ψ x) := by
      simpa only [hx, hx₀] using hb
    simpa only [hx] using cp_open_local_level_halfPlane ψ hDo hDr hr hb'
  have hsideE : ∀ y : Plane, ψ y = ψ y₀ →
      E =ᶠ[𝓝 y] {z | ψ y₀ < ψ z} ∨ E =ᶠ[𝓝 y] {z | ψ z < ψ y₀} := by
    intro y hy
    obtain ⟨r, hr, hb⟩ := cp_straightLine_local_level ψ hδ hEl (hy.trans hy₀)
    have hb' : ∀ z ∈ Metric.ball y r, (z ∈ frontier E ↔ ψ z = ψ y) := by
      simpa only [hy, hy₀] using hb
    simpa only [hy] using cp_open_local_level_halfPlane ψ hEo hEr hr hb'
  have hall := cp_uniform_germs_on_levels ψ hψ D E x₀ y₀ hsideD hsideE hg₀
  intro x y hx hy
  exact hall x y (hx.trans hx₀.symm) (hy.trans hy₀.symm)


/- The full-plane branch uses BOTH boundary species and nonempty status. This
   is reconstruction, not a suitable-carrier or stabilizer classification. -/
private theorem cp_full_of_no_boundary (K : PolygonalRegion) {S : Set Plane}
    (hS : S.Nonempty) (hp : Tiling.IsPacking K.prototileFamily (K.placements S))
    (hW : Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport K S) = ∅)
    (hl : ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 → ∀ a : Plane,
      ¬ Tiling.Polygonal.IsStraightFrontierLine (Tiling.Polygonal.regularSupport K S) δ a) :
    Tiling.Polygonal.regularSupport K S = Set.univ := by
  apply cp_eq_univ_of_all_periods (cp_regularSupport_nonempty K hS)
  intro u
  apply AddAction.mem_stabilizer_iff.mpr
  apply Tiling.Polygonal.properVertices_and_straightLines_determine_translate hS hS hp hp u
  · simp [hW]
  · intro v hv
    simp [hW] at hv
  · intro δ hδ a ha
    exact False.elim (hl δ hδ a ha)
  · intro δ hδ a ha
    exact False.elim (hl δ hδ a ha)



private theorem cp_polygonalRegion_eq_of_support_eq {K L : PolygonalRegion}
    (h : K.support = L.support) : K = L := by
  cases K
  cases L
  cases h
  rfl

private theorem cp_uniform_line_transport_packet
    (K : PolygonalRegion) (T : Set Plane)
    (hK : Tiling.RationalSlopes.HasRationalSlopes K) (hT : HasFLC T)
    (hDense : RelativeDense T)
    (hTile : TilesOn K T (Tiling.Polygonal.regularSupport K T)) :
    ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
      ∃ W : Finset Plane, Decorates K W ∧ 0 ∈ W ∧
      ∃ B : ℝ, 0 < B ∧ (∀ z ∈ K.support, ‖z‖ ≤ B) ∧
      ∃ N : Finset RationalNormal,
        (∀ δ : Submodule ℝ Plane, Tiling.Polygonal.HasBoundaryDirection K δ →
          ∃ n ∈ N, normalDirection n = δ) ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ ∧
            Decorates Kφ (W.image (deformPoint φ)) ∧
            (∀ z ∈ Kφ.support, ‖z‖ ≤ B) ∧
            (∀ δ : Submodule ℝ Plane, Tiling.Polygonal.HasBoundaryDirection Kφ δ ↔
              Tiling.Polygonal.HasBoundaryDirection K δ) ∧
            TilesOn Kφ (deformPoint φ '' T) (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' T)) ∧
            HasFLC (deformPoint φ '' T) ∧
            (∀ S ⊆ T, ∀ v ∈ decoratedCloud W T,
              Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K S) v
                (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) (deformPoint φ v)) ∧
            (∀ S ⊆ T, Tiling.Polygonal.properVertices
              (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) =
                deformPoint φ '' Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport K S)) ∧
            (∀ u ∈ decoratedCloud W T, ∀ v ∈ decoratedCloud W T,
              dist (deformPoint φ u) (deformPoint φ v) < (8 * B + 16) / 2 →
                dist u v < 8 * B + 16) ∧
            (∀ u ∈ decoratedCloud W T, ∀ v ∈ decoratedCloud W T,
              dist (deformPoint φ u) (deformPoint φ v) < (8 * B + 16) / 2 →
                ∀ n ∈ N, normalEval n (deformPoint φ u - deformPoint φ v) = 0 ↔
                  normalEval n (u - v) = 0) ∧
            (∀ u ∈ decoratedCloud W T, ∀ v ∈ decoratedCloud W T,
              dist u v < 8 * B + 16 → u ≠ v →
                ‖deformPoint φ (u - v) - (u - v)‖ < ‖u - v‖ ∧
                  ‖deformPoint φ (u - v)‖ < ‖u - v‖ + 1) := by
  classical
  obtain ⟨P, hP, W, hW, hW0, F₀, ε₀, hε₀, hFT⟩ :=
    flcRationalDeformation K T hK hT hDense hTile
  obtain ⟨Q, hQ, V, hV, hV0, B₁, L, hB₁, hL, F₁, ε₁, hε₁, hRG⟩ :=
    rationalPolygon_uniformBoundaryControl K hK
  obtain ⟨F₂, ε₂, hε₂, hCode⟩ := polyhedralDeformation_independentOfCode K P Q hP hQ
  obtain ⟨B₀, hB₀, hBound₀⟩ := K.isPolygonal.isCompact.isBounded.exists_pos_norm_le
  let B := max B₀ B₁
  have hB : 0 < B := lt_of_lt_of_le hB₀ (le_max_left _ _)
  have hBound : ∀ z ∈ K.support, ‖z‖ ≤ B := by
    intro z hz
    exact (hBound₀ z hz).trans (le_max_left _ _)
  obtain ⟨N, hN⟩ := cp_finite_boundary_normals K hK
  let Y := decoratedCloud W T
  have hY : HasFLC Y := by
    change HasFLC ((W : Set Plane) + T)
    rw [add_comm]
    exact hT.add_finset W
  have hYDense : RelativeDense Y := by
    obtain ⟨ρ, hρ, hρT⟩ := hDense
    refine ⟨ρ, hρ, ?_⟩
    intro z
    obtain ⟨t, ht, hdist⟩ := hρT z
    exact ⟨t, ⟨0, hW0, t, ht, zero_add _⟩, hdist⟩
  have hM : 0 < 8 * B + 16 := by positivity
  obtain ⟨F₃, ε₃, hε₃, hGaps⟩ := cp_deformation_bounded_gap_tests Y hY (8 * B + 16) hM
  obtain ⟨F₄, ε₄, hε₄, hMetric⟩ :=
    approximation_boundedMetricAndRelationControl Y hY hYDense (8 * B + 16) 1 N hM zero_lt_one
  let F := F₀ ∪ F₁ ∪ F₂ ∪ F₃ ∪ F₄
  let ε := min ε₀ (min ε₁ (min ε₂ (min ε₃ ε₄)))
  have hε : 0 < ε := lt_min hε₀ (lt_min hε₁ (lt_min hε₂ (lt_min hε₃ hε₄)))
  have hsub₀ : F₀ ⊆ F := by intro t ht; simp [F, ht]
  have hsub₁ : F₁ ⊆ F := by intro t ht; simp [F, ht]
  have hsub₂ : F₂ ⊆ F := by intro t ht; simp [F, ht]
  have hsub₃ : F₃ ⊆ F := by intro t ht; simp [F, ht]
  have hsub₄ : F₄ ⊆ F := by intro t ht; simp [F, ht]
  refine ⟨P, hP, W, hW, hW0, B, hB, hBound, N, hN, F, ε, hε, ?_⟩
  intro φ hφ
  have hφ₀ := finiteApproximation_strengthen F₀ F ε₀ ε φ hsub₀ (min_le_left _ _) hφ
  have hφ₁ := finiteApproximation_strengthen F₁ F ε₁ ε φ hsub₁
    ((min_le_right _ _).trans (min_le_left _ _)) hφ
  have hφ₂ := finiteApproximation_strengthen F₂ F ε₂ ε φ hsub₂
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) hφ
  have hφ₃ := finiteApproximation_strengthen F₃ F ε₃ ε φ hsub₃
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) hφ
  have hφ₄ := finiteApproximation_strengthen F₄ F ε₄ ε φ hsub₄
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) hφ
  obtain ⟨Kφ, hKφP, hRat, hSlopes, hDec, hInj, hTileφ, hFLCφ, hGerm, hProper⟩ := hFT φ hφ₀
  obtain ⟨Kψ, hKψQ, hKψB, hEdges, hDirs⟩ := hRG φ hφ₁
  have hSupport : Kψ.support = Kφ.support := by rw [hKψQ, hKφP, hCode φ hφ₂]
  have hEq : Kψ = Kφ := cp_polygonalRegion_eq_of_support_eq hSupport
  subst Kψ
  obtain ⟨hYInj, hApprox, hCoarse, hReflect⟩ := hMetric φ hφ₄
  refine ⟨Kφ, hKφP, hDec, ?_, hDirs, hTileφ, hFLCφ, hGerm, hProper,
    hCoarse, hReflect, hGaps φ hφ₃⟩
  intro z hz
  have hzB : ‖z‖ ≤ B₁ := by simpa [Metric.mem_closedBall, dist_zero_right] using hKψB hz
  exact hzB.trans (le_max_right _ _)


private theorem cp_subfamily_packing {K : PolygonalRegion} {S T : Set Plane}
    (hST : S ⊆ T) (hp : Tiling.IsPacking K.prototileFamily (K.placements T)) :
    Tiling.IsPacking K.prototileFamily (K.placements S) := by
  exact hp.mono (fun p hp => hST hp)

private theorem cp_cloud_mono (W : Finset Plane) {S T : Set Plane} (hST : S ⊆ T) :
    decoratedCloud W S ⊆ decoratedCloud W T := by
  rintro q ⟨w, hw, s, hs, rfl⟩
  exact ⟨w, hw, s, hST hs, rfl⟩

private theorem cp_cloud_hasFLC (W : Finset Plane) {T : Set Plane} (hT : HasFLC T) :
    HasFLC (decoratedCloud W T) := by
  change HasFLC ((W : Set Plane) + T)
  rw [add_comm]
  exact hT.add_finset W

private theorem cp_cloud_image (W : Finset Plane) (S : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ) :
    deformPoint φ '' decoratedCloud W S =
      decoratedCloud (W.image (deformPoint φ)) (deformPoint φ '' S) := by
  ext z
  constructor
  · rintro ⟨q, ⟨w, hw, s, hs, rfl⟩, rfl⟩
    exact ⟨deformPoint φ w, Finset.mem_image.mpr ⟨w, hw, rfl⟩,
      deformPoint φ s, ⟨s, hs, rfl⟩, ((deformPointLinear φ).map_add w s).symm⟩
  · rintro ⟨wφ, hwφ, sφ, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hwφ
    exact ⟨w + s, ⟨w, hw, s, hs, rfl⟩, (deformPointLinear φ).map_add w s⟩


private theorem cp_forward_straight_line_under_controls
    (K Kφ : PolygonalRegion) (S Y : Set Plane) (W : Finset Plane)
    (hDec : Decorates K W) (hPack : Tiling.IsPacking K.prototileFamily (K.placements S))
    (hS : HasFLC S) (hY : HasFLC Y) (hCloud : decoratedCloud W S ⊆ Y)
    (B : ℝ) (hB : 0 < B) (hBound : ∀ z ∈ K.support, ‖z‖ ≤ B)
    (n : RationalNormal) (hδ : Module.finrank ℝ (normalDirection n) = 1)
    (φ : ℝ →ₗ[ℚ] ℚ)
    (hProper : Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) =
      deformPoint φ '' Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport K S))
    (hGerm : ∀ v ∈ Y, Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K S) v
      (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) (deformPoint φ v))
    (hReflect : ∀ u ∈ Y, ∀ v ∈ Y,
      dist (deformPoint φ u) (deformPoint φ v) < (8 * B + 16) / 2 →
        (normalEval n (deformPoint φ u - deformPoint φ v) = 0 ↔ normalEval n (u - v) = 0))
    (hVector : ∀ u ∈ Y, ∀ v ∈ Y, dist u v < 8 * B + 16 → u ≠ v →
      ‖deformPoint φ (u - v) - (u - v)‖ < ‖u - v‖ ∧
        ‖deformPoint φ (u - v)‖ < ‖u - v‖ + 1)
    (a : Plane)
    (hLine : Tiling.Polygonal.IsStraightFrontierLine (Tiling.Polygonal.regularSupport K S)
      (normalDirection n) a) :
    Tiling.Polygonal.IsStraightFrontierLine (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S))
      (normalDirection n) (deformPoint φ a) ∧
      ∀ x ∈ a +ᵥ (normalDirection n : Set Plane),
        Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K S) x
          (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) (deformPoint φ x) := by
  classical
  let π := cp_rationalNormalFunctional n
  let ψ : Plane →L[ℝ] ℝ := ⟨π, π.continuous_of_finiteDimensional⟩
  let f : Plane →+ Plane := (deformPointLinear φ).toAddMonoidHom
  let D := Tiling.Polygonal.regularSupport K S
  let E := Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)
  let ρ := 2 * B + 3
  have hρ : 0 < ρ := by positivity
  have hπnormal (z : Plane) : π z = normalEval n z := cp_rationalNormalFunctional_eq_eval n z
  have hψ : Function.Surjective ψ := cp_rationalNormalFunctional_surjective n
  obtain ⟨e, τ, he, hπe, hτe, hrep⟩ := cp_exists_unit_kernel_coordinate π hδ
  have he0 : e ≠ 0 := norm_pos_iff.mp (by rw [he]; exact zero_lt_one)
  have hfront : {z : Plane | π z = π a} ⊆ frontier D := by
    intro z hz
    exact hLine.1 ((cp_mem_kernel_line π a z).mpr hz)
  have hEndpoints : ∀ z : Plane, π z = π a →
      ∃ w ∈ decoratedCloud W S, π w = π a ∧ dist z w < ρ := by
    have hRadius : 2 * B + ‖e‖ + 2 = ρ := by rw [he]; dsimp [ρ]; ring
    simpa only [hRadius] using cp_frontier_level_decoratedDense_of_bound
      K S W hDec hPack hS B hBound π a e he0 hπe hfront
  have hDenseY : ∀ z : Plane, normalEval n z = normalEval n a →
      ∃ w ∈ Y, normalEval n w = normalEval n a ∧ dist z w < ρ := by
    intro z hz
    obtain ⟨w, hw, hwline, hdist⟩ := hEndpoints z (by simpa only [hπnormal] using hz)
    exact ⟨w, hCloud hw, by simpa only [hπnormal] using hwline, hdist⟩
  have hForwardCtrl : ∀ u ∈ Y, ∀ v ∈ Y, dist u v < 2 * ρ → u ≠ v →
      ‖deformPoint φ (u - v) - (u - v)‖ < ‖u - v‖ ∧
        ‖deformPoint φ (u - v)‖ < 2 * ρ + 1 := by
    intro u hu v hv hdist hne
    obtain ⟨herr, hnorm⟩ := hVector u hu v hv (by dsimp [ρ] at hdist; linarith) hne
    refine ⟨herr, ?_⟩
    rw [dist_eq_norm] at hdist
    linarith
  have hImageDense := deformPoint_lineCloud_dense_of_gapControl Y hY n hδ a ρ hρ hDenseY φ hForwardCtrl
  have hProvenance : Tiling.Polygonal.properVertices D ⊆ Y := by
    intro v hv
    obtain ⟨p, hp, s, hs, hvEq⟩ := Tiling.Polygonal.properVertexProvenance hPack v hv
    rw [hvEq]
    exact hCloud ⟨p, decorates_intrinsicVertices K W hDec hp, s, hs, rfl⟩
  have hDisj : Disjoint {z : Plane | π z = π a} (Tiling.Polygonal.properVertices D) := by
    rw [Set.disjoint_left]
    intro z hz hvertex
    exact Set.disjoint_left.mp hLine.2 ((cp_mem_kernel_line π a z).mpr hz) hvertex
  have hTargetDisj : Disjoint {z : Plane | π z = π (f a)} (Tiling.Polygonal.properVertices E) := by
    apply cp_image_line_excludes_proper_vertices D E Y f π a (f a) (8 * B + 16)
      hProper hProvenance hDisj
    · intro z hz
      have hz' : normalEval n z = normalEval n (deformPoint φ a) := by
        change π z = π (deformPoint φ a) at hz
        simpa only [hπnormal] using hz
      obtain ⟨w, hw, hwline, hwimage, hdist⟩ := hImageDense z hz'
      refine ⟨w, hw, ?_, ?_, ?_⟩
      · simpa only [hπnormal] using hwline
      · change π (deformPoint φ w) = π (deformPoint φ a)
        simpa only [hπnormal] using hwimage
      · change dist z (deformPoint φ w) < (8 * B + 16) / 2
        dsimp [ρ] at hdist
        linarith
    · intro u hu v hv hd
      change dist (deformPoint φ u) (deformPoint φ v) < (8 * B + 16) / 2 at hd
      change (π (deformPoint φ u - deformPoint φ v) = 0 ↔ π (u - v) = 0)
      simpa only [hπnormal] using hReflect u hu v hv hd
  obtain ⟨w, hw, hwline, hwdist⟩ := hEndpoints a rfl
  have hwimage : π (f w) = π (f a) := by
    change normalEval n (deformPoint φ w) = normalEval n (deformPoint φ a)
    rw [rationalNormal_commutes, rationalNormal_commutes, ← hπnormal, ← hπnormal, hwline]
  obtain ⟨hTargetLine, hAllGerms⟩ := cp_complete_line_from_transport_data ψ hψ hδ
    (Tiling.Polygonal.regularSupport_isRegularOpen K S).1
    (Tiling.Polygonal.regularSupport_isRegularOpen K S).2
    (Tiling.Polygonal.regularSupport_isRegularOpen Kφ (deformPoint φ '' S)).1
    (Tiling.Polygonal.regularSupport_isRegularOpen Kφ (deformPoint φ '' S)).2
    hLine hTargetDisj ⟨w, f w, hwline, hwimage, hGerm w (hCloud hw)⟩
  refine ⟨hTargetLine, ?_⟩
  intro x hx
  have hxline := (cp_mem_kernel_line π a x).mp hx
  have hximage : π (f x) = π (f a) := by
    change normalEval n (deformPoint φ x) = normalEval n (deformPoint φ a)
    rw [rationalNormal_commutes, rationalNormal_commutes, ← hπnormal, ← hπnormal, hxline]
  exact hAllGerms x (f x) hxline hximage


private theorem cp_inverse_straight_line_under_controls
    (K Kφ : PolygonalRegion) (S Y : Set Plane) (W : Finset Plane)
    (φ : ℝ →ₗ[ℚ] ℚ) (hY : HasFLC Y) (hImageY : HasFLC (deformPoint φ '' Y))
    (hDec : Decorates Kφ (W.image (deformPoint φ)))
    (hPack : Tiling.IsPacking Kφ.prototileFamily (Kφ.placements (deformPoint φ '' S)))
    (hSφ : HasFLC (deformPoint φ '' S))
    (hCloud : decoratedCloud (W.image (deformPoint φ)) (deformPoint φ '' S) ⊆ deformPoint φ '' Y)
    (B : ℝ) (hB : 0 < B) (hBound : ∀ z ∈ Kφ.support, ‖z‖ ≤ B)
    (n : RationalNormal) (hδ : Module.finrank ℝ (normalDirection n) = 1)
    (hProper : Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) =
      deformPoint φ '' Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport K S))
    (hGerm : ∀ v ∈ Y, Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K S) v
      (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) (deformPoint φ v))
    (hCoarse : ∀ u ∈ Y, ∀ v ∈ Y,
      dist (deformPoint φ u) (deformPoint φ v) < (8 * B + 16) / 2 → dist u v < 8 * B + 16)
    (hReflect : ∀ u ∈ Y, ∀ v ∈ Y,
      dist (deformPoint φ u) (deformPoint φ v) < (8 * B + 16) / 2 →
        (normalEval n (deformPoint φ u - deformPoint φ v) = 0 ↔ normalEval n (u - v) = 0))
    (hVector : ∀ u ∈ Y, ∀ v ∈ Y, dist u v < 8 * B + 16 → u ≠ v →
      ‖deformPoint φ (u - v) - (u - v)‖ < ‖u - v‖ ∧
        ‖deformPoint φ (u - v)‖ < ‖u - v‖ + 1)
    (b : Plane)
    (hLine : Tiling.Polygonal.IsStraightFrontierLine (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S))
      (normalDirection n) b) :
    ∃ a : Plane, Tiling.Polygonal.IsStraightFrontierLine (Tiling.Polygonal.regularSupport K S)
      (normalDirection n) a ∧ b - deformPoint φ a ∈ normalDirection n ∧
      ∀ x ∈ a +ᵥ (normalDirection n : Set Plane),
        Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K S) x
          (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) (deformPoint φ x) := by
  classical
  let π := cp_rationalNormalFunctional n
  let ψ : Plane →L[ℝ] ℝ := ⟨π, π.continuous_of_finiteDimensional⟩
  let f : Plane →+ Plane := (deformPointLinear φ).toAddMonoidHom
  let D := Tiling.Polygonal.regularSupport K S
  let E := Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)
  let ρ := 2 * B + 3
  have hρ : 0 < ρ := by positivity
  have hπnormal (z : Plane) : π z = normalEval n z := cp_rationalNormalFunctional_eq_eval n z
  have hψ : Function.Surjective ψ := cp_rationalNormalFunctional_surjective n
  obtain ⟨e, τ, he, hπe, hτe, hrep⟩ := cp_exists_unit_kernel_coordinate π hδ
  have he0 : e ≠ 0 := norm_pos_iff.mp (by rw [he]; exact zero_lt_one)
  have hfront : {z : Plane | π z = π b} ⊆ frontier E := by
    intro z hz
    exact hLine.1 ((cp_mem_kernel_line π b z).mpr hz)
  have hEndpoints : ∀ z : Plane, π z = π b →
      ∃ w ∈ decoratedCloud (W.image (deformPoint φ)) (deformPoint φ '' S),
        π w = π b ∧ dist z w < ρ := by
    have hRadius : 2 * B + ‖e‖ + 2 = ρ := by rw [he]; dsimp [ρ]; ring
    simpa only [hRadius] using cp_frontier_level_decoratedDense_of_bound
      Kφ (deformPoint φ '' S) (W.image (deformPoint φ)) hDec hPack hSφ B hBound
      π b e he0 hπe hfront
  have hcloud : ∀ z : Plane, normalEval n z = normalEval n b →
      ∃ w ∈ deformPoint φ '' Y, normalEval n w = normalEval n b ∧ dist z w < ρ := by
    intro z hz
    obtain ⟨w, hw, hwline, hdist⟩ := hEndpoints z (by simpa only [hπnormal] using hz)
    exact ⟨w, hCloud hw, by simpa only [hπnormal] using hwline, hdist⟩
  obtain ⟨a, haY, hfaLevel, hSourceDense⟩ := cp_inverse_cloud_gives_source_fibre_density
    Y hY φ n hδ (normalEval n b) ρ (8 * B + 16) hImageY hρ
    (by dsimp [ρ]; linarith) hcloud hCoarse hReflect
    (fun u hu v hv hne hd => (hVector u hu v hv hd hne).1)
  have hfaπ : π (f a) = π b := by
    change π (deformPoint φ a) = π b
    simpa only [hπnormal] using hfaLevel
  have hfLevel (z : Plane) (hz : π z = π a) : π (f z) = π b := by
    have hh : π (f z) = π (f a) := by
      change normalEval n (deformPoint φ z) = normalEval n (deformPoint φ a)
      rw [rationalNormal_commutes, rationalNormal_commutes, ← hπnormal, ← hπnormal, hz]
    exact hh.trans hfaπ
  have hSourceDisj : Disjoint {z : Plane | π z = π a} (Tiling.Polygonal.properVertices D) := by
    rw [Set.disjoint_left]
    intro z hz hvertex
    have htargetVertex : f z ∈ Tiling.Polygonal.properVertices E := by
      change deformPoint φ z ∈ Tiling.Polygonal.properVertices
        (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S))
      rw [hProper]
      exact ⟨z, hvertex, rfl⟩
    exact Set.disjoint_left.mp hLine.2 ((cp_mem_kernel_line π b (f z)).mpr (hfLevel z hz)) htargetVertex
  obtain ⟨w, hw, hwline, hdist⟩ := hSourceDense a rfl
  have hwπ : π w = π a := by simpa only [hπnormal] using hwline
  obtain ⟨hSourceLine, hAllGerms⟩ := cp_complete_line_from_transport_data ψ hψ hδ
    (Tiling.Polygonal.regularSupport_isRegularOpen Kφ (deformPoint φ '' S)).1
    (Tiling.Polygonal.regularSupport_isRegularOpen Kφ (deformPoint φ '' S)).2
    (Tiling.Polygonal.regularSupport_isRegularOpen K S).1
    (Tiling.Polygonal.regularSupport_isRegularOpen K S).2
    hLine hSourceDisj ⟨f w, w, hfLevel w hwπ, hwπ, cp_sameGerm_symm (hGerm w hw)⟩
  refine ⟨a, hSourceLine, ?_, ?_⟩
  · change π (b - deformPoint φ a) = 0
    change π (b - f a) = 0
    rw [map_sub, ← hfaπ, sub_self]
  · intro x hx
    have hxπ := (cp_mem_kernel_line π a x).mp hx
    exact cp_sameGerm_symm (hAllGerms (f x) x (hfLevel x hxπ) hxπ)


private theorem image_addLeft_eq_vadd (u : Plane) (S : Set Plane) :
    (Homeomorph.addLeft u) '' S = u +ᵥ S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
    simpa [Homeomorph.addLeft, add_vadd] using hy
  · intro hx
    have hy : (-u) +ᵥ x ∈ S := Set.mem_vadd_set_iff_neg_vadd_mem.mp hx
    refine ⟨(-u) +ᵥ x, hy, ?_⟩
    simp [Homeomorph.addLeft]

/-- A period translates any complete straight frontier line to another one. -/
private theorem cp_period_translates_straight_frontier_line
    (D : Set Plane) (δ : Submodule ℝ Plane) (a u : Plane)
    (hu : u ∈ Tiling.Polygonal.periodGroup D)
    (hline : Tiling.Polygonal.IsStraightFrontierLine D δ a) :
    Tiling.Polygonal.IsStraightFrontierLine D δ (a + u) := by
  rcases hline with ⟨hfront, hproper⟩
  have hlineShift : (a + u) +ᵥ (δ : Set Plane) = u +ᵥ (a +ᵥ (δ : Set Plane)) := by
    ext x
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    constructor <;> intro hx <;> simpa [add_comm, add_left_comm, add_assoc] using hx
  have hperiod : u +ᵥ D = D := AddAction.mem_stabilizer_iff.mp hu
  have himage := image_addLeft_eq_vadd u D
  have hproperPeriod : u +ᵥ Tiling.Polygonal.properVertices D = Tiling.Polygonal.properVertices D := by
    have h := Tiling.Polygonal.properVertices_vadd D u
    rw [hperiod] at h
    exact h.symm
  have hfrontierShift : u +ᵥ frontier D = frontier D := by
    calc
      u +ᵥ frontier D = (Homeomorph.addLeft u) '' frontier D := by
        exact (image_addLeft_eq_vadd u (frontier D)).symm
      _ = frontier ((Homeomorph.addLeft u) '' D) := (Homeomorph.addLeft u).image_frontier D
      _ = frontier (u +ᵥ D) := by rw [himage]
      _ = frontier D := by rw [hperiod]
  constructor
  · rw [hlineShift]
    intro x hx
    have hxline : (-u) +ᵥ x ∈ a +ᵥ (δ : Set Plane) := by
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using hx
    have hfront' := hfront hxline
    have hx' : x ∈ u +ᵥ frontier D := by
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using hfront'
    rwa [hfrontierShift] at hx'
  · rw [hlineShift, ← hproperPeriod]
    rw [Set.disjoint_left] at hproper ⊢
    intro x hxline hxvertex
    exact hproper
      (by simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using hxline)
      (by
        exact Set.mem_vadd_set_iff_neg_vadd_mem.mp hxvertex)

/-- Moving the anchor along the line does not change its affine line or the straight-line
frontier predicate. -/
private theorem cp_straight_frontier_line_tangent_anchor_iff
    (D : Set Plane) (δ : Submodule ℝ Plane) (a b : Plane)
    (hba : b - a ∈ δ) :
    Tiling.Polygonal.IsStraightFrontierLine D δ a ↔ Tiling.Polygonal.IsStraightFrontierLine D δ b := by
  have hsets : b +ᵥ (δ : Set Plane) = a +ᵥ (δ : Set Plane) := by
    ext x
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    constructor
    · intro hx
      have hxa : -a + x = (-b + x) + (b - a) := by abel
      rw [hxa]
      exact δ.add_mem hx hba
    · intro hx
      have hxb : -b + x = (-a + x) + (a - b) := by abel
      rw [hxb]
      have hneg : a - b ∈ δ := by
        convert δ.neg_mem hba using 1 <;> abel
      exact δ.add_mem hx hneg
  simp only [Tiling.Polygonal.IsStraightFrontierLine, hsets]



private theorem cp_regularSupport_empty (K : PolygonalRegion) :
    Tiling.Polygonal.regularSupport K ∅ = ∅ := by
  simp [Tiling.Polygonal.regularSupport, Tiling.Polygonal.openUnion]

private theorem cp_no_straight_line_empty (δ : Submodule ℝ Plane) (a : Plane) :
    ¬ Tiling.Polygonal.IsStraightFrontierLine ∅ δ a := by
  intro h
  have ha : a ∈ a +ᵥ (δ : Set Plane) := ⟨0, δ.zero_mem, by simp [vadd_eq_add]⟩
  have hf := h.1 ha
  simpa using hf

theorem flcDeformation_transportsStraightFrontierLines :
  ∀ (K : PolygonalRegion) (T : Set Plane), Tiling.RationalSlopes.HasRationalSlopes K →
    Tiling.Polygonal.HasFLC T → RelativeDense T →
    Tiling.Polygonal.TilesOn K T (Tiling.Polygonal.regularSupport K T) →
      ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
        ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
          ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
            ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ ∧
              ∀ S ⊆ T, ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
                Tiling.RationalSlopes.HasRationalDirection δ →
                (∀ a : Plane,
                  Tiling.Polygonal.IsStraightFrontierLine
                    (Tiling.Polygonal.regularSupport K S) δ a →
                  Tiling.Polygonal.IsStraightFrontierLine
                    (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) δ
                      (deformPoint φ a) ∧
                  ∀ x ∈ a +ᵥ (δ : Set Plane),
                    Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K S) x
                      (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S))
                        (deformPoint φ x)) ∧
                (∀ b : Plane,
                  Tiling.Polygonal.IsStraightFrontierLine
                    (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S)) δ b →
                  ∃ a : Plane,
                    Tiling.Polygonal.IsStraightFrontierLine
                      (Tiling.Polygonal.regularSupport K S) δ a ∧
                    b - deformPoint φ a ∈ δ ∧
                    ∀ x ∈ a +ᵥ (δ : Set Plane),
                      Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport K S) x
                        (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' S))
                          (deformPoint φ x)) := by
  intro K T hK hT hDense hTile
  obtain ⟨P, hP, W, hW, hW0, B, hB, hBound, N, hN, F, ε, hε, hPacket⟩ :=
    cp_uniform_line_transport_packet K T hK hT hDense hTile
  refine ⟨P, hP, F, ε, hε, ?_⟩
  intro φ hφ
  obtain ⟨Kφ, hSupport, hDecφ, hBoundφ, hDirs, hTileφ, hFLCφ,
    hGerm, hProper, hCoarse, hReflect, hVector⟩ := hPacket φ hφ
  refine ⟨Kφ, hSupport, ?_⟩
  intro S hST δ hδ hRat
  by_cases hEmpty : S = ∅
  · subst S
    constructor
    · intro a hLine
      have hLine' : Tiling.Polygonal.IsStraightFrontierLine ∅ δ a := by
        simpa only [cp_regularSupport_empty] using hLine
      exact (cp_no_straight_line_empty δ a hLine').elim
    · intro b hLine
      have hLine' : Tiling.Polygonal.IsStraightFrontierLine ∅ δ b := by
        simpa only [Set.image_empty, cp_regularSupport_empty] using hLine
      exact (cp_no_straight_line_empty δ b hLine').elim
  have hPackS := cp_subfamily_packing hST hTile.2.1
  have hPackφS := cp_subfamily_packing (Set.image_mono hST) hTileφ.2.1
  have hSFLC := hT.mono hST
  have hSφFLC := hFLCφ.mono (Set.image_mono hST)
  have hY : HasFLC (decoratedCloud W T) := cp_cloud_hasFLC W hT
  have hImageY : HasFLC (deformPoint φ '' decoratedCloud W T) := by
    rw [cp_cloud_image]
    exact cp_cloud_hasFLC (W.image (deformPoint φ)) hFLCφ
  have hCloud := cp_cloud_mono W hST
  have hCloudφ : decoratedCloud (W.image (deformPoint φ)) (deformPoint φ '' S) ⊆
      deformPoint φ '' decoratedCloud W T := by
    rw [← cp_cloud_image]
    exact Set.image_mono hCloud
  constructor
  · intro a hLine
    have hBD := Tiling.Polygonal.straightFrontierLine_isBoundaryDirection hδ hPackS hLine
    obtain ⟨n, hn, hndir⟩ := hN δ hBD
    have hδn : Module.finrank ℝ (normalDirection n) = 1 := by rwa [hndir]
    have hLine' := hLine
    rw [← hndir] at hLine'
    have hforward := cp_forward_straight_line_under_controls K Kφ S (decoratedCloud W T) W
      hW hPackS hSFLC hY hCloud B hB hBound n hδn φ (hProper S hST) (hGerm S hST)
      (fun u hu v hv hd => hReflect u hu v hv hd n hn) hVector a hLine'
    simpa only [hndir] using hforward
  · intro b hLine
    have hBDφ := Tiling.Polygonal.straightFrontierLine_isBoundaryDirection hδ hPackφS hLine
    have hBD := (hDirs δ).mp hBDφ
    obtain ⟨n, hn, hndir⟩ := hN δ hBD
    have hδn : Module.finrank ℝ (normalDirection n) = 1 := by rwa [hndir]
    have hLine' := hLine
    rw [← hndir] at hLine'
    have hinverse := cp_inverse_straight_line_under_controls K Kφ S (decoratedCloud W T) W
      φ hY hImageY hDecφ hPackφS hSφFLC hCloudφ B hB hBoundφ n hδn (hProper S hST)
      (hGerm S hST) hCoarse (fun u hu v hv hd => hReflect u hu v hv hd n hn) hVector b hLine'
    simpa only [hndir] using hinverse

theorem periodicCarrier_centresRelativeDense :
  ∀ (K : PolygonalRegion) (T E : Set Plane), Tiling.Polygonal.TilesOn K T E →
    T.Nonempty → IsOpen E → Tiling.Polygonal.IsLatticePeriodic E → RelativeDense T := by
  intro K T E hTiles hT hEopen hPeriodic
  obtain ⟨L, hLperiod⟩ := hPeriodic
  obtain ⟨R, hRpos, hR⟩ := Tiling.Polygonal.planarLattice_boundedCosetRepresentative L
  obtain ⟨B, hBpos, hBbound⟩ := K.isPolygonal.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨c, hc⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hcopen : K.openCarrier ∈ 𝓝 c := isOpen_interior.mem_nhds hc
  obtain ⟨r, hrpos, hball⟩ := Metric.mem_nhds_iff.mp hcopen
  obtain ⟨t, ht⟩ := hT
  rcases hTiles with ⟨_, _, hcover⟩
  have htileBall : Metric.ball (t + c) r ⊆ Tiling.Polygonal.openUnion K T := by
    intro x hx
    rw [Tiling.Polygonal.openUnion, mem_iUnion]
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    apply hball
    simpa [dist_eq_norm_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx
  have hballMeasure : volume (Metric.ball (t + c) r) ≠ 0 := by
    exact (Metric.isOpen_ball.measure_pos volume ⟨t + c, Metric.mem_ball_self hrpos⟩).ne'
  obtain ⟨e, heball, hecover⟩ :=
    MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hballMeasure
      (hcover.filter_mono ae_restrict_le)
  have htileE : ∃ s : T, e ∈ (s : Plane) +ᵥ K.openCarrier := by
    have hsum : ∃ a ∈ T, ∃ b ∈ K.openCarrier, a + b = e := by
      simpa [Tiling.Polygonal.openUnion, Set.mem_add, vadd_eq_add] using htileBall heball
    obtain ⟨a, ha, b, hb, hab⟩ := hsum
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change -(a : Plane) + e ∈ K.openCarrier
    rw [← hab]
    simpa using hb
  have he : e ∈ E := hecover.mpr htileE
  have hnhds : E ∈ 𝓝 e := hEopen.mem_nhds he
  obtain ⟨s, hspos, hsmall⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨R + s + B, by linarith, ?_⟩
  intro z
  obtain ⟨g, hgL, hzg⟩ := hR (z - e)
  have hge : g ∈ Tiling.Polygonal.periodGroup E := hLperiod hgL
  change g +ᵥ E = E at hge
  have hsballMeasure : volume (Metric.ball (e + g) s) ≠ 0 := by
    exact (Metric.isOpen_ball.measure_pos volume ⟨e + g, Metric.mem_ball_self hspos⟩).ne'
  obtain ⟨q, hqball, hqcover⟩ :=
    MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hsballMeasure
      (hcover.filter_mono ae_restrict_le)
  have hqshift : q - g ∈ Metric.ball e s := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using hqball
  have hqtrans : q ∈ g +ᵥ E := by
    refine ⟨q - g, hsmall hqshift, ?_⟩
    simp [vadd_eq_add]
  have hqE : q ∈ E := by simpa [hge] using hqtrans
  have hqUnion : q ∈ Tiling.Polygonal.openUnion K T := by
    rw [Tiling.Polygonal.openUnion, mem_iUnion]
    exact hqcover.mp hqE
  rw [Tiling.Polygonal.openUnion, mem_iUnion] at hqUnion
  obtain ⟨u, k, hk, rfl⟩ := hqUnion
  have hdistzg : dist z (e + g) ≤ R := by
    simpa [dist_eq_norm_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzg
  have hdistEq : dist ((u : Plane) + k) (u : Plane) = ‖k‖ := by
    simp [dist_eq_norm]
  have hdistq : dist (e + g) (u + k) < s := by
    simpa [dist_comm] using hqball
  have hnormk : ‖k‖ ≤ B := hBbound k (interior_subset hk)
  refine ⟨u, u.2, ?_⟩
  calc
    dist z (u : Plane) ≤ dist z (u + k) + dist (u + k) u := dist_triangle z (u + k) u
    _ ≤ dist z (e + g) + dist (e + g) (u + k) + dist (u + k) u := by
      exact add_le_add (dist_triangle z (e + g) (u + k)) le_rfl
    _ < R + s + B := by
      rw [hdistEq]
      linarith [hdistzg, hdistq, hnormk]



private theorem cp_period_translates_line {D : Set Plane} {δ : Submodule ℝ Plane}
    {a u : Plane} (hu : u ∈ Tiling.Polygonal.periodGroup D)
    (hline : Tiling.Polygonal.IsStraightFrontierLine D δ a) :
    Tiling.Polygonal.IsStraightFrontierLine D δ (a + u) :=
  cp_period_translates_straight_frontier_line D δ a u hu hline

private def cp_boundary_normalFunctional (n : RationalNormal) : Plane →L[ℝ] ℝ :=
  (n.x : ℝ) • Complex.reCLM + (n.y : ℝ) • Complex.imCLM

private theorem cp_boundary_normalFunctional_eq_eval (n : RationalNormal) (z : Plane) :
    cp_boundary_normalFunctional n z = normalEval n z := by
  simp [cp_boundary_normalFunctional, normalEval]

private theorem cp_boundary_normalFunctional_ker (n : RationalNormal) :
    LinearMap.ker (cp_boundary_normalFunctional n).toLinearMap = normalDirection n := rfl

private theorem cp_boundary_normalFunctional_surjective (n : RationalNormal) :
    Function.Surjective (cp_boundary_normalFunctional n) := by
  intro r
  rcases n.nonzero with hx | hy
  · have hxR : (n.x : ℝ) ≠ 0 := by exact_mod_cast hx
    refine ⟨⟨r / (n.x : ℝ), 0⟩, ?_⟩
    rw [cp_boundary_normalFunctional_eq_eval, normalEval]
    simp only [mul_zero, add_zero]
    field_simp [hxR]
  · have hyR : (n.y : ℝ) ≠ 0 := by exact_mod_cast hy
    refine ⟨⟨0, r / (n.y : ℝ)⟩, ?_⟩
    rw [cp_boundary_normalFunctional_eq_eval, normalEval]
    field_simp [hyR] <;> ring

private theorem cp_deformPoint_add (φ : ℝ →ₗ[ℚ] ℚ) (x y : Plane) :
    deformPoint φ (x + y) = deformPoint φ x + deformPoint φ y := by
  exact (deformPointLinear φ).map_add x y

/-- Periods of the source transport to periods of complete target frontier lines, including
the local germ relation at every real point of the translated target line. -/
private theorem cp_source_period_transports_target_boundary_line
    (Kφ : PolygonalRegion) (Sφ D : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ)
    (δ : Submodule ℝ Plane) (u b : Plane)
    (hδ : Module.finrank ℝ δ = 1)
    (hδrat : Tiling.RationalSlopes.HasRationalDirection δ)
    (hEopen : IsOpen (Tiling.Polygonal.regularSupport Kφ Sφ))
    (hEreg : interior (closure (Tiling.Polygonal.regularSupport Kφ Sφ)) =
      Tiling.Polygonal.regularSupport Kφ Sφ)
    (hu : u ∈ Tiling.Polygonal.periodGroup D)
    (hforward : ∀ a : Plane,
      Tiling.Polygonal.IsStraightFrontierLine D δ a →
      Tiling.Polygonal.IsStraightFrontierLine
          (Tiling.Polygonal.regularSupport Kφ Sφ) δ (deformPoint φ a) ∧
        ∀ x ∈ a +ᵥ (δ : Set Plane),
          Tiling.Polygonal.SameGermAt D x
            (Tiling.Polygonal.regularSupport Kφ Sφ) (deformPoint φ x))
    (hbackward : ∀ b : Plane,
      Tiling.Polygonal.IsStraightFrontierLine
          (Tiling.Polygonal.regularSupport Kφ Sφ) δ b →
      ∃ a : Plane,
        Tiling.Polygonal.IsStraightFrontierLine D δ a ∧ b - deformPoint φ a ∈ δ ∧
          ∀ x ∈ a +ᵥ (δ : Set Plane),
            Tiling.Polygonal.SameGermAt D x
              (Tiling.Polygonal.regularSupport Kφ Sφ) (deformPoint φ x))
    (hline : Tiling.Polygonal.IsStraightFrontierLine
        (Tiling.Polygonal.regularSupport Kφ Sφ) δ b) :
    Tiling.Polygonal.IsStraightFrontierLine
        (Tiling.Polygonal.regularSupport Kφ Sφ) δ (b + deformPoint φ u) ∧
      ∀ x ∈ b +ᵥ (δ : Set Plane),
        Tiling.Polygonal.SameGermAt
          (Tiling.Polygonal.regularSupport Kφ Sφ) x
          (Tiling.Polygonal.regularSupport Kφ Sφ) (x + deformPoint φ u) := by
  classical
  let E := Tiling.Polygonal.regularSupport Kφ Sφ
  obtain ⟨n, hn⟩ := rationalDirection_hasNormal δ hδ hδrat
  let ψ := cp_boundary_normalFunctional n
  have hψeval (x : Plane) : ψ x = normalEval n x := cp_boundary_normalFunctional_eq_eval n x
  have hψsurj : Function.Surjective ψ := cp_boundary_normalFunctional_surjective n
  have hker : LinearMap.ker ψ.toLinearMap = δ := by
    rw [cp_boundary_normalFunctional_ker, hn]
  have hδker : Module.finrank ℝ (LinearMap.ker ψ.toLinearMap) = 1 := by
    rw [hker]
    exact hδ
  obtain ⟨a, haLine, habδ, hGerm⟩ := hbackward b hline
  have haShiftLine : Tiling.Polygonal.IsStraightFrontierLine D δ (a + u) :=
    cp_period_translates_line hu haLine
  obtain ⟨hImageShiftLine, hImageShiftGerms⟩ := hforward (a + u) haShiftLine
  have hImageAdd : deformPoint φ (a + u) = deformPoint φ a + deformPoint φ u :=
    cp_deformPoint_add φ a u
  have hAnchorDelta : (b + deformPoint φ u) - deformPoint φ (a + u) ∈ δ := by
    rw [hImageAdd]
    have heq : b + deformPoint φ u - (deformPoint φ a + deformPoint φ u) =
        b - deformPoint φ a := by abel
    rw [heq]
    exact habδ
  have hTargetShiftLine :=
    (cp_straight_frontier_line_tangent_anchor_iff E δ (deformPoint φ (a + u))
      (b + deformPoint φ u) hAnchorDelta).mp hImageShiftLine
  have hlineFa :=
    (cp_straight_frontier_line_tangent_anchor_iff E δ (deformPoint φ a) b habδ).mpr hline
  have haMem : a ∈ a +ᵥ (δ : Set Plane) := by
    refine ⟨0, δ.zero_mem, ?_⟩
    simp [vadd_eq_add]
  have hauMem : a + u ∈ (a + u) +ᵥ (δ : Set Plane) := by
    refine ⟨0, δ.zero_mem, ?_⟩
    simp [vadd_eq_add]
  have hGermA := hGerm a haMem
  have hGermAU := hImageShiftGerms (a + u) hauMem
  have hAnchorGerm := cp_transported_period_germ φ hu hGermA hGermAU
  have hlevelAnchor : ψ (deformPoint φ a) = ψ b := by
    have hmem : b - deformPoint φ a ∈ LinearMap.ker ψ.toLinearMap := by
      simpa only [hker] using habδ
    have hzero := LinearMap.mem_ker.mp hmem
    rw [map_sub] at hzero
    exact (sub_eq_zero.mp hzero).symm
  have hlevelAnchorShift :
      ψ (deformPoint φ a + deformPoint φ u) = ψ (b + deformPoint φ u) := by
    simp only [map_add, hlevelAnchor]
  have hlineFaKernel : Tiling.Polygonal.IsStraightFrontierLine E
      (LinearMap.ker ψ.toLinearMap) (deformPoint φ a) := by
    rw [hker]
    exact hlineFa
  have hImageShiftLineKernel : Tiling.Polygonal.IsStraightFrontierLine E
      (LinearMap.ker ψ.toLinearMap) (deformPoint φ a + deformPoint φ u) := by
    rw [hker]
    simpa only [hImageAdd] using hImageShiftLine
  have hUniform := cp_straightLine_uniform_germs ψ hψsurj hδker
    hEopen hEreg hEopen hEreg hlineFaKernel hImageShiftLineKernel hAnchorGerm
  refine ⟨hTargetShiftLine, ?_⟩
  intro x hxline
  have hxlevel : ψ x = ψ b := by
    have hxker : x ∈ b +ᵥ (LinearMap.ker ψ.toLinearMap : Set Plane) := by
      simpa only [hker] using hxline
    exact (cp_mem_kernel_line ψ.toLinearMap b x).mp hxker
  have htranslatedLevel :
      ψ (x + deformPoint φ u) = ψ (b + deformPoint φ u) := by
    simp only [map_add, hxlevel]
  exact hUniform x (x + deformPoint φ u)
    (hxlevel.trans hlevelAnchor.symm)
    (htranslatedLevel.trans hlevelAnchorShift.symm)



private theorem cp_target_period_from_boundary_data
    (Kφ : PolygonalRegion) (Sφ D : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ)
    (hSφ : Sφ.Nonempty) (hPackφ : Tiling.IsPacking Kφ.prototileFamily (Kφ.placements Sφ))
    (hProper : Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport Kφ Sφ) =
      deformPoint φ '' Tiling.Polygonal.properVertices D)
    (hGerm : ∀ v ∈ Tiling.Polygonal.properVertices D,
      Tiling.Polygonal.SameGermAt D v (Tiling.Polygonal.regularSupport Kφ Sφ) (deformPoint φ v))
    (u : Plane) (hu : u ∈ Tiling.Polygonal.periodGroup D)
    (hForward : ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 → ∀ b : Plane,
      Tiling.Polygonal.IsStraightFrontierLine (Tiling.Polygonal.regularSupport Kφ Sφ) δ b →
        Tiling.Polygonal.IsStraightFrontierLine (Tiling.Polygonal.regularSupport Kφ Sφ) δ
          (b + deformPoint φ u) ∧ ∀ x ∈ b +ᵥ (δ : Set Plane),
          Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport Kφ Sφ) x
            (Tiling.Polygonal.regularSupport Kφ Sφ) (x + deformPoint φ u))
    (hBackward : ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 → ∀ b : Plane,
      Tiling.Polygonal.IsStraightFrontierLine (Tiling.Polygonal.regularSupport Kφ Sφ) δ b →
        Tiling.Polygonal.IsStraightFrontierLine (Tiling.Polygonal.regularSupport Kφ Sφ) δ
          (b - deformPoint φ u) ∧ ∀ x ∈ b +ᵥ (δ : Set Plane),
          Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport Kφ Sφ) x
            (Tiling.Polygonal.regularSupport Kφ Sφ) (x - deformPoint φ u)) :
    deformPoint φ u ∈ Tiling.Polygonal.periodGroup (Tiling.Polygonal.regularSupport Kφ Sφ) := by
  have hW : deformPoint φ u +ᵥ Tiling.Polygonal.properVertices
      (Tiling.Polygonal.regularSupport Kφ Sφ) =
      Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport Kφ Sφ) := by
    rw [hProper]
    exact cp_image_properVertices_period φ hu
  have hG : ∀ q ∈ Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport Kφ Sφ),
      Tiling.Polygonal.SameGermAt (Tiling.Polygonal.regularSupport Kφ Sφ) q
        (Tiling.Polygonal.regularSupport Kφ Sφ) (q + deformPoint φ u) := by
    intro q hq
    rw [hProper] at hq
    obtain ⟨v, hv, rfl⟩ := hq
    have hshift : u +ᵥ Tiling.Polygonal.properVertices D = Tiling.Polygonal.properVertices D := by
      rw [← Tiling.Polygonal.properVertices_vadd D u, AddAction.mem_stabilizer_iff.mp hu]
    have hvu : v + u ∈ Tiling.Polygonal.properVertices D := by
      rw [← hshift]
      exact ⟨v, hv, by simp [vadd_eq_add, add_comm]⟩
    exact cp_transported_period_germ φ hu (hGerm v hv) (hGerm (v + u) hvu)
  exact AddAction.mem_stabilizer_iff.mpr
    (Tiling.Polygonal.properVertices_and_straightLines_determine_translate hSφ hSφ
      hPackφ hPackφ (deformPoint φ u) hW hG hForward hBackward)

private theorem cp_no_straight_line_univ (δ : Submodule ℝ Plane) (a : Plane) :
    ¬ Tiling.Polygonal.IsStraightFrontierLine Set.univ δ a := by
  intro h
  have ha : a ∈ a +ᵥ (δ : Set Plane) := ⟨0, δ.zero_mem, by simp [vadd_eq_add]⟩
  have hf := h.1 ha
  simpa using hf


theorem flcDeformation_preservesPeriodicCarrier :
  ∀ (K : PolygonalRegion) (T E : Set Plane), Tiling.RationalSlopes.HasRationalSlopes K →
    Tiling.Polygonal.HasFLC T → T.Nonempty → Tiling.Polygonal.TilesOn K T E →
    IsOpen E → interior (closure E) = E → Tiling.Polygonal.IsLatticePeriodic E →
      ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
        ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
          ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
            ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ ∧
              Tiling.Polygonal.IsLatticePeriodic
                (Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' T)) ∧
              (E = Set.univ → Tiling.Polygonal.regularSupport Kφ (deformPoint φ '' T) = Set.univ) := by
  intro K T E hK hT hTne hTile hEopen hEreg hPeriodic
  have hCarrier : Tiling.Polygonal.regularSupport K T = E :=
    Tiling.Polygonal.regularSupport_eq_of_tilesOn hEopen hEreg hTile
  have hDense : RelativeDense T := periodicCarrier_centresRelativeDense K T E hTile hTne hEopen hPeriodic
  have hTileReg : TilesOn K T (Tiling.Polygonal.regularSupport K T) := by rwa [hCarrier]
  obtain ⟨P, hP, F₀, ε₀, hε₀, hLinePacket⟩ :=
    flcDeformation_transportsStraightFrontierLines K T hK hT hDense hTileReg
  obtain ⟨Q, hQ, W, hW, hW0, F₁, ε₁, hε₁, hFT⟩ :=
    flcRationalDeformation K T hK hT hDense hTileReg
  obtain ⟨F₂, ε₂, hε₂, hCode⟩ := polyhedralDeformation_independentOfCode K P Q hP hQ
  obtain ⟨L, hLperiod⟩ := hPeriodic
  let u : Plane := L.basis 0
  let v : Plane := L.basis 1
  have hBasis : ![u, v] = L.basis := by
    funext i
    fin_cases i <;> rfl
  have hIndependent : LinearIndependent ℝ ![u, v] := by rw [hBasis]; exact L.independent
  have hu : u ∈ Tiling.Polygonal.periodGroup E :=
    hLperiod (AddSubgroup.subset_closure ⟨0, rfl⟩)
  have hv : v ∈ Tiling.Polygonal.periodGroup E :=
    hLperiod (AddSubgroup.subset_closure ⟨1, rfl⟩)
  obtain ⟨F₃, ε₃, hε₃, hDet⟩ := cp_finite_independence_control u v hIndependent
  let F := F₀ ∪ F₁ ∪ F₂ ∪ F₃
  let ε := min ε₀ (min ε₁ (min ε₂ ε₃))
  have hε : 0 < ε := lt_min hε₀ (lt_min hε₁ (lt_min hε₂ hε₃))
  have hsub₀ : F₀ ⊆ F := by intro t ht; simp [F, ht]
  have hsub₁ : F₁ ⊆ F := by intro t ht; simp [F, ht]
  have hsub₂ : F₂ ⊆ F := by intro t ht; simp [F, ht]
  have hsub₃ : F₃ ⊆ F := by intro t ht; simp [F, ht]
  refine ⟨P, hP, F, ε, hε, ?_⟩
  intro φ hφ
  have hφ₀ := finiteApproximation_strengthen F₀ F ε₀ ε φ hsub₀ (min_le_left _ _) hφ
  have hφ₁ := finiteApproximation_strengthen F₁ F ε₁ ε φ hsub₁
    ((min_le_right _ _).trans (min_le_left _ _)) hφ
  have hφ₂ := finiteApproximation_strengthen F₂ F ε₂ ε φ hsub₂
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) hφ
  have hφ₃ := finiteApproximation_strengthen F₃ F ε₃ ε φ hsub₃
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) hφ
  obtain ⟨Kφ, hKφQ, hRatφ, hSlopesφ, hDecφ, hInjφ, hTileφ, hFLCφ, hGerm, hProper⟩ := hFT φ hφ₁
  obtain ⟨Kψ, hKψP, hLines⟩ := hLinePacket φ hφ₀
  have hSupportEq : Kψ.support = Kφ.support := by rw [hKψP, hKφQ, hCode φ hφ₂]
  have hRegionEq : Kψ = Kφ := cp_polygonalRegion_eq_of_support_eq hSupportEq
  subst Kψ
  have hTargetSupport : Kφ.support = deformedPolyhedralSupport P φ :=
    hKφQ.trans (hCode φ hφ₂).symm
  have hBridge := hLines T (subset_refl T)
  rw [hCarrier] at hBridge
  let Sφ := deformPoint φ '' T
  have hSφ : Sφ.Nonempty := hTne.image (deformPoint φ)
  have hPackφ : Tiling.IsPacking Kφ.prototileFamily (Kφ.placements Sφ) := hTileφ.2.1
  have hRegularφ := Tiling.Polygonal.regularSupport_isRegularOpen Kφ Sφ
  have hProperE : Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport Kφ Sφ) =
      deformPoint φ '' Tiling.Polygonal.properVertices E := by
    simpa only [hCarrier] using hProper T (subset_refl T)
  have hGermE : ∀ x ∈ Tiling.Polygonal.properVertices E,
      Tiling.Polygonal.SameGermAt E x (Tiling.Polygonal.regularSupport Kφ Sφ) (deformPoint φ x) := by
    intro x hx
    have hxReg : x ∈ Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport K T) := by
      simpa only [hCarrier] using hx
    obtain ⟨w, hw, t, ht, hxEq⟩ := Tiling.Polygonal.properVertexProvenance hTile.2.1 x hxReg
    have hxCloud : x ∈ decoratedCloud W T :=
      ⟨w, decorates_intrinsicVertices K W hW hw, t, ht, hxEq.symm⟩
    simpa only [hCarrier] using hGerm T (subset_refl T) x hxCloud
  have hTargetRational : ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
      ∀ b : Plane, Tiling.Polygonal.IsStraightFrontierLine
        (Tiling.Polygonal.regularSupport Kφ Sφ) δ b → Tiling.RationalSlopes.HasRationalDirection δ := by
    intro δ hδ b hLine
    exact Tiling.Polygonal.hasRationalDirection_of_hasBoundaryDirection hSlopesφ
      (Tiling.Polygonal.straightFrontierLine_isBoundaryDirection hδ hPackφ hLine)
  have hLiftPeriod : ∀ w : Plane, w ∈ Tiling.Polygonal.periodGroup E →
      deformPoint φ w ∈ Tiling.Polygonal.periodGroup (Tiling.Polygonal.regularSupport Kφ Sφ) := by
    intro w hw
    apply cp_target_period_from_boundary_data Kφ Sφ E φ hSφ hPackφ hProperE hGermE w hw
    · intro δ hδ b hLine
      have hδrat := hTargetRational δ hδ b hLine
      exact cp_source_period_transports_target_boundary_line Kφ Sφ E φ δ w b hδ hδrat
        hRegularφ.1 hRegularφ.2 hw (hBridge δ hδ hδrat).1 (hBridge δ hδ hδrat).2 hLine
    · intro δ hδ b hLine
      have hδrat := hTargetRational δ hδ b hLine
      have hNegative := cp_source_period_transports_target_boundary_line Kφ Sφ E φ δ (-w) b hδ hδrat
        hRegularφ.1 hRegularφ.2 ((Tiling.Polygonal.periodGroup E).neg_mem hw)
        (hBridge δ hδ hδrat).1 (hBridge δ hδ hδrat).2 hLine
      have hφneg : deformPoint φ (-w) = -deformPoint φ w := (deformPointLinear φ).map_neg w
      simpa only [hφneg, sub_eq_add_neg] using hNegative
  have hTargetPeriodic : IsLatticePeriodic (Tiling.Polygonal.regularSupport Kφ Sφ) :=
    cp_lattice_of_pair_periods _ (deformPoint φ u) (deformPoint φ v)
      (hDet φ hφ₃) (hLiftPeriod u hu) (hLiftPeriod v hv)
  refine ⟨Kφ, hTargetSupport, hTargetPeriodic, ?_⟩
  intro hFull
  have hNoVertices : Tiling.Polygonal.properVertices (Tiling.Polygonal.regularSupport Kφ Sφ) = ∅ := by
    rw [hProperE, hFull]
    simp [Tiling.Polygonal.properVertices, Tiling.Polygonal.IsProperVertex]
  apply cp_full_of_no_boundary Kφ hSφ hPackφ hNoVertices
  intro δ hδ b hLine
  have hδrat := hTargetRational δ hδ b hLine
  obtain ⟨a, ha, hba, hGa⟩ := (hBridge δ hδ hδrat).2 b hLine
  rw [hFull] at ha
  exact cp_no_straight_line_univ δ a ha


end Tiling.RationalSlopes
