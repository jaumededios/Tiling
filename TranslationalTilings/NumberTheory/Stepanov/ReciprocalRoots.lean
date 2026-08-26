import Mathlib.Analysis.Complex.Circle
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import TranslationalTilings.NumberTheory.Stepanov.AdditivePointCount
import TranslationalTilings.NumberTheory.Stepanov.ArtinLSeries

/-!
# Bounds for reciprocal roots

This module turns the additive Stepanov point-count estimate into square-root cancellation for
extension-field exponential sums. A simultaneous phase-alignment argument then shows that an
eventual bound on all power sums controls every root norm. Applied to the Artin L-polynomial trace
identity, this places every reciprocal root in the disk of radius `sqrt p`.
-/

set_option relaxedAutoImplicit false

open scoped BigOperators Real

namespace TranslationalTilings.Stepanov

open Filter Polynomial

noncomputable section

/-- Nontrivial additive-character sums over sufficiently large extensions satisfy a
square-root bound. -/
theorem extensionExponentialSum_bound
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ‖extensionExponentialSum psi f n‖ ≤
        C * (Real.sqrt p) ^ n := by
  classical
  obtain ⟨C₀, hC₀, N₀, hcount⟩ :=
    additive_stepanov_point_count f hpos hsmall
  refine ⟨(p : ℝ) * C₀, mul_nonneg (Nat.cast_nonneg _) hC₀,
    N₀ + 1, ?_⟩
  intro n hn
  have hnN : N₀ ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite _
  let t : GaloisField p n → ZMod p := fun x ↦
    Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x)
  have hgroup :
      extensionExponentialSum psi f n =
        ∑ b : ZMod p, (tracePhaseFiberCard f n b : ℂ) * psi b := by
    rw [extensionExponentialSum]
    change (∑ x : GaloisField p n, psi (t x)) = _
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (GaloisField p n))
      t (fun x ↦ psi (t x))]
    apply Finset.sum_congr rfl
    intro b _hb
    calc
      (∑ x ∈ (Finset.univ : Finset (GaloisField p n)) with t x = b,
          psi (t x)) =
          ∑ _x ∈ (Finset.univ : Finset (GaloisField p n)) with t _x = b,
            psi b := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [(Finset.mem_filter.mp hx).2]
      _ = ((Finset.univ : Finset (GaloisField p n)).filter
            (fun x ↦ t x = b)).card • psi b := by
              rw [Finset.sum_const]
      _ = (tracePhaseFiberCard f n b : ℂ) * psi b := by
              simp only [nsmul_eq_mul]
              congr 2
  let main : ℝ := (p : ℝ) ^ (n - 1)
  have herror :
      extensionExponentialSum psi f n =
        ∑ b : ZMod p,
          (((tracePhaseFiberCard f n b : ℝ) - main : ℝ) : ℂ) * psi b := by
    rw [hgroup]
    have hdecomp (b : ZMod p) :
        (tracePhaseFiberCard f n b : ℂ) =
          (((tracePhaseFiberCard f n b : ℝ) - main : ℝ) : ℂ) +
            (main : ℂ) := by
      push_cast
      ring
    simp_rw [hdecomp, add_mul, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, AddChar.sum_eq_zero_of_ne_one hpsi]
    simp
  rw [herror]
  calc
    ‖∑ b : ZMod p,
        (((tracePhaseFiberCard f n b : ℝ) - main : ℝ) : ℂ) * psi b‖ ≤
        ∑ b : ZMod p,
          ‖(((tracePhaseFiberCard f n b : ℝ) - main : ℝ) : ℂ) * psi b‖ :=
      norm_sum_le _ _
    _ = ∑ b : ZMod p,
          |(tracePhaseFiberCard f n b : ℝ) - main| := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [norm_mul, AddChar.norm_apply, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
    _ ≤ ∑ _b : ZMod p, C₀ * (Real.sqrt p) ^ n := by
      apply Finset.sum_le_sum
      intro b _hb
      simpa only [main] using hcount n hnN b
    _ = (p : ℝ) * C₀ * (Real.sqrt p) ^ n := by
      simp [mul_assoc]

/-- Finitely many circle phases have a common strictly increasing sequence of powers
converging to one. -/
theorem exists_unbounded_aligned_powers
    {s : ℕ} (u : Fin s → Circle) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ i, Filter.Tendsto (fun m ↦ u i ^ n m)
        Filter.atTop (nhds 1) := by
  let v : ℕ → Fin s → Circle := fun k i ↦ u i ^ k
  obtain ⟨a, phi, hphi, hphi_lim⟩ := CompactSpace.tendsto_subseq v
  have hreturn : ∀ B q : ℕ, ∃ e : ℕ, B < e ∧
      ∀ i, dist (u i ^ e) 1 < 1 / ((q : ℝ) + 1) := by
    intro B q
    have hshift :
        Tendsto (fun k ↦ v (phi (k + (B + 1)))) atTop (nhds a) := by
      simpa only [Function.comp_def] using
        hphi_lim.comp (tendsto_add_atTop_nat (B + 1))
    have hquot :
        Tendsto (fun k ↦ v (phi (k + (B + 1))) * (v (phi k))⁻¹)
          atTop (nhds 1) := by
      simpa using hshift.mul hphi_lim.inv
    have hrad : 0 < 1 / ((q : ℝ) + 1) := by positivity
    obtain ⟨K, hK⟩ :=
      (Metric.tendsto_atTop.mp hquot) (1 / ((q : ℝ) + 1)) hrad
    let e := phi (K + (B + 1)) - phi K
    refine ⟨e, ?_, ?_⟩
    · have hgap : phi K + (B + 1) ≤ phi (K + (B + 1)) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          hphi.add_le_nat (B + 1) K
      dsimp only [e]
      omega
    · intro i
      have hle : phi K ≤ phi (K + (B + 1)) :=
        hphi.monotone (Nat.le_add_right K (B + 1))
      have heq :
          (v (phi (K + (B + 1))) * (v (phi K))⁻¹) i = u i ^ e := by
        simp only [v, Pi.mul_apply, Pi.inv_apply]
        exact (pow_sub (u i) hle).symm
      have hdist := hK K le_rfl
      rw [dist_pi_lt_iff hrad] at hdist
      simpa only [Pi.one_apply, heq] using hdist i
  let pick : ℕ → ℕ → ℕ := fun q B ↦ Classical.choose (hreturn B q)
  have pick_gt (q B : ℕ) : B < pick q B :=
    (Classical.choose_spec (hreturn B q)).1
  have pick_close (q B : ℕ) (i : Fin s) :
      dist (u i ^ pick q B) 1 < 1 / ((q : ℝ) + 1) :=
    (Classical.choose_spec (hreturn B q)).2 i
  let n : ℕ → ℕ :=
    Nat.rec (pick 0 0) (fun q previous ↦ pick (q + 1) previous)
  have hn_succ (q : ℕ) : n (q + 1) = pick (q + 1) (n q) := by
    simp only [n]
  have hn_close (q : ℕ) (i : Fin s) :
      dist (u i ^ n q) 1 < 1 / ((q : ℝ) + 1) := by
    cases q with
    | zero => simpa only [n, Nat.rec_zero, Nat.cast_zero, zero_add] using pick_close 0 0 i
    | succ q =>
        rw [hn_succ]
        exact pick_close (q + 1) (n q) i
  refine ⟨n, strictMono_nat_of_lt_succ (fun q ↦ ?_), ?_⟩
  · rw [hn_succ]
    exact pick_gt (q + 1) (n q)
  · intro i
    apply Metric.tendsto_atTop.mpr
    intro epsilon hepsilon
    have hzero :
        Tendsto (fun q : ℕ ↦ 1 / ((q : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have heventually :
        ∀ᶠ (q : ℕ) in atTop, 1 / ((q : ℝ) + 1) < epsilon :=
      hzero.eventually_lt_const hepsilon
    obtain ⟨N, hN⟩ := eventually_atTop.mp heventually
    exact ⟨N, fun q hq ↦ (hn_close q i).trans (hN q hq)⟩

/-- The multiplicity of roots whose norm equals the specified maximal radius. -/
noncomputable def maximalRootMultiplicity
    (roots : Multiset ℂ) (rho : ℝ) : ℕ := by
  classical
  exact (roots.filter fun z ↦ ‖z‖ = rho).card

/-- Along aligned powers, the normalized power sum tends to the multiplicity on the maximal
circle. -/
theorem exists_normalized_powerSum_tendsto_maximalMultiplicity
    (roots : Multiset ℂ) (rho : ℝ) (hrho : 0 < rho)
    (hle : ∀ z ∈ roots, ‖z‖ ≤ rho)
    (_hmax : ∃ z ∈ roots, ‖z‖ = rho) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      Filter.Tendsto
        (fun m ↦
          (roots.map fun z ↦ z ^ n m / (rho : ℂ) ^ n m).sum)
        Filter.atTop
        (nhds (maximalRootMultiplicity roots rho : ℂ)) := by
  classical
  let e : roots ≃ Fin roots.card := by
    simpa using Fintype.equivFin roots
  let phase : Fin roots.card → Circle := fun i ↦
    if hi : ‖((e.symm i : roots) : ℂ)‖ = rho then
      ⟨((e.symm i : roots) : ℂ) / (rho : ℂ), by
        change ((e.symm i : roots) : ℂ) / (rho : ℂ) ∈
          Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm]
        rw [norm_div, hi, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hrho, div_self hrho.ne']⟩
    else 1
  obtain ⟨n, hn, halign⟩ := exists_unbounded_aligned_powers phase
  have hrhoC : (rho : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrho.ne'
  have hterm (x : roots) :
      Tendsto
        (fun m ↦ ((x : ℂ) ^ n m / (rho : ℂ) ^ n m)) atTop
        (nhds (if ‖(x : ℂ)‖ = rho then 1 else 0)) := by
    by_cases hx : ‖(x : ℂ)‖ = rho
    · have hphase :
          ((phase (e x) : Circle) : ℂ) = (x : ℂ) / (rho : ℂ) := by
        simp [phase, hx]
      have hcircle := halign (e x)
      have hcomplex :
          Tendsto (fun m ↦ ((phase (e x) ^ n m : Circle) : ℂ)) atTop
            (nhds (1 : ℂ)) :=
        continuous_subtype_val.continuousAt.tendsto.comp hcircle
      simp only [Circle.coe_pow, hphase, div_pow] at hcomplex
      simpa [hx] using hcomplex
    · have hxlt : ‖(x : ℂ)‖ < rho :=
        lt_of_le_of_ne (hle (x : ℂ) Multiset.coe_mem) hx
      have hratio : ‖(x : ℂ)‖ / rho < 1 := by
        exact (div_lt_one hrho).mpr hxlt
      have hnormRatio : ‖(x : ℂ) / (rho : ℂ)‖ < 1 := by
        simpa [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho]
          using hratio
      have hzero :=
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnormRatio).comp
          hn.tendsto_atTop
      simpa only [Function.comp_def, div_pow, if_neg hx] using hzero
  have hsum :
      Tendsto
        (fun m ↦ ∑ x : roots,
          (x : ℂ) ^ n m / (rho : ℂ) ^ n m) atTop
        (nhds (∑ x : roots, if ‖(x : ℂ)‖ = rho then 1 else 0)) := by
    simpa only [Finset.sum_attach] using
      tendsto_finsetSum (Finset.univ : Finset roots)
        (fun x _hx ↦ hterm x)
  have hrootSum (m : ℕ) :
      (roots.map fun z ↦ z ^ n m / (rho : ℂ) ^ n m).sum =
        ∑ x : roots, (x : ℂ) ^ n m / (rho : ℂ) ^ n m := by
    have hroots :
        (Finset.univ : Finset roots).val.map (fun x : roots ↦ (x : ℂ)) = roots := by
      exact Multiset.map_univ_coe roots
    change (roots.map fun z ↦ z ^ n m / (rho : ℂ) ^ n m).sum =
      ((Finset.univ : Finset roots).val.map
        (fun x : roots ↦ (x : ℂ) ^ n m / (rho : ℂ) ^ n m)).sum
    change (roots.map fun z ↦ z ^ n m / (rho : ℂ) ^ n m).sum =
      ((Finset.univ : Finset roots).val.map
        ((fun z : ℂ ↦ z ^ n m / (rho : ℂ) ^ n m) ∘
          fun x : roots ↦ (x : ℂ))).sum
    rw [← Multiset.map_map, hroots]
  have hlimit :
      (∑ x : roots, if ‖(x : ℂ)‖ = rho then (1 : ℂ) else 0) =
        (maximalRootMultiplicity roots rho : ℂ) := by
    rw [Finset.sum_boole]
    norm_cast
    change ((Finset.univ : Finset roots).filter
      (fun x : roots ↦ ‖(x : ℂ)‖ = rho)).card =
        (roots.filter fun z ↦ ‖z‖ = rho).card
    have hroots :
        (Finset.univ : Finset roots).val.map (fun x : roots ↦ (x : ℂ)) = roots := by
      exact Multiset.map_univ_coe roots
    rw [Finset.card_def, Finset.filter_val]
    let p : ℂ → Prop := fun z ↦ ‖z‖ = rho
    let c : roots → ℂ := fun x ↦ (x : ℂ)
    have hfiltered := Multiset.filter_map p c (Finset.univ : Finset roots).val
    calc
      ((Finset.univ : Finset roots).val.filter
          (fun x : roots ↦ ‖(x : ℂ)‖ = rho)).card =
          (((Finset.univ : Finset roots).val.filter
            (fun x : roots ↦ ‖(x : ℂ)‖ = rho)).map c).card := by
            rw [Multiset.card_map]
      _ = (((Finset.univ : Finset roots).val.map c).filter p).card := by
            rw [hfiltered]
            simp only [p, c, Function.comp_apply]
      _ = (roots.filter fun z ↦ ‖z‖ = rho).card := by
            simp only [p, c, hroots]
  refine ⟨n, hn, ?_⟩
  simpa only [hrootSum, hlimit] using hsum

/-- An eventual exponential bound for every power sum bounds the norm of each root. -/
theorem norm_le_of_power_sum_bound
    (roots : Multiset ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hpow : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ‖(roots.map fun z ↦ z ^ n).sum‖ ≤ C * R ^ n) :
    ∀ z ∈ roots, ‖z‖ ≤ R := by
  classical
  obtain ⟨C, hC, N, hbound⟩ := hpow
  intro z hz
  by_contra hzR
  have hRz : R < ‖z‖ := lt_of_not_ge hzR
  have hnonempty : roots.toFinset.Nonempty :=
    ⟨z, Multiset.mem_toFinset.mpr hz⟩
  obtain ⟨zmax, hzmaxFin, hzmax⟩ :=
    Finset.exists_max_image roots.toFinset norm hnonempty
  have hzmaxMem : zmax ∈ roots := Multiset.mem_toFinset.mp hzmaxFin
  let rho : ℝ := ‖zmax‖
  have hrho : 0 < rho := by
    have := hzmax z (Multiset.mem_toFinset.mpr hz)
    dsimp only [rho]
    linarith
  have hRrho : R < rho := by
    have := hzmax z (Multiset.mem_toFinset.mpr hz)
    dsimp only [rho]
    exact hRz.trans_le this
  have hle : ∀ w ∈ roots, ‖w‖ ≤ rho := by
    intro w hw
    exact hzmax w (Multiset.mem_toFinset.mpr hw)
  have hmax : ∃ w ∈ roots, ‖w‖ = rho := ⟨zmax, hzmaxMem, rfl⟩
  obtain ⟨n, hn, hlimit⟩ :=
    exists_normalized_powerSum_tendsto_maximalMultiplicity
      roots rho hrho hle hmax
  let A : ℕ → ℂ := fun m ↦
    (roots.map fun w ↦ w ^ n m / (rho : ℂ) ^ n m).sum
  have hsumDiv (m : ℕ) :
      A m = (roots.map fun w ↦ w ^ n m).sum / (rho : ℂ) ^ n m := by
    simp only [A, div_eq_mul_inv]
    rw [Multiset.sum_map_mul_right]
  have heventBound : ∀ᶠ m in atTop,
      ‖A m‖ ≤ C * (R / rho) ^ n m := by
    filter_upwards [hn.tendsto_atTop.eventually_ge_atTop N] with m hm
    rw [hsumDiv, norm_div, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hrho.le]
    calc
      ‖(Multiset.map (fun w ↦ w ^ n m) roots).sum‖ / rho ^ n m ≤
          (C * R ^ n m) / rho ^ n m :=
        div_le_div_of_nonneg_right (hbound (n m) hm)
          (pow_nonneg hrho.le _)
      _ = C * (R / rho) ^ n m := by
        rw [div_pow, mul_div_assoc]
  have hratioNonneg : 0 ≤ R / rho := div_nonneg hR hrho.le
  have hratioLt : R / rho < 1 := (div_lt_one hrho).mpr hRrho
  have hright :
      Tendsto (fun m ↦ C * (R / rho) ^ n m) atTop (nhds 0) := by
    have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one hratioNonneg hratioLt
    simpa using tendsto_const_nhds.mul (hbase.comp hn.tendsto_atTop)
  have hnormZero : Tendsto (fun m ↦ ‖A m‖) atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
      heventBound hright
  have hzero : Tendsto A atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnormZero
  have hlimitA :
      Tendsto A atTop
        (nhds (maximalRootMultiplicity roots rho : ℂ)) := by
    simpa only [A] using hlimit
  have heq : (maximalRootMultiplicity roots rho : ℂ) = 0 :=
    tendsto_nhds_unique hlimitA hzero
  have hmultPos : 0 < maximalRootMultiplicity roots rho := by
    rw [maximalRootMultiplicity, Multiset.card_pos_iff_exists_mem]
    exact ⟨zmax, Multiset.mem_filter.mpr ⟨hzmaxMem, rfl⟩⟩
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hmultPos)) heq

/-- Every reciprocal root of the Artin L-polynomial has norm at most `sqrt p`. -/
theorem reciprocalRoots_norm_le
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ∀ omega ∈ reciprocalRoots psi f, ‖omega‖ ≤ Real.sqrt p := by
  apply norm_le_of_power_sum_bound
    (reciprocalRoots psi f) (Real.sqrt p) (Real.sqrt_nonneg p)
  obtain ⟨C, hC, N, hbound⟩ :=
    extensionExponentialSum_bound psi hpsi f hpos hsmall
  refine ⟨C, hC, N + 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have htrace :=
    artinLPolynomial_trace_identity psi hpsi f hf0 hpos hsmall hn0
  calc
    ‖((reciprocalRoots psi f).map fun omega ↦ omega ^ n).sum‖ =
        ‖extensionExponentialSum psi f n‖ := by
      rw [htrace, norm_neg]
    _ ≤ C * (Real.sqrt p) ^ n := hbound n hnN

end

end TranslationalTilings.Stepanov
