import Tiling.AxisParallel.Foundations.RationalMeshRaster
import Tiling.AxisParallel.Terminal.DiscreteFinerStructure
import Tiling.AxisParallel.Terminal.RationalSliceCore

/-!
# Finer structure for rational axis-parallel tilings

This module constructs the rational directional decomposition of an axis-parallel tiling whose
vertices and centres lie on a common rational mesh. It transfers the discrete decomposition through
the exact rational raster and records the resulting rational slice orbits and support transport.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Function Set
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel
private abbrev ZPlane := Tiling.AxisParallel.RationalMesh.ZPlane

private def rasterCentres (d : ℕ) (T : Set Tiling.Plane) : Set ZPlane :=
  {z | Tiling.AxisParallel.RationalMesh.rationalScale d z ∈ T}

private def scaleLatticeSet (d : ℕ) (A : Set ZPlane) : Set Tiling.Plane :=
  Tiling.AxisParallel.RationalMesh.rationalScale d '' A

private def scaleDirection (d : ℕ) (hd : 0 < d) (u : ZPlane) (hu : u ≠ 0) :
    RationalDirection := by
  refine ⟨fun i ↦ (u i : ℚ) / d, ?_⟩
  intro hz
  apply hu
  funext i
  have hi := congrFun hz i
  simp only [Pi.zero_apply] at hi
  rcases div_eq_zero_iff.mp hi with hi | hd0
  · exact_mod_cast hi
  · exact False.elim ((Nat.ne_of_gt hd) (by exact_mod_cast hd0))

private theorem rationalScale_zsmul : ∀ {d : ℕ}, 0 < d → ∀ (n : ℤ) (z : ZPlane),
    Tiling.AxisParallel.RationalMesh.rationalScale d (n • z) =
      n • Tiling.AxisParallel.RationalMesh.rationalScale d z := by
  intro d hd n z
  have hadd := Tiling.AxisParallel.RationalMesh.rationalScale_add (d := d) hd
  have hzero : Tiling.AxisParallel.RationalMesh.rationalScale d 0 = 0 := by
    have hzero' := hadd 0 0
    rw [zero_add] at hzero'
    have hz :
        Tiling.AxisParallel.RationalMesh.rationalScale d 0 + 0 =
          Tiling.AxisParallel.RationalMesh.rationalScale d 0 +
            Tiling.AxisParallel.RationalMesh.rationalScale d 0 := by
      simpa using hzero'.symm
    exact (add_left_cancel hz).symm
  have hneg (x : ZPlane) :
      Tiling.AxisParallel.RationalMesh.rationalScale d (-x) =
        -Tiling.AxisParallel.RationalMesh.rationalScale d x := by
    have h := hadd (-x) x
    have hz :
        Tiling.AxisParallel.RationalMesh.rationalScale d (-x) +
            Tiling.AxisParallel.RationalMesh.rationalScale d x = 0 := by
      rw [← h]
      simp [hzero]
    exact eq_neg_of_add_eq_zero_left hz
  induction n using Int.induction_on with
  | zero =>
      simp [hzero]
  | succ n ih =>
      rw [show (↑n + 1 : ℤ) • z = (↑n : ℤ) • z + z by simp [add_smul]]
      rw [hadd, ih]
      simp [add_smul]
  | pred n ih =>
      rw [show (-↑n - 1 : ℤ) • z = (-↑n : ℤ) • z + (-z) by module]
      rw [hadd, ih]
      rw [hneg]
      module

private theorem scaleDirection_toPlane : ∀ {d : ℕ} (hd : 0 < d) (u : ZPlane) (hu : u ≠ 0),
    (scaleDirection d hd u hu).toPlane =
      Tiling.AxisParallel.RationalMesh.rationalScale d u := by
  intro d hd u hu
  apply Complex.ext <;> simp [scaleDirection, RationalDirection.toPlane,
    RationalDirection.coordinates, Tiling.AxisParallel.RationalMesh.rationalScale]

private theorem rasterCentres_image : ∀ {d : ℕ}, 0 < d → ∀ {T : Set Tiling.Plane},
    Tiling.AxisParallel.RationalMesh.OnRationalMesh d T →
      scaleLatticeSet d (rasterCentres d T) = T := by
  intro d hd T hT
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    exact hz
  · intro x hx
    rcases hT hx with ⟨z, rfl⟩
    exact ⟨z, hx, rfl⟩

private theorem rasterTarget_vertical_periodic : ∀ {d : ℕ}, 0 < d → ∀ {E : Set Tiling.Plane},
    (∀ r : ℝ, (r * Complex.I) +ᵥ E = E) →
      Function.Periodic
        (TranslationalTilings.setIndicator
          (Tiling.AxisParallel.RationalMesh.rasterCells d E))
        (![0, 1] : ZPlane) := by
  intro d hd E hvertical z
  let c : Tiling.Plane :=
    Tiling.AxisParallel.RationalMesh.rationalScale d (![0, 1] : ZPlane)
  have hc : c = (1 / (d : ℝ)) * Complex.I := by
    apply Complex.ext <;>
      simp [c, Tiling.AxisParallel.RationalMesh.rationalScale]
  have hcE : c +ᵥ E = E := by
    rw [hc]
    simpa using hvertical ((1 : ℝ) / (d : ℝ))
  let a : ZPlane := ![0, 1]
  change TranslationalTilings.setIndicator
      (Tiling.AxisParallel.RationalMesh.rasterCells d E) (z + a) =
      TranslationalTilings.setIndicator
        (Tiling.AxisParallel.RationalMesh.rasterCells d E) z
  have hcell := Tiling.AxisParallel.RationalMesh.meshCell_add hd z a
  have hmem : z + a ∈
      Tiling.AxisParallel.RationalMesh.rasterCells d E ↔
      z ∈ Tiling.AxisParallel.RationalMesh.rasterCells d E := by
    change (Tiling.AxisParallel.RationalMesh.meshCell d (z + a) ⊆ E) ↔
      Tiling.AxisParallel.RationalMesh.meshCell d z ⊆ E
    rw [hcell]
    constructor
    · intro hsub x hx
      have hcx : c + x ∈ c +ᵥ Tiling.AxisParallel.RationalMesh.meshCell d z := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa [vadd_eq_add]
      have hce : c + x ∈ E := hsub hcx
      have hce' : c + x ∈ c +ᵥ E := by
        rw [hcE]
        exact hce
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hce'
    · intro hsub x hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
      have hy : -c + x ∈ Tiling.AxisParallel.RationalMesh.meshCell d z := by
        simpa [vadd_eq_add] using hx
      have hye : -c + x ∈ E := hsub hy
      have hxe : x ∈ c +ᵥ E := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hye
      rw [hcE] at hxe
      exact hxe
  by_cases h₂ : z ∈ Tiling.AxisParallel.RationalMesh.rasterCells d E
  · have h₁ := hmem.mpr h₂
    simp [TranslationalTilings.setIndicator, h₁, h₂]
  · have h₁ := hmem.not.mpr h₂
    simp only [TranslationalTilings.setIndicator, Set.indicator_of_notMem h₁,
      Set.indicator_of_notMem h₂]

private theorem frontier_vadd_eq_frontier
    {E : Set Tiling.Plane} (a : Tiling.Plane)
    (hE : a +ᵥ E = E) : a +ᵥ frontier E = frontier E := by
  have hcl : a +ᵥ closure E = closure E := by
    calc
      a +ᵥ closure E = closure (a +ᵥ E) := (closure_vadd a E).symm
      _ = closure E := congrArg closure hE
  have hint : a +ᵥ interior E = interior E := by
    calc
      a +ᵥ interior E = interior (a +ᵥ E) := (interior_vadd a E).symm
      _ = interior E := congrArg interior hE
  apply Set.ext
  intro x
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  change (-a + x ∈ closure E ∧ -a + x ∉ interior E) ↔
    (x ∈ closure E ∧ x ∉ interior E)
  have hcl' : -a + x ∈ closure E ↔ x ∈ closure E := by
    have hx := congrArg (fun S : Set Tiling.Plane => x ∈ S) hcl
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hx
  have hint' : -a + x ∈ interior E ↔ x ∈ interior E := by
    have hx := congrArg (fun S : Set Tiling.Plane => x ∈ S) hint
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hx
  exact and_congr hcl' (not_congr hint')

private theorem rasterTarget_horizontal_integerPeriod :
    ∀ {K : Region} {T E : Set Tiling.Plane} {d : ℕ},
    0 < d →
    Tiling.AxisParallel.RationalMesh.OnRationalMesh d K.vertices →
    Tiling.AxisParallel.RationalMesh.OnRationalMesh d T →
    IsOpen E → interior (closure E) = E →
    (∀ r : ℝ, (r * Complex.I) +ᵥ E = E) →
    (∃ b : ℝ, b ≠ 0 ∧ (b : Tiling.Plane) +ᵥ E = E) →
    TilesOn K T E →
      ∃ ell : ℕ, 0 < ell ∧
        Function.Periodic
          (TranslationalTilings.setIndicator
            (Tiling.AxisParallel.RationalMesh.rasterCells d E))
          (![(ell : ℤ), 0] : ZPlane) := by
  intro K T E d hd hK hT hEopen hEregular hvertical hhorizontal htiles
  classical
  by_cases hEempty : E = ∅
  · refine ⟨1, by omega, ?_⟩
    have hR : Tiling.AxisParallel.RationalMesh.rasterCells d E = ∅ := by
      rw [hEempty]
      ext z
      constructor
      · intro hz
        obtain ⟨x, hx⟩ := Tiling.AxisParallel.RationalMesh.meshCell_nonempty hd z
        exact False.elim (hz hx)
      · simp
    rw [hR]
    intro z
    simp [TranslationalTilings.setIndicator]
  by_cases hEuniv : E = Set.univ
  · refine ⟨1, by omega, ?_⟩
    rw [hEuniv]
    intro z
    simp [TranslationalTilings.setIndicator,
      Tiling.AxisParallel.RationalMesh.rasterCells]
  have hfront : frontier E ⊆
      Tiling.AxisParallel.RationalMesh.meshLines d := by
    have hEraster := Tiling.AxisParallel.RationalMesh.target_eq_regularizedRaster
      hd hK hT hEopen hEregular htiles
    have hf := Tiling.AxisParallel.RationalMesh.frontier_regularizedCellUnion_subset_meshLines
      hd (Tiling.AxisParallel.RationalMesh.rasterCells d E)
    have heqfront : frontier E = frontier
        (Tiling.AxisParallel.RationalMesh.regularizedCellUnion d
          (Tiling.AxisParallel.RationalMesh.rasterCells d E)) :=
      congrArg frontier hEraster
    rw [heqfront]
    exact hf
  have hfrontne : (frontier E).Nonempty := by
    apply nonempty_frontier_iff.mpr
    exact ⟨Set.nonempty_iff_ne_empty.mpr hEempty,
      hEuniv⟩
  obtain ⟨x, hxfront⟩ := hfrontne
  let bad : Set ℝ := {r | ∃ n : ℤ,
    x.im + r = (((n : ℚ) / (d : ℚ)) : ℝ)}
  have hbad : bad.Countable := by
    apply Set.Countable.mono (s₁ := bad) (s₂ :=
      Set.range (fun n : ℤ => (((n : ℚ) / (d : ℚ)) : ℝ) - x.im))
    · intro r hr
      rcases hr with ⟨n, hn⟩
      exact ⟨n, by linarith⟩
    · exact Set.countable_range _
  have hr : ∃ r : ℝ, r ∉ bad := by
    by_contra hnone
    push Not at hnone
    have hcount : Countable ℝ := by
      let f : ℝ → bad := fun s => ⟨s, hnone s⟩
      have hf : Function.Injective f := by
        intro s t hst
        exact congrArg Subtype.val hst
      exact @Function.Injective.countable ℝ bad hbad.to_subtype f hf
    exact (not_countable : ¬ Countable ℝ) hcount
  obtain ⟨r, hrbad⟩ := hr
  let y : Tiling.Plane := (r * Complex.I) +ᵥ x
  have hyfront : y ∈ frontier E := by
    have hvfront := frontier_vadd_eq_frontier (r * Complex.I) (hvertical r)
    rw [show y = (r * Complex.I) +ᵥ x by rfl, ← hvfront]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change -(r * Complex.I) + ((r * Complex.I) + x) ∈ frontier E
    simpa [vadd_eq_add] using hxfront
  have hyim : ∀ n : ℤ,
      y.im ≠ (((n : ℚ) / (d : ℚ)) : ℝ) := by
    intro n hn
    apply hrbad
    refine ⟨n, ?_⟩
    simpa [y, vadd_eq_add, add_comm] using hn
  have hyline := hfront hyfront
  have hyreal : ∃ n : ℤ,
      y.re = (((n : ℚ) / (d : ℚ)) : ℝ) := by
    rcases hyline with h | h
    · exact h
    · rcases h with ⟨n, hn⟩
      exact False.elim (hyim n hn)
  obtain ⟨b, hbne, hbperiod⟩ := hhorizontal
  have hbp : 0 < b ∨ 0 < -b := by
    rcases lt_or_gt_of_ne hbne with hb | hb
    · exact Or.inr (neg_pos.mpr hb)
    · exact Or.inl hb
  let p : ℝ := if 0 < b then b else -b
  have hpp : 0 < p := by
    dsimp [p]
    split <;> rename_i h
    · exact h
    · exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) hbne)
  have hpperiod : (p : Tiling.Plane) +ᵥ E = E := by
    dsimp [p]
    split <;> rename_i h
    · exact hbperiod
    · have hneg : (-b : Tiling.Plane) +ᵥ E = E := by
        apply Set.ext
        intro q
        have hq := congrArg (fun S : Set Tiling.Plane => q + (b : Tiling.Plane) ∈ S)
          hbperiod
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm] using hq.symm
      simpa using hneg
  let yp : Tiling.Plane := (p : Tiling.Plane) +ᵥ y
  have hypfront : yp ∈ frontier E := by
    have hvfront := frontier_vadd_eq_frontier (p : Tiling.Plane) hpperiod
    rw [show yp = (p : Tiling.Plane) +ᵥ y by rfl, ← hvfront]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change -(p : Tiling.Plane) + ((p : Tiling.Plane) + y) ∈ frontier E
    simpa [vadd_eq_add] using hyfront
  have hypim : ∀ n : ℤ,
      yp.im ≠ (((n : ℚ) / (d : ℚ)) : ℝ) := by
    intro n hn
    apply hrbad
    refine ⟨n, ?_⟩
    have him : yp.im = y.im := by
      simp [yp, vadd_eq_add]
    simpa [him, y, vadd_eq_add, add_comm] using hn
  have hypline := hfront hypfront
  have hypreal : ∃ m : ℤ,
      yp.re = (((m : ℚ) / (d : ℚ)) : ℝ) := by
    rcases hypline with h | h
    · exact h
    · rcases h with ⟨m, hm⟩
      exact False.elim (hypim m hm)
  obtain ⟨n, hn⟩ := hyreal
  obtain ⟨m, hm⟩ := hypreal
  have hq : (d : ℝ) * p = (m : ℝ) - n := by
    have hre : yp.re = y.re + p := by simp [yp, vadd_eq_add, add_comm]
    have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
    have hn' : (d : ℝ) * y.re = (n : ℝ) := by
      rw [hn]
      field_simp [hdne]
      norm_num
    have hm' : (d : ℝ) * yp.re = (m : ℝ) := by
      rw [hm]
      field_simp [hdne]
      norm_num
    calc
      (d : ℝ) * p = (d : ℝ) * (yp.re - y.re) := by rw [hre]; ring
      _ = (d : ℝ) * yp.re - (d : ℝ) * y.re := by ring
      _ = (m : ℝ) - (n : ℝ) := by rw [hm', hn']
  let q : ℤ := m - n
  have hqpos : 0 < q := by
    have hqpos' : (0 : ℝ) < (m : ℝ) - (n : ℝ) := by
      rw [← hq]
      positivity
    have hqpos'' : 0 < m - n := by exact_mod_cast hqpos'
    dsimp [q]
    exact hqpos''
  let ell : ℕ := Int.toNat q
  have hellq : (ell : ℤ) = q := by
    dsimp [ell]
    exact Int.toNat_of_nonneg (le_of_lt hqpos)
  have hell : 0 < ell := by
    apply Nat.pos_of_ne_zero
    intro hellzero
    have : q = 0 := by rw [← hellq, hellzero]; simp
    omega
  refine ⟨ell, hell, ?_⟩
  have hmem_period : ∀ (v : ZPlane) (a : Tiling.Plane),
      Tiling.AxisParallel.RationalMesh.rationalScale d v = a →
      a +ᵥ E = E → ∀ z,
      z + v ∈ Tiling.AxisParallel.RationalMesh.rasterCells d E ↔
        z ∈ Tiling.AxisParallel.RationalMesh.rasterCells d E := by
    intro v a hva ha z
    have hcell := Tiling.AxisParallel.RationalMesh.meshCell_add hd z v
    change (Tiling.AxisParallel.RationalMesh.meshCell d (z + v) ⊆ E) ↔
      Tiling.AxisParallel.RationalMesh.meshCell d z ⊆ E
    rw [hcell, hva]
    constructor
    · intro hsub x hx
      have hax : a + x ∈ a +ᵥ Tiling.AxisParallel.RationalMesh.meshCell d z := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa [vadd_eq_add]
      have hae : a + x ∈ E := hsub hax
      have hae' : a + x ∈ a +ᵥ E := by
        rw [ha]
        exact hae
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hae'
    · intro hsub x hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
      have hy : -a + x ∈ Tiling.AxisParallel.RationalMesh.meshCell d z := by
        simpa [vadd_eq_add] using hx
      have hye : -a + x ∈ E := hsub hy
      have hxe : x ∈ a +ᵥ E := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hye
      rw [ha] at hxe
      exact hxe
  have hscale :
      Tiling.AxisParallel.RationalMesh.rationalScale d
          (![ (ell : ℤ), 0] : ZPlane) = (p : Tiling.Plane) := by
    apply Complex.ext
    · simp only [Tiling.AxisParallel.RationalMesh.rationalScale, Complex.ofReal_re]
      change ((((ell : ℤ) : ℚ) / (d : ℚ)) : ℝ) = p
      norm_num
      have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
      have hellqR : (ell : ℝ) = (q : ℝ) := by exact_mod_cast hellq
      have hqR : (q : ℝ) = (d : ℝ) * p := by
        exact_mod_cast hq.symm
      rw [hellqR, hqR]
      field_simp [hdne]
    · simp [Tiling.AxisParallel.RationalMesh.rationalScale]
  have hmemell (z : ZPlane) :
      z + (![ (ell : ℤ), 0] : ZPlane) ∈
          Tiling.AxisParallel.RationalMesh.rasterCells d E ↔
        z ∈ Tiling.AxisParallel.RationalMesh.rasterCells d E := by
    exact hmem_period (![ (ell : ℤ), 0] : ZPlane) (p : Tiling.Plane)
      hscale hpperiod z
  intro z
  by_cases hz : z ∈ Tiling.AxisParallel.RationalMesh.rasterCells d E
  · have hz' := hmemell z |>.mpr hz
    simp only [TranslationalTilings.setIndicator,
      Set.indicator_of_mem hz', Set.indicator_of_mem hz]
  · have hz' := hmemell z |>.not.mpr hz
    simp only [TranslationalTilings.setIndicator,
      Set.indicator_of_notMem hz', Set.indicator_of_notMem hz]

private theorem rasterTarget_scalarPeriodic : ∀ {K : Region} {T E : Set Tiling.Plane} {d : ℕ},
    0 < d →
    Tiling.AxisParallel.RationalMesh.OnRationalMesh d K.vertices →
    Tiling.AxisParallel.RationalMesh.OnRationalMesh d T →
    IsOpen E → interior (closure E) = E →
    (∀ r : ℝ, (r * Complex.I) +ᵥ E = E) →
    (∃ b : ℝ, b ≠ 0 ∧ (b : Tiling.Plane) +ᵥ E = E) →
    TilesOn K T E →
      ∃ ell : ℕ, 0 < ell ∧
        TranslationalTilings.SetScalarPeriodic ell
          (Tiling.AxisParallel.RationalMesh.rasterCells d E) := by
  intro K T E d hd hK hT hEopen hEregular hvertical hhorizontal htiles
  obtain ⟨ell, hell, hhor⟩ := rasterTarget_horizontal_integerPeriod
    hd hK hT hEopen hEregular hvertical hhorizontal htiles
  have hver := rasterTarget_vertical_periodic (d := d) hd hvertical
  refine ⟨ell, hell, ?_⟩
  intro x z
  let p₁ : ZPlane := (z 0) • (![ (ell : ℤ), 0] : ZPlane)
  let p₂ : ZPlane := ((ell : ℤ) * z 1) • (![0, 1] : ZPlane)
  have hp₁ : Function.Periodic
      (TranslationalTilings.setIndicator
        (Tiling.AxisParallel.RationalMesh.rasterCells d E)) p₁ := by
    exact hhor.zsmul (z 0)
  have hp₂ : Function.Periodic
      (TranslationalTilings.setIndicator
        (Tiling.AxisParallel.RationalMesh.rasterCells d E)) p₂ := by
    exact hver.zsmul ((ell : ℤ) * z 1)
  have hp : p₁ + p₂ = (ell : ℤ) • z := by
    funext i
    fin_cases i
    · simp [p₁, p₂]
      ring
    · simp [p₁, p₂]
  have hind :
      TranslationalTilings.setIndicator
          (Tiling.AxisParallel.RationalMesh.rasterCells d E)
          (x + (ell : ℤ) • z) =
        TranslationalTilings.setIndicator
          (Tiling.AxisParallel.RationalMesh.rasterCells d E) x := by
    rw [← hp]
    calc
      TranslationalTilings.setIndicator
          (Tiling.AxisParallel.RationalMesh.rasterCells d E) (x + (p₁ + p₂)) =
          TranslationalTilings.setIndicator
            (Tiling.AxisParallel.RationalMesh.rasterCells d E) (x + p₁ + p₂) := by
              congr 1
              abel
      _ = TranslationalTilings.setIndicator
            (Tiling.AxisParallel.RationalMesh.rasterCells d E) (x + p₁) :=
          hp₂ (x + p₁)
      _ = TranslationalTilings.setIndicator
            (Tiling.AxisParallel.RationalMesh.rasterCells d E) x := hp₁ x
  have indicator_eq_iff {u v : ZPlane}
      (huv : TranslationalTilings.setIndicator
        (Tiling.AxisParallel.RationalMesh.rasterCells d E) u =
        TranslationalTilings.setIndicator
          (Tiling.AxisParallel.RationalMesh.rasterCells d E) v) :
      (u ∈ Tiling.AxisParallel.RationalMesh.rasterCells d E ↔
        v ∈ Tiling.AxisParallel.RationalMesh.rasterCells d E) := by
    by_cases hu : u ∈ Tiling.AxisParallel.RationalMesh.rasterCells d E
    · by_cases hv : v ∈ Tiling.AxisParallel.RationalMesh.rasterCells d E
      · exact Iff.intro (fun _ => hv) (fun _ => hu)
      · exfalso
        simp only [TranslationalTilings.setIndicator,
          Set.indicator_of_mem hu, Set.indicator_of_notMem hv] at huv
        omega
    · by_cases hv : v ∈ Tiling.AxisParallel.RationalMesh.rasterCells d E
      · exfalso
        simp only [TranslationalTilings.setIndicator,
          Set.indicator_of_notMem hu, Set.indicator_of_mem hv] at huv
        omega
      · exact Iff.intro (fun h => False.elim (hu h)) (fun h => False.elim (hv h))
  exact indicator_eq_iff hind

private theorem exists_exactPeriodicRaster : ∀ {K : Region} {T E : Set Tiling.Plane} {d : ℕ},
    0 < d →
    Tiling.AxisParallel.RationalMesh.OnRationalMesh d K.vertices →
    Tiling.AxisParallel.RationalMesh.OnRationalMesh d T →
    IsOpen E → interior (closure E) = E →
    (∀ r : ℝ, (r * Complex.I) +ᵥ E = E) →
    (∃ b : ℝ, b ≠ 0 ∧ (b : Tiling.Plane) +ᵥ E = E) →
    TilesOn K T E →
      ∃ (ell : ℕ) (F : Finset ZPlane),
        0 < ell ∧ F.Nonempty ∧
        (F : Set ZPlane) =
          Tiling.AxisParallel.RationalMesh.rasterCells d K.openCarrier ∧
        TranslationalTilings.SetScalarPeriodic ell
          (Tiling.AxisParallel.RationalMesh.rasterCells d E) ∧
        TranslationalTilings.Tiles F (rasterCentres d T)
          (Tiling.AxisParallel.RationalMesh.rasterCells d E) := by
  intro K T E d hd hK hT hEopen hEregular hvertical hhorizontal htiles
  have hEraster := Tiling.AxisParallel.RationalMesh.target_eq_regularizedRaster
    hd hK hT hEopen hEregular htiles
  obtain ⟨ell, hell, hscalar⟩ := rasterTarget_scalarPeriodic
    hd hK hT hEopen hEregular hvertical hhorizontal htiles
  obtain ⟨F, hFne, hF, _hFae, _hFreg⟩ :=
    Tiling.AxisParallel.RationalMesh.exists_regionRaster hd hK
  obtain ⟨F', hF'ne, hF', hiff⟩ :=
    Tiling.AxisParallel.RationalMesh.tilesOn_rationalScale_image_iff_raster
      (K := K) (A := rasterCentres d T) (E := E) (d := d)
      hd hK hEopen hEregular hEraster
  have hiff' := hiff
  rw [show Tiling.AxisParallel.RationalMesh.rationalScale d '' rasterCentres d T = T by
    exact rasterCentres_image hd hT] at hiff'
  have htiles' : TranslationalTilings.Tiles F' (rasterCentres d T)
      (Tiling.AxisParallel.RationalMesh.rasterCells d E) := hiff'.mp htiles
  refine ⟨ell, F', hell, hF'ne, hF', hscalar, htiles'⟩



private theorem realDirectionSubgroup_scale_multiple : ∀ {d : ℕ} (hd : 0 < d) {u within : ZPlane}
    (hu : TranslationalTilings.IsPrimitive u)
    (hwithin : ∃ m : ℤ, m ≠ 0 ∧ within = m • u),
    realDirectionSubgroup
        (scaleDirection d hd within (by
          obtain ⟨m, hm, rfl⟩ := hwithin
          exact smul_ne_zero hm hu.1)) =
      realDirectionSubgroup (scaleDirection d hd u hu.1) := by
  intro d hd u within hu hwithin
  obtain ⟨m, hm, rfl⟩ := hwithin
  let hw : (m • u : ZPlane) ≠ 0 := smul_ne_zero hm hu.1
  have hscale := Tiling.AxisParallel.RationalMesh.rationalScale_add (d := d) hd
  have hzero : Tiling.AxisParallel.RationalMesh.rationalScale d 0 = 0 := by
    apply add_left_cancel (a := Tiling.AxisParallel.RationalMesh.rationalScale d 0)
    simpa using (hscale 0 0).symm
  let f : ZPlane →+ Tiling.Plane := {
    toFun := Tiling.AxisParallel.RationalMesh.rationalScale d
    map_zero' := hzero
    map_add' := hscale }
  have hmul : Tiling.AxisParallel.RationalMesh.rationalScale d (m • u) =
      m • Tiling.AxisParallel.RationalMesh.rationalScale d u := by
    exact f.map_zsmul m u
  have hto : (scaleDirection d hd (m • u) hw).toPlane =
      (m : ℝ) • (scaleDirection d hd u hu.1).toPlane := by
    rw [scaleDirection_toPlane, scaleDirection_toPlane, hmul]
    norm_num [smul_eq_mul]
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨r * (m : ℝ), ?_⟩
    rw [hto]
    module
  · rintro ⟨r, rfl⟩
    refine ⟨r / (m : ℝ), ?_⟩
    rw [hto]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [smul_smul]
    field_simp [hmR]

private theorem mem_directionSubgroup_of_wedge_eq_zero
    {h d : ZPlane} (hh : TranslationalTilings.IsPrimitive h)
    (hwedge : TranslationalTilings.wedge h d = 0) :
    d ∈ TranslationalTilings.directionSubgroup h := by
  have hgcd : Int.gcd (h 0) (h 1) = 1 := by
    have hcontent := hh.2
    rw [TranslationalTilings.vectorContent,
      show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide] at hcontent
    simp only [Finset.gcd_insert, Finset.gcd_singleton, normalize_eq,
      gcd_eq_nat_gcd] at hcontent
    simpa only [Nat.gcd_zero_left, Int.gcd_eq_natAbs] using hcontent
  have hbezout : (1 : ℤ) =
      h 0 * Int.gcdA (h 0) (h 1) + h 1 * Int.gcdB (h 0) (h 1) := by
    rw [← Int.gcd_eq_gcd_ab, hgcd]
    norm_num
  let c : ℤ := d 0 * Int.gcdA (h 0) (h 1) +
    d 1 * Int.gcdB (h 0) (h 1)
  rw [TranslationalTilings.directionSubgroup,
    AddSubgroup.mem_zmultiples_iff]
  refine ⟨c, ?_⟩
  funext i
  fin_cases i
  · simp only [Pi.smul_apply, smul_eq_mul]
    dsimp [c]
    simp [TranslationalTilings.wedge] at hwedge
    linear_combination -d 0 * hbezout + Int.gcdB (h 0) (h 1) * hwedge
  · simp only [Pi.smul_apply, smul_eq_mul]
    dsimp [c]
    simp [TranslationalTilings.wedge] at hwedge
    linear_combination -d 1 * hbezout - Int.gcdA (h 0) (h 1) * hwedge

private theorem wedge_eq_zero_of_scaled_mem
    {d : ℕ} (hd : 0 < d) {u z : ZPlane} (hu : u ≠ 0)
    (hz : Tiling.AxisParallel.RationalMesh.rationalScale d z ∈
      realDirectionSubgroup (scaleDirection d hd u hu)) :
    TranslationalTilings.wedge u z = 0 := by
  obtain ⟨r, hr⟩ := hz
  rw [scaleDirection_toPlane hd u hu] at hr
  have hre := congrArg Complex.re hr
  have him := congrArg Complex.im hr
  simp [Tiling.AxisParallel.RationalMesh.rationalScale] at hre him
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp [hdq] at hre him
  have hcross : (u 0 : ℝ) * (z 1 : ℝ) -
      (u 1 : ℝ) * (z 0 : ℝ) = 0 := by
    linear_combination (u 0 : ℝ) * him - (u 1 : ℝ) * hre
  have hcrossZ : u 0 * z 1 - u 1 * z 0 = 0 := by
    exact_mod_cast hcross
  simpa [TranslationalTilings.wedge] using hcrossZ


private theorem exists_scaleDiscreteSlice : ∀ {d : ℕ} (hd : 0 < d) {u within : ZPlane}
    (hu : TranslationalTilings.IsPrimitive u)
    (hwithin : ∃ m : ℤ, m ≠ 0 ∧ within = m • u),
    ∃ scaleSlice :
        (ZPlane ⧸ TranslationalTilings.directionSubgroup u) →
          RationalSlice
            (scaleDirection d hd within (by
              obtain ⟨m, hm, rfl⟩ := hwithin
              exact smul_ne_zero hm hu.1)),
      Function.Injective scaleSlice ∧
      Set.range scaleSlice =
        {Q | (Q.carrier ∩
          Tiling.AxisParallel.RationalMesh.rationalMesh d).Nonempty} ∧
      (∀ Q,
        scaleLatticeSet d
            (TranslationalTilings.quotientCoset
              (TranslationalTilings.directionSubgroup u) Q) =
          (scaleSlice Q).carrier ∩
            Tiling.AxisParallel.RationalMesh.rationalMesh d) ∧
      (∀ Q a,
        scaleSlice
            (Q + QuotientAddGroup.mk'
              (TranslationalTilings.directionSubgroup u) a) =
          (scaleSlice Q).vadd
            (Tiling.AxisParallel.RationalMesh.rationalScale d a)) := by
  intro d hd u within hu hwithin
  obtain ⟨m, hm, rfl⟩ := hwithin
  let hw : (m • u : ZPlane) ≠ 0 := smul_ne_zero hm hu.1
  let v : RationalDirection := scaleDirection d hd (m • u) hw
  let rs := Tiling.AxisParallel.RationalMesh.rationalScale d
  have hscale : ∀ z a : ZPlane, rs (z + a) = rs z + rs a :=
    Tiling.AxisParallel.RationalMesh.rationalScale_add hd
  have hzero : rs 0 = 0 := by
    apply add_left_cancel (a := rs 0)
    simpa using (hscale 0 0).symm
  let f : ZPlane →+ Tiling.Plane :=
    { toFun := rs
      map_zero' := hzero
      map_add' := hscale }
  let qhom : ZPlane →+ RationalSlice v :=
    (QuotientAddGroup.mk' (realDirectionSubgroup v)).comp f
  have hbase : rs u ∈ realDirectionSubgroup v := by
    have heq := realDirectionSubgroup_scale_multiple hd hu
      ⟨m, hm, rfl⟩
    have hbaseU : rs u ∈
        realDirectionSubgroup (scaleDirection d hd u hu.1) := by
      change Tiling.AxisParallel.RationalMesh.rationalScale d u ∈ _
      rw [← scaleDirection_toPlane hd u hu.1]
      exact ⟨1, by simp⟩
    exact heq ▸ hbaseU
  have hker : TranslationalTilings.directionSubgroup u ≤ qhom.ker := by
    intro z hz
    obtain ⟨n, rfl⟩ := (AddSubgroup.mem_zmultiples_iff.mp hz)
    change QuotientAddGroup.mk' (realDirectionSubgroup v) (f (n • u)) = 0
    rw [f.map_zsmul]
    change (QuotientAddGroup.mk' (realDirectionSubgroup v))
        (n • f u) = (QuotientAddGroup.mk' (realDirectionSubgroup v)) 0
    change ((n • f u : Tiling.Plane) :
      Tiling.Plane ⧸ realDirectionSubgroup v) = (0 : Tiling.Plane)
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    simpa [f] using (realDirectionSubgroup v).zsmul_mem hbase n
  let scaleSlice :
      (ZPlane ⧸ TranslationalTilings.directionSubgroup u) → RationalSlice v :=
    QuotientAddGroup.lift _ qhom hker
  have hmk (z : ZPlane) : scaleSlice (QuotientAddGroup.mk'
      (TranslationalTilings.directionSubgroup u) z) =
      QuotientAddGroup.mk' (realDirectionSubgroup v) (rs z) := by
    exact QuotientAddGroup.lift_mk' _ _ z
  have hscale_mem (z : ZPlane) (hz : rs z ∈ realDirectionSubgroup v) :
      rs z ∈ Tiling.AxisParallel.RationalMesh.rationalMesh d :=
    ⟨z, rfl⟩
  have hinj : Function.Injective scaleSlice := by
    intro Q₁ Q₂ hQ
    obtain ⟨z₁, rfl⟩ := QuotientAddGroup.mk'_surjective
      (TranslationalTilings.directionSubgroup u) Q₁
    obtain ⟨z₂, rfl⟩ := QuotientAddGroup.mk'_surjective
      (TranslationalTilings.directionSubgroup u) Q₂
    rw [hmk, hmk] at hQ
    have hmem : rs z₁ - rs z₂ ∈ realDirectionSubgroup v := by
      apply (QuotientAddGroup.eq_iff_sub_mem.mp hQ)
    have hmem' : rs (z₁ - z₂) ∈ realDirectionSubgroup v := by
      have hsub := f.map_sub z₁ z₂
      rw [show f (z₁ - z₂) = rs (z₁ - z₂) by rfl] at hsub
      rw [hsub]
      exact hmem
    have hgroup := realDirectionSubgroup_scale_multiple hd hu
      ⟨m, hm, rfl⟩
    rw [hgroup] at hmem'
    have hwedge : TranslationalTilings.wedge u (z₁ - z₂) = 0 := by
      apply wedge_eq_zero_of_scaled_mem hd hu.1
      exact hmem'
    change (z₁ : ZPlane ⧸ TranslationalTilings.directionSubgroup u) = z₂
    rw [QuotientAddGroup.eq_iff_sub_mem]
    exact mem_directionSubgroup_of_wedge_eq_zero hu hwedge
  refine ⟨scaleSlice, hinj, ?_, ?_, ?_⟩
  · ext Q
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
        (TranslationalTilings.directionSubgroup u) q
      rw [hmk]
      refine ⟨rs z, ?_⟩
      constructor
      · change QuotientAddGroup.mk' (realDirectionSubgroup v) (rs z) =
          scaleSlice (QuotientAddGroup.mk'
            (TranslationalTilings.directionSubgroup u) z)
        exact (hmk z).symm
      · exact ⟨z, rfl⟩
    · intro hQ
      obtain ⟨x, hxQ, hxmesh⟩ := hQ
      obtain ⟨z, hz⟩ := hxmesh
      refine ⟨QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup u) z, ?_⟩
      change scaleSlice (QuotientAddGroup.mk'
        (TranslationalTilings.directionSubgroup u) z) = Q
      rw [hmk]
      change QuotientAddGroup.mk' (realDirectionSubgroup v) (rs z) = Q
      change QuotientAddGroup.mk' (realDirectionSubgroup v) x = Q at hxQ
      rw [← hz] at hxQ
      exact hxQ
  · intro Q
    change (rs '' TranslationalTilings.quotientCoset
      (TranslationalTilings.directionSubgroup u) Q) = _
    ext x
    constructor
    · rintro ⟨z, hzQ, rfl⟩
      refine ⟨?_, ?_⟩
      · change QuotientAddGroup.mk' (realDirectionSubgroup v) (rs z) =
          scaleSlice Q
        rw [← hzQ]
        exact (hmk z).symm
      · exact ⟨z, rfl⟩
    · rintro ⟨hxline, hxmesh⟩
      obtain ⟨z, hz⟩ := hxmesh
      refine ⟨z, ?_, hz⟩
      change QuotientAddGroup.mk'
        (TranslationalTilings.directionSubgroup u) z = Q
      apply hinj
      rw [hmk]
      change QuotientAddGroup.mk' (realDirectionSubgroup v) (rs z) =
        scaleSlice Q
      rw [← hz] at hxline
      change QuotientAddGroup.mk' (realDirectionSubgroup v) (rs z) =
        scaleSlice Q at hxline
      exact hxline
  · intro Q a
    obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective
      (TranslationalTilings.directionSubgroup u) Q
    rw [show Q = QuotientAddGroup.mk'
      (TranslationalTilings.directionSubgroup u) z by exact hz.symm]
    rw [hmk]
    change scaleSlice (QuotientAddGroup.mk'
      (TranslationalTilings.directionSubgroup u) (z + a)) = _
    rw [hmk]
    change (QuotientAddGroup.mk' (realDirectionSubgroup v))
      (rs (z + a)) =
      (QuotientAddGroup.mk' (realDirectionSubgroup v))
        (rs z + rs a)
    rw [hscale z a]


private theorem scaleDiscreteSlice_centres : ∀ {d : ℕ} (hd : 0 < d) {u within : ZPlane}
    (hu : TranslationalTilings.IsPrimitive u)
    (hwithin : ∃ m : ℤ, m ≠ 0 ∧ within = m • u)
    (scaleSlice :
      (ZPlane ⧸ TranslationalTilings.directionSubgroup u) →
        RationalSlice
          (scaleDirection d hd within (by
            obtain ⟨m, hm, rfl⟩ := hwithin
            exact smul_ne_zero hm hu.1)))
    (_hcarrier : ∀ Q,
      scaleLatticeSet d
          (TranslationalTilings.quotientCoset
            (TranslationalTilings.directionSubgroup u) Q) =
        (scaleSlice Q).carrier ∩
          Tiling.AxisParallel.RationalMesh.rationalMesh d),
    ∀ (A : Set ZPlane)
      (Q : ZPlane ⧸ TranslationalTilings.directionSubgroup u),
      scaleLatticeSet d (DiscreteSlice u Q A) =
        (scaleSlice Q).centres (scaleLatticeSet d A) := by
  intro d hd u within hu hwithin scaleSlice hcarrier A Q
  let rs := Tiling.AxisParallel.RationalMesh.rationalScale d
  have hrsinj : Function.Injective rs :=
    Tiling.AxisParallel.RationalMesh.rationalScale_injective hd
  have himageA : scaleLatticeSet d A ⊆
      Tiling.AxisParallel.RationalMesh.rationalMesh d := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨z, rfl⟩
  rw [show DiscreteSlice u Q A =
      A ∩ TranslationalTilings.quotientCoset
        (TranslationalTilings.directionSubgroup u) Q by rfl]
  change rs '' (A ∩ TranslationalTilings.quotientCoset
    (TranslationalTilings.directionSubgroup u) Q) =
    (rs '' A) ∩ (scaleSlice Q).carrier
  have hC : rs '' TranslationalTilings.quotientCoset
      (TranslationalTilings.directionSubgroup u) Q =
      (scaleSlice Q).carrier ∩
        Tiling.AxisParallel.RationalMesh.rationalMesh d := by
    simpa [scaleLatticeSet, rs] using hcarrier Q
  ext x
  constructor
  · rintro ⟨z, ⟨hzA, hzQ⟩, rfl⟩
    refine ⟨⟨z, hzA, rfl⟩, ?_⟩
    have hxC : rs z ∈ rs '' TranslationalTilings.quotientCoset
        (TranslationalTilings.directionSubgroup u) Q := ⟨z, hzQ, rfl⟩
    rw [hC] at hxC
    exact hxC.1
  · rintro ⟨⟨zA, hzA, hzx⟩, hxline⟩
    have hxmesh : rs zA ∈
        Tiling.AxisParallel.RationalMesh.rationalMesh d :=
      by
        apply himageA
        refine ⟨zA, hzA, ?_⟩
        rfl
    have hxC : rs zA ∈ rs '' TranslationalTilings.quotientCoset
        (TranslationalTilings.directionSubgroup u) Q := by
      rw [hC]
      rw [← hzx] at hxline
      exact ⟨hxline, hxmesh⟩
    obtain ⟨zQ, hzQ, hzQx⟩ := hxC
    have hzz : zA = zQ := hrsinj hzQx.symm
    subst zQ
    exact ⟨zA, ⟨hzA, hzQ⟩, hzx⟩


private theorem exists_scaleDiscreteOrbit : ∀ {K : Region} {d : ℕ} (hd : 0 < d)
    (_hMesh : Tiling.AxisParallel.RationalMesh.OnRationalMesh d K.vertices)
    (F : Finset ZPlane)
    (_hF : (F : Set ZPlane) =
      Tiling.AxisParallel.RationalMesh.rasterCells d K.openCarrier)
    {A : Set ZPlane} {u within transverse : ZPlane}
    (_hu : TranslationalTilings.IsPrimitive u)
    (htransverse : transverse ≠ 0)
    (O : DiscreteSliceOrbit F A u within transverse),
    ∃ _hwithin : ∃ m : ℤ, m ≠ 0 ∧ within = m • u,
      ∃ scaleSlice :
          (ZPlane ⧸ TranslationalTilings.directionSubgroup u) →
            RationalSlice (scaleDirection d hd within O.within_ne_zero),
        Function.Injective scaleSlice ∧
        Set.range scaleSlice =
          {Q | (Q.carrier ∩
            Tiling.AxisParallel.RationalMesh.rationalMesh d).Nonempty} ∧
        (∀ Q,
          scaleLatticeSet d
              (TranslationalTilings.quotientCoset
                (TranslationalTilings.directionSubgroup u) Q) =
            (scaleSlice Q).carrier ∩
              Tiling.AxisParallel.RationalMesh.rationalMesh d) ∧
        (∀ Q a,
          scaleSlice
              (Q + QuotientAddGroup.mk'
                (TranslationalTilings.directionSubgroup u) a) =
            (scaleSlice Q).vadd
              (Tiling.AxisParallel.RationalMesh.rationalScale d a)) ∧
        ∃ OR : RationalSliceOrbit K (scaleLatticeSet d A)
            (scaleDirection d hd within O.within_ne_zero)
            (scaleDirection d hd transverse htransverse),
          OR.phases = scaleSlice '' O.phases := by
  intro K d hd hMesh F hF A u within transverse hu htransverse O
  obtain ⟨m, hm, hwithin⟩ :=
    TranslationalTilings.integer_multiple_of_primitive_of_commensurable
      O.within_ne_zero hu O.within_parallel
  refine ⟨⟨m, hm, hwithin⟩, ?_⟩
  obtain ⟨scaleSlice, hinj, hrange, hcarrier, hvadd⟩ :=
    exists_scaleDiscreteSlice hd hu ⟨m, hm, hwithin⟩
  refine ⟨scaleSlice, hinj, hrange, hcarrier, hvadd, ?_⟩
  let rs := Tiling.AxisParallel.RationalMesh.rationalScale d
  let phases : Set (RationalSlice
      (scaleDirection d hd within O.within_ne_zero)) :=
    scaleSlice '' O.phases
  have hcentres (Q : RationalSlice
      (scaleDirection d hd within O.within_ne_zero)) :
      (Q.centres (scaleLatticeSet d A)).Nonempty ↔
        Q ∈ phases := by
    constructor
    · intro hQ
      obtain ⟨x, hxA, hxQ⟩ := hQ
      obtain ⟨z, hz, hzx⟩ := hxA
      have hmeshQ : x ∈ Tiling.AxisParallel.RationalMesh.rationalMesh d :=
        ⟨z, hzx⟩
      have hQrange : Q ∈ Set.range scaleSlice := by
        rw [hrange]
        exact ⟨x, hxQ, hmeshQ⟩
      obtain ⟨R, hR⟩ := hQrange
      have hdisc : (DiscreteSlice u R A).Nonempty := by
        have him : x ∈ scaleLatticeSet d (DiscreteSlice u R A) := by
          rw [scaleDiscreteSlice_centres hd hu ⟨m, hm, hwithin⟩
            scaleSlice hcarrier A R]
          rw [← hR] at hxQ
          constructor
          · exact ⟨z, hz, hzx⟩
          · exact hxQ
        obtain ⟨z', hz', _⟩ := him
        exact ⟨z', hz'⟩
      exact ⟨R, (O.phase_iff_nonempty R).2 hdisc, hR⟩
    · rintro ⟨R, hR, rfl⟩
      have hdisc := (O.phase_iff_nonempty R).1 hR
      obtain ⟨z, hz⟩ := hdisc
      refine ⟨rs z, ?_⟩
      constructor
      · exact ⟨z, hz.1, rfl⟩
      · have hzQ : z ∈ TranslationalTilings.quotientCoset
            (TranslationalTilings.directionSubgroup u) R := hz.2
        have hmesh' : rs z ∈ scaleLatticeSet d
            (TranslationalTilings.quotientCoset
              (TranslationalTilings.directionSubgroup u) R) :=
          ⟨z, hzQ, rfl⟩
        rw [hcarrier R] at hmesh'
        exact hmesh'.1
  let OR : RationalSliceOrbit K (scaleLatticeSet d A)
      (scaleDirection d hd within O.within_ne_zero)
      (scaleDirection d hd transverse htransverse) := {
    phases := phases
    phase_iff_nonempty := fun Q ↦ (hcentres Q).symm
    phases_nonempty := by
      obtain ⟨Q, hQ⟩ := O.phases_nonempty
      exact ⟨scaleSlice Q, ⟨Q, hQ, rfl⟩⟩
    slice_periodic := by
      intro Q hQ x
      obtain ⟨R, hR, hRQ⟩ := hQ
      have hslice :
          (scaleSlice R).centres (scaleLatticeSet d A) =
            Tiling.AxisParallel.RationalMesh.rationalScale d ''
              (DiscreteSlice u R A) := by
        symm
        exact scaleDiscreteSlice_centres hd hu ⟨m, hm, hwithin⟩
          scaleSlice hcarrier A R
      rw [← hRQ, hslice]
      change x + (scaleDirection d hd within O.within_ne_zero).toPlane ∈
          rs '' (DiscreteSlice u R A) ↔
        x ∈ rs '' (DiscreteSlice u R A)
      rw [scaleDirection_toPlane]
      constructor
      · rintro ⟨z, hz, hzx⟩
        have hz0 : rs (z - within) = x := by
          have hm' := Tiling.AxisParallel.RationalMesh.rationalScale_add hd
            z (-within)
          have hneg : rs (-within) = -rs within := by
            have hz0' := Tiling.AxisParallel.RationalMesh.rationalScale_add hd
              within (-within)
            have hzero : rs 0 = 0 := by
              change Tiling.AxisParallel.RationalMesh.rationalScale d 0 = 0
              apply add_left_cancel (a :=
                Tiling.AxisParallel.RationalMesh.rationalScale d 0)
              simpa using
                (Tiling.AxisParallel.RationalMesh.rationalScale_add hd 0 0).symm
            have hz0sum : rs within + rs (-within) = 0 := by
              have hz0'rs : rs 0 = rs within + rs (-within) := by
                simpa [rs] using hz0'
              rw [hzero] at hz0'rs
              exact hz0'rs.symm
            exact eq_neg_of_add_eq_zero_right hz0sum
          have hm'rs : rs (z + -within) = rs z + rs (-within) := by
            simpa [rs] using hm'
          have hz0' : rs (z + -within) = x := by
            rw [hm'rs, hneg, hzx]
            abel
          simpa [sub_eq_add_neg] using hz0'
        have hzD : z - within ∈ DiscreteSlice u R A := by
          apply (O.slice_periodic R hR (z - within)).mp
          simpa [sub_add_cancel] using hz
        exact ⟨z - within, hzD, hz0⟩
      · rintro ⟨z, hz, hzx⟩
        have hzD : z + within ∈ DiscreteSlice u R A := by
          apply (O.slice_periodic R hR z).mpr
          simpa [add_sub_cancel] using hz
        have hzsum : rs (z + within) = x + rs within := by
          calc
            rs (z + within) = rs z + rs within := by
              simpa [rs] using
                (Tiling.AxisParallel.RationalMesh.rationalScale_add hd z within)
            _ = x + rs within := by rw [hzx]
        exact ⟨z + within, hzD, hzsum⟩
    phase_translate_mem := by
      intro Q hQ n
      obtain ⟨R, hR, hRQ⟩ := hQ
      have hzero : rs 0 = 0 := by
        change Tiling.AxisParallel.RationalMesh.rationalScale d 0 = 0
        apply add_left_cancel (a :=
          Tiling.AxisParallel.RationalMesh.rationalScale d 0)
        simpa using
          (Tiling.AxisParallel.RationalMesh.rationalScale_add hd 0 0).symm
      let f : ZPlane →+ Tiling.Plane := {
        toFun := rs
        map_zero' := hzero
        map_add' := Tiling.AxisParallel.RationalMesh.rationalScale_add hd }
      have hsmul : rs (n • transverse) = n • rs transverse :=
        f.map_zsmul n transverse
      have htransPlane :
          (scaleDirection d hd transverse htransverse).toPlane =
            rs transverse := by
        exact scaleDirection_toPlane hd transverse htransverse
      have hperiod : rs (n • transverse) =
          n • (scaleDirection d hd transverse htransverse).toPlane := by
        rw [hsmul, htransPlane]
      have hR' := O.phase_translate_mem R hR n
      refine ⟨R + QuotientAddGroup.mk'
        (TranslationalTilings.directionSubgroup u) (n • transverse), hR', ?_⟩
      calc
        scaleSlice (R + QuotientAddGroup.mk'
            (TranslationalTilings.directionSubgroup u) (n • transverse)) =
            (scaleSlice R).vadd (rs (n • transverse)) :=
          hvadd R (n • transverse)
        _ = Q.vadd (n •
            (scaleDirection d hd transverse htransverse).toPlane) := by
          rw [hRQ, hperiod]
    regularSupport_transport := by
      intro Q hQ n
      obtain ⟨R, hR, hRQ⟩ := hQ
      let rs := Tiling.AxisParallel.RationalMesh.rationalScale d
      have hzero : rs 0 = 0 := by
        change Tiling.AxisParallel.RationalMesh.rationalScale d 0 = 0
        apply add_left_cancel (a :=
          Tiling.AxisParallel.RationalMesh.rationalScale d 0)
        simpa using
          (Tiling.AxisParallel.RationalMesh.rationalScale_add hd 0 0).symm
      let f : ZPlane →+ Tiling.Plane := {
        toFun := rs
        map_zero' := hzero
        map_add' := Tiling.AxisParallel.RationalMesh.rationalScale_add hd }
      have hsmul (a : ZPlane) (k : ℤ) : rs (k • a) = k • rs a :=
        f.map_zsmul k a
      have hraw (a : ZPlane) (B B' : Set ZPlane)
          (hB : TranslationalTilings.translateSet a B = B') :
          rs a +ᵥ (⋃ z : B, Tiling.AxisParallel.RationalMesh.meshCell d z.1) =
            (⋃ z : B', Tiling.AxisParallel.RationalMesh.meshCell d z.1) := by
        ext x
        constructor
        · rintro ⟨y, hyU, hxy⟩
          obtain ⟨z, hyz⟩ := Set.mem_iUnion.mp hyU
          refine Set.mem_iUnion_of_mem ⟨z.1 + a, ?_⟩ ?_
          · rw [← hB]
            change z.1 + a - a ∈ B
            have hza : z.1 + a - a = z.1 := by abel
            rw [hza]
            exact z.2
          · rw [Tiling.AxisParallel.RationalMesh.meshCell_add hd]
            refine ⟨y, hyz, ?_⟩
            change rs a + y = x
            simpa [hxy]
        · intro hx
          obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx
          have hzB' : z.1 ∈ TranslationalTilings.translateSet a B := by
            rw [hB]
            exact z.2
          change z.1 - a ∈ B at hzB'
          have hzcell : Tiling.AxisParallel.RationalMesh.meshCell d z.1 =
              rs a +ᵥ Tiling.AxisParallel.RationalMesh.meshCell d (z.1 - a) := by
            simpa only [sub_add_cancel] using
              (Tiling.AxisParallel.RationalMesh.meshCell_add hd (z.1 - a) a)
          rw [hzcell] at hz
          obtain ⟨y, hy, hxy⟩ := hz
          refine ⟨y, Set.mem_iUnion_of_mem ⟨z.1 - a, hzB'⟩ hy, ?_⟩
          exact hxy
      have hreg (a : ZPlane) (B B' : Set ZPlane)
          (hB : TranslationalTilings.translateSet a B = B') :
          rs a +ᵥ Tiling.AxisParallel.RationalMesh.regularizedCellUnion d B =
            Tiling.AxisParallel.RationalMesh.regularizedCellUnion d B' := by
        rw [Tiling.AxisParallel.RationalMesh.regularizedCellUnion,
          Tiling.AxisParallel.RationalMesh.regularizedCellUnion,
          ← interior_vadd, ← closure_vadd, hraw a B B']
        exact hB
      have hsliceR :
          (scaleSlice R).centres (scaleLatticeSet d A) =
            rs '' (DiscreteSlice u R A) := by
        symm
        exact scaleDiscreteSlice_centres hd hu ⟨m, hm, hwithin⟩
          scaleSlice hcarrier A R
      have hR' := O.phase_translate_mem R hR n
      let R' := R + QuotientAddGroup.mk'
        (TranslationalTilings.directionSubgroup u) (n • transverse)
      have hsliceR' :
          (scaleSlice R').centres (scaleLatticeSet d A) =
            rs '' (DiscreteSlice u R' A) := by
        symm
        exact scaleDiscreteSlice_centres hd hu ⟨m, hm, hwithin⟩
          scaleSlice hcarrier A R'
      have hscaledWithin :
          (scaleDirection d hd within O.within_ne_zero).toPlane = rs within :=
        scaleDirection_toPlane hd within O.within_ne_zero
      have hscaledTransverse :
          (scaleDirection d hd transverse htransverse).toPlane = rs transverse :=
        scaleDirection_toPlane hd transverse htransverse
      have hperiod : rs (n • transverse) =
          n • (scaleDirection d hd transverse htransverse).toPlane := by
        rw [hsmul, hscaledTransverse]
      have hQ' : Q.vadd (n •
          (scaleDirection d hd transverse htransverse).toPlane) =
          scaleSlice R' := by
        calc
          Q.vadd (n •
              (scaleDirection d hd transverse htransverse).toPlane) =
              (scaleSlice R).vadd (rs (n • transverse)) := by
            rw [hRQ, hperiod]
          _ = scaleSlice R' := (hvadd R (n • transverse)).symm
      have hregR := Tiling.AxisParallel.RationalMesh.regularSupport_rationalScale_image
        hd hMesh F hF
        (DiscreteSlice u R A)
      have hregR' := Tiling.AxisParallel.RationalMesh.regularSupport_rationalScale_image
        hd hMesh F hF
        (DiscreteSlice u R' A)
      calc
        n • (scaleDirection d hd transverse htransverse).toPlane +ᵥ
            regularSupport K (Q.centres (scaleLatticeSet d A)) =
            n • (scaleDirection d hd transverse htransverse).toPlane +ᵥ
              regularSupport K ((scaleSlice R).centres
                (scaleLatticeSet d A)) := by rw [hRQ]
        _ = n • (scaleDirection d hd transverse htransverse).toPlane +ᵥ
              Tiling.AxisParallel.RationalMesh.regularizedCellUnion d
                (Tiling.RationalPolygonal.discreteCarrier F
                  (DiscreteSlice u R A)) := by rw [hsliceR, hregR]
        _ = rs (n • transverse) +ᵥ
              Tiling.AxisParallel.RationalMesh.regularizedCellUnion d
                (Tiling.RationalPolygonal.discreteCarrier F
                  (DiscreteSlice u R A)) := by rw [hperiod]
        _ = Tiling.AxisParallel.RationalMesh.regularizedCellUnion d
              (Tiling.RationalPolygonal.discreteCarrier F
                (DiscreteSlice u R' A)) :=
          hreg (n • transverse)
            (Tiling.RationalPolygonal.discreteCarrier F
              (DiscreteSlice u R A))
            (Tiling.RationalPolygonal.discreteCarrier F
              (DiscreteSlice u R' A))
            (O.carrier_transport R hR n)
        _ = regularSupport K ((scaleSlice R').centres
              (scaleLatticeSet d A)) := by rw [hsliceR', hregR']
        _ = regularSupport K ((Q.vadd (n •
              (scaleDirection d hd transverse htransverse).toPlane)).centres
              (scaleLatticeSet d A)) := by rw [hQ']
    }
  exact ⟨OR, rfl⟩


private theorem scaleDirection_linearCombination :
    ∀ {d : ℕ} (hd : 0 < d) {h g within : ZPlane}
      (hh : h ≠ 0) (hg : g ≠ 0) (hwithin : within ≠ 0)
      (k l : ℤ), within = k • h + l • g →
      (scaleDirection d hd within hwithin).coordinates =
        RationalDirection.linearCombination
          (scaleDirection d hd h hh) (scaleDirection d hd g hg) k l := by
  intro d hd h g within hh hg hwithin k l heq
  funext i
  simp only [scaleDirection, RationalDirection.coordinates,
    RationalDirection.linearCombination]
  have hi := congrFun heq i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
  rw [hi]
  push_cast
  field_simp

private theorem scaleBasis_linearIndependent :
    ∀ {d : ℕ} (hd : 0 < d) {h g : ZPlane}
      (hh : h ≠ 0) (hg : g ≠ 0),
      TranslationalTilings.wedge h g ≠ 0 →
      LinearIndependent ℝ
        ![(scaleDirection d hd h hh).toPlane,
          (scaleDirection d hd g hg).toPlane] := by
  intro d hd h g hh hg hw
  rw [linearIndependent_fin2]
  constructor
  · intro hz
    have hzre := congrArg Complex.re hz
    have hzim := congrArg Complex.im hz
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, RationalDirection.toPlane,
      RationalDirection.coordinates, ne_eq, scaleDirection, Fin.isValue,
      Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Complex.ofReal_div,
      Complex.ofReal_intCast, Complex.ofReal_natCast, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Complex.add_re, Complex.div_natCast_re,
      Complex.intCast_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.div_natCast_im, Complex.intCast_im, zero_div, Complex.I_im,
      mul_one, sub_self, add_zero, Complex.zero_re, div_eq_zero_iff,
      Int.cast_eq_zero, Nat.cast_eq_zero, Complex.add_im, Complex.mul_im,
      zero_add, Complex.zero_im] at hzre hzim
    have hwR : (TranslationalTilings.wedge h g : ℝ) ≠ 0 := by
      exact_mod_cast hw
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    rcases hzre with hzre | hzre
    · rcases hzim with hzim | hzim
      · apply hwR
        norm_num [TranslationalTilings.wedge, hzre, hzim]
      · exact (Nat.ne_of_gt hd) hzim
    · exact (Nat.ne_of_gt hd) hzre
  · intro a ha
    have hare := congrArg Complex.re ha
    have haim := congrArg Complex.im ha
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, RationalDirection.toPlane,
      RationalDirection.coordinates, ne_eq, scaleDirection, Fin.isValue,
      Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Complex.ofReal_div,
      Complex.ofReal_intCast, Complex.ofReal_natCast, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, smul_add, Complex.real_smul, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.div_natCast_re,
      Complex.intCast_re, Complex.ofReal_im, Complex.div_natCast_im,
      Complex.intCast_im, zero_div, mul_zero, sub_zero, Complex.I_re,
      Complex.I_im, mul_one, sub_self, Complex.mul_im, add_zero, zero_mul,
      Matrix.cons_val_zero, Complex.add_im, zero_add] at hare haim
    have hwR : (TranslationalTilings.wedge h g : ℝ) ≠ 0 := by
      exact_mod_cast hw
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    have hare' : a * (g 0 : ℝ) = (h 0 : ℝ) := by
      have hare0 := hare
      rw [← mul_div_assoc] at hare0
      have hcross := (div_eq_div_iff hdR hdR).mp hare0
      exact mul_right_cancel₀ hdR hcross
    have haim' : a * (g 1 : ℝ) = (h 1 : ℝ) := by
      have haim0 := haim
      rw [← mul_div_assoc] at haim0
      have hcross := (div_eq_div_iff hdR hdR).mp haim0
      exact mul_right_cancel₀ hdR hcross
    have hdet : (h 0 : ℝ) * (g 1 : ℝ) - (h 1 : ℝ) * (g 0 : ℝ) = 0 := by
      calc
        (h 0 : ℝ) * (g 1 : ℝ) - (h 1 : ℝ) * (g 0 : ℝ) =
            (a * (g 0 : ℝ)) * (g 1 : ℝ) - (a * (g 1 : ℝ)) * (g 0 : ℝ) := by
          rw [hare', haim']
        _ = 0 := by ring
    apply hwR
    exact_mod_cast hdet

private theorem scale_parts_pairwiseDisjoint :
    ∀ {d m : ℕ}, 0 < d → ∀ {A : Set ZPlane}
      {part : Fin m → Set ZPlane},
      Set.PairwiseDisjoint Set.univ part → (⋃ i, part i) = A →
      Set.PairwiseDisjoint Set.univ
          (fun i ↦ scaleLatticeSet d (part i)) ∧
        (⋃ i, scaleLatticeSet d (part i)) = scaleLatticeSet d A := by
  intro d m hd A part hdisj hunion
  constructor
  · intro i _hi j _hj hij
    change Disjoint (scaleLatticeSet d (part i)) (scaleLatticeSet d (part j))
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases hxi with ⟨a, hai, hax⟩
    rcases hxj with ⟨b, hbj, hbx⟩
    have hscale : RationalMesh.rationalScale d a = RationalMesh.rationalScale d b :=
      hax.trans hbx.symm
    have hab : a = b := (RationalMesh.rationalScale_injective hd) hscale
    exact Set.disjoint_left.mp (hdisj (Set.mem_univ _) (Set.mem_univ _) hij)
      hai (hab ▸ hbj)
  · simp only [scaleLatticeSet]
    calc
      (⋃ i, Tiling.AxisParallel.RationalMesh.rationalScale d '' part i) =
          Tiling.AxisParallel.RationalMesh.rationalScale d '' (⋃ i, part i) :=
        (Set.image_iUnion).symm
      _ = Tiling.AxisParallel.RationalMesh.rationalScale d '' A :=
        congrArg (fun X ↦ Tiling.AxisParallel.RationalMesh.rationalScale d '' X) hunion

private theorem scaleLatticeSet_eq_empty_iff :
    ∀ {d : ℕ}, 0 < d → ∀ {A : Set ZPlane},
      scaleLatticeSet d A = ∅ ↔ A = ∅ := by
  intro d hd A
  constructor
  · intro hA
    rw [scaleLatticeSet] at hA
    exact Set.image_eq_empty.mp hA
  · intro hA
    rw [scaleLatticeSet, hA, Set.image_empty]


/-- The two transport fields of a rational slice orbit, bundled as the article's shift endpoint. -/
theorem rationalSlices_shiftTransport
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (D : RationalDirectionalDecomposition K T)
    (i : Fin D.numberOfParts)
    (Q : RationalSlice (D.direction i))
    (hQ : Q ∈ (D.orbit i).phases) (n : ℤ) :
    Q.vadd (n • D.gamma.toPlane) ∈ (D.orbit i).phases ∧
      n • D.gamma.toPlane +ᵥ
          Tiling.AxisParallel.regularSupport K (Q.centres (D.part i)) =
        Tiling.AxisParallel.regularSupport K
          ((Q.vadd (n • D.gamma.toPlane)).centres (D.part i)) :=
  ⟨(D.orbit i).phase_translate_mem Q hQ n,
    (D.orbit i).regularSupport_transport Q hQ n⟩

theorem exists_rationalFinerStructure :
    ∀ {K : Region} {T E : Set Tiling.Plane} {d : ℕ}, 0 < d →
      OnRationalMesh d (K.vertices ∪ T) →
      IsOpen E → interior (closure E) = E →
      (∀ r : ℝ, (r * Complex.I) +ᵥ E = E) →
      (∃ b : ℝ, b ≠ 0 ∧ (b : Tiling.Plane) +ᵥ E = E) →
      TilesOn K T E → Nonempty (RationalDirectionalDecomposition K T) := by
  intro K T E d hd hmesh hEopen hEregular hvertical hhorizontal htiles
  have hK : OnRationalMesh d K.vertices := by
    intro x hx
    exact hmesh (Set.mem_union_left _ hx)
  have hT : OnRationalMesh d T := by
    intro x hx
    exact hmesh (Set.mem_union_right _ hx)
  obtain ⟨ell, F, hell, hFne, hF, hscalar, htilesRaster⟩ :=
    exists_exactPeriodicRaster hd hK hT hEopen hEregular hvertical
      hhorizontal htiles
  obtain ⟨D⟩ :=
    exists_discreteFinerStructure hFne hell hscalar htilesRaster
  have hh : D.h ≠ 0 := by
    intro hzero
    apply D.independent
    rw [hzero]
    simp [TranslationalTilings.wedge]
  have hg : D.g ≠ 0 := by
    intro hzero
    apply D.independent
    rw [hzero]
    simp [TranslationalTilings.wedge]
  let lambda := scaleDirection d hd D.h hh
  let gamma := scaleDirection d hd D.g hg
  have hperiod_ne (i : Fin D.numberOfParts) :
      (D.direction i).period ≠ 0 := by
    change (D.direction i).hCoefficient • D.h +
      (D.direction i).gCoefficient • D.g ≠ 0
    rw [(D.direction i).period_eq]
    exact smul_ne_zero (D.direction i).multiple_ne_zero
      (D.direction i).primitive.1
  refine ⟨{
    lambda := lambda
    gamma := gamma
    basisIndependent := by
      exact scaleBasis_linearIndependent hd hh hg D.independent
    numberOfParts := D.numberOfParts
    number_zero_iff := by
      constructor
      · intro hm
        have hA := D.number_zero_iff.mp hm
        have himage : scaleLatticeSet d (rasterCentres d T) = ∅ := by
          rw [hA, scaleLatticeSet, Set.image_empty]
        rw [rasterCentres_image hd hT] at himage
        exact himage
      · intro hTempty
        apply D.number_zero_iff.mpr
        ext z
        simp [rasterCentres, hTempty]
    part := fun i ↦ scaleLatticeSet d (D.part i)
    part_nonempty := by
      intro i
      obtain ⟨x, hx⟩ := D.part_nonempty i
      exact ⟨Tiling.AxisParallel.RationalMesh.rationalScale d x,
        ⟨x, hx, rfl⟩⟩
    parts_pairwiseDisjoint := by
      exact (scale_parts_pairwiseDisjoint hd D.pairwiseDisjoint
        D.iUnion_parts).1
    parts_union := by
      rw [(scale_parts_pairwiseDisjoint hd D.pairwiseDisjoint
        D.iUnion_parts).2, rasterCentres_image hd hT]
    lambdaCoefficient := fun i ↦ (D.direction i).hCoefficient
    gammaCoefficient := fun i ↦ (D.direction i).gCoefficient
    lambdaCoefficient_ne_zero := fun i ↦
      (D.direction i).hCoefficient_ne_zero
    direction := fun i ↦
      scaleDirection d hd (D.direction i).period (hperiod_ne i)
    direction_coordinates := by
      intro i
      exact scaleDirection_linearCombination hd hh hg (hperiod_ne i)
        (D.direction i).hCoefficient (D.direction i).gCoefficient rfl
    orbit := by
      intro i
      have hres :=
        exists_scaleDiscreteOrbit hd hK F hF
          (_hu := (D.direction i).primitive) (htransverse := hg)
          (O := D.sliceOrbit i)
      have hres₁ := Exists.choose_spec hres
      let scaleSlice := Exists.choose hres₁
      have hres₂ := Exists.choose_spec hres₁
      have hOR : ∃ OR : RationalSliceOrbit K
          (scaleLatticeSet d (D.part i))
          (scaleDirection d hd (D.direction i).period (hperiod_ne i))
          (scaleDirection d hd D.g hg),
          OR.phases = scaleSlice '' (D.sliceOrbit i).phases :=
        hres₂.2.2.2.2
      exact Exists.choose hOR
  }⟩
end Tiling.AxisParallel.Terminal
