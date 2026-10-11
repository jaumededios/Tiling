import Tiling.AxisParallel.OneDimensional.FiniteInterval.IntervalGeometry

/-!
# Local rigidity for interval tilings

Two tilings of the same measurable target agree everywhere once their centres
agree on a window whose radius depends only on the tile.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Function MeasureTheory Set
open scoped Pointwise
noncomputable section

namespace Tiling.AxisParallel.OneDimensional.FiniteInterval

private theorem exists_right_interval_disjoint_of_locallyFinite
    {S : Set ℝ} {h : ℝ}
    (hloc : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite) :
    ∃ ε : ℝ, 0 < ε ∧ Ioo h (h + ε) ∩ S = ∅ := by
  have hf : (S ∩ Icc h (h + 1)).Finite := hloc _ (Metric.isBounded_Icc _ _)
  let F := hf.toFinset
  let ds : Finset ℝ := F.filter (h < ·)
  by_cases hd : ds.Nonempty
  · let m := ds.min' hd
    have hm : h < m := (Finset.mem_filter.mp (ds.min'_mem hd)).2
    refine ⟨(m - h) / 2, by linarith, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_Ioo, mem_empty_iff_false, iff_false]
    rintro ⟨hhx, hxS⟩
    have hxI : x ∈ Icc h (h + 1) := by
      constructor
      · exact hhx.1.le
      · have hmF : m ∈ S ∩ Icc h (h + 1) := by
          have hmF' : m ∈ F := (Finset.mem_filter.mp (ds.min'_mem hd)).1
          change m ∈ hf.toFinset at hmF'
          simpa only [Set.Finite.mem_toFinset] using hmF'
        linarith [hmF.2.2, hhx.2]
    have hxds : x ∈ ds := Finset.mem_filter.mpr
      ⟨(by simpa [F] using (show x ∈ S ∩ Icc h (h+1) from ⟨hxS,hxI⟩)), hhx.1⟩
    have := ds.min'_le x hxds
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_Ioo, mem_empty_iff_false, iff_false]
    rintro ⟨⟨hhx, hxh⟩, hxS⟩
    apply hd
    refine ⟨x, Finset.mem_filter.mpr ⟨?_, hhx⟩⟩
    simpa [F] using
      (show x ∈ S ∩ Icc h (h + 1) from ⟨hxS, ⟨hhx.le, hxh.le⟩⟩)

private theorem exists_left_interval_disjoint_of_locallyFinite
    {S : Set ℝ} {h : ℝ}
    (hloc : ∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite) :
    ∃ ε : ℝ, 0 < ε ∧ Ioo (h - ε) h ∩ S = ∅ := by
  have hf : (S ∩ Icc (h - 1) h).Finite := hloc _ (Metric.isBounded_Icc _ _)
  let F := hf.toFinset
  let ds : Finset ℝ := F.filter (· < h)
  by_cases hd : ds.Nonempty
  · let m := ds.max' hd
    have hm : m < h := (Finset.mem_filter.mp (ds.max'_mem hd)).2
    refine ⟨(h - m) / 2, by linarith, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_Ioo, mem_empty_iff_false, iff_false]
    rintro ⟨⟨hmx, hxh⟩, hxS⟩
    have hxI : x ∈ Icc (h - 1) h := by
      constructor
      · have hmF : m ∈ S ∩ Icc (h - 1) h :=
          by
            have hmF' : m ∈ F := (Finset.mem_filter.mp (ds.max'_mem hd)).1
            change m ∈ hf.toFinset at hmF'
            simpa only [Set.Finite.mem_toFinset] using hmF'
        exact le_trans hmF.2.1 (by linarith)
      · exact hxh.le
    have hxds : x ∈ ds := Finset.mem_filter.mpr
      ⟨(by simpa [F] using (show x ∈ S ∩ Icc (h-1) h from ⟨hxS,hxI⟩)), hxh⟩
    have := ds.le_max' x hxds
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_Ioo, mem_empty_iff_false, iff_false]
    rintro ⟨⟨hhx, hxh⟩, hxS⟩
    apply hd
    refine ⟨x, Finset.mem_filter.mpr ⟨?_, hxh⟩⟩
    simpa [F] using
      (show x ∈ S ∩ Icc (h - 1) h from ⟨hxS, ⟨hhx.le, hxh.le⟩⟩)

private theorem exists_least_right_discrepancy
    {H H' : Set ℝ} {d : ℝ}
    (hH : ∀ Q, Bornology.IsBounded Q → (H ∩ Q).Finite)
    (hH' : ∀ Q, Bornology.IsBounded Q → (H' ∩ Q).Finite)
    (hne : (((H \ H') ∪ (H' \ H)) ∩ Ioi d).Nonempty) :
    ∃ h ∈ ((H \ H') ∪ (H' \ H)) ∩ Ioi d,
      ∀ k ∈ ((H \ H') ∪ (H' \ H)) ∩ Ioi d, h ≤ k := by
  rcases hne with ⟨s, hsD, hds⟩
  let D := (H \ H') ∪ (H' \ H)
  have hf : (D ∩ Ioc d s).Finite := by
    refine Set.Finite.subset
      ((hH (Icc d s) (Metric.isBounded_Icc d s)).union
        (hH' (Icc d s) (Metric.isBounded_Icc d s))) ?_
    intro x hx
    rcases hx.1 with hbranch | hbranch
    · exact Or.inl ⟨hbranch.1, ⟨hx.2.1.le, hx.2.2⟩⟩
    · exact Or.inr ⟨hbranch.1, ⟨hx.2.1.le, hx.2.2⟩⟩
  have hn : (D ∩ Ioc d s).Nonempty := ⟨s, hsD, hds, le_rfl⟩
  let F := hf.toFinset
  have hFn : F.Nonempty := by simpa [F] using hn
  let m := F.min' hFn
  have mmem : m ∈ D ∩ Ioc d s := by
    simpa only [F, Set.Finite.mem_toFinset] using F.min'_mem hFn
  refine ⟨m, ⟨mmem.1, mmem.2.1⟩, ?_⟩
  · intro k ⟨hkD, hdk⟩
    by_cases hks : k ≤ s
    · apply F.min'_le k
      simpa only [F, Set.Finite.mem_toFinset] using
        (show k ∈ D ∩ Ioc d s from ⟨hkD, hdk, hks⟩)
    · exact le_trans mmem.2.2 (le_of_not_ge hks)

private theorem exists_greatest_left_discrepancy
    {H H' : Set ℝ} {d : ℝ}
    (hH : ∀ Q, Bornology.IsBounded Q → (H ∩ Q).Finite)
    (hH' : ∀ Q, Bornology.IsBounded Q → (H' ∩ Q).Finite)
    (hne : (((H \ H') ∪ (H' \ H)) ∩ Iio d).Nonempty) :
    ∃ h ∈ ((H \ H') ∪ (H' \ H)) ∩ Iio d,
      ∀ k ∈ ((H \ H') ∪ (H' \ H)) ∩ Iio d, k ≤ h := by
  rcases hne with ⟨s, hsD, hsd⟩
  let D := (H \ H') ∪ (H' \ H)
  have hf : (D ∩ Ico s d).Finite := by
    refine Set.Finite.subset
      ((hH (Icc s d) (Metric.isBounded_Icc s d)).union
        (hH' (Icc s d) (Metric.isBounded_Icc s d))) ?_
    intro x hx
    rcases hx.1 with hbranch | hbranch
    · exact Or.inl ⟨hbranch.1, ⟨hx.2.1, hx.2.2.le⟩⟩
    · exact Or.inr ⟨hbranch.1, ⟨hx.2.1, hx.2.2.le⟩⟩
  have hn : (D ∩ Ico s d).Nonempty := ⟨s, hsD, le_rfl, hsd⟩
  let F := hf.toFinset
  have hFn : F.Nonempty := by simpa [F] using hn
  let m := F.max' hFn
  have mmem : m ∈ D ∩ Ico s d := by
    simpa only [F, Set.Finite.mem_toFinset] using F.max'_mem hFn
  refine ⟨m, ⟨mmem.1, mmem.2.2⟩, ?_⟩
  · intro k ⟨hkD, hkd⟩
    by_cases hsk : s ≤ k
    · apply F.le_max' k
      simpa only [F, Set.Finite.mem_toFinset] using
        (show k ∈ D ∩ Ico s d from ⟨hkD, hsk, hkd⟩)
    · exact le_trans (le_of_not_ge hsk) mmem.2.1

private theorem exists_mem_Ioo_of_ae {P : ℝ → Prop} {u v : ℝ} (huv : u < v)
    (hP : ∀ᵐ x ∂volume, P x) : ∃ x ∈ Ioo u v, P x := by
  have hμ : volume.restrict (Ioo u v) ≠ 0 := by
    intro hz
    have : volume (Ioo u v) = 0 := by
      rw [← Measure.restrict_apply_univ (Ioo u v), hz]
      simp
    rw [Real.volume_Ioo] at this
    simp [ENNReal.ofReal_eq_zero, not_le.mpr (sub_pos.mpr huv)] at this
  let hne : (ae (volume.restrict (Ioo u v))).NeBot := ae_neBot.mpr hμ
  have hp' : ∀ᵐ x ∂volume.restrict (Ioo u v), P x := hP.filter_mono ae_restrict_le
  rcases @Filter.Eventually.exists ℝ _ (ae (volume.restrict (Ioo u v))) hne
      (hp'.and (ae_restrict_mem measurableSet_Ioo)) with ⟨x,hp,hx⟩
  exact ⟨x,hx,hp⟩

-- Propagation lemmas are kept separate so their symmetry remains visible during integration.
private theorem no_right_discrepancy
    {B H H' X : Set ℝ} {a b η c R : ℝ}
    (_hab : a < b) (hη : 0 < η) (hBsub : B ⊆ Icc a b)
    (hleft : Ioo a (a + η) ⊆ B) (hBopen : IsOpen B) (hR : b - a ≤ R)
    (hTile : LineTilesOn B H X) (hTile' : LineTilesOn B H' X)
    (hHlocal : ∀ Q, Bornology.IsBounded Q → (H ∩ Q).Finite)
    (hH'local : ∀ Q, Bornology.IsBounded Q → (H' ∩ Q).Finite)
    (hagree : H ∩ Icc (c - R) (c + R) = H' ∩ Icc (c - R) (c + R)) :
    ((H \ H') ∪ (H' \ H)) ∩ Ioi (c + R) = ∅ := by
  by_contra hn
  have hne : (((H \ H') ∪ (H' \ H)) ∩ Ioi (c + R)).Nonempty := nonempty_iff_ne_empty.mpr hn
  rcases exists_least_right_discrepancy hHlocal hH'local hne with ⟨h, ⟨hhD, hhgt⟩, hmin⟩
  change c + R < h at hhgt
  wlog hcase : h ∈ H' \ H generalizing H H'
  · have hh : h ∈ H \ H' := hhD.resolve_right hcase
    have hn' : ¬ ((H' \ H) ∪ (H \ H')) ∩ Ioi (c + R) = ∅ := by simpa [union_comm] using hn
    have hne' : (((H' \ H) ∪ (H \ H')) ∩ Ioi (c + R)).Nonempty := nonempty_iff_ne_empty.mpr hn'
    exact this hTile' hTile hH'local hHlocal hagree.symm
      hn' hne' (by simpa [union_comm] using hmin) (by simpa [union_comm] using hhD) hh
  have hh := hcase
  have hhH' : h ∈ H' := hh.1
  have hhnotH : h ∉ H := hh.2
  rcases exists_right_interval_disjoint_of_locallyFinite (h := h) hHlocal with ⟨ε0, hε0, hgap⟩
  let ε := min ε0 η
  have hε : 0 < ε := lt_min hε0 hη
  have hae : ∀ᵐ x ∂volume,
      (x ∈ X ↔ ∃ l : H, x ∈ (l : ℝ) +ᵥ B) ∧
      (x ∈ X ↔ ∃ l : H', x ∈ (l : ℝ) +ᵥ B) := hTile.2.2.2.2.and hTile'.2.2.2.2
  rcases exists_mem_Ioo_of_ae (by linarith : h + a < h + a + ε) hae with ⟨x, hxI, hx, hx'⟩
  rcases hxI with ⟨hxlo, hxhi⟩
  have hxTile' : x ∈ (h : ℝ) +ᵥ B := by
    rw [mem_vadd_set]
    refine ⟨x-h, hleft ⟨by linarith, ?_⟩, ?_⟩
    · dsimp [ε] at *
      linarith [min_le_right ε0 η]
    · simp [vadd_eq_add]
  have hxX : x ∈ X := hx'.mpr ⟨⟨h, hhH'⟩, hxTile'⟩
  rcases hx.mp hxX with ⟨k, hxk⟩
  have hkH : (k : ℝ) ∈ H := k.property
  rcases mem_vadd_set.mp hxk with ⟨y, hyB, hyx⟩
  change (k : ℝ) + y = x at hyx
  have hxb : x - b ≤ (k : ℝ) := by
    have := hBsub hyB
    linarith [this.2]
  have hka : (k : ℝ) ≤ x - a := by
    have := hBsub hyB
    linarith [this.1]
  have hklt : (k : ℝ) < h := by
    have hkupper : (k : ℝ) < h + ε0 := by dsimp [ε] at *; linarith [min_le_left ε0 η]
    by_contra hnot
    have hle : h ≤ (k : ℝ) := le_of_not_gt hnot
    rcases hle.eq_or_lt with rfl | hlt
    · exact hhnotH hkH
    · have hkbad : (k : ℝ) ∈ Ioo h (h + ε0) ∩ H := ⟨⟨hlt, hkupper⟩, hkH⟩
      rw [hgap] at hkbad
      exact hkbad
  have hklower : h - R < (k : ℝ) := by linarith
  have hkH' : (k : ℝ) ∈ H' := by
    by_cases hk : (k : ℝ) ≤ c + R
    · have kwin : (k : ℝ) ∈ Icc (c - R) (c + R) := ⟨by linarith [hhgt], hk⟩
      have : (k : ℝ) ∈ H' ∩ Icc (c - R) (c + R) := by rw [← hagree]; exact ⟨hkH, kwin⟩
      exact this.1
    · by_contra hk'
      have kd : (k : ℝ) ∈ (H \ H') ∪ (H' \ H) := Or.inl ⟨hkH, hk'⟩
      exact (not_le_of_gt hklt) (hmin _ ⟨kd, lt_of_not_ge hk⟩)
  have hdis : AEDisjoint volume ((h : ℝ) +ᵥ B) ((k : ℝ) +ᵥ B) :=
    hTile'.2.2.2.1 hhH' hkH' (by exact_mod_cast ne_of_gt hklt)
  have hopen : IsOpen (((h : ℝ) +ᵥ B) ∩ ((k : ℝ) +ᵥ B)) :=
    (hBopen.vadd _).inter (hBopen.vadd _)
  have hnon : (((h : ℝ) +ᵥ B) ∩ ((k : ℝ) +ᵥ B)).Nonempty := ⟨x, hxTile', hxk⟩
  exact (ne_of_gt (hopen.measure_pos volume hnon)) hdis

private theorem no_left_discrepancy
    {B H H' X : Set ℝ} {a b η c R : ℝ}
    (_hab : a < b) (hη : 0 < η) (hBsub : B ⊆ Icc a b)
    (hright : Ioo (b - η) b ⊆ B) (hBopen : IsOpen B) (hR : b - a ≤ R)
    (hTile : LineTilesOn B H X) (hTile' : LineTilesOn B H' X)
    (hHlocal : ∀ Q, Bornology.IsBounded Q → (H ∩ Q).Finite)
    (hH'local : ∀ Q, Bornology.IsBounded Q → (H' ∩ Q).Finite)
    (hagree : H ∩ Icc (c - R) (c + R) = H' ∩ Icc (c - R) (c + R)) :
    ((H \ H') ∪ (H' \ H)) ∩ Iio (c - R) = ∅ := by
  by_contra hn
  have hne := nonempty_iff_ne_empty.mpr hn
  rcases exists_greatest_left_discrepancy hHlocal hH'local hne with ⟨h, ⟨hhD, hhlt⟩, hmax⟩
  change h < c - R at hhlt
  wlog hcase : h ∈ H' \ H generalizing H H'
  · have hh : h ∈ H \ H' := hhD.resolve_right hcase
    have hn' : ¬ ((H' \ H) ∪ (H \ H')) ∩ Iio (c - R) = ∅ := by simpa [union_comm] using hn
    have hne' : (((H' \ H) ∪ (H \ H')) ∩ Iio (c - R)).Nonempty := nonempty_iff_ne_empty.mpr hn'
    exact this hTile' hTile hH'local hHlocal hagree.symm
      hn' hne' (by simpa [union_comm] using hmax) (by simpa [union_comm] using hhD) hh
  have hh := hcase
  have hhH' : h ∈ H' := hh.1
  have hhnotH : h ∉ H := hh.2
  rcases exists_left_interval_disjoint_of_locallyFinite (h := h) hHlocal with ⟨ε0, hε0, hgap⟩
  let ε := min ε0 η
  have hε : 0 < ε := lt_min hε0 hη
  have hae := hTile.2.2.2.2.and hTile'.2.2.2.2
  rcases exists_mem_Ioo_of_ae (by linarith : h + b - ε < h + b) hae with ⟨x, hxI, hx, hx'⟩
  rcases hxI with ⟨hxlo, hxhi⟩
  have hxTile' : x ∈ (h : ℝ) +ᵥ B := by
    rw [mem_vadd_set]
    refine ⟨x-h, hright ⟨?_, by linarith⟩, ?_⟩
    · dsimp [ε] at *
      linarith [min_le_right ε0 η]
    · simp [vadd_eq_add]
  have hxX : x ∈ X := hx'.mpr ⟨⟨h, hhH'⟩, hxTile'⟩
  rcases hx.mp hxX with ⟨k, hxk⟩
  have hkH : (k : ℝ) ∈ H := k.property
  rcases mem_vadd_set.mp hxk with ⟨y, hyB, hyx⟩
  change (k : ℝ) + y = x at hyx
  have hbds := hBsub hyB
  have hklower : h - ε0 < (k : ℝ) := by dsimp [ε] at *; linarith [min_le_left ε0 η, hbds.2]
  have hkupper : (k : ℝ) < h + R := by linarith [hbds.1]
  have hkgt : h < (k : ℝ) := by
    by_contra hnot
    have hle : (k : ℝ) ≤ h := le_of_not_gt hnot
    rcases hle.eq_or_lt with rfl | hlt
    · exact hhnotH hkH
    · have hkbad : (k : ℝ) ∈ Ioo (h - ε0) h ∩ H := ⟨⟨hklower, hlt⟩, hkH⟩
      rw [hgap] at hkbad
      exact hkbad
  have hkH' : (k : ℝ) ∈ H' := by
    by_cases hk : c - R ≤ (k : ℝ)
    · have kwin : (k : ℝ) ∈ Icc (c - R) (c + R) := ⟨hk, by linarith [hhlt]⟩
      have : (k : ℝ) ∈ H' ∩ Icc (c - R) (c + R) := by rw [← hagree]; exact ⟨hkH, kwin⟩
      exact this.1
    · by_contra hk'
      have kd : (k : ℝ) ∈ (H \ H') ∪ (H' \ H) := Or.inl ⟨hkH, hk'⟩
      exact (not_le_of_gt hkgt) (hmax _ ⟨kd, lt_of_not_ge hk⟩)
  have hdis : AEDisjoint volume ((h : ℝ) +ᵥ B) ((k : ℝ) +ᵥ B) :=
    hTile'.2.2.2.1 hhH' hkH' (by exact_mod_cast ne_of_lt hkgt)
  have hopen : IsOpen (((h : ℝ) +ᵥ B) ∩ ((k : ℝ) +ᵥ B)) :=
    (hBopen.vadd _).inter (hBopen.vadd _)
  have hnon : (((h : ℝ) +ᵥ B) ∩ ((k : ℝ) +ᵥ B)).Nonempty := ⟨x, hxTile', hxk⟩
  exact (ne_of_gt (hopen.measure_pos volume hnon)) hdis

/-- Two tilings of the same measurable target by a positive finite union of open intervals are
determined by their centres in one tile-sized window. -/
theorem finiteInterval_lineTilingsOn_localRigidity
    {B : Set ℝ}
    (hB : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion B)
    (hBpositive : 0 < (MeasureTheory.volume B).toReal) :
    ∃ R : ℝ, 0 < R ∧
      ∀ (H H' X : Set ℝ) (c : ℝ),
        Tiling.AxisParallel.OneDimensional.LineTilesOn B H X →
        Tiling.AxisParallel.OneDimensional.LineTilesOn B H' X →
        H ∩ Set.Icc (c - R) (c + R) =
          H' ∩ Set.Icc (c - R) (c + R) →
        H = H' := by
      rcases IsFiniteIntervalRegion.extremeCollars hB hBpositive with
        ⟨a,b,ηL,ηR,hab,hηL,hηR,hsub,hleft,hright⟩
      refine ⟨b-a, sub_pos.mpr hab, ?_⟩
      intro H H' X c ht ht' hagree
      have hloc := finiteInterval_lineTilesOn_centres_locallyFinite hB hBpositive ht
      have hloc' := finiteInterval_lineTilesOn_centres_locallyFinite hB hBpositive ht'
      have hr := no_right_discrepancy hab hηL hsub hleft (IsFiniteIntervalRegion.isOpen hB)
        (le_rfl) ht ht' hloc hloc' hagree
      have hl := no_left_discrepancy hab hηR hsub hright (IsFiniteIntervalRegion.isOpen hB)
        (le_rfl) ht ht' hloc hloc' hagree
      ext x
      constructor <;> intro hx
      · by_contra hx'
        have hd : x ∈ (H \ H') ∪ (H' \ H) := Or.inl ⟨hx,hx'⟩
        by_cases hxl : x < c-(b-a)
        · have hempty : x ∈ (∅ : Set ℝ) := hl ▸ ⟨hd,hxl⟩
          exact hempty
        by_cases hxr : c+(b-a) < x
        · have hempty : x ∈ (∅ : Set ℝ) := hr ▸ ⟨hd,hxr⟩
          exact hempty
        have : x ∈ H' ∩ Icc (c-(b-a)) (c+(b-a)) := by
          rw [← hagree]
          exact ⟨hx, le_of_not_gt hxl, le_of_not_gt hxr⟩
        exact hx' this.1
      · by_contra hx'
        have hd : x ∈ (H \ H') ∪ (H' \ H) := Or.inr ⟨hx,hx'⟩
        by_cases hxl : x < c-(b-a)
        · have hempty : x ∈ (∅ : Set ℝ) := hl ▸ ⟨hd,hxl⟩
          exact hempty
        by_cases hxr : c+(b-a) < x
        · have hempty : x ∈ (∅ : Set ℝ) := hr ▸ ⟨hd,hxr⟩
          exact hempty
        have : x ∈ H ∩ Icc (c-(b-a)) (c+(b-a)) := by
          rw [hagree]
          exact ⟨hx, le_of_not_gt hxl, le_of_not_gt hxr⟩
        exact hx' this.1

end Tiling.AxisParallel.OneDimensional.FiniteInterval
