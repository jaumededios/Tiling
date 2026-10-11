import Tiling.AxisParallel.Foundations.OneDimensionalTilings
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Mass in a period cell

The translates of a bounded measurable tile have finitely many centre residues
in a positive period cell. Tonelli's theorem identifies the period length with
the tile's measure times the number of residues.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped Pointwise ENNReal
noncomputable section
namespace Tiling.AxisParallel.OneDimensional.FiniteInterval

private noncomputable def periodRepresentative (p x : ℝ) : ℝ :=
  x - (Int.floor (x / p) : ℝ) * p

private def periodDecode (L : Set ℝ) (p : ℝ) (u : ↥(L ∩ Ico 0 p) × ℤ) : ℝ :=
  u.1.1 + (u.2 : ℝ) * p

private def periodCell (f p : ℝ) (m : ℤ) : Set ℝ :=
  Ico (-f - (m : ℝ) * p) (p - f - (m : ℝ) * p)

private theorem periodRepresentative_mem_Ico {p : ℝ} (hp : 0 < p) (x : ℝ) :
    periodRepresentative p x ∈ Ico 0 p := by
  rw [mem_Ico]
  constructor
  · have h := Int.floor_le (x / p)
    dsimp [periodRepresentative]
    have := (le_div_iff₀ hp).mp h
    linarith
  · have h := Int.lt_floor_add_one (x / p)
    dsimp [periodRepresentative]
    have := (div_lt_iff₀ hp).mp h
    linarith

private theorem periodRepresentative_mem {L : Set ℝ} {p : ℝ} (_hp : 0 < p)
    (hperiod : p +ᵥ L = L) {x : ℝ} (hx : x ∈ L) : periodRepresentative p x ∈ L := by
  have hper : (((-Int.floor (x / p) : ℤ) : ℝ) * p) +ᵥ L = L := by
    simpa only [Tiling.AxisParallel.periodGroup_isAddSubgroup, zsmul_eq_mul] using
      (Tiling.AxisParallel.periodGroup L).zsmul_mem hperiod (-Int.floor (x / p))
  rw [← hper]
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simpa [periodRepresentative] using hx

private theorem periodDecode_mem {L : Set ℝ} {p : ℝ} (hperiod : p +ᵥ L = L)
    (u : ↥(L ∩ Ico 0 p) × ℤ) : periodDecode L p u ∈ L := by
  have hper : ((u.2 : ℝ) * p) +ᵥ L = L := by
    simpa only [Tiling.AxisParallel.periodGroup_isAddSubgroup, zsmul_eq_mul] using
      (Tiling.AxisParallel.periodGroup L).zsmul_mem hperiod u.2
  have hm : periodDecode L p u ∈ ((u.2 : ℝ) * p) +ᵥ L := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [periodDecode] using u.1.2.1
  simpa only [hper] using hm

private theorem periodDecode_injective {L : Set ℝ} {p : ℝ}
    (hp : 0 < p) (hperiod : p +ᵥ L = L) :
    Injective (fun u : ↥(L ∩ Ico 0 p) × ℤ =>
      (⟨periodDecode L p u, periodDecode_mem hperiod u⟩ : L)) := by
  intro u v huv
  have heq : periodDecode L p u = periodDecode L p v := congrArg Subtype.val huv
  have hu0 := u.1.2.2.1
  have hup := u.1.2.2.2
  have hv0 := v.1.2.2.1
  have hvp := v.1.2.2.2
  have hm : u.2 = v.2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hi : (u.2 : ℝ) + 1 ≤ (v.2 : ℝ) := by exact_mod_cast hlt
      have hip : ((u.2 : ℝ) + 1) * p ≤ (v.2 : ℝ) * p :=
        mul_le_mul_of_nonneg_right hi hp.le
      dsimp [periodDecode] at heq
      nlinarith
    · have hi : (v.2 : ℝ) + 1 ≤ (u.2 : ℝ) := by exact_mod_cast hgt
      have hip : ((v.2 : ℝ) + 1) * p ≤ (u.2 : ℝ) * p :=
        mul_le_mul_of_nonneg_right hi hp.le
      dsimp [periodDecode] at heq
      nlinarith
  apply Prod.ext
  · apply Subtype.ext
    dsimp [periodDecode] at heq
    rw [hm] at heq
    linarith
  · exact hm

private theorem periodDecode_surjective {L : Set ℝ} {p : ℝ}
    (hp : 0 < p) (hperiod : p +ᵥ L = L) :
    Surjective (fun u : ↥(L ∩ Ico 0 p) × ℤ =>
      (⟨periodDecode L p u, periodDecode_mem hperiod u⟩ : L)) := by
  intro x
  let f := periodRepresentative p x.1
  let q := Int.floor (x.1 / p)
  have hfL : f ∈ L := periodRepresentative_mem hp hperiod x.2
  have hfI : f ∈ Ico 0 p := periodRepresentative_mem_Ico hp x.1
  let u : ↥(L ∩ Ico 0 p) × ℤ := ⟨⟨f, hfL, hfI⟩, q⟩
  refine ⟨u, Subtype.ext ?_⟩
  dsimp [u, f, q, periodDecode, periodRepresentative]
  ring

private theorem exists_periodResidueEquiv {L : Set ℝ} {p : ℝ}
    (hp : 0 < p) (hperiod : p +ᵥ L = L) :
    ∃ e : ↥(L ∩ Ico 0 p) × ℤ ≃ L, ∀ u, (e u).1 = periodDecode L p u := by
  let f := fun u : ↥(L ∩ Ico 0 p) × ℤ =>
    (⟨periodDecode L p u, periodDecode_mem hperiod u⟩ : L)
  refine ⟨Equiv.ofBijective f ⟨periodDecode_injective hp hperiod,
    periodDecode_surjective hp hperiod⟩, ?_⟩
  intro u
  rfl

private theorem linePeriod_representatives_finite {B L : Set ℝ}
    (hTile : LineTiles B L) (hBfinite : volume B ≠ ⊤)
    (hBpositive : 0 < (volume B).toReal) {p : ℝ} (_hp : 0 < p) :
    (L ∩ Ico 0 p).Finite := by
  obtain ⟨_, _, _, _, hlocal, _⟩ :=
    Tiling.AxisParallel.Foundations.linePacking_uniformlySeparated hTile hBfinite hBpositive
  exact hlocal (Ico 0 p) (Metric.isBounded_Ico 0 p)

private theorem lineTiles_centres_nonempty_of_coverage {B L : Set ℝ}
    (hTile : LineTiles B L) : L.Nonempty := by
  obtain ⟨x, hx⟩ := hTile.2.2.2.2.exists
  have hx' := hx.mp (Set.mem_univ x)
  exact ⟨hx'.choose, hx'.choose.property⟩

private theorem linePeriod_representatives_nonempty {B L : Set ℝ}
    (hTile : LineTiles B L) {p : ℝ} (hp : 0 < p) (hperiod : p +ᵥ L = L) :
    (L ∩ Ico 0 p).Nonempty := by
  obtain ⟨x, hx⟩ := lineTiles_centres_nonempty_of_coverage hTile
  exact ⟨periodRepresentative p x,
    periodRepresentative_mem hp hperiod hx, periodRepresentative_mem_Ico hp x⟩

private theorem periodCells_pairwiseDisjoint (f : ℝ) {p : ℝ} (hp : 0 < p) :
    Pairwise (Disjoint on periodCell f p) := by
  intro m n hmn
  change Disjoint (periodCell f p m) (periodCell f p n)
  rw [Set.disjoint_left]
  intro x hxm hxn
  simp only [periodCell, mem_Ico] at hxm hxn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hi : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
    have hip : ((m : ℝ) + 1) * p ≤ (n : ℝ) * p :=
      mul_le_mul_of_nonneg_right hi hp.le
    linarith
  · have hi : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hgt
    have hip : ((n : ℝ) + 1) * p ≤ (m : ℝ) * p :=
      mul_le_mul_of_nonneg_right hi hp.le
    linarith

private theorem iUnion_periodCells (f : ℝ) {p : ℝ} (hp : 0 < p) :
    (⋃ m : ℤ, periodCell f p m) = univ := by
  apply eq_univ_iff_forall.mpr
  intro x
  let q := Int.floor ((x + f) / p)
  refine mem_iUnion.mpr ⟨-q, ?_⟩
  simp only [periodCell, mem_Ico]
  have hlo := Int.floor_le ((x + f) / p)
  have hhi := Int.lt_floor_add_one ((x + f) / p)
  have hlo' := (le_div_iff₀ hp).mp hlo
  have hhi' := (div_lt_iff₀ hp).mp hhi
  dsimp [q]
  push_cast
  constructor <;> linarith

private theorem translate_inter_cell (B : Set ℝ) (f p : ℝ) (m : ℤ) :
    (-(f + (m : ℝ) * p)) +ᵥ
      ((((f + (m : ℝ) * p) +ᵥ B) ∩ Ico 0 p)) =
        B ∩ periodCell f p m := by
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, mem_inter_iff, mem_Ico, periodCell,
    vadd_eq_add]
  constructor
  · rintro ⟨hxB, hx0, hxp⟩
    constructor
    · convert hxB using 1
      all_goals ring_nf
    · constructor <;> linarith
  · rintro ⟨hxB, hx0, hxp⟩
    constructor
    · convert hxB using 1
      all_goals ring_nf
    · constructor <;> linarith

private theorem lintegral_translate_indicator_cell {B : Set ℝ} (hBmeas : MeasurableSet B)
    {p : ℝ} (f : ℝ) (m : ℤ) :
    (∫⁻ x in Ico 0 p,
      ((f + (m : ℝ) * p) +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) x ∂volume) =
      volume (B ∩ periodCell f p m) := by
  have hA : MeasurableSet ((f + (m : ℝ) * p) +ᵥ B) := by
    have hm := hBmeas.preimage
      (show Measurable (fun x : ℝ => x - (f + (m : ℝ) * p)) from
        measurable_id.sub measurable_const)
    convert hm using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    ring_nf
  rw [MeasureTheory.lintegral_indicator_one hA]
  rw [Measure.restrict_apply hA]
  rw [← MeasureTheory.measure_vadd volume (-(f + (m : ℝ) * p))]
  rw [translate_inter_cell]

private theorem inter_periodCells_pairwiseDisjoint (B : Set ℝ) (f : ℝ) {p : ℝ}
    (hp : 0 < p) : Pairwise (Disjoint on fun m : ℤ => B ∩ periodCell f p m) := by
  intro m n hmn
  exact (periodCells_pairwiseDisjoint f hp hmn).mono inter_subset_right inter_subset_right

private theorem iUnion_inter_periodCells (B : Set ℝ) (f : ℝ) {p : ℝ} (hp : 0 < p) :
    (⋃ m : ℤ, B ∩ periodCell f p m) = B := by
  rw [← inter_iUnion]
  rw [iUnion_periodCells f hp, inter_univ]

private theorem sum_int_translates_setLIntegral_Ico {B : Set ℝ}
    (hBmeas : MeasurableSet B) {p : ℝ} (hp : 0 < p) (f : ℝ) :
    (∫⁻ x in Ico 0 p, ∑' m : ℤ,
      ((f + (m : ℝ) * p) +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) x ∂volume) = volume B := by
  rw [MeasureTheory.lintegral_tsum]
  · simp_rw [lintegral_translate_indicator_cell hBmeas]
    rw [← MeasureTheory.measure_iUnion (inter_periodCells_pairwiseDisjoint B f hp)]
    · rw [iUnion_inter_periodCells B f hp]
    · intro m
      exact hBmeas.inter measurableSet_Ico
  · intro m
    have hA : MeasurableSet ((f + (m : ℝ) * p) +ᵥ B) := by
      have hm := hBmeas.preimage
        (show Measurable (fun x : ℝ => x - (f + (m : ℝ) * p)) from
          measurable_id.sub measurable_const)
      convert hm using 1
      ext x
      simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
      ring_nf
    exact (measurable_const.indicator hA).aemeasurable.restrict

private theorem lineTiles_lintegralMultiplicity_ae {B L : Set ℝ} (hTile : LineTiles B L) :
    (fun x => ∑' l : L,
      (l.1 +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) x) =ᵐ[volume] 1 := by
  let _ : Countable L := hTile.2.2.1
  have hover : ∀ᵐ x ∂volume, ∀ l m : L, l ≠ m →
      ¬(x ∈ l.1 +ᵥ B ∧ x ∈ m.1 +ᵥ B) := by
    apply ae_all_iff.mpr
    intro l
    apply ae_all_iff.mpr
    intro m
    by_cases hlm : l = m
    · filter_upwards [] with x
      simp [hlm]
    · have hz : volume ((l.1 +ᵥ B) ∩ (m.1 +ᵥ B)) = 0 :=
        hTile.2.2.2.1 l.2 m.2 (fun h => hlm (Subtype.ext h))
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx
      intro _
      simpa only [mem_inter_iff, not_and] using hx
  filter_upwards [hTile.2.2.2.2, hover] with x hcover hdisj
  obtain ⟨l, hl⟩ := hcover.mp (mem_univ x)
  rw [tsum_eq_single l]
  · simp [hl]
  · intro m hml
    have hm : x ∉ m.1 +ᵥ B := fun hm => hdisj l m (Ne.symm hml) ⟨hl, hm⟩
    simp [hm]

/-- The integral of periodic translate multiplicity over one half-open period cell. -/
theorem periodicMultiplicity_cellIntegral
    {B L : Set ℝ} {p : ℝ}
    (hBmeas : MeasurableSet B) (hp : 0 < p)
    (hperiod : p +ᵥ L = L) (hfinite : (L ∩ Ico 0 p).Finite) :
    (∫⁻ x in Ico 0 p,
        ∑' l : L, (l.1 +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) x ∂volume) =
      (Set.ncard (L ∩ Ico 0 p) : ℝ≥0∞) * volume B := by
  let _ : Fintype ↥(L ∩ Ico 0 p) := hfinite.fintype
  obtain ⟨e, he⟩ := exists_periodResidueEquiv hp hperiod
  have hreindex (x : ℝ) :
      (∑' l : L, (l.1 +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) x) =
        ∑' u : ↥(L ∩ Ico 0 p) × ℤ,
          ((u.1.1 + (u.2 : ℝ) * p) +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) x := by
    rw [← e.tsum_eq]
    apply tsum_congr
    intro u
    rw [he u]
    rfl
  calc
    _ = ∫⁻ x in Ico 0 p, ∑' u : ↥(L ∩ Ico 0 p) × ℤ,
        ((u.1.1 + (u.2 : ℝ) * p) +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) x ∂volume :=
      setLIntegral_congr_fun measurableSet_Ico (fun x _ ↦ hreindex x)
    _ = ∫⁻ x in Ico 0 p, ∑' f : ↥(L ∩ Ico 0 p), ∑' m : ℤ,
        ((f.1 + (m : ℝ) * p) +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) x ∂volume := by
      congr 1
      funext x
      exact ENNReal.tsum_prod'
    _ = ∑' f : ↥(L ∩ Ico 0 p), ∫⁻ x in Ico 0 p, ∑' m : ℤ,
        ((f.1 + (m : ℝ) * p) +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) x ∂volume := by
      rw [MeasureTheory.lintegral_tsum]
      intro f
      apply AEMeasurable.restrict
      apply AEMeasurable.tsum
      intro m
      have hA : MeasurableSet ((f.1 + (m : ℝ) * p) +ᵥ B) := by
        have hm := hBmeas.preimage
          (show Measurable (fun x : ℝ ↦ x - (f.1 + (m : ℝ) * p)) from
            measurable_id.sub measurable_const)
        convert hm using 1
        ext x
        simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
        ring_nf
      exact (measurable_const.indicator hA).aemeasurable
    _ = ∑' _f : ↥(L ∩ Ico 0 p), volume B := by
      apply tsum_congr
      intro f
      exact sum_int_translates_setLIntegral_Ico hBmeas hp f.1
    _ = (Set.ncard (L ∩ Ico 0 p) : ℝ≥0∞) * volume B := by
      rw [tsum_fintype]
      simp

theorem _root_.Tiling.AxisParallel.Foundations.linePeriod_mass
    {B L : Set ℝ} (hBbounded : Bornology.IsBounded B)
    (hBpositive : 0 < (volume B).toReal) (hTile : LineTiles B L)
    {p : ℝ} (hp : 0 < p) (hperiod : p +ᵥ L = L) :
    (L ∩ Ico 0 p).Finite ∧ (L ∩ Ico 0 p).Nonempty ∧
      p = (volume B).toReal * Set.ncard (L ∩ Ico 0 p) := by
  have hBfinite : volume B ≠ ⊤ := hBbounded.measure_lt_top.ne
  have hF := linePeriod_representatives_finite hTile hBfinite hBpositive hp
  have hFne := linePeriod_representatives_nonempty hTile hp hperiod
  refine ⟨hF, hFne, ?_⟩
  let _ : Fintype ↥(L ∩ Ico 0 p) := hF.fintype
  have hmeasure := periodicMultiplicity_cellIntegral hTile.1 hp hperiod hF
  have hmeasure' :
      (∫⁻ x in Ico 0 p,
        ∑' l : L, (l.1 +ᵥ B).indicator (1 : ℝ → ℝ≥0∞) x ∂volume) =
        (Fintype.card ↥(L ∩ Ico 0 p) : ℕ) * volume B := by
    rw [Set.fintypeCard_eq_ncard]
    exact hmeasure
  have hone :
      (∫⁻ _x in Ico 0 p, (1 : ℝ≥0∞) ∂volume) = ENNReal.ofReal p := by
    simp [Real.volume_Ico]
  have hmassENN : ENNReal.ofReal p =
      (Fintype.card ↥(L ∩ Ico 0 p) : ℕ) * volume B := by
    rw [← hone, ← hmeasure']
    apply setLIntegral_congr_fun_ae measurableSet_Ico
    filter_upwards [lineTiles_lintegralMultiplicity_ae hTile] with x hx
    intro _
    exact hx.symm
  have hreal := congrArg ENNReal.toReal hmassENN
  rw [ENNReal.toReal_ofReal hp.le] at hreal
  rw [ENNReal.toReal_mul] at hreal
  simp at hreal
  simpa only [mul_comm] using hreal

end Tiling.AxisParallel.OneDimensional.FiniteInterval
