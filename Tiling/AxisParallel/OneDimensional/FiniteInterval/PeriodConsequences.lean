import Tiling.AxisParallel.OneDimensional.FiniteInterval.WholeLine
import Tiling.AxisParallel.OneDimensional.FiniteInterval.PeriodMass
import Tiling.AxisParallel.Topology.FellCore

/-!
# Common periods and Fell stabilization

Finitely many normalized tilings admit a common positive period, obtained
from the integer mass indices. Convergent normalized tilings eventually agree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Function MeasureTheory Set
open scoped Pointwise ENNReal Topology
noncomputable section
namespace Tiling.AxisParallel.OneDimensional.FiniteInterval

private noncomputable def periodIndex (L : Set ℝ) (p : ℝ) : ℕ :=
  Set.ncard (L ∩ Ico 0 p)

private theorem periodIndex_pos_mass {B : Set ℝ}
    (hBbounded : Bornology.IsBounded B) (hBpositive : 0 < (volume B).toReal)
    (N : NormalizedLineTiling B) {p : ℝ} (hp : 0 < p)
    (hperiod : p +ᵥ N.centres = N.centres) :
    0 < periodIndex N.centres p ∧
      p = (volume B).toReal * periodIndex N.centres p := by
  obtain ⟨hfinite, hnonempty, hmass⟩ :=
    Tiling.AxisParallel.Foundations.linePeriod_mass
      hBbounded hBpositive N.tiles hp hperiod
  exact ⟨(Set.ncard_pos hfinite).2 hnonempty, hmass⟩

private def commonIndex {ι : Type*} [Fintype ι] (n : ι → ℕ) : ℕ :=
  ∏ i, n i

private theorem commonIndex_pos {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) : 0 < commonIndex n := by
  exact Finset.prod_pos (fun i _ ↦ hn i)

private theorem dvd_commonIndex {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (i : ι) : n i ∣ commonIndex n := by
  exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)

private theorem nsmul_linePeriod {L : Set ℝ} {p : ℝ}
    (hperiod : p +ᵥ L = L) (k : ℕ) : ((k : ℝ) * p) +ᵥ L = L := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (((k + 1 : ℕ) : ℝ) * p) +ᵥ L =
            (((k : ℕ) : ℝ) * p + p) +ᵥ L := by
              congr 1
              push_cast
              ring
        _ = (((k : ℕ) : ℝ) * p) +ᵥ (p +ᵥ L) := by
              rw [← add_vadd]
        _ = (((k : ℕ) : ℝ) * p) +ᵥ L := by rw [hperiod]
        _ = L := ih

private theorem lineTiles_centres_nonempty {B L : Set ℝ}
    (hTile : LineTiles B L) : L.Nonempty := by
  have hcover : ∀ᵐ x ∂volume, ∃ l : L, x ∈ ((l : ℝ) +ᵥ B) := by
    filter_upwards [hTile.2.2.2.2] with x hx
    exact hx.mp (Set.mem_univ x)
  obtain ⟨x, l, hl⟩ := hcover.exists
  exact ⟨l, l.property⟩

theorem exists_commonLinePeriod_of_finite_normalized
    {B : Set ℝ} (hBbounded : Bornology.IsBounded B)
    (hBpositive : 0 < (volume B).toReal)
    (hfinite : Finite (NormalizedLineTiling B)) :
    ∃ P : ℝ, 0 < P ∧
      (∃ M : ℕ, 0 < M ∧ P = M * (volume B).toReal) ∧
      ∀ L : Set ℝ, LineTiles B L → P +ᵥ L = L := by
  classical
  let _ : Finite (NormalizedLineTiling B) := hfinite
  let _ : Fintype (NormalizedLineTiling B) := Fintype.ofFinite _
  have hexistsPeriod : ∀ N : NormalizedLineTiling B,
      ∃ p : ℝ, 0 < p ∧ p +ᵥ N.centres = N.centres := fun N ↦
    exists_positiveLinePeriod_of_finite_normalized hBbounded N.tiles hfinite
  choose p hp hperiod using hexistsPeriod
  let n : NormalizedLineTiling B → ℕ := fun N ↦ periodIndex N.centres (p N)
  have hn : ∀ N, 0 < n N := fun N ↦
    (periodIndex_pos_mass hBbounded hBpositive N (hp N) (hperiod N)).1
  have hmass : ∀ N, p N = (volume B).toReal * n N := fun N ↦
    (periodIndex_pos_mass hBbounded hBpositive N (hp N) (hperiod N)).2
  let M : ℕ := commonIndex n
  have hM : 0 < M := commonIndex_pos n hn
  let P : ℝ := M * (volume B).toReal
  have hP : 0 < P := mul_pos (Nat.cast_pos.2 hM) hBpositive
  refine ⟨P, hP, ⟨M, hM, rfl⟩, ?_⟩
  intro L hTile
  obtain ⟨l₀, hl₀⟩ := lineTiles_centres_nonempty hTile
  obtain ⟨N, hNcentres, hNperiod⟩ :=
    Tiling.AxisParallel.Foundations.normalizeLineTiling_spec hTile hl₀
  obtain ⟨k, hk⟩ := dvd_commonIndex n N
  have hP_eq : P = (k : ℝ) * p N := by
    dsimp [P, M]
    rw [hk, hmass N]
    push_cast
    ring
  apply (hNperiod P).mp
  rw [hP_eq]
  exact nsmul_linePeriod (hperiod N) k

theorem exists_commonLinePeriod
    {B : Set ℝ} (hB : IsFiniteIntervalRegion B)
    (hBpositive : 0 < (volume B).toReal) :
    ∃ P : ℝ, 0 < P ∧
      (∃ M : ℕ, 0 < M ∧ P = M * (volume B).toReal) ∧
      ∀ L : Set ℝ, LineTiles B L → P +ᵥ L = L := by
  let presentation := IntervalPresentation.ofIsFiniteIntervalRegion hB
  exact exists_commonLinePeriod_of_finite_normalized
    presentation.isBounded hBpositive
    (finite_normalizedLineTilings hB hBpositive)

private theorem fellCompactification_injective {A L : Set ℝ}
    (hA : IsClosed A) (hL : IsClosed L)
    (heq : Tiling.AxisParallel.Topology.fellCompactification A hA =
      Tiling.AxisParallel.Topology.fellCompactification L hL) : A = L := by
  ext x
  have hx := congrArg
    (fun K : TopologicalSpace.NonemptyCompacts (OnePoint ℝ) ↦
      (x : OnePoint ℝ) ∈ (K : Set (OnePoint ℝ))) heq
  simpa [Tiling.AxisParallel.Topology.fellCompactification,
    Tiling.Topology.fellCompactification] using hx

private theorem fellCompactification_congr {A L : Set ℝ}
    (hA : IsClosed A) (hL : IsClosed L) (h : A = L) :
    Tiling.AxisParallel.Topology.fellCompactification A hA =
      Tiling.AxisParallel.Topology.fellCompactification L hL := by
  subst L
  rfl

private theorem locallyFellConverges_const_iff {A L : Set ℝ}
    (hA : IsClosed A) (hL : IsClosed L) :
    Tiling.AxisParallel.Topology.LocallyFellConverges
      (fun _ : ℕ ↦ A) L ↔ A = L := by
  constructor
  · rintro ⟨hseq, hL', hlim⟩
    have heq : Tiling.AxisParallel.Topology.fellCompactification A hA =
        Tiling.AxisParallel.Topology.fellCompactification L hL := by
      have hlim' : Tendsto
          (fun _ : ℕ ↦ Tiling.AxisParallel.Topology.fellCompactification A hA)
          atTop
          (nhds (Tiling.AxisParallel.Topology.fellCompactification L hL)) := by
        exact hlim
      exact tendsto_nhds_unique (l := atTop) tendsto_const_nhds hlim'
    exact fellCompactification_injective hA hL heq
  · intro h
    subst L
    exact ⟨fun _ ↦ hA, hA, tendsto_const_nhds⟩

theorem normalizedLineTilings_eventuallyEq_of_finite {B : Set ℝ}
    (hfinite : Finite (NormalizedLineTiling B))
    (N : ℕ → NormalizedLineTiling B) (L : Set ℝ) (hclosed : IsClosed L)
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (NormalizedLineTiling.centres ∘ N) L) :
    LineTiles B L ∧ 0 ∈ L ∧
      ∃ n0 : ℕ, ∀ n, n0 ≤ n → (N n).centres = L := by
  classical
  let _ : Finite (NormalizedLineTiling B) := hfinite
  let _ : Fintype (NormalizedLineTiling B) := Fintype.ofFinite _
  obtain ⟨hseqClosed, hLclosed, hlim⟩ := hconv
  have hAvoid : ∀ M : NormalizedLineTiling B, M.centres ≠ L →
      ∀ᶠ n in atTop, N n ≠ M := by
    intro M hML
    by_contra hnot
    have hfreq : ∃ᶠ n in atTop, N n = M := by
      simpa using (Filter.not_eventually.mp hnot)
    obtain ⟨φ, hφmono, hφ⟩ := extraction_of_frequently_atTop hfreq
    have hMclosed : IsClosed M.centres := by
      simpa [Function.comp_apply, hφ 0] using hseqClosed (φ 0)
    have hsub := hlim.comp hφmono.tendsto_atTop
    have hconstConv : Tiling.AxisParallel.Topology.LocallyFellConverges
        (fun _ : ℕ ↦ M.centres) L := by
      refine ⟨fun _ ↦ hMclosed, hclosed, ?_⟩
      convert hsub using 1
      funext i
      exact fellCompactification_congr hMclosed (hseqClosed (φ i))
        (congrArg NormalizedLineTiling.centres (hφ i)).symm
    exact hML ((locallyFellConverges_const_iff hMclosed hclosed).mp hconstConv)
  let U : Set (NormalizedLineTiling B) := Set.univ
  have hAll : ∀ᶠ n in atTop, ∀ M ∈ U, M.centres ≠ L → N n ≠ M := by
    apply (Filter.eventually_all_finite (Set.toFinite U)).2
    intro M hMU
    by_cases hML : M.centres = L
    · filter_upwards [] with n
      exact fun hneq ↦ (hneq hML).elim
    · exact (hAvoid M hML).mono (fun n hn _ ↦ hn)
  have hEventually : ∀ᶠ n in atTop, (N n).centres = L := by
    filter_upwards [hAll] with n hn
    by_contra hneq
    exact hn (N n) (Set.mem_univ _) hneq rfl
  obtain ⟨n, hn⟩ := hEventually.exists
  have hTile : LineTiles B L := by
    rw [← hn]
    exact (N n).tiles
  have hzero : 0 ∈ L := by
    rw [← hn]
    exact (N n).zero_mem
  exact ⟨hTile, hzero, Filter.eventually_atTop.1 hEventually⟩

theorem normalizedLineTilings_eventuallyEq
    {B : Set ℝ} (hB : IsFiniteIntervalRegion B)
    (hBpositive : 0 < (volume B).toReal)
    (N : ℕ → NormalizedLineTiling B) (L : Set ℝ) (hclosed : IsClosed L)
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (NormalizedLineTiling.centres ∘ N) L) :
    LineTiles B L ∧ 0 ∈ L ∧
      ∃ n0 : ℕ, ∀ n, n0 ≤ n → (N n).centres = L := by
  exact normalizedLineTilings_eventuallyEq_of_finite
    (finite_normalizedLineTilings hB hBpositive) N L hclosed hconv

end Tiling.AxisParallel.OneDimensional.FiniteInterval
