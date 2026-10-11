import Tiling.AxisParallel.Approximation.FiniteLocalComplexityControl
import Tiling.AxisParallel.Approximation.ControlledPeriodLifting
import Tiling.AxisParallel.Approximation.PeriodicBandDeformation
import Tiling.AxisParallel.Approximation.FLCIncidenceGermsAndColumns
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.Approximation.GoodApproximationPreservesTilings
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.OneDimensional.FiniteInterval.IntervalGeometry
import Tiling.AxisParallel.Foundations.GenericSlices
import Tiling.AxisParallel.Terminal.NoGapSliceGeometry
import Tiling.AxisParallel.Terminal.BoundaryReconstruction
import Tiling.AxisParallel.Foundations.FilledSliceChains
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.OneDimensional.ColumnSlices
import Tiling.AxisParallel.OneDimensional.FiniteInterval.TargetGeometry
import Tiling.AxisParallel.OneDimensional.FiniteInterval.WholeLine
import Tiling.AxisParallel.Approximation.Core
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true

open Bornology Function MeasureTheory Set
open scoped Pointwise Topology
noncomputable section

namespace Tiling.AxisParallel.Terminal

/-!
# Vertical packings with column

This implemented prefix contains the fourteen dependency-closed private numeric
and finite-control targets used by the later T07 construction.
-/

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Foundations
open Tiling.AxisParallel.Foundations.GenericSlices
open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.FiniteInterval

private def traceEndpoints (A Y : Set ℝ) : Set ℝ :=
  frontier (interior (closure (A + Y)))

private structure GenuineGenericSection (C : ApproximationContext.{0}) (axis : Axis) where
  transverse : ℝ
  generic : transverse ∉
    (IntrinsicVertices.intrinsicCoordinateLevels C.region axis.swap : Set ℝ)
  rawCarrier : Set ℝ
  rawCarrier_eq : rawCarrier =
    {x : ℝ | FilledSliceChains.slicePoint axis transverse x ∈ C.region.openCarrier}
  presentation : OneDimensional.FiniteInterval.IntervalPresentation rawCarrier
  nonempty : rawCarrier.Nonempty
  leftVertex : Fin presentation.n → ↥C.region.vertices
  rightVertex : Fin presentation.n → ↥C.region.vertices
  leftVertex_coord : ∀ i, axis.coord (leftVertex i).1 = presentation.left i
  rightVertex_coord : ∀ i, axis.coord (rightVertex i).1 = presentation.right i

private structure NormalizedGenericSection (C : ApproximationContext.{0})
    (axis : Axis) where
  raw : GenuineGenericSection C axis
  originInterval : Fin raw.presentation.n
  originVertex : ↥C.region.vertices
  originVertex_eq : originVertex = raw.leftVertex originInterval
  origin : ℝ
  origin_eq : origin = axis.coord originVertex.1
  originScalar : C.coordinateSpace
  originScalar_coe : (originScalar : ℝ) = origin
  carrier : Set ℝ
  carrier_eq : carrier = (-origin) +ᵥ raw.rawCarrier
  normalized : sInf (closure carrier) = 0
  mass : ℝ
  mass_eq : mass = volume.real carrier
  mass_pos : 0 < mass
  massScalar : C.coordinateSpace
  massScalar_coe : (massScalar : ℝ) = mass

private structure ControlledDifference (C : ApproximationContext.{0}) (R : ℝ) where
  axis : Axis
  left : ↥C.translatedVertices
  right : ↥C.translatedVertices
  close : dist (right : Tiling.Plane) left < R
  scalar : C.coordinateSpace
  scalar_eq : scalar = C.translatedDifferenceScalar axis right left

private structure FiniteCombinationData (C : ApproximationContext.{0}) (R : ℝ) where
  numberOfTerms : ℕ
  term : Fin numberOfTerms → ControlledDifference C R
  coefficient : Fin numberOfTerms → ℤ
  value : C.coordinateSpace
  value_eq : value = Finset.univ.sum fun i =>
    (coefficient i : ℚ) • (term i).scalar
  weight : ℕ
  weight_eq : weight = Finset.univ.sum fun i => (coefficient i).natAbs

private def FiniteCombinationData.mappedValue
    {C : ApproximationContext.{0}} {R : ℝ}
    (E : FiniteCombinationData C R)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) : ℝ :=
  Finset.univ.sum fun i =>
    (E.coefficient i : ℝ) * mapScalar phi (E.term i).scalar

private structure BoundedTraceComponentCode (C : ApproximationContext.{0}) (axis : Axis)
    (S : Set Tiling.Plane) (A : Set ℝ) (a b : ℝ) where
  ordered : a < b
  left : ↥C.translatedVertices
  right : ↥C.translatedVertices
  left_center_mem : ∃ t ∈ S, ∃ v ∈ C.region.vertices, left.1 = v + t
  right_center_mem : ∃ t ∈ S, ∃ v ∈ C.region.vertices, right.1 = v + t
  left_value : axis.coord left.1 = a
  right_value : axis.coord right.1 = b
  left_endpoint : a ∈ traceEndpoints A (axis.coord '' S)
  right_endpoint : b ∈ traceEndpoints A (axis.coord '' S)
  lengthScalar : C.coordinateSpace
  lengthScalar_formula : lengthScalar = C.translatedDifferenceScalar axis right left
  lengthScalar_eq : (lengthScalar : ℝ) = b - a

private theorem extremalTrace_displacement_propagates
    {D₀ D₁ : Set Tiling.Plane}
    {theta : properVertices D₀ ≃ properVertices D₁}
    {beta : Tiling.Plane} {E₀ : Set (properVertices D₀)}
    (_hE : E₀.Nonempty)
    (step : properVertices D₀ → properVertices D₀ → Prop)
    (hconn : ∀ e ∈ E₀, ∀ e' ∈ E₀, Relation.ReflTransGen step e e')
    (hstep : ∀ u v, step u v → theta u - u.1 = beta → theta v - v.1 = beta)
    (hseed : ∃ e ∈ E₀, theta e - e.1 = beta) :
    ∀ e ∈ E₀, theta e - e.1 = beta := by
  obtain ⟨e₀, he₀, he₀beta⟩ := hseed
  intro e he
  have hpath : ∀ {a b : properVertices D₀},
      Relation.ReflTransGen step a b →
        theta a - a.1 = beta → theta b - b.1 = beta := by
    intro a b hab ha
    induction hab with
    | refl => exact ha
    | tail hxy hyz ih => exact hstep _ _ hyz ih
  exact hpath (hconn e₀ he₀ e he) he₀beta

private theorem boundedTraceLength_reflects
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (hphi : IsEpsilonApproximation C P.threshold phi)
    {x y x' y' : C.coordinateSpace}
    (_hxy : x < y) (_hxy' : x' < y')
    (heq : mapScalar phi (y - x) = mapScalar phi (y' - x'))
    (hmem : y - x ∈ P.scalarAlphabet)
    (hmem' : y' - x' ∈ P.scalarAlphabet) :
    (y - x : ℝ) = (y' - x' : ℝ) := by
  have hz := (P.scalar_injective phi hphi (y - x)
    (Finset.mem_union_left _ hmem) (y' - x')
    (Finset.mem_union_left _ hmem')).mp heq
  exact congrArg (fun z : C.coordinateSpace => (z : ℝ)) hz

private theorem finiteCombination_mapped_error
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    {R : ℝ} (hR : R < P.controlRadius)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (E : FiniteCombinationData C R) :
    |E.mappedValue phi - (E.value : ℝ)| ≤
      (E.weight : ℝ) / P.scale := by
  have hterm : ∀ i : Fin E.numberOfTerms,
      |mapScalar phi (E.term i).scalar - ((E.term i).scalar : ℝ)| <
        P.coordinateError := by
    intro i
    have hdist := (E.term i).close
    have hscalar : (E.term i).scalar ∈ P.scalarAlphabet := by
      change (E.term i).scalar ∈ (P.scalarAlphabet : Set C.coordinateSpace)
      rw [P.scalarAlphabet_exact]
      rw [E.term i |>.scalar_eq]
      exact ⟨(E.term i).axis, (E.term i).right, (E.term i).left,
        lt_trans (E.term i).close hR, by cases (E.term i).axis <;> rfl⟩
    exact (P.scalar_close phi hphi _ (Finset.mem_union_left _ hscalar))
  have hvalue : E.mappedValue phi - (E.value : ℝ) =
      ∑ i : Fin E.numberOfTerms, (E.coefficient i : ℝ) *
        (mapScalar phi (E.term i).scalar - ((E.term i).scalar : ℝ)) := by
    rw [FiniteCombinationData.mappedValue, E.value_eq]
    simp only [mapScalar, Submodule.coe_sum, Submodule.coe_smul_of_tower,
      Rat.smul_def]
    simp_rw [mul_sub]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    norm_num
  rw [hvalue]
  calc
    _ ≤ ∑ i : Fin E.numberOfTerms,
        |(E.coefficient i : ℝ)| *
          |mapScalar phi (E.term i).scalar - ((E.term i).scalar : ℝ)| :=
      by simpa only [abs_mul] using
        (Finset.abs_sum_le_sum_abs
          (s := (Finset.univ : Finset (Fin E.numberOfTerms)))
          (f := fun i => (E.coefficient i : ℝ) *
            (mapScalar phi (E.term i).scalar - ((E.term i).scalar : ℝ))))
    _ ≤ ∑ i : Fin E.numberOfTerms,
        |(E.coefficient i : ℝ)| * P.coordinateError := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (le_of_lt (hterm i)) (abs_nonneg _)
    _ = (E.weight : ℝ) * P.coordinateError := by
      rw [E.weight_eq]
      simp only [Nat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have habs : |(E.coefficient i : ℝ)| =
          ((E.coefficient i).natAbs : ℝ) := by
        rw [← Int.cast_abs]
        have hz := congrArg (fun q : ℤ => (q : ℝ))
          (Int.natCast_natAbs (E.coefficient i)).symm
        exact hz
      rw [habs]
    _ ≤ (E.weight : ℝ) / P.scale := by
      have hsqrt : 1 < Real.sqrt 2 := by
        have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith [Real.sqrt_nonneg 2]
      have he : P.coordinateError ≤ P.scale⁻¹ := by
        have hc := P.coordinateError_small
        rw [P.localError_eq] at hc
        have hmul := mul_lt_mul_of_pos_right hsqrt P.coordinateError_pos
        linarith
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)

private theorem finiteCorrections_uniformBounds
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) {R : ℝ}
    (massExpression : FiniteCombinationData C R)
    (corrections : Finset (FiniteCombinationData C R)) :
    ∃ W : ℕ, massExpression.weight ≤ W ∧ ∃ B > 0,
      A.mass < B ∧
      ∀ E ∈ corrections, E.weight ≤ W ∧ |(E.value : ℝ)| < B / 2 := by
  let W := massExpression.weight + corrections.sum (fun E => E.weight)
  let B := A.mass + 1 + 2 * corrections.sum (fun E => |(E.value : ℝ)|)
  have hsumv : 0 ≤ corrections.sum (fun E => |(E.value : ℝ)|) := by
    exact Finset.sum_nonneg (fun E hE => abs_nonneg _)
  have hsumw : ∀ E ∈ corrections, E.weight ≤ corrections.sum (fun F => F.weight) := by
    intro E hE
    exact Finset.single_le_sum (fun F _ => Nat.zero_le _) hE
  refine ⟨W, Nat.le_add_right _ _, B, ?_, ?_, ?_⟩
  · dsimp [B]
    nlinarith [A.mass_pos, hsumv]
  · dsimp [B]
    nlinarith [A.mass_pos, hsumv]
  · dsimp [W, B]
    intro E hE
    constructor
    · exact Nat.le_add_left_of_le (hsumw E hE)
    · have hsum : |(E.value : ℝ)| ≤ corrections.sum (fun F => |(F.value : ℝ)|) := by
        exact Finset.single_le_sum (s := corrections)
          (f := fun F => |(F.value : ℝ)|)
          (fun F _ => abs_nonneg _) hE
      have hmass : 0 < A.mass := A.mass_pos
      nlinarith

private theorem natAbs_lt_mem_Icc {q : ℤ} {K : ℕ} (hq : q.natAbs < K) :
    q ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
  by_cases hq0 : 0 ≤ q
  · have hqn : (q.natAbs : ℤ) = q := Int.natAbs_of_nonneg hq0
    simp only [Finset.mem_Icc]
    omega
  · have hqn : (q.natAbs : ℤ) = -q := by
      have hqn' : ((-q).natAbs : ℤ) = -q :=
        Int.natAbs_of_nonneg (by omega)
      simpa only [Int.natAbs_neg] using hqn'
    simp only [Finset.mem_Icc]
    omega

private theorem finiteBulkCorrection_zeroSeparation
    {C : ApproximationContext.{0}} {R : ℝ} (h : C.coordinateSpace)
    (corrections : Finset (FiniteCombinationData C R)) (K : ℕ) :
    ∃ mu > 0, ∀ (q : ℤ) (c c' : FiniteCombinationData C R),
      q.natAbs < K → c ∈ corrections → c' ∈ corrections →
      (q : ℝ) * (h : ℝ) + c.value - c'.value ≠ 0 →
      mu ≤ |(q : ℝ) * (h : ℝ) + c.value - c'.value| := by
  let Q : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let triples := Q.product (corrections.product corrections)
  let value : ℤ → FiniteCombinationData C R →
      FiniteCombinationData C R → ℝ := fun q c c' =>
    (q : ℝ) * (h : ℝ) + c.value - c'.value
  let values : Finset ℝ := triples.image (fun t =>
    |value t.1 t.2.1 t.2.2|)
  let positive : Finset ℝ := values.filter (fun x => 0 < x)
  by_cases hp : positive.Nonempty
  · let mu := positive.min' hp
    have hmu : 0 < mu := by
      have hm := positive.min'_mem hp
      rw [Finset.mem_filter] at hm
      exact hm.2
    refine ⟨mu, hmu, ?_⟩
    intro q c c' hq hc hc' hne
    have hqQ : q ∈ Q := by exact natAbs_lt_mem_Icc hq
    have ht : (q, (c, c')) ∈ triples := by
      exact Finset.mem_product.mpr ⟨hqQ,
        Finset.mem_product.mpr ⟨hc, hc'⟩⟩
    have hv : |value q c c'| ∈ values := by
      exact Finset.mem_image.mpr ⟨(q, (c, c')), ht, rfl⟩
    have hvpos : |value q c c'| ∈ positive := by
      rw [Finset.mem_filter]
      exact ⟨hv, abs_pos.mpr hne⟩
    exact positive.min'_le _ hvpos
  · refine ⟨1, by norm_num, ?_⟩
    intro q c c' hq hc hc' hne
    have hqQ : q ∈ Q := natAbs_lt_mem_Icc hq
    have ht : (q, (c, c')) ∈ triples :=
      Finset.mem_product.mpr ⟨hqQ, Finset.mem_product.mpr ⟨hc, hc'⟩⟩
    have hv : |value q c c'| ∈ values :=
      Finset.mem_image.mpr ⟨(q, (c, c')), ht, rfl⟩
    have hvpos : |value q c c'| ∈ positive := by
      rw [Finset.mem_filter]
      exact ⟨hv, abs_pos.mpr hne⟩
    exact (hp ⟨_, hvpos⟩).elim

private theorem region_support_diam_pos (K : Region) :
    0 < Metric.diam K.support := by
  have hopen : 0 < Metric.diam K.openCarrier :=
    region_openCarrier_diam_pos K
  have heq : Metric.diam K.support = Metric.diam K.openCarrier := by
    change Metric.diam K.support = Metric.diam (interior K.support)
    nth_rewrite 1 [← K.isPolygonal.closure_interior]
    exact Metric.diam_closure _
  rw [heq]
  exact hopen

private theorem localError_lt_diam_of_two_div_lt_scale
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (sourceDiameter : ℝ) (hpos : 0 < sourceDiameter)
    (hscale : 2 / sourceDiameter < P.scale) :
    P.localError < sourceDiameter := by
  have htwo : 0 < 2 / sourceDiameter := div_pos (by norm_num) hpos
  have hinv : P.scale⁻¹ < (2 / sourceDiameter)⁻¹ :=
    (inv_lt_inv₀ P.scale_pos htwo).2 hscale
  calc
    P.localError = P.scale⁻¹ := P.localError_eq
    _ < (2 / sourceDiameter)⁻¹ := hinv
    _ = sourceDiameter / 2 := by field_simp
    _ < sourceDiameter := by linarith

private noncomputable def longComponentRecoveryScale
    (C : ApproximationContext) (R : ℝ) (W K N : ℕ)
    (B mu h G delta traceRadius : ℝ) : ℝ :=
  let d := Metric.diam C.region.support
  let nW : ℝ := ((K : ℝ) + 2) * (W : ℝ)
  |R| + 1 + (N : ℝ) * G + 2 * d + 2 / delta + d + 2 / d +
    2 * G + 2 * traceRadius + 4 + 2 * nW / h + 2 * nW / B + nW / mu

private theorem longComponentRecoveryScale_exists :
  ∀ (C : ApproximationContext)
    (R : ℝ) (W K N : ℕ) (B mu h G delta traceRadius : ℝ),
    0 < B → 0 < h → 0 < mu → 0 < delta → 0 < G → 0 < traceRadius →
    ∃ recoveryScale > 0, ∀ P : FLCControlPackage C,
      recoveryScale < P.scale →
      R < P.controlRadius ∧
      (N : ℝ) * G + 2 * Metric.diam C.region.support < P.scale ∧
      P.localError < delta / 2 ∧
      Metric.diam C.region.support < P.scale ∧
      P.localError ≤ Metric.diam C.region.support ∧
      Metric.diam C.region.support < P.controlRadius ∧
      G + P.localError < P.scale / 2 ∧
      traceRadius + 2 * P.localError < P.scale / 2 ∧
      ((K : ℝ) + 2) * (W : ℝ) / P.scale <
        min (h / 2) (min (B / 2) mu) := by
  intro C R W K N B mu h G delta traceRadius hB hh hmu hdelta hG htrace
  have hd : 0 < Metric.diam C.region.support :=
    region_support_diam_pos C.region
  let d : ℝ := Metric.diam C.region.support
  let nW : ℝ := ((K : ℝ) + 2) * (W : ℝ)
  let recoveryScale : ℝ :=
    |R| + 1 + (N : ℝ) * G + 2 * d + 2 / delta + d + 2 / d +
      2 * G + 2 * traceRadius + 4 + 2 * nW / h + 2 * nW / B + nW / mu
  have hR : R ≤ |R| := le_abs_self R
  have habsR : 0 ≤ |R| := abs_nonneg R
  have hnW : 0 ≤ nW := by positivity
  have hNG : 0 ≤ (N : ℝ) * G := by positivity
  have h2d : 0 ≤ 2 * d := by positivity
  have h2delta : 0 ≤ 2 / delta := by positivity
  have h2dinv : 0 ≤ 2 / d := by positivity
  have h2G : 0 ≤ 2 * G := by positivity
  have h2trace : 0 ≤ 2 * traceRadius := by positivity
  have hnWh0 : 0 ≤ 2 * nW / h := by positivity
  have hnWB0 : 0 ≤ 2 * nW / B := by positivity
  have hnWmu0 : 0 ≤ nW / mu := by positivity
  have hrecpos : 0 < recoveryScale := by
    dsimp [recoveryScale, d, nW]
    positivity
  refine ⟨recoveryScale, hrecpos, ?_⟩
  intro P hscale
  have hscale_control : P.scale < P.controlRadius := P.scale_lt_controlRadius
  have hRscale : R < P.scale := by
    have : R < recoveryScale := by
      dsimp [recoveryScale]
      linarith [hB, hd, hdelta, hG, htrace, hmu, hh]
    exact this.trans hscale
  have hDscale : d < P.scale := by
    have : d < recoveryScale := by
      dsimp [recoveryScale]
      linarith [hB, hd, hdelta, hG, htrace, hmu, hh]
    exact this.trans hscale
  have hNscale : (N : ℝ) * G + 2 * d < P.scale := by
    have : (N : ℝ) * G + 2 * d < recoveryScale := by
      dsimp [recoveryScale]
      linarith [hB, hd, hdelta, hG, htrace, hmu, hh]
    exact this.trans hscale
  have hone : (1 : ℝ) < P.scale := by
    have : (1 : ℝ) < recoveryScale := by
      dsimp [recoveryScale]
      linarith [hB, hd, hdelta, hG, htrace, hmu, hh]
    exact this.trans hscale
  have hlocal_one : P.localError < 1 := by
    rw [P.localError_eq]
    exact (inv_lt_one₀ P.scale_pos).2 hone
  have hlocal_delta : P.localError < delta / 2 := by
    have htwo : 0 < 2 / delta := div_pos (by norm_num) hdelta
    have hdeltaScale : 2 / delta < P.scale := by
      have : 2 / delta < recoveryScale := by
        dsimp [recoveryScale]
        linarith [hB, hd, hdelta, hG, htrace, hmu, hh]
      exact this.trans hscale
    have hi : P.scale⁻¹ < (2 / delta)⁻¹ :=
      (inv_lt_inv₀ P.scale_pos htwo).2 hdeltaScale
    calc
      P.localError = P.scale⁻¹ := P.localError_eq
      _ < (2 / delta)⁻¹ := hi
      _ = delta / 2 := by field_simp
  have hlocal_d : P.localError ≤ d := by
    have hrecip : 2 / d < P.scale := by
      have : 2 / d < recoveryScale := by
        dsimp [recoveryScale]
        linarith [hB, hd, hdelta, hG, htrace, hmu, hh]
      exact this.trans hscale
    have hi : P.scale⁻¹ < (2 / d)⁻¹ :=
      (inv_lt_inv₀ P.scale_pos (div_pos (by norm_num) hd)).2 hrecip
    rw [P.localError_eq]
    exact (calc
      P.scale⁻¹ < (2 / d)⁻¹ := hi
      _ = d / 2 := by field_simp
      _ ≤ d := by linarith).le
  have hGscale : 2 * G + 2 < P.scale := by
    have : 2 * G + 2 < recoveryScale := by
      dsimp [recoveryScale]
      linarith [hB, hd, hdelta, hG, htrace, hmu, hh]
    exact this.trans hscale
  have hGsmall : G + P.localError < P.scale / 2 := by
    linarith [hGscale, hlocal_one]
  have htracescale : 2 * traceRadius + 4 < P.scale := by
    have : 2 * traceRadius + 4 < recoveryScale := by
      dsimp [recoveryScale]
      linarith [hB, hd, hdelta, hG, htrace, hmu, hh]
    exact this.trans hscale
  have htracesmall : traceRadius + 2 * P.localError < P.scale / 2 := by
    linarith [htracescale, hlocal_one]
  have hnWh : 2 * nW / h < P.scale := by
    have : 2 * nW / h < recoveryScale := by
      dsimp [recoveryScale]
      linarith [hB, hd, hdelta, hG, htrace, hmu, hh]
    exact this.trans hscale
  have hnWB : 2 * nW / B < P.scale := by
    have : 2 * nW / B < recoveryScale := by
      dsimp [recoveryScale]
      linarith [hB, hd, hdelta, hG, htrace, hmu, hh]
    exact this.trans hscale
  have hnWmu : nW / mu < P.scale := by
    have : nW / mu < recoveryScale := by
      dsimp [recoveryScale]
      linarith [hB, hd, hdelta, hG, htrace, hmu, hh]
    exact this.trans hscale
  have hnh : nW / P.scale < h / 2 := by
    apply (div_lt_iff₀ P.scale_pos).2
    have hx : 2 * nW < P.scale * h := (div_lt_iff₀ hh).mp hnWh
    nlinarith
  have hnB : nW / P.scale < B / 2 := by
    apply (div_lt_iff₀ P.scale_pos).2
    have hx : 2 * nW < P.scale * B := (div_lt_iff₀ hB).mp hnWB
    nlinarith
  have hnmu : nW / P.scale < mu := by
    apply (div_lt_iff₀ P.scale_pos).2
    have hx : nW < P.scale * mu := (div_lt_iff₀ hmu).mp hnWmu
    simpa [mul_comm] using hx
  have hdiam_control : d < P.controlRadius := hDscale.trans hscale_control
  change Metric.diam C.region.support < P.scale at hDscale
  change Metric.diam C.region.support < P.controlRadius at hdiam_control
  exact ⟨hRscale.trans hscale_control, hNscale, hlocal_delta, hDscale,
    hlocal_d, hdiam_control, hGsmall, htracesmall, by
      rw [lt_min_iff, lt_min_iff]
      simpa [nW] using (show nW / P.scale < min (h / 2) (min (B / 2) mu) by
        rw [lt_min_iff, lt_min_iff]
        exact ⟨hnh, hnB, hnmu⟩)⟩

private theorem boundedTraceCode_mem_scalarAlphabet :
    ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      {axis : Axis} {S : Set Tiling.Plane} {A : Set ℝ} {a b : ℝ}
      (code : BoundedTraceComponentCode C axis S A a b),
      (∃ c : ℝ, ∀ s ∈ S, axis.transverseCoord s = c) →
      b - a + Metric.diam C.region.support < P.controlRadius →
        code.lengthScalar ∈ P.scalarAlphabet := by
  intro C P axis S A a b code halign hcontrol
  have hvSupport : ∀ v : ↥C.region.vertices,
      (v : Tiling.Plane) ∈ C.region.support := by
    intro v
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier C.region v.2)
  obtain ⟨tL, htL, vL, hvL, hL⟩ := code.left_center_mem
  obtain ⟨tR, htR, vR, hvR, hR⟩ := code.right_center_mem
  obtain ⟨c, hc⟩ := halign
  have hdistV : dist (vL : Tiling.Plane) vR ≤
      Metric.diam C.region.support :=
    Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded
      (hvSupport ⟨vL, hvL⟩) (hvSupport ⟨vR, hvR⟩)
  have hdist : dist code.right.1 code.left.1 < P.controlRadius := by
    have hnorm := Complex.norm_le_abs_re_add_abs_im
      (code.right.1 - code.left.1)
    rw [Complex.dist_eq]
    cases axis with
    | horizontal =>
        have halong : (code.right.1 - code.left.1).re = b - a := by
          have hRre : code.right.1.re = b := by
            simpa [Axis.coord] using code.right_value
          have hLre : code.left.1.re = a := by
            simpa [Axis.coord] using code.left_value
          simp [Complex.sub_re, hRre, hLre]
        have htransV : (code.right.1 - code.left.1).im = (vR - vL).im := by
          rw [show code.right.1 = vR + tR from hR,
            show code.left.1 = vL + tL from hL]
          simp only [Complex.sub_im, Complex.add_im]
          have hLc := hc tL htL
          have hRc := hc tR htR
          simp only [Axis.transverseCoord] at hLc hRc
          linarith
        have hV : |(code.right.1 - code.left.1).im| ≤
            Metric.diam C.region.support := by
          rw [htransV]
          have hdistV' : ‖vR - vL‖ ≤ Metric.diam C.region.support := by
            simpa [Complex.dist_eq, norm_sub_rev] using hdistV
          exact (Complex.abs_im_le_norm _).trans hdistV'
        have hab : 0 ≤ b - a := sub_nonneg.mpr code.ordered.le
        calc
          ‖code.right.1 - code.left.1‖ ≤
              |(code.right.1 - code.left.1).re| +
                |(code.right.1 - code.left.1).im| := hnorm
          _ ≤ Metric.diam C.region.support + (b - a) := by
            rw [halong, abs_of_nonneg hab]
            simpa [add_comm] using add_le_add_left hV (b - a)
          _ < P.controlRadius := by linarith [hcontrol]
    | vertical =>
        have halong : (code.right.1 - code.left.1).im = b - a := by
          have hRim : code.right.1.im = b := by
            simpa [Axis.coord] using code.right_value
          have hLim : code.left.1.im = a := by
            simpa [Axis.coord] using code.left_value
          simp [Complex.sub_im, hRim, hLim]
        have htransV : (code.right.1 - code.left.1).re = (vR - vL).re := by
          rw [show code.right.1 = vR + tR from hR,
            show code.left.1 = vL + tL from hL]
          simp only [Complex.sub_re, Complex.add_re]
          have hLc := hc tL htL
          have hRc := hc tR htR
          simp only [Axis.transverseCoord] at hLc hRc
          linarith
        have hV : |(code.right.1 - code.left.1).re| ≤
            Metric.diam C.region.support := by
          rw [htransV]
          have hdistV' : ‖vR - vL‖ ≤ Metric.diam C.region.support := by
            simpa [Complex.dist_eq, norm_sub_rev] using hdistV
          exact (Complex.abs_re_le_norm _).trans hdistV'
        have hab : 0 ≤ b - a := sub_nonneg.mpr code.ordered.le
        calc
          ‖code.right.1 - code.left.1‖ ≤
              |(code.right.1 - code.left.1).re| +
                |(code.right.1 - code.left.1).im| := hnorm
          _ ≤ (b - a) + Metric.diam C.region.support := by
            rw [halong, abs_of_nonneg hab]
            simpa [add_comm, add_left_comm] using add_le_add_right hV (b - a)
          _ < P.controlRadius := by linarith [hcontrol]
  have hmem : code.lengthScalar ∈ boundedScalarDifferences C P.controlRadius := by
    rw [code.lengthScalar_formula]
    refine ⟨axis, code.right, code.left, hdist, ?_⟩
    change (C.translatedDifferenceScalar axis code.right code.left : ℝ) =
      axis.coord ((code.right : Tiling.Plane) - (code.left : Tiling.Plane))
    cases axis <;> rfl
  rw [← P.scalarAlphabet_exact] at hmem
  exact hmem

private theorem genuineGenericSection_construct :
    ∀ (C : ApproximationContext.{0}) (axis : Axis) (q : ℝ),
    q ∉ (IntrinsicVertices.intrinsicCoordinateLevels C.region axis.swap : Set ℝ) →
    ({x : ℝ | FilledSliceChains.slicePoint axis q x ∈ C.region.openCarrier} : Set ℝ).Nonempty →
    ∃ A : GenuineGenericSection C axis,
      A.transverse = q ∧
      A.rawCarrier = {x : ℝ | FilledSliceChains.slicePoint axis q x ∈ C.region.openCarrier} := by
  intro C axis q hq hnonempty
  cases axis with
  | horizontal =>
      have hq' : q ∉ C.region.vertexFinset.image Complex.im := by
        simpa [IntrinsicVertices.intrinsicCoordinateLevels, Axis.swap, Axis.coord] using hq
      obtain ⟨P⟩ := horizontalGenericSlicePresentation_exists C.region hq'
      let B : Set ℝ :=
        {x : ℝ | FilledSliceChains.slicePoint Axis.horizontal q x ∈ C.region.openCarrier}
      have hB : B = horizontalSlice C.region q := by
        ext x
        have heq : FilledSliceChains.slicePoint Axis.horizontal q x = Complex.mk x q := by
          apply Complex.ext <;> simp [FilledSliceChains.slicePoint]
        change FilledSliceChains.slicePoint Axis.horizontal q x ∈ C.region.openCarrier ↔
          Complex.mk x q ∈ C.region.openCarrier
        rw [heq]
      let I : OneDimensional.FiniteInterval.IntervalPresentation B := {
        n := P.n
        left := P.left
        right := P.right
        lt := P.lt
        union_eq := hB.trans P.union_eq }
      refine ⟨{
        transverse := q
        generic := hq
        rawCarrier := B
        rawCarrier_eq := by rfl
        presentation := I
        nonempty := hnonempty
        leftVertex := P.leftVertex
        rightVertex := P.rightVertex
        leftVertex_coord := P.leftVertex_coord
        rightVertex_coord := P.rightVertex_coord }, rfl, ?_⟩
      rfl
  | vertical =>
      have hq' : q ∉ C.region.vertexFinset.image Complex.re := by
        simpa [IntrinsicVertices.intrinsicCoordinateLevels, Axis.swap, Axis.coord] using hq
      obtain ⟨P⟩ := verticalGenericSlicePresentation_exists C.region hq'
      let B : Set ℝ :=
        {x : ℝ | FilledSliceChains.slicePoint Axis.vertical q x ∈ C.region.openCarrier}
      have hB : B = verticalSlice C.region q := by
        ext x
        have heq : FilledSliceChains.slicePoint Axis.vertical q x = Complex.mk q x := by
          apply Complex.ext <;> simp [FilledSliceChains.slicePoint]
        change FilledSliceChains.slicePoint Axis.vertical q x ∈ C.region.openCarrier ↔
          Complex.mk q x ∈ C.region.openCarrier
        rw [heq]
      let I : OneDimensional.FiniteInterval.IntervalPresentation B := {
        n := P.n
        left := P.left
        right := P.right
        lt := P.lt
        union_eq := hB.trans P.union_eq }
      refine ⟨{
        transverse := q
        generic := hq
        rawCarrier := B
        rawCarrier_eq := by rfl
        presentation := I
        nonempty := hnonempty
        leftVertex := P.lowerVertex
        rightVertex := P.upperVertex
        leftVertex_coord := P.lowerVertex_coord
        rightVertex_coord := P.upperVertex_coord }, rfl, ?_⟩
      rfl

private theorem intervalPresentation_min_left
    {B : Set ℝ} (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hB : B.Nonempty) :
    ∃ i : Fin P.n, ∀ j : Fin P.n, P.left i ≤ P.left j := by
  have hE : P.endpoints.Nonempty := P.endpoints_nonempty hB
  let m : ℝ := P.endpoints.min' hE
  have hleft (j : Fin P.n) : P.left j ∈ P.endpoints := by
    rw [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union]
    exact Or.inl (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hright (j : Fin P.n) : P.right j ∈ P.endpoints := by
    rw [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hmin (j : Fin P.n) : m ≤ P.left j :=
    Finset.min'_le _ _ (hleft j)
  have hmleft : ∃ i : Fin P.n, m = P.left i := by
    have hm : m ∈ P.endpoints := Finset.min'_mem _ hE
    rw [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union] at hm
    rcases hm with hm | hm
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hm
      exact ⟨i, hi.symm⟩
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hm
      exfalso
      have hmi := hmin i
      dsimp only [m] at hi hmi
      rw [← hi] at hmi
      exact (not_lt_of_ge hmi) (P.lt i)
  obtain ⟨i, hi⟩ := hmleft
  refine ⟨i, ?_⟩
  intro j
  exact le_trans (le_of_eq hi.symm) (hmin j)

private theorem normalized_carrier_inf_of_min_left
    {B : Set ℝ} (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hB : B.Nonempty) (i : Fin P.n)
    (hmin : ∀ j : Fin P.n, P.left i ≤ P.left j) :
    sInf (closure ((-P.left i) +ᵥ B)) = 0 := by
  have hcl_nonempty : (closure ((-P.left i) +ᵥ B)).Nonempty := by
    rw [closure_vadd]
    exact (hB.mono subset_closure).image (fun x => -P.left i + x)
  have hcl_bdd : BddBelow (closure ((-P.left i) +ᵥ B)) := by
    refine ⟨0, ?_⟩
    intro x hx
    rw [closure_vadd] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy' : y ∈ ⋃ j : Fin P.n, Icc (P.left j) (P.right j) := by
      rw [← P.closure_eq_iUnion_Icc]
      exact hy
    rcases Set.mem_iUnion.mp hy' with ⟨j, hy⟩
    have hleft : P.left i ≤ P.left j := hmin j
    change 0 ≤ -P.left i + y
    linarith [hy.1]
  apply le_antisymm
  · apply csInf_le hcl_bdd
    rw [closure_vadd]
    have hiend : P.left i ∈ (P.endpoints : Set ℝ) := by
      change P.left i ∈ P.endpoints
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    exact ⟨P.left i, P.endpoint_subset_closure hiend, by simp⟩
  · apply le_csInf hcl_nonempty
    intro x hx
    rw [closure_vadd] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy' : y ∈ ⋃ j : Fin P.n, Icc (P.left j) (P.right j) := by
      rw [← P.closure_eq_iUnion_Icc]
      exact hy
    rcases Set.mem_iUnion.mp hy' with ⟨j, hy⟩
    change 0 ≤ -P.left i + y
    linarith [hy.1, hmin j]

private theorem intervalPresentation_volume_real_pos
    {B : Set ℝ} (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hB : B.Nonempty) : 0 < volume.real B := by
  rw [MeasureTheory.measureReal_def]
  exact ENNReal.toReal_pos (P.isOpen.measure_ne_zero volume hB) P.volume_ne_top

private theorem translated_intervalPresentation_volume_real_pos
    {B : Set ℝ} (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hB : B.Nonempty) (c : ℝ) : 0 < volume.real (c +ᵥ B) := by
  rw [MeasureTheory.measureReal_def, MeasureTheory.measure_vadd]
  exact intervalPresentation_volume_real_pos P hB

private theorem finiteIntersection_volume_mem_coordinateSpace
    {C : ApproximationContext.{0}} {B : Set ℝ}
    (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hleft : ∀ i, P.left i ∈ C.coordinateSpace)
    (hright : ∀ i, P.right i ∈ C.coordinateSpace)
    (u : Finset (Fin P.n)) (hu : u.Nonempty) :
    volume.real (⋂ i ∈ u, Set.Ioo (P.left i) (P.right i)) ∈ C.coordinateSpace := by
  classical
  let a : ℝ := u.sup' hu (fun i => P.left i)
  let b : ℝ := u.inf' hu (fun i => P.right i)
  have ha : a ∈ C.coordinateSpace := by
    obtain ⟨i, hi, hia⟩ := Finset.exists_mem_eq_sup' hu
      (fun i : Fin P.n => P.left i)
    change u.sup' hu (fun i => P.left i) ∈ C.coordinateSpace
    rw [hia]
    exact hleft i
  have hb : b ∈ C.coordinateSpace := by
    obtain ⟨i, hi, hib⟩ := Finset.exists_mem_eq_inf' hu
      (fun i : Fin P.n => P.right i)
    change u.inf' hu (fun i => P.right i) ∈ C.coordinateSpace
    rw [hib]
    exact hright i
  by_cases hne : (⋂ i ∈ u, Set.Ioo (P.left i) (P.right i)).Nonempty
  · have hinter : (⋂ i ∈ u, Set.Ioo (P.left i) (P.right i)) = Set.Ioo a b := by
      ext x
      constructor
      · intro hx
        have hxall := Set.mem_iInter₂.mp hx
        obtain ⟨i, hi, hia⟩ := Finset.exists_mem_eq_sup' hu
          (fun i : Fin P.n => P.left i)
        obtain ⟨j, hj, hjb⟩ := Finset.exists_mem_eq_inf' hu
          (fun i : Fin P.n => P.right i)
        refine ⟨?_, ?_⟩
        · change u.sup' hu (fun i => P.left i) < x
          rw [hia]
          exact (hxall i hi).1
        · change x < u.inf' hu (fun i => P.right i)
          rw [hjb]
          exact (hxall j hj).2
      · intro hx
        apply Set.mem_iInter₂.mpr
        intro i hi
        refine ⟨lt_of_le_of_lt (Finset.le_sup' _ hi) hx.1,
          lt_of_lt_of_le hx.2 (Finset.inf'_le _ hi)⟩
    have hab : a ≤ b := by
      obtain ⟨x, hx⟩ := hne
      rw [hinter] at hx
      exact hx.1.le.trans hx.2.le
    rw [hinter, Real.volume_real_Ioo_of_le hab]
    exact C.coordinateSpace.sub_mem hb ha
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, MeasureTheory.measureReal_empty]
    exact C.coordinateSpace.zero_mem

private theorem intervalPresentation_volume_mem_coordinateSpace
    {C : ApproximationContext.{0}} {B : Set ℝ}
    (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hleft : ∀ i, P.left i ∈ C.coordinateSpace)
    (hright : ∀ i, P.right i ∈ C.coordinateSpace) :
    volume.real B ∈ C.coordinateSpace := by
  classical
  rw [P.union_eq]
  have hsum := MeasureTheory.measureReal_biUnion_eq_sum_powerset
    (μ := volume)
    (t := (Finset.univ : Finset (Fin P.n)))
    (s := fun i : Fin P.n => Set.Ioo (P.left i) (P.right i))
    (fun i hi => measurableSet_Ioo)
    (fun i hi => (Metric.isBounded_Ioo (P.left i) (P.right i)).measure_lt_top.ne)
  have hsum' : volume.real (⋃ i : Fin P.n,
      Set.Ioo (P.left i) (P.right i)) =
      ∑ u ∈ (Finset.univ : Finset (Fin P.n)).powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) *
          volume.real (⋂ i ∈ u, Set.Ioo (P.left i) (P.right i)) := by
    simpa only [Finset.mem_univ, iUnion_true] using hsum
  rw [hsum']
  apply C.coordinateSpace.sum_mem
  intro u hu
  have hune : u.Nonempty := (Finset.mem_filter.mp hu).2
  have hcoeff : (-1 : ℝ) ^ (u.card + 1) = 1 ∨
      (-1 : ℝ) ^ (u.card + 1) = -1 := neg_one_pow_eq_or ℝ _
  rcases hcoeff with hcoeff | hcoeff
  · rw [hcoeff]
    simpa only [one_mul] using
      (finiteIntersection_volume_mem_coordinateSpace P hleft hright u hune)
  · rw [hcoeff]
    simpa only [neg_one_mul] using C.coordinateSpace.neg_mem
      (finiteIntersection_volume_mem_coordinateSpace P hleft hright u hune)

private structure NormalizedGenericSectionCore (C : ApproximationContext.{0})
    (axis : Axis) where
  raw : GenuineGenericSection C axis
  originInterval : Fin raw.presentation.n
  originVertex : ↥C.region.vertices
  originVertex_eq : originVertex = raw.leftVertex originInterval
  origin : ℝ
  origin_eq : origin = axis.coord originVertex.1
  originScalar : C.coordinateSpace
  originScalar_coe : (originScalar : ℝ) = origin
  carrier : Set ℝ
  carrier_eq : carrier = (-origin) +ᵥ raw.rawCarrier
  normalized : sInf (closure carrier) = 0
  mass : ℝ
  mass_eq : mass = volume.real carrier
  mass_pos : 0 < mass

private theorem normalizedGenericSection_core_construct :
    ∀ {C : ApproximationContext.{0}} {axis : Axis}
    (A : GenuineGenericSection C axis),
    ∃ N : NormalizedGenericSectionCore C axis, N.raw = A := by
  intro C axis A
  obtain ⟨i, hmin⟩ := intervalPresentation_min_left A.presentation A.nonempty
  let o : ℝ := A.presentation.left i
  let ov : ↥C.region.vertices := A.leftVertex i
  let os : C.coordinateSpace := match axis with
    | .horizontal => ⟨ov.1.re, C.vertex_re_mem ov.1 ov.2⟩
    | .vertical => ⟨ov.1.im, C.vertex_im_mem ov.1 ov.2⟩
  let B : Set ℝ := (-o) +ᵥ A.rawCarrier
  have hov : ov = A.leftVertex i := rfl
  have hoo : o = axis.coord ov.1 := by
    cases axis
    · change A.presentation.left i = (A.leftVertex i).1.re
      exact (A.leftVertex_coord i).symm
    · change A.presentation.left i = (A.leftVertex i).1.im
      exact (A.leftVertex_coord i).symm
  have hos : (os : ℝ) = o := by
    cases axis
    · change (A.leftVertex i).1.re = A.presentation.left i
      exact A.leftVertex_coord i
    · change (A.leftVertex i).1.im = A.presentation.left i
      exact A.leftVertex_coord i
  have hnorm : sInf (closure B) = 0 := by
    exact normalized_carrier_inf_of_min_left A.presentation A.nonempty i hmin
  have hmass : 0 < volume.real B := by
    exact translated_intervalPresentation_volume_real_pos A.presentation A.nonempty (-o)
  refine ⟨{
    raw := A
    originInterval := i
    originVertex := ov
    originVertex_eq := hov
    origin := o
    origin_eq := hoo
    originScalar := os
    originScalar_coe := hos
    carrier := B
    carrier_eq := rfl
    normalized := hnorm
    mass := volume.real B
    mass_eq := rfl
    mass_pos := hmass }, rfl⟩

private theorem normalizedGenericSection_construct :
    ∀ {C : ApproximationContext.{0}} {axis : Axis}
    (A : GenuineGenericSection C axis),
    ∃ N : NormalizedGenericSection C axis, N.raw = A := by
  intro C axis A
  obtain ⟨N, hN⟩ := normalizedGenericSection_core_construct A
  have hleft : ∀ i, N.raw.presentation.left i ∈ C.coordinateSpace := by
    intro i
    cases axis
    · rw [← N.raw.leftVertex_coord i]
      exact C.vertex_re_mem _ (N.raw.leftVertex i).property
    · rw [← N.raw.leftVertex_coord i]
      exact C.vertex_im_mem _ (N.raw.leftVertex i).property
  have hright : ∀ i, N.raw.presentation.right i ∈ C.coordinateSpace := by
    intro i
    cases axis
    · rw [← N.raw.rightVertex_coord i]
      exact C.vertex_re_mem _ (N.raw.rightVertex i).property
    · rw [← N.raw.rightVertex_coord i]
      exact C.vertex_im_mem _ (N.raw.rightVertex i).property
  have hmassRaw : volume.real N.raw.rawCarrier ∈ C.coordinateSpace :=
    intervalPresentation_volume_mem_coordinateSpace N.raw.presentation hleft hright
  have hmassCarrier : volume.real N.carrier ∈ C.coordinateSpace := by
    rw [N.carrier_eq, MeasureTheory.measureReal_def, MeasureTheory.measure_vadd]
    exact hmassRaw
  let ms : C.coordinateSpace := ⟨volume.real N.carrier, hmassCarrier⟩
  have hms : (ms : ℝ) = N.mass := by
    exact rfl |>.trans N.mass_eq.symm
  refine ⟨{
    raw := N.raw
    originInterval := N.originInterval
    originVertex := N.originVertex
    originVertex_eq := N.originVertex_eq
    origin := N.origin
    origin_eq := N.origin_eq
    originScalar := N.originScalar
    originScalar_coe := N.originScalar_coe
    carrier := N.carrier
    carrier_eq := N.carrier_eq
    normalized := N.normalized
    mass := N.mass
    mass_eq := N.mass_eq
    mass_pos := N.mass_pos
    massScalar := ms
    massScalar_coe := hms }, hN⟩

private theorem noGap_traceHole_bounded :
    ∀ (axis : Axis) {A Y : Set ℝ} {G : ℝ}, IsOpen A → A.Nonempty →
      OneDimensional.IsFiniteIntervalRegion A → Y.Nonempty →
      (∀ x : ℝ, ∃ y ∈ Y, x - G < y ∧ y < x + G) →
      Linked G (FilledSliceChains.slicePoint axis 0 '' Y) →
      ∀ {a b : ℝ}, a < b → Ioo a b ∩ interior (closure (A + Y)) = ∅ → b - a ≤ G := by
  intro axis A Y G hAopen hAne hAfin hYne hdense hlinked a b hab hhole
  rcases hAfin with ⟨n, left, right, hlt, hAeq⟩
  obtain ⟨x, hx⟩ := hAne
  rw [hAeq] at hx
  simp only [mem_iUnion] at hx
  obtain ⟨i, hxi⟩ := hx
  have huv : left i < right i := hlt i
  let u : ℝ := left i
  let v : ℝ := right i
  let L : ℝ := a - v
  let R : ℝ := b - u
  by_contra hnot
  have hGb : G < b - a := lt_of_not_ge hnot
  have hLR : G < R - L := by
    dsimp [R, L, u, v]
    linarith
  have hopenAdd : IsOpen (A + Y) := by
    have heq : A + Y = ⋃ y : Y, (y : ℝ) +ᵥ A := by
      ext z
      constructor
      · rintro ⟨x, hxA, y, hyY, rfl⟩
        refine mem_iUnion.2 ⟨⟨y, hyY⟩, ?_⟩
        exact ⟨x, hxA, by simp [vadd_eq_add, add_comm]⟩
      · intro hz
        rcases mem_iUnion.1 hz with ⟨y, hy⟩
        rcases hy with ⟨x, hxA, rfl⟩
        exact ⟨x, hxA, (y : ℝ), y.property, by simp [vadd_eq_add, add_comm]⟩
    rw [heq]
    exact isOpen_iUnion fun y : Y => hAopen.vadd (y : ℝ)
  have hYavoid : Y ∩ Ioo L R = ∅ := by
    ext y
    constructor
    · rintro ⟨hyY, hyL, hyR⟩
      have hmaxmin : max (u + y) a < min (v + y) b := by
        apply max_lt_iff.mpr
        constructor
        · apply lt_min_iff.mpr
          constructor
          · linarith [huv]
          · dsimp [R] at hyR
            linarith
        · apply lt_min_iff.mpr
          constructor
          · dsimp [L] at hyL
            linarith
          · exact hab
      have hcross : (Ioo (u + y) (v + y) ∩ Ioo a b).Nonempty := by
        rw [Ioo_inter_Ioo]
        exact nonempty_Ioo.mpr hmaxmin
      obtain ⟨z, hz⟩ := hcross
      have hzadd : z ∈ A + Y := by
        refine ⟨z - y, ?_, y, hyY, ?_⟩
        · rw [hAeq]
          exact mem_iUnion.2 ⟨i, ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩⟩
        · change (z - y) + y = z
          rw [sub_add_cancel]
      have hzsupport : z ∈ interior (closure (A + Y)) :=
        hopenAdd.subset_interior_closure hzadd
      have hzempty : z ∈ (∅ : Set ℝ) := by rw [← hhole]; exact ⟨hz.2, hzsupport⟩
      simp at hzempty
    · intro hy
      simp at hy
  have hcoord : ∀ y : ℝ, axis.coord (FilledSliceChains.slicePoint axis 0 y) = y := by
    intro y
    cases axis <;> simp [FilledSliceChains.slicePoint, Tiling.AxisParallel.Axis.coord]
  have hdist : ∀ y z : ℝ,
      dist (FilledSliceChains.slicePoint axis 0 y) (FilledSliceChains.slicePoint axis 0 z) =
        |y - z| := by
    intro y z
    cases axis <;>
      simp [FilledSliceChains.slicePoint, Complex.dist_eq, ← Complex.ofReal_sub, ← sub_mul]
  obtain ⟨yL, hyLY, hyL₁, hyL₂⟩ := hdense (L - G)
  obtain ⟨yR, hyRY, hyR₁, hyR₂⟩ := hdense (R + G)
  have hyLl : yL < L := by linarith
  have hyRr : R < yR := by linarith
  have hstep : ∀ {x y : Tiling.Plane},
      x ∈ FilledSliceChains.slicePoint axis 0 '' Y → y ∈ FilledSliceChains.slicePoint axis 0 '' Y →
      axis.coord x ≤ L → dist x y < G → axis.coord y ≤ L := by
    rintro x y ⟨xv, hxv, rfl⟩ ⟨yv, hyv, rfl⟩ hxL hxy
    have hyvCases : yv ≤ L ∨ R ≤ yv := by
      by_cases hyle : yv ≤ L
      · exact Or.inl hyle
      · right
        have hnot : ¬ yv < R := by
          intro hltR
          have hyempty : yv ∈ (∅ : Set ℝ) := by
            rw [← hYavoid]
            exact ⟨hyv, lt_of_not_ge hyle, hltR⟩
          simp at hyempty
        exact le_of_not_gt hnot
    rcases hyvCases with hyvL | hyvR
    · simpa only [hcoord] using hyvL
    · have hxy' : |xv - yv| < G := by simpa only [hdist] using hxy
      have hxL' : xv ≤ L := by simpa only [hcoord] using hxL
      rw [abs_of_nonpos (by linarith : xv - yv ≤ 0)] at hxy'
      linarith
  have hchain : Relation.ReflTransGen
      (fun u v : Tiling.Plane => u ∈ FilledSliceChains.slicePoint axis 0 '' Y ∧
        v ∈ FilledSliceChains.slicePoint axis 0 '' Y ∧ dist u v < G)
      (FilledSliceChains.slicePoint axis 0 yL) (FilledSliceChains.slicePoint axis 0 yR) :=
    hlinked.2 _ ⟨yL, hyLY, rfl⟩ _ ⟨yR, hyRY, rfl⟩
  have hleftChain : ∀ z : Tiling.Plane,
      Relation.ReflTransGen
        (fun u v : Tiling.Plane => u ∈ FilledSliceChains.slicePoint axis 0 '' Y ∧
          v ∈ FilledSliceChains.slicePoint axis 0 '' Y ∧ dist u v < G)
        (FilledSliceChains.slicePoint axis 0 yL) z → axis.coord z ≤ L := by
    intro z hz
    induction hz with
    | refl =>
        rw [hcoord]
        exact le_of_lt hyLl
    | tail hab hbc ih =>
        exact hstep hbc.1 hbc.2.1 ih hbc.2.2
  have hyRle : yR ≤ L := by
    simpa only [hcoord] using hleftChain _ hchain
  linarith

private def axisSection (K : Region) (axis : Axis) (q : ℝ) : Set ℝ :=
  {x | FilledSliceChains.slicePoint axis q x ∈ K.openCarrier}

private structure GenericAxisSection (K : Region) (axis : Axis) (A : Set ℝ) where
  transverse : ℝ
  generic : transverse ∉
    (IntrinsicVertices.intrinsicCoordinateLevels K axis.swap : Set ℝ)
  carrier_eq : A = axisSection K axis transverse
  finiteIntervals : OneDimensional.IsFiniteIntervalRegion A
  isOpen : IsOpen A
  nonempty : A.Nonempty

private theorem genericAxisSection_vertical_slice
    {K : Region} {A : Set ℝ} (hA : GenericAxisSection K Axis.vertical A) :
    A = Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K hA.transverse := by
  simpa [axisSection, Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice,
    FilledSliceChains.slicePoint] using hA.carrier_eq

private theorem vertical_trace_fiber_eq
    {K : Region} {S : Set Tiling.Plane} {c q : ℝ} {A Y : Set ℝ}
    (hA : A = Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K q)
    (hline : ∀ s ∈ S, s.re = c) (hY : Y = Complex.im '' S) :
    {y : ℝ | ((c + q : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
        Tiling.AxisParallel.openUnion K S} = A + Y := by
  ext y
  constructor
  · intro hy
    change ((c + q : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
      Tiling.AxisParallel.openUnion K S at hy
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hy
    obtain ⟨s, hs⟩ := hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hs
    change -((s : Tiling.Plane)) +
      (((c + q : ℝ) : ℂ) + (y : ℂ) * Complex.I) ∈ K.openCarrier at hs
    have hsr := hline s.1 s.2
    have hYmem : s.1.im ∈ Y := by
      rw [hY]
      exact ⟨s.1, s.2, rfl⟩
    refine Set.mem_add.mpr ⟨y - s.1.im, ?_, s.1.im, hYmem, by linarith⟩
    rw [hA]
    change (((q : ℝ) : ℂ) + ((y - s.1.im : ℝ) : ℂ) * Complex.I) ∈ K.openCarrier
    convert hs using 1
    apply Complex.ext <;> simp [hsr]
    ring
  · rintro hy
    rw [Set.mem_add] at hy
    obtain ⟨u, hu, v, hvY, huv⟩ := hy
    rw [hY] at hvY
    obtain ⟨s, hs, rfl⟩ := hvY
    change ((c + q : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
      Tiling.AxisParallel.openUnion K S
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change -((s : Tiling.Plane)) +
      (((c + q : ℝ) : ℂ) + (y : ℂ) * Complex.I) ∈ K.openCarrier
    rw [show y = u + s.im by linarith [huv]]
    rw [hA] at hu
    change (((q : ℝ) : ℂ) + ((u : ℝ) : ℂ) * Complex.I) ∈ K.openCarrier at hu
    convert hu using 1
    apply Complex.ext <;> simp [hline s hs]

private theorem vertical_regularSupport_fiber_eq_local
    {K : Region} {S : Set Tiling.Plane} {c q delta : ℝ} {A : Set ℝ}
    (hA : A = Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K q)
    (hline : ∀ s ∈ S, s.re = c)
    (hconst : ∀ r : ℝ, |r - q| < delta →
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r =
        Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K q) :
    ∀ x : ℝ, x ∈ Set.Ioo (c + q - delta) (c + q + delta) →
      {y : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈
          Tiling.AxisParallel.regularSupport K S} =
        interior (closure (A + Complex.im '' S)) := by
  let U : Set Tiling.Plane := Tiling.AxisParallel.openUnion K S
  let V : Set Tiling.Plane := Set.Ioo (c + q - delta) (c + q + delta) ×ℂ Set.univ
  let W : Set Tiling.Plane := Set.Ioo (c + q - delta) (c + q + delta) ×ℂ
    (A + Complex.im '' S)
  have hUV : U ∩ V = W := by
    ext z
    constructor
    · rintro ⟨hzU, hzV⟩
      change z.re ∈ Set.Ioo (c + q - delta) (c + q + delta) ∧
        z.im ∈ (Set.univ : Set ℝ) at hzV
      change z.re ∈ Set.Ioo (c + q - delta) (c + q + delta) ∧
        z.im ∈ A + Complex.im '' S
      refine ⟨hzV.1, ?_⟩
      have hclose : |(z.re - c) - q| < delta := by
        rw [abs_lt]
        constructor <;> linarith [hzV.1.1, hzV.1.2]
      have hslice := hconst (z.re - c) hclose
      have hfiber := vertical_trace_fiber_eq
        (K := K) (S := S) (c := c) (q := z.re - c)
        (A := Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K (z.re - c))
        (Y := Complex.im '' S) rfl hline rfl
      rw [hslice] at hfiber
      have hzU' : ((c + (z.re - c) : ℝ) : ℂ) +
          (z.im : ℂ) * Complex.I ∈ U := by
        simpa [U, sub_add_cancel] using hzU
      change z.im ∈ {y : ℝ | ((c + (z.re - c) : ℝ) : ℂ) +
        (y : ℂ) * Complex.I ∈ Tiling.AxisParallel.openUnion K S} at hzU'
      rw [hfiber] at hzU'
      have : z.im ∈
          Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K q +
            Complex.im '' S := hzU'
      simpa [hA] using this
    · intro hz
      change z.re ∈ Set.Ioo (c + q - delta) (c + q + delta) ∧
        z.im ∈ A + Complex.im '' S at hz
      have hclose : |(z.re - c) - q| < delta := by
        rw [abs_lt]
        constructor <;> linarith [hz.1.1, hz.1.2]
      have hslice := hconst (z.re - c) hclose
      have hfiber := vertical_trace_fiber_eq
        (K := K) (S := S) (c := c) (q := z.re - c)
        (A := Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K (z.re - c))
        (Y := Complex.im '' S) rfl hline rfl
      rw [hslice] at hfiber
      have hztrace : z.im ∈
          Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K q +
            Complex.im '' S := by simpa [hA] using hz.2
      have hzU' : z.im ∈ {y : ℝ | ((c + (z.re - c) : ℝ) : ℂ) +
          (y : ℂ) * Complex.I ∈ Tiling.AxisParallel.openUnion K S} := by
        rw [hfiber]
        exact hztrace
      change z ∈ U ∩ V
      refine ⟨?_, ?_⟩
      · simpa [U, sub_add_cancel] using hzU'
      · change z.re ∈ Set.Ioo (c + q - delta) (c + q + delta) ∧
          z.im ∈ (Set.univ : Set ℝ)
        exact ⟨hz.1, Set.mem_univ _⟩
  have hVopen : IsOpen V := by
    exact isOpen_Ioo.reProdIm isOpen_univ
  have hpointV (x y : ℝ)
      (hx : x ∈ Set.Ioo (c + q - delta) (c + q + delta)) :
      (x : ℂ) + (y : ℂ) * Complex.I ∈ V := by
    simp [V, Complex.mem_reProdIm, hx]
  have hlocal (z : Tiling.Plane) (hzV : z ∈ V) :
      z ∈ interior (closure U) ↔ z ∈ interior (closure (U ∩ V)) := by
    constructor
    · intro hz
      have hsub : closure U ∩ V ⊆ closure (U ∩ V) := hVopen.closure_inter
      have hopen : IsOpen (interior (closure U) ∩ V) :=
        isOpen_interior.inter hVopen
      have hmax : interior (closure U) ∩ V ⊆ interior (closure (U ∩ V)) :=
        interior_maximal (fun w hw => hsub ⟨interior_subset hw.1, hw.2⟩) hopen
      exact hmax ⟨hz, hzV⟩
    · intro hz
      exact interior_mono (closure_mono inter_subset_left) hz
  intro x hx
  ext y
  change (x : ℂ) + (y : ℂ) * Complex.I ∈
    interior (closure U) ↔ y ∈ interior (closure (A + Complex.im '' S))
  rw [hlocal _ (hpointV x y hx), hUV]
  rw [Complex.closure_reProdIm, Complex.interior_reProdIm]
  simp only [Complex.mem_reProdIm]
  constructor <;> intro h
  · simpa using h.2
  · have hre : (((x : ℂ) + (y : ℂ) * Complex.I).re = x) := by simp
    refine ⟨?_, by simpa using h⟩
    rw [hre]
    exact isOpen_Ioo.subset_interior_closure hx

private theorem vertical_column_centres_countable
    {K : Region} {c : ℝ} {Y : Set ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y})) : Y.Countable := by
  let Q : Set Tiling.Plane := {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}
  let P := K.polygonalProtoTiling Q
  let F : Q → Set Tiling.Plane := fun q ↦ (q : Tiling.Plane) +ᵥ K.support
  let placementOf : Q → P.placements := fun q ↦ ⟨((q : Tiling.Plane), ()), q.2⟩
  have hinj : Function.Injective placementOf := by
    intro a b hab
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) hab)
  have hloc : LocallyFinite F := by
    have h := (P.locallyFinite_placedTile hpacking).comp_injective hinj
    change LocallyFinite F at h
    exact h
  have hne : ∀ q : Q, (F q).Nonempty := by
    intro q
    obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
    exact ⟨q.1 + x, ⟨x, interior_subset hx, rfl⟩⟩
  let _ : Countable Q := Set.countable_univ_iff.mp (hloc.countable_univ hne)
  let e : Y → Q := fun y ↦
    ⟨(c : ℂ) + (y.1 : ℂ) * Complex.I, by simp [Q, y.2]⟩
  have he : Function.Injective e := by
    intro y z hyz
    apply Subtype.ext
    simpa [e] using congrArg (fun w : Q ↦ w.1.im) hyz
  let _ : Countable Y := he.countable
  exact Set.countable_coe_iff.mp inferInstance

private theorem vertical_slice_pairwise_of_packing
    {K : Region} {c : ℝ} {Y : Set ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y})) :
    ∀ r : ℝ, Set.Pairwise Y
      (MeasureTheory.AEDisjoint volume on
        ((· +ᵥ Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r) :
          ℝ → Set ℝ)) := by
  have hopen :=
    (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K
      {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}).mp hpacking
  intro r y hyY y' hy'Y hyy'
  apply Disjoint.aedisjoint
  rw [Set.disjoint_left]
  intro x hxy hxy'
  let sy : Tiling.Plane := (c : ℂ) + (y : ℂ) * Complex.I
  let sy' : Tiling.Plane := (c : ℂ) + (y' : ℂ) * Complex.I
  have hsy : sy ∈ {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
    exact ⟨by simp [sy], by simpa [sy] using hyY⟩
  have hsy' : sy' ∈ {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
    exact ⟨by simp [sy'], by simpa [sy'] using hy'Y⟩
  have hsysy' : sy ≠ sy' := by
    intro heq
    apply hyy'
    simpa [sy, sy'] using congrArg Complex.im heq
  have hd : Disjoint (sy +ᵥ K.openCarrier) (sy' +ᵥ K.openCarrier) :=
    hopen hsy hsy' hsysy'
  rw [Set.disjoint_left] at hd
  apply hd (a := (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I))
  · change x ∈ y +ᵥ
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r at hxy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxy
    rw [Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice] at hxy
    change r + ((-y + x : ℝ) : ℂ) * Complex.I ∈ K.openCarrier at hxy
    have heq : -sy + (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I) =
        r + ((-y + x : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [sy]
    change -sy + (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I) ∈ K.openCarrier
    rwa [heq]
  · change x ∈ y' +ᵥ
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r at hxy'
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxy'
    rw [Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice] at hxy'
    change r + ((-y' + x : ℝ) : ℂ) * Complex.I ∈ K.openCarrier at hxy'
    have heq : -sy' + (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I) =
        r + ((-y' + x : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [sy']
    change -sy' + (((c + r : ℝ) : ℂ) + (x : ℂ) * Complex.I) ∈ K.openCarrier
    rwa [heq]

private theorem vertical_openUnion_fubini
    {K : Region} {c : ℝ} {Y : Set ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y})) :
    ∀ᵐ x : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume,
      ((((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
          Tiling.AxisParallel.openUnion K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) ↔
        (((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
          Tiling.AxisParallel.regularSupport K
            {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y})) := by
  have hae := Tiling.AxisParallel.openUnion_aeEq_regularSupport hpacking
  have hpull :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hae
  have hprod : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      (((p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈
          Tiling.AxisParallel.openUnion K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) ↔
        ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈
          Tiling.AxisParallel.regularSupport K
            {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y})) := by
    filter_upwards [hpull] with p hp
    have heq : ({ re := p.1, im := p.2 } : ℂ) =
        (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    change (({ re := p.1, im := p.2 } : ℂ) ∈
      Tiling.AxisParallel.openUnion K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) =
      (({ re := p.1, im := p.2 } : ℂ) ∈
        Tiling.AxisParallel.regularSupport K
          {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) at hp
    rw [heq] at hp
    exact Iff.of_eq hp
  exact MeasureTheory.Measure.ae_ae_of_ae_prod hprod

private theorem vertical_lineTiles_of_full_section
    {K : Region} {S : Set Tiling.Plane} {c : ℝ} {A Y : Set ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) (_hne : S.Nonempty)
    (hline : ∀ s ∈ S, s.re = c)
    (hA : GenericAxisSection K Axis.vertical A)
    (hY : Y = Complex.im '' S)
    (hfull : interior (closure (A + Y)) = Set.univ) :
    Tiling.AxisParallel.OneDimensional.LineTiles A Y := by
  have hC : S = {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
    ext z
    constructor
    · intro hz
      exact ⟨hline z hz, by rw [hY]; exact ⟨z, hz, rfl⟩⟩
    · rintro ⟨hzre, hzY⟩
      rw [hY] at hzY
      obtain ⟨s, hs, hsim⟩ := hzY
      have hsz : s.re = c := hline s hs
      have hsz' : s = z := by
        apply Complex.ext
        · linarith [hsz, hzre]
        · exact hsim
      exact hsz' ▸ hs
  have hpackC : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) := by
    rw [← hC]
    exact hpacking
  have hAq := genericAxisSection_vertical_slice hA
  have hqoff : hA.transverse ∉ K.vertexFinset.image Complex.re := by
    simpa [IntrinsicVertices.intrinsicCoordinateLevels, Axis.swap, Axis.coord] using hA.generic
  obtain ⟨delta, hdelta, hconst⟩ :=
    Tiling.AxisParallel.Foundations.GenericSlices.verticalSlice_locallyConstant
      K hqoff
  have hconst' : ∀ r : ℝ, |r - hA.transverse| < delta →
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r =
        Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K hA.transverse := by
    have hEq : ∀ r : ℝ,
        Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r =
          Tiling.AxisParallel.Foundations.GenericSlices.verticalSlice K r := by
      intro r
      ext y
      change ((r : ℂ) + (y : ℂ) * Complex.I ∈ K.openCarrier) ↔
        (({ re := r, im := y } : ℂ) ∈ K.openCarrier)
      have heq : ((r : ℂ) + (y : ℂ) * Complex.I) =
          ({ re := r, im := y } : ℂ) := by
        apply Complex.ext <;> simp
      rw [heq]
    intro r hr
    exact (hEq r).trans ((hconst r hr).trans (hEq hA.transverse).symm)
  have hpair := vertical_slice_pairwise_of_packing hpackC
  have hcount := vertical_column_centres_countable hpackC
  have hpairA : Y.Pairwise (MeasureTheory.AEDisjoint volume on
      ((· +ᵥ A) : ℝ → Set ℝ)) := by
    simpa [hAq] using hpair hA.transverse
  refine ⟨hA.isOpen.measurableSet, MeasurableSet.univ, hcount, hpairA, ?_⟩
  have hgood := vertical_openUnion_fubini hpackC
  have hdense : Dense {x : ℝ | ∀ᵐ y : ℝ ∂volume,
      ((((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
          Tiling.AxisParallel.openUnion K {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) ↔
        (((x : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
          Tiling.AxisParallel.regularSupport K
            {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}))} :=
    volume.dense_of_ae hgood
  have hopenI : IsOpen (Set.Ioo (c + hA.transverse - delta)
      (c + hA.transverse + delta)) := isOpen_Ioo
  have hneI : (Set.Ioo (c + hA.transverse - delta)
      (c + hA.transverse + delta)).Nonempty := by
    refine ⟨c + hA.transverse, ?_⟩
    simp only [Set.mem_Ioo]
    constructor <;> linarith
  obtain ⟨x, hxgood, hxI⟩ := hdense.exists_mem_open hopenI hneI
  have hxclose : |(x - c) - hA.transverse| < delta := by
    rw [abs_lt]
    simp only [Set.mem_Ioo] at hxI
    constructor <;> linarith
  have hslice := hconst' (x - c) hxclose
  have htrace : {y : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈
      Tiling.AxisParallel.openUnion K S} = A + Complex.im '' S := by
    have hf := vertical_trace_fiber_eq (K := K) (S := S) (c := c)
      (q := x - c)
      (A := Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K (x - c))
      (Y := Complex.im '' S) rfl hline rfl
    calc
      {y : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈
          Tiling.AxisParallel.openUnion K S} =
          Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K (x - c) +
            Complex.im '' S := by simpa [sub_add_cancel] using hf
      _ = A + Complex.im '' S := by
        rw [hslice]
        exact congrArg (fun T : Set ℝ => T + Complex.im '' S) hAq.symm
  have hfull' : interior (closure (A + Complex.im '' S)) = Set.univ := by
    rw [← hY]
    exact hfull
  have hreg := vertical_regularSupport_fiber_eq_local
    (K := K) (S := S) (c := c) (q := hA.transverse) (delta := delta)
    (A := A) hAq hline hconst'
  filter_upwards [hxgood] with y hy
  constructor
  · intro _
    have hyreg : (x : ℂ) + (y : ℂ) * Complex.I ∈
        Tiling.AxisParallel.regularSupport K
          {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
      have hyregS : (x : ℂ) + (y : ℂ) * Complex.I ∈
          Tiling.AxisParallel.regularSupport K S := by
        change y ∈ {y : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈
          Tiling.AxisParallel.regularSupport K S}
        rw [hreg x hxI, hfull']
        exact Set.mem_univ _
      rw [← hC]
      exact hyregS
    have hyopen : (x : ℂ) + (y : ℂ) * Complex.I ∈
        Tiling.AxisParallel.openUnion K
          {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := hy.mpr hyreg
    have hyopenS : (x : ℂ) + (y : ℂ) * Complex.I ∈
        Tiling.AxisParallel.openUnion K S := by
      simpa [hC] using hyopen
    have hytrace : y ∈ A + Complex.im '' S := by
      rw [← htrace]
      exact hyopenS
    rw [Set.mem_add] at hytrace
    obtain ⟨u, hu, v, hv, huv⟩ := hytrace
    obtain ⟨s, hs, hsim⟩ := hv
    have himage : s.im ∈ Complex.im '' S := ⟨s, hs, rfl⟩
    have hlY : s.im ∈ Y := hY.symm ▸ himage
    refine ⟨⟨s.im, hlY⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have heq : -(↑(⟨s.im, hlY⟩ : Y) : ℝ) + y = u := by
      change -s.im + y = u
      linarith [huv, hsim]
    simpa [vadd_eq_add, heq] using hu
  · intro _
    exact Set.mem_univ _

private theorem vertical_fullGenericSection_forcesCenterColumn
    {K : Region}
    {S : Set Tiling.Plane}
    (_hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (_hne : S.Nonempty) (_hline : ∃ c, ∀ s ∈ S, s.re = c)
    (_hcolumnable : ∃ Col, IsCenterColumn Axis.vertical K Col)
    (A Y : Set ℝ) (hA : GenericAxisSection K Axis.vertical A)
    (hY : Y = Complex.im '' S)
    (hfull : interior (closure (A + Y)) = Set.univ) :
    IsCenterColumn Axis.vertical K S := by
  obtain ⟨c, hc⟩ := _hline
  have htileA : Tiling.AxisParallel.OneDimensional.LineTiles A Y :=
    vertical_lineTiles_of_full_section _hpack _hne hc hA hY hfull
  have hC : S = {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
    ext z
    constructor
    · intro hz
      exact ⟨hc z hz, by rw [hY]; exact ⟨z, hz, rfl⟩⟩
    · rintro ⟨hzre, hzY⟩
      rw [hY] at hzY
      obtain ⟨s, hs, hsim⟩ := hzY
      have hsz : s.re = c := hc s hs
      have hsz' : s = z := by
        apply Complex.ext
        · linarith [hsz, hzre]
        · exact hsim
      exact hsz' ▸ hs
  have hYne : Y.Nonempty := by
    obtain ⟨s, hs⟩ := _hne
    exact ⟨s.im, hY.symm ▸ ⟨s, hs, rfl⟩⟩
  have hpackC : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) := by
    rw [← hC]
    exact _hpack
  obtain ⟨Col, hCol⟩ := _hcolumnable
  rw [hC]
  apply (Tiling.AxisParallel.Foundations.centerColumn_iff_genericSlices
    (C := {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y}) (c := c) (Y := Y)
    rfl hYne hpackC).2
  intro r hr hBr
  have hBfinite :=
    (Tiling.AxisParallel.Region.verticalSlice_finiteIntervals K hr).1
  have hBpos := ColumnSlices.finiteIntervalRegion_volume_toReal_pos hBfinite hBr
  have hAfinite := hA.finiteIntervals
  have hApos := ColumnSlices.finiteIntervalRegion_volume_toReal_pos hAfinite hA.nonempty
  have hAq := genericAxisSection_vertical_slice hA
  have hAqne :
      (Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice
        K hA.transverse).Nonempty := by
    rw [← hAq]
    exact hA.nonempty
  obtain ⟨p, hp, hperiod⟩ :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.exists_positiveLinePeriod
      hAfinite hApos htileA
  have hqoff : hA.transverse ∉ K.vertexFinset.image Complex.re := by
    simpa [IntrinsicVertices.intrinsicCoordinateLevels, Axis.swap, Axis.coord] using hA.generic
  have hmeasure :=
    Tiling.AxisParallel.Foundations.centerColumn_genericSlice_measure_eq hCol
      hqoff hr hAqne hBr
  have hmeasure' :
      (volume (Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice
        K r)).toReal = (volume A).toReal := by
    calc
      (volume (Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice
          K r)).toReal =
          (volume (Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice
            K hA.transverse)).toReal := hmeasure.symm
      _ = (volume A).toReal :=
        congrArg (fun T : Set ℝ => (volume T).toReal) hAq.symm
  exact Tiling.AxisParallel.Foundations.periodicPacking_tiles_of_measure_eq
    hAfinite hBfinite htileA hp hperiod
    (vertical_slice_pairwise_of_packing hpackC r) hmeasure'

private theorem interior_closure_add_eq_univ_of_lineTiles
    {B Y : Set ℝ}
    (hB : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion B)
    (hBpos : 0 < (volume B).toReal)
    (hTile : Tiling.AxisParallel.OneDimensional.LineTiles B Y) :
    interior (closure (B + Y)) = Set.univ := by
  let P := IntervalPresentation.ofIsFiniteIntervalRegion hB
  obtain ⟨hO, hreg, _, hRae, _, _⟩ :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.LineTilesOn.regularizedTarget
      P hTile hBpos
  have hRuniv : Tiling.AxisParallel.OneDimensional.FiniteInterval.regularizedTarget B Y =
      Set.univ := by
    apply Tiling.AxisParallel.OneDimensional.FiniteInterval.regularOpen_real_eq_of_aeEq
      hO hreg isOpen_univ (by simp)
    exact hRae
  have hline : Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion B Y = B + Y := by
    ext x
    constructor
    · intro hx
      rw [Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion,
        Set.mem_iUnion] at hx
      obtain ⟨y, hy⟩ := hx
      rw [Set.mem_add]
      refine ⟨x - (y : ℝ), ?_, (y : ℝ), y.2, ?_⟩
      · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
        simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hy
      · linarith
    · intro hx
      rw [Set.mem_add] at hx
      obtain ⟨b, hb, y, hy, hxy⟩ := hx
      rw [Tiling.AxisParallel.OneDimensional.FiniteInterval.lineOpenUnion,
        Set.mem_iUnion]
      refine ⟨⟨y, hy⟩, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      have heq : -(↑(⟨y, hy⟩ : Y) : ℝ) + x = b := by
        change -y + x = b
        linarith
      simpa [vadd_eq_add, heq] using hb
  rw [← hline]
  exact hRuniv

private theorem vertical_fullGenericSection_propagates
    {K : Region}
    {S : Set Tiling.Plane}
    (hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (hne : S.Nonempty) (hline : ∃ c, ∀ s ∈ S, s.re = c)
    (hcolumnable : ∃ Col, IsCenterColumn Axis.vertical K Col)
    {A : Set ℝ} (hA : GenericAxisSection K Axis.vertical A)
    (hAfull : interior (closure (A + Complex.im '' S)) = Set.univ)
    {B : Set ℝ} (hB : GenericAxisSection K Axis.vertical B) :
    interior (closure (B + Complex.im '' S)) = Set.univ := by
  have hline' := hline
  obtain ⟨c, hc⟩ := hline
  have hScol := vertical_fullGenericSection_forcesCenterColumn hpack hne hline'
    hcolumnable A (Complex.im '' S) hA rfl hAfull
  have hC : S = {z : Tiling.Plane | z.re = c ∧ z.im ∈ Complex.im '' S} := by
    ext z
    constructor
    · intro hz
      exact ⟨hc z hz, ⟨z, hz, rfl⟩⟩
    · rintro ⟨hzre, hzY⟩
      obtain ⟨s, hs, hsim⟩ := hzY
      have hsz : s.re = c := hc s hs
      have hsz' : s = z := by
        apply Complex.ext
        · linarith [hsz, hzre]
        · exact hsim
      exact hsz' ▸ hs
  have hYne : (Complex.im '' S).Nonempty := by
    obtain ⟨s, hs⟩ := hne
    exact ⟨s.im, ⟨s, hs, rfl⟩⟩
  have hpackC : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        {z : Tiling.Plane | z.re = c ∧ z.im ∈ Complex.im '' S}) := by
    rw [← hC]
    exact hpack
  rw [hC] at hScol
  have hBq := genericAxisSection_vertical_slice hB
  have hBqne :
      (Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice
        K hB.transverse).Nonempty := by
    rw [← hBq]
    exact hB.nonempty
  have hqoff : hB.transverse ∉ K.vertexFinset.image Complex.re := by
    simpa [IntrinsicVertices.intrinsicCoordinateLevels, Axis.swap, Axis.coord] using hB.generic
  have hlineB :=
    (Tiling.AxisParallel.Foundations.centerColumn_iff_genericSlices
      (C := {z : Tiling.Plane | z.re = c ∧ z.im ∈ Complex.im '' S})
      (c := c) (Y := Complex.im '' S) rfl hYne hpackC).mp hScol
  have htileB := hlineB hB.transverse hqoff hBqne
  have htileB' : Tiling.AxisParallel.OneDimensional.LineTiles B
      (Complex.im '' S) := by
    rw [hBq]
    exact htileB
  have hBpos := ColumnSlices.finiteIntervalRegion_volume_toReal_pos
    hB.finiteIntervals hB.nonempty
  exact interior_closure_add_eq_univ_of_lineTiles hB.finiteIntervals hBpos htileB'

private theorem coordinateSwap_smul_real_local (a : ℝ) :
    Tiling.AxisParallel.coordinateSwap (a : ℂ) = (a : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

private theorem coordinateSwap_packing_local
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) :
    Tiling.IsPacking K.coordinateSwap.toPolygonalRegion.prototileFamily
      (K.coordinateSwap.toPolygonalRegion.placements
        (Tiling.AxisParallel.coordinateSwap '' S)) := by
  rw [Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K.coordinateSwap
    (Tiling.AxisParallel.coordinateSwap '' S)]
  have hdisj :=
    (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K S).mp hpacking
  intro p hp q hq hpq
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  have hst : s ≠ t := by
    intro hst
    apply hpq
    simp [hst]
  have hd := hdisj hs ht hst
  rw [coordinateSwap_openCarrier]
  change Disjoint
    (Tiling.AxisParallel.coordinateSwap s +ᵥ
      (Tiling.AxisParallel.coordinateSwap '' K.openCarrier))
    (Tiling.AxisParallel.coordinateSwap t +ᵥ
      (Tiling.AxisParallel.coordinateSwap '' K.openCarrier))
  rw [(coordinateSwap_image_vadd s K.openCarrier).symm,
    (coordinateSwap_image_vadd t K.openCarrier).symm]
  rw [Set.disjoint_left]
  intro z hzS hzT
  obtain ⟨w, hw, hws⟩ := hzS
  obtain ⟨w', hw', hw't⟩ := hzT
  have hww : w = w' :=
    Tiling.AxisParallel.coordinateSwap.injective (hws.trans hw't.symm)
  exact (Set.disjoint_left.mp hd) hw (hww ▸ hw')

private theorem horizontal_column_swap_local
    {K : Region} {S : Set Tiling.Plane}
    (hC : IsCenterColumn Axis.horizontal K S) :
    IsCenterColumn Axis.vertical K.coordinateSwap
      (Tiling.AxisParallel.coordinateSwap '' S) := by
  refine ⟨coordinateSwap_packing_local hC.1, ?_, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hC.2.1
    exact ⟨Tiling.AxisParallel.coordinateSwap s, ⟨s, hs, rfl⟩⟩
  · obtain ⟨c, hc⟩ := hC.2.2.1
    refine ⟨c, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    simpa [Axis.transverseCoord] using hc w hw
  · intro a
    have hreg := Tiling.AxisParallel.regularSupport_coordinateSwap K S
    have hinv := hC.2.2.2 (a : ℝ)
    change (a : ℂ) * Complex.I +ᵥ
      regularSupport K.coordinateSwap
        (Tiling.AxisParallel.coordinateSwap '' S) =
      regularSupport K.coordinateSwap
        (Tiling.AxisParallel.coordinateSwap '' S)
    rw [hreg]
    have himage := coordinateSwap_image_vadd (a : ℂ) (regularSupport K S)
    have hinvImage := congrArg (Tiling.AxisParallel.coordinateSwap '' ·) hinv
    calc
      (a : ℂ) * Complex.I +ᵥ
          Tiling.AxisParallel.coordinateSwap '' regularSupport K S =
          Tiling.AxisParallel.coordinateSwap (a : ℂ) +ᵥ
            Tiling.AxisParallel.coordinateSwap '' regularSupport K S := by
              rw [coordinateSwap_smul_real_local]
      _ = Tiling.AxisParallel.coordinateSwap ''
          ((a : ℂ) +ᵥ regularSupport K S) := himage.symm
      _ = Tiling.AxisParallel.coordinateSwap '' regularSupport K S := hinvImage

private theorem vertical_column_swap_local
    {K : Region} {S : Set Tiling.Plane}
    (hC : IsCenterColumn Axis.vertical K S) :
    IsCenterColumn Axis.horizontal K.coordinateSwap
      (Tiling.AxisParallel.coordinateSwap '' S) := by
  refine ⟨coordinateSwap_packing_local hC.1, ?_, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hC.2.1
    exact ⟨Tiling.AxisParallel.coordinateSwap s, ⟨s, hs, rfl⟩⟩
  · obtain ⟨c, hc⟩ := hC.2.2.1
    refine ⟨c, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    simpa [Axis.transverseCoord] using hc w hw
  · intro a
    have hreg := Tiling.AxisParallel.regularSupport_coordinateSwap K S
    change (a : ℂ) +ᵥ regularSupport K.coordinateSwap
        (Tiling.AxisParallel.coordinateSwap '' S) =
      regularSupport K.coordinateSwap (Tiling.AxisParallel.coordinateSwap '' S)
    rw [hreg]
    have hinv := hC.2.2.2 (a : ℝ)
    have hinvImage := congrArg (Tiling.AxisParallel.coordinateSwap '' ·) hinv
    have himage := coordinateSwap_image_vadd
      ((a : ℂ) * Complex.I) (regularSupport K S)
    calc
      (a : ℂ) +ᵥ Tiling.AxisParallel.coordinateSwap '' regularSupport K S =
          Tiling.AxisParallel.coordinateSwap ((a : ℂ) * Complex.I) +ᵥ
            Tiling.AxisParallel.coordinateSwap '' regularSupport K S := by
              rw [show Tiling.AxisParallel.coordinateSwap ((a : ℂ) * Complex.I) =
                (a : ℂ) by apply Complex.ext <;> simp]
      _ = Tiling.AxisParallel.coordinateSwap ''
          (((a : ℂ) * Complex.I) +ᵥ regularSupport K S) := himage.symm
      _ = Tiling.AxisParallel.coordinateSwap '' regularSupport K S := hinvImage

private theorem vertical_column_swap_back_local
    {K : Region} {S : Set Tiling.Plane}
    (hC : IsCenterColumn Axis.vertical K.coordinateSwap
      (Tiling.AxisParallel.coordinateSwap '' S)) :
    IsCenterColumn Axis.horizontal K S := by
  have hback := vertical_column_swap_local
    (K := K.coordinateSwap)
    (S := Tiling.AxisParallel.coordinateSwap '' S) hC
  rw [Region.coordinateSwap_involutive K,
    IntrinsicVertices.coordinateSwap_image_image] at hback
  exact hback

private theorem coordinateSwap_vertexLevels_local (K : Region) :
    K.coordinateSwap.vertexFinset.image Complex.re =
      K.vertexFinset.image Complex.im := by
  ext r
  constructor
  · intro hr
    rcases Finset.mem_image.mp hr with ⟨v, hv, rfl⟩
    have hv' : v ∈ Tiling.vertexSet
        (Tiling.AxisParallel.coordinateSwap '' K.support) := by
      have hv'' : v ∈ K.coordinateSwap.vertices := by
        have hvin : v ∈ (↑K.coordinateSwap.vertexFinset : Set Tiling.Plane) := hv
        rw [K.coordinateSwap.coe_vertexFinset] at hvin
        exact hvin
      simpa [Region.vertices, Region.coordinateSwap] using hv''
    have hv'' : v ∈ Tiling.AxisParallel.coordinateSwap '' Tiling.vertexSet K.support :=
      (IntrinsicVertices.coordinateSwap_vertexSet K.support) ▸ hv'
    rcases hv'' with ⟨w, hw, hvw⟩
    refine Finset.mem_image.mpr ⟨w, ?_, ?_⟩
    · change w ∈ (↑K.vertexFinset : Set Tiling.Plane)
      rw [K.coe_vertexFinset]
      simpa [Region.vertices] using hw
    · simpa only [Tiling.AxisParallel.coordinateSwap_re] using congrArg Complex.re hvw
  · intro hr
    rcases Finset.mem_image.mp hr with ⟨w, hw, rfl⟩
    have hw' : w ∈ Tiling.vertexSet K.support := by
      have hw'' : w ∈ K.vertices := by
        have hwin : w ∈ (↑K.vertexFinset : Set Tiling.Plane) := hw
        rw [K.coe_vertexFinset] at hwin
        exact hwin
      simpa [Region.vertices] using hw''
    have hv' : Tiling.AxisParallel.coordinateSwap w ∈
        Tiling.vertexSet
          (Tiling.AxisParallel.coordinateSwap '' K.support) :=
      (IntrinsicVertices.coordinateSwap_vertexSet K.support).symm ▸
        (show Tiling.AxisParallel.coordinateSwap w ∈
            Tiling.AxisParallel.coordinateSwap '' Tiling.vertexSet K.support from
          ⟨w, hw', rfl⟩)
    refine Finset.mem_image.mpr ⟨Tiling.AxisParallel.coordinateSwap w, ?_, ?_⟩
    · change Tiling.AxisParallel.coordinateSwap w ∈
        (↑K.coordinateSwap.vertexFinset : Set Tiling.Plane)
      rw [K.coordinateSwap.coe_vertexFinset]
      simpa [Region.vertices, Region.coordinateSwap] using hv'
    · simp

private def horizontal_genericSection_swap
    {K : Region} {A : Set ℝ}
    (hA : GenericAxisSection K Axis.horizontal A) :
    GenericAxisSection K.coordinateSwap Axis.vertical A := by
  refine
    { transverse := hA.transverse
      generic := ?_
      carrier_eq := ?_
      finiteIntervals := hA.finiteIntervals
      isOpen := hA.isOpen
      nonempty := hA.nonempty }
  · intro hq
    have hq' : hA.transverse ∈ K.vertexFinset.image Complex.im := by
      rw [← coordinateSwap_vertexLevels_local K]
      exact hq
    apply hA.generic
    simpa [IntrinsicVertices.intrinsicCoordinateLevels, Axis.swap, Axis.coord] using hq'
  · calc
      A = axisSection K Axis.horizontal hA.transverse := hA.carrier_eq
      _ = axisSection K.coordinateSwap Axis.vertical hA.transverse := by
        ext x
        change (x : ℂ) + (hA.transverse : ℂ) * Complex.I ∈ K.openCarrier ↔
          (hA.transverse : ℂ) + (x : ℂ) * Complex.I ∈ K.coordinateSwap.openCarrier
        rw [coordinateSwap_openCarrier]
        constructor
        · intro hz
          refine ⟨(x : ℂ) + (hA.transverse : ℂ) * Complex.I, hz, ?_⟩
          apply Complex.ext <;> simp
        · rintro ⟨z, hz, hzx⟩
          have hz' : z = Tiling.AxisParallel.coordinateSwap
              ((hA.transverse : ℂ) + (x : ℂ) * Complex.I) := by
            rw [← Tiling.AxisParallel.coordinateSwap_apply_apply z, hzx]
          have hpoint : Tiling.AxisParallel.coordinateSwap
              ((hA.transverse : ℂ) + (x : ℂ) * Complex.I) =
              (x : ℂ) + (hA.transverse : ℂ) * Complex.I := by
            apply Complex.ext <;> simp
          rw [hpoint] at hz'
          exact hz'.symm ▸ hz

private theorem fullGenericSection_forcesCenterColumn :
    ∀ {C : Tiling.AxisParallel.Approximation.ApproximationContext.{0}}
      {S : Set Tiling.Plane} (axis : Axis),
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements S) →
      S.Nonempty → (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) →
      (∃ Col, IsCenterColumn axis C.region Col) →
      (A Y : Set ℝ) → GenericAxisSection C.region axis A →
      Y = axis.coord '' S →
      interior (closure (A + Y)) = Set.univ →
      IsCenterColumn axis C.region S := by
  intro C S axis hpack hne hline hcolumnable A Y hA hY hfull
  cases axis with
  | vertical =>
      have hline' : ∃ c, ∀ s ∈ S, s.re = c := by
        simpa [Axis.transverseCoord] using hline
      have hY' : Y = Complex.im '' S := by
        simpa [Axis.coord] using hY
      exact vertical_fullGenericSection_forcesCenterColumn hpack hne hline'
        hcolumnable A Y hA hY' hfull
  | horizontal =>
      have hline' : ∃ c, ∀ s ∈ S, s.im = c := by
        simpa [Axis.transverseCoord] using hline
      have hY' : Y = Complex.re '' S := by
        simpa [Axis.coord] using hY
      have hpack' := coordinateSwap_packing_local hpack
      have hlineSwap : ∃ c, ∀ z ∈ Tiling.AxisParallel.coordinateSwap '' S, z.re = c := by
        obtain ⟨c, hc⟩ := hline'
        refine ⟨c, ?_⟩
        rintro z ⟨s, hs, rfl⟩
        simpa using hc s hs
      have hcolumnSwap : ∃ Col, IsCenterColumn Axis.vertical
          C.region.coordinateSwap Col := by
        obtain ⟨Col, hCol⟩ := hcolumnable
        exact ⟨Tiling.AxisParallel.coordinateSwap '' Col,
          horizontal_column_swap_local hCol⟩
      have hA' := horizontal_genericSection_swap hA
      have himage : Complex.im ''
          (Tiling.AxisParallel.coordinateSwap '' S) = Complex.re '' S := by
        ext y
        constructor
        · rintro ⟨z, ⟨s, hs, rfl⟩, rfl⟩
          exact ⟨s, hs, rfl⟩
        · rintro ⟨s, hs, rfl⟩
          exact ⟨Tiling.AxisParallel.coordinateSwap s,
            ⟨s, hs, rfl⟩, by simp⟩
      have hYswap : Y = Complex.im ''
          (Tiling.AxisParallel.coordinateSwap '' S) := hY'.trans himage.symm
      have hfull0 := hfull
      rw [hY'] at hfull0
      have hfull' : interior (closure (A + Y)) = Set.univ := by
        rw [hYswap]
        rw [himage]
        exact hfull0
      have hswap := vertical_fullGenericSection_forcesCenterColumn
        hpack' (by exact hne.image Tiling.AxisParallel.coordinateSwap)
        hlineSwap hcolumnSwap A Y hA' hYswap hfull'
      exact vertical_column_swap_back_local hswap

private theorem fullGenericSection_propagates :
    ∀ {C : Tiling.AxisParallel.Approximation.ApproximationContext.{0}}
      {S : Set Tiling.Plane} (axis : Axis),
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements S) →
      S.Nonempty → (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) →
      (∃ Col, IsCenterColumn axis C.region Col) →
      ∀ {A : Set ℝ}, GenericAxisSection C.region axis A →
      interior (closure (A + axis.coord '' S)) = Set.univ →
      ∀ {B : Set ℝ}, GenericAxisSection C.region axis B →
      interior (closure (B + axis.coord '' S)) = Set.univ := by
  intro C S axis hpack hne hline hcolumnable A hA hAfull B hB
  cases axis with
  | vertical =>
      have hline' : ∃ c, ∀ s ∈ S, s.re = c := by
        simpa [Axis.transverseCoord] using hline
      have hAfull' : interior (closure (A + Complex.im '' S)) = Set.univ := by
        simpa [Axis.coord] using hAfull
      have h := vertical_fullGenericSection_propagates hpack hne hline'
        hcolumnable hA hAfull' hB
      simpa [Axis.coord] using h
  | horizontal =>
      have hline' : ∃ c, ∀ s ∈ S, s.im = c := by
        simpa [Axis.transverseCoord] using hline
      have hpack' := coordinateSwap_packing_local hpack
      have hlineSwap : ∃ c, ∀ z ∈ Tiling.AxisParallel.coordinateSwap '' S, z.re = c := by
        obtain ⟨c, hc⟩ := hline'
        refine ⟨c, ?_⟩
        rintro z ⟨s, hs, rfl⟩
        simpa using hc s hs
      have hcolumnSwap : ∃ Col, IsCenterColumn Axis.vertical
          C.region.coordinateSwap Col := by
        obtain ⟨Col, hCol⟩ := hcolumnable
        exact ⟨Tiling.AxisParallel.coordinateSwap '' Col,
          horizontal_column_swap_local hCol⟩
      have hA' := horizontal_genericSection_swap hA
      have hB' := horizontal_genericSection_swap hB
      have himage : Complex.im ''
          (Tiling.AxisParallel.coordinateSwap '' S) = Complex.re '' S := by
        ext y
        constructor
        · rintro ⟨z, ⟨s, hs, rfl⟩, rfl⟩
          exact ⟨s, hs, rfl⟩
        · rintro ⟨s, hs, rfl⟩
          exact ⟨Tiling.AxisParallel.coordinateSwap s,
            ⟨s, hs, rfl⟩, by simp⟩
      have hAfull' : interior (closure (A +
          Complex.im '' (Tiling.AxisParallel.coordinateSwap '' S))) = Set.univ := by
        rw [himage]
        simpa [Axis.coord] using hAfull
      have hBfull' := vertical_fullGenericSection_propagates hpack'
        (by exact hne.image Tiling.AxisParallel.coordinateSwap)
        hlineSwap hcolumnSwap hA' hAfull' hB'
      rw [himage] at hBfull'
      simpa [Axis.coord] using hBfull'



open Tiling.AxisParallel.Approximation
private theorem vertical_slice_constant_on_interval
    {K : Region} {u v : ℝ} (_huv : u < v)
    (hcell : ∀ r ∈ Set.Ioo u v,
      r ∉ K.vertexFinset.image Complex.re) :
    ∀ {q : ℝ}, q ∈ Set.Ioo u v →
      ∀ {r : ℝ}, r ∈ Set.Ioo u v →
        Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r =
          Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K q := by
  intro q hq r hr
  have hEq (s : ℝ) :
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K s =
        Tiling.AxisParallel.Foundations.GenericSlices.verticalSlice K s := by
    ext y
    change ((s : ℂ) + (y : ℂ) * Complex.I ∈ K.openCarrier) ↔
      (({ re := s, im := y } : ℂ) ∈ K.openCarrier)
    have heq : ((s : ℂ) + (y : ℂ) * Complex.I) =
        ({ re := s, im := y } : ℂ) := by
      apply Complex.ext <;> simp
    rw [heq]
  let f : Set.Ioo u v → Set ℝ := fun x ↦
    Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K x.1
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨δ, hδ, hconst⟩ :=
      Tiling.AxisParallel.Foundations.GenericSlices.verticalSlice_locallyConstant K
        (hcell x.1 x.2)
    let U : Set (Set.Ioo u v) :=
      (fun y : Set.Ioo u v ↦ y.1) ⁻¹' Set.Ioo (x.1 - δ) (x.1 + δ)
    refine ⟨U, ?_, ?_, ?_⟩
    · exact isOpen_Ioo.preimage continuous_subtype_val
    · change x.1 ∈ Set.Ioo (x.1 - δ) (x.1 + δ)
      simp only [Set.mem_Ioo]
      constructor <;> linarith
    · intro y hy
      have hy' : |y.1 - x.1| < δ := by
        rw [abs_lt]
        change y.1 ∈ Set.Ioo (x.1 - δ) (x.1 + δ) at hy
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hconst' := (hEq y.1).trans ((hconst y.1 hy').trans (hEq x.1).symm)
      simpa [f] using hconst'
  let _ : PreconnectedSpace (Set.Ioo u v) :=
    Subtype.preconnectedSpace isPreconnected_Ioo
  have hqr : f ⟨r, hr⟩ = f ⟨q, hq⟩ :=
    hf.apply_eq_of_preconnectedSpace _ _
  exact hqr

private theorem horizontal_slice_constant_on_interval
    {K : Region} {u v : ℝ} (_huv : u < v)
    (hcell : ∀ r ∈ Set.Ioo u v,
      r ∉ K.vertexFinset.image Complex.im) :
    ∀ {q : ℝ}, q ∈ Set.Ioo u v →
      ∀ {r : ℝ}, r ∈ Set.Ioo u v →
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K r =
          Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K q := by
  intro q hq r hr
  let f : Set.Ioo u v → Set ℝ := fun x ↦
    Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K x.1
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨δ, hδ, hconst⟩ :=
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice_locallyConstant K
        (hcell x.1 x.2)
    let U : Set (Set.Ioo u v) :=
      (fun y : Set.Ioo u v ↦ y.1) ⁻¹' Set.Ioo (x.1 - δ) (x.1 + δ)
    refine ⟨U, ?_, ?_, ?_⟩
    · exact isOpen_Ioo.preimage continuous_subtype_val
    · change x.1 ∈ Set.Ioo (x.1 - δ) (x.1 + δ)
      simp only [Set.mem_Ioo]
      constructor <;> linarith
    · intro y hy
      have hy' : |y.1 - x.1| < δ := by
        rw [abs_lt]
        change y.1 ∈ Set.Ioo (x.1 - δ) (x.1 + δ) at hy
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hconst' := hconst y.1 hy'
      simpa [f] using hconst'
  let _ : PreconnectedSpace (Set.Ioo u v) :=
    Subtype.preconnectedSpace isPreconnected_Ioo
  have hqr : f ⟨r, hr⟩ = f ⟨q, hq⟩ :=
    hf.apply_eq_of_preconnectedSpace _ _
  exact hqr

private theorem regularSupportClosureTransverse_bounded_local :
    ∀ (axis : Axis) {K : Region} {S : Set Tiling.Plane},
      (∃ c : ℝ, ∀ s ∈ S, axis.transverseCoord s = c) →
      ∃ c R : ℝ, ∀ z ∈ closure (regularSupport K S),
        axis.transverseCoord z ∈ Metric.closedBall c R := by
  intro axis K S halign
  obtain ⟨c, hc⟩ := halign
  obtain ⟨R, hR⟩ :=
    (Tiling.AxisParallel.regularSupportTransverseProjection_bounded
      axis ⟨c, hc⟩).subset_closedBall c
  let H : Set Tiling.Plane := axis.transverseCoord ⁻¹' Metric.closedBall c R
  have hH : IsClosed H := by
    cases axis <;> simp only [H, Axis.transverseCoord]
    · exact Metric.isClosed_closedBall.preimage Complex.continuous_im
    · exact Metric.isClosed_closedBall.preimage Complex.continuous_re
  have hsub : regularSupport K S ⊆ H := by
    intro z hz
    exact hR ⟨z, hz, rfl⟩
  refine ⟨c, R, ?_⟩
  intro z hz
  exact closure_minimal hsub hH hz
private theorem completeBoundaryLine_axis_eq_of_bounded_local
    {axis : Axis} {K : Region} {S : Set Tiling.Plane}
    (halign : ∃ c : ℝ, ∀ s ∈ S, axis.transverseCoord s = c)
    (hlocal : IsLocallyAxisParallelPolygonal (regularSupport K S))
    (L : CompleteBoundaryLine)
    (hL : L ∈ completeBoundaryLines (regularSupport K S) hlocal) :
    L.axis = axis := by
  obtain ⟨c, R, hR⟩ := regularSupportClosureTransverse_bounded_local axis halign
  have hfront : frontier (regularSupport K S) ⊆
      closure (regularSupport K S) := frontier_subset_closure
  have hbound : ∀ z ∈ L.carrier,
      axis.transverseCoord z ∈ Metric.closedBall c R := by
    intro z hz
    exact hR z (hfront (hL.1 hz))
  cases axis with
  | vertical =>
      cases haxis : L.axis with
      | vertical => rfl
      | horizontal =>
          let x : ℝ := c + |R| + 1
          let z : Tiling.Plane := (x : ℂ) + (L.level : ℂ) * Complex.I
          have hz : z ∈ L.carrier := by
            simp [CompleteBoundaryLine.carrier, haxis, z, Axis.transverseCoord]
          have hb := hbound z hz
          have hineq : |x - c| ≤ R := by
            simpa [Axis.transverseCoord, z, Metric.mem_closedBall, Real.dist_eq] using hb
          have hx : |x - c| = |R| + 1 := by
            dsimp [x]
            rw [show c + |R| + 1 - c = |R| + 1 by ring,
              abs_of_nonneg (by positivity)]
          rw [hx] at hineq
          linarith [le_abs_self R]
  | horizontal =>
      cases haxis : L.axis with
      | horizontal => rfl
      | vertical =>
          let x : ℝ := c + |R| + 1
          let z : Tiling.Plane := (L.level : ℂ) + (x : ℂ) * Complex.I
          have hz : z ∈ L.carrier := by
            simp [CompleteBoundaryLine.carrier, haxis, z, Axis.transverseCoord]
          have hb := hbound z hz
          have hineq : |x - c| ≤ R := by
            simpa [Axis.transverseCoord, z, Metric.mem_closedBall, Real.dist_eq] using hb
          have hx : |x - c| = |R| + 1 := by
            dsimp [x]
            rw [show c + |R| + 1 - c = |R| + 1 by ring,
              abs_of_nonneg (by positivity)]
          rw [hx] at hineq
          linarith [le_abs_self R]



private theorem horizontal_regularSupport_fiber_eq_local
    {K : Region} {S : Set Tiling.Plane} {c q delta : ℝ} {A : Set ℝ}
    (hA : A = Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K q)
    (hline : ∀ s ∈ S, s.im = c)
    (hconst : ∀ r : ℝ, |r - q| < delta →
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K r =
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K q) :
    ∀ y : ℝ, y ∈ Set.Ioo (c + q - delta) (c + q + delta) →
      {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈
          Tiling.AxisParallel.regularSupport K S} =
        interior (closure (A + Complex.re '' S)) := by
  have hslice : ∀ r : ℝ,
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice
          K.coordinateSwap r =
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K r := by
    intro r
    ext x
    change (r : ℂ) + (x : ℂ) * Complex.I ∈ K.coordinateSwap.openCarrier ↔
      Complex.mk x r ∈ K.openCarrier
    rw [coordinateSwap_openCarrier]
    constructor
    · rintro ⟨z, hz, hzx⟩
      have hz' : z = Tiling.AxisParallel.coordinateSwap
          ((r : ℂ) + (x : ℂ) * Complex.I) := by
        rw [← Tiling.AxisParallel.coordinateSwap_apply_apply z, hzx]
      have hp : Tiling.AxisParallel.coordinateSwap
          ((r : ℂ) + (x : ℂ) * Complex.I) = Complex.mk x r := by
        apply Complex.ext <;> simp
      rw [hp] at hz'
      rw [← hz']
      exact hz
    · intro hz
      refine ⟨Complex.mk x r, hz, ?_⟩
      apply Complex.ext <;> simp
  have hconst' : ∀ r : ℝ, |r - q| < delta →
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice
          K.coordinateSwap r =
        Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice
          K.coordinateSwap q := by
    intro r hr
    rw [hslice r, hconst r hr, ← hslice q]
  have hline' : ∀ z ∈ Tiling.AxisParallel.coordinateSwap '' S, z.re = c := by
    rintro z ⟨s, hs, rfl⟩
    simpa using hline s hs
  have hA' : A =
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice
        K.coordinateSwap q := by
    rw [hslice q]
    exact hA
  have hreg' := vertical_regularSupport_fiber_eq_local
    (K := K.coordinateSwap)
    (S := Tiling.AxisParallel.coordinateSwap '' S)
    (c := c) (q := q) (delta := delta) (A := A) hA' hline' hconst'
  have hsupport := Tiling.AxisParallel.regularSupport_coordinateSwap K S
  have himage : Complex.im '' (Tiling.AxisParallel.coordinateSwap '' S) =
      Complex.re '' S := by
    ext t
    constructor
    · rintro ⟨z, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Tiling.AxisParallel.coordinateSwap s,
        ⟨s, hs, rfl⟩, by simp⟩
  intro y hy
  ext x
  have hxy : Tiling.AxisParallel.coordinateSwap
      ((x : ℂ) + (y : ℂ) * Complex.I) =
      (y : ℂ) + (x : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hmem :
      ((x : ℂ) + (y : ℂ) * Complex.I ∈
        Tiling.AxisParallel.regularSupport K S) ↔
      ((y : ℂ) + (x : ℂ) * Complex.I ∈
        Tiling.AxisParallel.regularSupport K.coordinateSwap
          (Tiling.AxisParallel.coordinateSwap '' S)) := by
    rw [hsupport]
    constructor
    · intro hz
      exact ⟨_, hz, hxy⟩
    · rintro ⟨z, hz, hzx⟩
      have hzp : z = (x : ℂ) + (y : ℂ) * Complex.I :=
        Tiling.AxisParallel.coordinateSwap.injective (hzx.trans hxy.symm)
      simpa [hzp] using hz
  change ((x : ℂ) + (y : ℂ) * Complex.I ∈
      Tiling.AxisParallel.regularSupport K S) ↔
    x ∈ interior (closure (A + Complex.re '' S))
  have hright : ((y : ℂ) + (x : ℂ) * Complex.I ∈
      Tiling.AxisParallel.regularSupport K.coordinateSwap
        (Tiling.AxisParallel.coordinateSwap '' S)) ↔
      x ∈ interior (closure (A + Complex.re '' S)) := by
    have hxset := congrArg (fun E : Set ℝ => x ∈ E) (hreg' y hy)
    rw [himage] at hxset
    simpa using hxset
  exact hmem.trans hright

private theorem noncolumn_completeBoundaryLine_meetsProperVertices :
    ∀ {C : ApproximationContext.{0}} {S : Set Tiling.Plane} (axis : Axis),
      (∃ Col, IsCenterColumn axis C.region Col) → S.Nonempty →
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements S) →
      (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) →
      ¬ IsCenterColumn axis C.region S →
      ∀ (hlocal : IsLocallyAxisParallelPolygonal (regularSupport C.region S))
        (L : CompleteBoundaryLine),
        L ∈ completeBoundaryLines (regularSupport C.region S) hlocal →
        (L.carrier ∩ properVertices (regularSupport C.region S)).Nonempty := by
  intro C S axis hcolumnable hne hpack halign hnoncolumn hlocal L hL
  by_contra hempty
  have hno : L.carrier ∩ properVertices (regularSupport C.region S) = ∅ := by
    ext z
    constructor
    · intro hz
      exact False.elim (hempty ⟨z, hz⟩)
    · intro hz
      exact hz.elim
  have hstraight : ∀ z ∈ L.carrier,
      Tiling.BoundaryLocallyStraightAt (regularSupport C.region S) z := by
    intro z hz
    by_contra hnot
    have hz' : z ∈ L.carrier ∩ properVertices (regularSupport C.region S) :=
      ⟨hz, ⟨hL.1 hz, hnot⟩⟩
    rw [hno] at hz'
    exact hz'.elim
  cases axis with
  | vertical =>
      obtain ⟨c, hc⟩ := halign
      have hLv := completeBoundaryLine_axis_eq_of_bounded_local
        (axis := Axis.vertical) (K := C.region) (S := S) ⟨c, hc⟩ hlocal L hL
      have hLaxis : L.axis = Axis.vertical := hLv
      let V : Finset ℝ := C.region.vertexFinset.image Complex.re
      let q₀ : ℝ := L.level - c
      have hVclosed : IsClosed ((V.erase q₀ : Set ℝ)) := Finset.isClosed _
      have hVopen : IsOpen (((V.erase q₀ : Set ℝ))ᶜ) := hVclosed.isOpen_compl
      have hq₀mem : q₀ ∈ (((V.erase q₀ : Set ℝ))ᶜ) := by
        simp [V]
      obtain ⟨u, v, hq₀uv, huvsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hVopen.mem_nhds hq₀mem)
      have hcell_pos : ∀ r ∈ Set.Ioo q₀ v,
          r ∉ C.region.vertexFinset.image Complex.re := by
        intro r hr hrV
        have hr' : r ∈ (V.erase q₀ : Set ℝ) := by
          simp only [Finset.mem_coe, Finset.mem_erase]
          exact ⟨by linarith [hr.1, hq₀uv.1], by simpa [V] using hrV⟩
        exact (huvsub ⟨by linarith [hq₀uv.1, hr.1], hr.2⟩) hr'
      have hcell_neg : ∀ r ∈ Set.Ioo u q₀,
          r ∉ C.region.vertexFinset.image Complex.re := by
        intro r hr hrV
        have hr' : r ∈ (V.erase q₀ : Set ℝ) := by
          simp only [Finset.mem_coe, Finset.mem_erase]
          exact ⟨by linarith [hr.2, hq₀uv.2], by simpa [V] using hrV⟩
        exact (huvsub ⟨hr.1, by linarith [hr.2, hq₀uv.2]⟩) hr'
      cases hpositive : L.insideOnPositiveSide with
      | false =>
          let q : ℝ := (u + q₀) / 2
          have hqI : q ∈ Set.Ioo u q₀ := by
            dsimp [q]
            constructor <;> linarith [hq₀uv.1, hq₀uv.2]
          have hqoff : q ∉ C.region.vertexFinset.image Complex.re :=
            hcell_neg q hqI
          have hconst : ∀ r : ℝ, |r - q| < min (q - u) (q₀ - q) →
              Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice C.region r =
                Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice C.region q := by
            intro r hr
            have hmid : q - u = q₀ - q := by
              dsimp [q]
              linarith
            have hδ : min (q - u) (q₀ - q) = q - u := by
              rw [min_eq_left]
              linarith [hmid]
            rw [hδ] at hr
            have hrI : r ∈ Set.Ioo u q₀ := by
              rw [abs_lt] at hr
              exact ⟨by linarith [hr.1, min_le_left (q - u) (q₀ - q)],
                by linarith [hr.2, min_le_right (q - u) (q₀ - q)]⟩
            exact vertical_slice_constant_on_interval hq₀uv.1 hcell_neg hqI hrI
          let A : Set ℝ :=
            Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice C.region q
          let Y : Set ℝ := Complex.im '' S
          have hAeq : A = axisSection C.region Axis.vertical q := by
            ext y
            rfl
          have hAopen : IsOpen A := by
            dsimp [A, Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice]
            unfold Region.openCarrier Tiling.RationalPolygonal.PolygonalRegion.openCarrier
            apply isOpen_interior.preimage
            exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
          have hAfin : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion A := by
            exact (C.region.verticalSlice_finiteIntervals hqoff).1
          have hAfull : interior (closure (A + Y)) = Set.univ := by
            apply Set.eq_univ_of_forall
            intro y
            have hz : ((c + L.level - c : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ L.carrier := by
              rw [CompleteBoundaryLine.carrier, hLaxis]
              change (((c + L.level - c : ℝ) : ℂ) + (y : ℂ) * Complex.I).re = L.level
              simp
            obtain ⟨ρ, hρ, hcollar⟩ := hL.2 _ hz
            let ε : ℝ := min ((q₀ - u) / 4) (ρ / 2)
            have hε : 0 < ε := by
              dsimp [ε]
              exact lt_min (by linarith [hq₀uv.1]) (by linarith)
            let x : ℝ := c + L.level - c - ε
            have hxI : x - c ∈ Set.Ioo u q₀ := by
              dsimp [x, q₀]
              have hε' := min_le_left ((q₀ - u) / 4) (ρ / 2)
              constructor <;> linarith [hε', hq₀uv.1, hq₀uv.2]
            have hdist : dist ((x : ℂ) + (y : ℂ) * Complex.I)
                (((c + L.level - c : ℝ) : ℂ) + (y : ℂ) * Complex.I) < ρ := by
              rw [Complex.dist_eq]
              have hdiff : ((x : ℂ) + (y : ℂ) * Complex.I) -
                  (((c + L.level - c : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
                  ((-ε : ℝ) : ℂ) := by
                apply Complex.ext <;> simp [x]
              rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_neg,
                abs_of_pos hε]
              exact lt_of_le_of_lt (min_le_right ((q₀ - u) / 4) (ρ / 2)) (by linarith)
            have hxF : (x : ℂ) + (y : ℂ) * Complex.I ∈
                regularSupport C.region S := by
              have hside := hcollar _ hdist
              have hmem : L.level > (x : ℝ) := by
                dsimp [x]
                linarith
              have hiff := hside
              rw [hLaxis, hpositive] at hiff
              exact hiff.mpr (by simpa [Axis.transverseCoord] using hmem)
            have hreg := vertical_regularSupport_fiber_eq_local
              (K := C.region) (S := S) (c := c) (q := q)
              (delta := min (q - u) (q₀ - q)) (A := A) hAeq hc hconst
            have hxδ : x ∈ Set.Ioo (c + q - min (q - u) (q₀ - q))
                (c + q + min (q - u) (q₀ - q)) := by
              rw [Set.mem_Ioo]
              have hδ : min (q - u) (q₀ - q) = q - u := by
                dsimp [q]
                rw [min_eq_left]
                linarith
              rw [hδ]
              dsimp [q] at *
              constructor <;> linarith [hxI.1, hxI.2]
            have hyreg : y ∈ interior (closure (A + Y)) := by
              have := (show y ∈ {y : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈
                  regularSupport C.region S} from hxF)
              rw [hreg x hxδ] at this
              exact this
            exact hyreg
          have hAne : A.Nonempty := by
            by_contra hnone
            have hAempty : A = (∅ : Set ℝ) := Set.not_nonempty_iff_eq_empty.mp hnone
            have : A + Y = (∅ : Set ℝ) := by rw [hAempty, Set.empty_add]
            rw [this] at hAfull
            have hu : (Set.univ : Set ℝ).Nonempty := Set.univ_nonempty
            rw [← hAfull] at hu
            exact Set.not_nonempty_empty (by
              simpa only [closure_empty, interior_empty] using hu)
          have hA : GenericAxisSection C.region Axis.vertical A :=
            { transverse := q
              generic := by
                simpa [IntrinsicVertices.intrinsicCoordinateLevels,
                  Axis.swap, Axis.coord] using hqoff
              carrier_eq := hAeq
              finiteIntervals := hAfin
              isOpen := hAopen
              nonempty := hAne }
          exact hnoncolumn (fullGenericSection_forcesCenterColumn Axis.vertical hpack hne
            ⟨c, hc⟩ hcolumnable A Y hA rfl hAfull)
      | true =>
          let q : ℝ := (q₀ + v) / 2
          have hqI : q ∈ Set.Ioo q₀ v := by
            dsimp [q]
            constructor <;> linarith [hq₀uv.1, hq₀uv.2]
          have hqoff : q ∉ C.region.vertexFinset.image Complex.re :=
            hcell_pos q hqI
          have hconst : ∀ r : ℝ, |r - q| < min (q - q₀) (v - q) →
              Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice C.region r =
                Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice C.region q := by
            intro r hr
            have hrI : r ∈ Set.Ioo q₀ v := by
              rw [abs_lt] at hr
              exact ⟨by linarith [hr.1, min_le_left (q - q₀) (v - q)],
                by linarith [hr.2, min_le_right (q - q₀) (v - q)]⟩
            exact vertical_slice_constant_on_interval hq₀uv.2 hcell_pos hqI hrI
          let A : Set ℝ :=
            Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice C.region q
          let Y : Set ℝ := Complex.im '' S
          have hAeq : A = axisSection C.region Axis.vertical q := by
            ext y
            rfl
          have hAopen : IsOpen A := by
            dsimp [A, Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice]
            unfold Region.openCarrier Tiling.RationalPolygonal.PolygonalRegion.openCarrier
            apply isOpen_interior.preimage
            exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
          have hAfin : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion A := by
            exact (C.region.verticalSlice_finiteIntervals hqoff).1
          have hAfull : interior (closure (A + Y)) = Set.univ := by
            apply Set.eq_univ_of_forall
            intro y
            have hz : ((c + L.level - c : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈ L.carrier := by
              rw [CompleteBoundaryLine.carrier, hLaxis]
              change (((c + L.level - c : ℝ) : ℂ) + (y : ℂ) * Complex.I).re = L.level
              simp
            obtain ⟨ρ, hρ, hcollar⟩ := hL.2 _ hz
            let ε : ℝ := min ((v - q₀) / 4) (ρ / 2)
            have hε : 0 < ε := by
              dsimp [ε]
              exact lt_min (by linarith [hq₀uv.2]) (by linarith)
            let x : ℝ := c + L.level - c + ε
            have hxI : x - c ∈ Set.Ioo q₀ v := by
              dsimp [x, q₀]
              have hε' := min_le_left ((v - q₀) / 4) (ρ / 2)
              constructor <;> linarith [hε', hq₀uv.1, hq₀uv.2]
            have hdist : dist ((x : ℂ) + (y : ℂ) * Complex.I)
                (((c + L.level - c : ℝ) : ℂ) + (y : ℂ) * Complex.I) < ρ := by
              rw [Complex.dist_eq]
              have hdiff : ((x : ℂ) + (y : ℂ) * Complex.I) -
                  (((c + L.level - c : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
                  ((ε : ℝ) : ℂ) := by
                apply Complex.ext <;> simp [x]
              rw [hdiff, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos hε]
              exact lt_of_le_of_lt (min_le_right ((v - q₀) / 4) (ρ / 2)) (by linarith)
            have hxF : (x : ℂ) + (y : ℂ) * Complex.I ∈
                regularSupport C.region S := by
              have hside := hcollar _ hdist
              have hmem : L.level < (x : ℝ) := by
                dsimp [x]
                linarith
              have hiff := hside
              rw [hLaxis, hpositive] at hiff
              exact hiff.mpr (by simpa [Axis.transverseCoord] using hmem)
            have hreg := vertical_regularSupport_fiber_eq_local
              (K := C.region) (S := S) (c := c) (q := q)
              (delta := min (q - q₀) (v - q)) (A := A) hAeq hc hconst
            have hxδ : x ∈ Set.Ioo (c + q - min (q - q₀) (v - q))
                (c + q + min (q - q₀) (v - q)) := by
              rw [Set.mem_Ioo]
              have hδ : min (q - q₀) (v - q) = v - q := by
                dsimp [q]
                rw [min_eq_right]
                linarith
              rw [hδ]
              dsimp [q] at *
              constructor <;> linarith [hxI.1, hxI.2]
            have hyreg : y ∈ interior (closure (A + Y)) := by
              have := (show y ∈ {y : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈
                  regularSupport C.region S} from hxF)
              rw [hreg x hxδ] at this
              exact this
            exact hyreg
          have hAne : A.Nonempty := by
            by_contra hnone
            have hAempty : A = (∅ : Set ℝ) := Set.not_nonempty_iff_eq_empty.mp hnone
            have : A + Y = (∅ : Set ℝ) := by rw [hAempty, Set.empty_add]
            rw [this] at hAfull
            have hu : (Set.univ : Set ℝ).Nonempty := Set.univ_nonempty
            rw [← hAfull] at hu
            exact Set.not_nonempty_empty (by
              simpa only [closure_empty, interior_empty] using hu)
          have hA : GenericAxisSection C.region Axis.vertical A :=
            { transverse := q
              generic := by
                simpa [IntrinsicVertices.intrinsicCoordinateLevels,
                  Axis.swap, Axis.coord] using hqoff
              carrier_eq := hAeq
              finiteIntervals := hAfin
              isOpen := hAopen
              nonempty := hAne }
          exact hnoncolumn (fullGenericSection_forcesCenterColumn Axis.vertical hpack hne
            ⟨c, hc⟩ hcolumnable A Y hA rfl hAfull)
  | horizontal =>
      obtain ⟨c, hc⟩ := halign
      have hLh := completeBoundaryLine_axis_eq_of_bounded_local
        (axis := Axis.horizontal) (K := C.region) (S := S) ⟨c, hc⟩ hlocal L hL
      have hLaxis : L.axis = Axis.horizontal := hLh
      let V : Finset ℝ := C.region.vertexFinset.image Complex.im
      let q₀ : ℝ := L.level - c
      have hVclosed : IsClosed ((V.erase q₀ : Set ℝ)) := Finset.isClosed _
      have hVopen : IsOpen (((V.erase q₀ : Set ℝ))ᶜ) := hVclosed.isOpen_compl
      have hq₀mem : q₀ ∈ (((V.erase q₀ : Set ℝ))ᶜ) := by
        simp [V]
      obtain ⟨u, v, hq₀uv, huvsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hVopen.mem_nhds hq₀mem)
      have hcell_pos : ∀ r ∈ Set.Ioo q₀ v,
          r ∉ C.region.vertexFinset.image Complex.im := by
        intro r hr hrV
        have hr' : r ∈ (V.erase q₀ : Set ℝ) := by
          simp only [Finset.mem_coe, Finset.mem_erase]
          exact ⟨by linarith [hr.1, hq₀uv.1], by simpa [V] using hrV⟩
        exact (huvsub ⟨by linarith [hq₀uv.1, hr.1], hr.2⟩) hr'
      have hcell_neg : ∀ r ∈ Set.Ioo u q₀,
          r ∉ C.region.vertexFinset.image Complex.im := by
        intro r hr hrV
        have hr' : r ∈ (V.erase q₀ : Set ℝ) := by
          simp only [Finset.mem_coe, Finset.mem_erase]
          exact ⟨by linarith [hr.2, hq₀uv.2], by simpa [V] using hrV⟩
        exact (huvsub ⟨hr.1, by linarith [hr.2, hq₀uv.2]⟩) hr'
      cases hpositive : L.insideOnPositiveSide with
      | false =>
          let q : ℝ := (u + q₀) / 2
          have hqI : q ∈ Set.Ioo u q₀ := by
            dsimp [q]
            constructor <;> linarith [hq₀uv.1, hq₀uv.2]
          have hqoff : q ∉ C.region.vertexFinset.image Complex.im :=
            hcell_neg q hqI
          have hconst : ∀ r : ℝ, |r - q| < min (q - u) (q₀ - q) →
              Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region r =
                Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region q := by
            intro r hr
            have hmid : q - u = q₀ - q := by
              dsimp [q]
              linarith
            have hδ : min (q - u) (q₀ - q) = q - u := by
              rw [min_eq_left]
              linarith [hmid]
            rw [hδ] at hr
            have hrI : r ∈ Set.Ioo u q₀ := by
              rw [abs_lt] at hr
              exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
            exact horizontal_slice_constant_on_interval hq₀uv.1 hcell_neg
              (q := q) (r := r) hqI hrI
          let A : Set ℝ :=
            Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region q
          let Y : Set ℝ := Complex.re '' S
          have hAeq : A = axisSection C.region Axis.horizontal q := by
            ext x
            change Complex.mk x q ∈ C.region.openCarrier ↔
              (x : ℂ) + (q : ℂ) * Complex.I ∈ C.region.openCarrier
            have heq : Complex.mk x q =
                (x : ℂ) + (q : ℂ) * Complex.I := by
              apply Complex.ext <;> simp
            rw [heq]
          have hAopen : IsOpen A := by
            dsimp [A, Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice]
            apply C.region.openCarrier_regularOpen.1.preimage
            rw [show (fun x : ℝ ↦ Complex.mk x q) =
                (fun x : ℝ ↦ (x : ℂ) + (q : ℂ) * Complex.I) by
              funext x
              apply Complex.ext <;> simp]
            exact Complex.continuous_ofReal.add
              (continuous_const.mul continuous_const)
          have hAfin : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion A := by
            exact Foundations.GenericSlices.horizontalSlice_isFiniteIntervalRegion
              C.region hqoff
          have hAfull : interior (closure (A + Y)) = Set.univ := by
            apply Set.eq_univ_of_forall
            intro y
            have hz : (y : ℂ) + (c + L.level - c : ℂ) * Complex.I ∈ L.carrier := by
              simp [CompleteBoundaryLine.carrier, hLaxis, Axis.transverseCoord]
            obtain ⟨ρ, hρ, hcollar⟩ := hL.2 _ hz
            let ε : ℝ := min ((q₀ - u) / 4) (ρ / 2)
            have hε : 0 < ε := by
              dsimp [ε]
              exact lt_min (by linarith [hq₀uv.1]) (by linarith)
            let x : ℝ := c + L.level - c - ε
            have hxI : x - c ∈ Set.Ioo u q₀ := by
              have heps : ε ≤ (q₀ - u) / 4 := min_le_left _ _
              have hxform : x - c = q₀ - ε := by
                dsimp [x, q₀]
                ring
              constructor <;> linarith [heps, hq₀uv.1, hxform]
            have hdist : dist ((y : ℂ) + (x : ℂ) * Complex.I)
                ((y : ℂ) + (c + L.level - c : ℂ) * Complex.I) < ρ := by
              have hdiff : (y : ℂ) + (x : ℂ) * Complex.I -
                  ((y : ℂ) + (c + L.level - c : ℂ) * Complex.I) =
                    ((-ε : ℝ) : ℂ) * Complex.I := by
                apply Complex.ext <;> simp [x]
              rw [Complex.dist_eq, hdiff, norm_mul, Complex.norm_real,
                Real.norm_eq_abs, Complex.norm_I]
              have hepsrho : ε < ρ := lt_of_le_of_lt
                (show ε ≤ ρ / 2 from min_le_right _ _) (by linarith)
              simpa [abs_of_nonpos (neg_nonpos.mpr hε.le),
                abs_of_nonneg hε.le] using hepsrho
            have hxF : (y : ℂ) + (x : ℂ) * Complex.I ∈
                regularSupport C.region S := by
              have hside := hcollar _ hdist
              have hmem : L.level > (x : ℝ) := by
                dsimp [x]
                linarith
              have hiff := hside
              rw [hLaxis, hpositive] at hiff
              exact hiff.mpr (by simpa [Axis.transverseCoord] using hmem)
            have hreg := horizontal_regularSupport_fiber_eq_local
              (K := C.region) (S := S) (c := c) (q := q)
              (delta := min (q - u) (q₀ - q)) (A := A) (by rfl) hc hconst
            have hxδ : x ∈ Set.Ioo (c + q - min (q - u) (q₀ - q))
                (c + q + min (q - u) (q₀ - q)) := by
              have hmid : q - u = q₀ - q := by
                dsimp [q]
                linarith
              have hδ : min (q - u) (q₀ - q) = q - u := by
                rw [min_eq_left]
                linarith [hmid]
              rw [hδ]
              have heps : ε ≤ (q₀ - u) / 4 := min_le_left _ _
              have hxform : x - c = q₀ - ε := by
                dsimp [x, q₀]
                ring
              dsimp [q]
              constructor <;> linarith [heps, hq₀uv.1, hxform]
            have hyreg : y ∈ interior (closure (A + Y)) := by
              have hmem' : y ∈ {t : ℝ | (t : ℂ) +
                  (x : ℂ) * Complex.I ∈ regularSupport C.region S} := hxF
              rw [hreg x hxδ] at hmem'
              simpa [Y] using hmem'
            exact hyreg
          have hAne : A.Nonempty := by
            by_contra hnone
            have hAempty : A = (∅ : Set ℝ) := Set.not_nonempty_iff_eq_empty.mp hnone
            rw [hAempty, Set.empty_add, closure_empty, interior_empty] at hAfull
            have hu : (Set.univ : Set ℝ).Nonempty := Set.univ_nonempty
            rw [← hAfull] at hu
            exact Set.not_nonempty_empty (by
              simpa only [closure_empty, interior_empty] using hu)
          have hA : GenericAxisSection C.region Axis.horizontal A :=
            { transverse := q
              generic := by
                simpa [IntrinsicVertices.intrinsicCoordinateLevels,
                  Axis.swap, Axis.coord] using hqoff
              carrier_eq := hAeq
              finiteIntervals := hAfin
              isOpen := hAopen
              nonempty := hAne }
          exact hnoncolumn (fullGenericSection_forcesCenterColumn Axis.horizontal hpack hne
            ⟨c, hc⟩ hcolumnable A Y hA rfl hAfull)
      | true =>
          let q : ℝ := (q₀ + v) / 2
          have hqI : q ∈ Set.Ioo q₀ v := by
            dsimp [q]
            constructor <;> linarith [hq₀uv.1, hq₀uv.2]
          have hqoff : q ∉ C.region.vertexFinset.image Complex.im :=
            hcell_pos q hqI
          have hconst : ∀ r : ℝ, |r - q| < min (q - q₀) (v - q) →
              Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region r =
                Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region q := by
            intro r hr
            have hmid : q - q₀ = v - q := by
              dsimp [q]
              linarith
            have hδ : min (q - q₀) (v - q) = q - q₀ := by
              rw [min_eq_left]
              linarith [hmid]
            rw [hδ] at hr
            have hrI : r ∈ Set.Ioo q₀ v := by
              rw [abs_lt] at hr
              exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
            exact horizontal_slice_constant_on_interval hq₀uv.2 hcell_pos
              (q := q) (r := r) hqI hrI
          let A : Set ℝ :=
            Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region q
          let Y : Set ℝ := Complex.re '' S
          have hAeq : A = axisSection C.region Axis.horizontal q := by
            ext x
            change Complex.mk x q ∈ C.region.openCarrier ↔
              (x : ℂ) + (q : ℂ) * Complex.I ∈ C.region.openCarrier
            have heq : Complex.mk x q =
                (x : ℂ) + (q : ℂ) * Complex.I := by
              apply Complex.ext <;> simp
            rw [heq]
          have hAopen : IsOpen A := by
            dsimp [A, Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice]
            apply C.region.openCarrier_regularOpen.1.preimage
            rw [show (fun x : ℝ ↦ Complex.mk x q) =
                (fun x : ℝ ↦ (x : ℂ) + (q : ℂ) * Complex.I) by
              funext x
              apply Complex.ext <;> simp]
            exact Complex.continuous_ofReal.add
              (continuous_const.mul continuous_const)
          have hAfin : Tiling.AxisParallel.OneDimensional.IsFiniteIntervalRegion A := by
            exact Foundations.GenericSlices.horizontalSlice_isFiniteIntervalRegion
              C.region hqoff
          have hAfull : interior (closure (A + Y)) = Set.univ := by
            apply Set.eq_univ_of_forall
            intro y
            have hz : (y : ℂ) + (c + L.level - c : ℂ) * Complex.I ∈ L.carrier := by
              simp [CompleteBoundaryLine.carrier, hLaxis, Axis.transverseCoord]
            obtain ⟨ρ, hρ, hcollar⟩ := hL.2 _ hz
            let ε : ℝ := min ((v - q₀) / 4) (ρ / 2)
            have hε : 0 < ε := by
              dsimp [ε]
              exact lt_min (by linarith [hq₀uv.2]) (by linarith)
            let x : ℝ := c + L.level - c + ε
            have hxI : x - c ∈ Set.Ioo q₀ v := by
              have heps : ε ≤ (v - q₀) / 4 := min_le_left _ _
              have hxform : x - c = q₀ + ε := by
                dsimp [x, q₀]
                ring
              constructor <;> linarith [heps, hq₀uv.2, hxform]
            have hdist : dist ((y : ℂ) + (x : ℂ) * Complex.I)
                ((y : ℂ) + (c + L.level - c : ℂ) * Complex.I) < ρ := by
              have hdiff : (y : ℂ) + (x : ℂ) * Complex.I -
                  ((y : ℂ) + (c + L.level - c : ℂ) * Complex.I) =
                    ((ε : ℝ) : ℂ) * Complex.I := by
                apply Complex.ext <;> simp [x]
              rw [Complex.dist_eq, hdiff, norm_mul, Complex.norm_real,
                Real.norm_eq_abs, Complex.norm_I]
              have heps : ε ≤ ρ / 2 := min_le_right _ _
              simpa [abs_of_nonneg hε.le] using
                (lt_of_le_of_lt heps (by linarith : ρ / 2 < ρ))
            have hxF : (y : ℂ) + (x : ℂ) * Complex.I ∈
                regularSupport C.region S := by
              have hside := hcollar _ hdist
              have hmem : L.level < (x : ℝ) := by
                dsimp [x]
                linarith
              have hiff := hside
              rw [hLaxis, hpositive] at hiff
              exact hiff.mpr (by simpa [Axis.transverseCoord] using hmem)
            have hreg := horizontal_regularSupport_fiber_eq_local
              (K := C.region) (S := S) (c := c) (q := q)
              (delta := min (q - q₀) (v - q)) (A := A) (by rfl) hc hconst
            have hxδ : x ∈ Set.Ioo (c + q - min (q - q₀) (v - q))
                (c + q + min (q - q₀) (v - q)) := by
              have hmid : q - q₀ = v - q := by
                dsimp [q]
                linarith
              have hδ : min (q - q₀) (v - q) = q - q₀ := by
                rw [min_eq_left]
                linarith [hmid]
              rw [hδ]
              have heps : ε ≤ (v - q₀) / 4 := min_le_left _ _
              have hxform : x - c = q₀ + ε := by
                dsimp [x, q₀]
                ring
              dsimp [q]
              constructor <;> linarith [heps, hq₀uv.2, hxform]
            have hyreg : y ∈ interior (closure (A + Y)) := by
              have hmem' : y ∈ {t : ℝ | (t : ℂ) +
                  (x : ℂ) * Complex.I ∈ regularSupport C.region S} := hxF
              rw [hreg x hxδ] at hmem'
              simpa [Y] using hmem'
            exact hyreg
          have hAne : A.Nonempty := by
            by_contra hnone
            have hAempty : A = (∅ : Set ℝ) := Set.not_nonempty_iff_eq_empty.mp hnone
            rw [hAempty, Set.empty_add, closure_empty, interior_empty] at hAfull
            have hu : (Set.univ : Set ℝ).Nonempty := Set.univ_nonempty
            rw [← hAfull] at hu
            exact Set.not_nonempty_empty (by
              simpa only [closure_empty, interior_empty] using hu)
          have hA : GenericAxisSection C.region Axis.horizontal A :=
            { transverse := q
              generic := by
                simpa [IntrinsicVertices.intrinsicCoordinateLevels,
                  Axis.swap, Axis.coord] using hqoff
              carrier_eq := hAeq
              finiteIntervals := hAfin
              isOpen := hAopen
              nonempty := hAne }
          exact hnoncolumn (fullGenericSection_forcesCenterColumn Axis.horizontal hpack hne
            ⟨c, hc⟩ hcolumnable A Y hA rfl hAfull)




open Filter

private theorem finite_coloured_patch_subsequence
    {U : Set Tiling.Plane} (hU : U.Finite)
    (A B : ℕ → Set Tiling.Plane)
    (hA : ∀ n, A n ⊆ U) (hB : ∀ n, B n ⊆ U) :
    ∃ (φ : ℕ → ℕ) (P Q : Set Tiling.Plane), StrictMono φ ∧
      ∀ n, A (φ n) = P ∧ B (φ n) = Q := by
  classical
  let rangePair : Set (Set Tiling.Plane × Set Tiling.Plane) :=
    Set.range (fun n ↦ (A n, B n))
  have hpair : rangePair.Finite := by
    refine hU.finite_subsets.prod hU.finite_subsets |>.subset ?_
    rintro p ⟨n, rfl⟩
    exact ⟨hA n, hB n⟩
  let g : ℕ → rangePair := fun n ↦ ⟨(A n, B n), ⟨n, rfl⟩⟩
  let _ : Fintype rangePair := hpair.fintype
  obtain ⟨p, hp⟩ := Finite.exists_infinite_fiber g
  have hbounded : ∀ N : ℕ, ∃ n, N < n ∧ g n = p := by
    intro N
    by_contra hN
    have hfinite : (g ⁻¹' {p}).Finite := by
      apply Set.Finite.subset (Set.finite_Iic N)
      intro n hn
      by_contra hlt
      exact hN ⟨n, lt_of_not_ge hlt, hn⟩
    let _ : Fintype (g ⁻¹' {p}) := hfinite.fintype
    exact Infinite.false hp
  obtain ⟨φ, hφ, hφmem⟩ :=
    Nat.exists_strictMono_subsequence (P := fun n ↦ g n = p) (by
      intro N
      obtain ⟨n, hn, hgn⟩ := hbounded N
      exact ⟨n, hn, hgn⟩)
  refine ⟨φ, p.1.1, p.1.2, hφ, ?_⟩
  intro n
  have h := congrArg Subtype.val (hφmem n)
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

private theorem diagonal_coloured_patches
    (A B : ℕ → ℕ → Set Tiling.Plane) (U : ℕ → Set Tiling.Plane)
    (hU : ∀ k, (U k).Finite)
    (hA : ∀ k n, A n k ⊆ U k) (hB : ∀ k n, B n k ⊆ U k) :
    ∃ (ψ : ℕ → ℕ) (P Q : ℕ → Set Tiling.Plane), StrictMono ψ ∧
      (∀ k, ∀ᶠ n in atTop, A (ψ n) k = P k ∧ B (ψ n) k = Q k) := by
  classical
  have hsel : ∀ (k : ℕ) (f : ℕ → ℕ),
      ∃ (g : ℕ → ℕ) (p q : Set Tiling.Plane), StrictMono g ∧
        ∀ n, A (f (g n)) k = p ∧ B (f (g n)) k = q := by
    intro k f
    obtain ⟨g, p, q, hg, hgpq⟩ :=
      finite_coloured_patch_subsequence (hU k) (fun n ↦ A (f n) k)
        (fun n ↦ B (f n) k) (fun n ↦ hA k (f n)) (fun n ↦ hB k (f n))
    exact ⟨g, p, q, hg, hgpq⟩
  choose g p q hg hgpq using hsel
  let f : ℕ → ℕ → ℕ := fun k ↦
    Nat.rec (fun n ↦ n) (fun k fk n ↦ fk (g k fk n)) k
  have hf : ∀ k, StrictMono (f k) := by
    intro k
    induction k with
    | zero => exact strictMono_id
    | succ k ih =>
        rw [show f (k + 1) = fun n ↦ f k (g k (f k) n) by
          simp [f]
        ]
        exact ih.comp (hg k (f k))
  have hgg : ∀ k f n, n ≤ g k f n := by
    intro k f n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        exact (Nat.succ_le_succ ih).trans
          (Nat.succ_le_of_lt (hg k f (Nat.lt_succ_self n)))
  have hge : ∀ (k : ℕ) (n : ℕ), n ≤ f k n := by
    intro k
    induction k with
    | zero => intro n; exact le_rfl
    | succ k ih =>
        intro n
        exact (hgg k (f k) n).trans (ih (g k (f k) n))
  have hstage : ∀ k n, A (f (k + 1) n) k = p k (f k) ∧
      B (f (k + 1) n) k = q k (f k) := by
    intro k n
    simpa [f, Nat.rec] using hgpq k (f k) n
  have hfactor : ∀ {k m : ℕ}, k ≤ m → ∀ n, ∃ r, f m n = f k r ∧ n ≤ r := by
    intro k m hkm
    induction hkm with
    | refl => intro n; exact ⟨n, rfl, le_rfl⟩
    | @step m hkm ih =>
        intro n
        obtain ⟨r, hr, hnr⟩ := ih (g m (f m) n)
        refine ⟨r, ?_, (hgg m (f m) n).trans hnr⟩
        · simpa [f, Nat.rec] using hr
  let ψ : ℕ → ℕ := fun n ↦ f n n
  have hψ : StrictMono ψ := by
    intro i j hij
    obtain ⟨r, hr, hir⟩ := hfactor (k := i) (m := j) (Nat.le_of_lt hij) j
    have hlt : f i i < f i r := (hf i) (lt_of_lt_of_le hij hir)
    calc
      ψ i = f i i := rfl
      _ < f i r := hlt
      _ = f j j := hr.symm
      _ = ψ j := rfl
  refine ⟨ψ, fun k ↦ p k (f k), fun k ↦ q k (f k), hψ, ?_⟩
  intro k
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  obtain ⟨r, hr, _⟩ := hfactor (k := k + 1) (m := n) hn n
  rw [show ψ n = f n n by rfl, hr]
  exact hstage k r

private theorem flc_diagonal_coloured_patches
    {T : Set Tiling.Plane} (hT : HasFLC T)
    (t : ℕ → Tiling.Plane) (ht : ∀ n, t n ∈ T)
    (S : ℕ → Set Tiling.Plane) (hS : ∀ n, S n ⊆ T) :
    ∃ (ψ : ℕ → ℕ) (P Q : ℕ → Set Tiling.Plane), StrictMono ψ ∧
      (∀ k : ℕ, ∀ᶠ n in atTop,
        ((-t (ψ n)) +ᵥ T) ∩ Metric.closedBall 0 (k : ℝ) = P k ∧
        ((-t (ψ n)) +ᵥ S (ψ n)) ∩ Metric.closedBall 0 (k : ℝ) = Q k) := by
  let U : ℕ → Set Tiling.Plane := fun k ↦
    (T - T) ∩ Metric.closedBall 0 (k : ℝ)
  have hU : ∀ k, (U k).Finite := by
    intro k
    cases k with
    | zero =>
        exact (Set.finite_singleton (0 : Tiling.Plane)).subset (by
          intro x hx
          simpa [U] using hx.2)
    | succ k =>
        simpa [U] using hT.2 (k + 1) (by positivity)
  let A : ℕ → ℕ → Set Tiling.Plane := fun n k ↦
    ((-t n) +ᵥ T) ∩ Metric.closedBall 0 (k : ℝ)
  let B : ℕ → ℕ → Set Tiling.Plane := fun n k ↦
    ((-t n) +ᵥ S n) ∩ Metric.closedBall 0 (k : ℝ)
  have hA : ∀ k n, A n k ⊆ U k := by
    intro k n x hx
    rcases hx.1 with ⟨y, hy, rfl⟩
    refine ⟨⟨y, hy, t n, ht n, by simp [vadd_eq_add, sub_eq_add_neg, add_comm]⟩, hx.2⟩
  have hB : ∀ k n, B n k ⊆ U k := by
    intro k n x hx
    rcases hx.1 with ⟨y, hy, rfl⟩
    refine ⟨⟨y, hS n hy, t n, ht n,
      by simp [vadd_eq_add, sub_eq_add_neg, add_comm]⟩, hx.2⟩
  obtain ⟨ψ, P, Q, hψ, hPQ⟩ := diagonal_coloured_patches A B U hU hA hB
  refine ⟨ψ, P, Q, hψ, ?_⟩
  intro k
  filter_upwards [hPQ k] with n hn
  simpa [A, B] using hn

private theorem packing_limit_of_eventual_centres
    {K : Region} (S : ℕ → Set Tiling.Plane) (Slim : Set Tiling.Plane)
    (hpack : ∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (S n)))
    (hevent : ∀ s ∈ Slim, ∀ t ∈ Slim, s ≠ t →
      ∃ N, ∀ n ≥ N, s ∈ S n ∧ t ∈ S n) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements Slim) := by
  rw [isPacking_iff_openCarrier_disjoint]
  intro s hs t ht hst
  obtain ⟨N, hN⟩ := hevent s hs t ht hst
  have hdis := (isPacking_iff_openCarrier_disjoint K (S N)).mp (hpack N)
    (hN N le_rfl).1 (hN N le_rfl).2 hst
  exact hdis

private theorem diagonal_limit_of_nested_patches
    (F : ℕ → ℕ → Set Tiling.Plane) (Q : ℕ → Set Tiling.Plane)
    (hbound : ∀ n k, F n k ⊆ Metric.closedBall 0 (k : ℝ))
    (hrestrict : ∀ n k m, k ≤ m →
      F n m ∩ Metric.closedBall 0 (k : ℝ) = F n k)
    (hstable : ∀ k, ∀ᶠ n in atTop, F n k = Q k) :
    ∃ Slim : Set Tiling.Plane, ∀ k,
      ∀ᶠ n in atTop, F n k = Slim ∩ Metric.closedBall 0 (k : ℝ) := by
  let Slim : Set Tiling.Plane := ⋃ k, Q k
  have hQbound : ∀ k, Q k ⊆ Metric.closedBall 0 (k : ℝ) := by
    intro k x hx
    obtain ⟨n, hn⟩ := (hstable k).exists
    rw [← hn] at hx
    exact hbound n k hx
  have hQrestrict : ∀ k m, k ≤ m →
      Q m ∩ Metric.closedBall 0 (k : ℝ) = Q k := by
    intro k m hkm
    ext x
    constructor
    · rintro ⟨hx, hxball⟩
      obtain ⟨n, hnk, hnm⟩ := (hstable k).and (hstable m) |>.exists
      rw [← hnm] at hx
      rw [← hnk]
      rw [← hrestrict n k m hkm]
      exact ⟨hx, hxball⟩
    · intro hx
      have hxball : x ∈ Metric.closedBall (0 : Tiling.Plane) (k : ℝ) :=
        hQbound k hx
      obtain ⟨n, hnk, hnm⟩ := (hstable k).and (hstable m) |>.exists
      rw [← hnk] at hx
      rw [← hnm]
      rw [hrestrict n k m hkm]
      exact hx
  refine ⟨Slim, ?_⟩
  intro k
  filter_upwards [hstable k] with n hnk
  ext x
  constructor
  · intro hx
    have hxQ : x ∈ Q k := by
      rw [← hnk]
      exact hx
    refine ⟨?_, hQbound k hxQ⟩
    change x ∈ ⋃ m, Q m
    exact Set.mem_iUnion.mpr ⟨k, hxQ⟩
  · rintro ⟨hxSlim, hxball⟩
    change x ∈ ⋃ m, Q m at hxSlim
    rcases Set.mem_iUnion.mp hxSlim with ⟨m, hxm⟩
    by_cases hkm : k ≤ m
    · have : x ∈ Q k := by
        rw [← hQrestrict k m hkm]
        exact ⟨hxm, hxball⟩
      rw [hnk]
      exact this
    · have hmk : m ≤ k := Nat.le_of_lt (lt_of_not_ge hkm)
      have hsub : Q m ⊆ Q k := by
        intro y hy
        have hy' : y ∈ Q k ∩ Metric.closedBall 0 (m : ℝ) := by
          rw [hQrestrict m k hmk]
          exact hy
        exact hy'.1
      rw [hnk]
      exact hsub hxm

private theorem flc_pointed_limit_exists
    {T : Set Tiling.Plane} (hT : HasFLC T)
    (t : ℕ → Tiling.Plane) (ht : ∀ n, t n ∈ T)
    (S : ℕ → Set Tiling.Plane) (hS : ∀ n, S n ⊆ T) :
    ∃ (ψ : ℕ → ℕ) (Slim : Set Tiling.Plane), StrictMono ψ ∧
      (∀ k : ℕ, ∀ᶠ n in atTop,
        ((-t (ψ n)) +ᵥ S (ψ n)) ∩ Metric.closedBall 0 (k : ℝ) =
          Slim ∩ Metric.closedBall 0 (k : ℝ)) := by
  obtain ⟨ψ, P, Q, hψ, hPQ⟩ := flc_diagonal_coloured_patches hT t ht S hS
  let F : ℕ → ℕ → Set Tiling.Plane := fun n k ↦
    ((-t (ψ n)) +ᵥ S (ψ n)) ∩ Metric.closedBall 0 (k : ℝ)
  have hbound : ∀ n k, F n k ⊆ Metric.closedBall 0 (k : ℝ) := by
    intro n k x hx
    exact hx.2
  have hrestrict : ∀ n k m, k ≤ m →
      F n m ∩ Metric.closedBall 0 (k : ℝ) = F n k := by
    intro n k m hkm
    have hball : Metric.closedBall (0 : Tiling.Plane) (k : ℝ) ⊆
        Metric.closedBall 0 (m : ℝ) :=
      Metric.closedBall_subset_closedBall (by exact_mod_cast hkm)
    ext x
    constructor
    · rintro ⟨⟨hx, _⟩, hxk⟩
      exact ⟨hx, hxk⟩
    · intro hx
      exact ⟨⟨hx.1, hball hx.2⟩, hx.2⟩
  have hstable : ∀ k, ∀ᶠ n in atTop, F n k = Q k := by
    intro k
    filter_upwards [hPQ k] with n hn
    simpa [F] using hn.2
  obtain ⟨Slim, hSlim⟩ := diagonal_limit_of_nested_patches F Q hbound hrestrict hstable
  exact ⟨ψ, Slim, hψ, hSlim⟩

private theorem packing_translate
    {K : Region} {S : Set Tiling.Plane} (hS :
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S)) (u : Tiling.Plane) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (u +ᵥ S)) := by
  rw [isPacking_iff_openCarrier_disjoint]
  intro x hx y hy hxy
  obtain ⟨x₀, hx₀, rfl⟩ := Set.mem_vadd_set.mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := Set.mem_vadd_set.mp hy
  have hxy₀ : x₀ ≠ y₀ := by
    intro h
    apply hxy
    simp [h]
  have hdis := (isPacking_iff_openCarrier_disjoint K S).mp hS hx₀ hy₀ hxy₀
  change Disjoint (x₀ +ᵥ K.openCarrier) (y₀ +ᵥ K.openCarrier) at hdis
  change Disjoint ((u +ᵥ x₀) +ᵥ K.openCarrier)
    ((u +ᵥ y₀) +ᵥ K.openCarrier)
  rw [Set.disjoint_left] at hdis ⊢
  intro z hz₁ hz₂
  refine @hdis (-u +ᵥ z) ?_ ?_
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz₁ ⊢
    simpa [vadd_eq_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz₁
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz₂ ⊢
    simpa [vadd_eq_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz₂

private theorem flc_packing_pointed_limit
    {K : Region} {T : Set Tiling.Plane} (hT : HasFLC T)
    (t : ℕ → Tiling.Plane) (ht : ∀ n, t n ∈ T)
    (S : ℕ → Set Tiling.Plane) (hS : ∀ n, S n ⊆ T)
    (hpack : ∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (S n))) :
    ∃ (ψ : ℕ → ℕ) (Slim : Set Tiling.Plane), StrictMono ψ ∧
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements Slim) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop,
        ((-t (ψ n)) +ᵥ S (ψ n)) ∩ Metric.closedBall 0 (k : ℝ) =
          Slim ∩ Metric.closedBall 0 (k : ℝ)) := by
  obtain ⟨ψ, Slim, hψ, hlocal⟩ := flc_pointed_limit_exists hT t ht S hS
  let S' : ℕ → Set Tiling.Plane := fun n ↦ (-t (ψ n)) +ᵥ S (ψ n)
  have hpack' : ∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (S' n)) := by
    intro n
    exact packing_translate (hpack (ψ n)) (-t (ψ n))
  have hevent : ∀ s ∈ Slim, ∀ t ∈ Slim, s ≠ t →
      ∃ N, ∀ n ≥ N, s ∈ S' n ∧ t ∈ S' n := by
    intro s hs t ht hst
    obtain ⟨k, hk⟩ := exists_nat_ge (max ‖s‖ ‖t‖)
    have hsball : s ∈ Metric.closedBall (0 : Tiling.Plane) (k : ℝ) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (le_max_left _ _).trans hk
    have htball : t ∈ Metric.closedBall (0 : Tiling.Plane) (k : ℝ) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (le_max_right _ _).trans hk
    obtain ⟨N, hN⟩ := (eventually_atTop.1 (hlocal k))
    refine ⟨N, ?_⟩
    intro n hn
    have heq := hN n hn
    have hs' : s ∈ S' n := by
      have hmem : s ∈ Slim ∩ Metric.closedBall 0 (k : ℝ) := ⟨hs, hsball⟩
      rw [← heq] at hmem
      exact hmem.1
    have ht' : t ∈ S' n := by
      have hmem : t ∈ Slim ∩ Metric.closedBall 0 (k : ℝ) := ⟨ht, htball⟩
      rw [← heq] at hmem
      exact hmem.1
    exact ⟨hs', ht'⟩
  have hSlimPack := packing_limit_of_eventual_centres S' Slim hpack' hevent
  refine ⟨ψ, Slim, hψ, hSlimPack, ?_⟩
  intro k
  simpa [S'] using hlocal k

private theorem openUnion_eventually_eq_on_window
    {K : Region} (S : ℕ → Set Tiling.Plane) (Slim Q : Set Tiling.Plane) (k : ℕ)
    (hrel : ∀ x ∈ Q, ∀ s : Tiling.Plane,
      x ∈ s +ᵥ K.openCarrier → s ∈ Metric.closedBall 0 (k : ℝ))
    (hrelLim : ∀ x ∈ Q, ∀ s : Tiling.Plane,
      x ∈ s +ᵥ K.openCarrier → s ∈ Metric.closedBall 0 (k : ℝ))
    (hpatch : ∀ᶠ n in atTop,
      S n ∩ Metric.closedBall 0 (k : ℝ) =
        Slim ∩ Metric.closedBall 0 (k : ℝ)) :
    ∀ᶠ n in atTop,
      openUnion K (S n) ∩ Q = openUnion K Slim ∩ Q := by
  filter_upwards [hpatch] with n hn
  ext x
  constructor
  · rintro ⟨hxU, hxQ⟩
    refine ⟨?_, hxQ⟩
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier] at hxU ⊢
    rw [Set.mem_iUnion] at hxU ⊢
    obtain ⟨s, hxs⟩ := hxU
    have hsball := hrel x hxQ (s : Tiling.Plane) hxs
    have hsSlim : (s : Tiling.Plane) ∈ Slim := by
      have : (s : Tiling.Plane) ∈ Slim ∩ Metric.closedBall 0 (k : ℝ) := by
        rw [← hn]
        exact ⟨s.property, hsball⟩
      exact this.1
    exact ⟨⟨(s : Tiling.Plane), hsSlim⟩, hxs⟩
  · rintro ⟨hxU, hxQ⟩
    refine ⟨?_, hxQ⟩
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier] at hxU ⊢
    rw [Set.mem_iUnion] at hxU ⊢
    obtain ⟨s, hxs⟩ := hxU
    have hsball := hrelLim x hxQ (s : Tiling.Plane) hxs
    have hsS : (s : Tiling.Plane) ∈ S n := by
      have : (s : Tiling.Plane) ∈ S n ∩ Metric.closedBall 0 (k : ℝ) := by
        rw [hn]
        exact ⟨s.property, hsball⟩
      exact this.1
    exact ⟨⟨(s : Tiling.Plane), hsS⟩, hxs⟩

private theorem bounded_openCarrier_window
    {K : Region} {Q : Set Tiling.Plane}
    (hQ : Bornology.IsBounded Q) :
    ∃ k : ℕ, ∀ x ∈ Q, ∀ s : Tiling.Plane,
      x ∈ s +ᵥ K.openCarrier →
        s ∈ Metric.closedBall 0 (k : ℝ) := by
  have hK : Bornology.IsBounded K.openCarrier := by
    apply K.isPolygonal.isBounded.subset
    intro y hy
    exact interior_subset (by
      simpa [Region.openCarrier,
        Tiling.RationalPolygonal.PolygonalRegion.openCarrier] using hy)
  obtain ⟨Rq, hRq⟩ := hQ.subset_closedBall (0 : Tiling.Plane)
  obtain ⟨Rk, hRk⟩ := hK.subset_closedBall (0 : Tiling.Plane)
  let Rq' := max Rq 0
  let Rk' := max Rk 0
  obtain ⟨k, hk⟩ := exists_nat_ge (Rq' + Rk')
  refine ⟨k, ?_⟩
  intro x hx s hs
  obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.mp hs
  have hx' : ‖x‖ ≤ Rq' := by
    have hx0 := hRq hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx0
    exact hx0.trans (le_max_left _ _)
  have hy' : ‖y‖ ≤ Rk' := by
    have hy0 := hRk hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy0
    exact hy0.trans (le_max_left _ _)
  have hs_norm : ‖s‖ ≤ Rq' + Rk' := by
    have hs_eq : s = x - y := by
      calc
        s = (s + y) - y := by abel
        _ = x - y := by
          simpa [vadd_eq_add] using congrArg (fun z ↦ z - y) hxy
    rw [hs_eq]
    exact (norm_sub_le x y).trans (add_le_add hx' hy')
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hs_norm.trans hk

private theorem regularized_local_transfer
    {D E : Set Tiling.Plane} {a w : Tiling.Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (ha : a ∈ Metric.ball w (ρ / 2))
    (hDE : ∀ z ∈ Metric.ball w ρ, z ∈ D ↔ z ∈ E) :
    a ∈ interior (closure D) ↔ a ∈ interior (closure E) := by
  have hclosure_local : ∀ z ∈ Metric.ball w (ρ / 2),
      z ∈ closure D ↔ z ∈ closure E := by
    intro z hz
    have hlocal : D =ᶠ[𝓝 z] E := by
      have hball : Metric.ball w (ρ / 2) ∈ 𝓝 z :=
        Metric.isOpen_ball.mem_nhds hz
      filter_upwards [hball] with y hy
      have hybig : y ∈ Metric.ball w ρ := by
        rw [Metric.mem_ball] at hy ⊢
        linarith [dist_triangle w y z, dist_comm y z]
      exact propext (hDE y hybig)
    rw [mem_closure_iff_frequently, mem_closure_iff_frequently]
    constructor
    · intro hf
      exact (hf.and_eventually hlocal).mono fun y hy ↦ Eq.mp hy.2 hy.1
    · intro hf
      exact (hf.and_eventually hlocal).mono fun y hy ↦ Eq.mpr hy.2 hy.1
  rw [mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds]
  constructor
  · intro hD
    have hball : Metric.ball w (ρ / 2) ∈ 𝓝 a :=
      Metric.isOpen_ball.mem_nhds ha
    exact Filter.mem_of_superset (Filter.inter_mem hD hball) fun z hz ↦
      (hclosure_local z hz.2).mp hz.1
  · intro hE
    have hball : Metric.ball w (ρ / 2) ∈ 𝓝 a :=
      Metric.isOpen_ball.mem_nhds ha
    exact Filter.mem_of_superset (Filter.inter_mem hE hball) fun z hz ↦
      (hclosure_local z hz.2).mpr hz.1

private theorem properVertex_regularSupport_local_transfer
    {K : Region} {S Slim : Set Tiling.Plane} {a w : Tiling.Plane} {ρ : ℝ}
    (hρ : 0 < ρ) (ha : a ∈ Metric.ball w (ρ / 2))
    (hraw : ∀ z ∈ Metric.ball w (2 * ρ),
      z ∈ openUnion K S ↔ z ∈ openUnion K Slim)
    (hx : IsProperVertex (regularSupport K S) a) :
    IsProperVertex (regularSupport K Slim) a := by
  have heq : regularSupport K S =ᶠ[nhds a] regularSupport K Slim := by
    have habig : a ∈ Metric.ball w ρ := by
      rw [Metric.mem_ball] at ha ⊢
      linarith
    have hball : Metric.ball w ρ ∈ nhds a :=
      Metric.isOpen_ball.mem_nhds habig
    filter_upwards [hball] with z hz
    have hreg := regularized_local_transfer
      (D := openUnion K S) (E := openUnion K Slim)
      (a := z) (w := w) (ρ := 2 * ρ) (by linarith)
      (by
        convert hz using 1
        ring_nf) hraw
    change (z ∈ regularSupport K S) = (z ∈ regularSupport K Slim)
    exact propext (by simpa only [regularSupport, Tiling.Polygonal.regularSupport,
      ← openUnion.eq_def] using hreg)
  exact (isProperVertex_iff_of_eventuallyEq heq).mp hx


private theorem finite_vertex_subsequence
    {K : Region} (v : ℕ → Tiling.Plane) (hv : ∀ n, v n ∈ K.vertices) :
    ∃ (φ : ℕ → ℕ) (w : Tiling.Plane), StrictMono φ ∧
      ∀ n, v (φ n) = w := by
  classical
  let g : ℕ → ↥K.vertices := fun n ↦ ⟨v n, hv n⟩
  have hfinite : K.vertices.Finite := by
    rw [← K.coe_vertexFinset]
    exact K.vertexFinset.finite_toSet
  let _ : Fintype ↥K.vertices := hfinite.fintype
  obtain ⟨w, hw⟩ := Finite.exists_infinite_fiber g
  obtain ⟨φ, hφ, hφmem⟩ := Nat.exists_strictMono_subsequence
      (P := fun n ↦ g n = w) (by
    intro N
    by_contra hN
    have hfinite : (g ⁻¹' {w}).Finite := by
      refine (Set.finite_Iic N).subset ?_
      intro n hn
      by_contra hlt
      exact hN ⟨n, lt_of_not_ge hlt, hn⟩
    let _ : Fintype (g ⁻¹' {w}) := hfinite.fintype
    exact Infinite.false hw)
  exact ⟨φ, w.1, hφ, fun n ↦ congrArg Subtype.val (hφmem n)⟩

private theorem properVertex_eventually_iff_of_patches
    {K : Region} (S : ℕ → Set Tiling.Plane) (Slim : Set Tiling.Plane)
    (hpatch : ∀ k : ℕ, ∀ᶠ n in atTop,
      S n ∩ Metric.closedBall 0 (k : ℝ) =
        Slim ∩ Metric.closedBall 0 (k : ℝ)) (a : Tiling.Plane) :
    ∀ᶠ n in atTop,
      a ∈ properVertices (regularSupport K (S n)) ↔
        a ∈ properVertices (regularSupport K Slim) := by
  obtain ⟨k, hk⟩ := bounded_openCarrier_window (K := K)
    (Q := Metric.ball a 2) (Metric.isBounded_ball)
  have hraw := openUnion_eventually_eq_on_window S Slim (Metric.ball a 2) k hk hk
    (hpatch k)
  filter_upwards [hraw] with n hn
  have heq : ∀ z ∈ Metric.ball a 2,
      z ∈ openUnion K (S n) ↔ z ∈ openUnion K Slim := by
    intro z hz
    have hm := Set.ext_iff.mp hn z
    simpa only [Set.mem_inter_iff, hz, and_true] using hm
  constructor
  · exact properVertex_regularSupport_local_transfer (w := a) (ρ := 1) (by norm_num)
      (by simp) (by simpa using heq)
  · apply properVertex_regularSupport_local_transfer (w := a) (ρ := 1) (by norm_num)
      (by simp)
    intro z hz
    exact (heq z (by simpa using hz)).symm

private theorem centre_eventually_mem_of_patches
    (S : ℕ → Set Tiling.Plane) (Slim : Set Tiling.Plane)
    (hpatch : ∀ k : ℕ, ∀ᶠ n in atTop,
      S n ∩ Metric.closedBall 0 (k : ℝ) =
        Slim ∩ Metric.closedBall 0 (k : ℝ))
    {s : Tiling.Plane} (hs : s ∈ Slim) :
    ∀ᶠ n in atTop, s ∈ S n := by
  obtain ⟨k, hk⟩ := exists_nat_ge ‖s‖
  have hball : s ∈ Metric.closedBall (0 : Tiling.Plane) (k : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hk
  filter_upwards [hpatch k] with n hn
  have hm : s ∈ Slim ∩ Metric.closedBall 0 (k : ℝ) := ⟨hs, hball⟩
  rw [← hn] at hm
  exact hm.1

private theorem zero_mem_limit_of_patches
    (S : ℕ → Set Tiling.Plane) (Slim : Set Tiling.Plane)
    (hpatch : ∀ k : ℕ, ∀ᶠ n in atTop,
      S n ∩ Metric.closedBall 0 (k : ℝ) =
        Slim ∩ Metric.closedBall 0 (k : ℝ))
    (hzero : ∀ n, (0 : Tiling.Plane) ∈ S n) :
    (0 : Tiling.Plane) ∈ Slim := by
  obtain ⟨n, hn⟩ := (hpatch 0).exists
  simp only [Nat.cast_zero] at hn
  have hm : (0 : Tiling.Plane) ∈ S n ∩ Metric.closedBall 0 (0 : ℝ) := by
    exact ⟨hzero n, by simp⟩
  rw [hn] at hm
  exact hm.1

private theorem aligned_limit_of_patches
    (S : ℕ → Set Tiling.Plane) (Slim : Set Tiling.Plane)
    (hpatch : ∀ k : ℕ, ∀ᶠ n in atTop,
      S n ∩ Metric.closedBall 0 (k : ℝ) =
        Slim ∩ Metric.closedBall 0 (k : ℝ))
    (axis : Axis) (halign : ∀ n s, s ∈ S n → axis.transverseCoord s = 0) :
    ∀ s ∈ Slim, axis.transverseCoord s = 0 := by
  intro s hs
  obtain ⟨n, hn⟩ := (centre_eventually_mem_of_patches S Slim hpatch hs).exists
  exact halign n s hn

private theorem no_outerWall_properVertex_of_patches
    {K : Region} (S : ℕ → Set Tiling.Plane) (Slim : Set Tiling.Plane)
    (hpatch : ∀ k : ℕ, ∀ᶠ n in atTop,
      S n ∩ Metric.closedBall 0 (k : ℝ) =
        Slim ∩ Metric.closedBall 0 (k : ℝ))
    (axis : Axis) (wall : ℝ) (anchor : Tiling.Plane)
    (hbad : ∀ n z, z ∈ properVertices (regularSupport K (S n)) →
      axis.transverseCoord z = wall → ¬ dist anchor z < (n : ℝ)) :
    ∀ z ∈ properVertices (regularSupport K Slim),
      axis.transverseCoord z ≠ wall := by
  intro z hz hwall
  have hproper := properVertex_eventually_iff_of_patches (K := K) S Slim hpatch z
  obtain ⟨N, hN⟩ := eventually_atTop.mp hproper
  obtain ⟨M, hM⟩ := exists_nat_gt (dist anchor z)
  let n := max N M
  have hn : N ≤ n := le_max_left _ _
  have hz' := (hN n hn).mpr hz
  apply hbad n z hz' hwall
  exact hM.trans_le (by exact_mod_cast (le_max_right N M))

private theorem transverseCoord_add_local (axis : Axis) (x y : Tiling.Plane) :
    axis.transverseCoord (x + y) = axis.transverseCoord x + axis.transverseCoord y := by
  cases axis <;> rfl

private theorem extremal_vertex_translate_back
    {K : Region} {S : Set Tiling.Plane} (axis : Axis)
    (u z : Tiling.Plane)
    (hz : z ∈ properVertices (regularSupport K (u +ᵥ S)))
    (hmin : ∀ y ∈ properVertices (regularSupport K (u +ᵥ S)),
      axis.transverseCoord z ≤ axis.transverseCoord y) :
    -u + z ∈ properVertices (regularSupport K S) ∧
      ∀ y ∈ properVertices (regularSupport K S),
        axis.transverseCoord (-u + z) ≤ axis.transverseCoord y := by
  have hproper : properVertices (regularSupport K (u +ᵥ S)) =
      u +ᵥ properVertices (regularSupport K S) := by
    rw [regularSupport_vadd, properVertices_vadd_eq]
  have hz' : -u + z ∈ properVertices (regularSupport K S) := by
    rw [hproper, Set.mem_vadd_set_iff_neg_vadd_mem] at hz
    exact hz
  refine ⟨hz', ?_⟩
  intro y hy
  have hy' : u + y ∈ properVertices (regularSupport K (u +ᵥ S)) := by
    rw [hproper]
    exact Set.mem_vadd_set.mpr ⟨y, hy, rfl⟩
  have hm := hmin (u + y) hy'
  rw [transverseCoord_add_local] at hm
  have hsub : axis.transverseCoord (-u + z) =
      -axis.transverseCoord u + axis.transverseCoord z := by
    cases axis <;> simp [Axis.transverseCoord]
  rw [hsub]
  linarith

private theorem normalized_pointed_limit
    {K : Region} {T : Set Tiling.Plane} (hT : HasFLC T)
    (S : ℕ → Set Tiling.Plane) (t : ℕ → Tiling.Plane) (anchor : Tiling.Plane)
    (hS : ∀ n, S n ⊆ T) (ht : ∀ n, t n ∈ S n)
    (hpack : ∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (S n)))
    (axis : Axis) (halign : ∀ n, ∃ c, ∀ s ∈ S n, axis.transverseCoord s = c)
    (hanchor : ∀ n, anchor + t n ∈ properVertices (regularSupport K (S n))) :
    ∃ (ψ : ℕ → ℕ) (Slim : Set Tiling.Plane), StrictMono ψ ∧
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements Slim) ∧
      (0 : Tiling.Plane) ∈ Slim ∧
      (∀ s ∈ Slim, axis.transverseCoord s = 0) ∧
      anchor ∈ properVertices (regularSupport K Slim) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop,
        ((-t (ψ n)) +ᵥ S (ψ n)) ∩ Metric.closedBall 0 (k : ℝ) =
          Slim ∩ Metric.closedBall 0 (k : ℝ)) := by
  obtain ⟨ψ, Slim, hψ, hpackLim, hpatch⟩ := flc_packing_pointed_limit hT t
    (fun n ↦ hS n (ht n)) S hS hpack
  let Sn : ℕ → Set Tiling.Plane := fun n ↦ (-t (ψ n)) +ᵥ S (ψ n)
  have hpatch' : ∀ k : ℕ, ∀ᶠ n in atTop,
      Sn n ∩ Metric.closedBall 0 (k : ℝ) =
        Slim ∩ Metric.closedBall 0 (k : ℝ) := hpatch
  have hzero : ∀ n, (0 : Tiling.Plane) ∈ Sn n := by
    intro n
    exact Set.mem_vadd_set.mpr ⟨t (ψ n), ht (ψ n), by simp⟩
  have halign' : ∀ n s, s ∈ Sn n → axis.transverseCoord s = 0 := by
    intro n s hs
    obtain ⟨c, hc⟩ := halign (ψ n)
    obtain ⟨s₀, hs₀, rfl⟩ := Set.mem_vadd_set.mp hs
    have hc₀ := hc s₀ hs₀
    have hct := hc (t (ψ n)) (ht (ψ n))
    cases axis <;> simp_all [Axis.transverseCoord, vadd_eq_add]
  have hanchorn : ∀ n, anchor ∈ properVertices (regularSupport K (Sn n)) := by
    intro n
    rw [regularSupport_vadd, properVertices_vadd_eq]
    exact Set.mem_vadd_set.mpr ⟨anchor + t (ψ n), hanchor (ψ n), by
      simp [vadd_eq_add, add_comm]⟩
  obtain ⟨n, hn⟩ := (properVertex_eventually_iff_of_patches (K := K) Sn Slim hpatch' anchor).exists
  exact ⟨ψ, Slim, hψ, hpackLim, zero_mem_limit_of_patches Sn Slim hpatch' hzero,
    aligned_limit_of_patches Sn Slim hpatch' axis halign', (hn.mp (hanchorn n)), hpatch⟩

private structure OuterVerticalCollar (K : Region) (A : Set ℝ) where
  wall : ℝ
  right : ℝ
  lower : ℝ
  upper : ℝ
  cell_mem : Set.Icc wall right ×ℂ Set.Icc lower upper ∈
    (IntrinsicVertices.intrinsicGridPieces K : Set (Set Tiling.Plane))
  wall_lt_right : wall < right
  lower_lt_upper : lower < upper
  first : ∀ r ∈ (IntrinsicVertices.intrinsicGridPieces K : Set (Set Tiling.Plane)),
    ∃ (xp yp : ℝ × ℝ),
      r = IntrinsicVertices.closedAxisBox xp.1 xp.2 yp.1 yp.2 ∧ wall ≤ xp.1
  exterior_empty : ∀ z : Tiling.Plane, z.re < wall → z ∉ K.openCarrier
  transverse : ℝ
  transverse_mem : transverse ∈ Set.Ioo wall right
  generic : transverse ∉ (IntrinsicVertices.intrinsicCoordinateLevels K Axis.horizontal : Set ℝ)
  carrier_eq : A = Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K transverse
  finiteIntervals : OneDimensional.IsFiniteIntervalRegion A
  isOpen : IsOpen A
  nonempty : A.Nonempty
  delta : ℝ
  delta_pos : 0 < delta
  locally_constant : ∀ r : ℝ, |r - transverse| < delta →
    Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r =
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K transverse
  cell_generic : ∀ r ∈ Set.Ioo wall right,
    r ∉ K.vertexFinset.image Complex.re
  cell_constant : ∀ r ∈ Set.Ioo wall right,
    Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r =
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K transverse

private theorem outerVerticalCollar_construct (K : Region) :
    ∃ A : Set ℝ, Nonempty (OuterVerticalCollar K A) := by
  classical
  obtain ⟨R, hR, _⟩ := IntrinsicVertices.exists_intrinsicGridRectangulation K
  have hPne : R.pieces.Nonempty := by
    obtain ⟨z, hz⟩ := K.nonempty
    rw [← R.sUnion_eq] at hz
    obtain ⟨r, hr, _⟩ := hz
    exact ⟨r, hr⟩
  have hdata_of (s : Set Tiling.Plane) (hs : s ∈ (R.pieces : Set (Set Tiling.Plane))) :
      ∃ (xp yp : ℝ × ℝ), xp ∈ IntrinsicVertices.consecutiveLevelPairs
          (IntrinsicVertices.intrinsicCoordinateLevels K Axis.horizontal) ∧
        yp ∈ IntrinsicVertices.consecutiveLevelPairs
          (IntrinsicVertices.intrinsicCoordinateLevels K Axis.vertical) ∧
        interior (IntrinsicVertices.closedAxisBox xp.1 xp.2 yp.1 yp.2) ⊆ K.openCarrier ∧
        s = IntrinsicVertices.closedAxisBox xp.1 xp.2 yp.1 yp.2 := by
    exact IntrinsicVertices.mem_intrinsicGridPieces K (by simpa [hR] using hs)
  let leftOf : Set Tiling.Plane → ℝ := fun r =>
    if hr : r ∈ (R.pieces : Set (Set Tiling.Plane)) then
      (Classical.choose (hdata_of r hr)).1 else 0
  have hfin : ((R.pieces : Set (Set Tiling.Plane))).Finite := R.pieces.finite_toSet
  have hPneSet : (R.pieces : Set (Set Tiling.Plane)).Nonempty := by
    simpa using hPne
  obtain ⟨r, hr, hmin⟩ := Set.exists_min_image (R.pieces : Set (Set Tiling.Plane))
    leftOf hfin hPneSet
  let hdataR := hdata_of r hr
  let xp : ℝ × ℝ := Classical.choose hdataR
  let hdataR' := Classical.choose_spec hdataR
  let yp : ℝ × ℝ := Classical.choose hdataR'
  have hdata := Classical.choose_spec hdataR'
  obtain ⟨hxp, hyp, hinside, hrbox⟩ := hdata
  have hxp' : xp ∈ ((IntrinsicVertices.intrinsicCoordinateLevels K Axis.horizontal ×ˢ
      IntrinsicVertices.intrinsicCoordinateLevels K Axis.horizontal).filter
        (fun p => p.1 < p.2 ∧ ∀ z ∈ IntrinsicVertices.intrinsicCoordinateLevels K Axis.horizontal,
          ¬(p.1 < z ∧ z < p.2))) := by
    simpa [IntrinsicVertices.consecutiveLevelPairs, xp, yp] using hxp
  have hyp' : yp ∈ ((IntrinsicVertices.intrinsicCoordinateLevels K Axis.vertical ×ˢ
      IntrinsicVertices.intrinsicCoordinateLevels K Axis.vertical).filter
        (fun p => p.1 < p.2 ∧ ∀ z ∈ IntrinsicVertices.intrinsicCoordinateLevels K Axis.vertical,
          ¬(p.1 < z ∧ z < p.2))) := by
    simpa [IntrinsicVertices.consecutiveLevelPairs, xp, yp] using hyp
  have hxpdata := Finset.mem_filter.mp hxp'
  have hypdata := Finset.mem_filter.mp hyp'
  let q := (xp.1 + xp.2) / 2
  have hqlo : xp.1 < q := by dsimp [q]; linarith
  have hqhi : q < xp.2 := by dsimp [q]; linarith
  have hqgeneric' : q ∉ (K.vertexFinset.image Complex.re : Set ℝ) := by
    intro hq
    have hqf : q ∈ K.vertexFinset.image Complex.re := hq
    obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp hqf
    have hqlevel : q ∈
        (IntrinsicVertices.intrinsicCoordinateLevels K Axis.horizontal : Set ℝ) := by
      change q ∈ K.vertexFinset.image Complex.re
      exact hqf
    exact hxpdata.2.2 _ hqlevel ⟨hqlo, hqhi⟩
  have hqgeneric : q ∉
      (IntrinsicVertices.intrinsicCoordinateLevels K Axis.horizontal : Set ℝ) := by
    simpa [IntrinsicVertices.intrinsicCoordinateLevels, Axis.coord] using hqgeneric'
  let y := (yp.1 + yp.2) / 2
  have hylo : yp.1 < y := by dsimp [y]; linarith
  have hyhi : y < yp.2 := by dsimp [y]; linarith
  have hinterior_closedAxisBox {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
      interior (IntrinsicVertices.closedAxisBox a b c d) =
        {z : Tiling.Plane | z.re ∈ Ioo a b ∧ z.im ∈ Ioo c d} := by
    change interior (Icc a b ×ℂ Icc c d) = _
    rw [Complex.interior_reProdIm, interior_Icc, interior_Icc]
    ext z
    exact Complex.mem_reProdIm
  have hqy : ((q : ℂ) + (y : ℂ) * Complex.I) ∈ K.openCarrier := by
    apply hinside
    rw [hinterior_closedAxisBox hxpdata.2.1 hypdata.2.1]
    simpa using (show q ∈ Ioo xp.1 xp.2 ∧ y ∈ Ioo yp.1 yp.2 from
      ⟨⟨hqlo, hqhi⟩, ⟨hylo, hyhi⟩⟩)
  let A := Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K q
  have hAn : A.Nonempty := ⟨y, hqy⟩
  have hfinite_and_const := Region.verticalSlice_finiteIntervals K (by
    simpa [IntrinsicVertices.intrinsicCoordinateLevels, Axis.swap, Axis.coord] using hqgeneric)
  have hopen : IsOpen A := by
    apply K.openCarrier_regularOpen.1.preimage
    fun_prop
  have hfinite := hfinite_and_const.1
  obtain ⟨δ, hδ, hconst⟩ := hfinite_and_const.2
  have hleft_r : leftOf r = xp.1 := by
    dsimp [leftOf]
    rw [dif_pos hr]
  let hcollar : OuterVerticalCollar K A := {
    wall := xp.1
    right := xp.2
    lower := yp.1
    upper := yp.2
    cell_mem := by
      change IntrinsicVertices.closedAxisBox xp.1 xp.2 yp.1 yp.2 ∈
        (IntrinsicVertices.intrinsicGridPieces K : Set (Set Tiling.Plane))
      rw [← hrbox, ← hR]
      exact hr
    wall_lt_right := hxpdata.2.1
    lower_lt_upper := hypdata.2.1
    first := by
      intro s hs
      have hsR : s ∈ (R.pieces : Set (Set Tiling.Plane)) := by simpa [hR] using hs
      let hdataS := hdata_of s hsR
      let xs : ℝ × ℝ := Classical.choose hdataS
      let hdataS' := Classical.choose_spec hdataS
      let ys : ℝ × ℝ := Classical.choose hdataS'
      have hsdata := Classical.choose_spec hdataS'
      obtain ⟨hxs, hys, _, hsbox⟩ := hsdata
      have hm := hmin s hsR
      have hleft_s : leftOf s = xs.1 := by
        dsimp [leftOf]
        rw [dif_pos hsR]
      refine ⟨xs, ys, hsbox, ?_⟩
      rw [← hleft_r, ← hleft_s]
      exact hm
    exterior_empty := by
      intro z hzwall hzo
      have hzs : z ∈ K.support := by
        rw [← K.isPolygonal.closure_interior]
        exact subset_closure hzo
      rw [← R.sUnion_eq] at hzs
      obtain ⟨s, hs, hzs⟩ := hzs
      let hdataS := hdata_of s hs
      let xs : ℝ × ℝ := Classical.choose hdataS
      let hdataS' := Classical.choose_spec hdataS
      let ys : ℝ × ℝ := Classical.choose hdataS'
      have hsdata := Classical.choose_spec hdataS'
      obtain ⟨_, _, _, hsbox⟩ := hsdata
      have hleft : xp.1 ≤ xs.1 := by
        have hm := hmin s hs
        have hleft_s : leftOf s = xs.1 := by
          dsimp [leftOf]
          rw [dif_pos hs]
        rw [← hleft_r, ← hleft_s]
        exact hm
      rw [hsbox] at hzs
      change z.re ∈ Set.Icc xs.1 xs.2 ∧ z.im ∈ Set.Icc ys.1 ys.2 at hzs
      linarith [hleft, hzs.1.1, hzwall]
    transverse := q
    transverse_mem := ⟨hqlo, hqhi⟩
    generic := hqgeneric
    carrier_eq := rfl
    finiteIntervals := hfinite
    isOpen := hopen
    nonempty := hAn
    delta := δ
    delta_pos := hδ
    locally_constant := hconst
    cell_generic := by
      intro r hr hlevel
      have hlevel' : r ∈
          (IntrinsicVertices.intrinsicCoordinateLevels K Axis.horizontal : Set ℝ) := by
        change r ∈ K.vertexFinset.image Complex.re
        exact hlevel
      exact hxpdata.2.2 r hlevel' hr
    cell_constant := by
      intro r hr
      exact vertical_slice_constant_on_interval hxpdata.2.1
        (fun r hr hlevel ↦ by
          have hlevel' : r ∈
              (IntrinsicVertices.intrinsicCoordinateLevels K Axis.horizontal : Set ℝ) := by
            change r ∈ K.vertexFinset.image Complex.re
            exact hlevel
          exact hxpdata.2.2 r hlevel' hr)
        (q := q) ⟨hqlo, hqhi⟩ (r := r) hr }
  exact ⟨A, ⟨hcollar⟩⟩

private theorem outerVerticalCollar_regularSupport_product
    {K : Region} {S : Set Tiling.Plane} {c : ℝ} {A : Set ℝ}
    (hline : ∀ s ∈ S, s.re = c)
    (hcollar : OuterVerticalCollar K A) :
    ∀ x : ℝ, x ∈ Set.Ioo (c + hcollar.wall) (c + hcollar.right) →
      {y : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈
        Tiling.AxisParallel.regularSupport K S} =
        interior (closure (A + Complex.im '' S)) := by
  intro x hx
  let r := x - c
  have hr : r ∈ Set.Ioo hcollar.wall hcollar.right := by
    change hcollar.wall < x - c ∧ x - c < hcollar.right
    simp only [Set.mem_Ioo] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hslice := hcollar.cell_constant r hr
  have hAr : A =
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r :=
    hcollar.carrier_eq.trans hslice.symm
  let ε := min (r - hcollar.wall) (hcollar.right - r) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)) (by norm_num)
  have hconst : ∀ s : ℝ, |s - r| < ε →
      Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K s =
        Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r := by
    intro s hs
    rw [abs_lt] at hs
    dsimp [ε] at hs
    have hsr : s ∈ Set.Ioo hcollar.wall hcollar.right := by
      have hminL := min_le_left (r - hcollar.wall) (hcollar.right - r)
      have hminR := min_le_right (r - hcollar.wall) (hcollar.right - r)
      constructor <;> linarith [hr.1, hr.2]
    exact (hcollar.cell_constant s hsr).trans hslice.symm
  have hxcenter : x ∈ Set.Ioo (c + r - ε) (c + r + ε) := by
    dsimp [r]
    constructor <;> linarith
  exact vertical_regularSupport_fiber_eq_local hAr hline hconst x hxcenter

private theorem outerVerticalCollar_regularSupport_leftBound
    {K : Region} {S : Set Tiling.Plane} {c : ℝ} {A : Set ℝ}
    (hline : ∀ s ∈ S, s.re = c)
    (hcollar : OuterVerticalCollar K A) :
    Tiling.AxisParallel.regularSupport K S ⊆
      {z : Tiling.Plane | c + hcollar.wall < z.re} := by
  let U : Set Tiling.Plane := Tiling.AxisParallel.openUnion K S
  let H : Set Tiling.Plane := {z | c + hcollar.wall ≤ z.re}
  have hU : U ⊆ H := by
    intro z hz
    change z ∈ Tiling.AxisParallel.openUnion K S at hz
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hz
    obtain ⟨s, hs⟩ := hz
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hs
    have hsc := hline s.1 s.2
    have hks : hcollar.wall ≤ (-((s : Tiling.Plane)) + z).re := by
      by_contra hn
      exact hcollar.exterior_empty (-((s : Tiling.Plane)) + z)
        (lt_of_not_ge hn) hs
    have hcoord : z.re = c + (-((s : Tiling.Plane)) + z).re := by
      simp [Complex.add_re, hsc]
    dsimp [H]
    rw [hcoord]
    linarith
  have hHclosed : IsClosed H := by
    exact isClosed_Ici.preimage Complex.continuous_re
  have hclosure : closure U ⊆ H := closure_minimal hU hHclosed
  have hinterior : interior H ⊆ {z : Tiling.Plane | c + hcollar.wall < z.re} := by
    intro z hz
    have hHeq : H = Complex.re ⁻¹' Set.Ici (c + hcollar.wall) := by
      ext w
      simp [H]
    rw [hHeq] at hz
    have hz' : z ∈ interior (Complex.re ⁻¹' Set.Ici (c + hcollar.wall)) := by
      exact hz
    rw [Complex.interior_preimage_re] at hz'
    simpa [interior_Ici] using hz'
  intro z hz
  change z ∈ interior (closure U) at hz
  have hzH : z ∈ interior H := interior_mono hclosure hz
  exact hinterior hzH

private theorem outerVerticalCollar_regularSupport_wall_germ
    {K : Region} {S : Set Tiling.Plane} {c : ℝ} {A : Set ℝ}
    (hline : ∀ s ∈ S, s.re = c)
    (hcollar : OuterVerticalCollar K A) :
    let ε : ℝ := (hcollar.right - hcollar.wall) / 2
    0 < ε ∧
      Tiling.AxisParallel.regularSupport K S ∩
          (Set.Ioo (c + hcollar.wall - ε) (c + hcollar.wall + ε) ×ℂ
            (Set.univ : Set ℝ)) =
        Set.Ioo (c + hcollar.wall) (c + hcollar.wall + ε) ×ℂ
          interior (closure (A + Complex.im '' S)) := by
  let ε : ℝ := (hcollar.right - hcollar.wall) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith [hcollar.wall_lt_right]
  have hεright : hcollar.wall + ε < hcollar.right := by
    dsimp [ε]
    linarith [hcollar.wall_lt_right]
  refine ⟨hε, ?_⟩
  let V : Set Tiling.Plane :=
    Set.Ioo (c + hcollar.wall - ε) (c + hcollar.wall + ε) ×ℂ (Set.univ : Set ℝ)
  let P : Set Tiling.Plane :=
    Set.Ioo (c + hcollar.wall) (c + hcollar.wall + ε) ×ℂ
      interior (closure (A + Complex.im '' S))
  ext z
  constructor
  · rintro ⟨hzRS, hzV⟩
    have hzV' : z.re ∈ Set.Ioo (c + hcollar.wall - ε)
        (c + hcollar.wall + ε) := by
      change z.re ∈ Set.Ioo (c + hcollar.wall - ε) (c + hcollar.wall + ε) ∧
        z.im ∈ (Set.univ : Set ℝ) at hzV
      exact hzV.1
    have hleft := outerVerticalCollar_regularSupport_leftBound hline hcollar hzRS
    have hx : z.re ∈ Set.Ioo (c + hcollar.wall) (c + hcollar.wall + ε) :=
      ⟨hleft, hzV'.2⟩
    have hright : z.re ∈ Set.Ioo (c + hcollar.wall) (c + hcollar.right) :=
      ⟨hx.1, lt_trans hx.2 (by linarith [hεright])⟩
    have hfiber := outerVerticalCollar_regularSupport_product hline hcollar z.re hright
    have hpoint : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp
    have hzim : z.im ∈ {y : ℝ | (z.re : ℂ) + (y : ℂ) * Complex.I ∈
        Tiling.AxisParallel.regularSupport K S} := by
      change (z.re : ℂ) + (z.im : ℂ) * Complex.I ∈
        Tiling.AxisParallel.regularSupport K S
      rw [hpoint]
      exact hzRS
    rw [hfiber] at hzim
    change z ∈ P
    exact ⟨hx, hzim⟩
  · intro hz
    change z ∈ P at hz
    have hx : z.re ∈ Set.Ioo (c + hcollar.wall) (c + hcollar.wall + ε) := hz.1
    have hy : z.im ∈ interior (closure (A + Complex.im '' S)) := hz.2
    have hright : z.re ∈ Set.Ioo (c + hcollar.wall) (c + hcollar.right) :=
      ⟨hx.1, lt_trans hx.2 (by linarith [hεright])⟩
    have hfiber := outerVerticalCollar_regularSupport_product hline hcollar z.re hright
    have hzim : z.im ∈ {y : ℝ | (z.re : ℂ) + (y : ℂ) * Complex.I ∈
        Tiling.AxisParallel.regularSupport K S} := by
      rw [hfiber]
      exact hy
    have hpoint : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp
    have hzRS : z ∈ Tiling.AxisParallel.regularSupport K S := by
      rw [← hpoint]
      exact hzim
    have hzV : z ∈ V := by
      change z.re ∈ Set.Ioo (c + hcollar.wall - ε) (c + hcollar.wall + ε) ∧
        z.im ∈ (Set.univ : Set ℝ)
      constructor
      · constructor <;> linarith [hx.1, hx.2]
      · exact Set.mem_univ _
    change z ∈ Tiling.AxisParallel.regularSupport K S ∩ V
    exact ⟨hzRS, hzV⟩


private def outerWallProduct (axis : Axis) (a : ℝ) (W : Set ℝ) : Set Tiling.Plane :=
  match axis with
  | .horizontal => W ×ℂ Set.Ioi a
  | .vertical => Set.Ioi a ×ℂ W

private theorem outerWall_product_frontier_vertical
    {W : Set ℝ} {a y : ℝ} (hy : y ∈ frontier W) :
    FilledSliceChains.slicePoint Axis.vertical a y ∈
      frontier (outerWallProduct Axis.vertical a W) := by
  rw [outerWallProduct, FilledSliceChains.slicePoint, Complex.frontier_reProdIm]
  left
  simp only [Complex.mem_reProdIm]
  simpa using (show a ∈ closure (Set.Ioi a) ∧ y ∈ frontier W from ⟨by simp, hy⟩)

private theorem outerWall_product_frontier_vertical_closure
    {W : Set ℝ} {a y : ℝ} (hy : y ∈ closure W) :
    FilledSliceChains.slicePoint Axis.vertical a y ∈
      frontier (outerWallProduct Axis.vertical a W) := by
  rw [outerWallProduct, FilledSliceChains.slicePoint, Complex.frontier_reProdIm]
  right
  simp only [Complex.mem_reProdIm]
  simpa using (show a ∈ frontier (Set.Ioi a) ∧ y ∈ closure W from ⟨by simp, hy⟩)

private theorem outerWall_product_frontier_horizontal
    {W : Set ℝ} {a y : ℝ} (hy : y ∈ frontier W) :
    FilledSliceChains.slicePoint Axis.horizontal a y ∈
      frontier (outerWallProduct Axis.horizontal a W) := by
  rw [outerWallProduct, FilledSliceChains.slicePoint, Complex.frontier_reProdIm]
  right
  simp only [Complex.mem_reProdIm]
  simpa using (show y ∈ frontier W ∧ a ∈ closure (Set.Ioi a) from ⟨hy, by simp⟩)

private theorem outerWall_product_frontier_horizontal_closure
    {W : Set ℝ} {a y : ℝ} (hy : y ∈ closure W) :
    FilledSliceChains.slicePoint Axis.horizontal a y ∈
      frontier (outerWallProduct Axis.horizontal a W) := by
  rw [outerWallProduct, FilledSliceChains.slicePoint, Complex.frontier_reProdIm]
  left
  simp only [Complex.mem_reProdIm]
  simpa using (show y ∈ closure W ∧ a ∈ frontier (Set.Ioi a) from ⟨hy, by simp⟩)

private theorem outerWall_product_frontier_vertical_shift
    {W : Set ℝ} {a y t : ℝ} (ht : 0 < t) (hy : y ∈ frontier W) :
    FilledSliceChains.slicePoint Axis.vertical (a + t) y ∈
      frontier (outerWallProduct Axis.vertical a W) := by
  rw [outerWallProduct, FilledSliceChains.slicePoint, Complex.frontier_reProdIm]
  left
  simp only [Complex.mem_reProdIm]
  simpa using
    (show a + t ∈ closure (Set.Ioi a) ∧ y ∈ frontier W from
      ⟨by simp [closure_Ioi, le_of_lt ht], hy⟩)

private theorem outerWall_product_frontier_horizontal_shift
    {W : Set ℝ} {a y t : ℝ} (ht : 0 < t) (hy : y ∈ frontier W) :
    FilledSliceChains.slicePoint Axis.horizontal (a + t) y ∈
      frontier (outerWallProduct Axis.horizontal a W) := by
  rw [outerWallProduct, FilledSliceChains.slicePoint, Complex.frontier_reProdIm]
  right
  simp only [Complex.mem_reProdIm]
  simpa using
    (show y ∈ frontier W ∧ a + t ∈ closure (Set.Ioi a) from
      ⟨hy, by simp [closure_Ioi, le_of_lt ht]⟩)

private theorem outerWallPoint_dist_vertical
    (a y u : ℝ) :
    dist (FilledSliceChains.slicePoint Axis.vertical a u)
        (FilledSliceChains.slicePoint Axis.vertical a y) = |u - y| := by
  rw [Complex.dist_eq]
  have heq : FilledSliceChains.slicePoint Axis.vertical a u -
      FilledSliceChains.slicePoint Axis.vertical a y =
      ((u - y : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [FilledSliceChains.slicePoint]
  rw [heq, norm_mul]
  rw [Complex.norm_real]
  simp [Real.norm_eq_abs]

private theorem outerWallPoint_dist_horizontal
    (a y u : ℝ) :
    dist (FilledSliceChains.slicePoint Axis.horizontal a u)
        (FilledSliceChains.slicePoint Axis.horizontal a y) = |u - y| := by
  rw [Complex.dist_eq]
  have heq : FilledSliceChains.slicePoint Axis.horizontal a u -
      FilledSliceChains.slicePoint Axis.horizontal a y =
      ((u - y : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [FilledSliceChains.slicePoint]
  rw [heq]
  rw [Complex.norm_real]
  simp [Real.norm_eq_abs]

private theorem outerWallPoint_shift_dist_vertical
    (a y t : ℝ) (ht : 0 < t) :
    dist (FilledSliceChains.slicePoint Axis.vertical (a + t) y)
        (FilledSliceChains.slicePoint Axis.vertical a y) = t := by
  rw [Complex.dist_eq]
  have heq : FilledSliceChains.slicePoint Axis.vertical (a + t) y -
      FilledSliceChains.slicePoint Axis.vertical a y = ((t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [FilledSliceChains.slicePoint]
  rw [heq, Complex.norm_real]
  simp [Real.norm_eq_abs, abs_of_pos ht]

private theorem outerWallPoint_shift_dist_horizontal
    (a y t : ℝ) (ht : 0 < t) :
    dist (FilledSliceChains.slicePoint Axis.horizontal (a + t) y)
        (FilledSliceChains.slicePoint Axis.horizontal a y) = t := by
  rw [Complex.dist_eq]
  have heq : FilledSliceChains.slicePoint Axis.horizontal (a + t) y -
      FilledSliceChains.slicePoint Axis.horizontal a y = ((t : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [FilledSliceChains.slicePoint]
  rw [heq, norm_mul, Complex.norm_real]
  simp [Real.norm_eq_abs, abs_of_pos ht]

private theorem outerWall_frontier_subset_proper
    {D : Set Tiling.Plane} {W₁ : Set ℝ} {axis : Axis} {a y R : ℝ}
    (hR : 0 < R)
    (hprod : ∀ z ∈ Metric.ball (FilledSliceChains.slicePoint axis a y) R,
      z ∈ D ↔ z ∈ outerWallProduct axis a W₁)
    (hWopen : IsOpen W₁)
    (hy : y ∈ frontier W₁) :
    FilledSliceChains.slicePoint axis a y ∈ properVertices D := by
  let p : Tiling.Plane := FilledSliceChains.slicePoint axis a y
  let P : Set Tiling.Plane := outerWallProduct axis a W₁
  have hmem : ∀ᶠ z in 𝓝 p, (z ∈ D ↔ z ∈ P) := by
    apply Metric.mem_nhds_iff.2
    refine ⟨R, hR, ?_⟩
    intro z hz
    exact hprod z hz
  have hpP : p ∈ frontier P := by
    cases axis with
    | vertical =>
        simpa [p, P] using outerWall_product_frontier_vertical (a := a) (y := y) hy
    | horizontal =>
        simpa [p, P] using outerWall_product_frontier_horizontal (a := a) (y := y) hy
  have hsetEq : D =ᶠ[nhds p] P :=
    hmem.mono fun _ hz ↦ propext hz
  have hfront := frontier_eventuallyEq_of_eventuallyEq hsetEq
  have hpD : p ∈ frontier D :=
    (Iff.of_eq hfront.self_of_nhds).mpr hpP
  refine ⟨hpD, ?_⟩
  intro hstraight
  obtain ⟨L, hpL, hdim, hLlocal⟩ := hstraight
  obtain ⟨ρ, hρ, hρall⟩ :=
    Metric.eventually_nhds_iff.1
      ((hfront.mono fun _ hz ↦ Iff.of_eq hz).and hLlocal)
  have hyNotW : y ∉ W₁ := by
    intro hyW
    apply hy.2
    exact mem_interior_iff_mem_nhds.mpr (hWopen.mem_nhds hyW)
  obtain ⟨u, huW, huvd⟩ := Metric.mem_closure_iff.1 hy.1 (ρ / 2) (half_pos hρ)
  have huv₁ : |u - y| < ρ / 2 := by
    simpa [Real.dist_eq, abs_sub_comm] using huvd
  have huy : u ≠ y := by
    intro huy
    apply hyNotW
    simpa [huy] using huW
  let v : ℝ := y
  have hv : v ∈ frontier W₁ := by simpa [v] using hy
  have huv₂ : |v - y| < ρ / 2 := by simpa [v] using half_pos hρ
  have huv : u ≠ v := by simpa [v] using huy
  have huCl : u ∈ closure W₁ := subset_closure huW
  cases axis with
  | vertical =>
      let pu : Tiling.Plane := FilledSliceChains.slicePoint Axis.vertical a u
      let pv : Tiling.Plane := FilledSliceChains.slicePoint Axis.vertical a v
      let q : Tiling.Plane := FilledSliceChains.slicePoint Axis.vertical (a + ρ / 2) y
      have hpuBall : pu ∈ Metric.ball p ρ := by
        rw [Metric.mem_ball, outerWallPoint_dist_vertical]
        exact huv₁.trans (by linarith)
      have hpvBall : pv ∈ Metric.ball p ρ := by
        rw [Metric.mem_ball, outerWallPoint_dist_vertical]
        exact huv₂.trans (by linarith)
      have hqBall : q ∈ Metric.ball p ρ := by
        rw [Metric.mem_ball,
          outerWallPoint_shift_dist_vertical (a := a) (y := y) (t := ρ / 2)
            (half_pos hρ)]
        exact half_lt_self hρ
      change dist pu p < ρ at hpuBall
      change dist pv p < ρ at hpvBall
      change dist q p < ρ at hqBall
      have hpuP : pu ∈ frontier P := by
        simpa [pu, P] using outerWall_product_frontier_vertical_closure (a := a) huCl
      have hpvP : pv ∈ frontier P := by
        simpa [pv, P] using outerWall_product_frontier_vertical (a := a) hv
      have hqP : q ∈ frontier P := by
        simpa [q, P] using
          outerWall_product_frontier_vertical_shift (a := a) (y := y)
            (t := ρ / 2) (half_pos hρ) hy
      have hpuD : pu ∈ frontier D := (hρall hpuBall).1.mpr hpuP
      have hpvD : pv ∈ frontier D := (hρall hpvBall).1.mpr hpvP
      have hqD : q ∈ frontier D := (hρall hqBall).1.mpr hqP
      have hpuL : pu ∈ (L : Set Tiling.Plane) := (hρall hpuBall).2.mp hpuD
      have hpvL : pv ∈ (L : Set Tiling.Plane) := (hρall hpvBall).2.mp hpvD
      have hqL : q ∈ (L : Set Tiling.Plane) := (hρall hqBall).2.mp hqD
      obtain ⟨d, hd, hLeq⟩ := Tiling.AffineSubspace.exists_affineLine_eq hpL hdim
      obtain ⟨r, hr⟩ := by
        rw [hLeq] at hpuL
        exact (Tiling.mem_affineLine_iff_exists_smul hd).1 hpuL
      obtain ⟨s, hs⟩ := by
        rw [hLeq] at hpvL
        exact (Tiling.mem_affineLine_iff_exists_smul hd).1 hpvL
      obtain ⟨t, ht⟩ := by
        rw [hLeq] at hqL
        exact (Tiling.mem_affineLine_iff_exists_smul hd).1 hqL
      have hrs : r ≠ s := by
        intro hrs
        apply huv
        have hEq : pu = pv := by rw [hr, hs, hrs]
        simpa [pu, pv, FilledSliceChains.slicePoint] using hEq
      have hrd : r * d.re = 0 := by
        have h := congrArg Complex.re hr
        have h' : pu.re = p.re + r * d.re := by
          simpa only [Complex.add_re, Complex.smul_re, smul_eq_mul] using h
        have hpuRe : pu.re = p.re := by simp [pu, p, FilledSliceChains.slicePoint]
        linarith
      have hsd : s * d.re = 0 := by
        have h := congrArg Complex.re hs
        have h' : pv.re = p.re + s * d.re := by
          simpa only [Complex.add_re, Complex.smul_re, smul_eq_mul] using h
        have hpvRe : pv.re = p.re := by simp [pv, p, FilledSliceChains.slicePoint]
        linarith
      have hdre : d.re = 0 := by
        apply (mul_eq_zero.mp (show (r - s) * d.re = 0 by linarith)).resolve_left
        exact sub_ne_zero.mpr hrs
      have hqre : q.re = p.re := by
        have h := congrArg Complex.re ht
        simpa [Complex.add_re, Complex.smul_re, smul_eq_mul, hdre] using h
      have hqre' : q.re ≠ p.re := by
        simp [q, p, FilledSliceChains.slicePoint]
        linarith
      exact hqre' hqre
  | horizontal =>
      let pu : Tiling.Plane := FilledSliceChains.slicePoint Axis.horizontal a u
      let pv : Tiling.Plane := FilledSliceChains.slicePoint Axis.horizontal a v
      let q : Tiling.Plane := FilledSliceChains.slicePoint Axis.horizontal (a + ρ / 2) y
      have hpuBall : pu ∈ Metric.ball p ρ := by
        rw [Metric.mem_ball, outerWallPoint_dist_horizontal]
        exact huv₁.trans (by linarith)
      have hpvBall : pv ∈ Metric.ball p ρ := by
        rw [Metric.mem_ball, outerWallPoint_dist_horizontal]
        exact huv₂.trans (by linarith)
      have hqBall : q ∈ Metric.ball p ρ := by
        rw [Metric.mem_ball,
          outerWallPoint_shift_dist_horizontal (a := a) (y := y) (t := ρ / 2)
            (half_pos hρ)]
        exact half_lt_self hρ
      change dist pu p < ρ at hpuBall
      change dist pv p < ρ at hpvBall
      change dist q p < ρ at hqBall
      have hpuP : pu ∈ frontier P := by
        simpa [pu, P] using outerWall_product_frontier_horizontal_closure (a := a) huCl
      have hpvP : pv ∈ frontier P := by
        simpa [pv, P] using outerWall_product_frontier_horizontal (a := a) hv
      have hqP : q ∈ frontier P := by
        simpa [q, P] using
          outerWall_product_frontier_horizontal_shift (a := a) (y := y)
            (t := ρ / 2) (half_pos hρ) hy
      have hpuD : pu ∈ frontier D := (hρall hpuBall).1.mpr hpuP
      have hpvD : pv ∈ frontier D := (hρall hpvBall).1.mpr hpvP
      have hqD : q ∈ frontier D := (hρall hqBall).1.mpr hqP
      have hpuL : pu ∈ (L : Set Tiling.Plane) := (hρall hpuBall).2.mp hpuD
      have hpvL : pv ∈ (L : Set Tiling.Plane) := (hρall hpvBall).2.mp hpvD
      have hqL : q ∈ (L : Set Tiling.Plane) := (hρall hqBall).2.mp hqD
      obtain ⟨d, hd, hLeq⟩ := Tiling.AffineSubspace.exists_affineLine_eq hpL hdim
      obtain ⟨r, hr⟩ := by
        rw [hLeq] at hpuL
        exact (Tiling.mem_affineLine_iff_exists_smul hd).1 hpuL
      obtain ⟨s, hs⟩ := by
        rw [hLeq] at hpvL
        exact (Tiling.mem_affineLine_iff_exists_smul hd).1 hpvL
      obtain ⟨t, ht⟩ := by
        rw [hLeq] at hqL
        exact (Tiling.mem_affineLine_iff_exists_smul hd).1 hqL
      have hrs : r ≠ s := by
        intro hrs
        apply huv
        have hEq : pu = pv := by rw [hr, hs, hrs]
        simpa [pu, pv, FilledSliceChains.slicePoint] using hEq
      have hrd : r * d.im = 0 := by
        have h := congrArg Complex.im hr
        have h' : pu.im = p.im + r * d.im := by
          simpa only [Complex.add_im, Complex.smul_im, smul_eq_mul] using h
        have hpuIm : pu.im = p.im := by simp [pu, p, FilledSliceChains.slicePoint]
        linarith
      have hsd : s * d.im = 0 := by
        have h := congrArg Complex.im hs
        have h' : pv.im = p.im + s * d.im := by
          simpa only [Complex.add_im, Complex.smul_im, smul_eq_mul] using h
        have hpvIm : pv.im = p.im := by simp [pv, p, FilledSliceChains.slicePoint]
        linarith
      have hdim' : d.im = 0 := by
        apply (mul_eq_zero.mp (show (r - s) * d.im = 0 by linarith)).resolve_left
        exact sub_ne_zero.mpr hrs
      have hqim : q.im = p.im := by
        have h := congrArg Complex.im ht
        simpa [Complex.add_im, Complex.smul_im, smul_eq_mul, hdim'] using h
      have hqim' : q.im ≠ p.im := by
        simp [q, p, FilledSliceChains.slicePoint]
        linarith
      exact hqim' hqim

private theorem outerWall_openUnion_lowerBound
    {K : Region} {S : Set Tiling.Plane} (axis : Axis) {c m : ℝ}
    (halign : ∀ s ∈ S, axis.transverseCoord s = c)
    (hK : ∀ z ∈ K.support, m ≤ axis.transverseCoord z) :
    openUnion K S ⊆ {z : Tiling.Plane | m + c ≤ axis.transverseCoord z} := by
  intro z hz
  rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hz
  obtain ⟨s, hs⟩ := hz
  obtain ⟨w, hw, hzw⟩ := Set.mem_vadd_set.mp hs
  have hw' : w ∈ K.support := interior_subset hw
  have hm := hK w hw'
  have hc := halign (s : Tiling.Plane) s.2
  have hcoord : axis.transverseCoord z =
      axis.transverseCoord w + axis.transverseCoord (s : Tiling.Plane) := by
    rw [← hzw]
    cases axis <;>
      simp [vadd_eq_add, Axis.transverseCoord, add_comm]
  change m + c ≤ axis.transverseCoord z
  rw [hcoord]
  linarith

private theorem outerWall_regularSupport_lowerBound
    {K : Region} {S : Set Tiling.Plane} (axis : Axis) {c m : ℝ}
    (halign : ∀ s ∈ S, axis.transverseCoord s = c)
    (hK : ∀ z ∈ K.support, m ≤ axis.transverseCoord z) :
    regularSupport K S ⊆ {z : Tiling.Plane | m + c ≤ axis.transverseCoord z} := by
  let H : Set Tiling.Plane := {z | m + c ≤ axis.transverseCoord z}
  have hopen : openUnion K S ⊆ H := by
    exact outerWall_openUnion_lowerBound axis halign hK
  have hclosed : IsClosed H := by
    cases axis <;>
      simp only [H, Axis.transverseCoord]
    · exact isClosed_Ici.preimage Complex.continuous_im
    · exact isClosed_Ici.preimage Complex.continuous_re
  have hclosure : closure (openUnion K S) ⊆ H :=
    closure_minimal hopen hclosed
  intro z hz
  change m + c ≤ axis.transverseCoord z
  exact hclosure (interior_subset hz)

private theorem outerWall_properVertex_transverse_minimum
    {K : Region} {S : Set Tiling.Plane} (axis : Axis) {c m : ℝ}
    (halign : ∀ s ∈ S, axis.transverseCoord s = c)
    (hK : ∀ z ∈ K.support, m ≤ axis.transverseCoord z) :
    ∀ x ∈ properVertices (regularSupport K S),
      m + c ≤ axis.transverseCoord x := by
  let H : Set Tiling.Plane := {z | m + c ≤ axis.transverseCoord z}
  have hclosed : IsClosed H := by
    cases axis <;>
      simp only [H, Axis.transverseCoord]
    · exact isClosed_Ici.preimage Complex.continuous_im
    · exact isClosed_Ici.preimage Complex.continuous_re
  have hsupport : regularSupport K S ⊆ H :=
    outerWall_regularSupport_lowerBound axis halign hK
  have hclosure : closure (regularSupport K S) ⊆ H :=
    closure_minimal hsupport hclosed
  intro x hx
  have hfront : x ∈ frontier (regularSupport K S) := hx.1
  change m + c ≤ axis.transverseCoord x
  exact hclosure (frontier_subset_closure hfront)

private theorem outerWall_properVertex_transverse_isMinimal
    {K : Region} {S : Set Tiling.Plane} (axis : Axis) {c m : ℝ}
    (halign : ∀ s ∈ S, axis.transverseCoord s = c)
    (hK : ∀ z ∈ K.support, m ≤ axis.transverseCoord z)
    {x : Tiling.Plane} (_hx : x ∈ properVertices (regularSupport K S))
    (hwall : axis.transverseCoord x = m + c) :
    ∀ y ∈ properVertices (regularSupport K S),
      axis.transverseCoord x ≤ axis.transverseCoord y := by
  intro y hy
  have hmin := outerWall_properVertex_transverse_minimum axis halign hK y hy
  rw [hwall]
  exact hmin

private theorem centerColumn_noProperVertices
    {K : Region} {S : Set Tiling.Plane} {axis : Axis}
    (hcol : IsCenterColumn axis K S) :
    properVertices (regularSupport K S) = ∅ := by
  let D := regularSupport K S
  have horbit (a : ℝ) {z : Tiling.Plane} (hz : z ∈ frontier D) :
      (a • properVertexAxisVector axis) + z ∈ frontier D := by
    have hinv : (a • properVertexAxisVector axis) +ᵥ D = D := by
      cases axis <;> simpa [D, properVertexAxisVector, Complex.real_smul] using hcol.2.2.2 a
    rw [← hinv, frontier_vadd_eq]
    exact ⟨z, hz, rfl⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hpfront : p ∈ frontier D := hp.1
  obtain ⟨r, hr, hcross⟩ := regularSupport_localBoundaryCross hcol.1 p
  apply hp.2
  refine ⟨properVertexAxisLine axis p, (mem_properVertexAxisLine_iff axis p p).2 rfl, ?_, ?_⟩
  · rw [properVertexAxisLine, AffineSubspace.direction_mk']
    exact finrank_span_singleton (properVertexAxisVector_ne_zero axis)
  · filter_upwards [Metric.ball_mem_nhds p (half_pos hr)] with z hz
    change z ∈ frontier D ↔ z ∈ properVertexAxisLine axis p
    rw [mem_properVertexAxisLine_iff]
    constructor
    · intro hzfront
      have hzball : z ∈ Metric.ball p r :=
        Metric.ball_subset_ball (le_of_lt (half_lt_self hr)) hz
      rcases hcross z hzball hzfront with hre | him
      · cases axis with
        | vertical => exact hre
        | horizontal =>
          by_contra hneq
          have hshiftfront := horbit (r / 4) hzfront
          have hshiftball : ((r / 4 : ℝ) • properVertexAxisVector Axis.horizontal) + z ∈
              Metric.ball p r := by
            rw [Metric.mem_ball]
            calc
              dist (((r / 4 : ℝ) • properVertexAxisVector Axis.horizontal) + z) p ≤
                  dist (((r / 4 : ℝ) • properVertexAxisVector Axis.horizontal) + z) z +
                    dist z p :=
                dist_triangle _ _ _
              _ < r / 4 + r / 2 := by
                have hn :
                    dist (((r / 4 : ℝ) • properVertexAxisVector Axis.horizontal) + z) z =
                      r / 4 := by
                  simp only [dist_eq_norm, add_sub_cancel_right, norm_smul,
                    properVertexAxisVector, norm_one, mul_one, Real.norm_eq_abs]
                  exact abs_of_pos (by positivity)
                rw [hn]
                exact add_lt_add_right (Metric.mem_ball.mp hz) _
              _ < r := by linarith
          rcases hcross _ hshiftball hshiftfront with hshiftre | hshiftim
          · simp [properVertexAxisVector, hre] at hshiftre
            linarith
          · exact hneq (by simpa [Axis.transverseCoord, properVertexAxisVector] using hshiftim)
      · cases axis with
        | horizontal => exact him
        | vertical =>
          by_contra hneq
          have hshiftfront := horbit (r / 4) hzfront
          have hshiftball : ((r / 4 : ℝ) • properVertexAxisVector Axis.vertical) + z ∈
              Metric.ball p r := by
            rw [Metric.mem_ball]
            calc
              dist (((r / 4 : ℝ) • properVertexAxisVector Axis.vertical) + z) p ≤
                  dist (((r / 4 : ℝ) • properVertexAxisVector Axis.vertical) + z) z +
                    dist z p :=
                dist_triangle _ _ _
              _ < r / 4 + r / 2 := by
                have hn :
                    dist (((r / 4 : ℝ) • properVertexAxisVector Axis.vertical) + z) z =
                      r / 4 := by
                  simp only [dist_eq_norm, add_sub_cancel_right, norm_smul,
                    properVertexAxisVector, Complex.norm_I, mul_one, Real.norm_eq_abs]
                  exact abs_of_pos (by positivity)
                rw [hn]
                exact add_lt_add_right (Metric.mem_ball.mp hz) _
              _ < r := by linarith
          rcases hcross _ hshiftball hshiftfront with hshiftre | hshiftim
          · exact hneq (by simpa [Axis.transverseCoord, properVertexAxisVector] using hshiftre)
          · simp [properVertexAxisVector, him] at hshiftim
            linarith
    · intro hcoord
      cases axis with
      | horizontal =>
          have him : z.im = p.im := hcoord
          have heq : ((z.re - p.re) • properVertexAxisVector Axis.horizontal) + p = z := by
            apply Complex.ext <;> simp [properVertexAxisVector, him]
          exact heq ▸ horbit (z.re - p.re) hpfront
      | vertical =>
          have hre : z.re = p.re := hcoord
          have heq : ((z.im - p.im) • properVertexAxisVector Axis.vertical) + p = z := by
            apply Complex.ext <;> simp [properVertexAxisVector, hre]
          exact heq ▸ horbit (z.im - p.im) hpfront


private theorem normalized_escaping_limit
    {K : Region} {T : Set Tiling.Plane} (hT : HasFLC T) (axis : Axis)
    (hcounter : ∀ n : ℕ, ∃ S : Set Tiling.Plane, S ⊆ T ∧
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) ∧
      (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) ∧
      ∃ u ∈ properVertices (regularSupport K S),
        ∀ e ∈ properVertices (regularSupport K S),
          (∀ v ∈ properVertices (regularSupport K S),
            axis.transverseCoord e ≤ axis.transverseCoord v) →
          ¬ dist u e < (n : ℝ) + 1) :
    ∃ (Sn : ℕ → Set Tiling.Plane) (Slim : Set Tiling.Plane) (anchor : Tiling.Plane),
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements Slim) ∧
      (0 : Tiling.Plane) ∈ Slim ∧
      (∀ s ∈ Slim, axis.transverseCoord s = 0) ∧
      anchor ∈ properVertices (regularSupport K Slim) ∧
      (∀ n s, s ∈ Sn n → axis.transverseCoord s = 0) ∧
      (∀ k : ℕ, ∀ᶠ n in atTop,
        Sn n ∩ Metric.closedBall 0 (k : ℝ) = Slim ∩ Metric.closedBall 0 (k : ℝ)) ∧
      (∀ n z, z ∈ properVertices (regularSupport K (Sn n)) →
        (∀ v ∈ properVertices (regularSupport K (Sn n)),
          axis.transverseCoord z ≤ axis.transverseCoord v) →
        ¬ dist anchor z < (n : ℝ)) := by
  classical
  choose S hS hpack halign u hu hbad using hcounter
  choose v hv t ht heq using (fun n ↦ properVertexProvenance (hpack n) (u n) (hu n))
  obtain ⟨φ, w, hφ, hw⟩ := finite_vertex_subsequence v hv
  have hanchor : ∀ n, w + t (φ n) ∈ properVertices (regularSupport K (S (φ n))) := by
    intro n
    have h := hu (φ n)
    rw [heq (φ n), hw n] at h
    exact h
  obtain ⟨ψ, Slim, hψ, hp, hz, hl, ha, hpatch⟩ := normalized_pointed_limit hT
    (fun n ↦ S (φ n)) (fun n ↦ t (φ n)) w
    (fun n ↦ hS (φ n)) (fun n ↦ ht (φ n)) (fun n ↦ hpack (φ n))
    axis (fun n ↦ halign (φ n)) hanchor
  let Sn : ℕ → Set Tiling.Plane := fun n ↦ (-t (φ (ψ n))) +ᵥ S (φ (ψ n))
  have hSnline : ∀ n s, s ∈ Sn n → axis.transverseCoord s = 0 := by
    intro n s hs
    obtain ⟨c, hc⟩ := halign (φ (ψ n))
    obtain ⟨s₀, hs₀, rfl⟩ := Set.mem_vadd_set.mp hs
    have hc₀ := hc s₀ hs₀
    have hct := hc (t (φ (ψ n))) (ht (φ (ψ n)))
    cases axis <;> simp_all [Axis.transverseCoord, vadd_eq_add]
  refine ⟨Sn, Slim, w, hp, hz, hl, ha, hSnline, hpatch, ?_⟩
  intro n z hz hmin hdist
  have hback := extremal_vertex_translate_back axis (-t (φ (ψ n))) z hz hmin
  have hback' : t (φ (ψ n)) + z ∈ properVertices (regularSupport K (S (φ (ψ n)))) := by
    simpa only [neg_neg] using hback.1
  have hmin' : ∀ y ∈ properVertices (regularSupport K (S (φ (ψ n)))),
      axis.transverseCoord (t (φ (ψ n)) + z) ≤ axis.transverseCoord y := by
    simpa only [neg_neg] using hback.2
  apply hbad (φ (ψ n)) (t (φ (ψ n)) + z) hback' hmin'
  have huEq : u (φ (ψ n)) = w + t (φ (ψ n)) := by
    rw [heq, hw]
  rw [huEq, add_comm w, dist_add_left]
  have hindex : n ≤ φ (ψ n) := by
    have hle : ∀ (f : ℕ → ℕ), StrictMono f → ∀ m, m ≤ f m := by
      intro f hf m
      induction m with
      | zero => exact Nat.zero_le _
      | succ m ih => exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt (hf (Nat.lt_succ_self m)))
    exact (hle ψ hψ n).trans (hle φ hφ (ψ n))
  have hindexR : (n : ℝ) ≤ (φ (ψ n) : ℝ) := by exact_mod_cast hindex
  linarith

private theorem outerVerticalCollar_support_lowerBound
    {K : Region} {A : Set ℝ} (collar : OuterVerticalCollar K A) :
    ∀ z ∈ K.support, collar.wall ≤ z.re := by
  let H : Set Tiling.Plane := {z | collar.wall ≤ z.re}
  have hsub : K.openCarrier ⊆ H := by
    intro z hz
    exact le_of_not_gt (fun h ↦ collar.exterior_empty z h hz)
  have hcl : closure K.openCarrier ⊆ H :=
    closure_minimal hsub (isClosed_Ici.preimage Complex.continuous_re)
  have heq : closure K.openCarrier = K.support := K.isPolygonal.closure_interior
  rw [heq] at hcl
  exact hcl



private theorem outerWall_trace_full
    {K : Region} {S : Set Tiling.Plane} {A : Set ℝ} (axis : Axis)
    (hAopen : IsOpen A) (hAne : A.Nonempty) (hzero : (0 : Tiling.Plane) ∈ S)
    (wall ε : ℝ) (hε : 0 < ε)
    (hgerm : regularSupport K S ∩
      {z | axis.transverseCoord z ∈ Set.Ioo (wall - ε) (wall + ε)} =
      {z | axis.transverseCoord z ∈ Set.Ioo wall (wall + ε) ∧
        axis.coord z ∈ interior (closure (A + axis.coord '' S))})
    (hno : ∀ z ∈ properVertices (regularSupport K S), axis.transverseCoord z ≠ wall) :
    interior (closure (A + axis.coord '' S)) = Set.univ := by
  let W := interior (closure (A + axis.coord '' S))
  have hWne : W.Nonempty := by
    have hsub : A ⊆ A + axis.coord '' S := by
      intro a ha
      refine ⟨a, ha, 0, ⟨0, hzero, ?_⟩, by simp⟩
      cases axis <;> rfl
    exact hAne.mono (interior_maximal (hsub.trans subset_closure) hAopen)
  have hfront : frontier W = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    let p := FilledSliceChains.slicePoint axis wall y
    have hpcoord : axis.transverseCoord p = wall := by
      cases axis <;> simp [p, FilledSliceChains.slicePoint, Axis.transverseCoord]
    have hprod : ∀ z ∈ Metric.ball p ε,
        z ∈ regularSupport K S ↔ z ∈ outerWallProduct axis wall W := by
      intro z hz
      have hd : |axis.transverseCoord z - axis.transverseCoord p| ≤ dist z p := by
        cases axis with
        | horizontal => simpa only [Axis.transverseCoord, Complex.sub_im, Complex.dist_eq]
            using Complex.abs_im_le_norm (z - p)
        | vertical => simpa only [Axis.transverseCoord, Complex.sub_re, Complex.dist_eq]
            using Complex.abs_re_le_norm (z - p)
      rw [hpcoord] at hd
      have hre := hd.trans_lt hz
      rw [abs_lt] at hre
      have hzV : z ∈ {z | axis.transverseCoord z ∈ Set.Ioo (wall - ε) (wall + ε)} :=
        ⟨by linarith [hre.1], by linarith [hre.2]⟩
      have hm := Set.ext_iff.mp hgerm z
      simp only [Set.mem_inter_iff, hzV, and_true] at hm
      have hP : z ∈ outerWallProduct axis wall W ↔
          wall < axis.transverseCoord z ∧ axis.coord z ∈ W := by
        cases axis <;> simp only [outerWallProduct, Axis.transverseCoord, Axis.coord,
          Complex.mem_reProdIm, Set.mem_Ioi]
        exact and_comm
      rw [hP]
      change z ∈ regularSupport K S ↔
        axis.transverseCoord z ∈ Set.Ioo wall (wall + ε) ∧ axis.coord z ∈ W at hm
      simpa only [Set.mem_Ioo, show axis.transverseCoord z < wall + ε by linarith [hre.2],
        and_true] using hm
    have hp := outerWall_frontier_subset_proper hε hprod isOpen_interior hy
    exact hno p hp hpcoord
  exact (isClopen_iff_frontier_eq_empty.mpr hfront).eq_univ hWne

private def verticalGenericSection_swapBack
    {K : Region} {A : Set ℝ}
    (hA : GenericAxisSection K.coordinateSwap Axis.vertical A) :
    GenericAxisSection K Axis.horizontal A := by
  refine {
    transverse := hA.transverse
    generic := ?_
    carrier_eq := ?_
    finiteIntervals := hA.finiteIntervals
    isOpen := hA.isOpen
    nonempty := hA.nonempty }
  · intro hq
    have hq0 : hA.transverse ∈ K.vertexFinset.image Complex.im := by
      simpa [IntrinsicVertices.intrinsicCoordinateLevels, Axis.swap, Axis.coord] using hq
    have hq' : hA.transverse ∈ K.coordinateSwap.vertexFinset.image Complex.re := by
      rw [coordinateSwap_vertexLevels_local K]
      exact hq0
    apply hA.generic
    simpa [IntrinsicVertices.intrinsicCoordinateLevels, Axis.swap, Axis.coord] using hq'
  · calc
      A = axisSection K.coordinateSwap Axis.vertical hA.transverse := hA.carrier_eq
      _ = axisSection K Axis.horizontal hA.transverse := by
        ext x
        change (hA.transverse : ℂ) + (x : ℂ) * Complex.I ∈
            K.coordinateSwap.openCarrier ↔
          (x : ℂ) + (hA.transverse : ℂ) * Complex.I ∈ K.openCarrier
        rw [coordinateSwap_openCarrier]
        constructor
        · rintro ⟨z, hz, hzx⟩
          have hp : Tiling.AxisParallel.coordinateSwap
              ((hA.transverse : ℂ) + (x : ℂ) * Complex.I) =
                (x : ℂ) + (hA.transverse : ℂ) * Complex.I := by
            apply Complex.ext <;> simp
          have hz' : z = (x : ℂ) + (hA.transverse : ℂ) * Complex.I := by
            calc
              z = Tiling.AxisParallel.coordinateSwap
                  (Tiling.AxisParallel.coordinateSwap z) := by simp
              _ = Tiling.AxisParallel.coordinateSwap
                  ((hA.transverse : ℂ) + (x : ℂ) * Complex.I) :=
                congrArg Tiling.AxisParallel.coordinateSwap hzx
              _ = (x : ℂ) + (hA.transverse : ℂ) * Complex.I := hp
          exact hz'.symm ▸ hz
        · intro hz
          refine ⟨(x : ℂ) + (hA.transverse : ℂ) * Complex.I, hz, ?_⟩
          apply Complex.ext <;> simp
private def outerVerticalCollar_genericSection
    {K : Region} {A : Set ℝ} (hcollar : OuterVerticalCollar K A) :
    GenericAxisSection K Axis.vertical A := by
  refine {
    transverse := hcollar.transverse
    generic := hcollar.generic
    carrier_eq := ?_
    finiteIntervals := hcollar.finiteIntervals
    isOpen := hcollar.isOpen
    nonempty := hcollar.nonempty }
  simpa [axisSection, FilledSliceChains.slicePoint,
    Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice] using hcollar.carrier_eq

private theorem exists_vertical_outerWallData (K : Region) :
    ∃ (A : Set ℝ) (a ε : ℝ), Nonempty (GenericAxisSection K Axis.vertical A) ∧
      A.Nonempty ∧ 0 < ε ∧
      (∀ z ∈ K.support, a ≤ z.re) ∧
      ∀ S : Set Tiling.Plane, (∀ s ∈ S, s.re = 0) →
        Tiling.AxisParallel.regularSupport K S ∩
            {z | z.re ∈ Set.Ioo (a - ε) (a + ε)} =
          {z | z.re ∈ Set.Ioo a (a + ε) ∧
            z.im ∈ interior (closure (A + Complex.im '' S))} := by
  obtain ⟨A, ⟨hcollar⟩⟩ := outerVerticalCollar_construct K
  let ε : ℝ := (hcollar.right - hcollar.wall) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith [hcollar.wall_lt_right]
  refine ⟨A, hcollar.wall, ε, ⟨outerVerticalCollar_genericSection hcollar⟩,
    hcollar.nonempty, hε, ?_, ?_⟩
  · exact outerVerticalCollar_support_lowerBound hcollar
  · intro S hline
    have hgerm := outerVerticalCollar_regularSupport_wall_germ
      hline hcollar
    rcases hgerm with ⟨_, heq⟩
    ext z
    have hp := congrArg (fun E : Set Tiling.Plane => z ∈ E) heq
    simp only [Set.mem_inter_iff, Complex.mem_reProdIm, Set.mem_univ] at hp
    have hp' : (z ∈ Tiling.AxisParallel.regularSupport K S ∧
        z.re ∈ Set.Ioo (hcollar.wall - ε) (hcollar.wall + ε)) ↔
      z.re ∈ Set.Ioo hcollar.wall (hcollar.wall + ε) ∧
        z.im ∈ interior (closure (A + Complex.im '' S)) := by
      simpa [ε, zero_add] using hp
    constructor
    · rintro ⟨hzRS, hzband⟩
      exact hp'.mp ⟨hzRS, hzband⟩
    · rintro ⟨hzpos, hzim⟩
      have hzband : z.re ∈ Set.Ioo (hcollar.wall - ε) (hcollar.wall + ε) := by
        constructor <;> linarith [hzpos.1, hzpos.2]
      have hh := hp'.mpr ⟨hzpos, hzim⟩
      exact ⟨hh.1, hzband⟩


private theorem exists_axis_outerWallData (K : Region) (axis : Axis) :
    ∃ (A : Set ℝ) (a ε : ℝ), Nonempty (GenericAxisSection K axis A) ∧
      A.Nonempty ∧ 0 < ε ∧
      (∀ z ∈ K.support, a ≤ axis.transverseCoord z) ∧
      ∀ S : Set Tiling.Plane, (∀ s ∈ S, axis.transverseCoord s = 0) →
        Tiling.AxisParallel.regularSupport K S ∩
            {z | axis.transverseCoord z ∈ Set.Ioo (a - ε) (a + ε)} =
          {z | axis.transverseCoord z ∈ Set.Ioo a (a + ε) ∧
            axis.coord z ∈ interior (closure (A + axis.coord '' S))} := by
  cases axis with
  | vertical =>
      obtain ⟨A, a, ε, hA, hAn, hε, hbound, hgerm⟩ :=
        exists_vertical_outerWallData K
      refine ⟨A, a, ε, hA, hAn, hε, ?_, ?_⟩
      · intro z hz
        simpa [Axis.transverseCoord] using hbound z hz
      · intro S hline
        simpa [Axis.transverseCoord, Axis.coord] using hgerm S (by
          simpa [Axis.transverseCoord] using hline)
  | horizontal =>
      obtain ⟨A, a, ε, hA, hAn, hε, hbound, hgerm⟩ :=
        exists_vertical_outerWallData K.coordinateSwap
      refine ⟨A, a, ε, ⟨verticalGenericSection_swapBack hA.some⟩,
        hAn, hε, ?_, ?_⟩
      · intro z hz
        have hz' : Tiling.AxisParallel.coordinateSwap z ∈
            K.coordinateSwap.support := by
          change Tiling.AxisParallel.coordinateSwap z ∈
            Tiling.AxisParallel.coordinateSwap '' K.support
          exact ⟨z, hz, rfl⟩
        have hb := hbound (Tiling.AxisParallel.coordinateSwap z) hz'
        simpa [Axis.transverseCoord] using hb
      · intro S hline
        let S' := Tiling.AxisParallel.coordinateSwap '' S
        have hline' : ∀ s ∈ S', s.re = 0 := by
          rintro s ⟨t, ht, rfl⟩
          simpa [Axis.transverseCoord] using hline t ht
        have himage : Complex.im '' S' = Complex.re '' S := by
          ext r
          constructor
          · rintro ⟨z, ⟨s, hs, rfl⟩, rfl⟩
            exact ⟨s, hs, rfl⟩
          · rintro ⟨s, hs, rfl⟩
            exact ⟨Tiling.AxisParallel.coordinateSwap s,
              ⟨s, hs, rfl⟩, by simp⟩
        have hG := hgerm S' hline'
        have hreg := Tiling.AxisParallel.regularSupport_coordinateSwap K S
        have hRS (z : Tiling.Plane) :
            z ∈ Tiling.AxisParallel.regularSupport K S ↔
              Tiling.AxisParallel.coordinateSwap z ∈
                Tiling.AxisParallel.regularSupport K.coordinateSwap S' := by
          rw [hreg]
          constructor
          · intro hz
            exact ⟨z, hz, rfl⟩
          · rintro ⟨w, hw, hsw⟩
            have hwz : w = z := Tiling.AxisParallel.coordinateSwap.injective hsw
            simpa [hwz] using hw
        ext z
        constructor
        · rintro ⟨hzRS, hzband⟩
          have hzRS' := (hRS z).mp hzRS
          have hzband' : (Tiling.AxisParallel.coordinateSwap z).re ∈
              Set.Ioo (a - ε) (a + ε) := by
            simpa [Axis.transverseCoord] using hzband
          have hzG := (Set.ext_iff.mp hG) (Tiling.AxisParallel.coordinateSwap z)
          have hzprod := hzG.mp ⟨hzRS', hzband'⟩
          refine ⟨?_, ?_⟩
          · simpa [Axis.transverseCoord] using hzprod.1
          · simpa [Axis.coord, himage] using hzprod.2
        · rintro ⟨hzpos, hzw⟩
          have hzpos' : (Tiling.AxisParallel.coordinateSwap z).re ∈
              Set.Ioo a (a + ε) := by
            simpa [Axis.transverseCoord] using hzpos
          have hzw' : (Tiling.AxisParallel.coordinateSwap z).im ∈
              interior (closure (A + Complex.im '' S')) := by
            simpa [Axis.coord, himage] using hzw
          have hzG := (Set.ext_iff.mp hG) (Tiling.AxisParallel.coordinateSwap z)
          have hzprod := hzG.mpr ⟨hzpos', hzw'⟩
          refine ⟨(hRS z).mpr hzprod.1, ?_⟩
          simpa [Axis.transverseCoord] using hzprod.2

private theorem escaping_extrema_impossible
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres) (axis : Axis)
    (hcol : ∃ Col, IsCenterColumn axis C.region Col)
    (hcounter : ∀ n : ℕ, ∃ S : Set Tiling.Plane, S ⊆ C.centres ∧
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements S) ∧
      (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) ∧
      ∃ u ∈ properVertices (regularSupport C.region S),
        ∀ e ∈ properVertices (regularSupport C.region S),
          (∀ v ∈ properVertices (regularSupport C.region S),
            axis.transverseCoord e ≤ axis.transverseCoord v) →
          ¬ dist u e < (n : ℝ) + 1) : False := by
  obtain ⟨Sn, Slim, anchor, hp, hz, hl, ha, hline, hpatch, hbad⟩ :=
    normalized_escaping_limit hT axis hcounter
  obtain ⟨A, wall, ε, ⟨hA⟩, hAne, hε, hK, hgerm⟩ :=
    exists_axis_outerWallData C.region axis
  have hbadWall : ∀ n z, z ∈ properVertices (regularSupport C.region (Sn n)) →
      axis.transverseCoord z = wall → ¬ dist anchor z < (n : ℝ) := by
    intro n z hz hwall
    apply hbad n z hz
    apply outerWall_properVertex_transverse_isMinimal axis (hline n) hK hz
    simpa using hwall
  have hno := no_outerWall_properVertex_of_patches Sn Slim hpatch axis wall anchor hbadWall
  have hfull := outerWall_trace_full axis hA.isOpen hAne hz wall ε hε (hgerm Slim hl) hno
  have hcolumn := fullGenericSection_forcesCenterColumn axis hp ⟨0, hz⟩ ⟨0, hl⟩
    hcol A (axis.coord '' Slim) hA rfl hfull
  rw [centerColumn_noProperVertices hcolumn] at ha
  exact ha

private theorem uniform_nearMinimum
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres) (axis : Axis)
    (hcol : ∃ Col, IsCenterColumn axis C.region Col) :
    ∃ r > 0, ∀ S : Set Tiling.Plane, S ⊆ C.centres →
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements S) →
      (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) →
      ∀ u ∈ properVertices (regularSupport C.region S),
        ∃ e ∈ properVertices (regularSupport C.region S), dist u e < r ∧
          ∀ v ∈ properVertices (regularSupport C.region S),
            axis.transverseCoord e ≤ axis.transverseCoord v := by
  classical
  by_contra hnone
  push Not at hnone
  apply escaping_extrema_impossible hT axis hcol
  intro n
  obtain ⟨S, hS, hp, hl, u, hu, hbad⟩ := hnone ((n : ℝ) + 1) (by positivity)
  refine ⟨S, hS, hp, hl, u, hu, ?_⟩
  intro e he hmin hdist
  obtain ⟨v, hv, hlt⟩ := hbad e he hdist
  exact (not_lt_of_ge (hmin v hv)) hlt

private theorem columnable_extremalTrace_uniformLinked :
  ∀ {C : ApproximationContext.{0}}, HasFLC C.centres →
    ∀ axis, (∃ Col, IsCenterColumn axis C.region Col) →
    ∃ r > 0, ∀ {S : Set Tiling.Plane}, S ⊆ C.centres → S.Nonempty →
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements S) →
      Linked (60 * Metric.diam C.region.openCarrier) S →
      (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) →
      ¬ IsCenterColumn axis C.region S →
      ∀ u, ∀ hu : u ∈ properVertices (regularSupport C.region S),
        ∃ e, ∃ he : e ∈ properVertices (regularSupport C.region S),
          Relation.ReflTransGen
            (fun x y : ↥(properVertices (regularSupport C.region S)) => dist x.1 y.1 < r)
            ⟨u, hu⟩ ⟨e, he⟩ ∧
          ∀ v ∈ properVertices (regularSupport C.region S),
            axis.transverseCoord e ≤ axis.transverseCoord v := by
  intro C hT axis hcol
  obtain ⟨r, hr, hnear⟩ := uniform_nearMinimum hT axis hcol
  refine ⟨r, hr, ?_⟩
  intro S hS _hne hp _hlinked hline _hncol u hu
  obtain ⟨e, he, hdist, hmin⟩ := hnear S hS hp hline u hu
  exact ⟨e, he, Relation.ReflTransGen.single hdist, hmin⟩

private theorem aligned_coordinate_boundedWindowFinite
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres)
    (axis : Axis) {S : Set Tiling.Plane} (hS : S ⊆ C.centres)
    (hline : ∃ c, ∀ s ∈ S, axis.transverseCoord s = c) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q → ((axis.coord '' S) ∩ Q).Finite := by
  obtain ⟨c, hc⟩ := hline
  intro Q hQ
  obtain ⟨R, hR⟩ := hQ.exists_norm_le
  let B : Set Tiling.Plane := Metric.closedBall 0 (R + |c|)
  have hfinite := hT.1 B Metric.isBounded_closedBall
  apply (hfinite.image axis.coord).subset
  rintro x ⟨⟨s, hs, rfl⟩, hxQ⟩
  refine ⟨s, ⟨hS hs, ?_⟩, rfl⟩
  have hxR : |axis.coord s| ≤ R := by simpa only [Real.norm_eq_abs] using hR _ hxQ
  have hsline := hc s hs
  change dist s 0 ≤ R + |c|
  rw [dist_zero_right]
  have hnorm := Complex.norm_le_abs_re_add_abs_im s
  cases axis <;> simp only [Axis.coord, Axis.transverseCoord] at hxR hsline
  · rw [hsline] at hnorm
    exact hnorm.trans (by linarith)
  · rw [hsline] at hnorm
    exact hnorm.trans (by linarith)

private theorem genuineTraceEndpoint_intrinsicLabel
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres)
    (axis : Axis) {S : Set Tiling.Plane} (hS : S ⊆ C.centres)
    (hline : ∃ c, ∀ s ∈ S, axis.transverseCoord s = c)
    {A : Set ℝ} (hA : GenericAxisSection C.region axis A) {a : ℝ}
    (ha : a ∈ traceEndpoints A (axis.coord '' S)) :
    ∃ t ∈ S, ∃ v ∈ C.region.vertices, axis.coord (v + t) = a := by
  have hraw : A = {x | FilledSliceChains.slicePoint axis hA.transverse x ∈
      C.region.openCarrier} := hA.carrier_eq
  obtain ⟨B, _, hBraw⟩ := genuineGenericSection_construct C axis hA.transverse
    hA.generic (by simpa only [← hraw] using hA.nonempty)
  have hBA : B.rawCarrier = A := hBraw.trans hraw.symm
  have hlocal := locallyFinite_closedTranslates_of_boundedWindowFinite B.presentation
    (aligned_coordinate_boundedWindowFinite hT axis hS hline)
  have hunion : lineOpenUnion B.rawCarrier (axis.coord '' S) =
      B.rawCarrier + axis.coord '' S := by
    ext x
    simp only [lineOpenUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨s, y, hy, rfl⟩
      exact ⟨y, hy, s, s.2, by simp [vadd_eq_add, add_comm]⟩
    · rintro ⟨y, hy, s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, y, hy, by simp [vadd_eq_add, add_comm]⟩
  have ha' : a ∈ frontier (FiniteInterval.regularizedTarget B.rawCarrier (axis.coord '' S)) := by
    change a ∈ frontier (interior (closure (lineOpenUnion B.rawCarrier (axis.coord '' S))))
    rw [hunion, hBA]
    exact ha
  have he := frontier_regularizedTarget_subset_translatedEndpointSet B.presentation hlocal ha'
  obtain ⟨y, ⟨t, ht, rfl⟩, e, he, hae⟩ := (mem_translatedEndpointSet_iff B.presentation).mp he
  simp only [IntervalPresentation.endpoints, Finset.mem_union, Finset.mem_image] at he
  rcases he with ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩
  · refine ⟨t, ht, B.leftVertex i, (B.leftVertex i).2, ?_⟩
    rw [show axis.coord ((B.leftVertex i).1 + t) =
      axis.coord (B.leftVertex i).1 + axis.coord t by cases axis <;> rfl,
      B.leftVertex_coord]
    simpa only [add_comm] using hae.symm
  · refine ⟨t, ht, B.rightVertex i, (B.rightVertex i).2, ?_⟩
    rw [show axis.coord ((B.rightVertex i).1 + t) =
      axis.coord (B.rightVertex i).1 + axis.coord t by cases axis <;> rfl,
      B.rightVertex_coord]
    simpa only [add_comm] using hae.symm

private theorem boundedTraceComponentCode_finite :
    ∀ {C : ApproximationContext.{0}}, HasFLC C.centres → ∀ (axis : Axis) (R : ℝ), 0 < R →
      ∃ Z : Finset C.coordinateSpace, ∀ {S : Set Tiling.Plane}, S ⊆ C.centres →
        (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) →
        ∀ {A : Set ℝ}, GenericAxisSection C.region axis A →
        ∀ {a b : ℝ}, a < b → a ∈ traceEndpoints A (axis.coord '' S) →
          b ∈ traceEndpoints A (axis.coord '' S) → b - a ≤ R →
          ∃ code : BoundedTraceComponentCode C axis S A a b,
            code.lengthScalar ∈ Z := by
  classical
  intro C hT axis R hR
  let d := Metric.diam C.region.support
  let D : Set Tiling.Plane := (C.translatedVertices - C.translatedVertices) ∩
    Metric.closedBall 0 (R + d)
  have hD : D.Finite := boundedDifferenceSet_finite C hT (R + d)
    (by dsimp [d]; linarith [show 0 ≤ Metric.diam C.region.support from Metric.diam_nonneg])
  let Zset : Set C.coordinateSpace := (fun z : C.coordinateSpace => (z : ℝ)) ⁻¹'
    (axis.coord '' D)
  have hZ : Zset.Finite := (hD.image axis.coord).preimage Subtype.val_injective.injOn
  refine ⟨hZ.toFinset, ?_⟩
  intro S hS hline A hA a b hab ha hb hlen
  obtain ⟨tL, htL, vL, hvL, hLa⟩ := genuineTraceEndpoint_intrinsicLabel hT axis hS hline hA ha
  obtain ⟨tR, htR, vR, hvR, hRb⟩ := genuineTraceEndpoint_intrinsicLabel hT axis hS hline hA hb
  let left : ↥C.translatedVertices := ⟨vL + tL, vL, hvL, tL, hS htL, rfl⟩
  let right : ↥C.translatedVertices := ⟨vR + tR, vR, hvR, tR, hS htR, rfl⟩
  let lengthScalar := C.translatedDifferenceScalar axis right left
  have hscalar : (lengthScalar : ℝ) = b - a := by
    have hcoord : (lengthScalar : ℝ) = axis.coord (right.1 - left.1) := by
      cases axis <;> rfl
    rw [hcoord]
    change axis.coord ((vR + tR) - (vL + tL)) = b - a
    cases axis <;> simp only [Axis.coord, Complex.sub_re, Complex.sub_im] at hLa hRb ⊢ <;>
      linarith
  let code : BoundedTraceComponentCode C axis S A a b := {
    ordered := hab
    left := left
    right := right
    left_center_mem := ⟨tL, htL, vL, hvL, rfl⟩
    right_center_mem := ⟨tR, htR, vR, hvR, rfl⟩
    left_value := hLa
    right_value := hRb
    left_endpoint := ha
    right_endpoint := hb
    lengthScalar := lengthScalar
    lengthScalar_formula := rfl
    lengthScalar_eq := hscalar }
  refine ⟨code, hZ.mem_toFinset.mpr ?_⟩
  change (lengthScalar : ℝ) ∈ axis.coord '' D
  refine ⟨right.1 - left.1, ⟨⟨right, right.2, left, left.2, rfl⟩, ?_⟩, ?_⟩
  · have hvLs : vL ∈ C.region.support := by
      rw [← C.region.isPolygonal.closure_interior]
      exact frontier_subset_closure (IntrinsicVertices.region_vertices_subset_frontier C.region hvL)
    have hvRs : vR ∈ C.region.support := by
      rw [← C.region.isPolygonal.closure_interior]
      exact frontier_subset_closure (IntrinsicVertices.region_vertices_subset_frontier C.region hvR)
    have hdistV : ‖vR - vL‖ ≤ d := by
      simpa only [Complex.dist_eq] using
        Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded hvRs hvLs
    obtain ⟨c, hc⟩ := hline
    have htrans : axis.transverseCoord (right.1 - left.1) =
        axis.transverseCoord (vR - vL) := by
      have hLc := hc tL htL
      have hRc := hc tR htR
      change axis.transverseCoord ((vR + tR) - (vL + tL)) =
        axis.transverseCoord (vR - vL)
      cases axis <;> simp only [Axis.transverseCoord, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im] at hLc hRc ⊢ <;> linarith
    have htransBound : |axis.transverseCoord (right.1 - left.1)| ≤ d := by
      rw [htrans]
      cases axis with
      | horizontal => exact (Complex.abs_im_le_norm _).trans hdistV
      | vertical => exact (Complex.abs_re_le_norm _).trans hdistV
    have halong : axis.coord (right.1 - left.1) = b - a := by
      calc
        axis.coord (right.1 - left.1) = (lengthScalar : ℝ) := by cases axis <;> rfl
        _ = b - a := hscalar
    have hnorm : ‖right.1 - left.1‖ ≤ |axis.coord (right.1 - left.1)| +
        |axis.transverseCoord (right.1 - left.1)| := by
      cases axis with
      | horizontal => exact Complex.norm_le_abs_re_add_abs_im _
      | vertical => simpa only [Axis.coord, Axis.transverseCoord, add_comm] using
          Complex.norm_le_abs_re_add_abs_im (right.1 - left.1)
    change dist (right.1 - left.1) 0 ≤ R + d
    rw [dist_zero_right]
    rw [halong, abs_of_nonneg (sub_nonneg.mpr hab.le)] at hnorm
    linarith
  · cases axis <;> rfl

private theorem support_eq_vadd_of_properVertexGerms :
    ∀ {D₀ D₁ : Set Tiling.Plane} (hlocal₀ : IsLocallyAxisParallelPolygonal D₀)
      (hlocal₁ : IsLocallyAxisParallelPolygonal D₁), D₀.Nonempty → D₁.Nonempty →
      D₀ ≠ Set.univ → D₁ ≠ Set.univ → ∀ beta,
      properVertices D₁ = beta +ᵥ properVertices D₀ →
      (∀ p, ∀ hp : p ∈ properVertices D₀,
        ∀ hp' : beta + p ∈ properVertices D₁,
          localCone D₁ (beta + p) hlocal₁ hp' = localCone D₀ p hlocal₀ hp) →
      (∀ L ∈ completeBoundaryLines D₀ hlocal₀,
        (L.carrier ∩ properVertices D₀).Nonempty) →
      (∀ L ∈ completeBoundaryLines D₁ hlocal₁,
        (L.carrier ∩ properVertices D₁).Nonempty) →
      D₁ = beta +ᵥ D₀ := by
  intro D₀ D₁ hlocal₀ hlocal₁ hne₀ hne₁ hproper₀ hproper₁ beta hvertices hcones hlines₀ hlines₁
  have completeLines_empty (D : Set Tiling.Plane) (hlocal : IsLocallyAxisParallelPolygonal D)
      (hlines : ∀ L ∈ completeBoundaryLines D hlocal,
        (L.carrier ∩ properVertices D).Nonempty) :
      completeBoundaryLines D hlocal = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro L hL
    obtain ⟨x, hxL, hxProper⟩ := hlines L hL
    obtain ⟨r, hr, hside⟩ := hL.2 x hxL
    let H : Set Tiling.Plane := {z | if L.insideOnPositiveSide then
      L.level < L.axis.transverseCoord z else L.axis.transverseCoord z < L.level}
    have hDH : D =ᶠ[𝓝 x] H := by
      filter_upwards [Metric.ball_mem_nhds x hr] with z hz
      exact propext (hside z hz)
    have hstraight : Tiling.BoundaryLocallyStraightAt H x := by
      refine ⟨properVertexAxisLine L.axis x,
        (mem_properVertexAxisLine_iff L.axis x x).mpr rfl, ?_, ?_⟩
      · rw [properVertexAxisLine, AffineSubspace.direction_mk']
        exact finrank_span_singleton (properVertexAxisVector_ne_zero L.axis)
      · have hfront : frontier H = L.carrier := by
          cases haxis : L.axis <;> cases hpos : L.insideOnPositiveSide <;>
            simp only [H, haxis, hpos, Bool.false_eq_true, ↓reduceIte,
              Axis.transverseCoord, CompleteBoundaryLine.carrier]
          · exact (Complex.frontier_preimage_im (Set.Iio L.level)).trans
              (by rw [frontier_Iio]; rfl)
          · exact (Complex.frontier_preimage_im (Set.Ioi L.level)).trans
              (by rw [frontier_Ioi]; rfl)
          · exact (Complex.frontier_preimage_re (Set.Iio L.level)).trans
              (by rw [frontier_Iio]; rfl)
          · exact (Complex.frontier_preimage_re (Set.Ioi L.level)).trans
              (by rw [frontier_Ioi]; rfl)
        filter_upwards [] with z
        rw [hfront]
        change z ∈ L.carrier ↔ z ∈ properVertexAxisLine L.axis x
        rw [mem_properVertexAxisLine_iff]
        change L.axis.transverseCoord z = L.level ↔
          L.axis.transverseCoord z = L.axis.transverseCoord x
        rw [show L.axis.transverseCoord x = L.level from hxL]
    exact ((isProperVertex_iff_of_eventuallyEq hDH).mp hxProper).2 hstraight
  have hlinesEq₀ := completeLines_empty D₀ hlocal₀ hlines₀
  have hlinesEq₁ := completeLines_empty D₁ hlocal₁ hlines₁
  apply eq_vadd_of_boundaryCode hlocal₀.1 hlocal₁.1 hlocal₀.2.1 hlocal₁.2.1
    hne₀ hne₁ hproper₀ hproper₁ hlocal₀ hlocal₁
  apply (boundaryCode_eq_vadd_iff hlocal₀ hlocal₁ beta).mpr
  refine ⟨hvertices, ?_, ?_⟩
  · ext q
    rcases q with ⟨x, cone⟩
    constructor
    · rintro ⟨hx, hcone⟩
      have hxV : x ∈ beta +ᵥ properVertices D₀ := hvertices ▸ hx
      obtain ⟨p, hp, hpx⟩ := hxV
      change beta + p = x at hpx
      subst x
      refine ⟨⟨p, hp, rfl⟩, ?_⟩
      change cone = localCone D₀ ((beta + p) - beta) hlocal₀
        (by simpa only [add_sub_cancel_left] using (show IsProperVertex D₀ p from hp))
      simpa only [localCone, add_sub_cancel_left] using hcone.trans (hcones p hp hx)
    · rintro ⟨hx, hcone⟩
      obtain ⟨p, hp, hpx⟩ := hx
      change beta + p = x at hpx
      subst x
      have hx' : beta + p ∈ properVertices D₁ := hvertices.symm ▸ ⟨p, hp, rfl⟩
      refine ⟨hx', ?_⟩
      change cone = localCone D₀ ((beta + p) - beta) hlocal₀
        (by simpa only [add_sub_cancel_left] using (show IsProperVertex D₀ p from hp)) at hcone
      have hcone' : cone = localCone D₀ p hlocal₀ hp := by
        simpa only [localCone, add_sub_cancel_left] using hcone
      exact hcone'.trans (hcones p hp hx').symm
  · change completeBoundaryLines D₁ hlocal₁ =
      (fun L => L.vadd beta) '' completeBoundaryLines D₀ hlocal₀
    rw [hlinesEq₀, hlinesEq₁, Set.image_empty]

private def sourceGeometryCentreVertex
    {C : ApproximationContext} (s : ↥C.centres) : ↥C.translatedVertices :=
  ⟨s, ⟨0, C.zero_mem_vertices, s, s.2, zero_add (s : Tiling.Plane)⟩⟩

private theorem sourceGeometryCentreVertex_map
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (s : ↥C.centres) :
    mapTranslatedVertex phi (sourceGeometryCentreVertex s) = Tphi s := by
  rw [mapTranslatedVertex]
  have hpoint : C.translatedVertexPoint (sourceGeometryCentreVertex s) =
      C.centrePoint s.1 s.2 := by
    apply Subtype.ext
    rfl
  rw [hpoint, ← hTphi s]

private theorem sourceGeometry_coord_abs_le (axis : Axis) (a b : Tiling.Plane) :
    |axis.coord a - axis.coord b| ≤ dist a b := by
  have hRe : |(a - b).re| ≤ ‖a - b‖ := Complex.abs_re_le_norm (a - b)
  have hIm : |(a - b).im| ≤ ‖a - b‖ := Complex.abs_im_le_norm (a - b)
  cases axis with
  | horizontal => simpa [Axis.coord, Complex.sub_re, dist_eq_norm] using hRe
  | vertical => simpa [Axis.coord, Complex.sub_im, dist_eq_norm] using hIm

private theorem sourceGeometry_linked_path_near
    {U : Set Tiling.Plane} {G x : ℝ} (hG : 0 < G) (axis : Axis)
    {a b : Tiling.Plane}
    (hp : Relation.ReflTransGen
      (fun u v : Tiling.Plane ↦ u ∈ U ∧ v ∈ U ∧ dist u v < G) a b)
    (ha : a ∈ U) (hb : b ∈ U)
    (hax : axis.coord a ≤ x) (hbx : x ≤ axis.coord b) :
    ∃ z ∈ U, x - G < axis.coord z ∧ axis.coord z < x + G := by
  induction hp generalizing hax ha with
  | refl =>
      refine ⟨a, ha, ?_, ?_⟩ <;> linarith
  | @tail m b htail edge ih =>
      rcases edge with ⟨hm, hb', hdist⟩
      by_cases hmx : axis.coord m ≤ x
      · have hstep : |axis.coord m - axis.coord b| < G :=
          lt_of_le_of_lt (sourceGeometry_coord_abs_le axis m b) hdist
        refine ⟨b, hb', ?_, ?_⟩ <;> linarith [abs_lt.mp hstep]
      · exact ih ha hm hax (le_of_lt (lt_of_not_ge hmx))

private theorem periodicImageLine_sourceGeometry
    : ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hphi : IsEpsilonApproximation C P.threshold phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres) (G : ℝ),
    0 < G → G + P.localError < P.scale / 2 →
    S.Nonempty → Linked G (Subtype.val '' S) →
    (∃ c, ∀ s : S, axis.transverseCoord (Tphi s) = c) →
    ∀ imagePeriod : Tiling.Plane, imagePeriod ≠ 0 →
      axis.transverseCoord imagePeriod = 0 →
      imagePeriod +ᵥ deformedCenterCarrierOn Tphi S =
        deformedCenterCarrierOn Tphi S →
      (∃ c, ∀ s ∈ Subtype.val '' S, axis.transverseCoord s = c) ∧
      ∀ x : ℝ, ∃ y ∈ axis.coord '' (Subtype.val '' S),
        x - G < y ∧ y < x + G := by
  intro C P hScale phi hphi Tphi hTphi axis S G hG hmargin hSne hLinked hcol
    imagePeriod hne haxis hperiod
  obtain ⟨hU_nonempty, hconn⟩ := hLinked
  have hGscale : G < P.scale := by
    have : G + P.localError < P.scale / 2 := hmargin
    linarith [P.localError_pos]
  have hIndexed : IndexedShortEdgeConnected C G S := by
    intro x hx y hy
    exact hconn x hx y hy
  obtain ⟨alpha, halpha_ne, halpha_axis, halpha_map, halpha_set⟩ :=
    connectedAlignedIndexedPeriodLift P phi hphi Tphi hTphi axis S G
      hSne hIndexed hcol hGscale hmargin imagePeriod hne haxis hperiod
  let U : Set Tiling.Plane := Subtype.val '' S
  have hu_source (u : ↥U) : ∃ s : ↥S, (s : Tiling.Plane) = u.1 := by
    rcases u.2 with ⟨s, hs, hsu⟩
    exact ⟨⟨s, hs⟩, hsu⟩
  let sourceAt : ∀ u : ↥U, ↥S := fun u => Classical.choose (hu_source u)
  have sourceAt_spec (u : ↥U) : (sourceAt u : Tiling.Plane) = u.1 :=
    Classical.choose_spec (hu_source u)
  have edge_trans : ∀ {s t : ↥S}, dist (s : Tiling.Plane) t < G →
      axis.transverseCoord ((s : Tiling.Plane) - (t : Tiling.Plane)) = 0 := by
    intro s t hst
    let a_s := sourceGeometryCentreVertex s.1
    let a_t := sourceGeometryCentreVertex t.1
    have hst' : dist (s : Tiling.Plane) t < P.scale := lt_trans hst hGscale
    have hlocal := P.local_accuracy phi hphi a_s a_t (by
      simpa [a_s, a_t, sourceGeometryCentreVertex] using hst')
    have htriangle : dist (mapTranslatedVertex phi a_s - mapTranslatedVertex phi a_t) 0 ≤
        dist (mapTranslatedVertex phi a_s - mapTranslatedVertex phi a_t)
          ((a_s : Tiling.Plane) - (a_t : Tiling.Plane)) +
        dist ((a_s : Tiling.Plane) - (a_t : Tiling.Plane)) 0 :=
      dist_triangle _ _ _
    have hdist : dist (Tphi s.1) (Tphi t.1) ≤
        dist (mapTranslatedVertex phi a_s - mapTranslatedVertex phi a_t)
          ((a_s : Tiling.Plane) - (a_t : Tiling.Plane)) + dist (s : Tiling.Plane) t := by
      calc
        dist (Tphi s.1) (Tphi t.1) =
            dist (mapTranslatedVertex phi a_s) (mapTranslatedVertex phi a_t) := by
          rw [← sourceGeometryCentreVertex_map phi Tphi hTphi s.1,
            ← sourceGeometryCentreVertex_map phi Tphi hTphi t.1]
        _ ≤ _ := by
          simpa [a_s, a_t, sourceGeometryCentreVertex, dist_eq_norm] using htriangle
    have hm : dist (Tphi s.1) (Tphi t.1) < P.scale / 2 := by
      calc
        dist (Tphi s.1) (Tphi t.1) ≤ _ := hdist
        _ < P.localError + dist (s : Tiling.Plane) t := by
          simpa [add_comm] using add_lt_add_right hlocal (dist (s : Tiling.Plane) t)
        _ < P.scale / 2 := by linarith
    have hm' : dist (mapTranslatedVertex phi a_s) (mapTranslatedVertex phi a_t) <
        P.scale / 2 := by
      rw [sourceGeometryCentreVertex_map phi Tphi hTphi s.1,
        sourceGeometryCentreVertex_map phi Tphi hTphi t.1]
      exact hm
    have htarget : axis.transverseCoord
        (mapTranslatedVertex phi a_s - mapTranslatedVertex phi a_t) = 0 := by
      rw [sourceGeometryCentreVertex_map phi Tphi hTphi s.1,
        sourceGeometryCentreVertex_map phi Tphi hTphi t.1]
      obtain ⟨c, hc⟩ := hcol
      have hs := hc s
      have ht := hc t
      cases axis <;> simp only [Axis.transverseCoord, Complex.sub_re, Complex.sub_im] at hs ht ⊢
      · linarith
      · linarith
    have hsource := (deformation_reflectsAxisCoset P phi hphi axis a_s a_t hm').mpr htarget
    simpa [a_s, a_t, sourceGeometryCentreVertex, Axis.transverseCoord,
      Complex.sub_re, Complex.sub_im] using hsource
  have path_trans : ∀ {x y : Tiling.Plane}
      (hp : Relation.ReflTransGen
        (fun u v : Tiling.Plane ↦ u ∈ U ∧ v ∈ U ∧ dist u v < G) x y),
      ∀ hx : x ∈ U, ∀ hy : y ∈ U,
        axis.transverseCoord (sourceAt ⟨x, hx⟩ : Tiling.Plane) =
          axis.transverseCoord (sourceAt ⟨y, hy⟩ : Tiling.Plane) := by
    intro x y hp
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl => intro hx hy; rfl
    | head edge htail ih =>
        intro hx hy
        rcases edge with ⟨hxmid, hymid, hdist⟩
        have hst : dist (sourceAt ⟨_, hxmid⟩ : Tiling.Plane)
            (sourceAt ⟨_, hymid⟩ : Tiling.Plane) < G := by
          simpa only [sourceAt_spec] using hdist
        have hz := edge_trans hst
        have heq : axis.transverseCoord (sourceAt ⟨_, hxmid⟩ : Tiling.Plane) =
            axis.transverseCoord (sourceAt ⟨_, hymid⟩ : Tiling.Plane) := by
          cases axis <;> simp only [Axis.transverseCoord, Complex.sub_re, Complex.sub_im] at hz ⊢
          · linarith
          · linarith
        exact heq.trans (ih hymid hy)
  obtain ⟨s₀, hs₀⟩ := hSne
  refine ⟨⟨axis.transverseCoord (s₀ : Tiling.Plane), ?_⟩, ?_⟩
  · intro p hp
    rcases hp with ⟨s, hs, rfl⟩
    let s₀' : ↥S := ⟨s₀, hs₀⟩
    let s' : ↥S := ⟨s, hs⟩
    have hp_path := hconn (s₀' : Tiling.Plane) ⟨s₀', s₀'.2, rfl⟩
      (s' : Tiling.Plane) ⟨s', s'.2, rfl⟩
    have htr := path_trans hp_path ⟨s₀', s₀'.2, rfl⟩ ⟨s', s'.2, rfl⟩
    have hfirst : sourceAt ⟨(s₀' : Tiling.Plane), ⟨s₀', s₀'.2, rfl⟩⟩ = s₀' := by
      apply Subtype.ext
      apply Subtype.ext
      exact sourceAt_spec _
    have hlast : sourceAt ⟨(s' : Tiling.Plane), ⟨s', s'.2, rfl⟩⟩ = s' := by
      apply Subtype.ext
      apply Subtype.ext
      exact sourceAt_spec _
    have hsource : axis.transverseCoord (s₀' : Tiling.Plane) =
        axis.transverseCoord (s' : Tiling.Plane) := by simpa [hfirst, hlast] using htr
    exact hsource.symm
  · intro x
    let d := axis.coord (alpha : Tiling.Plane)
    have hd_ne : d ≠ 0 := by
      dsimp [d]
      cases axis with
      | horizontal =>
        change alpha.1.im = 0 at halpha_axis
        change alpha.1.re ≠ 0
        intro h
        apply halpha_ne
        apply Complex.ext <;> assumption
      | vertical =>
        change alpha.1.re = 0 at halpha_axis
        change alpha.1.im ≠ 0
        intro h
        apply halpha_ne
        apply Complex.ext <;> assumption
    let beta : Tiling.Plane := if 0 < d then alpha else -alpha
    have hbeta_coord : axis.coord beta = |d| := by
      dsimp [beta]
      split_ifs with h
      · simp [d, abs_of_pos h]
      · have hneg : d < 0 := lt_of_le_of_ne (le_of_not_gt h) hd_ne
        have hcoord_neg : axis.coord (-((alpha : Tiling.Plane))) = -d := by
          cases axis <;> simp [d, Axis.coord, Complex.neg_re, Complex.neg_im]
        rw [hcoord_neg, abs_of_neg hneg]
    have hbeta_period : beta +ᵥ U = U := by
      by_cases hpos : 0 < d
      · simpa [beta, hpos] using halpha_set
      · have hneg_period : (-((alpha : Tiling.Plane)) +ᵥ U) = U := by
          have hinverse (z : Tiling.Plane) (hz : z ∈ U) : -alpha + z ∈ U := by
            have hmem : z ∈ (alpha : Tiling.Plane) +ᵥ U :=
              (Set.ext_iff.mp halpha_set z).mpr hz
            rcases hmem with ⟨w, hw, hzw⟩
            have haux : -alpha + z = w := by
              rw [← hzw]
              simp [vadd_eq_add]
            simpa [haux] using hw
          ext z
          constructor
          · rintro ⟨w, hw, rfl⟩
            exact hinverse w hw
          · intro hz
            refine ⟨alpha + z, ?_, ?_⟩
            · exact (Set.ext_iff.mp halpha_set (alpha + z)).mp ⟨z, hz, rfl⟩
            · simp
        simpa [beta, hpos] using hneg_period
    have hnegative_period : (-beta) +ᵥ U = U := by
      have hinverse (z : Tiling.Plane) (hz : z ∈ U) : -beta + z ∈ U := by
        have hmem : z ∈ beta +ᵥ U := (Set.ext_iff.mp hbeta_period z).mpr hz
        rcases hmem with ⟨w, hw, hzw⟩
        have haux : -beta + z = w := by
          rw [← hzw]
          simp [vadd_eq_add]
        simpa [haux] using hw
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hinverse w hw
      · intro hz
        refine ⟨beta + z, ?_, ?_⟩
        · exact (Set.ext_iff.mp hbeta_period (beta + z)).mp ⟨z, hz, rfl⟩
        · simp
    have forward_iter (v : Tiling.Plane) (hv : v ∈ U) :
        ∀ n : ℕ, (n • beta) + v ∈ U := by
      intro n
      induction n with
      | zero => simpa using hv
      | succ n ih =>
          have hstep : beta + ((n • beta) + v) ∈ U :=
            (Set.ext_iff.mp hbeta_period _).mp ⟨(n • beta) + v, ih, rfl⟩
          have heq : beta + ((n • beta) + v) = ((n + 1) • beta) + v := by
            apply Complex.ext <;> simp [Complex.add_re, Complex.add_im] <;> ring
          rw [← heq]
          exact hstep
    have backward_iter (v : Tiling.Plane) (hv : v ∈ U) :
        ∀ n : ℕ, (n • (-beta)) + v ∈ U := by
      intro n
      induction n with
      | zero => simpa using hv
      | succ n ih =>
          have hstep : -beta + ((n • (-beta)) + v) ∈ U :=
            (Set.ext_iff.mp hnegative_period _).mp ⟨(n • (-beta)) + v, ih, rfl⟩
          have heq : -beta + ((n • (-beta)) + v) = ((n + 1) • (-beta)) + v := by
            apply Complex.ext <;> simp [Complex.add_re, Complex.add_im] <;> ring
          rw [← heq]
          exact hstep
    have hdelta : 0 < |d| := abs_pos.mpr hd_ne
    have hcoord_add (u v : Tiling.Plane) : axis.coord (u + v) =
        axis.coord u + axis.coord v := by
      cases axis <;> simp [Axis.coord, Complex.add_re, Complex.add_im]
    have hcoord_n (n : ℕ) (v : Tiling.Plane) :
        axis.coord (n • v) = (n : ℝ) * axis.coord v := by
      induction n with
      | zero => cases axis <;> simp [Axis.coord]
      | succ n ih =>
          rw [succ_nsmul, hcoord_add, ih]
          push_cast
          ring_nf
    have hbaseU : (s₀ : Tiling.Plane) ∈ U := ⟨s₀, hs₀, rfl⟩
    obtain ⟨nleft, hnleft⟩ := exists_nat_gt ((axis.coord (s₀ : Tiling.Plane) - x) / |d|)
    obtain ⟨nright, hnright⟩ := exists_nat_gt ((x - axis.coord (s₀ : Tiling.Plane)) / |d|)
    have hleft_coord : axis.coord ((nleft • (-beta)) + (s₀ : Tiling.Plane)) < x := by
      have hlarge : (axis.coord (s₀ : Tiling.Plane) - x) < (nleft : ℝ) * |d| := by
        have := mul_lt_mul_of_pos_right hnleft hdelta
        nlinarith [div_mul_cancel₀ (axis.coord (s₀ : Tiling.Plane) - x) (ne_of_gt hdelta)]
      have hformula : axis.coord ((nleft • (-beta)) + (s₀ : Tiling.Plane)) =
          axis.coord (s₀ : Tiling.Plane) - (nleft : ℝ) * |d| := by
        have hcoord_neg : axis.coord (-beta) = -axis.coord beta := by
          cases axis <;> simp [Axis.coord]
        calc
          axis.coord ((nleft • (-beta)) + (s₀ : Tiling.Plane)) =
              axis.coord (nleft • (-beta)) + axis.coord (s₀ : Tiling.Plane) :=
                hcoord_add _ _
          _ = (nleft : ℝ) * axis.coord (-beta) + axis.coord (s₀ : Tiling.Plane) := by
                rw [hcoord_n _ (-beta)]
          _ = axis.coord (s₀ : Tiling.Plane) - (nleft : ℝ) * |d| := by
                rw [hcoord_neg, hbeta_coord]
                ring
      rw [hformula]
      linarith
    have hright_coord : x < axis.coord ((nright • beta) + (s₀ : Tiling.Plane)) := by
      have hlarge : (x - axis.coord (s₀ : Tiling.Plane)) < (nright : ℝ) * |d| := by
        have := mul_lt_mul_of_pos_right hnright hdelta
        nlinarith [div_mul_cancel₀ (x - axis.coord (s₀ : Tiling.Plane)) (ne_of_gt hdelta)]
      have hformula : axis.coord ((nright • beta) + (s₀ : Tiling.Plane)) =
          (nright : ℝ) * |d| + axis.coord (s₀ : Tiling.Plane) := by
        calc
          axis.coord ((nright • beta) + (s₀ : Tiling.Plane)) =
              axis.coord (nright • beta) + axis.coord (s₀ : Tiling.Plane) :=
                hcoord_add _ _
          _ = (nright : ℝ) * axis.coord beta + axis.coord (s₀ : Tiling.Plane) := by
                rw [hcoord_n _ beta]
          _ = (nright : ℝ) * |d| + axis.coord (s₀ : Tiling.Plane) := by rw [hbeta_coord]
      rw [hformula]
      linarith
    have hleft_mem : (nleft • (-beta)) + (s₀ : Tiling.Plane) ∈ U :=
      backward_iter _ hbaseU nleft
    have hright_mem : (nright • beta) + (s₀ : Tiling.Plane) ∈ U :=
      forward_iter _ hbaseU nright
    obtain ⟨z, hzU, hzleft, hzright⟩ := sourceGeometry_linked_path_near hG axis
      (hconn _ hleft_mem _ hright_mem) hleft_mem hright_mem hleft_coord.le hright_coord.le
    refine ⟨axis.coord z, ⟨z, hzU, rfl⟩, ?_, ?_⟩
    · linarith [hzleft]
    · linarith [hzright]

private theorem longComponentLength_reflects
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) {R : ℝ}
    (massExpression : FiniteCombinationData C R)
    (corrections : Finset (FiniteCombinationData C R))
    (W : ℕ) (K : ℕ) (B : ℝ) (mu : ℝ) :
    massExpression.value = A.massScalar → massExpression.weight ≤ W →
    0 < A.mass → A.mass < B →
    (∀ E ∈ corrections, E.weight ≤ W ∧ |(E.value : ℝ)| < B / 2) →
    (4 * B / A.mass < K) →
    0 < mu →
    (∀ (q : ℤ) (c c' : FiniteCombinationData C R),
      q.natAbs < K → c ∈ corrections → c' ∈ corrections →
      (q : ℝ) * A.mass + c.value - c'.value ≠ 0 →
      mu ≤ |(q : ℝ) * A.mass + c.value - c'.value|) →
    ∀ (P : FLCControlPackage C),
      R < P.controlRadius →
      ((K : ℝ) + 2) * (W : ℝ) / P.scale <
        min (A.mass / 2) (min (B / 2) mu) →
      ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
        IsEpsilonApproximation C P.threshold phi →
        ∀ (k k' : ℕ) (c c' : FiniteCombinationData C R),
          c ∈ corrections → c' ∈ corrections →
          (k : ℝ) * mapScalar phi A.massScalar + c.mappedValue phi =
            (k' : ℝ) * mapScalar phi A.massScalar + c'.mappedValue phi →
          (k : ℝ) * A.mass + c.value = (k' : ℝ) * A.mass + c'.value := by
  intro hmassExpr hmassWeight hmass hB hcorr hK hmu hseparate P hR hscale phi hphi
    k k' c c' hc hc' heq
  let e : ℝ := (W : ℝ) / P.scale
  have he_nonneg : 0 ≤ e := by
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt P.scale_pos)
  have hscalePieces := (lt_min_iff.mp hscale)
  have hscaleTail := (lt_min_iff.mp hscalePieces.2)
  have hscaleMass : ((K : ℝ) + 2) * e < A.mass / 2 := by
    have hmulDiv : ((K : ℝ) + 2) * e = ((K : ℝ) + 2) * (W : ℝ) / P.scale := by
      dsimp [e]
      ring
    rw [hmulDiv]
    exact hscalePieces.1
  have hscaleB : ((K : ℝ) + 2) * e < B / 2 := by
    have hmulDiv : ((K : ℝ) + 2) * e = ((K : ℝ) + 2) * (W : ℝ) / P.scale := by
      dsimp [e]
      ring
    rw [hmulDiv]
    exact hscaleTail.1
  have he_lt : (K : ℝ) * e + 2 * e < mu := by
    have hmulDiv : ((K : ℝ) + 2) * e = ((K : ℝ) + 2) * (W : ℝ) / P.scale := by
      dsimp [e]
      ring
    calc
      (K : ℝ) * e + 2 * e = ((K : ℝ) + 2) * e := by ring
      _ = ((K : ℝ) + 2) * (W : ℝ) / P.scale := hmulDiv
      _ < mu := hscaleTail.2
  have he_lt_halfMass : e < A.mass / 2 := by
    have hKpos : 0 < (K : ℝ) + 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right (show 1 ≤ (K : ℝ) + 2 by linarith)
      he_nonneg
    nlinarith [hscaleMass]
  have he_lt_halfB : e < B / 2 := by
    have hKpos : 0 < (K : ℝ) + 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right (show 1 ≤ (K : ℝ) + 2 by linarith)
      he_nonneg
    nlinarith [hscaleB]
  have hmassMap : massExpression.mappedValue phi = mapScalar phi A.massScalar := by
    simp [FiniteCombinationData.mappedValue, mapScalar, ← hmassExpr,
      massExpression.value_eq, map_sum, map_smul, Rat.cast_sum, Rat.cast_mul]
  have hmassErr := finiteCombination_mapped_error P hR phi hphi massExpression
  have hmassErr' : |mapScalar phi A.massScalar - A.mass| ≤ e := by
    calc
      |mapScalar phi A.massScalar - A.mass| =
          |massExpression.mappedValue phi - (massExpression.value : ℝ)| := by
        have hmval : (massExpression.value : ℝ) = A.mass := by
          rw [hmassExpr, A.massScalar_coe]
        rw [hmassMap, ← hmassExpr, hmval]
      _ ≤ (massExpression.weight : ℝ) / P.scale := hmassErr
      _ ≤ e := by
        dsimp [e]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hmassWeight)
          (le_of_lt P.scale_pos)
  have hmassMap_pos : 0 < mapScalar phi A.massScalar := by
    have hbounds := abs_le.mp hmassErr'
    dsimp [e] at hbounds
    linarith
  have hcErr := finiteCombination_mapped_error P hR phi hphi c
  have hc'Err := finiteCombination_mapped_error P hR phi hphi c'
  have hcErrBound : |c.mappedValue phi - (c.value : ℝ)| ≤ e := by
    calc
      |c.mappedValue phi - (c.value : ℝ)| ≤ (c.weight : ℝ) / P.scale := hcErr
      _ ≤ e := by
        dsimp [e]
        exact div_le_div_of_nonneg_right (by exact_mod_cast (hcorr c hc).1)
          (le_of_lt P.scale_pos)
  have hc'ErrBound : |c'.mappedValue phi - (c'.value : ℝ)| ≤ e := by
    calc
      |c'.mappedValue phi - (c'.value : ℝ)| ≤ (c'.weight : ℝ) / P.scale := hc'Err
      _ ≤ e := by
        dsimp [e]
        exact div_le_div_of_nonneg_right (by exact_mod_cast (hcorr c' hc').1)
          (le_of_lt P.scale_pos)
  have hcMap_lt : |c.mappedValue phi| < B := by
    have hval := (hcorr c hc).2
    have hbound := abs_le.mp hcErrBound
    calc
      |c.mappedValue phi| = |(c.mappedValue phi - (c.value : ℝ)) + (c.value : ℝ)| := by
        congr 1
        ring
      _ ≤ |c.mappedValue phi - (c.value : ℝ)| + |(c.value : ℝ)| := abs_add_le _ _
      _ < B := by linarith
  have hc'Map_lt : |c'.mappedValue phi| < B := by
    have hval := (hcorr c' hc').2
    have hbound := abs_le.mp hc'ErrBound
    calc
      |c'.mappedValue phi| = |(c'.mappedValue phi - (c'.value : ℝ)) + (c'.value : ℝ)| := by
        congr 1
        ring
      _ ≤ |c'.mappedValue phi - (c'.value : ℝ)| + |(c'.value : ℝ)| := abs_add_le _ _
      _ < B := by linarith
  let q : ℤ := (k : ℤ) - (k' : ℤ)
  have hbulk : ((k : ℝ) - (k' : ℝ)) * mapScalar phi A.massScalar =
      c'.mappedValue phi - c.mappedValue phi := by
    linear_combination heq
  have hbulkAbs : |(k : ℝ) - (k' : ℝ)| * mapScalar phi A.massScalar < 2 * B := by
    have hEqAbs := congrArg abs hbulk
    rw [abs_mul, abs_of_pos hmassMap_pos] at hEqAbs
    have hright : |c'.mappedValue phi - c.mappedValue phi| < 2 * B := by
      calc
        |c'.mappedValue phi - c.mappedValue phi| =
            |c'.mappedValue phi + -(c.mappedValue phi)| := by congr 1
        _ ≤ |c'.mappedValue phi| + |-(c.mappedValue phi)| := abs_add_le _ _
        _ < 2 * B := by simp only [abs_neg]; linarith
    rw [hEqAbs]
    exact hright
  have hmassMap_lower : A.mass / 2 ≤ mapScalar phi A.massScalar := by
    have hbounds := abs_le.mp hmassErr'
    dsimp [e] at hbounds
    nlinarith [he_lt_halfMass]
  have hbulkHalf : |(k : ℝ) - (k' : ℝ)| * (A.mass / 2) < 2 * B := by
    calc
      |(k : ℝ) - (k' : ℝ)| * (A.mass / 2) ≤
          |(k : ℝ) - (k' : ℝ)| * mapScalar phi A.massScalar :=
        mul_le_mul_of_nonneg_left hmassMap_lower
          (abs_nonneg _)
      _ < 2 * B := hbulkAbs
  have hbulkMass : |(k : ℝ) - (k' : ℝ)| * A.mass < 4 * B := by
    calc
      |(k : ℝ) - (k' : ℝ)| * A.mass =
          2 * (|(k : ℝ) - (k' : ℝ)| * (A.mass / 2)) := by ring
      _ < 2 * (2 * B) := mul_lt_mul_of_pos_left hbulkHalf (by norm_num)
      _ = 4 * B := by ring
  have hqabs : (q.natAbs : ℝ) = |(k : ℝ) - (k' : ℝ)| := by
    simp [q, Nat.cast_natAbs, Int.cast_abs]
  have hqsmall : q.natAbs < K := by
    have hqreal : (q.natAbs : ℝ) < K := by
      rw [hqabs]
      exact (lt_div_iff₀ hmass).2 hbulkMass |>.trans hK
    exact_mod_cast hqreal
  have hqmul : (q : ℝ) = (k : ℝ) - (k' : ℝ) := by
    simp [q]
  have hmappedZero : (q : ℝ) * mapScalar phi A.massScalar +
      c.mappedValue phi - c'.mappedValue phi = 0 := by
    rw [hqmul]
    linear_combination heq
  have hmassErr'' : |(A.mass : ℝ) - mapScalar phi A.massScalar| ≤ e := by
    simpa [abs_sub_comm] using hmassErr'
  have hcErr'' : |(c.value : ℝ) - c.mappedValue phi| ≤ e := by
    simpa [abs_sub_comm] using hcErrBound
  have hc'Err'' : |c'.mappedValue phi - (c'.value : ℝ)| ≤ e := hc'ErrBound
  have hexpr : (q : ℝ) * A.mass + c.value - c'.value =
      (q : ℝ) * (A.mass - mapScalar phi A.massScalar) +
        ((c.value : ℝ) - c.mappedValue phi) +
        (c'.mappedValue phi - (c'.value : ℝ)) := by
    calc
      _ = ((q : ℝ) * A.mass + c.value - c'.value) -
          ((q : ℝ) * mapScalar phi A.massScalar + c.mappedValue phi - c'.mappedValue phi) := by
        rw [hmappedZero]
        ring
      _ = _ := by ring
  have hexpr_small : |(q : ℝ) * A.mass + c.value - c'.value| < mu := by
    rw [hexpr]
    calc
      |(q : ℝ) * (A.mass - mapScalar phi A.massScalar) +
          ((c.value : ℝ) - c.mappedValue phi) +
          (c'.mappedValue phi - (c'.value : ℝ))|
          ≤ |(q : ℝ) * (A.mass - mapScalar phi A.massScalar)| +
            |(c.value : ℝ) - c.mappedValue phi| +
            |c'.mappedValue phi - (c'.value : ℝ)| := by
        have htriOuter := abs_add_le
          ((q : ℝ) * (A.mass - mapScalar phi A.massScalar) +
            ((c.value : ℝ) - c.mappedValue phi))
          (c'.mappedValue phi - (c'.value : ℝ))
        have htriInner := abs_add_le
          ((q : ℝ) * (A.mass - mapScalar phi A.massScalar))
          ((c.value : ℝ) - c.mappedValue phi)
        calc
          _ ≤ |(q : ℝ) * (A.mass - mapScalar phi A.massScalar) +
              ((c.value : ℝ) - c.mappedValue phi)| +
              |c'.mappedValue phi - (c'.value : ℝ)| := htriOuter
          _ ≤ |(q : ℝ) * (A.mass - mapScalar phi A.massScalar)| +
              |(c.value : ℝ) - c.mappedValue phi| +
              |c'.mappedValue phi - (c'.value : ℝ)| :=
            add_le_add_left htriInner _
      _ ≤ (q.natAbs : ℝ) * e + e + e := by
        have hqabsCast : |(q : ℝ)| = (q.natAbs : ℝ) := by
          rw [hqmul, ← hqabs]
        rw [abs_mul, hqabsCast]
        have hmassprod := mul_le_mul_of_nonneg_left hmassErr'' (Nat.cast_nonneg q.natAbs)
        exact add_le_add (add_le_add hmassprod hcErr'') hc'Err''
      _ ≤ (K : ℝ) * e + 2 * e := by
        have hqcast : (q.natAbs : ℝ) < K := by exact_mod_cast hqsmall
        have hnonstrict := mul_le_mul_of_nonneg_right (le_of_lt hqcast) he_nonneg
        linarith
      _ < mu := he_lt
  by_contra hne
  have hnonzero : (q : ℝ) * A.mass + c.value - c'.value ≠ 0 := by
    intro hz
    apply hne
    have hz' := hz
    rw [hqmul] at hz'
    linear_combination hz'
  have hsep := hseparate q c c' hqsmall hc hc' hnonzero
  linarith

/- Concrete private records for the remaining genuine trace stages.  Trace unions
are literal expressions; the shared FilledSliceChains point provider is reused. -/

private structure SectionEndpointLabel {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) where
  interval : Fin A.raw.presentation.n
  isRight : Bool

private def SectionEndpointLabel.vertex {C : ApproximationContext.{0}} {axis : Axis}
    {A : NormalizedGenericSection C axis} (e : SectionEndpointLabel A) :
    ↥C.region.vertices :=
  if e.isRight then A.raw.rightVertex e.interval else A.raw.leftVertex e.interval

private def SectionEndpointLabel.rawValue {C : ApproximationContext.{0}} {axis : Axis}
    {A : NormalizedGenericSection C axis} (e : SectionEndpointLabel A) : ℝ :=
  if e.isRight then A.raw.presentation.right e.interval else A.raw.presentation.left e.interval

private structure IndexedSectionEndpoint {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) (S : Set ↥C.centres) where
  label : SectionEndpointLabel A
  centre : S

private def IndexedSectionEndpoint.sourceValue {C : ApproximationContext.{0}} {axis : Axis}
    {A : NormalizedGenericSection C axis} {S : Set ↥C.centres}
    (e : IndexedSectionEndpoint A S) : ℝ :=
  e.label.rawValue + axis.coord e.centre.1.1 - A.origin

private def IndexedSectionEndpoint.targetValue {C : ApproximationContext.{0}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ} {D : CoordinateDeformation C phi}
    {Tphi : ↥C.centres ↪ Tiling.Plane} {axis : Axis}
    {A : NormalizedGenericSection C axis} {S : Set ↥C.centres}
    (e : IndexedSectionEndpoint A S) : ℝ :=
  axis.coord (D.planarHomeomorph e.label.vertex.1 + Tphi e.centre.1) -
    mapScalar phi A.originScalar

private structure BoundedOccupiedTraceComponent
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) (S : Set Tiling.Plane) where
  left : ℝ
  right : ℝ
  ordered : left < right
  component_eq : connectedComponentIn
      (interior (closure (A.carrier + axis.coord '' S)))
      ((left + right) / 2) = Set.Ioo left right
  midpoint_mem : (left + right) / 2 ∈ interior (closure (A.carrier + axis.coord '' S))

private def bulkCentres {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) (S : Set Tiling.Plane)
    (J : BoundedOccupiedTraceComponent A S) : Set Tiling.Plane :=
  {s ∈ S | convexHull ℝ ((axis.coord s) +ᵥ closure A.carrier) ⊆ Set.Ioo J.left J.right}

private structure ComponentMassCode {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) (S : Set Tiling.Plane)
    (J : BoundedOccupiedTraceComponent A S) (R : ℝ) where
  bulk : Finset Tiling.Plane
  bulk_coe : (bulk : Set Tiling.Plane) = bulkCentres A S J
  correction : FiniteCombinationData C R
  correction_nonneg : 0 ≤ (correction.value : ℝ)
  length_eq : J.right - J.left = (bulk.card : ℝ) * A.mass + correction.value

private structure AllEndpointWeakOrderTransport
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (axis : Axis) (S : Set ↥C.centres)
    (A : NormalizedGenericSection C axis) where
  indexedCentre_formula : ∀ t,
    Tphi t = mapPoint phi (C.centrePoint t.1 t.2)
  weakOrder_iff : ∀ e f : IndexedSectionEndpoint A S,
    e.sourceValue ≤ f.sourceValue ↔
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ≤
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f
  source_interval : ∀ (i : Fin A.raw.presentation.n) (s : S),
    Set.Ioo
      ((IndexedSectionEndpoint.mk ⟨i, false⟩ s).sourceValue)
      ((IndexedSectionEndpoint.mk ⟨i, true⟩ s).sourceValue) =
      (-A.origin + axis.coord s.1.1) +ᵥ
        Set.Ioo (A.raw.presentation.left i) (A.raw.presentation.right i)
  target_interval : ∀ (i : Fin A.raw.presentation.n) (s : S),
    Set.Ioo
      (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
        (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
      (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
        (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) =
      (axis.coord (Tphi s.1) - mapScalar phi A.originScalar) +ᵥ
        Set.Ioo
          (axis.coord (D.planarHomeomorph (A.raw.leftVertex i).1))
          (axis.coord (D.planarHomeomorph (A.raw.rightVertex i).1))
  source_union_eq : interior (closure (A.carrier + axis.coord '' (Subtype.val '' S))) =
    interior (closure (⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
      Set.Ioo
        ((IndexedSectionEndpoint.mk ⟨i, false⟩ s).sourceValue)
        ((IndexedSectionEndpoint.mk ⟨i, true⟩ s).sourceValue)))
  target_union_eq :
    interior (closure (⋃ s : deformedCenterCarrierOn Tphi S,
      axis.coord s +ᵥ {x : ℝ | FilledSliceChains.slicePoint axis
        (axis.transverseCoord (D.planarHomeomorph
          (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
            D.deformedRegion.openCarrier})) =
    (mapScalar phi A.originScalar) +ᵥ
    interior (closure (⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
      Set.Ioo
        (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
        (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, true⟩ s))))
  sourceValues_locallyFinite : ∀ a b : ℝ,
    ({x | ∃ e : IndexedSectionEndpoint A S, e.sourceValue = x} ∩
      Set.Icc a b).Finite
  targetValues_locallyFinite : ∀ a b : ℝ,
    ({x | ∃ e : IndexedSectionEndpoint A S,
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e = x} ∩
      Set.Icc a b).Finite
  source_frontier_subset : frontier
      (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S)))) ⊆
    {x | ∃ e : IndexedSectionEndpoint A S, e.sourceValue = x}
  target_frontier_subset : frontier
      ((-mapScalar phi A.originScalar) +ᵥ
        interior (closure (⋃ s : deformedCenterCarrierOn Tphi S,
          axis.coord s +ᵥ {x : ℝ | FilledSliceChains.slicePoint axis
            (axis.transverseCoord (D.planarHomeomorph
              (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
                D.deformedRegion.openCarrier}))) ⊆
    {x | ∃ e : IndexedSectionEndpoint A S,
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e = x}

private noncomputable def finiteCombinationOfFamily
    {C : ApproximationContext.{0}} {R : ℝ} {ι : Type*} [Fintype ι]
    (atom : ι → ControlledDifference C R) (coeff : ι → ℤ) :
    FiniteCombinationData C R where
  numberOfTerms := Fintype.card ι
  term := fun i => atom ((Fintype.equivFin ι).symm i)
  coefficient := fun i => coeff ((Fintype.equivFin ι).symm i)
  value := ∑ i : ι, (coeff i : ℚ) • (atom i).scalar
  value_eq := by
    apply Fintype.sum_equiv (Fintype.equivFin ι)
    intro i
    simp only [Equiv.symm_apply_apply]
  weight := ∑ i : ι, (coeff i).natAbs
  weight_eq := by
    apply Fintype.sum_equiv (Fintype.equivFin ι)
    intro i
    simp only [Equiv.symm_apply_apply]

private theorem normalized_subfamilyMassExpressions_exists
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) :
    ∃ R > 0,
      ∃ atom : {u : Finset (Fin A.raw.presentation.n) // u.Nonempty} →
        ControlledDifference C R,
      ∀ selected : Finset (Fin A.raw.presentation.n),
        ∃ coeff : {u : Finset (Fin A.raw.presentation.n) // u.Nonempty} → ℤ,
          (∀ u, -1 ≤ coeff u ∧ coeff u ≤ 1) ∧
          ((finiteCombinationOfFamily atom coeff).value : ℝ) =
            volume.real (⋃ i ∈ selected,
              Set.Ioo (A.raw.presentation.left i) (A.raw.presentation.right i)) := by
  classical
  let P := A.raw.presentation
  let U := {u : Finset (Fin P.n) // u.Nonempty}
  let R := Metric.diam C.region.support + 1
  have hR : 0 < R := by
    dsimp [R]
    linarith [region_support_diam_pos C.region]
  let leftIndex (u : U) : Fin P.n :=
    Classical.choose (Finset.exists_mem_eq_sup' u.2 P.left)
  let rightIndex (u : U) : Fin P.n :=
    Classical.choose (Finset.exists_mem_eq_inf' u.2 P.right)
  have leftIndex_spec (u : U) :
      leftIndex u ∈ u.1 ∧ u.1.sup' u.2 P.left = P.left (leftIndex u) :=
    Classical.choose_spec (Finset.exists_mem_eq_sup' u.2 P.left)
  have rightIndex_spec (u : U) :
      rightIndex u ∈ u.1 ∧ u.1.inf' u.2 P.right = P.right (rightIndex u) :=
    Classical.choose_spec (Finset.exists_mem_eq_inf' u.2 P.right)
  let leftVertex (u : U) : ↥C.translatedVertices :=
    ⟨A.raw.leftVertex (leftIndex u),
      ⟨A.raw.leftVertex (leftIndex u), (A.raw.leftVertex (leftIndex u)).2,
        0, C.zero_mem_centres, add_zero _⟩⟩
  let rightVertex (u : U) : ↥C.translatedVertices :=
    ⟨A.raw.rightVertex (rightIndex u),
      ⟨A.raw.rightVertex (rightIndex u), (A.raw.rightVertex (rightIndex u)).2,
        0, C.zero_mem_centres, add_zero _⟩⟩
  have hsupport (v : ↥C.region.vertices) : v.1 ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier C.region v.2)
  have hclose (u : U) : dist (rightVertex u).1 (leftVertex u).1 < R := by
    have hdiam := Metric.dist_le_diam_of_mem C.region.isPolygonal.isCompact.isBounded
      (hsupport (A.raw.rightVertex (rightIndex u)))
      (hsupport (A.raw.leftVertex (leftIndex u)))
    change dist (A.raw.rightVertex (rightIndex u)).1
      (A.raw.leftVertex (leftIndex u)).1 < Metric.diam C.region.support + 1
    linarith
  let atom (u : U) : ControlledDifference C R := {
    axis := axis
    left := leftVertex u
    right := rightVertex u
    close := hclose u
    scalar := C.translatedDifferenceScalar axis (rightVertex u) (leftVertex u)
    scalar_eq := rfl }
  have atom_value (u : U) : ((atom u).scalar : ℝ) =
      P.right (rightIndex u) - P.left (leftIndex u) := by
    change (C.translatedDifferenceScalar axis (rightVertex u) (leftVertex u) : ℝ) = _
    cases axis <;> simp only [ApproximationContext.translatedDifferenceScalar,
      rightVertex, leftVertex, Complex.sub_re, Complex.sub_im]
    · exact congrArg₂ (· - ·) (A.raw.rightVertex_coord (rightIndex u))
        (A.raw.leftVertex_coord (leftIndex u))
    · exact congrArg₂ (· - ·) (A.raw.rightVertex_coord (rightIndex u))
        (A.raw.leftVertex_coord (leftIndex u))
  have intersection_eq (u : U) :
      (⋂ i ∈ u.1, Set.Ioo (P.left i) (P.right i)) =
        Set.Ioo (P.left (leftIndex u)) (P.right (rightIndex u)) := by
    ext x
    constructor
    · intro hx
      have hxall := Set.mem_iInter₂.mp hx
      exact ⟨(hxall _ (leftIndex_spec u).1).1,
        (hxall _ (rightIndex_spec u).1).2⟩
    · intro hx
      apply Set.mem_iInter₂.mpr
      intro i hi
      have hl := Finset.le_sup' P.left hi
      have hr := Finset.inf'_le P.right hi
      rw [(leftIndex_spec u).2] at hl
      rw [(rightIndex_spec u).2] at hr
      exact ⟨hl.trans_lt hx.1, hx.2.trans_le hr⟩
  refine ⟨R, hR, atom, ?_⟩
  intro selected
  let coeff (u : U) : ℤ :=
    if u.1 ⊆ selected ∧ P.left (leftIndex u) < P.right (rightIndex u)
      then (-1 : ℤ) ^ (u.1.card + 1) else 0
  refine ⟨coeff, ?_, ?_⟩
  · intro u
    dsimp only [coeff]
    split_ifs
    · rcases neg_one_pow_eq_or ℤ (u.1.card + 1) with h | h <;> rw [h] <;> norm_num
    · norm_num
  · have contribution (u : U) :
        (coeff u : ℝ) * ((atom u).scalar : ℝ) =
          if u.1 ⊆ selected then
            (-1 : ℝ) ^ (u.1.card + 1) *
              volume.real (⋂ i ∈ u.1, Set.Ioo (P.left i) (P.right i)) else 0 := by
      rw [atom_value, intersection_eq, Real.volume_real_Ioo]
      dsimp only [coeff]
      by_cases hu : u.1 ⊆ selected
      · simp only [hu, true_and, ite_true]
        split_ifs with hlt
        · rw [max_eq_left (sub_nonneg.mpr hlt.le)]
          push_cast
          rfl
        · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt hlt))]
          simp
      · simp [hu]
    have hsum := MeasureTheory.measureReal_biUnion_eq_sum_powerset
      (μ := volume) (t := selected)
      (s := fun i : Fin P.n => Set.Ioo (P.left i) (P.right i))
      (fun i _ => measurableSet_Ioo)
      (fun i _ => (Metric.isBounded_Ioo (P.left i) (P.right i)).measure_lt_top.ne)
    have hfilter : (Finset.univ : Finset U).filter (fun u => u.1 ⊆ selected) =
        selected.powerset.subtype (fun u => u.Nonempty) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ((Finset.mem_subtype (p := fun u : Finset (Fin P.n) => u.Nonempty)
        (s := selected.powerset) (a := u)).trans Finset.mem_powerset).symm
    change ((∑ u : U, (coeff u : ℚ) • (atom u).scalar : C.coordinateSpace) : ℝ) = _
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Rat.smul_def]
    push_cast
    simp_rw [contribution]
    rw [← Finset.sum_filter, hfilter]
    exact (Finset.sum_subtype_eq_sum_filter
      (s := selected.powerset)
      (fun u : Finset (Fin P.n) => (-1 : ℝ) ^ (u.card + 1) *
        volume.real (⋂ i ∈ u, Set.Ioo (P.left i) (P.right i)))).trans hsum.symm

private theorem normalized_massExpression_exists
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) :
    ∃ R > 0, ∃ massExpression : FiniteCombinationData C R,
      massExpression.value = A.massScalar := by
  obtain ⟨R, hR, atom, hfamily⟩ := normalized_subfamilyMassExpressions_exists A
  obtain ⟨coeff, _hcoeff, hvalue⟩ := hfamily Finset.univ
  refine ⟨R, hR, finiteCombinationOfFamily atom coeff, ?_⟩
  apply Subtype.ext
  have hmass : ((finiteCombinationOfFamily atom coeff).value : ℝ) = A.mass := by
    rw [A.mass_eq, A.carrier_eq, MeasureTheory.measureReal_def,
      MeasureTheory.measure_vadd, ← MeasureTheory.measureReal_def]
    rw [congrArg volume.real A.raw.presentation.union_eq]
    simpa only [Finset.mem_univ, iUnion_true] using hvalue
  exact hmass.trans A.massScalar_coe.symm

private theorem occupiedComponent_interval_subset
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) {S : Set Tiling.Plane}
    (J : BoundedOccupiedTraceComponent A S) {s : Tiling.Plane} (hs : s ∈ S)
    (i : Fin A.raw.presentation.n)
    (hmeet : (Set.Ioo
      (A.raw.presentation.left i + axis.coord s - A.origin)
      (A.raw.presentation.right i + axis.coord s - A.origin) ∩
        Set.Ioo J.left J.right).Nonempty) :
    Set.Ioo
      (A.raw.presentation.left i + axis.coord s - A.origin)
      (A.raw.presentation.right i + axis.coord s - A.origin) ⊆
        Set.Ioo J.left J.right := by
  let U := interior (closure (A.carrier + axis.coord '' S))
  let l := A.raw.presentation.left i + axis.coord s - A.origin
  let r := A.raw.presentation.right i + axis.coord s - A.origin
  have hraw : Set.Ioo l r ⊆ A.carrier + axis.coord '' S := by
    intro x hx
    refine ⟨x - axis.coord s, ?_, axis.coord s, ⟨s, hs, rfl⟩, by ring⟩
    rw [A.carrier_eq]
    refine ⟨x - axis.coord s + A.origin, ?_, by simp [vadd_eq_add]⟩
    rw [A.raw.presentation.union_eq, Set.mem_iUnion]
    refine ⟨i, ?_⟩
    change l < x ∧ x < r at hx
    dsimp only [l, r] at hx
    constructor <;> linarith [hx.1, hx.2]
  have hU : Set.Ioo l r ⊆ U :=
    interior_maximal (hraw.trans subset_closure) isOpen_Ioo
  obtain ⟨x, hxInterval, hxJ⟩ := hmeet
  have hxComp : x ∈ connectedComponentIn U ((J.left + J.right) / 2) := by
    rw [J.component_eq]
    exact hxJ
  have hcomponent : connectedComponentIn U x =
      connectedComponentIn U ((J.left + J.right) / 2) :=
    (connectedComponentIn_eq hxComp).symm
  have hsubset := isPreconnected_Ioo.subset_connectedComponentIn hxInterval hU
  rw [hcomponent, J.component_eq] at hsubset
  exact hsubset

private theorem sourceEndpointValues_locallyFinite
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres)
    (axis : Axis) (A : NormalizedGenericSection C axis) (S : Set ↥C.centres)
    (hline : ∃ c, ∀ s : S, axis.transverseCoord s.1.1 = c) :
    ∀ a b : ℝ,
      ({x | ∃ e : IndexedSectionEndpoint A S, e.sourceValue = x} ∩
        Set.Icc a b).Finite := by
  intro a b
  have hS : Subtype.val '' S ⊆ C.centres := by
    rintro x ⟨s, _, rfl⟩
    exact s.2
  have hline' : ∃ c, ∀ s ∈ Subtype.val '' S, axis.transverseCoord s = c := by
    obtain ⟨c, hc⟩ := hline
    refine ⟨c, ?_⟩
    rintro x ⟨s, hs, rfl⟩
    exact hc ⟨s, hs⟩
  have offset_finite (p : ℝ) :
      ({x | ∃ s : S, p + axis.coord s.1.1 - A.origin = x} ∩ Set.Icc a b).Finite := by
    have hfin := aligned_coordinate_boundedWindowFinite hT axis hS hline'
      (Set.Icc (a - p + A.origin) (b - p + A.origin))
        (Metric.isBounded_Icc _ _)
    apply (hfin.image (fun y => p + y - A.origin)).subset
    rintro x ⟨⟨s, hs⟩, hx⟩
    refine ⟨axis.coord s.1.1, ⟨⟨s.1.1, ⟨s.1, s.2, rfl⟩, rfl⟩, ?_⟩, hs⟩
    constructor <;> linarith [hx.1, hx.2]
  have hfin :
      (⋃ i : Fin A.raw.presentation.n,
        ({x | ∃ s : S, A.raw.presentation.left i + axis.coord s.1.1 - A.origin = x} ∩
          Set.Icc a b) ∪
        ({x | ∃ s : S, A.raw.presentation.right i + axis.coord s.1.1 - A.origin = x} ∩
          Set.Icc a b)).Finite :=
    Set.finite_iUnion fun i => (offset_finite _).union (offset_finite _)
  apply hfin.subset
  rintro x ⟨⟨⟨⟨i, side⟩, s⟩, he⟩, hx⟩
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  cases side
  · exact Or.inl ⟨⟨s, he⟩, hx⟩
  · exact Or.inr ⟨⟨s, he⟩, hx⟩

private theorem allEndpointWeakOrderTransport_endpoint_eq_iff
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (e f : IndexedSectionEndpoint A S) :
    e.sourceValue = f.sourceValue ↔
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e =
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f := by
  constructor
  · intro h
    apply le_antisymm
    · exact (E.weakOrder_iff e f).mp (le_of_eq h)
    · exact (E.weakOrder_iff f e).mp (le_of_eq h.symm)
  · intro h
    apply le_antisymm
    · exact (E.weakOrder_iff e f).mpr (le_of_eq h)
    · exact (E.weakOrder_iff f e).mpr (le_of_eq h.symm)

private theorem allEndpointWeakOrderTransport_endpoint_lt_iff
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (e f : IndexedSectionEndpoint A S) :
    e.sourceValue < f.sourceValue ↔
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f := by
  constructor
  · intro h
    rcases lt_or_eq_of_le ((E.weakOrder_iff e f).mp h.le) with hlt | heq
    · exact hlt
    · have hreverse : IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f ≤
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e := by
        rw [heq]
      exact ((not_le_of_gt h) ((E.weakOrder_iff f e).mpr hreverse)).elim
  · intro h
    rcases lt_or_eq_of_le ((E.weakOrder_iff e f).mpr h.le) with hlt | heq
    · exact hlt
    · exact False.elim (h.ne ((allEndpointWeakOrderTransport_endpoint_eq_iff E e f).mp heq))

private theorem boundedIntervalComponent_endpoints_frontier
    {U : Set ℝ} {a b : ℝ} (hU : IsOpen U) (hab : a < b)
    (hcomp : connectedComponentIn U ((a + b) / 2) = Set.Ioo a b) :
    a ∈ frontier U ∧ b ∈ frontier U := by
  have hIooU : Set.Ioo a b ⊆ U := by
    rw [← hcomp]
    exact connectedComponentIn_subset U ((a + b) / 2)
  have ha_not : a ∉ U := by
    intro haU
    have hleftOpen : IsOpen (connectedComponentIn U a) := hU.connectedComponentIn
    have hleftNhds : connectedComponentIn U a ∈ 𝓝 a :=
      hleftOpen.mem_nhds (mem_connectedComponentIn haU)
    obtain ⟨x, y, hxy, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hleftNhds
    have hmin : a < min y b := lt_min hxy.2 hab
    let z : ℝ := (a + min y b) / 2
    have hza : a < z := by dsimp [z]; linarith
    have hzy : z < y := by dsimp [z]; linarith [min_le_left y b]
    have hzb : z < b := by dsimp [z]; linarith [min_le_right y b]
    have hzleft : z ∈ connectedComponentIn U a := hsub ⟨by linarith [hxy.1], hzy⟩
    have hzmid : z ∈ connectedComponentIn U ((a + b) / 2) := by
      rw [hcomp]
      exact ⟨hza, hzb⟩
    have hcompEq : connectedComponentIn U a =
        connectedComponentIn U ((a + b) / 2) := by
      calc
        connectedComponentIn U a = connectedComponentIn U z := connectedComponentIn_eq hzleft
        _ = connectedComponentIn U ((a + b) / 2) := (connectedComponentIn_eq hzmid).symm
    have ha_mem : a ∈ connectedComponentIn U a := mem_connectedComponentIn haU
    have ha_mem_mid : a ∈ connectedComponentIn U ((a + b) / 2) := by
      rw [← hcompEq]
      exact ha_mem
    have : a ∈ Set.Ioo a b := by rw [hcomp] at ha_mem_mid; exact ha_mem_mid
    exact lt_irrefl a this.1
  have hb_not : b ∉ U := by
    intro hbU
    have hrightOpen : IsOpen (connectedComponentIn U b) := hU.connectedComponentIn
    have hrightNhds : connectedComponentIn U b ∈ 𝓝 b :=
      hrightOpen.mem_nhds (mem_connectedComponentIn hbU)
    obtain ⟨x, y, hxy, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hrightNhds
    have hmax : max x a < b := max_lt_iff.mpr ⟨hxy.1, hab⟩
    let z : ℝ := (max x a + b) / 2
    have hzx : x < z := by dsimp [z]; linarith [le_max_left x a]
    have hza : a < z := by dsimp [z]; linarith [le_max_right x a]
    have hzb : z < b := by dsimp [z]; linarith
    have hzright : z ∈ connectedComponentIn U b := hsub ⟨hzx, by linarith [hxy.2]⟩
    have hzmid : z ∈ connectedComponentIn U ((a + b) / 2) := by
      rw [hcomp]
      exact ⟨hza, hzb⟩
    have hcompEq : connectedComponentIn U b =
        connectedComponentIn U ((a + b) / 2) := by
      calc
        connectedComponentIn U b = connectedComponentIn U z := connectedComponentIn_eq hzright
        _ = connectedComponentIn U ((a + b) / 2) := (connectedComponentIn_eq hzmid).symm
    have hb_mem : b ∈ connectedComponentIn U b := mem_connectedComponentIn hbU
    have hb_mem_mid : b ∈ connectedComponentIn U ((a + b) / 2) := by
      rw [← hcompEq]
      exact hb_mem
    have : b ∈ Set.Ioo a b := by rw [hcomp] at hb_mem_mid; exact hb_mem_mid
    exact lt_irrefl b this.2
  constructor
  · rw [frontier, Set.mem_sdiff]
    refine ⟨?_, ?_⟩
    · have haClosure : a ∈ closure (Set.Ioo a b) := by
        rw [closure_Ioo hab.ne]
        exact left_mem_Icc.mpr hab.le
      exact closure_mono hIooU haClosure
    · intro haInterior
      exact ha_not (interior_subset haInterior)
  · rw [frontier, Set.mem_sdiff]
    refine ⟨?_, ?_⟩
    · have hbClosure : b ∈ closure (Set.Ioo a b) := by
        rw [closure_Ioo hab.ne]
        exact right_mem_Icc.mpr hab.le
      exact closure_mono hIooU hbClosure
    · intro hbInterior
      exact hb_not (interior_subset hbInterior)

private theorem boundedOccupiedTraceComponent_labelledEndpoints
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S)) :
    ∃ e f : IndexedSectionEndpoint A S,
      e.sourceValue = J.left ∧ f.sourceValue = J.right := by
  have hfront := boundedIntervalComponent_endpoints_frontier
    (U := interior (closure (A.carrier + axis.coord '' (Subtype.val '' S))))
    isOpen_interior J.ordered J.component_eq
  obtain ⟨e, he⟩ := E.source_frontier_subset hfront.1
  obtain ⟨f, hf⟩ := E.source_frontier_subset hfront.2
  exact ⟨e, f, he, hf⟩

private def planeAxisCoordScalar {C : ApproximationContext.{0}}
    (axis : Axis) (p : {z : Tiling.Plane //
      z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}) : C.coordinateSpace :=
  match axis with
  | .horizontal => ⟨p.1.re, p.2.1⟩
  | .vertical => ⟨p.1.im, p.2.2⟩

private theorem planeAxisCoordScalar_coe {C : ApproximationContext.{0}}
    (axis : Axis) (p : {z : Tiling.Plane //
      z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}) :
    (planeAxisCoordScalar axis p : ℝ) = axis.coord p.1 := by
  cases axis <;> rfl

private theorem SectionEndpointLabel.rawValue_eq_vertex_coord
    {C : ApproximationContext.{0}} {axis : Axis}
    {A : NormalizedGenericSection C axis} (e : SectionEndpointLabel A) :
    e.rawValue = axis.coord e.vertex.1 := by
  by_cases h : e.isRight
  · simp [SectionEndpointLabel.rawValue, SectionEndpointLabel.vertex, h,
      A.raw.rightVertex_coord]
  · simp [SectionEndpointLabel.rawValue, SectionEndpointLabel.vertex, h,
      A.raw.leftVertex_coord]

private theorem mapPoint_axisCoord
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (axis : Axis) (p : {z : Tiling.Plane //
      z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}) :
    axis.coord (mapPoint phi p) = mapScalar phi (planeAxisCoordScalar axis p) := by
  cases axis <;> simp [Axis.coord, mapPoint, mapScalar, planeAxisCoordScalar]

private def IndexedSectionEndpoint.sourceCoordScalar
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) {S : Set ↥C.centres}
    (e : IndexedSectionEndpoint A S) : C.coordinateSpace :=
  planeAxisCoordScalar axis
      (C.vertexPoint e.label.vertex.1 e.label.vertex.2) +
    planeAxisCoordScalar axis
      (C.centrePoint e.centre.1.1 e.centre.1.2) - A.originScalar

private theorem IndexedSectionEndpoint.sourceCoordScalar_coe
    {C : ApproximationContext.{0}} {axis : Axis}
    {A : NormalizedGenericSection C axis} {S : Set ↥C.centres}
    (e : IndexedSectionEndpoint A S) :
    (e.sourceCoordScalar A : ℝ) = e.sourceValue := by
  change (planeAxisCoordScalar axis
      (C.vertexPoint e.label.vertex.1 e.label.vertex.2) : ℝ) +
    (planeAxisCoordScalar axis
      (C.centrePoint e.centre.1.1 e.centre.1.2) : ℝ) -
      (A.originScalar : ℝ) = e.sourceValue
  rw [planeAxisCoordScalar_coe, planeAxisCoordScalar_coe, A.originScalar_coe,
    IndexedSectionEndpoint.sourceValue, SectionEndpointLabel.rawValue_eq_vertex_coord]
  rfl

private theorem IndexedSectionEndpoint.sourceCoordScalar_map
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (e : IndexedSectionEndpoint A S) :
    mapScalar phi (e.sourceCoordScalar A) =
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e := by
  have hvertex : mapScalar phi
      (planeAxisCoordScalar axis (C.vertexPoint e.label.vertex.1 e.label.vertex.2)) =
      axis.coord (D.planarHomeomorph e.label.vertex.1) := by
    rw [D.vertex_agreement e.label.vertex.1 e.label.vertex.2]
    exact (mapPoint_axisCoord phi axis
      (C.vertexPoint e.label.vertex.1 e.label.vertex.2)).symm
  have hcentre : mapScalar phi
      (planeAxisCoordScalar axis (C.centrePoint e.centre.1.1 e.centre.1.2)) =
      axis.coord (Tphi e.centre.1) := by
    rw [hTphi e.centre.1]
    exact (mapPoint_axisCoord phi axis
      (C.centrePoint e.centre.1.1 e.centre.1.2)).symm
  have hcoord_add : axis.coord (D.planarHomeomorph e.label.vertex.1 + Tphi e.centre.1) =
      axis.coord (D.planarHomeomorph e.label.vertex.1) + axis.coord (Tphi e.centre.1) := by
    cases axis <;> simp [Axis.coord, Complex.add_re, Complex.add_im]
  have hlinear (x y z : C.coordinateSpace) :
      mapScalar phi (x + y - z) = mapScalar phi x + mapScalar phi y - mapScalar phi z := by
    simp [mapScalar, map_add, map_sub]
  change mapScalar phi
      (planeAxisCoordScalar axis (C.vertexPoint e.label.vertex.1 e.label.vertex.2) +
       planeAxisCoordScalar axis (C.centrePoint e.centre.1.1 e.centre.1.2) - A.originScalar) =
    axis.coord (D.planarHomeomorph e.label.vertex.1 + Tphi e.centre.1) -
      mapScalar phi A.originScalar
  rw [hlinear, hvertex, hcentre, hcoord_add]

private theorem finiteCombination_mappedValue_eq_mapScalar
    {C : ApproximationContext.{0}} {R : ℝ}
    (E : FiniteCombinationData C R) (phi : C.coordinateSpace →ₗ[ℚ] ℚ) :
    E.mappedValue phi = mapScalar phi E.value := by
  rw [FiniteCombinationData.mappedValue, E.value_eq]
  simp only [mapScalar, map_sum, map_smul, Rat.smul_def, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  norm_num

private theorem boundedOccupiedComponent_code_mappedEndpointLength
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S)) {R : ℝ}
    (code : ComponentMassCode A (Subtype.val '' S) J R) :
    ∃ e f : IndexedSectionEndpoint A S,
      e.sourceValue = J.left ∧ f.sourceValue = J.right ∧
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f ∧
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f -
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e =
          (code.bulk.card : ℝ) * mapScalar phi A.massScalar +
            code.correction.mappedValue phi := by
  obtain ⟨e, f, he, hf⟩ := boundedOccupiedTraceComponent_labelledEndpoints E J
  have hsourceDiff_coe :
      ((f.sourceCoordScalar A - e.sourceCoordScalar A : C.coordinateSpace) : ℝ) =
        (code.bulk.card : ℝ) * A.mass + (code.correction.value : ℝ) := by
    rw [Submodule.coe_sub, IndexedSectionEndpoint.sourceCoordScalar_coe,
      IndexedSectionEndpoint.sourceCoordScalar_coe, hf, he]
    exact code.length_eq
  have hcode_coe :
      (((code.bulk.card : ℚ) • A.massScalar + code.correction.value : C.coordinateSpace) : ℝ) =
        (code.bulk.card : ℝ) * A.mass + (code.correction.value : ℝ) := by
    simp [A.massScalar_coe, Rat.smul_def]
  have hsourceDiff : f.sourceCoordScalar A - e.sourceCoordScalar A =
      (code.bulk.card : ℚ) • A.massScalar + code.correction.value := by
    apply Subtype.ext
    calc
      ((f.sourceCoordScalar A - e.sourceCoordScalar A : C.coordinateSpace) : ℝ) =
          (code.bulk.card : ℝ) * A.mass + (code.correction.value : ℝ) := hsourceDiff_coe
      _ = (((code.bulk.card : ℚ) • A.massScalar + code.correction.value :
          C.coordinateSpace) : ℝ) := hcode_coe.symm
  have htargetOrder : IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e <
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f :=
    (allEndpointWeakOrderTransport_endpoint_lt_iff E e f).mp (by rw [he, hf]; exact J.ordered)
  refine ⟨e, f, he, hf, htargetOrder, ?_⟩
  calc
    IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f -
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e =
      mapScalar phi (f.sourceCoordScalar A - e.sourceCoordScalar A) := by
        rw [← IndexedSectionEndpoint.sourceCoordScalar_map E.indexedCentre_formula f,
          ← IndexedSectionEndpoint.sourceCoordScalar_map E.indexedCentre_formula e]
        simp [mapScalar, map_sub]
    _ = mapScalar phi ((code.bulk.card : ℚ) • A.massScalar + code.correction.value) := by
      rw [hsourceDiff]
    _ = (code.bulk.card : ℝ) * mapScalar phi A.massScalar +
        code.correction.mappedValue phi := by
      have hmapadd : mapScalar phi
          ((code.bulk.card : ℚ) • A.massScalar + code.correction.value) =
          mapScalar phi ((code.bulk.card : ℚ) • A.massScalar) +
            mapScalar phi code.correction.value := by
        simp [mapScalar, map_add]
      have hmapsmul : mapScalar phi ((code.bulk.card : ℚ) • A.massScalar) =
          (code.bulk.card : ℝ) * mapScalar phi A.massScalar := by
        simp [mapScalar, map_smul]
      rw [hmapadd, hmapsmul, ← finiteCombination_mappedValue_eq_mapScalar]

private theorem targetEndpointValues_locallyFinite
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (axis : Axis) (A : NormalizedGenericSection C axis) (S : Set ↥C.centres)
    (hpacking : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (deformedCenterCarrierOn Tphi S)))
    (hline : ∃ c, ∀ s : S, axis.transverseCoord (Tphi s.1) = c) :
    ∀ a b : ℝ,
      ({x | ∃ e : IndexedSectionEndpoint A S,
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e = x} ∩
          Set.Icc a b).Finite := by
  intro a b
  obtain ⟨c, hc⟩ := hline
  have hlocal := (Tiling.AxisParallel.IsPacking.locallyFinite_centres hpacking).1
  have offset_finite (p : ℝ) :
      ({x | ∃ s : S, p + axis.coord (Tphi s.1) - mapScalar phi A.originScalar = x} ∩
        Set.Icc a b).Finite := by
    let Q := Set.Icc (a - p + mapScalar phi A.originScalar)
      (b - p + mapScalar phi A.originScalar)
    obtain ⟨R, hR⟩ := (Metric.isBounded_Icc
      (a - p + mapScalar phi A.originScalar)
      (b - p + mapScalar phi A.originScalar)).exists_norm_le
    let B : Set Tiling.Plane := Metric.closedBall 0 (R + |c|)
    have hfinite := hlocal B Metric.isBounded_closedBall
    apply (hfinite.image
      (fun z => p + axis.coord z - mapScalar phi A.originScalar)).subset
    rintro x ⟨⟨s, hs⟩, hx⟩
    refine ⟨Tphi s.1, ⟨⟨s.1, s.2, rfl⟩, ?_⟩, hs⟩
    have hsQ : axis.coord (Tphi s.1) ∈ Q := by
      constructor <;> linarith [hx.1, hx.2]
    have hxR : |axis.coord (Tphi s.1)| ≤ R := by
      simpa only [Real.norm_eq_abs] using hR _ hsQ
    have hsline := hc s
    change dist (Tphi s.1) 0 ≤ R + |c|
    rw [dist_zero_right]
    have hnorm := Complex.norm_le_abs_re_add_abs_im (Tphi s.1)
    cases axis <;> simp only [Axis.coord, Axis.transverseCoord] at hxR hsline
    · rw [hsline] at hnorm
      exact hnorm.trans (by linarith)
    · rw [hsline] at hnorm
      exact hnorm.trans (by linarith)
  have hfin :
      (⋃ i : Fin A.raw.presentation.n,
        ({x | ∃ s : S,
          axis.coord (D.planarHomeomorph (A.raw.leftVertex i).1) +
            axis.coord (Tphi s.1) - mapScalar phi A.originScalar = x} ∩ Set.Icc a b) ∪
        ({x | ∃ s : S,
          axis.coord (D.planarHomeomorph (A.raw.rightVertex i).1) +
            axis.coord (Tphi s.1) - mapScalar phi A.originScalar = x} ∩ Set.Icc a b)).Finite :=
    Set.finite_iUnion fun i => (offset_finite _).union (offset_finite _)
  apply hfin.subset
  rintro x ⟨⟨⟨⟨i, side⟩, s⟩, he⟩, hx⟩
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  cases side
  · left
    refine ⟨⟨s, ?_⟩, hx⟩
    cases axis <;> simpa [IndexedSectionEndpoint.targetValue,
      SectionEndpointLabel.vertex, Axis.coord] using he
  · right
    refine ⟨⟨s, ?_⟩, hx⟩
    cases axis <;> simpa [IndexedSectionEndpoint.targetValue,
      SectionEndpointLabel.vertex, Axis.coord] using he

private theorem boundedCombinationFamily_finite
    {C : ApproximationContext.{0}} {R : ℝ} {ι : Type*} [Fintype ι]
    (atom : ι → ControlledDifference C R) (M : ℕ) :
    ∃ expressions : Finset (FiniteCombinationData C R),
      ∀ coeff : ι → ℤ,
        (∀ i, -(M : ℤ) ≤ coeff i ∧ coeff i ≤ M) →
        finiteCombinationOfFamily atom coeff ∈ expressions := by
  classical
  let Z := {z : ℤ // z ∈ Set.Icc (-(M : ℤ)) M}
  let : Fintype Z := (Set.finite_Icc (-(M : ℤ)) M).fintype
  let expression : (ι → Z) → FiniteCombinationData C R :=
    fun v => finiteCombinationOfFamily atom (fun i => (v i).1)
  refine ⟨Finset.univ.image expression, ?_⟩
  intro coeff hcoeff
  exact Finset.mem_image.mpr
    ⟨fun i => ⟨coeff i, hcoeff i⟩, Finset.mem_univ _, rfl⟩

private theorem endpoint_interval_fields
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (axis : Axis) (A : NormalizedGenericSection C axis) (S : Set ↥C.centres) :
    (∀ (i : Fin A.raw.presentation.n) (s : S),
      Set.Ioo
        ((IndexedSectionEndpoint.mk ⟨i, false⟩ s).sourceValue)
        ((IndexedSectionEndpoint.mk ⟨i, true⟩ s).sourceValue) =
      (-A.origin + axis.coord s.1.1) +ᵥ
        Set.Ioo (A.raw.presentation.left i) (A.raw.presentation.right i)) ∧
    (∀ (i : Fin A.raw.presentation.n) (s : S),
      Set.Ioo
        (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
        (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) =
      (axis.coord (Tphi s.1) - mapScalar phi A.originScalar) +ᵥ
        Set.Ioo
          (axis.coord (D.planarHomeomorph (A.raw.leftVertex i).1))
          (axis.coord (D.planarHomeomorph (A.raw.rightVertex i).1))) := by
  constructor
  · intro i s
    change Set.Ioo
        (A.raw.presentation.left i + axis.coord s.1.1 - A.origin)
        (A.raw.presentation.right i + axis.coord s.1.1 - A.origin) = _
    ext x
    simp only [Set.mem_Ioo, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    constructor <;> intro hx <;> constructor <;> linarith
  · intro i s
    have hl : IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, false⟩ s) =
        axis.coord (Tphi s.1) - mapScalar phi A.originScalar +
          axis.coord (D.planarHomeomorph (A.raw.leftVertex i).1) := by
      change axis.coord (D.planarHomeomorph (A.raw.leftVertex i).1 + Tphi s.1) -
        mapScalar phi A.originScalar = _
      cases axis <;> simp [Axis.coord, D.planarHomeomorph_apply] <;> ring
    have hr : IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, true⟩ s) =
        axis.coord (Tphi s.1) - mapScalar phi A.originScalar +
          axis.coord (D.planarHomeomorph (A.raw.rightVertex i).1) := by
      change axis.coord (D.planarHomeomorph (A.raw.rightVertex i).1 + Tphi s.1) -
        mapScalar phi A.originScalar = _
      cases axis <;> simp [Axis.coord, D.planarHomeomorph_apply] <;> ring
    rw [hl, hr]
    ext x
    simp only [Set.mem_Ioo, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    constructor <;> intro hx <;> constructor <;> linarith

private def endpointAxisHomeomorph
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (axis : Axis) : ℝ ≃ₜ ℝ :=
  match axis with
  | Axis.horizontal => D.firstHomeomorph
  | Axis.vertical => D.secondHomeomorph

private def endpointTransverseHomeomorph
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (axis : Axis) : ℝ ≃ₜ ℝ :=
  match axis with
  | Axis.horizontal => D.secondHomeomorph
  | Axis.vertical => D.firstHomeomorph

private theorem endpointAxisHomeomorph_strictMono
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (axis : Axis) :
    StrictMono (endpointAxisHomeomorph D axis) := by
  cases axis with
  | horizontal => exact D.firstHomeomorph_strictMono
  | vertical => exact D.secondHomeomorph_strictMono

private theorem endpoint_planar_coord
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (axis : Axis) (z : Tiling.Plane) :
    axis.coord (D.planarHomeomorph z) = endpointAxisHomeomorph D axis (axis.coord z) := by
  cases axis <;> simp [endpointAxisHomeomorph, Axis.coord, D.planarHomeomorph_apply]

private theorem endpoint_planar_transverse
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (axis : Axis) (z : Tiling.Plane) :
    axis.transverseCoord (D.planarHomeomorph z) =
      endpointTransverseHomeomorph D axis (axis.transverseCoord z) := by
  cases axis <;> simp [endpointTransverseHomeomorph, Axis.transverseCoord,
    D.planarHomeomorph_apply]

private theorem endpoint_planar_slicePoint
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (axis : Axis) (q x : ℝ) :
    D.planarHomeomorph (FilledSliceChains.slicePoint axis q x) =
      FilledSliceChains.slicePoint axis
        (axis.transverseCoord
          (D.planarHomeomorph (FilledSliceChains.slicePoint axis q 0)))
        (endpointAxisHomeomorph D axis x) := by
  cases axis <;> apply Complex.ext <;>
    simp [FilledSliceChains.slicePoint, endpointAxisHomeomorph,
      Axis.transverseCoord,
      D.planarHomeomorph_apply]

private theorem endpoint_deformedSection_eq
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (axis : Axis)
    (A : NormalizedGenericSection C axis) :
    {x : ℝ | FilledSliceChains.slicePoint axis
      (axis.transverseCoord (D.planarHomeomorph
        (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
        D.deformedRegion.openCarrier} =
      endpointAxisHomeomorph D axis '' A.raw.rawCarrier := by
  let q' := axis.transverseCoord (D.planarHomeomorph
    (FilledSliceChains.slicePoint axis A.raw.transverse 0))
  have hlineq (x : ℝ) :
      axis.transverseCoord (FilledSliceChains.slicePoint axis q' x) = q' := by
    cases axis <;> simp [FilledSliceChains.slicePoint, Axis.transverseCoord]
  have hq' : q' = endpointTransverseHomeomorph D axis
      (axis.transverseCoord (FilledSliceChains.slicePoint axis A.raw.transverse 0)) := by
    dsimp [q']
    exact endpoint_planar_transverse D axis _
  ext x
  constructor
  · intro hx
    rw [D.deformedRegion_openCarrier] at hx
    rcases hx with ⟨z, hz, hzEq⟩
    have hcoord : endpointAxisHomeomorph D axis (axis.coord z) = x := by
      calc
        endpointAxisHomeomorph D axis (axis.coord z) = axis.coord (D.planarHomeomorph z) :=
          (endpoint_planar_coord D axis z).symm
        _ = axis.coord (FilledSliceChains.slicePoint axis q' x) := congrArg axis.coord hzEq
        _ = x := by cases axis <;> simp [FilledSliceChains.slicePoint, Axis.coord]
    have htrans : axis.transverseCoord z =
        axis.transverseCoord (FilledSliceChains.slicePoint axis A.raw.transverse 0) := by
      apply (endpointTransverseHomeomorph D axis).injective
      calc
        endpointTransverseHomeomorph D axis (axis.transverseCoord z) =
            axis.transverseCoord (D.planarHomeomorph z) :=
          (endpoint_planar_transverse D axis z).symm
        _ = q' := by rw [hzEq]; exact hlineq x
        _ = endpointTransverseHomeomorph D axis
            (axis.transverseCoord (FilledSliceChains.slicePoint axis A.raw.transverse 0)) := hq'
    have hzLine : z = FilledSliceChains.slicePoint axis A.raw.transverse (axis.coord z) := by
      cases axis with
      | horizontal =>
          apply Complex.ext
          · simp [FilledSliceChains.slicePoint, Axis.coord]
          · simpa [FilledSliceChains.slicePoint, Axis.transverseCoord] using htrans
      | vertical =>
          apply Complex.ext
          · simpa [FilledSliceChains.slicePoint, Axis.transverseCoord] using htrans
          · simp [FilledSliceChains.slicePoint, Axis.coord]
    refine ⟨axis.coord z, ?_, hcoord⟩
    rw [A.raw.rawCarrier_eq]
    change FilledSliceChains.slicePoint axis A.raw.transverse (axis.coord z) ∈
      C.region.openCarrier
    rw [← hzLine]
    exact hz
  · rintro ⟨y, hy, rfl⟩
    rw [D.deformedRegion_openCarrier]
    refine ⟨FilledSliceChains.slicePoint axis A.raw.transverse y, ?_, ?_⟩
    · rw [A.raw.rawCarrier_eq] at hy
      exact hy
    · simpa [q'] using (endpoint_planar_slicePoint D axis A.raw.transverse y)

private theorem endpointAxisHomeomorph_image_Ioo
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (axis : Axis) (a b : ℝ) :
    endpointAxisHomeomorph D axis '' Set.Ioo a b =
      Set.Ioo (endpointAxisHomeomorph D axis a)
        (endpointAxisHomeomorph D axis b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hmono := endpointAxisHomeomorph_strictMono D axis
    exact ⟨hmono hx.1, hmono hx.2⟩
  · intro hy
    refine ⟨(endpointAxisHomeomorph D axis).symm y, ?_, ?_⟩
    · constructor
      · exact (endpointAxisHomeomorph_strictMono D axis).lt_iff_lt.mp
          (by simpa using hy.1)
      · exact (endpointAxisHomeomorph_strictMono D axis).lt_iff_lt.mp
          (by simpa using hy.2)
    · exact (endpointAxisHomeomorph D axis).apply_symm_apply y

private theorem endpoint_targetCenter_section_eq
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (axis : Axis) (A : NormalizedGenericSection C axis) (S : Set ↥C.centres)
    (s : S) :
    axis.coord (Tphi s.1) +ᵥ
        {x : ℝ | FilledSliceChains.slicePoint axis
          (axis.transverseCoord (D.planarHomeomorph
            (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
              D.deformedRegion.openCarrier} =
      mapScalar phi A.originScalar +ᵥ
        ⋃ i : Fin A.raw.presentation.n,
          Set.Ioo
            (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
              (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
            (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
              (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) := by
  have hleft (i : Fin A.raw.presentation.n) :
      axis.coord (D.planarHomeomorph (A.raw.leftVertex i).1) =
        endpointAxisHomeomorph D axis (A.raw.presentation.left i) := by
    rw [endpoint_planar_coord, A.raw.leftVertex_coord]
  have hright (i : Fin A.raw.presentation.n) :
      axis.coord (D.planarHomeomorph (A.raw.rightVertex i).1) =
        endpointAxisHomeomorph D axis (A.raw.presentation.right i) := by
    rw [endpoint_planar_coord, A.raw.rightVertex_coord]
  have hset (i : Fin A.raw.presentation.n) :
      axis.coord (Tphi s.1) +ᵥ
          Set.Ioo (endpointAxisHomeomorph D axis (A.raw.presentation.left i))
            (endpointAxisHomeomorph D axis (A.raw.presentation.right i)) =
        mapScalar phi A.originScalar +ᵥ
          Set.Ioo
            (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
              (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
            (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
              (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) := by
    have hi := (endpoint_interval_fields D Tphi axis A S).2 i s
    rw [hleft, hright] at hi
    rw [hi]
    ext x
    simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, Set.mem_Ioo]
    constructor <;> intro hx <;> constructor <;> linarith
  have himage : endpointAxisHomeomorph D axis '' A.raw.rawCarrier =
      endpointAxisHomeomorph D axis ''
        (⋃ i : Fin A.raw.presentation.n,
          Set.Ioo (A.raw.presentation.left i) (A.raw.presentation.right i)) :=
    congrArg (fun U : Set ℝ => endpointAxisHomeomorph D axis '' U)
      A.raw.presentation.union_eq
  calc
    axis.coord (Tphi s.1) +ᵥ
        {x : ℝ | FilledSliceChains.slicePoint axis
          (axis.transverseCoord (D.planarHomeomorph
            (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
              D.deformedRegion.openCarrier} =
        axis.coord (Tphi s.1) +ᵥ
          (endpointAxisHomeomorph D axis '' A.raw.rawCarrier) := by
            rw [endpoint_deformedSection_eq D axis A]
    _ = axis.coord (Tphi s.1) +ᵥ
          (endpointAxisHomeomorph D axis ''
            (⋃ i : Fin A.raw.presentation.n,
              Set.Ioo (A.raw.presentation.left i) (A.raw.presentation.right i))) :=
            congrArg (fun U : Set ℝ => axis.coord (Tphi s.1) +ᵥ U) himage
    _ = ⋃ i : Fin A.raw.presentation.n,
          axis.coord (Tphi s.1) +ᵥ
            Set.Ioo (endpointAxisHomeomorph D axis (A.raw.presentation.left i))
              (endpointAxisHomeomorph D axis (A.raw.presentation.right i)) := by
            rw [Set.image_iUnion]
            simp_rw [endpointAxisHomeomorph_image_Ioo]
            ext x
            simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, Set.mem_iUnion]
    _ = ⋃ i : Fin A.raw.presentation.n,
          mapScalar phi A.originScalar +ᵥ
            Set.Ioo
              (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
                (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
              (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
                (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) :=
            Set.iUnion_congr hset
    _ = mapScalar phi A.originScalar +ᵥ
          ⋃ i : Fin A.raw.presentation.n,
            Set.Ioo
              (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
                (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
              (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
                (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) := by
            ext x
            simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, Set.mem_iUnion]

private theorem endpoint_targetRawUnion_eq
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (axis : Axis) (A : NormalizedGenericSection C axis) (S : Set ↥C.centres) :
    (⋃ t : deformedCenterCarrierOn Tphi S,
      axis.coord t.1 +ᵥ
        {x : ℝ | FilledSliceChains.slicePoint axis
          (axis.transverseCoord (D.planarHomeomorph
            (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
              D.deformedRegion.openCarrier}) =
      mapScalar phi A.originScalar +ᵥ
        ⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
          Set.Ioo
            (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
              (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
            (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
              (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨t, hx⟩
    rcases t.2 with ⟨s, hs, hts⟩
    rw [← hts, endpoint_targetCenter_section_eq D Tphi axis A S ⟨s, hs⟩] at hx
    simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, Set.mem_iUnion] at hx ⊢
    rcases hx with ⟨i, hi⟩
    exact ⟨i, ⟨⟨s, hs⟩, hi⟩⟩
  · intro hx
    simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, Set.mem_iUnion] at hx
    rcases hx with ⟨i, s, hs⟩
    let t : deformedCenterCarrierOn Tphi S :=
      ⟨Tphi s.1, ⟨s.1, s.2, rfl⟩⟩
    refine ⟨t, ?_⟩
    rw [endpoint_targetCenter_section_eq D Tphi axis A S s]
    simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, Set.mem_iUnion]
    exact ⟨i, hs⟩

private theorem endpoint_target_union_eq
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (axis : Axis) (A : NormalizedGenericSection C axis) (S : Set ↥C.centres) :
    interior (closure (⋃ t : deformedCenterCarrierOn Tphi S,
      axis.coord t.1 +ᵥ
        {x : ℝ | FilledSliceChains.slicePoint axis
          (axis.transverseCoord (D.planarHomeomorph
            (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
              D.deformedRegion.openCarrier})) =
      mapScalar phi A.originScalar +ᵥ
        interior (closure (⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
          Set.Ioo
            (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
              (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
            (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
              (IndexedSectionEndpoint.mk ⟨i, true⟩ s)))) := by
  rw [endpoint_targetRawUnion_eq D Tphi axis A S, closure_vadd, interior_vadd]

private theorem endpoint_sourceRawUnion_eq
    {C : ApproximationContext.{0}} (axis : Axis)
    (A : NormalizedGenericSection C axis) (S : Set ↥C.centres) :
    A.carrier + axis.coord '' (Subtype.val '' S) =
      ⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
        Set.Ioo
          ((IndexedSectionEndpoint.mk ⟨i, false⟩ s).sourceValue)
          ((IndexedSectionEndpoint.mk ⟨i, true⟩ s).sourceValue) := by
  rw [A.carrier_eq]
  ext x
  constructor
  · intro hx
    rw [Set.mem_add] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg] at ha
    rw [A.raw.presentation.union_eq, Set.mem_iUnion] at ha
    rcases ha with ⟨i, hi⟩
    rcases hb with ⟨p, hp, rfl⟩
    rcases hp with ⟨s, hs, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_Ioo, IndexedSectionEndpoint.sourceValue,
      SectionEndpointLabel.rawValue]
    change ∃ j : Fin A.raw.presentation.n, ∃ t : S,
      A.raw.presentation.left j + axis.coord t.1.1 - A.origin < x ∧
        x < A.raw.presentation.right j + axis.coord t.1.1 - A.origin
    refine ⟨i, ⟨s, hs⟩, ?_⟩
    constructor <;> linarith [hi.1, hi.2, hab]
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_Ioo, IndexedSectionEndpoint.sourceValue,
      SectionEndpointLabel.rawValue] at hx
    change ∃ i : Fin A.raw.presentation.n, ∃ s : S,
      A.raw.presentation.left i + axis.coord s.1.1 - A.origin < x ∧
        x < A.raw.presentation.right i + axis.coord s.1.1 - A.origin at hx
    rcases hx with ⟨i, s, hx⟩
    let y : ℝ := x + A.origin - axis.coord s.1.1
    have hy : y ∈ A.raw.rawCarrier := by
      rw [A.raw.presentation.union_eq, Set.mem_iUnion]
      refine ⟨i, ?_⟩
      change A.raw.presentation.left i < y ∧ y < A.raw.presentation.right i
      dsimp [y]
      constructor <;> linarith
    let a : ℝ := -A.origin + y
    have ha : a ∈ -A.origin +ᵥ A.raw.rawCarrier := by
      change -A.origin +ᵥ y ∈ -A.origin +ᵥ A.raw.rawCarrier
      exact vadd_mem_vadd_set hy
    have hb : axis.coord s.1.1 ∈ axis.coord '' (Subtype.val '' S) := by
      exact ⟨s.1.1, ⟨s.1, s.2, rfl⟩, rfl⟩
    apply Set.mem_add.mpr
    refine ⟨a, ha, axis.coord s.1.1, hb, ?_⟩
    dsimp [a, y]
    linarith

private theorem endpoint_source_union_eq
    {C : ApproximationContext.{0}} (axis : Axis)
    (A : NormalizedGenericSection C axis) (S : Set ↥C.centres) :
    interior (closure (A.carrier + axis.coord '' (Subtype.val '' S))) =
      interior (closure (⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
        Set.Ioo
          ((IndexedSectionEndpoint.mk ⟨i, false⟩ s).sourceValue)
          ((IndexedSectionEndpoint.mk ⟨i, true⟩ s).sourceValue))) := by
  rw [endpoint_sourceRawUnion_eq axis A S]

private theorem normalizedSection_translates_pairwiseDisjoint
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements S))
    (hline : ∃ c, ∀ s ∈ S, axis.transverseCoord s = c) :
    S.Pairwise (fun s t => Disjoint ((axis.coord s) +ᵥ A.carrier)
      ((axis.coord t) +ᵥ A.carrier)) := by
  obtain ⟨c, hc⟩ := hline
  have hdisjoint := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
    C.region S).mp hpacking
  intro s hs t ht hst
  rw [Set.disjoint_left]
  intro x hxs hxt
  let z := FilledSliceChains.slicePoint axis (A.raw.transverse + c) (x + A.origin)
  have hplaced (u : Tiling.Plane) (hu : u ∈ S)
      (hxu : x ∈ (axis.coord u) +ᵥ A.carrier) : z ∈ u +ᵥ C.region.openCarrier := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxu ⊢
    rw [A.carrier_eq, Set.mem_vadd_set_iff_neg_vadd_mem, A.raw.rawCarrier_eq] at hxu
    have huc := hc u hu
    have heq : -u + z = FilledSliceChains.slicePoint axis A.raw.transverse
        (-(-A.origin) + (-axis.coord u + x)) := by
      cases axis <;> apply Complex.ext <;>
        simp [z, FilledSliceChains.slicePoint, Axis.coord, Axis.transverseCoord] at huc ⊢ <;>
        linarith
    change -u + z ∈ C.region.openCarrier
    rw [heq]
    simpa only [vadd_eq_add, Set.mem_ofPred_eq] using hxu
  exact Set.disjoint_left.mp (hdisjoint hs ht hst) (hplaced s hs hxs) (hplaced t ht hxt)

private theorem closure_interval_union_diff_subset_endpoints
    {ι : Type*} (l r : ι → ℝ)
    (hfinite : ∀ a b : ℝ,
      ({x : ℝ | ∃ i, x = l i ∨ x = r i} ∩ Set.Icc a b).Finite) :
    Set.diff (closure (⋃ i, Set.Ioo (l i) (r i))) (⋃ i, Set.Ioo (l i) (r i)) ⊆
      {x : ℝ | ∃ i, x = l i ∨ x = r i} := by
  intro x hx
  let E : Set ℝ := {x | ∃ i, x = l i ∨ x = r i}
  by_contra hxE
  let F : Set ℝ := E ∩ Set.Icc (x - 1) (x + 1)
  have hFfinite : F.Finite := by
    exact hfinite (x - 1) (x + 1)
  have hxF : x ∉ F := by
    intro hx
    exact hxE hx.1
  have hFclosed : IsClosed F := hFfinite.isClosed
  have hFcomplNhds : Fᶜ ∈ 𝓝 x := hFclosed.isOpen_compl.mem_nhds hxF
  obtain ⟨a, b, hxab, hab⟩ :=
    (mem_nhds_iff_exists_Ioo_subset (a := x) (s := Fᶜ)).mp hFcomplNhds
  let ε : ℝ := min 1 (min ((x - a) / 2) ((b - x) / 2))
  have hεpos : 0 < ε := by
    have hxa : 0 < x - a := by linarith [hxab.1]
    have hbx : 0 < b - x := by linarith [hxab.2]
    dsimp [ε]
    positivity
  have hεleft : ε ≤ (x - a) / 2 := by
    dsimp [ε]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεright : ε ≤ (b - x) / 2 := by
    dsimp [ε]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hεone : ε ≤ 1 := by
    dsimp [ε]
    exact min_le_left _ _
  have hleft : a < x - ε := by linarith
  have hright : x + ε < b := by linarith
  let V : Set ℝ := Set.Ioo (x - ε) (x + ε)
  have hVsubab : V ⊆ Set.Ioo a b := by
    intro z hz
    exact ⟨lt_trans hleft hz.1, lt_trans hz.2 hright⟩
  have hVsubIcc : V ⊆ Set.Icc (x - 1) (x + 1) := by
    intro z hz
    constructor <;> linarith [hz.1, hz.2, hεone]
  have hVavoid : ∀ z ∈ V, z ∉ E := by
    intro z hz hzE
    have hzF : z ∈ F := ⟨hzE, hVsubIcc hz⟩
    have hzcomp : z ∈ Fᶜ := hab (hVsubab hz)
    exact hzcomp hzF
  let U : Set ℝ := ⋃ i, Set.Ioo (l i) (r i)
  by_cases hmeet : ∃ i, ∃ y, y ∈ V ∧ y ∈ Set.Ioo (l i) (r i)
  · obtain ⟨i, y, hyV, hyI⟩ := hmeet
    have hliNotV : l i ∉ V := by
      intro hliV
      exact hVavoid (l i) hliV ⟨i, Or.inl rfl⟩
    have hriNotV : r i ∉ V := by
      intro hriV
      exact hVavoid (r i) hriV ⟨i, Or.inr rfl⟩
    have hli : l i ≤ x - ε := by
      have hbound : l i ≤ x - ε ∨ x + ε ≤ l i := by
        by_contra h
        push Not at h
        exact hliNotV ⟨h.1, h.2⟩
      rcases hbound with hli | hli
      · exact hli
      · linarith [hyV.2, hyI.1]
    have hri : x + ε ≤ r i := by
      have hbound : r i ≤ x - ε ∨ x + ε ≤ r i := by
        by_contra h
        push Not at h
        exact hriNotV ⟨h.1, h.2⟩
      rcases hbound with hri | hri
      · linarith [hyV.1, hyI.2]
      · exact hri
    have hVsubU : V ⊆ U := by
      intro z hz
      change z ∈ ⋃ j, Set.Ioo (l j) (r j)
      rw [Set.mem_iUnion]
      refine ⟨i, ?_⟩
      exact ⟨lt_of_le_of_lt hli hz.1, lt_of_lt_of_le hz.2 hri⟩
    have hxV : x ∈ V := ⟨by linarith, by linarith⟩
    have hxU : x ∈ U := hVsubU hxV
    exact hx.2 hxU
  · have hVdisjU : ∀ z ∈ V, z ∉ U := by
      intro z hz hzU
      apply hmeet
      have hzU' : ∃ i, z ∈ Set.Ioo (l i) (r i) := by simpa [U] using hzU
      rcases hzU' with ⟨i, hi⟩
      exact ⟨i, z, hz, hi⟩
    have hVdisjClosure : ∀ z ∈ V, z ∉ closure U := by
      intro z hz hzclosure
      have hzcl := (mem_closure_iff.mp hzclosure) V isOpen_Ioo hz
      rcases hzcl with ⟨w, hwV, hwU⟩
      exact hVdisjU w hwV hwU
    have hxV : x ∈ V := ⟨by linarith, by linarith⟩
    exact (hVdisjClosure x hxV) hx.1

private theorem frontier_regularized_interval_union_subset_endpoints
    {ι : Type*} (l r : ι → ℝ)
    (hfinite : ∀ a b : ℝ,
      ({x : ℝ | ∃ i, x = l i ∨ x = r i} ∩ Set.Icc a b).Finite) :
    frontier (interior (closure (⋃ i, Set.Ioo (l i) (r i)))) ⊆
      {x : ℝ | ∃ i, x = l i ∨ x = r i} := by
  intro x hxfront
  by_contra hxE
  let U : Set ℝ := ⋃ i, Set.Ioo (l i) (r i)
  have hxclosureU : x ∈ closure U := by
    have hxclosureT := frontier_subset_closure hxfront
    have hTsub : interior (closure U) ⊆ closure U := interior_subset
    simpa [U, closure_closure] using (closure_mono hTsub) hxclosureT
  have hxnotU : x ∉ U := by
    intro hxU
    have hUopen : IsOpen U := isOpen_iUnion fun i => isOpen_Ioo
    have hUsubT : U ⊆ interior (closure U) := by
      calc
        U = interior U := hUopen.interior_eq.symm
        _ ⊆ interior (closure U) := interior_mono subset_closure
    have hxT : x ∈ interior (closure U) := hUsubT hxU
    have hTopen : IsOpen (interior (closure U)) := isOpen_interior
    have hxInteriorT : x ∈ interior (interior (closure U)) := by
      rw [hTopen.interior_eq]
      exact hxT
    have hxnotInterior :=
      (mem_frontier_iff_notMem_interior hxT).mp (by simpa [U] using hxfront)
    exact hxnotInterior hxInteriorT
  exact hxE ((closure_interval_union_diff_subset_endpoints l r hfinite) ⟨hxclosureU, hxnotU⟩)

private theorem sourceTrace_endpointControl
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres)
    (axis : Axis) (A : NormalizedGenericSection C axis) (S : Set ↥C.centres)
    (hline : ∃ c, ∀ s : S, axis.transverseCoord s.1.1 = c) :
    (∀ a b : ℝ,
      ((closure (A.carrier + axis.coord '' (Subtype.val '' S)) \
        (A.carrier + axis.coord '' (Subtype.val '' S))) ∩ Set.Icc a b).Finite) ∧
    frontier (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S)))) ⊆
      {x | ∃ e : IndexedSectionEndpoint A S, e.sourceValue = x} := by
  let l (p : Fin A.raw.presentation.n × S) :=
    (IndexedSectionEndpoint.mk ⟨p.1, false⟩ p.2).sourceValue
  let r (p : Fin A.raw.presentation.n × S) :=
    (IndexedSectionEndpoint.mk ⟨p.1, true⟩ p.2).sourceValue
  let E : Set ℝ := {x | ∃ p, x = l p ∨ x = r p}
  have hE : E = {x | ∃ e : IndexedSectionEndpoint A S, e.sourceValue = x} := by
    ext x
    constructor
    · rintro ⟨⟨i, s⟩, hx | hx⟩
      · exact ⟨⟨⟨i, false⟩, s⟩, hx.symm⟩
      · exact ⟨⟨⟨i, true⟩, s⟩, hx.symm⟩
    · rintro ⟨⟨⟨i, side⟩, s⟩, hx⟩
      cases side
      · exact ⟨(i, s), Or.inl hx.symm⟩
      · exact ⟨(i, s), Or.inr hx.symm⟩
  have hfinite : ∀ a b : ℝ, (E ∩ Set.Icc a b).Finite := by
    rw [hE]
    exact sourceEndpointValues_locallyFinite hT axis A S hline
  have hU : A.carrier + axis.coord '' (Subtype.val '' S) =
      ⋃ p, Set.Ioo (l p) (r p) := by
    rw [endpoint_sourceRawUnion_eq axis A S, Set.iUnion_prod']
  constructor
  · intro a b
    have hsubset := closure_interval_union_diff_subset_endpoints l r hfinite
    rw [hU]
    exact (hfinite a b).subset (Set.inter_subset_inter_left _ hsubset)
  · rw [hU]
    exact (frontier_regularized_interval_union_subset_endpoints l r hfinite).trans
      hE.subset

private theorem boundedOccupiedTraceComponent_raw_mass
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres)
    (axis : Axis) (A : NormalizedGenericSection C axis) (S : Set ↥C.centres)
    (hline : ∃ c, ∀ s : S, axis.transverseCoord s.1.1 = c)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S)) :
    volume.real ((A.carrier + axis.coord '' (Subtype.val '' S)) ∩
      Set.Ioo J.left J.right) = J.right - J.left := by
  let U := A.carrier + axis.coord '' (Subtype.val '' S)
  have hJsubset : Set.Ioo J.left J.right ⊆ closure U := by
    rw [← J.component_eq]
    exact (connectedComponentIn_subset _ _).trans interior_subset
  have hfinite := (sourceTrace_endpointControl hT axis A S hline).1 J.left J.right
  have hmissing : (Set.Ioo J.left J.right \ (U ∩ Set.Ioo J.left J.right)).Finite := by
    apply hfinite.subset
    rintro x ⟨hxJ, hxraw⟩
    refine ⟨⟨hJsubset hxJ, ?_⟩, hxJ.1.le, hxJ.2.le⟩
    intro hxU
    exact hxraw ⟨hxU, hxJ⟩
  have hmeasure := MeasureTheory.measure_eq_measure_of_null_sdiff
    (μ := volume) (Set.inter_subset_right (s := U) (t := Set.Ioo J.left J.right))
    (hmissing.measure_zero volume)
  rw [MeasureTheory.measureReal_def, hmeasure, ← MeasureTheory.measureReal_def,
    Real.volume_real_Ioo, max_eq_left (sub_nonneg.mpr J.ordered.le)]

private theorem finiteCombinationOfFamily_value_sum
    {C : ApproximationContext.{0}} {R : ℝ} {ι κ : Type*} [Fintype ι]
    (atom : ι → ControlledDifference C R) (Q : Finset κ) (coeff : κ → ι → ℤ) :
    (finiteCombinationOfFamily atom (fun i => ∑ s ∈ Q, coeff s i)).value =
      ∑ s ∈ Q, (finiteCombinationOfFamily atom (coeff s)).value := by
  classical
  change (∑ i : ι, ((∑ s ∈ Q, coeff s i : ℤ) : ℚ) • (atom i).scalar) =
    ∑ s ∈ Q, ∑ i : ι, (coeff s i : ℚ) • (atom i).scalar
  push_cast
  simp_rw [Finset.sum_smul]
  exact Finset.sum_comm

private theorem finiteCombinationOfFamily_sum_coeff_bound
    {ι κ : Type*} (Q : Finset κ) (coeff : κ → ι → ℤ) (M : ℕ)
    (hcard : Q.card ≤ M)
    (hcoeff : ∀ s ∈ Q, ∀ i, -1 ≤ coeff s i ∧ coeff s i ≤ 1) :
    ∀ i, -(M : ℤ) ≤ ∑ s ∈ Q, coeff s i ∧ ∑ s ∈ Q, coeff s i ≤ M := by
  intro i
  have hl := Finset.sum_le_sum (fun s hs => (hcoeff s hs i).1)
  have hr := Finset.sum_le_sum (fun s hs => (hcoeff s hs i).2)
  have hc : (Q.card : ℤ) ≤ M := by exact_mod_cast hcard
  simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one] at hl hr
  constructor <;> linarith

private theorem targetTrace_frontier_subset_endpoints
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (axis : Axis) (A : NormalizedGenericSection C axis) (S : Set ↥C.centres)
    (hpacking : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (deformedCenterCarrierOn Tphi S)))
    (hline : ∃ c, ∀ s : S, axis.transverseCoord (Tphi s.1) = c) :
    frontier ((-mapScalar phi A.originScalar) +ᵥ
      interior (closure (⋃ s : deformedCenterCarrierOn Tphi S,
        axis.coord s +ᵥ {x : ℝ | FilledSliceChains.slicePoint axis
          (axis.transverseCoord (D.planarHomeomorph
            (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
              D.deformedRegion.openCarrier}))) ⊆
      {x | ∃ e : IndexedSectionEndpoint A S,
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e = x} := by
  let l (p : Fin A.raw.presentation.n × S) :=
    IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
      (IndexedSectionEndpoint.mk ⟨p.1, false⟩ p.2)
  let r (p : Fin A.raw.presentation.n × S) :=
    IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
      (IndexedSectionEndpoint.mk ⟨p.1, true⟩ p.2)
  let E : Set ℝ := {x | ∃ p, x = l p ∨ x = r p}
  have hE : E = {x | ∃ e : IndexedSectionEndpoint A S,
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e = x} := by
    ext x
    constructor
    · rintro ⟨⟨i, s⟩, hx | hx⟩
      · exact ⟨⟨⟨i, false⟩, s⟩, hx.symm⟩
      · exact ⟨⟨⟨i, true⟩, s⟩, hx.symm⟩
    · rintro ⟨⟨⟨i, side⟩, s⟩, hx⟩
      cases side
      · exact ⟨(i, s), Or.inl hx.symm⟩
      · exact ⟨(i, s), Or.inr hx.symm⟩
  have hfinite : ∀ a b : ℝ, (E ∩ Set.Icc a b).Finite := by
    rw [hE]
    exact targetEndpointValues_locallyFinite D Tphi axis A S hpacking hline
  have hU : (⋃ p, Set.Ioo (l p) (r p)) =
      ⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
        Set.Ioo
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) :=
    Set.iUnion_prod' (fun p => Set.Ioo (l p) (r p))
  rw [endpoint_target_union_eq D Tphi axis A S, neg_vadd_vadd, ← hU]
  exact (frontier_regularized_interval_union_subset_endpoints l r hfinite).trans hE.subset

private theorem bulkCentres_finite
    {C : ApproximationContext.{0}} {axis : Axis}
    (hT : HasFLC C.centres) {S : Set Tiling.Plane}
    (hS : S ⊆ C.centres) (hline : ∃ c, ∀ s ∈ S, axis.transverseCoord s = c)
    (A : NormalizedGenericSection C axis) (J : BoundedOccupiedTraceComponent A S) :
    (bulkCentres A S J).Finite := by
  classical
  have hleftMem : A.raw.presentation.left A.originInterval ∈
      A.raw.presentation.endpoints := by
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨A.originInterval, Finset.mem_univ _, rfl⟩)
  have hleftClosure :=
    A.raw.presentation.endpoint_subset_closure hleftMem
  have horigin : A.origin = A.raw.presentation.left A.originInterval := by
    rw [A.origin_eq, A.originVertex_eq]
    exact A.raw.leftVertex_coord A.originInterval
  have hzero : (0 : ℝ) ∈ closure A.carrier := by
    rw [A.carrier_eq, closure_vadd]
    exact ⟨A.raw.presentation.left A.originInterval, hleftClosure, by simp [horigin]⟩
  have hcoordFinite :
      ((axis.coord '' S) ∩ Set.Ioo J.left J.right).Finite :=
    aligned_coordinate_boundedWindowFinite hT axis hS hline
      (Set.Ioo J.left J.right) (Metric.isBounded_Ioo J.left J.right)
  have himage : (axis.coord '' bulkCentres A S J).Finite := by
    apply hcoordFinite.subset
    rintro x ⟨s, hs, rfl⟩
    have hs' := hs
    simp only [bulkCentres, Set.mem_ofPred_eq] at hs'
    refine ⟨⟨s, hs'.1, rfl⟩, ?_⟩
    have hcenter : axis.coord s ∈
        convexHull ℝ ((axis.coord s) +ᵥ closure A.carrier) := by
      apply subset_convexHull ℝ _
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa only [vadd_eq_add, neg_add_cancel] using hzero
    exact hs'.2 hcenter
  apply himage.of_finite_image
  intro s hs t ht hst
  have hsS : s ∈ S := by
    have := hs
    simp only [bulkCentres, Set.mem_ofPred_eq] at this
    exact this.1
  have htS : t ∈ S := by
    have := ht
    simp only [bulkCentres, Set.mem_ofPred_eq] at this
    exact this.1
  obtain ⟨c, hc⟩ := hline
  cases axis with
  | horizontal =>
      apply Complex.ext
      · simpa only [Axis.coord] using hst
      · have hcs : s.im = c := by simpa only [Axis.transverseCoord] using hc s hsS
        have hct : t.im = c := by simpa only [Axis.transverseCoord] using hc t htS
        rw [hcs, hct]
  | vertical =>
      apply Complex.ext
      · have hcs : s.re = c := by simpa only [Axis.transverseCoord] using hc s hsS
        have hct : t.re = c := by simpa only [Axis.transverseCoord] using hc t htS
        rw [hcs, hct]
      · simpa only [Axis.coord] using hst

private theorem boundedCenterWindow_offsets_finite
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres)
    {S : Set Tiling.Plane} (hS : S ⊆ C.centres)
    (anchor : Tiling.Plane) (hanchor : anchor ∈ C.centres)
    (r : ℝ) (hr : 0 < r) :
    ∃ offsets : Finset Tiling.Plane,
      ∀ s ∈ S, dist s anchor ≤ r → s - anchor ∈ offsets := by
  let D : Set Tiling.Plane :=
    (C.centres - C.centres) ∩ Metric.closedBall 0 r
  have hD : D.Finite := by
    exact hT.2 r hr
  refine ⟨hD.toFinset, ?_⟩
  intro s hs hdist
  have hdiff : s - anchor ∈ C.centres - C.centres := by
    rw [Set.mem_sub]
    exact ⟨s, hS hs, anchor, hanchor, rfl⟩
  have hball : s - anchor ∈ Metric.closedBall 0 r := by
    change dist (s - anchor) 0 ≤ r
    simpa only [dist_eq_norm, sub_zero] using hdist
  exact hD.mem_toFinset.mpr ⟨hdiff, hball⟩

private theorem boundedCenterWindow_ncard_le_differenceAlphabet
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres)
    (anchor : Tiling.Plane) (hanchor : anchor ∈ C.centres)
    (r : ℝ) (hr : 0 < r) :
    (C.centres ∩ Metric.closedBall anchor r).ncard ≤
      ((C.centres - C.centres) ∩ Metric.closedBall 0 r).ncard := by
  let D : Set Tiling.Plane :=
    (C.centres - C.centres) ∩ Metric.closedBall 0 r
  have hD : D.Finite := hT.2 r hr
  change (C.centres ∩ Metric.closedBall anchor r).ncard ≤ D.ncard
  apply Set.ncard_le_ncard_of_injOn (s := C.centres ∩ Metric.closedBall anchor r)
    (t := D) (fun s : Tiling.Plane => s - anchor) (ht := hD)
  · intro s hs
    have hdiff : s - anchor ∈ C.centres - C.centres := by
      rw [Set.mem_sub]
      exact ⟨s, hs.1, anchor, hanchor, rfl⟩
    have hdist : dist s anchor ≤ r := Metric.mem_closedBall.mp hs.2
    have hball : s - anchor ∈ Metric.closedBall 0 r := by
      change dist (s - anchor) 0 ≤ r
      simpa only [dist_eq_norm, sub_zero] using hdist
    exact ⟨hdiff, hball⟩
  · intro s hs t ht hst
    have heq := congrArg (fun z : Tiling.Plane => z + anchor) hst
    simpa using heq

private theorem boundedOccupiedTraceComponent_endpoints_mem_traceEndpoints
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) {S : Set Tiling.Plane}
    (J : BoundedOccupiedTraceComponent A S) :
    J.left ∈ traceEndpoints A.carrier (axis.coord '' S) ∧
      J.right ∈ traceEndpoints A.carrier (axis.coord '' S) := by
  let U := interior (closure (A.carrier + axis.coord '' S))
  have hcomponentSubset : connectedComponentIn U ((J.left + J.right) / 2) ⊆ U :=
    connectedComponentIn_subset U ((J.left + J.right) / 2)
  have hIoo : Set.Ioo J.left J.right ⊆ U := by
    rw [← J.component_eq]
    exact hcomponentSubset
  have hleftIcc : J.left ∈ Set.Icc J.left J.right :=
    ⟨le_rfl, J.ordered.le⟩
  have hrightIcc : J.right ∈ Set.Icc J.left J.right :=
    ⟨J.ordered.le, le_rfl⟩
  have hleftClosure : J.left ∈ closure U := by
    apply closure_mono hIoo
    rw [closure_Ioo (ne_of_lt J.ordered)]
    exact hleftIcc
  have hrightClosure : J.right ∈ closure U := by
    apply closure_mono hIoo
    rw [closure_Ioo (ne_of_lt J.ordered)]
    exact hrightIcc
  have hleftNotU : J.left ∉ U := by
    intro hleft
    have hbridge : Set.Icc J.left ((J.left + J.right) / 2) ⊆ U := by
      intro x hx
      by_cases hxeq : x = J.left
      · simpa [hxeq] using hleft
      · apply hIoo
        constructor
        · exact lt_of_le_of_ne hx.1 (Ne.symm hxeq)
        · have hmidRight : (J.left + J.right) / 2 < J.right := by
            linarith [J.ordered]
          exact lt_of_le_of_lt hx.2 hmidRight
    have hleftComponent :
        J.left ∈ connectedComponentIn U ((J.left + J.right) / 2) := by
      have hlm : J.left ≤ (J.left + J.right) / 2 := by linarith [J.ordered]
      have hmid : (J.left + J.right) / 2 ∈
          Set.Icc J.left ((J.left + J.right) / 2) := ⟨hlm, le_rfl⟩
      have hbridgeComponent :=
        isPreconnected_Icc.subset_connectedComponentIn hmid hbridge
      exact hbridgeComponent (left_mem_Icc.mpr (by linarith [J.ordered]))
    have hleftIoo : J.left ∈ Set.Ioo J.left J.right := by
      rwa [J.component_eq] at hleftComponent
    exact (lt_irrefl J.left) hleftIoo.1
  have hrightNotU : J.right ∉ U := by
    intro hright
    have hbridge : Set.Icc ((J.left + J.right) / 2) J.right ⊆ U := by
      intro x hx
      by_cases hxeq : x = J.right
      · simpa [hxeq] using hright
      · apply hIoo
        constructor
        · have hleftMid : J.left < (J.left + J.right) / 2 := by
            linarith [J.ordered]
          exact lt_of_lt_of_le hleftMid hx.1
        · exact lt_of_le_of_ne hx.2 hxeq
    have hrightComponent :
        J.right ∈ connectedComponentIn U ((J.left + J.right) / 2) := by
      have hmr : (J.left + J.right) / 2 ≤ J.right := by linarith [J.ordered]
      have hmid : (J.left + J.right) / 2 ∈
          Set.Icc ((J.left + J.right) / 2) J.right := ⟨le_rfl, hmr⟩
      have hbridgeComponent :=
        isPreconnected_Icc.subset_connectedComponentIn hmid hbridge
      exact hbridgeComponent (right_mem_Icc.mpr hmr)
    have hrightIoo : J.right ∈ Set.Ioo J.left J.right := by
      rwa [J.component_eq] at hrightComponent
    exact (lt_irrefl J.right) hrightIoo.2
  constructor
  · change J.left ∈ frontier U
    rw [frontier, interior_interior]
    exact ⟨hleftClosure, hleftNotU⟩
  · change J.right ∈ frontier U
    rw [frontier, interior_interior]
    exact ⟨hrightClosure, hrightNotU⟩

private theorem boundedOccupiedTraceComponent_endpointAnchors
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres)
    {axis : Axis} (A : NormalizedGenericSection C axis) {S : Set Tiling.Plane}
    (hS : S ⊆ C.centres)
    (hline : ∃ c, ∀ s ∈ S, axis.transverseCoord s = c)
    (J : BoundedOccupiedTraceComponent A S) :
    (∃ tL ∈ S, ∃ vL ∈ C.region.vertices,
      axis.coord (vL + tL) - A.origin = J.left) ∧
      ∃ tR ∈ S, ∃ vR ∈ C.region.vertices,
        axis.coord (vR + tR) - A.origin = J.right := by
  have hA : GenericAxisSection C.region axis A.raw.rawCarrier := {
    transverse := A.raw.transverse
    generic := A.raw.generic
    carrier_eq := by simpa only [axisSection] using A.raw.rawCarrier_eq
    finiteIntervals := ⟨A.raw.presentation.n, A.raw.presentation.left,
      A.raw.presentation.right, A.raw.presentation.lt, A.raw.presentation.union_eq⟩
    isOpen := A.raw.presentation.isOpen
    nonempty := A.raw.nonempty }
  obtain ⟨hleft, hright⟩ :=
    boundedOccupiedTraceComponent_endpoints_mem_traceEndpoints A J
  have hnormalizedUnion : A.carrier + axis.coord '' S =
      (-A.origin) +ᵥ (A.raw.rawCarrier + axis.coord '' S) := by
    rw [A.carrier_eq]
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      have haRaw : A.origin + a ∈ A.raw.rawCarrier := by
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add] using ha
      apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
      refine ⟨A.origin +ᵥ a, haRaw, b, hb, ?_⟩
      calc
        (A.origin +ᵥ a) + b = A.origin + (a + b) := by simp [vadd_eq_add, add_assoc]
        _ = A.origin + x := congrArg (fun z : ℝ => A.origin + z) hab
        _ = - -A.origin +ᵥ x := by simp [vadd_eq_add]
    · intro hx
      have hx' : A.origin + x ∈ A.raw.rawCarrier + axis.coord '' S :=
        by simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add] using hx
      rcases hx' with ⟨a, ha, b, hb, hab⟩
      refine ⟨-A.origin + a, ?_, b, hb, ?_⟩
      · apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
        simpa [vadd_eq_add] using ha
      · linarith
  have hnormalizedOpenTrace :
      interior (closure (A.carrier + axis.coord '' S)) =
        (-A.origin) +ᵥ interior (closure (A.raw.rawCarrier + axis.coord '' S)) := by
    rw [hnormalizedUnion, closure_vadd, interior_vadd]
  have hleftRaw :
      J.left + A.origin ∈ traceEndpoints A.raw.rawCarrier (axis.coord '' S) := by
    change J.left ∈ frontier
      (interior (closure (A.carrier + axis.coord '' S))) at hleft
    rw [hnormalizedOpenTrace, frontier, closure_vadd, interior_vadd] at hleft
    change J.left + A.origin ∈ frontier
      (interior (closure (A.raw.rawCarrier + axis.coord '' S)))
    rw [frontier]
    constructor
    · have hmem := Set.mem_vadd_set_iff_neg_vadd_mem.mp hleft.1
      simpa [vadd_eq_add, add_comm] using hmem
    · intro hmem
      apply hleft.2
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [vadd_eq_add, add_comm] using hmem
  have hrightRaw :
      J.right + A.origin ∈ traceEndpoints A.raw.rawCarrier (axis.coord '' S) := by
    change J.right ∈ frontier
      (interior (closure (A.carrier + axis.coord '' S))) at hright
    rw [hnormalizedOpenTrace, frontier, closure_vadd, interior_vadd] at hright
    change J.right + A.origin ∈ frontier
      (interior (closure (A.raw.rawCarrier + axis.coord '' S)))
    rw [frontier]
    constructor
    · have hmem := Set.mem_vadd_set_iff_neg_vadd_mem.mp hright.1
      simpa [vadd_eq_add, add_comm] using hmem
    · intro hmem
      apply hright.2
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [vadd_eq_add, add_comm] using hmem
  obtain ⟨tL, htL, vL, hvL, hcoordL⟩ :=
    genuineTraceEndpoint_intrinsicLabel hT axis hS hline hA hleftRaw
  obtain ⟨tR, htR, vR, hvR, hcoordR⟩ :=
    genuineTraceEndpoint_intrinsicLabel hT axis hS hline hA hrightRaw
  refine ⟨⟨tL, htL, vL, hvL, ?_⟩, tR, htR, vR, hvR, ?_⟩ <;> linarith

private theorem normalizedSection_closure_subset_diameter
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) :
    closure A.carrier ⊆ Set.Icc (-Metric.diam C.region.support)
      (Metric.diam C.region.support) := by
  let d := Metric.diam C.region.support
  have horiginVertex : A.originVertex = A.raw.leftVertex A.originInterval :=
    A.originVertex_eq
  have horigin : A.origin = axis.coord (A.raw.leftVertex A.originInterval).1 := by
    rw [A.origin_eq, horiginVertex]
  have hvertexSupport : ∀ v : ↥C.region.vertices,
      (v : Tiling.Plane) ∈ C.region.support := by
    intro v
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier C.region v.2)
  have hdiam : ∀ v : ↥C.region.vertices,
      dist (v : Tiling.Plane) (A.raw.leftVertex A.originInterval).1 ≤ d := by
    intro v
    exact Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded
      (hvertexSupport v) (hvertexSupport (A.raw.leftVertex A.originInterval))
  have hleftAbs (i : Fin A.raw.presentation.n) :
      |A.raw.presentation.left i - A.origin| ≤ d := by
    calc
      |A.raw.presentation.left i - A.origin| =
          |axis.coord (A.raw.leftVertex i).1 -
            axis.coord (A.raw.leftVertex A.originInterval).1| := by
              rw [A.raw.leftVertex_coord, horigin]
      _ ≤ dist (A.raw.leftVertex i).1 (A.raw.leftVertex A.originInterval).1 :=
        sourceGeometry_coord_abs_le axis _ _
      _ ≤ d := hdiam (A.raw.leftVertex i)
  have hrightAbs (i : Fin A.raw.presentation.n) :
      |A.raw.presentation.right i - A.origin| ≤ d := by
    calc
      |A.raw.presentation.right i - A.origin| =
          |axis.coord (A.raw.rightVertex i).1 -
            axis.coord (A.raw.leftVertex A.originInterval).1| := by
              rw [A.raw.rightVertex_coord, horigin]
      _ ≤ dist (A.raw.rightVertex i).1 (A.raw.leftVertex A.originInterval).1 :=
        sourceGeometry_coord_abs_le axis _ _
      _ ≤ d := hdiam (A.raw.rightVertex i)
  have hrawBound : ∀ y ∈ A.raw.rawCarrier, |y - A.origin| ≤ d := by
    intro y hy
    rw [A.raw.presentation.union_eq] at hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    have hlower := (abs_le.mp (hleftAbs i)).1
    have hupper := (abs_le.mp (hrightAbs i)).2
    apply abs_le.mpr
    constructor <;> linarith [hi.1, hi.2]
  have hcarrierBound : A.carrier ⊆ Set.Icc (-d) d := by
    intro x hx
    rw [A.carrier_eq] at hx
    have hxraw : A.origin + x ∈ A.raw.rawCarrier := by
      have hmem := Set.mem_vadd_set_iff_neg_vadd_mem.mp hx
      simpa [vadd_eq_add, add_comm] using hmem
    have hxbound := hrawBound (A.origin + x) hxraw
    have hxabs : |x| ≤ d := by simpa using hxbound
    exact abs_le.mp hxabs
  calc
    closure A.carrier ⊆ closure (Set.Icc (-d) d) := closure_mono hcarrierBound
    _ = Set.Icc (-d) d := isClosed_Icc.closure_eq

private theorem aligned_centers_dist_eq_abs_axisCoord
    (axis : Axis) {s t : Tiling.Plane}
    (htrans : axis.transverseCoord s = axis.transverseCoord t) :
    dist s t = |axis.coord s - axis.coord t| := by
  cases axis with
  | horizontal =>
      rw [Complex.dist_eq]
      have htrans' : s.im = t.im := by
        simpa only [Axis.transverseCoord] using htrans
      have hdiff : s - t = ((s.re - t.re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [htrans']
      rw [hdiff]
      rw [Complex.norm_real]
      simp [Axis.coord, Real.norm_eq_abs]
  | vertical =>
      rw [Complex.dist_eq]
      have htrans' : s.re = t.re := by
        simpa only [Axis.transverseCoord] using htrans
      have hdiff : s - t = ((s.im - t.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [htrans']
        · simp
      rw [hdiff, norm_mul]
      rw [Complex.norm_real]
      simp [Axis.coord, Real.norm_eq_abs]

private theorem normalizedSection_translatedHull_subset
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) (s : Tiling.Plane) :
    convexHull ℝ ((axis.coord s) +ᵥ closure A.carrier) ⊆
      Set.Icc (axis.coord s - Metric.diam C.region.support)
        (axis.coord s + Metric.diam C.region.support) := by
  let d := Metric.diam C.region.support
  have htranslate : (axis.coord s) +ᵥ closure A.carrier ⊆
      Set.Icc (axis.coord s - d) (axis.coord s + d) := by
    intro x hx
    have hx' : x - axis.coord s ∈ closure A.carrier := by
      have hmem := Set.mem_vadd_set_iff_neg_vadd_mem.mp hx
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hmem
    have hb := normalizedSection_closure_subset_diameter A hx'
    rcases hb with ⟨hlo, hhi⟩
    constructor <;> linarith
  exact convexHull_min htranslate (convex_Icc _ _)

private theorem nonbulkContributingCenter_nearComponentEndpoint
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) {S : Set Tiling.Plane}
    (J : BoundedOccupiedTraceComponent A S) {s : Tiling.Plane}
    (hsS : s ∈ S) (hsNotBulk : s ∉ bulkCentres A S J)
    (hcontrib : ∃ i : Fin A.raw.presentation.n, ∃ x : ℝ,
      x ∈ Set.Ioo
        (A.raw.presentation.left i + axis.coord s - A.origin)
        (A.raw.presentation.right i + axis.coord s - A.origin) ∧
      x ∈ Set.Ioo J.left J.right) :
    |axis.coord s - J.left| ≤ 3 * Metric.diam C.region.support ∨
      |axis.coord s - J.right| ≤ 3 * Metric.diam C.region.support := by
  let c := axis.coord s
  let d := Metric.diam C.region.support
  have hd_nonneg : 0 ≤ d := by dsimp [d]; exact Metric.diam_nonneg
  let H := convexHull ℝ (c +ᵥ closure A.carrier)
  have hHbound : H ⊆ Set.Icc (c - d) (c + d) := by
    simpa only [H, c, d] using normalizedSection_translatedHull_subset A s
  have hsNotBulk' : ¬ (s ∈ S ∧ H ⊆ Set.Ioo J.left J.right) := by
    simpa only [bulkCentres, Set.mem_ofPred_eq, H, c, d] using hsNotBulk
  have hHnotSubset : ¬ H ⊆ Set.Ioo J.left J.right := by
    intro hsub
    exact hsNotBulk' ⟨hsS, hsub⟩
  obtain ⟨y, hyH, hyOutside⟩ := Set.not_subset.mp hHnotSubset
  obtain ⟨i, x, hxInterval, hxJ⟩ := hcontrib
  have hxRaw : x - axis.coord s + A.origin ∈ A.raw.rawCarrier := by
    rw [A.raw.presentation.union_eq]
    simp only [Set.mem_iUnion]
    refine ⟨i, ?_⟩
    constructor <;> linarith [hxInterval.1, hxInterval.2]
  have hxCarrier : x - axis.coord s ∈ A.carrier := by
    rw [A.carrier_eq, Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hxRaw
  have hxTranslate : x ∈ c +ᵥ closure A.carrier := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have hcl : x - c ∈ closure A.carrier := subset_closure hxCarrier
    simpa [c, vadd_eq_add, sub_eq_add_neg, add_comm] using hcl
  have hxH : x ∈ H := subset_convexHull ℝ _ hxTranslate
  have hxBounds := hHbound hxH
  have hyBounds := hHbound hyH
  have hxdist : |x - c| ≤ d := by
    rcases hxBounds with ⟨hlo, hhi⟩
    apply abs_le.mpr
    constructor <;> linarith
  have hydist : |y - c| ≤ d := by
    rcases hyBounds with ⟨hlo, hhi⟩
    apply abs_le.mpr
    constructor <;> linarith
  have hxyDist : |x - y| ≤ 2 * d := by
    apply abs_le.mpr
    constructor <;> linarith [abs_le.mp hxdist, abs_le.mp hydist]
  have hySide : y ≤ J.left ∨ J.right ≤ y := by
    by_contra h
    push Not at h
    exact hyOutside h
  rcases hySide with hyleft | hyright
  · have hxleftDist : |x - J.left| ≤ 2 * d := by
      apply abs_le.mpr
      constructor
      · have hnonneg : 0 ≤ x - J.left := by linarith [hxJ.1]
        linarith [hnonneg, hd_nonneg]
      · have hxyUpper := (abs_le.mp hxyDist).2
        linarith [hyleft, hxyUpper]
    apply Or.inl
    apply abs_le.mpr
    constructor <;> linarith [abs_le.mp hxdist, abs_le.mp hxleftDist]
  · have hxrightDist : |x - J.right| ≤ 2 * d := by
      apply abs_le.mpr
      constructor
      · have hxyLower := (abs_le.mp hxyDist).1
        linarith [hyright, hxyLower]
      · have hnonpos : x - J.right ≤ 0 := by linarith [hxJ.2]
        linarith [hnonpos, hd_nonneg]
    apply Or.inr
    apply abs_le.mpr
    constructor <;> linarith [abs_le.mp hxdist, abs_le.mp hxrightDist]

private theorem nonbulkContributingCenter_in_endpointWindows
    {C : ApproximationContext.{0}} (_hT : HasFLC C.centres)
    {axis : Axis} (A : NormalizedGenericSection C axis) {S : Set Tiling.Plane}
    (_hS : S ⊆ C.centres)
    (hline : ∃ c, ∀ s ∈ S, axis.transverseCoord s = c)
    (J : BoundedOccupiedTraceComponent A S)
    (tL tR : Tiling.Plane) (htL : tL ∈ S) (htR : tR ∈ S)
    (vL vR : Tiling.Plane) (hvL : vL ∈ C.region.vertices)
    (hvR : vR ∈ C.region.vertices)
    (hleftValue : axis.coord (vL + tL) - A.origin = J.left)
    (hrightValue : axis.coord (vR + tR) - A.origin = J.right)
    {s : Tiling.Plane}
    (hsS : s ∈ S) (hsNotBulk : s ∉ bulkCentres A S J)
    (hcontrib : ∃ i : Fin A.raw.presentation.n, ∃ x : ℝ,
      x ∈ Set.Ioo
        (A.raw.presentation.left i + axis.coord s - A.origin)
        (A.raw.presentation.right i + axis.coord s - A.origin) ∧
      x ∈ Set.Ioo J.left J.right) :
    dist s tL ≤ 4 * Metric.diam C.region.support + 1 ∨
      dist s tR ≤ 4 * Metric.diam C.region.support + 1 := by
  have hnear := nonbulkContributingCenter_nearComponentEndpoint A J hsS hsNotBulk hcontrib
  rcases hnear with hleft | hright
  · let t := tL
    let v := vL
    have htS := htL
    have hv := hvL
    have hvalue := hleftValue
    have hvertexSupport (w : ↥C.region.vertices) :
        (w : Tiling.Plane) ∈ C.region.support := by
      rw [← C.region.isPolygonal.closure_interior]
      exact frontier_subset_closure
        (IntrinsicVertices.region_vertices_subset_frontier C.region w.2)
    have hdistVertex : dist (v : Tiling.Plane) A.originVertex ≤
        Metric.diam C.region.support :=
      Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded
        (hvertexSupport ⟨v, hv⟩) (hvertexSupport A.originVertex)
    have hvertexCoord : |axis.coord v - A.origin| ≤ Metric.diam C.region.support := by
      have horigin : A.origin = axis.coord A.originVertex := A.origin_eq
      calc
        |axis.coord v - A.origin| = |axis.coord v - axis.coord A.originVertex| := by rw [horigin]
        _ ≤ dist v A.originVertex := sourceGeometry_coord_abs_le axis _ _
        _ ≤ Metric.diam C.region.support := hdistVertex
    have hcoordAdd : axis.coord (v + t) = axis.coord v + axis.coord t := by
      cases axis <;> rfl
    have hanchorDelta : J.left - axis.coord t = axis.coord v - A.origin := by
      rw [← hvalue, hcoordAdd]
      ring
    have hcoordDist : |axis.coord s - axis.coord t| ≤
        4 * Metric.diam C.region.support := by
      calc
        |axis.coord s - axis.coord t| =
            |(axis.coord s - J.left) + (J.left - axis.coord t)| := by congr 1; ring
        _ ≤ |axis.coord s - J.left| + |J.left - axis.coord t| := abs_add_le _ _
        _ ≤ 3 * Metric.diam C.region.support + Metric.diam C.region.support :=
          add_le_add hleft (by rw [hanchorDelta]; exact hvertexCoord)
        _ = 4 * Metric.diam C.region.support := by ring
    obtain ⟨c, hc⟩ := hline
    have htrans : axis.transverseCoord s = axis.transverseCoord t :=
      (hc s hsS).trans (hc t htS).symm
    apply Or.inl
    change dist s t ≤ 4 * Metric.diam C.region.support + 1
    rw [aligned_centers_dist_eq_abs_axisCoord axis htrans]
    exact hcoordDist.trans (by linarith)
  · let t := tR
    let v := vR
    have htS := htR
    have hv := hvR
    have hvalue := hrightValue
    have hvertexSupport (w : ↥C.region.vertices) :
        (w : Tiling.Plane) ∈ C.region.support := by
      rw [← C.region.isPolygonal.closure_interior]
      exact frontier_subset_closure
        (IntrinsicVertices.region_vertices_subset_frontier C.region w.2)
    have hdistVertex : dist (v : Tiling.Plane) A.originVertex ≤
        Metric.diam C.region.support :=
      Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded
        (hvertexSupport ⟨v, hv⟩) (hvertexSupport A.originVertex)
    have hvertexCoord : |axis.coord v - A.origin| ≤ Metric.diam C.region.support := by
      have horigin : A.origin = axis.coord A.originVertex := A.origin_eq
      calc
        |axis.coord v - A.origin| = |axis.coord v - axis.coord A.originVertex| := by rw [horigin]
        _ ≤ dist v A.originVertex := sourceGeometry_coord_abs_le axis _ _
        _ ≤ Metric.diam C.region.support := hdistVertex
    have hcoordAdd : axis.coord (v + t) = axis.coord v + axis.coord t := by
      cases axis <;> rfl
    have hanchorDelta : J.right - axis.coord t = axis.coord v - A.origin := by
      rw [← hvalue, hcoordAdd]
      ring
    have hcoordDist : |axis.coord s - axis.coord t| ≤
        4 * Metric.diam C.region.support := by
      calc
        |axis.coord s - axis.coord t| =
            |(axis.coord s - J.right) + (J.right - axis.coord t)| := by congr 1; ring
        _ ≤ |axis.coord s - J.right| + |J.right - axis.coord t| := abs_add_le _ _
        _ ≤ 3 * Metric.diam C.region.support + Metric.diam C.region.support :=
          add_le_add hright (by rw [hanchorDelta]; exact hvertexCoord)
        _ = 4 * Metric.diam C.region.support := by ring
    obtain ⟨c, hc⟩ := hline
    have htrans : axis.transverseCoord s = axis.transverseCoord t :=
      (hc s hsS).trans (hc t htS).symm
    apply Or.inr
    change dist s t ≤ 4 * Metric.diam C.region.support + 1
    rw [aligned_centers_dist_eq_abs_axisCoord axis htrans]
    exact hcoordDist.trans (by linarith)

private theorem twoEndpointCenterWindows_finite_card_bound
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres)
    (tL tR : Tiling.Plane) (htL : tL ∈ C.centres) (htR : tR ∈ C.centres)
    (r : ℝ) (hr : 0 < r) :
    let W := (C.centres ∩ Metric.closedBall tL r) ∪
      (C.centres ∩ Metric.closedBall tR r)
    W.Finite ∧ W.ncard ≤ 2 *
      ((C.centres - C.centres) ∩ Metric.closedBall 0 r).ncard := by
  let WL := C.centres ∩ Metric.closedBall tL r
  let WR := C.centres ∩ Metric.closedBall tR r
  let W := WL ∪ WR
  have hWL : WL.Finite := by
    simpa only [WL] using
      hT.1 (Metric.closedBall tL r) Metric.isBounded_closedBall
  have hWR : WR.Finite := by
    simpa only [WR] using
      hT.1 (Metric.closedBall tR r) Metric.isBounded_closedBall
  have hboundL := boundedCenterWindow_ncard_le_differenceAlphabet hT tL htL r hr
  have hboundR := boundedCenterWindow_ncard_le_differenceAlphabet hT tR htR r hr
  constructor
  · exact hWL.union hWR
  · change (WL ∪ WR).ncard ≤ 2 *
      ((C.centres - C.centres) ∩ Metric.closedBall 0 r).ncard
    calc
      (WL ∪ WR).ncard ≤ WL.ncard + WR.ncard := Set.ncard_union_le WL WR
      _ ≤ ((C.centres - C.centres) ∩ Metric.closedBall 0 r).ncard +
          ((C.centres - C.centres) ∩ Metric.closedBall 0 r).ncard :=
        add_le_add hboundL hboundR
      _ = 2 * ((C.centres - C.centres) ∩ Metric.closedBall 0 r).ncard := by omega

private theorem nonbulkContributingCenters_finite_card_bound
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres)
    {axis : Axis} (A : NormalizedGenericSection C axis) {S : Set Tiling.Plane}
    (hS : S ⊆ C.centres)
    (hline : ∃ c, ∀ s ∈ S, axis.transverseCoord s = c)
    (J : BoundedOccupiedTraceComponent A S) :
    let E := {s | s ∈ S ∧ s ∉ bulkCentres A S J ∧
      ∃ i : Fin A.raw.presentation.n, ∃ x : ℝ,
        x ∈ Set.Ioo
          (A.raw.presentation.left i + axis.coord s - A.origin)
          (A.raw.presentation.right i + axis.coord s - A.origin) ∧
        x ∈ Set.Ioo J.left J.right}
    E.Finite ∧ E.ncard ≤
      2 * ((C.centres - C.centres) ∩
        Metric.closedBall 0 (4 * Metric.diam C.region.support + 1)).ncard := by
  classical
  obtain ⟨⟨tL, htL, vL, hvL, hleft⟩, tR, htR, vR, hvR, hright⟩ :=
    boundedOccupiedTraceComponent_endpointAnchors hT A hS hline J
  let r := 4 * Metric.diam C.region.support + 1
  have hr : 0 < r := by
    dsimp [r]
    have hdiam := region_support_diam_pos C.region
    linarith
  let W := (C.centres ∩ Metric.closedBall tL r) ∪
    (C.centres ∩ Metric.closedBall tR r)
  have hW := twoEndpointCenterWindows_finite_card_bound hT tL tR
    (hS htL) (hS htR) r hr
  have hEsub : {s | s ∈ S ∧ s ∉ bulkCentres A S J ∧
      ∃ i : Fin A.raw.presentation.n, ∃ x : ℝ,
        x ∈ Set.Ioo
          (A.raw.presentation.left i + axis.coord s - A.origin)
          (A.raw.presentation.right i + axis.coord s - A.origin) ∧
        x ∈ Set.Ioo J.left J.right} ⊆ W := by
    intro s hs
    rcases hs with ⟨hsS, hsNotBulk, ⟨i, x, hxI, hxJ⟩⟩
    have hnear := nonbulkContributingCenter_in_endpointWindows
      hT A hS hline J tL tR htL htR vL vR hvL hvR hleft hright
      hsS hsNotBulk ⟨i, x, hxI, hxJ⟩
    rcases hnear with hleftNear | hrightNear
    · apply Set.mem_union_left
      refine ⟨hS hsS, ?_⟩
      exact Metric.mem_closedBall.mpr (by simpa [r] using hleftNear)
    · apply Set.mem_union_right
      refine ⟨hS hsS, ?_⟩
      exact Metric.mem_closedBall.mpr (by simpa [r] using hrightNear)
  constructor
  · exact hW.1.subset hEsub
  · calc
      {s | s ∈ S ∧ s ∉ bulkCentres A S J ∧
        ∃ i : Fin A.raw.presentation.n, ∃ x : ℝ,
          x ∈ Set.Ioo
            (A.raw.presentation.left i + axis.coord s - A.origin)
            (A.raw.presentation.right i + axis.coord s - A.origin) ∧
          x ∈ Set.Ioo J.left J.right}.ncard ≤ W.ncard :=
        Set.ncard_le_ncard hEsub hW.1
      _ ≤ 2 * ((C.centres - C.centres) ∩ Metric.closedBall 0 r).ncard := by
        simpa [W, r] using hW.2

private theorem strictOrder_of_locallyFinite_consecutive_values
    {ι : Type*} (v w : ι → ℝ)
    (hlocal : ∀ a b : ℝ,
      ({x : ℝ | ∃ i, v i = x} ∩ Set.Icc a b).Finite)
    (heq : ∀ i j, v i = v j → w i = w j)
    (hadj : ∀ i j, v i < v j →
      (∀ k, v i < v k → v k < v j → False) → w i < w j) :
    ∀ i j, v i < v j → w i < w j := by
  let E : Set ℝ := {x | ∃ i, v i = x}
  let α := {x : ℝ // x ∈ E}
  let f : α → ℝ := fun x => w (Classical.choose x.2)
  have hchoose (x : α) : v (Classical.choose x.2) = x.1 := Classical.choose_spec x.2
  have hlocalSubtype : ∀ a b : α, (Set.Icc a b).Finite := by
    intro a b
    apply Set.Finite.of_injOn (f := fun x : α => (x : ℝ))
        (s := Set.Icc a b) (t := E ∩ Set.Icc (a : ℝ) (b : ℝ))
    · intro x hx
      exact ⟨x.2, hx.1, hx.2⟩
    · intro x hx y hy hxy
      exact Subtype.ext hxy
    · simpa [E] using hlocal (a : ℝ) (b : ℝ)
  let : LocallyFiniteOrder α := LocallyFiniteOrder.ofFiniteIcc hlocalSubtype
  have hf_repr (i : ι) : f ⟨v i, ⟨i, rfl⟩⟩ = w i := by
    dsimp [f]
    apply heq
    exact hchoose ⟨v i, ⟨i, rfl⟩⟩
  have hf_strict : StrictMono f := by
    rw [strictMono_iff_forall_covBy]
    intro a b hab
    let i := Classical.choose a.2
    let j := Classical.choose b.2
    have hi : v i = a.1 := Classical.choose_spec a.2
    have hj : v j = b.1 := Classical.choose_spec b.2
    have hij : v i < v j := by rw [hi, hj]; exact hab.1
    have hno : ∀ k, v i < v k → v k < v j → False := by
      intro k hik hkj
      apply hab.2 (c := ⟨v k, ⟨k, rfl⟩⟩)
      · change a.1 < v k
        simpa [hi] using hik
      · change v k < b.1
        simpa [hj] using hkj
    have hwiwj : w i < w j := hadj i j hij hno
    change w i < w j
    exact hwiwj
  intro i j hij
  calc
    w i = f ⟨v i, ⟨i, rfl⟩⟩ := (hf_repr i).symm
    _ < f ⟨v j, ⟨j, rfl⟩⟩ := hf_strict hij
    _ = w j := hf_repr j

private theorem endpointFiniteWindow_homeomorph
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A) (a b : ℝ) :
    ∃ h : ℝ ≃ₜ ℝ, StrictMono h ∧
      ∀ e : IndexedSectionEndpoint A S, a ≤ e.sourceValue → e.sourceValue ≤ b →
        h e.sourceValue = IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e := by
  classical
  let V := {x | ∃ e : IndexedSectionEndpoint A S, e.sourceValue = x} ∩ Set.Icc a b
  have hV : V.Finite := E.sourceValues_locallyFinite a b
  let F := hV.toFinset
  have hlabel (x : ↥F) : ∃ e : IndexedSectionEndpoint A S, e.sourceValue = x.1 :=
    (hV.mem_toFinset.mp x.2).1
  let label (x : ↥F) := Classical.choose (hlabel x)
  have hsource (x : ↥F) : (label x).sourceValue = x.1 := Classical.choose_spec (hlabel x)
  let f : ↥F → ℝ := fun x =>
    IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) (label x)
  have hf : StrictMono f := by
    intro x y hxy
    apply (allEndpointWeakOrderTransport_endpoint_lt_iff E (label x) (label y)).mp
    rw [hsource, hsource]
    exact hxy
  obtain ⟨h, hhmono, hh⟩ := exists_strictMonoHomeomorph_extension F f hf
  refine ⟨h, hhmono, ?_⟩
  intro e hae heb
  have heF : e.sourceValue ∈ F := hV.mem_toFinset.mpr ⟨⟨e, rfl⟩, hae, heb⟩
  have ht := hh ⟨e.sourceValue, heF⟩
  have heq : f ⟨e.sourceValue, heF⟩ =
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e :=
    (allEndpointWeakOrderTransport_endpoint_eq_iff E _ e).mp
      (hsource ⟨e.sourceValue, heF⟩)
  exact ht.trans heq

private abbrev SourceEndpointValues
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) (S : Set ↥C.centres) :=
  {x : ℝ // ∃ e : IndexedSectionEndpoint A S, e.sourceValue = x}

private abbrev TargetEndpointValues
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} (A : NormalizedGenericSection C axis) :=
  {x : ℝ // ∃ e : IndexedSectionEndpoint A S,
    IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e = x}

private noncomputable def endpointValueOrderIso
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A) :
    SourceEndpointValues A S ≃o
      TargetEndpointValues (D := D) (Tphi := Tphi) (S := S) A := by
  let toTarget (x : SourceEndpointValues A S) :
      TargetEndpointValues (D := D) (Tphi := Tphi) (S := S) A := by
    let e := Classical.choose x.2
    exact ⟨IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e, ⟨e, rfl⟩⟩
  let toSource (y : TargetEndpointValues (D := D) (Tphi := Tphi) (S := S) A) :
      SourceEndpointValues A S := by
    let e := Classical.choose y.2
    exact ⟨e.sourceValue, ⟨e, rfl⟩⟩
  refine {
    toFun := toTarget
    invFun := toSource
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · intro x
    apply Subtype.ext
    let e := Classical.choose x.2
    have he : e.sourceValue = x.1 := Classical.choose_spec x.2
    let y := toTarget x
    let f := Classical.choose y.2
    have hf : IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f = y.1 :=
      Classical.choose_spec y.2
    have hye : y.1 = IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e := rfl
    have htarget : IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f =
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e := hf.trans hye
    have hsource := (allEndpointWeakOrderTransport_endpoint_eq_iff E f e).mpr htarget
    change f.sourceValue = x.1
    exact hsource.trans he
  · intro y
    apply Subtype.ext
    let e := Classical.choose y.2
    have he : IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e = y.1 :=
      Classical.choose_spec y.2
    let x := toSource y
    let f := Classical.choose x.2
    have hf : f.sourceValue = x.1 := Classical.choose_spec x.2
    have hxe : x.1 = e.sourceValue := rfl
    have hsource : f.sourceValue = e.sourceValue := hf.trans hxe
    have htarget := (allEndpointWeakOrderTransport_endpoint_eq_iff E f e).mp hsource
    change IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f = y.1
    exact htarget.trans he
  · intro x y
    let e := Classical.choose x.2
    let f := Classical.choose y.2
    change IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ≤
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f ↔
        x.1 ≤ y.1
    have he : e.sourceValue = x.1 := Classical.choose_spec x.2
    have hf : f.sourceValue = y.1 := Classical.choose_spec y.2
    rw [← he, ← hf]
    exact (E.weakOrder_iff e f).symm

private theorem endpointValueOrderIso_apply_coe
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (x : SourceEndpointValues A S) :
    ((endpointValueOrderIso E x :
      TargetEndpointValues (D := D) (Tphi := Tphi) (S := S) A) : ℝ) =
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
        (Classical.choose x.2) := rfl

private theorem endpointValueOrderIso_apply_label
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (e : IndexedSectionEndpoint A S) :
    ((endpointValueOrderIso E ⟨e.sourceValue, ⟨e, rfl⟩⟩ :
      TargetEndpointValues (D := D) (Tphi := Tphi) (S := S) A) : ℝ) =
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e := by
  let x : SourceEndpointValues A S := ⟨e.sourceValue, ⟨e, rfl⟩⟩
  let f := Classical.choose x.2
  have hf : f.sourceValue = x.1 := Classical.choose_spec x.2
  rw [endpointValueOrderIso_apply_coe]
  change IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f =
    IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e
  exact (allEndpointWeakOrderTransport_endpoint_eq_iff E f e).mp (by simpa [x] using hf)

private theorem endpointValueOrderIso_symm_apply_label
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (e : IndexedSectionEndpoint A S) :
    (((endpointValueOrderIso E).symm
      ⟨IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e, ⟨e, rfl⟩⟩ :
        SourceEndpointValues A S) : ℝ) = e.sourceValue := by
  let y : TargetEndpointValues (D := D) (Tphi := Tphi) (S := S) A :=
    ⟨IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e, ⟨e, rfl⟩⟩
  let f := Classical.choose y.2
  have hf : IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f = y.1 :=
    Classical.choose_spec y.2
  change f.sourceValue = e.sourceValue
  exact (allEndpointWeakOrderTransport_endpoint_eq_iff E f e).mpr (by simpa [y] using hf)

private def IndexedSectionEndpoint.translatedVertex
    {C : ApproximationContext.{0}} {axis : Axis}
    {A : NormalizedGenericSection C axis} {S : Set ↥C.centres}
    (e : IndexedSectionEndpoint A S) : ↥C.translatedVertices :=
  ⟨e.label.vertex.1 + e.centre.1.1, by
    rcases e.label.vertex.2 with hv
    exact ⟨e.label.vertex.1, hv, e.centre.1.1, e.centre.1.2, rfl⟩⟩

private theorem mapPoint_add_axis
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (axis : Axis) (p q : {z : Tiling.Plane //
      z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}) :
    axis.coord (mapPoint phi ⟨p.1 + q.1, by
        exact C.coordinateSpace.add_mem p.2.1 q.2.1,
      by exact C.coordinateSpace.add_mem p.2.2 q.2.2⟩) =
      axis.coord (mapPoint phi p) + axis.coord (mapPoint phi q) := by
  cases axis
  · simp only [Axis.coord, mapPoint, mapScalar, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    have h : (⟨p.1.re + q.1.re, C.coordinateSpace.add_mem p.2.1 q.2.1⟩ :
        C.coordinateSpace) = ⟨p.1.re, p.2.1⟩ + ⟨q.1.re, q.2.1⟩ := by
      apply Subtype.ext
      rfl
    rw [h, map_add]
    norm_cast
  · simp only [Axis.coord, mapPoint, mapScalar, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, zero_add]
    have h : (⟨p.1.im + q.1.im, C.coordinateSpace.add_mem p.2.2 q.2.2⟩ :
        C.coordinateSpace) = ⟨p.1.im, p.2.2⟩ + ⟨q.1.im, q.2.2⟩ := by
      apply Subtype.ext
      rfl
    rw [h, map_add]
    norm_cast

private theorem endpoint_local_sign_transport
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (hphi : IsEpsilonApproximation C P.threshold phi)
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {A : NormalizedGenericSection C axis} {S : Set ↥C.centres}
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (e f : IndexedSectionEndpoint A S)
    (hclose : dist (e.translatedVertex : Tiling.Plane)
      (f.translatedVertex : Tiling.Plane) < P.controlRadius) :
    Real.sign (e.sourceValue - f.sourceValue) =
      Real.sign (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e -
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f) := by
  have hreflect := (deformation_reflectsFiniteValues P phi hphi axis
    e.translatedVertex f.translatedVertex e.translatedVertex f.translatedVertex
    hclose hclose).1
  have hsource : axis.coord
      ((e.translatedVertex : Tiling.Plane) - (f.translatedVertex : Tiling.Plane)) =
      e.sourceValue - f.sourceValue := by
    rw [IndexedSectionEndpoint.sourceValue, IndexedSectionEndpoint.sourceValue]
    rw [SectionEndpointLabel.rawValue_eq_vertex_coord e.label,
      SectionEndpointLabel.rawValue_eq_vertex_coord f.label]
    cases axis <;> simp [IndexedSectionEndpoint.translatedVertex, Axis.coord,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  have htarget : axis.coord
      (mapTranslatedVertex phi e.translatedVertex - mapTranslatedVertex phi f.translatedVertex) =
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e -
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f := by
    have hpoint (g : IndexedSectionEndpoint A S) :
        C.translatedVertexPoint g.translatedVertex =
          ⟨(C.vertexPoint g.label.vertex.1 g.label.vertex.2).1 +
            (C.centrePoint g.centre.1.1 g.centre.1.2).1,
            C.coordinateSpace.add_mem
              (C.vertexPoint g.label.vertex.1 g.label.vertex.2).2.1
              (C.centrePoint g.centre.1.1 g.centre.1.2).2.1,
            C.coordinateSpace.add_mem
              (C.vertexPoint g.label.vertex.1 g.label.vertex.2).2.2
              (C.centrePoint g.centre.1.1 g.centre.1.2).2.2⟩ := by
      apply Subtype.ext
      rfl
    have hcoord (g : IndexedSectionEndpoint A S) :
        axis.coord (mapTranslatedVertex phi g.translatedVertex) =
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) g +
            mapScalar phi A.originScalar := by
      rw [mapTranslatedVertex, hpoint g, mapPoint_add_axis,
        IndexedSectionEndpoint.targetValue]
      rw [D.vertex_agreement g.label.vertex.1 g.label.vertex.2,
        hTphi g.centre.1]
      cases axis <;> simp [Axis.coord, Complex.add_re, Complex.add_im]
    have hcoord_sub (z w : Tiling.Plane) :
        axis.coord (z - w) = axis.coord z - axis.coord w := by
      cases axis <;> simp [Axis.coord, Complex.sub_re, Complex.sub_im]
    rw [hcoord_sub, hcoord e, hcoord f]
    ring
  rw [hsource, htarget] at hreflect
  exact hreflect.symm

private theorem endpoint_translated_distance_le
    {C : ApproximationContext.{0}} {axis : Axis}
    {A : NormalizedGenericSection C axis} {S : Set ↥C.centres}
    (hline : ∃ c, ∀ s : S, axis.transverseCoord s.1.1 = c)
    (e f : IndexedSectionEndpoint A S) :
    dist (e.translatedVertex : Tiling.Plane) (f.translatedVertex : Tiling.Plane) ≤
      |e.sourceValue - f.sourceValue| + Metric.diam C.region.support := by
  have hvSupport (v : ↥C.region.vertices) : (v : Tiling.Plane) ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier C.region v.2)
  have hdiam : dist (e.label.vertex : Tiling.Plane) f.label.vertex ≤
      Metric.diam C.region.support :=
    Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded
      (hvSupport e.label.vertex) (hvSupport f.label.vertex)
  have hax : axis.coord
      ((e.translatedVertex : Tiling.Plane) - (f.translatedVertex : Tiling.Plane)) =
      e.sourceValue - f.sourceValue := by
    rw [IndexedSectionEndpoint.sourceValue, IndexedSectionEndpoint.sourceValue,
      SectionEndpointLabel.rawValue_eq_vertex_coord e.label,
      SectionEndpointLabel.rawValue_eq_vertex_coord f.label]
    cases axis <;> simp [IndexedSectionEndpoint.translatedVertex, Axis.coord,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  have htrans : |axis.transverseCoord
      ((e.translatedVertex : Tiling.Plane) - (f.translatedVertex : Tiling.Plane))| ≤
      Metric.diam C.region.support := by
    obtain ⟨c, hc⟩ := hline
    have he := hc e.centre
    have hf := hc f.centre
    cases axis
    · simp only [Axis.transverseCoord] at he hf ⊢
      have he' : (e.centre.1.1 : Tiling.Plane).im = c := he
      have hf' : (f.centre.1.1 : Tiling.Plane).im = c := hf
      have hsum : ((e.translatedVertex : Tiling.Plane) -
          (f.translatedVertex : Tiling.Plane)).im =
          (e.label.vertex.1 - f.label.vertex.1).im := by
        simp [IndexedSectionEndpoint.translatedVertex, Complex.add_im, he', hf']
      rw [hsum]
      have hv : |(e.label.vertex.1 - f.label.vertex.1).im| ≤
          dist e.label.vertex.1 f.label.vertex.1 := by
        have hh := Complex.abs_im_le_norm (e.label.vertex.1 - f.label.vertex.1)
        simpa [dist_eq_norm] using hh
      exact hv.trans hdiam
    · simp only [Axis.transverseCoord] at he hf ⊢
      have he' : (e.centre.1.1 : Tiling.Plane).re = c := he
      have hf' : (f.centre.1.1 : Tiling.Plane).re = c := hf
      have hsum : ((e.translatedVertex : Tiling.Plane) -
          (f.translatedVertex : Tiling.Plane)).re =
          (e.label.vertex.1 - f.label.vertex.1).re := by
        simp [IndexedSectionEndpoint.translatedVertex, Complex.add_re, he', hf']
      rw [hsum]
      have hv : |(e.label.vertex.1 - f.label.vertex.1).re| ≤
          dist e.label.vertex.1 f.label.vertex.1 := by
        have hh := Complex.abs_re_le_norm (e.label.vertex.1 - f.label.vertex.1)
        simpa [dist_eq_norm] using hh
      exact hv.trans hdiam
  cases axis with
  | horizontal =>
      have hnorm := Complex.norm_le_abs_re_add_abs_im
        ((e.translatedVertex : Tiling.Plane) - (f.translatedVertex : Tiling.Plane))
      have hax' : |((e.translatedVertex : Tiling.Plane) -
          (f.translatedVertex : Tiling.Plane)).re| =
          |e.sourceValue - f.sourceValue| := by simpa [Axis.coord] using congrArg abs hax
      have htr' : |((e.translatedVertex : Tiling.Plane) -
          (f.translatedVertex : Tiling.Plane)).im| ≤ Metric.diam C.region.support := by
        simpa [Axis.transverseCoord] using htrans
      rw [dist_eq_norm]
      calc
        ‖(e.translatedVertex : Tiling.Plane) - (f.translatedVertex : Tiling.Plane)‖ ≤ _ := hnorm
        _ ≤ |e.sourceValue - f.sourceValue| + Metric.diam C.region.support :=
          add_le_add (le_of_eq hax') htr'
  | vertical =>
      have hnorm := Complex.norm_le_abs_re_add_abs_im
        ((e.translatedVertex : Tiling.Plane) - (f.translatedVertex : Tiling.Plane))
      have hax' : |((e.translatedVertex : Tiling.Plane) -
          (f.translatedVertex : Tiling.Plane)).im| =
          |e.sourceValue - f.sourceValue| := by simpa [Axis.coord] using congrArg abs hax
      have htr' : |((e.translatedVertex : Tiling.Plane) -
          (f.translatedVertex : Tiling.Plane)).re| ≤ Metric.diam C.region.support := by
        simpa [Axis.transverseCoord] using htrans
      rw [dist_eq_norm]
      calc
        ‖(e.translatedVertex : Tiling.Plane) - (f.translatedVertex : Tiling.Plane)‖ ≤ _ := hnorm
        _ ≤ |e.sourceValue - f.sourceValue| + Metric.diam C.region.support := by
          simpa [add_comm] using add_le_add htr' (le_of_eq hax')

private theorem linked_axis_cut_edge
    {U : Set Tiling.Plane} {axis : Axis} {G x y : ℝ}
    {a b : Tiling.Plane}
    (hpath : Relation.ReflTransGen
      (fun u v : Tiling.Plane => u ∈ U ∧ v ∈ U ∧ dist u v < G) a b)
    (hno : ∀ z ∈ U, x < axis.coord z → axis.coord z < y → False)
    (hxy : x < y) (ha : axis.coord a ≤ x) (hb : y ≤ axis.coord b) :
    ∃ u v : Tiling.Plane, u ∈ U ∧ v ∈ U ∧ dist u v < G ∧
      axis.coord u ≤ x ∧ y ≤ axis.coord v := by
  induction hpath generalizing ha with
  | refl => linarith
  | @tail m b htail hedge ih =>
      rcases hedge with ⟨hm, hbU, hdist⟩
      by_cases hmx : axis.coord m ≤ x
      · exact ⟨m, b, hm, hbU, hdist, hmx, hb⟩
      · have hmy : y ≤ axis.coord m := by
          by_contra hnot
          have hxm : x < axis.coord m := lt_of_not_ge hmx
          have hmy' : axis.coord m < y := lt_of_not_ge hnot
          exact hno m hm hxm hmy'
        exact ih ha hmy

private theorem linked_path_has_nonself_edge
    {U : Set Tiling.Plane} {a b : Tiling.Plane} {G : ℝ}
    (hpath : Relation.ReflTransGen
      (fun u v : Tiling.Plane => u ∈ U ∧ v ∈ U ∧ dist u v < G) a b)
    (hab : a ≠ b) :
    ∃ u v : Tiling.Plane,
      u ∈ U ∧ v ∈ U ∧ dist u v < G ∧ u ≠ v := by
  induction hpath with
  | refl => exact (hab rfl).elim
  | @tail m b htail hedge ih =>
      by_cases ham : a = m
      · subst a
        rcases hedge with ⟨hm, hb, hdist⟩
        exact ⟨m, b, hm, hb, hdist, hab⟩
      · exact ih ham

private theorem originEndpoint_sourceValue
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) {S : Set ↥C.centres}
    (s : S) :
    (IndexedSectionEndpoint.mk ⟨A.originInterval, false⟩ s).sourceValue =
      axis.coord s.1.1 := by
  simp [IndexedSectionEndpoint.sourceValue, SectionEndpointLabel.rawValue,
    A.raw.leftVertex_coord, A.originVertex_eq, A.origin_eq]

private theorem endpointPlaneSeparation_control
    {C : ApproximationContext.{0}} {axis : Axis}
    (P : FLCControlPackage C) {A : NormalizedGenericSection C axis}
    {S : Set ↥C.centres} {G δ d : ℝ} {N : ℕ}
    (hLinked : Linked G (Subtype.val '' S))
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ ≤ dist (s : Tiling.Plane) (t : Tiling.Plane))
    (hline : ∃ c, ∀ s : S, axis.transverseCoord s.1.1 = c)
    (hδ : 0 < δ) (hNδ : (N : ℝ) * δ > 4 * d)
    (hNG : (N : ℝ) * G + 2 * d < P.scale)
    (hd : d = Metric.diam C.region.support)
    (hdscale : d < P.scale)
    : (∀ (e f : IndexedSectionEndpoint A S),
        e.sourceValue < f.sourceValue →
        (∀ g : IndexedSectionEndpoint A S,
          ¬ (e.sourceValue < g.sourceValue ∧ g.sourceValue < f.sourceValue)) →
        dist (e.translatedVertex : Tiling.Plane) (f.translatedVertex : Tiling.Plane) <
          P.scale) ∧
      (∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
        IsEpsilonApproximation C P.threshold phi →
        ∀ (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane),
        (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
        Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
          (D.deformedRegion.toPolygonalRegion.placements
            (deformedCenterCarrierOn Tphi S)) →
        (∃ c, ∀ s : S, axis.transverseCoord (Tphi s.1) = c) →
        P.localError < δ / 2 →
        P.localError ≤ Metric.diam C.region.support →
        Nonempty (AllEndpointWeakOrderTransport phi D Tphi axis S A)) := by
  have hcontrolled (e f : IndexedSectionEndpoint A S)
      (hxy : e.sourceValue < f.sourceValue)
      (hadj : ∀ g : IndexedSectionEndpoint A S,
        ¬ (e.sourceValue < g.sourceValue ∧ g.sourceValue < f.sourceValue)) :
      dist (e.translatedVertex : Tiling.Plane) (f.translatedVertex : Tiling.Plane) <
        P.scale := by
    have hd0 : 0 ≤ d := by rw [hd]; exact Metric.diam_nonneg
    have hpair := endpoint_translated_distance_le hline e f
    by_cases hgap : f.sourceValue - e.sourceValue ≤ 2 * d
    · by_cases hcentres : e.centre.1.1 = f.centre.1.1
      · have hvSupport (v : ↥C.region.vertices) :
            (v : Tiling.Plane) ∈ C.region.support := by
          rw [← C.region.isPolygonal.closure_interior]
          exact frontier_subset_closure
            (IntrinsicVertices.region_vertices_subset_frontier C.region v.2)
        have hvertex : dist (e.label.vertex : Tiling.Plane) f.label.vertex ≤ d := by
          rw [hd]
          exact Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded
            (hvSupport e.label.vertex) (hvSupport f.label.vertex)
        have heqdist : dist (e.translatedVertex : Tiling.Plane)
            (f.translatedVertex : Tiling.Plane) =
              dist (e.label.vertex : Tiling.Plane) f.label.vertex := by
          simp [IndexedSectionEndpoint.translatedVertex, hcentres, dist_eq_norm,
            add_sub_add_right_eq_sub]
        rw [heqdist]
        exact lt_of_le_of_lt hvertex hdscale
      · obtain ⟨hne, hconn⟩ := hLinked
        have hsmallBound : dist (e.translatedVertex : Tiling.Plane)
            (f.translatedVertex : Tiling.Plane) ≤ 3 * d := by
          calc
            dist _ _ ≤ |e.sourceValue - f.sourceValue| + d := by simpa [hd] using hpair
            _ = f.sourceValue - e.sourceValue + d := by
              rw [abs_of_neg (by linarith : e.sourceValue - f.sourceValue < 0)]
              ring
            _ ≤ 3 * d := by nlinarith
        have hUe : (e.centre.1.1 : Tiling.Plane) ∈ Subtype.val '' S :=
          ⟨e.centre.1, e.centre.2, rfl⟩
        have hUf : (f.centre.1.1 : Tiling.Plane) ∈ Subtype.val '' S :=
          ⟨f.centre.1, f.centre.2, rfl⟩
        have hpath := hconn (e.centre.1.1) hUe (f.centre.1.1) hUf
        obtain ⟨u, v, hu, hv, huv, hneuv⟩ :=
          linked_path_has_nonself_edge hpath hcentres
        rcases hu with ⟨su, hsu, rfl⟩
        rcases hv with ⟨sv, hsv, rfl⟩
        have hst : su ≠ sv := by
          intro h
          apply hneuv
          exact congrArg (fun t : ↥C.centres => (t : Tiling.Plane)) h
        have hδG : δ < G :=
          lt_of_le_of_lt (hsep su hsu sv hsv hst) huv
        have hNpos : 0 < (N : ℝ) := by nlinarith [hNδ, hd0]
        have hNδG : (N : ℝ) * δ < (N : ℝ) * G :=
          mul_lt_mul_of_pos_left hδG hNpos
        have h4 : 4 * d < (N : ℝ) * G := lt_trans hNδ hNδG
        have h3scale : 3 * d < P.scale := by nlinarith [hNG, hd0, h4]
        exact lt_of_le_of_lt hsmallBound h3scale
    · have hlarge : 2 * d < f.sourceValue - e.sourceValue := lt_of_not_ge hgap
      have heoffset : |e.sourceValue - axis.coord e.centre.1.1| ≤ d := by
        have hvSupport (v : ↥C.region.vertices) :
            (v : Tiling.Plane) ∈ C.region.support := by
          rw [← C.region.isPolygonal.closure_interior]
          exact frontier_subset_closure
            (IntrinsicVertices.region_vertices_subset_frontier C.region v.2)
        have hvertex : dist (e.label.vertex : Tiling.Plane) A.originVertex ≤ d := by
          rw [hd]
          exact Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded
            (hvSupport e.label.vertex) (hvSupport A.originVertex)
        have hcoord := sourceGeometry_coord_abs_le axis e.label.vertex.1 A.originVertex.1
        have hcoord' : |axis.coord e.label.vertex.1 - axis.coord A.originVertex.1| ≤ d :=
          le_trans hcoord hvertex
        calc
          |e.sourceValue - axis.coord e.centre.1.1| =
              |axis.coord e.label.vertex.1 - axis.coord A.originVertex.1| := by
            rw [IndexedSectionEndpoint.sourceValue,
              SectionEndpointLabel.rawValue_eq_vertex_coord e.label, A.origin_eq]
            congr 1
            ring
          _ ≤ d := hcoord'
      have hfoffset : |f.sourceValue - axis.coord f.centre.1.1| ≤ d := by
        have hvSupport (v : ↥C.region.vertices) :
            (v : Tiling.Plane) ∈ C.region.support := by
          rw [← C.region.isPolygonal.closure_interior]
          exact frontier_subset_closure
            (IntrinsicVertices.region_vertices_subset_frontier C.region v.2)
        have hvertex : dist (f.label.vertex : Tiling.Plane) A.originVertex ≤ d := by
          rw [hd]
          exact Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded
            (hvSupport f.label.vertex) (hvSupport A.originVertex)
        have hcoord := sourceGeometry_coord_abs_le axis f.label.vertex.1 A.originVertex.1
        have hcoord' : |axis.coord f.label.vertex.1 - axis.coord A.originVertex.1| ≤ d :=
          le_trans hcoord hvertex
        calc
          |f.sourceValue - axis.coord f.centre.1.1| =
              |axis.coord f.label.vertex.1 - axis.coord A.originVertex.1| := by
            rw [IndexedSectionEndpoint.sourceValue,
              SectionEndpointLabel.rawValue_eq_vertex_coord f.label, A.origin_eq]
            congr 1
            ring
          _ ≤ d := hcoord'
      have hnoCentre : ∀ z ∈ (Subtype.val '' S),
          e.sourceValue < axis.coord z → axis.coord z < f.sourceValue → False := by
        intro z hz hx hy
        rcases hz with ⟨s, hs, rfl⟩
        let g : IndexedSectionEndpoint A S := ⟨⟨A.originInterval, false⟩, ⟨s, hs⟩⟩
        have hg : g.sourceValue = axis.coord s.1 := by
          simpa [g] using originEndpoint_sourceValue A ⟨s, hs⟩
        exact hadj g ⟨by rw [hg]; exact hx, by rw [hg]; exact hy⟩
      have hcle : axis.coord e.centre.1.1 ≤ e.sourceValue := by
        have hupper := (abs_le.mp heoffset).1
        by_contra hnot
        have hxe : e.sourceValue < axis.coord e.centre.1.1 := lt_of_not_ge hnot
        have hcy : axis.coord e.centre.1.1 < f.sourceValue := by linarith [hupper, hlarge]
        exact hnoCentre (e.centre.1.1) (by exact ⟨e.centre.1, e.centre.2, rfl⟩) hxe hcy
      have hcrf : f.sourceValue ≤ axis.coord f.centre.1.1 := by
        have hlower := (abs_le.mp hfoffset).2
        by_contra hnot
        have hfy : axis.coord f.centre.1.1 < f.sourceValue := lt_of_not_ge hnot
        have hxf : e.sourceValue < axis.coord f.centre.1.1 := by linarith [hlower, hlarge]
        exact hnoCentre (f.centre.1.1) (by exact ⟨f.centre.1, f.centre.2, rfl⟩) hxf hfy
      obtain ⟨hne, hconn⟩ := hLinked
      have hUe : (e.centre.1.1 : Tiling.Plane) ∈ Subtype.val '' S :=
        ⟨e.centre.1, e.centre.2, rfl⟩
      have hUf : (f.centre.1.1 : Tiling.Plane) ∈ Subtype.val '' S :=
        ⟨f.centre.1, f.centre.2, rfl⟩
      have hpath := hconn (e.centre.1.1) hUe (f.centre.1.1) hUf
      obtain ⟨u, v, hu, hv, huv, hucoord, hvcoord⟩ :=
        linked_axis_cut_edge hpath hnoCentre (by linarith) hcle hcrf
      have hproj : f.sourceValue - e.sourceValue ≤ dist u v := by
        have hcoord := sourceGeometry_coord_abs_le axis u v
        have huvcoord : axis.coord u ≤ axis.coord v := by
          exact le_trans hucoord (le_trans hxy.le hvcoord)
        have habs : |axis.coord u - axis.coord v| = axis.coord v - axis.coord u := by
          calc
            |axis.coord u - axis.coord v| = -(axis.coord u - axis.coord v) :=
              abs_of_nonpos (sub_nonpos.mpr huvcoord)
            _ = axis.coord v - axis.coord u := by ring
        rw [habs] at hcoord
        have hspan : f.sourceValue - e.sourceValue ≤ axis.coord v - axis.coord u := by
          linarith
        exact hspan.trans hcoord
      have hgapG : f.sourceValue - e.sourceValue < G := lt_of_le_of_lt hproj huv
      have hGpos : 0 < G := lt_trans (by linarith : 0 < f.sourceValue - e.sourceValue) hgapG
      have hNpos : 0 < (N : ℝ) := by nlinarith [hNδ, hd0]
      have hNone : 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hNpos.ne')
      have hGN : G ≤ (N : ℝ) * G := by nlinarith
      have hscale : G + d ≤ (N : ℝ) * G + 2 * d := by nlinarith [hd0, hGN]
      calc
        dist (e.translatedVertex : Tiling.Plane) (f.translatedVertex : Tiling.Plane) ≤
            |e.sourceValue - f.sourceValue| + d := by simpa [hd] using hpair
        _ = f.sourceValue - e.sourceValue + d := by
          rw [abs_of_neg (by linarith : e.sourceValue - f.sourceValue < 0)]
          ring
        _ < G + d := by simpa [add_comm] using add_lt_add_right hgapG d
        _ ≤ (N : ℝ) * G + 2 * d := hscale
        _ < P.scale := hNG
  refine ⟨hcontrolled, ?_⟩
  intro phi hphi D Tphi hTphi hpacking hlineT _hError _hErrorD
  have hsourceEqTargetEq (e f : IndexedSectionEndpoint A S) :
      e.sourceValue = f.sourceValue →
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e =
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f := by
    intro heq
    have hscalar : e.sourceCoordScalar A = f.sourceCoordScalar A := by
      apply Subtype.ext
      rw [IndexedSectionEndpoint.sourceCoordScalar_coe,
        IndexedSectionEndpoint.sourceCoordScalar_coe, heq]
    have hmap := congrArg (mapScalar phi) hscalar
    rw [IndexedSectionEndpoint.sourceCoordScalar_map hTphi e,
      IndexedSectionEndpoint.sourceCoordScalar_map hTphi f] at hmap
    exact hmap
  have hstrict : ∀ e f : IndexedSectionEndpoint A S,
      e.sourceValue < f.sourceValue →
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e <
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f := by
    apply strictOrder_of_locallyFinite_consecutive_values
      (v := fun e : IndexedSectionEndpoint A S => e.sourceValue)
      (w := fun e => IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e)
    · exact sourceEndpointValues_locallyFinite P.source_hasFLC axis A S hline
    · intro e f heq
      exact hsourceEqTargetEq e f heq
    · intro e f hlt hadj
      have hadj' : ∀ g : IndexedSectionEndpoint A S,
          ¬ (e.sourceValue < g.sourceValue ∧ g.sourceValue < f.sourceValue) := by
        intro g h
        exact hadj g h.1 h.2
      have hdist := hcontrolled e f hlt hadj'
      have hclose : dist (e.translatedVertex : Tiling.Plane)
          (f.translatedVertex : Tiling.Plane) < P.controlRadius :=
        lt_trans hdist P.scale_lt_controlRadius
      have hsign := endpoint_local_sign_transport (D := D) (Tphi := Tphi)
        P hphi hTphi e f hclose
      rw [Real.sign_of_neg (by linarith : e.sourceValue - f.sourceValue < 0)] at hsign
      have htargetNeg :
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e -
            IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f < 0 := by
        by_contra hnot
        have hnonneg := le_of_not_gt hnot
        rcases eq_or_lt_of_le hnonneg with heq | hpos
        · rw [heq.symm, Real.sign_zero] at hsign
          norm_num at hsign
        · rw [Real.sign_of_pos hpos] at hsign
          norm_num at hsign
      linarith
  have hweak (e f : IndexedSectionEndpoint A S) :
      e.sourceValue ≤ f.sourceValue ↔
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ≤
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f := by
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact (hstrict e f hlt).le
      · have htarget := hsourceEqTargetEq e f heq
        rw [htarget]
    · intro h
      by_contra hsource
      have hrev : f.sourceValue < e.sourceValue := lt_of_not_ge hsource
      have htarget := hstrict f e hrev
      linarith
  refine ⟨{
    indexedCentre_formula := hTphi
    weakOrder_iff := hweak
    source_interval := (endpoint_interval_fields D Tphi axis A S).1
    target_interval := (endpoint_interval_fields D Tphi axis A S).2
    source_union_eq := endpoint_source_union_eq axis A S
    target_union_eq := endpoint_target_union_eq D Tphi axis A S
    sourceValues_locallyFinite := sourceEndpointValues_locallyFinite
      P.source_hasFLC axis A S hline
    targetValues_locallyFinite := targetEndpointValues_locallyFinite
      D Tphi axis A S hpacking hlineT
    source_frontier_subset :=
      (sourceTrace_endpointControl P.source_hasFLC axis A S hline).2
    target_frontier_subset :=
      targetTrace_frontier_subset_endpoints D Tphi axis A S hpacking hlineT
  }⟩

private theorem adjacentEndpointPair_controlled
    {C : ApproximationContext.{0}} {axis : Axis}
    (P : FLCControlPackage C) {A : NormalizedGenericSection C axis}
    {S : Set ↥C.centres} {G δ d : ℝ} {N : ℕ}
    (hLinked : Linked G (Subtype.val '' S))
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ ≤ dist s.1.1 t.1.1)
    (hline : ∃ c, ∀ s : S, axis.transverseCoord s.1.1 = c)
    (hδ : 0 < δ) (hNδ : (N : ℝ) * δ > 4 * d)
    (hNG : (N : ℝ) * G + 2 * d < P.scale)
    (hd : d = Metric.diam C.region.support)
    (hdscale : d < P.scale)
    (e f : IndexedSectionEndpoint A S)
    (hxy : e.sourceValue < f.sourceValue)
    (hadj : ∀ g : IndexedSectionEndpoint A S,
      ¬ (e.sourceValue < g.sourceValue ∧ g.sourceValue < f.sourceValue)) :
    dist (e.translatedVertex : Tiling.Plane) (f.translatedVertex : Tiling.Plane) < P.scale := by
  have hPlane : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      δ ≤ dist (s : Tiling.Plane) (t : Tiling.Plane) := by
    intro s hs t ht hne
    have hreal := hsep s hs t ht hne
    have hcoord := sourceGeometry_coord_abs_le Axis.horizontal
      (s : Tiling.Plane) (t : Tiling.Plane)
    exact (show δ ≤ |(s : Tiling.Plane).re - (t : Tiling.Plane).re| by
      simpa only [Real.dist_eq] using hreal).trans hcoord
  exact (endpointPlaneSeparation_control P hLinked hPlane hline hδ hNδ hNG
    hd hdscale).1 e f hxy hadj


private noncomputable def componentSelectedIntervals
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) {S : Set Tiling.Plane}
    (J : BoundedOccupiedTraceComponent A S)
    (s : Tiling.Plane) : Finset (Fin A.raw.presentation.n) := by
  classical
  exact Finset.univ.filter fun i =>
    ((Set.Ioo
      (A.raw.presentation.left i + axis.coord s - A.origin)
      (A.raw.presentation.right i + axis.coord s - A.origin)) ∩
      Set.Ioo J.left J.right).Nonempty

private theorem bulkCenter_section_subset_component
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) {S : Set Tiling.Plane}
    (J : BoundedOccupiedTraceComponent A S) {s : Tiling.Plane}
    (hs : s ∈ bulkCentres A S J) :
    ((axis.coord s) +ᵥ A.carrier) ⊆ Set.Ioo J.left J.right := by
  have hs' := hs
  simp only [bulkCentres, Set.mem_ofPred_eq] at hs'
  intro x hx
  have hxClosure : x ∈ (axis.coord s) +ᵥ closure A.carrier := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx ⊢
    exact subset_closure hx
  have hxHull : x ∈ convexHull ℝ ((axis.coord s) +ᵥ closure A.carrier) :=
    subset_convexHull ℝ _ hxClosure
  exact hs'.2 hxHull

private theorem componentSelectedIntervals_eq_section_inter_component
    {C : ApproximationContext.{0}} {axis : Axis}
    (A : NormalizedGenericSection C axis) {S : Set Tiling.Plane}
    (J : BoundedOccupiedTraceComponent A S) {s : Tiling.Plane} (hs : s ∈ S) :
    ((axis.coord s) +ᵥ A.carrier) ∩ Set.Ioo J.left J.right =
      ⋃ i ∈ componentSelectedIntervals A J s,
        Set.Ioo
          (A.raw.presentation.left i + axis.coord s - A.origin)
          (A.raw.presentation.right i + axis.coord s - A.origin) := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxCarrier, hxJ⟩
    have hxA : x - axis.coord s ∈ A.carrier := by
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hxCarrier
    have hxRaw : A.origin + (x - axis.coord s) ∈ A.raw.rawCarrier := by
      rw [A.carrier_eq] at hxA
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg] using hxA
    have hxPresentation : x - axis.coord s + A.origin ∈
        ⋃ i : Fin A.raw.presentation.n,
          Set.Ioo (A.raw.presentation.left i) (A.raw.presentation.right i) := by
      have hxRaw' : x - axis.coord s + A.origin ∈ A.raw.rawCarrier := by
        simpa [add_comm] using hxRaw
      rw [A.raw.presentation.union_eq] at hxRaw'
      exact hxRaw'
    rcases Set.mem_iUnion.mp hxPresentation with ⟨i, hxi⟩
    have hxiTranslated : x ∈ Set.Ioo
        (A.raw.presentation.left i + axis.coord s - A.origin)
        (A.raw.presentation.right i + axis.coord s - A.origin) := by
      change A.raw.presentation.left i < x - axis.coord s + A.origin ∧
        x - axis.coord s + A.origin < A.raw.presentation.right i at hxi
      constructor <;> linarith
    have hselected : i ∈ componentSelectedIntervals A J s := by
      simp only [componentSelectedIntervals, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨x, hxiTranslated, hxJ⟩
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hselected, hxiTranslated⟩⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hi, hxi⟩
    have hselected := (Finset.mem_filter.mp hi).2
    obtain ⟨y, hyi, hyJ⟩ := hselected
    have hwhole := occupiedComponent_interval_subset A J hs i ⟨y, hyi, hyJ⟩
    have hxJ : x ∈ Set.Ioo J.left J.right := hwhole hxi
    have hxRaw : x - axis.coord s + A.origin ∈ A.raw.rawCarrier := by
      rw [A.raw.presentation.union_eq, Set.mem_iUnion]
      refine ⟨i, ?_⟩
      change A.raw.presentation.left i + axis.coord s - A.origin < x ∧
        x < A.raw.presentation.right i + axis.coord s - A.origin at hxi
      constructor <;> linarith
    have hxCarrier : x - axis.coord s ∈ A.carrier := by
      rw [A.carrier_eq, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
      simpa [neg_neg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hxRaw
    have hxTranslated : x ∈ (axis.coord s) +ᵥ A.carrier := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hxCarrier
    exact ⟨hxTranslated, hxJ⟩

private theorem boundedOccupiedTraceComponent_finite_section_split
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres)
    (axis : Axis) (A : NormalizedGenericSection C axis)
    (S : Set ↥C.centres)
    (_hpacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S)))
    (hline : ∃ c, ∀ s : S, axis.transverseCoord s.1.1 = c)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S)) :
    ∃ bulk exceptional : Finset Tiling.Plane,
      (bulk : Set Tiling.Plane) = bulkCentres A (Subtype.val '' S) J ∧
      (bulk : Set Tiling.Plane) ⊆ Subtype.val '' S ∧
      (exceptional : Set Tiling.Plane) ⊆ Subtype.val '' S ∧
      Disjoint (bulk : Set Tiling.Plane) (exceptional : Set Tiling.Plane) ∧
      exceptional.card ≤ 2 * ((C.centres - C.centres) ∩ Metric.closedBall 0
        (4 * Metric.diam C.region.support + 1)).ncard ∧
      ((A.carrier + axis.coord '' (Subtype.val '' S)) ∩ Set.Ioo J.left J.right) =
        (⋃ s ∈ bulk, ((axis.coord s) +ᵥ A.carrier) ∩ Set.Ioo J.left J.right) ∪
          (⋃ s ∈ exceptional,
            ((axis.coord s) +ᵥ A.carrier) ∩ Set.Ioo J.left J.right) := by
  classical
  let Splane : Set Tiling.Plane := Subtype.val '' S
  have hSplane : Splane ⊆ C.centres := by
    rintro s ⟨t, ht, rfl⟩
    exact t.2
  obtain ⟨c, hc⟩ := hline
  have hlineplane : ∃ c, ∀ s ∈ Splane, axis.transverseCoord s = c := by
    refine ⟨c, ?_⟩
    rintro s ⟨t, ht, rfl⟩
    exact hc ⟨t, ht⟩
  let Bset := bulkCentres A Splane J
  have hBfinite : Bset.Finite := by
    exact bulkCentres_finite hT hSplane hlineplane A J
  let bulk := hBfinite.toFinset
  have hbulk : (bulk : Set Tiling.Plane) = Bset := by
    ext s
    simp [bulk, Bset]
  let Eset := {s | s ∈ Splane ∧ s ∉ Bset ∧
      ∃ i : Fin A.raw.presentation.n, ∃ x : ℝ,
        x ∈ Set.Ioo
          (A.raw.presentation.left i + axis.coord s - A.origin)
          (A.raw.presentation.right i + axis.coord s - A.origin) ∧
        x ∈ Set.Ioo J.left J.right}
  have hE := nonbulkContributingCenters_finite_card_bound hT A hSplane hlineplane J
  have hEfinite : Eset.Finite := by
    simpa only [Eset, Bset] using hE.1
  let exceptional := hEfinite.toFinset
  have hexceptional : (exceptional : Set Tiling.Plane) = Eset := by
    ext s
    simp [exceptional, Eset]
  have hcard : exceptional.card ≤
      2 * ((C.centres - C.centres) ∩ Metric.closedBall 0
        (4 * Metric.diam C.region.support + 1)).ncard := by
    calc
      exceptional.card = Eset.ncard := by
        symm
        exact Set.ncard_eq_toFinset_card Eset hEfinite
      _ ≤ 2 * ((C.centres - C.centres) ∩ Metric.closedBall 0
          (4 * Metric.diam C.region.support + 1)).ncard := by
        simpa [Eset, Bset] using hE.2
  have hbulk_subset : (bulk : Set Tiling.Plane) ⊆ Splane := by
    intro s hs
    have hsB : s ∈ Bset := by rw [hbulk] at hs; exact hs
    have hsB' := hsB
    simp only [Bset, bulkCentres, Set.mem_ofPred_eq] at hsB'
    exact hsB'.1
  have hexceptional_subset : (exceptional : Set Tiling.Plane) ⊆ Splane := by
    intro s hs
    have hsE : s ∈ Eset := by rw [hexceptional] at hs; exact hs
    exact hsE.1
  have hdisjoint : Disjoint (bulk : Set Tiling.Plane) (exceptional : Set Tiling.Plane) := by
    rw [Set.disjoint_left]
    intro s hsB hsE
    have hsB' : s ∈ Bset := by rw [hbulk] at hsB; exact hsB
    have hsE' : s ∈ Eset := by rw [hexceptional] at hsE; exact hsE
    exact hsE'.2.1 hsB'
  have hUeq : A.carrier + axis.coord '' Splane =
      ⋃ s ∈ Splane, (axis.coord s) +ᵥ A.carrier := by
    ext x
    constructor
    · rintro ⟨a, ha, b, ⟨s, hs, rfl⟩, hab⟩
      refine Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hs, ?_⟩⟩
      apply Set.mem_vadd_set_iff_neg_vadd_mem.mpr
      change -axis.coord s + x ∈ A.carrier
      have hxa : -axis.coord s + x = a := calc
        -axis.coord s + x = -axis.coord s + (a + axis.coord s) := by rw [← hab]
        _ = a := by ring
      rw [hxa]
      exact ha
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨s, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hs, hxs⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hxs
      have hxs' : x - axis.coord s ∈ A.carrier := by
        simpa [sub_eq_add_neg, add_comm] using hxs
      refine ⟨x - axis.coord s, hxs', axis.coord s, ?_, by ring⟩
      exact ⟨s, hs, rfl⟩
  have hsplit :
      (A.carrier + axis.coord '' Splane) ∩ Set.Ioo J.left J.right =
        (⋃ s ∈ bulk, ((axis.coord s) +ᵥ A.carrier) ∩ Set.Ioo J.left J.right) ∪
          (⋃ s ∈ exceptional,
            ((axis.coord s) +ᵥ A.carrier) ∩ Set.Ioo J.left J.right) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxU, hxJ⟩
      rw [hUeq] at hxU
      rcases Set.mem_iUnion.mp hxU with ⟨s, hxU⟩
      rcases Set.mem_iUnion.mp hxU with ⟨hs, hxs⟩
      have hsSectionJ : x ∈ ((axis.coord s) +ᵥ A.carrier) ∩ Set.Ioo J.left J.right :=
        ⟨hxs, hxJ⟩
      by_cases hsB : s ∈ bulk
      · apply Set.mem_union_left
        exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hsB, hsSectionJ⟩⟩
      · have hsBset : s ∉ Bset := by
          intro h
          apply hsB
          have hs' : s ∈ (bulk : Set Tiling.Plane) := by
            rw [hbulk]
            exact h
          exact hs'
        have hsSectionJ0 := hsSectionJ
        have hselector := componentSelectedIntervals_eq_section_inter_component A J hs
        rw [hselector] at hsSectionJ
        rcases Set.mem_iUnion.mp hsSectionJ with ⟨i, hselected⟩
        rcases Set.mem_iUnion.mp hselected with ⟨hi, hxi⟩
        have hsE : s ∈ Eset := by
          refine ⟨hs, hsBset, ?_⟩
          exact ⟨i, x, hxi, hxJ⟩
        have hsExc : s ∈ exceptional := by
          change s ∈ (exceptional : Set Tiling.Plane)
          rw [hexceptional]
          exact hsE
        apply Set.mem_union_right
        exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hsExc, hsSectionJ0⟩⟩
    · intro hx
      rcases hx with hxBulk | hxExc
      · rcases Set.mem_iUnion.mp hxBulk with ⟨s, hxBulk⟩
        rcases Set.mem_iUnion.mp hxBulk with ⟨hs, hxPiece⟩
        have hsSplane : s ∈ Splane := by
          have hsBset : s ∈ Bset := by
            have hs' : s ∈ (bulk : Set Tiling.Plane) := hs
            rw [hbulk] at hs'
            exact hs'
          have hs' := hsBset
          simp only [Bset, bulkCentres, Set.mem_ofPred_eq] at hs'
          exact hs'.1
        have hxU : x ∈ A.carrier + axis.coord '' Splane := by
          rw [hUeq]
          exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hsSplane, hxPiece.1⟩⟩
        exact ⟨hxU, hxPiece.2⟩
      · rcases Set.mem_iUnion.mp hxExc with ⟨s, hxExc⟩
        rcases Set.mem_iUnion.mp hxExc with ⟨hs, hxPiece⟩
        have hsEset : s ∈ Eset := by
          have hs' : s ∈ (exceptional : Set Tiling.Plane) := hs
          rw [hexceptional] at hs'
          exact hs'
        have hsSplane : s ∈ Splane := hsEset.1
        have hxU : x ∈ A.carrier + axis.coord '' Splane := by
          rw [hUeq]
          exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hsSplane, hxPiece.1⟩⟩
        exact ⟨hxU, hxPiece.2⟩
  exact ⟨bulk, exceptional, hbulk, hbulk_subset, hexceptional_subset,
    hdisjoint, hcard, hsplit⟩

private theorem boundedOccupiedTraceComponent_mass_decomposition
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres)
    (axis : Axis) (A : NormalizedGenericSection C axis) (S : Set ↥C.centres)
    (hpacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S)))
    (hline : ∃ c, ∀ s : S, axis.transverseCoord s.1.1 = c) :
    ∀ J : BoundedOccupiedTraceComponent A (Subtype.val '' S),
      ∃ bulk exceptional : Finset Tiling.Plane,
        (bulk : Set Tiling.Plane) = bulkCentres A (Subtype.val '' S) J ∧
        exceptional.card ≤ 2 * ((C.centres - C.centres) ∩ Metric.closedBall 0
          (4 * Metric.diam C.region.support + 1)).ncard ∧
        ∃ selected : Tiling.Plane → Finset (Fin A.raw.presentation.n),
          J.right - J.left = (bulk.card : ℝ) * A.mass +
            ∑ s ∈ exceptional, volume.real
              (⋃ i ∈ selected s,
                Set.Ioo (A.raw.presentation.left i) (A.raw.presentation.right i)) := by
  classical
  intro J
  obtain ⟨bulk, exceptional, hbulk, hbulkS, hexceptionalS, hdisjoint, hcard, hsplit⟩ :=
    boundedOccupiedTraceComponent_finite_section_split hT axis A S hpacking hline J
  let selected := fun s : Tiling.Plane => componentSelectedIntervals A J s
  let piece := fun s : Tiling.Plane =>
    ((axis.coord s) +ᵥ A.carrier) ∩ Set.Ioo J.left J.right
  let Q := bulk ∪ exceptional
  have hQS : (Q : Set Tiling.Plane) ⊆ Subtype.val '' S := by
    intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact hbulkS hs
    · exact hexceptionalS hs
  have hlinePlane : ∃ c, ∀ s ∈ Subtype.val '' S, axis.transverseCoord s = c := by
    obtain ⟨c, hc⟩ := hline
    refine ⟨c, ?_⟩
    rintro s ⟨t, ht, rfl⟩
    exact hc ⟨t, ht⟩
  have hpackingSections := normalizedSection_translates_pairwiseDisjoint A hpacking hlinePlane
  have hpair : Set.PairwiseDisjoint (Q : Set Tiling.Plane) piece := by
    intro s hs t ht hst
    exact (hpackingSections (hQS hs) (hQS ht) hst).mono Set.inter_subset_left
      Set.inter_subset_left
  have hAopen : IsOpen A.carrier := by
    rw [A.carrier_eq]
    exact (Homeomorph.vadd (-A.origin)).isOpenMap _ A.raw.presentation.isOpen
  have hmeas (s : Tiling.Plane) : MeasurableSet (piece s) := by
    exact ((Homeomorph.vadd (axis.coord s)).isOpenMap _ hAopen).measurableSet.inter
      measurableSet_Ioo
  have hfinite (s : Tiling.Plane) : volume (piece s) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_right
      (Metric.isBounded_Ioo J.left J.right).measure_lt_top.ne
  have hunion : (A.carrier + axis.coord '' (Subtype.val '' S)) ∩
      Set.Ioo J.left J.right = ⋃ s ∈ Q, piece s := by
    simpa only [Q, piece, Finset.mem_union, Set.iUnion_or,
      Set.iUnion_union_distrib] using hsplit
  have hsum : J.right - J.left = ∑ s ∈ Q, volume.real (piece s) := by
    rw [← boundedOccupiedTraceComponent_raw_mass hT axis A S hline J, hunion]
    exact MeasureTheory.measureReal_biUnion_finset hpair (fun s _ => hmeas s)
      (fun s _ => hfinite s)
  have hbulkValue (s : Tiling.Plane) (hs : s ∈ bulk) : volume.real (piece s) = A.mass := by
    have hsbulk : s ∈ bulkCentres A (Subtype.val '' S) J := hbulk ▸ hs
    have hpiece : piece s = (axis.coord s) +ᵥ A.carrier :=
      Set.inter_eq_left.mpr (bulkCenter_section_subset_component A J hsbulk)
    rw [hpiece, MeasureTheory.measureReal_def, MeasureTheory.measure_vadd,
      ← MeasureTheory.measureReal_def, ← A.mass_eq]
  have hexceptionalValue (s : Tiling.Plane) (hs : s ∈ exceptional) :
      volume.real (piece s) = volume.real
        (⋃ i ∈ selected s, Set.Ioo (A.raw.presentation.left i) (A.raw.presentation.right i)) := by
    have hpiece : piece s = (axis.coord s - A.origin) +ᵥ
        (⋃ i ∈ selected s,
          Set.Ioo (A.raw.presentation.left i) (A.raw.presentation.right i)) := by
      dsimp only [piece]
      rw [componentSelectedIntervals_eq_section_inter_component A J (hexceptionalS hs)]
      ext x
      simp only [Set.mem_iUnion, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        Set.mem_Ioo]
      constructor
      · rintro ⟨i, hi, hl, hr⟩
        exact ⟨i, hi, by constructor <;> linarith⟩
      · rintro ⟨i, hi, hl, hr⟩
        exact ⟨i, hi, by constructor <;> linarith⟩
    rw [hpiece, MeasureTheory.measureReal_def, MeasureTheory.measure_vadd,
      ← MeasureTheory.measureReal_def]
  refine ⟨bulk, exceptional, hbulk, hcard, selected, ?_⟩
  have hdisjointFinset : Disjoint bulk exceptional := by
    simpa only [Finset.disjoint_coe] using hdisjoint
  rw [hsum, Finset.sum_union hdisjointFinset]
  congr 1
  · calc
      ∑ s ∈ bulk, volume.real (piece s) = ∑ _s ∈ bulk, A.mass :=
        Finset.sum_congr rfl (fun s hs => hbulkValue s hs)
      _ = (bulk.card : ℝ) * A.mass := by simp
  · exact Finset.sum_congr rfl (fun s hs => hexceptionalValue s hs)

private theorem componentCorrections_finite :
    ∀ {C : ApproximationContext.{0}}, HasFLC C.centres →
      ∀ (axis : Axis) (A : NormalizedGenericSection C axis),
      ∃ R > 0, ∃ massExpression : FiniteCombinationData C R,
        massExpression.value = A.massScalar ∧
      ∃ corrections : Finset (FiniteCombinationData C R),
        ∀ {S : Set Tiling.Plane}, S ⊆ C.centres →
          Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
            (C.region.toPolygonalRegion.placements S) →
          (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) →
          ∀ J : BoundedOccupiedTraceComponent A S,
            ∃ code : ComponentMassCode A S J R, code.correction ∈ corrections := by
  classical
  intro C hT axis A
  obtain ⟨R, hR, atom, hfamily⟩ := normalized_subfamilyMassExpressions_exists A
  obtain ⟨massCoeff, _hmassCoeff, hmassValue⟩ := hfamily Finset.univ
  let massExpression := finiteCombinationOfFamily atom massCoeff
  have hmass : massExpression.value = A.massScalar := by
    apply Subtype.ext
    have hm : (massExpression.value : ℝ) = A.mass := by
      rw [A.mass_eq, A.carrier_eq, MeasureTheory.measureReal_def,
        MeasureTheory.measure_vadd, ← MeasureTheory.measureReal_def]
      rw [congrArg volume.real A.raw.presentation.union_eq]
      simpa only [Finset.mem_univ, iUnion_true] using hmassValue
    exact hm.trans A.massScalar_coe.symm
  let M := 2 * ((C.centres - C.centres) ∩
    Metric.closedBall 0 (4 * Metric.diam C.region.support + 1)).ncard
  obtain ⟨corrections, hcorrections⟩ := boundedCombinationFamily_finite atom M
  refine ⟨R, hR, massExpression, hmass, corrections, ?_⟩
  intro S hS hpacking hline J
  let Sidx : Set ↥C.centres := {s | s.1 ∈ S}
  have hSidx : Subtype.val '' Sidx = S := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hs
      exact ⟨⟨s, hS hs⟩, hs, rfl⟩
  have hlineIdx : ∃ c, ∀ s : Sidx, axis.transverseCoord s.1.1 = c := by
    obtain ⟨c, hc⟩ := hline
    exact ⟨c, fun s => hc s.1.1 s.2⟩
  have hpackingIdx : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' Sidx)) := by
    rw [hSidx]
    exact hpacking
  have hdecomposition := boundedOccupiedTraceComponent_mass_decomposition
    hT axis A Sidx hpackingIdx hlineIdx
  rw [hSidx] at hdecomposition
  obtain ⟨bulk, exceptional, hbulk, hcard, selected, hlength⟩ := hdecomposition J
  choose coeff hcoeff hvalue using fun s : Tiling.Plane => hfamily (selected s)
  let correction := finiteCombinationOfFamily atom (fun u => ∑ s ∈ exceptional, coeff s u)
  have hcorrectionValue : (correction.value : ℝ) =
      ∑ s ∈ exceptional, volume.real
        (⋃ i ∈ selected s, Set.Ioo (A.raw.presentation.left i) (A.raw.presentation.right i)) := by
    dsimp only [correction]
    rw [finiteCombinationOfFamily_value_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl (fun s _ => hvalue s)
  have hnonneg : 0 ≤ (correction.value : ℝ) := by
    rw [hcorrectionValue]
    exact Finset.sum_nonneg (fun s _ => MeasureTheory.measureReal_nonneg)
  let code : ComponentMassCode A S J R := {
    bulk := bulk
    bulk_coe := hbulk
    correction := correction
    correction_nonneg := hnonneg
    length_eq := by rw [hcorrectionValue]; exact hlength }
  refine ⟨code, ?_⟩
  exact hcorrections _ (finiteCombinationOfFamily_sum_coeff_bound exceptional coeff M
    hcard (fun s _ u => hcoeff s u))

private theorem allEndpointWeakOrderTransport_construct
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (A : NormalizedGenericSection C axis)
    (S : Set ↥C.centres) (G delta : ℝ) (N : ℕ)
    (hδ : 0 < delta) (hLinked : Linked G (Subtype.val '' S))
    (hpacking : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements
        (deformedCenterCarrierOn Tphi S)))
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → delta ≤ dist s.1.1 t.1.1)
    (hline : ∃ c, ∀ s : S, axis.transverseCoord s.1.1 = c)
    (hlineT : ∃ c, ∀ s : S, axis.transverseCoord (Tphi s.1) = c)
    (hNδ : (N : ℝ) * delta > 4 * Metric.diam C.region.support)
    (hNG : (N : ℝ) * G + 2 * Metric.diam C.region.support < P.scale)
    (_hError : P.localError < delta / 2)
    (hdscale : Metric.diam C.region.support < P.scale)
    (_hErrorD : P.localError ≤ Metric.diam C.region.support) :
    Nonempty (AllEndpointWeakOrderTransport phi D Tphi axis S A) := by
  have hPlane : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      delta ≤ dist (s : Tiling.Plane) (t : Tiling.Plane) := by
    intro s hs t ht hne
    have hreal := hsep s hs t ht hne
    have hcoord := sourceGeometry_coord_abs_le Axis.horizontal
      (s : Tiling.Plane) (t : Tiling.Plane)
    exact (show delta ≤ |(s : Tiling.Plane).re - (t : Tiling.Plane).re| by
      simpa only [Real.dist_eq] using hreal).trans hcoord
  exact (endpointPlaneSeparation_control P hLinked hPlane hline hδ hNδ hNG
    rfl hdscale).2 phi hphi D Tphi hTphi hpacking hlineT _hError _hErrorD

private theorem boundedComponent_targetInterval_subset
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S)) :
    ∃ e f : IndexedSectionEndpoint A S,
      e.sourceValue = J.left ∧ f.sourceValue = J.right ∧
      Set.Ioo (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e)
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f) ⊆
        interior (closure (⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
          Set.Ioo
            (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
              (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
            (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
              (IndexedSectionEndpoint.mk ⟨i, true⟩ s)))) := by
  let sourceTrace := interior (closure (A.carrier + axis.coord '' (Subtype.val '' S)))
  let sourceIntervals := ⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
    Set.Ioo
      ((IndexedSectionEndpoint.mk ⟨i, false⟩ s).sourceValue)
      ((IndexedSectionEndpoint.mk ⟨i, true⟩ s).sourceValue)
  let targetIntervals := ⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
    Set.Ioo
      (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
        (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
      (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
        (IndexedSectionEndpoint.mk ⟨i, true⟩ s))
  have hsourceTrace : sourceTrace = interior (closure sourceIntervals) := E.source_union_eq
  have hSourceOpen : IsOpen sourceTrace := isOpen_interior
  have hEnds := boundedIntervalComponent_endpoints_frontier hSourceOpen J.ordered J.component_eq
  obtain ⟨e, he⟩ := E.source_frontier_subset hEnds.1
  obtain ⟨f, hf⟩ := E.source_frontier_subset hEnds.2
  obtain ⟨h, hmono, hwindow⟩ := endpointFiniteWindow_homeomorph E J.left J.right
  have hleftMap : h J.left = IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e := by
    calc
      h J.left = h e.sourceValue := congrArg h he.symm
      _ = IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e := by
        apply hwindow e
        · rw [he]
        · rw [he]
          exact J.ordered.le
  have hrightMap : h J.right = IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f := by
    calc
      h J.right = h f.sourceValue := congrArg h hf.symm
      _ = IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f := by
        apply hwindow f
        · rw [hf]
          exact J.ordered.le
        · rw [hf]
  have hIooSource : Set.Ioo J.left J.right ⊆ sourceTrace := by
    intro x hx
    have hxcomp : x ∈ connectedComponentIn sourceTrace ((J.left + J.right) / 2) := by
      rw [J.component_eq]
      exact hx
    exact connectedComponentIn_subset sourceTrace _ hxcomp
  have hSourceClosure : Set.Ioo J.left J.right ⊆ closure sourceIntervals := by
    rw [hsourceTrace] at hIooSource
    exact hIooSource.trans interior_subset
  let localSourceIntervals := sourceIntervals ∩ Set.Ioo J.left J.right
  have hlocalDense : Set.Ioo J.left J.right ⊆ closure localSourceIntervals := by
    intro x hx
    rw [mem_closure_iff]
    intro V hVopen hxV
    have hOVopen : IsOpen (V ∩ Set.Ioo J.left J.right) := hVopen.inter isOpen_Ioo
    have hxOV : x ∈ V ∩ Set.Ioo J.left J.right := ⟨hxV, hx⟩
    obtain ⟨y, hyOV, hyU⟩ := (mem_closure_iff.mp (hSourceClosure hx))
      (V ∩ Set.Ioo J.left J.right) hOVopen hxOV
    exact ⟨y, hyOV.1, ⟨hyU, hyOV.2⟩⟩
  have hlocalReg : Set.Ioo J.left J.right ⊆ interior (closure localSourceIntervals) :=
    interior_maximal hlocalDense isOpen_Ioo
  have hRawImage : h '' localSourceIntervals ⊆ targetIntervals := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases (show x ∈ sourceIntervals from hx.1) with hxIntervals
    have hxIntervals' : ∃ i : Fin A.raw.presentation.n, ∃ s : S,
        x ∈ Set.Ioo
          ((IndexedSectionEndpoint.mk ⟨i, false⟩ s).sourceValue)
          ((IndexedSectionEndpoint.mk ⟨i, true⟩ s).sourceValue) := by
      simpa [sourceIntervals] using hxIntervals
    rcases hxIntervals' with ⟨i, s, hxi⟩
    let e₀ : IndexedSectionEndpoint A S := IndexedSectionEndpoint.mk ⟨i, false⟩ s
    let e₁ : IndexedSectionEndpoint A S := IndexedSectionEndpoint.mk ⟨i, true⟩ s
    have hmeet : (Set.Ioo
        (A.raw.presentation.left i + axis.coord s.1.1 - A.origin)
        (A.raw.presentation.right i + axis.coord s.1.1 - A.origin) ∩
          Set.Ioo J.left J.right).Nonempty := by
      refine ⟨x, ?_, hx.2⟩
      simpa [e₀, e₁, IndexedSectionEndpoint.sourceValue,
        SectionEndpointLabel.rawValue] using hxi
    have hintervalSubset := occupiedComponent_interval_subset A J
      (show s.1.1 ∈ Subtype.val '' S from ⟨s.1, s.2, rfl⟩) i hmeet
    have hlt : e₀.sourceValue < e₁.sourceValue := by
      simpa [e₀, e₁, IndexedSectionEndpoint.sourceValue,
        SectionEndpointLabel.rawValue] using A.raw.presentation.lt i
    have hintervalSubset' : Set.Ioo e₀.sourceValue e₁.sourceValue ⊆
        Set.Ioo J.left J.right := by
      simpa [e₀, e₁, IndexedSectionEndpoint.sourceValue,
        SectionEndpointLabel.rawValue] using hintervalSubset
    have hclosedSubset : Set.Icc e₀.sourceValue e₁.sourceValue ⊆
        Set.Icc J.left J.right := by
      rw [← closure_Ioo (ne_of_lt hlt), ← closure_Ioo (ne_of_lt J.ordered)]
      exact closure_mono hintervalSubset'
    have he₀range : e₀.sourceValue ∈ Set.Icc J.left J.right :=
      hclosedSubset ⟨le_rfl, hlt.le⟩
    have he₁range : e₁.sourceValue ∈ Set.Icc J.left J.right :=
      hclosedSubset ⟨hlt.le, le_rfl⟩
    have h₀ : h e₀.sourceValue =
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₀ :=
      hwindow e₀ he₀range.1 he₀range.2
    have h₁ : h e₁.sourceValue =
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₁ :=
      hwindow e₁ he₁range.1 he₁range.2
    have hxi' : x ∈ Set.Ioo e₀.sourceValue e₁.sourceValue := by
      simpa [e₀, e₁] using hxi
    have hyTarget : h x ∈ Set.Ioo
        (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₀)
        (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₁) := by
      rw [← h₀, ← h₁]
      exact ⟨hmono hxi'.1, hmono hxi'.2⟩
    change h x ∈ targetIntervals
    simp only [targetIntervals, Set.mem_iUnion]
    exact ⟨i, s, hyTarget⟩
  have hImageReg : h '' interior (closure localSourceIntervals) =
      interior (closure (h '' localSourceIntervals)) := by
    rw [h.image_interior, h.image_closure]
  have hImageSubset : h '' Set.Ioo J.left J.right ⊆
      interior (closure targetIntervals) := by
    calc
      h '' Set.Ioo J.left J.right ⊆ h '' interior (closure localSourceIntervals) :=
        image_mono hlocalReg
      _ = interior (closure (h '' localSourceIntervals)) := hImageReg
      _ ⊆ interior (closure targetIntervals) :=
        interior_mono (closure_mono hRawImage)
  refine ⟨e, f, he, hf, ?_⟩
  intro y hy
  let x := h.symm y
  have hxy : h x = y := h.apply_symm_apply y
  have hxleft : J.left < x := by
    apply hmono.lt_iff_lt.mp
    simpa [hxy, hleftMap] using hy.1
  have hxright : x < J.right := by
    apply hmono.lt_iff_lt.mp
    simpa [hxy, hrightMap] using hy.2
  have hmem : h x ∈ h '' Set.Ioo J.left J.right := ⟨x, ⟨hxleft, hxright⟩, rfl⟩
  rw [← hxy]
  simpa [targetIntervals] using hImageSubset hmem

private theorem boundedComponent_noTargetInterval_cross_left
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S))
    (e : IndexedSectionEndpoint A S) (he : e.sourceValue = J.left)
    (i : Fin A.raw.presentation.n) (s : S) :
    ¬ (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, false⟩ s) <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ∧
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) := by
  intro hcross
  let e₀ : IndexedSectionEndpoint A S := IndexedSectionEndpoint.mk ⟨i, false⟩ s
  let e₁ : IndexedSectionEndpoint A S := IndexedSectionEndpoint.mk ⟨i, true⟩ s
  have hcross' :
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₀ <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ∧
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₁ := by
    simpa [e₀, e₁] using hcross
  have hsourceLeft : e₀.sourceValue < J.left := by
    rw [← he]
    exact (allEndpointWeakOrderTransport_endpoint_lt_iff E e₀ e).mpr hcross'.1
  have hsourceRight : J.left < e₁.sourceValue := by
    rw [← he]
    exact (allEndpointWeakOrderTransport_endpoint_lt_iff E e e₁).mpr hcross'.2
  have hmeet : (Set.Ioo
      (A.raw.presentation.left i + axis.coord s.1.1 - A.origin)
      (A.raw.presentation.right i + axis.coord s.1.1 - A.origin) ∩
        Set.Ioo J.left J.right).Nonempty := by
    have hupper : J.left < min e₁.sourceValue J.right := lt_min hsourceRight J.ordered
    obtain ⟨x, hleft, hright⟩ := exists_between hupper
    refine ⟨x, ⟨?_, ?_⟩, ⟨hleft, ?_⟩⟩
    · simpa [e₀, IndexedSectionEndpoint.sourceValue,
        SectionEndpointLabel.rawValue] using hsourceLeft.trans hleft
    · simpa [e₁, IndexedSectionEndpoint.sourceValue,
        SectionEndpointLabel.rawValue] using
          (lt_of_lt_of_le hright (min_le_left _ _))
    · exact lt_of_lt_of_le hright (min_le_right _ _)
  have hsubset := occupiedComponent_interval_subset A J
    (show s.1.1 ∈ Subtype.val '' S from ⟨s.1, s.2, rfl⟩) i hmeet
  have hlt : e₀.sourceValue < e₁.sourceValue := by
    simpa [e₀, e₁, IndexedSectionEndpoint.sourceValue,
      SectionEndpointLabel.rawValue] using A.raw.presentation.lt i
  have hsubset' : Set.Ioo e₀.sourceValue e₁.sourceValue ⊆ Set.Ioo J.left J.right := by
    simpa [e₀, e₁, IndexedSectionEndpoint.sourceValue,
      SectionEndpointLabel.rawValue] using hsubset
  have hclosed : Set.Icc e₀.sourceValue e₁.sourceValue ⊆ Set.Icc J.left J.right := by
    rw [← closure_Ioo (ne_of_lt hlt), ← closure_Ioo (ne_of_lt J.ordered)]
    exact closure_mono hsubset'
  have hleftmem : e₀.sourceValue ∈ Set.Icc J.left J.right :=
    hclosed ⟨le_rfl, hlt.le⟩
  exact (not_lt_of_ge hleftmem.1) hsourceLeft

private theorem boundedComponent_noTargetExteriorInterval_end_left
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S))
    (e : IndexedSectionEndpoint A S) (he : e.sourceValue = J.left)
    (i : Fin A.raw.presentation.n) (s : S) :
    ¬ (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, false⟩ s) <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ∧
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, true⟩ s) =
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e) := by
  intro hexterior
  let e₀ : IndexedSectionEndpoint A S := IndexedSectionEndpoint.mk ⟨i, false⟩ s
  let e₁ : IndexedSectionEndpoint A S := IndexedSectionEndpoint.mk ⟨i, true⟩ s
  have hexterior' :
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₀ <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ∧
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₁ =
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e := by
    simpa [e₀, e₁] using hexterior
  have hsourceLeft : e₀.sourceValue < J.left := by
    rw [← he]
    exact (allEndpointWeakOrderTransport_endpoint_lt_iff E e₀ e).mpr hexterior'.1
  have hsourceRight : e₁.sourceValue = J.left := by
    rw [← he]
    exact (allEndpointWeakOrderTransport_endpoint_eq_iff E e₁ e).mpr hexterior'.2
  let sourceTrace := interior (closure (A.carrier + axis.coord '' (Subtype.val '' S)))
  let sourceIntervals := ⋃ j : Fin A.raw.presentation.n, ⋃ t : S,
    Set.Ioo
      ((IndexedSectionEndpoint.mk ⟨j, false⟩ t).sourceValue)
      ((IndexedSectionEndpoint.mk ⟨j, true⟩ t).sourceValue)
  have hsourceTrace : sourceTrace = interior (closure sourceIntervals) := E.source_union_eq
  have hleftSourceOpen : IsOpen sourceTrace := isOpen_interior
  have hleftFrontier : J.left ∈ frontier sourceTrace := by
    have hEnds := boundedIntervalComponent_endpoints_frontier hleftSourceOpen
      J.ordered J.component_eq
    exact hEnds.1
  have hsourceLt : e₀.sourceValue < e₁.sourceValue := by
    simpa [e₀, e₁, IndexedSectionEndpoint.sourceValue,
      SectionEndpointLabel.rawValue] using A.raw.presentation.lt i
  have hrawSubset : Set.Ioo e₀.sourceValue e₁.sourceValue ⊆ sourceIntervals := by
    intro x hx
    simp only [sourceIntervals, Set.mem_iUnion]
    exact ⟨i, s, by simpa [e₀, e₁] using hx⟩
  have hclosedSubset : Set.Icc e₀.sourceValue e₁.sourceValue ⊆ closure sourceIntervals := by
    rw [← closure_Ioo (ne_of_lt hsourceLt)]
    exact closure_mono hrawSubset
  have hIooSource : Set.Ioo J.left J.right ⊆ sourceTrace := by
    intro x hx
    have hxcomp : x ∈ connectedComponentIn sourceTrace ((J.left + J.right) / 2) := by
      rw [J.component_eq]
      exact hx
    exact connectedComponentIn_subset sourceTrace _ hxcomp
  have hmidLeft : J.left < (J.left + J.right) / 2 := by linarith [J.ordered]
  have hmidRight : (J.left + J.right) / 2 < J.right := by linarith [J.ordered]
  have hnear : Set.Ioo e₀.sourceValue ((J.left + J.right) / 2) ⊆
      closure sourceIntervals := by
    intro x hx
    by_cases hxa : x ≤ J.left
    · exact hclosedSubset ⟨hx.1.le, by simpa [hsourceRight] using hxa⟩
    · have hxJ : x ∈ Set.Ioo J.left J.right := ⟨lt_of_not_ge hxa, lt_trans hx.2 hmidRight⟩
      have hxtrace := hIooSource hxJ
      rw [hsourceTrace] at hxtrace
      exact interior_subset hxtrace
  have hleftInterior : J.left ∈ interior (closure sourceIntervals) := by
    apply interior_maximal hnear isOpen_Ioo
    constructor
    · exact hsourceLeft
    · exact hmidLeft
  have hleftInTrace : J.left ∈ sourceTrace := by
    rw [hsourceTrace]
    exact hleftInterior
  have hleftNotInterior : J.left ∉ interior sourceTrace :=
    (mem_frontier_iff_notMem_interior hleftInTrace).mp hleftFrontier
  have hleftOpenInterior : J.left ∈ interior sourceTrace := by
    rw [hleftSourceOpen.interior_eq]
    exact hleftInTrace
  exact hleftNotInterior hleftOpenInterior

private theorem locallyFinite_interval_endpoint_not_interior
    {ι : Type*} (l r : ι → ℝ) (a : ℝ)
    (hfinite : ∀ b c : ℝ,
      ({x : ℝ | ∃ i, x = l i ∨ x = r i} ∩ Set.Icc b c).Finite)
    (hcross : ∀ i, l i < a → a < r i → False)
    (hend : ∀ i, l i < a → r i = a → False) :
    a ∉ interior (closure (⋃ i, Set.Ioo (l i) (r i))) := by
  intro haInterior
  let E : Set ℝ := {x : ℝ | ∃ i, x = l i ∨ x = r i}
  let F : Set ℝ := E ∩ Set.Icc (a - 1) (a + 1)
  let G : Set ℝ := F \ {a}
  have hFfinite : F.Finite := hfinite (a - 1) (a + 1)
  have hGfinite : G.Finite := hFfinite.sdiff
  have haG : a ∉ G := by simp [G]
  have hGclosed : IsClosed G := hGfinite.isClosed
  have hGcomplNhds : Gᶜ ∈ 𝓝 a := hGclosed.isOpen_compl.mem_nhds haG
  have hInteriorNhds : interior (closure (⋃ i, Set.Ioo (l i) (r i))) ∈ 𝓝 a :=
    isOpen_interior.mem_nhds haInterior
  have hBothNhds :
      (interior (closure (⋃ i, Set.Ioo (l i) (r i))) ∩ Gᶜ) ∈ 𝓝 a :=
    inter_mem hInteriorNhds hGcomplNhds
  obtain ⟨p, q, hapq, hGpq⟩ :=
    (mem_nhds_iff_exists_Ioo_subset (a := a)
      (s := interior (closure (⋃ i, Set.Ioo (l i) (r i))) ∩ Gᶜ)).mp hBothNhds
  have hlower : max p (a - 1) < a := by
    rw [max_lt_iff]
    exact ⟨hapq.1, by linarith⟩
  obtain ⟨x, hxa, hax⟩ := exists_between hlower
  have hxIoo : x ∈ Set.Ioo p q := by
    constructor
    · exact lt_of_le_of_lt (le_max_left _ _) hxa
    · exact lt_trans hax hapq.2
  have hax1 : a - 1 < x := lt_of_le_of_lt (le_max_right _ _) hxa
  have hxInterior : x ∈ interior (closure (⋃ i, Set.Ioo (l i) (r i))) :=
    (hGpq hxIoo).1
  have hxIcc : x ∈ Set.Icc (a - 1) (a + 1) := by constructor <;> linarith
  have hxnotE : x ∉ E := by
    intro hxE
    have hxF : x ∈ F := ⟨hxE, hxIcc⟩
    have hxG : x ∈ G := by
      simp only [G, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨hxF, ne_of_lt hax⟩
    exact (hGpq hxIoo).2 hxG
  have hxclosure : x ∈ closure (⋃ i, Set.Ioo (l i) (r i)) := interior_subset hxInterior
  have hxU : x ∈ ⋃ i, Set.Ioo (l i) (r i) := by
    by_contra hxnotU
    exact hxnotE (closure_interval_union_diff_subset_endpoints l r hfinite
      ⟨hxclosure, hxnotU⟩)
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxU
  have hleft : l i < x := hxi.1
  have hleftA : l i < a := lt_trans hleft hax
  rcases lt_trichotomy (r i) a with hright | hright | hright
  · have hrIoo : r i ∈ Set.Ioo p q := by
      exact ⟨lt_trans hxIoo.1 hxi.2, lt_trans hright hapq.2⟩
    have hrIcc : r i ∈ Set.Icc (a - 1) (a + 1) := by
      exact ⟨(lt_trans hax1 hxi.2).le, hright.le.trans (by linarith)⟩
    have hrG : r i ∈ G := by
      simp only [G, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨⟨⟨i, Or.inr rfl⟩, hrIcc⟩, ne_of_lt hright⟩
    exact (hGpq hrIoo).2 hrG
  · exact hend i hleftA hright
  · exact hcross i hleftA hright

private theorem boundedComponent_targetLeft_not_interior
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S))
    (e : IndexedSectionEndpoint A S) (he : e.sourceValue = J.left) :
    IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ∉
      interior (closure (⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
        Set.Ioo
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, true⟩ s)))) := by
  let P := Fin A.raw.presentation.n × S
  let l : P → ℝ := fun p => IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
    (IndexedSectionEndpoint.mk ⟨p.1, false⟩ p.2)
  let r : P → ℝ := fun p => IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
    (IndexedSectionEndpoint.mk ⟨p.1, true⟩ p.2)
  have hfinite : ∀ a b : ℝ,
      ({x : ℝ | ∃ p, x = l p ∨ x = r p} ∩ Set.Icc a b).Finite := by
    intro a b
    apply (E.targetValues_locallyFinite a b).subset
    intro x hx
    rcases hx with ⟨hxE, hxIcc⟩
    rcases hxE with ⟨⟨i, s⟩, hx | hx⟩
    · refine ⟨⟨IndexedSectionEndpoint.mk ⟨i, false⟩ s, hx.symm⟩, hxIcc⟩
    · refine ⟨⟨IndexedSectionEndpoint.mk ⟨i, true⟩ s, hx.symm⟩, hxIcc⟩
  have hcross : ∀ p, l p < IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e →
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e < r p → False := by
    intro p hl hr
    rcases p with ⟨i, s⟩
    exact boundedComponent_noTargetInterval_cross_left E J e he i s
      (by simpa [l, r] using And.intro hl hr)
  have hend : ∀ p, l p < IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e →
      r p = IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e → False := by
    intro p hl hr
    rcases p with ⟨i, s⟩
    exact boundedComponent_noTargetExteriorInterval_end_left E J e he i s
      (by simpa [l, r] using And.intro hl hr)
  have hnot := locallyFinite_interval_endpoint_not_interior l r
    (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e)
    hfinite hcross hend
  have hunion : (⋃ p : P, Set.Ioo (l p) (r p)) =
      ⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
        Set.Ioo
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) := by
    ext x
    simp [P, l, r]
  have hnot' : IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ∉
      interior (closure (⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
        Set.Ioo
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, true⟩ s)))) := by
    rw [← hunion]
    exact hnot
  exact hnot'

private theorem locallyOrderedWindow_comparison
    {ι : Type*} (v w : ι → ℝ)
    (horder : ∀ i j, v i ≤ v j ↔ w i ≤ w j)
    (e f : ι) (h : ℝ ≃ₜ ℝ) (hmono : StrictMono h)
    (hwindow : ∀ g, v e ≤ v g → v g ≤ v f → h (v g) = w g)
    {x : ℝ} (hx : x ∈ Set.Ioo (v e) (v f)) (g : ι) :
    (v g < x ↔ w g < h x) ∧ (x < v g ↔ h x < w g) := by
  have hstrict : ∀ i j, v i < v j ↔ w i < w j := by
    intro i j
    simpa only [not_le] using not_congr (horder j i)
  have hef : v e < v f := hx.1.trans hx.2
  have heMap : h (v e) = w e := hwindow e le_rfl hef.le
  have hfMap : h (v f) = w f := hwindow f hef.le le_rfl
  by_cases hge : v g < v e
  · have hsource : v g < x := hge.trans hx.1
    have htarget : w g < h x := by
      calc
        w g < w e := (hstrict g e).mp hge
        _ = h (v e) := heMap.symm
        _ < h x := hmono hx.1
    exact ⟨⟨fun _ => htarget, fun _ => hsource⟩,
      ⟨fun hbad => (not_lt_of_ge hsource.le hbad).elim,
        fun hbad => (not_lt_of_ge htarget.le hbad).elim⟩⟩
  by_cases hfg : v f < v g
  · have hsource : x < v g := hx.2.trans hfg
    have htarget : h x < w g := by
      calc
        h x < h (v f) := hmono hx.2
        _ = w f := hfMap
        _ < w g := (hstrict f g).mp hfg
    exact ⟨⟨fun hbad => (not_lt_of_ge hsource.le hbad).elim,
        fun hbad => (not_lt_of_ge htarget.le hbad).elim⟩,
      ⟨fun _ => htarget, fun _ => hsource⟩⟩
  have hgMap : h (v g) = w g :=
    hwindow g (le_of_not_gt hge) (le_of_not_gt hfg)
  rw [← hgMap]
  exact ⟨hmono.lt_iff_lt.symm, hmono.lt_iff_lt.symm⟩

private theorem regularized_mem_iff_regularized_inter_open
    {s W : Set ℝ} (hW : IsOpen W) {x : ℝ} (hx : x ∈ W) :
    x ∈ interior (closure s) ↔ x ∈ interior (closure (s ∩ W)) := by
  constructor
  · intro hxs
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset
      (inter_mem (mem_interior_iff_mem_nhds.mp hxs) (hW.mem_nhds hx))
    intro y hy
    exact hW.closure_inter hy
  · intro hxs
    exact interior_mono
      (closure_mono (Set.inter_subset_left : s ∩ W ⊆ s)) hxs

private theorem locallyOrderedWindow_regularizedIntervals_iff
    {ι κ : Type*} (v w : ι → ℝ) (left right : κ → ι)
    (horder : ∀ i j, v i ≤ v j ↔ w i ≤ w j)
    (e f : ι) (h : ℝ ≃ₜ ℝ) (hmono : StrictMono h)
    (hwindow : ∀ g, v e ≤ v g → v g ≤ v f → h (v g) = w g)
    {x : ℝ} (hx : x ∈ Set.Ioo (v e) (v f)) :
    x ∈ interior (closure (⋃ i, Set.Ioo (v (left i)) (v (right i)))) ↔
      h x ∈ interior (closure (⋃ i, Set.Ioo (w (left i)) (w (right i)))) := by
  let U := ⋃ i, Set.Ioo (v (left i)) (v (right i))
  let V := ⋃ i, Set.Ioo (w (left i)) (w (right i))
  let W := Set.Ioo (v e) (v f)
  have hraw : ∀ y ∈ W, y ∈ U ↔ h y ∈ V := by
    intro y hy
    simp only [U, V, Set.mem_iUnion, Set.mem_Ioo]
    constructor
    · rintro ⟨i, hli, hri⟩
      exact ⟨i,
        (locallyOrderedWindow_comparison v w horder e f h hmono hwindow hy (left i)).1.mp hli,
        (locallyOrderedWindow_comparison v w horder e f h hmono hwindow hy (right i)).2.mp hri⟩
    · rintro ⟨i, hli, hri⟩
      exact ⟨i,
        (locallyOrderedWindow_comparison v w horder e f h hmono hwindow hy (left i)).1.mpr hli,
        (locallyOrderedWindow_comparison v w horder e f h hmono hwindow hy (right i)).2.mpr hri⟩
  have hlocal : U ∩ W = (h ⁻¹' V) ∩ W := by
    ext y
    constructor
    · intro hy
      exact ⟨(hraw y hy.2).mp hy.1, hy.2⟩
    · intro hy
      exact ⟨(hraw y hy.2).mpr hy.1, hy.2⟩
  have hpreimage : h ⁻¹' interior (closure V) =
      interior (closure (h ⁻¹' V)) := by
    rw [h.preimage_interior, h.preimage_closure]
  change x ∈ interior (closure U) ↔ h x ∈ interior (closure V)
  change x ∈ interior (closure U) ↔ x ∈ h ⁻¹' interior (closure V)
  rw [hpreimage]
  calc
    x ∈ interior (closure U) ↔ x ∈ interior (closure (U ∩ W)) :=
      regularized_mem_iff_regularized_inter_open isOpen_Ioo hx
    _ ↔ x ∈ interior (closure ((h ⁻¹' V) ∩ W)) := by rw [hlocal]
    _ ↔ x ∈ interior (closure (h ⁻¹' V)) :=
      (regularized_mem_iff_regularized_inter_open isOpen_Ioo hx).symm

private theorem real_component_eq_iff_uIcc_subset
    {U : Set ℝ} {x z : ℝ} (hx : x ∈ U) (hz : z ∈ U) :
    connectedComponentIn U x = connectedComponentIn U z ↔ Set.uIcc x z ⊆ U := by
  constructor
  · intro hsame
    have hzcomp : z ∈ connectedComponentIn U x := by
      rw [hsame]
      exact mem_connectedComponentIn hz
    exact (isPreconnected_connectedComponentIn.ordConnected.uIcc_subset
      (mem_connectedComponentIn hx) hzcomp).trans (connectedComponentIn_subset U x)
  · intro hsegment
    exact connectedComponentIn_eq
      ((isPreconnected_uIcc.subset_connectedComponentIn Set.left_mem_uIcc hsegment)
        Set.right_mem_uIcc)

private theorem increasing_localTrace_component_eq_iff
    (U V : Set ℝ) (a b : ℝ) (h : ℝ ≃ₜ ℝ) (hmono : StrictMono h)
    (hlocal : ∀ y ∈ Set.Ioo a b, y ∈ U ↔ h y ∈ V)
    {x z : ℝ} (hx : x ∈ Set.Ioo a b) (hz : z ∈ Set.Ioo a b)
    (hxU : x ∈ U) (hzU : z ∈ U) :
    connectedComponentIn U x = connectedComponentIn U z ↔
      connectedComponentIn V (h x) = connectedComponentIn V (h z) := by
  have hwindow : Set.uIcc x z ⊆ Set.Ioo a b :=
    Set.ordConnected_Ioo.uIcc_subset hx hz
  have hsymmMono : Monotone h.symm := by
    intro y t hyt
    apply hmono.le_iff_le.mp
    simpa only [h.apply_symm_apply] using hyt
  rw [real_component_eq_iff_uIcc_subset hxU hzU,
    real_component_eq_iff_uIcc_subset ((hlocal x hx).mp hxU) ((hlocal z hz).mp hzU)]
  constructor
  · intro hsegment y hy
    have hpre : h.symm y ∈ Set.uIcc x z := by
      simpa only [h.symm_apply_apply] using
        hsymmMono.image_uIcc_subset (Set.mem_image_of_mem h.symm hy)
    have hpreV := (hlocal (h.symm y) (hwindow hpre)).mp (hsegment hpre)
    simpa only [h.apply_symm_apply] using hpreV
  · intro hsegment y hy
    exact (hlocal y (hwindow hy)).mpr
      (hsegment (hmono.monotone.image_uIcc_subset (Set.mem_image_of_mem h hy)))

/-!
Private component-shape lemmas for the T07 component-closure scratch proof.

This fragment is intended to be inserted inside
`Tiling.AxisParallel.Terminal`, after the successor prelude. It deliberately
adds no imports or production declarations.
-/

private theorem not_open_left_boundary {s : Set ℝ} {a : ℝ}
    (hs : IsOpen s) (ha : a ∈ s) (hout : ∀ y < a, y ∉ s) : False := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs a ha
  have hnear : a - ε / 2 ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_nonpos (by linarith : a - ε / 2 - a ≤ 0)]
    linarith
  exact hout (a - ε / 2) (by linarith) (hball hnear)

private theorem not_open_right_boundary {s : Set ℝ} {b : ℝ}
    (hs : IsOpen s) (hb : b ∈ s) (hout : ∀ y, b < y → y ∉ s) : False := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs b hb
  have hnear : b + ε / 2 ∈ Metric.ball b ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_nonneg (by linarith : b + ε / 2 - b ≥ 0)]
    linarith
  exact hout (b + ε / 2) (by linarith) (hball hnear)

private theorem connectedComponentIn_open_classification
    {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) :
    (∃ a b, a < b ∧ connectedComponentIn U x = Set.Ioo a b) ∨
    (∃ a, connectedComponentIn U x = Set.Ioi a) ∨
    (∃ b, connectedComponentIn U x = Set.Iio b) ∨
    connectedComponentIn U x = Set.univ := by
  let J : Set ℝ := connectedComponentIn U x
  have hxJ : x ∈ J := by
    exact mem_connectedComponentIn hx
  have hJopen : IsOpen J := by
    exact hU.connectedComponentIn
  have hJpre : IsPreconnected J := by
    exact isPreconnected_connectedComponentIn
  rcases hJpre.mem_intervals with
    hIcc | hIco | hIoc | hIoo | hIci | hIoi | hIic | hIio | hUniv | hEmpty
  · have hxI : x ∈ Set.Icc (sInf J) (sSup J) :=
      (Set.ext_iff.mp hIcc x).mp hxJ
    have haI : sInf J ∈ Set.Icc (sInf J) (sSup J) := by
      change sInf J ≤ sInf J ∧ sInf J ≤ sSup J
      exact ⟨le_rfl, hxI.1.trans hxI.2⟩
    have haJ : sInf J ∈ J := (Set.ext_iff.mp hIcc (sInf J)).mpr haI
    exact False.elim <| not_open_left_boundary hJopen haJ fun y hy => by
      intro hyJ
      have hyI : y ∈ Set.Icc (sInf J) (sSup J) :=
        (Set.ext_iff.mp hIcc y).mp hyJ
      exact (not_le_of_gt hy) hyI.1
  · have hxI : x ∈ Set.Ico (sInf J) (sSup J) :=
      (Set.ext_iff.mp hIco x).mp hxJ
    have haI : sInf J ∈ Set.Ico (sInf J) (sSup J) := by
      change sInf J ≤ sInf J ∧ sInf J < sSup J
      exact ⟨le_rfl, hxI.1.trans_lt hxI.2⟩
    have haJ : sInf J ∈ J := (Set.ext_iff.mp hIco (sInf J)).mpr haI
    exact False.elim <| not_open_left_boundary hJopen haJ fun y hy => by
      intro hyJ
      have hyI : y ∈ Set.Ico (sInf J) (sSup J) :=
        (Set.ext_iff.mp hIco y).mp hyJ
      exact (not_le_of_gt hy) hyI.1
  · have hxI : x ∈ Set.Ioc (sInf J) (sSup J) :=
      (Set.ext_iff.mp hIoc x).mp hxJ
    have hbI : sSup J ∈ Set.Ioc (sInf J) (sSup J) := by
      change sInf J < sSup J ∧ sSup J ≤ sSup J
      exact ⟨hxI.1.trans_le hxI.2, le_rfl⟩
    have hbJ : sSup J ∈ J := (Set.ext_iff.mp hIoc (sSup J)).mpr hbI
    exact False.elim <| not_open_right_boundary hJopen hbJ fun y hy => by
      intro hyJ
      have hyI : y ∈ Set.Ioc (sInf J) (sSup J) :=
        (Set.ext_iff.mp hIoc y).mp hyJ
      exact (not_le_of_gt hy) hyI.2
  · have hxI : x ∈ Set.Ioo (sInf J) (sSup J) :=
      (Set.ext_iff.mp hIoo x).mp hxJ
    refine Or.inl ⟨sInf J, sSup J, hxI.1.trans hxI.2, ?_⟩
    change J = Set.Ioo (sInf J) (sSup J)
    exact hIoo
  · have hxI : x ∈ Set.Ici (sInf J) :=
      (Set.ext_iff.mp hIci x).mp hxJ
    have haI : sInf J ∈ Set.Ici (sInf J) := by
      change sInf J ≤ sInf J
      exact le_rfl
    have haJ : sInf J ∈ J := (Set.ext_iff.mp hIci (sInf J)).mpr haI
    exact False.elim <| not_open_left_boundary hJopen haJ fun y hy => by
      intro hyJ
      have hyI : y ∈ Set.Ici (sInf J) :=
        (Set.ext_iff.mp hIci y).mp hyJ
      exact (not_le_of_gt hy) hyI
  · refine Or.inr <| Or.inl ⟨sInf J, ?_⟩
    change J = Set.Ioi (sInf J)
    exact hIoi
  · have hxI : x ∈ Set.Iic (sSup J) :=
      (Set.ext_iff.mp hIic x).mp hxJ
    have hbI : sSup J ∈ Set.Iic (sSup J) := by
      change sSup J ≤ sSup J
      exact le_rfl
    have hbJ : sSup J ∈ J := (Set.ext_iff.mp hIic (sSup J)).mpr hbI
    exact False.elim <| not_open_right_boundary hJopen hbJ fun y hy => by
      intro hyJ
      have hyI : y ∈ Set.Iic (sSup J) :=
        (Set.ext_iff.mp hIic y).mp hyJ
      exact (not_le_of_gt hy) hyI
  · refine Or.inr <| Or.inr <| Or.inl ⟨sSup J, ?_⟩
    change J = Set.Iio (sSup J)
    exact hIio
  · refine Or.inr <| Or.inr <| Or.inr ?_
    change J = Set.univ
    exact hUniv
  · rw [hEmpty] at hxJ
    simp at hxJ

private theorem connectedComponentIn_finite_endpoint_frontier
    {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U)
    {J : Set ℝ} (hJ : J = connectedComponentIn U x) :
    (∀ a b, a < b → J = Set.Ioo a b → a ∈ frontier U ∧ b ∈ frontier U) ∧
    (∀ a, J = Set.Ioi a → a ∈ frontier U) ∧
    (∀ b, J = Set.Iio b → b ∈ frontier U) := by
  have hxJ : x ∈ J := by rw [hJ]; exact mem_connectedComponentIn hx
  have hJsub : J ⊆ U := by rw [hJ]; exact connectedComponentIn_subset U x
  have endpoint_frontier : ∀ e : ℝ, e ∈ closure J → e ∉ J → e ∈ frontier U := by
    intro e heclosure heJ
    have heclosureU : e ∈ closure U := closure_mono hJsub heclosure
    have hnotU : e ∉ U := by
      intro heU
      have hcompOpen : IsOpen (connectedComponentIn U e) := hU.connectedComponentIn
      have hcompNhds : connectedComponentIn U e ∈ 𝓝 e :=
        hcompOpen.mem_nhds (mem_connectedComponentIn heU)
      obtain ⟨y, hycomp, hyJ⟩ := mem_closure_iff_nhds.mp heclosure _ hcompNhds
      have hyx : y ∈ connectedComponentIn U x := by
        rw [← hJ]
        exact hyJ
      have hye : y ∈ connectedComponentIn U e := hycomp
      have heqE := connectedComponentIn_eq hye
      have heqX := connectedComponentIn_eq hyx
      have heq : connectedComponentIn U e = connectedComponentIn U x := heqE.trans heqX.symm
      apply heJ
      rw [hJ, ← heq]
      exact mem_connectedComponentIn heU
    have hnotInterior : e ∉ interior U := fun he => hnotU (interior_subset he)
    exact ⟨heclosureU, hnotInterior⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab hshape
    have haClosure : a ∈ closure J := by
      rw [hshape, closure_Ioo hab.ne]
      exact ⟨le_rfl, hab.le⟩
    have hbClosure : b ∈ closure J := by
      rw [hshape, closure_Ioo hab.ne]
      exact ⟨hab.le, le_rfl⟩
    have haNot : a ∉ J := by simp [hshape]
    have hbNot : b ∉ J := by simp [hshape]
    exact ⟨endpoint_frontier a haClosure haNot, endpoint_frontier b hbClosure hbNot⟩
  · intro a hshape
    have haClosure : a ∈ closure J := by
      rw [hshape, closure_Ioi]
      change a ≤ a
      exact le_rfl
    have haNot : a ∉ J := by simp [hshape]
    exact endpoint_frontier a haClosure haNot
  · intro b hshape
    have hbClosure : b ∈ closure J := by
      rw [hshape, closure_Iio]
      change b ≤ b
      exact le_rfl
    have hbNot : b ∉ J := by simp [hshape]
    exact endpoint_frontier b hbClosure hbNot

/-!
The endpoint-label midpoint component correspondence for the T07 successor.
Insert this private theorem inside `Tiling.AxisParallel.Terminal`, after the
endpoint-window and local component helpers.
-/

private theorem endpointIntervalMidpoint_sameComponent_iff
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (i j : Fin A.raw.presentation.n) (s t : S) :
    let sourceIntervals := ⋃ k : Fin A.raw.presentation.n, ⋃ u : S,
      Set.Ioo
        ((IndexedSectionEndpoint.mk ⟨k, false⟩ u).sourceValue)
        ((IndexedSectionEndpoint.mk ⟨k, true⟩ u).sourceValue)
    let targetIntervals := ⋃ k : Fin A.raw.presentation.n, ⋃ u : S,
      Set.Ioo
        (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨k, false⟩ u))
        (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨k, true⟩ u))
    let sourceLeft := (IndexedSectionEndpoint.mk ⟨i, false⟩ s).sourceValue
    let sourceRight := (IndexedSectionEndpoint.mk ⟨i, true⟩ s).sourceValue
    let sourceLeft' := (IndexedSectionEndpoint.mk ⟨j, false⟩ t).sourceValue
    let sourceRight' := (IndexedSectionEndpoint.mk ⟨j, true⟩ t).sourceValue
    let targetLeft := IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
      (IndexedSectionEndpoint.mk ⟨i, false⟩ s)
    let targetRight := IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
      (IndexedSectionEndpoint.mk ⟨i, true⟩ s)
    let targetLeft' := IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
      (IndexedSectionEndpoint.mk ⟨j, false⟩ t)
    let targetRight' := IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
      (IndexedSectionEndpoint.mk ⟨j, true⟩ t)
    connectedComponentIn (interior (closure sourceIntervals))
        ((sourceLeft + sourceRight) / 2) =
      connectedComponentIn (interior (closure sourceIntervals))
        ((sourceLeft' + sourceRight') / 2) ↔
      connectedComponentIn (interior (closure targetIntervals))
        ((targetLeft + targetRight) / 2) =
      connectedComponentIn (interior (closure targetIntervals))
        ((targetLeft' + targetRight') / 2) := by
  classical
  let P := Fin A.raw.presentation.n × S
  let leftLabel : P → IndexedSectionEndpoint A S :=
    fun p => IndexedSectionEndpoint.mk ⟨p.1, false⟩ p.2
  let rightLabel : P → IndexedSectionEndpoint A S :=
    fun p => IndexedSectionEndpoint.mk ⟨p.1, true⟩ p.2
  let v : IndexedSectionEndpoint A S → ℝ := fun e => e.sourceValue
  let w : IndexedSectionEndpoint A S → ℝ := fun e =>
    IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e
  let p : P := (i, s)
  let q : P := (j, t)
  let e : IndexedSectionEndpoint A S :=
    if v (leftLabel p) ≤ v (leftLabel q) then leftLabel p else leftLabel q
  let f : IndexedSectionEndpoint A S :=
    if v (rightLabel p) ≤ v (rightLabel q) then rightLabel q else rightLabel p
  have hleftP : v (leftLabel p) < v (rightLabel p) := by
    dsimp [v, leftLabel, rightLabel, p, IndexedSectionEndpoint.sourceValue,
      SectionEndpointLabel.rawValue]
    linarith [A.raw.presentation.lt i]
  have hleftQ : v (leftLabel q) < v (rightLabel q) := by
    dsimp [v, leftLabel, rightLabel, q, IndexedSectionEndpoint.sourceValue,
      SectionEndpointLabel.rawValue]
    linarith [A.raw.presentation.lt j]
  have hminP : v e ≤ v (leftLabel p) := by
    dsimp [e]
    split_ifs with h
    · exact le_rfl
    · exact le_of_not_ge h
  have hminQ : v e ≤ v (leftLabel q) := by
    dsimp [e]
    split_ifs with h
    · exact h
    · exact le_rfl
  have hmaxP : v (rightLabel p) ≤ v f := by
    dsimp [f]
    split_ifs with h
    · exact h
    · exact le_rfl
  have hmaxQ : v (rightLabel q) ≤ v f := by
    dsimp [f]
    split_ifs with h
    · exact le_rfl
    · exact le_of_not_ge h
  let m : P → ℝ := fun z => (v (leftLabel z) + v (rightLabel z)) / 2
  have hmidPleft : v (leftLabel p) < m p := by
    dsimp [m]
    linarith
  have hmidPright : m p < v (rightLabel p) := by
    dsimp [m]
    linarith
  have hmidQleft : v (leftLabel q) < m q := by
    dsimp [m]
    linarith
  have hmidQright : m q < v (rightLabel q) := by
    dsimp [m]
    linarith
  have hxP : m p ∈ Set.Ioo (v e) (v f) :=
    ⟨lt_of_le_of_lt hminP hmidPleft, lt_of_lt_of_le hmidPright hmaxP⟩
  have hxQ : m q ∈ Set.Ioo (v e) (v f) :=
    ⟨lt_of_le_of_lt hminQ hmidQleft, lt_of_lt_of_le hmidQright hmaxQ⟩
  obtain ⟨h, hmono, hwindow⟩ := endpointFiniteWindow_homeomorph E (v e) (v f)
  have horder : ∀ a b, v a ≤ v b ↔ w a ≤ w b := E.weakOrder_iff
  have hlocal : ∀ y ∈ Set.Ioo (v e) (v f),
      y ∈ interior (closure (⋃ z : P,
        Set.Ioo (v (leftLabel z)) (v (rightLabel z)))) ↔
      h y ∈ interior (closure (⋃ z : P,
        Set.Ioo (w (leftLabel z)) (w (rightLabel z)))) := by
    intro y hy
    exact locallyOrderedWindow_regularizedIntervals_iff v w leftLabel rightLabel
      horder e f h hmono hwindow hy
  have hmidPsource : m p ∈ interior (closure (⋃ z : P,
      Set.Ioo (v (leftLabel z)) (v (rightLabel z)))) := by
    have hraw : m p ∈ ⋃ z : P, Set.Ioo (v (leftLabel z)) (v (rightLabel z)) :=
      Set.mem_iUnion.mpr ⟨p, ⟨hmidPleft, hmidPright⟩⟩
    exact (isOpen_iUnion fun z => isOpen_Ioo).subset_interior_closure hraw
  have hmidQsource : m q ∈ interior (closure (⋃ z : P,
      Set.Ioo (v (leftLabel z)) (v (rightLabel z)))) := by
    have hraw : m q ∈ ⋃ z : P, Set.Ioo (v (leftLabel z)) (v (rightLabel z)) :=
      Set.mem_iUnion.mpr ⟨q, ⟨hmidQleft, hmidQright⟩⟩
    exact (isOpen_iUnion fun z => isOpen_Ioo).subset_interior_closure hraw
  have hcomponentImages := increasing_localTrace_component_eq_iff
    (interior (closure (⋃ z : P, Set.Ioo (v (leftLabel z)) (v (rightLabel z)))))
    (interior (closure (⋃ z : P, Set.Ioo (w (leftLabel z)) (w (rightLabel z)))))
    (v e) (v f) h hmono hlocal hxP hxQ hmidPsource hmidQsource
  have htargetLeftP : h (v (leftLabel p)) = w (leftLabel p) := by
    apply hwindow
    · exact hminP
    · exact (hleftP.le.trans hmaxP)
  have htargetRightP : h (v (rightLabel p)) = w (rightLabel p) := by
    apply hwindow
    · exact (hminP.trans hleftP.le)
    · exact hmaxP
  have htargetLeftQ : h (v (leftLabel q)) = w (leftLabel q) := by
    apply hwindow
    · exact hminQ
    · exact (hleftQ.le.trans hmaxQ)
  have htargetRightQ : h (v (rightLabel q)) = w (rightLabel q) := by
    apply hwindow
    · exact (hminQ.trans hleftQ.le)
    · exact hmaxQ
  let n : P → ℝ := fun z => (w (leftLabel z) + w (rightLabel z)) / 2
  have himagePleft : w (leftLabel p) < h (m p) := by
    rw [← htargetLeftP]
    exact hmono hmidPleft
  have himagePright : h (m p) < w (rightLabel p) := by
    rw [← htargetRightP]
    exact hmono hmidPright
  have himageQleft : w (leftLabel q) < h (m q) := by
    rw [← htargetLeftQ]
    exact hmono hmidQleft
  have himageQright : h (m q) < w (rightLabel q) := by
    rw [← htargetRightQ]
    exact hmono hmidQright
  have htargetP : w (leftLabel p) < w (rightLabel p) := by
    rw [← htargetLeftP, ← htargetRightP]
    exact hmono hleftP
  have htargetQ : w (leftLabel q) < w (rightLabel q) := by
    rw [← htargetLeftQ, ← htargetRightQ]
    exact hmono hleftQ
  have htargetMidP : n p ∈ Set.Ioo (w (leftLabel p)) (w (rightLabel p)) := by
    dsimp [n]
    constructor <;> linarith [htargetP]
  have htargetMidQ : n q ∈ Set.Ioo (w (leftLabel q)) (w (rightLabel q)) := by
    dsimp [n]
    constructor <;> linarith [htargetQ]
  have htargetIntervalP : Set.Ioo (w (leftLabel p)) (w (rightLabel p)) ⊆
      interior (closure (⋃ z : P, Set.Ioo (w (leftLabel z)) (w (rightLabel z)))) := by
    intro z hz
    have hzRaw : z ∈ ⋃ z : P, Set.Ioo (w (leftLabel z)) (w (rightLabel z)) :=
      Set.mem_iUnion.mpr ⟨p, hz⟩
    exact (isOpen_iUnion fun z => isOpen_Ioo).subset_interior_closure hzRaw
  have htargetIntervalQ : Set.Ioo (w (leftLabel q)) (w (rightLabel q)) ⊆
      interior (closure (⋃ z : P, Set.Ioo (w (leftLabel z)) (w (rightLabel z)))) := by
    intro z hz
    have hzRaw : z ∈ ⋃ z : P, Set.Ioo (w (leftLabel z)) (w (rightLabel z)) :=
      Set.mem_iUnion.mpr ⟨q, hz⟩
    exact (isOpen_iUnion fun z => isOpen_Ioo).subset_interior_closure hzRaw
  have hcomponentP : connectedComponentIn
        (interior (closure (⋃ z : P, Set.Ioo (w (leftLabel z)) (w (rightLabel z)))))
        (h (m p)) = connectedComponentIn
        (interior (closure (⋃ z : P, Set.Ioo (w (leftLabel z)) (w (rightLabel z)))))
        (n p) := by
    apply connectedComponentIn_eq
    have hsub := isPreconnected_Ioo.subset_connectedComponentIn
      ⟨himagePleft, himagePright⟩ htargetIntervalP
    exact hsub htargetMidP
  have hcomponentQ : connectedComponentIn
        (interior (closure (⋃ z : P, Set.Ioo (w (leftLabel z)) (w (rightLabel z)))))
        (h (m q)) = connectedComponentIn
        (interior (closure (⋃ z : P, Set.Ioo (w (leftLabel z)) (w (rightLabel z)))))
        (n q) := by
    apply connectedComponentIn_eq
    have hsub := isPreconnected_Ioo.subset_connectedComponentIn
      ⟨himageQleft, himageQright⟩ htargetIntervalQ
    exact hsub htargetMidQ
  have hsourceIndex :
      (⋃ k : Fin A.raw.presentation.n, ⋃ u : S,
        Set.Ioo
          ((IndexedSectionEndpoint.mk ⟨k, false⟩ u).sourceValue)
          ((IndexedSectionEndpoint.mk ⟨k, true⟩ u).sourceValue)) =
        ⋃ z : P, Set.Ioo (v (leftLabel z)) (v (rightLabel z)) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, u, hx⟩
      exact ⟨(k, u), by simpa [v, leftLabel, rightLabel] using hx⟩
    · rintro ⟨⟨k, u⟩, hx⟩
      exact ⟨k, u, by simpa [v, leftLabel, rightLabel] using hx⟩
  have htargetIndex :
      (⋃ k : Fin A.raw.presentation.n, ⋃ u : S,
        Set.Ioo
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨k, false⟩ u))
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨k, true⟩ u)) ) =
        ⋃ z : P, Set.Ioo (w (leftLabel z)) (w (rightLabel z)) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, u, hx⟩
      exact ⟨(k, u), by simpa [w, leftLabel, rightLabel] using hx⟩
    · rintro ⟨⟨k, u⟩, hx⟩
      exact ⟨k, u, by simpa [w, leftLabel, rightLabel] using hx⟩
  dsimp only
  rw [hsourceIndex, htargetIndex]
  change connectedComponentIn
      (interior (closure (⋃ z : P, Set.Ioo (v (leftLabel z)) (v (rightLabel z))))) (m p) =
    connectedComponentIn
      (interior (closure (⋃ z : P, Set.Ioo (v (leftLabel z)) (v (rightLabel z))))) (m q) ↔
    connectedComponentIn
      (interior (closure (⋃ z : P, Set.Ioo (w (leftLabel z)) (w (rightLabel z))))) (n p) =
    connectedComponentIn
      (interior (closure (⋃ z : P, Set.Ioo (w (leftLabel z)) (w (rightLabel z))))) (n q)
  rw [← hcomponentP, ← hcomponentQ]
  exact hcomponentImages

private theorem intervalMidpoint_mem_regularizedUnion
    {ι : Type*} (l r : ι → ℝ) (hlt : ∀ i, l i < r i) (i : ι) :
    (l i + r i) / 2 ∈ interior (closure (⋃ j, Set.Ioo (l j) (r j))) := by
  have hmid : (l i + r i) / 2 ∈ Set.Ioo (l i) (r i) := by
    constructor <;> linarith [hlt i]
  have hraw : (l i + r i) / 2 ∈ ⋃ j, Set.Ioo (l j) (r j) :=
    Set.mem_iUnion.mpr ⟨i, hmid⟩
  exact (isOpen_iUnion fun _ => isOpen_Ioo).subset_interior_closure hraw

private theorem regularizedIntervalComponent_contains_midpoint
    {ι : Type*} (l r : ι → ℝ) (hlt : ∀ i, l i < r i)
    {x : ℝ} (hx : x ∈ interior (closure (⋃ j, Set.Ioo (l j) (r j)))) :
    ∃ i, (l i + r i) / 2 ∈ connectedComponentIn
      (interior (closure (⋃ j, Set.Ioo (l j) (r j)))) x := by
  let raw := ⋃ j, Set.Ioo (l j) (r j)
  let U := interior (closure raw)
  have hxU : x ∈ U := hx
  have hcompOpen : IsOpen (connectedComponentIn U x) :=
    isOpen_interior.connectedComponentIn
  have hcompNhds : connectedComponentIn U x ∈ 𝓝 x :=
    hcompOpen.mem_nhds (mem_connectedComponentIn hxU)
  obtain ⟨y, hyComp, hyRaw⟩ :=
    mem_closure_iff_nhds.mp (interior_subset hxU) _ hcompNhds
  obtain ⟨i, hyI⟩ := Set.mem_iUnion.mp hyRaw
  have hrawU : raw ⊆ U := (isOpen_iUnion fun _ => isOpen_Ioo).subset_interior_closure
  have hIU : Set.Ioo (l i) (r i) ⊆ U := by
    intro z hz
    exact hrawU (Set.mem_iUnion.mpr ⟨i, hz⟩)
  have hIcomp : Set.Ioo (l i) (r i) ⊆ connectedComponentIn U y :=
    isPreconnected_Ioo.subset_connectedComponentIn hyI hIU
  have hmid : (l i + r i) / 2 ∈ Set.Ioo (l i) (r i) := by
    constructor <;> linarith [hlt i]
  refine ⟨i, ?_⟩
  change (l i + r i) / 2 ∈ connectedComponentIn U x
  rw [connectedComponentIn_eq hyComp]
  exact hIcomp hmid

private theorem regularizedIntervalComponents_equiv_of_midpointRelation
    {ι : Type*} (l r l' r' : ι → ℝ)
    (hlt : ∀ i, l i < r i) (hlt' : ∀ i, l' i < r' i)
    (hrelation : ∀ i j,
      connectedComponentIn (interior (closure (⋃ k, Set.Ioo (l k) (r k))))
          ((l i + r i) / 2) =
        connectedComponentIn (interior (closure (⋃ k, Set.Ioo (l k) (r k))))
          ((l j + r j) / 2) ↔
      connectedComponentIn (interior (closure (⋃ k, Set.Ioo (l' k) (r' k))))
          ((l' i + r' i) / 2) =
        connectedComponentIn (interior (closure (⋃ k, Set.Ioo (l' k) (r' k))))
          ((l' j + r' j) / 2)) :
    let U := interior (closure (⋃ k, Set.Ioo (l k) (r k)))
    let V := interior (closure (⋃ k, Set.Ioo (l' k) (r' k)))
    ∃ F : ↥{J : Set ℝ | ∃ x ∈ U, J = connectedComponentIn U x} ≃
        ↥{J : Set ℝ | ∃ x ∈ V, J = connectedComponentIn V x},
      ∀ J i, (l i + r i) / 2 ∈ J.1 ↔ (l' i + r' i) / 2 ∈ (F J).1 := by
  let U := interior (closure (⋃ k, Set.Ioo (l k) (r k)))
  let V := interior (closure (⋃ k, Set.Ioo (l' k) (r' k)))
  let source := {J : Set ℝ | ∃ x ∈ U, J = connectedComponentIn U x}
  let target := {J : Set ℝ | ∃ x ∈ V, J = connectedComponentIn V x}
  let m : ι → ℝ := fun i => (l i + r i) / 2
  let n : ι → ℝ := fun i => (l' i + r' i) / 2
  have hm (i : ι) : m i ∈ U := intervalMidpoint_mem_regularizedUnion l r hlt i
  have hn (i : ι) : n i ∈ V := intervalMidpoint_mem_regularizedUnion l' r' hlt' i
  have hsource (J : ↥source) : ∃ i, connectedComponentIn U (m i) = J.1 := by
    obtain ⟨x, hx, hJ⟩ := J.2
    obtain ⟨i, hi⟩ := regularizedIntervalComponent_contains_midpoint l r hlt hx
    refine ⟨i, ?_⟩
    exact (connectedComponentIn_eq hi).symm.trans hJ.symm
  have htarget (J : ↥target) : ∃ i, connectedComponentIn V (n i) = J.1 := by
    obtain ⟨x, hx, hJ⟩ := J.2
    obtain ⟨i, hi⟩ := regularizedIntervalComponent_contains_midpoint l' r' hlt' hx
    refine ⟨i, ?_⟩
    exact (connectedComponentIn_eq hi).symm.trans hJ.symm
  let chooseSource (J : ↥source) : ι := Classical.choose (hsource J)
  let chooseTarget (J : ↥target) : ι := Classical.choose (htarget J)
  have hchooseSource (J : ↥source) :
      connectedComponentIn U (m (chooseSource J)) = J.1 :=
    Classical.choose_spec (hsource J)
  have hchooseTarget (J : ↥target) :
      connectedComponentIn V (n (chooseTarget J)) = J.1 :=
    Classical.choose_spec (htarget J)
  let toTarget (J : ↥source) : ↥target :=
    ⟨connectedComponentIn V (n (chooseSource J)),
      ⟨n (chooseSource J), hn (chooseSource J), rfl⟩⟩
  let toSource (J : ↥target) : ↥source :=
    ⟨connectedComponentIn U (m (chooseTarget J)),
      ⟨m (chooseTarget J), hm (chooseTarget J), rfl⟩⟩
  let F : ↥source ≃ ↥target := {
    toFun := toTarget
    invFun := toSource
    left_inv := by
      intro J
      apply Subtype.ext
      change connectedComponentIn U (m (chooseTarget (toTarget J))) = J.1
      calc
        connectedComponentIn U (m (chooseTarget (toTarget J))) =
            connectedComponentIn U (m (chooseSource J)) :=
          (hrelation _ _).mpr (hchooseTarget (toTarget J))
        _ = J.1 := hchooseSource J
    right_inv := by
      intro J
      apply Subtype.ext
      change connectedComponentIn V (n (chooseSource (toSource J))) = J.1
      calc
        connectedComponentIn V (n (chooseSource (toSource J))) =
            connectedComponentIn V (n (chooseTarget J)) :=
          (hrelation _ _).mp (hchooseSource (toSource J))
        _ = J.1 := hchooseTarget J
  }
  refine ⟨F, ?_⟩
  intro J i
  have hJ : J.1 = connectedComponentIn U (m (chooseSource J)) :=
    (hchooseSource J).symm
  change m i ∈ J.1 ↔ n i ∈ connectedComponentIn V (n (chooseSource J))
  rw [hJ]
  constructor
  · intro hi
    have hsourceEq := connectedComponentIn_eq hi
    have htargetEq := (hrelation (chooseSource J) i).mp hsourceEq
    rw [htargetEq]
    exact mem_connectedComponentIn (hn i)
  · intro hi
    have htargetEq := connectedComponentIn_eq hi
    have hsourceEq := (hrelation (chooseSource J) i).mpr htargetEq
    rw [hsourceEq]
    exact mem_connectedComponentIn (hm i)

private theorem boundedComponent_noTargetInterval_cross_right
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S))
    (e : IndexedSectionEndpoint A S) (he : e.sourceValue = J.right)
    (i : Fin A.raw.presentation.n) (s : S) :
    ¬ (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, false⟩ s) <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ∧
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) := by
  intro hcross
  let e₀ : IndexedSectionEndpoint A S := IndexedSectionEndpoint.mk ⟨i, false⟩ s
  let e₁ : IndexedSectionEndpoint A S := IndexedSectionEndpoint.mk ⟨i, true⟩ s
  have hcross' :
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₀ <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ∧
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₁ := by
    simpa [e₀, e₁] using hcross
  have hsourceLeft : e₀.sourceValue < J.right := by
    rw [← he]
    exact (allEndpointWeakOrderTransport_endpoint_lt_iff E e₀ e).mpr hcross'.1
  have hsourceRight : J.right < e₁.sourceValue := by
    rw [← he]
    exact (allEndpointWeakOrderTransport_endpoint_lt_iff E e e₁).mpr hcross'.2
  have hlower : max e₀.sourceValue J.left < J.right := by
    rw [max_lt_iff]
    exact ⟨hsourceLeft, J.ordered⟩
  obtain ⟨x, hxlower, hxupper⟩ := exists_between hlower
  have hmeet : (Set.Ioo
      (A.raw.presentation.left i + axis.coord s.1.1 - A.origin)
      (A.raw.presentation.right i + axis.coord s.1.1 - A.origin) ∩
        Set.Ioo J.left J.right).Nonempty := by
    refine ⟨x, ⟨?_, ?_⟩, ⟨?_, hxupper⟩⟩
    · simpa [e₀, IndexedSectionEndpoint.sourceValue,
        SectionEndpointLabel.rawValue] using
          lt_of_le_of_lt (le_max_left _ _) hxlower
    · simpa [e₁, IndexedSectionEndpoint.sourceValue,
        SectionEndpointLabel.rawValue] using
          lt_trans hxupper hsourceRight
    · exact lt_of_le_of_lt (le_max_right _ _) hxlower
  have hsubset := occupiedComponent_interval_subset A J
    (show s.1.1 ∈ Subtype.val '' S from ⟨s.1, s.2, rfl⟩) i hmeet
  have hlt : e₀.sourceValue < e₁.sourceValue := by
    simpa [e₀, e₁, IndexedSectionEndpoint.sourceValue,
      SectionEndpointLabel.rawValue] using A.raw.presentation.lt i
  have hsubset' : Set.Ioo e₀.sourceValue e₁.sourceValue ⊆ Set.Ioo J.left J.right := by
    simpa [e₀, e₁, IndexedSectionEndpoint.sourceValue,
      SectionEndpointLabel.rawValue] using hsubset
  have hclosed : Set.Icc e₀.sourceValue e₁.sourceValue ⊆ Set.Icc J.left J.right := by
    rw [← closure_Ioo (ne_of_lt hlt), ← closure_Ioo (ne_of_lt J.ordered)]
    exact closure_mono hsubset'
  have hrightmem : e₁.sourceValue ∈ Set.Icc J.left J.right :=
    hclosed ⟨hlt.le, le_rfl⟩
  exact (not_lt_of_ge hrightmem.2) hsourceRight

private theorem boundedComponent_noTargetExteriorInterval_start_right
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S))
    (e : IndexedSectionEndpoint A S) (he : e.sourceValue = J.right)
    (i : Fin A.raw.presentation.n) (s : S) :
    ¬ (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e =
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, false⟩ s) ∧
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) := by
  intro hexterior
  let e₀ : IndexedSectionEndpoint A S := IndexedSectionEndpoint.mk ⟨i, false⟩ s
  let e₁ : IndexedSectionEndpoint A S := IndexedSectionEndpoint.mk ⟨i, true⟩ s
  have hexterior' :
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e =
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₀ ∧
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₁ := by
    simpa [e₀, e₁] using hexterior
  have hsourceLeft : e₀.sourceValue = J.right := by
    rw [← he]
    exact (allEndpointWeakOrderTransport_endpoint_eq_iff E e₀ e).mpr hexterior'.1.symm
  have hsourceRight : J.right < e₁.sourceValue := by
    rw [← he]
    exact (allEndpointWeakOrderTransport_endpoint_lt_iff E e e₁).mpr hexterior'.2
  let sourceTrace := interior (closure (A.carrier + axis.coord '' (Subtype.val '' S)))
  let sourceIntervals := ⋃ j : Fin A.raw.presentation.n, ⋃ t : S,
    Set.Ioo
      ((IndexedSectionEndpoint.mk ⟨j, false⟩ t).sourceValue)
      ((IndexedSectionEndpoint.mk ⟨j, true⟩ t).sourceValue)
  have hsourceTrace : sourceTrace = interior (closure sourceIntervals) := E.source_union_eq
  have hrightSourceOpen : IsOpen sourceTrace := isOpen_interior
  have hrightFrontier : J.right ∈ frontier sourceTrace := by
    have hEnds := boundedIntervalComponent_endpoints_frontier hrightSourceOpen
      J.ordered J.component_eq
    exact hEnds.2
  have hsourceLt : e₀.sourceValue < e₁.sourceValue := by
    simpa [e₀, e₁, IndexedSectionEndpoint.sourceValue,
      SectionEndpointLabel.rawValue] using A.raw.presentation.lt i
  have hrawSubset : Set.Ioo e₀.sourceValue e₁.sourceValue ⊆ sourceIntervals := by
    intro x hx
    simp only [sourceIntervals, Set.mem_iUnion]
    exact ⟨i, s, by simpa [e₀, e₁] using hx⟩
  have hclosedSubset : Set.Icc e₀.sourceValue e₁.sourceValue ⊆ closure sourceIntervals := by
    rw [← closure_Ioo (ne_of_lt hsourceLt)]
    exact closure_mono hrawSubset
  have hIooSource : Set.Ioo J.left J.right ⊆ sourceTrace := by
    intro x hx
    have hxcomp : x ∈ connectedComponentIn sourceTrace ((J.left + J.right) / 2) := by
      rw [J.component_eq]
      exact hx
    exact connectedComponentIn_subset sourceTrace _ hxcomp
  have hmidLeft : J.left < (J.left + J.right) / 2 := by linarith [J.ordered]
  have hmidRight : (J.left + J.right) / 2 < J.right := by linarith [J.ordered]
  have hnear : Set.Ioo ((J.left + J.right) / 2) e₁.sourceValue ⊆
      closure sourceIntervals := by
    intro x hx
    by_cases hxa : J.right ≤ x
    · exact hclosedSubset ⟨by simpa [hsourceLeft] using hxa, hx.2.le⟩
    · have hxJ : x ∈ Set.Ioo J.left J.right :=
        ⟨lt_trans hmidLeft hx.1, lt_of_not_ge hxa⟩
      have hxtrace := hIooSource hxJ
      rw [hsourceTrace] at hxtrace
      exact interior_subset hxtrace
  have hrightInterior : J.right ∈ interior (closure sourceIntervals) := by
    apply interior_maximal hnear isOpen_Ioo
    constructor
    · exact hmidRight
    · exact hsourceRight
  have hrightInTrace : J.right ∈ sourceTrace := by
    rw [hsourceTrace]
    exact hrightInterior
  have hrightNotInterior : J.right ∉ interior sourceTrace :=
    (mem_frontier_iff_notMem_interior hrightInTrace).mp hrightFrontier
  have hrightOpenInterior : J.right ∈ interior sourceTrace := by
    rw [hrightSourceOpen.interior_eq]
    exact hrightInTrace
  exact hrightNotInterior hrightOpenInterior

private theorem locallyFinite_interval_endpoint_not_interior_right
    {ι : Type*} (l r : ι → ℝ) (a : ℝ)
    (hfinite : ∀ b c : ℝ,
      ({x : ℝ | ∃ i, x = l i ∨ x = r i} ∩ Set.Icc b c).Finite)
    (hcross : ∀ i, l i < a → a < r i → False)
    (hstart : ∀ i, l i = a → a < r i → False) :
    a ∉ interior (closure (⋃ i, Set.Ioo (l i) (r i))) := by
  intro haInterior
  let E : Set ℝ := {x : ℝ | ∃ i, x = l i ∨ x = r i}
  let F : Set ℝ := E ∩ Set.Icc (a - 1) (a + 1)
  let G : Set ℝ := F \ {a}
  have hFfinite : F.Finite := hfinite (a - 1) (a + 1)
  have hGfinite : G.Finite := hFfinite.sdiff
  have haG : a ∉ G := by simp [G]
  have hGclosed : IsClosed G := hGfinite.isClosed
  have hGcomplNhds : Gᶜ ∈ 𝓝 a := hGclosed.isOpen_compl.mem_nhds haG
  have hInteriorNhds : interior (closure (⋃ i, Set.Ioo (l i) (r i))) ∈ 𝓝 a :=
    isOpen_interior.mem_nhds haInterior
  have hBothNhds :
      (interior (closure (⋃ i, Set.Ioo (l i) (r i))) ∩ Gᶜ) ∈ 𝓝 a :=
    inter_mem hInteriorNhds hGcomplNhds
  obtain ⟨p, q, hapq, hBoth⟩ :=
    (mem_nhds_iff_exists_Ioo_subset (a := a)
      (s := interior (closure (⋃ i, Set.Ioo (l i) (r i))) ∩ Gᶜ)).mp hBothNhds
  have hupper : a < min q (a + 1) := lt_min hapq.2 (by linarith)
  obtain ⟨x, hax, hxa⟩ := exists_between hupper
  have hxIoo : x ∈ Set.Ioo p q :=
    ⟨lt_trans hapq.1 hax, hxa.trans_le (min_le_left _ _)⟩
  have hxInterior : x ∈ interior (closure (⋃ i, Set.Ioo (l i) (r i))) :=
    (hBoth hxIoo).1
  have hx1 : x < a + 1 := lt_of_lt_of_le hxa (min_le_right _ _)
  have hxIcc : x ∈ Set.Icc (a - 1) (a + 1) := by constructor <;> linarith
  have hxnotE : x ∉ E := by
    intro hxE
    have hxF : x ∈ F := ⟨hxE, hxIcc⟩
    have hxG : x ∈ G := by
      simp only [G, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨hxF, ne_of_gt hax⟩
    exact (hBoth hxIoo).2 hxG
  have hxclosure : x ∈ closure (⋃ i, Set.Ioo (l i) (r i)) := interior_subset hxInterior
  have hxU : x ∈ ⋃ i, Set.Ioo (l i) (r i) := by
    by_contra hxnotU
    exact hxnotE (closure_interval_union_diff_subset_endpoints l r hfinite
      ⟨hxclosure, hxnotU⟩)
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxU
  have hright : x < r i := hxi.2
  rcases lt_trichotomy (l i) a with hleft | hleft | hleft
  · exact hcross i hleft (lt_trans hax hright)
  · exact hstart i hleft (lt_trans hax hright)
  · have hlIoo : l i ∈ Set.Ioo p q :=
      ⟨lt_trans hapq.1 hleft, lt_trans hxi.1 hxIoo.2⟩
    have hlIcc : l i ∈ Set.Icc (a - 1) (a + 1) :=
      ⟨by linarith, (lt_trans hxi.1 hx1).le⟩
    have hlG : l i ∈ G := by
      simp only [G, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨⟨⟨i, Or.inl rfl⟩, hlIcc⟩, ne_of_gt hleft⟩
    exact (hBoth hlIoo).2 hlG

private theorem boundedComponent_targetRight_not_interior
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S))
    (e : IndexedSectionEndpoint A S) (he : e.sourceValue = J.right) :
    IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ∉
      interior (closure (⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
        Set.Ioo
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, true⟩ s)))) := by
  let P := Fin A.raw.presentation.n × S
  let l : P → ℝ := fun p => IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
    (IndexedSectionEndpoint.mk ⟨p.1, false⟩ p.2)
  let r : P → ℝ := fun p => IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
    (IndexedSectionEndpoint.mk ⟨p.1, true⟩ p.2)
  have hfinite : ∀ a b : ℝ,
      ({x : ℝ | ∃ p, x = l p ∨ x = r p} ∩ Set.Icc a b).Finite := by
    intro a b
    apply (E.targetValues_locallyFinite a b).subset
    intro x hx
    rcases hx with ⟨hxE, hxIcc⟩
    rcases hxE with ⟨⟨i, s⟩, hx | hx⟩
    · exact ⟨⟨IndexedSectionEndpoint.mk ⟨i, false⟩ s, hx.symm⟩, hxIcc⟩
    · exact ⟨⟨IndexedSectionEndpoint.mk ⟨i, true⟩ s, hx.symm⟩, hxIcc⟩
  have hcross : ∀ p, l p < IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e →
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e < r p → False := by
    intro p hl hr
    rcases p with ⟨i, s⟩
    exact boundedComponent_noTargetInterval_cross_right E J e he i s
      (by simpa [l, r] using And.intro hl hr)
  have hstart : ∀ p, l p = IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e →
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e < r p → False := by
    intro p hl hr
    rcases p with ⟨i, s⟩
    exact boundedComponent_noTargetExteriorInterval_start_right E J e he i s
      (by simpa [l, r] using And.intro hl.symm hr)
  have hnot := locallyFinite_interval_endpoint_not_interior_right l r
    (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e) hfinite hcross hstart
  have hunion : (⋃ p : P, Set.Ioo (l p) (r p)) =
      ⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
        Set.Ioo
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) := by
    ext x
    simp [P, l, r]
  rw [← hunion]
  exact hnot

private theorem boundedComponent_targetComponent_eq
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S)) :
    ∃ e f : IndexedSectionEndpoint A S,
      e.sourceValue = J.left ∧ f.sourceValue = J.right ∧
      connectedComponentIn
        ((-mapScalar phi A.originScalar) +ᵥ
          interior (closure (⋃ s : deformedCenterCarrierOn Tphi S,
          axis.coord s +ᵥ {x : ℝ | FilledSliceChains.slicePoint axis
            (axis.transverseCoord (D.planarHomeomorph
              (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
                D.deformedRegion.openCarrier})))
        ((IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e +
            IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f) / 2) =
        Set.Ioo
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e)
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f) := by
  obtain ⟨e, f, he, hf, hbase⟩ := boundedComponent_targetInterval_subset E J
  let left : ℝ := IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e
  let right : ℝ := IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f
  let baseTrace := interior (closure (⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
    Set.Ioo
      (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
        (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
        (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨i, true⟩ s))))
  let normalizedTrace := (-mapScalar phi A.originScalar) +ᵥ
    interior (closure (⋃ s : deformedCenterCarrierOn Tphi S,
    axis.coord s +ᵥ {x : ℝ | FilledSliceChains.slicePoint axis
      (axis.transverseCoord (D.planarHomeomorph
        (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
          D.deformedRegion.openCarrier}))
  have hnormalized : normalizedTrace = baseTrace := by
    dsimp [normalizedTrace, baseTrace]
    rw [E.target_union_eq, neg_vadd_vadd]
  have horder : left < right := by
    apply (allEndpointWeakOrderTransport_endpoint_lt_iff E e f).mp
    rw [he, hf]
    exact J.ordered
  have hleftBaseAbsent : left ∉ baseTrace := by
    simpa [baseTrace, left] using boundedComponent_targetLeft_not_interior E J e he
  have hrightBaseAbsent : right ∉ baseTrace := by
    simpa [baseTrace, right] using boundedComponent_targetRight_not_interior E J f hf
  have htranslated : Set.Ioo left right ⊆ normalizedTrace := by
    intro y hy
    rw [hnormalized]
    exact hbase hy
  have hleftAbsent : left ∉ normalizedTrace := by
    rw [hnormalized]
    exact hleftBaseAbsent
  have hrightAbsent : right ∉ normalizedTrace := by
    rw [hnormalized]
    exact hrightBaseAbsent
  let midpoint := (left + right) / 2
  have hmidLeft : left < midpoint := by dsimp [midpoint]; linarith
  have hmidRight : midpoint < right := by dsimp [midpoint]; linarith
  have hmidMem : midpoint ∈ Set.Ioo left right :=
    ⟨hmidLeft, hmidRight⟩
  have hmidTrace : midpoint ∈ normalizedTrace := htranslated hmidMem
  have hmidComponent : midpoint ∈ connectedComponentIn normalizedTrace midpoint :=
    mem_connectedComponentIn hmidTrace
  have hcompPre : IsPreconnected (connectedComponentIn normalizedTrace midpoint) :=
    isPreconnected_connectedComponentIn
  have hcompSub : connectedComponentIn normalizedTrace midpoint ⊆ normalizedTrace :=
    connectedComponentIn_subset normalizedTrace midpoint
  have hintervalSub : Set.Ioo left right ⊆
      connectedComponentIn normalizedTrace midpoint := by
    exact isPreconnected_Ioo.subset_connectedComponentIn hmidMem htranslated
  have hcompInterval : connectedComponentIn normalizedTrace midpoint ⊆
      Set.Ioo left right := by
    intro y hy
    by_cases hleftY : left < y
    · by_cases hyRight : y < right
      · exact ⟨hleftY, hyRight⟩
      · have hrightY : right ≤ y := le_of_not_gt hyRight
        have hsegment := hcompPre.Icc_subset hmidComponent hy
        have hrightMem : right ∈ Set.Icc midpoint y :=
          ⟨le_of_lt hmidRight, hrightY⟩
        exact (hrightAbsent (hcompSub (hsegment hrightMem))).elim
    · have hyLeft : y ≤ left := le_of_not_gt hleftY
      have hsegment := hcompPre.Icc_subset hy hmidComponent
      have hleftMem : left ∈ Set.Icc y midpoint :=
        ⟨hyLeft, le_of_lt hmidLeft⟩
      exact (hleftAbsent (hcompSub (hsegment hleftMem))).elim
  refine ⟨e, f, he, hf, ?_⟩
  have hcompEq : connectedComponentIn normalizedTrace midpoint = Set.Ioo left right :=
    Set.Subset.antisymm hcompInterval hintervalSub
  simpa [normalizedTrace, midpoint, left, right] using hcompEq

private theorem boundedComponent_targetInterval_midpoint_mem
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A)
    (J : BoundedOccupiedTraceComponent A (Subtype.val '' S)) :
    ∃ e f : IndexedSectionEndpoint A S,
      e.sourceValue = J.left ∧ f.sourceValue = J.right ∧
      connectedComponentIn
        ((-mapScalar phi A.originScalar) +ᵥ
          interior (closure (⋃ s : deformedCenterCarrierOn Tphi S,
          axis.coord s +ᵥ {x : ℝ | FilledSliceChains.slicePoint axis
            (axis.transverseCoord (D.planarHomeomorph
              (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
                D.deformedRegion.openCarrier})))
        ((IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e +
            IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f) / 2) =
        Set.Ioo
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e)
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f) ∧
      ∀ (i : Fin A.raw.presentation.n) (s : S),
        ((IndexedSectionEndpoint.mk ⟨i, false⟩ s).sourceValue +
          (IndexedSectionEndpoint.mk ⟨i, true⟩ s).sourceValue) / 2 ∈
            Set.Ioo J.left J.right →
        ((IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, false⟩ s) +
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) / 2 ∈
              Set.Ioo
                (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e)
                (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f) ∧
         (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, false⟩ s) +
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) / 2 ∈
            connectedComponentIn
              ((-mapScalar phi A.originScalar) +ᵥ
                interior (closure (⋃ s : deformedCenterCarrierOn Tphi S,
                axis.coord s +ᵥ {x : ℝ | FilledSliceChains.slicePoint axis
                  (axis.transverseCoord (D.planarHomeomorph
                    (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
                      D.deformedRegion.openCarrier})))
              ((IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e +
                IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f) / 2)) := by
  obtain ⟨e, f, he, hf, hcomponent⟩ := boundedComponent_targetComponent_eq E J
  refine ⟨e, f, he, hf, hcomponent, ?_⟩
  intro i s hsourceMid
  let e₀ : IndexedSectionEndpoint A S := IndexedSectionEndpoint.mk ⟨i, false⟩ s
  let f₀ : IndexedSectionEndpoint A S := IndexedSectionEndpoint.mk ⟨i, true⟩ s
  have hsourceOrder : e₀.sourceValue < f₀.sourceValue := by
    dsimp [e₀, f₀, IndexedSectionEndpoint.sourceValue, SectionEndpointLabel.rawValue]
    linarith [A.raw.presentation.lt i]
  have hsourceMidInterval :
      (e₀.sourceValue + f₀.sourceValue) / 2 ∈ Set.Ioo e₀.sourceValue f₀.sourceValue := by
    constructor <;> linarith
  have hsourceMeet :
      (Set.Ioo (A.raw.presentation.left i + axis.coord s.1.1 - A.origin)
        (A.raw.presentation.right i + axis.coord s.1.1 - A.origin) ∩
        Set.Ioo J.left J.right).Nonempty := by
    refine ⟨(e₀.sourceValue + f₀.sourceValue) / 2, ?_, hsourceMid⟩
    simpa [e₀, f₀, IndexedSectionEndpoint.sourceValue, SectionEndpointLabel.rawValue]
      using hsourceMidInterval
  have hs : s.1.1 ∈ Subtype.val '' S := ⟨s.1, s.2, rfl⟩
  have hsourceInterval := occupiedComponent_interval_subset A J
    (s := s.1.1) hs i hsourceMeet
  have hsourceSubset : Set.Ioo e₀.sourceValue f₀.sourceValue ⊆ Set.Ioo J.left J.right := by
    simpa [e₀, f₀, IndexedSectionEndpoint.sourceValue, SectionEndpointLabel.rawValue]
      using hsourceInterval
  have hsourceLeftMem : e₀.sourceValue ∈ closure (Set.Ioo e₀.sourceValue f₀.sourceValue) := by
    rw [closure_Ioo hsourceOrder.ne]
    exact ⟨le_rfl, hsourceOrder.le⟩
  have hsourceRightMem : f₀.sourceValue ∈ closure (Set.Ioo e₀.sourceValue f₀.sourceValue) := by
    rw [closure_Ioo hsourceOrder.ne]
    exact ⟨hsourceOrder.le, le_rfl⟩
  have hclosureSubset :
      closure (Set.Ioo e₀.sourceValue f₀.sourceValue) ⊆ closure (Set.Ioo J.left J.right) :=
    closure_mono hsourceSubset
  have hsourceLeftIcc : e₀.sourceValue ∈ Set.Icc J.left J.right := by
    have hmem := hclosureSubset hsourceLeftMem
    rwa [closure_Ioo J.ordered.ne] at hmem
  have hsourceRightIcc : f₀.sourceValue ∈ Set.Icc J.left J.right := by
    have hmem := hclosureSubset hsourceRightMem
    rwa [closure_Ioo J.ordered.ne] at hmem
  have hsourceLeftOrder : e.sourceValue ≤ e₀.sourceValue := by
    rw [he]
    exact hsourceLeftIcc.1
  have hsourceRightOrder : f₀.sourceValue ≤ f.sourceValue := by
    rw [hf]
    exact hsourceRightIcc.2
  have htargetLeftOrder :
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ≤
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₀ :=
    (E.weakOrder_iff e e₀).mp hsourceLeftOrder
  have htargetRightOrder :
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f₀ ≤
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f :=
    (E.weakOrder_iff f₀ f).mp hsourceRightOrder
  have htargetIntervalOrder :
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₀ <
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f₀ :=
    (allEndpointWeakOrderTransport_endpoint_lt_iff E e₀ f₀).mp hsourceOrder
  have htargetMidpoint :
      (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₀ +
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f₀) / 2 ∈
          Set.Ioo
            (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e)
            (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f) := by
    constructor <;> linarith
  refine ⟨htargetMidpoint, ?_⟩
  rw [hcomponent]
  exact htargetMidpoint

private theorem intervalFamily_raw_subset_regularized
    {ι : Type*} (l r : ι → ℝ) :
    (⋃ i, Set.Ioo (l i) (r i)) ⊆
      interior (closure (⋃ i, Set.Ioo (l i) (r i))) := by
  have hopen : IsOpen (⋃ i, Set.Ioo (l i) (r i)) :=
    isOpen_iUnion fun i => isOpen_Ioo
  have hsub : (⋃ i, Set.Ioo (l i) (r i)) ⊆
      closure (⋃ i, Set.Ioo (l i) (r i)) := subset_closure
  exact interior_maximal hsub hopen

private theorem intervalFamily_component_endpointCluster_bddAbove_iff
    {ι : Type*} (l r : ι → ℝ) (hlt : ∀ i, l i < r i) (x : ℝ) :
  BddAbove
        (connectedComponentIn
          (interior (closure (⋃ i, Set.Ioo (l i) (r i)))) x) ↔
      BddAbove
        {z : ℝ | ∃ i,
          ((l i + r i) / 2 ∈ connectedComponentIn
            (interior (closure (⋃ i, Set.Ioo (l i) (r i)))) x) ∧
          (z = l i ∨ z = r i)} := by
  let U := interior (closure (⋃ i, Set.Ioo (l i) (r i)))
  let C := connectedComponentIn U x
  let E := {z : ℝ | ∃ i, ((l i + r i) / 2 ∈ C) ∧ (z = l i ∨ z = r i)}
  have hraw : (⋃ i, Set.Ioo (l i) (r i)) ⊆ U :=
    intervalFamily_raw_subset_regularized l r
  have hmid : ∀ i, (l i + r i) / 2 ∈ Set.Ioo (l i) (r i) := by
    intro i
    constructor <;> linarith [hlt i]
  have hintervalComp : ∀ i, (l i + r i) / 2 ∈ C →
      Set.Ioo (l i) (r i) ⊆ C := by
    intro i himid
    change Set.Ioo (l i) (r i) ⊆ connectedComponentIn U x
    rw [connectedComponentIn_eq himid]
    exact isPreconnected_Ioo.subset_connectedComponentIn (hmid i)
      (fun y hy => hraw (Set.mem_iUnion.mpr ⟨i, hy⟩))
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro z hz
    rcases hz with ⟨i, himid, hz⟩
    have hrBound : r i ≤ M := by
      by_contra hnot
      have hMr : M < r i := lt_of_not_ge hnot
      have hlM : l i < M := lt_of_lt_of_le (hmid i).1 (hM himid)
      obtain ⟨y, hMy, hyr⟩ := exists_between hMr
      have hyIoo : y ∈ Set.Ioo (l i) (r i) := ⟨lt_trans hlM hMy, hyr⟩
      have hyC := hintervalComp i himid hyIoo
      exact (not_lt_of_ge (hM hyC)) hMy
    rcases hz with hz | hz
    · rw [hz]
      exact (hlt i).le.trans hrBound
    · rw [hz]
      exact hrBound
  · rintro ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro y hyC
    by_contra hyM
    have hMy : M < y := lt_of_not_ge hyM
    have hyU : y ∈ U := connectedComponentIn_subset U x hyC
    have hUopenNhds : U ∈ 𝓝 y := isOpen_interior.mem_nhds hyU
    have hIoiNhds : Set.Ioi M ∈ 𝓝 y := isOpen_Ioi.mem_nhds hMy
    have hboth : U ∩ Set.Ioi M ∈ 𝓝 y := inter_mem hUopenNhds hIoiNhds
    obtain ⟨a, b, hyab, hab⟩ :=
      (mem_nhds_iff_exists_Ioo_subset (a := y) (s := U ∩ Set.Ioi M)).mp hboth
    have hVsubU : Set.Ioo a b ⊆ U := fun z hz => (hab hz).1
    have hVcompAtY : Set.Ioo a b ⊆ connectedComponentIn U y :=
      isPreconnected_Ioo.subset_connectedComponentIn hyab hVsubU
    have hVcomp : Set.Ioo a b ⊆ C := by
      change Set.Ioo a b ⊆ connectedComponentIn U x
      rw [connectedComponentIn_eq hyC]
      exact hVcompAtY
    have hyClosure : y ∈ closure (⋃ i, Set.Ioo (l i) (r i)) := interior_subset hyU
    obtain ⟨z, hzV, hzRaw⟩ :=
      (mem_closure_iff.mp hyClosure) (Set.Ioo a b) isOpen_Ioo hyab
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzRaw
    have hmidCz : (l i + r i) / 2 ∈ connectedComponentIn U z :=
      isPreconnected_Ioo.subset_connectedComponentIn hzi
        (fun y hy => hraw (Set.mem_iUnion.mpr ⟨i, hy⟩)) (hmid i)
    have hmidC : (l i + r i) / 2 ∈ C := by
      change (l i + r i) / 2 ∈ connectedComponentIn U x
      rw [connectedComponentIn_eq (hVcomp hzV)]
      exact hmidCz
    have hrBound := hM ⟨i, hmidC, Or.inr rfl⟩
    have hzAbove : M < z := (hab hzV).2
    exact (not_lt_of_ge hrBound) (lt_trans hzAbove hzi.2)

private theorem intervalFamily_component_endpointCluster_bddBelow_iff
    {ι : Type*} (l r : ι → ℝ) (hlt : ∀ i, l i < r i) (x : ℝ) :
  BddBelow
        (connectedComponentIn
          (interior (closure (⋃ i, Set.Ioo (l i) (r i)))) x) ↔
      BddBelow
        {z : ℝ | ∃ i,
          ((l i + r i) / 2 ∈ connectedComponentIn
            (interior (closure (⋃ i, Set.Ioo (l i) (r i)))) x) ∧
          (z = l i ∨ z = r i)} := by
  let U := interior (closure (⋃ i, Set.Ioo (l i) (r i)))
  let C := connectedComponentIn U x
  let E := {z : ℝ | ∃ i, ((l i + r i) / 2 ∈ C) ∧ (z = l i ∨ z = r i)}
  have hraw : (⋃ i, Set.Ioo (l i) (r i)) ⊆ U :=
    intervalFamily_raw_subset_regularized l r
  have hmid : ∀ i, (l i + r i) / 2 ∈ Set.Ioo (l i) (r i) := by
    intro i
    constructor <;> linarith [hlt i]
  have hintervalComp : ∀ i, (l i + r i) / 2 ∈ C →
      Set.Ioo (l i) (r i) ⊆ C := by
    intro i himid
    change Set.Ioo (l i) (r i) ⊆ connectedComponentIn U x
    rw [connectedComponentIn_eq himid]
    exact isPreconnected_Ioo.subset_connectedComponentIn (hmid i)
      (fun y hy => hraw (Set.mem_iUnion.mpr ⟨i, hy⟩))
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro z hz
    rcases hz with ⟨i, himid, hz⟩
    have hlBound : M ≤ l i := by
      by_contra hnot
      have hlM : l i < M := lt_of_not_ge hnot
      have hMm : M ≤ (l i + r i) / 2 := hM himid
      obtain ⟨y, hly, hyM⟩ := exists_between hlM
      have hyr : y < r i := lt_of_lt_of_le hyM (le_trans hMm (hmid i).2.le)
      have hyIoo : y ∈ Set.Ioo (l i) (r i) := ⟨hly, hyr⟩
      have hyC := hintervalComp i himid hyIoo
      exact (not_le_of_gt hyM) (hM hyC)
    rcases hz with hz | hz
    · rw [hz]
      exact hlBound
    · rw [hz]
      exact hlBound.trans (hlt i).le
  · rintro ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro y hyC
    by_contra hyM
    have hyM' : y < M := lt_of_not_ge hyM
    have hyU : y ∈ U := connectedComponentIn_subset U x hyC
    have hUopenNhds : U ∈ 𝓝 y := isOpen_interior.mem_nhds hyU
    have hIioNhds : Set.Iio M ∈ 𝓝 y := isOpen_Iio.mem_nhds hyM'
    have hboth : U ∩ Set.Iio M ∈ 𝓝 y := inter_mem hUopenNhds hIioNhds
    obtain ⟨a, b, hyab, hab⟩ :=
      (mem_nhds_iff_exists_Ioo_subset (a := y) (s := U ∩ Set.Iio M)).mp hboth
    have hVsubU : Set.Ioo a b ⊆ U := fun z hz => (hab hz).1
    have hVcompAtY : Set.Ioo a b ⊆ connectedComponentIn U y :=
      isPreconnected_Ioo.subset_connectedComponentIn hyab hVsubU
    have hVcomp : Set.Ioo a b ⊆ C := by
      change Set.Ioo a b ⊆ connectedComponentIn U x
      rw [connectedComponentIn_eq hyC]
      exact hVcompAtY
    have hyClosure : y ∈ closure (⋃ i, Set.Ioo (l i) (r i)) := interior_subset hyU
    obtain ⟨z, hzV, hzRaw⟩ :=
      (mem_closure_iff.mp hyClosure) (Set.Ioo a b) isOpen_Ioo hyab
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzRaw
    have hmidCz : (l i + r i) / 2 ∈ connectedComponentIn U z :=
      isPreconnected_Ioo.subset_connectedComponentIn hzi
        (fun y hy => hraw (Set.mem_iUnion.mpr ⟨i, hy⟩)) (hmid i)
    have hmidC : (l i + r i) / 2 ∈ C := by
      change (l i + r i) / 2 ∈ connectedComponentIn U x
      rw [connectedComponentIn_eq (hVcomp hzV)]
      exact hmidCz
    have hlBound := hM ⟨i, hmidC, Or.inl rfl⟩
    have hzBelow : z < M := (hab hzV).2
    exact (not_lt_of_ge hlBound) (lt_trans hzi.1 hzBelow)

private theorem locallyFinite_endpoint_subset_bddAbove_has_max
    (endpoint A : Set ℝ)
    (hlocal : ∀ a b, (endpoint ∩ Set.Icc a b).Finite)
    (hsub : A ⊆ endpoint) (hne : A.Nonempty) (hbound : BddAbove A) :
    ∃ m ∈ A, ∀ z ∈ A, z ≤ m := by
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨M, hM⟩ := hbound
  have hz₀M : z₀ ≤ M := hM hz₀
  let F := A ∩ Set.Icc z₀ M
  have hFfinite : F.Finite := (hlocal z₀ M).subset fun z hz =>
    ⟨hsub hz.1, hz.2⟩
  have hFne : F.Nonempty := ⟨z₀, hz₀, le_rfl, hz₀M⟩
  obtain ⟨m, hm, hmax⟩ := Set.exists_max_image F id hFfinite hFne
  refine ⟨m, hm.1, ?_⟩
  intro z hz
  by_cases hzz₀ : z < z₀
  · exact (le_of_lt hzz₀).trans hm.2.1
  · have hz₀z : z₀ ≤ z := le_of_not_gt hzz₀
    have hzM : z ≤ M := hM hz
    have hzF : z ∈ F := ⟨hz, hz₀z, hzM⟩
    simpa using hmax z hzF

private theorem locallyFinite_endpoint_subset_bddBelow_has_min
    (endpoint A : Set ℝ)
    (hlocal : ∀ a b, (endpoint ∩ Set.Icc a b).Finite)
    (hsub : A ⊆ endpoint) (hne : A.Nonempty) (hbound : BddBelow A) :
    ∃ m ∈ A, ∀ z ∈ A, m ≤ z := by
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨M, hM⟩ := hbound
  have hMz₀ : M ≤ z₀ := hM hz₀
  let F := A ∩ Set.Icc M z₀
  have hFfinite : F.Finite := (hlocal M z₀).subset fun z hz =>
    ⟨hsub hz.1, hz.2⟩
  have hFne : F.Nonempty := ⟨z₀, hz₀, hMz₀, le_rfl⟩
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image F id hFfinite hFne
  refine ⟨m, hm.1, ?_⟩
  intro z hz
  by_cases hz₀z : z₀ < z
  · exact hm.2.2.trans (le_of_lt hz₀z)
  · have hz₀ : z ≤ z₀ := le_of_not_gt hz₀z
    have hMz : M ≤ z := hM hz
    have hzF : z ∈ F := ⟨hz, hMz, hz₀⟩
    simpa using hmin z hzF

private theorem frontierGap_hole_or_boundedComponent
    (U : Set ℝ) (hU : IsOpen U) {a b : ℝ} (hab : a < b)
    (ha : a ∈ frontier U) (hb : b ∈ frontier U)
    (hno : ∀ x ∈ Set.Ioo a b, x ∉ frontier U) :
    (Set.Ioo a b ∩ U = ∅) ∨
      (connectedComponentIn U ((a + b) / 2) = Set.Ioo a b ∧
        (a + b) / 2 ∈ U) := by
  have hcover : Set.Ioo a b ⊆ U ∪ (closure U)ᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · right
      by_cases hxClosure : x ∈ closure U
      · have hxFrontier : x ∈ frontier U := by
          rw [hU.frontier_eq]
          exact ⟨hxClosure, hxU⟩
        exact False.elim ((hno x hx) hxFrontier)
      · exact hxClosure
  have hdisjoint : Set.Ioo a b ∩ (U ∩ (closure U)ᶜ) = ∅ := by
    ext x
    constructor
    · rintro ⟨hx, hxU, hxNotClosure⟩
      exact (hxNotClosure (subset_closure hxU)).elim
    · intro hx
      exact hx.elim
  have hchoice := (isPreconnected_iff_subset_of_disjoint.mp isPreconnected_Ioo)
    U (closure U)ᶜ hU isClosed_closure.isOpen_compl hcover hdisjoint
  rcases hchoice with hoccupied | houtside
  · have haNotU : a ∉ U := by
      intro haU
      rw [hU.frontier_eq] at ha
      exact ha.2 haU
    have hbNotU : b ∉ U := by
      intro hbU
      rw [hU.frontier_eq] at hb
      exact hb.2 hbU
    have hmidLeft : a < (a + b) / 2 := by linarith
    have hmidRight : (a + b) / 2 < b := by linarith
    have hmidIoo : (a + b) / 2 ∈ Set.Ioo a b := ⟨hmidLeft, hmidRight⟩
    have hmidU : (a + b) / 2 ∈ U := hoccupied hmidIoo
    have hmidComponent : (a + b) / 2 ∈ connectedComponentIn U ((a + b) / 2) :=
      mem_connectedComponentIn hmidU
    have hcomponentPre :
        IsPreconnected (connectedComponentIn U ((a + b) / 2)) :=
      isPreconnected_connectedComponentIn
    have hcomponentSubset : connectedComponentIn U ((a + b) / 2) ⊆ U :=
      connectedComponentIn_subset U ((a + b) / 2)
    have hintervalSubset : Set.Ioo a b ⊆
        connectedComponentIn U ((a + b) / 2) :=
      isPreconnected_Ioo.subset_connectedComponentIn hmidIoo hoccupied
    have hcomponentInterval : connectedComponentIn U ((a + b) / 2) ⊆ Set.Ioo a b := by
      intro y hy
      by_cases hay : a < y
      · by_cases hyb : y < b
        · exact ⟨hay, hyb⟩
        · have hby : b ≤ y := le_of_not_gt hyb
          have hsegment := hcomponentPre.Icc_subset hmidComponent hy
          have hbIcc : b ∈ Set.Icc ((a + b) / 2) y := ⟨le_of_lt hmidRight, hby⟩
          exact (hbNotU (hcomponentSubset (hsegment hbIcc))).elim
      · have hya : y ≤ a := le_of_not_gt hay
        have hsegment := hcomponentPre.Icc_subset hy hmidComponent
        have haIcc : a ∈ Set.Icc y ((a + b) / 2) := ⟨hya, le_of_lt hmidLeft⟩
        exact (haNotU (hcomponentSubset (hsegment haIcc))).elim
    exact Or.inr ⟨Set.Subset.antisymm hcomponentInterval hintervalSubset, hmidU⟩
  · apply Or.inl
    ext x
    constructor
    · rintro ⟨hx, hxU⟩
      exact houtside hx (subset_closure hxU)
    · intro hx
      exact hx.elim

private theorem orderedLocallyFiniteImages_bddAbove_iff
    {ι : Type*} (v w : ι → ℝ)
    (horder : ∀ i j, v i ≤ v j ↔ w i ≤ w j)
    (hvLocal : ∀ a b, ({x : ℝ | ∃ i, v i = x} ∩ Set.Icc a b).Finite)
    (hwLocal : ∀ a b, ({x : ℝ | ∃ i, w i = x} ∩ Set.Icc a b).Finite)
    (I : Set ι) : BddAbove (v '' I) ↔ BddAbove (w '' I) := by
  by_cases hI : I.Nonempty
  · have hvSub : v '' I ⊆ {x : ℝ | ∃ i, v i = x} := by
      rintro x ⟨i, _hi, rfl⟩
      exact ⟨i, rfl⟩
    have hwSub : w '' I ⊆ {x : ℝ | ∃ i, w i = x} := by
      rintro x ⟨i, _hi, rfl⟩
      exact ⟨i, rfl⟩
    constructor
    · intro hvBound
      obtain ⟨m, hm, hmax⟩ := locallyFinite_endpoint_subset_bddAbove_has_max
        {x : ℝ | ∃ i, v i = x} (v '' I) hvLocal hvSub (hI.image v) hvBound
      obtain ⟨i₀, _hi₀, rfl⟩ := hm
      refine ⟨w i₀, ?_⟩
      rintro y ⟨i, hi, rfl⟩
      exact (horder i i₀).mp (hmax (v i) (Set.mem_image_of_mem v hi))
    · intro hwBound
      obtain ⟨m, hm, hmax⟩ := locallyFinite_endpoint_subset_bddAbove_has_max
        {x : ℝ | ∃ i, w i = x} (w '' I) hwLocal hwSub (hI.image w) hwBound
      obtain ⟨i₀, _hi₀, rfl⟩ := hm
      refine ⟨v i₀, ?_⟩
      rintro y ⟨i, hi, rfl⟩
      exact (horder i i₀).mpr (hmax (w i) (Set.mem_image_of_mem w hi))
  · have hEmpty : I = ∅ := Set.not_nonempty_iff_eq_empty.mp hI
    simp [hEmpty]

private theorem orderedLocallyFiniteImages_bddBelow_iff
    {ι : Type*} (v w : ι → ℝ)
    (horder : ∀ i j, v i ≤ v j ↔ w i ≤ w j)
    (hvLocal : ∀ a b, ({x : ℝ | ∃ i, v i = x} ∩ Set.Icc a b).Finite)
    (hwLocal : ∀ a b, ({x : ℝ | ∃ i, w i = x} ∩ Set.Icc a b).Finite)
    (I : Set ι) : BddBelow (v '' I) ↔ BddBelow (w '' I) := by
  by_cases hI : I.Nonempty
  · have hvSub : v '' I ⊆ {x : ℝ | ∃ i, v i = x} := by
      rintro x ⟨i, _hi, rfl⟩
      exact ⟨i, rfl⟩
    have hwSub : w '' I ⊆ {x : ℝ | ∃ i, w i = x} := by
      rintro x ⟨i, _hi, rfl⟩
      exact ⟨i, rfl⟩
    constructor
    · intro hvBound
      obtain ⟨m, hm, hmin⟩ := locallyFinite_endpoint_subset_bddBelow_has_min
        {x : ℝ | ∃ i, v i = x} (v '' I) hvLocal hvSub (hI.image v) hvBound
      obtain ⟨i₀, _hi₀, rfl⟩ := hm
      refine ⟨w i₀, ?_⟩
      rintro y ⟨i, hi, rfl⟩
      exact (horder i₀ i).mp (hmin (v i) (Set.mem_image_of_mem v hi))
    · intro hwBound
      obtain ⟨m, hm, hmin⟩ := locallyFinite_endpoint_subset_bddBelow_has_min
        {x : ℝ | ∃ i, w i = x} (w '' I) hwLocal hwSub (hI.image w) hwBound
      obtain ⟨i₀, _hi₀, rfl⟩ := hm
      refine ⟨v i₀, ?_⟩
      rintro y ⟨i, hi, rfl⟩
      exact (horder i₀ i).mpr (hmin (w i) (Set.mem_image_of_mem w hi))
  · have hEmpty : I = ∅ := Set.not_nonempty_iff_eq_empty.mp hI
    simp [hEmpty]

private theorem orderedIntervalComponentEquiv_bounds
    {ι κ : Type*} (v w : ι → ℝ) (left right : κ → ι)
    (horder : ∀ i j, v i ≤ v j ↔ w i ≤ w j)
    (hvLocal : ∀ a b, ({x : ℝ | ∃ i, v i = x} ∩ Set.Icc a b).Finite)
    (hwLocal : ∀ a b, ({x : ℝ | ∃ i, w i = x} ∩ Set.Icc a b).Finite)
    (hlt : ∀ i, v (left i) < v (right i))
    (hlt' : ∀ i, w (left i) < w (right i)) :
    let U := interior (closure (⋃ i, Set.Ioo (v (left i)) (v (right i))))
    let V := interior (closure (⋃ i, Set.Ioo (w (left i)) (w (right i))))
    ∀ F : ↥{J : Set ℝ | ∃ x ∈ U, J = connectedComponentIn U x} ≃
        ↥{J : Set ℝ | ∃ x ∈ V, J = connectedComponentIn V x},
      (∀ J i, (v (left i) + v (right i)) / 2 ∈ J.1 ↔
        (w (left i) + w (right i)) / 2 ∈ (F J).1) →
      ∀ J, (BddAbove J.1 ↔ BddAbove (F J).1) ∧
        (BddBelow J.1 ↔ BddBelow (F J).1) := by
  dsimp only
  let U := interior (closure (⋃ i, Set.Ioo (v (left i)) (v (right i))))
  let V := interior (closure (⋃ i, Set.Ioo (w (left i)) (w (right i))))
  intro F hmid J
  obtain ⟨x, _hx, hJ⟩ := J.2
  obtain ⟨y, _hy, hK⟩ := (F J).2
  let I : Set ι := {e | ∃ i,
    (v (left i) + v (right i)) / 2 ∈ J.1 ∧ (e = left i ∨ e = right i)}
  let sourceCluster : Set ℝ := {z | ∃ i,
    (v (left i) + v (right i)) / 2 ∈ J.1 ∧
      (z = v (left i) ∨ z = v (right i))}
  let targetCluster : Set ℝ := {z | ∃ i,
    (w (left i) + w (right i)) / 2 ∈ (F J).1 ∧
      (z = w (left i) ∨ z = w (right i))}
  have hsourceImage : sourceCluster = v '' I := by
    ext z
    constructor
    · rintro ⟨i, hi, hz | hz⟩
      · exact ⟨left i, ⟨i, hi, Or.inl rfl⟩, hz.symm⟩
      · exact ⟨right i, ⟨i, hi, Or.inr rfl⟩, hz.symm⟩
    · rintro ⟨e, ⟨i, hi, he | he⟩, hz⟩
      · refine ⟨i, hi, Or.inl ?_⟩
        rw [← hz, he]
      · refine ⟨i, hi, Or.inr ?_⟩
        rw [← hz, he]
  have htargetImage : targetCluster = w '' I := by
    ext z
    constructor
    · rintro ⟨i, hi, hz | hz⟩
      · exact ⟨left i, ⟨i, (hmid J i).mpr hi, Or.inl rfl⟩, hz.symm⟩
      · exact ⟨right i, ⟨i, (hmid J i).mpr hi, Or.inr rfl⟩, hz.symm⟩
    · rintro ⟨e, ⟨i, hi, he | he⟩, hz⟩
      · refine ⟨i, (hmid J i).mp hi, Or.inl ?_⟩
        rw [← hz, he]
      · refine ⟨i, (hmid J i).mp hi, Or.inr ?_⟩
        rw [← hz, he]
  have hsourceAbove : BddAbove J.1 ↔ BddAbove sourceCluster := by
    simpa only [sourceCluster, hJ, U] using
      intervalFamily_component_endpointCluster_bddAbove_iff
        (fun i => v (left i)) (fun i => v (right i)) hlt x
  have htargetAbove : BddAbove (F J).1 ↔ BddAbove targetCluster := by
    simpa only [targetCluster, hK, V] using
      intervalFamily_component_endpointCluster_bddAbove_iff
        (fun i => w (left i)) (fun i => w (right i)) hlt' y
  have hsourceBelow : BddBelow J.1 ↔ BddBelow sourceCluster := by
    simpa only [sourceCluster, hJ, U] using
      intervalFamily_component_endpointCluster_bddBelow_iff
        (fun i => v (left i)) (fun i => v (right i)) hlt x
  have htargetBelow : BddBelow (F J).1 ↔ BddBelow targetCluster := by
    simpa only [targetCluster, hK, V] using
      intervalFamily_component_endpointCluster_bddBelow_iff
        (fun i => w (left i)) (fun i => w (right i)) hlt' y
  constructor
  · apply hsourceAbove.trans
    apply Iff.trans _ htargetAbove.symm
    rw [hsourceImage, htargetImage]
    exact orderedLocallyFiniteImages_bddAbove_iff v w horder hvLocal hwLocal I
  · apply hsourceBelow.trans
    apply Iff.trans _ htargetBelow.symm
    rw [hsourceImage, htargetImage]
    exact orderedLocallyFiniteImages_bddBelow_iff v w horder hvLocal hwLocal I

/-!
Boundedness consumers of the open real-component classification.
Insert inside `Tiling.AxisParallel.Terminal` after
`connectedComponentIn_open_classification`.
-/

private theorem connectedComponentIn_Ioi_iff_boundedness
    {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) :
    (∃ a, connectedComponentIn U x = Set.Ioi a) ↔
      BddBelow (connectedComponentIn U x) ∧ ¬ BddAbove (connectedComponentIn U x) := by
  constructor
  · rintro ⟨a, hEq⟩
    constructor
    · rw [hEq]
      exact bddBelow_Ioi (a := a)
    · rw [hEq]
      exact not_bddAbove_Ioi (a := a)
  · rintro ⟨hbelow, hnotabove⟩
    rcases connectedComponentIn_open_classification hU hx with
      ⟨a, b, hab, hEq⟩ | ⟨a, hEq⟩ | ⟨b, hEq⟩ | hEq
    · have habove : BddAbove (connectedComponentIn U x) := by
        rw [hEq]
        exact bddAbove_Ioo (a := a) (b := b)
      exact (hnotabove habove).elim
    · exact ⟨a, hEq⟩
    · have hnotbelow : ¬ BddBelow (connectedComponentIn U x) := by
        rw [hEq]
        exact not_bddBelow_Iio (a := b)
      exact (hnotbelow hbelow).elim
    · have hnotbelow : ¬ BddBelow (connectedComponentIn U x) := by
        rw [hEq]
        exact not_bddBelow_univ
      exact (hnotbelow hbelow).elim

private theorem connectedComponentIn_Iio_iff_boundedness
    {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) :
    (∃ b, connectedComponentIn U x = Set.Iio b) ↔
      ¬ BddBelow (connectedComponentIn U x) ∧ BddAbove (connectedComponentIn U x) := by
  constructor
  · rintro ⟨b, hEq⟩
    constructor
    · rw [hEq]
      exact not_bddBelow_Iio (a := b)
    · rw [hEq]
      exact bddAbove_Iio (a := b)
  · rintro ⟨hnotbelow, habove⟩
    rcases connectedComponentIn_open_classification hU hx with
      ⟨a, b, hab, hEq⟩ | ⟨a, hEq⟩ | ⟨b, hEq⟩ | hEq
    · have hbelow : BddBelow (connectedComponentIn U x) := by
        rw [hEq]
        exact ⟨a, fun y hy => le_of_lt hy.1⟩
      exact (hnotbelow hbelow).elim
    · have hnotabove : ¬ BddAbove (connectedComponentIn U x) := by
        rw [hEq]
        exact not_bddAbove_Ioi (a := a)
      exact (hnotabove habove).elim
    · exact ⟨b, hEq⟩
    · have hnotabove : ¬ BddAbove (connectedComponentIn U x) := by
        rw [hEq]
        exact not_bddAbove_univ
      exact (hnotabove habove).elim

private theorem connectedComponentIn_univ_iff_unbounded
    {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) :
    connectedComponentIn U x = Set.univ ↔
      ¬ BddBelow (connectedComponentIn U x) ∧ ¬ BddAbove (connectedComponentIn U x) := by
  constructor
  · intro hEq
    constructor
    · rw [hEq]
      exact not_bddBelow_univ
    · rw [hEq]
      exact not_bddAbove_univ
  · rintro ⟨hnotbelow, hnotabove⟩
    rcases connectedComponentIn_open_classification hU hx with
      ⟨a, b, hab, hEq⟩ | ⟨a, hEq⟩ | ⟨b, hEq⟩ | hEq
    · have hbelow : BddBelow (connectedComponentIn U x) := by
        rw [hEq]
        exact ⟨a, fun y hy => le_of_lt hy.1⟩
      exact (hnotbelow hbelow).elim
    · have hbelow : BddBelow (connectedComponentIn U x) := by
        rw [hEq]
        exact bddBelow_Ioi (a := a)
      exact (hnotbelow hbelow).elim
    · have habove : BddAbove (connectedComponentIn U x) := by
        rw [hEq]
        exact bddAbove_Iio (a := b)
      exact (hnotabove habove).elim
    · exact hEq

/-!
Pure-real reachability by consecutive values in a locally finite endpoint set.
Insert inside `Tiling.AxisParallel.Terminal`; this adds no relation wrapper.
-/

private theorem locallyFiniteReal_consecutiveEndpoint_reflTransGen
    (E : Set ℝ) (hlocal : ∀ a b : ℝ, (E ∩ Set.Icc a b).Finite)
    {a b : ℝ} (ha : a ∈ E) (hb : b ∈ E) :
    Relation.ReflTransGen
      (fun u v : ℝ =>
        u ∈ E ∧ v ∈ E ∧
          ((u < v ∧ ∀ z, z ∈ E → ¬ (u < z ∧ z < v)) ∨
            (v < u ∧ ∀ z, z ∈ E → ¬ (v < z ∧ z < u))))
      a b := by
  classical
  let α := {x : ℝ // x ∈ E}
  have hfiniteIcc : ∀ x y : α, (Set.Icc x y).Finite := by
    intro x y
    apply Set.Finite.of_injOn (f := fun z : α => (z : ℝ))
      (s := Set.Icc x y) (t := E ∩ Set.Icc (x : ℝ) (y : ℝ))
    · intro z hz
      exact ⟨z.2, hz.1, hz.2⟩
    · intro z hz w hw hzw
      exact Subtype.ext hzw
    · exact hlocal (x : ℝ) (y : ℝ)
  let hlf : LocallyFiniteOrder α := LocallyFiniteOrder.ofFiniteIcc hfiniteIcc
  let hs : SuccOrder α := @LinearLocallyFiniteOrder.succOrder α inferInstance hlf
  let harch : IsSuccArchimedean α := by
    let : LocallyFiniteOrder α := hlf
    let : SuccOrder α := hs
    infer_instance
  let Adj : α → α → Prop := fun x y => x ⋖ y ∨ y ⋖ x
  let R : ℝ → ℝ → Prop := fun u v =>
    u ∈ E ∧ v ∈ E ∧
      ((u < v ∧ ∀ z, z ∈ E → ¬ (u < z ∧ z < v)) ∨
        (v < u ∧ ∀ z, z ∈ E → ¬ (v < z ∧ z < u)))
  have hpath : Relation.ReflTransGen Adj (⟨a, ha⟩ : α) ⟨b, hb⟩ := by
    apply @reflTransGen_of_succ α inferInstance hs harch Adj
    · intro i hi
      left
      apply @Order.covBy_succ_of_not_isMax α inferInstance hs
      exact not_isMax_iff.mpr ⟨⟨b, hb⟩, hi.2⟩
    · intro i hi
      right
      apply @Order.covBy_succ_of_not_isMax α inferInstance hs
      exact not_isMax_iff.mpr ⟨⟨a, ha⟩, hi.2⟩
  have hmap : ∀ x y : α, Adj x y → R (x : ℝ) (y : ℝ) := by
    intro x y hxy
    rcases hxy with hxy | hyx
    · rcases hxy with ⟨hxy, hno⟩
      exact ⟨x.2, y.2, Or.inl ⟨hxy, fun z hz hzbetween =>
        hno (c := (⟨z, hz⟩ : α)) hzbetween.1 hzbetween.2⟩⟩
    · rcases hyx with ⟨hyx, hno⟩
      exact ⟨x.2, y.2, Or.inr ⟨hyx, fun z hz hzbetween =>
        hno (c := (⟨z, hz⟩ : α)) hzbetween.1 hzbetween.2⟩⟩
  change Relation.ReflTransGen R a b
  exact hpath.lift Subtype.val (fun x y hxy => hmap x y hxy)

private theorem allEndpointWeakOrderTransport_componentEquiv
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A) :
    let U := interior (closure (A.carrier + axis.coord '' (Subtype.val '' S)))
    let V := (-mapScalar phi A.originScalar) +ᵥ
      interior (closure (⋃ s : deformedCenterCarrierOn Tphi S,
        axis.coord s +ᵥ {x : ℝ | FilledSliceChains.slicePoint axis
          (axis.transverseCoord (D.planarHomeomorph
            (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
              D.deformedRegion.openCarrier}))
    ∃ F : ↥{J : Set ℝ | ∃ x ∈ U, J = connectedComponentIn U x} ≃
        ↥{J : Set ℝ | ∃ x ∈ V, J = connectedComponentIn V x},
      (∀ J (i : Fin A.raw.presentation.n) (s : S),
        (((IndexedSectionEndpoint.mk ⟨i, false⟩ s).sourceValue +
            (IndexedSectionEndpoint.mk ⟨i, true⟩ s).sourceValue) / 2 ∈ J.1) ↔
        ((IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, false⟩ s) +
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) / 2 ∈ (F J).1)) ∧
      (∀ J, (BddAbove J.1 ↔ BddAbove (F J).1) ∧
        (BddBelow J.1 ↔ BddBelow (F J).1)) := by
  let P := Fin A.raw.presentation.n × S
  let v : IndexedSectionEndpoint A S → ℝ := fun e => e.sourceValue
  let w : IndexedSectionEndpoint A S → ℝ := fun e =>
    IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e
  let left : P → IndexedSectionEndpoint A S :=
    fun p => IndexedSectionEndpoint.mk ⟨p.1, false⟩ p.2
  let right : P → IndexedSectionEndpoint A S :=
    fun p => IndexedSectionEndpoint.mk ⟨p.1, true⟩ p.2
  let l : P → ℝ := fun p => v (left p)
  let r : P → ℝ := fun p => v (right p)
  let l' : P → ℝ := fun p => w (left p)
  let r' : P → ℝ := fun p => w (right p)
  have hlt (p : P) : l p < r p := by
    dsimp [l, r, v, left, right, IndexedSectionEndpoint.sourceValue,
      SectionEndpointLabel.rawValue]
    linarith [A.raw.presentation.lt p.1]
  have hlt' (p : P) : l' p < r' p :=
    (allEndpointWeakOrderTransport_endpoint_lt_iff E (left p) (right p)).mp (hlt p)
  have hsourceUnion : (⋃ p : P, Set.Ioo (l p) (r p)) =
      ⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
        Set.Ioo ((IndexedSectionEndpoint.mk ⟨i, false⟩ s).sourceValue)
          ((IndexedSectionEndpoint.mk ⟨i, true⟩ s).sourceValue) := by
    ext x
    simp [P, l, r, v, left, right]
  have htargetUnion : (⋃ p : P, Set.Ioo (l' p) (r' p)) =
      ⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
        Set.Ioo
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, false⟩ s))
          (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
            (IndexedSectionEndpoint.mk ⟨i, true⟩ s)) := by
    ext x
    simp [P, l', r', w, left, right]
  have hrelation (p q : P) :
      connectedComponentIn (interior (closure (⋃ k, Set.Ioo (l k) (r k))))
          ((l p + r p) / 2) =
        connectedComponentIn (interior (closure (⋃ k, Set.Ioo (l k) (r k))))
          ((l q + r q) / 2) ↔
      connectedComponentIn (interior (closure (⋃ k, Set.Ioo (l' k) (r' k))))
          ((l' p + r' p) / 2) =
        connectedComponentIn (interior (closure (⋃ k, Set.Ioo (l' k) (r' k))))
          ((l' q + r' q) / 2) := by
    rw [hsourceUnion, htargetUnion]
    exact endpointIntervalMidpoint_sameComponent_iff E p.1 q.1 p.2 q.2
  obtain ⟨F, hmid⟩ := regularizedIntervalComponents_equiv_of_midpointRelation
    l r l' r' hlt hlt' hrelation
  have hbounds := orderedIntervalComponentEquiv_bounds v w left right
    E.weakOrder_iff E.sourceValues_locallyFinite E.targetValues_locallyFinite
    hlt hlt' F hmid
  have hsourceEq : interior (closure (A.carrier + axis.coord '' (Subtype.val '' S))) =
      interior (closure (⋃ p : P, Set.Ioo (l p) (r p))) := by
    rw [E.source_union_eq, hsourceUnion]
  have htargetEq : (-mapScalar phi A.originScalar) +ᵥ
      interior (closure (⋃ s : deformedCenterCarrierOn Tphi S,
        axis.coord s +ᵥ {x : ℝ | FilledSliceChains.slicePoint axis
          (axis.transverseCoord (D.planarHomeomorph
            (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
              D.deformedRegion.openCarrier})) =
      interior (closure (⋃ p : P, Set.Ioo (l' p) (r' p))) := by
    rw [E.target_union_eq, neg_vadd_vadd, htargetUnion]
  dsimp only
  rw [hsourceEq, htargetEq]
  refine ⟨F, ?_, hbounds⟩
  intro J i s
  exact hmid J (i, s)

private theorem componentCodeTransport
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {axis : Axis} {S : Set ↥C.centres} {A : NormalizedGenericSection C axis}
    (E : AllEndpointWeakOrderTransport phi D Tphi axis S A) :
    let source := interior (closure (A.carrier + axis.coord '' (Subtype.val '' S)))
    let target := (-mapScalar phi A.originScalar) +ᵥ
      interior (closure (⋃ s : deformedCenterCarrierOn Tphi S,
        axis.coord s +ᵥ {x : ℝ | FilledSliceChains.slicePoint axis
          (axis.transverseCoord (D.planarHomeomorph
            (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
              D.deformedRegion.openCarrier}))
    ∃ componentEquiv :
        ↥{J : Set ℝ | ∃ x ∈ source, J = connectedComponentIn source x} ≃
        ↥{J : Set ℝ | ∃ x ∈ target, J = connectedComponentIn target x},
      (∀ J, Bornology.IsBounded (J.1 : Set ℝ) ↔
        Bornology.IsBounded ((componentEquiv J).1 : Set ℝ)) ∧
      (∀ J, (∃ a, J.1 = Set.Ioi a) ↔
        ∃ a, (componentEquiv J).1 = Set.Ioi a) ∧
      (∀ J, (∃ b, J.1 = Set.Iio b) ↔
        ∃ b, (componentEquiv J).1 = Set.Iio b) ∧
      (∀ J, J.1 = Set.univ ↔ (componentEquiv J).1 = Set.univ) ∧
      (∀ (J : BoundedOccupiedTraceComponent A (Subtype.val '' S)) {R : ℝ}
          (code : ComponentMassCode A (Subtype.val '' S) J R),
        ∃ targetLeft targetRight : ℝ,
          (componentEquiv ⟨Set.Ioo J.left J.right,
            ⟨(J.left + J.right) / 2, J.midpoint_mem, J.component_eq.symm⟩⟩).1 =
              Set.Ioo targetLeft targetRight ∧
          targetRight - targetLeft =
          (code.bulk.card : ℝ) * mapScalar phi A.massScalar +
            code.correction.mappedValue phi) := by
  let U := interior (closure (A.carrier + axis.coord '' (Subtype.val '' S)))
  let V := (-mapScalar phi A.originScalar) +ᵥ
    interior (closure (⋃ s : deformedCenterCarrierOn Tphi S,
      axis.coord s +ᵥ {x : ℝ | FilledSliceChains.slicePoint axis
        (axis.transverseCoord (D.planarHomeomorph
          (FilledSliceChains.slicePoint axis A.raw.transverse 0))) x ∈
            D.deformedRegion.openCarrier}))
  have hUOpen : IsOpen U := isOpen_interior
  have hVOpen : IsOpen V := by
    dsimp [V]
    rw [E.target_union_eq, neg_vadd_vadd]
    exact isOpen_interior
  obtain ⟨F, hmid, hbounds⟩ := allEndpointWeakOrderTransport_componentEquiv E
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · intro J
    rw [isBounded_iff_bddBelow_bddAbove,
      isBounded_iff_bddBelow_bddAbove, (hbounds J).1, (hbounds J).2]
  · intro J
    obtain ⟨x, hx, hJ⟩ := J.2
    obtain ⟨y, hy, hK⟩ := (F J).2
    have hsource : (∃ a, J.1 = Set.Ioi a) ↔ BddBelow J.1 ∧ ¬ BddAbove J.1 := by
      simpa only [hJ] using connectedComponentIn_Ioi_iff_boundedness hUOpen hx
    have htarget : (∃ a, (F J).1 = Set.Ioi a) ↔
        BddBelow (F J).1 ∧ ¬ BddAbove (F J).1 := by
      simpa only [hK] using connectedComponentIn_Ioi_iff_boundedness hVOpen hy
    rw [hsource, htarget, (hbounds J).1, (hbounds J).2]
  · intro J
    obtain ⟨x, hx, hJ⟩ := J.2
    obtain ⟨y, hy, hK⟩ := (F J).2
    have hsource : (∃ b, J.1 = Set.Iio b) ↔ ¬ BddBelow J.1 ∧ BddAbove J.1 := by
      simpa only [hJ] using connectedComponentIn_Iio_iff_boundedness hUOpen hx
    have htarget : (∃ b, (F J).1 = Set.Iio b) ↔
        ¬ BddBelow (F J).1 ∧ BddAbove (F J).1 := by
      simpa only [hK] using connectedComponentIn_Iio_iff_boundedness hVOpen hy
    rw [hsource, htarget, (hbounds J).1, (hbounds J).2]
  · intro J
    obtain ⟨x, hx, hJ⟩ := J.2
    obtain ⟨y, hy, hK⟩ := (F J).2
    have hsource : J.1 = Set.univ ↔ ¬ BddBelow J.1 ∧ ¬ BddAbove J.1 := by
      simpa only [hJ] using connectedComponentIn_univ_iff_unbounded hUOpen hx
    have htarget : (F J).1 = Set.univ ↔
        ¬ BddBelow (F J).1 ∧ ¬ BddAbove (F J).1 := by
      simpa only [hK] using connectedComponentIn_univ_iff_unbounded hVOpen hy
    rw [hsource, htarget, (hbounds J).1, (hbounds J).2]
  · intro J R code
    let J₀ : ↥{K : Set ℝ | ∃ x ∈ U, K = connectedComponentIn U x} :=
      ⟨Set.Ioo J.left J.right,
        ⟨(J.left + J.right) / 2, J.midpoint_mem, J.component_eq.symm⟩⟩
    let P := Fin A.raw.presentation.n × S
    let l : P → ℝ := fun p => (IndexedSectionEndpoint.mk ⟨p.1, false⟩ p.2).sourceValue
    let r : P → ℝ := fun p => (IndexedSectionEndpoint.mk ⟨p.1, true⟩ p.2).sourceValue
    have hlt (p : P) : l p < r p := by
      dsimp [l, r, IndexedSectionEndpoint.sourceValue, SectionEndpointLabel.rawValue]
      linarith [A.raw.presentation.lt p.1]
    have hsourceUnion : (⋃ p : P, Set.Ioo (l p) (r p)) =
        ⋃ i : Fin A.raw.presentation.n, ⋃ s : S,
          Set.Ioo ((IndexedSectionEndpoint.mk ⟨i, false⟩ s).sourceValue)
            ((IndexedSectionEndpoint.mk ⟨i, true⟩ s).sourceValue) := by
      ext x
      simp [P, l, r]
    have hsourceEq : U = interior (closure (⋃ p : P, Set.Ioo (l p) (r p))) := by
      dsimp [U]
      rw [E.source_union_eq, hsourceUnion]
    have hmidU : (J.left + J.right) / 2 ∈
        interior (closure (⋃ p : P, Set.Ioo (l p) (r p))) := by
      rw [← hsourceEq]
      exact J.midpoint_mem
    obtain ⟨p, hp⟩ := regularizedIntervalComponent_contains_midpoint l r hlt hmidU
    have hsourceMid : (l p + r p) / 2 ∈ Set.Ioo J.left J.right := by
      rw [← hsourceEq, J.component_eq] at hp
      exact hp
    obtain ⟨e, f, he, hf, htargetComp, hboundedMid⟩ :=
      boundedComponent_targetInterval_midpoint_mem E J
    let le : ℝ := IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e
    let rf : ℝ := IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f
    let n : ℝ :=
      (IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨p.1, false⟩ p.2) +
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi)
          (IndexedSectionEndpoint.mk ⟨p.1, true⟩ p.2)) / 2
    have hnF : n ∈ (F J₀).1 := (hmid J₀ p.1 p.2).mp hsourceMid
    obtain ⟨y, _hy, hFJ⟩ := (F J₀).2
    have hnComp : n ∈ connectedComponentIn V y := by
      rw [← hFJ]
      exact hnF
    have hcompF : connectedComponentIn V n = (F J₀).1 :=
      (connectedComponentIn_eq hnComp).symm.trans hFJ.symm
    have hnBoundedComp : n ∈ connectedComponentIn V ((le + rf) / 2) := by
      exact (hboundedMid p.1 p.2 hsourceMid).2
    have htargetEq : (F J₀).1 = Set.Ioo le rf := by
      calc
        (F J₀).1 = connectedComponentIn V n := hcompF.symm
        _ = connectedComponentIn V ((le + rf) / 2) :=
          (connectedComponentIn_eq hnBoundedComp).symm
        _ = Set.Ioo le rf := htargetComp
    obtain ⟨g, h, hg, hh, _horder, hlength⟩ :=
      boundedOccupiedComponent_code_mappedEndpointLength E J code
    have heg : le = IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) g :=
      (allEndpointWeakOrderTransport_endpoint_eq_iff E e g).mp (he.trans hg.symm)
    have hfh : rf = IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) h :=
      (allEndpointWeakOrderTransport_endpoint_eq_iff E f h).mp (hf.trans hh.symm)
    refine ⟨le, rf, htargetEq, ?_⟩
    rw [heg, hfh]
    exact hlength

private theorem columnable_preApproximationControls
    {C : ApproximationContext.{0}} (hT : HasFLC C.centres) (axis : Axis)
    (hcol : ∃ Col, IsCenterColumn axis C.region Col) :
    ∃ (outerA : Set ℝ) (wall collarWidth transverse : ℝ)
      (A : NormalizedGenericSection C axis) (R : ℝ)
      (massExpression : FiniteCombinationData C R)
      (corrections : Finset (FiniteCombinationData C R))
      (W K N : ℕ) (B mu delta G traceRadius recoveryScale finalScale : ℝ),
      A.raw.transverse = transverse ∧
      A.raw.rawCarrier = outerA ∧
      outerA.Nonempty ∧ 0 < collarWidth ∧
      (∀ z ∈ C.region.support, wall ≤ axis.transverseCoord z) ∧
      (∀ S : Set Tiling.Plane, (∀ s ∈ S, axis.transverseCoord s = 0) →
        Tiling.AxisParallel.regularSupport C.region S ∩
            {z | axis.transverseCoord z ∈ Set.Ioo (wall - collarWidth)
              (wall + collarWidth)} =
          {z | axis.transverseCoord z ∈ Set.Ioo wall (wall + collarWidth) ∧
            axis.coord z ∈ interior (closure (outerA + axis.coord '' S))}) ∧
      0 < R ∧ massExpression.value = A.massScalar ∧
      massExpression.weight ≤ W ∧ 0 < B ∧ A.mass < B ∧
      (∀ E ∈ corrections, E.weight ≤ W ∧ |(E.value : ℝ)| < B / 2) ∧
      (∀ {S : Set Tiling.Plane}, S ⊆ C.centres →
        Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
          (C.region.toPolygonalRegion.placements S) →
        (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) →
        ∀ J : BoundedOccupiedTraceComponent A S,
          ∃ code : ComponentMassCode A S J R, code.correction ∈ corrections) ∧
      4 * B / A.mass < (K : ℝ) ∧ 0 < mu ∧
      (∀ (q : ℤ) (c c' : FiniteCombinationData C R),
        q.natAbs < K → c ∈ corrections → c' ∈ corrections →
        (q : ℝ) * A.mass + c.value - c'.value ≠ 0 →
        mu ≤ |(q : ℝ) * A.mass + c.value - c'.value|) ∧
      0 < delta ∧
      (∀ S : Set Tiling.Plane,
        Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
          (C.region.toPolygonalRegion.placements S) →
        ∀ s ∈ S, ∀ t ∈ S, s ≠ t → delta ≤ dist s t) ∧
      G = 60 * Metric.diam C.region.openCarrier ∧ 0 < G ∧ 0 < traceRadius ∧
      (∀ {S : Set Tiling.Plane}, S ⊆ C.centres → S.Nonempty →
        Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
          (C.region.toPolygonalRegion.placements S) →
        Linked (60 * Metric.diam C.region.openCarrier) S →
        (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) →
        ¬ IsCenterColumn axis C.region S →
        ∀ u, ∀ hu : u ∈ properVertices (regularSupport C.region S),
          ∃ e, ∃ he : e ∈ properVertices (regularSupport C.region S),
            Relation.ReflTransGen
              (fun x y : ↥(properVertices (regularSupport C.region S)) =>
                dist x.1 y.1 < traceRadius)
              ⟨u, hu⟩ ⟨e, he⟩ ∧
            ∀ v ∈ properVertices (regularSupport C.region S),
              axis.transverseCoord e ≤ axis.transverseCoord v) ∧
      (N : ℝ) * delta > 4 * Metric.diam C.region.support ∧
      0 < recoveryScale ∧ 0 < finalScale ∧
      recoveryScale ≤ finalScale ∧
      10 * (Metric.diam C.region.openCarrier + 1) ≤ finalScale ∧
      (∀ P : FLCControlPackage C, finalScale < P.scale →
        10 * (Metric.diam C.region.openCarrier + 1) < P.scale ∧
        R < P.controlRadius ∧
        (N : ℝ) * G + 2 * Metric.diam C.region.support < P.scale ∧
        P.localError < delta / 2 ∧
        Metric.diam C.region.support < P.scale ∧
        P.localError ≤ Metric.diam C.region.support ∧
        Metric.diam C.region.support < P.controlRadius ∧
        G + P.localError < P.scale / 2 ∧
        traceRadius + 2 * P.localError < P.scale / 2 ∧
        ((K : ℝ) + 2) * (W : ℝ) / P.scale <
          min (A.mass / 2) (min (B / 2) mu)) := by
  obtain ⟨outerA, wall, collarWidth, hgeneric, houterNonempty, hcollarWidth,
      hwallLower, hwallGerm⟩ := exists_axis_outerWallData C.region axis
  obtain ⟨genericSection⟩ := hgeneric
  have hsliceNonempty :
      ({x : ℝ | FilledSliceChains.slicePoint axis genericSection.transverse x ∈
        C.region.openCarrier} : Set ℝ).Nonempty := by
    simpa [genericSection.carrier_eq, axisSection] using genericSection.nonempty
  obtain ⟨genuineSection, htransverse, hrawCarrier⟩ :=
    genuineGenericSection_construct C axis genericSection.transverse
      genericSection.generic hsliceNonempty
  have hgenuineCarrier : genuineSection.rawCarrier = outerA := by
    calc
      genuineSection.rawCarrier =
          {x : ℝ | FilledSliceChains.slicePoint axis genericSection.transverse x ∈
            C.region.openCarrier} := hrawCarrier
      _ = axisSection C.region axis genericSection.transverse := rfl
      _ = outerA := genericSection.carrier_eq.symm
  obtain ⟨A, hAraw⟩ := normalizedGenericSection_construct genuineSection
  have hAtransverse : A.raw.transverse = genericSection.transverse := by
    rw [hAraw, htransverse]
  have hAouterCarrier : A.raw.rawCarrier = outerA := by
    rw [hAraw]
    exact hgenuineCarrier
  obtain ⟨R, hR, massExpression, hmassExpression, corrections, hcorrections⟩ :=
    componentCorrections_finite hT axis A
  obtain ⟨W, hW, B, hB, hmassB, hcorrectionBounds⟩ :=
    finiteCorrections_uniformBounds A massExpression corrections
  obtain ⟨delta, hdelta, hpackingSeparation⟩ :=
    Tiling.AxisParallel.exists_packingSeparation C.region
  obtain ⟨traceRadius, htraceRadius, hlinkedPath⟩ :=
    columnable_extremalTrace_uniformLinked hT axis hcol
  obtain ⟨K, hK⟩ := exists_nat_gt (4 * B / A.mass)
  obtain ⟨mu, hmu, hzeroSeparation⟩ :=
    finiteBulkCorrection_zeroSeparation A.massScalar corrections K
  let supportDiameter := Metric.diam C.region.support
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * supportDiameter / delta)
  have hNdelta : (N : ℝ) * delta > 4 * supportDiameter := by
    exact (div_lt_iff₀ hdelta).mp hN
  let G := 60 * Metric.diam C.region.openCarrier
  have hG : 0 < G := by
    dsimp [G]
    exact mul_pos (by norm_num) (region_openCarrier_diam_pos C.region)
  obtain ⟨recoveryScale, hRecoveryPositive, hRecovery⟩ :=
    longComponentRecoveryScale_exists C R W K N B mu A.mass G delta traceRadius
      hB A.mass_pos hmu hdelta hG htraceRadius
  let geometryScale := 10 * (Metric.diam C.region.openCarrier + 1)
  let finalScale := max recoveryScale geometryScale
  have hfinalPositive : 0 < finalScale := by
    dsimp [finalScale, geometryScale]
    exact lt_of_lt_of_le (by positivity : 0 < 10 * (Metric.diam C.region.openCarrier + 1))
      (le_max_right recoveryScale (10 * (Metric.diam C.region.openCarrier + 1)))
  refine ⟨outerA, wall, collarWidth, genericSection.transverse, A, R,
    massExpression, corrections,
    W, K, N, B, mu, delta, G, traceRadius, recoveryScale, finalScale,
    hAtransverse, hAouterCarrier, houterNonempty, hcollarWidth, hwallLower,
    hwallGerm, hR, hmassExpression, hW, hB, hmassB, hcorrectionBounds,
    hcorrections, hK, hmu, ?_, hdelta, hpackingSeparation, rfl, hG,
    htraceRadius, hlinkedPath, hNdelta, hRecoveryPositive, hfinalPositive,
    le_max_left recoveryScale geometryScale,
    le_max_right recoveryScale geometryScale, ?_⟩
  · intro q c c' hq hc hc' hne
    have hne' : (q : ℝ) * (A.massScalar : ℝ) + c.value - c'.value ≠ 0 := by
      simpa only [A.massScalar_coe] using hne
    simpa only [A.massScalar_coe] using hzeroSeparation q c c' hq hc hc' hne'
  · intro P hP
    have hRecoveryP : recoveryScale < P.scale :=
      lt_of_le_of_lt (le_max_left recoveryScale geometryScale) hP
    have hGeometryP : geometryScale < P.scale :=
      lt_of_le_of_lt (le_max_right recoveryScale geometryScale) hP
    exact ⟨hGeometryP, hRecovery P hRecoveryP⟩

private structure ActualProperVertexCorrespondence
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (S : Set ↥C.centres)
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (hTarget : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))) where
  properVertexEquiv :
    ↥(properVertices (regularSupport C.region (Subtype.val '' S))) ≃
      ↥(properVertices
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)))
  source_label : ∀ x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S))),
    ∃ (v : ↥C.region.vertices) (t : S),
      x.1 = v.1 + t.1.1
  target_formula : ∀ x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S))),
    ∀ (v : ↥C.region.vertices) (t : S),
      x.1 = v.1 + t.1.1 →
      (properVertexEquiv x).1 = D.planarHomeomorph v.1 + Tphi t.1
  cone_preserved : ∀ x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S))),
    localCone _ x.1 hSource x.2 =
      localCone _ (properVertexEquiv x).1 hTarget (properVertexEquiv x).2

private theorem mapPoint_add_controlled
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧
      z.im ∈ C.coordinateSpace}) :
    mapPoint phi ⟨x.1 + y.1, C.coordinateSpace.add_mem x.2.1 y.2.1,
      C.coordinateSpace.add_mem x.2.2 y.2.2⟩ =
        mapPoint phi x + mapPoint phi y := by
  apply Complex.ext <;>
    simp only [mapPoint, mapScalar, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add] <;>
    norm_cast
  all_goals
    rw [← map_add]
    rfl

private theorem indexedTranslatedVertex_mapLabel
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (a : ↥C.translatedVertices) (v : ↥C.region.vertices)
    (t : ↥C.centres) (ha : a.1 = v.1 + t.1) :
    mapTranslatedVertex phi a = D.planarHomeomorph v.1 + Tphi t := by
  rw [mapTranslatedVertex]
  have hpoint : C.translatedVertexPoint a =
      ⟨v.1 + t.1,
        C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2)
          (C.centre_re_mem t.1 t.2),
        C.coordinateSpace.add_mem (C.vertex_im_mem v.1 v.2)
          (C.centre_im_mem t.1 t.2)⟩ := by
    apply Subtype.ext
    exact ha
  rw [hpoint]
  calc
    mapPoint phi ⟨v.1 + t.1,
        C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2)
          (C.centre_re_mem t.1 t.2),
        C.coordinateSpace.add_mem (C.vertex_im_mem v.1 v.2)
          (C.centre_im_mem t.1 t.2)⟩ =
        mapPoint phi (C.vertexPoint v.1 v.2) +
          mapPoint phi (C.centrePoint t.1 t.2) := by
            exact mapPoint_add_controlled phi
              (C.vertexPoint v.1 v.2) (C.centrePoint t.1 t.2)
    _ = D.planarHomeomorph v.1 + Tphi t := by
      rw [← D.vertex_agreement v.1 v.2, ← hTphi t]

private theorem actualProperVertexCorrespondence_exists
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S : Set ↥C.centres)
    (hpackSource : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S)))
    (hpackTarget : Tiling.IsPacking
      D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements
        (deformedCenterCarrierOn Tphi S)))
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (hTarget : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))) :
    Nonempty (ActualProperVertexCorrespondence C phi D Tphi S hSource hTarget) := by
  classical
  let Source : Set Tiling.Plane :=
    properVertices (regularSupport C.region (Subtype.val '' S))
  let Target : Set Tiling.Plane :=
    properVertices
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))
  have hlabel (x : ↥Source) :
      ∃ (v : ↥C.region.vertices) (t : S), x.1 = v.1 + t.1.1 := by
    obtain ⟨v, hv, s, hs, hxs⟩ :=
      Tiling.AxisParallel.properVertexProvenance hpackSource x.1 x.2
    obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨⟨v, hv⟩, ⟨t, ht⟩, hxs⟩
  let indexedLabel (x : ↥Source) : ↥C.translatedVertices :=
    ⟨x.1, by
      rw [ApproximationContext.translatedVertices]
      obtain ⟨v, t, hxt⟩ := hlabel x
      exact Set.mem_add.mpr ⟨v.1, v.2, t.1.1, t.1.2, hxt.symm⟩⟩
  have hlabelMem (x : ↥Source) :
      (indexedLabel x : Tiling.Plane) ∈
        C.region.vertices + Set.image Subtype.val S := by
    obtain ⟨v, t, hxt⟩ := hlabel x
    exact ⟨v.1, v.2, t.1.1, ⟨t.1, t.2, rfl⟩, hxt.symm⟩
  have hproper (x : ↥Source) :
      mapTranslatedVertex phi (indexedLabel x) ∈ Target := by
    obtain ⟨r₀, hr₀, hforward⟩ := deformation_preserves_localCone
      P hScale phi hphi D Tphi hTphi S (indexedLabel x) (hlabelMem x)
    obtain ⟨r₁, hr₁, hbackward⟩ := deformation_reflects_localCone
      P hScale phi hphi D Tphi hTphi S (indexedLabel x) (hlabelMem x)
    have hgerm : ∀ᶠ d in 𝓝 (0 : Tiling.Plane),
        ((indexedLabel x : Tiling.Plane) + d ∈
            regularSupport C.region (Subtype.val '' S) ↔
          mapTranslatedVertex phi (indexedLabel x) + d ∈
            regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)) := by
      apply Metric.eventually_nhds_iff.mpr
      refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_⟩
      intro d hd
      exact ⟨hforward d (hd.trans_le (min_le_left _ _)),
        hbackward d (hd.trans_le (min_le_right _ _))⟩
    apply (Tiling.AxisParallel.isProperVertex_iff_of_offset_germ
      hgerm).mp
    exact x.2
  let f : ↥Source → ↥Target :=
    fun x => ⟨mapTranslatedVertex phi (indexedLabel x), hproper x⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hmap : mapTranslatedVertex phi (indexedLabel x) =
        mapTranslatedVertex phi (indexedLabel y) := congrArg Subtype.val hxy
    have hxy' := deformation_injectiveOnTranslatedVertices P phi hphi hmap
    apply Subtype.ext
    exact congrArg (fun a : ↥C.translatedVertices => (a : Tiling.Plane)) hxy'
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨w, hw, s, hs, hys⟩ :=
      Tiling.AxisParallel.properVertexProvenance hpackTarget y.1 y.2
    rw [D.vertices_image] at hw
    obtain ⟨v, hv, hvw⟩ := hw
    obtain ⟨t, ht, rfl⟩ := hs
    let a' : ↥C.translatedVertices :=
      ⟨v + t.1, ⟨v, hv, t.1, t.2, rfl⟩⟩
    have ha' : (a' : Tiling.Plane) ∈
        C.region.vertices + Set.image Subtype.val S :=
      ⟨v, hv, t.1, ⟨t, ht, rfl⟩, rfl⟩
    have hys' : y.1 = D.planarHomeomorph v + Tphi t := by
      simpa only [hvw] using hys
    have hmap : mapTranslatedVertex phi a' = y.1 := by
      rw [indexedTranslatedVertex_mapLabel Tphi hTphi a' ⟨v, hv⟩ t rfl]
      exact hys'.symm
    have hproper' : (a' : Tiling.Plane) ∈ Source := by
      obtain ⟨r₀, hr₀, hforward⟩ := deformation_preserves_localCone
        P hScale phi hphi D Tphi hTphi S a' ha'
      obtain ⟨r₁, hr₁, hbackward⟩ := deformation_reflects_localCone
        P hScale phi hphi D Tphi hTphi S a' ha'
      have hgerm : ∀ᶠ d in 𝓝 (0 : Tiling.Plane),
          ((a' : Tiling.Plane) + d ∈ regularSupport C.region
              (Subtype.val '' S) ↔
            mapTranslatedVertex phi a' + d ∈ regularSupport D.deformedRegion
              (deformedCenterCarrierOn Tphi S)) := by
        apply Metric.eventually_nhds_iff.mpr
        refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_⟩
        intro d hd
        exact ⟨hforward d (hd.trans_le (min_le_left _ _)),
          hbackward d (hd.trans_le (min_le_right _ _))⟩
      apply (Tiling.AxisParallel.isProperVertex_iff_of_offset_germ
        hgerm).mpr
      have hyproper : IsProperVertex
          (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)) y.1 := by
        simpa only [Target, properVertices, Tiling.Polygonal.properVertices,
          Set.mem_ofPred_eq] using y.2
      simpa only [hmap] using hyproper
    let x : ↥Source := ⟨a'.1, hproper'⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change mapTranslatedVertex phi (indexedLabel x) = y.1
    have hax : indexedLabel x = a' := Subtype.ext rfl
    rw [hax, hmap]
  let e : ↥Source ≃ ↥Target := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨{
    properVertexEquiv := e
    source_label := hlabel
    target_formula := ?_
    cone_preserved := ?_
  }⟩
  · intro x v t hxt
    change mapTranslatedVertex phi (indexedLabel x) =
      D.planarHomeomorph v.1 + Tphi t.1
    exact indexedTranslatedVertex_mapLabel Tphi hTphi
      (indexedLabel x) v t.1 hxt
  · intro x
    change localCone _ x.1 hSource x.2 =
      localCone _ (mapTranslatedVertex phi (indexedLabel x)) hTarget
        (hproper x)
    obtain ⟨r₀, hr₀, hforward⟩ := deformation_preserves_localCone
      P hScale phi hphi D Tphi hTphi S (indexedLabel x) (hlabelMem x)
    obtain ⟨r₁, hr₁, hbackward⟩ := deformation_reflects_localCone
      P hScale phi hphi D Tphi hTphi S (indexedLabel x) (hlabelMem x)
    have hgerm : ∀ᶠ d in 𝓝 (0 : Tiling.Plane),
        ((indexedLabel x : Tiling.Plane) + d ∈
            regularSupport C.region (Subtype.val '' S) ↔
          mapTranslatedVertex phi (indexedLabel x) + d ∈
            regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)) := by
      apply Metric.eventually_nhds_iff.mpr
      refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_⟩
      intro d hd
      exact ⟨hforward d (hd.trans_le (min_le_left _ _)),
        hbackward d (hd.trans_le (min_le_right _ _))⟩
    exact Tiling.AxisParallel.Terminal.localCone_eq_of_eventually_mem_iff_offset
      hSource hTarget x.2 (hproper x) hgerm

private structure ActualProperVertexPairCorrespondence
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (S₀ S₁ : Set ↥C.centres)
    (hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀)))
    (hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁)))
    (hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)))
    (hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)))
    (eta : Tiling.Plane) where
  theta :
    ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))) ≃
      ↥(properVertices (regularSupport C.region (Subtype.val '' S₁)))
  source_label₀ : ∀ x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))),
    ∃ (v : ↥C.region.vertices) (t : S₀),
      x.1 = v.1 + t.1.1
  source_label₁ : ∀ x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))),
    ∃ (v : ↥C.region.vertices) (t : S₁),
      (theta x).1 = v.1 + t.1.1
  cone_preserved : ∀ x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))),
    localCone _ x.1 hSource₀ x.2 =
      localCone _ (theta x).1 hSource₁ (theta x).2
  controlled_displacement : ∀ x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))),
    ∃ beta : ControlledDisplacement C,
      (beta : Tiling.Plane) = (theta x).1 - x.1 ∧
        mapPoint phi beta = eta

private theorem mapPoint_sub_controlled
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧
      z.im ∈ C.coordinateSpace}) :
    mapPoint phi ⟨x.1 - y.1, C.coordinateSpace.sub_mem x.2.1 y.2.1,
      C.coordinateSpace.sub_mem x.2.2 y.2.2⟩ = mapPoint phi x - mapPoint phi y := by
  apply Complex.ext
  · simp only [mapPoint, mapScalar, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, sub_zero, add_zero]
    exact_mod_cast (map_sub phi
      (⟨x.1.re, x.2.1⟩ : C.coordinateSpace)
      (⟨y.1.re, y.2.1⟩ : C.coordinateSpace))
  · simp only [mapPoint, mapScalar, Complex.sub_re, Complex.sub_im,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, add_zero, zero_add]
    exact_mod_cast (map_sub phi
      (⟨x.1.im, x.2.2⟩ : C.coordinateSpace)
      (⟨y.1.im, y.2.2⟩ : C.coordinateSpace))

private theorem actualProperVertexPairCorrespondence_exists
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S₀ S₁ : Set ↥C.centres)
    (hpackSource₀ : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S₀)))
    (hpackSource₁ : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S₁)))
    (hpackTarget₀ : Tiling.IsPacking
      D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements
        (deformedCenterCarrierOn Tphi S₀)))
    (hpackTarget₁ : Tiling.IsPacking
      D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements
        (deformedCenterCarrierOn Tphi S₁)))
    (hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀)))
    (hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁)))
    (hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)))
    (hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)))
    (eta : Tiling.Plane)
    (hImageSupport : regularSupport D.deformedRegion
        (deformedCenterCarrierOn Tphi S₁) =
      eta +ᵥ regularSupport D.deformedRegion
        (deformedCenterCarrierOn Tphi S₀)) :
    Nonempty (ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta) := by
  classical
  obtain ⟨B₀⟩ := actualProperVertexCorrespondence_exists P hScale phi hphi D
    Tphi hTphi S₀ hpackSource₀ hpackTarget₀ hSource₀ hTarget₀
  obtain ⟨B₁⟩ := actualProperVertexCorrespondence_exists P hScale phi hphi D
    Tphi hTphi S₁ hpackSource₁ hpackTarget₁ hSource₁ hTarget₁
  let Source₀ : Set Tiling.Plane :=
    properVertices (regularSupport C.region (Subtype.val '' S₀))
  let Source₁ : Set Tiling.Plane :=
    properVertices (regularSupport C.region (Subtype.val '' S₁))
  let Target₀ : Set Tiling.Plane :=
    properVertices
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))
  let Target₁ : Set Tiling.Plane :=
    properVertices
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))
  have hTargetVertices : Target₁ = eta +ᵥ Target₀ := by
    change properVertices
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)) =
      eta +ᵥ properVertices
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))
    rw [hImageSupport, Tiling.AxisParallel.properVertices_vadd_eq]
  let shift : ↥Target₀ ≃ ↥Target₁ := Equiv.ofBijective
    (fun y : ↥Target₀ =>
      (⟨eta + y.1, by
        rw [hTargetVertices]
        exact ⟨y.1, y.2, rfl⟩⟩ : ↥Target₁))
    ⟨by
      intro x y hxy
      apply Subtype.ext
      exact add_left_cancel (congrArg Subtype.val hxy),
      by
        intro y
        have hy : y.1 ∈ eta +ᵥ Target₀ := by
          rw [← hTargetVertices]
          exact y.2
        obtain ⟨z, hz, hzy⟩ := Set.mem_vadd_set.mp hy
        refine ⟨⟨z, hz⟩, ?_⟩
        apply Subtype.ext
        change eta + z = y.1
        exact hzy⟩
  let theta : ↥Source₀ ≃ ↥Source₁ :=
    B₀.properVertexEquiv.trans (shift.trans B₁.properVertexEquiv.symm)
  have hpaired (x : ↥Source₀) :
      B₁.properVertexEquiv (theta x) = shift (B₀.properVertexEquiv x) := by
    simp [theta]
  have hpairedValue (x : ↥Source₀) :
      (B₁.properVertexEquiv (theta x)).1 =
        eta + (B₀.properVertexEquiv x).1 := by
    calc
      (B₁.properVertexEquiv (theta x)).1 =
          (shift (B₀.properVertexEquiv x)).1 :=
        congrArg Subtype.val (hpaired x)
      _ = eta + (B₀.properVertexEquiv x).1 := rfl
  have hcone (x : ↥Source₀) :
      localCone _ x.1 hSource₀ x.2 =
        localCone _ (theta x).1 hSource₁ (theta x).2 := by
    have hTargetProper :
        eta + (B₀.properVertexEquiv x).1 ∈ Target₁ := by
      rw [← hpairedValue x]
      exact (B₁.properVertexEquiv (theta x)).2
    change IsProperVertex
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))
      (eta + (B₀.properVertexEquiv x).1) at hTargetProper
    calc
      localCone _ x.1 hSource₀ x.2 =
          localCone _ (B₀.properVertexEquiv x).1 hTarget₀
            (B₀.properVertexEquiv x).2 := B₀.cone_preserved x
      _ = localCone _ (eta + (B₀.properVertexEquiv x).1) hTarget₁
            hTargetProper :=
        Tiling.AxisParallel.Terminal.localCone_eq_of_vadd_eq
          hTarget₀ hTarget₁ (B₀.properVertexEquiv x).2 hTargetProper
          hImageSupport
      _ = localCone _ (theta x).1 hSource₁ (theta x).2 := by
        let shifted : ↥Target₁ :=
          ⟨eta + (B₀.properVertexEquiv x).1, hTargetProper⟩
        have hshifted : shifted = B₁.properVertexEquiv (theta x) :=
          Subtype.ext (hpairedValue x).symm
        have hconeShift := congrArg
          (fun y : ↥Target₁ =>
            localCone _ y.1 hTarget₁ y.2) hshifted
        exact hconeShift.trans (B₁.cone_preserved (theta x)).symm
  have hdisplacement (x : ↥Source₀) :
      ∃ beta : ControlledDisplacement C,
        (beta : Tiling.Plane) = (theta x).1 - x.1 ∧
          mapPoint phi beta = eta := by
    obtain ⟨v₀, t₀, hxLabel⟩ := B₀.source_label x
    obtain ⟨v₁, t₁, hyLabel⟩ := B₁.source_label (theta x)
    let a₀ : ↥C.translatedVertices := ⟨x.1, by
      rw [ApproximationContext.translatedVertices]
      exact Set.mem_add.mpr
        ⟨v₀.1, v₀.2, t₀.1.1, t₀.1.2, hxLabel.symm⟩⟩
    let a₁ : ↥C.translatedVertices := ⟨(theta x).1, by
      rw [ApproximationContext.translatedVertices]
      exact Set.mem_add.mpr
        ⟨v₁.1, v₁.2, t₁.1.1, t₁.1.2, hyLabel.symm⟩⟩
    have hmap₀ : mapTranslatedVertex phi a₀ =
        (B₀.properVertexEquiv x).1 := by
      calc
        mapTranslatedVertex phi a₀ =
            D.planarHomeomorph v₀.1 + Tphi t₀.1 :=
          indexedTranslatedVertex_mapLabel Tphi hTphi a₀ v₀ t₀.1 hxLabel
        _ = (B₀.properVertexEquiv x).1 :=
          (B₀.target_formula x v₀ t₀ hxLabel).symm
    have hmap₁ : mapTranslatedVertex phi a₁ =
        (B₁.properVertexEquiv (theta x)).1 := by
      calc
        mapTranslatedVertex phi a₁ =
            D.planarHomeomorph v₁.1 + Tphi t₁.1 :=
          indexedTranslatedVertex_mapLabel Tphi hTphi a₁ v₁ t₁.1 hyLabel
        _ = (B₁.properVertexEquiv (theta x)).1 :=
          (B₁.target_formula (theta x) v₁ t₁ hyLabel).symm
    let beta : ControlledDisplacement C :=
      ⟨(C.translatedVertexPoint a₁).1 -
          (C.translatedVertexPoint a₀).1,
        C.coordinateSpace.sub_mem (C.translatedVertexPoint a₁).2.1
          (C.translatedVertexPoint a₀).2.1,
        C.coordinateSpace.sub_mem (C.translatedVertexPoint a₁).2.2
          (C.translatedVertexPoint a₀).2.2⟩
    have hbetaValue : (beta : Tiling.Plane) = (theta x).1 - x.1 := by
      rfl
    have hbetaMap : mapPoint phi beta = eta := by
      have hsub : mapPoint phi beta =
          mapTranslatedVertex phi a₁ - mapTranslatedVertex phi a₀ := by
        change mapPoint phi ⟨
          (C.translatedVertexPoint a₁).1 - (C.translatedVertexPoint a₀).1,
          C.coordinateSpace.sub_mem (C.translatedVertexPoint a₁).2.1
            (C.translatedVertexPoint a₀).2.1,
          C.coordinateSpace.sub_mem (C.translatedVertexPoint a₁).2.2
            (C.translatedVertexPoint a₀).2.2⟩ = _
        simpa only [mapTranslatedVertex] using
          mapPoint_sub_controlled phi (C.translatedVertexPoint a₁)
            (C.translatedVertexPoint a₀)
      rw [hsub, hmap₁, hmap₀, hpairedValue]
      simp
    exact ⟨beta, hbetaValue, hbetaMap⟩
  exact ⟨{
    theta := theta
    source_label₀ := B₀.source_label
    source_label₁ := fun x => B₁.source_label (theta x)
    cone_preserved := hcone
    controlled_displacement := hdisplacement
  }⟩

private theorem actualPair_endpoint_target_difference
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S₀ S₁ : Set ↥C.centres}
    {hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀))}
    {hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁))}
    {hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))}
    {hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))}
    {eta : Tiling.Plane} {axis : Axis}
    {A : NormalizedGenericSection C axis}
    (pair : ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (x : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))))
    (e : IndexedSectionEndpoint A S₀) (f : IndexedSectionEndpoint A S₁)
    (he : e.sourceValue = axis.coord x.1 - A.origin)
    (hf : f.sourceValue = axis.coord (pair.theta x).1 - A.origin) :
    IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f -
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e =
        axis.coord eta := by
  obtain ⟨beta, hbeta, hbetaMap⟩ := pair.controlled_displacement x
  have hscalarDiff : f.sourceCoordScalar A - e.sourceCoordScalar A =
      planeAxisCoordScalar axis beta := by
    apply Subtype.ext
    simp only [Submodule.coe_sub, planeAxisCoordScalar_coe]
    rw [f.sourceCoordScalar_coe, e.sourceCoordScalar_coe, hf, he, hbeta]
    cases axis <;> simp [Axis.coord, Complex.sub_re, Complex.sub_im]
  have hsourceMapF := IndexedSectionEndpoint.sourceCoordScalar_map (D := D) hTphi f
  have hsourceMapE := IndexedSectionEndpoint.sourceCoordScalar_map (D := D) hTphi e
  calc
    IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f -
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e =
      mapScalar phi (f.sourceCoordScalar A) - mapScalar phi (e.sourceCoordScalar A) := by
        rw [← hsourceMapF, ← hsourceMapE]
    _ = mapScalar phi (f.sourceCoordScalar A - e.sourceCoordScalar A) := by
      simp [mapScalar, map_sub]
    _ = mapScalar phi (planeAxisCoordScalar axis beta) := by rw [hscalarDiff]
    _ = axis.coord eta := by
      rw [← mapPoint_axisCoord phi axis beta, hbetaMap]

private theorem actualPair_endpoint_weakOrder_at_traceFrontier
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S₀ S₁ : Set ↥C.centres}
    {hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀))}
    {hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁))}
    {hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))}
    {hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))}
    {eta : Tiling.Plane} {axis : Axis}
    {A : NormalizedGenericSection C axis}
    (pair : ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta)
    (E₀ : AllEndpointWeakOrderTransport phi D Tphi axis S₀ A)
    (E₁ : AllEndpointWeakOrderTransport phi D Tphi axis S₁ A)
    (u v : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))))
    (hu₀ : axis.coord u.1 - A.origin ∈
      frontier (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀)))))
    (hv₀ : axis.coord v.1 - A.origin ∈
      frontier (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀)))))
    (hu₁ : axis.coord (pair.theta u).1 - A.origin ∈
      frontier (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₁)))))
    (hv₁ : axis.coord (pair.theta v).1 - A.origin ∈
      frontier (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₁))))) :
    axis.coord u.1 ≤ axis.coord v.1 ↔
      axis.coord (pair.theta u).1 ≤ axis.coord (pair.theta v).1 := by
  obtain ⟨e, he⟩ := E₀.source_frontier_subset hu₀
  obtain ⟨f, hf⟩ := E₀.source_frontier_subset hv₀
  obtain ⟨g, hg⟩ := E₁.source_frontier_subset hu₁
  obtain ⟨h, hh⟩ := E₁.source_frontier_subset hv₁
  have hsourceOrder : axis.coord u.1 ≤ axis.coord v.1 ↔
      e.sourceValue ≤ f.sourceValue := by
    rw [he, hf]
    constructor <;> intro horder <;> linarith
  have htargetShiftU :
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) g =
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e +
          axis.coord eta := by
    have hdiff := actualPair_endpoint_target_difference (A := A) pair
      E₀.indexedCentre_formula u e g he hg
    linarith
  have htargetShiftV :
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) h =
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f +
          axis.coord eta := by
    have hdiff := actualPair_endpoint_target_difference (A := A) pair
      E₀.indexedCentre_formula v f h hf hh
    linarith
  have htargetOrder :
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e ≤
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f ↔
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) g ≤
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) h := by
    rw [htargetShiftU, htargetShiftV]
    constructor <;> intro horder <;> linarith
  have htargetSourceOrder := (E₀.weakOrder_iff e f)
  have hsourceTargetOrder := (E₁.weakOrder_iff g h).symm
  have hsourceOrder₁ : g.sourceValue ≤ h.sourceValue ↔
      axis.coord (pair.theta u).1 ≤ axis.coord (pair.theta v).1 := by
    rw [hg, hh]
    constructor <;> intro horder <;> linarith
  exact hsourceOrder.trans (htargetSourceOrder.trans
    (htargetOrder.trans (hsourceTargetOrder.trans hsourceOrder₁)))

/-!
Transfer equality of source component lengths across an actual proper-vertex pair.

This private fragment uses the actual bounded-component mass codes, endpoint
labels, pair displacement, and frozen long-component reflection controls.
-/

private theorem actualPair_boundedComponent_displacement
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S₀ S₁ : Set ↥C.centres}
    {hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀))}
    {hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁))}
    {hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))}
    {hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))}
    {eta : Tiling.Plane} {axis : Axis} {A : NormalizedGenericSection C axis}
    (pair : ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (E₀ : AllEndpointWeakOrderTransport phi D Tphi axis S₀ A)
    (E₁ : AllEndpointWeakOrderTransport phi D Tphi axis S₁ A)
    (u v : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))))
    (J₀ : BoundedOccupiedTraceComponent A (Subtype.val '' S₀))
    (J₁ : BoundedOccupiedTraceComponent A (Subtype.val '' S₁))
    {R : ℝ}
    (code₀ : ComponentMassCode A (Subtype.val '' S₀) J₀ R)
    (code₁ : ComponentMassCode A (Subtype.val '' S₁) J₁ R)
    (hJ₀left : J₀.left = axis.coord u.1 - A.origin)
    (hJ₀right : J₀.right = axis.coord v.1 - A.origin)
    (hJ₁left : J₁.left = axis.coord (pair.theta u).1 - A.origin)
    (hJ₁right : J₁.right = axis.coord (pair.theta v).1 - A.origin)
    (massExpression : FiniteCombinationData C R)
    (corrections : Finset (FiniteCombinationData C R))
    (W K : ℕ) (B mu : ℝ)
    (hmassExpression : massExpression.value = A.massScalar)
    (hmassWeight : massExpression.weight ≤ W)
    (hmassPos : 0 < A.mass) (hmassBound : A.mass < B)
    (hcorrections : ∀ E ∈ corrections,
      E.weight ≤ W ∧ |(E.value : ℝ)| < B / 2)
    (hK : 4 * B / A.mass < K) (hmu : 0 < mu)
    (hseparate : ∀ (q : ℤ) (c c' : FiniteCombinationData C R),
      q.natAbs < K → c ∈ corrections → c' ∈ corrections →
      (q : ℝ) * A.mass + c.value - c'.value ≠ 0 →
      mu ≤ |(q : ℝ) * A.mass + c.value - c'.value|)
    (P : FLCControlPackage C) (hR : R < P.controlRadius)
    (hscale : ((K : ℝ) + 2) * (W : ℝ) / P.scale <
      min (A.mass / 2) (min (B / 2) mu))
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (hcode₀ : code₀.correction ∈ corrections)
    (hcode₁ : code₁.correction ∈ corrections) :
    J₀.right - J₀.left = J₁.right - J₁.left := by
  obtain ⟨e₀, f₀, he₀, hf₀, _horder₀, hlength₀⟩ :=
    boundedOccupiedComponent_code_mappedEndpointLength E₀ J₀ code₀
  obtain ⟨e₁, f₁, he₁, hf₁, _horder₁, hlength₁⟩ :=
    boundedOccupiedComponent_code_mappedEndpointLength E₁ J₁ code₁
  have hleftDisplacement := actualPair_endpoint_target_difference pair hTphi u e₀ e₁
    (he₀.trans hJ₀left) (he₁.trans hJ₁left)
  have hrightDisplacement := actualPair_endpoint_target_difference pair hTphi v f₀ f₁
    (hf₀.trans hJ₀right) (hf₁.trans hJ₁right)
  have htargetLength :
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f₀ -
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₀ =
      IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f₁ -
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₁ := by
    linarith
  have hmappedLength :
      (code₀.bulk.card : ℝ) * mapScalar phi A.massScalar +
          code₀.correction.mappedValue phi =
        (code₁.bulk.card : ℝ) * mapScalar phi A.massScalar +
          code₁.correction.mappedValue phi := by
    calc
      (code₀.bulk.card : ℝ) * mapScalar phi A.massScalar +
          code₀.correction.mappedValue phi =
        IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f₀ -
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₀ := hlength₀.symm
      _ = IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) f₁ -
          IndexedSectionEndpoint.targetValue (D := D) (Tphi := Tphi) e₁ := htargetLength
      _ = (code₁.bulk.card : ℝ) * mapScalar phi A.massScalar +
          code₁.correction.mappedValue phi := hlength₁
  have hsourceLength := longComponentLength_reflects A massExpression corrections W K B mu
    hmassExpression hmassWeight hmassPos hmassBound hcorrections hK hmu hseparate
    P hR hscale phi hphi code₀.bulk.card code₁.bulk.card
    code₀.correction code₁.correction hcode₀ hcode₁ hmappedLength
  calc
    J₀.right - J₀.left =
        (code₀.bulk.card : ℝ) * A.mass + (code₀.correction.value : ℝ) := code₀.length_eq
    _ = (code₁.bulk.card : ℝ) * A.mass + (code₁.correction.value : ℝ) := hsourceLength
    _ = J₁.right - J₁.left := code₁.length_eq.symm

private theorem actualProperVertexPair_shortStep_displacement
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S₀ S₁ : Set ↥C.centres}
    {hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀))}
    {hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁))}
    {hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))}
    {hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))}
    {eta : Tiling.Plane}
    (pair : ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta)
    (P : FLCControlPackage C)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (u v : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))))
    (hDistance : dist u.1 v.1 < P.scale)
    (hMargin : dist u.1 v.1 + P.localError < P.scale / 2) :
    (pair.theta v).1 - (pair.theta u).1 = v.1 - u.1 := by
  classical
  obtain ⟨v₀u, t₀u, hu₀Label⟩ := pair.source_label₀ u
  obtain ⟨v₀v, t₀v, hv₀Label⟩ := pair.source_label₀ v
  obtain ⟨v₁u, t₁u, hu₁Label⟩ := pair.source_label₁ u
  obtain ⟨v₁v, t₁v, hv₁Label⟩ := pair.source_label₁ v
  let a₀u : ↥C.translatedVertices := ⟨u.1, by
    rw [ApproximationContext.translatedVertices]
    exact Set.mem_add.mpr
      ⟨v₀u.1, v₀u.2, t₀u.1.1, t₀u.1.2, hu₀Label.symm⟩⟩
  let a₀v : ↥C.translatedVertices := ⟨v.1, by
    rw [ApproximationContext.translatedVertices]
    exact Set.mem_add.mpr
      ⟨v₀v.1, v₀v.2, t₀v.1.1, t₀v.1.2, hv₀Label.symm⟩⟩
  let a₁u : ↥C.translatedVertices := ⟨(pair.theta u).1, by
    rw [ApproximationContext.translatedVertices]
    exact Set.mem_add.mpr
      ⟨v₁u.1, v₁u.2, t₁u.1.1, t₁u.1.2, hu₁Label.symm⟩⟩
  let a₁v : ↥C.translatedVertices := ⟨(pair.theta v).1, by
    rw [ApproximationContext.translatedVertices]
    exact Set.mem_add.mpr
      ⟨v₁v.1, v₁v.2, t₁v.1.1, t₁v.1.2, hv₁Label.symm⟩⟩
  have hImageShift (x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))))
      (a₀ a₁ : ↥C.translatedVertices)
      (ha₀ : (a₀ : Tiling.Plane) = x.1)
      (ha₁ : (a₁ : Tiling.Plane) = (pair.theta x).1) :
      mapTranslatedVertex phi a₁ - mapTranslatedVertex phi a₀ = eta := by
    obtain ⟨beta, hbetaValue, hbetaMap⟩ := pair.controlled_displacement x
    let betaDiff : ControlledDisplacement C :=
      ⟨(C.translatedVertexPoint a₁).1 - (C.translatedVertexPoint a₀).1,
        C.coordinateSpace.sub_mem (C.translatedVertexPoint a₁).2.1
          (C.translatedVertexPoint a₀).2.1,
        C.coordinateSpace.sub_mem (C.translatedVertexPoint a₁).2.2
          (C.translatedVertexPoint a₀).2.2⟩
    have hdiffValue : (betaDiff : Tiling.Plane) = (pair.theta x).1 - x.1 := by
      change (a₁ : Tiling.Plane) - (a₀ : Tiling.Plane) = _
      rw [ha₁, ha₀]
    have hbetaEq : beta = betaDiff :=
      Subtype.ext (hbetaValue.trans hdiffValue.symm)
    have hmapDiff : mapPoint phi betaDiff =
        mapTranslatedVertex phi a₁ - mapTranslatedVertex phi a₀ := by
      change mapPoint phi ⟨
        (C.translatedVertexPoint a₁).1 - (C.translatedVertexPoint a₀).1,
        C.coordinateSpace.sub_mem (C.translatedVertexPoint a₁).2.1
          (C.translatedVertexPoint a₀).2.1,
        C.coordinateSpace.sub_mem (C.translatedVertexPoint a₁).2.2
          (C.translatedVertexPoint a₀).2.2⟩ = _
      simpa only [mapTranslatedVertex] using
        mapPoint_sub_controlled phi (C.translatedVertexPoint a₁)
          (C.translatedVertexPoint a₀)
    calc
      mapTranslatedVertex phi a₁ - mapTranslatedVertex phi a₀ =
          mapPoint phi betaDiff := hmapDiff.symm
      _ = mapPoint phi beta := by
        rw [hbetaEq.symm]
      _ = eta := hbetaMap
  have hImageShift₀u :
      mapTranslatedVertex phi a₁u - mapTranslatedVertex phi a₀u = eta :=
    hImageShift u a₀u a₁u rfl rfl
  have hImageShift₀v :
      mapTranslatedVertex phi a₁v - mapTranslatedVertex phi a₀v = eta :=
    hImageShift v a₀v a₁v rfl rfl
  have hImagePoint₀u : mapTranslatedVertex phi a₁u =
      eta + mapTranslatedVertex phi a₀u := by
    calc
      mapTranslatedVertex phi a₁u =
          (mapTranslatedVertex phi a₁u - mapTranslatedVertex phi a₀u) +
            mapTranslatedVertex phi a₀u := by abel
      _ = eta + mapTranslatedVertex phi a₀u := by rw [hImageShift₀u]
  have hImagePoint₀v : mapTranslatedVertex phi a₁v =
      eta + mapTranslatedVertex phi a₀v := by
    calc
      mapTranslatedVertex phi a₁v =
          (mapTranslatedVertex phi a₁v - mapTranslatedVertex phi a₀v) +
            mapTranslatedVertex phi a₀v := by abel
      _ = eta + mapTranslatedVertex phi a₀v := by rw [hImageShift₀v]
  have hImageEdge : mapTranslatedVertex phi a₁v - mapTranslatedVertex phi a₁u =
      mapTranslatedVertex phi a₀v - mapTranslatedVertex phi a₀u := by
    rw [hImagePoint₀v, hImagePoint₀u]
    abel
  have hDistanceReversed : dist v.1 u.1 < P.scale := by
    simpa only [dist_comm] using hDistance
  have hDistanceLabels : dist (a₀v : Tiling.Plane) (a₀u : Tiling.Plane) <
      P.scale := by
    simpa only [a₀v, a₀u] using hDistanceReversed
  have hlocal := P.local_accuracy phi hphi a₀v a₀u hDistanceLabels
  have hlocal' :
      dist (mapTranslatedVertex phi a₀v - mapTranslatedVertex phi a₀u)
        (v.1 - u.1) < P.localError := by
    change dist (mapTranslatedVertex phi a₀v - mapTranslatedVertex phi a₀u)
      ((a₀v : Tiling.Plane) - (a₀u : Tiling.Plane)) < P.localError at hlocal
    simpa only [a₀v, a₀u] using hlocal
  have hsourceDifferenceNorm : dist (v.1 - u.1) 0 = dist u.1 v.1 := by
    simp only [dist_eq_norm, sub_zero, norm_sub_rev]
  have dist_eq_difference (a b : Tiling.Plane) :
      dist a b = dist (a - b) 0 := by
    simp only [dist_eq_norm, sub_zero]
  have hMappedEdgeBound :
      dist (mapTranslatedVertex phi a₀v - mapTranslatedVertex phi a₀u) 0 <
        P.scale / 2 := by
    calc
      dist (mapTranslatedVertex phi a₀v - mapTranslatedVertex phi a₀u) 0 ≤
          dist (mapTranslatedVertex phi a₀v - mapTranslatedVertex phi a₀u)
              (v.1 - u.1) + dist (v.1 - u.1) 0 :=
        dist_triangle _ _ _
      _ < P.localError + dist u.1 v.1 := by
        rw [hsourceDifferenceNorm]
        linarith
      _ < P.scale / 2 := by linarith
  have hMappedPairBound :
      dist (mapTranslatedVertex phi a₀v) (mapTranslatedVertex phi a₀u) <
        P.scale / 2 := by
    rw [dist_eq_difference]
    exact hMappedEdgeBound
  have hTargetMappedEdgeBound :
      dist (mapTranslatedVertex phi a₁v) (mapTranslatedVertex phi a₁u) <
        P.scale / 2 := by
    calc
      dist (mapTranslatedVertex phi a₁v) (mapTranslatedVertex phi a₁u) =
          dist (mapTranslatedVertex phi a₁v - mapTranslatedVertex phi a₁u) 0 :=
        dist_eq_difference _ _
      _ = dist (mapTranslatedVertex phi a₀v - mapTranslatedVertex phi a₀u) 0 := by
        rw [hImageEdge]
      _ = dist (mapTranslatedVertex phi a₀v) (mapTranslatedVertex phi a₀u) :=
        (dist_eq_difference _ _).symm
      _ < P.scale / 2 := hMappedPairBound
  have hMappedEdgeCoordinate (axis : Axis) :
      Axis.coord axis (mapTranslatedVertex phi a₀v - mapTranslatedVertex phi a₀u) =
        Axis.coord axis (mapTranslatedVertex phi a₁v - mapTranslatedVertex phi a₁u) := by
    rw [← hImageEdge]
  have hHorizontal := deformation_reflectsBoundedCoordinateDisplacement
    P phi hphi Axis.horizontal a₀u a₀v a₁u a₁v
    hMappedPairBound hTargetMappedEdgeBound
    (hMappedEdgeCoordinate Axis.horizontal)
  have hVertical := deformation_reflectsBoundedCoordinateDisplacement
    P phi hphi Axis.vertical a₀u a₀v a₁u a₁v
    hMappedPairBound hTargetMappedEdgeBound
    (hMappedEdgeCoordinate Axis.vertical)
  have hLabelledEdge :
      (a₁v : Tiling.Plane) - (a₁u : Tiling.Plane) =
        (a₀v : Tiling.Plane) - (a₀u : Tiling.Plane) := by
    apply Complex.ext
    · simpa only [Axis.coord, Complex.sub_re] using hHorizontal.symm
    · simpa only [Axis.coord, Complex.sub_im] using hVertical.symm
  simpa only [a₁v, a₁u, a₀v, a₀u] using hLabelledEdge

private theorem actualProperVertexPair_shortStep_displacement_either
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S₀ S₁ : Set ↥C.centres}
    {hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀))}
    {hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁))}
    {hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))}
    {hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))}
    {eta : Tiling.Plane}
    (pair : ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta)
    (P : FLCControlPackage C)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (u v : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))))
    (hShort : (dist u.1 v.1 < P.scale ∧
        dist u.1 v.1 + P.localError < P.scale / 2) ∨
      (dist (pair.theta u).1 (pair.theta v).1 < P.scale ∧
        dist (pair.theta u).1 (pair.theta v).1 + P.localError < P.scale / 2)) :
    (pair.theta v).1 - (pair.theta u).1 = v.1 - u.1 := by
  classical
  rcases hShort with hSource | hTarget
  · exact actualProperVertexPair_shortStep_displacement pair P hphi u v
      hSource.1 hSource.2
  · let inversePair : ActualProperVertexPairCorrespondence C phi D Tphi S₁ S₀
        hSource₁ hSource₀ hTarget₁ hTarget₀ (-eta) := {
      theta := pair.theta.symm
      source_label₀ := by
        intro x
        obtain ⟨w, s, hws⟩ := pair.source_label₁ (pair.theta.symm x)
        exact ⟨w, s, by simpa using hws⟩
      source_label₁ := by
        intro x
        obtain ⟨w, s, hws⟩ := pair.source_label₀ (pair.theta.symm x)
        exact ⟨w, s, by simpa using hws⟩
      cone_preserved := by
        intro x
        have hθ : pair.theta (pair.theta.symm x) = x :=
          pair.theta.apply_symm_apply x
        have hθCone := congrArg
          (fun z : ↥(properVertices
              (regularSupport C.region (Subtype.val '' S₁))) =>
            localCone _ z.1 hSource₁ z.2) hθ
        calc
          localCone _ x.1 hSource₁ x.2 =
              localCone _ (pair.theta (pair.theta.symm x)).1 hSource₁
                (pair.theta (pair.theta.symm x)).2 := hθCone.symm
          _ = localCone _ (pair.theta.symm x).1 hSource₀
                (pair.theta.symm x).2 :=
              (pair.cone_preserved (pair.theta.symm x)).symm
      controlled_displacement := by
        intro x
        obtain ⟨beta, hbeta, hmap⟩ :=
          pair.controlled_displacement (pair.theta.symm x)
        let betaNeg : ControlledDisplacement C :=
          ⟨-(beta : Tiling.Plane),
            C.coordinateSpace.neg_mem beta.2.1,
            C.coordinateSpace.neg_mem beta.2.2⟩
        have hbetaValue : (betaNeg : Tiling.Plane) =
            (pair.theta.symm x).1 - x.1 := by
          change -(beta : Tiling.Plane) = _
          calc
            -(beta : Tiling.Plane) =
                -((pair.theta (pair.theta.symm x)).1 -
                  (pair.theta.symm x).1) := congrArg Neg.neg hbeta
            _ = (pair.theta.symm x).1 - x.1 := by simp
        have hmapNeg : mapPoint phi betaNeg = -mapPoint phi beta := by
          have hRe :
              (⟨-(beta : Tiling.Plane).re,
                C.coordinateSpace.neg_mem beta.2.1⟩ : C.coordinateSpace) =
                -⟨(beta : Tiling.Plane).re, beta.2.1⟩ := Subtype.ext rfl
          have hIm :
              (⟨-(beta : Tiling.Plane).im,
                C.coordinateSpace.neg_mem beta.2.2⟩ : C.coordinateSpace) =
                -⟨(beta : Tiling.Plane).im, beta.2.2⟩ := Subtype.ext rfl
          apply Complex.ext
          · simp only [mapPoint, betaNeg, Complex.add_re, Complex.mul_re,
              Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
              Complex.I_im, Complex.neg_re, mul_zero]
            rw [hRe]
            simp [mapScalar]
          · simp only [mapPoint, betaNeg, Complex.add_im, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
              Complex.I_im, Complex.neg_im, mul_zero, mul_one, zero_add]
            rw [hIm]
            simp [mapScalar]
        refine ⟨betaNeg, hbetaValue, ?_⟩
        rw [hmapNeg, hmap]
    }
    have hInverse := actualProperVertexPair_shortStep_displacement
      inversePair P hphi (pair.theta u) (pair.theta v) hTarget.1 hTarget.2
    calc
      (pair.theta v).1 - (pair.theta u).1 =
          (inversePair.theta (pair.theta v)).1 -
            (inversePair.theta (pair.theta u)).1 := hInverse.symm
      _ = v.1 - u.1 := by simp [inversePair]

/-!
Compare a consecutive edge of the two actual normalized wall traces.
Holes use projected source connectivity and density; occupied gaps use the
actual component mass codes. All controls below are private producer outputs.
-/

private theorem actualPair_consecutiveWallEdge_displacement
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S₀ S₁ : Set ↥C.centres}
    {hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀))}
    {hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁))}
    {hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))}
    {hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))}
    {eta : Tiling.Plane} {axis : Axis} {A : NormalizedGenericSection C axis}
    (pair : ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta)
    (P : FLCControlPackage C) (hphi : IsEpsilonApproximation C P.threshold phi)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (E₀ : AllEndpointWeakOrderTransport phi D Tphi axis S₀ A)
    (E₁ : AllEndpointWeakOrderTransport phi D Tphi axis S₁ A)
    (u v : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))))
    (hwall₀ : axis.transverseCoord u.1 = axis.transverseCoord v.1)
    (hwall₁ : axis.transverseCoord (pair.theta u).1 =
      axis.transverseCoord (pair.theta v).1)
    (hu₀ : axis.coord u.1 - A.origin ∈
      frontier (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀)))))
    (hv₀ : axis.coord v.1 - A.origin ∈
      frontier (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀)))))
    (hu₁ : axis.coord (pair.theta u).1 - A.origin ∈
      frontier (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₁)))))
    (hv₁ : axis.coord (pair.theta v).1 - A.origin ∈
      frontier (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₁)))))
    (horder₀ : axis.coord u.1 - A.origin < axis.coord v.1 - A.origin)
    (horder₁ : axis.coord (pair.theta u).1 - A.origin <
      axis.coord (pair.theta v).1 - A.origin)
    (hno₀ : ∀ x ∈ Set.Ioo (axis.coord u.1 - A.origin) (axis.coord v.1 - A.origin),
      x ∉ frontier (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀)))))
    (hno₁ : ∀ x ∈ Set.Ioo (axis.coord (pair.theta u).1 - A.origin)
        (axis.coord (pair.theta v).1 - A.origin),
      x ∉ frontier (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₁)))))
    {G : ℝ}
    (originalLinked₀ : Linked G (Subtype.val '' S₀))
    (originalLinked₁ : Linked G (Subtype.val '' S₁))
    (hMargin : G + P.localError < P.scale / 2)
    (hdensity₀ : ∀ x : ℝ, ∃ y ∈ axis.coord '' (Subtype.val '' S₀),
      x - G < y ∧ y < x + G)
    (hdensity₁ : ∀ x : ℝ, ∃ y ∈ axis.coord '' (Subtype.val '' S₁),
      x - G < y ∧ y < x + G)
    (hpacking₀ : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S₀)))
    (hpacking₁ : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S₁)))
    (hline₀ : ∃ c, ∀ s ∈ Subtype.val '' S₀, axis.transverseCoord s = c)
    (hline₁ : ∃ c, ∀ s ∈ Subtype.val '' S₁, axis.transverseCoord s = c)
    {R : ℝ} (massExpression : FiniteCombinationData C R)
    (corrections : Finset (FiniteCombinationData C R))
    (hCodes : ∀ {S : Set Tiling.Plane}, S ⊆ C.centres →
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements S) →
      (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) →
      ∀ J : BoundedOccupiedTraceComponent A S,
        ∃ code : ComponentMassCode A S J R, code.correction ∈ corrections)
    (W K : ℕ) (B mu : ℝ)
    (hmassExpression : massExpression.value = A.massScalar)
    (hmassWeight : massExpression.weight ≤ W)
    (hmassBound : A.mass < B)
    (hcorrections : ∀ E ∈ corrections,
      E.weight ≤ W ∧ |(E.value : ℝ)| < B / 2)
    (hK : 4 * B / A.mass < K) (hmu : 0 < mu)
    (hseparate : ∀ (q : ℤ) (c c' : FiniteCombinationData C R),
      q.natAbs < K → c ∈ corrections → c' ∈ corrections →
      (q : ℝ) * A.mass + c.value - c'.value ≠ 0 →
      mu ≤ |(q : ℝ) * A.mass + c.value - c'.value|)
    (hR : R < P.controlRadius)
    (hscale : ((K : ℝ) + 2) * (W : ℝ) / P.scale <
      min (A.mass / 2) (min (B / 2) mu)) :
    (pair.theta v).1 - (pair.theta u).1 = v.1 - u.1 := by
  have hsliceDistance (q x y : ℝ) :
      dist (FilledSliceChains.slicePoint axis q x)
        (FilledSliceChains.slicePoint axis q y) = |x - y| := by
    cases axis with
    | horizontal => exact outerWallPoint_dist_horizontal q y x
    | vertical => exact outerWallPoint_dist_vertical q y x
  have hprojectedLinked (S : Set Tiling.Plane) (hLinked : Linked G S) :
      Linked G (FilledSliceChains.slicePoint axis 0 '' (axis.coord '' S)) := by
    let f : Tiling.Plane → Tiling.Plane :=
      fun z => FilledSliceChains.slicePoint axis 0 (axis.coord z)
    have hImage : f '' S = FilledSliceChains.slicePoint axis 0 '' (axis.coord '' S) := by
      rw [Set.image_image]
    rw [← hImage]
    refine ⟨hLinked.1.image f, ?_⟩
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
    have hmap : ∀ {s t : Tiling.Plane},
        Relation.ReflTransGen
          (fun x y : Tiling.Plane => x ∈ S ∧ y ∈ S ∧ dist x y < G) s t →
        Relation.ReflTransGen
          (fun x y : Tiling.Plane => x ∈ f '' S ∧ y ∈ f '' S ∧ dist x y < G)
          (f s) (f t) := by
      intro s t hpath
      induction hpath with
      | refl => exact Relation.ReflTransGen.refl
      | @tail t w _hpath hedge ih =>
          refine ih.tail ⟨⟨t, hedge.1, rfl⟩, ⟨w, hedge.2.1, rfl⟩, ?_⟩
          have hdist : dist (f t) (f w) = |axis.coord t - axis.coord w| :=
            hsliceDistance 0 (axis.coord t) (axis.coord w)
          rw [hdist]
          exact lt_of_le_of_lt (sourceGeometry_coord_abs_le axis t w) hedge.2.2
    exact hmap (hLinked.2 s hs t ht)
  have hAopen : IsOpen A.carrier := by
    rw [A.carrier_eq]
    exact A.raw.presentation.isOpen.vadd (-A.origin)
  have hAnonempty : A.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := A.raw.nonempty
    rw [A.carrier_eq]
    exact ⟨-A.origin + x, x, hx, rfl⟩
  have hAfinite : OneDimensional.IsFiniteIntervalRegion A.carrier := by
    refine ⟨A.raw.presentation.n,
      (fun i => A.raw.presentation.left i - A.origin),
      (fun i => A.raw.presentation.right i - A.origin), ?_, ?_⟩
    · intro i
      linarith [A.raw.presentation.lt i]
    · rw [A.carrier_eq]
      ext x
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg,
        A.raw.presentation.union_eq, Set.mem_iUnion, Set.mem_Ioo]
      constructor
      · rintro ⟨i, hleft, hright⟩
        exact ⟨i, by constructor <;> linarith⟩
      · rintro ⟨i, hleft, hright⟩
        exact ⟨i, by constructor <;> linarith⟩
  have hpoint (p : Tiling.Plane) : p =
      FilledSliceChains.slicePoint axis (axis.transverseCoord p) (axis.coord p) := by
    cases axis <;> apply Complex.ext <;>
      simp [FilledSliceChains.slicePoint, Axis.coord, Axis.transverseCoord]
  have hwallDistance (p q : Tiling.Plane)
      (hwall : axis.transverseCoord p = axis.transverseCoord q) :
      dist p q = |axis.coord p - axis.coord q| := by
    calc
      dist p q = dist
          (FilledSliceChains.slicePoint axis (axis.transverseCoord p) (axis.coord p))
          (FilledSliceChains.slicePoint axis (axis.transverseCoord q) (axis.coord q)) :=
        congrArg₂ dist (hpoint p) (hpoint q)
      _ = |axis.coord p - axis.coord q| := by
        rw [← hwall]
        exact hsliceDistance _ _ _
  have horderedWallDistance (p q : Tiling.Plane)
      (hwall : axis.transverseCoord p = axis.transverseCoord q)
      (horder : axis.coord p - A.origin < axis.coord q - A.origin) :
      dist p q = (axis.coord q - A.origin) - (axis.coord p - A.origin) := by
    rw [hwallDistance p q hwall, abs_of_nonpos (by linarith)]
    ring
  have hwidth₀ := horderedWallDistance u.1 v.1 hwall₀ horder₀
  have hwidth₁ := horderedWallDistance (pair.theta u).1 (pair.theta v).1 hwall₁ horder₁
  rcases frontierGap_hole_or_boundedComponent
    (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀))))
    isOpen_interior horder₀ hu₀ hv₀ hno₀ with hhole₀ | hoccupied₀
  · have hbound := noGap_traceHole_bounded axis hAopen hAnonempty hAfinite
      (originalLinked₀.1.image axis.coord) hdensity₀
      (hprojectedLinked _ originalLinked₀) horder₀ hhole₀
    have hdist : dist u.1 v.1 ≤ G := by rw [hwidth₀]; exact hbound
    apply actualProperVertexPair_shortStep_displacement_either pair P hphi u v
    exact Or.inl ⟨by linarith [P.localError_pos, P.scale_pos], by linarith⟩
  · rcases frontierGap_hole_or_boundedComponent
      (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₁))))
      isOpen_interior horder₁ hu₁ hv₁ hno₁ with hhole₁ | hoccupied₁
    · have hbound := noGap_traceHole_bounded axis hAopen hAnonempty hAfinite
        (originalLinked₁.1.image axis.coord) hdensity₁
        (hprojectedLinked _ originalLinked₁) horder₁ hhole₁
      have hdist : dist (pair.theta u).1 (pair.theta v).1 ≤ G := by
        rw [hwidth₁]
        exact hbound
      apply actualProperVertexPair_shortStep_displacement_either pair P hphi u v
      exact Or.inr ⟨by linarith [P.localError_pos, P.scale_pos], by linarith⟩
    · let J₀ : BoundedOccupiedTraceComponent A (Subtype.val '' S₀) := {
        left := axis.coord u.1 - A.origin
        right := axis.coord v.1 - A.origin
        ordered := horder₀
        component_eq := hoccupied₀.1
        midpoint_mem := hoccupied₀.2 }
      let J₁ : BoundedOccupiedTraceComponent A (Subtype.val '' S₁) := {
        left := axis.coord (pair.theta u).1 - A.origin
        right := axis.coord (pair.theta v).1 - A.origin
        ordered := horder₁
        component_eq := hoccupied₁.1
        midpoint_mem := hoccupied₁.2 }
      have hsubset₀ : Subtype.val '' S₀ ⊆ C.centres := by
        rintro s ⟨t, _ht, rfl⟩
        exact t.2
      have hsubset₁ : Subtype.val '' S₁ ⊆ C.centres := by
        rintro s ⟨t, _ht, rfl⟩
        exact t.2
      obtain ⟨code₀, hcode₀⟩ := hCodes hsubset₀ hpacking₀ hline₀ J₀
      obtain ⟨code₁, hcode₁⟩ := hCodes hsubset₁ hpacking₁ hline₁ J₁
      have hlength := actualPair_boundedComponent_displacement pair hTphi E₀ E₁ u v
        J₀ J₁ code₀ code₁ rfl rfl rfl rfl massExpression corrections W K B mu
        hmassExpression hmassWeight A.mass_pos hmassBound hcorrections hK hmu hseparate
        P hR hscale hphi hcode₀ hcode₁
      change (axis.coord v.1 - A.origin) - (axis.coord u.1 - A.origin) =
        (axis.coord (pair.theta v).1 - A.origin) -
          (axis.coord (pair.theta u).1 - A.origin) at hlength
      have hlong : axis.coord (pair.theta v).1 - axis.coord (pair.theta u).1 =
          axis.coord v.1 - axis.coord u.1 := by linarith
      cases axis with
      | horizontal =>
          apply Complex.ext
          · change (pair.theta v).1.re - (pair.theta u).1.re = v.1.re - u.1.re
            exact hlong
          · change (pair.theta v).1.im - (pair.theta u).1.im = v.1.im - u.1.im
            change u.1.im = v.1.im at hwall₀
            change (pair.theta u).1.im = (pair.theta v).1.im at hwall₁
            linarith
      | vertical =>
          apply Complex.ext
          · change (pair.theta v).1.re - (pair.theta u).1.re = v.1.re - u.1.re
            change u.1.re = v.1.re at hwall₀
            change (pair.theta u).1.re = (pair.theta v).1.re at hwall₁
            linarith
          · change (pair.theta v).1.im - (pair.theta u).1.im = v.1.im - u.1.im
            exact hlong

private theorem actualProperVertexPair_shortStep_preserves_displacement
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S₀ S₁ : Set ↥C.centres}
    {hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀))}
    {hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁))}
    {hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))}
    {hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))}
    {eta beta : Tiling.Plane}
    (pair : ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta)
    (P : FLCControlPackage C)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (u v : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))))
    (hDistance : dist u.1 v.1 < P.scale)
    (hMargin : dist u.1 v.1 + P.localError < P.scale / 2)
    (hAnchor : (pair.theta u).1 - u.1 = beta) :
    (pair.theta v).1 - v.1 = beta := by
  have hEdge := actualProperVertexPair_shortStep_displacement
    pair P hphi u v hDistance hMargin
  calc
    (pair.theta v).1 - v.1 =
        ((pair.theta v).1 - (pair.theta u).1) +
          ((pair.theta u).1 - v.1) := by abel
    _ = (v.1 - u.1) + ((pair.theta u).1 - v.1) := by rw [hEdge]
    _ = (pair.theta u).1 - u.1 := by abel
    _ = beta := hAnchor

private theorem actualProperVertexPair_transverse_difference
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S₀ S₁ : Set ↥C.centres}
    {hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀))}
    {hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁))}
    {hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))}
    {hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))}
    {eta : Tiling.Plane}
    (pair : ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta)
    (P : FLCControlPackage C)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (hDiam : Metric.diam C.region.support < P.controlRadius)
    (axis : Axis)
    (hline₀ : ∃ c, ∀ s ∈ Subtype.val '' S₀,
      axis.transverseCoord s = c)
    (hline₁ : ∃ c, ∀ s ∈ Subtype.val '' S₁,
      axis.transverseCoord s = c)
    (u v : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀)))) :
    axis.transverseCoord ((pair.theta v).1 - (pair.theta u).1) =
      axis.transverseCoord (v.1 - u.1) := by
  classical
  obtain ⟨c₀, hc₀⟩ := hline₀
  obtain ⟨c₁, hc₁⟩ := hline₁
  obtain ⟨w₀u, s₀u, hu₀⟩ := pair.source_label₀ u
  obtain ⟨w₀v, s₀v, hv₀⟩ := pair.source_label₀ v
  obtain ⟨w₁u, s₁u, hu₁⟩ := pair.source_label₁ u
  obtain ⟨w₁v, s₁v, hv₁⟩ := pair.source_label₁ v
  let label (w : ↥C.region.vertices) (s : ↥C.centres) :
      ↥C.translatedVertices :=
    ⟨w.1 + s.1, Set.mem_add.mpr ⟨w.1, w.2, s.1, s.2, rfl⟩⟩
  let a₀u := label w₀u s₀u.1
  let a₀v := label w₀v s₀v.1
  let a₁u := label w₁u s₁u.1
  let a₁v := label w₁v s₁v.1
  have hlabelMap (w : ↥C.region.vertices) (s : ↥C.centres) :
      mapTranslatedVertex phi (label w s) =
        mapPoint phi (C.vertexPoint w.1 w.2) +
          mapPoint phi (C.centrePoint s.1 s.2) := by
    rw [mapTranslatedVertex]
    have hpoint : C.translatedVertexPoint (label w s) =
        ⟨w.1 + s.1,
          C.coordinateSpace.add_mem (C.vertex_re_mem w.1 w.2)
            (C.centre_re_mem s.1 s.2),
          C.coordinateSpace.add_mem (C.vertex_im_mem w.1 w.2)
            (C.centre_im_mem s.1 s.2)⟩ := by
      apply Subtype.ext
      rfl
    rw [hpoint]
    exact mapPoint_add_controlled phi (C.vertexPoint w.1 w.2)
      (C.centrePoint s.1 s.2)
  have hshift (x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))))
      (a₀ a₁ : ↥C.translatedVertices)
      (ha₀ : (a₀ : Tiling.Plane) = x.1)
      (ha₁ : (a₁ : Tiling.Plane) = (pair.theta x).1) :
      mapTranslatedVertex phi a₁ - mapTranslatedVertex phi a₀ = eta := by
    obtain ⟨beta, hbeta, hbetaMap⟩ := pair.controlled_displacement x
    let betaDiff : ControlledDisplacement C :=
      ⟨(C.translatedVertexPoint a₁).1 - (C.translatedVertexPoint a₀).1,
        C.coordinateSpace.sub_mem (C.translatedVertexPoint a₁).2.1
          (C.translatedVertexPoint a₀).2.1,
        C.coordinateSpace.sub_mem (C.translatedVertexPoint a₁).2.2
          (C.translatedVertexPoint a₀).2.2⟩
    have hdiff : (betaDiff : Tiling.Plane) = (pair.theta x).1 - x.1 := by
      change (a₁ : Tiling.Plane) - (a₀ : Tiling.Plane) = _
      rw [ha₁, ha₀]
    have hbetaEq : beta = betaDiff := Subtype.ext (hbeta.trans hdiff.symm)
    have hmapDiff : mapPoint phi betaDiff =
        mapTranslatedVertex phi a₁ - mapTranslatedVertex phi a₀ := by
      change mapPoint phi ⟨
        (C.translatedVertexPoint a₁).1 - (C.translatedVertexPoint a₀).1,
        C.coordinateSpace.sub_mem (C.translatedVertexPoint a₁).2.1
          (C.translatedVertexPoint a₀).2.1,
        C.coordinateSpace.sub_mem (C.translatedVertexPoint a₁).2.2
          (C.translatedVertexPoint a₀).2.2⟩ = _
      simpa only [mapTranslatedVertex] using
        mapPoint_sub_controlled phi (C.translatedVertexPoint a₁)
          (C.translatedVertexPoint a₀)
    calc
      mapTranslatedVertex phi a₁ - mapTranslatedVertex phi a₀ =
          mapPoint phi betaDiff := hmapDiff.symm
      _ = mapPoint phi beta := by rw [hbetaEq.symm]
      _ = eta := hbetaMap
  have hshift₀u : mapTranslatedVertex phi a₁u -
      mapTranslatedVertex phi a₀u = eta := by
    exact hshift u a₀u a₁u (by simp [a₀u, label, hu₀])
      (by simp [a₁u, label, hu₁])
  have hshift₀v : mapTranslatedVertex phi a₁v -
      mapTranslatedVertex phi a₀v = eta := by
    exact hshift v a₀v a₁v (by simp [a₀v, label, hv₀]) (by simp [a₁v, label, hv₁])
  have himageEdge : mapTranslatedVertex phi a₁v - mapTranslatedVertex phi a₁u =
      mapTranslatedVertex phi a₀v - mapTranslatedVertex phi a₀u := by
    rw [show mapTranslatedVertex phi a₁v = eta + mapTranslatedVertex phi a₀v by
          calc
            mapTranslatedVertex phi a₁v =
                (mapTranslatedVertex phi a₁v - mapTranslatedVertex phi a₀v) +
                  mapTranslatedVertex phi a₀v := by abel
            _ = _ := by rw [hshift₀v],
        show mapTranslatedVertex phi a₁u = eta + mapTranslatedVertex phi a₀u by
          calc
            mapTranslatedVertex phi a₁u =
                (mapTranslatedVertex phi a₁u - mapTranslatedVertex phi a₀u) +
                  mapTranslatedVertex phi a₀u := by abel
            _ = _ := by rw [hshift₀u]]
    abel
  have hcenterMap (s t : ↥C.centres)
      (hst : axis.transverseCoord s.1 = axis.transverseCoord t.1) :
      axis.transverseCoord
        (mapPoint phi (C.centrePoint s.1 s.2) -
          mapPoint phi (C.centrePoint t.1 t.2)) = 0 := by
    cases axis with
    | horizontal =>
        have hst' : s.1.im = t.1.im := hst
        have hscalar :
            (⟨s.1.im, C.centre_im_mem s.1 s.2⟩ : C.coordinateSpace) =
              ⟨t.1.im, C.centre_im_mem t.1 t.2⟩ := Subtype.ext hst'
        have hscalarMap : mapScalar phi
            (⟨s.1.im, C.centre_im_mem s.1 s.2⟩ : C.coordinateSpace) =
            mapScalar phi
              (⟨t.1.im, C.centre_im_mem t.1 t.2⟩ : C.coordinateSpace) :=
          congrArg (mapScalar phi) hscalar
        simp [Axis.transverseCoord, mapPoint, ApproximationContext.centrePoint,
          hscalarMap]
    | vertical =>
        have hst' : s.1.re = t.1.re := hst
        have hscalar :
            (⟨s.1.re, C.centre_re_mem s.1 s.2⟩ : C.coordinateSpace) =
              ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := Subtype.ext hst'
        have hscalarMap : mapScalar phi
            (⟨s.1.re, C.centre_re_mem s.1 s.2⟩ : C.coordinateSpace) =
            mapScalar phi
              (⟨t.1.re, C.centre_re_mem t.1 t.2⟩ : C.coordinateSpace) :=
          congrArg (mapScalar phi) hscalar
        simp [Axis.transverseCoord, mapPoint, ApproximationContext.centrePoint,
          hscalarMap]
  have hs₀line : axis.transverseCoord s₀v.1.1 =
      axis.transverseCoord s₀u.1.1 := by
    exact hc₀ _ ⟨s₀v.1, s₀v.2, rfl⟩ |>.trans
      (hc₀ _ ⟨s₀u.1, s₀u.2, rfl⟩).symm
  have hs₁line : axis.transverseCoord s₁v.1.1 =
      axis.transverseCoord s₁u.1.1 := by
    exact hc₁ _ ⟨s₁v.1, s₁v.2, rfl⟩ |>.trans
      (hc₁ _ ⟨s₁u.1, s₁u.2, rfl⟩).symm
  have hcenter₀ := hcenterMap s₀v.1 s₀u.1 hs₀line
  have hcenter₁ := hcenterMap s₁v.1 s₁u.1 hs₁line
  have hmappedIntrinsic :
      axis.transverseCoord
          (mapPoint phi (C.vertexPoint w₁v.1 w₁v.2) -
            mapPoint phi (C.vertexPoint w₁u.1 w₁u.2)) =
        axis.transverseCoord
          (mapPoint phi (C.vertexPoint w₀v.1 w₀v.2) -
            mapPoint phi (C.vertexPoint w₀u.1 w₀u.2)) := by
    have h := congrArg (axis.transverseCoord ·) himageEdge
    rw [show a₁v = label w₁v s₁v.1 by rfl,
        show a₁u = label w₁u s₁u.1 by rfl,
        show a₀v = label w₀v s₀v.1 by rfl,
        show a₀u = label w₀u s₀u.1 by rfl,
        hlabelMap, hlabelMap, hlabelMap, hlabelMap] at h
    have htransAdd (x y : Tiling.Plane) :
        axis.transverseCoord (x + y) =
          axis.transverseCoord x + axis.transverseCoord y := by
      cases axis <;> simp [Axis.transverseCoord]
    have htransSub (x y : Tiling.Plane) :
        axis.transverseCoord (x - y) =
          axis.transverseCoord x - axis.transverseCoord y := by
      cases axis <;> simp [Axis.transverseCoord]
    rw [show mapPoint phi (C.vertexPoint w₁v.1 w₁v.2) +
          mapPoint phi (C.centrePoint s₁v.1.1 s₁v.1.2) -
            (mapPoint phi (C.vertexPoint w₁u.1 w₁u.2) +
              mapPoint phi (C.centrePoint s₁u.1.1 s₁u.1.2)) =
          (mapPoint phi (C.vertexPoint w₁v.1 w₁v.2) -
              mapPoint phi (C.vertexPoint w₁u.1 w₁u.2)) +
            (mapPoint phi (C.centrePoint s₁v.1.1 s₁v.1.2) -
              mapPoint phi (C.centrePoint s₁u.1.1 s₁u.1.2)) by abel,
        show mapPoint phi (C.vertexPoint w₀v.1 w₀v.2) +
          mapPoint phi (C.centrePoint s₀v.1.1 s₀v.1.2) -
            (mapPoint phi (C.vertexPoint w₀u.1 w₀u.2) +
              mapPoint phi (C.centrePoint s₀u.1.1 s₀u.1.2)) =
            (mapPoint phi (C.vertexPoint w₀v.1 w₀v.2) -
              mapPoint phi (C.vertexPoint w₀u.1 w₀u.2)) +
            (mapPoint phi (C.centrePoint s₀v.1.1 s₀v.1.2) -
              mapPoint phi (C.centrePoint s₀u.1.1 s₀u.1.2)) by abel] at h
    simp_rw [htransAdd] at h
    rw [hcenter₁, hcenter₀] at h
    simp_rw [htransSub] at h ⊢
    linarith
  let z₀u : ↥C.translatedVertices :=
    ⟨w₀u.1, Set.mem_add.mpr ⟨w₀u.1, w₀u.2, 0,
      C.zero_mem_centres, by simp⟩⟩
  let z₀v : ↥C.translatedVertices :=
    ⟨w₀v.1, Set.mem_add.mpr ⟨w₀v.1, w₀v.2, 0,
      C.zero_mem_centres, by simp⟩⟩
  let z₁u : ↥C.translatedVertices :=
    ⟨w₁u.1, Set.mem_add.mpr ⟨w₁u.1, w₁u.2, 0,
      C.zero_mem_centres, by simp⟩⟩
  let z₁v : ↥C.translatedVertices :=
    ⟨w₁v.1, Set.mem_add.mpr ⟨w₁v.1, w₁v.2, 0,
      C.zero_mem_centres, by simp⟩⟩
  have hvSupport (w : ↥C.region.vertices) : (w : Tiling.Plane) ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (Tiling.AxisParallel.IntrinsicVertices.region_vertices_subset_frontier C.region w.2)
  have hdiamPair (x y : ↥C.region.vertices) :
      dist (x : Tiling.Plane) y ≤ Metric.diam C.region.support :=
    Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded (hvSupport x) (hvSupport y)
  have hcontrol₀ : dist (z₀v : Tiling.Plane) z₀u < P.controlRadius := by
    apply lt_of_le_of_lt _ hDiam
    simpa only [z₀v, z₀u] using hdiamPair w₀v w₀u
  have hcontrol₁ : dist (z₁v : Tiling.Plane) z₁u < P.controlRadius := by
    apply lt_of_le_of_lt _ hDiam
    simpa only [z₁v, z₁u] using hdiamPair w₁v w₁u
  have hzeroMap (w : ↥C.region.vertices) (z : ↥C.translatedVertices)
      (hz : (z : Tiling.Plane) = w.1) :
      mapTranslatedVertex phi z = mapPoint phi (C.vertexPoint w.1 w.2) := by
    rw [mapTranslatedVertex]
    have hp : C.translatedVertexPoint z = C.vertexPoint w.1 w.2 := by
      apply Subtype.ext
      exact hz
    rw [hp]
  have hcoordSwap (z : Tiling.Plane) :
      Axis.coord (Axis.swap axis) z = axis.transverseCoord z := by
    cases axis <;> rfl
  have hzeroImage :
      Axis.coord axis.swap
          (mapTranslatedVertex phi z₁v - mapTranslatedVertex phi z₁u) =
        Axis.coord axis.swap
          (mapTranslatedVertex phi z₀v - mapTranslatedVertex phi z₀u) := by
    rw [hzeroMap w₁v z₁v (by simp [z₁v]),
      hzeroMap w₁u z₁u (by simp [z₁u]),
      hzeroMap w₀v z₀v (by simp [z₀v]),
      hzeroMap w₀u z₀u (by simp [z₀u]), hcoordSwap, hcoordSwap]
    exact hmappedIntrinsic
  have hreflect := deformation_reflectsFiniteValues P phi hphi (Axis.swap axis)
    z₁v z₁u z₀v z₀u hcontrol₁ hcontrol₀
  have hsourceIntrinsic :
      Axis.coord axis.swap ((z₁v : Tiling.Plane) - z₁u) =
        Axis.coord axis.swap ((z₀v : Tiling.Plane) - z₀u) :=
    hreflect.2.2 hzeroImage
  have hgoal :
      axis.transverseCoord ((pair.theta v).1 - (pair.theta u).1) =
        axis.transverseCoord (v.1 - u.1) := by
    rw [show (pair.theta v).1 = w₁v.1 + s₁v.1.1 by exact hv₁,
        show (pair.theta u).1 = w₁u.1 + s₁u.1.1 by exact hu₁,
        show v.1 = w₀v.1 + s₀v.1.1 by exact hv₀,
        show u.1 = w₀u.1 + s₀u.1.1 by exact hu₀]
    have hs0 : axis.transverseCoord s₀v.1.1 = axis.transverseCoord s₀u.1.1 := hs₀line
    have hs1 : axis.transverseCoord s₁v.1.1 = axis.transverseCoord s₁u.1.1 := hs₁line
    have hvertex : axis.transverseCoord (w₁v.1 - w₁u.1) =
        axis.transverseCoord (w₀v.1 - w₀u.1) := by
      have hsource' := hsourceIntrinsic
      rw [hcoordSwap, hcoordSwap] at hsource'
      simpa only [z₁v, z₁u, z₀v, z₀u] using hsource'
    cases axis <;>
      simp only [Axis.transverseCoord, Complex.add_im, Complex.add_re,
        Complex.sub_im, Complex.sub_re] at hvertex hs0 hs1 ⊢ <;>
      linarith
  exact hgoal

private theorem aligned_noncolumn_properVertices_nonempty
    {C : ApproximationContext.{0}} {S : Set Tiling.Plane} (axis : Axis)
    (hColumnable : ∃ Col, IsCenterColumn axis C.region Col)
    (hS : S.Nonempty)
    (hpack : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements S))
    (hline : ∃ c, ∀ s ∈ S, axis.transverseCoord s = c)
    (hNotColumn : ¬ IsCenterColumn axis C.region S) :
    (properVertices (regularSupport C.region S)).Nonempty := by
  by_contra hnone
  have hEmpty : properVertices (regularSupport C.region S) = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hnone
  obtain ⟨s, hs⟩ := hS
  let U := (-s) +ᵥ S
  have hzero : (0 : Tiling.Plane) ∈ U := by
    exact Set.mem_vadd_set.mpr ⟨s, hs, by simp⟩
  have hlineU : ∀ u ∈ U, axis.transverseCoord u = 0 := by
    obtain ⟨c, hc⟩ := hline
    rintro u ⟨t, ht, rfl⟩
    have hsCoord := hc s hs
    have htCoord := hc t ht
    cases axis <;> simp only [vadd_eq_add, Axis.transverseCoord, Complex.add_re,
      Complex.add_im, Complex.neg_re, Complex.neg_im] at * <;> linarith
  have hpackU : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements U) := packing_translate hpack (-s)
  have hEmptyU : properVertices (regularSupport C.region U) = ∅ := by
    dsimp [U]
    rw [regularSupport_vadd, properVertices_vadd_eq, hEmpty]
    simp
  obtain ⟨A, wall, ε, ⟨hA⟩, hAne, hε, _hLower, hgerm⟩ :=
    exists_axis_outerWallData C.region axis
  have hno : ∀ z ∈ properVertices (regularSupport C.region U),
      axis.transverseCoord z ≠ wall := by
    intro z hz
    rw [hEmptyU] at hz
    exact hz.elim
  have hfull := outerWall_trace_full axis hA.isOpen hAne hzero wall ε hε
    (hgerm U hlineU) hno
  have hColumnU := fullGenericSection_forcesCenterColumn axis hpackU
    ⟨0, hzero⟩ ⟨0, hlineU⟩ hColumnable A (axis.coord '' U) hA rfl hfull
  apply hNotColumn
  refine ⟨hpack, ⟨s, hs⟩, hline, ?_⟩
  intro a
  have hperiod := hColumnU.2.2.2 a
  change (match axis with
      | .horizontal => (a : ℂ)
      | .vertical => (a : ℂ) * Complex.I) +ᵥ regularSupport C.region U =
    regularSupport C.region U at hperiod
  dsimp [U] at hperiod
  rw [regularSupport_vadd] at hperiod
  have htranslated := congrArg (fun X : Set Tiling.Plane => s +ᵥ X) hperiod
  rw [vadd_vadd, vadd_vadd, vadd_vadd] at htranslated
  cases axis with
  | horizontal =>
      have hsum : s + (a : ℂ) + -s = (a : ℂ) := by abel
      rw [hsum, add_neg_cancel, zero_vadd] at htranslated
      exact htranslated
  | vertical =>
      have hsum : s + (a : ℂ) * Complex.I + -s = (a : ℂ) * Complex.I := by abel
      rw [hsum, add_neg_cancel, zero_vadd] at htranslated
      exact htranslated

private theorem selectedOuterWall_properSlice_iff
    (K : Region) (axis : Axis) {S : Set Tiling.Plane}
    {A : Set ℝ} {wall ε : ℝ} (hε : 0 < ε)
    (hgerm : regularSupport K S ∩
      {z | axis.transverseCoord z ∈ Set.Ioo (wall - ε) (wall + ε)} =
      {z | axis.transverseCoord z ∈ Set.Ioo wall (wall + ε) ∧
        axis.coord z ∈ interior (closure (A + axis.coord '' S))}) :
    ∀ y : ℝ,
      FilledSliceChains.slicePoint axis wall y ∈
          properVertices (regularSupport K S) ↔
        y ∈ frontier (interior (closure (A + axis.coord '' S))) := by
  intro y
  let W := interior (closure (A + axis.coord '' S))
  let p := FilledSliceChains.slicePoint axis wall y
  let D := regularSupport K S
  let P := outerWallProduct axis wall W
  have hWopen : IsOpen W := isOpen_interior
  have hpTrans : axis.transverseCoord p = wall := by
    cases axis <;> simp [p, FilledSliceChains.slicePoint, Axis.transverseCoord]
  have hpCoord : axis.coord p = y := by
    cases axis <;> simp [p, FilledSliceChains.slicePoint, Axis.coord]
  have hprod (z : Tiling.Plane) (hz : z ∈ Metric.ball p (ε / 2)) :
      z ∈ D ↔ z ∈ P := by
    have hcoord' : |axis.transverseCoord z - wall| ≤ dist z p := by
      cases axis with
      | horizontal =>
          have hc := sourceGeometry_coord_abs_le Axis.vertical z p
          rw [← hpTrans]
          simpa [Axis.coord, Axis.transverseCoord] using hc
      | vertical =>
          have hc := sourceGeometry_coord_abs_le Axis.horizontal z p
          rw [← hpTrans]
          simpa [Axis.coord, Axis.transverseCoord] using hc
    have hd : dist z p < ε / 2 := Metric.mem_ball.mp hz
    have hcoordAbs : |axis.transverseCoord z - wall| < ε :=
      lt_of_le_of_lt hcoord' (by linarith)
    have hband :
        axis.transverseCoord z ∈ Set.Ioo (wall - ε) (wall + ε) := by
      rw [abs_lt] at hcoordAbs
      constructor <;> linarith
    have hg := congrArg (fun X : Set Tiling.Plane => z ∈ X)
      hgerm
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hg
    have hslice :
        z ∈ D ↔
          axis.transverseCoord z ∈ Set.Ioo wall (wall + ε) ∧
            axis.coord z ∈ W := by
      simpa [W, hband] using hg
    have hproduct : z ∈ P ↔
        wall < axis.transverseCoord z ∧ axis.coord z ∈ W := by
      cases axis <;>
        simp [P, outerWallProduct, Axis.transverseCoord, Axis.coord,
          Complex.mem_reProdIm, Set.mem_Ioi, and_comm]
    rw [hslice, hproduct]
    constructor
    · rintro ⟨⟨hwall, hup⟩, hW⟩
      exact ⟨hwall, hW⟩
    · rintro ⟨hwall, hW⟩
      exact ⟨⟨hwall, hband.2⟩, hW⟩
  have hmem : ∀ᶠ z in 𝓝 p, (z ∈ D ↔ z ∈ P) := by
    apply Metric.mem_nhds_iff.2
    exact ⟨ε / 2, half_pos hε, hprod⟩
  have hsetEq : D =ᶠ[𝓝 p] P := hmem.mono fun _ hz => propext hz
  have hproper : p ∈ properVertices D ↔ p ∈ properVertices P :=
    isProperVertex_iff_of_eventuallyEq hsetEq
  constructor
  · intro hy
    have hpP : p ∈ properVertices P := hproper.mp hy
    have hyClosure : y ∈ closure W := by
      have hfront := hpP.1
      cases axis with
      | vertical =>
          change FilledSliceChains.slicePoint Axis.vertical wall y ∈
            frontier (outerWallProduct Axis.vertical wall W) at hfront
          rw [FilledSliceChains.slicePoint, outerWallProduct,
            Complex.frontier_reProdIm] at hfront
          rcases hfront with hleft | hright
          · have hcoordinates := Complex.mem_reProdIm.mp hleft
            have hyFront : y ∈ frontier W := by simpa using hcoordinates.2
            exact frontier_subset_closure hyFront
          · have hcoordinates := Complex.mem_reProdIm.mp hright
            simpa using hcoordinates.2
      | horizontal =>
          change FilledSliceChains.slicePoint Axis.horizontal wall y ∈
            frontier (outerWallProduct Axis.horizontal wall W) at hfront
          rw [FilledSliceChains.slicePoint, outerWallProduct,
            Complex.frontier_reProdIm] at hfront
          rcases hfront with hleft | hright
          · have hcoordinates := Complex.mem_reProdIm.mp hleft
            simpa using hcoordinates.1
          · have hcoordinates := Complex.mem_reProdIm.mp hright
            have hyFront : y ∈ frontier W := by simpa using hcoordinates.1
            exact frontier_subset_closure hyFront
    have hyNotW : y ∉ W := by
      intro hyW
      obtain ⟨r, hr, hball⟩ :=
        Metric.mem_nhds_iff.mp (hWopen.mem_nhds hyW)
      have hcoordNear : ∀ᶠ z in 𝓝 p, axis.coord z ∈ W := by
        apply Metric.mem_nhds_iff.2
        refine ⟨min (ε / 2) r, lt_min (half_pos hε) hr, ?_⟩
        intro z hz
        apply hball
        rw [Metric.mem_ball]
        have hcoordDist : dist (axis.coord z) y ≤ dist z p := by
          have hc := sourceGeometry_coord_abs_le axis z p
          rw [hpCoord] at hc
          simpa only [Real.dist_eq] using hc
        exact lt_of_le_of_lt hcoordDist (lt_of_lt_of_le
          (Metric.mem_ball.mp hz) (min_le_right _ _))
      have hstraight : Tiling.BoundaryLocallyStraightAt P p := by
        refine ⟨properVertexAxisLine axis p,
          (mem_properVertexAxisLine_iff axis p p).2 rfl, ?_, ?_⟩
        · rw [properVertexAxisLine, AffineSubspace.direction_mk']
          exact finrank_span_singleton (properVertexAxisVector_ne_zero axis)
        · filter_upwards [hcoordNear] with z hzW
          change z ∈ frontier P ↔ z ∈ properVertexAxisLine axis p
          have hnotFrontier : axis.coord z ∉ frontier W := by
            intro hzFrontier
            have hempty := hWopen.inter_frontier_eq
            have hmemInter : axis.coord z ∈ W ∩ frontier W := ⟨hzW, hzFrontier⟩
            simp only [hempty, Set.mem_empty_iff_false] at hmemInter
          have hzClosure : axis.coord z ∈ closure W := subset_closure hzW
          have hlocal : z ∈ frontier P ↔
              axis.transverseCoord z = wall := by
            cases axis with
            | horizontal =>
                have hnotFrontier' : z.re ∉ frontier W := hnotFrontier
                have hzClosure' : z.re ∈ closure W := hzClosure
                change z ∈ frontier
                  (outerWallProduct Axis.horizontal wall W) ↔ z.im = wall
                rw [outerWallProduct, Complex.frontier_reProdIm]
                constructor
                · intro hz
                  rcases hz with hleft | hright
                  · have hcoordinates := Complex.mem_reProdIm.mp hleft
                    have himWall : z.im ∈ frontier (Set.Ioi wall) :=
                      hcoordinates.2
                    simpa only [frontier_Ioi, Set.mem_singleton_iff] using himWall
                  · have hcoordinates := Complex.mem_reProdIm.mp hright
                    exact False.elim (hnotFrontier' hcoordinates.1)
                · intro him
                  change (z.re ∈ closure W ∧
                    z.im ∈ frontier (Set.Ioi wall)) ∨
                    (z.re ∈ frontier W ∧
                      z.im ∈ closure (Set.Ioi wall))
                  left
                  exact ⟨hzClosure', by simp [him]⟩
            | vertical =>
                have hnotFrontier' : z.im ∉ frontier W := hnotFrontier
                have hzClosure' : z.im ∈ closure W := hzClosure
                change z ∈ frontier
                  (outerWallProduct Axis.vertical wall W) ↔ z.re = wall
                rw [outerWallProduct, Complex.frontier_reProdIm]
                constructor
                · intro hz
                  rcases hz with hleft | hright
                  · have hcoordinates := Complex.mem_reProdIm.mp hleft
                    exact False.elim (hnotFrontier' hcoordinates.2)
                  · have hcoordinates := Complex.mem_reProdIm.mp hright
                    have hreWall : z.re ∈ frontier (Set.Ioi wall) :=
                      hcoordinates.1
                    simpa only [frontier_Ioi, Set.mem_singleton_iff] using hreWall
                · intro hre
                  change (z.re ∈ closure (Set.Ioi wall) ∧
                    z.im ∈ frontier W) ∨
                    (z.re ∈ frontier (Set.Ioi wall) ∧
                      z.im ∈ closure W)
                  right
                  exact ⟨by simp [hre], hzClosure'⟩
          rw [hlocal, mem_properVertexAxisLine_iff, hpTrans]
      exact hpP.2 hstraight
    rw [hWopen.frontier_eq]
    exact ⟨hyClosure, hyNotW⟩
  · intro hyW
    exact outerWall_frontier_subset_proper (half_pos hε) hprod hWopen hyW

private theorem selectedDatum_normalizedWall_proper_iff
    {C : ApproximationContext.{0}} {axis : Axis}
    {outerA : Set ℝ} {wall ε : ℝ} (hε : 0 < ε)
    (hgerm : ∀ U : Set Tiling.Plane,
      (∀ s ∈ U, axis.transverseCoord s = 0) →
        regularSupport C.region U ∩
            {z | axis.transverseCoord z ∈ Set.Ioo (wall - ε) (wall + ε)} =
          {z | axis.transverseCoord z ∈ Set.Ioo wall (wall + ε) ∧
            axis.coord z ∈ interior (closure (outerA + axis.coord '' U))})
    (A : NormalizedGenericSection C axis) (hraw : A.raw.rawCarrier = outerA)
    {S : Set Tiling.Plane} {c : ℝ}
    (hline : ∀ s ∈ S, axis.transverseCoord s = c)
    {u : Tiling.Plane} (hu : axis.transverseCoord u = wall + c) :
    u ∈ properVertices (regularSupport C.region S) ↔
      axis.coord u - A.origin ∈
        frontier (interior (closure (A.carrier + axis.coord '' S))) := by
  let q : Tiling.Plane := FilledSliceChains.slicePoint axis c 0
  let U : Set Tiling.Plane := -q +ᵥ S
  have hqCoord : axis.coord q = 0 := by
    cases axis <;> simp [q, FilledSliceChains.slicePoint, Axis.coord]
  have hcoordShift (s : Tiling.Plane) : axis.coord (-q + s) = axis.coord s := by
    cases axis with
    | horizontal =>
        change q.re = 0 at hqCoord
        change (-q + s).re = s.re
        simp [hqCoord]
    | vertical =>
        change q.im = 0 at hqCoord
        change (-q + s).im = s.im
        simp [hqCoord]
  have hlineU : ∀ s ∈ U, axis.transverseCoord s = 0 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Set.mem_vadd_set.mp hs
    have htLine := hline t ht
    cases axis <;>
      simp [q, FilledSliceChains.slicePoint, Axis.transverseCoord,
        vadd_eq_add] at htLine ⊢ <;> linarith
  have hImage : axis.coord '' U = axis.coord '' S := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨s, hs, rfl⟩ := Set.mem_vadd_set.mp ht
      exact ⟨s, hs, (hcoordShift s).symm⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨-q + s, ?_, hcoordShift s⟩
      exact ⟨s, hs, rfl⟩
  have hshiftPoint : -q + u =
      FilledSliceChains.slicePoint axis wall (axis.coord u) := by
    cases axis <;> apply Complex.ext <;>
      simp [q, FilledSliceChains.slicePoint, Axis.coord,
        Axis.transverseCoord] at hu ⊢ <;> linarith
  have hproperShift :
      (-q + u) ∈ properVertices (regularSupport C.region U) ↔
        u ∈ properVertices (regularSupport C.region S) := by
    dsimp only [U]
    rw [regularSupport_vadd, properVertices_vadd_eq,
      Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [vadd_eq_add, neg_neg, add_neg_cancel_left]
  have hslice := selectedOuterWall_properSlice_iff C.region axis hε
    (hgerm U hlineU) (axis.coord u)
  rw [hImage] at hslice
  rw [hshiftPoint] at hproperShift
  have hcarrierSum : A.carrier + axis.coord '' S =
      (-A.origin) +ᵥ (outerA + axis.coord '' S) := by
    rw [A.carrier_eq, hraw]
    ext x
    constructor
    · rintro ⟨a, ha, y, hy, rfl⟩
      obtain ⟨b, hb, rfl⟩ := Set.mem_vadd_set.mp ha
      refine ⟨b + y, ⟨b, hb, y, hy, rfl⟩, ?_⟩
      simp only [vadd_eq_add]
      ring
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨a, ha, y, hy, rfl⟩ := hz
      refine ⟨-A.origin + a, ⟨a, ha, rfl⟩, y, hy, ?_⟩
      simp only [vadd_eq_add]
      ring
  have hfrontier : frontier (interior (closure (A.carrier + axis.coord '' S))) =
      (-A.origin) +ᵥ frontier (interior (closure (outerA + axis.coord '' S))) := by
    rw [hcarrierSum, closure_vadd, interior_vadd]
    simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
      ((Homeomorph.addLeft (-A.origin)).image_frontier
        (interior (closure (outerA + axis.coord '' S)))).symm
  have hnormalized :
      axis.coord u - A.origin ∈
          frontier (interior (closure (A.carrier + axis.coord '' S))) ↔
        axis.coord u ∈
          frontier (interior (closure (outerA + axis.coord '' S))) := by
    rw [hfrontier, Set.mem_vadd_set_iff_neg_vadd_mem]
    have hcancel : A.origin + (axis.coord u - A.origin) = axis.coord u := by ring
    simp only [neg_neg, vadd_eq_add, hcancel]
  exact (hproperShift.symm.trans hslice).trans hnormalized.symm

/-!
Actual selected-wall endpoint existence from a noncolumn packed source family.
This consumes the chosen wall data and normalized section directly; no
frontier-existence certificate or wall-membership result is assumed.
-/

private theorem selectedDatum_noncolumn_extremalVertex
    {C : ApproximationContext.{0}} {axis : Axis}
    {outerA : Set ℝ} {wall ε : ℝ} (hε : 0 < ε)
    (hgerm : ∀ U : Set Tiling.Plane,
      (∀ s ∈ U, axis.transverseCoord s = 0) →
        regularSupport C.region U ∩
            {z | axis.transverseCoord z ∈ Set.Ioo (wall - ε) (wall + ε)} =
          {z | axis.transverseCoord z ∈ Set.Ioo wall (wall + ε) ∧
            axis.coord z ∈ interior (closure (outerA + axis.coord '' U))})
    (hLower : ∀ z ∈ C.region.support, wall ≤ axis.transverseCoord z)
    (A : NormalizedGenericSection C axis)
    (hraw : A.raw.rawCarrier = outerA)
    {S : Set Tiling.Plane} {c : ℝ}
    (hpack : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements S))
    (hS : S.Nonempty)
    (hline : ∀ s ∈ S, axis.transverseCoord s = c)
    (hColumnable : ∃ Col, IsCenterColumn axis C.region Col)
    (hNotColumn : ¬ IsCenterColumn axis C.region S) :
    ∃ u ∈ properVertices (regularSupport C.region S),
      axis.transverseCoord u = wall + c ∧
      (∀ z ∈ properVertices (regularSupport C.region S),
        wall + c ≤ axis.transverseCoord z) ∧
      (∀ z ∈ properVertices (regularSupport C.region S),
        (∀ w ∈ properVertices (regularSupport C.region S),
          axis.transverseCoord z ≤ axis.transverseCoord w) ↔
        axis.transverseCoord z = wall + c) ∧
      (∀ z ∈ properVertices (regularSupport C.region S),
        axis.transverseCoord z = wall + c →
          axis.coord z - A.origin ∈
            frontier (interior (closure (A.carrier + axis.coord '' S)))) := by
  let rawTrace := outerA + axis.coord '' S
  let F := interior (closure rawTrace)
  have hSection : GenericAxisSection C.region axis outerA := {
    transverse := A.raw.transverse
    generic := A.raw.generic
    carrier_eq := by
      calc
        outerA = A.raw.rawCarrier := hraw.symm
        _ = axisSection C.region axis A.raw.transverse := by
          simpa only [axisSection] using A.raw.rawCarrier_eq
    finiteIntervals := by
      rw [← hraw]
      exact ⟨A.raw.presentation.n, A.raw.presentation.left,
        A.raw.presentation.right, A.raw.presentation.lt,
        A.raw.presentation.union_eq⟩
    isOpen := by
      rw [← hraw]
      exact A.raw.presentation.isOpen
    nonempty := by
      rw [← hraw]
      exact A.raw.nonempty }
  have hFne : F.Nonempty := by
    obtain ⟨s, hs⟩ := hS
    obtain ⟨a, ha⟩ := hSection.nonempty
    let translated := (Homeomorph.addLeft (axis.coord s)) '' outerA
    have htranslatedOpen : IsOpen translated :=
      (Homeomorph.addLeft (axis.coord s)).isOpenMap _ hSection.isOpen
    have htranslatedSubset : translated ⊆ rawTrace := by
      rintro x ⟨b, hb, rfl⟩
      exact ⟨b, hb, axis.coord s, ⟨s, hs, rfl⟩, by simp [add_comm]⟩
    have htranslatedPoint : axis.coord s + a ∈ translated := by
      exact ⟨a, ha, by simp⟩
    refine ⟨axis.coord s + a, ?_⟩
    exact interior_maximal (htranslatedSubset.trans subset_closure)
      htranslatedOpen htranslatedPoint
  have hFproper : F ≠ Set.univ := by
    intro hfull
    apply hNotColumn
    exact fullGenericSection_forcesCenterColumn axis hpack hS ⟨c, hline⟩
      hColumnable outerA (axis.coord '' S) hSection rfl (by
        simpa [F, rawTrace] using hfull)
  have hFfrontier : (frontier F).Nonempty :=
    frontier_nonempty_of_nonempty_proper_regularOpen hFne isOpen_interior
      (by simp [F]) hFproper
  obtain ⟨y, hyFrontier⟩ := hFfrontier
  have hcarrierSum : A.carrier + axis.coord '' S =
      (-A.origin) +ᵥ rawTrace := by
    rw [A.carrier_eq, hraw]
    ext x
    constructor
    · rintro ⟨a, ha, y, hy, rfl⟩
      obtain ⟨b, hb, rfl⟩ := Set.mem_vadd_set.mp ha
      refine ⟨b + y, ⟨b, hb, y, hy, rfl⟩, ?_⟩
      simp only [vadd_eq_add]
      ring
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨a, ha, y, hy, rfl⟩ := hz
      refine ⟨-A.origin + a, ⟨a, ha, rfl⟩, y, hy, ?_⟩
      simp only [vadd_eq_add]
      ring
  have hnormalizedFrontier :
      y - A.origin ∈ frontier (interior (closure (A.carrier + axis.coord '' S))) := by
    have hfrontier :
        frontier (interior (closure (A.carrier + axis.coord '' S))) =
          (-A.origin) +ᵥ frontier F := by
      rw [hcarrierSum, closure_vadd, interior_vadd]
      simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
        ((Homeomorph.addLeft (-A.origin)).image_frontier F).symm
    rw [hfrontier, Set.mem_vadd_set_iff_neg_vadd_mem]
    have hcancel : -(-A.origin) + (y - A.origin) = y := by ring
    simp only [vadd_eq_add]
    rw [hcancel]
    exact hyFrontier
  let u := FilledSliceChains.slicePoint axis (wall + c) y
  have huTrans : axis.transverseCoord u = wall + c := by
    cases axis <;> simp [u, FilledSliceChains.slicePoint, Axis.transverseCoord]
  have huCoord : axis.coord u = y := by
    cases axis <;> simp [u, FilledSliceChains.slicePoint, Axis.coord]
  have huProper : u ∈ properVertices (regularSupport C.region S) := by
    have hselected := selectedDatum_normalizedWall_proper_iff hε hgerm A hraw
      hline huTrans
    apply hselected.mpr
    rw [huCoord]
    exact hnormalizedFrontier
  have hminimum := outerWall_properVertex_transverse_isMinimal axis hline
    hLower huProper huTrans
  refine ⟨u, huProper, huTrans, ?_, ?_, ?_⟩
  · simpa only [huTrans] using hminimum
  · intro z hz
    constructor
    · intro hzmin
      have hzu : axis.transverseCoord z ≤ wall + c := by
        simpa only [huTrans] using hzmin u huProper
      apply le_antisymm hzu
      simpa only [huTrans] using hminimum z hz
    · intro hzwall
      exact outerWall_properVertex_transverse_isMinimal axis hline hLower hz hzwall
  · intro z hz hzwall
    exact (selectedDatum_normalizedWall_proper_iff hε hgerm A hraw
      hline hzwall).mp hz

private theorem outerWallTrace_frontier_eq_properSlice
    (K : Region) (axis : Axis) {S : Set Tiling.Plane}
    (hline : ∀ s ∈ S, axis.transverseCoord s = 0) :
    ∃ (A : Set ℝ) (wall ε : ℝ),
      Nonempty (GenericAxisSection K axis A) ∧ 0 < ε ∧
      (∀ z ∈ K.support, wall ≤ axis.transverseCoord z) ∧
      (∀ y : ℝ,
        FilledSliceChains.slicePoint axis wall y ∈
            properVertices (regularSupport K S) ↔
          y ∈ frontier (interior (closure (A + axis.coord '' S)))) ∧
      (∀ y : ℝ,
        FilledSliceChains.slicePoint axis wall y ∈
            properVertices (regularSupport K S) →
        ∀ z ∈ properVertices (regularSupport K S),
          axis.transverseCoord (FilledSliceChains.slicePoint axis wall y) ≤
            axis.transverseCoord z) := by
  obtain ⟨A, wall, ε, hA, _hAne, hε, hLower, hgerm⟩ :=
    exists_axis_outerWallData K axis
  refine ⟨A, wall, ε, hA, hε, hLower,
    selectedOuterWall_properSlice_iff K axis hε (hgerm S hline), ?_⟩
  intro y hy z hz
  have hpTrans : axis.transverseCoord
      (FilledSliceChains.slicePoint axis wall y) = wall := by
    cases axis <;> simp [FilledSliceChains.slicePoint, Axis.transverseCoord]
  have hmin := outerWall_properVertex_transverse_isMinimal axis hline hLower
    hy (by simpa using hpTrans)
  exact hmin z hz

/-!
Coordinate equivalence for proper vertices on the extremal outer wall.

This private fragment consumes the actual outer-wall/source-geometry producer;
it adds no trace, support, or frontier wrapper.
-/

private theorem outerWallTrace_extremalProperVertex_coordinateEquiv
    (K : Region) (axis : Axis) {S : Set Tiling.Plane}
    (hline : ∀ s ∈ S, axis.transverseCoord s = 0) :
    ∃ (A : Set ℝ) (wall ε : ℝ),
      Nonempty (GenericAxisSection K axis A) ∧ 0 < ε ∧
      (∀ z ∈ K.support, wall ≤ axis.transverseCoord z) ∧
      Nonempty ({p : ↥(properVertices (regularSupport K S)) //
          axis.transverseCoord p.1 = wall} ≃
        {y : ℝ // y ∈ frontier (interior (closure (A + axis.coord '' S)))}) := by
  obtain ⟨A, wall, ε, hA, hε, hLower, hslice, _hmin⟩ :=
    outerWallTrace_frontier_eq_properSlice K axis hline
  refine ⟨A, wall, ε, hA, hε, hLower, ?_⟩
  let D := regularSupport K S
  let F := frontier (interior (closure (A + axis.coord '' S)))
  have hpoint (p : Tiling.Plane) (htrans : axis.transverseCoord p = wall) :
      p = FilledSliceChains.slicePoint axis wall (axis.coord p) := by
    cases axis with
    | horizontal =>
        apply Complex.ext
        · simp [FilledSliceChains.slicePoint, Axis.coord]
        · change p.im = wall at htrans
          simpa [FilledSliceChains.slicePoint] using htrans
    | vertical =>
        apply Complex.ext
        · change p.re = wall at htrans
          simpa [FilledSliceChains.slicePoint] using htrans
        · simp [FilledSliceChains.slicePoint, Axis.coord]
  have hcoordSlice (y : ℝ) :
      axis.coord (FilledSliceChains.slicePoint axis wall y) = y := by
    cases axis <;> simp [Axis.coord, FilledSliceChains.slicePoint]
  refine ⟨?_⟩
  refine {
    toFun := fun p => ⟨axis.coord (p.1.1), ?_⟩
    invFun := fun y => ⟨⟨FilledSliceChains.slicePoint axis wall y.1,
      (hslice y.1).mpr y.2⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · change axis.coord (p.1.1) ∈ F
    have hpSlice : FilledSliceChains.slicePoint axis wall (axis.coord (p.1.1)) ∈
        properVertices D := by
      rw [← hpoint (p.1.1) p.2]
      exact p.1.2
    exact (hslice (axis.coord (p.1.1))).mp hpSlice
  · change axis.transverseCoord (FilledSliceChains.slicePoint axis wall y.1) = wall
    cases axis <;> simp [Axis.transverseCoord, FilledSliceChains.slicePoint]
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    exact (hpoint (p.1.1) p.2).symm
  · intro y
    apply Subtype.ext
    exact hcoordSlice y.1

private def verticalOrbitIndices {C : ApproximationContext.{0}}
    (Tphi : ↥C.centres ↪ Tiling.Plane) {u : RationalDirection}
    (Q : RationalSlice u) (part : Set Tiling.Plane) : Set ↥C.centres :=
  {t | Tphi t ∈ Q.centres part}

private theorem rationalSlice_re_constant_of_vertical
    {u : RationalDirection} (Q : RationalSlice u) (part : Set Tiling.Plane)
    (hpart : (Q.centres part).Nonempty) (hvertical : u.toPlane.re = 0) :
    ∃ c : ℝ, ∀ z ∈ Q.centres part, z.re = c := by
  classical
  obtain ⟨z₀, hz₀⟩ := hpart
  refine ⟨z₀.re, ?_⟩
  intro z hz
  have hzCarrier : z ∈ Q.carrier := hz.2
  have hz₀Carrier : z₀ ∈ Q.carrier := hz₀.2
  change QuotientAddGroup.mk' (realDirectionSubgroup u) z = Q at hzCarrier
  change QuotientAddGroup.mk' (realDirectionSubgroup u) z₀ = Q at hz₀Carrier
  obtain ⟨r, hr⟩ := QuotientAddGroup.eq_iff_sub_mem.mp
    (hzCarrier.trans hz₀Carrier.symm)
  have hre := congrArg Complex.re hr
  simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul, hvertical, mul_zero] at hre
  linarith

private theorem rationalDirection_toPlane_ne_zero
    (u : RationalDirection) : u.toPlane ≠ 0 := by
  intro hz
  apply u.2
  funext j
  fin_cases j
  · have h := congrArg Complex.re hz
    have h' : (u.coordinates 0 : ℝ) = 0 := by
      simpa [RationalDirection.toPlane] using h
    exact_mod_cast h'
  · have h := congrArg Complex.im hz
    have h' : (u.coordinates 1 : ℝ) = 0 := by
      simpa [RationalDirection.toPlane] using h
    exact_mod_cast h'

private structure VerticalNoGapOrbitPairData
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i))
    (G : ℝ) (m : ℤ) where
  S₀ : Set ↥C.centres
  Sₘ : Set ↥C.centres
  S₀_eq : S₀ = verticalOrbitIndices Tphi Q (Dcmp.part i)
  Sₘ_eq : Sₘ = verticalOrbitIndices Tphi
    (Q.vadd (m • Dcmp.gamma.toPlane)) (Dcmp.part i)
  phase₀ : Q ∈ (Dcmp.orbit i).phases
  phaseₘ : Q.vadd (m • Dcmp.gamma.toPlane) ∈ (Dcmp.orbit i).phases
  noGap₀ : Q ∈ (Dcmp.orbit i).noGapPhases (originalSlice i) G
  noGapₘ : Q.vadd (m • Dcmp.gamma.toPlane) ∈
    (Dcmp.orbit i).noGapPhases (originalSlice i) G
  source₀_eq : originalSlice i Q = Set.image Subtype.val S₀
  sourceₘ_eq : originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
    Set.image Subtype.val Sₘ
  image₀_eq : deformedCenterCarrierOn Tphi S₀ =
    Q.centres (Dcmp.part i)
  imageₘ_eq : deformedCenterCarrierOn Tphi Sₘ =
    (Q.vadd (m • Dcmp.gamma.toPlane)).centres (Dcmp.part i)
  nonempty₀ : S₀.Nonempty
  nonemptyₘ : Sₘ.Nonempty
  linked₀ : Linked G (Set.image Subtype.val S₀)
  linkedₘ : Linked G (Set.image Subtype.val Sₘ)
  sourcePacking₀ : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
    (C.region.toPolygonalRegion.placements (Set.image Subtype.val S₀))
  sourcePackingₘ : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
    (C.region.toPolygonalRegion.placements (Set.image Subtype.val Sₘ))
  imagePacking₀ : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
    (D.deformedRegion.toPolygonalRegion.placements (deformedCenterCarrierOn Tphi S₀))
  imagePackingₘ : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
    (D.deformedRegion.toPolygonalRegion.placements (deformedCenterCarrierOn Tphi Sₘ))
  imageLine₀ : ∃ c, ∀ t : S₀, Axis.vertical.transverseCoord (Tphi t.1) = c
  imageLineₘ : ∃ c, ∀ t : Sₘ, Axis.vertical.transverseCoord (Tphi t.1) = c
  imagePeriod : Tiling.Plane
  imagePeriod_ne : imagePeriod ≠ 0
  imagePeriod_vertical : Axis.vertical.transverseCoord imagePeriod = 0
  imagePeriod_invariant₀ : imagePeriod +ᵥ deformedCenterCarrierOn Tphi S₀ =
    deformedCenterCarrierOn Tphi S₀
  imagePeriod_invariantₘ : imagePeriod +ᵥ deformedCenterCarrierOn Tphi Sₘ =
    deformedCenterCarrierOn Tphi Sₘ
  imageSupport_shift : regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi Sₘ) =
    (m • Dcmp.gamma.toPlane) +ᵥ regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi S₀)

private theorem verticalNoGapOrbitPairData_exists
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (B : PeriodicBandData C) (hFine : IsPeriodicBandFineness B P.threshold)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ} (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
    (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i))
    (G : ℝ) (m : ℤ)
    (hOrbitNoGap : ∀ n : ℤ,
      Q.vadd (n • Dcmp.gamma.toPlane) ∈
        (Dcmp.orbit i).noGapPhases (originalSlice i) G)
    (hvertical : (Dcmp.direction i).toPlane.re = 0) :
    Nonempty (VerticalNoGapOrbitPairData P D Tphi Dcmp originalSlice i Q G m) := by
  classical
  let Q₀ := Q
  let Qₘ := Q.vadd (m • Dcmp.gamma.toPlane)
  let S₀ := verticalOrbitIndices Tphi Q₀ (Dcmp.part i)
  let Sₘ := verticalOrbitIndices Tphi Qₘ (Dcmp.part i)
  have hNoGap₀ : Q₀ ∈ (Dcmp.orbit i).noGapPhases (originalSlice i) G := by
    simpa [Q₀, RationalSlice.vadd] using hOrbitNoGap 0
  have hNoGapₘ : Qₘ ∈ (Dcmp.orbit i).noGapPhases (originalSlice i) G := by
    simpa [Qₘ] using hOrbitNoGap m
  have hphase₀ : Q₀ ∈ (Dcmp.orbit i).phases := hNoGap₀.1
  have hphaseₘ : Qₘ ∈ (Dcmp.orbit i).phases := hNoGapₘ.1
  have hpart : Dcmp.part i ⊆ Set.range Tphi := by
    intro z hz
    rw [← Dcmp.parts_union]
    exact Set.mem_iUnion.mpr ⟨i, hz⟩
  have hsource₀ : originalSlice i Q₀ = Set.image Subtype.val S₀ := by
    exact hPreimage i Q₀ hphase₀
  have hsourceₘ : originalSlice i Qₘ = Set.image Subtype.val Sₘ := by
    exact hPreimage i Qₘ hphaseₘ
  have himage₀ : deformedCenterCarrierOn Tphi S₀ = Q₀.centres (Dcmp.part i) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hz
      obtain ⟨t, rfl⟩ := hpart hz.1
      exact ⟨t, hz, rfl⟩
  have himageₘ : deformedCenterCarrierOn Tphi Sₘ = Qₘ.centres (Dcmp.part i) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hz
      obtain ⟨t, rfl⟩ := hpart hz.1
      exact ⟨t, hz, rfl⟩
  have hindices_nonempty (R : RationalSlice (Dcmp.direction i))
      (hphase : R ∈ (Dcmp.orbit i).phases) :
      (verticalOrbitIndices Tphi R (Dcmp.part i)).Nonempty := by
    obtain ⟨z, hz⟩ := ((Dcmp.orbit i).phase_iff_nonempty R).mp hphase
    obtain ⟨t, ht⟩ := hpart hz.1
    refine ⟨t, ?_⟩
    change Tphi t ∈ R.centres (Dcmp.part i)
    rw [ht]
    exact hz
  have hne₀ : S₀.Nonempty := hindices_nonempty Q₀ hphase₀
  have hneₘ : Sₘ.Nonempty := hindices_nonempty Qₘ hphaseₘ
  have hphaseOriginalNonempty : ∀ R : RationalSlice (Dcmp.direction i),
      R ∈ (Dcmp.orbit i).phases → (originalSlice i R).Nonempty := by
    intro R hphase
    rw [hPreimage i R hphase]
    exact (hindices_nonempty R hphase).image Subtype.val
  have hlinked₀ : Linked G (Set.image Subtype.val S₀) := by
    rw [← hsource₀]
    exact (Dcmp.orbit i).linked_originalSlice_of_mem_noGapPhases
      (originalSlice i) hphaseOriginalNonempty hNoGap₀
  have hlinkedₘ : Linked G (Set.image Subtype.val Sₘ) := by
    rw [← hsourceₘ]
    exact (Dcmp.orbit i).linked_originalSlice_of_mem_noGapPhases
      (originalSlice i) hphaseOriginalNonempty hNoGapₘ
  obtain ⟨Tphi₀, Xphi, aphi, hmap, hopen, hregular, hnonempty, hproper,
    hperiod, hpositive, hperiodic, hfrontier, hoccupied, htiles, hsupport⟩ :=
      periodicBandDeformation B P.threshold hFine phi hphi D
  have hTphiEq : Tphi₀ = Tphi := by
    ext t
    exact (hmap t).trans (hTphi t).symm
  have hTiles : TilesOn D.deformedRegion (Set.range Tphi)
      {z : Tiling.Plane | z.re ∈ Xphi} := by
    rw [← hTphiEq]
    exact htiles
  have hImageSub (S : Set ↥C.centres) :
      deformedCenterCarrierOn Tphi S ⊆ Set.range Tphi := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨t, rfl⟩
  have himagePack (S : Set ↥C.centres)
      (hS : deformedCenterCarrierOn Tphi S ⊆ Set.range Tphi) :
      Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
        (D.deformedRegion.toPolygonalRegion.placements
          (deformedCenterCarrierOn Tphi S)) := by
    intro a ha b hb hab
    exact hTiles.2.1 (hS ha) (hS hb) hab
  have hsourcePack (S : Set ↥C.centres) :
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements (Set.image Subtype.val S)) := by
    have hSourceSub : Set.image Subtype.val S ⊆ C.centres := by
      rintro z ⟨t, ht, rfl⟩
      exact t.2
    intro a ha b hb hab
    exact P.source_tilesOn.2.1
      (hSourceSub ha) (hSourceSub hb) hab
  have hlineCenters (R : RationalSlice (Dcmp.direction i))
      (hphase : R ∈ (Dcmp.orbit i).phases) :
      ∃ c, ∀ z ∈ R.centres (Dcmp.part i), z.re = c := by
    apply rationalSlice_re_constant_of_vertical R (Dcmp.part i)
      (((Dcmp.orbit i).phase_iff_nonempty R).mp hphase) hvertical
  have hline₀ : ∃ c, ∀ t : S₀,
      Axis.vertical.transverseCoord (Tphi t.1) = c := by
    obtain ⟨c, hc⟩ := hlineCenters Q₀ hphase₀
    refine ⟨c, ?_⟩
    intro t
    have hmem : Tphi t.1 ∈ Q₀.centres (Dcmp.part i) := by
      exact t.2
    simpa [Axis.transverseCoord] using hc (Tphi t.1) hmem
  have hlineₘ : ∃ c, ∀ t : Sₘ,
      Axis.vertical.transverseCoord (Tphi t.1) = c := by
    obtain ⟨c, hc⟩ := hlineCenters Qₘ hphaseₘ
    refine ⟨c, ?_⟩
    intro t
    have hmem : Tphi t.1 ∈ Qₘ.centres (Dcmp.part i) := by
      exact t.2
    simpa [Axis.transverseCoord] using hc (Tphi t.1) hmem
  let imagePeriod : Tiling.Plane := (Dcmp.direction i).toPlane
  have himagePeriodNe : imagePeriod ≠ 0 := rationalDirection_toPlane_ne_zero _
  have himagePeriodVertical : Axis.vertical.transverseCoord imagePeriod = 0 := by
    simpa [imagePeriod, Axis.transverseCoord] using hvertical
  have hperiod₀ : imagePeriod +ᵥ deformedCenterCarrierOn Tphi S₀ =
      deformedCenterCarrierOn Tphi S₀ := by
    rw [himage₀]
    exact (setPeriodicBy_iff_vadd_eq _ _).mp
      ((Dcmp.orbit i).slice_periodic Q₀ hphase₀)
  have hperiodₘ : imagePeriod +ᵥ deformedCenterCarrierOn Tphi Sₘ =
      deformedCenterCarrierOn Tphi Sₘ := by
    rw [himageₘ]
    exact (setPeriodicBy_iff_vadd_eq _ _).mp
      ((Dcmp.orbit i).slice_periodic Qₘ hphaseₘ)
  have hsupportShift : regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi Sₘ) =
      (m • Dcmp.gamma.toPlane) +ᵥ regularSupport D.deformedRegion
        (deformedCenterCarrierOn Tphi S₀) := by
    rw [himageₘ, himage₀]
    exact ((Dcmp.orbit i).regularSupport_transport Q₀ hphase₀ m).symm
  exact ⟨{
    S₀ := S₀
    Sₘ := Sₘ
    S₀_eq := rfl
    Sₘ_eq := rfl
    phase₀ := hphase₀
    phaseₘ := hphaseₘ
    noGap₀ := hNoGap₀
    noGapₘ := hNoGapₘ
    source₀_eq := hsource₀
    sourceₘ_eq := hsourceₘ
    image₀_eq := himage₀
    imageₘ_eq := himageₘ
    nonempty₀ := hne₀
    nonemptyₘ := hneₘ
    linked₀ := hlinked₀
    linkedₘ := hlinkedₘ
    sourcePacking₀ := hsourcePack S₀
    sourcePackingₘ := hsourcePack Sₘ
    imagePacking₀ := himagePack S₀ (hImageSub S₀)
    imagePackingₘ := himagePack Sₘ (hImageSub Sₘ)
    imageLine₀ := hline₀
    imageLineₘ := hlineₘ
    imagePeriod := imagePeriod
    imagePeriod_ne := himagePeriodNe
    imagePeriod_vertical := himagePeriodVertical
    imagePeriod_invariant₀ := hperiod₀
    imagePeriod_invariantₘ := hperiodₘ
    imageSupport_shift := hsupportShift
  }⟩

/-!
Propagate the actual pair displacement from transverse minima to every source
proper vertex. The path-control premise is the field supplied by
`columnable_preApproximationControls`; the seeds belong only to the minimum set.
-/

/-!
Actual selected-wall frontier order equivalence.

This fragment is to be inserted in the existing terminal namespace after the
actual pair, selected-wall membership, and weak-order lemmas.  The only wall
inputs are genuine wall points and the support lower bound; the theta/minimum
and frontier correspondences are derived below.
-/

private theorem actualPair_theta_preserves_transverse_minimum
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S₀ S₁ : Set ↥C.centres}
    {hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀))}
    {hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁))}
    {hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))}
    {hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))}
    {eta : Tiling.Plane}
    (pair : ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta)
    (P : FLCControlPackage C)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (hDiam : Metric.diam C.region.support < P.controlRadius)
    (axis : Axis)
    (hline₀ : ∃ c, ∀ s ∈ Subtype.val '' S₀,
      axis.transverseCoord s = c)
    (hline₁ : ∃ c, ∀ s ∈ Subtype.val '' S₁,
      axis.transverseCoord s = c)
    (u : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀)))) :
    (∀ v : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))),
      axis.transverseCoord u.1 ≤ axis.transverseCoord v.1) ↔
    (∀ v : ↥(properVertices (regularSupport C.region (Subtype.val '' S₁))),
      axis.transverseCoord (pair.theta u).1 ≤ axis.transverseCoord v.1) := by
  have hdiff (v : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀)))) :
      axis.transverseCoord (pair.theta u).1 -
          axis.transverseCoord (pair.theta v).1 =
        axis.transverseCoord u.1 - axis.transverseCoord v.1 := by
    have h := actualProperVertexPair_transverse_difference pair P hphi hDiam
      axis hline₀ hline₁ u v
    have h' : axis.transverseCoord (pair.theta v).1 -
          axis.transverseCoord (pair.theta u).1 =
        axis.transverseCoord v.1 - axis.transverseCoord u.1 := by
      cases axis <;>
        simpa [Axis.transverseCoord, Complex.sub_re, Complex.sub_im] using h
    linarith
  constructor
  · intro hu v
    let w := pair.theta.symm v
    have hw : pair.theta w = v := pair.theta.apply_symm_apply v
    have hmin := hu w
    have heq := hdiff w
    rw [hw] at heq
    linarith
  · intro hu v
    have hv := hu (pair.theta v)
    have heq := hdiff v
    linarith

private theorem actualPair_selectedWall_frontierOrderEquiv
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S₀ S₁ : Set ↥C.centres}
    {hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀))}
    {hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁))}
    {hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))}
    {hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))}
    {eta : Tiling.Plane} {axis : Axis} {A : NormalizedGenericSection C axis}
    (pair : ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta)
    (E₀ : AllEndpointWeakOrderTransport phi D Tphi axis S₀ A)
    (E₁ : AllEndpointWeakOrderTransport phi D Tphi axis S₁ A)
    (P : FLCControlPackage C)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (hDiam : Metric.diam C.region.support < P.controlRadius)
    {outerA : Set ℝ} {wall ε : ℝ} (hε : 0 < ε)
    (hgerm : ∀ U : Set Tiling.Plane,
      (∀ s ∈ U, axis.transverseCoord s = 0) →
        regularSupport C.region U ∩
            {z | axis.transverseCoord z ∈ Set.Ioo (wall - ε) (wall + ε)} =
          {z | axis.transverseCoord z ∈ Set.Ioo wall (wall + ε) ∧
            axis.coord z ∈ interior (closure (outerA + axis.coord '' U))})
    (hraw : A.raw.rawCarrier = outerA)
    {c₀ c₁ : ℝ}
    (hline₀ : ∀ s ∈ Subtype.val '' S₀, axis.transverseCoord s = c₀)
    (hline₁ : ∀ s ∈ Subtype.val '' S₁, axis.transverseCoord s = c₁)
    (hLower : ∀ z ∈ C.region.support, wall ≤ axis.transverseCoord z)
    (w₀ : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))))
    (hw₀ : axis.transverseCoord w₀.1 = wall + c₀)
    (w₁ : ↥(properVertices (regularSupport C.region (Subtype.val '' S₁))))
    (hw₁ : axis.transverseCoord w₁.1 = wall + c₁) :
    ∃ e :
      {x : ℝ // x ∈ frontier
        (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀))))} ≃
      {y : ℝ // y ∈ frontier
        (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₁))))},
      (∀ (x y : {x : ℝ // x ∈ frontier
          (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀))))}),
        (x : ℝ) ≤ y ↔ (e x : ℝ) ≤ e y) ∧
      (∀ (u : ↥(properVertices
          (regularSupport C.region (Subtype.val '' S₀))))
        (_hmin : ∀ v : ↥(properVertices
          (regularSupport C.region (Subtype.val '' S₀))),
          axis.transverseCoord u.1 ≤ axis.transverseCoord v.1)
        (huF : axis.coord u.1 - A.origin ∈
          frontier (interior (closure
            (A.carrier + axis.coord '' (Subtype.val '' S₀))))),
        (e ⟨axis.coord u.1 - A.origin, huF⟩).1 =
          axis.coord (pair.theta u).1 - A.origin) := by
  classical
  let PV₀ := ↥(properVertices
    (regularSupport C.region (Subtype.val '' S₀)))
  let PV₁ := ↥(properVertices
    (regularSupport C.region (Subtype.val '' S₁)))
  let F₀ : Set ℝ := frontier
    (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀))))
  let F₁ : Set ℝ := frontier
    (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₁))))
  let Min₀ : Set PV₀ := {u | ∀ v : PV₀,
    axis.transverseCoord u.1 ≤ axis.transverseCoord v.1}
  let Min₁ : Set PV₁ := {u | ∀ v : PV₁,
    axis.transverseCoord u.1 ≤ axis.transverseCoord v.1}
  have hlevel₀ (u : PV₀) : u ∈ Min₀ ↔
      axis.transverseCoord u.1 = wall + c₀ := by
    constructor
    · intro hu
      have hlow := outerWall_properVertex_transverse_minimum axis hline₀
        hLower u.1 u.2
      have huw := hu w₀
      rw [hw₀] at huw
      exact le_antisymm huw hlow
    · intro hu v
      exact outerWall_properVertex_transverse_isMinimal axis hline₀ hLower
        u.2 hu v.1 v.2
  have hlevel₁ (u : PV₁) : u ∈ Min₁ ↔
      axis.transverseCoord u.1 = wall + c₁ := by
    constructor
    · intro hu
      have hlow := outerWall_properVertex_transverse_minimum axis hline₁
        hLower u.1 u.2
      have huw := hu w₁
      rw [hw₁] at huw
      exact le_antisymm huw hlow
    · intro hu v
      exact outerWall_properVertex_transverse_isMinimal axis hline₁ hLower
        u.2 hu v.1 v.2
  have hminMap (u : PV₀) :
      (u ∈ Min₀) ↔ pair.theta u ∈ Min₁ := by
    change (∀ v : PV₀, axis.transverseCoord u.1 ≤ axis.transverseCoord v.1) ↔
      (∀ v : PV₁, axis.transverseCoord (pair.theta u).1 ≤ axis.transverseCoord v.1)
    exact actualPair_theta_preserves_transverse_minimum pair P hphi hDiam axis
      ⟨c₀, hline₀⟩ ⟨c₁, hline₁⟩ u
  let F₀Sub := {x : ℝ // x ∈ F₀}
  let F₁Sub := {y : ℝ // y ∈ F₁}
  let Coord₀ : {u : PV₀ // u ∈ Min₀} ≃ F₀Sub := by
    let f : {u : PV₀ // u ∈ Min₀} → F₀Sub := fun u =>
      ⟨axis.coord u.1.1 - A.origin, by
        have hlevel := (hlevel₀ u.1).mp u.2
        exact (selectedDatum_normalizedWall_proper_iff hε hgerm A hraw
          hline₀ hlevel).mp u.1.2⟩
    have hf : Function.Bijective f := by
      constructor
      · intro u v huv
        apply Subtype.ext
        apply Subtype.ext
        have hcoord : axis.coord u.1.1 = axis.coord v.1.1 := by
          have := congrArg Subtype.val huv
          dsimp [f] at this
          linarith
        have htrans : axis.transverseCoord u.1.1 =
            axis.transverseCoord v.1.1 := by
          rw [(hlevel₀ u.1).mp u.2, (hlevel₀ v.1).mp v.2]
        have hpoint : u.1.1 = v.1.1 := by
          cases axis with
          | horizontal =>
              apply Complex.ext
              · exact hcoord
              · simpa [Axis.coord, Axis.transverseCoord] using htrans
          | vertical =>
              apply Complex.ext
              · simpa [Axis.coord, Axis.transverseCoord] using htrans
              · exact hcoord
        exact hpoint
      · intro x
        have hcoord : axis.coord
            (FilledSliceChains.slicePoint axis (wall + c₀)
              (x.1 + A.origin)) = x.1 + A.origin := by
          cases axis <;> simp [FilledSliceChains.slicePoint, Axis.coord]
        have hnormalized : axis.coord
            (FilledSliceChains.slicePoint axis (wall + c₀)
              (x.1 + A.origin)) - A.origin = x.1 := by
          rw [hcoord]
          ring
        refine ⟨⟨⟨FilledSliceChains.slicePoint axis (wall + c₀)
            (x.1 + A.origin), ?_⟩, ?_⟩, ?_⟩
        · exact (selectedDatum_normalizedWall_proper_iff hε hgerm A hraw
            hline₀ (by
              cases axis <;>
                simp [FilledSliceChains.slicePoint, Axis.transverseCoord])).mpr
              (by rw [hnormalized]; simp [F₀])
        · apply (hlevel₀ _).mpr
          cases axis <;>
            simp [FilledSliceChains.slicePoint, Axis.transverseCoord]
        · apply Subtype.ext
          change axis.coord (FilledSliceChains.slicePoint axis (wall + c₀)
            (x.1 + A.origin)) - A.origin = x.1
          rw [hcoord]
          ring
    exact Equiv.ofBijective f hf
  let Coord₁ : {u : PV₁ // u ∈ Min₁} ≃ F₁Sub := by
    let f : {u : PV₁ // u ∈ Min₁} → F₁Sub := fun u =>
      ⟨axis.coord u.1.1 - A.origin, by
        have hlevel := (hlevel₁ u.1).mp u.2
        exact (selectedDatum_normalizedWall_proper_iff hε hgerm A hraw
          hline₁ hlevel).mp u.1.2⟩
    have hf : Function.Bijective f := by
      constructor
      · intro u v huv
        apply Subtype.ext
        apply Subtype.ext
        have hcoord : axis.coord u.1.1 = axis.coord v.1.1 := by
          have := congrArg Subtype.val huv
          dsimp [f] at this
          linarith
        have htrans : axis.transverseCoord u.1.1 =
            axis.transverseCoord v.1.1 := by
          rw [(hlevel₁ u.1).mp u.2, (hlevel₁ v.1).mp v.2]
        have hpoint : u.1.1 = v.1.1 := by
          cases axis with
          | horizontal =>
              apply Complex.ext
              · exact hcoord
              · simpa [Axis.coord, Axis.transverseCoord] using htrans
          | vertical =>
              apply Complex.ext
              · simpa [Axis.coord, Axis.transverseCoord] using htrans
              · exact hcoord
        exact hpoint
      · intro x
        have hcoord : axis.coord
            (FilledSliceChains.slicePoint axis (wall + c₁)
              (x.1 + A.origin)) = x.1 + A.origin := by
          cases axis <;> simp [FilledSliceChains.slicePoint, Axis.coord]
        have hnormalized : axis.coord
            (FilledSliceChains.slicePoint axis (wall + c₁)
              (x.1 + A.origin)) - A.origin = x.1 := by
          rw [hcoord]
          ring
        refine ⟨⟨⟨FilledSliceChains.slicePoint axis (wall + c₁)
            (x.1 + A.origin), ?_⟩, ?_⟩, ?_⟩
        · exact (selectedDatum_normalizedWall_proper_iff hε hgerm A hraw
            hline₁ (by
              cases axis <;>
                simp [FilledSliceChains.slicePoint, Axis.transverseCoord])).mpr
              (by rw [hnormalized]; simp [F₁])
        · apply (hlevel₁ _).mpr
          cases axis <;>
            simp [FilledSliceChains.slicePoint, Axis.transverseCoord]
        · apply Subtype.ext
          change axis.coord (FilledSliceChains.slicePoint axis (wall + c₁)
            (x.1 + A.origin)) - A.origin = x.1
          rw [hcoord]
          ring
    exact Equiv.ofBijective f hf
  let thetaMin : {u : PV₀ // u ∈ Min₀} ≃ {u : PV₁ // u ∈ Min₁} := {
    toFun := fun u => ⟨pair.theta u.1, (hminMap u.1).mp u.2⟩
    invFun := fun v => ⟨pair.theta.symm v.1, (hminMap (pair.theta.symm v.1)).mpr
      (by simp)⟩
    left_inv := by intro u; apply Subtype.ext; exact pair.theta.left_inv u.1
    right_inv := by intro v; apply Subtype.ext; exact pair.theta.right_inv v.1 }
  let e : F₀Sub ≃ F₁Sub := Coord₀.symm.trans (thetaMin.trans Coord₁)
  refine ⟨e, ?_, ?_⟩
  · intro x y
    let u : {u : PV₀ // u ∈ Min₀} := Coord₀.symm x
    let v : {u : PV₀ // u ∈ Min₀} := Coord₀.symm y
    have hucoord : axis.coord u.1.1 - A.origin = x.1 := by
      exact congrArg Subtype.val (Coord₀.apply_symm_apply x)
    have hvcoord : axis.coord v.1.1 - A.origin = y.1 := by
      exact congrArg Subtype.val (Coord₀.apply_symm_apply y)
    have hfrontU := (selectedDatum_normalizedWall_proper_iff hε hgerm A hraw
      hline₀ ((hlevel₀ u.1).mp u.2)).mp u.1.2
    have hfrontV := (selectedDatum_normalizedWall_proper_iff hε hgerm A hraw
      hline₀ ((hlevel₀ v.1).mp v.2)).mp v.1.2
    have hfrontThetaU := (selectedDatum_normalizedWall_proper_iff hε hgerm A hraw
      hline₁ ((hlevel₁ (pair.theta u.1)).mp ((hminMap u.1).mp u.2))).mp
        (pair.theta u.1).2
    have hfrontThetaV := (selectedDatum_normalizedWall_proper_iff hε hgerm A hraw
      hline₁ ((hlevel₁ (pair.theta v.1)).mp ((hminMap v.1).mp v.2))).mp
        (pair.theta v.1).2
    have horder := actualPair_endpoint_weakOrder_at_traceFrontier pair E₀ E₁
      u.1 v.1 hfrontU hfrontV hfrontThetaU hfrontThetaV
    have hecoordU : axis.coord (pair.theta u.1).1 - A.origin = (e x).1 := by
      change axis.coord (pair.theta u.1).1 - A.origin =
        (Coord₁ (thetaMin u)).1
      rfl
    have hecoordV : axis.coord (pair.theta v.1).1 - A.origin = (e y).1 := by
      change axis.coord (pair.theta v.1).1 - A.origin =
        (Coord₁ (thetaMin v)).1
      rfl
    have huAxis : axis.coord u.1.1 = x.1 + A.origin := by linarith
    have hvAxis : axis.coord v.1.1 = y.1 + A.origin := by linarith
    constructor
    · intro hxy
      have hxy' : axis.coord u.1.1 ≤ axis.coord v.1.1 := by linarith
      have ht := horder.mp hxy'
      have htargetU : axis.coord (pair.theta u.1).1 = (e x).1 + A.origin := by
        linarith
      have htargetV : axis.coord (pair.theta v.1).1 = (e y).1 + A.origin := by
        linarith
      rw [htargetU, htargetV] at ht
      linarith
    · intro hxy
      have htargetU : axis.coord (pair.theta u.1).1 = (e x).1 + A.origin := by
        linarith
      have htargetV : axis.coord (pair.theta v.1).1 = (e y).1 + A.origin := by
        linarith
      have hxy' : axis.coord (pair.theta u.1).1 ≤
          axis.coord (pair.theta v.1).1 := by
        linarith
      have ht := horder.mpr hxy'
      rw [huAxis, hvAxis] at ht
      linarith
  · intro u hmin huF
    let u₀ : {u : PV₀ // u ∈ Min₀} := ⟨u, hmin⟩
    let x : F₀Sub := ⟨axis.coord u.1 - A.origin, huF⟩
    have hcoord : Coord₀ u₀ = x := by
      apply Subtype.ext
      rfl
    have hpreimage : Coord₀.symm x = u₀ := by
      calc
        Coord₀.symm x = Coord₀.symm (Coord₀ u₀) := by rw [hcoord]
        _ = u₀ := Coord₀.symm_apply_apply u₀
    have heq : e x = Coord₁ (thetaMin u₀) := by
      change Coord₁ (thetaMin (Coord₀.symm x)) = _
      rw [hpreimage]
    calc
      (e x).1 = (Coord₁ (thetaMin u₀)).1 := congrArg Subtype.val heq
      _ = axis.coord (pair.theta u).1 - A.origin := rfl

/-!
Pure-real transport of consecutive frontier values through an order equivalence.

The order datum is the already-derived order equivalence between the actual
selected-wall frontiers.  This lemma only transports one consecutive pair; it
does not assert or package any endpoint correspondence.
-/

private theorem frontierOrderEquiv_maps_consecutive_values
    {F₀ F₁ : Set ℝ}
    (e : {x : ℝ // x ∈ F₀} ≃ {y : ℝ // y ∈ F₁})
    (horder : ∀ x y : {x : ℝ // x ∈ F₀},
      (x : ℝ) ≤ y ↔ (e x : ℝ) ≤ e y)
    {a b : ℝ} (ha : a ∈ F₀) (hb : b ∈ F₀) (hab : a < b)
    (hgap : ∀ z : ℝ, z ∈ Set.Ioo a b → z ∉ F₀) :
    (e ⟨a, ha⟩ : ℝ) < e ⟨b, hb⟩ ∧
      ∀ z : ℝ, z ∈ Set.Ioo (e ⟨a, ha⟩ : ℝ) (e ⟨b, hb⟩ : ℝ) → z ∉ F₁ := by
  have hforward : (e ⟨a, ha⟩ : ℝ) ≤ e ⟨b, hb⟩ :=
    (horder ⟨a, ha⟩ ⟨b, hb⟩).mp (le_of_lt hab)
  have hnotReverse : ¬ (e ⟨b, hb⟩ : ℝ) ≤ e ⟨a, ha⟩ := by
    intro hba
    have hba' : b ≤ a := (horder ⟨b, hb⟩ ⟨a, ha⟩).mpr hba
    exact (not_le_of_gt hab) hba'
  have hstrict := (lt_iff_le_not_ge).2 ⟨hforward, hnotReverse⟩
  refine ⟨hstrict, ?_⟩
  intro z hz hzF
  let x : {x : ℝ // x ∈ F₀} := e.symm ⟨z, hzF⟩
  have hxImage : (e x : ℝ) = z := by
    change (e (e.symm ⟨z, hzF⟩) : ℝ) = z
    rw [e.apply_symm_apply]
  have hax : a ≤ (x : ℝ) := by
    apply (horder ⟨a, ha⟩ x).mpr
    rw [hxImage]
    exact le_of_lt hz.1
  have hxNotA : ¬ (x : ℝ) ≤ a := by
    intro hxa
    have hza : z ≤ (e ⟨a, ha⟩ : ℝ) := by
      have h := (horder x ⟨a, ha⟩).mp hxa
      simpa [hxImage] using h
    exact (not_le_of_gt hz.1) hza
  have hltA : a < (x : ℝ) := (lt_iff_le_not_ge).2 ⟨hax, hxNotA⟩
  have hxb : (x : ℝ) ≤ b := by
    apply (horder x ⟨b, hb⟩).mpr
    rw [hxImage]
    exact le_of_lt hz.2
  have hxNotB : ¬ b ≤ (x : ℝ) := by
    intro hbx
    have hbz : (e ⟨b, hb⟩ : ℝ) ≤ z := by
      have h := (horder ⟨b, hb⟩ x).mp hbx
      simpa [hxImage] using h
    exact (not_le_of_gt hz.2) hbz
  have hltB : (x : ℝ) < b := (lt_iff_le_not_ge).2 ⟨hxb, hxNotB⟩
  exact hgap x.1 ⟨hltA, hltB⟩ x.2

/-!
Propagate one actual pair displacement over the selected source wall.  The
local edge input is only equality on consecutive actual wall vertices; global
constancy is derived here from frontier local finiteness and real reachability.
-/

private theorem actualWallConsecutive_displacement_propagates
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S₀ S₁ : Set ↥C.centres}
    {hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀))}
    {hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁))}
    {hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))}
    {hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))}
    {eta : Tiling.Plane} {axis : Axis} {A : NormalizedGenericSection C axis}
    (pair : ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta)
    (E₀ : AllEndpointWeakOrderTransport phi D Tphi axis S₀ A)
    {outerA : Set ℝ} {wall ε : ℝ} (hε : 0 < ε)
    (hgerm : ∀ U : Set Tiling.Plane,
      (∀ s ∈ U, axis.transverseCoord s = 0) →
        regularSupport C.region U ∩
            {z | axis.transverseCoord z ∈ Set.Ioo (wall - ε) (wall + ε)} =
          {z | axis.transverseCoord z ∈ Set.Ioo wall (wall + ε) ∧
            axis.coord z ∈ interior (closure (outerA + axis.coord '' U))})
    (hLower : ∀ z ∈ C.region.support, wall ≤ axis.transverseCoord z)
    (hraw : A.raw.rawCarrier = outerA)
    (hPacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S₀)))
    (hS₀ : S₀.Nonempty) {c : ℝ}
    (hline : ∀ s ∈ Subtype.val '' S₀, axis.transverseCoord s = c)
    (hColumnable : ∃ Col, IsCenterColumn axis C.region Col)
    (hNotColumn : ¬ IsCenterColumn axis C.region (Subtype.val '' S₀))
    (u₀ : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))))
    (hu₀min : ∀ v ∈ properVertices
      (regularSupport C.region (Subtype.val '' S₀)),
        axis.transverseCoord u₀.1 ≤ axis.transverseCoord v)
    (beta : Tiling.Plane)
    (hseed : (pair.theta u₀).1 - u₀.1 = beta)
    (hAdjacent : ∀ u v : ↥(properVertices
        (regularSupport C.region (Subtype.val '' S₀))),
      (∀ w ∈ properVertices
        (regularSupport C.region (Subtype.val '' S₀)),
          axis.transverseCoord u.1 ≤ axis.transverseCoord w) →
      (∀ w ∈ properVertices
        (regularSupport C.region (Subtype.val '' S₀)),
          axis.transverseCoord v.1 ≤ axis.transverseCoord w) →
      let F := frontier (interior (closure
        (A.carrier + axis.coord '' (Subtype.val '' S₀))))
      axis.coord u.1 - A.origin ∈ F ∧
        axis.coord v.1 - A.origin ∈ F ∧
        ((axis.coord u.1 - A.origin < axis.coord v.1 - A.origin ∧
            ∀ x, x ∈ F →
              ¬ (axis.coord u.1 - A.origin < x ∧
                x < axis.coord v.1 - A.origin)) ∨
          (axis.coord v.1 - A.origin < axis.coord u.1 - A.origin ∧
            ∀ x, x ∈ F →
              ¬ (axis.coord v.1 - A.origin < x ∧
                x < axis.coord u.1 - A.origin))) →
      (pair.theta v).1 - (pair.theta u).1 = v.1 - u.1) :
    ∀ u : ↥(properVertices
        (regularSupport C.region (Subtype.val '' S₀))),
      (∀ v ∈ properVertices
        (regularSupport C.region (Subtype.val '' S₀)),
          axis.transverseCoord u.1 ≤ axis.transverseCoord v) →
      (pair.theta u).1 - u.1 = beta := by
  classical
  let Source := regularSupport C.region (Subtype.val '' S₀)
  let F := frontier (interior (closure
    (A.carrier + axis.coord '' (Subtype.val '' S₀))))
  let IsMinimum (u : ↥(properVertices Source)) : Prop :=
    ∀ v ∈ properVertices Source,
      axis.transverseCoord u.1 ≤ axis.transverseCoord v
  let MinimumVertices : Set (↥(properVertices Source)) := {u | IsMinimum u}
  obtain ⟨wallSeed, hwallSeed, _hwallSeedTrans, _hwallLower, hminimumIff,
      hwallFrontier⟩ :=
    selectedDatum_noncolumn_extremalVertex hε hgerm hLower A hraw hPacking
      (by
        obtain ⟨s, hs⟩ := hS₀
        exact ⟨s.1, s, hs, rfl⟩)
      hline hColumnable hNotColumn
  have hselected (z : Tiling.Plane)
      (hz : axis.transverseCoord z = wall + c) :
      z ∈ properVertices (regularSupport C.region (Subtype.val '' S₀)) ↔
        axis.coord z - A.origin ∈ F :=
    selectedDatum_normalizedWall_proper_iff hε hgerm A hraw hline hz
  have hsliceTrans (x : ℝ) :
      axis.transverseCoord
        (FilledSliceChains.slicePoint axis (wall + c) (x + A.origin)) =
        wall + c := by
    cases axis <;>
      simp [FilledSliceChains.slicePoint, Axis.transverseCoord]
  have hsliceCoord (x : ℝ) :
      axis.coord
        (FilledSliceChains.slicePoint axis (wall + c) (x + A.origin)) =
        x + A.origin := by
    cases axis <;> simp [FilledSliceChains.slicePoint, Axis.coord]
  have hslicePoint (z : Tiling.Plane)
      (hz : axis.transverseCoord z = wall + c) :
      FilledSliceChains.slicePoint axis (wall + c) (axis.coord z) = z := by
    cases axis with
    | horizontal =>
        apply Complex.ext
        · simp [FilledSliceChains.slicePoint, Axis.coord]
        · change z.im = wall + c at hz
          simpa [FilledSliceChains.slicePoint] using hz.symm
    | vertical =>
        apply Complex.ext
        · change z.re = wall + c at hz
          simpa [FilledSliceChains.slicePoint] using hz.symm
        · simp [FilledSliceChains.slicePoint, Axis.coord]
  have hpointNorm (x : ℝ) :
      axis.coord
          (FilledSliceChains.slicePoint axis (wall + c) (x + A.origin)) -
          A.origin = x := by
    rw [hsliceCoord]
    ring
  have hpointProper (x : ℝ) (hx : x ∈ F) :
      FilledSliceChains.slicePoint axis (wall + c) (x + A.origin) ∈
        properVertices (regularSupport C.region (Subtype.val '' S₀)) := by
    apply (hselected _ (hsliceTrans x)).mpr
    rw [hpointNorm]
    exact hx
  let wallPoint : ℝ → ↥(properVertices Source) := fun x =>
    if hx : x ∈ F then
      ⟨FilledSliceChains.slicePoint axis (wall + c) (x + A.origin),
        hpointProper x hx⟩
    else ⟨wallSeed, hwallSeed⟩
  have hwallPoint_eq (x : ℝ) (hx : x ∈ F) :
      wallPoint x =
        ⟨FilledSliceChains.slicePoint axis (wall + c) (x + A.origin),
          hpointProper x hx⟩ := by
    simp [wallPoint, hx]
  have hwallPointValue (x : ℝ) (hx : x ∈ F) :
      axis.coord (wallPoint x).1 - A.origin = x := by
    rw [hwallPoint_eq x hx, hsliceCoord]
    ring
  have hwallPointMinimum (x : ℝ) (hx : x ∈ F) :
      IsMinimum (wallPoint x) := by
    change ∀ v ∈ properVertices Source,
      axis.transverseCoord (wallPoint x).1 ≤ axis.transverseCoord v
    rw [hwallPoint_eq x hx]
    exact outerWall_properVertex_transverse_isMinimal axis hline hLower
      (hpointProper x hx) (hsliceTrans x)
  have hminimumWall (u : ↥(properVertices Source)) (hu : IsMinimum u) :
      axis.transverseCoord u.1 = wall + c :=
    (hminimumIff u u.2).mp hu
  have hminimumFrontier (u : ↥(properVertices Source)) (hu : IsMinimum u) :
      axis.coord u.1 - A.origin ∈ F := by
    exact hwallFrontier u.1 u.2 (hminimumWall u hu)
  have hFsubset : F ⊆
      {x | ∃ e : IndexedSectionEndpoint A S₀, e.sourceValue = x} := by
    exact E₀.source_frontier_subset
  have hFlocallyFinite : ∀ a b : ℝ, (F ∩ Set.Icc a b).Finite := by
    intro a b
    apply (E₀.sourceValues_locallyFinite a b).subset
    intro x hx
    exact ⟨hFsubset hx.1, hx.2⟩
  let realStep : ℝ → ℝ → Prop := fun x y =>
    x ∈ F ∧ y ∈ F ∧
      ((x < y ∧ ∀ z, z ∈ F → ¬ (x < z ∧ z < y)) ∨
        (y < x ∧ ∀ z, z ∈ F → ¬ (y < z ∧ z < x)))
  let step : ↥(properVertices Source) → ↥(properVertices Source) → Prop :=
    fun u v =>
      IsMinimum u ∧ IsMinimum v ∧
        axis.coord u.1 - A.origin ∈ F ∧
        axis.coord v.1 - A.origin ∈ F ∧
        ((axis.coord u.1 - A.origin < axis.coord v.1 - A.origin ∧
            ∀ x, x ∈ F →
              ¬ (axis.coord u.1 - A.origin < x ∧
                x < axis.coord v.1 - A.origin)) ∨
          (axis.coord v.1 - A.origin < axis.coord u.1 - A.origin ∧
            ∀ x, x ∈ F →
              ¬ (axis.coord v.1 - A.origin < x ∧
                x < axis.coord u.1 - A.origin)))
  have hconn : ∀ u ∈ MinimumVertices, ∀ v ∈ MinimumVertices,
      Relation.ReflTransGen step u v := by
    intro u hu v hv
    let x := axis.coord u.1 - A.origin
    let y := axis.coord v.1 - A.origin
    have hx : x ∈ F := hminimumFrontier u hu
    have hy : y ∈ F := hminimumFrontier v hv
    have hreal := locallyFiniteReal_consecutiveEndpoint_reflTransGen
      F hFlocallyFinite hx hy
    have hmap : ∀ x y : ℝ, realStep x y →
        step (wallPoint x) (wallPoint y) := by
      intro x y hxy
      rcases hxy with ⟨hx, hy, hbetween⟩
      have hxMin := hwallPointMinimum x hx
      have hyMin := hwallPointMinimum y hy
      have hxValue := hwallPointValue x hx
      have hyValue := hwallPointValue y hy
      change IsMinimum (wallPoint x) ∧ IsMinimum (wallPoint y) ∧
          axis.coord (wallPoint x).1 - A.origin ∈ F ∧
          axis.coord (wallPoint y).1 - A.origin ∈ F ∧
          ((axis.coord (wallPoint x).1 - A.origin <
                axis.coord (wallPoint y).1 - A.origin ∧
              ∀ z, z ∈ F →
                ¬ (axis.coord (wallPoint x).1 - A.origin < z ∧
                  z < axis.coord (wallPoint y).1 - A.origin)) ∨
            (axis.coord (wallPoint y).1 - A.origin <
                axis.coord (wallPoint x).1 - A.origin ∧
              ∀ z, z ∈ F →
                ¬ (axis.coord (wallPoint y).1 - A.origin < z ∧
                  z < axis.coord (wallPoint x).1 - A.origin)))
      rw [hxValue, hyValue]
      exact ⟨hxMin, hyMin, hx, hy, hbetween⟩
    have hpath : Relation.ReflTransGen step (wallPoint x) (wallPoint y) :=
      hreal.lift wallPoint (fun x y hxy => hmap x y hxy)
    have hstart : wallPoint x = u := by
      apply Subtype.ext
      rw [hwallPoint_eq x hx]
      change FilledSliceChains.slicePoint axis (wall + c) (x + A.origin) = u.1
      have huWall := hminimumWall u hu
      have hsum : x + A.origin = axis.coord u.1 := by
        dsimp [x]
        ring
      rw [hsum]
      exact hslicePoint u.1 huWall
    have hfinish : wallPoint y = v := by
      apply Subtype.ext
      rw [hwallPoint_eq y hy]
      change FilledSliceChains.slicePoint axis (wall + c) (y + A.origin) = v.1
      have hvWall := hminimumWall v hv
      have hsum : y + A.origin = axis.coord v.1 := by
        dsimp [y]
        ring
      rw [hsum]
      exact hslicePoint v.1 hvWall
    rw [hstart, hfinish] at hpath
    exact hpath
  have hstep : ∀ u v, step u v →
      (pair.theta u).1 - u.1 = beta →
        (pair.theta v).1 - v.1 = beta := by
    intro u v huv huBeta
    rcases huv with ⟨huMin, hvMin, huFront, hvFront, hadj⟩
    have hedge := hAdjacent u v huMin hvMin ⟨huFront, hvFront, hadj⟩
    calc
      (pair.theta v).1 - v.1 =
          ((pair.theta v).1 - (pair.theta u).1) +
            ((pair.theta u).1 - u.1) - (v.1 - u.1) := by abel
      _ = (v.1 - u.1) + ((pair.theta u).1 - u.1) - (v.1 - u.1) := by
        rw [hedge]
      _ = beta := by rw [huBeta]; abel
  have hseedSet : ∃ u ∈ MinimumVertices,
      (pair.theta u).1 - u.1 = beta := ⟨u₀, hu₀min, hseed⟩
  have hpropagated := extremalTrace_displacement_propagates
    (show MinimumVertices.Nonempty from ⟨u₀, hu₀min⟩)
    step hconn hstep hseedSet
  intro u hu
  exact hpropagated u hu

private theorem actualPair_nearWall_displacement_propagates
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S₀ S₁ : Set ↥C.centres}
    {hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀))}
    {hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁))}
    {hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀))}
    {hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))}
    {eta beta : Tiling.Plane}
    (pair : ActualProperVertexPairCorrespondence C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ eta)
    (P : FLCControlPackage C)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (axis : Axis) {traceRadius : ℝ}
    (hPaths : ∀ {S : Set Tiling.Plane}, S ⊆ C.centres → S.Nonempty →
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements S) →
      Linked (60 * Metric.diam C.region.openCarrier) S →
      (∃ c, ∀ s ∈ S, axis.transverseCoord s = c) →
      ¬ IsCenterColumn axis C.region S →
      ∀ u, ∀ hu : u ∈ properVertices (regularSupport C.region S),
        ∃ e, ∃ he : e ∈ properVertices (regularSupport C.region S),
          Relation.ReflTransGen
            (fun x y : ↥(properVertices (regularSupport C.region S)) =>
              dist x.1 y.1 < traceRadius)
            ⟨u, hu⟩ ⟨e, he⟩ ∧
          ∀ v ∈ properVertices (regularSupport C.region S),
            axis.transverseCoord e ≤ axis.transverseCoord v)
    (hMargin : traceRadius + 2 * P.localError < P.scale / 2)
    (hNonempty : S₀.Nonempty)
    (hPacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S₀)))
    (hLinked : Linked (60 * Metric.diam C.region.openCarrier) (Subtype.val '' S₀))
    (hAligned : ∃ c, ∀ s ∈ Subtype.val '' S₀, axis.transverseCoord s = c)
    (hNotColumn : ¬ IsCenterColumn axis C.region (Subtype.val '' S₀))
    (hMinimumSeed : ∀ e : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))),
      (∀ v ∈ properVertices (regularSupport C.region (Subtype.val '' S₀)),
        axis.transverseCoord e.1 ≤ axis.transverseCoord v) →
      (pair.theta e).1 - e.1 = beta) :
    ∀ u : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))),
      (pair.theta u).1 - u.1 = beta := by
  have hSourceSubset : Subtype.val '' S₀ ⊆ C.centres := by
    rintro s ⟨t, _ht, rfl⟩
    exact t.2
  have hSourceNonempty : (Subtype.val '' S₀).Nonempty := by
    obtain ⟨s, hs⟩ := hNonempty
    exact ⟨s.1, s, hs, rfl⟩
  have hbackward :
      ∀ {u v : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀)))},
        Relation.ReflTransGen
          (fun x y : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))) =>
            dist x.1 y.1 < traceRadius) u v →
        (pair.theta v).1 - v.1 = beta →
          (pair.theta u).1 - u.1 = beta := by
    intro u v huv
    induction huv with
    | refl => exact fun hu => hu
    | @tail v w _hpath hstep ih =>
        intro hw
        have hReverseRadius : dist w.1 v.1 < traceRadius := by
          simpa only [dist_comm] using hstep
        have hReverseMargin : dist w.1 v.1 + P.localError < P.scale / 2 := by
          linarith [P.localError_pos]
        have hReverseDistance : dist w.1 v.1 < P.scale := by
          linarith [P.localError_pos, P.scale_pos]
        exact ih (actualProperVertexPair_shortStep_preserves_displacement
          pair P hphi w v hReverseDistance hReverseMargin hw)
  intro u
  obtain ⟨e, he, hpath, hminimum⟩ := hPaths hSourceSubset hSourceNonempty
    hPacking hLinked hAligned hNotColumn u.1 u.2
  exact hbackward hpath (hMinimumSeed ⟨e, he⟩ hminimum)

/-!
Literal public columnable endpoint assembled from the actual source/target data.
This authoring fragment has not been compiled or accepted yet.
-/

theorem columnableAxisLocalTransport :
    ∀ {C : ApproximationContext.{0}} (_hFLC : HasFLC C.centres) (axis : Axis)
      (_hColumnable : ∃ Col : Set Tiling.Plane, IsCenterColumn axis C.region Col),
      ∃ recoveryScale : ℝ, 0 < recoveryScale ∧
        ∀ (P : FLCControlPackage C), recoveryScale < P.scale →
        ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
          IsEpsilonApproximation C P.threshold phi →
        ∀ (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane),
          (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
        ∀ (S₀ S₁ : Set ↥C.centres) (G : ℝ),
          G = 60 * Metric.diam C.region.openCarrier →
        (Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
            (C.region.toPolygonalRegion.placements (Set.image Subtype.val S₀)) ∧
         Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
            (C.region.toPolygonalRegion.placements (Set.image Subtype.val S₁)) ∧
         Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
            (D.deformedRegion.toPolygonalRegion.placements
              (deformedCenterCarrierOn Tphi S₀)) ∧
         Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
            (D.deformedRegion.toPolygonalRegion.placements
              (deformedCenterCarrierOn Tphi S₁))) →
        S₀.Nonempty ∧ S₁.Nonempty →
        ((∃ c, ∀ s : S₀, axis.transverseCoord (Tphi s) = c) ∧
         (∃ c, ∀ s : S₁, axis.transverseCoord (Tphi s) = c)) →
        Linked G (Set.image Subtype.val S₀) ∧ Linked G (Set.image Subtype.val S₁) →
        ∀ imagePeriod : Tiling.Plane, imagePeriod ≠ 0 →
          axis.transverseCoord imagePeriod = 0 →
        (imagePeriod +ᵥ deformedCenterCarrierOn Tphi S₀ =
            deformedCenterCarrierOn Tphi S₀ ∧
         imagePeriod +ᵥ deformedCenterCarrierOn Tphi S₁ =
            deformedCenterCarrierOn Tphi S₁) →
        ¬ IsCenterColumn axis C.region (Set.image Subtype.val S₀) →
        ∀ eta, regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁) =
          eta +ᵥ regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀) →
        ∃ beta : {z : Tiling.Plane //
          z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
          regularSupport C.region (Set.image Subtype.val S₁) =
            (beta : Tiling.Plane) +ᵥ regularSupport C.region (Set.image Subtype.val S₀) ∧
          mapPoint phi beta = eta ∧
          properVertices (regularSupport C.region (Set.image Subtype.val S₀)) ≠ ∅ ∧
          properVertices (regularSupport C.region (Set.image Subtype.val S₁)) ≠ ∅ := by
  classical
  intro C hFLC axis hColumnable
  obtain ⟨outerA, wall, ε, transverse, A, R, massExpression, corrections,
      W, K, N, B, mu, delta, G₀, traceRadius, recoveryScale, finalScale,
      _hTransverse, hraw, _hOuterNonempty, hε, hLower, hgerm, _hRpositive,
      hmassExpression, hmassWeight, _hBpositive, hmassBound, hcorrections,
      hCodes, hK, hmu, hseparate, hdelta, hPackingSeparation, hG₀, hGpositive,
      _hTraceRadiusPositive, hPaths, hNdelta, _hRecoveryPositive, hFinalPositive,
      _hRecoveryLeFinal, _hGeometryLeFinal, hScaleControls⟩ :=
    columnable_preApproximationControls hFLC axis hColumnable
  refine ⟨finalScale, hFinalPositive, ?_⟩
  intro P hP phi hphi D Tphi hTphi S₀ S₁ G hG hPackings hNonempty hTargetLines
    hLinked imagePeriod hImagePeriodNe hImagePeriodAxis hImagePeriods hNotColumn eta hImageSupport
  obtain ⟨hGeometryScale, hR, hNG, hError, hdScale, hErrorD, hDiam,
      hGmargin, hTraceMargin, hLongScale⟩ := hScaleControls P hP
  obtain ⟨hPack₀, hPack₁, hTargetPack₀, hTargetPack₁⟩ := hPackings
  obtain ⟨hS₀, hS₁⟩ := hNonempty
  obtain ⟨hTargetLine₀, hTargetLine₁⟩ := hTargetLines
  obtain ⟨hLinked₀, hLinked₁⟩ := hLinked
  obtain ⟨hImagePeriod₀, hImagePeriod₁⟩ := hImagePeriods
  have hGeq : G = G₀ := hG.trans hG₀.symm
  rw [hGeq] at hLinked₀ hLinked₁
  have sourceGeometry₀ := periodicImageLine_sourceGeometry P hGeometryScale phi hphi
    Tphi hTphi axis S₀ G₀ hGpositive hGmargin hS₀ hLinked₀ hTargetLine₀
    imagePeriod hImagePeriodNe hImagePeriodAxis hImagePeriod₀
  have sourceGeometry₁ := periodicImageLine_sourceGeometry P hGeometryScale phi hphi
    Tphi hTphi axis S₁ G₀ hGpositive hGmargin hS₁ hLinked₁ hTargetLine₁
    imagePeriod hImagePeriodNe hImagePeriodAxis hImagePeriod₁
  obtain ⟨c₀, hline₀⟩ := sourceGeometry₀.1
  obtain ⟨c₁, hline₁⟩ := sourceGeometry₁.1
  have hSource₀ := packing_regularSupport_isLocallyAxisParallelPolygonal hPack₀
  have hSource₁ := packing_regularSupport_isLocallyAxisParallelPolygonal hPack₁
  have hTarget₀ := packing_regularSupport_isLocallyAxisParallelPolygonal hTargetPack₀
  have hTarget₁ := packing_regularSupport_isLocallyAxisParallelPolygonal hTargetPack₁
  obtain ⟨pair⟩ := actualProperVertexPairCorrespondence_exists P hGeometryScale
    phi hphi D Tphi hTphi S₀ S₁ hPack₀ hPack₁ hTargetPack₀ hTargetPack₁
    hSource₀ hSource₁ hTarget₀ hTarget₁ eta hImageSupport
  have hIndexedLine₀ : ∃ c, ∀ s : S₀, axis.transverseCoord s.1.1 = c :=
    ⟨c₀, fun s => hline₀ s.1.1 ⟨s.1, s.2, rfl⟩⟩
  have hIndexedLine₁ : ∃ c, ∀ s : S₁, axis.transverseCoord s.1.1 = c :=
    ⟨c₁, fun s => hline₁ s.1.1 ⟨s.1, s.2, rfl⟩⟩
  have hPlaneSeparation₀ : ∀ s ∈ S₀, ∀ t ∈ S₀, s ≠ t →
      delta ≤ dist (s : Tiling.Plane) (t : Tiling.Plane) := by
    intro s hs t ht hne
    apply hPackingSeparation (Subtype.val '' S₀) hPack₀
      s.1 ⟨s, hs, rfl⟩ t.1 ⟨t, ht, rfl⟩
    intro h
    exact hne (Subtype.ext h)
  have hPlaneSeparation₁ : ∀ s ∈ S₁, ∀ t ∈ S₁, s ≠ t →
      delta ≤ dist (s : Tiling.Plane) (t : Tiling.Plane) := by
    intro s hs t ht hne
    apply hPackingSeparation (Subtype.val '' S₁) hPack₁
      s.1 ⟨s, hs, rfl⟩ t.1 ⟨t, ht, rfl⟩
    intro h
    exact hne (Subtype.ext h)
  obtain ⟨E₀⟩ := (endpointPlaneSeparation_control (A := A) P hLinked₀
    hPlaneSeparation₀ hIndexedLine₀ hdelta hNdelta hNG rfl hdScale).2
      phi hphi D Tphi hTphi hTargetPack₀ hTargetLine₀ hError hErrorD
  obtain ⟨E₁⟩ := (endpointPlaneSeparation_control (A := A) P hLinked₁
    hPlaneSeparation₁ hIndexedLine₁ hdelta hNdelta hNG rfl hdScale).2
      phi hphi D Tphi hTphi hTargetPack₁ hTargetLine₁ hError hErrorD
  obtain ⟨w₀, hw₀, hw₀wall, hwallLower₀, hminimumIff₀, _hWallFrontier₀⟩ :=
    selectedDatum_noncolumn_extremalVertex hε hgerm hLower A hraw hPack₀
      (hS₀.image Subtype.val) hline₀ hColumnable hNotColumn
  let u₀ : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))) := ⟨w₀, hw₀⟩
  have hNotColumn₁ : ¬ IsCenterColumn axis C.region (Subtype.val '' S₁) := by
    intro hColumn
    have hproper := (pair.theta u₀).2
    simp only [centerColumn_noProperVertices hColumn, Set.mem_empty_iff_false] at hproper
  obtain ⟨w₁, hw₁, hw₁wall, _hwallLower₁, hminimumIff₁, _hWallFrontier₁⟩ :=
    selectedDatum_noncolumn_extremalVertex hε hgerm hLower A hraw hPack₁
      (hS₁.image Subtype.val) hline₁ hColumnable hNotColumn₁
  let u₁ : ↥(properVertices (regularSupport C.region (Subtype.val '' S₁))) := ⟨w₁, hw₁⟩
  obtain ⟨e, hOrder, hFormula⟩ := actualPair_selectedWall_frontierOrderEquiv pair E₀ E₁
    P hphi hDiam hε hgerm hraw hline₀ hline₁ hLower u₀ hw₀wall u₁ hw₁wall
  have hForward (u v : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))))
      (huMin : ∀ w ∈ properVertices (regularSupport C.region (Subtype.val '' S₀)),
        axis.transverseCoord u.1 ≤ axis.transverseCoord w)
      (hvMin : ∀ w ∈ properVertices (regularSupport C.region (Subtype.val '' S₀)),
        axis.transverseCoord v.1 ≤ axis.transverseCoord w)
      (huF : axis.coord u.1 - A.origin ∈ frontier
        (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀)))))
      (hvF : axis.coord v.1 - A.origin ∈ frontier
        (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀)))))
      (huv : axis.coord u.1 - A.origin < axis.coord v.1 - A.origin)
      (hno : ∀ x, x ∈ frontier
        (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀)))) →
        ¬ (axis.coord u.1 - A.origin < x ∧ x < axis.coord v.1 - A.origin)) :
      (pair.theta v).1 - (pair.theta u).1 = v.1 - u.1 := by
    have huMinPV := fun w : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))) => huMin w.1 w.2
    have hvMinPV := fun w : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))) => hvMin w.1 w.2
    have huWall := (hminimumIff₀ u.1 u.2).mp huMin
    have hvWall := (hminimumIff₀ v.1 v.2).mp hvMin
    have hThetaUMin := (actualPair_theta_preserves_transverse_minimum pair P hphi
      hDiam axis ⟨c₀, hline₀⟩ ⟨c₁, hline₁⟩ u).mp huMinPV
    have hThetaVMin := (actualPair_theta_preserves_transverse_minimum pair P hphi
      hDiam axis ⟨c₀, hline₀⟩ ⟨c₁, hline₁⟩ v).mp hvMinPV
    have hThetaUWall := (hminimumIff₁ (pair.theta u).1 (pair.theta u).2).mp
      (fun w hw => hThetaUMin ⟨w, hw⟩)
    have hThetaVWall := (hminimumIff₁ (pair.theta v).1 (pair.theta v).2).mp
      (fun w hw => hThetaVMin ⟨w, hw⟩)
    have hThetaUF := (selectedDatum_normalizedWall_proper_iff hε hgerm A hraw
      hline₁ hThetaUWall).mp (pair.theta u).2
    have hThetaVF := (selectedDatum_normalizedWall_proper_iff hε hgerm A hraw
      hline₁ hThetaVWall).mp (pair.theta v).2
    obtain ⟨hTargetOrder, hTargetGap⟩ := frontierOrderEquiv_maps_consecutive_values
      e hOrder huF hvF huv (fun x hx hxF => hno x hxF hx)
    rw [hFormula u huMinPV huF, hFormula v hvMinPV hvF] at hTargetOrder hTargetGap
    exact actualPair_consecutiveWallEdge_displacement pair P hphi hTphi E₀ E₁ u v
      (huWall.trans hvWall.symm) (hThetaUWall.trans hThetaVWall.symm)
      huF hvF hThetaUF hThetaVF huv hTargetOrder
      (fun x hx hxF => hno x hxF hx) hTargetGap hLinked₀ hLinked₁ hGmargin
      sourceGeometry₀.2 sourceGeometry₁.2 hPack₀ hPack₁
      ⟨c₀, hline₀⟩ ⟨c₁, hline₁⟩ massExpression corrections hCodes W K B mu
      hmassExpression hmassWeight hmassBound hcorrections hK hmu hseparate hR hLongScale
  have hAdjacent : ∀ u v : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))),
      (∀ w ∈ properVertices (regularSupport C.region (Subtype.val '' S₀)),
        axis.transverseCoord u.1 ≤ axis.transverseCoord w) →
      (∀ w ∈ properVertices (regularSupport C.region (Subtype.val '' S₀)),
        axis.transverseCoord v.1 ≤ axis.transverseCoord w) →
      let F := frontier (interior (closure (A.carrier + axis.coord '' (Subtype.val '' S₀))))
      axis.coord u.1 - A.origin ∈ F ∧ axis.coord v.1 - A.origin ∈ F ∧
        ((axis.coord u.1 - A.origin < axis.coord v.1 - A.origin ∧
            ∀ x, x ∈ F → ¬ (axis.coord u.1 - A.origin < x ∧
              x < axis.coord v.1 - A.origin)) ∨
          (axis.coord v.1 - A.origin < axis.coord u.1 - A.origin ∧
            ∀ x, x ∈ F → ¬ (axis.coord v.1 - A.origin < x ∧
              x < axis.coord u.1 - A.origin))) →
      (pair.theta v).1 - (pair.theta u).1 = v.1 - u.1 := by
    intro u v huMin hvMin
    dsimp only
    rintro ⟨huF, hvF, hCases⟩
    rcases hCases with ⟨huv, hno⟩ | ⟨hvu, hno⟩
    · exact hForward u v huMin hvMin huF hvF huv hno
    · have hReverse := hForward v u hvMin huMin hvF huF hvu hno
      calc
        (pair.theta v).1 - (pair.theta u).1 =
            -((pair.theta u).1 - (pair.theta v).1) := by abel
        _ = -(u.1 - v.1) := by rw [hReverse]
        _ = v.1 - u.1 := by abel
  obtain ⟨beta, hBeta, hMap⟩ := pair.controlled_displacement u₀
  have hu₀min : ∀ v ∈ properVertices (regularSupport C.region (Subtype.val '' S₀)),
      axis.transverseCoord u₀.1 ≤ axis.transverseCoord v := by
    simpa only [u₀, hw₀wall] using hwallLower₀
  have hMinimumDisplacement := actualWallConsecutive_displacement_propagates pair E₀
    hε hgerm hLower hraw hPack₀ hS₀ hline₀ hColumnable hNotColumn
    u₀ hu₀min (beta : Tiling.Plane) hBeta.symm hAdjacent
  have hAllDisplacement := actualPair_nearWall_displacement_propagates pair P hphi axis
    hPaths hTraceMargin hS₀ hPack₀ (by simpa only [hG₀] using hLinked₀)
    ⟨c₀, hline₀⟩ hNotColumn hMinimumDisplacement
  have hVertices : properVertices (regularSupport C.region (Subtype.val '' S₁)) =
      (beta : Tiling.Plane) +ᵥ properVertices
        (regularSupport C.region (Subtype.val '' S₀)) := by
    ext p
    constructor
    · intro hp
      let q := pair.theta.symm ⟨p, hp⟩
      have hq := hAllDisplacement q
      have hqp : (pair.theta q).1 = p := congrArg Subtype.val
        (pair.theta.apply_symm_apply ⟨p, hp⟩)
      rw [hqp] at hq
      refine ⟨q.1, q.2, ?_⟩
      change (beta : Tiling.Plane) + q.1 = p
      rw [← hq]
      abel
    · rintro ⟨q, hq, rfl⟩
      have hDisplacement := hAllDisplacement ⟨q, hq⟩
      have htheta : (pair.theta ⟨q, hq⟩).1 = (beta : Tiling.Plane) + q := by
        rw [← hDisplacement]
        abel
      change (beta : Tiling.Plane) + q ∈
        properVertices (regularSupport C.region (Subtype.val '' S₁))
      rw [← htheta]
      exact (pair.theta ⟨q, hq⟩).2
  have hCones : ∀ p, ∀ hp : p ∈ properVertices
      (regularSupport C.region (Subtype.val '' S₀)),
      ∀ hp' : (beta : Tiling.Plane) + p ∈ properVertices
        (regularSupport C.region (Subtype.val '' S₁)),
      localCone _ ((beta : Tiling.Plane) + p) hSource₁ hp' =
        localCone _ p hSource₀ hp := by
    intro p hp hp'
    have hDisplacement := hAllDisplacement ⟨p, hp⟩
    have htheta : (pair.theta ⟨p, hp⟩).1 = (beta : Tiling.Plane) + p := by
      rw [← hDisplacement]
      abel
    simpa only [htheta, localCone] using (pair.cone_preserved ⟨p, hp⟩).symm
  have hSupportNonempty₀ : (regularSupport C.region (Subtype.val '' S₀)).Nonempty :=
    Set.Nonempty.of_closure ⟨w₀, frontier_subset_closure hw₀.1⟩
  have hSupportNonempty₁ : (regularSupport C.region (Subtype.val '' S₁)).Nonempty :=
    Set.Nonempty.of_closure ⟨w₁, frontier_subset_closure hw₁.1⟩
  have hSupportProper₀ : regularSupport C.region (Subtype.val '' S₀) ≠ Set.univ := by
    intro h
    have hf := hw₀.1
    simp only [h, frontier_univ, Set.mem_empty_iff_false] at hf
  have hSupportProper₁ : regularSupport C.region (Subtype.val '' S₁) ≠ Set.univ := by
    intro h
    have hf := hw₁.1
    simp only [h, frontier_univ, Set.mem_empty_iff_false] at hf
  have hSupport := support_eq_vadd_of_properVertexGerms hSource₀ hSource₁
    hSupportNonempty₀ hSupportNonempty₁ hSupportProper₀ hSupportProper₁ beta
    hVertices hCones
    (noncolumn_completeBoundaryLine_meetsProperVertices axis hColumnable
      (hS₀.image Subtype.val) hPack₀ ⟨c₀, hline₀⟩ hNotColumn hSource₀)
    (noncolumn_completeBoundaryLine_meetsProperVertices axis hColumnable
      (hS₁.image Subtype.val) hPack₁ ⟨c₁, hline₁⟩ hNotColumn₁ hSource₁)
  exact ⟨beta, hSupport, hMap, (show
    (properVertices (regularSupport C.region (Subtype.val '' S₀))).Nonempty from
      ⟨w₀, hw₀⟩).ne_empty, (show
    (properVertices (regularSupport C.region (Subtype.val '' S₁))).Nonempty from
      ⟨w₁, hw₁⟩).ne_empty⟩

theorem verticalFLCNoGapOrbitTransport :
    ∀ {C : ApproximationContext.{0}} (_hFLC : HasFLC C.centres)
      (_hColumnable : ∃ Col : Set Tiling.Plane,
        IsCenterColumn Axis.vertical C.region Col),
      ∃ recoveryScale : ℝ, 0 < recoveryScale ∧
        ∀ (P : FLCControlPackage C), recoveryScale < P.scale →
        ∀ (B : PeriodicBandData C), IsPeriodicBandFineness B P.threshold →
        ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
          IsEpsilonApproximation C P.threshold phi →
        ∀ (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane),
          (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
          ∀ (Dcmp : RationalDirectionalDecomposition
              D.deformedRegion (Set.range Tphi))
            (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
              RationalSlice (Dcmp.direction i) → Set Tiling.Plane),
            (∀ i Q, Q ∈ (Dcmp.orbit i).phases →
              originalSlice i Q = Set.image Subtype.val
                {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)}) →
            ∀ (i : Fin Dcmp.numberOfParts)
              (Q : RationalSlice (Dcmp.direction i)),
              (∀ m : ℤ, Q.vadd (m • Dcmp.gamma.toPlane) ∈
                (Dcmp.orbit i).noGapPhases (originalSlice i)
                  (60 * Metric.diam C.region.openCarrier)) →
              (Dcmp.direction i).toPlane.re = 0 →
              (¬ IsCenterColumn Axis.vertical C.region (originalSlice i Q)) →
              ∀ m : ℤ, ∃ beta : {z : Tiling.Plane //
                z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
                regularSupport C.region
                    (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
                  (beta : Tiling.Plane) +ᵥ
                    regularSupport C.region (originalSlice i Q) ∧
                mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
                properVertices (regularSupport C.region
                  (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
  intro C hFLC hColumnable
  obtain ⟨recoveryScale, hRecoveryScale,
    hColumnableTransport⟩ :=
      columnableAxisLocalTransport hFLC Axis.vertical hColumnable
  refine ⟨recoveryScale, hRecoveryScale, ?_⟩
  intro P hRecovery Pband hFine phi hphi D Tphi hTphi Dcmp originalSlice
    hPreimage i Q hOrbitNoGap hvertical hNotColumn m
  let G : ℝ := 60 * Metric.diam C.region.openCarrier
  obtain ⟨data⟩ := verticalNoGapOrbitPairData_exists (phi := phi)
    P Pband hFine hphi D Tphi hTphi Dcmp originalSlice hPreimage i Q G m
    (by simpa [G] using hOrbitNoGap) hvertical
  have hNotColumnIndices :
      ¬ IsCenterColumn Axis.vertical C.region
        (Set.image Subtype.val data.S₀) := by
    rw [← data.source₀_eq]
    exact hNotColumn
  have hTransported := hColumnableTransport P hRecovery phi hphi D Tphi hTphi
    data.S₀ data.Sₘ G (by rfl)
    ⟨data.sourcePacking₀, data.sourcePackingₘ,
      data.imagePacking₀, data.imagePackingₘ⟩
    ⟨data.nonempty₀, data.nonemptyₘ⟩
    ⟨data.imageLine₀, data.imageLineₘ⟩
    ⟨data.linked₀, data.linkedₘ⟩
    data.imagePeriod data.imagePeriod_ne data.imagePeriod_vertical
    ⟨data.imagePeriod_invariant₀, data.imagePeriod_invariantₘ⟩
    hNotColumnIndices
  obtain ⟨beta, hSupport, hMap, _hProper₀, hProperₘ⟩ :=
    hTransported (m • Dcmp.gamma.toPlane) data.imageSupport_shift
  refine ⟨beta, ?_, hMap, ?_⟩
  · rw [data.sourceₘ_eq, data.source₀_eq]
    exact hSupport
  · rw [data.sourceₘ_eq]
    exact hProperₘ

end Tiling.AxisParallel.Terminal
