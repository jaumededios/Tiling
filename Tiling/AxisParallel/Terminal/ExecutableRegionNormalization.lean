import Tiling.AxisParallel.Terminal.ExecutableInputSemantics
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Terminal.ExecutableInput
import Tiling.AxisParallel.Terminal.OracleProgramCore
import Tiling.AxisParallel.Terminal.CertificateCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Pointwise
open Set
open Tiling.AxisParallel.IntrinsicVertices

namespace Tiling.AxisParallel.Terminal.Executable.Semantics

private def evalCoeffAgainst {C : RegionCode}
    (vertex : Fin C.vertexCount → Tiling.Plane) (s : CoordSort) (a : Coeff C) : Real :=
  ∑ i, (a i : Real) * s.axis.coord (vertex i)

/-- Correctness of an oracle whose finite identifiers denote original, untranslated vertices. -/
def CorrectOriginalOracle {C : RegionCode} (vertex : Fin C.vertexCount → Tiling.Plane)
    (O : Oracle C) : Prop :=
  ∀ q, O.answer q = true ↔
    evalCoeffAgainst vertex q.sort q.lhs ≤ evalCoeffAgainst vertex q.sort q.rhs

private def realizationClosedCell {C : RegionCode} (R : Realization C)
    (e : Fin C.cellCount) : Set Tiling.Plane :=
  closedAxisBox
    (R.vertex (C.leftVertex e)).re (R.vertex (C.rightVertex e)).re
    (R.vertex (C.bottomVertex e)).im (R.vertex (C.topVertex e)).im

/-- Proof-only bridge from an arbitrary region to finite normalized runtime input. -/
structure RegionNormalization (K : Tiling.AxisParallel.Region) where
  anchor : Tiling.Plane
  anchor_mem : anchor ∈ K.vertices
  code : RegionCode
  normalized : Realization code
  originalVertex : Fin code.vertexCount → Tiling.Plane
  originalVertex_injective : Function.Injective originalVertex
  originalVertex_range : Set.range originalVertex = K.vertices
  origin_originalVertex : originalVertex code.originVertex = anchor
  normalizedVertex_formula : ∀ i, normalized.vertex i = originalVertex i - anchor
  normalized_support : normalized.region.support = (-anchor) +ᵥ K.support
  normalized_openCarrier : normalized.region.openCarrier = (-anchor) +ᵥ K.openCarrier
  normalized_vertices : normalized.region.vertices = (-anchor) +ᵥ K.vertices
  intrinsicVertexEquiv : Fin code.vertexCount ≃ ↥K.vertices
  intrinsicVertexEquiv_value : ∀ i,
    ((intrinsicVertexEquiv i : ↥K.vertices) : Tiling.Plane) = originalVertex i
  closedCell_intrinsic : ∀ e, IsIntrinsicGridRectangle normalized.region
    (realizationClosedCell normalized e)
  closedCells_cover : (⋃ e, realizationClosedCell normalized e) = normalized.region.support
  closedCells_pairwiseIntersection_volume_zero : ∀ e₁ e₂, e₁ ≠ e₂ →
    MeasureTheory.volume
      (realizationClosedCell normalized e₁ ∩ realizationClosedCell normalized e₂) = 0
  tilesOn_translate : ∀ S : Set Tiling.Plane,
    Tiling.AxisParallel.TilesOn K S Set.univ ↔
      Tiling.AxisParallel.TilesOn normalized.region (anchor +ᵥ S) Set.univ

/-- Finite identifier bridge from a normalization to a historical encoded region. -/
structure LegacyNormalizationAdapter (E : EncodedAxisParallelRegion)
    (N : RegionNormalization E.region) where
  vertexEquiv : Fin N.code.vertexCount ≃ ↥E.region.vertexFinset
  intrinsic_compat : ∀ i,
    ((vertexEquiv i : ↥E.region.vertexFinset) : Tiling.Plane) =
      ((N.intrinsicVertexEquiv i : ↥E.region.vertices) : Tiling.Plane)
  vertexEquiv_value : ∀ i,
    ((vertexEquiv i : ↥E.region.vertexFinset) : Tiling.Plane) = N.originalVertex i

noncomputable def toLegacyCoeff {E : EncodedAxisParallelRegion}
    {N : RegionNormalization E.region} (A : LegacyNormalizationAdapter E N)
    (a : Coeff N.code) : ↥E.region.vertexFinset →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun v => a (A.vertexEquiv.symm v))

noncomputable def toLegacyQuery {E : EncodedAxisParallelRegion}
    {N : RegionNormalization E.region} (A : LegacyNormalizationAdapter E N)
    (q : Query N.code) : CoordQuery E :=
  match q.sort with
  | .horizontal => .horizontalLe (toLegacyCoeff A q.lhs) (toLegacyCoeff A q.rhs)
  | .vertical => .verticalLe (toLegacyCoeff A q.lhs) (toLegacyCoeff A q.rhs)

private theorem sub_mem_uIcc_iff (a x p q : ℝ) :
    -a + x ∈ Set.uIcc p q ↔ x ∈ Set.uIcc (a + p) (a + q) := by
  simp only [Set.mem_uIcc]
  constructor
  · rintro (h | h)
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · rintro (h | h)
    · left; constructor <;> linarith
    · right; constructor <;> linarith

private theorem vadd_rectangle (a p q : Tiling.Plane) :
    a +ᵥ Complex.Rectangle p q = Complex.Rectangle (a + p) (a + q) := by
  ext z
  simp only [Complex.Rectangle, Set.mem_vadd_set_iff_neg_vadd_mem,
    Complex.mem_reProdIm, vadd_eq_add, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, sub_mem_uIcc_iff]

private noncomputable def vaddRectangulation {s : Set Tiling.Plane}
    (R : Tiling.Rectangulation s) (a : Tiling.Plane) :
    Tiling.Rectangulation (a +ᵥ s) where
  pieces := R.pieces.image (a +ᵥ ·)
  isRectangle := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨p, q, hre, him, rfl⟩ := R.isRectangle q hq
    exact ⟨a + p, a + q, by simpa using hre, by simpa using him,
      vadd_rectangle a p q⟩
  pairwiseAEDisjoint := by
    rw [Finset.coe_image]
    rintro _ ⟨r, hr, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    apply Tiling.aedisjoint_vadd a
    apply R.pairwiseAEDisjoint hr hq
    intro hrq
    exact hne (by simp [hrq])
  sUnion_eq := by
    ext z
    constructor
    · rintro ⟨u, hu, hzu⟩
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzu ⊢
      rw [← R.sUnion_eq]
      exact Set.mem_sUnion_of_mem hzu hq
    · intro hz
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz
      obtain ⟨q, hq, hzq⟩ := Set.mem_sUnion.mp (R.sUnion_eq.symm ▸ hz)
      exact Set.mem_sUnion_of_mem
        (by simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using hzq)
        (Finset.mem_image.mpr ⟨q, hq, rfl⟩)

private noncomputable def vaddRegion (K : Tiling.AxisParallel.Region)
    (a : Tiling.Plane) : Tiling.AxisParallel.Region where
  support := a +ᵥ K.support
  isPolygonal := K.isPolygonal.vadd a
  nonempty := by
    obtain ⟨x, hx⟩ := K.nonempty
    exact ⟨a + x, by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hx⟩
  isAxisParallel := by
    obtain ⟨R⟩ := K.isAxisParallel
    exact ⟨vaddRectangulation R a⟩

private theorem vaddRegion_openCarrier (K : Tiling.AxisParallel.Region)
    (a : Tiling.Plane) :
    (vaddRegion K a).openCarrier = a +ᵥ K.openCarrier := by
  change interior (a +ᵥ K.support) = a +ᵥ interior K.support
  rw [interior_vadd]

private theorem vaddRegion_vertices (K : Tiling.AxisParallel.Region)
    (a : Tiling.Plane) :
    (vaddRegion K a).vertices = a +ᵥ K.vertices := by
  exact Tiling.vertexSet_vadd a K.support

private theorem add_vadd_set (a b : Tiling.Plane) (S : Set Tiling.Plane) :
    a +ᵥ (b +ᵥ S) = (a + b) +ᵥ S := by
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  constructor <;> intro hx <;> convert hx using 1 <;> abel

private theorem vadd_neg_vadd_set (a : Tiling.Plane) (S : Set Tiling.Plane) :
    (-a) +ᵥ (a +ᵥ S) = S := by
  rw [add_vadd_set, neg_add_cancel, zero_vadd]

private theorem vaddRegion_neg_vadd (K : Tiling.AxisParallel.Region)
    (a : Tiling.Plane) : vaddRegion (vaddRegion K a) (-a) = K := by
  cases K with
  | mk K hK =>
      cases K with
      | mk Ks Kp Kn =>
          simp only [vaddRegion, Tiling.AxisParallel.Region.mk.injEq,
            Tiling.RationalPolygonal.PolygonalRegion.mk.injEq]
          exact vadd_neg_vadd_set a Ks

private theorem tilesOn_vadd
    (K : Tiling.AxisParallel.Region) (S D : Set Tiling.Plane)
    (a b : Tiling.Plane) (h : Tiling.AxisParallel.TilesOn K S D) :
    Tiling.AxisParallel.TilesOn (vaddRegion K a) (b +ᵥ S) ((a + b) +ᵥ D) := by
  refine ⟨?_, ?_, ?_⟩
  · have hset : b +ᵥ S = (fun s : Tiling.Plane ↦ b + s) '' S := by
      ext x
      constructor
      · intro hx
        exact ⟨-b + x, by
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hx,
          by abel_nf⟩
      · rintro ⟨s, hs, rfl⟩
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          neg_add_cancel_left] using hs
    rw [hset]
    exact h.1.image _
  · intro i hi j hj hij
    let i₀ : Tiling.Placement Tiling.Plane Unit := (-b + i.1, ())
    let j₀ : Tiling.Placement Tiling.Plane Unit := (-b + j.1, ())
    have hi₀ : i₀ ∈ K.toPolygonalRegion.placements S := by
      change -b + i.1 ∈ S
      change i.1 ∈ b +ᵥ S at hi
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hi
    have hj₀ : j₀ ∈ K.toPolygonalRegion.placements S := by
      change -b + j.1 ∈ S
      change j.1 ∈ b +ᵥ S at hj
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hj
    have hij₀ : i₀ ≠ j₀ := by
      intro heq
      apply hij
      apply Prod.ext
      · have := congrArg Prod.fst heq
        dsimp only [i₀, j₀] at this
        linear_combination this
      · exact Subsingleton.elim _ _
    have hd := h.2.1 hi₀ hj₀ hij₀
    have hd' := Tiling.aedisjoint_vadd (a + b) hd
    have hiTile :
        (a + b) +ᵥ ((-b + i.1) +ᵥ K.support) =
          i.1 +ᵥ (a +ᵥ K.support) := by
      rw [add_vadd_set, add_vadd_set]
      congr 1
      abel
    have hjTile :
        (a + b) +ᵥ ((-b + j.1) +ᵥ K.support) =
          j.1 +ᵥ (a +ᵥ K.support) := by
      rw [add_vadd_set, add_vadd_set]
      congr 1
      abel
    change MeasureTheory.AEDisjoint MeasureTheory.volume
      (i.1 +ᵥ (a +ᵥ K.support)) (j.1 +ᵥ (a +ᵥ K.support))
    rw [← hiTile, ← hjTile]
    exact hd'
  · have hpull :=
      (MeasureTheory.quasiMeasurePreserving_add_left MeasureTheory.volume (-(a + b))).ae h.2.2
    filter_upwards [hpull] with x hx
    have htarget : x ∈ (a + b) +ᵥ D ↔ -(a + b) + x ∈ D := by
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    have hunion :
        (∃ s : b +ᵥ S, x ∈ ((s : Tiling.Plane) +ᵥ (vaddRegion K a).openCarrier)) ↔
          ∃ s : S, -(a + b) + x ∈ ((s : Tiling.Plane) +ᵥ K.openCarrier) := by
      rw [vaddRegion_openCarrier]
      constructor
      · rintro ⟨s, hsx⟩
        let s₀ : S := ⟨-b + s.1, by
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using s.2⟩
        refine ⟨s₀, ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsx ⊢
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsx
        convert hsx using 1
        simp only [s₀, vadd_eq_add]
        abel
      · rintro ⟨s, hsx⟩
        let s' : b +ᵥ S := ⟨b + s.1, by
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
            neg_add_cancel_left] using s.2⟩
        refine ⟨s', ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsx ⊢
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        convert hsx using 1
        simp only [s', vadd_eq_add]
        abel
    exact htarget.trans (hx.trans hunion.symm)

private theorem tilesOn_vadd_iff
    (K : Tiling.AxisParallel.Region) (S D : Set Tiling.Plane)
    (a b : Tiling.Plane) :
    Tiling.AxisParallel.TilesOn K S D ↔
      Tiling.AxisParallel.TilesOn (vaddRegion K a) (b +ᵥ S) ((a + b) +ᵥ D) := by
  constructor
  · exact tilesOn_vadd K S D a b
  · intro h
    have hback := tilesOn_vadd (vaddRegion K a) (b +ᵥ S) ((a + b) +ᵥ D)
      (-a) (-b) h
    rw [vaddRegion_neg_vadd, vadd_neg_vadd_set, add_vadd_set,
      show -a + -b + (a + b) = 0 by abel, zero_vadd] at hback
    exact hback

private noncomputable def intrinsicVertexEnumeration (K : Tiling.AxisParallel.Region) :
    Fin K.vertexFinset.card ≃ ↥K.vertices :=
  K.vertexFinset.equivFin.symm.trans (Equiv.setCongr K.coe_vertexFinset)

private def cellPiece {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    (e : Fin R.pieces.card) : Set Tiling.Plane :=
  (R.pieces.equivFin.symm e).1

private theorem cellPiece_mem {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    (e : Fin R.pieces.card) : cellPiece R e ∈ R.pieces :=
  (R.pieces.equivFin.symm e).2

private structure IntrinsicRectangleData (K : Tiling.AxisParallel.Region)
    (r : Set Tiling.Plane) where
  x₀ : ℝ
  x₁ : ℝ
  y₀ : ℝ
  y₁ : ℝ
  x_lt : x₀ < x₁
  y_lt : y₀ < y₁
  box_eq : r = closedAxisBox x₀ x₁ y₀ y₁
  leftVertex : ↥K.vertices
  rightVertex : ↥K.vertices
  bottomVertex : ↥K.vertices
  topVertex : ↥K.vertices
  left_value : leftVertex.1.re = x₀
  right_value : rightVertex.1.re = x₁
  bottom_value : bottomVertex.1.im = y₀
  top_value : topVertex.1.im = y₁

private noncomputable def intrinsicRectangleData {K : Tiling.AxisParallel.Region}
    {r : Set Tiling.Plane} (h : IsIntrinsicGridRectangle K r) :
    IntrinsicRectangleData K r := by
  classical
  let x₀ := Classical.choose h
  let hx₀ := Classical.choose_spec h
  let x₁ := Classical.choose hx₀
  let hx₁ := Classical.choose_spec hx₀
  let y₀ := Classical.choose hx₁
  let hy₀ := Classical.choose_spec hx₁
  let y₁ := Classical.choose hy₀
  have hs := Classical.choose_spec hy₀
  let vl := Classical.choose hs.2.2.2.1
  have hvl := Classical.choose_spec hs.2.2.2.1
  let vr := Classical.choose hs.2.2.2.2.1
  have hvr := Classical.choose_spec hs.2.2.2.2.1
  let vb := Classical.choose hs.2.2.2.2.2.1
  have hvb := Classical.choose_spec hs.2.2.2.2.2.1
  let vt := Classical.choose hs.2.2.2.2.2.2
  have hvt := Classical.choose_spec hs.2.2.2.2.2.2
  exact ⟨x₀, x₁, y₀, y₁, hs.1, hs.2.1, hs.2.2.1, ⟨vl, hvl.1⟩, ⟨vr, hvr.1⟩,
    ⟨vb, hvb.1⟩, ⟨vt, hvt.1⟩, hvl.2, hvr.2, hvb.2, hvt.2⟩

private noncomputable def regionCodeOfRectangulation
    (K : Tiling.AxisParallel.Region) (R : Tiling.Rectangulation K.support)
    (hR : ∀ r ∈ R.pieces, IsIntrinsicGridRectangle K r)
    (origin : Fin K.vertexFinset.card) : RegionCode where
  vertexCount := K.vertexFinset.card
  cellCount := R.pieces.card
  originVertex := origin
  leftVertex := fun e => (intrinsicVertexEnumeration K).symm
    (intrinsicRectangleData (hR (cellPiece R e) (cellPiece_mem R e))).leftVertex
  rightVertex := fun e => (intrinsicVertexEnumeration K).symm
    (intrinsicRectangleData (hR (cellPiece R e) (cellPiece_mem R e))).rightVertex
  bottomVertex := fun e => (intrinsicVertexEnumeration K).symm
    (intrinsicRectangleData (hR (cellPiece R e) (cellPiece_mem R e))).bottomVertex
  topVertex := fun e => (intrinsicVertexEnumeration K).symm
    (intrinsicRectangleData (hR (cellPiece R e) (cellPiece_mem R e))).topVertex

private theorem interior_closedAxisBox'
    {a b c d : ℝ} (_hab : a < b) (_hcd : c < d) :
    interior (closedAxisBox a b c d) =
      {z : Tiling.Plane | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d} := by
  change interior (Icc a b ×ℂ Icc c d) = _
  rw [Complex.interior_reProdIm, interior_Icc, interior_Icc]
  ext z
  simp only [Complex.mem_reProdIm, Set.mem_ofPred_eq, Set.mem_Ioo]
  tauto

private theorem cellPiece_iUnion {s : Set Tiling.Plane} (R : Tiling.Rectangulation s) :
    (⋃ e, cellPiece R e) = ⋃ r ∈ (R.pieces : Set (Set Tiling.Plane)), r := by
  ext x
  constructor
  · rw [Set.mem_iUnion]
    rintro ⟨e, he⟩
    exact Set.mem_biUnion (cellPiece_mem R e) he
  · intro hx
    rw [Set.mem_iUnion]
    rw [Set.mem_iUnion] at hx
    obtain ⟨r, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨hr, hxr⟩ := hx
    let e := R.pieces.equivFin ⟨r, hr⟩
    refine ⟨e, ?_⟩
    change x ∈ (R.pieces.equivFin.symm e).1
    simpa only [e, Equiv.symm_apply_apply] using hxr

private theorem interior_cellPiece_iUnion_ae {s : Set Tiling.Plane}
    (R : Tiling.Rectangulation s) :
    (⋃ e, interior (cellPiece R e)) =ᵐ[MeasureTheory.volume] s := by
  have h₁ : (⋃ e, interior (cellPiece R e)) =ᵐ[MeasureTheory.volume]
      ⋃ e, cellPiece R e :=
    Filter.EventuallyEq.countable_iUnion fun e =>
      (R.isRectangle (cellPiece R e) (cellPiece_mem R e)).isPolygonal.interior_ae_eq
  have hset : (⋃ e, cellPiece R e) = s := by
    rw [cellPiece_iUnion, ← Set.sUnion_eq_biUnion, R.sUnion_eq]
  have h₂ : (⋃ e, cellPiece R e) =ᵐ[MeasureTheory.volume] s :=
    Filter.Eventually.of_forall fun x => congrFun hset x
  exact h₁.trans h₂

private theorem interior_cellPiece_pairwiseDisjoint {s : Set Tiling.Plane}
    (R : Tiling.Rectangulation s) :
    Set.PairwiseDisjoint Set.univ (fun e : Fin R.pieces.card => interior (cellPiece R e)) := by
  intro e _ f _ hef
  change Disjoint (interior (cellPiece R e)) (interior (cellPiece R f))
  rw [Set.disjoint_left]
  intro x hxe hxf
  have hpiece : cellPiece R e ≠ cellPiece R f := by
    intro h
    apply hef
    exact R.pieces.equivFin.symm.injective (Subtype.ext h)
  have hnull := (R.pairwiseAEDisjoint (cellPiece_mem R e) (cellPiece_mem R f) hpiece).mono
    interior_subset interior_subset
  have hpos := (isOpen_interior.inter isOpen_interior).measure_pos MeasureTheory.volume
    ⟨x, hxe, hxf⟩
  exact (ne_of_gt hpos) hnull

private def untranslateVertexEquiv (K : Tiling.AxisParallel.Region)
    (anchor : Tiling.Plane) : ↥(vaddRegion K (-anchor)).vertices ≃ ↥K.vertices where
  toFun v := ⟨v.1 + anchor, by
    have hv : v.1 ∈ (-anchor) +ᵥ K.vertices := by
      simpa only [vaddRegion_vertices] using v.2
    obtain ⟨w, hw, hvw⟩ := hv
    change -anchor + w = v.1 at hvw
    convert hw using 1
    linear_combination -hvw⟩
  invFun v := ⟨v.1 - anchor, by
    rw [vaddRegion_vertices]
    exact ⟨v.1, v.2, by simp only [vadd_eq_add]; abel⟩⟩
  left_inv := by
    intro v
    apply Subtype.ext
    simp only [add_sub_cancel_right]
  right_inv := by
    intro v
    apply Subtype.ext
    simp only [sub_add_cancel]

theorem existsRegionNormalization (K : Tiling.AxisParallel.Region) :
    Nonempty (RegionNormalization K) := by
  classical
  obtain ⟨anchor, hanchor, _⟩ := exists_intrinsicDiameterPair K
  let NK := vaddRegion K (-anchor)
  have hzero : 0 ∈ NK.vertices := by
    change 0 ∈ (vaddRegion K (-anchor)).vertices
    rw [vaddRegion_vertices]
    exact ⟨anchor, hanchor, by simp only [vadd_eq_add]; abel⟩
  obtain ⟨R, _hRpieces, hRintrinsic⟩ := exists_intrinsicGridRectangulation NK
  let V := intrinsicVertexEnumeration NK
  let origin : Fin NK.vertexFinset.card := V.symm ⟨0, hzero⟩
  let code := regionCodeOfRectangulation NK R hRintrinsic origin
  let vertex : Fin code.vertexCount → Tiling.Plane := fun i => (V i).1
  have hRnonempty : R.pieces.Nonempty := by
    by_contra h
    have hempty : R.pieces = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨x, hx⟩ := NK.nonempty
    have : x ∈ ⋃₀ (R.pieces : Set (Set Tiling.Plane)) := by
      rw [R.sUnion_eq]
      exact hx
    apply (Set.mem_empty_iff_false x).mp
    simpa only [hempty, Finset.coe_empty, Set.sUnion_empty] using this
  have hleft (e : Fin code.cellCount) :
      vertex (code.leftVertex e) =
        (intrinsicRectangleData
          (hRintrinsic (cellPiece R e) (cellPiece_mem R e))).leftVertex.1 := by
    simp only [vertex, code, regionCodeOfRectangulation, V, Equiv.apply_symm_apply]
  have hright (e : Fin code.cellCount) :
      vertex (code.rightVertex e) =
        (intrinsicRectangleData
          (hRintrinsic (cellPiece R e) (cellPiece_mem R e))).rightVertex.1 := by
    simp only [vertex, code, regionCodeOfRectangulation, V, Equiv.apply_symm_apply]
  have hbottom (e : Fin code.cellCount) :
      vertex (code.bottomVertex e) =
        (intrinsicRectangleData
          (hRintrinsic (cellPiece R e) (cellPiece_mem R e))).bottomVertex.1 := by
    simp only [vertex, code, regionCodeOfRectangulation, V, Equiv.apply_symm_apply]
  have htop (e : Fin code.cellCount) :
      vertex (code.topVertex e) =
        (intrinsicRectangleData
          (hRintrinsic (cellPiece R e) (cellPiece_mem R e))).topVertex.1 := by
    simp only [vertex, code, regionCodeOfRectangulation, V, Equiv.apply_symm_apply]
  have hopenCell (e : Fin code.cellCount) :
      {z : Tiling.Plane |
        (vertex (code.leftVertex e)).re < z.re ∧
        z.re < (vertex (code.rightVertex e)).re ∧
        (vertex (code.bottomVertex e)).im < z.im ∧
        z.im < (vertex (code.topVertex e)).im} =
        interior (cellPiece R e) := by
    let d := intrinsicRectangleData
      (hRintrinsic (cellPiece R e) (cellPiece_mem R e))
    calc
      _ = {z : Tiling.Plane |
          d.x₀ < z.re ∧ z.re < d.x₁ ∧ d.y₀ < z.im ∧ z.im < d.y₁} := by
        rw [hleft, hright, hbottom, htop, d.left_value, d.right_value,
          d.bottom_value, d.top_value]
      _ = interior (closedAxisBox d.x₀ d.x₁ d.y₀ d.y₁) :=
        (interior_closedAxisBox' d.x_lt d.y_lt).symm
      _ = interior (cellPiece R e) := congrArg interior d.box_eq.symm
  let normalized : Realization code :=
    { region := NK
      vertex := vertex
      vertex_injective := by
        intro i j hij
        exact V.injective (Subtype.ext hij)
      vertex_range := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          exact (V i).2
        · intro hx
          obtain ⟨i, hi⟩ := V.surjective ⟨x, hx⟩
          exact ⟨i, congrArg Subtype.val hi⟩
      wellFormed := by
        simp only [code, regionCodeOfRectangulation, RegionCode.wellFormed,
          decide_eq_true_eq]
        exact Finset.card_pos.mpr hRnonempty
      origin_eq_zero := by
        simp only [vertex, code, regionCodeOfRectangulation, origin, V,
          Equiv.apply_symm_apply]
      left_lt_right := by
        intro e
        rw [hleft, hright]
        let d := intrinsicRectangleData
          (hRintrinsic (cellPiece R e) (cellPiece_mem R e))
        rw [d.left_value, d.right_value]
        exact d.x_lt
      bottom_lt_top := by
        intro e
        rw [hbottom, htop]
        let d := intrinsicRectangleData
          (hRintrinsic (cellPiece R e) (cellPiece_mem R e))
        rw [d.bottom_value, d.top_value]
        exact d.y_lt
      cells_pairwiseDisjoint := by
        intro e _ f _ hef
        change Disjoint
          {z : Tiling.Plane |
            (vertex (code.leftVertex e)).re < z.re ∧
            z.re < (vertex (code.rightVertex e)).re ∧
            (vertex (code.bottomVertex e)).im < z.im ∧
            z.im < (vertex (code.topVertex e)).im}
          {z : Tiling.Plane |
            (vertex (code.leftVertex f)).re < z.re ∧
            z.re < (vertex (code.rightVertex f)).re ∧
            (vertex (code.bottomVertex f)).im < z.im ∧
            z.im < (vertex (code.topVertex f)).im}
        rw [hopenCell e, hopenCell f]
        exact interior_cellPiece_pairwiseDisjoint R (Set.mem_univ e) (Set.mem_univ f) hef
      presentation_correct := by
        change (⋃ e, {z : Tiling.Plane |
          (vertex (code.leftVertex e)).re < z.re ∧
          z.re < (vertex (code.rightVertex e)).re ∧
          (vertex (code.bottomVertex e)).im < z.im ∧
          z.im < (vertex (code.topVertex e)).im}) =ᵐ[MeasureTheory.volume]
            interior NK.support
        simp_rw [hopenCell]
        exact (interior_cellPiece_iUnion_ae R).trans NK.isPolygonal.interior_ae_eq.symm }
  let originalEquiv := V.trans (untranslateVertexEquiv K anchor)
  let originalVertex : Fin code.vertexCount → Tiling.Plane := fun i => (originalEquiv i).1
  have horiginal_formula (i : Fin code.vertexCount) : originalVertex i = vertex i + anchor := by
    rfl
  have hclosedCell (e : Fin code.cellCount) :
      realizationClosedCell normalized e = cellPiece R e := by
    let d := intrinsicRectangleData
      (hRintrinsic (cellPiece R e) (cellPiece_mem R e))
    change closedAxisBox
      (vertex (code.leftVertex e)).re (vertex (code.rightVertex e)).re
      (vertex (code.bottomVertex e)).im (vertex (code.topVertex e)).im = cellPiece R e
    rw [hleft, hright, hbottom, htop, d.left_value, d.right_value,
      d.bottom_value, d.top_value]
    exact d.box_eq.symm
  refine ⟨{
    anchor := anchor
    anchor_mem := hanchor
    code := code
    normalized := normalized
    originalVertex := originalVertex
    originalVertex_injective := by
      intro i j hij
      exact originalEquiv.injective (Subtype.ext hij)
    originalVertex_range := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (originalEquiv i).2
      · intro hx
        obtain ⟨i, hi⟩ := originalEquiv.surjective ⟨x, hx⟩
        exact ⟨i, congrArg Subtype.val hi⟩
    origin_originalVertex := by
      rw [horiginal_formula]
      have hv0 := normalized.origin_eq_zero
      change vertex code.originVertex = 0 at hv0
      rw [hv0, zero_add]
    normalizedVertex_formula := by
      intro i
      change vertex i = originalVertex i - anchor
      rw [horiginal_formula]
      exact (add_sub_cancel_right (vertex i) anchor).symm
    normalized_support := rfl
    normalized_openCarrier := by
      exact vaddRegion_openCarrier K (-anchor)
    normalized_vertices := by
      exact vaddRegion_vertices K (-anchor)
    intrinsicVertexEquiv := originalEquiv
    intrinsicVertexEquiv_value := by
      intro i
      rfl
    closedCell_intrinsic := by
      intro e
      rw [hclosedCell]
      exact hRintrinsic (cellPiece R e) (cellPiece_mem R e)
    closedCells_cover := by
      simp_rw [hclosedCell]
      change (⋃ e : Fin R.pieces.card, cellPiece R e) = NK.support
      rw [cellPiece_iUnion, ← Set.sUnion_eq_biUnion, R.sUnion_eq]
    closedCells_pairwiseIntersection_volume_zero := by
      intro e f hef
      rw [hclosedCell, hclosedCell]
      have hpiece : cellPiece R e ≠ cellPiece R f := by
        intro h
        apply hef
        exact R.pieces.equivFin.symm.injective (Subtype.ext h)
      exact R.pairwiseAEDisjoint (cellPiece_mem R e) (cellPiece_mem R f) hpiece
    tilesOn_translate := by
      intro S
      simpa only [NK, neg_add_cancel, zero_vadd] using
        (tilesOn_vadd_iff K S Set.univ (-anchor) anchor) }⟩

theorem evalCoeffAgainstRebaseCoeff {C : RegionCode}
    (vertex : Fin C.vertexCount → Tiling.Plane) (origin : Fin C.vertexCount)
    (s : CoordSort) (a : Coeff C) :
    evalCoeffAgainst vertex s (RuntimeRebase.rebaseCoeff origin a) =
      ∑ i, (a i : Real) * s.axis.coord (vertex i - vertex origin) := by
  classical
  simp only [evalCoeffAgainst, RuntimeRebase.rebaseCoeff, Coeff.sub, Coeff.single,
    Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  simp only [Int.cast_ite, Int.cast_sum, Int.cast_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  cases s <;>
    simp only [CoordSort.axis, Tiling.AxisParallel.Axis.coord, Complex.sub_re,
      Complex.sub_im, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

theorem normalizedEvalEqOriginalRebased {K : Tiling.AxisParallel.Region}
    (N : RegionNormalization K) (s : CoordSort) (a : Coeff N.code) :
    evalCoeff N.normalized s a =
      evalCoeffAgainst N.originalVertex s
        (RuntimeRebase.rebaseCoeff N.code.originVertex a) := by
  rw [evalCoeffAgainstRebaseCoeff]
  simp only [evalCoeff]
  apply Finset.sum_congr rfl
  intro i _
  rw [N.normalizedVertex_formula, N.origin_originalVertex]

theorem rebaseOracleCorrect {K : Tiling.AxisParallel.Region}
    (N : RegionNormalization K) (O : Oracle N.code)
    (hO : CorrectOriginalOracle N.originalVertex O) :
    ∃ CO : CorrectOracle N.code N.normalized,
      CO.toOracle = RuntimeRebase.rebaseOracle N.code.originVertex O := by
  let CO : CorrectOracle N.code N.normalized :=
    { answer := (RuntimeRebase.rebaseOracle N.code.originVertex O).answer
      correct := by
        intro q
        change O.answer (RuntimeRebase.rebaseQuery N.code.originVertex q) = true ↔ _
        rw [hO (RuntimeRebase.rebaseQuery N.code.originVertex q)]
        change evalCoeffAgainst N.originalVertex q.sort
            (RuntimeRebase.rebaseCoeff N.code.originVertex q.lhs) ≤
          evalCoeffAgainst N.originalVertex q.sort
            (RuntimeRebase.rebaseCoeff N.code.originVertex q.rhs) ↔ _
        rw [← normalizedEvalEqOriginalRebased, ← normalizedEvalEqOriginalRebased] }
  exact ⟨CO, rfl⟩

theorem tileableNormalizedIff {K : Tiling.AxisParallel.Region}
    (N : RegionNormalization K) :
    (∃ S : Set Tiling.Plane,
      Tiling.AxisParallel.TilesOn N.normalized.region S Set.univ) ↔
      ∃ S : Set Tiling.Plane, Tiling.AxisParallel.TilesOn K S Set.univ := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨(-N.anchor) +ᵥ S, ?_⟩
    apply (N.tilesOn_translate ((-N.anchor) +ᵥ S)).2
    convert hS using 1
    ext x
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    constructor <;> intro hx <;> convert hx using 1 <;> abel
  · rintro ⟨S, hS⟩
    exact ⟨N.anchor +ᵥ S, (N.tilesOn_translate S).1 hS⟩

theorem legacyAdapter_exists (E : EncodedAxisParallelRegion)
    (N : RegionNormalization E.region) : Nonempty (LegacyNormalizationAdapter E N) := by
  classical
  let vertexSetEquiv : ↥E.region.vertices ≃ ↥E.region.vertexFinset :=
    { toFun := fun v => ⟨v, by
          change v.1 ∈ (E.region.vertexFinset : Set Tiling.Plane)
          rw [E.region.coe_vertexFinset]
          exact v.2⟩
      invFun := fun v => ⟨v, by
          rw [← E.region.coe_vertexFinset]
          exact v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let vertexEquiv := N.intrinsicVertexEquiv.trans vertexSetEquiv
  exact ⟨{
    vertexEquiv := vertexEquiv
    intrinsic_compat := by intro i; rfl
    vertexEquiv_value := by intro i; exact N.intrinsicVertexEquiv_value i }⟩

private theorem eval_toLegacyCoeff {E : EncodedAxisParallelRegion}
    {N : RegionNormalization E.region} (A : LegacyNormalizationAdapter E N)
    (s : CoordSort) (a : Coeff N.code) :
    evalCoordExpr E s.axis (toLegacyCoeff A a) = evalCoeffAgainst N.originalVertex s a := by
  classical
  rw [evalCoordExpr, toLegacyCoeff]
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  change (∑ i : ↥E.region.vertexFinset,
    (a (A.vertexEquiv.symm i) : Real) * s.axis.coord (i : Tiling.Plane)) = _
  calc
    _ = ∑ i : Fin N.code.vertexCount,
        (a (A.vertexEquiv.symm (A.vertexEquiv i)) : Real) *
          s.axis.coord (A.vertexEquiv i : Tiling.Plane) :=
      (Equiv.sum_comp A.vertexEquiv _).symm
    _ = _ := by
      simp only [Equiv.symm_apply_apply, A.vertexEquiv_value, evalCoeffAgainst]

theorem legacyQuery_answer (E : EncodedAxisParallelRegion)
    (O : SelectedCoordinateOracles E) (N : RegionNormalization E.region)
    (A : LegacyNormalizationAdapter E N) :
    ∃ originalOracle : Oracle N.code,
      CorrectOriginalOracle N.originalVertex originalOracle ∧
      ∀ q, originalOracle.answer q = O.answer (toLegacyQuery A q) := by
  let originalOracle : Oracle N.code := ⟨fun q => O.answer (toLegacyQuery A q)⟩
  refine ⟨originalOracle, ?_, fun _ => rfl⟩
  rintro ⟨s, lhs, rhs⟩
  cases s
  · change O.horizontal.answer (toLegacyCoeff A lhs) (toLegacyCoeff A rhs) = true ↔ _
    rw [O.horizontal.correct]
    change evalCoordExpr E CoordSort.horizontal.axis (toLegacyCoeff A lhs) ≤
      evalCoordExpr E CoordSort.horizontal.axis (toLegacyCoeff A rhs) ↔ _
    rw [eval_toLegacyCoeff, eval_toLegacyCoeff]
  · change O.vertical.answer (toLegacyCoeff A lhs) (toLegacyCoeff A rhs) = true ↔ _
    rw [O.vertical.correct]
    change evalCoordExpr E CoordSort.vertical.axis (toLegacyCoeff A lhs) ≤
      evalCoordExpr E CoordSort.vertical.axis (toLegacyCoeff A rhs) ↔ _
    rw [eval_toLegacyCoeff, eval_toLegacyCoeff]

end Tiling.AxisParallel.Terminal.Executable.Semantics
