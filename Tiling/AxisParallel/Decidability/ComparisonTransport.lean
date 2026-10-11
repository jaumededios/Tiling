import Tiling.AxisParallel.Decidability.Comparisons
import Tiling.AxisParallel.Decidability.Certificates.PositiveCoding
import Mathlib.Computability.Partrec

/-!
# Transport packed vertex comparisons to corner queries

A packed vertex stores the two corner-list labels used for its coordinates.
After subtracting the origin vertex, a finite signed comparison is a corner
comparison with one additional origin term accounting for the translation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

open Tiling.Computability.Rational

namespace Tiling.AxisParallel.Decidability.QueryTransport

open Tiling.AxisParallel.Decidability.Queries

abbrev PointLabel := ℕ × ℕ
abbrev PackedComparison := Bool × List ℤ × List ℤ

def selectedLabel (axis : Fin 2) (p : PointLabel) : ℕ :=
  if axis = 0 then p.1 else p.2

def originCornerLabel (axis : Fin 2) (labels : List PointLabel) (origin : ℕ) : ℕ :=
  selectedLabel axis (labels.getD origin (0, 0))

def indexedCornerLabel (axis : Fin 2) (labels : List PointLabel) (origin i : ℕ) : ℕ :=
  selectedLabel axis (labels.getD i (labels.getD origin (0, 0)))

def transportedTermPieces (ctx : Fin 2 × (List PointLabel × ℕ))
    (term : SignedTerm) : List SignedTerm :=
  [(indexedCornerLabel ctx.1 ctx.2.1 ctx.2.2 term.1, term.2),
    (originCornerLabel ctx.1 ctx.2.1 ctx.2.2, -term.2)]

def normalizedVertices (corners : List Plane) (labels : List PointLabel)
    (origin : ℕ) : List Plane :=
  let originLabel := labels.getD origin (0, 0)
  labels.map fun p =>
    ⟨(corners.getD p.1 0).re - (corners.getD originLabel.1 0).re,
      (corners.getD p.2 0).im - (corners.getD originLabel.2 0).im⟩

def transportSignedTerms (axis : Fin 2) (labels : List PointLabel) (origin : ℕ)
    (terms : List SignedTerm) : List SignedTerm :=
  terms.flatMap (transportedTermPieces (axis, (labels, origin)))

def coefficientTerms (axis : Fin 2) (labels : List PointLabel) (origin : ℕ)
    (coefficients : List ℤ) : List SignedTerm :=
  let terms := (List.range coefficients.length).map fun i => (i, coefficients.getD i 0)
  transportSignedTerms axis labels origin terms

def compileTransportedComparison (axis : Fin 2) (labels : List PointLabel)
    (origin : ℕ) (terms : List SignedTerm) : Query :=
  compileSignedComparison axis (transportSignedTerms axis labels origin terms)

def compileCoefficientComparison (axis : Fin 2) (labels : List PointLabel)
    (origin : ℕ) (coefficients : List ℤ) : Query :=
  compileSignedComparison axis (coefficientTerms axis labels origin coefficients)

def indexedCoefficients (coefficients : List ℤ) : List SignedTerm :=
  (List.range coefficients.length).map fun i => (i, coefficients.getD i 0)

def comparisonTerms (lhs rhs : List ℤ) : List SignedTerm :=
  indexedCoefficients lhs ++
    (indexedCoefficients rhs).map fun (i, c) => (i, -c)

def compileNormalizedComparison (axis : Fin 2) (labels : List PointLabel)
    (origin : ℕ) (lhs rhs : List ℤ) : Query :=
  compileSignedComparison axis
    (transportSignedTerms axis labels origin (comparisonTerms lhs rhs))

def packedAxis (vertical : Bool) : Fin 2 := if vertical then 1 else 0

def compilePackedComparison (labels : List PointLabel) (origin : ℕ)
    (q : PackedComparison) : Query :=
  compileNormalizedComparison (packedAxis q.1) labels origin q.2.1 q.2.2

def linearCoordinateSum (V : List Plane) (axis : Fin 2) (coefficients : List ℤ) : ℝ :=
  ((indexedCoefficients coefficients).map fun (i, c) =>
    (c : ℝ) * coordinate axis (V.getD i 0)).sum

private theorem selectedLabel_primrec :
    Primrec (fun x : Fin 2 × PointLabel => selectedLabel x.1 x.2) := by
  have heq : Primrec (fun x : Fin 2 × PointLabel => decide (x.1 = 0)) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const (0 : Fin 2))).decide
  refine (Primrec.cond heq (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd)).of_eq ?_
  intro x
  rcases x with ⟨axis, p⟩
  fin_cases axis <;> simp [selectedLabel]

private theorem originCornerLabel_primrec :
    Primrec (fun x : Fin 2 × (List PointLabel × ℕ) =>
      originCornerLabel x.1 x.2.1 x.2.2) := by
  have hget : Primrec (fun x : Fin 2 × (List PointLabel × ℕ) =>
      x.2.1.getD x.2.2 (0, 0)) :=
    (Primrec.list_getD (0, 0)).comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact selectedLabel_primrec.comp (Primrec.pair Primrec.fst hget)

private theorem indexedCornerLabel_primrec :
    Primrec (fun x : (Fin 2 × (List PointLabel × ℕ)) × ℕ =>
      indexedCornerLabel x.1.1 x.1.2.1 x.1.2.2 x.2) := by
  have hbase : Primrec (fun x : (Fin 2 × (List PointLabel × ℕ)) × ℕ =>
      x.1.2.1.getD x.1.2.2 (0, 0)) :=
    (Primrec.list_getD (0, 0)).comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hget? : Primrec (fun x : (Fin 2 × (List PointLabel × ℕ)) × ℕ =>
      x.1.2.1[x.2]?) :=
    Primrec.list_getElem?.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      Primrec.snd
  have hget : Primrec (fun x : (Fin 2 × (List PointLabel × ℕ)) × ℕ =>
      (x.1.2.1[x.2]?).getD (x.1.2.1.getD x.1.2.2 (0, 0))) :=
    (Primrec.option_getD.comp hget? hbase)
  exact selectedLabel_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst) hget)

private theorem indexedCoefficients_primrec : Primrec indexedCoefficients := by
  have hrange : Primrec (fun coefficients : List ℤ => List.range coefficients.length) :=
    Primrec.list_range.comp (Primrec.list_length.comp Primrec.id)
  have hpair : Primrec₂ (fun coefficients : List ℤ => fun i : ℕ =>
      (i, coefficients.getD i 0)) :=
    (Primrec.pair Primrec.snd
      ((Primrec.list_getD 0).comp Primrec.fst Primrec.snd)).to₂
  exact (Primrec.list_map hrange hpair).of_eq (fun _ => rfl)

private theorem comparisonTerms_primrec :
    Primrec (fun x : List ℤ × List ℤ => comparisonTerms x.1 x.2) := by
  have hleft : Primrec (fun x : List ℤ × List ℤ => indexedCoefficients x.1) :=
    indexedCoefficients_primrec.comp Primrec.fst
  have hright : Primrec (fun x : List ℤ × List ℤ => indexedCoefficients x.2) :=
    indexedCoefficients_primrec.comp Primrec.snd
  have hneg : Primrec₂ (fun _ : List ℤ × List ℤ => fun t : SignedTerm => (t.1, -t.2)) :=
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (int_neg_primrec.comp (Primrec.snd.comp Primrec.snd))).to₂
  exact (Primrec.list_append.comp hleft (Primrec.list_map hright hneg)).of_eq
    (fun _ => rfl)

abbrev TransportInput := Fin 2 × (List PointLabel × (ℕ × List SignedTerm))

private theorem transportedTermPieces_primrec :
    Primrec₂ (fun ctx : Fin 2 × (List PointLabel × ℕ) =>
      fun term : SignedTerm => transportedTermPieces ctx term) := by
  have hindexed : Primrec (fun x : (Fin 2 × (List PointLabel × ℕ)) × ℕ =>
      indexedCornerLabel x.1.1 x.1.2.1 x.1.2.2 x.2) := indexedCornerLabel_primrec
  have horigin : Primrec (fun x : (Fin 2 × (List PointLabel × ℕ)) × SignedTerm =>
      originCornerLabel x.1.1 x.1.2.1 x.1.2.2) :=
    originCornerLabel_primrec.comp Primrec.fst
  have hindex : Primrec (fun x : (Fin 2 × (List PointLabel × ℕ)) × SignedTerm =>
      indexedCornerLabel x.1.1 x.1.2.1 x.1.2.2 x.2.1) :=
    hindexed.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  have hcoeff : Primrec (fun x : (Fin 2 × (List PointLabel × ℕ)) × SignedTerm => x.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hneg : Primrec (fun x : (Fin 2 × (List PointLabel × ℕ)) × SignedTerm => -x.2.2) :=
    int_neg_primrec.comp hcoeff
  refine (Primrec.list_cons.comp (Primrec.pair hindex hcoeff)
    (Primrec.list_cons.comp (Primrec.pair horigin hneg) (Primrec.const []))).to₂.of_eq ?_
  intro ctx term
  rfl

private theorem transportSignedTerms_primrec :
    Primrec (fun x : TransportInput =>
      transportSignedTerms x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have hcontext : Primrec (fun x : TransportInput => (x.1, (x.2.1, x.2.2.1))) :=
    Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hterms : Primrec (fun x : TransportInput => x.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hcallback : Primrec₂ (fun x : TransportInput => fun t : SignedTerm =>
      transportedTermPieces (x.1, (x.2.1, x.2.2.1)) t) := by
    refine (Primrec₂.comp transportedTermPieces_primrec (hcontext.comp Primrec.fst)
      Primrec.snd).to₂.of_eq ?_
    intro x t
    rfl
  exact (Primrec.list_flatMap hterms hcallback).of_eq (fun _ => rfl)

theorem compileNormalizedComparison_primrec :
    Primrec (fun x : Fin 2 × (List PointLabel × (ℕ × (List ℤ × List ℤ))) =>
      compileNormalizedComparison x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  have hterms : Primrec (fun x : Fin 2 × (List PointLabel × (ℕ × (List ℤ × List ℤ))) =>
      comparisonTerms x.2.2.2.1 x.2.2.2.2) :=
    comparisonTerms_primrec.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have htransport : Primrec (fun x : Fin 2 × (List PointLabel × (ℕ × (List ℤ × List ℤ))) =>
      transportSignedTerms x.1 x.2.1 x.2.2.1 (comparisonTerms x.2.2.2.1 x.2.2.2.2)) :=
    transportSignedTerms_primrec.comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hterms)))
  have hquery : Primrec (fun x : Fin 2 × (List PointLabel × (ℕ × (List ℤ × List ℤ))) =>
      compileSignedComparison x.1
        (transportSignedTerms x.1 x.2.1 x.2.2.1
          (comparisonTerms x.2.2.2.1 x.2.2.2.2))) :=
    compileSignedComparison_primrec.comp (Primrec.pair Primrec.fst htransport)
  exact hquery.of_eq (fun _ => rfl)

theorem compileNormalizedComparison_computable :
    Computable (fun x : Fin 2 × (List PointLabel × (ℕ × (List ℤ × List ℤ))) =>
      compileNormalizedComparison x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) :=
  compileNormalizedComparison_primrec.to_comp

theorem compilePackedComparison_primrec :
    Primrec (fun x : List PointLabel × (ℕ × PackedComparison) =>
      compilePackedComparison x.1 x.2.1 x.2.2) := by
  let Input := List PointLabel × (ℕ × PackedComparison)
  have hx2 : Primrec (fun x : Input => x.2) := Primrec.snd
  have hx22 : Primrec (fun x : Input => x.2.2) := Primrec.snd.comp hx2
  have hqvertical : Primrec (fun x : Input => x.2.2.1) := Primrec.fst.comp hx22
  have hqlists : Primrec (fun x : Input => x.2.2.2) := Primrec.snd.comp hx22
  have hleft : Primrec (fun x : Input => x.2.2.2.1) := Primrec.fst.comp hqlists
  have hright : Primrec (fun x : Input => x.2.2.2.2) := Primrec.snd.comp hqlists
  have horigin : Primrec (fun x : Input => x.2.1) := Primrec.fst.comp hx2
  have haxis : Primrec (fun x : Input => packedAxis x.2.2.1) := by
      refine (Primrec.cond hqvertical
        (Primrec.const (1 : Fin 2)) (Primrec.const (0 : Fin 2))).of_eq ?_
      intro x
      cases x.2.2.1 <;> rfl
  have hqueryInput : Primrec (fun x : Input =>
      (packedAxis x.2.2.1, (x.1, (x.2.1, (x.2.2.2.1, x.2.2.2.2))))) :=
    Primrec.pair haxis (Primrec.pair Primrec.fst (Primrec.pair horigin (Primrec.pair hleft hright)))
  exact (compileNormalizedComparison_primrec.comp hqueryInput).of_eq (fun _ => rfl)

theorem compilePackedComparison_computable :
    Computable (fun x : List PointLabel × (ℕ × PackedComparison) =>
      compilePackedComparison x.1 x.2.1 x.2.2) :=
  compilePackedComparison_primrec.to_comp

theorem coordinate_normalizedVertices (corners : List Plane) (labels : List PointLabel)
    (origin i : ℕ) (axis : Fin 2) :
    coordinate axis ((normalizedVertices corners labels origin).getD i 0) =
      coordinate axis
          (corners.getD
            (selectedLabel axis (labels.getD i (labels.getD origin (0, 0)))) 0) -
        coordinate axis
          (corners.getD (selectedLabel axis (labels.getD origin (0, 0))) 0) := by
  fin_cases axis <;> by_cases hi : i < labels.length <;>
    simp [normalizedVertices, selectedLabel, coordinate, hi]

theorem signedWeightSum_normalizedVertices (corners : List Plane)
    (labels : List PointLabel) (origin : ℕ) (axis : Fin 2) (terms : List SignedTerm) :
    signedWeightSum (normalizedVertices corners labels origin) axis terms =
      signedWeightSum corners axis (transportSignedTerms axis labels origin terms) := by
  unfold signedWeightSum transportSignedTerms
  induction terms with
  | nil => simp [normalizedVertices]
  | cons term terms ih =>
      rcases term with ⟨i, c⟩
      simp only [List.flatMap_cons, List.map_append, List.sum_append]
      simp only [List.map_cons, List.sum_cons]
      rw [coordinate_normalizedVertices]
      rw [ih]
      simp [transportedTermPieces, indexedCornerLabel, originCornerLabel]
      ring

theorem signedWeightSum_indexedCoefficients (V : List Plane) (axis : Fin 2)
    (coefficients : List ℤ) :
    signedWeightSum V axis (indexedCoefficients coefficients) =
      linearCoordinateSum V axis coefficients := by
  rfl

private theorem sum_map_neg {α : Type*} (f : α → ℝ) (xs : List α) :
    (xs.map fun x => -f x).sum = -(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring

theorem signedWeightSum_comparisonTerms (V : List Plane) (axis : Fin 2)
    (lhs rhs : List ℤ) :
    signedWeightSum V axis
        (comparisonTerms lhs rhs) =
      linearCoordinateSum V axis lhs - linearCoordinateSum V axis rhs := by
  unfold signedWeightSum linearCoordinateSum comparisonTerms
  simp only [List.map_append, List.sum_append, List.map_map]
  let f : SignedTerm → ℝ := fun x => (x.2 : ℝ) * coordinate axis (V.getD x.1 0)
  let g : SignedTerm → SignedTerm := fun x => (x.1, -x.2)
  have hneg :
      ((indexedCoefficients rhs).map (f ∘ g)).sum =
        -((indexedCoefficients rhs).map f).sum := by
    calc
      _ = ((indexedCoefficients rhs).map fun x => -f x).sum := by
        congr 1
        apply List.map_congr_left
        intro x hx
        dsimp [f, g]
        simp [Int.cast_neg, neg_mul]
      _ = _ := sum_map_neg f _
  change ((indexedCoefficients lhs).map f).sum +
      ((indexedCoefficients rhs).map (f ∘ g)).sum = _
  rw [hneg]
  ring

theorem compileNormalizedComparison_correct {corners : List Plane}
    {answer : Query → Bool} (hanswer : CorrectOracle corners answer)
    (axis : Fin 2) (labels : List PointLabel) (origin : ℕ) (lhs rhs : List ℤ) :
    answer (compileNormalizedComparison axis labels origin lhs rhs) = true ↔
      linearCoordinateSum (normalizedVertices corners labels origin) axis lhs -
          linearCoordinateSum (normalizedVertices corners labels origin) axis rhs ≤ 0 := by
  unfold compileNormalizedComparison
  rw [compileSignedComparison_correct hanswer]
  rw [← signedWeightSum_normalizedVertices]
  exact signedWeightSum_comparisonTerms
    (normalizedVertices corners labels origin) axis lhs rhs |>.symm ▸ Iff.rfl

theorem compilePackedComparison_correct {corners : List Plane}
    {answer : Query → Bool} (hanswer : CorrectOracle corners answer)
    (labels : List PointLabel) (origin : ℕ) (q : PackedComparison) :
    answer (compilePackedComparison labels origin q) = true ↔
      linearCoordinateSum (normalizedVertices corners labels origin) (packedAxis q.1) q.2.1 -
          linearCoordinateSum (normalizedVertices corners labels origin)
            (packedAxis q.1) q.2.2 ≤ 0 := by
  exact compileNormalizedComparison_correct hanswer (packedAxis q.1) labels origin
    q.2.1 q.2.2

end Tiling.AxisParallel.Decidability.QueryTransport
