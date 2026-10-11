import Tiling.AxisParallel.Decidability.RectangleInput.Oracle
import Tiling.AxisParallel.Decidability.Certificates.FormulaExpressions
import Tiling.AxisParallel.Decidability.Affine.Stages

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.OracleDecision

open RectangleInput CertificateFormulas

/-- Normalize arbitrary packed selectors exactly as the production region decoder does. -/
def normalizeCell (n : ℕ) (c : RectangleInput.Cell) : RectangleInput.Cell :=
  ((c.1.1 % n, c.1.2 % n), (c.2.1 % n, c.2.2 % n))

def normalizedRegion (P : PackedRegion) : RegionInput :=
  (P.1.length, P.2.map (normalizeCell P.1.length))

/-- The finite formula compiler's input, computed from the first query table. -/
def formulaRegion (input : TableInput) : RegionInput := normalizedRegion (packedRegion input)

/-- Transport signed comparisons from intrinsic vertices to labelled rectangle corners. -/
def transport (input : TableInput) (q : Affine.PackedQuery) : Query :=
  QueryTransport.compilePackedComparison (vertexLabels input) 0 q

private theorem normalizeCell_primrec : Primrec₂ normalizeCell :=
  ((Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) Primrec.fst).pair
    (Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) Primrec.fst)).pair
  ((Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst).pair
    (Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst))

theorem normalizedRegion_primrec : Primrec normalizedRegion :=
  (Primrec.list_length.comp Primrec.fst).pair
    (Primrec.list_map Primrec.snd
      (normalizeCell_primrec.comp
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂)

theorem formulaRegion_computable : Computable formulaRegion :=
  (normalizedRegion_primrec.comp packedRegion_primrec).to_comp

theorem transport_computable : Computable₂ transport := by
  have hlabels : Computable (fun x : TableInput × Affine.PackedQuery =>
      vertexLabels x.1) := vertexLabels_primrec.to_comp.comp Computable.fst
  exact (QueryTransport.compilePackedComparison_computable.comp
    (hlabels.pair ((Computable.const 0).pair Computable.snd))).of_eq (fun _ => rfl)

/-- Computed finite syntax agrees with the production decoder on every nonempty label list. -/
theorem normalizedRegion_eq_encodeRegion (P : PackedRegion) (hP : 0 < P.1.length) :
    normalizedRegion P = CertificateFormulas.Native.encodeRegion (regionCode P hP) := by
  change (P.1.length, P.2.map (normalizeCell P.1.length)) =
    (P.1.length, List.ofFn (fun i : Fin P.2.length =>
      normalizeCell P.1.length (P.2.getD i (0, 0))))
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_ofFn]
    rw [List.getD_eq_getElem P.2 (0, 0) (by simpa only [List.length_map] using hi)]

/-- The finite frontend's production and computational region presentations coincide. -/
theorem formulaRegion_eq_encodeRegion (input : TableInput)
    (hinput : 0 < (vertexLabels input).length) :
    formulaRegion input =
      CertificateFormulas.Native.encodeRegion (inputCode input hinput) :=
  normalizedRegion_eq_encodeRegion (packedRegion input) hinput

/-- Packed native queries undergo exactly the verified corner-query transport. -/
theorem transport_packQuery (input : TableInput)
    (hinput : 0 < (vertexLabels input).length)
    (q : Tiling.AxisParallel.Terminal.Executable.Query (inputCode input hinput)) :
    transport input (Affine.Native.packQuery q) = nativeQueryToCorner q := by
  cases q with
  | mk sort lhs rhs => cases sort <;> rfl

/-- A compiled native certificate formula is true exactly under its production semantics. -/
theorem certificateTree_correct {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} {answer : Query → Bool}
    (hR : RectanglePresentation R Ω) (htable : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length)
    (hanswer : CorrectOracle (cornerList R) answer)
    (f : Tiling.AxisParallel.Terminal.Executable.Formula (inputCode (R.length, history) hinput) 0 0)
    (result b : Bool) :
    OracleReplay.StageAnswer answer
      (Affine.Trees.certificateTree (transport (R.length, history)) result
        (Affine.Native.packFormula f)) b ↔
      Tiling.AxisParallel.Terminal.Executable.Formula.Holds (realization hR htable hinput)
        f Fin.elim0 Fin.elim0 ∧ result = b := by
  apply Affine.Trees.certificateTree_native_correct
    (realization hR htable hinput) (oracle hR htable hinput hanswer)
  intro q
  rw [transport_packQuery]
  rfl

end Tiling.AxisParallel.Decidability.OracleDecision
