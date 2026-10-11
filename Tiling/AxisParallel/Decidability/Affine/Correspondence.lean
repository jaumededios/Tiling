import Tiling.AxisParallel.Decidability.Affine.Compiler

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.Affine.Native

open Tiling.AxisParallel.Terminal.Executable

private def dummy : SortedAtom := (false, false, [], [])

def compilationTrace {C : RegionCode} : {h v : ℕ} → Formula C h v → List DNF
  | _, _, .conjunction p q => compilationTrace p ++ compilationTrace q ++
      [packDNF (AffineCompiler.compile (.conjunction p q))]
  | _, _, .disjunction p q => compilationTrace p ++ compilationTrace q ++
      [packDNF (AffineCompiler.compile (.disjunction p q))]
  | _, _, .negation p => compilationTrace p ++ [packDNF (AffineCompiler.compile (.negation p))]
  | _, _, .existsHorizontal p => compilationTrace p ++
      [packDNF (AffineCompiler.compile (.existsHorizontal p))]
  | _, _, .existsVertical p => compilationTrace p ++
      [packDNF (AffineCompiler.compile (.existsVertical p))]
  | _, _, f => [packDNF (AffineCompiler.compile f)]

/-- Pack native formulas into postorder instructions with absolute child indices.
The offset is the length of the already compiled instruction prefix. -/
def packFormulaAt {C : RegionCode} : {h v : ℕ} → ℕ → Formula C h v → Code
  | _, _, _, .truth => [(0, dummy, 0, 0)]
  | _, _, _, .falsity => [(1, dummy, 0, 0)]
  | _, _, _, .horizontalLe a b => [(2, (false, packAtom ⟨.weak,
      (AffineCompiler.LinearExpr.ofAffine a).sub (AffineCompiler.LinearExpr.ofAffine b)⟩), 0, 0)]
  | _, _, _, .horizontalLt a b => [(2, (false, packAtom ⟨.strict,
      (AffineCompiler.LinearExpr.ofAffine a).sub (AffineCompiler.LinearExpr.ofAffine b)⟩), 0, 0)]
  | _, _, _, .verticalLe a b => [(2, (true, packAtom ⟨.weak,
      (AffineCompiler.LinearExpr.ofAffine a).sub (AffineCompiler.LinearExpr.ofAffine b)⟩), 0, 0)]
  | _, _, _, .verticalLt a b => [(2, (true, packAtom ⟨.strict,
      (AffineCompiler.LinearExpr.ofAffine a).sub (AffineCompiler.LinearExpr.ofAffine b)⟩), 0, 0)]
  | _, _, offset, .conjunction p q =>
      packFormulaAt offset p ++ packFormulaAt (offset + (compilationTrace p).length) q ++
        [(3, dummy, offset + (compilationTrace p).length - 1,
          offset + (compilationTrace p).length + (compilationTrace q).length - 1)]
  | _, _, offset, .disjunction p q =>
      packFormulaAt offset p ++ packFormulaAt (offset + (compilationTrace p).length) q ++
        [(4, dummy, offset + (compilationTrace p).length - 1,
          offset + (compilationTrace p).length + (compilationTrace q).length - 1)]
  | _, _, offset, .negation p =>
      packFormulaAt offset p ++ [(5, dummy, offset + (compilationTrace p).length - 1, 0)]
  | _, _, offset, .existsHorizontal p =>
      packFormulaAt offset p ++ [(6, dummy, offset + (compilationTrace p).length - 1, 0)]
  | _, _, offset, .existsVertical p =>
      packFormulaAt offset p ++ [(7, dummy, offset + (compilationTrace p).length - 1, 0)]

def packFormula {C : RegionCode} {h v : ℕ} (f : Formula C h v) : Code := packFormulaAt 0 f

private theorem compilationTrace_ends {C : RegionCode} {h v : ℕ} (f : Formula C h v) :
    ∃ initial, compilationTrace f = initial ++ [packDNF (AffineCompiler.compile f)] := by
  cases f <;> first | exact ⟨[], rfl⟩ | exact ⟨_, rfl⟩

/-- Every encoded formula has at least its root instruction. -/
theorem compilationTrace_length_pos {C : RegionCode} {h v : ℕ} (f : Formula C h v) :
    0 < (compilationTrace f).length := by
  obtain ⟨initial, h⟩ := compilationTrace_ends f
  rw [h]
  simp

/-- Offset changes do not change the number of packed instructions. -/
theorem packFormulaAt_length {C : RegionCode} {h v : ℕ} (f : Formula C h v) (offset : ℕ) :
    (packFormulaAt offset f).length = (compilationTrace f).length := by
  induction f generalizing offset <;> simp [packFormulaAt, compilationTrace, *]

@[simp] theorem packFormula_length {C : RegionCode} {h v : ℕ} (f : Formula C h v) :
    (packFormula f).length = (compilationTrace f).length := packFormulaAt_length f 0

private theorem getD_middle (initial ending : List DNF) (value : DNF) :
    (initial ++ [value] ++ ending).getD initial.length [] = value := by
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by rfl)]
  simp

private theorem compilationTrace_getD {C : RegionCode} {h v : ℕ} (f : Formula C h v)
    (initial ending : List DNF) :
    (initial ++ compilationTrace f ++ ending).getD
      (initial.length + (compilationTrace f).length - 1) [] =
        packDNF (AffineCompiler.compile f) := by
  obtain ⟨initial', htrace⟩ := compilationTrace_ends f
  rw [htrace]
  have hindex : initial.length + (initial' ++ [packDNF (AffineCompiler.compile f)]).length - 1 =
      (initial ++ initial').length := by simp
  rw [hindex]
  simpa only [List.append_assoc] using
    getD_middle (initial ++ initial') ending (packDNF (AffineCompiler.compile f))

private theorem compileInto_append (initial : List DNF) (left right : Code) :
    compileInto initial (left ++ right) = compileInto (compileInto initial left) right := by
  exact List.foldl_append

/-- Every intermediate packed result agrees with native quantifier elimination. -/
theorem compileInto_packFormula {C : RegionCode} {h v : ℕ} (f : Formula C h v)
    (initial : List DNF) :
    compileInto initial (packFormulaAt initial.length f) = initial ++ compilationTrace f := by
  induction f generalizing initial with
  | truth => simp [packFormulaAt, compileInto, compilationTrace, instruction, packDNF,
      AffineCompiler.compile, AffineCompiler.dnfTrue]
  | falsity => simp [packFormulaAt, compileInto, compilationTrace, instruction, packDNF,
      AffineCompiler.compile, AffineCompiler.dnfFalse]
  | horizontalLe a b => simp [packFormulaAt, compileInto, compilationTrace, instruction,
      packDNF, packSorted, AffineCompiler.compile, AffineCompiler.dnfAtom]
  | horizontalLt a b => simp [packFormulaAt, compileInto, compilationTrace, instruction,
      packDNF, packSorted, AffineCompiler.compile, AffineCompiler.dnfAtom]
  | verticalLe a b => simp [packFormulaAt, compileInto, compilationTrace, instruction,
      packDNF, packSorted, AffineCompiler.compile, AffineCompiler.dnfAtom]
  | verticalLt a b => simp [packFormulaAt, compileInto, compilationTrace, instruction,
      packDNF, packSorted, AffineCompiler.compile, AffineCompiler.dnfAtom]
  | conjunction p q ihp ihq =>
    rw [packFormulaAt, compileInto_append, compileInto_append, ihp]
    rw [show initial.length + (compilationTrace p).length =
      (initial ++ compilationTrace p).length by simp, ihq]
    simp only [compileInto, List.foldl_cons, List.foldl_nil, instruction,
      show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide,
      show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
    simp only [List.length_append]
    rw [compilationTrace_getD p initial (compilationTrace q)]
    have hright := compilationTrace_getD q (initial ++ compilationTrace p) []
    simp only [List.length_append, List.append_nil] at hright
    rw [hright]
    simp only [packDNF_and, compilationTrace, AffineCompiler.compile, List.append_assoc]
  | disjunction p q ihp ihq =>
    rw [packFormulaAt, compileInto_append, compileInto_append, ihp]
    rw [show initial.length + (compilationTrace p).length =
      (initial ++ compilationTrace p).length by simp, ihq]
    simp only [compileInto, List.foldl_cons, List.foldl_nil, instruction,
      show (4 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 1 by decide,
      show (4 : ℕ) ≠ 2 by decide, show (4 : ℕ) ≠ 3 by decide, ↓reduceIte]
    simp only [List.length_append]
    rw [compilationTrace_getD p initial (compilationTrace q)]
    have hright := compilationTrace_getD q (initial ++ compilationTrace p) []
    simp only [List.length_append, List.append_nil] at hright
    rw [hright]
    simp only [packDNF_or, compilationTrace, AffineCompiler.compile, List.append_assoc]
  | negation p ih =>
    rw [packFormulaAt, compileInto_append, ih]
    simp only [compileInto, List.foldl_cons, List.foldl_nil, instruction,
      show (5 : ℕ) ≠ 0 by decide, show (5 : ℕ) ≠ 1 by decide,
      show (5 : ℕ) ≠ 2 by decide, show (5 : ℕ) ≠ 3 by decide,
      show (5 : ℕ) ≠ 4 by decide, ↓reduceIte]
    rw [show (initial ++ compilationTrace p).getD
        (initial.length + (compilationTrace p).length - 1) [] =
      packDNF (AffineCompiler.compile p) by
        simpa using compilationTrace_getD p initial []]
    simp only [pack_negateDNF, compilationTrace, AffineCompiler.compile, List.append_assoc]
  | existsHorizontal p ih =>
    rw [packFormulaAt, compileInto_append, ih]
    simp only [compileInto, List.foldl_cons, List.foldl_nil, instruction,
      show (6 : ℕ) ≠ 0 by decide, show (6 : ℕ) ≠ 1 by decide,
      show (6 : ℕ) ≠ 2 by decide, show (6 : ℕ) ≠ 3 by decide,
      show (6 : ℕ) ≠ 4 by decide, show (6 : ℕ) ≠ 5 by decide, ↓reduceIte]
    rw [show (initial ++ compilationTrace p).getD
        (initial.length + (compilationTrace p).length - 1) [] =
      packDNF (AffineCompiler.compile p) by
        simpa using compilationTrace_getD p initial []]
    simp only [pack_eliminate_horizontal, compilationTrace, AffineCompiler.compile,
      List.append_assoc]
  | existsVertical p ih =>
    rw [packFormulaAt, compileInto_append, ih]
    simp only [compileInto, List.foldl_cons, List.foldl_nil, instruction,
      show (7 : ℕ) ≠ 0 by decide, show (7 : ℕ) ≠ 1 by decide,
      show (7 : ℕ) ≠ 2 by decide, show (7 : ℕ) ≠ 3 by decide,
      show (7 : ℕ) ≠ 4 by decide, show (7 : ℕ) ≠ 5 by decide,
      show (7 : ℕ) ≠ 6 by decide, ↓reduceIte]
    rw [show (initial ++ compilationTrace p).getD
        (initial.length + (compilationTrace p).length - 1) [] =
      packDNF (AffineCompiler.compile p) by
        simpa using compilationTrace_getD p initial []]
    simp only [pack_eliminate_vertical, compilationTrace, AffineCompiler.compile,
      List.append_assoc]

/-- The packed compiler implements native finite Fourier–Motzkin compilation. -/
theorem compile_packFormula {C : RegionCode} {h v : ℕ} (f : Formula C h v) :
    compile (packFormula f) = packDNF (AffineCompiler.compile f) := by
  have h := compileInto_packFormula f []
  obtain ⟨initial, htrace⟩ := compilationTrace_ends f
  simp only [List.length_nil, List.nil_append] at h
  rw [compile, packFormula, h, htrace]
  simp

end Tiling.AxisParallel.Decidability.Affine.Native
