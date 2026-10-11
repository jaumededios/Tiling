import Tiling.AxisParallel.Core
import Tiling.AxisParallel.Terminal.ExecutableInput

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Semantic interpretation of executable input

Proof-layer realizations and semantics for the finite runtime syntax. This owner introduces no
legacy certificate adapters or compiler definitions.
-/

open scoped BigOperators
open Set

namespace Tiling.AxisParallel.Terminal.Executable

/-- A proof-only realization of runtime identifiers by the vertices and cells of a region. -/
structure Realization (C : RegionCode) where
  region : Tiling.AxisParallel.Region
  vertex : Fin C.vertexCount → Tiling.Plane
  vertex_injective : Function.Injective vertex
  vertex_range : Set.range vertex = region.vertices
  wellFormed : C.wellFormed = true
  origin_eq_zero : vertex C.originVertex = 0
  left_lt_right : ∀ e,
    (vertex (C.leftVertex e)).re < (vertex (C.rightVertex e)).re
  bottom_lt_top : ∀ e,
    (vertex (C.bottomVertex e)).im < (vertex (C.topVertex e)).im
  cells_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ (fun e =>
    {z : Tiling.Plane |
      (vertex (C.leftVertex e)).re < z.re ∧
      z.re < (vertex (C.rightVertex e)).re ∧
      (vertex (C.bottomVertex e)).im < z.im ∧
      z.im < (vertex (C.topVertex e)).im})
  presentation_correct :
    (⋃ e, {z : Tiling.Plane |
      (vertex (C.leftVertex e)).re < z.re ∧
      z.re < (vertex (C.rightVertex e)).re ∧
      (vertex (C.bottomVertex e)).im < z.im ∧
      z.im < (vertex (C.topVertex e)).im}) =ᵐ[MeasureTheory.volume]
      region.openCarrier

def CoordSort.axis : CoordSort → Tiling.AxisParallel.Axis
  | .horizontal => .horizontal
  | .vertical => .vertical

def evalCoeff {C : RegionCode} (R : Realization C) (s : CoordSort) (a : Coeff C) : Real :=
  ∑ i, (a i : Real) * s.axis.coord (R.vertex i)

def evalAffine {C : RegionCode} (R : Realization C) (s : CoordSort)
    {n : Nat} (A : AffineExpr C n) (x : Fin n → Real) : Real :=
  (∑ i, (A.variableCoefficient i : Real) * x i) + evalCoeff R s A.inputConstant

/-- Proof-carrying correctness for a runtime oracle. -/
structure CorrectOracle (C : RegionCode) (R : Realization C) extends Oracle C where
  correct : ∀ q, answer q = true ↔ evalCoeff R q.sort q.lhs ≤ evalCoeff R q.sort q.rhs

def Formula.Holds {C : RegionCode} (R : Realization C) :
    {h v : Nat} → Formula C h v → (Fin h → Real) → (Fin v → Real) → Prop
  | _, _, .truth, _, _ => True
  | _, _, .falsity, _, _ => False
  | _, _, .horizontalLe A B, x, _ =>
      evalAffine R .horizontal A x ≤ evalAffine R .horizontal B x
  | _, _, .horizontalLt A B, x, _ =>
      evalAffine R .horizontal A x < evalAffine R .horizontal B x
  | _, _, .verticalLe A B, _, y =>
      evalAffine R .vertical A y ≤ evalAffine R .vertical B y
  | _, _, .verticalLt A B, _, y =>
      evalAffine R .vertical A y < evalAffine R .vertical B y
  | _, _, .conjunction F G, x, y => F.Holds R x y ∧ G.Holds R x y
  | _, _, .disjunction F G, x, y => F.Holds R x y ∨ G.Holds R x y
  | _, _, .negation F, x, y => ¬F.Holds R x y
  | _, _, .existsHorizontal F, x, y => ∃ t, F.Holds R (Fin.cons t x) y
  | _, _, .existsVertical F, x, y => ∃ t, F.Holds R x (Fin.cons t y)

end Tiling.AxisParallel.Terminal.Executable
