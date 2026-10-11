import Tiling.AxisParallel.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.RationalMesh

abbrev ZPlane := TranslationalTilings.Plane

/-- Historical mesh embedding. Division is performed in `ℚ` before the
coordinates are cast to `ℝ`; this body is intentionally frozen. -/
noncomputable def rationalScale (d : ℕ) : ZPlane → Tiling.Plane :=
  fun z ↦ Complex.mk ((((z 0 : ℤ) : ℚ) / (d : ℚ)) : ℝ)
    ((((z 1 : ℤ) : ℚ) / (d : ℚ)) : ℝ)

def rationalMesh (d : ℕ) : Set Tiling.Plane :=
  Set.range (rationalScale d)

def OnRationalMesh (d : ℕ) (S : Set Tiling.Plane) : Prop :=
  S ⊆ rationalMesh d

/-- Open mesh cell based at an integer lattice point. -/
def meshCell (d : ℕ) (z : ZPlane) : Set Tiling.Plane :=
  {x | (rationalScale d z).re < x.re ∧
    x.re < (rationalScale d z).re + (1 / d : ℝ) ∧
    (rationalScale d z).im < x.im ∧
    x.im < (rationalScale d z).im + (1 / d : ℝ)}

def rasterCells (d : ℕ) (E : Set Tiling.Plane) : Set ZPlane :=
  {z | meshCell d z ⊆ E}

def regularizedCellUnion (d : ℕ) (A : Set ZPlane) : Set Tiling.Plane :=
  interior (closure (⋃ z : A, meshCell d z))

/-- Union of all vertical and horizontal mesh lines. -/
def meshLines (d : ℕ) : Set Tiling.Plane :=
  {x | (∃ n : ℤ, x.re = (((n : ℚ) / (d : ℚ)) : ℝ)) ∨
    (∃ n : ℤ, x.im = (((n : ℚ) / (d : ℚ)) : ℝ))}

end Tiling.AxisParallel.RationalMesh
