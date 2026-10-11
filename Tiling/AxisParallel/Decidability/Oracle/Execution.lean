import Tiling.AxisParallel.Decidability.Input

/-! Internal bounded execution used to prove termination of certificate search. -/

set_option autoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability

abbrev OracleCode := ℕ → List Bool → Bool ⊕ Query

def run (step : List Bool → Bool ⊕ Query) (answer : Query → Bool) :
    ℕ → List Bool → Option Bool
  | 0, _ => none
  | n + 1, history =>
    match step history with
    | .inl b => some b
    | .inr q => run step answer n (history ++ [answer q])

end Tiling.AxisParallel.Decidability
