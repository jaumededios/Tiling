/-!
# Finite oracle-query programs

This definition-only runtime core contains the generic finite oracle-query tree and its evaluator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tiling.AxisParallel.Terminal

/-- A terminating finite query tree over an abstract Boolean oracle. -/
inductive OracleProgram (Q : Type) (alpha : Type)
  | pure : alpha → OracleProgram Q alpha
  | query : Q → (Bool → OracleProgram Q alpha) → OracleProgram Q alpha

/-- Evaluate a finite oracle-query tree. -/
def OracleProgram.evaluate {Q alpha : Type} (answer : Q → Bool) :
    OracleProgram Q alpha → alpha
  | .pure a => a
  | .query q next => evaluate answer (next (answer q))

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal.OracleProgram

def bind {Q α β : Type} :
    OracleProgram Q α → (α → OracleProgram Q β) → OracleProgram Q β
  | .pure a, k => k a
  | .query q next, k => .query q (fun b => bind (next b) k)

def map {Q α β : Type} (f : α → β) (p : OracleProgram Q α) :
    OracleProgram Q β :=
  bind p (fun a => .pure (f a))

def mapQuery {Q Q' α : Type} (f : Q → Q') :
    OracleProgram Q α → OracleProgram Q' α
  | .pure a => .pure a
  | .query q next => .query (f q) (fun b => mapQuery f (next b))

theorem evaluate_bind {Q α β : Type} (answer : Q → Bool)
    (p : OracleProgram Q α) (k : α → OracleProgram Q β) :
    OracleProgram.evaluate answer (bind p k) =
      OracleProgram.evaluate answer
        (k (OracleProgram.evaluate answer p)) := by
  induction p with
  | pure a => rfl
  | query q next ih =>
      simpa only [bind, OracleProgram.evaluate] using ih (answer q)

theorem evaluate_map {Q α β : Type} (answer : Q → Bool)
    (f : α → β) (p : OracleProgram Q α) :
    OracleProgram.evaluate answer (map f p) =
      f (OracleProgram.evaluate answer p) := by
  simpa only [map, OracleProgram.evaluate] using
    evaluate_bind answer p (fun a => .pure (f a))

theorem evaluate_mapQuery {Q Q' α : Type} (answer : Q' → Bool)
    (f : Q → Q') (p : OracleProgram Q α) :
    OracleProgram.evaluate answer (mapQuery f p) =
      OracleProgram.evaluate (fun q => answer (f q)) p := by
  induction p with
  | pure a => rfl
  | query q next ih =>
      simpa only [mapQuery, OracleProgram.evaluate] using ih (answer (f q))

end Tiling.AxisParallel.Terminal.OracleProgram
