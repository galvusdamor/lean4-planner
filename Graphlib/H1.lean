import Validator.PlanningTask.Core
import Validator.PlanningTask.Basic
import Graphlib.NatGraph
import Graphlib.Planning
import Graphlib.Heuristics
import Graphlib.CriticalPath
import Graphlib.PerfectHeuristic

import Graphlib.temp

namespace Validator



-- termination by the fact that h_1_step is monotone in its bef argument and that WF.lean contains well-foundedness results for Vectors (if needed)
def h_1_iter_fix (n : ℕ) (prob : STRIPS n) (bef : Vector (WithTop ℕ) n) : Vector (WithTop ℕ) n :=
  let next := h_1_step n prob bef
  if next = bef then
    bef
  else
    h_1_iter_fix n prob next

-- h_1 effectively considers delete relaxation
def h_1_new {n : ℕ} (prob : STRIPS n) (s : State' n) : ℕ :=
  let f : Vector (WithTop ℕ) n → Fin (prob.actions'.length) → Vector (WithTop ℕ) n := fun a _ =>
    h_1_step n prob a
  let result := (List.finRange prob.actions'.length).foldl f (h_1_base n s)
  let s_b := vec_to_state n result
  
  -- check if the goal has been reached
  if h_sat : satisfies' prob.goal' s_b then
    let pre_cost : List ℕ := prob.goal'.val.attach.map (fun x : { x : Fin n // x ∈ prob.goal'.val } =>
      result[x.1].get (by exact vec_to_state_isSome_of_satisfies n result prob.goal' h_sat x.1 x.2))

    -- cost of the action plus most expensive precondition
    if pre_cost_nil : pre_cost = [] then 0 else pre_cost.max pre_cost_nil
  else
    (2^n) * (max_action_cost prob) -- state is unsolvable


lemma h_1_has_invar {n : ℕ} (prob : STRIPS n):
  h_1_heuristic_regression_invariant prob h_1_new := by sorry


theorem h_1_new_admissible {n : ℕ} (prob : STRIPS n) :
  heur_admissible prob (h_1_new prob) := by
    apply admissible_of_h_1_regression_invariant
    apply h_1_has_invar
