import Validator.PlanningTask.Core
import Validator.PlanningTask.Basic
import Graphlib.NatGraph
import Graphlib.Planning
import Graphlib.Heuristics

import Graphlib.temp

import Mathlib.Logic.Lemmas
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Vector.Basic

namespace Validator



def h_1_base (n : ℕ) (s : State' n) : Vector (WithTop ℕ) n :=
    (Vector.finRange n).map (fun i => if s[i] then some 0 else none)


def vec_to_state (n : ℕ) (bef : Vector (WithTop ℕ) n) : State' n :=
  let l_bool : List Bool := (bef.map (fun x => x.isSome)).toList
  have l_bool_len : l_bool.length = n := by grind
  l_bool_len ▸ BitVec.ofBoolListLE l_bool



def h_1_step (n : ℕ) (prob : STRIPS n) (bef : Vector (WithTop ℕ) n) : Vector (WithTop ℕ) n :=
  let s_b := vec_to_state n bef
  -- update the values of each fact 
  (Vector.finRange n).map (fun i : Fin n =>
    let applicable : List ℕ := prob.actions'.filterMap (fun a =>
    if i ∈ a.add'.1 then -- consider only actions that add the fact i. We ignore delete effects
      if is_appli : applicable' a s_b then
        let pre_cost : List ℕ := a.pre'.1.attach.map (fun x : { x : Fin n // x ∈a.pre'.1 } =>
          bef[x.1].get (by
            unfold applicable' satisfies' at is_appli
            unfold Option.isSome
            simp_all
            sorry))
         
        -- cost of the action plus most expensive precondition 
        if pre_cost_nil : pre_cost = [] then .some (a.cost)
        else
          let preMax : ℕ := pre_cost.max pre_cost_nil
          .some (a.cost + preMax)
      else .none -- action not applicable given the facts that are currently .some 
    else .none)
    
    if appli_nil : applicable = [] then bef[i]
    else
      let minCost : ℕ := applicable.min appli_nil 
      if minCost < i then .some minCost else bef[i]
  )


-- h_1 effectively considers delete relaxation
def h_1 {n : ℕ} (prob : STRIPS n) (s : State' n) : ℕ :=
  let f : Vector (WithTop ℕ) n → Fin (prob.actions'.length) → Vector (WithTop ℕ) n := fun a _ =>
    h_1_step n prob a
  let result := (List.finRange prob.actions'.length).foldl f (h_1_base n s) 
  
  let s_b := vec_to_state n result
  
  -- check if the goal has been reached
  if satisfies' prob.goal' s_b then
    let pre_cost : List ℕ := prob.goal'.val.attach.map (fun x : { x : Fin n // x ∈ prob.goal'.val } =>
      result[x.1].get (by sorry))
     
    -- cost of the action plus most expensive precondition 
    if pre_cost_nil : pre_cost = [] then 0 else pre_cost.max pre_cost_nil
  else
    (2^n) * (max_action_cost prob) -- state is unsolvable



lemma h_1_admissible {n : ℕ} (prob : STRIPS n) : heur_admissible' prob (h_1 prob) := by
  sorry
