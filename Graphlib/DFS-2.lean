import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum

import Graphlib.Lists
import Graphlib.Basic

set_option trace.split.failure true
--set_option diagnostics true


-- def local global variable for a graph
variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V] [DecidableEq E]
variable (G : WeightedDiGraph V E)

------ DFS implementation and proof ------



structure dfs_state [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) where
    visited : Finset V
    mother : visited → V
    stack : List V


def dfs_step_expand[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g)
    (stackHead : V)
    (stackTail : List V):
    (dfs_state g) :=
      let newly_visited : Finset V := (Finset.univ).filterMap
        (λ v => if @decide (g.Adj stackHead v) (g.instDecAdj stackHead v) ∧ v ∉ priorState.visited
                  then some v
                  else none)
        (by intro a a' b a_1 a_2; simp_all) -- filter neighbors to expand the visited list

      
      let vList : List V := (FinEnum.toList (Finset.univ : Finset V))
      let newly_visited_list : List V :=
        vList.filterMap (λ v => if v ∈ newly_visited then some v else none)
      let new_visited : Finset V := priorState.visited ∪ newly_visited
      let new_stack : List V := newly_visited_list ++ stackTail -- add neighbors in front to stack
     
      let new_mother : new_visited → V := fun ⟨v, hv⟩  =>
        if h: (v ∈ priorState.visited) then priorState.mother ⟨ v, by exact h⟩
        else stackHead

      dfs_state.mk new_visited new_mother new_stack


def dfs_step [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (goal : V)
    (priorState : dfs_state g) :
    (dfs_state g) × (Option (Option V)) :=
  match priorState.stack with
    | [] => (priorState, some none) -- goal not found
    | (s :: xs) =>
    if h : s = goal then (priorState, some (some s))
    else
      (dfs_step_expand g priorState s xs, none)




def dfs_recurse[ FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (goal : V)
    (priorState : dfs_state g) :
    (dfs_state g) × (Option (Option V)) :=
  let ⟨ nextState, result ⟩ := dfs_step g goal priorState
  match result with 
    | none => dfs_recurse g goal nextState
    | some x => ⟨ nextState, result ⟩ 
termination_by (Fintype.card V - priorState.visited.card, priorState.stack.length) -- must be a well-founded relation/measure
decreasing_by
  sorry



def dfs[ FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    (priorState : dfs_state g) :
    (Option (Option V)) :=
  let initialVisited : Finset V := ⟨ {start},  by sorry ⟩ 
  let initialMother : initialVisited → V := fun x => start 
  let initialStack : List V := [start]
  let startState : dfs_state g := dfs_state.mk initialVisited initialMother initialStack

  (dfs_recurse g goal startState).2
