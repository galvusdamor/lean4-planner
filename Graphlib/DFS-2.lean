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
    pathOrder : visited → Nat 
    mother : visited → V
    stack : List V


abbrev dfs_invar_stack_is_visited [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (s : dfs_state g):=
      ∀ x : V, x ∈ s.stack → x ∈ s.visited

abbrev dfs_invar_mother_is_visited [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (s : dfs_state g):=
      ∀ x : s.visited, s.mother x ∈ s.visited


abbrev dfs_invar_mother_decreasing_path_order [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : dfs_state g)
    (mother_invar : dfs_invar_mother_is_visited g s)
    :=
      ∀ x : s.visited, ↑x ≠ start →
        s.pathOrder ⟨(s.mother x), by simp_all only [Subtype.forall]⟩  < s.pathOrder x 


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

      let new_order : new_visited → Nat := fun ⟨v, hv⟩  =>
        if h: (v ∈ priorState.visited) then priorState.pathOrder ⟨ v, by exact h⟩
        else priorState.stack.length

      dfs_state.mk new_visited new_order new_mother new_stack


lemma dfs_expand_newly_added_are_adjacent --[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g)
    (stackHead : V)
    (stackTail : List V):
    ∀ x : V, x ∉ priorState.visited ∧ x ∉ stackTail ∧
      x ∈ (dfs_step_expand g priorState stackHead stackTail).stack →  
      g.Adj stackHead x := by
    intro x
    intro ⟨x_not_visi, ⟨ x_not_on_stack_before, x_on_stack_after ⟩  ⟩
    unfold dfs_step_expand at x_on_stack_after
    simp_all


lemma dfs_expand_keeps_stack_in_visited --[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g)
    (stackHead : V)
    (stackTail : List V):
    dfs_invar_stack_is_visited g priorState ∧
      stackHead ∈ priorState.visited ∧ (∀ x : V, x ∉ priorState.visited → x ∉ stackTail) →
      dfs_invar_stack_is_visited g (dfs_step_expand g priorState stackHead stackTail) := by
      intro ⟨ stack_is_visited_prior, stackhead_visited, x_not_in_stack_tail⟩ 
      unfold dfs_invar_stack_is_visited
      intro x 
      intro x_now_on_stack
      unfold dfs_step_expand
      simp_all
      by_cases x_was_visited : x ∈ priorState.visited
      · left
        exact x_was_visited
      · right
        apply And.intro
        · apply (dfs_expand_newly_added_are_adjacent g priorState stackHead stackTail)
          simp_all
        · exact x_was_visited


lemma dfs_expand_keeps_mother_in_visited --[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g)
    (stackHead : V)
    (stackTail : List V):
    dfs_invar_mother_is_visited g priorState ∧ stackHead ∈ priorState.visited → dfs_invar_mother_is_visited g (dfs_step_expand g priorState stackHead stackTail) := by
      intro mother_is_visited_prior
      unfold dfs_invar_mother_is_visited
      intro x
      simp_all
      unfold dfs_step_expand
      simp_all
      by_cases x_is_already_visited : ↑x ∈ priorState.visited
      all_goals
        simp_all


--abbrev [FinEnum V] [DecidableEq E] [DecidableEq V]
--    (g: WeightedDiGraph V E) (start : V) (s : dfs_state g start):=
--      ∀ x : s.visited, (∃ y ∈ s.stack, y.node = x) ∨ ∀ y : V, (g.Adj x y) → y ∈ s.visited






---------------------------------------------------------------------------------------

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


lemma dfs_step_keeps_stack_in_visited --[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g):
    ∀ goal : V,
    dfs_invar_stack_is_visited g priorState →
      dfs_invar_stack_is_visited g (dfs_step g goal priorState).fst := by
        intro goal
        intro stack_is_visited_prior 
        unfold dfs_step
        split
        · simp_all
          exact stack_is_visited_prior
        next _ head tail head_tail_compose =>
        split
        · simp_all
          exact stack_is_visited_prior
        apply dfs_expand_keeps_stack_in_visited
        simp_all
        constructor
        · exact stack_is_visited_prior
        intro y y_not_visited
        intro y_in_tail
        simp_all
      


lemma dfs_step_keeps_mother_in_visited --[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g):
    ∀ goal : V,
    dfs_invar_stack_is_visited g priorState ∧ dfs_invar_mother_is_visited g priorState →
      dfs_invar_mother_is_visited g (dfs_step g goal priorState).fst := by
      intro goal
      intro ⟨ mother_is_visited_prior, stack_is_visited_prior ⟩ 
      unfold dfs_step
      split
      · simp_all
      next _ head tail head_tail_compose =>
      split
      · simp_all
      apply dfs_expand_keeps_mother_in_visited
      simp_all




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
  let initialVisited : Finset V := ⟨ {start},  by simp ⟩ 
  let initialMother : initialVisited → V := fun x => start 
  let initialPathOrder : initialVisited → Nat := fun x => 0 
  let initialStack : List V := [start]
  let startState : dfs_state g := dfs_state.mk initialVisited initialPathOrder initialMother initialStack

  (dfs_recurse g goal startState).2
