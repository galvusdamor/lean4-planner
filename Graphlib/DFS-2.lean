import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Empty
import Mathlib.Data.List.MinMax

import Graphlib.Lists
import Graphlib.FinEnum
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
    pathOrder : V → Nat 
    mother : visited → V
    stack : List V


def maximum_path_order_of [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (dfs_state : dfs_state g)
    (states : Finset V)
    (non_empty : states ≠ ∅): Nat :=
  let vList : List V := (FinEnum.toList states)
  have vListNonEmpty : vList ≠ [] := by
    unfold vList
    intro a
    simp_all
    have statesEmpty : states = ∅ := by
      by_cases h : ∃ x, x ∈ states
      · obtain ⟨s, s_in_states⟩ := h
        have hh : s ∈ (FinEnum.toList { x // x ∈ states }).unattach := by
          clear a
          simp_all only [List.mem_unattach, FinEnum.mem_toList, exists_const]
        simp_all 
      · ext y
        simp_all only [not_exists, Finset.notMem_empty]
    contradiction
  let opt : Option Nat := List.max? (vList.map (λ s => dfs_state.pathOrder s))

  have optNotBot : opt ≠ none := by 
    unfold opt
    intro _
    simp_all
  Option.get opt (by
    unfold Option.isSome
    unfold opt
    split
    · rfl
    · simp_all
  )

lemma maximum_path_order_is_le 
    (g: WeightedDiGraph V E)
    (dfs_state : dfs_state g)
    (states : Finset V)
    (non_empty : states ≠ ∅):
    ∀ s ∈ states, dfs_state.pathOrder s ≤ maximum_path_order_of g dfs_state states non_empty := by
    intro s s_in_states
    unfold maximum_path_order_of
    simp_all
    apply maximum_of_non_empty_le
    · simp_all
      apply List.ne_nil_of_mem
      rotate_right
      · use s
      · simp_all
    · simp_all
      use s

abbrev dfs_invar_stack_is_visited [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (s : dfs_state g):=
      ∀ x : V, x ∈ s.stack → x ∈ s.visited

abbrev dfs_invar_mother_is_visited [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (s : dfs_state g):=
      ∀ x : s.visited, s.mother x ∈ s.visited

abbrev dfs_invar_mother_decreasing_path_order [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : dfs_state g) :=
      ∀ x : s.visited, ↑x ≠ start → s.pathOrder (s.mother x) < s.pathOrder x 


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

      let new_order : V → Nat := fun v  =>
        if h: (v ∈ priorState.visited) then priorState.pathOrder v
        else if hh : (priorState.visited.card = 0) then 0
        else 1 + maximum_path_order_of g priorState priorState.visited (by simp_all)
        -- priorState.stack.length
      
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



lemma dfs_expand_keeps_mother_ordered --[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g)
    (stackHead : V)
    (stackTail : List V):
    dfs_invar_mother_is_visited g priorState ∧
      stackHead ∈ priorState.visited ∧ 
      dfs_invar_mother_decreasing_path_order g start priorState
      → dfs_invar_mother_decreasing_path_order g start
          (dfs_step_expand g priorState stackHead stackTail)
          := by
    intro ⟨mother_is_visited, stack_head_visited_prior,mother_decreasing_prior⟩  
    unfold dfs_invar_mother_decreasing_path_order
    intro a a_not_stat
    unfold dfs_step_expand
    simp_all
    split
    · next a_visited =>
      simp_all
    · next a_not_visited =>
      split
      · simp_all
      · rw [Nat.add_comm]
        apply Nat.lt_succ_of_le
        apply maximum_path_order_is_le
        simp_all

--abbrev [FinEnum V] [DecidableEq E] [DecidableEq V]
--    (g: WeightedDiGraph V E) (start : V) (s : dfs_state g start):=
--      ∀ x : s.visited, (∃ y ∈ s.stack, y.node = x) ∨ ∀ y : V, (g.Adj x y) → y ∈ s.visited


---------------------------------------------------------------------------------------
-- run one step of the DFS. Mostly case distinction and running expansion if necessary
def dfs_step [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (goal : V)
    (priorState : dfs_state g) :
    (dfs_state g) × (Option (Option V)) :=
  match priorState.stack with
    | [] => (priorState, some none) -- goal not found
    | (s :: xs) =>
    if s = goal then (priorState, some (some s))
    else
      (dfs_step_expand g priorState s xs, none)

----------
-- the step also keeps the invariants
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


lemma dfs_step_keeps_mother_ordered
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g):
    ∀ goal : V,
      dfs_invar_stack_is_visited g priorState ∧
      dfs_invar_mother_is_visited g priorState ∧
      dfs_invar_mother_decreasing_path_order g start priorState
      → dfs_invar_mother_decreasing_path_order g start (dfs_step g goal priorState).fst := by
        intro goal
        intro ⟨ stack_visited, mother_visited, mother_decreasing⟩ 
        unfold dfs_step
        split
        · simp_all
        next _ head tail head_tail_compose => 
        split
        · simp_all
        apply dfs_expand_keeps_mother_ordered
        simp_all


--------------------------------------------------------------------------------------------------
-- main recursion loop 
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


--------------------------------------------------------------------------------------------------
-- initial configuration of the DFS
def dfs_initial_state [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V) :
    dfs_state g :=
  let initialVisited : Finset V := ⟨ {start},  by simp ⟩ 
  let initialMother : initialVisited → V := fun x => start 
  let initialPathOrder : V → Nat := fun x => 0 
  let initialStack : List V := [start]
  dfs_state.mk initialVisited initialPathOrder initialMother initialStack


----- Proofs that the initial state of the DFS satisfies the invariants
theorem dfs_invar_stack_is_visited_initial 
    (g: WeightedDiGraph V E) (start : V) (goal : V) :
      dfs_invar_stack_is_visited g (dfs_initial_state g start goal) := by 
      unfold dfs_invar_stack_is_visited
      unfold dfs_initial_state
      simp


theorem dfs_invar_mother_is_visited_initial 
    (g: WeightedDiGraph V E) (start : V) (goal : V) :
      dfs_invar_mother_is_visited g (dfs_initial_state g start goal) := by 
      unfold dfs_invar_mother_is_visited
      unfold dfs_initial_state
      simp

theorem dfs_invar_mother_decreasing_path_order_initial
    (g: WeightedDiGraph V E) (start : V) (goal : V) :
      dfs_invar_mother_decreasing_path_order g start (dfs_initial_state g start goal) := by 
      unfold dfs_invar_mother_decreasing_path_order  
      unfold dfs_initial_state
      simp


----------------- the actual DFS: create the initial search state and then recurse
def dfs[ FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    (Option (Option V)) :=
  let startState : dfs_state g := dfs_initial_state g start goal

  (dfs_recurse g goal startState).2
