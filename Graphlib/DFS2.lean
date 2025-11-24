import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Empty
import Mathlib.Data.List.MinMax

import Graphlib.Lists
import Graphlib.FinEnum
import Graphlib.Basic
import Graphlib.SearchCommon

set_option trace.split.failure true
--set_option diagnostics true

-- def local global variable for a graph
variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V] [DecidableEq E]
variable (G : WeightedDiGraph V E)

-----------------------------------------------------------------------
------ DFS implementation and proof ------

def dfs_step_expand[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start)
    (stackHead : V)
    (stackTail : List V):
    (base_search_state g start) :=
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
      
      --let new_mother_proof (v : new_visited): ↑v ≠ start → g.Adj (new_mother v) v :=
      -- fun not_start =>
      --  by
      --    unfold new_mother
      --    simp_all
      --    split
      --    · next prior_visited_v =>
      --      exact priorState.mother_proof ⟨↑v, prior_visited_v⟩ not_start
      --    · next not_prior_visited_v => 
      --      obtain ⟨ vv, v_new_visited ⟩ := v
      --      unfold new_visited at v_new_visited
      --      simp_all
      --      simp at v_new_visited
      --      simp_all
      --      unfold newly_visited at v_new_visited
      --      simp_all

      let new_order : V → Nat := fun v  =>
        if h: (v ∈ priorState.visited) then priorState.pathOrder v
        else if hh : (priorState.visited.card = 0) then 0
        --else 1 + maximum_path_order_of g priorState priorState.visited (by simp_all)
        else 1 + priorState.pathOrder stackHead
        -- priorState.stack.length
      
      base_search_state.mk new_visited new_order new_mother new_stack false


lemma dfs_expand_newly_added_are_adjacent --[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start)
    (stackHead : V)
    (stackTail : List V):
    ∀ x : V, x ∉ priorState.visited ∧ x ∉ stackTail ∧
      x ∈ (dfs_step_expand g start priorState stackHead stackTail).stack →  
      g.Adj stackHead x := by
    intro x
    intro ⟨x_not_visi, ⟨ x_not_on_stack_before, x_on_stack_after ⟩  ⟩
    unfold dfs_step_expand at x_on_stack_after
    simp_all


lemma dfs_expand_keeps_stack_in_visited --[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start)
    (stackHead : V)
    (stackTail : List V):
    search_invar_stack_is_visited g start priorState ∧
      stackHead ∈ priorState.visited ∧ (∀ x : V, x ∉ priorState.visited → x ∉ stackTail) →
      search_invar_stack_is_visited g start (dfs_step_expand g start priorState stackHead stackTail) := by
      intro ⟨ stack_is_visited_prior, stackhead_visited, x_not_in_stack_tail⟩ 
      unfold search_invar_stack_is_visited
      intro x 
      intro x_now_on_stack
      unfold dfs_step_expand
      simp_all
      by_cases x_was_visited : x ∈ priorState.visited
      · left
        exact x_was_visited
      · right
        apply And.intro
        · apply (dfs_expand_newly_added_are_adjacent g start priorState stackHead stackTail)
          simp_all
        · exact x_was_visited


lemma dfs_expand_keeps_mother_in_visited --[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_visited g start priorState ∧ stackHead ∈ priorState.visited → search_invar_mother_is_visited g start (dfs_step_expand g start priorState stackHead stackTail) := by
      intro mother_is_visited_prior
      unfold search_invar_mother_is_visited
      intro x
      simp_all
      unfold dfs_step_expand
      simp_all
      by_cases x_is_already_visited : ↑x ∈ priorState.visited
      all_goals
        simp_all

lemma dfs_expand_keeps_mother_is_adjacent --[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_adjacent g start priorState → search_invar_mother_is_adjacent g start (dfs_step_expand g start priorState stackHead stackTail) := by
      intro mother_is_adjacent_prior
      unfold search_invar_mother_is_adjacent
      intro x
      simp_all
      intro x_not_start
      unfold dfs_step_expand
      simp_all
      split
      · simp_all
      · next x_not_prior_visited => 
        obtain ⟨ xx, x_in_new_visited ⟩ := x
        unfold dfs_step_expand at x_in_new_visited
        simp at x_in_new_visited
        simp_all

lemma dfs_expand_keeps_mother_ordered --[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_visited g start priorState ∧
      stackHead ∈ priorState.visited ∧ 
      search_invar_mother_decreasing_path_order g start priorState
      → search_invar_mother_decreasing_path_order g start
          (dfs_step_expand g start priorState stackHead stackTail)
          := by
    intro ⟨mother_is_visited, stack_head_visited_prior,mother_decreasing_prior⟩  
    unfold search_invar_mother_decreasing_path_order
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
        apply le_refl
        --apply maximum_path_order_is_le
        --simp_all

lemma dfs_expand_keeps_on_stack_or_all_neighbours_visited
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start)
    (stackHead : V)
    (stackTail : List V):
     search_invar_on_stack_or_all_neighbours_visited g start priorState
     ∧ priorState.stack = (stackHead :: stackTail)
     → search_invar_on_stack_or_all_neighbours_visited g start
          (dfs_step_expand g start priorState stackHead stackTail)
          := by
      intro ⟨ invar_holds_on_prior_state, stack_composition ⟩ 
      unfold search_invar_on_stack_or_all_neighbours_visited
      intro ⟨ x, x_now_on_stack⟩
      by_cases x_not_stack_head : x ≠ stackHead
      · by_cases x_was_not_in_stack_tail_: x ∈ stackTail
        · left
          unfold dfs_step_expand
          simp_all
        · by_cases x_not_visited : x ∉ priorState.visited
          · left
            unfold dfs_step_expand
            unfold dfs_step_expand at x_now_on_stack
            simp at x_now_on_stack
            simp_all
          · simp_all -- x was visited before and is not on the stack any more
            right
            intro y x_adj_y
            unfold dfs_step_expand
            simp_all
            left
            have x_invar := invar_holds_on_prior_state x
            simp_all
      · simp_all
        right
        intro y x_adj_y
        unfold dfs_step_expand
        simp_all
        by_cases h : y ∈ priorState.visited
        · left; exact h
        · right; exact h

lemma dfs_expand_keeps_start_visited
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start)
    (stackHead : V)
    (stackTail : List V):
     search_invar_start_visited g start priorState →
     search_invar_start_visited g start (dfs_step_expand g start priorState stackHead stackTail)
          := by
      intro pre_invar
      unfold dfs_step_expand
      unfold search_invar_start_visited 
      simp_all


---------------------------------------------------------------------------------------
-- run one step of the DFS. Mostly case distinction and running expansion if necessary
def dfs_step [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    (priorState : base_search_state g start) :
    (base_search_state g start) × (Option Bool) :=
  match priorState.stack with
    | [] => ({priorState with terminated := true} , some false) -- goal not found
    | (s :: xs) =>
    if s = goal then ({priorState with terminated := true}, some true)
    else
      (dfs_step_expand g start priorState s xs, none)


lemma dfs_step_visited_subset 
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    (priorState : base_search_state g start) :
    priorState.visited ⊆ (dfs_step g start goal priorState).1.visited := by
    unfold dfs_step
    split
    · simp_all
    split
    · simp_all
    unfold dfs_step_expand
    simp_all

lemma dfs_step_visited_is_smaller_than_V 
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    (priorState : base_search_state g start):
   (dfs_step g start goal priorState).1.visited.card ≤ Fintype.card V := by
    apply Finset.card_le_univ
  
lemma dfs_step_visited_increases
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    (priorState : base_search_state g start):
      (dfs_step g start goal priorState).1.visited.card ≥ priorState.visited.card := by
    change priorState.visited.card ≤ (dfs_step g start goal priorState).1.visited.card
    apply Finset.card_le_card
    apply dfs_step_visited_subset

----------
-- the step also keeps the invariants
lemma dfs_step_keeps_stack_in_visited 
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start):
    ∀ goal : V,
    search_invar_stack_is_visited g start priorState →
      search_invar_stack_is_visited g start (dfs_step g start goal priorState).fst := by
        intro goal stack_is_visited_prior 
        unfold dfs_step
        split
        · unfold search_invar_stack_is_visited
          simp_all
        next _ head tail head_tail_compose =>
        split
        · unfold search_invar_stack_is_visited
          simp_all
        apply dfs_expand_keeps_stack_in_visited
        simp_all
        constructor
        · exact stack_is_visited_prior
        intro y y_not_visited y_in_tail
        simp_all


lemma dfs_step_keeps_mother_in_visited 
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start):
    ∀ goal : V,
    search_invar_stack_is_visited g start priorState ∧ search_invar_mother_is_visited g start priorState →
      search_invar_mother_is_visited g start (dfs_step g start goal priorState).fst := by
      intro goal ⟨ mother_is_visited_prior, stack_is_visited_prior ⟩ 
      unfold dfs_step
      split
      · simp_all
      next _ head tail head_tail_compose =>
      split
      · simp_all
      apply dfs_expand_keeps_mother_in_visited
      simp_all


lemma dfs_step_keeps_mother_is_adjacent
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start):
    ∀ goal : V,
    search_invar_mother_is_adjacent g start priorState →
      search_invar_mother_is_adjacent g start (dfs_step g start goal priorState).fst := by
      intro goal mother_is_adjacent_prior
      unfold dfs_step
      split
      · simp_all
      next _ head tail head_tail_compose =>
      split
      · simp_all
      apply dfs_expand_keeps_mother_is_adjacent
      simp_all


lemma dfs_step_keeps_mother_ordered
    (g: WeightedDiGraph V E)
    (start : V)(priorState : base_search_state g start):
    ∀ goal : V,
      search_invar_stack_is_visited g start priorState ∧
      search_invar_mother_is_visited g start priorState ∧
      search_invar_mother_decreasing_path_order g start priorState
      → search_invar_mother_decreasing_path_order g start (dfs_step g start goal priorState).fst := by
        intro goal ⟨ stack_visited, mother_visited, mother_decreasing⟩ 
        unfold dfs_step
        split
        · simp_all
        next _ head tail head_tail_compose => 
        split
        · simp_all
        apply dfs_expand_keeps_mother_ordered
        simp_all


lemma dfs_step_keeps_on_stack_or_all_neighbours_visited
    (g: WeightedDiGraph V E)
    (start : V)(priorState : base_search_state g start):
    ∀ goal : V,
     search_invar_on_stack_or_all_neighbours_visited g start priorState
     → search_invar_on_stack_or_all_neighbours_visited g start 
          (dfs_step g start goal priorState).fst := by
        intro goal stack_or_neighbour_visited
        unfold dfs_step
        split
        · simp_all
          exact stack_or_neighbour_visited
        next _ head tail head_tail_compose => 
        split
        · simp_all
        apply dfs_expand_keeps_on_stack_or_all_neighbours_visited
        simp_all

lemma dfs_step_keeps_start_in_visited 
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start):
    ∀ goal : V,
    search_invar_start_visited g start priorState →
      search_invar_start_visited g start (dfs_step g start goal priorState).fst := by
        intro goal stack_is_visited_prior 
        unfold dfs_step
        split
        · unfold search_invar_start_visited
          simp_all
        next _ head tail head_tail_compose =>
        split
        · unfold search_invar_start_visited
          simp_all
        apply dfs_expand_keeps_start_visited
        simp_all

lemma dfs_step_keeps_all_basic_invars
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start):
     search_invar_all_basic g start priorState →
     search_invar_all_basic g start (dfs_step g start goal priorState).fst
          := by
        unfold search_invar_all_basic
        intro ⟨ invar_stack_visited, invar_mother_visited, invar_mother_adjacent, invar_mother_decreasing, invar_nei_visited, invar_start_visited⟩
        repeat rw [← and_assoc]
        repeat constructor
        · apply dfs_step_keeps_stack_in_visited
          exact invar_stack_visited
        · apply dfs_step_keeps_mother_in_visited
          exact ⟨ invar_stack_visited, invar_mother_visited⟩ 
        · apply dfs_step_keeps_mother_is_adjacent
          exact invar_mother_adjacent
        · apply dfs_step_keeps_mother_ordered
          exact ⟨ invar_stack_visited, invar_mother_visited, invar_mother_decreasing ⟩ 
        · apply dfs_step_keeps_on_stack_or_all_neighbours_visited
          exact invar_nei_visited
        · apply dfs_step_keeps_start_in_visited
          exact invar_start_visited

lemma dfs_step_keeps_goal_on_stack
    (g: WeightedDiGraph V E)
    (start : V) (goal : V)
    (priorState : base_search_state g start):
    search_prop_goal_on_stack g start goal priorState → 
    search_prop_goal_on_stack g start goal (dfs_step g start goal priorState).fst := by
      unfold search_prop_goal_on_stack
      intro goal_prior_on_stack
      unfold dfs_step
      split
      · simp_all
      · simp_all
        split
        · simp_all
        · simp_all
          unfold dfs_step_expand
          simp_all
          right
          cases goal_prior_on_stack
          · next h h' =>
            rw [h'] at h
            contradiction 
          · next h => exact h


lemma dfs_step_returns_none_means_not_terminated
  (g: WeightedDiGraph V E) (start : V) (goal : V)(priorState : base_search_state g start):
  (dfs_step g start goal priorState).2 = none → 
    search_state_not_terminated g start (dfs_step g start goal priorState).1 := by
    intro step_returned_none
    unfold search_state_not_terminated
    unfold dfs_step at step_returned_none ⊢
    split
    · simp_all
    · split
      · simp_all
      · unfold dfs_step_expand
        simp [has_base_search_state.to_base_state]

lemma dfs_step_goal_on_stack_if_terminated
    (g: WeightedDiGraph V E) (start : V)(priorState : base_search_state g start):
    ∀ goal : V, (dfs_step g start goal priorState).2 = true →
     goal ∈ (dfs_step g start goal priorState).1.stack := by
   intro goal terminated_with_true
   next step_did_terminate =>
   unfold dfs_step at terminated_with_true ⊢
   split
   · next l stack_empty =>
     simp_all
   · next l head tail stack_not_empty =>
     simp_all
     split
     all_goals
      simp_all

lemma dfs_step_stack_empty_if_terminated_without_goal
    (g: WeightedDiGraph V E) (start : V)(priorState : base_search_state g start):
    ∀ goal : V, (dfs_step g start goal priorState).2 = false →
     (dfs_step g start goal priorState).1.stack  = [] := by
   intro goal terminated_with_true
   next step_did_terminate =>
   unfold dfs_step at terminated_with_true ⊢
   split
   · next l stack_empty =>
     simp_all
   · next l head tail stack_not_empty =>
     simp_all
     split
     all_goals
      simp_all


--------------------------------------------------------------------------------------------------
-- main recursion loop 


lemma termination_dfs_recurse 
    (g: WeightedDiGraph V E) (start : V)(goal : V)
    (priorState : base_search_state g start)
    (nextState : base_search_state g start):
    (nextState = (dfs_step g start goal priorState).1) ∧ (nextState.terminated = false)
    → ((Fintype.card V - nextState.visited.card < Fintype.card V - priorState.visited.card
        ∨ (Fintype.card V - nextState.visited.card = Fintype.card V - priorState.visited.card ∧ nextState.stack.length < priorState.stack.length)) ):= by
  intro ⟨ nextStateDef, still_not_terminated ⟩
  apply (Classical.or_iff_not_imp_left).mpr
  intro visited_not_decreasing
  simp_all
  have same_visited : (dfs_step g start goal priorState).1.visited.card = priorState.visited.card := by
    have k2 : (dfs_step g start goal priorState).1.visited.card ≤ Fintype.card V :=
      dfs_step_visited_is_smaller_than_V g start goal priorState
    have k3 : (dfs_step g start goal priorState).1.visited.card ≥ priorState.visited.card := 
      dfs_step_visited_increases g start goal priorState
    omega
  have visited_eq : priorState.visited = (dfs_step g start goal priorState).1.visited := by
    ext a
    constructor
    · apply Finset.mem_of_subset
      apply dfs_step_visited_subset 
    apply finsetLemma
    · apply dfs_step_visited_subset 
    exact same_visited

  constructor
  · omega
  · unfold dfs_step
    split
    · have contra : nextState.terminated = true := by 
        clear still_not_terminated same_visited 
        rw [nextStateDef]
        unfold dfs_step 
        split
        · simp_all
        split
        · simp_all 
        unfold dfs_step_expand
        simp_all
      simp_all
    split -- style is bad!
    · next _ head tail compose is_goal =>
      have contra : nextState.terminated = true := by 
        clear still_not_terminated same_visited 
        rw [nextStateDef]
        unfold dfs_step 
        split
        · simp_all
        split
        · simp_all
        unfold dfs_step_expand
        simp_all
      simp_all
    next _ head tail compose not_goal =>
    unfold dfs_step_expand
    simp_all
    simp [Nat.add_comm]
    intro a head_adj_a
    rw [visited_eq]
    unfold dfs_step
    split
    · simp_all
    split
    · simp_all
    unfold dfs_step_expand
    simp_all
    by_cases h : a ∈ (dfs_step g start goal priorState).1.visited
    · left; exact h
    · right; exact h

lemma dfs_step_reduces_metric
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    ∀ s : base_search_state g start,
        search_state_not_terminated g start (dfs_step g start goal s).1 → 
        Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2)
        (base_search_state_termination_metric g start (dfs_step g start goal s).1) (base_search_state_termination_metric g start s) := by
    intro state did_not_terminate
    unfold base_search_state_termination_metric
    apply Prod.lex_def.mpr
    simp
    apply termination_dfs_recurse
    rotate_left
    · use goal
    · simp
      unfold search_state_not_terminated at did_not_terminate
      exact did_not_terminate


lemma dfs_step_does_not_set_terminate
    (g: WeightedDiGraph V E) (start : V) (goal : V):
search_step_does_not_terminate g start goal (dfs_step g start) := by
  unfold search_step_does_not_terminate
  simp
  intro s returned_none
  unfold dfs_step at returned_none ⊢
  split
  · simp_all
  · next _ head tail compose =>
    simp_all
    split
    all_goals
      simp_all -- one goal vanishes
    rfl -- no idea why this works without unfolding the dfs_step


def dfs_recurse [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    (priorState : base_search_state g start)
    (not_terminated : priorState.terminated = false):
    (base_search_state g start) × Bool :=
    search_recurse g start goal priorState (by unfold search_state_not_terminated; exact not_terminated) (dfs_step g start) (dfs_step_does_not_set_terminate g start goal) (base_search_state_termination_metric g start) (dfs_step_reduces_metric g start goal)




--------------------------------------------------------------------------------------------------
-- initial configuration of the DFS
def dfs_initial_state [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V):
    base_search_state g start :=
  let initialVisited : Finset V := ⟨ {start},  by simp ⟩ 
  let initialMother : initialVisited → V := fun x => start 
  let initialPathOrder : V → Nat := fun x => 0 
  let initialStack : List V := [start]
  base_search_state.mk initialVisited initialPathOrder initialMother initialStack false


----- Proofs that the initial state of the DFS satisfies the invariants
lemma search_invar_stack_is_visited_initial 
    (g: WeightedDiGraph V E) (start : V):
      search_invar_stack_is_visited g start (dfs_initial_state g start) := by 
      unfold search_invar_stack_is_visited
      unfold dfs_initial_state
      simp


lemma search_invar_mother_is_visited_initial 
    (g: WeightedDiGraph V E) (start : V):
      search_invar_mother_is_visited g start (dfs_initial_state g start) := by 
      unfold search_invar_mother_is_visited
      unfold dfs_initial_state
      simp

lemma search_invar_mother_is_adjacent_initial
    (g: WeightedDiGraph V E) (start : V):
      search_invar_mother_is_adjacent g start (dfs_initial_state g start) := by 
      unfold search_invar_mother_is_adjacent
      unfold dfs_initial_state
      simp

lemma search_invar_mother_decreasing_path_order_initial
    (g: WeightedDiGraph V E) (start : V):
      search_invar_mother_decreasing_path_order g start (dfs_initial_state g start) := by 
      unfold search_invar_mother_decreasing_path_order  
      unfold dfs_initial_state
      simp

lemma search_invar_on_stack_or_all_neighbours_visited_initial
    (g: WeightedDiGraph V E) (start : V):
      search_invar_on_stack_or_all_neighbours_visited g start (dfs_initial_state g start) := by 
      unfold search_invar_on_stack_or_all_neighbours_visited  
      unfold dfs_initial_state
      simp

lemma search_invar_start_visited_initial
    (g: WeightedDiGraph V E) (start : V):
      search_invar_start_visited g start (dfs_initial_state g start) := by 
      unfold search_invar_start_visited  
      unfold dfs_initial_state
      simp

lemma dfs_initial_state_is_not_termianted
    (g: WeightedDiGraph V E) (start : V):
      (dfs_initial_state g start).terminated = false := by
      unfold dfs_initial_state
      simp

lemma dfs_initial_state_all_basic_invars
    (g: WeightedDiGraph V E) (start : V):
    search_invar_all_basic g start (dfs_initial_state g start) := by
      unfold search_invar_all_basic 
      repeat rw [← and_assoc]
      repeat constructor
      · apply search_invar_stack_is_visited_initial
      · apply search_invar_mother_is_visited_initial
      · apply search_invar_mother_is_adjacent_initial
      · apply search_invar_mother_decreasing_path_order_initial
      · apply search_invar_on_stack_or_all_neighbours_visited_initial
      · apply search_invar_start_visited_initial


----------------- the actual DFS: create the initial search state and then recurse

def dfs_internal[ FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V): (base_search_state g start) × Bool :=
  (dfs_recurse g start goal (dfs_initial_state g start) (dfs_initial_state_is_not_termianted g start))


lemma dfs_returns_with_invariants
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    search_invar_all_basic g start (dfs_internal g start goal).1 := by
    unfold dfs_internal
    apply search_recurse_lift_invariant 
    constructor
    · unfold dfs_initial_state
      simp_all
      apply dfs_initial_state_all_basic_invars
    · unfold invar_carries_over_step
      intro s cond
      apply dfs_step_keeps_all_basic_invars
      exact cond
 
lemma dfs_returns_with_stack_visited
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    search_invar_stack_is_visited g start (dfs_internal g start goal).1 := by
    have all_invars := dfs_returns_with_invariants g start goal
    unfold search_invar_all_basic at all_invars
    exact all_invars.1

lemma dfs_returns_with_mother_visited
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    search_invar_mother_is_visited g start (dfs_internal g start goal).1 := by
    have all_invars := dfs_returns_with_invariants g start goal
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.1

lemma dfs_returns_with_mother_adjacent
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    search_invar_mother_is_adjacent g start (dfs_internal g start goal).1 := by
    have all_invars := dfs_returns_with_invariants g start goal
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.2.1

lemma dfs_returns_with_mother_decreasing
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    search_invar_mother_decreasing_path_order g start (dfs_internal g start goal).1 := by
    have all_invars := dfs_returns_with_invariants g start goal
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.2.2.1

lemma dfs_returns_with_start_visited
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    search_invar_start_visited g start (dfs_internal g start goal).1 := by
    have all_invars := dfs_returns_with_invariants g start goal
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.2.2.2.2

lemma dfs_returns_with_node_on_stack_or_all_neighbours_visited
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    search_invar_on_stack_or_all_neighbours_visited g start (dfs_internal g start goal).1 := by
    have all_invars := dfs_returns_with_invariants g start goal
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.2.2.2.1


lemma dfs_goal_on_stack_if_returned_true
    (g: WeightedDiGraph V E) (start : V) (goal : V): 
    (dfs_internal g start goal).2 = true → goal ∈ (dfs_internal g start goal).1.stack := by 
    intro terminated_with_goal_found 
    unfold dfs_internal
    unfold dfs_recurse
    apply search_recurse_obtain_termination_property g start goal (dfs_initial_state g start) (property_after_termination := search_prop_goal_on_stack g start goal) (terminated_with := true) 
    · intro s
      apply dfs_step_goal_on_stack_if_terminated
    · exact terminated_with_goal_found

lemma dfs_visited_goal_if_returned_true 
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    (dfs_internal g start goal).2 = true → goal ∈ (dfs_internal g start goal).1.visited := by 
    intro terminated_with_goal_found 
    apply dfs_returns_with_stack_visited g start goal
    apply dfs_goal_on_stack_if_returned_true
    exact terminated_with_goal_found 



lemma dfs_empty_stack_if_returned_false_recurse
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    (priorState : base_search_state g start)
    (not_terminated : priorState.terminated = false):
    (dfs_recurse g start goal priorState not_terminated).2 = false → (dfs_recurse g start goal priorState not_terminated).1.stack = [] := by
    intro terminated_with_goal_not_found
    unfold dfs_recurse
    apply search_recurse_obtain_termination_property g start goal priorState (property_after_termination := search_prop_stack_empty g start) (terminated_with := false) 
    · intro s
      apply dfs_step_stack_empty_if_terminated_without_goal 
    · exact terminated_with_goal_not_found

lemma dfs_empty_stack_if_returned_false
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    (dfs_internal g start goal).2 = false → (dfs_internal g start goal).1.stack = [] := by
    intro terminated_with_goal_not_found
    unfold dfs_internal at terminated_with_goal_not_found ⊢ 
    apply dfs_empty_stack_if_returned_false_recurse
    exact terminated_with_goal_not_found

lemma dfs_recurse_if_goal_on_stack_it_remains
    (g: WeightedDiGraph V E)
    (start : V) (priorState : base_search_state g start)
    (not_terminated : priorState.terminated = false):
    ∀ goal : V, search_prop_goal_on_stack g start goal priorState
      → search_prop_goal_on_stack g start goal (dfs_recurse g start goal priorState not_terminated).1:= by
      intro goal invar_initial
      unfold dfs_recurse
      apply search_recurse_lift_invariant 
      constructor
      · exact invar_initial
      · unfold invar_carries_over_step
        apply dfs_step_keeps_goal_on_stack
        

lemma dfs_recurse_goal_not_visited_if_terminated
    (g: WeightedDiGraph V E)
    (start : V)(priorState : base_search_state g start)
    (not_terminated : priorState.terminated = false)
    (invar_stack_visited : search_invar_stack_is_visited g start priorState):
    ∀ goal : V, (dfs_recurse g start goal priorState not_terminated).2 = false 
    ∧ goal ∉ priorState.visited
    → goal ∉ (dfs_recurse g start goal priorState not_terminated).1.visited := by
  intro goal ⟨ terminated_with_false, goal_not_visited ⟩ 
  have new_new := terminated_with_false

  apply dfs_empty_stack_if_returned_false_recurse at terminated_with_false
  · --unfold dfs_internal at terminated_with_false
    unfold dfs_recurse at terminated_with_false
    unfold search_recurse at terminated_with_false
    simp_all
    split at terminated_with_false
    · next step_returns_none =>
      unfold dfs_recurse
      unfold search_recurse
      simp_all
      apply dfs_recurse_goal_not_visited_if_terminated
      · apply dfs_step_keeps_stack_in_visited
        exact invar_stack_visited
      · constructor
        · unfold dfs_recurse at new_new
          unfold search_recurse at new_new
          simp_all
          exact new_new 
        · unfold dfs_step
          split
          · simp_all
          · split
            · simp_all
            · next l head tail composed head_not_goal =>
              simp_all
              unfold dfs_step_expand
              simp_all
              by_contra head_adj_goal
              have goal_is_now_on_stack : goal ∈ (dfs_step g start goal priorState).1.stack := by
                unfold dfs_step
                simp_all
                unfold dfs_step_expand
                simp_all
              apply dfs_recurse_if_goal_on_stack_it_remains at goal_is_now_on_stack
              · unfold dfs_recurse at goal_is_now_on_stack
                unfold search_prop_goal_on_stack at goal_is_now_on_stack              
                rw [terminated_with_false] at goal_is_now_on_stack
                simp_all only [List.not_mem_nil]
              · unfold dfs_step at step_returns_none ⊢ 
                simp_all
                unfold dfs_step_expand
                simp
      · unfold dfs_step at step_returns_none ⊢
        split
        · next prior_stack_empty => 
          rw [prior_stack_empty] at step_returns_none
          simp at step_returns_none
        · next head tail compose =>
          rw [compose] at step_returns_none
          simp_all
          split
          · simp_all
          · simp_all
            unfold dfs_step_expand
            simp
    · next step_returns_not_none =>
      unfold dfs_recurse
      unfold search_recurse
      simp_all
      unfold dfs_step at terminated_with_false ⊢
      by_cases stack_empty : priorState.stack = []
      · simp_all
      · apply List.length_pos_iff.mpr at stack_empty
        apply List.exists_cons_of_length_pos at stack_empty
        obtain ⟨head, tail, compose⟩ := stack_empty 
        simp_all
        split
        · simp_all
        · next head_not_goal =>
          simp_all
          unfold dfs_step_expand at terminated_with_false ⊢
          simp_all
          by_contra head_adj_goal
          have ⟨ all_adj_in_visi, tail_empty ⟩ := terminated_with_false 
          simp_all
termination_by base_search_state_termination_metric g start priorState
decreasing_by
  apply dfs_step_reduces_metric g start goal
  next h =>
  apply dfs_step_returns_none_means_not_terminated
  exact h



lemma dfs_not_visited_goal_if_returned_false
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    (dfs_internal g start goal).2 = false → goal ∉ (dfs_internal g start goal).1.visited := by
     intro terminated_with_not_goal_found
     unfold dfs_internal at terminated_with_not_goal_found ⊢ 
     apply dfs_recurse_goal_not_visited_if_terminated
     · apply search_invar_stack_is_visited_initial 
     · constructor
       · exact terminated_with_not_goal_found 
       · unfold dfs_initial_state
         simp
         by_contra goal_is_start
         unfold dfs_recurse at terminated_with_not_goal_found
         unfold search_recurse at terminated_with_not_goal_found
         unfold dfs_step at terminated_with_not_goal_found
         unfold dfs_initial_state at terminated_with_not_goal_found
         simp_all


def dfs [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V): Option (Path g start goal) :=

  let dfs_ret := dfs_internal g start goal
  let final_state :=dfs_ret.1
  let found_goal := dfs_ret.2

  if found_goal_true : found_goal = true then
    some (extract_path_to g start goal final_state
      (dfs_visited_goal_if_returned_true g start goal found_goal_true)
      (dfs_returns_with_mother_visited g start goal)
      (dfs_returns_with_mother_adjacent g start goal)
      (dfs_returns_with_mother_decreasing g start goal)).1
  else
    none


theorem dfs_is_sound (g: WeightedDiGraph V E) (start : V) (goal : V) :
    (Option.isSome (dfs g start goal) → (∃ x : (Path g start goal), x = x)) := by
  intro h -- Option.isSome true on some and false on none, x = x since we need a formula
  constructor -- since goal is existence
  rfl
  let w := Option.get (dfs g start goal) -- Option.get extracts value of returned some and fails otherwise
  apply w
  simp_all


theorem dfs_is_complete (g: WeightedDiGraph V E) (start : V) (goal : V) :
    ((∃ x : (Path g start goal), x = x) → Option.isSome (dfs g start goal)) := by
    -- or Option.isNone (dfs g start goal) → ∄ x (Path g start goal), x = x
      intro path_exists
      apply Exists.elim path_exists
      intro thePath a; clear a-- uninformativ x=X

      let final := dfs_internal g start goal
      let final_state := final.1
      
      have start_visited : search_invar_start_visited g start final_state :=
        dfs_returns_with_start_visited g start goal 
      have on_stack_or_all_nei_visited : search_invar_on_stack_or_all_neighbours_visited g start final_state:=
        dfs_returns_with_node_on_stack_or_all_neighbours_visited g start goal


      by_contra terminates_with_none
      simp at terminates_with_none

      have dfs_returned_false : (dfs_internal g start goal).2 = false := by
        unfold dfs at terminates_with_none
        simp at terminates_with_none
        exact terminates_with_none

      have final_stack_empty : final_state.stack = [] :=
        dfs_empty_stack_if_returned_false g start goal dfs_returned_false

      have goal_not_visited : goal ∉ final_state.visited :=
        dfs_not_visited_goal_if_returned_false g start goal dfs_returned_false

      obtain ⟨theWalk, nodupe ⟩ := thePath
      have goal_in_final := search_termination_with_empty_stack_implies_goal_visited g start goal start theWalk final_state start_visited final_stack_empty on_stack_or_all_nei_visited
      contradiction


theorem dfs_is_complete_inv (g: WeightedDiGraph V E) (start : V) (goal : V) :
    Option.isNone (dfs g start goal) → ¬ ∃ x : (Path g start goal), x = x := by
      intro optionIsNone
      by_contra pathExists
      have isSome := dfs_is_complete g start goal pathExists
      simp_all

