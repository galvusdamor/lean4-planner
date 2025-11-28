import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Empty
import Mathlib.Data.List.MinMax

import Graphlib.Lists
import Graphlib.FinEnum
import Graphlib.Basic
import Graphlib.SearchState
import Graphlib.SearchAlgorithm
import Graphlib.SearchStep

set_option trace.split.failure true
--set_option diagnostics true

-- def local global variable for a graph
variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V] [DecidableEq E]
variable {g : WeightedDiGraph V E}

-----------------------------------------------------------------------
------ BFS implementation and proof ------

def bfs_step_expand[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    (base_search_state g) :=
      let newly_visited : Finset V := (Finset.univ).filterMap
        (λ v => if @decide (g.Adj stackHead v) (g.instDecAdj stackHead v) ∧ v ∉ priorState.visited
                  then some v
                  else none)
        (by intro a a' b a_1 a_2; simp_all) -- filter neighbors to expand the visited list
      
      let vList : List V := (FinEnum.toList (Finset.univ : Finset V))
      let newly_visited_list : List V :=
        vList.filterMap (λ v => if v ∈ newly_visited then some v else none)
      let new_visited : Finset V := priorState.visited ∪ newly_visited
      let new_stack : List V := stackTail ++ newly_visited_list -- add neighbors at end of stack
     
      let new_mother : new_visited → V := fun ⟨v, hv⟩  =>
        if h: (v ∈ priorState.visited) then priorState.mother ⟨ v, by exact h⟩
        else stackHead
      
      let new_order : V → Nat := fun v  =>
        if h: (v ∈ priorState.visited) then priorState.pathOrder v
        else if hh : (priorState.visited.card = 0) then 0
        --else 1 + maximum_path_order_of g priorState priorState.visited (by simp_all)
        else 1 + priorState.pathOrder stackHead
        -- priorState.stack.length
      
      base_search_state.mk new_visited new_order new_mother new_stack


lemma bfs_expand_newly_added_are_adjacent 
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    ∀ x : V, x ∉ priorState.visited ∧ x ∉ stackTail ∧
      x ∈ (bfs_step_expand g priorState stackHead stackTail).stack →  
      g.Adj stackHead x := by
    intro x ⟨x_not_visi, ⟨ x_not_on_stack_before, x_on_stack_after ⟩  ⟩
    unfold bfs_step_expand at x_on_stack_after
    simp_all


lemma bfs_expand_keeps_stack_in_visited 
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    search_invar_stack_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧ (∀ x : V, x ∉ priorState.visited → x ∉ stackTail) →
      search_invar_stack_is_visited (bfs_step_expand g priorState stackHead stackTail) := by
      intro ⟨ stack_is_visited_prior, stackhead_visited, x_not_in_stack_tail⟩ 
      unfold search_invar_stack_is_visited
      intro x x_now_on_stack
      unfold bfs_step_expand
      simp_all
      by_cases x_was_visited : x ∈ priorState.visited
      · left
        exact x_was_visited
      · right
        apply And.intro
        · apply (bfs_expand_newly_added_are_adjacent priorState stackHead stackTail)
          simp_all
        · exact x_was_visited


lemma bfs_expand_keeps_mother_in_visited 
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_visited priorState ∧ stackHead ∈ priorState.visited → search_invar_mother_is_visited (bfs_step_expand g priorState stackHead stackTail) := by
      intro mother_is_visited_prior
      unfold search_invar_mother_is_visited
      intro x
      simp_all
      unfold bfs_step_expand
      simp_all
      by_cases x_is_already_visited : ↑x ∈ priorState.visited
      all_goals
        simp_all

lemma bfs_expand_keeps_mother_is_adjacent
    (start : V)
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_adjacent start priorState → search_invar_mother_is_adjacent start (bfs_step_expand g priorState stackHead stackTail) := by
      intro mother_is_adjacent_prior
      unfold search_invar_mother_is_adjacent
      intro x
      simp_all
      intro x_not_start
      unfold bfs_step_expand
      simp_all
      split
      · simp_all
      · next x_not_prior_visited => 
        obtain ⟨ xx, x_in_new_visited ⟩ := x
        unfold bfs_step_expand at x_in_new_visited
        simp at x_in_new_visited
        simp_all

lemma bfs_expand_keeps_mother_ordered 
    (start : V)
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧ 
      search_invar_mother_decreasing_path_order start priorState
      → search_invar_mother_decreasing_path_order start
          (bfs_step_expand g priorState stackHead stackTail)
          := by
    intro ⟨mother_is_visited, stack_head_visited_prior,mother_decreasing_prior⟩  
    unfold search_invar_mother_decreasing_path_order
    intro a a_not_stat
    unfold bfs_step_expand
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

lemma bfs_expand_keeps_on_stack_or_all_neighbours_visited
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
     search_invar_on_stack_or_all_neighbours_visited priorState
     ∧ priorState.stack = (stackHead :: stackTail)
     → search_invar_on_stack_or_all_neighbours_visited  
          (bfs_step_expand g priorState stackHead stackTail)
          := by
      intro ⟨ invar_holds_on_prior_state, stack_composition ⟩ 
      unfold search_invar_on_stack_or_all_neighbours_visited
      intro ⟨ x, x_now_on_stack⟩
      by_cases x_not_stack_head : x ≠ stackHead
      · by_cases x_was_not_in_stack_tail_: x ∈ stackTail
        · left
          unfold bfs_step_expand
          simp_all
        · by_cases x_not_visited : x ∉ priorState.visited
          · left
            unfold bfs_step_expand
            unfold bfs_step_expand at x_now_on_stack
            simp at x_now_on_stack
            simp_all
          · simp_all -- x was visited before and is not on the stack any more
            right
            intro y x_adj_y
            unfold bfs_step_expand
            simp_all
            left
            have x_invar := invar_holds_on_prior_state x
            simp_all
      · simp_all
        right
        intro y x_adj_y
        unfold bfs_step_expand
        simp_all
        by_cases h : y ∈ priorState.visited
        · left; exact h
        · right; exact h

lemma bfs_expand_keeps_start_visited
    (start : V)
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
     search_invar_start_visited start priorState →
     search_invar_start_visited start (bfs_step_expand g priorState stackHead stackTail)
          := by
      intro pre_invar
      unfold bfs_step_expand
      unfold search_invar_start_visited 
      simp_all

lemma bfs_expand_visited_subset (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    priorState.visited ⊆ (bfs_step_expand g priorState stackHead stackTail).visited := by
    unfold bfs_step_expand
    simp_all

lemma bfs_expand_keeps_goal_on_stack :
    base_invar_carries_over_expand (state_type := base_search_state g) goal (bfs_step_expand g) (search_prop_goal_on_stack (g:=g) goal):= by
    unfold base_invar_carries_over_expand
    intro s head tail ⟨ goal_prior_on_stack, head_not_goal, compose⟩ 
    change search_prop_goal_on_stack goal (bfs_step_expand g s head tail)
    unfold bfs_step_expand
    unfold search_prop_goal_on_stack at ⊢ goal_prior_on_stack
    simp_all 
    cases  goal_prior_on_stack
    all_goals
      simp_all

lemma bfs_expand_goal_becomes_visited_puts_it_on_stack
  (goal : V)
  : 
  goal_becomes_visited_puts_it_on_stack (g:=g) goal (bfs_step_expand g):= by
    unfold goal_becomes_visited_puts_it_on_stack
    intro s head tail ⟨ a,b,c,d⟩ 
    change search_prop_goal_on_stack goal (bfs_step_expand g s head tail)
    have bb : goal ∈ (bfs_step_expand g s head tail).visited := b
    clear b
    unfold bfs_step_expand at bb ⊢
    unfold search_prop_goal_on_stack
    simp_all
    cases bb
    · contradiction
    · next h => left; exact h


lemma visited_is_smaller_than_V (state : base_search_state g): state.visited.card ≤ Fintype.card V := by
    apply Finset.card_le_univ
  

lemma bfs_expand_visited_increases
    (priorState : base_search_state g)
    (head : V)
    (tail : List V):
      (bfs_step_expand g priorState head tail).visited.card ≥ priorState.visited.card := by
    change priorState.visited.card ≤ (bfs_step_expand g priorState head tail).visited.card
    apply Finset.card_le_card
    apply bfs_expand_visited_subset


lemma bfs_expand_keeps_base_invars:
  base_invar_carries_over_expand goal (bfs_step_expand g) (search_invar_all_basic (g:=g) start) := by
  unfold base_invar_carries_over_expand
  unfold search_invar_all_basic
  intro s head tail ⟨ ⟨ i1,i2,i3,i4,i5,i6⟩ , head_not_goal, compose⟩ 
  have head_is_visited : head ∈ s.visited := by
    apply i1
    rw [compose]
    simp
  repeat rw [← and_assoc]
  repeat constructor
  · apply bfs_expand_keeps_stack_in_visited
    constructor
    · exact i1
    · constructor
      · exact head_is_visited 
      · intro x x_not_visited
        by_contra x_in_tail
        have x_on_stack : x ∈ (has_base_search_state.to_base_state (g:=g) s).stack := by
          rw [compose]
          simp_all
        apply i1 at x_on_stack
        contradiction 
  · apply bfs_expand_keeps_mother_in_visited
    constructor
    · exact i2
    · exact head_is_visited
  · apply bfs_expand_keeps_mother_is_adjacent
    exact i3
  · apply bfs_expand_keeps_mother_ordered
    constructor
    · exact i2
    · constructor
      · exact head_is_visited
      · exact i4
  · apply bfs_expand_keeps_on_stack_or_all_neighbours_visited
    constructor
    · exact i5 
    · exact compose 
  · apply bfs_expand_keeps_start_visited
    exact i6

--------------------------------------------------------------------------------------------------
-- main recursion loop 

lemma termination_bfs_recurse
    (priorState : base_search_state g)
    (nextState : base_search_state g)
    (head : V)
    (tail : List V)
    (compose : priorState.stack = head :: tail):
    (nextState = (bfs_step_expand g priorState head tail))
    → ((Fintype.card V - nextState.visited.card < Fintype.card V - priorState.visited.card
        ∨ (Fintype.card V - nextState.visited.card = Fintype.card V - priorState.visited.card ∧ nextState.stack.length < priorState.stack.length)) ):= by
  intro nextStateDef
  apply (Classical.or_iff_not_imp_left).mpr
  intro visited_not_decreasing
  simp_all
  have same_visited : (bfs_step_expand g priorState head tail).visited.card = priorState.visited.card := by
    have k2 : (bfs_step_expand g priorState head tail).visited.card ≤ Fintype.card V := by
      apply visited_is_smaller_than_V 
    have k3 : (bfs_step_expand g priorState head tail).visited.card ≥ priorState.visited.card := by
      apply bfs_expand_visited_increases 
    omega
  have visited_eq : priorState.visited = (bfs_step_expand g priorState head tail).visited := by
    ext a
    constructor
    · apply Finset.mem_of_subset
      apply bfs_expand_visited_subset 
    apply finsetLemma
    · apply bfs_expand_visited_subset 
    exact same_visited

  constructor
  · omega
  · unfold bfs_step_expand
    simp_all
    simp [Nat.add_comm]
    intro a head_adj_a
    rw [visited_eq]
    unfold bfs_step_expand
    simp_all
    classical
    by_cases h : a ∈ (bfs_step_expand g priorState head tail).visited
    · left; exact h
    · right; exact h

lemma bfs_expand_metric_reduction : termination_proof_for_expand (g:=g) goal (bfs_step_expand g) base_search_state_termination_metric := by
    unfold termination_proof_for_expand
    unfold base_search_state_termination_metric
    simp
    intro s head tail head_not_goal stack_not_empty 
    apply termination_bfs_recurse
    · exact stack_not_empty
    · rfl 


----------------- the actual bfs: create the initial search state and then recurse

def bfs(g: WeightedDiGraph V E) (start : V) (goal : V): Option (Path g start goal) :=
  let start_state := base_search_state_initial start
  have h : has_base_search_state.to_base_state (g:=g) start_state = base_search_state_initial start:= by simp_all only [start_state]; rfl

  search_exe_with_stack_step (g:=g) (start := start) (goal:=goal) (start_state:=start_state) (termination_metric := base_search_state_termination_metric) (bfs_step_expand g) bfs_expand_metric_reduction bfs_expand_keeps_base_invars h 



theorem bfs_is_sound (g: WeightedDiGraph V E) (start : V) (goal : V) :
    (Option.isSome (bfs g start goal) → (∃ x : (Path g start goal), x = x)) := by
  apply search_with_stack_step_is_sound
  · apply bfs_expand_metric_reduction
  · apply bfs_expand_keeps_base_invars
  · rfl



theorem bfs_is_complete (g: WeightedDiGraph V E) (start : V) (goal : V):
    ((∃ x : (Path g start goal), x = x) → Option.isSome (bfs g start goal)) := by
  apply search_with_stack_step_is_complete
  · apply bfs_expand_metric_reduction
  · apply bfs_expand_keeps_base_invars
  · rfl
  · apply bfs_expand_keeps_goal_on_stack
  · apply bfs_expand_goal_becomes_visited_puts_it_on_stack

