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
------ DFS implementation and proof ------

def dfs_step_expand[FinEnum V] [DecidableEq E] [DecidableEq V]
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
      let new_stack : List V := newly_visited_list ++ stackTail -- add neighbors in front to stack
     
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


lemma dfs_expand_newly_added_are_adjacent 
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    ∀ x : V, x ∉ priorState.visited ∧ x ∉ stackTail ∧
      x ∈ (dfs_step_expand g priorState stackHead stackTail).stack →  
      g.Adj stackHead x := by
    intro x ⟨x_not_visi, ⟨ x_not_on_stack_before, x_on_stack_after ⟩  ⟩
    unfold dfs_step_expand at x_on_stack_after
    simp_all


lemma dfs_expand_keeps_stack_in_visited 
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    search_invar_stack_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧ (∀ x : V, x ∉ priorState.visited → x ∉ stackTail) →
      search_invar_stack_is_visited (dfs_step_expand g priorState stackHead stackTail) := by
      intro ⟨ stack_is_visited_prior, stackhead_visited, x_not_in_stack_tail⟩ 
      unfold search_invar_stack_is_visited
      intro x x_now_on_stack
      unfold dfs_step_expand
      simp_all
      by_cases x_was_visited : x ∈ priorState.visited
      · left
        exact x_was_visited
      · right
        apply And.intro
        · apply (dfs_expand_newly_added_are_adjacent priorState stackHead stackTail)
          simp_all
        · exact x_was_visited


lemma dfs_expand_keeps_mother_in_visited 
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_visited priorState ∧ stackHead ∈ priorState.visited → search_invar_mother_is_visited (dfs_step_expand g priorState stackHead stackTail) := by
      intro mother_is_visited_prior
      unfold search_invar_mother_is_visited
      intro x
      simp_all
      unfold dfs_step_expand
      simp_all
      by_cases x_is_already_visited : ↑x ∈ priorState.visited
      all_goals
        simp_all

lemma dfs_expand_keeps_mother_is_adjacent
    (start : V)
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_adjacent start priorState → search_invar_mother_is_adjacent start (dfs_step_expand g priorState stackHead stackTail) := by
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

lemma dfs_expand_keeps_mother_ordered 
    (start : V)
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    search_invar_mother_is_visited priorState ∧
      stackHead ∈ priorState.visited ∧ 
      search_invar_mother_decreasing_path_order start priorState
      → search_invar_mother_decreasing_path_order start
          (dfs_step_expand g priorState stackHead stackTail)
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

lemma dfs_expand_keeps_on_stack_or_all_neighbours_visited
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
     search_invar_on_stack_or_all_neighbours_visited priorState
     ∧ priorState.stack = (stackHead :: stackTail)
     → search_invar_on_stack_or_all_neighbours_visited  
          (dfs_step_expand g priorState stackHead stackTail)
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
    (start : V)
    (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
     search_invar_start_visited start priorState →
     search_invar_start_visited start (dfs_step_expand g priorState stackHead stackTail)
          := by
      intro pre_invar
      unfold dfs_step_expand
      unfold search_invar_start_visited 
      simp_all

lemma dfs_expand_visited_subset (priorState : base_search_state g)
    (stackHead : V)
    (stackTail : List V):
    priorState.visited ⊆ (dfs_step_expand g priorState stackHead stackTail).visited := by
    unfold dfs_step_expand
    simp_all



---------------------------------------------------------------------------------------
-- run one step of the DFS. Mostly case distinction and running expansion if necessary
def dfs_step 
    (g: WeightedDiGraph V E) (goal : V)
    (priorState : base_search_state g) :
    (base_search_state g) × (Option Bool) :=
  match priorState.stack with
    | [] => (priorState, some false) -- goal not found
    | (s :: xs) =>
      if s = goal then (priorState, some true)
      else (dfs_step_expand g priorState s xs, none)


lemma dfs_step_visited_subset (goal : V) (priorState : base_search_state g) :
    priorState.visited ⊆ (dfs_step g goal priorState).1.visited := by
    unfold dfs_step
    split
    · simp_all
    split
    · simp_all
    unfold dfs_step_expand
    simp_all

lemma dfs_step_visited_is_smaller_than_V 
    (goal : V) (priorState : base_search_state g):
    (dfs_step g goal priorState).1.visited.card ≤ Fintype.card V := by
    apply Finset.card_le_univ

lemma visited_is_smaller_than_V (state : base_search_state g): state.visited.card ≤ Fintype.card V := by
    apply Finset.card_le_univ
  
lemma dfs_step_visited_increases
    (goal : V) (priorState : base_search_state g):
      (dfs_step g goal priorState).1.visited.card ≥ priorState.visited.card := by
    change priorState.visited.card ≤ (dfs_step g goal priorState).1.visited.card
    apply Finset.card_le_card
    apply dfs_step_visited_subset


lemma dfs_expand_visited_increases
    (priorState : base_search_state g)
    (head : V)
    (tail : List V):
      (dfs_step_expand g priorState head tail).visited.card ≥ priorState.visited.card := by
    change priorState.visited.card ≤ (dfs_step_expand g priorState head tail).visited.card
    apply Finset.card_le_card
    apply dfs_expand_visited_subset


lemma dfs_expand_keeps_base_invars:
  base_invar_carries_over_expand goal (dfs_step_expand g) (search_invar_all_basic (g:=g) start) := by
  unfold base_invar_carries_over_expand
  unfold search_invar_all_basic
  intro s head tail ⟨ ⟨ i1,i2,i3,i4,i5,i6⟩ , head_not_goal, compose⟩ 
  have head_is_visited : head ∈ s.visited := by
    apply i1
    rw [compose]
    simp
  repeat rw [← and_assoc]
  repeat constructor
  · apply dfs_expand_keeps_stack_in_visited
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
  · apply dfs_expand_keeps_mother_in_visited
    constructor
    · exact i2
    · exact head_is_visited
  · apply dfs_expand_keeps_mother_is_adjacent
    exact i3
  · apply dfs_expand_keeps_mother_ordered
    constructor
    · exact i2
    · constructor
      · exact head_is_visited
      · exact i4
  · apply dfs_expand_keeps_on_stack_or_all_neighbours_visited
    constructor
    · exact i5 
    · exact compose 
  · apply dfs_expand_keeps_start_visited
    exact i6


----------
-- the step also keeps the invariants
lemma dfs_step_keeps_stack_in_visited 
    (priorState : base_search_state g):
    ∀ goal : V, search_invar_stack_is_visited priorState →
      search_invar_stack_is_visited (dfs_step g goal priorState).fst := by
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
    (priorState : base_search_state g):
    ∀ goal : V,
    search_invar_stack_is_visited priorState ∧ search_invar_mother_is_visited priorState →
      search_invar_mother_is_visited (dfs_step g goal priorState).fst := by
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
    (start : V) (priorState : base_search_state g):
    ∀ goal : V,
    search_invar_mother_is_adjacent start priorState →
      search_invar_mother_is_adjacent start (dfs_step g goal priorState).fst := by
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
    (start : V)(priorState : base_search_state g):
    ∀ goal : V,
      search_invar_stack_is_visited priorState ∧
      search_invar_mother_is_visited priorState ∧
      search_invar_mother_decreasing_path_order start priorState
      → search_invar_mother_decreasing_path_order start (dfs_step g goal priorState).fst := by
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
    (priorState : base_search_state g):
    ∀ goal : V, search_invar_on_stack_or_all_neighbours_visited priorState
     → search_invar_on_stack_or_all_neighbours_visited 
          (dfs_step g goal priorState).fst := by
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
    (start : V) (priorState : base_search_state g):
    ∀ goal : V,
    search_invar_start_visited start priorState →
      search_invar_start_visited start (dfs_step g goal priorState).fst := by
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
    (start : V) (priorState : base_search_state g):
     search_invar_all_basic start priorState →
     search_invar_all_basic start (dfs_step g goal priorState).fst
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
    (goal : V) (priorState : base_search_state g):
    search_prop_goal_on_stack goal priorState → 
    search_prop_goal_on_stack goal (dfs_step g goal priorState).fst := by
      unfold search_prop_goal_on_stack
      intro goal_prior_on_stack
      unfold dfs_step
      split
      · simp_all
      · simp_all
        split
        · simp_all
        · unfold dfs_step_expand
          simp_all
          cases goal_prior_on_stack
          all_goals
            simp_all

lemma dfs_step_goal_on_stack_if_terminated (priorState : base_search_state g):
    ∀ goal : V, (dfs_step g goal priorState).2 = true →
     goal ∈ (dfs_step g goal priorState).1.stack := by
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

lemma dfs_step_stack_empty_if_terminated_without_goal (priorState : base_search_state g):
    ∀ goal : V, (dfs_step g goal priorState).2 = false →
     (dfs_step g goal priorState).1.stack  = [] := by
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


lemma dfs_step_goal_becomes_visited_it_is_on_stack:
  goal ∉ priorState.visited ∧ goal ∈ (dfs_step g goal priorState).1.visited 
  → search_prop_goal_on_stack goal (dfs_step g goal priorState).1
    := by 
  intro ⟨ goal_was_not_visited, goal_now_visited ⟩  
  unfold dfs_step at goal_now_visited ⊢
  split
  · simp_all
  · simp_all
    split
    · simp_all
    · unfold search_prop_goal_on_stack
      simp_all
      unfold dfs_step_expand at goal_now_visited ⊢
      simp_all

lemma dfs_step_terminates_when_goal_stack_head:
  (∃ tail : List V, priorState.stack = goal :: tail) → (dfs_step g goal priorState).2 = some true := by
  intro ⟨ tail, goal_head ⟩ 
  unfold dfs_step
  simp_all


--------------------------------------------------------------------------------------------------
-- main recursion loop 

lemma termination_dfs_recurse2
    (priorState : base_search_state g)
    (nextState : base_search_state g)
    (head : V)
    (tail : List V)
    (compose : priorState.stack = head :: tail):
    (nextState = (dfs_step_expand g priorState head tail))
    → ((Fintype.card V - nextState.visited.card < Fintype.card V - priorState.visited.card
        ∨ (Fintype.card V - nextState.visited.card = Fintype.card V - priorState.visited.card ∧ nextState.stack.length < priorState.stack.length)) ):= by
  intro nextStateDef
  apply (Classical.or_iff_not_imp_left).mpr
  intro visited_not_decreasing
  simp_all
  have same_visited : (dfs_step_expand g priorState head tail).visited.card = priorState.visited.card := by
    have k2 : (dfs_step_expand g priorState head tail).visited.card ≤ Fintype.card V := by
      apply visited_is_smaller_than_V 
    have k3 : (dfs_step_expand g priorState head tail).visited.card ≥ priorState.visited.card := by
      apply dfs_expand_visited_increases 
    omega
  have visited_eq : priorState.visited = (dfs_step_expand g priorState head tail).visited := by
    ext a
    constructor
    · apply Finset.mem_of_subset
      apply dfs_expand_visited_subset 
    apply finsetLemma
    · apply dfs_expand_visited_subset 
    exact same_visited

  constructor
  · omega
  · unfold dfs_step_expand
    simp_all
    simp [Nat.add_comm]
    intro a head_adj_a
    rw [visited_eq]
    unfold dfs_step_expand
    simp_all
    classical
    by_cases h : a ∈ (dfs_step_expand g priorState head tail).visited
    · left; exact h
    · right; exact h


lemma termination_dfs_recurse 
    (goal : V)
    (priorState : base_search_state g)
    (priorStackNotEmpty : priorState.stack ≠ [])
    (stack_head_not_goal : priorState.stack.head priorStackNotEmpty ≠ goal)
    (nextState : base_search_state g):
    (nextState = (dfs_step g goal priorState).1)
    → ((Fintype.card V - nextState.visited.card < Fintype.card V - priorState.visited.card
        ∨ (Fintype.card V - nextState.visited.card = Fintype.card V - priorState.visited.card ∧ nextState.stack.length < priorState.stack.length)) ):= by
  intro nextStateDef
  apply (Classical.or_iff_not_imp_left).mpr
  intro visited_not_decreasing
  simp_all
  have same_visited : (dfs_step g goal priorState).1.visited.card = priorState.visited.card := by
    have k2 : (dfs_step g goal priorState).1.visited.card ≤ Fintype.card V :=
      dfs_step_visited_is_smaller_than_V goal priorState
    have k3 : (dfs_step g goal priorState).1.visited.card ≥ priorState.visited.card := 
      dfs_step_visited_increases goal priorState
    omega
  have visited_eq : priorState.visited = (dfs_step g goal priorState).1.visited := by
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
    · simp_all
    split -- style is bad!
    · simp_all 
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
    by_cases h : a ∈ (dfs_step g goal priorState).1.visited
    · left; exact h
    · right; exact h

lemma dfs_step_reduces_metric (goal : V):
    ∀ s : base_search_state g,
        (dfs_step g goal s).2 = none → 
        Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2)
        (base_search_state_termination_metric (dfs_step g goal s).1) (base_search_state_termination_metric s) := by
    intro state did_not_terminate
    unfold base_search_state_termination_metric
    apply Prod.lex_def.mpr
    simp

    have h : state.stack ≠ [] := by
      unfold dfs_step at did_not_terminate
      split at did_not_terminate
      · simp_all
      · simp_all

    apply termination_dfs_recurse
    rotate_left
    rotate_left
    · use goal
    rotate_right
    · rfl
    · exact h 
    · unfold dfs_step at did_not_terminate
      simp_all
      split at did_not_terminate
      · simp_all
      · simp_all
        split at did_not_terminate
        · simp_all
        · simp_all

----------------- the actual DFS: create the initial search state and then recurse

def dfs(g: WeightedDiGraph V E) (start : V) (goal : V): Option (Path g start goal) :=
  let start_state := base_search_state_initial start
  have h : has_base_search_state.to_base_state start_state = base_search_state_initial start:= by simp_all only [start_state]; rfl

  search_exe (start := start) (goal:=goal) (start_state:=start_state) (search_step:=dfs_step g) (termination_metric := base_search_state_termination_metric) (dfs_step_reduces_metric goal) h (by apply dfs_step_keeps_all_basic_invars) (by apply dfs_step_goal_on_stack_if_terminated)


theorem dfs_is_sound (g: WeightedDiGraph V E) (start : V) (goal : V) :
    (Option.isSome (dfs g start goal) → (∃ x : (Path g start goal), x = x)) := by
  apply search_is_sound
  · rfl
  · apply dfs_step_keeps_all_basic_invars
  · apply dfs_step_goal_on_stack_if_terminated

theorem dfs_is_complete (g: WeightedDiGraph V E) (start : V) (goal : V):
    ((∃ x : (Path g start goal), x = x) → Option.isSome (dfs g start goal)) := by
  apply search_is_complete
  · rfl
  · apply dfs_step_keeps_all_basic_invars
  · apply dfs_step_goal_on_stack_if_terminated
  · intro s
    apply dfs_step_stack_empty_if_terminated_without_goal
  · apply dfs_step_keeps_goal_on_stack
  · apply dfs_step_goal_becomes_visited_it_is_on_stack 
  · apply dfs_step_terminates_when_goal_stack_head 


--------

def dfs2(g: WeightedDiGraph V E) (start : V) (goal : V): Option (Path g start goal) :=
  let start_state := base_search_state_initial start
  have h : has_base_search_state.to_base_state (g:=g) start_state = base_search_state_initial start:= by simp_all only [start_state]; rfl

  have reduces : termination_proof_for_expand goal (dfs_step_expand g) base_search_state_termination_metric := by
    unfold termination_proof_for_expand
    unfold base_search_state_termination_metric
    simp
    intro s head tail head_not_goal stack_not_empty 
    apply termination_dfs_recurse2
    · exact stack_not_empty
    · rfl 

  search_exe_with_stack_step (g:=g) (start := start) (goal:=goal) (start_state:=start_state) (termination_metric := base_search_state_termination_metric) (dfs_step_expand g) reduces dfs_expand_keeps_base_invars h 


