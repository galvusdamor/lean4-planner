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
      
      let new_mother_proof (v : new_visited): ↑v ≠ start → g.Adj (new_mother v) v :=
       fun not_start =>
        by
          unfold new_mother
          simp_all
          split
          · next prior_visited_v =>
            exact priorState.mother_proof ⟨↑v, prior_visited_v⟩ not_start
          · next not_prior_visited_v => 
            obtain ⟨ vv, v_new_visited ⟩ := v
            unfold new_visited at v_new_visited
            simp_all
            simp at v_new_visited
            simp_all
            unfold newly_visited at v_new_visited
            simp_all

      let new_order : V → Nat := fun v  =>
        if h: (v ∈ priorState.visited) then priorState.pathOrder v
        else if hh : (priorState.visited.card = 0) then 0
        --else 1 + maximum_path_order_of g priorState priorState.visited (by simp_all)
        else 1 + priorState.pathOrder stackHead
        -- priorState.stack.length
      
      base_search_state.mk new_visited new_order new_mother new_mother_proof new_stack false


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
        intro goal
        intro stack_is_visited_prior 
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
        intro y y_not_visited
        intro y_in_tail
        simp_all
      


lemma dfs_step_keeps_mother_in_visited 
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start):
    ∀ goal : V,
    search_invar_stack_is_visited g start priorState ∧ search_invar_mother_is_visited g start priorState →
      search_invar_mother_is_visited g start (dfs_step g start goal priorState).fst := by
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
    (start : V)(priorState : base_search_state g start):
    ∀ goal : V,
      search_invar_stack_is_visited g start priorState ∧
      search_invar_mother_is_visited g start priorState ∧
      search_invar_mother_decreasing_path_order g start priorState
      → search_invar_mother_decreasing_path_order g start (dfs_step g start goal priorState).fst := by
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


lemma dfs_step_keeps_on_stack_or_all_neighbours_visited
    (g: WeightedDiGraph V E)
    (start : V)(priorState : base_search_state g start):
    ∀ goal : V,
     search_invar_on_stack_or_all_neighbours_visited g start priorState
     → search_invar_on_stack_or_all_neighbours_visited g start 
          (dfs_step g start goal priorState).fst := by
        intro goal
        intro stack_or_neighbour_visited
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
        intro goal
        intro stack_is_visited_prior 
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
        intro ⟨ invar_stack_visited, invar_mother_visited, invar_mother_decreasing, invar_nei_visited, invar_start_visited⟩
        rw [← and_assoc]
        rw [← and_assoc]
        rw [← and_assoc]
        repeat constructor
        · apply dfs_step_keeps_stack_in_visited
          exact invar_stack_visited
        · apply dfs_step_keeps_mother_in_visited
          exact ⟨ invar_stack_visited, invar_mother_visited⟩ 
        · apply dfs_step_keeps_mother_ordered
          exact ⟨ invar_stack_visited, invar_mother_visited, invar_mother_decreasing ⟩ 
        · apply dfs_step_keeps_on_stack_or_all_neighbours_visited
          exact invar_nei_visited
        · apply dfs_step_keeps_start_in_visited
          exact invar_start_visited


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

def dfs_recurse [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    (priorState : base_search_state g start)
    (not_terminated : priorState.terminated = false):
    (base_search_state g start) × Bool :=
  let qq := dfs_step g start goal priorState
  let nextState := qq.fst
  let result := qq.snd
  if result_is_none : result = none then 
    let still_not_terminated : nextState.terminated = false := by
      unfold nextState
      unfold result at result_is_none
      unfold qq at result_is_none ⊢
      unfold dfs_step at result_is_none ⊢
      split
      · simp_all
      · next _ head tail compose =>
        simp_all
        split
        all_goals
          simp_all -- one goal vanishes
        unfold dfs_step_expand
        simp_all
    dfs_recurse g start goal nextState still_not_terminated
  else ⟨ nextState, result.get (by apply Option.isSome_iff_ne_none.mpr ; exact result_is_none) ⟩ 
termination_by (¬priorState.terminated, Fintype.card V - priorState.visited.card, priorState.stack.length, goal) -- must be a well-founded relation/measure
decreasing_by
  rw [Prod.lex_iff]
  apply (Classical.or_iff_not_imp_left).mpr
  simp_all
  rw [Prod.lex_iff]
  rw [Prod.lex_iff]
  simp_all
  constructor
  · simp_all only [qq, nextState]
  unfold nextState at still_not_terminated
  unfold qq at still_not_terminated
  apply termination_dfs_recurse
  rotate_right
  use goal
  simp_all


abbrev search_invar_over_step [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)(start : V)(goal : V)(invar : base_search_state g start → Prop) :=
      ∀ s : base_search_state g start, invar s → invar (dfs_step g start goal s).fst

lemma dfs_recurse_lift_invar
    (g: WeightedDiGraph V E)
    (start : V)(priorState : base_search_state g start)
    (not_terminated : priorState.terminated = false)
    (invar : base_search_state g start → Prop):
    ∀ (goal : V), invar priorState ∧ (search_invar_over_step g start goal invar)
     → invar (dfs_recurse g start goal priorState not_terminated).fst := by
      intro goal ⟨ invar_holds_initially, dfs_step_keeps_invar ⟩ 
      unfold dfs_recurse
      simp
      unfold search_invar_over_step at dfs_step_keeps_invar
      have h := dfs_step_keeps_invar priorState invar_holds_initially 

      split
      · next step_returns_none =>
        have still_not_terminated : (dfs_step g start goal priorState).1.terminated = false := by
          unfold dfs_step at ⊢ step_returns_none
          simp_all
          split
          · next stack_empty =>
            rw [stack_empty] at step_returns_none
            simp_all
          · simp_all
            split
            · next head tail compose is_goal =>
              simp_all
            · unfold dfs_step_expand
              simp_all
        exact dfs_recurse_lift_invar g start (dfs_step g start goal priorState).1 still_not_terminated invar goal ⟨ h, dfs_step_keeps_invar ⟩
      · simp
        exact h
termination_by (¬priorState.terminated, Fintype.card V - priorState.visited.card, priorState.stack.length) -- must be a well-founded relation/measure
decreasing_by
  rw [Prod.lex_iff]
  apply (Classical.or_iff_not_imp_left).mpr
  simp_all
  rw [Prod.lex_iff]
  apply termination_dfs_recurse
  rotate_right
  use goal
  simp_all

lemma dfs_step_returning_non_did_not_terminate(g: WeightedDiGraph V E)
    (start : V) (goal : V) (priorState : base_search_state g start):
    (dfs_step g start goal priorState).2 = none → 
    (dfs_step g start goal priorState).1.terminated = false := by
      intro gg
      unfold dfs_step at gg ⊢
      split
      · simp_all
      · simp_all
        split
        · simp_all
        · simp_all
          unfold dfs_step_expand
          simp_all


lemma dfs_recurse_goal_visited_if_terminated
    (g: WeightedDiGraph V E)
    (start : V)(priorState : base_search_state g start)
    (not_terminated : priorState.terminated = false)
    (invar_stack_visited : search_invar_stack_is_visited g start priorState):
    ∀ goal : V, (dfs_recurse g start goal priorState not_terminated).2 = true →
     goal ∈ (dfs_recurse g start goal priorState not_terminated).1.visited := by
   intro goal terminated_with_true
   unfold dfs_recurse at terminated_with_true ⊢ 
   simp_all
   split
   · simp_all
     apply dfs_recurse_goal_visited_if_terminated
     · apply dfs_step_keeps_stack_in_visited
       exact invar_stack_visited
     · exact terminated_with_true
   · next step_did_terminate =>
     simp_all
     unfold dfs_step at terminated_with_true ⊢
     split
     · next l stack_empty =>
       simp_all
     · next l head tail stack_not_empty =>
       simp_all
       split
       · next head_is_goal =>
         simp_all
       · next head_is_not_goal =>
         simp_all
         unfold dfs_step_expand
         simp_all
         by_cases goal_was_visited : goal ∈ priorState.visited
         · left; exact goal_was_visited
         · right
           constructor
           · unfold dfs_step at step_did_terminate
             simp_all
           · exact goal_was_visited
termination_by (¬priorState.terminated, Fintype.card V - priorState.visited.card, priorState.stack.length) -- must be a well-founded relation/measure
decreasing_by
  rw [Prod.lex_iff]
  apply (Classical.or_iff_not_imp_left).mpr
  simp_all
  rw [Prod.lex_iff]
  next a b c d e f gg =>
  clear b c d e f
  have did_terminate_before : (dfs_step g start goal priorState).1.terminated = false := by
    apply dfs_step_returning_non_did_not_terminate
    exact gg
  constructor
  · exact did_terminate_before
  apply termination_dfs_recurse
  rotate_right
  use goal
  simp_all

lemma dfs_recurse_stack_empty_if_terminated
    (g: WeightedDiGraph V E)
    (start : V)
    (priorState : base_search_state g start)
    (not_terminated : priorState.terminated = false)
    (invar_stack_visited : search_invar_stack_is_visited g start priorState):
    ∀ goal : V, (dfs_recurse g start goal priorState not_terminated).2 = false →
     (dfs_recurse g start goal priorState not_terminated).1.stack = [] := by
   intro goal terminated_with_false 
   unfold dfs_recurse at terminated_with_false ⊢ 
   simp_all
   split
   · next step_did_not_terminate =>
     simp_all
     apply dfs_recurse_stack_empty_if_terminated
     · apply dfs_step_keeps_stack_in_visited
       exact invar_stack_visited
     · simp_all
   · next step_did_terminate =>
     simp [step_did_terminate] at terminated_with_false
     unfold dfs_step at terminated_with_false
     by_cases prior_stack_empty : priorState.stack = []
     · simp [prior_stack_empty] at terminated_with_false
       simp_all
       unfold dfs_step
       simp_all
     · simp_all
       by_cases stack_composed : ∃ a : V, ∃ l : List V, priorState.stack = a :: l
       · obtain ⟨a,l,stack_composition⟩ := stack_composed 
         simp_all
         split at terminated_with_false
         · simp_all
         · next head_not_goal =>
           simp_all
           unfold dfs_step at step_did_terminate
           simp_all
       · have stackEmpty: priorState.stack = [] := by
           apply List.eq_nil_of_length_eq_zero
           unfold List.length
           split
           · rfl
           · next l head tail compose=>
             simp_all
         simp_all
termination_by (¬priorState.terminated, Fintype.card V - priorState.visited.card, priorState.stack.length) -- must be a well-founded relation/measure
decreasing_by
  rw [Prod.lex_iff]
  apply (Classical.or_iff_not_imp_left).mpr
  simp_all
  rw [Prod.lex_iff]
  next a b c d e f gg =>
  clear b c d e f
  have did_terminate_before : (dfs_step g start goal priorState).1.terminated = false := by
    apply dfs_step_returning_non_did_not_terminate
    exact gg
  constructor
  · exact did_terminate_before
  apply termination_dfs_recurse
  rotate_right
  use goal
  simp_all

lemma dfs_recurse_if_goal_on_stack_return_true
    (g: WeightedDiGraph V E)
    (start : V) (priorState : base_search_state g start)
    (not_terminated : priorState.terminated = false)
    (invar_stack_visited : search_invar_stack_is_visited g start priorState):
    ∀ goal : V, goal ∈ priorState.stack
      → (dfs_recurse g start goal priorState not_terminated).2 = true := by
  intro goal goal_on_stack
  unfold dfs_recurse
  simp
  split
  · apply dfs_recurse_if_goal_on_stack_return_true
    · apply dfs_step_keeps_stack_in_visited
      exact invar_stack_visited
    · next step_returned_none =>
      unfold dfs_step at step_returned_none ⊢ 
      split
      · next l emptyStack =>
        simp_all
      · next l head tail stackCompose =>
        simp_all
        split
        · simp_all
        · next head_not_goal =>
          simp_all
          have goal_not_head : goal ≠ head := by
            intro a
            apply head_not_goal
            exact a.symm
          simp at goal_not_head; clear head_not_goal
          apply (Classical.or_iff_not_imp_left).mp at goal_on_stack
          apply goal_on_stack at goal_not_head
          unfold dfs_step_expand
          simp_all
  · next h =>
    simp_all
    unfold dfs_step
    by_cases prior_state_non_empty: priorState.stack ≠ []
    · simp_all
      apply List.length_pos_iff.mpr at prior_state_non_empty
      apply List.length_pos_iff_exists_cons.mp at prior_state_non_empty
      obtain ⟨head,tail,compose⟩ := prior_state_non_empty
      simp_all
      split
      all_goals
        simp_all
    · simp_all
termination_by (¬priorState.terminated, Fintype.card V - priorState.visited.card, priorState.stack.length) -- must be a well-founded relation/measure
decreasing_by
  rw [Prod.lex_iff]
  apply (Classical.or_iff_not_imp_left).mpr
  simp_all
  rw [Prod.lex_iff]
  next a b c d e f gg =>
  clear b c d e f
  have did_terminate_before : (dfs_step g start goal priorState).1.terminated = false := by
    apply dfs_step_returning_non_did_not_terminate
    exact gg
  constructor
  · exact did_terminate_before
  apply termination_dfs_recurse
  rotate_right
  use goal
  simp_all


lemma dfs_recurse_goal_not_visited_if_terminated
    (g: WeightedDiGraph V E)
    (start : V)(priorState : base_search_state g start)
    (not_terminated : priorState.terminated = false)
    (invar_stack_visited : search_invar_stack_is_visited g start priorState):
    ∀ goal : V, (dfs_recurse g start goal priorState not_terminated).2 = false 
    ∧ goal ∉ priorState.visited
    → goal ∉ (dfs_recurse g start goal priorState not_terminated).1.visited := by
  intro goal
  intro ⟨ terminated_with_false, goal_not_visited ⟩ 
  have new_new := terminated_with_false
  apply dfs_recurse_stack_empty_if_terminated at terminated_with_false
  · unfold dfs_recurse at terminated_with_false
    simp_all
    split at terminated_with_false
    · next step_returns_none =>
      unfold dfs_recurse
      simp_all
      apply dfs_recurse_goal_not_visited_if_terminated
      · apply dfs_step_keeps_stack_in_visited
        exact invar_stack_visited
      · constructor
        · unfold dfs_recurse at new_new
          simp_all
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
              apply dfs_recurse_if_goal_on_stack_return_true at goal_is_now_on_stack
              unfold dfs_recurse at new_new
              simp_all
              · unfold dfs_step
                simp_all
                unfold dfs_step_expand
                simp_all
              · apply dfs_step_keeps_stack_in_visited
                exact invar_stack_visited
    · unfold dfs_recurse
      simp_all
      unfold dfs_step at terminated_with_false ⊢
      split
      · simp_all
      · simp_all
        split
        · simp_all
        · simp_all
          unfold dfs_step_expand at terminated_with_false ⊢
          simp_all
          next l head tail step_did_not_return_none stackCompose head_not_goal =>
          by_contra head_adj_goal
          have ⟨ all_adj_in_visi, tail_empty ⟩ := terminated_with_false 
          simp_all
  · exact invar_stack_visited
termination_by (¬priorState.terminated, Fintype.card V - priorState.visited.card, priorState.stack.length) -- must be a well-founded relation/measure
decreasing_by
  rw [Prod.lex_iff]
  apply (Classical.or_iff_not_imp_left).mpr
  simp_all
  rw [Prod.lex_iff]
  next a b c d e f gg =>
  clear b c d e f
  have did_terminate_before : (dfs_step g start goal priorState).1.terminated = false := by
    apply dfs_step_returning_non_did_not_terminate
    exact gg
  constructor
  · exact did_terminate_before
  apply termination_dfs_recurse
  rotate_right
  use goal
  simp_all


--------------------------------------------------------------------------------------------------
-- initial configuration of the DFS
def dfs_initial_state [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V) :
    base_search_state g start :=
  let initialVisited : Finset V := ⟨ {start},  by simp ⟩ 
  let initialMother : initialVisited → V := fun x => start 
  let initialMotherProof (v : initialVisited): ↑v ≠ start → g.Adj (initialMother v) v := by
    intro v_noit_start
    obtain ⟨ vv, v_in_initial⟩ := v
    simp_all
    unfold initialVisited at v_in_initial 
    simp at v_in_initial 
    contradiction

  let initialPathOrder : V → Nat := fun x => 0 
  let initialStack : List V := [start]
  base_search_state.mk initialVisited initialPathOrder initialMother initialMotherProof initialStack false


----- Proofs that the initial state of the DFS satisfies the invariants
lemma search_invar_stack_is_visited_initial 
    (g: WeightedDiGraph V E) (start : V) (goal : V) :
      search_invar_stack_is_visited g start (dfs_initial_state g start goal) := by 
      unfold search_invar_stack_is_visited
      unfold dfs_initial_state
      simp


lemma search_invar_mother_is_visited_initial 
    (g: WeightedDiGraph V E) (start : V) (goal : V) :
      search_invar_mother_is_visited g start (dfs_initial_state g start goal) := by 
      unfold search_invar_mother_is_visited
      unfold dfs_initial_state
      simp

lemma search_invar_mother_decreasing_path_order_initial
    (g: WeightedDiGraph V E) (start : V) (goal : V) :
      search_invar_mother_decreasing_path_order g start (dfs_initial_state g start goal) := by 
      unfold search_invar_mother_decreasing_path_order  
      unfold dfs_initial_state
      simp

lemma search_invar_on_stack_or_all_neighbours_visited_initial
    (g: WeightedDiGraph V E) (start : V) (goal : V) :
      search_invar_on_stack_or_all_neighbours_visited g start (dfs_initial_state g start goal) := by 
      unfold search_invar_on_stack_or_all_neighbours_visited  
      unfold dfs_initial_state
      simp

lemma search_invar_start_visited_initial
    (g: WeightedDiGraph V E) (start : V) (goal : V) :
      search_invar_start_visited g start (dfs_initial_state g start goal) := by 
      unfold search_invar_start_visited  
      unfold dfs_initial_state
      simp

lemma dfs_initial_state_is_not_termianted (g: WeightedDiGraph V E) (start : V) (goal : V) :
  (dfs_initial_state g start goal).terminated = false := by
    unfold dfs_initial_state
    simp

lemma dfs_initial_state_all_basic_invars
    (g: WeightedDiGraph V E) (start : V) (goal : V) :
    search_invar_all_basic g start (dfs_initial_state g start goal) := by
      unfold search_invar_all_basic 
      rw [← and_assoc]
      rw [← and_assoc]
      rw [← and_assoc]
      repeat constructor
      ·  apply search_invar_stack_is_visited_initial
      ·  apply search_invar_mother_is_visited_initial
      ·  apply search_invar_mother_decreasing_path_order_initial
      ·  apply search_invar_on_stack_or_all_neighbours_visited_initial
      ·  apply search_invar_start_visited_initial


----------------- the actual DFS: create the initial search state and then recurse

def dfs_internal[ FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V): (base_search_state g start) × Bool :=
  (dfs_recurse g start goal (dfs_initial_state g start goal) (dfs_initial_state_is_not_termianted g start goal))



lemma dfs_returns_correct_results 
    (g: WeightedDiGraph V E) (start : V) (goal : V) (final : base_search_state g start):
    final = (dfs_internal g start goal).1 →
      search_invar_all_basic g start final
    ∧ ((dfs_internal g start goal).2 = true → goal ∈ final.visited)
    ∧ ((dfs_internal g start goal).2 = false → goal ∉ final.visited ∧ final.stack = []) := by
    
    intro s_is_final

    let startState : base_search_state g start := dfs_initial_state g start goal
    let proof : startState.terminated = false := dfs_initial_state_is_not_termianted g start goal
    rw [s_is_final]
    clear s_is_final final
    let final := (dfs_internal g start goal).1

    constructor
    · unfold dfs_internal
      apply dfs_recurse_lift_invar g start startState proof (search_invar_all_basic g start)
      constructor
      · unfold startState
        apply dfs_initial_state_all_basic_invars
      · unfold search_invar_over_step
        intro s
        intro cond
        apply dfs_step_keeps_all_basic_invars
        exact cond
    -- prove the the properties for the two termination cases
    constructor
    · intro terminated_with_goal_found
      apply dfs_recurse_goal_visited_if_terminated
      apply search_invar_stack_is_visited_initial
      unfold dfs_internal at terminated_with_goal_found
      exact terminated_with_goal_found
    · intro terminated_with_goal_not_found
      repeat constructor
      · apply dfs_recurse_goal_not_visited_if_terminated
        apply search_invar_stack_is_visited_initial
        constructor
        · unfold dfs_internal at terminated_with_goal_not_found
          simp_all
        · unfold dfs_initial_state
          simp_all
          by_contra goal_is_start
          unfold dfs_internal at terminated_with_goal_not_found
          simp_all
          unfold dfs_recurse at terminated_with_goal_not_found
          simp_all
          unfold dfs_initial_state at terminated_with_goal_not_found
          unfold dfs_step at terminated_with_goal_not_found
          simp_all
      · apply dfs_recurse_stack_empty_if_terminated
        apply search_invar_stack_is_visited_initial
        unfold dfs_internal at terminated_with_goal_not_found
        exact terminated_with_goal_not_found

def dfs [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V): Option (Path g start goal) :=

  let dfs_ret := dfs_internal g start goal
  let final_state :=dfs_ret.1
  let found_goal := dfs_ret.2

  if found_goal_true : found_goal = true then
    have correct_result := dfs_returns_correct_results g start goal final_state (by
      unfold final_state 
      unfold dfs_ret
      rfl)

    have mother_invar : search_invar_mother_is_visited g start final_state := by
      have inv := correct_result.1
      unfold search_invar_all_basic at inv
      exact inv.2.1
    have decreasing_invar : search_invar_mother_decreasing_path_order g start final_state := by
      have inv := correct_result.1
      unfold search_invar_all_basic at inv
      exact inv.2.2.1

    some (extract_path_to g start goal final_state (correct_result.2.1 found_goal_true) mother_invar decreasing_invar).1
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


lemma my_induction (g: WeightedDiGraph V E) (start : V) (goal : V) (f : V) 
  (theWalk : Walk g f goal)
  (final_state : base_search_state g start)
  (f_visited : f ∈ final_state.visited)
  (final_stack_empty : final_state.stack = [])
  (on_stack_or_all_nei_visited : ∀ a ∈ final_state.visited, ∀ (y : V), g.Adj a y → y ∈ final_state.visited): goal ∈ final_state.visited := by
    cases theWalk
    · exact f_visited
    · next nextNode adj rest_walk =>
      apply my_induction g start goal nextNode rest_walk
      · apply on_stack_or_all_nei_visited f
        · exact f_visited
        · exact adj
      · exact final_stack_empty
      · exact on_stack_or_all_nei_visited


theorem dfs_is_complete (g: WeightedDiGraph V E) (start : V) (goal : V) :
    ((∃ x : (Path g start goal), x = x) → Option.isSome (dfs g start goal)) := by
    -- or Option.isNone (dfs g start goal) → ∄ x (Path g start goal), x = x
      intro path_exists
      apply Exists.elim path_exists
      intro thePath
      intro a; clear a-- uninformativ x=X
      
      by_contra terminates_with_none
      simp at terminates_with_none

      let final := dfs_internal g start goal
      let final_state := final.1

      have xx := dfs_returns_correct_results g start goal final_state (by
        unfold final_state 
        unfold final
        rfl)

      have h := xx.2.2
      unfold search_invar_all_basic at xx
      have start_visited := xx.1.2.2.2.2
      unfold search_invar_start_visited at start_visited
      have on_stack_or_all_nei_visited := xx.1.2.2.2.1
      clear xx
      unfold dfs at terminates_with_none
      simp at terminates_with_none
      apply h at terminates_with_none
      clear h
      simp_all
      obtain ⟨goal_not_visited, final_stack_empty⟩ := terminates_with_none

      obtain ⟨theWalk, nodupe ⟩ := thePath
      have goal_in_final := my_induction g start goal start theWalk final_state start_visited final_stack_empty on_stack_or_all_nei_visited
      contradiction


theorem dfs_is_complete_inv (g: WeightedDiGraph V E) (start : V) (goal : V) :
    Option.isNone (dfs g start goal) → ¬ ∃ x : (Path g start goal), x = x := by
      intro optionIsNone
      by_contra pathExists
      have isSome := dfs_is_complete g start goal pathExists
      simp_all




def dfs_step_does_not_terminate [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V) : 
      search_step_does_not_terminate g start goal (state_type := base_search_state g start) (dfs_step g start) := by
      unfold search_step_does_not_terminate
      simp_all
      intro prior_state
      intro result_is_none 
      unfold dfs_step at result_is_none ⊢
      split
      · simp_all
      · next _ head tail compose =>
        simp_all
        split
        all_goals
          simp_all -- one goal vanishes
        simp [has_base_search_state.to_base_state]
        unfold dfs_step_expand
        simp_all


def dfs_termination_metric[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V) (state : base_search_state g start) : ℕ × ℕ := 
    (Fintype.card V - state.visited.card, state.stack.length)


def dfs_decreasing_metric_proof[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V):
      ∀ s : base_search_state g start,
      search_state_not_terminated g start (dfs_step g start goal s).1 → 
      Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2) (dfs_termination_metric g start goal (dfs_step g start goal s).1) (dfs_termination_metric g start goal s)
      :=
  by
    intro prior_state not_terminated
    unfold dfs_termination_metric
    apply Prod.lex_def.mpr
    simp_all
    apply termination_dfs_recurse g start goal
    constructor
    · rfl
    · apply not_terminated 


def def_rec[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    (priorState : base_search_state g start)
    (not_terminated : priorState.terminated = false):
    (base_search_state g start) × Bool :=
      search_recurse  g start goal priorState (by
        unfold search_state_not_terminated; apply not_terminated) (dfs_step g start) (by
          unfold search_step_does_not_terminate
          apply dfs_step_does_not_terminate
        ) (dfs_termination_metric g start goal) (dfs_decreasing_metric_proof g start goal)

