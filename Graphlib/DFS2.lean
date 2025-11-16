import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Empty
import Mathlib.Data.List.MinMax

import Graphlib.Lists
import Graphlib.FinEnum
import Graphlib.Basic


#eval false < true

set_option trace.split.failure true
--set_option diagnostics true

-- def local global variable for a graph
variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V] [DecidableEq E]
variable (G : WeightedDiGraph V E)



-----------------------------------------------------------------------
------ Search state of the DFS and its invariants
structure dfs_state [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) where
    visited : Finset V
    pathOrder : V → Nat 
    mother : visited → V
    stack : List V
    terminated : Bool

abbrev dfs_invar_stack_is_visited [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (s : dfs_state g):=
      ∀ x : V, x ∈ s.stack → x ∈ s.visited

abbrev dfs_invar_mother_is_visited [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (s : dfs_state g):=
      ∀ x : s.visited, s.mother x ∈ s.visited

abbrev dfs_invar_mother_decreasing_path_order [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : dfs_state g) :=
      ∀ x : s.visited, ↑x ≠ start → s.pathOrder (s.mother x) < s.pathOrder x 

abbrev dfs_invar_on_stack_or_all_neighbours_visited [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (s : dfs_state g):=
      ∀ x : s.visited, ↑x ∈ s.stack ∨ ∀ y : V, (g.Adj x y) → y ∈ s.visited

abbrev dfs_invar_goal_not_visited [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (goal : V) (s : dfs_state g) :=
      goal ∉ s.visited

def extract_path_to [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V) (search_state : dfs_state g)
    (goal_reached : goal ∈ search_state.visited)
    (mother_invar : dfs_invar_mother_is_visited g search_state)
    (decreasing_invar : dfs_invar_mother_decreasing_path_order g start search_state):
      Path g start goal := by sorry




-----------------------------------------------------------------------
------ DFS implementation and proof ------

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
        --else 1 + maximum_path_order_of g priorState priorState.visited (by simp_all)
        else 1 + priorState.pathOrder stackHead
        -- priorState.stack.length
      
      dfs_state.mk new_visited new_order new_mother new_stack false


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
    (start : V)
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
        apply le_refl
        --apply maximum_path_order_is_le
        --simp_all

lemma dfs_expand_keeps_on_stack_or_all_neighbours_visited
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g)
    (stackHead : V)
    (stackTail : List V):
     dfs_invar_on_stack_or_all_neighbours_visited g priorState
     ∧ priorState.stack = (stackHead :: stackTail)
     → dfs_invar_on_stack_or_all_neighbours_visited g
          (dfs_step_expand g priorState stackHead stackTail)
          := by
      intro ⟨ invar_holds_on_prior_state, stack_composition ⟩ 
      unfold dfs_invar_on_stack_or_all_neighbours_visited
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

---------------------------------------------------------------------------------------
-- run one step of the DFS. Mostly case distinction and running expansion if necessary
def dfs_step [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (goal : V)
    (priorState : dfs_state g) :
    (dfs_state g) × (Option Bool) :=
  match priorState.stack with
    | [] => ({priorState with terminated := true} , some false) -- goal not found
    | (s :: xs) =>
    if s = goal then ({priorState with terminated := true}, some true)
    else
      (dfs_step_expand g priorState s xs, none)


lemma dfs_step_visited_subset [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (goal : V)
    (priorState : dfs_state g) :
    priorState.visited ⊆ (dfs_step g goal priorState).1.visited := by
    unfold dfs_step
    split
    · simp_all
    split
    · simp_all
    unfold dfs_step_expand
    simp_all

lemma dfs_step_visited_is_smaller_than_V [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (goal : V)
    (priorState : dfs_state g):
   (dfs_step g goal priorState).1.visited.card ≤ Fintype.card V := by
    apply Finset.card_le_univ
  
lemma dfs_step_visited_increases[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (goal : V)
    (priorState : dfs_state g):
      (dfs_step g goal priorState).1.visited.card ≥ priorState.visited.card := by
    change   priorState.visited.card ≤ (dfs_step g goal priorState).1.visited.card
    apply Finset.card_le_card
    apply dfs_step_visited_subset

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
        · unfold dfs_invar_stack_is_visited
          simp_all
        next _ head tail head_tail_compose =>
        split
        · unfold dfs_invar_stack_is_visited
          simp_all
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

lemma dfs_step_keeps_stack_and_mother_correct
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g):
    ∀ goal : V,
      dfs_invar_stack_is_visited g priorState ∧
      dfs_invar_mother_is_visited g priorState ∧
      dfs_invar_mother_decreasing_path_order g start priorState
      → 
      dfs_invar_stack_is_visited g (dfs_step g goal priorState).fst ∧
      dfs_invar_mother_is_visited g (dfs_step g goal priorState).fst ∧
      dfs_invar_mother_decreasing_path_order g start (dfs_step g goal priorState).fst := by
        intro goal
        intro ⟨ stack_visited, mother_visited, mother_decreasing⟩
        constructor
        · apply dfs_step_keeps_stack_in_visited
          exact stack_visited
        · constructor
          · apply dfs_step_keeps_mother_in_visited
            exact ⟨ stack_visited, mother_visited ⟩ 
          · apply dfs_step_keeps_mother_ordered
            exact ⟨ stack_visited, mother_visited, mother_decreasing⟩ 


lemma dfs_step_keeps_on_stack_or_all_neighbours_visited
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g):
    ∀ goal : V,
     dfs_invar_on_stack_or_all_neighbours_visited g priorState
     → dfs_invar_on_stack_or_all_neighbours_visited g
          (dfs_step g goal priorState).fst := by
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



--------------------------------------------------------------------------------------------------
-- main recursion loop 


lemma termination_dfs_recurse [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (goal : V)
    (priorState : dfs_state g)
    (nextState : dfs_state g):
    (nextState = (dfs_step g goal priorState).1) ∧ (nextState.terminated = false)
    → ((Fintype.card V - nextState.visited.card < Fintype.card V - priorState.visited.card
        ∨ (Fintype.card V - nextState.visited.card = Fintype.card V - priorState.visited.card ∧ nextState.stack.length < priorState.stack.length)) ):= by
  intro ⟨ nextStateDef, still_not_terminated ⟩
  apply (Classical.or_iff_not_imp_left).mpr
  intro visited_not_decreasing
  simp_all
  have same_visited : (dfs_step g goal priorState).1.visited.card = priorState.visited.card := by
    have k2 : (dfs_step g goal priorState).1.visited.card ≤ Fintype.card V :=
      dfs_step_visited_is_smaller_than_V g goal priorState
    have k3 : (dfs_step g goal priorState).1.visited.card ≥ priorState.visited.card := 
      dfs_step_visited_increases g goal priorState
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
    by_cases h : a ∈ (dfs_step g goal priorState).1.visited
    · left; exact h
    · right; exact h

def dfs_recurse [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (goal : V)
    (priorState : dfs_state g)
    (not_terminated : priorState.terminated = false):
    (dfs_state g) × Bool :=
  let qq := dfs_step g goal priorState
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
    dfs_recurse g goal nextState still_not_terminated
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


abbrev dfs_invar_over_step [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (invar : V → dfs_state g → Prop) (start : V) (goal : V) :=
      ∀ s : dfs_state g, invar start s → invar start (dfs_step g goal s).fst

lemma dfs_recurse_lift_invar
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g)
    (not_terminated : priorState.terminated = false)
    (invar : V → dfs_state g → Prop):
    ∀ (start goal : V), invar start priorState ∧ (dfs_invar_over_step g invar start goal)
     → invar start (dfs_recurse g goal priorState not_terminated).fst := by
      intro start goal ⟨ invar_holds_initially, dfs_step_keeps_invar ⟩ 
      unfold dfs_recurse
      simp
      unfold dfs_invar_over_step at dfs_step_keeps_invar
      have h := dfs_step_keeps_invar priorState invar_holds_initially 

      split
      · next step_returns_none =>
        have still_not_terminated : (dfs_step g goal priorState).1.terminated = false := by
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
        exact dfs_recurse_lift_invar g (dfs_step g goal priorState).1 still_not_terminated invar start goal ⟨ h, dfs_step_keeps_invar ⟩
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
    (priorState : dfs_state g):
    (dfs_step g goal priorState).2 = none → 
    (dfs_step g goal priorState).1.terminated = false := by
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
    (priorState : dfs_state g)
    (not_terminated : priorState.terminated = false)
    (invar_stack_visited : dfs_invar_stack_is_visited g priorState):
    ∀ goal : V, (dfs_recurse g goal priorState not_terminated).2 = true →
     goal ∈ (dfs_recurse g goal priorState not_terminated).1.visited := by
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
  have did_terminate_before : (dfs_step g goal priorState).1.terminated = false := by
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
    (priorState : dfs_state g)
    (not_terminated : priorState.terminated = false)
    (invar_stack_visited : dfs_invar_stack_is_visited g priorState):
    ∀ goal : V, (dfs_recurse g goal priorState not_terminated).2 = false →
     (dfs_recurse g goal priorState not_terminated).1.stack = [] := by
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
  have did_terminate_before : (dfs_step g goal priorState).1.terminated = false := by
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
    (priorState : dfs_state g)
    (not_terminated : priorState.terminated = false)
    (invar_stack_visited : dfs_invar_stack_is_visited g priorState):
    ∀ goal : V, goal ∈ priorState.stack
      → (dfs_recurse g goal priorState not_terminated).2 = true := by
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
  have did_terminate_before : (dfs_step g goal priorState).1.terminated = false := by
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
    (priorState : dfs_state g)
    (not_terminated : priorState.terminated = false)
    (invar_stack_visited : dfs_invar_stack_is_visited g priorState):
    ∀ goal : V, (dfs_recurse g goal priorState not_terminated).2 = false 
    ∧ goal ∉ priorState.visited
    → goal ∉ (dfs_recurse g goal priorState not_terminated).1.visited := by
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
              have goal_is_now_on_stack : goal ∈ (dfs_step g goal priorState).1.stack := by
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
  have did_terminate_before : (dfs_step g goal priorState).1.terminated = false := by
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
    dfs_state g :=
  let initialVisited : Finset V := ⟨ {start},  by simp ⟩ 
  let initialMother : initialVisited → V := fun x => start 
  let initialPathOrder : V → Nat := fun x => 0 
  let initialStack : List V := [start]
  dfs_state.mk initialVisited initialPathOrder initialMother initialStack false


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

theorem dfs_invar_on_stack_or_all_neighbours_visited_initial
    (g: WeightedDiGraph V E) (start : V) (goal : V) :
      dfs_invar_on_stack_or_all_neighbours_visited g (dfs_initial_state g start goal) := by 
      unfold dfs_invar_on_stack_or_all_neighbours_visited  
      unfold dfs_initial_state
      simp


----------------- the actual DFS: create the initial search state and then recurse
def dfs[ FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V): Bool :=
  let startState : dfs_state g := dfs_initial_state g start goal
  let proof : startState.terminated = false := by
    unfold startState
    unfold dfs_initial_state
    simp

  (dfs_recurse g goal startState proof).2


lemma dfs_returns_correct_results [ FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V):
    ∃ s : dfs_state g, dfs_invar_on_stack_or_all_neighbours_visited g s 
    ∧ dfs_invar_stack_is_visited g s
    ∧ dfs_invar_mother_is_visited g s
    ∧ dfs_invar_mother_decreasing_path_order g start s
    ∧ ((dfs g start goal) = true → goal ∈ s.visited)
    ∧ ((dfs g start goal) = false → goal ∉ s.visited ∧ s.stack = []) := by
    let startState : dfs_state g := dfs_initial_state g start goal
    let proof : startState.terminated = false := by
      unfold startState
      unfold dfs_initial_state
      simp

    let final := (dfs_recurse g goal startState proof).1
    use final
    constructor
    · apply dfs_recurse_lift_invar g startState proof (fun _ => dfs_invar_on_stack_or_all_neighbours_visited g) start goal
      constructor
      apply dfs_invar_on_stack_or_all_neighbours_visited_initial
      unfold dfs_invar_over_step
      intro s
      apply dfs_step_keeps_on_stack_or_all_neighbours_visited g s
    rw [← and_assoc]
    rw [← and_assoc]
    
    have three_invars : dfs_invar_stack_is_visited g final ∧ dfs_invar_mother_is_visited g final ∧ dfs_invar_mother_decreasing_path_order g start final := by
      apply dfs_recurse_lift_invar g startState proof (fun st s =>
        dfs_invar_stack_is_visited g s ∧ dfs_invar_mother_is_visited g s ∧ dfs_invar_mother_decreasing_path_order g st s) start goal
      constructor
      · rw [← and_assoc]
        repeat constructor
        apply dfs_invar_stack_is_visited_initial
        apply dfs_invar_mother_is_visited_initial
        apply dfs_invar_mother_decreasing_path_order_initial
      unfold dfs_invar_over_step
      intro s
      apply dfs_step_keeps_stack_and_mother_correct

    constructor
    · apply and_assoc.mpr
      exact three_invars
    -- prove the the properties for the two termination cases
    constructor
    · intro terminated_with_goal_found
      unfold final
      apply dfs_recurse_goal_visited_if_terminated
      apply dfs_invar_stack_is_visited_initial
      unfold dfs at terminated_with_goal_found
      simp at terminated_with_goal_found
      exact terminated_with_goal_found
    · intro terminated_with_goal_not_found
      constructor
      · apply dfs_recurse_goal_not_visited_if_terminated
        apply dfs_invar_stack_is_visited_initial
        constructor
        · unfold dfs at terminated_with_goal_not_found
          simp_all
          unfold startState
          simp_all
        · unfold startState
          unfold dfs_initial_state
          simp_all
          by_contra goal_is_start
          unfold dfs at terminated_with_goal_not_found
          simp_all
          unfold dfs_recurse at terminated_with_goal_not_found
          simp_all
          unfold dfs_initial_state at terminated_with_goal_not_found
          unfold dfs_step at terminated_with_goal_not_found
          simp_all
      · apply dfs_recurse_stack_empty_if_terminated
        apply dfs_invar_stack_is_visited_initial
        unfold dfs at terminated_with_goal_not_found
        simp at terminated_with_goal_not_found
        exact terminated_with_goal_not_found


lemma dfs_recurse_lift_invar
    (g: WeightedDiGraph V E)
    (priorState : dfs_state g)
    (not_terminated : priorState.terminated = false)
    (invar : V → dfs_state g → Bool):
    ∀ (start goal : V), invar start priorState ∧ (dfs_invar_over_step g invar start goal)
     → invar start (dfs_recurse g goal priorState not_terminated).fst := by





















