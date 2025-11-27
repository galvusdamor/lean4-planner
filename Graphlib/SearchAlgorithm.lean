import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Empty
import Mathlib.Data.List.MinMax

import Graphlib.Lists
import Graphlib.FinEnum
import Graphlib.Basic
import Graphlib.SearchState

set_option trace.split.failure true
--set_option diagnostics true

-- def local global variable for a graph
variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V] [DecidableEq E]
variable {g : WeightedDiGraph V E}


def extract_path_to (start : V) (goal : V) (search_state : base_search_state g)
    (goal_reached : goal ∈ search_state.visited)
    (mother_invar : search_invar_mother_is_visited search_state)
    (mother_invar_adj : search_invar_mother_is_adjacent start search_state)
    (decreasing_invar : search_invar_mother_decreasing_path_order start search_state):
      Σ' (p : Path g start goal), (∀ v ∈ support g p.walk, search_state.pathOrder v ≤ search_state.pathOrder goal):= 
      if start_is_goal : goal = start then
        let emptyW : Walk g start goal := start_is_goal ▸ Walk.nil
        let emptyP : Path g start goal := Path.mk emptyW (by
          simp [emptyW]
          unfold support
          split
          · next u u' x w rest u_adj_v walk_is_cons => 
            simp_all
            subst start_is_goal
            simp_all only [reduceCtorEq] 
          · simp
        )

        have order : ∀ v ∈ support g emptyP.walk, search_state.pathOrder v ≤ search_state.pathOrder goal := by
          intro a a_in_support
          unfold emptyP at a_in_support
          unfold emptyW at a_in_support
          unfold support at a_in_support
          simp_all
          subst start_is_goal
          simp_all only [List.mem_cons, List.not_mem_nil, or_false, le_refl]

        ⟨ emptyP, order ⟩ 
      else
        let goal_predecessor : V := search_state.mother ⟨ goal, goal_reached ⟩
        let ⟨ path_start_pre, order_proof ⟩ := -- : Path g start goal_predecessor :=
          extract_path_to start goal_predecessor search_state (by apply mother_invar) mother_invar mother_invar_adj decreasing_invar 
        let pre_adj_goal : g.Adj goal_predecessor goal := mother_invar_adj ⟨ goal , goal_reached ⟩ start_is_goal
        let goal_not_visited : goal ∉ support g path_start_pre.walk := by
          by_contra goal_is_in_support
          have h := order_proof goal goal_is_in_support
          unfold goal_predecessor at h
          unfold search_invar_mother_decreasing_path_order at decreasing_invar
          have h' := decreasing_invar ⟨ goal, goal_reached⟩ 
          clear mother_invar decreasing_invar
          simp_all
          omega

        let goal_path : Path g start goal := extend_path g path_start_pre pre_adj_goal goal_not_visited

        let new_order_proof : ∀ v ∈ support g goal_path.walk, search_state.pathOrder v ≤ search_state.pathOrder goal := by
          intro a a_in_support
          unfold goal_path at a_in_support
          rw [extend_path_extends_support] at a_in_support
          simp_all
          apply a_in_support.elim
          · intro a_in_old_path
            apply le_trans 
            · apply order_proof
              exact a_in_old_path
            · unfold goal_predecessor
              apply le_of_lt
              exact decreasing_invar ⟨ goal,goal_reached ⟩ start_is_goal
          · simp_all

        ⟨ goal_path, new_order_proof ⟩ 

termination_by search_state.pathOrder goal
decreasing_by
  simp_all only [Subtype.forall, ne_eq, not_false_eq_true]


theorem search_termination_with_empty_stack_implies_goal_visited (start : V) (goal : V) (f : V) 
  (theWalk : Walk g f goal)
  (final_state : base_search_state g)
  (f_visited : f ∈ final_state.visited)
  (final_stack_empty : final_state.stack = [])
  (on_stack_or_all_nei_visited : search_invar_on_stack_or_all_neighbours_visited final_state): goal ∈ final_state.visited := by
    cases theWalk
    · exact f_visited
    · next nextNode adj rest_walk =>
      apply search_termination_with_empty_stack_implies_goal_visited start goal nextNode rest_walk
      · unfold search_invar_on_stack_or_all_neighbours_visited at on_stack_or_all_nei_visited
        rw [final_stack_empty] at on_stack_or_all_nei_visited
        simp at on_stack_or_all_nei_visited
        apply on_stack_or_all_nei_visited f f_visited nextNode adj
      · exact final_stack_empty
      · exact on_stack_or_all_nei_visited


-- the graph should be an explicit parameter here
abbrev search_step_function (g : WeightedDiGraph V E)
    {state_type : Type} [has_base_search_state g state_type] :=
      V → state_type → state_type × (Option Bool)

def base_search_state_termination_metric 
    (s : base_search_state g): ℕ × ℕ :=
    (Fintype.card V - s.visited.card, s.stack.length)

abbrev termination_metric_decreasing_proof
   {state_type : Type} [has_base_search_state g state_type]
  (goal : V)
  (search_step : search_step_function (state_type := state_type) (g:=g))
  (termination_metric : state_type → ℕ × ℕ) :=
    ∀ s : state_type, (search_step goal s).2 = none → 
        Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2)
        (termination_metric (search_step goal s).1) (termination_metric s)



------------------------------------------------------------------------------------------
-- Search Recurse
------------------
def search_recurse {state_type : Type} [has_base_search_state g state_type]
    (goal : V)
    (priorState : state_type)
    (search_step : search_step_function g)
    (termination_metric : state_type → ℕ × ℕ)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric):
    state_type × Bool :=
  let qq := search_step goal priorState
  let nextState := qq.fst
  let result : Option Bool := qq.snd
  if result_is_none : result = none then 
    
    --let still_not_terminated : nextState.terminated = false := by
    search_recurse goal nextState search_step termination_metric decreasing_proof
  else ⟨ nextState, result.get (by apply Option.isSome_iff_ne_none.mpr ; exact result_is_none) ⟩ 
termination_by termination_metric priorState
decreasing_by
  apply decreasing_proof
  apply result_is_none



lemma search_recurse_obtain_termination_property {state_type : Type} [has_base_search_state g state_type]
    (goal : V)
    (priorState : state_type)
    (search_step : search_step_function g)
    (termination_metric : state_type → ℕ × ℕ)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
        -- until here all necessary for calling the search_recurse
    (terminated_with : Bool) -- recursion terminated with
    (property_after_termination : state_type → Prop):
      (∀ s : state_type, (search_step goal s).2 = some terminated_with → property_after_termination (search_step goal s).1)
    → 
      ((search_recurse goal priorState search_step termination_metric decreasing_proof).2 = terminated_with → 
      property_after_termination (search_recurse goal priorState search_step termination_metric decreasing_proof).1):= by
      intro step_termination_property recursion_terminated_with
      unfold search_recurse at recursion_terminated_with ⊢
      simp_all
      split
      · next search_step_returned_none =>
        -- recursive case
        simp_all
        apply search_recurse_obtain_termination_property goal
        rotate_right
        · use terminated_with -- recursion termiantes with same result
        · apply step_termination_property
        · apply recursion_terminated_with
      · next h =>
        simp_all
        apply step_termination_property
        apply Option.eq_some_iff_get_eq.mpr
        simp_all
        apply Option.isSome_iff_ne_none.mpr
        exact h
termination_by termination_metric priorState
decreasing_by
  next step_returned_none =>
  apply decreasing_proof
  apply step_returned_none



lemma search_recurse_obtain_base_termination_property {state_type : Type} [has_base_search_state g state_type]
    (goal : V)
    (priorState : state_type)
    (search_step : search_step_function g)
    (termination_metric : state_type → ℕ × ℕ)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
        -- until here all necessary for calling the search_recurse
    (terminated_with : Bool) -- recursion terminated with
    (property_after_termination : base_search_state g → Prop):
      (∀ s : state_type, (search_step goal s).2 = some terminated_with → property_after_termination (has_base_search_state.to_base_state (search_step goal s).1))
    → 
      ((search_recurse goal priorState search_step termination_metric decreasing_proof).2 = terminated_with → 
      property_after_termination (has_base_search_state.to_base_state (search_recurse goal priorState search_step termination_metric decreasing_proof).1)) := by
      intro property_holds
      apply search_recurse_obtain_termination_property goal priorState search_step termination_metric decreasing_proof (terminated_with) (fun x => property_after_termination (has_base_search_state.to_base_state x)) -- fun needed to tell lean what the "invariant" is it should apply
      exact property_holds


abbrev invar_carries_over_step 
    {state_type : Type} [has_base_search_state g state_type]
    (goal : V)
    (search_step : search_step_function (g:=g) (state_type := state_type))
    (invar : state_type → Prop) :=
      ∀ s : state_type, invar s → invar (search_step goal s).fst


abbrev base_invar_carries_over_step 
    {state_type : Type} [has_base_search_state g state_type]
    (goal : V)
    (search_step : search_step_function (g:=g) (state_type := state_type))
    (invar : base_search_state g → Prop) :=
      ∀ s : state_type, invar (has_base_search_state.to_base_state s) → invar (has_base_search_state.to_base_state (search_step goal s).fst)



lemma search_recurse_lift_invariant {state_type : Type} [has_base_search_state g state_type]
    (goal : V)
    (priorState : state_type)
    (search_step : search_step_function (g:=g))
    (termination_metric : state_type → ℕ × ℕ)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
        -- until here all necessary for calling the search_recurse
    (invar : state_type → Prop):
      invar priorState ∧ (invar_carries_over_step goal search_step invar)
         → invar (search_recurse goal priorState search_step termination_metric decreasing_proof).fst:= by
      intro ⟨ prior_invar, invar_carries ⟩ 
      unfold search_recurse 
      simp_all
      split
      · next search_step_returned_none =>
        -- recursive case
        apply search_recurse_lift_invariant goal
        constructor
        · unfold invar_carries_over_step at invar_carries
          apply invar_carries
          exact prior_invar
        · exact invar_carries
      · next h =>
        simp_all
termination_by termination_metric priorState
decreasing_by
  next step_returned_none =>
  apply decreasing_proof
  apply step_returned_none



lemma search_recurse_lift_invariant_under_return_assumption 
    {state_type : Type} [has_base_search_state g state_type]
    (goal : V)
    (priorState : state_type)
    (search_step : search_step_function g)
    (termination_metric : state_type → ℕ × ℕ)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
        -- until here all necessary for calling the search_recurse
    (invar : state_type → Prop)
    (return_value : Bool):
      invar priorState ∧ (invar_carries_over_step goal search_step invar)
      ∧ (search_recurse goal priorState search_step termination_metric decreasing_proof).snd = return_value
         → invar (search_recurse goal priorState search_step termination_metric decreasing_proof).fst:= by
      intro ⟨ prior_invar, invar_carries, returned_value⟩ 
      unfold search_recurse 
      simp_all
      split
      · next search_step_returned_none =>
        -- recursive case
        apply search_recurse_lift_invariant_under_return_assumption goal
        rw [← and_assoc]
        repeat constructor
        rotate_right
        · use return_value
        · unfold invar_carries_over_step at invar_carries
          apply invar_carries
          exact prior_invar
        · exact invar_carries
        · unfold search_recurse at returned_value
          simp_all
      · next h =>
        simp_all
termination_by termination_metric priorState
decreasing_by
  next step_returned_none =>
  apply decreasing_proof
  apply step_returned_none



lemma search_recurse_lift_base_invariant  
    {state_type : Type} [has_base_search_state g state_type]
    (goal : V)
    (priorState : state_type)
    (search_step : search_step_function g)
    (termination_metric : state_type → ℕ × ℕ)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
        -- until here all necessary for calling the search_recurse
    (invar : base_search_state g → Prop):
      invar (has_base_search_state.to_base_state priorState)
      ∧ (base_invar_carries_over_step goal search_step invar)
         → invar (has_base_search_state.to_base_state (search_recurse goal priorState search_step termination_metric decreasing_proof).fst) := by
      intro ⟨invar_holds_on_base, invar_carries⟩
      apply search_recurse_lift_invariant goal priorState search_step termination_metric decreasing_proof (fun x => invar (has_base_search_state.to_base_state x)) -- fun needed to tell lean what the "invariant" is it should apply
      constructor
      · use invar_holds_on_base
      · use invar_carries



abbrev invar_becoming_true_causes_other_invar 
    {state_type : Type} [has_base_search_state g state_type]
    (goal : V)
    (search_step : search_step_function (g:=g) (state_type := state_type))
    (invar_1 : state_type → Prop) (invar_2 : state_type → Prop) :=
      ∀ s : state_type, ¬ invar_1 s ∧ invar_1 (search_step goal s).fst → invar_2 (search_step goal s).fst



lemma search_recurse_lift_invariant_under_trigger
    {state_type : Type} [has_base_search_state g state_type]
    (goal : V)
    (priorState : state_type)
    (search_step : search_step_function g)
    (termination_metric : state_type → ℕ × ℕ)
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
        -- until here all necessary for calling the search_recurse
    (invar_end : state_type → Prop)
    (invar_middle : state_type → Prop):
      (¬ invar_middle (search_recurse goal priorState search_step termination_metric decreasing_proof).fst)
      ∧ (¬ invar_end priorState)
      ∧ (invar_carries_over_step goal search_step invar_middle)
      ∧ (invar_becoming_true_causes_other_invar goal search_step invar_end invar_middle)
      → ¬ invar_end (search_recurse goal priorState search_step termination_metric decreasing_proof).fst:= by
      intro ⟨ terminated_with_invar_middle_false, not_invar_end_prior, invar_middle_carries, invar_end_triggers_middle⟩ 

      unfold search_recurse at terminated_with_invar_middle_false ⊢
      simp_all
      split
      · simp_all
        let next_state := (search_step goal priorState).1
        by_cases invar_end next_state
        · next invar_end_becomes_true =>
          have invar_middle_becomes_true := invar_end_triggers_middle priorState ⟨not_invar_end_prior, invar_end_becomes_true ⟩
          have invar_middle_stays_true : invar_middle (search_recurse goal (search_step goal priorState).1 search_step termination_metric decreasing_proof).1 := by
            apply search_recurse_lift_invariant
            exact ⟨ invar_middle_becomes_true, invar_middle_carries⟩ 
          contradiction
        · next invar_end_not_true =>
          apply search_recurse_lift_invariant_under_trigger
          rotate_left
          · use invar_middle 
          · repeat rw [← and_assoc]
            repeat constructor
            · use terminated_with_invar_middle_false
            · use invar_end_not_true
            · use invar_middle_carries 
            · use invar_end_triggers_middle 
      · -- search step showed termination
        simp_all
        by_contra invar_end_becomes_true
        have invar_middle_becomes_true := invar_end_triggers_middle priorState ⟨not_invar_end_prior, invar_end_becomes_true ⟩
        contradiction
termination_by termination_metric priorState
decreasing_by
  next step_returned_none invar_holds =>
  apply decreasing_proof
  apply step_returned_none


section

variable {state_type : Type} [has_base_search_state g state_type]
variable {start : V}
variable {goal : V}
variable {start_state : state_type}
variable {search_step : search_step_function g (state_type := state_type)}
variable {termination_metric : state_type → ℕ × ℕ}


def search_internal
  (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric):
  state_type × Bool :=
  search_recurse goal start_state search_step termination_metric decreasing_proof


lemma search_returns_with_invariants
  (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
  (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
  (invar_carries_over_step : base_invar_carries_over_step goal search_step (search_invar_all_basic start)):
    search_invar_all_basic start (has_base_search_state.to_base_state (g:=g) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    unfold search_internal
    apply search_recurse_lift_base_invariant 
    constructor
    · rw [start_is_base_init]
      unfold base_search_state_initial
      simp_all
      apply base_search_state_initial_all_basic_invars
    · exact invar_carries_over_step

      --unfold base_invar_carries_over_step
      --intro s cond
      --apply dfs_step_keeps_all_basic_invars
      --exact cond
 
lemma search_returns_with_stack_visited
  (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
  (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
  (invar_carries_over_step : base_invar_carries_over_step goal search_step (search_invar_all_basic start)):
    search_invar_stack_is_visited (has_base_search_state.to_base_state (g:=g) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    have all_invars := search_returns_with_invariants (g:=g) decreasing_proof start_is_base_init invar_carries_over_step
    unfold search_invar_all_basic at all_invars
    exact all_invars.1



abbrev search_step_goal_on_stack_if_terminated :=
    ∀ s : state_type, ∀ goal : V, (search_step goal s).2 = true →
      goal ∈ (has_base_search_state.to_base_state (g:=g) (search_step goal s).1).stack 


lemma search_goal_on_stack_if_returned_true
  (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
  (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=search_step)):
    (search_internal (g:=g) (start_state:=start_state) decreasing_proof).2 = true →
      search_prop_goal_on_stack goal (has_base_search_state.to_base_state (g:=g) (search_internal (start_state:=start_state) decreasing_proof).1) := by 
    intro terminated_with_goal_found 
    unfold search_internal
    apply search_recurse_obtain_base_termination_property goal (start_state) (property_after_termination := search_prop_goal_on_stack goal) (terminated_with := true) 
    · intro s
      apply goal_on_stack_if_terminated
    · exact terminated_with_goal_found


lemma search_visited_goal_if_returned_true 
  (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
  (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
  (invar_carries_over_step : base_invar_carries_over_step goal search_step (search_invar_all_basic start))
  (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=search_step)):
  (search_internal (g:=g) (start_state:=start_state) decreasing_proof).2 = true → goal ∈ (has_base_search_state.to_base_state (g:=g) (search_internal (start_state:=start_state) decreasing_proof).1).visited := by 
    intro terminated_with_goal_found 
    apply search_returns_with_stack_visited 
    · exact start_is_base_init 
    · exact invar_carries_over_step
    · apply search_goal_on_stack_if_returned_true
      · exact goal_on_stack_if_terminated
      · exact terminated_with_goal_found 



lemma search_returns_with_mother_visited
  (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
  (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
  (invar_carries_over_step : base_invar_carries_over_step goal search_step (search_invar_all_basic start)):
    search_invar_mother_is_visited (has_base_search_state.to_base_state (g:=g) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    have all_invars := search_returns_with_invariants (g:=g) decreasing_proof start_is_base_init invar_carries_over_step
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.1

lemma search_returns_with_mother_adjacent
  (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
  (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
  (invar_carries_over_step : base_invar_carries_over_step goal search_step (search_invar_all_basic start)):
    search_invar_mother_is_adjacent start (has_base_search_state.to_base_state (g:=g) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    have all_invars := search_returns_with_invariants (g:=g) decreasing_proof start_is_base_init invar_carries_over_step
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.2.1

lemma search_returns_with_mother_decreasing
  (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
  (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
  (invar_carries_over_step : base_invar_carries_over_step goal search_step (search_invar_all_basic start)):
    search_invar_mother_decreasing_path_order start (has_base_search_state.to_base_state (g:=g) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    have all_invars := search_returns_with_invariants (g:=g) decreasing_proof start_is_base_init invar_carries_over_step
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.2.2.1

lemma search_returns_with_start_visited
  (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
  (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
  (invar_carries_over_step : base_invar_carries_over_step goal search_step (search_invar_all_basic start)):
    search_invar_start_visited start (has_base_search_state.to_base_state (g:=g) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    have all_invars := search_returns_with_invariants (g:=g) decreasing_proof start_is_base_init invar_carries_over_step
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.2.2.2.2

lemma search_returns_with_node_on_stack_or_all_neighbours_visited 
  (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
  (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
  (invar_carries_over_step : base_invar_carries_over_step goal search_step (search_invar_all_basic start)):
    search_invar_on_stack_or_all_neighbours_visited (has_base_search_state.to_base_state (g:=g) (search_internal (start_state:=start_state) decreasing_proof).1) := by
    have all_invars := search_returns_with_invariants (g:=g) decreasing_proof start_is_base_init invar_carries_over_step
    unfold search_invar_all_basic at all_invars
    exact all_invars.2.2.2.2.1



------------------------------------------------------------------------------
-- Execution of search

def search_exe
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
    (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
    (invar_carries_over_step : base_invar_carries_over_step goal search_step (search_invar_all_basic start))
    (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=search_step)):
    Option (Path g start goal) :=
  let ret := search_internal decreasing_proof
  let final_state:= ret.1
  let found_goal := ret.2

  if found_goal_true : found_goal = true then

    have goal_in_final_visited :=
      search_visited_goal_if_returned_true decreasing_proof start_is_base_init invar_carries_over_step goal_on_stack_if_terminated found_goal_true

    have mother_visited := search_returns_with_mother_visited decreasing_proof start_is_base_init invar_carries_over_step

    have mother_adjacent := search_returns_with_mother_adjacent decreasing_proof start_is_base_init invar_carries_over_step

    have mother_decreasing := search_returns_with_mother_decreasing decreasing_proof start_is_base_init invar_carries_over_step

    some (extract_path_to start goal (has_base_search_state.to_base_state final_state)
      goal_in_final_visited mother_visited mother_adjacent mother_decreasing).1
  else
    none

theorem search_is_sound
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
    (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
    (invar_carries_over_step : base_invar_carries_over_step goal search_step (search_invar_all_basic start))
    (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=search_step)):
    (Option.isSome (search_exe decreasing_proof start_is_base_init invar_carries_over_step goal_on_stack_if_terminated) → (∃ x : (Path g start goal), x = x)) := by
  intro h -- Option.isSome true on some and false on none, x = x since we need a formula
  constructor -- since goal is existence
  rfl
  let w := Option.get (search_exe decreasing_proof start_is_base_init invar_carries_over_step goal_on_stack_if_terminated) -- Option.get extracts value of returned some and fails otherwise
  apply w
  simp_all


abbrev step_stack_empty_if_terminated_without_goal :=
  ∀ s : state_type,
    (search_step goal s).2 = false →
      search_prop_stack_empty (has_base_search_state.to_base_state (g:=g) (search_step goal s).1)

abbrev step_keeps_goal_on_stack :=
  ∀ s : state_type,
    search_prop_goal_on_stack goal (has_base_search_state.to_base_state (g:=g) s) → 
    search_prop_goal_on_stack goal (has_base_search_state.to_base_state (g:=g) (search_step goal s).1)

abbrev step_goal_becomes_visited_it_is_on_stack:=
  ∀ s : state_type,
  goal ∉ (has_base_search_state.to_base_state (g:=g) s).visited ∧ goal ∈ (has_base_search_state.to_base_state (g:=g) (search_step goal s).1).visited 
  → search_prop_goal_on_stack goal (has_base_search_state.to_base_state (g:=g) (search_step goal s).1)

abbrev search_step_terminates_when_goal_stack_head
--  (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
:= (∃ tail : List V, (has_base_search_state.to_base_state (g:=g) start_state).stack = goal :: tail) → (search_step goal start_state).2 = some true 
--:= (has_base_search_state.to_base_state (g:=g) start_state).stack = [goal] → (search_step goal start_state).2 = some true 


lemma search_empty_stack_if_returned_false_recurse
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
    (stack_empty_if_terminated_without_goal : step_stack_empty_if_terminated_without_goal (g:=g) (search_step:=search_step) (goal:=goal))
    :
    (search_internal (start_state := start_state) decreasing_proof).2 = false
    → search_prop_stack_empty (has_base_search_state.to_base_state (g:=g) (search_internal (start_state := start_state) decreasing_proof).1) := by
    intro terminated_with_goal_not_found
    unfold search_internal
    let prop_after_termination : state_type → Prop :=
      (fun s => search_prop_stack_empty (g:=g) (has_base_search_state.to_base_state (g:=g) s))
    apply search_recurse_obtain_termination_property (g:=g) goal start_state (property_after_termination := prop_after_termination) (terminated_with := false) 
    · intro s
      unfold prop_after_termination
      unfold step_stack_empty_if_terminated_without_goal at stack_empty_if_terminated_without_goal
      apply stack_empty_if_terminated_without_goal 
    · exact terminated_with_goal_not_found


lemma search_recurse_goal_not_visited_if_terminated
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
    (stack_empty_if_terminated_without_goal : step_stack_empty_if_terminated_without_goal (g:=g) (search_step:=search_step) (goal:=goal))
    (keeps_goal_on_stack : step_keeps_goal_on_stack (g:=g) (search_step:=search_step) (goal:=goal))
    (goal_becomes_visited_implies_on_stack: step_goal_becomes_visited_it_is_on_stack (g:=g) (search_step:=search_step) (goal:=goal))
    :
    (search_internal (start_state := start_state) decreasing_proof).2 = false
    ∧ ¬ search_prop_goal_visited goal (has_base_search_state.to_base_state (g:=g) start_state)
    → ¬ search_prop_goal_visited goal (has_base_search_state.to_base_state (g:=g) (search_internal (start_state := start_state) decreasing_proof).1) := by
    intro ⟨ terminated_with_false, goal_not_visited_before ⟩ 
    unfold search_internal
    apply search_recurse_lift_invariant_under_trigger goal start_state search_step (invar_end:= fun s => search_prop_goal_visited goal (has_base_search_state.to_base_state s))
    repeat rw [← and_assoc]
    repeat constructor
    rotate_right
    · use (fun s =>
        let base_state : base_search_state g := (has_base_search_state.to_base_state s)
        search_prop_goal_on_stack goal base_state)
    · apply search_empty_stack_if_returned_false_recurse at terminated_with_false
      unfold search_prop_goal_on_stack at ⊢  
      unfold search_prop_stack_empty at terminated_with_false
      unfold search_internal at terminated_with_false
      simp_all
      exact stack_empty_if_terminated_without_goal
    · apply goal_not_visited_before
    · apply keeps_goal_on_stack
    · apply goal_becomes_visited_implies_on_stack



lemma search_not_visited_goal_if_returned_false
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
    (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
    (step_terminates_if_goal_is_stack_head : search_step_terminates_when_goal_stack_head (search_step:=search_step) (goal:=goal) (start_state:=start_state))
    (stack_empty_if_terminated_without_goal : step_stack_empty_if_terminated_without_goal (g:=g) (search_step:=search_step) (goal:=goal))
    (keeps_goal_on_stack : step_keeps_goal_on_stack (g:=g) (search_step:=search_step) (goal:=goal))
    (goal_becomes_visited_implies_on_stack: step_goal_becomes_visited_it_is_on_stack (g:=g) (search_step:=search_step) (goal:=goal))
    :
    (search_internal (start_state := start_state) decreasing_proof).2 = false → goal ∉ (has_base_search_state.to_base_state (g:=g) (search_internal (start_state := start_state) decreasing_proof).1).visited := by
    --(start : V) (goal : V):
    --(dfs_internal g start goal).2 = false → goal ∉ (dfs_internal g start goal).1.visited := by
     intro terminated_with_not_goal_found
     apply search_recurse_goal_not_visited_if_terminated
     · exact stack_empty_if_terminated_without_goal
     · exact keeps_goal_on_stack
     · exact goal_becomes_visited_implies_on_stack
     constructor
     · exact terminated_with_not_goal_found 
     · rw [start_is_base_init]
       unfold base_search_state_initial
       unfold search_prop_goal_visited
       simp
       by_contra goal_is_start
       unfold search_internal at terminated_with_not_goal_found
       unfold search_recurse at terminated_with_not_goal_found
       have initial_stack_is_goal : (has_base_search_state.to_base_state (g:=g) start_state).stack = [goal] := by
         rw [start_is_base_init]
         unfold base_search_state_initial 
         simp_all
       unfold search_step_terminates_when_goal_stack_head at step_terminates_if_goal_is_stack_head
       simp_all


theorem search_is_complete 
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
    (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
    (invar_carries_over_step : base_invar_carries_over_step goal search_step (search_invar_all_basic start))
    (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=search_step))
    (stack_empty_if_terminated_without_goal : step_stack_empty_if_terminated_without_goal (g:=g) (search_step:=search_step) (goal:=goal))
    (keeps_goal_on_stack : step_keeps_goal_on_stack (g:=g) (search_step:=search_step) (goal:=goal))
    (goal_becomes_visited_implies_on_stack: step_goal_becomes_visited_it_is_on_stack (g:=g) (search_step:=search_step) (goal:=goal))
----
    (step_terminates_if_goal_is_stack_head : search_step_terminates_when_goal_stack_head (search_step:=search_step) (goal:=goal) (start_state:=start_state))
    :
    ((∃ x : (Path g start goal), x = x) → Option.isSome (search_exe decreasing_proof start_is_base_init invar_carries_over_step goal_on_stack_if_terminated)) := by
    -- or Option.isNone (dfs g start goal) → ∄ x (Path g start goal), x = x
      intro path_exists
      apply Exists.elim path_exists
      intro thePath a; clear a-- uninformativ x=X

      let final := search_internal (start_state:=start_state) decreasing_proof
      let final_state : base_search_state g := has_base_search_state.to_base_state final.1
      
      have start_visited : search_invar_start_visited start final_state :=
        search_returns_with_start_visited decreasing_proof start_is_base_init invar_carries_over_step
      have on_stack_or_all_nei_visited : search_invar_on_stack_or_all_neighbours_visited final_state:=
        search_returns_with_node_on_stack_or_all_neighbours_visited decreasing_proof start_is_base_init invar_carries_over_step 

      by_contra terminates_with_none
      simp at terminates_with_none

      have search_returned_false : (search_internal (start_state:=start_state) decreasing_proof).2 = false := by
        unfold search_exe at terminates_with_none
        simp at terminates_with_none
        exact terminates_with_none

      have final_stack_empty : final_state.stack = [] := by
        apply search_empty_stack_if_returned_false_recurse
        · exact stack_empty_if_terminated_without_goal
        · exact search_returned_false


      have goal_not_visited : goal ∉ final_state.visited := --
        search_not_visited_goal_if_returned_false decreasing_proof start_is_base_init step_terminates_if_goal_is_stack_head stack_empty_if_terminated_without_goal keeps_goal_on_stack goal_becomes_visited_implies_on_stack search_returned_false 

      obtain ⟨theWalk, nodupe ⟩ := thePath
      have goal_in_final := search_termination_with_empty_stack_implies_goal_visited start goal start theWalk final_state start_visited final_stack_empty on_stack_or_all_nei_visited
      contradiction


theorem search_is_complete_inv
    (decreasing_proof : termination_metric_decreasing_proof goal search_step termination_metric)
    (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
    (invar_carries_over_step : base_invar_carries_over_step goal search_step (search_invar_all_basic start))
    (goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=search_step))
    (stack_empty_if_terminated_without_goal : step_stack_empty_if_terminated_without_goal (g:=g) (search_step:=search_step) (goal:=goal))
    (keeps_goal_on_stack : step_keeps_goal_on_stack (g:=g) (search_step:=search_step) (goal:=goal))
    (goal_becomes_visited_implies_on_stack: step_goal_becomes_visited_it_is_on_stack (g:=g) (search_step:=search_step) (goal:=goal))
----
    (step_terminates_if_goal_is_stack_head : search_step_terminates_when_goal_stack_head (search_step:=search_step) (goal:=goal) (start_state:=start_state))
    :
    Option.isNone (search_exe decreasing_proof start_is_base_init invar_carries_over_step goal_on_stack_if_terminated) → ¬ ∃ x : (Path g start goal), x = x := by
      intro optionIsNone
      by_contra pathExists
      have isSome := search_is_complete decreasing_proof start_is_base_init invar_carries_over_step goal_on_stack_if_terminated stack_empty_if_terminated_without_goal keeps_goal_on_stack goal_becomes_visited_implies_on_stack step_terminates_if_goal_is_stack_head
      simp_all

end
