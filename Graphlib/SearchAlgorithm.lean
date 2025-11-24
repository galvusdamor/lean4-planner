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
