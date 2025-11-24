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
--variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V] [DecidableEq E]
--variable (G : WeightedDiGraph V E)



-----------------------------------------------------------------------
------ Search state of the DFS and its invariants
structure base_search_state [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) where
    visited : Finset V
    pathOrder : V → Nat 
    mother : visited → V
    stack : List V
    terminated : Bool

class has_base_search_state [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (B : Type) where
  to_base_state : B → base_search_state g start


instance [FinEnum V] [DecidableEq E] [DecidableEq V](g: WeightedDiGraph V E) (start : V):
    has_base_search_state g start (base_search_state g start) where
  to_base_state := fun x => x 

abbrev search_prop_goal_on_stack[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V) (s : base_search_state g start):=
      goal ∈ s.stack

abbrev search_prop_goal_visited[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V) (s : base_search_state g start):=
      goal ∈ s.visited

abbrev search_prop_stack_empty[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : base_search_state g start):=
      s.stack = []

abbrev search_invar_stack_is_visited [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : base_search_state g start):=
      ∀ x : V, x ∈ s.stack → x ∈ s.visited

abbrev search_invar_mother_is_visited [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : base_search_state g start):=
      ∀ x : s.visited, s.mother x ∈ s.visited

abbrev search_invar_mother_is_adjacent [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : base_search_state g start):=
      ∀ x : s.visited, ↑x ≠ start → g.Adj (s.mother x) x

abbrev search_invar_mother_decreasing_path_order [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : base_search_state g start) :=
      ∀ x : s.visited, ↑x ≠ start → s.pathOrder (s.mother x) < s.pathOrder x 

abbrev search_invar_on_stack_or_all_neighbours_visited [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : base_search_state g start):=
      ∀ x : s.visited, ↑x ∈ s.stack ∨ ∀ y : V, (g.Adj x y) → y ∈ s.visited

abbrev search_invar_start_visited [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : base_search_state g start) :=
      start ∈ s.visited

abbrev search_invar_all_basic[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : base_search_state g start) :=
      search_invar_stack_is_visited g start s
      ∧ search_invar_mother_is_visited g start s
      ∧ search_invar_mother_is_adjacent g start s
      ∧ search_invar_mother_decreasing_path_order g start s
      ∧ search_invar_on_stack_or_all_neighbours_visited g start s
      ∧ search_invar_start_visited g start s


def extract_path_to [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V) (search_state : base_search_state g start)
    (goal_reached : goal ∈ search_state.visited)
    (mother_invar : search_invar_mother_is_visited g start search_state)
    (mother_invar_adj : search_invar_mother_is_adjacent g start search_state)
    (decreasing_invar : search_invar_mother_decreasing_path_order g start search_state):
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
          extract_path_to g start goal_predecessor search_state (by apply mother_invar) mother_invar mother_invar_adj decreasing_invar 
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


theorem search_termination_with_empty_stack_implies_goal_visited [FinEnum V] [DecidableEq E] [DecidableEq V](g: WeightedDiGraph V E) (start : V) (goal : V) (f : V) 
  (theWalk : Walk g f goal)
  (final_state : base_search_state g start)
  (f_visited : f ∈ final_state.visited)
  (final_stack_empty : final_state.stack = [])
  (on_stack_or_all_nei_visited : search_invar_on_stack_or_all_neighbours_visited g start final_state): goal ∈ final_state.visited := by
    cases theWalk
    · exact f_visited
    · next nextNode adj rest_walk =>
      apply search_termination_with_empty_stack_implies_goal_visited  g start goal nextNode rest_walk
      · unfold search_invar_on_stack_or_all_neighbours_visited at on_stack_or_all_nei_visited
        rw [final_stack_empty] at on_stack_or_all_nei_visited
        simp at on_stack_or_all_nei_visited
        apply on_stack_or_all_nei_visited f f_visited nextNode adj
      · exact final_stack_empty
      · exact on_stack_or_all_nei_visited


abbrev search_step_function [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V)
    {state_type : Type} [has_base_search_state g start state_type] :=
      V → state_type → state_type × (Option Bool)


abbrev search_state_not_terminated [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) 
    {state_type : Type} [has_base_search_state g start state_type]
    (state : state_type):=
    let base_state : base_search_state g start := (has_base_search_state.to_base_state state)
    base_state.terminated = false


abbrev search_step_does_not_terminate [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    {state_type : Type} [has_base_search_state g start state_type]
    (search_step : search_step_function (state_type := state_type) g start) :=
    ∀ s :
      state_type,
        let res : state_type × (Option Bool) := search_step goal s
        let res_state : base_search_state g start := (has_base_search_state.to_base_state res.fst)
        res.snd = none → res_state.terminated = false

def base_search_state_termination_metric [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : base_search_state g start): ℕ × ℕ :=
    (Fintype.card V - s.visited.card, s.stack.length)


------------------------------------------------------------------------------------------
-- Search Recurse
------------------
def search_recurse [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V)
    {state_type : Type} [has_base_search_state g start state_type]
    (goal : V)
    (priorState : state_type)
    (not_terminated : search_state_not_terminated g start (state_type := state_type) priorState)
    (search_step : search_step_function g start)
    (does_not_set_teriminate: search_step_does_not_terminate g start goal (state_type := state_type) search_step)
    (termination_metric : state_type → ℕ × ℕ)
    (decreasing_proof : ∀ s : state_type,
        search_state_not_terminated g start (search_step goal s).1 → 
        Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2)
        (termination_metric (search_step goal s).1) (termination_metric s)):
    state_type × Bool :=
  let qq := search_step goal priorState
  let nextState := qq.fst
  let result : Option Bool := qq.snd
  if result_is_none : result = none then 
    let still_not_terminated : (has_base_search_state.to_base_state nextState).terminated = false := by
      apply does_not_set_teriminate
      apply result_is_none

    --let still_not_terminated : nextState.terminated = false := by
    search_recurse g start goal nextState
      still_not_terminated search_step does_not_set_teriminate termination_metric decreasing_proof
  else ⟨ nextState, result.get (by apply Option.isSome_iff_ne_none.mpr ; exact result_is_none) ⟩ 
termination_by termination_metric priorState
decreasing_by
  apply decreasing_proof
  apply still_not_terminated



lemma search_recurse_obtain_termination_property [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V)
    {state_type : Type} [has_base_search_state g start state_type]
    (goal : V)
    (priorState : state_type)
    (not_terminated : search_state_not_terminated g start (state_type := state_type) priorState)
    (search_step : search_step_function g start)
    (does_not_set_teriminate: search_step_does_not_terminate g start goal (state_type := state_type) search_step)
    (termination_metric : state_type → ℕ × ℕ)
    (decreasing_proof : ∀ s : state_type,
        search_state_not_terminated g start (search_step goal s).1 → 
        Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2)
        (termination_metric (search_step goal s).1) (termination_metric s))
    -- until here all necessary for calling the search_recurse
    (terminated_with : Bool) -- recursion terminated with
    (property_after_termination : state_type → Prop):
      (∀ s : state_type, (search_step goal s).2 = some terminated_with → property_after_termination (search_step goal s).1)
    → 
      ((search_recurse g start goal priorState not_terminated search_step does_not_set_teriminate termination_metric decreasing_proof).2 = terminated_with → 
      property_after_termination (search_recurse g start goal priorState not_terminated search_step does_not_set_teriminate termination_metric decreasing_proof).1):= by
      intro step_termination_property recursion_terminated_with
      unfold search_recurse at recursion_terminated_with ⊢
      simp_all
      split
      · next search_step_returned_none =>
        -- recursive case
        simp_all
        apply search_recurse_obtain_termination_property g start goal
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

  let nextState : state_type := (search_step goal priorState).1
  let still_not_terminated : (has_base_search_state.to_base_state nextState).terminated = false := by
      apply does_not_set_teriminate
      apply step_returned_none

  apply still_not_terminated


abbrev invar_carries_over_step [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)(start : V)
    {state_type : Type} [has_base_search_state g start state_type]
    (goal : V)
    (search_step : search_step_function g start (state_type := state_type))
    (invar : state_type → Prop) :=
      ∀ s : state_type, invar s → invar (search_step goal s).fst


abbrev base_invar_carries_over_step [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E)(start : V)
    {state_type : Type} [has_base_search_state g start state_type]
    (goal : V)
    (search_step : search_step_function g start (state_type := state_type))
    (invar : base_search_state g start → Prop) :=
      ∀ s : state_type, invar (has_base_search_state.to_base_state s) → invar (has_base_search_state.to_base_state (search_step goal s).fst)



lemma search_recurse_lift_invariant [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V)
    {state_type : Type} [has_base_search_state g start state_type]
    (goal : V)
    (priorState : state_type)
    (not_terminated : search_state_not_terminated g start (state_type := state_type) priorState)
    (search_step : search_step_function g start)
    (does_not_set_teriminate: search_step_does_not_terminate g start goal (state_type := state_type) search_step)
    (termination_metric : state_type → ℕ × ℕ)
    (decreasing_proof : ∀ s : state_type,
        search_state_not_terminated g start (search_step goal s).1 → 
        Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2)
        (termination_metric (search_step goal s).1) (termination_metric s))
    -- until here all necessary for calling the search_recurse
    (invar : state_type → Prop):
      invar priorState ∧ (invar_carries_over_step g start goal search_step invar)
         → invar (search_recurse g start goal priorState not_terminated search_step does_not_set_teriminate termination_metric decreasing_proof).fst:= by
      intro ⟨ prior_invar, invar_carries ⟩ 
      unfold search_recurse 
      simp_all
      split
      · next search_step_returned_none =>
        -- recursive case
        apply search_recurse_lift_invariant g start goal
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

  let nextState : state_type := (search_step goal priorState).1
  let still_not_terminated : (has_base_search_state.to_base_state nextState).terminated = false := by
      apply does_not_set_teriminate
      apply step_returned_none

  apply still_not_terminated


lemma search_recurse_lift_invariant_under_return_assumption [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V)
    {state_type : Type} [has_base_search_state g start state_type]
    (goal : V)
    (priorState : state_type)
    (not_terminated : search_state_not_terminated g start (state_type := state_type) priorState)
    (search_step : search_step_function g start)
    (does_not_set_teriminate: search_step_does_not_terminate g start goal (state_type := state_type) search_step)
    (termination_metric : state_type → ℕ × ℕ)
    (decreasing_proof : ∀ s : state_type,
        search_state_not_terminated g start (search_step goal s).1 → 
        Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2)
        (termination_metric (search_step goal s).1) (termination_metric s))
    -- until here all necessary for calling the search_recurse
    (invar : state_type → Prop)
    (return_value : Bool):
      invar priorState ∧ (invar_carries_over_step g start goal search_step invar)
      ∧ (search_recurse g start goal priorState not_terminated search_step does_not_set_teriminate termination_metric decreasing_proof).snd = return_value
         → invar (search_recurse g start goal priorState not_terminated search_step does_not_set_teriminate termination_metric decreasing_proof).fst:= by
      intro ⟨ prior_invar, invar_carries, returned_value⟩ 
      unfold search_recurse 
      simp_all
      split
      · next search_step_returned_none =>
        -- recursive case
        apply search_recurse_lift_invariant_under_return_assumption g start goal
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

  let nextState : state_type := (search_step goal priorState).1
  let still_not_terminated : (has_base_search_state.to_base_state nextState).terminated = false := by
      apply does_not_set_teriminate
      apply step_returned_none

  apply still_not_terminated


lemma search_recurse_lift_base_invariant [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V)
    {state_type : Type} [has_base_search_state g start state_type]
    (goal : V)
    (priorState : state_type)
    (not_terminated : search_state_not_terminated g start (state_type := state_type) priorState)
    (search_step : search_step_function g start)
    (does_not_set_teriminate: search_step_does_not_terminate g start goal (state_type := state_type) search_step)
    (termination_metric : state_type → ℕ × ℕ)
    (decreasing_proof : ∀ s : state_type,
        search_state_not_terminated g start (search_step goal s).1 → 
        Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2)
        (termination_metric (search_step goal s).1) (termination_metric s))
    -- until here all necessary for calling the search_recurse
    (invar : base_search_state g start → Prop):
      invar (has_base_search_state.to_base_state priorState)
      ∧ (base_invar_carries_over_step g start goal search_step invar)
         → invar (has_base_search_state.to_base_state (search_recurse g start goal priorState not_terminated search_step does_not_set_teriminate termination_metric decreasing_proof).fst) := by
      intro ⟨invar_holds_on_base, invar_carries⟩
      apply search_recurse_lift_invariant g start goal priorState not_terminated search_step does_not_set_teriminate termination_metric decreasing_proof (fun x => invar (has_base_search_state.to_base_state x)) -- fun needed to tell lean what the "invariant" is it should apply
      constructor
      · use invar_holds_on_base
      · use invar_carries
