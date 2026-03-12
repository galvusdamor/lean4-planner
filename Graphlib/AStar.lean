import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Empty
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.ToFinsupp
import Mathlib.Data.List.Pairwise
import Mathlib.Algebra.Group.WithOne.Defs

import Graphlib.WF

import Graphlib.Lists
import Graphlib.FinEnum
import Graphlib.Basic
import Graphlib.NatGraph
import Graphlib.SearchState
import Graphlib.SearchAlgorithm
import Graphlib.SearchStep
import Graphlib.HeuristicSearch
import Init.SimpLemmas
import Init.Core

set_option trace.split.failure true
--set_option diagnostics true

-- def local global variable for a graph
variable {V : Type} [FinEnum V] [DecidableEq V]
variable {g : NatGraph V}


namespace NatGraph

open WeightedDiGraph

/-- a heuristic is admissible iff for all nodes, the true cost is greater or equal to the heuristic --/
abbrev admissible (heur : V → ℕ) (goal : V) :=
  ∀ v : V, g.cost_ge v goal (heur v)

variable (heur : V → ℕ)

def astar (start : V) (goal : V): Option (g.Path start goal) :=
  let start_state := WeightedDiGraph.base_search_state_initial start ⟨0,0⟩
  have h : WeightedDiGraph.has_base_search_state.to_base_state (G:=g) start_state = WeightedDiGraph.base_search_state_initial start (0,0):= by simp_all only [start_state]; rfl

  WeightedDiGraph.search_exe_with_stack_step (G:=g) (start := start) (goal:=goal) (start_state:=start_state) (termination_metric := hsearch_termination_metric) (hsearch_step_expand heur) (hsearch_expand_metric_reduction heur) (hsearch_expand_keeps_base_invars heur) h 


def astar_last_state (start : V) (goal : V): WeightedDiGraph.base_search_state g (ℕ×ℕ) × Bool :=
  WeightedDiGraph.search_with_stack_step (goal:=goal) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (hsearch_step_expand heur) (hsearch_expand_metric_reduction heur)


theorem astar_is_sound (start : V) (goal : V) :
    (Option.isSome (astar (g:=g) heur start goal) → (∃ x : (g.Path start goal), x = x)) := by
  apply WeightedDiGraph.search_with_stack_step_is_sound
  · apply hsearch_expand_metric_reduction
  · apply hsearch_expand_keeps_base_invars
  · rfl



theorem astar_is_complete (start : V) (goal : V):
    ((∃ x : (g.Path start goal), x = x) → Option.isSome (astar (g:=g) heur start goal)) := by
  apply WeightedDiGraph.search_with_stack_step_is_complete
  · apply hsearch_expand_metric_reduction
  · apply hsearch_expand_keeps_base_invars
  · rfl
  · apply hsearch_expand_keeps_goal_on_stack
  · apply hsearch_expand_goal_becomes_visited_puts_it_on_stack




/-- Optimality proof --/
/- stack is sorted by the path_order (i.e. distance) value -/

abbrev astar_stack_sorted (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
  List.Pairwise (fun u v =>
    (add_heur u (s.pathOrder u) heur = add_heur v (s.pathOrder v) heur) ∨ (add_heur u (s.pathOrder u) heur ≺ add_heur v (s.pathOrder v) heur)) s.stack



abbrev node_open (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) (v : V) :=
  v ∈ s.stack

abbrev node_closed (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) (v : V) :=
  v ∈ s.visited ∧ v ∉ s.stack


/-- Invar propose by Hart et al, 1968 (lemma 1):
    any non-closed node v (i.e. any node that is either on the stack or not visited)
    for all optimal paths p from start to it
    there is an open node v' on p for which its current known distance from start is the optimum -/
abbrev astar_invar (start : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
  ∀ v : V, ¬ (node_closed s v) → ∀ p : g.Path start v, p.is_cheapest →
    ∃ v' ∈ p.support, (node_open s v') ∧ g.cost_is start v' (s.pathOrder v').1 

abbrev astar_path_invar (start : V) (goal : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ)) :=
  --∀ p : g.Path start goal, p.is_cheapest → ∃ v' ∈ p.support, (node_open s v')
  ∀ p : g.Path start goal, ∃ v' ∈ p.support, (node_open s v')


omit [DecidableEq V] in
lemma astar_invar_holds_at_init (start : V):
  astar_invar start (WeightedDiGraph.base_search_state_initial (G:=g) start (0,0)) := by
  unfold astar_invar
  unfold WeightedDiGraph.base_search_state_initial
  simp_all
  intro v a nodup cheapest
  use start
  constructor
  · simp
  · unfold node_open
    simp
    apply cost_v_v




section
variable (state : WeightedDiGraph.base_search_state g (ℕ×ℕ))

lemma astar_expand_keeps_stack_sorted (goal : V)
    :
     ∀ head : V, ∀ tail : List V, 
        astar_stack_sorted heur state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → astar_stack_sorted  heur (hsearch_step_expand heur state head tail) := by
      intro head tail ⟨ prior_invar,head_ne_goal,compose⟩ 
      unfold astar_stack_sorted
      unfold hsearch_step_expand
      apply merge_two_prop 
      · intro a b c a_b b_c
        apply hsearch_merge_trans
        · apply a_b
        · apply b_c
      · intro a b
        apply hsearch_merge_total
      · ext x y
        rw [FValueComp.lt_B_eq]
        simp


lemma astar_expand_keeps_path_invar (goal : V)
    (on_stack_or_nei_visited : search_invar_on_stack_or_all_neighbours_visited state)
    :
     ∀ head : V, ∀ tail : List V, 
        astar_path_invar start goal state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → astar_path_invar start goal (hsearch_step_expand heur state head tail) := by
    intro head tail ⟨ prior_invar, head_ne_goal, stack_compose ⟩
    unfold astar_path_invar at prior_invar ⊢
    intro p
    specialize prior_invar p
    obtain ⟨v', v'_in_p, was_open ⟩ := prior_invar
    unfold node_open at was_open ⊢
    rw [stack_compose] at was_open
    cases was_open
    case head =>
      have head_visited : head ∈ state.visited := by sorry
      obtain ⟨start_head, head_goal, compose⟩ := p.val.split_at v'_in_p
      have head_goal_nodup : head_goal.support.Nodup := by sorry


      -- TODO: more complicated, we have to run through the path at the next time -- or equivalently, we have to start at the next node
      --obtain ⟨head',nil_path,adj_head_u',u'_v,supp1,supp2,compose⟩  := Path.recompose ⟨ head_goal, head_goal_nodup⟩ (u:=head) (by simp) head_ne_goal 

      cases head_goal
      case nil =>
        contradiction -- (goal ≠ goal)
      case cons head' adj_head_head' head'_goal =>
        sorry
        --have run_path := run_path_through_state_yields_node_on_stack_or_all_visited head goal (Ne.symm head_ne_goal) ⟨head_goal, head_goal_nodup⟩ state head_visited on_stack_or_nei_visited
        --
        --cases run_path
        --case inl first_open =>
        --  obtain ⟨ u, u_in_support, u_on_stack, u_not_goal, prop ⟩ := first_open
        --  use u
        --  constructor
        --  · sorry -- follows as subpath of u_in_support
        --  · sorry
        --case inr all_not_on_stack =>
        --  sorry
    case tail v'_in_tail =>
      use v'
      constructor
      · exact v'_in_p 
      · unfold hsearch_step_expand
        simp
        left
        exact v'_in_tail

lemma astar_expand_keeps_main_invar (goal : V)
    :
     ∀ head : V, ∀ tail : List V, 
        astar_invar start state
          ∧ head ≠ goal
          ∧ state.stack = head :: tail
        → astar_invar start (hsearch_step_expand heur state head tail) := by
    sorry

end

omit [DecidableEq V] in 
lemma walk_more_costly_than_chapest (start v : V) (d : ℕ)
(v_cost_is : g.cost_is start v d) 
(w : g.Walk start v) :
    d ≤ w.cost := by
    unfold cost_is at v_cost_is
    obtain ⟨p,p_cost,p_cheapest⟩ := v_cost_is
    rw [←p_cost]
    unfold Path.is_cheapest at p_cheapest
    obtain ⟨w', w'_cheaper ⟩ := w.cheaper_path_exists
    apply le_trans
    · exact p_cheapest w'
    · exact w'_cheaper


lemma astar_open_node_with_lower_f (start goal : V) (s : WeightedDiGraph.base_search_state g (ℕ×ℕ))
  (is_admissible : g.admissible heur goal)
  -- invariant: goal has not been removed ... I.e. every path still has a node on the stack
  -- this is a strange invariant as the expansion will actually break it!
  -- actually not! as we only have to prove the invar iff head ≠ goal
  (has_astar_invar : astar_invar start s)
  (has_path_invar : astar_path_invar start goal s)
  :
  ∀ p : g.Path start goal, p.is_cheapest → 
    ∃ v' ∈ p.support, (node_open s v') ∧ (s.pathOrder v').1 + (heur v') ≤ p.cost
  := by
  intro p p_cheapest
  unfold astar_invar at has_astar_invar
  unfold astar_path_invar at has_path_invar
  obtain ⟨v', v'_in_p, v'_open⟩ := has_path_invar p

  specialize has_astar_invar v'
  unfold node_closed at has_astar_invar
  simp [v'_open] at has_astar_invar
  obtain ⟨start_v', v'_goal, compose⟩ := p.val.split_at v'_in_p
  have start_v'_nodup : start_v'.support.Nodup := by sorry -- from subpath
  -- Theorem: subpaths of cheapest paths are cheapest
  -- needs the subpath argument for nodup
  have start_v'_cheapest : Path.is_cheapest ⟨start_v', start_v'_nodup⟩ := by sorry
  
  specialize has_astar_invar start_v' start_v'_nodup start_v'_cheapest

  obtain ⟨v'',v''_in_support,v''_open,v''_cost_is⟩ := has_astar_invar 

  use v''
  and_intros
  · unfold Path.support
    rw [←compose]
    rw [Walk.support_of_append]
    rw [List.mem_append]
    left
    exact v''_in_support
  · exact v''_open
  · unfold Path.cost 
    have v''_in_p : v'' ∈ p.support := by sorry 
    obtain ⟨start_v'', v''_goal, compose⟩ := p.val.split_at v''_in_p

    rw [←compose]
    rw [Walk.append_cost]
    apply add_le_add
    · apply walk_more_costly_than_chapest
      exact v''_cost_is
    · unfold admissible at is_admissible
      specialize is_admissible v''
      unfold cost_ge at is_admissible
  
      -- subwalk of p
      have v''_goal_nodup : v''_goal.support.Nodup := by sorry
      specialize is_admissible ⟨v''_goal, v''_goal_nodup⟩ 
      apply is_admissible



@[simp]
theorem admissible_heur_zero_for_goal
    (is_admissible : g.admissible heur goal):
    heur goal = 0 := by sorry

/- -/
theorem astar_is_optimal (start : V) (goal : V)
    (is_admissible : g.admissible heur goal)
    (returned_path : Option.isSome (astar (g:=g) heur start goal)):
    ((astar (g:=g) heur start goal).get returned_path).is_cheapest := by
    let final : WeightedDiGraph.base_search_state g (ℕ×ℕ) × Bool := WeightedDiGraph.search_with_stack_step (goal:=goal) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (hsearch_step_expand heur) (hsearch_expand_metric_reduction heur)
    let final_state := final.1
 
    -- general properties
    have h_4 : WeightedDiGraph.search_prop_stack_head_is_goal goal final_state := by
      --intro terminated_with_goal_found 
      --unfold search_prop_stack_head_is_goal
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp
      unfold WeightedDiGraph.search_internal
      apply WeightedDiGraph.search_recurse_obtain_base_termination_property (G:=g) (D:=ℕ×ℕ) (T:=(Vector (WithTop (ℕ × ℕ)) g.nodeNum) × ℕ) goal (WeightedDiGraph.base_search_state_initial start (0,0)) (property_after_termination := WeightedDiGraph.search_prop_stack_head_is_goal (D:=ℕ×ℕ) goal ) (terminated_with := true) (search_step := WeightedDiGraph.search_stack_step (G:=g) (D:=ℕ×ℕ) (hsearch_step_expand (g:=g) heur)) hsearch_termination_metric 
      · intro s
        apply WeightedDiGraph.search_stack_step_goal_stack_head_if_terminated
      · unfold astar at returned_path
        unfold WeightedDiGraph.search_exe_with_stack_step at returned_path
        unfold WeightedDiGraph.search_exe at returned_path
        simp_all
        apply returned_path

    have t_0 : WeightedDiGraph.search_invar_stack_is_visited final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_stack_visited (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply hsearch_expand_keeps_base_invars

    have h_3 : WeightedDiGraph.search_prop_goal_visited goal final_state := by
      apply t_0
      unfold WeightedDiGraph.search_prop_stack_head_is_goal at h_4 
      apply List.eq_cons_of_mem_head? at h_4
      rw [h_4]
      simp

    have t_1 : WeightedDiGraph.search_invar_mother_is_visited final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_mother_visited (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply hsearch_expand_keeps_base_invars

    have t_2 : WeightedDiGraph.search_invar_mother_is_adjacent start final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_mother_adjacent (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply hsearch_expand_keeps_base_invars

    have t_3 : WeightedDiGraph.search_invar_mother_decreasing_path_order start final_state := by
      unfold final_state
      unfold final
      unfold WeightedDiGraph.search_with_stack_step
      simp only []
      apply WeightedDiGraph.search_returns_with_mother_decreasing (state_type := WeightedDiGraph.base_search_state g (ℕ×ℕ)) (start_state := WeightedDiGraph.base_search_state_initial start (0,0)) (start := start)
      · rfl
      · apply WeightedDiGraph.base_invar_carries_over_stack_step
        apply hsearch_expand_keeps_base_invars
    
    have prop := hsearch_path_extracted_not_longer_than_path_order start final_state t_1 t_2 t_3 (by sorry)

    have has_astar_invar : astar_invar start final_state := by sorry
    have has_astar_path_invar : astar_path_invar start goal final_state := by sorry
    have xx := astar_open_node_with_lower_f heur start goal final_state is_admissible has_astar_invar


    apply Path.sufficient_cheapest_path_cheaper

    --unfold Path.is_cheapest
    intro p' p'_cheapest

    specialize xx has_astar_path_invar p' p'_cheapest

    obtain ⟨v', v'_on_p', v'_open,cost⟩ := xx 

    apply le_trans ; rotate_left
    · apply cost
    · clear cost
      unfold astar search_exe_with_stack_step search_exe
      simp
      specialize prop goal h_3
      apply le_trans
      · apply prop
      · -- from invariant
        have final_stack_sorted : astar_stack_sorted heur final_state := by sorry
        unfold astar_stack_sorted at final_stack_sorted
        unfold search_prop_stack_head_is_goal at h_4 
        apply List.head?_eq_some_iff.mp at h_4
        obtain ⟨tail, compose⟩ := h_4
        unfold node_open at v'_open
        rw [compose] at final_stack_sorted v'_open
        rw [List.pairwise_cons] at final_stack_sorted
        obtain ⟨tail_larger, _⟩ := final_stack_sorted
        cases v'_open
        · apply Nat.le_add_right
        · next v'_in_tail =>
          specialize tail_larger v' v'_in_tail
          unfold add_heur at tail_larger
          rw [admissible_heur_zero_for_goal heur is_admissible] at tail_larger
          simp only [add_zero] at tail_larger
          cases tail_larger
          case inl h =>
            apply le_of_eq
            exact (Prod.mk_inj.mp h).1
          case inr h => 
            unfold FValueComp.lt Nat.instFValueCompProd at h
            simp at h
            apply Prod.lex_iff.mp at h
            cases h
            case inl h =>
              apply le_of_lt
              exact h
            case inr h =>
              apply le_of_eq
              exact h.1

end NatGraph
