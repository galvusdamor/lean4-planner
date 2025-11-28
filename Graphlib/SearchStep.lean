import Graphlib.SearchState
import Graphlib.SearchAlgorithm




section

-- def local global variable for a graph
variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V] [DecidableEq E]
variable {g : WeightedDiGraph V E}


abbrev search_expand(g : WeightedDiGraph V E)
    {state_type : Type} [has_base_search_state g state_type] :=
    state_type → V → List V → state_type


section
variable {state_type : Type} [has_base_search_state g state_type]
variable {start : V}
--variable {goal : V}


section
--variable {prior_state : state_type}

def search_stack_step
  (expand : search_expand g (state_type := state_type))
  (goal : V)
  (prior_state : state_type):
  state_type × (Option Bool) :=
  let s := (has_base_search_state.to_base_state (g:=g) prior_state)

  match s.stack with
    | [] => (prior_state, some false) -- goal not found
    | (s :: xs) =>
      if s = goal then (prior_state, some true)
      else (expand prior_state s xs, none)


lemma search_stack_step_goal_on_stack_if_terminated
  (goal : V)
  (priorState : state_type)
  (expand : search_expand g (state_type := state_type))
  :
    (search_stack_step expand goal priorState).2 = true →
     goal ∈ (has_base_search_state.to_base_state (g:=g) (search_stack_step expand goal priorState).1).stack := by
   intro terminated_with_true
   next step_did_terminate =>
   unfold search_stack_step at terminated_with_true ⊢
   simp
   split
   · next l stack_empty =>
     simp_all
   · next l head tail stack_not_empty =>
     simp_all
     split
     all_goals
      simp_all


abbrev base_invar_carries_over_expand
    (goal : V)
    (expand : search_expand g (state_type := state_type))
    (invar : base_search_state g → Prop) :=
      ∀ s : state_type, ∀ head : V, ∀ tail : List V, 
        invar (has_base_search_state.to_base_state s)
          ∧ ¬ head = goal
          ∧ (has_base_search_state.to_base_state (g:=g) s).stack = head :: tail
        → invar (has_base_search_state.to_base_state (expand s head tail))



lemma base_invar_carries_over_stack_step 
    (goal : V)
    (expand : search_expand g (state_type := state_type))
    (invar : base_search_state g → Prop)
    (invar_carries : base_invar_carries_over_expand goal expand invar):
  base_invar_carries_over_step goal (search_stack_step expand) invar := by
  unfold base_invar_carries_over_step
  intro s invar_holds_for_s
  unfold search_stack_step
  simp
  split
  · exact invar_holds_for_s 
  · split
    · exact invar_holds_for_s 
    · next head tail compose head_not_goal=>
      apply invar_carries
      rw [← and_assoc]
      repeat constructor
      · exact invar_holds_for_s
      · exact head_not_goal 
      · exact compose


end

--------------------------
-- Actual search algorithm

section
--variable {expand : search_expand g (state_type := state_type)}
variable {termination_metric : state_type → ℕ × ℕ}
variable {start_state : state_type}


abbrev termination_proof_for_expand
    (goal : V)
    (expand : search_expand g (state_type := state_type))
    (termination_metric : state_type → ℕ × ℕ):=
    ∀ state : state_type, ∀ head : V, ∀ tail : List V,
      head ≠ goal ∧ (has_base_search_state.to_base_state (g:=g) state).stack = head :: tail
    → 
    (termination_metric (expand state head tail)).1 < (termination_metric state).1 ∨
      (termination_metric (expand state head tail)).1 = (termination_metric state).1 ∧
        (termination_metric (expand state head tail)).2 < (termination_metric state).2

lemma search_stack_step_reduces_metric (goal : V)
  (expand : search_expand g (state_type := state_type))
  (termination_metric : state_type → ℕ × ℕ)
  (termination_dfs_recurse : termination_proof_for_expand goal expand termination_metric)
  :
    ∀ s : state_type, (search_stack_step expand goal s).2 = none → 
        Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2)
        (termination_metric (search_stack_step expand goal s).1) (termination_metric s) := by
    intro state did_not_terminate
    apply Prod.lex_def.mpr
    
    unfold search_stack_step at did_not_terminate
    simp_all

    have h : ¬search_prop_stack_empty (has_base_search_state.to_base_state (g:=g) state) := by
      unfold search_prop_stack_empty
      split at did_not_terminate
      all_goals
        simp_all

    unfold search_prop_stack_empty at h
    apply List.length_pos_iff_ne_nil.mpr at h
    obtain ⟨ head, tail, compose ⟩ := List.exists_of_length_succ (n:=(has_base_search_state.to_base_state (g:=g) state).stack.length - 1) (has_base_search_state.to_base_state (g:=g) state).stack (by omega) 

    unfold search_stack_step 
    simp_all
    split
    · simp_all
    · apply termination_dfs_recurse
      · constructor
        · split at did_not_terminate
          · simp_all
          · simp_all
        · exact compose

def search_exe_with_stack_step
    (expand : search_expand g (state_type := state_type))
    (metric_for_expand_proof : termination_proof_for_expand goal expand termination_metric)
    (invar_carries : base_invar_carries_over_expand goal expand (search_invar_all_basic start))
    (start_is_base_init : (has_base_search_state.to_base_state (g:=g) start_state) = (base_search_state_initial start))
    :
    Option (Path g start goal) :=
    
    let step : search_step_function g := search_stack_step expand
    let termination_proof : termination_metric_decreasing_proof goal step termination_metric :=
      search_stack_step_reduces_metric goal expand termination_metric metric_for_expand_proof

    let goal_on_stack_if_terminated : search_step_goal_on_stack_if_terminated (search_step:=step) (state_type := state_type):= by
      unfold search_step_goal_on_stack_if_terminated
      intro st goal
      apply search_stack_step_goal_on_stack_if_terminated

    let base_invars_carry : base_invar_carries_over_step goal step (search_invar_all_basic start) := by
      apply base_invar_carries_over_stack_step 
      exact invar_carries

    search_exe (start := start) (goal:=goal) (start_state:=start_state) (search_step:=step) (termination_metric := termination_metric) (termination_proof) start_is_base_init base_invars_carry goal_on_stack_if_terminated



end


end

end
