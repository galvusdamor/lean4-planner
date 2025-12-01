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
    · next h => right; exact h


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
    intro a head_adj_a
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


def bfs_last_state (g: WeightedDiGraph V E) (start : V) (goal : V): base_search_state g × Bool :=
  search_with_stack_step (goal:=goal) (start_state := base_search_state_initial start) (bfs_step_expand g) bfs_expand_metric_reduction


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



-------------


abbrev bfs_invar_on_stack_or_all_neighbours_max_order (s : base_search_state g):=
  ∀ x : s.visited, ↑x ∉ s.stack → ∀ y : V, (g.Adj x y) → s.pathOrder y ≤ 1 + s.pathOrder x

abbrev bfs_path_exists (start : V) (s : base_search_state g) :=
  ∀ u ∈ s.visited, ∃ p : Path g start u, p=p

abbrev bfs_path_as_long_as_sort_index (start : V) (s : base_search_state g) :=
  ∀ u ∈ s.visited, ∃ p : Path g start u, path_length g p = s.pathOrder u

abbrev bfs_path_as_extracted_as_long_as_sort_index (start : V) (s : base_search_state g)
    (mother_invar : search_invar_mother_is_visited s)
    (mother_invar_adj : search_invar_mother_is_adjacent start s)
    (decreasing_invar : search_invar_mother_decreasing_path_order start s):=
  ∀ u : V, ∀ h : u ∈ s.visited,
    path_length g (extract_path_to start u s h mother_invar mother_invar_adj decreasing_invar).1 = s.pathOrder u

-- stack is sorted by the path_order (i.e. distance) value
abbrev bfs_stack_sorted (s : base_search_state g) :=
  List.Sorted (fun u v => s.pathOrder u ≤ s.pathOrder v) s.stack

-- for BFS we don't sort the stack, we just append
-- this is allowed as the maximum difference of values in the stack is one (from head to tail)
abbrev bfs_stack_max_diff (s : base_search_state g) :=
  if stack_not_empty : s.stack ≠ [] then
    s.pathOrder (s.stack.head stack_not_empty) + 1 ≥ s.pathOrder (s.stack.getLast stack_not_empty)
  else true


-- this invariant is only true for BFS and Dijkstra
-- for A*, we might have to re-open
abbrev bfs_stack_shortest_path (start : V) (s : base_search_state g) :=
  ∀ u ∈ s.visited, u ∉ s.stack ∨ (if ne : s.stack ≠ [] then s.stack.head ne = u else false) → graph_distance_is g start u (s.pathOrder u)


-- for A*, a node that is not on the stack might have a shortert path that goes through some node that is actually still on the stack
-- this is due to inconsistent heuristics requiring re-opening
-- TODO here we need a "splicing lemma" for paths that states that in these cases the 
abbrev astar_stack_shortest_path (start : V) (s : base_search_state g) :=
  ∀ u ∈ s.visited, u ∉ s.stack ∨ (if ne : s.stack ≠ [] then s.stack.head ne = u else false) → (graph_distance_is g start u (s.pathOrder u) ∨ (
    ∀ p : Path g start u, path_is_shortest g p → support g p.walk ∩ s.stack ≠ ∅
  ))

abbrev bfs_expansion_in_order (start : V) (s : base_search_state g) :=
  if stack_not_empty : s.stack ≠ [] then
    let head_dist := s.pathOrder (s.stack.head stack_not_empty)
    
    ∀ u ∈ s.stack, graph_distance_ge g start u head_dist
  else true



lemma support_of_path_visited (u v : V) (w : Walk g u v)
    (state : base_search_state g)
    (mother_invar : search_invar_mother_is_visited state)
    (end_visited : v ∈ state.visited)
    :
    ∀ u ∈ support g w, u ∈ state.visited:= by
      sorry
  --intro u
  --induction path_to_head.walk
  --· unfold support
  --  simp_all
  --· unfold support
  --  next f w t adj sub_walk ih =>
  --  intro u_is_in_support
  --  simp at u_is_in_support
  --  cases u_is_in_support
  --  · sorry
  --  · sorry

theorem head_iff {α : Type u_1} {l tail : List α} {head : α} (compose : l = head :: tail) (ne_nil : l ≠ []):
    l.head ne_nil = head := by
    simp_all


lemma triangle_in_eq {start u v : V}
  (start_u_v_walk : Walk g start v) (u_in_walk : u ∈ support g start_u_v_walk)
  (u_not_v : u ≠ v)
  : graph_distance_lt g start u (walk_length g start_u_v_walk) := by
  sorry




lemma bar {start u head v : V}
  (dhead : ℕ) 
  (du_ge_dhead : graph_distance_ge g start u dhead)
  (u_ne_v : u ≠ v)
  (start_u_v_walk : Walk g start v) (u_in_walk : u ∈ support g start_u_v_walk)
  (shortest_start_head_walk : Walk g start head) (head_walk_shortest : walk_length g shortest_start_head_walk = dhead)
  (head_adj_v : g.Adj head v)
  (u_walk_shorter : walk_length g start_u_v_walk < walk_length g (extend_walk g shortest_start_head_walk head_adj_v))
  : ⊥ := by
  let start_head_v_walk : Walk g start v := extend_walk g shortest_start_head_walk head_adj_v

  have length_start_head_v_walk : walk_length g start_head_v_walk = 1 + dhead := by
    unfold start_head_v_walk
    rw [← head_walk_shortest]
    apply extend_walk_inc_length_by_one

  have shortest_u_lt_length_start_u_w_walk : graph_distance_lt g start u (walk_length g start_u_v_walk) := by
    apply triangle_in_eq
    · exact u_in_walk
    · exact u_ne_v 

  rw [length_start_head_v_walk] at u_walk_shorter
  unfold graph_distance_lt at shortest_u_lt_length_start_u_w_walk
  obtain ⟨ start_u_path, start_u_path_shorter_than_start_u_v_walk⟩ := shortest_u_lt_length_start_u_w_walk 
  --let start_u_walk : Walk g start u := start_u_path.walk
  unfold path_length at start_u_path_shorter_than_start_u_v_walk
  
  have length_start_u_le_dhead : walk_length g start_u_path.walk < 1 + dhead := by
    apply lt_trans (b:=walk_length g start_u_v_walk) 
    · exact start_u_path_shorter_than_start_u_v_walk
    · exact u_walk_shorter


  unfold graph_distance_ge at du_ge_dhead
  apply du_ge_dhead at start_u_path
  unfold path_length at start_u_path

  --(du : ℕ) (du_proof : graph_distance_is g start u du)
  --(dhead_le_du : dhead ≤ du)
  
  --have length_start_u_path_gt_du : walk_length g start_u_path.walk > du := by sorry

  omega


lemma extract_path_to_compose(start : V) (goal : V) (state : base_search_state g)
    (goal_reached : goal ∈ state.visited)
    (mother_invar : search_invar_mother_is_visited state)
    (mother_invar_adj : search_invar_mother_is_adjacent start state)
    (decreasing_invar : search_invar_mother_decreasing_path_order start state)
    (goal_ne_start : goal ≠ start)
  :
    (extract_path_to start goal state goal_reached mother_invar mother_invar_adj decreasing_invar).1.walk =
    extend_walk g (extract_path_to start (state.mother ⟨goal,goal_reached⟩) state (mother_invar ⟨goal,goal_reached⟩) mother_invar mother_invar_adj decreasing_invar).1.walk (mother_invar_adj ⟨goal,goal_reached⟩ goal_ne_start) 
    :=  by sorry






lemma foo (start : V) (goal : V):
      base_invar_carries_over_expand goal (bfs_step_expand g) (bfs_stack_shortest_path (g:=g) start) := by
        unfold base_invar_carries_over_expand
        intro state head tail ⟨prior_invar,head_is_not_goal,compose⟩ 
        unfold bfs_stack_shortest_path --at prior_invar ⊢
        intro v v_visited not_on_stack_or_head



        ----- co-invariants needed for path extraction
        have mother_invar : search_invar_mother_is_visited state := by sorry
        have mother_invar_adj : search_invar_mother_is_adjacent start state := by sorry
        have decreasing_invar : search_invar_mother_decreasing_path_order start state := by sorry
        have t_0 : search_invar_stack_is_visited state := by sorry
        have extract_length_invar : bfs_path_as_extracted_as_long_as_sort_index start state mother_invar mother_invar_adj decreasing_invar := by sorry

        unfold has_base_search_state.to_base_state at prior_invar compose not_on_stack_or_head v_visited ⊢ 
        unfold instHas_base_search_stateBase_search_state at prior_invar compose not_on_stack_or_head v_visited ⊢


        have v_not_start : v ≠ start := by sorry
        

        cases not_on_stack_or_head
        · next v_not_on_stack =>
          have h := prior_invar v 
          clear prior_invar
          unfold bfs_step_expand at v_not_on_stack v_visited ⊢
          simp at v_visited
          cases v_visited
          · next v_was_visited =>
            simp_all 
            apply h 
            by_cases hh : head = v
            · right; exact hh 
            · left ; intro hhh ; symm at hhh ; contradiction
          · next both =>
            obtain ⟨ head_adj_v, v_was_not_visited ⟩ := both
            simp_all -- contractiction. This case is impossible
        · next v_now_stack_head =>
          simp at v_now_stack_head
          obtain ⟨ stack_not_empty_after, head_after_is_v ⟩ := v_now_stack_head
          unfold bfs_step_expand at stack_not_empty_after head_after_is_v v_visited ⊢
          simp at v_visited
          
          cases v_visited
          · next v_was_visited_before=>
            -- v is *now* the head of the stack, but it was already visited before.
            -- this means it had to already have been on the stack before
            
            unfold graph_distance_is

            let path_to_v : Path g start v :=
              (extract_path_to start v state v_was_visited_before mother_invar mother_invar_adj decreasing_invar).1

            use path_to_v
            constructor
            · simp_all
              apply extract_length_invar v
            · unfold path_is_shortest
              intro p'
              by_contra p'_is_shorter
              simp_all
              
              have p'_elem_on_stack_or_v_visited :
                (∃ u ∈ support g p'.walk, u ∈ state.stack ∧ u ≠ v) ∨
                  (v ∈ state.visited ∧ ∀ u ∈ support g p'.walk, u ≠ v → u ∉ state.stack ∧ u ∈ state.visited) := by sorry
              
              cases p'_elem_on_stack_or_v_visited
              · next u_in_support_on_stack =>
                obtain ⟨u, ⟨u_in_support, ⟨ u_on_stack, u_ne_v ⟩ ⟩ ⟩ := u_in_support_on_stack
                
                have stack_nodes_have_ge_paths : bfs_expansion_in_order start state := by sorry
                unfold bfs_expansion_in_order at stack_nodes_have_ge_paths
                simp at stack_nodes_have_ge_paths

                let v_mother : V := state.mother ⟨ v, v_was_visited_before ⟩
                have v_mother_was_visited : v_mother ∈ state.visited := by apply mother_invar
                let path_to_mother : Path g start v_mother :=
                  (extract_path_to start v_mother state v_mother_was_visited mother_invar mother_invar_adj decreasing_invar).1


                have stack_before_not_empty : ¬ state.stack = [] := by
                  apply List.ne_nil_of_mem
                  apply u_on_stack

                have stack_sorted : bfs_stack_sorted state := by sorry
                

                have dist_u_ge_stack_head := stack_nodes_have_ge_paths stack_before_not_empty u u_on_stack
                have dist_u_ge_v_mother : graph_distance_ge g start u (state.pathOrder v_mother) := by
                  have u_ne_head : u ≠ head := by sorry
                  apply graph_distance_ge_lt
                  constructor
                  rotate_left
                  · unfold v_mother
                    apply le_iff_eq_or_lt.mpr
                    right
                    apply decreasing_invar (x:=⟨v, v_was_visited_before⟩)
                    exact v_not_start
                  · simp
                    sorry
                  --constructor
                  --· exact dist_u_ge_stack_head
                  --· apply le_trans
                  --  · rw [head_iff compose] 
                  --    unfold bfs_stack_sorted at stack_sorted
                  --    rw [compose] at stack_sorted
                  --    simp at stack_sorted
                  --    obtain ⟨ head_le_tail, _rest ⟩ := stack_sorted
                  --    sorry


                apply bar (g:=g) (dhead := state.pathOrder v_mother) (start:=start) (u:=u) (v:=v) (head:=v_mother) (shortest_start_head_walk:=path_to_mother.walk)
                · exact dist_u_ge_v_mother
                · exact u_ne_v 
                · exact u_in_support
                · have hh := extract_length_invar v_mother v_mother_was_visited
                  rw [← hh]
                  unfold path_length
                  rfl
                · unfold path_length at p'_is_shorter
                  unfold path_to_v at p'_is_shorter
                  --unfold extend_path at p'_is_shorter
                  --p'_is_shorter
                  --simp at p'_is_shorter
                  unfold path_to_mother
                  unfold v_mother
                  rw [← extract_path_to_compose (g:=g) (state:=state) (start:=start) (goal:=v) (goal_reached:=v_was_visited_before) (mother_invar := mother_invar) (mother_invar_adj:=mother_invar_adj) (decreasing_invar := decreasing_invar)]
                  · exact p'_is_shorter 
                  · exact v_not_start
              · next both =>
                obtain ⟨v_visited, support_not_on_stack⟩ := both 
                obtain ⟨ w,path_start_w,w_adj_v,v_not_earlier_in_path,p'_compose⟩ := split_path_at_end g p' (Ne.symm v_not_start)
                have path_start_w_length : path_length g path_start_w + 1 = path_length g p' := by
                  rw [p'_compose]
                  apply Eq.symm
                  rw [add_comm]
                  apply extend_path_inc_length_by_one
                rw [← path_start_w_length] at p'_is_shorter
                clear path_start_w_length
                have w_in_supp : w ∈ support g p'.walk := by
                  rw [p'_compose]
                  rw [extend_path_extends_support]
                  simp
                  left
                  apply path_goal_in_support
                have w_ne_v : w ≠ v := by
                  by_contra w_eq_v
                  rw [← w_eq_v] at v_not_earlier_in_path
                  have w_in_supp : w ∈ support g path_start_w.walk := path_goal_in_support g path_start_w
                  contradiction
                have w_visited : w ∈ state.visited := (support_not_on_stack w w_in_supp w_ne_v).right
                have w_not_on_stack : w ∉ state.stack := (support_not_on_stack w w_in_supp w_ne_v).left

                have update_invar : bfs_invar_on_stack_or_all_neighbours_max_order state := by sorry
                --unfold bfs_invar_on_stack_or_all_neighbours_max_order at update_invar
                have w_nei_updated := update_invar ⟨w, w_visited⟩ w_not_on_stack v w_adj_v
                have w_dist_is_order := prior_invar w w_visited (Or.inl w_not_on_stack)
                unfold graph_distance_is at w_dist_is_order
                obtain ⟨shortest_to_w, ⟨w_len,is_shortest⟩ ⟩ := w_dist_is_order 
                unfold path_is_shortest at is_shortest
                simp at w_nei_updated
                rw [←w_len] at w_nei_updated
                have path_to_v_has_order_length := extract_length_invar v v_was_visited_before
                unfold path_to_v at p'_is_shorter
                rw [path_to_v_has_order_length] at p'_is_shorter
                clear path_to_v_has_order_length
                have path_start_w_shorter_than_shortest := lt_of_lt_of_le p'_is_shorter w_nei_updated
                have path_start_w_longer_than_shortest := is_shortest path_start_w
                omega
          · next both =>
            obtain ⟨ head_adj_v, v_not_visited_before ⟩ := both
            simp_all
            split
            · next visited_empty =>
              clear stack_not_empty_after head_after_is_v
              have head_in_stack : head ∈ state.stack := by simp_all
              apply t_0 at head_in_stack
              simp_all -- by contradiction
            · next visited_not_empty =>
              by_cases tail_empty : tail = []
              · simp_all
                clear stack_not_empty_after head_after_is_v
                unfold graph_distance_is
                -- we newly inserted v as the neighbour of head and it became the stack head immediately
                
                have head_was_visited_before : head ∈ state.visited := by simp_all
                let path_to_head : Path g start head :=
                  (extract_path_to start head state head_was_visited_before mother_invar mother_invar_adj decreasing_invar).1
                have support_visited : ∀ u ∈ support g path_to_head.walk, u ∈ state.visited := by
                  apply support_of_path_visited
                  · exact mother_invar 
                  · exact head_was_visited_before 

                let path_to_v : Path g start v := extend_path g path_to_head head_adj_v (by
                  by_contra v_in_support
                  have v_visited_before := support_visited v v_in_support
                  contradiction)
                use path_to_v
                constructor
                · unfold bfs_path_as_extracted_as_long_as_sort_index at extract_length_invar 
                  have hh := extract_length_invar head head_was_visited_before
                  rw [← hh]
                  unfold path_to_v
                  unfold path_to_head
                  apply extend_path_inc_length_by_one
                · unfold path_is_shortest
                  intro p'
                  by_contra p'_is_shorter
                  simp at p'_is_shorter

                  have v_not_on_stack_before : v ∉ state.stack := by
                    by_contra v_on_stack
                    apply t_0 at v_on_stack
                    contradiction
                  
                  have p'_elem_on_stack_or_v_visited :
                    (∃ u ∈ support g p'.walk, u ∈ state.stack) ∨ v ∈ state.visited := by sorry
                  
                  cases p'_elem_on_stack_or_v_visited
                  · next u_in_support_on_stack =>
                    obtain ⟨u, ⟨u_in_support, u_on_stack ⟩ ⟩ := u_in_support_on_stack
                    have u_not_v : u ≠ v := by
                      simp_all
                      by_contra head_eq_v
                      rw [head_eq_v] at v_not_on_stack_before
                      simp_all
                    
                    have stack_nodes_have_ge_paths : bfs_expansion_in_order start state := by sorry
                    unfold bfs_expansion_in_order at stack_nodes_have_ge_paths
                    have stack_before_not_empty : ¬ state.stack = [] := by
                      apply List.ne_nil_of_mem
                      apply u_on_stack
                    simp at stack_nodes_have_ge_paths

                    have dist_u_ge_stack_head := stack_nodes_have_ge_paths stack_before_not_empty u u_on_stack
                    rw [head_iff compose] at dist_u_ge_stack_head
                    apply bar (g:=g) (dhead := state.pathOrder head) (start:=start) (u:=u) (v:=v) (head:=head) (shortest_start_head_walk:=path_to_head.walk)
                    --· apply prior_invar
                    --  · exact head_was_visited_before
                    --  · simp_all 
                    · exact dist_u_ge_stack_head
                    · exact u_not_v 
                    · exact u_in_support 
                    · have hh := extract_length_invar head head_was_visited_before
                      rw [← hh]
                      unfold path_length
                      rfl
                    · unfold path_length at p'_is_shorter
                      unfold path_to_v at p'_is_shorter
                      unfold extend_path at p'_is_shorter
                      simp at p'_is_shorter
                      exact p'_is_shorter 
                    --· exact head_adj_v 
                  · contradiction
              · -- tail is not empty: this is impossible as v becomes the head
                simp_all
                have v_was_on_stack : v ∈ state.stack := by
                  rw [compose]
                  apply List.mem_cons.mpr
                  right
                  simp_all
                  apply List.mem_of_head?
                  rw [← head_after_is_v]
                  apply List.head?_eq_some_head
                have v_visited_before : v ∈ state.visited := t_0 v v_was_on_stack
                simp_all

lemma gak {start v : V } (state : base_search_state g)
  (path_to_v p' : Path g start v)
  (p'_is_shorter : path_length g p' < path_length g path_to_v)
  (v_visited : v ∈ state.visited)
  (support_not_on_stack : ∀ u ∈ support g p'.walk, u ≠ v → u ∉ state.stack)
  : ⊥ := by
    sorry



theorem bfs_is_optimal(g: WeightedDiGraph V E) (start : V) (goal : V)
    (returned_path : Option.isSome (bfs g start goal)):
    path_is_shortest g ((bfs g start goal).get returned_path) := by

    let final := search_with_stack_step (goal:=goal) (start_state := base_search_state_initial start) (bfs_step_expand g) bfs_expand_metric_reduction
    let final_state := final.1

    -- general properties
    --have h_4_1 : ¬ search_prop_stack_empty final_state := by sorry
    have h_4 : search_prop_stack_head_is_goal goal final_state := by
      --intro terminated_with_goal_found 
      --unfold search_prop_stack_head_is_goal
      unfold final_state
      unfold final
      unfold search_with_stack_step
      simp
      unfold search_internal
      apply search_recurse_obtain_base_termination_property goal (base_search_state_initial start) (property_after_termination := search_prop_stack_head_is_goal goal ) (terminated_with := true) (search_step := search_stack_step (bfs_step_expand g))
      · intro s
        apply search_stack_step_goal_stack_head_if_terminated
      · unfold bfs at returned_path
        unfold search_exe_with_stack_step at returned_path
        unfold search_exe at returned_path
        simp_all
        apply returned_path

    have t_0 : search_invar_stack_is_visited final_state := by
      unfold final_state
      unfold final
      unfold search_with_stack_step
      simp only []
      apply search_returns_with_stack_visited (state_type := base_search_state g) (start_state := base_search_state_initial start) (start := start)
      · rfl
      · apply base_invar_carries_over_stack_step
        apply bfs_expand_keeps_base_invars

    have h_3 : search_prop_goal_visited goal final_state := by
      apply t_0
      unfold search_prop_stack_head_is_goal at h_4 
      apply List.eq_cons_of_mem_head? at h_4
      rw [h_4]
      simp

    have t_1 : search_invar_mother_is_visited final_state := by
      unfold final_state
      unfold final
      unfold search_with_stack_step
      simp only []
      apply search_returns_with_mother_visited (state_type := base_search_state g) (start_state := base_search_state_initial start) (start := start)
      · rfl
      · apply base_invar_carries_over_stack_step
        apply bfs_expand_keeps_base_invars

    have t_2 : search_invar_mother_is_adjacent start final_state := by
      unfold final_state
      unfold final
      unfold search_with_stack_step
      simp only []
      apply search_returns_with_mother_adjacent (state_type := base_search_state g) (start_state := base_search_state_initial start) (start := start)
      · rfl
      · apply base_invar_carries_over_stack_step
        apply bfs_expand_keeps_base_invars

    have t_3 : search_invar_mother_decreasing_path_order start final_state := by
      unfold final_state
      unfold final
      unfold search_with_stack_step
      simp only []
      apply search_returns_with_mother_decreasing (state_type := base_search_state g) (start_state := base_search_state_initial start) (start := start)
      · rfl
      · apply base_invar_carries_over_stack_step
        apply bfs_expand_keeps_base_invars


    -- BFS specific ones
    have i_1 : bfs_stack_shortest_path start final_state := by sorry

    have h_2 : bfs_path_as_extracted_as_long_as_sort_index start final_state t_1 t_2 t_3 := by sorry


    have h : graph_distance_is g start goal (final_state.pathOrder goal) := by
      unfold graph_distance_is
      unfold bfs_stack_shortest_path at i_1
      have i_1' := i_1 goal h_3
      have i_1'' : graph_distance_is g start goal (final_state.pathOrder goal) := by
        unfold search_prop_stack_head_is_goal at h_4
        apply i_1'
        right
        simp_all
      unfold graph_distance_is at i_1''
      exact i_1''


    unfold bfs
    unfold search_exe_with_stack_step
    unfold search_exe
    unfold path_is_shortest
    intro p'
    unfold graph_distance_is at h 
    obtain ⟨p, ⟨ p_path_length, p_is_shortest ⟩ ⟩  := h

    unfold bfs_path_as_extracted_as_long_as_sort_index at h_2
    have prop := h_2 goal
    clear h_2
    simp_all
    unfold final_state at prop
    unfold final at prop
    unfold search_with_stack_step at prop
    simp_all
    unfold has_base_search_state.to_base_state
    unfold instHas_base_search_stateBase_search_state
    rw [prop]
    clear prop t_1 t_2 t_3
    unfold final_state at p_path_length
    unfold final at p_path_length
    unfold search_with_stack_step at p_path_length
    simp_all
    rw [← p_path_length]
    unfold path_is_shortest at p_is_shortest
    simp_all

