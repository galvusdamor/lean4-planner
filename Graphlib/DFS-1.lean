import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Bool.AllAny
import Mathlib.Data.FinEnum

import Graphlib.Lists
import Graphlib.Basic

set_option trace.split.failure true


------ DFS implementation and proof ------


/-- `NodePathPair` is the triple that is used for the stack in the `inner_DFS` algorithm, having
the fields `node : V`, `path : Path G start node`, and `reached_nodes_proofs : (support G path.walk).toFinset ⊆ visited`. -/
structure NodePathPair (start : V) (visited : Finset V)  where
  node : V
  path : Path G start node
  reached_nodes_proofs : (support G path.walk).toFinset ⊆ visited
  --deriving DecidableEq


/-- `inner_DFS` is the main part of the algorithm depth first search,
called from `DFS` with an the `start` node in the visited list and a first `NodePathPair` with the
`start` vertex in the first coordinate as an input, a `WeightedDiGraph V E`,
a start node `start : V`, and a goal node `goal : V`as imput. -/
def inner_dfs [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (visited : Finset V) (stack : List (NodePathPair g start visited)) (goal : V) : (Option (Path g start goal)) :=
  match stack with
    | [] => none -- goal not found
    | (s :: xs) =>
    if h : s.node = goal then some (h ▸ s.path)
    else
      let newly_visited : Finset V := (Finset.univ).filterMap
        (λ v => if @decide (g.Adj s.node v) (g.instDecAdj s.node v) ∧ v ∉ visited
                  then some v
                  else none)
        (by intro a a' b a_1 a_2; simp_all) -- filter neighbors to expand the visited list

      let new_visited := visited ∪ newly_visited

      let new_nodes_neighbors : List (NodePathPair g start new_visited) :=
      (FinEnum.toList (Finset.univ : Finset V)).filterMap
       (λ v =>
         if notVisited : v ∉ visited then
          have := g.instDecAdj s.node v -- We need this later.
          if d : decide (g.Adj s.node v) then
            let oldpath : Path g start s.node := s.path
            let w : Path g start v := extend_path g oldpath (by
              exact of_decide_eq_true d
            ) (by
              let oldpath_proof : (support g s.path.walk).toFinset ⊆ visited := s.reached_nodes_proofs
              simp [oldpath]
              rw [← List.mem_toFinset]
              exact Set.notMem_subset oldpath_proof notVisited
            )
            let r : NodePathPair g start new_visited := NodePathPair.mk v w (by -- proof that support(path) ⊆ new_visisted
              simp [new_visited,w,extend_path_extends_support]
              apply Finset.union_subset_union s.reached_nodes_proofs
              simp_all only [decide_eq_true_eq, Finset.singleton_subset_iff, Finset.mem_filterMap,
                Finset.mem_univ, Option.ite_none_right_eq_some, Option.some.injEq, true_and,
                exists_eq_right, not_false_eq_true, and_true, newly_visited]
              exact of_decide_eq_true d
            )
            r
          else
            none -- edge does not exist
        else
          none -- target node has already been visited
      ) -- filter neighbors to expand stack

      let new_stack_old_nodes : List (NodePathPair g start new_visited):= List.map (fun npp =>
        NodePathPair.mk npp.node npp.path (by
          let partPath := npp.reached_nodes_proofs
          simp [new_visited]
          apply subset_trans
          exact partPath
          apply Finset.subset_union_left
        )
      ) xs  -- updates old stack with paths and updates type

      let new_stack : List (NodePathPair g start new_visited):=
        new_nodes_neighbors ++ new_stack_old_nodes -- add neighbors in front to stack

      inner_dfs g start new_visited new_stack  goal
termination_by (Fintype.card V - visited.card, stack.length) -- must be a well-founded relation/measure
decreasing_by
  ·     simp_wf
        -- case distinction: if the newly_visited set is empty, then the first number stays the same. So we need to prove that size of the stack decreases. This is true as no new elements get added
        by_cases no_new_visited : newly_visited = ∅
        simp [newly_visited] at no_new_visited
        simp [no_new_visited]
        apply Prod.Lex.right
        simp [Nat.add_comm]
        intro a
        intro anotvisited
        have aNotInNewlyVisited : a ∉ newly_visited := by
          unfold newly_visited
          simp [no_new_visited]
        simp [newly_visited] at aNotInNewlyVisited
        intro adj
        apply aNotInNewlyVisited at adj
        contradiction

        -- helper theorem on the visited list
        have newly_not_yet_visited : visited ∩ newly_visited = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro xNotInIntersect
          intro xInIntersect
          simp [newly_visited] at xInIntersect
          have xInVisi := xInIntersect.left
          have xNotInVisi := xInIntersect.right.right
          contradiction

        -- first case done
        apply Prod.Lex.left
        -- first half of the Lex.left
        apply Nat.sub_lt_sub_left
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        rw [Finset.eq_empty_iff_forall_notMem] at no_new_visited
        simp at no_new_visited
        apply Exists.elim no_new_visited
        intro b
        intro bInNewlyVisited
        exists b
        apply And.intro
        simp
        intro bInVisited
        have bInIntersect : b ∈ visited ∩ newly_visited := by
          apply Finset.mem_inter_of_mem
          exact bInVisited
          exact bInNewlyVisited
        simp_all only [Finset.notMem_empty]
        simp_all [Finset.subset_univ]

        -- second half of the Lex.left
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · rw [Finset.eq_empty_iff_forall_notMem] at no_new_visited
          simp at no_new_visited
          apply Exists.elim no_new_visited
          intro b
          intro bInNewlyVisited
          exists b
          apply And.intro
          · simp
            right
            simp [newly_visited] at bInNewlyVisited
            exact bInNewlyVisited
          · intro bInVisited
            have bInIntersect : b ∈ visited ∩ newly_visited := by
              apply Finset.mem_inter_of_mem bInVisited bInNewlyVisited
            simp_all
        · simp_all



/-- `DFS`is the algorithm depth first search, expecting a `WeightedDiGraph V E`, a start node `start : V`and a goal node `goal : V`as imput. -/
def dfs [FinEnum V] [DecidableEq V] [DecidableEq E] (g: WeightedDiGraph V E) (start : V) (goal : V) : (Option (Path g start goal)) :=
    let emptyW : Walk g start start := Walk.nil
    let emptyP : Path g start start := Path.mk emptyW (by
      simp [emptyW]
      unfold support
      simp
    )
    -- initially the visited list only contains start and we have a path that goes from start to itself (a nil path)
    let reached_nodes_proof : (support g emptyW).toFinset ⊆ {start} := by
      simp [emptyW]
      right
      simp [support]
    let p : NodePathPair g start {start} := NodePathPair.mk start emptyP reached_nodes_proof
    inner_dfs g start {start} [p] goal

theorem dfs_is_sound (g: WeightedDiGraph V E) (start : V) (goal : V) :
    (Option.isSome (dfs g start goal) → (∃ x : (Path g start goal), x = x)) := by
  intro h -- Option.isSome true on some and false on none, x = x since we need a formula
  constructor -- since goal is existence
  rfl
  let w := Option.get (dfs g start goal) -- Option.get extracts value of returned some and fails otherwise
  apply w
  simp_all

-------------------------------------------------------------------------------------------------
--
-- heute: Funktion auf Listen. Das eigentliche Lemma ist listFind, listFind.go ist eine Hilfe für die Induktion
--
-------------------------------------------------------------------------------------------------

-- heute: allgemeinstes Lemma. Ein Beweis für dieses Lemma könnte reichen. einfachere typen
lemma listFind_general
  (α : Type)
  (list : List α)
  (p : α → Bool)
  (hasElem : (list.findFinIdx? p).isSome) :
    p list[(list.findFinIdx? p).get hasElem] := by
  rcases Option.isSome_iff_exists.1 hasElem with ⟨i, def_some_i⟩
  simp_rw [def_some_i] -- MG: normal "simp" did not work here, but this does!
  rw [List.findFinIdx?_eq_some_iff] at def_some_i
  simp_all

lemma listFind.go
  (g: WeightedDiGraph V E) (start : V) (visited : Finset V)
  (x : V)
  (list : List (NodePathPair g start visited))
  (curlist : List (NodePathPair g start visited))
  (sameList : curlist = list)
  (h : curlist.length = list.length)
  (hasElem : (List.findFinIdx?.go (fun elem => elem.node = x) list curlist 0 h).isSome = true):
    list[(List.findFinIdx?.go (fun elem => elem.node = x) list curlist 0 h).get hasElem].node = x
  := by
      induction curlist
      · have noElemIn :
          (List.findFinIdx?.go (fun elem : NodePathPair g start visited=> decide (elem.node = x)) list [] 0 h).isSome = false := by
          simp
          rfl
        rw [noElemIn] at hasElem
        contradiction
      next head tail ih =>
        simp_all
        by_cases head_is_x : head.node = x
        · unfold List.findFinIdx?.go
          simp_all
          sorry
        · unfold List.findFinIdx?.go
          simp
          sorry

lemma listFind
  (g: WeightedDiGraph V E) (start : V) (visited : Finset V)
  (x : V)
  (list : List (NodePathPair g start visited))
  (hasElem : (list.findFinIdx? (fun elem => elem.node = x)).isSome = true):
    list[(list.findFinIdx? (fun elem => elem.node = x)).get hasElem].node = x
  := by
    unfold List.findFinIdx?
    let list' := list
    apply listFind.go
    sorry


-------------------------------------------------------------------------------------------------
--
-- New implementation that uses a monad-like structure.
--
-------------------------------------------------------------------------------------------------

structure dfs_state [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) where
    visited : Finset V
    stack : List (NodePathPair g start visited)

--- invariant for all nodes
-- TODO: should use dep_invar_for_x instead
abbrev dep_invar[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : dfs_state g start):=
      ∀ x : s.visited, (∃ y ∈ s.stack, y.node = x) ∨ ∀ y : V, (g.Adj x y) → y ∈ s.visited

-- invariant formulated for one node x only
abbrev dep_invar_for_x[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (s : dfs_state g start)
    (x : V):=
      x ∈ s.visited → (∃ y ∈ s.stack, y.node = x) ∨ ∀ y : V, (g.Adj x y) → y ∈ s.visited


def inner_dfs_not_really_monad_compute_next[FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    (priorState : dfs_state g start)
    (s : NodePathPair g start priorState.visited)
    (xs : List (NodePathPair g start priorState.visited)):
    (dfs_state g start) × (Option (Option (Path g start goal))) :=
      let newly_visited : Finset V := (Finset.univ).filterMap
        (λ v => if @decide (g.Adj s.node v) (g.instDecAdj s.node v) ∧ v ∉ priorState.visited
                  then some v
                  else none)
        (by intro a a' b a_1 a_2; simp_all) -- filter neighbors to expand the visited list

      let new_visited := priorState.visited ∪ newly_visited

      let new_nodes_neighbors : List (NodePathPair g start new_visited) :=
      (FinEnum.toList (Finset.univ : Finset V)).filterMap
       (λ v =>
         if notVisited : v ∉ priorState.visited then
          have := g.instDecAdj s.node v -- We need this later.
          if d : decide (g.Adj s.node v) then
            let oldpath : Path g start s.node := s.path
            let w : Path g start v := extend_path g oldpath (by
              exact of_decide_eq_true d
            ) (by
              let oldpath_proof : (support g s.path.walk).toFinset ⊆ priorState.visited := s.reached_nodes_proofs
              simp [oldpath]
              rw [← List.mem_toFinset]
              apply Set.notMem_subset
              exact oldpath_proof
              exact notVisited
            )
            let r : NodePathPair g start new_visited := NodePathPair.mk v w (by -- proof that support(path) ⊆ new_visisted
              simp [new_visited,w,extend_path_extends_support]
              apply Finset.union_subset_union
              exact s.reached_nodes_proofs
              simp_all only [decide_eq_true_eq, Finset.singleton_subset_iff, Finset.mem_filterMap, Finset.mem_univ, Option.ite_none_right_eq_some, Option.some.injEq, true_and, exists_eq_right, newly_visited]
              simp
              exact of_decide_eq_true d
            )
            r
          else
            none -- edge does not exist
        else
          none -- target node has already been visited
      ) -- filter neighbors to expand stack

      let new_stack_old_nodes : List (NodePathPair g start new_visited):= List.map (fun npp =>
        NodePathPair.mk npp.node npp.path (by
          let partPath := npp.reached_nodes_proofs
          simp [new_visited]
          apply subset_trans
          exact partPath
          apply Finset.subset_union_left
        )
      ) xs  -- updates old stack with paths and updates type

      let new_stack : List (NodePathPair g start new_visited):=
        new_nodes_neighbors ++ new_stack_old_nodes -- add neighbors in front to stack

      let nextState := dfs_state.mk new_visited new_stack
      (nextState, none)


def inner_dfs_not_really_monad [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    (priorState : dfs_state g start) :
    (dfs_state g start) × (Option (Option (Path g start goal))) :=
  match priorState.stack with
    | [] => (priorState, some none) -- goal not found
    | (s :: xs) =>
    if h : s.node = goal then (priorState, some (some (h ▸ s.path)))
    else
      inner_dfs_not_really_monad_compute_next g start goal priorState s xs

lemma dfs_not_really_monad_if_goal_return_same_state
    (g: WeightedDiGraph V E) (start : V) (goal : V) (priorState : dfs_state g start)
    (stack_not_empty : priorState.stack ≠ [])
    (stack_head_is_goal : (priorState.stack.head stack_not_empty).node = goal)
    :
      (inner_dfs_not_really_monad g start goal priorState).1 = priorState := by
        unfold inner_dfs_not_really_monad
        aesop

omit [DecidableEq E] in
lemma nodePathPairNodeKeepsEquality
    (g: WeightedDiGraph V E) (start : V) (visited : Finset V)
    (eq : visited = visited') (p : NodePathPair g start visited)  :
    p.node = (eq ▸ p).node := by
      subst eq
      simp_all only

def nodePathPairNodeKeepsSubset
    (visited : Finset V)
    (sub : visited ⊆ visited') :
    (NodePathPair g start visited) → (NodePathPair g start visited') := by
      intro small
      have npp : NodePathPair g start visited' :=
        NodePathPair.mk small.node small.path (by
          let partPath := small.reached_nodes_proofs
          apply subset_trans
          exact partPath
          exact sub
        )
      exact npp



lemma dfs_not_really_monad_invar_one_step_stack_empty
    (g: WeightedDiGraph V E) (start : V) (goal : V) (priorState : dfs_state g start)
    (stack_empty: priorState.stack = []):
      dep_invar g start priorState → dep_invar g start (inner_dfs_not_really_monad g start goal priorState).1 := by
        intro priorInvar
        unfold inner_dfs_not_really_monad
        simp_all
        exact priorInvar

lemma dfs_not_really_monad_invar_one_step_head_is_goal
    (g: WeightedDiGraph V E) (start : V) (goal : V) (priorState : dfs_state g start)
    (stack_not_empty: priorState.stack ≠ [])
    (stack_head_is_goal: (priorState.stack.head stack_not_empty).node = goal):
      dep_invar g start priorState → dep_invar g start (inner_dfs_not_really_monad g start goal priorState).1 := by
        intro priorInvar
        unfold dep_invar
        intro x
        by_cases x_is_on_stack : (∃ y ∈ priorState.stack, y.node = x)
        · left
          clear priorInvar
          convert x_is_on_stack
          all_goals
            simp [inner_dfs_not_really_monad]
            aesop
        · right
          unfold dep_invar at priorInvar
          specialize priorInvar ⟨ x.1, ?_⟩
          · have ⟨ x_as_v , x_in_after_inner ⟩ := x
            simp
            convert x_in_after_inner
            simp_all [dfs_not_really_monad_if_goal_return_same_state]
          · apply Or.resolve_left at priorInvar
            simp_all
            convert priorInvar
            simp_all [dfs_not_really_monad_if_goal_return_same_state]



-- if the node was not visited before, the invariant does not say anything about it!
lemma dfs_not_really_monad_invar_one_step_head_is_not_goal_node_x_not_previously_visited
    (g: WeightedDiGraph V E) (start : V) (goal : V) (priorState : dfs_state g start)
    (stack_not_empty: priorState.stack ≠ [])
    (stack_head_is_not_goal: (priorState.stack.head stack_not_empty).node ≠ goal)
    (x : V) (x_in_prior_visited : x ∉ priorState.visited):
        dep_invar_for_x g start (inner_dfs_not_really_monad g start goal priorState).1 x := by
        unfold dep_invar_for_x
        intro x_is_now_visited
        left
        -- we know that the node x has been added newly to visited. This is only possible
        -- if was added to the stack by expanding a neighbour
        unfold inner_dfs_not_really_monad
        split
        · next stack_empty' =>
          exact False.elim (stack_not_empty stack_empty')
        · next _ignore stack_head rest_stack stack_composition =>
          simp_all
          refine' Exists.intro ?w ?hh
          · simp_all
            unfold inner_dfs_not_really_monad_compute_next
            simp_all
            sorry
          sorry
          /- -- MG: commented unused/broken part here
          next stack_head rest_stack stack_composition is_goal' =>
            have contra: stack_head.node ≠ goal := by
              simp_all
            exact False.elim (contra is_goal')
          simp_all
          sorry
          -/

lemma dfs_not_really_monad_invar_one_step_head_is_not_goal_node_x_previously_visited_and_stack_head
    (g: WeightedDiGraph V E) (start : V) (goal : V) (priorState : dfs_state g start)
    (stack_not_empty: priorState.stack ≠ [])
    (stack_head_is_not_goal: (priorState.stack.head stack_not_empty).node ≠ goal)
    (x : V)
    (x_is_stack_head : (priorState.stack.head stack_not_empty).node = x):
        dep_invar_for_x g start (inner_dfs_not_really_monad g start goal priorState).1 x := by
      unfold dep_invar_for_x
      intro x_is_now_in_visited
      simp_all
      -- x was the stack of the head, so its neighbours got inserted into visited list
      right
      intro y
      intro x_nei_y
      unfold inner_dfs_not_really_monad
      split
      · next stack_empty => exact False.elim (stack_not_empty stack_empty)
      simp_all
      unfold inner_dfs_not_really_monad_compute_next
      simp_all
      apply Decidable.em

lemma dfs_not_really_monad_invar_one_step_head_is_not_goal_node_x_previously_visited_and_not_on_stack
    (g: WeightedDiGraph V E) (start : V) (goal : V) (priorState : dfs_state g start)
    (stack_not_empty: priorState.stack ≠ [])
    (stack_head_is_not_goal: (priorState.stack.head stack_not_empty).node ≠ goal)
    (x : V) (x_in_prior_visited : x ∈ priorState.visited)
    (x_was_not_on_previous_stack : ∀ y ∈ priorState.stack, y.node ≠ x):
      dep_invar_for_x g start priorState x →
        dep_invar_for_x g start (inner_dfs_not_really_monad g start goal priorState).1 x := by
      intro priorInvar
      unfold dep_invar_for_x
      intro x_is_in_new_visited
      right -- this was true previously, so also now
      intro y
      intro x_nei_y
      unfold inner_dfs_not_really_monad
      split
      next stack_empty' => exact False.elim (stack_not_empty stack_empty')
      split
      next stack_head rest_stack stack_composition is_goal' =>
        have contra: stack_head.node ≠ goal := by
          simp_all
        exact False.elim (contra is_goal')
      unfold inner_dfs_not_really_monad_compute_next
      next stack_head rest_stack stack_composition s_not_goal =>
        simp_all
        have ⟨ x_not_stack_head , x_not_in_rest_stack ⟩ := x_was_not_on_previous_stack
        left
        cases priorInvar with
        | inl a =>
          obtain ⟨w, w_in_stack, w_is_x⟩ := a
          exact False.elim (x_not_in_rest_stack w w_in_stack w_is_x)
        | inr a =>
          exact a y x_nei_y

omit [DecidableEq E] in
lemma nodePathPairNodeKeepsEqualityForCast
  (g: WeightedDiGraph V E) (start : V) (visited : Finset V)
    (eq : visited = visited')
    (eqq : NodePathPair g start visited = NodePathPair g start visited')
    (p : NodePathPair g start visited):
    (cast eqq p).node = p.node := by
      subst eq
      simp_all only [cast_eq]

lemma dfs_not_really_monad_invar_one_step_head_is_not_goal_node_x_previously_visited_and_on_stack_but_not_head
    (g: WeightedDiGraph V E) (start : V) (goal : V) (priorState : dfs_state g start)
    (stack_not_empty: priorState.stack ≠ [])
    (stack_head_is_not_goal: (priorState.stack.head stack_not_empty).node ≠ goal)
    (x : V) (x_in_prior_visited : x ∈ priorState.visited)
    (x_is_not_stack_head : (priorState.stack.head stack_not_empty).node ≠ x)
    (x_was_on_previous_stack : ∃ y ∈ priorState.stack, y.node = x):
        dep_invar_for_x g start (inner_dfs_not_really_monad g start goal priorState).1 x := by
      intro x_is_visited_afterwards
      left -- it still has to be on the stack
      unfold inner_dfs_not_really_monad
      split
      next stack_empty' => exact False.elim (stack_not_empty stack_empty')
      next stack_head rest_stack stack_composition =>
      simp_all only [List.head_cons, ne_eq, List.mem_cons, exists_eq_or_imp, false_or]
      --split -- Malvin: not possible here
      -- MG: Could do `by_cases h : stack_head.node = goal` but
      -- then rw [h] also leads to "motive not type correct" :-/
      let isNodeX : NodePathPair g start priorState.visited → Bool := (fun elem => elem.node = x)
      let priorIndexOpt: Option (Fin priorState.stack.length) := priorState.stack.findFinIdx? isNodeX
      let priorIndex : Fin priorState.stack.length := priorIndexOpt.get $ by
        unfold priorIndexOpt
        convert List.isSome_findFinIdx?
        symm
        rw [List.any_iff_exists_prop]
        simp_all

      -- reststack has at least one element
      have reststack_at_least_one : 1 ≤ rest_stack.length := by
        -- MG: writing "x_was_on_previous_stack.2.1" here is dangerous because it would do exists-elim
        obtain ⟨_,h,_⟩  := x_was_on_previous_stack
        apply List.length_pos_of_mem h

      -- stack has at least two elements
      have priorState_stack_at_least_two : 2 ≤ priorState.stack.length := by simp_all

      have priorIndex_at_least_one : Fin.mk 1 (by omega) ≤ priorIndex := by
        unfold priorIndex priorIndexOpt
        simp_all
        rw [Fin.le_def]
        simp
        -- rw [stack_composition] -- Malvin: Motive not correct ???

        --conv =>
        --  right
        unfold List.findFinIdx?
        unfold List.findFinIdx?.go
        sorry

      let priorFromEnd : Fin priorState.stack.length := ⟨ priorState.stack.length - priorIndex - 1, by omega⟩

      let inner_dfs_result := (inner_dfs_not_really_monad_compute_next g start goal priorState stack_head rest_stack)
      let outer_dfs_result := (inner_dfs_not_really_monad g start goal priorState)
      have visiteds_are_the_same :
        inner_dfs_result.1.visited = outer_dfs_result.1.visited := by
        unfold outer_dfs_result
        unfold inner_dfs_not_really_monad
        simp_all
        rfl
      have myTypeRewrite :=
        nodePathPairNodeKeepsEquality g start inner_dfs_result.1.visited visiteds_are_the_same

      let result_stack_length := inner_dfs_result.1.stack.length

      have prior_stack_size : priorState.stack.length ≥ 1 := by simp_all
      have prior_stack_size_two : priorState.stack.length ≥ 2 := by simp_all
      have stack_size_not_too_decreasing :
        result_stack_length + 1 ≥ priorState.stack.length := by
          simp_all [result_stack_length, inner_dfs_result, inner_dfs_not_really_monad_compute_next]

      have priorIndexNatGreaterOne : priorIndex.val ≥ 1 := by
        simp_all only [ge_iff_le, inner_dfs_result, outer_dfs_result, priorIndex, priorIndexOpt, isNodeX]
        obtain ⟨w, h⟩ := x_was_on_previous_stack
        obtain ⟨left, right⟩ := h
        subst right
        exact priorIndex_at_least_one

      have prior_from_end_not_max : priorFromEnd < priorState.stack.length - 1 := by
          obtain ⟨w, h⟩ := x_was_on_previous_stack
          obtain ⟨left, right⟩ := h
          simp_all only [priorFromEnd, ne_eq, reduceCtorEq, not_false_eq_true, ge_iff_le, List.length_cons, le_add_iff_nonneg_left, zero_le, Nat.reduceLeDiff, add_le_add_iff_right, add_tsub_cancel_right, inner_dfs_result, outer_dfs_result, result_stack_length, priorIndex, priorIndexOpt, isNodeX]
          subst right
          omega

      let indexInResult : Fin inner_dfs_result.1.stack.length :=
        ⟨inner_dfs_result.1.stack.length - 1 - priorFromEnd, by omega⟩

      let priorFromEndOtherLimit : Fin inner_dfs_result.1.stack.reverse.length := ⟨ priorFromEnd, by
        have : inner_dfs_result.1.stack.length = inner_dfs_result.1.stack.reverse.length := List.length_reverse.symm
        omega⟩

      refine' Exists.intro ?w ?_
      · simp_all
        exact inner_dfs_result.1.stack.reverse.get priorFromEndOtherLimit
      · constructor
        · simp
          sorry -- Malvin: how to get rid of cast here? split before sorry is not possible!
        · unfold inner_dfs_result inner_dfs_not_really_monad_compute_next
          simp_all
          rw [List.getElem_append_left]
          · rw [List.getElem_reverse]
            · simp_all
              rw [nodePathPairNodeKeepsEqualityForCast]
              · simp_all [priorFromEndOtherLimit, priorFromEnd]
                have arith_helper : rest_stack.length - 1 - (rest_stack.length + 1 - priorIndex.val - 1) = priorIndex.val - 1 := by
                  -- needed for the next omega in arith_helper -- MG: so we can move it here to avoid clutter hypotheses
                  have help42: ((↑priorIndex):Nat) ≤ rest_stack.length := by
                    have help43: ((↑priorIndex):Nat) < priorState.stack.length := by omega
                    have help44: priorState.stack.length - 1 = rest_stack.length := by simp_all
                    omega
                  omega
                simp only [arith_helper]
                have goal : priorState.stack[↑ priorIndex].node = x := by apply listFind
                convert goal
                simp_all only [Fin.getElem_fin]
                conv =>
                  left
                  rw [← List.getElem_cons_succ]
                  rfl
                  exact stack_head
                  tactic =>
                    simp_all
                    omega
                congr
                omega
              · simp_all -- MG: No need to "only ..." when using simp as last tactic
            · simp_all [priorFromEndOtherLimit, priorFromEnd]
              omega

lemma dfs_not_really_monad_invar_one_step_head_is_not_goal_node_x_previously_visited_and_not_stack_head
    (g: WeightedDiGraph V E) (start : V) (goal : V) (priorState : dfs_state g start)
    (stack_not_empty: priorState.stack ≠ [])
    (stack_head_is_not_goal: (priorState.stack.head stack_not_empty).node ≠ goal)
    (x : V) (x_in_prior_visited : x ∈ priorState.visited)
    (x_is_not_stack_head : (priorState.stack.head stack_not_empty).node ≠ x):
      dep_invar_for_x g start priorState x →
        dep_invar_for_x g start (inner_dfs_not_really_monad g start goal priorState).1 x := by
      intro priorInvar
      by_cases x_was_on_previous_stack : ∃ y ∈ priorState.stack, y.node = x
      · apply dfs_not_really_monad_invar_one_step_head_is_not_goal_node_x_previously_visited_and_on_stack_but_not_head
        exact stack_head_is_not_goal
        exact x_in_prior_visited
        exact x_is_not_stack_head
        exact x_was_on_previous_stack
      · apply dfs_not_really_monad_invar_one_step_head_is_not_goal_node_x_previously_visited_and_not_on_stack
        exact stack_head_is_not_goal
        exact x_in_prior_visited
        -- exact x_is_not_stack_head -- MG: not needed in that lemma
        simp at x_was_on_previous_stack
        exact x_was_on_previous_stack
        exact priorInvar

lemma dfs_not_really_monad_invar_one_step_head_is_not_goal_node_x_previously_visited
    (g: WeightedDiGraph V E) (start : V) (goal : V) (priorState : dfs_state g start)
    (stack_not_empty: priorState.stack ≠ [])
    (stack_head_is_not_goal: (priorState.stack.head stack_not_empty).node ≠ goal)
    (x : V) (x_in_prior_visited : x ∈ priorState.visited)
    :
      dep_invar_for_x g start priorState x →
        dep_invar_for_x g start (inner_dfs_not_really_monad g start goal priorState).1 x := by
        intro priorInvar
        by_cases x_is_stack_head : (priorState.stack.head stack_not_empty).node = x
        · apply dfs_not_really_monad_invar_one_step_head_is_not_goal_node_x_previously_visited_and_stack_head
          exact stack_head_is_not_goal
          -- exact x_in_prior_visited -- MG: not needed in that lemma
          exact x_is_stack_head
        · apply dfs_not_really_monad_invar_one_step_head_is_not_goal_node_x_previously_visited_and_not_stack_head
          exact stack_head_is_not_goal
          exact x_in_prior_visited
          exact x_is_stack_head
          exact priorInvar

lemma dfs_not_really_monad_invar_one_step_head_is_not_goal
    (g: WeightedDiGraph V E) (start : V) (goal : V) (priorState : dfs_state g start)
    (stack_not_empty: priorState.stack ≠ [])
    (stack_head_is_not_goal: (priorState.stack.head stack_not_empty).node ≠ goal):
      dep_invar g start priorState → dep_invar g start (inner_dfs_not_really_monad g start goal priorState).1 := by
        ---- case: stack is not empty
        ---- head of the stack was not the goal node
        ---- so we took some node from the stack, expanded it
        intro priorInvar
        intro x
        have ⟨x_as_v, x_is_in_new_visited ⟩ := x
        simp
        by_cases x_was_previously_visited : x_as_v ∈ priorState.visited
        · apply dfs_not_really_monad_invar_one_step_head_is_not_goal_node_x_previously_visited
          exact stack_head_is_not_goal
          exact x_was_previously_visited
          unfold dep_invar_for_x
          simp_all
          exact x_is_in_new_visited
        · apply dfs_not_really_monad_invar_one_step_head_is_not_goal_node_x_not_previously_visited
          exact stack_head_is_not_goal
          exact x_was_previously_visited
          simp_all

lemma dfs_not_really_monad_invar_one_step
    (g: WeightedDiGraph V E) (start : V) (goal : V) (priorState : dfs_state g start):
      dep_invar g start priorState → dep_invar g start (inner_dfs_not_really_monad g start goal priorState).1 := by
        intro priorInvar
        --
        by_cases stack_empty : priorState.stack = []
        · apply dfs_not_really_monad_invar_one_step_stack_empty
          exact stack_empty
          exact priorInvar
        --next prior_state_stack expanded_node rest_of_stack stack_composition =>
        · by_cases stack_head_is_goal : (priorState.stack.head stack_empty).node = goal
          · apply dfs_not_really_monad_invar_one_step_head_is_goal
            exact stack_head_is_goal
            exact priorInvar
          · apply dfs_not_really_monad_invar_one_step_head_is_not_goal
            exact stack_head_is_goal
            exact priorInvar


------------------------------------------------------------------------------------------------
-- Actual main DFS algorithm
------------------------------------------------------------------------------------------------

def dfs_not_really_monad_loop [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (start : V) (goal : V)
    (priorState : dfs_state g start) :
      (dfs_state g start) × (Option (Path g start goal)) :=
      let (nextState, one_round_result) := inner_dfs_not_really_monad g start goal priorState
      match one_round_result with
        | none =>
            dfs_not_really_monad_loop g start goal nextState
        | some result => (nextState, result)
termination_by (Fintype.card V - priorState.visited.card, priorState.stack.length)
decreasing_by
sorry  -- to be copied from above and changed accordingly.


-- heute: lemma: die Loop erhält die Invariante. D.h. wenn invariante davor, dann gilt invariante danach!
-- mit hilfe von: dfs_not_really_monad_invar_one_step
-- schritte: intro (für die linke Seite vom →); dann unfold;
-- dann split (wegen dem match in dfs_not_really_monad_loop)
-- dann hab ich zwei Fälle; einer müsste trivial sein (der some fall),
-- für den anderen müsste ich die nötige invariante haben.
-- möglicherweise muss man auch irgendwie induktion machen?
-- Unklar worüber. Will ich hier einen zyklischen Beweis führen? ...
lemma dfs_not_really_monad_invar_loop
    (g: WeightedDiGraph V E) (start : V) (goal : V) (priorState : dfs_state g start):
      dep_invar g start priorState → dep_invar g start (dfs_not_really_monad_loop g start goal priorState).1 := by
  sorry



/-- `DFS`is the algorithm depth first search, expecting a `WeightedDiGraph V E`, a start node `start : V`and a goal node `goal : V`as imput. -/
def dfs_not_really_monad [FinEnum V] [DecidableEq V] [DecidableEq E] (g: WeightedDiGraph V E) (start : V) (goal : V) : (Option (Path g start goal)) :=
    let emptyW : Walk g start start := Walk.nil
    let emptyP : Path g start start := Path.mk emptyW (by
      simp [emptyW]
      unfold support
      simp
    )
    -- initially the visited list only contains start and we have a path that goes from start to itself (a nil path)
    let reached_nodes_proof : (support g emptyW).toFinset ⊆ {start} := by
      simp [emptyW]
      right
      simp [support]
    let p : NodePathPair g start {start} := NodePathPair.mk start emptyP reached_nodes_proof

    -- generate initial DFS state
    -- dfs_not_really_monad_loop g start goal (by sorry) -- heute!
    sorry -- MG: was a type mismatch here


theorem dfs_not_really_monad_is_sound (g: WeightedDiGraph V E) (start : V) (goal : V) :
    (Option.isSome (dfs_not_really_monad g start goal) → (∃ x : (Path g start goal), x = x)) := by
  intro h -- Option.isSome true on some and false on none, x = x since we need a formula
  constructor -- since goal is existence
  rfl
  let w := Option.get (dfs g start goal) -- Option.get extracts value of returned some and fails otherwise
  apply w
  sorry

-- heute: Korrektheit der DFS. Benutze die Lemmas über die Invariante!
theorem dfs_not_really_monad_is_complete (g: WeightedDiGraph V E) (start : V) (goal : V) :
    ((∃ x : (Path g start goal), x = x) → Option.isSome (dfs_not_really_monad g start goal)) := by -- or Option.isNone (dfs g start goal) → ∄ x (Path g start goal), x = x
      intro walk_exists
      apply Exists.elim walk_exists
      intro theWalk
      intro
      by_contra terminates_with_none
      simp at terminates_with_none
      --unfold dfs
      sorry


--
--
--def inner_dfs_monad [FinEnum V] [DecidableEq E] [DecidableEq V]
--    (g: WeightedDiGraph V E) (start : V) (goal : V) : StateM (dfs_state g start) (Option (Option (Path g start goal))) := by sorry
--
--    --WellFounded.fix (by sorry)
--
--
---- Gregors (failed) approach:
--def dfs_monad_loop [FinEnum V] [DecidableEq E] [DecidableEq V]
--    (g: WeightedDiGraph V E) (start : V) (goal : V) (fuel : Nat × Nat): StateM (dfs_state g start) (Option (Path g start goal)) :=
--    do
--    --if fuel = (0,0) then pure Option.none
--    --else
--      let state_before ← get -- needed for the proof.
--      let one_round_result ← inner_dfs_monad g start goal
--      let state_after ← get
--      match one_round_result with
--        | none =>
--            let h : fuel = (Fintype.card V - state_before.visited.card, state_before.stack.length) :=
--             by sorry
--            dfs_monad_loop g start goal
--              (Fintype.card V - state_after.visited.card, state_after.stack.length)
--        | some result => pure result
--termination_by fuel
--decreasing_by
--
--sorry
--
--
--
--def inner_dfs_not_really_monad [FinEnum V] [DecidableEq E] [DecidableEq V]
--    (g: WeightedDiGraph V E) (start : V) (goal : V)
--    (priorState : dfs_state g start) :
--    (dfs_state g start) × (Option (Option (Path g start goal))) :=
--
--
--
--
--
---- with dependent types -> not good
--def inner_dfs_invar [FinEnum V] [DecidableEq E] [DecidableEq V]
--    (g: WeightedDiGraph V E) (start : V) (goal : V)
--    (visited : Finset V)
--    (stack : List (NodePathPair g start visited))
--    (invar : ∀ x ∈ visited, (∃ y ∈ stack, y.node = x) ∨ (∀ y : V, (g.Adj x y) → y ∈ visited))
--    : Σ (path: Option (Path g start goal)),
--    (Σ (finalVisited : Finset V),
--    (Σ' (finalstack : List (NodePathPair g start finalVisited)),
--    (∀ x : finalVisited, (∃ y ∈ finalstack, y.node = x) ∨ (∀ y : V, (g.Adj x y) → y ∈ finalVisited))))
--
--    := by sorry
--
--
--
--
--/-- `DFS`is the algorithm depth first search, expecting a `WeightedDiGraph V E`, a start node `start : V`and a goal node `goal : V`as imput. -/
--def dfsInvar [FinEnum V] [DecidableEq V] [DecidableEq E] (g: WeightedDiGraph V E) (start : V) (goal : V) : (Option (Path g start goal)) :=
--    let emptyW : Walk g start start := Walk.nil
--    let emptyP : Path g start start := Path.mk emptyW (by
--      simp [emptyW]
--      unfold support
--      simp
--    )
--    -- initially the visited list only contains start and we have a path that goes from start to itself (a nil path)
--    let reached_nodes_proof : (support g emptyW).toFinset ⊆ {start} := by
--      simp [emptyW]
--      right
--      simp [support]
--    let p : NodePathPair g start {start} := NodePathPair.mk start emptyP reached_nodes_proof
--    let dfs_result := inner_dfs_invar g start {start} [p] goal
--
--    dfs_result
--
--
--
--
--theorem dfs_is_complete (g: WeightedDiGraph V E) (start : V) (goal : V) :
--    ((∃ x : (Path g start goal), x = x) → Option.isSome (dfs g start goal)) := by -- or Option.isNone (dfs g start goal) → ∄ x (Path g start goal), x = x
--      intro walk_exists
--      apply Exists.elim walk_exists
--      intro theWalk
--      intro
--      by_contra terminates_with_none
--      simp at terminates_with_none
--
--      --unfold dfs
--      sorry
--
--
--
---- current further ideas:
---- possible invariants:
----$\forall v \in $ \texttt{visited} $\setminus $  \texttt{vertices(stack) :}  \texttt{neighbors(v)} $ \subseteq $ \texttt{visited}
---- h: $\forall $ \texttt{paths(start,goal)} $\exists v \in $ \texttt{vertices(stack) :}  \texttt{isPath(v,goal)}
---- return (pfad, h (h= hyp), maybe the stack, but then also visited set
---- or with mutual block mutual inner_dfs .. theorem end, and later call theorem in completeness proof
---- rewrite algorithm?:
---- using state monads to simulate step function, make outside a step function for a call on each step, try to use kind of a loop
--
--
--
--
--
---- tests
--
--#eval List.dropLast [1, 2, 3, 4]  -- Output: [1, 2, 3]
--
----#eval graph1.Adj 1 0 -- none
----#eval dfs graph1 1 0  -- false
----#eval dfs graph1 0 2  -- true
----#eval Finset.toList (neighbors graph1 1)
----#eval neighbors graph1 1
----#eval is_valid_path graph1 [1,2]   --true
----#eval is_valid_path graph1 [0,1,2] --true
----#eval is_valid_path graph1 [1,2,3] --false
----#eval is_valid_path graph1 [1,2,1] --false
