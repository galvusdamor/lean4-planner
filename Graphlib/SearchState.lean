import Graphlib.Basic


-----------------------------------------------------------------------
------ Search state of the DFS and its invariants
structure base_search_state [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) where
    visited : Finset V
    pathOrder : V → Nat 
    mother : visited → V
    stack : List V


-- type class for possible expansions later on
class has_base_search_state [FinEnum V] [DecidableEq E] [DecidableEq V]
    (g: WeightedDiGraph V E) (B : Type) where
  to_base_state : B → base_search_state g

instance [FinEnum V] [DecidableEq E] [DecidableEq V](g: WeightedDiGraph V E):
    has_base_search_state g (base_search_state g) where
  to_base_state := fun x => x 


--------------------------- basic properties
variable {V : Type} {E : Type} [FinEnum V] [DecidableEq V] [DecidableEq E]
variable {{g : WeightedDiGraph V E}}

abbrev search_prop_goal_on_stack (goal : V) (s : base_search_state g):=
      goal ∈ s.stack

abbrev search_prop_goal_visited (goal : V) (s : base_search_state g):=
      goal ∈ s.visited

abbrev search_prop_stack_empty (s : base_search_state g):=
      s.stack = []

abbrev search_invar_stack_is_visited (s : base_search_state g):=
      ∀ x : V, x ∈ s.stack → x ∈ s.visited

abbrev search_invar_mother_is_visited (s : base_search_state g):=
      ∀ x : s.visited, s.mother x ∈ s.visited

abbrev search_invar_mother_is_adjacent (start : V) (s : base_search_state g):=
      ∀ x : s.visited, ↑x ≠ start → g.Adj (s.mother x) x

abbrev search_invar_mother_decreasing_path_order (start : V) (s : base_search_state g) :=
      ∀ x : s.visited, ↑x ≠ start → s.pathOrder (s.mother x) < s.pathOrder x 

abbrev search_invar_on_stack_or_all_neighbours_visited (s : base_search_state g):=
      ∀ x : s.visited, ↑x ∈ s.stack ∨ ∀ y : V, (g.Adj x y) → y ∈ s.visited

abbrev search_invar_start_visited (start : V) (s : base_search_state g) :=
      start ∈ s.visited

abbrev search_invar_all_basic (start : V) (s : base_search_state g) :=
      search_invar_stack_is_visited s
      ∧ search_invar_mother_is_visited s
      ∧ search_invar_mother_is_adjacent start s
      ∧ search_invar_mother_decreasing_path_order start s
      ∧ search_invar_on_stack_or_all_neighbours_visited s
      ∧ search_invar_start_visited start s


----------------------------------------------------------------------------------------
-- initial configuration of the DFS
def base_search_state_initial (start : V): base_search_state g :=
  let initialVisited : Finset V := ⟨ {start},  by simp ⟩ 
  let initialMother : initialVisited → V := fun x => start 
  let initialPathOrder : V → Nat := fun x => 0 
  let initialStack : List V := [start]
  base_search_state.mk initialVisited initialPathOrder initialMother initialStack


----- Proofs that the initial state of the DFS satisfies the invariants
lemma search_invar_stack_is_visited_initial (start : V):
      search_invar_stack_is_visited (g:=g) (base_search_state_initial start) := by 
      unfold search_invar_stack_is_visited
      unfold base_search_state_initial
      simp

lemma search_invar_mother_is_visited_initial (start : V):
      search_invar_mother_is_visited (g:=g) (base_search_state_initial start) := by 
      unfold search_invar_mother_is_visited
      unfold base_search_state_initial
      simp

lemma search_invar_mother_is_adjacent_initial (start : V):
      search_invar_mother_is_adjacent (g:=g) start (base_search_state_initial start) := by 
      unfold search_invar_mother_is_adjacent
      unfold base_search_state_initial
      simp

lemma search_invar_mother_decreasing_path_order_initial (start : V):
      search_invar_mother_decreasing_path_order (g:=g) start (base_search_state_initial start) := by 
      unfold search_invar_mother_decreasing_path_order  
      unfold base_search_state_initial
      simp

lemma search_invar_on_stack_or_all_neighbours_visited_initial (start : V):
      search_invar_on_stack_or_all_neighbours_visited (g:=g) (base_search_state_initial start) := by 
      unfold search_invar_on_stack_or_all_neighbours_visited  
      unfold base_search_state_initial
      simp

lemma search_invar_start_visited_initial (start : V):
      search_invar_start_visited (g:=g) start (base_search_state_initial start) := by 
      unfold search_invar_start_visited  
      unfold base_search_state_initial
      simp

lemma base_search_state_initial_all_basic_invars (start : V):
    search_invar_all_basic (g:=g) start (base_search_state_initial start) := by
      unfold search_invar_all_basic 
      repeat rw [← and_assoc]
      repeat constructor
      · apply search_invar_stack_is_visited_initial
      · apply search_invar_mother_is_visited_initial
      · apply search_invar_mother_is_adjacent_initial
      · apply search_invar_mother_decreasing_path_order_initial
      · apply search_invar_on_stack_or_all_neighbours_visited_initial
      · apply search_invar_start_visited_initial


